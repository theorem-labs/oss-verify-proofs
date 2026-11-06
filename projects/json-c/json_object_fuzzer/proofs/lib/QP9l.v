(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QTEu Qsw7 QJjn QRUw QT7i Q7UD Qhd4 Qwm6 QlKV QsKa QpNt QgoM Q4v2 Qiiq QfqZ Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0. Import QT7i.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QpNt.Mq4 QgoM.Mq1 Q4v2.Mq0 Qiiq.Mq3 QfqZ.Mq0 QsKa.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section APbMemappendEntry.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (pb n : Z) (T : TSet).

Definition printbuf_memappend_A_entry : Z := 0x9a0ac.

Lemma memappend_A_cps_c :
forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (tp a0 a1 a2 : word)
(buf bpos cap b : Z) (content src : list byte) (errv : word) (A : ASA A4L HIx),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B0 m0 md0 ->
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
F (Z_to_bv 64 printbuf_memappend_A_entry) fc None m0 (seg_rom asegs)).
Proof.
intros until A. intros HP PBX Hn SRC SRCL Hb0 SRCB UPS0 ST LO LOS SPA HT ERR TP RA A0 A1 A2 BB K.
pose proof PBX as PB0. destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold_consts. unfold printbuf_memappend_A_entry, A_SB, A_TP, A_ERRNO in *. word_range sp SPR. subst tp a0 a1 a2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP pb 16 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
pose proof (src_loc_facts HIx _ _ _ _ _ _ _ _ _ _ _ _ HP SRCB ltac:(lia)) as (Hslo & Hshi & DISJbs & DISJps & Hsimg & AMS).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hsimg.
shadow_nowA A4L HIx HP pb 16 SHpb.
pose proof (proj1 (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 1 pb 16 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity))) as SHhi.

pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ 804279 HP ltac:(cbn; lia) ltac:(cbn; lia)) as ERRSH.
cbn [hl_reg_globals hl_sb A4L] in ERRSH.
match type of ERRSH with bytes_at _ _ _ [Z_to_bv 8 ?v] => let w := eval vm_compute in v in change v with w in ERRSH end.
a4l.
assert (ERRSHc : ro_cells asegs m0 2148255159 [C1 (Z_to_bv 8 0)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact ERRSH]). clear ERRSH.
stash PBUF. stash SRC. stash DISJbs. stash Hbimg.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m0) as MU.
change (6434400 - 164) with 6434236 in ERR.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6434236, 6434240)] m0) as MUE.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 112%nat ST.
do 14 step.
step. step. step.
step. if_falsex.
step.
asan_chkA.
step. norm_w32.
step. step. step.
match goal with |- context [bv_swrap 32 ?z] =>
replace z with ((2147483646 - bpos) + 4294967295 * 4294967296) by (rewrite unsigned_lit by lia; lia) end.
rewrite swrap32_shift. rewrite swrap32_id by lia.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (EFB : forall (xra x9 y1 y3 y4 x18 x22 x23 x24 x25 : word),
evt asegs (AJ5e A4L HIx A T md0)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 6434400) t0 t1 t2 (Z_to_bv 64 (pb + 8)) x9
(Z_to_bv 64 6434236) y1 (Z_to_bv 64 n) y3 y4 a5 a6 a7
x18 s3 (Z_to_bv 64 2147450880) (Z_to_bv 64 (pb / 8 + 2147450881)) x22 x23 x24 x25 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9a130) fc None mc (seg_rom asegs)))
end.
{ intros xra x9 y1 y3 y4 x18 x22 x23 x24 x25. clear MU.
step. stepz.
step. step.
do 15 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
evt_done5. apply K. unfold memappend_A_post_c.
unstash PBUF.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
eapply (rw_cells_transport asegs _ m0 mf) in PBUF; [| exact MUE | exact WM | cbn [disjoint_from]; simpl_sizes; unstash Hbimg; unfold alloc_ceiling in *; lia];
exists mf, (2^64 - 1), (Z_to_bv 64 27), buf, cap, B0 end.
split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split.
{ eapply heap_pres_trans; [exact HPR|]. eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MUE | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | clia |].
apply Forall_cons; [cbn [fst snd]; left; unfold alloc_ceiling in *; lia|].
apply Forall_cons; [cbn [fst snd]; right; right; intros x Hx; cbn; unfold A_TP; lia | apply Forall_nil]. }
split; [assumption|]. split; [pose proof (memappend_costX2_nonneg cap bpos n ltac:(lia)); lia|]. split; [lia|].
split.
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | assumption].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MUE).
apply Forall_cons; [cbn [fst snd]; left; unfold alloc_ceiling in *; lia|].
apply Forall_cons; [cbn [fst snd]; right; right; intros x Hx; cbn; unfold A_TP; lia | apply Forall_nil]. }
right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [left; lia|].
unfold pbuf_core. repeat (split; [first [lia | eassumption] |]). exact PBUF. }
step.
destruct (Z.le_gt_cases n (2147483646 - bpos)) as [Hroom0|Hbig0].
2:{ if_falsex.
step. step. step. step.
step. step. step. step. if_false. rewrite ?sxb_zero.
apply EFB. }
if_truex.
step.
asan_chkA.
step. norm_w32. step. norm_w32. step. norm_w32.
step. sh_norm.
step.
unstash SRC. unstash DISJbs. unstash Hbimg. unstash PBUF.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (bytes_at_transport asegs _ m0 mc) in SRC; [| exact MU | cbn [disjoint_from]; simpl_sizes; rewrite ?SRCL; unfold alloc_ceiling in *; lia];
eapply (rw_cells_transport asegs _ m0 mc) in PBUF; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia];
assert (HPc : HEAPAx A ((pb, 16) :: (buf, cap) :: LB) LM FRS B0 mc md0) by heap_nowA A4L HIx HP MU WM MI;
assert (HPRc : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc)
by (eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | clia | solve_clientWA A4L HIx HP]);
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ pb 16 HP ltac:(left; reflexivity)) as APB; cbn [hl_sb A4L] in APB;
assert (UPSc : 0 < n -> unpoisoned asegs mc A_SB b n)
by (intros Hpos; eapply unpoisoned_transport; [exact (UPS0 Hpos) | exact MU |];
intros a k Ha Hk; unfold shadow_span_lo, shadow_span_hi in Ha, Hk; unfold A_SB in Ha, Hk, APB; cbn [disjoint_from]; Z.div_mod_to_equations; lia)
end.
destruct (Z.lt_ge_cases (bpos + n + 1) cap) as [Hfit|Hgrow].
-
if_truex.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
evt_done5.
eapply (memappend_A_tail HIx ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb buf bpos cap n content T s0)
with (md := md0) (buf := buf) (bpos := bpos) (cap := cap) (b := b) (content := content) (src := src) (errv := errv);
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ => unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- _ -> unpoisoned _ _ _ _ _ => exact UPSc
| |- _ \/ app_mem _ _ => exact AMS
| |- model_vm_only (cfg_model _) (cfg_model _) => apply model_vm_only_refl
| |- bB _ - _ <= _ => pose proof (memappend_costX2_nonneg cap bpos n ltac:(lia)); lia
| |- _ = memappend_cap2 _ _ _ => rewrite memappend_cap2_keep by lia; reflexivity
| |- _ => try (unfold_consts; lia)
end.
- if_falsex.
step.
try replace (2147450880 + pb / 8) with (pb / 8 + 2147450880) by lia.
step. step. if_false. rewrite ?zxb_zero.
step.
step.
destruct (Z.lt_ge_cases (bpos + n) cap) as [Heq1|Hge1].
+
if_truex.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
evt_done5.
eapply (memappend_A_rebase HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb n T buf bpos cap content) with (md := md0) (obuf := buf) (ocap := cap) (buf := buf) (bpos := bpos) (cap := cap) (b := b)
(content := content) (src := src) (errv := errv);
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ => unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- _ -> unpoisoned _ _ _ _ _ => exact UPSc
| |- _ \/ app_mem _ _ => exact AMS
| |- model_vm_only (cfg_model _) (cfg_model _) => apply model_vm_only_refl
| |- bB _ - _ <= _ => pose proof (memappend_costX2_nonneg cap bpos n ltac:(lia)); lia
| |- _ = memappend_cap2 _ _ _ => rewrite memappend_cap2_keep by lia; reflexivity
| |- _ => try (unfold_consts; lia)
end.
+ if_falsex.
step. step.
step.
destruct (Z.lt_ge_cases (bpos + n) 2147483639) as [Hok2|Hbig2].
* if_truex.
evt_done5.
eapply (memappend_A_grow HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb n T) with (md := md0) (buf := buf) (bpos := bpos) (cap := cap) (b := b) (content := content) (src := src) (errv := errv);
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ => unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- model_vm_only (cfg_model _) (cfg_model _) => apply model_vm_only_refl
| |- _ => try (rewrite ?memappend_costX_grow in * by lia; rewrite ?memappend_costX2_grow in * by lia; unfold memappend_costB in *; unfold_consts; lia)
end.
* if_falsex.
step. step. step. step.
step. step. step. step. if_true.
apply EFB.
Qed.
End APbMemappendEntry.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgHv QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0. Import QT7i.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QpNt.Mq4 QgoM.Mq1 Q4v2.Mq0 QgHv.Mq0 QSHS.Mq0 QsKa.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section APbMemappendGrow.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (pb n : Z) (T : TSet).

Lemma memappend_A_grow_nf :
forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(buf bpos cap b : Z) (content src : list byte) (errv : word) (fjunk : list byte),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbufx m pb buf bpos cap content ->
cap <= bpos + n -> bpos + n < 2147483639 -> 0 <= n < 2^31 ->
bytes_at asegs m b src -> Z.of_nat (length src) = n -> 0 <= b ->
src_locA LB FRS b n -> (0 < n -> unpoisoned asegs m A_SB b n) ->
stk asegs m lo (bv_unsigned sp + -112) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -112 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m (bv_unsigned sp + -112) [CB 8 fjunk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
bB B0 <= bB B -> bD B0 <= bD B -> memappend_costB cap bpos n <= bB B ->
(forall ms' md' A', memappend_A_post_nf HIx ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb buf bpos cap content src n lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pb + 8)) (Z_to_bv 64 (pb + 12))
(Z_to_bv 64 pb) (Z_to_bv 64 b) (Z_to_bv 64 n) (Z_to_bv 64 (bpos + n)) (Z_to_bv 64 2147483639) a5 a6 a7
(Z_to_bv 64 buf) s3 (Z_to_bv 64 A_SB) (Z_to_bv 64 (pb / 8 + 2147450881)) (Z_to_bv 64 (pb / 8)) (Z_to_bv 64 (pb / 8 + A_SB))
(Z_to_bv 64 cap) (Z_to_bv 64 (pb / 8 + 2147450881)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9a1ac) fc None m (seg_rom asegs)).
Proof.
intros until fjunk.
intros HP PBX Hgrow Hmax Hn SRC SRCL Hb0 SRCB UPS0 ST LO LOS SPA HT FR ERR RA VM0 HPR BB0 BD0 BB K.
destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
assert (LEN : length content = Z.to_nat cap) by (destruct PBUF as [[[Hwf _] _] _]; exact Hwf).
unfold_consts. unfold A_SB, A_TP, A_ERRNO, memappend_costB in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
blk_factsA A4L HIx HP pb 16 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
a4l.
stash PBUF. stash SRC.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
step. stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (JOIN : forall (ns : Z) (y3 y4 : word), bpos + n + 1 <= ns -> cap <= ns < 2^31 -> 16 * ns <= 16 * Z.max (2 * cap) (bpos + n + 9) -> ns = memappend_cap2 cap bpos n ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 6434400) t0 t1 t2 (Z_to_bv 64 (pb + 8)) (Z_to_bv 64 (pb + 12))
(Z_to_bv 64 pb) (Z_to_bv 64 b) (Z_to_bv 64 n) y3 y4 a5 a6 a7
(Z_to_bv 64 buf) (Z_to_bv 64 ns) (Z_to_bv 64 2147450880) (Z_to_bv 64 (pb / 8 + 2147450881)) (Z_to_bv 64 (pb / 8)) (Z_to_bv 64 (pb / 8 + 2147450880))
(Z_to_bv 64 cap) (Z_to_bv 64 (pb / 8 + 2147450881)) (Z_to_bv 64 pb) (Z_to_bv 64 n) t3 t4 t5 t6)
F (Z_to_bv 64 0x9a1e0) fc None mc (seg_rom asegs)))
end.
2:{ step.
destruct (Z.lt_ge_cases cap 1073741824) as [Hsmall|Hlarge].
- if_truex. step.
rewrite (unsigned_lit cap) by lia. rewrite (Z.shiftl_mul_pow2 cap 1) by lia. change (2^1) with 2.
rewrite (swrap32_id (cap * 2)) by lia.
step. norm_w32.
step.
destruct (Z.lt_ge_cases (bpos + n + 9) (cap * 2)) as [Hlt3|Hge3].
+ if_truex. step. step. apply (JOIN (cap * 2)); try lia. rewrite memappend_cap2_grow_small by lia. lia.
+ if_falsex. step. step. step. apply (JOIN (bpos + n + 9)); try lia. rewrite memappend_cap2_grow_small by lia. lia.
- if_falsex. step. step. step. norm_w32. step.
apply (JOIN (bpos + n + 9)); try lia. rewrite memappend_cap2_grow_large by lia. reflexivity. }
intros ns y3 y4 Hns1 Hns2 Hns3 CAPE.
step. step. step.

assert (Hne : pb <> buf).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst. apply Hni. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pb 16 buf cap HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne) as DISJ.
unstash PBUF.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (rw_cells_transport asegs _ m mc) in PBUF; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; rewrite ?Z2Nat.id by lia; unfold alloc_ceiling in *; lia] end.
rewrite <- (app_nil_r content) in PBUF.
a4l.
alloc_callA OBL_REALLOC_NF blk buf uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (right; left; reflexivity).
all: try exact PBUF.
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; first [left; lia | unfold a4_straces; repeat first [left; reflexivity | right] | lia]).
all: try (pose proof (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP)); cbn [uw_cost]; lia).
intros ms2 m2 md2 A2 r errv2 RS VM2 ST2 ERR2 OUT2. open_ret RS. a4l.
rewrite lb_remove_other in OUT2 by (cbn; lia). rewrite lb_remove_head in OUT2.
pose proof (src_loc_facts HIx _ _ _ _ _ _ _ _ _ _ _ _ HP SRCB ltac:(lia)) as (Hslo & Hshi & DISJbs & DISJps & Hsimg & AMS).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hsimg. a4l.

pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ pb 16 HP ltac:(left; reflexivity)) as APB. cbn [hl_sb A4L] in APB.
assert (UPS1 : 0 < n -> unpoisoned asegs m1 A_SB b n).
{ intros Hpos. eapply unpoisoned_transport; [exact (UPS0 Hpos) | exact MU |].
intros a k Ha Hk. unfold shadow_span_lo, shadow_span_hi in Ha, Hk. unfold A_SB in Ha, Hk, APB. cbn [disjoint_from]. Z.div_mod_to_equations. lia. }
unstash SRC.
eapply (bytes_at_transport asegs _ m m1) in SRC; [| exact MU | cbn [disjoint_from]; simpl_sizes; rewrite ?SRCL; unfold alloc_ceiling in *; lia].
destruct OUT2 as (Hr & HPR2 & [junk BLK] & HP2).
-
assert (SRC2 : bytes_at asegs m2 b src).
{ eapply (src_loc_bytes_pres _ LB LM FRS); [exact HPR2 | exact MI | exact (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) | | rewrite SRCL; exact SRCB | exact SRC]. intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; exact Hbb | right; exact Hbb]. }
assert (UPS2 : 0 < n -> unpoisoned asegs m2 A_SB b n).
{ intros Hpos. destruct SRCB as [(sa & sk & Hsrc & Hsa & Hsk) | [(Fs & ks & HFs & HFa & HFk) | SG]].
- eapply (unpoisoned_of_blk HIx); [exact HP2 | right; right; exact Hsrc | lia | lia | lia].
- eapply (unpoisoned_pres_frame HIx); [exact HP | exact HFs | exact HFa | exact HFk | exact (UPS1 Hpos) | exact HPR2].
- eapply (unpoisoned_of_glob HIx); [exact HP2 | exact SG | exact Hpos]. }
clear SRC.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r ns HP2 ltac:(left; reflexivity)) as (_ & Hral & Hrlo & Hrhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r ns HP2 ltac:(left; reflexivity)) as Hrimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi.
assert (Hrpb : r <> pb).
{ pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2) as ND. rewrite map_app in ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. intros E; subst r; apply Hni; left; reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r ns pb 16 HP2 ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hrpb) as DISJrp.
pose proof (src_loc_fresh HIx _ _ _ _ _ _ _ _ _ LB b n HP2 SRCB ltac:(lia) ltac:(intros sa sk Hsk; right; exact Hsk)) as DISJrs.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in PBS; [| right; right; exists (pb, 16); cbn; split; [left; reflexivity | lia]].
a4l. clear MU WM MI ST PBUF.
rewrite LEN, Z.min_r, Z2Nat.id, firstn_all2 in BLK by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
shadow_nowA A4L HIx HP2 pb 16 SHpb.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 0 pb 16 HP2 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 1 pb 16 HP2 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP1.
a4l.
pose proof (munch_refl [(pb, pb + 16)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
stash SRC2. stash BLK. stash DISJrs. stash DISJbs. stash DISJps. stash Hrimg. stash Hsimg.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
step.
step. step. if_false. rewrite ?sxb_zero.
step. stepz.
step. step. step. if_false. rewrite ?zxb_zero.
step. stepz.
clear SHpb SEP0 SEP1.
unstash SRC2. unstash BLK. unstash DISJrs. unstash DISJbs. unstash DISJps. unstash Hrimg. unstash Hsimg.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (bytes_at_transport asegs _ m2 mc) in SRC2; [| exact MU | cbn [disjoint_from]; simpl_sizes; rewrite ?SRCL; lia];
eapply (rw_cells_transport asegs _ m2 mc) in BLK; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia];
assert (HP3 : HEAPAx A2 ((pb, 16) :: (r, ns) :: LB) LM FRS (charge B (16 * ns + 512) (uw_cost UWptr)) mc md2)
end.
{ eapply (heapA_perm A4L HIx); [ | apply perm_swap | apply Permutation_refl | apply Permutation_refl ].
eapply (heapA_client_frame A4L HIx); [ exact HP2 | | exact WM | exact MI ].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU). solve_frameW_withA HP2. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (UPS3 : 0 < n -> unpoisoned asegs mc A_SB b n) end.
{ intros Hpos. eapply unpoisoned_transport; [exact (UPS2 Hpos) | exact MU |].
intros a k Ha Hk. unfold shadow_span_lo, shadow_span_hi in Ha, Hk. unfold A_SB in Ha, Hk, APB. cbn [disjoint_from]. Z.div_mod_to_equations. lia. }
match goal with FRc : rw_cells asegs ?mc (bv_unsigned sp + -112) (C8 (Z_to_bv 64 b) :: ?rest) |- _ =>
apply (rw_cells_recast_prefix asegs mc _ [C8 (Z_to_bv 64 b)] [CB 8 (le8 (Z_to_bv 64 b))] rest) in FRc; [| split; [apply length_le8 | exact I] | reflexivity | reflexivity] end.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
evt_done5.
eapply (memappend_A_rebase_nf HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb n T buf bpos cap content) with (md := md2) (A := A2) (obuf := buf) (ocap := cap) (buf := r) (bpos := bpos) (cap := ns) (b := b)
(content := content ++ junk) (src := src) (errv := errv2) (fjunk := le8 (Z_to_bv 64 b));
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ =>
unfold pbufx, pbuf_core; split; [lia|]; split; [lia|]; split; [destruct BLK as [[[Hwf _] _] _]; rewrite Hwf; lia|]; split; [eassumption|]; exact BLK
| |- _ -> unpoisoned _ _ _ _ _ => exact UPS3
| |- _ \/ app_mem _ _ => exact AMS
| |- model_vm_only (cfg_model _) (cfg_model _) => eapply model_vm_only_trans; eassumption
| |- heap_pres _ _ _ _ _ =>
eapply heap_pres_trans; [exact HPR|];
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP2 | intros bb Hbb0; right; right; exact Hbb0 | clia | solve_clientWA A4L HIx HP2]
| |- firstn _ _ = firstn _ _ => rewrite firstn_app; replace (Z.to_nat bpos - length content)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r
| |- bB _ - _ <= _ => cbn [bB charge]; rewrite ?memappend_costX2_grow by lia; unfold memappend_costB in *; lia
| |- bD _ - _ <= _ => cbn [bD charge uw_cost]; lia
| |- bD _ <= _ => cbn [bD charge uw_cost]; lia
| |- _ => try (unfold_consts; lia)
end.
Qed.
End APbMemappendGrow.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0. Import QT7i.
Import QbFI. Import QRUw. Import Qwm6.Mq1.    Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QpNt.Mq8 QgoM Q4v2 Qiiq.Mqa QfqZ QsKa.Mqf.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section APbMemappendEntry.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (pb n : Z) (T : TSet).

Definition printbuf_memappend_A_entry : Z := 0x9b4fc.

Lemma memappend_A_cps_c :
forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (tp a0 a1 a2 : word)
(buf bpos cap b : Z) (content src : list byte) (errv : word) (A : ASA A4L HIx),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B0 m0 md0 ->
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
F (Z_to_bv 64 printbuf_memappend_A_entry) fc None m0 (seg_rom asegs)).
Proof.
intros until A. intros HP PBX Hn SRC SRCL Hb0 SRCB UPS0 ST LO LOS SPA HT ERR TP RA A0 A1 A2 BB K.
pose proof PBX as PB0. destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold_consts. unfold printbuf_memappend_A_entry, A_SB, A_TP, A_ERRNO in *. word_range sp SPR. subst tp a0 a1 a2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP pb 16 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
pose proof (src_loc_facts HIx _ _ _ _ _ _ _ _ _ _ _ _ HP SRCB ltac:(lia)) as (Hslo & Hshi & DISJbs & DISJps & Hsimg & AMS).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hsimg.
shadow_nowA A4L HIx HP pb 16 SHpb.
pose proof (proj1 (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 1 pb 16 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity))) as SHhi.

pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ 805519 HP ltac:(cbn; lia) ltac:(cbn; lia)) as ERRSH.
cbn [hl_reg_globals hl_sb A4L] in ERRSH.
match type of ERRSH with bytes_at _ _ _ [Z_to_bv 8 ?v] => let w := eval vm_compute in v in change v with w in ERRSH end.
a4l.
assert (ERRSHc : ro_cells asegs m0 2148256399 [C1 (Z_to_bv 8 0)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact ERRSH]). clear ERRSH.
stash PBUF. stash SRC. stash DISJbs. stash Hbimg.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m0) as MU.
change (6444320 - 164) with 6444156 in ERR.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6444156, 6444160)] m0) as MUE.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 112%nat ST.
do 14 step.
step. step. step.
step. if_falsex.
step. if_falsex.
step. step. ubsan_align Hal.
step.
asan_chkA.
step. norm_w32.
step. step. step. step. norm_w32.
step. if_falsex.
step. step. norm_w32. step. if_falsex.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (EFB : forall (xra x9 y1 y3 y4 y5 x18 x22 x23 x24 x25 : word),
evt asegs (AJ5e A4L HIx A T md0)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 6444320) t0 t1 t2 (Z_to_bv 64 (pb + 8)) x9
(Z_to_bv 64 6444156) y1 (Z_to_bv 64 n) y3 y4 y5 a6 a7
x18 s3 (Z_to_bv 64 2147450880) (Z_to_bv 64 (pb / 8 + 2147450881)) x22 x23 x24 x25 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b5ac) fc None mc (seg_rom asegs)))
end.
{ intros xra x9 y1 y3 y4 y5 x18 x22 x23 x24 x25. clear MU.
step. stepz.
step. step.
do 15 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
evt_done5. apply K. unfold memappend_A_post_c.
unstash PBUF.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
eapply (rw_cells_transport asegs _ m0 mf) in PBUF; [| exact MUE | exact WM | cbn [disjoint_from]; simpl_sizes; unstash Hbimg; unfold alloc_ceiling in *; lia];
exists mf, (2^64 - 1), (Z_to_bv 64 27), buf, cap, B0 end.
split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split.
{ eapply heap_pres_trans; [exact HPR|]. eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MUE | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | clia |].
apply Forall_cons; [cbn [fst snd]; left; unfold alloc_ceiling in *; lia|].
apply Forall_cons; [cbn [fst snd]; right; right; intros x Hx; cbn; unfold A_TP; lia | apply Forall_nil]. }
split; [assumption|]. split; [pose proof (memappend_costX2_nonneg cap bpos n ltac:(lia)); lia|]. split; [lia|].
split.
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | assumption].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MUE).
apply Forall_cons; [cbn [fst snd]; left; unfold alloc_ceiling in *; lia|].
apply Forall_cons; [cbn [fst snd]; right; right; intros x Hx; cbn; unfold A_TP; lia | apply Forall_nil]. }
right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [left; lia|].
unfold pbuf_core. repeat (split; [first [lia | eassumption] |]). exact PBUF. }
step.
destruct (Z.le_gt_cases n (2147483646 - bpos)) as [Hroom0|Hbig0].
2:{ if_falsex.
step. step. step. step.
step. first [if_falsex | if_lit].
step. step. first [if_falsex | if_lit].
step. step. step. step. if_false. rewrite ?sxb_zero.
apply EFB. }
if_truex.
step.
asan_chkA.
step. step. norm_w32. step. if_falsex.
step. step. norm_w32. step. if_falsex.
step. norm_w32.
step. sh_norm.
step.
unstash SRC. unstash DISJbs. unstash Hbimg. unstash PBUF.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (bytes_at_transport asegs _ m0 mc) in SRC; [| exact MU | cbn [disjoint_from]; simpl_sizes; rewrite ?SRCL; unfold alloc_ceiling in *; lia];
eapply (rw_cells_transport asegs _ m0 mc) in PBUF; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia];
assert (HPc : HEAPAx A ((pb, 16) :: (buf, cap) :: LB) LM FRS B0 mc md0) by heap_nowA A4L HIx HP MU WM MI;
assert (HPRc : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc)
by (eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | clia | solve_clientWA A4L HIx HP]);
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ pb 16 HP ltac:(left; reflexivity)) as APB; cbn [hl_sb A4L] in APB;
assert (UPSc : 0 < n -> unpoisoned asegs mc A_SB b n)
by (intros Hpos; eapply unpoisoned_transport; [exact (UPS0 Hpos) | exact MU |];
intros a k Ha Hk; unfold shadow_span_lo, shadow_span_hi in Ha, Hk; unfold A_SB in Ha, Hk, APB; cbn [disjoint_from]; Z.div_mod_to_equations; lia)
end.
destruct (Z.lt_ge_cases (bpos + n + 1) cap) as [Hfit|Hgrow].
-
if_truex.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
evt_done5.
eapply (memappend_A_tail HIx ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb buf bpos cap n content T s0)
with (md := md0) (buf := buf) (bpos := bpos) (cap := cap) (b := b) (content := content) (src := src) (errv := errv);
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ => unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- _ -> unpoisoned _ _ _ _ _ => exact UPSc
| |- _ \/ app_mem _ _ => exact AMS
| |- model_vm_only (cfg_model _) (cfg_model _) => apply model_vm_only_refl
| |- bB _ - _ <= _ => pose proof (memappend_costX2_nonneg cap bpos n ltac:(lia)); lia
| |- _ = memappend_cap2 _ _ _ => rewrite memappend_cap2_keep by lia; reflexivity
| |- _ => try (unfold_consts; lia)
end.
- if_falsex.
step.
try replace (2147450880 + pb / 8) with (pb / 8 + 2147450880) by lia.
step. step. if_false. rewrite ?zxb_zero.
step.
step.
destruct (Z.lt_ge_cases (bpos + n) cap) as [Heq1|Hge1].
+
if_truex.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
evt_done5.
eapply (memappend_A_rebase HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb n T buf bpos cap content) with (md := md0) (obuf := buf) (ocap := cap) (buf := buf) (bpos := bpos) (cap := cap) (b := b)
(content := content) (src := src) (errv := errv);
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ => unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- _ -> unpoisoned _ _ _ _ _ => exact UPSc
| |- _ \/ app_mem _ _ => exact AMS
| |- model_vm_only (cfg_model _) (cfg_model _) => apply model_vm_only_refl
| |- bB _ - _ <= _ => pose proof (memappend_costX2_nonneg cap bpos n ltac:(lia)); lia
| |- _ = memappend_cap2 _ _ _ => rewrite memappend_cap2_keep by lia; reflexivity
| |- _ => try (unfold_consts; lia)
end.
+ if_falsex.
step. step. norm_w32.
step.
destruct (Z.lt_ge_cases (bpos + n) 2147483639) as [Hok2|Hbig2].
* if_truex.
evt_done5.
eapply (memappend_A_grow HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb n T) with (md := md0) (buf := buf) (bpos := bpos) (cap := cap) (b := b) (content := content) (src := src) (errv := errv);
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ => unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- model_vm_only (cfg_model _) (cfg_model _) => apply model_vm_only_refl
| |- _ => try (rewrite ?memappend_costX_grow in * by lia; rewrite ?memappend_costX2_grow in * by lia; unfold memappend_costB in *; unfold_consts; lia)
end.
* if_falsex.
step. step. step. step.
step. first [if_falsex | if_lit].
step. step. first [if_falsex | if_lit].
step. step. step. step. if_true.
apply EFB.
Qed.
End APbMemappendEntry.
End RC__1.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTEu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTEu. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QT7i.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI.  From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpNt.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgHv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgHv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSHS.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqf.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section APbMemappendGrow.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (pb n : Z) (T : TSet).

Lemma memappend_A_grow_nf :
forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(buf bpos cap b : Z) (content src : list byte) (errv : word) (fjunk : list byte),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbufx m pb buf bpos cap content ->
cap <= bpos + n -> bpos + n < 2147483639 -> 0 <= n < 2^31 ->
bytes_at asegs m b src -> Z.of_nat (length src) = n -> 0 <= b ->
src_locA LB FRS b n -> (0 < n -> unpoisoned asegs m A_SB b n) ->
stk asegs m lo (bv_unsigned sp + -112) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -112 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m (bv_unsigned sp + -112) [CB 8 fjunk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
bB B0 <= bB B -> bD B0 <= bD B -> memappend_costB cap bpos n <= bB B ->
(forall ms' md' A', memappend_A_post_nf HIx ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb buf bpos cap content src n lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pb + 8)) (Z_to_bv 64 (pb + 12))
(Z_to_bv 64 pb) (Z_to_bv 64 b) (Z_to_bv 64 n) (Z_to_bv 64 (bpos + n + 1)) (Z_to_bv 64 2147483640) a5 a6 a7
(Z_to_bv 64 buf) s3 (Z_to_bv 64 A_SB) (Z_to_bv 64 (pb / 8 + 2147450881)) (Z_to_bv 64 (pb / 8)) (Z_to_bv 64 (pb / 8 + A_SB))
(Z_to_bv 64 cap) (Z_to_bv 64 (pb / 8 + 2147450881)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b644) fc None m (seg_rom asegs)).
Proof.
intros until fjunk.
intros HP PBX Hgrow Hmax Hn SRC SRCL Hb0 SRCB UPS0 ST LO LOS SPA HT FR ERR RA VM0 HPR BB0 BD0 BB K.
destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
assert (LEN : length content = Z.to_nat cap) by (destruct PBUF as [[[Hwf _] _] _]; exact Hwf).
unfold_consts. unfold A_SB, A_TP, A_ERRNO, memappend_costB in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
blk_factsA A4L HIx HP pb 16 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
a4l.
stash PBUF. stash SRC.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
step. stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (JOIN : forall (ns : Z) (y3 y4 : word), bpos + n + 1 <= ns -> cap <= ns < 2^31 -> 16 * ns <= 16 * Z.max (2 * cap) (bpos + n + 9) -> ns = memappend_cap2 cap bpos n ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 6444320) t0 t1 t2 (Z_to_bv 64 (pb + 8)) (Z_to_bv 64 (pb + 12))
(Z_to_bv 64 pb) (Z_to_bv 64 b) (Z_to_bv 64 n) y3 y4 a5 a6 a7
(Z_to_bv 64 buf) (Z_to_bv 64 ns) (Z_to_bv 64 2147450880) (Z_to_bv 64 (pb / 8 + 2147450881)) (Z_to_bv 64 (pb / 8)) (Z_to_bv 64 (pb / 8 + 2147450880))
(Z_to_bv 64 cap) (Z_to_bv 64 (pb / 8 + 2147450881)) (Z_to_bv 64 pb) (Z_to_bv 64 n) t3 t4 t5 t6)
F (Z_to_bv 64 0x9b684) fc None mc (seg_rom asegs)))
end.
2:{ step.
destruct (Z.lt_ge_cases cap 1073741824) as [Hsmall|Hlarge].
- if_truex. step. step. norm_w32. step. if_falsex.
step.
rewrite (unsigned_lit cap) by lia. rewrite (Z.shiftl_mul_pow2 cap 1) by lia. change (2^1) with 2.
rewrite (swrap32_id (cap * 2)) by lia.
step. norm_w32.
step.
destruct (Z.lt_ge_cases (bpos + n + 9) (cap * 2)) as [Hlt3|Hge3].
+ if_truex. step. step. apply (JOIN (cap * 2)); try lia. rewrite memappend_cap2_grow_small by lia. lia.
+ if_falsex. step. step. step. apply (JOIN (bpos + n + 9)); try lia. rewrite memappend_cap2_grow_small by lia. lia.
- if_falsex. step. step. step. norm_w32. step.
apply (JOIN (bpos + n + 9)); try lia. rewrite memappend_cap2_grow_large by lia. reflexivity. }
intros ns y3 y4 Hns1 Hns2 Hns3 CAPE.
step. step. step.

assert (Hne : pb <> buf).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst. apply Hni. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pb 16 buf cap HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne) as DISJ.
unstash PBUF.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (rw_cells_transport asegs _ m mc) in PBUF; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; rewrite ?Z2Nat.id by lia; unfold alloc_ceiling in *; lia] end.
rewrite <- (app_nil_r content) in PBUF.
a4l.
alloc_callA OBL_REALLOC_NF blk buf uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (right; left; reflexivity).
all: try exact PBUF.
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; first [left; lia | unfold a4_straces; repeat first [left; reflexivity | right] | lia]).
all: try (pose proof (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP)); cbn [uw_cost]; lia).
intros ms2 m2 md2 A2 r errv2 RS VM2 ST2 ERR2 OUT2. open_ret RS. a4l.
rewrite lb_remove_other in OUT2 by (cbn; lia). rewrite lb_remove_head in OUT2.
pose proof (src_loc_facts HIx _ _ _ _ _ _ _ _ _ _ _ _ HP SRCB ltac:(lia)) as (Hslo & Hshi & DISJbs & DISJps & Hsimg & AMS).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hsimg. a4l.

pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ pb 16 HP ltac:(left; reflexivity)) as APB. cbn [hl_sb A4L] in APB.
assert (UPS1 : 0 < n -> unpoisoned asegs m1 A_SB b n).
{ intros Hpos. eapply unpoisoned_transport; [exact (UPS0 Hpos) | exact MU |].
intros a k Ha Hk. unfold shadow_span_lo, shadow_span_hi in Ha, Hk. unfold A_SB in Ha, Hk, APB. cbn [disjoint_from]. Z.div_mod_to_equations. lia. }
unstash SRC.
eapply (bytes_at_transport asegs _ m m1) in SRC; [| exact MU | cbn [disjoint_from]; simpl_sizes; rewrite ?SRCL; unfold alloc_ceiling in *; lia].
destruct OUT2 as (Hr & HPR2 & [junk BLK] & HP2).
-
assert (SRC2 : bytes_at asegs m2 b src).
{ eapply (src_loc_bytes_pres _ LB LM FRS); [exact HPR2 | exact MI | exact (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) | | rewrite SRCL; exact SRCB | exact SRC]. intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; exact Hbb | right; exact Hbb]. }
assert (UPS2 : 0 < n -> unpoisoned asegs m2 A_SB b n).
{ intros Hpos. destruct SRCB as [(sa & sk & Hsrc & Hsa & Hsk) | [(Fs & ks & HFs & HFa & HFk) | SG]].
- eapply (unpoisoned_of_blk HIx); [exact HP2 | right; right; exact Hsrc | lia | lia | lia].
- eapply (unpoisoned_pres_frame HIx); [exact HP | exact HFs | exact HFa | exact HFk | exact (UPS1 Hpos) | exact HPR2].
- eapply (unpoisoned_of_glob HIx); [exact HP2 | exact SG | exact Hpos]. }
clear SRC.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r ns HP2 ltac:(left; reflexivity)) as (_ & Hral & Hrlo & Hrhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r ns HP2 ltac:(left; reflexivity)) as Hrimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi.
assert (Hrpb : r <> pb).
{ pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2) as ND. rewrite map_app in ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. intros E; subst r; apply Hni; left; reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r ns pb 16 HP2 ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hrpb) as DISJrp.
pose proof (src_loc_fresh HIx _ _ _ _ _ _ _ _ _ LB b n HP2 SRCB ltac:(lia) ltac:(intros sa sk Hsk; right; exact Hsk)) as DISJrs.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in PBS; [| right; right; exists (pb, 16); cbn; split; [left; reflexivity | lia]].
a4l. clear MU WM MI ST PBUF.
rewrite LEN, Z.min_r, Z2Nat.id, firstn_all2 in BLK by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
shadow_nowA A4L HIx HP2 pb 16 SHpb.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 0 pb 16 HP2 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 1 pb 16 HP2 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP1.
a4l.
pose proof (munch_refl [(pb, pb + 16)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
stash SRC2. stash BLK. stash DISJrs. stash DISJbs. stash DISJps. stash Hrimg. stash Hsimg.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
step.
step. step. if_false. rewrite ?sxb_zero.
step. stepz.
step. step. step. if_false. rewrite ?zxb_zero.
step. stepz.
clear SHpb SEP0 SEP1.
unstash SRC2. unstash BLK. unstash DISJrs. unstash DISJbs. unstash DISJps. unstash Hrimg. unstash Hsimg.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (bytes_at_transport asegs _ m2 mc) in SRC2; [| exact MU | cbn [disjoint_from]; simpl_sizes; rewrite ?SRCL; lia];
eapply (rw_cells_transport asegs _ m2 mc) in BLK; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia];
assert (HP3 : HEAPAx A2 ((pb, 16) :: (r, ns) :: LB) LM FRS (charge B (16 * ns + 512) (uw_cost UWptr)) mc md2)
end.
{ eapply (heapA_perm A4L HIx); [ | apply perm_swap | apply Permutation_refl | apply Permutation_refl ].
eapply (heapA_client_frame A4L HIx); [ exact HP2 | | exact WM | exact MI ].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU). solve_frameW_withA HP2. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (UPS3 : 0 < n -> unpoisoned asegs mc A_SB b n) end.
{ intros Hpos. eapply unpoisoned_transport; [exact (UPS2 Hpos) | exact MU |].
intros a k Ha Hk. unfold shadow_span_lo, shadow_span_hi in Ha, Hk. unfold A_SB in Ha, Hk, APB. cbn [disjoint_from]. Z.div_mod_to_equations. lia. }
match goal with FRc : rw_cells asegs ?mc (bv_unsigned sp + -112) (C8 (Z_to_bv 64 b) :: ?rest) |- _ =>
apply (rw_cells_recast_prefix asegs mc _ [C8 (Z_to_bv 64 b)] [CB 8 (le8 (Z_to_bv 64 b))] rest) in FRc; [| split; [apply length_le8 | exact I] | reflexivity | reflexivity] end.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
evt_done5.
eapply (memappend_A_rebase_nf HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb n T buf bpos cap content) with (md := md2) (A := A2) (obuf := buf) (ocap := cap) (buf := r) (bpos := bpos) (cap := ns) (b := b)
(content := content ++ junk) (src := src) (errv := errv2) (fjunk := le8 (Z_to_bv 64 b));
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ =>
unfold pbufx, pbuf_core; split; [lia|]; split; [lia|]; split; [destruct BLK as [[[Hwf _] _] _]; rewrite Hwf; lia|]; split; [eassumption|]; exact BLK
| |- _ -> unpoisoned _ _ _ _ _ => exact UPS3
| |- _ \/ app_mem _ _ => exact AMS
| |- model_vm_only (cfg_model _) (cfg_model _) => eapply model_vm_only_trans; eassumption
| |- heap_pres _ _ _ _ _ =>
eapply heap_pres_trans; [exact HPR|];
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP2 | intros bb Hbb0; right; right; exact Hbb0 | clia | solve_clientWA A4L HIx HP2]
| |- firstn _ _ = firstn _ _ => rewrite firstn_app; replace (Z.to_nat bpos - length content)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r
| |- bB _ - _ <= _ => cbn [bB charge]; rewrite ?memappend_costX2_grow by lia; unfold memappend_costB in *; lia
| |- bD _ - _ <= _ => cbn [bD charge uw_cost]; lia
| |- bD _ <= _ => cbn [bD charge uw_cost]; lia
| |- _ => try (unfold_consts; lia)
end.
Qed.
End APbMemappendGrow.
End RC__1.
