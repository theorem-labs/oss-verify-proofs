(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uu4M.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uihm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uihm. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIsM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UunB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UunB.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UrIB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UrIB.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ShallowP2.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB BS : list blk) (lo p D : Z) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - SH_STK_P.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis SPD : bv_unsigned sp <= D.
Hypothesis DHI : D + 8 <= hi_top S4L HIx.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_rep S4L S4F r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv,
jf_postD S4L D ra sp gp (wz 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) lo rv m' ms' md' ->
jc_glob_P m' -> jroot_rep S4L S4F r m' BS p -> shallow_res S4L HIx S4F r BS LB D m' md' rv ->
realizes rsegs (mkCfg ms' md') T.
Hypothesis NEWO : jo_new_object_P HIx.

Notation sh_inv := (sh_inv ra sp s0 s1 s2 s3 s4 s5 F m0 md0 LB BS lo D).
Notation sh_regs := (sh_regs sp gp s6 s7 s8 s9 s10 s11 p D).

Ltac sh_hyps := try first [ exact Kont | exact JR0 | exact NN | exact DAL | exact DHI | exact SPD | exact RA | exact HT | exact SPA | exact LOS | exact LO ].

#[using="LO LOS SPA HT RA SPD DHI DAL NN JR0 Kont NEWO"] Lemma sh_object :
forall (x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (np tojs pb udel ud : Z) (dold errc : word),
sh_inv mc mdc -> HEAPx A (BS ++ LB) mc mdc -> In (p, np) BS -> 48 <= np ->
rw_cells rsegs mc D [C8 dold] -> rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
rw_cells rsegs mc p (jhdr_cells JT_OBJECT 1 tojs pb udel ud) ->
(forall m' q pbq PBSq t TBS, rw_cells rsegs m' q (jhdr_cells JT_OBJECT 1 tojs pbq 0 0 ++ [C8 (wz t)]) ->
opt_pbuf rsegs m' PBSq pbq -> lhtab2 rsegs S4F m' TBS t [] -> scopy S4L S4F r m' ((q, 48) :: TBS ++ PBSq) q) ->
realizes rsegs (mkCfg (MS (sh_regs x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6)
F (wz 0x26ae0) fc None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until errc. intros INV HP INp Hnp DC ERR SRC SCB. pose proof INV as (VM & PRES & ST & FR & G).
unfold UrIB.Mq0.sh_frame in FR. unfold UrIB.Mq0.sh_regs. unfold SH_STK_P in LOS. unfold_consts. word_range sp SPR.
change (0x77c00 - 164) with 490332 in ERR.
assert (INp1 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p np HP INp1) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
assert (HD0 : 0 < D < 2^64) by (first [pose proof (rw_cells_bound _ _ _ _ DC) as HB | pose proof (rw_cells_bound _ _ _ DC) as HB]; cbn in HB; lia).
unfold jhdr_cells in SRC.
apply (proj1 (rw_cells_app rsegs _ p [_; _] _)) in SRC as X. destruct X as [_ SRC8]. cbn [cells_size csize Nat.add app] in SRC8.
apply (proj1 (rw_cells_app rsegs _ (p + 8) [_] _)) in SRC8 as [SRC8 _]. clear SRC.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
stash G. stash SCB.
apply rz_evt; [exact MOK|].
bstep.
apply evt_RZ_done.
unstash G.
pose proof NEWO as NO. unfold jo_new_object_P, jo_new_container_stmt in NO.
eapply NO with (A := A) (LB := BS ++ LB) (lo := lo) (errv := errc); clear NO.
{ unfold jo_pre. cbn [hl_segs hl_tp S4L]. rewrite !(unsigned_lit (bv_unsigned sp + -64)) by lia.
split; [exact HP|]. split; [exact ST|]. split; [clia|]. split; [lia|].
split; [rewrite <- Zplus_mod_idemp_l, SPA; reflexivity|]. split; [clia|].
split; [exact ERR|]. split; [reflexivity|]. rewrite unsigned_lit by lia. reflexivity. }
{ exact G. }
intros ms2 md2 m2 rq (RS2 & VM2 & ST2 & HPR2 & [e2 ERR2]) OUT.
destruct RS2 as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR2 by lia.
replace (ret_pc (wz 0x26ae4)) with (wz 0x26ae4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
extend_presD_call PRES HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in SRC8; [| eapply client_range_block; [exact INp1 | lia | cbn; lia]]. cbn [hl_segs S4L] in SRC8.
pose proof (jc_glob_P_pres _ _ _ _ HPR2 G) as G2. clear G.
unstash SCB.
destruct OUT as [(-> & A2 & HP2) | (Hr & A2 & OBS & JV & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
apply rz_evt; [exact MOK2|].
step. if_truex. ub_skip.
apply evt_RZ_done.
eapply (sh_join38 HIx) with (ty := JT_OBJECT) (tojs := tojs); sh_hyps;
[ split; [eapply model_vm_only_trans; [exact VM | exact VM2] | split; [exact PRES | split; [exact ST2 | split; [exact FR | exact G2]]]]
| apply fsv8_of_fsaved; exact FS2 | exact FRM2 | exact DC | exact ERR2 | exact SRC8 | left; split; [reflexivity | exists A2; exact HP2] ].
-
destruct JV as (pbq & PBSq & REST & EOBS & OPBq & t & TBS & kvs & KBS & EREST & QHDR & TAB & LK & LKB & _).
destruct kvs as [|kv kvs]; [| cbn in LK; discriminate]. destruct KBS as [|kb KBS]; [| cbn in LKB; discriminate].
cbn [concat] in EREST. rewrite app_nil_r in EREST. subst REST OBS.
cbn [app] in HP2.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_blk S4L HIx _ _ _ _ rq 48 HP2 ltac:(left; reflexivity)) as (_ & Hral & Hrlo & Hrhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi.
unfold jhdr_cells in QHDR. cbn [app] in QHDR.
apply (proj1 (rw_cells_app rsegs _ rq [_; _; _] _)) in QHDR as X. destruct X as [QH QT]. cbn [cells_size csize Nat.add app] in QT.
apply rz_evt; [exact MOK2|].
step. if_truex. ub_skip.
apply evt_RZ_done.
eapply (sh_join38 HIx) with (ty := JT_OBJECT) (tojs := tojs); sh_hyps;
[ split; [eapply model_vm_only_trans; [exact VM | exact VM2] | split; [exact PRES | split; [exact ST2 | split; [exact FR | exact G2]]]]
| apply fsv8_of_fsaved; exact FS2 | exact FRM2 | exact DC | exact ERR2 | exact SRC8 | ].
right. split; [exact Hr|]. exists A2, ((rq, 48) :: TBS ++ PBSq), 48, (fn_obj_to_json_string S4F).
split; [eapply (heap_perm S4L HIx); [exact HP2 | perm] |].
split; [left; reflexivity|]. split; [lia|]. split; [exact QH|].
intros m' QH' MU' WM'.
assert (AGR : agree_on rsegs (TBS ++ PBSq) m2 m').
{ eapply (agree_of_munch rsegs); [exact MU' | exact WM' |].
intros a k Hin.
pose proof (heap_blk S4L HIx _ _ _ _ a k HP2 ltac:(right; apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _).
assert (Har : a <> rq) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ k HP2 ltac:(apply in_or_app; left; exact Hin))).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k rq 48 HP2 ltac:(right; apply in_or_app; left; exact Hin) ltac:(left; reflexivity) Har) as Hdj.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi. cbn. lia. }
eapply (SCB m' rq pbq PBSq t TBS).
+ unfold jhdr_cells. cbn [app].
apply (proj2 (rw_cells_app rsegs m' rq [_; _; _] _)). split; [exact QH'|]. cbn [cells_size csize Nat.add app].
eapply (rw_cells_transport rsegs); [exact QT | exact MU' | exact WM' |]. cbn. lia.
+ eapply opt_pbuf_agree; [exact OPBq | exact AGR | intros b Hb; apply in_or_app; right; exact Hb].
+ eapply (lhtab2_agree rsegs S4F); [exact TAB | exact AGR | intros b Hb; apply in_or_app; left; exact Hb].
Qed.

#[using="LO LOS SPA HT RA SPD DHI DAL NN JR0 Kont"] Lemma sh_array :
forall (x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (np tojs pb udel ud : Z) (dold errc : word),
sh_inv mc mdc -> HEAPx A (BS ++ LB) mc mdc -> In (p, np) BS -> 48 <= np ->
rw_cells rsegs mc D [C8 dold] -> rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
rw_cells rsegs mc p (jhdr_cells JT_ARRAY 1 tojs pb udel ud) ->
(forall m' q a ABS, rw_cells rsegs m' q (jhdr_cells JT_ARRAY 1 tojs 0 0 0 ++ [C8 (wz a)]) ->
alist rsegs S4F m' ABS a [] -> scopy S4L S4F r m' ((q, 48) :: ABS) q) ->
realizes rsegs (mkCfg (MS (sh_regs x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6)
F (wz 0x26a14) fc None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until errc. intros INV HP INp Hnp DC ERR SRC SCB. pose proof INV as (VM & PRES & ST & FR & G).
unfold UrIB.Mq0.sh_frame in FR. unfold UrIB.Mq0.sh_regs. unfold SH_STK_P in LOS. unfold_consts. word_range sp SPR.
change (0x77c00 - 164) with 490332 in ERR.
assert (INp1 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p np HP INp1) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p np HP INp1) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
unfold jhdr_cells in SRC.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] mc) as MU.
stash G. stash SCB.
apply rz_evt; [exact MOK|].
bstep. bstep.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR2 by lia.
extend_presD S4L HIx PRES MU WM HP. extend_presD_call PRES HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in SRC; [| eapply client_range_block; [exact INp1 | lia | cbn; lia]]. cbn [hl_segs S4L] in SRC.
unstash G. pose proof (jc_glob_P_pres _ _ _ _ HPR2 (jc_glob_P_munch _ _ _ G MU WM ltac:(repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia))) as G2. clear G.
clear MU WM MI ST.
apply (proj1 (rw_cells_app rsegs _ p [_; _] _)) in SRC as X. destruct X as [_ SRC8]. cbn [cells_size csize Nat.add app] in SRC8.
apply (proj1 (rw_cells_app rsegs _ (p + 8) [_] _)) in SRC8 as [SRC8 _]. clear SRC.
destruct OUT2 as [(-> & _ & HP2) | (Hq & [junk0 BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2.
bstep. if_true.
apply evt_RZ_done.
eapply (sh_join HIx) with (ty := JT_ARRAY) (tojs := tojs); sh_hyps;
[ split; [eapply model_vm_only_trans; [exact VM | exact VM2] | split; [exact PRES | split; [exact ST2 | split; [exact FR | exact G2]]]]
| apply fsv8_refl | intros Hf; exact Hf | exact DC | exact ERR2 | exact SRC8 | left; split; [reflexivity | exists A2; exact HP2] ].
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ q 48 HP2 ltac:(left; reflexivity)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q 48 HP2 ltac:(left; reflexivity)) as Hqimg. cbn [hl_img_lo hl_img_hi S4L] in Hqimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
assert (Hqp : q <> p) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ np HP2 INp1)).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q 48 p np HP2 ltac:(left; reflexivity) ltac:(right; exact INp1) Hqp) as Hdqp.
pose proof (munch_refl [(q, q + 48)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
stash G2.
reenter MOK2.
bstep. if_falsex.
do 5 bstep. bstepz. bstepz. bstepz. bstepz. bstepz.
do 5 bstep. bstep.
unstash G2.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (G3 : jc_glob_P mx) by
(eapply jc_glob_P_outside; [exact G2 | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia);
assert (HP3 : HEAPx A2 ((q, 48) :: BS ++ LB) mx md2) by heap_now S4L HIx HP2 MU WM MI
end.
extend_presD S4L HIx PRES MU WM HP2.
apply evt_RZ_done.
eapply (array_list_new2_cps HIx) with (LB := (q, 48) :: BS ++ LB) (lo := lo) (isz := 32);
[ exact HP3 | .. ]; try alloc_side.
intros ms3 md3 (m3 & A3 & al & e3 & RS3 & VM3 & ST3 & HPR3 & ERR3 & OUT3).
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR3 by lia.
extend_presD_call PRES HPR3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in SRC8; [| eapply client_range_block; [right; exact INp1 | lia | cbn; lia]]. cbn [hl_segs S4L] in SRC8.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
pose proof (jc_glob_P_pres _ _ _ _ HPR3 G3) as G4.
clear MU WM MI G2 G3.
destruct OUT3 as [(-> & HP4) | (Hal & ABS & AL & HP4)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(q, q + 48)] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
stash G4.
reenter MOK4.
bstep. bstep. bstepz. bstep. if_false. bstep.
unstash G4.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HP5 : HEAPx A3 ((q, 48) :: BS ++ LB) mx md3) by heap_now S4L HIx HP4 MU WM MI;
assert (G5 : jc_glob_P mx) by
(eapply jc_glob_P_outside; [exact G4 | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia)
end.
extend_presD S4L HIx PRES MU WM HP4.
clear BLK MU WM.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (munch_refl [] mx) as MU; pose proof (wmono_refl rsegs mx) as WM end.

alloc_call (hi_free S4L HIx) S4L HIx HP5 MU WM MI.
{ right. exists 48. left. reflexivity. }
intros ms7 m7 md7 A7 r7 RS7 VM7 ST7 HPR7 ERR7 HP7. open_ret RS7. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR7, HP7.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST7 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR7 by lia.
extend_presD_call PRES HPR7.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR7) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR7) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR7) in SRC8; [| eapply client_range_block; [exact INp1 | lia | cbn; lia]]. cbn [hl_segs S4L] in SRC8.
pose proof (jc_glob_P_pres _ _ _ _ HPR7 G5) as G7.
clear MU WM MI HP5 G5.
pose proof (heap_model_ok _ _ _ _ _ _ HP7) as MOK7.
pose proof (heap_mem_inv _ _ _ _ _ _ HP7) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m7) as MU. pose proof (wmono_refl rsegs m7) as WM.
reenter MOK7.
bstep. bstep.
unstash SCB.
apply evt_RZ_done.
eapply (sh_join HIx) with (ty := JT_ARRAY) (tojs := tojs); sh_hyps;
[ split; [| split; [exact PRES | split; [exact ST7 | split; [exact FR | exact G7]]]]
| apply fsv8_of_fsaved; exact FS3 | exact FRM3 | exact DC | exact ERR7 | exact SRC8 | left; split; [reflexivity | exists A7; exact HP7] ].
eapply model_vm_only_trans; [exact VM|]. eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3 | exact VM7].
+
pose proof AL as (arr & size & ajunk & EBS & Hlen & Hsz & AHDR & AARR). subst ABS. cbn [app] in HP4.
pose proof (rw_cells_bound rsegs m3 al _ AHDR) as R2B. cbn [cells_size csize Nat.add] in R2B.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk_img S4L HIx _ _ _ _ al 32 HP4 ltac:(left; reflexivity)) as Himg_al. cbn [hl_img_lo hl_img_hi S4L] in Himg_al.
pose proof (heap_blk_img S4L HIx _ _ _ _ arr (8 * size) HP4 ltac:(right; left; reflexivity)) as Himg_arr. cbn [hl_img_lo hl_img_hi S4L] in Himg_arr.
pose proof (heap_blk S4L HIx _ _ _ _ al 32 HP4 ltac:(left; reflexivity)) as (_ & Halal & Hallo & Halhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ arr (8 * size) HP4 ltac:(right; left; reflexivity)) as (_ & Haal & Halo & Hahi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Halhi, Hahi.
assert (Halq : al <> q) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ 48 HP4 ltac:(right; left; reflexivity))).
assert (Harrq : arr <> q).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP4) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x' l' Hni' Hnd']; subst. apply Hni'. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ al 32 q 48 HP4 ltac:(left; reflexivity) ltac:(right; right; left; reflexivity) Halq) as Hdj1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ arr (8 * size) q 48 HP4 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) Harrq) as Hdj2.
clear AHDR AARR. stash AL. stash G4.
pose proof (munch_refl [(q, q + 48)] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
reenter MOK4.
bstep. bstep. bstep. bstep. if_truex.
unstash AL. unstash G4. unstash SCB.
apply evt_RZ_done.
jhdr_split BLK.
apply (proj1 (rw_cells_app rsegs _ q [_; _; _] _)) in BLK as X. destruct X as [QH QT]. cbn [cells_size csize Nat.add app] in QT.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
assert (HP5 : HEAPx A3 ((al, 32) :: (arr, 8 * size) :: (q, 48) :: BS ++ LB) mx md3) by heap_now S4L HIx HP4 MU WM MI;
assert (G5 : jc_glob_P mx) by
(eapply jc_glob_P_outside; [exact G4 | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; (clear - Hqimg; lia))
end.
extend_presD S4L HIx PRES MU WM HP4.
eapply (sh_join HIx) with (ty := JT_ARRAY) (tojs := tojs); sh_hyps;
[ split; [| split; [exact PRES | split; [exact ST3 | split; [exact FR | exact G5]]]]
| apply fsv8_of_fsaved; exact FS3 | exact FRM3 | exact DC | exact ERR3 | exact SRC8 | ].
{ eapply model_vm_only_trans; [exact VM|]. eapply model_vm_only_trans; [exact VM2 | exact VM3]. }
right. split; [exact Hq|]. exists A3, [(q, 48); (al, 32); (arr, 8 * size)], 48, (fn_arr_to_json_string S4F).
split; [eapply (heap_perm S4L HIx); [exact HP5 | perm] |].
split; [left; reflexivity|]. split; [lia|]. split; [exact QH|].
intros m' QH' MU' WM'. eapply (SCB m' q al).
* unfold jhdr_cells. cbn [app].
apply (proj2 (rw_cells_app rsegs m' q [_; _; _] _)). split; [exact QH'|]. cbn [cells_size csize Nat.add app].
eapply (rw_cells_transport rsegs); [exact QT | exact MU' | exact WM' |]. cbn. lia.
* eapply (alist_agree rsegs S4F); [exact AL | | apply incl_refl].
eapply agree_on_trans.
-- eapply (agree_of_munch rsegs); [exact MU | exact WM |].
intros b k Hb. cbn in Hb. cbn. destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia.
-- eapply (agree_of_munch rsegs); [exact MU' | exact WM' |].
intros b k Hb. cbn in Hb. cbn. destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; (clear - LO LOS SPD Halhi Hdj1 Hahi Hdj2; lia).
Qed.

End ShallowP2.

End RC__1.
