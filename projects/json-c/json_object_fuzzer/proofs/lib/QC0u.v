(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTEu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTEu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qr5P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qr5P. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QW22.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qmgs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qmgs.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MNewObjOk.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Ltac asan_chkA_tail :=
step; sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end;
step; step; first [ if_false | if_true ]; rewrite ?sxb_zero, ?zxb_zero.

Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Hypothesis OBL_RTC_LHEQ : rtc_lheq_stmt HIx.

Definition newobj_costB : Z := (16 * 48 + 512) + ((16 * (1 * 56) + 512) + (16 * (16 * 40) + 512) + 512) + 1024 + 512.
Definition newobj_okB : Z := (16 * 48 + 512) + ((16 * (1 * 56) + 512) + (16 * (16 * 40) + 512) + 512).

Definition new_objc_A3ok_post (u : uwd) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
lh_globA m' /\
bB B - newobj_costB <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ bB B - newobj_okB <= bB B' /\ exists BS, jval asegs A4F (Sobj []) m' BS r 1 /\ length BS = 3%nat /\ obj_capA BS = 16 /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md') ).

Definition jo_new_object_A3ok_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FRS B m md ->
lh_globA m ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d38c) u ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 48 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
newobj_costB <= bB B -> uw_cost u <= bD B ->
(forall ms' md' A', new_objc_A3ok_post u ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_object_A_entry) fc None m (seg_rom asegs)).

Lemma json_object_new_object_A3ok_cps : jo_new_object_A3ok_stmt.
Proof.
unfold jo_new_object_A3ok_stmt.
intros until u. intros HP G UW UWK ST LO LOS SPA HT ERR TP RA BB BD K. pose proof OBL_AMEMSET as OBL_unused_on_B.
unfold_consts. unfold newobj_costB in BB. word_range sp SPR.
pose proof G as G0. destruct G as (G1 & [seed G2]). unfold GHASHA in G1. unfold GSEEDA in G2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
subst tp. a4l. reenterA asegs A4L HIx asegs_wx HP. unfold json_object_new_object_A_entry, A_ERRNO in *. a4l.
carve_frame 48%nat ST.
do 6 bstep.
do 3 bstep.
bstep. bstep.

alloc_callA (hiA_malloc A4L HIx) uw u A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (solve [eapply (uw_at_pre _ _ _ _ _ _ _ _ UW MU); [repeat apply Forall_cons; cbn; try apply Forall_nil; lia | lia]]).
all: try (solve [exact UWK]).
all: try (solve [destruct u; cbn [uw_cost bD charge] in *; lia]).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in G1; [| right; left; intros z Hz; cbn in Hz; cbn; unfold a4_client_static; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in G2; [| right; left; intros z Hz; cbn in Hz; cbn; unfold a4_client_static; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_true. do 9 bstep.
evt_done5. apply K. unfold new_objc_A3ok_post.
exists m2, 0, e2, (charge B (16 * 48 + 512) (uw_cost u)).
split; [apply ret_statew_same|]. split; [exact VM2|]. split; [release_frame FR ST2 (bv_unsigned sp); exact ST2|].
split; [exact HPR|]. split; [exact ERR2|].
split; [eapply lh_globA_frame; [eapply lh_globA_client; [exact HPR | exact G0] | exact MU | exact WM | unfold GHASHA, GSEEDA; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia]|].
split; [unfold newobj_costB; cbn [bB charge]; lia|]. split; [cbn [bD charge uw_cost]; destruct u; cbn [uw_cost] in *; lia|]. left; auto.
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 r 48 Hal Hlo Hhi Himg_r.
shadow_nowA A4L HIx HP2 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 0 r 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 48); (lo, bv_unsigned sp - 48)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_falsex. bstep.
asan_chkA.
bstep. bstep. bstepz.
asan_chkA.
bstep. bstep. bstepz.
asan_chkA.
bstep. bstep. bstep.
bstep.
bstepz.
asan_chkA_tail. bstepz.
bstep. asan_chkA. bstepz.
bstep. asan_chkA. bstepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with BLKc : rw_cells asegs mc r [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7] |- _ =>
change [c1; c2; c3; c4; c5; c6; c7] with ([c1; c2; c3] ++ ([c4; c5; c6] ++ [c7])) in BLKc;
destruct (proj1 (rw_cells_app asegs mc r _ _) BLKc) as [HDR REST]; clear BLKc;
cbn [cells_size csize Nat.add] in REST; replace (r + Z.of_nat 16) with (r + 16) in REST by lia;
destruct (proj1 (rw_cells_app asegs mc (r + 16) _ _) REST) as [DST4 TL]; clear REST;
cbn [cells_size csize Nat.add] in TL; replace (r + 16 + Z.of_nat 24) with (r + 40) in TL by lia;
try (apply (rw_cells_recast asegs mc (r + 16) _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in DST4;
[| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity])
end end.
do 4 bstep.

evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with MIc : mem_inv asegs mc |- _ =>
eapply (lh_kchar_table_new_A3_cps HIx OBL_RTC_LHEQ) with (LB := (r, 48) :: LB) (lo := lo) (u := UWptr);
[ heap_nowA A4L HIx HP2 MU WM MIc | split; [exact G1 | exists seed; exact G2] | .. ] end end;
a4l_goal; rewrite ?unsigned_lit by lia; try first [eassumption | reflexivity].
all: try (solve [apply uw_at_ptr; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [rewrite <- Zplus_mod_idemp_l, SPA; reflexivity]).
all: try (solve [unfold lhnew_costB; cbn [bB charge]; lia]).
all: try (solve [cbn [bD charge uw_cost]; destruct u; cbn [uw_cost] in *; lia]).
all: try (solve [lia]).
intros ms3 md3 A3 (mB & t & e3 & B3 & RS3 & VM3 & ST3 & HPR3 & ERR3 & G3 & BB3 & BD3 & OUT3).
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3). a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR3 by lia.
unfold lhnew_costB in BB3. cbn [bB bD charge uw_cost] in BB3, BD3.
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in HDR; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in DST4; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in TL; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. a4l.
clear MU WM SHr SEP0 SEP5.
try clear MI.
destruct OUT3 as [(-> & HP3) | (Ht & BS2 & TAB & (tq & EBSq) & HP3)].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
shadow_nowA A4L HIx HP3 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 2 r 48 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP2.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 48)] mB) as MU. pose proof (wmono_refl asegs mB) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
bstep. asan_chkA. bstepz.
bstep. if_falsex.
bstep. bstep. first [ if_false | if_true ]. rewrite ?sxb_zero, ?zxb_zero.
bstep. bstep.
evt_done5.
eapply (printbuf_free_A_cps HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md3 T A3 ((r, 48) :: LB) LM [] FRS B3 0 lo e3 UWpaid);
[ cbn [app]; heap_nowA A4L HIx HP3 MU WM MI | intros X0; exfalso; apply X0; reflexivity | intros X0; exfalso; apply X0; reflexivity | left; split; reflexivity | .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [eassumption | reflexivity | exact I].
all: try (solve [rewrite <- Zplus_mod_idemp_l, SPA; reflexivity]).
all: try (solve [cbn [bB bD charge uw_cost length Z.of_nat Z.eqb Z.mul] in *; destruct u; cbn [uw_cost] in *; lia]).
all: try (solve [lia]).
intros ms5 md5 A5 (mC & r5 & B5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & BB5 & BD5 & HP5). cbn in BB5, BD5.
destruct RS5 as (x0 & x1' & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & F5 & fc5 & -> & FS5 & FRM5). a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST5 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR5 by lia.
extend_presA A4L HIx HPR MU WM HP3 HPR5.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI HDR DST4 TL SHr SEP2 SEP5.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] mC) as MU. pose proof (wmono_refl asegs mC) as WM.
reenterA asegs A4L HIx asegs_wx HP5.
bstep. bstep.
alloc_callA (hiA_free A4L HIx) blk r uw UWptr A4L HIx HP5 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 48. left. reflexivity. }
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec r 0); cbn [bB bD charge uw_cost] in *; destruct u; cbn [uw_cost] in *; lia).
intros ms6 mD md6 A6 r6 RS6 VM6 ST6 HPR6 ERR6 HP6. open_ret RS6. a4l.
rewrite lb_remove_head in HPR6, HP6.
replace (if r =? 0 then 0 else uw_cost UWptr) with 0 in HP6 by (destruct (r =? 0); reflexivity).
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST6 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR6 by lia.
extend_presA A4L HIx HPR MU WM HP5 HPR6.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP6) as MI.
pose proof (errno_shadowA HIx _ _ _ _ _ _ _ HP6) as ESH. a4l. change ((6444320 - 164) / 8 + 2147450880) with 2148256399 in ESH.
change (6444320 - 164) with 6444156 in ERR6.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (6444156, 6444160)] mD) as MU. pose proof (wmono_refl asegs mD) as WM.
reenterA asegs A4L HIx asegs_wx HP6.
bstep.
bstep. bstep. bstep.
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
bstep. bstep. bstep. rewrite ?sxb_zero, ?zxb_zero. bstep. if_false.
bstep. bstep. bstepz. bstep.
do 8 bstep.
evt_done5. apply K. unfold new_objc_A3ok_post.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf (seg_rom _)] => exists mf, 0, (Z_to_bv 64 12), (charge B5 512 0) end.
split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| left; split; [reflexivity|]]]]]]]]].
* apply ret_statew_intro; [eapply fsaved_trans; [exact FS3 | exact FS5] | intros Hf; apply FRM5; apply FRM3; exact Hf].
* eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3|]. eapply model_vm_only_trans; [exact VM5 | exact VM6].
* lazymatch goal with STx : stk asegs ?mf _ _ |- stk asegs ?mf _ _ => release_frame FR STx (bv_unsigned sp); exact STx end.
* eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP6 | intros bb Hbb; exact Hbb | clia |].
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
[ left; split; clia | right; right; intros; cbn [hl_scratch hla_base A4L A4H]; unfold A_TP; lia ].
* unfold A_ERRNO, A_TP. match goal with H : rw_cells asegs ?mf 6444156 _ |- rw_cells asegs ?mf _ _ => exact H end.
* eapply lh_globA_frame; [eapply lh_globA_client; [exact HPR | exact G0] | exact MU | exact WM |].
unfold GHASHA, GSEEDA. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
* unfold newobj_costB. cbn [bB charge]. lia.
* cbn [bD charge uw_cost] in *. destruct u; cbn [uw_cost] in *; lia.
* eapply (heapA_client_frame A4L HIx); [exact HP6 | | exact WM | match goal with H : mem_inv asegs ?mf |- mem_inv _ ?mf => exact H end].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP6 MU).
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
[ left; split; clia | right; right; intros; cbn [hl_scratch hla_base A4L A4H]; unfold A_TP; lia ].
+
pose proof TAB as (tbl & size & es & svs & Hkvs & EBS2 & OPEN).
destruct es as [|e0 es']; [| cbn in Hkvs; discriminate].
assert (Esz : size = 16) by (pose proof EBS2 as E2; rewrite EBSq in E2; unfold lh_blocks in E2; cbn [map app] in E2; injection E2 as E40; lia).
clear EBSq. subst BS2. unfold lh_blocks in HP3. cbn [map app] in HP3.
pose proof (proj1 OPEN) as THDR. unfold lh_hdrf in THDR.
pose proof (rw_cells_bound asegs mB t _ THDR) as R2B. cbn [cells_size csize Nat.add] in R2B. clear THDR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
blk_factsA A4L HIx HP3 t 56 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP3 tbl (40 * size) Hbal Hblo Hbhi Himg_b.
assert (Htr : t <> r) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ 48 HP3 ltac:(apply in_or_app; left; right; left; reflexivity))).
assert (Hbr : tbl <> r).
{ intros ->. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x' l' Hni' Hnd']; subst. apply Hni'. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ t 56 r 48 HP3 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; right; left; reflexivity) Htr) as Hdj1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tbl (40 * size) r 48 HP3 ltac:(apply in_or_app; left; right; left; reflexivity) ltac:(apply in_or_app; left; right; right; left; reflexivity) Hbr) as Hdj2.
shadow_nowA A4L HIx HP3 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP3 ltac:(right; right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; right; left; reflexivity)) as SEP5.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 t 56 HP3 ltac:(right; right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5t.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 tbl (40 * size) HP3 ltac:(right; right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP5b.
a4l.
stash TAB. clear OPEN.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 48)] mB) as MU. pose proof (wmono_refl asegs mB) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
bstep. asan_chkA. bstepz.
bstep. if_truex.
do 8 bstep.
unstash TAB.
evt_done5. apply K. unfold new_objc_A3ok_post.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf (seg_rom _)] => exists mf, r, e3, B3 end.
split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| right; split; [exact Hr | split; [unfold newobj_okB; lia |]]]]]]]]]].
* apply ret_statew_intro; [exact FS3 | exact FRM3].
* eapply model_vm_only_trans; [exact VM2 | exact VM3].
* lazymatch goal with STx : stk asegs ?mf _ _ |- stk asegs ?mf _ _ => release_frame FR STx (bv_unsigned sp); exact STx end.
* eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP3 | intros b Hb; in_tailA Hb | clia | solve_clientWA A4L HIx HP3].
* match goal with H : rw_cells asegs ?mf (6444320 - 164) _ |- rw_cells asegs ?mf _ _ => exact H end.
* eapply lh_globA_frame; [eapply lh_globA_client; [exact HPR | exact G0] | exact MU | exact WM |].
unfold GHASHA, GSEEDA. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
* unfold newobj_costB. lia.
* cbn [bD charge uw_cost] in *. destruct u; cbn [uw_cost] in *; lia.
* exists [(r, 48); (t, 56); (tbl, 40 * size)]. split; [| split; [reflexivity | split; [unfold obj_capA; cbn [nth snd]; rewrite Esz; reflexivity |]]].
-- eapply (sobj_close asegs A4F) with (TBS := [(t, 56); (tbl, 40 * size)]) (KBS := []) (PBS := []) (pb := 0) (kvs := []) (t := t); try reflexivity.
++ left. split; reflexivity.
++ unfold jhdr_cells. cbn [fn_obj_to_json_string A4F app].
lazymatch goal with |- rw_cells _ ?mf _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7] =>
change [c1; c2; c3; c4; c5; c6; c7] with ([c1; c2; c3] ++ ([c4; c5; c6] ++ [c7]));
apply (proj2 (rw_cells_app asegs mf r _ _)); cbn [cells_size csize Nat.add];
split; [ match goal with H : rw_cells asegs mf r _ |- _ => exact H end |];
replace (r + Z.of_nat 16) with (r + 16) by lia;
apply (proj2 (rw_cells_app asegs mf (r + 16) _ _)); cbn [cells_size csize Nat.add];
replace (r + 16 + Z.of_nat 24) with (r + 40) by lia;
split; [ match goal with H : rw_cells asegs mf (r + 16) _ |- _ => exact H end
| match goal with H : rw_cells asegs mf (r + 40) _ |- _ => exact H end ] end.
++ eapply (lhtab2_agree asegs A4F); [exact TAB | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros b k Hb. cbn in Hb. cbn. destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia.
-- cbn [app]. eapply (heapA_perm A4L HIx); [| | apply Permutation_refl | apply Permutation_refl].
++ eapply (heapA_client_frame A4L HIx); [exact HP3 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP3 MU); solve_frameW_withA HP3 | exact WM | ].
match goal with H : mem_inv asegs ?mf |- mem_inv _ ?mf => exact H end.
++ perm.
Qed.
End MNewObjOk.
End RC__1.
