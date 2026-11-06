(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCfx YChv YChx YChi YChn YChg YCf6 YCft YCi1 YCie YCph YCrr YCrd YCrc YCrn YCr3 YCr9 YCr7 YCr4 YCr5 YCr2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o YG0t YG0r YG0q YC00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 250.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac nat_side := first [ apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (Nat.eqb_neq _ _)); vm_compute; reflexivity
| cbn [length Nat.add]; apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity ].
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Ltac add_u16 HS AG Fv K off HFp EK v Rv :=
lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict (w_H ?Wx) ?msv) =>
let Vv := fresh "Vv" in let HS3 := fresh "HS3" in
destruct (rtb_val_mem_byte2 (w_H Wx) (ms_mem msv) (Fv + off) (proj1 (HFp (Fv + off) ltac:(clear; lia))) (proj1 (HFp (Fv + off + 1) ltac:(clear; lia)))) as (v & Rv & Vv);
pose proof (st_ok_havoc_win trbsegs K Ev ssv (restrict (w_H Wx) msv) [Z_to_bv 64 v] HS ltac:(vm_compute; reflexivity)) as HS3;
assert (EK : ew (havoc Ev K [Z_to_bv 64 v]) K = Z_to_bv 64 v) by (exact (ew_havoc_new _ K [Z_to_bv 64 v] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
clear HS; rename HS3 into HS;
lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msx2 =>
pose proof (st_ok_add_fact trbsegs Ev2 ssx2 msx2 K (mkAF 0 65535 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK; rewrite unsigned_lit_small by (clear - Rv; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rv; lia)) as HS3;
clear HS; rename HS3 into HS end;
lazymatch type of HS with st_ok _ ?Ev2 _ _ =>
pose proof (ast_ok_add_region trbsegs Ev2 _ _ (YQ0b.mkRegion (Some 75%nat) off (off + 2) 0 0 [YQ0b.mkChunk off (CVal 2 (SOff K 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
evalE AG; split; [lia|]; split; [lia|]; split;
[ intros o Ho; exfalso; clear - Ho; lia
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trbsegs Ev2 _ Fv off 2 (SOff K 0) v); [rewrite sv_denot_SOff0; exact EK | clear - Rv; cbn; lia | clear; cbn; lia | exact Vv] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
unfold SB in *; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end end.
Lemma rt_D_aux : rt_from B ss_X (INV_X B) -> rt_from B ss_E (INV_E B) -> rt_from B ss_D (INV_Bn B 520).
Proof.
intros RX RE. rt_prelude.
destruct HINV as ((Hk0 & Eab3 & curi & Ecur & Hcuri) & r1 & E360 & Hr1v). cbn [c_ly c_S c_n] in Eab3, Hcuri, Hr1v.
relowRT HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK RTBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK RTBspan.
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => clear Hb end.
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RTBspan 0x814f4.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
clear_frames.
ra_join_win HS ss_X 2000%nat rt_X_deads_bv ltac:(idtac).
rt_hand RX HS.
split; [cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0]; lazymatch goal with |- rbv ?Sx ?S3x _ _ => match goal with HJx : ajournal _ _ _ _ _ _ Sx _ _ _ _ _ S3x _ _ _ _ |- _ => apply (rt_bv_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx) end end; [clear - Hk0; unfold RGB_COARSE; lia | clear; lia]|].
split; [assert (0 <= EV_RLIB) by (vm_compute; discriminate); clear - Hk0 H; lia | cbn [c_ly c_S]; rewrite Eab3; apply Permutation_refl].
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
hc_bool Hc ltac:(fun H => idtac). hc_prop Hc.
destruct (U_or_zero _ _ _ Hc) as [Hc1 _]. destruct (U_or_zero _ _ _ Hc1) as [Hc2 _]. destruct (U_or_zero _ _ _ Hc2) as [_ Hc3].
assert (Hr10 : r1 = 0) by (rewrite (U_atom E 360 r1 E360) in Hc3 by (clear - Hr1v; lia); exact Hc3).
assert (Hn2 : 2 <= n) by (apply (proj2 Hr1v); exact Hr10).
clear Hc Hc1 Hc2 Hc3 Hr10.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ3) Hfin3) as (_ & _ & HFpN & _). change (fs_frame_bytes 2) with 256 in HFpN. rewrite !EFA3 in HFpN. fold F in HFpN.
norm_ss HS.
add_u16 HS AG F 540%nat 66 HFpN E540 Wd RWd. rebaseE HS AG HEv; clear HEv.
add_u16 HS AG F 541%nat 68 HFpN E541 Hd RHd. rebaseE HS AG HEv; clear HEv.
clear HFpN.
relowRT HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK RTBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK RTBspan.
+
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => clear Hb end.
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RTBspan 0x814f4.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
clear_frames.
ra_join_win HS ss_X 2000%nat rt_X_deads_bv ltac:(idtac).
rt_hand RX HS.
split; [cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0]; lazymatch goal with |- rbv ?Sx ?S3x _ _ => match goal with HJx : ajournal _ _ _ _ _ _ Sx _ _ _ _ _ S3x _ _ _ _ |- _ => apply (rt_bv_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx) end end; [clear - Hk0; unfold RGB_COARSE; lia | clear; lia]|].
split; [assert (0 <= EV_RLIB) by (vm_compute; discriminate); clear - Hk0 H; lia | cbn [c_ly c_S]; rewrite Eab3; apply Permutation_refl].
+ lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
hc_bool Hc ltac:(fun H => idtac). hc_prop Hc.
lazymatch type of Hc with U ?Ex (SMd M_MUL ?eH ?eW) <= _ =>
assert (HN : U Ex (SMd M_MUL eH eW) = Wd * Hd)
by (rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom Ex 541 Hd E541), (U_atom Ex 540 Wd E540) by (clear - RWd RHd; lia);
rewrite zcanon_id by (unfold M64; clear - RWd RHd; nia); clear; lia);
assert (DN : sv_denot Ex (SMd M_MUL eH eW) = Z_to_bv 64 (Wd * Hd)) by (rewrite denot_lit_U, HN; reflexivity);
rewrite HN in Hc; clear HN end.
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RTBspan 0x81484.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
clear_frames.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
let e := eval vm_compute in (sr_get (ss_regs ssx) (20%bv : bv 5)) in
assert (DN2 : sv_denot Ex e = Z_to_bv 64 (Wd * Hd)) by (first [exact DN | rewrite !denot_havoc_below by (vm_compute; reflexivity); exact DN]);
rreg_by HS (20%bv : bv 5) (Z_to_bv 64 (Wd * Hd)) DN2 R20 end.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) [20%bv : bv 5]) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc_win trbsegs 542 Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
assert (E542 : ew (havoc Ex 542 vals') 542 = Z_to_bv 64 (Wd * Hd))
by (rewrite (ew_havoc_new _ 542 vals' 0 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; cbn [ms_regs restrict] in R20; exact R20);
clear HS; rename HS3 into HS;
set_regs_rec HS 542%nat vals' 0%nat [20%bv : bv 5] end.
rebaseE HS AG HEv; clear HEv.
rt_hand RE HS.
split; [exact Hk0|]. split; [cbn [c_ly c_S]; exact Eab3|]. split; [cbn [c_n]; exact Hn2|].
split; [exists curi; cbn [c_n]; split; [exact Ecur | exact Hcuri]|].
exists Wd, Hd.
split; [exact E540|]. split; [exact E541|]. split; [exact E542|].
split; [clear - RWd; lia|]. split; [clear - RHd; lia|]. exact Hc.
Qed.
Lemma rt_D : rt_from B ss_X (INV_X B) -> rt_from B ss_E (INV_E B) -> rt_from B ss_D (INV_Bn B 520).
Proof. exact rt_D_aux. Qed.
End b.
End a.
