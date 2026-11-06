(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx
YCi1 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCpk YCpl YCq8 YCqb
YClx YCm2.
Ltac rga_E_tac HEE0 := repeat first [apply rga_E_havoc; [lia|] | apply rga_E_ewset; [lia|]]; exact HEE0.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_B1 : rga_fromFA B ss_EPI (fun _ => INV_X B) -> rga_fromA B ss_E1b (fun _ => INV_0 B 0) -> rga_from B ss_E1 (INV_0 B 0).
Proof.
intros RX RC. rga_prelude.
destruct HINV as (Hk0 & Eab3 & Hbb3).
destruct Hk0 as [Hk0 Hbud].
pose proof Hrgb as Hrgb'. cbn [obj_at LAY_Rgb] in Hrgb'.
destruct Hrgb' as ([_ R0v] & [_ R8v] & [_ R16v] & [_ R24v] & [_ R32v] & [_ R36v] & [_ R40v] & [_ R42v] & [_ R44v] & [_ R48v] & [_ R56v] & [_ R60v] & _).
cbn [fst snd N.to_nat Z.of_N] in R0v, R8v, R16v, R24v, R32v, R36v, R40v, R42v, R44v, R48v, R56v, R60v.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hrin).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK GBspan.
all: try (unfold GBx; ga_obl_blk HJ3 E10n E44 Hrin3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
-
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x820f8.
all: try (unfold GBx; ga_obl_blk HJ3 E10n E44 Hrin3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
ga_join HS ss_E1b 200%nat (@nil (bv 5)) ltac:(idtac).
rga_hand RC HS HJ3 k; [rga_E_tac HEE0 | split; [split; [exact Hk0 | rga_bud_tac Hbud]|]; split; [exact Eab3 | exact Hbb3]].
- aj_run_tok trbtbl_lib_ok HS HJ3 SHOK GBspan.
all: try (unfold GBx; ga_obl_blk HJ3 E10n E44 Hrin3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
+
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x820f8.
all: try (unfold GBx; ga_obl_blk HJ3 E10n E44 Hrin3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
ga_join HS ss_E1b 200%nat (@nil (bv 5)) ltac:(idtac).
rga_hand RC HS HJ3 k; [rga_E_tac HEE0 | split; [split; [exact Hk0 | rga_bud_tac Hbud]|]; split; [exact Eab3 | exact Hbb3]].
+
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x84428.
all: try (unfold GBx; ga_obl_blk HJ3 E10n E44 Hrin3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (HEEv : rga_E (mkRGCX ly S W regs mem md ch r cfp g wfn ctx path attr gen loops Wd Hd bef beffmt cur s N img fmt fattr fgen delay rest cid pos fpos E0) Ex)
by (rga_E_tac HEE0);
let rs := eval vm_compute in (ss_mem ssx) in
let idx := ga_idx_of_base rs 10%nat in let idx := eval vm_compute in idx in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) idx _ HS eq_refl) as HRr; cbn [ms_mem restrict] in HRr;
assert (Hobj : obj_at trbsegs (mrestrict (w_H W3) (ms_mem msX)) r LAY_Rgb ([g; wfn; ctx; path; attr; gen; loops; Wd; Hd; bef; beffmt] ++ [cur]))
end.
{ destruct HEEv as (AGv & EXv & _). unfold rgc_vals in EXv. rga_cbn_cx EXv. rga_cbn_cx AGv.
pose proof (EXv 0%nat ltac:(lia)) as X0.
pose proof (EXv 1%nat ltac:(lia)) as X1.
pose proof (EXv 2%nat ltac:(lia)) as X2.
pose proof (EXv 3%nat ltac:(lia)) as X3.
pose proof (EXv 4%nat ltac:(lia)) as X4.
pose proof (EXv 5%nat ltac:(lia)) as X5.
pose proof (EXv 6%nat ltac:(lia)) as X6.
pose proof (EXv 7%nat ltac:(lia)) as X7.
pose proof (EXv 8%nat ltac:(lia)) as X8.
pose proof (EXv 9%nat ltac:(lia)) as X9.
pose proof (EXv 10%nat ltac:(lia)) as X10.
pose proof (EXv 11%nat ltac:(lia)) as X11.
cbn [Nat.add nth rga_vals] in X0, X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11.
eapply (rga_obj_r_of_region _ _ r _ _ _ _ _ _ (SOff 43 0) cur HRr).
- rewrite (AGv 10%nat) by lia. rewrite E10. apply unsigned_lit_small. lia.
- reflexivity.
- intros j v Hj. do 11 (destruct j as [|j]; [injection Hj as <-; split; [cbn [Nat.add]; assumption|]; split; [cbn [nth LAY_Rgb snd fst Z.of_N]; assumption | cbn; tauto]|]).
destruct j; discriminate Hj.
- cbn; tauto.
- cbn [sv_denot]. rewrite X11. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- exact R60v. }
cbn [app] in Hobj. clear HRr.
pose proof (ajournal_fp_mono B _ _ (ablocks_fp [(r, RGB_SIZE)]) (ablocks_fp (trgb_own r g s N bef beffmt)) _ _ _ _ _ _ _ _ _ _ _ _
ltac:(intros a (rg & [<- | []] & Hr); exists (r, r + req_size RGB_SIZE); split; [left; reflexivity | exact Hr]) HJ3) as HJF.
ga_join HS ss_EPI 900%nat rga_deads_X ltac:(idtac).
lazymatch goal with |- SRr _ ?W3x (mkCfg ?msx ?mdx) _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HX : INV_X B (mkRGCX ly S W regs mem md ch r cfp g wfn ctx path attr gen loops Wd Hd bef beffmt cur s N img fmt fattr fgen delay rest cid pos fpos E0)
Ev k ly3 S3 W3x msx mdx) end end.
{ eapply (rga_INV_X_same B LAWS _ _ k ly3 S3 W3 _ _ [(7, fpos)] cur HBASE0).
- unfold rgc_FPs. rga_cbn_cx_goal. exact HJ3.
- assert (0 <= EV_RGBADD) by (vm_compute; discriminate). lia.
- rga_bud_tac Hbud.
- rga_cbn_cx_goal. rewrite Eab3. apply Permutation_refl.
- rga_cbn_cx_goal. exact Hobj. }
rga_hand RX HS HJF k; [rga_E_tac HEE0 | exact HX].
Qed.
End c.
End b.
