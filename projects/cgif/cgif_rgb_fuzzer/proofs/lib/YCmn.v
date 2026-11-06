(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx YCi1 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCqf YCea YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn5 YCn6 YCn7 YCn8 YCoi YCoj YCok YCn9 YCna YCol YCo3 YCo5 YCo9 YCmr YCmq YCms YCmt.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis COLHASH : tcolhash_spec B.
Hypothesis ABCMP : abcmp_realizes trbsegs B A_bcmp_tra.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_SM_loop : rga_fromA B ss_SMT (fun _ => INV_SMT B) -> forall n, rga_from B ss_SMH (INV_SM B n).
Proof.
intros RSMT. induction n as [|n IH].
{
intros cx E k ly3 S3 W3 ms3 md3 _ _ _ _ _ HINV _. exfalso.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & ix & Ht & ent & HINV).
repeat (destruct HINV as [? HINV]). lia. }
pose proof (rga_SM_store B TL LAWS FFL RSMT n IH) as RS.
pose proof (rga_SM_store_e B TL LAWS FFL RSMT n IH) as RSe.
apply (rga_SM_head B TL LAWS FFL ABCMP n); [apply (rga_SM_colhash B TL LAWS FFL COLHASH n); exact RS | exact RSe].
Qed.
Lemma rga_SM : rga_fromA B ss_SMT (fun _ => INV_SMT B) -> rga_from B ss_SM0 (INV_HDx B 0 256).
Proof.
intros RSMT. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & Ht & ent & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & Rcnt & RT & Rha & Hha & Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & Hcnt).
destruct Hk0 as [Hk0 Hbud].
unfold ss_SM0 in HS.
pose proof Hwf as Hwf0. destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
pose proof Hrgb as Hrgb'. cbn [obj_at LAY_Rgb] in Hrgb'.
destruct Hrgb' as ([_ R0v] & [_ R8v] & [_ R16v] & [_ R24v] & [_ R32v] & [_ R36v] & [_ R40v] & [_ R42v] & [_ R44v] & [_ R48v] & [_ R56v] & [_ R60v] & _).
cbn [fst snd N.to_nat Z.of_N] in R0v, R8v, R16v, R24v, R32v, R36v, R40v, R42v, R44v, R48v, R56v, R60v.
assert (Hfim_in3 : In (fim, N) (ablocks B ly3 S3))
by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; left; right; left; reflexivity]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ fim N HAR3 Hfim_in3) as (Hfim4096 & _ & Hfimceil & _).
pose proof (req_size_pos N ltac:(clear - HN1; lia)) as HrqN.
rregU HS (23%bv : bv 5) (fim + 0) ltac:(rewrite (U_atom _ 184 fim Rfim) by (clear - Hfim4096 Hfimceil HrqN C1; lia); clear; lia) Q20.
rregU HS (20%bv : bv 5) (fmt * 0) ltac:(rewrite Z.mul_0_r; reflexivity) Q23.
rregU HS (21%bv : bv 5) (beffmt * 0) ltac:(rewrite Z.mul_0_r; reflexivity) Q24.
rregU HS (18%bv : bv 5) (N - 0)
ltac:(rewrite Z.sub_0_r; apply U_zext32_shifts; [apply m_U_add0; rewrite HNhw; apply (U_HW _ 40 39 Hd Wd E40 E39 R44v R42v); rewrite <- HNhw; clear - HN1 HN; unfold RGB_NMAX in *; lia
| clear - HN1 HN; unfold RGB_NMAX in *; lia]) Q26.
rregU HS (25%bv : bv 5) (fim + 0) ltac:(rewrite (U_atom _ 184 fim Rfim) by (clear - Hfim4096 Hfimceil HrqN C1; lia); clear; lia) QS.
ga_join HS ss_SMH 700%nat rga_deads_SMH
ltac:(idtac; ga_join_val HS 700%nat 17%nat Q20 N717; ga_join_val HS 700%nat 18%nat Q23 N718; ga_join_val HS 700%nat 19%nat Q24 N719;
ga_join_val HS 700%nat 20%nat Q26 N720; ga_join_val HS 700%nat 21%nat QS N721).
pose proof (rga_SM_loop RSMT (Z.to_nat N)) as LOOP.
m_hand_ih LOOP HS HJ3 k; [rga_E_tac HEE0 | ].
assert (Hix0 : 0 <= 0 < N) by (clear - HN1; lia).
assert (Hnix0 : Z.of_nat (Z.to_nat N) = N - 0) by (rewrite Z2Nat.id by (clear - HN1; lia); clear; lia).
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, 0, Ht, ent. m_inv_auto.
Qed.
End b.
End a.
