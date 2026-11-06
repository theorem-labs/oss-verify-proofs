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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCnf YCoi YCoj YCok YCol YCom YCon YCoo YCnd YCni YCnb.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCnc YCnk.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCil YCim YCin YP16 YI0f YI09 YCji.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_CL_of_CLn : forall n, rga_fromA B ss_CLn (fun _ => INV_CL B n) -> rga_from B ss_CL (INV_CL B n).
Proof.
intros n RCLn.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & T & cnt & ent & tail & st & tns & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rdn & Tdn & Adn) & Hown & Rcnt & RT & Rha & Hha & (av & Rav & Hav) &
HTch & HcntT & HentOk & HentND & Hsum & Hlen_ent & Hcinv & HL254 & Htail & HCLm & Hlen_tns & Hmatch & Hfacts & MOK & Rroot & R817 & R818 & Hmeas).
destruct Hk0 as [Hk0 Hbud].
unfold ss_CL in HS.
ga_join HS ss_CLn 819%nat (@nil (bv 5)) ltac:(idtac).
rga_hand RCLn HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, T, cnt, ent, tail, st, tns.
split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HPm3|].
do 9 (split; [split; [m_ewT | split; eassumption]|]).
split; [exact Hown|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [exact Hha|].
split; [exists av; split; [m_ewT | exact Hav]|].
split; [exact HTch|]. split; [exact HcntT|].
split; [exact HentOk|]. split; [exact HentND|]. split; [exact Hsum|]. split; [exact Hlen_ent|].
split; [exact Hcinv|]. split; [exact HL254|]. split; [exact Htail|].
split; [exact HCLm|]. split; [exact Hlen_tns|]. split; [exact Hmatch|]. split; [exact Hfacts|]. split; [exact MOK|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. exact Hmeas.
Qed.
End b.
End a.
