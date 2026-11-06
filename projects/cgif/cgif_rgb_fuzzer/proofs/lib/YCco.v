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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC1b YC2u YC4o YC4q YC4h YC27 YC2r YC20 YC16 YC4u YCct YC4z YCcq YCcv YCcw.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Let HBcode := tl_code B TL.
Lemma rf_RET : rf_from B ss_RET (INV_RET B).
Proof.
rf_prelude.
pose proof HINV as (Hkk & res & cur2 & Ra0 & Vp & Vn & Vc & Hcur2 & HRES).
rreg HS (1%bv : bv 5) Rra.
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (SRr_ret_at trasegs tratbl_lib tratbl_lib_ok Hwx_tfa Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
intros mat'. unfold rf_post.
cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_lyc x_Sc x_W x_memc x_mdc x_k x_regs x_Bb x_st x_dst x_N x_pdata x_nb x_cur x_cid x_pos x_E0].
lazymatch goal with |- exists ly' S' regs' mem' md' res' cur', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists ly3, S3, rg, mm, mdx, res, cur2 end.
split.
{ rewrite Rra. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 1%nat) by lia.
rewrite (EE 1%nat 1%bv eq_refl). rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
rewrite Hra. reflexivity. }
split; [cbn [ms_mem]; apply (ajournal_materialize trasegs _ LAWS tra_segs_low); eapply (ajournal_mono_k trasegs); [exact HJ3 | exact Hkk]|].
split; [apply aregs_preserved_eqs; creg HS AG EE|].
split; [exact Hfrs3|].
split; [apply (jbud_mono _ _ _ _ HJB); clear - Hkk; lia|].
split; [exact Ra0|].
destruct HKEPT as (K1 & K2 & K3).
split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
split; [exact Vp|]. split; [exact Vn|]. split; [exact Vc|]. split; [exact Hcur2|]. exact HRES.
Qed.
End b.
End a.
