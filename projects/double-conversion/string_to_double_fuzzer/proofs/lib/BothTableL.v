(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec StoreOk AgentLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages BothPlanImages AsanInit AsanPlanImagesInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Definition BOTHL : atable := BOTH.
Definition both_initL : acs := init_acs_of BOTHL.

Lemma BOTHL_eq : BOTHL = BOTH. Proof. reflexivity. Qed.
Lemma both_initL_eq : both_initL = both_init. Proof. reflexivity. Qed.
Lemma BOTHL_lib_fp : lib_fp BOTHL = [(0x664dc0, 0x665ed8)].   (* [comment removed for export] *)
Proof. reflexivity. Qed.

Lemma bothL_in_hull : forall a : word, APS.in_hull BOTHL (bv_unsigned a) = false -> find_segment BSEGS (bv_unsigned a) 1 = None.
Proof. exact both_in_hull. Qed.
Lemma bothL_res_len : APS.res_len_ok BSEGS BOTHL.
Proof. exact both_res_len. Qed.
Lemma bothL_res_hull : Forall (fun iv => img_lo BOTHL <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi BOTHL) (segments_reserved BSEGS).
Proof. exact both_res_hull. Qed.
Lemma bothL_res_chain : (Z.ltb (img_lo BOTHL) (img_hi BOTHL) && res_chain (segments_reserved BSEGS) (img_lo BOTHL) (img_hi BOTHL))%bool = true.
Proof. exact both_res_chain. Qed.
Lemma bothL_hull_ok : APS.hull_ok BOTHL.
Proof. exact both_hull_ok. Qed.
Lemma bothL_shadow_ok : APS.shadow_ok BOTHL.
Proof. exact both_shadow_ok. Qed.
Lemma bothL_img_facts : img_facts BSEGS BOTHL BPH.
Proof. exact both_img_facts. Qed.

(* [comment removed for export] *)
Lemma bothL_lfp_hull : forall z, in_lfp BOTHL z = true -> img_lo BOTHL <= z < img_hi BOTHL.
Proof.
  intros z H. unfold in_lfp in H. apply existsb_exists in H as (r & Hin & Hr).
  cbn [lib_fp BOTHL BOTH] in Hin.
  repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; apply andb_prop in Hr as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; cbn [img_lo img_hi BOTHL BOTH]; lia|]).
  destruct Hin.
Qed.
