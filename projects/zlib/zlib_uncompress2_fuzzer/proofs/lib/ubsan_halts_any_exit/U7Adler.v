(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_zlib_uncompress2_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem U7AdlerBase U7Adler_code U7AdlerIface FuzzAdlerLib U7AdlerA U7AdlerB.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.cks Require Import CkTables CkModel CkMathAdler CkWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque adler32_z_model lo16 hi16 byte_at.

#[local] Abbreviation W8 v := (word_to_le_bytes 8 v).


Definition am13 (m : word -> option byte) (usp : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (usp - 8)) (W8 (getr regs 1)))
    (Z_to_bv 64 (usp - 16)) (W8 (getr regs 8)))
    (Z_to_bv 64 (usp - 24)) (W8 (getr regs 9)))
    (Z_to_bv 64 (usp - 32)) (W8 (getr regs 18)))
    (Z_to_bv 64 (usp - 40)) (W8 (getr regs 19)))
    (Z_to_bv 64 (usp - 48)) (W8 (getr regs 20)))
    (Z_to_bv 64 (usp - 56)) (W8 (getr regs 21)))
    (Z_to_bv 64 (usp - 64)) (W8 (getr regs 22)))
    (Z_to_bv 64 (usp - 72)) (W8 (getr regs 23)))
    (Z_to_bv 64 (usp - 80)) (W8 (getr regs 24)))
    (Z_to_bv 64 (usp - 88)) (W8 (getr regs 25)))
    (Z_to_bv 64 (usp - 96)) (W8 (getr regs 26)))
    (Z_to_bv 64 (usp - 104)) (W8 (getr regs 27)).

Definition aM2 (m : word -> option byte) (usp : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (am13 m usp regs)
    (Z_to_bv 64 (usp - 112)) (W8 (Z_to_bv 64 NEG5552)))
    (Z_to_bv 64 (usp - 120)) (W8 (Z_to_bv 64 5552)).

Lemma austk8 {RCa1 : RunCtx}  : forall (m m' : word -> option byte) (usp z : Z),
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 128)) 128 = true -> 128 <= usp < two64 -> mem_grows m m' ->
  usp - 128 <= z -> z + 8 <= usp -> store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m' (Z_to_bv 64 z) 8 = true.
Proof.
  intros m m' usp z Hstk Husp Hg Hlo Hhi.
  eapply store_ok_mono; [exact Hg|].
  eapply (store_ok_sub (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 128)) _ 128 8);
    [u_norm; lia | exact Hstk | u_norm; lia
    | u_norm; change (Z.of_nat 8) with 8%Z; change (Z.of_nat 128%nat) with 128%Z; lia].
Qed.

Ltac grows := repeat (first [ apply mem_grows_refl | eapply mem_grows_trans; [| apply wbytes_grows] ]).

Lemma am13_grows : forall m usp regs, mem_grows m (am13 m usp regs).
Proof. intros. unfold am13. grows. Qed.

Lemma aM2_grows : forall m usp regs, mem_grows m (aM2 m usp regs).
Proof. intros. unfold aM2, am13. grows. Qed.

Ltac fm1 := eapply frame_mod_trans_same;
    [| eapply frame_mod_weaken; [| apply frame_mod_wbytes; rewrite lenW8; change (Z.of_nat 8) with 8%Z; u_norm; lia];
       intros a [Ha _]; split; [|exact I]; rewrite lenW8; change (Z.of_nat 8) with 8%Z;
       intros Hin; apply Ha; unfold in_rng in *; revert Hin; u_norm; lia ].

Lemma am13_frame : forall m usp regs, 128 <= usp < two64 ->
  frame_mod m (am13 m usp regs) [(Z_to_bv 64 (usp - 128), 128%Z)].
Proof.
  intros m usp regs Husp. unfold am13. repeat fm1. apply frame_mod_refl.
Qed.

Lemma aM2_frame : forall m usp regs, 128 <= usp < two64 ->
  frame_mod m (aM2 m usp regs) [(Z_to_bv 64 (usp - 128), 128%Z)].
Proof.
  intros m usp regs Husp. unfold aM2, am13. repeat fm1. apply frame_mod_refl.
Qed.

Lemma aframe_ro {RCa1 : RunCtx}  : forall m usp, 128 <= usp < two64 ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 128)) 128 = true -> img_ok m -> RO_HI <= usp - 128 \/ usp <= RO_LO.
Proof.
  intros m usp Husp Hstk Hi.
  pose proof (store_ok_off_ro m (usp - 128) 128%nat Hstk ltac:(lia) ltac:(change (Z.of_nat 128%nat) with 128%Z; lia)
                ltac:(change (Z.of_nat 128%nat) with 128%Z; lia) Hi) as Hro.
  change (Z.of_nat 128%nat) with 128%Z in Hro. lia.
Qed.

Lemma am13_img {RCa1 : RunCtx}  : forall m usp regs, 128 <= usp < two64 ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 128)) 128 = true -> img_ok m -> img_ok (am13 m usp regs).
Proof.
  intros m usp regs Husp Hstk Hi.
  pose proof (aframe_ro m usp Husp Hstk Hi) as Hro. unfold RO_LO, RO_HI in Hro.
  unfold am13.
  repeat (apply img_ok_wbytes; [ | rewrite lenW8; change (Z.of_nat 8) with 8%Z; u_norm; unfold RO_LO, RO_HI; lia
                                 | rewrite lenW8; change (Z.of_nat 8) with 8%Z; u_norm; lia ]).
  exact Hi.
Qed.

Lemma aM2_img {RCa1 : RunCtx}  : forall m usp regs, 128 <= usp < two64 ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 128)) 128 = true -> img_ok m -> img_ok (aM2 m usp regs).
Proof.
  intros m usp regs Husp Hstk Hi.
  pose proof (aframe_ro m usp Husp Hstk Hi) as Hro. unfold RO_LO, RO_HI in Hro.
  unfold aM2.
  repeat (apply img_ok_wbytes; [ | rewrite lenW8; change (Z.of_nat 8) with 8%Z; u_norm; unfold RO_LO, RO_HI; lia
                                 | rewrite lenW8; change (Z.of_nat 8) with 8%Z; u_norm; lia ]).
  first [ exact Hi | apply am13_img; assumption ].
Qed.

Lemma aM2_s16 {RCa1 : RunCtx}  : forall m usp regs, 128 <= usp < two64 ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (aM2 m usp regs) (Z_to_bv 64 (usp - 128 + 16)) 8 = Some (W8 (Z_to_bv 64 NEG5552)).
Proof.
  intros m usp regs Husp. replace (usp - 128 + 16) with (usp - 112) by lia. unfold aM2. rdn_solve.
Qed.

Lemma aM2_s8 {RCa1 : RunCtx}  : forall m usp regs, 128 <= usp < two64 ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (aM2 m usp regs) (Z_to_bv 64 (usp - 128 + 8)) 8 = Some (W8 (Z_to_bv 64 5552)).
Proof.
  intros m usp regs Husp. replace (usp - 128 + 8) with (usp - 120) by lia. unfold aM2. rdn_solve.
Qed.


Section TOP.
Context {RCa1 : RunCtx}.
  Ltac zbv := apply (f_equal (fun z : Z => Z_to_bv 64 z)); lia.
  Ltac solve_kb := first [ assumption | apply lkeeps_refl | solve_lkeeps
                         | eapply lkeeps_trans; [eassumption | solve_kb] ].
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_kb ].

  Ltac sdz F D aa oktac :=
    chain_step;
    [ reflexivity
    | eapply step_sd_at with (a := aa);
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi; zbv
      | gres; reflexivity
      | oktac ]
    | step_simpl ].

  Ltac ldz F D vv E :=
    chain_step;
    [ reflexivity
    | eapply step_ld with (v := vv);
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ =>
          match type of E with rdn _ _ (Z_to_bv 64 ?y) _ = _ => replace x with y by lia end end;
        exact E
      | apply bytes_le_to_Z_8 ]
    | step_simpl; gres ].

  Definition UPK : list reg := [1; 3; 4; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

  Lemma upro_run : forall regs m rom (usp : Z),
    getr regs 2 = Z_to_bv 64 usp ->
    128 <= usp < two64 -> store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 128)) 128 = true ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x17da0 : word) m rom) (mkst r (0x17dd8 : word) (am13 m usp regs) rom)
      /\ getr r 2 = Z_to_bv 64 (usp - 128)
      /\ lkeeps UPK regs r.
  Proof.
    intros regs m rom usp R2 Husp Hstk.
    eexists. split.
    - stepz F_17c88 D_17c88.
      sdz F_17c8c D_17c8c (Z_to_bv 64 (usp - 8)) ltac:(apply (austk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_17c90 D_17c90 (Z_to_bv 64 (usp - 16)) ltac:(apply (austk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_17c94 D_17c94 (Z_to_bv 64 (usp - 24)) ltac:(apply (austk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_17c98 D_17c98 (Z_to_bv 64 (usp - 32)) ltac:(apply (austk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_17c9c D_17c9c (Z_to_bv 64 (usp - 40)) ltac:(apply (austk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_17ca0 D_17ca0 (Z_to_bv 64 (usp - 48)) ltac:(apply (austk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_17ca4 D_17ca4 (Z_to_bv 64 (usp - 56)) ltac:(apply (austk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_17ca8 D_17ca8 (Z_to_bv 64 (usp - 64)) ltac:(apply (austk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_17cac D_17cac (Z_to_bv 64 (usp - 72)) ltac:(apply (austk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_17cb0 D_17cb0 (Z_to_bv 64 (usp - 80)) ltac:(apply (austk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_17cb4 D_17cb4 (Z_to_bv 64 (usp - 88)) ltac:(apply (austk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_17cb8 D_17cb8 (Z_to_bv 64 (usp - 96)) ltac:(apply (austk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      sdz F_17cbc D_17cbc (Z_to_bv 64 (usp - 104)) ltac:(apply (austk8 m _ usp); [exact Hstk | lia | grows | lia | lia]).
      apply mst_refl.
    - unfold UPK. post.
  Qed.

  Definition UKE : list reg := [3; 4; 10]%bv.

  Lemma uepi_run : forall regs M rom (retw : word) (usp : Z) (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word),
    v1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 (usp - 128) -> 128 <= usp < two64 ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 8)) 8 = Some (W8 v1) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 16)) 8 = Some (W8 v8) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 24)) 8 = Some (W8 v9) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 32)) 8 = Some (W8 v18) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 40)) 8 = Some (W8 v19) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 48)) 8 = Some (W8 v20) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 56)) 8 = Some (W8 v21) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 64)) 8 = Some (W8 v22) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 72)) 8 = Some (W8 v23) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 80)) 8 = Some (W8 v24) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 88)) 8 = Some (W8 v25) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 96)) 8 = Some (W8 v26) ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (usp - 104)) 8 = Some (W8 v27) ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x18290 : word) M rom) (mkst r retw M rom)
      /\ getr r 10 = getr regs 10 /\ getr r 2 = Z_to_bv 64 usp /\ getr r 1 = v1
      /\ getr r 8 = v8 /\ getr r 9 = v9 /\ getr r 18 = v18 /\ getr r 19 = v19 /\ getr r 20 = v20
      /\ getr r 21 = v21 /\ getr r 22 = v22 /\ getr r 23 = v23 /\ getr r 24 = v24
      /\ getr r 25 = v25 /\ getr r 26 = v26 /\ getr r 27 = v27
      /\ lkeeps UKE regs r.
  Proof.
    intros regs M rom retw usp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hv1 Hret R2 Husp
           E1 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27.
    eexists. split.
    - ldz F_18178 D_18178 v1 E1.
      ldz F_1817c D_1817c v8 E8.
      ldz F_18180 D_18180 v9 E9.
      ldz F_18184 D_18184 v18 E18.
      ldz F_18188 D_18188 v19 E19.
      ldz F_1818c D_1818c v20 E20.
      ldz F_18190 D_18190 v21 E21.
      ldz F_18194 D_18194 v22 E22.
      ldz F_18198 D_18198 v23 E23.
      ldz F_1819c D_1819c v24 E24.
      ldz F_181a0 D_181a0 v25 E25.
      ldz F_181a4 D_181a4 v26 E26.
      ldz F_181a8 D_181a8 v27 E27.
      stepz F_181ac D_181ac.
      stepret F_181b0 D_181b0 retw ltac:(rwR; subst v1; reflexivity).
      apply mst_refl.
    - unfold UKE. post.
  Qed.

  Lemma ust2_run : forall regs m rom r0 (usp : Z),
    getr regs 2 = Z_to_bv 64 (usp - 128) -> getr regs 21 = Z_to_bv 64 NEG5552 -> getr regs 22 = Z_to_bv 64 4096 ->
    128 <= usp < two64 -> store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 128)) 128 = true ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x17f38 : word) (am13 m usp r0) rom) (mkst r (0x17f44 : word) (aM2 m usp r0) rom)
      /\ r = regupd regs 21 (Z_to_bv 64 5552).
  Proof.
    intros regs m rom r0 usp R2 R21 R22 Husp Hstk.
    eexists. split.
    - sdz F_17e20 D_17e20 (Z_to_bv 64 (usp - 112))
          ltac:(apply (austk8 m _ usp); [exact Hstk | lia | unfold am13; grows | lia | lia]).
      rewrite R21.
      stepz F_17e24 D_17e24.
      sdz F_17e28 D_17e28 (Z_to_bv 64 (usp - 120))
          ltac:(apply (austk8 m _ usp); [exact Hstk | lia | unfold am13; grows | lia | lia]).
      apply mst_refl.
    - reflexivity.
  Qed.
End TOP.


Ltac kb_chain :=
  repeat match goal with
    | K : lkeeps _ ?a ?b |- getr ?b ?r = _ => rewrite (K r) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto]))
    end.

Ltac slots13 := unfold aM2, am13; rdn_solve.

Section RUNZ.
Context {RCa1 : RunCtx}.
  Variables (m rom : word -> option byte) (retw : word) (usp a adr len : Z).
  Hypothesis Hret : ret_ok retw.
  Hypothesis Ha : 0 <= a < two64.
  Hypothesis Hadr : 1 <= adr.
  Hypothesis Hlen : 0 <= len.
  Hypothesis Hnw : adr + len < two64.
  Hypothesis Husp : 128 <= usp < two64.
  Hypothesis Hstk : store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 128)) 128 = true.
  Hypothesis Hbelow : 1 <= len -> adr + len <= usp - 128.
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (adr + i)) 1 = Some [b].

  Lemma uepi_any : forall regs r2 M,
    (M = am13 m usp regs \/ M = aM2 m usp regs) ->
    getr regs 1 = retw -> getr r2 2 = Z_to_bv 64 (usp - 128) ->
    exists r3, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r2 (0x18290 : word) M rom) (mkst r3 retw M rom)
      /\ getr r3 10 = getr r2 10 /\ getr r3 2 = Z_to_bv 64 usp /\ getr r3 1 = getr regs 1
      /\ getr r3 8 = getr regs 8 /\ getr r3 9 = getr regs 9 /\ getr r3 18 = getr regs 18
      /\ getr r3 19 = getr regs 19 /\ getr r3 20 = getr regs 20 /\ getr r3 21 = getr regs 21
      /\ getr r3 22 = getr regs 22 /\ getr r3 23 = getr regs 23 /\ getr r3 24 = getr regs 24
      /\ getr r3 25 = getr regs 25 /\ getr r3 26 = getr regs 26 /\ getr r3 27 = getr regs 27
      /\ lkeeps UKE r2 r3.
  Proof.
    intros regs r2 M HM R1 T2.
    apply (uepi_run r2 M rom retw usp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
             (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
             (getr regs 26) (getr regs 27) R1 Hret T2 Husp);
      (destruct HM as [-> | ->]; slots13).
  Qed.

  Theorem uadler32_z_run : forall regs,
    getr regs 1 = retw -> getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 a ->
    getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 len ->
    exists r m',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x17da0 : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m adr (Z.to_nat len)))
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 128), 128%Z)].
  Proof.
    intros regs R1 R2 R10 R11 R12.
    set (M := am13 m usp regs).
    assert (HMi : img_ok M) by (apply am13_img; [exact Husp | exact Hstk | exact Himg]).
    assert (HMr : forall i, 0 <= i < len -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (adr + i)) 1 = Some [b])
      by (apply (readable_grows (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m M adr len (am13_grows m usp regs) Hrd)).
    assert (Hfm : frame_mod m M [(Z_to_bv 64 (usp - 128), 128%Z)]) by (apply am13_frame; exact Husp).
    assert (EB : forall M', frame_mod m M' [(Z_to_bv 64 (usp - 128), 128%Z)] ->
                 bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M' adr (Z.to_nat len) = bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m adr (Z.to_nat len)).
    { intros M' Hf. destruct (Z.eq_dec len 0) as [-> | Hz]; [reflexivity|].
      apply (bytes_at_frame1 (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m M' (Z.to_nat len) adr (usp - 128) 128 Hf); lia. }
    destruct (upro_run regs m rom usp R2 Husp Hstk) as (r1 & M1 & S2 & K1). fold M in M1.
    assert (S10 : getr r1 10 = Z_to_bv 64 a) by (kb_chain; exact R10).
    assert (S11 : getr r1 11 = Z_to_bv 64 adr) by (kb_chain; exact R11).
    assert (S12 : getr r1 12 = Z_to_bv 64 len) by (kb_chain; exact R12).
    destruct (Z.eq_dec len 1) as [H1 | H1].
    -
      rewrite H1 in S12.
      destruct (ua1_run M rom adr len HMr ltac:(lia) ltac:(lia) r1 a S10 S11 S12 Ha ltac:(lia) Hadr)
        as (r2 & M2 & V2 & K2).
      assert (T2 : getr r2 2 = Z_to_bv 64 (usp - 128)) by (kb_chain; exact S2).
      destruct (uepi_any regs r2 M ltac:(left; reflexivity) R1 T2)
        as (r3 & M3 & W10 & W2 & W1 & W8' & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & K3).
      exists r3, M. split; [|split; [|split]].
      + eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2 | exact M3].
      + rewrite W10, V2, <- (EB M Hfm), H1. reflexivity.
      + intros rr Hin. cbv [callee_saved In] in Hin.
        repeat (destruct Hin as [<- | Hin]);
          first [ rewrite W2; symmetry; exact R2
                | assumption
                | kb_chain; first [ reflexivity | assumption ]
                | destruct Hin ].
      + exact Hfm.
    - destruct (uhalves_run M rom adr len ltac:(lia) ltac:(lia) r1 a S10 S11 S12 Ha Hlen H1 Hadr)
        as (r2 & M2 & T14 & T13 & T10 & T11 & T12 & K2).
      assert (T2 : getr r2 2 = Z_to_bv 64 (usp - 128)) by (kb_chain; exact S2).
      destruct (Z.lt_ge_cases len NMAX) as [Hlt | Hge].
      +
        destruct (ubody_run M rom adr len HMi HMr ltac:(lia) ltac:(lia) Hlen r2 a T11 T12 T14 T13 H1 Hlt)
          as (r3 & M3 & V3 & K3).
        assert (U2 : getr r3 2 = Z_to_bv 64 (usp - 128)) by (kb_chain; exact S2).
        destruct (uepi_any regs r3 M ltac:(left; reflexivity) R1 U2)
          as (r4 & M4 & W10 & W2 & W1 & W8' & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & K4).
        exists r4, M. split; [|split; [|split]].
        * eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|].
          eapply msteps_trans; [exact M3 | exact M4].
        * rewrite W10, V3, <- (EB M Hfm). reflexivity.
        * intros rr Hin. cbv [callee_saved In] in Hin.
          repeat (destruct Hin as [<- | Hin]);
            first [ rewrite W2; symmetry; exact R2
                  | assumption
                  | kb_chain; first [ reflexivity | assumption ]
                  | destruct Hin ].
        * exact Hfm.
      +
        destruct (ulong_head M rom adr len ltac:(lia) ltac:(lia) Hlen r2 T12 Hge)
          as (r3 & M3 & HCK3 & T21 & T22 & T23 & K3).
        assert (U2 : getr r3 2 = Z_to_bv 64 (usp - 128)) by (kb_chain; exact S2).
        destruct (ust2_run r3 m rom regs usp U2 T21 T22 Husp Hstk) as (r4 & M4 & Er4).
        set (M' := aM2 m usp regs) in *.
        assert (HMi' : img_ok M') by (apply aM2_img; [exact Husp | exact Hstk | exact Himg]).
        assert (HMr' : forall i, 0 <= i < len -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) M' (Z_to_bv 64 (adr + i)) 1 = Some [b])
          by (apply (readable_grows (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m M' adr len (aM2_grows m usp regs) Hrd)).
        assert (Hfm' : frame_mod m M' [(Z_to_bv 64 (usp - 128), 128%Z)]) by (apply aM2_frame; exact Husp).
        assert (G4 : forall x : reg, x <> 21%bv -> getr r4 x = getr r3 x).
        { intros x Hx. rewrite Er4. rewrite getr_other by (exact Hx). reflexivity. }
        assert (HCK4 : CK16 r4).
        { apply (CK16_kept [10; 15; 16; 17; 5; 6; 7; 28; 29; 30; 31; 8; 9; 18; 19; 20]%bv r3 r4 HCK3); [|incl_dec].
          intros x Hx. apply G4. intros ->. revert Hx. cbv. intuition discriminate. }
        destruct (ulong_body M' rom adr len HMi' HMr' ltac:(lia) ltac:(lia) Hlen r4 a (usp - 128) HCK4
                    ltac:(rewrite G4 by (intros E; discriminate E); exact U2) ltac:(lia)
                    (aM2_s16 m usp regs Husp) (aM2_s8 m usp regs Husp)
                    ltac:(rewrite G4 by (intros E; discriminate E); exact T23)
                    ltac:(rewrite G4 by (intros E; discriminate E); kb_chain; exact T11)
                    ltac:(rewrite G4 by (intros E; discriminate E); kb_chain; exact T12)
                    ltac:(rewrite G4 by (intros E; discriminate E); kb_chain; exact T14)
                    ltac:(rewrite G4 by (intros E; discriminate E); kb_chain; exact T13) Hge)
          as (r5 & M5 & V5 & K5).
        assert (W2' : getr r5 2 = Z_to_bv 64 (usp - 128)).
        { rewrite (K5 (2%bv : reg)) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite G4 by (intros E; discriminate E). exact U2. }
        destruct (uepi_any regs r5 M' ltac:(right; reflexivity) R1 W2')
          as (r6 & M6 & W10 & W2 & W1 & W8' & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & K6).
        exists r6, M'. split; [|split; [|split]].
        * eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|].
          eapply msteps_trans; [exact M3|]. eapply msteps_trans; [exact M4|].
          eapply msteps_trans; [exact M5 | exact M6].
        * rewrite W10, V5, <- (EB M' Hfm'). reflexivity.
        * intros rr Hin. cbv [callee_saved In] in Hin.
          repeat (destruct Hin as [<- | Hin]);
            first [ rewrite W2; symmetry; exact R2
                  | assumption
                  | rewrite (K6 _), (K5 _) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); rewrite G4 by (intros E; discriminate E);
                    kb_chain; first [ reflexivity | assumption ]
                  | destruct Hin ].
        * exact Hfm'.
  Qed.
End RUNZ.

Theorem u7_adler32_z {RCa1 : RunCtx}  : U7_adler32_z_stmt.
Proof.
  unfold U7_adler32_z_stmt.
  intros regs m rom retw usp a adr len R1 Hret R2 R10 R11 R12 Ha Hadr Hlen Hnw Husp Hstk Hbelow Himg Hrd.
  change (2 ^ 64) with two64 in Ha, Hnw, Husp.
  exact (uadler32_z_run m rom retw usp a adr len Hret Ha Hadr Hlen Hnw Husp Hstk Hbelow Himg Hrd regs R1 R2 R10 R11 R12).
Qed.

Theorem u7_adler32_z_null {RCa1 : RunCtx}  : U7_adler32_z_null_stmt.
Proof.
  unfold U7_adler32_z_null_stmt.
  intros regs m rom retw usp R1 Hret R2 R11 R12 Husp Hstk.
  change (2 ^ 64) with two64 in Husp.
  set (M := am13 m usp regs).
  destruct (upro_run regs m rom usp R2 Husp Hstk) as (r1 & M1 & S2 & K1). fold M in M1.
  assert (S11 : getr r1 11 = Z_to_bv 64 0) by (kb_chain; exact R11).
  assert (S12 : getr r1 12 = Z_to_bv 64 0) by (kb_chain; exact R12).
  assert (PRE : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r1 (0x17dd8 : word) M rom) (mkst r (0x18290 : word) M rom)
           /\ getr r 10 = Z_to_bv 64 1 /\ getr r 2 = Z_to_bv 64 (usp - 128) /\ lkeeps ULH r1 r).
  { eexists. split.
    - stepi F_17cc0 D_17cc0.
      stepi F_17cc4 D_17cc4.
      stepz F_17cc8 D_17cc8.
      stepi F_17ccc D_17ccc.
      stepb_tk F_17cd0 D_17cd0 ltac:(condZ).
      stepb_tk F_17d28 D_17d28 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; rwR; first [reflexivity | assumption | solve_lkeeps]. }
  destruct PRE as (r2 & M2 & T10 & T2 & K2).
  destruct (uepi_run r2 M rom retw usp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
              (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
              (getr regs 26) (getr regs 27) R1 Hret T2 Husp)
    as (r3 & M3 & W10 & W2 & W1 & W8' & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & K3).
  1-13: subst M; slots13.
  exists r3, M. split; [|split; [|split]].
  - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2 | exact M3].
  - rewrite W10. exact T10.
  - intros rr Hin. cbv [callee_saved In] in Hin.
    repeat (destruct Hin as [<- | Hin]);
      first [ rewrite W2; symmetry; exact R2
            | assumption
            | kb_chain; first [ reflexivity | assumption ]
            | destruct Hin ].
  - subst M. apply am13_frame. exact Husp.
Qed.

Theorem u7_adler32 {RCa1 : RunCtx}  : U7_adler32_stmt.
Proof.
  unfold U7_adler32_stmt.
  intros regs m rom retw usp a adr v len R1 Hret R2 R10 R11 R12 Hv Hvl Ha Hadr Hnw Husp Hstk Hbelow Himg Hrd.
  pose proof (mod32_range v) as Hl. change (2 ^ 32) with two32 in Hvl. rewrite Hvl in Hl.
  assert (PRE : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x182d0 : word) m rom) (mkst r (0x17da0 : word) m rom)
           /\ (getr r 1 = retw /\ getr r 2 = Z_to_bv 64 usp /\ getr r 10 = Z_to_bv 64 a
               /\ getr r 11 = Z_to_bv 64 adr /\ getr r 12 = Z_to_bv 64 len /\ keeps_cs regs r)).
  { eexists. split.
    - stepz F_181b8 D_181b8. stepz F_181bc D_181bc. rewrite Hvl.
      stepz F_181c0 D_181c0.
      apply mst_refl.
    - repeat split; gres; rwR; try reflexivity. apply (proj2 (keeps_cs_lkeeps _ _)). solve_lkeeps. }
  destruct PRE as (r1 & M1 & S1 & S2 & S10 & S11 & S12 & K1).
  destruct (u7_adler32_z r1 m rom retw usp a adr len S1 Hret S2 S10 S11 S12 Ha Hadr ltac:(lia) Hnw Husp Hstk Hbelow Himg Hrd)
    as (r2 & m' & M2 & V10 & K2 & F2).
  exists r2, m'. split; [eapply msteps_trans; [exact M1 | exact M2]|]. split; [exact V10|]. split; [| exact F2].
  eapply keeps_cs_trans; [exact K1 | exact K2].
Qed.

Theorem u7_adler32_null {RCa1 : RunCtx}  : U7_adler32_null_stmt.
Proof.
  unfold U7_adler32_null_stmt.
  intros regs m rom retw usp R1 Hret R2 R11 R12 Husp Hstk.
  assert (PRE : exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x182d0 : word) m rom) (mkst r (0x17da0 : word) m rom)
           /\ (getr r 1 = retw /\ getr r 2 = Z_to_bv 64 usp /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 0
               /\ keeps_cs regs r)).
  { eexists. split.
    - stepi F_181b8 D_181b8. stepi F_181bc D_181bc.
      stepz F_181c0 D_181c0.
      apply mst_refl.
    - repeat split; gres; rwR; try reflexivity;
        first [ apply (proj2 (keeps_cs_lkeeps _ _)); solve_lkeeps | apply bv_eq; vm_compute; reflexivity ]. }
  destruct PRE as (r1 & M1 & S1 & S2 & S11 & S12 & K1).
  destruct (u7_adler32_z_null r1 m rom retw usp S1 Hret S2 S11 S12 Husp Hstk) as (r2 & m' & M2 & V10 & K2 & F2).
  exists r2, m'. split; [eapply msteps_trans; [exact M1 | exact M2]|]. split; [exact V10|]. split.
  - eapply keeps_cs_trans; [exact K1 | exact K2].
  - exact F2.
Qed.
