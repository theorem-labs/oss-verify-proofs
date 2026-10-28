(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeDefs TimeKit TimeKit2 TimeFmtPure TimeToTmDefs W_time_leaves W_time_to_tm_A.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma mask47_digit : forall c, 48 <= c <= 57 -> Z.land ((Z.shiftr 140737488355333 (Z.land (c + -43) 63)) mod 2 ^ 64) 1 = 0.
Proof.
  intros c Hc. assert (H : c = 48 \/ c = 49 \/ c = 50 \/ c = 51 \/ c = 52 \/ c = 53 \/ c = 54 \/ c = 55 \/ c = 56 \/ c = 57) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; vm_compute; reflexivity.
Qed.

Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
Definition t2t_iter_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte)
    (DA GS tm : Z) (t : tm6) (i : Z) : machine_state -> Prop :=
  fun ms' => exists (x1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte),
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp tp x5 x6 x7 sp (Z_to_bv 64 (2 * i + 2)) (Z_to_bv 64 (i + 1))
                  (Z_to_bv 64 (fld i t + 48)) (Z_to_bv 64 (fld i t)) (Z_to_bv 64 (case_pc i)) x14 x15 x16 x17
                  (Z_to_bv 64 DA) (Z_to_bv 64 24) (Z_to_bv 64 19) (Z_to_bv 64 i) (Z_to_bv 64 (GS + (2 * i + 1))) (Z_to_bv 64 1)
                  (Z_to_bv 64 (2 * i)) (Z_to_bv 64 GS) (Z_to_bv 64 12) (Z_to_bv 64 (chi i t)) x28 x29 x30 x31)
             F (Z_to_bv 64 (case_pc i)) fc None m' (seg_rom ctusegs)
    /\ munch [(lo, bv_unsigned sp + -256)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp + -256).

Definition t2t_iter_stmt (i : Z) : Prop :=
  forall (x1 sp gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo DA GS tm ms mo yr : Z) (t : tm6) (tmc : list cell) (sv : list cell),
  stk ctusegs m lo (bv_unsigned sp + -256) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  ro_cells ctusegs m DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> (DA + 24 <= lo \/ bv_unsigned sp <= DA) -> DA + 24 <= 2^64 ->
  ro_cells ctusegs m GS (gcells t ms) -> (GS + 19 <= lo \/ bv_unsigned sp <= GS) -> 0 < GS -> GS + 19 <= 2^63 ->
  rw_cells ctusegs m (bv_unsigned sp + -256) (T2T_CONSTS 19 mo yr tm ++ tmc ++ sv) ->
  tm_valid t -> 0 <= ms < 1000 ->
  evt ctusegs (t2t_iter_post sp gp tp F fc lo m DA GS tm t i)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 i) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 DA) x19 (Z_to_bv 64 19) x21 x22 (Z_to_bv 64 1) (Z_to_bv 64 (2 * i)) (Z_to_bv 64 GS) (Z_to_bv 64 12) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x12c298) fc None m (seg_rom ctusegs)).

Lemma t2t_iter_0 : t2t_iter_stmt 0.
Proof.
  unfold t2t_iter_stmt. intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS GS0 SHI FR TV MSR.
  unfold TIME_TO_TM_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 256 - 16 \/ bv_unsigned sp - 256 <= DA) by lia.
  assert (SEPS' : GS + 19 <= bv_unsigned sp - 256 - 16 \/ bv_unsigned sp - 256 <= GS) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp + -256)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (fld_range 0 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 0 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 0 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 0 t TV ltac:(lia)) as PV.
  unfold T2T_CONSTS, A_MINTAB, MASK47 in FR. cbn [app] in FR. unfold gcells, zb8 in HS.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = bv_unsigned sp + -256) by (apply unsigned_lit; lia).
  pose proof (mintab_cell m 0 MI ltac:(lia)) as TMIN. pose proof (maxtab_cell m 0 MI ltac:(lia)) as TMAX. pose proof (jtab_cell m 0 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  assert (U8 : bv_unsigned (Z_to_bv 8 (chi 0 t)) = chi 0 t) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
  (* [comment removed for export] *)
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_true. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAN; zify_cond KAN; [exfalso; repeat match type of KAN with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KAN; first [discriminate KAN | lia] | clear KAN].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAW; zify_cond KAW; [exfalso; rewrite ?unsigned_lit in KAW by lia; lia | clear KAW].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAZ; zify_cond KAZ; [exfalso; rewrite ?unsigned_lit in KAZ by lia; lia | clear KAZ].
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  rewrite U8. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -256))) with (lo := lo) (c := chi 0 t); rewrite ?ESP;
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m1. rewrite ?ESP in *.
  rewrite (isdigit_range (chi 0 t)) by lia.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KB4; [ exfalso; zify_cond KB4; rewrite ?U8, ?land64 in KB4; rewrite ?unsigned_lit in KB4 by lia; repeat match type of KB4 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KB4; first [discriminate KB4 | lia] | clear KB4 ].
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KB5; [ exfalso; zify_cond KB5; rewrite ?U8, ?land64 in KB5; rewrite ?unsigned_lit in KB5 by lia; repeat match type of KB5 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KB5; first [discriminate KB5 | lia] | clear KB5 ].
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  assert (U8C : bv_unsigned (Z_to_bv 8 (clo 0 t)) = clo 0 t) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
  rewrite U8C. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -256))) with (lo := lo) (c := clo 0 t); rewrite ?ESP;
      [exact ST2| assumption| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m2. rewrite ?ESP in *.
  rewrite (isdigit_range (clo 0 t)) by lia.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 8 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KC6; [ exfalso; zify_cond KC6; rewrite ?U8, ?land64 in KC6; rewrite ?unsigned_lit in KC6 by lia; repeat match type of KC6 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KC6; first [discriminate KC6 | lia] | clear KC6 ].
  do 4 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  rewrite U8, U8C, (sx32_small 99) by lia.
  replace (chi 0 t * 10 + clo 0 t + -528) with (fld 0 t) by lia.
  brF ltsz.
  (* [comment removed for export] *)
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 7 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  rewrite (sx32_small 24) by lia.
  replace (chi 0 t * 10 + clo 0 t + -480) with (fld 0 t + 48) by lia.
  apply evt_done. unfold t2t_iter_post. do 12 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iter_1 : t2t_iter_stmt 1.
Proof.
  unfold t2t_iter_stmt. intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS GS0 SHI FR TV MSR.
  unfold TIME_TO_TM_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 256 - 16 \/ bv_unsigned sp - 256 <= DA) by lia.
  assert (SEPS' : GS + 19 <= bv_unsigned sp - 256 - 16 \/ bv_unsigned sp - 256 <= GS) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp + -256)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (fld_range 1 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 1 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 1 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 1 t TV ltac:(lia)) as PV.
  unfold T2T_CONSTS, A_MINTAB, MASK47 in FR. cbn [app] in FR. unfold gcells, zb8 in HS.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = bv_unsigned sp + -256) by (apply unsigned_lit; lia).
  pose proof (mintab_cell m 1 MI ltac:(lia)) as TMIN. pose proof (maxtab_cell m 1 MI ltac:(lia)) as TMAX. pose proof (jtab_cell m 1 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  assert (U8 : bv_unsigned (Z_to_bv 8 (chi 1 t)) = chi 1 t) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
  (* [comment removed for export] *)
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_true. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAN; zify_cond KAN; [exfalso; repeat match type of KAN with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KAN; first [discriminate KAN | lia] | clear KAN].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAW; zify_cond KAW; [exfalso; rewrite ?unsigned_lit in KAW by lia; lia | clear KAW].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAZ; zify_cond KAZ; [exfalso; rewrite ?unsigned_lit in KAZ by lia; lia | clear KAZ].
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  rewrite U8. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -256))) with (lo := lo) (c := chi 1 t); rewrite ?ESP;
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m1. rewrite ?ESP in *.
  rewrite (isdigit_range (chi 1 t)) by lia.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KB4; [ exfalso; zify_cond KB4; rewrite ?U8, ?land64 in KB4; rewrite ?unsigned_lit in KB4 by lia; repeat match type of KB4 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KB4; first [discriminate KB4 | lia] | clear KB4 ].
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KB5; [ exfalso; zify_cond KB5; rewrite ?U8, ?land64 in KB5; rewrite ?unsigned_lit in KB5 by lia; repeat match type of KB5 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KB5; first [discriminate KB5 | lia] | clear KB5 ].
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  assert (U8C : bv_unsigned (Z_to_bv 8 (clo 1 t)) = clo 1 t) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
  rewrite U8C. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -256))) with (lo := lo) (c := clo 1 t); rewrite ?ESP;
      [exact ST2| assumption| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m2. rewrite ?ESP in *.
  rewrite (isdigit_range (clo 1 t)) by lia.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 8 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KC6; [ exfalso; zify_cond KC6; rewrite ?U8, ?land64 in KC6; rewrite ?unsigned_lit in KC6 by lia; repeat match type of KC6 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KC6; first [discriminate KC6 | lia] | clear KC6 ].
  do 4 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  rewrite U8, U8C, (sx32_small 99) by lia.
  replace (chi 1 t * 10 + clo 1 t + -528) with (fld 1 t) by lia.
  brF ltsz.
  (* [comment removed for export] *)
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 7 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  rewrite (sx32_small 24) by lia.
  replace (chi 1 t * 10 + clo 1 t + -480) with (fld 1 t + 48) by lia.
  apply evt_done. unfold t2t_iter_post. do 12 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iter_2 : t2t_iter_stmt 2.
Proof.
  unfold t2t_iter_stmt. intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS GS0 SHI FR TV MSR.
  unfold TIME_TO_TM_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 256 - 16 \/ bv_unsigned sp - 256 <= DA) by lia.
  assert (SEPS' : GS + 19 <= bv_unsigned sp - 256 - 16 \/ bv_unsigned sp - 256 <= GS) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp + -256)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (fld_range 2 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 2 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 2 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 2 t TV ltac:(lia)) as PV.
  unfold T2T_CONSTS, A_MINTAB, MASK47 in FR. cbn [app] in FR. unfold gcells, zb8 in HS.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = bv_unsigned sp + -256) by (apply unsigned_lit; lia).
  pose proof (mintab_cell m 2 MI ltac:(lia)) as TMIN. pose proof (maxtab_cell m 2 MI ltac:(lia)) as TMAX. pose proof (jtab_cell m 2 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  assert (U8 : bv_unsigned (Z_to_bv 8 (chi 2 t)) = chi 2 t) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
  (* [comment removed for export] *)
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_true. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAN; zify_cond KAN; [exfalso; repeat match type of KAN with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KAN; first [discriminate KAN | lia] | clear KAN].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAW; zify_cond KAW; [exfalso; rewrite ?unsigned_lit in KAW by lia; lia | clear KAW].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAZ; zify_cond KAZ; [exfalso; rewrite ?unsigned_lit in KAZ by lia; lia | clear KAZ].
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  rewrite U8. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -256))) with (lo := lo) (c := chi 2 t); rewrite ?ESP;
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m1. rewrite ?ESP in *.
  rewrite (isdigit_range (chi 2 t)) by lia.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KB4; [ exfalso; zify_cond KB4; rewrite ?U8, ?land64 in KB4; rewrite ?unsigned_lit in KB4 by lia; repeat match type of KB4 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KB4; first [discriminate KB4 | lia] | clear KB4 ].
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KB5; [ exfalso; zify_cond KB5; rewrite ?U8, ?land64 in KB5; rewrite ?unsigned_lit in KB5 by lia; repeat match type of KB5 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KB5; first [discriminate KB5 | lia] | clear KB5 ].
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  assert (U8C : bv_unsigned (Z_to_bv 8 (clo 2 t)) = clo 2 t) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
  rewrite U8C. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -256))) with (lo := lo) (c := clo 2 t); rewrite ?ESP;
      [exact ST2| assumption| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m2. rewrite ?ESP in *.
  rewrite (isdigit_range (clo 2 t)) by lia.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 8 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. rewrite U8, U8C, (sx32_small 1) by lia. replace (chi 2 t * 10 + clo 2 t + -528) with (fld 2 t) by lia. brF ltsz.
  do 4 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  rewrite ?U8, ?U8C, (sx32_small 12) by lia.
  replace (chi 2 t * 10 + clo 2 t + -528) with (fld 2 t) by lia.
  brF ltsz.
  (* [comment removed for export] *)
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 7 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  rewrite (sx32_small 24) by lia.
  replace (chi 2 t * 10 + clo 2 t + -480) with (fld 2 t + 48) by lia.
  apply evt_done. unfold t2t_iter_post. do 12 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iter_3 : t2t_iter_stmt 3.
Proof.
  unfold t2t_iter_stmt. intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS GS0 SHI FR TV MSR.
  unfold TIME_TO_TM_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 256 - 16 \/ bv_unsigned sp - 256 <= DA) by lia.
  assert (SEPS' : GS + 19 <= bv_unsigned sp - 256 - 16 \/ bv_unsigned sp - 256 <= GS) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp + -256)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (fld_range 3 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 3 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 3 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 3 t TV ltac:(lia)) as PV.
  unfold T2T_CONSTS, A_MINTAB, MASK47 in FR. cbn [app] in FR. unfold gcells, zb8 in HS.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = bv_unsigned sp + -256) by (apply unsigned_lit; lia).
  pose proof (mintab_cell m 3 MI ltac:(lia)) as TMIN. pose proof (maxtab_cell m 3 MI ltac:(lia)) as TMAX. pose proof (jtab_cell m 3 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  assert (U8 : bv_unsigned (Z_to_bv 8 (chi 3 t)) = chi 3 t) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
  (* [comment removed for export] *)
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_true. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAN; zify_cond KAN; [exfalso; repeat match type of KAN with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KAN; first [discriminate KAN | lia] | clear KAN].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAW; zify_cond KAW; [exfalso; rewrite ?unsigned_lit in KAW by lia; lia | clear KAW].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAZ; zify_cond KAZ; [exfalso; rewrite ?unsigned_lit in KAZ by lia; lia | clear KAZ].
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  rewrite U8. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -256))) with (lo := lo) (c := chi 3 t); rewrite ?ESP;
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m1. rewrite ?ESP in *.
  rewrite (isdigit_range (chi 3 t)) by lia.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KB4; [ exfalso; zify_cond KB4; rewrite ?U8, ?land64 in KB4; rewrite ?unsigned_lit in KB4 by lia; repeat match type of KB4 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KB4; first [discriminate KB4 | lia] | clear KB4 ].
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KB5; [ exfalso; zify_cond KB5; rewrite ?U8, ?land64 in KB5; rewrite ?unsigned_lit in KB5 by lia; repeat match type of KB5 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KB5; first [discriminate KB5 | lia] | clear KB5 ].
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  assert (U8C : bv_unsigned (Z_to_bv 8 (clo 3 t)) = clo 3 t) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
  rewrite U8C. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -256))) with (lo := lo) (c := clo 3 t); rewrite ?ESP;
      [exact ST2| assumption| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m2. rewrite ?ESP in *.
  rewrite (isdigit_range (clo 3 t)) by lia.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 8 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. rewrite U8, U8C, (sx32_small 1) by lia. replace (chi 3 t * 10 + clo 3 t + -528) with (fld 3 t) by lia. brF ltsz.
  do 4 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  rewrite ?U8, ?U8C, (sx32_small 31) by lia.
  replace (chi 3 t * 10 + clo 3 t + -528) with (fld 3 t) by lia.
  brF ltsz.
  (* [comment removed for export] *)
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 7 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  rewrite (sx32_small 24) by lia.
  replace (chi 3 t * 10 + clo 3 t + -480) with (fld 3 t + 48) by lia.
  apply evt_done. unfold t2t_iter_post. do 12 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iter_4 : t2t_iter_stmt 4.
Proof.
  unfold t2t_iter_stmt. intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS GS0 SHI FR TV MSR.
  unfold TIME_TO_TM_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 256 - 16 \/ bv_unsigned sp - 256 <= DA) by lia.
  assert (SEPS' : GS + 19 <= bv_unsigned sp - 256 - 16 \/ bv_unsigned sp - 256 <= GS) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp + -256)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (fld_range 4 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 4 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 4 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 4 t TV ltac:(lia)) as PV.
  unfold T2T_CONSTS, A_MINTAB, MASK47 in FR. cbn [app] in FR. unfold gcells, zb8 in HS.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = bv_unsigned sp + -256) by (apply unsigned_lit; lia).
  pose proof (mintab_cell m 4 MI ltac:(lia)) as TMIN. pose proof (maxtab_cell m 4 MI ltac:(lia)) as TMAX. pose proof (jtab_cell m 4 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  assert (U8 : bv_unsigned (Z_to_bv 8 (chi 4 t)) = chi 4 t) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
  (* [comment removed for export] *)
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_true. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAN; zify_cond KAN; [exfalso; repeat match type of KAN with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KAN; first [discriminate KAN | lia] | clear KAN].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAW; zify_cond KAW; [exfalso; rewrite ?unsigned_lit in KAW by lia; lia | clear KAW].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAZ; zify_cond KAZ; [exfalso; rewrite ?unsigned_lit in KAZ by lia; lia | clear KAZ].
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  rewrite U8. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -256))) with (lo := lo) (c := chi 4 t); rewrite ?ESP;
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m1. rewrite ?ESP in *.
  rewrite (isdigit_range (chi 4 t)) by lia.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KB4; [ exfalso; zify_cond KB4; rewrite ?U8, ?land64 in KB4; rewrite ?unsigned_lit in KB4 by lia; repeat match type of KB4 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KB4; first [discriminate KB4 | lia] | clear KB4 ].
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KB5; [ exfalso; zify_cond KB5; rewrite ?U8, ?land64 in KB5; rewrite ?unsigned_lit in KB5 by lia; repeat match type of KB5 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KB5; first [discriminate KB5 | lia] | clear KB5 ].
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  assert (U8C : bv_unsigned (Z_to_bv 8 (clo 4 t)) = clo 4 t) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
  rewrite U8C. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -256))) with (lo := lo) (c := clo 4 t); rewrite ?ESP;
      [exact ST2| assumption| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m2. rewrite ?ESP in *.
  rewrite (isdigit_range (clo 4 t)) by lia.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 8 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KC6; [ exfalso; zify_cond KC6; rewrite ?U8, ?land64 in KC6; rewrite ?unsigned_lit in KC6 by lia; repeat match type of KC6 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KC6; first [discriminate KC6 | lia] | clear KC6 ].
  do 4 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  rewrite U8, U8C, (sx32_small 23) by lia.
  replace (chi 4 t * 10 + clo 4 t + -528) with (fld 4 t) by lia.
  brF ltsz.
  (* [comment removed for export] *)
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 7 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  rewrite (sx32_small 24) by lia.
  replace (chi 4 t * 10 + clo 4 t + -480) with (fld 4 t + 48) by lia.
  apply evt_done. unfold t2t_iter_post. do 12 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iter_5 : t2t_iter_stmt 5.
Proof.
  unfold t2t_iter_stmt. intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS GS0 SHI FR TV MSR.
  unfold TIME_TO_TM_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 256 - 16 \/ bv_unsigned sp - 256 <= DA) by lia.
  assert (SEPS' : GS + 19 <= bv_unsigned sp - 256 - 16 \/ bv_unsigned sp - 256 <= GS) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp + -256)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (fld_range 5 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 5 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 5 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 5 t TV ltac:(lia)) as PV.
  unfold T2T_CONSTS, A_MINTAB, MASK47 in FR. cbn [app] in FR. unfold gcells, zb8 in HS.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = bv_unsigned sp + -256) by (apply unsigned_lit; lia).
  pose proof (mintab_cell m 5 MI ltac:(lia)) as TMIN. pose proof (maxtab_cell m 5 MI ltac:(lia)) as TMAX. pose proof (jtab_cell m 5 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  assert (U8 : bv_unsigned (Z_to_bv 8 (chi 5 t)) = chi 5 t) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
  (* [comment removed for export] *)
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_true. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAN; zify_cond KAN; [exfalso; destruct (Z.ltb_spec (GS + 10) 1); cbn in KAN; first [discriminate KAN | lia] | clear KAN].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAW; zify_cond KAW; [exfalso; rewrite ?unsigned_lit in KAW by lia; lia | clear KAW].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAZ; zify_cond KAZ; [exfalso; rewrite ?unsigned_lit in KAZ by lia; lia | clear KAZ].
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  rewrite U8. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -256))) with (lo := lo) (c := chi 5 t); rewrite ?ESP;
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m1. rewrite ?ESP in *.
  rewrite (isdigit_range (chi 5 t)) by lia.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KB4; [ exfalso; zify_cond KB4; rewrite ?U8, ?land64 in KB4; rewrite ?unsigned_lit in KB4 by lia; repeat match type of KB4 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KB4; first [discriminate KB4 | lia] | clear KB4 ].
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KB5; [ exfalso; zify_cond KB5; rewrite ?U8, ?land64 in KB5; rewrite ?unsigned_lit in KB5 by lia; repeat match type of KB5 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KB5; first [discriminate KB5 | lia] | clear KB5 ].
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  assert (U8C : bv_unsigned (Z_to_bv 8 (clo 5 t)) = clo 5 t) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
  rewrite U8C. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -256))) with (lo := lo) (c := clo 5 t); rewrite ?ESP;
      [exact ST2| assumption| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m2. rewrite ?ESP in *.
  rewrite (isdigit_range (clo 5 t)) by lia.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 8 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KC6; [ exfalso; zify_cond KC6; rewrite ?U8, ?land64 in KC6; rewrite ?unsigned_lit in KC6 by lia; repeat match type of KC6 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KC6; first [discriminate KC6 | lia] | clear KC6 ].
  do 4 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  rewrite U8, U8C, (sx32_small 59) by lia.
  replace (chi 5 t * 10 + clo 5 t + -528) with (fld 5 t) by lia.
  brF ltsz.
  (* [comment removed for export] *)
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 7 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  rewrite (sx32_small 24) by lia.
  replace (chi 5 t * 10 + clo 5 t + -480) with (fld 5 t + 48) by lia.
  apply evt_done. unfold t2t_iter_post. do 12 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iter_6 : t2t_iter_stmt 6.
Proof.
  unfold t2t_iter_stmt. intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS GS0 SHI FR TV MSR.
  unfold TIME_TO_TM_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 256 - 16 \/ bv_unsigned sp - 256 <= DA) by lia.
  assert (SEPS' : GS + 19 <= bv_unsigned sp - 256 - 16 \/ bv_unsigned sp - 256 <= GS) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp + -256)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (fld_range 6 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 6 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 6 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 6 t TV ltac:(lia)) as PV.
  unfold T2T_CONSTS, A_MINTAB, MASK47 in FR. cbn [app] in FR. unfold gcells, zb8 in HS.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = bv_unsigned sp + -256) by (apply unsigned_lit; lia).
  pose proof (mintab_cell m 6 MI ltac:(lia)) as TMIN. pose proof (maxtab_cell m 6 MI ltac:(lia)) as TMAX. pose proof (jtab_cell m 6 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  assert (U8 : bv_unsigned (Z_to_bv 8 (chi 6 t)) = chi 6 t) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
  (* [comment removed for export] *)
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  (* [comment removed for export] *)
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KN; zify_cond KN; [exfalso; destruct (Z.ltb_spec (GS + 12) 1); cbn in KN; first [discriminate KN | lia] | clear KN].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KW; zify_cond KW; [exfalso; rewrite ?unsigned_lit in KW by lia; lia | clear KW].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia | clear KZ].
  do 4 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KR; zify_cond KR; [exfalso; rewrite ?U8, ?land64 in KR; lia | clear KR].
  do 4 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with true by (symmetry; rewrite U8, land64, (mask47_digit (chi 6 t)) by lia; reflexivity) end; cbv iota.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAN; zify_cond KAN; [exfalso; destruct (Z.ltb_spec (GS + 12) 1); cbn in KAN; first [discriminate KAN | lia] | clear KAN].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAW; zify_cond KAW; [exfalso; rewrite ?unsigned_lit in KAW by lia; lia | clear KAW].
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KAZ; zify_cond KAZ; [exfalso; rewrite ?unsigned_lit in KAZ by lia; lia | clear KAZ].
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  rewrite U8. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -256))) with (lo := lo) (c := chi 6 t); rewrite ?ESP;
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m1. rewrite ?ESP in *.
  rewrite (isdigit_range (chi 6 t)) by lia.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KB4; [ exfalso; zify_cond KB4; rewrite ?U8, ?land64 in KB4; rewrite ?unsigned_lit in KB4 by lia; repeat match type of KB4 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KB4; first [discriminate KB4 | lia] | clear KB4 ].
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KB5; [ exfalso; zify_cond KB5; rewrite ?U8, ?land64 in KB5; rewrite ?unsigned_lit in KB5 by lia; repeat match type of KB5 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KB5; first [discriminate KB5 | lia] | clear KB5 ].
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  assert (U8C : bv_unsigned (Z_to_bv 8 (clo 6 t)) = clo 6 t) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
  rewrite U8C. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -256))) with (lo := lo) (c := clo 6 t); rewrite ?ESP;
      [exact ST2| assumption| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m2. rewrite ?ESP in *.
  rewrite (isdigit_range (clo 6 t)) by lia.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 5 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 8 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_cases KC6; [ exfalso; zify_cond KC6; rewrite ?U8, ?land64 in KC6; rewrite ?unsigned_lit in KC6 by lia; repeat match type of KC6 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in KC6; first [discriminate KC6 | lia] | clear KC6 ].
  do 4 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 3 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  rewrite U8, U8C, (sx32_small 59) by lia.
  replace (chi 6 t * 10 + clo 6 t + -528) with (fld 6 t) by lia.
  brF ltsz.
  (* [comment removed for export] *)
  do 2 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. if_false.
  do 7 OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
  (* [comment removed for export] *)
  rewrite (sx32_small 24) by lia.
  replace (chi 6 t * 10 + clo 6 t + -480) with (fld 6 t + 48) by lia.
  apply evt_done. unfold t2t_iter_post. do 12 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iter : forall i, 0 <= i <= 6 -> t2t_iter_stmt i.
Proof.
  intros i Hi. assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
  destruct H as [->|[->|[->|[->|[->|[->| ->]]]]]];
    [exact t2t_iter_0| exact t2t_iter_1| exact t2t_iter_2| exact t2t_iter_3| exact t2t_iter_4| exact t2t_iter_5| exact t2t_iter_6].
Qed.

End WithCeiling.
