(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From OSSVerify.Proofs.openssl.ct.lib.CtP Require Import Layout Lib_kit.
From OSSVerify.Proofs.openssl.ct.lib.CtBnP Require Import BnKit.
From OSSVerify.Proofs.openssl.ct.lib.CtRepP Require Import ApWalkTac.
From OSSVerify.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeKit2 TimeFmtPure TimeToTmDefs W_time_leaves W_time_to_tm_A.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
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
    (DA GS tm : Z) (t : tm6) (i : Z) (x23 x25 : word) : machine_state -> Prop :=
  fun ms' => exists (x1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte),
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -272)) gp tp x5 x6 x7 sp (Z_to_bv 64 (18 - 2 * i)) (Z_to_bv 64 (fld i t + 48))
                  (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (fld i t)) (Z_to_bv 64 (case_pc i)) x14 x15 x16 x17
                  (Z_to_bv 64 DA) (Z_to_bv 64 24) (Z_to_bv 64 i) (Z_to_bv 64 7) (Z_to_bv 64 (chi i t)) x23 (Z_to_bv 64 (2 * i)) x25
                  (Z_to_bv 64 12) (Z_to_bv 64 (GS + (2 * i + 1))) x28 x29 x30 x31)
             F (Z_to_bv 64 (case_pc i)) fc None m' (seg_rom ctpsegs)
    /\ munch [(lo, bv_unsigned sp + -272)]%Z m m' /\ wmono ctpsegs m m' /\ mem_inv ctpsegs m' /\ stk ctpsegs m' lo (bv_unsigned sp + -272).

Definition t2t_iter_stmt (i : Z) : Prop :=
  forall (x1 sp gp tp x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x25 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo DA GS tm ms : Z) (t : tm6) (tmc : list cell) (sv : list cell),
  stk ctpsegs m lo (bv_unsigned sp + -272) -> mem_inv ctpsegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  ro_cells ctpsegs m DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> (DA + 24 <= lo \/ bv_unsigned sp <= DA) -> DA + 24 <= 2^64 ->
  ro_cells ctpsegs m GS (gcells t ms) -> (GS + 19 <= lo \/ bv_unsigned sp <= GS) -> GS + 19 <= 2^63 ->
  rw_cells ctpsegs m (bv_unsigned sp + -272) (T2T_CONSTS 19 19 GS tm ++ tmc ++ sv) ->
  tm_valid t -> 0 <= ms < 1000 ->
  evt ctpsegs (t2t_iter_post sp gp tp F fc lo m DA GS tm t i x23 x25)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -272)) gp tp x5 x6 x7 sp (Z_to_bv 64 (18 - 2 * i)) x10 (Z_to_bv 64 i) x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 DA) x19 x20 (Z_to_bv 64 7) x22 x23 (Z_to_bv 64 (2 * i)) x25 (Z_to_bv 64 12) (Z_to_bv 64 (GS + (2 * i + 1))) x28 x29 x30 x31)
        F (Z_to_bv 64 0x11d480) fc None m (seg_rom ctpsegs)).

Lemma t2t_iter_0 : t2t_iter_stmt 0.
Proof.
  unfold t2t_iter_stmt. intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS SHI FR TV MSR.
  unfold TIME_TO_TM_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 272 - 16 \/ bv_unsigned sp - 272 <= DA) by lia.
  assert (SEPS' : GS + 19 <= bv_unsigned sp - 272 - 16 \/ bv_unsigned sp - 272 <= GS) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp + -272)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  pose proof (fld_range 0 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 0 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 0 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 0 t TV ltac:(lia)) as PV.
  unfold T2T_CONSTS, A_MINTAB, MASK47 in FR. cbn [app] in FR. unfold gcells, zb8 in HS.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -272)) = bv_unsigned sp + -272) by (apply unsigned_lit; lia).
  pose proof (mintab_cell m 0 MI ltac:(lia)) as TMIN. pose proof (maxtab_cell m 0 MI ltac:(lia)) as TMAX. pose proof (jtab_cell m 0 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (chi 0 t)) by lia. step.
  step. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. try clear K0.
  (* [comment removed for export] *)
  step. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -272))) with (lo := lo) (c := chi 0 t); rewrite ?ESP;
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctpsegs m1. rewrite ?ESP in *.
  rewrite (isdigit_range (chi 0 t)) by lia.
  match goal with H : stk ctpsegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. try clear K1.
  step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. try clear K2.
  step. rewrite (zxb_lit (chi 0 t)) by lia. step. rewrite (zxb_lit (clo 0 t)) by lia.
  step. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -272))) with (lo := lo) (c := clo 0 t); rewrite ?ESP;
      [exact ST2| assumption| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctpsegs m2. rewrite ?ESP in *.
  rewrite (isdigit_range (clo 0 t)) by lia.
  match goal with H : stk ctpsegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. try clear K3.
  step. step. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia|]. try clear K4.
  step. rewrite (sx32_small 24) by lia. zstep. step. step.
  step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|]. try clear K5.
  step.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (clo 0 t)) by lia. zstep. step. zstep. step. rewrite sx32_small by lia. step. zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (fld 0 t)) ltac:(wmodk PV CH2 CL2).
  step. brF ltsz.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia.
  step. brF ltsz.
  step. step. if_cases K6; zify_cond K6; [exfalso; rewrite ?unsigned_lit in K6 by lia; lia|]. try clear K6.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia. zstep. zstep.
  setreg 10%Z (Z_to_bv 64 (fld 0 t + 48)) ltac:(wmodk PV CH2 CL2).
  step.
  apply evt_done. unfold t2t_iter_post. do 12 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iter_1 : t2t_iter_stmt 1.
Proof.
  unfold t2t_iter_stmt. intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS SHI FR TV MSR.
  unfold TIME_TO_TM_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 272 - 16 \/ bv_unsigned sp - 272 <= DA) by lia.
  assert (SEPS' : GS + 19 <= bv_unsigned sp - 272 - 16 \/ bv_unsigned sp - 272 <= GS) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp + -272)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  pose proof (fld_range 1 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 1 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 1 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 1 t TV ltac:(lia)) as PV.
  unfold T2T_CONSTS, A_MINTAB, MASK47 in FR. cbn [app] in FR. unfold gcells, zb8 in HS.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -272)) = bv_unsigned sp + -272) by (apply unsigned_lit; lia).
  pose proof (mintab_cell m 1 MI ltac:(lia)) as TMIN. pose proof (maxtab_cell m 1 MI ltac:(lia)) as TMAX. pose proof (jtab_cell m 1 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (chi 1 t)) by lia. step.
  step. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. try clear K0.
  (* [comment removed for export] *)
  step. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -272))) with (lo := lo) (c := chi 1 t); rewrite ?ESP;
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctpsegs m1. rewrite ?ESP in *.
  rewrite (isdigit_range (chi 1 t)) by lia.
  match goal with H : stk ctpsegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. try clear K1.
  step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. try clear K2.
  step. rewrite (zxb_lit (chi 1 t)) by lia. step. rewrite (zxb_lit (clo 1 t)) by lia.
  step. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -272))) with (lo := lo) (c := clo 1 t); rewrite ?ESP;
      [exact ST2| assumption| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctpsegs m2. rewrite ?ESP in *.
  rewrite (isdigit_range (clo 1 t)) by lia.
  match goal with H : stk ctpsegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. try clear K3.
  step. step. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia|]. try clear K4.
  step. rewrite (sx32_small 24) by lia. zstep. step. step.
  step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|]. try clear K5.
  step.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (clo 1 t)) by lia. zstep. step. zstep. step. rewrite sx32_small by lia. step. zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (fld 1 t)) ltac:(wmodk PV CH2 CL2).
  step. brF ltsz.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia.
  step. brF ltsz.
  step. step. if_cases K6; zify_cond K6; [exfalso; rewrite ?unsigned_lit in K6 by lia; lia|]. try clear K6.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia. zstep. zstep.
  setreg 10%Z (Z_to_bv 64 (fld 1 t + 48)) ltac:(wmodk PV CH2 CL2).
  step.
  apply evt_done. unfold t2t_iter_post. do 12 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iter_2 : t2t_iter_stmt 2.
Proof.
  unfold t2t_iter_stmt. intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS SHI FR TV MSR.
  unfold TIME_TO_TM_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 272 - 16 \/ bv_unsigned sp - 272 <= DA) by lia.
  assert (SEPS' : GS + 19 <= bv_unsigned sp - 272 - 16 \/ bv_unsigned sp - 272 <= GS) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp + -272)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  pose proof (fld_range 2 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 2 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 2 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 2 t TV ltac:(lia)) as PV.
  unfold T2T_CONSTS, A_MINTAB, MASK47 in FR. cbn [app] in FR. unfold gcells, zb8 in HS.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -272)) = bv_unsigned sp + -272) by (apply unsigned_lit; lia).
  pose proof (mintab_cell m 2 MI ltac:(lia)) as TMIN. pose proof (maxtab_cell m 2 MI ltac:(lia)) as TMAX. pose proof (jtab_cell m 2 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (chi 2 t)) by lia. step.
  step. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. try clear K0.
  (* [comment removed for export] *)
  step. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -272))) with (lo := lo) (c := chi 2 t); rewrite ?ESP;
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctpsegs m1. rewrite ?ESP in *.
  rewrite (isdigit_range (chi 2 t)) by lia.
  match goal with H : stk ctpsegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. try clear K1.
  step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. try clear K2.
  step. rewrite (zxb_lit (chi 2 t)) by lia. step. rewrite (zxb_lit (clo 2 t)) by lia.
  step. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -272))) with (lo := lo) (c := clo 2 t); rewrite ?ESP;
      [exact ST2| assumption| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctpsegs m2. rewrite ?ESP in *.
  rewrite (isdigit_range (clo 2 t)) by lia.
  match goal with H : stk ctpsegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. try clear K3.
  step. step. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia|]. try clear K4.
  step. rewrite (sx32_small 24) by lia. zstep. step. step.
  step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|]. try clear K5.
  step.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (clo 2 t)) by lia. zstep. step. zstep. step. rewrite sx32_small by lia. step. zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (fld 2 t)) ltac:(wmodk PV CH2 CL2).
  step. brF ltsz.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia.
  step. brF ltsz.
  step. step. if_cases K6; zify_cond K6; [exfalso; rewrite ?unsigned_lit in K6 by lia; lia|]. try clear K6.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia. zstep. zstep.
  setreg 10%Z (Z_to_bv 64 (fld 2 t + 48)) ltac:(wmodk PV CH2 CL2).
  step.
  apply evt_done. unfold t2t_iter_post. do 12 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iter_3 : t2t_iter_stmt 3.
Proof.
  unfold t2t_iter_stmt. intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS SHI FR TV MSR.
  unfold TIME_TO_TM_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 272 - 16 \/ bv_unsigned sp - 272 <= DA) by lia.
  assert (SEPS' : GS + 19 <= bv_unsigned sp - 272 - 16 \/ bv_unsigned sp - 272 <= GS) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp + -272)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  pose proof (fld_range 3 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 3 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 3 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 3 t TV ltac:(lia)) as PV.
  unfold T2T_CONSTS, A_MINTAB, MASK47 in FR. cbn [app] in FR. unfold gcells, zb8 in HS.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -272)) = bv_unsigned sp + -272) by (apply unsigned_lit; lia).
  pose proof (mintab_cell m 3 MI ltac:(lia)) as TMIN. pose proof (maxtab_cell m 3 MI ltac:(lia)) as TMAX. pose proof (jtab_cell m 3 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (chi 3 t)) by lia. step.
  step. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. try clear K0.
  (* [comment removed for export] *)
  step. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -272))) with (lo := lo) (c := chi 3 t); rewrite ?ESP;
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctpsegs m1. rewrite ?ESP in *.
  rewrite (isdigit_range (chi 3 t)) by lia.
  match goal with H : stk ctpsegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. try clear K1.
  step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. try clear K2.
  step. rewrite (zxb_lit (chi 3 t)) by lia. step. rewrite (zxb_lit (clo 3 t)) by lia.
  step. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -272))) with (lo := lo) (c := clo 3 t); rewrite ?ESP;
      [exact ST2| assumption| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctpsegs m2. rewrite ?ESP in *.
  rewrite (isdigit_range (clo 3 t)) by lia.
  match goal with H : stk ctpsegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. try clear K3.
  step. step. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia|]. try clear K4.
  step. rewrite (sx32_small 24) by lia. zstep. step. step.
  step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|]. try clear K5.
  step.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (clo 3 t)) by lia. zstep. step. zstep. step. rewrite sx32_small by lia. step. zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (fld 3 t)) ltac:(wmodk PV CH2 CL2).
  step. brF ltsz.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia.
  step. brF ltsz.
  step. step. if_cases K6; zify_cond K6; [exfalso; rewrite ?unsigned_lit in K6 by lia; lia|]. try clear K6.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia. zstep. zstep.
  setreg 10%Z (Z_to_bv 64 (fld 3 t + 48)) ltac:(wmodk PV CH2 CL2).
  step.
  apply evt_done. unfold t2t_iter_post. do 12 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iter_4 : t2t_iter_stmt 4.
Proof.
  unfold t2t_iter_stmt. intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS SHI FR TV MSR.
  unfold TIME_TO_TM_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 272 - 16 \/ bv_unsigned sp - 272 <= DA) by lia.
  assert (SEPS' : GS + 19 <= bv_unsigned sp - 272 - 16 \/ bv_unsigned sp - 272 <= GS) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp + -272)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  pose proof (fld_range 4 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 4 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 4 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 4 t TV ltac:(lia)) as PV.
  unfold T2T_CONSTS, A_MINTAB, MASK47 in FR. cbn [app] in FR. unfold gcells, zb8 in HS.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -272)) = bv_unsigned sp + -272) by (apply unsigned_lit; lia).
  pose proof (mintab_cell m 4 MI ltac:(lia)) as TMIN. pose proof (maxtab_cell m 4 MI ltac:(lia)) as TMAX. pose proof (jtab_cell m 4 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (chi 4 t)) by lia. step.
  step. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. try clear K0.
  (* [comment removed for export] *)
  step. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -272))) with (lo := lo) (c := chi 4 t); rewrite ?ESP;
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctpsegs m1. rewrite ?ESP in *.
  rewrite (isdigit_range (chi 4 t)) by lia.
  match goal with H : stk ctpsegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. try clear K1.
  step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. try clear K2.
  step. rewrite (zxb_lit (chi 4 t)) by lia. step. rewrite (zxb_lit (clo 4 t)) by lia.
  step. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -272))) with (lo := lo) (c := clo 4 t); rewrite ?ESP;
      [exact ST2| assumption| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctpsegs m2. rewrite ?ESP in *.
  rewrite (isdigit_range (clo 4 t)) by lia.
  match goal with H : stk ctpsegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. try clear K3.
  step. step. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia|]. try clear K4.
  step. rewrite (sx32_small 24) by lia. zstep. step. step.
  step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|]. try clear K5.
  step.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (clo 4 t)) by lia. zstep. step. zstep. step. rewrite sx32_small by lia. step. zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (fld 4 t)) ltac:(wmodk PV CH2 CL2).
  step. brF ltsz.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia.
  step. brF ltsz.
  step. step. if_cases K6; zify_cond K6; [exfalso; rewrite ?unsigned_lit in K6 by lia; lia|]. try clear K6.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia. zstep. zstep.
  setreg 10%Z (Z_to_bv 64 (fld 4 t + 48)) ltac:(wmodk PV CH2 CL2).
  step.
  apply evt_done. unfold t2t_iter_post. do 12 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iter_5 : t2t_iter_stmt 5.
Proof.
  unfold t2t_iter_stmt. intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS SHI FR TV MSR.
  unfold TIME_TO_TM_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 272 - 16 \/ bv_unsigned sp - 272 <= DA) by lia.
  assert (SEPS' : GS + 19 <= bv_unsigned sp - 272 - 16 \/ bv_unsigned sp - 272 <= GS) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp + -272)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  pose proof (fld_range 5 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 5 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 5 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 5 t TV ltac:(lia)) as PV.
  unfold T2T_CONSTS, A_MINTAB, MASK47 in FR. cbn [app] in FR. unfold gcells, zb8 in HS.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -272)) = bv_unsigned sp + -272) by (apply unsigned_lit; lia).
  pose proof (mintab_cell m 5 MI ltac:(lia)) as TMIN. pose proof (maxtab_cell m 5 MI ltac:(lia)) as TMAX. pose proof (jtab_cell m 5 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (chi 5 t)) by lia. step.
  step. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. try clear K0.
  (* [comment removed for export] *)
  step. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -272))) with (lo := lo) (c := chi 5 t); rewrite ?ESP;
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctpsegs m1. rewrite ?ESP in *.
  rewrite (isdigit_range (chi 5 t)) by lia.
  match goal with H : stk ctpsegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. try clear K1.
  step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. try clear K2.
  step. rewrite (zxb_lit (chi 5 t)) by lia. step. rewrite (zxb_lit (clo 5 t)) by lia.
  step. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -272))) with (lo := lo) (c := clo 5 t); rewrite ?ESP;
      [exact ST2| assumption| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctpsegs m2. rewrite ?ESP in *.
  rewrite (isdigit_range (clo 5 t)) by lia.
  match goal with H : stk ctpsegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. try clear K3.
  step. step. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia|]. try clear K4.
  step. rewrite (sx32_small 24) by lia. zstep. step. step.
  step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|]. try clear K5.
  step.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (clo 5 t)) by lia. zstep. step. zstep. step. rewrite sx32_small by lia. step. zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (fld 5 t)) ltac:(wmodk PV CH2 CL2).
  step. brF ltsz.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia.
  step. brF ltsz.
  step. step. if_cases K6; zify_cond K6; [exfalso; rewrite ?unsigned_lit in K6 by lia; lia|]. try clear K6.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia. zstep. zstep.
  setreg 10%Z (Z_to_bv 64 (fld 5 t + 48)) ltac:(wmodk PV CH2 CL2).
  step.
  apply evt_done. unfold t2t_iter_post. do 12 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iter_6 : t2t_iter_stmt 6.
Proof.
  unfold t2t_iter_stmt. intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS SHI FR TV MSR.
  unfold TIME_TO_TM_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPD' : DA + 24 <= bv_unsigned sp - 272 - 16 \/ bv_unsigned sp - 272 <= DA) by lia.
  assert (SEPS' : GS + 19 <= bv_unsigned sp - 272 - 16 \/ bv_unsigned sp - 272 <= GS) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp + -272)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  pose proof (fld_range 6 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 6 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 6 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 6 t TV ltac:(lia)) as PV.
  unfold T2T_CONSTS, A_MINTAB, MASK47 in FR. cbn [app] in FR. unfold gcells, zb8 in HS.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -272)) = bv_unsigned sp + -272) by (apply unsigned_lit; lia).
  pose proof (mintab_cell m 6 MI ltac:(lia)) as TMIN. pose proof (maxtab_cell m 6 MI ltac:(lia)) as TMAX. pose proof (jtab_cell m 6 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (chi 6 t)) by lia. step.
  step. if_cases K0; zify_cond K0; [exfalso; apply K0; reflexivity|]. try clear K0.
  (* [comment removed for export] *)
  zstep. step. step. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|]. try clear KB.
  step. zstep. zstep.
  setreg 11%Z (Z_to_bv 64 0) ltac:(symmetry; f_equal; rewrite ?land64; apply mask47_digit; lia).
  step. if_cases KC; zify_cond KC; [exfalso; apply KC; reflexivity|]. try clear KC.
  (* [comment removed for export] *)
  step. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -272))) with (lo := lo) (c := chi 6 t); rewrite ?ESP;
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctpsegs m1. rewrite ?ESP in *.
  rewrite (isdigit_range (chi 6 t)) by lia.
  match goal with H : stk ctpsegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. try clear K1.
  step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. try clear K2.
  step. rewrite (zxb_lit (chi 6 t)) by lia. step. rewrite (zxb_lit (clo 6 t)) by lia.
  step. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_spec _ (Z_to_bv 64 (bv_unsigned sp + -272))) with (lo := lo) (c := clo 6 t); rewrite ?ESP;
      [exact ST2| assumption| unfold GLOBALS_TOP; lia| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctpsegs m2. rewrite ?ESP in *.
  rewrite (isdigit_range (clo 6 t)) by lia.
  match goal with H : stk ctpsegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. try clear K3.
  step. step. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia|]. try clear K4.
  step. rewrite (sx32_small 24) by lia. zstep. step. step.
  step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|]. try clear K5.
  step.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (clo 6 t)) by lia. zstep. step. zstep. step. rewrite sx32_small by lia. step. zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (fld 6 t)) ltac:(wmodk PV CH2 CL2).
  step. brF ltsz.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia.
  step. brF ltsz.
  step. step. if_cases K6; zify_cond K6; [exfalso; rewrite ?unsigned_lit in K6 by lia; lia|]. try clear K6.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia. zstep. zstep.
  setreg 10%Z (Z_to_bv 64 (fld 6 t + 48)) ltac:(wmodk PV CH2 CL2).
  step.
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
