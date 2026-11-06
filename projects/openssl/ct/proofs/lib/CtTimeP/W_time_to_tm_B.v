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
From OSSVerify.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeKit2 TimeFmtPure TimeToTmDefs W_time_leaves W_time_to_tm_A W_time_to_tm_it.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

(* [comment removed for export] *)
Ltac iter_call i tmcv :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let IT := fresh "IT" in
    pose proof (t2t_iter i ltac:(lia)) as IT; unfold t2t_iter_stmt in IT;
    eapply evt_cut;
    [ eapply IT with (tmc := tmcv); clear IT; try eassumption;
      unfold T2T_CONSTS, TM_CELLS, A_MINTAB, MASK47; cbn [app];
      match goal with H : rw_cells _ _ (bv_unsigned _ + -272) _ |- _ => exact H end
    | clear IT; intros ms' PO; unfold t2t_iter_post in PO; revert ms' PO; post_call ctpsegs mx;
      match goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => let v := eval vm_compute in p in change p with v end ]
  end.

Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
Definition t2t_head_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte)
    (DA GS tm : Z) (t : tm6) (ms : Z) (i : Z) (x23 x25 : word) (tmc sv : list cell) : machine_state -> Prop :=
  fun ms' => exists (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x22 x28 x29 x30 x31 : word) (m' : word -> option byte),
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -272)) gp tp x5 x6 x7 sp (Z_to_bv 64 (18 - 2 * i)) x10 (Z_to_bv 64 i) x12 x13 x14 x15 x16 x17
                  (Z_to_bv 64 DA) x19 x20 (Z_to_bv 64 7) x22 x23 (Z_to_bv 64 (2 * i)) x25 (Z_to_bv 64 12) (Z_to_bv 64 (GS + (2 * i + 1))) x28 x29 x30 x31)
             F (Z_to_bv 64 0x11d480) fc None m' (seg_rom ctpsegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono ctpsegs m m' /\ mem_inv ctpsegs m' /\ stk ctpsegs m' lo (bv_unsigned sp + -272)
    /\ rw_cells ctpsegs m' (bv_unsigned sp + -272) (T2T_CONSTS 19 19 GS tm ++ tmc ++ sv).

Lemma t2t_segB : forall (x1 sp gp tp x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x22 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo DA GS tm ms : Z) (t : tm6) (sv : list cell),
  stk ctpsegs m lo (bv_unsigned sp + -272) -> mem_inv ctpsegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  ro_cells ctpsegs m DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> (DA + 24 <= lo \/ bv_unsigned sp <= DA) -> DA + 24 <= 2^64 ->
  ro_cells ctpsegs m GS (gcells t ms) -> (GS + 19 <= lo \/ bv_unsigned sp <= GS) -> GS + 19 <= 2^63 ->
  rw_cells ctpsegs m (bv_unsigned sp + -272) (T2T_CONSTS 19 19 GS tm ++ TM_CELLS 0 0 0 0 0 0 0 0 ++ sv) -> cells_size sv = 104%nat ->
  tm_valid t -> 0 <= ms < 1000 ->
  evt ctpsegs (t2t_head_post sp gp tp F fc lo m DA GS tm t ms 3 (Z_to_bv 64 (t_year t - 1900)) (Z_to_bv 64 (t_mon t - 1))
                 (TM_CELLS 0 0 0 0 (t_mon t - 1) (t_year t - 1900) 0 0) sv)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -272)) gp tp x5 x6 x7 sp (Z_to_bv 64 18) x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 DA) x19 x20 (Z_to_bv 64 7) x22 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 12) (Z_to_bv 64 (GS + 1)) x28 x29 x30 x31)
        F (Z_to_bv 64 0x11d480) fc None m (seg_rom ctpsegs)).
Proof.
  intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS SHI FR SVS TV MSR.
  pose proof LO as LO'. unfold TIME_TO_TM_STACK, GLOBALS_TOP in LO', GLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof TV as (VY & VMO & VMD & VHH & VMI & VSS).
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  unfold gcells, zb8 in HS. unfold T2T_CONSTS, TM_CELLS, A_MINTAB, MASK47 in FR. cbn [app] in FR.
  (* [comment removed for export] *)
  iter_call 0 (TM_CELLS 0 0 0 0 0 0 0 0). name_mem m1.
  pose proof (fld_range 0 t TV ltac:(lia)) as [F00 F01]. cbv [mintab maxtab Z.eqb orb Pos.eqb] in F00.
  (* [comment removed for export] *)
  step. zstep. zstep. step. step. step.
  zstep. zstep. zstep. step. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. try clear K0.
  (* [comment removed for export] *)
  iter_call 1 (TM_CELLS 0 0 0 0 0 (fld 0 t * 100 + -1900) 0 0). name_mem m2.
  pose proof (fld_range 1 t TV ltac:(lia)) as [F10 F11]. cbv [mintab maxtab Z.eqb orb Pos.eqb] in F10.
  (* [comment removed for export] *)
  step. step. if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia]. try clear K1.
  zstep.
  assert (YE : fld 0 t * 100 + -1900 + fld 1 t = t_year t - 1900).
  { unfold fld. cbv [Z.eqb Pos.eqb]. pose proof (Z.div_mod (t_year t) 100 ltac:(lia)). lia. }
  rewrite YE. step. step.
  zstep. zstep. zstep. step. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. try clear K0.
  (* [comment removed for export] *)
  iter_call 2 (TM_CELLS 0 0 0 0 0 (t_year t - 1900) 0 0). name_mem m3.
  pose proof (fld_range 2 t TV ltac:(lia)) as [F20 F21]. cbv [mintab maxtab Z.eqb orb Pos.eqb] in F20.
  (* [comment removed for export] *)
  zstep. setreg 25%Z (Z_to_bv 64 (t_mon t - 1)) ltac:(unfold fld; cbv [Z.eqb Pos.eqb]; w32k F21 VMO).
  step. step.
  zstep. zstep. zstep. step. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. try clear K0.
  name_mem m4. apply evt_done. unfold t2t_head_post. do 18 eexists. exists m4. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold T2T_CONSTS, TM_CELLS, A_MINTAB, MASK47. cbn [app]. assumption.
Qed.

End WithCeiling.
