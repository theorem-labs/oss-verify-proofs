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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeDefs TimeKit TimeKit2 TimeKit3 TimeFmtPure TimeToTmDefs W_time_leaves W_time_to_tm_A W_time_to_tm_it.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
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

Local Ltac brc :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    let v := eval vm_compute in c in
    lazymatch v with
    | true => replace (if c then a else b) with a by (vm_compute; reflexivity)
    | false => replace (if c then a else b) with b by (vm_compute; reflexivity)
    end
  end.
Local Ltac uchk1 := let C := fresh "C" in if_cases C; zify_cond C;
  [exfalso; repeat (rewrite Z.shiftl_mul_pow2 in C by lia); rewrite ?land64 in C; rewrite ?unsigned_lit in C by lia;
   rewrite ?ZBridge.zb_lxor_ones in C by lia; rewrite ?unsigned_lit in C by lia; lia | ]; try clear C.

Lemma addw_wrap : forall a b, bv_swrap 32 (bv_unsigned (Z_to_bv 64 a) + bv_unsigned (Z_to_bv 64 b)) = bv_swrap 32 (a + b).
Proof.
  intros a b. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_swrap, bv_wrap, bv_modulus, bv_half_modulus.
  change (2 ^ Z.of_N 64) with (4294967296 * 4294967296). change (2 ^ Z.of_N 32) with 4294967296. change (Z.of_N 32 - 1) with 31. change (2^31) with 2147483648.
  f_equal. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Ltac iter_call i tmcv mov yrv :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let IT := fresh "IT" in
    pose proof (t2t_iter i ltac:(lia)) as IT; unfold t2t_iter_stmt in IT;
    eapply evt_cut;
    [ eapply IT with (tmc := tmcv) (mo := mov) (yr := yrv); clear IT; try eassumption;
      unfold T2T_CONSTS, TM_CELLS, MASK47; cbn [app];
      match goal with H : rw_cells _ _ (bv_unsigned _ + -256) _ |- _ => exact H end
    | clear IT; intros ms' PO; unfold t2t_iter_post in PO; revert ms' PO; post_call ctusegs mx;
      match goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => let v := eval vm_compute in p in change p with v end ]
  end.

Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
Definition t2t_head_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte)
    (DA GS tm : Z) (t : tm6) (ms : Z) (i : Z) (mo yr : Z) (tmc sv : list cell) : machine_state -> Prop :=
  fun ms' => exists (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x27 x28 x29 x30 x31 : word) (m' : word -> option byte),
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 i) x11 x12 x13 x14 x15 x16 x17
                  (Z_to_bv 64 DA) (Z_to_bv 64 24) (Z_to_bv 64 19) x21 x22 (Z_to_bv 64 1) (Z_to_bv 64 (2 * i)) (Z_to_bv 64 GS)
                  (Z_to_bv 64 12) x27 x28 x29 x30 x31)
             F (Z_to_bv 64 0x12c298) fc None m' (seg_rom ctusegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp + -256)
    /\ rw_cells ctusegs m' (bv_unsigned sp + -256) (T2T_CONSTS 19 mo yr tm ++ tmc ++ sv).

Lemma t2t_segB : forall (x1 sp gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo DA GS tm ms : Z) (t : tm6) (sv : list cell),
  stk ctusegs m lo (bv_unsigned sp + -256) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  ro_cells ctusegs m DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> (DA + 24 <= lo \/ bv_unsigned sp <= DA) -> DA + 24 <= 2^64 ->
  ro_cells ctusegs m GS (gcells t ms) -> (GS + 19 <= lo \/ bv_unsigned sp <= GS) -> 0 < GS -> GS + 19 <= 2^63 ->
  rw_cells ctusegs m (bv_unsigned sp + -256) (T2T_CONSTS 19 0 0 tm ++ TM_CELLS 0 0 0 0 0 0 0 0 ++ sv) -> cells_size sv = 104%nat ->
  tm_valid t -> 0 <= ms < 1000 ->
  evt ctusegs (t2t_head_post sp gp tp F fc lo m DA GS tm t ms 3 (t_mon t - 1) (t_year t - 1900)
                 (TM_CELLS 0 0 0 0 (t_mon t - 1) (t_year t - 1900) 0 0) sv)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 DA) (Z_to_bv 64 24) (Z_to_bv 64 19) x21 x22 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 GS) (Z_to_bv 64 12) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x12c298) fc None m (seg_rom ctusegs)).
Proof.
  intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS GS0 SHI FR SVS TV MSR.
  pose proof LO as LO'. unfold TIME_TO_TM_STACK, GLOBALS_TOP in LO', GLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof TV as (VY & VMO & VMD & VHH & VMI & VSS).
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  unfold gcells, zb8 in HS. unfold T2T_CONSTS, TM_CELLS, MASK47 in FR. cbn [app] in FR.
  (* [comment removed for export] *)
  iter_call 0 (TM_CELLS 0 0 0 0 0 0 0 0) 0 0. name_mem m1.
  pose proof (fld_range 0 t TV ltac:(lia)) as [F00 F01]. cbv [mintab maxtab Z.eqb orb Pos.eqb] in F00.
  (* [comment removed for export] *)
  step. zstep. zstep. step. step. step. step.
  zstep. step. step. brc.
  (* [comment removed for export] *)
  iter_call 1 (TM_CELLS 0 0 0 0 0 (fld 0 t * 100 + -1900) 0 0) 0 (fld 0 t * 100 + -1900). name_mem m2.
  pose proof (fld_range 1 t TV ltac:(lia)) as [F10 F11]. cbv [mintab maxtab Z.eqb orb Pos.eqb] in F10.
  (* [comment removed for export] *)
  step. step. brc.
  assert (YE : fld 0 t * 100 + -1900 + fld 1 t = t_year t - 1900).
  { unfold fld. cbv [Z.eqb Pos.eqb]. pose proof (Z.div_mod (t_year t) 100 ltac:(lia)). lia. }
  match goal with H : rw_cells ctusegs _ (bv_unsigned sp + -256) _ |- _ => rename H into FR1 end.
  yr_split 9%nat FR1. step. rewrite (sx32_signed (fld 0 t * 100 + -1900)) by lia. yr_join 9%nat FR1.
  step. setreg 13%Z (Z_to_bv 64 (t_year t - 1900)) ltac:(rewrite <- YE; wmod).
  step. setreg 11%Z (Z_to_bv 64 (t_year t - 1900)) ltac:(rewrite <- YE; first [w32k F11 F01 VY| rewrite addw_wrap, swrap32_small by (clear - F11 F01 VY; lia); reflexivity]).
  step.
  step. uchk1. step. step. step.
  zstep. step. step. brc.
  (* [comment removed for export] *)
  iter_call 2 (TM_CELLS 0 0 0 0 0 (t_year t - 1900) 0 0) 0 (t_year t - 1900). name_mem m3.
  pose proof (fld_range 2 t TV ltac:(lia)) as [F20 F21]. cbv [mintab maxtab Z.eqb orb Pos.eqb] in F20.
  (* [comment removed for export] *)
  zstep. setreg 11%Z (Z_to_bv 64 (t_mon t - 1)) ltac:(unfold fld; cbv [Z.eqb Pos.eqb]; w32k F21 VMO).
  step. step. step.
  zstep. step. step. brc.
  name_mem m4. apply evt_done. unfold t2t_head_post. do 19 eexists. exists m4. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold T2T_CONSTS, TM_CELLS, MASK47. cbn [app]. assumption.
Qed.

End WithCeiling.
