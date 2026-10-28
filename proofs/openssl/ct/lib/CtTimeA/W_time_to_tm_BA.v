(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeKit TimeKit2 TimeKit3 TimeFmtPure TimeToTmDefs W_time_to_tm_it.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA TimeKitA W_time_leavesA TimeToTmDefsA W_time_to_tm_itA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.      (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac brc :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    let v := eval vm_compute in c in
    lazymatch v with
    | true => replace (if c then a else b) with a by (vm_compute; reflexivity)
    | false => replace (if c then a else b) with b by (vm_compute; reflexivity)
    end
  end.

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
Lemma addw_wrap : forall a b, bv_swrap 32 (bv_unsigned (Z_to_bv 64 a) + bv_unsigned (Z_to_bv 64 b)) = bv_swrap 32 (a + b).
Proof.
  intros a b. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_swrap, bv_wrap, bv_modulus, bv_half_modulus.
  change (2 ^ Z.of_N 64) with (4294967296 * 4294967296). change (2 ^ Z.of_N 32) with 4294967296. change (Z.of_N 32 - 1) with 31. change (2^31) with 2147483648.
  f_equal. Z.div_mod_to_equations. lia.
Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.

(* [comment removed for export] *)
Ltac iter_callA i m0 MU OFF ACCD ACCS ACCMIN ACCMAX :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let IT := fresh "IT" in
    pose proof (t2t_iterA i ltac:(lia)) as IT; unfold t2t_iterA_stmt in IT;
    eapply evt_cut;
    [ eapply IT; clear IT; try eassumption;
      first [ unfold t2t_lowA, MASK47, gcells, zb8; match goal with H : rw_cells _ mx _ _ |- _ => exact H end
            | eapply (acc_munch ctasegs _ m0 mx); [ first [exact ACCD | exact ACCS | exact ACCMIN | exact ACCMAX] | exact MU | exact OFF | unfold A_MINTAB_A, A_MAXTAB_A; alia | unfold A_MINTAB_A, A_MAXTAB_A; alia ]
            | alia ]
    | clear IT; intros ms' PO; unfold t2t_iterA_post in PO; revert ms' PO; post_call ctasegs mx;
      match goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => let v := eval vm_compute in p in change p with v end ]
  end.

(* [comment removed for export] *)
Definition t2t_headA_post (sp : word) (spa : Z) (gp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte)
    (f DA GS tm : Z) (i mon year : Z) (tmc : list cell) (j0 j192 j200 junk : list byte) (g : nat) : machine_state -> Prop :=
  fun ms' => exists (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x27 x28 x29 x30 x31 : word) (m' : word -> option byte),
    ms' = MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 (Z_to_bv 64 i) x12 x13 x14 x15 x16 x17
                  x18 x19 (Z_to_bv 64 SHB) (Z_to_bv 64 (2 * i)) x22 x23 (Z_to_bv 64 (2 * i)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) x27 x28 x29 x30 x31)
             F (Z_to_bv 64 T2T_HEAD_A) fc None m' (seg_rom ctasegs)
    /\ munch [(lo, spa + 232); (f + 32, f + 32 + 56)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo spa
    /\ rw_cells ctasegs m' spa (t2t_lowA j0 j192 j200 19 tm f DA GS mon year g junk)
    /\ rw_cells ctasegs m' (f + 32) tmc.

Lemma t2t_segBA : forall (x1 sp gp x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo spa f DA GS tm mon year ms : Z) (t : tm6)
         (j0 j192 j200 junk : list byte) (g : nat),
  stk ctasegs m lo spa -> mem_inv ctasegs m -> ACEIL <= lo -> lo + 16 <= spa -> spa + 304 <= USTACK_TOP -> spa mod 16 = 0 ->
  SEGTOP_A <= ACEIL -> SHHI <= ACEIL -> ACEIL + STACK_WIN <= USTACK_TOP ->
  rw_cells ctasegs m DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> acc ctasegs m DA 16 -> DA mod 8 = 0 ->
  0 < DA -> DA + 16 <= ACEIL ->
  rw_cells ctasegs m GS (gcells t ms) -> acc ctasegs m GS 19 -> GS mod 8 = 0 -> 0 < GS -> GS + 19 <= ACEIL ->
  rw_cells ctasegs m spa (t2t_lowA j0 j192 j200 19 tm f DA GS mon year g junk) ->
  acc ctasegs m A_MINTAB_A 36 -> acc ctasegs m A_MAXTAB_A 36 ->
  tm_valid t -> 0 <= ms < 1000 -> 0 <= f -> f + 128 <= ACEIL -> f mod 8 = 0 -> (f + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= f) ->
  (DA + 16 <= f + 32 \/ f + 32 + 56 <= DA) -> (GS + 19 <= f + 32 \/ f + 32 + 56 <= GS) ->
  rw_cells ctasegs m (f + 32) (TM_CELLS_A 0 0 0 0 0 0 0 0) ->
  evt ctasegs (t2t_headA_post sp spa gp F fc lo m f DA GS tm 3 (t_mon t - 1) (t_year t - 1900)
                 (TM_CELLS_A 0 0 0 0 (t_mon t - 1) (t_year t - 1900) 0 0) j0 j192 j200 junk g)
    (MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 SHB) (Z_to_bv 64 0) x22 x23 (Z_to_bv 64 0) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 T2T_HEAD_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until g. intros ST MI CEIL LO TOP AL16 C1 C2 C3 HD ACCD ALD D0 DHI HS ACCS ALS S0 SHI LOW ACCMIN ACCMAX TV MSR F0 FHI F8 FG5 SEPD SEPS TMP.
  unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, TOP. pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu, C1, C2, C3, DHI, SHI, FHI.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  pose proof TV as (VY & VMO & VMD & VHH & VMI & VSS).
  pose proof (munch_refl [(lo, spa + 232); (f + 32, f + 32 + 56)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(lo, spa + 232); (f + 32, f + 32 + 56)]%Z) by (cbn [offshW]; alia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - LO LO0 TOP; lia).
  assert (SEPT : f + 32 + 56 <= spa - 16 \/ spa + 304 <= f + 32) by (clear - FHI CEILu LO; lia).
  unfold TM_CELLS_A in TMP. unfold t2t_lowA, MASK47 in LOW. unfold gcells, zb8 in HS.
  (* [comment removed for export] *)
  iter_callA 0 m MU OFF ACCD ACCS ACCMIN ACCMAX. name_mem m1.
  pose proof (fld_range 0 t TV ltac:(lia)) as [F00 F01]. cbv [mintab maxtab Z.eqb orb Pos.eqb] in F00.
  (* [comment removed for export] *)
  step. zstep. zstep. step. step. step. step.
  zstep. try rewrite (swrap32_small (2 * 0 + 2)) by lia. zstep. step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  iter_callA 1 m MU OFF ACCD ACCS ACCMIN ACCMAX. name_mem m2.
  pose proof (fld_range 1 t TV ltac:(lia)) as [F10 F11]. cbv [mintab maxtab Z.eqb orb Pos.eqb] in F10.
  (* [comment removed for export] *)
  step. step. brc.
  assert (YE : fld 0 t * 100 + -1900 + fld 1 t = t_year t - 1900).
  { unfold fld. cbv [Z.eqb Pos.eqb]. pose proof (Z.div_mod (t_year t) 100 ltac:(lia)). lia. }
  match goal with H : rw_cells ctasegs _ spa _ |- _ => rename H into FR1 end.
  step. zstep. setreg 10%Z (Z_to_bv 64 (t_year t - 1900)) ltac:(rewrite <- YE; wmod).
  step.
  step.
  step. (* [comment removed for export] *)
  zstep. try rewrite (swrap32_small (2 * 1 + 2)) by lia. zstep. step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  iter_callA 2 m MU OFF ACCD ACCS ACCMIN ACCMAX. name_mem m3.
  pose proof (fld_range 2 t TV ltac:(lia)) as [F20 F21]. cbv [mintab maxtab Z.eqb orb Pos.eqb] in F20.
  (* [comment removed for export] *)
  zstep. setreg 10%Z (Z_to_bv 64 (t_mon t - 1)) ltac:(unfold fld; cbv [Z.eqb Pos.eqb]; w32k F21 VMO).
  step. step. step.
  zstep. try rewrite (swrap32_small (2 * 2 + 2)) by lia. zstep. step. step. brc.
  (* [comment removed for export] *)
  name_mem m4. apply evt_done. unfold t2t_headA_post. do 20 eexists. exists m4. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [unfold t2t_lowA, MASK47; assumption| unfold TM_CELLS_A; assumption].
Qed.

End WithRT.
