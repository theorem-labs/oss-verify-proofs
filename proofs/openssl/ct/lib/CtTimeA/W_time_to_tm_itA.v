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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeKit TimeKit2 TimeFmtPure TimeToTmDefs W_time_to_tm_it.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA TimeKitA W_time_leavesA TimeToTmDefsA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.      (* [comment removed for export] *)
Local Ltac shz := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; rewrite ?zxb_z8, ?sxb_z8; if_false.
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

Section WithRT.
Context {AR : ARun}.
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.

(* [comment removed for export] *)
Definition t2t_iterA_post (sp : word) (spa : Z) (gp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte)
    (f DA GS : Z) (t : tm6) (i : Z) : machine_state -> Prop :=
  fun ms' => exists (x1 x5 x6 x7 x10 x15 x16 x17 x18 x27 x28 x29 x30 x31 : word) (m' : word -> option byte),
    ms' = MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10
                  (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (fld i t + 48)) (Z_to_bv 64 (fld i t)) (Z_to_bv 64 24) x15 x16 x17
                  x18 (Z_to_bv 64 i) (Z_to_bv 64 SHB) (Z_to_bv 64 (2 * i)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (DA + 4))
                  (Z_to_bv 64 (2 * i)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) x27 x28 x29 x30 x31)
             F (Z_to_bv 64 (case_pcA i)) fc None m' (seg_rom ctasegs)
    /\ munch [(lo, spa)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo spa.

Definition t2t_iterA_stmt (i : Z) : Prop :=
  forall (x1 sp gp x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo spa f DA GS tm mon year ms : Z) (t : tm6)
         (j0 j192 j200 junk : list byte) (g : nat),
  stk ctasegs m lo spa -> mem_inv ctasegs m -> ACEIL <= lo -> lo + 16 <= spa -> spa + 304 <= USTACK_TOP -> spa mod 16 = 0 ->
  SEGTOP_A <= ACEIL -> SHHI <= ACEIL -> ACEIL + STACK_WIN <= USTACK_TOP ->
  rw_cells ctasegs m DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> acc ctasegs m DA 16 -> DA mod 8 = 0 ->
  0 < DA -> DA + 16 <= ACEIL ->
  rw_cells ctasegs m GS (gcells t ms) -> acc ctasegs m GS 19 -> GS mod 8 = 0 -> 0 < GS -> GS + 19 <= ACEIL ->
  rw_cells ctasegs m spa (t2t_lowA j0 j192 j200 19 tm f DA GS mon year g junk) ->
  acc ctasegs m A_MINTAB_A 36 -> acc ctasegs m A_MAXTAB_A 36 ->
  tm_valid t -> 0 <= ms < 1000 -> 0 <= f -> f + 128 <= ACEIL ->
  evt ctasegs (t2t_iterA_post sp spa gp F fc lo m f DA GS t i)
    (MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 (Z_to_bv 64 i) x12 x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 SHB) (Z_to_bv 64 (2 * i)) x22 x23 (Z_to_bv 64 (2 * i)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 T2T_HEAD_A) fc None m (seg_rom ctasegs)).

Lemma t2t_iterA_0 : t2t_iterA_stmt 0.
Proof.
  unfold t2t_iterA_stmt. intros until g. intros ST MI CEIL LO TOP AL16 C1 C2 C3 HD ACCD ALD D0 DHI HS ACCS ALS S0 SHI LOW ACCMIN ACCMAX TV MSR F0 FHI.
  unfold T2T_HEAD_A in *. unfold A_MINTAB_A in ACCMIN. unfold A_MAXTAB_A in ACCMAX.
  unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, TOP. pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu, C1, C2, C3, DHI, SHI, FHI.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  pose proof (munch_refl [(lo, spa)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(lo, spa)]%Z) by (cbn [offshW]; alia).
  pose proof (fld_range 0 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 0 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 0 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 0 t TV ltac:(lia)) as PV.
  unfold t2t_lowA, MASK47 in LOW. unfold gcells, zb8 in HS.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - LO LO0 TOP; alia).
  pose proof (mintabA_cell m 0 MI ltac:(lia)) as TMIN. pose proof (maxtabA_cell m 0 MI ltac:(lia)) as TMAX. pose proof (jtabA_cell m 0 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  (* [comment removed for export] *)
  step. step. step. step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. ab_shload 1. shz.
  step. rewrite (zxb_lit (chi 0 t)) by lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_specA _ (Z_to_bv 64 spa)) with (lo := lo) (c := chi 0 t); rewrite ?ESPA;
      [exact ST| exact MI| exact CEIL| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO. post_call ctasegs m1. rewrite ?ESPA in *.
  rewrite (isdigit_range (chi 0 t)) by lia.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  step. brc.
  ab_shload 1. shz.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. step. ab_shload 1. step. rewrite (zxb_lit (chi 0 t)) by lia. shz.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (clo 0 t)) by lia.
  step. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_specA _ (Z_to_bv 64 spa)) with (lo := lo) (c := clo 0 t); rewrite ?ESPA;
      [exact ST2| assumption| exact CEIL| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO. post_call ctasegs m2. rewrite ?ESPA in *.
  rewrite (isdigit_range (clo 0 t)) by lia.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  step. brc.
  ab_shload 1. shz.
  step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. ab_shload 4. step. rewrite (zxb_lit (clo 0 t)) by lia. shz.
  (* [comment removed for export] *)
  step. step. rewrite (sx32_small 24) by lia. step. try rewrite (swrap32_small (0 + 1)) by lia.
  step. step. step. step. brc. step. step. step. step. step.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. ab_shload 4. shz.
  zstep. zstep. step. rewrite sx32_small by lia. zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (fld 0 t + 48)) ltac:(wmodk PV CH2 CL2).
  setreg 13%Z (Z_to_bv 64 (fld 0 t)) ltac:(wmodk PV CH2 CL2).
  step. if_cases KM; zify_cond KM; [exfalso; rewrite ?ab_signed_small, ?signed_lit in KM by lia; lia|]. try clear KM.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. step. ab_shload 4. shz.
  zstep. rewrite sx32_small by lia.
  step. if_cases KX; zify_cond KX; [exfalso; rewrite ?ab_signed_small, ?signed_lit in KX by lia; lia|]. try clear KX.
  step. step. brc.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia. zstep.
  step.
  (* [comment removed for export] *)
  apply evt_done. unfold t2t_iterA_post. do 14 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iterA_1 : t2t_iterA_stmt 1.
Proof.
  unfold t2t_iterA_stmt. intros until g. intros ST MI CEIL LO TOP AL16 C1 C2 C3 HD ACCD ALD D0 DHI HS ACCS ALS S0 SHI LOW ACCMIN ACCMAX TV MSR F0 FHI.
  unfold T2T_HEAD_A in *. unfold A_MINTAB_A in ACCMIN. unfold A_MAXTAB_A in ACCMAX.
  unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, TOP. pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu, C1, C2, C3, DHI, SHI, FHI.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  pose proof (munch_refl [(lo, spa)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(lo, spa)]%Z) by (cbn [offshW]; alia).
  pose proof (fld_range 1 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 1 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 1 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 1 t TV ltac:(lia)) as PV.
  unfold t2t_lowA, MASK47 in LOW. unfold gcells, zb8 in HS.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - LO LO0 TOP; alia).
  pose proof (mintabA_cell m 1 MI ltac:(lia)) as TMIN. pose proof (maxtabA_cell m 1 MI ltac:(lia)) as TMAX. pose proof (jtabA_cell m 1 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  (* [comment removed for export] *)
  step. step. step. step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. ab_shload 1. shz.
  step. rewrite (zxb_lit (chi 1 t)) by lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_specA _ (Z_to_bv 64 spa)) with (lo := lo) (c := chi 1 t); rewrite ?ESPA;
      [exact ST| exact MI| exact CEIL| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO. post_call ctasegs m1. rewrite ?ESPA in *.
  rewrite (isdigit_range (chi 1 t)) by lia.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  step. brc.
  ab_shload 1. shz.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. step. ab_shload 1. step. rewrite (zxb_lit (chi 1 t)) by lia. shz.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (clo 1 t)) by lia.
  step. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_specA _ (Z_to_bv 64 spa)) with (lo := lo) (c := clo 1 t); rewrite ?ESPA;
      [exact ST2| assumption| exact CEIL| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO. post_call ctasegs m2. rewrite ?ESPA in *.
  rewrite (isdigit_range (clo 1 t)) by lia.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  step. brc.
  ab_shload 1. shz.
  step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. ab_shload 4. step. rewrite (zxb_lit (clo 1 t)) by lia. shz.
  (* [comment removed for export] *)
  step. step. rewrite (sx32_small 24) by lia. step. try rewrite (swrap32_small (1 + 1)) by lia.
  step. step. step. step. brc. step. step. step. step. step.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. ab_shload 4. shz.
  zstep. zstep. step. rewrite sx32_small by lia. zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (fld 1 t + 48)) ltac:(wmodk PV CH2 CL2).
  setreg 13%Z (Z_to_bv 64 (fld 1 t)) ltac:(wmodk PV CH2 CL2).
  step. if_cases KM; zify_cond KM; [exfalso; rewrite ?ab_signed_small, ?signed_lit in KM by lia; lia|]. try clear KM.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. step. ab_shload 4. shz.
  zstep. rewrite sx32_small by lia.
  step. if_cases KX; zify_cond KX; [exfalso; rewrite ?ab_signed_small, ?signed_lit in KX by lia; lia|]. try clear KX.
  step. step. brc.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia. zstep.
  step.
  (* [comment removed for export] *)
  apply evt_done. unfold t2t_iterA_post. do 14 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iterA_2 : t2t_iterA_stmt 2.
Proof.
  unfold t2t_iterA_stmt. intros until g. intros ST MI CEIL LO TOP AL16 C1 C2 C3 HD ACCD ALD D0 DHI HS ACCS ALS S0 SHI LOW ACCMIN ACCMAX TV MSR F0 FHI.
  unfold T2T_HEAD_A in *. unfold A_MINTAB_A in ACCMIN. unfold A_MAXTAB_A in ACCMAX.
  unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, TOP. pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu, C1, C2, C3, DHI, SHI, FHI.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  pose proof (munch_refl [(lo, spa)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(lo, spa)]%Z) by (cbn [offshW]; alia).
  pose proof (fld_range 2 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 2 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 2 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 2 t TV ltac:(lia)) as PV.
  unfold t2t_lowA, MASK47 in LOW. unfold gcells, zb8 in HS.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - LO LO0 TOP; alia).
  pose proof (mintabA_cell m 2 MI ltac:(lia)) as TMIN. pose proof (maxtabA_cell m 2 MI ltac:(lia)) as TMAX. pose proof (jtabA_cell m 2 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  (* [comment removed for export] *)
  step. step. step. step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. ab_shload 1. shz.
  step. rewrite (zxb_lit (chi 2 t)) by lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_specA _ (Z_to_bv 64 spa)) with (lo := lo) (c := chi 2 t); rewrite ?ESPA;
      [exact ST| exact MI| exact CEIL| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO. post_call ctasegs m1. rewrite ?ESPA in *.
  rewrite (isdigit_range (chi 2 t)) by lia.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  step. brc.
  ab_shload 1. shz.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. step. ab_shload 1. step. rewrite (zxb_lit (chi 2 t)) by lia. shz.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (clo 2 t)) by lia.
  step. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_specA _ (Z_to_bv 64 spa)) with (lo := lo) (c := clo 2 t); rewrite ?ESPA;
      [exact ST2| assumption| exact CEIL| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO. post_call ctasegs m2. rewrite ?ESPA in *.
  rewrite (isdigit_range (clo 2 t)) by lia.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  step. brc.
  ab_shload 1. shz.
  step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. ab_shload 4. step. rewrite (zxb_lit (clo 2 t)) by lia. shz.
  (* [comment removed for export] *)
  step. step. rewrite (sx32_small 24) by lia. step. try rewrite (swrap32_small (2 + 1)) by lia.
  step. step. step. step. brc. step. step. step. step. step.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. ab_shload 4. shz.
  zstep. zstep. step. rewrite sx32_small by lia. zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (fld 2 t + 48)) ltac:(wmodk PV CH2 CL2).
  setreg 13%Z (Z_to_bv 64 (fld 2 t)) ltac:(wmodk PV CH2 CL2).
  step. if_cases KM; zify_cond KM; [exfalso; rewrite ?ab_signed_small, ?signed_lit in KM by lia; lia|]. try clear KM.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. step. ab_shload 4. shz.
  zstep. rewrite sx32_small by lia.
  step. if_cases KX; zify_cond KX; [exfalso; rewrite ?ab_signed_small, ?signed_lit in KX by lia; lia|]. try clear KX.
  step. step. brc.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia. zstep.
  step.
  (* [comment removed for export] *)
  apply evt_done. unfold t2t_iterA_post. do 14 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iterA_3 : t2t_iterA_stmt 3.
Proof.
  unfold t2t_iterA_stmt. intros until g. intros ST MI CEIL LO TOP AL16 C1 C2 C3 HD ACCD ALD D0 DHI HS ACCS ALS S0 SHI LOW ACCMIN ACCMAX TV MSR F0 FHI.
  unfold T2T_HEAD_A in *. unfold A_MINTAB_A in ACCMIN. unfold A_MAXTAB_A in ACCMAX.
  unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, TOP. pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu, C1, C2, C3, DHI, SHI, FHI.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  pose proof (munch_refl [(lo, spa)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(lo, spa)]%Z) by (cbn [offshW]; alia).
  pose proof (fld_range 3 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 3 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 3 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 3 t TV ltac:(lia)) as PV.
  unfold t2t_lowA, MASK47 in LOW. unfold gcells, zb8 in HS.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - LO LO0 TOP; alia).
  pose proof (mintabA_cell m 3 MI ltac:(lia)) as TMIN. pose proof (maxtabA_cell m 3 MI ltac:(lia)) as TMAX. pose proof (jtabA_cell m 3 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  (* [comment removed for export] *)
  step. step. step. step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. ab_shload 1. shz.
  step. rewrite (zxb_lit (chi 3 t)) by lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_specA _ (Z_to_bv 64 spa)) with (lo := lo) (c := chi 3 t); rewrite ?ESPA;
      [exact ST| exact MI| exact CEIL| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO. post_call ctasegs m1. rewrite ?ESPA in *.
  rewrite (isdigit_range (chi 3 t)) by lia.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  step. brc.
  ab_shload 1. shz.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. step. ab_shload 1. step. rewrite (zxb_lit (chi 3 t)) by lia. shz.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (clo 3 t)) by lia.
  step. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_specA _ (Z_to_bv 64 spa)) with (lo := lo) (c := clo 3 t); rewrite ?ESPA;
      [exact ST2| assumption| exact CEIL| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO. post_call ctasegs m2. rewrite ?ESPA in *.
  rewrite (isdigit_range (clo 3 t)) by lia.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  step. brc.
  ab_shload 1. shz.
  step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. ab_shload 4. step. rewrite (zxb_lit (clo 3 t)) by lia. shz.
  (* [comment removed for export] *)
  step. step. rewrite (sx32_small 24) by lia. step. try rewrite (swrap32_small (3 + 1)) by lia.
  step. step. step. step. brc. step. step. step. step. step.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. ab_shload 4. shz.
  zstep. zstep. step. rewrite sx32_small by lia. zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (fld 3 t + 48)) ltac:(wmodk PV CH2 CL2).
  setreg 13%Z (Z_to_bv 64 (fld 3 t)) ltac:(wmodk PV CH2 CL2).
  step. if_cases KM; zify_cond KM; [exfalso; rewrite ?ab_signed_small, ?signed_lit in KM by lia; lia|]. try clear KM.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. step. ab_shload 4. shz.
  zstep. rewrite sx32_small by lia.
  step. if_cases KX; zify_cond KX; [exfalso; rewrite ?ab_signed_small, ?signed_lit in KX by lia; lia|]. try clear KX.
  step. step. brc.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia. zstep.
  step.
  (* [comment removed for export] *)
  apply evt_done. unfold t2t_iterA_post. do 14 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iterA_4 : t2t_iterA_stmt 4.
Proof.
  unfold t2t_iterA_stmt. intros until g. intros ST MI CEIL LO TOP AL16 C1 C2 C3 HD ACCD ALD D0 DHI HS ACCS ALS S0 SHI LOW ACCMIN ACCMAX TV MSR F0 FHI.
  unfold T2T_HEAD_A in *. unfold A_MINTAB_A in ACCMIN. unfold A_MAXTAB_A in ACCMAX.
  unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, TOP. pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu, C1, C2, C3, DHI, SHI, FHI.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  pose proof (munch_refl [(lo, spa)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(lo, spa)]%Z) by (cbn [offshW]; alia).
  pose proof (fld_range 4 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 4 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 4 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 4 t TV ltac:(lia)) as PV.
  unfold t2t_lowA, MASK47 in LOW. unfold gcells, zb8 in HS.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - LO LO0 TOP; alia).
  pose proof (mintabA_cell m 4 MI ltac:(lia)) as TMIN. pose proof (maxtabA_cell m 4 MI ltac:(lia)) as TMAX. pose proof (jtabA_cell m 4 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  (* [comment removed for export] *)
  step. step. step. step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. ab_shload 1. shz.
  step. rewrite (zxb_lit (chi 4 t)) by lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_specA _ (Z_to_bv 64 spa)) with (lo := lo) (c := chi 4 t); rewrite ?ESPA;
      [exact ST| exact MI| exact CEIL| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO. post_call ctasegs m1. rewrite ?ESPA in *.
  rewrite (isdigit_range (chi 4 t)) by lia.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  step. brc.
  ab_shload 1. shz.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. step. ab_shload 1. step. rewrite (zxb_lit (chi 4 t)) by lia. shz.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (clo 4 t)) by lia.
  step. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_specA _ (Z_to_bv 64 spa)) with (lo := lo) (c := clo 4 t); rewrite ?ESPA;
      [exact ST2| assumption| exact CEIL| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO. post_call ctasegs m2. rewrite ?ESPA in *.
  rewrite (isdigit_range (clo 4 t)) by lia.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  step. brc.
  ab_shload 1. shz.
  step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. ab_shload 4. step. rewrite (zxb_lit (clo 4 t)) by lia. shz.
  (* [comment removed for export] *)
  step. step. rewrite (sx32_small 24) by lia. step. try rewrite (swrap32_small (4 + 1)) by lia.
  step. step. step. step. brc. step. step. step. step. step.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. ab_shload 4. shz.
  zstep. zstep. step. rewrite sx32_small by lia. zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (fld 4 t + 48)) ltac:(wmodk PV CH2 CL2).
  setreg 13%Z (Z_to_bv 64 (fld 4 t)) ltac:(wmodk PV CH2 CL2).
  step. if_cases KM; zify_cond KM; [exfalso; rewrite ?ab_signed_small, ?signed_lit in KM by lia; lia|]. try clear KM.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. step. ab_shload 4. shz.
  zstep. rewrite sx32_small by lia.
  step. if_cases KX; zify_cond KX; [exfalso; rewrite ?ab_signed_small, ?signed_lit in KX by lia; lia|]. try clear KX.
  step. step. brc.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia. zstep.
  step.
  (* [comment removed for export] *)
  apply evt_done. unfold t2t_iterA_post. do 14 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iterA_5 : t2t_iterA_stmt 5.
Proof.
  unfold t2t_iterA_stmt. intros until g. intros ST MI CEIL LO TOP AL16 C1 C2 C3 HD ACCD ALD D0 DHI HS ACCS ALS S0 SHI LOW ACCMIN ACCMAX TV MSR F0 FHI.
  unfold T2T_HEAD_A in *. unfold A_MINTAB_A in ACCMIN. unfold A_MAXTAB_A in ACCMAX.
  unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, TOP. pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu, C1, C2, C3, DHI, SHI, FHI.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  pose proof (munch_refl [(lo, spa)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(lo, spa)]%Z) by (cbn [offshW]; alia).
  pose proof (fld_range 5 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 5 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 5 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 5 t TV ltac:(lia)) as PV.
  unfold t2t_lowA, MASK47 in LOW. unfold gcells, zb8 in HS.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - LO LO0 TOP; alia).
  pose proof (mintabA_cell m 5 MI ltac:(lia)) as TMIN. pose proof (maxtabA_cell m 5 MI ltac:(lia)) as TMAX. pose proof (jtabA_cell m 5 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  (* [comment removed for export] *)
  step. step. step. step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. ab_shload 1. shz.
  step. rewrite (zxb_lit (chi 5 t)) by lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_specA _ (Z_to_bv 64 spa)) with (lo := lo) (c := chi 5 t); rewrite ?ESPA;
      [exact ST| exact MI| exact CEIL| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO. post_call ctasegs m1. rewrite ?ESPA in *.
  rewrite (isdigit_range (chi 5 t)) by lia.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  step. brc.
  ab_shload 1. shz.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. step. ab_shload 1. step. rewrite (zxb_lit (chi 5 t)) by lia. shz.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (clo 5 t)) by lia.
  step. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_specA _ (Z_to_bv 64 spa)) with (lo := lo) (c := clo 5 t); rewrite ?ESPA;
      [exact ST2| assumption| exact CEIL| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO. post_call ctasegs m2. rewrite ?ESPA in *.
  rewrite (isdigit_range (clo 5 t)) by lia.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  step. brc.
  ab_shload 1. shz.
  step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. ab_shload 4. step. rewrite (zxb_lit (clo 5 t)) by lia. shz.
  (* [comment removed for export] *)
  step. step. rewrite (sx32_small 24) by lia. step. try rewrite (swrap32_small (5 + 1)) by lia.
  step. step. step. step. brc. step. step. step. step. step.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. ab_shload 4. shz.
  zstep. zstep. step. rewrite sx32_small by lia. zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (fld 5 t + 48)) ltac:(wmodk PV CH2 CL2).
  setreg 13%Z (Z_to_bv 64 (fld 5 t)) ltac:(wmodk PV CH2 CL2).
  step. if_cases KM; zify_cond KM; [exfalso; rewrite ?ab_signed_small, ?signed_lit in KM by lia; lia|]. try clear KM.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. step. ab_shload 4. shz.
  zstep. rewrite sx32_small by lia.
  step. if_cases KX; zify_cond KX; [exfalso; rewrite ?ab_signed_small, ?signed_lit in KX by lia; lia|]. try clear KX.
  step. step. brc.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia. zstep.
  step.
  (* [comment removed for export] *)
  apply evt_done. unfold t2t_iterA_post. do 14 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.

Lemma t2t_iterA_6 : t2t_iterA_stmt 6.
Proof.
  unfold t2t_iterA_stmt. intros until g. intros ST MI CEIL LO TOP AL16 C1 C2 C3 HD ACCD ALD D0 DHI HS ACCS ALS S0 SHI LOW ACCMIN ACCMAX TV MSR F0 FHI.
  unfold T2T_HEAD_A in *. unfold A_MINTAB_A in ACCMIN. unfold A_MAXTAB_A in ACCMAX.
  unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, TOP. pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu, C1, C2, C3, DHI, SHI, FHI.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  pose proof (munch_refl [(lo, spa)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(lo, spa)]%Z) by (cbn [offshW]; alia).
  pose proof (fld_range 6 t TV ltac:(lia)) as [FR0 FR1]. pose proof (chi_val 6 t TV ltac:(lia)) as [CH1 CH2]. pose proof (clo_val 6 t TV ltac:(lia)) as [CL1 CL2].
  pose proof (pair_val 6 t TV ltac:(lia)) as PV.
  unfold t2t_lowA, MASK47 in LOW. unfold gcells, zb8 in HS.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - LO LO0 TOP; alia).
  pose proof (mintabA_cell m 6 MI ltac:(lia)) as TMIN. pose proof (maxtabA_cell m 6 MI ltac:(lia)) as TMAX. pose proof (jtabA_cell m 6 MI ltac:(lia)) as TJ.
  lazymatch type of TMIN with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMIN end.
  lazymatch type of TMAX with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TMAX end.
  lazymatch type of TJ with ro_cells _ _ ?a [C4 (Z_to_bv 64 ?j)] => let v := eval vm_compute in a in change a with v in TJ;
      let vj := eval vm_compute in j in change j with vj in TJ end.
  cbv [mintab maxtab Z.eqb orb Pos.eqb] in TMIN, TMAX. cbv [mintab maxtab Z.eqb orb Pos.eqb] in FR0.
  (* [comment removed for export] *)
  step. step. step. step. step. brc.
  (* [comment removed for export] *)
(* [comment removed for export] *)
  step. step. ab_shload 1. shz.
  step. rewrite (zxb_lit (chi 6 t)) by lia. zstep. step. step. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|]. try clear KB.
  step. zstep. zstep.
  setreg 10%Z (Z_to_bv 64 0) ltac:(symmetry; f_equal; rewrite ?land64; apply mask47_digit; lia).
  step. brc.
  (* [comment removed for export] *)
  step. step. ab_shload 1. shz.
  step. rewrite (zxb_lit (chi 6 t)) by lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. name_mem m1. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_specA _ (Z_to_bv 64 spa)) with (lo := lo) (c := chi 6 t); rewrite ?ESPA;
      [exact ST| exact MI| exact CEIL| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO. post_call ctasegs m1. rewrite ?ESPA in *.
  rewrite (isdigit_range (chi 6 t)) by lia.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST2 end. name_mem m2.
  (* [comment removed for export] *)
  step. brc.
  ab_shload 1. shz.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. step. ab_shload 1. step. rewrite (zxb_lit (chi 6 t)) by lia. shz.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (clo 6 t)) by lia.
  step. eapply evt_cut.
  { eapply (ossl_ascii_isdigit_specA _ (Z_to_bv 64 spa)) with (lo := lo) (c := clo 6 t); rewrite ?ESPA;
      [exact ST2| assumption| exact CEIL| lia| lia| reflexivity]. }
  intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO. post_call ctasegs m2. rewrite ?ESPA in *.
  rewrite (isdigit_range (clo 6 t)) by lia.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  step. brc.
  ab_shload 1. shz.
  step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. ab_shload 4. step. rewrite (zxb_lit (clo 6 t)) by lia. shz.
  (* [comment removed for export] *)
  step. step. rewrite (sx32_small 24) by lia. step. try rewrite (swrap32_small (6 + 1)) by lia.
  step. step. step. step. brc. step. step. step. step. step.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. ab_shload 4. shz.
  zstep. zstep. step. rewrite sx32_small by lia. zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (fld 6 t + 48)) ltac:(wmodk PV CH2 CL2).
  setreg 13%Z (Z_to_bv 64 (fld 6 t)) ltac:(wmodk PV CH2 CL2).
  step. if_cases KM; zify_cond KM; [exfalso; rewrite ?ab_signed_small, ?signed_lit in KM by lia; lia|]. try clear KM.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. step. ab_shload 4. shz.
  zstep. rewrite sx32_small by lia.
  step. if_cases KX; zify_cond KX; [exfalso; rewrite ?ab_signed_small, ?signed_lit in KX by lia; lia|]. try clear KX.
  step. step. brc.
  (* [comment removed for export] *)
  zstep. zstep. zstep. step. rewrite sx32_small by lia. zstep.
  step.
  (* [comment removed for export] *)
  apply evt_done. unfold t2t_iterA_post. do 14 eexists. exists m3. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact ST3].
Qed.


Lemma t2t_iterA : forall i, 0 <= i <= 6 -> t2t_iterA_stmt i.
Proof.
  intros i Hi. assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
  destruct H as [->|[->|[->|[->|[->|[->| ->]]]]]];
    [exact t2t_iterA_0| exact t2t_iterA_1| exact t2t_iterA_2| exact t2t_iterA_3| exact t2t_iterA_4| exact t2t_iterA_5| exact t2t_iterA_6].
Qed.

End WithRT.
