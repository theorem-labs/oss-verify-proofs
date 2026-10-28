(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac MState Mem Frame Cells Step Exec ImageA RzCPS RegsEquiv StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import TopA_iodefs RT_cli. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_hkit Sj_num_akit Sj_acps. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec AxSymExec3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import El_xs_core.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import El_xs_coreA El_xs_adaptA El_xs_kitA El_throwA El_xcxaA El_xsitesA El_xr_bbegin El_xr_bcast El_xr_bend.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Import AX2.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition kd_fsz (RA : Z) : Z := if RA =? 0xb2d1c then 48 else 32.
Definition kd_hcs (RA : Z) : list hcellA :=
  if RA =? 0xb2d1c then el_hcs_bcast else if RA =? 0xb3014 then el_hcs_bbegin else el_hcs_bend.
Definition kd_xr (RA : Z) : xregs_exit :=
  if RA =? 0xb2d1c then el_xr_bcast else if RA =? 0xb3014 then el_xr_bbegin else el_xr_bend.
Definition kd_xk (RA : Z) : xstack_exit :=
  if RA =? 0xb2d1c then el_xk_bcast else if RA =? 0xb3014 then el_xk_bbegin else el_xk_bend.
Definition kd_IT (RA : Z) : itab :=
  if RA =? 0xb2d1c then el_IT_bcast else if RA =? 0xb3014 then el_IT_bbegin else el_IT_bend.

Definition kd_es0 (RA : Z) : expr := if RA =? 0xb2d1c then EVar 52 else EVar 50.
Definition kd_es1 (RA : Z) : expr := if RA =? 0xb2d1c then EVar 51 else EVar 49.
Definition kd_ok (RA : Z) : Prop := RA = 0xb2d1c \/ RA = 0xb3014 \/ RA = 0xb31d0.
Definition FUZZ_SP0GAP_X : Z := 0x1000.

Lemma kd_run : forall RA uw, kd_ok RA ->
  exit_okA (kd_fsz RA) (kd_xr RA) (kd_xk RA) (xautoXA (kd_fsz RA) (kd_IT RA) XS_END_A XSA_FUEL XSA_K (xs_ss0A (kd_fsz RA) (kd_hcs RA) RA uw)) = true.
Proof.
  intros RA uw [-> |[-> | ->]]; [exact (xr_bcast_ok uw)| exact (xr_bbegin_ok uw)| exact (xr_bend_ok uw)].
Qed.

Lemma kd_static : forall RA, kd_ok RA ->
  (32 <= kd_fsz RA <= 4096 /\ kd_fsz RA mod 16 = 0)
  /\ (forall o w v, In (o, w, v) (kd_hcs RA) -> 0 <= o /\ o + Z.of_nat w <= kd_fsz RA)
  /\ (length (kd_hcs RA) < 100)%nat
  /\ 0 <= RA < 2^64
  /\ (forall re, In re (kd_xr RA) -> xexp_ok (snd re) = true /\ (18 <= fst re <= 27)%nat)
  /\ In (kd_fsz RA - 8, ELit EL_LRET_XA) (kd_xk RA)
  /\ (In (kd_fsz RA - 16, kd_es0 RA) (kd_xk RA) /\ xexp_ok (kd_es0 RA) = true)
  /\ (In (kd_fsz RA - 24, kd_es1 RA) (kd_xk RA) /\ xexp_ok (kd_es1 RA) = true).
Proof.
  intros RA [-> |[-> | ->]]; cbn -[Z.le Z.lt Z.add Z.sub Z.modulo Z.pow Z.of_nat];
  (split; [lia|]; split; [intros o w v H; decompose sum H; try match goal with H : (_, _, _) = (_, _, _) |- _ => injection H as <- <- <- end; cbn; try lia; try tauto|];
   split; [lia|]; split; [lia|]; split; [intros re H; decompose sum H; subst; cbn; (split; [reflexivity| lia]) || tauto|];
   split; [tauto|]; split; [split; [tauto| reflexivity]| split; [tauto| reflexivity]]).
Qed.

Lemma itab_sound_kd : forall RA, itab_sound asegs (kd_IT RA).
Proof.
  intros RA. unfold kd_IT, el_IT_bcast, el_IT_bbegin, el_IT_bend.
  destruct (RA =? 0xb2d1c); [| destruct (RA =? 0xb3014)]; apply itab_of_ranges_soundA.
Qed.

Lemma el_xroA_dtor : forall m, el_xroA m -> ro_cells asegs m XS_DTORGOT [C8 (Z_to_bv 64 XS_DTOR)].
Proof. intros m H. unfold el_xroA in H. rewrite Forall_forall in H. exact (H (0x16aeb8, 0x104dd0) ltac:(cbn; tauto)). Qed.

Definition io_ro_ok (m : mem) : Prop := Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro.
Local Ltac io_inx := unfold io_ro; cbn [In]; repeat (first [ left; reflexivity | right ]).
Lemma el_xroA_of_io : forall m, io_ro_ok m -> ro_cells asegs m 0x16afd8 [C8 (Z_to_bv 64 0x6c7ea8)] -> el_xroA m.
Proof.
  intros m IO G. pose proof (proj1 (Forall_forall _ _) IO) as IOF. cbn beta in IOF.
  unfold el_xroA, el_xro_wordsA. repeat apply Forall_cons; [.. | apply Forall_nil]; cbn [fst snd].
  - exact (ro_cells_mid m 0x164570 [] (C8 (Z_to_bv 64 0x167c28)) [C8 (Z_to_bv 64 0x236cc); C8 (Z_to_bv 64 0x1679d8)] (IOF (0x164570, [C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x236cc); C8 (Z_to_bv 64 0x1679d8)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x164570 [C8 (Z_to_bv 64 0x167c28)] (C8 (Z_to_bv 64 0x236cc)) [C8 (Z_to_bv 64 0x1679d8)] (IOF (0x164570, [C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x236cc); C8 (Z_to_bv 64 0x1679d8)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x164570 [C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x236cc)] (C8 (Z_to_bv 64 0x1679d8)) [] (IOF (0x164570, [C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x236cc); C8 (Z_to_bv 64 0x1679d8)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x1679d8 [] (C8 (Z_to_bv 64 0x167bd8)) [C8 (Z_to_bv 64 0x2e900)] (IOF (0x1679d8, [C8 (Z_to_bv 64 0x167bd8); C8 (Z_to_bv 64 0x2e900)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x1679d8 [C8 (Z_to_bv 64 0x167bd8)] (C8 (Z_to_bv 64 0x2e900)) [] (IOF (0x1679d8, [C8 (Z_to_bv 64 0x167bd8); C8 (Z_to_bv 64 0x2e900)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x167bb0 [] (C8 (Z_to_bv 64 0x167c28)) [C8 (Z_to_bv 64 0x2e9bf)] (IOF (0x167bb0, [C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x2e9bf)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x167bb0 [C8 (Z_to_bv 64 0x167c28)] (C8 (Z_to_bv 64 0x2e9bf)) [] (IOF (0x167bb0, [C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x2e9bf)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x167bf8 [] (C8 (Z_to_bv 64 0x1051c8)) [] (IOF (0x167bf8, [C8 (Z_to_bv 64 0x1051c8)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x167c10 [] (C8 (Z_to_bv 64 0x10552c)) [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x167c68)] (IOF (0x167c10, [C8 (Z_to_bv 64 0x10552c); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x167c68)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x167c10 [C8 (Z_to_bv 64 0x10552c)] (C8 (Z_to_bv 64 0x0)) [C8 (Z_to_bv 64 0x167c68)] (IOF (0x167c10, [C8 (Z_to_bv 64 0x10552c); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x167c68)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x167c10 [C8 (Z_to_bv 64 0x10552c); C8 (Z_to_bv 64 0x0)] (C8 (Z_to_bv 64 0x167c68)) [] (IOF (0x167c10, [C8 (Z_to_bv 64 0x10552c); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x167c68)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x167c50 [] (C8 (Z_to_bv 64 0x1061a0)) [] (IOF (0x167c50, [C8 (Z_to_bv 64 0x1061a0)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x167c60 [] (C8 (Z_to_bv 64 0x1055a8)) [C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x2e9e1); C8 (Z_to_bv 64 0x167bb0)] (IOF (0x167c60, [C8 (Z_to_bv 64 0x1055a8); C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x2e9e1); C8 (Z_to_bv 64 0x167bb0)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x167c60 [C8 (Z_to_bv 64 0x1055a8)] (C8 (Z_to_bv 64 0x167c28)) [C8 (Z_to_bv 64 0x2e9e1); C8 (Z_to_bv 64 0x167bb0)] (IOF (0x167c60, [C8 (Z_to_bv 64 0x1055a8); C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x2e9e1); C8 (Z_to_bv 64 0x167bb0)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x167c60 [C8 (Z_to_bv 64 0x1055a8); C8 (Z_to_bv 64 0x167c28)] (C8 (Z_to_bv 64 0x2e9e1)) [C8 (Z_to_bv 64 0x167bb0)] (IOF (0x167c60, [C8 (Z_to_bv 64 0x1055a8); C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x2e9e1); C8 (Z_to_bv 64 0x167bb0)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x167c60 [C8 (Z_to_bv 64 0x1055a8); C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x2e9e1)] (C8 (Z_to_bv 64 0x167bb0)) [] (IOF (0x167c60, [C8 (Z_to_bv 64 0x1055a8); C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x2e9e1); C8 (Z_to_bv 64 0x167bb0)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x16a000 [] (C8 (Z_to_bv 64 0x145120)) [C8 (Z_to_bv 64 0x145158); C8 (Z_to_bv 64 0x1451f4)] (IOF (0x16a000, [C8 (Z_to_bv 64 0x145120); C8 (Z_to_bv 64 0x145158); C8 (Z_to_bv 64 0x1451f4)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x16a000 [C8 (Z_to_bv 64 0x145120)] (C8 (Z_to_bv 64 0x145158)) [C8 (Z_to_bv 64 0x1451f4)] (IOF (0x16a000, [C8 (Z_to_bv 64 0x145120); C8 (Z_to_bv 64 0x145158); C8 (Z_to_bv 64 0x1451f4)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x16a000 [C8 (Z_to_bv 64 0x145120); C8 (Z_to_bv 64 0x145158)] (C8 (Z_to_bv 64 0x1451f4)) [] (IOF (0x16a000, [C8 (Z_to_bv 64 0x145120); C8 (Z_to_bv 64 0x145158); C8 (Z_to_bv 64 0x1451f4)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x16a030 [] (C8 (Z_to_bv 64 0x145318)) [C8 (Z_to_bv 64 0x145400); C8 (Z_to_bv 64 0x145428)] (IOF (0x16a030, [C8 (Z_to_bv 64 0x145318); C8 (Z_to_bv 64 0x145400); C8 (Z_to_bv 64 0x145428)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x16a030 [C8 (Z_to_bv 64 0x145318)] (C8 (Z_to_bv 64 0x145400)) [C8 (Z_to_bv 64 0x145428)] (IOF (0x16a030, [C8 (Z_to_bv 64 0x145318); C8 (Z_to_bv 64 0x145400); C8 (Z_to_bv 64 0x145428)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x16a030 [C8 (Z_to_bv 64 0x145318); C8 (Z_to_bv 64 0x145400)] (C8 (Z_to_bv 64 0x145428)) [] (IOF (0x16a030, [C8 (Z_to_bv 64 0x145318); C8 (Z_to_bv 64 0x145400); C8 (Z_to_bv 64 0x145428)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x16a058 [] (C8 (Z_to_bv 64 0x1454d4)) [] (IOF (0x16a058, [C8 (Z_to_bv 64 0x1454d4)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x16a128 [] (C8 (Z_to_bv 64 0x16ea38)) [] (IOF (0x16a128, [C8 (Z_to_bv 64 0x16ea38)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x16a1d8 [] (C8 (Z_to_bv 64 0x0)) [] (IOF (0x16a1d8, [C8 (Z_to_bv 64 0x0)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x16ae98 [] (C8 (Z_to_bv 64 0x16a128)) [C8 (Z_to_bv 64 0)] (IOF (0x16ae98, [C8 (Z_to_bv 64 0x16a128); C8 (Z_to_bv 64 0)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x16aeb8 [] (C8 (Z_to_bv 64 0x104dd0)) [] (IOF (0x16aeb8, [C8 (Z_to_bv 64 0x104dd0)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x16af38 [] (C8 (Z_to_bv 64 0x16e998)) [] (IOF (0x16af38, [C8 (Z_to_bv 64 0x16e998)]) ltac:(io_inx))).
  - exact (ro_cells_mid m 0x16af40 [] (C8 (Z_to_bv 64 0x16e990)) [] (IOF (0x16af40, [C8 (Z_to_bv 64 0x16e990)]) ltac:(io_inx))).
  - exact G.
Qed.

Lemma mkR_sel_s : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  let R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 in
  reg_get R (Z_to_bv 5 18) = x18 /\ reg_get R (Z_to_bv 5 19) = x19 /\ reg_get R (Z_to_bv 5 20) = x20 /\ reg_get R (Z_to_bv 5 21) = x21
  /\ reg_get R (Z_to_bv 5 24) = x24 /\ reg_get R (Z_to_bv 5 25) = x25 /\ reg_get R (Z_to_bv 5 26) = x26 /\ reg_get R (Z_to_bv 5 27) = x27.
Proof. intros. repeat split; reflexivity. Qed.

Definition kd_i0 (RA : Z) : nat := if RA =? 0xb2d1c then 3 else 1.
Definition kd_i1 (RA : Z) : nat := if RA =? 0xb2d1c then 2 else 0.
Definition kd_x18 (RA : Z) (ws : list word) (s2 : word) : word := if RA =? 0xb2d1c then nth 1 ws (Z_to_bv 64 0) else s2.
Definition kd_x19 (RA : Z) (ws : list word) (s3 : word) : word := if RA =? 0xb2d1c then nth 0 ws (Z_to_bv 64 0) else s3.

Lemma kd_exit_regs : forall RA (R FIN : bvmap 5 word) (u : Z) (ws : list word), kd_ok RA ->
  (forall re, In re (kd_xr RA) -> reg_get FIN (Z_to_bv 5 (Z.of_nat (fst re))) = xden R u ws (snd re)) ->
  reg_get FIN (Z_to_bv 5 18) = kd_x18 RA ws (reg_get R (Z_to_bv 5 18)) /\ reg_get FIN (Z_to_bv 5 19) = kd_x19 RA ws (reg_get R (Z_to_bv 5 19))
  /\ reg_get FIN (Z_to_bv 5 20) = reg_get R (Z_to_bv 5 20) /\ reg_get FIN (Z_to_bv 5 21) = reg_get R (Z_to_bv 5 21)
  /\ reg_get FIN (Z_to_bv 5 24) = reg_get R (Z_to_bv 5 24) /\ reg_get FIN (Z_to_bv 5 25) = reg_get R (Z_to_bv 5 25)
  /\ reg_get FIN (Z_to_bv 5 26) = reg_get R (Z_to_bv 5 26) /\ reg_get FIN (Z_to_bv 5 27) = reg_get R (Z_to_bv 5 27).
Proof.
  intros RA R FIN u ws KA RG.
  assert (G : forall n e, In (n, e) (kd_xr RA) -> reg_get FIN (Z_to_bv 5 (Z.of_nat n)) = xden R u ws e) by (intros n e H; exact (RG (n, e) H)).
  destruct KA as [-> |[-> | ->]]; unfold kd_xr, kd_x18, kd_x19, el_xr_bcast, el_xr_bbegin, el_xr_bend in *; cbn [Z.eqb Pos.eqb] in *;
  (repeat split;
   [change (Z_to_bv 5 18) with (Z_to_bv 5 (Z.of_nat 18)); rewrite (G 18%nat _ ltac:(cbn; tauto))| change (Z_to_bv 5 19) with (Z_to_bv 5 (Z.of_nat 19)); rewrite (G 19%nat _ ltac:(cbn; tauto))| change (Z_to_bv 5 20) with (Z_to_bv 5 (Z.of_nat 20)); rewrite (G 20%nat _ ltac:(cbn; tauto))| change (Z_to_bv 5 21) with (Z_to_bv 5 (Z.of_nat 21)); rewrite (G 21%nat _ ltac:(cbn; tauto))
   | change (Z_to_bv 5 24) with (Z_to_bv 5 (Z.of_nat 24)); rewrite (G 24%nat _ ltac:(cbn; tauto))| change (Z_to_bv 5 25) with (Z_to_bv 5 (Z.of_nat 25)); rewrite (G 25%nat _ ltac:(cbn; tauto))| change (Z_to_bv 5 26) with (Z_to_bv 5 (Z.of_nat 26)); rewrite (G 26%nat _ ltac:(cbn; tauto))| change (Z_to_bv 5 27) with (Z_to_bv 5 (Z.of_nat 27)); rewrite (G 27%nat _ ltac:(cbn; tauto))];
   reflexivity).
Qed.

Section SiteCoreB.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC : rt_contracts RT.
  Hypothesis ALC : aligned_alloc_contract RT.
  Variable WIN : rt_win RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis XROW : forall c Σ (m : mem), ARTW RT WIN c Σ m -> io_ro_ok m.
  Let TLS : forall c, tls_icG (RTX RT WIN c) TPV_XA XS_TLS_A := fun c => w_tls RT WIN c.
  Let XROE : forall c Σ (m : mem), ARTW RT WIN c Σ m -> el_xroA m :=
    fun c Σ m H => el_xroA_of_io m (XROW c Σ m H) (proj1 (af_got_lib (RTX RT WIN c) (w_facts RT WIN c) Σ m H)).

  Variables (RA RA0 RA1 : Z).
  Hypothesis KA : kd_ok RA.
  Variable XP : mem -> Z -> Prop.
  Variable RGS : Z -> word -> Prop.
  Hypothesis XPT : forall (m m' : mem) usp, XP m usp -> agree_on (fun x => usp <= x < usp + kd_fsz RA) m m' -> XP m' usp.
  Hypothesis WKA : forall (usp p : Z) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
    RGS usp s1 -> XP m usp ->
    0 < p -> p + 144 < 2^47 -> p mod 16 = 0 ->
    rw_cells asegs m p [CB 128 (repeat z8 128); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
    (forall m', munch [(p + 128, p + 144)] m m' -> wmono asegs m m' -> shz m' (p + 128) 16) -> mem_inv asegs m ->
    (forall m' a n, munch [(p + 128, p + 144)] m m' -> wmono asegs m m' -> usp <= a -> a mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> a + n <= usp + kd_fsz RA -> shz m' a n) ->
    evt asegs (siteA_post RA1 usp p gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR (Z_to_bv 64 RA0) (Z_to_bv 64 usp) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 (Z_to_bv 64 (p + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RA0) fc None m (seg_rom asegs)).
  Hypothesis WKB : siteB_walk RA1 RA.
  Hypothesis RA0R : 0 <= RA0 < 2^32 /\ RA0 mod 2 = 0.
  Hypothesis RA1R : 0 <= RA1 < 2^32 /\ RA1 mod 2 = 0.

  Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB, NORET_DEPTH, FUZZ_SP0GAP_X, XS_SPLO, EXC_SIZE in *; lia.

  Definition site_postB (Σ Σ2 : rts RT) (m m2 : mem) (usp lo c : Z) : Prop :=
    ARTW RT WIN c Σ2 m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp + kd_fsz RA)
    /\ rt_live RT Σ2 = rt_live RT Σ /\ rt_frames RT Σ2 = rt_frames RT Σ /\ rt_sp0 RT Σ2 = rt_sp0 RT Σ /\ c = rt_credit RT Σ - mcost EXC_SIZE
    /\ rw_cells asegs m2 EL_EHG_XA [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ bytes_at asegs m2 EL_UNW_XA (map (fun b => Z_to_bv 8 b) (uw_bytesA true)) /\ wr_at asegs m2 EL_UNW_XA 8
    /\ (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + kd_fsz RA) (bv_unsigned x) ->
          ~ (EL_EHG_XA <= bv_unsigned x < EL_EHG_XA + 12) -> ~ (EL_UNW_XA <= bv_unsigned x < EL_UNW_XA + 8) -> m2 x = m x).

  Theorem site_rawB : forall (Σ : rts RT) (K : config -> Prop) (usp lo spx : Z) (ws : list word) (uw : bool) (fr : list cell)
      (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    RGS usp s1 -> XP m usp -> hcells_okA m usp 0 (kd_hcs RA) ws -> rw_cells asegs m usp fr -> Z.of_nat (cells_size fr) = kd_fsz RA ->
    lposA (rt_live RT Σ) -> Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX -> mcost EXC_SIZE <= rt_credit RT Σ ->
    ART RT Σ m -> mem_inv asegs m -> stk asegs m lo usp ->
    0x7fff7f800000 <= lo -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 0x15000 <= usp -> usp + kd_fsz RA + 0xb0 <= rt_sp0 RT Σ -> rt_sp0 RT Σ <= usp + 0x3c000 ->
    usp mod 16 = 0 ->
    rw_cells asegs m EL_EHG_XA [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
    bytes_at asegs m EL_UNW_XA (map (fun b => Z_to_bv 8 b) (uw_bytesA uw)) /\ wr_at asegs m EL_UNW_XA 8 ->
    el_xdataA m -> (exists g : word, cells_at asegs m EL_CANARY_XA [C8 g]) -> El_xs_adaptA.el_auxvA spx m -> usp + kd_fsz RA <= spx ->
    (forall (Σ2 : rts RT) (m2 : mem) (F2 : bvmap 5 word) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' t3' t4' t5' t6' : word),
       site_postB Σ Σ2 m m2 usp lo (rt_credit RT Σ - mcost EXC_SIZE) ->
       aevt RT PMc Σ2 K (MS (mkR (Z_to_bv 64 EL_LRET_XA) (Z_to_bv 64 (usp + kd_fsz RA)) gp (Z_to_bv 64 TPV_XA) t0' t1' t2'
                               (nth (kd_i0 RA) ws (Z_to_bv 64 0)) (nth (kd_i1 RA) ws (Z_to_bv 64 0)) a0' a1' a2' a3' a4' a5' a6' a7'
                               (kd_x18 RA ws s2) (kd_x19 RA ws s3) s4 s5
                               s6' s7' s8 s9 s10 s11 t3' t4' t5' t6')
                          F2 (Z_to_bv 64 EL_LRET_XA) fc None m2 (seg_rom asegs))) ->
    aevt RT PMc Σ K (MS (mkR (Z_to_bv 64 RA0) (Z_to_bv 64 usp) gp (Z_to_bv 64 TPV_XA) t0 t1 t2 s0 s1 (Z_to_bv 64 16) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 EL_CXA_ALLOC_XA) fc None m (seg_rom asegs)).
  Proof.
    intros Σ K usp lo spx ws uw fr gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      RG0 XP0 HC FR CSZ LPA LVB CRB ARTg MIg STg LLO WLO LOR SP1 SP2 U16 EHG UNW XD CAN AUX SPX POST.
    pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R.
    assert (FSZ : 32 <= kd_fsz RA <= 144) by (unfold kd_fsz; destruct (RA =? 0xb2d1c); lia).
    set (fsz := kd_fsz RA) in *.
    assert (MC : mcost EXC_SIZE = 2 * DCOST) by reflexivity. assert (DC : 0 <= DCOST) by (unfold DCOST; lia).
    assert (UB : lo + 48 + RT_STACK <= usp /\ usp + 16 <= USTACK_TOP /\ 64 <= usp) by (clear - FSZ LOR SP1 SP0R LLO; ul).
    destruct UB as (UB1 & UB2 & UB3).

    change TPV_XA with 0x6a7e68.
    apply (aevt_cxa_allocA RT AF RC ALC PMc FDO MST Σ K gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp lo RA0
             ltac:(lia) (proj2 RA0R) ltac:(clear - LVB; lia) CRB ARTg MIg STg WLO UB1 UB2 U16).
    intros Σ1 p u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 m1 ART1 MI1 WM1 ST1 PRES1 BLK1 LV1 FRS1 SP01 CR1 P0 P16 PTOP.
    assert (INP : In (p, EXC_SIZE) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
    pose proof (af_live_range RT AF Σ1 m1 p EXC_SIZE ART1 INP) as (_ & PHI & PSEG).
    assert (NB : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> ~ (p <= x < p + EXC_SIZE)).
    { intros x [Sx|[CSx|[LVa|[FRa|FSa]]]] Hb.
      - clear - Sx Hb PHI WLO UB1 SP01. ul.
      - pose proof (client_static_range _ CSx). clear - H Hb PSEG. ul.
      - destruct LVa as (q & n & HIn & Hq).
        pose proof (af_live_disj RT AF Σ1 m1 p EXC_SIZE q n [] (rt_live RT Σ) ART1 ltac:(rewrite LV1; reflexivity) HIn). lia.
      - destruct FRa as (f & k & HIn & Hf). rewrite <- FRS1 in HIn. destruct (af_frames_range RT AF Σ1 m1 f k ART1 HIn) as (_ & _ & _ & DJ). pose proof (DJ p EXC_SIZE INP). lia.
      - destruct FSa as (f & k & HIn & Hf). rewrite <- FRS1 in HIn. destruct (af_fshadow_apart RT AF Σ1 m1 f k ART1 HIn) as [DJ _]. pose proof (DJ p EXC_SIZE INP). lia. }
    assert (SZ : forall m', munch [(p + 128, p + 144)] m1 m' -> wmono asegs m1 m' -> shz m' (p + 128) 16).
    { intros m' MU WM. assert (ART' : ART RT Σ1 m').
      { apply (art_client_write RT AF Σ1 m1 m' usp ART1 ltac:(rewrite SP01; clear - WLO UB1; ul)); [| exact WM].
        intros x Hx. apply MU. cbn [outside]. split; [| exact I]. intros Hin. apply Hx. right; right; left. exists p, EXC_SIZE. split; [exact INP| clear - Hin; ul]. }
      apply (shz_sub m' p (8 * (EXC_SIZE / 8))); [| lia| clear; ul]. apply (shz_live RT AF Σ1 m' p EXC_SIZE ART' INP). clear - P16. Z.div_mod_to_equations. lia. }
    assert (SZS : forall m' a n, munch [(p + 128, p + 144)] m1 m' -> wmono asegs m1 m' -> usp <= a -> a mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> a + n <= usp + kd_fsz RA -> shz m' a n).
    { intros m' a n MU WM A1 A8 N8 N0 A2. assert (ART' : ART RT Σ1 m').
      { apply (art_client_write RT AF Σ1 m1 m' usp ART1 ltac:(rewrite SP01; clear - WLO UB1; ul)); [| exact WM].
        intros x Hx. apply MU. cbn [outside]. split; [| exact I]. intros Hin. apply Hx. right; right; left. exists p, EXC_SIZE. split; [exact INP| clear - Hin; ul]. }
      apply (shz_stack RT AF Σ1 m' a n ART'); [rewrite SP01; clear - A1 WLO UB1; ul| fold fsz in A2; clear - A2 FSZ SP1 SP0R SP01; ul| exact A8| exact N8| exact N0]. }
    assert (XP1 : XP m1 usp).
    { apply (XPT m m1 usp XP0). intros x Hx. symmetry. symmetry. apply PRES1. left. clear - Hx UB2 FSZ SP1 SP0R. ul. }

    apply (aevt_evt RT AF PMc MST).
    eapply evt_mono; [apply (WKA usp p gp u0 u1 u2 s0 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F1 fc m1 RG0 XP1 P0 ltac:(clear - PTOP; ul) P16 BLK1 SZ MI1 SZS)|].
    cbv beta. intros ms (a0' & a1' & a2' & code & m3 & -> & MU3 & WM3 & MI3 & BLK3).
    assert (AG3 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m3 x = m x).
    { intros x Hx. rewrite (MU3 x); [exact (PRES1 x Hx)|]. cbn [outside]. split; [| exact I]. pose proof (NB _ Hx). clear - H. unfold EXC_SIZE in H. lia. }
    assert (ART3 : ART RT Σ1 m3).
    { apply (art_client_write RT AF Σ1 m1 m3 usp ART1 ltac:(rewrite SP01; clear - WLO UB1; ul)); [| exact WM3].
      intros x Hx. apply MU3. cbn [outside]. split; [| exact I]. intros Hin. apply Hx. right; right; left. exists p, EXC_SIZE. split; [exact INP| clear - Hin; ul]. }
    assert (ST3 : stk asegs m3 lo usp).
    { apply (stk_agree_nw asegs m1 m3 _ _ ST1). intros x Hx. apply MU3. cbn [outside]. split; [| exact I]. clear - Hx PHI WLO SP01. ul. }

    assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; clear - UB2 UB3; ul).
    assert (COK3 : call_ok RT Σ1 m3 (Z_to_bv 64 usp) lo).
    { unfold call_ok. rewrite EU, SP01. split; [exact ST3|]. split; [exact WLO|]. split; [clear - UB1; ul|]. split; [exact UB2| exact U16]. }
    apply (aevt_call2x RT PMc Σ1 K _ _ (w_enter RT WIN (rt_credit RT Σ1) Σ1 PMc (Z_to_bv 64 RA1) (Z_to_bv 64 usp) gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 (p + 128)) s1 a0' a1' a2' b3 b4 b5 b6 b7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F1 fc m3 lo FDO MST eq_refl (conj ART3 eq_refl) MI3 COK3
              ltac:(rewrite EU, SP01; clear - SP1 SP2 FSZ; ul) ltac:(rewrite EU, SP01; clear - SP1 SP2 FSZ; ul))).
    intros c4 Hc4. exists Σ1. eexists. split; [exact Hc4|].
    intros ms4 (v4 & m4 & RS4 & HA4 & MI4 & WM4 & ST4 & PR4).
    destruct RS4 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F4 & ->). rewrite EU in ST4, PR4.
    rewrite (ret_pc_even RA1) by lia.
    assert (AG4 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m4 x = m x).
    { intros x Hx. rewrite (PR4 x); [exact (AG3 x Hx)|]. rewrite LV1, FRS1. apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; right; exact He| auto| lia]. }
    pose proof (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM3 WM4)) as WM04.

    apply (aevt_evt RT AF PMc MST).
    eapply evt_mono; [apply (WKB _ gp _ w0 w1 w2 _ _ v4 d1 d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc m4 (el_xroA_dtor m4 (XROE _ Σ1 m4 HA4)) MI4)|].
    cbv beta. intros ms ->.

    pose proof (kd_static RA KA) as (FSZR & HCO & HCN & RAR & XROK & XK0 & XK1 & XK2). fold fsz in FSZR, HCO, XK0, XK1, XK2.
    assert (HB4 : rw_cells asegs m4 p [CB 128 (repeat (Z_to_bv 8 0) 128); C8 (Z_to_bv 64 EL_VPTR_XA); C4 code; C4 (Z_to_bv 64 0)]).
    { change (Z_to_bv 8 0) with z8. change EL_VPTR_XA with XS_VPTR. apply (rw_cells_agree asegs m3 m4 _ _ BLK3); [| exact WM4].
      apply (agree_of_pres _ _ _ _ _ _ PR4). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      right; right; left. exists p, EXC_SIZE. split; [exact INP| clear - Hx; ul]. }
    assert (AGF : agree_on (fun x => usp <= x < usp + fsz) m m4) by (intros x Hx; apply AG4; left; clear - Hx UB2 FSZ SP1 SP0R; ul).
    assert (HC4 : hcells_okA m4 usp 0 (kd_hcs RA) ws).
    { revert HC AGF WM04 HCO. clear. generalize (kd_hcs RA) as hcs. generalize 0%nat as k. intros k hcs HC AGF WM HCO.
      revert k HC HCO. induction hcs as [|[[o w] v] tl IH]; intros k HC HCO; [exact I|].
      assert (OW : 0 <= o /\ o + Z.of_nat w <= fsz) by (apply (HCO o w v); left; reflexivity).
      assert (TL : forall o' w' v', In (o', w', v') tl -> 0 <= o' /\ o' + Z.of_nat w' <= fsz) by (intros o' w' v' H; apply (HCO o' w' v'); right; exact H).
      cbn [hcells_okA] in HC |- *. destruct v as [z|j|];
        [destruct HC as (C & Z1 & W & REST)| destruct HC as (C & Z1 & W & REST)| destruct HC as (C & W & REST)];
        (assert (CSZ : Z.of_nat (cells_size [cwA w _]) = Z.of_nat w) by (destruct W as [-> | ->]; reflexivity)) || idtac.
      - split; [| split; [exact Z1| split; [exact W| exact (IH k REST TL)]]].
        apply (rw_cells_agree asegs m m4 _ _ C); [| exact WM]. intros x Hx. apply AGF. destruct W as [-> | ->]; cbn [cells_size csize cwA Nat.add] in Hx; lia.
      - split; [| split; [exact Z1| split; [exact W| exact (IH k REST TL)]]].
        apply (rw_cells_agree asegs m m4 _ _ C); [| exact WM]. intros x Hx. apply AGF. destruct W as [-> | ->]; cbn [cells_size csize cwA Nat.add] in Hx; lia.
      - split; [| split; [exact W| exact (IH (S k) REST TL)]].
        apply (rw_cells_agree asegs m m4 _ _ C); [| exact WM]. intros x Hx. apply AGF. destruct W as [-> | ->]; cbn [cells_size csize cwA Nat.add] in Hx; lia. }
    assert (ST4' : stk asegs m4 lo (usp + fsz)).
    { assert (FR4 : rw_cells asegs m4 usp fr) by (apply (rw_cells_agree asegs m m4 _ _ FR); [| exact WM04]; intros x Hx; apply AGF; rewrite CSZ in Hx; exact Hx).
      pose proof (stk_release asegs m4 lo usp _ ST4 FR4 ltac:(clear - UB1; ul)) as X4. rewrite CSZ in X4. exact X4. }
    assert (AGS : forall x : word, client_static (bv_unsigned x) -> m4 x = m x) by (intros x Hx; apply AG4; right; left; exact Hx).
    assert (EHG4 : rw_cells asegs m4 EL_EHG_XA [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]).
    { apply (rw_cells_agree asegs m m4 _ _ EHG); [| exact WM04]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply AGS. apply xstatics_client. left. exact Hx. }
    assert (UNW4 : bytes_at asegs m4 EL_UNW_XA (map (fun b => Z_to_bv 8 b) (uw_bytesA uw)) /\ wr_at asegs m4 EL_UNW_XA 8).
    { destruct UNW as [B W]. split.
      - apply (bytes_at_agree asegs m m4 _ _ B). intros x Hx. cbn [map length uw_bytesA Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply AGS. apply xstatics_client. right; left. destruct uw; cbn in Hx; lia.
      - destruct W as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i Hi. apply WM04. exact (W3 i Hi). }
    assert (XD4 : el_xdataA m4).
    { destruct XD as [X1 X2]. split; (eapply rw_cells_agree; [eassumption| | exact WM04]); intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply AGS; apply xstatics_client;
        [right; right; left; exact Hx| right; right; right; left; exact Hx]. }
    assert (CAN4 : exists g : word, cells_at asegs m4 EL_CANARY_XA [C8 g]).
    { destruct CAN as (g & G2). exists g. apply (cells_at_agree asegs m m4 _ _ G2). intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply AGS. apply xstatics_client.
      right; right; right; right; left. exact Hx. }
    assert (AUX4 : El_xs_adaptA.el_auxvA spx m4).
    { destruct AUX as (av & x16 & x6 & x11 & x12 & x23 & rnd & AC & AB & AV1 & AV2 & AV3 & REST). exists av, x16, x6, x11, x12, x23, rnd.
      split; [| split; [| exact (conj AV1 (conj AV2 (conj AV3 REST)))]].
      - apply (ro_cells_agree asegs m m4 _ _ AC). intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply AGS. apply xstatics_client. right; right; right; right; right. exact Hx.
      - apply (bytes_at_agree asegs m m4 _ _ AB). intros x Hx. replace (Z.of_nat (length (u64sA (el_auxv_words x16 x6 x11 x12 x23 rnd)))) with 160 in Hx by reflexivity. apply AG4. left.
        clear - Hx AV1 AV2 SPX FSZ. ul. }
    change 0x6a7e68 with TPV_XA. change XS_TINFO with EL_TINFO_XA. change XS_DTOR with EL_DTOR_XA. change XS_CXA_THROW with EL_CXA_THROW_XA.
    apply (xs_throwA RT WIN (rt_credit RT Σ1) PMc FDO MST (TLS _) (XROE _) fsz (kd_hcs RA) RA (kd_xr RA) (kd_xk RA) (kd_IT RA) (kd_es0 RA) (kd_es1 RA)
             FSZR HCO HCN RAR XROK XK0 XK1 XK2 (itab_sound_kd RA) (fun uw' => kd_run RA uw' KA)
             Σ1 (Z_to_bv 64 usp) gp w0 w1 w2 s1 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc m4 p lo spx code uw ws
             HB4 INP (conj P0 (conj P16 (conj PHI PSEG))) ltac:(rewrite EU; exact ST4') LLO ltac:(rewrite SP01; exact WLO) ltac:(rewrite EU; clear - UB1 LOR FSZ; ul)
             ltac:(rewrite EU, SP01; clear - SP1 SP2 FSZ; ul) ltac:(rewrite EU, SP01; clear - SP1 SP2 FSZ; ul) ltac:(rewrite SP01; clear - SP0R; lia)
             ltac:(rewrite EU; exact U16) MI4 HA4 EHG4 UNW4 XD4 CAN4 AUX4 ltac:(rewrite EU; exact SPX) ltac:(rewrite EU; exact HC4)).
    intros Σ2 m2 F2 t0' t1' t2' e0 e1 e2 e3 e4 e5 e6 e7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' XPo RGx.
    rewrite EU in RGx |- *. unfold xs_postA in XPo. rewrite EU in XPo. cbn [rt_live rt_frames rt_sp0 RTX rt_sigW] in XPo.
    destruct XPo as (HA2 & MI2 & ST2 & LV2 & FR2 & SP02 & EHG2 & UB2' & WR2 & PRES2).

    lazymatch goal with |- context [xden ?Rx _ _ _] => set (R0 := Rx) in * end.
    destruct (kd_exit_regs RA R0 _ usp ws KA RGx) as (V2 & V3 & V4 & V5 & V8 & V9 & V10 & V11).
    destruct (mkR_sel_s (Z_to_bv 64 EL_LRET_XA) (Z_to_bv 64 (usp + fsz)) gp (Z_to_bv 64 TPV_XA) t0' t1' t2' (xden R0 usp ws (kd_es0 RA)) (xden R0 usp ws (kd_es1 RA))
                e0 e1 e2 e3 e4 e5 e6 e7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6') as (Y18 & Y19 & Y20 & Y21 & Y24 & Y25 & Y26 & Y27).
    rewrite Y18 in V2. rewrite Y19 in V3. rewrite Y20 in V4. rewrite Y21 in V5. rewrite Y24 in V8. rewrite Y25 in V9. rewrite Y26 in V10. rewrite Y27 in V11.
    replace (reg_get R0 (Z_to_bv 5 18)) with s2 in V2 by reflexivity. replace (reg_get R0 (Z_to_bv 5 19)) with s3 in V3 by reflexivity.
    replace (reg_get R0 (Z_to_bv 5 20)) with s4 in V4 by reflexivity. replace (reg_get R0 (Z_to_bv 5 21)) with s5 in V5 by reflexivity. replace (reg_get R0 (Z_to_bv 5 24)) with s8 in V8 by reflexivity.
    replace (reg_get R0 (Z_to_bv 5 25)) with s9 in V9 by reflexivity. replace (reg_get R0 (Z_to_bv 5 26)) with s10 in V10 by reflexivity.
    replace (reg_get R0 (Z_to_bv 5 27)) with s11 in V11 by reflexivity.
    subst s2' s3' s4' s5' s8' s9' s10' s11'.
    replace (xden R0 usp ws (kd_es0 RA)) with (nth (kd_i0 RA) ws (Z_to_bv 64 0)) by (unfold xden, kd_es0, kd_i0; destruct (RA =? 0xb2d1c); reflexivity).
    replace (xden R0 usp ws (kd_es1 RA)) with (nth (kd_i1 RA) ws (Z_to_bv 64 0)) by (unfold xden, kd_es1, kd_i1; destruct (RA =? 0xb2d1c); reflexivity).
    lazymatch goal with |- aevt _ ?P ?S ?KK ?ms => change (aevt RT P S KK ms) end.
    apply (POST Σ2 m2 F2 t0' t1' t2' e0 e1 e2 e3 e4 e5 e6 e7 s6' s7' t3' t4' t5' t6').

    assert (LVE : live_remove p (rt_live RT Σ1) = rt_live RT Σ).
    { rewrite LV1. apply live_remove_hd. intros [q k] Hin Eq. cbn [fst] in Eq. subst q.
      destruct (LPA p k Hin) as (k' & Hin' & K0).
      pose proof (af_live_disj RT AF Σ1 m1 p EXC_SIZE p k' [] (rt_live RT Σ) ART1 ltac:(rewrite LV1; reflexivity) Hin'). clear - H K0. ul. }
    rewrite LVE, FRS1 in PRES2.
    unfold site_postB. fold fsz.
    split; [rewrite <- CR1; exact HA2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [rewrite LV2; exact LVE|]. split; [rewrite FR2; exact FRS1|]. split; [rewrite SP02; exact SP01|]. split; [reflexivity|].
    split; [exact EHG2|]. split; [exact UB2'|]. split; [exact WR2|].
    intros x Hx NE NU. rewrite (PRES2 x); [apply AG4; apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto| auto| clear - FSZ; lia]| | | exact NE| exact NU].
    - apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto| auto| clear - FSZ; ul].
    - destruct (aclient_split_c RT AF Σ m (usp + fsz) (bv_unsigned x) ARTg Hx) as [H|H]; clear - H FSZ WLO UB1; ul.
  Qed.
End SiteCoreB.

Definition XP_none (m : mem) (usp : Z) : Prop := True.
Definition RGS_s1 (usp : Z) (s1 : word) : Prop := s1 = Z_to_bv 64 SHB /\ 0 <= usp /\ usp + 144 < 2^63.

Lemma XP_none_T : forall RA (m m' : mem) usp, XP_none m usp -> agree_on (fun x => usp <= x < usp + kd_fsz RA) m m' -> XP_none m' usp.
Proof. intros; exact I. Qed.

Section SitesB.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC : rt_contracts RT.
  Hypothesis ALC : aligned_alloc_contract RT.
  Variable WIN : rt_win RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis XROW : forall c Σ (m : mem), ARTW RT WIN c Σ m -> io_ro_ok m.

  Local Ltac wka_std L :=
    intros xu xp xgp xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc xm YRG _ YP0 YP47 YP16 YBLK YSZ YMI _;
    unfold RGS_s1 in YRG; destruct YRG as (YE & _ & _); rewrite YE;
    exact (L xu xp xgp _ xt0 xt1 xt2 xs0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc xm YP0 YP47 YP16 YBLK YSZ YMI).

  Definition site_stmtB (pcs RA : Z) (XP : mem -> Z -> Prop) (RGS : Z -> word -> Prop) : Prop :=
    forall (Σ : rts RT) (K : config -> Prop) (usp lo spx : Z) (ws : list word) (uw : bool) (fr : list cell)
      (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    RGS usp s1 -> XP m usp -> hcells_okA m usp 0 (kd_hcs RA) ws -> rw_cells asegs m usp fr -> Z.of_nat (cells_size fr) = kd_fsz RA ->
    lposA (rt_live RT Σ) -> Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX -> mcost EXC_SIZE <= rt_credit RT Σ ->
    ART RT Σ m -> mem_inv asegs m -> stk asegs m lo usp ->
    0x7fff7f800000 <= lo -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 0x15000 <= usp -> usp + kd_fsz RA + 0xb0 <= rt_sp0 RT Σ -> rt_sp0 RT Σ <= usp + 0x3c000 ->
    usp mod 16 = 0 ->
    rw_cells asegs m EL_EHG_XA [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
    bytes_at asegs m EL_UNW_XA (map (fun b => Z_to_bv 8 b) (uw_bytesA uw)) /\ wr_at asegs m EL_UNW_XA 8 ->
    el_xdataA m -> (exists g : word, cells_at asegs m EL_CANARY_XA [C8 g]) -> El_xs_adaptA.el_auxvA spx m -> usp + kd_fsz RA <= spx ->
    (forall (Σ2 : rts RT) (m2 : mem) (F2 : bvmap 5 word) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' t3' t4' t5' t6' : word),
       site_postB RT WIN RA Σ Σ2 m m2 usp lo (rt_credit RT Σ - mcost EXC_SIZE) ->
       aevt RT PMc Σ2 K (MS (mkR (Z_to_bv 64 EL_LRET_XA) (Z_to_bv 64 (usp + kd_fsz RA)) gp (Z_to_bv 64 TPV_XA) t0' t1' t2'
                               (nth (kd_i0 RA) ws (Z_to_bv 64 0)) (nth (kd_i1 RA) ws (Z_to_bv 64 0)) a0' a1' a2' a3' a4' a5' a6' a7'
                               (kd_x18 RA ws s2) (kd_x19 RA ws s3) s4 s5
                               s6' s7' s8 s9 s10 s11 t3' t4' t5' t6')
                          F2 (Z_to_bv 64 EL_LRET_XA) fc None m2 (seg_rom asegs))) ->
    aevt RT PMc Σ K (MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TPV_XA) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 pcs) fc None m (seg_rom asegs)).

  Local Ltac siteB RA RA0 RA1 XP RGS XPT WKA WKB :=
    unfold site_stmtB; intros Σ K usp lo spx ws uw fr ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RG0 XP0 HC FR CSZ LPA LVB CRB ARTg MIg STg LLO WLO LOR SP1 SP2 U16 EHG UNW XD CAN AUX SPX POST;
    apply (aevt_evt RT AF PMc MST); unfold TPV_XA; zstep; zstep; apply evt_done;
    change 6979176 with TPV_XA; change 1074508 with EL_CXA_ALLOC_XA;
    exact (site_rawB RT AF RC ALC WIN PMc FDO MST XROW RA RA0 RA1 ltac:(unfold kd_ok; tauto) XP RGS XPT ltac:(WKA) WKB ltac:(lia) ltac:(lia)
             Σ K usp lo spx ws uw fr gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             RG0 XP0 HC FR CSZ LPA LVB CRB ARTg MIg STg LLO WLO LOR SP1 SP2 U16 EHG UNW XD CAN AUX SPX POST).

  Theorem site_rawB_b272c : site_stmtB 0xb272c 0xb2d1c XP_none RGS_s1.
  Proof using AF RC ALC FDO MST XROW. siteB 0xb2d1c 0xb2734 0xb2780 XP_none RGS_s1 (XP_none_T 0xb2d1c) ltac:(wka_std siteA_b272c) siteB_b272c. Qed.
  Theorem site_rawB_b27f8 : site_stmtB 0xb27f8 0xb2d1c XP_none RGS_s1.
  Proof using AF RC ALC FDO MST XROW. siteB 0xb2d1c 0xb2800 0xb2840 XP_none RGS_s1 (XP_none_T 0xb2d1c) ltac:(wka_std siteA_b27f8) siteB_b27f8. Qed.
  Theorem site_rawB_b29e8 : site_stmtB 0xb29e8 0xb2d1c XP_none RGS_s1.
  Proof using AF RC ALC FDO MST XROW. siteB 0xb2d1c 0xb29f0 0xb2a30 XP_none RGS_s1 (XP_none_T 0xb2d1c) ltac:(wka_std siteA_b29e8) siteB_b29e8. Qed.
  Theorem site_rawB_b2ac4 : site_stmtB 0xb2ac4 0xb2d1c XP_none RGS_s1.
  Proof using AF RC ALC FDO MST XROW. siteB 0xb2d1c 0xb2acc 0xb2b0c XP_none RGS_s1 (XP_none_T 0xb2d1c) ltac:(wka_std siteA_b2ac4) siteB_b2ac4. Qed.
  Theorem site_rawB_b2b84 : site_stmtB 0xb2b84 0xb2d1c XP_none RGS_s1.
  Proof using AF RC ALC FDO MST XROW. siteB 0xb2d1c 0xb2b8c 0xb2bcc XP_none RGS_s1 (XP_none_T 0xb2d1c) ltac:(wka_std siteA_b2b84) siteB_b2b84. Qed.
  Theorem site_rawB_b2c64 : site_stmtB 0xb2c64 0xb2d1c XP_none RGS_s1.
  Proof using AF RC ALC FDO MST XROW. siteB 0xb2d1c 0xb2c6c 0xb2ca8 XP_none RGS_s1 (XP_none_T 0xb2d1c) ltac:(wka_std siteA_b2c64) siteB_b2c64. Qed.
  Theorem site_rawB_b2cc0 : site_stmtB 0xb2cc0 0xb2d1c XP_none RGS_s1.
  Proof using AF RC ALC FDO MST XROW. siteB 0xb2d1c 0xb2cc8 0xb2d04 XP_none RGS_s1 (XP_none_T 0xb2d1c) ltac:(wka_std siteA_b2cc0) siteB_b2cc0. Qed.
  Theorem site_rawB_b2d2c : site_stmtB 0xb2d2c 0xb2d1c XP_none RGS_s1.
  Proof using AF RC ALC FDO MST XROW. siteB 0xb2d1c 0xb2d34 0xb2d74 XP_none RGS_s1 (XP_none_T 0xb2d1c) ltac:(wka_std siteA_b2d2c) siteB_b2d2c. Qed.
  Theorem site_rawB_b2fb4 : site_stmtB 0xb2fb4 0xb3014 XP_none RGS_s1.
  Proof using AF RC ALC FDO MST XROW. siteB 0xb3014 0xb2fbc 0xb2ffc XP_none RGS_s1 (XP_none_T 0xb3014) ltac:(wka_std siteA_b2fb4) siteB_b2fb4. Qed.
  Theorem site_rawB_b3170 : site_stmtB 0xb3170 0xb31d0 XP_none RGS_s1.
  Proof using AF RC ALC FDO MST XROW. siteB 0xb31d0 0xb3178 0xb31b8 XP_none RGS_s1 (XP_none_T 0xb31d0) ltac:(wka_std siteA_b3170) siteB_b3170. Qed.
End SitesB.
