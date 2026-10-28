(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_num_kitu Sj_num_kitn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition PMU_ENTRY : Z := 0x5ceb0.
Definition PMU_POW10 : Z := 0x1ab98.

Definition pmu_pow10_tbl : list byte :=
  Eval vm_compute in match image_bytes usegs PMU_POW10 160 with Some bs => bs | None => [] end.
Lemma pmu_pow10_len : length pmu_pow10_tbl = 160%nat.
Proof. reflexivity. Qed.
Lemma pmu_pow10_at : forall m, mem_inv usegs m -> bytes_at usegs m PMU_POW10 pmu_pow10_tbl.
Proof.
  intros m MI.
  assert (RO : ro_cells usegs m PMU_POW10 [CB (length pmu_pow10_tbl) pmu_pow10_tbl]).
  { apply (ro_cells_image usegs m PMU_POW10 pmu_pow10_tbl MI); [vm_compute; reflexivity | unfold PMU_POW10; lia | unfold PMU_POW10; cbn; lia]. }
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma pmu_pow10_nz : forall cn, (0 <= cn <= 19)%Z -> (0 < bv_unsigned (limbz pmu_pow10_tbl (8 * cn)))%Z.
Proof.
  intros cn H.
  assert (C : (cn = 0 \/ cn = 1 \/ cn = 2 \/ cn = 3 \/ cn = 4 \/ cn = 5 \/ cn = 6 \/ cn = 7 \/ cn = 8 \/ cn = 9 \/ cn = 10 \/ cn = 11 \/ cn = 12 \/
               cn = 13 \/ cn = 14 \/ cn = 15 \/ cn = 16 \/ cn = 17 \/ cn = 18 \/ cn = 19)%Z) by lia.
  repeat (destruct C as [->|C]; [vm_compute; reflexivity|]). subst cn. vm_compute. reflexivity.
Qed.

Record pmuenv : Type := mkPmuEnv {
  p_ra : word; p_sp : word; p_gp : word; p_tp : word;
  p_s0 : word; p_s1 : word; p_s2 : word; p_s3 : word; p_s4 : word; p_s5 : word;
  p_s6 : word; p_s7 : word; p_s8 : word; p_s9 : word; p_s10 : word; p_s11 : word;
  p_F : bvmap 5 word; p_fc : bv 32;
  p_X : Z; p_A : Z; p_IP : Z; p_IL : Z; p_FPT : Z; p_FL : Z; p_lo : Z; p_txt : list byte; p_m0 : mem }.

Notation p_SP E := (bv_unsigned (p_sp E)).
Notation p_TL E := (Z.of_nat (length (p_txt E))).

Record pmu_ok (E : pmuenv) : Prop := mkPmuOk {
  po_room : (p_lo E + PMU_STACK <= p_SP E)%Z;
  po_gtop : (NUMU_GTOP <= p_lo E)%Z;
  po_xlo : (p_SP E <= p_X E - 40)%Z;
  po_xhi : (p_X E + 512 <= 2^64)%Z;
  po_tlo : (p_A E + p_TL E <= p_lo E)%Z;
  po_tmax : (p_TL E < NUM_TXT_MAX)%Z;
  po_a0 : (0 < p_A E)%Z;
  po_spans : pm_spans_ok (p_A E) (p_txt E) (p_IP E) (p_IL E) (p_FPT E) (p_FL E) }.

Definition pmu_W (E : pmuenv) : list (Z * Z) := [(p_SP E - PMU_STACK, p_SP E); (p_X E, p_X E + 498); (p_X E + 504, p_X E + 512)]%Z.
Notation pmu_post E := (pmu_post_g usegs (p_ra E) (p_sp E) (p_gp E) (p_tp E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E)
                          (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (p_F E) (p_fc E)
                          (p_X E) (p_IP E) (p_IL E) (p_FPT E) (p_FL E) (p_lo E) (p_m0 E)).

Definition pmu_saved (E : pmuenv) : list cell :=
  [C8 (p_s11 E); C8 (p_s10 E); C8 (p_s9 E); C8 (p_s8 E); C8 (p_s7 E); C8 (p_s6 E); C8 (p_s5 E); C8 (p_s4 E); C8 (p_s3 E); C8 (p_s2 E); C8 (p_s1 E);
   C8 (p_s0 E); C8 (p_ra E)].
Definition pmu_spans (E : pmuenv) : list cell :=
  [C8 (Z_to_bv 64 (p_IP E)); C8 (Z_to_bv 64 (p_IL E)); C8 (Z_to_bv 64 (p_FPT E)); C8 (Z_to_bv 64 (p_FL E))].

Definition PMUINVg (E : pmuenv) (mm : mem) (len dg : Z) (v16 : word) (P : Prop) : Prop :=
  (exists j v8, rw_cells usegs mm (p_SP E + -128) (CB 8 j :: C8 v8 :: C8 v16 :: pmu_saved E)) /\
  (exists bs, u8arr usegs mm (p_X E) bs /\ length bs = 496%nat /\ (P -> bignorm_b bs len)) /\
  rw_cells usegs mm (p_X E + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
  rw_cells usegs mm (p_X E + 504) [C8 (Z_to_bv 64 dg)] /\
  rw_cells usegs mm (p_X E + -40) (pmu_spans E) /\
  bytes_at usegs mm (p_A E) (p_txt E) /\
  bytes_at usegs mm PMU_POW10 pmu_pow10_tbl /\
  mem_inv usegs mm /\ munch (pmu_W E) (p_m0 E) mm /\ wmono usegs (p_m0 E) mm /\ stk usegs mm (p_lo E) (p_SP E + -128).
Notation PMUINV E mm len dg v16 := (PMUINVg E mm len dg v16 (dg < PMU_NORM_DG)%Z).

Ltac pm_open H :=
  let j := fresh "j" in let v8 := fresh "v8" in let bs := fresh "bs" in
  destruct H as ((j & v8 & FR) & (bs & XA & ?XL & NB) & XN & ?LEN & DG & SPANS & TXT & TBL & MI & MU & WM & ST);
  unfold pmu_saved in FR; unfold pmu_spans in SPANS; unfold pmu_W, PMU_STACK in MU; unfold PMU_POW10 in TBL; unfold PMU_NORM_DG in NB;
  let TXB := fresh "TXB" in pose proof (bytes_at_bound _ _ _ _ TXT) as TXB;
  let TBLL := fresh "TBLL" in pose proof pmu_pow10_len as TBLL.

Ltac pm_close_with nb :=
  lazymatch goal with
  | |- PMUINVg _ _ _ _ _ _ =>
      split; [eexists; eexists; eassumption|]; split; [eexists; split; [eassumption| split; [lia | unfold PMU_NORM_DG; nb]]|];
      split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
      split; [eassumption|];
      split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac pm_close := pm_close_with ltac:(first [ eassumption | intro; exfalso; lia | intro; lazymatch goal with NB : _ -> bignorm_b _ _ |- _ => apply NB; lia end ]).

Notation PM E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
  (MS (mkR xra (Z_to_bv 64 (p_SP E + -128)) (p_gp E) (p_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) (p_F E) (Z_to_bv 64 pc) (p_fc E) None mm (seg_rom usegs)).

Ltac pm_env OK :=
  let ROOM := fresh "ROOM" in let GTOP := fresh "GTOP" in let XLO := fresh "XLO" in let XHI := fresh "XHI" in let TLO := fresh "TLO" in
  let TMAX := fresh "TMAX" in let A0 := fresh "A0" in let SPN := fresh "SPN" in
  destruct OK as [ROOM GTOP XLO XHI TLO TMAX A0 SPN];
  unfold PMU_STACK, NUMU_GTOP, NUM_TXT_MAX, pm_spans_ok in *;
  change (2 ^ 64)%Z with 18446744073709551616%Z in XHI;
  destruct SPN as (SPN1 & SPN2 & SPN3 & SPN4);
  lazymatch goal with E : pmuenv |- _ =>
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 (p_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR end.

Section PMUDEFS.
  Variable E : pmuenv.
  Hypothesis OK : pmu_ok E.
  Notation X := (p_X E).

  Lemma pm_exit : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len dg v16,
    PMUINV E mm len dg v16 -> (0 <= dg <= 770)%Z -> (19 * len <= 2 * dg + 76)%Z ->
    evt usegs (pmu_post E) (PM E 0x5de0c xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until v16. intros INV HD HC. pm_open INV. pm_env OK.
    do 13 zstep. zstep. zstep.
    release_frame FR ST (p_SP E).
    destruct (u64arr_of_u8arr_s usegs mm X bs XA XL) as (ws & WL & EW & WA).
    apply evt_done. unfold pmu_post_g. do 15 eexists. exists mm, ws, len, dg.
    split; [cbv delta [mkR]; reflexivity|].
    unfold PMU_STACK, bigint_at.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [split; [exact WA| split; [exact WL| split; [exact XN| lia]]] |].
    split; [exact DG|]. split; [exact SPANS|]. split; [exact ST|]. split; [lia|]. split; [lia|].
    unfold PMU_NORM_DG. intros HN. apply bignorm_of_b; [rewrite EW; apply NB; exact HN | lia].
  Qed.
End PMUDEFS.
