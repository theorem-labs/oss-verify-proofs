(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C10 ECH_AKit ECH_AsKit ECH_AC1_malloc ECH_AC1_free ECH_AC1_dup.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac ubal_any :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      lazymatch R with
      | context [Z.land ?x 7] =>
          first [ match goal with H : _ mod 16 = 0 |- _ => ubal_by H end
                | match goal with H : _ mod 8 = 0 |- _ => ubal_by H end
                | idtac ]
      | context [Z.land ?x 3] =>
          first [ match goal with H : _ mod 16 = 0 |- _ => ubal_by H end
                | match goal with H : _ mod 8 = 0 |- _ => ubal_by H end
                | match goal with H : _ mod 4 = 0 |- _ => ubal_by H end
                | idtac ]
      | _ => idtac
      end
  | _ => idtac
  end.
Local Ltac if_lit :=
  match goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      tryif (match c with context [?x] => is_var x end) then fail 1 "if_lit: open condition" else
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition APM_RA1 : Z := 0x554a60.    Definition APM_RA2 : Z := 0x554adc.    Definition APM_RET : Z := 0x554b00.
  Definition APS_RA1 : Z := 0x554e04.    Definition APS_RA2 : Z := 0x554e4c.
  Definition APK_FILE : Z := 0x400aa.   (* [comment removed for export] *)
  Definition SHB : Z := 0x7fff8000.      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition apm_frame (s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
    [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition aps_frame (s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition apm1_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s6 s8 : word)
      (F : bvmap 5 word) (fc : bv 32) (pkt dptr lptr lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1,
      ms' = MS (mkR (Z_to_bv 64 APM_RA1) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 lptr)
                   (Z_to_bv 64 0) (Z_to_bv 64 APK_FILE) (Z_to_bv 64 518) a3 a4 a5 a6 a7
                   (Z_to_bv 64 dptr) (Z_to_bv 64 pkt) s4 s5 (Z_to_bv 64 (Z.shiftr dptr 3 + SHB)) (Z_to_bv 64 SHB) s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
      /\ munch [(bv_unsigned sp + -80, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp + -80)
      /\ rw_cells asegs m1 (bv_unsigned sp + -80) (apm_frame s8 s7 s6 s5 s4 s3 s2 s1 s0 ra).

  Lemma apm_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (pkt dptr lptr lo : Z),
      rw_cells asegs m dptr [C8 (wz 0)] -> (dptr + 8 <= lo \/ bv_unsigned sp <= dptr) ->
      accessible m dptr 8 -> dptr mod 8 = 0 ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 80 -> mem_inv asegs m ->
      evt asegs (apm1_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s6 s8 F fc pkt dptr lptr lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pkt) (Z_to_bv 64 dptr) (Z_to_bv 64 lptr) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_PACKET_memdup) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros DP OD ACC ALD GSB SHB0 ST CEIL LO MI. acb. unfold P_PACKET_memdup, P_CRYPTO_free. unfold wz in DP.
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    pose proof (aword_range sp) as SPR. pose proof (rw_cells_bound _ _ _ _ DP) as DB. cbn [cells_size csize Nat.add] in DB.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACC as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 80%nat ST.
    (* [comment removed for export] *)
    pose proof ACC as ACC'. clear ACC. change (id (accessible m dptr 8)) in ACC'.
    do 15 st1. ubal_any. if_lit. do 6 st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx dptr 8)
        by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU|]; constructor; [cbn; unfold AHI_LO in *; lia| constructor]);
      rename mx into m0 end.
    clear ACC'.
    (* [comment removed for export] *)
    ck8_check ACC dptr.
    (* [comment removed for export] *)
    do 6 st1.
    (* [comment removed for export] *)
    st1.
    unfold apm1_post, APM_RA1, APK_FILE, SHB. finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition apm2_post (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : word)
      (F : bvmap 5 word) (fc : bv 32) (pkt cur ms len dptr lptr : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1,
      ( (len = 0 /\ exists a1x : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1x a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m1 (seg_rom asegs))
        \/ (len <> 0 /\
         ms' = MS (mkR (Z_to_bv 64 APM_RA2) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 lptr)
                      (Z_to_bv 64 cur) (Z_to_bv 64 len) (Z_to_bv 64 APK_FILE) (Z_to_bv 64 527) a4 a5 a6 a7
                      (Z_to_bv 64 dptr) (Z_to_bv 64 pkt) (Z_to_bv 64 1) (Z_to_bv 64 len)
                      (Z_to_bv 64 (Z.shiftr dptr 3 + SHB)) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr lptr 3 + SHB)) s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 P_CRYPTO_memdup) fc None m1 (seg_rom asegs)
         /\ rw_cells asegs m1 (bv_unsigned sp + -80) (apm_frame s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) )
      /\ munch [(dptr, dptr + 8); (lptr, lptr + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 pkt (pk_cells cur ms len)
      /\ rw_cells asegs m1 dptr [C8 (wz 0)] /\ rw_cells asegs m1 lptr [C8 (wz 0)].

  Lemma apm_seg2 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (pkt cur ms len dptr lptr oldlen : Z),
      rw_cells asegs m pkt (pk_cells cur ms len) -> 0 <= len < 2^64 ->
      rw_cells asegs m dptr [C8 (wz 0)] -> rw_cells asegs m lptr [C8 (wz oldlen)] -> cells_apart dptr lptr ->
      apart pkt 24 dptr 8 -> apart pkt 24 lptr 8 ->
      (dptr + 8 <= bv_unsigned sp + -80 \/ bv_unsigned sp <= dptr) -> (lptr + 8 <= bv_unsigned sp + -80 \/ bv_unsigned sp <= lptr) ->
      (dptr + 8 <= ALOWSH_LO \/ AHI_LO <= dptr) -> (lptr + 8 <= ALOWSH_LO \/ AHI_LO <= lptr) ->
      accessible m pkt 24 -> accessible m dptr 8 -> accessible m lptr 8 ->
      rw_cells asegs m (bv_unsigned sp + -80) (apm_frame s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) -> mem_inv asegs m -> lptr mod 8 = 0 -> pkt mod 8 = 0 ->
      evt asegs (apm2_post sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 F fc pkt cur ms len dptr lptr m)
        (MS (mkR (Z_to_bv 64 APM_RA1) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 lptr)
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 dptr) (Z_to_bv 64 pkt) s4 s5 (Z_to_bv 64 (Z.shiftr dptr 3 + SHB)) (Z_to_bv 64 SHB) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 APM_RA1)) fc None m (seg_rom asegs)).
  Proof.
    intros until oldlen. intros PK HL DP LP AP APD APL OD OL NSD NSL ACCP ACCD ACCL FR MI. unfold APM_RA1, APM_RA2, APK_FILE, SHB, P_CRYPTO_memdup in *.
    replace (ret_pc (Z_to_bv 64 0x554a60)) with (Z_to_bv 64 0x554a60) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold cells_apart, apart, pk_cells, apm_frame, wz in *.
    pose proof (aword_range sp) as SPR.
    pose proof (rw_cells_bound _ _ _ _ DP) as DB. pose proof (rw_cells_bound _ _ _ _ LP) as LBB. pose proof (rw_cells_bound _ _ _ _ PK) as PB.
    cbn [cells_size csize Nat.add] in DB, LBB, PB.
    pose proof ACCP as (_ & PHI & _). unfold AAPP_HI in PHI.
    pose proof (munch_refl [(dptr, dptr + 8); (lptr, lptr + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    intros ALL ALP. ck8_check ACCD dptr.
    (* [comment removed for export] *)
    pose proof ACCP as ACCP'. clear ACCP. change (id (accessible m pkt 24)) in ACCP'.
    pose proof ACCL as ACCL'. clear ACCL. change (id (accessible m lptr 8)) in ACCL'. clear ACCD.
    (* [comment removed for export] *)
    do 3 st1. ubal_any. if_lit. do 2 st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCL : accessible mx lptr 8)
        by (unfold id in ACCL'; eapply accessible_across; [exact ACCL'| exact MU|]; constructor; [cbn; lia| constructor; [cbn; lia| constructor]]) end.
    clear ACCL'.
    (* [comment removed for export] *)
    ck8_check ACCL lptr. clear ACCL.
    (* [comment removed for export] *)
    do 3 st1. ubal_any. if_lit. do 3 st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCP : accessible mx pkt 24)
        by (unfold id in ACCP'; eapply accessible_across; [exact ACCP'| exact MU|]; constructor; [cbn; lia| constructor; [cbn; lia| constructor]]) end.
    clear ACCP'.
    (* [comment removed for export] *)
    ck8_check ACCP (pkt + 16).
    do 3 st1. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      do 13 st1. apply evt_done. eexists. split; [left; split; [| eexists; reflexivity]|].
      { revert K0. rewrite ?unsigned_lit by lia. lia. }
      repeat (split; [assumption|]). assumption.
    - (* [comment removed for export] *)
      do 2 st1. ck8_check ACCP pkt.
      do 7 st1. apply evt_done. eexists. split; [right; split; [| split; [reflexivity| eassumption]]|].
      { revert K0. rewrite ?unsigned_lit by lia. lia. }
      repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma apm_seg3 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (pkt len dptr lptr D : Z),
      0 < D < 2^64 -> 0 <= len < 2^64 ->
      rw_cells asegs m dptr [C8 (wz 0)] -> rw_cells asegs m lptr [C8 (wz 0)] -> cells_apart dptr lptr ->
      (dptr + 8 <= bv_unsigned sp + -80 \/ bv_unsigned sp <= dptr) -> (lptr + 8 <= bv_unsigned sp + -80 \/ bv_unsigned sp <= lptr) ->
      (dptr + 8 <= ALOWSH_LO \/ AHI_LO <= dptr) -> (lptr + 8 <= ALOWSH_LO \/ AHI_LO <= lptr) ->
      accessible m dptr 8 -> accessible m lptr 8 ->
      rw_cells asegs m (bv_unsigned sp + -80) (apm_frame s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (a1x : word) m1,
                   ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1x a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (ret_pc ra) fc None m1 (seg_rom asegs)
                   /\ munch [(dptr, dptr + 8); (lptr, lptr + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
                   /\ rw_cells asegs m1 dptr [C8 (wz D)] /\ rw_cells asegs m1 lptr [C8 (wz len)])
        (MS (mkR (Z_to_bv 64 APM_RA2) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 lptr)
                 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 dptr) (Z_to_bv 64 pkt) (Z_to_bv 64 1) (Z_to_bv 64 len)
                 (Z_to_bv 64 (Z.shiftr dptr 3 + SHB)) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr lptr 3 + SHB)) s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 APM_RA2)) fc None m (seg_rom asegs)).
  Proof.
    intros until D. intros HD HL DP LP AP OD OL NSD NSL ACCD ACCL FR MI. unfold APM_RA2, SHB in *.
    replace (ret_pc (Z_to_bv 64 0x554adc)) with (Z_to_bv 64 0x554adc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold cells_apart, apart, apm_frame, wz in *.
    pose proof (aword_range sp) as SPR.
    pose proof (rw_cells_bound _ _ _ _ DP) as DB. pose proof (rw_cells_bound _ _ _ _ LP) as LBB. cbn [cells_size csize Nat.add] in DB, LBB.
    pose proof (munch_refl [(dptr, dptr + 8); (lptr, lptr + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    ck8_check ACCD dptr. clear ACCD.
    pose proof ACCL as ACCL'. clear ACCL. change (id (accessible m lptr 8)) in ACCL'.
    (* [comment removed for export] *)
    do 2 st1. ub_dead.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCL : accessible mx lptr 8)
        by (unfold id in ACCL'; eapply accessible_across; [exact ACCL'| exact MU|]; constructor; [cbn; lia| constructor; [cbn; lia| constructor]]) end.
    clear ACCL'.
    (* [comment removed for export] *)
    ck8_check ACCL lptr. clear ACCL.
    do 15 st1. finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition aps1_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 : word)
      (F : bvmap 5 word) (fc : bv 32) (pkt dptr lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1,
      ms' = MS (mkR (Z_to_bv 64 APS_RA1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 dptr)
                   (Z_to_bv 64 0) (Z_to_bv 64 APK_FILE) (Z_to_bv 64 547) a3 a4 a5 a6 a7
                   (Z_to_bv 64 pkt) (Z_to_bv 64 (Z.shiftr dptr 3 + SHB)) (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
      /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp + -48)
      /\ rw_cells asegs m1 (bv_unsigned sp + -48) (aps_frame s4 s3 s2 s1 s0 ra).

  Lemma aps_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (pkt dptr lo : Z),
      rw_cells asegs m dptr [C8 (wz 0)] -> (dptr + 8 <= lo \/ bv_unsigned sp <= dptr) ->
      accessible m dptr 8 -> dptr mod 8 = 0 ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m ->
      evt asegs (aps1_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 F fc pkt dptr lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pkt) (Z_to_bv 64 dptr) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_PACKET_strndup) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros DP OD ACC ALD GSB SHB0 ST CEIL LO MI. acb. unfold P_PACKET_strndup, P_CRYPTO_free. unfold wz in DP.
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    pose proof (aword_range sp) as SPR. pose proof (rw_cells_bound _ _ _ _ DP) as DB. cbn [cells_size csize Nat.add] in DB.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACC as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 48%nat ST.
    pose proof ACC as ACC'. clear ACC. change (id (accessible m dptr 8)) in ACC'.
    do 11 st1. ubal_any. if_lit. do 6 st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx dptr 8)
        by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU|]; constructor; [cbn; unfold AHI_LO in *; lia| constructor]);
      rename mx into m0 end.
    clear ACC'.
    (* [comment removed for export] *)
    ck8_check ACC dptr.
    (* [comment removed for export] *)
    do 5 st1.
    (* [comment removed for export] *)
    st1.
    unfold aps1_post, APS_RA1, APK_FILE, SHB. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma aps_seg2 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0x : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (pkt cur ms len dptr : Z),
      rw_cells asegs m pkt (pk_cells cur ms len) -> accessible m pkt 24 -> mem_inv asegs m -> pkt mod 8 = 0 ->
      evt asegs (fun ms' =>
                   ms' = MS (mkR (Z_to_bv 64 APS_RA2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x (Z_to_bv 64 dptr)
                                 (Z_to_bv 64 cur) (Z_to_bv 64 len) (Z_to_bv 64 APK_FILE) (Z_to_bv 64 550) a4 a5 a6 a7
                                 (Z_to_bv 64 pkt) (Z_to_bv 64 (Z.shiftr dptr 3 + SHB)) (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 P_CRYPTO_strndup) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 APS_RA1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x (Z_to_bv 64 dptr)
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pkt) (Z_to_bv 64 (Z.shiftr dptr 3 + SHB)) (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 APS_RA1)) fc None m (seg_rom asegs)).
  Proof.
    intros until dptr. intros PK ACCP MI. unfold APS_RA1, APS_RA2, APK_FILE, SHB, P_CRYPTO_strndup.
    replace (ret_pc (Z_to_bv 64 0x554e04)) with (Z_to_bv 64 0x554e04) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold pk_cells, wz in PK. pose proof (aword_range sp) as SPR.
    pose proof (rw_cells_bound _ _ _ _ PK) as PB. cbn [cells_size csize Nat.add] in PB.
    pose proof ACCP as (_ & PHI & _). unfold AAPP_HI in PHI.
    (* [comment removed for export] *)
    intros ALP. do 2 st1. ubal_any. if_lit. do 2 st1. ck8_check ACCP pkt.
    (* [comment removed for export] *)
    do 3 st1. ck8_check ACCP (pkt + 16).
    (* [comment removed for export] *)
    do 7 st1. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma aps_seg3 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (pkt dptr D : Z),
      0 < D < 2^64 ->
      rw_cells asegs m dptr [C8 (wz 0)] -> (dptr + 8 <= bv_unsigned sp + -48 \/ bv_unsigned sp <= dptr) ->
      accessible m dptr 8 ->
      rw_cells asegs m (bv_unsigned sp + -48) (aps_frame s4 s3 s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
                   ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (ret_pc ra) fc None m1 (seg_rom asegs)
                   /\ munch [(dptr, dptr + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
                   /\ rw_cells asegs m1 dptr [C8 (wz D)])
        (MS (mkR (Z_to_bv 64 APS_RA2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 dptr)
                 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pkt) (Z_to_bv 64 (Z.shiftr dptr 3 + SHB)) (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 APS_RA2)) fc None m (seg_rom asegs)).
  Proof.
    intros until D. intros HD DP OD ACCD FR MI. unfold APS_RA2, SHB in *.
    replace (ret_pc (Z_to_bv 64 0x554e4c)) with (Z_to_bv 64 0x554e4c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold aps_frame, wz in *. pose proof (aword_range sp) as SPR.
    pose proof (rw_cells_bound _ _ _ _ DP) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (munch_refl [(dptr, dptr + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    ck8_check ACCD dptr. clear ACCD.
    (* [comment removed for export] *)
    do 10 st1. replace (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 D)) with (Z_to_bv 64 1) by (rewrite v_sltu_b2z, !unsigned_lit by lia; destruct (Z.ltb_spec 0 D); [reflexivity| lia]).
    (* [comment removed for export] *)
    st1. finish.
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bx (P : Prop) : Prop := P.
Ltac box H := let T := type of H in change (bx T) in H.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Local Definition XM (pkt dptr lptr : Z) : list (Z * Z) := [(pkt, pkt + 24); (dptr, dptr + 8); (lptr, lptr + 8)] ++ memflag_foot.

  Lemma apkmemdup_spec : pkmemdup_stmt H.
  Proof.
    unfold pkmemdup_stmt. intros until CH.
    intros VIS A0 A1 A2 PK OBP PKB DP LP AP OBD OBL APD APL ACD ACL ACP BS HBIN HBLO HBHI HL ALP ALD ALL
           RFS AWD AWL ACCP ACCD ACCL ACCC HP KREL BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS OCD OCL PF HAL MF IM GM.
    assert (V01 : v = 0 \/ v = 1) by (destruct MF as (fbq & _ & _ & Kv); exact Kv).   (* [comment removed for export] *)
    unfold PKMEMDUP_STACK, FR_PACKET_memdup, CMEMDUP_STACK, CFREE_STACK, CMALLOC_STACK, FR_CRYPTO_memdup, FR_CRYPTO_malloc, AMALLOC_STACK, AFREE_STACK in LO.
    acb. subst a0 a1 a2 tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (CSP0 : aceil <= bv_unsigned sp) by lia. assert (CSP : aceil <= bv_unsigned sp + -80) by lia.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    unfold cells_apart, apart in AP, APD, APL, ACD, ACL, ACP. unfold offchain in OCD, OCL.
    box AP; box APD; box APL; box ACD; box ACL; box ACP.
    pose proof (rw_cells_bound _ _ _ _ PK) as PB. unfold pk_cells in PB. cbn [cells_size csize Nat.add] in PB.
    pose proof (rw_cells_bound _ _ _ _ DP) as DB. pose proof (rw_cells_bound _ _ _ _ LP) as LBB. cbn [cells_size csize Nat.add] in DB, LBB.
    pose proof (proj1 (ah_costs H HH) (Z.of_nat (length bs)) ltac:(lia)) as CM0.
    (* [comment removed for export] *)
    pose proof (ashobj_bounds H HH _ _ _ _ _ _ HP CSP0 OBP ltac:(lia)) as [PT PNS].
    pose proof (ashobj_bounds H HH _ _ _ _ _ _ HP CSP0 OBD ltac:(lia)) as [DT DNS].
    pose proof (ashobj_bounds H HH _ _ _ _ _ _ HP CSP0 OBL ltac:(lia)) as [LT LNS].
    pose proof (ashobj_off_frame H HH _ _ _ _ _ _ lo HP OBP CEIL) as OFFP.
    pose proof (ashobj_off_frame H HH _ _ _ _ _ _ lo HP OBD CEIL) as OFFD.
    pose proof (ashobj_off_frame H HH _ _ _ _ _ _ lo HP OBL CEIL) as OFFL.
    pose proof (ashobj_lowerSP H _ _ (bv_unsigned sp + -80) _ _ OBP ltac:(lia)) as OBP'.
    pose proof (ashobj_lowerSP H _ _ (bv_unsigned sp + -80) _ _ OBD ltac:(lia)) as OBD'.
    pose proof (ashobj_lowerSP H _ _ (bv_unsigned sp + -80) _ _ OBL ltac:(lia)) as OBL'.
    destruct bC as [[pC AC_] nC]. cbn [blk_addr blk_size fst snd] in HBLO, HBHI.
    pose proof (ah_blocks H HH _ _ _ _ HP HBIN) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4, K5, K6, K7. unfold AIMG_TOP in K4.
    assert (OBC' : ashobj H LB (bv_unsigned sp + -80) cur (Z.of_nat (length bs))).
    { left. exists (pC, AC_, nC). split; [exact HBIN| cbn; lia]. }
    pose proof (ACONST_shbase m AC) as [GSB SHB0].
    unfold AIMG_TOP in PT, DT, LT. clear PNS K6.
    box OFFP; box OFFD; box OFFL; box DNS; box LNS.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply apm_seg1 with (lo := lo); [exact DP| exact OFFD| exact ACCD| exact ALD| exact GSB| exact SHB0| exact ST| exact CEIL| clear - LO; lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -80, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -80, bv_unsigned sp)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]. }
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). unfold AIMG_TOP in F1.
    assert (FW : Forall (afs_write_ok H LF) [(bv_unsigned sp + -80, bv_unsigned sp)]).
    { constructor; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *; lia| constructor]. }
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(bv_unsigned sp + -80, bv_unsigned sp)]).
    { constructor; [cbn; unfold AHI_LO in *; lia| constructor]. }
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]).
    assert (RFS1 : as_RFS H LF m1) by (eapply (ah_RFS_frame H HH); [exact RFS| exact MU1| exact WM1| exact FW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (MF1 : MEMFLAG m1 v) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (PK1 : rw_cells asegs m1 pkt (pk_cells cur ms (Z.of_nat (length bs)))) by (unfold bx in OFFP; eapply rw_cells_transport; [exact PK| exact MU1| exact WM1| cbn; lia]).
    assert (LP1 : rw_cells asegs m1 lptr [C8 (wz oldlen)]) by (unfold bx in OFFL; eapply rw_cells_transport; [exact LP| exact MU1| exact WM1| cbn; lia]).
    assert (DP1 : rw_cells asegs m1 dptr [C8 (wz 0)]) by (unfold bx in OFFD; eapply rw_cells_transport; [exact DP| exact MU1| exact WM1| cbn; lia]).
    assert (BS1 : bytes_at asegs m1 cur bs) by (eapply bytes_at_transport; [exact BS| exact MU1| cbn; lia]).
    assert (ACCP1 : accessible m1 pkt 24) by (eapply accessible_across; [exact ACCP| exact MU1| exact NSW]).
    assert (ACCD1 : accessible m1 dptr 8) by (eapply accessible_across; [exact ACCD| exact MU1| exact NSW]).
    assert (ACCL1 : accessible m1 lptr 8) by (eapply accessible_across; [exact ACCL| exact MU1| exact NSW]).
    assert (ACCC1 : accessible m1 cur (Z.of_nat (length bs))) by (eapply accessible_across; [exact ACCC| exact MU1| exact NSW]).
    assert (XP1 : xpres H LB (bv_unsigned sp) (XM pkt dptr lptr) m m1).
    { eapply (xpres_of_munch H s LB _ _ _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    clear CW AW FW NSW.
    (* [comment removed for export] *)
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. constructor; [left; cbn; lia| constructor]. }
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SP16| lia| lia|].
      pose proof FR1 as FR2. unfold apm_frame in FR2.
      change ([C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -80 + 64) by lia.
      rewrite Z_to_bv_bv_unsigned || idtac. exact FR2 || (revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2). }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -80 + 16 <= fp').
    { intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]. }
    (* [comment removed for export] *)
    pose proof (acfree_null_spec H HH) as CF. unfold cfree_null_stmt in CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB) (s := s) (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS1| ..]; rewrite ?unsigned_lit by lia.
      all: lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- as_rauxv_ok _ _ _ => exact AUX1
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => exact ERR1
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; rewrite Zminus_mod, SP16; reflexivity
           | |- ACONST _ => exact AC1
           | |- as_chain _ _ _ _ => exact CH1
           | |- forall fp' ra', In _ _ -> _ => exact CHS1
           | |- _ <= as_AL _ _ => lia
           | |- IMPL_mem _ => exact IM1
           | |- GOT_mem _ => exact GM1
           | |- _ => first [assumption | lia | unfold CFREE_STACK, AFREE_STACK; lia | match goal with |- ?G => idtac "LEFT:" G end]
           end. }
    intros [msF2 mo2] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s2' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & HP2 & IM2 & GM2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -80)) in ST2, XP2 by lia.
    pose proof (xpres_nil_apres H _ _ _ _ XP2) as AP2.
    eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| constructor]. rename FR1 into FR2.
    assert (PK2 : rw_cells asegs m2 pkt (pk_cells cur ms (Z.of_nat (length bs)))).
    { eapply (apres_rw_cells H); [exact AP2| exact PK1| apply (ashobj_client_range H); exact OBP']. }
    assert (DP2 : rw_cells asegs m2 dptr [C8 (wz 0)]) by (eapply (apres_rw_cells H); [exact AP2| exact DP1| apply (ashobj_client_range H); exact OBD']).
    assert (LP2 : rw_cells asegs m2 lptr [C8 (wz oldlen)]) by (eapply (apres_rw_cells H); [exact AP2| exact LP1| apply (ashobj_client_range H); exact OBL']).
    assert (BS2 : bytes_at asegs m2 cur bs) by (eapply (xpres_bytes_at' H); [exact XP2| exact BS1| apply (ashobj_client_range H); exact OBC'| constructor]).
    assert (ACCP2 : accessible m2 pkt 24) by (eapply (ashobj_accessible_xpres H HH); [exact HP1| exact CSP| exact OBP'| exact ACCP1| exact XP2| constructor]).
    assert (ACCD2 : accessible m2 dptr 8) by (eapply (ashobj_accessible_xpres H HH); [exact HP1| exact CSP| exact OBD'| exact ACCD1| exact XP2| constructor]).
    assert (ACCL2 : accessible m2 lptr 8) by (eapply (ashobj_accessible_xpres H HH); [exact HP1| exact CSP| exact OBL'| exact ACCL1| exact XP2| constructor]).
    assert (ACCC2 : accessible m2 cur (Z.of_nat (length bs))) by (eapply (ashobj_accessible_xpres H HH); [exact HP1| exact CSP| exact OBC'| exact ACCC1| exact XP2| constructor]).
    assert (RFS2 : as_RFS H LF m2) by (eapply (RFS_via_apres H HH); [exact RFS1| exact AP2]).
    assert (MF2 : MEMFLAG m2 v) by (eapply (MEMFLAG_apres H); [exact AP2| exact MF1]).
    assert (CH2 : as_chain H m2 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (chain_via_apres H HH); [exact CH1| exact AP2| exact CHS1]. }
    assert (XP12 : xpres H LB (bv_unsigned sp) (XM pkt dptr lptr) m m2).
    { eapply xpres_trans; [exact XP1|]. eapply (xpres_weaken H LB LB _ _ []); [exact XP2| lia| auto| intros a K; destruct K]. }
    clear MU1 WM1 MI1 ST1 HP1 AUX1 AC1 RFS1 ERR1 MF1 IM1 GM1 PK1 LP1 DP1 BS1 ACCP1 ACCD1 ACCL1 ACCC1 XP1 CH0 CH1 CF VIS1 KREL1 XP2 AP2.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply apm_seg2 with (oldlen := oldlen);
      [exact PK2| lia| exact DP2| exact LP2| exact AP| exact APD| exact APL| unfold bx in OFFD; clear - OFFD LO; lia| unfold bx in OFFL; clear - OFFL LO; lia
      | exact DNS| exact LNS| exact ACCP2| exact ACCD2| exact ACCL2| exact FR2| exact MI2| exact ALL| exact ALP]|].
    intros msF3 mo3 KREL3 MP3 (m3 & CASES & MU3 & WM3 & MI3 & PK3 & DP3 & LP3).
    assert (CW3 : forall LBx, (forall b, In b LB -> In b LBx) -> Forall (aclient_write_ok H LBx) [(dptr, dptr + 8); (lptr, lptr + 8)]).
    { intros LBx HLB. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      - eapply (ashobj_write_ok H); [exact CSP0|]. eapply (ashobj_mono H); [exact OBD| exact HLB].
      - eapply (ashobj_write_ok H); [exact CSP0|]. eapply (ashobj_mono H); [exact OBL| exact HLB]. }
    assert (AW3 : Forall aconst_ok [(dptr, dptr + 8); (lptr, lptr + 8)]).
    { apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      - eapply (ashobj_aconst_ok H HH); [exact HP| exact CSP0| exact OBD| lia| lia].
      - eapply (ashobj_aconst_ok H HH); [exact HP| exact CSP0| exact OBL| lia| lia]. }
    assert (FW3 : Forall (afs_write_ok H LF) [(dptr, dptr + 8); (lptr, lptr + 8)]) by (constructor; [exact AWD| constructor; [exact AWL| constructor]]).
    assert (NS3 : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(dptr, dptr + 8); (lptr, lptr + 8)]).
    { constructor; [exact DNS| constructor; [exact LNS| constructor]]. }
    apply (stk_transport_disjoint asegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| unfold bx in OFFD, OFFL; clear - OFFD OFFL LO SPR; cbn; lia].
    assert (ERR3 : rw_cells asegs m3 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR2| exact MU3| exact WM3| unfold ATP; cbn; lia]).
    apply (rw_cells_transport asegs _ m2 m3 _ _ FR2) in MU3 as FR3; [| exact WM3| unfold bx in OFFD, OFFL; clear - OFFD OFFL LO SPR; cbn; lia].
    assert (HP3 : as_RHEAP H s2' LB m3) by (eapply (ah_RHEAP_frame H HH); [exact HP2| exact MU3| exact WM3| apply CW3; intros bb Hbb; exact Hbb]).
    assert (AUX3 : as_rauxv_ok H m3 B) by (eapply (ah_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3| apply CW3; intros bb Hbb; exact Hbb]).
    assert (AC3 : ACONST m3) by (eapply ACONST_frame; [exact AC2| exact MU3| exact WM3| exact AW3]).
    assert (RFS3 : as_RFS H LF m3) by (eapply (ah_RFS_frame H HH); [exact RFS2| exact MU3| exact WM3| exact FW3]).
    assert (MF3 : MEMFLAG m3 v) by (eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]).
    assert (IM3 : IMPL_mem m3) by (eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]).
    assert (GM3 : GOT_mem m3) by (eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2]).
    assert (BS3 : bytes_at asegs m3 cur bs) by (unfold bx in ACD, ACL; eapply bytes_at_transport; [exact BS2| exact MU3| cbn; lia]).
    assert (ACCC3 : accessible m3 cur (Z.of_nat (length bs))) by (eapply accessible_across; [exact ACCC2| exact MU3| exact NS3]).
    assert (ACCD3 : accessible m3 dptr 8) by (eapply accessible_across; [exact ACCD2| exact MU3| exact NS3]).
    assert (ACCL3 : accessible m3 lptr 8) by (eapply accessible_across; [exact ACCL2| exact MU3| exact NS3]).
    assert (CH3 : as_chain H m3 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (achain_below H HH m2 m3 _ _ _ (bv_unsigned sp)); [exact CH2| intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]| exact MU3|].
      unfold bx in OFFD, OFFL.
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; cbn [fst snd]; intros fp' ra' [E|Hin];
        [injection E as <- <-; lia| exact (OCD _ _ Hin)| injection E as <- <-; lia| exact (OCL _ _ Hin)]. }
    assert (XP13 : xpres H LB (bv_unsigned sp) (XM pkt dptr lptr) m m3).
    { eapply xpres_trans; [exact XP12|]. eapply (xpres_of_munch H s LB _ _ _ m m2 m3); [exact HH| exact HP| exact MU3| exact WM3|].
      constructor; [right; intros a Ha; cbn in Ha |- *; lia|]. constructor; [right; intros a Ha; cbn in Ha |- *; lia| constructor]. }
    destruct CASES as [(L0 & a1x & VIS3)|(L1 & VIS3 & _)].
    - (* [comment removed for export] *)
      eapply (ah_done H HH). unfold pkmemdup_post. cbn [cfg_ms cfg_model]. unfold zlength.
      exists u0, u1, u2, a1x, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m3, errv, s2', LB, 0.
      split; [exact VIS3|]. split; [exact KREL3|].
      split; [eapply (ah_mpres_trans H HH); [| exact MP3]; eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|].
      split; [exact MI3|]. split; [exact AC3|].
      split. { unfold apm_frame in FR3. release_frame FR3 ST3 (bv_unsigned sp). exact ST3. }
      split. { rewrite unsigned_lit by (unfold ATP; lia). exact ERR3. }
      split; [exact AUX3|]. split; [exact HP3|]. split; [exact RFS3|].
      split; [exact PK3|]. split; [exact DP3|]. split; [rewrite L0; exact LP3|].
      split; [left; repeat split; [exact L0| lia]|].
      split; [exact XP13|]. split; [exists v; split; [exact MF3| apply Z.le_refl]|]. split; [exact IM3| exact GM3].
    - (* [comment removed for export] *)
      pose proof (acmemdup_spec H HH) as CM. unfold cmemdup_stmt in CM. unfold zlength in CM.
      eapply (ah_seq H HH).
      { eapply CM with (lo := lo) (B := B) (LB := LB) (s := s2') (v := v) (bs := bs) (D := cur) (bD := (pC, AC_, nC)) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
          [exact VIS3| reflexivity| reflexivity| ..]; rewrite ?unsigned_lit by lia.
        all: first [lazymatch goal with
             | |- bytes_at _ _ _ _ => exact BS3
             | |- In _ _ => exact HBIN
             | |- as_RHEAP _ _ _ _ => exact HP3
             | |- as_AKREL _ _ _ => exact KREL3
             | |- as_rauxv_ok _ _ _ => exact AUX3
             | |- stk _ _ _ _ => exact ST3
             | |- rw_cells _ _ _ [C4 _] => exact ERR3
             | |- mem_inv _ _ => exact MI3
             | |- _ = Z_to_bv 64 ATP => reflexivity
             | |- _ mod 16 = 0 => replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; rewrite Zminus_mod, SP16; reflexivity
             | |- ACONST _ => exact AC3
             | |- as_chain _ _ _ _ => exact CH3
             | |- forall fp' ra', In _ _ -> _ => exact CHS1
             | |- pf_ok _ _ _ _ => unfold APM_RA2; rewrite ?unsigned_lit by lia; eapply pf_ok_call; [exact PF|]; unfold PF_pkmemdup; intros x Hx; exact Hx
             | |- _ <= as_AL _ _ => lia
             | |- accessible _ _ _ => exact ACCC3
             | |- MEMFLAG _ _ => exact MF3
             | |- IMPL_mem _ => exact IM3
             | |- GOT_mem _ => exact GM3
             | |- _ => first [assumption | cbn [blk_addr blk_size fst snd]; lia | unfold CMEMDUP_STACK, CMALLOC_STACK, FR_CRYPTO_memdup, FR_CRYPTO_malloc, AMALLOC_STACK; lia
                              | match goal with |- ?G => idtac "LEFT:" G end]
             end | match goal with |- ?G => idtac "FAILED:" G end]. }
      intros [msF4 mo4] PO. unfold cmemdup_post in PO. cbn [cfg_ms cfg_model] in PO. unfold zlength in PO.
      destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m4 & errv4 & D & p & s4' &
                      VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & XP4 & BR & HP4 & BLK4 & ADDR4 & MF4 & IM4 & GM4 & AL4).
      rewrite (unsigned_lit (bv_unsigned sp + -80)) in ST4, XP4 by lia.
      pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5 & BR6 & BR7). unfold AIMG_TOP in BR4. clear BR6.
      pose proof (aapp_bounds D (Z.of_nat (length bs)) BR7 ltac:(clear - BB; lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
      assert (MFF : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) memflag_foot).
      { unfold memflag_foot, A_mem_inited. constructor; [cbn; unfold ALOWSH_LO; lia| constructor]. }
      eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4) in FR3; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]]. rename FR3 into FR4.
      eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4) in DP3; [| apply (ashobj_client_range H); exact OBD'| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]]. rename DP3 into DP4.
      eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4) in LP3; [| apply (ashobj_client_range H); exact OBL'| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]]. rename LP3 into LP4.
      eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4) in PK3; [| apply (ashobj_client_range H); exact OBP'| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]]. rename PK3 into PK4.
      assert (ACCD4 : accessible m4 dptr 8) by (eapply (ashobj_accessible_xpres H HH); [exact HP3| exact CSP| exact OBD'| exact ACCD3| exact XP4| exact MFF]).
      assert (ACCL4 : accessible m4 lptr 8) by (eapply (ashobj_accessible_xpres H HH); [exact HP3| exact CSP| exact OBL'| exact ACCL3| exact XP4| exact MFF]).
      assert (RFS4 : as_RFS H LF m4).
      { eapply (RFS_via_xpres H HH); [exact RFS3| exact XP4|]. unfold memflag_foot, A_mem_inited, ATLS_PRIV_LO, ATP. constructor; [cbn; lia| constructor]. }
      (* [comment removed for export] *)
      assert (E8 : 0 < 8) by lia. assert (LEN1 : 0 < Z.of_nat (length bs)) by lia.
      pose proof (afresh_apart H HH _ _ _ _ _ _ _ _ _ HP4 CSP (ashobj_client_range H _ _ _ _ OBD') E8 LEN1) as FD.
      pose proof (afresh_apart H HH _ _ _ _ _ _ _ _ _ HP4 CSP (ashobj_client_range H _ _ _ _ OBL') E8 LEN1) as FL.
      box FD; box FL.
      (* [comment removed for export] *)
      eapply (ahh_evt H HH); [exact KREL4| exact VIS4| eapply apm_seg3;
        [lia| lia| exact DP4| exact LP4| exact AP| unfold bx in OFFD; clear - OFFD LO; lia| unfold bx in OFFL; clear - OFFL LO; lia
        | exact DNS| exact LNS| exact ACCD4| exact ACCL4| exact FR4| exact MI4]|].
      intros msF5 mo5 KREL5 MP5 (a1y & m5 & VIS5 & MU5 & WM5 & MI5 & DP5 & LP5).
      apply (stk_transport_disjoint asegs _ m4 m5 _ _ ST4) in MU5 as ST5; [| exact WM5| unfold bx in OFFD, OFFL; clear - OFFD OFFL LO SPR; cbn; lia].
      apply (rw_cells_transport asegs _ m4 m5 _ _ FR4) in MU5 as FR5; [| exact WM5| unfold bx in OFFD, OFFL; clear - OFFD OFFL LO SPR; cbn; lia].
      unfold pkmemdup_post. cbn [cfg_ms cfg_model]. unfold zlength.
      exists v0, v1, v2, a1y, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, m5, errv4, s4', ((p, D, Z.of_nat (length bs)) :: LB), D.
      split; [exact VIS5|]. split; [exact KREL5|].
      split; [eapply (ah_mpres_trans H HH); [| exact MP5]; eapply (ah_mpres_trans H HH); [| exact MP4]; eapply (ah_mpres_trans H HH); [| exact MP3];
              eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|].
      split; [exact MI5|]. split; [eapply ACONST_frame; [exact AC4| exact MU5| exact WM5| exact AW3]|].
      split. { unfold apm_frame in FR5. release_frame FR5 ST5 (bv_unsigned sp). exact ST5. }
      split. { rewrite unsigned_lit by (unfold ATP; lia). eapply errno_across; [exact ERR4| exact MU5| exact WM5| unfold ATP; cbn; lia]. }
      split. { eapply (ah_rauxv_frame H HH) with (LB := LB); [exact AUX4| exact MU5| exact WM5| apply CW3; intros b Hb; exact Hb]. }
      split. { eapply (ah_RHEAP_frame H HH); [exact HP4| exact MU5| exact WM5| apply CW3; intros b Hb; apply in_cons; exact Hb]. }
      split. { eapply (ah_RFS_frame H HH); [exact RFS4| exact MU5| exact WM5| exact FW3]. }
      split. { unfold bx in APD, APL. eapply rw_cells_transport; [exact PK4| exact MU5| exact WM5| cbn; lia]. }
      split; [exact DP5|]. split; [destruct (Z.eqb_spec (Z.of_nat (length bs)) 0); [lia| exact LP5]|].
      split.
      { right. split; [lia|]. exists p. split; [exact BR|]. split; [reflexivity|].
        split. { unfold bx, zlength in FD, FL. eapply rw_cells_transport; [exact BLK4| exact MU5| exact WM5| clear - FD FL; cbn; lia]. }
        split. { eapply addressable_transport; [exact ADDR4| exact MU5| exact WM5|].
                 pose proof (sh_aapp_range D (Z.of_nat (length bs)) BR7 ltac:(clear - BB; lia)) as (S1 & S2 & S3). unfold AHI_LO in S3.
                 assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in S1.
                 unfold bx, ALOWSH_LO, AHI_LO in DNS, LNS. clear - S1 S2 S3 DNS LNS. cbn. lia. }
        lia. }
      split.
      { eapply xpres_trans; [exact XP13|]. eapply xpres_trans.
        - eapply (xpres_weaken H LB LB _ _ memflag_foot); [exact XP4| lia| auto| intros a K; unfold XM; apply (proj2 (rin_ivs_app _ _ a)); right; exact K].
        - eapply (xpres_of_munch_fresh H HH); [exact HP4| exact CSP0| exact MU5| exact WM5|].
          constructor; [right; right; intros a Ha; cbn in Ha |- *; lia|]. constructor; [right; right; intros a Ha; cbn in Ha |- *; lia| constructor]. }
      split; [exists 1; split; [eapply MEMFLAG_across; [exact MU5| exact WM5| unfold A_mem_inited; cbn; lia| exact MF4]| clear - V01; lia]|].
      split; [eapply IMPL_across; [exact MU5| exact WM5| unfold A_malloc_impl; cbn; lia| exact IM4]|].
      eapply GOT_across; [exact MU5| exact WM5| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM4].
  Qed.

  (* [comment removed for export] *)
  Local Definition XS (pkt dptr : Z) : list (Z * Z) := [(pkt, pkt + 24); (dptr, dptr + 8)] ++ memflag_foot.

  Lemma apkstrndup_spec : pkstrndup_stmt H.
  Proof.
    unfold pkstrndup_stmt. intros until CH.
    intros VIS A0 A1 PK OBP PKB HC DP OBD APD ACD ACP BS HBIN HBLO HBHI HL ALP ALD
           RFS AWD ACCP ACCD ACCC HP KREL BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL MF IM GM.
    unfold PKSTRNDUP_STACK, FR_PACKET_strndup, CSTRNDUP_STACK, CFREE_STACK, CMALLOC_STACK, FR_CRYPTO_strndup, FR_CRYPTO_malloc, AMALLOC_STACK, AFREE_STACK in LO.
    acb. subst a0 a1 tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (CSP0 : aceil <= bv_unsigned sp) by lia. assert (CSP : aceil <= bv_unsigned sp + -48) by lia.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    unfold apart in APD, ACD, ACP. box APD; box ACD; box ACP.
    pose proof (rw_cells_bound _ _ _ _ PK) as PB. unfold pk_cells in PB. cbn [cells_size csize Nat.add] in PB.
    pose proof (rw_cells_bound _ _ _ _ DP) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (proj1 (ah_costs H HH) (Z.of_nat (length bs) + 1) ltac:(lia)) as CM0.
    pose proof (strnlen_le bs) as SNL.
    pose proof (ashobj_bounds H HH _ _ _ _ _ _ HP CSP0 OBP ltac:(lia)) as [PT PNS].
    pose proof (ashobj_bounds H HH _ _ _ _ _ _ HP CSP0 OBD ltac:(lia)) as [DT DNS].
    pose proof (ashobj_off_frame H HH _ _ _ _ _ _ lo HP OBP CEIL) as OFFP.
    pose proof (ashobj_off_frame H HH _ _ _ _ _ _ lo HP OBD CEIL) as OFFD.
    pose proof (ashobj_lowerSP H _ _ (bv_unsigned sp + -48) _ _ OBP ltac:(lia)) as OBP'.
    pose proof (ashobj_lowerSP H _ _ (bv_unsigned sp + -48) _ _ OBD ltac:(lia)) as OBD'.
    destruct bC as [[pC AC_] nC]. cbn [blk_addr blk_size fst snd] in HBLO, HBHI.
    pose proof (ah_blocks H HH _ _ _ _ HP HBIN) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4, K5, K6, K7. unfold AIMG_TOP in K4.
    assert (OBC' : ashobj H LB (bv_unsigned sp + -48) cur (Z.of_nat (length bs))).
    { left. exists (pC, AC_, nC). split; [exact HBIN| cbn; lia]. }
    pose proof (ACONST_shbase m AC) as [GSB SHB0].
    unfold AIMG_TOP in PT, DT. clear PNS K6.
    box OFFP; box OFFD; box DNS.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply aps_seg1 with (lo := lo); [exact DP| exact OFFD| exact ACCD| exact ALD| exact GSB| exact SHB0| exact ST| exact CEIL| clear - LO; lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -48, bv_unsigned sp)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]. }
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). unfold AIMG_TOP in F1.
    assert (FW : Forall (afs_write_ok H LF) [(bv_unsigned sp + -48, bv_unsigned sp)]).
    { constructor; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *; lia| constructor]. }
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(bv_unsigned sp + -48, bv_unsigned sp)]).
    { constructor; [cbn; unfold AHI_LO in *; lia| constructor]. }
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]).
    assert (RFS1 : as_RFS H LF m1) by (eapply (ah_RFS_frame H HH); [exact RFS| exact MU1| exact WM1| exact FW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (MF1 : MEMFLAG m1 v) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (PK1 : rw_cells asegs m1 pkt (pk_cells cur ms (Z.of_nat (length bs)))) by (unfold bx in OFFP; eapply rw_cells_transport; [exact PK| exact MU1| exact WM1| cbn; lia]).
    assert (DP1 : rw_cells asegs m1 dptr [C8 (wz 0)]) by (unfold bx in OFFD; eapply rw_cells_transport; [exact DP| exact MU1| exact WM1| cbn; lia]).
    assert (BS1 : bytes_at asegs m1 cur bs) by (eapply bytes_at_transport; [exact BS| exact MU1| cbn; lia]).
    assert (ACCP1 : accessible m1 pkt 24) by (eapply accessible_across; [exact ACCP| exact MU1| exact NSW]).
    assert (ACCD1 : accessible m1 dptr 8) by (eapply accessible_across; [exact ACCD| exact MU1| exact NSW]).
    assert (ACCC1 : accessible m1 cur (Z.of_nat (length bs))) by (eapply accessible_across; [exact ACCC| exact MU1| exact NSW]).
    assert (XP1 : xpres H LB (bv_unsigned sp) (XS pkt dptr) m m1).
    { eapply (xpres_of_munch H s LB _ _ _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    clear CW AW FW NSW.
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. constructor; [left; cbn; lia| constructor]. }
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SP16| lia| lia|].
      pose proof FR1 as FR2. unfold aps_frame in FR2.
      change ([C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -48 + 32) by lia.
      rewrite Z_to_bv_bv_unsigned || idtac. exact FR2 || (revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2). }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -48 + 16 <= fp').
    { intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]. }
    (* [comment removed for export] *)
    pose proof (acfree_null_spec H HH) as CF. unfold cfree_null_stmt in CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB) (s := s) (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS1| ..]; rewrite ?unsigned_lit by lia.
      all: lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- as_rauxv_ok _ _ _ => exact AUX1
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => exact ERR1
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SP16; reflexivity
           | |- ACONST _ => exact AC1
           | |- as_chain _ _ _ _ => exact CH1
           | |- forall fp' ra', In _ _ -> _ => exact CHS1
           | |- _ <= as_AL _ _ => lia
           | |- IMPL_mem _ => exact IM1
           | |- GOT_mem _ => exact GM1
           | |- _ => first [assumption | lia | unfold CFREE_STACK, AFREE_STACK; lia | match goal with |- ?G => idtac "LEFT:" G end]
           end. }
    intros [msF2 mo2] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s2' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & HP2 & IM2 & GM2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, XP2 by lia.
    pose proof (xpres_nil_apres H _ _ _ _ XP2) as AP2.
    eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| constructor]. rename FR1 into FR2.
    assert (PK2 : rw_cells asegs m2 pkt (pk_cells cur ms (Z.of_nat (length bs)))).
    { eapply (apres_rw_cells H); [exact AP2| exact PK1| apply (ashobj_client_range H); exact OBP']. }
    assert (DP2 : rw_cells asegs m2 dptr [C8 (wz 0)]) by (eapply (apres_rw_cells H); [exact AP2| exact DP1| apply (ashobj_client_range H); exact OBD']).
    assert (BS2 : bytes_at asegs m2 cur bs) by (eapply (xpres_bytes_at' H); [exact XP2| exact BS1| apply (ashobj_client_range H); exact OBC'| constructor]).
    assert (ACCP2 : accessible m2 pkt 24) by (eapply (ashobj_accessible_xpres H HH); [exact HP1| exact CSP| exact OBP'| exact ACCP1| exact XP2| constructor]).
    assert (ACCD2 : accessible m2 dptr 8) by (eapply (ashobj_accessible_xpres H HH); [exact HP1| exact CSP| exact OBD'| exact ACCD1| exact XP2| constructor]).
    assert (ACCC2 : accessible m2 cur (Z.of_nat (length bs))) by (eapply (ashobj_accessible_xpres H HH); [exact HP1| exact CSP| exact OBC'| exact ACCC1| exact XP2| constructor]).
    assert (RFS2 : as_RFS H LF m2) by (eapply (RFS_via_apres H HH); [exact RFS1| exact AP2]).
    assert (MF2 : MEMFLAG m2 v) by (eapply (MEMFLAG_apres H); [exact AP2| exact MF1]).
    assert (CH2 : as_chain H m2 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (chain_via_apres H HH); [exact CH1| exact AP2| exact CHS1]. }
    assert (XP12 : xpres H LB (bv_unsigned sp) (XS pkt dptr) m m2).
    { eapply xpres_trans; [exact XP1|]. eapply (xpres_weaken H LB LB _ _ []); [exact XP2| lia| auto| intros a K; destruct K]. }
    clear MU1 WM1 MI1 ST1 HP1 AUX1 AC1 RFS1 ERR1 MF1 IM1 GM1 PK1 DP1 BS1 ACCP1 ACCD1 ACCC1 XP1 CH0 CH1 CF VIS1 KREL1 XP2 AP2.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply aps_seg2; [exact PK2| exact ACCP2| exact MI2| exact ALP]|].
    intros msF3 mo3 KREL3 MP3 VIS3.
    (* [comment removed for export] *)
    pose proof (acstrndup_spec H HH) as CS. unfold cstrndup_stmt in CS. unfold zlength in CS.
    eapply (ah_seq H HH).
    { eapply CS with (lo := lo) (B := B) (LB := LB) (s := s2') (v := v) (bs := bs) (S := cur) (bS := (pC, AC_, nC)) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS3| reflexivity| exact HC| reflexivity| ..]; rewrite ?unsigned_lit by lia.
      all: first [lazymatch goal with
           | |- bytes_at _ _ _ _ => exact BS2
           | |- In _ _ => exact HBIN
           | |- as_RHEAP _ _ _ _ => exact HP2
           | |- as_AKREL _ _ _ => exact KREL3
           | |- as_rauxv_ok _ _ _ => exact AUX2
           | |- stk _ _ _ _ => exact ST2
           | |- rw_cells _ _ _ [C4 _] => exact ERR2
           | |- mem_inv _ _ => exact MI2
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SP16; reflexivity
           | |- ACONST _ => exact AC2
           | |- as_chain _ _ _ _ => exact CH2
           | |- forall fp' ra', In _ _ -> _ => exact CHS1
           | |- pf_ok _ _ _ _ => unfold APS_RA2; rewrite ?unsigned_lit by lia; eapply pf_ok_call; [exact PF|]; unfold PF_pkstrndup; intros x Hx; exact Hx
           | |- _ <= as_AL _ _ => lia
           | |- accessible _ _ _ => exact ACCC2
           | |- MEMFLAG _ _ => exact MF2
           | |- IMPL_mem _ => exact IM2
           | |- GOT_mem _ => exact GM2
           | |- _ => first [assumption | cbn [blk_addr blk_size fst snd]; lia | unfold CSTRNDUP_STACK, CMALLOC_STACK, FR_CRYPTO_strndup, FR_CRYPTO_malloc, AMALLOC_STACK; lia
                            | match goal with |- ?G => idtac "LEFT:" G end]
           end | match goal with |- ?G => idtac "FAILED:" G end]. }
    intros [msF4 mo4] PO. unfold cstrndup_post in PO. cbn [cfg_ms cfg_model] in PO. unfold zlength in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m4 & errv4 & D & p & s4' &
                    VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & XP4 & BR & HP4 & BLK4 & ADDR4 & MF4 & IM4 & GM4 & AL4).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST4, XP4 by lia.
    set (k := strnlen bs) in *.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5 & BR6 & BR7). unfold AIMG_TOP in BR4. clear BR6.
    assert (HK : 0 <= Z.of_nat k + 1) by lia.
    pose proof (aapp_bounds D (Z.of_nat k + 1) BR7 HK) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    assert (MFF : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) memflag_foot).
    { unfold memflag_foot, A_mem_inited. constructor; [cbn; unfold ALOWSH_LO; lia| constructor]. }
    eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4) in FR2; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]]. rename FR2 into FR4.
    eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4) in DP2; [| apply (ashobj_client_range H); exact OBD'| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]]. rename DP2 into DP4.
    eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4) in PK2; [| apply (ashobj_client_range H); exact OBP'| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]]. rename PK2 into PK4.
    assert (ACCD4 : accessible m4 dptr 8) by (eapply (ashobj_accessible_xpres H HH); [exact HP2| exact CSP| exact OBD'| exact ACCD2| exact XP4| exact MFF]).
    assert (RFS4 : as_RFS H LF m4).
    { eapply (RFS_via_xpres H HH); [exact RFS2| exact XP4|]. unfold memflag_foot, A_mem_inited, ATLS_PRIV_LO, ATP. constructor; [cbn; lia| constructor]. }
    assert (E8 : 0 < 8) by lia. assert (LEN1 : 0 < Z.of_nat k + 1) by lia.
    pose proof (afresh_apart H HH _ _ _ _ _ _ _ _ _ HP4 CSP (ashobj_client_range H _ _ _ _ OBD') E8 LEN1) as FD. box FD.
    assert (AWD1 : Forall (aclient_write_ok H ((p, D, Z.of_nat k + 1) :: LB)) [(dptr, dptr + 8)]).
    { apply Forall_cons; [| apply Forall_nil]. eapply (ashobj_write_ok H); [exact CSP0|]. eapply (ashobj_mono H); [exact OBD| intros b Hb; apply in_cons; exact Hb]. }
    assert (AWD0 : Forall (aclient_write_ok H LB) [(dptr, dptr + 8)]).
    { apply Forall_cons; [| apply Forall_nil]. eapply (ashobj_write_ok H); [exact CSP0| exact OBD]. }
    assert (ACD1 : Forall aconst_ok [(dptr, dptr + 8)]).
    { apply Forall_cons; [| apply Forall_nil]. eapply (ashobj_aconst_ok H HH); [exact HP| exact CSP0| exact OBD| lia| lia]. }
    (* [comment removed for export] *)
    eapply (ahh_evt H HH); [exact KREL4| exact VIS4| eapply aps_seg3;
      [clear - AB3 AB4 HK; lia| exact DP4| unfold bx in OFFD; clear - OFFD LO; lia| exact ACCD4| exact FR4| exact MI4]|].
    intros msF5 mo5 KREL5 MP5 (m5 & VIS5 & MU5 & WM5 & MI5 & DP5).
    apply (stk_transport_disjoint asegs _ m4 m5 _ _ ST4) in MU5 as ST5; [| exact WM5| unfold bx in OFFD; clear - OFFD LO SPR; cbn; lia].
    apply (rw_cells_transport asegs _ m4 m5 _ _ FR4) in MU5 as FR5; [| exact WM5| unfold bx in OFFD; clear - OFFD LO SPR; cbn; lia].
    unfold pkstrndup_post. cbn [cfg_ms cfg_model]. unfold zlength. fold k.
    exists v0, v1, v2, (Z_to_bv 64 1), d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, m5, errv4, s4', D, p.
    split; [exact VIS5|]. split; [exact KREL5|].
    split; [eapply (ah_mpres_trans H HH); [| exact MP5]; eapply (ah_mpres_trans H HH); [| exact MP4]; eapply (ah_mpres_trans H HH); [| exact MP3];
            eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|].
    split; [exact MI5|]. split; [eapply ACONST_frame; [exact AC4| exact MU5| exact WM5| exact ACD1]|].
    split. { unfold aps_frame in FR5. release_frame FR5 ST5 (bv_unsigned sp). exact ST5. }
    split. { rewrite unsigned_lit by (unfold ATP; lia). eapply errno_across; [exact ERR4| exact MU5| exact WM5| unfold ATP; cbn; lia]. }
    split. { eapply (ah_rauxv_frame H HH) with (LB := LB); [exact AUX4| exact MU5| exact WM5| exact AWD0]. }
    split; [exact BR|].
    split. { eapply (ah_RHEAP_frame H HH); [exact HP4| exact MU5| exact WM5| exact AWD1]. }
    split. { eapply (ah_RFS_frame H HH); [exact RFS4| exact MU5| exact WM5|]. apply Forall_cons; [exact AWD| apply Forall_nil]. }
    split. { unfold bx in FD. eapply rw_cells_transport; [exact BLK4| exact MU5| exact WM5| clear - FD SNL; cbn; rewrite ?firstn_length_le by lia; lia]. }
    split. { eapply addressable_transport; [exact ADDR4| exact MU5| exact WM5|].
             pose proof (sh_aapp_range D (Z.of_nat k + 1) BR7 HK) as (S1 & S2 & S3). unfold AHI_LO in S3.
             assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in S1.
             unfold bx, ALOWSH_LO, AHI_LO in DNS. clear - S1 S2 S3 DNS. cbn. lia. }
    split. { unfold bx in APD. eapply rw_cells_transport; [exact PK4| exact MU5| exact WM5| clear - APD; cbn; lia]. }
    split; [exact DP5|].
    split.
    { eapply xpres_trans; [exact XP12|]. eapply xpres_trans.
      - eapply (xpres_weaken H LB LB _ _ memflag_foot); [exact XP4| lia| auto| intros a K; unfold XS; apply (proj2 (rin_ivs_app _ _ a)); right; exact K].
      - eapply (xpres_of_munch_fresh H HH); [exact HP4| exact CSP0| exact MU5| exact WM5|].
        apply Forall_cons; [right; right; intros a Ha; cbn in Ha |- *; lia| apply Forall_nil]. }
    split; [eapply MEMFLAG_across; [exact MU5| exact WM5| unfold A_mem_inited; cbn; lia| exact MF4]|].
    split; [eapply IMPL_across; [exact MU5| exact WM5| unfold A_malloc_impl; cbn; lia| exact IM4]|].
    split; [eapply GOT_across; [exact MU5| exact WM5| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM4]|].
    lia.
  Qed.

  Lemma AC10_spec : C10_stmts H.
  Proof. split; [exact apkmemdup_spec| exact apkstrndup_spec]. Qed.
End W.

