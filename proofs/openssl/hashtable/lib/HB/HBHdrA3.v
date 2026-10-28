(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOfAps CxReblob HBPlanImage HBAtable HBCheck0 HBCheck1 HBCheck2 HBCheck3 HBArg HBChain HBUsageDefs HBOpenDefs HBHdrDefs
  BC3A3Lit BC4e BC6 BC4A3Lit BFEEndOA3 HBOpenA3 BC6A3Lit BC66aA3Cert BC66bA3Cert BC67aA3Cert BC67bA3Cert BFEEndHA3 BXu BXHA3Cert.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Lemma c66aa3_shape_eq : c66aa3_shape = hdr_shape1 short_lit. Proof. reflexivity. Qed.
Lemma c66ba3_shape_eq : c66ba3_shape = hdr_shape1 short_lit. Proof. reflexivity. Qed.
Lemma c67aa3_shape_eq : c67aa3_shape = hdr_shape1 overrun_lit. Proof. reflexivity. Qed.
Lemma c67ba3_shape_eq : c67ba3_shape = hdr_shape1 overrun_lit. Proof. reflexivity. Qed.

Section HdrA3.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Let c := content_of argv fs.
  Let argv1 := nth 1 argv [].
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation PIECE := (piece SV argH ISP fs).
  #[local] Notation FXHOLE := (fx_hole SV argH ISP fs).
  Let SVF := SINVm_frame HAPH sp rdraw brk0 argv envp uid hw c.
  Let SVA := SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c.
  Let SV1 := SVm_to1 sp rdraw brk0 argv envp uid hw c.
  #[local] Notation CHK1 := (ha1_check_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV1 SVF SVA).

  (* [comment removed for export] *)
  Hypothesis H_FEO : FXHOLE c4a3_hs21 feendoa3.
  Hypothesis H_FEH : FXHOLE c6a3_hs24 feendha3.
  (* [comment removed for export] *)
  Hypothesis Hne : argv1 <> [].
  Hypothesis Hsl : path_has_slash argv1 = false.
  Hypothesis Hdr : path_is_dirref argv1 = false.
  Hypothesis Hln : (length argv1 <= 4095)%nat.
  Hypothesis Hlk : fs_lookup fs argv1 = Some c.

  Lemma xh_piece_a3 : PIECE feendha3 T_exit2.
  Proof.
    intros E R FULL m HC.
    exact (CHK1 (fun _ : nat => @None acs) (fun _ _ _ => t_nil) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl)
             (fun h ch Hh => ltac:(discriminate Hh)) xha3_IT xha3_IT_ok 0%nat true 3000%nat 400000%nat xu_plan feendha3 xha3_shape xha3_cert E R FULL m HC).
  Qed.
  Lemma feh_piece_a3 : PIECE c6a3_hs24 T_exit2.
  Proof. apply (hole_compose SV argH ISP fs c6a3_hs24 feendha3 T_exit2); [vm_compute; lia | intros E E' fs0 _; reflexivity | exact H_FEH | exact xh_piece_a3]. Qed.

  Lemma c6_holes_a3 : holes_stmt HASEGS HAT LIM C6A3_HS SV argH ISP HOLES6 fs.
  Proof.
    intros h ch Hh E R FULL m HC. unfold C6A3_HS, C6A3_HS0 in Hh. unfold HOLES6.
    destruct (Nat.eqb h 21) eqn:H21.
    { apply Nat.eqb_eq in H21; subst h. diet_injection Hh. cbn [orb]. exact (feo_piece_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO E R FULL m HC). }
    destruct (Nat.eqb h 24) eqn:H24; [|discriminate Hh].
    apply Nat.eqb_eq in H24; subst h. diet_injection Hh. cbn [orb]. exact (feh_piece_a3 E R FULL m HC).
  Qed.

  (* [comment removed for export] *)
  Section Class.
    Variable T : ION.iotab. Variables lo hi : Z. Variable lit : list Z.
    Hypothesis HO : ION.io_open T = ION.OFile lo hi. Hypothesis HB : ION.io_blob T = JB. Hypothesis HF : lo <= flen c <= hi. Hypothesis HH : ION.hdr_ok T c.
    Variable IT : itab. Hypothesis IT_ok : itab_sound HASEGS IT. Variable s : shape.
    Hypothesis Hcert : CAP.check HASEGS IT HAT NX0 AsanInit.LIMIT (ha3_XN T) ha3_XE (ha3_XB T) C6A3_HS 0 true false true 400000 3000 None c3a3_hs98 c6_top0 = COk s.
    Hypothesis Hshape : s = hdr_shape1 lit.
    Lemma class_piece_a3 : PIECE c3a3_hs98 (fun _ fs' => T_hdr lit argv1 fs').
    Proof.
      intros E R FULL m HC.
      assert (HCL : match ION.io_open T with
        | ION.ONone => True
        | ION.OTooLong => (4096 <= length argv1)%nat
        | ION.ONoEnt => argv1 = [] \/ (path_has_slash argv1 = false /\ path_is_dirref argv1 = false /\ (length argv1 <= 4095)%nat /\ fs_lookup fs argv1 = None)
        | ION.ODir => path_is_dirref argv1 = true /\ (length argv1 <= 4095)%nat
        | ION.OFile lo0 hi0 => exists c0, argv1 <> [] /\ path_has_slash argv1 = false /\ path_is_dirref argv1 = false /\ (length argv1 <= 4095)%nat /\ fs_lookup fs argv1 = Some c0
                     /\ lo0 <= flen c0 <= hi0
                     /\ (forall E0 M0, SV E0 M0 -> forall j, 65536 * Z.of_nat j < 2 ^ 26 -> eb E0 (ION.io_blob T + j)%nat = chunk j c0)
                     /\ ION.hdr_ok T c0
        end).
      { rewrite HO. exists c. split; [exact Hne|]. split; [exact Hsl|]. split; [exact Hdr|]. split; [exact Hln|]. split; [exact Hlk|]. split; [exact HF|]. split; [|exact HH].
        intros E0 M0 HS j _. rewrite HB, CxOfAps.chunk_eq. exact (proj2 (proj2 (proj2 HS)) j). }
      pose proof (ha3_check_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV1 SVF SVA T HCL
                    C6A3_HS HOLES6 HOLES6_agree HOLES6_nil HOLES6_mod c6_holes_a3 IT IT_ok 0%nat true 3000%nat 400000%nat
                    c6_top0 c3a3_hs98 s Hcert E R FULL m HC) as RZ.
      rewrite Hshape in RZ. eapply crz_conseq; [exact RZ|].
      destruct (vals1_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as [U7 B2].
      exact (hdr_eval1 E (m_fs m) argv1 lit U7 B2).
    Qed.
  End Class.

  Lemma flen_nonneg : 0 <= flen c. Proof. unfold flen. lia. Qed.
  Lemma hdr_ok_simple : forall o, ION.hdr_ok (ION.iot_simple o 32) c. Proof. intros o. unfold ION.hdr_ok. cbn. tauto. Qed.

  Theorem hdr_short_a3 : flen c <= 5 -> PIECE c3a3_hs98 (fun _ fs' => T_hdr short_lit argv1 fs').
  Proof.
    intros H5. pose proof flen_nonneg as H0. destruct (Z.eq_dec (flen c) 0) as [Hz|Hnz].
    - exact (class_piece_a3 (ION.iot_simple (ION.OFile 0 0) 32) 0 0 short_lit eq_refl eq_refl ltac:(lia) (hdr_ok_simple _) c66aa3_IT c66aa3_IT_ok c66aa3_shape c66aa3_cert c66aa3_shape_eq).
    - exact (class_piece_a3 (ION.iot_simple (ION.OFile 1 5) 32) 1 5 short_lit eq_refl eq_refl ltac:(lia) (hdr_ok_simple _) c66ba3_IT c66ba3_IT_ok c66ba3_shape c66ba3_cert c66ba3_shape_eq).
  Qed.

  Lemma hdr_ok_overrun : forall o, 6 <= flen c -> ION.room c < 0 -> ION.hdr_ok (ION.IOT o 32 (Some (0, 32767)) (Some (-32767, -1)) None None) c.
  Proof.
    intros o H6 Hr. unfold ION.hdr_ok, ION.in_opt. cbn [ION.io_cfg ION.io_room ION.io_cmod ION.io_b1s].
    assert (HC : 0 <= ION.cfglen c <= 32767) by (unfold ION.cfglen; pose proof (Z.mod_pos_bound (ION.hbyte 0 c + 256 * ION.hbyte 1 c) 32768 ltac:(lia)); lia).
    unfold ION.room, ION.flenZ in *. unfold flen in H6. repeat split; lia.
  Qed.
  Theorem hdr_overrun_a3 : 6 <= flen c -> ION.room c < 0 -> PIECE c3a3_hs98 (fun _ fs' => T_hdr overrun_lit argv1 fs').
  Proof.
    intros H6 Hr.
    assert (HC : 0 <= ION.cfglen c <= 32767) by (unfold ION.cfglen; pose proof (Z.mod_pos_bound (ION.hbyte 0 c + 256 * ION.hbyte 1 c) 32768 ltac:(lia)); lia).
    assert (H7 : flen c <= 32772) by (unfold ION.room, ION.flenZ in Hr; unfold flen; lia).
    destruct (Z_le_gt_dec (flen c) 64) as [H64|H65].
    - exact (class_piece_a3 (ION.IOT (ION.OFile 6 64) 32 (Some (0, 32767)) (Some (-32767, -1)) None None) 6 64 overrun_lit eq_refl eq_refl ltac:(lia) (hdr_ok_overrun _ H6 Hr)
               c67aa3_IT c67aa3_IT_ok c67aa3_shape c67aa3_cert c67aa3_shape_eq).
    - exact (class_piece_a3 (ION.IOT (ION.OFile 65 32772) 32 (Some (0, 32767)) (Some (-32767, -1)) None None) 65 32772 overrun_lit eq_refl eq_refl ltac:(lia) (hdr_ok_overrun _ H6 Hr)
               c67ba3_IT c67ba3_IT_ok c67ba3_shape c67ba3_cert c67ba3_shape_eq).
  Qed.
End HdrA3.
