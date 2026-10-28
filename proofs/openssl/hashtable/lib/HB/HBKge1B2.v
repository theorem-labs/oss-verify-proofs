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
  BC3B2Lit BC3B2LitK BC4e BC4B2Lit BFEEndOB2 HBOpenB2 BC7 BC7B2Lit BC7B2Cert BKInv BKPa BKPB2Inv BKPB2Lit BKPB2Cert BKW1a BKW1B2Inv BKW1B2Lit BKW1B2Cert BKW2a BKW2B2Inv BKW2B2Lit BKW2B2Cert BKW3a BKW3B2Inv BKW3B2Lit BKW3B2Cert BKW4a BKW4B2Inv BKW4B2Lit BKW4B2Cert BKW5a BKW5B2Inv BKW5B2Lit BKW5B2Cert BKW6a BKW6B2Inv BKW6B2Lit BKW6B2Cert BKW7a BKW7B2Inv BKW7B2Lit BKW7B2Cert BKW8a BKW8B2Inv BKW8B2Lit BKW8B2Cert BKW9a BKW9B2Inv BKW9B2Lit BKW9B2Cert BKE1a BKE1B2Inv BKE1B2Lit BKE1B2Cert BKE2a BKE2B2Inv BKE2B2Lit BKE2B2Cert BKE3a BKE3B2Inv BKE3B2Lit BKE3B2Cert BKE4a BKE4B2Inv BKE4B2Lit BKE4B2Cert BKE5a BKE5B2Inv BKE5B2Lit BKE5B2Cert BKE6a BKE6B2Inv BKE6B2Lit BKE6B2Cert BKE7a BKE7B2Inv BKE7B2Lit BKE7B2Cert BKE8a BKE8B2Inv BKE8B2Lit BKE8B2Cert BKE9a BKE9B2Inv BKE9B2Lit BKE9B2Cert BKE10a BKE10B2Inv BKE10B2Lit BKE10B2Cert BKC1B2Inv BKC1B2Lit BKC1B2Cert BKC2B2Inv BKC2B2Lit BKC2B2Cert BKC3B2Inv BKC3B2Lit BKC3B2Cert BKC4B2Inv BKC4B2Lit BKC4B2Cert BKC5B2Inv BKC5B2Lit BKC5B2Cert BKC6B2Inv BKC6B2Lit BKC6B2Cert BKC7B2Inv BKC7B2Lit BKC7B2Cert BKC8B2Inv BKC8B2Lit BKC8B2Cert BKC9B2Inv BKC9B2Lit BKC9B2Cert BKC10B2Inv BKC10B2Lit BKC10B2Cert BKRa BKRB2Inv BKRB2Lit BKRB2Cert BFEEndRB2 BXu BXRB2Cert.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Lemma kpb2_shape_eq : kpb2_shape = SAlt2 noent_shape (SHole 101). Proof. reflexivity. Qed.
Lemma c7b2_shape_eq : c7b2_shape = SAlt2 noent_shape (SHole 25). Proof. reflexivity. Qed.
Definition refused_lit : list Z := [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 54; 55; 49; 48; 56; 56; 54; 52; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10].
Lemma krb2_shape_eq : krb2_shape = SEmitP 2 [SPLit refused_lit] (SHole 230). Proof. reflexivity. Qed.

Section Kge1B2.
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
  Hypothesis H_FEO : FXHOLE c4b2_hs21 feendob2.
  (* [comment removed for export] *)
  Hypothesis Hne : argv1 <> [].
  Hypothesis Hsl : path_has_slash argv1 = false.
  Hypothesis Hdr : path_is_dirref argv1 = false.
  Hypothesis Hln : (length argv1 <= 4095)%nat.
  Hypothesis Hlk : fs_lookup fs argv1 = Some c.

  (* [comment removed for export] *)
  Section Step.
    Variable TT : env -> Fs.Fs -> TSet.
    Hypothesis TT_agree : t_agree TT.
    Hypothesis TT_nil : forall E fs0, TT E fs0 [].
    Variable hN : nat.
    Hypothesis HhN : (hN < 1000)%nat.
    Definition HOLESK (h : nat) (E : env) (fs' : Fs.Fs) : TSet :=
      if Nat.eqb (CAP.hole_cls h) 21 then T_exit2 E fs' else if Nat.eqb (CAP.hole_cls h) hN then TT E fs' else t_nil.
    Lemma HOLESK_mod : forall h E fs0, HOLESK h E fs0 = HOLESK (CAP.hole_cls h) E fs0.
    Proof. intros h E fs0. unfold HOLESK, CAP.hole_cls. rewrite Nat.Div0.mod_mod. reflexivity. Qed.
    Lemma HOLESK_agree : forall h E E' fs0, env_agree NX0 E E' -> HOLESK h E fs0 = HOLESK h E' fs0.
    Proof. intros h E E' fs0 Ha. unfold HOLESK. destruct (Nat.eqb (CAP.hole_cls h) 21); [reflexivity|]. destruct (Nat.eqb (CAP.hole_cls h) hN); [exact (TT_agree E E' fs0 Ha) | reflexivity]. Qed.
    Lemma HOLESK_nil : forall h E fs0, HOLESK h E fs0 [].
    Proof. intros h E fs0. unfold HOLESK. destruct (Nat.eqb (CAP.hole_cls h) 21); [apply CXS.t_exit_has_nil|]. destruct (Nat.eqb (CAP.hole_cls h) hN); [apply TT_nil | reflexivity]. Qed.
    Lemma HOLESK_hN : hN <> 21%nat -> forall E fs0, HOLESK hN E fs0 = TT E fs0.
    Proof.
      intros Hn E fs0. unfold HOLESK, CAP.hole_cls. rewrite (Nat.mod_small hN 1000 HhN).
      destruct (Nat.eqb hN 21) eqn:H21; [apply Nat.eqb_eq in H21; contradiction|]. rewrite Nat.eqb_refl. reflexivity.
    Qed.

    Variable T : ION.iotab. Variables lo hi : Z.
    Hypothesis HO : ION.io_open T = ION.OFile lo hi. Hypothesis HB : ION.io_blob T = JB. Hypothesis HF : lo <= flen c <= hi. Hypothesis HH : ION.hdr_ok T c.
    Variable HS : nat -> option acs. Variable NEXT : acs.
    Hypothesis HHS : forall h ch, HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = hN /\ hN <> 21%nat /\ ch = NEXT).
    Hypothesis Hnext : PIECE NEXT TT.
    Lemma stepk_holes : holes_stmt HASEGS HAT LIM HS SV argH ISP HOLESK fs.
    Proof.
      intros h ch Hh E R FULL m HC. destruct (HHS h ch Hh) as [[-> ->] | (-> & Hn & ->)].
      - change (HOLESK 21 E (m_fs m)) with (T_exit2 E (m_fs m)). exact (feo_piece_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO E R FULL m HC).
      - rewrite (HOLESK_hN Hn). exact (Hnext E R FULL m HC).
    Qed.
    Variable IT : itab. Hypothesis IT_ok : itab_sound HASEGS IT. Variable START : acs. Variable p : plan. Variable s : shape.
    Hypothesis Hcert : CAP.check HASEGS IT HAT NX0 AsanInit.LIMIT (ha3_XN T) ha3_XE (ha3_XB T) HS 0 true false true 400000 3000 None START p = COk s.
    Lemma stepk_sd : forall E R FULL m, cs_ok HASEGS HAT LIM SV argH ISP fs E START R FULL m -> crz HASEGS (cfg_of HASEGS R (pc START) FULL m) (sd HOLESK t_nil E (m_fs m) s).
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
        intros E0 M0 HS0 j _. rewrite HB, CxOfAps.chunk_eq. exact (proj2 (proj2 (proj2 HS0)) j). }
      exact (ha3_check_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV1 SVF SVA T HCL
               HS HOLESK HOLESK_agree HOLESK_nil HOLESK_mod stepk_holes IT IT_ok 0%nat true 3000%nat 400000%nat p START s Hcert E R FULL m HC).
    Qed.
    (* [comment removed for export] *)
    Lemma stepk_piece : s = SHole hN -> hN <> 21%nat -> PIECE START TT.
    Proof. intros Hs Hn E R FULL m HC. pose proof (stepk_sd E R FULL m HC) as RZ. rewrite Hs in RZ. cbn [sd] in RZ. rewrite (HOLESK_hN Hn) in RZ. exact RZ. Qed.
  End Step.

  Lemma flen_nonneg : 0 <= flen c. Proof. unfold flen. lia. Qed.
  Lemma flen_cap : flen c <= 2 ^ 26. Proof. unfold flen. lia. Qed.
  Lemma hdr_ok_simple : forall o, ION.hdr_ok (ION.iot_simple o 32) c. Proof. intros o. unfold ION.hdr_ok. cbn. tauto. Qed.
  Lemma hdr_ok_big : forall o rhi, 65536 <= flen c -> flen c - 6 <= rhi -> ION.hdr_ok (ION.IOT o 32 (Some (0, 32767)) (Some (0, rhi)) None None) c.
  Proof.
    intros o rhi H6 Hr. unfold ION.hdr_ok, ION.in_opt. cbn [ION.io_cfg ION.io_room ION.io_cmod ION.io_b1s].
    assert (HC : 0 <= ION.cfglen c <= 32767) by (unfold ION.cfglen; pose proof (Z.mod_pos_bound (ION.hbyte 0 c + 256 * ION.hbyte 1 c) 32768 ltac:(lia)); lia).
    unfold ION.room, ION.flenZ in *. unfold flen in H6, Hr. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hdr_ok_k0 : forall o, 6 <= flen c <= 65535 -> 0 <= ION.room c -> ION.hdr_ok (ION.IOT o 32 (Some (0, 32767)) (Some (0, 65529)) None None) c.
  Proof.
    intros o H6 Hr. unfold ION.hdr_ok, ION.in_opt. cbn [ION.io_cfg ION.io_room ION.io_cmod ION.io_b1s].
    assert (HC : 0 <= ION.cfglen c <= 32767) by (unfold ION.cfglen; pose proof (Z.mod_pos_bound (ION.hbyte 0 c + 256 * ION.hbyte 1 c) 32768 ltac:(lia)); lia).
    unfold ION.room, ION.flenZ in *. unfold flen in H6. repeat split; lia.
  Qed.
  Theorem k0_b2 : forall (TT : env -> Fs.Fs -> TSet), t_agree TT -> (forall E fs0, TT E fs0 []) -> 6 <= flen c <= 65535 -> 0 <= ION.room c ->
    PIECE c7b2_hs25 TT -> PIECE c3b2_hs98 (fun E fs' => t_alt2 (T_cannot argv1 fs') (TT E fs')).
  Proof.
    intros TT TA TN HF Hr Hn E R FULL m HC.
    assert (HHS : forall h ch, C7B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 25%nat /\ 25%nat <> 21%nat /\ ch = c7b2_hs25)).
    { intros h ch Hh. unfold C7B2_HS, C7B2_HS0 in Hh. destruct (Nat.eqb h 21) eqn:H21; [apply Nat.eqb_eq in H21; diet_injection Hh; left; split; [exact H21 | reflexivity]|].
      destruct (Nat.eqb h 25) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
    pose proof (stepk_sd TT TA TN 25%nat ltac:(lia) (ION.IOT (ION.OFile 6 65535) 32 (Some (0, 32767)) (Some (0, 65529)) None None) 6 65535 eq_refl eq_refl HF (hdr_ok_k0 _ HF Hr)
                  C7B2_HS c7b2_hs25 HHS Hn c7b2_IT c7b2_IT_ok c3b2_hs98 c7_top0 c7b2_shape c7b2_cert E R FULL m HC) as RZ.
    rewrite c7b2_shape_eq in RZ. eapply crz_conseq; [exact RZ|]. cbn [sd].
    destruct (vals1_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as [U7 B2].
    apply t_eq_alt2; [exact (noent_eval E (m_fs m) argv1 U7 B2)|].
    rewrite (HOLESK_hN TT 25%nat ltac:(lia) ltac:(discriminate)). apply t_eq_refl.
  Qed.

  Lemma flen_cap' : flen c <= 67108864. Proof. unfold flen. lia. Qed.

  Section Chain.
    Variable TT : env -> Fs.Fs -> TSet.
    Hypothesis TT_agree : t_agree TT.
    Hypothesis TT_nil : forall E fs0, TT E fs0 [].
    (* [comment removed for export] *)
    Lemma kp_piece_b2 : 65536 <= flen c -> PIECE kpb2_hs101 TT -> PIECE c3b2_hs98k (fun E fs' => t_alt2 (T_cannot argv1 fs') (TT E fs')).
    Proof.
      intros HF Hn E R FULL m HC.
      assert (HHS : forall h ch, KPB2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 101%nat /\ 101%nat <> 21%nat /\ ch = kpb2_hs101)).
      { intros h ch Hh. unfold KPB2_HS, KPB2_HS0 in Hh. destruct (Nat.eqb h 21) eqn:H21; [apply Nat.eqb_eq in H21; diet_injection Hh; left; split; [exact H21 | reflexivity]|]. destruct (Nat.eqb h 101) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      pose proof (stepk_sd TT TT_agree TT_nil 101%nat ltac:(lia) (ION.IOT (ION.OFile 65536 67108864) 32 None None None None) 65536 67108864 eq_refl eq_refl (conj HF flen_cap') (hdr_ok_simple _)
                    KPB2_HS kpb2_hs101 HHS Hn kpb2_IT kpb2_IT_ok c3b2_hs98k kpb2_pl kpb2_shape kpb2_cert E R FULL m HC) as RZ.
      rewrite kpb2_shape_eq in RZ. eapply crz_conseq; [exact RZ|]. cbn [sd].
      destruct (vals1_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as [U7 B2].
      apply t_eq_alt2; [exact (noent_eval E (m_fs m) argv1 U7 B2)|].
      rewrite (HOLESK_hN TT 101%nat ltac:(lia) ltac:(discriminate)). apply t_eq_refl.
    Qed.
    Lemma kw1_step_b2 : 131072 <= flen c -> PIECE kw1b2_hs102 TT -> PIECE kpb2_hs101 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW1B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 102%nat /\ 102%nat <> 21%nat /\ ch = kw1b2_hs102)).
      { intros h ch Hh. unfold KW1B2_HS, KW1B2_HS0 in Hh. destruct (Nat.eqb h 102) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 102%nat ltac:(lia) (ION.IOT (ION.OFile 131072 67108864) 32 None None None None) 131072 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW1B2_HS kw1b2_hs102 HHS Hn kw1b2_IT kw1b2_IT_ok kpb2_hs101 kw1b2_pl kw1b2_shape kw1b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw2_step_b2 : 262144 <= flen c -> PIECE kw2b2_hs103 TT -> PIECE kw1b2_hs102 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW2B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 103%nat /\ 103%nat <> 21%nat /\ ch = kw2b2_hs103)).
      { intros h ch Hh. unfold KW2B2_HS, KW2B2_HS0 in Hh. destruct (Nat.eqb h 103) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 103%nat ltac:(lia) (ION.IOT (ION.OFile 262144 67108864) 32 None None None None) 262144 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW2B2_HS kw2b2_hs103 HHS Hn kw2b2_IT kw2b2_IT_ok kw1b2_hs102 kw2b2_pl kw2b2_shape kw2b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw3_step_b2 : 524288 <= flen c -> PIECE kw3b2_hs104 TT -> PIECE kw2b2_hs103 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW3B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 104%nat /\ 104%nat <> 21%nat /\ ch = kw3b2_hs104)).
      { intros h ch Hh. unfold KW3B2_HS, KW3B2_HS0 in Hh. destruct (Nat.eqb h 104) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 104%nat ltac:(lia) (ION.IOT (ION.OFile 524288 67108864) 32 None None None None) 524288 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW3B2_HS kw3b2_hs104 HHS Hn kw3b2_IT kw3b2_IT_ok kw2b2_hs103 kw3b2_pl kw3b2_shape kw3b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw4_step_b2 : 1048576 <= flen c -> PIECE kw4b2_hs105 TT -> PIECE kw3b2_hs104 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW4B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 105%nat /\ 105%nat <> 21%nat /\ ch = kw4b2_hs105)).
      { intros h ch Hh. unfold KW4B2_HS, KW4B2_HS0 in Hh. destruct (Nat.eqb h 105) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 105%nat ltac:(lia) (ION.IOT (ION.OFile 1048576 67108864) 32 None None None None) 1048576 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW4B2_HS kw4b2_hs105 HHS Hn kw4b2_IT kw4b2_IT_ok kw3b2_hs104 kw4b2_pl kw4b2_shape kw4b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw5_step_b2 : 2097152 <= flen c -> PIECE kw5b2_hs106 TT -> PIECE kw4b2_hs105 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW5B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 106%nat /\ 106%nat <> 21%nat /\ ch = kw5b2_hs106)).
      { intros h ch Hh. unfold KW5B2_HS, KW5B2_HS0 in Hh. destruct (Nat.eqb h 106) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 106%nat ltac:(lia) (ION.IOT (ION.OFile 2097152 67108864) 32 None None None None) 2097152 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW5B2_HS kw5b2_hs106 HHS Hn kw5b2_IT kw5b2_IT_ok kw4b2_hs105 kw5b2_pl kw5b2_shape kw5b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw6_step_b2 : 4194304 <= flen c -> PIECE kw6b2_hs107 TT -> PIECE kw5b2_hs106 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW6B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 107%nat /\ 107%nat <> 21%nat /\ ch = kw6b2_hs107)).
      { intros h ch Hh. unfold KW6B2_HS, KW6B2_HS0 in Hh. destruct (Nat.eqb h 107) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 107%nat ltac:(lia) (ION.IOT (ION.OFile 4194304 67108864) 32 None None None None) 4194304 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW6B2_HS kw6b2_hs107 HHS Hn kw6b2_IT kw6b2_IT_ok kw5b2_hs106 kw6b2_pl kw6b2_shape kw6b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw7_step_b2 : 8388608 <= flen c -> PIECE kw7b2_hs108 TT -> PIECE kw6b2_hs107 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW7B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 108%nat /\ 108%nat <> 21%nat /\ ch = kw7b2_hs108)).
      { intros h ch Hh. unfold KW7B2_HS, KW7B2_HS0 in Hh. destruct (Nat.eqb h 108) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 108%nat ltac:(lia) (ION.IOT (ION.OFile 8388608 67108864) 32 None None None None) 8388608 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW7B2_HS kw7b2_hs108 HHS Hn kw7b2_IT kw7b2_IT_ok kw6b2_hs107 kw7b2_pl kw7b2_shape kw7b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw8_step_b2 : 16777216 <= flen c -> PIECE kw8b2_hs109 TT -> PIECE kw7b2_hs108 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW8B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 109%nat /\ 109%nat <> 21%nat /\ ch = kw8b2_hs109)).
      { intros h ch Hh. unfold KW8B2_HS, KW8B2_HS0 in Hh. destruct (Nat.eqb h 109) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 109%nat ltac:(lia) (ION.IOT (ION.OFile 16777216 67108864) 32 None None None None) 16777216 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW8B2_HS kw8b2_hs109 HHS Hn kw8b2_IT kw8b2_IT_ok kw7b2_hs108 kw8b2_pl kw8b2_shape kw8b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw9_step_b2 : 33554432 <= flen c -> PIECE kw9b2_hs110 TT -> PIECE kw8b2_hs109 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW9B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 110%nat /\ 110%nat <> 21%nat /\ ch = kw9b2_hs110)).
      { intros h ch Hh. unfold KW9B2_HS, KW9B2_HS0 in Hh. destruct (Nat.eqb h 110) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 110%nat ltac:(lia) (ION.IOT (ION.OFile 33554432 67108864) 32 None None None None) 33554432 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW9B2_HS kw9b2_hs110 HHS Hn kw9b2_IT kw9b2_IT_ok kw8b2_hs109 kw9b2_pl kw9b2_shape kw9b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke1_step_b2 : 65536 <= flen c <= 131071 -> PIECE ke1b2_hs201 TT -> PIECE kpb2_hs101 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE1B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 201%nat /\ 201%nat <> 21%nat /\ ch = ke1b2_hs201)).
      { intros h ch Hh. unfold KE1B2_HS, KE1B2_HS0 in Hh. destruct (Nat.eqb h 201) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 201%nat ltac:(lia) (ION.IOT (ION.OFile 65536 131071) 32 (Some (0, 32767)) (Some (0, 131065)) None None) 65536 131071 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 131065 ltac:(lia) ltac:(lia))
               KE1B2_HS ke1b2_hs201 HHS Hn ke1b2_IT ke1b2_IT_ok kpb2_hs101 ke1b2_pl ke1b2_shape ke1b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke2_step_b2 : 131072 <= flen c <= 262143 -> PIECE ke2b2_hs202 TT -> PIECE kw1b2_hs102 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE2B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 202%nat /\ 202%nat <> 21%nat /\ ch = ke2b2_hs202)).
      { intros h ch Hh. unfold KE2B2_HS, KE2B2_HS0 in Hh. destruct (Nat.eqb h 202) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 202%nat ltac:(lia) (ION.IOT (ION.OFile 131072 262143) 32 (Some (0, 32767)) (Some (0, 262137)) None None) 131072 262143 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 262137 ltac:(lia) ltac:(lia))
               KE2B2_HS ke2b2_hs202 HHS Hn ke2b2_IT ke2b2_IT_ok kw1b2_hs102 ke2b2_pl ke2b2_shape ke2b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke3_step_b2 : 262144 <= flen c <= 524287 -> PIECE ke3b2_hs203 TT -> PIECE kw2b2_hs103 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE3B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 203%nat /\ 203%nat <> 21%nat /\ ch = ke3b2_hs203)).
      { intros h ch Hh. unfold KE3B2_HS, KE3B2_HS0 in Hh. destruct (Nat.eqb h 203) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 203%nat ltac:(lia) (ION.IOT (ION.OFile 262144 524287) 32 (Some (0, 32767)) (Some (0, 524281)) None None) 262144 524287 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 524281 ltac:(lia) ltac:(lia))
               KE3B2_HS ke3b2_hs203 HHS Hn ke3b2_IT ke3b2_IT_ok kw2b2_hs103 ke3b2_pl ke3b2_shape ke3b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke4_step_b2 : 524288 <= flen c <= 1048575 -> PIECE ke4b2_hs204 TT -> PIECE kw3b2_hs104 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE4B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 204%nat /\ 204%nat <> 21%nat /\ ch = ke4b2_hs204)).
      { intros h ch Hh. unfold KE4B2_HS, KE4B2_HS0 in Hh. destruct (Nat.eqb h 204) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 204%nat ltac:(lia) (ION.IOT (ION.OFile 524288 1048575) 32 (Some (0, 32767)) (Some (0, 1048569)) None None) 524288 1048575 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 1048569 ltac:(lia) ltac:(lia))
               KE4B2_HS ke4b2_hs204 HHS Hn ke4b2_IT ke4b2_IT_ok kw3b2_hs104 ke4b2_pl ke4b2_shape ke4b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke5_step_b2 : 1048576 <= flen c <= 2097151 -> PIECE ke5b2_hs205 TT -> PIECE kw4b2_hs105 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE5B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 205%nat /\ 205%nat <> 21%nat /\ ch = ke5b2_hs205)).
      { intros h ch Hh. unfold KE5B2_HS, KE5B2_HS0 in Hh. destruct (Nat.eqb h 205) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 205%nat ltac:(lia) (ION.IOT (ION.OFile 1048576 2097151) 32 (Some (0, 32767)) (Some (0, 2097145)) None None) 1048576 2097151 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 2097145 ltac:(lia) ltac:(lia))
               KE5B2_HS ke5b2_hs205 HHS Hn ke5b2_IT ke5b2_IT_ok kw4b2_hs105 ke5b2_pl ke5b2_shape ke5b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke6_step_b2 : 2097152 <= flen c <= 4194303 -> PIECE ke6b2_hs206 TT -> PIECE kw5b2_hs106 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE6B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 206%nat /\ 206%nat <> 21%nat /\ ch = ke6b2_hs206)).
      { intros h ch Hh. unfold KE6B2_HS, KE6B2_HS0 in Hh. destruct (Nat.eqb h 206) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 206%nat ltac:(lia) (ION.IOT (ION.OFile 2097152 4194303) 32 (Some (0, 32767)) (Some (0, 4194297)) None None) 2097152 4194303 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 4194297 ltac:(lia) ltac:(lia))
               KE6B2_HS ke6b2_hs206 HHS Hn ke6b2_IT ke6b2_IT_ok kw5b2_hs106 ke6b2_pl ke6b2_shape ke6b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke7_step_b2 : 4194304 <= flen c <= 8388607 -> PIECE ke7b2_hs207 TT -> PIECE kw6b2_hs107 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE7B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 207%nat /\ 207%nat <> 21%nat /\ ch = ke7b2_hs207)).
      { intros h ch Hh. unfold KE7B2_HS, KE7B2_HS0 in Hh. destruct (Nat.eqb h 207) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 207%nat ltac:(lia) (ION.IOT (ION.OFile 4194304 8388607) 32 (Some (0, 32767)) (Some (0, 8388601)) None None) 4194304 8388607 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 8388601 ltac:(lia) ltac:(lia))
               KE7B2_HS ke7b2_hs207 HHS Hn ke7b2_IT ke7b2_IT_ok kw6b2_hs107 ke7b2_pl ke7b2_shape ke7b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke8_step_b2 : 8388608 <= flen c <= 16777215 -> PIECE ke8b2_hs208 TT -> PIECE kw7b2_hs108 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE8B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 208%nat /\ 208%nat <> 21%nat /\ ch = ke8b2_hs208)).
      { intros h ch Hh. unfold KE8B2_HS, KE8B2_HS0 in Hh. destruct (Nat.eqb h 208) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 208%nat ltac:(lia) (ION.IOT (ION.OFile 8388608 16777215) 32 (Some (0, 32767)) (Some (0, 16777209)) None None) 8388608 16777215 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 16777209 ltac:(lia) ltac:(lia))
               KE8B2_HS ke8b2_hs208 HHS Hn ke8b2_IT ke8b2_IT_ok kw7b2_hs108 ke8b2_pl ke8b2_shape ke8b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke9_step_b2 : 16777216 <= flen c <= 33554431 -> PIECE ke9b2_hs209 TT -> PIECE kw8b2_hs109 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE9B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 209%nat /\ 209%nat <> 21%nat /\ ch = ke9b2_hs209)).
      { intros h ch Hh. unfold KE9B2_HS, KE9B2_HS0 in Hh. destruct (Nat.eqb h 209) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 209%nat ltac:(lia) (ION.IOT (ION.OFile 16777216 33554431) 32 (Some (0, 32767)) (Some (0, 33554425)) None None) 16777216 33554431 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 33554425 ltac:(lia) ltac:(lia))
               KE9B2_HS ke9b2_hs209 HHS Hn ke9b2_IT ke9b2_IT_ok kw8b2_hs109 ke9b2_pl ke9b2_shape ke9b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke10_step_b2 : 33554432 <= flen c <= 67108863 -> PIECE ke10b2_hs210 TT -> PIECE kw9b2_hs110 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE10B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 210%nat /\ 210%nat <> 21%nat /\ ch = ke10b2_hs210)).
      { intros h ch Hh. unfold KE10B2_HS, KE10B2_HS0 in Hh. destruct (Nat.eqb h 210) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 210%nat ltac:(lia) (ION.IOT (ION.OFile 33554432 67108863) 32 (Some (0, 32767)) (Some (0, 67108857)) None None) 33554432 67108863 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 67108857 ltac:(lia) ltac:(lia))
               KE10B2_HS ke10b2_hs210 HHS Hn ke10b2_IT ke10b2_IT_ok kw9b2_hs110 ke10b2_pl ke10b2_shape ke10b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc1_step_b2 : 65536 <= flen c <= 131071 -> PIECE kc1b2_hs301 TT -> PIECE ke1b2_hs201 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC1B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 301%nat /\ 301%nat <> 21%nat /\ ch = kc1b2_hs301)).
      { intros h ch Hh. unfold KC1B2_HS, KC1B2_HS0 in Hh. destruct (Nat.eqb h 301) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 301%nat ltac:(lia) (ION.IOT (ION.OFile 65536 131071) 32 (Some (0, 32767)) (Some (0, 131065)) None None) 65536 131071 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 131065 ltac:(lia) ltac:(lia))
               KC1B2_HS kc1b2_hs301 HHS Hn kc1b2_IT kc1b2_IT_ok ke1b2_hs201 kc1b2_pl kc1b2_shape kc1b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc2_step_b2 : 131072 <= flen c <= 262143 -> PIECE kc2b2_hs302 TT -> PIECE ke2b2_hs202 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC2B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 302%nat /\ 302%nat <> 21%nat /\ ch = kc2b2_hs302)).
      { intros h ch Hh. unfold KC2B2_HS, KC2B2_HS0 in Hh. destruct (Nat.eqb h 302) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 302%nat ltac:(lia) (ION.IOT (ION.OFile 131072 262143) 32 (Some (0, 32767)) (Some (0, 262137)) None None) 131072 262143 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 262137 ltac:(lia) ltac:(lia))
               KC2B2_HS kc2b2_hs302 HHS Hn kc2b2_IT kc2b2_IT_ok ke2b2_hs202 kc2b2_pl kc2b2_shape kc2b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc3_step_b2 : 262144 <= flen c <= 524287 -> PIECE kc3b2_hs303 TT -> PIECE ke3b2_hs203 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC3B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 303%nat /\ 303%nat <> 21%nat /\ ch = kc3b2_hs303)).
      { intros h ch Hh. unfold KC3B2_HS, KC3B2_HS0 in Hh. destruct (Nat.eqb h 303) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 303%nat ltac:(lia) (ION.IOT (ION.OFile 262144 524287) 32 (Some (0, 32767)) (Some (0, 524281)) None None) 262144 524287 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 524281 ltac:(lia) ltac:(lia))
               KC3B2_HS kc3b2_hs303 HHS Hn kc3b2_IT kc3b2_IT_ok ke3b2_hs203 kc3b2_pl kc3b2_shape kc3b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc4_step_b2 : 524288 <= flen c <= 1048575 -> PIECE kc4b2_hs304 TT -> PIECE ke4b2_hs204 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC4B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 304%nat /\ 304%nat <> 21%nat /\ ch = kc4b2_hs304)).
      { intros h ch Hh. unfold KC4B2_HS, KC4B2_HS0 in Hh. destruct (Nat.eqb h 304) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 304%nat ltac:(lia) (ION.IOT (ION.OFile 524288 1048575) 32 (Some (0, 32767)) (Some (0, 1048569)) None None) 524288 1048575 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 1048569 ltac:(lia) ltac:(lia))
               KC4B2_HS kc4b2_hs304 HHS Hn kc4b2_IT kc4b2_IT_ok ke4b2_hs204 kc4b2_pl kc4b2_shape kc4b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc5_step_b2 : 1048576 <= flen c <= 2097151 -> PIECE kc5b2_hs305 TT -> PIECE ke5b2_hs205 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC5B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 305%nat /\ 305%nat <> 21%nat /\ ch = kc5b2_hs305)).
      { intros h ch Hh. unfold KC5B2_HS, KC5B2_HS0 in Hh. destruct (Nat.eqb h 305) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 305%nat ltac:(lia) (ION.IOT (ION.OFile 1048576 2097151) 32 (Some (0, 32767)) (Some (0, 2097145)) None None) 1048576 2097151 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 2097145 ltac:(lia) ltac:(lia))
               KC5B2_HS kc5b2_hs305 HHS Hn kc5b2_IT kc5b2_IT_ok ke5b2_hs205 kc5b2_pl kc5b2_shape kc5b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc6_step_b2 : 2097152 <= flen c <= 4194303 -> PIECE kc6b2_hs306 TT -> PIECE ke6b2_hs206 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC6B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 306%nat /\ 306%nat <> 21%nat /\ ch = kc6b2_hs306)).
      { intros h ch Hh. unfold KC6B2_HS, KC6B2_HS0 in Hh. destruct (Nat.eqb h 306) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 306%nat ltac:(lia) (ION.IOT (ION.OFile 2097152 4194303) 32 (Some (0, 32767)) (Some (0, 4194297)) None None) 2097152 4194303 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 4194297 ltac:(lia) ltac:(lia))
               KC6B2_HS kc6b2_hs306 HHS Hn kc6b2_IT kc6b2_IT_ok ke6b2_hs206 kc6b2_pl kc6b2_shape kc6b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc7_step_b2 : 4194304 <= flen c <= 8388607 -> PIECE kc7b2_hs307 TT -> PIECE ke7b2_hs207 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC7B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 307%nat /\ 307%nat <> 21%nat /\ ch = kc7b2_hs307)).
      { intros h ch Hh. unfold KC7B2_HS, KC7B2_HS0 in Hh. destruct (Nat.eqb h 307) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 307%nat ltac:(lia) (ION.IOT (ION.OFile 4194304 8388607) 32 (Some (0, 32767)) (Some (0, 8388601)) None None) 4194304 8388607 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 8388601 ltac:(lia) ltac:(lia))
               KC7B2_HS kc7b2_hs307 HHS Hn kc7b2_IT kc7b2_IT_ok ke7b2_hs207 kc7b2_pl kc7b2_shape kc7b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc8_step_b2 : 8388608 <= flen c <= 16777215 -> PIECE kc8b2_hs308 TT -> PIECE ke8b2_hs208 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC8B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 308%nat /\ 308%nat <> 21%nat /\ ch = kc8b2_hs308)).
      { intros h ch Hh. unfold KC8B2_HS, KC8B2_HS0 in Hh. destruct (Nat.eqb h 308) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 308%nat ltac:(lia) (ION.IOT (ION.OFile 8388608 16777215) 32 (Some (0, 32767)) (Some (0, 16777209)) None None) 8388608 16777215 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 16777209 ltac:(lia) ltac:(lia))
               KC8B2_HS kc8b2_hs308 HHS Hn kc8b2_IT kc8b2_IT_ok ke8b2_hs208 kc8b2_pl kc8b2_shape kc8b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc9_step_b2 : 16777216 <= flen c <= 33554431 -> PIECE kc9b2_hs309 TT -> PIECE ke9b2_hs209 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC9B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 309%nat /\ 309%nat <> 21%nat /\ ch = kc9b2_hs309)).
      { intros h ch Hh. unfold KC9B2_HS, KC9B2_HS0 in Hh. destruct (Nat.eqb h 309) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 309%nat ltac:(lia) (ION.IOT (ION.OFile 16777216 33554431) 32 (Some (0, 32767)) (Some (0, 33554425)) None None) 16777216 33554431 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 33554425 ltac:(lia) ltac:(lia))
               KC9B2_HS kc9b2_hs309 HHS Hn kc9b2_IT kc9b2_IT_ok ke9b2_hs209 kc9b2_pl kc9b2_shape kc9b2_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc10_step_b2 : 33554432 <= flen c <= 67108863 -> PIECE kc10b2_hs310 TT -> PIECE ke10b2_hs210 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC10B2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 310%nat /\ 310%nat <> 21%nat /\ ch = kc10b2_hs310)).
      { intros h ch Hh. unfold KC10B2_HS, KC10B2_HS0 in Hh. destruct (Nat.eqb h 310) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 310%nat ltac:(lia) (ION.IOT (ION.OFile 33554432 67108863) 32 (Some (0, 32767)) (Some (0, 67108857)) None None) 33554432 67108863 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 67108857 ltac:(lia) ltac:(lia))
               KC10B2_HS kc10b2_hs310 HHS Hn kc10b2_IT kc10b2_IT_ok ke10b2_hs210 kc10b2_pl kc10b2_shape kc10b2_cert eq_refl ltac:(discriminate)).
    Qed.
  End Chain.
  (* [comment removed for export] *)
  Definition fi_start_b2 (k : Z) : acs := if k =? 1 then kc1b2_hs301 else if k =? 2 then kc2b2_hs302 else if k =? 3 then kc3b2_hs303 else if k =? 4 then kc4b2_hs304 else if k =? 5 then kc5b2_hs305 else if k =? 6 then kc6b2_hs306 else if k =? 7 then kc7b2_hs307 else if k =? 8 then kc8b2_hs308 else if k =? 9 then kc9b2_hs309 else kc10b2_hs310.

  Theorem kge1_b2 : forall (TT : env -> Fs.Fs -> TSet), t_agree TT -> (forall E fs0, TT E fs0 []) ->
    forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (fi_start_b2 k) TT ->
    PIECE c3b2_hs98k (fun E fs' => t_alt2 (T_cannot argv1 fs') (TT E fs')).
  Proof.
    intros TT TA TN k Hk HF HP.
    assert (HK : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
    destruct HK as [HK | [HK | [HK | [HK | [HK | [HK | [HK | [HK | [HK | HK]]]]]]]]]; subst k; cbn in HF; unfold fi_start_b2 in HP; cbn in HP.
    - apply (kp_piece_b2 TT TA TN); [lia|]. exact (ke1_step_b2 TT TA TN ltac:(lia) (kc1_step_b2 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_b2 TT TA TN); [lia|]. apply (kw1_step_b2 TT TA TN); [lia|]. exact (ke2_step_b2 TT TA TN ltac:(lia) (kc2_step_b2 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_b2 TT TA TN); [lia|]. apply (kw1_step_b2 TT TA TN); [lia|]. apply (kw2_step_b2 TT TA TN); [lia|]. exact (ke3_step_b2 TT TA TN ltac:(lia) (kc3_step_b2 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_b2 TT TA TN); [lia|]. apply (kw1_step_b2 TT TA TN); [lia|]. apply (kw2_step_b2 TT TA TN); [lia|]. apply (kw3_step_b2 TT TA TN); [lia|]. exact (ke4_step_b2 TT TA TN ltac:(lia) (kc4_step_b2 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_b2 TT TA TN); [lia|]. apply (kw1_step_b2 TT TA TN); [lia|]. apply (kw2_step_b2 TT TA TN); [lia|]. apply (kw3_step_b2 TT TA TN); [lia|]. apply (kw4_step_b2 TT TA TN); [lia|]. exact (ke5_step_b2 TT TA TN ltac:(lia) (kc5_step_b2 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_b2 TT TA TN); [lia|]. apply (kw1_step_b2 TT TA TN); [lia|]. apply (kw2_step_b2 TT TA TN); [lia|]. apply (kw3_step_b2 TT TA TN); [lia|]. apply (kw4_step_b2 TT TA TN); [lia|]. apply (kw5_step_b2 TT TA TN); [lia|]. exact (ke6_step_b2 TT TA TN ltac:(lia) (kc6_step_b2 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_b2 TT TA TN); [lia|]. apply (kw1_step_b2 TT TA TN); [lia|]. apply (kw2_step_b2 TT TA TN); [lia|]. apply (kw3_step_b2 TT TA TN); [lia|]. apply (kw4_step_b2 TT TA TN); [lia|]. apply (kw5_step_b2 TT TA TN); [lia|]. apply (kw6_step_b2 TT TA TN); [lia|]. exact (ke7_step_b2 TT TA TN ltac:(lia) (kc7_step_b2 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_b2 TT TA TN); [lia|]. apply (kw1_step_b2 TT TA TN); [lia|]. apply (kw2_step_b2 TT TA TN); [lia|]. apply (kw3_step_b2 TT TA TN); [lia|]. apply (kw4_step_b2 TT TA TN); [lia|]. apply (kw5_step_b2 TT TA TN); [lia|]. apply (kw6_step_b2 TT TA TN); [lia|]. apply (kw7_step_b2 TT TA TN); [lia|]. exact (ke8_step_b2 TT TA TN ltac:(lia) (kc8_step_b2 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_b2 TT TA TN); [lia|]. apply (kw1_step_b2 TT TA TN); [lia|]. apply (kw2_step_b2 TT TA TN); [lia|]. apply (kw3_step_b2 TT TA TN); [lia|]. apply (kw4_step_b2 TT TA TN); [lia|]. apply (kw5_step_b2 TT TA TN); [lia|]. apply (kw6_step_b2 TT TA TN); [lia|]. apply (kw7_step_b2 TT TA TN); [lia|]. apply (kw8_step_b2 TT TA TN); [lia|]. exact (ke9_step_b2 TT TA TN ltac:(lia) (kc9_step_b2 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_b2 TT TA TN); [lia|]. apply (kw1_step_b2 TT TA TN); [lia|]. apply (kw2_step_b2 TT TA TN); [lia|]. apply (kw3_step_b2 TT TA TN); [lia|]. apply (kw4_step_b2 TT TA TN); [lia|]. apply (kw5_step_b2 TT TA TN); [lia|]. apply (kw6_step_b2 TT TA TN); [lia|]. apply (kw7_step_b2 TT TA TN); [lia|]. apply (kw8_step_b2 TT TA TN); [lia|]. apply (kw9_step_b2 TT TA TN); [lia|]. exact (ke10_step_b2 TT TA TN ltac:(lia) (kc10_step_b2 TT TA TN ltac:(lia) HP)).
  Qed.

  (* [comment removed for export] *)
  Section Refused.
    Hypothesis H_FER : FXHOLE krb2_hs230 feendrb2.
    Lemma xr_piece_b2 : PIECE feendrb2 T_exit2.
    Proof.
      intros E R FULL m HC.
      exact (CHK1 (fun _ : nat => @None acs) (fun _ _ _ => t_nil) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl)
               (fun h ch Hh => ltac:(discriminate Hh)) xrb2_IT xrb2_IT_ok 0%nat true 3000%nat 400000%nat xu_plan feendrb2 xrb2_shape xrb2_cert E R FULL m HC).
    Qed.
    Lemma fer_piece_b2 : PIECE krb2_hs230 T_exit2.
    Proof. apply (hole_compose SV argH ISP fs krb2_hs230 feendrb2 T_exit2); [vm_compute; lia | intros E E' fs0 _; reflexivity | exact H_FER | exact xr_piece_b2]. Qed.
    Let TR : env -> Fs.Fs -> TSet := fun _ fs' => T_lit refused_lit fs'.
    Lemma TR_agree : t_agree TR. Proof. intros E E' fs0 _. reflexivity. Qed.
    Lemma TR_nil : forall E fs0, TR E fs0 []. Proof. intros E fs0. unfold TR, T_lit. apply t_emit_has_nil. Qed.
    Lemma kr_piece_b2 : 67108864 <= flen c -> PIECE kw9b2_hs110 TR.
    Proof.
      intros HF E R FULL m HC.
      assert (HHS : forall h ch, KRB2_HS h = Some ch -> (h = 21%nat /\ ch = c4b2_hs21) \/ (h = 230%nat /\ 230%nat <> 21%nat /\ ch = krb2_hs230)).
      { intros h ch Hh. unfold KRB2_HS, KRB2_HS0 in Hh. destruct (Nat.eqb h 230) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      pose proof (stepk_sd T_exit2 (fun E0 E1 fs0 _ => eq_refl) (fun E0 fs0 => CXS.t_exit_has_nil _ fs0) 230%nat ltac:(lia) (ION.IOT (ION.OFile 67108864 67108864) 32 None None None None) 67108864 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
                    KRB2_HS krb2_hs230 HHS fer_piece_b2 krb2_IT krb2_IT_ok kw9b2_hs110 krb2_pl krb2_shape krb2_cert E R FULL m HC) as RZ.
      rewrite krb2_shape_eq in RZ. eapply crz_conseq; [exact RZ|]. cbn [sd].
      rewrite (HOLESK_hN T_exit2 230%nat ltac:(lia) ltac:(discriminate)). unfold TR. exact (leafL E (m_fs m) refused_lit).
    Qed.
    Theorem refused_b2 : 67108864 <= flen c -> PIECE c3b2_hs98k (fun _ fs' => T_hdr refused_lit argv1 fs').
    Proof.
      intros HF. unfold T_hdr. apply (kp_piece_b2 TR TR_agree TR_nil); [lia|].
      apply (kw1_step_b2 TR TR_agree TR_nil); [lia|]. apply (kw2_step_b2 TR TR_agree TR_nil); [lia|]. apply (kw3_step_b2 TR TR_agree TR_nil); [lia|]. apply (kw4_step_b2 TR TR_agree TR_nil); [lia|]. apply (kw5_step_b2 TR TR_agree TR_nil); [lia|]. apply (kw6_step_b2 TR TR_agree TR_nil); [lia|]. apply (kw7_step_b2 TR TR_agree TR_nil); [lia|]. apply (kw8_step_b2 TR TR_agree TR_nil); [lia|]. apply (kw9_step_b2 TR TR_agree TR_nil); [lia|]. exact (kr_piece_b2 HF).
    Qed.
  End Refused.

End Kge1B2.
