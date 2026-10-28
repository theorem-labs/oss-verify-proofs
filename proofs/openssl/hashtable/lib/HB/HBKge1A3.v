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
  BC3A3Lit BC3A3LitK BC4e BC4A3Lit BFEEndOA3 HBOpenA3 BC7 BC7A3Lit BC7A3Cert BKInv BKPb BKPA3Inv BKPA3Lit BKPA3Cert BKW1b BKW1A3Inv BKW1A3Lit BKW1A3Cert BKW2b BKW2A3Inv BKW2A3Lit BKW2A3Cert BKW3b BKW3A3Inv BKW3A3Lit BKW3A3Cert BKW4b BKW4A3Inv BKW4A3Lit BKW4A3Cert BKW5b BKW5A3Inv BKW5A3Lit BKW5A3Cert BKW6b BKW6A3Inv BKW6A3Lit BKW6A3Cert BKW7b BKW7A3Inv BKW7A3Lit BKW7A3Cert BKW8b BKW8A3Inv BKW8A3Lit BKW8A3Cert BKW9b BKW9A3Inv BKW9A3Lit BKW9A3Cert BKE1b BKE1A3Inv BKE1A3Lit BKE1A3Cert BKE2b BKE2A3Inv BKE2A3Lit BKE2A3Cert BKE3b BKE3A3Inv BKE3A3Lit BKE3A3Cert BKE4b BKE4A3Inv BKE4A3Lit BKE4A3Cert BKE5b BKE5A3Inv BKE5A3Lit BKE5A3Cert BKE6b BKE6A3Inv BKE6A3Lit BKE6A3Cert BKE7b BKE7A3Inv BKE7A3Lit BKE7A3Cert BKE8b BKE8A3Inv BKE8A3Lit BKE8A3Cert BKE9b BKE9A3Inv BKE9A3Lit BKE9A3Cert BKE10b BKE10A3Inv BKE10A3Lit BKE10A3Cert BKC1A3Inv BKC1A3Lit BKC1A3Cert BKC2A3Inv BKC2A3Lit BKC2A3Cert BKC3A3Inv BKC3A3Lit BKC3A3Cert BKC4A3Inv BKC4A3Lit BKC4A3Cert BKC5A3Inv BKC5A3Lit BKC5A3Cert BKC6A3Inv BKC6A3Lit BKC6A3Cert BKC7A3Inv BKC7A3Lit BKC7A3Cert BKC8A3Inv BKC8A3Lit BKC8A3Cert BKC9A3Inv BKC9A3Lit BKC9A3Cert BKC10A3Inv BKC10A3Lit BKC10A3Cert BKRb BKRA3Inv BKRA3Lit BKRA3Cert BFEEndRA3 BXu BXRA3Cert.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Lemma kpa3_shape_eq : kpa3_shape = SAlt2 noent_shape (SHole 101). Proof. reflexivity. Qed.
Lemma c7a3_shape_eq : c7a3_shape = SAlt2 noent_shape (SHole 25). Proof. reflexivity. Qed.
Definition refused_lit : list Z := [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 54; 55; 49; 48; 56; 56; 54; 52; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10].
Lemma kra3_shape_eq : kra3_shape = SEmitP 2 [SPLit refused_lit] (SHole 230). Proof. reflexivity. Qed.

Section Kge1A3.
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
    Hypothesis HHS : forall h ch, HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = hN /\ hN <> 21%nat /\ ch = NEXT).
    Hypothesis Hnext : PIECE NEXT TT.
    Lemma stepk_holes : holes_stmt HASEGS HAT LIM HS SV argH ISP HOLESK fs.
    Proof.
      intros h ch Hh E R FULL m HC. destruct (HHS h ch Hh) as [[-> ->] | (-> & Hn & ->)].
      - change (HOLESK 21 E (m_fs m)) with (T_exit2 E (m_fs m)). exact (feo_piece_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEO E R FULL m HC).
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
  Theorem k0_a3 : forall (TT : env -> Fs.Fs -> TSet), t_agree TT -> (forall E fs0, TT E fs0 []) -> 6 <= flen c <= 65535 -> 0 <= ION.room c ->
    PIECE c7a3_hs25 TT -> PIECE c3a3_hs98 (fun E fs' => t_alt2 (T_cannot argv1 fs') (TT E fs')).
  Proof.
    intros TT TA TN HF Hr Hn E R FULL m HC.
    assert (HHS : forall h ch, C7A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 25%nat /\ 25%nat <> 21%nat /\ ch = c7a3_hs25)).
    { intros h ch Hh. unfold C7A3_HS, C7A3_HS0 in Hh. destruct (Nat.eqb h 21) eqn:H21; [apply Nat.eqb_eq in H21; diet_injection Hh; left; split; [exact H21 | reflexivity]|].
      destruct (Nat.eqb h 25) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
    pose proof (stepk_sd TT TA TN 25%nat ltac:(lia) (ION.IOT (ION.OFile 6 65535) 32 (Some (0, 32767)) (Some (0, 65529)) None None) 6 65535 eq_refl eq_refl HF (hdr_ok_k0 _ HF Hr)
                  C7A3_HS c7a3_hs25 HHS Hn c7a3_IT c7a3_IT_ok c3a3_hs98 c7_top0 c7a3_shape c7a3_cert E R FULL m HC) as RZ.
    rewrite c7a3_shape_eq in RZ. eapply crz_conseq; [exact RZ|]. cbn [sd].
    destruct (vals1_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as [U7 B2].
    apply t_eq_alt2; [exact (noent_eval E (m_fs m) argv1 U7 B2)|].
    rewrite (HOLESK_hN TT 25%nat ltac:(lia) ltac:(discriminate)). apply t_eq_refl.
  Qed.

  Lemma flen_cap' : flen c <= 67108864. Proof. unfold flen. lia. Qed.

  Section Chain.
    Variable TT : env -> Fs.Fs -> TSet.
    Hypothesis TT_agree : t_agree TT.
    Hypothesis TT_nil : forall E fs0, TT E fs0 [].
    (* [comment removed for export] *)
    Lemma kp_piece_a3 : 65536 <= flen c -> PIECE kpa3_hs101 TT -> PIECE c3a3_hs98k (fun E fs' => t_alt2 (T_cannot argv1 fs') (TT E fs')).
    Proof.
      intros HF Hn E R FULL m HC.
      assert (HHS : forall h ch, KPA3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 101%nat /\ 101%nat <> 21%nat /\ ch = kpa3_hs101)).
      { intros h ch Hh. unfold KPA3_HS, KPA3_HS0 in Hh. destruct (Nat.eqb h 21) eqn:H21; [apply Nat.eqb_eq in H21; diet_injection Hh; left; split; [exact H21 | reflexivity]|]. destruct (Nat.eqb h 101) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      pose proof (stepk_sd TT TT_agree TT_nil 101%nat ltac:(lia) (ION.IOT (ION.OFile 65536 67108864) 32 None None None None) 65536 67108864 eq_refl eq_refl (conj HF flen_cap') (hdr_ok_simple _)
                    KPA3_HS kpa3_hs101 HHS Hn kpa3_IT kpa3_IT_ok c3a3_hs98k kpa3_pl kpa3_shape kpa3_cert E R FULL m HC) as RZ.
      rewrite kpa3_shape_eq in RZ. eapply crz_conseq; [exact RZ|]. cbn [sd].
      destruct (vals1_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as [U7 B2].
      apply t_eq_alt2; [exact (noent_eval E (m_fs m) argv1 U7 B2)|].
      rewrite (HOLESK_hN TT 101%nat ltac:(lia) ltac:(discriminate)). apply t_eq_refl.
    Qed.
    Lemma kw1_step_a3 : 131072 <= flen c -> PIECE kw1a3_hs102 TT -> PIECE kpa3_hs101 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW1A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 102%nat /\ 102%nat <> 21%nat /\ ch = kw1a3_hs102)).
      { intros h ch Hh. unfold KW1A3_HS, KW1A3_HS0 in Hh. destruct (Nat.eqb h 102) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 102%nat ltac:(lia) (ION.IOT (ION.OFile 131072 67108864) 32 None None None None) 131072 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW1A3_HS kw1a3_hs102 HHS Hn kw1a3_IT kw1a3_IT_ok kpa3_hs101 kw1a3_pl kw1a3_shape kw1a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw2_step_a3 : 262144 <= flen c -> PIECE kw2a3_hs103 TT -> PIECE kw1a3_hs102 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW2A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 103%nat /\ 103%nat <> 21%nat /\ ch = kw2a3_hs103)).
      { intros h ch Hh. unfold KW2A3_HS, KW2A3_HS0 in Hh. destruct (Nat.eqb h 103) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 103%nat ltac:(lia) (ION.IOT (ION.OFile 262144 67108864) 32 None None None None) 262144 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW2A3_HS kw2a3_hs103 HHS Hn kw2a3_IT kw2a3_IT_ok kw1a3_hs102 kw2a3_pl kw2a3_shape kw2a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw3_step_a3 : 524288 <= flen c -> PIECE kw3a3_hs104 TT -> PIECE kw2a3_hs103 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW3A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 104%nat /\ 104%nat <> 21%nat /\ ch = kw3a3_hs104)).
      { intros h ch Hh. unfold KW3A3_HS, KW3A3_HS0 in Hh. destruct (Nat.eqb h 104) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 104%nat ltac:(lia) (ION.IOT (ION.OFile 524288 67108864) 32 None None None None) 524288 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW3A3_HS kw3a3_hs104 HHS Hn kw3a3_IT kw3a3_IT_ok kw2a3_hs103 kw3a3_pl kw3a3_shape kw3a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw4_step_a3 : 1048576 <= flen c -> PIECE kw4a3_hs105 TT -> PIECE kw3a3_hs104 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW4A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 105%nat /\ 105%nat <> 21%nat /\ ch = kw4a3_hs105)).
      { intros h ch Hh. unfold KW4A3_HS, KW4A3_HS0 in Hh. destruct (Nat.eqb h 105) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 105%nat ltac:(lia) (ION.IOT (ION.OFile 1048576 67108864) 32 None None None None) 1048576 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW4A3_HS kw4a3_hs105 HHS Hn kw4a3_IT kw4a3_IT_ok kw3a3_hs104 kw4a3_pl kw4a3_shape kw4a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw5_step_a3 : 2097152 <= flen c -> PIECE kw5a3_hs106 TT -> PIECE kw4a3_hs105 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW5A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 106%nat /\ 106%nat <> 21%nat /\ ch = kw5a3_hs106)).
      { intros h ch Hh. unfold KW5A3_HS, KW5A3_HS0 in Hh. destruct (Nat.eqb h 106) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 106%nat ltac:(lia) (ION.IOT (ION.OFile 2097152 67108864) 32 None None None None) 2097152 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW5A3_HS kw5a3_hs106 HHS Hn kw5a3_IT kw5a3_IT_ok kw4a3_hs105 kw5a3_pl kw5a3_shape kw5a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw6_step_a3 : 4194304 <= flen c -> PIECE kw6a3_hs107 TT -> PIECE kw5a3_hs106 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW6A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 107%nat /\ 107%nat <> 21%nat /\ ch = kw6a3_hs107)).
      { intros h ch Hh. unfold KW6A3_HS, KW6A3_HS0 in Hh. destruct (Nat.eqb h 107) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 107%nat ltac:(lia) (ION.IOT (ION.OFile 4194304 67108864) 32 None None None None) 4194304 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW6A3_HS kw6a3_hs107 HHS Hn kw6a3_IT kw6a3_IT_ok kw5a3_hs106 kw6a3_pl kw6a3_shape kw6a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw7_step_a3 : 8388608 <= flen c -> PIECE kw7a3_hs108 TT -> PIECE kw6a3_hs107 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW7A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 108%nat /\ 108%nat <> 21%nat /\ ch = kw7a3_hs108)).
      { intros h ch Hh. unfold KW7A3_HS, KW7A3_HS0 in Hh. destruct (Nat.eqb h 108) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 108%nat ltac:(lia) (ION.IOT (ION.OFile 8388608 67108864) 32 None None None None) 8388608 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW7A3_HS kw7a3_hs108 HHS Hn kw7a3_IT kw7a3_IT_ok kw6a3_hs107 kw7a3_pl kw7a3_shape kw7a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw8_step_a3 : 16777216 <= flen c -> PIECE kw8a3_hs109 TT -> PIECE kw7a3_hs108 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW8A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 109%nat /\ 109%nat <> 21%nat /\ ch = kw8a3_hs109)).
      { intros h ch Hh. unfold KW8A3_HS, KW8A3_HS0 in Hh. destruct (Nat.eqb h 109) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 109%nat ltac:(lia) (ION.IOT (ION.OFile 16777216 67108864) 32 None None None None) 16777216 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW8A3_HS kw8a3_hs109 HHS Hn kw8a3_IT kw8a3_IT_ok kw7a3_hs108 kw8a3_pl kw8a3_shape kw8a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kw9_step_a3 : 33554432 <= flen c -> PIECE kw9a3_hs110 TT -> PIECE kw8a3_hs109 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KW9A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 110%nat /\ 110%nat <> 21%nat /\ ch = kw9a3_hs110)).
      { intros h ch Hh. unfold KW9A3_HS, KW9A3_HS0 in Hh. destruct (Nat.eqb h 110) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 110%nat ltac:(lia) (ION.IOT (ION.OFile 33554432 67108864) 32 None None None None) 33554432 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
               KW9A3_HS kw9a3_hs110 HHS Hn kw9a3_IT kw9a3_IT_ok kw8a3_hs109 kw9a3_pl kw9a3_shape kw9a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke1_step_a3 : 65536 <= flen c <= 131071 -> PIECE ke1a3_hs201 TT -> PIECE kpa3_hs101 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE1A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 201%nat /\ 201%nat <> 21%nat /\ ch = ke1a3_hs201)).
      { intros h ch Hh. unfold KE1A3_HS, KE1A3_HS0 in Hh. destruct (Nat.eqb h 201) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 201%nat ltac:(lia) (ION.IOT (ION.OFile 65536 131071) 32 (Some (0, 32767)) (Some (0, 131065)) None None) 65536 131071 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 131065 ltac:(lia) ltac:(lia))
               KE1A3_HS ke1a3_hs201 HHS Hn ke1a3_IT ke1a3_IT_ok kpa3_hs101 ke1a3_pl ke1a3_shape ke1a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke2_step_a3 : 131072 <= flen c <= 262143 -> PIECE ke2a3_hs202 TT -> PIECE kw1a3_hs102 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE2A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 202%nat /\ 202%nat <> 21%nat /\ ch = ke2a3_hs202)).
      { intros h ch Hh. unfold KE2A3_HS, KE2A3_HS0 in Hh. destruct (Nat.eqb h 202) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 202%nat ltac:(lia) (ION.IOT (ION.OFile 131072 262143) 32 (Some (0, 32767)) (Some (0, 262137)) None None) 131072 262143 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 262137 ltac:(lia) ltac:(lia))
               KE2A3_HS ke2a3_hs202 HHS Hn ke2a3_IT ke2a3_IT_ok kw1a3_hs102 ke2a3_pl ke2a3_shape ke2a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke3_step_a3 : 262144 <= flen c <= 524287 -> PIECE ke3a3_hs203 TT -> PIECE kw2a3_hs103 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE3A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 203%nat /\ 203%nat <> 21%nat /\ ch = ke3a3_hs203)).
      { intros h ch Hh. unfold KE3A3_HS, KE3A3_HS0 in Hh. destruct (Nat.eqb h 203) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 203%nat ltac:(lia) (ION.IOT (ION.OFile 262144 524287) 32 (Some (0, 32767)) (Some (0, 524281)) None None) 262144 524287 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 524281 ltac:(lia) ltac:(lia))
               KE3A3_HS ke3a3_hs203 HHS Hn ke3a3_IT ke3a3_IT_ok kw2a3_hs103 ke3a3_pl ke3a3_shape ke3a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke4_step_a3 : 524288 <= flen c <= 1048575 -> PIECE ke4a3_hs204 TT -> PIECE kw3a3_hs104 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE4A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 204%nat /\ 204%nat <> 21%nat /\ ch = ke4a3_hs204)).
      { intros h ch Hh. unfold KE4A3_HS, KE4A3_HS0 in Hh. destruct (Nat.eqb h 204) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 204%nat ltac:(lia) (ION.IOT (ION.OFile 524288 1048575) 32 (Some (0, 32767)) (Some (0, 1048569)) None None) 524288 1048575 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 1048569 ltac:(lia) ltac:(lia))
               KE4A3_HS ke4a3_hs204 HHS Hn ke4a3_IT ke4a3_IT_ok kw3a3_hs104 ke4a3_pl ke4a3_shape ke4a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke5_step_a3 : 1048576 <= flen c <= 2097151 -> PIECE ke5a3_hs205 TT -> PIECE kw4a3_hs105 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE5A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 205%nat /\ 205%nat <> 21%nat /\ ch = ke5a3_hs205)).
      { intros h ch Hh. unfold KE5A3_HS, KE5A3_HS0 in Hh. destruct (Nat.eqb h 205) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 205%nat ltac:(lia) (ION.IOT (ION.OFile 1048576 2097151) 32 (Some (0, 32767)) (Some (0, 2097145)) None None) 1048576 2097151 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 2097145 ltac:(lia) ltac:(lia))
               KE5A3_HS ke5a3_hs205 HHS Hn ke5a3_IT ke5a3_IT_ok kw4a3_hs105 ke5a3_pl ke5a3_shape ke5a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke6_step_a3 : 2097152 <= flen c <= 4194303 -> PIECE ke6a3_hs206 TT -> PIECE kw5a3_hs106 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE6A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 206%nat /\ 206%nat <> 21%nat /\ ch = ke6a3_hs206)).
      { intros h ch Hh. unfold KE6A3_HS, KE6A3_HS0 in Hh. destruct (Nat.eqb h 206) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 206%nat ltac:(lia) (ION.IOT (ION.OFile 2097152 4194303) 32 (Some (0, 32767)) (Some (0, 4194297)) None None) 2097152 4194303 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 4194297 ltac:(lia) ltac:(lia))
               KE6A3_HS ke6a3_hs206 HHS Hn ke6a3_IT ke6a3_IT_ok kw5a3_hs106 ke6a3_pl ke6a3_shape ke6a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke7_step_a3 : 4194304 <= flen c <= 8388607 -> PIECE ke7a3_hs207 TT -> PIECE kw6a3_hs107 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE7A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 207%nat /\ 207%nat <> 21%nat /\ ch = ke7a3_hs207)).
      { intros h ch Hh. unfold KE7A3_HS, KE7A3_HS0 in Hh. destruct (Nat.eqb h 207) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 207%nat ltac:(lia) (ION.IOT (ION.OFile 4194304 8388607) 32 (Some (0, 32767)) (Some (0, 8388601)) None None) 4194304 8388607 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 8388601 ltac:(lia) ltac:(lia))
               KE7A3_HS ke7a3_hs207 HHS Hn ke7a3_IT ke7a3_IT_ok kw6a3_hs107 ke7a3_pl ke7a3_shape ke7a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke8_step_a3 : 8388608 <= flen c <= 16777215 -> PIECE ke8a3_hs208 TT -> PIECE kw7a3_hs108 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE8A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 208%nat /\ 208%nat <> 21%nat /\ ch = ke8a3_hs208)).
      { intros h ch Hh. unfold KE8A3_HS, KE8A3_HS0 in Hh. destruct (Nat.eqb h 208) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 208%nat ltac:(lia) (ION.IOT (ION.OFile 8388608 16777215) 32 (Some (0, 32767)) (Some (0, 16777209)) None None) 8388608 16777215 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 16777209 ltac:(lia) ltac:(lia))
               KE8A3_HS ke8a3_hs208 HHS Hn ke8a3_IT ke8a3_IT_ok kw7a3_hs108 ke8a3_pl ke8a3_shape ke8a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke9_step_a3 : 16777216 <= flen c <= 33554431 -> PIECE ke9a3_hs209 TT -> PIECE kw8a3_hs109 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE9A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 209%nat /\ 209%nat <> 21%nat /\ ch = ke9a3_hs209)).
      { intros h ch Hh. unfold KE9A3_HS, KE9A3_HS0 in Hh. destruct (Nat.eqb h 209) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 209%nat ltac:(lia) (ION.IOT (ION.OFile 16777216 33554431) 32 (Some (0, 32767)) (Some (0, 33554425)) None None) 16777216 33554431 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 33554425 ltac:(lia) ltac:(lia))
               KE9A3_HS ke9a3_hs209 HHS Hn ke9a3_IT ke9a3_IT_ok kw8a3_hs109 ke9a3_pl ke9a3_shape ke9a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma ke10_step_a3 : 33554432 <= flen c <= 67108863 -> PIECE ke10a3_hs210 TT -> PIECE kw9a3_hs110 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KE10A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 210%nat /\ 210%nat <> 21%nat /\ ch = ke10a3_hs210)).
      { intros h ch Hh. unfold KE10A3_HS, KE10A3_HS0 in Hh. destruct (Nat.eqb h 210) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 210%nat ltac:(lia) (ION.IOT (ION.OFile 33554432 67108863) 32 (Some (0, 32767)) (Some (0, 67108857)) None None) 33554432 67108863 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 67108857 ltac:(lia) ltac:(lia))
               KE10A3_HS ke10a3_hs210 HHS Hn ke10a3_IT ke10a3_IT_ok kw9a3_hs110 ke10a3_pl ke10a3_shape ke10a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc1_step_a3 : 65536 <= flen c <= 131071 -> PIECE kc1a3_hs301 TT -> PIECE ke1a3_hs201 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC1A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 301%nat /\ 301%nat <> 21%nat /\ ch = kc1a3_hs301)).
      { intros h ch Hh. unfold KC1A3_HS, KC1A3_HS0 in Hh. destruct (Nat.eqb h 301) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 301%nat ltac:(lia) (ION.IOT (ION.OFile 65536 131071) 32 (Some (0, 32767)) (Some (0, 131065)) None None) 65536 131071 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 131065 ltac:(lia) ltac:(lia))
               KC1A3_HS kc1a3_hs301 HHS Hn kc1a3_IT kc1a3_IT_ok ke1a3_hs201 kc1a3_pl kc1a3_shape kc1a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc2_step_a3 : 131072 <= flen c <= 262143 -> PIECE kc2a3_hs302 TT -> PIECE ke2a3_hs202 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC2A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 302%nat /\ 302%nat <> 21%nat /\ ch = kc2a3_hs302)).
      { intros h ch Hh. unfold KC2A3_HS, KC2A3_HS0 in Hh. destruct (Nat.eqb h 302) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 302%nat ltac:(lia) (ION.IOT (ION.OFile 131072 262143) 32 (Some (0, 32767)) (Some (0, 262137)) None None) 131072 262143 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 262137 ltac:(lia) ltac:(lia))
               KC2A3_HS kc2a3_hs302 HHS Hn kc2a3_IT kc2a3_IT_ok ke2a3_hs202 kc2a3_pl kc2a3_shape kc2a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc3_step_a3 : 262144 <= flen c <= 524287 -> PIECE kc3a3_hs303 TT -> PIECE ke3a3_hs203 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC3A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 303%nat /\ 303%nat <> 21%nat /\ ch = kc3a3_hs303)).
      { intros h ch Hh. unfold KC3A3_HS, KC3A3_HS0 in Hh. destruct (Nat.eqb h 303) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 303%nat ltac:(lia) (ION.IOT (ION.OFile 262144 524287) 32 (Some (0, 32767)) (Some (0, 524281)) None None) 262144 524287 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 524281 ltac:(lia) ltac:(lia))
               KC3A3_HS kc3a3_hs303 HHS Hn kc3a3_IT kc3a3_IT_ok ke3a3_hs203 kc3a3_pl kc3a3_shape kc3a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc4_step_a3 : 524288 <= flen c <= 1048575 -> PIECE kc4a3_hs304 TT -> PIECE ke4a3_hs204 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC4A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 304%nat /\ 304%nat <> 21%nat /\ ch = kc4a3_hs304)).
      { intros h ch Hh. unfold KC4A3_HS, KC4A3_HS0 in Hh. destruct (Nat.eqb h 304) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 304%nat ltac:(lia) (ION.IOT (ION.OFile 524288 1048575) 32 (Some (0, 32767)) (Some (0, 1048569)) None None) 524288 1048575 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 1048569 ltac:(lia) ltac:(lia))
               KC4A3_HS kc4a3_hs304 HHS Hn kc4a3_IT kc4a3_IT_ok ke4a3_hs204 kc4a3_pl kc4a3_shape kc4a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc5_step_a3 : 1048576 <= flen c <= 2097151 -> PIECE kc5a3_hs305 TT -> PIECE ke5a3_hs205 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC5A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 305%nat /\ 305%nat <> 21%nat /\ ch = kc5a3_hs305)).
      { intros h ch Hh. unfold KC5A3_HS, KC5A3_HS0 in Hh. destruct (Nat.eqb h 305) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 305%nat ltac:(lia) (ION.IOT (ION.OFile 1048576 2097151) 32 (Some (0, 32767)) (Some (0, 2097145)) None None) 1048576 2097151 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 2097145 ltac:(lia) ltac:(lia))
               KC5A3_HS kc5a3_hs305 HHS Hn kc5a3_IT kc5a3_IT_ok ke5a3_hs205 kc5a3_pl kc5a3_shape kc5a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc6_step_a3 : 2097152 <= flen c <= 4194303 -> PIECE kc6a3_hs306 TT -> PIECE ke6a3_hs206 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC6A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 306%nat /\ 306%nat <> 21%nat /\ ch = kc6a3_hs306)).
      { intros h ch Hh. unfold KC6A3_HS, KC6A3_HS0 in Hh. destruct (Nat.eqb h 306) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 306%nat ltac:(lia) (ION.IOT (ION.OFile 2097152 4194303) 32 (Some (0, 32767)) (Some (0, 4194297)) None None) 2097152 4194303 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 4194297 ltac:(lia) ltac:(lia))
               KC6A3_HS kc6a3_hs306 HHS Hn kc6a3_IT kc6a3_IT_ok ke6a3_hs206 kc6a3_pl kc6a3_shape kc6a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc7_step_a3 : 4194304 <= flen c <= 8388607 -> PIECE kc7a3_hs307 TT -> PIECE ke7a3_hs207 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC7A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 307%nat /\ 307%nat <> 21%nat /\ ch = kc7a3_hs307)).
      { intros h ch Hh. unfold KC7A3_HS, KC7A3_HS0 in Hh. destruct (Nat.eqb h 307) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 307%nat ltac:(lia) (ION.IOT (ION.OFile 4194304 8388607) 32 (Some (0, 32767)) (Some (0, 8388601)) None None) 4194304 8388607 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 8388601 ltac:(lia) ltac:(lia))
               KC7A3_HS kc7a3_hs307 HHS Hn kc7a3_IT kc7a3_IT_ok ke7a3_hs207 kc7a3_pl kc7a3_shape kc7a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc8_step_a3 : 8388608 <= flen c <= 16777215 -> PIECE kc8a3_hs308 TT -> PIECE ke8a3_hs208 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC8A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 308%nat /\ 308%nat <> 21%nat /\ ch = kc8a3_hs308)).
      { intros h ch Hh. unfold KC8A3_HS, KC8A3_HS0 in Hh. destruct (Nat.eqb h 308) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 308%nat ltac:(lia) (ION.IOT (ION.OFile 8388608 16777215) 32 (Some (0, 32767)) (Some (0, 16777209)) None None) 8388608 16777215 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 16777209 ltac:(lia) ltac:(lia))
               KC8A3_HS kc8a3_hs308 HHS Hn kc8a3_IT kc8a3_IT_ok ke8a3_hs208 kc8a3_pl kc8a3_shape kc8a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc9_step_a3 : 16777216 <= flen c <= 33554431 -> PIECE kc9a3_hs309 TT -> PIECE ke9a3_hs209 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC9A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 309%nat /\ 309%nat <> 21%nat /\ ch = kc9a3_hs309)).
      { intros h ch Hh. unfold KC9A3_HS, KC9A3_HS0 in Hh. destruct (Nat.eqb h 309) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 309%nat ltac:(lia) (ION.IOT (ION.OFile 16777216 33554431) 32 (Some (0, 32767)) (Some (0, 33554425)) None None) 16777216 33554431 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 33554425 ltac:(lia) ltac:(lia))
               KC9A3_HS kc9a3_hs309 HHS Hn kc9a3_IT kc9a3_IT_ok ke9a3_hs209 kc9a3_pl kc9a3_shape kc9a3_cert eq_refl ltac:(discriminate)).
    Qed.
    Lemma kc10_step_a3 : 33554432 <= flen c <= 67108863 -> PIECE kc10a3_hs310 TT -> PIECE ke10a3_hs210 TT.
    Proof.
      intros HF Hn.
      assert (HHS : forall h ch, KC10A3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 310%nat /\ 310%nat <> 21%nat /\ ch = kc10a3_hs310)).
      { intros h ch Hh. unfold KC10A3_HS, KC10A3_HS0 in Hh. destruct (Nat.eqb h 310) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      exact (stepk_piece TT TT_agree TT_nil 310%nat ltac:(lia) (ION.IOT (ION.OFile 33554432 67108863) 32 (Some (0, 32767)) (Some (0, 67108857)) None None) 33554432 67108863 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_big _ 67108857 ltac:(lia) ltac:(lia))
               KC10A3_HS kc10a3_hs310 HHS Hn kc10a3_IT kc10a3_IT_ok ke10a3_hs210 kc10a3_pl kc10a3_shape kc10a3_cert eq_refl ltac:(discriminate)).
    Qed.
  End Chain.
  (* [comment removed for export] *)
  Definition fi_start_a3 (k : Z) : acs := if k =? 1 then kc1a3_hs301 else if k =? 2 then kc2a3_hs302 else if k =? 3 then kc3a3_hs303 else if k =? 4 then kc4a3_hs304 else if k =? 5 then kc5a3_hs305 else if k =? 6 then kc6a3_hs306 else if k =? 7 then kc7a3_hs307 else if k =? 8 then kc8a3_hs308 else if k =? 9 then kc9a3_hs309 else kc10a3_hs310.

  Theorem kge1_a3 : forall (TT : env -> Fs.Fs -> TSet), t_agree TT -> (forall E fs0, TT E fs0 []) ->
    forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (fi_start_a3 k) TT ->
    PIECE c3a3_hs98k (fun E fs' => t_alt2 (T_cannot argv1 fs') (TT E fs')).
  Proof.
    intros TT TA TN k Hk HF HP.
    assert (HK : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
    destruct HK as [HK | [HK | [HK | [HK | [HK | [HK | [HK | [HK | [HK | HK]]]]]]]]]; subst k; cbn in HF; unfold fi_start_a3 in HP; cbn in HP.
    - apply (kp_piece_a3 TT TA TN); [lia|]. exact (ke1_step_a3 TT TA TN ltac:(lia) (kc1_step_a3 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_a3 TT TA TN); [lia|]. apply (kw1_step_a3 TT TA TN); [lia|]. exact (ke2_step_a3 TT TA TN ltac:(lia) (kc2_step_a3 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_a3 TT TA TN); [lia|]. apply (kw1_step_a3 TT TA TN); [lia|]. apply (kw2_step_a3 TT TA TN); [lia|]. exact (ke3_step_a3 TT TA TN ltac:(lia) (kc3_step_a3 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_a3 TT TA TN); [lia|]. apply (kw1_step_a3 TT TA TN); [lia|]. apply (kw2_step_a3 TT TA TN); [lia|]. apply (kw3_step_a3 TT TA TN); [lia|]. exact (ke4_step_a3 TT TA TN ltac:(lia) (kc4_step_a3 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_a3 TT TA TN); [lia|]. apply (kw1_step_a3 TT TA TN); [lia|]. apply (kw2_step_a3 TT TA TN); [lia|]. apply (kw3_step_a3 TT TA TN); [lia|]. apply (kw4_step_a3 TT TA TN); [lia|]. exact (ke5_step_a3 TT TA TN ltac:(lia) (kc5_step_a3 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_a3 TT TA TN); [lia|]. apply (kw1_step_a3 TT TA TN); [lia|]. apply (kw2_step_a3 TT TA TN); [lia|]. apply (kw3_step_a3 TT TA TN); [lia|]. apply (kw4_step_a3 TT TA TN); [lia|]. apply (kw5_step_a3 TT TA TN); [lia|]. exact (ke6_step_a3 TT TA TN ltac:(lia) (kc6_step_a3 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_a3 TT TA TN); [lia|]. apply (kw1_step_a3 TT TA TN); [lia|]. apply (kw2_step_a3 TT TA TN); [lia|]. apply (kw3_step_a3 TT TA TN); [lia|]. apply (kw4_step_a3 TT TA TN); [lia|]. apply (kw5_step_a3 TT TA TN); [lia|]. apply (kw6_step_a3 TT TA TN); [lia|]. exact (ke7_step_a3 TT TA TN ltac:(lia) (kc7_step_a3 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_a3 TT TA TN); [lia|]. apply (kw1_step_a3 TT TA TN); [lia|]. apply (kw2_step_a3 TT TA TN); [lia|]. apply (kw3_step_a3 TT TA TN); [lia|]. apply (kw4_step_a3 TT TA TN); [lia|]. apply (kw5_step_a3 TT TA TN); [lia|]. apply (kw6_step_a3 TT TA TN); [lia|]. apply (kw7_step_a3 TT TA TN); [lia|]. exact (ke8_step_a3 TT TA TN ltac:(lia) (kc8_step_a3 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_a3 TT TA TN); [lia|]. apply (kw1_step_a3 TT TA TN); [lia|]. apply (kw2_step_a3 TT TA TN); [lia|]. apply (kw3_step_a3 TT TA TN); [lia|]. apply (kw4_step_a3 TT TA TN); [lia|]. apply (kw5_step_a3 TT TA TN); [lia|]. apply (kw6_step_a3 TT TA TN); [lia|]. apply (kw7_step_a3 TT TA TN); [lia|]. apply (kw8_step_a3 TT TA TN); [lia|]. exact (ke9_step_a3 TT TA TN ltac:(lia) (kc9_step_a3 TT TA TN ltac:(lia) HP)).
    - apply (kp_piece_a3 TT TA TN); [lia|]. apply (kw1_step_a3 TT TA TN); [lia|]. apply (kw2_step_a3 TT TA TN); [lia|]. apply (kw3_step_a3 TT TA TN); [lia|]. apply (kw4_step_a3 TT TA TN); [lia|]. apply (kw5_step_a3 TT TA TN); [lia|]. apply (kw6_step_a3 TT TA TN); [lia|]. apply (kw7_step_a3 TT TA TN); [lia|]. apply (kw8_step_a3 TT TA TN); [lia|]. apply (kw9_step_a3 TT TA TN); [lia|]. exact (ke10_step_a3 TT TA TN ltac:(lia) (kc10_step_a3 TT TA TN ltac:(lia) HP)).
  Qed.

  (* [comment removed for export] *)
  Section Refused.
    Hypothesis H_FER : FXHOLE kra3_hs230 feendra3.
    Lemma xr_piece_a3 : PIECE feendra3 T_exit2.
    Proof.
      intros E R FULL m HC.
      exact (CHK1 (fun _ : nat => @None acs) (fun _ _ _ => t_nil) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl)
               (fun h ch Hh => ltac:(discriminate Hh)) xra3_IT xra3_IT_ok 0%nat true 3000%nat 400000%nat xu_plan feendra3 xra3_shape xra3_cert E R FULL m HC).
    Qed.
    Lemma fer_piece_a3 : PIECE kra3_hs230 T_exit2.
    Proof. apply (hole_compose SV argH ISP fs kra3_hs230 feendra3 T_exit2); [vm_compute; lia | intros E E' fs0 _; reflexivity | exact H_FER | exact xr_piece_a3]. Qed.
    Let TR : env -> Fs.Fs -> TSet := fun _ fs' => T_lit refused_lit fs'.
    Lemma TR_agree : t_agree TR. Proof. intros E E' fs0 _. reflexivity. Qed.
    Lemma TR_nil : forall E fs0, TR E fs0 []. Proof. intros E fs0. unfold TR, T_lit. apply t_emit_has_nil. Qed.
    Lemma kr_piece_a3 : 67108864 <= flen c -> PIECE kw9a3_hs110 TR.
    Proof.
      intros HF E R FULL m HC.
      assert (HHS : forall h ch, KRA3_HS h = Some ch -> (h = 21%nat /\ ch = c4a3_hs21) \/ (h = 230%nat /\ 230%nat <> 21%nat /\ ch = kra3_hs230)).
      { intros h ch Hh. unfold KRA3_HS, KRA3_HS0 in Hh. destruct (Nat.eqb h 230) eqn:HN; [|discriminate Hh]. apply Nat.eqb_eq in HN. diet_injection Hh. right. split; [exact HN | split; [discriminate | reflexivity]]. }
      pose proof (stepk_sd T_exit2 (fun E0 E1 fs0 _ => eq_refl) (fun E0 fs0 => CXS.t_exit_has_nil _ fs0) 230%nat ltac:(lia) (ION.IOT (ION.OFile 67108864 67108864) 32 None None None None) 67108864 67108864 eq_refl eq_refl ltac:(pose proof flen_cap'; lia) (hdr_ok_simple _)
                    KRA3_HS kra3_hs230 HHS fer_piece_a3 kra3_IT kra3_IT_ok kw9a3_hs110 kra3_pl kra3_shape kra3_cert E R FULL m HC) as RZ.
      rewrite kra3_shape_eq in RZ. eapply crz_conseq; [exact RZ|]. cbn [sd].
      rewrite (HOLESK_hN T_exit2 230%nat ltac:(lia) ltac:(discriminate)). unfold TR. exact (leafL E (m_fs m) refused_lit).
    Qed.
    Theorem refused_a3 : 67108864 <= flen c -> PIECE c3a3_hs98k (fun _ fs' => T_hdr refused_lit argv1 fs').
    Proof.
      intros HF. unfold T_hdr. apply (kp_piece_a3 TR TR_agree TR_nil); [lia|].
      apply (kw1_step_a3 TR TR_agree TR_nil); [lia|]. apply (kw2_step_a3 TR TR_agree TR_nil); [lia|]. apply (kw3_step_a3 TR TR_agree TR_nil); [lia|]. apply (kw4_step_a3 TR TR_agree TR_nil); [lia|]. apply (kw5_step_a3 TR TR_agree TR_nil); [lia|]. apply (kw6_step_a3 TR TR_agree TR_nil); [lia|]. apply (kw7_step_a3 TR TR_agree TR_nil); [lia|]. apply (kw8_step_a3 TR TR_agree TR_nil); [lia|]. apply (kw9_step_a3 TR TR_agree TR_nil); [lia|]. exact (kr_piece_a3 HF).
    Qed.
  End Refused.

End Kge1A3.
