(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefPrintfLib LibTail RefMemcpyLib
  LazyRestrict LazySR LazyFdNodes LazySym.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import RefExitBase RefStdioDefs AsLazyRun AsStdioWrite AsStdioCall AsScLib
  AsPrintfFirst AsExitCas AsCarryKeep.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsExit Require Import FeDefs FeRun AsUnreg AsExitDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition x_regions : list sregion :=
  [(SA (EVar 0) (-1024), 1024); (SA (ELit 0) 0xc01ce0, 24); (SA (ELit 0) 0xc01f00, 4); (SA (ELit 0) 0x6a7290, 1);
   (SA (ELit 0) 0x6a7240, 8); (SA (ELit 0) 0x5ede88, 232)]%Z.

Section Exit.
  Variable sp0 : word.
  Variables (L S Zr : list (word * word)).

  Definition x_regions_w : list (word * Z) :=
    [(Z_to_bv 64 (bv_unsigned sp0 - 1024), 1024%Z); (Z_to_bv 64 0xc01ce0, 24%Z); (Z_to_bv 64 0xc01f00, 4%Z); (Z_to_bv 64 0x6a7290, 1%Z);
     (Z_to_bv 64 0x6a7240, 8%Z); (Z_to_bv 64 0x5ede88, 232%Z)].

  Lemma x_regions_denot : forall vals, vals_ev vals 0 = sp0 -> (ASP_LO <= bv_unsigned sp0)%Z ->
    map (rdenot (ENV vals)) x_regions = x_regions_w.
  Proof.
    intros vals P0 Hlo. unfold ASP_LO in Hlo. unfold x_regions, x_regions_w, rdenot, estart. cbn [map fst snd a_base a_off edenot ev ENV].
    rewrite P0. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. repeat f_equal; lia.
  Qed.

  Lemma x_regions_flat : forall vals, vals_ev vals 0 = sp0 ->
    (ASP_LO <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= ASP_HI)%Z -> regions_flat (ENV vals) x_regions.
  Proof.
    intros vals P0 Hlo Hhi r Hr. unfold ASP_LO, ASP_HI in *. unfold x_regions in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV];
      rewrite ?P0; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma x_regions_buf : forall (i : Z), (0 <= i < 1024)%Z -> (ASP_LO <= bv_unsigned sp0)%Z ->
    outside (Z_to_bv 64 (0xc027a8 + i)) x_regions_w.
  Proof.
    intros i Hi Hlo. unfold ASP_LO in Hlo. pose proof (u64_range sp0). unfold x_regions_w. cbn [outside]. unfold in_rng.
    rewrite !u64_lit by lia. lia.
  Qed.
  Lemma fe_buf : forall (i spz : Z), (0 <= i < 1024)%Z -> (ASP_LO <= spz)%Z -> ~ fe_written spz (bv_unsigned (Z_to_bv 64 (0xc027a8 + i))).
  Proof.
    intros i spz Hi Hlo. unfold ASP_LO in Hlo. rewrite u64_lit by lia. unfold fe_written, FE_STK, FE_SH_LO, FE_SH_HI, FE_WR_PAGES. cbn [In].
    intros [A|[A|A]]; [lia | | lia].
    assert (E : ((12593064 + i) / 4096 = 3023)%Z) by (Z.div_mod_to_equations; lia). rewrite E in A. lia.
  Qed.

  (* [comment removed for export] *)
  Definition fe_regions_w (spz : Z) : list (word * Z) :=
    [(Z_to_bv 64 (spz - 512), 512%Z); (Z_to_bv 64 0x6a8000, 4096%Z); (Z_to_bv 64 0xbdd000, 4096%Z); (Z_to_bv 64 0xbdf000, 4096%Z);
     (Z_to_bv 64 0xbe1000, 4096%Z); (Z_to_bv 64 FE_SH_LO, (FE_SH_HI - FE_SH_LO)%Z)].
  Lemma fe_frame : forall (M M' : word -> option byte) (spz : Z), (4294967296 <= spz <= ASP_HI)%Z ->
    (forall x : word, ~ fe_written spz (bv_unsigned x) -> M' x = M x) -> mem_grows M M' -> frame_mod M M' (fe_regions_w spz).
  Proof.
    intros M M' spz Hsp Hfr Hg. split; [|exact Hg]. intros x Hout. apply Hfr. intros Hw.
    unfold ASP_LO, ASP_HI in Hsp. pose proof (u64_range x) as Hx.
    unfold fe_regions_w in Hout. cbn [outside] in Hout. unfold in_rng, FE_SH_LO, FE_SH_HI in Hout. rewrite !u64_lit in Hout by lia.
    unfold fe_written, FE_STK, FE_SH_LO, FE_SH_HI, FE_WR_PAGES in Hw. cbn [In] in Hw.
    destruct Hw as [Hw|[Hw|Hw]]; [lia | | lia].
    destruct Hw as [Hw|[Hw|[Hw|[Hw|[]]]]];
      match type of Hw with (?p = _)%Z => assert (p * 4096 <= bv_unsigned x < p * 4096 + 4096)%Z by (rewrite Hw; Z.div_mod_to_equations; lia) end; lia.
  Qed.
  Lemma x_regions_bufF : forall (i spz : Z), (0 <= i < 1024)%Z -> (ASP_LO <= bv_unsigned sp0)%Z -> (4294967296 <= spz <= ASP_HI)%Z ->
    outside (Z_to_bv 64 (0xc027a8 + i)) (x_regions_w ++ [(Z_to_bv 64 0xc01f00, 4%Z)] ++ x_regions_w ++ fe_regions_w spz ++ x_regions_w).
  Proof.
    intros i spz Hi Hlo Hspz. unfold ASP_LO, ASP_HI in *. pose proof (u64_range sp0).
    repeat (apply outside_app; split);
      lazymatch goal with
      | |- outside _ x_regions_w => apply x_regions_buf; [lia | unfold ASP_LO; lia]
      | |- _ => unfold fe_regions_w; cbn [outside]; unfold in_rng, FE_SH_LO, FE_SH_HI; rewrite ?u64_lit by lia; repeat split; first [exact I | lia]
      end.
  Qed.

  (* [comment removed for export] *)
  Lemma frame_wbytes_lit : forall m (a : Z) w (v : word), (0 <= a < 2^64)%Z -> (a + Z.of_nat w <= 2^64)%Z ->
    frame_mod m (wbytes m (Z_to_bv 64 a) (word_to_le_bytes w v)) [(Z_to_bv 64 a, Z.of_nat w)].
  Proof.
    intros m a w v Ha Hw. pose proof (frame_mod_wbytes m (Z_to_bv 64 a) (word_to_le_bytes w v)) as F.
    rewrite length_N_to_le_bytes in F. apply F. rewrite u64_lit by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma one_carry_ok : forall E M kn a w v (x : word) kn' hs',
    carry [SE (SA (ELit 0) a) w v] kn [] = (kn', [], hs') ->
    know_ok RSEGS E M kn -> edenot E v = x -> (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat w <= 2 ^ 64)%Z -> (w <= 8)%nat ->
    know_ok RSEGS E (wbytes M (Z_to_bv 64 a) (word_to_le_bytes w x)) kn'.
  Proof.
    intros E M kn a w v x kn' hs' Hc HK Hv Ha Hw Hw8.
    replace (wbytes M (Z_to_bv 64 a) (word_to_le_bytes w x)) with (mem_denot E M [SE (SA (ELit 0) a) w v]).
    - eapply carry_after; [exact Hc | | exact HK | constructor].
      cbn [log_flat]. split; [exact Hw8|]. split; [| exact I]. unfold flat, estart. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
    - cbn [mem_denot]. rewrite adenot_lit0, Hv. reflexivity.
  Qed.

  Theorem ax_sound_1c : forall vals R M msF mo (code : word),
    length vals = NV -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = code ->
    regs_ok (ENV vals) x_sr R -> know_ok RSEGS (ENV vals) M (ax_kn false false false) ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 AEXIT) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs mo)).
  Proof.
    intros vals R M msF mo code HL P0 P2 HR HK OK RS.
    pose proof (know_nth RSEGS _ _ (ax_kn false false false) 1%nat _ HK eq_refl) as Hrg. cbn [kentry_ok edenot ev ENV] in Hrg. rewrite P0 in Hrg.
    unfold ASP_LO, ASP_HI in Hrg. pose proof (u64_range sp0) as Hsp.
    pose proof x_itinerary_1c as (PC1 & SC1 & CC1 & CC2i & KR1 & PC2 & SC2 & CC2 & UC & PC3 & SC3 & CC3).
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr XFUEL XSTOPS scr0 AEXIT x_sr (ax_kn false false false) NV (fst (fst rX11c)) (snd (fst rX11c)) (snd rX11c)
              (fst (fst cX11c)) (snd (fst cX11c)) (snd cX11c) (ENV vals) M (seg_rom RSEGS) R msF mo);
      [ vm_cast_no_check (@eq_refl _ rX11c) | vm_cast_no_check (@eq_refl _ cX11c)
      | exact HR | exact HK | rewrite SC1; constructor | rewrite CC1; constructor | exact OK | exact RS | ].
    clear HR HK RS OK. intros R1 M1 msF1 mo1 HR HK EQ1 LF1 OK1 SB1 HS1 RS1.
    clear EQ1 LF1.
    change (s_regs (fst (fst rX11c))) with srX11c in HR. change (fst (fst cX11c)) with knX11c in HK. rewrite PC1 in RS1.
    (* [comment removed for export] *)
    pose proof (kread_rdn RSEGS (ENV vals) M1 knX11c (ELit 0) 0xc01f00 4 _ HK KR1 ltac:(lia) ltac:(lia)
                  ltac:(unfold flat, estart; cbn [a_base a_off edenot]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia)) as Mlock.
    rewrite adenot_lit0 in Mlock. cbn [edenot] in Mlock.
    eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact OK1 | exact RS1 | |].
    { replace (Z_to_bv 64 AEXIT_LR) with (0x55e57c : word) by (apply bv_eq; reflexivity).
      apply (cas_exit_lock R1 M1 (seg_rom RSEGS) (getr R1 12)); [regv HR (13:reg); reflexivity | regv HR (11:reg); reflexivity | reflexivity | exact Mlock]. }
    clear Mlock. intros msF2 mo2 OK2 SB2 HS2 RS2.
    assert (HR2 : regs_ok (ENV vals) srX2i1c (regupd (regupd R1 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 0))).
    { change srX2i1c with (sr_upd (sr_upd srX11c (ridx 14) (ELit 0%Z)) (ridx 15) (ELit 0%Z)).
      apply regs_ok_set; [apply regs_ok_set; [exact HR | discriminate | reflexivity] | discriminate | reflexivity]. }
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M1 (Z_to_bv 64 0xc01f00) (word_to_le_bytes 4 (getr R1 12))) knX2i1c).
    { change knX2i1c with (fst (fst cX2i1c)).
      apply (one_carry_ok (ENV vals) M1 knX11c 0xc01f00 4 (sr_get srX11c 12) (getr R1 12) (fst (fst cX2i1c)) (snd cX2i1c));
        [ vm_cast_no_check (@eq_refl _ cX2i1c) | exact HK | symmetry; apply HR | lia | cbn; lia | lia ]. }
    
    clear HR HK. replace (0x55e588 : word) with (Z_to_bv 64 AEXIT_CAS_RET) in RS2 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr XFUEL XSTOPS scr0 AEXIT_CAS_RET srX2i1c knX2i1c NV (fst (fst rX21c)) (snd (fst rX21c)) (snd rX21c)
              (fst (fst cX21c)) (snd (fst cX21c)) (snd cX21c) (ENV vals) _ (seg_rom RSEGS) _ msF2 mo2);
      [ vm_cast_no_check (@eq_refl _ rX21c) | vm_cast_no_check (@eq_refl _ cX21c)
      | exact HR2 | exact HK2 | rewrite SC2; constructor | rewrite CC2; constructor | exact OK2 | exact RS2 | ].
    clear HR2 HK2 RS2 OK2. intros R2 M2 msF3 mo3 HR HK EQ2 LF2 OK3 SB3 HS3 RS3.
    clear EQ2 LF2.
    change (s_regs (fst (fst rX21c))) with srX21c in HR. change (fst (fst cX21c)) with knX21c in HK. rewrite PC2 in RS3.
    (* [comment removed for export] *)
    eapply (unreg_call_sound L S Zr vals (blobs_ev []) srX21c knX21c R2 M2 msF3 mo3 uX1c);
      [ exact HR | exact HK | rewrite HL; exact UC | exact OK3 | exact RS3 | ].
    clear HR HK. intros R3 M3 msF4 mo4 HR HK FR3 GR3 OK4 SB4 HS4 RS4.
    set (vals' := vals ++ junk_vals R3) in *.
    change (Env (vals_ev vals') (blobs_ev [])) with (ENV vals') in HR, HK.
    clear FR3 GR3.
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr XFUEL XSTOPS scr0 FE_RET (uc_sr uX1c) (uc_kn uX1c) 73 (fst (fst rX31c)) (snd (fst rX31c)) (snd rX31c)
              (fst (fst cX31c)) (snd (fst cX31c)) (snd cX31c) (ENV vals') M3 (seg_rom RSEGS) R3 msF4 mo4);
      [ vm_cast_no_check (@eq_refl _ rX31c) | vm_cast_no_check (@eq_refl _ cX31c)
      | exact HR | exact HK | rewrite SC3; constructor | rewrite CC3; constructor | exact OK4 | exact RS4 | ].
    clear HR HK RS4 OK4. intros R4 M4 msF5 mo5 HR HK EQ4 LF4 OK5 SB5 HS5 RS5.
    clear EQ4 LF4.
    change (s_regs (fst (fst rX31c))) with srX31c in HR. change (fst (fst cX31c)) with knX31c in HK. rewrite PC3 in RS5.
    rewrite <- (same_but_materialized_fs _ _ SB1), <- (same_but_materialized_fs _ _ SB2), <- (same_but_materialized_fs _ _ SB3),
            <- (same_but_materialized_fs _ _ SB4), <- (same_but_materialized_fs _ _ SB5).
    eapply (rz_exit_at_lazy RSEGS L S Zr msF5 R4 (Z_to_bv 64 AEXIT_ECALL) M4 (seg_rom RSEGS) mo5 ECALLW code);
      [ vm_compute; reflexivity | apply is_ecall_ECALLW | exact OK5 | exact RS5 | reflexivity
      | left; regv HR (17:reg); reflexivity | regv HR (10:reg) ].
    change (edenot (ENV vals') (EVar 2)) with (vals_ev vals' 2). subst vals'. rewrite vals_ev_app_l by (rewrite HL; unfold NV; lia). exact P2.
  Qed.

  Theorem ax_sound_2zc : forall vals R M msF mo (code : word),
    length vals = NV -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = code ->
    regs_ok (ENV vals) x_sr R -> know_ok RSEGS (ENV vals) M (ax_kn true false false) ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 AEXIT) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs mo)).
  Proof.
    intros vals R M msF mo code HL P0 P2 HR HK OK RS.
    pose proof (know_nth RSEGS _ _ (ax_kn true false false) 1%nat _ HK eq_refl) as Hrg. cbn [kentry_ok edenot ev ENV] in Hrg. rewrite P0 in Hrg.
    unfold ASP_LO, ASP_HI in Hrg. pose proof (u64_range sp0) as Hsp.
    pose proof x_itinerary_2zc as (PC1 & SC1 & CC1 & CC2i & KR1 & PC2 & SC2 & CC2 & UC & PC3 & SC3 & CC3).
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr XFUEL XSTOPS scr0 AEXIT x_sr (ax_kn true false false) NV (fst (fst rX12zc)) (snd (fst rX12zc)) (snd rX12zc)
              (fst (fst cX12zc)) (snd (fst cX12zc)) (snd cX12zc) (ENV vals) M (seg_rom RSEGS) R msF mo);
      [ vm_cast_no_check (@eq_refl _ rX12zc) | vm_cast_no_check (@eq_refl _ cX12zc)
      | exact HR | exact HK | rewrite SC1; constructor | rewrite CC1; constructor | exact OK | exact RS | ].
    clear HR HK RS OK. intros R1 M1 msF1 mo1 HR HK EQ1 LF1 OK1 SB1 HS1 RS1.
    clear EQ1 LF1.
    change (s_regs (fst (fst rX12zc))) with srX12zc in HR. change (fst (fst cX12zc)) with knX12zc in HK. rewrite PC1 in RS1.
    (* [comment removed for export] *)
    pose proof (kread_rdn RSEGS (ENV vals) M1 knX12zc (ELit 0) 0xc01f00 4 _ HK KR1 ltac:(lia) ltac:(lia)
                  ltac:(unfold flat, estart; cbn [a_base a_off edenot]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia)) as Mlock.
    rewrite adenot_lit0 in Mlock. cbn [edenot] in Mlock.
    eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact OK1 | exact RS1 | |].
    { replace (Z_to_bv 64 AEXIT_LR) with (0x55e57c : word) by (apply bv_eq; reflexivity).
      apply (cas_exit_lock R1 M1 (seg_rom RSEGS) (getr R1 12)); [regv HR (13:reg); reflexivity | regv HR (11:reg); reflexivity | reflexivity | exact Mlock]. }
    clear Mlock. intros msF2 mo2 OK2 SB2 HS2 RS2.
    assert (HR2 : regs_ok (ENV vals) srX2i2zc (regupd (regupd R1 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 0))).
    { change srX2i2zc with (sr_upd (sr_upd srX12zc (ridx 14) (ELit 0%Z)) (ridx 15) (ELit 0%Z)).
      apply regs_ok_set; [apply regs_ok_set; [exact HR | discriminate | reflexivity] | discriminate | reflexivity]. }
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M1 (Z_to_bv 64 0xc01f00) (word_to_le_bytes 4 (getr R1 12))) knX2i2zc).
    { change knX2i2zc with (fst (fst cX2i2zc)).
      apply (one_carry_ok (ENV vals) M1 knX12zc 0xc01f00 4 (sr_get srX12zc 12) (getr R1 12) (fst (fst cX2i2zc)) (snd cX2i2zc));
        [ vm_cast_no_check (@eq_refl _ cX2i2zc) | exact HK | symmetry; apply HR | lia | cbn; lia | lia ]. }
    
    clear HR HK. replace (0x55e588 : word) with (Z_to_bv 64 AEXIT_CAS_RET) in RS2 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr XFUEL XSTOPS scr0 AEXIT_CAS_RET srX2i2zc knX2i2zc NV (fst (fst rX22zc)) (snd (fst rX22zc)) (snd rX22zc)
              (fst (fst cX22zc)) (snd (fst cX22zc)) (snd cX22zc) (ENV vals) _ (seg_rom RSEGS) _ msF2 mo2);
      [ vm_cast_no_check (@eq_refl _ rX22zc) | vm_cast_no_check (@eq_refl _ cX22zc)
      | exact HR2 | exact HK2 | rewrite SC2; constructor | rewrite CC2; constructor | exact OK2 | exact RS2 | ].
    clear HR2 HK2 RS2 OK2. intros R2 M2 msF3 mo3 HR HK EQ2 LF2 OK3 SB3 HS3 RS3.
    clear EQ2 LF2.
    change (s_regs (fst (fst rX22zc))) with srX22zc in HR. change (fst (fst cX22zc)) with knX22zc in HK. rewrite PC2 in RS3.
    (* [comment removed for export] *)
    eapply (unreg_call_sound L S Zr vals (blobs_ev []) srX22zc knX22zc R2 M2 msF3 mo3 uX2zc);
      [ exact HR | exact HK | rewrite HL; exact UC | exact OK3 | exact RS3 | ].
    clear HR HK. intros R3 M3 msF4 mo4 HR HK FR3 GR3 OK4 SB4 HS4 RS4.
    set (vals' := vals ++ junk_vals R3) in *.
    change (Env (vals_ev vals') (blobs_ev [])) with (ENV vals') in HR, HK.
    clear FR3 GR3.
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr XFUEL XSTOPS scr0 FE_RET (uc_sr uX2zc) (uc_kn uX2zc) 73 (fst (fst rX32zc)) (snd (fst rX32zc)) (snd rX32zc)
              (fst (fst cX32zc)) (snd (fst cX32zc)) (snd cX32zc) (ENV vals') M3 (seg_rom RSEGS) R3 msF4 mo4);
      [ vm_cast_no_check (@eq_refl _ rX32zc) | vm_cast_no_check (@eq_refl _ cX32zc)
      | exact HR | exact HK | rewrite SC3; constructor | rewrite CC3; constructor | exact OK4 | exact RS4 | ].
    clear HR HK RS4 OK4. intros R4 M4 msF5 mo5 HR HK EQ4 LF4 OK5 SB5 HS5 RS5.
    clear EQ4 LF4.
    change (s_regs (fst (fst rX32zc))) with srX32zc in HR. change (fst (fst cX32zc)) with knX32zc in HK. rewrite PC3 in RS5.
    rewrite <- (same_but_materialized_fs _ _ SB1), <- (same_but_materialized_fs _ _ SB2), <- (same_but_materialized_fs _ _ SB3),
            <- (same_but_materialized_fs _ _ SB4), <- (same_but_materialized_fs _ _ SB5).
    eapply (rz_exit_at_lazy RSEGS L S Zr msF5 R4 (Z_to_bv 64 AEXIT_ECALL) M4 (seg_rom RSEGS) mo5 ECALLW code);
      [ vm_compute; reflexivity | apply is_ecall_ECALLW | exact OK5 | exact RS5 | reflexivity
      | left; regv HR (17:reg); reflexivity | regv HR (10:reg) ].
    change (edenot (ENV vals') (EVar 2)) with (vals_ev vals' 2). subst vals'. rewrite vals_ev_app_l by (rewrite HL; unfold NV; lia). exact P2.
  Qed.

  Lemma x_cov1_2zf : log_covered x_regions (s_log (fst (fst rX12zf))) = true. Proof. vm_compute. reflexivity. Qed.
  Lemma x_cov2_2zf : log_covered x_regions (s_log (fst (fst rX22zf))) = true. Proof. vm_compute. reflexivity. Qed.
  Lemma x_cov3_2zf : log_covered x_regions (s_log (fst (fst rX32zf))) = true. Proof. vm_compute. reflexivity. Qed.

  Theorem ax_sound_2zf : forall vals R M msF mo (pending : list byte) (code : word),
    length vals = NV -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = code ->
    regs_ok (ENV vals) x_sr R -> know_ok RSEGS (ENV vals) M (ax_kn true false true) ->
    (* [comment removed for export] *)
    (bv_unsigned (vals_ev vals 4) - 0xc027a8 = Z.of_nat (length pending))%Z ->
    (Z.of_nat (length pending) <= 1024)%Z ->
    rdn RSEGS M (Z_to_bv 64 0xc027a8) (length pending) = Some pending ->
    fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 AEXIT) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (map (WriteEv (Z_to_bv 64 1)) pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs mo))).
  Proof.
    intros vals R M msF mo pending code HL P0 P2 HR HK LEN MAX RDP Hfd1 OK RS.
    pose proof (know_nth RSEGS _ _ (ax_kn true false true) 1%nat _ HK eq_refl) as Hrg. cbn [kentry_ok edenot ev ENV] in Hrg. rewrite P0 in Hrg.
    pose proof (know_nth RSEGS _ _ (ax_kn true false true) 25%nat _ HK eq_refl) as Hwp. cbn [kentry_ok edenot ev ENV] in Hwp.
    unfold ASP_LO, ASP_HI in Hrg. pose proof (u64_range sp0) as Hsp.
    pose proof (x_regions_flat vals P0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF.
    pose proof (x_regions_denot vals P0 ltac:(unfold ASP_LO; lia)) as RD.
    pose proof x_itinerary_2zf as (PC1 & SC1 & CC1 & CC2i & KR1 & PC2 & SC2 & CC2 & UC & PC3 & SC3 & CC3 & SCALL & PC4 & SC4 & CC4).
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr XFUEL XSTOPS scr0 AEXIT x_sr (ax_kn true false true) NV (fst (fst rX12zf)) (snd (fst rX12zf)) (snd rX12zf)
              (fst (fst cX12zf)) (snd (fst cX12zf)) (snd cX12zf) (ENV vals) M (seg_rom RSEGS) R msF mo);
      [ vm_cast_no_check (@eq_refl _ rX12zf) | vm_cast_no_check (@eq_refl _ cX12zf)
      | exact HR | exact HK | rewrite SC1; constructor | rewrite CC1; constructor | exact OK | exact RS | ].
    clear HR HK RS OK. intros R1 M1 msF1 mo1 HR HK EQ1 LF1 OK1 SB1 HS1 RS1.
    pose proof (log_covered_frame (ENV vals) M x_regions _ x_cov1_2zf RF LF1) as F1. rewrite <- EQ1, RD in F1. clear EQ1 LF1.
    change (s_regs (fst (fst rX12zf))) with srX12zf in HR. change (fst (fst cX12zf)) with knX12zf in HK. rewrite PC1 in RS1.
    (* [comment removed for export] *)
    pose proof (kread_rdn RSEGS (ENV vals) M1 knX12zf (ELit 0) 0xc01f00 4 _ HK KR1 ltac:(lia) ltac:(lia)
                  ltac:(unfold flat, estart; cbn [a_base a_off edenot]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia)) as Mlock.
    rewrite adenot_lit0 in Mlock. cbn [edenot] in Mlock.
    eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact OK1 | exact RS1 | |].
    { replace (Z_to_bv 64 AEXIT_LR) with (0x55e57c : word) by (apply bv_eq; reflexivity).
      apply (cas_exit_lock R1 M1 (seg_rom RSEGS) (getr R1 12)); [regv HR (13:reg); reflexivity | regv HR (11:reg); reflexivity | reflexivity | exact Mlock]. }
    clear Mlock. intros msF2 mo2 OK2 SB2 HS2 RS2.
    assert (HR2 : regs_ok (ENV vals) srX2i2zf (regupd (regupd R1 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 0))).
    { change srX2i2zf with (sr_upd (sr_upd srX12zf (ridx 14) (ELit 0%Z)) (ridx 15) (ELit 0%Z)).
      apply regs_ok_set; [apply regs_ok_set; [exact HR | discriminate | reflexivity] | discriminate | reflexivity]. }
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M1 (Z_to_bv 64 0xc01f00) (word_to_le_bytes 4 (getr R1 12))) knX2i2zf).
    { change knX2i2zf with (fst (fst cX2i2zf)).
      apply (one_carry_ok (ENV vals) M1 knX12zf 0xc01f00 4 (sr_get srX12zf 12) (getr R1 12) (fst (fst cX2i2zf)) (snd cX2i2zf));
        [ vm_cast_no_check (@eq_refl _ cX2i2zf) | exact HK | symmetry; apply HR | lia | cbn; lia | lia ]. }
    pose proof (frame_wbytes_lit M1 0xc01f00 4 (getr R1 12) ltac:(lia) ltac:(cbn; lia)) as F1c.
    clear HR HK. replace (0x55e588 : word) with (Z_to_bv 64 AEXIT_CAS_RET) in RS2 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr XFUEL XSTOPS scr0 AEXIT_CAS_RET srX2i2zf knX2i2zf NV (fst (fst rX22zf)) (snd (fst rX22zf)) (snd rX22zf)
              (fst (fst cX22zf)) (snd (fst cX22zf)) (snd cX22zf) (ENV vals) _ (seg_rom RSEGS) _ msF2 mo2);
      [ vm_cast_no_check (@eq_refl _ rX22zf) | vm_cast_no_check (@eq_refl _ cX22zf)
      | exact HR2 | exact HK2 | rewrite SC2; constructor | rewrite CC2; constructor | exact OK2 | exact RS2 | ].
    clear HR2 HK2 RS2 OK2. intros R2 M2 msF3 mo3 HR HK EQ2 LF2 OK3 SB3 HS3 RS3.
    pose proof (log_covered_frame (ENV vals) (wbytes M1 (Z_to_bv 64 0xc01f00) (word_to_le_bytes 4 (getr R1 12))) x_regions _ x_cov2_2zf RF LF2) as F2. rewrite <- EQ2, RD in F2. clear EQ2 LF2.
    change (s_regs (fst (fst rX22zf))) with srX22zf in HR. change (fst (fst cX22zf)) with knX22zf in HK. rewrite PC2 in RS3.
    (* [comment removed for export] *)
    eapply (unreg_call_sound L S Zr vals (blobs_ev []) srX22zf knX22zf R2 M2 msF3 mo3 uX2zf);
      [ exact HR | exact HK | rewrite HL; exact UC | exact OK3 | exact RS3 | ].
    clear HR HK. intros R3 M3 msF4 mo4 HR HK FR3 GR3 OK4 SB4 HS4 RS4.
    set (vals' := vals ++ junk_vals R3) in *.
    change (Env (vals_ev vals') (blobs_ev [])) with (ENV vals') in HR, HK.
    assert (HL' : length vals' = 73%nat) by (subst vals'; rewrite length_app, HL; reflexivity).
    assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; unfold NV; lia); exact P0).
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr XFUEL XSTOPS scr0 FE_RET (uc_sr uX2zf) (uc_kn uX2zf) 73 (fst (fst rX32zf)) (snd (fst rX32zf)) (snd rX32zf)
              (fst (fst cX32zf)) (snd (fst cX32zf)) (snd cX32zf) (ENV vals') M3 (seg_rom RSEGS) R3 msF4 mo4);
      [ vm_cast_no_check (@eq_refl _ rX32zf) | vm_cast_no_check (@eq_refl _ cX32zf)
      | exact HR | exact HK | rewrite SC3; constructor | rewrite CC3; constructor | exact OK4 | exact RS4 | ].
    clear HR HK RS4 OK4. intros R4 M4 msF5 mo5 HR HK EQ4 LF4 OK5 SB5 HS5 RS5.
    pose proof (log_covered_frame (ENV vals') M3 x_regions _ x_cov3_2zf (x_regions_flat vals' P0' ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) LF4) as F4. rewrite <- EQ4, (x_regions_denot vals' P0' ltac:(unfold ASP_LO; lia)) in F4. clear EQ4 LF4.
    change (s_regs (fst (fst rX32zf))) with srX32zf in HR. change (fst (fst cX32zf)) with knX32zf in HK. rewrite PC3 in RS5.
    (* [comment removed for export] *)
    cbn [nth srX22zf edenot ev ENV] in FR3. rewrite P0, alu_add, vadd_wZ in FR3. rewrite u64_lit in FR3 by lia.
    pose proof (fe_frame M2 M3 (bv_unsigned sp0 + -80) ltac:(unfold ASP_HI; lia) FR3 GR3) as FFE. clear FR3 GR3.
    assert (FM : frame_mod M M4 (x_regions_w ++ [(Z_to_bv 64 0xc01f00, 4%Z)] ++ x_regions_w ++ fe_regions_w (bv_unsigned sp0 + -80) ++ x_regions_w)).
    { eapply frame_mod_trans; [exact F1|]. eapply frame_mod_trans; [exact F1c|]. eapply frame_mod_trans; [exact F2|].
      eapply frame_mod_trans; [exact FFE| exact F4]. }
    assert (RDP4 : rdn RSEGS M4 (Z_to_bv 64 0xc027a8) (length pending) = Some pending).
    { rewrite <- RDP. apply (frame_mod_rdn RSEGS M M4 _ (length pending) (Z_to_bv 64 0xc027a8) FM).
      - intros i Hi. rewrite u64_lit by lia. apply x_regions_bufF; [lia | unfold ASP_LO; lia | unfold ASP_HI; lia].
      - rewrite u64_lit by lia. lia. }
    (* [comment removed for export] *)
    assert (P4' : vals_ev vals' 4 = vals_ev vals 4) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; unfold NV; lia); reflexivity).
    pose proof (u64_range (vals_ev vals 4)) as H4r.
    rewrite <- (app_nil_r pending).
    apply (stdio_call_sound vals' (blobs_ev []) srX32zf knX32zf R4 M4 L S Zr msF5 mo5 scX2zf pending [] _ HR HK
             (eq_trans (f_equal (fun n => stdio_call n srX32zf knX32zf) HL') SCALL));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scX2zf length edenot ev ENV Z.of_nat Pos.of_succ_nat Pos.succ];
      rewrite ?P0', ?P4'.
    all: try change (bv_unsigned (Z_to_bv 64 12593064)) with 12593064%Z.
    all: try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    - lia.
    - lia.
    - lia.
    - reflexivity.
    - cbn [length]. lia.
    - left. rewrite alu_add, vadd_wZ. unorm. lia.
    - left. rewrite alu_add, vadd_wZ. unorm. lia.
    - lia.
    - exact RDP4.
    - reflexivity.
    - rewrite (same_but_materialized_fds _ _ SB5), (same_but_materialized_fds _ _ SB4), (same_but_materialized_fds _ _ SB3),
              (same_but_materialized_fds _ _ SB2), (same_but_materialized_fds _ _ SB1). exact Hfd1.
    - exact OK5.
    - exact RS5.
    - apply t_emit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R5 M5 msF6 mo6 HR HK OK6 SB6 HS6 RS6.
      set (vals'' := vals' ++ junk_vals R5) in *.
      change (Env (vals_ev vals'') (blobs_ev [])) with (ENV vals'') in HR, HK.
      eapply (rz_run_lazy RSEGS L S Zr XFUEL XSTOPS scr0 (sc_ret scX2zf) (sc_sr scX2zf) (sc_kn scX2zf) 105 (fst (fst rX42zf)) (snd (fst rX42zf)) (snd rX42zf)
                (fst (fst cX42zf)) (snd (fst cX42zf)) (snd cX42zf) (ENV vals'') M5 (seg_rom RSEGS) R5 msF6 mo6);
        [ vm_cast_no_check (@eq_refl _ rX42zf) | vm_cast_no_check (@eq_refl _ cX42zf)
        | exact HR | exact HK | rewrite SC4; constructor | rewrite CC4; constructor | exact OK6 | exact RS6 | ].
      clear HR HK. intros R6 M6 msF7 mo7 HR HK EQ6 OK7 SB7 HS7 RS7. rewrite PC4 in RS7.
      rewrite <- (same_but_materialized_fs _ _ SB1), <- (same_but_materialized_fs _ _ SB2), <- (same_but_materialized_fs _ _ SB3),
              <- (same_but_materialized_fs _ _ SB4), <- (same_but_materialized_fs _ _ SB5), <- (same_but_materialized_fs _ _ SB6),
              <- (same_but_materialized_fs _ _ SB7).
      eapply (rz_exit_at_lazy RSEGS L S Zr msF7 R6 (Z_to_bv 64 AEXIT_ECALL) M6 (seg_rom RSEGS) mo7 ECALLW code);
        [ vm_compute; reflexivity | apply is_ecall_ECALLW | exact OK7 | exact RS7 | reflexivity
        | left; regv HR (17:reg); reflexivity | regv HR (10:reg) ].
      change (edenot (ENV vals'') (EVar 2)) with (vals_ev vals'' 2). subst vals'' vals'. rewrite <- app_assoc.
      rewrite vals_ev_app_l by (rewrite HL; unfold NV; lia). exact P2.
  Qed.

  Theorem ax_sound_2nc : forall vals R M msF mo (code : word),
    length vals = NV -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = code ->
    regs_ok (ENV vals) x_sr R -> know_ok RSEGS (ENV vals) M (ax_kn true true false) ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 AEXIT) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs mo)).
  Proof.
    intros vals R M msF mo code HL P0 P2 HR HK OK RS.
    pose proof (know_nth RSEGS _ _ (ax_kn true true false) 1%nat _ HK eq_refl) as Hrg. cbn [kentry_ok edenot ev ENV] in Hrg. rewrite P0 in Hrg.
    unfold ASP_LO, ASP_HI in Hrg. pose proof (u64_range sp0) as Hsp.
    pose proof x_itinerary_2nc as (PC1 & SC1 & CC1 & CC2i & KR1 & PC2 & SC2 & CC2 & UC & PC3 & SC3 & CC3).
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr XFUEL XSTOPS scr0 AEXIT x_sr (ax_kn true true false) NV (fst (fst rX12nc)) (snd (fst rX12nc)) (snd rX12nc)
              (fst (fst cX12nc)) (snd (fst cX12nc)) (snd cX12nc) (ENV vals) M (seg_rom RSEGS) R msF mo);
      [ vm_cast_no_check (@eq_refl _ rX12nc) | vm_cast_no_check (@eq_refl _ cX12nc)
      | exact HR | exact HK | rewrite SC1; constructor | rewrite CC1; constructor | exact OK | exact RS | ].
    clear HR HK RS OK. intros R1 M1 msF1 mo1 HR HK EQ1 LF1 OK1 SB1 HS1 RS1.
    clear EQ1 LF1.
    change (s_regs (fst (fst rX12nc))) with srX12nc in HR. change (fst (fst cX12nc)) with knX12nc in HK. rewrite PC1 in RS1.
    (* [comment removed for export] *)
    pose proof (kread_rdn RSEGS (ENV vals) M1 knX12nc (ELit 0) 0xc01f00 4 _ HK KR1 ltac:(lia) ltac:(lia)
                  ltac:(unfold flat, estart; cbn [a_base a_off edenot]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia)) as Mlock.
    rewrite adenot_lit0 in Mlock. cbn [edenot] in Mlock.
    eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact OK1 | exact RS1 | |].
    { replace (Z_to_bv 64 AEXIT_LR) with (0x55e57c : word) by (apply bv_eq; reflexivity).
      apply (cas_exit_lock R1 M1 (seg_rom RSEGS) (getr R1 12)); [regv HR (13:reg); reflexivity | regv HR (11:reg); reflexivity | reflexivity | exact Mlock]. }
    clear Mlock. intros msF2 mo2 OK2 SB2 HS2 RS2.
    assert (HR2 : regs_ok (ENV vals) srX2i2nc (regupd (regupd R1 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 0))).
    { change srX2i2nc with (sr_upd (sr_upd srX12nc (ridx 14) (ELit 0%Z)) (ridx 15) (ELit 0%Z)).
      apply regs_ok_set; [apply regs_ok_set; [exact HR | discriminate | reflexivity] | discriminate | reflexivity]. }
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M1 (Z_to_bv 64 0xc01f00) (word_to_le_bytes 4 (getr R1 12))) knX2i2nc).
    { change knX2i2nc with (fst (fst cX2i2nc)).
      apply (one_carry_ok (ENV vals) M1 knX12nc 0xc01f00 4 (sr_get srX12nc 12) (getr R1 12) (fst (fst cX2i2nc)) (snd cX2i2nc));
        [ vm_cast_no_check (@eq_refl _ cX2i2nc) | exact HK | symmetry; apply HR | lia | cbn; lia | lia ]. }
    
    clear HR HK. replace (0x55e588 : word) with (Z_to_bv 64 AEXIT_CAS_RET) in RS2 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr XFUEL XSTOPS scr0 AEXIT_CAS_RET srX2i2nc knX2i2nc NV (fst (fst rX22nc)) (snd (fst rX22nc)) (snd rX22nc)
              (fst (fst cX22nc)) (snd (fst cX22nc)) (snd cX22nc) (ENV vals) _ (seg_rom RSEGS) _ msF2 mo2);
      [ vm_cast_no_check (@eq_refl _ rX22nc) | vm_cast_no_check (@eq_refl _ cX22nc)
      | exact HR2 | exact HK2 | rewrite SC2; constructor | rewrite CC2; constructor | exact OK2 | exact RS2 | ].
    clear HR2 HK2 RS2 OK2. intros R2 M2 msF3 mo3 HR HK EQ2 LF2 OK3 SB3 HS3 RS3.
    clear EQ2 LF2.
    change (s_regs (fst (fst rX22nc))) with srX22nc in HR. change (fst (fst cX22nc)) with knX22nc in HK. rewrite PC2 in RS3.
    (* [comment removed for export] *)
    eapply (unreg_call_sound L S Zr vals (blobs_ev []) srX22nc knX22nc R2 M2 msF3 mo3 uX2nc);
      [ exact HR | exact HK | rewrite HL; exact UC | exact OK3 | exact RS3 | ].
    clear HR HK. intros R3 M3 msF4 mo4 HR HK FR3 GR3 OK4 SB4 HS4 RS4.
    set (vals' := vals ++ junk_vals R3) in *.
    change (Env (vals_ev vals') (blobs_ev [])) with (ENV vals') in HR, HK.
    clear FR3 GR3.
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr XFUEL XSTOPS scr0 FE_RET (uc_sr uX2nc) (uc_kn uX2nc) 73 (fst (fst rX32nc)) (snd (fst rX32nc)) (snd rX32nc)
              (fst (fst cX32nc)) (snd (fst cX32nc)) (snd cX32nc) (ENV vals') M3 (seg_rom RSEGS) R3 msF4 mo4);
      [ vm_cast_no_check (@eq_refl _ rX32nc) | vm_cast_no_check (@eq_refl _ cX32nc)
      | exact HR | exact HK | rewrite SC3; constructor | rewrite CC3; constructor | exact OK4 | exact RS4 | ].
    clear HR HK RS4 OK4. intros R4 M4 msF5 mo5 HR HK EQ4 LF4 OK5 SB5 HS5 RS5.
    clear EQ4 LF4.
    change (s_regs (fst (fst rX32nc))) with srX32nc in HR. change (fst (fst cX32nc)) with knX32nc in HK. rewrite PC3 in RS5.
    rewrite <- (same_but_materialized_fs _ _ SB1), <- (same_but_materialized_fs _ _ SB2), <- (same_but_materialized_fs _ _ SB3),
            <- (same_but_materialized_fs _ _ SB4), <- (same_but_materialized_fs _ _ SB5).
    eapply (rz_exit_at_lazy RSEGS L S Zr msF5 R4 (Z_to_bv 64 AEXIT_ECALL) M4 (seg_rom RSEGS) mo5 ECALLW code);
      [ vm_compute; reflexivity | apply is_ecall_ECALLW | exact OK5 | exact RS5 | reflexivity
      | left; regv HR (17:reg); reflexivity | regv HR (10:reg) ].
    change (edenot (ENV vals') (EVar 2)) with (vals_ev vals' 2). subst vals'. rewrite vals_ev_app_l by (rewrite HL; unfold NV; lia). exact P2.
  Qed.

  Lemma x_cov1_2nf : log_covered x_regions (s_log (fst (fst rX12nf))) = true. Proof. vm_compute. reflexivity. Qed.
  Lemma x_cov2_2nf : log_covered x_regions (s_log (fst (fst rX22nf))) = true. Proof. vm_compute. reflexivity. Qed.
  Lemma x_cov3_2nf : log_covered x_regions (s_log (fst (fst rX32nf))) = true. Proof. vm_compute. reflexivity. Qed.

  Theorem ax_sound_2nf : forall vals R M msF mo (pending : list byte) (code : word),
    length vals = NV -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = code ->
    regs_ok (ENV vals) x_sr R -> know_ok RSEGS (ENV vals) M (ax_kn true true true) ->
    (* [comment removed for export] *)
    (bv_unsigned (vals_ev vals 4) - 0xc027a8 = Z.of_nat (length pending))%Z ->
    (Z.of_nat (length pending) <= 1024)%Z ->
    rdn RSEGS M (Z_to_bv 64 0xc027a8) (length pending) = Some pending ->
    fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 AEXIT) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (map (WriteEv (Z_to_bv 64 1)) pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs mo))).
  Proof.
    intros vals R M msF mo pending code HL P0 P2 HR HK LEN MAX RDP Hfd1 OK RS.
    pose proof (know_nth RSEGS _ _ (ax_kn true true true) 1%nat _ HK eq_refl) as Hrg. cbn [kentry_ok edenot ev ENV] in Hrg. rewrite P0 in Hrg.
    pose proof (know_nth RSEGS _ _ (ax_kn true true true) 25%nat _ HK eq_refl) as Hwp. cbn [kentry_ok edenot ev ENV] in Hwp.
    unfold ASP_LO, ASP_HI in Hrg. pose proof (u64_range sp0) as Hsp.
    pose proof (x_regions_flat vals P0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF.
    pose proof (x_regions_denot vals P0 ltac:(unfold ASP_LO; lia)) as RD.
    pose proof x_itinerary_2nf as (PC1 & SC1 & CC1 & CC2i & KR1 & PC2 & SC2 & CC2 & UC & PC3 & SC3 & CC3 & SCALL & PC4 & SC4 & CC4).
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr XFUEL XSTOPS scr0 AEXIT x_sr (ax_kn true true true) NV (fst (fst rX12nf)) (snd (fst rX12nf)) (snd rX12nf)
              (fst (fst cX12nf)) (snd (fst cX12nf)) (snd cX12nf) (ENV vals) M (seg_rom RSEGS) R msF mo);
      [ vm_cast_no_check (@eq_refl _ rX12nf) | vm_cast_no_check (@eq_refl _ cX12nf)
      | exact HR | exact HK | rewrite SC1; constructor | rewrite CC1; constructor | exact OK | exact RS | ].
    clear HR HK RS OK. intros R1 M1 msF1 mo1 HR HK EQ1 LF1 OK1 SB1 HS1 RS1.
    pose proof (log_covered_frame (ENV vals) M x_regions _ x_cov1_2nf RF LF1) as F1. rewrite <- EQ1, RD in F1. clear EQ1 LF1.
    change (s_regs (fst (fst rX12nf))) with srX12nf in HR. change (fst (fst cX12nf)) with knX12nf in HK. rewrite PC1 in RS1.
    (* [comment removed for export] *)
    pose proof (kread_rdn RSEGS (ENV vals) M1 knX12nf (ELit 0) 0xc01f00 4 _ HK KR1 ltac:(lia) ltac:(lia)
                  ltac:(unfold flat, estart; cbn [a_base a_off edenot]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia)) as Mlock.
    rewrite adenot_lit0 in Mlock. cbn [edenot] in Mlock.
    eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact OK1 | exact RS1 | |].
    { replace (Z_to_bv 64 AEXIT_LR) with (0x55e57c : word) by (apply bv_eq; reflexivity).
      apply (cas_exit_lock R1 M1 (seg_rom RSEGS) (getr R1 12)); [regv HR (13:reg); reflexivity | regv HR (11:reg); reflexivity | reflexivity | exact Mlock]. }
    clear Mlock. intros msF2 mo2 OK2 SB2 HS2 RS2.
    assert (HR2 : regs_ok (ENV vals) srX2i2nf (regupd (regupd R1 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 0))).
    { change srX2i2nf with (sr_upd (sr_upd srX12nf (ridx 14) (ELit 0%Z)) (ridx 15) (ELit 0%Z)).
      apply regs_ok_set; [apply regs_ok_set; [exact HR | discriminate | reflexivity] | discriminate | reflexivity]. }
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M1 (Z_to_bv 64 0xc01f00) (word_to_le_bytes 4 (getr R1 12))) knX2i2nf).
    { change knX2i2nf with (fst (fst cX2i2nf)).
      apply (one_carry_ok (ENV vals) M1 knX12nf 0xc01f00 4 (sr_get srX12nf 12) (getr R1 12) (fst (fst cX2i2nf)) (snd cX2i2nf));
        [ vm_cast_no_check (@eq_refl _ cX2i2nf) | exact HK | symmetry; apply HR | lia | cbn; lia | lia ]. }
    pose proof (frame_wbytes_lit M1 0xc01f00 4 (getr R1 12) ltac:(lia) ltac:(cbn; lia)) as F1c.
    clear HR HK. replace (0x55e588 : word) with (Z_to_bv 64 AEXIT_CAS_RET) in RS2 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr XFUEL XSTOPS scr0 AEXIT_CAS_RET srX2i2nf knX2i2nf NV (fst (fst rX22nf)) (snd (fst rX22nf)) (snd rX22nf)
              (fst (fst cX22nf)) (snd (fst cX22nf)) (snd cX22nf) (ENV vals) _ (seg_rom RSEGS) _ msF2 mo2);
      [ vm_cast_no_check (@eq_refl _ rX22nf) | vm_cast_no_check (@eq_refl _ cX22nf)
      | exact HR2 | exact HK2 | rewrite SC2; constructor | rewrite CC2; constructor | exact OK2 | exact RS2 | ].
    clear HR2 HK2 RS2 OK2. intros R2 M2 msF3 mo3 HR HK EQ2 LF2 OK3 SB3 HS3 RS3.
    pose proof (log_covered_frame (ENV vals) (wbytes M1 (Z_to_bv 64 0xc01f00) (word_to_le_bytes 4 (getr R1 12))) x_regions _ x_cov2_2nf RF LF2) as F2. rewrite <- EQ2, RD in F2. clear EQ2 LF2.
    change (s_regs (fst (fst rX22nf))) with srX22nf in HR. change (fst (fst cX22nf)) with knX22nf in HK. rewrite PC2 in RS3.
    (* [comment removed for export] *)
    eapply (unreg_call_sound L S Zr vals (blobs_ev []) srX22nf knX22nf R2 M2 msF3 mo3 uX2nf);
      [ exact HR | exact HK | rewrite HL; exact UC | exact OK3 | exact RS3 | ].
    clear HR HK. intros R3 M3 msF4 mo4 HR HK FR3 GR3 OK4 SB4 HS4 RS4.
    set (vals' := vals ++ junk_vals R3) in *.
    change (Env (vals_ev vals') (blobs_ev [])) with (ENV vals') in HR, HK.
    assert (HL' : length vals' = 73%nat) by (subst vals'; rewrite length_app, HL; reflexivity).
    assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; unfold NV; lia); exact P0).
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr XFUEL XSTOPS scr0 FE_RET (uc_sr uX2nf) (uc_kn uX2nf) 73 (fst (fst rX32nf)) (snd (fst rX32nf)) (snd rX32nf)
              (fst (fst cX32nf)) (snd (fst cX32nf)) (snd cX32nf) (ENV vals') M3 (seg_rom RSEGS) R3 msF4 mo4);
      [ vm_cast_no_check (@eq_refl _ rX32nf) | vm_cast_no_check (@eq_refl _ cX32nf)
      | exact HR | exact HK | rewrite SC3; constructor | rewrite CC3; constructor | exact OK4 | exact RS4 | ].
    clear HR HK RS4 OK4. intros R4 M4 msF5 mo5 HR HK EQ4 LF4 OK5 SB5 HS5 RS5.
    pose proof (log_covered_frame (ENV vals') M3 x_regions _ x_cov3_2nf (x_regions_flat vals' P0' ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) LF4) as F4. rewrite <- EQ4, (x_regions_denot vals' P0' ltac:(unfold ASP_LO; lia)) in F4. clear EQ4 LF4.
    change (s_regs (fst (fst rX32nf))) with srX32nf in HR. change (fst (fst cX32nf)) with knX32nf in HK. rewrite PC3 in RS5.
    (* [comment removed for export] *)
    cbn [nth srX22nf edenot ev ENV] in FR3. rewrite P0, alu_add, vadd_wZ in FR3. rewrite u64_lit in FR3 by lia.
    pose proof (fe_frame M2 M3 (bv_unsigned sp0 + -80) ltac:(unfold ASP_HI; lia) FR3 GR3) as FFE. clear FR3 GR3.
    assert (FM : frame_mod M M4 (x_regions_w ++ [(Z_to_bv 64 0xc01f00, 4%Z)] ++ x_regions_w ++ fe_regions_w (bv_unsigned sp0 + -80) ++ x_regions_w)).
    { eapply frame_mod_trans; [exact F1|]. eapply frame_mod_trans; [exact F1c|]. eapply frame_mod_trans; [exact F2|].
      eapply frame_mod_trans; [exact FFE| exact F4]. }
    assert (RDP4 : rdn RSEGS M4 (Z_to_bv 64 0xc027a8) (length pending) = Some pending).
    { rewrite <- RDP. apply (frame_mod_rdn RSEGS M M4 _ (length pending) (Z_to_bv 64 0xc027a8) FM).
      - intros i Hi. rewrite u64_lit by lia. apply x_regions_bufF; [lia | unfold ASP_LO; lia | unfold ASP_HI; lia].
      - rewrite u64_lit by lia. lia. }
    (* [comment removed for export] *)
    assert (P4' : vals_ev vals' 4 = vals_ev vals 4) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; unfold NV; lia); reflexivity).
    pose proof (u64_range (vals_ev vals 4)) as H4r.
    rewrite <- (app_nil_r pending).
    apply (stdio_call_sound vals' (blobs_ev []) srX32nf knX32nf R4 M4 L S Zr msF5 mo5 scX2nf pending [] _ HR HK
             (eq_trans (f_equal (fun n => stdio_call n srX32nf knX32nf) HL') SCALL));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scX2nf length edenot ev ENV Z.of_nat Pos.of_succ_nat Pos.succ];
      rewrite ?P0', ?P4'.
    all: try change (bv_unsigned (Z_to_bv 64 12593064)) with 12593064%Z.
    all: try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    - lia.
    - lia.
    - lia.
    - reflexivity.
    - cbn [length]. lia.
    - left. rewrite alu_add, vadd_wZ. unorm. lia.
    - left. rewrite alu_add, vadd_wZ. unorm. lia.
    - lia.
    - exact RDP4.
    - reflexivity.
    - rewrite (same_but_materialized_fds _ _ SB5), (same_but_materialized_fds _ _ SB4), (same_but_materialized_fds _ _ SB3),
              (same_but_materialized_fds _ _ SB2), (same_but_materialized_fds _ _ SB1). exact Hfd1.
    - exact OK5.
    - exact RS5.
    - apply t_emit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R5 M5 msF6 mo6 HR HK OK6 SB6 HS6 RS6.
      set (vals'' := vals' ++ junk_vals R5) in *.
      change (Env (vals_ev vals'') (blobs_ev [])) with (ENV vals'') in HR, HK.
      eapply (rz_run_lazy RSEGS L S Zr XFUEL XSTOPS scr0 (sc_ret scX2nf) (sc_sr scX2nf) (sc_kn scX2nf) 105 (fst (fst rX42nf)) (snd (fst rX42nf)) (snd rX42nf)
                (fst (fst cX42nf)) (snd (fst cX42nf)) (snd cX42nf) (ENV vals'') M5 (seg_rom RSEGS) R5 msF6 mo6);
        [ vm_cast_no_check (@eq_refl _ rX42nf) | vm_cast_no_check (@eq_refl _ cX42nf)
        | exact HR | exact HK | rewrite SC4; constructor | rewrite CC4; constructor | exact OK6 | exact RS6 | ].
      clear HR HK. intros R6 M6 msF7 mo7 HR HK EQ6 OK7 SB7 HS7 RS7. rewrite PC4 in RS7.
      rewrite <- (same_but_materialized_fs _ _ SB1), <- (same_but_materialized_fs _ _ SB2), <- (same_but_materialized_fs _ _ SB3),
              <- (same_but_materialized_fs _ _ SB4), <- (same_but_materialized_fs _ _ SB5), <- (same_but_materialized_fs _ _ SB6),
              <- (same_but_materialized_fs _ _ SB7).
      eapply (rz_exit_at_lazy RSEGS L S Zr msF7 R6 (Z_to_bv 64 AEXIT_ECALL) M6 (seg_rom RSEGS) mo7 ECALLW code);
        [ vm_compute; reflexivity | apply is_ecall_ECALLW | exact OK7 | exact RS7 | reflexivity
        | left; regv HR (17:reg); reflexivity | regv HR (10:reg) ].
      change (edenot (ENV vals'') (EVar 2)) with (vals_ev vals'' 2). subst vals'' vals'. rewrite <- app_assoc.
      rewrite vals_ev_app_l by (rewrite HL; unfold NV; lia). exact P2.
  Qed.
End Exit.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Plain.
  Variables (L S Zr : list (word * word)).

  (* [comment removed for export] *)
  Record axH (ax2 : bool) (mem : word -> option byte) (sp : word) (tid can : Z) (we re ro : word) : Prop := AXH {
    Xsp16 : (bv_unsigned sp mod 16 = 0)%Z;
    XspLo : (ASP_LO <= bv_unsigned sp)%Z;
    XspHi : (bv_unsigned sp <= ASP_HI)%Z;
    Xstk  : stk_ok RSEGS mem sp 1024;
    Xtid  : (0 < tid < 2147483648)%Z;
    Xtidc : rdn RSEGS mem (Z_to_bv 64 0xbe1be8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
    Ximg  : forall i, (0x10000 <= i < 0x195000)%Z -> mem (Z_to_bv 64 i) = None;
    Xtext : forall i, (0x195000 <= i < 0x571000)%Z -> mem (Z_to_bv 64 i) = None;
    Xgot  : forall i, (0x571000 <= i < 0x5ea000)%Z -> mem (Z_to_bv 64 i) = None;
    Xuse2 : forall i, (0x5edd90 <= i < 0x5ede88)%Z -> mem (Z_to_bv 64 i) = None;
    Xglb  : forall i, (0x5edf70 <= i < 0x6a7220 /\ ~ (0x5edf88 <= i < 0x5edf90))%Z -> mem (Z_to_bv 64 i) = None;   (* [comment removed for export] *)
    Xcan  : rdn RSEGS mem (Z_to_bv 64 0xc01cd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    Xcan64 : (0 <= can < 2 ^ 64)%Z;
    Xew1  : rdn RSEGS mem (Z_to_bv 64 0x5edcd0) 8 = Some (word_to_le_bytes 8 we);
    Xew2  : rdn RSEGS mem (Z_to_bv 64 0x5edce0) 8 = Some (word_to_le_bytes 8 we);
    Xer1  : rdn RSEGS mem (Z_to_bv 64 0x5edcb0) 8 = Some (word_to_le_bytes 8 re);
    Xer2  : rdn RSEGS mem (Z_to_bv 64 0x5edcb8) 8 = Some (word_to_le_bytes 8 re);
    Xor1  : rdn RSEGS mem (Z_to_bv 64 0x5ede90) 8 = Some (word_to_le_bytes 8 ro);
    Xor2  : rdn RSEGS mem (Z_to_bv 64 0x5ede98) 8 = Some (word_to_le_bytes 8 ro);
    Xcells : cells_ok mem ax_lit_cells;
    Xatexit : cells_ok mem (ax_atexit_cells ax2);
    Xshw  : forall (a : word) (n : nat), (0x7fffa000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x7fffa000 + 0x17e800)%Z ->
              store_ok RSEGS mem a n = true }.

  Definition x_vals (regs : bvmap 5 word) (sp : word) (tid : Z) (code : word) (can wp : Z) (we re ro : word) (bi : Z) : list word :=
    [sp; Z_to_bv 64 tid; code; Z_to_bv 64 can; Z_to_bv 64 wp; we; re; ro] ++ junk_vals regs ++ [Z_to_bv 64 bi].

  Lemma x_vals_len : forall regs sp tid code can wp we re ro bi, length (x_vals regs sp tid code can wp we re ro bi) = NV.
  Proof. intros. unfold x_vals. rewrite !length_app, junk_vals_length. reflexivity. Qed.

  Lemma x_ev_junk : forall regs sp tid code can wp we re ro bi i, (8 <= i < 40)%nat ->
    ev (ENV (x_vals regs sp tid code can wp we re ro bi)) i = getr regs (Z_to_bv 5 (Z.of_nat (i - 8))).
  Proof.
    intros regs sp tid code can wp we re ro bi i Hi. unfold ENV, x_vals. cbn [ev]. unfold vals_ev.
    replace i with (length [sp; Z_to_bv 64 tid; code; Z_to_bv 64 can; Z_to_bv 64 wp; we; re; ro] + (i - 8))%nat at 1 by (cbn; lia).
    rewrite app_nth2_plus. rewrite app_nth1 by (rewrite junk_vals_length; lia). unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  Lemma x_ev_bi : forall regs sp tid code can wp we re ro bi,
    ev (ENV (x_vals regs sp tid code can wp we re ro bi)) 40 = Z_to_bv 64 bi.
  Proof.
    intros. unfold ENV, x_vals. cbn [ev]. unfold vals_ev.
    change 40%nat with (length [sp; Z_to_bv 64 tid; code; Z_to_bv 64 can; Z_to_bv 64 wp; we; re; ro] + 32)%nat.
    rewrite app_nth2_plus. rewrite app_nth2 by (rewrite junk_vals_length; lia). rewrite junk_vals_length. reflexivity.
  Qed.

  Lemma x_regs_ok : forall regs sp tid code can wp we re ro bi,
    getr regs 2 = sp -> getr regs 4 = Z_to_bv 64 0xbe1c90 -> getr regs 10 = code ->
    regs_ok (ENV (x_vals regs sp tid code can wp we re ro bi)) x_sr regs.
  Proof.
    intros regs sp tid code can wp we re ro bi R2 R4 R10.
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth x_sr allregs32 edenot].
    1: apply getr_zero.
    2: exact R2.
    3: exact R4.
    8: exact R10.
    all: rewrite x_ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  Ltac kw_var Z0 EV H := eapply (kword_intro RSEGS _ _ (ELit 0%Z) (Z_to_bv 64 0)); [reflexivity | exact EV | lia | lia | rewrite Z0; lia
        | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact H].
  Ltac kwr_data := cbn [kentry_ok]; unfold flat, estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia;
        split; [lia|]; intros d m Hd Hm; apply store_ok_data; rewrite u64_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma x_know_ok_common : forall (ax2 binz fl : bool) regs mem sp tid code can wp we re ro bi extra,
    axH ax2 mem sp tid can we re ro ->
    (if binz then rdn RSEGS mem (Z_to_bv 64 0xbdd420) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bi)) /\ (1 <= bi <= 255)%Z
     else rdn RSEGS mem (Z_to_bv 64 0xbdd420) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0))) ->
    know_ok RSEGS (ENV (x_vals regs sp tid code can wp we re ro bi)) mem extra ->
    know_ok RSEGS (ENV (x_vals regs sp tid code can wp we re ro bi)) mem
      ([KAlign (EVar 0) 16; KRange (EVar 0) ASP_LO ASP_HI; KWr (SA (EVar 0) (-1024)) 1024; KRange (EVar 1) 1 2147483647;
        KImg 0x10000 0x195000; KImg 0x195000 0x571000; KImg 0x571000 0x5ea000; KImg 0x5edd90 0x5ede88; KImg 0x5edf70 0x5edf88; KImg 0x5edf90 0x6a7220;
        KWord (SA (ELit 0) 0xbe1be8) 4 (EVar 1); KWord (SA (ELit 0) 0xc01cd0) 8 (EVar 3);
        KWord (SA (ELit 0) 0x5edcd0) 8 (EVar 5); KWord (SA (ELit 0) 0x5edce0) 8 (EVar 5);
        KWord (SA (ELit 0) 0x5edcb0) 8 (EVar 6); KWord (SA (ELit 0) 0x5edcb8) 8 (EVar 6);
        KWord (SA (ELit 0) 0x5ede90) 8 (EVar 7); KWord (SA (ELit 0) 0x5ede98) 8 (EVar 7);
        KWr (SA (ELit 0) 0xc01ce0) 24; KWr (SA (ELit 0) 0xc01f00) 4; KWr (SA (ELit 0) 0x6a7290) 1; KWr (SA (ELit 0) 0x6a7240) 8;
        KWr (SA (ELit 0) 0x7fffa000) 0x17e800; KWr (SA (ELit 0) 0x5ede88) 232]%Z
       ++ (if binz then [KWord (SA (ELit 0) 0xbdd420) 1 (EVar 40); KRange (EVar 40) 1 255]%Z else [KWord (SA (ELit 0) 0xbdd420) 1 (ELit 0)]%Z)
       ++ extra ++ kn_cells (ax_atexit_cells ax2) ++ kn_cells ax_lit_cells).
  Proof.
    intros ax2 binz fl regs mem sp tid code can wp we re ro bi extra XH Hbi HEX. destruct XH. pose proof (u64_range sp) as Hsp.
    set (E := ENV (x_vals regs sp tid code can wp we re ro bi)) in *.
    assert (E0 : ev E 0 = sp) by reflexivity.
    assert (E1 : ev E 1 = Z_to_bv 64 tid) by reflexivity.
    assert (E3 : ev E 3 = Z_to_bv 64 can) by reflexivity.
    assert (E5 : ev E 5 = we) by reflexivity. assert (E6 : ev E 6 = re) by reflexivity. assert (E7 : ev E 7 = ro) by reflexivity.
    assert (E40 : ev E 40 = Z_to_bv 64 bi) by (subst E; apply x_ev_bi).
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0%Z) by reflexivity.
    unfold ASP_LO, ASP_HI in *.
    apply (proj2 (know_ok_app RSEGS _ _ _ _)). split.
    2:{ apply (proj2 (know_ok_app RSEGS _ _ _ _)). split.
        - destruct binz.
          + destruct Hbi as [Hb Hr]. repeat (apply Forall_cons); [ | | apply Forall_nil].
            * kw_var Z0 E40 Hb.
            * apply krange_intro. cbn [edenot]. rewrite E40, u64_lit by lia. lia.
          + repeat (apply Forall_cons); [ | apply Forall_nil].
            eapply (kword_intro RSEGS _ _ (ELit 0%Z) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia
              | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Hbi].
        - apply (proj2 (know_ok_app RSEGS _ _ _ _)). split; [exact HEX|].
          apply (proj2 (know_ok_app RSEGS _ _ _ _)). split.
          + apply cells_know; [destruct ax2; vm_compute; reflexivity | assumption].
          + apply cells_know; [vm_compute; reflexivity | assumption]. }
    repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite E0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite E0. unfold ASP_LO, ASP_HI. lia.
    - apply (kwr_of_stk_ok RSEGS _ mem (EVar 0) sp 1024); [exact E0 | assumption | lia].
    - apply krange_intro. cbn [edenot]. rewrite E1, u64_lit by lia. lia.
    - apply kimg_intro; [lia | lia | assumption].
    - apply kimg_intro; [lia | lia | assumption].
    - apply kimg_intro; [lia | lia | assumption].
    - apply kimg_intro; [lia | lia | assumption].
    - apply kimg_intro; [lia | lia | intros i Hi; apply Xglb0; lia].
    - apply kimg_intro; [lia | lia | intros i Hi; apply Xglb0; lia].
    - kw_var Z0 E1 Xtidc0.
    - kw_var Z0 E3 Xcan0.
    - kw_var Z0 E5 Xew3. - kw_var Z0 E5 Xew4. - kw_var Z0 E6 Xer3. - kw_var Z0 E6 Xer4. - kw_var Z0 E7 Xor3. - kw_var Z0 E7 Xor4.
    - kwr_data. - kwr_data. - kwr_data. - kwr_data.
    - cbn [kentry_ok]; unfold flat, estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply Xshw0; rewrite u64_lit by lia; lia.
    - kwr_data.
  Qed.

  (* [comment removed for export] *)
  Theorem as_exit_clean1 : forall regs mem msF mo (sp code we re ro wpw : word) (tid can : Z),
    axH false mem sp tid can we re ro ->
    rdn RSEGS mem (Z_to_bv 64 0xbdd420) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) ->       (* [comment removed for export] *)
    rdn RSEGS mem (Z_to_bv 64 0x5edeb0) 8 = Some (word_to_le_bytes 8 wpw) ->                  (* [comment removed for export] *)
    rdn RSEGS mem (Z_to_bv 64 0x5edec0) 8 = Some (word_to_le_bytes 8 wpw) ->                  (* [comment removed for export] *)
    getr regs 2 = sp -> getr regs 4 = Z_to_bv 64 0xbe1c90 -> getr regs 10 = code ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 AEXIT) mem (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs mo)).
  Proof.
    intros regs mem msF mo sp code we re ro wpw tid can XH Hbi Xwp Xwb R2 R4 R10 OK RS.
    apply (ax_sound_1c sp L S Zr (x_vals regs sp tid code can (bv_unsigned wpw) we re ro 0) regs mem msF mo code);
      [ apply x_vals_len | reflexivity | reflexivity | apply x_regs_ok; assumption | | exact OK | exact RS ].
    unfold ax_kn. apply (x_know_ok_common false false false); [exact XH | exact Hbi |].
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0%Z) by reflexivity.
    assert (E4 : ev (ENV (x_vals regs sp tid code can (bv_unsigned wpw) we re ro 0)) 4 = wpw) by (cbn; apply Z_to_bv_bv_unsigned).
    repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - kw_var Z0 E4 Xwp.
    - kw_var Z0 E4 Xwb.
  Qed.

  (* [comment removed for export] *)
  Theorem as_exit_clean2 : forall regs mem msF mo (sp code we re ro wpw : word) (tid can bi : Z),
    axH true mem sp tid can we re ro ->
    rdn RSEGS mem (Z_to_bv 64 0xbdd420) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bi)) -> (0 <= bi <= 255)%Z ->
    rdn RSEGS mem (Z_to_bv 64 0x5edeb0) 8 = Some (word_to_le_bytes 8 wpw) ->
    rdn RSEGS mem (Z_to_bv 64 0x5edec0) 8 = Some (word_to_le_bytes 8 wpw) ->
    getr regs 2 = sp -> getr regs 4 = Z_to_bv 64 0xbe1c90 -> getr regs 10 = code ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 AEXIT) mem (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs mo)).
  Proof.
    intros regs mem msF mo sp code we re ro wpw tid can bi XH Hbi Hbir Xwp Xwb R2 R4 R10 OK RS.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0%Z) by reflexivity.
    assert (E4 : ev (ENV (x_vals regs sp tid code can (bv_unsigned wpw) we re ro bi)) 4 = wpw) by (cbn; apply Z_to_bv_bv_unsigned).
    destruct (Z.eq_dec bi 0) as [->|Hnz].
    - apply (ax_sound_2zc sp L S Zr (x_vals regs sp tid code can (bv_unsigned wpw) we re ro 0) regs mem msF mo code);
        [ apply x_vals_len | reflexivity | reflexivity | apply x_regs_ok; assumption | | exact OK | exact RS ].
      unfold ax_kn. apply (x_know_ok_common true false false); [exact XH | exact Hbi |].
      repeat (apply Forall_cons); [ .. | apply Forall_nil ]; [kw_var Z0 E4 Xwp | kw_var Z0 E4 Xwb].
    - apply (ax_sound_2nc sp L S Zr (x_vals regs sp tid code can (bv_unsigned wpw) we re ro bi) regs mem msF mo code);
        [ apply x_vals_len | reflexivity | reflexivity | apply x_regs_ok; assumption | | exact OK | exact RS ].
      unfold ax_kn. apply (x_know_ok_common true true false); [exact XH | split; [exact Hbi | lia] |].
      repeat (apply Forall_cons); [ .. | apply Forall_nil ]; [kw_var Z0 E4 Xwp | kw_var Z0 E4 Xwb].
  Qed.

  (* [comment removed for export] *)
  Theorem as_exit_flush2 : forall regs mem msF mo (sp code we re ro : word) (tid can wp bi : Z) (pending : list byte),
    axH true mem sp tid can we re ro ->
    rdn RSEGS mem (Z_to_bv 64 0xbdd420) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bi)) -> (0 <= bi <= 255)%Z ->
    rdn RSEGS mem (Z_to_bv 64 0x5edeb0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wp)) ->     (* [comment removed for export] *)
    cells_ok mem ax_flush_cells ->                                                             (* [comment removed for export] *)
    (0xc027a9 <= wp <= 0xc02ba8)%Z -> (wp - 0xc027a8 = Z.of_nat (length pending))%Z ->
    rdn RSEGS mem (Z_to_bv 64 0xc027a8) (length pending) = Some pending ->
    getr regs 2 = sp -> getr regs 4 = Z_to_bv 64 0xbe1c90 -> getr regs 10 = code ->
    fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 AEXIT) mem (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (map (WriteEv (Z_to_bv 64 1)) pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs mo))).
  Proof.
    intros regs mem msF mo sp code we re ro tid can wp bi pending XH Hbi Hbir Xwp Xfc Hwp LEN RDP R2 R4 R10 Hfd1 OK RS.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0%Z) by reflexivity.
    assert (E4 : forall b, ev (ENV (x_vals regs sp tid code can wp we re ro b)) 4 = Z_to_bv 64 wp) by reflexivity.
    destruct (Z.eq_dec bi 0) as [->|Hnz].
    - apply (ax_sound_2zf sp L S Zr (x_vals regs sp tid code can wp we re ro 0) regs mem msF mo pending code);
        [ apply x_vals_len | reflexivity | reflexivity | apply x_regs_ok; assumption | | cbn [vals_ev x_vals nth app]; rewrite u64_lit by lia; lia
        | lia | exact RDP | exact Hfd1 | exact OK | exact RS ].
      unfold ax_kn. apply (x_know_ok_common true false true); [exact XH | exact Hbi |].
      apply (proj2 (know_ok_app RSEGS _ _ _ _)). split; [| apply cells_know; [vm_compute; reflexivity | exact Xfc]].
      repeat (apply Forall_cons); [ .. | apply Forall_nil ].
      + kw_var Z0 (E4 0%Z) Xwp.
      + apply krange_intro. cbn [edenot]. rewrite (E4 0%Z), u64_lit by lia. lia.
    - apply (ax_sound_2nf sp L S Zr (x_vals regs sp tid code can wp we re ro bi) regs mem msF mo pending code);
        [ apply x_vals_len | reflexivity | reflexivity | apply x_regs_ok; assumption | | cbn [vals_ev x_vals nth app]; rewrite u64_lit by lia; lia
        | lia | exact RDP | exact Hfd1 | exact OK | exact RS ].
      unfold ax_kn. apply (x_know_ok_common true true true); [exact XH | split; [exact Hbi | lia] |].
      apply (proj2 (know_ok_app RSEGS _ _ _ _)). split; [| apply cells_know; [vm_compute; reflexivity | exact Xfc]].
      repeat (apply Forall_cons); [ .. | apply Forall_nil ].
      + kw_var Z0 (E4 bi) Xwp.
      + apply krange_intro. cbn [edenot]. rewrite (E4 bi), u64_lit by lia. lia.
  Qed.
End Plain.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
