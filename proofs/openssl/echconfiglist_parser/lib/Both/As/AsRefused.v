(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefPrintfLib LibTail Spec
  LazyRestrict LazySR LazyFdNodes LazySym.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import RefExitBase RefStdioDefs AsLazyRun AsStdioWrite AsStdioCall AsScLib AsPrintfFirst AsSxKit.
Import ListNotations.
Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RF_FR : Z := 5600%Z.
Definition AEXIT : Z := 0x55e55c%Z.
Definition STOPSR : list Z := [0x56407c; AEXIT]%Z.
Definition FUELR : nat := 20000.

(* [comment removed for export] *)
Definition rf_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0
                          | _ => EVar (2 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
Definition rf_cells : list (Z * nat * Z) :=
  [(0x5ea8e0, 8%nat, 0x56571c);
   (0x5eaa68, 8%nat, 0x5699dc);
   (0x5eaa70, 8%nat, 0x569e10);
   (0x6aa8f8, 8%nat, 0x7fff8000);
   (0x6ab5d8, 1%nat, 0x1);
   (0x6ab5d9, 1%nat, 0x1);
   (0x73c47c, 1%nat, 0x1);
   (0x5edca8, 4%nat, 0x5);
   (0x5edcc8, 8%nat, 0x0);
   (0x5edcd0, 8%nat, 0x0);
   (0x5edce0, 8%nat, 0x0);
   (0x5edcf0, 8%nat, 0x56407c);
   (0x5edd00, 8%nat, 0xc02398);
   (0x5edd08, 8%nat, 0x0);
   (0x5edd20, 4%nat, 0x2);
   (0x5edd30, 4%nat, 0x0);
   (0x5edd34, 4%nat, 0xffffffff);
   (0x5edd38, 4%nat, 0xffffffff);
   (0x7fffde08, 8%nat, 0x0);
   (0x7fffde10, 8%nat, 0x0)]%Z.

(* [comment removed for export] *)
Definition RF_OFFS : list Z := [-464; -451; -849; -856; -443; -450; -427; -442]%Z.

Definition rf_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) ASP_LO ASP_HI; KWr (SA (EVar 0) (- RF_FR)) RF_FR;
   KImg 0x10000 0x195000; KImg 0x571000 0x5ea000]%Z
  ++ shkn RF_OFFS
  ++ [KWord (SA (ELit 0) 0xc01cd0) 8 (EVar 1); KWr (SA (ELit 0) 0x5edca8) 232]%Z
  ++ kn_cells rf_cells.

(* [comment removed for export] *)
Definition rf_dirsA : list bool := [false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false; false; false; false; false; false; false; false; true; false; false].
Definition scrR : scripts := SCR rf_dirsA [] [].

(* [comment removed for export] *)
Definition rf_rA := Eval vm_compute in (sym_exec RSEGS FUELR true STOPSR scrR (SS 0x1eef6c rf_sr [] rf_kn 34) []).
Definition rf_cA := Eval vm_compute in (carry (s_log (fst (fst rf_rA))) rf_kn []).
Definition rf_srA : list expr := Eval vm_compute in (s_regs (fst (fst rf_rA))).
Definition rf_knA : list kentry := Eval vm_compute in (fst (fst rf_cA)).
Definition rf_scsA : list sidecond := Eval vm_compute in (snd (fst rf_rA)).
(* [comment removed for export] *)
Definition rf_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 rf_srA rf_knA with Some r => r
   | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end).
(* [comment removed for export] *)
Definition rf_rC := Eval vm_compute in (sym_exec RSEGS FUELR true STOPSR scr0 (SS (sc_ret rf_sc) (sc_sr rf_sc) [] (sc_kn rf_sc) 66) []).
Definition rf_cC := Eval vm_compute in (carry (s_log (fst (fst rf_rC))) (sc_kn rf_sc) []).
Definition rf_srF : list expr := Eval vm_compute in (s_regs (fst (fst rf_rC))).
Definition rf_knF : list kentry := Eval vm_compute in (fst (fst rf_cC)).

(* [comment removed for export] *)
Definition rf_msgZ : list Z := Eval vm_compute in (match kbytes rf_knA (EVar 0) (-464) 38 with Some l => l | None => [] end).

Lemma rf_itinerary :
  s_pc (fst (fst rf_rA)) = 0x56407c%Z /\ snd (fst rf_rA) = rf_scsA /\ snd (fst rf_cA) = []
  /\ stdio_call 34 rf_srA rf_knA = Some rf_sc
  /\ (sc_ret rf_sc, sc_f rf_sc, sc_fd rf_sc, sc_s rf_sc, sc_l rf_sc, sc_wb rf_sc, sc_wp rf_sc)
     = (0x565844%Z, 0x5edca8%Z, 2%Z, ELit 0%Z, ELit 0%Z, EAlu ALU_ADD (EVar 0) (ELit (-464)%Z), EAlu ALU_ADD (EVar 0) (ELit (-426)%Z))
  /\ kbytes rf_knA (EVar 0) (-464) 38 = Some rf_msgZ /\ zbytes rf_msgZ = msg_refused
  /\ s_pc (fst (fst rf_rC)) = AEXIT /\ snd (fst rf_rC) = [] /\ snd (fst rf_cC) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rf_regions : list sregion :=
  [(SA (EVar 0) (- RF_FR), RF_FR); (SA (ELit 0) 0x5edca8, 232)]%Z.

Lemma rf_covA : log_covered rf_regions (s_log (fst (fst rf_rA))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma rf_covC : log_covered rf_regions (s_log (fst (fst rf_rC))) = true. Proof. vm_compute. reflexivity. Qed.

Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev []).

(* [comment removed for export] *)
Lemma rf_scs_ok : forall vals M (sp0 : word),
  vals_ev vals 0 = sp0 -> (ASP_LO <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= ASP_HI)%Z -> (bv_unsigned sp0 mod 16 = 0)%Z ->
  scs_denot RSEGS M (ENV vals) rf_scsA.
Proof.
  intros vals M sp0 P0 Hlo Hhi Hal. unfold ASP_LO, ASP_HI in *. unfold rf_scsA, scs_denot.
  repeat (apply Forall_cons; [cbn [sc_denot edenot ev ENV]; rewrite P0; asc_br |]).
  apply Forall_nil.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
  Variable sp0 : word.
  Variables (L S Zr : list (word * word)).

  Definition rf_regions_w : list (word * Z) :=
    [(Z_to_bv 64 (bv_unsigned sp0 - RF_FR), RF_FR); (Z_to_bv 64 0x5edca8, 232%Z)].

  Lemma rf_regions_denot : forall vals, vals_ev vals 0 = sp0 ->
    (ASP_LO <= bv_unsigned sp0)%Z ->
    map (rdenot (ENV vals)) rf_regions = rf_regions_w.
  Proof.
    intros vals P0 Hlo. unfold ASP_LO in Hlo. unfold rf_regions, rf_regions_w, rdenot, estart, RF_FR.
    cbn [map fst snd a_base a_off edenot ev ENV].
    rewrite P0. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    repeat f_equal; lia.
  Qed.

  Lemma rf_regions_flat : forall vals, vals_ev vals 0 = sp0 ->
    (ASP_LO <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= ASP_HI)%Z ->
    regions_flat (ENV vals) rf_regions.
  Proof.
    intros vals P0 Hlo Hhi r Hr. unfold ASP_LO, ASP_HI in *. unfold rf_regions, RF_FR in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV];
      rewrite ?P0; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
  Qed.

  Theorem rf_sound : forall vals R M msF mo (KX : TSet),
    length vals = 34%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) rf_sr R -> know_ok RSEGS (ENV vals) M rf_kn ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0x1eef6c) M (seg_rom RSEGS) ->
    KX [] ->
    (forall Rj R' M' msF' mo',
       regs_ok (ENV (vals ++ junk_vals Rj)) rf_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' rf_knF ->
       frame_mod M M' rf_regions_w ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst R' (Z_to_bv 64 AEXIT) M' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') KX) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_refused) KX).
  Proof.
    intros vals R M msF mo KX HL P0 HR HK Hfd2 OK RS HKnil HCONT.
    pose proof (know_nth RSEGS _ _ rf_kn 1%nat _ HK eq_refl) as Hrg; cbn [kentry_ok edenot ev ENV] in Hrg; rewrite P0 in Hrg.
    pose proof (know_nth RSEGS _ _ rf_kn 0%nat _ HK eq_refl) as Hal; cbn [kentry_ok edenot ev ENV] in Hal; rewrite P0 in Hal.
    unfold ASP_LO, ASP_HI in Hrg.
    pose proof (rf_regions_flat vals P0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF.
    pose proof (rf_regions_denot vals P0 ltac:(unfold ASP_LO; lia)) as RD.
    pose proof rf_itinerary as (PCA & SCA & CCA & SC & _ & KB & MSGEQ & PCC & SCC & CCC).
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr FUELR STOPSR scrR 0x1eef6c rf_sr rf_kn 34 (fst (fst rf_rA)) (snd (fst rf_rA)) (snd rf_rA)
              (fst (fst rf_cA)) (snd (fst rf_cA)) (snd rf_cA) (ENV vals) M (seg_rom RSEGS) R msF mo);
      [ vm_cast_no_check (@eq_refl _ rf_rA) | vm_cast_no_check (@eq_refl _ rf_cA)
      | exact HR | exact HK
      | rewrite SCA; apply (rf_scs_ok vals M sp0 P0); unfold ASP_LO, ASP_HI; first [lia | exact (proj2 Hal)]
      | rewrite CCA; constructor | exact OK | exact RS | ].
    clear HR HK. intros RA MA msFA moA HR HK EQA LFA OKA SBA HSA RSA.
    pose proof (log_covered_frame (ENV vals) M rf_regions _ rf_covA RF LFA) as FA. rewrite <- EQA, RD in FA.
    change (s_regs (fst (fst rf_rA))) with rf_srA in HR. change (fst (fst rf_cA)) with rf_knA in HK.
    rewrite PCA in RSA.
    (* [comment removed for export] *)
    pose proof (kbytes_rdn_sp (ENV vals) MA rf_knA 0 sp0 (-464) 38 rf_msgZ HK P0 KB ltac:(lia) ltac:(lia)) as MSG.
    rewrite MSGEQ in MSG.
    (* [comment removed for export] *)
    unfold W. rewrite <- (app_nil_r msg_refused).
    apply (stdio_call_sound_post vals (blobs_ev []) rf_srA rf_knA RA MA L S Zr msFA moA rf_sc msg_refused [] KX
             HR HK (eq_trans (f_equal (fun n => stdio_call n rf_srA rf_knA) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn rf_sc edenot ev ENV app];
      change (@length byte msg_refused) with 38%nat; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].
    - rewrite P0, !alu_add, !vadd_wZ. unorm. lia.
    - rewrite P0, !alu_add, !vadd_wZ. unorm. lia.
    - rewrite P0, !alu_add, !vadd_wZ. unorm. lia.
    - reflexivity.
    - lia.
    - right. rewrite P0, !alu_add, !vadd_wZ. unorm. lia.
    - left. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite P0, !alu_add, !vadd_wZ. unorm. lia.
    - change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
    - rewrite P0, !alu_add, !vadd_wZ. unorm. replace (bv_unsigned sp0 + -464)%Z with (bv_unsigned sp0 - 464)%Z in MSG by lia. exact MSG.
    - reflexivity.
    - rewrite (same_but_materialized_fds _ _ SBA). exact Hfd2.
    - exact OKA.
    - exact RSA.
    - exact HKnil.
    - (* [comment removed for export] *)
      clear HR HK. intros Rj MC msFC moC HR HK HPOST OKC SBC HSC RSC.
      assert (FC0 : frame_mod MA MC rf_regions_w).
      { eapply sw_post_frame_mod; [exact HPOST|]. intros x Hx. unfold rf_regions_w, RF_FR in Hx. cbn [outside] in Hx.
        unfold in_rng in Hx. rewrite P0, alu_add, vadd_wZ. revert Hx. unorm. intros (N1 & N2 & _). lia. }
      set (vals' := vals ++ junk_vals Rj) in *.
      assert (HL' : length vals' = 66%nat) by (subst vals'; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      pose proof (rf_regions_flat vals' P0' ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF'.
      pose proof (rf_regions_denot vals' P0' ltac:(unfold ASP_LO; lia)) as RD'.
      change (Env (vals_ev vals') (blobs_ev [])) with (ENV vals') in HR, HK.
      eapply (rz_run_lf_lazy RSEGS L S Zr FUELR STOPSR scr0 0x565844 (sc_sr rf_sc) (sc_kn rf_sc) 66 (fst (fst rf_rC)) (snd (fst rf_rC)) (snd rf_rC)
                (fst (fst rf_cC)) (snd (fst rf_cC)) (snd rf_cC) (ENV vals') MC (seg_rom RSEGS) _ msFC moC);
        [ vm_cast_no_check (@eq_refl _ rf_rC) | vm_cast_no_check (@eq_refl _ rf_cC)
        | exact HR | exact HK | rewrite SCC; constructor | rewrite CCC; constructor | exact OKC | exact RSC | ].
      clear HR HK. intros RC MF msFF moF HR HK EQC LFC OKF SBF HSF RSF.
      pose proof (log_covered_frame (ENV vals') MC rf_regions _ rf_covC RF' LFC) as FC. rewrite <- EQC, RD' in FC.
      change (s_regs (fst (fst rf_rC))) with rf_srF in HR. change (fst (fst rf_cC)) with rf_knF in HK.
      rewrite PCC in RSF.
      apply (HCONT Rj RC MF msFF moF HR HK).
      + eapply frame_mod_trans_same; [exact FA|]. eapply frame_mod_trans_same; [exact FC0 | exact FC].
      + exact OKF.
      + eapply same_but_materialized_trans; [exact SBA|]. eapply same_but_materialized_trans; [exact SBC | exact SBF].
      + eapply hid_same_trans; [exact HSA|]. eapply hid_same_trans; [exact HSC | exact HSF].
      + exact RSF.
  Qed.
End Sound.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Plain.
  Variables (L S Zr : list (word * word)).

  (* [comment removed for export] *)
  Record rfH (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z) : Prop := RFH {
    R2  : getr regs 2 = sp;
    Rsp16 : (bv_unsigned sp mod 16 = 0)%Z;
    RspLo : (ASP_LO <= bv_unsigned sp)%Z;
    RspHi : (bv_unsigned sp <= ASP_HI)%Z;
    Rstk  : stk_ok RSEGS mem sp RF_FR;
    Rimg  : forall i, (0x10000 <= i < 0x195000)%Z -> mem (Z_to_bv 64 i) = None;
    Rgot  : forall i, (0x571000 <= i < 0x5ea000)%Z -> mem (Z_to_bv 64 i) = None;
    Rcells : cells_ok mem rf_cells;
    Rcan  : rdn RSEGS mem (Z_to_bv 64 0xc01cd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    Rcan64 : (0 <= can < 2 ^ 64)%Z;
    Rsh0  : forall a, (2147450880 + (bv_unsigned sp - 4096) / 8 <= a < 2147450880 + bv_unsigned sp / 8)%Z ->
              mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0) }.

  (* [comment removed for export] *)
  Record rfPost (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z)
                (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := RFP {
    P_sp  : getr regs' 2 = sp;
    P_ra  : getr regs' 1 = Z_to_bv 64 0x1eefb8;
    P_a0  : getr regs' 10 = Z_to_bv 64 2;
    P_cs  : forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r;
    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - RF_FR), RF_FR); (Z_to_bv 64 0x5edca8, 232%Z)];
    P_flags : rdn RSEGS mem' (Z_to_bv 64 0x5edca8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    P_rpos  : rdn RSEGS mem' (Z_to_bv 64 0x5edcb0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_rend  : rdn RSEGS mem' (Z_to_bv 64 0x5edcb8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wend  : rdn RSEGS mem' (Z_to_bv 64 0x5edcc8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wpos  : rdn RSEGS mem' (Z_to_bv 64 0x5edcd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wbase : rdn RSEGS mem' (Z_to_bv 64 0x5edce0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_buf   : rdn RSEGS mem' (Z_to_bv 64 0x5edd00) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc02398));
    P_bsz   : rdn RSEGS mem' (Z_to_bv 64 0x5edd08) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_lock  : rdn RSEGS mem' (Z_to_bv 64 0x5edd34) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_can   : rdn RSEGS mem' (Z_to_bv 64 0xc01cd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    P_stk   : stk_ok RSEGS mem' sp RF_FR }.

  Definition rf_vals (regs : bvmap 5 word) (sp : word) (can : Z) : list word :=
    [sp; Z_to_bv 64 can] ++ junk_vals regs.

  Lemma rf_ev_junk : forall regs sp can i, (2 <= i < 34)%nat ->
    ev (ENV (rf_vals regs sp can)) i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2))).
  Proof.
    intros regs sp can i Hi. unfold ENV, rf_vals. cbn [ev]. unfold vals_ev.
    replace i with (length [sp; Z_to_bv 64 can] + (i - 2))%nat at 1 by (cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  Lemma rf_regs_ok : forall regs mem sp can, rfH regs mem sp can ->
    regs_ok (ENV (rf_vals regs sp can)) rf_sr regs.
  Proof.
    intros regs mem sp can PH. destruct PH.
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth rf_sr allregs32 edenot].
    1: apply getr_zero.
    2: cbn [ev ENV]; assumption.
    all: rewrite rf_ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  Lemma rf_know_ok : forall regs mem sp can, rfH regs mem sp can ->
    know_ok RSEGS (ENV (rf_vals regs sp can)) mem rf_kn.
  Proof.
    intros regs mem sp can PH. destruct PH. pose proof (u64_range sp) as Hsp.
    assert (E0 : ev (ENV (rf_vals regs sp can)) 0 = sp) by reflexivity.
    assert (E1 : ev (ENV (rf_vals regs sp can)) 1 = Z_to_bv 64 can) by reflexivity.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0%Z) by reflexivity.
    unfold rf_kn. apply (proj2 (know_ok_app RSEGS _ _ _ _)). split.
    2:{ apply (proj2 (know_ok_app RSEGS _ _ _ _)). split.
        - apply (shkn_ok _ mem sp RF_OFFS E0 RspLo0 RspHi0); [| exact Rsh1].
          unfold RF_OFFS. repeat (apply Forall_cons; [lia|]). apply Forall_nil.
        - apply (proj2 (know_ok_app RSEGS _ _ _ _)). split; [| apply cells_know; [vm_compute; reflexivity | assumption]].
          repeat (apply Forall_cons); [ .. | apply Forall_nil ].
          + eapply (kword_intro RSEGS _ mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | exact E1 | lia | lia | rewrite Z0; lia
              | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; assumption].
          + cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
            split; [lia|]. intros d m Hd Hm. apply store_ok_data. rewrite u64_lit by lia. lia. }
    unfold ASP_LO, ASP_HI in *.
    repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite E0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite E0. unfold ASP_LO, ASP_HI. lia.
    - apply (kwr_of_stk_ok RSEGS _ mem (EVar 0) sp RF_FR); [exact E0 | assumption | unfold RF_FR; lia].
    - apply kimg_intro; [lia | lia | assumption].
    - apply kimg_intro; [lia | lia | assumption].
  Qed.

  (* [comment removed for export] *)
  Theorem as_refused_k : forall regs mem msF mo (sp : word) (can : Z) (KX : TSet),
    rfH regs mem sp can ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0x1eef6c) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    KX [] ->
    (forall regs' mem' msF' mo', rfPost regs mem sp can regs' mem' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst regs' (Z_to_bv 64 AEXIT) mem' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') KX) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_refused) KX).
  Proof.
    intros regs mem msF mo sp can KX PH OK RS Hfd2 HKnil HCONT.
    pose proof (rf_regs_ok regs mem sp can PH) as HR; pose proof (rf_know_ok regs mem sp can PH) as HK.
    destruct PH; pose proof (u64_range sp) as Hsp; unfold ASP_LO, ASP_HI in *.
    apply (rf_sound sp L S Zr (rf_vals regs sp can) regs mem msF mo KX);
      [ unfold rf_vals; rewrite length_app, junk_vals_length; reflexivity | reflexivity | exact HR | exact HK
      | exact Hfd2 | exact OK | exact RS | exact HKnil |].
    clear HR HK; intros Rj R' M' msF' mo' HR HK FM OK' SB' HS' RS'.
    set (vals' := rf_vals regs sp can ++ junk_vals Rj) in *.
    assert (P0 : vals_ev vals' 0 = sp) by reflexivity.
    assert (P1 : vals_ev vals' 1 = Z_to_bv 64 can) by reflexivity.
    assert (PJ : forall i, (2 <= i < 34)%nat -> vals_ev vals' i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2)))).
    { intros i Hi; subst vals'; rewrite vals_ev_app_l by (unfold rf_vals; rewrite length_app, junk_vals_length; cbn; lia).
      apply (rf_ev_junk regs sp can i Hi). }
    apply (HCONT R' M' msF' mo'); [| exact OK' | exact SB' | exact HS' | exact RS']. split.
    - regv HR (2 : reg); exact P0.
    - regv HR (1 : reg); reflexivity.
    - regv HR (10 : reg); reflexivity.
    - intros r Hr; cbn [In] in Hr;
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
        lazymatch goal with |- getr R' ?rr = _ => regv HR rr end; cbn [edenot ev ENV]; rewrite PJ by lia; f_equal; apply bv_eq; reflexivity.
    - exact FM.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - let Hc := fresh "Hc" in krd HK 0xc01cd0%Z 8%nat Hc; rewrite Hc; cbn [ev ENV]; rewrite P1; reflexivity.
    - intros a n Ha Hn; eapply frame_mod_store_ok; [exact FM|].
      match goal with Hs : stk_ok _ mem sp _ |- _ => apply Hs; assumption end.
  Qed.
End Plain.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
