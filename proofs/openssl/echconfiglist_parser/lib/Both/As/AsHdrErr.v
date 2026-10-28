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
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefPrintfLib LibTail
  LazyRestrict LazySR LazyFdNodes LazySym Spec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import RefExitBase RefStdioDefs AsLazyRun AsStdioWrite AsStdioCall AsScLib AsPrintfFirst.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HF_FR : Z := 2400%Z.
Definition STOPSH : list Z := [0x56407c; 0x1eef18]%Z.
Definition FUELH : nat := 8000.

(* [comment removed for export] *)
Definition h_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0
                          | _ => EVar (2 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
Definition hf_cells : list (Z * nat * Z) :=
  [(0x5ea8b0, 8%nat, 0x5654a0)   (* [comment removed for export] *);
   (0x6aa8f8, 8%nat, 0x7fff8000) (* [comment removed for export] *);
   (0x6ab5d8, 1%nat, 0x1)        (* [comment removed for export] *);
   (0x5edca8, 4%nat, 0x5)        (* [comment removed for export] *);
   (0x5edcc8, 8%nat, 0x0)        (* [comment removed for export] *);
   (0x5edcf0, 8%nat, 0x56407c)   (* [comment removed for export] *);
   (0x5edd00, 8%nat, 0xc02398)   (* [comment removed for export] *);
   (0x5edd08, 8%nat, 0x0)        (* [comment removed for export] *);
   (0x5edd20, 4%nat, 0x2)        (* [comment removed for export] *);
   (0x5edd30, 4%nat, 0x0)        (* [comment removed for export] *);
   (0x5edd34, 4%nat, 0xffffffff) (* [comment removed for export] *);
   (0x800008e8, 8%nat, 0x0); (0x800008f0, 8%nat, 0x0)   (* [comment removed for export] *);
   (0x7fffc220, 8%nat, 0x0); (0x7fffc228, 8%nat, 0x0)   (* [comment removed for export] *)]%Z.

Definition h_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) ASP_LO ASP_HI;
   KWr (SA (EVar 0) (- HF_FR)) HF_FR;
   KImg 0x10000 0x195000; KImg 0x571000 0x5ea000;
   KWord (SA (ELit 0) 0xc01cd0) 8 (EVar 1);
   KWr (SA (ELit 0) 0x5edca8) 232]%Z
  ++ kn_cells hf_cells.

Definition sc_dummy : stdio_res := SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [].

(* [comment removed for export] *)
Definition hs_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x1eeedc h_sr [] h_kn 34) []).
Definition hs_cA := Eval vm_compute in (carry (s_log (fst (fst hs_rA))) h_kn []).
Definition hs_srA : list expr := Eval vm_compute in (s_regs (fst (fst hs_rA))).
Definition hs_knA : list kentry := Eval vm_compute in (fst (fst hs_cA)).
Definition hs_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 hs_srA hs_knA with Some r => r | None => sc_dummy end).
Definition hs_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x565528 (sc_sr hs_sc) [] (sc_kn hs_sc) 66) []).
Definition hs_cC := Eval vm_compute in (carry (s_log (fst (fst hs_rC))) (sc_kn hs_sc) []).
Definition hs_srF : list expr := Eval vm_compute in (s_regs (fst (fst hs_rC))).
Definition hs_knF : list kentry := Eval vm_compute in (fst (fst hs_cC)).

Lemma hs_itinerary :
  s_pc (fst (fst hs_rA)) = 0x56407c%Z /\ snd (fst hs_rA) = [] /\ snd (fst hs_cA) = []
  /\ stdio_call 34 hs_srA hs_knA = Some hs_sc
  /\ (sc_ret hs_sc, sc_f hs_sc, sc_fd hs_sc, sc_s hs_sc, sc_l hs_sc) = (0x565528%Z, 0x5edca8%Z, 2%Z, ELit 0x44788%Z, ELit 31%Z)
  /\ s_pc (fst (fst hs_rC)) = 0x1eef18%Z /\ snd (fst hs_rC) = [] /\ snd (fst hs_cC) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Definition ho_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x1eeef8 h_sr [] h_kn 34) []).
Definition ho_cA := Eval vm_compute in (carry (s_log (fst (fst ho_rA))) h_kn []).
Definition ho_srA : list expr := Eval vm_compute in (s_regs (fst (fst ho_rA))).
Definition ho_knA : list kentry := Eval vm_compute in (fst (fst ho_cA)).
Definition ho_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 ho_srA ho_knA with Some r => r | None => sc_dummy end).
Definition ho_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x565528 (sc_sr ho_sc) [] (sc_kn ho_sc) 66) []).
Definition ho_cC := Eval vm_compute in (carry (s_log (fst (fst ho_rC))) (sc_kn ho_sc) []).
Definition ho_srF : list expr := Eval vm_compute in (s_regs (fst (fst ho_rC))).
Definition ho_knF : list kentry := Eval vm_compute in (fst (fst ho_cC)).

Lemma ho_itinerary :
  s_pc (fst (fst ho_rA)) = 0x56407c%Z /\ snd (fst ho_rA) = [] /\ snd (fst ho_cA) = []
  /\ stdio_call 34 ho_srA ho_knA = Some ho_sc
  /\ (sc_ret ho_sc, sc_f ho_sc, sc_fd ho_sc, sc_s ho_sc, sc_l ho_sc) = (0x565528%Z, 0x5edca8%Z, 2%Z, ELit 0x21138%Z, ELit 31%Z)
  /\ s_pc (fst (fst ho_rC)) = 0x1eef18%Z /\ snd (fst ho_rC) = [] /\ snd (fst ho_cC) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma msg_short_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x44788) 31 = Some msg_short.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_overrun_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x21138) 31 = Some msg_overrun.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_short_len : length msg_short = 31%nat. Proof. reflexivity. Qed.
Lemma msg_overrun_len : length msg_overrun = 31%nat. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition h_regions : list sregion :=
  [(SA (EVar 0) (- HF_FR), HF_FR); (SA (ELit 0) 0x5edca8, 232)]%Z.

Lemma hs_covA : log_covered h_regions (s_log (fst (fst hs_rA))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma hs_covC : log_covered h_regions (s_log (fst (fst hs_rC))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma ho_covA : log_covered h_regions (s_log (fst (fst ho_rA))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma ho_covC : log_covered h_regions (s_log (fst (fst ho_rC))) = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
  Variable sp0 : word.
  Variables (L S Zr : list (word * word)).

  Definition h_regions_w : list (word * Z) :=
    [(Z_to_bv 64 (bv_unsigned sp0 - HF_FR), HF_FR); (Z_to_bv 64 0x5edca8, 232%Z)].

  Lemma h_regions_denot : forall vals, vals_ev vals 0 = sp0 ->
    (ASP_LO <= bv_unsigned sp0)%Z ->
    map (rdenot (ENV vals)) h_regions = h_regions_w.
  Proof.
    intros vals P0 Hlo. unfold ASP_LO in Hlo. unfold h_regions, h_regions_w, rdenot, estart, HF_FR.
    cbn [map fst snd a_base a_off edenot ev ENV].
    rewrite P0. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    repeat f_equal; lia.
  Qed.

  Lemma h_regions_flat : forall vals, vals_ev vals 0 = sp0 ->
    (ASP_LO <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= ASP_HI)%Z ->
    regions_flat (ENV vals) h_regions.
  Proof.
    intros vals P0 Hlo Hhi r Hr. unfold ASP_LO, ASP_HI in *. unfold h_regions, HF_FR in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV];
      rewrite ?P0; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac hf_sound pcA rA cA srA knA sc rC cC srF knF ITIN COVA COVC MSG_IMG MSG_LEN msg :=
    intros vals R M msF mo K HL P0 HR HK Hfd2 OK RS HKnil HCONT;
    pose proof (know_nth RSEGS _ _ h_kn 1%nat _ HK eq_refl) as Hrg; cbn [kentry_ok edenot ev ENV] in Hrg; rewrite P0 in Hrg;
    unfold ASP_LO, ASP_HI in Hrg;
    pose proof (h_regions_flat vals P0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF;
    pose proof (h_regions_denot vals P0 ltac:(unfold ASP_LO; lia)) as RD;
    pose proof ITIN as (PCA & SCA & CCA & SC & _ & PCC & SCC & CCC);
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr FUELH STOPSH scr0 pcA h_sr h_kn 34 (fst (fst rA)) (snd (fst rA)) (snd rA)
              (fst (fst cA)) (snd (fst cA)) (snd cA) (ENV vals) M (seg_rom RSEGS) R msF mo);
      [ vm_cast_no_check (@eq_refl _ rA) | vm_cast_no_check (@eq_refl _ cA)
      | exact HR | exact HK | rewrite SCA; constructor | rewrite CCA; constructor | exact OK | exact RS | ];
    clear HR HK; intros RA MA msFA moA HR HK EQA LFA OKA SBA HSA RSA;
    pose proof (log_covered_frame (ENV vals) M h_regions _ COVA RF LFA) as FA; rewrite <- EQA, RD in FA;
    change (s_regs (fst (fst rA))) with srA in HR; change (fst (fst cA)) with knA in HK;
    rewrite PCA in RSA;
    (* [comment removed for export] *)
    apply (stdio_call_sound_post vals (blobs_ev []) srA knA RA MA L S Zr msFA moA sc [] msg K
             HR HK (eq_trans (f_equal (fun n => stdio_call n srA knA) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn sc edenot ev ENV app];
      rewrite ?MSG_LEN; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
    [ unorm; lia
    | unorm; lia
    | unorm; lia
    | unorm; reflexivity
    | lia
    | left; rewrite P0, alu_add, vadd_wZ; unorm; lia
    | left; rewrite P0, alu_add, vadd_wZ; unorm; lia
    | unorm; lia
    | unorm; reflexivity
    | (* [comment removed for export] *)
      lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) 31 = _ =>
        rewrite (kimg_rdn RSEGS (ENV vals) _ knA ltac:(let i := kidx knA (is_kimg_cov a 31) in exact i)
                   _ _ a 31 HK eq_refl) by (cbn; lia) end;
      apply MSG_IMG
    | rewrite (same_but_materialized_fds _ _ SBA); exact Hfd2
    | exact OKA
    | exact RSA
    | exact HKnil
    | (* [comment removed for export] *)
      clear HR HK; intros Rj MC msFC moC HR HK HPOST OKC SBC HSC RSC;
      assert (FC0 : frame_mod MA MC h_regions_w);
      [ eapply sw_post_frame_mod; [exact HPOST|]; intros x Hx; unfold h_regions_w, HF_FR in Hx; cbn [outside] in Hx;
        unfold in_rng in Hx; rewrite P0, alu_add, vadd_wZ; revert Hx; unorm; intros (N1 & N2 & _); lia |];
      set (vals' := vals ++ junk_vals Rj) in *;
      assert (HL' : length vals' = 66%nat) by (subst vals'; rewrite length_app, junk_vals_length, HL; reflexivity);
      assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0);
      pose proof (h_regions_flat vals' P0' ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF';
      pose proof (h_regions_denot vals' P0' ltac:(unfold ASP_LO; lia)) as RD';
      change (Env (vals_ev vals') (blobs_ev [])) with (ENV vals') in HR, HK;
      eapply (rz_run_lf_lazy RSEGS L S Zr FUELH STOPSH scr0 0x565528 (sc_sr sc) (sc_kn sc) 66 (fst (fst rC)) (snd (fst rC)) (snd rC)
                (fst (fst cC)) (snd (fst cC)) (snd cC) (ENV vals') MC (seg_rom RSEGS) _ msFC moC);
        [ vm_cast_no_check (@eq_refl _ rC) | vm_cast_no_check (@eq_refl _ cC)
        | exact HR | exact HK | rewrite SCC; constructor | rewrite CCC; constructor | exact OKC | exact RSC | ];
      clear HR HK; intros RC MF msFF moF HR HK EQC LFC OKF SBF HSF RSF;
      pose proof (log_covered_frame (ENV vals') MC h_regions _ COVC RF' LFC) as FC; rewrite <- EQC, RD' in FC;
      change (s_regs (fst (fst rC))) with srF in HR; change (fst (fst cC)) with knF in HK;
      rewrite PCC in RSF;
      apply (HCONT Rj RC MF msFF moF HR HK);
      [ eapply frame_mod_trans_same; [exact FA|]; eapply frame_mod_trans_same; [exact FC0 | exact FC]
      | exact OKF
      | eapply same_but_materialized_trans; [exact SBA|]; eapply same_but_materialized_trans; [exact SBC | exact SBF]
      | eapply hid_same_trans; [exact HSA|]; eapply hid_same_trans; [exact HSC | exact HSF]
      | exact RSF ] ].

  Theorem hs_sound : forall vals R M msF mo (K : TSet),
    length vals = 34%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) h_sr R -> know_ok RSEGS (ENV vals) M h_kn ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0x1eeedc) M (seg_rom RSEGS) ->
    K [] ->
    (forall Rj R' M' msF' mo',
       regs_ok (ENV (vals ++ junk_vals Rj)) hs_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' hs_knF ->
       frame_mod M M' h_regions_w ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst R' (Z_to_bv 64 0x1eef18) M' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_short) K).
  Proof.
    unfold W.
    hf_sound 0x1eeedc%Z hs_rA hs_cA hs_srA hs_knA hs_sc hs_rC hs_cC hs_srF hs_knF
             hs_itinerary hs_covA hs_covC msg_short_img msg_short_len msg_short.
  Qed.

  Theorem ho_sound : forall vals R M msF mo (K : TSet),
    length vals = 34%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) h_sr R -> know_ok RSEGS (ENV vals) M h_kn ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0x1eeef8) M (seg_rom RSEGS) ->
    K [] ->
    (forall Rj R' M' msF' mo',
       regs_ok (ENV (vals ++ junk_vals Rj)) ho_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' ho_knF ->
       frame_mod M M' h_regions_w ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst R' (Z_to_bv 64 0x1eef18) M' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_overrun) K).
  Proof.
    unfold W.
    hf_sound 0x1eeef8%Z ho_rA ho_cA ho_srA ho_knA ho_sc ho_rC ho_cC ho_srF ho_knF
             ho_itinerary ho_covA ho_covC msg_overrun_img msg_overrun_len msg_overrun.
  Qed.
End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Plain.
  Variables (L S Zr : list (word * word)).

  (* [comment removed for export] *)
  Record hfH (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z) : Prop := HFH {
    H2  : getr regs 2 = sp;
    Hsp16 : (bv_unsigned sp mod 16 = 0)%Z;
    HspLo : (ASP_LO <= bv_unsigned sp)%Z;
    HspHi : (bv_unsigned sp <= ASP_HI)%Z;
    Hstk  : stk_ok RSEGS mem sp HF_FR;
    Himg  : forall i, (0x10000 <= i < 0x195000)%Z -> mem (Z_to_bv 64 i) = None;
    Hgot  : forall i, (0x571000 <= i < 0x5ea000)%Z -> mem (Z_to_bv 64 i) = None;
    Hcells : cells_ok mem hf_cells;
    Hcan  : rdn RSEGS mem (Z_to_bv 64 0xc01cd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    Hcan64 : (0 <= can < 2 ^ 64)%Z }.

  (* [comment removed for export] *)
  Record hfPost (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z)
                (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := HFP {
    P_sp  : getr regs' 2 = sp;
    P_a0  : getr regs' 10 = Z_to_bv 64 1;
    P_cs  : forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r;
    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - HF_FR), HF_FR); (Z_to_bv 64 0x5edca8, 232%Z)];
    P_flags : rdn RSEGS mem' (Z_to_bv 64 0x5edca8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    P_rpos  : rdn RSEGS mem' (Z_to_bv 64 0x5edcb0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_rend  : rdn RSEGS mem' (Z_to_bv 64 0x5edcb8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wend  : rdn RSEGS mem' (Z_to_bv 64 0x5edcc8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc02398));
    P_wpos  : rdn RSEGS mem' (Z_to_bv 64 0x5edcd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc02398));
    P_wbase : rdn RSEGS mem' (Z_to_bv 64 0x5edce0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc02398));
    P_mode  : rdn RSEGS mem' (Z_to_bv 64 0x5edd30) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_lock  : rdn RSEGS mem' (Z_to_bv 64 0x5edd34) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_can   : rdn RSEGS mem' (Z_to_bv 64 0xc01cd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    P_stk   : stk_ok RSEGS mem' sp HF_FR }.

  Definition h_vals (regs : bvmap 5 word) (sp : word) (can : Z) : list word :=
    [sp; Z_to_bv 64 can] ++ junk_vals regs.

  Lemma h_ev_junk : forall regs sp can i, (2 <= i < 34)%nat ->
    ev (ENV (h_vals regs sp can)) i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2))).
  Proof.
    intros regs sp can i Hi. unfold ENV, h_vals. cbn [ev]. unfold vals_ev.
    replace i with (length [sp; Z_to_bv 64 can] + (i - 2))%nat at 1 by (cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  Lemma h_regs_ok : forall regs mem sp can, hfH regs mem sp can ->
    regs_ok (ENV (h_vals regs sp can)) h_sr regs.
  Proof.
    intros regs mem sp can PH. destruct PH.
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth h_sr allregs32 edenot].
    1: apply getr_zero.
    2: cbn [ev ENV]; assumption.
    all: rewrite h_ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  Lemma h_know_ok : forall regs mem sp can, hfH regs mem sp can ->
    know_ok RSEGS (ENV (h_vals regs sp can)) mem h_kn.
  Proof.
    intros regs mem sp can PH. destruct PH. pose proof (u64_range sp) as Hsp.
    assert (E0 : ev (ENV (h_vals regs sp can)) 0 = sp) by reflexivity.
    assert (E1 : ev (ENV (h_vals regs sp can)) 1 = Z_to_bv 64 can) by reflexivity.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0%Z) by reflexivity.
    unfold ASP_LO, ASP_HI in *.
    unfold h_kn. apply (proj2 (know_ok_app RSEGS _ _ _ _)). split; [| apply cells_know; [vm_compute; reflexivity | assumption]].
    repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite E0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite E0. unfold ASP_LO, ASP_HI. lia.
    - apply (kwr_of_stk_ok RSEGS _ mem (EVar 0) sp HF_FR); [exact E0 | assumption | unfold HF_FR; lia].
    - apply kimg_intro; [lia | lia | assumption].
    - apply kimg_intro; [lia | lia | assumption].
    - eapply (kword_intro RSEGS _ mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | exact E1 | lia | lia | rewrite Z0; lia
        | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; assumption].
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply store_ok_data. rewrite u64_lit by lia. lia.
  Qed.

  Ltac hf_plain SOUND :=
    intros regs mem msF mo sp can K PH OK RS Hfd2 HKnil HCONT;
    pose proof (h_regs_ok regs mem sp can PH) as HR; pose proof (h_know_ok regs mem sp can PH) as HK;
    destruct PH; pose proof (u64_range sp) as Hsp; unfold ASP_LO, ASP_HI in *;
    apply (SOUND sp L S Zr (h_vals regs sp can) regs mem msF mo K);
      [ unfold h_vals; rewrite length_app, junk_vals_length; reflexivity | reflexivity | exact HR | exact HK
      | exact Hfd2 | exact OK | exact RS | exact HKnil |];
    clear HR HK; intros Rj R' M' msF' mo' HR HK FM OK' SB' HS' RS';
    set (vals' := h_vals regs sp can ++ junk_vals Rj) in *;
    assert (P0 : vals_ev vals' 0 = sp) by reflexivity;
    assert (P1 : vals_ev vals' 1 = Z_to_bv 64 can) by reflexivity;
    assert (PJ : forall i, (2 <= i < 34)%nat -> vals_ev vals' i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2))));
    [ intros i Hi; subst vals'; rewrite vals_ev_app_l by (unfold h_vals; rewrite length_app, junk_vals_length; cbn; lia);
      apply (h_ev_junk regs sp can i Hi) |];
    apply (HCONT R' M' msF' mo'); [| exact OK' | exact SB' | exact HS' | exact RS']; split;
    [ regv HR (2 : reg); exact P0
    | regv HR (10 : reg); reflexivity
    | intros r Hr; cbn [In] in Hr;
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
        lazymatch goal with |- getr R' ?rr = _ => regv HR rr end; cbn [edenot ev ENV]; rewrite PJ by lia; f_equal; apply bv_eq; reflexivity
    | exact FM
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | let Hc := fresh "Hc" in krd HK 0xc01cd0%Z 8%nat Hc; rewrite Hc; cbn [ev ENV]; rewrite P1; reflexivity
    | intros a n Ha Hn; eapply frame_mod_store_ok; [exact FM|];
      match goal with Hs : stk_ok _ mem sp _ |- _ => apply Hs; assumption end ].

  Theorem as_hdr_short_fwrite : forall regs mem msF mo (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0x1eeedc) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst regs' (Z_to_bv 64 0x1eef18) mem' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_short) K).
  Proof. hf_plain hs_sound. Qed.

  Theorem as_hdr_overrun_fwrite : forall regs mem msF mo (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0x1eeef8) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst regs' (Z_to_bv 64 0x1eef18) mem' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_overrun) K).
  Proof. hf_plain ho_sound. Qed.
End Plain.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
