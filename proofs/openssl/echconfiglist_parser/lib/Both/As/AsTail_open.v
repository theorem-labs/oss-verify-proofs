(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 SymAux LibKnowFrame MemSplit LibTail RefMemcpyLib
  SReach RegsEquivM MainEqv HeapCeil LazyRestrict LazySR MainMem Spec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Arr Step Frame MState Exec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsanMemcpyBase AsanMemcpy.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsStack0 AsMemchr N6_rip
  AsLazyRun AsPrintfFirst AsSxKit AsScLib AsDrvMem AsDrvCells AsStdioWrite AsStdioCall AsExitDefs AsExit AsTailExit
  AsStrnlenK AsFprintfS_open AsTail_open_defs.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev []).

Definition PRE17 : list byte := s2b "cli: cannot open "%string.
Lemma PRE17_words :
  word_to_le_bytes 8 (Z_to_bv 64 7953747406983097443) ++ word_to_le_bytes 8 (Z_to_bv 64 7954887939408031598)
  ++ word_to_le_bytes 1 (Z_to_bv 64 32) = PRE17.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma PRE17_len : length PRE17 = 17%nat. Proof. reflexivity. Qed.
Lemma nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x3d337) 1 = Some [Z_to_bv 8 10]. Proof. vm_compute. reflexivity. Qed.
Lemma pre17_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x3d324) 17 = Some PRE17. Proof. vm_compute. reflexivity. Qed.
Lemma NL_word : word_to_le_bytes 1 (Z_to_bv 64 10) = [Z_to_bv 8 10]. Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.

Section Tail.
  Variables (L S Zr : list (word * word)).
  Variable sp0 : word.                 (* [comment removed for export] *)
  Variable mem0 : word -> option byte. (* [comment removed for export] *)
  Variable mo0 : Model.
  Variables (pp : word) (path t8 : list byte) (can : Z).
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hfd2 : fd_lookup (m_fds mo0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  (* [comment removed for export] *)
  Hypothesis Hstk : stk asegs mem0 (bv_unsigned sp0 - 128 - OT_FR) (bv_unsigned sp0 - 128).
  Hypothesis Hgot : forall i, 0x571000 <= i < 0x5ea000 -> mem0 (Z_to_bv 64 i) = None.
  Hypothesis Hac : ACONST mem0.
  Hypothesis Hinv : mem_inv asegs mem0.
  Hypothesis Hcells : cells_ok mem0 ot_cells.
  Hypothesis Hcan : rdn RSEGS mem0 (Z_to_bv 64 0xc01cd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).
  Hypothesis Hcan64 : 0 <= can < 2 ^ 64.
  (* [comment removed for export] *)
  Hypothesis Hstr : rdn RSEGS mem0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]).
  Hypothesis Ht8 : rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8.
  Hypothesis Hnonul : ~ In (Z_to_bv 8 0) path.
  Hypothesis HppLo : bv_unsigned sp0 <= bv_unsigned pp.
  Hypothesis HppHi : bv_unsigned pp + Z.of_nat (length path) + 17 <= AAPP_HI.
  (* [comment removed for export] *)
  Hypothesis Hsh0 : forall a, ASHADOW_BASE + (bv_unsigned sp0 - 128 - 65536) / 8 <= a < ASHADOW_BASE + 2^44 ->
                    mem0 (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
  (* [comment removed for export] *)
  Variables (tid : Z) (ro wpw : word).
  Hypothesis HexitH : exitH mem0 (Z_to_bv 64 (bv_unsigned sp0 - 128)) tid ro wpw.

  Let SPlo : 0x7fff80000000 <= bv_unsigned sp0 := proj1 Hvsp.
  Let SPhi : bv_unsigned sp0 <= 0x800000000000 := proj1 (proj2 Hvsp).
  Let SPal : bv_unsigned sp0 mod 16 = 0 := proj2 (proj2 Hvsp).
  Notation P := (Z.of_nat (length path)).
  Notation spm := (Z_to_bv 64 (bv_unsigned sp0 - 128)).

  (* [comment removed for export] *)
  Record tst (msF : machine_state) (mo : Model) (M : word -> option byte) : Prop := TST {
    t_ok : lzok RSEGS L S Zr (mkCfg msF mo);
    t_sb : same_but_materialized mo0 mo;
    t_fm : frame_mod mem0 M (tail_regions spm OT_FR) }.

  Lemma spm_u : bv_unsigned spm = bv_unsigned sp0 - 128.
  Proof. pose proof SPlo. apply u_small. lia. Qed.

  (* [comment removed for export] *)
  Definition ot_regions : list sregion := [(SA (EVar 0) (-128 - OT_FR), OT_FR); (SA (ELit 0) 0x5edca8, 232)].

  Lemma ot_regions_denot : forall vals, vals_ev vals 0 = sp0 -> map (rdenot (ENV vals)) ot_regions = tail_regions spm OT_FR.
  Proof.
    intros vals P0. pose proof SPlo. unfold ot_regions, tail_regions, rdenot, estart, OT_FR.
    cbn [map fst snd a_base a_off edenot ev ENV]. rewrite P0, spm_u. change (bv_unsigned (Z_to_bv 64 0)) with 0. repeat f_equal; lia.
  Qed.
  Lemma ot_regions_flat : forall vals, vals_ev vals 0 = sp0 -> regions_flat (ENV vals) ot_regions.
  Proof.
    intros vals P0 r Hr. pose proof SPlo. pose proof SPhi. unfold ot_regions, OT_FR in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV]; rewrite ?P0;
      try change (bv_unsigned (Z_to_bv 64 0)) with 0; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma tfacts : forall M, frame_mod mem0 M (tail_regions spm OT_FR) ->
    stk asegs M (bv_unsigned sp0 - 128 - OT_FR) (bv_unsigned sp0 - 128) /\ mem_inv asegs M /\ ACONST M
    /\ (forall i, 0x571000 <= i < 0x5ea000 -> M (Z_to_bv 64 i) = None)
    /\ rdn RSEGS M (Z_to_bv 64 0xc01cd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can))
    /\ rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])
    /\ rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8
    /\ (forall a, ASHADOW_BASE + (bv_unsigned sp0 - 128 - 65536) / 8 <= a < ASHADOW_BASE + 2^44 -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
  Proof.
    intros M FM. pose proof SPlo. pose proof SPhi. pose proof (u64_range pp). unfold AAPP_HI in HppHi.
    assert (RS : forall r, In r (tail_regions spm OT_FR) ->
              (bv_unsigned (fst r) = bv_unsigned sp0 - 128 - OT_FR /\ snd r = OT_FR) \/ (bv_unsigned (fst r) = 0x5edca8 /\ snd r = 232)).
    { intros r Hr. unfold tail_regions in Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd];
        rewrite ?spm_u; unfold OT_FR; unorm; lia. }
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    - eapply astk_grows; [exact Hstk | unfold OT_FR; lia | lia | exact (proj2 FM)].
    - eapply amem_inv_frame; [exact Hinv | exact FM |]. apply Forall_forall. intros r Hr. destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; unfold OT_FR; lia.
    - eapply ACONST_frame; [exact Hac | apply frame_mod_munch; exact FM | apply (aframe_mod_wmono _ _ _ FM) |].
      unfold ivls, tail_regions, OT_FR. cbn [map fst snd]. rewrite spm_u. unorm.
      constructor; [|constructor; [|constructor]].
      + apply aconst_ok_high; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; change (12599296 / 8) with 1574912; lia | lia].
      + apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
          AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP; rewrite ?ASHADOW_BASE_val; cbn; lia.
    - eapply arange_none_frame; [exact Hgot | exact FM | | lia | lia]. intros r Hr. destruct (RS r Hr) as [[-> ->]|[-> ->]]; unfold OT_FR; lia.
    - eapply ardn_frame; [exact FM | exact Hcan | lia | cbn; lia |]. intros r Hr. destruct (RS r Hr) as [[-> ->]|[-> ->]]; cbn; unfold OT_FR; lia.
    - rewrite <- (Z_to_bv_bv_unsigned pp). eapply ardn_frame; [exact FM | rewrite Z_to_bv_bv_unsigned; exact Hstr | lia | lia |].
      intros r Hr. destruct (RS r Hr) as [[-> ->]|[-> ->]]; unfold OT_FR; lia.
    - eapply ardn_frame; [exact FM | exact Ht8 | lia | cbn; lia |]. intros r Hr. destruct (RS r Hr) as [[-> ->]|[-> ->]]; cbn; unfold OT_FR; lia.
    - intros a Ha. rewrite (proj1 FM); [apply Hsh0; exact Ha|]. apply outside_tail; unfold ASP_LO, OT_FR; rewrite ?spm_u, ?ASHADOW_BASE_val in *; try lia.
      all: Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac tblk r FX scr pc sr kn nx E M R msF mo HR HK SCS OK RS :=
    pose proof FX as (SC0 & CC0 & LC0);
    eapply (rz_run_lf_lazy RSEGS L S Zr FUELT STOPT scr pc sr kn nx (fst (fst r)) (snd (fst r)) (snd r)
              (fst (fst (carry (s_log (fst (fst r))) kn []))) (snd (fst (carry (s_log (fst (fst r))) kn []))) (snd (carry (s_log (fst (fst r))) kn []))
              E M (seg_rom RSEGS) R msF mo);
      [ vm_cast_no_check (@eq_refl _ r) | destruct (carry (s_log (fst (fst r))) kn []) as [[? ?] ?]; reflexivity
      | exact HR | exact HK | rewrite SC0; SCS | rewrite CC0; constructor | exact OK | exact RS | clear SC0 CC0 ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_I_gen : forall (rX : sym_state * list sidecond * scripts) (srX : list expr) (knX : list kentry),
    sym_exec RSEGS FUELT true STOPT scr0 (SS 0x565844 srX [] knX 291) [] = rX ->
    snd (fst rX) = [] -> snd (fst (carry (s_log (fst (fst rX))) knX [])) = [] -> log_covered ot_regions (s_log (fst (fst rX))) = true ->
    s_pc (fst (fst rX)) = AEXIT ->
    let srY := s_regs (fst (fst rX)) in let knY := fst (fst (carry (s_log (fst (fst rX))) knX [])) in
    sr_get srY 2%bv = spx (-128) -> sr_get srY 4%bv = ELit 0xbe1c90 -> sr_get srY 10%bv = ELit 2 ->
    kread RSEGS knY (ELit 0) 0x5edcd0 8 = Some (ELit 0) -> kread RSEGS knY (ELit 0) 0x5edce0 8 = Some (ELit 0) ->
    kread RSEGS knY (ELit 0) 0x5edcb0 8 = Some (ELit 0) -> kread RSEGS knY (ELit 0) 0x5edcb8 8 = Some (ELit 0) ->
    kread RSEGS knY (ELit 0) 0x5edd34 4 = Some (ELit 4294967295) ->
    forall vals R M msF mo,
    length vals = 291%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srX R -> know_ok RSEGS (ENV vals) M knX -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 0x565844) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_exit (exit_code 2) (m_fs mo0)).
  Proof.
    intros rX srX knX EX SC CC LC PC srY knY Y2 Y4 Y10 K1 K2 K3 K4 K5 vals R M msF mo HL P0 HR HK [OK SB FM] RS.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SPal as Hal.
    eapply (rz_run_lf_lazy RSEGS L S Zr FUELT STOPT scr0 0x565844 srX knX 291 (fst (fst rX)) (snd (fst rX)) (snd rX)
              knY (snd (fst (carry (s_log (fst (fst rX))) knX []))) (snd (carry (s_log (fst (fst rX))) knX [])) (ENV vals) M (seg_rom RSEGS) R msF mo);
      [ rewrite <- EX; destruct (sym_exec _ _ _ _ _ _ _) as [[? ?] ?]; reflexivity
      | subst knY; destruct (carry (s_log (fst (fst rX))) knX []) as [[? ?] ?]; reflexivity
      | exact HR | exact HK | rewrite SC; constructor | rewrite CC; constructor | exact OK | exact RS | ].
    clear HR HK OK RS. intros R' M' msF' mo' HR HK EQ LF OK' SB' HS' RS'.
    pose proof (log_covered_frame (ENV vals) M ot_regions _ LC (ot_regions_flat vals P0) LF) as F'.
    rewrite <- EQ, (ot_regions_denot vals P0) in F'. rewrite PC in RS'.
    assert (FM' : frame_mod mem0 M' (tail_regions spm OT_FR)) by (eapply frame_mod_trans_same; [exact FM | exact F']).
    destruct (tfacts M' FM') as (ST' & INV' & AC' & GOT' & CAN' & _).
    rewrite <- (same_but_materialized_fs _ _ (same_but_materialized_trans _ _ _ SB SB')).
    assert (KR : forall a n v, kread RSEGS knY (ELit 0) a n = Some (ELit v) -> (1 <= n <= 8)%nat -> 0 <= a -> a + 8 < 2 ^ 64 ->
                 rdn RSEGS M' (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v))).
    { intros a n v Hk Hn Ha Ha'. pose proof (kread_rdn RSEGS (ENV vals) M' knY (ELit 0) a n (ELit v) HK Hk ltac:(lia) ltac:(lia)
        ltac:(unfold flat, estart; cbn [a_base a_off edenot]; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia)) as X.
      unfold adenot, v_addi in X. cbn [a_base a_off edenot] in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X. rewrite Z.add_0_l in X. exact X. }
    apply (tail_exit2 L S Zr R' mem0 M' msF' mo' spm OT_FR tid can ro wpw (Z_to_bv 64 0) (Z_to_bv 64 0) HexitH);
      [ rewrite spm_u; rewrite <- Zminus_mod_idemp_l, Hal; reflexivity
      | unfold ASP_LO; rewrite spm_u; lia | unfold ASP_HI; rewrite spm_u; lia
      | apply (amem_inv_ro_none mem0 Hinv) | exact Hgot | exact FM' | unfold OT_FR; lia
      | eapply astk_stk_ok; [exact ST' | rewrite spm_u; unfold OT_FR; lia | rewrite spm_u; lia | lia | lia]
      | exact Hcan64 | exact CAN'
      | apply (KR _ _ _ K1); lia | apply (KR _ _ _ K2); lia | apply (KR _ _ _ K3); lia | apply (KR _ _ _ K4); lia | apply (KR _ _ _ K5); lia
      | rewrite (HR 2%bv), Y2; unfold spx; cbn [edenot ev ENV]; rewrite P0, alu_add, vadd_wZ; f_equal; lia
      | rewrite (HR 4%bv), Y4; reflexivity | rewrite (HR 10%bv), Y10; reflexivity
      | exact OK' | exact RS' ].
  Qed.

  Lemma seg_I : forall vals R M msF mo,
    length vals = 291%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srI0 R -> know_ok RSEGS (ENV vals) M knI0 -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 0x565844) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_exit (exit_code 2) (m_fs mo0)).
  Proof. apply (seg_I_gen rI srI0 knI0); vm_compute; reflexivity. Qed.
  Lemma seg_I3 : forall vals R M msF mo,
    length vals = 291%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srI30 R -> know_ok RSEGS (ENV vals) M knI30 -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 0x565844) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_exit (exit_code 2) (m_fs mo0)).
  Proof. apply (seg_I_gen rI3 srI30 knI30); vm_compute; reflexivity. Qed.
  Lemma seg_I4 : forall vals R M msF mo,
    length vals = 291%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srI40 R -> know_ok RSEGS (ENV vals) M knI40 -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 0x565844) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_exit (exit_code 2) (m_fs mo0)).
  Proof. apply (seg_I_gen rI4 srI40 knI40); vm_compute; reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac buf_prefix HK P0 Mq H17 :=
    let Hw0 := fresh "Hw0" in let Hw1 := fresh "Hw1" in let Hw2 := fresh "Hw2" in
    krdv HK 0%nat (-592) 8%nat Hw0; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia|];
    krdv HK 0%nat (-584) 8%nat Hw1; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia|];
    krdv HK 0%nat (-576) 1%nat Hw2; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia|];
    unfold adenot, v_addi in Hw0, Hw1, Hw2; cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2; rewrite P0 in Hw0, Hw1, Hw2;
    assert (H17 : rdn RSEGS Mq (Z_to_bv 64 (bv_unsigned sp0 + -592)) 17 = Some PRE17);
    [ rewrite <- PRE17_words; change 17%nat with (8 + (8 + 1))%nat;
      apply rdn_app_Z; [exact Hw0 | | lia | lia];
      apply rdn_app_Z; [ | | lia | lia];
      [ replace (bv_unsigned sp0 + -592 + Z.of_nat 8) with (bv_unsigned sp0 + -584) by lia; exact Hw1
      | replace (bv_unsigned sp0 + -592 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp0 + -576) by lia; exact Hw2 ]
    | clear Hw0 Hw1 Hw2 ].

  (* [comment removed for export] *)
  Lemma buf_fact_block : forall vals M log (a : Z) n v,
    vals_ev vals 0 = sp0 -> log_out_b 0 (BUF_LO + NPRE) BUF_HI IHI log = true ->
    bv_unsigned sp0 + (BUF_LO + NPRE) <= a -> a + Z.of_nat n <= bv_unsigned sp0 + BUF_HI ->
    rdn RSEGS M (Z_to_bv 64 a) n = v -> rdn RSEGS (mem_denot (ENV vals) M log) (Z_to_bv 64 a) n = v.
  Proof.
    intros vals M log a n v P0 LO Ha Hn Hr. pose proof SPlo. pose proof SPhi. unfold BUF_LO, BUF_HI, NPRE, IHI in *.
    rewrite (rdn_mem_denot_out RSEGS (ENV vals) M log 0 (-592 + 17) (-512) 0x80000000);
      [exact Hr | exact LO | unfold win_ok; cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; unorm; lia | cbn [ev ENV]; rewrite P0; unorm; lia].
  Qed.

  Lemma seg_H : forall vals R M msF mo, 0 <= P <= 62 ->
    length vals = 259%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 141 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srH0 R -> know_ok RSEGS (ENV vals) M knH0 -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 AMEMCPY_RET) M (seg_rom RSEGS) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 575)) (length path) = Some path ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 575 + P)) 1 = Some [Z_to_bv 8 10] ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs mo0))).
  Proof.
    intros vals R M msF mo HP HL P0 P141 HR HK [OK SB FM] RS SBp SBn.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp). unfold AAPP_HI in HppHi.
    pose proof ot_itinerary as (_ & IT & _ & _ & SCALL & _). apply (f_equal (fun t => snd (snd (snd (fst t))))) in IT || idtac.
    tblk rH factsH scr0 AMEMCPY_RET srH0 knH0 259%nat (ENV vals) M R msF mo HR HK ltac:(constructor) OK RS.
    clear HR HK OK RS. intros R' M' msF' mo' HR HK EQ LF OK' SB' HS' RS'.
    pose proof (log_covered_frame (ENV vals) M ot_regions _ LC0 (ot_regions_flat vals P0) LF) as F'.
    rewrite <- EQ, (ot_regions_denot vals P0) in F'. clear LC0 LF.
    replace (s_pc (fst (fst rH))) with ASTDIO_WRITE in RS' by (vm_compute; reflexivity).
    assert (SBp' : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 - 575)) (length path) = Some path).
    { rewrite EQ. apply buf_fact_block; [exact P0 | vm_compute; reflexivity | unfold BUF_LO, NPRE; lia | unfold BUF_HI; lia | exact SBp]. }
    assert (SBn' : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 - 575 + P)) 1 = Some [Z_to_bv 8 10]).
    { rewrite EQ. apply buf_fact_block; [exact P0 | vm_compute; reflexivity | unfold BUF_LO, NPRE; lia | unfold BUF_HI; cbn; lia | exact SBn]. }
    clear EQ SBp SBn.
    buf_prefix HK P0 M' H17.
    assert (MSG : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -592)) (17 + (length path + 1)) = Some (msg_cannot_open path)).
    { unfold msg_cannot_open. change (s2b _) with PRE17.
      apply rdn_app_Z; [exact H17 | | lia | lia]. apply rdn_app_Z; [| | lia | lia].
      + replace (bv_unsigned sp0 + -592 + Z.of_nat 17) with (bv_unsigned sp0 - 575) by lia. exact SBp'.
      + replace (bv_unsigned sp0 + -592 + Z.of_nat 17 + Z.of_nat (length path)) with (bv_unsigned sp0 - 575 + P) by lia. exact SBn'. }
    assert (LEN : length (msg_cannot_open path) = (17 + (length path + 1))%nat) by (unfold msg_cannot_open; rewrite !length_app; reflexivity).
    replace (W 2 (msg_cannot_open path)) with (map (WriteEv (Z_to_bv 64 2)) (msg_cannot_open path ++ [])) by (unfold W; rewrite app_nil_r; reflexivity).
    assert (FM' : frame_mod mem0 M' (tail_regions spm OT_FR)) by (eapply frame_mod_trans_same; [exact FM | exact F']).
    lazymatch goal with |- realizes _ (mkCfg ?msFc ?moc) _ =>
    apply (stdio_call_sound_post vals (blobs_ev []) srH knH R' M' L S Zr msFc moc scOF (msg_cannot_open path) []
             (t_exit (exit_code 2) (m_fs mo0)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH knH) HL) SCALL));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scOF]; rewrite ?LEN end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P141). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P141). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P141). unorm. lia.
    - cbn [edenot length]. reflexivity.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P141). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P141). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P141). unorm. exact MSG.
    - reflexivity.
    - rewrite (same_but_materialized_fds _ _ (same_but_materialized_trans _ _ _ SB SB')) || rewrite <- (same_but_materialized_fds _ _ (same_but_materialized_trans _ _ _ SB SB')). exact Hfd2.
    - exact OK'.
    - exact RS'.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 msF2 mo2 HR HK HPOST OK2 SB2 HS2 RS2.
      change (Env (vals_ev (vals ++ junk_vals R2)) (blobs_ev [])) with (ENV (vals ++ junk_vals R2)) in HR, HK.
      eapply (seg_I (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK | | exact RS2 ].
      split; [exact OK2 | |].
      + eapply same_but_materialized_trans; [exact SB|]. eapply same_but_materialized_trans; [exact SB' | exact SB2].
      + eapply frame_mod_trans_same; [exact FM'|]. eapply sw_post_frame_mod; [exact HPOST|].
        intros x Hx. unfold tail_regions, OT_FR in Hx. cbn [OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.outside] in Hx. unfold OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.in_rng in Hx. rewrite spm_u in Hx.
        ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). revert Hx. unorm. intros (N1 & N2 & _). lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition shxg (X : expr) : expr := EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL X (ELit 3)) (ELit 2147450880)) (ELit (-8)).
  Lemma shxg_denot : forall E X x, bv_unsigned (edenot E X) = x -> bv_unsigned (edenot E (shxg X)) = shw8 x.
  Proof.
    intros E X x HX. pose proof (u64_range (edenot E X)) as R. rewrite HX in R. unfold shxg, shw8. cbn [edenot]. cbn [alu64 alu].
    rewrite bv_and_unsigned, bv_add_unsigned, bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, HX.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
    change (3 mod 2 ^ 64)%Z with 3%Z. change (63 mod 2 ^ 64)%Z with 63%Z.
    change (Z.land 3 63) with 3%Z. change (2147450880 mod 2 ^ 64)%Z with 2147450880%Z.
    change ((-8) mod 2 ^ 64)%Z with 18446744073709551608%Z.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3)%Z with 8%Z. rewrite ASHADOW_BASE_val.
    rewrite (Z.mod_small (_ / 8 + _)) by (Z.div_mod_to_equations; lia).
    rewrite land_m8' by (Z.div_mod_to_equations; lia). reflexivity.
  Qed.
  Lemma shprobe_ok : forall E M X x (Z0 : Z),
    bv_unsigned (edenot E X) = x -> 2 ^ 46 <= x -> x < AAPP_HI ->
    (forall a, Z0 <= a < ASHADOW_BASE + 2 ^ 44 -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) ->
    Z0 <= shw8 x ->
    kentry_ok RSEGS E M (KRange (shxg X) 0x20000000000 0x10007fff8000) /\ kentry_ok RSEGS E M (KZero (SA (shxg X) 0) (ELit 8)).
  Proof.
    intros E M X x Z0 HX Hlo Hhi Hz HZ0. pose proof (shxg_denot E X x HX) as HS.
    pose proof (shw8_eq x ltac:(lia)) as EQ. rewrite ASHADOW_BASE_val in *. unfold AAPP_HI in Hhi.
    split.
    - apply krange_intro. rewrite HS. Z.div_mod_to_equations. lia.
    - eapply (kzero_intro RSEGS E M (shxg X) (edenot E (shxg X)) 0 (ELit 8) 8);
        [reflexivity | reflexivity | rewrite HS; lia | lia | rewrite HS; Z.div_mod_to_equations; lia |].
      intros i Hi. rewrite HS. apply Hz. Z.div_mod_to_equations. lia.
  Qed.
  Lemma know_ok_filter : forall E M f kn, know_ok RSEGS E M kn -> know_ok RSEGS E M (List.filter f kn).
  Proof. intros E M f kn HK. unfold know_ok in *. rewrite Forall_forall in *. intros k Hk. apply filter_In in Hk as [Hk _]. auto. Qed.
  Lemma know_ok_app2 : forall E M k1 k2, know_ok RSEGS E M k1 -> know_ok RSEGS E M k2 -> know_ok RSEGS E M (k1 ++ k2).
  Proof. intros. unfold know_ok in *. apply Forall_app. auto. Qed.

  Lemma px_range_ok : forall vals M lo hi kn,
    vals_ev vals 141 = Z_to_bv 64 P -> lo <= P <= hi ->
    know_ok RSEGS (ENV vals) M kn -> know_ok RSEGS (ENV vals) M (px_range lo hi kn).
  Proof.
    intros vals M lo hi kn P141 HP HK. pose proof (u64_range pp). unfold AAPP_HI in HppHi.
    unfold px_range. constructor; [|apply know_ok_filter; exact HK].
    apply krange_intro. unfold PX. cbn [edenot ev ENV]. rewrite P141, u_small by lia. lia.
  Qed.

  Lemma kn_readd_ok : forall vals M lo hi kn,
    vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 141 = Z_to_bv 64 P -> lo <= P <= hi ->
    (forall a, ASHADOW_BASE + (bv_unsigned sp0 - 128 - 65536) / 8 <= a < ASHADOW_BASE + 2^44 -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) ->
    know_ok RSEGS (ENV vals) M kn -> know_ok RSEGS (ENV vals) M (kn_readd lo hi kn).
  Proof.
    intros vals M lo hi kn P0 P2 P141 HP SH HK. pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hpp.
    unfold AAPP_HI in HppHi.
    unfold kn_readd. apply px_range_ok; [exact P141 | exact HP |].
    set (Z0 := ASHADOW_BASE + (bv_unsigned sp0 - 128 - 65536) / 8) in SH.
    assert (SHP : forall X x, bv_unsigned (edenot (ENV vals) X) = x -> bv_unsigned sp0 - 600 <= x -> x < AAPP_HI ->
              kentry_ok RSEGS (ENV vals) M (KRange (shxg X) 0x20000000000 0x10007fff8000)
              /\ kentry_ok RSEGS (ENV vals) M (KZero (SA (shxg X) 0) (ELit 8))).
    { intros X x HX Hx1 Hx2. apply (shprobe_ok (ENV vals) M X x Z0 HX ltac:(lia) Hx2 SH).
      subst Z0. rewrite shw8_eq by lia. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
    destruct (SHP (EAlu ALU_ADD (EAlu ALU_ADD (EVar 2) (EVar 141)) (ELit (-1))) (bv_unsigned pp + P - 1)) as [A1 A2];
      [ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P2, ?P141); unorm; lia | lia | unfold AAPP_HI; lia |].
    destruct (SHP (EVar 2) (bv_unsigned pp)) as [B1 B2]; [cbn [edenot ev ENV]; rewrite P2; reflexivity | lia | unfold AAPP_HI; lia |].
    destruct (SHP (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-576))) (bv_unsigned sp0 + P - 576)) as [C1 C2];
      [ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P2, ?P141); unorm; lia | lia | unfold AAPP_HI; lia |].
    destruct (SHP (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-575))) (bv_unsigned sp0 + P - 575)) as [D1 D2];
      [ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P2, ?P141); unorm; lia | lia | unfold AAPP_HI; lia |].
    change (shxkn OT_SHX ++ shkn OT_SHOFFS2 ++ kn) with
      (KRange (shxg (EAlu ALU_ADD (EAlu ALU_ADD (EVar 2) (EVar 141)) (ELit (-1)))) 0x20000000000 0x10007fff8000
       :: KZero (SA (shxg (EAlu ALU_ADD (EAlu ALU_ADD (EVar 2) (EVar 141)) (ELit (-1)))) 0) (ELit 8)
       :: KRange (shxg (EVar 2)) 0x20000000000 0x10007fff8000 :: KZero (SA (shxg (EVar 2)) 0) (ELit 8)
       :: KRange (shxg (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-576)))) 0x20000000000 0x10007fff8000
       :: KZero (SA (shxg (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-576)))) 0) (ELit 8)
       :: KRange (shxg (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-575)))) 0x20000000000 0x10007fff8000
       :: KZero (SA (shxg (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-575)))) 0) (ELit 8)
       :: (shkn OT_SHOFFS2 ++ kn)).
    constructor; [exact A1|]. constructor; [exact A2|]. constructor; [exact B1|]. constructor; [exact B2|].
    constructor; [exact C1|]. constructor; [exact C2|]. constructor; [exact D1|]. constructor; [exact D2|].
    apply know_ok_app2; [|exact HK].
    apply (shkn_ok (ENV vals) M sp0 OT_SHOFFS2); [cbn [ev ENV]; exact P0 | unfold ASP_LO; lia | unfold ASP_HI; lia
      | unfold OT_SHOFFS2; repeat constructor; lia |].
    intros a Ha. apply SH. subst Z0. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition keptI : list reg := [1; 2; 3; 4; 8; 9; 10; 18; 21; 22; 23; 24; 25; 26; 27]%bv.
  Lemma keptI_MCI : map ridx keptI = KEPT_MCI. Proof. vm_compute. reflexivity. Qed.
  Lemma kept_MC : map ridx callee_kept = KEPT_MC. Proof. reflexivity. Qed.
  Lemma keptI_sub : forall r : reg, In r keptI -> In r callee_kept.
  Proof using can Hcan64.
    intros r Hr. unfold keptI in Hr. unfold callee_kept. cbn [In] in Hr |- *.
    repeat (destruct Hr as [<-|Hr]; [(first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])])|]). destruct Hr.
  Qed.
  Lemma keptI_no0 : ~ In (0%bv : reg) keptI.
  Proof. unfold keptI. cbn [In]. intros Hin. repeat (destruct Hin as [E|Hin]; [apply (f_equal bv_unsigned) in E; discriminate E|]). exact Hin. Qed.

  (* [comment removed for export] *)
  Lemma call_memcpy : forall vals sr R M msF mo (dst src : word) n bs (kept : list reg) T,
    regs_ok (ENV vals) sr R -> lzok RSEGS L S Zr (mkCfg msF mo) ->
    restrict L S msF = mkst R (Z_to_bv 64 AMEMCPY) M (seg_rom RSEGS) ->
    mcH M dst src n bs ->
    getr R 1 = Z_to_bv 64 AMEMCPY_RET -> getr R 10 = dst -> getr R 11 = src -> getr R 12 = Z_to_bv 64 n ->
    sr_vars_lt (length vals) sr = true -> (forall r, In r kept -> In r callee_kept) -> ~ In 0%bv kept ->
    (forall R2 msF2 mo2,
       regs_ok (ENV (vals ++ junk_vals R2)) (sr_after_call_j sr (map ridx kept) (length vals)) R2 ->
       lzok RSEGS L S Zr (mkCfg msF2 mo2) -> same_but_materialized mo mo2 ->
       restrict L S msF2 = mkst R2 (Z_to_bv 64 AMEMCPY_RET) (wbytes M dst bs) (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF2 mo2) T) ->
    realizes RSEGS (mkCfg msF mo) T.
  Proof.
    intros vals sr R M msF mo dst src n bs kept T HR OK RS MC G1 G10 G11 G12 VL KS K0 CONT.
    destruct (ref_memcpy M dst src n bs (seg_rom RSEGS) MC R (Z_to_bv 64 AMEMCPY_RET) ltac:(apply ret_ok_even; reflexivity) G1 G10 G11 G12)
      as (R2 & Hms & Hkeep).
    replace (Z_to_bv 64 AMEMCPY) with (@BV 64 0x5699dc I) in RS by (apply bv_eq; reflexivity).
    eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact OK | exact RS | exact Hms |]. clear Hms RS.
    intros msF2 mo2 OK2 SB2 HS2 RS2.
    apply (CONT R2 msF2 mo2); [| exact OK2 | exact SB2 | exact RS2].
    apply (regs_after_keeps vals (blobs_ev []) sr R R2 kept VL HR); [| exact K0].
    intros r Hr. apply Hkeep. apply KS. exact Hr.
  Qed.

  (* [comment removed for export] *)
  Lemma tst_memcpy : forall msF mo M (dst : word) bs msF2 mo2,
    tst msF mo M -> lzok RSEGS L S Zr (mkCfg msF2 mo2) -> same_but_materialized mo mo2 ->
    bv_unsigned sp0 - 128 - OT_FR <= bv_unsigned dst -> bv_unsigned dst + Z.of_nat (length bs) <= bv_unsigned sp0 - 128 ->
    tst msF2 mo2 (wbytes M dst bs).
  Proof.
    intros msF mo M dst bs msF2 mo2 [OK SB FM] OK2 SB2 D1 D2. pose proof SPlo. pose proof SPhi.
    split; [exact OK2 | eapply same_but_materialized_trans; [exact SB | exact SB2] |].
    eapply frame_mod_trans_same; [exact FM|].
    eapply frame_mod_weaken; [| apply frame_mod_wbytes; lia].
    intros a Ha. pose proof (u64_range a).
    unfold tail_regions in Ha. cbn [OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.outside] in Ha |- *.
    unfold OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.in_rng in Ha |- *. rewrite ?spm_u in Ha. cbn [fst snd] in Ha. unfold OT_FR in *.
    revert Ha. unorm. intros Ha. split; [lia | exact I].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_G : forall vals R M msF mo, 0 <= P <= 62 ->
    length vals = 227%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 141 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 AMEMCPY_RET) M (seg_rom RSEGS) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 575)) (length path) = Some path ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs mo0))).
  Proof.
    intros vals R M msF mo HP HL P0 P2 P141 HR HK TS RS SBp. pose proof TS as [OK SB FM].
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hpp. unfold AAPP_HI in HppHi.
    (* [comment removed for export] *)
    tblk rG factsG (SCR [false] [] []) AMEMCPY_RET srG0 knG0 227%nat (ENV vals) M R msF mo HR HK
         ltac:(constructor; [|constructor]; unfold sc_denot; cbn [edenot ev ENV]; rewrite P0, P141;
               apply bt_ltu_not_false; rewrite ?alu_add, ?vadd_wZ; unorm; lia) OK RS.
    clear HR HK OK RS. intros R' M' msF' mo' HR HK EQ LF OK' SB' HS' RS'.
    pose proof (log_covered_frame (ENV vals) M ot_regions _ LC0 (ot_regions_flat vals P0) LF) as F'.
    rewrite <- EQ, (ot_regions_denot vals P0) in F'. clear LC0 LF.
    replace (s_pc (fst (fst rG))) with AMEMCPY in RS' by (vm_compute; reflexivity).
    replace (fst (fst (carry (s_log (fst (fst rG))) knG0 []))) with knG in HK by (vm_compute; reflexivity).
    assert (SBp' : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 - 575)) (length path) = Some path).
    { rewrite EQ. apply buf_fact_block; [exact P0 | vm_compute; reflexivity | unfold BUF_LO, NPRE; lia | unfold BUF_HI; lia | exact SBp]. }
    clear EQ SBp.
    assert (FM' : frame_mod mem0 M' (tail_regions spm OT_FR)) by (eapply frame_mod_trans_same; [exact FM | exact F']).
    assert (TS' : tst msF' mo' M') by (split; [exact OK' | eapply same_but_materialized_trans; [exact SB | exact SB'] | exact FM']).
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 575 + P)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x3d337) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kimg_cov 0x3d337 1) in exact i)
                 _ _ 0x3d337 1 HK eq_refl) by (cbn; lia). apply nl_img. }
    assert (Hdst : store_ok RSEGS M' dst 1 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kwr_cov (EVar 0) (-575) 64) in exact i)
                    _ _ _ (-575 + P) 1 HK eq_refl ltac:(unfold OT_FR; lia) ltac:(unfold OT_FR; cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 575 + P)%Z with (bv_unsigned sp0 + (-575 + P))%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x3d337) 1 [Z_to_bv 8 10]).
    { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    apply (call_memcpy vals _ R' M' msF' mo' dst (Z_to_bv 64 0x3d337) 1 [Z_to_bv 8 10] callee_kept _ HR OK' RS' MC);
      [ regv HR (1%bv : reg); apply bv_eq; reflexivity
      | regv HR (10%bv : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P141); f_equal; lia
      | regv HR (11%bv : reg); reflexivity | regv HR (12%bv : reg); reflexivity
      | rewrite HL; vm_compute; reflexivity | intros r Hr; exact Hr | exact callee_kept_no0 |].
    clear HR OK' RS'. intros R2 msF2 mo2 HR OK2 SB2 RS2.
    rewrite kept_MC, HL in HR. change (sr_after_call_j (s_regs (fst (fst rG))) KEPT_MC 227) with srH0 in HR.
    (* [comment removed for export] *)
    assert (TS2 : tst msF2 mo2 (wbytes M' dst [Z_to_bv 8 10])).
    { eapply tst_memcpy; [exact TS' | exact OK2 | exact SB2 | subst dst; unfold OT_FR; unorm; lia | subst dst; cbn [length]; unorm; lia]. }
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst [Z_to_bv 8 10]) 0 (BUF_LO + NPRE) BUF_HI IHI knG
                  ltac:(unfold win_ok, BUF_LO, BUF_HI, NPRE, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst [Z_to_bv 8 10] (ENV vals) 0 (BUF_LO + NPRE) BUF_HI);
                        cbn [ev ENV length]; rewrite P0; subst dst; unfold BUF_LO, BUF_HI, NPRE; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK.
    pose proof (kn_readd_ok vals (wbytes M' dst [Z_to_bv 8 10]) 0 62 _ P0 P2 P141 HP
                  ltac:(destruct (tfacts _ (t_fm _ _ _ TS2)) as (_ & _ & _ & _ & _ & _ & _ & SH); exact SH) HK2) as HK.
    clear HK2. change (kn_readd 0 62 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knG)) with knH0 in HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev []) _ knH0 ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    change (Env (vals_ev (vals ++ junk_vals R2)) (blobs_ev [])) with (ENV (vals ++ junk_vals R2)) in HR, HK.
    eapply (seg_H (vals ++ junk_vals R2));
      [ exact HP | rewrite length_app, junk_vals_length, HL; reflexivity
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P141
      | exact HR | exact HK | exact TS2 | exact RS2 | | ].
    - (* [comment removed for export] *)
      rewrite CatExec.rdn_wbytes_out; [exact SBp' | | |]; cbn [length]; subst dst; rewrite ?u_small by lia; lia.
    - (* [comment removed for export] *)
      subst dst. pose proof (rdn_wbytes_hit RSEGS [Z_to_bv 8 10] M' (Z_to_bv 64 (bv_unsigned sp0 - 575 + P))) as Hn.
      cbn [length] in Hn. apply Hn. rewrite u_small by lia. lia.
  Qed.
  Definition atG (lo hi : Z) (knX : list kentry) (T : TSet) : Prop :=
    forall vals R M msF mo,
      length vals = 227%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 141 = Z_to_bv 64 P ->
      regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knX -> tst msF mo M ->
      restrict L S msF = mkst R (Z_to_bv 64 AMEMCPY_RET) M (seg_rom RSEGS) ->
      rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 575)) (length path) = Some path ->
      realizes RSEGS (mkCfg msF mo) T.
  Lemma bt_ltu_not_false0 : forall (x : word) n,
    bv_unsigned x + n <= 2 ^ 64 - 1 -> 0 <= n ->
    branch_taken BC_LTU (alu64 ALU_XOR x (Z_to_bv 64 (-1))) (Z_to_bv 64 n) = false.
  Proof.
    intros x n H1 Hn. cbn [branch_taken alu64 alu]. unfold bv_ltu. apply Z.ltb_ge.
    rewrite bv_xor_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    pose proof (u64_range x) as Hx.
    change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite lxor_ones64 by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma bt_geu_true : forall a b : word, bv_unsigned b <= bv_unsigned a -> branch_taken BC_GEU a b = true.
  Proof. intros a b H. cbn [branch_taken]. unfold bv_ltu. apply Bool.negb_true_iff. apply Z.ltb_ge. exact H. Qed.
  Lemma bt_eq_false : forall a b : word, bv_unsigned a <> bv_unsigned b -> branch_taken BC_EQ a b = false.
  Proof. intros a b H. cbn [branch_taken]. unfold bv_eqb. apply Z.eqb_neq. exact H. Qed.
  Lemma bt_ltu_false : forall a b : word, bv_unsigned b <= bv_unsigned a -> branch_taken BC_LTU a b = false.
  Proof. intros a b H. cbn [branch_taken]. unfold bv_ltu. apply Z.ltb_ge. exact H. Qed.
  Lemma seg_F_gen : forall lo hi T vals R M msF mo, 1 <= P <= 63 -> lo <= P <= hi ->
    length vals = 195%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 141 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knF0_ -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 AMEMCPY_RET) M (seg_rom RSEGS) ->
    atG lo hi (kn_readd lo hi (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF)) T ->
    realizes RSEGS (mkCfg msF mo) T.
  Proof.
    intros lo hi T vals R M msF mo HP HPl HL P0 P2 P141 HR HK TS RS CONT. pose proof TS as [OK SB FM].
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hpp. unfold AAPP_HI in HppHi.
    assert (Psmall : (bv_unsigned (edenot (ENV vals) (EVar 141)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite P141, u_small by lia. lia. }
    (* [comment removed for export] *)
    tblk rF factsF (SCR [true; false; true; false; false] [] []) AMEMCPY_RET srF0 knF0_ 195%nat (ENV vals) M R msF mo HR HK
         ltac:(unfold scs_denot;
               apply Forall_cons; [unfold sc_denot; cbn [edenot ev ENV]; rewrite P0, P141; apply bt_ltu_not_false; lia|];
               apply Forall_cons; [unfold sc_denot; cbn [edenot ev ENV]; rewrite P2, P141; apply bt_ltu_not_false0; lia|];
               apply Forall_cons; [unfold sc_denot; cbn [edenot ev ENV]; rewrite P0, P2, P141; apply bt_geu_true;
                                   rewrite ?alu_add, ?vadd_wZ, ?vadd_ZZ; unorm; lia|];
               apply Forall_cons; [unfold sc_denot; cbn [edenot ev ENV]; rewrite P0, P2; apply bt_eq_false; rewrite ?alu_add, ?vadd_wZ; unorm; lia|];
               apply Forall_cons; [unfold sc_denot; rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _)
                                     by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall);
                                   cbn [branch_taken]; unfold bv_lts; rewrite Z.ltb_irrefl; reflexivity|];
               apply Forall_nil) OK RS.
    clear HR HK OK RS. intros R' M' msF' mo' HR HK EQ LF OK' SB' HS' RS'.
    pose proof (log_covered_frame (ENV vals) M ot_regions _ LC0 (ot_regions_flat vals P0) LF) as F'.
    rewrite <- EQ, (ot_regions_denot vals P0) in F'. clear LC0 LF EQ.
    replace (s_pc (fst (fst rF))) with AMEMCPY in RS' by (vm_compute; reflexivity).
    replace (fst (fst (carry (s_log (fst (fst rF))) knF0_ []))) with knF in HK by (vm_compute; reflexivity).
    assert (FM' : frame_mod mem0 M' (tail_regions spm OT_FR)) by (eapply frame_mod_trans_same; [exact FM | exact F']).
    assert (TS' : tst msF' mo' M') by (split; [exact OK' | eapply same_but_materialized_trans; [exact SB | exact SB'] | exact FM']).
    destruct (tfacts M' FM') as (_ & _ & _ & _ & _ & Hstr' & _ & _).
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 575)).
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    assert (Hdst : store_ok RSEGS M' dst (length path) = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-575) 64) in exact i)
                    _ _ _ (-575) (length path) HK eq_refl ltac:(unfold OT_FR; lia) ltac:(unfold OT_FR; cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 575)%Z with (bv_unsigned sp0 + -575)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst pp P path).
    { constructor; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    apply (call_memcpy vals _ R' M' msF' mo' dst pp P path keptI _ HR OK' RS' MC);
      [ regv HR (1%bv : reg); apply bv_eq; reflexivity
      | regv HR (10%bv : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia
      | regv HR (11%bv : reg); cbn [edenot ev ENV]; exact P2 | regv HR (12%bv : reg); cbn [edenot ev ENV]; exact P141
      | rewrite HL; vm_compute; reflexivity | exact keptI_sub | exact keptI_no0 |].
    clear HR OK' RS'. intros R2 msF2 mo2 HR OK2 SB2 RS2.
    rewrite keptI_MCI, HL in HR. change (sr_after_call_j (s_regs (fst (fst rF))) KEPT_MCI 195) with srG0 in HR.
    assert (TS2 : tst msF2 mo2 (wbytes M' dst path)).
    { eapply tst_memcpy; [exact TS' | exact OK2 | exact SB2 | subst dst; unfold OT_FR; unorm; lia | subst dst; unorm; lia]. }
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst path) 0 (BUF_LO + NPRE) BUF_HI IHI knF
                  ltac:(unfold win_ok, BUF_LO, BUF_HI, NPRE, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst path (ENV vals) 0 (BUF_LO + NPRE) BUF_HI);
                        cbn [ev ENV]; rewrite P0; subst dst; unfold BUF_LO, BUF_HI, NPRE; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev []) _ (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF)
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2. change (Env (vals_ev (vals ++ junk_vals R2)) (blobs_ev [])) with (ENV (vals ++ junk_vals R2)) in HR, HK.
    assert (Q0 : vals_ev (vals ++ junk_vals R2) 0 = sp0) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev (vals ++ junk_vals R2) 2 = pp) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q141 : vals_ev (vals ++ junk_vals R2) 141 = Z_to_bv 64 P) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P141).
    pose proof (kn_readd_ok (vals ++ junk_vals R2) (wbytes M' dst path) lo hi _ Q0 Q2 Q141 HPl
                  ltac:(destruct (tfacts _ (t_fm _ _ _ TS2)) as (_ & _ & _ & _ & _ & _ & _ & SH); exact SH) HK) as HK2.
    clear HK. rename HK2 into HK.
    eapply (CONT (vals ++ junk_vals R2));
      [ rewrite length_app, junk_vals_length, HL; reflexivity | exact Q0 | exact Q2 | exact Q141
      | exact HR | exact HK | exact TS2 | exact RS2 | ].
    subst dst. apply rdn_wbytes_hit. unorm. lia.
  Qed.
  Lemma seg_F : forall vals R M msF mo, 1 <= P <= 62 ->
    length vals = 195%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 141 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knF0_ -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 AMEMCPY_RET) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs mo0))).
  Proof.
    intros vals R M msF mo HP HL P0 P2 P141 HR HK TS RS.
    eapply (seg_F_gen 0 62 _ vals); try eassumption; [lia | lia |].
    intros vals' R' M' msF' mo' HL' Q0 Q2 Q141 HR' HK' TS' RS' SB. eapply (seg_G vals'); try eassumption. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_H3 : forall vals R M msF mo,
    length vals = 259%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srH30 R -> know_ok RSEGS (ENV vals) M knH30 -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 (sc_ret scG3)) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_exit (exit_code 2) (m_fs mo0)).
  Proof.
    intros vals R M msF mo HL P0 HR HK [OK SB FM] RS.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp). unfold AAPP_HI in HppHi.
    pose proof ot_itinerary as (_ & _ & _ & _ & _ & _ & SCALL & _).
    tblk rH3 factsH3 scr0 (sc_ret scG3) srH30 knH30 259%nat (ENV vals) M R msF mo HR HK ltac:(constructor) OK RS.
    clear HR HK OK RS. intros R' M' msF' mo' HR HK EQ LF OK' SB' HS' RS'.
    pose proof (log_covered_frame (ENV vals) M ot_regions _ LC0 (ot_regions_flat vals P0) LF) as F'.
    rewrite <- EQ, (ot_regions_denot vals P0) in F'. clear LC0 LF EQ.
    replace (s_pc (fst (fst rH3))) with ASTDIO_WRITE in RS' by (vm_compute; reflexivity).
    assert (FM' : frame_mod mem0 M' (tail_regions spm OT_FR)) by (eapply frame_mod_trans_same; [exact FM | exact F']).
    apply (rz_conseq RSEGS _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ [])) (t_exit (exit_code 2) (m_fs mo0)))).
    2:{ cbn [map app]. apply t_emit_nil_eq. apply t_exit_has_nil. }
    lazymatch goal with |- realizes _ (mkCfg ?msFc ?moc) _ =>
    apply (stdio_call_sound_post vals (blobs_ev []) srH3 knH3 R' M' L S Zr msFc moc scH3 [] []
             (t_exit (exit_code 2) (m_fs mo0)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH3 knH3) HL) SCALL));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH3 length Z.of_nat] end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. apply u_small. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - reflexivity.
    - reflexivity.
    - rewrite (same_but_materialized_fds _ _ (same_but_materialized_trans _ _ _ SB SB')) || rewrite <- (same_but_materialized_fds _ _ (same_but_materialized_trans _ _ _ SB SB')). exact Hfd2.
    - exact OK'.
    - exact RS'.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 msF2 mo2 HR HK HPOST OK2 SB2 HS2 RS2.
      change (Env (vals_ev (vals ++ junk_vals R2)) (blobs_ev [])) with (ENV (vals ++ junk_vals R2)) in HR, HK.
      eapply (seg_I3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK | | exact RS2 ].
      split; [exact OK2 | |].
      + eapply same_but_materialized_trans; [exact SB|]. eapply same_but_materialized_trans; [exact SB' | exact SB2].
      + eapply frame_mod_trans_same; [exact FM'|]. eapply sw_post_frame_mod; [exact HPOST|].
        intros x Hx. unfold tail_regions, OT_FR in Hx. cbn [OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.outside] in Hx. unfold OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.in_rng in Hx. rewrite spm_u in Hx.
        ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). revert Hx. unorm. intros (N1 & N2 & _). lia.
  Qed.
  Lemma seg_G3 : forall vals R M msF mo, P = 63 ->
    length vals = 227%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 141 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG30 -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 AMEMCPY_RET) M (seg_rom RSEGS) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 575)) (length path) = Some path ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs mo0))).
  Proof.
    intros vals R M msF mo HP HL P0 P2 P141 HR HK [OK SB FM] RS SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hpp. unfold AAPP_HI in HppHi.
    pose proof ot_itinerary as (_ & _ & _ & _ & _ & SCALL & _).
    (* [comment removed for export] *)
    tblk rG3 factsG3 scr0 AMEMCPY_RET srG0 knG30 227%nat (ENV vals) M R msF mo HR HK ltac:(constructor) OK RS.
    clear HR HK OK RS. intros R' M' msF' mo' HR HK EQ LF OK' SB' HS' RS'.
    pose proof (log_covered_frame (ENV vals) M ot_regions _ LC0 (ot_regions_flat vals P0) LF) as F'.
    rewrite <- EQ, (ot_regions_denot vals P0) in F'. clear LC0 LF.
    replace (s_pc (fst (fst rG3))) with ASTDIO_WRITE in RS' by (vm_compute; reflexivity).
    replace (fst (fst (carry (s_log (fst (fst rG3))) knG30 []))) with knG3 in HK by (vm_compute; reflexivity).
    assert (SBp' : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 - 575)) (length path) = Some path).
    { rewrite EQ. apply buf_fact_block; [exact P0 | vm_compute; reflexivity | unfold BUF_LO, NPRE; lia | unfold BUF_HI; lia | exact SBp]. }
    clear EQ SBp.
    assert (FM' : frame_mod mem0 M' (tail_regions spm OT_FR)) by (eapply frame_mod_trans_same; [exact FM | exact F']).
    buf_prefix HK P0 M' H17.
    assert (B80 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -592)) (17 + length path) = Some (PRE17 ++ path)).
    { apply rdn_app_Z; [exact H17 | | lia | lia].
      replace (bv_unsigned sp0 + -592 + Z.of_nat 17)%Z with (bv_unsigned sp0 - 575)%Z by lia. exact SBp'. }
    assert (Hnl : rdn RSEGS M' (Z_to_bv 64 0x3d337) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knG3 ltac:(let i := kidx knG3 (is_kimg_cov 0x3d337 1) in exact i)
                 _ _ 0x3d337 1 HK eq_refl) by (cbn; lia). apply nl_img. }
    (* [comment removed for export] *)
    unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W.
    lazymatch goal with |- realizes _ (mkCfg ?msFc ?moc) _ =>
    apply (stdio_call_sound_post vals (blobs_ev []) srG3 knG3 R' M' L S Zr msFc moc scG3 (PRE17 ++ path) [Z_to_bv 8 10]
             (t_exit (exit_code 2) (m_fs mo0)) HR HK (eq_trans (f_equal (fun n => stdio_call n srG3 knG3) HL) SCALL));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scG3];
      rewrite ?length_app, ?PRE17_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P141). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P141). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P141). unorm. lia.
    - cbn [edenot length]. apply u_small. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P141). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P141). unorm. exact B80.
    - cbn [edenot]. exact Hnl.
    - rewrite (same_but_materialized_fds _ _ (same_but_materialized_trans _ _ _ SB SB')) || rewrite <- (same_but_materialized_fds _ _ (same_but_materialized_trans _ _ _ SB SB')). exact Hfd2.
    - exact OK'.
    - exact RS'.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 msF2 mo2 HR HK HPOST OK2 SB2 HS2 RS2.
      change (Env (vals_ev (vals ++ junk_vals R2)) (blobs_ev [])) with (ENV (vals ++ junk_vals R2)) in HR, HK.
      eapply (seg_H3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK | | exact RS2 ].
      split; [exact OK2 | |].
      + eapply same_but_materialized_trans; [exact SB|]. eapply same_but_materialized_trans; [exact SB' | exact SB2].
      + eapply frame_mod_trans_same; [exact FM'|]. eapply sw_post_frame_mod; [exact HPOST|].
        intros x Hx. unfold tail_regions, OT_FR in Hx. cbn [OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.outside] in Hx. unfold OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.in_rng in Hx. rewrite spm_u in Hx.
        ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). revert Hx. unorm. intros (N1 & N2 & _). lia.
  Qed.

  Lemma seg_F3 : forall vals R M msF mo, P = 63 ->
    length vals = 195%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 141 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knF0_ -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 AMEMCPY_RET) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs mo0))).
  Proof.
    intros vals R M msF mo HP HL P0 P2 P141 HR HK TS RS.
    eapply (seg_F_gen 63 63 _ vals); try eassumption; [lia | lia |].
    intros vals' R' M' msF' mo' HL' Q0 Q2 Q141 HR' HK' TS' RS' SB. eapply (seg_G3 vals'); try eassumption.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_F0 : forall vals R M msF mo, P = 0 ->
    length vals = 195%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 141 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knF00 -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 AMEMCPY_RET) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs mo0))).
  Proof.
    intros vals R M msF mo HP HL P0 P2 P141 HR HK TS RS. pose proof TS as [OK SB FM].
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hpp. unfold AAPP_HI in HppHi.
    tblk rF0 factsF0 (SCR [false; true] [] []) AMEMCPY_RET srF0 knF00 195%nat (ENV vals) M R msF mo HR HK
         ltac:(unfold scs_denot;
               apply Forall_cons; [unfold sc_denot; cbn [edenot ev ENV]; rewrite P0, P2, P141; apply bt_geu_true;
                                   rewrite ?alu_add, ?vadd_wZ, ?vadd_ZZ; unorm; lia|];
               apply Forall_cons; [unfold sc_denot; cbn [edenot ev ENV]; rewrite P0, P2; apply bt_eq_false; rewrite ?alu_add, ?vadd_wZ; unorm; lia|];
               apply Forall_nil) OK RS.
    clear HR HK OK RS. intros R' M' msF' mo' HR HK EQ LF OK' SB' HS' RS'.
    pose proof (log_covered_frame (ENV vals) M ot_regions _ LC0 (ot_regions_flat vals P0) LF) as F'.
    rewrite <- EQ, (ot_regions_denot vals P0) in F'. clear LC0 LF EQ.
    replace (s_pc (fst (fst rF0))) with AMEMCPY in RS' by (vm_compute; reflexivity).
    replace (fst (fst (carry (s_log (fst (fst rF0))) knF00 []))) with knF0' in HK by (vm_compute; reflexivity).
    assert (FM' : frame_mod mem0 M' (tail_regions spm OT_FR)) by (eapply frame_mod_trans_same; [exact FM | exact F']).
    assert (TS' : tst msF' mo' M') by (split; [exact OK' | eapply same_but_materialized_trans; [exact SB | exact SB'] | exact FM']).
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 575)).
    assert (MC : mcH M' dst pp 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    apply (call_memcpy vals _ R' M' msF' mo' dst pp 0 [] keptI _ HR OK' RS' MC);
      [ regv HR (1%bv : reg); apply bv_eq; reflexivity
      | regv HR (10%bv : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia
      | regv HR (11%bv : reg); cbn [edenot ev ENV]; exact P2
      | regv HR (12%bv : reg); cbn [edenot ev ENV]; rewrite P141, HP; reflexivity
      | rewrite HL; vm_compute; reflexivity | exact keptI_sub | exact keptI_no0 |].
    clear HR OK' RS'. intros R2 msF2 mo2 HR OK2 SB2 RS2. change (wbytes M' dst []) with M' in RS2.
    rewrite keptI_MCI, HL in HR. change (sr_after_call_j (s_regs (fst (fst rF0))) KEPT_MCI 195) with srG0 in HR.
    assert (TS2 : tst msF2 mo2 M').
    { split; [exact OK2 | eapply same_but_materialized_trans; [exact (t_sb _ _ _ TS') | exact SB2] | exact FM']. }
    pose proof (know_cut_sound RSEGS (ENV vals) M' M' 0 (BUF_LO + NPRE) BUF_HI IHI knF0'
                  ltac:(unfold win_ok, BUF_LO, BUF_HI, NPRE, IHI; cbn [ev ENV]; rewrite P0; lia)
                  (fun x _ => eq_refl) (mem_grows_refl M') HK) as HK2.
    clear HK.
    pose proof (kn_readd_ok vals M' 0 62 _ P0 P2 P141 ltac:(lia)
                  ltac:(destruct (tfacts _ FM') as (_ & _ & _ & _ & _ & _ & _ & SH); exact SH) HK2) as HK.
    clear HK2. change (kn_readd 0 62 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF0')) with knG0 in HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev []) _ knG0 ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    change (Env (vals_ev (vals ++ junk_vals R2)) (blobs_ev [])) with (ENV (vals ++ junk_vals R2)) in HR, HK.
    eapply (seg_G (vals ++ junk_vals R2));
      [ lia | rewrite length_app, junk_vals_length, HL; reflexivity
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P2
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P141
      | exact HR | exact HK | exact TS2 | exact RS2 | ].
    destruct path as [|b r]; [reflexivity | exfalso; cbn [length] in HP; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_H4 : forall vals R M msF mo,
    length vals = 259%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srH40 R -> know_ok RSEGS (ENV vals) M knH40 -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 AMEMCPY_RET) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs mo0))).
  Proof.
    intros vals R M msF mo HL P0 HR HK [OK SB FM] RS.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp). unfold AAPP_HI in HppHi.
    pose proof ot_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & SCALL).
    tblk rH4 factsH4 scr0 AMEMCPY_RET srH40 knH40 259%nat (ENV vals) M R msF mo HR HK ltac:(constructor) OK RS.
    clear HR HK OK RS. intros R' M' msF' mo' HR HK EQ LF OK' SB' HS' RS'.
    pose proof (log_covered_frame (ENV vals) M ot_regions _ LC0 (ot_regions_flat vals P0) LF) as F'.
    rewrite <- EQ, (ot_regions_denot vals P0) in F'. clear LC0 LF EQ.
    replace (s_pc (fst (fst rH4))) with ASTDIO_WRITE in RS' by (vm_compute; reflexivity).
    assert (FM' : frame_mod mem0 M' (tail_regions spm OT_FR)) by (eapply frame_mod_trans_same; [exact FM | exact F']).
    krdv HK 0%nat (-592) 1%nat Hnl; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia|].
    unfold adenot, v_addi in Hnl. cbn [a_base a_off edenot ev ENV] in Hnl. rewrite P0, NL_word in Hnl.
    replace (W 2 [Z_to_bv 8 10]) with (map (WriteEv (Z_to_bv 64 2)) ([Z_to_bv 8 10] ++ [])) by reflexivity.
    lazymatch goal with |- realizes _ (mkCfg ?msFc ?moc) _ =>
    apply (stdio_call_sound_post vals (blobs_ev []) srH4 knH4 R' M' L S Zr msFc moc scH4 [Z_to_bv 8 10] []
             (t_exit (exit_code 2) (m_fs mo0)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH4 knH4) HL) SCALL));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH4 length Z.of_nat Pos.of_succ_nat Pos.succ] end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. apply u_small. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. exact Hnl.
    - reflexivity.
    - rewrite (same_but_materialized_fds _ _ (same_but_materialized_trans _ _ _ SB SB')) || rewrite <- (same_but_materialized_fds _ _ (same_but_materialized_trans _ _ _ SB SB')). exact Hfd2.
    - exact OK'.
    - exact RS'.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 msF2 mo2 HR HK HPOST OK2 SB2 HS2 RS2.
      change (Env (vals_ev (vals ++ junk_vals R2)) (blobs_ev [])) with (ENV (vals ++ junk_vals R2)) in HR, HK.
      eapply (seg_I4 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK | | exact RS2 ].
      split; [exact OK2 | |].
      + eapply same_but_materialized_trans; [exact SB|]. eapply same_but_materialized_trans; [exact SB' | exact SB2].
      + eapply frame_mod_trans_same; [exact FM'|]. eapply sw_post_frame_mod; [exact HPOST|].
        intros x Hx. unfold tail_regions, OT_FR in Hx. cbn [OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.outside] in Hx. unfold OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.in_rng in Hx. rewrite spm_u in Hx.
        ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). revert Hx. unorm. intros (N1 & N2 & _). lia.
  Qed.
  Lemma seg_FG4 : forall vals R M msF mo, 64 <= P <= 131071 ->
    length vals = 195%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 141 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knF40 -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 AMEMCPY_RET) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs mo0))).
  Proof.
    intros vals R M msF mo HP HL P0 P2 P141 HR HK TS RS. pose proof TS as [OK SB FM].
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hpp. unfold AAPP_HI in HppHi.
    pose proof ot_itinerary as (_ & _ & _ & _ & _ & _ & _ & SCALL4 & _).
    assert (Psmall : (bv_unsigned (edenot (ENV vals) (EVar 141)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite P141, u_small by lia. lia. }
    (* [comment removed for export] *)
    tblk rF4 factsF4 (SCR [true] [] []) AMEMCPY_RET srF0 knF40 195%nat (ENV vals) M R msF mo HR HK
         ltac:(unfold scs_denot;
               apply Forall_cons; [unfold sc_denot; rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _)
                                     by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall);
                                   cbn [branch_taken]; unfold bv_lts; rewrite Z.ltb_irrefl; reflexivity|];
               apply Forall_nil) OK RS.
    clear HR HK OK RS. intros R' M' msF' mo' HR HK EQ LF OK' SB' HS' RS'.
    pose proof (log_covered_frame (ENV vals) M ot_regions _ LC0 (ot_regions_flat vals P0) LF) as F'.
    rewrite <- EQ, (ot_regions_denot vals P0) in F'. clear LC0 LF EQ.
    replace (s_pc (fst (fst rF4))) with ASTDIO_WRITE in RS' by (vm_compute; reflexivity).
    replace (fst (fst (carry (s_log (fst (fst rF4))) knF40 []))) with knF4 in HK by (vm_compute; reflexivity).
    assert (FM' : frame_mod mem0 M' (tail_regions spm OT_FR)) by (eapply frame_mod_trans_same; [exact FM | exact F']).
    destruct (tfacts M' FM') as (_ & _ & _ & _ & _ & Hstr' & _ & _).
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    buf_prefix HK P0 M' H17.
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 2 (PRE17 ++ path)) (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs mo0))))).
    2:{ unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W. rewrite (map_app _ (PRE17 ++ path)).
        apply t_eq_sym. apply t_emit_app. }
    unfold W at 1.
    lazymatch goal with |- realizes _ (mkCfg ?msFc ?moc) _ =>
    apply (stdio_call_sound_post vals (blobs_ev []) srF4 knF4 R' M' L S Zr msFc moc scF4 PRE17 path
             (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs mo0))) HR HK
             (eq_trans (f_equal (fun n => stdio_call n srF4 knF4) HL) SCALL4));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scF4];
      rewrite ?PRE17_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV PX]. rewrite P141. rewrite u_small by lia. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - right. cbn [edenot ev ENV PX]. rewrite P2. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV PX]. rewrite P2, P141. rewrite u_small by lia. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -592)%Z with (bv_unsigned sp0 + -592)%Z by lia. exact H17.
    - cbn [edenot ev ENV PX]. rewrite P2. exact Hsrc.
    - rewrite (same_but_materialized_fds _ _ (same_but_materialized_trans _ _ _ SB SB')) || rewrite <- (same_but_materialized_fds _ _ (same_but_materialized_trans _ _ _ SB SB')). exact Hfd2.
    - exact OK'.
    - exact RS'.
    - apply t_emit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R1 M1 msF1 mo1 HR HK HPOST OK1 SB1 HS1 RS1.
      clear Hstr' Hsrc H17 Psmall.
      assert (FM1 : frame_mod mem0 M1 (tail_regions spm OT_FR)).
      { eapply frame_mod_trans_same; [exact FM'|]. eapply sw_post_frame_mod; [exact HPOST|].
        intros x Hx. unfold tail_regions, OT_FR in Hx. cbn [OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.outside] in Hx. unfold OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.in_rng in Hx. rewrite spm_u in Hx.
        ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). revert Hx. unorm. intros (N1 & N2 & _). lia. }
      assert (TS1 : tst msF1 mo1 M1).
      { split; [exact OK1 | | exact FM1]. eapply same_but_materialized_trans; [exact SB|]. eapply same_but_materialized_trans; [exact SB' | exact SB1]. }
      lazymatch type of HR with regs_ok _ ?sr _ => change sr with srG40 in HR end.
      change (Env (vals_ev (vals ++ junk_vals R1)) (blobs_ev [])) with (ENV (vals ++ junk_vals R1)) in HR, HK.
      assert (Q0 : vals_ev (vals ++ junk_vals R1) 0 = sp0) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q2 : vals_ev (vals ++ junk_vals R1) 2 = pp) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
      assert (Q141 : vals_ev (vals ++ junk_vals R1) 141 = Z_to_bv 64 P) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P141).
      pose proof (kn_readd_ok (vals ++ junk_vals R1) M1 (62 + 2) 131071 _ Q0 Q2 Q141 ltac:(lia)
                    ltac:(destruct (tfacts _ FM1) as (_ & _ & _ & _ & _ & _ & _ & SH); exact SH) HK) as HK2.
      clear HK. change (kn_readd (62 + 2) 131071 (sc_kn scF4)) with knG40 in HK2. rename HK2 into HK.
      set (vals1 := vals ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 227%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      clearbody vals1. clear HPOST HL P0 P2 P141. clear vals. rename HL1 into HL. rename Q0 into P0. rename Q2 into P2. rename Q141 into P141.
      tblk rG4 factsG4 (SCR [false] [] []) (sc_ret scF4) srG40 knG40 227%nat (ENV vals1) M1 R1 msF1 mo1 HR HK
           ltac:(unfold scs_denot;
                 apply Forall_cons; [unfold sc_denot; cbn [edenot ev ENV]; rewrite P0; apply bt_ltu_not_false; lia|];
                 apply Forall_nil) OK1 RS1.
      clear HR HK OK1 RS1. intros RG MG msFG moG HR HK EQ LF OKG SBG HSG RSG.
      pose proof (log_covered_frame (ENV vals1) M1 ot_regions _ LC0 (ot_regions_flat vals1 P0) LF) as FG.
      rewrite <- EQ, (ot_regions_denot vals1 P0) in FG. clear LC0 LF EQ.
      replace (s_pc (fst (fst rG4))) with AMEMCPY in RSG by (vm_compute; reflexivity).
      replace (fst (fst (carry (s_log (fst (fst rG4))) knG40 []))) with knG4 in HK by (vm_compute; reflexivity).
      assert (FMG : frame_mod mem0 MG (tail_regions spm OT_FR)) by (eapply frame_mod_trans_same; [exact FM1 | exact FG]).
      assert (TSG : tst msFG moG MG).
      { split; [exact OKG | eapply same_but_materialized_trans; [exact (t_sb _ _ _ TS1) | exact SBG] | exact FMG]. }
      (* [comment removed for export] *)
      set (dst := Z_to_bv 64 (bv_unsigned sp0 - 592)).
      assert (Hnl : rdn RSEGS MG (Z_to_bv 64 0x3d337) 1 = Some [Z_to_bv 8 10]).
      { rewrite (kimg_rdn RSEGS (ENV vals1) _ knG4 ltac:(let i := kidx knG4 (is_kimg_cov 0x3d337 1) in exact i)
                   _ _ 0x3d337 1 HK eq_refl) by (cbn; lia). apply nl_img. }
      assert (Hdst : store_ok RSEGS MG dst 1 = true).
      { pose proof (kwr_store_ok RSEGS (ENV vals1) _ knG4 ltac:(let i := kidx knG4 (is_kwr_cov (EVar 0) (-592) 1) in exact i)
                      _ _ _ (-592) 1 HK eq_refl ltac:(unfold OT_FR; lia) ltac:(unfold OT_FR; cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        subst dst. replace (bv_unsigned sp0 - 592)%Z with (bv_unsigned sp0 + -592)%Z by lia. exact Hst. }
      assert (MC : mcH MG dst (Z_to_bv 64 0x3d337) 1 [Z_to_bv 8 10]).
      { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
        - exact Hnl.
        - exact Hdst. }
      apply (call_memcpy vals1 _ RG MG msFG moG dst (Z_to_bv 64 0x3d337) 1 [Z_to_bv 8 10] callee_kept _ HR OKG RSG MC);
        [ regv HR (1%bv : reg); apply bv_eq; reflexivity
        | regv HR (10%bv : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia
        | regv HR (11%bv : reg); reflexivity | regv HR (12%bv : reg); reflexivity
        | rewrite HL; vm_compute; reflexivity | intros r Hr; exact Hr | exact callee_kept_no0 |].
      clear HR OKG RSG. intros R2 msF2 mo2 HR OK2 SB2 RS2.
      rewrite kept_MC, HL in HR. change (sr_after_call_j (s_regs (fst (fst rG4))) KEPT_MC 227) with srH40 in HR.
      assert (TS2 : tst msF2 mo2 (wbytes MG dst [Z_to_bv 8 10])).
      { eapply tst_memcpy; [exact TSG | exact OK2 | exact SB2 | subst dst; unfold OT_FR; unorm; lia | subst dst; cbn [length]; unorm; lia]. }
      (* [comment removed for export] *)
      pose proof (know_after_store RSEGS (ENV vals1) MG knG4 (SA (EVar 0) BUF_LO) 1 (ELit 10) [Z_to_bv 8 10]
                    knH40 [] [] ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
                    ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; unfold BUF_LO; lia)
                    ltac:(cbn [edenot]; symmetry; apply NL_word)) as HK2.
      clear HK.
      assert (Edst : adenot (ENV vals1) (SA (EVar 0) BUF_LO) = dst).
      { unfold adenot, v_addi, BUF_LO. cbn [a_base a_off edenot ev ENV]. rewrite P0. subst dst. f_equal; lia. }
      rewrite Edst in HK2.
      pose proof (env_app_know RSEGS vals1 (junk_vals R2) (blobs_ev []) (wbytes MG dst [Z_to_bv 8 10]) knH40
                    ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
      clear HK2.
      change (Env (vals_ev (vals1 ++ junk_vals R2)) (blobs_ev [])) with (ENV (vals1 ++ junk_vals R2)) in HR, HK.
      eapply (seg_H4 (vals1 ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK | exact TS2 | exact RS2 ].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mcH_nil : forall M (dst src : word), mcH M dst src 0 [].
  Proof.
    intros M dst src. pose proof (u64_range dst). pose proof (u64_range src).
    constructor; cbn [length]; try lia; reflexivity.
  Qed.

  Lemma kept_CS : map ridx callee_saved = KEPT_CS. Proof. reflexivity. Qed.

  Lemma snpost_keeps : forall regs mem sp ra K regs' mem',
    snPost regs mem sp ra K regs' mem' -> getr regs 2 = sp -> getr regs 1 = ra ->
    forall r : reg, In r callee_saved -> getr regs' r = getr regs r.
  Proof using sp0 can Hcan64.
    intros regs mem sp ra K regs' mem' PO G2 G1 r Hr.
    destruct PO as [Psp Pra _ Pcs _ _ _ _].
    unfold callee_saved in Hr. cbn [In] in Hr.
    destruct Hr as [<-|Hr]; [rewrite Pra, G1; reflexivity|].
    destruct Hr as [<-|Hr]; [rewrite Psp, G2; reflexivity|].
    apply Pcs. cbn [In]. (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])]).
  Qed.

  Lemma seg_DE : forall vals R M msF mo, 0 <= P <= 131071 ->
    length vals = 131%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    regs_ok (ENV vals) srD0 R -> know_ok RSEGS (ENV vals) M knC -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 AMEMCPY_RET) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs mo0))).
  Proof.
    intros vals R M msF mo HP HL P0 P2 HR HK TS RS. pose proof TS as [OK SB FM].
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SPal as Hal. pose proof (u64_range pp) as Hpp. unfold AAPP_HI in HppHi.
    (* [comment removed for export] *)
    tblk rD factsD scr0 AMEMCPY_RET srD0 knC 131%nat (ENV vals) M R msF mo HR HK ltac:(constructor) OK RS.
    clear HR HK OK RS. intros R' M' msF' mo' HR HK EQ LF OK' SB' HS' RS'.
    pose proof (log_covered_frame (ENV vals) M ot_regions _ LC0 (ot_regions_flat vals P0) LF) as F'.
    rewrite <- EQ, (ot_regions_denot vals P0) in F'. clear LC0 LF EQ.
    replace (s_pc (fst (fst rD))) with ASTRNLEN_TR in RS' by (vm_compute; reflexivity). unfold ASTRNLEN_TR in RS'.
    replace (fst (fst (carry (s_log (fst (fst rD))) knC []))) with knD in HK by (vm_compute; reflexivity).
    assert (FM' : frame_mod mem0 M' (tail_regions spm OT_FR)) by (eapply frame_mod_trans_same; [exact FM | exact F']).
    destruct (tfacts M' FM') as (ST' & INV' & AC' & GOT' & _ & Hstr' & Ht8' & SH').
    (* [comment removed for export] *)
    set (spS := Z_to_bv 64 (bv_unsigned sp0 - 1152)).
    pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
    assert (Hbuf : rdn RSEGS M' pp (length (path ++ t8)) = Some (path ++ t8)).
    { rewrite length_app. rewrite (word_Z pp). apply rdn_app_Z; [ | | lia | lia].
      - rewrite <- (word_Z pp). replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
          by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
        eapply rdn_firstn; [exact Hstr' | lia].
      - rewrite L8. exact Ht8'. }
    assert (Hz : nth (length path) (path ++ t8) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { rewrite app_nth2, Nat.sub_diag by lia.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp) (length path + 1) _ (length path)
                    ltac:(rewrite <- (word_Z pp); exact Hstr') ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp + P) 8 t8 0 Ht8' ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
      replace (bv_unsigned pp + P + Z.of_nat 0)%Z with (bv_unsigned pp + P)%Z in B2 by lia.
      rewrite B1 in B2. injection B2 as E. rewrite <- E. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. }
    assert (MC : mchrH M' pp (path ++ t8) P 0x7fffffff).
    { constructor.
      - exact Hbuf.
      - rewrite length_app, L8.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      - rewrite length_app, L8. lia.
      - lia.
      - rewrite Nat2Z.id, Hz. reflexivity.
      - intros j Hj. rewrite Nat2Z.id in Hj. rewrite nth_app_l by exact Hj.
        intros E. apply (In_nth_neq path (Z_to_bv 8 0) (Z_to_bv 8 0) j Hnonul Hj). apply bv_eq. exact E.
      - lia.
      - lia.
      - intros i Hi. apply (amem_inv_ro_none M' INV'). lia. }
    assert (SNH : snH R' M' spS pp (Z_to_bv 64 0x565eec) P (path ++ t8)).
    { constructor.
      - regv HR (1%bv : reg). apply bv_eq. reflexivity.
      - regv HR (2%bv : reg). subst spS. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). f_equal; lia.
      - regv HR (10%bv : reg). cbn [edenot ev ENV]. exact P2.
      - regv HR (11%bv : reg). reflexivity.
      - subst spS. unorm. rewrite <- Zminus_mod_idemp_l, Hal. reflexivity.
      - subst spS. unfold ASP_LO. unorm. lia.
      - subst spS. unfold ASP_HI. unorm. lia.
      - subst spS. unorm. destruct ST' as (S1 & S2 & S3). split; [unfold SN_FR; lia|]. split; [lia|].
        intros a Ha. apply S3. unfold SN_FR, OT_FR in *. lia.
      - apply (amem_inv_ro_none M' INV').
      - exact GOT'.
      - exact AC'.
      - exact INV'.
      - exact MC.
      - unfold AHI_LO. lia.
      - unfold AAPP_HI. lia.
      - right. subst spS. unorm. lia.
      - intros a Ha. apply SH'. rewrite !shw8_eq in Ha by lia. rewrite ASHADOW_BASE_val in Ha |- *.
        Z.div_mod_to_equations. lia. }
    apply (as_strnlen_k L S Zr R' M' msF' mo' spS pp (Z_to_bv 64 0x565eec) P (path ++ t8) _ SNH OK' RS').
    intros R2 M2 msF2 mo2 POST OK2 SB2 HS2 RS2. unfold SN_RET in RS2.
    pose proof (snpost_keeps _ _ _ _ _ _ _ POST (AsStrnlenK.R2 _ _ _ _ _ _ _ SNH) (AsStrnlenK.R1 _ _ _ _ _ _ _ SNH)) as Hkeep.
    destruct POST as [Psp Pra Pa0 Pcs [Pagree Pgrow] Pstk Pinv Pac].
    (* [comment removed for export] *)
    pose proof (regs_after_keeps vals (blobs_ev []) (s_regs (fst (fst rD))) R' R2 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_saved_no0) as HR2.
    rewrite kept_CS, HL in HR2. clear HR Hkeep. rename HR2 into HR.
    change (sr_after_call_j (s_regs (fst (fst rD))) KEPT_CS 131) with srE0 in HR.
    (* [comment removed for export] *)
    assert (FM2 : frame_mod mem0 M2 (tail_regions spm OT_FR)).
    { eapply frame_mod_trans_same; [exact FM'|]. eapply frame_mod_weaken; [| exact (conj Pagree Pgrow)].
      intros a Ha. pose proof (u64_range a).
      unfold tail_regions in Ha. cbn [OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.outside] in Ha |- *.
      unfold OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.in_rng in Ha |- *. cbn [fst snd] in Ha. subst spS. unfold OT_FR, SN_FR in *.
      revert Ha. unorm. intros Ha. split; [lia | exact I]. }
    assert (TS2 : tst msF2 mo2 M2).
    { split; [exact OK2 | | exact FM2]. eapply same_but_materialized_trans; [exact SB|]. eapply same_but_materialized_trans; [exact SB' | exact SB2]. }
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' M2 0 (-1152 - 4400) (-1152) IHI knD
                  ltac:(unfold win_ok, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(intros x Hx; apply Pagree; cbn [OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.outside]; split; [|exact I];
                        unfold OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.in_rng; subst spS; unfold SN_FR; unorm;
                        cbn [ev ENV] in Hx; rewrite P0 in Hx; lia)
                  Pgrow HK) as HK2.
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev []) M2 (kn_cut 0 (-1152 - 4400) (-1152) IHI knD)
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 163%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q141 : vals_ev vals1 141 = Z_to_bv 64 P).
    { subst vals1. change 141%nat with (131 + 10)%nat. rewrite <- HL. rewrite vals_ev_junk by lia. exact Pa0. }
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev [])) with (ENV vals1) in HR, HK3.
    pose proof (kn_readd_ok vals1 M2 0 131071 _ Q0 Q2 Q141 HP
                  ltac:(destruct (tfacts _ FM2) as (_ & _ & _ & _ & _ & _ & _ & SH); exact SH) HK3) as HK.
    clear HK3. change (kn_readd 0 131071 (kn_cut 0 (-1152 - 4400) (-1152) IHI knD)) with knE0 in HK.
    destruct (tfacts _ FM2) as (_ & _ & _ & _ & _ & Hstr2 & _ & _).
    clear Hstr' Ht8' Hbuf Hz MC SNH Pagree Pgrow Pstk Pinv Pac Psp Pra Pa0 Pcs ST' INV' AC' GOT' SH' L8 FM' F' OK' SB' HS' RS' HL P0 P2.
    rename HL1 into HL. rename Q0 into P0. rename Q2 into P2. rename Q141 into P141.
    assert (Psmall : (bv_unsigned (edenot (ENV vals1) (EVar 141)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite P141, u_small by lia. lia. }
    (* [comment removed for export] *)
    tblk rE factsE (SCR [false] [ELit 0] []) ASTRNLEN_RET srE0 knE0 163%nat (ENV vals1) M2 R2 msF2 mo2 HR HK
         ltac:(unfold scs_denot;
               apply Forall_cons; [unfold sc_denot; rewrite (edenot_addw0_r _ _ Psmall); cbn [branch_taken]; unfold bv_lts; rewrite Z.ltb_irrefl; reflexivity|];
               apply Forall_cons; [unfold sc_denot; exists [Z_to_bv 8 0]; split;
                 [ unfold adenot, v_addi; cbn [a_base a_off]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
                   ed_lin ltac:(cbn [ev ENV]; rewrite ?P2, ?P141);
                   pose proof (rdn_byte_Z RSEGS M2 (bv_unsigned pp) (length path + 1) _ (length path)
                      ltac:(rewrite <- (word_Z pp); exact Hstr2) ltac:(lia) ltac:(lia) ltac:(lia)) as B1;
                   rewrite app_nth2, Nat.sub_diag in B1 by lia; cbn [nth] in B1; exact B1
                 | reflexivity ]|];
               apply Forall_nil) OK2 RS2.
    clear HR HK OK2 RS2. intros R3 M3 msF3 mo3 HR HK EQ LF OK3 SB3 HS3 RS3.
    pose proof (log_covered_frame (ENV vals1) M2 ot_regions _ LC0 (ot_regions_flat vals1 P0) LF) as F3.
    rewrite <- EQ, (ot_regions_denot vals1 P0) in F3. clear LC0 LF EQ.
    replace (s_pc (fst (fst rE))) with AMEMCPY in RS3 by (vm_compute; reflexivity).
    replace (fst (fst (carry (s_log (fst (fst rE))) knE0 []))) with knE in HK by (vm_compute; reflexivity).
    assert (FM3 : frame_mod mem0 M3 (tail_regions spm OT_FR)) by (eapply frame_mod_trans_same; [exact FM2 | exact F3]).
    assert (TS3 : tst msF3 mo3 M3).
    { split; [exact OK3 | eapply same_but_materialized_trans; [exact (t_sb _ _ _ TS2) | exact SB3] | exact FM3]. }
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 575)).
    apply (call_memcpy vals1 _ R3 M3 msF3 mo3 dst (getr R3 11%bv) 0 [] callee_kept _ HR OK3 RS3 (mcH_nil M3 dst (getr R3 11%bv)));
      [ regv HR (1%bv : reg); apply bv_eq; reflexivity
      | regv HR (10%bv : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia
      | reflexivity | regv HR (12%bv : reg); reflexivity
      | rewrite HL; vm_compute; reflexivity | intros r Hr; exact Hr | exact callee_kept_no0 |].
    clear HR OK3 RS3. intros R4 msF4 mo4 HR OK4 SB4 RS4. change (wbytes M3 dst []) with M3 in RS4.
    rewrite kept_MC, HL in HR. change (sr_after_call_j (s_regs (fst (fst rE))) KEPT_MC 163) with srF0 in HR.
    assert (TS4 : tst msF4 mo4 M3).
    { split; [exact OK4 | eapply same_but_materialized_trans; [exact (t_sb _ _ _ TS3) | exact SB4] | exact FM3]. }
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev []) M3 knE ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    change (Env (vals_ev (vals1 ++ junk_vals R4)) (blobs_ev [])) with (ENV (vals1 ++ junk_vals R4)) in HR, HK.
    assert (HL2 : length (vals1 ++ junk_vals R4) = 195%nat) by (rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (W0 : vals_ev (vals1 ++ junk_vals R4) 0 = sp0) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (W2 : vals_ev (vals1 ++ junk_vals R4) 2 = pp) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (W141 : vals_ev (vals1 ++ junk_vals R4) 141 = Z_to_bv 64 P) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P141).
    (* [comment removed for export] *)
    destruct (Z.eq_dec P 0) as [HP0|HP0].
    { eapply (seg_F0 (vals1 ++ junk_vals R4)); [exact HP0 | exact HL2 | exact W0 | exact W2 | exact W141 | exact HR | | exact TS4 | exact RS4].
      change knF00 with (px_range 0 0 knE). apply px_range_ok; [exact W141 | lia | exact HK]. }
    destruct (Z.le_gt_cases P 62) as [Hle|Hgt].
    { eapply (seg_F (vals1 ++ junk_vals R4)); [lia | exact HL2 | exact W0 | exact W2 | exact W141 | exact HR | | exact TS4 | exact RS4].
      change knF0_ with (px_range 1 (62 + 1) knE). apply px_range_ok; [exact W141 | lia | exact HK]. }
    destruct (Z.le_gt_cases P 63) as [Hle2|Hgt2].
    { eapply (seg_F3 (vals1 ++ junk_vals R4)); [lia | exact HL2 | exact W0 | exact W2 | exact W141 | exact HR | | exact TS4 | exact RS4].
      change knF0_ with (px_range 1 (62 + 1) knE). apply px_range_ok; [exact W141 | lia | exact HK]. }
    eapply (seg_FG4 (vals1 ++ junk_vals R4)); [lia | exact HL2 | exact W0 | exact W2 | exact W141 | exact HR | | exact TS4 | exact RS4].
    change knF40 with (px_range (62 + 2) 131071 knE). apply px_range_ok; [exact W141 | lia | exact HK].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma memcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV vals) M logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 592)) PRE17.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE17_words. cbn [mem_denot logM1]. rewrite !wbytes_app.
    unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
    rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
    repeat (f_equal; try (f_equal; lia)).
  Qed.

  Lemma seg_BC : forall vals R M msF mo, 0 <= P <= 131071 ->
    length vals = 67%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    regs_ok (ENV vals) srV0 R -> know_ok RSEGS (ENV vals) M knV0 -> tst msF mo M ->
    restrict L S msF = mkst R (Z_to_bv 64 0x56571c) M (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs mo0))).
  Proof.
    intros vals R M msF mo HP HL P0 P2 HR HK TS RS. pose proof TS as [OK SB FM].
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hpp. unfold AAPP_HI in HppHi.
    (* [comment removed for export] *)
    tblk rB factsB (SCR [false] [] []) 0x56571c srV0 knV0 67%nat (ENV vals) M R msF mo HR HK
         ltac:(unfold scs_denot;
               apply Forall_cons; [unfold sc_denot; cbn [edenot ev ENV]; rewrite P0; apply bt_ltu_not_false; lia|];
               apply Forall_nil) OK RS.
    clear HR HK OK RS. intros R' M' msF' mo' HR HK EQ LF OK' SB' HS' RS'.
    pose proof (log_covered_frame (ENV vals) M ot_regions _ LC0 (ot_regions_flat vals P0) LF) as F'.
    rewrite <- EQ, (ot_regions_denot vals P0) in F'. clear LC0 LF EQ.
    replace (s_pc (fst (fst rB))) with AMEMCPY in RS' by (vm_compute; reflexivity).
    replace (fst (fst (carry (s_log (fst (fst rB))) knV0 []))) with knB in HK by (vm_compute; reflexivity).
    assert (FM' : frame_mod mem0 M' (tail_regions spm OT_FR)) by (eapply frame_mod_trans_same; [exact FM | exact F']).
    assert (TS' : tst msF' mo' M') by (split; [exact OK' | eapply same_but_materialized_trans; [exact SB | exact SB'] | exact FM']).
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 592)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x3d324) 17 = Some PRE17).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x3d324 17) in exact i)
                 _ _ 0x3d324 17 HK eq_refl) by (cbn; lia). apply pre17_img. }
    assert (Hdst : store_ok RSEGS M' dst 17 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-592) 17) in exact i)
                    _ _ _ (-592) 17 HK eq_refl ltac:(unfold OT_FR; lia) ltac:(unfold OT_FR; cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 592)%Z with (bv_unsigned sp0 + -592)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x3d324) 17 PRE17).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    apply (call_memcpy vals _ R' M' msF' mo' dst (Z_to_bv 64 0x3d324) 17 PRE17 callee_kept _ HR OK' RS' MC);
      [ regv HR (1%bv : reg); apply bv_eq; reflexivity
      | regv HR (10%bv : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia
      | regv HR (11%bv : reg); reflexivity | regv HR (12%bv : reg); reflexivity
      | rewrite HL; vm_compute; reflexivity | intros r Hr; exact Hr | exact callee_kept_no0 |].
    clear HR OK' RS'. intros R2 msF2 mo2 HR OK2 SB2 RS2.
    rewrite kept_MC, HL in HR. change (sr_after_call_j (s_regs (fst (fst rB))) KEPT_MC 67) with srC0 in HR.
    assert (TS2 : tst msF2 mo2 (wbytes M' dst PRE17)).
    { eapply tst_memcpy; [exact TS' | exact OK2 | exact SB2 | subst dst; unfold OT_FR; unorm; lia | subst dst; rewrite PRE17_len; unorm; lia]. }
    (* [comment removed for export] *)
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M' dst PRE17) knC0).
    { subst dst. rewrite <- (memcpy1_denot vals M' P0).
      eapply (carry_after RSEGS (ENV vals) M' logM1 knB [] knC0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM1].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev []) (wbytes M' dst PRE17) knC0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 99%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev [])) with (ENV vals1) in HR, HK.
    clear Hsrc Hdst MC. clearbody dst.
    set (M1 := wbytes M' dst PRE17) in *. clearbody M1. clear F' FM' TS' HL P0 P2 vals. clear M' dst.
    rename HL1 into HL. rename Q0 into P0. rename Q2 into P2.
    (* [comment removed for export] *)
    tblk rC factsC scr0 AMEMCPY_RET srC0 knC0 99%nat (ENV vals1) M1 R2 msF2 mo2 HR HK ltac:(constructor) OK2 RS2.
    clear HR HK OK2 RS2. intros R3 M3 msF3 mo3 HR HK EQ LF OK3 SB3 HS3 RS3.
    pose proof (log_covered_frame (ENV vals1) M1 ot_regions _ LC0 (ot_regions_flat vals1 P0) LF) as F3.
    rewrite <- EQ, (ot_regions_denot vals1 P0) in F3. clear LC0 LF EQ.
    replace (s_pc (fst (fst rC))) with AMEMCPY in RS3 by (vm_compute; reflexivity).
    replace (fst (fst (carry (s_log (fst (fst rC))) knC0 []))) with knC in HK by (vm_compute; reflexivity).
    assert (FM3 : frame_mod mem0 M3 (tail_regions spm OT_FR)) by (eapply frame_mod_trans_same; [exact (t_fm _ _ _ TS2) | exact F3]).
    assert (TS3 : tst msF3 mo3 M3).
    { split; [exact OK3 | eapply same_but_materialized_trans; [exact (t_sb _ _ _ TS2) | exact SB3] | exact FM3]. }
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 575)).
    apply (call_memcpy vals1 _ R3 M3 msF3 mo3 dst (getr R3 11%bv) 0 [] callee_kept _ HR OK3 RS3 (mcH_nil M3 dst (getr R3 11%bv)));
      [ regv HR (1%bv : reg); apply bv_eq; reflexivity
      | regv HR (10%bv : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia
      | reflexivity | regv HR (12%bv : reg); reflexivity
      | rewrite HL; vm_compute; reflexivity | intros r Hr; exact Hr | exact callee_kept_no0 |].
    clear HR OK3 RS3. intros R4 msF4 mo4 HR OK4 SB4 RS4. change (wbytes M3 dst []) with M3 in RS4.
    rewrite kept_MC, HL in HR. change (sr_after_call_j (s_regs (fst (fst rC))) KEPT_MC 99) with srD0 in HR.
    assert (TS4 : tst msF4 mo4 M3).
    { split; [exact OK4 | eapply same_but_materialized_trans; [exact (t_sb _ _ _ TS3) | exact SB4] | exact FM3]. }
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev []) M3 knC ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    change (Env (vals_ev (vals1 ++ junk_vals R4)) (blobs_ev [])) with (ENV (vals1 ++ junk_vals R4)) in HR, HK.
    eapply (seg_DE (vals1 ++ junk_vals R4));
      [ exact HP | rewrite length_app, junk_vals_length, HL; reflexivity
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P2
      | exact HR | exact HK | exact TS4 | exact RS4 ].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition srA0 : list expr :=
    map (fun i => match i with 0 => ELit 0 | 2 => spx (-128) | 4 => ELit 0xbe1c90 | 18 => EVar 2 | _ => EVar (3 + i) end)%nat (seq 0 32).
  Definition knA0 : list kentry := [KImg 0x10000 0x195000; KImg 0x571000 0x5ea000].
  Definition rA := Eval vm_compute in sym_exec RSEGS 100 true [0x1a8750] scr0 (SS 0x1eefb8 srA0 [] knA0 35) [].
  Lemma rA_facts : s_pc (fst (fst rA)) = 0x1a8750 /\ snd (fst rA) = [] /\ s_log (fst (fst rA)) = [].
  Proof. vm_compute. repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ot_vals0 (R1 : bvmap 5 word) : list word := [sp0; Z_to_bv 64 can; pp] ++ junk_vals R1.
  Definition ot_vals (R1 R2 : bvmap 5 word) : list word := ot_vals0 R1 ++ junk_vals R2.

  Lemma ot_vals0_len : forall R1, length (ot_vals0 R1) = 35%nat.
  Proof. intros. unfold ot_vals0. rewrite length_app, junk_vals_length. reflexivity. Qed.
  Lemma ot_vals_len : forall R1 R2, length (ot_vals R1 R2) = 67%nat.
  Proof. intros. unfold ot_vals. rewrite length_app, junk_vals_length, ot_vals0_len. reflexivity. Qed.
  Lemma ot_ev1 : forall R1 R2 i, (i < 32)%nat -> vals_ev (ot_vals R1 R2) (3 + i) = getr R1 (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros R1 R2 i Hi. unfold ot_vals. rewrite vals_ev_app_l by (rewrite ot_vals0_len; lia). unfold ot_vals0.
    change (3 + i)%nat with (length [sp0; Z_to_bv 64 can; pp] + i)%nat. apply vals_ev_junk. exact Hi.
  Qed.
  Lemma ot_ev2 : forall R1 R2 i, (i < 32)%nat -> vals_ev (ot_vals R1 R2) (35 + i) = getr R2 (Z_to_bv 5 (Z.of_nat i)).
  Proof. intros R1 R2 i Hi. unfold ot_vals. rewrite <- (ot_vals0_len R1). apply vals_ev_junk. exact Hi. Qed.
  Lemma ot_ev_0 : forall R1 R2, vals_ev (ot_vals R1 R2) 0 = sp0. Proof. reflexivity. Qed.
  Lemma ot_ev_1 : forall R1 R2, vals_ev (ot_vals R1 R2) 1 = Z_to_bv 64 can. Proof. reflexivity. Qed.
  Lemma ot_ev_2 : forall R1 R2, vals_ev (ot_vals R1 R2) 2 = pp. Proof. reflexivity. Qed.

  Theorem as_open_tail : forall regs msF mo,
    P <= 131071 ->
    getr regs 2 = spm -> getr regs 4 = Z_to_bv 64 0xbe1c90 -> getr regs 18 = pp ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> same_but_materialized mo0 mo ->
    restrict L S msF = mkst regs (Z_to_bv 64 0x1eefb8) mem0 (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs mo0))).
  Proof.
    intros regs msF mo HPmax G2 G4 G18 OK SB RS.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SPal as Hal. pose proof (u64_range pp) as Hpp. unfold AAPP_HI in HppHi.
    pose proof rA_facts as (PCA & SCA & LGA).
    set (vals0 := ot_vals0 regs).
    assert (V0 : vals_ev vals0 0 = sp0) by reflexivity.
    assert (HR0 : regs_ok (ENV vals0) srA0 regs).
    { apply regs_ok_by_idx. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth srA0 allregs32 map seq edenot ev ENV]; unfold spx; cbn [edenot ev ENV].
      1: apply getr_zero.
      all: first [ rewrite V0, G2, alu_add, vadd_wZ; f_equal; lia
                 | exact G4 | exact G18
                 | subst vals0; unfold ot_vals0;
                   lazymatch goal with |- _ = vals_ev _ ?n =>
                     let i := eval compute in (n - 3)%nat in
                     change n with (length [sp0; Z_to_bv 64 can; pp] + i)%nat end;
                   rewrite vals_ev_junk by lia; f_equal; apply bv_eq; reflexivity ]. }
    assert (HK0 : know_ok RSEGS (ENV vals0) mem0 knA0).
    { unfold knA0. constructor; [apply kimg_intro; [lia | lia | apply (amem_inv_ro_none mem0 Hinv)] |].
      constructor; [apply kimg_intro; [lia | lia | exact Hgot] | constructor]. }
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr 100 [0x1a8750] scr0 0x1eefb8 srA0 knA0 35 (fst (fst rA)) (snd (fst rA)) (snd rA)
              knA0 [] [] (ENV vals0) mem0 (seg_rom RSEGS) regs msF mo);
      [ vm_cast_no_check (@eq_refl _ rA) | rewrite LGA; reflexivity | exact HR0 | exact HK0
      | rewrite SCA; constructor | constructor | exact OK | exact RS | ].
    clear HR0 HK0 OK RS. intros R1 M1 msF1 mo1 HR HK EQ LF OK1 SB1 HS1 RS1.
    rewrite LGA in EQ. cbn [mem_denot] in EQ. subst M1. rewrite PCA in RS1.
    (* [comment removed for export] *)
    assert (FPH : fpH R1 mem0 spm pp (Z_to_bv 64 0x1eef88) path).
    { constructor.
      - regv HR (1%bv : reg). apply bv_eq. reflexivity.
      - regv HR (2%bv : reg). unfold spx. cbn [edenot ev ENV]. rewrite V0, alu_add, vadd_wZ. f_equal; lia.
      - regv HR (11%bv : reg). reflexivity.
      - regv HR (12%bv : reg). cbn [edenot ev ENV]. reflexivity.
      - rewrite spm_u. rewrite <- Zminus_mod_idemp_l, Hal. reflexivity.
      - rewrite spm_u. unfold ASP_LO. lia.
      - rewrite spm_u. unfold ASP_HI. lia.
      - rewrite spm_u. destruct Hstk as (S1 & S2 & S3). split; [unfold FP_FR; lia|]. split; [lia|].
        intros a Ha. apply S3. unfold FP_FR, OT_FR in *. lia.
      - exact Hgot.
      - exact Hac.
      - exact Hinv.
      - rewrite Z_to_bv_bv_unsigned. exact Hstr.
      - exact Hnonul.
      - unfold AHI_LO. lia.
      - unfold AAPP_HI. lia.
      - unfold PMAXF. lia.
      - right. rewrite spm_u. lia.
      - intros a Ha. apply Hsh0. rewrite !shw8_eq in Ha by lia. rewrite ASHADOW_BASE_val in Ha |- *.
        Z.div_mod_to_equations. lia. }
    apply (as_fprintf_open_k L S Zr R1 mem0 msF1 mo1 spm pp (Z_to_bv 64 0x1eef88) path _ FPH OK1 RS1).
    intros R2 M2 msF2 mo2 POST OK2 SB2 HS2 RS2. unfold AVFPRINTF in RS2.
    destruct POST as [Qsp Qra Qa0 Qa1 Qa2 Qs0 Qs1 Qs2 Qcs [Qagree Qgrow] Qva0 Qsra Qss0 Qss1 Qss2 Qstk Qinv Qac].
    rewrite spm_u in *.
    assert (FM2 : frame_mod mem0 M2 (tail_regions spm OT_FR)).
    { eapply frame_mod_weaken; [| exact (conj Qagree Qgrow)].
      intros a Ha. pose proof (u64_range a).
      unfold tail_regions in Ha. cbn [OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.outside] in Ha |- *.
      unfold OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.in_rng in Ha |- *. cbn [fst snd] in Ha. unfold OT_FR, FP_FR in *.
      revert Ha. unorm. intros Ha. split; [lia | exact I]. }
    assert (TS2 : tst msF2 mo2 M2).
    { split; [exact OK2 | | exact FM2]. eapply same_but_materialized_trans; [exact SB|]. eapply same_but_materialized_trans; [exact SB1 | exact SB2]. }
    destruct (tfacts M2 FM2) as (ST2 & INV2 & AC2 & GOT2 & CAN2 & Hstr2 & Ht82 & SH2).
    (* [comment removed for export] *)
    set (vals := ot_vals R1 R2).
    assert (A10 : getr R1 10%bv = Z_to_bv 64 0x5edca8) by (regv HR (10%bv : reg); reflexivity).
    assert (A4 : getr R1 4%bv = Z_to_bv 64 0xbe1c90) by (regv HR (4%bv : reg); reflexivity).
    assert (HRV : regs_ok (ENV vals) srV0 R2).
    { apply regs_ok_by_idx. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth srV0 allregs32 map seq edenot ev ENV]; unfold spx, FMT; cbn [edenot ev ENV]; subst vals; rewrite ?ot_ev_0.
      1: apply getr_zero.
      all: first [ exact Qra
                 | rewrite Qsp, alu_add, vadd_wZ; f_equal; lia
                 | rewrite (Qcs 4%bv) by (cbn [In]; tauto); exact A4
                 | exact Qs0 | rewrite Qs1; exact A10 | rewrite Qa0; exact A10 | exact Qa1
                 | rewrite Qa2, alu_add, vadd_wZ; f_equal; lia
                 | rewrite Qs2, alu_add, vadd_wZ; f_equal; lia
                 | lazymatch goal with |- _ = vals_ev _ ?n =>
                     let i := eval compute in (n - 35)%nat in change n with (35 + i)%nat end;
                   rewrite ot_ev2 by lia; f_equal; apply bv_eq; reflexivity ]. }
    assert (STK2 : stk_ok RSEGS M2 spm OT_FR).
    { eapply astk_stk_ok; [exact ST2 | rewrite spm_u; lia | rewrite spm_u; lia | unfold OT_FR; lia | lia]. }
    assert (CELLS2 : cells_ok M2 ot_cells).
    { unfold cells_ok in Hcells |- *. rewrite Forall_forall in Hcells |- *. intros [[a w] v] Hin.
      pose proof (Hcells _ Hin) as Hc. unfold cell_ok in Hc |- *.
      assert (LOW : a + Z.of_nat w <= 0x80000000 /\ 0 <= a).
      { unfold ot_cells in Hin. cbn [In] in Hin.
        repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; (first [clear; lia | lia])|]). destruct Hin. }
      rewrite (frame_mod_rdn RSEGS mem0 M2 _ w (Z_to_bv 64 a) (conj Qagree Qgrow)); [exact Hc | | unorm; lia].
      intros i Hi. cbn [OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.outside]. split; [|exact I].
      unfold OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.in_rng. unfold FP_FR. unorm. lia. }
    assert (HKV : know_ok RSEGS (ENV vals) M2 knV0).
    { unfold knV0. apply know_ok_app2; [| apply know_ok_app2; [| apply cells_know; [vm_compute; reflexivity | exact CELLS2]]].
      2:{ apply (shkn_ok (ENV vals) M2 sp0 OT_SHOFFS); [subst vals; cbn [ev ENV]; apply ot_ev_0 | unfold ASP_LO; lia | unfold ASP_HI; lia
            | unfold OT_SHOFFS; repeat constructor; lia |].
          intros a Ha. apply SH2. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
      subst vals.
      apply Forall_cons. { apply kalign_intro; [lia|]. cbn [edenot ev ENV]. rewrite ot_ev_0. exact Hal. }
      apply Forall_cons. { apply krange_intro. cbn [edenot ev ENV]. rewrite ot_ev_0. lia. }
      apply Forall_cons. { cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot ev ENV]. rewrite ot_ev_0.
                           split; [unfold OT_FR; lia|]. intros d m Hd Hm. apply STK2; rewrite spm_u; unfold OT_FR in *; unorm; lia. }
      apply Forall_cons. { apply krange_intro. cbn [edenot ev ENV]. rewrite ot_ev_2. unfold AHI_LO, AAPP_HI. lia. }
      apply Forall_cons. { apply kimg_intro; [lia | lia | apply (amem_inv_ro_none M2 INV2)]. }
      apply Forall_cons. { apply kimg_intro; [lia | lia | exact GOT2]. }
      apply Forall_cons. { eapply (kword_intro RSEGS _ M2 (EVar 0) sp0 (-176) 8 (EVar 2) pp);
                             [cbn [edenot ev ENV]; apply ot_ev_0 | cbn [edenot ev ENV]; apply ot_ev_2 | lia | lia | lia | lia |].
                           replace (bv_unsigned sp0 + -176) with (bv_unsigned sp0 - 128 - 48) by lia. exact Qva0. }
      apply Forall_cons. { eapply (kword_intro RSEGS _ M2 (EVar 0) sp0 (-184) 8 (ELit 0x1eef88) (Z_to_bv 64 0x1eef88));
                             [cbn [edenot ev ENV]; apply ot_ev_0 | reflexivity | lia | lia | lia | lia |].
                           replace (bv_unsigned sp0 + -184) with (bv_unsigned sp0 - 128 - 56) by lia. exact Qsra. }
      apply Forall_cons. { eapply (kword_intro RSEGS _ M2 (EVar 0) sp0 (-192) 8 (EVar 11) (getr R1 8%bv));
                             [cbn [edenot ev ENV]; apply ot_ev_0 | cbn [edenot ev ENV]; apply (ot_ev1 R1 R2 8) ; lia | lia | lia | lia | lia |].
                           replace (bv_unsigned sp0 + -192) with (bv_unsigned sp0 - 128 - 64) by lia. exact Qss0. }
      apply Forall_cons. { eapply (kword_intro RSEGS _ M2 (EVar 0) sp0 (-200) 8 (EVar 12) (getr R1 9%bv));
                             [cbn [edenot ev ENV]; apply (ot_ev_0 R1 R2) | cbn [edenot ev ENV]; apply (ot_ev1 R1 R2 9); lia | lia | lia | lia | lia |].
                           replace (bv_unsigned sp0 + -200) with (bv_unsigned sp0 - 128 - 72) by lia. exact Qss1. }
      apply Forall_cons. { eapply (kword_intro RSEGS _ M2 (EVar 0) sp0 (-208) 8 (EVar 21) (getr R1 18%bv));
                             [cbn [edenot ev ENV]; apply (ot_ev_0 R1 R2) | cbn [edenot ev ENV]; apply (ot_ev1 R1 R2 18); lia | lia | lia | lia | lia |].
                           replace (bv_unsigned sp0 + -208) with (bv_unsigned sp0 - 128 - 80) by lia. exact Qss2. }
      apply Forall_cons. { eapply (kword_intro RSEGS _ M2 (ELit 0) (Z_to_bv 64 0) 0xc01cd0 8 (EVar 1) (Z_to_bv 64 can));
                             [reflexivity | cbn [edenot ev ENV]; apply ot_ev_1 | lia | lia | unorm; lia | unorm; lia |].
                           unorm. rewrite Z.add_0_l. exact CAN2. }
      apply Forall_cons. { cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. unorm.
                           split; [lia|]. intros d m Hd Hm. apply RefExitBase.store_ok_data. unorm. lia. }
      apply Forall_nil. }
    eapply (seg_BC vals R2 M2 msF2 mo2);
      [ lia | subst vals; apply ot_vals_len | subst vals; apply ot_ev_0 | subst vals; apply ot_ev_2
      | exact HRV | exact HKV | exact TS2 | exact RS2 ].
  Qed.
End Tail.
