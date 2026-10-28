(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame Spec LibWritev HUExitBase HUStdioDefs HUExit HULibStdioCall RefMemcpyLib HUMemcpyBase HUMemcpy HUMemchr HUStrnlen HUStartup HUMainEntry LibTail HUOpenFail_defs HUOpenFail_tail2.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HUMainEntryN HUUsage_defs HUStartupDefs.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen RefLayout SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 Spec LibWritev RefNodes HUExitBase HUExit RefMemcpyLib HUMemcpyBase HUMemcpy HUMemchr HUStrnlen HUStartup HUStartupFacts HUMainEntry LibTail HUOpenFail_defs HUOpenFail_tail2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)

(* [comment removed for export] *)
Module H0Usage_tail.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ShapeAlg OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Nodes OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Hoare OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Frame ShapeLaws OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SpecConsts OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MmapSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AllocSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FileSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AgentLib OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2 OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2Sound OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymRun OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDrive OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDriveX OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDriveH4 OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibKnowFrame Spec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibWritev HUExitBase HUStdioDefs HUExit HULibStdioCall OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefMemcpyLib HUMemcpyBase HUMemcpy HUMemchr HUStrnlen HUStartup HUMainEntry OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibTail HUOpenFail_defs HUOpenFail_tail2.H0OpenFail_tail HUOpenFail_tail2.
Import HUMainEntryN HUUsage_defs.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition PRE7 : list byte := s2b "usage: "%string.
Definition SUF7 : list byte := s2b " INPUT"%string ++ [Z_to_bv 8 10].

Lemma PRE7_word : word_to_le_bytes 7 (Z_to_bv 64 9071406455288693) = PRE7.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma SUF7_word : word_to_le_bytes 7 (Z_to_bv 64 2907475163367712) = SUF7.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma pre7_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x1bc91) 7 = Some PRE7.
Proof. vm_compute. reflexivity. Qed.
Lemma suf7_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x1bc9a) 7 = Some SUF7.
Proof. vm_compute. reflexivity. Qed.
Lemma PRE7_len : length PRE7 = 7%nat. Proof. reflexivity. Qed.
Lemma SUF7_len : length SUF7 = 7%nat. Proof. reflexivity. Qed.
Lemma msg_usage_eq : forall a0s, msg_usage a0s = PRE7 ++ a0s ++ SUF7.
Proof. intros. unfold msg_usage, PRE7, SUF7. reflexivity. Qed.

Section UTail.
  Variable sp0 : word.
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  (* [comment removed for export] *)
  Variable BL : list (list byte).
  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev BL).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

(* [comment removed for export] *)
Ltac close_exit_at HR HK P0 Hh Hlazy sp0 OFF WLO :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV EN] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - OFF)), (Z_to_bv 64 0x331ae8), (bv_unsigned (ev E 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV EN];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) WLO 144) in exact i)
                      _ _ _ WLO 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENV EN] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - OFF - 144)%Z with (bv_unsigned sp0 + WLO)%Z by lia; exact Hst
      | lit_u; cbn [ev ENV EN] in Ktid |- *; lia
      | lit_u; cbn [ev ENV EN] in Ktid |- *; lia
      | cbn [ev ENV EN] in Ktid |- *; lia
      | lit_u; change (3349224 - 168)%Z with 0x331a40%Z;
        let Htc := fresh "Htc" in
        krd HK 0x331a40%Z 4%nat Htc; rewrite Htc; cbn [ev ENV EN] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma us_segH : forall vals R M,
    length vals = 262%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) u_srH0 R -> know_ok RSEGS (ENV vals) M u_knH0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b6224) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 262%nat.
    close_exit_at HR HK P0 Hh Hlazy sp0 48%Z (-192)%Z.
  Qed.

  Lemma us_segG : forall (a0s : list byte) (L : Z) vals R M,
    Z.of_nat (length a0s) = L -> (0 <= L <= 66)%Z ->
    length vals = 230%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 112 = Z_to_bv 64 L ->
    regs_ok (ENV vals) u_srG0 R -> know_ok RSEGS (ENV vals) M u_knG0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 553 + L)) 7%nat = Some SUF7 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b5e94) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros a0s L vals R M HP HPr HL P0 P112 HR HK SBp SBn.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk_keep scr0 230%nat.
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    assert (SBn' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553 + L)) 7 = Some SUF7).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBn | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; cbn; lia]. }
    clear EQM SBp SBn. rename M0 into M'.
    krdv HK 0%nat (-560)%Z 7%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0. cbn [a_base a_off edenot ev ENV] in Hw0. rewrite P0, PRE7_word in Hw0.
    assert (MSG : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (7 + (length a0s + 7))
                  = Some (msg_usage a0s)).
    { rewrite msg_usage_eq.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [| | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 7)%Z with (bv_unsigned sp0 - 553)%Z by lia. exact SBp'.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 7 + Z.of_nat (length a0s))%Z
          with (bv_unsigned sp0 - 553 + L)%Z by lia. exact SBn'. }
    replace (W 2 (msg_usage a0s)) with (map (WriteEv (Z_to_bv 64 2)) (msg_usage a0s ++ []))
      by (unfold W; rewrite app_nil_r; reflexivity).
    assert (LEN : length (msg_usage a0s) = (7 + (length a0s + 7))%nat)
      by (rewrite msg_usage_eq, !length_app, PRE7_len, SUF7_len; reflexivity).
    pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) u_srG u_knG Rc Mc model u_scG (msg_usage a0s) []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srG u_knG) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scG]; rewrite ?LEN end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - (* [comment removed for export] *) ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - cbn [edenot length]. reflexivity.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact MSG.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (us_segH (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  Definition atUF0 (a0s : list byte) (L : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 198%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 112 = Z_to_bv 64 L ->
      regs_ok (ENV vals) u_srF0 R -> know_ok RSEGS (ENV vals) M u_knF0 ->
      rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b5e94) M (seg_rom RSEGS)) model) T.

  Lemma us_segF : forall (a0s : list byte) (L : Z), Z.of_nat (length a0s) = L -> (0 <= L <= 66)%Z ->
    atUF0 a0s L (t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros a0s L HP HPr vals R M HL P0 P112 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk_keep u_scrF 198%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112).
      replace (-1 * L + 73)%Z with (73 - L)%Z by lia.
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553 + L)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x1bc9a) 7 = Some SUF7).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ u_knF ltac:(let i := kidx u_knF (is_kimg_cov 0x1bc9a 7) in exact i)
                 _ _ 0x1bc9a 7 HK eq_refl) by (cbn; lia). apply suf7_img. }
    assert (Hdst : store_ok RSEGS M' dst 7 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knF ltac:(let i := kidx u_knF (is_kwr_cov (EVar 0) (-553) 73) in exact i)
                    _ _ _ (-553 + L) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 553 + L)%Z with (bv_unsigned sp0 + (-553 + L))%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x1bc9a) 7 SUF7).
    { constructor; subst dst; rewrite ?u_small by lia; rewrite ?SUF7_len; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2b5e94 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1bc9a) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x1bc9a) 7 _ (seg_rom RSEGS) MC Rc (0x2b5e94 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 2867236) with (0x2bc024 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x2b5e94 : word) with (Z_to_bv 64 0x2b5e94) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst SUF7) 0 (-553) BUF_HI IHI u_knF
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst SUF7 (ENV vals) 0 (-553) BUF_HI);
                        cbn [ev ENV]; rewrite P0, ?SUF7_len; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-553) BUF_HI IHI u_knF) with u_knG0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst SUF7) u_knG0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 230%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q112 : vals_ev vals1 112 = Z_to_bv 64 L) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P112).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (us_segG a0s L vals1); try eassumption.
    - rewrite rdn_wbytes_out; [exact SBp' | | |]; rewrite ?SUF7_len; subst dst; rewrite ?u_small by lia; lia.
    - subst dst. rewrite <- SUF7_len.
      apply (rdn_wbytes_hit RSEGS SUF7 M'). rewrite SUF7_len, u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma us_segE_gen : forall (a0s : list byte) (pp : word) (L : Z) (T : TSet) vals R M,
    Z.of_nat (length a0s) = L -> (0 <= L <= 73)%Z ->
    length vals = 166%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp -> vals_ev vals 112 = Z_to_bv 64 L ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) u_srE0 R -> know_ok RSEGS (ENV vals) M u_knD ->
    rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
    atUF0 a0s L T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b5e94) M (seg_rom RSEGS)) model) T.
  Proof.
    intros a0s pp L T vals R M HP HPr HL P0 P1 P112 Hpp1 Hpp2 HR HK Hstr HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Psmall : (bv_unsigned (edenot (ENV vals) (EVar 112)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite P112, u_small by lia. lia. }
    run_blk_keep u_scrE 166%nat.
    { unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P112).
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    { unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia
        | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553)).
    assert (Hsrc : rdn RSEGS M' pp (length a0s) = Some a0s).
    { replace a0s with (firstn (length a0s) (a0s ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    assert (Hdst : store_ok RSEGS M' dst (length a0s) = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knE ltac:(let i := kidx u_knE (is_kwr_cov (EVar 0) (-553) 73) in exact i)
                    _ _ _ (-553) (length a0s) HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 553)%Z with (bv_unsigned sp0 + -553)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst pp L a0s).
    { constructor; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2b5e94 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = pp) by (regv HR (11 : reg); cbn [edenot ev ENV]; exact P1);
      assert (A12 : getr Rc 12 = Z_to_bv 64 L) by (regv HR (12 : reg); cbn [edenot ev ENV]; exact P112);
      destruct (ref_memcpy M' dst pp L _ (seg_rom RSEGS) MC Rc (0x2b5e94 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 2867236) with (0x2bc024 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x2b5e94 : word) with (Z_to_bv 64 0x2b5e94) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst a0s) 0 (-553) BUF_HI IHI u_knE
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst a0s (ENV vals) 0 (-553) BUF_HI);
                        cbn [ev ENV]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-553) BUF_HI IHI u_knE) with u_knF0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst a0s) u_knF0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 198%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q112 : vals_ev vals1 112 = Z_to_bv 64 L) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P112).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (HF0 vals1); try eassumption.
    subst dst. rewrite <- HP at 1 || idtac.
    pose proof (rdn_wbytes_hit RSEGS a0s M' (Z_to_bv 64 (bv_unsigned sp0 - 553))) as Hc.
    apply Hc. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition atUE0 (a0s : list byte) (pp : word) (L : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 166%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp -> vals_ev vals 112 = Z_to_bv 64 L ->
      regs_ok (ENV vals) u_srE0 R -> know_ok RSEGS (ENV vals) M u_knD ->
      rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b5e94) M (seg_rom RSEGS)) model) T.

  Lemma us_segCD : forall (a0s : list byte) (pp : word) (L : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length a0s) = L -> (0 <= L <= 131071)%Z -> ~ In (Z_to_bv 8 0) a0s ->
    length vals = 102%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) u_srC0 R -> know_ok RSEGS (ENV vals) M u_knB ->
    rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8 ->
    atUE0 a0s pp L T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b5e94) M (seg_rom RSEGS)) model) T.
  Proof.
    intros a0s pp L T t8 vals R M HP HPr Hnonul HL P0 P1 Hpp1 Hpp2 HR HK Hstr Ht8 HE0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 102%nat.
    assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M'.
    set (spS := Z_to_bv 64 (bv_unsigned sp0 - 1120)).
    assert (Hbuf : rdn RSEGS M' pp (length (a0s ++ t8)) = Some (a0s ++ t8)).
    { rewrite length_app. rewrite (word_Z pp). apply rdn_app_Z; [ | | lia | lia].
      - rewrite <- (word_Z pp). replace a0s with (firstn (length a0s) (a0s ++ [Z_to_bv 8 0])) at 2
          by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
        eapply rdn_firstn; [exact Hstr' | lia].
      - pose proof (rdn_length _ _ _ _ _ Ht8') as L8. rewrite L8, HP. exact Ht8'. }
    assert (Hz : nth (length a0s) (a0s ++ t8) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      rewrite app_nth2, Nat.sub_diag by lia.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp) (length a0s + 1) _ (length a0s)
                    ltac:(rewrite <- (word_Z pp); exact Hstr') ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp + L) 8 t8 0 Ht8' ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
      replace (bv_unsigned pp + Z.of_nat (length a0s))%Z with (bv_unsigned pp + L)%Z in B1 by lia.
      replace (bv_unsigned pp + L + Z.of_nat 0)%Z with (bv_unsigned pp + L)%Z in B2 by lia.
      rewrite B1 in B2. injection B2 as E. rewrite <- E. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. }
    assert (MC : mchrH M' pp (a0s ++ t8) L 0x7fffffff).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      constructor.
      - exact Hbuf.
      - rewrite length_app, L8.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      - rewrite length_app, L8. lia.
      - lia.
      - rewrite <- HP, Nat2Z.id, Hz. reflexivity.
      - intros j Hj. rewrite <- HP, Nat2Z.id in Hj. rewrite nth_app_l by exact Hj.
        intros E. apply (In_nth_neq a0s (Z_to_bv 8 0) (Z_to_bv 8 0) j Hnonul Hj). apply bv_eq. exact E.
      - lia.
      - lia.
      - intros i Hi.
        pose proof (know_nth RSEGS _ _ u_knC ltac:(let k := kidx u_knC (is_kimg_cov 0x3a768 24) in exact k) _ HK eq_refl)
          as (_ & _ & Hnone). apply Hnone. lia. }
    assert (Hstk : store_ok RSEGS M' (Z_to_bv 64 (bv_unsigned spS - 32)) 32 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knC ltac:(let i := kidx u_knC (is_kwr_cov (EVar 0) (-1152) 32) in exact i)
                    _ _ _ (-1152) 32 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst spS. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 1120 - 32)%Z with (bv_unsigned sp0 + -1152)%Z by lia. exact Hst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2b68c4 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A2 : getr Rc 2 = spS)
        by (regv HR (2 : reg); subst spS; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A10 : getr Rc 10 = pp) by (regv HR (10 : reg); cbn [edenot ev ENV]; exact P1);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x7fffffff) by (regv HR (11 : reg); reflexivity);
      destruct (ref_strnlen M' pp spS (a0s ++ t8) L 0x7fffffff (seg_rom RSEGS) Rc (0x2b68c4 : word) MC
                  ltac:(lia) Hstk ltac:(subst spS; rewrite u_small by lia; lia)
                  ltac:(right; subst spS; rewrite u_small by lia; lia)
                  ltac:(apply ret_ok_even; reflexivity) A1 A2 A10 A11) as (R2 & M2 & Hms & Hkeep & HresP & Hfr);
      clear A1 A2 A10 A11
    end.
    replace (Z_to_bv 64 2870448) with (0x2bccb0 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x2b68c4 : word) with (Z_to_bv 64 0x2b68c4) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_saved
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    destruct Hfr as [Hagree Hgrow].
    pose proof (know_cut_sound RSEGS (ENV vals) M' M2 0 (-1152) (-1120) IHI u_knC
                  ltac:(unfold win_ok, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(intros x Hx; apply Hagree; cbn [outside]; split; [|exact I];
                        unfold in_rng; subst spS; unorm;
                        cbn [ev ENV] in Hx; rewrite P0 in Hx; lia)
                  Hgrow HK) as HK2.
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) M2 (kn_cut 0 (-1152) (-1120) IHI u_knC)
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 134%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q1 : vals_ev vals1 1 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    assert (Q112 : vals_ev vals1 112 = Z_to_bv 64 L).
    { subst vals1. change 112%nat with (102 + 10)%nat. rewrite <- HL. rewrite vals_ev_junk by lia. exact HresP. }
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK3.
    assert (HK : know_ok RSEGS (ENV vals1) M2 u_knD0).
    { unfold u_knD0. apply know_ok_cons; [|exact HK3].
      apply krange_intro. cbn [edenot ev ENV LX]. rewrite Q112, u_small by lia. lia. }
    clear HK3.
    assert (Hstr2 : rdn RSEGS M2 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite (frame_mod_rdn RSEGS M' M2 _ _ pp (conj Hagree Hgrow)); [exact Hstr' | | lia].
      intros i Hi. cbn [outside]. split; [|exact I]. unfold in_rng. subst spS. unorm. lia. }
    clear Hstr' Ht8' Hbuf Hz MC Hstk Hagree Hgrow HresP.
    assert (Psmall : (bv_unsigned (edenot (ENV vals1) (EVar 112)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite Q112, u_small by lia. lia. }
    (* [comment removed for export] *)
    run_blk_keep u_scrD 134%nat.
    { unfold sc_denot. cbn [branch_taken]. rewrite (edenot_addw0_r _ _ Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    { unfold sc_denot. exists [Z_to_bv 8 0]. split.
      - unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
        ed_lin ltac:(cbn [ev ENV]; rewrite ?Q1, ?Q112). rewrite <- HP.
        pose proof (rdn_byte_Z RSEGS M2 (bv_unsigned pp) (length a0s + 1) _ (length a0s)
                      ltac:(rewrite <- (word_Z pp); exact Hstr2) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
        rewrite app_nth2, Nat.sub_diag in B1 by lia. cbn [nth] in B1. exact B1.
      - reflexivity. }
    assert (Hstr3 : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M2 _ 0 0 4194304 IHI);
        [exact Hstr2 | vm_compute; reflexivity | unfold win_ok, IHI; cbn [ev ENV]; rewrite Q0; lia
        | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
    clear EQM Hstr2. rename M0 into M3.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x1169a) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2b5e94 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1169a) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x1169a) 0 _ (seg_rom RSEGS) MC Rc (0x2b5e94 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 2867236) with (0x2bc024 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x2b5e94 : word) with (Z_to_bv 64 0x2b5e94) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 u_knD ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals1 ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 166%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
    assert (W1 : vals_ev vals2 1 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q1).
    assert (W112 : vals_ev vals2 112 = Z_to_bv 64 L) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q112).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (HE0 vals2); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma us_segB : forall (a0s : list byte) (pp : word) (L : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length a0s) = L -> (0 <= L <= 131071)%Z -> ~ In (Z_to_bv 8 0) a0s ->
    length vals = 70%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) u_srB0 R -> know_ok RSEGS (ENV vals) M u_knB0 ->
    rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8 ->
    atUE0 a0s pp L T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b5e94) M (seg_rom RSEGS)) model) T.
  Proof.
    intros a0s pp L T t8 vals R M HP HPr Hnonul HL P0 P1 Hpp1 Hpp2 HR HK Hstr Ht8 HE0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    run_blk_keep scr0 70%nat.
    assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + L)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M3.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 553)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x1bc98) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2b5e94 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1bc98) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x1bc98) 0 _ (seg_rom RSEGS) MC Rc (0x2b5e94 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 2867236) with (0x2bc024 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x2b5e94 : word) with (Z_to_bv 64 0x2b5e94) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals (junk_vals R4) (blobs_ev BL) M3 u_knB ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 102%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (W1 : vals_ev vals2 1 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (us_segCD a0s pp L T t8 vals2); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma us_segH3 : forall vals R M,
    length vals = 262%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) u_srH30 R -> know_ok RSEGS (ENV vals) M u_knH30 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b6224) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 262%nat.
    close_exit_at HR HK P0 Hh Hlazy sp0 48%Z (-192)%Z.
  Qed.

  Lemma us_segG3 : forall vals R M,
    length vals = 230%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) u_srG30 R -> know_ok RSEGS (ENV vals) M u_knG30 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b63f4) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 230%nat.
    apply (rz_conseq RSEGS _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ [])) (t_exit (exit_code 2) (m_fs model)))).
    2:{ cbn [map app]. apply t_eq_sym. apply t_emit_nil_exit. }
    pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) u_srG3 u_knG3 Rc Mc model u_scG3 [] []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srG3 u_knG3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scG3 length Z.of_nat] end.
    - lia.
    - (* [comment removed for export] *) ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - lia.
    - cbn [edenot]. apply u_small. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - reflexivity.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (us_segH3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  Lemma us_segF3 : forall (a0s : list byte) (L : Z), Z.of_nat (length a0s) = L -> (67 <= L <= 73)%Z ->
    atUF0 a0s L (t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros a0s L HP HPr vals R M HL P0 P112 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk_keep u_scrF3 198%nat.
    { unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      rewrite <- (zbv_mod (-1 * L + 73)%Z).
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 553)) (length a0s) = Some a0s).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    krdv HK 0%nat (-560)%Z 7%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0. cbn [a_base a_off edenot ev ENV] in Hw0. rewrite P0, PRE7_word in Hw0.
    assert (B80 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (7 + length a0s) = Some (PRE7 ++ a0s)).
    { apply rdn_app_Z; [exact Hw0 | | lia | lia].
      replace (bv_unsigned sp0 + -560 + Z.of_nat 7)%Z with (bv_unsigned sp0 - 553)%Z by lia. exact SBp'. }
    assert (Hsuf : rdn RSEGS M' (Z_to_bv 64 0x1bc9a) 7 = Some SUF7).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ u_knF3 ltac:(let i := kidx u_knF3 (is_kimg_cov 0x1bc9a 7) in exact i)
                 _ _ 0x1bc9a 7 HK eq_refl) by (cbn; lia). apply suf7_img. }
    rewrite msg_usage_eq, app_assoc. unfold W.
    pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) u_srF3 u_knF3 Rc Mc model u_scF3 (PRE7 ++ a0s) SUF7
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srF3 u_knF3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scF3];
      rewrite ?length_app, ?PRE7_len, ?SUF7_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - (* [comment removed for export] *) ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - cbn [edenot]. apply u_small. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112). unorm.
      replace (7 + length a0s)%nat with (7 + length a0s)%nat by lia. exact B80.
    - cbn [edenot]. exact Hsuf.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (us_segG3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma us_segH4 : forall vals R M,
    length vals = 262%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) u_srH40 R -> know_ok RSEGS (ENV vals) M u_knH40 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b6224) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 262%nat.
    close_exit_at HR HK P0 Hh Hlazy sp0 48%Z (-192)%Z.
  Qed.

  Lemma us_segG4 : forall vals R M,
    length vals = 230%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) u_srG40 R -> know_ok RSEGS (ENV vals) M u_knG40 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b5e94) M (seg_rom RSEGS)) model)
               (t_emit (W 2 SUF7) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 230%nat.
    krdv HK 0%nat (-560)%Z 7%nat Hb. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    rewrite SUF7_word in Hb.
    unfold adenot, v_addi in Hb. cbn [a_base a_off edenot ev ENV] in Hb. rewrite P0 in Hb.
    replace (W 2 SUF7) with (map (WriteEv (Z_to_bv 64 2)) (SUF7 ++ [])) by (unfold W; rewrite app_nil_r; reflexivity).
    pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) u_srG4 u_knG4 Rc Mc model u_scG4 SUF7 []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n u_srG4 u_knG4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scG4];
      rewrite ?SUF7_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - (* [comment removed for export] *) ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot length Z.of_nat]. apply u_small. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hb.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (us_segH4 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  Lemma us_segEF4 : forall (a0s : list byte) (pp : word) (L : Z), Z.of_nat (length a0s) = L -> (74 <= L <= 131071)%Z ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + L + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    (bv_unsigned pp + L + 1 <= 0x800000000000)%Z ->   (* [comment removed for export] *)
    atUE0 a0s pp L (t_emit (W 2 (msg_usage a0s)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros a0s pp L HP HPr Hpp1 Hpp2 Hpp3 vals R M HL P0 P1 P112 HR HK Hstr.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (Psmall : (bv_unsigned (edenot (ENV vals) (EVar 112)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite P112, u_small by lia. lia. }
    run_blk_keep u_scrE4 166%nat.
    { unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P112).
      rewrite ltu_ZZ by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    { unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    assert (Hsrc : rdn RSEGS M' pp (length a0s) = Some a0s).
    { replace a0s with (firstn (length a0s) (a0s ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    krdv HK 0%nat (-560)%Z 7%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0. cbn [a_base a_off edenot ev ENV] in Hw0. rewrite P0, PRE7_word in Hw0.
    apply (rz_conseq RSEGS _ (t_emit (W 2 (PRE7 ++ a0s)) (t_emit (W 2 SUF7) (t_exit (exit_code 2) (m_fs model))))).
    2:{ rewrite msg_usage_eq, app_assoc. unfold W. rewrite (map_app _ (PRE7 ++ a0s)).
        apply t_eq_sym. apply t_emit_app. }
    unfold W at 1.
    pose proof u_itinerary as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) u_srE4 u_knE4 Rc Mc model u_scE4 PRE7 a0s
             (t_emit (W 2 SUF7) (t_exit (exit_code 2) (m_fs model))) HR HK
             (eq_trans (f_equal (fun n => stdio_call n u_srE4 u_knE4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn u_scE4];
      rewrite ?PRE7_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - (* [comment removed for export] *) ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV LX]. rewrite P112. rewrite u_small by lia. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - right. cbn [edenot ev ENV LX]. rewrite P1. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV LX]. rewrite P1, P112. rewrite u_small by lia. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hw0.
    - cbn [edenot ev ENV LX]. rewrite P1. exact Hsrc.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_emit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R1 M1 HR HK.
      clear Hstr' Hsrc Hw0 Psmall.
      lazymatch type of HK with know_ok _ _ _ ?k => change k with u_knF40 in HK end.
      lazymatch type of HR with regs_ok _ ?sr _ => change sr with u_srF40 in HR end.
      set (vals0 := vals) in P1, P112.
      set (vals1 := vals ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 198%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals1 vals0. clear HL P0 WOKS. clear vals. rename HL1 into HL. rename Q0 into P0.
      change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
      run_blk scr0 198%nat.
      lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ => rename Mc into MG end.
      set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
      assert (Hsuf : rdn RSEGS MG (Z_to_bv 64 0x1bc9a) 7 = Some SUF7).
      { rewrite (kimg_rdn RSEGS (ENV vals1) _ u_knF4 ltac:(let i := kidx u_knF4 (is_kimg_cov 0x1bc9a 7) in exact i)
                   _ _ 0x1bc9a 7 HK eq_refl) by (cbn; lia). apply suf7_img. }
      assert (Hdst : store_ok RSEGS MG dst 7 = true).
      { pose proof (kwr_store_ok RSEGS (ENV vals1) _ u_knF4 ltac:(let i := kidx u_knF4 (is_kwr_cov (EVar 0) (-560) 7) in exact i)
                      _ _ _ (-560) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
      assert (MC : mcH MG dst (Z_to_bv 64 0x1bc9a) 7 SUF7).
      { constructor; subst dst; rewrite ?u_small by lia; rewrite ?SUF7_len; try (cbn; lia).
        - exact Hsuf.
        - exact Hdst. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (A1 : getr Rc 1 = (0x2b5e94 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
        assert (A10 : getr Rc 10 = dst)
          by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
        assert (A11 : getr Rc 11 = Z_to_bv 64 0x1bc9a) by (regv HR (11 : reg); reflexivity);
        assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
        destruct (ref_memcpy MG dst (Z_to_bv 64 0x1bc9a) 7 _ (seg_rom RSEGS) MC Rc (0x2b5e94 : word)
                    ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
        clear A1 A10 A11 A12
      end.
      replace (Z_to_bv 64 2867236) with (0x2bc024 : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
      replace (0x2b5e94 : word) with (Z_to_bv 64 0x2b5e94) by (apply bv_eq; reflexivity).
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R2 callee_kept
                      ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
      rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
      pose proof (know_after_store RSEGS (ENV vals1) MG u_knF4 (SA (EVar 0) (-560)) 7 (ELit 2907475163367712) SUF7
                    u_knG40 [] [] ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
                    ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia)
                    ltac:(cbn [edenot]; symmetry; apply SUF7_word)) as HK2.
      clear HK.
      assert (Edst : adenot (ENV vals1) (SA (EVar 0) (-560)) = dst).
      { unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. subst dst. f_equal; lia. }
      rewrite Edst in HK2.
      pose proof (env_app_know RSEGS vals1 (junk_vals R2) (blobs_ev BL) (wbytes MG dst SUF7) u_knG40
                    ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
      clear HK2.
      set (vals2 := vals1 ++ junk_vals R2) in *.
      assert (HL2 : length vals2 = 230%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
      eapply (us_segG4 vals2); [exact HL2 | exact Q0 | exact HR | exact HK].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem us_tail : forall (a0s : list byte) (pp : word) (t8 : list byte) vals R M,
    ~ In (Z_to_bv 8 0) a0s -> (Z.of_nat (length a0s) <= 131071)%Z ->
    length vals = 70%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z ->
    (bv_unsigned pp + Z.of_nat (length a0s) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    (bv_unsigned pp + Z.of_nat (length a0s) + 1 <= 0x800000000000)%Z ->   (* [comment removed for export] *)
    regs_ok (ENV vals) u_srB0 R -> know_ok RSEGS (ENV vals) M u_knB0 ->
    rdn RSEGS M pp (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length a0s))) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b5e94) M (seg_rom RSEGS)) model)
               (t_die (msg_usage a0s) (m_fs model)).
  Proof.
    intros a0s pp t8 vals R M Hnonul HPl HL P0 P1 Hpp1 Hpp2 Hpp3 HR HK Hstr Ht8.
    unfold t_die.
    eapply (us_segB a0s pp (Z.of_nat (length a0s)) _ t8 vals); try eassumption; try lia.
    intros vals' R' M' HL' Q0 Q1 Q112 HR' HK' Hstr'.
    destruct (Z.le_gt_cases (Z.of_nat (length a0s)) 73) as [Hle | Hgt].
    - eapply (us_segE_gen a0s pp _ _ vals'); try eassumption; try lia.
      destruct (Z.le_gt_cases (Z.of_nat (length a0s)) 66) as [Hle2 | Hgt2].
      + apply us_segF; [reflexivity | lia].
      + apply us_segF3; [reflexivity | lia].
    - eapply (us_segEF4 a0s pp _ eq_refl); try eassumption; lia.
  Qed.

End UTail.
End H0Usage_tail.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ShapeAlg OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Nodes OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Hoare OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Frame OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MmapSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AllocSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FileSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AgentLib OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ArgvEnv OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MuslStrlen OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefLayout OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2 OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2Sound OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymRun OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDrive OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDriveX OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDriveH4 Spec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibWritev OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefNodes HUExitBase HUExit OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefMemcpyLib HUMemcpyBase HUMemcpy HUMemchr HUStrnlen HUStartup HUStartupFacts HUMainEntry OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibTail HUOpenFail_defs HUOpenFail_tail2.H0OpenFail_tail HUOpenFail_tail2.
Import HUMainEntryN HUUsage_defs H0Usage_tail.
Import HUStartupDefs.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Usage.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  (* [comment removed for export] *)
  Variable lim : Z.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hfits : entry_stack_fits sp0 av envv.   (* [comment removed for export] *)
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hargc : length av <> 2%nat.

  (* [comment removed for export] *)
  Let BL : list (list byte) := [[]; []; rnd16 rdraw; canary8 rdraw].

  Definition model0 : Model :=
    with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputA av envv fs0 stdin0)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Lemma model0_halted : m_halted model0 = None. Proof. reflexivity. Qed.
  Lemma model0_lazy : m_vm_lazy model0 = []. Proof. reflexivity. Qed.
  Lemma model0_fd2 : fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)). Proof. reflexivity. Qed.
  Lemma model0_fs : m_fs model0 = fs0. Proof. reflexivity. Qed.

  Lemma a0s_nonul : ~ In (Z_to_bv 8 0) (hd [] av).
  Proof.
    destruct Hva as ([H1 _] & _ & _ & Hn & _). destruct av as [|a0s rest]; [cbn in H1; lia|].
    inversion Hn; subst. assumption.
  Qed.

  Lemma hd_nth : hd [] av = nth 0 av [].
  Proof. destruct av; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma umemcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV BL vals) M u_logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE7.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE7_word. cbn [mem_denot u_logM1].
    unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
    f_equal; f_equal; lia.
  Qed.

  Lemma pre7_len_w : length (word_to_le_bytes 7 (Z_to_bv 64 9071406455288693)) = 7%nat.
  Proof. apply length_N_to_le_bytes. Qed.

  Theorem ref_usage :
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0xe1984) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_usage (hd [] av)) fs0).
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Hlen : (1 <= length av <= 1024)%nat) by (destruct Hva as [[H1 H2] _]; lia).
    assert (HR : regs_ok (EN sp0 av envv rdraw tid regs0) sr_mainN regs0) by (eapply main_regs_okN; eassumption).
    assert (HK : know_ok RSEGS (EN sp0 av envv rdraw tid regs0) mem0 kn_mainN) by (eapply main_know_okN; eassumption).
    assert (Hac : ev (EN sp0 av envv rdraw tid regs0) 16 = argcN av) by (eapply evN_argc; eassumption).
    change (EN sp0 av envv rdraw tid regs0) with (ENV BL (valsN sp0 av envv tid regs0)) in HR, HK, Hac.
    set (vals := valsN sp0 av envv tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold valsN; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0N sp0 av envv) by reflexivity.
    cbn [ev ENV] in Hac.
    edestruct (main_strN sp0 av envv uid hw rdraw tid regs0 mem0) as (Sr & Slo & Shi & Slen & [t8 Ht8] & Send); try eassumption.
    1:{ instantiate (1 := 0%nat). lia. }
    rewrite <- hd_nth in Sr, Slen, Ht8. set (a0s := hd [] av) in *.
    pose proof (u64_range (cat_argv_ptr sp0 av envv 0)) as Hppr.
    clearbody vals.
    pose proof model0_halted as Hh.
    (* [comment removed for export] *)
    run_blk_keep u_scrA 38%nat.
    { unfold sc_denot. cbn [branch_taken edenot ev ENV]. rewrite Hac.
      unfold bv_eqb. rewrite (u_argcN av Hva). change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
      apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
    assert (Habove : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x).
    { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV BL vals) mem0 _ 0%nat 0x354000);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
    clear EQM.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x1bc91) 7 = Some PRE7).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ u_knA ltac:(let i := kidx u_knA (is_kimg_cov 0x1bc91 7) in exact i)
                 _ _ 0x1bc91 7 HK eq_refl) by (cbn; lia). apply pre7_img. }
    assert (Hdst : store_ok RSEGS M dst 7 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ u_knA ltac:(let i := kidx u_knA (is_kwr_cov (EVar 0) (-560) 7) in exact i)
                    _ _ _ (-560) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x1bc91) 7 PRE7).
    { constructor; subst dst; rewrite ?u_small by lia; rewrite ?PRE7_len; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2b5e94 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1bc91) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x1bc91) 7 _ (seg_rom RSEGS) MC Rc (0x2b5e94 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 2867236) with (0x2bc024 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact model0_lazy | exact Hms |]. clear Hms.
    replace (0x2b5e94 : word) with (Z_to_bv 64 0x2b5e94) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst PRE7) u_knB0).
    { subst dst. rewrite <- (umemcpy1_denot vals M P0).
      eapply (carry_after RSEGS (ENV BL vals) M u_logM1 u_knA [] u_knB0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat u_logM1]. split; [lia|]. split; [|exact I].
      apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst PRE7) u_knB0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 70%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q1 : vals_ev vals1 1 = p0N sp0 av envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    rewrite <- model0_fs.
    eapply (us_tail sp0 model0 Hvsp model0_halted model0_lazy model0_fd2 BL a0s (p0N sp0 av envv) t8 vals1); try eassumption.
    - apply a0s_nonul.
    - unfold p0N. lia.
    - unfold p0N. subst a0s. rewrite hd_nth. lia.
    - unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
  Qed.

  Corollary ref_usage_w :
    realizes RSEGS (mkCfg (mkst regs0 (0xe1984 : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_usage (hd [] av)) fs0).
  Proof.
    replace (0xe1984 : word) with (Z_to_bv 64 0xe1984) by (apply bv_eq; reflexivity). apply ref_usage.
  Qed.

End Usage.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
