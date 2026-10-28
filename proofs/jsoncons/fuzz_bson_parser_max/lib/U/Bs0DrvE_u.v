(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
  MmapSim AllocSim FileSim AgentLib SpecConsts DivergeSim SpinAlg SpinAlgX
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame
  Spec LibWritev RefNodes RefMemcpyLib RefReadLib RefPrintfLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0StartupDefs_u Bs0Startup_u Bs0MainEntry_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import Hoare MemSplit Frame.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.musl Require Import Bs0MemcpyBase_u Bs0Memcpy_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0ExitBase_u Bs0StdioDefs_u Bs0Exit_u Bs0LibStdioCall_u Bs0LibMainRet_u Bs0PrintfBufBase_u Bs0PrintfBuf_u.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface LibIface DrvKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0Drv_defs_u Bs0DrvLib_u Bs0DrvA_u Bs0DrvB_u Bs0DrvC_defs_u Bs0DrvC_u Bs0DrvD_defs_u Bs0DrvLibL_u Bs0DrvD_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Local Ltac lia := first [ solve [ try (match goal with H : (length _ <= S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _)))))))))))))))))))))))))))))))))%nat |- _ => clear dependent H end); Lia.lia ] | Lia.lia ].

Tactic Notation "run_blockT" constr(scr) constr(NX) := run_block_gen FUEL STOPS_T scr NX false.
Tactic Notation "run_blockT_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_T scr NX true.
Tactic Notation "run_blockP_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_P scr NX true.
Tactic Notation "run_blockR_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_R scr NX true.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable scfg : SpuriousCfg.

#[using="Type"] Lemma length_zero_lines : forall j, length (zero_lines j) = (2 * j)%nat.
Proof. induction j as [|j IH]; [reflexivity|]. cbn [zero_lines length]. rewrite IH. lia. Qed.

#[using="Type"] Lemma zero_lines_snoc : forall j, zero_lines (S j) = zero_lines j ++ [Z_to_bv 8 48; Z_to_bv 8 10].
Proof. induction j as [|j IH]; [reflexivity|]. cbn [zero_lines]. rewrite IH at 1. reflexivity. Qed.

Section DrvE.
  Context {RE : RunEnv}.
  Variable L : heap_layout.
  Variable HI : heap_iface.
  Hypothesis HIok : heap_iface_ok L scfg HI.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable VM0 : VmMaps.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable fdata : list byte.
  Variable cr0 : credit.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hplen : (length path <= 4095)%nat.
  Hypothesis DL : drv_layout L sp0.
  Variable CAP : Z.
  Hypothesis HCAP : (65536 <= CAP <= 67108864)%Z.
  Variable crC : credit.
  Hypothesis HLEN : (Z.of_nat (length fdata) < CAP)%Z.
  Variable Lay : lib_layout.
  Variable LSt : lib_statics.
  Hypothesis DLL : drv_lib_layout Lay L.
  Hypothesis LIok : lib_iface_ok Lay scfg HI LSt.
  (* [comment removed for export] *)
  Hypothesis LSX : forall g M, ls_ok LSt g M -> exists ax : axv, atexit_cells M ax.

  Let Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z := conj (proj1 Hvsp) (proj1 (proj2 Hvsp)).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let LEN : Z := Z.of_nat (length fdata).
  Let ENVb (vals : list word) : env := ENV a0s path hw rdraw fdata vals.
  Let above (M : word -> option byte) : Prop := above_sp0 sp0 mem0 M.
  Let model2 (VM : VmMaps) : Model := model2 tid fs0 stdin0 VM.
  Let CFG : Z := CFG fdata.
  Let PL : Z := PL fdata.
  Let B2 : Z := B2 fdata.
  Let CALLS : Z := CALLS fdata.
  Let payload : list byte := payload fdata.
  Let lh_vals := lh_vals sp0 a0s path envv tid fdata.
  Let blk_facts := blk_facts L fdata CAP.
  Let lh1_k := lh1_k scfg L HI sp0 a0s path envv hw rdraw tid mem0 fs0 stdin0 fdata CAP crC.
  Let relay_regs := relay_regs sp0 a0s path hw rdraw tid mem0 VM0 fs0 stdin0 fdata Hvsp Htid Hplen CAP HCAP.
  Let relay_agree := relay_agree sp0 a0s path hw rdraw fdata Hplen.
  Let relay_len := relay_len sp0 path fdata Hplen.
  Let relay_lo := relay_lo sp0 path fdata Hplen.
  Let relay_81 := relay_81 sp0 path fdata Hplen.
  Let relay_101 := relay_101 sp0 path fdata Hplen.
  Let hiv_facts' := hiv_facts' sp0 a0s path envv uid hw rdraw Hva Hve Hvsp Hplen.
  Let content_block' := content_block' sp0 a0s path hw rdraw fdata Hvsp.

  Hypothesis Hok : (6 + CFG <= LEN)%Z.

  (* [comment removed for export] *)
  Definition E (n : nat) : TSet := t_emit (W 1 (zero_lines n)) (t_exit (exit_code 0) fs0).
  (* [comment removed for export] *)
  Definition WP (j : nat) : Z := (0xea7b0 + 2 * Z.of_nat j)%Z.

  (* [comment removed for export] *)
  Definition SSP (k : Z) (j : nat) (K : TSet) : Prop :=
    forall (fx' : PropExec.FPState) vals R M VM (A1 PTR OWN : Z) LB cr g,
      lh_vals vals A1 PTR OWN k -> vals_ev vals 84 = Z_to_bv 64 0 -> vals_ev vals 101 = Z_to_bv 64 (WP j) ->
      (Z.of_nat j + k <= 4)%Z -> (1 <= k)%Z ->
      regs_ok (ENVb vals) srLH R -> know_ok RSEGS (ENVb vals) M knLH2 ->
      above M -> blk_facts A1 PTR OWN LB ->
      rdn RSEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
      rdn RSEGS M (Z_to_bv 64 PTR) (length payload) = Some payload ->
      rdn RSEGS M (Z_to_bv 64 0xea7b0) (length (zero_lines j)) = Some (zero_lines j) ->
      hi_heap HI LB cr M VM -> credit_le (credit_scale (k - 1) (ll_credit Lay PL)) cr ->
      ls_ok LSt g M ->
      srealizes RSEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0x34628) M (seg_rom RSEGS)) (model2 VM)) K.

  (* [comment removed for export] *)
  Definition LH2P (k : Z) (j : nat) (K : TSet) : Prop :=
    forall (fx' : PropExec.FPState) vals R M VM (A1 PTR OWN : Z) LB cr g,
      lh_vals vals A1 PTR OWN k -> vals_ev vals 101 = Z_to_bv 64 (WP j) ->
      (Z.of_nat j + k <= 3)%Z -> (1 <= k)%Z ->
      regs_ok (ENVb vals) srLH R -> know_ok RSEGS (ENVb vals) M knLH2 ->
      above M -> blk_facts A1 PTR OWN LB ->
      rdn RSEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
      rdn RSEGS M (Z_to_bv 64 PTR) (length payload) = Some payload ->
      rdn RSEGS M (Z_to_bv 64 0xea7b0) (length (zero_lines j)) = Some (zero_lines j) ->
      hi_heap HI LB cr M VM -> credit_le (credit_scale k (ll_credit Lay PL)) cr ->
      ls_ok LSt g M ->
      srealizes RSEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0x34604) M (seg_rom RSEGS)) (model2 VM)) K.

  #[using="Type"] Lemma m2_but' : forall VM m', model_but_vm (model2 VM) m' -> m' = model2 (m_vmmaps m').
  Proof. intros VM m' H. exact H. Qed.
  #[using="sp0 path Hvsp Hplen CAP HCAP HLEN Hsp LEN CFG B2 CALLS Hok"] Lemma PL_range' : (0 <= PL <= 67108857)%Z.
  Proof. subst PL CFG LEN. unfold Bs0DrvC_u.PL. pose proof (CFG_range fdata). lia. Qed.

  (* [comment removed for export] *)
  #[using="sp0 Hplen LEN CFG PL B2 CALLS"] Lemma dec_val : forall vals k, vals_ev vals 81 = Z_to_bv 64 k -> (1 <= k <= 4)%Z ->
    edenot (ENVb vals) dec_x = Z_to_bv 64 (k - 1).
  Proof.
    intros vals k P81 Hk. unfold dec_x. cbn [edenot ev ENVb ENV]. rewrite P81.
    assert (k = 1 \/ k = 2 \/ k = 3 \/ k = 4)%Z as [-> |[-> |[-> | ->]]] by lia; vm_compute; reflexivity.
  Qed.

  #[using="sp0 Hplen LEN CFG PL B2 CALLS"] Lemma dec_sc : forall vals M k t, vals_ev vals 81 = Z_to_bv 64 k -> (1 <= k <= 4)%Z ->
    negb (Z.eqb (k - 1) 0) = t ->
    sc_denot RSEGS M (ENVb vals) (SCBr t BC_NE dec_x (ELit 0)).
  Proof.
    intros vals M k t P81 Hk Ht. cbn [sc_denot branch_taken]. rewrite (dec_val vals k P81 Hk). cbn [edenot].
    unfold bv_eqb. rewrite !u_small by lia. exact Ht.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition CANZ : Z := bv_unsigned (canary_w (ed_random rdraw)).
  #[using="Type"] Lemma can_of_know : forall vals M kn,
    know_ok RSEGS (ENVb vals) M kn -> kblob_find kn (ELit 0) 0xea230 = Some (ELit 8, 2%nat) ->
    rdn RSEGS M (Z_to_bv 64 0xea230) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 CANZ)).
  Proof.
    intros vals M kn HK Hc. unfold CANZ. rewrite Z_to_bv_bv_unsigned.
    pose proof (kblob_rdn RSEGS (ENVb vals) M kn (ELit 0) 0xea230 (ELit 8) 2%nat HK Hc) as R.
    replace (adenot (ENVb vals) (SA (ELit 0) 0xea230)) with (Z_to_bv 64 0xea230) in R by (apply bv_eq; vm_compute; reflexivity).
    cbn [eb ENVb ENV blobs_ev nth app blobs0] in R. rewrite length_word_to_le_bytes in R. exact R.
  Qed.
  #[using="Type"] Lemma CANZ_range : (0 <= CANZ < 2 ^ 64)%Z.
  Proof. unfold CANZ. apply u64_range. Qed.

  #[using="sp0 Hplen LEN CFG PL B2 CALLS"] Lemma ssp_of_know : forall vals M kn,
    know_ok RSEGS (ENVb vals) M kn ->
    kread RSEGS kn (ELit 0) 0xb71e8 8 = Some (ELit 0xea230) ->
    kblob_find kn (ELit 0) 0xea230 = Some (ELit 8, 2%nat) ->
    ssp_cells M (canary_w (ed_random rdraw)).
  Proof.
    intros vals M kn HK Hg Hc. split.
    - pose proof (kread_rdn RSEGS (ENVb vals) M kn (ELit 0) 0xb71e8 8 (ELit 0xea230) HK Hg ltac:(lia) ltac:(lia) ltac:(apply flat_abs0; lia)) as R.
      replace (adenot (ENVb vals) (SA (ELit 0) 0xb71e8)) with (Z_to_bv 64 0xb71e8) in R by (apply bv_eq; vm_compute; reflexivity). exact R.
    - pose proof (kblob_rdn RSEGS (ENVb vals) M kn (ELit 0) 0xea230 (ELit 8) 2%nat HK Hc) as R.
      replace (adenot (ENVb vals) (SA (ELit 0) 0xea230)) with (Z_to_bv 64 0xea230) in R by (apply bv_eq; vm_compute; reflexivity).
      cbn [eb ENVb ENV blobs_ev nth app blobs0] in R. rewrite length_word_to_le_bytes in R. exact R.
  Qed.

  #[using="HIok uid Hva Hve Hvsp Htid Hplen DL HCAP Hsp Hal LEN CFG PL B2 CALLS hiv_facts'"] Lemma tail_X : forall (fx' : PropExec.FPState) (j : nat) (ax : axv) vals R M VM (A1 : Z) cr,
    length vals = 134%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 48 = Z_to_bv 64 A1 ->
    vals_ev vals 3 = auxvp sp0 a0s path envv -> vals_ev vals 4 = rnd sp0 a0s path envv -> vals_ev vals 5 = tid ->
    vals_ev vals 84 = Z_to_bv 64 0 -> vals_ev vals 101 = Z_to_bv 64 (WP j) -> (Z.of_nat j <= 3)%Z ->
    regs_ok (ENVb vals) srX0 R -> know_ok RSEGS (ENVb vals) M knX0 ->
    block_range L A1 CAP ->
    rdn RSEGS M (Z_to_bv 64 0xea7b0) (length (zero_lines j)) = Some (zero_lines j) ->
    hi_heap HI [(A1, CAP)] cr M VM ->
    atexit_cells M ax ->      (* [comment removed for export] *)
    srealizes RSEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0x34644) M (seg_rom RSEGS)) (model2 VM)) (E j).
  Proof.
    intros fx' j ax vals R M VM A1 cr HL P0 P48 P3 P4 P5 P84 P101 Hj HR HK HBR HBUF HH HAX.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Q1 & Q2 & Q4).
    pose proof (hiv_facts' vals P3 P4) as HIV.
    (* [comment removed for export] *)
    run_blockT_keep scr0 134%nat.
    cbn [mem_denot] in EQM. subst M0.
    (* [comment removed for export] *)
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      destruct (main_ret_0 Rc M (seg_rom RSEGS) ltac:(regv HR (10 : reg); try (cbn [edenot ev ENVb ENV]; rewrite P84); reflexivity))
        as (R2 & MS & G8 & G10 & Gother) end.
    replace (Z_to_bv 64 214000) with (0x343f0%bv : word) by (apply bv_eq; reflexivity).
    eapply srz_msteps; [reflexivity | reflexivity | exact MS |]. clear MS.
    replace (0x34470%bv : word) with (Z_to_bv 64 0x34470) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    set (vals2 := vals ++ [getr R2 1; getr R2 11]).
    assert (HL2 : length vals2 = 136%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
    assert (HR2 : regs_ok (ENVb vals2) srY0 R2).
    { apply regs_ok_by_nth. intros i Hi.
      assert (AG : forall e, expr_vars_lt 134 e = true -> edenot (ENVb vals2) e = edenot (ENVb vals) e).
      { intros e He. symmetry. apply (edenot_agree 134); [| exact He]. subst vals2. rewrite <- HL. apply vals_app_agree. }
      destruct (Nat.eq_dec i 1) as [->|N1].
      { change (nth 1 srY0 (ELit 0)) with (EVar 134). cbn [edenot ev ENVb ENV]. subst vals2.
        rewrite <- HL, <- (Nat.add_0_r (length vals)), vals_ev_app_r. reflexivity. }
      destruct (Nat.eq_dec i 11) as [->|N11].
      { change (nth 11 srY0 (ELit 0)) with (EVar 135). cbn [edenot ev ENVb ENV]. subst vals2.
        replace 135%nat with (length vals + 1)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
      destruct (Nat.eq_dec i 8) as [->|N8]. { change (nth 8 srY0 (ELit 0)) with (ELit 0). exact G8. }
      destruct (Nat.eq_dec i 10) as [->|N10]. { change (nth 10 srY0 (ELit 0)) with (ELit 0). exact G10. }
      rewrite Gother by (intros E1; apply (f_equal ridx) in E1; rewrite ridx_lit in E1 by lia;
                         lazymatch type of E1 with i = ridx ?c => let v := eval vm_compute in (ridx c) in change (ridx c) with v in E1 end; lia).
      rewrite (HR (Z_to_bv 5 (Z.of_nat i))), sr_get_nat by lia.
      assert (EQi : nth i srY0 (ELit 0) = nth i srX (ELit 0) /\ expr_vars_lt 134 (nth i srX (ELit 0)) = true).
      { clear -Hi N1 N11 N8 N10. do 32 (destruct i as [|i]; [first [lia | (split; reflexivity)] |]). lia. }
      destruct EQi as [-> Ev]. symmetry. apply AG. exact Ev. }
    pose proof (env_app_know RSEGS vals [getr R2 1; getr R2 11] _ M knX0 ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
    fold vals2 in HK2. change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals2) in HK2.
    assert (Y0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Y3 : vals_ev vals2 3 = auxvp sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
    assert (Y4 : vals_ev vals2 4 = rnd sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P4).
    assert (Y5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
    assert (Y48 : vals_ev vals2 48 = Z_to_bv 64 A1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
    assert (Y101 : vals_ev vals2 101 = Z_to_bv 64 (WP j)) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P101).
    pose proof (hiv_facts' vals2 Y3 Y4) as HIV2.
    clear HR HK. rename HR2 into HR. rename HK2 into HK. clearbody vals2. clear Gother G8 G10 HL P0 P3 P4 P5 P48 P84 P101 HIV vals.
    (* [comment removed for export] *)
    run_blockT_keep scr0 136%nat.
    cbn [mem_denot] in EQM. subst M0.
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    lazymatch type of HK with know_ok _ _ _ ?knc =>
    eapply (free_site scfg L HI HIok sp0 Hsp' Hal' DL vals2 _ srY knc Rc Mc (model2 VM) [(A1, CAP)] cr A1 CAP (-128) [] [] 0x34478 (E j)) end;
      [ exact HR | exact HK
      | rewrite HL2; vm_compute; reflexivity | rewrite HL2; vm_compute; reflexivity | rewrite HL2; lia
      | exact Y0 | exact HIV2 | vm_compute; reflexivity
      | regv HR (2 : reg); cbn [edenot ev ENVb ENV]; rewrite Y0; apply alu_add_w_lit
      | lia | reflexivity
      | left; reflexivity
      | regv HR (10 : reg); cbn [edenot ev ENVb ENV]; exact Y48
      | regv HR (4 : reg); reflexivity
      | regv HR (1 : reg); reflexivity
      | lia | reflexivity
      | exact HH | reflexivity | reflexivity | reflexivity
      | intros i nb Hf; discriminate
      | intros v b Hf; discriminate
      | unfold E; apply t_emit_has_nil | ]
    end.
    clear HR HK.
    intros R' M' model' vals' E' HL' HR HK HH' HBUT HAB HBLK HIMG. subst vals' E'.
    rewrite (m2_but' _ _ HBUT).
    set (vals3 := vals2 ++ junk_vals R') in *.
    change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals3) in HR, HK.
    assert (Z0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Y0).
    assert (Z5 : vals_ev vals3 5 = tid) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Y5).
    assert (Z101 : vals_ev vals3 101 = Z_to_bv 64 (WP j)) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Y101).
    assert (HBUF' : rdn RSEGS M' (Z_to_bv 64 0xea7b0) (length (zero_lines j)) = Some (zero_lines j)).
    { rewrite <- HBUF. apply rdn_agree. intros q Hq. rewrite length_zero_lines in Hq. rewrite u_small by lia. apply HIMG; lia. }
    assert (HAX' : atexit_cells M' ax) by (apply (atexit_cells_frame M M' ax); [intros q Hq; apply HIMG; lia | exact HAX]).
    clear HBUF HIMG HBLK HAB.
    rewrite HL2 in HR. try rewrite HL2 in HK.
    (* [comment removed for export] *)
    run_blockT_keep scr0 168%nat.
    cbn [mem_denot] in EQM. subst M0.
    (* [comment removed for export] *)
    unfold E.
    lazymatch goal with |- srealizes _ _ (mkCfg _ ?model) _ =>
      apply (srz_conseq RSEGS scfg _ (t_emit (W 1 (zero_lines j)) (t_exit (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255)) (m_fs model))));
      [ | replace (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255)) with (exit_code 0) by (apply bv_eq; reflexivity); apply t_eq_refl ]
    end.
    apply ref_exit_Z.
    lazymatch type of HK with know_ok ?segs ?Ex ?Mx ?kn =>
      pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl) as Ktid;
      cbn [kentry_ok edenot ev ENVb ENV] in Ktid; rewrite Z5 in Ktid;
      exists (Z_to_bv 64 (bv_unsigned sp0 - 48)), (Z_to_bv 64 0xc9fc0), (bv_unsigned tid), (Z_to_bv 64 0), (Z_to_bv 64 0);
      split; [|split; [reflexivity|split; [reflexivity|]]];
      [ constructor;
        [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVb ENV];
          rewrite Z0; f_equal; lia
        | regv HR (4 : reg); reflexivity
        | regv HR (10 : reg); reflexivity
        | rewrite u_small by lia; lia
        | rewrite u_small by lia; lia
        | rewrite u_small by lia;
          pose proof (kwr_store_ok segs Ex _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-192) 144) in exact i)
                        _ _ _ (-192) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
          unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENVb ENV] in Hst; rewrite Z0 in Hst;
          replace (bv_unsigned sp0 - 48 - 144)%Z with (bv_unsigned sp0 + -192)%Z by lia; exact Hst
        | lit_u; lia
        | lit_u; lia
        | lia
        | lit_u; change (827328 - 168)%Z with 0xc9f18%Z;
          krd HK 0xc9f18%Z 4%nat Htc; rewrite Htc; cbn [ev ENVb ENV]; rewrite Z5;
          rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
          rewrite Z_to_bv_bv_unsigned; reflexivity
        | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | (exists ax; exact HAX') | krd_solve HK (* [comment removed for export] *) | krd_solve HK
        | repeat split; krd_solve HK
        | repeat split; krd_solve HK ]
      | ]
    end.
    (* [comment removed for export] *)
    destruct j as [|j'].
    - left. split; [reflexivity|]. exists (Z_to_bv 64 (WP 0)), (Z_to_bv 64 0).
      repeat split; try krd_solve HK; cbn [ev ENVb ENV]; rewrite ?Z101; reflexivity.
    - right. eexists 960432%Z, (WP (S j')), _, _, (Z_to_bv 64 0), (canary_w (ed_random rdraw)). split; [|reflexivity].
      pose proof rw_bytes_max_ge17 as RW. pose proof (length_zero_lines (S j')) as LZ.
      constructor; try exact HBUF'; try (rewrite ?LZ; unfold WP; lia); try krd_solve HK; try (cbn [ev ENVb ENV]; rewrite ?Z101; reflexivity).
      eapply ssp_of_know; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HIok uid Hva Hve Hvsp Htid Hplen DL HCAP Hsp Hal LEN CFG B2 CALLS hiv_facts' LSX"] Lemma last_S : forall j, SSP 1 j (E j).
  Proof.
    intros j. unfold SSP.
    intros fx' vals R M VM A1 PTR OWN LB cr g (HL & P0 & P1 & P2 & P3 & P4 & P5 & P48 & P70 & P73 & P79 & P81 & P82 & P83)
           P84 P101 Hjk Hk HR HK HA HBLK HC HPAY HBUF HH Hcr Hls.
    destruct (LSX g M Hls) as [ax HAX].
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    pose proof (hiv_facts' vals P3 P4) as HIV.
    (* [comment removed for export] *)
    assert (HR0 : regs_ok (ENVb vals) srS0 R).
    { apply regs_ok_upd_same; [exact HR | discriminate |]. rewrite (HR (19%bv : reg)). change (sr_get srLH 19) with (EVar 84). cbn [edenot ev ENVb ENV]. symmetry. exact P84. }
    clear HR. rename HR0 into HR.
    run_blockT_keep (SCR [false] [] []) 102%nat.
    { apply (dec_sc vals M 1 false P81); [lia | reflexivity]. }
    cbn [mem_denot] in EQM. subst M0.
    destruct HBLK as [HBR REST].
    pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Q1 & Q2 & Q4).
    destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)]; subst LB.
    - (* [comment removed for export] *)
      pose proof (hio_free_null L scfg HI HIok) as FN. unfold free_null_spec in FN.
      rewrite (dl_segs L sp0 DL), (dl_free L sp0 DL) in FN.
      lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        apply (FN fx' Rc M (model2 VM) (E j));
        [ reflexivity | reflexivity
        | regv HR (10 : reg); cbn [edenot ev ENVb ENV]; rewrite P83, HOWN; reflexivity
        | regv HR (1 : reg); apply ret_ok_even; reflexivity
        | unfold E; apply t_emit_has_nil
        | ];
        intros R' HPres; rewrite (reg_val _ _ _ (1 : reg) HR); change (edenot (ENVb vals) (sr_get srS_ft 1)) with (Z_to_bv 64 0x34644)
      end.
      pose proof (regs_after_keeps vals _ srS_ft _ R' c_kept ltac:(rewrite HL; vm_compute; reflexivity) HR
                    (regs_preserved_kept sp0 Hsp' _ R' HPres) c_kept_no0) as HR'.
      rewrite HL in HR'. change (sr_after_call_j srS_ft (map ridx c_kept) 102) with srX0 in HR'.
      pose proof (env_app_know RSEGS vals (junk_vals R') _ M knLH2 ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK'.
      apply (tail_X fx' j ax (vals ++ junk_vals R') R' M VM A1 cr);
        try (rewrite vals_ev_app_l by (rewrite HL; lia); assumption).
      + rewrite length_app, junk_vals_length, HL. reflexivity.
      + lia.
      + exact HR'.
      + eapply ksubl_sound; [exact HK' | vm_compute; reflexivity].
      + exact HBR.
      + exact HBUF.
      + exact HH.
      + exact HAX.
    - (* [comment removed for export] *)
      subst PTR.
      lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      eapply (free_site scfg L HI HIok sp0 Hsp' Hal' DL vals _ srS_ft knLH2 Rc M (model2 VM) [(OWN, PL); (A1, CAP)] cr OWN PL (-208)
                [(48%nat, 65536%Z)] [] 0x34644 (E j));
        [ exact HR | exact HK
        | rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia
        | exact P0 | exact HIV | vm_compute; reflexivity
        | regv HR (2 : reg); cbn [edenot ev ENVb ENV]; rewrite P0; apply alu_add_w_lit
        | lia | reflexivity
        | left; reflexivity
        | regv HR (10 : reg); cbn [edenot ev ENVb ENV]; exact P83
        | regv HR (4 : reg); reflexivity
        | regv HR (1 : reg); reflexivity
        | lia | reflexivity
        | exact HH | reflexivity | reflexivity | reflexivity
        | intros i nb Hf; cbn in Hf;
          destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL; lia|];
                                           rewrite P48, u_small by lia; exists CAP; split; [lia|]; split; [| exact HBR];
                                           cbn [lb_remove fst]; rewrite Z.eqb_refl; left; reflexivity
                                         | discriminate]
        | intros v b Hf; discriminate
        | unfold E; apply t_emit_has_nil | ]
      end.
      clear HR HK.
      intros R' M' model' vals' E' HL' HR HK HH' HBUT HAB HBLK' HIMG. subst vals' E'.
      rewrite (m2_but' _ _ HBUT).
      cbn [lb_remove fst] in HH'. rewrite Z.eqb_refl in HH'.
      rewrite HL in HR. try rewrite HL in HK. change (sr_after_call_j srS_ft (map ridx c_kept) 102) with srX0 in HR.
      change (keep_alloc (-208) [(48%nat, 65536%Z)] [] knLH2) with knX0 in HK.
      apply (tail_X fx' j ax (vals ++ junk_vals R') R' M' (m_vmmaps model') A1 cr);
        try (rewrite vals_ev_app_l by (rewrite HL; lia); assumption).
      + rewrite length_app, junk_vals_length, HL. reflexivity.
      + lia.
      + exact HR.
      + exact HK.
      + exact HBR.
      + rewrite <- HBUF. apply rdn_agree. intros q Hq. rewrite length_zero_lines in Hq. rewrite u_small by lia. apply HIMG; lia.
      + exact HH'.
      + apply (atexit_cells_frame M M' ax); [intros q Hq; apply HIMG; lia | exact HAX].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition relay2 (vals : list word) (R : bvmap 5 word) (W : word) : list word :=
    firstn 81 vals ++ (getr R 21 :: tl (lay_ext vals R W)).
  Definition shared_pos2 : list nat := [2; 3; 4; 8; 20; 22; 23; 24; 25; 26; 27]%nat.
  Definition relay2_ok_b (sr : list expr) : bool :=
    forallb (fun i => expr_eqb (nth i sr (ELit 0)) (nth i srLH (ELit 0)) && expr_vars_lt 81 (nth i sr (ELit 0))) shared_pos2.

  #[using="sp0 path fdata Hplen LEN CFG PL B2 CALLS"] Lemma relay2_len : forall vals R W, (81 <= length vals)%nat -> length (relay2 vals R W) = 102%nat.
  Proof. intros. unfold relay2. rewrite len_lay by lia. reflexivity. Qed.
  #[using="sp0 path fdata Hplen LEN CFG PL B2 CALLS"] Lemma relay2_lo : forall vals R W j, (81 <= length vals)%nat -> (j < 81)%nat -> vals_ev (relay2 vals R W) j = vals_ev vals j.
  Proof. intros. unfold relay2. apply vals_lo; lia. Qed.
  #[using="sp0 path fdata Hplen LEN CFG PL B2 CALLS"] Lemma relay2_hi : forall vals R W i, (81 <= length vals)%nat ->
    vals_ev (relay2 vals R W) (81 + i) = nth i (getr R 21 :: tl (lay_ext vals R W)) (Z_to_bv 64 0).
  Proof. intros. unfold relay2. apply vals_hi. lia. Qed.
  #[using="sp0 Hplen LEN CFG PL B2 CALLS"] Lemma relay2_agree : forall vals R W, (81 <= length vals)%nat ->
    env_agree 81 (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) (ENVb (relay2 vals R W)).
  Proof.
    intros vals R W HL. split; [|reflexivity]. intros n Hn. cbn [ev ENVb ENV]. symmetry. apply relay2_lo; lia.
  Qed.
  #[using="RE L sp0 envv tid mem0 VM0 fs0 stdin0 Hvsp Hplen CAP Hsp LEN above model2 CFG PL B2 CALLS lh_vals blk_facts"] Lemma relay2_regs : forall vals sr R W,
    (81 <= length vals)%nat -> relay2_ok_b sr = true ->
    regs_ok (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) sr R ->
    regs_ok (ENVb (relay2 vals R W)) srLH R.
  Proof.
    intros vals sr R W HL Hokb HR.
    unfold relay2_ok_b in Hokb. rewrite forallb_forall in Hokb.
    assert (SH : forall i, In i shared_pos2 -> getr R (Z_to_bv 5 (Z.of_nat i)) = edenot (ENVb (relay2 vals R W)) (nth i srLH (ELit 0))).
    { intros i Hi. pose proof (Hokb i Hi) as H. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1.
      rewrite <- H1. rewrite <- (edenot_agree 81 _ _ _ (relay2_agree vals R W HL) H2).
      assert (Hi32 : (0 < i < 32)%nat) by (unfold shared_pos2 in Hi; cbn in Hi; lia).
      rewrite (HR (Z_to_bv 5 (Z.of_nat i))), sr_get_nat by exact Hi32. reflexivity. }
    apply regs_ok_by_nth. intros i Hi.
    assert (JK : forall r k, nth r srLH (ELit 0) = EVar (81 + k) ->
                 nth k (getr R 21 :: tl (lay_ext vals R W)) (Z_to_bv 64 0) = getr R (Z_to_bv 5 (Z.of_nat r)) ->
                 getr R (Z_to_bv 5 (Z.of_nat r)) = edenot (ENVb (relay2 vals R W)) (nth r srLH (ELit 0))).
    { intros r k Hr Hk2. rewrite Hr. cbn [edenot ev ENVb ENV]. rewrite relay2_hi by lia. symmetry. exact Hk2. }
    do 32 (destruct i as [|i]; [first [lia | apply SH; cbn; tauto | eapply JK; reflexivity] |]). lia.
  Qed.

  #[using="VM0 Hvsp Hplen Hsp LEN CFG B2 CALLS"] Lemma step_S : forall k j K, (2 <= k)%Z -> LH2P (k - 1) j K -> SSP k j K.
  Proof.
    intros k j K Hk2 HLH. unfold SSP.
    intros fx' vals R M VM A1 PTR OWN LB cr g (HL & P0 & P1 & P2 & P3 & P4 & P5 & P48 & P70 & P73 & P79 & P81 & P82 & P83)
           P84 P101 Hjk Hk HR HK HA HBLK HC HPAY HBUF HH Hcr Hls.
    (* [comment removed for export] *)
    assert (HR0 : regs_ok (ENVb vals) srS0 R).
    { apply regs_ok_upd_same; [exact HR | discriminate |]. rewrite (HR (19%bv : reg)). change (sr_get srLH 19) with (EVar 84). cbn [edenot ev ENVb ENV]. symmetry. exact P84. }
    clear HR. rename HR0 into HR.
    run_blockT_keep (SCR [true] [] []) 102%nat.
    { apply (dec_sc vals M k true P81); [lia | apply Bool.negb_true_iff; apply Z.eqb_neq; lia]. }
    cbn [mem_denot] in EQM. subst M0.
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ => rename Rc into RS end.
    assert (V81 : getr RS 21 = Z_to_bv 64 (k - 1)).
    { regv HR (21 : reg). change (sr_get srS_tk 21) with dec_x. apply (dec_val vals k P81). lia. }
    set (valsL := relay2 vals RS (Z_to_bv 64 (WP j))).
    apply (HLH fx' valsL RS M VM A1 PTR OWN LB cr g).
    - unfold lh_vals, Bs0DrvD_u.lh_vals. subst valsL. rewrite (relay2_len vals RS _ ltac:(lia)).
      rewrite !(relay2_lo vals RS _) by lia.
      repeat split; try assumption.
      + change 81%nat with (81 + 0)%nat. rewrite relay2_hi by lia. exact V81.
      + change 82%nat with (81 + 1)%nat. rewrite relay2_hi by lia. cbn [nth tl lay_ext]. regv HR (9 : reg). cbn [edenot ev ENVb ENV]. exact P82.
      + change 83%nat with (81 + 2)%nat. rewrite relay2_hi by lia. cbn [nth tl lay_ext]. regv HR (18 : reg). cbn [edenot ev ENVb ENV]. exact P83.
    - subst valsL. change 101%nat with (81 + 20)%nat. rewrite relay2_hi by lia. reflexivity.
    - lia.
    - lia.
    - subst valsL. eapply (relay2_regs vals srS_tk RS _ ltac:(lia)); [vm_compute; reflexivity | exact HR].
    - (* [comment removed for export] *)
      subst valsL. unfold knLH2 in HK |- *.
      pose proof (Forall_inv HK) as K1. pose proof (Forall_inv (Forall_inv_tail HK)) as K2.
      pose proof (Forall_inv_tail (Forall_inv_tail HK)) as K3.
      constructor; [|constructor].
      + cbn [kentry_ok] in K1 |- *. destruct K1 as (K1a & K1b & K1c). split; [exact K1a|]. split; [exact K1b|].
        rewrite SymDriveX.adenot_lit0 in K1c |- *. cbn [edenot ev ENVb ENV] in K1c |- *.
        change 101%nat with (81 + 20)%nat. rewrite relay2_hi by lia. cbn [nth tl lay_ext]. rewrite P101 in K1c. exact K1c.
      + cbn [kentry_ok edenot ev ENVb ENV] in K2 |- *. change 101%nat with (81 + 20)%nat. rewrite relay2_hi by lia. cbn [nth tl lay_ext].
        rewrite P101 in K2. exact K2.
      + eapply (know_ok_agree RSEGS 81); [apply relay2_agree; lia | vm_compute; reflexivity | exact K3].
    - exact HA.
    - exact HBLK.
    - exact HC.
    - exact HPAY.
    - exact HBUF.
    - exact HH.
    - exact Hcr.
    - exact Hls.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pf_rs (w : Z) : list (word * Z) :=
    [(Z_to_bv 64 (bv_unsigned sp0 - 208 - 1056), 1056%Z); (Z_to_bv 64 0xb83f0, 4%Z); (Z_to_bv 64 0xb8418, 8%Z); (Z_to_bv 64 w, 2%Z)].
  Definition CPpf (w : Z) (a : Z) : Prop :=
    (~ (bv_unsigned sp0 - 208 - 1056 <= a < bv_unsigned sp0 - 208) /\ ~ (0xb83f0 <= a < 0xb83f4) /\ ~ (0xb8418 <= a < 0xb8420) /\ ~ (w <= a < w + 2))%Z.
  Definition SCpf (a : Z) : Prop := (bv_unsigned sp0 - 208 - 1056 <= a < bv_unsigned sp0 - 208)%Z.

  #[using="path fdata Hvsp Hplen Hsp LEN CFG PL B2 CALLS"] Lemma CPpf_outside : forall w a, (0 <= a < 2 ^ 64)%Z -> (0xea7b0 <= w <= 0xeabae)%Z -> CPpf w a -> outside (Z_to_bv 64 a) (pf_rs w).
  Proof.
    intros w a Ha Hw (C1 & C2 & C3 & C4). pose proof Hsp as Hsp'.
    cbn [outside pf_rs]. unfold in_rng. rewrite !u_small by lia. repeat split; lia.
  Qed.

  #[using="Hvsp Hplen Hsp LEN CFG PL B2 CALLS"] Lemma regions_pf : forall vals (w A1 : Z),
    vals_ev vals 0 = sp0 -> vals_ev vals 48 = Z_to_bv 64 A1 -> hz sp0 A1 65536 ->
    (0xea7b0 <= w <= 0xeabae)%Z ->
    (forall i, In i [3%nat; 4%nat] -> (bv_unsigned sp0 <= bv_unsigned (vals_ev vals i))%Z /\ (bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64)%Z) ->
    regions_ok RSEGS 0 (-208) 1056 [(48%nat, 65536%Z)] [] [3%nat; 4%nat] IMG_PF IMG_RW (ENVb vals) (CPpf w) SCpf.
  Proof.
    intros vals w A1 P0 P48 (HA1 & HA2 & HA3) Hw Hhi. pose proof Hsp as Hsp'.
    constructor; cbn [ev ENVb ENV]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CPpf. lia.
    - intros z Hz. right. unfold SCpf. lia.
    - intros i nb Hf. cbn in Hf. destruct (Nat.eqb i 48) eqn:Ei; [|discriminate]. apply Nat.eqb_eq in Ei. subst i. injection Hf as <-.
      rewrite P48, u_small by lia. split; [lia|]. intros z Hz. unfold CPpf. lia.
    - intros v b Hf. discriminate.
    - intros i Hi. destruct (Hhi i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|]. intros z Hz. unfold CPpf. lia.
    - intros lo hi Hin. unfold IMG_PF in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; unfold CPpf; lia.
    - intros lo hi Hin. unfold IMG_RW in Hin.
      destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros Mx d m Hd Hm.
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xb1000) _ 28672%nat m 0xb1000 0xb8000);
          [reflexivity | reflexivity | lia | apply wseg_5addc | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xb8000) _ 208896%nat m 0xb8000 0xeb000);
          [reflexivity | reflexivity | lia | apply wseg_5fddc | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Hvsp Hplen Hsp LEN CFG PL B2 CALLS"] Lemma know_pf : forall vals M M' kn (w A1 : Z),
    vals_ev vals 0 = sp0 -> vals_ev vals 48 = Z_to_bv 64 A1 -> hz sp0 A1 65536 ->
    (0xea7b0 <= w <= 0xeabae)%Z ->
    (forall i, In i [3%nat; 4%nat] -> (bv_unsigned sp0 <= bv_unsigned (vals_ev vals i))%Z /\ (bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64)%Z) ->
    know_ok RSEGS (ENVb vals) M kn -> has_window kn = true ->
    frame_mod M M' (pf_rs w) ->
    know_ok RSEGS (ENVb vals) M' (keep_pf kn).
  Proof.
    intros vals M M' kn w A1 P0 P48 HZ Hw Hhi HK Hwin [HFe HFg]. pose proof Hsp as Hsp'.
    unfold keep_pf.
    eapply (know_keep_sound RSEGS 0 (-208) 1056 [(48%nat, 65536%Z)] [] [3%nat; 4%nat] IMG_PF IMG_RW (ENVb vals) (CPpf w) SCpf).
    - eapply regions_pf; eassumption.
    - intros a Ha HC. apply HFe. apply CPpf_outside; assumption.
    - intros a Ha. apply HFg. destruct (has_window_nth kn Hwin) as [i Hn].
      pose proof (kwr_store_ok RSEGS (ENVb vals) M kn i (EVar 0) (-8388608) 8388608 (a - bv_unsigned sp0) 1%nat HK Hn
                    ltac:(unfold SCpf in Ha; lia) ltac:(unfold SCpf in Ha; cbn; lia)) as W.
      unfold adenot in W. cbn [a_base a_off edenot ev ENVb ENV] in W. rewrite P0 in W. unfold v_addi in W.
      replace (bv_unsigned sp0 + (a - bv_unsigned sp0))%Z with a in W by lia.
      apply (window_defined M a); [unfold SCpf in Ha; lia | unfold SCpf in Ha; lia | exact W].
    - exact HK.
  Qed.

  (* [comment removed for export] *)
  #[using="scfg L HIok path fdata Hvsp Hplen DL Hsp LEN CFG PL B2 CALLS"] Lemma heap_pf : forall LB cr M M' VM w, hi_heap HI LB cr M VM -> frame_mod M M' (pf_rs w) -> (0xea7b0 <= w <= 0xeabae)%Z ->
    hi_heap HI LB cr M' VM.
  Proof.
    intros LB cr M M' VM w HH [HFe HFg] Hw. pose proof Hsp as Hsp'.
    pose proof (dl_ro L sp0 DL) as RO. pose proof (dl_static L sp0 DL) as STA.
    pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
    apply (hio_frame L scfg HI HIok LB cr M M' VM HH).
    - intros a Ha Hpriv. apply HFe. apply CPpf_outside; [exact Ha | exact Hw |]. unfold CPpf.
      destruct Hpriv as [[A [_ B]]|A].
      + rewrite (dl_sptop L sp0 DL) in A. rewrite IL, IH in B.
        assert (~ (0xb8000 <= a < 0xeb000) \/ hl_alloc_static L a)%Z as [C|C] by (destruct (Z_lt_ge_dec a 0xb8000); [left; lia|]; destruct (Z_lt_ge_dec a 0xeb000); [|left; lia]; right; apply Classical_Prop.NNPP; intros Hn; apply B; split; [lia| exact Hn]).
        * lia.
        * apply STA in C. lia.
      + apply RO in A. lia.
    - exact HFg.
  Qed.

  #[using="scfg L HI path fdata Hvsp Hplen DL Lay DLL LIok Hsp LEN CFG PL B2 CALLS"] Lemma ls_pf : forall g M M' w, ls_ok LSt g M -> frame_mod M M' (pf_rs w) -> (0xea7b0 <= w <= 0xeabae)%Z -> ls_ok LSt g M'.
  Proof.
    intros g M M' w Hls [HFe HFg] Hw. pose proof Hsp as Hsp'.
    apply (lio_frame Lay scfg HI LSt LIok g M M' Hls).
    - intros a Ha Hf. apply HFe. apply CPpf_outside; [exact Ha | exact Hw |].
      destruct Hf as (iv & Hin & Hr). apply (dll_foot Lay L DLL) in Hin. unfold CPpf. lia.
    - intros a Ha Hn. rewrite <- (Z_to_bv_bv_unsigned 64 a). rewrite HFe; [rewrite Z_to_bv_bv_unsigned; exact Hn|].
      pose proof (dll_rw_lo Lay L DLL). pose proof (u64_range a).
      apply CPpf_outside; [lia | exact Hw |]. unfold CPpf. lia.
    - intros a Ha Hi. apply HFe. apply CPpf_outside; [exact Ha | exact Hw |].
      destruct Hi as [(iv & Hin & Hr) | Hi].
      + apply (dll_initc Lay L DLL) in Hin. unfold CPpf. lia.
      + rewrite (dll_heap Lay L DLL), (dl_sptop L sp0 DL) in Hi. unfold CPpf. lia.
  Qed.

  #[using="path fdata Hvsp Hplen Hsp LEN CFG PL B2 CALLS"] Lemma above_pf : forall M M' w, above M -> frame_mod M M' (pf_rs w) -> (0xea7b0 <= w <= 0xeabae)%Z -> above M'.
  Proof.
    intros M M' w HA [HFe HFg] Hw a Ha. pose proof Hsp as Hsp'. pose proof (u64_range a).
    rewrite <- (Z_to_bv_bv_unsigned 64 a). rewrite HFe; [rewrite Z_to_bv_bv_unsigned; apply HA; exact Ha|].
    apply CPpf_outside; [lia | exact Hw |]. unfold CPpf. lia.
  Qed.

  #[using="path fdata Hvsp Hplen Hsp LEN CFG PL B2 CALLS"] Lemma rdn_pf : forall M M' w (a : Z) n data, frame_mod M M' (pf_rs w) -> (0xea7b0 <= w <= 0xeabae)%Z ->
    (forall i, (a <= i < a + Z.of_nat n)%Z -> CPpf w i) -> (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
    rdn RSEGS M (Z_to_bv 64 a) n = Some data -> rdn RSEGS M' (Z_to_bv 64 a) n = Some data.
  Proof.
    intros M M' w a n data HF Hw HC Ha Han HR. rewrite <- HR. apply (frame_mod_rdn RSEGS M M' (pf_rs w) n); [exact HF | | rewrite u_small by lia; lia].
    intros i Hi. rewrite u_small by lia. apply CPpf_outside; [lia | exact Hw | apply HC; lia].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition IMG_FL : list (Z * Z) := [(0xc8550, 0xc8558)]%Z.
  Definition CPfl (a : Z) : Prop := ((0xc8550 <= a < 0xc8558) \/ (bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0))%Z.

  #[using="Hvsp Hplen Hsp LEN CFG PL B2 CALLS"] Lemma regions_fl : forall vals, vals_ev vals 0 = sp0 ->
    regions_ok RSEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_FL [] (ENVb vals) CPfl (fun _ => True).
  Proof.
    intros vals P0. pose proof Hsp as Hsp'.
    constructor; cbn [ev ENVb ENV]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CPfl. lia.
    - intros z Hz. right. exact I.
    - intros i nb Hf. discriminate.
    - intros v b Hf. discriminate.
    - intros i [].
    - intros lo hi Hin. unfold IMG_FL in Hin.
      destruct Hin as [E1|[]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; unfold CPfl; lia.
    - intros lo hi [].
  Qed.

  (* [comment removed for export] *)
  #[using="scfg L HIok Hvsp Hplen DL Lay DLL LIok Hsp LEN CFG PL B2 CALLS"] Lemma block_fl : forall vals M log LB cr VM g,
    vals_ev vals 0 = sp0 ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_FL log = true ->
    (hi_heap HI LB cr M VM -> hi_heap HI LB cr (mem_denot (ENVb vals) M log) VM)
    /\ (above M -> above (mem_denot (ENVb vals) M log))
    /\ (ls_ok LSt g M -> ls_ok LSt g (mem_denot (ENVb vals) M log))
    /\ (forall (a : Z) n bs, (0 <= a)%Z -> (a + Z.of_nat n <= 0xc8550 \/ (0xc8558 <= a /\ a + Z.of_nat n <= bv_unsigned sp0 - 8388608))%Z ->
          rdn RSEGS M (Z_to_bv 64 a) n = Some bs -> rdn RSEGS (mem_denot (ENVb vals) M log) (Z_to_bv 64 a) n = Some bs).
  Proof.
    intros vals M log LB cr VM g P0 Hlog. pose proof Hsp as Hsp'.
    pose proof (dl_ro L sp0 DL) as RO. pose proof (dl_static L sp0 DL) as STA.
    pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
    assert (FR : forall a, (0 <= a < 2 ^ 64)%Z -> ~ CPfl a -> mem_denot (ENVb vals) M log (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hn. exact (mem_denot_frame_Z RSEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_FL (ENVb vals) CPfl (fun _ => True) [] (regions_fl vals P0) M log a Hlog Ha Hn). }
    split; [|split; [|split]].
    - intros HH. apply (hio_frame L scfg HI HIok LB cr M _ VM HH).
      + intros a Ha Hpriv. apply FR; [exact Ha|]. unfold CPfl.
        destruct Hpriv as [[A [_ B]]|A].
        * rewrite (dl_sptop L sp0 DL) in A. rewrite IL, IH in B.
          assert (~ (0xb8000 <= a < 0xeb000) \/ hl_alloc_static L a)%Z as [C|C]
            by (destruct (Z_lt_ge_dec a 0xb8000); [left; lia|]; destruct (Z_lt_ge_dec a 0xeb000); [|left; lia];
                right; apply Classical_Prop.NNPP; intros Hn; apply B; split; [lia| exact Hn]).
          -- lia.
          -- apply STA in C. lia.
        * apply RO in A. lia.
      + intros x Hx. exact (mem_denot_grows (ENVb vals) M log x Hx).
    - intros HA a Ha. pose proof (u64_range a) as Hu. rewrite <- (Z_to_bv_bv_unsigned 64 a). rewrite FR; [rewrite Z_to_bv_bv_unsigned; apply HA; exact Ha | lia | unfold CPfl; lia].
    - intros Hls. apply (lio_frame Lay scfg HI LSt LIok g M _ Hls).
      + intros a Ha Hf. apply FR; [exact Ha|]. destruct Hf as (iv & Hin & Hr). apply (dll_foot Lay L DLL) in Hin. unfold CPfl. lia.
      + intros a Ha Hn. pose proof (dll_rw_lo Lay L DLL). pose proof (u64_range a).
        rewrite <- (Z_to_bv_bv_unsigned 64 a), FR; [rewrite Z_to_bv_bv_unsigned; exact Hn | lia | unfold CPfl; lia].
      + intros a Ha Hi. apply FR; [exact Ha|]. destruct Hi as [(iv & Hin & Hr) | Hi].
        * apply (dll_initc Lay L DLL) in Hin. unfold CPfl. lia.
        * rewrite (dll_heap Lay L DLL), (dl_sptop L sp0 DL) in Hi. unfold CPfl. lia.
    - intros a n bs Ha0 Han HR.
      rewrite <- HR. apply rdn_agree. intros q Hq. rewrite u_small by lia. apply FR; [lia | unfold CPfl; lia].
  Qed.

  #[using="HIok uid VM0 Hva Hve Hvsp Htid Hplen DL HCAP crC HLEN DLL LIok Hsp Hal LEN CFG B2 CALLS lh1_k relay_regs relay_agree relay_len relay_lo relay_81 relay_101 hiv_facts' Hok"] Lemma iter2 : forall k j K, (1 <= k)%Z -> K [] -> SSP k (S j) K -> LH2P k j K.
  Proof.
    intros k j K Hk1 HK0 HSS. unfold LH2P.
    intros fx' vals R M VM A1 PTR OWN LB cr g (HL & P0 & P1 & P2 & P3 & P4 & P5 & P48 & P70 & P73 & P79 & P81 & P82 & P83)
           P101 Hjk Hk HR HK HA HBLK HC HPAY HBUF HH Hcr Hls.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    pose proof (hiv_facts' vals P3 P4) as HIV.
    destruct HBLK as [HBR REST].
    pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Q1 & Q2 & Q4).
    pose proof PL_range' as HPr. pose proof (payload_len fdata) as PLN. fold PL in PLN. fold payload in PLN.
    pose proof (dll_credit_pos Lay L DLL PL ltac:(lia)) as [CP1 CP2].
    (* [comment removed for export] *)
    run_blockT_keep scr0 102%nat.
    lazymatch type of EQM with _ = mem_denot _ _ ?lg =>
      destruct (block_fl vals M lg LB cr VM g P0 ltac:(vm_compute; reflexivity)) as (BH & BA & BL & BRd) end.
    rewrite <- EQM in BH, BA, BL, BRd.
    pose proof (BH HH) as HH0. pose proof (BA HA) as HA0. pose proof (BL Hls) as Hls0.
    pose proof (BRd A1 (length fdata) fdata ltac:(lia) ltac:(unfold LEN in HLEN; lia) HC) as HC0.
    assert (HPAY0 : rdn RSEGS M0 (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as (U1 & U2 & U4). subst PTR.
        apply (BRd OWN (length payload) payload ltac:(lia) ltac:(rewrite PLN; lia) HPAY). }
    pose proof (BRd 0xea7b0%Z (length (zero_lines j)) (zero_lines j) ltac:(lia) ltac:(rewrite length_zero_lines; lia) HBUF) as HBUF0.
    clear BH BA BL BRd EQM HH HA Hls HC HPAY HBUF. rename HH0 into HH. rename HA0 into HA. rename Hls0 into Hls. rename HC0 into HC.
    rename HPAY0 into HPAY. rename HBUF0 into HBUF. clear M. rename M0 into M.
    (* [comment removed for export] *)
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
    eapply (lib_site scfg L HI HIok sp0 Hsp' Hal' DL Lay LSt DLL LIok vals _ srLB knLc2 Rc M (model2 VM) LB cr g (-208)
              [(48%nat, 65536%Z)] [] PTR 0x34618 payload K);
      [ exact HR | exact HK
      | rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia
      | exact P0 | exact HIV | vm_compute; reflexivity
      | regv HR (2 : reg); cbn [edenot ev ENVb ENV]; rewrite P0; apply alu_add_w_lit
      | lia | reflexivity
      | regv HR (1 : reg); reflexivity | lia | reflexivity
      | regv HR (3 : reg); reflexivity | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); cbn [edenot ev ENVb ENV]; exact P82
      | regv HR (11 : reg); cbn [edenot ev ENVb ENV]; rewrite P79, PLN; f_equal; lia
      | rewrite PLN; lia
      | destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)];
        [ left; split; [rewrite PLN; lia | exact HPTR] | right; split; [rewrite PLN; lia|]; subst LB PTR; left; rewrite PLN; f_equal; lia ]
      | exact HPAY
      | rewrite PLN; replace (Z.of_nat (Z.to_nat PL)) with PL by lia; exact (credit_le_head sp0 Hsp' k (ll_credit Lay PL) cr Hk1 CP1 CP2 Hcr)
      | exact Hls
      | exact HH | reflexivity | reflexivity | reflexivity
      | intros i nb Hf; cbn in Hf;
        destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL; lia|];
                                         rewrite P48, u_small by lia; exists CAP; split; [lia|]; split; [| exact HBR];
                                         destruct REST as [(_ & _ & _ & ->) | (_ & _ & _ & _ & ->)]; [left | right; left]; reflexivity
                                       | discriminate]
      | intros v b Hf; discriminate
      | exact HK0 | ]
    end.
    clear HR HK.
    intros fx2 R' M' model' g' cr' vals' E' HL' HR HK HH' HBUT Hls' Hcr' HAB HBLK' HIMG. subst vals' E'.
    rewrite (m2_but' _ _ HBUT). rewrite (m2_but' _ _ HBUT) in HH'. cbn [m_vmmaps Bs0DrvB_u.model2 mkModelE with_net with_creds mkModel m_vm vmst_maps] in HH'.
    set (VM2 := m_vmmaps model') in *. clearbody VM2.
    rewrite HL in HR, HL'. change (keep_lib (-208) [(48%nat, 65536%Z)] [] knLc2) with knLr2 in HK.
    set (vals2 := vals ++ junk_vals R') in *.
    change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals2) in HR, HK.
    assert (XL : forall q x, (q < 102)%nat -> vals_ev vals q = x -> vals_ev vals2 q = x).
    { intros q x Hq Hx. subst vals2. rewrite vals_ev_app_l by (rewrite HL; exact Hq). exact Hx. }
    pose proof (XL 0%nat _ ltac:(lia) P0) as X0. pose proof (XL 3%nat _ ltac:(lia) P3) as X3. pose proof (XL 4%nat _ ltac:(lia) P4) as X4.
    pose proof (XL 48%nat _ ltac:(lia) P48) as X48. pose proof (XL 101%nat _ ltac:(lia) P101) as X101.
    pose proof (hiv_facts' vals2 X3 X4) as HIV2.
    (* [comment removed for export] *)
    assert (HA2 : above M') by (intros a Ha; rewrite HAB by exact Ha; apply HA; exact Ha).
    assert (HC2 : rdn RSEGS M' (Z_to_bv 64 A1) (length fdata) = Some fdata).
    { rewrite <- HC. apply rdn_agree. intros q Hq. rewrite u_small by lia. apply HBLK'; [lia|].
      exists (A1, CAP). split; [destruct REST as [(_ & _ & _ & ->)|(_ & _ & _ & _ & ->)]; [left|right; left]; reflexivity|]. cbn [fst snd]. lia. }
    assert (HPAY2 : rdn RSEGS M' (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - rewrite PLN. replace (Z.to_nat PL) with 0%nat by lia. rewrite PLN in HPAY. replace (Z.to_nat PL) with 0%nat in HPAY by lia. exact HPAY.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as (U1 & U2 & U4).
        rewrite <- HPAY. apply rdn_agree. intros q Hq. rewrite PLN in Hq. rewrite u_small by lia. apply HBLK'; [lia|].
        exists (OWN, PL). subst LB PTR. split; [left; reflexivity|]. cbn [fst snd]. lia. }
    assert (HBUF2 : rdn RSEGS M' (Z_to_bv 64 0xea7b0) (length (zero_lines j)) = Some (zero_lines j)).
    { rewrite <- HBUF. apply rdn_agree. intros q Hq. rewrite length_zero_lines in Hq. rewrite u_small by lia. apply HIMG; lia. }
    clear HA HC HPAY HBUF HAB HBLK' HIMG Hls HH.
    (* [comment removed for export] *)
    run_blockT_keep scr0 134%nat.
    lazymatch type of EQM with _ = mem_denot _ _ ?lg =>
      destruct (block_fl vals2 M' lg LB cr' VM2 g' X0 ltac:(vm_compute; reflexivity)) as (BH & BA & BL & BRd) end.
    rewrite <- EQM in BH, BA, BL, BRd.
    pose proof (BH HH') as HH'c. pose proof (BA HA2) as HA2c. pose proof (BL Hls') as Hls'c.
    pose proof (BRd A1 (length fdata) fdata ltac:(lia) ltac:(unfold LEN in HLEN; lia) HC2) as HC2c.
    assert (HPAY2c : rdn RSEGS M0 (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as (U1 & U2 & U4). subst PTR.
        apply (BRd OWN (length payload) payload ltac:(lia) ltac:(rewrite PLN; lia) HPAY2). }
    pose proof (BRd 0xea7b0%Z (length (zero_lines j)) (zero_lines j) ltac:(lia) ltac:(rewrite length_zero_lines; lia) HBUF2) as HBUF2c.
    clear BH BA BL BRd EQM HH' HA2 Hls' HC2 HPAY2 HBUF2.
    rename HH'c into HH'. rename HA2c into HA2. rename Hls'c into Hls'. rename HC2c into HC2. rename HPAY2c into HPAY2. rename HBUF2c into HBUF2.
    clear M'. rename M0 into M'.
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ => rename Rc into RP end.
    (* [comment removed for export] *)
    assert (PH : pfH M' (Z_to_bv 64 (bv_unsigned sp0 - 208)) (WP j) CANZ).
    { destruct (has_window_nth knLp2 ltac:(vm_compute; reflexivity)) as [iw Hnw].
      constructor; rewrite ?u_small by lia.
      - rewrite <- Zminus_mod_idemp_l, Hal'. reflexivity.
      - lia.
      - lia.
      - intros a n H1 H2. rewrite u_small in H1, H2 by lia.
        pose proof (kwr_store_ok RSEGS (ENVb vals2) M' knLp2 iw (EVar 0) (-8388608) 8388608 (bv_unsigned a - bv_unsigned sp0) n HK Hnw
                      ltac:(unfold PF_FR in H1; lia) ltac:(lia)) as W.
        unfold adenot in W. cbn [a_base a_off edenot ev ENVb ENV] in W. rewrite X0 in W. unfold v_addi in W.
        replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in W by lia. rewrite Z_to_bv_bv_unsigned in W. exact W.
      - intros i Hi.
        pose proof (know_nth RSEGS _ _ knLp2 ltac:(let q := kidx knLp2 (is_kimg_cov 0x10000 0xa17f0) in exact q) _ HK eq_refl) as KI.
        cbn [kentry_ok] in KI. destruct KI as (_ & _ & KI). apply KI. lia.
      - krd_solve HK.
      - krd_solve HK.
      - krd HK 0xb8418%Z 8%nat Hw. rewrite Hw. cbn [ev ENVb ENV]. rewrite X101. reflexivity.
      - unfold WP. lia.
      - krd_solve HK.
      - krd_solve HK.
      - krd_solve HK.
      - eapply can_of_know; [exact HK | vm_compute; reflexivity].
      - apply CANZ_range. }
    destruct (printf0_buffered RP M' (seg_rom RSEGS) (Z_to_bv 64 (bv_unsigned sp0 - 208)) (WP j) CANZ PH
                ltac:(regv HR (1 : reg); reflexivity)
                ltac:(regv HR (2 : reg); cbn [edenot ev ENVb ENV]; rewrite X0; apply alu_add_w_lit)
                ltac:(regv HR (11 : reg); reflexivity)) as (R2 & M2 & MS & KCS & FM & Rw & Rwpos & Rflags).
    rewrite u_small in FM by lia.
    eapply srz_msteps; [reflexivity | reflexivity | exact MS |]. clear MS.
    change (frame_mod M' M2 (pf_rs (WP j))) in FM.
    assert (HwB : (0xea7b0 <= WP j <= 0xeabae)%Z) by (unfold WP; lia).
    (* [comment removed for export] *)
    pose proof (regs_after_keeps vals2 _ srP0 RP R2 callee_saved ltac:(rewrite HL'; vm_compute; reflexivity) HR KCS ltac:(cbn; intuition discriminate)) as HR3.
    rewrite HL' in HR3.
    set (vals3 := vals2 ++ junk_vals R2) in *.
    assert (HL3 : length vals3 = 166%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL'; reflexivity).
    assert (YL : forall q x, (q < 102)%nat -> vals_ev vals q = x -> vals_ev vals3 q = x).
    { intros q x Hq Hx. subst vals3. rewrite vals_ev_app_l by (rewrite HL'; lia). apply XL; assumption. }
    pose proof (know_pf vals2 M' M2 knLH2 (WP j) A1 X0 X48 ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | lia]) HwB HIV2 ltac:(eapply ksubl_sound; [exact HK | vm_compute; reflexivity]) ltac:(vm_compute; reflexivity) FM) as HK3.
    lazymatch type of HK3 with know_ok _ _ _ ?k => let k' := eval vm_compute in k in change k with k' in HK3 end.
    lazymatch type of HK3 with know_ok _ _ _ ?k3 =>
      pose proof (env_app_know RSEGS vals2 (junk_vals R2) _ M2 k3 ltac:(rewrite HL'; vm_compute; reflexivity) HK3) as HK4 end.
    fold vals3 in HK4. change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals3) in HR3, HK4.
    set (valsS := relay vals3 R2 (Z_to_bv 64 (WP (S j)))).
    apply (HSS fx2 valsS R2 M2 VM2 A1 PTR OWN LB cr' g').
    - unfold lh_vals, Bs0DrvD_u.lh_vals. subst valsS. rewrite (relay_len vals3 R2 _ ltac:(lia)), relay_81 by lia.
      rewrite !(relay_lo vals3 R2 _) by lia.
      repeat split; try (apply YL; [lia | assumption]).
      + unfold relay. change 82%nat with (81 + 1)%nat. rewrite vals_hi by lia. cbn [nth lay_ext].
        rewrite (KCS (9%bv : reg)) by (cbn; tauto). regv HR (9 : reg). cbn [edenot ev ENVb ENV]. apply XL; [lia | exact P82].
      + unfold relay. change 83%nat with (81 + 2)%nat. rewrite vals_hi by lia. cbn [nth lay_ext].
        rewrite (KCS (18%bv : reg)) by (cbn; tauto). regv HR (18 : reg). cbn [edenot ev ENVb ENV]. apply XL; [lia | exact P83].
    - subst valsS. unfold relay. change 84%nat with (81 + 3)%nat. rewrite vals_hi by lia. cbn [nth lay_ext].
      rewrite (KCS (19%bv : reg)) by (cbn; tauto). regv HR (19 : reg). reflexivity.
    - subst valsS. apply relay_101. lia.
    - lia.
    - lia.
    - subst valsS. eapply (relay_regs vals3 _ R2 _ ltac:(lia)); [| exact HR3]. vm_compute. reflexivity.
    - (* [comment removed for export] *)
      subst valsS. unfold knLH2.
      constructor; [|constructor; [|constructor]].
      + cbn [kentry_ok]. split; [lia|]. split; [apply flat_abs0; lia|]. rewrite SymDriveX.adenot_lit0. cbn [edenot ev ENVb ENV].
        rewrite relay_101 by lia. replace (WP (S j)) with (WP j + 2)%Z by (unfold WP; lia). exact Rwpos.
      + cbn [kentry_ok edenot ev ENVb ENV]. rewrite relay_101 by lia. unfold WP. rewrite u_small by lia. lia.
      + cbn [kentry_ok]. split; [lia|]. split; [apply flat_abs0; lia|]. rewrite SymDriveX.adenot_lit0. cbn [edenot]. exact Rflags.
      + eapply (know_ok_agree RSEGS 82); [apply relay_agree; lia | vm_compute; reflexivity |].
        eapply ksubl_sound; [exact HK4 | vm_compute; reflexivity].
    - eapply above_pf; [exact HA2 | exact FM | exact HwB].
    - split; [exact HBR | exact REST].
    - eapply (rdn_pf M' M2 (WP j)); [exact FM | exact HwB | intros i Hi; unfold CPpf, WP; lia | lia | lia | exact HC2].
    - destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      + assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia).
        rewrite Hp0. reflexivity.
      + pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as (U1 & U2 & U4). subst PTR.
        eapply (rdn_pf M' M2 (WP j)); [exact FM | exact HwB | intros i Hi; rewrite PLN in Hi; unfold CPpf, WP; lia | lia | rewrite PLN; lia | exact HPAY2].
    - rewrite zero_lines_snoc, length_app. cbn [length]. apply rdn_app.
      + eapply (rdn_pf M' M2 (WP j)); [exact FM | exact HwB | intros i Hi; rewrite length_zero_lines in Hi; unfold CPpf, WP; lia | lia
                                       | rewrite length_zero_lines; lia | exact HBUF2].
      + rewrite length_zero_lines. replace (Z_to_bv 64 0xea7b0 + nat_to_word (2 * j)) with (Z_to_bv 64 (WP j)); [exact Rw|].
        apply bv_eq. rewrite w_add_nat. rewrite (u_small 0xea7b0) by lia. rewrite !u_small by (unfold WP; lia). unfold WP. lia.
    - eapply heap_pf; [exact HH' | exact FM | exact HwB].
    - rewrite PLN in Hcr'. replace (Z.of_nat (Z.to_nat PL)) with PL in Hcr' by lia.
      exact (credit_le_step sp0 Hsp' k (ll_credit Lay PL) cr cr' Hk1 CP1 CP2 Hcr Hcr').
    - eapply ls_pf; [exact Hls' | exact FM | exact HwB].
  Qed.

End DrvE.
End FPX_1.
