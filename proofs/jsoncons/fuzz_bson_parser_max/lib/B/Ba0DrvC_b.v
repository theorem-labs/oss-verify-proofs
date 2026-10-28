(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  LibTail RefReadLib RefPrintfLib RefNodes HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvA_b
  Ba0DrvG_defs_b Ba0DrvG_b Ba0DrvC_defs_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma w2le1_byteA : forall (x : byte), word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned x)) = [x].
Proof.
  intros x. pose proof (bv_unsigned_in_range _ x) as Hx. change (bv_modulus 8) with 256 in Hx.
  unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal.
  rewrite u_small by lia. apply Z_to_bv_bv_unsigned.
Qed.
Lemma content_byteA : forall M (A : Z) (data : list byte) j,
  rdn ASEGS M (Z_to_bv 64 A) (length data) = Some data -> (j < length data)%nat ->
  0 <= A -> A + Z.of_nat (length data) < 2 ^ 64 ->
  rdn ASEGS M (Z_to_bv 64 (A + Z.of_nat j)) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned (nth j data (Z_to_bv 8 0))))).
Proof.
  intros M A data j Hc Hj HA HA2.
  pose proof (SeqExec.rdn_nth ASEGS M (length data) _ data j Hc Hj) as H.
  rewrite w_add_nat in H. rewrite u_small in H by lia. rewrite w2le1_byteA. exact H.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvC.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Variable fs0 : Fs.Fs.
  Variable fdata : list byte.
  Variables p0 p1 can : word.
  Variable M0 : word -> option byte.
  Variable LK0 : list fframe.
  Variable A0 : list (Z * Z).
  Variable CAP : Z.
  Hypothesis HCAP : 65536 <= CAP <= 67108864.
  Variable crC : credit.
  Hypothesis HLEN : Z.of_nat (length fdata) < CAP.

  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation ENVG := (ENVA fdata).
  Let LEN : Z := Z.of_nat (length fdata).

  (* [comment removed for export] *)
  Definition B0A : Z := bv_unsigned (nth 0 fdata (Z_to_bv 8 0)).
  Definition B1A : Z := bv_unsigned (nth 1 fdata (Z_to_bv 8 0)).
  Definition B2A : Z := bv_unsigned (nth 2 fdata (Z_to_bv 8 0)).
  Definition CFGA : Z := (B0A + 256 * B1A) mod 32768.
  Definition PLA : Z := LEN - 6 - CFGA.
  Lemma B0A_range : 0 <= B0A < 256.
  Proof. clear HLEN. unfold B0A. pose proof (bv_unsigned_in_range _ (nth 0 fdata (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256 in H. lia. Qed.
  Lemma B1A_range : 0 <= B1A < 256.
  Proof. clear HLEN. unfold B1A. pose proof (bv_unsigned_in_range _ (nth 1 fdata (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256 in H. lia. Qed.
  Lemma B2A_range : 0 <= B2A < 256.
  Proof. clear HLEN. unfold B2A. pose proof (bv_unsigned_in_range _ (nth 2 fdata (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256 in H. lia. Qed.
  Lemma CFGA_range : 0 <= CFGA < 32768.
  Proof. clear HLEN. unfold CFGA. apply Z.mod_pos_bound. lia. Qed.

  (* [comment removed for export] *)
  Definition target_kA (KT : TSet) : Prop :=
    forall vals R M (model : Model) A (A1 : Z),
      length vals = 81%nat -> hdr_valsA sp0 p0 p1 can vals -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 LEN ->
      vals_ev vals 71 = Z_to_bv 64 B0A -> vals_ev vals 72 = Z_to_bv 64 B1A -> vals_ev vals 73 = Z_to_bv 64 CFGA ->
      vals_ev vals 79 = Z_to_bv 64 PLA -> vals_ev vals 80 = Z_to_bv 64 B2A ->
      regs_ok (ENVG vals) srT0A R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knT0A ->
      rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
      dinvA [(A1, CAP)] LK0 crC A M model -> incl A0 A ->
      m_fds model = fds0 -> m_fs model = fs0 ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xa7dd4) M (seg_rom ASEGS)) model) KT.

  (* [comment removed for export] *)
  Lemma ltu_hdr_scA : forall vals M t,
    vals_ev vals 70 = Z_to_bv 64 LEN -> vals_ev vals 71 = Z_to_bv 64 B0A -> vals_ev vals 72 = Z_to_bv 64 B1A ->
    Z.ltb LEN (CFGA + 6) = t ->
    sc_denot ASEGS M (ENVG vals) (SCBr t BC_LTU (EVar 70) (EAlu ALU_ADD cfglen_xA (ELit 6))).
  Proof.
    intros vals M t P70 P71 P72 Ht. pose proof B0A_range as R0. pose proof B1A_range as R1. pose proof CFGA_range as RC.
    cbn [sc_denot branch_taken].
    change (edenot (ENVG vals) (EAlu ALU_ADD cfglen_xA (ELit 6))) with (alu64 ALU_ADD (edenot (ENVG vals) cfglen_xA) (Z_to_bv 64 6)).
    change (edenot (ENVG vals) (EVar 70)) with (vals_ev vals 70).
    unfold ENVA. rewrite cfglen_x_cfgFA, P70, P71, P72, cfgF_valA by lia. fold CFGA.
    rewrite alu_add_Z. unfold bv_ltu. rewrite !u_small by (unfold LEN in *; lia). exact Ht.
  Qed.

  (* [comment removed for export] *)
  Lemma content_visA : forall LK cr A M model (u n : Z) (m : nat) bs,
    dinvA [(u, n)] LK cr A M model -> Z.of_nat m <= n ->
    rdn ASEGS M (Z_to_bv 64 u) m = Some bs -> rdn ASEGS (mrestrict (ahid A model) M) (Z_to_bv 64 u) m = Some bs.
  Proof.
    intros LK cr A M model u n m bs D Hm HC. pose proof Hsp as Hsp'.
    destruct (inv_block1 scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ _ D (or_introl eq_refl)) as (_ & _ & (Z1 & Z2 & Z3)).
    rewrite <- HC. apply rdn_agree. intros j Hj. rewrite u_small by lia. unfold mrestrict.
    rewrite (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (u + Z.of_nat j) (di_inv _ _ _ _ _ _ _ _ _ _ D) ltac:(lia)); [reflexivity|].
    right. right. exists (u, n). split; [left; reflexivity | cbn [fst snd]; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma kbyte48A : forall vals MV (A1 : Z) (k : Z) (v : nat),
    vals_ev vals 48 = Z_to_bv 64 A1 -> hzA sp0 A1 CAP ->
    rdn ASEGS MV (Z_to_bv 64 A1) (length fdata) = Some fdata ->
    0 <= k -> (Z.to_nat k < length fdata)%nat ->
    vals_ev vals v = Z_to_bv 64 (bv_unsigned (nth (Z.to_nat k) fdata (Z_to_bv 8 0))) ->
    kentry_ok ASEGS (ENVG vals) MV (KWord (SA (EVar 48) k) 1 (EVar v)).
  Proof.
    intros vals MV A1 k v P48 (Z1 & Z2 & Z3) HC Hk Hkl Pv. pose proof Hsp as Hsp'.
    cbn [kentry_ok]. split; [lia|]. split.
    - apply flat_intro; cbn [edenot ev ENVA]; rewrite ?P48, ?u_small by lia; lia.
    - unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVA]. rewrite P48, Pv, u_small by lia.
      replace (A1 + k) with (A1 + Z.of_nat (Z.to_nat k)) by lia. apply content_byteA; [exact HC | exact Hkl | lia | lia].
  Qed.
  Lemma krange_litA : forall vals MV (v : nat) (x lo hi : Z),
    vals_ev vals v = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> lo <= x <= hi ->
    kentry_ok ASEGS (ENVG vals) MV (KRange (EVar v) lo hi).
  Proof. intros vals MV v x lo hi Pv Hx Hr. cbn [kentry_ok edenot ev ENVA]. rewrite Pv, u_small by lia. lia. Qed.

  Lemma know_GLA : forall vals MV (A1 : Z),
    length vals = 73%nat -> vals_ev vals 48 = Z_to_bv 64 A1 -> hzA sp0 A1 CAP ->
    rdn ASEGS MV (Z_to_bv 64 A1) (length fdata) = Some fdata -> (6 <= length fdata)%nat ->
    vals_ev vals 71 = Z_to_bv 64 B0A -> vals_ev vals 72 = Z_to_bv 64 B1A ->
    know_ok ASEGS (ENVG vals) MV (knGA 6 67108863) ->
    know_ok ASEGS (ENVG vals) MV knGLA.
  Proof.
    intros vals MV A1 HL P48 HZ HC H6 P71 P72 HK. pose proof B0A_range as R0. pose proof B1A_range as R1.
    unfold knGLA, kn_hdrA. apply Forall_app. split; [|exact HK].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    - eapply kbyte48A; [exact P48 | exact HZ | exact HC | lia | cbn; lia | exact P71].
    - eapply kbyte48A; [exact P48 | exact HZ | exact HC | lia | cbn; lia | exact P72].
    - eapply krange_litA; [exact P71 | lia | lia].
    - eapply krange_litA; [exact P72 | lia | lia].
  Qed.

  Ltac drv_blockH0 HIok Hsp DL HR HK DI P0 scr NX :=
    let HZ := fresh "HZ" in
    pose proof (dinv_lzinv _ _ _ _ _ _ HIok _ DL _ _ _ _ _ _ _ DI) as HZ;
    run_block_lz_with HR HK HZ asegs_wx FUELA STOPS_HA scr NX true;
    [ .. | drv_block_post0 HIok Hsp DL DI P0 HZ ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem hdr_okA : 6 + CFGA <= LEN -> forall KT, target_kA KT -> KT [] ->
    close_kgA scfg ar HI sp0 fs0 fdata p0 p1 can M0 LK0 A0 CAP crC KT.
  Proof.
    intros Hok KT HKT HKT0. unfold close_kgA.
    intros vals R M model A A1 HL HV P48 P70 HR HK HC DI HINC G1 G2.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    destruct (inv_block1 scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ _ DI (or_introl eq_refl)) as (HBR & HDEF & HZ). pose proof HZ as (Z1 & Z2 & Z3).
    pose proof HV as (P0 & P1 & P2 & P3).
    pose proof B0A_range as HB0r. pose proof B1A_range as HB1r. pose proof B2A_range as HB2r. pose proof CFGA_range as HCr.
    assert (ELEN : LEN = Z.of_nat (length fdata)) by reflexivity.
    assert (Hge : (6 <= length fdata)%nat) by lia.
    specialize (HK 6 67108863 ltac:(lia)).
    (* [comment removed for export] *)
    set (vals1 := vals ++ [Z_to_bv 64 B0A; Z_to_bv 64 B1A]).
    assert (HL1 : length vals1 = 73%nat) by (subst vals1; rewrite length_app, HL; reflexivity).
    assert (YV : hdr_valsA sp0 p0 p1 can vals1) by (subst vals1; unfold hdr_valsA in *; rewrite !vals_ev_app_l by (rewrite HL; lia); exact HV).
    pose proof YV as (Y0 & _).
    assert (Y48 : vals_ev vals1 48 = Z_to_bv 64 A1) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
    assert (Y70 : vals_ev vals1 70 = Z_to_bv 64 LEN) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    assert (Y71 : vals_ev vals1 71 = Z_to_bv 64 B0A).
    { subst vals1. rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
    assert (Y72 : vals_ev vals1 72 = Z_to_bv 64 B1A).
    { subst vals1. replace 72%nat with (length vals + 1)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    pose proof (env_app_regs vals [Z_to_bv 64 B0A; Z_to_bv 64 B1A] _ srGLA R ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know ASEGS vals [Z_to_bv 64 B0A; Z_to_bv 64 B1A] _ _ (knGA 6 67108863) ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK0.
    fold vals1 in HR1, HK0. change (Env (vals_ev vals1) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals1) in HR1, HK0.
    pose proof (content_visA _ _ _ _ _ _ _ (length fdata) fdata DI ltac:(lia) HC) as HCV.
    pose proof (know_GLA vals1 _ A1 HL1 Y48 HZ HCV Hge Y71 Y72 HK0) as HK1.
    clear HR HK HK0 HCV.
    (* [comment removed for export] *)
    drv_blockH0 HIok Hsp DL HR1 HK1 DI Y0 scr_fallA 73%nat.
    { apply (ltu_hdr_scA vals1 _ false Y70 Y71 Y72). apply Z.ltb_ge. lia. }
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
    assert (HC1 : rdn ASEGS M1 (Z_to_bv 64 A1) (length fdata) = Some fdata).
    { rewrite <- HC. apply rdn_agree. intros j Hj. apply EQA. }
    clear EQM EQH EQA SBM HR1 HK1 DI HC G1 G2 HDEF. clear M model R.
    (* [comment removed for export] *)
    set (ext := [Z_to_bv 64 CFGA; sx8FA (Z_to_bv 64 B1A);
                 Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (2 + CFGA)) fdata (Z_to_bv 8 0)));
                 Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (3 + CFGA)) fdata (Z_to_bv 8 0)));
                 Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (4 + CFGA)) fdata (Z_to_bv 8 0)));
                 Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (5 + CFGA)) fdata (Z_to_bv 8 0)))]).
    set (vals2 := vals1 ++ ext).
    assert (HL2 : length vals2 = 79%nat) by (subst vals2 ext; rewrite length_app, HL1; reflexivity).
    assert (WV : hdr_valsA sp0 p0 p1 can vals2) by (subst vals2; unfold hdr_valsA in *; rewrite !vals_ev_app_l by (rewrite HL1; lia); exact YV).
    pose proof WV as (W0 & _).
    assert (W48 : vals_ev vals2 48 = Z_to_bv 64 A1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y48).
    assert (W70 : vals_ev vals2 70 = Z_to_bv 64 LEN) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y70).
    assert (W71 : vals_ev vals2 71 = Z_to_bv 64 B0A) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y71).
    assert (W72 : vals_ev vals2 72 = Z_to_bv 64 B1A) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y72).
    assert (WX : forall i, (i < 6)%nat -> vals_ev vals2 (73 + i) = nth i ext (Z_to_bv 64 0)).
    { intros i Hi. subst vals2. replace (73 + i)%nat with (length vals1 + i)%nat by (rewrite HL1; reflexivity).
      rewrite vals_ev_app_r. reflexivity. }
    pose proof (WX 0%nat ltac:(lia)) as W73. pose proof (WX 1%nat ltac:(lia)) as W74.
    pose proof (WX 2%nat ltac:(lia)) as W75. pose proof (WX 3%nat ltac:(lia)) as W76.
    pose proof (WX 4%nat ltac:(lia)) as W77. pose proof (WX 5%nat ltac:(lia)) as W78.
    cbn [nth ext Nat.add] in W73, W74, W75, W76, W77, W78. clear WX.
    (* [comment removed for export] *)
    pose proof (env_app_regs vals1 ext _ srHa _ ltac:(rewrite HL1; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know ASEGS vals1 ext _ _ knGLA ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK0.
    fold vals2 in HR1, HK0. change (Env (vals_ev vals2) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals2) in HR1, HK0.
    assert (Ecfg : edenot (ENVG vals2) cfglen_xA = edenot (ENVG vals2) (EVar 73)).
    { unfold ENVA. rewrite cfglen_x_cfgFA, W71, W72, cfgF_valA by lia. fold CFGA. symmetry. exact W73. }
    assert (Esx8 : edenot (ENVG vals2) sx8_xA = edenot (ENVG vals2) (EVar 74)).
    { unfold ENVA. rewrite sx8_x_sx8FA, W72. symmetry. exact W74. }
    pose proof (regs_ok_esub _ _ _ _ _ Esx8 (regs_ok_esub _ _ _ _ _ Ecfg HR1)) as HR2.
    lazymatch type of HR2 with regs_ok ?Ex ?srx ?Rx => assert (HRb : regs_ok Ex srHb0 Rx) by (exact HR2) end.
    clear HR HR1 HR2.
    (* [comment removed for export] *)
    pose proof (content_visA _ _ _ _ _ _ _ (length fdata) fdata DI0 ltac:(lia) HC1) as HCV.
    assert (HKb : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A model0) M1) knHb0).
    { rewrite knHb0_eq. unfold kn_bmA. apply Forall_app. split; [|exact HK0].
      assert (PXv : edenot (ENVG vals2) PXA = Z_to_bv 64 (A1 + CFGA)).
      { cbn [edenot ev ENVA PXA]. rewrite W48, W73. apply alu_add_Z. }
      assert (KB : forall (j : Z) (v : nat), 2 <= j <= 5 ->
                vals_ev vals2 v = Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (j + CFGA)) fdata (Z_to_bv 8 0))) ->
                kentry_ok ASEGS (ENVG vals2) (mrestrict (ahid A model0) M1) (KWord (SA PXA j) 1 (EVar v))).
      { intros j v Hj Pv. cbn [kentry_ok]. split; [lia|]. split.
        - unfold flat, estart. cbn [a_base a_off]. rewrite PXv, u_small by lia. lia.
        - unfold adenot, v_addi. cbn [a_base a_off]. rewrite PXv, u_small by lia.
          change (edenot (ENVG vals2) (EVar v)) with (vals_ev vals2 v). rewrite Pv.
          replace (A1 + CFGA + j) with (A1 + Z.of_nat (Z.to_nat (j + CFGA))) by lia.
          apply content_byteA; [exact HCV | lia | lia | lia]. }
      constructor; [eapply krange_litA; [exact W73 | lia | lia]|].
      constructor; [apply (KB 2); [lia | exact W75]|].
      constructor; [apply (KB 3); [lia | exact W76]|].
      constructor; [apply (KB 4); [lia | exact W77]|].
      constructor; [apply (KB 5); [lia | exact W78]|].
      assert (BR : forall (v : nat) k, vals_ev vals2 v = Z_to_bv 64 (bv_unsigned (nth k fdata (Z_to_bv 8 0))) ->
                 kentry_ok ASEGS (ENVG vals2) (mrestrict (ahid A model0) M1) (KRange (EVar v) 0 255)).
      { intros v k Pv. pose proof (bv_unsigned_in_range _ (nth k fdata (Z_to_bv 8 0))) as Hb. change (bv_modulus 8) with 256 in Hb.
        eapply krange_litA; [exact Pv | lia | lia]. }
      constructor; [exact (BR _ _ W75)|]. constructor; [exact (BR _ _ W76)|].
      constructor; [exact (BR _ _ W77)|]. constructor; [exact (BR _ _ W78)|]. constructor. }
    clear HK HK0.
    (* [comment removed for export] *)
    drv_blockH0 HIok Hsp DL HRb HKb DI0 W0 scr0 79%nat.
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
    assert (HC2 : rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata).
    { rewrite <- HC1. apply rdn_agree. intros j Hj. apply EQA. }
    pose proof (content_visA _ _ _ _ _ _ _ (length fdata) fdata DI ltac:(lia) HC2) as HCV2.
    clear EQM EQH EQA SBM HRb HKb DI0 HC1 HCV F1 F2. clear M1 model0 R0.
    (* [comment removed for export] *)
    set (ext2 := [Z_to_bv 64 PLA; Z_to_bv 64 B2A]).
    set (vals3 := vals2 ++ ext2).
    assert (HL3 : length vals3 = 81%nat) by (subst vals3 ext2; rewrite length_app, HL2; reflexivity).
    assert (V79 : vals_ev vals3 79 = Z_to_bv 64 PLA).
    { subst vals3. rewrite <- HL2, <- (Nat.add_0_r (length vals2)). rewrite vals_ev_app_r. reflexivity. }
    assert (V80 : vals_ev vals3 80 = Z_to_bv 64 B2A).
    { subst vals3. replace 80%nat with (length vals2 + 1)%nat by (rewrite HL2; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    pose proof (env_app_regs vals2 ext2 _ srHb _ ltac:(rewrite HL2; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know ASEGS vals2 ext2 _ _ knHb0 ltac:(rewrite HL2; vm_compute; reflexivity) HK) as HK0.
    fold vals3 in HR1, HK0. change (Env (vals_ev vals3) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals3) in HR1, HK0.
    assert (TV : hdr_valsA sp0 p0 p1 can vals3) by (subst vals3; unfold hdr_valsA in *; rewrite !vals_ev_app_l by (rewrite HL2; lia); exact WV).
    assert (T70 : vals_ev vals3 70 = Z_to_bv 64 LEN) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W70).
    assert (T71 : vals_ev vals3 71 = Z_to_bv 64 B0A) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W71).
    assert (T72 : vals_ev vals3 72 = Z_to_bv 64 B1A) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W72).
    assert (T73 : vals_ev vals3 73 = Z_to_bv 64 CFGA) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W73).
    assert (T48 : vals_ev vals3 48 = Z_to_bv 64 A1) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W48).
    assert (Epl : edenot (ENVG vals3) plen_xA = edenot (ENVG vals3) (EVar 79)).
    { unfold ENVA. rewrite (plen_valA LEN CFGA vals3 _ ltac:(lia) ltac:(unfold LEN in *; lia) T70 T73). symmetry. exact V79. }
    pose proof (regs_ok_esub _ _ _ _ _ Epl HR1) as HR2.
    lazymatch type of HR2 with regs_ok ?Ex ?srx ?Rx => assert (HRt : regs_ok Ex srT0A Rx) by (exact HR2) end.
    clear HR HR1 HR2.
    assert (HKt : know_ok ASEGS (ENVG vals3) (mrestrict (ahid A model) M) knT0A).
    { eapply ksubl_sound; [|exact knT0A_sub]. apply Forall_app. split; [|exact HK0]. unfold kn_tgtA.
      constructor; [eapply krange_litA; [exact T73 | lia | lia]|].
      constructor; [eapply krange_litA; [exact V79 | unfold PLA, LEN in *; lia | unfold PLA, LEN in *; lia]|].
      constructor; [eapply kbyte48A; [exact T48 | exact HZ | exact HCV2 | lia | cbn; lia | exact V80]|].
      constructor; [eapply krange_litA; [exact V80 | lia | lia]|]. constructor. }
    clear HK HK0.
    apply (HKT vals3 R M model A A1 HL3 TV T48 T70 T71 T72 T73 V79 V80 HRt HKt HC2 DI HINC G1 G2).
  Qed.


End DrvC.
End FPX_1.
