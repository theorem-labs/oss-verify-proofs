(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  RefNodes RefPrintfLib HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm8IcptLayout PmIcptDrvA LibIface PmLibIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Pm8DrvEntry Pm8Drv_defs Pm8DrvLib Pm8DrvRead Pm8DrvA
  Pm8DrvG_defs Pm8DrvG Pm8DrvC_defs Pm8DrvC Pm8DrvD_defs Pm8DrvLibL Pm8DrvD Pm8DrvE_defs Pm8DrvStdio Pm8DrvPrintfK Pm8DrvPrintf1 Pm8DrvExit Pm8DrvLibInit Pm8DrvPfKeep Pm8DrvE.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import ShapeLaws AgentLib Spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvE2.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_ok L ar C scfg HI.
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Variable fs0 : Fs.Fs.
  Variable fdata : list byte.
  Variables p0 p1 can : word.
  Variable M0 : word -> option byte.
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
  Variable A0 : list (Z * Z).
  Variable CAP : Z.
  Hypothesis HCAP : 65536 <= CAP <= 67108864.
  Hypothesis HLEN : Z.of_nat (length fdata) < CAP.
  Variable Lay : lib_layoutA.
  Variable LSt : lib_statics.
  Hypothesis ILY : as0_icpt_layout IL.
  Hypothesis Hpr : incl PR_CELLS (asc_cells C).
  Hypothesis DLL : drv_lib_layoutA Lay L.
  Hypothesis DLC : drv_lib_cellsA Lay.
  Variable LSA : ls_state LSt -> list (Z * Z).
  Hypothesis LIOK : lib_iface_okA Lay ar scfg HI LSt LSA.

  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation ENVG := (ENVA fdata).
  #[local] Notation usp := (bv_unsigned sp0).
  Let LEN : Z := Z.of_nat (length fdata).
  Let CFG : Z := CFGA fdata.
  Let PL : Z := PLA fdata.
  #[local] Notation payloadA := (Pm8DrvD.payloadA fdata).
  #[local] Notation blk_factsA := (Pm8DrvD.blk_factsA L ar fdata CAP).
  #[local] Notation SSPA := (Pm8DrvE.SSPA scfg L ar HI sp0 fs0 fdata p0 p1 can M0 A0 CAP Lay LSt).
  #[local] Notation LH2PA := (Pm8DrvE.LH2PA scfg L ar HI sp0 fs0 fdata p0 p1 can M0 A0 CAP Lay LSt).
  #[local] Notation e_factsA := (Pm8DrvE.e_factsA L ar HI sp0 fs0 fdata M0 A0 CAP Lay LSt).
  #[local] Notation e_valsA := (Pm8DrvE.e_valsA sp0 fdata p0 p1 can).
  #[local] Notation lib_roomA := (Pm8DrvE.lib_roomA fdata Lay).
  #[local] Notation EA := (Pm8DrvE.EA fs0).
  #[local] Notation LV := (lib_view Lay ar).

  Definition CWS (a : Z) : Prop := usp - 8388608 <= a < usp.
  Lemma regions_write_stk : forall vals ebs,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    regions_ok ASEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] [] [] E CWS (fun _ => True).
  Proof.
    intros vals ebs E P0. pose proof Hsp as Hsp'.
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CWS. lia.
    - intros z Hz. right. exact I.
    - intros i nb Hf. discriminate.
    - intros v b Hf. discriminate.
    - intros i [].
    - intros lo hi [].
    - intros lo hi [].
  Qed.
  Lemma block_frame_stk : forall vals ebs A M M' (model : Model) log,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] [] log = true ->
    mrestrict (ahid A model) M' = mem_denot E (mrestrict (ahid A model) M) log ->
    (forall a, ahid A model a = true -> M' a = M a) ->
    forall a, 0 <= a < 2 ^ 64 -> ~ CWS a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Proof.
    intros vals ebs A M M' model log E P0 Hlog EQM EQH a Ha HC.
    pose proof (regions_write_stk vals ebs P0) as RG.
    destruct (ahid A model (Z_to_bv 64 a)) eqn:Hh; [apply EQH; exact Hh|].
    assert (E1 : M' (Z_to_bv 64 a) = mrestrict (ahid A model) M' (Z_to_bv 64 a)) by (unfold mrestrict; rewrite Hh; reflexivity).
    rewrite E1, EQM.
    rewrite (mem_denot_frame_Z ASEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] [] _ CWS (fun _ => True) [] RG _ log a Hlog Ha HC).
    unfold mrestrict. rewrite Hh. reflexivity.
  Qed.

  Definition DW (a : Z) : Prop := usp - 8388608 <= a < usp \/ 1407568 <= a < 1407568 + 232 \/ SOBUF <= a < SOBUF + 1024.

  Definition CWSA (a : Z) : Prop := CWS a \/ 6877204 <= a < 6877204 + 1.
  Definition DWA (a : Z) : Prop := DW a \/ 6877204 <= a < 6877204 + 1.
  Lemma regions_write_stkA : forall vals ebs,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    regions_ok ASEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] [(6877204, 6877204 + 1)] [] E CWSA (fun _ => True).
  Proof.
    intros vals ebs E P0. pose proof Hsp as Hsp'.
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CWSA, CWS. left. lia.
    - intros z Hz. right. exact I.
    - intros i nb Hf. discriminate.
    - intros v b Hf. discriminate.
    - intros i [].
    - intros lo hi Hin. cbn [In] in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <-. split; [lia|]. split; [lia|]. intros a Ha. unfold CWSA. right. lia.
    - intros lo hi [].
  Qed.
  Lemma block_frame_stkA : forall vals ebs A M M' (model : Model) log,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] [(6877204, 6877204 + 1)] log = true ->
    mrestrict (ahid A model) M' = mem_denot E (mrestrict (ahid A model) M) log ->
    (forall a, ahid A model a = true -> M' a = M a) ->
    forall a, 0 <= a < 2 ^ 64 -> ~ CWSA a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Proof.
    intros vals ebs A M M' model log E P0 Hlog EQM EQH a Ha HC.
    pose proof (regions_write_stkA vals ebs P0) as RG.
    destruct (ahid A model (Z_to_bv 64 a)) eqn:Hh; [apply EQH; exact Hh|].
    assert (E1 : M' (Z_to_bv 64 a) = mrestrict (ahid A model) M' (Z_to_bv 64 a)) by (unfold mrestrict; rewrite Hh; reflexivity).
    rewrite E1, EQM.
    rewrite (mem_denot_frame_Z ASEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] [(6877204, 6877204 + 1)] _ CWSA (fun _ => True) [] RG _ log a Hlog Ha HC).
    unfold mrestrict. rewrite Hh. reflexivity.
  Qed.
  Lemma ls_ok_frameWA : forall g (M M' : word -> option byte),
    ls_ok LSt g M -> (forall a, 0 <= a < 2 ^ 64 -> ~ DWA a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> ls_ok LSt g M'.
  Proof.
    intros g M M' HLS FR. pose proof Hsp as Hsp'.
    apply (lioa_frame _ _ _ _ _ _ LIOK g M M' HLS).
    - intros a Ha Hf. apply FR; [exact Ha|]. intros HD.
      destruct (Z_lt_le_dec a 0x67f010) as [Hlo|Hhi].
      + apply (not_foot_off_image L ar sp0 Hsp Lay DLL a); [lia | exact Hf].
      + destruct (Z_lt_le_dec a 0x6b3000) as [Hlo2|Hhi2].
        * apply (not_foot_of_hole L ar sp0 Hsp Lay DLL a); [|exact Hf]. intros hl hh Hh. unfold LIB_HOLES in Hh. cbn [In] in Hh. unfold DWA, DW, SOBUF in HD.
          repeat (destruct Hh as [Hh|Hh]; [injection Hh as <- <-; lia|]). destruct Hh.
        * apply (not_foot_off_image L ar sp0 Hsp Lay DLL a); [lia | exact Hf].
    - intros a Ha Hn. cbn [lib_view ll_rw_lo] in Ha. pose proof (dlc_rw_lo Lay DLC) as RW.
      rewrite <- (Z_to_bv_bv_unsigned 64 a). rewrite <- (Z_to_bv_bv_unsigned 64 a) in Hn. pose proof (u64_range a) as UR.
      rewrite FR; [exact Hn | lia|]. unfold DWA, DW, SOBUF. lia.
    - intros a Ha [(iv & Hin & Hr)|Hab].
      + cbn [lib_view ll_initc] in Hin. destruct (dlc_initc Lay DLC iv Hin) as (I1 & I2 & I3 & I4). pose proof (dlc_initc_aef Lay DLC iv Hin) as I5.
        apply FR; [exact Ha|]. unfold DWA, DW, SOBUF. lia.
      + cbn [lib_view ll_heap heap_view hl_sptop] in Hab. rewrite (dla_sptop L ar IL sp0 DL) in Hab.
        apply FR; [exact Ha|]. unfold DWA, DW, SOBUF. lia.
  Qed.
  Lemma ls_ok_frameW : forall g (M M' : word -> option byte),
    ls_ok LSt g M -> (forall a, 0 <= a < 2 ^ 64 -> ~ DW a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> ls_ok LSt g M'.
  Proof.
    intros g M M' HLS FR. pose proof Hsp as Hsp'.
    apply (lioa_frame _ _ _ _ _ _ LIOK g M M' HLS).
    - intros a Ha Hf. apply FR; [exact Ha|]. intros HD.
      destruct (Z_lt_le_dec a 0x67f010) as [Hlo|Hhi].
      + apply (not_foot_off_image L ar sp0 Hsp Lay DLL a); [lia | exact Hf].
      + destruct (Z_lt_le_dec a 0x6b3000) as [Hlo2|Hhi2].
        * apply (not_foot_of_hole L ar sp0 Hsp Lay DLL a); [|exact Hf]. intros hl hh Hh. unfold LIB_HOLES in Hh. cbn [In] in Hh. unfold DW, SOBUF in HD.
          repeat (destruct Hh as [Hh|Hh]; [injection Hh as <- <-; lia|]). destruct Hh.
        * apply (not_foot_off_image L ar sp0 Hsp Lay DLL a); [lia | exact Hf].
    - intros a Ha Hn. cbn [lib_view ll_rw_lo] in Ha. pose proof (dlc_rw_lo Lay DLC) as RW.
      rewrite <- (Z_to_bv_bv_unsigned 64 a). rewrite <- (Z_to_bv_bv_unsigned 64 a) in Hn. pose proof (u64_range a) as UR.
      rewrite FR; [exact Hn | lia|]. unfold DW, SOBUF. lia.
    - intros a Ha [(iv & Hin & Hr)|Hab].
      + cbn [lib_view ll_initc] in Hin. destruct (dlc_initc Lay DLC iv Hin) as (I1 & I2 & I3 & I4).
        apply FR; [exact Ha|]. unfold DW, SOBUF. lia.
      + cbn [lib_view ll_heap heap_view hl_sptop] in Hab. rewrite (dla_sptop L ar IL sp0 DL) in Hab.
        apply FR; [exact Ha|]. unfold DW, SOBUF. lia.
  Qed.

  Lemma Wpf_in_Wpf1 : forall S j a, 0 <= j <= 510 -> Wpf S j a -> Wpf1 S a.
  Proof. intros S j a Hj. unfold Wpf, Wpf1, SOBUF. lia. Qed.
  Lemma Wpf1_in_DW : forall S a, usp - 4096 <= S <= usp -> Wpf1 S a -> DW a.
  Proof. intros S a HS. unfold Wpf1, DW, SOBUF. lia. Qed.

  Lemma e_vals_app : forall n vals ext A1 PTR OWN k, (102 <= n)%nat -> e_valsA n vals A1 PTR OWN k -> e_valsA (n + length ext) (vals ++ ext) A1 PTR OWN k.
  Proof.
    intros n vals ext A1 PTR OWN k Hn (HL & HV & P48 & P70 & P73 & P79 & P81 & P82 & P83). unfold Pm8DrvE.e_valsA.
    rewrite length_app, HL. rewrite !vals_ev_app_l by lia.
    split; [reflexivity|]. split; [apply (hdr_appA sp0 fdata); [exact HV | lia]|]. tauto.
  Qed.

  Lemma pf_postA : forall (fx' : PropExec.FPState) knX vals R R' M M1 (model model1 : Model) A (A1 PTR OWN k j' : Z) LB LK cr g K,
    kn_vars_lt 134 knX = true -> has_window knX = true -> ksubl_b (keep_pfA PSO [(48%nat, 65536)] knX) knLH2A = true ->
    e_valsA 134 vals A1 PTR OWN k -> 1 <= k -> 0 <= j' -> j' + k <= 4 ->
    regs_ok (ENVG vals) srPA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knX ->
    blk_factsA A1 PTR OWN LB ->
    rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
    rdn ASEGS M (Z_to_bv 64 PTR) (length payloadA) = Some payloadA ->
    incl A0 A -> m_fds model = fds0 -> m_fs model = fs0 -> ls_ok LSt g M -> lib_roomA (k - 1) LK cr ->
    dinvA LB LK cr A M1 model1 -> same_but_materialized model model1 ->
    (forall r, In r c_kept -> getr R' r = getr R r) ->
    stdoutA j' (mrestrict (ahid A model1) M1) -> stdoutXA (mrestrict (ahid A model1) M1) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf1 (usp + PSO) a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf1 (usp + PSO) a -> mrestrict (ahid A model1) M1 (Z_to_bv 64 a) = mrestrict (ahid A model) M (Z_to_bv 64 a)) ->
    (forall a : word, mrestrict (ahid A model) M a <> None -> mrestrict (ahid A model1) M1 a <> None) ->
    SSPA k j' K ->
    PmLibIfaceA.fp_ok fx' ->
    srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xaf178) M1 (seg_rom ASEGS)) model1) K.
  Proof.
    intros fx' knX vals R R' M M1 model model1 A A1 PTR OWN k j' LB LK cr g K KV HW EKN EV Hk Hj Hjk HR HK HBLK HC HPAY HINC F1 F2 HLS HROOM
           DI1 SBM KEPT SO SOX FRM FRV GROW HSS HFP.
    pose proof Hsp as Hsp'. pose proof EV as (HL & HV & P48 & _). pose proof HV as (P0 & _).
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
    pose proof HBLK as (HBR & REST). pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR) as (Y1 & Y2 & Y3).
    assert (OFF : forall a, 0x6b3000 <= a < usp - 8388608 \/ 4096 <= a < 0x10000 -> ~ Wpf1 (usp + PSO) a) by (intros a Ha; unfold Wpf1, PSO, SOBUF; lia).
    set (vals' := vals ++ junk_vals R').
    assert (EV' : e_valsA 166 vals' A1 PTR OWN k).
    { pose proof (e_vals_app 134 vals (junk_vals R') A1 PTR OWN k ltac:(lia) EV) as X. rewrite junk_vals_length in X. exact X. }
    apply (HSS fx' vals' R' M1 model1 A A1 PTR OWN LB LK cr g EV' Hk Hj Hjk).
    -
      pose proof (regs_after_keeps vals _ srPA R R' c_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEPT (c_kept_no0A)) as X.
      rewrite HL in X. exact X.
    -
      pose proof (env_app_know ASEGS vals (junk_vals R') _ _ knX ltac:(rewrite HL; exact KV) HK) as HK1. fold vals' in HK1.
      eapply ksubl_sound; [|exact EKN]. unfold keep_pfA.
      refine (know_keep_sound ASEGS 0 PSO 3232 [(48%nat, 65536)] [] [] IMG_PF_A IMG_RW_A (ENVG vals')
                (fun a => ~ Wpf1 (usp + PSO) a) (fun a => usp + PSO - 3232 <= a < usp + PSO) _
                (mrestrict (ahid A model) M) (mrestrict (ahid A model1) M1) _ _ knX HK1).
      + apply (regions_pf1A sp0 Hsp vals' _ PSO [(48%nat, 65536)]); [destruct EV' as (_ & (Q0 & _) & _); exact Q0 | unfold PSO; lia|].
        intros i nb Hf. cbn [find_nz] in Hf. destruct (Nat.eqb i 48) eqn:E48; [|discriminate Hf]. apply Nat.eqb_eq in E48. subst i. injection Hf as <-.
        destruct EV' as (_ & _ & Q48 & _). rewrite Q48, u_small by lia. unfold hzA. pose proof HCAP. lia.
      + intros a Ha Hn. exact (FRV a Ha Hn).
      + intros a Ha. apply GROW. apply (store_ok_defined sp0); [unfold PSO in Ha; lia|].
        pose proof (stk_wr sp0 Hsp vals _ _ knX a 1 HK HW P0 ltac:(unfold PSO in Ha; lia) ltac:(unfold PSO in Ha; lia) 0 1%nat ltac:(lia) ltac:(lia)) as W.
        rewrite Z.add_0_r in W. exact W.
    -
      unfold Pm8DrvE.e_factsA. split; [exact HBLK|].
      split. { rewrite <- HC. apply rdn_agree. intros q Hq. rewrite u_small by lia. apply FRM; [lia|]. apply OFF. unfold LEN in *. lia. }
      split. { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
               - assert (Hp0 : payloadA = []) by (apply length_zero_iff_nil; rewrite (payloadA_len sp0 Hsp fdata); fold PL; lia). rewrite Hp0. reflexivity.
               - pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR2) as (U1 & U2 & U3). subst PTR.
                 rewrite <- HPAY. apply rdn_agree. intros q Hq. rewrite (payloadA_len sp0 Hsp fdata) in Hq. fold PL in Hq. rewrite u_small by lia. apply FRM; [lia|]. apply OFF. lia. }
      split; [exact DI1|]. split; [exact HINC|]. split; [exact G1|]. split; [exact G2|]. split; [exact SO|]. split; [exact SOX|].
      split; [|exact HROOM].
      apply (ls_ok_frameW g M M1 HLS). intros a Ha Hn. apply FRM; [exact Ha|]. intros HWp. apply Hn. apply (Wpf1_in_DW (usp + PSO)); [unfold PSO; lia | exact HWp].
    - exact HFP.
  Qed.

  Lemma kword_sp : forall vals ebs (MV : word -> option byte) kn off (w : nat) v,
    know_ok ASEGS (Env (vals_ev vals) ebs) MV kn -> existsb (kentry_eqb (KWord (SA (EVar 0) off) w v)) kn = true -> vals_ev vals 0 = sp0 ->
    rdn ASEGS MV (Z_to_bv 64 (usp + off)) w = Some (word_to_le_bytes w (edenot (Env (vals_ev vals) ebs) v)).
  Proof.
    intros vals ebs MV kn off w v HK Hb P0. apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X. destruct X as (_ & Hf & X).
    rewrite <- (Z_to_bv_bv_unsigned 64 (adenot _ _)) in X. rewrite (flat_u _ _ _ Hf) in X. unfold estart in X. cbn [a_base a_off edenot ev] in X. rewrite P0 in X. exact X.
  Qed.

  Lemma kept_of_KS : forall (KSl : list nat) (R R' : bvmap 5 word),
    (forall x, In x KSl -> getr R' (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x))) ->
    forallb (fun n => existsb (Nat.eqb n) KSl) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat = true ->
    forall r, In r c_kept -> getr R' r = getr R r.
  Proof.
    intros KSl R R' KS Hb r Hr. rewrite forallb_forall in Hb.
    assert (IN : forall n, In n [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> In n KSl).
    { intros n Hn. pose proof (Hb n Hn) as X. apply existsb_exists in X as (m & Hm & Em). apply Nat.eqb_eq in Em. subst m. exact Hm. }
    unfold c_kept in Hr. cbn [In] in Hr.
    destruct Hr as [<-|Hr]; [exact (KS 2%nat (IN 2%nat ltac:(cbn; tauto)))|]. destruct Hr as [<-|Hr]; [exact (KS 3%nat (IN 3%nat ltac:(cbn; tauto)))|].
    destruct Hr as [<-|Hr]; [exact (KS 4%nat (IN 4%nat ltac:(cbn; tauto)))|]. destruct Hr as [<-|Hr]; [exact (KS 8%nat (IN 8%nat ltac:(cbn; tauto)))|].
    destruct Hr as [<-|Hr]; [exact (KS 9%nat (IN 9%nat ltac:(cbn; tauto)))|]. destruct Hr as [<-|Hr]; [exact (KS 18%nat (IN 18%nat ltac:(cbn; tauto)))|].
    destruct Hr as [<-|Hr]; [exact (KS 19%nat (IN 19%nat ltac:(cbn; tauto)))|]. destruct Hr as [<-|Hr]; [exact (KS 20%nat (IN 20%nat ltac:(cbn; tauto)))|].
    destruct Hr as [<-|Hr]; [exact (KS 21%nat (IN 21%nat ltac:(cbn; tauto)))|]. destruct Hr as [<-|Hr]; [exact (KS 22%nat (IN 22%nat ltac:(cbn; tauto)))|].
    destruct Hr as [<-|Hr]; [exact (KS 23%nat (IN 23%nat ltac:(cbn; tauto)))|]. destruct Hr as [<-|Hr]; [exact (KS 24%nat (IN 24%nat ltac:(cbn; tauto)))|].
    destruct Hr as [<-|Hr]; [exact (KS 25%nat (IN 25%nat ltac:(cbn; tauto)))|]. destruct Hr as [<-|Hr]; [exact (KS 26%nat (IN 26%nat ltac:(cbn; tauto)))|].
    destruct Hr as [<-|Hr]; [exact (KS 27%nat (IN 27%nat ltac:(cbn; tauto)))|]. destruct Hr.
  Qed.

  Definition PF_KN : list kentry := [KWord (SA (EVar 0) (-264)) 8 (ELit 0); KImg 65536 1392640; KWord (SA (ELit 0) 7015056) 8 (EVar 3)].
  Definition pf_kn_ok (knX : list kentry) : bool :=
    forallb (fun K => existsb (kentry_eqb K) knX) PF_KN && kn_vars_lt 134 knX && has_window knX && ksubl_b (keep_pfA PSO [(48%nat, 65536)] knX) knLH2A.

  Lemma zero4_of_zero8 : firstn 4 (word_to_le_bytes 8 (Z_to_bv 64 0)) = word_to_le_bytes 4 (Z_to_bv 64 0).
  Proof. vm_compute. repeat (apply f_equal2; [apply bv_eq; reflexivity|]). reflexivity. Qed.

  Lemma pf_premsA : forall knX vals R (MV : word -> option byte) A1 PTR OWN k,
    pf_kn_ok knX = true -> e_valsA 134 vals A1 PTR OWN k ->
    regs_ok (ENVG vals) srPA R -> know_ok ASEGS (ENVG vals) MV knX ->
    let S := usp + PSO in
    (usp - 4096 <= S /\ S + 32 <= usp /\ S mod 16 = 0 /\ 0 <= bv_unsigned can < 2 ^ 64)
    /\ (getr R 1%bv = Z_to_bv 64 717176 /\ getr R 2%bv = Z_to_bv 64 S /\ getr R 10%bv = Z_to_bv 64 86425 /\ getr R 11%bv = Z_to_bv 64 (S + 24))
    /\ (forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 1392640 -> MV (Z_to_bv 64 i) = None)
    /\ rdn ASEGS MV (Z_to_bv 64 7015056) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned can)))
    /\ rdn ASEGS MV (Z_to_bv 64 (S + 24)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Proof.
    intros knX vals R MV A1 PTR OWN k OKb (HL & HV & _) HR HK S. pose proof HV as (P0 & _ & _ & P3). pose proof Hsp as Hsp'.
    unfold pf_kn_ok in OKb. apply andb_prop in OKb as (OKb & EKN). apply andb_prop in OKb as (OKb & HW). apply andb_prop in OKb as (OKb & KV).
    rewrite forallb_forall in OKb.
    assert (KB : forall K, In K PF_KN -> existsb (kentry_eqb K) knX = true) by (intros K HKin; exact (OKb K HKin)).
    split. { unfold S, PSO. split; [lia|]. split; [lia|]. split; [|exact (u64_range can)].
             Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
             clear - Hal. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split. { split; [regv HR (1%bv : reg); reflexivity|]. split; [regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite P0; apply alu_add_w_litA|].
             split; [regv HR (10%bv : reg); reflexivity|]. regv HR (11%bv : reg). cbn [edenot ev ENVA]. rewrite P0. rewrite alu_add_w_litA. f_equal. unfold S, PSO. lia. }
    split. { intros a n Ha Hn d q Hd Hq. exact (stk_wr sp0 Hsp vals _ MV knX a n HK HW P0 Ha Hn d q Hd Hq). }
    split. { exact (kimg_clear _ MV knX 65536 1392640 HK (KB (KImg 65536 1392640) ltac:(unfold PF_KN; cbn [In]; tauto))). }
    split. { rewrite Z_to_bv_bv_unsigned, <- P3.
             exact (kword_lit sp0 _ MV knX 7015056 8%nat (EVar 3) HK (KB (KWord (SA (ELit 0) 7015056) 8 (EVar 3)) ltac:(unfold PF_KN; cbn [In]; tauto)) ltac:(lia) ltac:(cbn; lia)). }
    pose proof (kword_sp vals _ MV knX (-264) 8%nat (ELit 0) HK (KB (KWord (SA (EVar 0) (-264)) 8 (ELit 0)) ltac:(unfold PF_KN; cbn [In]; tauto)) P0) as X.
    cbn [edenot] in X. replace (S + 24) with (usp + -264) by (unfold S, PSO; lia).
    rewrite <- zero4_of_zero8. exact (SeqExec.rdn_firstn ASEGS MV 8%nat _ _ 4%nat X ltac:(lia)).
  Qed.

  Lemma pf_siteKA : forall (fx' : PropExec.FPState) knX vals R M (model : Model) A (A1 PTR OWN k : Z) (j : nat) LB LK cr g K,
    pf_kn_ok knX = true -> e_valsA 134 vals A1 PTR OWN k -> 1 <= k -> Z.of_nat j + 1 + k <= 4 ->
    regs_ok (ENVG vals) srPA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knX ->
    e_factsA (k - 1) (Z.of_nat j) A1 PTR OWN LB LK cr g A M model ->
    SSPA k (Z.of_nat j + 1) K ->
    PmLibIfaceA.fp_ok fx' ->
    srealizes ASEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0x6a58c) M (seg_rom ASEGS)) model) K.
  Proof.
    intros fx' knX vals R M model A A1 PTR OWN k j LB LK cr g K OKb EV Hk Hjk HR HK (HBLK & HC & HPAY & DI & HINC & F1 & F2 & SO & SOX & HLS & HROOM) HSS HFP.
    destruct (pf_premsA knX vals R _ A1 PTR OWN k OKb EV HR HK) as ((S1 & S2 & S16 & CZ) & (R1 & R2 & R10 & R11) & WIN & IMG & CAN & ARG).
    pose proof OKb as OKb'. unfold pf_kn_ok in OKb'. apply andb_prop in OKb' as (OKb' & EKN). apply andb_prop in OKb' as (OKb' & HW). apply andb_prop in OKb' as (_ & KV).

    assert (SOXT : forall (MVb : word -> option byte) (W : Z -> Prop) jj,
              (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> MVb (Z_to_bv 64 a) = mrestrict (ahid A model) M (Z_to_bv 64 a)) ->
              0 <= jj -> (forall a, W a -> Wpf (usp + PSO) jj a) -> stdoutXA MVb).
    { intros MVb W jj FR Hjj WS. destruct SOX as (X1 & X2 & X3 & X4 & X5). pose proof Hsp as Hsp'.
      unfold stdoutXA. repeat split; (eapply (TRf _ MVb W FR); [eassumption | lia | cbn; lia |]); intros i Hi Hw; apply WS in Hw; unfold Wpf, PSO, SOBUF in Hw; cbn in Hi; lia. }
    destruct j as [|[|[|j]]]; [ | | | lia].
    - change (Z.of_nat 0) with 0 in *.
      apply (@printf2_run fx' scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hpr M0 LB LK cr A M model R (usp + PSO) (bv_unsigned can) K DI S1 S2 S16 CZ R1 R2 R10 R11 WIN IMG CAN ARG SO HFP).
      intros fx2 R' M1 model1 HFP2 DI1 SBM KS Q10 SO1 FRM FRV GROW.
      assert (WI : forall a, ~ Wpf1 (usp + PSO) a -> ~ Wpf (usp + PSO) 0 a) by (intros a Hn Hw; apply Hn; exact (Wpf_in_Wpf1 _ 0 a ltac:(lia) Hw)).
      apply (pf_postA fx2 knX vals R R' M M1 model model1 A A1 PTR OWN k 1 LB LK cr g K KV HW EKN EV Hk ltac:(lia) ltac:(lia) HR HK HBLK HC HPAY HINC F1 F2 HLS HROOM DI1 SBM
               (kept_of_KS _ R R' KS ltac:(vm_compute; reflexivity)) SO1); [ | | | | exact HSS | exact HFP2].
      + exact (SOXT _ _ 0 (fun a Ha Hn => FRV a Ha Hn) ltac:(lia) (fun a Hw => Hw)).
      + intros a Ha Hn. exact (FRM a Ha (WI a Hn)).
      + intros a Ha Hn. exact (FRV a Ha (WI a Hn)).
      + exact GROW.
    - change (Z.of_nat 1) with 1 in *.
      apply (@printf3_run fx' scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hpr M0 LB LK cr A M model R (usp + PSO) (bv_unsigned can) K DI S1 S2 S16 CZ R1 R2 R10 R11 WIN IMG CAN ARG SO HFP).
      intros fx2 R' M1 model1 HFP2 DI1 SBM KS Q10 SO1 FRM FRV GROW.
      assert (WI : forall a, ~ Wpf1 (usp + PSO) a -> ~ Wpf (usp + PSO) 1 a) by (intros a Hn Hw; apply Hn; exact (Wpf_in_Wpf1 _ 1 a ltac:(lia) Hw)).
      apply (pf_postA fx2 knX vals R R' M M1 model model1 A A1 PTR OWN k 2 LB LK cr g K KV HW EKN EV Hk ltac:(lia) ltac:(lia) HR HK HBLK HC HPAY HINC F1 F2 HLS HROOM DI1 SBM
               (kept_of_KS _ R R' KS ltac:(vm_compute; reflexivity)) SO1); [ | | | | exact HSS | exact HFP2].
      + exact (SOXT _ _ 1 (fun a Ha Hn => FRV a Ha Hn) ltac:(lia) (fun a Hw => Hw)).
      + intros a Ha Hn. exact (FRM a Ha (WI a Hn)).
      + intros a Ha Hn. exact (FRV a Ha (WI a Hn)).
      + exact GROW.
    - change (Z.of_nat 2) with 2 in *.
      apply (@printf4_run fx' scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hpr M0 LB LK cr A M model R (usp + PSO) (bv_unsigned can) K DI S1 S2 S16 CZ R1 R2 R10 R11 WIN IMG CAN ARG SO HFP).
      intros fx2 R' M1 model1 HFP2 DI1 SBM KS Q10 SO1 FRM FRV GROW.
      assert (WI : forall a, ~ Wpf1 (usp + PSO) a -> ~ Wpf (usp + PSO) 2 a) by (intros a Hn Hw; apply Hn; exact (Wpf_in_Wpf1 _ 2 a ltac:(lia) Hw)).
      apply (pf_postA fx2 knX vals R R' M M1 model model1 A A1 PTR OWN k 3 LB LK cr g K KV HW EKN EV Hk ltac:(lia) ltac:(lia) HR HK HBLK HC HPAY HINC F1 F2 HLS HROOM DI1 SBM
               (kept_of_KS _ R R' KS ltac:(vm_compute; reflexivity)) SO1); [ | | | | exact HSS | exact HFP2].
      + exact (SOXT _ _ 2 (fun a Ha Hn => FRV a Ha Hn) ltac:(lia) (fun a Hw => Hw)).
      + intros a Ha Hn. exact (FRM a Ha (WI a Hn)).
      + intros a Ha Hn. exact (FRV a Ha (WI a Hn)).
      + exact GROW.
  Qed.

  Lemma pf_site1A : forall (fx' : PropExec.FPState) knX vals R M (model : Model) A (A1 PTR OWN k : Z) LB LK cr g K,
    pf_kn_ok knX = true -> existsb (kentry_eqb (KImg 0x157a50 0x157b38)) knX = true -> e_valsA 134 vals A1 PTR OWN k -> 1 <= k <= 4 ->
    regs_ok (ENVG vals) srPA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knX ->
    blk_factsA A1 PTR OWN LB ->
    rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
    rdn ASEGS M (Z_to_bv 64 PTR) (length payloadA) = Some payloadA ->
    dinvA LB LK cr A M model -> incl A0 A -> m_fds model = fds0 -> m_fs model = fs0 -> ls_ok LSt g M -> lib_roomA (k - 1) LK cr ->
    K [] -> SSPA k 0 K ->
    PmLibIfaceA.fp_ok fx' ->
    srealizes ASEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0x6a58c) M (seg_rom ASEGS)) model) (t_emit (W 1 (zero_lines 1)) K).
  Proof.
    intros fx' knX vals R M model A A1 PTR OWN k LB LK cr g K OKb KIMG EV Hk HR HK HBLK HC HPAY DI HINC F1 F2 HLS HROOM HK0 HSS HFP.
    destruct (pf_premsA knX vals R _ A1 PTR OWN k OKb EV HR HK) as ((S1 & S2 & S16 & CZ) & (R1 & R2 & R10 & R11) & WIN & IMG & CAN & ARG).
    pose proof OKb as OKb'. unfold pf_kn_ok in OKb'. apply andb_prop in OKb' as (OKb' & EKN). apply andb_prop in OKb' as (OKb' & HW). apply andb_prop in OKb' as (_ & KV).
    pose proof (stdout0_of_kn sp0 Hsp fdata _ _ _ HK KIMG) as SO0.
    assert (FD1 : fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) by (rewrite F1; exact fds0_lookup1).
    apply (@printf1_run fx' scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hpr M0 LB LK cr A M model R (usp + PSO) (bv_unsigned can) K DI S1 S2 S16 CZ R1 R2 R10 R11 WIN IMG CAN ARG SO0 FD1 HK0 HFP).
    intros fx2 R' M1 model1 HFP2 DI1 SBM KEPT Q10 SO1 SOX1 FRM FRV GROW.
    exact (pf_postA fx2 knX vals R R' M M1 model model1 A A1 PTR OWN k 0 LB LK cr g K KV HW EKN EV ltac:(lia) ltac:(lia) ltac:(lia) HR HK HBLK HC HPAY HINC F1 F2 HLS HROOM DI1 SBM
             KEPT SO1 SOX1 FRM FRV GROW HSS HFP2).
  Qed.

  Lemma PL_bound : 0 <= PL -> PL < 2 ^ 26.
  Proof. intros H. subst PL. unfold PLA in *. pose proof (CFGA_range sp0 fdata). pose proof HCAP. pose proof HLEN. lia. Qed.

  Lemma room_head : forall kc LK cr, 1 <= kc -> 0 <= PL -> lib_roomA kc LK cr ->
    credit_le (lla_credit Lay PL) cr /\ (forall c, In c PM_FS_CLASSES -> Z.of_nat (ff_count c LK) + lla_frames Lay c <= ff_cap c).
  Proof.
    intros kc LK cr Hk HPL ((C1 & C2) & FR). destruct (dlla_credit_pos Lay L DLL PL HPL) as (P1 & P2).
    unfold Pm8DrvE.credit_scaleA in C1, C2. cbn [fst snd] in C1, C2. fold PL in C1, C2.
    split. { split; nia. }
    intros c Hc. specialize (FR c Hc). destruct (dlla_frames Lay L DLL c Hc) as (LK0 & _). nia.
  Qed.
  Lemma room_step : forall kc LK LK' cr cr', 1 <= kc -> 0 <= PL -> lib_roomA kc LK cr ->
    credit_le (credit_sub cr (lla_credit Lay PL)) cr' ->
    (forall c, In c PM_FS_CLASSES -> Z.of_nat (ff_count c LK') <= Z.of_nat (ff_count c LK) + lla_leak Lay c) ->
    lib_roomA (kc - 1) LK' cr'.
  Proof.
    intros kc LK LK' cr cr' Hk HPL ((C1 & C2) & FR) (S1 & S2) HLEAK.
    unfold Pm8DrvE.lib_roomA, Pm8DrvE.credit_scaleA, credit_le, credit_sub in *. cbn [fst snd] in *. fold PL in C1, C2 |- *.
    split. { split; [replace ((kc - 1) * fst (lla_credit Lay PL)) with (kc * fst (lla_credit Lay PL) - fst (lla_credit Lay PL)) by ring
                    | replace ((kc - 1) * snd (lla_credit Lay PL)) with (kc * snd (lla_credit Lay PL) - snd (lla_credit Lay PL)) by ring]; lia. }
    intros c Hc. specialize (FR c Hc). specialize (HLEAK c Hc).
    replace ((kc - 1) * lla_leak Lay c) with (kc * lla_leak Lay c - lla_leak Lay c) by ring. lia.
  Qed.

  Lemma lib_then_pfA : forall (fx' : PropExec.FPState) knL vals R M (model : Model) A (A1 PTR OWN k : Z) LB LK cr g (KP : TSet),
    kn_vars_lt 102 knL = true -> has_window knL = true ->
    e_valsA 102 vals A1 PTR OWN k -> 1 <= k <= 4 ->
    regs_ok (ENVG vals) srLBA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knL ->
    blk_factsA A1 PTR OWN LB ->
    rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
    rdn ASEGS M (Z_to_bv 64 PTR) (length payloadA) = Some payloadA ->
    dinvA LB LK cr A M model -> incl A0 A -> m_fds model = fds0 -> m_fs model = fs0 -> ls_ok LSt g M -> lib_roomA k LK cr ->
    KP [] ->
    (forall (fx2 : PropExec.FPState) vals' R' M' (model' : Model) A' LK' cr' g',
       e_valsA 134 vals' A1 PTR OWN k ->
       regs_ok (ENVG vals') srLr0A R' -> know_ok ASEGS (ENVG vals') (mrestrict (ahid A' model') M') (keep_libA TSO LIBSTK [(48%nat, 65536)] [] knL) ->
       rdn ASEGS M' (Z_to_bv 64 A1) (length fdata) = Some fdata ->
       rdn ASEGS M' (Z_to_bv 64 PTR) (length payloadA) = Some payloadA ->
       dinvA LB LK' cr' A' M' model' -> incl A0 A' -> m_fds model' = fds0 -> m_fs model' = fs0 -> ls_ok LSt g' M' -> lib_roomA (k - 1) LK' cr' ->
       (forall lo hi a, In (lo, hi) IMG_LIB_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       PmLibIfaceA.fp_ok fx2 ->
       srealizes ASEGS scfg (mkCfg (@mkst fx2 R' (Z_to_bv 64 0xaf080) M' (seg_rom ASEGS)) model') KP) ->
    PmLibIfaceA.fp_ok fx' ->
    srealizes ASEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0xaf184) M (seg_rom ASEGS)) model) KP.
  Proof.
    intros fx' knL vals R M model A A1 PTR OWN k LB LK cr g KP KV HW EV Hk HR HK HBLK HC HPAY DI HINC F1 F2 HLS HROOM HKP0 CONT HFP.
    pose proof Hsp as Hsp'. pose proof EV as (HL & HV & P48 & P70 & P73 & P79 & P81 & P82 & P83). pose proof HV as (P0 & _).
    pose proof HBLK as (HBR & REST). pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR) as (Y1 & Y2 & Y3).
    assert (HPL : 0 <= PL) by (destruct REST as [(HPL0 & _) | (HPLp & _)]; lia).
    pose proof (PL_bound HPL) as HPL26. pose proof (payloadA_len sp0 Hsp fdata) as PLN. fold PL in PLN.
    destruct (room_head k LK cr ltac:(lia) HPL HROOM) as (HCR & HFF).
    destruct (dlla_stack Lay L DLL) as ((ST1 & ST2) & ST3).
    apply (@alib_site fx' scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def Lay LSt DLL (lioa_call _ _ _ _ _ _ LIOK) vals _ srLBA knL R M model LB LK cr A g TSO LIBSTK
             [(48%nat, 65536)] [] PTR 0xaf080 payloadA KP HR HK).
    - rewrite HL. vm_compute. reflexivity.
    - rewrite HL. exact KV.
    - rewrite HL. lia.
    - exact P0.
    - exact HW.
    - regv HR (2%bv : reg). cbn [edenot ev ENVA]. rewrite P0. apply alu_add_w_litA.
    - unfold TSO. lia.
    - reflexivity.
    - unfold LIBSTK. lia.
    - regv HR (1%bv : reg). reflexivity.
    - lia.
    - reflexivity.
    - regv HR (3%bv : reg). reflexivity.
    - regv HR (4%bv : reg). reflexivity.
    - regv HR (10%bv : reg). cbn [edenot ev ENVA]. exact P82.
    - regv HR (11%bv : reg). cbn [edenot ev ENVA]. rewrite P79, PLN. f_equal. lia.
    - rewrite PLN. lia.
    - destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      + left. split; [rewrite PLN; lia | rewrite (dlla_empty Lay L DLL); exact HPTR].
      + right. split; [rewrite PLN; lia|]. subst LB PTR. left. rewrite PLN. f_equal. lia.
    - exact HPAY.
    - rewrite PLN. replace (Z.of_nat (Z.to_nat PL)) with PL by lia. exact HCR.
    - exact HFF.
    - exact HLS.
    - exact DI.
    - intros i nb Hf. cbn [find_nz] in Hf. destruct (Nat.eqb i 48) eqn:E48; [|discriminate Hf]. apply Nat.eqb_eq in E48. subst i. injection Hf as <-.
      split; [rewrite HL; lia|]. rewrite P48. pose proof HBR as (B1 & _ & _ & _ & _ & (_ & _ & B47)). pose proof HCAP. rewrite u_small by lia. exists CAP. split; [lia|]. split; [|exact HBR].
      destruct REST as [(_ & _ & _ & ->) | (_ & _ & _ & _ & ->)]; [left | right; left]; reflexivity.
    - intros v b Hf. discriminate Hf.
    - exact HFP.
    - exact HKP0.
    - intros fx2 R' M' model' g' cr' LK' A' HFP2 vals' E' HL' HR' HK' DI' MRT HINC' HLEAK HLS' HCR' HAB HBLK' HIMG'.
      rewrite HL in HL', HR'. change (sr_upd (sr_after_call_j srLBA (map ridx c_kept) 102) (ridx 10) (ELit 0)) with srLr0A in HR'.
      destruct (model_rt_fds _ _ MRT) as (Q1 & Q2). rewrite F1 in Q1. rewrite F2 in Q2.
      apply (CONT fx2 vals' R' M' model' A' LK' cr' g').
      + pose proof (e_vals_app 102 vals (junk_vals R') A1 PTR OWN k ltac:(lia) EV) as X. rewrite junk_vals_length in X. exact X.
      + exact HR'.
      + exact HK'.
      + rewrite <- HC. apply rdn_agree. intros q Hq. rewrite u_small by lia. apply HBLK'; [lia|].
        exists (A1, CAP). split; [destruct REST as [(_ & _ & _ & ->)|(_ & _ & _ & _ & ->)]; [left|right; left]; reflexivity|]. cbn [fst snd]. unfold LEN in *. lia.
      + destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
        * assert (Hp0 : payloadA = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
        * pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR2) as (U1 & U2 & U3).
          rewrite <- HPAY. apply rdn_agree. intros q Hq. rewrite PLN in Hq. rewrite u_small by lia. apply HBLK'; [lia|].
          exists (OWN, PL). subst LB PTR. split; [left; reflexivity|]. cbn [fst snd]. lia.
      + exact DI'.
      + intros x Hx. apply HINC'. apply HINC. exact Hx.
      + exact Q1.
      + exact Q2.
      + exact HLS'.
      + rewrite PLN in HCR'. replace (Z.of_nat (Z.to_nat PL)) with PL in HCR' by lia. exact (room_step k LK LK' cr cr' ltac:(lia) HPL HROOM HCR' HLEAK).
      + exact HIMG'.
      + exact HFP2.
  Qed.

  Lemma facts_offstkA : forall (M M2 : word -> option byte) (H2 : word -> bool) (A1 PTR OWN : Z) LB g,
    (forall a, 0 <= a < 2 ^ 64 -> ~ CWS a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    blk_factsA A1 PTR OWN LB ->
    rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
    rdn ASEGS M (Z_to_bv 64 PTR) (length payloadA) = Some payloadA ->
    ls_ok LSt g M ->
    rdn ASEGS M2 (Z_to_bv 64 A1) (length fdata) = Some fdata /\ rdn ASEGS M2 (Z_to_bv 64 PTR) (length payloadA) = Some payloadA /\ ls_ok LSt g M2
    /\ (forall j, 0 <= j <= 500 -> stdoutA j (mrestrict H2 M) -> stdoutXA (mrestrict H2 M) -> stdoutA j (mrestrict H2 M2) /\ stdoutXA (mrestrict H2 M2)).
  Proof.
    intros M M2 H2 A1 PTR OWN LB g FRS HBLK HC HPAY HLS. pose proof Hsp as Hsp'.
    pose proof HBLK as (HBR & REST). pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR) as (Y1 & Y2 & Y3).
    pose proof (payloadA_len sp0 Hsp fdata) as PLN. fold PL in PLN.
    split. { rewrite <- HC. apply rdn_agree. intros q Hq. rewrite u_small by lia. apply FRS; [lia|]. unfold CWS, LEN in *. lia. }
    split. { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
             - assert (Hp0 : payloadA = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
             - pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR2) as (U1 & U2 & U3). subst PTR.
               rewrite <- HPAY. apply rdn_agree. intros q Hq. rewrite PLN in Hq. rewrite u_small by lia. apply FRS; [lia|]. unfold CWS. lia. }
    split. { apply (ls_ok_frameW g M M2 HLS). intros a Ha Hn. apply FRS; [exact Ha|]. intros HS. apply Hn. unfold DW. left. exact HS. }
    intros j Hj SO SOX. apply (stdout_agree sp0 Hsp fdata j _ _ SO SOX Hj). intros a Ha. unfold mrestrict.
    destruct (H2 (Z_to_bv 64 a)); [reflexivity|]. apply FRS; [unfold SOBUF in Ha; lia | unfold CWS, SOBUF in *; lia].
  Qed.

  Lemma facts_offstkAA : forall (M M2 : word -> option byte) (H2 : word -> bool) (A1 PTR OWN : Z) LB g,
    (forall a, 0 <= a < 2 ^ 64 -> ~ CWSA a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    blk_factsA A1 PTR OWN LB ->
    rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
    rdn ASEGS M (Z_to_bv 64 PTR) (length payloadA) = Some payloadA ->
    ls_ok LSt g M ->
    rdn ASEGS M2 (Z_to_bv 64 A1) (length fdata) = Some fdata /\ rdn ASEGS M2 (Z_to_bv 64 PTR) (length payloadA) = Some payloadA /\ ls_ok LSt g M2
    /\ (forall j, 0 <= j <= 500 -> stdoutA j (mrestrict H2 M) -> stdoutXA (mrestrict H2 M) -> stdoutA j (mrestrict H2 M2) /\ stdoutXA (mrestrict H2 M2)).
  Proof.
    intros M M2 H2 A1 PTR OWN LB g FRS HBLK HC HPAY HLS. pose proof Hsp as Hsp'.
    pose proof HBLK as (HBR & REST). pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR) as (Y1 & Y2 & Y3).
    pose proof (payloadA_len sp0 Hsp fdata) as PLN. fold PL in PLN.
    split. { rewrite <- HC. apply rdn_agree. intros q Hq. rewrite u_small by lia. apply FRS; [lia|]. unfold CWSA, CWS, LEN in *. lia. }
    split. { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
             - assert (Hp0 : payloadA = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
             - pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR2) as (U1 & U2 & U3). subst PTR.
               rewrite <- HPAY. apply rdn_agree. intros q Hq. rewrite PLN in Hq. rewrite u_small by lia. apply FRS; [lia|]. unfold CWSA, CWS. lia. }
    split. { apply (ls_ok_frameWA g M M2 HLS). intros a Ha Hn. apply FRS; [exact Ha|]. intros HS. apply Hn. unfold DWA. destruct HS as [HS|HS]; [left; unfold DW; left; exact HS | right; exact HS]. }
    intros j Hj SO SOX. apply (stdout_agree sp0 Hsp fdata j _ _ SO SOX Hj). intros a Ha. unfold mrestrict.
    destruct (H2 (Z_to_bv 64 a)); [reflexivity|]. apply FRS; [unfold SOBUF in Ha; lia | unfold CWSA, CWS, SOBUF in *; lia].
  Qed.

  Lemma iter2A : forall k (j : nat) K, K [] -> SSPA k (Z.of_nat j + 1) K -> LH2PA k (Z.of_nat j) K.
  Proof.
    intros k j K HKnil HSS. unfold Pm8DrvE.LH2PA.
    intros fx' vals R M model A A1 PTR OWN LB LK cr g EV Hk Hj Hjk HR HK (HBLK & HC & HPAY & DI & HINC & F1 & F2 & SO & SOX & HLS & HROOM) HFP.
    pose proof EV as (HL & HV & _). pose proof HV as (P0 & _). pose proof Hsp as Hsp'.

    drv_blockT0 HIok Hsp DL HR HK DI P0 scr0 102%nat.
    all: Pm8DrvD.r23_store_side.
    lazymatch type of EQM with _ = mem_denot _ _ ?lg => pose proof (block_frame_stkA vals _ A M M1 model lg P0 ltac:(vm_compute; reflexivity) EQM EQH) as FRB end.
    destruct (facts_offstkAA M M1 (ahid A model) A1 PTR OWN LB g FRB HBLK HC HPAY HLS) as (HCb & HPAYb & HLSb & SOTb).
    destruct (SOTb (Z.of_nat j) ltac:(lia) SO SOX) as (SOb & SOXb). clear SO SOX. rename SOb into SO, SOXb into SOX.
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
    pose proof (ahid_sbm A model model0 SBM) as AH. rewrite <- AH in SO, SOX.
    clear HR HK DI EQM EQH SBM AH F1 F2 HC HPAY HLS. rename R0 into Rb, HR0 into HRb, HK0 into HKb, DI0 into DIb, model0 into modelb, M into Mlh, M1 into M, HCb into HC, HPAYb into HPAY, HLSb into HLS.
    apply (lib_then_pfA fx' knLB2A vals Rb M modelb A A1 PTR OWN k LB LK cr g K ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) EV ltac:(lia) HRb HKb HBLK HC HPAY DIb HINC G1 G2 HLS HROOM HKnil); [|exact HFP].
    intros fx2 vals' R' M' model' A' LK' cr' g' EV' HR' HK' HC' HPAY' DI' HINC' Q1 Q2 HLS' HROOM' HIMG' HFP2.
    destruct (stdout_lib scfg L ar C IL HI HIok sp0 Hsp DL fdata M0 (Z.of_nat j) _ _ _ _ _ _ _ _ _ _ _ _ (in_lib_1 sp0 Hsp CAP HCAP) (in_lib_2 sp0 Hsp CAP HCAP) DIb DI' ltac:(lia) HIMG' SO SOX) as (SO' & SOX').
    pose proof EV' as (HL' & HV' & _). pose proof HV' as (P0' & _).
    clear HRb HKb DIb HC HPAY HLS HROOM SO SOX HIMG' G1 G2.

    drv_blockT0 HIok Hsp DL HR' HK' DI' P0' scr0 134%nat.
    all: Pm8DrvD.r23_store_side.
    lazymatch type of EQM with _ = mem_denot _ _ ?lg => pose proof (block_frame_stkA vals' _ A' M' M1 model' lg P0' ltac:(vm_compute; reflexivity) EQM EQH) as FRS end.
    destruct (facts_offstkAA M' M1 (ahid A' model') A1 PTR OWN LB g' FRS HBLK HC' HPAY' HLS') as (HC2 & HPAY2 & HLS2 & SOT).
    destruct (SOT (Z.of_nat j) ltac:(lia) SO' SOX') as (SO2 & SOX2).
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite Q1 in G1. rewrite Q2 in G2.
    pose proof (ahid_sbm A' model' model0 SBM) as AH. rewrite <- AH in SO2, SOX2.
    apply (pf_siteKA fx2 knP2A vals' R0 M1 model0 A' A1 PTR OWN k j LB LK' cr' g' K ltac:(vm_compute; reflexivity) EV' ltac:(lia) ltac:(lia) HR HK).
    - exact (conj HBLK (conj HC2 (conj HPAY2 (conj DI (conj HINC' (conj G1 (conj G2 (conj SO2 (conj SOX2 (conj HLS2 HROOM')))))))))).
    - exact HSS.
    - exact HFP2.
  Qed.

  Variable LK0 : list fframe.
  Variable crC : credit.
  #[local] Notation CALLS := (Pm8DrvD.CALLSA fdata).
  #[local] Notation cr1 := (Pm8DrvD.cr1A L fdata crC).
  #[local] Notation lh1_kA := (Pm8DrvD.lh1_kA scfg L ar HI sp0 fs0 fdata p0 p1 can M0 LK0 A0 CAP crC).

  Hypothesis AUXV : auxv_atA sp0 p0 M0.
  Hypothesis HROOM1 : lib_roomA CALLS LK0 cr1.

  Hypothesis TAILX : forall j : nat, SSPA 1 (Z.of_nat j) (EA j).

  Lemma iter1A : forall K, K [] -> SSPA CALLS 0 K -> lh1_kA (t_emit (W 1 (zero_lines 1)) K).
  Proof.
    intros K HKnil HSS. unfold Pm8DrvD.lh1_kA.
    intros fx' vals R M model A A1 PTR OWN LB EV HR HK HBLK HC HPAY DI HINC F1 F2 HFP.
    change (e_valsA 102 vals A1 PTR OWN CALLS) in EV.
    pose proof EV as (HL & HV & _). pose proof HV as (P0 & P1 & _). pose proof Hsp as Hsp'. pose proof (CALLSA_range sp0 fdata) as HKr.

    destruct (lib_init_at_call scfg L ar C IL HI HIok sp0 Hsp DL M0 Lay (dlla_L Lay L DLL) DLC vals _ knLH1A LB LK0 cr1 A M model p0 HK ltac:(vm_compute; reflexivity) P1 DI AUXV)
      as (av & uid & rnd & tid & cny & hw & LIF).
    destruct (atexit_init_at_call scfg L ar C IL HI HIok sp0 Hsp DL M0 Lay (dlla_L Lay L DLL) vals _ knLH1A LB LK0 cr1 A M model HK ltac:(vm_compute; reflexivity) DI
                (dlla_atexit Lay L DLL) (dlla_hs0 Lay L DLL) (dlla_need_locks Lay L DLL)) as (AT0 & NL0).
    pose proof (lioa_init _ _ _ _ _ _ LIOK av uid rnd tid cny hw M LIF AT0 NL0) as HLS.

    drv_blockT0 HIok Hsp DL HR HK DI P0 scr0 102%nat.
    all: Pm8DrvD.r23_store_side.
    lazymatch type of EQM with _ = mem_denot _ _ ?lg => pose proof (block_frame_stkA vals _ A M M1 model lg P0 ltac:(vm_compute; reflexivity) EQM EQH) as FRB end.
    destruct (facts_offstkAA M M1 (ahid A model) A1 PTR OWN LB (ls_g0 LSt) FRB HBLK HC HPAY HLS) as (HCb & HPAYb & HLSb & _).
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
    clear HR HK DI EQM EQH SBM F1 F2 HC HPAY HLS. rename R0 into Rb, HR0 into HRb, HK0 into HKb, DI0 into DIb, model0 into modelb, M into Mlh, M1 into M, HCb into HC, HPAYb into HPAY, HLSb into HLS.
    apply (lib_then_pfA fx' knLB1A vals Rb M modelb A A1 PTR OWN CALLS LB LK0 cr1 (ls_g0 LSt) (t_emit (W 1 (zero_lines 1)) K) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             EV HKr HRb HKb HBLK HC HPAY DIb HINC G1 G2 HLS HROOM1 (t_emit_has_nil _ _)); [|exact HFP].
    intros fx2 vals' R' M' model' A' LK' cr' g' EV' HR' HK' HC' HPAY' DI' HINC' Q1 Q2 HLS' HROOM' HIMG' HFP2.
    pose proof EV' as (HL' & HV' & _). pose proof HV' as (P0' & _).
    clear HRb HKb DIb HC HPAY HLS HIMG' G1 G2.

    drv_blockT0 HIok Hsp DL HR' HK' DI' P0' scr0 134%nat.
    all: Pm8DrvD.r23_store_side.
    lazymatch type of EQM with _ = mem_denot _ _ ?lg => pose proof (block_frame_stkA vals' _ A' M' M1 model' lg P0' ltac:(vm_compute; reflexivity) EQM EQH) as FRS end.
    destruct (facts_offstkAA M' M1 (ahid A' model') A1 PTR OWN LB g' FRS HBLK HC' HPAY' HLS') as (HC2 & HPAY2 & HLS2 & _).
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite Q1 in G1. rewrite Q2 in G2.
    exact (pf_site1A fx2 knPA vals' R0 M1 model0 A' A1 PTR OWN CALLS LB LK' cr' g' K ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) EV' HKr HR HK HBLK HC2 HPAY2 DI HINC' G1 G2 HLS2 HROOM'
             HKnil HSS HFP2).
  Qed.

  Lemma SS_realA : forall (n j : nat), (1 <= n)%nat -> Z.of_nat j + Z.of_nat n <= 4 -> SSPA (Z.of_nat n) (Z.of_nat j) (EA (j + n - 1)%nat).
  Proof.
    induction n as [|n IH]; intros j Hn Hjn; [lia|].
    destruct n as [|n'].
    - replace (j + 1 - 1)%nat with j by lia. change (Z.of_nat 1) with 1. apply TAILX.
    - apply (step_SA scfg L ar C IL HI HIok sp0 Hsp DL fs0 fdata p0 p1 can M0 A0 CAP HCAP Lay LSt); [lia|].
      replace (Z.of_nat (Datatypes.S (Datatypes.S n')) - 1) with (Z.of_nat (Datatypes.S n')) by lia.
      apply iter2A; [unfold Pm8DrvE.EA; apply t_emit_has_nil|].
      replace (j + Datatypes.S (Datatypes.S n') - 1)%nat with (Datatypes.S j + Datatypes.S n' - 1)%nat by lia.
      replace (Z.of_nat j + 1) with (Z.of_nat (Datatypes.S j)) by lia. apply IH; lia.
  Qed.

  Theorem drv_loopA : lh1_kA (t_emit (W 1 (zero_lines (Z.to_nat CALLS))) (t_exit (exit_code 0) fs0)).
  Proof.
    pose proof (CALLSA_range sp0 fdata) as HKr.
    set (n := Z.to_nat CALLS). assert (En : Z.of_nat n = CALLS) by (subst n; lia). clearbody n.
    assert (H1 : lh1_kA (t_emit (W 1 (zero_lines 1)) (EA (0 + n - 1)%nat))).
    { apply iter1A; [unfold Pm8DrvE.EA; apply t_emit_has_nil|]. rewrite <- En. exact (SS_realA n 0%nat ltac:(lia) ltac:(lia)). }
    unfold Pm8DrvD.lh1_kA in H1 |- *. intros fx' vals R M model A A1 PTR OWN LB EV HR HK HBLK HC HPAY DI HINC F1 F2 HFP.
    eapply srz_conseq; [exact (H1 fx' vals R M model A A1 PTR OWN LB EV HR HK HBLK HC HPAY DI HINC F1 F2 HFP)|].
    unfold Pm8DrvE.EA. eapply t_eq_trans; [apply t_emit_W_app|].
    replace (zero_lines 1 ++ zero_lines (0 + n - 1)) with (zero_lines n); [apply t_eq_refl|].
    destruct n as [|m]; [lia|]. replace (0 + Datatypes.S m - 1)%nat with m by lia. reflexivity.
  Qed.
End DrvE2.
End FPX_1.
