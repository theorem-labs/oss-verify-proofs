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
  RefNodes RefPrintfLib HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvA_b
  Ba0DrvG_defs_b Ba0DrvG_b Ba0DrvC_defs_b Ba0DrvC_b Ba0DrvD_defs_b Ba0DrvLibL_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma wseg_init : wseg_ok ASEGS (Z_to_bv 64 0x672290) 1 = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma wseg_ax : wseg_ok ASEGS (Z_to_bv 64 0x693d50) 544 = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Ltac entry_store :=
  cbn [sc_denot]; unfold adenot, v_addi; cbn [a_base a_off edenot];
  lazymatch goal with |- store_ok _ _ _ ?n = true =>
    first [ apply (store_ok_window ASEGS _ (Z_to_bv 64 0x693d50) _ 544%nat n 0x693d50 0x693f70);
              first [exact wseg_ax | reflexivity | lia | (vm_compute; intuition discriminate) | (rewrite u_small by lia; lia)]
          | apply (store_ok_window ASEGS _ (Z_to_bv 64 0x672290) _ 1%nat 1%nat 0x672290 0x672291);
              first [exact wseg_init | reflexivity | lia | (vm_compute; intuition discriminate)] ]
  end.

(* [comment removed for export] *)
Ltac drv_blockT0 HIok Hsp DL HR HK DI P0 scr NX :=
  let HZ := fresh "HZ" in
  pose proof (dinv_lzinv _ _ _ _ _ _ HIok _ DL _ _ _ _ _ _ _ DI) as HZ;
  run_block_lz_with HR HK HZ asegs_wx FUELA STOPS_TA scr NX true;
  [ .. | drv_block_post0 HIok Hsp DL DI P0 HZ ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma vals_loA : forall (vals ext : list word) (n j : nat),
  (n <= length vals)%nat -> (j < n)%nat -> vals_ev (firstn n vals ++ ext) j = vals_ev vals j.
Proof.
  intros vals ext n j Hn Hj. unfold vals_ev. rewrite app_nth1 by (rewrite length_firstn; lia).
  rewrite nth_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj). reflexivity.
Qed.
Lemma vals_hiA : forall (vals ext : list word) (n i : nat),
  (n <= length vals)%nat -> vals_ev (firstn n vals ++ ext) (n + i) = nth i ext (Z_to_bv 64 0).
Proof.
  intros vals ext n i Hn. unfold vals_ev. rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn. replace (n + i - Nat.min n (length vals))%nat with i by lia. reflexivity.
Qed.
Lemma len_layA : forall (vals ext : list word) n, (n <= length vals)%nat -> length (firstn n vals ++ ext) = (n + length ext)%nat.
Proof. intros. rewrite length_app, length_firstn. lia. Qed.
Lemma ridx_litA : forall n, (n < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat n)) = n.
Proof.
  intros n Hn. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sr_get_natA : forall sr n, (0 < n < 32)%nat -> sr_get sr (Z_to_bv 5 (Z.of_nat n)) = nth n sr (ELit 0).
Proof.
  intros sr n Hn. unfold sr_get.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz, ridx_litA by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition lay_extA (vals : list word) (R : bvmap 5 word) (W : word) : list word :=
  [vals_ev vals 81; getr R 9; getr R 18; getr R 19; getr R 1; getr R 5; getr R 6; getr R 7;
   getr R 10; getr R 11; getr R 12; getr R 13; getr R 14; getr R 15; getr R 16; getr R 17;
   getr R 28; getr R 29; getr R 30; getr R 31; W].
Definition relayA (vals : list word) (R : bvmap 5 word) (W : word) : list word := firstn 81 vals ++ lay_extA vals R W.

Lemma relayA_len : forall vals R W, (81 <= length vals)%nat -> length (relayA vals R W) = 102%nat.
Proof. intros. unfold relayA. rewrite len_layA by lia. reflexivity. Qed.
Lemma relayA_lo : forall vals R W j, (81 <= length vals)%nat -> (j < 81)%nat -> vals_ev (relayA vals R W) j = vals_ev vals j.
Proof. intros. unfold relayA. apply vals_loA; lia. Qed.
Lemma relayA_81 : forall vals R W, (81 <= length vals)%nat -> vals_ev (relayA vals R W) 81 = vals_ev vals 81.
Proof.
  intros vals R W H. unfold relayA.
  change (vals_ev (firstn 81 vals ++ lay_extA vals R W) 81) with (vals_ev (firstn 81 vals ++ lay_extA vals R W) (81 + 0)).
  rewrite vals_hiA by lia. reflexivity.
Qed.
Lemma relayA_101 : forall vals R W, (81 <= length vals)%nat -> vals_ev (relayA vals R W) 101 = W.
Proof.
  intros vals R W H. unfold relayA.
  change (vals_ev (firstn 81 vals ++ lay_extA vals R W) 101) with (vals_ev (firstn 81 vals ++ lay_extA vals R W) (81 + 20)).
  rewrite vals_hiA by lia. reflexivity.
Qed.
Lemma relayA_agree : forall ebs vals R W, (82 <= length vals)%nat ->
  env_agree 82 (Env (vals_ev vals) ebs) (Env (vals_ev (relayA vals R W)) ebs).
Proof.
  intros ebs vals R W HL. split; [|reflexivity]. intros n Hn. cbn [ev].
  destruct (Nat.eq_dec n 81) as [->|Hne]; [symmetry; apply relayA_81; lia | symmetry; apply relayA_lo; lia].
Qed.

(* [comment removed for export] *)
Definition shared_posD : list nat := [2; 3; 4; 8; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition relay_ok_bD (sr : list expr) : bool :=
  forallb (fun i => expr_eqb (nth i sr (ELit 0)) (nth i srLHA (ELit 0)) && expr_vars_lt 82 (nth i sr (ELit 0))) shared_posD.

Lemma relayA_regs : forall ebs vals sr R W,
  (82 <= length vals)%nat -> relay_ok_bD sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R ->
  regs_ok (Env (vals_ev (relayA vals R W)) ebs) srLHA R.
Proof.
  intros ebs vals sr R W HL Hokb HR.
  unfold relay_ok_bD in Hokb. rewrite forallb_forall in Hokb.
  assert (SH : forall i, In i shared_posD -> getr R (Z_to_bv 5 (Z.of_nat i)) = edenot (Env (vals_ev (relayA vals R W)) ebs) (nth i srLHA (ELit 0))).
  { intros i Hi. pose proof (Hokb i Hi) as H. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1.
    rewrite <- H1. rewrite <- (edenot_agree 82 _ _ _ (relayA_agree ebs vals R W HL) H2).
    assert (Hi32 : (0 < i < 32)%nat) by (unfold shared_posD in Hi; cbn in Hi; lia).
    rewrite (HR (Z_to_bv 5 (Z.of_nat i))), sr_get_natA by exact Hi32. reflexivity. }
  apply regs_ok_by_nth. intros i Hi.
  assert (JK : forall r k, nth r srLHA (ELit 0) = EVar (81 + k) -> nth k (lay_extA vals R W) (Z_to_bv 64 0) = getr R (Z_to_bv 5 (Z.of_nat r)) ->
               getr R (Z_to_bv 5 (Z.of_nat r)) = edenot (Env (vals_ev (relayA vals R W)) ebs) (nth r srLHA (ELit 0))).
  { intros r k Hr Hk. rewrite Hr. cbn [edenot ev]. unfold relayA. rewrite vals_hiA by lia. symmetry. exact Hk. }
  do 32 (destruct i as [|i]; [first [lia | apply SH; cbn; tauto | eapply JK; reflexivity] |]). lia.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvD.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
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
  Variable LK0 : list fframe.
  Variable A0 : list (Z * Z).
  (* [comment removed for export] *)
  Variable CAP : Z.
  Hypothesis HCAP : 65536 <= CAP <= 67108864.
  Variable crC : credit.
  Hypothesis HLEN : Z.of_nat (length fdata) < CAP.

  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation ENVG := (ENVA fdata).
  Let LEN : Z := Z.of_nat (length fdata).
  Let CFG : Z := CFGA fdata.
  Let PL : Z := PLA fdata.
  Let B2 : Z := B2A fdata.
  Let target_k := target_kA scfg ar HI sp0 fs0 fdata p0 p1 can M0 LK0 A0 CAP crC.

  (* [comment removed for export] *)
  Hypothesis Hok : 6 + CFG <= LEN.
  (* [comment removed for export] *)
  Hypothesis Hcr1 : 0 < PL -> acredit_ok L crC PL.

  Definition CALLSA : Z := if CFG =? 0 then 1 else B2 mod 4 + 1.
  Definition payloadA : list byte := skipn (Z.to_nat (6 + CFG)) fdata.
  (* [comment removed for export] *)
  Definition cr1A : credit := if PL =? 0 then crC else adebit L crC PL.

  #[using="sp0 LEN PL"] Lemma CALLSA_range : 1 <= CALLSA <= 4.
  Proof. clear Hok Hcr1 HLEN. unfold CALLSA. destruct (CFG =? 0); [lia|]. pose proof (Z.mod_pos_bound B2 4 ltac:(lia)). lia. Qed.
  #[using="sp0 Hsp CAP HCAP HLEN LEN CFG B2 Hok"] Lemma PLA_range : 0 <= PL <= 67108857.
  Proof. clear Hcr1. subst PL CFG LEN. unfold PLA in *. pose proof (CFGA_range sp0 fdata). lia. Qed.
  #[using="sp0 Hsp B2"] Lemma payloadA_len : length payloadA = Z.to_nat PL.
  Proof. clear Hcr1. unfold payloadA. rewrite length_skipn. subst PL LEN CFG. unfold PLA in *. pose proof (CFGA_range sp0 fdata). lia. Qed.

  (* [comment removed for export] *)
  Definition lh_valsA (vals : list word) (A1 PTR OWN k : Z) : Prop :=
    length vals = 102%nat /\ hdr_valsA sp0 p0 p1 can vals
    /\ vals_ev vals 48 = Z_to_bv 64 A1 /\ vals_ev vals 70 = Z_to_bv 64 LEN
    /\ vals_ev vals 73 = Z_to_bv 64 CFG /\ vals_ev vals 79 = Z_to_bv 64 PL
    /\ vals_ev vals 81 = Z_to_bv 64 k /\ vals_ev vals 82 = Z_to_bv 64 PTR /\ vals_ev vals 83 = Z_to_bv 64 OWN.

  (* [comment removed for export] *)
  Definition blk_factsA (A1 PTR OWN : Z) (LB : list (Z * Z)) : Prop :=
    ablock_range L ar A1 CAP /\
    ((PL = 0 /\ PTR = 0x6722a0 /\ OWN = 0 /\ LB = [(A1, CAP)])
     \/ (0 < PL /\ PTR = OWN /\ ablock_range L ar OWN PL /\ blocks_apart OWN PL [(A1, CAP)] /\ LB = [(OWN, PL); (A1, CAP)])).

  (* [comment removed for export] *)
  Definition lh1_kA (K : TSet) : Prop :=
    forall (fx' : PropExec.FPState) vals R M (model : Model) A (A1 PTR OWN : Z) LB,
      lh_valsA vals A1 PTR OWN CALLSA ->
      regs_ok (ENVG vals) srLHA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knLH1A ->
      blk_factsA A1 PTR OWN LB ->
      rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
      rdn ASEGS M (Z_to_bv 64 PTR) (length payloadA) = Some payloadA ->
      dinvA LB LK0 cr1A A M model -> incl A0 A ->
      m_fds model = fds0 -> m_fs model = fs0 ->
      srealizes ASEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0xa7e8c) M (seg_rom ASEGS)) model) K.

  (* [comment removed for export] *)
  Definition callsFA (v80 : word) : word :=
    edenot (Env (fun n => match n with 80%nat => v80 | _ => Z_to_bv 64 0 end) (blobs_ev [])) calls_xA.
  #[using="Type"] Lemma calls_x_callsFA : forall vals bl, edenot (Env (vals_ev vals) (blobs_ev bl)) calls_xA = callsFA (vals_ev vals 80).
  Proof. intros. reflexivity. Qed.
  #[using="Type"] Lemma callsFA_tab : forallb (fun b => Z.eqb (bv_unsigned (callsFA (Z_to_bv 64 b))) (b mod 4 + 1)) (zseqA 256) = true.
  Proof. vm_compute. reflexivity. Qed.
  #[using="sp0 fdata LEN CFG PL B2"] Lemma callsFA_val : forall b, 0 <= b < 256 -> callsFA (Z_to_bv 64 b) = Z_to_bv 64 (b mod 4 + 1).
  Proof.
    intros b Hb. pose proof callsFA_tab as T. rewrite forallb_forall in T.
    specialize (T b (proj2 (in_zseqA 256 b) ltac:(cbn; lia))). apply Z.eqb_eq in T.
    apply bv_eq. rewrite T. symmetry. apply u_small. pose proof (Z.mod_pos_bound b 4 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="sp0 Hsp CAP HCAP HLEN LEN B2 Hok"] Lemma know_TcA : forall vals M clo chi plo phi,
    vals_ev vals 73 = Z_to_bv 64 CFG -> vals_ev vals 79 = Z_to_bv 64 PL ->
    clo <= CFG <= chi -> plo <= PL <= phi ->
    know_ok ASEGS (ENVG vals) M knT0A -> know_ok ASEGS (ENVG vals) M (knTcA clo chi plo phi).
  Proof.
    intros vals M clo chi plo phi P73 P79 HC HP HK. pose proof (CFGA_range sp0 fdata) as RC. pose proof PLA_range as RP.
    unfold knTcA. constructor; [|constructor; [|exact HK]]; cbn [kentry_ok edenot ev ENVA].
    - rewrite P73, u_small by (subst CFG; lia). lia.
    - rewrite P79, u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="fx C IL HIok Hsp DL HCAP target_k"] Lemma pl0_to_lhA : forall K (fx' : PropExec.FPState) vals1 srX R' M' (model' : Model) A (A1 : Z),
    lh1_kA K ->
    length vals1 = 82%nat -> hdr_valsA sp0 p0 p1 can vals1 ->
    vals_ev vals1 48 = Z_to_bv 64 A1 -> vals_ev vals1 70 = Z_to_bv 64 LEN -> vals_ev vals1 73 = Z_to_bv 64 CFG ->
    vals_ev vals1 79 = Z_to_bv 64 PL -> vals_ev vals1 81 = Z_to_bv 64 CALLSA ->
    regs_ok (ENVG vals1) srX R' -> relay_ok_bD (sr_upd srX (ridx 21) (EVar 81)) = true ->
    nth 9 srX (ELit 0) = ELit 0x6722a0 -> nth 18 srX (ELit 0) = ELit 0 ->
    edenot (ENVG vals1) (nth 21 srX (ELit 0)) = Z_to_bv 64 CALLSA ->
    know_ok ASEGS (ENVG vals1) (mrestrict (ahid A model') M') knTeA ->
    rdn ASEGS M' (Z_to_bv 64 A1) (length fdata) = Some fdata ->
    PL = 0 -> dinvA [(A1, CAP)] LK0 crC A M' model' -> incl A0 A -> m_fds model' = fds0 -> m_fs model' = fs0 ->
    srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xa7e8c) M' (seg_rom ASEGS)) model') K.
  Proof.
    intros K fx' vals1 srX R' M' model' A A1 HLH HL1 WV W48 W70 W73 W79 V81 HR' Hrel H9 H18 H20 HK' HC1 HPL0 DI HINC F1 F2.
    pose proof Hsp as Hsp'.
    assert (Hpay : payloadA = []).
    { pose proof payloadA_len as X. rewrite HPL0 in X. destruct payloadA; [reflexivity | discriminate]. }
    assert (HR2 : regs_ok (ENVG vals1) (sr_upd srX (ridx 21) (EVar 81)) R').
    { apply regs_ok_upd_sameA; [exact HR' | discriminate |].
      rewrite (HR' (21%bv : reg)). change (sr_get srX (21%bv : reg)) with (nth 21 srX (ELit 0)). rewrite H20.
      cbn [edenot ev ENVA]. exact V81. }
    destruct (inv_block1 scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ _ DI (or_introl eq_refl)) as (HBR & _ & _).
    set (valsL := relayA vals1 R' (Z_to_bv 64 0)).
    apply (HLH fx' valsL R' M' model' A A1 0x6722a0 0 [(A1, CAP)]).
    - (* [comment removed for export] *)
      unfold lh_valsA, hdr_valsA in *. subst valsL. rewrite (relayA_len vals1 R' _ ltac:(lia)), relayA_81 by lia.
      rewrite !(relayA_lo vals1 R' _) by lia.
      repeat split; try tauto; try assumption.
      + unfold relayA. change 82%nat with (81 + 1)%nat. rewrite vals_hiA by lia. cbn [nth lay_extA].
        rewrite (HR' (9%bv : reg)). change (sr_get srX (9%bv : reg)) with (nth 9 srX (ELit 0)). rewrite H9. reflexivity.
      + unfold relayA. change 83%nat with (81 + 2)%nat. rewrite vals_hiA by lia. cbn [nth lay_extA].
        rewrite (HR' (18%bv : reg)). change (sr_get srX (18%bv : reg)) with (nth 18 srX (ELit 0)). rewrite H18. reflexivity.
    - (* [comment removed for export] *)
      subst valsL. eapply (relayA_regs _ vals1 _ R' _ ltac:(lia)); [exact Hrel | exact HR2].
    - (* [comment removed for export] *)
      subst valsL. eapply (know_ok_agree ASEGS 82); [apply relayA_agree; lia | vm_compute; reflexivity |].
      eapply ksubl_sound; [exact HK' | vm_compute; reflexivity].
    - split; [exact HBR|]. left. repeat split; lia.
    - exact HC1.
    - rewrite Hpay. reflexivity.
    - unfold cr1A. rewrite (proj2 (Z.eqb_eq PL 0) HPL0). exact DI.
    - exact HINC.
    - exact F1.
    - exact F2.
  Qed.

  #[using="C IL HIok ICok Hsp Hal DL M0_def HCAP HLEN Hok Hcr1"] Theorem drv_targetA : forall K, lh1_kA K -> K [] -> target_k K.
  Proof.
    intros K HLH HK0. unfold target_k, target_kA.
    intros vals R M model A A1 HL HV P48 P70 P71 P72 P73 P79 P80 HR HK HC DI HINC F1 F2.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    destruct (inv_block1 scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ _ DI (or_introl eq_refl)) as (HBR & _ & HZ). pose proof HZ as (Q1 & Q2 & Q4).
    pose proof (CFGA_range sp0 fdata) as HCr. pose proof PLA_range as HPr. pose proof (B2A_range sp0 fdata) as HB2r. pose proof CALLSA_range as HKr.
    assert (ELEN : LEN = Z.of_nat (length fdata)) by reflexivity.
    assert (EPL : PL = LEN - 6 - CFG) by reflexivity.
    fold CFG in P73, HCr. fold PL in P79. fold B2 in P80, HB2r. fold LEN in P70.
    pose proof HV as (P0 & _).
    assert (HPAY0 : rdn ASEGS M (Z_to_bv 64 (A1 + 6 + CFG)) (length payloadA) = Some payloadA).
    { unfold payloadA. rewrite length_skipn.
      pose proof (rdn_skipn ASEGS M (length fdata) (Z_to_bv 64 A1) fdata (Z.to_nat (6 + CFG)) HC ltac:(lia)) as X.
      rewrite w_add_nat, u_small in X by lia.
      replace (A1 + Z.of_nat (Z.to_nat (6 + CFG))) with (A1 + 6 + CFG) in X by lia. exact X. }
    (* [comment removed for export] *)
    set (vals1 := vals ++ [Z_to_bv 64 CALLSA]).
    assert (HL1 : length vals1 = 82%nat) by (subst vals1; rewrite length_app, HL; reflexivity).
    assert (V81 : vals_ev vals1 81 = Z_to_bv 64 CALLSA).
    { subst vals1. rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
    assert (VL : forall j x, (j < 81)%nat -> vals_ev vals j = x -> vals_ev vals1 j = x).
    { intros j x Hj Hx. subst vals1. rewrite vals_ev_app_l by (rewrite HL; exact Hj). exact Hx. }
    assert (WV : hdr_valsA sp0 p0 p1 can vals1) by (subst vals1; apply (hdr_appA sp0 fdata); [exact HV | rewrite HL; lia]).
    pose proof WV as (W0 & _).
    pose proof (VL 48%nat _ ltac:(lia) P48) as W48. pose proof (VL 70%nat _ ltac:(lia) P70) as W70.
    pose proof (VL 73%nat _ ltac:(lia) P73) as W73. pose proof (VL 79%nat _ ltac:(lia) P79) as W79. pose proof (VL 80%nat _ ltac:(lia) P80) as W80.
    pose proof (env_app_regs vals [Z_to_bv 64 CALLSA] _ srT0A R ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know ASEGS vals [Z_to_bv 64 CALLSA] _ _ knT0A ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK1.
    fold vals1 in HR1, HK1. change (Env (vals_ev vals1) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals1) in HR1, HK1.
    clear HR HK. rename HR1 into HR.
    clearbody vals1. clear VL HL HV P0 P48 P70 P71 P72 P73 P79 P80 vals.
    (* [comment removed for export] *)
    assert (HCALLS : CALLSA = (if CFG =? 0 then 1 else B2 mod 4 + 1)) by reflexivity.
    assert (Ecx : (CFG =? 0) = false -> edenot (ENVG vals1) calls_xA = Z_to_bv 64 CALLSA).
    { intros E. unfold ENVA. rewrite calls_x_callsFA, W80, callsFA_val by lia. rewrite HCALLS, E. reflexivity. }
    (* [comment removed for export] *)
    assert (POST : forall M' (model' : Model) log,
               log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_W_A log = true ->
               mrestrict (ahid A model) M' = mem_denot (ENVG vals1) (mrestrict (ahid A model) M) log ->
               (forall a, ahid A model a = true -> M' a = M a) ->
               same_but_materialized model model' ->
               rdn ASEGS M' (Z_to_bv 64 A1) (length fdata) = Some fdata
               /\ rdn ASEGS M' (Z_to_bv 64 (A1 + 6 + CFG)) (length payloadA) = Some payloadA
               /\ m_fds model' = fds0 /\ m_fs model' = fs0).
    { intros M' model' log Hlog EQM EQH SBM. destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
      split; [|split; [|split; [exact G1 | exact G2]]].
      - apply (content_block0 sp0 Hsp fdata vals1 _ A M M' model log A1 CAP (length fdata) fdata W0 Hlog EQM EQH HZ ltac:(lia) HC).
      - apply (content_block0 sp0 Hsp fdata vals1 _ A M M' model log (A1 + 6 + CFG) (CAP - 6 - CFG) (length payloadA) payloadA W0 Hlog EQM EQH);
          [unfold hzA in *; lia | rewrite payloadA_len; lia | exact HPAY0]. }
    destruct (Z.eq_dec PL 0) as [HPL0 | HPLp].
    - (* [comment removed for export] *)
      destruct (CFG =? 0) eqn:ECFG.
      + (* [comment removed for export] *)
        pose proof (know_TcA vals1 _ 0 0 0 0 W73 W79 ltac:(apply Z.eqb_eq in ECFG; lia) ltac:(lia) HK1) as HK. clear HK1.
        drv_blockT0 HIok Hsp DL HR HK DI W0 scr0 82%nat.
        1-4: entry_store.      (* [comment removed for export] *)
        lazymatch goal with EQM : mrestrict _ _ = mem_denot _ _ ?log |- _ =>
          destruct (POST _ _ log ltac:(vm_compute; reflexivity) EQM EQH SBM) as (HC1 & _ & G1 & G2) end.
        eapply (pl0_to_lhA K fx vals1 sr00 R0 M1 model0 A A1 HLH HL1 WV W48 W70 W73 W79 V81 HR0);
          [ vm_compute; reflexivity | reflexivity | reflexivity | cbn [nth sr00 edenot]; rewrite HCALLS; reflexivity
          | eapply ksubl_sound; [exact HK1 | vm_compute; reflexivity] | exact HC1 | exact HPL0 | exact DI0 | exact HINC | exact G1 | exact G2 ].
      + (* [comment removed for export] *)
        pose proof (know_TcA vals1 _ 1 32767 0 0 W73 W79 ltac:(apply Z.eqb_neq in ECFG; lia) ltac:(lia) HK1) as HK. clear HK1.
        drv_blockT0 HIok Hsp DL HR HK DI W0 scr0 82%nat.
        1-4: entry_store.      (* [comment removed for export] *)
        lazymatch goal with EQM : mrestrict _ _ = mem_denot _ _ ?log |- _ =>
          destruct (POST _ _ log ltac:(vm_compute; reflexivity) EQM EQH SBM) as (HC1 & _ & G1 & G2) end.
        eapply (pl0_to_lhA K fx vals1 sr10 R0 M1 model0 A A1 HLH HL1 WV W48 W70 W73 W79 V81 HR0);
          [ vm_compute; reflexivity | reflexivity | reflexivity | change (nth 21 sr10 (ELit 0)) with calls_xA; apply Ecx; reflexivity
          | eapply ksubl_sound; [exact HK1 | vm_compute; reflexivity] | exact HC1 | exact HPL0 | exact DI0 | exact HINC | exact G1 | exact G2 ].
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (TAILm : forall srX R' M' (model' : Model),
                 regs_ok (ENVG vals1) srX R' -> sr_upd srX (ridx 21) (EVar 81) = srTm0A ->
                 edenot (ENVG vals1) (nth 21 srX (ELit 0)) = Z_to_bv 64 CALLSA ->
                 know_ok ASEGS (ENVG vals1) (mrestrict (ahid A model') M') knTeA ->
                 rdn ASEGS M' (Z_to_bv 64 A1) (length fdata) = Some fdata ->
                 rdn ASEGS M' (Z_to_bv 64 (A1 + 6 + CFG)) (length payloadA) = Some payloadA ->
                 dinvA [(A1, CAP)] LK0 crC A M' model' -> m_fds model' = fds0 -> m_fs model' = fs0 ->
                 srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 0x79818) M' (seg_rom ASEGS)) model') K).
      2:{ destruct (CFG =? 0) eqn:ECFG.
          - pose proof (know_TcA vals1 _ 0 0 1 67108857 W73 W79 ltac:(apply Z.eqb_eq in ECFG; lia) ltac:(lia) HK1) as HK. clear HK1.
            drv_blockT0 HIok Hsp DL HR HK DI W0 scr0 82%nat.
            1-4: entry_store.      (* [comment removed for export] *)
            lazymatch goal with EQM : mrestrict _ _ = mem_denot _ _ ?log |- _ =>
              destruct (POST _ _ log ltac:(vm_compute; reflexivity) EQM EQH SBM) as (HC1 & HPAY1 & G1 & G2) end.
            apply (TAILm sr01 _ _ _ HR0); [vm_compute; reflexivity | cbn [nth sr01 edenot]; rewrite HCALLS; reflexivity
              | eapply ksubl_sound; [exact HK1 | vm_compute; reflexivity] | exact HC1 | exact HPAY1 | exact DI0 | exact G1 | exact G2].
          - pose proof (know_TcA vals1 _ 1 32767 1 67108857 W73 W79 ltac:(apply Z.eqb_neq in ECFG; lia) ltac:(lia) HK1) as HK. clear HK1.
            drv_blockT0 HIok Hsp DL HR HK DI W0 scr0 82%nat.
            1-4: entry_store.      (* [comment removed for export] *)
            lazymatch goal with EQM : mrestrict _ _ = mem_denot _ _ ?log |- _ =>
              destruct (POST _ _ log ltac:(vm_compute; reflexivity) EQM EQH SBM) as (HC1 & HPAY1 & G1 & G2) end.
            apply (TAILm sr11 _ _ _ HR0); [vm_compute; reflexivity | change (nth 21 sr11 (ELit 0)) with calls_xA; apply Ecx; reflexivity
              | eapply ksubl_sound; [exact HK1 | vm_compute; reflexivity] | exact HC1 | exact HPAY1 | exact DI0 | exact G1 | exact G2]. }
      clear POST HC HPAY0 HK1 HR DI F1 F2. clear M model R.
      intros srX R M model HR1 HsrX H20 HK HC1 HPAY1 DI G1 G2.
      assert (HR2 : regs_ok (ENVG vals1) srTm0A R).
      { rewrite <- HsrX. apply regs_ok_upd_sameA; [exact HR1 | discriminate |].
        rewrite (HR1 (21%bv : reg)). change (sr_get srX (21%bv : reg)) with (nth 21 srX (ELit 0)). rewrite H20.
        cbn [edenot ev ENVA]. exact V81. }
      clear HR1 HsrX H20.
      (* [comment removed for export] *)
      eapply (amalloc_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals1 _ srTm0A knTeA R M model [(A1, CAP)] LK0 crC A PL TSO
                [(48%nat, 65536)] [] 0xa7e38 K);
        [ exact HR2 | exact HK
        | rewrite HL1; vm_compute; reflexivity | rewrite HL1; vm_compute; reflexivity | rewrite HL1; lia
        | exact W0 | vm_compute; reflexivity
        | regv HR2 (2%bv : reg); cbn [edenot ev ENVA]; rewrite W0; apply alu_add_w_litA
        | unfold TSO; lia | reflexivity
        | regv HR2 (10%bv : reg); cbn [edenot ev ENVA]; exact W79
        | lia
        | apply Hcr1; lia
        | regv HR2 (4%bv : reg); reflexivity
        | regv HR2 (1%bv : reg); reflexivity
        | lia | reflexivity
        | exact DI
        | intros i nb Hf; cbn in Hf;
          destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL1; lia|];
                                           rewrite W48, u_small by lia; exists CAP; split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
        | intros v b Hf; discriminate
        | exact HK0 | ].
      intros R' M' model' A' u vals' E' HL' HA2 HR' HK' DI' HRT HINC' HBR2 HAP HSHB HAB HBLK HIMG. subst vals' E'.
      set (vals2 := vals1 ++ junk_vals R') in *.
      change (Env (vals_ev vals2) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals2) in HR', HK'.
      rewrite HL1 in HL', HA2, HR', HK'. change (82 + 10)%nat with 92%nat in HA2, HK'. change (82 + 32)%nat with 114%nat in HL'.
      destruct (model_rt_fds _ _ HRT) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
      pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U3). pose proof HBR2 as (_ & _ & U4 & _ & _).
      assert (NEQ : u <> A1).
      { specialize (HAP (A1, CAP) ltac:(left; reflexivity)). cbn [fst snd] in HAP. lia. }
      assert (X0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact W0).
      assert (XV : hdr_valsA sp0 p0 p1 can vals2) by (subst vals2; apply (hdr_appA sp0 fdata); [exact WV | rewrite HL1; lia]).
      assert (X48 : vals_ev vals2 48 = Z_to_bv 64 A1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact W48).
      assert (X73 : vals_ev vals2 73 = Z_to_bv 64 CFG) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact W73).
      assert (X79 : vals_ev vals2 79 = Z_to_bv 64 PL) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact W79).
      (* [comment removed for export] *)
      apply Forall_app in HK' as [HKB HK'].
      assert (HKU : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A' model') M') knU0A).
      { change knU0A with (kn_blk2A 92 ++ knTkA). apply Forall_app. split.
        - unfold kn_blk2A. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [kentry_ok edenot ev ENVA]; rewrite HA2, u_small by lia; lia.
        - exact HK'. }
      clear HK' HKB HK HR2.
      (* [comment removed for export] *)
      assert (HC2 : rdn ASEGS M' (Z_to_bv 64 A1) (length fdata) = Some fdata).
      { rewrite <- HC1. apply rdn_agree. intros k Hk. rewrite u_small by lia. apply HBLK; [lia|].
        exists (A1, CAP). split; [left; reflexivity|]. cbn [fst snd]. lia. }
      assert (HPAY2 : rdn ASEGS M' (Z_to_bv 64 (A1 + 6 + CFG)) (length payloadA) = Some payloadA).
      { rewrite <- HPAY1. apply rdn_agree. intros k Hk. rewrite payloadA_len in Hk. rewrite u_small by lia. apply HBLK; [lia|].
        exists (A1, CAP). split; [left; reflexivity|]. cbn [fst snd]. lia. }
      clear HC1 HPAY1 DI HBLK HIMG HAB G1 G2 HRT. clear M model R.
      (* [comment removed for export] *)
      drv_blockT0 HIok Hsp DL HR' HKU DI' X0 scr0 114%nat.
      pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
      destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
      assert (HC3 : rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata).
      { rewrite <- HC2. apply rdn_agree. intros j Hj. apply EQA. }
      assert (HPAY3 : rdn ASEGS M (Z_to_bv 64 (A1 + 6 + CFG)) (Z.to_nat PL) = Some payloadA).
      { rewrite <- payloadA_len, <- HPAY2. apply rdn_agree. intros j Hj. apply EQA. }
      clear EQM EQH EQA SBM HR' HKU DI' HC2 HPAY2 F1 F2 HSHB. clear M' model'.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ => lazymatch type of HK with know_ok _ _ _ ?kn =>
      eapply (amemcpy_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def ICok vals2 _ sr kn R M model [(u, PL); (A1, CAP)] LK0
                (adebit L crC PL) A' u PL u (A1 + 6 + CFG) PL payloadA TSO [(48%nat, 65536)] [] 0xa7e4c K) end end;
        [ exact HR | exact HK
        | rewrite HL'; vm_compute; reflexivity | rewrite HL'; vm_compute; reflexivity | rewrite HL'; lia
        | exact X0 | vm_compute; reflexivity
        | regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite X0; apply alu_add_w_litA
        | unfold TSO; lia | reflexivity
        | regv HR (10%bv : reg); cbn [edenot ev ENVA]; exact HA2
        | regv HR (11%bv : reg); cbn [edenot ev ENVA]; rewrite X48, X73, !alu_add_Z; f_equal; lia
        | regv HR (12%bv : reg); cbn [edenot ev ENVA]; exact X79
        | lia
        | regv HR (4%bv : reg); reflexivity
        | regv HR (1%bv : reg); reflexivity
        | lia | reflexivity
        | exact DI
        | left; reflexivity | lia | lia
        | apply (src_blk_aacc scfg L ar C HI HIok sp0 Hsp _ _ _ _ _ _ _ A1 CAP (A1 + 6 + CFG) PL (di_inv _ _ _ _ _ _ _ _ _ _ DI)); [right; left; reflexivity | lia | lia]
        | lia | lia
        | apply (src_blk_app_rng scfg L ar C HI HIok sp0 Hsp _ _ _ _ _ _ _ A1 CAP (A1 + 6 + CFG) PL (di_inv _ _ _ _ _ _ _ _ _ _ DI)); [right; left; reflexivity | lia | lia]
        | intros i Hi; right; exists (A1, CAP); split; [right; left; reflexivity | cbn [fst snd]; lia]
        | exact HPAY3
        | specialize (HAP (A1, CAP) ltac:(left; reflexivity)); cbn [fst snd] in HAP; lia
        | intros i nb Hf; cbn in Hf;
          destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL'; lia|];
                                           rewrite X48, u_small by lia; rewrite lb_remove_hdA; exists CAP; split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
        | intros v b Hf; discriminate
        | exact HK0
        | ].
      intros R3 M3 model3 vals' E' HL3 HR3 HK3 DI3 HRT3 HDST HBLK3 HIMG3. subst vals' E'.
      rewrite HL' in HL3, HR3. change (114 + 32)%nat with 146%nat in HL3.
      change (sr_after_call_j _ (map ridx c_kept) 114) with srV0A in HR3.
      change (keep_allocA TSO 4096 [(48%nat, 65536)] [] _) with knV0A in HK3.
      destruct (model_rt_fds _ _ HRT3) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
      set (vals3 := vals2 ++ junk_vals R3) in *.
      change (Env (vals_ev vals3) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals3) in HR3, HK3.
      assert (Y0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X0).
      assert (YV : hdr_valsA sp0 p0 p1 can vals3) by (subst vals3; apply (hdr_appA sp0 fdata); [exact XV | rewrite HL'; lia]).
      assert (Y92 : vals_ev vals3 92 = Z_to_bv 64 u) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact HA2).
      assert (YL : forall j, (j < 82)%nat -> vals_ev vals3 j = vals_ev vals1 j).
      { intros j Hj. subst vals3 vals2. rewrite !vals_ev_app_l by (rewrite ?length_app, ?junk_vals_length, HL1; lia). reflexivity. }
      assert (HC4 : rdn ASEGS M3 (Z_to_bv 64 A1) (length fdata) = Some fdata).
      { rewrite <- HC3. apply rdn_agree. intros k Hk. rewrite u_small by lia. apply HBLK3; [lia | | ].
        - exists (A1, CAP). split; [right; left; reflexivity|]. cbn [fst snd]. lia.
        - specialize (HAP (A1, CAP) ltac:(left; reflexivity)). cbn [fst snd] in HAP. lia. }
      clear HR HK DI HC3 HPAY3 HBLK3 HIMG3 G1 G2 HRT3. clear M model R.
      (* [comment removed for export] *)
      drv_blockT0 HIok Hsp DL HR3 HK3 DI3 Y0 scr0 146%nat.
      pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
      destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
      assert (HC5 : rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata).
      { rewrite <- HC4. apply rdn_agree. intros j Hj. apply EQA. }
      assert (HPAY5 : rdn ASEGS M (Z_to_bv 64 u) (length payloadA) = Some payloadA).
      { rewrite payloadA_len, <- HDST. apply rdn_agree. intros j Hj. apply EQA. }
      (* [comment removed for export] *)
      set (valsL := relayA vals3 R (Z_to_bv 64 0)).
      apply (HLH fx valsL R M model A' A1 u u [(u, PL); (A1, CAP)]).
      + unfold lh_valsA, hdr_valsA in *. subst valsL. rewrite (relayA_len vals3 R _ ltac:(lia)), relayA_81 by lia.
        rewrite !(relayA_lo vals3 R _) by lia. rewrite !YL by lia.
        repeat split; try tauto; try assumption.
        * unfold relayA. change 82%nat with (81 + 1)%nat. rewrite vals_hiA by lia. cbn [nth lay_extA].
          regv HR (9%bv : reg). cbn [edenot ev ENVA]. exact Y92.
        * unfold relayA. change 83%nat with (81 + 2)%nat. rewrite vals_hiA by lia. cbn [nth lay_extA].
          regv HR (18%bv : reg). cbn [edenot ev ENVA]. exact Y92.
      + subst valsL. eapply (relayA_regs _ vals3 _ R _ ltac:(lia)); [|exact HR]. vm_compute; reflexivity.
      + subst valsL. eapply (know_ok_agree ASEGS 82); [apply relayA_agree; lia | vm_compute; reflexivity |].
        eapply ksubl_sound; [exact HK | vm_compute; reflexivity].
      + split; [exact HBR|]. right. split; [lia|]. split; [reflexivity|]. split; [exact HBR2|]. split; [exact HAP | reflexivity].
      + exact HC5.
      + exact HPAY5.
      + unfold cr1A. replace (PL =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exact DI.
      + intros x Hx. apply HINC'. apply HINC. exact Hx.
      + exact G1.
      + exact G2.
  Qed.

End DrvD.
End FPX_1.
