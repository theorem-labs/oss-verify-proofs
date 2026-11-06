(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  RefNodes RefPrintfLib HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm9IcptLayout PmIcptDrvA LibIface PmLibIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Pm9DrvEntry Pm9Drv_defs Pm9DrvLib Pm9DrvRead Pm9DrvA
  Pm9DrvG_defs Pm9DrvG Pm9DrvC_defs Pm9DrvC Pm9DrvD_defs Pm9DrvLibL Pm9DrvD Pm9DrvE_defs Pm9DrvStdio Pm9DrvPrintfK Pm9DrvPrintf1 Pm9DrvExit HeapIfaceANull Pm9DrvFreeNull.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import ShapeLaws AgentLib Spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition relayE (vals : list word) (R : bvmap 5 word) (W : word) : list word := firstn 81 vals ++ (getr R 21 :: tl (lay_extA vals R W)).
Definition shared_posE : list nat := [2; 3; 4; 8; 20; 22; 23; 24; 25; 26; 27]%nat.
Definition relay_ok_bE (sr : list expr) : bool :=
  forallb (fun i => expr_eqb (nth i sr (ELit 0)) (nth i srLHA (ELit 0)) && expr_vars_lt 81 (nth i sr (ELit 0))) shared_posE.

Lemma relayE_len : forall vals R W, (81 <= length vals)%nat -> length (relayE vals R W) = 102%nat.
Proof. intros. unfold relayE. rewrite len_layA by lia. reflexivity. Qed.
Lemma relayE_lo : forall vals R W j, (81 <= length vals)%nat -> (j < 81)%nat -> vals_ev (relayE vals R W) j = vals_ev vals j.
Proof. intros. unfold relayE. apply vals_loA; lia. Qed.
Lemma relayE_hi : forall vals R W i, (81 <= length vals)%nat -> vals_ev (relayE vals R W) (81 + i) = nth i (getr R 21 :: tl (lay_extA vals R W)) (Z_to_bv 64 0).
Proof. intros. unfold relayE. apply vals_hiA. lia. Qed.
Lemma relayE_agree : forall ebs vals R W, (81 <= length vals)%nat -> env_agree 81 (Env (vals_ev vals) ebs) (Env (vals_ev (relayE vals R W)) ebs).
Proof. intros ebs vals R W HL. split; [|reflexivity]. intros n Hn. cbn [ev]. symmetry. apply relayE_lo; lia. Qed.
Lemma relayE_regs : forall ebs vals sr R W,
  (81 <= length vals)%nat -> relay_ok_bE sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R ->
  regs_ok (Env (vals_ev (relayE vals R W)) ebs) srLHA R.
Proof.
  intros ebs vals sr R W HL Hokb HR.
  unfold relay_ok_bE in Hokb. rewrite forallb_forall in Hokb.
  assert (SH : forall i, In i shared_posE -> getr R (Z_to_bv 5 (Z.of_nat i)) = edenot (Env (vals_ev (relayE vals R W)) ebs) (nth i srLHA (ELit 0))).
  { intros i Hi. pose proof (Hokb i Hi) as H. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1.
    rewrite <- H1. rewrite <- (edenot_agree 81 _ _ _ (relayE_agree ebs vals R W HL) H2).
    assert (Hi32 : (0 < i < 32)%nat) by (unfold shared_posE in Hi; cbn in Hi; lia).
    rewrite (HR (Z_to_bv 5 (Z.of_nat i))), sr_get_natA by exact Hi32. reflexivity. }
  apply regs_ok_by_nth. intros i Hi.
  assert (JK : forall r k, nth r srLHA (ELit 0) = EVar (81 + k) -> nth k (getr R 21 :: tl (lay_extA vals R W)) (Z_to_bv 64 0) = getr R (Z_to_bv 5 (Z.of_nat r)) ->
               getr R (Z_to_bv 5 (Z.of_nat r)) = edenot (Env (vals_ev (relayE vals R W)) ebs) (nth r srLHA (ELit 0))).
  { intros r k Hr Hk. rewrite Hr. cbn [edenot ev]. rewrite relayE_hi by lia. symmetry. exact Hk. }
  do 32 (destruct i as [|i]; [first [lia | apply SH; cbn; tauto | eapply JK; reflexivity] |]). lia.
Qed.

Section Pf1Keep.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Lemma regions_pf1A : forall vals ebs so bls,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 -> - 2 ^ 22 <= so <= 0 ->
    (forall i nb, find_nz i bls = Some nb -> hzA sp0 (bv_unsigned (vals_ev vals i)) nb) ->
    regions_ok ASEGS 0 so 3232 bls [] [] IMG_PF_A IMG_RW_A E (fun a => ~ Wpf1 (bv_unsigned sp0 + so) a) (fun a => bv_unsigned sp0 + so - 3232 <= a < bv_unsigned sp0 + so).
  Proof.
    intros vals ebs so bls E P0 Hso Hbl. pose proof Hsp as Hsp'.
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold Wpf1, SOBUF. lia.
    - intros z Hz. right. lia.
    - intros i nb Hf. destruct (Hbl i nb Hf) as (Z1 & Z2 & Z3). split; [lia|]. intros z Hz. unfold Wpf1, SOBUF. lia.
    - intros v b Hf. discriminate.
    - intros i [].
    - intros lo hi Hin. unfold IMG_PF_A in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; (split; [lia|]; split; [lia|]; intros a Ha; unfold Wpf1, SOBUF; lia)|]). destruct Hin.
    - intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
      intros Mx d m Hd Hm.
      apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x680350) (Z_to_bv 64 d) 65536%nat m 0x680350 0x690350);
        first [exact (wseg_stage) | reflexivity | lia | (rewrite u_small by lia; lia)].
  Qed.
End Pf1Keep.

Definition XKN_R : list kentry :=
  [KWord (SA (ELit 0) 7020544) 4 (ELit 0); KWord (SA (ELit 0) 7021976) 8 (ELit 0);
   KWord (SA (ELit 0) 6888680) 4 (EVar 4); KRange (EVar 4) 1 4194303; KImg 0x158d28 0x158e18; KImg 0x158f00 0x15a640;
   KWord (SA (ELit 0) 6882132) 1 (ELit 0)].

Definition XKN : list kentry :=
  map (fun c : Z * nat * Z => KWord (SA (ELit 0) (fst (fst c))) (snd (fst c)) (ELit (snd c))) XC9_CELLS
  ++ [KWord (SA (ELit 0) 6888680) 4 (EVar 4); KRange (EVar 4) 1 4194303; KImg 0x158d28 0x158e18; KImg 0x158f00 0x15a640].

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvE.
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
  Hypothesis Hex : incl EX_CELLS (asc_cells C).
  Hypothesis FNULL : afree_null_spec L ar scfg HI.

  Variable LSA : ls_state LSt -> list (Z * Z).
  Hypothesis DLL : drv_lib_layoutA Lay L.
  Hypothesis LEX : lib_exit_factsA Lay LSt LSA.
  Hypothesis LSX : forall g, LSA g = [] \/ LSA g = LS2_HANDLERS \/ LSA g = LS2C_HANDLERS \/ LSA g = LS2JC_HANDLERS \/ LSA g = LS2CJ_HANDLERS.

  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation ENVG := (ENVA fdata).
  Let LEN : Z := Z.of_nat (length fdata).
  Let CFG : Z := CFGA fdata.
  Let PL : Z := PLA fdata.
  #[local] Notation payloadA := (Pm9DrvD.payloadA fdata).
  #[local] Notation blk_factsA := (Pm9DrvD.blk_factsA L ar fdata CAP).

  Definition e_valsA (n : nat) (vals : list word) (A1 PTR OWN k : Z) : Prop :=
    length vals = n /\ hdr_valsA sp0 p0 p1 can vals
    /\ vals_ev vals 48 = Z_to_bv 64 A1 /\ vals_ev vals 70 = Z_to_bv 64 LEN
    /\ vals_ev vals 73 = Z_to_bv 64 CFG /\ vals_ev vals 79 = Z_to_bv 64 PL
    /\ vals_ev vals 81 = Z_to_bv 64 k /\ vals_ev vals 82 = Z_to_bv 64 PTR /\ vals_ev vals 83 = Z_to_bv 64 OWN.

  Definition credit_scaleA (k : Z) (c : credit) : credit := (k * fst c, k * snd c).
  Definition lib_roomA (kc : Z) (LK : list fframe) (cr : credit) : Prop :=
    credit_le (credit_scaleA kc (lla_credit Lay PL)) cr
    /\ (forall c, In c PM_FS_CLASSES -> Z.of_nat (ff_count c LK) + kc * lla_leak Lay c + lla_frames Lay c <= ff_cap c).

  Definition e_factsA (kc j : Z) (A1 PTR OWN : Z) (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (g : ls_state LSt) A M (model : Model) : Prop :=
    blk_factsA A1 PTR OWN LB
    /\ rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata
    /\ rdn ASEGS M (Z_to_bv 64 PTR) (length payloadA) = Some payloadA
    /\ dinvA LB LK cr A M model /\ incl A0 A
    /\ m_fds model = fds0 /\ m_fs model = fs0
    /\ stdoutA j (mrestrict (ahid A model) M) /\ stdoutXA (mrestrict (ahid A model) M)
    /\ ls_ok LSt g M /\ lib_roomA kc LK cr.

  Definition SSPA (k j : Z) (K : TSet) : Prop :=
    forall (fx' : PropExec.FPState) vals R M (model : Model) A (A1 PTR OWN : Z) LB LK cr g,
      e_valsA 166 vals A1 PTR OWN k -> 1 <= k -> 0 <= j -> j + k <= 4 ->
      regs_ok (ENVG vals) srQ0A R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knLH2A ->
      e_factsA (k - 1) j A1 PTR OWN LB LK cr g A M model ->
      PmLibIfaceA.fp_ok fx' ->
      srealizes ASEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0xaf538) M (seg_rom ASEGS)) model) K.

  Definition LH2PA (k j : Z) (K : TSet) : Prop :=
    forall (fx' : PropExec.FPState) vals R M (model : Model) A (A1 PTR OWN : Z) LB LK cr g,
      e_valsA 102 vals A1 PTR OWN k -> 1 <= k -> 0 <= j -> j + k <= 3 ->
      regs_ok (ENVG vals) srLHA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knLH2A ->
      e_factsA k j A1 PTR OWN LB LK cr g A M model ->
      PmLibIfaceA.fp_ok fx' ->
      srealizes ASEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0xaf42c) M (seg_rom ASEGS)) model) K.

  Definition dec_xA : expr := EAluw ALU_ADD (EVar 81) (ELit (-1)).
  Lemma dec_valA : forall vals k, vals_ev vals 81 = Z_to_bv 64 k -> 1 <= k <= 4 -> edenot (ENVG vals) dec_xA = Z_to_bv 64 (k - 1).
  Proof.
    intros vals k P81 Hk. unfold dec_xA. cbn [edenot ev ENVA]. rewrite P81.
    assert (k = 1 \/ k = 2 \/ k = 3 \/ k = 4) as [-> |[-> |[-> | ->]]] by lia; vm_compute; reflexivity.
  Qed.
  Lemma dec_scA : forall vals M k t, vals_ev vals 81 = Z_to_bv 64 k -> 1 <= k <= 4 -> negb (Z.eqb (k - 1) 0) = t ->
    sc_denot ASEGS M (ENVG vals) (SCBr t BC_NE dec_xA (ELit 0)).
  Proof.
    intros vals M k t P81 Hk Ht. cbn [sc_denot branch_taken]. rewrite (dec_valA vals k P81 Hk). cbn [edenot].
    unfold bv_eqb. rewrite !u_small by lia. exact Ht.
  Qed.

  Lemma step_SA : forall k j K, 2 <= k -> LH2PA (k - 1) j K -> SSPA k j K.
  Proof.
    intros k j K Hk2 HLH. unfold SSPA.
    intros fx' vals R M model A A1 PTR OWN LB LK cr g (HL & HV & P48 & P70 & P73 & P79 & P81 & P82 & P83) Hk Hj Hjk HR HK
           (HBLK & HC & HPAY & DI & HINC & F1 & F2 & SO & SOX & HLS & HROOM).
    intros HFP.
    pose proof HV as (P0 & _).
    drv_blockT0 HIok Hsp DL HR HK DI P0 (SCR [true] [] []) 166%nat.
    { apply (dec_scA vals _ k true P81); [lia | apply Bool.negb_true_iff; apply Z.eqb_neq; lia]. }
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
    pose proof (ahid_sbm A model model0 SBM) as AH.
    assert (V81 : getr R0 21%bv = Z_to_bv 64 (k - 1)).
    { regv HR0 (21%bv : reg). change (sr_get srSt2A (21%bv : reg)) with dec_xA. apply (dec_valA vals k P81). lia. }
    set (valsL := relayE vals R0 (Z_to_bv 64 0)).
    apply (HLH fx' valsL R0 M model0 A A1 PTR OWN LB LK cr g).
    - unfold e_valsA, hdr_valsA in *. subst valsL. rewrite (relayE_len vals R0 _ ltac:(lia)).
      rewrite !(relayE_lo vals R0 _) by lia.
      repeat split; try tauto; try assumption.
      + change 81%nat with (81 + 0)%nat. rewrite relayE_hi by lia. exact V81.
      + change 82%nat with (81 + 1)%nat. rewrite relayE_hi by lia. cbn [nth tl lay_extA]. regv HR0 (9%bv : reg). cbn [edenot ev ENVA]. exact P82.
      + change 83%nat with (81 + 2)%nat. rewrite relayE_hi by lia. cbn [nth tl lay_extA]. regv HR0 (18%bv : reg). cbn [edenot ev ENVA]. exact P83.
    - lia.
    - exact Hj.
    - lia.
    - subst valsL. eapply (relayE_regs _ vals _ R0 _ ltac:(lia)); [|exact HR0]. vm_compute; reflexivity.
    - subst valsL. eapply (know_ok_agree ASEGS 81); [apply relayE_agree; lia | vm_compute; reflexivity |].
      exact HK0.
    - unfold e_factsA. rewrite AH. exact (conj HBLK (conj HC (conj HPAY (conj DI0 (conj HINC (conj G1 (conj G2 (conj SO (conj SOX (conj HLS HROOM)))))))))).
    - exact HFP.
  Qed.

  Definition EA (j : nat) : TSet := t_emit (W 1 (zero_lines j)) (t_exit (exit_code 0) fs0).

  Lemma exitf_of_kn : forall vals (MV : word -> option byte) kn,
    know_ok ASEGS (ENVG vals) MV kn -> forallb (fun K => existsb (kentry_eqb K) kn) XKN = true ->
    exitA (bv_unsigned (vals_ev vals 4)) MV.
  Proof.
    intros vals MV kn HK HB. rewrite forallb_forall in HB.
    assert (KB : forall K, In K XKN -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (HB K HKin)).
    pose proof (kimg_clear (ENVG vals) MV kn 0x158d28 0x158e18 HK (KB (KImg 0x158d28 0x158e18) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLa.
    pose proof (kimg_clear (ENVG vals) MV kn 0x158f00 0x15a640 HK (KB (KImg 0x158f00 0x15a640) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLb.
    assert (ICa : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x158d28 <=? a) && (a + Z.of_nat n <=? 0x158e18) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLa. lia. }
    assert (ICb : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x158f00 <=? a) && (a + Z.of_nat n <=? 0x15a640) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLb. lia. }
    unfold exitA. split; [|split; [|split]].
    - unfold cells_at, XC_CELLS.
      constructor; [exact (kword_lit sp0 _ MV kn 7020544 4%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 7020544) 4 (ELit 0)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 7020579 1%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 7020579) 1 (ELit 0)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 7020016 8%nat (ELit 7020024) HK (KB (KWord (SA (ELit 0) 7020016) 8 (ELit 7020024)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 7020008 4%nat (ELit 1) HK (KB (KWord (SA (ELit 0) 7020008) 4 (ELit 1)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 7020032 8%nat (ELit 1266496) HK (KB (KWord (SA (ELit 0) 7020032) 8 (ELit 1266496)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 7020288 8%nat (ELit 649988) HK (KB (KWord (SA (ELit 0) 7020288) 8 (ELit 649988)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 7020004 4%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 7020004) 4 (ELit 0)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 7020024 8%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 7020024) 8 (ELit 0)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 7021976 8%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 7021976) 8 (ELit 0)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (ICb 1413104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1412872)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1413012 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1412912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1412928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1412880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1412888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1412864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1412632)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1412624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1412392)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1412532 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1412432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1412448 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1412400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1412408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor.
    - rewrite Z_to_bv_bv_unsigned. exact (kword_lit sp0 _ MV kn 6888680 4%nat (EVar 4) HK (KB (KWord (SA (ELit 0) 6888680) 4 (EVar 4)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)).
    - pose proof (KB (KRange (EVar 4) 1 4194303) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) as Hb.
      apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
      pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok edenot ev ENVA] in X. exact X.
    - intros i Hi. apply CLb. lia.
  Qed.

  Lemma exitr_of_kn : forall vals (MV : word -> option byte) kn,
    know_ok ASEGS (ENVG vals) MV kn -> forallb (fun K => existsb (kentry_eqb K) kn) XKN_R = true ->
    exitR (bv_unsigned (vals_ev vals 4)) MV.
  Proof.
    intros vals MV kn HK HB. rewrite forallb_forall in HB.
    assert (KB : forall K, In K XKN_R -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (HB K HKin)).
    pose proof (kimg_clear (ENVG vals) MV kn 0x158d28 0x158e18 HK (KB (KImg 0x158d28 0x158e18) ltac:(unfold XKN_R; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLa.
    pose proof (kimg_clear (ENVG vals) MV kn 0x158f00 0x15a640 HK (KB (KImg 0x158f00 0x15a640) ltac:(unfold XKN_R; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLb.
    assert (ICa : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x158d28 <=? a) && (a + Z.of_nat n <=? 0x158e18) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLa. lia. }
    assert (ICb : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x158f00 <=? a) && (a + Z.of_nat n <=? 0x15a640) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLb. lia. }
    unfold exitR. split; [|split; [|split]].
    - unfold cells_at, XC_REST.
      constructor; [exact (kword_lit sp0 _ MV kn 7020544 4%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 7020544) 4 (ELit 0)) ltac:(unfold XKN_R; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 7021976 8%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 7021976) 8 (ELit 0)) ltac:(unfold XKN_R; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (ICb 1413104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1412872)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1413012 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1412912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1412928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1412880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1412888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1412864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1412632)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1412624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1412392)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1412532 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1412432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1412448 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1412400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1412408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (kword_lit sp0 _ MV kn 6882132 1%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6882132) 1 (ELit 0)) ltac:(unfold XKN_R; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor.
    - rewrite Z_to_bv_bv_unsigned. exact (kword_lit sp0 _ MV kn 6888680 4%nat (EVar 4) HK (KB (KWord (SA (ELit 0) 6888680) 4 (EVar 4)) ltac:(unfold XKN_R; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)).
    - pose proof (KB (KRange (EVar 4) 1 4194303) ltac:(unfold XKN_R; cbn [In map XC9_CELLS app fst snd]; tauto)) as Hb.
      apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
      pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok edenot ev ENVA] in X. exact X.
    - intros i Hi. apply CLb. lia.
  Qed.
  Lemma EXITR : forall vals LB LK cr A M (model : Model),
    know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) (kn_after rT3A knF2A) -> dinvA LB LK cr A M model ->
    exitR (bv_unsigned (vals_ev vals 4)) (mrestrict (ahid A model) M).
  Proof. intros vals LB LK cr A M model HK _. exact (exitr_of_kn vals _ _ HK ltac:(vm_compute; reflexivity)). Qed.

  Lemma fds0_lookup1 : fd_lookup fds0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
  Proof. vmc_refl. Qed.

  Lemma tail_FA : forall (fx' : PropExec.FPState) (j : nat) (ls2 : xtag) vals R M (model : Model) A LK cr,
    length vals = 230%nat -> hdr_valsA sp0 p0 p1 can vals -> (j <= 3)%nat ->
    regs_ok (ENVG vals) srF2A R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knF2A ->
    dinvA [] LK cr A M model -> m_fds model = fds0 -> m_fs model = fs0 ->
    stdoutA (Z.of_nat j) (mrestrict (ahid A model) M) -> stdoutXA (mrestrict (ahid A model) M) ->
    cells_at M (ATX ls2) ->
    srealizes ASEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0xaf2a0) M (seg_rom ASEGS)) model) (EA j).
  Proof.
    intros fx' j ls2 vals R M model A LK cr HL HV Hj HR HK DI F1 F2 SO SOX HATX.
    pose proof HV as (P0 & _ & _ & P3). pose proof Hsp as Hsp'.
    drv_block0 HIok Hsp DL HR HK DI P0 scr0 230%nat.
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
    pose proof (ahid_sbm A model model0 SBM) as AH. rewrite <- AH in SO, SOX.
    set (MV := mrestrict (ahid A model0) M) in *.
    set (S := bv_unsigned sp0 - 48).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (HS16 : S mod 16 = 0) by (unfold S; clear - Hal; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

    assert (XR : exitR (bv_unsigned (vals_ev vals 4)) MV) by exact (EXITR vals [] LK cr A M model0 HK0 DI0).
    assert (XT : cells_at MV (ATX ls2)) by exact (atx_vis scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ ls2 DI0 HATX).
    assert (XPC : dinvA [] LK cr A M model0 /\ bv_unsigned sp0 - 4096 <= S /\ S <= bv_unsigned sp0 /\ S mod 16 = 0
                  /\ (forall a n, bv_unsigned sp0 - 8388608 <= a -> a + n <= bv_unsigned sp0 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
                  /\ (forall i, 65536 <= i < 1400832 -> MV (Z_to_bv 64 i) = None)).
    { split; [exact DI0|]. split; [unfold S; lia|]. split; [unfold S; lia|].
      split; [exact HS16|].
      split; [intros a n Ha Hn d k Hd Hk; exact (stk_wr sp0 Hsp vals _ MV _ a n HK0 ltac:(vm_compute; reflexivity) P0 Ha Hn d k Hd Hk)|].
      exact (kimg_clear _ MV _ 65536 1400832 HK0 ltac:(vm_compute; reflexivity)). }
    destruct XPC as (XP1 & XP2 & XP3 & XP4 & XP5 & XP6).
    assert (G1r : getr R0 1%bv = Z_to_bv 64 1264592) by (regv HR0 (1%bv : reg); reflexivity).
    assert (G2r : getr R0 2%bv = Z_to_bv 64 S).
    { regv HR0 (2%bv : reg). cbn [edenot ev ENVA]. rewrite P0. unfold S. apply alu_add_w_litA. }
    assert (G4r : getr R0 4%bv = Z_to_bv 64 6888848) by (regv HR0 (4%bv : reg); reflexivity).
    assert (G10r : getr R0 10%bv = Z_to_bv 64 0) by (regv HR0 (10%bv : reg); reflexivity).
    assert (FD1 : fd_lookup (m_fds model0) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) by (rewrite G1; exact fds0_lookup1).
    assert (CANc : rdn ASEGS MV (Z_to_bv 64 7019984) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned can)))).
    { rewrite Z_to_bv_bv_unsigned, <- P3. exact (kword_lit sp0 _ MV _ 7019984 8%nat (EVar 3) HK0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)). }
    unfold EA, exit_code. rewrite <- G2.
    destruct ls2.
    -
      assert (XP : exit_preT ar HI sp0 M0 [] LK cr A M model0 S (bv_unsigned (vals_ev vals 4))) by exact (conj XP1 (conj XP2 (conj XP3 (conj XP4 (conj XP5 (conj XP6 (exitT_of_R _ _ XR XT))))))).
      destruct j as [|[|[|[|j]]]]; [| | | | lia].
      * eapply srz_conseq; [|apply t_eq_sym; apply t_emit_W_nil; apply t_exit_has_nil].
        exact (exit_run_0 scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ XP ltac:(lia) G1r G2r G4r G10r SO SOX).
      * exact (exit_run_2 scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      * exact (exit_run_3 scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      * exact (exit_run_4 scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
    -
      assert (XP : exit_preL ar HI sp0 M0 [] LK cr A M model0 S (bv_unsigned (vals_ev vals 4))) by exact (conj XP1 (conj XP2 (conj XP3 (conj XP4 (conj XP5 (conj XP6 (exitL_of_R _ _ XR XT))))))).
      destruct j as [|[|[|[|j]]]]; [| | | | lia].
      * eapply srz_conseq; [|apply t_eq_sym; apply t_emit_W_nil; apply t_exit_has_nil].
        exact (exit_run_0L scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ XP ltac:(lia) G1r G2r G4r G10r SO SOX).
      * exact (exit_run_2L scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      * exact (exit_run_3L scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      * exact (exit_run_4L scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
    -
      assert (XP : exit_preC ar HI sp0 M0 [] LK cr A M model0 S (bv_unsigned (vals_ev vals 4))) by exact (conj XP1 (conj XP2 (conj XP3 (conj XP4 (conj XP5 (conj XP6 (exitC_of_R _ _ XR XT))))))).
      destruct j as [|[|[|[|j]]]]; [| | | | lia].
      * eapply srz_conseq; [|apply t_eq_sym; apply t_emit_W_nil; apply t_exit_has_nil].
        exact (exit_run_0C scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ XP ltac:(lia) G1r G2r G4r G10r SO SOX).
      * exact (exit_run_2C scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      * exact (exit_run_3C scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      * exact (exit_run_4C scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
    -
      assert (XP : exit_preJC ar HI sp0 M0 [] LK cr A M model0 S (bv_unsigned (vals_ev vals 4))) by exact (conj XP1 (conj XP2 (conj XP3 (conj XP4 (conj XP5 (conj XP6 (exitJC_of_R _ _ XR XT))))))).
      destruct j as [|[|[|[|j]]]]; [| | | | lia].
      * eapply srz_conseq; [|apply t_eq_sym; apply t_emit_W_nil; apply t_exit_has_nil].
        exact (exit_run_0JC scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ XP ltac:(lia) G1r G2r G4r G10r SO SOX).
      * exact (exit_run_2JC scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      * exact (exit_run_3JC scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      * exact (exit_run_4JC scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
    -
      assert (XP : exit_preCJ ar HI sp0 M0 [] LK cr A M model0 S (bv_unsigned (vals_ev vals 4))) by exact (conj XP1 (conj XP2 (conj XP3 (conj XP4 (conj XP5 (conj XP6 (exitCJ_of_R _ _ XR XT))))))).
      destruct j as [|[|[|[|j]]]]; [| | | | lia].
      * eapply srz_conseq; [|apply t_eq_sym; apply t_emit_W_nil; apply t_exit_has_nil].
        exact (exit_run_0CJ scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ XP ltac:(lia) G1r G2r G4r G10r SO SOX).
      * exact (exit_run_2CJ scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      * exact (exit_run_3CJ scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      * exact (exit_run_4CJ scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
  Qed.

  Lemma wseg_sofile : wseg_ok ASEGS (Z_to_bv 64 1412632) 232 = true.  Proof. vmc_refl. Qed.
  Lemma wseg_sobuf : wseg_ok ASEGS (Z_to_bv 64 SOBUF) 1024 = true.  Proof. vmc_refl. Qed.

  Lemma stdout_agree : forall j (MV MV' : word -> option byte), stdoutA j MV -> stdoutXA MV -> 0 <= j <= 500 ->
    (forall a, 1412632 <= a < 1412632 + 232 \/ SOBUF <= a < SOBUF + 1024 -> MV' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
    stdoutA j MV' /\ stdoutXA MV'.
  Proof.
    intros j MV MV' (F1 & F2 & F3 & F4 & F5 & F6 & F7 & FW & BW & BC) (X1 & X2 & X3 & X4 & X5) Hj AG.
    assert (TR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> 1412632 <= a -> a + Z.of_nat n <= 1412632 + 232 -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr H1 H2. apply (rdn_tr MV MV' a n bs Hr); [lia | lia|]. intros i Hi. apply AG. left. lia. }
    assert (TRB : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> SOBUF <= a -> a + Z.of_nat n <= SOBUF + 1024 -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr H1 H2. apply (rdn_tr MV MV' a n bs Hr); [unfold SOBUF in *; lia | unfold SOBUF in *; lia|]. intros i Hi. apply AG. right. lia. }
    split.
    - unfold stdoutA. repeat split; try (apply TR; [assumption | cbn; lia | cbn; lia]).
      + intros a n H1 H2 d k Hd Hk. apply (store_ok_window ASEGS MV' (Z_to_bv 64 1412632) (Z_to_bv 64 (a + d)) 232%nat k 1412632 (1412632 + 232));
          first [exact wseg_sofile | reflexivity | lia | (rewrite u_small by lia; lia)].
      + intros a n H1 H2 d k Hd Hk. apply (store_ok_window ASEGS MV' (Z_to_bv 64 SOBUF) (Z_to_bv 64 (a + d)) 1024%nat k SOBUF (SOBUF + 1024));
          first [exact wseg_sobuf | reflexivity | (unfold SOBUF in *; lia) | (rewrite u_small by (unfold SOBUF in *; lia); unfold SOBUF in *; lia)].
      + destruct (BC i H) as (B1 & _). apply TRB; [exact B1 | lia | cbn; lia].
      + destruct (BC i H) as (_ & B2). apply TRB; [exact B2 | lia | cbn; lia].
    - unfold stdoutXA. repeat split; apply TR; first [assumption | cbn; lia].
  Qed.

  Lemma stdout0_of_kn : forall E (MV : word -> option byte) kn, know_ok ASEGS E MV kn -> existsb (kentry_eqb (KImg 0x158e18 0x158f00)) kn = true -> stdout0A MV.
  Proof.
    intros E MV kn HK Hb. pose proof (kimg_clear E MV kn 0x158e18 0x158f00 HK Hb) as CL.
    assert (IC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x158e18 <=? a) && (a + Z.of_nat n <=? 0x158f00) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CL. lia. }
    unfold stdout0A.
    split; [exact (IC 1412772 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|]. split; [exact (IC 1412632 4%nat (word_to_le_bytes 4 (Z_to_bv 64 5)) ltac:(img_rd) eq_refl)|].
    split; [exact (IC 1412728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1024)) ltac:(img_rd) eq_refl)|]. split; [exact (IC 1412664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
    split; [exact (IC 1412768 4%nat (word_to_le_bytes 4 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|]. split; [exact (IC 1412720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 SOBUF)) ltac:(img_rd) eq_refl)|].
    split; [exact (IC 1412776 4%nat (word_to_le_bytes 4 (Z_to_bv 64 10)) ltac:(img_rd) eq_refl)|]. split; [exact (IC 1412704 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1301116)) ltac:(img_rd) eq_refl)|].
    split; [exact (IC 1412752 4%nat (word_to_le_bytes 4 (Z_to_bv 64 1)) ltac:(img_rd) eq_refl)|].
    split.
    - intros a n H1 H2 d k Hd Hk. apply (store_ok_window ASEGS MV (Z_to_bv 64 1412632) (Z_to_bv 64 (a + d)) 232%nat k 1412632 (1412632 + 232));
        first [exact wseg_sofile | reflexivity | lia | (rewrite u_small by lia; lia)].
    - intros a n H1 H2 d k Hd Hk. apply (store_ok_window ASEGS MV (Z_to_bv 64 SOBUF) (Z_to_bv 64 (a + d)) 1024%nat k SOBUF (SOBUF + 1024));
        first [exact wseg_sobuf | reflexivity | (unfold SOBUF in *; lia) | (rewrite u_small by (unfold SOBUF in *; lia); unfold SOBUF in *; lia)].
  Qed.

  Lemma stdout_call_g : forall (IMG : list (Z * Z)) j LB LK cr A M (model : Model) LB' LK' cr' A' M' (model' : Model),
    In (0x158c38, 0x15a640) IMG -> (exists lo2 hi2, In (lo2, hi2) IMG /\ lo2 <= 0x6b25b0 /\ 0x6b29b0 <= hi2) ->
    dinvA LB LK cr A M model -> dinvA LB' LK' cr' A' M' model' -> 0 <= j <= 500 ->
    (forall lo hi a, In (lo, hi) IMG -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    stdoutA j (mrestrict (ahid A model) M) -> stdoutXA (mrestrict (ahid A model) M) ->
    stdoutA j (mrestrict (ahid A' model') M') /\ stdoutXA (mrestrict (ahid A' model') M').
  Proof.
    intros IMG j LB LK cr A M model LB' LK' cr' A' M' model' I1 (lo2 & hi2 & I2 & I2l & I2h) D D' Hj FR SO SOX.
    apply (stdout_agree j _ _ SO SOX Hj). intros a Ha. unfold mrestrict.
    rewrite (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ a D) by (unfold SOBUF in Ha; lia).
    rewrite (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ a D') by (unfold SOBUF in Ha; lia).
    destruct Ha as [Ha|Ha].
    - apply (FR 0x158c38 0x15a640); [exact I1 | lia].
    - apply (FR lo2 hi2); [exact I2 | unfold SOBUF in Ha; lia].
  Qed.

  Definition stdout_call := stdout_call_g IMG_CLIENT_A.
  Definition stdout_lib := stdout_call_g IMG_LIB_A.
  Lemma in_client_1 : In (0x158c38, 0x15a640) IMG_CLIENT_A.  Proof. unfold IMG_CLIENT_A; cbn [In]; tauto. Qed.
  Lemma in_client_2 : exists lo2 hi2, In (lo2, hi2) IMG_CLIENT_A /\ lo2 <= 0x6b25b0 /\ 0x6b29b0 <= hi2.
  Proof. exists 0x691dc0, 0x6b3248. split; [unfold IMG_CLIENT_A; cbn [In]; tauto | split; apply Z.leb_le; reflexivity]. Qed.
  Lemma in_lib_1 : In (0x158c38, 0x15a640) IMG_LIB_A.  Proof. unfold IMG_LIB_A; cbn [In]; tauto. Qed.
  Lemma in_lib_2 : exists lo2 hi2, In (lo2, hi2) IMG_LIB_A /\ lo2 <= 0x6b25b0 /\ 0x6b29b0 <= hi2.
  Proof using Hsp HCAP. exists 0x6b2104, 0x6b3248. split; [unfold IMG_LIB_A; cbn [In]; tauto | split; apply Z.leb_le; reflexivity]. Qed.

  Lemma atx_of_ls : forall g M, ls_ok LSt g M -> exists ls2, cells_at M (ATX ls2).
  Proof.
    intros g M HLS. destruct (LEX g M HLS) as (AT & NLK).
    rewrite (dlla_L Lay L DLL), (dla_segs L ar IL sp0 DL) in AT, NLK. rewrite (dlla_atexit Lay L DLL), (dlla_hs0 Lay L DLL) in AT. rewrite (dlla_need_locks Lay L DLL) in NLK.
    destruct (LSX g) as [E|[E|[E|[E|E]]]]; rewrite E in AT; unfold LS2_HANDLERS, LS2C_HANDLERS, LS2JC_HANDLERS, LS2CJ_HANDLERS in AT; cbn [app] in AT; destruct AT as (_ & LOCK & _ & HEAD & SLOT & NEXT & FA); [exists XT_NONE | exists XT_J | exists XT_C | exists XT_JC | exists XT_CJ]; unfold ATX, cells_at.
    - destruct (FA 0%nat _ _ eq_refl) as (F0 & A0'). destruct (FA 1%nat _ _ eq_refl) as (FG & AG).
      repeat (apply Forall_cons; [first [exact NLK | exact HEAD | exact SLOT | exact F0 | exact A0' | exact FG | exact AG | exact LOCK | exact NEXT]|]). apply Forall_nil.
    - destruct (FA 0%nat _ _ eq_refl) as (F0 & A0'). destruct (FA 1%nat _ _ eq_refl) as (FG & AG). destruct (FA 2%nat _ _ eq_refl) as (F1' & A1'). destruct (FA 3%nat _ _ eq_refl) as (F2' & A2').
      repeat (apply Forall_cons; [first [exact NLK | exact HEAD | exact SLOT | exact F0 | exact A0' | exact FG | exact AG | exact F1' | exact A1' | exact F2' | exact A2' | exact LOCK | exact NEXT]|]). apply Forall_nil.
    - destruct (FA 0%nat _ _ eq_refl) as (F0 & A0'). destruct (FA 1%nat _ _ eq_refl) as (FG & AG). destruct (FA 2%nat _ _ eq_refl) as (F1' & A1'). destruct (FA 3%nat _ _ eq_refl) as (F2' & A2').
      repeat (apply Forall_cons; [first [exact NLK | exact HEAD | exact SLOT | exact F0 | exact A0' | exact FG | exact AG | exact F1' | exact A1' | exact F2' | exact A2' | exact LOCK | exact NEXT]|]). apply Forall_nil.
    - destruct (FA 0%nat _ _ eq_refl) as (F0 & A0'). destruct (FA 1%nat _ _ eq_refl) as (FG & AG). destruct (FA 2%nat _ _ eq_refl) as (F1' & A1'). destruct (FA 3%nat _ _ eq_refl) as (F2' & A2'). destruct (FA 4%nat _ _ eq_refl) as (F3' & A3'). destruct (FA 5%nat _ _ eq_refl) as (F4' & A4').
      repeat (apply Forall_cons; [first [exact NLK | exact HEAD | exact SLOT | exact F0 | exact A0' | exact FG | exact AG | exact F1' | exact A1' | exact F2' | exact A2' | exact F3' | exact A3' | exact F4' | exact A4' | exact LOCK | exact NEXT]|]). apply Forall_nil.
    - destruct (FA 0%nat _ _ eq_refl) as (F0 & A0'). destruct (FA 1%nat _ _ eq_refl) as (FG & AG). destruct (FA 2%nat _ _ eq_refl) as (F1' & A1'). destruct (FA 3%nat _ _ eq_refl) as (F2' & A2'). destruct (FA 4%nat _ _ eq_refl) as (F3' & A3'). destruct (FA 5%nat _ _ eq_refl) as (F4' & A4').
      repeat (apply Forall_cons; [first [exact NLK | exact HEAD | exact SLOT | exact F0 | exact A0' | exact FG | exact AG | exact F1' | exact A1' | exact F2' | exact A2' | exact F3' | exact A3' | exact F4' | exact A4' | exact LOCK | exact NEXT]|]). apply Forall_nil.
  Qed.
  Lemma atx_call : forall ls2 (M M' : word -> option byte),
    (forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> cells_at M (ATX ls2) -> cells_at M' (ATX ls2).
  Proof.
    intros ls2 M M' FR HC. apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) HC c Hc) as X. rewrite <- X.
    apply rdn_agree. intros q Hq. apply (FR 0x691dc0 0x6b3248); [unfold IMG_CLIENT_A; cbn [In]; tauto|].
    destruct ls2; unfold ATX in Hc; cbn [In] in Hc; repeat (destruct Hc as [<-|Hc]; [cbn [fst snd] in Hq |- *; rewrite u_small by lia; cbn in Hq; lia|]); destruct Hc.
  Qed.

  Lemma tail_MA : forall (fx' : PropExec.FPState) (j : nat) (ls2 : xtag) vals R M (model : Model) A (A1 : Z) LK cr,
    length vals = 198%nat -> hdr_valsA sp0 p0 p1 can vals -> vals_ev vals 48 = Z_to_bv 64 A1 -> (j <= 3)%nat ->
    regs_ok (ENVG vals) srF1A R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knF1A ->
    dinvA [(A1, CAP)] LK cr A M model -> m_fds model = fds0 -> m_fs model = fs0 ->
    stdoutA (Z.of_nat j) (mrestrict (ahid A model) M) -> stdoutXA (mrestrict (ahid A model) M) ->
    cells_at M (ATX ls2) ->
    srealizes ASEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0xaf46c) M (seg_rom ASEGS)) model) (EA j).
  Proof.
    intros fx' j ls2 vals R M model A A1 LK cr HL HV P48 Hj HR HK DI F1 F2 SO SOX HATX.
    pose proof HV as (P0 & _). pose proof Hsp as Hsp'.

    drv_blockT0 HIok Hsp DL HR HK DI P0 scr0 198%nat.
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
    pose proof (ahid_sbm A model model0 SBM) as AH. rewrite <- AH in SO, SOX.
    clear HR HK DI EQM EQH EQA SBM AH F1 F2. rename R0 into R1, HR0 into HR, HK0 into HK, DI0 into DI, model0 into model1.

    assert (FREEB : forall (fxq : PropExec.FPState) srX knX Rq Mq (modelq : Model) Aq,
              regs_ok (ENVG vals) srX Rq -> know_ok ASEGS (ENVG vals) (mrestrict (ahid Aq modelq) Mq) knX ->
              sr_vars_lt 198 srX = true -> kn_vars_lt 198 knX = true -> has_window knX = true ->
              sr_after_call_j srX (map ridx c_kept) 198 = srF2A -> ksubl_b (keep_allocA MSO 4096 [] [] knX) knF2A = true ->
              (nth 1 srX (ELit 0), nth 2 srX (ELit 0), nth 4 srX (ELit 0), nth 10 srX (ELit 0)) = (ELit 0xaf2a0, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 6888848, EVar 48) ->
              dinvA [(A1, CAP)] LK cr Aq Mq modelq -> m_fds modelq = fds0 -> m_fs modelq = fs0 ->
              stdoutA (Z.of_nat j) (mrestrict (ahid Aq modelq) Mq) -> stdoutXA (mrestrict (ahid Aq modelq) Mq) -> cells_at Mq (ATX ls2) ->
              srealizes ASEGS scfg (mkCfg (@mkst fxq Rq (Z_to_bv 64 0x80db4) Mq (seg_rom ASEGS)) modelq) (EA j)).
    { intros fxq srX knX Rq Mq modelq Aq HRq HKq SV KV HW ESR EKN ENTH DIq F1q F2q SOq SOXq HATXq.
      injection ENTH as N1 N2 N4 N10.
      apply (@afree_site fxq scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals _ srX knX Rq Mq modelq [(A1, CAP)] LK cr Aq A1 CAP MSO [] [] 0xaf2a0 (EA j) HRq HKq).
      - rewrite HL. exact SV.
      - rewrite HL. exact KV.
      - rewrite HL. lia.
      - exact P0.
      - exact HW.
      - rewrite (HRq (2%bv : reg)). change (sr_get srX (2%bv : reg)) with (nth 2 srX (ELit 0)). rewrite N2. cbn [edenot ev ENVA]. rewrite P0. apply alu_add_w_litA.
      - unfold MSO. lia.
      - reflexivity.
      - left. reflexivity.
      - rewrite (HRq (10%bv : reg)). change (sr_get srX (10%bv : reg)) with (nth 10 srX (ELit 0)). rewrite N10. cbn [edenot ev ENVA]. exact P48.
      - rewrite (HRq (4%bv : reg)). change (sr_get srX (4%bv : reg)) with (nth 4 srX (ELit 0)). rewrite N4. reflexivity.
      - rewrite (HRq (1%bv : reg)). change (sr_get srX (1%bv : reg)) with (nth 1 srX (ELit 0)). rewrite N1. reflexivity.
      - lia.
      - reflexivity.
      - exact DIq.
      - intros i nb Hf. discriminate Hf.
      - intros v b Hf. discriminate Hf.
      - unfold EA. apply t_emit_has_nil.
      - intros R' M' model' A' vals' E' HL' HR' HK' DI' MRT HINC' _ _ FRc.
        rewrite lb_remove_hdA in DI'. rewrite HL in HL', HR'. rewrite ESR in HR'.
        destruct (model_rt_fds _ _ MRT) as (Q1 & Q2). rewrite F1q in Q1. rewrite F2q in Q2.
        destruct (stdout_call (Z.of_nat j) _ _ _ _ _ _ _ _ _ _ _ _ in_client_1 in_client_2 DIq DI' ltac:(lia) FRc SOq SOXq) as (SO' & SOX').
        apply (tail_FA fxq j ls2 vals' R' M' model' A' LK cr HL').
        + subst vals'. apply (hdr_appA sp0 fdata); [exact HV | rewrite HL; lia].
        + exact Hj.
        + exact HR'.
        + eapply ksubl_sound; [exact HK' | exact EKN].
        + exact DI'.
        + exact Q1.
        + exact Q2.
        + exact SO'.
        + exact SOX'.
        + exact (atx_call ls2 Mq M' FRc HATXq). }
    destruct (branch_taken BC_LT (vals_ev vals 74) (Z_to_bv 64 0)) eqn:BT.
    - drv_block0 HIok Hsp DL HR HK DI P0 (SCR [true] [] []) 198%nat.
      { cbn [sc_denot edenot ev ENVA]. exact BT. }
      pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
      assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
      destruct (sbm_fds _ _ SBM) as (Q1 & Q2). rewrite G1 in Q1. rewrite G2 in Q2.
      pose proof (ahid_sbm A model1 model0 SBM) as AH. rewrite <- AH in SO, SOX.
      apply (FREEB fx' _ _ R0 M model0 A HR0 HK0); first [exact DI0 | exact Q1 | exact Q2 | exact SO | exact SOX | exact HATX | (vm_compute; reflexivity)].
    - drv_block0 HIok Hsp DL HR HK DI P0 (SCR [false] [] []) 198%nat.
      { cbn [sc_denot edenot ev ENVA]. exact BT. }
      pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
      assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
      destruct (sbm_fds _ _ SBM) as (Q1 & Q2). rewrite G1 in Q1. rewrite G2 in Q2.
      pose proof (ahid_sbm A model1 model0 SBM) as AH. rewrite <- AH in SO, SOX.
      apply (FREEB fx' _ _ R0 M model0 A HR0 HK0); first [exact DI0 | exact Q1 | exact Q2 | exact SO | exact SOX | exact HATX | (vm_compute; reflexivity)].
  Qed.

  Lemma afree_null_siteA : forall (fxq : PropExec.FPState) vals ebs sr kn R M (model : Model) LB LK cr A so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true -> (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> has_window kn = true ->
    getr R 2%bv = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    getr R 10%bv = Z_to_bv 64 0 -> getr R 4%bv = Z_to_bv 64 0x691d90 -> getr R 1%bv = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    dinvA LB LK cr A M model ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA L ar LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    (forall R' M' (model' : Model) A',
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A' model') M') (keep_allocA so 4096 bls vbnd kn) ->
       dinvA LB LK cr A' M' model' -> model_rt model model' -> incl A A' ->
       (forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (@mkst fxq R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0x80db4) M (seg_rom ASEGS)) model) K.
  Proof. intros fxq. exact (@afree_null_site fxq scfg L ar C IL HI HIok FNULL sp0 Hsp Hal DL M0 M0_def). Qed.

  Lemma tail_XA : forall j : nat, SSPA 1 (Z.of_nat j) (EA j).
  Proof.
    intros j. unfold SSPA.
    intros fx' vals R M model A A1 PTR OWN LB LK cr g (HL & HV & P48 & P70 & P73 & P79 & P81 & P82 & P83) Hk Hj Hjk HR HK
           (HBLK & HC & HPAY & DI & HINC & F1 & F2 & SO & SOX & HLS & HROOM).
    intros _.
    destruct (atx_of_ls g M HLS) as (ls2 & HATX).
    pose proof HV as (P0 & _). pose proof Hsp as Hsp'.
    drv_blockT0 HIok Hsp DL HR HK DI P0 (SCR [false] [] []) 166%nat.
    { apply (dec_scA vals _ 1 false P81); [lia | reflexivity]. }
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
    pose proof (ahid_sbm A model model0 SBM) as AH. rewrite <- AH in SO, SOX.
    destruct HBLK as (HBR & REST).
    assert (R2q : getr R0 2%bv = Z_to_bv 64 (bv_unsigned sp0 + TSO)).
    { regv HR0 (2%bv : reg). cbn [edenot ev ENVA]. rewrite P0. apply alu_add_w_litA. }
    assert (R10q : getr R0 10%bv = Z_to_bv 64 OWN) by (regv HR0 (10%bv : reg); cbn [edenot ev ENVA]; exact P83).
    assert (R4q : getr R0 4%bv = Z_to_bv 64 0x691d90) by (regv HR0 (4%bv : reg); reflexivity).
    assert (R1q : getr R0 1%bv = Z_to_bv 64 0xaf46c) by (regv HR0 (1%bv : reg); reflexivity).
    assert (SUB : forall LBx, In (A1, CAP) LBx -> forall i nb, find_nz i [(48%nat, 65536)] = Some nb -> (i < length vals)%nat /\ sub_blockA L ar LBx (bv_unsigned (vals_ev vals i)) nb).
    { intros LBx Hin i nb Hf. cbn [find_nz] in Hf. destruct (Nat.eqb i 48) eqn:E48; [|discriminate Hf]. apply Nat.eqb_eq in E48. subst i. injection Hf as <-.
      split; [rewrite HL; lia|]. rewrite P48. pose proof HBR as (B1 & _ & _ & _ & _ & (_ & _ & B47)). rewrite u_small by lia. exists CAP. split; [lia|]. split; [exact Hin | exact HBR]. }

    assert (KONT : forall R' M' (model' : Model) A',
              let vals' := vals ++ junk_vals R' in
              length vals' = (length vals + 32)%nat ->
              regs_ok (ENVG vals') (sr_after_call_j srSf2A (map ridx c_kept) (length vals)) R' ->
              know_ok ASEGS (ENVG vals') (mrestrict (ahid A' model') M') (keep_allocA TSO 4096 [(48%nat, 65536)] [] (kn_after rSf2A knLH2A)) ->
              dinvA [(A1, CAP)] LK cr A' M' model' -> model_rt model0 model' ->
              (forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
              srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xaf46c) M' (seg_rom ASEGS)) model') (EA j)).
    { intros R' M' model' A' vals' HL' HR' HK' DI' MRT FRc. rewrite HL in HL', HR'.
      destruct (model_rt_fds _ _ MRT) as (Q1 & Q2). rewrite G1 in Q1. rewrite G2 in Q2.
      destruct (stdout_call (Z.of_nat j) _ _ _ _ _ _ _ _ _ _ _ _ in_client_1 in_client_2 DI0 DI' ltac:(lia) FRc SO SOX) as (SO' & SOX').
      apply (tail_MA fx' j ls2 vals' R' M' model' A' A1 LK cr HL').
      - subst vals'. apply (hdr_appA sp0 fdata); [exact HV | rewrite HL; lia].
      - subst vals'. rewrite vals_ev_app_l by (rewrite HL; lia). exact P48.
      - lia.
      - exact HR'.
      - exact HK'.
      - exact DI'.
      - exact Q1.
      - exact Q2.
      - exact SO'.
      - exact SOX'.
      - exact (atx_call ls2 M M' FRc HATX). }
    destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)]; subst LB.
    -
      subst OWN.
      apply (afree_null_siteA fx' vals _ srSf2A (kn_after rSf2A knLH2A) R0 M model0 [(A1, CAP)] LK cr A TSO [(48%nat, 65536)] [] 0xaf46c (EA j) HR0 HK0);
        [ rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia | exact P0 | vm_compute; reflexivity | exact R2q | unfold TSO; lia | reflexivity
        | exact R10q | exact R4q | exact R1q | lia | reflexivity | exact DI0 | apply SUB; left; reflexivity | intros v b Hf; discriminate Hf | unfold EA; apply t_emit_has_nil | ].
      intros R' M' model' A' vals' E' HL' HR' HK' DI' MRT _ _ _ FRc. exact (KONT R' M' model' A' HL' HR' HK' DI' MRT FRc).
    -
      apply (@afree_site fx' scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals _ srSf2A (kn_after rSf2A knLH2A) R0 M model0 [(OWN, PL); (A1, CAP)] LK cr A OWN PL TSO
               [(48%nat, 65536)] [] 0xaf46c (EA j) HR0 HK0);
        [ rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia | exact P0 | vm_compute; reflexivity | exact R2q | unfold TSO; lia | reflexivity
        | left; reflexivity | exact R10q | exact R4q | exact R1q | lia | reflexivity | exact DI0 | rewrite lb_remove_hdA; apply SUB; left; reflexivity | intros v b Hf; discriminate Hf
        | unfold EA; apply t_emit_has_nil | ].
      intros R' M' model' A' vals' E' HL' HR' HK' DI' MRT _ _ _ FRc. rewrite lb_remove_hdA in DI'. exact (KONT R' M' model' A' HL' HR' HK' DI' MRT FRc).
  Qed.
End DrvE.
End FPX_1.
