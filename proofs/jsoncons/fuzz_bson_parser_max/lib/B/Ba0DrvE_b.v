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
  RefNodes RefPrintfLib HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface LibIfaceAB DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvA_b
  Ba0DrvG_defs_b Ba0DrvG_b Ba0DrvC_defs_b Ba0DrvC_b Ba0DrvD_defs_b Ba0DrvLibL_b Ba0DrvD_b Ba0DrvE_defs_b Ba0DrvStdio_b Ba0DrvPrintfK_b Ba0DrvPrintf1_b Ba0DrvExit_b Ba0DrvExitB_b Ba0DrvExitS_b Ba0DrvExitSB_b Ba0DrvExitBS_b Ba0ExitCells_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceANull. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvFreeNull_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ShapeLaws AgentLib Spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition relayE (vals : list word) (R : bvmap 5 word) (W : word) : list word := firstn 81 vals ++ (getr R 21 :: tl (lay_extA vals R W)).
Definition shared_posE : list nat := [2; 3; 4; 8; 20; 22; 23; 24; 25; 26; 27]%nat.      (* [comment removed for export] *)
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

(* [comment removed for export] *)
Section Pf1Keep.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  #[using="Hsp"] Lemma regions_pf1A : forall vals ebs so bls,
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
      apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x662290) (Z_to_bv 64 d) 65536%nat m 0x662290 0x672290);
        first [exact (wseg_stage) | reflexivity | lia | (rewrite u_small by lia; lia)].
  Qed.
End Pf1Keep.

(* [comment removed for export] *)
Definition XKN : list kentry :=
  map (fun c : Z * nat * Z => KWord (SA (ELit 0) (fst (fst c))) (snd (fst c)) (ELit (snd c))) XC9_CELLS
  ++ [KWord (SA (ELit 0) 6765656) 4 (EVar 4); KRange (EVar 4) 1 4194303; KImg 0x13bcc8 0x13bdb8; KImg 0x13bea0 0x13c580].
(* [comment removed for export] *)
Definition XKN_X : list kentry :=
  [KWord (SA (ELit 0) 6897520) 4 (ELit 0); KWord (SA (ELit 0) 6897555) 1 (ELit 0); KWord (SA (ELit 0) 6898952) 8 (ELit 0); KWord (SA (ELit 0) 6897776) 4 (ELit 0);
   KWord (SA (ELit 0) 6759060) 1 (ELit 0)]      (* [comment removed for export] *)
  ++ [KWord (SA (ELit 0) 6765656) 4 (EVar 4); KRange (EVar 4) 1 4194303; KImg 0x13bcc8 0x13bdb8; KImg 0x13bea0 0x13c580].

(* [comment removed for export] *)
Definition exit_of (ax : axv) : Z -> (word -> option byte) -> Prop :=
  match ax with AX0 => exitA | AXc => exitB | AXs => exitS | AXcs => exitBS | AXsc => exitSB end.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvE.
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
  Variable A0 : list (Z * Z).
  Variable CAP : Z.
  Hypothesis HCAP : 65536 <= CAP <= 67108864.
  Hypothesis HLEN : Z.of_nat (length fdata) < CAP.
  Variable Lay : lib_layoutA.
  Variable LSt : lib_statics.
  Hypothesis ILY : as0_icpt_layout IL.
  Hypothesis Hex : incl EX_CELLS (asc_cells C).
  Hypothesis FNULL : afree_null_spec L ar scfg HI.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis LSXA : forall g M, ls_ok LSt g M -> exists ax : axv, atexit_cellsA M ax.

  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation ENVG := (ENVA fdata).
  Let LEN : Z := Z.of_nat (length fdata).
  Let CFG : Z := CFGA fdata.
  Let PL : Z := PLA fdata.
  #[local] Notation payloadA := (Ba0DrvD_b.payloadA fdata).
  #[local] Notation blk_factsA := (Ba0DrvD_b.blk_factsA L ar fdata CAP).

  (* [comment removed for export] *)
  Definition e_valsA (n : nat) (vals : list word) (A1 PTR OWN k : Z) : Prop :=
    length vals = n /\ hdr_valsA sp0 p0 p1 can vals
    /\ vals_ev vals 48 = Z_to_bv 64 A1 /\ vals_ev vals 70 = Z_to_bv 64 LEN
    /\ vals_ev vals 73 = Z_to_bv 64 CFG /\ vals_ev vals 79 = Z_to_bv 64 PL
    /\ vals_ev vals 81 = Z_to_bv 64 k /\ vals_ev vals 82 = Z_to_bv 64 PTR /\ vals_ev vals 83 = Z_to_bv 64 OWN.

  (* [comment removed for export] *)
  Definition credit_scaleA (k : Z) (c : credit) : credit := (k * fst c, k * snd c).
  Definition lib_roomA (kc : Z) (LK : list fframe) (cr : credit) : Prop :=
    credit_le (credit_scaleA kc (lla_credit Lay PL)) cr
    /\ (forall c, In c [0; 1; 2; 3; 4; 5] -> Z.of_nat (ff_count c LK) + kc * lla_leak Lay c + lla_frames Lay c <= ff_cap c).

  (* [comment removed for export] *)
  Definition e_factsA (kc j : Z) (A1 PTR OWN : Z) (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (g : ls_state LSt) A M (model : Model) : Prop :=
    blk_factsA A1 PTR OWN LB
    /\ rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata
    /\ rdn ASEGS M (Z_to_bv 64 PTR) (length payloadA) = Some payloadA
    /\ dinvA LB LK cr A M model /\ incl A0 A
    /\ m_fds model = fds0 /\ m_fs model = fs0
    /\ stdoutA j (mrestrict (ahid A model) M) /\ stdoutXA (mrestrict (ahid A model) M)
    /\ ls_ok LSt g M /\ lib_roomA kc LK cr.

  (* [comment removed for export] *)
  Definition SSPA (k j : Z) (K : TSet) : Prop :=
    forall (fx' : PropExec.FPState) vals R M (model : Model) A (A1 PTR OWN : Z) LB LK cr g,
      e_valsA 166 vals A1 PTR OWN k -> 1 <= k -> 0 <= j -> j + k <= 4 ->
      regs_ok (ENVG vals) srQ0A R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knLH2A ->
      e_factsA (k - 1) j A1 PTR OWN LB LK cr g A M model ->
      srealizes ASEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0xa7f98) M (seg_rom ASEGS)) model) K.

  (* [comment removed for export] *)
  Definition LH2PA (k j : Z) (K : TSet) : Prop :=
    forall (fx' : PropExec.FPState) vals R M (model : Model) A (A1 PTR OWN : Z) LB LK cr g,
      e_valsA 102 vals A1 PTR OWN k -> 1 <= k -> 0 <= j -> j + k <= 3 ->
      regs_ok (ENVG vals) srLHA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knLH2A ->
      e_factsA k j A1 PTR OWN LB LK cr g A M model ->
      srealizes ASEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0xa7e8c) M (seg_rom ASEGS)) model) K.

  (* [comment removed for export] *)
  Definition dec_xA : expr := EAluw ALU_ADD (EVar 81) (ELit (-1)).
  #[using="sp0 LEN CFG PL"] Lemma dec_valA : forall vals k, vals_ev vals 81 = Z_to_bv 64 k -> 1 <= k <= 4 -> edenot (ENVG vals) dec_xA = Z_to_bv 64 (k - 1).
  Proof.
    intros vals k P81 Hk. unfold dec_xA. cbn [edenot ev ENVA]. rewrite P81.
    assert (k = 1 \/ k = 2 \/ k = 3 \/ k = 4) as [-> |[-> |[-> | ->]]] by lia; vm_compute; reflexivity.
  Qed.
  #[using="sp0 can LEN CFG PL"] Lemma dec_scA : forall vals M k t, vals_ev vals 81 = Z_to_bv 64 k -> 1 <= k <= 4 -> negb (Z.eqb (k - 1) 0) = t ->
    sc_denot ASEGS M (ENVG vals) (SCBr t BC_NE dec_xA (ELit 0)).
  Proof.
    intros vals M k t P81 Hk Ht. cbn [sc_denot branch_taken]. rewrite (dec_valA vals k P81 Hk). cbn [edenot].
    unfold bv_eqb. rewrite !u_small by lia. exact Ht.
  Qed.

  (* [comment removed for export] *)
  #[using="C IL HIok Hsp DL HCAP"] Lemma step_SA : forall k j K, 2 <= k -> LH2PA (k - 1) j K -> SSPA k j K.
  Proof.
    intros k j K Hk2 HLH. unfold SSPA.
    intros fx' vals R M model A A1 PTR OWN LB LK cr g (HL & HV & P48 & P70 & P73 & P79 & P81 & P82 & P83) Hk Hj Hjk HR HK
           (HBLK & HC & HPAY & DI & HINC & F1 & F2 & SO & SOX & HLS & HROOM).
    pose proof HV as (P0 & _).
    drv_blockT0 HIok Hsp DL HR HK DI P0 (SCR [true] [] []) 166%nat.
    { apply (dec_scA vals _ k true P81); [lia | apply Bool.negb_true_iff; apply Z.eqb_neq; lia]. }
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
    pose proof (ahid_sbm A model model0 SBM) as AH.
    assert (V81 : getr R0 21%bv = Z_to_bv 64 (k - 1)).
    { regv HR0 (21%bv : reg). change (sr_get srSt2A (21%bv : reg)) with dec_xA. apply (dec_valA vals k P81). lia. }      (* [comment removed for export] *)
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
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EA (j : nat) : TSet := t_emit (W 1 (zero_lines j)) (t_exit (exit_code 0) fs0).

  (* [comment removed for export] *)
  #[using="sp0 Hsp CAP HCAP LEN CFG PL"] Lemma exitf_of_kn : forall vals (MV : word -> option byte) kn,
    know_ok ASEGS (ENVG vals) MV kn -> forallb (fun K => existsb (kentry_eqb K) kn) XKN = true ->
    exitE (bv_unsigned (vals_ev vals 4)) MV.      (* [comment removed for export] *)
  Proof.
    intros vals MV kn HK HB. rewrite forallb_forall in HB.
    assert (KB : forall K, In K XKN -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (HB K HKin)).
    pose proof (kimg_clear (ENVG vals) MV kn 0x13bcc8 0x13bdb8 HK (KB (KImg 0x13bcc8 0x13bdb8) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLa.
    pose proof (kimg_clear (ENVG vals) MV kn 0x13bea0 0x13c580 HK (KB (KImg 0x13bea0 0x13c580) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLb.
    assert (ICa : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bcc8 <=? a) && (a + Z.of_nat n <=? 0x13bdb8) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLa. lia. }
    assert (ICb : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bea0 <=? a) && (a + Z.of_nat n <=? 0x13c580) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLb. lia. }
    unfold exitE. split; [|split; [|split]].
    - unfold cells_at, XC_CELLS_E.
      constructor; [exact (kword_lit sp0 _ MV kn 6897520 4%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6897520) 4 (ELit 0)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6897555 1%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6897555) 1 (ELit 0)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6896992 8%nat (ELit 6897000) HK (KB (KWord (SA (ELit 0) 6896992) 8 (ELit 6897000)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6896984 4%nat (ELit 1) HK (KB (KWord (SA (ELit 0) 6896984) 4 (ELit 1)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6897008 8%nat (ELit 1148964) HK (KB (KWord (SA (ELit 0) 6897008) 8 (ELit 1148964)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6897264 8%nat (ELit 619876) HK (KB (KWord (SA (ELit 0) 6897264) 8 (ELit 619876)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6896980 4%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6896980) 4 (ELit 0)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6897000 8%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6897000) 8 (ELit 0)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6898952 8%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6898952) 8 (ELit 0)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (ICb 1294224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293992)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294132 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1293984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293752)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293512)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293652 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor.
    - rewrite Z_to_bv_bv_unsigned. exact (kword_lit sp0 _ MV kn 6765656 4%nat (EVar 4) HK (KB (KWord (SA (ELit 0) 6765656) 4 (EVar 4)) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)).
    - pose proof (KB (KRange (EVar 4) 1 4194303) ltac:(unfold XKN; cbn [In map XC9_CELLS app fst snd]; tauto)) as Hb.
      apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
      pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok edenot ev ENVA] in X. exact X.
    - intros i Hi. apply CLb. lia.
  Qed.
  #[using="sp0 Hsp CAP HCAP LEN CFG PL"] Lemma exitf_ax_A : forall vals (MV : word -> option byte) kn,
    know_ok ASEGS (ENVG vals) MV kn -> forallb (fun K => existsb (kentry_eqb K) kn) XKN_X = true -> atexit_cellsA MV AX0 ->
    exitA (bv_unsigned (vals_ev vals 4)) MV.
  Proof.
    intros vals MV kn HK HB HAX. rewrite forallb_forall in HB.
    assert (KB : forall K, In K XKN_X -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (HB K HKin)).
    pose proof (kimg_clear (ENVG vals) MV kn 0x13bcc8 0x13bdb8 HK (KB (KImg 0x13bcc8 0x13bdb8) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLa.
    pose proof (kimg_clear (ENVG vals) MV kn 0x13bea0 0x13c580 HK (KB (KImg 0x13bea0 0x13c580) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLb.
    assert (ICa : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bcc8 <=? a) && (a + Z.of_nat n <=? 0x13bdb8) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLa. lia. }
    assert (ICb : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bea0 <=? a) && (a + Z.of_nat n <=? 0x13c580) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLb. lia. }
    unfold exitA. split; [|split; [|split]].
    - unfold cells_at, XC_CELLS.
      constructor; [exact (kword_lit sp0 _ MV kn 6897520 4%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6897520) 4 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6897555 1%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6897555) 1 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AX0 6896992 8 6897000 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AX0 6896984 4 2 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AX0 6897008 8 1148964 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AX0 6897264 8 619876 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AX0 6896980 4 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AX0 6897000 8 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6898952 8%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6898952) 8 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (ICb 1294224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293992)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294132 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1293984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293752)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293512)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293652 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (atexit_cellsA_atb MV AX0 6897016 8 1148964 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AX0 6897272 8 687916 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6759060 1%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6759060) 1 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor.
    - rewrite Z_to_bv_bv_unsigned. exact (kword_lit sp0 _ MV kn 6765656 4%nat (EVar 4) HK (KB (KWord (SA (ELit 0) 6765656) 4 (EVar 4)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)).
    - pose proof (KB (KRange (EVar 4) 1 4194303) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) as Hb.
      apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
      pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok edenot ev ENVA] in X. exact X.
    - intros i Hi. apply CLb. lia.
  Qed.
  #[using="sp0 Hsp CAP HCAP LEN CFG PL"] Lemma exitf_ax_B : forall vals (MV : word -> option byte) kn,
    know_ok ASEGS (ENVG vals) MV kn -> forallb (fun K => existsb (kentry_eqb K) kn) XKN_X = true -> atexit_cellsA MV AXc ->
    exitB (bv_unsigned (vals_ev vals 4)) MV.
  Proof.
    intros vals MV kn HK HB HAX. rewrite forallb_forall in HB.
    assert (KB : forall K, In K XKN_X -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (HB K HKin)).
    pose proof (kimg_clear (ENVG vals) MV kn 0x13bcc8 0x13bdb8 HK (KB (KImg 0x13bcc8 0x13bdb8) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLa.
    pose proof (kimg_clear (ENVG vals) MV kn 0x13bea0 0x13c580 HK (KB (KImg 0x13bea0 0x13c580) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLb.
    assert (ICa : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bcc8 <=? a) && (a + Z.of_nat n <=? 0x13bdb8) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLa. lia. }
    assert (ICb : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bea0 <=? a) && (a + Z.of_nat n <=? 0x13c580) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLb. lia. }
    unfold exitB. split; [|split; [|split]].
    - unfold cells_at, XC_CELLS_B.
      constructor; [exact (kword_lit sp0 _ MV kn 6897520 4%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6897520) 4 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6897555 1%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6897555) 1 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXc 6896992 8 6897000 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXc 6896984 4 4 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXc 6897008 8 1148964 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXc 6897264 8 619876 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXc 6896980 4 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXc 6897000 8 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6898952 8%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6898952) 8 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (ICb 1294224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293992)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294132 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1293984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293752)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293512)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293652 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (atexit_cellsA_atb MV AXc 6897016 8 1148964 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXc 6897272 8 687916 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6759060 1%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6759060) 1 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXc 6897024 8 872740 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXc 6897032 8 449180 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXc 6897280 8 1293304 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXc 6897288 8 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor.
    - rewrite Z_to_bv_bv_unsigned. exact (kword_lit sp0 _ MV kn 6765656 4%nat (EVar 4) HK (KB (KWord (SA (ELit 0) 6765656) 4 (EVar 4)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)).
    - pose proof (KB (KRange (EVar 4) 1 4194303) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) as Hb.
      apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
      pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok edenot ev ENVA] in X. exact X.
    - intros i Hi. apply CLb. lia.
  Qed.
  #[using="sp0 Hsp CAP HCAP LEN CFG PL"] Lemma exitf_ax_S : forall vals (MV : word -> option byte) kn,
    know_ok ASEGS (ENVG vals) MV kn -> forallb (fun K => existsb (kentry_eqb K) kn) XKN_X = true -> atexit_cellsA MV AXs ->
    exitS (bv_unsigned (vals_ev vals 4)) MV.
  Proof.
    intros vals MV kn HK HB HAX. rewrite forallb_forall in HB.
    assert (KB : forall K, In K XKN_X -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (HB K HKin)).
    pose proof (kimg_clear (ENVG vals) MV kn 0x13bcc8 0x13bdb8 HK (KB (KImg 0x13bcc8 0x13bdb8) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLa.
    pose proof (kimg_clear (ENVG vals) MV kn 0x13bea0 0x13c580 HK (KB (KImg 0x13bea0 0x13c580) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLb.
    assert (ICa : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bcc8 <=? a) && (a + Z.of_nat n <=? 0x13bdb8) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLa. lia. }
    assert (ICb : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bea0 <=? a) && (a + Z.of_nat n <=? 0x13c580) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLb. lia. }
    unfold exitS. split; [|split; [|split]].
    - unfold cells_at, XC_CELLS_S.
      constructor; [exact (kword_lit sp0 _ MV kn 6897520 4%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6897520) 4 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6897555 1%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6897555) 1 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6896992 8 6897000 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6896984 4 6 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6897008 8 1148964 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6897264 8 619876 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6896980 4 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6897000 8 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6898952 8%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6898952) 8 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (ICb 1294224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293992)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294132 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1293984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293752)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293512)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293652 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6897016 8 1148964 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6897272 8 687916 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6759060 1%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6759060) 1 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6759112 1 16 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6759144 1 6 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6897024 8 874172 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6897032 8 449180 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6897040 8 874172 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6897048 8 449180 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6897280 8 6759112 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6897288 8 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6897296 8 6759144 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXs 6897304 8 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor.
    - rewrite Z_to_bv_bv_unsigned. exact (kword_lit sp0 _ MV kn 6765656 4%nat (EVar 4) HK (KB (KWord (SA (ELit 0) 6765656) 4 (EVar 4)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)).
    - pose proof (KB (KRange (EVar 4) 1 4194303) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) as Hb.
      apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
      pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok edenot ev ENVA] in X. exact X.
    - intros i Hi. apply CLb. lia.
  Qed.
  #[using="sp0 Hsp CAP HCAP LEN CFG PL"] Lemma exitf_ax_SB : forall vals (MV : word -> option byte) kn,
    know_ok ASEGS (ENVG vals) MV kn -> forallb (fun K => existsb (kentry_eqb K) kn) XKN_X = true -> atexit_cellsA MV AXsc ->
    exitSB (bv_unsigned (vals_ev vals 4)) MV.
  Proof.
    intros vals MV kn HK HB HAX. rewrite forallb_forall in HB.
    assert (KB : forall K, In K XKN_X -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (HB K HKin)).
    pose proof (kimg_clear (ENVG vals) MV kn 0x13bcc8 0x13bdb8 HK (KB (KImg 0x13bcc8 0x13bdb8) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLa.
    pose proof (kimg_clear (ENVG vals) MV kn 0x13bea0 0x13c580 HK (KB (KImg 0x13bea0 0x13c580) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLb.
    assert (ICa : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bcc8 <=? a) && (a + Z.of_nat n <=? 0x13bdb8) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLa. lia. }
    assert (ICb : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bea0 <=? a) && (a + Z.of_nat n <=? 0x13c580) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLb. lia. }
    unfold exitSB. split; [|split; [|split]].
    - unfold cells_at, XC_CELLS_SB.
      constructor; [exact (kword_lit sp0 _ MV kn 6897520 4%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6897520) 4 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6897555 1%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6897555) 1 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6896992 8 6897000 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6896984 4 8 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897008 8 1148964 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897264 8 619876 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6896980 4 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897000 8 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6898952 8%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6898952) 8 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (ICb 1294224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293992)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294132 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1293984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293752)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293512)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293652 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897016 8 1148964 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897272 8 687916 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6759060 1%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6759060) 1 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6759112 1 16 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6759144 1 6 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897024 8 874172 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897032 8 449180 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897040 8 874172 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897048 8 449180 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897056 8 872740 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897064 8 449180 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897280 8 6759112 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897288 8 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897296 8 6759144 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897304 8 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897312 8 1293304 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXsc 6897320 8 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor.
    - rewrite Z_to_bv_bv_unsigned. exact (kword_lit sp0 _ MV kn 6765656 4%nat (EVar 4) HK (KB (KWord (SA (ELit 0) 6765656) 4 (EVar 4)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)).
    - pose proof (KB (KRange (EVar 4) 1 4194303) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) as Hb.
      apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
      pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok edenot ev ENVA] in X. exact X.
    - intros i Hi. apply CLb. lia.
  Qed.
  #[using="sp0 Hsp CAP HCAP LEN CFG PL"] Lemma exitf_ax_BS : forall vals (MV : word -> option byte) kn,
    know_ok ASEGS (ENVG vals) MV kn -> forallb (fun K => existsb (kentry_eqb K) kn) XKN_X = true -> atexit_cellsA MV AXcs ->
    exitBS (bv_unsigned (vals_ev vals 4)) MV.
  Proof.
    intros vals MV kn HK HB HAX. rewrite forallb_forall in HB.
    assert (KB : forall K, In K XKN_X -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (HB K HKin)).
    pose proof (kimg_clear (ENVG vals) MV kn 0x13bcc8 0x13bdb8 HK (KB (KImg 0x13bcc8 0x13bdb8) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLa.
    pose proof (kimg_clear (ENVG vals) MV kn 0x13bea0 0x13c580 HK (KB (KImg 0x13bea0 0x13c580) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto))) as CLb.
    assert (ICa : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bcc8 <=? a) && (a + Z.of_nat n <=? 0x13bdb8) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLa. lia. }
    assert (ICb : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bea0 <=? a) && (a + Z.of_nat n <=? 0x13c580) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLb. lia. }
    unfold exitBS. split; [|split; [|split]].
    - unfold cells_at, XC_CELLS_BS.
      constructor; [exact (kword_lit sp0 _ MV kn 6897520 4%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6897520) 4 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6897555 1%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6897555) 1 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6896992 8 6897000 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6896984 4 8 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897008 8 1148964 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897264 8 619876 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6896980 4 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897000 8 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6898952 8%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6898952) 8 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (ICb 1294224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293992)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294132 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1294008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICb 1293984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293752)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1293512)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293652 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (ICa 1293528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897016 8 1148964 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897272 8 687916 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (kword_lit sp0 _ MV kn 6759060 1%nat (ELit 0) HK (KB (KWord (SA (ELit 0) 6759060) 1 (ELit 0)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6759112 1 16 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6759144 1 6 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897024 8 872740 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897032 8 449180 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897040 8 874172 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897048 8 449180 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897056 8 874172 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897064 8 449180 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897280 8 1293304 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897288 8 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897296 8 6759112 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897304 8 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897312 8 6759144 HAX ltac:(vm_compute; reflexivity))|].
      constructor; [exact (atexit_cellsA_atb MV AXcs 6897320 8 0 HAX ltac:(vm_compute; reflexivity))|].
      constructor.
    - rewrite Z_to_bv_bv_unsigned. exact (kword_lit sp0 _ MV kn 6765656 4%nat (EVar 4) HK (KB (KWord (SA (ELit 0) 6765656) 4 (EVar 4)) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)).
    - pose proof (KB (KRange (EVar 4) 1 4194303) ltac:(unfold XKN_X; cbn [In map XC9_CELLS app fst snd]; tauto)) as Hb.
      apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
      pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok edenot ev ENVA] in X. exact X.
    - intros i Hi. apply CLb. lia.
  Qed.
  #[using="scfg L C IL HIok Hsp DL CAP HCAP LEN CFG PL"] Lemma EXITFX : forall (ax : axv) vals LB LK cr A M (model : Model),
    know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) (kn_after rT3A knF2A) -> dinvA LB LK cr A M model -> atexit_cellsA M ax ->
    exit_of ax (bv_unsigned (vals_ev vals 4)) (mrestrict (ahid A model) M).
  Proof.
    intros ax vals LB LK cr A M model HK D HAX. pose proof (ax_cells_vis scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model ax D HAX) as HV.
    destruct ax; cbn [exit_of]; [exact (exitf_ax_A vals _ _ HK ltac:(vm_compute; reflexivity) HV) | exact (exitf_ax_B vals _ _ HK ltac:(vm_compute; reflexivity) HV) | exact (exitf_ax_S vals _ _ HK ltac:(vm_compute; reflexivity) HV) | exact (exitf_ax_BS vals _ _ HK ltac:(vm_compute; reflexivity) HV) | exact (exitf_ax_SB vals _ _ HK ltac:(vm_compute; reflexivity) HV)].
  Qed.

  #[using="Type"] Lemma fds0_lookup1 : fd_lookup fds0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="L C IL HIok ICok Hsp Hal DL CAP HCAP ILY Hex LEN CFG PL"] Lemma tail_FA : forall (fx' : PropExec.FPState) (j : nat) (ax : axv) vals R M (model : Model) A LK cr,
    length vals = 230%nat -> hdr_valsA sp0 p0 p1 can vals -> (j <= 3)%nat ->
    regs_ok (ENVG vals) srF2A R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knF2A ->
    dinvA [] LK cr A M model -> m_fds model = fds0 -> m_fs model = fs0 ->
    stdoutA (Z.of_nat j) (mrestrict (ahid A model) M) -> stdoutXA (mrestrict (ahid A model) M) -> atexit_cellsA M ax ->
    srealizes ASEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0xa7d00) M (seg_rom ASEGS)) model) (EA j).
  Proof.
    intros fx' j ax vals R M model A LK cr HL HV Hj HR HK DI F1 F2 SO SOX HAX.
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
    destruct ax.
    { (* [comment removed for export] *)
      assert (XP : exit_pre ar HI sp0 M0 [] LK cr A M model0 S (bv_unsigned (vals_ev vals 4))).
      { unfold exit_pre. split; [exact DI0|]. split; [unfold S; lia|]. split; [unfold S; lia|].
        split; [exact HS16|].
        split; [intros a n Ha Hn d k Hd Hk; exact (stk_wr sp0 Hsp vals _ MV _ a n HK0 ltac:(vm_compute; reflexivity) P0 Ha Hn d k Hd Hk)|].
        split; [exact (kimg_clear _ MV _ 65536 1282048 HK0 ltac:(vm_compute; reflexivity))|].
        exact (EXITFX AX0 vals [] LK cr A M model0 HK0 DI0 HAX). }
      assert (G1r : getr R0 1%bv = Z_to_bv 64 1147060) by (regv HR0 (1%bv : reg); reflexivity).
      assert (G2r : getr R0 2%bv = Z_to_bv 64 S).
      { regv HR0 (2%bv : reg). cbn [edenot ev ENVA]. rewrite P0. unfold S. apply alu_add_w_litA. }
      assert (G4r : getr R0 4%bv = Z_to_bv 64 6765824) by (regv HR0 (4%bv : reg); reflexivity).
      assert (G10r : getr R0 10%bv = Z_to_bv 64 0) by (regv HR0 (10%bv : reg); reflexivity).
      assert (FD1 : fd_lookup (m_fds model0) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) by (rewrite G1; exact fds0_lookup1).
      assert (CANc : rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned can)))).
      { rewrite Z_to_bv_bv_unsigned, <- P3. exact (kword_lit sp0 _ MV _ 6896960 8%nat (EVar 3) HK0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)). }
      unfold EA, exit_code. rewrite <- G2.
      destruct j as [|[|[|[|j]]]]; [| | | | lia].
      - eapply srz_conseq; [|apply t_eq_sym; apply t_emit_W_nil; apply t_exit_has_nil].
        exact (exit_run_0 scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ XP ltac:(lia) G1r G2r G4r G10r SO SOX).
      - exact (exit_run_2 scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      - exact (exit_run_3 scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      - exact (exit_run_4 scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
    }
    { (* [comment removed for export] *)
      assert (XP : exit_preB ar HI sp0 M0 [] LK cr A M model0 S (bv_unsigned (vals_ev vals 4))).
      { unfold exit_preB. split; [exact DI0|]. split; [unfold S; lia|]. split; [unfold S; lia|].
        split; [exact HS16|].
        split; [intros a n Ha Hn d k Hd Hk; exact (stk_wr sp0 Hsp vals _ MV _ a n HK0 ltac:(vm_compute; reflexivity) P0 Ha Hn d k Hd Hk)|].
        split; [exact (kimg_clear _ MV _ 65536 1282048 HK0 ltac:(vm_compute; reflexivity))|].
        exact (EXITFX AXc vals [] LK cr A M model0 HK0 DI0 HAX). }
      assert (G1r : getr R0 1%bv = Z_to_bv 64 1147060) by (regv HR0 (1%bv : reg); reflexivity).
      assert (G2r : getr R0 2%bv = Z_to_bv 64 S).
      { regv HR0 (2%bv : reg). cbn [edenot ev ENVA]. rewrite P0. unfold S. apply alu_add_w_litA. }
      assert (G4r : getr R0 4%bv = Z_to_bv 64 6765824) by (regv HR0 (4%bv : reg); reflexivity).
      assert (G10r : getr R0 10%bv = Z_to_bv 64 0) by (regv HR0 (10%bv : reg); reflexivity).
      assert (FD1 : fd_lookup (m_fds model0) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) by (rewrite G1; exact fds0_lookup1).
      assert (CANc : rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned can)))).
      { rewrite Z_to_bv_bv_unsigned, <- P3. exact (kword_lit sp0 _ MV _ 6896960 8%nat (EVar 3) HK0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)). }
      unfold EA, exit_code. rewrite <- G2.
      destruct j as [|[|[|[|j]]]]; [| | | | lia].
      - eapply srz_conseq; [|apply t_eq_sym; apply t_emit_W_nil; apply t_exit_has_nil].
        exact (exit_run_0B scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ XP ltac:(lia) G1r G2r G4r G10r SO SOX).
      - exact (exit_run_2B scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      - exact (exit_run_3B scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      - exact (exit_run_4B scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
    }
    { (* [comment removed for export] *)
      assert (XP : exit_preS ar HI sp0 M0 [] LK cr A M model0 S (bv_unsigned (vals_ev vals 4))).
      { unfold exit_preS. split; [exact DI0|]. split; [unfold S; lia|]. split; [unfold S; lia|].
        split; [exact HS16|].
        split; [intros a n Ha Hn d k Hd Hk; exact (stk_wr sp0 Hsp vals _ MV _ a n HK0 ltac:(vm_compute; reflexivity) P0 Ha Hn d k Hd Hk)|].
        split; [exact (kimg_clear _ MV _ 65536 1282048 HK0 ltac:(vm_compute; reflexivity))|].
        exact (EXITFX AXs vals [] LK cr A M model0 HK0 DI0 HAX). }
      assert (G1r : getr R0 1%bv = Z_to_bv 64 1147060) by (regv HR0 (1%bv : reg); reflexivity).
      assert (G2r : getr R0 2%bv = Z_to_bv 64 S).
      { regv HR0 (2%bv : reg). cbn [edenot ev ENVA]. rewrite P0. unfold S. apply alu_add_w_litA. }
      assert (G4r : getr R0 4%bv = Z_to_bv 64 6765824) by (regv HR0 (4%bv : reg); reflexivity).
      assert (G10r : getr R0 10%bv = Z_to_bv 64 0) by (regv HR0 (10%bv : reg); reflexivity).
      assert (FD1 : fd_lookup (m_fds model0) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) by (rewrite G1; exact fds0_lookup1).
      assert (CANc : rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned can)))).
      { rewrite Z_to_bv_bv_unsigned, <- P3. exact (kword_lit sp0 _ MV _ 6896960 8%nat (EVar 3) HK0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)). }
      unfold EA, exit_code. rewrite <- G2.
      destruct j as [|[|[|[|j]]]]; [| | | | lia].
      - eapply srz_conseq; [|apply t_eq_sym; apply t_emit_W_nil; apply t_exit_has_nil].
        exact (exit_run_0S scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ XP ltac:(lia) G1r G2r G4r G10r SO SOX).
      - exact (exit_run_2S scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      - exact (exit_run_3S scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      - exact (exit_run_4S scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
    }
    { (* [comment removed for export] *)
      assert (XP : exit_preBS ar HI sp0 M0 [] LK cr A M model0 S (bv_unsigned (vals_ev vals 4))).
      { unfold exit_preBS. split; [exact DI0|]. split; [unfold S; lia|]. split; [unfold S; lia|].
        split; [exact HS16|].
        split; [intros a n Ha Hn d k Hd Hk; exact (stk_wr sp0 Hsp vals _ MV _ a n HK0 ltac:(vm_compute; reflexivity) P0 Ha Hn d k Hd Hk)|].
        split; [exact (kimg_clear _ MV _ 65536 1282048 HK0 ltac:(vm_compute; reflexivity))|].
        exact (EXITFX AXcs vals [] LK cr A M model0 HK0 DI0 HAX). }
      assert (G1r : getr R0 1%bv = Z_to_bv 64 1147060) by (regv HR0 (1%bv : reg); reflexivity).
      assert (G2r : getr R0 2%bv = Z_to_bv 64 S).
      { regv HR0 (2%bv : reg). cbn [edenot ev ENVA]. rewrite P0. unfold S. apply alu_add_w_litA. }
      assert (G4r : getr R0 4%bv = Z_to_bv 64 6765824) by (regv HR0 (4%bv : reg); reflexivity).
      assert (G10r : getr R0 10%bv = Z_to_bv 64 0) by (regv HR0 (10%bv : reg); reflexivity).
      assert (FD1 : fd_lookup (m_fds model0) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) by (rewrite G1; exact fds0_lookup1).
      assert (CANc : rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned can)))).
      { rewrite Z_to_bv_bv_unsigned, <- P3. exact (kword_lit sp0 _ MV _ 6896960 8%nat (EVar 3) HK0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)). }
      unfold EA, exit_code. rewrite <- G2.
      destruct j as [|[|[|[|j]]]]; [| | | | lia].
      - eapply srz_conseq; [|apply t_eq_sym; apply t_emit_W_nil; apply t_exit_has_nil].
        exact (exit_run_0BS scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ XP ltac:(lia) G1r G2r G4r G10r SO SOX).
      - exact (exit_run_2BS scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      - exact (exit_run_3BS scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      - exact (exit_run_4BS scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
    }
    { (* [comment removed for export] *)
      assert (XP : exit_preSB ar HI sp0 M0 [] LK cr A M model0 S (bv_unsigned (vals_ev vals 4))).
      { unfold exit_preSB. split; [exact DI0|]. split; [unfold S; lia|]. split; [unfold S; lia|].
        split; [exact HS16|].
        split; [intros a n Ha Hn d k Hd Hk; exact (stk_wr sp0 Hsp vals _ MV _ a n HK0 ltac:(vm_compute; reflexivity) P0 Ha Hn d k Hd Hk)|].
        split; [exact (kimg_clear _ MV _ 65536 1282048 HK0 ltac:(vm_compute; reflexivity))|].
        exact (EXITFX AXsc vals [] LK cr A M model0 HK0 DI0 HAX). }
      assert (G1r : getr R0 1%bv = Z_to_bv 64 1147060) by (regv HR0 (1%bv : reg); reflexivity).
      assert (G2r : getr R0 2%bv = Z_to_bv 64 S).
      { regv HR0 (2%bv : reg). cbn [edenot ev ENVA]. rewrite P0. unfold S. apply alu_add_w_litA. }
      assert (G4r : getr R0 4%bv = Z_to_bv 64 6765824) by (regv HR0 (4%bv : reg); reflexivity).
      assert (G10r : getr R0 10%bv = Z_to_bv 64 0) by (regv HR0 (10%bv : reg); reflexivity).
      assert (FD1 : fd_lookup (m_fds model0) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) by (rewrite G1; exact fds0_lookup1).
      assert (CANc : rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned can)))).
      { rewrite Z_to_bv_bv_unsigned, <- P3. exact (kword_lit sp0 _ MV _ 6896960 8%nat (EVar 3) HK0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)). }
      unfold EA, exit_code. rewrite <- G2.
      destruct j as [|[|[|[|j]]]]; [| | | | lia].
      - eapply srz_conseq; [|apply t_eq_sym; apply t_emit_W_nil; apply t_exit_has_nil].
        exact (exit_run_0SB scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ XP ltac:(lia) G1r G2r G4r G10r SO SOX).
      - exact (exit_run_2SB scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      - exact (exit_run_3SB scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
      - exact (exit_run_4SB scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 [] LK cr A M model0 R0 S 0 _ (bv_unsigned can) XP ltac:(lia) (u64_range _) G1r G2r G4r G10r CANc SO SOX FD1).
    }
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma wseg_sofile : wseg_ok ASEGS (Z_to_bv 64 1293752) 232 = true.  Proof. vm_compute. reflexivity. Qed.
  #[using="Type"] Lemma wseg_sobuf : wseg_ok ASEGS (Z_to_bv 64 SOBUF) 1024 = true.  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="sp0 Hsp fdata LEN CFG PL"] Lemma stdout_agree : forall j (MV MV' : word -> option byte), stdoutA j MV -> stdoutXA MV -> 0 <= j <= 500 ->
    (forall a, 1293752 <= a < 1293752 + 232 \/ SOBUF <= a < SOBUF + 1024 -> MV' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
    stdoutA j MV' /\ stdoutXA MV'.
  Proof.
    intros j MV MV' (F1 & F2 & F3 & F4 & F5 & F6 & F7 & FW & BW & BC) (X1 & X2 & X3 & X4 & X5) Hj AG.
    assert (TR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> 1293752 <= a -> a + Z.of_nat n <= 1293752 + 232 -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr H1 H2. apply (rdn_tr MV MV' a n bs Hr); [lia | lia|]. intros i Hi. apply AG. left. lia. }
    assert (TRB : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> SOBUF <= a -> a + Z.of_nat n <= SOBUF + 1024 -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr H1 H2. apply (rdn_tr MV MV' a n bs Hr); [unfold SOBUF in *; lia | unfold SOBUF in *; lia|]. intros i Hi. apply AG. right. lia. }
    split.
    - unfold stdoutA. repeat split; try (apply TR; [assumption | cbn; lia | cbn; lia]).
      + intros a n H1 H2 d k Hd Hk. apply (store_ok_window ASEGS MV' (Z_to_bv 64 1293752) (Z_to_bv 64 (a + d)) 232%nat k 1293752 (1293752 + 232));
          first [exact wseg_sofile | reflexivity | lia | (rewrite u_small by lia; lia)].
      + intros a n H1 H2 d k Hd Hk. apply (store_ok_window ASEGS MV' (Z_to_bv 64 SOBUF) (Z_to_bv 64 (a + d)) 1024%nat k SOBUF (SOBUF + 1024));
          first [exact wseg_sobuf | reflexivity | (unfold SOBUF in *; lia) | (rewrite u_small by (unfold SOBUF in *; lia); unfold SOBUF in *; lia)].
      + destruct (BC i H) as (B1 & _). apply TRB; [exact B1 | lia | cbn; lia].
      + destruct (BC i H) as (_ & B2). apply TRB; [exact B2 | lia | cbn; lia].
    - unfold stdoutXA. repeat split; apply TR; first [assumption | cbn; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="sp0 Hsp fdata LEN CFG PL"] Lemma stdout0_of_kn : forall E (MV : word -> option byte) kn, know_ok ASEGS E MV kn -> existsb (kentry_eqb (KImg 0x13bdb8 0x13bea0)) kn = true -> stdout0A MV.
  Proof.
    intros E MV kn HK Hb. pose proof (kimg_clear E MV kn 0x13bdb8 0x13bea0 HK Hb) as CL.
    assert (IC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bdb8 <=? a) && (a + Z.of_nat n <=? 0x13bea0) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CL. lia. }
    unfold stdout0A.
    split; [exact (IC 1293892 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|]. split; [exact (IC 1293752 4%nat (word_to_le_bytes 4 (Z_to_bv 64 5)) ltac:(img_rd) eq_refl)|].
    split; [exact (IC 1293848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1024)) ltac:(img_rd) eq_refl)|]. split; [exact (IC 1293784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
    split; [exact (IC 1293888 4%nat (word_to_le_bytes 4 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|]. split; [exact (IC 1293840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 SOBUF)) ltac:(img_rd) eq_refl)|].
    split; [exact (IC 1293896 4%nat (word_to_le_bytes 4 (Z_to_bv 64 10)) ltac:(img_rd) eq_refl)|]. split; [exact (IC 1293824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1183420)) ltac:(img_rd) eq_refl)|].
    split; [exact (IC 1293872 4%nat (word_to_le_bytes 4 (Z_to_bv 64 1)) ltac:(img_rd) eq_refl)|].
    split.
    - intros a n H1 H2 d k Hd Hk. apply (store_ok_window ASEGS MV (Z_to_bv 64 1293752) (Z_to_bv 64 (a + d)) 232%nat k 1293752 (1293752 + 232));
        first [exact wseg_sofile | reflexivity | lia | (rewrite u_small by lia; lia)].
    - intros a n H1 H2 d k Hd Hk. apply (store_ok_window ASEGS MV (Z_to_bv 64 SOBUF) (Z_to_bv 64 (a + d)) 1024%nat k SOBUF (SOBUF + 1024));
        first [exact wseg_sobuf | reflexivity | (unfold SOBUF in *; lia) | (rewrite u_small by (unfold SOBUF in *; lia); unfold SOBUF in *; lia)].
  Qed.

  (* [comment removed for export] *)
  #[using="scfg L C IL HIok Hsp DL fdata LEN CFG PL"] Lemma stdout_call_g : forall (IMG : list (Z * Z)) j LB LK cr A M (model : Model) LB' LK' cr' A' M' (model' : Model),
    In (0x13bbe0, 0x13c580) IMG -> (exists w2, In (w2, 0x6951b8) IMG /\ w2 <= 0x694520) ->
    dinvA LB LK cr A M model -> dinvA LB' LK' cr' A' M' model' -> 0 <= j <= 500 ->
    (forall lo hi a, In (lo, hi) IMG -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    stdoutA j (mrestrict (ahid A model) M) -> stdoutXA (mrestrict (ahid A model) M) ->
    stdoutA j (mrestrict (ahid A' model') M') /\ stdoutXA (mrestrict (ahid A' model') M').
  Proof.
    intros IMG j LB LK cr A M model LB' LK' cr' A' M' model' I1 I2 D D' Hj FR SO SOX.
    apply (stdout_agree j _ _ SO SOX Hj). intros a Ha. unfold mrestrict.
    rewrite (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ a D) by (unfold SOBUF in Ha; lia).
    rewrite (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ a D') by (unfold SOBUF in Ha; lia).
    destruct Ha as [Ha|Ha].
    - apply (FR 0x13bbe0 0x13c580); [exact I1 | lia].
    - destruct I2 as (w2 & I2 & Hw2). apply (FR w2 0x6951b8); [exact I2 | unfold SOBUF in Ha; lia].
  Qed.
  (* [comment removed for export] *)
  Definition stdout_call := stdout_call_g IMG_CLIENT_A.
  Definition stdout_lib := stdout_call_g IMG_LIB_A.
  #[using="sp0 Hsp CAP HCAP"] Lemma in_client_1 : In (0x13bbe0, 0x13c580) IMG_CLIENT_A.  Proof. unfold IMG_CLIENT_A; cbn [In]; tauto. Qed.
  #[using="sp0 Hsp CAP HCAP"] Lemma in_client_2 : In (0x673d30, 0x6951b8) IMG_CLIENT_A.  Proof. unfold IMG_CLIENT_A; cbn [In]; tauto. Qed.
  #[using="sp0 Hsp CAP HCAP"] Lemma in_client_3 : In (0x662290, 0x673ca8) IMG_CLIENT_A.  Proof. unfold IMG_CLIENT_A; cbn [In]; tauto. Qed.
  #[using="sp0 Hsp CAP HCAP"] Lemma in_lib_1 : In (0x13bbe0, 0x13c580) IMG_LIB_A.  Proof. unfold IMG_LIB_A; cbn [In]; tauto. Qed.
  #[using="sp0 Hsp CAP HCAP"] Lemma in_lib_2 : In (0x693f70, 0x6951b8) IMG_LIB_A.  Proof. unfold IMG_LIB_A; cbn [In]; tauto. Qed.
  #[using="sp0 Hsp CAP HCAP"] Lemma in_client_2x : exists w2, In (w2, 0x6951b8) IMG_CLIENT_A /\ w2 <= 0x694520.  Proof. exists 0x673d30. split; [unfold IMG_CLIENT_A; cbn [In]; tauto | apply Z.leb_le; reflexivity]. Qed.
  #[using="sp0 Hsp CAP HCAP"] Lemma in_lib_2x : exists w2, In (w2, 0x6951b8) IMG_LIB_A /\ w2 <= 0x694520.  Proof. exists 0x693f70. split; [unfold IMG_LIB_A; cbn [In]; tauto | apply Z.leb_le; reflexivity]. Qed.

  (* [comment removed for export] *)
  #[using="L C IL HIok ICok Hsp Hal DL M0_def HCAP ILY Hex LEN CFG PL"] Lemma tail_MA : forall (fx' : PropExec.FPState) (j : nat) (ax : axv) vals R M (model : Model) A (A1 : Z) LK cr,
    length vals = 198%nat -> hdr_valsA sp0 p0 p1 can vals -> vals_ev vals 48 = Z_to_bv 64 A1 -> (j <= 3)%nat ->
    regs_ok (ENVG vals) srF1A R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knF1A ->
    dinvA [(A1, CAP)] LK cr A M model -> m_fds model = fds0 -> m_fs model = fs0 ->
    stdoutA (Z.of_nat j) (mrestrict (ahid A model) M) -> stdoutXA (mrestrict (ahid A model) M) -> atexit_cellsA M ax ->
    srealizes ASEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0xa7ecc) M (seg_rom ASEGS)) model) (EA j).
  Proof.
    intros fx' j ax vals R M model A A1 LK cr HL HV P48 Hj HR HK DI F1 F2 SO SOX HAX.
    pose proof HV as (P0 & _). pose proof Hsp as Hsp'.
    (* [comment removed for export] *)
    drv_blockT0 HIok Hsp DL HR HK DI P0 scr0 198%nat.
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
    pose proof (ahid_sbm A model model0 SBM) as AH. rewrite <- AH in SO, SOX.
    clear HR HK DI EQM EQH EQA SBM AH F1 F2. rename R0 into R1, HR0 into HR, HK0 into HK, DI0 into DI, model0 into model1.
    (* [comment removed for export] *)
    assert (FREEB : forall (fxq : PropExec.FPState) srX knX Rq Mq (modelq : Model) Aq,
              regs_ok (ENVG vals) srX Rq -> know_ok ASEGS (ENVG vals) (mrestrict (ahid Aq modelq) Mq) knX ->
              sr_vars_lt 198 srX = true -> kn_vars_lt 198 knX = true -> has_window knX = true ->
              sr_after_call_j srX (map ridx c_kept) 198 = srF2A -> ksubl_b (keep_allocA MSO 4096 [] [] knX) knF2A = true ->
              (nth 1 srX (ELit 0), nth 2 srX (ELit 0), nth 4 srX (ELit 0), nth 10 srX (ELit 0)) = (ELit 0xa7d00, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 6765824, EVar 48) ->
              dinvA [(A1, CAP)] LK cr Aq Mq modelq -> m_fds modelq = fds0 -> m_fs modelq = fs0 ->
              stdoutA (Z.of_nat j) (mrestrict (ahid Aq modelq) Mq) -> stdoutXA (mrestrict (ahid Aq modelq) Mq) -> atexit_cellsA Mq ax ->
              srealizes ASEGS scfg (mkCfg (@mkst fxq Rq (Z_to_bv 64 0x79814) Mq (seg_rom ASEGS)) modelq) (EA j)).
    { intros fxq srX knX Rq Mq modelq Aq HRq HKq SV KV HW ESR EKN ENTH DIq F1q F2q SOq SOXq HAXq.
      injection ENTH as N1 N2 N4 N10.
      apply (@afree_site fxq scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals _ srX knX Rq Mq modelq [(A1, CAP)] LK cr Aq A1 CAP MSO [] [] 0xa7d00 (EA j) HRq HKq).
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
        destruct (stdout_call (Z.of_nat j) _ _ _ _ _ _ _ _ _ _ _ _ in_client_1 in_client_2x DIq DI' ltac:(lia) FRc SOq SOXq) as (SO' & SOX').
        apply (tail_FA fxq j ax vals' R' M' model' A' LK cr HL').
        + subst vals'. apply (hdr_appA sp0 fdata); [exact HV | rewrite HL; lia].
        + exact Hj.
        + exact HR'.
        + eapply ksubl_sound; [exact HK' | exact EKN].
        + exact DI'.
        + exact Q1.
        + exact Q2.
        + exact SO'.
        + exact SOX'.
        + exact (atexit_cellsA_frame Mq M' ax (fun a Ha => FRc _ _ a in_client_2 ltac:(unfold AXLO, AXHI in Ha; lia)) (fun a Ha => FRc _ _ a in_client_3 ltac:(unfold SSLO, SSHI in Ha; lia)) HAXq). }
    destruct (branch_taken BC_LT (vals_ev vals 74) (Z_to_bv 64 0)) eqn:BT.
    - drv_block0 HIok Hsp DL HR HK DI P0 (SCR [true] [] []) 198%nat.
      { cbn [sc_denot edenot ev ENVA]. exact BT. }
      pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
      assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
      destruct (sbm_fds _ _ SBM) as (Q1 & Q2). rewrite G1 in Q1. rewrite G2 in Q2.
      pose proof (ahid_sbm A model1 model0 SBM) as AH. rewrite <- AH in SO, SOX.
      apply (FREEB fx' _ _ R0 M model0 A HR0 HK0); first [exact DI0 | exact Q1 | exact Q2 | exact SO | exact SOX | exact HAX | (vm_compute; reflexivity)].
    - drv_block0 HIok Hsp DL HR HK DI P0 (SCR [false] [] []) 198%nat.
      { cbn [sc_denot edenot ev ENVA]. exact BT. }
      pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
      assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
      destruct (sbm_fds _ _ SBM) as (Q1 & Q2). rewrite G1 in Q1. rewrite G2 in Q2.
      pose proof (ahid_sbm A model1 model0 SBM) as AH. rewrite <- AH in SO, SOX.
      apply (FREEB fx' _ _ R0 M model0 A HR0 HK0); first [exact DI0 | exact Q1 | exact Q2 | exact SO | exact SOX | exact HAX | (vm_compute; reflexivity)].
  Qed.

  (* [comment removed for export] *)
  #[using="C IL HIok Hsp Hal DL M0_def FNULL"] Lemma afree_null_siteA : forall (fxq : PropExec.FPState) vals ebs sr kn R M (model : Model) LB LK cr A so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true -> (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> has_window kn = true ->
    getr R 2%bv = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    getr R 10%bv = Z_to_bv 64 0 -> getr R 4%bv = Z_to_bv 64 0x673d00 -> getr R 1%bv = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
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
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0x79814) M (seg_rom ASEGS)) model) K.
  Proof. intros fxq. exact (@afree_null_site fxq scfg L ar C IL HI HIok FNULL sp0 Hsp Hal DL M0 M0_def). Qed.

  (* [comment removed for export] *)
  #[using="C IL HIok ICok Hsp Hal DL M0_def HCAP ILY Hex FNULL LSXA"] Lemma tail_XA : forall j : nat, SSPA 1 (Z.of_nat j) (EA j).
  Proof.
    intros j. unfold SSPA.
    intros fx' vals R M model A A1 PTR OWN LB LK cr g (HL & HV & P48 & P70 & P73 & P79 & P81 & P82 & P83) Hk Hj Hjk HR HK
           (HBLK & HC & HPAY & DI & HINC & F1 & F2 & SO & SOX & HLS & HROOM).
    destruct (LSXA g M HLS) as [ax HAX].      (* [comment removed for export] *)
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
    assert (R4q : getr R0 4%bv = Z_to_bv 64 0x673d00) by (regv HR0 (4%bv : reg); reflexivity).
    assert (R1q : getr R0 1%bv = Z_to_bv 64 0xa7ecc) by (regv HR0 (1%bv : reg); reflexivity).
    assert (SUB : forall LBx, In (A1, CAP) LBx -> forall i nb, find_nz i [(48%nat, 65536)] = Some nb -> (i < length vals)%nat /\ sub_blockA L ar LBx (bv_unsigned (vals_ev vals i)) nb).
    { intros LBx Hin i nb Hf. cbn [find_nz] in Hf. destruct (Nat.eqb i 48) eqn:E48; [|discriminate Hf]. apply Nat.eqb_eq in E48. subst i. injection Hf as <-.
      split; [rewrite HL; lia|]. rewrite P48. pose proof HBR as (B1 & _ & _ & _ & _ & (_ & _ & B47)). rewrite u_small by lia. exists CAP. split; [lia|]. split; [exact Hin | exact HBR]. }
    (* [comment removed for export] *)
    assert (KONT : forall R' M' (model' : Model) A',
              let vals' := vals ++ junk_vals R' in
              length vals' = (length vals + 32)%nat ->
              regs_ok (ENVG vals') (sr_after_call_j srSf2A (map ridx c_kept) (length vals)) R' ->
              know_ok ASEGS (ENVG vals') (mrestrict (ahid A' model') M') (keep_allocA TSO 4096 [(48%nat, 65536)] [] (kn_after rSf2A knLH2A)) ->
              dinvA [(A1, CAP)] LK cr A' M' model' -> model_rt model0 model' ->
              (forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
              srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xa7ecc) M' (seg_rom ASEGS)) model') (EA j)).
    { intros R' M' model' A' vals' HL' HR' HK' DI' MRT FRc. rewrite HL in HL', HR'.
      destruct (model_rt_fds _ _ MRT) as (Q1 & Q2). rewrite G1 in Q1. rewrite G2 in Q2.
      destruct (stdout_call (Z.of_nat j) _ _ _ _ _ _ _ _ _ _ _ _ in_client_1 in_client_2x DI0 DI' ltac:(lia) FRc SO SOX) as (SO' & SOX').
      apply (tail_MA fx' j ax vals' R' M' model' A' A1 LK cr HL').
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
      - exact (atexit_cellsA_frame M M' ax (fun a Ha => FRc _ _ a in_client_2 ltac:(unfold AXLO, AXHI in Ha; lia)) (fun a Ha => FRc _ _ a in_client_3 ltac:(unfold SSLO, SSHI in Ha; lia)) HAX). }
    destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)]; subst LB.
    - (* [comment removed for export] *)
      subst OWN.
      apply (afree_null_siteA fx' vals _ srSf2A (kn_after rSf2A knLH2A) R0 M model0 [(A1, CAP)] LK cr A TSO [(48%nat, 65536)] [] 0xa7ecc (EA j) HR0 HK0);
        [ rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia | exact P0 | vm_compute; reflexivity | exact R2q | unfold TSO; lia | reflexivity
        | exact R10q | exact R4q | exact R1q | lia | reflexivity | exact DI0 | apply SUB; left; reflexivity | intros v b Hf; discriminate Hf | unfold EA; apply t_emit_has_nil | ].
      intros R' M' model' A' vals' E' HL' HR' HK' DI' MRT _ _ _ FRc. exact (KONT R' M' model' A' HL' HR' HK' DI' MRT FRc).
    - (* [comment removed for export] *)
      apply (@afree_site fx' scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals _ srSf2A (kn_after rSf2A knLH2A) R0 M model0 [(OWN, PL); (A1, CAP)] LK cr A OWN PL TSO
               [(48%nat, 65536)] [] 0xa7ecc (EA j) HR0 HK0);
        [ rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia | exact P0 | vm_compute; reflexivity | exact R2q | unfold TSO; lia | reflexivity
        | left; reflexivity | exact R10q | exact R4q | exact R1q | lia | reflexivity | exact DI0 | rewrite lb_remove_hdA; apply SUB; left; reflexivity | intros v b Hf; discriminate Hf
        | unfold EA; apply t_emit_has_nil | ].
      intros R' M' model' A' vals' E' HL' HR' HK' DI' MRT _ _ _ FRc. rewrite lb_remove_hdA in DI'. exact (KONT R' M' model' A' HL' HR' HK' DI' MRT FRc).
  Qed.
End DrvE.
End FPX_1.
