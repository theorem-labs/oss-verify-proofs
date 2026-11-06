(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmHdr LbA_PmCall LbA_PmXp LbA_DiagStmt LbA_PmDS LbA_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition RT_HEX : list (reg * expr) :=
  [(1%bv, ELit 973988); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, ELit 2147450880); (19%bv, EVar 38);
   (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (22%bv, EAlu ALU_ADD (EVar 33) (ELit 14672));
   (23%bv, EAlu ALU_ADD (EVar 33) (ELit 13584)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 13200));
   (25%bv, EAlu ALU_ADD (EVar 33) (ELit 13264)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 13136));
   (27%bv, EAlu ALU_ADD (EVar 32) (ELit 56))].

Definition RT_HEXCALL : list (reg * expr) :=
  [(1%bv, ELit 974120); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 14672));
   (18%bv, ELit 2147450880); (19%bv, EVar 38); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880));
   (22%bv, EAlu ALU_ADD (EVar 33) (ELit 14672)); (23%bv, EAlu ALU_ADD (EVar 33) (ELit 13584));
   (24%bv, EAlu ALU_ADD (EVar 33) (ELit 13200)); (25%bv, EAlu ALU_ADD (EVar 33) (ELit 13264));
   (26%bv, EAlu ALU_ADD (EVar 33) (ELit 13136)); (27%bv, EAlu ALU_ADD (EVar 32) (ELit 56))].
Definition TBL_BM : list (Z * expr) :=
  [(1056, EVar 33); (968, EVar 33); (1040, EVar 33);
   (1048, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880));
   (1008, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880));
   (1000, EAlu ALU_ADD (EVar 32) (ELit 48))].
Definition BM_INS : list nat := [86; 87]%nat.

Definition KHEX : list kentry :=
  [KWord (SA (EVar WV_FF) 14672) 8 (EVar 41);
   KWord (SA (EVar 41) (-24)) 8 (ELit 112);
   KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 41) (ELit (-24))) (ELit 3)) 2147450880) 1 (ELit 0);
   KWord (SA (EVar WV_FF) 14792) 4 (EVar 42);
   KDisj (SA (EVar WV_WORDS) 0) (ELit 20) (SA (EVar WV_S1) PM_RF_LO) (ELit (1216 - PM_RF_LO));
   KDisj (SA (EVar WV_WORDS) 0) (ELit 20) (SA (EVar WV_FF) 0) (ELit 16384)].

Lemma sh0_of_acc8 : forall m a, accessible m a 8 -> sh0 m a.
Proof.
  intros m a (A0 & A1 & AC).
  assert (Hx : a <= a + (7 - a mod 8) < a + 8) by (pose proof (Z.mod_pos_bound a 8 ltac:(lia)); lia).
  destruct (AC _ Hx) as (v & V0 & RD & OK).
  assert (SHE : sh (a + (7 - a mod 8)) = sh a) by (unfold sh; f_equal; Z.div_mod_to_equations; lia).
  destruct OK as [->|OK].
  - apply sh0_of_mrd; [lia|]. rewrite <- SHE. exact RD.
  - exfalso. replace ((a + (7 - a mod 8)) mod 8) with 7 in OK by (Z.div_mod_to_equations; lia). lia.
Qed.

Lemma swrap32_sx32 : forall x, 0 <= x < 2 ^ 32 -> Z_to_bv 64 (bv_swrap 32 x) = Z_to_bv 64 (sx32 x).
Proof.
  intros x Hx. unfold sx32. destruct (Z.ltb_spec x 2147483648) as [L|L]; apply bv_eq; rewrite !Z_to_bv_unsigned;
    unfold bv_swrap, bv_wrap; change (bv_modulus 32) with (2 ^ 32); change (bv_half_modulus 32) with (2 ^ 31);
    change (bv_modulus 64) with (2 ^ 64).
  - rewrite (Z.mod_small (x + 2 ^ 31) (2 ^ 32)) by lia. replace (x + 2 ^ 31 - 2 ^ 31) with x by lia. reflexivity.
  - replace (x + 2 ^ 31) with ((x - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z_mod_plus_full. rewrite (Z.mod_small (x - 2 ^ 31)) by lia.
    rewrite <- (Z_mod_plus_full (x - 2 ^ 31 - 2 ^ 31) 1 (2 ^ 64)). f_equal. lia.
Qed.

Lemma rdn4_of_mdef : forall m a, mdef m a 4 -> 0 <= a -> a + 4 < 2 ^ 64 ->
  exists bs, PropExec.rdn asegs m (Z_to_bv 64 a) 4 = Some bs /\ length bs = 4%nat.
Proof.
  intros m a MD H0 H1.
  assert (G : forall i, 0 <= i < 4 -> exists b, m (Z_to_bv 64 (a + i)) = Some b).
  { intros i Hi. pose proof (MD i Hi) as D. destruct (m (Z_to_bv 64 (a + i))) as [b|]; [exists b; reflexivity | contradiction]. }
  destruct (G 0 ltac:(lia)) as (b0 & E0). destruct (G 1 ltac:(lia)) as (b1 & E1).
  destruct (G 2 ltac:(lia)) as (b2 & E2). destruct (G 3 ltac:(lia)) as (b3 & E3).
  exists [b0; b1; b2; b3]. split; [| reflexivity].
  rewrite Z.add_0_r in E0. cbn [PropExec.rdn]. rewrite E0.
  rewrite (bv_add1_lit a) by lia. rewrite E1. rewrite (bv_add1_lit (a + 1)) by lia. replace (a + 1 + 1) with (a + 2) by lia. rewrite E2.
  rewrite (bv_add1_lit (a + 2)) by lia. replace (a + 2 + 1) with (a + 3) by lia. rewrite E3. reflexivity.
Qed.

Lemma bytes_le_to_Z_rng : forall bs : list byte, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length].
  - cbn. lia.
  - pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
    rewrite HBytes.lor_shiftl8_add by lia. rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia.
    change (2 ^ 8) with 256. nia.
Qed.

Lemma bytes_le_to_Z_range4 : forall bs : list byte, length bs = 4%nat -> 0 <= bytes_le_to_Z bs < 2 ^ 32.
Proof. intros bs L. pose proof (bytes_le_to_Z_rng bs) as R. rewrite L in R. exact R. Qed.

Lemma hex_flags : forall E e fl, edenot E e = Z_to_bv 64 fl -> (fl = DS_FL0 \/ fl = DS_FLHEX) ->
  edenot E (EAlu ALU_ADD (EAlu ALU_AND (EExt false 0 4 e) (ELit (-75))) (ELit 8)) = Z_to_bv 64 DS_FLHEX.
Proof.
  intros E e fl He Hf. cbn [edenot]. rewrite He. unfold DS_FL0, DS_FLHEX in Hf. destruct Hf as [->| ->]; vm_compute; reflexivity.
Qed.

Section Hex.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV ds_repA.

  Lemma HHh : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma pm_bm_hexnum : forall (w : pmwA H) s LB LBs m mo c TB spal msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c BM_INS TBL_BM [] TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xedca4) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_HEX -> PropExec.getr R 4%bv = wa_tp w ->
    wa_words w <> 0 -> 5 <= wa_n w ->
    ds_repA LB m (wa_ff w + 14672) (-4) 29 TB -> spal + ds_cost (29 + 24) <= PM_RESERVE ->
    (forall msF1 mo1 R1 F1 fc1 (s1 : as_St H) LB1 m1 TB1,
       as_AKREL H s1 (mkCfg msF1 mo1) -> as_VIS H s1 msF1 = MS R1 F1 (Z_to_bv 64 0xedd28) fc1 None m1 (seg_rom asegs) ->
       rfull R1 -> frm_zero fc1 ->
       PMXAT H LINV w s1 LB1 LBs m1 mo1 c BM_INS TBL_BM [] TB1 (spal + ds_cost (29 + 24)) ->
       regs_tbl w R1 (rt_keep RT_HEXCALL) ->
       PropExec.getr R1 3%bv = PropExec.getr R 3%bv -> PropExec.getr R1 4%bv = PropExec.getr R 4%bv ->
       ds_repA LB1 m1 (wa_ff w + 14672) (-4) (29 + 24) TB1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c TB spal msF R F fc Q OK X KR VIS RF FZ HT G4 HW HN DS0 Hsp K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.

    destruct (dla_hex _ _ DSL _ _ _ _ _ _ (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) DS0)
      as (vt & fl & HVT & HRO & HACC & HFL & HFLC & HREP).
    pose proof HACC as (AV0 & AV1 & _).

    pose proof (xa_wbuf _ _ _ _ _ _ _ _ _ _ _ _ _ _ X HW) as WB.
    destruct (rdn4_of_mdef m (wa_words w) ltac:(intros i Hi; apply WB; lia) ltac:(lia) ltac:(lia)) as (bs & RDW & LW).
    pose proof (bytes_le_to_Z_range4 bs LW) as XR.
    set (x := bytes_le_to_Z bs) in *.
    set (Xs := [Z_to_bv 64 vt; Z_to_bv 64 fl; Z_to_bv 64 (bv_swrap 32 x)]).
    assert (EF : bv_unsigned (edenot (Eseed R (wenv_vals w ++ Xs)) (EVar WV_FF)) = wa_ff w)
      by exact (ev_ff H w _ OK (env_world_seed H w R Xs)).
    assert (HK : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m KHEX).
    { apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]]].
      - eapply (kword_of_rw_cells asegs _ m (wa_ff w + 14672) _ 0 (C8 (Z_to_bv 64 vt))); [exact HVT | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | reflexivity].
      - eapply (kword_of_cells asegs _ m (vt - 24) _ 0 (C8 (Z_to_bv 64 DS_VBOFF))); [exact HRO | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; change (edenot _ (EVar 41)) with (Z_to_bv 64 vt); rewrite u64_of_Z by (unfold AAPP_HI in *; lia); cbn [Z.of_nat]; lia
          | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; unfold AAPP_HI in *; lia | reflexivity].
      - eapply (kshadow0 _ m _ (vt - 24)); [| unfold AAPP_HI in *; lia | exact (sh0_of_acc8 m (vt - 24) HACC)].
        replace (vt - 24) with (vt + -24) by lia. eapply ev_add; [reflexivity | unfold AAPP_HI in *; lia | unfold AAPP_HI in *; lia].
      - eapply (kword_of_rw_cells asegs _ m (wa_ff w + 14672 + DS_VBOFF + 8) _ 0 (C4 (Z_to_bv 64 fl))); [exact HFLC | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EF; unfold DS_VBOFF; cbn [Z.of_nat]; lia | unfold DS_VBOFF; cbn [Z.of_nat]; lia
          | unfold DS_VBOFF; cbn [Z.of_nat]; lia | reflexivity].
      - pmk_entry H HHh w OK X (env_world_seed H w R Xs).
      - pmk_entry H HHh w OK X (env_world_seed H w R Xs). }
    pm_goX HHh LINV_frame OK X KR VIS RF HT Xs KHEX HK 100%nat [APUT_U32] (@nil bool) 43%N
          BM_INS (@nil Z) (@nil Z) TBL_BM (@nil (Z * expr)) RT_HEXCALL.
    { assert (EV41 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 vt) by reflexivity.
      assert (EVm : edenot (Eseed R (wenv_vals w ++ Xs)) (EAlu ALU_ADD (EVar 41) (ELit (-24))) = Z_to_bv 64 (vt - 24)).
      { replace (vt - 24) with (vt + -24) by lia. eapply ev_add; [exact EV41 | unfold AAPP_HI in *; lia | unfold AAPP_HI in *; lia]. }
      destruct (ev_world_all H w _ (env_world_seed H w R Xs)) as (_ & _ & _ & _ & EW36 & _).
      split_scs.
      -
        cbn [sc_denot]. exists bs. split.
        + rewrite (adenot_of_estart _ _ (wa_words w)); [exact RDW | | lia].
          unfold estart. cbn [a_base a_off]. rewrite EW36, u64_of_Z by lia. lia.
        + reflexivity.
      - cbn [sc_denot]. unfold flat, estart, elenZ. cbn [a_base a_off]. rewrite EV41, u64_of_Z by (unfold AAPP_HI in *; lia).
        cbn [edenot]. rewrite u64_of_Z by lia. unfold AAPP_HI in *. lia.
      - cbn [sc_denot]. unfold flat, estart, elenZ. cbn [a_base a_off]. rewrite (srl3_val _ _ (vt - 24) EVm) by (unfold AAPP_HI in *; lia).
        cbn [edenot]. rewrite u64_of_Z by lia. unfold AAPP_HI in *. assert (0 <= (vt - 24) / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] Xs R1 RT_HEXCALL HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    assert (G31 : PropExec.getr R1 3%bv = PropExec.getr R 3%bv) by (rewrite (HR1 3%bv); reflexivity).
    assert (G41 : PropExec.getr R1 4%bv = PropExec.getr R 4%bv) by (rewrite (HR1 4%bv); reflexivity).
    assert (G111 : PropExec.getr R1 11%bv = Z_to_bv 64 (sx32 x)) by (rewrite (HR1 11%bv); exact (swrap32_sx32 x XR)).

    assert (DS1 : ds_repA LB M1 (wa_ff w + 14672) (-4) 29 TB).
    { apply HREP.
      - intros a Ha Hout. subst M1.
        pose proof (munch_sym (Eseed R (wenv_vals w ++ Xs)) m _ [(EVar WV_FF, 14792, 14796)] Hlf1 ltac:(vm_compute; reflexivity)) as MU.
        cbn [num_wins map] in MU. rewrite EF in MU. apply MU. unfold wa. rewrite u64_of_Z by lia.
        cbn [outside fst snd]. unfold DS_VBOFF in Hout. split; [lia | exact I].
      - subst M1. eapply (rw_cells_log_nth_sb _ m _ 0 (EVar WV_FF) 14792 4); [exact Hlf1 | reflexivity | reflexivity
          | rewrite EF; unfold DS_VBOFF; lia | | reflexivity | exact I | ].
        + pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (W0 & W1 & W2). change (fsz PM_FCLASS) with 16384 in *.
          unfold DS_VBOFF. split; [lia|]. split; [cbn; lia|]. intros i Hi. replace (wa_ff w + 14672 + 112 + 8 + i) with (wa_ff w + (14792 + i)) by lia.
          apply W2. cbn in Hi. lia.
        + cbn [cbytes]. f_equal. symmetry. exact (hex_flags (Eseed R (wenv_vals w ++ Xs)) (EVar 42) fl eq_refl HFL). }

    eapply (pm_put_num H HHbp LINV ds_repA DSL APUT_U32 0 (2 ^ 32) sx32 HU32 w s LB LBs M1 mo1 c BM_INS TBL_BM [] TB spal msF1 R1 F fc
              14672 0xedd28 x (-4) 29);
      [exact OK | exact X1 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR1 | exact VIS1 | exact RF1 | exact FZ
      | rtf HT1 | reflexivity | lia | rtf HT1 | rtf HT1 | rewrite G41; exact G4 | rtf HT1 | exact G111 | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | exact DS1 | unfold DS_MAXLEN; lia | exact Hsp | ].
    intros msF2 mo2 R2 F2 fc2 s2 LB2 m2 TB2 KR2 VIS2 RF2 FZ2 X2 KEEP2 (DS2 & _) _.
    eapply (K msF2 mo2 R2 F2 fc2 s2 LB2 m2 TB2 KR2 VIS2 RF2 FZ2 X2 (regs_keep w [] R1 R2 RT_HEXCALL HT1 KEEP2)); [| | exact DS2].
    - rewrite (KEEP2 3%bv ltac:(inb)). exact G31.
    - rewrite (KEEP2 4%bv ltac:(inb)). exact G41.
  Qed.
End Hex.
