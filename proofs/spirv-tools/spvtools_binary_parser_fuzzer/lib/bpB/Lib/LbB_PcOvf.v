(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface RtB_IMemset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ContStmt LbB_StrPbR LbB_StrPb LbB_PcStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DPdK.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma ftbl1_of_fld : forall W B m k (w : nat) e v, CRep.fld ASEGS m (B + k) w v -> wr_at asegs m (B + k) (Z.of_nat w) ->
  edenot (wenv W) e = Z_to_bv 64 v -> 0 <= B + k -> ftbl W B m [(k, w, e)].
Proof.
  intros W B m k w e v HF HW HE H0. constructor; [| constructor]. cbn beta iota. rewrite HE.
  pose proof HW as (HW0 & HW1 & _).
  split; [split|].
  - cbn. split; [unfold word_to_le_bytes; apply length_Z_to_le_bytes | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_at_of_rdn; [exact H0 | unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; lia
                           | unfold word_to_le_bytes in *; rewrite length_Z_to_le_bytes; exact HF].
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma w_add_g : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- Z.add_mod by lia. reflexivity.
Qed.
Lemma w_mul_g : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b. apply bv_eq. cbn [mul_div]. rewrite bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- Z.mul_mod by lia. reflexivity.
Qed.

Lemma bit_odd : forall a, 0 <= a -> 2 * a + 1 < 2 ^ 64 ->
  alu64 ALU_AND (ext_val false 0 1 (Z_to_bv 64 (2 * a + 1))) (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof.
  intros a H0 H1. unfold ext_val, ext_Z. cbn [Z.of_nat Nat.mul].
  rewrite unsigned_lit by lia. change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 1)) with 256. rewrite Z.div_1_r.
  apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small 1) by lia. rewrite (Z.mod_small ((2 * a + 1) mod 256)) by (pose proof (Z.mod_pos_bound (2 * a + 1) 256); lia).
  change 1 with (Z.ones 1) at 2. rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 128; reflexivity). rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full.
  reflexivity.
Qed.

Lemma shvis_wmono_hi : forall m m' lo hi, shvis m lo hi -> wmono asegs m m' -> AIMG_TOP <= sh (hull_lo lo) -> shvis m' lo hi.
Proof.
  intros m m' lo hi SV WM HA. unfold shvis in *. pose proof SV as (T1 & T2 & T3).
  split; [exact T1|]. split; [exact T2|]. intros x Hx. destruct (T3 x Hx) as [HV _].
  pose proof (WM (wa x) HV) as HV'. split; [exact HV'|].
  assert (HX : AIMG_TOP <= bv_unsigned (wa x)) by (unfold wa; rewrite unsigned_lit by (clear - T1 T2 Hx; lia); clear - Hx HA; lia).
  rewrite (BakeStackRep.wview_high m' (wa x) HX) in HV'.
  unfold mrd. destruct (m' (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction].
Qed.

Definition kst_o : list kentry :=
  [ KWr (SA (EVar 33) (-8192)) (ELit 8192); KRange (EVar 33) (2 ^ 45) (2 ^ 47);
    KWr (SA (EVar 32) 0) (ELit 392); KRange (EVar 32) 0x6e8000 (2 ^ 47 - 392);
    KDisj (SA (EVar 32) 0) (ELit 392) (SA (EVar 33) (-8192)) (ELit 8192) ].

Definition RTO0 : list (reg * expr) :=
  [(1%bv, EVar 34); (2%bv, EVar 33); (3%bv, EVar 48); (4%bv, EVar 49); (8%bv, EVar 36); (9%bv, EVar 37);
   (18%bv, EVar 38); (19%bv, EVar 39); (20%bv, EVar 40); (21%bv, EVar 41); (22%bv, EVar 42); (23%bv, EVar 43);
   (24%bv, EVar 44); (25%bv, EVar 45); (26%bv, EVar 46); (27%bv, EVar 47);
   (10%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (11%bv, EVar 35)].

Definition DTO0a : list fent :=
  [(24, 8%nat, ELit 0); (32, 8%nat, ELit 0); (40, 8%nat, ELit 0); (48, 8%nat, EVar 50); (56, 8%nat, EVar 51);
   (64, 8%nat, EVar 51)].
Definition DTO0b : list fent := [(96, 8%nat, EVar 52); (104, 4%nat, ELit 16)].
Definition DTO0 : list fent := DTO0a ++ DTO0b.

Definition STO1 : list fent :=
  [(-8, 8%nat, EVar 34); (-16, 8%nat, EVar 36); (-24, 8%nat, EVar 37); (-32, 8%nat, EVar 38); (-40, 8%nat, EVar 39);
   (-48, 8%nat, EVar 40); (-56, 8%nat, EVar 41); (-64, 8%nat, EVar 42); (-72, 8%nat, EVar 43); (-80, 8%nat, EVar 44)].
Definition RTO1 : list (reg * expr) :=
  [(1%bv, ELit 0x126038); (2%bv, EAlu ALU_ADD (EVar 33) (ELit (-80))); (3%bv, EVar 48); (4%bv, EVar 49);
   (8%bv, ELit 18446744073709551615); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 72)); (10%bv, EAlu ALU_ADD (EVar 32) (ELit 72));
   (11%bv, ELit 0); (18%bv, EVar 51); (19%bv, ELit 0); (20%bv, ELit 0); (21%bv, EVar 50); (22%bv, EVar 52);
   (23%bv, EVar 35); (24%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (25%bv, EVar 45); (26%bv, EVar 46); (27%bv, EVar 47)].

Section O1.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m0 : mem) (ds c data pp hm lo : Z).
  Hypothesis DSO : app_obj ds DS_SIZE.
  Hypothesis DSW : wr_at asegs m0 ds DS_SIZE.
  Hypothesis STK : stk asegs m0 lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - 8192.
  Hypothesis SPHI : bv_unsigned sp <= 2 ^ 47.
  Hypothesis SPD : ds + DS_SIZE <= lo.
  Hypothesis CR : 0 <= c <= 255.
  Hypothesis VR : 0 <= data < 2 ^ 64 /\ 0 <= pp < 2 ^ 64 /\ 0 <= hm < 2 ^ 64.
  Hypothesis HDT : ftbl [Z_to_bv 64 ds; sp; ra; Z_to_bv 64 c; s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; gp; tp;
                         Z_to_bv 64 data; Z_to_bv 64 pp; Z_to_bv 64 hm] ds m0 DTO0.

  Notation spz := (bv_unsigned sp) (only parsing).
  Definition Wo : list word :=
    [Z_to_bv 64 ds; sp; ra; Z_to_bv 64 c; s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; gp; tp;
     Z_to_bv 64 data; Z_to_bv 64 pp; Z_to_bv 64 hm].

  Definition Po (m : mem) : Prop := munch [(spz - 8192, spz); (ds + 24, ds + 72); (ds + 96, ds + 108)] m0 m /\ wmono asegs m0 m.

  Lemma o_ranges : 0 <= spz < 2 ^ 64 /\ aceil + 8192 <= spz /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000
                   /\ AIMG_TOP <= ds /\ ds + DS_SIZE <= lo.
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    pose proof aceil_facts as ((A1 & A2) & _). pose proof DSO as (O1 & _).
    clear - R A1 A2 O1 CEIL LO SPD. repeat split; lia.
  Qed.

  Lemma o_keep : forall m, Po m -> mem_inv asegs m -> stk asegs m lo spz /\ wr_at asegs m ds DS_SIZE.
  Proof.
    intros m [MU WM] MI. split; [| eapply wr_at_transport; [exact DSW | exact WM]].
    pose proof o_ranges as (R1 & R2 & R3 & R4 & R5).
    eapply stk_transport; [exact STK | exact MU | exact WM |]. intros x Hx. right.
    pose proof STK as (T1 & T2 & T3). destruct (T3 x Hx) as [HV _].
    pose proof (WM (wa x) HV) as HV'.
    assert (HX : AIMG_TOP <= bv_unsigned (wa x)).
    { unfold wa. rewrite unsigned_lit by (clear - T1 T2 Hx; lia). clear - Hx CEIL R3. unfold AIMG_TOP. lia. }
    rewrite (BakeStackRep.wview_high m (wa x) HX) in HV'.
    destruct (m (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction].
  Qed.

  Ltac evwo := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wo;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Lemma kst_o_ok : forall R X m, Po m -> mem_inv asegs m -> know_ok asegs (HLib.Eseed R (Wo ++ X)) m kst_o.
  Proof.
    intros R X m PW MI. destruct (o_keep m PW MI) as (ST & DW).
    pose proof o_ranges as (R1 & R2 & R3 & R4 & R5). pose proof DSO as (O1 & O2 & O3).
    unfold DS_SIZE, AIMG_TOP, AAPP_HI in *.
    unfold know_ok, kst_o. repeat apply Forall_cons; try apply Forall_nil.
    - eapply kwr_of_stk; [exact ST | | |]; evwo; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwo. lia.
    - eapply kwr_of_wr_at; [exact DW | | |]; evwo; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwo. rewrite unsigned_lit by lia. lia.
    - cbn [kentry_ok]. evwo. rewrite !unsigned_lit by lia. lia.
  Qed.

  Definition tSo (T : list fent) (ks : list (Z * nat)) : tab := (EVar 33, spz, -8192, 0, T, ks).

  Definition tDo1 (T : list fent) (ks : list (Z * nat)) : tab := (EVar 32, ds, 24, 72, T, ks).
  Definition tDo2 (T : list fent) (ks : list (Z * nat)) : tab := (EVar 32, ds, 96, 108, T, ks).

  Lemma tabs_wf_o : forall ST DT1 DT2 ks1 ks2 ks3,
    fwcl (wbound Wo) ST = true -> fwcl (wbound Wo) DT1 = true -> fwcl (wbound Wo) DT2 = true ->
    fin (-8192) 0 (fkeys ST ++ ks1) = true -> fin 24 72 (fkeys DT1 ++ ks2) = true -> fin 96 108 (fkeys DT2 ++ ks3) = true ->
    tabs_wf Wo [tSo ST ks1; tDo1 DT1 ks2; tDo2 DT2 ks3].
  Proof.
    intros ST DT1 DT2 ks1 ks2 ks3 C1 C2 C3 F1 F2 F3. pose proof o_ranges as (R1 & R2 & R3 & R4 & R5).
    assert (VD : bv_unsigned (edenot (wenv Wo) (EVar 32)) = ds) by (apply unsigned_lit; unfold AIMG_TOP, DS_SIZE in *; lia).
    split.
    - repeat constructor; cbn [tb tB tlo thi ttbl tks tSo tDo1 tDo2]; try reflexivity; try assumption;
        clear - R1 R2 R3 R4 R5 LO; unfold DS_SIZE, AIMG_TOP in *; lia.
    - intros t1 t2 H1 H2 Hb. cbn [In] in H1, H2.
      destruct H1 as [<-|[<-|[<-|[]]]]; destruct H2 as [<-|[<-|[<-|[]]]]; cbn [tb tB tlo thi tSo tDo1 tDo2] in *;
        try (vm_compute in Hb; discriminate Hb); clear - R1 R2 R3 R4 R5 LO; unfold DS_SIZE in *; lia.
  Qed.

  Lemma tabs_ok_o : forall m ST DT1 DT2 ks1 ks2 ks3, Po m -> mem_inv asegs m ->
    ftbl Wo spz m ST -> ftbl Wo ds m DT1 -> ftbl Wo ds m DT2 ->
    fin (-8192) 0 ks1 = true -> fin 24 72 ks2 = true -> fin 96 108 ks3 = true ->
    tabs_ok Wo m [tSo ST ks1; tDo1 DT1 ks2; tDo2 DT2 ks3].
  Proof.
    intros m ST DT1 DT2 ks1 ks2 ks3 PW MI H1 H2 H3 F1 F2 F3. destruct (o_keep m PW MI) as (ST0 & DW).
    pose proof o_ranges as (R1 & R2 & R3 & R4 & R5).
    apply Forall_cons; [split; [exact H1|]|].
    { intros k w Hi. cbn [tB tks tSo] in *. destruct (fin_In _ _ _ k w F1 Hi) as (K1 & K2 & K3).
      pose proof (wr_at_of_stk asegs m lo spz ST0) as W. eapply wr_at_sub; [exact W | lia | lia | lia]. }
    apply Forall_cons; [split; [exact H2|]|].
    { intros k w Hi. cbn [tB tks tDo1] in *. destruct (fin_In _ _ _ k w F2 Hi) as (K1 & K2 & K3).
      eapply wr_at_sub; [exact DW | unfold DS_SIZE; lia | unfold DS_SIZE; lia | lia]. }
    apply Forall_cons; [split; [exact H3|] | apply Forall_nil].
    { intros k w Hi. cbn [tB tks tDo2] in *. destruct (fin_In _ _ _ k w F3 Hi) as (K1 & K2 & K3).
      eapply wr_at_sub; [exact DW | unfold DS_SIZE; lia | unfold DS_SIZE; lia | lia]. }
  Qed.

  Lemma Po_step : forall ST DT1 DT2 ks1 ks2 ks3 m m', Po m -> munch (winsT [tSo ST ks1; tDo1 DT1 ks2; tDo2 DT2 ks3]) m m' ->
    wmono asegs m m' -> mem_inv asegs m' -> Po m'.
  Proof.
    intros ST DT1 DT2 ks1 ks2 ks3 m m' [MU0 WM0] MU WM _. split; [| eapply wmono_trans; eassumption].
    eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU].
    apply sub_fp_of. unfold winsT. cbn [map tB tlo thi tSo tDo1 tDo2].
    apply Forall_cons; [sfp_in (spz - 8192, spz)|].
    apply Forall_cons; [sfp_in (ds + 24, ds + 72)|].
    apply Forall_cons; [sfp_in (ds + 96, ds + 108)| apply Forall_nil].
  Qed.

  Ltac dkrunO HRT HST HDT1 HDT2 HP HMI fuel stops dirs :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HST with ftbl _ _ _ ?ST =>
      lazymatch type of HDT1 with ftbl _ _ _ ?DT1 =>
      lazymatch type of HDT2 with ftbl _ _ _ ?DT2 =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tSo ST []; tDo1 DT1 []; tDo2 DT2 []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR dirs [] []) (SS pc (HLib.srs sr_id RT) [] (kst_o ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wo) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) ST) in
          let ks2 := eval vm_compute in (nkeys (EVar 32) (s_log SSr) DT1) in
          let ks3 := eval vm_compute in (nkeys (EVar 32) (s_log SSr) DT2) in
          eapply (dk_runN Wo [tSo ST ks1; tDo1 DT1 ks2; tDo2 DT2 ks3]
                    (tabs_wf_o ST DT1 DT2 ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity))
                    Po (Po_step ST DT1 DT2 ks1 ks2 ks3)
                    Q R F pc fc m ro RT [] kst_o fuel stops (SCR dirs [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok_o; [exact HP | exact HMI | exact HST | exact HDT1 | exact HDT2 | vm_compute; reflexivity .. ]
          | exact HP | exact HMI | apply kst_o_ok; [exact HP | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end
    end.

  Lemma o1_evt : forall R, rfull R -> rtbl Wo R RTO0 -> mem_inv asegs m0 ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 SPB_ENTRY) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl Wo R1 RTO1 /\ ftbl Wo spz m1 STO1 /\ ftbl Wo ds m1 DTO0 /\ Po m1 /\ mem_inv asegs m1)
        (MS R F (Z_to_bv 64 AOVF) fc None m0 (seg_rom asegs)).
  Proof.
    intros R RF HRT MI.
    assert (HST : ftbl Wo spz m0 []) by constructor.
    assert (HP : Po m0) by (split; [apply munch_refl | apply wmono_refl]).
    assert (HDTab : ftbl Wo ds m0 DTO0a /\ ftbl Wo ds m0 DTO0b) by (pose proof HDT as K; unfold DTO0, ftbl in *; apply Forall_app in K; exact K).
    destruct HDTab as [HDT1 HDT2].
    unfold AOVF.
    dkrunO HRT HST HDT1 HDT2 HP MI 600%nat [SPB_ENTRY] [false].
    { split_scs. cbn [sc_denot].
      change (edenot (HLib.Eseed R (Wo ++ [])) (EVar 35)) with (Z_to_bv 64 c).
      cbn [edenot]. rewrite br_eq by (clear - CR; lia). apply Z.eqb_neq. clear - CR. lia. }
    intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
    lazymatch type of HTS1 with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS1; clear E end.
    apply Forall_cons_iff in HTS1 as [HS1 HTS1]. apply Forall_cons_iff in HTS1 as [HD1 HTS1].
    apply Forall_cons_iff in HTS1 as [HD2 _]. cbn [fst snd] in HS1, HD1, HD2.
    apply evt_done. exists R1, m1. split; [reflexivity|]. split; [exact RF1|].
    split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HS1); vm_compute; reflexivity|].
    split; [unfold DTO0; apply ftbl_app; [apply (ftbl_sub _ _ _ _ _ HD1) | apply (ftbl_sub _ _ _ _ _ HD2)]; vm_compute; reflexivity|].
    split; [exact HP1 | exact HMI1].
  Qed.
End O1.

Definition DTQS : list fent := DTO0 ++ [(72, 8%nat, ELit 49); (80, 8%nat, ELit 23); (88, 8%nat, EVar 53)].

Definition RTQ0 : list (reg * expr) :=
  [(1%bv, ELit 0x126038); (2%bv, EAlu ALU_ADD (EVar 33) (ELit (-80))); (3%bv, EVar 48); (4%bv, EVar 49);
   (8%bv, ELit 18446744073709551615); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 72));
   (18%bv, EVar 51); (19%bv, ELit 0); (20%bv, ELit 0); (21%bv, EVar 50); (22%bv, EVar 52);
   (23%bv, EVar 35); (24%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (25%bv, EVar 45); (26%bv, EVar 46); (27%bv, EVar 47)].

Definition kst_q : list kentry :=
  kst_o ++
  [ KWr (SA (EVar 53) 0) (ELit 48); KRange (EVar 53) 0x6e8000 (2 ^ 47 - 48);
    KDisj (SA (EVar 53) 0) (ELit 48) (SA (EVar 33) (-8192)) (ELit 8192);
    KDisj (SA (EVar 53) 0) (ELit 48) (SA (EVar 32) 0) (ELit 392) ].

Lemma o_ret_ok : forall (Q : machine_state -> Prop) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (ret_pc x1) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x125fc0) fc None m (seg_rom asegs)).
Proof.
  intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HQ.
  step. apply evt_done. exact HQ.
Qed.

Definition RTQ4 : list (reg * expr) :=
  [(1%bv, EVar 34); (2%bv, EVar 33); (3%bv, EVar 48); (4%bv, EVar 49); (8%bv, EVar 36); (9%bv, EVar 37);
   (18%bv, EVar 38); (19%bv, EVar 39); (20%bv, EVar 40); (21%bv, EVar 41); (22%bv, EVar 42); (23%bv, EVar 43);
   (24%bv, EVar 44); (25%bv, EVar 45); (26%bv, EVar 46); (27%bv, EVar 47); (10%bv, EAlu ALU_AND (EVar 35) (ELit 255))].
Definition DTQ4 : list fent :=
  [(24, 8%nat, ELit 0); (32, 8%nat, ELit 0); (40, 8%nat, ELit 0); (48, 8%nat, EVar 53);
   (56, 8%nat, EAlu ALU_ADD (EVar 53) (ELit 23)); (64, 8%nat, EAlu ALU_ADD (EVar 53) (ELit 47));
   (96, 8%nat, EAlu ALU_ADD (EVar 53) (ELit 23)); (104, 4%nat, ELit 16); (72, 8%nat, ELit 49); (80, 8%nat, ELit 47);
   (88, 8%nat, EVar 53)].
Definition BTQ4 : list fent := (22, 1%nat, EVar 35) :: zents1 23 25.

Definition re_subst (e e' : expr) (RT : list (reg * expr)) : list (reg * expr) :=
  map (fun re => (fst re, if expr_eqb (snd re) e then e' else snd re)) RT.
Lemma rtbl_subst : forall W R RT e e', edenot (wenv W) e = edenot (wenv W) e' -> rtbl W R RT -> rtbl W R (re_subst e e' RT).
Proof.
  intros W R RT e e' HE H. unfold rtbl, re_subst in *. apply Forall_map. eapply Forall_impl; [|exact H].
  intros [r x] Hx. cbn [fst snd] in *. destruct (expr_eqb x e) eqn:Ex; [apply expr_eqb_eq in Ex; subst x; rewrite Hx; exact HE | exact Hx].
Qed.
Definition fe_subst (e e' : expr) (T : list fent) : list fent :=
  map (fun f => match f with (k, w, x) => (k, w, if expr_eqb x e then e' else x) end) T.
Lemma ftbl_subst : forall W B m T e e', edenot (wenv W) e = edenot (wenv W) e' -> ftbl W B m T -> ftbl W B m (fe_subst e e' T).
Proof.
  intros W B m T e e' HE H. unfold ftbl, fe_subst in *. apply Forall_map. eapply Forall_impl; [|exact H].
  intros [[k w] x] Hx. cbv beta iota in *. destruct (expr_eqb x e) eqn:Ex; [apply expr_eqb_eq in Ex; subst x; rewrite <- HE; exact Hx | exact Hx].
Qed.

Section O23S.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m2 : mem) (ds c data pp hm lo d' : Z).
  Hypothesis DSO : app_obj ds DS_SIZE.
  Hypothesis DSW : wr_at asegs m2 ds DS_SIZE.
  Hypothesis STK : stk asegs m2 lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - 8192.
  Hypothesis SPHI : bv_unsigned sp <= 2 ^ 47.
  Hypothesis SPD : ds + DS_SIZE <= lo.
  Hypothesis CR : 0 <= c <= 255.
  Hypothesis VR : 0 <= data < 2 ^ 64 /\ 0 <= pp < 2 ^ 64 /\ 0 <= hm < 2 ^ 64.

  Hypothesis BR : AIMG_TOP <= d' /\ d' + 48 <= lo /\ d' mod 16 = 0.
  Hypothesis BDS : d' + 48 <= ds \/ ds + DS_SIZE <= d'.
  Hypothesis BW : wr_at asegs m2 d' 48.
  Hypothesis BA : addressable m2 d' 48.
  Hypothesis BV : shvis m2 d' (d' + 48).
  Hypothesis BAPP : in_app_mem d' (d' + 48).
  Hypothesis BAC : aconst_ok (d', d' + 48).
  Hypothesis MI2 : mem_inv asegs m2.
  Hypothesis AC2 : ACONST m2.

  Notation spz := (bv_unsigned sp) (only parsing).
  Definition Wq : list word :=
    [Z_to_bv 64 ds; sp; ra; Z_to_bv 64 c; s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; gp; tp;
     Z_to_bv 64 data; Z_to_bv 64 pp; Z_to_bv 64 hm; Z_to_bv 64 d'].

  Definition Pq (m : mem) : Prop := munch [(spz - 8192, spz); (ds + 24, ds + 108); (d' + 22, d' + 48)] m2 m /\ wmono asegs m2 m.

  Lemma q_ranges : 0 <= spz < 2 ^ 64 /\ aceil + 8192 <= spz /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000
                   /\ AIMG_TOP <= ds /\ ds + DS_SIZE <= lo.
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    pose proof aceil_facts as ((A1 & A2) & _). pose proof DSO as (O1 & _).
    clear - R A1 A2 O1 CEIL LO SPD. repeat split; lia.
  Qed.

  Lemma q_aconst : forall m, Pq m -> ACONST m.
  Proof.
    intros m [MU WM]. pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    pose proof aceil_facts as ((A1 & A2) & _). pose proof DSO as (O1 & O2 & O3).
    eapply ACONST_frame; [exact AC2 | exact MU | exact WM |].
    apply Forall_cons; [apply LbB_DPdK.aconst_ok_hi; clear - A1 CEIL LO R; lia|].
    apply Forall_cons; [| apply Forall_cons; [intros a Ha; apply BAC; cbn [fst snd] in *; clear - Ha; lia | apply Forall_nil]].
    clear - O1 O2 O3. unfold AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, DS_SIZE in *.
    destruct O2 as [O2|O2]; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP; lia.
  Qed.

  Lemma q_keep : forall m, Pq m -> mem_inv asegs m ->
    stk asegs m lo spz /\ wr_at asegs m ds DS_SIZE /\ wr_at asegs m d' 48.
  Proof.
    intros m [MU WM] MI. split; [| split; [eapply wr_at_transport; [exact DSW | exact WM] | eapply wr_at_transport; [exact BW | exact WM]]].
    pose proof q_ranges as (R1 & R2 & R3 & R4 & R5).
    eapply stk_transport; [exact STK | exact MU | exact WM |]. intros x Hx. right.
    pose proof STK as (T1 & T2 & T3). destruct (T3 x Hx) as [HV _].
    pose proof (WM (wa x) HV) as HV'.
    assert (HX : AIMG_TOP <= bv_unsigned (wa x)).
    { unfold wa. rewrite unsigned_lit by (clear - T1 T2 Hx; lia). clear - Hx CEIL R3. unfold AIMG_TOP. lia. }
    rewrite (BakeStackRep.wview_high m (wa x) HX) in HV'.
    destruct (m (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction].
  Qed.

  Ltac evwq := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wq;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Lemma kst_q_ok : forall R X m, Pq m -> mem_inv asegs m -> know_ok asegs (HLib.Eseed R (Wq ++ X)) m kst_q.
  Proof.
    intros R X m PW MI. destruct (q_keep m PW MI) as (ST & DW & BW').
    pose proof q_ranges as (R1 & R2 & R3 & R4 & R5). pose proof DSO as (O1 & O2 & O3).
    pose proof BR as (B1 & B2 & B3).
    unfold DS_SIZE, AIMG_TOP, AAPP_HI in *.
    unfold know_ok, kst_q, kst_o. repeat apply Forall_cons; try apply Forall_nil.
    - eapply kwr_of_stk; [exact ST | | |]; evwq; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwq. lia.
    - eapply kwr_of_wr_at; [exact DW | | |]; evwq; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwq. rewrite unsigned_lit by lia. lia.
    - cbn [kentry_ok]. evwq. rewrite !unsigned_lit by lia. lia.
    - eapply kwr_of_wr_at; [exact BW' | | |]; evwq; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwq. rewrite unsigned_lit by lia. lia.
    - cbn [kentry_ok]. evwq. rewrite !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. evwq. rewrite !unsigned_lit by lia. clear - BDS R4 R5 O1 O3 B1 B2. unfold DS_SIZE in *. lia.
  Qed.

  Definition tSq (T : list fent) (ks : list (Z * nat)) : tab := (EVar 33, spz, -8192, 0, T, ks).
  Definition tDq (T : list fent) (ks : list (Z * nat)) : tab := (EVar 32, ds, 24, 108, T, ks).
  Definition tBq (T : list fent) (ks : list (Z * nat)) : tab := (EVar 53, d', 22, 48, T, ks).

  Lemma tabs_wf_q : forall ST DT BT ks1 ks2 ks3,
    fwcl (wbound Wq) ST = true -> fwcl (wbound Wq) DT = true -> fwcl (wbound Wq) BT = true ->
    fin (-8192) 0 (fkeys ST ++ ks1) = true -> fin 24 108 (fkeys DT ++ ks2) = true -> fin 22 48 (fkeys BT ++ ks3) = true ->
    tabs_wf Wq [tSq ST ks1; tDq DT ks2; tBq BT ks3].
  Proof.
    intros ST DT BT ks1 ks2 ks3 C1 C2 C3 F1 F2 F3. pose proof q_ranges as (R1 & R2 & R3 & R4 & R5).
    pose proof BR as (B1 & B2 & B3). pose proof DSO as (O1 & O2 & O3).
    assert (VD : bv_unsigned (edenot (wenv Wq) (EVar 32)) = ds) by (apply unsigned_lit; unfold AIMG_TOP, DS_SIZE, AAPP_HI in *; lia).
    assert (VB : bv_unsigned (edenot (wenv Wq) (EVar 53)) = d') by (apply unsigned_lit; unfold AIMG_TOP in *; lia).
    split.
    - repeat constructor; cbn [tb tB tlo thi ttbl tks tSq tDq tBq]; try reflexivity; try assumption;
        clear - R1 R2 R3 R4 R5 B1 B2 O1 O3 LO; unfold DS_SIZE, AIMG_TOP, AAPP_HI in *; lia.
    - intros t1 t2 H1 H2 Hb. cbn [In] in H1, H2.
      destruct H1 as [<-|[<-|[<-|[]]]]; destruct H2 as [<-|[<-|[<-|[]]]]; cbn [tb tB tlo thi tSq tDq tBq] in *;
        try (vm_compute in Hb; discriminate Hb); clear - R1 R2 R3 R4 R5 B1 B2 BDS LO; unfold DS_SIZE in *; lia.
  Qed.

  Lemma tabs_ok_q : forall m ST DT BT ks1 ks2 ks3, Pq m -> mem_inv asegs m ->
    ftbl Wq spz m ST -> ftbl Wq ds m DT -> ftbl Wq d' m BT ->
    fin (-8192) 0 ks1 = true -> fin 24 108 ks2 = true -> fin 22 48 ks3 = true ->
    tabs_ok Wq m [tSq ST ks1; tDq DT ks2; tBq BT ks3].
  Proof.
    intros m ST DT BT ks1 ks2 ks3 PW MI H1 H2 H3 F1 F2 F3. destruct (q_keep m PW MI) as (ST0 & DW & BW').
    pose proof q_ranges as (R1 & R2 & R3 & R4 & R5).
    apply Forall_cons; [split; [exact H1|]|].
    { intros k w Hi. cbn [tB tks tSq] in *. destruct (fin_In _ _ _ k w F1 Hi) as (K1 & K2 & K3).
      pose proof (wr_at_of_stk asegs m lo spz ST0) as W. eapply wr_at_sub; [exact W | lia | lia | lia]. }
    apply Forall_cons; [split; [exact H2|]|].
    { intros k w Hi. cbn [tB tks tDq] in *. destruct (fin_In _ _ _ k w F2 Hi) as (K1 & K2 & K3).
      eapply wr_at_sub; [exact DW | unfold DS_SIZE; lia | unfold DS_SIZE; lia | lia]. }
    apply Forall_cons; [split; [exact H3|] | apply Forall_nil].
    { intros k w Hi. cbn [tB tks tBq] in *. destruct (fin_In _ _ _ k w F3 Hi) as (K1 & K2 & K3).
      eapply wr_at_sub; [exact BW' | lia | lia | lia]. }
  Qed.

  Lemma Pq_step : forall ST DT BT ks1 ks2 ks3 m m', Pq m -> munch (winsT [tSq ST ks1; tDq DT ks2; tBq BT ks3]) m m' ->
    wmono asegs m m' -> mem_inv asegs m' -> Pq m'.
  Proof.
    intros ST DT BT ks1 ks2 ks3 m m' [MU0 WM0] MU WM _. split; [| eapply wmono_trans; eassumption].
    eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU].
    apply sub_fp_of. unfold winsT. cbn [map tB tlo thi tSq tDq tBq].
    apply Forall_cons; [sfp_in (spz - 8192, spz)|].
    apply Forall_cons; [sfp_in (ds + 24, ds + 108)|].
    apply Forall_cons; [sfp_in (d' + 22, d' + 48)| apply Forall_nil].
  Qed.

  Ltac dkrunQ HRT HST HDT HBT HP HMI fuel stops dirs :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HST with ftbl _ _ _ ?ST =>
      lazymatch type of HDT with ftbl _ _ _ ?DT =>
      lazymatch type of HBT with ftbl _ _ _ ?BT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tSq ST []; tDq DT []; tBq BT []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR dirs [] []) (SS pc (HLib.srs sr_id RT) [] (kst_q ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wq) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) ST) in
          let ks2 := eval vm_compute in (nkeys (EVar 32) (s_log SSr) DT) in
          let ks3 := eval vm_compute in (nkeys (EVar 53) (s_log SSr) BT) in
          eapply (dk_runN Wq [tSq ST ks1; tDq DT ks2; tBq BT ks3]
                    (tabs_wf_q ST DT BT ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity))
                    Pq (Pq_step ST DT BT ks1 ks2 ks3)
                    Q R F pc fc m ro RT [] kst_q fuel stops (SCR dirs [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok_q; [exact HP | exact HMI | exact HST | exact HDT | exact HBT | vm_compute; reflexivity .. ]
          | exact HP | exact HMI | apply kst_q_ok; [exact HP | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end
    end.

  Lemma qs_memset : forall (Q : machine_state -> Prop) R1 m RT ST DT BT (retpc spc : Z),
    rfull R1 -> rtbl Wq R1 RT -> ftbl Wq spz m ST -> ftbl Wq ds m DT -> ftbl Wq d' m BT -> Pq m -> mem_inv asegs m ->
    ACONST m ->
    PropExec.getr R1 10 = Z_to_bv 64 (d' + 23) -> PropExec.getr R1 11 = Z_to_bv 64 0 -> PropExec.getr R1 12 = Z_to_bv 64 24 ->
    PropExec.getr R1 2 = Z_to_bv 64 spc -> PropExec.getr R1 1 = Z_to_bv 64 retpc ->
    spz - 256 <= spc <= spz - 128 -> 0 <= retpc < 2 ^ 64 -> retpc mod 2 = 0 ->
    fin (-8192) 0 (fkeys ST) = true -> fin 24 108 (fkeys DT) = true -> fin 22 48 (fkeys BT) = true ->
    (forall R2 m3, rfull R2 -> rtbl Wq R2 (LbB_DCtorK.keptf RT) -> ftbl Wq spz m3 (fabove (spc - spz) ST) ->
       ftbl Wq ds m3 DT -> ftbl Wq d' m3 (fdrop 23 24 BT ++ zents1 23 24) -> Pq m3 -> mem_inv asegs m3 -> ACONST m3 ->
       evt asegs Q (MS R2 F (Z_to_bv 64 retpc) fc None m3 (seg_rom asegs))) ->
    evt asegs Q (MS R1 F (Z_to_bv 64 AMEMSET_STUB) fc None m (seg_rom asegs)).
  Proof.
    intros Q R1 m RT ST DT BT retpc spc RF HRT HST HDT HBT HP HMI AC G10 G11 G12 G2 G1 Hs Hr1 Hr2 Hf1 Hf2 Hf3 K.
    pose proof q_ranges as (R1' & R2' & R3' & R4' & R5'). pose proof BR as (B1 & B2 & B3).
    destruct (q_keep m HP HMI) as (ST0 & DW & BW').
    assert (Us : bv_unsigned (PropExec.getr R1 2) = spc) by (rewrite G2; apply unsigned_lit; clear - Hs R1' R2' R3'; lia).
    destruct (rw_cells_of_wr_hi m (d' + 23) 24 ltac:(eapply wr_at_sub; [exact BW' | lia | lia | lia])
               ltac:(clear - B1; unfold AIMG_TOP in *; lia) ltac:(lia)) as [junk DST].
    assert (BA' : addressable m d' 48).
    { eapply addressable_transport; [exact BA | exact (proj1 HP) | exact (proj2 HP) |].
      cbn [disjoint_from]. assert (N : nsh 48 = 6) by reflexivity. rewrite N.
      pose proof (app_obj_sh_apart ds DS_SIZE d' 48 DSO ltac:(clear - B1; unfold AIMG_TOP in *; lia)
                    ltac:(clear - B2 R1' LO SPHI; unfold AAPP_HI; lia) ltac:(clear; lia)) as D1.
      clear - D1 B1 B2 B3 R1' R2' R3' R4' R5' LO BAPP SPHI. unfold in_app_mem, sh, ASHADOW_BASE, AHI_LO, AAPP_HI, DS_SIZE, AIMG_TOP in *.
      repeat split; [clear - B2 LO R2' R3' R1' B1; unfold AIMG_TOP in *; Z.div_mod_to_equations; lia
                    | clear - D1; unfold nsh in D1; Z.div_mod_to_equations; lia | clear - BAPP; Z.div_mod_to_equations; lia | ..]. }
    destruct (stk_split asegs m lo (spc - AINTRIN_STACK) spz ST0 ltac:(clear - Hs LO; unfold AINTRIN_STACK in *; lia)) as [_ S2].
    destruct (stk_split asegs m (spc - AINTRIN_STACK) spc spz S2 ltac:(clear - Hs; unfold AINTRIN_STACK in *; lia)) as [S3 _].
    rewrite <- Us in S3.
    eapply evt_cut.
    { eapply (memset_icpt_u R1 F fc m (d' + 23) 24 0 (bv_unsigned (PropExec.getr R1 2) - AINTRIN_STACK) junk);
        try eassumption; try (clear; lia).
      - clear - B1. unfold AIMG_TOP in *. lia.
      - clear - B2 LO R1'. lia.
      - eapply addressable_accessible; [exact BA' | clear; lia | clear; lia | clear - B2 LO R1' SPHI; unfold AAPP_HI; lia].
      - assert (SVm : shvis m d' (d' + 48)).
        { apply (shvis_wmono_hi m2 m _ _ BV (proj2 HP)). pose proof (hull_lo_le d' ltac:(clear - B1; unfold AIMG_TOP in *; lia)) as (HL1 & HL2 & HL3).
          clear - HL1 HL2 HL3 B1. unfold sh, ASHADOW_BASE, AIMG_TOP in *. Z.div_mod_to_equations. lia. }
        eapply shvis_sub; [exact SVm | clear - B1; unfold AIMG_TOP in *; lia | clear; lia | clear; lia | clear; lia
                          | clear - B1; unfold AIMG_TOP in *; lia].
      - rewrite Us. clear - Hs R2' LO. unfold AINTRIN_STACK in *. lia.
      - eapply in_app_mem_sub; [exact BAPP | clear; lia | clear; lia].
      - intros a Ha. apply BAC. cbn [fst snd] in *. clear - Ha. lia.
      - left. rewrite Us. clear - Hs B2 LO. unfold AINTRIN_STACK in *. lia. }
    intros ms' (Rr & mr & E2 & RF2 & KP & MU & WM & MI2' & AC2' & CB & ST2). subst ms'.
    rewrite G1, ret_pc_even by lia. rewrite Us in MU.
    apply K.
    - exact RF2.
    - eapply rtbl_keep; [exact (LbB_DCtorK.rtbl_keptf Wq R1 RT HRT) | apply LbB_DCtorK.rsub_keptf | exact KP].
    - eapply (ftbl_munch Wq spz m mr (fabove (spc - spz) ST) _ (spc - spz) 0);
        [exact (ftbl_fabove _ _ _ _ _ HST) | exact MU | exact WM | exact (fin_fabove _ _ _ Hf1) |].
      cbn [disjoint_from]. clear - Hs B1 B2 LO R2'. unfold AINTRIN_STACK in *. lia.
    - eapply (ftbl_munch Wq ds m mr DT _ 24 108); [exact HDT | exact MU | exact WM | exact Hf2 |].
      cbn [disjoint_from]. clear - Hs B1 B2 LO R2' R5' BDS. unfold AINTRIN_STACK, DS_SIZE in *. lia.
    - apply ftbl_app.
      + eapply (ftbl_munch_drop Wq d' m mr BT [(spc - AINTRIN_STACK, spc)] 22 48 23 24); [exact HBT | exact MU | exact WM | exact Hf3 | | lia].
        cbn [disjoint_from]. clear - Hs B1 B2 LO R2'. unfold AINTRIN_STACK in *. lia.
      + pose proof (ftbl_zres1 Wq d' mr (d' + 23) 24 ltac:(lia) CB) as Z2. replace (d' + 23 - d') with 23 in Z2 by lia. exact Z2.
    - destruct HP as [MU0 WM0]. split; [| eapply wmono_trans; eassumption].
      eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. apply sub_fp_of.
      apply Forall_cons; [sfp_in (d' + 22, d' + 48)|].
      apply Forall_cons; [exists (spz - 8192, spz); split; [left; reflexivity | cbn [fst snd]; clear - Hs; unfold AINTRIN_STACK; lia]|].
      apply Forall_nil.
    - exact MI2'.
    - exact AC2'.
  Qed.

  Ltac tnormq H :=
    lazymatch type of H with
    | ftbl ?W ?B ?m ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    | rtbl ?W ?R ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    end.

  Lemma q_vals : 0 <= ds < 2 ^ 64 /\ 0 <= d' < 2 ^ 64 /\ 0 <= c < 2 ^ 64.
  Proof.
    pose proof q_ranges as (R1 & R2 & R3 & R4 & R5). pose proof BR as (B1 & B2 & B3). pose proof DSO as (O1 & O2 & O3).
    clear - R1 R4 R5 B1 B2 LO SPHI CR O3. unfold AIMG_TOP, DS_SIZE, AAPP_HI in *. lia.
  Qed.

  Ltac rgetq HRT r H :=
    lazymatch type of HRT with
    | rtbl ?W ?R ?RT =>
        let e := eval vm_compute in (match List.find (fun re => bv_eqb (fst re) r) RT with Some re => snd re | None => ELit 0 end) in
        assert (H : PropExec.getr R r = edenot (wenv W) e)
          by (apply (rtbl_In W R RT r e HRT); apply LbB_DCtorK.inb_In'; vm_compute; reflexivity);
        unfold wenv in H; cbn [edenot] in H; unfold HLib.Eseed, reg_ev, Wq in H;
        lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
              Init.Nat.add Nat.sub nth app] in H;
        rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z in H by (pose proof q_vals; pose proof q_ranges; lia)
    end.

  Lemma o23s_evt : pp = data + 22 -> data <= hm <= data + 22 ->
    forall R, rfull R -> rtbl Wq R RTQ0 -> ftbl Wq spz m2 STO1 -> ftbl Wq ds m2 DTQS ->
    evt asegs (fun ms => exists R' m', ms = MS R' F (ret_pc ra) fc None m' (seg_rom asegs) /\ rfull R'
                 /\ rtbl Wq R' RTQ4 /\ ftbl Wq ds m' DTQ4 /\ ftbl Wq d' m' BTQ4 /\ Pq m' /\ mem_inv asegs m' /\ ACONST m')
        (MS R F (Z_to_bv 64 0x126038) fc None m2 (seg_rom asegs)).
  Proof.
    intros HPP HHM R RF HRT HST HDT.
    pose proof q_vals as (V1 & V2 & V3). pose proof VR as (VR1 & VR2 & VR3).
    assert (EPP : edenot (wenv Wq) (EVar 51) = edenot (wenv Wq) (EAlu ALU_ADD (EVar 50) (ELit 22))).
    { cbn [edenot]. change (ev (wenv Wq) 51) with (Z_to_bv 64 pp). change (ev (wenv Wq) 50) with (Z_to_bv 64 data).
      rewrite w_add by (clear - VR1 VR2 HPP; lia). f_equal. exact HPP. }
    apply (rtbl_subst _ _ _ _ _ EPP) in HRT. apply (ftbl_subst _ _ _ _ _ _ EPP) in HDT.
    tnormq HRT. tnormq HDT.
    assert (HBT : ftbl Wq d' m2 []) by constructor.
    assert (HP : Pq m2) by (split; [apply munch_refl | apply wmono_refl]).
    dkrunQ HRT HST HDT HBT HP MI2 600%nat [AMEMSET_STUB] (@nil bool).
    { apply Forall_nil. }
    intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
    lazymatch type of HTS1 with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS1; clear E end.
    apply Forall_cons_iff in HTS1 as [HS1 HTS1]. apply Forall_cons_iff in HTS1 as [HD1 HTS1].
    apply Forall_cons_iff in HTS1 as [HB1 _]. cbn [fst snd] in HS1, HD1, HB1.
    cbn [s_pc].
    rgetq HRT1 (10%bv : reg) G10. rgetq HRT1 (11%bv : reg) G11. rgetq HRT1 (12%bv : reg) G12.
    rgetq HRT1 (2%bv : reg) G2. rgetq HRT1 (1%bv : reg) G1.
    rewrite <- (Z_to_bv_bv_unsigned sp) in G2. rewrite w_addm in G2 by (pose proof q_ranges as (QR1 & QR2 & QR3 & _); clear - QR1 QR2 QR3; lia).
    eapply (qs_memset _ R1 m1 _ _ _ _ 0x1202c8 (spz + -160) RF1 HRT1 HS1 HD1 HB1 HP1 HMI1 (q_aconst m1 HP1) G10 G11 G12 G2 G1);
      [ clear; lia | clear; lia | reflexivity | vm_compute; reflexivity .. | ].
    intros R2 m3 RF2 HRT2 HS2 HD2 HB2 HP2 HMI2 AC3.
    rewrite LbB_DCtorK.sub_off in HS2. tnormq HRT2. tnormq HS2. tnormq HB2.
    dkrunQ HRT2 HS2 HD2 HB2 HP2 HMI2 600%nat [0x125fc0] [true].
    { split_scs. cbn [sc_denot edenot]. unfold HLib.Eseed, reg_ev, Wq;
        lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
              Init.Nat.add Nat.sub nth app].
      rewrite !w_mul_g, !w_add_g. rewrite br_geu by (clear - V2 HHM VR1 VR3 BR LO SPHI; destruct BR as (B1 & B2 & B3); unfold AIMG_TOP in *; lia).
      apply (proj2 (Bool.negb_true_iff _)). apply Z.ltb_ge. clear - HHM. lia. }
    intros R4 m4 RF4 HRT4 HTS4 HP4 HMI4 MU4 WM4.
    lazymatch type of HTS4 with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS4; clear E end.
    apply Forall_cons_iff in HTS4 as [HS4 HTS4]. apply Forall_cons_iff in HTS4 as [HD4 HTS4].
    apply Forall_cons_iff in HTS4 as [HB4 _]. cbn [fst snd] in HS4, HD4, HB4.
    cbn [s_pc].
    rewrite (MS_full_eq R4 F _ fc m4 _ RF4).
    rgetq HRT4 (1%bv : reg) K1.
    apply o_ret_ok. rewrite <- (rfull_eq R4 RF4). rewrite K1. exists R4, m4.
    split; [reflexivity|]. split; [exact RF4|].
    split; [apply (rtbl_sub _ _ _ _ HRT4); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HD4); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HB4); vm_compute; reflexivity|].
    split; [exact HP4|]. split; [exact HMI4 | exact (q_aconst m4 HP4)].
  Qed.
End O23S.

Definition DTQL : list fent := DTO0 ++ [(72, 8%nat, EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 54)) (ELit 1)); (80, 8%nat, EVar 54);
                                       (88, 8%nat, EVar 53)].

Definition kst_l : list kentry :=
  kst_o ++
  [ KWr (SA (EVar 53) 0) (EMd M_MUL (ELit 2) (EVar 54)); KRange (EVar 53) 0x6e8000 (2 ^ 47);
    KRange (EVar 54) 48 (2 ^ 25);
    KDisj (SA (EVar 53) 0) (EMd M_MUL (ELit 2) (EVar 54)) (SA (EVar 33) (-8192)) (ELit 8192);
    KDisj (SA (EVar 53) 0) (EMd M_MUL (ELit 2) (EVar 54)) (SA (EVar 32) 0) (ELit 392) ].

Section O23L.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m2 : mem) (ds c data pp hm lo d' asz : Z).
  Hypothesis DSO : app_obj ds DS_SIZE.
  Hypothesis DSW : wr_at asegs m2 ds DS_SIZE.
  Hypothesis STK : stk asegs m2 lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - 8192.
  Hypothesis SPHI : bv_unsigned sp <= 2 ^ 47.
  Hypothesis SPD : ds + DS_SIZE <= lo.
  Hypothesis CR : 0 <= c <= 255.
  Hypothesis VR : 0 <= data < 2 ^ 64 /\ 0 <= pp < 2 ^ 64 /\ 0 <= hm < 2 ^ 64.
  Hypothesis AR : 48 <= asz <= 2 ^ 25 /\ asz mod 16 = 0.

  Hypothesis BR : AIMG_TOP <= d' /\ d' + 2 * asz <= lo /\ d' mod 16 = 0.
  Hypothesis BDS : d' + 2 * asz <= ds \/ ds + DS_SIZE <= d'.
  Hypothesis BW : wr_at asegs m2 d' (2 * asz).
  Hypothesis BA : addressable m2 d' (2 * asz).
  Hypothesis BV : shvis m2 d' (d' + 2 * asz).
  Hypothesis BAPP : in_app_mem d' (d' + 2 * asz).
  Hypothesis BAC : aconst_ok (d', d' + 2 * asz).
  Hypothesis MI2 : mem_inv asegs m2.
  Hypothesis AC2 : ACONST m2.

  Notation spz := (bv_unsigned sp) (only parsing).
  Definition Wl : list word :=
    [Z_to_bv 64 ds; sp; ra; Z_to_bv 64 c; s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; gp; tp;
     Z_to_bv 64 data; Z_to_bv 64 pp; Z_to_bv 64 hm; Z_to_bv 64 d'; Z_to_bv 64 asz].

  Definition Pl (m : mem) : Prop := munch [(spz - 8192, spz); (ds + 24, ds + 108); (d' + asz - 1, d' + 2 * asz)] m2 m /\ wmono asegs m2 m.

  Lemma l_ranges : 0 <= spz < 2 ^ 64 /\ aceil + 8192 <= spz /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000
                   /\ AIMG_TOP <= ds /\ ds + DS_SIZE <= lo.
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    pose proof aceil_facts as ((A1 & A2) & _). pose proof DSO as (O1 & _).
    clear - R A1 A2 O1 CEIL LO SPD. repeat split; lia.
  Qed.

  Lemma l_keep : forall m, Pl m -> mem_inv asegs m ->
    stk asegs m lo spz /\ wr_at asegs m ds DS_SIZE /\ wr_at asegs m d' (2 * asz).
  Proof.
    intros m [MU WM] MI. split; [| split; [eapply wr_at_transport; [exact DSW | exact WM] | eapply wr_at_transport; [exact BW | exact WM]]].
    pose proof l_ranges as (R1 & R2 & R3 & R4 & R5).
    eapply stk_transport; [exact STK | exact MU | exact WM |]. intros x Hx. right.
    pose proof STK as (T1 & T2 & T3). destruct (T3 x Hx) as [HV _].
    pose proof (WM (wa x) HV) as HV'.
    assert (HX : AIMG_TOP <= bv_unsigned (wa x)).
    { unfold wa. rewrite unsigned_lit by (clear - T1 T2 Hx; lia). clear - Hx CEIL R3. unfold AIMG_TOP. lia. }
    rewrite (BakeStackRep.wview_high m (wa x) HX) in HV'.
    destruct (m (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction].
  Qed.

  Lemma l_aconst : forall m, Pl m -> ACONST m.
  Proof.
    intros m [MU WM]. pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    pose proof aceil_facts as ((A1 & A2) & _). pose proof DSO as (O1 & O2 & O3).
    eapply ACONST_frame; [exact AC2 | exact MU | exact WM |].
    apply Forall_cons; [apply LbB_DPdK.aconst_ok_hi; clear - A1 CEIL LO R; lia|].
    apply Forall_cons; [| apply Forall_cons; [intros a Ha; apply BAC; cbn [fst snd] in *; pose proof AR as (AR1 & _); clear - Ha AR1; lia | apply Forall_nil]].
    clear - O1 O2 O3. unfold AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, DS_SIZE in *.
    destruct O2 as [O2|O2]; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP; lia.
  Qed.

  Ltac evwl := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wl;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Lemma l_vals : 0 <= ds < 2 ^ 64 /\ 0 <= d' < 2 ^ 64 /\ 0 <= c < 2 ^ 64 /\ 0 <= asz < 2 ^ 64 /\ 0 <= d' + 2 * asz < 2 ^ 64.
  Proof.
    pose proof l_ranges as (R1 & R2 & R3 & R4 & R5). pose proof BR as (B1 & B2 & B3). pose proof DSO as (O1 & O2 & O3).
    pose proof AR as (A1 & A2).
    clear - R1 R4 R5 B1 B2 LO SPHI CR O3 A1. unfold AIMG_TOP, DS_SIZE, AAPP_HI in *. lia.
  Qed.

  Lemma kst_l_ok : forall R X m, Pl m -> mem_inv asegs m -> know_ok asegs (HLib.Eseed R (Wl ++ X)) m kst_l.
  Proof.
    intros R X m PW MI. destruct (l_keep m PW MI) as (ST & DW & BW').
    pose proof l_ranges as (R1 & R2 & R3 & R4 & R5). pose proof DSO as (O1 & O2 & O3).
    pose proof BR as (B1 & B2 & B3). pose proof AR as (A1 & A2). pose proof l_vals as (V1 & V2 & V3 & V4 & V5).
    assert (E2 : mul_div M_MUL (Z_to_bv 64 2) (Z_to_bv 64 asz) = Z_to_bv 64 (2 * asz)) by apply w_mul_g.
    unfold DS_SIZE, AIMG_TOP, AAPP_HI in *.
    unfold know_ok, kst_l, kst_o. repeat apply Forall_cons; try apply Forall_nil.
    - eapply kwr_of_stk; [exact ST | | |]; evwl; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwl. lia.
    - eapply kwr_of_wr_at; [exact DW | | |]; evwl; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwl. rewrite unsigned_lit by lia. lia.
    - cbn [kentry_ok]. evwl. rewrite !unsigned_lit by lia. lia.
    - eapply kwr_of_wr_at; [exact BW' | | |]; evwl; rewrite ?E2, ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwl. rewrite unsigned_lit by lia. lia.
    - cbn [kentry_ok]. evwl. rewrite unsigned_lit by lia. lia.
    - cbn [kentry_ok]. evwl. rewrite E2, !unsigned_lit by lia. lia.
    - cbn [kentry_ok]. evwl. rewrite E2, !unsigned_lit by lia. clear - BDS R4 R5 O1 O3 B1 B2 V5. unfold DS_SIZE in *. lia.
  Qed.

  Definition RTL0 : list (reg * expr) :=
    re_subst (EVar 51) (EAlu ALU_ADD (EVar 50) (EAlu ALU_ADD (EVar 54) (ELit (-1)))) RTQ0.
  Definition DTL0 : list fent :=
    fe_subst (EVar 51) (EAlu ALU_ADD (EVar 50) (EAlu ALU_ADD (EVar 54) (ELit (-1)))) DTQL.
  Definition CB_L : expr := EAlu ALU_ADD (EVar 53) (EVar 54).
  Definition TB_L : expr := EAlu ALU_ADD (EVar 53) (EMd M_MUL (ELit 2) (EVar 54)).
  Definition kst_l2 : list kentry :=
    kst_l ++
    [ KDisj (SA CB_L (-1)) (ELit 1) (SA (EVar 33) (-8192)) (ELit 8192); KDisj (SA CB_L (-1)) (ELit 1) (SA (EVar 32) 0) (ELit 392);
      KDisj (SA TB_L (-1)) (ELit 1) (SA (EVar 33) (-8192)) (ELit 8192); KDisj (SA TB_L (-1)) (ELit 1) (SA (EVar 32) 0) (ELit 392);
      KDisj (SA CB_L (-1)) (ELit 1) (SA TB_L (-1)) (ELit 1);
      KWr (SA CB_L (-1)) (ELit 1); KWr (SA TB_L (-1)) (ELit 1) ].

  Lemma l_cbv : forall E, (forall n, (32 <= n < 55)%N -> ev E n = ev (wenv Wl) n) ->
    bv_unsigned (edenot E CB_L) = d' + asz /\ bv_unsigned (edenot E TB_L) = d' + 2 * asz.
  Proof.
    intros E HE. pose proof l_vals as (V1 & V2 & V3 & V4 & V5). pose proof AR as (A1 & A2).
    unfold CB_L, TB_L. cbn [edenot]. rewrite !HE by lia.
    unfold wenv, HLib.Eseed, reg_ev, Wl;
      lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
            Init.Nat.add Nat.sub nth app].
    rewrite !w_mul_g, !w_add_g. rewrite !unsigned_lit by (clear - V2 V4 V5; lia). split; reflexivity.
  Qed.

  Lemma kst_l2_ok : forall R X m, Pl m -> mem_inv asegs m -> know_ok asegs (HLib.Eseed R (Wl ++ X)) m kst_l2.
  Proof.
    intros R X m PW MI. unfold know_ok, kst_l2. apply Forall_app. split; [exact (kst_l_ok R X m PW MI)|].
    destruct (l_keep m PW MI) as (ST & DW & BW').
    pose proof l_ranges as (R1 & R2 & R3 & R4 & R5). pose proof DSO as (O1 & O2 & O3).
    pose proof BR as (B1 & B2 & B3). pose proof AR as (A1 & A2). pose proof l_vals as (V1 & V2 & V3 & V4 & V5).
    destruct (l_cbv (HLib.Eseed R (Wl ++ X)) ltac:(intros n Hn; apply Eseed_wenv; exact Hn)) as [C1 C2].
    assert (EC : estart (HLib.Eseed R (Wl ++ X)) (SA CB_L (-1)) = d' + asz - 1) by (unfold estart; cbn [a_base a_off]; rewrite C1; lia).
    assert (ET : estart (HLib.Eseed R (Wl ++ X)) (SA TB_L (-1)) = d' + 2 * asz - 1) by (unfold estart; cbn [a_base a_off]; rewrite C2; lia).
    unfold DS_SIZE, AIMG_TOP, AAPP_HI in *.
    assert (VE : forall k, 0 <= k < 2 ^ 64 -> bv_unsigned (edenot (HLib.Eseed R (Wl ++ X)) (ELit k)) = k)
      by (intros k Hk; cbn [edenot]; apply unsigned_lit; exact Hk).
    assert (S33 : estart (HLib.Eseed R (Wl ++ X)) (SA (EVar 33) (-8192)) = spz - 8192) by (evwl; lia).
    assert (S32 : estart (HLib.Eseed R (Wl ++ X)) (SA (EVar 32) 0) = ds) by (evwl; rewrite unsigned_lit by lia; lia).
    apply Forall_cons; [cbn [kentry_ok]; unfold flat, elenZ; rewrite EC, S33, !VE by lia; clear - B1 B2 A1 R1 R2 R3 LO; lia|].
    apply Forall_cons; [cbn [kentry_ok]; unfold flat, elenZ; rewrite EC, S32, !VE by lia; clear - B1 B2 A1 R4 R5 O1 O3 LO BDS V5; lia|].
    apply Forall_cons; [cbn [kentry_ok]; unfold flat, elenZ; rewrite ET, S33, !VE by lia; clear - B1 B2 A1 R1 R2 R3 LO; lia|].
    apply Forall_cons; [cbn [kentry_ok]; unfold flat, elenZ; rewrite ET, S32, !VE by lia; clear - B1 B2 A1 R4 R5 O1 O3 LO BDS V5; lia|].
    apply Forall_cons; [cbn [kentry_ok]; unfold flat, elenZ; rewrite EC, ET, !VE by lia; clear - B1 B2 A1 V5; lia|].
    apply Forall_cons; [eapply kwr_of_wr_at; [exact BW' | rewrite EC; lia | rewrite EC; unfold elenZ; rewrite VE by lia; lia
                                              | unfold elenZ; rewrite VE by lia; lia]|].
    apply Forall_cons; [eapply kwr_of_wr_at; [exact BW' | rewrite ET; lia | rewrite ET; unfold elenZ; rewrite VE by lia; lia
                                              | unfold elenZ; rewrite VE by lia; lia]|].
    apply Forall_nil.
  Qed.

  Definition tSl (T : list fent) (ks : list (Z * nat)) : tab := (EVar 33, spz, -8192, 0, T, ks).
  Definition tDl (T : list fent) (ks : list (Z * nat)) : tab := (EVar 32, ds, 24, 108, T, ks).
  Definition tCl (T : list fent) (ks : list (Z * nat)) : tab := (CB_L, d' + asz, -1, 0, T, ks).
  Definition tTl (T : list fent) (ks : list (Z * nat)) : tab := (TB_L, d' + 2 * asz, -1, 0, T, ks).

  Lemma tabs_wf_l : forall ST DT CT TT ks1 ks2 ks3 ks4,
    fwcl (wbound Wl) ST = true -> fwcl (wbound Wl) DT = true -> fwcl (wbound Wl) CT = true -> fwcl (wbound Wl) TT = true ->
    fin (-8192) 0 (fkeys ST ++ ks1) = true -> fin 24 108 (fkeys DT ++ ks2) = true ->
    fin (-1) 0 (fkeys CT ++ ks3) = true -> fin (-1) 0 (fkeys TT ++ ks4) = true ->
    tabs_wf Wl [tSl ST ks1; tDl DT ks2; tCl CT ks3; tTl TT ks4].
  Proof.
    intros ST DT CT TT ks1 ks2 ks3 ks4 C1 C2 C3 C4 F1 F2 F3 F4. pose proof l_ranges as (R1 & R2 & R3 & R4 & R5).
    pose proof BR as (B1 & B2 & B3). pose proof DSO as (O1 & O2 & O3). pose proof AR as (A1 & A2).
    pose proof l_vals as (V1 & V2 & V3 & V4 & V5).
    destruct (l_cbv (wenv Wl) ltac:(intros; reflexivity)) as [CC CT'].
    assert (VD : bv_unsigned (edenot (wenv Wl) (EVar 32)) = ds) by (apply unsigned_lit; clear - V1; lia).
    split.
    - repeat constructor; cbn [tb tB tlo thi ttbl tks tSl tDl tCl tTl]; try reflexivity; try assumption;
        clear - R1 R2 R3 R4 R5 B1 B2 O1 O3 LO A1 V5; unfold DS_SIZE, AIMG_TOP, AAPP_HI in *; lia.
    - intros t1 t2 H1 H2 Hb. cbn [In] in H1, H2.
      destruct H1 as [<-|[<-|[<-|[<-|[]]]]]; destruct H2 as [<-|[<-|[<-|[<-|[]]]]]; cbn [tb tB tlo thi tSl tDl tCl tTl] in *;
        try (vm_compute in Hb; discriminate Hb); clear - R1 R2 R3 R4 R5 B1 B2 BDS LO A1; unfold DS_SIZE in *; lia.
  Qed.

  Lemma tabs_ok_l : forall m ST DT CT TT ks1 ks2 ks3 ks4, Pl m -> mem_inv asegs m ->
    ftbl Wl spz m ST -> ftbl Wl ds m DT -> ftbl Wl (d' + asz) m CT -> ftbl Wl (d' + 2 * asz) m TT ->
    fin (-8192) 0 ks1 = true -> fin 24 108 ks2 = true -> fin (-1) 0 ks3 = true -> fin (-1) 0 ks4 = true ->
    tabs_ok Wl m [tSl ST ks1; tDl DT ks2; tCl CT ks3; tTl TT ks4].
  Proof.
    intros m ST DT CT TT ks1 ks2 ks3 ks4 PW MI H1 H2 H3 H4 F1 F2 F3 F4. destruct (l_keep m PW MI) as (ST0 & DW & BW').
    pose proof l_ranges as (R1 & R2 & R3 & R4 & R5). pose proof AR as (A1 & A2). pose proof BR as (B1 & B2 & B3).
    apply Forall_cons; [split; [exact H1|]|].
    { intros k w Hi. cbn [tB tks tSl] in *. destruct (fin_In _ _ _ k w F1 Hi) as (K1 & K2 & K3).
      pose proof (wr_at_of_stk asegs m lo spz ST0) as W. eapply wr_at_sub; [exact W | lia | lia | lia]. }
    apply Forall_cons; [split; [exact H2|]|].
    { intros k w Hi. cbn [tB tks tDl] in *. destruct (fin_In _ _ _ k w F2 Hi) as (K1 & K2 & K3).
      eapply wr_at_sub; [exact DW | unfold DS_SIZE; lia | unfold DS_SIZE; lia | lia]. }
    apply Forall_cons; [split; [exact H3|]|].
    { intros k w Hi. cbn [tB tks tCl] in *. destruct (fin_In _ _ _ k w F3 Hi) as (K1 & K2 & K3).
      eapply wr_at_sub; [exact BW' | clear - K1 A1; lia | clear - K2 A1; lia | lia]. }
    apply Forall_cons; [split; [exact H4|] | apply Forall_nil].
    { intros k w Hi. cbn [tB tks tTl] in *. destruct (fin_In _ _ _ k w F4 Hi) as (K1 & K2 & K3).
      eapply wr_at_sub; [exact BW' | clear - K1 A1; lia | clear - K2 A1; lia | lia]. }
  Qed.

  Lemma Pl_step : forall ST DT CT TT ks1 ks2 ks3 ks4 m m',
    Pl m -> munch (winsT [tSl ST ks1; tDl DT ks2; tCl CT ks3; tTl TT ks4]) m m' -> wmono asegs m m' -> mem_inv asegs m' -> Pl m'.
  Proof.
    intros ST DT CT TT ks1 ks2 ks3 ks4 m m' [MU0 WM0] MU WM _. split; [| eapply wmono_trans; eassumption].
    pose proof AR as (A1 & A2).
    eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU].
    apply sub_fp_of. unfold winsT. cbn [map tB tlo thi tSl tDl tCl tTl].
    apply Forall_cons; [sfp_in (spz - 8192, spz)|].
    apply Forall_cons; [sfp_in (ds + 24, ds + 108)|].
    apply Forall_cons; [exists (d' + asz - 1, d' + 2 * asz); split; [right; right; left; reflexivity | cbn [fst snd]; clear - A1; lia]|].
    apply Forall_cons; [exists (d' + asz - 1, d' + 2 * asz); split; [right; right; left; reflexivity | cbn [fst snd]; clear - A1; lia]|].
    apply Forall_nil.
  Qed.

  Ltac dkrunL HRT HST HDT HCT HTT HP HMI fuel stops dirs :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HST with ftbl _ _ _ ?ST =>
      lazymatch type of HDT with ftbl _ _ _ ?DT =>
      lazymatch type of HCT with ftbl _ _ _ ?CT =>
      lazymatch type of HTT with ftbl _ _ _ ?TT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tSl ST []; tDl DT []; tCl CT []; tTl TT []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR dirs [] []) (SS pc (HLib.srs sr_id RT) [] (kst_l2 ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wl) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) ST) in
          let ks2 := eval vm_compute in (nkeys (EVar 32) (s_log SSr) DT) in
          let ks3 := eval vm_compute in (nkeys CB_L (s_log SSr) CT) in
          let ks4 := eval vm_compute in (nkeys TB_L (s_log SSr) TT) in
          eapply (dk_runN Wl [tSl ST ks1; tDl DT ks2; tCl CT ks3; tTl TT ks4]
                    (tabs_wf_l ST DT CT TT ks1 ks2 ks3 ks4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pl (Pl_step ST DT CT TT ks1 ks2 ks3 ks4)
                    Q R F pc fc m ro RT [] kst_l2 fuel stops (SCR dirs [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok_l; [exact HP | exact HMI | exact HST | exact HDT | exact HCT | exact HTT | vm_compute; reflexivity .. ]
          | exact HP | exact HMI | apply kst_l2_ok; [exact HP | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end
    end.

  Lemma ql_memset : forall (Q : machine_state -> Prop) R1 m RT ST DT CT TT (retpc spc : Z),
    rfull R1 -> rtbl Wl R1 RT -> ftbl Wl spz m ST -> ftbl Wl ds m DT -> ftbl Wl (d' + asz) m CT -> ftbl Wl (d' + 2 * asz) m TT ->
    Pl m -> mem_inv asegs m -> ACONST m ->
    PropExec.getr R1 10 = Z_to_bv 64 (d' + asz) -> PropExec.getr R1 11 = Z_to_bv 64 0 -> PropExec.getr R1 12 = Z_to_bv 64 (asz - 1) ->
    PropExec.getr R1 2 = Z_to_bv 64 spc -> PropExec.getr R1 1 = Z_to_bv 64 retpc ->
    spz - 256 <= spc <= spz - 128 -> 0 <= retpc < 2 ^ 64 -> retpc mod 2 = 0 ->
    fin (-8192) 0 (fkeys ST) = true -> fin 24 108 (fkeys DT) = true -> fin (-1) 0 (fkeys CT) = true -> fin (-1) 0 (fkeys TT) = true ->
    (forall R2 m3, rfull R2 -> rtbl Wl R2 (LbB_DCtorK.keptf RT) -> ftbl Wl spz m3 (fabove (spc - spz) ST) ->
       ftbl Wl ds m3 DT -> ftbl Wl (d' + asz) m3 CT -> ftbl Wl (d' + 2 * asz) m3 TT ->
       rw_cells asegs m3 (d' + asz) [CB (Z.to_nat (asz - 1)) (poison_bytes (Z.to_nat (asz - 1)) 0)] ->
       Pl m3 -> mem_inv asegs m3 -> ACONST m3 ->
       evt asegs Q (MS R2 F (Z_to_bv 64 retpc) fc None m3 (seg_rom asegs))) ->
    evt asegs Q (MS R1 F (Z_to_bv 64 AMEMSET_STUB) fc None m (seg_rom asegs)).
  Proof.
    intros Q R1 m RT ST DT CT TT retpc spc RF HRT HST HDT HCT HTT HP HMI AC G10 G11 G12 G2 G1 Hs Hr1 Hr2 Hf1 Hf2 Hf3 Hf4 K.
    pose proof l_ranges as (R1' & R2' & R3' & R4' & R5'). pose proof BR as (B1 & B2 & B3). pose proof AR as (A1 & A2).
    pose proof l_vals as (V1 & V2 & V3 & V4 & V5).
    destruct (l_keep m HP HMI) as (ST0 & DW & BW').
    assert (Us : bv_unsigned (PropExec.getr R1 2) = spc) by (rewrite G2; apply unsigned_lit; clear - Hs R1' R2' R3'; lia).
    destruct (rw_cells_of_wr_hi m (d' + asz) (asz - 1) ltac:(eapply wr_at_sub; [exact BW' | clear - A1; lia | clear - A1; lia | clear - A1; lia])
               ltac:(clear - B1 A1; unfold AIMG_TOP in *; lia) ltac:(clear - A1; lia)) as [junk DST].
    assert (BA' : addressable m d' (2 * asz)).
    { eapply addressable_transport; [exact BA | exact (proj1 HP) | exact (proj2 HP) |].
      cbn [disjoint_from].
      pose proof (app_obj_sh_apart ds DS_SIZE d' (2 * asz) DSO ltac:(clear - B1; unfold AIMG_TOP in *; lia)
                    ltac:(clear - B2 R1' LO SPHI; unfold AAPP_HI; lia) ltac:(clear - A1; lia)) as D1.
      assert (N : nsh (2 * asz) = asz / 4) by (unfold nsh; clear - A1 A2; Z.div_mod_to_equations; lia).
      rewrite N in D1 |- *.
      repeat split; [clear - B2 LO R2' R3' R1' B1 A1 A2; unfold sh, ASHADOW_BASE, AIMG_TOP in *; Z.div_mod_to_equations; lia
                    | clear - D1; unfold DS_SIZE in D1; lia | clear - BAPP A1 A2; unfold in_app_mem, sh, ASHADOW_BASE, AHI_LO, AAPP_HI in *; Z.div_mod_to_equations; lia | ..]. }
    destruct (stk_split asegs m lo (spc - AINTRIN_STACK) spz ST0 ltac:(clear - Hs LO; unfold AINTRIN_STACK in *; lia)) as [_ S2].
    destruct (stk_split asegs m (spc - AINTRIN_STACK) spc spz S2 ltac:(clear - Hs; unfold AINTRIN_STACK in *; lia)) as [S3 _].
    rewrite <- Us in S3.
    eapply evt_cut.
    { eapply (memset_icpt_u R1 F fc m (d' + asz) (asz - 1) 0 (bv_unsigned (PropExec.getr R1 2) - AINTRIN_STACK) junk);
        try eassumption; try (clear; lia).
      - clear - V2 V4 A1. lia.
      - clear - A1. lia.
      - clear - V5 A1. lia.
      - eapply addressable_accessible; [exact BA' | clear - A1; lia | clear - A1; lia | clear - B2 LO R1' SPHI; unfold AAPP_HI; lia].
      - assert (SVm : shvis m d' (d' + 2 * asz)).
        { apply (shvis_wmono_hi m2 m _ _ BV (proj2 HP)). pose proof (hull_lo_le d' ltac:(clear - B1; unfold AIMG_TOP in *; lia)) as (HL1 & HL2 & HL3).
          clear - HL1 HL2 HL3 B1. unfold sh, ASHADOW_BASE, AIMG_TOP in *. Z.div_mod_to_equations. lia. }
        eapply shvis_sub; [exact SVm | clear - B1; unfold AIMG_TOP in *; lia | clear - A1; lia | clear - A1; lia | clear - A1; lia
                          | clear - B1 A1; unfold AIMG_TOP in *; lia].
      - rewrite Us. clear - Hs R2' LO. unfold AINTRIN_STACK in *. lia.
      - clear - A1. lia.
      - eapply in_app_mem_sub; [exact BAPP | clear - A1; lia | clear - A1; lia].
      - intros a Ha. apply BAC. cbn [fst snd] in *. clear - Ha A1. lia.
      - left. rewrite Us. clear - Hs B2 LO A1. unfold AINTRIN_STACK in *. lia. }
    intros ms' (Rr & mr & E2 & RF2 & KP & MU & WM & MI2' & AC2' & CB & ST2). subst ms'.
    rewrite G1, ret_pc_even by lia. rewrite Us in MU.
    apply K.
    - exact RF2.
    - eapply rtbl_keep; [exact (LbB_DCtorK.rtbl_keptf Wl R1 RT HRT) | apply LbB_DCtorK.rsub_keptf | exact KP].
    - eapply (ftbl_munch Wl spz m mr (fabove (spc - spz) ST) _ (spc - spz) 0);
        [exact (ftbl_fabove _ _ _ _ _ HST) | exact MU | exact WM | exact (fin_fabove _ _ _ Hf1) |].
      cbn [disjoint_from]. clear - Hs B1 B2 LO R2' A1. unfold AINTRIN_STACK in *. lia.
    - eapply (ftbl_munch Wl ds m mr DT _ 24 108); [exact HDT | exact MU | exact WM | exact Hf2 |].
      cbn [disjoint_from]. clear - Hs B1 B2 LO R2' R5' BDS A1. unfold AINTRIN_STACK, DS_SIZE in *. lia.
    - eapply (ftbl_munch Wl (d' + asz) m mr CT _ (-1) 0); [exact HCT | exact MU | exact WM | exact Hf3 |].
      cbn [disjoint_from]. clear - Hs B1 B2 LO R2' A1. unfold AINTRIN_STACK in *. lia.
    - eapply (ftbl_munch Wl (d' + 2 * asz) m mr TT _ (-1) 0); [exact HTT | exact MU | exact WM | exact Hf4 |].
      cbn [disjoint_from]. clear - Hs B1 B2 LO R2' A1. unfold AINTRIN_STACK in *. lia.
    - exact CB.
    - destruct HP as [MU0 WM0]. split; [| eapply wmono_trans; eassumption].
      eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. apply sub_fp_of.
      apply Forall_cons; [exists (d' + asz - 1, d' + 2 * asz); split; [right; right; left; reflexivity | cbn [fst snd]; clear - A1; lia]|].
      apply Forall_cons; [exists (spz - 8192, spz); split; [left; reflexivity | cbn [fst snd]; clear - Hs; unfold AINTRIN_STACK; lia]|].
      apply Forall_nil.
    - exact MI2'.
    - exact AC2'.
  Qed.

  Ltac tnorml H :=
    lazymatch type of H with
    | ftbl ?W ?B ?m ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    | rtbl ?W ?R ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    end.

  Ltac rgetl HRT r H :=
    lazymatch type of HRT with
    | rtbl ?W ?R ?RT =>
        let e := eval vm_compute in (match List.find (fun re => bv_eqb (fst re) r) RT with Some re => snd re | None => ELit 0 end) in
        assert (H : PropExec.getr R r = edenot (wenv W) e)
          by (apply (rtbl_In W R RT r e HRT); apply LbB_DCtorK.inb_In'; vm_compute; reflexivity);
        unfold wenv in H; cbn [edenot] in H; unfold HLib.Eseed, reg_ev, Wl in H;
        lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
              Init.Nat.add Nat.sub nth app] in H;
        rewrite ?w_mul_g, ?w_add_g in H
    end.

  Definition DTL4 : list fent :=
    [(24, 8%nat, ELit 0); (32, 8%nat, ELit 0); (40, 8%nat, ELit 0); (48, 8%nat, EVar 53);
     (56, 8%nat, EAlu ALU_ADD (EVar 53) (EVar 54));
     (64, 8%nat, EAlu ALU_ADD (EAlu ALU_ADD (EVar 53) (EMd M_MUL (ELit 2) (EVar 54))) (ELit (-1)));
     (96, 8%nat, EAlu ALU_ADD (EVar 53) (EVar 54)); (104, 4%nat, ELit 16);
     (72, 8%nat, EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 54)) (ELit 1));
     (80, 8%nat, EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 54)) (ELit (-1))); (88, 8%nat, EVar 53)].

  Lemma l_bit : forall (E : env), (forall n, (32 <= n < 55)%N -> ev E n = ev (wenv Wl) n) ->
    edenot E (EAlu ALU_AND (EExt false 0 1 (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 54)) (ELit 1))) (ELit 1)) = Z_to_bv 64 1.
  Proof.
    intros E HE. pose proof l_vals as (V1 & V2 & V3 & V4 & V5). pose proof AR as (A1 & A2).
    cbn [edenot]. rewrite HE by lia.
    change (ev (wenv Wl) 54) with (Z_to_bv 64 asz). rewrite w_mul_g, w_add_g. apply bit_odd; clear - A1; lia.
  Qed.

  Lemma o23l_evt : pp = data + (asz - 1) -> data <= hm <= data + (asz - 1) ->
    forall R, rfull R -> rtbl Wl R RTQ0 -> ftbl Wl spz m2 STO1 -> ftbl Wl ds m2 DTQL ->
    evt asegs (fun ms => exists R' m', ms = MS R' F (ret_pc ra) fc None m' (seg_rom asegs) /\ rfull R'
                 /\ rtbl Wl R' RTQ4 /\ ftbl Wl ds m' DTL4 /\ ftbl Wl (d' + asz) m' [(-1, 1%nat, EVar 35)]
                 /\ ftbl Wl (d' + 2 * asz) m' [(-1, 1%nat, ELit 0)]
                 /\ rw_cells asegs m' (d' + asz) [CB (Z.to_nat (asz - 1)) (poison_bytes (Z.to_nat (asz - 1)) 0)]
                 /\ Pl m' /\ mem_inv asegs m' /\ ACONST m')
        (MS R F (Z_to_bv 64 0x126038) fc None m2 (seg_rom asegs)).
  Proof.
    intros HPP HHM R RF HRT HST HDT.
    pose proof l_vals as (V1 & V2 & V3 & V4 & V5). pose proof VR as (VR1 & VR2 & VR3). pose proof AR as (A1 & A2).
    pose proof BR as (B1 & B2 & B3).
    assert (EPP : edenot (wenv Wl) (EVar 51) = edenot (wenv Wl) (EAlu ALU_ADD (EVar 50) (EAlu ALU_ADD (EVar 54) (ELit (-1))))).
    { cbn [edenot]. change (ev (wenv Wl) 51) with (Z_to_bv 64 pp). change (ev (wenv Wl) 50) with (Z_to_bv 64 data).
      change (ev (wenv Wl) 54) with (Z_to_bv 64 asz). rewrite !w_add_g. f_equal. exact HPP. }
    apply (rtbl_subst _ _ _ _ _ EPP) in HRT. apply (ftbl_subst _ _ _ _ _ _ EPP) in HDT.
    tnorml HRT. tnorml HDT.
    assert (HCT : ftbl Wl (d' + asz) m2 []) by constructor.
    assert (HTT : ftbl Wl (d' + 2 * asz) m2 []) by constructor.
    assert (HP : Pl m2) by (split; [apply munch_refl | apply wmono_refl]).
    dkrunL HRT HST HDT HCT HTT HP MI2 600%nat [AMEMSET_STUB] [true; false; true].
    { assert (LB : edenot (HLib.Eseed R (Wl ++ []))
                     (EAlu ALU_AND (EExt false 0 1 (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 54)) (ELit 1))) (ELit 1)) = Z_to_bv 64 1)
        by (apply l_bit; intros n Hn; apply Eseed_wenv; exact Hn).
      split_scs; cbn [sc_denot]; rewrite ?LB; cbn [edenot].
      - rewrite br_ne by (clear; lia). reflexivity.
      - cbn [edenot]. unfold HLib.Eseed, reg_ev, Wl;
          lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
                Init.Nat.add Nat.sub nth app].
        rewrite !w_mul_g, !w_add_g. rewrite br_geu by (clear - A1; lia). apply (proj2 (Bool.negb_false_iff _)). apply Z.ltb_lt. clear - A1. lia.
      - rewrite br_ne by (clear; lia). reflexivity. }
    intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
    lazymatch type of HTS1 with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS1; clear E end.
    apply Forall_cons_iff in HTS1 as [HS1 HTS1]. apply Forall_cons_iff in HTS1 as [HD1 HTS1].
    apply Forall_cons_iff in HTS1 as [HC1 HTS1]. apply Forall_cons_iff in HTS1 as [HT1 _]. cbn [fst snd] in HS1, HD1, HC1, HT1.
    cbn [s_pc].
    rgetl HRT1 (10%bv : reg) G10. rgetl HRT1 (11%bv : reg) G11. rgetl HRT1 (12%bv : reg) G12.
    rgetl HRT1 (2%bv : reg) G2. rgetl HRT1 (1%bv : reg) G1.
    rewrite <- (Z_to_bv_bv_unsigned sp) in G2. rewrite w_addm in G2 by (pose proof l_ranges as (QR1 & QR2 & QR3 & _); clear - QR1 QR2 QR3; lia).
    cbn [edenot] in G11.
    eapply (ql_memset _ R1 m1 _ _ _ _ _ 0x1202c8 (spz + -160) RF1 HRT1 HS1 HD1 HC1 HT1 HP1 HMI1 (l_aconst m1 HP1) G10 G11 G12 G2 G1);
      [ clear; lia | clear; lia | reflexivity | vm_compute; reflexivity .. | ].
    intros R2 m3 RF2 HRT2 HS2 HD2 HC2 HT2 ZZ HP2 HMI2 AC3.
    rewrite LbB_DCtorK.sub_off in HS2. tnorml HRT2. tnorml HS2.
    dkrunL HRT2 HS2 HD2 HC2 HT2 HP2 HMI2 600%nat [0x125fc0] [true; false; true; true].
    { assert (LB : edenot (HLib.Eseed R2 (Wl ++ []))
                     (EAlu ALU_AND (EExt false 0 1 (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 54)) (ELit 1))) (ELit 1)) = Z_to_bv 64 1)
        by (apply l_bit; intros n Hn; apply Eseed_wenv; exact Hn).
      split_scs; cbn [sc_denot]; rewrite ?LB; cbn [edenot].
      - unfold HLib.Eseed, reg_ev, Wl;
          lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
                Init.Nat.add Nat.sub nth app].
        rewrite !w_mul_g, !w_add_g. rewrite br_geu by (clear - V2 V4 V5 HHM A1; lia).
        apply (proj2 (Bool.negb_true_iff _)). apply Z.ltb_ge. clear - HHM. lia.
      - rewrite br_ne by (clear; lia). reflexivity.
      - rewrite br_eq by (clear; lia). reflexivity.
      - rewrite br_ne by (clear; lia). reflexivity. }
    intros R4 m4 RF4 HRT4 HTS4 HP4 HMI4 MU4 WM4.
    lazymatch type of HTS4 with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS4; clear E end.
    apply Forall_cons_iff in HTS4 as [HS4 HTS4]. apply Forall_cons_iff in HTS4 as [HD4 HTS4].
    apply Forall_cons_iff in HTS4 as [HC4 HTS4]. apply Forall_cons_iff in HTS4 as [HT4 _]. cbn [fst snd] in HS4, HD4, HC4, HT4.
    cbn [s_pc].
    rewrite (MS_full_eq R4 F _ fc m4 _ RF4).
    rgetl HRT4 (1%bv : reg) K1.
    apply o_ret_ok. rewrite <- (rfull_eq R4 RF4). rewrite K1. exists R4, m4.
    split; [reflexivity|]. split; [exact RF4|].
    split; [apply (rtbl_sub _ _ _ _ HRT4); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HD4); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HC4); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HT4); vm_compute; reflexivity|].
    split.
    { eapply rw_cells_transport; [exact ZZ | exact MU4 | exact WM4 |].
      unfold winsT. cbn [map tB tlo thi tSl tDl tCl tTl disjoint_from cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - A1; lia).
      pose proof l_ranges as (QR1 & QR2 & QR3 & QR4 & QR5).
      clear - QR1 QR2 QR3 QR4 QR5 B1 B2 BDS LO A1. unfold DS_SIZE in *. lia. }
    split; [exact HP4|]. split; [exact HMI4 | exact (l_aconst m4 HP4)].
  Qed.

End O23L.
