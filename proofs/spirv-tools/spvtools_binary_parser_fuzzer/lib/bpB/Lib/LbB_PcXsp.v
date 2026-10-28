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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PcStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DPdK LbB_PcOvf.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition AXLOOP : Z := 0x124ad8.
Definition AXRET : Z := 0x124b5c.
Definition AXMRA : Z := 0x124b04.
Definition AXORA : Z := 0x124b20.

Lemma bv_signed_small63x : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite (SymExec3.SX2.swrap_small 64 (bv_unsigned (Z_to_bv 64 z)) (2 ^ 63) (2 ^ 64));
    [| reflexivity | reflexivity | rewrite u64_of_Z by lia; lia | lia].
  rewrite u64_of_Z by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia.
Qed.
Lemma br_ltx : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !bv_signed_small63x by lia. reflexivity. Qed.
Lemma br_gex : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !bv_signed_small63x by lia. reflexivity. Qed.

Lemma stk_wmono_hix : forall W m m' lo hi, stk asegs m lo hi -> munch W m m' -> wmono asegs m m' -> AIMG_TOP <= lo ->
  stk asegs m' lo hi.
Proof.
  intros W m m' lo hi STK MU WM HL. eapply stk_transport; [exact STK | exact MU | exact WM |]. intros x Hx. right.
  pose proof STK as (T1 & T2 & T3). destruct (T3 x Hx) as [HV _].
  pose proof (WM (wa x) HV) as HV'.
  assert (HX : AIMG_TOP <= bv_unsigned (wa x)) by (unfold wa; rewrite unsigned_lit by (clear - T1 T2 Hx; lia); clear - Hx HL; lia).
  rewrite (BakeStackRep.wview_high m' (wa x) HX) in HV'.
  destruct (m' (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction].
Qed.

Definition kst_x : list kentry :=
  [ KWr (SA (EVar 33) (-8192)) (ELit 8192); KRange (EVar 33) (2 ^ 45) (2 ^ 47);
    KWr (SA (EVar 32) 0) (ELit 392); KRange (EVar 32) 0x6e8000 (2 ^ 47 - 392);
    KDisj (SA (EVar 32) 0) (ELit 392) (SA (EVar 33) (-8192)) (ELit 8192);
    KImg 0x17e000 0x186000; KWord (SA (EVar 32) 8) 8 (ELit VT_SB_A) ].

Definition STX : list fent :=
  [(-8, 8%nat, EVar 34); (-16, 8%nat, EVar 37); (-24, 8%nat, EVar 38); (-32, 8%nat, EVar 39); (-40, 8%nat, EVar 40);
   (-48, 8%nat, EVar 41); (-56, 8%nat, EVar 42)].

Definition DTX : list fent := [(56, 8%nat, EVar 52); (64, 8%nat, EVar 53)].

Definition DTV : list fent := [(8, 8%nat, ELit VT_SB_A)].

Definition RTXE : list (reg * expr) :=
  [(1%bv, EVar 34); (2%bv, EVar 33); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 37); (9%bv, EVar 38);
   (18%bv, EVar 39); (19%bv, EVar 40); (20%bv, EVar 41); (21%bv, EVar 42); (22%bv, EVar 43); (23%bv, EVar 44);
   (24%bv, EVar 45); (25%bv, EVar 46); (26%bv, EVar 47); (27%bv, EVar 48);
   (10%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (11%bv, EVar 35); (12%bv, EVar 36)].

Definition RTXH : list (reg * expr) :=
  [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-64))); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 51); (9%bv, EVar 36);
   (18%bv, EAlu ALU_ADD (EVar 35) (EVar 51)); (19%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (21%bv, ELit 18446744073709551615);
   (22%bv, EVar 43); (23%bv, EVar 44); (24%bv, EVar 45); (25%bv, EVar 46); (26%bv, EVar 47); (27%bv, EVar 48)].

Definition RTXA : list (reg * expr) :=
  [(1%bv, ELit 0x124b04); (2%bv, EAlu ALU_ADD (EVar 33) (ELit (-64))); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 51);
   (9%bv, EVar 36); (10%bv, EVar 52); (11%bv, EAlu ALU_ADD (EVar 35) (EVar 51)); (12%bv, EVar 55);
   (18%bv, EAlu ALU_ADD (EVar 35) (EVar 51)); (19%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (20%bv, EVar 55);
   (21%bv, ELit 18446744073709551615);
   (22%bv, EVar 43); (23%bv, EVar 44); (24%bv, EVar 45); (25%bv, EVar 46); (26%bv, EVar 47); (27%bv, EVar 48)].

Definition RTXO : list (reg * expr) :=
  [(1%bv, ELit 0x124b20); (2%bv, EAlu ALU_ADD (EVar 33) (ELit (-64))); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 51);
   (9%bv, EVar 36); (10%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (11%bv, EVar 54);
   (18%bv, EAlu ALU_ADD (EVar 35) (EVar 51)); (19%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (21%bv, ELit 18446744073709551615);
   (22%bv, EVar 43); (23%bv, EVar 44); (24%bv, EVar 45); (25%bv, EVar 46); (26%bv, EVar 47); (27%bv, EVar 48)].

Definition RTXM : list (reg * expr) :=
  [(1%bv, ELit 0x124b04); (2%bv, EAlu ALU_ADD (EVar 33) (ELit (-64))); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 51);
   (9%bv, EVar 36); (10%bv, EVar 52); (18%bv, EAlu ALU_ADD (EVar 35) (EVar 51)); (19%bv, EAlu ALU_ADD (EVar 32) (ELit 8));
   (20%bv, EVar 55); (21%bv, ELit 18446744073709551615);
   (22%bv, EVar 43); (23%bv, EVar 44); (24%bv, EVar 45); (25%bv, EVar 46); (26%bv, EVar 47); (27%bv, EVar 48)].

Definition RTXC : list (reg * expr) :=
  [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-64))); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EAlu ALU_ADD (EVar 51) (EVar 55));
   (9%bv, EVar 36); (18%bv, EAlu ALU_ADD (EVar 35) (EAlu ALU_ADD (EVar 51) (EVar 55)));
   (19%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (21%bv, ELit 18446744073709551615);
   (22%bv, EVar 43); (23%bv, EVar 44); (24%bv, EVar 45); (25%bv, EVar 46); (26%bv, EVar 47); (27%bv, EVar 48)].
Definition DTXC : list fent := [(56, 8%nat, EAlu ALU_ADD (EVar 52) (EVar 55)); (64, 8%nat, EVar 53)].

Definition RTXR : list (reg * expr) :=
  [(1%bv, EVar 34); (2%bv, EVar 33); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 37); (9%bv, EVar 38);
   (18%bv, EVar 39); (19%bv, EVar 40); (20%bv, EVar 41); (21%bv, EVar 42);
   (22%bv, EVar 43); (23%bv, EVar 44); (24%bv, EVar 45); (25%bv, EVar 46); (26%bv, EVar 47); (27%bv, EVar 48);
   (10%bv, EAlu ALU_ADD (EVar 51) (EVar 55))].

Definition RTXP : list (reg * expr) :=
  [(1%bv, ELit 0x124b20); (2%bv, EAlu ALU_ADD (EVar 33) (ELit (-64))); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 51);
   (9%bv, EVar 36); (10%bv, EVar 54); (18%bv, EAlu ALU_ADD (EVar 35) (EVar 51)); (19%bv, EAlu ALU_ADD (EVar 32) (ELit 8));
   (21%bv, ELit 18446744073709551615);
   (22%bv, EVar 43); (23%bv, EVar 44); (24%bv, EVar 45); (25%bv, EVar 46); (26%bv, EVar 47); (27%bv, EVar 48)].

Definition RTXB : list (reg * expr) :=
  [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-64))); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EAlu ALU_ADD (EVar 51) (ELit 1));
   (9%bv, EVar 36); (18%bv, EAlu ALU_ADD (EAlu ALU_ADD (EVar 35) (EVar 51)) (ELit 1));
   (19%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (21%bv, ELit 18446744073709551615);
   (22%bv, EVar 43); (23%bv, EVar 44); (24%bv, EVar 45); (25%bv, EVar 46); (26%bv, EVar 47); (27%bv, EVar 48)].

Definition RTXR1 : list (reg * expr) :=
  [(1%bv, EVar 34); (2%bv, EVar 33); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 37); (9%bv, EVar 38);
   (18%bv, EVar 39); (19%bv, EVar 40); (20%bv, EVar 41); (21%bv, EVar 42);
   (22%bv, EVar 43); (23%bv, EVar 44); (24%bv, EVar 45); (25%bv, EVar 46); (26%bv, EVar 47); (27%bv, EVar 48);
   (10%bv, EAlu ALU_ADD (EVar 51) (ELit 1))].

Section XR.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m0 : mem) (ds p n i pp ep c k lo : Z).
  Hypothesis DSO : app_obj ds DS_SIZE.
  Hypothesis DSW : wr_at asegs m0 ds DS_SIZE.
  Hypothesis STK : stk asegs m0 lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - 8192.
  Hypothesis SPHI : bv_unsigned sp <= 2 ^ 47.
  Hypothesis SPD : ds + DS_SIZE <= lo.
  Hypothesis RL : relro0 m0.
  Hypothesis VT0 : rw_cells asegs m0 (ds + 8) [C8 (Z_to_bv 64 VT_SB_A)].
  Hypothesis VR : 0 <= p /\ p + n <= 2 ^ 47 /\ 0 < n <= 2 ^ 24 /\ 0 <= i <= n /\ 0 <= pp < 2 ^ 47 /\ 0 <= ep < 2 ^ 47
                  /\ 0 <= c <= 255 /\ 0 <= k <= n.

  Notation spz := (bv_unsigned sp) (only parsing).
  Definition Wx : list word :=
    [Z_to_bv 64 ds; sp; ra; Z_to_bv 64 p; Z_to_bv 64 n; s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; gp; tp;
     Z_to_bv 64 i; Z_to_bv 64 pp; Z_to_bv 64 ep; Z_to_bv 64 c; Z_to_bv 64 k].

  Definition Px (m : mem) : Prop := munch [(spz - 64, spz); (ds + 56, ds + 72)] m0 m /\ wmono asegs m0 m.

  Lemma x_ranges : 0 <= spz < 2 ^ 64 /\ aceil + 8192 <= spz /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000
                   /\ AIMG_TOP <= ds /\ ds + DS_SIZE <= lo.
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    pose proof aceil_facts as ((A1 & A2) & _). pose proof DSO as (O1 & _).
    clear - R A1 A2 O1 CEIL LO SPD. repeat split; lia.
  Qed.

  Lemma x_keep : forall m, Px m -> mem_inv asegs m -> stk asegs m lo spz /\ wr_at asegs m ds DS_SIZE /\ relro0 m
                               /\ rw_cells asegs m (ds + 8) [C8 (Z_to_bv 64 VT_SB_A)].
  Proof.
    intros m [MU WM] MI. pose proof x_ranges as (R1 & R2 & R3 & R4 & R5).
    assert (VTm : rw_cells asegs m (ds + 8) [C8 (Z_to_bv 64 VT_SB_A)]).
    { eapply rw_cells_transport; [exact VT0 | exact MU | exact WM |]. cbn [cells_size csize disjoint_from fst snd].
      clear - R2 R4 R5 LO. unfold DS_SIZE in *. lia. }
    split; [| split; [eapply wr_at_transport; [exact DSW | exact WM] | split; [| exact VTm]]].
    - eapply stk_transport; [exact STK | exact MU | exact WM |]. intros x Hx. right.
      pose proof STK as (T1 & T2 & T3). destruct (T3 x Hx) as [HV _].
      pose proof (WM (wa x) HV) as HV'.
      assert (HX : AIMG_TOP <= bv_unsigned (wa x)).
      { unfold wa. rewrite unsigned_lit by (clear - T1 T2 Hx; lia). clear - Hx CEIL R3. unfold AIMG_TOP. lia. }
      rewrite (BakeStackRep.wview_high m (wa x) HX) in HV'.
      destruct (m (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction].
    - intros a Ha. rewrite <- (RL a Ha). apply MU. rewrite unsigned_lit by (clear - Ha; lia). cbn [outside].
      clear - Ha R2 R4 R3. unfold AIMG_TOP in *. lia.
  Qed.

  Ltac evwx := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wx;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Lemma kst_x_ok : forall R X m, Px m -> mem_inv asegs m -> know_ok asegs (HLib.Eseed R (Wx ++ X)) m kst_x.
  Proof.
    intros R X m PW MI. destruct (x_keep m PW MI) as (ST & DW & RL' & VTm).
    pose proof x_ranges as (R1 & R2 & R3 & R4 & R5). pose proof DSO as (O1 & O2 & O3).
    unfold DS_SIZE, AIMG_TOP, AAPP_HI in *.
    unfold know_ok, kst_x. repeat apply Forall_cons; try apply Forall_nil.
    - eapply kwr_of_stk; [exact ST | | |]; evwx; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwx. lia.
    - eapply kwr_of_wr_at; [exact DW | | |]; evwx; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evwx. rewrite unsigned_lit by lia. lia.
    - cbn [kentry_ok]. evwx. rewrite !unsigned_lit by lia. lia.
    - apply kimg_relro. exact RL'.
    - assert (VTf : ftbl Wx ds m DTV) by (apply ftbl_of_C8; cbn [edenot]; exact VTm).
      pose proof (ftbl_kn Wx ds m DTV (HLib.Eseed R (Wx ++ X)) (EVar 32) 8 16 VTf) as K1.
      apply (Forall_inv (l:=[])). apply K1.
      + cbn [edenot]. rewrite Eseed_wenv by (vm_compute; split; [discriminate | reflexivity]). evwx. apply unsigned_lit. lia.
      + intros n0 Hn0. apply Eseed_wenv. exact Hn0.
      + vm_compute. reflexivity.
      + vm_compute. reflexivity.
      + lia.
      + lia.
  Qed.

  Definition tSx (T : list fent) (ks : list (Z * nat)) : tab := (EVar 33, spz, -64, 0, T, ks).
  Definition tDx (T : list fent) (ks : list (Z * nat)) : tab := (EVar 32, ds, 56, 72, T, ks).

  Lemma tabs_wf_x : forall ST DT ks1 ks2,
    fwcl (wbound Wx) ST = true -> fwcl (wbound Wx) DT = true ->
    fin (-64) 0 (fkeys ST ++ ks1) = true -> fin 56 72 (fkeys DT ++ ks2) = true ->
    tabs_wf Wx [tSx ST ks1; tDx DT ks2].
  Proof.
    intros ST DT ks1 ks2 C1 C2 F1 F2. pose proof x_ranges as (R1 & R2 & R3 & R4 & R5).
    assert (VD : bv_unsigned (edenot (wenv Wx) (EVar 32)) = ds) by (apply unsigned_lit; unfold AIMG_TOP, DS_SIZE in *; lia).
    split.
    - repeat constructor; cbn [tb tB tlo thi ttbl tks tSx tDx]; try reflexivity; try assumption;
        clear - R1 R2 R3 R4 R5 LO; unfold DS_SIZE, AIMG_TOP in *; lia.
    - intros t1 t2 H1 H2 Hb. cbn [In] in H1, H2.
      destruct H1 as [<-|[<-|[]]]; destruct H2 as [<-|[<-|[]]]; cbn [tb tB tlo thi tSx tDx] in *;
        try (vm_compute in Hb; discriminate Hb); clear - R1 R2 R3 R4 R5 LO; unfold DS_SIZE in *; lia.
  Qed.

  Lemma tabs_ok_x : forall m ST DT ks1 ks2, Px m -> mem_inv asegs m ->
    ftbl Wx spz m ST -> ftbl Wx ds m DT -> fin (-64) 0 ks1 = true -> fin 56 72 ks2 = true ->
    tabs_ok Wx m [tSx ST ks1; tDx DT ks2].
  Proof.
    intros m ST DT ks1 ks2 PW MI H1 H2 F1 F2. destruct (x_keep m PW MI) as (ST0 & DW & _).
    pose proof x_ranges as (R1 & R2 & R3 & R4 & R5).
    apply Forall_cons; [split; [exact H1|]|]; [|apply Forall_cons; [split; [exact H2|]| apply Forall_nil]].
    - intros k' w Hi. cbn [tB tks tSx] in *. destruct (fin_In _ _ _ k' w F1 Hi) as (K1 & K2 & K3).
      pose proof (wr_at_of_stk asegs m lo spz ST0) as W. eapply wr_at_sub; [exact W | lia | lia | lia].
    - intros k' w Hi. cbn [tB tks tDx] in *. destruct (fin_In _ _ _ k' w F2 Hi) as (K1 & K2 & K3).
      eapply wr_at_sub; [exact DW | unfold DS_SIZE; lia | unfold DS_SIZE; lia | lia].
  Qed.

  Lemma Px_step : forall ST DT ks1 ks2 m m', Px m -> munch (winsT [tSx ST ks1; tDx DT ks2]) m m' -> wmono asegs m m' ->
    mem_inv asegs m' -> Px m'.
  Proof.
    intros ST DT ks1 ks2 m m' [MU0 WM0] MU WM _. split; [| eapply wmono_trans; eassumption].
    eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU].
    apply sub_fp_of. unfold winsT. cbn [map tB tlo thi tSx tDx].
    apply Forall_cons; [sfp_in (spz - 64, spz)|].
    apply Forall_cons; [sfp_in (ds + 56, ds + 72)| apply Forall_nil].
  Qed.

  Ltac dkrunX kst kst_ok HRT HST HDT HP HMI fuel stops dirs :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HST with ftbl _ _ _ ?ST =>
      lazymatch type of HDT with ftbl _ _ _ ?DT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tSx ST []; tDx DT []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR dirs [] []) (SS pc (HLib.srs sr_id RT) [] (kst ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wx) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) ST) in
          let ks2 := eval vm_compute in (nkeys (EVar 32) (s_log SSr) DT) in
          eapply (dk_runN Wx [tSx ST ks1; tDx DT ks2]
                    (tabs_wf_x ST DT ks1 ks2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Px (Px_step ST DT ks1 ks2)
                    Q R F pc fc m ro RT [] kst fuel stops (SCR dirs [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok_x; [exact HP | exact HMI | exact HST | exact HDT | vm_compute; reflexivity .. ]
          | exact HP | exact HMI | apply kst_ok; [exact HP | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end
    end.

  Lemma x_vals : 0 <= ds < 2 ^ 64 /\ 0 <= p < 2 ^ 64 /\ 0 <= n < 2 ^ 64 /\ 0 <= i < 2 ^ 64 /\ 0 <= pp < 2 ^ 64
                 /\ 0 <= ep < 2 ^ 64 /\ 0 <= c < 2 ^ 64 /\ 0 <= k < 2 ^ 64.
  Proof.
    pose proof x_ranges as (R1 & R2 & R3 & R4 & R5). pose proof DSO as (O1 & O2 & O3).
    pose proof VR as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
    clear - R1 R4 R5 LO SPHI O3 V1 V2 V3 V4 V5 V6 V7 V8. unfold AIMG_TOP, DS_SIZE, AAPP_HI in *. lia.
  Qed.

  Ltac tnormx H :=
    lazymatch type of H with
    | ftbl ?W ?B ?m ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    | rtbl ?W ?R ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    end.

  Ltac scsx := split_scs; cbn [sc_denot edenot]; unfold HLib.Eseed, reg_ev, Wx;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app]; rewrite ?LbB_PcOvf.w_mul_g, ?LbB_PcOvf.w_add_g.

  Ltac tsplit2 HTS HS HD :=
    lazymatch type of HTS with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS; clear E end;
    apply Forall_cons_iff in HTS as [HS HTS]; apply Forall_cons_iff in HTS as [HD _]; cbn [fst snd] in HS, HD.

  Lemma xr_entry : i = 0 -> forall R, rfull R -> rtbl Wx R RTXE -> ftbl Wx ds m0 DTX -> mem_inv asegs m0 ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 AXLOOP) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl Wx R1 RTXH /\ ftbl Wx spz m1 STX /\ ftbl Wx ds m1 DTX /\ Px m1 /\ mem_inv asegs m1)
        (MS R F (Z_to_bv 64 AXSP) fc None m0 (seg_rom asegs)).
  Proof.
    intros EI0 R RF HRT HDT MI.
    assert (HST : ftbl Wx spz m0 []) by constructor.
    assert (HP : Px m0) by (split; [apply munch_refl | apply wmono_refl]).
    unfold AXSP.
    pose proof x_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8). pose proof VR as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    dkrunX kst_x kst_x_ok HRT HST HDT HP MI 600%nat [AXLOOP] [false].
    { scsx. rewrite br_gex by (clear - W3; lia). apply (proj2 (Bool.negb_false_iff _)). apply Z.ltb_lt. clear - W3. lia. }
    intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1. tsplit2 HTS1 HS1 HD1.
    assert (E51 : edenot (wenv Wx) (ELit 0) = edenot (wenv Wx) (EVar 51))
      by (change (edenot (wenv Wx) (EVar 51)) with (Z_to_bv 64 i); rewrite EI0; reflexivity).
    apply (LbB_PcOvf.rtbl_subst _ _ _ _ _ E51) in HRT1.
    assert (E35 : edenot (wenv Wx) (EVar 35) = edenot (wenv Wx) (EAlu ALU_ADD (EVar 35) (EVar 51))).
    { cbn [edenot]. change (ev (wenv Wx) 35) with (Z_to_bv 64 p). change (ev (wenv Wx) 51) with (Z_to_bv 64 i).
      rewrite LbB_PcOvf.w_add_g, EI0, Z.add_0_r. reflexivity. }
    apply (LbB_PcOvf.rtbl_subst _ _ _ _ _ E35) in HRT1. tnormx HRT1.
    apply evt_done. exists R1, m1. split; [reflexivity|]. split; [exact RF1|].
    split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HS1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HD1); vm_compute; reflexivity|].
    split; [exact HP1 | exact HMI1].
  Qed.

  Lemma xr_a : forall R, rfull R -> rtbl Wx R RTXH -> ftbl Wx spz m0 STX -> ftbl Wx ds m0 DTX -> mem_inv asegs m0 ->
    pp < ep -> i < n -> ((n - i < ep - pp /\ k = n - i) \/ (ep - pp <= n - i /\ k = ep - pp)) ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 AMEMMOVE_STUB) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl Wx R1 RTXA /\ ftbl Wx spz m1 STX /\ ftbl Wx ds m1 DTX /\ Px m1 /\ mem_inv asegs m1)
        (MS R F (Z_to_bv 64 AXLOOP) fc None m0 (seg_rom asegs)).
  Proof.
    intros R RF HRT HST HDT MI HPE HIN CASE.
    assert (HP : Px m0) by (split; [apply munch_refl | apply wmono_refl]).
    pose proof x_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8). pose proof VR as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    unfold AXLOOP.
    destruct CASE as [(C1 & C2)|(C1 & C2)].
    - dkrunX kst_x kst_x_ok HRT HST HDT HP MI 600%nat [AMEMMOVE_STUB] [false; true; false].
      { scsx.
        - rewrite br_eq by (clear - W3 W4; lia). apply Z.eqb_neq. clear - HIN. lia.
        - rewrite br_ltx by (clear - W3 W4 W5 W6 HPE; lia). apply Z.ltb_lt. clear - C1. lia.
        - rewrite br_geu by (clear - V5 V6; lia). apply (proj2 (Bool.negb_false_iff _)). apply Z.ltb_lt. exact HPE. }
      intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1. tsplit2 HTS1 HS1 HD1.
      assert (EK : edenot (wenv Wx) (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit (-1)) (EVar 51))) = edenot (wenv Wx) (EVar 55)).
      { cbn [edenot]. change (ev (wenv Wx) 36) with (Z_to_bv 64 n). change (ev (wenv Wx) 51) with (Z_to_bv 64 i).
        change (ev (wenv Wx) 55) with (Z_to_bv 64 k). rewrite LbB_PcOvf.w_mul_g, LbB_PcOvf.w_add_g. f_equal. clear - C2. lia. }
      apply (LbB_PcOvf.rtbl_subst _ _ _ _ _ EK) in HRT1. tnormx HRT1.
      apply evt_done. exists R1, m1. split; [reflexivity|]. split; [exact RF1|].
      split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
      split; [apply (ftbl_sub _ _ _ _ _ HS1); vm_compute; reflexivity|].
      split; [apply (ftbl_sub _ _ _ _ _ HD1); vm_compute; reflexivity|].
      split; [exact HP1 | exact HMI1].
    - dkrunX kst_x kst_x_ok HRT HST HDT HP MI 600%nat [AMEMMOVE_STUB] [false; false; false].
      { scsx.
        - rewrite br_eq by (clear - W5 W6 HPE; lia). apply Z.eqb_neq. clear - HPE. lia.
        - rewrite br_ltx by (clear - W3 W4 W5 W6 HPE; lia). apply Z.ltb_ge. clear - C1. lia.
        - rewrite br_geu by (clear - V5 V6; lia). apply (proj2 (Bool.negb_false_iff _)). apply Z.ltb_lt. exact HPE. }
      intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1. tsplit2 HTS1 HS1 HD1.
      assert (EK : edenot (wenv Wx) (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 52)) (EVar 53)) = edenot (wenv Wx) (EVar 55)).
      { cbn [edenot]. change (ev (wenv Wx) 52) with (Z_to_bv 64 pp). change (ev (wenv Wx) 53) with (Z_to_bv 64 ep).
        change (ev (wenv Wx) 55) with (Z_to_bv 64 k). rewrite LbB_PcOvf.w_mul_g, LbB_PcOvf.w_add_g. f_equal. clear - C2. lia. }
      apply (LbB_PcOvf.rtbl_subst _ _ _ _ _ EK) in HRT1. tnormx HRT1.
      apply evt_done. exists R1, m1. split; [reflexivity|]. split; [exact RF1|].
      split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
      split; [apply (ftbl_sub _ _ _ _ _ HS1); vm_compute; reflexivity|].
      split; [apply (ftbl_sub _ _ _ _ _ HD1); vm_compute; reflexivity|].
      split; [exact HP1 | exact HMI1].
  Qed.

  Definition kst_xb : list kentry := kst_x ++ [KWord (SA (EAlu ALU_ADD (EVar 35) (EVar 51)) 0) 1 (EVar 54)].

  Lemma ext_byte : forall x, 0 <= x <= 255 -> ext_val false 0 1 (Z_to_bv 64 x) = Z_to_bv 64 x.
  Proof.
    intros x Hc. unfold ext_val, ext_Z. cbn [Z.of_nat Nat.mul].
    rewrite unsigned_lit by lia. change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 1)) with 256. rewrite Z.div_1_r.
    change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite (Z.mod_small x 256) by lia. reflexivity.
  Qed.

  Lemma xr_b : forall R, rfull R -> rtbl Wx R RTXH -> ftbl Wx spz m0 STX -> ftbl Wx ds m0 DTX -> mem_inv asegs m0 ->
    ep <= pp -> i < n ->
    (forall m, Px m -> mem_inv asegs m -> kentry_ok asegs (HLib.Eseed R (Wx ++ [])) m (KWord (SA (EAlu ALU_ADD (EVar 35) (EVar 51)) 0) 1 (EVar 54))) ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 AOVF) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl Wx R1 RTXO /\ ftbl Wx spz m1 STX /\ ftbl Wx ds m1 DTX /\ Px m1 /\ mem_inv asegs m1)
        (MS R F (Z_to_bv 64 AXLOOP) fc None m0 (seg_rom asegs)).
  Proof.
    intros R RF HRT HST HDT MI HPE HIN KSRC.
    assert (HP : Px m0) by (split; [apply munch_refl | apply wmono_refl]).
    assert (KB : forall m, Px m -> mem_inv asegs m -> know_ok asegs (HLib.Eseed R (Wx ++ [])) m kst_xb).
    { intros m PW MIm. unfold know_ok, kst_xb. apply Forall_app. split; [exact (kst_x_ok R [] m PW MIm)|].
      apply Forall_cons; [exact (KSRC m PW MIm) | apply Forall_nil]. }
    pose proof x_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8). pose proof VR as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    unfold AXLOOP.
    dkrunX kst_xb KB HRT HST HDT HP MI 600%nat [AOVF] [true].
    { scsx.
      - unfold flat, estart, elenZ. cbn [a_base a_off edenot]. unfold HLib.Eseed, reg_ev, Wx;
          lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
                Init.Nat.add Nat.sub nth app].
        rewrite LbB_PcOvf.w_add_g, !unsigned_lit by (clear - W1 W2 W4; lia). clear - W1 W2 W4. lia.
      - rewrite br_geu by (clear - V5 V6; lia). apply (proj2 (Bool.negb_true_iff _)). apply Z.ltb_ge. exact HPE. }
    intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1. tsplit2 HTS1 HS1 HD1.
    assert (EC : edenot (wenv Wx) (EExt false 0 1 (EVar 54)) = edenot (wenv Wx) (EVar 54)).
    { cbn [edenot]. change (ev (wenv Wx) 54) with (Z_to_bv 64 c). apply ext_byte. clear - W7. lia. }
    apply (LbB_PcOvf.rtbl_subst _ _ _ _ _ EC) in HRT1. tnormx HRT1.
    apply evt_done. exists R1, m1. split; [reflexivity|]. split; [exact RF1|].
    split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HS1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HD1); vm_compute; reflexivity|].
    split; [exact HP1 | exact HMI1].
  Qed.

  Lemma xr_a2c : forall R, rfull R -> rtbl Wx R RTXM -> ftbl Wx spz m0 STX -> ftbl Wx ds m0 DTX -> mem_inv asegs m0 ->
    i + k < n ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 AXLOOP) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl Wx R1 RTXC /\ ftbl Wx spz m1 STX /\ ftbl Wx ds m1 DTXC /\ Px m1 /\ mem_inv asegs m1)
        (MS R F (Z_to_bv 64 AXMRA) fc None m0 (seg_rom asegs)).
  Proof.
    intros R RF HRT HST HDT MI HIK.
    assert (HP : Px m0) by (split; [apply munch_refl | apply wmono_refl]).
    pose proof x_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8). pose proof VR as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    unfold AXMRA.
    dkrunX kst_x kst_x_ok HRT HST HDT HP MI 600%nat [AXLOOP] [false].
    { scsx. rewrite br_gex by (clear - W3 W4 W8; lia). apply (proj2 (Bool.negb_false_iff _)). apply Z.ltb_lt. exact HIK. }
    intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1. tsplit2 HTS1 HS1 HD1.
    apply evt_done. exists R1, m1. split; [reflexivity|]. split; [exact RF1|].
    split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HS1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HD1); vm_compute; reflexivity|].
    split; [exact HP1 | exact HMI1].
  Qed.

  Lemma xr_a2x : forall R, rfull R -> rtbl Wx R RTXM -> ftbl Wx spz m0 STX -> ftbl Wx ds m0 DTX -> mem_inv asegs m0 ->
    n <= i + k ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 AXRET) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl Wx R1 RTXR /\ ftbl Wx ds m1 DTXC /\ Px m1 /\ mem_inv asegs m1)
        (MS R F (Z_to_bv 64 AXMRA) fc None m0 (seg_rom asegs)).
  Proof.
    intros R RF HRT HST HDT MI HIK.
    assert (HP : Px m0) by (split; [apply munch_refl | apply wmono_refl]).
    pose proof x_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8). pose proof VR as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    unfold AXMRA.
    dkrunX kst_x kst_x_ok HRT HST HDT HP MI 600%nat [AXRET] [true].
    { scsx. rewrite br_gex by (clear - W3 W4 W8; lia). apply (proj2 (Bool.negb_true_iff _)). apply Z.ltb_ge. exact HIK. }
    intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1. tsplit2 HTS1 HS1 HD1.
    apply evt_done. exists R1, m1. split; [reflexivity|]. split; [exact RF1|].
    split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HD1); vm_compute; reflexivity|].
    split; [exact HP1 | exact HMI1].
  Qed.

  Lemma xr_b2c : forall R, rfull R -> rtbl Wx R RTXP -> ftbl Wx spz m0 STX -> ftbl Wx ds m0 DTX -> mem_inv asegs m0 -> i + 1 < n ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 AXLOOP) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl Wx R1 RTXB /\ ftbl Wx spz m1 STX /\ ftbl Wx ds m1 DTX /\ Px m1 /\ mem_inv asegs m1)
        (MS R F (Z_to_bv 64 AXORA) fc None m0 (seg_rom asegs)).
  Proof.
    intros R RF HRT HST HDT MI HIK.
    assert (HP : Px m0) by (split; [apply munch_refl | apply wmono_refl]).
    pose proof x_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8). pose proof VR as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    unfold AXORA.
    dkrunX kst_x kst_x_ok HRT HST HDT HP MI 600%nat [AXLOOP] [false; true].
    { scsx.
      - rewrite br_ltx by (clear - W3 W4; lia). apply Z.ltb_lt. exact HIK.
      - rewrite br_eq by (clear - W7; lia). apply Z.eqb_neq. clear - W7. lia. }
    intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1. tsplit2 HTS1 HS1 HD1.
    apply evt_done. exists R1, m1. split; [reflexivity|]. split; [exact RF1|].
    split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HS1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HD1); vm_compute; reflexivity|].
    split; [exact HP1 | exact HMI1].
  Qed.

  Lemma xr_b2x : forall R, rfull R -> rtbl Wx R RTXP -> ftbl Wx spz m0 STX -> ftbl Wx ds m0 DTX -> mem_inv asegs m0 -> n <= i + 1 ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 AXRET) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl Wx R1 RTXR1 /\ ftbl Wx ds m1 DTX /\ Px m1 /\ mem_inv asegs m1)
        (MS R F (Z_to_bv 64 AXORA) fc None m0 (seg_rom asegs)).
  Proof.
    intros R RF HRT HST HDT MI HIK.
    assert (HP : Px m0) by (split; [apply munch_refl | apply wmono_refl]).
    pose proof x_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8). pose proof VR as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    unfold AXORA.
    dkrunX kst_x kst_x_ok HRT HST HDT HP MI 600%nat [AXRET] [false; false].
    { scsx.
      - rewrite br_ltx by (clear - W3 W4; lia). apply Z.ltb_ge. exact HIK.
      - rewrite br_eq by (clear - W7; lia). apply Z.eqb_neq. clear - W7. lia. }
    intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1. tsplit2 HTS1 HS1 HD1.
    apply evt_done. exists R1, m1. split; [reflexivity|]. split; [exact RF1|].
    split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HD1); vm_compute; reflexivity|].
    split; [exact HP1 | exact HMI1].
  Qed.
End XR.

Lemma xs_ret_ok : forall (Q : machine_state -> Prop) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (ret_pc x1) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 AXRET) fc None m (seg_rom asegs)).
Proof.
  intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HQ.
  unfold AXRET. step. apply evt_done. exact HQ.
Qed.

Section MM.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma memmove_icpt_u : forall R1 F fc m1 (d sa n lo : Z) src junk,
    rfull R1 -> PropExec.getr R1 10 = Z_to_bv 64 d -> PropExec.getr R1 11 = Z_to_bv 64 sa -> PropExec.getr R1 12 = Z_to_bv 64 n ->
    0 <= d -> 0 <= sa -> 0 <= n -> d + n < 2 ^ 64 -> sa + n < 2 ^ 64 ->
    bytes_at asegs m1 sa src -> length src = Z.to_nat n ->
    rw_cells asegs m1 d [CB (Z.to_nat n) junk] -> (sa + n <= d \/ d + n <= sa) ->
    accessible m1 sa n -> accessible m1 d n -> shvis m1 sa (sa + n) -> shvis m1 d (d + n) ->
    stk asegs m1 lo (bv_unsigned (PropExec.getr R1 2)) -> aceil <= lo -> lo <= bv_unsigned (PropExec.getr R1 2) - AINTRIN_STACK ->
    mem_inv asegs m1 -> ACONST m1 -> n <= 2 ^ 40 -> in_app_mem sa (sa + n) -> in_app_mem d (d + n) -> aconst_ok (d, d + n) ->
    (d + n <= lo \/ bv_unsigned (PropExec.getr R1 2) <= d) -> (sa + n <= lo \/ bv_unsigned (PropExec.getr R1 2) <= sa) ->
    evt asegs (ipost R1 F fc d n (bv_unsigned (PropExec.getr R1 2)) src m1)
        (MS R1 F (Z_to_bv 64 AMEMMOVE_STUB) fc None m1 (BLPropExec.seg_rom asegs)).
  Proof.
    intros R1 F fc m1 d sa n lo src junk RF H10 H11 H12 Hd Hsa Hn Hdn Hsn SRC LEN DST SEP ACS ACD SVS SVD ST CE LO MI AC N40 INS IND AOK DJ DJS.
    rewrite (MS_full_eq R1 F _ fc m1 _ RF).
    assert (Ud : bv_unsigned (PropExec.getr R1 10) = d) by (rewrite H10; apply unsigned_lit; lia).
    assert (Us : bv_unsigned (PropExec.getr R1 11) = sa) by (rewrite H11; apply unsigned_lit; lia).
    assert (Un : bv_unsigned (PropExec.getr R1 12) = n) by (rewrite H12; apply unsigned_lit; lia).
    eapply evt_mono; [eapply ((ah_memmove_icpt H HH) (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) (PropExec.getr R1 5) (PropExec.getr R1 6) (PropExec.getr R1 7) (PropExec.getr R1 8) (PropExec.getr R1 9) (PropExec.getr R1 10) (PropExec.getr R1 11) (PropExec.getr R1 12) (PropExec.getr R1 13) (PropExec.getr R1 14) (PropExec.getr R1 15) (PropExec.getr R1 16) (PropExec.getr R1 17) (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20) (PropExec.getr R1 21) (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25) (PropExec.getr R1 26) (PropExec.getr R1 27) (PropExec.getr R1 28) (PropExec.getr R1 29) (PropExec.getr R1 30) (PropExec.getr R1 31) F fc m1 src junk lo); rewrite ?Ud, ?Us, ?Un; eassumption|].
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E' & MU & WM & MI' & ST' & CB & AC').
    rewrite Ud, Un in *.
    exists (mkR (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) t0' t1' t2'
                (PropExec.getr R1 8) (PropExec.getr R1 9) (PropExec.getr R1 10) a1' a2' a3' a4' a5' a6' a7'
                (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20) (PropExec.getr R1 21) (PropExec.getr R1 22)
                (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25) (PropExec.getr R1 26) (PropExec.getr R1 27)
                t3' t4' t5' t6'), m'.
    split; [exact E'|]. split; [apply rfull_mkR|]. split.
    { intros r Hr. cbn [In KEPT] in Hr. repeat (destruct Hr as [<-|Hr]; [reflexivity|]). destruct Hr. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact AC'|]. split; [exact CB|].
    destruct ST' as (S0 & S1 & S). split; [lia|]. split; [lia|]. intros a Ha. apply S. unfold AINTRIN_STACK in *. lia.
  Qed.
End MM.

Section XC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m0 : mem) (ds p n i pp ep c k lo : Z).
  Hypothesis DSO : app_obj ds DS_SIZE.
  Hypothesis DSW : wr_at asegs m0 ds DS_SIZE.
  Hypothesis STK : stk asegs m0 lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - 8192.
  Hypothesis SPHI : bv_unsigned sp <= 2 ^ 47.
  Hypothesis SPD : ds + DS_SIZE <= lo.
  Hypothesis RL : relro0 m0.
  Hypothesis VT0 : rw_cells asegs m0 (ds + 8) [C8 (Z_to_bv 64 VT_SB_A)].
  Hypothesis VR : 0 <= p /\ p + n <= 2 ^ 47 /\ 0 < n <= 2 ^ 24 /\ 0 <= i <= n /\ 0 <= pp < 2 ^ 47 /\ 0 <= ep < 2 ^ 47
                  /\ 0 <= c <= 255 /\ 0 <= k <= n.
  Notation W := (Wx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n i pp ep c k).
  Notation spz := (bv_unsigned sp).

  Definition WC : list (Z * Z) := [(spz - 8192, spz); (ds + 56, ds + 72); (pp, pp + k)].

  Ltac rgetw HRT r G :=
    lazymatch type of HRT with
    | rtbl ?Wl ?R ?RT =>
        let e := eval vm_compute in (match List.find (fun re => bv_eqb (fst re) r) RT with Some re => snd re | None => ELit 0 end) in
        assert (G : PropExec.getr R r = edenot (wenv Wl) e)
          by (apply (rtbl_In Wl R RT r e HRT); apply LbB_DCtorK.inb_In'; vm_compute; reflexivity);
        unfold wenv in G; cbn [edenot] in G; unfold HLib.Eseed, reg_ev, Wx in G;
        lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
              Init.Nat.add Nat.sub nth app] in G
    end.

  Lemma xc_relro : forall m m' Wn, relro0 m -> munch Wn m m' -> Forall (fun iv : Z * Z => 0x186000 <= fst iv) Wn -> relro0 m'.
  Proof.
    intros m m' Wn HR MU FW a Ha. rewrite <- (HR a Ha). apply MU. rewrite unsigned_lit by lia.
    clear - FW Ha. induction FW as [|[l h] Wn' Hlh _ IH]; [exact I|]. cbn [fst] in Hlh. cbn [outside]. split; [lia | exact IH].
  Qed.

  Lemma xr_copy : forall R srcb junk, rfull R -> rtbl W R RTXH -> ftbl W spz m0 STX -> ftbl W ds m0 DTX -> mem_inv asegs m0 ->
    ACONST m0 ->
    pp < ep -> i < n -> ((n - i < ep - pp /\ k = n - i) \/ (ep - pp <= n - i /\ k = ep - pp)) ->
    bytes_at asegs m0 (p + i) srcb -> length srcb = Z.to_nat k ->
    rw_cells asegs m0 pp [CB (Z.to_nat k) junk] -> (p + i + k <= pp \/ pp + k <= p + i) ->
    accessible m0 (p + i) k -> accessible m0 pp k -> shvis m0 (p + i) (p + i + k) -> shvis m0 pp (pp + k) ->
    in_app_mem (p + i) (p + i + k) -> in_app_mem pp (pp + k) -> aconst_ok (pp, pp + k) ->
    AIMG_TOP <= pp -> pp + k <= lo -> (p + i + k <= spz - 64 - AINTRIN_STACK \/ spz <= p + i) ->
    (pp + k <= ds + 8 \/ ds + 72 <= pp) -> ((p + i + k <= ds + 8 \/ ds + 72 <= p + i)) ->
    AIMG_TOP <= sh (hull_lo (p + i)) -> AIMG_TOP <= sh (hull_lo pp) ->
    evt asegs (fun ms => exists R1 m1, rfull R1 /\ munch WC m0 m1 /\ wmono asegs m0 m1 /\ mem_inv asegs m1 /\ ACONST m1
                  /\ rw_cells asegs m1 pp [CB (Z.to_nat k) srcb] /\ ftbl W ds m1 DTXC
                  /\ ((i + k < n /\ ms = MS R1 F (Z_to_bv 64 AXLOOP) fc None m1 (seg_rom asegs) /\ rtbl W R1 RTXC
                       /\ ftbl W spz m1 STX)
                      \/ (n <= i + k /\ ms = MS R1 F (ret_pc ra) fc None m1 (seg_rom asegs) /\ rtbl W R1 RTXR)))
        (MS R F (Z_to_bv 64 AXLOOP) fc None m0 (seg_rom asegs)).
  Proof.
    intros R srcb junk RF HRT HST HDT MI AC HPE HIN CASE SB SL DJ SEP ACS ACD SVS SVD INS IND AOK PPI PPL SRCS DPP SRCD HLS HLD.
    pose proof (x_ranges sp ds lo DSO CEIL LO SPD) as (R1' & R2' & R3' & R4' & R5').
    pose proof VR as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    assert (K0 : 0 < k) by (destruct CASE as [(C1 & C2)|(C1 & C2)]; clear - C1 C2 HPE HIN; lia).
    eapply evt_cut; [exact (xr_a ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 ds p n i pp ep c k lo
                                 DSO DSW STK CEIL LO SPHI SPD RL VT0 VR R RF HRT HST HDT MI HPE HIN CASE)|].
    intros ms (R1 & m1 & E1 & RF1 & HRT1 & HST1 & HDT1 & HP1 & MI1). subst ms.
    destruct HP1 as [MU1 WM1].
    rgetw HRT1 (1%bv : reg) G1. rgetw HRT1 (2%bv : reg) G2. rgetw HRT1 (10%bv : reg) G10. rgetw HRT1 (11%bv : reg) G11.
    rgetw HRT1 (12%bv : reg) G12.
    rewrite LbB_PcOvf.w_add_g in G11. rewrite <- (Z_to_bv_bv_unsigned sp) in G2. rewrite LbB_PcOvf.w_add_g in G2.
    replace (spz + -64) with (spz - 64) in G2 by (clear; lia).
    assert (U2 : bv_unsigned (PropExec.getr R1 2) = spz - 64) by (rewrite G2; apply unsigned_lit; clear - R1' R2' R3'; lia).
    assert (WH1 : wins_hi [(spz - 64, spz); (ds + 56, ds + 72)]).
    { pose proof DSO as (O1 & O2 & O3). unfold wins_hi. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - right. clear - R2' R3'. unfold AHI_LO. lia.
      - destruct O2 as [O2|O2]; [left | right]; clear - O1 O2; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, DS_SIZE in *; lia. }
    assert (DJ1 : forall A n0, (A + n0 <= ds + 8 \/ ds + 72 <= A) -> A + n0 <= spz - 64 \/ spz <= A ->
                  disjoint_from [(spz - 64, spz); (ds + 56, ds + 72)] A n0).
    { intros A n0 K1 K2. cbn [disjoint_from]. clear - K1 K2. lia. }
    assert (ST1 : stk asegs m1 lo spz) by (eapply stk_wmono_hix; [exact STK | exact MU1 | exact WM1 | clear - CEIL R3'; unfold AIMG_TOP; lia]).
    assert (AC1 : ACONST m1).
    { eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 |]. pose proof DSO as (O1 & O2 & O3).
      repeat apply Forall_cons; try apply Forall_nil.
      - apply LbB_DPdK.aconst_ok_hi. clear - R2' R3'. lia.
      - destruct O2 as [O2|O2]; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP;
          clear - O1 O2; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, DS_SIZE in *; lia. }

    eapply evt_cut.
    { eapply (memmove_icpt_u H HH R1 F fc m1 pp (p + i) k (spz - 64 - AINTRIN_STACK) srcb junk RF1 G10 G11 G12);
        try (clear - W1 W2 W3 W4 W5 W8; lia).
      - eapply bytes_at_transport; [exact SB | exact MU1 |]. rewrite SL, Z2Nat.id by lia. apply DJ1; [exact SRCD|].
        clear - SRCS. unfold AINTRIN_STACK in *. lia.
      - exact SL.
      - eapply rw_cells_transport; [exact DJ | exact MU1 | exact WM1 |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
        apply DJ1; [exact DPP | clear - PPL LO; lia].
      - exact SEP.
      - eapply accessible_transport_hi; [exact ACS | exact MU1 | exact WH1].
      - eapply accessible_transport_hi; [exact ACD | exact MU1 | exact WH1].
      - exact (LbB_PcOvf.shvis_wmono_hi m0 m1 _ _ SVS WM1 HLS).
      - exact (LbB_PcOvf.shvis_wmono_hi m0 m1 _ _ SVD WM1 HLD).
      - rewrite U2. destruct (stk_split asegs m1 lo (spz - 64 - AINTRIN_STACK) spz ST1 ltac:(clear - LO; unfold AINTRIN_STACK; lia)) as [_ S2].
        exact (proj1 (stk_split asegs m1 (spz - 64 - AINTRIN_STACK) (spz - 64) spz S2 ltac:(clear - R2'; unfold AINTRIN_STACK; lia))).
      - clear - CEIL LO. unfold AINTRIN_STACK. lia.
      - rewrite U2. clear. lia.
      - exact MI1.
      - exact AC1.
      - exact INS.
      - exact IND.
      - exact AOK.
      - left. clear - PPL LO. unfold AINTRIN_STACK. lia.
      - rewrite U2. destruct SRCS as [SRCS|SRCS]; [left; exact SRCS | right; clear - SRCS; lia]. }
    intros ms (R2 & m2 & E2 & RF2 & KP & MU2 & WM2 & MI2 & AC2 & CB2 & ST2). subst ms.
    rewrite G1, ret_pc_even by (clear; first [reflexivity | lia]).
    rewrite U2 in MU2.
    assert (HRT2 : rtbl W R2 RTXM).
    { eapply (rtbl_keep W R1 R2 RTXM (10%bv :: KEPT)); [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity | vm_compute; reflexivity | exact KP]. }
    assert (DJ2 : forall A n0, (A + n0 <= pp \/ pp + k <= A) -> (A + n0 <= spz - 64 - AINTRIN_STACK \/ spz - 64 <= A) ->
                  disjoint_from [(pp, pp + k); (spz - 64 - AINTRIN_STACK, spz - 64)] A n0).
    { intros A n0 K1 K2. cbn [disjoint_from]. clear - K1 K2. lia. }
    assert (HST2 : ftbl W spz m2 STX).
    { eapply (ftbl_munch W spz m1 m2 STX _ (-64) 0); [exact HST1 | exact MU2 | exact WM2 | vm_compute; reflexivity |].
      apply DJ2; [right; clear - PPL LO; lia | right; clear; lia]. }
    assert (HDT2 : ftbl W ds m2 DTX).
    { eapply (ftbl_munch W ds m1 m2 DTX _ 8 72); [exact HDT1 | exact MU2 | exact WM2 | vm_compute; reflexivity |].
      apply DJ2; [destruct DPP as [Dp|Dp]; [right | left]; clear - Dp; lia | left; clear - R4' R5' LO SPD; unfold DS_SIZE, AINTRIN_STACK in *; lia]. }
    assert (MU02 : munch WC m0 m2).
    { eapply munch_trans; (eapply munch_weaken; [| eassumption]); apply sub_fp_of; unfold WC;
        repeat apply Forall_cons; try apply Forall_nil.
      all: first [ sfp_in (spz - 8192, spz) | sfp_in (ds + 56, ds + 72) | sfp_in (pp, pp + k)
                 | (exists (spz - 8192, spz); split; [left; reflexivity | cbn [fst snd]; clear - R2'; unfold AINTRIN_STACK; lia]) ]. }
    assert (WM02 : wmono asegs m0 m2) by (eapply wmono_trans; eassumption).
    assert (DSW2 : wr_at asegs m2 ds DS_SIZE) by (eapply wr_at_transport; [exact DSW | exact WM02]).
    assert (STK2 : stk asegs m2 lo spz) by (eapply stk_wmono_hix; [exact STK | exact MU02 | exact WM02 | clear - CEIL R3'; unfold AIMG_TOP; lia]).
    assert (RL2 : relro0 m2).
    { eapply xc_relro; [exact RL | exact MU02 |]. unfold WC. pose proof DSO as (O1 & _).
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; clear - O1 R2' R3' PPI; unfold AIMG_TOP in *; lia. }
    assert (WC2 : wins_hi [(spz - 64, spz); (ds + 56, ds + 72)]) by exact WH1.
    assert (VT2 : rw_cells asegs m2 (ds + 8) [C8 (Z_to_bv 64 VT_SB_A)]).
    { eapply rw_cells_transport; [exact VT0 | exact MU02 | exact WM02 |]. unfold WC. cbn [cells_size csize disjoint_from fst snd].
      clear - R2' R4' R5' LO DPP. unfold DS_SIZE in *. lia. }
    destruct (Z_lt_le_dec (i + k) n) as [Hc|Hx].
    - eapply evt_cut; [exact (xr_a2c ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 ds p n i pp ep c k lo
                                   DSO DSW2 STK2 CEIL LO SPHI SPD RL2 VT2 VR R2 RF2 HRT2 HST2 HDT2 MI2 Hc)|].
      intros ms (R3 & m3 & E3 & RF3 & HRT3 & HST3 & HDT3 & (MU3 & WM3) & MI3). subst ms.
      apply evt_done. exists R3, m3. split; [exact RF3|].
      split.
      { eapply munch_trans; [exact MU02|]. eapply munch_weaken; [| exact MU3]. apply sub_fp_of. unfold WC.
        repeat apply Forall_cons; try apply Forall_nil; [sfp_in (spz - 8192, spz) | sfp_in (ds + 56, ds + 72)]. }
      split; [eapply wmono_trans; eassumption|]. split; [exact MI3|].
      split.
      { eapply ACONST_frame; [exact AC2 | exact MU3 | exact WM3 |]. pose proof DSO as (O1 & O2 & O3).
        repeat apply Forall_cons; try apply Forall_nil.
        - apply LbB_DPdK.aconst_ok_hi. clear - R2' R3'. lia.
        - destruct O2 as [O2|O2]; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP;
            clear - O1 O2; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, DS_SIZE in *; lia. }
      split.
      { eapply rw_cells_transport; [exact CB2 | exact MU3 | exact WM3 |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
        apply DJ1; [exact DPP | clear - PPL LO; lia]. }
      split; [exact HDT3|]. left. split; [exact Hc|]. split; [reflexivity|]. split; [exact HRT3 | exact HST3].
    - eapply evt_cut; [exact (xr_a2x ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 ds p n i pp ep c k lo
                                   DSO DSW2 STK2 CEIL LO SPHI SPD RL2 VT2 VR R2 RF2 HRT2 HST2 HDT2 MI2 Hx)|].
      intros ms (R3 & m3 & E3 & RF3 & HRT3 & HDT3 & (MU3 & WM3) & MI3). subst ms.
      rgetw HRT3 (1%bv : reg) K1.
      rewrite (rfull_eq R3 RF3). apply xs_ret_ok. rewrite <- (rfull_eq R3 RF3). rewrite K1.
      exists R3, m3. split; [exact RF3|].
      split.
      { eapply munch_trans; [exact MU02|]. eapply munch_weaken; [| exact MU3]. apply sub_fp_of. unfold WC.
        repeat apply Forall_cons; try apply Forall_nil; [sfp_in (spz - 8192, spz) | sfp_in (ds + 56, ds + 72)]. }
      split; [eapply wmono_trans; eassumption|]. split; [exact MI3|].
      split.
      { eapply ACONST_frame; [exact AC2 | exact MU3 | exact WM3 |]. pose proof DSO as (O1 & O2 & O3).
        repeat apply Forall_cons; try apply Forall_nil.
        - apply LbB_DPdK.aconst_ok_hi. clear - R2' R3'. lia.
        - destruct O2 as [O2|O2]; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP;
            clear - O1 O2; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, DS_SIZE in *; lia. }
      split.
      { eapply rw_cells_transport; [exact CB2 | exact MU3 | exact WM3 |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
        apply DJ1; [exact DPP | clear - PPL LO; lia]. }
      split; [exact HDT3|]. right. split; [exact Hx|]. split; [reflexivity | exact HRT3].
  Qed.

  Lemma xr_after_ovf : forall R, rfull R -> rtbl W R RTXP -> ftbl W spz m0 STX -> ftbl W ds m0 DTX -> mem_inv asegs m0 -> ACONST m0 ->
    evt asegs (fun ms => exists R1 m1, rfull R1 /\ munch [(spz - 64, spz); (ds + 56, ds + 72)] m0 m1 /\ wmono asegs m0 m1
                  /\ mem_inv asegs m1 /\ ACONST m1 /\ ftbl W ds m1 DTX
                  /\ ((i + 1 < n /\ ms = MS R1 F (Z_to_bv 64 AXLOOP) fc None m1 (seg_rom asegs) /\ rtbl W R1 RTXB
                       /\ ftbl W spz m1 STX)
                      \/ (n <= i + 1 /\ ms = MS R1 F (ret_pc ra) fc None m1 (seg_rom asegs) /\ rtbl W R1 RTXR1)))
        (MS R F (Z_to_bv 64 AXORA) fc None m0 (seg_rom asegs)).
  Proof.
    intros R RF HRT HST HDT MI AC.
    pose proof (x_ranges sp ds lo DSO CEIL LO SPD) as (R1' & R2' & R3' & R4' & R5').
    assert (ACk : forall m1, munch [(spz - 64, spz); (ds + 56, ds + 72)] m0 m1 -> wmono asegs m0 m1 -> ACONST m1).
    { intros m1 MU WM. eapply ACONST_frame; [exact AC | exact MU | exact WM |]. pose proof DSO as (O1 & O2 & O3).
      repeat apply Forall_cons; try apply Forall_nil.
      - apply LbB_DPdK.aconst_ok_hi. clear - R2' R3'. lia.
      - destruct O2 as [O2|O2]; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP;
          clear - O1 O2; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, DS_SIZE in *; lia. }
    destruct (Z_lt_le_dec (i + 1) n) as [Hc|Hx].
    - eapply evt_cut; [exact (xr_b2c ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 ds p n i pp ep c k lo
                                   DSO DSW STK CEIL LO SPHI SPD RL VT0 VR R RF HRT HST HDT MI Hc)|].
      intros ms (R3 & m3 & E3 & RF3 & HRT3 & HST3 & HDT3 & (MU3 & WM3) & MI3). subst ms.
      apply evt_done. exists R3, m3. split; [exact RF3|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|].
      split; [exact (ACk m3 MU3 WM3)|]. split; [exact HDT3|]. left. split; [exact Hc|]. split; [reflexivity|]. split; [exact HRT3 | exact HST3].
    - eapply evt_cut; [exact (xr_b2x ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 ds p n i pp ep c k lo
                                   DSO DSW STK CEIL LO SPHI SPD RL VT0 VR R RF HRT HST HDT MI Hx)|].
      intros ms (R3 & m3 & E3 & RF3 & HRT3 & HDT3 & (MU3 & WM3) & MI3). subst ms.
      rgetw HRT3 (1%bv : reg) K1.
      rewrite (rfull_eq R3 RF3). apply xs_ret_ok. rewrite <- (rfull_eq R3 RF3). rewrite K1.
      exists R3, m3. split; [exact RF3|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|].
      split; [exact (ACk m3 MU3 WM3)|]. split; [exact HDT3|]. right. split; [exact Hx|]. split; [reflexivity | exact HRT3].
  Qed.
End XC.
