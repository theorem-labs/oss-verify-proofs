(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Ox Require F03.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 RtB_Iface RtB_IMemset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtorR1 LbB_DPdK.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition RET_MALLOC : Z := 977904.
Definition CALL_MEMSET : Z := 978152.
Definition RET_MEMSET : Z := 978156.
Definition CALL_CTOR : Z := 978268.
Definition RET_CTOR : Z := 978272.
Definition RETPC : Z := 978668.

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 33) (ELit k).

Definition RT2 : list (reg * expr) :=
  [(1%bv, ELit RET_MALLOC); (2%bv, spx (-112)); (3%bv, EVar 50); (4%bv, EVar 51); (8%bv, EVar 33); (9%bv, spx (-112));
   (10%bv, EVar 52); (18%bv, EVar 40); (19%bv, EVar 37); (20%bv, EVar 32); (21%bv, EVar 54); (22%bv, EVar 44);
   (23%bv, ELit SHBASE); (24%bv, EVar 46); (25%bv, EVar 47); (26%bv, EVar 48); (27%bv, EVar 49)].
Definition SF2 : list fent :=
  [(-96, 8%nat, ELit 0); (-8, 8%nat, EVar 34); (-16, 8%nat, EVar 38); (-24, 8%nat, EVar 39); (-32, 8%nat, EVar 40);
   (-40, 8%nat, EVar 41); (-48, 8%nat, EVar 42); (-56, 8%nat, EVar 43); (-64, 8%nat, EVar 44); (-72, 8%nat, EVar 45);
   (-80, 8%nat, EVar 46); (-88, 8%nat, EVar 47)].
Definition FT2 : list fent := [(248, 8%nat, EVar 53)].

Lemma pd_ret_ok : forall (Q : machine_state -> Prop) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (ret_pc x1) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 RETPC) fc None m (seg_rom asegs)).
Proof.
  intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HQ.
  step. apply evt_done. exact HQ.
Qed.

Section Pd0B.

  Local Notation PD_SHB := LbB_DPdK.PD_SHB (only parsing).
  Local Notation kst_pd := LbB_DPdK.kst_pd (only parsing).
  Local Notation outside_of := LbB_DPdK.outside_of (only parsing).
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m1 : mem) (ds pcons icount err lo ff fp p : Z) (LF : list fframe).

  Hypothesis DSA : addressable m1 ds DS_SIZE.
  Hypothesis DSW : wr_at asegs m1 ds DS_SIZE.
  Hypothesis DSO : app_obj ds DS_SIZE.
  Hypothesis DS8 : ds mod 8 = 0.
  Hypothesis DSV : shvis m1 ds (ds + DS_SIZE).
  Hypothesis DSH : ds + DS_SIZE + 64 <= AAPP_HI.
  Hypothesis DSM : ds + DS_SIZE <= aceil.
  Hypothesis DSin : obj_inframe LF ds DS_SIZE.

  Hypothesis PCA : addressable m1 pcons 48.
  Hypothesis PCO : app_obj pcons 48.
  Hypothesis PC8 : pcons mod 8 = 0.
  Hypothesis PCC : rw_cells asegs m1 (pcons + 32) [C8 (Z_to_bv 64 0)].
  Hypothesis DISJ : forall a, ds <= a < ds + DS_SIZE -> ~ (pcons <= a < pcons + 48).
  Hypothesis ERR : - 2 ^ 31 <= err < 0.
  Hypothesis ICN : 0 <= icount < 2 ^ 63.

  Hypothesis STK : stk asegs m1 lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - ADS_STACK.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPHI : bv_unsigned sp <= AAPP_HI.
  Hypothesis SPOBJ : forall O n, O = ds /\ n = DS_SIZE \/ O = pcons /\ n = 48 ->
                     O + n <= bv_unsigned sp - ADS_STACK \/ bv_unsigned sp <= O.

  Hypothesis FFR : aframe_range H 2 ff fp.
  Hypothesis FSB_OK : afsb_ok H.
  Hypothesis FFDS : ff + 256 <= ds \/ ds + DS_SIZE <= ff.
  Hypothesis FFPC : ff + 256 <= pcons \/ pcons + 48 <= ff.
  Hypothesis FPPC : fp + 1 <= pcons \/ pcons + 48 <= fp.
  Hypothesis FPDS : fp + 1 <= ds \/ ds + DS_SIZE <= fp.
  Hypothesis HULL : hull_hi (ds + DS_SIZE) <= ff \/ ff + 256 <= hull_lo ds.
  Hypothesis FRW : wr_at asegs m1 ff 256.
  Hypothesis FSV : shvis m1 ff (ff + 256).
  Hypothesis FSW : wr_at asegs m1 (sh ff) 32.
  Hypothesis FLW : wr_at asegs m1 fp 1.

  Hypothesis MI1 : mem_inv asegs m1.
  Hypothesis AC1 : ACONST m1.
  Hypothesis LV1 : LINV_P5 m1.
  Hypothesis PPA8 : addressable m1 (p + 8) 8.
  Hypothesis PPA80 : addressable m1 (p + 80) 8.
  Hypothesis PPC8 : ro_cells asegs m1 (p + 8) [C8 (Z_to_bv 64 pcons)].
  Hypothesis PPC80 : ro_cells asegs m1 (p + 80) [C8 (Z_to_bv 64 icount)].
  Hypothesis PPO8 : app_obj (p + 8) 8.
  Hypothesis PPO80 : app_obj (p + 80) 8.
  Hypothesis PP8 : p mod 8 = 0.
  Hypothesis P16 : pcons mod 16 = 0.
  Hypothesis PPS : forall O, O = p + 8 \/ O = p + 80 -> O + 8 <= bv_unsigned sp - ADS_STACK \/ bv_unsigned sp <= O.
  Hypothesis PPF : forall O, O = p + 8 \/ O = p + 80 -> ff + 256 <= O \/ O + 8 <= ff.
  Hypothesis PPL : forall O, O = p + 8 \/ O = p + 80 -> fp + 1 <= O \/ O + 8 <= fp.
  Hypothesis PPH : forall O, O = p + 8 \/ O = p + 80 -> sh ff + 32 <= O \/ O + 8 <= sh ff.

  Local Notation aconst_ok_lo := (@LbB_DPdK.aconst_ok_lo lo) (only parsing).
  Local Notation aconst_ok_hi := (@LbB_DPdK.aconst_ok_hi lo) (only parsing).
  Local Notation Wp := (@LbB_DPdK.Wp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw ds pcons icount ff fp p) (only parsing).
  Local Notation PW := (@LbB_DPdK.PW sp ds ff fp) (only parsing).
  Local Notation Pw := (@LbB_DPdK.Pw sp m1 ds ff fp) (only parsing).
  Local Notation Pw_m1 := (@LbB_DPdK.Pw_m1 sp m1 ds ff fp) (only parsing).
  Local Notation pd_ranges := (@LbB_DPdK.pd_ranges HCEIL H sp m1 ds pcons icount lo ff fp ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation sh_mono8 := (@LbB_DPdK.sh_mono8 sp ds pcons icount ICN) (only parsing).
  Local Notation pw_aconst := (@LbB_DPdK.pw_aconst HCEIL H sp m1 ds pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation pw_out_img := (@LbB_DPdK.pw_out_img HCEIL H sp m1 ds pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation pw_sh_apart := (@LbB_DPdK.pw_sh_apart HCEIL H sp m1 ds pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation pw_hull_apart := (@LbB_DPdK.pw_hull_apart HCEIL H sp m1 ds pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation pd_keep := (@LbB_DPdK.pd_keep HCEIL H sp m1 ds pcons icount lo ff fp DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation evWp := (@LbB_DPdK.evWp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw ds pcons icount ff fp p ICN) (only parsing).
  Local Notation pd_vals := (@LbB_DPdK.pd_vals HCEIL H sp m1 ds pcons icount lo ff fp DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation kst_pd_ok := (@LbB_DPdK.kst_pd_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 ds pcons icount lo ff fp p DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation tS := (@LbB_DPdK.tS sp) (only parsing).
  Local Notation tF := (@LbB_DPdK.tF ff) (only parsing).
  Local Notation tH := (@LbB_DPdK.tH ff) (only parsing).
  Local Notation tL := (@LbB_DPdK.tL fp) (only parsing).
  Local Notation pd_wins := (@LbB_DPdK.pd_wins HCEIL H sp m1 ds pcons icount lo ff fp ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tab_vals := (@LbB_DPdK.tab_vals HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 ds pcons icount lo ff fp p DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tabs_wf3 := (@LbB_DPdK.tabs_wf3 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 ds pcons icount lo ff fp p DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tabs_wf4 := (@LbB_DPdK.tabs_wf4 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 ds pcons icount lo ff fp p DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation wk_stk := (@LbB_DPdK.wk_stk sp ds pcons icount lo ICN LO) (only parsing).
  Local Notation wk_win := (@LbB_DPdK.wk_win sp ds pcons icount ICN) (only parsing).
  Local Notation inPW := (@LbB_DPdK.inPW sp ds ff fp) (only parsing).
  Local Notation Pw_ext := (@LbB_DPdK.Pw_ext sp m1 ds ff fp) (only parsing).
  Local Notation in_stk := (@LbB_DPdK.in_stk sp ds pcons icount ff fp ICN) (only parsing).
  Local Notation in_ds := (@LbB_DPdK.in_ds sp ds pcons icount ff fp ICN) (only parsing).
  Local Notation in_fr := (@LbB_DPdK.in_fr sp ds pcons icount ff fp ICN) (only parsing).
  Local Notation in_sh := (@LbB_DPdK.in_sh sp ds pcons icount ff fp ICN) (only parsing).
  Local Notation in_fl := (@LbB_DPdK.in_fl sp ds pcons icount ff fp ICN) (only parsing).
  Local Notation shb_eq := (@LbB_DPdK.shb_eq sp ds pcons icount ff ICN) (only parsing).
  Local Notation Pw_step3 := (@LbB_DPdK.Pw_step3 sp m1 ds pcons icount ff fp ICN) (only parsing).
  Local Notation Pw_step4 := (@LbB_DPdK.Pw_step4 sp m1 ds pcons icount ff fp ICN) (only parsing).
  Local Notation HHb := (@LbB_DPdK.HHb HCEIL H HHbp) (only parsing).
  Local Notation afs_ok_frame := (@LbB_DPdK.afs_ok_frame H sp ds pcons icount ff fp LF ICN) (only parsing).
  Local Notation afs_ok_stack := (@LbB_DPdK.afs_ok_stack HCEIL H sp m1 ds pcons icount lo ff fp LF ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation afs_ok_shadow := (@LbB_DPdK.afs_ok_shadow HCEIL H sp m1 ds pcons icount lo ff fp LF ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation pd_memset := (@LbB_DPdK.pd_memset HCEIL H HHbp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw F fc m1 ds pcons icount err lo ff fp p LF DSA DSW DSO DS8 DSV DSH DSM DSin PCA PCO PC8 PCC DISJ ERR ICN STK CEIL LO SP16 SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW MI1 AC1 LV1) (only parsing).
  Local Notation fr_app := (@LbB_DPdK.fr_app HCEIL H sp m1 ds pcons icount lo ff fp ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation fr_addr := (@LbB_DPdK.fr_addr HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 ds pcons icount lo ff fp p DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation fr_str := (@LbB_DPdK.fr_str HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 ds pcons icount lo ff fp p ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation pd_s28 := (@LbB_DPdK.pd_s28 H sp ds pcons icount ff fp ICN FFR) (only parsing).
  Local Notation pd_ctor := (@LbB_DPdK.pd_ctor HCEIL H HHbp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw F fc m1 ds pcons icount err lo ff fp p LF DSA DSW DSO DS8 DSV DSH DSM DSin PCA PCO PC8 PCC DISJ ERR ICN STK CEIL LO SP16 SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW MI1 AC1 LV1) (only parsing).
  Local Notation pd_P := (@LbB_DPdK.pd_P H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 ds err ff fp LF) (only parsing).
  Local Notation w4_ds := (@LbB_DPdK.w4_ds HCEIL H sp m1 ds pcons icount lo ff fp DSO DS8 DSM ICN STK CEIL LO SPHI FFR FSB_OK FFDS FPDS) (only parsing).
  Local Notation pd_post := (@LbB_DPdK.pd_post HCEIL H HHbp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw F fc m1 ds pcons icount err lo ff fp p LF DSO DS8 DSM ICN STK CEIL LO SPHI FFR FSB_OK FFDS FPDS) (only parsing).
  Local Notation tabs_ok3 := (@LbB_DPdK.tabs_ok3 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 ds pcons icount lo ff fp p DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation tabs_ok4 := (@LbB_DPdK.tabs_ok4 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 ds pcons icount lo ff fp p DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation RFS_step3 := (@LbB_DPdK.RFS_step3 HCEIL H HHbp sp m1 ds pcons icount lo ff fp LF ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).

  Notation spz := (bv_unsigned sp) (only parsing).

  Ltac evwp := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wp;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Ltac tnormp H :=
    lazymatch type of H with
    | ftbl ?W ?B ?m ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    | rtbl ?W ?R ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    end.

  Ltac dkrunP3 HRT HSF HFT HHT HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tF FT []; tH HT []]) in
        let kf := eval vm_compute in (kfix stops pc (HLib.srs sr_id RT) (kst_pd ++ fknT L0)) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] ((kst_pd ++ kf) ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          eapply (dk_runN Wp [tS SF ks1; tF FT ks2; tH HT ks3]
                    (tabs_wf3 SF FT HT ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step3 SF FT HT ks1 ks2 ks3)
                    Q R F pc fc m ro RT [] (kst_pd ++ kf) fuel stops (SCR [] [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok3; [exact HP | exact HMI | exact HSF | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HP | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply kst_pd_ok; [exact HP | exact HMI] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end
    end.

  Ltac dkrunP4 HRT HSF HFT HHT HLT HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HLT with ftbl _ _ _ ?LT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tF FT []; tH HT []; tL LT []]) in
        let kf := eval vm_compute in (kfix stops pc (HLib.srs sr_id RT) (kst_pd ++ fknT L0)) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] ((kst_pd ++ kf) ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          let ks4 := eval vm_compute in (nkeys (EVar 53) (s_log SSr) LT) in
          eapply (dk_runN Wp [tS SF ks1; tF FT ks2; tH HT ks3; tL LT ks4]
                    (tabs_wf4 SF FT HT LT ks1 ks2 ks3 ks4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step4 SF FT HT LT ks1 ks2 ks3 ks4)
                    Q R F pc fc m ro RT [] (kst_pd ++ kf) fuel stops (SCR [] [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok4; [exact HP | exact HMI | exact HSF | exact HFT | exact HHT | exact HLT | vm_compute; reflexivity .. ]
          | exact HP | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply kst_pd_ok; [exact HP | exact HMI] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end
    end.

  Ltac tcomp HTS :=
    lazymatch type of HTS with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS; clear E
    end.
  Ltac tsplit HTS H1 H2 H3 :=
    tcomp HTS;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS];
    apply Forall_cons_iff in HTS as [H3 HTS]; clear HTS; cbn [fst snd] in H1, H2, H3.
  Ltac tsplit4 HTS H1 H2 H3 H4 :=
    tcomp HTS;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS];
    apply Forall_cons_iff in HTS as [H3 HTS]; apply Forall_cons_iff in HTS as [H4 HTS]; clear HTS; cbn [fst snd] in H1, H2, H3, H4.

  Ltac rgetp HRT r H :=
    lazymatch type of HRT with
    | rtbl ?W ?R ?RT =>
        let e := eval vm_compute in (match List.find (fun re => bv_eqb (fst re) r) RT with Some re => snd re | None => ELit 0 end) in
        assert (H : PropExec.getr R r = edenot (wenv W) e)
          by (apply (rtbl_In W R RT r e HRT); apply LbB_DCtorK.inb_In'; vm_compute; reflexivity);
        unfold wenv in H; cbn [edenot] in H; unfold HLib.Eseed, reg_ev, Wp in H;
        lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
              Init.Nat.add Nat.sub nth app] in H;
        rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z in H by (pose proof pd_vals; lia)
    end.

  Definition RTm : list (reg * expr) :=
    [(1%bv, ELit RET_MEMSET); (2%bv, EAlu ALU_ADD (EVar 33) (ELit (-112))); (3%bv, EVar 50); (4%bv, EVar 51);
     (8%bv, EVar 33); (9%bv, EAlu ALU_ADD (EVar 33) (ELit (-112))); (10%bv, EAlu ALU_ADD (EVar 52) (ELit 32));
     (18%bv, EVar 52); (19%bv, EVar 37); (20%bv, EVar 32); (21%bv, EVar 54);
     (22%bv, EAlu ALU_ADD (EVar 52) (ELit 32)); (23%bv, ELit SHBASE);
     (24%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit SHBASE)); (25%bv, EVar 52); (26%bv, EVar 48);
     (27%bv, EVar 49)].
  Definition SFm : list fent :=
    [(-96, 8%nat, ELit 0); (-8, 8%nat, EVar 34); (-16, 8%nat, EVar 38); (-24, 8%nat, EVar 39);
     (-32, 8%nat, EVar 40); (-40, 8%nat, EVar 41); (-48, 8%nat, EVar 42); (-56, 8%nat, EVar 43);
     (-64, 8%nat, EVar 44); (-72, 8%nat, EVar 45); (-80, 8%nat, EVar 46); (-88, 8%nat, EVar 47);
     (-112, 8%nat, EVar 52)].
  Definition FTm : list fent :=
    [(248, 8%nat, EVar 53); (0, 8%nat, ELit 1102416563); (8, 8%nat, ELit 123192); (16, 8%nat, ELit 977792);
     (32, 8%nat, ELit 0); (40, 8%nat, ELit 0)].
  Definition HTm : list fent :=
    [(SHBASE + 0, 1%nat, ELit 18446744073709551601); (SHBASE + 1, 1%nat, ELit 18446744073709551601);
     (SHBASE + 2, 1%nat, ELit 18446744073709551601); (SHBASE + 3, 1%nat, ELit 18446744073709551601);
     (SHBASE + 4, 1%nat, ELit 0); (SHBASE + 5, 1%nat, ELit 0); (SHBASE + 6, 1%nat, ELit 0);
     (SHBASE + 7, 1%nat, ELit 18446744073709551602); (SHBASE + 12, 1%nat, ELit 18446744073709551608);
     (SHBASE + 13, 1%nat, ELit 18446744073709551608); (SHBASE + 14, 1%nat, ELit 18446744073709551608);
     (SHBASE + 15, 1%nat, ELit 18446744073709551602); (SHBASE + 8, 1%nat, ELit 18446744073709551602);
     (SHBASE + 9, 1%nat, ELit 18446744073709551602); (SHBASE + 10, 1%nat, ELit 18446744073709551602);
     (SHBASE + 11, 1%nat, ELit 18446744073709551602); (SHBASE + 20, 1%nat, ELit 0); (SHBASE + 21, 1%nat, ELit 0);
     (SHBASE + 22, 1%nat, ELit 0); (SHBASE + 23, 1%nat, ELit 18446744073709551603);
     (SHBASE + 16, 1%nat, ELit 18446744073709551602); (SHBASE + 17, 1%nat, ELit 18446744073709551602);
     (SHBASE + 18, 1%nat, ELit 18446744073709551602); (SHBASE + 19, 1%nat, ELit 18446744073709551602);
     (SHBASE + 24, 1%nat, ELit 18446744073709551603); (SHBASE + 25, 1%nat, ELit 18446744073709551603);
     (SHBASE + 26, 1%nat, ELit 18446744073709551603); (SHBASE + 27, 1%nat, ELit 18446744073709551603)].
  Definition RTc : list (reg * expr) :=
    [(1%bv, ELit RET_CTOR); (2%bv, EAlu ALU_ADD (EVar 33) (ELit (-112))); (3%bv, EVar 50); (4%bv, EVar 51);
     (8%bv, EVar 33); (9%bv, EAlu ALU_ADD (EVar 33) (ELit (-112))); (18%bv, EVar 52); (19%bv, EVar 37);
     (20%bv, EVar 32); (21%bv, EAlu ALU_ADD (EVar 52) (ELit 96)); (22%bv, EAlu ALU_ADD (EVar 52) (ELit 32));
     (23%bv, EAlu ALU_ADD (EVar 52) (ELit 160));
     (24%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit SHBASE)); (25%bv, EVar 52); (26%bv, EVar 48);
     (27%bv, EVar 49)].
  Definition SFc : list fent :=
    [(-96, 8%nat, ELit 0); (-8, 8%nat, EVar 34); (-16, 8%nat, EVar 38); (-24, 8%nat, EVar 39);
     (-32, 8%nat, EVar 40); (-40, 8%nat, EVar 41); (-48, 8%nat, EVar 42); (-56, 8%nat, EVar 43);
     (-64, 8%nat, EVar 44); (-72, 8%nat, EVar 45); (-80, 8%nat, EVar 46); (-88, 8%nat, EVar 47);
     (-112, 8%nat, EVar 52)].
  Definition FTc : list fent :=
    [(248, 8%nat, EVar 53); (0, 8%nat, ELit 1102416563); (8, 8%nat, ELit 123192); (16, 8%nat, ELit 977792);
     (32, 8%nat, ELit 0); (40, 8%nat, ELit 0); (48, 8%nat, EVar 36); (96, 1%nat, ELit 0); (97, 1%nat, ELit 0);
     (160, 1%nat, ELit 0); (161, 1%nat, ELit 0)].
  Definition HTc : list fent :=
    [(SHBASE + 0, 1%nat, ELit 18446744073709551601); (SHBASE + 1, 1%nat, ELit 18446744073709551601);
     (SHBASE + 2, 1%nat, ELit 18446744073709551601); (SHBASE + 3, 1%nat, ELit 18446744073709551601);
     (SHBASE + 4, 1%nat, ELit 0); (SHBASE + 5, 1%nat, ELit 0); (SHBASE + 6, 1%nat, ELit 0);
     (SHBASE + 7, 1%nat, ELit 18446744073709551602); (SHBASE + 12, 1%nat, ELit 0); (SHBASE + 13, 1%nat, ELit 0);
     (SHBASE + 14, 1%nat, ELit 0); (SHBASE + 15, 1%nat, ELit 18446744073709551602);
     (SHBASE + 8, 1%nat, ELit 18446744073709551602); (SHBASE + 9, 1%nat, ELit 18446744073709551602);
     (SHBASE + 10, 1%nat, ELit 18446744073709551602); (SHBASE + 11, 1%nat, ELit 18446744073709551602);
     (SHBASE + 20, 1%nat, ELit 0); (SHBASE + 21, 1%nat, ELit 0); (SHBASE + 22, 1%nat, ELit 0);
     (SHBASE + 23, 1%nat, ELit 18446744073709551603); (SHBASE + 16, 1%nat, ELit 18446744073709551602);
     (SHBASE + 17, 1%nat, ELit 18446744073709551602); (SHBASE + 18, 1%nat, ELit 18446744073709551602);
     (SHBASE + 19, 1%nat, ELit 18446744073709551602); (SHBASE + 24, 1%nat, ELit 18446744073709551603);
     (SHBASE + 25, 1%nat, ELit 18446744073709551603); (SHBASE + 26, 1%nat, ELit 18446744073709551603);
     (SHBASE + 27, 1%nat, ELit 18446744073709551603)].

  Lemma pd_c3 : forall R m, rfull R -> rtbl Wp R RTc -> ftbl Wp spz m SFc -> ftbl Wp ff m FTc -> ftbl Wp (ff / 8) m HTc ->
    Pw m -> mem_inv asegs m -> as_RFS H ((2, ff, fp) :: LF) m -> (forall LB, ds_repA0 LB m ds err 0 []) ->
    evt asegs pd_P (MS R F (Z_to_bv 64 RET_CTOR) fc None m (seg_rom asegs)).
  Proof using All.
    intros R m RF HRT HSF HFT HHT HP HMI HRFS HDS.
    assert (HLT : ftbl Wp fp m []) by apply Forall_nil.
    dkrunP4 HRT HSF HFT HHT HLT HP HMI 600%nat [RETPC].
    - apply Forall_nil.
    - apply Forall_nil.
    - intros R1 m1' RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
      tsplit4 HTS1 HSF1 HFT1 HHT1 HLT1.
      cbn [s_pc].
      rgetp HRT1 (1%bv : bv 5) G1. rgetp HRT1 (2%bv : bv 5) G2. rgetp HRT1 (3%bv : bv 5) G3. rgetp HRT1 (4%bv : bv 5) G4.
      rgetp HRT1 (8%bv : bv 5) G8. rgetp HRT1 (9%bv : bv 5) G9. rgetp HRT1 (18%bv : bv 5) G18. rgetp HRT1 (19%bv : bv 5) G19.
      rgetp HRT1 (20%bv : bv 5) G20. rgetp HRT1 (21%bv : bv 5) G21. rgetp HRT1 (22%bv : bv 5) G22.
      rgetp HRT1 (23%bv : bv 5) G23. rgetp HRT1 (24%bv : bv 5) G24. rgetp HRT1 (25%bv : bv 5) G25.
      rgetp HRT1 (26%bv : bv 5) G26. rgetp HRT1 (27%bv : bv 5) G27.
      rewrite (MS_full_eq R1 F _ fc m1' _ RF1).
      apply pd_ret_ok.
      rewrite <- (MS_full_eq R1 F (ret_pc (PropExec.getr R1 1)) fc m1' (seg_rom asegs) RF1).
      eapply pd_post;
        [ exact RF1 | exact G1 | exact G2 | exact G3 | exact G4 | exact G8 | exact G9 | exact G18 | exact G19
        | exact G20 | exact G21 | exact G22 | exact G23 | exact G24 | exact G25 | exact G26 | exact G27
        | exact HP1 | exact HMI1 | exact HLT1 | vm_compute; reflexivity | exact HRFS | exact MU1 | exact WM1 | exact HDS ].
  Qed.

  Ltac dkrunP3k HRT HSF HFT HHT HP HMI fuel stops kx :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tF FT []; tH HT []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] ((kst_pd ++ kx) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          eapply (dk_runN Wp [tS SF ks1; tF FT ks2; tH HT ks3]
                    (tabs_wf3 SF FT HT ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step3 SF FT HT ks1 ks2 ks3)
                    Q R F pc fc m ro RT [] (kst_pd ++ kx) fuel stops (SCR [] [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok3; [exact HP | exact HMI | exact HSF | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HP | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply kst_pd_ok; [exact HP | exact HMI] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end
    end.

  Definition pS (k : Z) : saddr := SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 54) (ELit k)) (ELit 3)) SHBASE.

  Definition kp : list kentry :=
    [KWord (SA (EVar 54) 8) 8 (EVar 35); KWord (SA (EVar 54) 80) 8 (EVar 36);
     KRange (EVar 54) (AIMG_TOP - 8) (AAPP_HI - 88); KRange (EVar 35) AIMG_TOP (AAPP_HI - 48);
     KAlign (EVar 35) 16; KAlign (EVar 54) 8;
     KWord (pS 8) 1 (ELit 0); KWord (pS 80) 1 (ELit 0);
     KDisj (pS 8) (ELit 1) (SA PD_SHB SHBASE) (ELit 32); KDisj (pS 80) (ELit 1) (SA PD_SHB SHBASE) (ELit 32)].

  Lemma cell8_of_ro : forall m a z, ro_cells asegs m a [C8 (Z_to_bv 64 z)] -> 0 <= z < 2 ^ 64 -> HRep.cellw asegs m a 8 z.
  Proof.
    intros m a z Hc Hz. split; [change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hz|].
    pose proof (ro_cells_read asegs m a _ 0%nat _ Hc eq_refl) as RD. replace (a + Z.of_nat 0) with a in RD by lia.
    rewrite <- rdn_of_ov. exact RD.
  Qed.

  Lemma pd_p_rng : AIMG_TOP <= p + 8 /\ p + 88 <= AAPP_HI /\ AIMG_TOP <= pcons /\ pcons + 48 <= AAPP_HI.
  Proof.
    destruct PPO8 as (O1 & _ & _). destruct PPO80 as (_ & _ & O3). destruct PCO as (Q1 & _ & Q3). lia.
  Qed.

  Lemma ev54 : forall R X, ev (HLib.Eseed R (Wp ++ X)) 54 = Z_to_bv 64 p.
  Proof. intros R X. reflexivity. Qed.

  Lemma ev35 : forall R X, ev (HLib.Eseed R (Wp ++ X)) 35 = Z_to_bv 64 pcons.
  Proof. intros R X. reflexivity. Qed.

  Lemma ev36 : forall R X, ev (HLib.Eseed R (Wp ++ X)) 36 = Z_to_bv 64 icount.
  Proof. intros R X. reflexivity. Qed.

  Lemma evp : forall R X k, 0 <= k <= 88 ->
    edenot (HLib.Eseed R (Wp ++ X)) (EAlu ALU_ADD (EVar 54) (ELit k)) = Z_to_bv 64 (p + k).
  Proof.
    intros R X k Hk. pose proof pd_p_rng as (T1 & T2 & _).
    cbn [edenot]. rewrite ev54. apply w_add; clear - Hk T1 T2; unfold AIMG_TOP, AAPP_HI in *; lia.
  Qed.

  Lemma pS_start : forall R X k, 0 <= k <= 88 -> estart (HLib.Eseed R (Wp ++ X)) (pS k) = (p + k) / 8 + SHBASE.
  Proof.
    intros R X k Hk. pose proof pd_p_rng as (T1 & T2 & _). unfold pS.
    apply estart_sh; [apply evp; exact Hk | clear - Hk T1 T2; unfold AIMG_TOP, AAPP_HI in *; lia].
  Qed.

  Lemma pa_start : forall R X k, 0 <= k <= 88 -> estart (HLib.Eseed R (Wp ++ X)) (SA (EVar 54) k) = p + k.
  Proof.
    intros R X k Hk. pose proof pd_p_rng as (T1 & T2 & _). unfold estart. cbn [a_base a_off edenot].
    rewrite ev54, unsigned_lit by (clear - T1 T2; unfold AIMG_TOP, AAPP_HI in *; lia). reflexivity.
  Qed.

  Lemma fa_start : forall R X k, estart (HLib.Eseed R (Wp ++ X)) (SA (EVar 52) k) = ff + k.
  Proof.
    intros R X k. pose proof pd_vals as (_ & V2 & _). unfold estart. cbn [a_base a_off edenot].
    change (ev (HLib.Eseed R (Wp ++ X)) 52) with (Z_to_bv 64 ff). rewrite unsigned_lit by lia. reflexivity.
  Qed.

  Lemma fsh_start : forall R X, estart (HLib.Eseed R (Wp ++ X)) (SA PD_SHB SHBASE) = ff / 8 + SHBASE.
  Proof.
    intros R X. pose proof pd_vals as (_ & V2 & _). unfold PD_SHB.
    apply estart_sh; [reflexivity | exact V2].
  Qed.

  Lemma pd_sh_apart : forall k, k = 8 \/ k = 80 ->
    (p + k) / 8 + SHBASE + 1 <= ff / 8 + SHBASE \/ ff / 8 + SHBASE + 32 <= (p + k) / 8 + SHBASE.
  Proof.
    intros k Hk. pose proof pd_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    assert (FD : ff + 256 <= p + k \/ p + k + 8 <= ff) by (apply PPF; lia).
    clear - Hk FD R6 PP8. Z.div_mod_to_equations. lia.
  Qed.

  Lemma pd_sh_app : forall k, k = 8 \/ k = 80 ->
    (p + k) / 8 + SHBASE + 1 <= ff + 48 \/ ff + 56 <= (p + k) / 8 + SHBASE.
  Proof.
    intros k Hk. pose proof pd_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof pd_p_rng as (T1 & T2 & _).
    clear - Hk R4 R5 R8 R11 T1 T2. unfold AIMG_TOP, AAPP_HI, ALOWSH_LO, AHI_LO, AFS_HDR, AFS_SIZE, SHBASE in *.
    Z.div_mod_to_equations. lia.
  Qed.

  Lemma kp_ok : forall R X m, addressable m (p + 8) 8 -> addressable m (p + 80) 8 ->
    ro_cells asegs m (p + 8) [C8 (Z_to_bv 64 pcons)] -> ro_cells asegs m (p + 80) [C8 (Z_to_bv 64 icount)] ->
    know_ok asegs (HLib.Eseed R (Wp ++ X)) m kp.
  Proof.
    intros R X m A8 A80 C8 C80.
    pose proof pd_p_rng as (T1 & T2 & T3 & T4). pose proof pd_vals as (V1 & V2 & V3 & V4 & V5).
    assert (B : 0 <= p < 2 ^ 64 /\ p + 88 < 2 ^ 64) by (clear - T1 T2; unfold AIMG_TOP, AAPP_HI in *; lia).
    assert (KS : forall k, k = 8 \/ k = 80 -> addressable m (p + k) 8 ->
                 kentry_ok asegs (HLib.Eseed R (Wp ++ X)) m (KWord (pS k) 1 (ELit 0))).
    { intros k Hk A. unfold pS.
      apply (kshadow _ m (EAlu ALU_ADD (EVar 54) (ELit k)) (p + k) 0 (ELit 0));
        [ apply evp; lia | lia | lia | reflexivity
        | apply (sh0_of_addressable m (p + k) 8 (p + k) A); change (8 * (8 / 8)) with 8; lia ]. }
    assert (KD : forall k, k = 8 \/ k = 80 ->
                 kentry_ok asegs (HLib.Eseed R (Wp ++ X)) m (KDisj (pS k) (ELit 1) (SA PD_SHB SHBASE) (ELit 32))).
    { intros k Hk. cbn [kentry_ok]. rewrite pS_start, fsh_start by lia.
      unfold elenZ. cbn [edenot]. rewrite !unsigned_lit by (clear; lia). apply pd_sh_apart; exact Hk. }
    unfold know_ok, kp. repeat apply Forall_cons; try apply Forall_nil.
    - apply (kword_var asegs _ m 54 p 8 8 pcons (EVar 35));
        [ apply cell8_of_ro; [exact C8 | exact V4] | lia | apply ev54 | lia | lia | lia | apply ev35 ].
    - apply (kword_var asegs _ m 54 p 80 8 icount (EVar 36));
        [ apply cell8_of_ro; [exact C80 | exact V5] | lia | apply ev54 | lia | lia | lia | apply ev36 ].
    - apply krange_var with (z := p); [apply ev54 | lia | lia].
    - apply krange_var with (z := pcons); [apply ev35 | lia | lia].
    - apply kalign_var with (z := pcons); [apply ev35 | lia | lia | exact P16].
    - apply kalign_var with (z := p); [apply ev54 | lia | lia | exact PP8].
    - apply KS; [left; reflexivity | exact A8].
    - apply KS; [right; reflexivity | exact A80].
    - apply KD; left; reflexivity.
    - apply KD; right; reflexivity.
  Qed.

  Lemma sc_p8 : forall R segs base,
    sc_denot segs base (HLib.Eseed R (Wp ++ [])) (SCDisj (pS 8) (ELit 1) (SA (EVar 52) 48) (ELit 8)).
  Proof.
    intros R segs base. pose proof pd_p_rng as (T1 & T2 & _).
    pose proof pd_ranges as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12).
    pose proof (pd_sh_app 8 (or_introl eq_refl)) as SA8.
    cbn [sc_denot]. unfold elenZ, flat. rewrite !pS_start, !fa_start by lia.
    cbn [edenot]. rewrite !unsigned_lit by (clear; lia).
    clear - T1 T2 Q4 Q5 Q8 Q9 Q12 SA8. unfold AIMG_TOP, AAPP_HI, AFS_HDR, SHBASE in *. Z.div_mod_to_equations. lia.
  Qed.

  Lemma pd_c2 : aw = Z_to_bv 64 (err mod 2 ^ 64) ->
    forall R m, rfull R -> rtbl Wp R RTm -> ftbl Wp spz m SFm -> ftbl Wp ff m FTm -> ftbl Wp (ff / 8) m HTm ->
    Pw m -> mem_inv asegs m -> as_RFS H ((2, ff, fp) :: LF) m ->
    addressable m (p + 8) 8 -> addressable m (p + 80) 8 ->
    ro_cells asegs m (p + 8) [C8 (Z_to_bv 64 pcons)] -> ro_cells asegs m (p + 80) [C8 (Z_to_bv 64 icount)] ->
    evt asegs pd_P (MS R F (Z_to_bv 64 RET_MEMSET) fc None m (seg_rom asegs)).
  Proof using All.
    intros AW R m RF HRT HSF HFT HHT HP HMI HRFS A8 A80 C8 C80.
    dkrunP3k HRT HSF HFT HHT HP HMI 600%nat [ADS_CTOR] kp.
    - apply kp_ok; assumption.
    - pose proof pd_p_rng as (T1 & T2 & _).
      pose proof pd_ranges as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12).
      assert (FD : ff + 256 <= p + 8 \/ p + 8 + 8 <= ff) by (apply PPF; lia).
      pose proof (pd_sh_app 8 (or_introl eq_refl)) as SA8.
      unfold scs_denot. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      + cbn [sc_denot]. unfold elenZ, flat. cbn [edenot]. rewrite !unsigned_lit by (clear; lia).
        rewrite pa_start, fa_start by lia.
        clear - T1 T2 Q4 Q5 Q8 Q9 Q12 FD. unfold AIMG_TOP, AAPP_HI, AFS_HDR in *. lia.
      + apply sc_p8.
    - intros R1 m' RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
      tsplit HTS1 HSF1 HFT1 HHT1. cbn [s_pc].
      pose proof pd_ranges as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12).
      assert (FB : 0 <= ff /\ ff + 256 < 2 ^ 64) by (clear - Q4 Q5 Q8 Q9 Q12; unfold AIMG_TOP, AFS_HDR in *; lia).
      rgetp HRT1 (10%bv : bv 5) G10. rgetp HRT1 (11%bv : bv 5) G11. rgetp HRT1 (12%bv : bv 5) G12.
      rgetp HRT1 (13%bv : bv 5) G13. rgetp HRT1 (14%bv : bv 5) G14. rgetp HRT1 (15%bv : bv 5) G15.
      rgetp HRT1 (2%bv : bv 5) G2. rgetp HRT1 (1%bv : bv 5) G1.
      rewrite <- (Z_to_bv_bv_unsigned sp), w_addm in G2 by (clear - Q1 Q2 Q12; unfold ADS_STACK in *; lia).
      eapply (pd_ctor pd_P R1 m');
        [ exact RF1 | exact HRT1 | exact HSF1 | exact HFT1 | exact HHT1 | exact HP1 | exact HMI1
        | eapply RFS_step3; [exact HRFS | exact MU1 | exact WM1]
        | exact G10 | exact G11 | exact G12 | exact G13 | rewrite G14; exact AW | exact G15 | exact G2
        | first [left; lia | right; lia]
        | vm_compute; reflexivity ..
        | ].
      intros R2 m2 RF2 KEQ HSF2 HFT2 HHT2 HP2 HMI2 HRFS2 HDS2.
      rewrite G1, ret_pc_even; [| clear; lia | reflexivity].
      apply pd_c3; [exact RF2 | | | | | exact HP2 | exact HMI2 | exact HRFS2 | exact HDS2].
      + lazymatch type of HRT1 with rtbl _ _ ?T => replace RTc with (keptk T) by (vm_compute; reflexivity) end.
        eapply rtbl_keep; [apply rtbl_keptk; exact HRT1 | apply rsub_keptk | exact KEQ].
      + lazymatch type of HSF2 with ftbl _ _ _ (fabove ?d _) =>
          first [replace d with (-96) in HSF2 by lia | replace d with (-112) in HSF2 by lia] end.
        lazymatch type of HSF2 with ftbl _ _ _ ?T => replace SFc with T by (vm_compute; reflexivity) end.
        exact HSF2.
      + pose proof (ftbl_fsplit _ _ _ 96 1 _ (ftbl_fsplit _ _ _ 160 1 _ HFT2)) as HFc.
        lazymatch type of HFc with ftbl _ _ _ ?T => replace FTc with T by (vm_compute; reflexivity) end.
        exact HFc.
      + lazymatch type of HHT2 with ftbl _ _ _ ?T => replace HTc with T by (vm_compute; reflexivity) end.
        exact HHT2.
  Qed.

  Definition pd_p4 (m : mem) : Prop :=
    addressable m (p + 8) 8 /\ addressable m (p + 80) 8
    /\ ro_cells asegs m (p + 8) [C8 (Z_to_bv 64 pcons)] /\ ro_cells asegs m (p + 80) [C8 (Z_to_bv 64 icount)].

  Lemma pd_p4_keepW : forall W m m',
    (forall x, outside [(spz - ADS_STACK, spz); (ff, ff + 256); (sh ff, sh ff + 32)] x -> outside W x) ->
    munch W m m' -> wmono asegs m m' -> pd_p4 m -> pd_p4 m'.
  Proof using All.
    intros W m m' Hs MU WM HP. unfold pd_p4 in *. destruct HP as (Ha8 & Ha80 & Hc8 & Hc80).
    assert (MU3 : munch [(spz - ADS_STACK, spz); (ff, ff + 256); (sh ff, sh ff + 32)] m m')
      by (eapply munch_weaken; [exact Hs | exact MU]).
    assert (Hsh : forall O, O = p + 8 \/ O = p + 80 -> app_obj O 8 ->
      disjoint_from [(spz - ADS_STACK, spz); (ff, ff + 256); (sh ff, sh ff + 32)] (sh O) (nsh 8)).
    { intros O HO (HO1 & _ & HO3).
      assert (HO8 : O mod 8 = 0).
      { destruct HO as [-> | ->];
          [replace (p + 8) with (p + 1 * 8) by lia | replace (p + 80) with (p + 10 * 8) by lia];
          rewrite Z.mod_add by lia; exact PP8. }
      assert (D : disjoint_from PW (sh O) (nsh 8)).
      { pose proof (PPF O HO) as F1. pose proof (PPS O HO) as S1. unfold ADS_STACK in S1.
        apply pw_sh_apart; [exact HO1 | exact HO8 | lia | reflexivity | exact HO3 | lia | lia]. }
      unfold LbB_DPdK.PW in D. cbn [disjoint_from] in D |- *. unfold ADS_STACK. lia. }
    assert (Hro : forall O, O = p + 8 \/ O = p + 80 ->
      disjoint_from [(spz - ADS_STACK, spz); (ff, ff + 256); (sh ff, sh ff + 32)] O 8).
    { intros O HO. pose proof (PPS O HO). pose proof (PPF O HO). pose proof (PPH O HO).
      cbn [disjoint_from]. lia. }
    split; [|split; [|split]].
    - eapply addressable_transport; [exact Ha8 | exact MU3 | exact WM | apply Hsh; [left; reflexivity | exact PPO8]].
    - eapply addressable_transport; [exact Ha80 | exact MU3 | exact WM | apply Hsh; [right; reflexivity | exact PPO80]].
    - eapply ro_cells_transport; [exact Hc8 | exact MU3 | exact (Hro _ (or_introl eq_refl))].
    - eapply ro_cells_transport; [exact Hc80 | exact MU3 | exact (Hro _ (or_intror eq_refl))].
  Qed.

  Lemma pd_p4_keep3 : forall SF FT HT ks1 ks2 ks3 m m',
    munch (winsT [tS SF ks1; tF FT ks2; tH HT ks3]) m m' -> wmono asegs m m' -> pd_p4 m -> pd_p4 m'.
  Proof using All.
    intros SF FT HT ks1 ks2 ks3 m m' MU WM HP. eapply pd_p4_keepW; [| exact MU | exact WM | exact HP].
    intros x Hx. pose proof shb_eq as Hq. unfold ADS_STACK in Hx.
    cbn [outside winsT map tB tlo thi LbB_DPdK.tS LbB_DPdK.tF LbB_DPdK.tH] in Hx |- *. lia.
  Qed.

  Lemma pd_p4_keepM : forall spc m m', spz - ADS_STACK + AINTRIN_STACK <= spc <= spz ->
    munch [(ff + 32, ff + 32 + 16); (spc - AINTRIN_STACK, spc)] m m' -> wmono asegs m m' -> pd_p4 m -> pd_p4 m'.
  Proof using All.
    intros spc m m' Hspc MU WM HP. eapply pd_p4_keepW; [| exact MU | exact WM | exact HP].
    intros x Hx. cbn [outside] in Hx |- *. lia.
  Qed.

  Lemma pd2 : aw = Z_to_bv 64 (err mod 2 ^ 64) -> forall R, rfull R -> rtbl Wp R RT2 -> ftbl Wp spz m1 SF2 -> ftbl Wp ff m1 FT2 ->
    ftbl Wp (ff / 8) m1 [] -> as_RFS H ((2, ff, fp) :: LF) m1 ->
    evt asegs pd_P (MS R F (Z_to_bv 64 RET_MALLOC) fc None m1 (seg_rom asegs)).
  Proof using All.
    intros HAW R RF HRT HSF HFT HHT HRFS.
    pose proof Pw_m1 as HP.
    dkrunP3 HRT HSF HFT HHT HP MI1 600%nat [AASAN_MEMSET].
    - apply Forall_nil.
    - apply Forall_nil.
    - intros R1 m1' RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
      tsplit HTS1 HSF1 HFT1 HHT1.
      cbn [s_pc].
      assert (RF1m : as_RFS H ((2, ff, fp) :: LF) m1') by (eapply RFS_step3; [exact HRFS | exact MU1 | exact WM1]).
      pose proof (pd_p4_keep3 _ _ _ _ _ _ m1 m1' MU1 WM1 (conj PPA8 (conj PPA80 (conj PPC8 PPC80)))) as PK1.
      pose proof pd_ranges as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
      pose proof pd_vals as (V1 & V2 & V3 & V4 & V5).
      rgetp HRT1 (10%bv : bv 5) E10. rgetp HRT1 (11%bv : bv 5) E11. rgetp HRT1 (12%bv : bv 5) E12.
      rgetp HRT1 (2%bv : bv 5) E2. rgetp HRT1 (1%bv : bv 5) E1.
      assert (EA : alu64 ALU_ADD sp (Z_to_bv 64 (-112)) = Z_to_bv 64 (spz - 112)).
      { rewrite <- (Z_to_bv_bv_unsigned sp) at 1. rewrite w_addm by (clear - G1 G2 G3 G12; unfold ADS_STACK in *; lia).
        f_equal; clear; lia. }
      rewrite EA in E2.
      eapply (pd_memset _ R1 m1' _ _ _ _ RET_MEMSET (spz - 112) RF1 HRT1 HSF1 HFT1 HHT1 HP1 HMI1 RF1m E10 E11 E12 E2 E1);
        [ lia | unfold RET_MEMSET; lia | unfold RET_MEMSET; reflexivity | vm_compute; reflexivity
        | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | ].
      intros R2 m2 RF2 HRT2 HSF2 HFT2 HHT2 HP2 HMI2 HRFS2 MU2 WM2.
      destruct (pd_p4_keepM (spz - 112) m1' m2 ltac:(unfold ADS_STACK, AINTRIN_STACK; lia) MU2 WM2 PK1) as (Q1 & Q2 & Q3 & Q4).
      replace (spz - 112 - spz) with (-112) in HSF2 by lia.
      assert (T1 : rtbl Wp R2 RTm) by (apply (rtbl_sub _ R2 _ _ HRT2); vm_compute; reflexivity).
      assert (T2 : ftbl Wp spz m2 SFm) by (apply (ftbl_sub _ _ _ _ _ HSF2); vm_compute; reflexivity).
      assert (T3 : ftbl Wp ff m2 FTm) by (apply (ftbl_sub _ _ _ _ _ HFT2); vm_compute; reflexivity).
      assert (T4 : ftbl Wp (ff / 8) m2 HTm) by (apply (ftbl_sub _ _ _ _ _ HHT2); vm_compute; reflexivity).
      exact (pd_c2 HAW R2 m2 RF2 T1 T2 T3 T4 HP2 HMI2 HRFS2 Q1 Q2 Q3 Q4).
  Qed.
End Pd0B.
