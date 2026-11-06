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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmCall LbA_PmXp LbA_PmXv LbA_PmVec LbA_PmVup LbA_PmGlue LbA_PmVops.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma set_v2A_id : forall c, set_v2A c (c_v2 c) = c. Proof. intros []; reflexivity. Qed.
Lemma set_v1A_id : forall c, set_v1A c (c_v1 c) = c. Proof. intros []; reflexivity. Qed.

Definition E_SH (k : Z) : expr := EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit k)) (ELit 3)) (ELit SHBASE).
Definition E_P (k : Z) : expr := EAlu ALU_ADD (EVar WV_P) (ELit k).

Definition RT_VSC : list (reg * expr) := [(9%bv, EVar 35); (10%bv, EVar 41); (25%bv, E_P 248)].
Definition RT_VSC' : list (reg * expr) := [(9%bv, EVar 35); (10%bv, ELit 0); (11%bv, E_P 216); (24%bv, EVar 41); (25%bv, E_P 248)].
Definition RT_VSR : list (reg * expr) := [(9%bv, EVar 35); (10%bv, EVar 41)].
Definition RT_VSR' : list (reg * expr) := [(9%bv, EVar 35); (10%bv, ELit 0); (25%bv, E_P 248); (26%bv, EVar 41)].
Definition RT_VSO : list (reg * expr) := [(9%bv, EVar 35); (10%bv, EVar 41); (19%bv, E_SH 224)].
Definition RT_VSO' : list (reg * expr) := [(9%bv, EVar 35); (10%bv, E_P 56); (11%bv, E_P 224); (19%bv, E_SH 224); (25%bv, EVar 41)].
Definition VS_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 26; 27]%bv.
Definition VSR_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 27]%bv.
Definition VSO_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv.

Section VS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma HHv : asan_rt_hyps H. Proof. exact (rt_bp_base H HHbp). Qed.

  Lemma pm_vstore_same2_gen : forall (pc pc' : Z) (RT RT' : list (reg * expr)) (KEPT : list reg) (sl : list (Z * expr)) (kx : list kentry)
      (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> incl sl tbl ->
    (forall E, env_world H w E -> know_ok asegs E m kx) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) -> rfull R ->
    tbl_closed tbl = true -> keys_ok (map fst tbl) = true -> keys_nonneg (map fst tbl) = true ->
    tbl_closed ftbl = true -> fkeys_ok (map fst ftbl) = true ->
    regs_tblX w [Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)))] R RT ->
    (forall fuel, let kn := PM_KN_FIX ++ slot_kn sl ++ kx in
       let r := sym_exec ASEGS fuel true [pc'] (SCR [] [] []) (SS pc (srs sr_id RT) [] kn 42%N) [] in
       fuel = 40%nat ->
       s_pc (fst (fst r)) = pc' /\ snd (fst r) = [] /\ s_log (fst (fst r)) = [SE (SA (EVar 32) 248) 8 (EVar 41)]
       /\ sr_tbl_checkX 42%N (s_regs (fst (fst r))) RT' = true
       /\ (forall r0, In r0 KEPT -> sr_get (s_regs (fst (fst r))) r0 = sr_get (srs sr_id RT) r0)) ->
    tbl_okX 42%N RT = true ->
    (forall msF2 mo2 m2 R2, as_AKREL H s (mkCfg msF2 mo2) ->
       as_VIS H s msF2 = MS R2 F (Z_to_bv 64 pc') fc None m2 (seg_rom asegs) -> rfull R2 ->
       PMXAT H LINV w s LB LBs m2 mo2 c ins tbl ftbl TB spal ->
       (forall r, In r KEPT -> PropExec.getr R2 r = PropExec.getr R r) ->
       regs_tblX w [Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)))] R2 RT' ->
       ffkeep w m m2 ->
       as_SR H Q (mkCfg msF2 mo2)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros pc pc' RT RT' KEPT sl kx w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc Q OK X Hsl HKX KR VIS RF Hc Hk Hknn Hfc Hfk HTv RUN Hok K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as V2.
    destruct (c_v2 c) as [[b xs] cap] eqn:EV2. cbn [t3a t3b t3c fst snd] in *.
    pose proof V2 as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2 & FE).
    set (e := b + 4 * Zlen xs) in *.
    assert (Hbr : 0 <= b /\ b + 4 * cap <= 2 ^ 63) by (destruct Hb as [[-> ->]|(B1 & B2 & B3 & B4 & _)]; lia).
    set (Xv := [Z_to_bv 64 e]) in *.
    assert (HE : env_world H w (Eseed R (wenv_vals w ++ Xv))) by apply env_world_seed.
    pose proof (ev_p H w _ OK HE) as EP.
    specialize (RUN 40%nat eq_refl). cbn zeta in RUN.
    set (r := sym_exec ASEGS 40 true [pc'] (SCR [] [] []) (SS pc (srs sr_id RT) [] (PM_KN_FIX ++ slot_kn sl ++ kx) 42) []) in RUN.
    destruct r as [[SSr scs] scr'] eqn:Er. cbn [fst snd] in RUN. destruct RUN as (RPC & -> & RLOG & RTB & RKEPT).
    assert (HK0 : know_ok asegs (Eseed R (wenv_vals w ++ Xv)) m (PM_KN_FIX ++ slot_kn sl ++ kx)).
    { destruct (pm_kn_fix_ok H HHv LINV w s LB LBs m mo c ins tbl ftbl TB spal _ OK X HE Hc Hk Hfc Hfk) as (K1 & K2 & _).
      unfold know_ok. apply Forall_app. split; [exact K1|]. apply Forall_app. split; [| exact (HKX _ HE)].
      unfold slot_kn. apply Forall_forall. intros ke Hin.
      apply in_map_iff in Hin. destruct Hin as ([k e'] & <- & Hin). cbn [fst snd]. apply K2. apply Hsl. exact Hin. }
    eapply (pm_run_raw H HHv LINV w s LB LBs m mo c ins tbl ftbl TB spal _ R F fc pc RT Xv (PM_KN_FIX ++ slot_kn sl ++ kx) 40%nat [pc'] (SCR [] [] []) 42%N SSr [] scr' RT' _ OK X KR VIS RF HTv Hok Er HK0 ltac:(constructor) RTB).
    intros msF1 mo1 R1 KR1 MP1 VIS1 RF1 MI1 HT1 HR1 Hlf1. rewrite RPC in VIS1. rewrite RLOG in Hlf1, VIS1, MI1.
    set (M1 := mem_denot (Eseed R (wenv_vals w ++ Xv)) m [SE (SA (EVar 32) 248) 8 (EVar 41)]) in *.
    pose proof (munch_sym (Eseed R (wenv_vals w ++ Xv)) m _ [(EVar WV_P, 248, 256)] Hlf1 ltac:(vm_compute; reflexivity)) as MU1.
    cbn [num_wins map] in MU1. rewrite EP in MU1.
    pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as STK.
    destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) STK ltac:(lia)) as [STK1 _].
    assert (OMP : forall y k, Forall (omiss (Eseed R (wenv_vals w ++ Xv)) (EVar WV_P) y k) [SE (SA (EVar 32) 248) 8 (EVar 41)]).
    { intros y k. apply Forall_cons; [| apply Forall_nil]. intros Hne. cbn in Hne. discriminate. }
    assert (X1 : PMXAT H LINV w s LB LBs M1 mo1 c ins tbl ftbl TB spal).
    { rewrite <- (set_v2A_id c). rewrite EV2.
      replace (b, xs, cap) with (t3a (c_v2 c), xs, t3c (c_v2 c)) by (rewrite EV2; reflexivity).
      eapply (pmxa_vupd2 H HHv LINV LINV_frame w s LB LBs m mo c ins tbl ftbl TB spal M1 mo1 [(wa_p w + 248, wa_p w + 256)] []);
        [exact OK | exact X | exact Hknn | exact Hfk | rewrite app_nil_r; exact MU1 | apply wmono_mem_denot
        | intros x Hx; apply mem_denot_defined; exact Hx | exact MP1 | exact MI1 | apply stk_mem_denot; exact STK1
        | apply Forall_cons; [| apply Forall_nil] | apply Forall_nil | |].
      - split; [cbn; lia|]. left. cbn [fst snd]. unfold O_V2. lia.
      - rewrite EV2. cbn [t3a t3c fst snd]. unfold vec32.
        split; [exact Hv|]. split; [exact Hv'|]. split; [intros i Hi; apply mem_denot_defined; apply HD; lia|].
        split; [exact Hlen|]. split; [exact Hb|]. split; [| split; [| split]].
        + replace (wa_p w + O_V2) with (wa_p w + 240) by reflexivity.
          eapply (fld_field_after (Eseed R (wenv_vals w ++ Xv)) m _ (EVar WV_P) (wa_p w) 240 8 b Hlf1 EP);
            [apply OMP | vm_compute; reflexivity | lia | cbn; lia | exact F0].
        + replace (wa_p w + O_V2 + 8) with (wa_p w + 248) by (unfold O_V2; lia).
          assert (SV : sval (Eseed R (wenv_vals w ++ Xv)) [SE (SA (EVar 32) 248) 8 (EVar 41)] (EVar WV_P) 248 8 e = e).
          { unfold sval. lfield_rw. cbv beta iota. ev_xs. rewrite u64_of_Z by lia. reflexivity. }
          enough (FF1 : fld ASEGS M1 (wa_p w + 248) 8 (sval (Eseed R (wenv_vals w ++ Xv)) [SE (SA (EVar 32) 248) 8 (EVar 41)] (EVar WV_P) 248 8 e)) by (rewrite SV in FF1; exact FF1).
          eapply (fld_field_after (Eseed R (wenv_vals w ++ Xv)) m _ (EVar WV_P) (wa_p w) 248 8 e Hlf1 EP);
            [apply OMP | vm_compute; reflexivity | lia | cbn; lia | replace (wa_p w + 248) with (wa_p w + O_V2 + 8) by (unfold O_V2; lia); exact F1].
        + replace (wa_p w + O_V2 + 16) with (wa_p w + 256) by (unfold O_V2; lia).
          eapply (fld_field_after (Eseed R (wenv_vals w ++ Xv)) m _ (EVar WV_P) (wa_p w) 256 8 (b + 4 * cap) Hlf1 EP);
            [apply OMP | vm_compute; reflexivity | lia | cbn; lia | replace (wa_p w + 256) with (wa_p w + O_V2 + 16) by (unfold O_V2; lia); exact F2].
        + intros i Hi. destruct (FE i Hi) as [R1i F1i]. split; [exact R1i|].
          destruct Hb as [[B0 C0]|(Bpos & B16 & Cpos & Bhi & Hlive & Bapart)]; [exfalso; lia|].
          eapply fld_munch; [exact F1i | exact MU1 | | lia | cbn; lia]. cbn [disjoint_from]. unfold O_V2 in Bapart. split; [lia | exact I].
      - rewrite EV2. cbn [t3a t3b t3c fst snd]. intros NZ. cbn [t3a t3b t3c fst snd] in NZ |- *.
        pose proof (proj1 (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)) as (_ & _ & _ & _ & S5 & _). rewrite EV2 in S5. specialize (S5 NZ). cbn [t3a t3b t3c fst snd] in S5.
        destruct Hb as [[B0 C0]|(Bpos & B16 & Cpos & Bhi & Hlive & Bapart)]; [exfalso; lia|].
        pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
        assert (BLK : exists pid, In (pid, b, 4 * cap) LBs /\ In (pid, b, 4 * cap) LB /\ In (b, 4 * cap) (lbl LB) /\ ablock_range H b (4 * cap) /\ 4 * cap <= 2 ^ 31).
        { apply (cblk_facts H HHv LINV w s LB LBs m mo c ins tbl ftbl TB spal b (4 * cap) OK X).
          unfold c_blocks. rewrite EV2. cbn [t3a t3c fst snd]. rewrite !in_app_iff. right; right; right; right; left.
          destruct (Z.eqb_spec b 0); [lia | left; reflexivity]. }
        destruct BLK as (pid & _ & _ & _ & (R0 & R16 & Rn & RI & RC & RF' & RAPP) & SZ).
        pose proof (aapp_bounds _ _ RAPP Rn) as (AB1 & AB2 & AB3 & AB4 & AB5).
        pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE b (4 * cap) PA ltac:(lia) ltac:(lia) ltac:(lia)) as DSH.
        eapply SHAD_transport; [exact S5 | exact MU1 | apply wmono_mem_denot |].
        rewrite RtA_Iface.cc_gen_length by lia. cbn [disjoint_from]. unfold PARSER_SIZE in DSH. split; [lia | exact I]. }
    eapply (K msF1 mo1 M1 R1 KR1 VIS1 RF1 X1).
    - intros r0 Hr0. rewrite (HR1 r0), (RKEPT r0 Hr0).
      symmetry. exact (regs_ok_of_tbl w R RT Xv 42%N HTv Hok r0).
    - exact HT1.
    - apply (ffkeep_munch w _ m M1 MU1 (wmono_mem_denot _ _ _)). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      pose proof (p_apart_ff H w OK) as PAF. unfold O_WIDX, PARSER_SIZE in PAF. lia.
  Qed.

  Lemma pm_vstore_same2c : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xee9c0) fc None m (seg_rom asegs) -> rfull R ->
    tbl_closed tbl = true -> keys_ok (map fst tbl) = true -> keys_nonneg (map fst tbl) = true ->
    tbl_closed ftbl = true -> fkeys_ok (map fst ftbl) = true ->
    In (1032, E_SH 248) tbl -> In (768, E_P 216) tbl ->
    PropExec.getr R 9%bv = Z_to_bv 64 (wa_s1 w) ->
    PropExec.getr R 10%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c))) -> PropExec.getr R 25%bv = Z_to_bv 64 (wa_p w + 248) ->
    (forall msF2 mo2 m2 R2, as_AKREL H s (mkCfg msF2 mo2) ->
       as_VIS H s msF2 = MS R2 F (Z_to_bv 64 0xee9dc) fc None m2 (seg_rom asegs) -> rfull R2 ->
       PMXAT H LINV w s LB LBs m2 mo2 c ins tbl ftbl TB spal ->
       (forall r, In r VS_KEPT -> PropExec.getr R2 r = PropExec.getr R r) ->
       PropExec.getr R2 10%bv = Z_to_bv 64 0 -> PropExec.getr R2 11%bv = Z_to_bv 64 (wa_p w + 216) ->
       PropExec.getr R2 24%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c))) -> PropExec.getr R2 25%bv = Z_to_bv 64 (wa_p w + 248) ->
       ffkeep w m m2 ->
       as_SR H Q (mkCfg msF2 mo2)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc Q OK X KR VIS RF Hc Hk Hknn Hfc Hfk H1032 H768 G9 G10 G25 K.
    pose proof (pmw_bounds H w OK) as BND.
    eapply (pm_vstore_same2_gen 0xee9c0 0xee9dc RT_VSC RT_VSC' VS_KEPT [(1032, E_SH 248); (768, E_P 216)]
              [KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 248)) (ELit 3)) 2147450880) 1 (ELit 0)] w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc Q OK X);
      [intros ke Hke; destruct Hke as [<-|[<-|[]]]; assumption | intros E HE; unfold know_ok; pmk_list H HHv w OK X HE | exact KR | exact VIS | exact RF | exact Hc | exact Hk | exact Hknn | exact Hfc | exact Hfk | | | vm_compute; reflexivity |].
    - unfold regs_tblX, RT_VSC. repeat (apply Forall_cons); [| | | apply Forall_nil]; cbn [fst snd].
      + rewrite G9. reflexivity. + rewrite G10. reflexivity. + rewrite G25. symmetry. eapply ev_add; [reflexivity | lia | lia].
    - intros fuel; cbn zeta; intros ->. vm_compute. repeat split; try reflexivity. intros r0 Hr0. unfold VS_KEPT in Hr0.
      repeat (destruct Hr0 as [<-|Hr0]; [vm_compute; reflexivity|]). destruct Hr0.
    - intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2 HT2 FK2. eapply (K msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2); [rtf HT2 | rtf HT2 | rtf HT2 | rtf HT2 | exact FK2].
  Qed.

  Lemma pm_vstore_same2r : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf24e4) fc None m (seg_rom asegs) -> rfull R ->
    tbl_closed tbl = true -> keys_ok (map fst tbl) = true -> keys_nonneg (map fst tbl) = true ->
    tbl_closed ftbl = true -> fkeys_ok (map fst ftbl) = true ->
    In (1032, E_SH 248) tbl -> In (928, E_P 248) tbl ->
    PropExec.getr R 9%bv = Z_to_bv 64 (wa_s1 w) ->
    PropExec.getr R 10%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c))) ->
    (forall msF2 mo2 m2 R2, as_AKREL H s (mkCfg msF2 mo2) ->
       as_VIS H s msF2 = MS R2 F (Z_to_bv 64 0xf2500) fc None m2 (seg_rom asegs) -> rfull R2 ->
       PMXAT H LINV w s LB LBs m2 mo2 c ins tbl ftbl TB spal ->
       (forall r, In r VSR_KEPT -> PropExec.getr R2 r = PropExec.getr R r) ->
       PropExec.getr R2 10%bv = Z_to_bv 64 0 -> PropExec.getr R2 25%bv = Z_to_bv 64 (wa_p w + 248) ->
       PropExec.getr R2 26%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c))) ->
       ffkeep w m m2 ->
       as_SR H Q (mkCfg msF2 mo2)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc Q OK X KR VIS RF Hc Hk Hknn Hfc Hfk H1032 H928 G9 G10 K.
    pose proof (pmw_bounds H w OK) as BND.
    eapply (pm_vstore_same2_gen 0xf24e4 0xf2500 RT_VSR RT_VSR' VSR_KEPT [(1032, E_SH 248); (928, E_P 248)]
              [KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 248)) (ELit 3)) 2147450880) 1 (ELit 0)] w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc Q OK X);
      [intros ke Hke; destruct Hke as [<-|[<-|[]]]; assumption | intros E HE; unfold know_ok; pmk_list H HHv w OK X HE | exact KR | exact VIS | exact RF | exact Hc | exact Hk | exact Hknn | exact Hfc | exact Hfk | | | vm_compute; reflexivity |].
    - unfold regs_tblX, RT_VSR. repeat (apply Forall_cons); [| | apply Forall_nil]; cbn [fst snd].
      + rewrite G9. reflexivity. + rewrite G10. reflexivity.
    - intros fuel; cbn zeta; intros ->. vm_compute. repeat split; try reflexivity. intros r0 Hr0. unfold VSR_KEPT in Hr0.
      repeat (destruct Hr0 as [<-|Hr0]; [vm_compute; reflexivity|]). destruct Hr0.
    - intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2 HT2 FK2. eapply (K msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2); [rtf HT2 | rtf HT2 | rtf HT2 | exact FK2].
  Qed.

  Lemma pm_vstore_same1 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf2358) fc None m (seg_rom asegs) -> rfull R ->
    tbl_closed tbl = true -> keys_ok (map fst tbl) = true -> keys_nonneg (map fst tbl) = true ->
    tbl_closed ftbl = true -> fkeys_ok (map fst ftbl) = true ->
    In (944, E_P 56) tbl -> In (896, E_P 224) tbl ->
    PropExec.getr R 9%bv = Z_to_bv 64 (wa_s1 w) ->
    PropExec.getr R 10%bv = Z_to_bv 64 (t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c)) ->
    PropExec.getr R 19%bv = edenot (Eseed bvmap_empty (wenv_vals w)) (E_SH 224) ->
    (forall msF2 mo2 m2 R2, as_AKREL H s (mkCfg msF2 mo2) ->
       as_VIS H s msF2 = MS R2 F (Z_to_bv 64 0xf2374) fc None m2 (seg_rom asegs) -> rfull R2 ->
       PMXAT H LINV w s LB LBs m2 mo2 c ins tbl ftbl TB spal ->
       (forall r, In r VSO_KEPT -> PropExec.getr R2 r = PropExec.getr R r) ->
       PropExec.getr R2 10%bv = Z_to_bv 64 (wa_p w + 56) -> PropExec.getr R2 11%bv = Z_to_bv 64 (wa_p w + 224) ->
       PropExec.getr R2 25%bv = Z_to_bv 64 (t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c)) ->
       ffkeep w m m2 ->
       as_SR H Q (mkCfg msF2 mo2)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc Q OK X KR VIS RF Hc Hk Hknn Hfc Hfk H944 H896 G9 G10 G19 K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as V1.
    destruct (c_v1 c) as [[b n] cap] eqn:EV1. cbn [t3a t3b t3c fst snd] in *.
    pose proof V1 as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2).
    set (e := b + OPND_SZ * n) in *.
    assert (Hbr : 0 <= b /\ b + OPND_SZ * cap <= 2 ^ 63) by (destruct Hb as [[-> ->]|(B1 & B2 & B3 & B4 & _)]; unfold OPND_SZ in *; lia).
    assert (He : 0 <= e <= b + OPND_SZ * cap) by (unfold e, OPND_SZ in *; lia).
    set (Xv := [Z_to_bv 64 e]) in *.
    assert (HE : env_world H w (Eseed R (wenv_vals w ++ Xv))) by apply env_world_seed.
    pose proof (ev_p H w _ OK HE) as EP.
    assert (HTv : regs_tblX w Xv R RT_VSO).
    { unfold regs_tblX, RT_VSO. repeat (apply Forall_cons); [| | | apply Forall_nil]; cbn [fst snd].
      - rewrite G9. reflexivity. - rewrite G10. reflexivity.
      - rewrite G19. apply (edenot_app_x bvmap_empty (wenv_vals w) Xv 41%N); [reflexivity | rewrite wenv_vals_length; cbn; lia]. }
    assert (HK0 : know_ok asegs (Eseed R (wenv_vals w ++ Xv)) m
              (PM_KN_FIX ++ slot_kn [(944, E_P 56); (896, E_P 224)] ++ [KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) 2147450880) 1 (ELit 0)])).
    { destruct (pm_kn_fix_ok H HHv LINV w s LB LBs m mo c ins tbl ftbl TB spal _ OK X HE Hc Hk Hfc Hfk) as (K1 & K2 & _).
      unfold know_ok. apply Forall_app. split; [exact K1|]. apply Forall_app. split.
      - cbn [slot_kn map fst snd]. apply Forall_cons; [exact (K2 _ _ H944)|]. apply Forall_cons; [exact (K2 _ _ H896) | apply Forall_nil].
      - unfold know_ok. pmk_list H HHv w OK X HE. }
    pm_goR0 HHv (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) KR VIS RF HTv Xv
      (PM_KN_FIX ++ slot_kn [(944, E_P 56); (896, E_P 224)] ++ [KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) 2147450880) 1 (ELit 0)])
      HK0 40%nat [0xf2374] (@nil bool) 42%N RT_VSO'.
    { split_scs. }
    intros msF1 mo1 R1 KR1 MP1 VIS1 RF1 MI1 HT1 HR1 Hlf1.
    lazymatch type of VIS1 with _ = MS _ _ _ _ _ ?mm _ => set (M1 := mm) in * end.
    pose proof (munch_sym (Eseed R (wenv_vals w ++ Xv)) m _ [(EVar WV_P, 224, 232)] Hlf1 ltac:(vm_compute; reflexivity)) as MU1.
    cbn [num_wins map] in MU1. rewrite EP in MU1. fold M1 in MU1.
    pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as STK.
    destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) STK ltac:(lia)) as [STK1 _].
    assert (OMP : forall y k, Forall (omiss (Eseed R (wenv_vals w ++ Xv)) (EVar WV_P) y k) (s_log SSr)).
    { intros y k. subst SSr. cbn [s_log]. apply Forall_cons; [| apply Forall_nil]. intros Hne. cbn in Hne. discriminate. }
    assert (X1 : PMXAT H LINV w s LB LBs M1 mo1 c ins tbl ftbl TB spal).
    { rewrite <- (set_v1A_id c). rewrite EV1.
      replace (b, n, cap) with (t3a (c_v1 c), n, t3c (c_v1 c)) by (rewrite EV1; reflexivity).
      eapply (pmxa_vupd1 H HHv LINV LINV_frame w s LB LBs m mo c ins tbl ftbl TB spal M1 mo1 [(wa_p w + 224, wa_p w + 232)] []);
        [exact OK | exact X | exact Hknn | exact Hfk | rewrite app_nil_r; exact MU1 | apply wmono_mem_denot
        | intros x Hx; apply mem_denot_defined; exact Hx | exact MP1 | exact MI1 | subst M1; apply stk_mem_denot; exact STK1
        | apply Forall_cons; [| apply Forall_nil] | apply Forall_nil | |].
      - split; [cbn; lia|]. left. cbn [fst snd]. unfold O_V1. lia.
      - rewrite EV1. cbn [t3a t3c fst snd]. unfold vec_opnd.
        split; [exact Hv|]. split; [exact Hv'|]. split; [intros i Hi; apply mem_denot_defined; apply HD; lia|].
        split; [exact Hlen|]. split; [exact Hb|]. split; [| split].
        + replace (wa_p w + O_V1) with (wa_p w + 216) by reflexivity.
          eapply (fld_field_after (Eseed R (wenv_vals w ++ Xv)) m _ (EVar WV_P) (wa_p w) 216 8 b Hlf1 EP);
            [apply OMP | vm_compute; reflexivity | lia | cbn; lia | exact F0].
        + replace (wa_p w + O_V1 + 8) with (wa_p w + 224) by (unfold O_V1; lia).
          assert (SV : sval (Eseed R (wenv_vals w ++ Xv)) (s_log SSr) (EVar WV_P) 224 8 e = e).
          { unfold sval. subst SSr. cbn [s_log]. lfield_rw. cbv beta iota. ev_xs. rewrite u64_of_Z by lia. reflexivity. }
          enough (FF1 : fld ASEGS M1 (wa_p w + 224) 8 (sval (Eseed R (wenv_vals w ++ Xv)) (s_log SSr) (EVar WV_P) 224 8 e)) by (rewrite SV in FF1; exact FF1).
          eapply (fld_field_after (Eseed R (wenv_vals w ++ Xv)) m _ (EVar WV_P) (wa_p w) 224 8 e Hlf1 EP);
            [apply OMP | vm_compute; reflexivity | lia | cbn; lia | replace (wa_p w + 224) with (wa_p w + O_V1 + 8) by (unfold O_V1; lia); exact F1].
        + replace (wa_p w + O_V1 + 16) with (wa_p w + 232) by (unfold O_V1; lia).
          eapply (fld_field_after (Eseed R (wenv_vals w ++ Xv)) m _ (EVar WV_P) (wa_p w) 232 8 (b + OPND_SZ * cap) Hlf1 EP);
            [apply OMP | vm_compute; reflexivity | lia | cbn; lia | replace (wa_p w + 232) with (wa_p w + O_V1 + 16) by (unfold O_V1; lia); exact F2].
      - rewrite EV1. cbn [t3a t3b t3c fst snd]. intros NZ. cbn [t3a t3b t3c fst snd] in NZ |- *.
        pose proof (proj1 (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)) as (_ & _ & _ & S4 & _). rewrite EV1 in S4. specialize (S4 NZ). cbn [t3a t3b t3c fst snd] in S4.
        destruct Hb as [[B0 C0]|(Bpos & B16 & Cpos & Bhi & Hlive & Bapart)]; [exfalso; lia|].
        pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
        assert (BLK : exists pid, In (pid, b, OPND_SZ * cap) LBs /\ In (pid, b, OPND_SZ * cap) LB /\ In (b, OPND_SZ * cap) (lbl LB) /\ ablock_range H b (OPND_SZ * cap) /\ OPND_SZ * cap <= 2 ^ 31).
        { apply (cblk_facts H HHv LINV w s LB LBs m mo c ins tbl ftbl TB spal b (OPND_SZ * cap) OK X).
          unfold c_blocks. rewrite EV1. cbn [t3a t3c fst snd]. rewrite !in_app_iff. right; right; right; left.
          unfold vec_opnd_blocks. destruct (Z.eqb_spec b 0); [lia | left; reflexivity]. }
        destruct BLK as (pid & _ & _ & _ & (R0 & R16 & Rn & RI & RC & RF' & RAPP) & SZ).
        pose proof (aapp_bounds _ _ RAPP Rn) as (AB1 & AB2 & AB3 & AB4 & AB5).
        pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE b (OPND_SZ * cap) PA ltac:(lia) ltac:(lia) ltac:(lia)) as DSH.
        eapply SHAD_transport; [exact S4 | exact MU1 | apply wmono_mem_denot |].
        rewrite RtA_Iface.cc_gen_length by lia. cbn [disjoint_from]. unfold PARSER_SIZE in DSH. split; [lia | exact I]. }
    eapply (K msF1 mo1 M1 R1 KR1 VIS1 RF1 X1).
    - intros r0 Hr0. rewrite (HR1 r0). unfold VSO_KEPT in Hr0.
      repeat (destruct Hr0 as [<-|Hr0]; [first [rewrite G9; reflexivity | rewrite G19; apply (edenot_wv w R bvmap_empty Xv); reflexivity | reflexivity] |]). destruct Hr0.
    - rtf HT1.
    - rtf HT1.
    - rtf HT1.
    - apply (ffkeep_munch w _ m M1 MU1 (wmono_mem_denot _ _ _)). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      pose proof (p_apart_ff H w OK) as PAF. unfold O_WIDX, PARSER_SIZE in PAF. lia.
  Qed.
End VS.
