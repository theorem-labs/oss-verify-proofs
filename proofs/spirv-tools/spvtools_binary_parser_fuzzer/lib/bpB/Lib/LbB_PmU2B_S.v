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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmInit LbB_PmFin LbB_PmExit2 LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmLH LbB_PmVops LbB_PmU2K LbB_ContStmt LbB_PmVS LbB_PmU2B_F.

Definition RT_F091C : list (reg * expr) :=
  [(1%bv, ELit 0xf0920); (2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1);
   (10%bv, EAlu ALU_ADD (EVar WV_P) (ELit 240)); (11%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9120));
   (18%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9120));
   (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 256)) (ELit 3)) (ELit SHBASE)); (20%bv, SH_FF);
   (21%bv, EAlu ALU_ADD (EVar WV_P) (ELit 248)); (22%bv, EAlu ALU_ADD (EVar WV_P) (ELit 256)); (25%bv, ELit SHBASE);
   (26%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 248)) (ELit 3)) (ELit SHBASE));
   (27%bv, EAlu ALU_ADD (EVar WV_P) (ELit 48))].

Definition RT_F0920 : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (18%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9120));
   (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 256)) (ELit 3)) (ELit SHBASE)); (20%bv, SH_FF);
   (21%bv, EAlu ALU_ADD (EVar WV_P) (ELit 248)); (22%bv, EAlu ALU_ADD (EVar WV_P) (ELit 256)); (25%bv, ELit SHBASE);
   (26%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 248)) (ELit 3)) (ELit SHBASE));
   (27%bv, EAlu ALU_ADD (EVar WV_P) (ELit 48))].

Definition RT_F0940 : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (10%bv, ELit 5);
   (18%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9120)); (19%bv, EVar WV_P); (20%bv, SH_FF);
   (21%bv, EAlu ALU_ADD (EVar WV_P) (ELit 248)); (22%bv, EVar 41); (24%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9040));
   (25%bv, ELit SHBASE); (26%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 248)) (ELit 3)) (ELit SHBASE));
   (27%bv, EAlu ALU_ADD (EVar WV_P) (ELit 48))].

Definition SL_F0920 : list (Z * expr) := [(648, EVar WV_P); (624, EAlu ALU_ADD (EVar WV_FF) (ELit 9040))].
Definition KX_F0920 : list kentry :=
  [KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 248)) (ELit 3)) SHBASE) 1 (ELit 0)].

Lemma ev_and3_add : forall E (n : N) (e k : Z), edenot E (EVar n) = Z_to_bv 64 e -> 0 <= e < 2 ^ 64 ->
  0 <= e + k < 2 ^ 64 -> edenot E (EAlu ALU_AND (EAlu ALU_ADD (EVar n) (ELit k)) (ELit 3)) = Z_to_bv 64 ((e + k) mod 4).
Proof.
  intros E n e k Hx H0 H1.
  change (edenot E (EAlu ALU_AND (EAlu ALU_ADD (EVar n) (ELit k)) (ELit 3)))
    with (alu64 ALU_AND (edenot E (EAlu ALU_ADD (EVar n) (ELit k))) (Z_to_bv 64 3)).
  rewrite (ev_add E n e k Hx H0 H1). rewrite w_and by lia.
  change 3 with (Z.ones 2) at 1. rewrite Z.land_ones by lia. reflexivity.
Qed.

Section U2B.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Local Notation XS_S c := [Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c))); Z_to_bv 64 (t3a (c_v2 c) + 4 * t3c (c_v2 c))]
    (only parsing).

  Lemma pm_u2b_S : forall (w : pmwA H) s LB LBs m mo c TB spal msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [OB_INST; OB_FIRST_WORD] TBL_F0884 [] TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf0884) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_F0884 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    Zlen (t3b (c_v2 c)) = t3c (c_v2 c) ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 (v4_entry V32_SLOW_CREF)) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s LB LBs m1 mo1 c [OB_INST; OB_FIRST_WORD] TBL_F08EC [] TB spal ->
       regs_tbl w R1 RT_F091C -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       PropExec.getr R1 23%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c))) ->
       ffkeep w m m1 -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c TB spal msF R F fc Q OK X0 KR0 VIS0 RF0 HT0 G3_0 G4_0 HCAP KB.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (Hv2 & Hv2' & HD2 & Hlen2 & Hb2 & F20 & F21 & F22 & FE2).
    assert (Hbr2 : 0 <= t3a (c_v2 c) /\ t3a (c_v2 c) + 4 * t3c (c_v2 c) <= 2 ^ 63)
      by (destruct Hb2 as [[E1 E2]|(B1 & B2 & B3 & B4 & _)]; lia).
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (XS_S c) (@nil kentry) 200%nat [v4_entry V32_SLOW_CREF] [true] 41%N
          [OB_INST; OB_FIRST_WORD] [648] (@nil Z) TBL_F08EC (@nil (Z * expr)) RT_F091C.
    { split_scs;
        first [ eapply (sc_rd_fld8 _ _ _ (wa_p w + O_V2 + 8));
                [ exact F21
                | rewrite (adenot_of_estart _ _ (wa_p w + O_V2 + 8));
                  [ reflexivity
                  | rewrite (estart_p H w _ _ OK (env_world_seed H w R (XS_S c))); unfold O_V2; lia
                  | unfold O_V2; lia ]
                | cbn [edenot]; ev_xs; reflexivity ]
              | eapply (sc_rd_fld8 _ _ _ (wa_p w + O_V2 + 16));
                [ exact F22
                | rewrite (adenot_of_estart _ _ (wa_p w + O_V2 + 16));
                  [ reflexivity
                  | rewrite (estart_p H w _ _ OK (env_world_seed H w R (XS_S c))); unfold O_V2; lia
                  | unfold O_V2; lia ]
                | cbn [edenot]; ev_xs; reflexivity ]
              | (cbn [sc_denot]; ev_xs; cbn [edenot];
                 rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia;
                 first [ apply Z.eqb_neq | apply Z.leb_gt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.leb_le
                       | apply Z.ltb_lt | idtac ]; lia) ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_F091C HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_s1 H w _ OK (env_world_seed H w R (XS_S c))) as ES1.
    assert (FK : ffkeep w m M1).
    { pose proof (munch_sym _ m (s_log SSr) [(EVar WV_S1, 648, 656)] Hlf1 ltac:(vm_compute; reflexivity)) as MU.
      cbn [num_wins map] in MU. rewrite ES1 in MU.
      apply (ffkeep_munch w _ _ _ MU (wmono_mem_denot _ _ _)).
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
    eapply (KB msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1);
      first [ exact FK
            | (rewrite (HR1 _); cbn [sr_get s_regs nth];
               first [ reflexivity
                     | (eapply ev_add; [reflexivity | lia | lia])
                     | (cbn [edenot]; ev_xs; first [reflexivity | (rewrite u64_of_Z by lia; reflexivity)]) ]) ].
  Qed.

  Lemma pm_u2b_SR : forall (w : pmwA H) s LB LBs m mo c TB spal msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [OB_INST; OB_FIRST_WORD] TBL_F08EC [] TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf0920) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_F0920 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c))) ->
    0 < Zlen (t3b (c_v2 c)) ->
    (forall msF1 mo1 m1 R1, HS_F0950 H LINV w s LB LBs m1 mo1 c TB spal msF1 R1 F fc -> ffkeep w m m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c TB spal msF R F fc Q OK X0 KR0 VIS0 RF0 HT0 G3_0 G4_0 G10_0 HLEN KB.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (Hv2 & Hv2' & HD2 & Hlen2 & Hb2 & F20 & F21 & F22 & FE2).
    assert (Hbr2 : 0 < t3a (c_v2 c) /\ t3a (c_v2 c) mod 16 = 0 /\ t3a (c_v2 c) + 4 * t3c (c_v2 c) <= 2 ^ 63)
      by (destruct Hb2 as [[E1 E2]|(B1 & B2 & B3 & B4 & _)]; lia).
    assert (HTv : regs_tblX w [Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)))] R ((10%bv, EVar 41) :: RT_F0920)).
    { apply regs_tbl_cons.
      - rewrite G10_0. symmetry. exact (ev_xseed H w bvmap_empty [Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)))] 41%N _ eq_refl eq_refl).
      - exact (regs_tbl_ext w [] _ R RT_F0920 HT0 ltac:(vm_compute; reflexivity)). }
    eapply (pm_vstore_same2_gen H HHbp LINV LINV_frame 0xf0920 0xf0940 ((10%bv, EVar 41) :: RT_F0920) RT_F0940 [3; 4]%bv
              SL_F0920 KX_F0920 w s LB LBs m mo c _ _ _ TB spal msF R F fc Q OK X0).
    - apply tbl_incl. vm_compute. reflexivity.
    - intros E HE. apply Forall_cons; [| apply Forall_nil].
      exact (pmk_sh_p H LINV w s LB LBs m mo c _ _ _ TB spal E 248 OK X0 HE ltac:(lia)).
    - exact KR0.
    - exact VIS0.
    - exact RF0.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - exact HTv.
    - intros fuel. cbv zeta. intros ->.
      split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
      split; [vm_compute; reflexivity|].
      intros r0 Hr0. cbn [In] in Hr0.
      destruct Hr0 as [<- | [<- | []]]; vm_compute; reflexivity.
    - vm_compute. reflexivity.
    - intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 HK2 HT2 FK2.
      pm_goXT HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil kentry)
              (@Forall_nil kentry (kentry_ok asegs (Eseed R2 (wenv_vals w ++ [Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)))])) m2))
              20%nat [0xf0950] [false; false] 42%N [OB_INST; OB_FIRST_WORD] (@nil Z) (@nil Z) TBL_F08EC (@nil (Z * expr))
              RT_F0950.
      + split_scs.
        * cbn [sc_denot].
          rewrite (ev_and3_add _ 41%N (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c))) (-4)) by (first [ev_xs; reflexivity | lia]).
          cbn [edenot]. rewrite br_ne by (Z.div_mod_to_equations; lia).
          apply negb_false_iff. apply Z.eqb_eq. Z.div_mod_to_equations; lia.
        * cbn [sc_denot]. ev_xs. cbn [edenot]. rewrite br_ltu by lia. apply Z.ltb_ge. Z.div_mod_to_equations; lia.
      + intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HT3 HR3 Hlf3.
        pose proof (regs_tbl_restrict w [] _ R3 RT_F0950 HT3 ltac:(vm_compute; reflexivity)) as HT3'.
        apply (KB msF3 mo3 m2 R3); [| exact FK2].
        constructor.
        * exact X3.
        * exact KR3.
        * exact VIS3.
        * exact RF3.
        * exact HT3'.
        * rewrite (HR3 3%bv). change (PropExec.getr R2 3%bv = wa_gp w).
          rewrite (HK2 3%bv ltac:(cbn; tauto)). exact G3_0.
        * rewrite (HR3 4%bv). change (PropExec.getr R2 4%bv = wa_tp w).
          rewrite (HK2 4%bv ltac:(cbn; tauto)). exact G4_0.
        * rewrite (HR3 22%bv). cbn [sr_get s_regs nth].
          replace (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)) - 4) with (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)) + -4) by lia.
          eapply ev_add; [ev_xs; reflexivity | lia | Z.div_mod_to_equations; lia].
  Qed.

End U2B.
