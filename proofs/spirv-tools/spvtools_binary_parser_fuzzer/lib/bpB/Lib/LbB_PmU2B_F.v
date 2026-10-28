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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmLH LbB_PmVops LbB_PmU2K.

Definition RT_F0884 : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (18%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9120));
   (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 256)) (ELit 3)) (ELit SHBASE)); (20%bv, SH_FF);
   (21%bv, EAlu ALU_ADD (EVar WV_P) (ELit 248)); (22%bv, EAlu ALU_ADD (EVar WV_P) (ELit 256)); (23%bv, EVar WV_P);
   (25%bv, ELit SHBASE); (26%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 248)) (ELit 3)) (ELit SHBASE));
   (27%bv, EAlu ALU_ADD (EVar WV_P) (ELit 48))].

Definition TBL_F0884 : list (Z * expr) :=
  [(480, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 240)) (ELit 3)) (ELit SHBASE));
   (512, EAlu ALU_ADD (EVar WV_P) (ELit 88));
   (520, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 88)) (ELit 3)) (ELit SHBASE));
   (536, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 48)) (ELit 3)) (ELit SHBASE));
   (544, ELit 2305843009213693952); (560, EAlu ALU_ADD (EVar WV_P) (ELit 240)); (568, EVar WV_FF); (576, EVar WV_FF);
   (624, EAlu ALU_ADD (EVar WV_FF) (ELit 9040));
   (656, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 72)) (ELit 3)) (ELit SHBASE));
   (664, EAlu ALU_ADD (EVar WV_P) (ELit 72)); (680, EVar WV_FF)].

Definition TBL_F08EC : list (Z * expr) := TBL_F0884 ++ [(648, EVar WV_P)].

Definition RT_F08E8 : list (reg * expr) :=
  [(1%bv, ELit 0xf08ec); (2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1);
   (18%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9120));
   (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 256)) (ELit 3)) (ELit SHBASE)); (20%bv, SH_FF);
   (21%bv, EAlu ALU_ADD (EVar WV_P) (ELit 248)); (25%bv, ELit SHBASE);
   (26%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 248)) (ELit 3)) (ELit SHBASE));
   (27%bv, EAlu ALU_ADD (EVar WV_P) (ELit 48))].

Definition RT_F0950 : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (18%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9120));
   (19%bv, EVar WV_P); (20%bv, SH_FF); (21%bv, EAlu ALU_ADD (EVar WV_P) (ELit 248));
   (24%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9040)); (25%bv, ELit SHBASE);
   (26%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 248)) (ELit 3)) (ELit SHBASE));
   (27%bv, EAlu ALU_ADD (EVar WV_P) (ELit 48))].

Ltac pm_goXT HHH LINVF OK X KR VIS RF HT extra HKX fuel stops dirs nx ins' ks fks tbl' ftbl' RT' :=
  lazymatch type of X with PMXAT ?H ?LINV ?w ?s ?LB ?LBs ?m ?mo ?c ?ins ?tbl ?ftbl ?TB ?spal =>
  lazymatch type of HT with regs_tblX _ ?Xs ?R ?RT =>
  lazymatch type of VIS with _ = MS _ ?F (Z_to_bv 64 ?pc) ?fc _ _ _ =>
    let kn0 := constr:(pm_kn_base tbl ftbl ++ extra) in
    let fixes := eval vm_compute in (skipn (length kn0) (kn_fix3 30 fuel ins stops (SCR dirs [] []) pc (srs sr_id RT) kn0 nx)) in
    let kn := constr:(pm_kn_base tbl ftbl ++ (extra ++ fixes)) in
    let r := eval vm_compute in (sym_exec ASEGS fuel true stops (SCR dirs [] []) (SS pc (srs sr_id RT) [] kn nx) []) in
    lazymatch r with (?ss', ?scs, ?scr') =>
      let SSr := fresh "SSr" in pose (SSr := ss');
      eapply (pm_run H HHH LINV LINVF w s LB LBs m mo c ins tbl ftbl TB spal _ R F fc pc RT Xs kn fuel stops (SCR dirs [] []) nx SSr scs scr'
                ins' ks fks tbl' ftbl' RT' _ OK X KR VIS RF HT);
      [ vm_compute; reflexivity
      | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
      | unfold know_ok; apply Forall_app; split;
        [ eapply (pm_kn_base_ok H HHH LINV w s LB LBs m mo c ins tbl ftbl TB spal _ OK X (env_world_seed H w R Xs));
          vm_compute; reflexivity
        | apply Forall_app; split; [exact HKX | cbn [List.app]; pmk_list H HHH w OK X (env_world_seed H w R Xs)] ]
      | idtac
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | idtac ]
    end end end end.

Section U2B.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Record HS_F0950 (w : pmwA H) (s : as_St H) (LB LBs : list block) (m : mem) (mo : Model) (c : pmc) (TB : list block)
         (spal : Z) (msF : machine_state) (R F : bvmap 5 word) (fc : bv 32) : Prop := MKHS_F0950 {
    h50_x    : PMXAT H LINV w s LB LBs m mo c [OB_INST; OB_FIRST_WORD] TBL_F08EC [] TB spal;
    h50_kr   : as_AKREL H s (mkCfg msF mo);
    h50_vis  : as_VIS H s msF = MS R F (Z_to_bv 64 0xf0950) fc None m (seg_rom asegs);
    h50_rf   : rfull R;
    h50_rt   : regs_tbl w R RT_F0950;
    h50_gp   : PropExec.getr R 3%bv = wa_gp w;
    h50_tp   : PropExec.getr R 4%bv = wa_tp w;
    h50_back : PropExec.getr R 22%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)) - 4)
  }.

  Local Notation XS_F c := [Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c))); Z_to_bv 64 (t3a (c_v2 c) + 4 * t3c (c_v2 c));
                            Z_to_bv 64 (t3a (c_v2 c))] (only parsing).

  Lemma pm_u2b_F : forall (w : pmwA H) s LB LBs m mo c TB spal msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [OB_INST; OB_FIRST_WORD] TBL_F0884 [] TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf0884) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_F0884 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    Zlen (t3b (c_v2 c)) < t3c (c_v2 c) ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AANNOTATE_CC) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s LB LBs m1 mo1 c [OB_INST; OB_FIRST_WORD] TBL_F08EC [] TB spal ->
       regs_tbl w R1 RT_F08E8 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       PropExec.getr R1 10%bv = Z_to_bv 64 (t3a (c_v2 c)) ->
       PropExec.getr R1 11%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * t3c (c_v2 c)) ->
       PropExec.getr R1 12%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c))) ->
       PropExec.getr R1 13%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)) + 4) ->
       PropExec.getr R1 22%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)) + 4) ->
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
    assert (Hbr2 : 0 < t3a (c_v2 c) /\ t3a (c_v2 c) mod 16 = 0 /\ t3a (c_v2 c) + 4 * t3c (c_v2 c) <= 2 ^ 63)
      by (destruct Hb2 as [[E1 E2]|(B1 & B2 & B3 & B4 & _)]; lia).
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0
          (XS_F c) (@nil kentry) 200%nat [AANNOTATE_CC] [false; false; false; false; false] 41%N
          [OB_INST; OB_FIRST_WORD] [648] (@nil Z) TBL_F08EC (@nil (Z * expr)) RT_F08E8.
    { split_scs;
        first [ eapply (sc_rd_fld8 _ _ _ (wa_p w + O_V2));
                [ exact F20
                | rewrite (adenot_of_estart _ _ (wa_p w + O_V2));
                  [ reflexivity
                  | rewrite (estart_p H w _ _ OK (env_world_seed H w R (XS_F c))); unfold O_V2; lia
                  | unfold O_V2; lia ]
                | cbn [edenot]; ev_xs; reflexivity ]
              | eapply (sc_rd_fld8 _ _ _ (wa_p w + O_V2 + 8));
                [ exact F21
                | rewrite (adenot_of_estart _ _ (wa_p w + O_V2 + 8));
                  [ reflexivity
                  | rewrite (estart_p H w _ _ OK (env_world_seed H w R (XS_F c))); unfold O_V2; lia
                  | unfold O_V2; lia ]
                | cbn [edenot]; ev_xs; reflexivity ]
              | eapply (sc_rd_fld8 _ _ _ (wa_p w + O_V2 + 16));
                [ exact F22
                | rewrite (adenot_of_estart _ _ (wa_p w + O_V2 + 16));
                  [ reflexivity
                  | rewrite (estart_p H w _ _ OK (env_world_seed H w R (XS_F c))); unfold O_V2; lia
                  | unfold O_V2; lia ]
                | cbn [edenot]; ev_xs; reflexivity ]
              | (cbn [sc_denot]; ev_xs; cbn [edenot];
                 rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia;
                 first [ apply Z.eqb_neq | apply Z.leb_gt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.leb_le
                       | apply Z.ltb_lt | idtac ]; lia)
              | (cbn [sc_denot];
                 rewrite (ev_add _ 41%N (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c))) 4) by (first [ev_xs; reflexivity | lia]);
                 ev_xs; cbn [edenot]; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia;
                 first [ apply Z.eqb_neq | apply Z.leb_gt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.leb_le
                       | apply Z.ltb_lt | idtac ]; lia) ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_F08E8 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_s1 H w _ OK (env_world_seed H w R (XS_F c))) as ES1.
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

End U2B.
