(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_VecT LbB_NtStmt LbB_NtK LbB_NtD LbB_NtI LbB_NtI2 LbB_NtI3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_HEmpD LbB_HEmpI LbB_HEmpS LbB_HEmpI3.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section NtI4.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.
  Variables (gp tp s0 s4 ty wd enc : word) (S1 : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj key v408 v576 v624 : Z) (ents : list ent).
  Variables (bl bc lo B shi : Z) (m0 : mem) (mo0 : Model).

  Abbreviation IPREx := (IPRE H tp ty enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0).
  Abbreviation QIx := (QI H gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0).
  Abbreviation ISTATEx := (ISTATE H gp tp s0 s4 wd S1 obj).

  Ltac sckH HV := eapply ckT_srl; [evs; rewrite ?w_addm, ?w_and, ?w_remu by lia; rewrite HV; rewrite w_add by lia; reflexivity | lia | lia].
  Ltac shdjF := unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in *; sc_shdjX.
  Ltac fsc Rdb Flb HV :=
    lazymatch goal with
    | |- sc_denot _ _ _ (SCDisj (SA (EAlu ALU_SRL _ _) _) _ _ _) => shdjF
    | |- sc_denot _ _ _ (SCDisj _ _ (SA (EAlu ALU_SRL _ _) _) _) => shdjF
    | |- sc_denot _ _ _ (SCDisj _ _ _ _) => unfold apart in *; sc_djX
    | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_SRL _ _) _) _) => sc_shdjX
    | |- sc_denot _ _ _ (SCBr _ _ (EAlu ALU_AND (EVar 35) _) _) => sc_andE
    | |- sc_denot _ _ _ (SCBr true BC_EQ (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_AND _ _) _) _) _) => sckH HV
    | |- sc_denot _ _ _ (SCBr true BC_EQ (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_REMU _ _) _) _) _) => sckH HV
    | |- sc_denot _ _ _ (SCReadBase (SA (EAlu ALU_ADD (EMd _ _ _) _) _) _ _ _) => exact Rdb
    | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_ADD (EMd _ _ _) _) _) _) => exact Flb
    | |- sc_denot _ _ _ (SCBr _ _ _ _) => first [sckT | sc_br]
    | |- sc_denot _ _ _ (SCReadBase _ _ _ _) => match goal with H : cellw _ _ _ _ _ |- _ => sc_rd H end
    | |- sc_denot _ _ _ (SCFlat _ _) => sc_fl
    end.

  Lemma stage_ins_front : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y28 y29 : word)
      (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z) (ents2 : list ent) (rehashed : bool) (j584 : word),
    ISTATEx msF s m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y28 y29 p bc2 (hmod key bc2) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPREx s mo m errv' LB' LBm' p bl2 bc2 ents2 rehashed j584 ->
    cell8 ASEGS m (bl2 + 8 * hmod key bc2) 0 ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y28 y29
      errv' LB' LBm' p bl2 bc2 ents2 rehashed j584 VIS FRZ KR IP Cb0.
    unfold ISTATE in VIS.
    pose proof IP as IP0.
    destruct IP0 as (MP & WS & NS & SPL & SPH & V1 & V2 & V3 & MI & ST & ERR & RA & TPV & ACL & LOS & LFO & U2 & SH2 & PERM2 & BC2 & LOAD & KR32
                     & AD & WR & P0 & P1 & P16 & PO & PA & NC & ADP & CR3 & CR4 & RH & PE & PM & OWN & XP & RF & AC & S0 & AL).
    pose proof (LbB_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3).
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    pose proof (u_obj_lo U2) as Ho0. pose proof (u_obj_hi U2) as Ho1. pose proof (u_obj_al U2) as Hoal.
    pose proof (u_bl_lo U2 BC2) as Hbl0. pose proof (u_bl_hi U2) as Hbl1. pose proof (u_bl_obj U2 BC2) as Hblo.
    pose proof (u_bl_al U2) as Hbla.
    pose proof (LbB_HFind.BSEQ_boundA bc2 (u_bseq U2)) as BCR.
    destruct (u_hdr U2) as [Cbl Cbc Cp1 Csz Cmlf Cdef].
    destruct SH2 as [SHb SHn]. unfold HStmts.t3a, HStmts.t3b, HStmts.t3c in SHb, SHn. cbn [Datatypes.fst Datatypes.snd] in SHb, SHn.
    assert (INBL : In (bl2, 8 * bc2) (umap_blocks 32 bl2 bc2 ents2))
      by (unfold umap_blocks; apply in_app_iff; left; destruct (Z.eqb_spec bc2 0); [lia | left; reflexivity]).
    pose proof (PA bl2 (8 * bc2) INBL) as PBL.
    assert (INM : forall q n, In (q, n) (lbl LBm') -> exists qi, In (qi, q, n) LBm' /\ In (qi, q, n) LB'
                   /\ 0 < q /\ q mod 16 = 0 /\ AIMG_TOP <= q /\ q + n <= aceil /\ aapp q n).
    { intros q n Hq. destruct (lbl_in_inv LBm' q n Hq) as (qi & Qi).
      assert (QiL : In (qi, q, n) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact Qi).
      pose proof (ah_blocks H HH _ _ _ _ RH QiL) as (B0 & B16 & Bn & BI & BC & BF & BA).
      cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in B0, B16, Bn, BI, BC, BF, BA.
      exists qi. repeat split; assumption. }
    destruct (INM p 32 (Permutation_in _ (Permutation_sym PM) (or_introl eq_refl))) as (qp & QPm & QPl & _ & _ & PIM & PCE & PAPP).
    destruct (INM bl2 (8 * bc2) (Permutation_in _ (Permutation_sym PM) (or_intror INBL))) as (qbl & QBm & QBl & _ & _ & BIM & BCE & BAPP).
    pose proof (lb_own_In LBm' m _ OWN QPm) as WRP. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in WRP.
    pose proof (lb_own_In LBm' m _ OWN QBm) as WRB. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in WRB.
    unfold AIMG_TOP in OB3, PIM, BIM.
    set (h := hmod key bc2) in *.
    assert (Hh : 0 <= h < bc2) by (subst h; unfold hmod; apply Z.mod_pos_bound; lia).
    assert (GZO : gz m obj 40) by (intros i Hi; eapply sh0_of_addressable; [exact AD | change (8 * (40 / 8)) with 40; lia]).
    assert (GZP : gz m p 32) by (intros i Hi; eapply sh0_of_addressable; [exact ADP | change (8 * (32 / 8)) with 32; lia]).
    assert (GZB : gz m bl2 (8 * bc2)) by (apply LbB_HEmpI.gzA; [exact (SHb BC2) | rewrite Z.mul_comm, Z_mod_mult; reflexivity]).
    assert (WRp8 : wr_at asegs m p 8) by exact (LbB_HEmpD.wr_at_subE m p 32 p 8 WRP ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (WRs : wr_at asegs m (obj + 16) 8) by exact (LbB_HEmpD.wr_at_subE m obj 40 (obj + 16) 8 WR ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (WRk : wr_at asegs m (bl2 + 8 * h) 8) by exact (LbB_HEmpD.wr_at_subE m bl2 (8 * bc2) (bl2 + 8 * h) 8 WRB ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold cell8 in Cb0, Cbl, Cp1.
    destruct WS as (W584 & W600 & W632 & W656).
    destruct NS as (R408 & R576 & R616 & R624 & R648).
    remember (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 (Z_to_bv 64 SHBASE) y16 y17
                  y18 y19 s4 y21 (Z_to_bv 64 h) (Z_to_bv 64 p) wd (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 24))
                  (Z_to_bv 64 bc2) y28 y29 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60))) as R eqn:HR0.
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    destruct ents2 as [|[fn [k1 v1]] rest].
    - pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 p; Z_to_bv 64 obj; Z_to_bv 64 bc2; Z_to_bv 64 h;
                          Z_to_bv 64 bl2; Z_to_bv 64 0; Z_to_bv 64 0]).
      assert (HR : regs_ok E srI R).
      { unfold srI. apply regs_ok_srs; [apply regs_ok_seed|].
        repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]).
        apply Forall_nil. }
      assert (Rdb : sc_denot ASEGS m E (SCReadBase (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 36)) (EVar 37)) 0) 8 false (EVar 38))).
      { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cb0); [cbn; lia | evs; rewrite w_mul, w_add, v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
      assert (Flb : sc_denot ASEGS m E (SCFlat (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 36)) (EVar 37)) 0) (ELit 8))).
      { eapply (sc_flat _ _ _ _ (8 * h + bl2)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | cbn; lia | lia | cbn; lia]. }
      assert (HK : know_ok asegs E m (kn_fix 20 [E_END] SCR_F0 E_INS srI KNF 50)).
      { kn_eval. unfold know_ok.
        kni_tac obj S1 p W632 W584 R616 R648.
        apply Forall_cons. { eapply kwr_of_wr_at; [exact WRp8 | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
        apply Forall_cons. { eapply kwr_of_wr_at; [exact WRs | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
        apply Forall_cons. { eapply kwr_of_wr_at; [exact WRk | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
        do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R E_INS m (seg_rom asegs) HR HK 80%nat [E_END] SCR_F0 50%N.
      { split_scs; fsc Rdb Flb (eq_refl 0). }
      clear HK.
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      assert (MU1 : munch [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * h, bl2 + 8 * h + 8)] m M1).
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?w_mul, ?w_add, ?u64_of_Z by lia;
                                    cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
        apply Forall_nil. }
      assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
      assert (MG1 : mem_grows m M1) by (subst M1; apply mem_denot_grows).
      assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
      assert (ST1 : stk asegs M1 lo (S1 + 672)) by (subst M1; apply stk_mem_denot; exact ST).
      assert (Cs1 : rw_cells asegs M1 (obj + 16) [C8 (Z_to_bv 64 p)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRs).
      assert (Ck1 : rw_cells asegs M1 (bl2 + 8 * h) [C8 (alu64 ALU_ADD (Z_to_bv 64 obj) (Z_to_bv 64 16))]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRk).
      rewrite w_add in Ck1 by lia.
      readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
      assert (Cn1 : rw_cells asegs M1 p [C8 (Z_to_bv 64 0)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRp8).
      rreg HR' 9%bv G9. rreg HR' 15%bv G15. rreg HR' 23%bv G23.
      rewrite G9, G15, G23 in HRe.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply (front_post H HH gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0
                s msF1 mo1 m M1 F fc) with (W := [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * h, bl2 + 8 * h + 8)]) (ents2 := []) (j584 := j584);
        [ exact VIS1 | exact FRZ | exact KR1 | | exact MU1 | exact WM1 | exact MG1 | exact MI1 | exact ST1 | | exact Cn1 | exact Cs1 | ].
      + destruct IP as (MPx & IPr). split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP1] | exact IPr].
      + apply Forall_cons; [left; reflexivity|]. apply Forall_cons; [right; left; reflexivity|].
        apply Forall_cons; [right; right; cbn; lia | apply Forall_nil].
      + intros i Hi. destruct (Z.eq_dec i h) as [->|Hne].
        * exists (obj + 16). split.
          -- exact (cellw8_of_rw_cells M1 (bl2 + 8 * h) (obj + 16) Ck1 ltac:(lia) ltac:(lia)).
          -- right; right. split; [reflexivity|]. split; [discriminate|]. reflexivity.
        * destruct (u_bkt U2 i Hi) as (b' & Cb' & Hok'). exists b'. split.
          -- eapply cellw_agree; [exact Cb' | | lia | cbn; lia]. intros j Hj.
             unfold apart in PBL, Hblo. apply MU1. rewrite u64_of_Z by lia. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I].
          -- destruct Hok' as [H0 | [Hn | (Hs & Hne' & Hi')]]; [left; exact H0 | cbn in Hn; destruct Hn | exfalso; apply Hne'; reflexivity].
    - destruct (u_node U2 fn k1 v1 (or_introl eq_refl)) as (_ & Fn0 & Fn1 & Fn16 & Ck & _ & K1R & _ & FnO & FnB).
      specialize (FnB BC2).
      assert (INF : In (fn, 32) (umap_blocks 32 bl2 bc2 ((fn, (k1, v1)) :: rest)))
        by (unfold umap_blocks; apply in_app_iff; right; left; reflexivity).
      pose proof (PA fn 32 INF) as PFN.
      assert (GZF : gz m fn 32)
        by (intros i Hi; eapply sh0_of_addressable; [exact (SHn fn k1 v1 (or_introl eq_refl)) | change (8 * (32 / 8)) with 32; lia]).
      unfold cell8 in Ck.
      pose proof (LbB_HEmpI3.bseq_land_boundE bc2 (u_bseq U2)) as LB2.
      set (idx2 := hmod k1 bc2).
      assert (IDX2 : 0 <= idx2 < bc2) by (subst idx2; unfold hmod; apply Z.mod_pos_bound; lia).
      pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 p; Z_to_bv 64 obj; Z_to_bv 64 bc2; Z_to_bv 64 h;
                          Z_to_bv 64 bl2; Z_to_bv 64 0; Z_to_bv 64 fn; Z_to_bv 64 k1]).
      assert (HR : regs_ok E srI R).
      { unfold srI. apply regs_ok_srs; [apply regs_ok_seed|].
        repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]).
        apply Forall_nil. }
      assert (Rdb : sc_denot ASEGS m E (SCReadBase (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 36)) (EVar 37)) 0) 8 false (EVar 38))).
      { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cb0); [cbn; lia | evs; rewrite w_mul, w_add, v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
      assert (Flb : sc_denot ASEGS m E (SCFlat (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 36)) (EVar 37)) 0) (ELit 8))).
      { eapply (sc_flat _ _ _ _ (8 * h + bl2)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | cbn; lia | lia | cbn; lia]. }
      destruct (LbB_HEmpI3.bseq_pow2E bc2 (u_bseq U2) BC2) as [(Hb2 & Hl0) | (Hb3 & Hl1)].
      + assert (LAND : Z.land bc2 (bc2 + -1) = 0) by (replace (bc2 + -1) with (bc2 - 1) by lia; exact Hl0).
        assert (HV : Z.land k1 (bc2 + -1) = idx2) by (subst idx2; unfold hmod; rewrite Hb2; change (2 + -1) with 1; apply LbB_HEmpI3.land_1E).
        assert (HK : know_ok asegs E m (kn_fix 20 [E_J2] SCR_F2 E_INS srI KNF 50)).
        { kn_eval. unfold know_ok.
          kni_tac obj S1 p W632 W584 R616 R648.
          apply Forall_cons. { eapply kwr_of_wr_at; [exact WRp8 | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
          apply Forall_cons. { eapply kwr_of_wr_at; [exact WRs | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
          apply Forall_cons. { eapply kwr_of_wr_at; [exact WRk | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
          do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
          know_tac. }
        xrun_at (PropExec.mkFP F fc) asegs R E_INS m (seg_rom asegs) HR HK 100%nat [E_J2] SCR_F2 50%N.
        { split_scs; fsc Rdb Flb HV. }
        clear HK.
        lazymatch type of Hlf with log_flat _ ?lg =>
          lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
            change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
        assert (MU1 : munch [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * h, bl2 + 8 * h + 8)] m M1).
        { subst M1. apply munch_mem_denot; [exact Hlf|].
          repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?w_mul, ?w_add, ?u64_of_Z by lia;
                                      cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
          apply Forall_nil. }
        assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
        assert (MG1 : mem_grows m M1) by (subst M1; apply mem_denot_grows).
        assert (ST1 : stk asegs M1 lo (S1 + 672)) by (subst M1; apply stk_mem_denot; exact ST).
        assert (Cs1 : rw_cells asegs M1 (obj + 16) [C8 (Z_to_bv 64 p)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRs).
        assert (Ck1 : rw_cells asegs M1 (bl2 + 8 * h) [C8 (alu64 ALU_ADD (Z_to_bv 64 obj) (Z_to_bv 64 16))]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRk).
        rewrite w_add in Ck1 by lia.
        readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
        assert (Cn1 : rw_cells asegs M1 p [C8 (Z_to_bv 64 fn)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRp8).
        rreg HR' 9%bv G9. rreg HR' 10%bv G10. rreg HR' 12%bv G12. rreg HR' 15%bv G15. rreg HR' 23%bv G23.
        assert (G10' : getr R' 10%bv = Z_to_bv 64 idx2) by (rewrite G10; rewrite w_addm, w_and by lia; rewrite HV; reflexivity).
        rewrite G9, G10', G12, G15, G23 in HRe.
        eapply (front_j2 H HH gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0
                  s msF mo m M1 F fc R R');
          [ exact VIS | exact FHF | exact Hms | exact HRe | exact FRZ | exact KR | exact IP | exact MU1 | exact WM1 | exact MG1
          | exact ST1 | exact Cn1 | exact Cs1 | exact Ck1 ].
      + assert (LANDNZ : Z.land bc2 (bc2 + -1) <> 0) by (replace (bc2 + -1) with (bc2 - 1) by lia; exact Hl1).
        destruct (Z_lt_le_dec k1 bc2) as [Hlt | Hge].
        * assert (HV : k1 = idx2) by (subst idx2; unfold hmod; rewrite Z.mod_small by lia; reflexivity).
          assert (HK : know_ok asegs E m (kn_fix 20 [E_J2] SCR_F3 E_INS srI KNF 50)).
          { kn_eval. unfold know_ok.
            kni_tac obj S1 p W632 W584 R616 R648.
            apply Forall_cons. { eapply kwr_of_wr_at; [exact WRp8 | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
            apply Forall_cons. { eapply kwr_of_wr_at; [exact WRs | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
            apply Forall_cons. { eapply kwr_of_wr_at; [exact WRk | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
            do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
            know_tac. }
          xrun_at (PropExec.mkFP F fc) asegs R E_INS m (seg_rom asegs) HR HK 100%nat [E_J2] SCR_F3 50%N.
          { split_scs; fsc Rdb Flb (eq_refl 0). }
          clear HK.
          lazymatch type of Hlf with log_flat _ ?lg =>
            lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
              change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
          assert (MU1 : munch [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * h, bl2 + 8 * h + 8)] m M1).
          { subst M1. apply munch_mem_denot; [exact Hlf|].
            repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?w_mul, ?w_add, ?u64_of_Z by lia;
                                        cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
            apply Forall_nil. }
          assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
          assert (MG1 : mem_grows m M1) by (subst M1; apply mem_denot_grows).
          assert (ST1 : stk asegs M1 lo (S1 + 672)) by (subst M1; apply stk_mem_denot; exact ST).
          assert (Cs1 : rw_cells asegs M1 (obj + 16) [C8 (Z_to_bv 64 p)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRs).
          assert (Ck1 : rw_cells asegs M1 (bl2 + 8 * h) [C8 (alu64 ALU_ADD (Z_to_bv 64 obj) (Z_to_bv 64 16))]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRk).
          rewrite w_add in Ck1 by lia.
          readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
          assert (Cn1 : rw_cells asegs M1 p [C8 (Z_to_bv 64 fn)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRp8).
          rreg HR' 9%bv G9. rreg HR' 10%bv G10. rreg HR' 12%bv G12. rreg HR' 15%bv G15. rreg HR' 23%bv G23.
          assert (G10' : getr R' 10%bv = Z_to_bv 64 idx2) by (rewrite G10, HV; reflexivity).
          rewrite G9, G10', G12, G15, G23 in HRe.
          eapply (front_j2 H HH gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0
                    s msF mo m M1 F fc R R');
            [ exact VIS | exact FHF | exact Hms | exact HRe | exact FRZ | exact KR | exact IP | exact MU1 | exact WM1 | exact MG1
            | exact ST1 | exact Cn1 | exact Cs1 | exact Ck1 ].
        * assert (HV : k1 mod bc2 = idx2) by reflexivity.
          assert (HK : know_ok asegs E m (kn_fix 20 [E_J2] SCR_F4 E_INS srI KNF 50)).
          { kn_eval. unfold know_ok.
            kni_tac obj S1 p W632 W584 R616 R648.
            apply Forall_cons. { eapply kwr_of_wr_at; [exact WRp8 | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
            apply Forall_cons. { eapply kwr_of_wr_at; [exact WRs | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
            apply Forall_cons. { eapply kwr_of_wr_at; [exact WRk | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
            do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
            know_tac. }
          xrun_at (PropExec.mkFP F fc) asegs R E_INS m (seg_rom asegs) HR HK 100%nat [E_J2] SCR_F4 50%N.
          { split_scs; fsc Rdb Flb HV. }
          clear HK.
          lazymatch type of Hlf with log_flat _ ?lg =>
            lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
              change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
          assert (MU1 : munch [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * h, bl2 + 8 * h + 8)] m M1).
          { subst M1. apply munch_mem_denot; [exact Hlf|].
            repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?w_mul, ?w_add, ?u64_of_Z by lia;
                                        cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
            apply Forall_nil. }
          assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
          assert (MG1 : mem_grows m M1) by (subst M1; apply mem_denot_grows).
          assert (ST1 : stk asegs M1 lo (S1 + 672)) by (subst M1; apply stk_mem_denot; exact ST).
          assert (Cs1 : rw_cells asegs M1 (obj + 16) [C8 (Z_to_bv 64 p)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRs).
          assert (Ck1 : rw_cells asegs M1 (bl2 + 8 * h) [C8 (alu64 ALU_ADD (Z_to_bv 64 obj) (Z_to_bv 64 16))]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRk).
          rewrite w_add in Ck1 by lia.
          readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
          assert (Cn1 : rw_cells asegs M1 p [C8 (Z_to_bv 64 fn)]) by (subst M1; unfold apart in PO, PBL, Hblo; rwc_new Hlf WRp8).
          rreg HR' 9%bv G9. rreg HR' 10%bv G10. rreg HR' 12%bv G12. rreg HR' 15%bv G15. rreg HR' 23%bv G23.
          assert (G10' : getr R' 10%bv = Z_to_bv 64 idx2) by (rewrite G10; rewrite w_remu by lia; rewrite HV; reflexivity).
          rewrite G9, G10', G12, G15, G23 in HRe.
          eapply (front_j2 H HH gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0
                    s msF mo m M1 F fc R R');
            [ exact VIS | exact FHF | exact Hms | exact HRe | exact FRZ | exact KR | exact IP | exact MU1 | exact WM1 | exact MG1
            | exact ST1 | exact Cn1 | exact Cs1 | exact Ck1 ].
  Qed.

  Lemma stage_ins : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y28 y29 : word)
      (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z) (ents2 : list ent) (rehashed : bool) (j584 : word),
    ISTATEx msF s m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y28 y29 p bc2 (hmod key bc2) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPREx s mo m errv' LB' LBm' p bl2 bc2 ents2 rehashed j584 ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y28 y29
      errv' LB' LBm' p bl2 bc2 ents2 rehashed j584 VIS FRZ KR IP.
    pose proof IP as IP0.
    destruct IP0 as (MP & WS & NS & SPL & SPH & V1 & V2 & V3 & MI & ST & ERR & RA & TPV & ACL & LOS & LFO & U2 & SH2 & PERM2 & BC2 & LOAD & KR32 & _).
    pose proof (LbB_HFind.BSEQ_boundA bc2 (u_bseq U2)) as BCR.
    assert (Hh : 0 <= hmod key bc2 < bc2) by (unfold hmod; apply Z.mod_pos_bound; lia).
    destruct (u_bkt U2 (hmod key bc2) Hh) as (b & Cb & Hok).
    destruct (Z.eq_dec b 0) as [Hb0 | Hbnz].
    - subst b. exact (stage_ins_front s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y28 y29
                        errv' LB' LBm' p bl2 bc2 ents2 rehashed j584 VIS FRZ KR IP Cb).
    - exact (stage_ins_pn H HH gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0
               s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y28 y29
               errv' LB' LBm' p bl2 bc2 ents2 rehashed j584 b VIS FRZ KR IP Cb Hok Hbnz).
  Qed.
End NtI4.
