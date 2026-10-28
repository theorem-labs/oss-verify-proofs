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
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_VecT LbB_NtStmt LbB_NtK LbB_NtD LbB_NtI.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_HEmpD LbB_HEmpI LbB_HEmpS LbB_HEmpI2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E_J2 : Z := 0xf5c80.

Definition srT : list expr := srs sr_id [(23%bv, EVar 32); (10%bv, EVar 33); (12%bv, EVar 34); (15%bv, ELit SHBASE)].
Definition KNT : list kentry := [KWr (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 33)) (EVar 34)) 0) (ELit 8)].
Definition SCR_T := SCR [true; true] [] [].

Lemma ev_notT : forall E e x, edenot E e = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  edenot E (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) e) (ELit (-1))) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
  intros E e x He Hx. cbn [edenot]. rewrite He. apply bv_eq. cbn [alu64 alu mul_div].
  rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small x) by lia.
  rewrite Z.mul_mod_idemp_l, Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia.
  replace (2 ^ 64 - 1 - x) with (-1 * x + -1 + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Section NtI2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.
  Variables (gp tp s0 s4 ty wd enc : word) (S1 : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj key v408 v576 v624 : Z) (ents : list ent).
  Variables (bl bc lo B shi : Z) (m0 : mem) (mo0 : Model).

  Abbreviation IPREx := (IPRE H tp ty enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0).
  Abbreviation QIx := (QI H gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0).

  Lemma front_post : forall (s : as_St H) (msF : machine_state) (mo : Model) (m M2 : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y22 y25 y27 y28 y29 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z) (ents2 : list ent) (rehashed : bool) (j584 : word) (W : list (Z * Z)),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 (Z_to_bv 64 SHBASE) y16 y17
                             y18 y19 s4 y21 y22 (Z_to_bv 64 p) wd y25 (Z_to_bv 64 (obj + 24)) y27 y28 y29
                             (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) y31)
                        F (Z_to_bv 64 E_END) fc None M2 (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPREx s mo m errv' LB' LBm' p bl2 bc2 ents2 rehashed j584 ->
    munch W m M2 -> wmono asegs m M2 -> mem_grows m M2 -> mem_inv asegs M2 -> stk asegs M2 lo (S1 + 672) ->
    Forall (fun iv => iv = (p, p + 8) \/ iv = (obj + 16, obj + 24) \/ (bl2 <= fst iv /\ snd iv <= bl2 + 8 * bc2)) W ->
    rw_cells asegs M2 p [C8 (Z_to_bv 64 (hdaddr ents2))] -> rw_cells asegs M2 (obj + 16) [C8 (Z_to_bv 64 p)] ->
    (forall i, 0 <= i < bc2 -> exists b', cell8 ASEGS M2 (bl2 + 8 * i) b' /\ bucket_ok obj bc2 ((p, (key, (0, 0, 0))) :: ents2) i b') ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m M2 F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y22 y25 y27 y28 y29 y31
      errv' LB' LBm' p bl2 bc2 ents2 rehashed j584 W VIS FRZ KR IP MU2 WM2 MG2 MI2 ST2 FW Cn2 Cs2 CB2.
    eapply (ins_post H HH gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0
              s msF mo m M2 F fc) with (l1 := []) (l2 := ents2) (W := W);
      [ exact VIS | exact FRZ | exact KR | exact IP | exact MU2 | exact WM2 | exact MG2 | exact MI2 | exact ST2
      | | exact Cn2 | exact Cs2 | exact CB2 ].
    eapply Forall_impl; [|exact FW]. intros iv [-> | [-> | Hiv]].
    - left; reflexivity.
    - right; left. cbn [LbB_NtK.lasta]. f_equal; lia.
    - right; right; exact Hiv.
  Qed.

  Lemma front_tail : forall (s : as_St H) (msF : machine_state) (mo : Model) (m M1 : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y11 y13 y14 y16 y17 y18 y19 y21 y22 y25 y27 y28 y29 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z) (fn k1 : Z) (v1 : Z * Z * Z) (rest : list ent) (rehashed : bool) (j584 : word),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (hmod k1 bc2)) y11
                             (Z_to_bv 64 bl2) y13 y14 (Z_to_bv 64 SHBASE) y16 y17 y18 y19 s4 y21 y22 (Z_to_bv 64 p) wd y25
                             (Z_to_bv 64 (obj + 24)) y27 y28 y29 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) y31)
                        F (Z_to_bv 64 E_J2) fc None M1 (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPREx s mo m errv' LB' LBm' p bl2 bc2 ((fn, (k1, v1)) :: rest) rehashed j584 ->
    munch [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * hmod key bc2, bl2 + 8 * hmod key bc2 + 8)] m M1 -> wmono asegs m M1 ->
    mem_grows m M1 -> mem_inv asegs M1 -> stk asegs M1 lo (S1 + 672) ->
    rw_cells asegs M1 p [C8 (Z_to_bv 64 fn)] -> rw_cells asegs M1 (obj + 16) [C8 (Z_to_bv 64 p)] ->
    rw_cells asegs M1 (bl2 + 8 * hmod key bc2) [C8 (Z_to_bv 64 (obj + 16))] ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m M1 F fc y1 y5 y6 y7 y11 y13 y14 y16 y17 y18 y19 y21 y22 y25 y27 y28 y29 y31
      errv' LB' LBm' p bl2 bc2 fn k1 v1 rest rehashed j584 VIS FRZ KR IP MU1 WM1 MG1 MI1 ST1 Cn1 Cs1 Cb1.
    pose proof IP as IP0.
    destruct IP0 as (MP & WS & NS & SPL & SPH & V1 & V2 & V3 & MI & ST & ERR & RA & TPV & ACL & LOS & LFO & U2 & SH2 & PERM2 & BC2
                     & LOAD & KR32 & AD & WR & P0 & P1 & P16 & PO & PA & NC & ADP & CR3 & CR4 & RH & PE & PM & OWN & XP & RF & AC & S0 & AL).
    pose proof (LbB_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3).
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (u_obj_lo U2) as Ho0. pose proof (u_obj_hi U2) as Ho1.
    pose proof (u_bl_lo U2 BC2) as Hbl0. pose proof (u_bl_hi U2) as Hbl1. pose proof (u_bl_obj U2 BC2) as Hblo. unfold apart in Hblo.
    pose proof (u_bl_al U2) as Hbla.
    pose proof (LbB_HFind.BSEQ_boundA bc2 (u_bseq U2)) as BCR.
    destruct (u_node U2 fn k1 v1 (or_introl eq_refl)) as (_ & Fn0 & Fn1 & _ & _ & _ & K1R & _ & _ & _).
    destruct SH2 as [SHb SHn]. unfold HStmts.t3a, HStmts.t3b, HStmts.t3c in SHb, SHn. cbn [Datatypes.fst Datatypes.snd] in SHb, SHn.
    assert (INBL : In (bl2, 8 * bc2) (umap_blocks 32 bl2 bc2 ((fn, (k1, v1)) :: rest)))
      by (unfold umap_blocks; apply in_app_iff; left; destruct (Z.eqb_spec bc2 0); [lia | left; reflexivity]).
    assert (PBL : p + 32 <= bl2 \/ bl2 + 8 * bc2 <= p) by (pose proof (PA bl2 (8 * bc2) INBL) as Hap; unfold apart in Hap; exact Hap).
    destruct (lbl_in_inv LBm' bl2 (8 * bc2) (Permutation_in _ (Permutation_sym PM) (or_intror INBL))) as (qbl & QBm).
    pose proof (lb_own_In LBm' m _ OWN QBm) as WRB. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in WRB.
    pose proof PO as PO'. unfold apart in PO'.
    set (idx := hmod key bc2) in *.
    assert (IDX : 0 <= idx < bc2) by (subst idx; unfold hmod; apply Z.mod_pos_bound; lia).
    set (idx2 := hmod k1 bc2) in *.
    assert (IDX2 : 0 <= idx2 < bc2) by (subst idx2; unfold hmod; apply Z.mod_pos_bound; lia).

    assert (QBL : In (qbl, bl2, 8 * bc2) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact QBm).
    pose proof (ah_blocks H HH _ _ _ _ RH QBL) as (_ & _ & _ & BIM & BCE & _ & BAPP).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in BIM, BCE, BAPP.
    destruct (lbl_in_inv LBm' p 32 (Permutation_in _ (Permutation_sym PM) (or_introl eq_refl))) as (qp & QPm).
    assert (QPL : In (qp, p, 32) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact QPm).
    pose proof (ah_blocks H HH _ _ _ _ RH QPL) as (_ & _ & _ & PIM & PCE & _ & PAPP).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in PIM, PCE, PAPP. unfold AIMG_TOP in PIM, BIM.

    assert (FAPP1 : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv)
                      [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * idx, bl2 + 8 * idx + 8)]).
    { unfold aapp, aapp_lo, aapp_hi in VA, PAPP, BAPP.
      apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia | apply Forall_nil]. }
    assert (GZB1 : gz M1 bl2 (8 * bc2)).
    { apply LbB_HEmpI.gzA; [| rewrite Z.mul_comm, Z_mod_mult; reflexivity].
      eapply addressable_transport; [exact (SHb BC2) | exact MU1 | exact WM1 | apply LbB_HEmpI.dsh_app; [exact FAPP1 | lia | lia | lia]]. }
    assert (WRK : wr_at asegs M1 (bl2 + 8 * idx2) 8)
      by exact (LbB_HEmpD.wr_at_subE M1 bl2 (8 * bc2) (bl2 + 8 * idx2) 8 (wr_at_wmono _ _ _ _ WRB WM1) ltac:(lia) ltac:(lia) ltac:(lia)).
    remember (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) (Z_to_bv 64 idx2) y11
                  (Z_to_bv 64 bl2) y13 y14 (Z_to_bv 64 SHBASE) y16 y17 y18 y19 s4 y21 y22 (Z_to_bv 64 p) wd y25
                  (Z_to_bv 64 (obj + 24)) y27 y28 y29 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 idx2; Z_to_bv 64 bl2]).
    assert (HR : regs_ok E srT R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]).
      apply Forall_nil. }
    assert (HK : know_ok asegs E M1 (kn_fix 20 [E_END] SCR_T E_J2 srT KNT 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WRK | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R E_J2 M1 (seg_rom asegs) HR HK 20%nat [E_END] SCR_T 50%N.
    { split_scs; first [ sckT | sc_shdj
                       | eapply ckT_geu; [LbB_HEmpS.sck_ev | eapply ev_notT; [LbB_HEmpS.sck_ev | lia] | lia | lia]
                       | eapply (sc_flat _ _ _ _ (8 * idx2 + bl2)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | cbn; lia | lia | cbn; lia] ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E M1 lg) in Hms; set (M2 := mem_denot E M1 lg) in Hms end end.
    set (bk2 := bl2 + 8 * idx2) in *.
    assert (MU12 : munch [(bk2, bk2 + 8)] M1 M2).
    { subst M2. apply munch_mem_denot; [exact Hlf|].
      apply Forall_cons; [|apply Forall_nil]. cbn [e_addr e_width]. unfold estart; evs. rewrite ?w_mul, ?w_add, ?u64_of_Z by lia.
      cbn [inside a_off Z.of_nat Pos.of_succ_nat Pos.succ]. left. lia. }
    assert (WM12 : wmono asegs M1 M2) by (subst M2; apply wmono_mem_denot).
    assert (MG12 : mem_grows M1 M2) by (subst M2; apply mem_denot_grows).
    assert (MI2 : mem_inv asegs M2) by exact (msteps_mem_inv asegs _ _ Hms MI1).
    assert (ST2 : stk asegs M2 lo (S1 + 672)) by (subst M2; apply stk_mem_denot; exact ST1).
    assert (Cb2 : rw_cells asegs M2 bk2 [C8 (Z_to_bv 64 p)]) by (subst M2; rwc_new Hlf WRK).
    assert (Cn2 : rw_cells asegs M2 p [C8 (Z_to_bv 64 fn)])
      by (eapply rw_cells_transport; [exact Cn1 | exact MU12 | exact WM12 | cbn [disjoint_from cells_size csize Z.of_nat]; subst bk2; lia]).
    assert (Cs2 : rw_cells asegs M2 (obj + 16) [C8 (Z_to_bv 64 p)])
      by (eapply rw_cells_transport; [exact Cs1 | exact MU12 | exact WM12 | cbn [disjoint_from cells_size csize Z.of_nat]; subst bk2; lia]).
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 23%bv G23. rreg HR' 15%bv G15. rewrite G23, G15 in HRe.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (front_post s msF1 mo1 m M2 F fc) with
      (W := [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * idx, bl2 + 8 * idx + 8); (bk2, bk2 + 8)]) (ents2 := (fn, (k1, v1)) :: rest);
      [ exact VIS1 | exact FRZ | exact KR1 | | | | | | | | | | ].
    - destruct IP as (MPx & IPr). split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP1] | exact IPr].
    - exact (LbB_HEmpI2.munch_app_trans [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * idx, bl2 + 8 * idx + 8)] [(bk2, bk2 + 8)] m M1 M2 MU1 MU12).
    - exact (wmono_trans asegs _ _ _ WM1 WM12).
    - exact (mem_grows_trans _ _ _ MG1 MG12).
    - exact MI2.
    - exact ST2.
    - apply Forall_cons; [left; reflexivity|]. apply Forall_cons; [right; left; reflexivity|].
      apply Forall_cons; [right; right; cbn; lia|]. apply Forall_cons; [right; right; cbn; subst bk2; lia | apply Forall_nil].
    - exact Cn2.
    - exact Cs2.
    - intros i Hi. destruct (Z.eq_dec i idx2) as [->|Hne2].
      + exists p. split; [exact (cellw8_of_rw_cells M2 bk2 p Cb2 ltac:(lia) ltac:(lia))|]. right; left; left; reflexivity.
      + destruct (Z.eq_dec i idx) as [->|Hne1].
        * exists (obj + 16). split.
          -- assert (C1 : rw_cells asegs M2 (bl2 + 8 * idx) [C8 (Z_to_bv 64 (obj + 16))]).
             { eapply rw_cells_transport; [exact Cb1 | exact MU12 | exact WM12 |]. cbn [disjoint_from cells_size csize Z.of_nat]. subst bk2. lia. }
             exact (cellw8_of_rw_cells M2 (bl2 + 8 * idx) (obj + 16) C1 ltac:(lia) ltac:(lia)).
          -- right; right. split; [reflexivity|]. split; [discriminate|]. reflexivity.
        * destruct (u_bkt U2 i Hi) as (b' & Cb' & Hok'). exists b'. split.
          -- eapply cellw_agree; [exact Cb' | | lia | cbn; lia]. intros j Hj.
             rewrite (MU12 (Z_to_bv 64 (bl2 + 8 * i + j))) by (rewrite u64_of_Z by lia; cbn [outside]; subst bk2; split; [lia | exact I]).
             apply MU1. rewrite u64_of_Z by lia. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I].
          -- destruct Hok' as [H0 | [Hn | (Hs & Hne & Hi')]]; [left; exact H0 | right; left; right; exact Hn |].
             exfalso. apply Hne2. rewrite Hi'. reflexivity.
  Qed.
End NtI2.
