(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMallocA AMalmys ANodeA7 ATransp ABudget ACor4x6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG1 APopG2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG1.APopDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pboth).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kShadowGapBeg, kHighShadowMapSize,
                        kAuCap, kFreeArraySize, kUserMapSize, kFreeArrayMapSize in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pop_mod {Clg : Ceiling} (A : AState) (md mdk : Model) : Prop :=   (* [comment removed for export] *)
  vm5_same (m_vmmaps md) (m_vmmaps mdk) /\ aledger_ AL_pboth (a_pl A) (a_reg A) (a_sec A) mdk /\ acover_ LPA (a_pl A) (a_sec A) (m_vmmaps mdk) /\
  alloc_top (m_vmmaps mdk) = alloc_ceiling /\ amd_frame md mdk /\ m_halted mdk = None.

Section Mod.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Lemma pop_mod_entry : pop_mod A md md.
  Proof. exact (entry_model A m md AI). Qed.
  Lemma pop_mod_sbm : forall mdk mdk', pop_mod A md mdk -> same_but_materialized mdk mdk' -> pop_mod A md mdk'.
  Proof. (intros mdk mdk'; (first [ intro dR_2; dand6 dR_2 as V L _ _ F HH | intros (V & L & _ & _ & F & HH) ]); intros SB). exact (s_model A m md AI mdk mdk' V L HH F SB). Qed.
End Mod.

(* [comment removed for export] *)
Section ModAny.
Context {Clg : Ceiling}.
  Lemma pop_mod_sbm_any : forall (A' : AState) md mdk mdk', pop_mod A' md mdk -> same_but_materialized mdk mdk' -> pop_mod A' md mdk'.
  Proof.
    intros A' md mdk mdk' (V & L & C & T & F & HH) SB. pose proof (same_but_materialized_vmmaps _ _ SB) as VM.
    split; [rewrite VM; exact V|]. split; [exact (aledger_sbm _ _ _ _ _ _ SB L)|]. split; [rewrite VM; exact C|]. split; [rewrite VM; exact T|].
    split; [| rewrite (same_but_materialized_halted _ _ SB); exact HH].
    (first [ pose proof ((same_but_materialized_frame _ _ SB)) as dR; dand18 dR as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 Xr | pose proof (same_but_materialized_frame _ _ SB) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & Xr) ]).
    unfold amd_frame in *. rewrite X1, X2, X4, X5, X6, X7, X8, X17. decompose [and] F. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.
  Lemma pop_mod_grow : forall (A A' : AState) md mdk beg len,
    a_pl A' = a_pl A -> a_sec A' = a_sec A -> 0 <= len ->
    (forall c', 1 <= c' <= 31 ->
       (rg_mapped_user (a_reg A' c') = rg_mapped_user (a_reg A c') \/
        (region_beg (a_sb A) c' + rg_mapped_user (a_reg A c') = beg /\ rg_mapped_user (a_reg A' c') = rg_mapped_user (a_reg A c') + len)) /\
       (rg_mapped_fa (a_reg A' c') = rg_mapped_fa (a_reg A c') \/
        (region_beg (a_sb A) c' + kFreeArrayOffset + rg_mapped_fa (a_reg A c') = beg /\ rg_mapped_fa (a_reg A' c') = rg_mapped_fa (a_reg A c') + len))) ->
    pop_mod A md mdk -> lazy_free (m_vm_lazy mdk) beg (beg + len) -> pop_mod A' md mdk.
  Proof.
    intros A A' md mdk beg len EP ES LEN GROW (V & L & C & T & F & HH) LZ. unfold pop_mod. rewrite EP, ES.
    refine (conj V (conj _ (conj C (conj T (conj F HH))))).
    apply (aledger_upd _ _ (a_reg A) _ _ _ L). pose proof (aledger_lzfree _ _ _ _ _ L) as (Z1 & Z2 & Z3).
    refine (conj Z1 (conj Z2 _)). intros c' Hc. destruct (Z3 c' Hc) as [ZU ZF]. unfold a_sb in GROW. destruct (GROW c' Hc) as [GU GF]. split.
    - destruct GU as [E|[B E]]; rewrite E; [exact ZU|]. apply (lazy_free_join _ _ beg); [rewrite <- B; exact ZU|].
      replace (region_beg (p_sb (a_pl A)) c' + (rg_mapped_user (a_reg A c') + len)) with (beg + len) by lia. exact LZ.
    - destruct GF as [E|[B E]]; rewrite E; [exact ZF|]. apply (lazy_free_join _ _ beg); [rewrite <- B; exact ZF|].
      replace (region_beg (p_sb (a_pl A)) c' + kFreeArrayOffset + (rg_mapped_fa (a_reg A c') + len)) with (beg + len) by lia. exact LZ.
  Qed.
End ModAny.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Node.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Variables (md1 : Model) (H0 HL0 : hull) (E0 : Z) (beg len : Z).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable A' : AState.
  Hypothesis EPL : a_pl A' = a_pl A.
  Hypothesis ESEC : a_sec A' = a_sec A.
  Hypothesis PM1 : pop_mod A' md md1.
  Hypothesis HI1 : MInv H0 HL0 E0 md1.
  Hypothesis RANGE : a_sb A <= beg /\ beg + len <= a_sb A + kSpaceSize + 4096 /\ beg mod 4096 = 0 /\ len mod 4096 = 0 /\ 0 < len.
  Hypothesis BR : E0 + len + hull_bytes HL0 <= p_tlim (a_pl A).   (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (M1 : mem) (Tg : TSet).

  Let W0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.
  Let SBF := sb_facts A W0.
  Let BEGW : bv_unsigned (wz beg) = beg. Proof. apply unsigned_lit. pose proof SBF. pose proof RANGE. kung_all. lia. Qed.
  Let LENW : bv_unsigned (wz len) = len. Proof. apply unsigned_lit. pose proof SBF. pose proof RANGE. kung_all. lia. Qed.
  Let PRU : page_round_up_Z len = len.
  Proof.
    unfold page_round_up_Z, page_size. destruct RANGE as (_ & _ & _ & L1 & L0).
    pose proof (Z_div_mod_eq_full len 4096) as E. rewrite L1 in E.
    replace (len + 4096 - 1) with ((len / 4096) * 4096 + 4095) by lia. rewrite Z.div_add_l by lia. replace (4095 / 4096) with 0 by reflexivity. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem pop_node :
    (* [comment removed for export] *)
    (let md2 := commit_model (wz 50) (wz beg) (wz len) false md1 in
     MInv H0 HL0 (E0 + len) md2 -> pop_mod A' md md2 -> lazy_free (m_vm_lazy md2) beg (beg + len) ->
     srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz beg) (wz len) (wz 3) (wz 50) (wz (-1)) (wz 0) a6 (wz 222)
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz mmap_after_pc) fc None (apply_zeros M1 [(wz beg, wz len)]) (seg_rom rsegs)) md2) Tg) ->
    srealizes rsegs (mkCfg (MSsvc (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz beg) (wz len) (wz 3) (wz 50) (wz (-1)) (wz 0) a6 (wz 222)
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz mmap_ecall_pc) (wz 222) fc None M1 (seg_rom rsegs)) md1)
               Tg.
  Proof.
    intros GRANT. destruct PM1 as (V1 & LED1 & COV1 & TOP1 & AMD1 & HH1). rewrite EPL, ESEC in LED1, COV1.
    match goal with |- srealizes _ (mkCfg ?ms _) _ => set (ms1 := ms) end.
    assert (A0E : ms_gpr ms1 0 = wz beg) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (A1E : ms_gpr ms1 1 = wz len) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (PRU1 : page_round_up_Z (bv_unsigned (ms_gpr ms1 1)) = len) by (rewrite A1E, LENW; exact PRU).
    eapply (srz_mmap_fixed_rw_contained_nf rsegs ms1 md1 (wz 222) (wz 50) Tg HH1 eq_refl eq_refl).
    - unfold mmap_fixed_args. subst ms1. rewrite !ms_gpr_MSsvc. simp_regs. split; [| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity].
      intros E. apply (f_equal bv_unsigned) in E. rewrite LENW, unsigned_lit in E by lia. destruct RANGE as (_ & _ & _ & _ & L0). lia.
    - exact fixed_rw_shape_plain.
    - rewrite PRU1, A0E. eapply (c_gate A m md AI); eassumption.
    - unfold fixed_contained. rewrite PRU1, A0E. eapply (c_contained A m md AI); eassumption.
    - rewrite PRU1, A0E. eapply (c_budget A m md AI); eassumption.
    - rewrite !PRU1, !A0E. subst ms1.
      rewrite advance_apply_MSsvc, mkR_set_a0, lit_add_lit. change (mmap_ecall_pc + 4) with mmap_after_pc.
      cbn [apply_writes apply_unmaps].
      apply GRANT.
      + eapply (c_minv A m md AI); eassumption.
      + unfold pop_mod. rewrite EPL, ESEC. split; [eapply c_vm5; eassumption|]. split; [eapply (c_ledger A m md AI); eassumption|].
        split; [eapply (c_cover A m md AI); eassumption|]. split; [eapply (c_ceil A m md AI); eassumption|].
        split; [eapply c_amd; eassumption| eapply c_halted; eassumption].
      + eapply (c_lzfree_new A m md AI); eassumption.
  Qed.
End Node.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Switch.
Context {Clg : Ceiling}.
  Variables (H0 H1 : hull) (beg len : Z) (M v1 : mem).
  Hypothesis HLE : hull_le H0 H1.
  (* [comment removed for export] *)
  Hypothesis NEWH : forall x, in_hullb H1 x = true -> in_hullb H0 x = false -> (beg <= x < beg + len) \/ (sh beg <= x < sh beg + len / 8).
  (* [comment removed for export] *)
  Hypothesis FEB : kHighMemBeg <= beg /\ beg + len <= 2^47 /\ 0 < len.
  Hypothesis SHB : kLowShadowMapBeg <= sh beg /\ sh beg + len / 8 <= kHighMemBeg.
  Hypothesis CL1 : forall a, hidc H0 a = true -> v1 a = None.
  Hypothesis MI1 : mem_inv rsegs v1.

  #[warnings="-notation-for-abbreviation"] Local Notation M1 := (munrestrict (hidc H0) M v1).
  #[warnings="-notation-for-abbreviation"] Local Notation M2 := (apply_zeros (munrestrict (hidc H0) M v1) [(wz beg, wz len)]).
  #[warnings="-notation-for-abbreviation"] Local Notation v2 := (mrestrict (hidc H1) (apply_zeros (munrestrict (hidc H0) M v1) [(wz beg, wz len)])).
  #[warnings="-notation-for-abbreviation"] Local Notation Wg := [(beg, beg + len); (sh beg, sh beg + len / 8)].

  Lemma sw_zspec : forall x : word, M2 x = if in_range beg len x then Some (Z_to_bv 8 0) else M1 x.
  Proof. intros x. change (Z_to_bv 64 beg) with (wa beg). apply apply_zeros_spec; kung_all; lia. Qed.

  Lemma sw_munch : munch Wg v1 v2.
  Proof.
    apply (restrict_grow_munch_le H0 H1 Wg HLE) with (full := M).
    - intros x X1 X0 OUT. cbn [outside] in OUT. (first [ dand3 OUT as O1 O2 _ | destruct OUT as (O1 & O2 & _) ]). destruct (NEWH x X1 X0) as [N|N]; [exact (O1 N)| exact (O2 N)].
    - exact CL1.
    - intros a OUT. rewrite sw_zspec. cbn [outside] in OUT. destruct OUT as (O1 & _). unfold in_range.
      replace ((beg <=? bv_unsigned a) && (bv_unsigned a <? beg + len)) with false; [reflexivity|].
      symmetry. apply andb_false_iff. destruct (Z_lt_le_dec (bv_unsigned a) beg) as [l|g]; [left; apply Z.leb_gt; exact l| right; apply Z.ltb_ge; lia].
  Qed.

  Lemma sw_wmono : wmono rsegs v1 v2.
  Proof.
    apply (restrict_grow_wmono_le H0 H1 HLE v1 _ CL1).
    intros a V0 NZ. rewrite sw_zspec. destruct (in_range beg len a); [discriminate|]. unfold munrestrict. rewrite V0. exact NZ.
  Qed.

  (* [comment removed for export] *)

  Lemma sw_mem_inv : mem_inv rsegs v2.
  Proof.
    intros a bb Hab. unfold mrestrict in Hab. destruct (hidc H1 a) eqn:V1; [discriminate|]. rewrite sw_zspec in Hab.
    destruct (ro_addr rsegs a) eqn:RO; [| reflexivity]. exfalso. pose proof (proj1 (pa_ro_addr_iff _) RO) as ROr.
    destruct (in_range beg len a) eqn:IR.
    - unfold in_range in IR. apply andb_true_iff in IR as [I1 I2]. apply Z.leb_le in I1. kung_all. lia.
    - unfold munrestrict in Hab. destruct (hidc H0 a) eqn:V0; [| rewrite (MI1 a bb Hab) in RO; discriminate].
      unfold hidc in V0, V1. apply negb_true_iff in V0. apply negb_false_iff in V1.
      destruct (NEWH _ V1 V0) as [N|N]; kung_all; lia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis VISN : forall x, beg <= x < beg + len -> in_hullb H1 x = true.
  Lemma sw_hidden : forall a, hidc H1 a = true -> M2 a = M a.
  Proof.
    intros a Ha. rewrite sw_zspec. destruct (in_range beg len a) eqn:IR.
    - exfalso. unfold in_range in IR. apply andb_true_iff in IR as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
      unfold hidc in Ha. rewrite (VISN _ (conj I1 I2)) in Ha. discriminate.
    - unfold munrestrict. rewrite (hidc_grow_le H0 H1 HLE a Ha). reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma sw_zero : forall x, beg <= x < beg + len -> v2 (wz x) = Some (Z_to_bv 8 0).
  Proof.
    intros x Hx. unfold mrestrict. assert (U : bv_unsigned (wz x) = x) by (apply unsigned_lit; kung_all; lia).
    unfold hidc. rewrite U, (VISN x Hx). cbn [negb]. rewrite sw_zspec. unfold in_range. rewrite U.
    replace ((beg <=? x) && (x <? beg + len)) with true; [reflexivity|]. symmetry. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Switch.
