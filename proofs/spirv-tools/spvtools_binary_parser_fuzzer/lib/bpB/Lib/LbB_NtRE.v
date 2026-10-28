(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts HRehashModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_VecT LbB_NtStmt LbB_NtK LbB_NtRK LbB_NtD LbB_NtI LbB_NtI4 LbB_NtRL.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_TopKit LbB_HEmpD LbB_HEmpI LbB_HEmpS LbB_HEmpR LbB_HEmpI3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit LbB_RwSem LbB_RwStm LbB_NtRLR.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma firstn_repeat8 : forall {X : Type} (x : X) (j k : nat), (j + 8 <= k)%nat -> firstn 8 (skipn j (repeat x k)) = repeat x 8.
Proof.
  intros X x j k Hk. revert k Hk. induction j as [|j IH]; intros k Hk.
  - cbn [skipn]. destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try lia. reflexivity.
  - destruct k as [|k]; [lia|]. cbn [repeat skipn]. apply IH. lia.
Qed.

Lemma rw_cells_CB_to_C8 : forall m A bs w, rw_cells asegs m A [CB 8 bs] -> bs = le8 w -> rw_cells asegs m A [C8 w].
Proof.
  intros m A bs w [[Hwf HB] HW] E. subst bs. split; [split|].
  - cbn. split; exact I.
  - cbn [cells_bytes cbytes] in HB |- *. exact HB.
  - cbn [cells_size csize] in HW |- *. exact HW.
Qed.

Lemma zero_cell8 : forall m p (k : nat) (i : Z), rw_cells asegs m p [CB k (poison_bytes k 0)] -> 0 <= p -> 0 <= i -> 8 * i + 8 <= Z.of_nat k ->
  HRep.cellw asegs m (p + 8 * i) 8 0.
Proof.
  intros m p k i RC Hp Hi Hk.
  destruct (rw_cells_CB_split asegs m p k (Z.to_nat (8 * i)) _ RC ltac:(lia)) as [_ R2].
  rewrite Z2Nat.id in R2 by lia.
  destruct (rw_cells_CB_split asegs m (p + 8 * i) _ 8 _ R2 ltac:(lia)) as [R3 _].
  apply cellw8_of_rw_cells; [| lia | lia]. eapply rw_cells_CB_to_C8; [exact R3|].
  unfold poison_bytes. rewrite firstn_repeat8 by lia. reflexivity.
Qed.

Lemma disjoint_from_nodes : forall (l : list (Z * (Z * (Z * Z * Z)))) a k,
  (forall e, In e l -> a + k <= HRehashModel.addr (Z * Z * Z) e \/ HRehashModel.addr (Z * Z * Z) e + 8 <= a) ->
  disjoint_from (map (fun e => (HRehashModel.addr (Z * Z * Z) e, HRehashModel.addr (Z * Z * Z) e + 8)) l) a k.
Proof.
  intros l a k. induction l as [|e l IH]; intros Hd; cbn; [exact I|].
  split; [apply Hd; left; reflexivity | apply IH; intros e' He'; apply Hd; right; exact He'].
Qed.

Lemma Forall_nodes : forall (P : Z * Z -> Prop) (l : list (Z * (Z * (Z * Z * Z)))),
  (forall e, In e l -> P (HRehashModel.addr (Z * Z * Z) e, HRehashModel.addr (Z * Z * Z) e + 8)) ->
  Forall P (map (fun e => (HRehashModel.addr (Z * Z * Z) e, HRehashModel.addr (Z * Z * Z) e + 8)) l).
Proof. intros P l Hl. apply Forall_map. apply Forall_forall. intros e He. exact (Hl e He). Qed.

Definition keptXI : list reg := [1; 2; 3; 4; 8; 9; 14; 18; 19; 20; 21; 23; 24; 25; 26; 30; 31]%bv.

Ltac in_keptRE := try unfold keptXI; try unfold keptX; cbn [In]; repeat (first [left; reflexivity | right]).

Lemma x_step : forall (F : bvmap 5 word) (fc : bv 32) (R : bvmap 5 word) (M : mem) (S1 obj key nn : Z),
  getr R 9%bv = Z_to_bv 64 S1 -> getr R 18%bv = Z_to_bv 64 key ->
  fldA M (S1 + 616) 8 SHBASE -> fldA M (S1 + 664) 8 ((obj + 8) / 8 + SHBASE) -> fldA M (S1 + 632) 8 (obj + 8) ->
  fldA M (obj + 8) 8 nn -> sh0 M (obj + 8) ->
  0 < obj -> obj + 40 <= 2 ^ 47 -> obj mod 8 = 0 -> 2 <= nn <= 2 ^ 25 -> 0 <= key < 2 ^ 32 ->
  2 ^ 45 <= S1 -> S1 + 672 <= 2 ^ 47 ->
  0 <= Z.land nn (nn + -1) < 2 ^ 31 -> nn = 2 \/ Z.land nn (nn - 1) <> 0 ->
  exists R', CatSim.msteps asegs (@PropExec.mkst (PropExec.mkFP F fc) R (Z_to_bv 64 R_EXIT) M (seg_rom asegs))
                                 (@PropExec.mkst (PropExec.mkFP F fc) R' (Z_to_bv 64 E_INS) M (seg_rom asegs))
    /\ getr R' 15%bv = Z_to_bv 64 SHBASE /\ getr R' 22%bv = Z_to_bv 64 (hmod key nn) /\ getr R' 27%bv = Z_to_bv 64 nn
    /\ (forall r, In r keptXI -> getr R' r = getr R r).
Proof.
  intros F fc R M S1 obj key nn X9 X18 F616 F664 F632 FN SH Ho0 Ho1 Hoal Hn Hk SPL SPH HLB Hcase.
  set (fx := PropExec.mkFP F fc).
  assert (HR : regs_ok (x_E R S1 nn obj key) x_sr R) by (unfold x_E, x_sr; rw_seedB).
  destruct Hcase as [Hn2 | Hnp].
  - subst nn.
    assert (HK : know_ok bsegs (x_E R S1 2 obj key) M x_P_knF) by (unfold x_E; knowB).
    assert (HS : scs_denot bsegs M (x_E R S1 2 obj key) x_P_scs) by (unfold x_P_scs, x_E; split_scs; sc_closeB).
    destruct (x_P_run fx R M (seg_rom asegs) S1 2 obj key HS HR HK) as (R' & HR' & HL & Hms).
    change bsegs with asegs in Hms. cbn [s_regs s_log s_pc mem_denot x_P_ss] in Hms.
    exists R'. split; [exact Hms|].
    unfold x_E in HR, HR'. rreg HR' 15%bv G15. rreg HR' 22%bv G22. rreg HR' 27%bv G27.
    split; [rewrite G15; reflexivity|]. split; [| split; [rewrite G27; reflexivity | keptB HR HR' keptXI]].
    rewrite G22. wnormB. f_equal. unfold hmod. rewrite Z.land_comm. exact (LbB_HEmpI3.land_1E key).
  - assert (Hnp' : Z.land nn (nn + -1) <> 0) by (replace (nn + -1) with (nn - 1) by lia; exact Hnp).
    destruct (Z.lt_ge_cases key nn) as [Hlt | Hge].
    + assert (HK : know_ok bsegs (x_E R S1 nn obj key) M x_L_knF) by (unfold x_E; knowB).
      assert (HS : scs_denot bsegs M (x_E R S1 nn obj key) x_L_scs) by (unfold x_L_scs, x_E, scs_denot; apply Forall_cons; [sc_brB | apply Forall_cons; [sc_brB | apply Forall_nil]]).
      destruct (x_L_run fx R M (seg_rom asegs) S1 nn obj key HS HR HK) as (R' & HR' & HL & Hms).
      change bsegs with asegs in Hms. cbn [s_regs s_log s_pc mem_denot x_L_ss] in Hms.
      exists R'. split; [exact Hms|].
      unfold x_E in HR, HR'. rreg HR' 15%bv G15. rreg HR' 22%bv G22. rreg HR' 27%bv G27.
      split; [rewrite G15; reflexivity|]. split; [| split; [rewrite G27; reflexivity | keptB HR HR' keptXI]].
      rewrite G22. unfold hmod. rewrite Z.mod_small by lia. reflexivity.
    + assert (HK : know_ok bsegs (x_E R S1 nn obj key) M x_M_knF) by (unfold x_E; knowB).
      assert (HS : scs_denot bsegs M (x_E R S1 nn obj key) x_M_scs) by (unfold x_M_scs, x_E, scs_denot; apply Forall_cons; [sc_brB | apply Forall_cons; [sc_brB | apply Forall_nil]]).
      destruct (x_M_run fx R M (seg_rom asegs) S1 nn obj key HS HR HK) as (R' & HR' & HL & Hms).
      change bsegs with asegs in Hms. cbn [s_regs s_log s_pc mem_denot x_M_ss] in Hms.
      exists R'. split; [exact Hms|].
      unfold x_E in HR, HR'. rreg HR' 15%bv G15. rreg HR' 22%bv G22. rreg HR' 27%bv G27.
      split; [rewrite G15; reflexivity|]. split; [| split; [rewrite G27; reflexivity | keptB HR HR' keptXI]].
      rewrite G22. rewrite w_remu by lia. reflexivity.
Qed.
Section NtRE.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHB : asan_rt_hyps_bp H.
  Let HH : asan_rt_hyps H := rt_bp_base H HHB.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.
  Variables (gp tp s0 s4 ty wd enc : word) (S1 : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj key v408 v576 v624 : Z) (ents : list ent).
  Variables (bl bc lo B shi : Z) (m0 : mem) (mo0 : Model).
  Variables (LBe : list block).
  #[local] Notation n := (bseq_next bc).
  #[local] Notation addr := (HRehashModel.addr (Z * Z * Z)).
  #[local] Notation hkey := (HRehashModel.hkey (Z * Z * Z)).
  #[local] Notation sent := (obj + 16).

  Hypothesis U0 : umapx MI_A 32 (nval32 ASEGS) (lbl LBe) m0 obj bl bc ents.
  Hypothesis Hlast : bc <> BSEQ_LAST.
  Hypothesis OCE : obj + 40 <= aceil.
  Hypothesis LFO : map_live_frame LF obj.
  Hypothesis ACL : aceil <= lo.
  Hypothesis LOS : lo <= S1.
  Hypothesis TPV : tp = Z_to_bv 64 ATP.
  Hypothesis KR32 : 0 <= key < 2 ^ 32.
  Hypothesis ZLEN : Zlength ents + 1 < 2 ^ 24.

  #[local] Opaque bseq_next.
  Abbreviation IPREx := (IPRE H tp ty enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0).
  Abbreviation QIx := (QI H gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0).

  Lemma stage_post : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y15 y16 y17 y19 y21 y22 y28 y29 : word) (errv : word) (LB' LBn : list block) (pid qn : bptr) (p pn : Z)
      (j584 : word),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 (Z_to_bv 64 (2 ^ 64 - 1 - p)) (Z_to_bv 64 p)
                             y15 y16 y17 (Z_to_bv 64 key) y19 s4 y21 y22 (Z_to_bv 64 pn) wd (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 24))
                             (Z_to_bv 64 n) y28 y29 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60)))
                        F (Z_to_bv 64 R_MS) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    WSLOTS ty enc S1 obj m j584 (Z_to_bv 64 (pn / 8 + SHBASE)) -> nt_slots m S1 obj v408 v576 v624 ->
    2 ^ 45 <= S1 -> S1 + 672 <= 2 ^ 47 -> (0 <= v408 < 2 ^ 64 /\ 0 <= v576 < 2 ^ 64 /\ 0 <= v624 < 2 ^ 64) ->
    mem_inv asegs m -> stk asegs m lo (S1 + 672) -> rw_cells asegs m (errno_addr tp) [C4 errv] -> as_rauxv_ok H m B ->
    (forall e, In e ents -> agree_on m0 m (addr e) 32) -> agree_on m0 m (obj + 16) 24 ->
    cell8 ASEGS m obj p -> cell8 ASEGS m (obj + 8) n ->
    rw_cells asegs m p [CB (Z.to_nat (8 * n)) (poison_bytes (Z.to_nat (8 * n)) 0)] ->
    addressable m p (8 * n) -> addressable m obj 40 -> (forall e, In e ents -> addressable m (addr e) 32) ->
    wr_at asegs m obj 40 ->
    as_RHEAP H s LB' m -> Permutation LB' (LB0 ++ (pid, p, 8 * n) :: (qn, pn, 32) :: LBn) ->
    Permutation (lbl LBn) (map (fun e : ent => (addr e, 32)) ents) ->
    lb_own ((pid, p, 8 * n) :: (qn, pn, 32) :: LBn) m ->
    xpres H LB0 S1 (nt_X S1 obj) m0 m -> as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_AL H s >= as_AL H sk0 - ICM (8 * n) ->

    rw_cells asegs m pn [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
    addressable m pn 32 -> (bc = 0 \/ Zlength ents = bc) ->
    as_SR H QIx (mkCfg msF mo).
  Proof using HHB U0 Hlast OCE LFO ACL LOS TPV KR32 ZLEN.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y15 y16 y17 y19 y21 y22 y28 y29 errv LB' LBn pid qn p pn j584
      VIS FRZ KR MP WS NS SPL SPH VR MI ST ERR RA NODES HDR24 Cbl Cbc ZER ADP ADH ADN WRH RH PE PM OWN XP RF AC S0 AL PNC PNA BCZ.
    destruct (LbB_HEmpR.bseq_next_factsE bc (u_bseq U0) Hlast) as (HnB & Hbcn & Hn28 & Hncase).
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U0)) as Hbc0.
    assert (Hn0 : 0 < n) by lia.
    assert (Hn2 : 2 <= n <= 2 ^ 25) by (destruct Hncase as [[_ E] | [E _]]; lia).
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (u_obj_lo U0) as Ho0. pose proof (u_obj_hi U0) as Ho1. pose proof (u_obj_al U0) as Hoal.
    pose proof (LbB_HEmpD.obj_place H HH LF obj m RF LFO) as (OAPP & OB1 & OB2 & OB3).
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).

    assert (INP : In (pid, p, 8 * n) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; left; reflexivity).
    assert (INQ : In (qn, pn, 32) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; right; left; reflexivity).
    pose proof (ah_blocks H HH _ _ _ _ RH INP) as (Hp0 & Hp16 & _ & HpI & HpC & HpF & HpA).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Hp0, Hp16, HpI, HpC, HpF, HpA.
    pose proof (ah_blocks H HH _ _ _ _ RH INQ) as (Hq0 & Hq16 & _ & HqI & HqC & HqF & HqA).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Hq0, Hq16, HqI, HqC, HqF, HqA.
    assert (HPO : apart p (8 * n) obj 40) by (unfold apart; unfold AFS_SIZE in *; clear - HpF OB1 OB2 Hn0; lia).
    assert (HQO : apart pn 32 obj 40) by (unfold apart; unfold AFS_SIZE in *; clear - HqF OB1 OB2; lia).

    assert (INN : forall e, In e ents -> exists q, In (q, addr e, 32) LBn /\ In (q, addr e, 32) LB').
    { intros e He. destruct (lbl_in_inv LBn (addr e) 32 (Permutation_in _ (Permutation_sym PM) (in_map (fun e0 : ent => (addr e0, 32)) _ _ He))) as (q & Hq).
      exists q. split; [exact Hq|]. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. right. right. right. exact Hq. }
    pose proof (ah_nodup H HH _ _ _ RH) as NDB.
    assert (ND1 : List.NoDup (map blk_id ((pid, p, 8 * n) :: (qn, pn, 32) :: LBn))).
    { assert (ND0 : List.NoDup (map blk_id (LB0 ++ (pid, p, 8 * n) :: (qn, pn, 32) :: LBn)))
        by (eapply Permutation_NoDup; [apply Permutation_map; exact PE | exact NDB]).
      rewrite map_app in ND0. exact (NoDup_app_remove_l _ _ ND0). }
    cbn [map blk_id Datatypes.fst] in ND1.
    apply NoDup_cons_iff in ND1. destruct ND1 as (Hni1 & ND2).
    apply NoDup_cons_iff in ND2. destruct ND2 as (Hni2 & _).
    assert (BD : forall q A N, In (q, A, N) LBn -> (p + 8 * n + 16 <= A \/ A + N + 16 <= p) /\ (pn + 32 + 16 <= A \/ A + N + 16 <= pn)).
    { intros q A N Hq.
      assert (HqL : In (q, A, N) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; right; right; exact Hq).
      assert (Hin : In q (map blk_id LBn)) by (change q with (blk_id (q, A, N)); apply in_map; exact Hq).
      split.
      - assert (Hne : pid <> q) by (intros <-; apply Hni1; right; exact Hin).
        pose proof (ah_disj H HH _ _ _ _ _ RH INP HqL Hne) as D. cbn [blk_addr blk_size blk_id Datatypes.fst Datatypes.snd] in D. exact D.
      - assert (Hne : qn <> q) by (intros <-; apply Hni2; exact Hin).
        pose proof (ah_disj H HH _ _ _ _ _ RH INQ HqL Hne) as D. cbn [blk_addr blk_size blk_id Datatypes.fst Datatypes.snd] in D. exact D. }
    assert (HQP : pn + 32 + 16 <= p \/ p + 8 * n + 16 <= pn).
    { assert (Hne : pid <> qn) by (intros <-; apply Hni1; left; reflexivity).
      pose proof (ah_disj H HH _ _ _ _ _ RH INP INQ Hne) as D. cbn [blk_addr blk_size blk_id Datatypes.fst Datatypes.snd] in D. lia. }
    assert (HPN : forall e, In e ents -> apart p (8 * n) (addr e) 32).
    { intros e He. destruct (INN e He) as (q & HqN & _). destruct (BD q _ _ HqN) as (D & _). unfold apart. lia. }
    assert (HQN : forall e, In e ents -> apart pn 32 (addr e) 32).
    { intros e He. destruct (INN e He) as (q & HqN & _). destruct (BD q _ _ HqN) as (_ & D). unfold apart. lia. }
    assert (NAPP : forall e, In e ents -> aapp (addr e) 32).
    { intros e He. destruct (INN e He) as (q & _ & HqL). pose proof (ah_blocks H HH _ _ _ _ RH HqL) as (_ & _ & _ & _ & _ & _ & BA). exact BA. }
    assert (NCE : forall e, In e ents -> AIMG_TOP <= addr e /\ addr e + 32 <= aceil).
    { intros e He. destruct (INN e He) as (q & _ & HqL). pose proof (ah_blocks H HH _ _ _ _ RH HqL) as (_ & _ & _ & QI & QC & _).
      cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in QI, QC. lia. }
    assert (WRP : wr_at asegs m p (8 * n)) by exact (lb_own_In _ m _ OWN (or_introl eq_refl)).
    assert (WRN : forall e, In e ents -> wr_at asegs m (addr e) 32).
    { intros e He. destruct (INN e He) as (q & HqN & _). exact (lb_own_In _ m _ OWN (or_intror (or_intror HqN))). }

    destruct (u_hdr U0) as [_ _ Cp10 Csz0 Cmlf0 _].
    assert (Cp1 : cell8 ASEGS m sent (hdaddr ents)) by (eapply cellw_agree; [exact Cp10 | eapply agree_on_sub; [exact HDR24 | lia | cbn; lia] | lia | cbn; lia]).
    assert (CH : chain ASEGS m ents).
    { apply lnk_chain. eapply lnk_agree; [apply lnk_chain; exact (u_chain U0) | |].
      - intros a Ha. eapply agree_on_sub; [exact (NODES a Ha) | lia | cbn; lia].
      - intros a Ha. destruct (ent_facts _ _ _ _ _ _ a U0 Ha) as (Ha0 & Ha1 & _). lia. }
    assert (HASH : forall e, In e ents -> cell8 ASEGS m (addr e + 8) (hkey e)).
    { intros e He. destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _).
      destruct (u_node U0 (addr e) (hkey e) (snd (snd e)) ltac:(destruct e as [q [k v]]; exact He)) as (_ & _ & _ & _ & C8k & _).
      eapply cellw_agree; [exact C8k | eapply agree_on_sub; [exact (NODES e He) | lia | cbn; lia] | lia | cbn; lia]. }
    assert (BK0 : forall i, 0 <= i < n -> cell8 ASEGS m (p + 8 * i) 0).
    { intros i Hi. apply (zero_cell8 m p _ i ZER); lia. }
    destruct NS as (S408 & S576 & S616 & S624 & S648).
    destruct WS as (W584 & W600 & W632 & W656).

    set (R := mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 (Z_to_bv 64 (2 ^ 64 - 1 - p)) (Z_to_bv 64 p)
                  y15 y16 y17 (Z_to_bv 64 key) y19 s4 y21 y22 (Z_to_bv 64 pn) wd (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 24))
                  (Z_to_bv 64 n) y28 y29 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60))) in VIS.
    assert (RG : REGF S1 bc p R) by (unfold REGF; repeat split; reflexivity).
    destruct (loop_all S1 F fc obj bl bc p ents (lbl LBe) m0 m U0 Hlast
                (conj Hp0 (conj Hp16 (conj HpI (conj HpC HpA)))) HPN HPO OCE OAPP NAPP (conj SPL SPH) ltac:(lia) S616 S648
                R RG Cp1 CH HASH BK0 ADP ADH ADN MI WRP WRH WRN) as (R' & M' & Hms & RGX & FINAL).

    assert (MUW : munch (WL obj bc p ents) m M' /\ wmono asegs m M' /\ mem_inv asegs M'
                  /\ addressable M' p (8 * n) /\ addressable M' obj 40 /\ (forall e, In e ents -> addressable M' (addr e) 32) /\ wr_at asegs M' obj 40).
    { destruct FINAL as [[HE ->] | (P' & Bf' & LS)].
      - split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ADP|]. split; [exact ADH|]. split; [exact ADN | exact WRH].
      - destruct LS as [_ _ _ _ _ _ _ Ladp Ladh Ladn Lmu Lwm Lmi _ Lwrh _ _].
        split; [exact Lmu|]. split; [exact Lwm|]. split; [exact Lmi|]. split; [exact Ladp|]. split; [exact Ladh|]. split; [exact Ladn | exact Lwrh]. }
    destruct MUW as (MU & WM & MI' & ADP' & ADH' & ADN' & WRH').

    pose proof (fun q A N a1 a2 => blk_win H HH LF s LB' m q A N a1 a2 RH) as BW.
    assert (WOK : Forall (aclient_write_ok H LB') (WL obj bc p ents) /\ Forall (afs_write_ok H LF) (WL obj bc p ents)
                  /\ Forall aconst_ok (WL obj bc p ents) /\ Forall stack0_ok (WL obj bc p ents)
                  /\ Forall (wmix ((pid, p, 8 * n) :: (qn, pn, 32) :: LBn) S1 (nt_X S1 obj)) (WL obj bc p ents)
                  /\ Forall (fun iv : Z * Z => Datatypes.snd iv <= ALOWSH_LO \/ AHI_LO <= Datatypes.fst iv) (WL obj bc p ents)).
    { destruct (BW pid p (8 * n) p (p + 8 * n) INP ltac:(lia) ltac:(lia)) as (P1 & P2 & P3 & P4 & P6).
      destruct (LbB_HEmpD.obj_window_ok H HH LF obj LB' m (obj + 16) (obj + 24) RF LFO ltac:(lia) ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
      assert (Q6 : obj + 24 <= ALOWSH_LO \/ AHI_LO <= obj + 16).
      { pose proof (aapp_not_shadowland (obj + 16) 8 (aapp_sub obj 40 (obj + 16) 8 OAPP ltac:(lia) ltac:(lia))) as X. lia. }
      assert (NW : forall e, In e ents -> aclient_write_ok H LB' (addr e, addr e + 8) /\ afs_write_ok H LF (addr e, addr e + 8)
                     /\ aconst_ok (addr e, addr e + 8) /\ stack0_ok (addr e, addr e + 8)
                     /\ wmix ((pid, p, 8 * n) :: (qn, pn, 32) :: LBn) S1 (nt_X S1 obj) (addr e, addr e + 8)
                     /\ (addr e + 8 <= ALOWSH_LO \/ AHI_LO <= addr e)).
      { intros e He. destruct (INN e He) as (q & HqN & HqL).
        destruct (BW q (addr e) 32 (addr e) (addr e + 8) HqL ltac:(lia) ltac:(lia)) as (N1 & N2 & N3 & N4 & N6).
        split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [|exact N6].
        right; right. exists q, (addr e), 32. split; [right; right; exact HqN | cbn; lia]. }
      unfold WL.
      split; [apply Forall_cons; [exact P1 | apply Forall_cons; [exact Q1 | apply Forall_nodes; intros e He; exact (proj1 (NW e He))]]|].
      split; [apply Forall_cons; [exact P2 | apply Forall_cons; [exact Q2 | apply Forall_nodes; intros e He; exact (proj1 (proj2 (NW e He)))]]|].
      split; [apply Forall_cons; [exact P3 | apply Forall_cons; [exact Q3 | apply Forall_nodes; intros e He; exact (proj1 (proj2 (proj2 (NW e He))))]]|].
      split; [apply Forall_cons; [exact P4 | apply Forall_cons; [exact Q4 | apply Forall_nodes; intros e He; exact (proj1 (proj2 (proj2 (proj2 (NW e He)))))]]|].
      split.
      - apply Forall_cons; [right; right; exists pid, p, (8 * n); split; [left; reflexivity | cbn; lia]|].
        apply Forall_cons; [right; left; intros a Ha; unfold nt_X; cbn [rin_ivs Datatypes.fst Datatypes.snd] in *; left; lia|].
        apply Forall_nodes. intros e He. exact (proj1 (proj2 (proj2 (proj2 (proj2 (NW e He)))))).
      - apply Forall_cons; [cbn [Datatypes.fst Datatypes.snd]; exact P6|].
        apply Forall_cons; [cbn [Datatypes.fst Datatypes.snd]; exact Q6|].
        apply Forall_nodes. intros e He. cbn [Datatypes.fst Datatypes.snd]. exact (proj2 (proj2 (proj2 (proj2 (proj2 (NW e He)))))). }
    destruct WOK as (W1 & W2 & W3 & W4 & W5 & W6).
    destruct (client_frame H HH s LB' LF B _ m M' RH RF AC RA MU WM W1 W2 W3) as (RH' & RF' & AC' & RA').
    assert (S0' : stack0 M' lo shi) by (eapply stack0_transport; [exact S0 | exact MU | exact WM | exact W4]).
    assert (XP' : xpres H LB0 S1 (nt_X S1 obj) m0 M').
    { eapply (xpres_munch_mixed H HH s LB' LB0 ((pid, p, 8 * n) :: (qn, pn, 32) :: LBn) S1 (nt_X S1 obj) _ m0 m M');
        [exact XP | exact RH | exact PE | lia | exact MU | exact WM | exact W5]. }
    assert (OWN' : lb_own ((pid, p, 8 * n) :: (qn, pn, 32) :: LBn) M') by exact (lb_own_wmono _ _ _ OWN WM).
    assert (ST' : stk asegs M' lo (S1 + 672)) by (eapply LbB_TopKit.stk_wmono; [exact ST | exact WM | lia]).

    assert (DJ : forall a k, 0 <= k -> (a + k <= p \/ p + 8 * n <= a) -> (a + k <= obj + 16 \/ obj + 24 <= a) ->
                 (forall e, In e ents -> a + k <= addr e \/ addr e + 8 <= a) -> disjoint_from (WL obj bc p ents) a k).
    { intros a k Hk D1 D2 D3. unfold WL. cbn [disjoint_from app]. split; [exact D1|]. split; [exact D2|]. apply disjoint_from_nodes. exact D3. }
    assert (TR : forall A cs, rw_cells asegs m A cs -> aceil <= A -> rw_cells asegs M' A cs).
    { intros A cs RC HA. eapply rw_cells_transport; [exact RC | exact MU | exact WM |].
      apply DJ; [lia | lia | lia |]. intros e He. pose proof (NCE e He). lia. }
    assert (WS' : WSLOTS ty enc S1 obj M' j584 (Z_to_bv 64 (pn / 8 + SHBASE))).
    { unfold WSLOTS, nt_wslots. refine (conj _ (conj _ (conj _ _))); apply TR; first [assumption | lia]. }
    assert (NS' : nt_slots M' S1 obj v408 v576 v624).
    { unfold nt_slots. refine (conj _ (conj _ (conj _ (conj _ _)))); apply TR; first [assumption | lia]. }
    assert (ATPB : ATP - 164 + 4 <= AIMG_TOP) by (unfold ATP, AIMG_TOP; lia).
    assert (EA : errno_addr tp = ATP - 164) by (rewrite TPV, u64_of_Z by (unfold ATP; lia); lia).
    assert (ERR' : rw_cells asegs M' (errno_addr tp) [C4 errv]).
    { rewrite EA in ERR |- *. eapply rw_cells_transport; [exact ERR | exact MU | exact WM | apply (DJ (ATP - 164) 4)]; [lia | lia | lia |].
      intros e He. pose proof (NCE e He). lia. }
    assert (PNC' : rw_cells asegs M' pn [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]).
    { eapply rw_cells_transport; [exact PNC | exact MU | exact WM | apply (DJ pn 32)]; [lia | lia | unfold apart in HQO; lia |].
      intros e He. pose proof (HQN e He) as X. unfold apart in X. lia. }
    assert (PNA' : addressable M' pn 32).
    { eapply addressable_transport; [exact PNA | exact MU | exact WM |]. apply LbB_HEmpI.dsh_app; [exact W6 | lia | lia | lia]. }

    assert (NODEWIN : forall e, In e ents -> forall e', In e' ents -> addr e + 8 + 24 <= addr e' \/ addr e' + 8 <= addr e + 8).
    { intros e He e' He'. destruct (Z.eq_dec (addr e') (addr e)) as [Eq | Ne]; [lia|].
      pose proof (nodes_apart _ _ _ _ _ _ e' e U0 He' He Ne) as Hap. unfold apart in Hap. lia. }
    assert (NODES' : forall e, In e ents -> agree_on m0 M' (addr e + 8) 24).
    { intros e He. destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _).
      destruct (u_node U0 (addr e) (hkey e) (snd (snd e)) ltac:(destruct e as [q [k v]]; exact He)) as (_ & _ & _ & _ & _ & _ & _ & _ & Heo & _).
      eapply agree_on_trans; [eapply agree_on_sub; [exact (NODES e He) | lia | lia] |].
      eapply agree_of_munch; [exact MU | | lia | lia]. intros z Hz.
      pose proof (HPN e He) as Hpe. unfold apart in Hpe, Heo.
      apply (disjoint_outside _ (addr e + 8) 24 z); [|lia]. apply DJ; [lia | clear - Hpe; lia | clear - Heo; lia | exact (NODEWIN e He)]. }
    assert (HAG : forall a k, 0 <= k -> obj <= a -> a + k <= obj + 16 \/ (obj + 24 <= a /\ a + k <= obj + 40) -> agree_on m M' a k).
    { intros a k Hk Ha Hak. eapply agree_of_munch; [exact MU | | lia | lia]. intros z Hz. apply (disjoint_outside _ a k z); [|lia].
      apply DJ; [lia | clear - HPO Ha Hak Hk; unfold apart in HPO; lia | clear - Ha Hak Hk; lia |].
      intros e He. destruct (u_node U0 (addr e) (hkey e) (snd (snd e)) ltac:(destruct e as [q [k' v]]; exact He)) as (_ & _ & _ & _ & _ & _ & _ & _ & Heo & _).
      clear - Heo Ha Hak Hk. unfold apart in Heo. lia. }
    assert (Cbl' : cell8 ASEGS M' obj p) by (eapply cellw_agree; [exact Cbl | apply HAG; lia | lia | cbn; lia]).
    assert (Cbc' : cell8 ASEGS M' (obj + 8) n) by (eapply cellw_agree; [exact Cbc | apply HAG; lia | lia | cbn; lia]).
    assert (Csz' : cell8 ASEGS M' (obj + 24) (Zlength ents)).
    { eapply cellw_agree; [exact Csz0 | | lia | cbn; lia]. eapply agree_on_trans; [eapply agree_on_sub; [exact HDR24 | lia | cbn; lia] | apply HAG; cbn; lia]. }
    assert (Cmlf' : cell4 ASEGS M' (obj + 32) 0x3f800000).
    { eapply cellw_agree; [exact Cmlf0 | | lia | cbn; lia]. eapply agree_on_trans; [eapply agree_on_sub; [exact HDR24 | lia | cbn; lia] | apply HAG; cbn; lia]. }
    assert (DEFH' : HRep.defined M' obj 40).
    { destruct (rw_cells_of_wr_hi M' obj 40 WRH' ltac:(lia) ltac:(lia)) as (hbs & HBS).
      pose proof (defined_of_rw_cells_hi M' obj _ HBS ltac:(lia)) as D. cbn [cells_size csize] in D. exact D. }

    assert (HU : exists ents', Permutation ents' ents /\ umapx MI_A 32 (nval32 ASEGS) (lbl LB') M' obj p n ents').
    { assert (NODEF : forall q k v (ents' : list ent), Permutation ents' ents -> In (q, (k, v)) ents' ->
                 cell8 ASEGS M' (q + 8) k ->
                 In (q, 32) (lbl LB') /\ 0 < q /\ q + 32 <= 2 ^ 47 /\ q mod 16 = 0
                 /\ cell8 ASEGS M' (q + 8) k /\ cell4 ASEGS M' (q + 16) k /\ 0 <= k < 2 ^ 32 /\ nval32 ASEGS M' q v
                 /\ apart q 32 obj 40 /\ (n <> 0 -> apart q 32 p (8 * n))).
      { intros q k v ents' PERM Hin C8k. assert (Hine : In (q, (k, v)) ents) by (eapply Permutation_in; [exact PERM | exact Hin]).
        destruct (u_node U0 q k v Hine) as (_ & Hq0' & Hq1' & Hqal' & _ & C4k & Hk & Hnv & Hap & _).
        pose proof (NODES' _ Hine) as TL. unfold HRehashModel.addr in TL. cbn [fst snd] in TL.
        split; [destruct (INN _ Hine) as (qi & _ & HqL); exact (lbl_in _ _ _ _ HqL)|].
        split; [exact Hq0'|]. split; [exact Hq1'|]. split; [exact Hqal'|]. split; [exact C8k|].
        split; [eapply cellw_agree; [exact C4k | eapply agree_on_sub; [exact TL | lia | cbn; lia] | lia | cbn; lia]|].
        split; [exact Hk|].
        split; [eapply nval32_agree; [exact Hnv | eapply agree_on_sub; [exact TL | lia | lia] | lia | lia]|].
        split; [exact Hap|].
        intros _. pose proof (HPN _ Hine) as X. unfold HRehashModel.addr in X. cbn [fst snd] in X. unfold apart in X |- *. clear - X. lia. }
      destruct FINAL as [[HE HM] | (P' & Bf' & LS)].
      - exists (@nil ent). rewrite HE in *. split; [apply Permutation_refl|].
        constructor; try (intros; exfalso; assumption).
        + constructor; [exact Cbl' | exact Cbc' | rewrite HM; exact Cp1 | exact Csz' | exact Cmlf' | exact DEFH'].
        + exact Hoal. + exact Ho0. + exact Ho1. + exact HnB.
        + unfold Zlength. cbn [length Z.of_nat]. lia.
        + right. split; [lia | exact (lbl_in _ _ _ _ INP)].
        + exact Hp16. + intros _; exact Hp0. + lia. + intros _. exact HPO.
        + intros i Hi. exists 0. split; [rewrite HM; exact (BK0 i Hi) | left; reflexivity].
        + constructor.
        + exact I.
      - exists P'. destruct LS as [PERM BI HPn Cp1' CH' HASH' BK _ _ _ _ _ _ _ _ _ _].
        rewrite app_nil_r in PERM, Cp1', CH'.
        assert (Hnoty : forall P1 y z P2, P' = P1 ++ y :: z :: P2 -> addr y <> sent).
        { intros P1 y z P2 HP'' Heq. assert (Hin : In y ents) by (eapply Permutation_in; [exact PERM | rewrite HP''; apply in_app_iff; right; left; reflexivity]).
          destruct y as [q [k v]]. destruct (u_node U0 q k v Hin) as (_ & Hq0' & _ & _ & _ & _ & _ & _ & Hap & _). unfold apart in Hap. cbn in Heq. lia. }
        split; [exact PERM|].
        constructor.
        + constructor; [exact Cbl' | exact Cbc' | exact Cp1' | | exact Cmlf' | exact DEFH'].
          unfold Zlength. rewrite (Permutation_length PERM). exact Csz'.
        + exact Hoal. + exact Ho0. + exact Ho1. + exact HnB.
        + unfold Zlength. rewrite (Permutation_length PERM). pose proof (u_load U0) as HL. unfold Zlength in HL. lia.
        + right. split; [lia | exact (lbl_in _ _ _ _ INP)].
        + exact Hp16. + intros _; exact Hp0. + lia. + intros _. exact HPO.
        + intros i Hi. exists (Bf' i). split; [exact (BK i Hi)|].
          destruct (binv_weak (Z * Z * Z) n sent P' Bf' i BI Hi Hnoty) as [Hb | [Hb | [Hb (x & P'' & HP'' & Hx)]]]; [left; exact Hb | right; left; exact Hb | right; right].
          split; [exact Hb|]. split; [rewrite HP''; discriminate|]. rewrite HP''. destruct x as [q [k v]]. cbn. symmetry. exact Hx.
        + apply (proj2 (base.NoDup_ListNoDup _)). exact (perm_nodup _ _ _ _ _ _ _ U0 PERM).
        + exact CH'.
        + intros q k v Hin. apply (NODEF q k v P' PERM Hin). exact (HASH' (q, (k, v)) ltac:(eapply Permutation_in; [exact PERM | exact Hin])).
        + intros q q' Hq Hq' Hne. apply (u_napart U0); [| | exact Hne].
          * apply in_map_iff in Hq. destruct Hq as (e & <- & He). apply in_map. eapply Permutation_in; [exact PERM | exact He].
          * apply in_map_iff in Hq'. destruct Hq' as (e & <- & He). apply in_map. eapply Permutation_in; [exact PERM | exact He]. }
    destruct HU as (ents' & PERM' & U').
    assert (SH' : umap_sh M' 32 (p, n, ents')).
    { unfold umap_sh, HStmts.t3a, HStmts.t3b, HStmts.t3c. cbn [Datatypes.fst Datatypes.snd]. split; [intros _; exact ADP'|].
      intros q k v Hin. exact (ADN' (q, (k, v)) ltac:(eapply Permutation_in; [exact PERM' | exact Hin])). }
    assert (PM' : Permutation (lbl ((pid, p, 8 * n) :: (qn, pn, 32) :: LBn)) ((pn, 32) :: umap_blocks 32 p n ents')).
    { unfold umap_blocks. destruct (Z.eqb_spec n 0); [lia|]. cbn [lbl map app blk_addr blk_size Datatypes.fst Datatypes.snd].
      eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_skip. eapply Permutation_trans; [exact PM|].
      change (fun e : Z * (Z * (Z * Z * Z)) => (Datatypes.fst e, 32)) with (fun e : ent => (addr e, 32)).
      apply Permutation_map. apply Permutation_sym. exact PERM'. }
    assert (HQB : forall q k, In (q, k) (umap_blocks 32 p n ents') -> apart pn 32 q k).
    { intros q k Hq. unfold umap_blocks in Hq. replace (n =? 0) with false in Hq by (symmetry; apply Z.eqb_neq; clear - Hn0; lia).
      cbn [app] in Hq. destruct Hq as [Hq | Hq].
      - injection Hq as E1 E2. subst q k. unfold apart. clear - HQP. lia.
      - apply in_map_iff in Hq. destruct Hq as (e & Heq & He). injection Heq as E1 E2. subst q k.
        apply (Permutation_in _ PERM') in He. exact (HQN e He). }

    assert (F616' : fldA M' (S1 + 616) 8 SHBASE) by (apply fld_of_slot; [exact (TR _ _ S616 ltac:(clear - ACL LOS; lia)) | unfold SHBASE; clear; lia | clear - SPL; lia]).
    assert (F632' : fldA M' (S1 + 632) 8 (obj + 8)).
    { destruct (proj1 (rw_cells_app asegs M' (S1 + 632) [C8 (Z_to_bv 64 (obj + 8))] [C8 (Z_to_bv 64 (obj / 8))]) (TR _ _ W632 ltac:(clear - ACL LOS; lia))) as (X & _).
      apply fld_of_slot; [exact X | clear - Ho0 Ho1; lia | clear - SPL; lia]. }
    assert (F664' : fldA M' (S1 + 664) 8 ((obj + 8) / 8 + SHBASE)).
    { destruct (proj1 (rw_cells_app asegs M' (S1 + 656) [C8 (Z_to_bv 64 obj)] [C8 (Z_to_bv 64 (sh (obj + 8)))]) (TR _ _ W656 ltac:(clear - ACL LOS; lia))) as (_ & X).
      replace (S1 + 656 + Z.of_nat (cells_size [C8 (Z_to_bv 64 obj)])) with (S1 + 664) in X by (cbn; clear; lia).
      replace (sh (obj + 8)) with ((obj + 8) / 8 + SHBASE) in X by (unfold sh, SHBASE; rewrite ASHADOW_BASE_val; clear; lia).
      apply fld_of_slot; [exact X | unfold SHBASE; clear - Ho0 Ho1; Z.div_mod_to_equations; lia | clear - SPL; lia]. }
    assert (FN' : fldA M' (obj + 8) 8 n) by (apply fld_of_cell8; exact Cbc').
    assert (SH8 : sh0 M' (obj + 8)) by (eapply sh0_of_addressable; [exact ADH' | change (40 / 8) with 5; clear; lia]).
    assert (EQX : forall r, In r keptX -> getr R' r = getr R r) by exact RGX.
    assert (K9 : getr R' 9%bv = Z_to_bv 64 S1) by (rewrite (EQX 9%bv ltac:(in_keptRE)); reflexivity).
    assert (K18 : getr R' 18%bv = Z_to_bv 64 key) by (rewrite (EQX 18%bv ltac:(in_keptRE)); reflexivity).
    destruct (x_step F fc R' M' S1 obj key n K9 K18 F616' F664' F632' FN' SH8 Ho0 Ho1 Hoal Hn2 KR32 SPL SPH
                (LbB_HEmpI3.bseq_land_boundE n HnB)
                ltac:(destruct Hncase as [[_ E] | [_ E]]; [left; exact E | right; exact E])) as (R2 & Hms2 & X15 & X22 & X27 & XK).
    assert (EQR : forall r, In r keptXI -> getr R2 r = getr R r).
    { intros r Hr. rewrite (XK r Hr). apply EQX. revert Hr. unfold keptXI. cbn [In]. intros Hr.
      repeat (destruct Hr as [Hr | Hr]; [subst r; in_keptRE |]). destruct Hr. }

    assert (FHF : rfull R) by apply rfull_mkR.
    eapply (sr_blk H HH); [exact KR | exact VIS | exact FHF | eapply CatSim.msteps_trans; [exact Hms | exact Hms2] |].
    intros msF1 mo1 KR1 MP1 VIS1.
    rewrite (EQR 2%bv ltac:(in_keptRE)), (EQR 3%bv ltac:(in_keptRE)), (EQR 4%bv ltac:(in_keptRE)), (EQR 8%bv ltac:(in_keptRE)),
      (EQR 9%bv ltac:(in_keptRE)), (EQR 20%bv ltac:(in_keptRE)), (EQR 23%bv ltac:(in_keptRE)), (EQR 24%bv ltac:(in_keptRE)),
      (EQR 25%bv ltac:(in_keptRE)), (EQR 26%bv ltac:(in_keptRE)), (EQR 30%bv ltac:(in_keptRE)), (EQR 31%bv ltac:(in_keptRE)),
      X15, X22, X27 in VIS1.
    eapply (stage_ins H HH gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0
              s msF1 mo1 M' F fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ errv LB' ((pid, p, 8 * n) :: (qn, pn, 32) :: LBn) pn p n ents' true j584);
      [ unfold ISTATE; exact VIS1 | exact FRZ | exact KR1 | ].
    unfold IPRE.
    refine (conj _ (conj WS' (conj NS' (conj SPL (conj SPH (conj (proj1 VR) (conj (proj1 (proj2 VR)) (conj (proj2 (proj2 VR))
      (conj MI' (conj ST' (conj ERR' (conj RA' (conj TPV (conj ACL (conj LOS (conj LFO
      (conj U' (conj SH' (conj PERM' (conj _ (conj _ (conj KR32 (conj ADH' (conj WRH'
      (conj Hq0 (conj _ (conj Hq16 (conj HQO (conj HQB (conj PNC' (conj PNA' (conj _ (conj _
      (conj RH' (conj PE (conj PM' (conj OWN' (conj XP' (conj RF' (conj AC' (conj S0' AL))))))))))))))))))))))))))))))))))))))))).
    - eapply (ah_mpres_trans H HH); [exact MP | exact MP1].
    - clear - Hn0. lia.
    - pose proof (u_load U0) as HL. clear - HL Hbcn. lia.
    - clear - HqC ACF2. lia.
    - intros X. discriminate X.
    - intros _. split; [exact BCZ | reflexivity].
  Qed.
End NtRE.
