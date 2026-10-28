(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3 Hoare RefMemcpyLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts HRehashModel HFpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_HStKit LbB_VecT LbB_NtStmt LbB_NtK LbB_NtRK LbB_NtD LbB_NtI LbB_NtI4
  LbB_NtRL LbB_NtRB LbB_NtF.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_TopKit LbB_HEmpD LbB_HEmpI LbB_HEmpS LbB_HEmpR LbB_HEmpL LbB_HEmpN
  LbB_HEmpI2 LbB_HEmpI3 LbB_HEmpF LbB_HNextPrime.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HWord.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


Definition E_LF : Z := 0xf545c.
Definition E_FLW : Z := 0xf5490.
Definition E_NG : Z := 0xf54b8.
Definition E_GR : Z := 0xf54c4.
Definition E_G2 : Z := 0xf5540.
Definition E_NPR : Z := 0xf5578.
Definition E_RA : Z := 0xf5594.

Section NtG.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHB : asan_rt_hyps_bp H.
  Let HH : asan_rt_hyps H := rt_bp_base H HHB.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.
  Variables (gp tp s0 s4 ty wd enc : word) (S1 : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj key v408 v576 v624 : Z) (ents : list ent).
  Variables (bl bc lo B shi : Z) (m0 : mem) (mo0 : Model).
  Variable (CH : list (Z * Z)).
  #[local] Notation n := (bseq_next bc).
  #[local] Notation addr := (HRehashModel.addr (Z * Z * Z)).
  #[local] Notation hkey := (HRehashModel.hkey (Z * Z * Z)).

  Hypothesis BSQ : In bc BSEQ.
  Hypothesis Hlast : bc <> BSEQ_LAST.
  Hypothesis OCE : obj + 40 <= aceil.
  Hypothesis LFO : map_live_frame LF obj.
  Hypothesis ACL : aceil <= lo.
  Hypothesis LOS : lo <= S1.
  Hypothesis LOR : lo <= S1 - ANT_STACK.
  Hypothesis TPV : tp = Z_to_bv 64 ATP.
  Hypothesis KR32 : 0 <= key < 2 ^ 32.
  Hypothesis ZLEN : Zlength ents + 1 < 2 ^ 24.
  Hypothesis SP16 : S1 mod 16 = 0.
  Hypothesis SPB : S1 + 672 <= B.
  Hypothesis BR : B < 2 ^ 64.
  Hypothesis SHI : S1 + 672 <= shi.
  Hypothesis TRK : trace_ok (as_TR H) APC0_FREE (R_DRET :: map snd CH).
  Hypothesis CHH : forall fp ra, In (fp, ra) CH -> S1 + 688 <= fp.
  #[local] Opaque bseq_next.
  Abbreviation IPREx := (IPRE H tp ty enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0).

  Abbreviation QIg sk mz := (QI H gp tp s0 s4 ty wd enc S1 sk LB0 LF obj key v408 v576 v624 ents bl bc lo B shi mz mo0).
  Abbreviation QIx := (QIg sk0 m0).

  Lemma QI_mono : forall (s1 : as_St H) (m1 : mem) c,
    QIg s1 m1 c -> as_AL H s1 >= as_AL H sk0 -> xpres H LB0 S1 (nt_X S1 obj) m0 m1 -> QIx c.
  Proof.
    intros s1 m1 c Q AL XP. unfold QI, QF, nt_post in Q |- *.
    repeat match type of Q with ex _ => let x := fresh "x" in destruct Q as [x Q]; exists x end.
    repeat match type of Q with _ /\ _ => let C := fresh "C" in destruct Q as [C Q] end.
    repeat match goal with |- _ /\ _ => split end; try assumption.
    all: match goal with
         | |- xpres _ _ _ _ _ _ => eapply xpres_trans; eassumption
         | |- _ => clear - Q AL; lia
         end.
  Qed.

  Definition LPRE (s : as_St H) (mo : Model) (m : mem) (errv' : word) (LB' LBm : list block) (p : Z) : Prop :=
    as_MPRES H mo0 mo
    /\ (exists j584, rw_cells asegs m (S1 + 584) [C8 j584; C8 (Z_to_bv 64 (p / 8 + SHBASE))])
    /\ nt_wslots m S1 obj ty enc /\ nt_slots m S1 obj v408 v576 v624
    /\ 2 ^ 45 <= S1 /\ S1 + 672 <= 2 ^ 47 /\ (0 <= v408 < 2 ^ 64 /\ 0 <= v576 < 2 ^ 64 /\ 0 <= v624 < 2 ^ 64)
    /\ mem_inv asegs m /\ stk asegs m lo (S1 + 672) /\ rw_cells asegs m (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m B
    /\ umapx MI_A 32 (nval32 ASEGS) (lbl LB') m obj bl bc ents /\ umap_sh m 32 (bl, bc, ents)
    /\ addressable m obj 40 /\ wr_at asegs m obj 40
    /\ 0 < p /\ p + 32 <= 2 ^ 47 /\ p mod 16 = 0 /\ apart p 32 obj 40
    /\ (forall q k, In (q, k) (umap_blocks 32 bl bc ents) -> apart p 32 q k)
    /\ rw_cells asegs m p [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ addressable m p 32
    /\ as_RHEAP H s LB' m /\ Permutation LB' (LB0 ++ LBm) /\ Permutation (lbl LBm) ((p, 32) :: umap_blocks 32 bl bc ents) /\ lb_own LBm m
    /\ xpres H LB0 S1 (nt_X S1 obj) m0 m /\ as_RFS H LF m /\ ACONST m /\ stack0 m lo shi
    /\ as_AL H s >= as_AL H sk0 /\ 0 <= as_AL H s
    /\ lb_small LB' + nsmall (8 * n) <= RT_SMALL_MAX /\ Z.of_nat (length LB') + 1 <= RT_CNT_MAX /\ nlarge LB' + nlg (8 * n) <= RT_LARGE_MAX
    /\ ((bc = 0 \/ Zlength ents = bc) -> ICM (8 * n) <= as_AL H s)
    /\ as_chain H m (bv_unsigned s0) CH.

  #[local] Ltac dLP LP :=
    destruct LP as (MP & W584 & WS & RS & SPL & SPH & V64 & MI & ST & ERR & RA & U & SH & ADH & WRH & P0 & P47 & P16 & PO & PA & NC & ADPN
                    & RH & PE & PM & OWN & XP & RF & AC & S0 & AL & AL0 & RSM & RCN & RLG & RICM & CHN).

  Lemma lpre_stack : forall s mo m m1 errv' LB' LBm p (W : list (Z * Z)),
    LPRE s mo m errv' LB' LBm p ->
    munch W m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    Forall (fun iv => aceil <= fst iv /\ snd iv <= S1 /\ fst iv <= snd iv) W ->
    LPRE s mo m1 errv' LB' LBm p.
  Proof.
    intros s mo m m1 errv' LB' LBm p W LP MU WM MI1 FW. dLP LP.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    pose proof (LbB_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.

    assert (FWK : Forall (fun iv => aclient_write_ok H LB' iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) W).
    { eapply Forall_impl; [|exact FW]. intros [l h] (X1 & X2 & X3). cbn [Datatypes.fst Datatypes.snd] in *.
      destruct (stack_window_ok H LB' LF l h X1 ltac:(unfold AFS_SIZE in *; lia)) as (W1 & W2 & W3).
      split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. left. cbn. unfold AHI_LO. lia. }
    assert (F1 : Forall (aclient_write_ok H LB') W) by (eapply Forall_impl; [|exact FWK]; intros iv X; exact (proj1 X)).
    assert (F2 : Forall (afs_write_ok H LF) W) by (eapply Forall_impl; [|exact FWK]; intros iv X; exact (proj1 (proj2 X))).
    assert (F3 : Forall aconst_ok W) by (eapply Forall_impl; [|exact FWK]; intros iv X; exact (proj1 (proj2 (proj2 X)))).
    assert (F4 : Forall stack0_ok W) by (eapply Forall_impl; [|exact FWK]; intros iv X; exact (proj2 (proj2 (proj2 X)))).
    assert (FDJ : forall a k, a + k <= aceil \/ S1 <= a -> disjoint_from W a k).
    { intros a k Hc. apply LbB_HEmpI2.dj_of_forall. eapply Forall_impl; [|exact FW]. intros iv (X1 & X2 & X3). lia. }
    assert (FSH : forall A k, 0 <= A -> 0 <= k -> A + k <= 2 ^ 47 -> disjoint_from W (sh A) (nsh k)).
    { intros A k HA Hk Hak. apply LbB_HEmpI2.dj_of_forall. eapply Forall_impl; [|exact FW]. intros iv (X1 & X2 & X3).
      pose proof (sh_nsh_high A k HA Hk ltac:(unfold AAPP_HI; lia)) as SN. unfold AHI_LO in SN. lia. }
    destruct (client_frame H HH s LB' LF B W m m1 RH RF AC RA MU WM F1 F2 F3) as (RH1 & RF1 & AC1 & RA1).
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    unfold LPRE.
    split; [exact MP|].
    split; [destruct W584 as (j584 & X1); exists j584;
           (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply FDJ; right; lia])|].
    split; [unfold nt_wslots in WS |- *; destruct WS as (X1 & X2 & X3); split; [|split];
           (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply FDJ; right; lia])|].
    split; [unfold nt_slots in RS |- *; destruct RS as (X1 & X2 & X3 & X4 & X5); repeat match goal with |- _ /\ _ => split end;
           (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply FDJ; right; lia])|].
    split; [exact SPL|]. split; [exact SPH|]. split; [exact V64|].
    split; [exact MI1|].
    split; [eapply LbB_TopKit.stk_wmono; [exact ST | exact WM | lia]|].
    split. { rewrite TPV in ERR |- *. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
             eapply rw_cells_transport; [exact ERR | exact MU | exact WM | apply FDJ; left; cbn; unfold ATP; lia]. }
    split; [exact RA1|].

    assert (BLK : forall q k, In (q, k) (umap_blocks 32 bl bc ents) -> 0 < q /\ q + k <= aceil /\ 0 <= k /\ aapp q k).
    { intros q k Hq. destruct (lbl_in_inv LBm q k (Permutation_in _ (Permutation_sym PM) (or_intror Hq))) as (qi & Qi).
      assert (QiL : In (qi, q, k) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact Qi).
      pose proof (ah_blocks H HH _ _ _ _ RH QiL) as (B0 & _ & Bn & _ & BC & _ & BA).
      cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in B0, Bn, BC, BA. split; [lia|]. split; [lia|]. split; [lia | exact BA]. }
    assert (FPA : forall a, umap_foot 32 obj bl bc ents a -> 0 <= a < aceil).
    { intros a [Ha | [[Hbc Ha] | (q & Hq & Hqa)]].
      - lia.
      - assert (IB : In (bl, 8 * bc) (umap_blocks 32 bl bc ents))
          by (unfold umap_blocks; apply in_app_iff; left; destruct (Z.eqb_spec bc 0); [lia | left; reflexivity]).
        destruct (BLK _ _ IB) as (B0 & BC & _). lia.
      - apply in_map_iff in Hq. destruct Hq as ([z [k v]] & Hz & Hin). cbn in Hz. subst z.
        assert (IB : In (q, 32) (umap_blocks 32 bl bc ents))
          by (unfold umap_blocks; apply in_app_iff; right; apply in_map_iff; exists (q, (k, v)); split; [reflexivity | exact Hin]).
        destruct (BLK _ _ IB) as (B0 & BC & _). lia. }
    assert (OUT : forall a, 0 <= a < aceil -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a Ha. apply MU. rewrite u64_of_Z by lia. apply LbB_HEmpI2.out_of_forall. eapply Forall_impl; [|exact FW]. intros iv (X1 & X2 & X3). lia. }
    split; [eapply (umapx_agree ASEGS LY_A MI_A 32 _ (nval32 ASEGS) (nval32_agree ASEGS) ltac:(lia) (lbl LB') (lbl LB') m m1);
              [exact U | intros a Ha; exact (OUT a (FPA a Ha)) | intros; assumption]|].
    split.
    { destruct SH as [SHb SHn]. unfold umap_sh, HStmts.t3a, HStmts.t3b, HStmts.t3c in *. cbn [Datatypes.fst Datatypes.snd] in *. split.
      - intros Hbc. assert (IB : In (bl, 8 * bc) (umap_blocks 32 bl bc ents))
          by (unfold umap_blocks; apply in_app_iff; left; destruct (Z.eqb_spec bc 0); [lia | left; reflexivity]).
        destruct (BLK _ _ IB) as (B0 & BC & Bn & _).
        eapply addressable_transport; [exact (SHb Hbc) | exact MU | exact WM | apply FSH; lia].
      - intros q k v Hin. assert (IB : In (q, 32) (umap_blocks 32 bl bc ents))
          by (unfold umap_blocks; apply in_app_iff; right; apply in_map_iff; exists (q, (k, v)); split; [reflexivity | exact Hin]).
        destruct (BLK _ _ IB) as (B0 & BC & Bn & _).
        eapply addressable_transport; [exact (SHn q k v Hin) | exact MU | exact WM | apply FSH; lia]. }
    split; [eapply addressable_transport; [exact ADH | exact MU | exact WM | apply FSH; lia]|].
    split; [exact (wr_at_wmono _ _ _ _ WRH WM)|].
    split; [exact P0|]. split; [exact P47|]. split; [exact P16|]. split; [exact PO|]. split; [exact PA|].
    destruct (lbl_in_inv LBm p 32 (Permutation_in _ (Permutation_sym PM) (or_introl eq_refl))) as (qp & QPm).
    assert (QPL : In (qp, p, 32) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact QPm).
    pose proof (ah_blocks H HH _ _ _ _ RH QPL) as (_ & _ & _ & _ & PCE & _ & _). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in PCE.
    split; [eapply rw_cells_transport; [exact NC | exact MU | exact WM | apply FDJ; left; cbn [cells_size csize Z.of_nat]; lia]|].
    split; [eapply addressable_transport; [exact ADPN | exact MU | exact WM | apply FSH; lia]|].
    split; [exact RH1|]. split; [exact PE|]. split; [exact PM|].
    split; [exact (lb_own_wmono _ _ _ OWN WM)|].
    split.
    { eapply xpres_trans; [exact XP|]. eapply (xpres_weaken H).
      - eapply (xpres_of_munch H s LB' S1 (nt_X S1 obj) W m m m1 HH RH MU WM).
        eapply Forall_impl; [|exact FW]; intros iv (X1 & X2 & X3); left; lia.
      - lia.
      - intros b Hb. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. left. exact Hb.
      - intros a Ha. exact Ha. }
    split; [exact RF1|]. split; [exact AC1|]. split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact F4]|].
    split; [exact AL|]. split; [exact AL0|]. split; [exact RSM|]. split; [exact RCN|]. split; [exact RLG|]. split; [exact RICM|].
    eapply (chain_keep H HH m m1 _ CH S1); [exact CHN | exact CHH |].
    intros a Ha. apply MU. rewrite u64_of_Z by lia. apply LbB_HEmpI2.out_of_forall. eapply Forall_impl; [|exact FW]. intros iv (X1 & X2 & X3). lia.
  Qed.

  Definition srRA : list expr :=
    srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32); (22%bv, EAlu ALU_ADD (EVar 33) (ELit 8)); (27%bv, EVar 34)].
  Definition KNRA : list kentry :=
    [KWord (SA (EVar 32) 664) 8 (EVar 36); KWord (SA (EVar 36) 0) 1 (ELit 0); KRange (EVar 34) 1 (2 ^ 28);
     KRange (EVar 33) 7241728 (2 ^ 47 - 40); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672)].

  Lemma stage_ra : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y28 y29 : word) (errv' : word) (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 key) y19 s4 y21 (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p) wd (Z_to_bv 64 obj)
                             (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 n) y28 y29 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60)))
                        F (Z_to_bv 64 E_RA) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> LPRE s mo m errv' LB' LBm p -> (bc = 0 \/ Zlength ents = bc) ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y28 y29 errv' LB' LBm p VIS FRZ KR LP GROW.
    pose proof LP as LP0. dLP LP0.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof LOR as LOR'. unfold ANT_STACK, AOPNEW_STACK, AMALLOC_STACK in LOR'.
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1. pose proof (u_obj_al U) as Hoal.
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U)) as BCR.
    destruct (LbB_HEmpR.bseq_next_factsE bc (u_bseq U) Hlast) as (HnB & Hbcn & Hn28 & _).
    assert (Hn0 : 0 < n) by (clear - BCR Hbcn; lia).
    pose proof (LbB_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    destruct (u_hdr U) as [_ Cbc _ _ _ _].
    assert (GZO : gz m obj 40) by (apply LbB_HEmpI.gzA; [exact ADH | reflexivity]).
    pose proof WS as WS0. destruct WS0 as (W600 & W632 & W656).

    destruct (LbB_HEmpR.lbl_split LBm p 32 _ PM) as (qp & LBmr & PMs & PMr).
    assert (PEr : Permutation LB' (LB0 ++ (qp, p, 32) :: LBmr)) by (eapply perm_trans; [exact PE | apply Permutation_app_head; exact PMs]).
    assert (QPL : In (qp, p, 32) LB') by (apply (Permutation_in _ (Permutation_sym PEr)); apply in_or_app; right; left; reflexivity).

    remember (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 key) y19 s4 y21 (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p) wd (Z_to_bv 64 obj)
                  (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 n) y28 y29 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60))) as R eqn:HR0.
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 obj; Z_to_bv 64 n; Z_to_bv 64 bc; Z_to_bv 64 (sh (obj + 8))]).
    assert (HR : regs_ok E srRA R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; rewrite ?w_add by lia; reflexivity] |]). apply Forall_nil. }
    assert (Hrd_bc : sc_denot asegs m E (SCReadBase (SA (EVar 33) 8) 8 false (EVar 35))).
    { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbc); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
    assert (HK : know_ok asegs E m (kn_fix 20 [AOPNEW] (SCR [false] [EVar 35] []) E_RA srRA KNRA 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons; [kword_cell W656 8%nat (C8 (Z_to_bv 64 (sh (obj + 8))))|].
      apply Forall_cons; [eapply (kshadow0_reg E m (EVar 36) (obj + 8)); [evs; unfold sh; rewrite ASHADOW_BASE_val; unfold SHBASE; f_equal; lia | lia | exact (gz_at m obj 40 8 GZO ltac:(lia))]|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - Hn0 Hn28; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - OB3 Ho1; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - SPL SPH; lia|].
      clear - GZO Ho0 Ho1 OB3. know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R E_RA m (seg_rom asegs) HR HK 30%nat [AOPNEW] (SCR [false] [EVar 35] []) 50%N.
    { split_scs; [ | exact Hrd_bc | ].
      - clear - E BCR Hbcn Hn28 Hn0. cbn [sc_denot]; evs. rewrite ?br_ne, ?br_eq, ?br_ltu, ?br_geu by lia. bool_lia.
      - clear - E Ho0 Ho1 SPL SPH; cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [edenot a_base a_off];
        unfold sh; rewrite ?ASHADOW_BASE_val; unfold SHBASE;
        rewrite ?u64_of_Z by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia. }
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 1%bv G1. rreg HR' 10%bv G10. rreg HR' 21%bv G21. rreg HR' 22%bv G22. rreg HR' 27%bv G27.
    rreg HR' 2%bv G2. rreg HR' 9%bv G9.
    rewrite (w_mul 8 n) in G10 by lia.
    assert (G21' : getr R' 21 = LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) by (rewrite G21, HR0; reflexivity).
    assert (G22' : getr R' 22 = Z_to_bv 64 (2 ^ 60)) by (rewrite G22, HR0; reflexivity).
    rewrite G1, G10, G21', G22', G27, G2, G9 in HRe. clear G21 G22.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.

    assert (AOK : as_alloc_ok H s LB' (8 * n)) by exact (rt_bp_live H HHB s LB' m (8 * n) RH ltac:(lia) RSM RCN RLG).
    assert (CM : as_Cm H (8 * n) <= as_AL H s) by (rewrite (proj2 (rt_bp_cost H HHB) (8 * n)); exact (RICM GROW)).
    eapply (ah_seq H HH).
    { eapply (ah_opnew H HH) with (n := 8 * n) (LB := LB') (lo := lo) (B := B) (errv := errv');
        [ exact VIS1 | exact RH | exact KR1 | exact AOK | exact CM | exact RA
        | rewrite u64_of_Z by lia; lia
        | rewrite u64_of_Z by lia; exact (proj1 (stk_split asegs m lo S1 (S1 + 672) ST ltac:(lia)))
        | exact ACL | rewrite u64_of_Z by lia; unfold AOPNEW_STACK, AMALLOC_STACK; lia
        | exact ERR | exact MI | exact TPV | rewrite u64_of_Z by lia; exact SP16
        | exact AC | reflexivity | lia ]. }
    intros [msF2 mo2] POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & p8 & junk & pid & s'
                      & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & AP2 & ABR & RH2 & CB2 & ADDR & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    first [rewrite (ret_pc_even R_NEWRET ltac:(unfold R_NEWRET; lia) eq_refl) in VIS2 | rewrite (ret_pc_even 0xf55c0 ltac:(lia) eq_refl) in VIS2].
    rewrite u64_of_Z in AP2, ST2 by lia.
    rewrite (proj2 (rt_bp_cost H HHB) (8 * n)) in AL2.

    assert (XP12 : xpres H LB' S1 [] m m2) by exact (xpres_of_apres H _ _ [] _ _ AP2).
    assert (ST2' : stk asegs m2 lo (S1 + 672)).
    { apply (stk_merge asegs m2 lo S1 (S1 + 672)); [exact ST2 | | clear - ACL LOR'; lia].
      eapply (apres_stk H); [exact AP2 | exact (proj2 (stk_split asegs m lo S1 (S1 + 672) ST ltac:(clear - ACL LOR'; lia))) | lia]. }
    assert (RF2 : as_RFS H LF m2) by exact (RFS_via_apres H HH LF LB' _ m m2 RF AP2).
    assert (S02 : stack0 m2 lo shi) by (eapply (stack0_xpres H); [exact XP12 | exact S0 | apply Forall_nil]).
    assert (OWN2 : lb_own ((qp, p, 32) :: LBmr) m2).
    { eapply (lb_own_apres H); [eapply lb_own_incl; [| exact OWN] | exact AP2 |].
      - intros b Hb. apply (Permutation_in _ (Permutation_sym PMs)). exact Hb.
      - intros b Hb. apply (Permutation_in _ (Permutation_sym PEr)). apply in_or_app. right. exact Hb. }
    assert (HOX : forall i, 0 <= i < 40 -> xclient H LB' S1 [] (obj + i)).
    { intros i Hi. split; [|intros K; exact K]. right; right; right; right; left. unfold AFS_SIZE in *. lia. }
    assert (INm : forall q k, In (q, k) (umap_blocks 32 bl bc ents) -> In (q, k) (lbl LBm)).
    { intros q k Hq. apply (Permutation_in _ (Permutation_sym PM)). right. exact Hq. }
    assert (INL : forall q k, In (q, k) (lbl LBm) -> In (q, k) (lbl LB')).
    { intros q k Hq. destruct (lbl_in_inv _ _ _ Hq) as (qi & Qi). unfold lbl. apply in_map_iff. exists (qi, q, k). split; [reflexivity|].
      apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. right. exact Qi. }
    assert (U2 : umapx MI_A 32 (nval32 ASEGS) (lbl LB') m2 obj bl bc ents).
    { eapply (umapx_xp H 32 _ (nval32 ASEGS) LB' S1 [] LB' LB' m m2 obj); [exact (nval32_agree ASEGS) | lia | exact XP12 | exact U | exact HOX |].
      apply (blkx_intro H). intros q k Hq. split; [exact (INL q k (INm q k Hq))|]. split; [exact (INL q k (INm q k Hq))|]. intros a _ K. exact K. }
    assert (SH2 : umap_sh m2 32 (bl, bc, ents)).
    { eapply (umap_sh_xp H); [exact XP12 | exact SH |]. apply (blksh_intro H). intros q k Hq. split; [exact (INL q k (INm q k Hq)) | intros a _ K; exact K]. }
    assert (AD2 : addressable m2 obj 40).
    { eapply (addressable_xp H); [exact XP12 | exact ADH |]. intros a Ha. split; [|intros K; exact K].
      right; right; right; right; right; left.
      unfold sh, nsh in Ha |- *. clear - Ha OB1 OB2 Hoal Ho0. Z.div_mod_to_equations. lia. }
    assert (WR2 : wr_at asegs m2 obj 40).
    { eapply xpres_wr_at; [exact XP12 | exact WRH |]. split; [right; right; right; right; left; unfold AFS_SIZE in *; lia | apply Forall_nil]. }
    assert (CRS : forall a k, S1 <= a -> aclient_range H LB' S1 a k) by (intros a k Ha; left; exact Ha).
    assert (W5842 : exists j584, rw_cells asegs m2 (S1 + 584) [C8 j584; C8 (Z_to_bv 64 (p / 8 + SHBASE))]).
    { destruct W584 as (j584 & X1). exists j584. eapply (apres_rw_cells H); [exact AP2 | exact X1 | apply CRS; lia]. }
    assert (WS2 : nt_wslots m2 S1 obj ty enc).
    { unfold nt_wslots in WS |- *. destruct WS as (X1 & X2 & X3).
      split; [|split]; (eapply (apres_rw_cells H); [exact AP2 | eassumption | apply CRS; lia]). }
    assert (RS2 : nt_slots m2 S1 obj v408 v576 v624).
    { unfold nt_slots in RS |- *. destruct RS as (X1 & X2 & X3 & X4 & X5).
      repeat match goal with |- _ /\ _ => split end; (eapply (apres_rw_cells H); [exact AP2 | eassumption | apply CRS; lia]). }
    assert (NC2 : rw_cells asegs m2 p [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]).
    { eapply (apres_rw_cells H); [exact AP2 | exact NC |]. cbn [cells_size csize Z.of_nat]. right; right; left. exists (qp, p, 32). split; [exact QPL | cbn; lia]. }
    assert (ADPN2 : addressable m2 p 32) by (eapply (apres_addressable H); [exact AP2 | exact ADPN | exact QPL]).
    assert (CHN2 : as_chain H m2 (bv_unsigned s0) CH).
    { eapply (chain_keep H HH m m2 _ CH S1); [exact CHN | exact CHH |]. intros a Ha. exact (proj1 (AP2 a ltac:(lia) ltac:(left; lia))). }
    assert (XP2 : xpres H LB0 S1 (nt_X S1 obj) m0 m2).
    { eapply xpres_trans; [exact XP|]. eapply (xpres_weaken H); [exact XP12 | lia | | intros a Ha; destruct Ha].
      intros b Hb. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. left. exact Hb. }
    destruct SH2 as [SHb SHn]. unfold HStmts.t3a, HStmts.t3b, HStmts.t3c in SHb, SHn. cbn [Datatypes.fst Datatypes.snd] in SHb, SHn.
    destruct W5842 as (j584 & W5842).
    eapply (ah_mono H HH).
    { eapply (LbB_NtRB.stage_b H HHB gp tp s0 s4 ty wd enc S1 s LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m2 mo0 LB' CH
                U2 Hlast (RICM GROW) OCE LFO ACL LOS LOR TPV KR32 ZLEN SP16 SPB TRK CHH);
        [ exact VIS2 | exact FRZ | exact KR2 | eapply (ah_mpres_trans H HH); [exact MP | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2]]
        | unfold WSLOTS; split; [exact W5842 | exact WS2] | exact RS2 | exact SPL | exact SPH | exact V64 | exact MI2 | exact ST2' | exact ERR2 | exact RA2
        | intros e He; apply agree_on_refl | apply agree_on_refl
        | intros Hb; exact (SHb Hb) | exact AD2 | intros [q [k v]] He; exact (SHn q k v He) | exact WR2
        | exact RH2 | exact PEr | exact PMr | exact OWN2 | exact CB2 | exact ADDR
        | apply xpres_refl | exact RF2 | exact AC2 | exact S02 | clear - AL2; lia | exact NC2 | exact ADPN2 | exact GROW | exact CHN2 ]. }
    intros c' Q'. eapply (QI_mono s m2 c' Q'); [clear - AL; lia | exact XP2].
  Qed.

  Lemma lpre_ipre : forall s mo m errv' LB' LBm p, LPRE s mo m errv' LB' LBm p -> bc <> 0 -> Zlength ents + 1 <= bc ->
    exists j584, IPREx s mo m errv' LB' LBm p bl bc ents false j584.
  Proof.
    intros s mo m errv' LB' LBm p LP Hbc LOAD. dLP LP.
    destruct W584 as (j584 & W584). destruct V64 as (V1 & V2 & V3). exists j584.
    unfold IPRE.
    split; [exact MP|]. split; [unfold WSLOTS; split; [exact W584 | exact WS]|]. split; [exact RS|].
    split; [exact SPL|]. split; [exact SPH|]. split; [exact V1|]. split; [exact V2|]. split; [exact V3|].
    split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact RA|]. split; [exact TPV|]. split; [exact ACL|]. split; [exact LOS|].
    split; [exact LFO|]. split; [exact U|]. split; [exact SH|]. split; [apply Permutation_refl|]. split; [exact Hbc|].
    split; [exact LOAD|]. split; [exact KR32|]. split; [exact ADH|]. split; [exact WRH|].
    split; [exact P0|]. split; [exact P47|]. split; [exact P16|]. split; [exact PO|]. split; [exact PA|]. split; [exact NC|].
    split; [exact ADPN|]. split; [intros _; split; reflexivity|]. split; [intros X; discriminate X|].
    split; [exact RH|]. split; [exact PE|]. split; [exact PM|]. split; [exact OWN|]. split; [exact XP|].
    split; [exact RF|]. split; [exact AC|]. split; [exact S0|]. clear - AL. lia.
  Qed.

  Lemma stage_np : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y21 y28 y29 y30 y31 : word) (errv' : word) (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR (Z_to_bv 64 E_NPR) (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1)
                             (Z_to_bv 64 (np_arg bc)) y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 (obj + 24)) y19 s4 y21 (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p)
                             (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) wd (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 key) y28 y29 y30 y31)
                        F (Z_to_bv 64 LbB_HNextPrime.NP_A) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> LPRE s mo m errv' LB' LBm p -> bc <> 0 -> (bc = 0 \/ Zlength ents = bc) ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y21 y28 y29 y30 y31 errv' LB' LBm p VIS FRZ KR LP Hbc0 GROW.
    pose proof LP as LP0. dLP LP0.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof LOR as LOR'. unfold ANT_STACK, AOPNEW_STACK, AMALLOC_STACK in LOR'.
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U)) as BCR.
    remember (mkR (Z_to_bv 64 E_NPR) (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1)
                  (Z_to_bv 64 (np_arg bc)) y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 (obj + 24)) y19 s4 y21 (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p)
                  (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) wd (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 key) y28 y29 y30 y31) as R eqn:HR0.

    eapply (LbB_HEmpN.np_sr H HH QIx s msF mo R F fc m bc S1 (Z_to_bv 64 E_NPR) KR VIS (u_bseq U) Hbc0);
      [ unfold LbB_HNextPrime.BSEQ_LAST_A; unfold BSEQ_LAST in Hlast; exact Hlast
      | rewrite HR0; reflexivity | rewrite HR0; reflexivity | vm_compute; reflexivity | rewrite HR0; reflexivity
      | exact SP16 | lia | lia
      | apply (LbB_HEmpN.stack_room_of_stk (S1 + 672) lo); [exact ST | lia | lia | lia] | exact MI | rewrite HR0; apply rfull_mkR | ].
    intros msF2 mo2 R2 KR2 MP2 VIS2 KEPT G10n FR2.

    assert (Q1 : getr R2 1 = Z_to_bv 64 E_NPR) by (rewrite (KEPT 1%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q2 : getr R2 2 = Z_to_bv 64 S1) by (rewrite (KEPT 2%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q3 : getr R2 3 = gp) by (rewrite (KEPT 3%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q4 : getr R2 4 = tp) by (rewrite (KEPT 4%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q8 : getr R2 8 = s0) by (rewrite (KEPT 8%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q9 : getr R2 9 = Z_to_bv 64 S1) by (rewrite (KEPT 9%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q18 : getr R2 18 = Z_to_bv 64 (obj + 24)) by (rewrite (KEPT 18%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q19 : getr R2 19 = y19) by (rewrite (KEPT 19%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q20 : getr R2 20 = s4) by (rewrite (KEPT 20%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q21 : getr R2 21 = y21) by (rewrite (KEPT 21%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q22 : getr R2 22 = Z_to_bv 64 (obj + 8)) by (rewrite (KEPT 22%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q23 : getr R2 23 = Z_to_bv 64 p) by (rewrite (KEPT 23%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q24 : getr R2 24 = LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) by (rewrite (KEPT 24%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q25 : getr R2 25 = wd) by (rewrite (KEPT 25%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q26 : getr R2 26 = Z_to_bv 64 (2 ^ 60)) by (rewrite (KEPT 26%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q27 : getr R2 27 = Z_to_bv 64 key) by (rewrite (KEPT 27%bv ltac:(cbn; tauto)), HR0; reflexivity).
    rewrite (rfull_eq R2 FR2) in VIS2.
    rewrite Q1, Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27, G10n in VIS2.

    set (bs := word_to_le_bytes 8 (Z_to_bv 64 E_NPR)) in VIS2.
    assert (Lbs : length bs = 8%nat) by reflexivity.
    set (m1 := CatExec.wbytes m (Z_to_bv 64 (S1 - 8)) bs) in VIS2.
    assert (E1 : m1 = write_to_mem m (wa (S1 - 8)) bs) by (subst m1; rewrite wbytes_eq; reflexivity).
    assert (MU1 : munch [(S1 - 8, S1)] m m1).
    { rewrite E1. apply munch_write; [apply munch_refl | lia | rewrite Lbs; cbn; lia | rewrite Lbs; cbn; lia]. }
    assert (WM1 : wmono asegs m m1) by (rewrite E1; apply wmono_write; apply wmono_refl).
    assert (MI1 : mem_inv asegs m1).
    { rewrite E1. apply mem_inv_store; [exact MI|]. rewrite Lbs.
      pose proof (LbB_HEmpN.stack_room_of_stk (S1 + 672) lo m S1 8 ST ltac:(lia) ltac:(lia) ltac:(lia)) as SR0. unfold stack_room in SR0. exact SR0. }
    pose proof (lpre_stack s mo2 m m1 errv' LB' LBm p [(S1 - 8, S1)] ltac:(destruct LP as (MPx & LPr); split;
                  [eapply (ah_mpres_trans H HH); [exact MPx | exact MP2] | exact LPr])
                  MU1 WM1 MI1 ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) as LP1.
    pose proof LP1 as LP10. destruct LP10 as (_ & _ & WS1 & _).
    pose proof WS1 as WS10. destruct WS10 as (W600 & W632 & W656).
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.

    remember (mkR (Z_to_bv 64 E_NPR) (Z_to_bv 64 S1) gp tp (getr R2 5) (getr R2 6) (getr R2 7) s0 (Z_to_bv 64 S1)
                  (Z_to_bv 64 n) (getr R2 11) (getr R2 12) (getr R2 13) (getr R2 14) (getr R2 15) (getr R2 16) (getr R2 17)
                  (Z_to_bv 64 (obj + 24)) y19 s4 y21 (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p)
                  (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) wd (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 key)
                  (getr R2 28) (getr R2 29) (getr R2 30) (getr R2 31)) as R3 eqn:HR3.
    pose (E3 := Eseed R3 [Z_to_bv 64 S1; Z_to_bv 64 obj]).
    assert (HR3' : regs_ok E3 (srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32)]) R3).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R3; evs; reflexivity] |]). apply Forall_nil. }
    assert (HK3 : know_ok asegs E3 m1 [KWord (SA (EVar 32) 656) 8 (EVar 33); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672)]).
    { unfold know_ok.
      apply Forall_cons; [kword_cell W656 0%nat (C8 (Z_to_bv 64 obj))|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - SPL SPH; lia | apply Forall_nil]. }
    assert (FHF3 : rfull R3) by (rewrite HR3; apply rfull_mkR).
    xrun_at (PropExec.mkFP F fc) asegs R3 E_NPR m1 (seg_rom asegs) HR3' HK3 10%nat [E_RA] (SCR [] [] []) 50%N.
    { split_scs. }
    readback HR' (msteps_full asegs _ _ Hms FHF3) HR3 HRe3.
    rreg HR' 18%bv G18r. rreg HR' 24%bv G24r. rreg HR' 25%bv G25r. rreg HR' 26%bv G26r. rreg HR' 27%bv G27r.
    rreg HR' 30%bv G30r. rreg HR' 31%bv G31r. rreg HR' 2%bv G2r. rreg HR' 9%bv G9r.
    assert (G18r' : getr R' 18 = Z_to_bv 64 key) by (rewrite G18r, HR3; reflexivity).
    assert (G24r' : getr R' 24 = wd) by (rewrite G24r, HR3; reflexivity).
    assert (G26r' : getr R' 26 = Z_to_bv 64 (obj + 24)) by (rewrite G26r, HR3; reflexivity).
    assert (G27r' : getr R' 27 = Z_to_bv 64 n) by (rewrite G27r, HR3; reflexivity).
    assert (G30r' : getr R' 30 = LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) by (rewrite G30r, HR3; reflexivity).
    assert (G31r' : getr R' 31 = Z_to_bv 64 (2 ^ 60)) by (rewrite G31r, HR3; reflexivity).
    rewrite G18r', G24r', G25r, G26r', G27r', G30r', G31r', G2r, G9r in HRe3. clear G18r G24r G25r G26r G27r G30r G31r G2r G9r.
    eapply (sr_blk_eq H HH); [exact KR2 | exact VIS2 | exact FHF3 | exact Hms | exact HRe3 |].
    intros msF4 mo4 KR4 MP4 VIS4.
    eapply (stage_ra s msF4 mo4 m1 F fc); [exact VIS4 | exact FRZ | exact KR4 | | exact GROW].
    destruct LP1 as (MPx & LPr). split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP4] | exact LPr].
  Qed.

  Lemma lf_nogrow : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y25 y28 y29 : word) (errv' : word) (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 y15 y16 y17
                             y18 y19 s4 y21 (Z_to_bv 64 (hmod key bc)) (Z_to_bv 64 p) wd y25 (Z_to_bv 64 (obj + 24))
                             (Z_to_bv 64 bc) y28 y29 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60)))
                        F (Z_to_bv 64 E_NG) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> LPRE s mo m errv' LB' LBm p -> bc <> 0 -> Zlength ents + 1 <= bc ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y25 y28 y29 errv' LB' LBm p VIS FRZ KR LP Hbc LOAD.
    destruct (lpre_ipre s mo m errv' LB' LBm p LP Hbc LOAD) as (j584 & IP).
    pose proof LP as LP0. dLP LP0.
    pose proof RS as RS0. destruct RS0 as (R408 & R576 & R616 & R624 & R648).
    pose proof WS as WS0. destruct WS0 as (W600 & W632 & W656).
    remember (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 y15 y16 y17
                  y18 y19 s4 y21 (Z_to_bv 64 (hmod key bc)) (Z_to_bv 64 p) wd y25 (Z_to_bv 64 (obj + 24))
                  (Z_to_bv 64 bc) y28 y29 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60))) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 obj]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]). apply Forall_nil. }
    assert (HK : know_ok asegs E m [KWord (SA (EVar 32) 616) 8 (ELit SHBASE); KWord (SA (EVar 32) 656) 8 (EVar 33);
                                    KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672)]).
    { unfold know_ok.
      apply Forall_cons; [kword_cell R616 0%nat (C8 (Z_to_bv 64 SHBASE))|].
      apply Forall_cons; [kword_cell W656 0%nat (C8 (Z_to_bv 64 obj))|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - SPL SPH; lia | apply Forall_nil]. }
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    xrun_at (PropExec.mkFP F fc) asegs R E_NG m (seg_rom asegs) HR HK 10%nat [E_INS] (SCR [] [] []) 50%N.
    { split_scs. }
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 15%bv G15. rreg HR' 25%bv G25. rreg HR' 2%bv G2. rreg HR' 9%bv G9.
    change (getr R' 15 = Z_to_bv 64 SHBASE) in G15.
    rewrite G15, G25, G2, G9 in HRe. clear G15 G25 G2 G9.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (stage_ins H HH gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0 s msF1 mo1 m F fc);
      [unfold ISTATE; exact VIS1 | exact FRZ | exact KR1 |].
    destruct IP as (MPx & IPr). split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP1] | exact IPr].
  Qed.

  Lemma lf_grow : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y25 y28 y29 : word) (errv' : word) (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) (Z_to_bv 64 1) y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 key) y19 s4 y21 y22 (Z_to_bv 64 p) wd y25 (Z_to_bv 64 (obj + 24))
                             (Z_to_bv 64 bc) y28 y29 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60)))
                        F (Z_to_bv 64 E_GR) fc None m (seg_rom asegs) ->
    frm_zero fc -> fholds (PropExec.mkFP F fc) 15 one32 -> fholds (PropExec.mkFP F fc) 14 (ieee (Zlength ents + 1)) ->
    as_AKREL H s (mkCfg msF mo) -> LPRE s mo m errv' LB' LBm p -> (bc = 0 \/ Zlength ents = bc) ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y25 y28 y29 errv' LB' LBm p VIS FRZ H15 H14 KR LP GROW.
    pose proof LP as LP0. dLP LP0.
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U)) as BCR. pose proof (u_load U) as ULD.
    pose proof (LbB_HEmpL.bseq_lt24 bc (u_bseq U) Hlast) as BC24.
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose proof (LbB_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    assert (SZ0 : 0 <= Zlength ents) by (unfold Zlength; lia).
    pose proof WS as WS0. destruct WS0 as (W600 & W632 & W656).
    eapply (ahh_evt_then H HH _ _ s msF _ mo KR VIS
              (gr_fpN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (seg_rom asegs) S1 obj bc (Zlength ents + 1)
                 (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 (sh (obj + 8)))
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) W632 W656 FRZ H15 H14)).
    intros msF1 mo1 KR1 MP1 (F1 & fc1 & v10 & v11 & VIS1 & FZ1).
    rewrite (LbB_HEmpL.grq_nreq bc (Zlength ents) (u_bseq U) SZ0 ULD ltac:(lia)) in VIS1.
    assert (LP1 : LPRE s mo1 m errv' LB' LBm p).
    { destruct LP as (MPx & REST). split; [|exact REST]. eapply (ah_mpres_trans H HH); [exact MPx | exact MP1]. }
    destruct (Z.eq_dec bc 0) as [B0 | B1].
    -
      assert (NQ : LbB_HEmpN.nreq bc = 1) by (rewrite B0; reflexivity).
      rewrite NQ in VIS1.
      remember (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) v10 v11 y12 y13 y14 y15 y16 y17
                    (Z_to_bv 64 key) y19 s4 y21 (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p) wd (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 24))
                    (Z_to_bv 64 1) y28 y29 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60))) as R2 eqn:HR2.
      pose (E2 := Eseed R2 []).
      assert (HR2' : regs_ok E2 (srs sr_id [(27%bv, ELit 1)]) R2).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R2; evs; reflexivity] |]). apply Forall_nil. }
      assert (HK2 : know_ok asegs E2 m []) by constructor.
      assert (FHF2 : rfull R2) by (rewrite HR2; apply rfull_mkR).
      xrun_at (PropExec.mkFP F1 fc1) asegs R2 E_G2 m (seg_rom asegs) HR2' HK2 20%nat [LbB_HNextPrime.NP_A; E_RA] (SCR [] [] []) 50%N.
      { split_scs; try sc_auto1. }
      readback HR' (msteps_full asegs _ _ Hms FHF2) HR2 HRe2.
      rreg HR' 10%bv G10b. rreg HR' 27%bv G27b. rewrite G10b, G27b in HRe2. clear G10b G27b.
      eapply (sr_blk_eq H HH); [exact KR1 | exact VIS1 | exact FHF2 | exact Hms | exact HRe2 |].
      intros msF3 mo3 KR3 MP3 VIS3.
      assert (BN : n = 2) by (rewrite B0; reflexivity).
      eapply (stage_ra s msF3 mo3 m F1 fc1); [rewrite BN; exact VIS3 | exact FZ1 | exact KR3 | | exact GROW].
      destruct LP1 as (MPx & LPr). split; [|exact LPr].
      eapply (ah_mpres_trans H HH); [exact MPx | exact MP3].
    -
      assert (Hsz : Zlength ents = bc) by (destruct GROW as [G|G]; [lia | exact G]).
      assert (Hbc2 : 1 <= bc) by (clear - BCR B1; lia).
      assert (NQ : LbB_HEmpN.nreq bc = np_arg bc) by (unfold LbB_HEmpN.nreq; rewrite (proj2 (Z.eqb_neq bc 0) B1); reflexivity).
      rewrite NQ in VIS1.
      remember (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) v10 v11 y12 y13 y14 y15 y16 y17
                    (Z_to_bv 64 key) y19 s4 y21 (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p) wd (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 24))
                    (Z_to_bv 64 (np_arg bc)) y28 y29 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60))) as R2 eqn:HR2.
      pose (E2 := Eseed R2 [Z_to_bv 64 (np_arg bc)]).
      assert (HR2' : regs_ok E2 (srs sr_id [(27%bv, EVar 32)]) R2).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R2; evs; reflexivity] |]). apply Forall_nil. }
      assert (HK2 : know_ok asegs E2 m []) by constructor.
      assert (FHF2 : rfull R2) by (rewrite HR2; apply rfull_mkR).
      pose proof (LbB_HEmpL.land_odd_even bc ltac:(lia)) as LOE.
      xrun_at (PropExec.mkFP F1 fc1) asegs R2 E_G2 m (seg_rom asegs) HR2' HK2 20%nat [LbB_HNextPrime.NP_A; E_RA] (SCR [true; false] [] []) 50%N.
      { clear - E2 Hbc2 BCR LOE. unfold np_arg in E2. split_scs; try sc_auto1.
        all: cbn [sc_denot]; evs; rewrite ?w_addm by lia; try replace (2 * bc + 1 + -1) with (2 * bc) by lia;
             rewrite ?w_and by lia; rewrite ?LOE; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia. }
      readback HR' (msteps_full asegs _ _ Hms FHF2) HR2 HRe2.
      rreg HR' 1%bv G1. rreg HR' 10%bv G10b. rreg HR' 18%bv G18b. rreg HR' 24%bv G24b. rreg HR' 25%bv G25b.
      rreg HR' 26%bv G26b. rreg HR' 27%bv G27b.
      assert (G18b' : getr R' 18 = Z_to_bv 64 (obj + 24)) by (rewrite G18b, HR2; reflexivity).
      assert (G24b' : getr R' 24 = LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) by (rewrite G24b, HR2; reflexivity).
      assert (G25b' : getr R' 25 = wd) by (rewrite G25b, HR2; reflexivity).
      assert (G26b' : getr R' 26 = Z_to_bv 64 (2 ^ 60)) by (rewrite G26b, HR2; reflexivity).
      assert (G27b' : getr R' 27 = Z_to_bv 64 key) by (rewrite G27b, HR2; reflexivity).
      rewrite G1, G10b, G18b', G24b', G25b', G26b', G27b' in HRe2. clear G18b G24b G25b G26b G27b.
      eapply (sr_blk_eq H HH); [exact KR1 | exact VIS1 | exact FHF2 | exact Hms | exact HRe2 |].
      intros msF3 mo3 KR3 MP3 VIS3.
      eapply (stage_np s msF3 mo3 m F1 fc1); [exact VIS3 | exact FZ1 | exact KR3 | | exact B1 | exact GROW].
      destruct LP1 as (MPx & LPr). split; [|exact LPr].
      eapply (ah_mpres_trans H HH); [exact MPx | exact MP3].
  Qed.

  Definition srLF : list expr := srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32); (24%bv, ELit SHBASE)].
  Definition KNLF : list kentry :=
    [KWord (SA (EVar 32) 648) 8 (EVar 35); KRange (EVar 33) 7241728 (2 ^ 47 - 40); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672)].
  Definition SCR_LF := SCR [] [EVar 34] [].

  Lemma stage_lf : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y26 y28 y29 y30 y31 : word) (errv' : word)
      (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 key) y19 s4 y21 y22 (Z_to_bv 64 p) (Z_to_bv 64 SHBASE) wd y26 (Z_to_bv 64 bc)
                             y28 y29 y30 y31)
                        F (Z_to_bv 64 E_LF) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> LPRE s mo m errv' LB' LBm p ->
    (bc <> 0 -> y22 = Z_to_bv 64 (hmod key bc)) ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y26 y28 y29 y30 y31 errv' LB' LBm p VIS FRZ KR LP Y22.
    pose proof LP as LP0. dLP LP0.
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U)) as BCR. pose proof (u_load U) as ULD.
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose proof (LbB_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    destruct (u_hdr U) as [Cbl Cbc Cp1 Csz Cmlf Cdef].
    assert (GZO : gz m obj 40) by (apply LbB_HEmpI.gzA; [exact ADH | reflexivity]).
    assert (SZ0 : 0 <= Zlength ents) by (unfold Zlength; lia).
    pose proof RS as RS0. destruct RS0 as (R408 & R576 & R616 & R624 & R648).
    remember (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 key) y19 s4 y21 y22 (Z_to_bv 64 p) (Z_to_bv 64 SHBASE) wd y26 (Z_to_bv 64 bc)
                  y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 obj; Z_to_bv 64 (Zlength ents); Z_to_bv 64 (obj - 136)]).
    assert (HR : regs_ok E srLF R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]). apply Forall_nil. }
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    assert (Hrd_sz : sc_denot asegs m E (SCReadBase (SA (EVar 35) 160) 8 false (EVar 34))).
    { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Csz); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
    assert (HK : know_ok asegs E m (kn_fix 20 [E_FLW] SCR_LF E_LF srLF KNLF 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons; [kword_cell R648 0%nat (C8 (Z_to_bv 64 (obj - 136)))|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - OB3 Ho1; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - SPL SPH; lia|].
      clear - GZO Ho0 Ho1 OB3. know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R E_LF m (seg_rom asegs) HR HK 20%nat [E_FLW] SCR_LF 50%N.
    { clear - E Hrd_sz GZO Ho0 Ho1 OB3 BCR KR32 ZLEN SZ0 SPL SPH.
      split_scs; first [exact Hrd_sz | sc_shdj | sc_dj | sc_auto1]. }
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 10%bv G10. rreg HR' 21%bv G21. rreg HR' 26%bv G26. rreg HR' 30%bv G30.
    rreg HR' 2%bv G2. rreg HR' 9%bv G9. rreg HR' 24%bv G24.
    change (getr R' 24 = Z_to_bv 64 SHBASE) in G24.
    rewrite (w_add (Zlength ents) 1) in G10 by lia.
    rewrite (w_add (obj - 136) 168) in G21 by lia. replace (obj - 136 + 168) with (obj + 32) in G21 by lia.
    rewrite (w_add (obj - 136) 160) in G26 by lia. replace (obj - 136 + 160) with (obj + 24) in G26 by lia.
    rewrite (w_add (obj - 136) 160) in G30 by lia. replace (obj - 136 + 160) with (obj + 24) in G30 by lia.
    change (getr R' 30 = LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) in G30.
    rewrite G10, G21, G26, G30, G2, G9, G24 in HRe. clear G10 G21 G26 G30 G2 G9 G24.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.

    pose proof (LbB_HEmpL.bseq_lt24 bc (u_bseq U) Hlast) as BC24.
    unfold cell4, cellw in Cmlf.
    assert (Ho0' : 0 <= obj) by (clear - Ho0; lia).
    eapply (ahh_evt_then H HH _ _ s msF1 _ mo1 KR1 VIS1
              (lf_fpN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (seg_rom asegs) obj (Zlength ents) bc
                 SZ0 ZLEN BC24 Ho0' Ho1 (proj2 Cmlf) FRZ)).
    intros msF2 mo2 KR2 MP2 (F2 & fc2 & a1 & VIS2 & FZ2 & H15 & H14).
    assert (LP2 : LPRE s mo2 m errv' LB' LBm p).
    { destruct LP as (MPx & REST). split; [|exact REST].
      eapply (ah_mpres_trans H HH); [exact MPx | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2]]. }
    destruct ((bc =? 0) || (bc <? Zlength ents + 1)) eqn:GR.
    -
      assert (GROW : bc = 0 \/ Zlength ents = bc).
      { apply orb_true_iff in GR. destruct GR as [G|G]; [left; apply Z.eqb_eq; exact G | right; apply Z.ltb_lt in G; clear - G ULD; lia]. }
      eapply (lf_grow s msF2 mo2 m F2 fc2); [exact VIS2 | exact FZ2 | exact H15 | exact H14 | exact KR2 | exact LP2 | exact GROW].
    -
      apply orb_false_iff in GR. destruct GR as [G0 G1]. apply Z.eqb_neq in G0. apply Z.ltb_ge in G1.
      rewrite (Y22 G0) in VIS2.
      eapply (lf_nogrow s msF2 mo2 m F2 fc2); [exact VIS2 | exact FZ2 | exact KR2 | exact LP2 | exact G0 | clear - G1; lia].
  Qed.
End NtG.
