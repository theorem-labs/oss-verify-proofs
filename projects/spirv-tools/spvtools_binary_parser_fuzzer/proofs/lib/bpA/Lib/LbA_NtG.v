(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3 Hoare RefMemcpyLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts HRehashModel HFpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HExec HLFrame HStep HSysStep TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsStack0 AsWalk CXXRep RtA_Iface LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_Own LbA_MILB
  LbA_PrsStmt LbA_ContStmt LbA_HEmpStmt LbA_HKit LbA_HStKit LbA_VecT LbA_NtStmt LbA_NtK LbA_NtRK LbA_NtD LbA_NtI LbA_NtI4
  LbA_NtRL LbA_NtRE LbA_NtRB LbA_NtF.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_HFind LbA_TopKit LbA_HEmpD LbA_HEmpI LbA_HEmpS LbA_HEmpR LbA_HEmpL LbA_HEmpN
  LbA_HEmpI2 LbA_HEmpI3 LbA_HEmpF LbA_HRehB LbA_HNextPrime.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HWord.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E_LF : Z := 0xf368c.
Definition E_FLW : Z := 0xf36bc.
Definition E_BD0 : Z := 0xf36d4.
Definition E_FDIV : Z := 0xf3714.
Definition E_NPR : Z := 0xf374c.
Definition E_RA : Z := 0xf3754.

Section NtG.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHB : asan_rt_hyps_bp H.
  Let HH : asan_rt_hyps H := rt_bp_base H HHB.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.
  Variables (gp tp s0 s3 s4 s6 s7 s9 s11 : word) (S1 : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj key keyp v784 : Z) (ents : list ent).
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
  Hypothesis SPB : S1 + 1040 <= B.
  Hypothesis BR : B < 2 ^ 64.
  Hypothesis SHI : S1 + 1040 <= shi.
  Hypothesis TRK : trace_ok (as_TR H) APC0_FREE (R_DRET :: map snd CH).
  Hypothesis CHH : forall fp ra, In (fp, ra) CH -> S1 + 1056 <= fp.
  #[local] Opaque bseq_next.
  Abbreviation IPREx := (IPRE H tp s3 s7 s9 S1 sk0 LB0 LF obj key keyp v784 ents bl bc lo B shi m0 mo0).

  Abbreviation QIg sk mz := (QI H gp tp s0 s3 s4 s6 s7 s9 s11 S1 sk LB0 LF obj key v784 ents bl bc lo B shi mz mo0).
  Abbreviation QIx := (QIg sk0 m0).

  Lemma QI_mono : forall (s1 : as_St H) (m1 : mem) c,
    QIg s1 m1 c -> as_AL H s1 >= as_AL H sk0 -> xpres H LB0 S1 (nt_X S1 obj) m0 m1 -> QIx c.
  Proof.
    intros s1 m1 c Q AL XP. unfold QI, QF, nt_post in Q |- *.
    destruct Q as (ra' & t0 & t1 & t2 & a0 & a1 & a2 & a4 & a5 & a6 & a7 & s2' & s5' & s7' & t3 & t4 & t5 & t6 & m' & errv' & s' & LB' & LBm'
                   & F' & fc' & p & bl' & bc' & ents' & inserted & rehashed & j816 & j824 & j880 & j904 & Q).
    exists ra', t0, t1, t2, a0, a1, a2, a4, a5, a6, a7, s2', s5', s7', t3, t4, t5, t6, m', errv', s', LB', LBm',
           F', fc', p, bl', bc', ents', inserted, rehashed, j816, j824, j880, j904.
    destruct Q as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20
                & C21 & C22 & C23 & C24 & C25 & C26 & C27 & C28 & C29 & C30).
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - eapply xpres_trans; eassumption.
    - clear - C30 AL. lia.
  Qed.

  Definition LPRE (s : as_St H) (mo : Model) (m : mem) (errv' : word) (LB' LBm : list block) (p : Z) : Prop :=
    as_MPRES H mo0 mo
    /\ WSLOTS s7 s9 S1 obj m (Z_to_bv 64 (p / 8 + SHBASE)) s3 (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key) /\ nt_slots m S1 obj keyp v784
    /\ 2 ^ 45 <= S1 /\ S1 + 1040 <= 2 ^ 47 /\ 0 <= v784 < 2 ^ 64
    /\ mem_inv asegs m /\ stk asegs m lo (S1 + 1040) /\ rw_cells asegs m (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m B
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
    destruct LP as (MP & WS & RS & SPL & SPH & V64 & MI & ST & ERR & RA & U & SH & ADH & WRH & P0 & P47 & P16 & PO & PA & NC & ADPN
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
    pose proof (LbA_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.

    assert (FWK : Forall (fun iv => aclient_write_ok H LB' iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) W).
    { eapply Forall_impl; [|exact FW]. intros [l h] (X1 & X2 & X3). cbn [Datatypes.fst Datatypes.snd] in *.
      destruct (stack_window_ok H LB' LF l h X1 ltac:(unfold AFS_SIZE in *; lia)) as (W1 & W2 & W3).
      split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. left. cbn. unfold AHI_LO. lia. }
    assert (F1 : Forall (aclient_write_ok H LB') W) by (eapply Forall_impl; [|exact FWK]; intros iv X; exact (proj1 X)).
    assert (F2 : Forall (afs_write_ok H LF) W) by (eapply Forall_impl; [|exact FWK]; intros iv X; exact (proj1 (proj2 X))).
    assert (F3 : Forall aconst_ok W) by (eapply Forall_impl; [|exact FWK]; intros iv X; exact (proj1 (proj2 (proj2 X)))).
    assert (F4 : Forall stack0_ok W) by (eapply Forall_impl; [|exact FWK]; intros iv X; exact (proj2 (proj2 (proj2 X)))).
    assert (FDJ : forall a k, a + k <= aceil \/ S1 <= a -> disjoint_from W a k).
    { intros a k Hc. apply LbA_HEmpI2.dj_of_forall. eapply Forall_impl; [|exact FW]. intros iv (X1 & X2 & X3). lia. }
    assert (FSH : forall A k, 0 <= A -> 0 <= k -> A + k <= 2 ^ 47 -> disjoint_from W (sh A) (nsh k)).
    { intros A k HA Hk Hak. apply LbA_HEmpI2.dj_of_forall. eapply Forall_impl; [|exact FW]. intros iv (X1 & X2 & X3).
      pose proof (sh_nsh_high A k HA Hk ltac:(unfold AAPP_HI; lia)) as SN. unfold AHI_LO in SN. lia. }
    destruct (client_frame H HH s LB' LF B W m m1 RH RF AC RA MU WM F1 F2 F3) as (RH1 & RF1 & AC1 & RA1).
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    unfold LPRE.
    split; [exact MP|].
    split; [unfold WSLOTS in WS |- *; destruct WS as (X1 & X2 & X3 & X4); split; [|split; [|split]];
           (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply FDJ; right; lia])|].
    split; [unfold nt_slots in RS |- *; destruct RS as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); repeat match goal with |- _ /\ _ => split end;
           (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply FDJ; right; lia])|].
    split; [exact SPL|]. split; [exact SPH|]. split; [exact V64|].
    split; [exact MI1|].
    split; [eapply LbA_TopKit.stk_wmono; [exact ST | exact WM | lia]|].
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
    { intros a Ha. apply MU. rewrite u64_of_Z by lia. apply LbA_HEmpI2.out_of_forall. eapply Forall_impl; [|exact FW]. intros iv (X1 & X2 & X3). lia. }
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
    intros a Ha. apply MU. rewrite u64_of_Z by lia. apply LbA_HEmpI2.out_of_forall. eapply Forall_impl; [|exact FW]. intros iv (X1 & X2 & X3). lia.
  Qed.

  Definition srRA : list expr :=
    srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 8)); (26%bv, EVar 34); (18%bv, ELit SHBASE)].
  Definition KNRA : list kentry :=
    [KWord (SA (EVar 32) 1032) 8 (EVar 36); KWord (SA (EVar 36) 0) 1 (ELit 0); KRange (EVar 34) 1 (2 ^ 28);
     KRange (EVar 33) 7233536 (2 ^ 47 - 40); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 1040)].

  Lemma stage_ra : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y23 y28 y29 y30 y31 : word) (errv' : word) (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 SHBASE) y19 s4 y21 s6 y23 (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p) (Z_to_bv 64 n) s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_RA) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> LPRE s mo m errv' LB' LBm p -> (bc = 0 \/ Zlength ents = bc) ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y23 y28 y29 y30 y31 errv' LB' LBm p VIS FRZ KR LP GROW.
    pose proof LP as LP0. dLP LP0.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof LOR as LOR'. unfold ANT_STACK, AOPNEW_STACK, AMALLOC_STACK in LOR'.
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1. pose proof (u_obj_al U) as Hoal.
    pose proof (LbA_HFind.BSEQ_boundA bc (u_bseq U)) as BCR.
    destruct (LbA_HEmpR.bseq_next_factsE bc (u_bseq U) Hlast) as (HnB & Hbcn & Hn28 & _).
    assert (Hn0 : 0 < n) by (clear - BCR Hbcn; lia).
    pose proof (LbA_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    destruct (u_hdr U) as [_ Cbc _ _ _ _].
    assert (GZO : gz m obj 40) by (apply LbA_HEmpI.gzA; [exact ADH | reflexivity]).
    pose proof WS as WS0. destruct WS0 as (W816 & W880 & W904 & W1032).

    destruct (LbA_HEmpR.lbl_split LBm p 32 _ PM) as (qp & LBmr & PMs & PMr).
    assert (PEr : Permutation LB' (LB0 ++ (qp, p, 32) :: LBmr)) by (eapply perm_trans; [exact PE | apply Permutation_app_head; exact PMs]).
    assert (QPL : In (qp, p, 32) LB') by (apply (Permutation_in _ (Permutation_sym PEr)); apply in_or_app; right; left; reflexivity).

    remember (mkR y1 (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 SHBASE) y19 s4 y21 s6 y23 (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p) (Z_to_bv 64 n) s11 y28 y29 y30 y31) as R eqn:HR0.
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 obj; Z_to_bv 64 n; Z_to_bv 64 bc; Z_to_bv 64 (sh (obj + 8))]).
    assert (HR : regs_ok E srRA R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; rewrite ?w_add by lia; reflexivity] |]). apply Forall_nil. }
    assert (Hrd_bc : sc_denot asegs m E (SCReadBase (SA (EVar 33) 8) 8 false (EVar 35))).
    { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbc); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
    assert (HK : know_ok asegs E m (kn_fix 20 [AOPNEW] (SCR [false] [EVar 35] []) E_RA srRA KNRA 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons; [kword_cell W1032 0%nat (C8 (Z_to_bv 64 (sh (obj + 8))))|].
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
    rreg HR' 1%bv G1. rreg HR' 10%bv G10. rreg HR' 21%bv G21. rreg HR' 23%bv G23. rreg HR' 24%bv G24. rreg HR' 27%bv G27.
    rreg HR' 2%bv G2. rreg HR' 9%bv G9. rreg HR' 18%bv G18. rreg HR' 26%bv G26.
    change (getr R' 18 = Z_to_bv 64 SHBASE) in G18.
    rewrite (w_mul 8 n) in G10 by lia. rewrite (w_mul 8 n) in G27 by lia. rewrite (w_add obj 8) in G23 by lia.
    assert (G21' : getr R' 21 = s11) by (rewrite G21, HR0; reflexivity).
    assert (G24' : getr R' 24 = LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) by (rewrite G24, HR0; reflexivity).
    rewrite G1, G10, G21', G23, G24', G27, G2, G9, G18, G26 in HRe. clear G21 G24.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.

    assert (AOK : as_alloc_ok H s LB' (8 * n)) by exact (rt_bp_live H HHB s LB' m (8 * n) RH ltac:(lia) RSM RCN RLG).
    assert (CM : as_Cm H (8 * n) <= as_AL H s) by (rewrite (proj2 (rt_bp_cost H HHB) (8 * n)); exact (RICM GROW)).
    eapply (ah_seq H HH).
    { eapply (ah_opnew H HH) with (n := 8 * n) (LB := LB') (lo := lo) (B := B) (errv := errv');
        [ exact VIS1 | exact RH | exact KR1 | exact AOK | exact CM | exact RA
        | rewrite u64_of_Z by lia; lia
        | rewrite u64_of_Z by lia; exact (proj1 (stk_split asegs m lo S1 (S1 + 1040) ST ltac:(lia)))
        | exact ACL | rewrite u64_of_Z by lia; unfold AOPNEW_STACK, AMALLOC_STACK; lia
        | exact ERR | exact MI | exact TPV | rewrite u64_of_Z by lia; exact SP16
        | exact AC | reflexivity | lia ]. }
    intros [msF2 mo2] POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & p8 & junk & pid & s'
                      & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & AP2 & ABR & RH2 & CB2 & ADDR & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    first [rewrite (ret_pc_even R_NEWRET ltac:(unfold R_NEWRET; lia) eq_refl) in VIS2 | rewrite (ret_pc_even 997260 ltac:(lia) eq_refl) in VIS2].
    rewrite u64_of_Z in AP2, ST2 by lia.
    rewrite (proj2 (rt_bp_cost H HHB) (8 * n)) in AL2.

    assert (XP12 : xpres H LB' S1 [] m m2) by exact (xpres_of_apres H _ _ [] _ _ AP2).
    assert (ST2' : stk asegs m2 lo (S1 + 1040)).
    { apply (stk_merge asegs m2 lo S1 (S1 + 1040)); [exact ST2 | | clear - ACL LOR'; lia].
      eapply (apres_stk H); [exact AP2 | exact (proj2 (stk_split asegs m lo S1 (S1 + 1040) ST ltac:(clear - ACL LOR'; lia))) | lia]. }
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
    assert (WS2 : WSLOTS s7 s9 S1 obj m2 (Z_to_bv 64 (p / 8 + SHBASE)) s3 (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key)).
    { unfold WSLOTS in WS |- *. destruct WS as (X1 & X2 & X3 & X4).
      split; [|split; [|split]]; (eapply (apres_rw_cells H); [exact AP2 | eassumption | apply CRS; lia]). }
    assert (RS2 : nt_slots m2 S1 obj keyp v784).
    { unfold nt_slots in RS |- *. destruct RS as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
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
    eapply (ah_mono H HH).
    { eapply (LbA_NtRB.stage_b H HHB gp tp s0 s3 s4 s6 s7 s9 s11 S1 s LB0 LF obj key keyp v784 ents bl bc lo B shi m2 mo0 LB' CH
                U2 Hlast (RICM GROW) OCE LFO ACL LOS LOR TPV KR32 ZLEN SP16 SPB TRK CHH
                s' msF2 mo2 m2 F fc t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' y19 t3' t4' t5' t6' errv2 LB' LBmr pid qp p8 p junk);
        [ exact VIS2 | exact FRZ | exact KR2 | eapply (ah_mpres_trans H HH); [exact MP | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2]]
        | exact WS2 | exact RS2 | exact SPL | exact SPH | exact V64 | exact MI2 | exact ST2' | exact ERR2 | exact RA2
        | intros e He; apply agree_on_refl | apply agree_on_refl
        | intros Hb; exact (SHb Hb) | exact AD2 | intros [q [k v]] He; exact (SHn q k v He) | exact WR2
        | exact RH2 | exact PEr | exact PMr | exact OWN2 | exact CB2 | exact ADDR
        | apply xpres_refl | exact RF2 | exact AC2 | exact S02 | clear - AL2; lia | exact NC2 | exact ADPN2 | exact GROW | exact CHN2 ]. }
    intros c' Q'. eapply (QI_mono s m2 c' Q'); [clear - AL; lia | exact XP2].
  Qed.

  Lemma lpre_ipre : forall s mo m errv' LB' LBm p, LPRE s mo m errv' LB' LBm p -> bc <> 0 -> Zlength ents + 1 <= bc ->
    IPREx s mo m errv' LB' LBm p bl bc ents false (Z_to_bv 64 key).
  Proof.
    intros s mo m errv' LB' LBm p LP Hbc LOAD. dLP LP.
    unfold IPRE.
    split; [exact MP|]. split; [exact WS|]. split; [exact RS|]. split; [exact SPL|]. split; [exact SPH|]. split; [exact V64|].
    split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact RA|]. split; [exact TPV|]. split; [exact ACL|]. split; [exact LOS|].
    split; [exact LFO|]. split; [exact U|]. split; [exact SH|]. split; [apply Permutation_refl|]. split; [exact Hbc|].
    split; [exact LOAD|]. split; [exact KR32|]. split; [exact ADH|]. split; [exact WRH|].
    split; [exact P0|]. split; [exact P47|]. split; [exact P16|]. split; [exact PO|]. split; [exact PA|]. split; [exact NC|].
    split; [exact ADPN|]. split; [intros _; split; reflexivity|]. split; [intros X; discriminate X|].
    split; [exact RH|]. split; [exact PE|]. split; [exact PM|]. split; [exact OWN|]. split; [exact XP|].
    split; [exact RF|]. split; [exact AC|]. split; [exact S0|]. clear - AL. lia.
  Qed.

  Lemma stage_np : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y21 y26 y28 y29 y30 y31 : word) (errv' : word) (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR (Z_to_bv 64 E_NPR) (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1)
                             (Z_to_bv 64 (np_arg bc)) y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 SHBASE) y19 s4 y21 s6 (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p) y26 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 LbA_HNextPrime.NP_A) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> LPRE s mo m errv' LB' LBm p -> bc <> 0 -> (bc = 0 \/ Zlength ents = bc) ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y21 y26 y28 y29 y30 y31 errv' LB' LBm p VIS FRZ KR LP Hbc0 GROW.
    pose proof LP as LP0. dLP LP0.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof LOR as LOR'. unfold ANT_STACK, AOPNEW_STACK, AMALLOC_STACK in LOR'.
    pose proof (LbA_HFind.BSEQ_boundA bc (u_bseq U)) as BCR.
    remember (mkR (Z_to_bv 64 E_NPR) (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1)
                  (Z_to_bv 64 (np_arg bc)) y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 SHBASE) y19 s4 y21 s6 (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p) y26 s11 y28 y29 y30 y31)
      as R eqn:HR0.

    eapply (LbA_HEmpN.np_sr H HH QIx s msF mo R F fc m bc S1 (Z_to_bv 64 E_NPR) KR VIS (u_bseq U) Hbc0);
      [ unfold LbA_HNextPrime.BSEQ_LAST_A; unfold BSEQ_LAST in Hlast; exact Hlast
      | rewrite HR0; reflexivity | rewrite HR0; reflexivity | vm_compute; reflexivity | rewrite HR0; reflexivity
      | exact SP16 | lia | lia
      | apply (LbA_HEmpN.stack_room_of_stk (S1 + 1040) lo); [exact ST | lia | lia | lia] | exact MI | rewrite HR0; apply rfull_mkR | ].
    intros msF2 mo2 R2 KR2 MP2 VIS2 KEPT G10n FR2.

    assert (Q1 : getr R2 1 = Z_to_bv 64 E_NPR) by (rewrite (KEPT 1%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q2 : getr R2 2 = Z_to_bv 64 S1) by (rewrite (KEPT 2%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q3 : getr R2 3 = gp) by (rewrite (KEPT 3%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q4 : getr R2 4 = tp) by (rewrite (KEPT 4%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q8 : getr R2 8 = s0) by (rewrite (KEPT 8%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q9 : getr R2 9 = Z_to_bv 64 S1) by (rewrite (KEPT 9%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q18 : getr R2 18 = Z_to_bv 64 SHBASE) by (rewrite (KEPT 18%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q19 : getr R2 19 = y19) by (rewrite (KEPT 19%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q20 : getr R2 20 = s4) by (rewrite (KEPT 20%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q21 : getr R2 21 = y21) by (rewrite (KEPT 21%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q22 : getr R2 22 = s6) by (rewrite (KEPT 22%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q23 : getr R2 23 = LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) by (rewrite (KEPT 23%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q24 : getr R2 24 = Z_to_bv 64 (obj + 8)) by (rewrite (KEPT 24%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q25 : getr R2 25 = Z_to_bv 64 p) by (rewrite (KEPT 25%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q26 : getr R2 26 = y26) by (rewrite (KEPT 26%bv ltac:(cbn; tauto)), HR0; reflexivity).
    assert (Q27 : getr R2 27 = s11) by (rewrite (KEPT 27%bv ltac:(cbn; tauto)), HR0; reflexivity).
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
      pose proof (LbA_HEmpN.stack_room_of_stk (S1 + 1040) lo m S1 8 ST ltac:(lia) ltac:(lia) ltac:(lia)) as SR0. unfold stack_room in SR0. exact SR0. }
    pose proof (lpre_stack s mo2 m m1 errv' LB' LBm p [(S1 - 8, S1)] ltac:(destruct LP as (MPx & LPr); split;
                  [eapply (ah_mpres_trans H HH); [exact MPx | exact MP2] | exact LPr])
                  MU1 WM1 MI1 ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) as LP1.

    remember (mkR (Z_to_bv 64 E_NPR) (Z_to_bv 64 S1) gp tp (getr R2 5) (getr R2 6) (getr R2 7) s0 (Z_to_bv 64 S1)
                  (Z_to_bv 64 n) (getr R2 11) (getr R2 12) (getr R2 13) (getr R2 14) (getr R2 15) (getr R2 16) (getr R2 17)
                  (Z_to_bv 64 SHBASE) y19 s4 y21 s6 (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p) y26 s11
                  (getr R2 28) (getr R2 29) (getr R2 30) (getr R2 31)) as R3 eqn:HR3.
    pose (E3 := Eseed R3 []).
    assert (HR3' : regs_ok E3 (srs sr_id []) R3) by (apply regs_ok_srs; [apply regs_ok_seed | apply Forall_nil]).
    assert (HK3 : know_ok asegs E3 m1 []) by constructor.
    assert (FHF3 : rfull R3) by (rewrite HR3; apply rfull_mkR).
    xrun_at (PropExec.mkFP F fc) asegs R3 E_NPR m1 (seg_rom asegs) HR3' HK3 10%nat [E_RA] (SCR [] [] []) 50%N.
    { split_scs. }
    readback HR' (msteps_full asegs _ _ Hms FHF3) HR3 HRe3.
    rreg HR' 5%bv G5r. rreg HR' 26%bv G26r.
    assert (G5r' : getr R' 5 = LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) by (rewrite G5r, HR3; reflexivity).
    assert (G26r' : getr R' 26 = Z_to_bv 64 n) by (rewrite G26r, HR3; reflexivity).
    rewrite G5r', G26r' in HRe3. clear G5r G26r.
    eapply (sr_blk_eq H HH); [exact KR2 | exact VIS2 | exact FHF3 | exact Hms | exact HRe3 |].
    intros msF4 mo4 KR4 MP4 VIS4.
    eapply (stage_ra s msF4 mo4 m1 F fc); [exact VIS4 | exact FRZ | exact KR4 | | exact GROW].
    destruct LP1 as (MPx & LPr). split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP4] | exact LPr].
  Qed.

  Lemma lf_nogrow : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y6 y7 y11 y12 y14 y15 y16 y17 y19 y21 y24 y28 y29 y30 y31 : word) (errv' : word) (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1)
                             (Z_to_bv 64 0) y11 y12 (Z_to_bv 64 (obj + 32)) y14 y15 y16 y17
                             (Z_to_bv 64 SHBASE) y19 s4 y21 s6 (Z_to_bv 64 bc) y24 (Z_to_bv 64 p) (Z_to_bv 64 (hmod key bc)) s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_BD0) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> LPRE s mo m errv' LB' LBm p -> bc <> 0 -> Zlength ents + 1 <= bc ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y6 y7 y11 y12 y14 y15 y16 y17 y19 y21 y24 y28 y29 y30 y31 errv' LB' LBm p VIS FRZ KR LP Hbc LOAD.
    pose proof (lpre_ipre s mo m errv' LB' LBm p LP Hbc LOAD) as IP.
    pose proof LP as LP0. dLP LP0.
    pose proof (LbA_HFind.BSEQ_boundA bc (u_bseq U)) as BCR. pose proof (LbA_HEmpL.bseq_lt24 bc (u_bseq U) Hlast) as BC24.
    remember (mkR y1 (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1)
                  (Z_to_bv 64 0) y11 y12 (Z_to_bv 64 (obj + 32)) y14 y15 y16 y17
                  (Z_to_bv 64 SHBASE) y19 s4 y21 s6 (Z_to_bv 64 bc) y24 (Z_to_bv 64 p) (Z_to_bv 64 (hmod key bc)) s11 y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 bc]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (23%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]). apply Forall_nil. }
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 28)]).
    { unfold know_ok. apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - Hbc BCR BC24; lia | apply Forall_nil]. }
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    xrun_at (PropExec.mkFP F fc) asegs R E_BD0 m (seg_rom asegs) HR HK 10%nat [E_INS; E_FDIV] (SCR [] [] []) 50%N.
    { split_scs. }
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 10%bv G10. rreg HR' 23%bv G23. rewrite G10, G23 in HRe. clear G10 G23.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (stage_ins H HH gp tp s0 s3 s4 s6 s7 s9 s11 S1 sk0 LB0 LF obj key keyp v784 ents bl bc lo B shi m0 mo0 s msF1 mo1 m F fc);
      [unfold ISTATE; exact VIS1 | exact FRZ | exact KR1 |].
    destruct IP as (MPx & IPr). split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP1] | exact IPr].
  Qed.

  Lemma lf_grow3 : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y6 y7 y11 y12 y14 y15 y16 y17 y19 y21 y24 y26 y28 y29 y30 y31 : word) (errv' : word) (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1)
                             (Z_to_bv 64 1) y11 y12 (Z_to_bv 64 (obj + 32)) y14 y15 y16 y17
                             (Z_to_bv 64 SHBASE) y19 s4 y21 s6 (Z_to_bv 64 bc) y24 (Z_to_bv 64 p) y26 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_BD0) fc None m (seg_rom asegs) ->
    frm_zero fc -> fholds (PropExec.mkFP F fc) 15 one32 -> fholds (PropExec.mkFP F fc) 14 (ieee (Zlength ents + 1)) ->
    as_AKREL H s (mkCfg msF mo) -> LPRE s mo m errv' LB' LBm p -> 3 <= bc -> Zlength ents = bc ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y6 y7 y11 y12 y14 y15 y16 y17 y19 y21 y24 y26 y28 y29 y30 y31 errv' LB' LBm p VIS FRZ H15 H14 KR LP Hbc3 Hsz.
    pose proof LP as LP0. dLP LP0.
    pose proof (LbA_HFind.BSEQ_boundA bc (u_bseq U)) as BCR.
    pose proof (LbA_HEmpI3.bseq_pow2E bc (u_bseq U) ltac:(lia)) as [[Hbc2 _] | [Hbcb Hland]]; [lia|].
    replace (bc - 1) with (bc + -1) in Hland by lia. pose proof (LbA_HEmpI3.bseq_land_boundE bc (u_bseq U)) as LANDB.
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose proof RS as RS0. destruct RS0 as (R264 & R312 & R336 & R384 & R400 & R440 & R448 & R784 & R976).
    remember (mkR y1 (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1)
                  (Z_to_bv 64 1) y11 y12 (Z_to_bv 64 (obj + 32)) y14 y15 y16 y17
                  (Z_to_bv 64 SHBASE) y19 s4 y21 s6 (Z_to_bv 64 bc) y24 (Z_to_bv 64 p) y26 s11 y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 obj; Z_to_bv 64 bc]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32); (10%bv, ELit 1); (23%bv, EVar 34); (18%bv, ELit SHBASE)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]). apply Forall_nil. }
    assert (HK : know_ok asegs E m [KRange (EVar 34) 3 (2 ^ 28); KWord (SA (EVar 32) 384) 8 (EAlu ALU_ADD (EVar 33) (ELit 8)); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 1040)]).
    { unfold know_ok. apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - Hbc3 BCR; lia|].
      apply Forall_cons; [| apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - SPL SPH; lia | apply Forall_nil]].
      eapply (kword_of_rw_cells _ _ _ _ _ 0%nat (C8 (Z_to_bv 64 (obj + 8))));
        [ exact R384 | reflexivity | reflexivity | lia
        | unfold SymExec3Sound.SX2S.estart; HLib.evs; rewrite ?HLib.u64_of_Z by lia; cbn [SymExec3.SX2.a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
        | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
        | cbn [cbytes]; evs; rewrite w_add by lia; reflexivity ]. }
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    xrun_at (PropExec.mkFP F fc) asegs R E_BD0 m (seg_rom asegs) HR HK 20%nat [E_INS; E_FDIV] (SCR [] [] []) 50%N.
    { clear - E Hbc3 BCR Hland LANDB SPL SPH. split_scs; try sc_auto1; sc_dj. }
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 10%bv G10. rreg HR' 24%bv G24. rreg HR' 26%bv G26.
    rreg HR' 2%bv G2. rreg HR' 9%bv G9. rreg HR' 18%bv G18. rreg HR' 23%bv G23.
    change (getr R' 18 = Z_to_bv 64 SHBASE) in G18.
    assert (Hsl : Z.ltb 0 (Z.land bc (bc + -1)) = true) by (apply Z.ltb_lt; pose proof (Z.land_nonneg bc (bc + -1)); lia).
    assert (G26' : getr R' 26 = Z_to_bv 64 (np_arg bc)).
    { rewrite G26. rewrite w_addm, w_and by lia. rewrite LbA_HEmpL.w_sltuE by lia. rewrite Hsl. rewrite w_mul by lia. rewrite w_add by lia. reflexivity. }
    rewrite (w_mul 2 bc) in G10 by lia. rewrite (w_add obj 8) in G24 by lia.
    rewrite G10, G24, G26', G2, G9, G18, G23 in HRe. clear G26 G26'.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.

    eapply (ahh_evt_then H HH _ _ s msF1 _ mo1 KR1 VIS1
              (gr_fpN E_FDIV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (seg_rom asegs) (Zlength ents)
                 F_f3704 F_f3708 ltac:(unfold E_FDIV; lia) ltac:(unfold E_FDIV; lia) ltac:(unfold Zlength; lia) ltac:(lia) FRZ H15 H14)).
    intros msF2 mo2 KR2 MP2 (F2 & fc2 & VIS2 & FZ2).
    change (E_FDIV + 8) with 0xf371c in VIS2. rewrite Hsz in VIS2.

    remember (mkR y1 (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1)
                  (Z_to_bv 64 (bc + 1)) (getr R' 11) y12 (Z_to_bv 64 (obj + 32)) y14 y15 y16 y17
                  (Z_to_bv 64 SHBASE) y19 s4 y21 s6 (Z_to_bv 64 bc) (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p) (Z_to_bv 64 (np_arg bc)) s11 y28 y29 y30 y31)
      as R2 eqn:HR2.
    pose (E2 := Eseed R2 [Z_to_bv 64 (np_arg bc); Z_to_bv 64 (bc + 1)]).
    assert (HR2' : regs_ok E2 (srs sr_id [(26%bv, EVar 32); (10%bv, EVar 33)]) R2).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R2; evs; reflexivity] |]). apply Forall_nil. }
    assert (HK2 : know_ok asegs E2 m []) by constructor.
    assert (FHF2 : rfull R2) by (rewrite HR2; apply rfull_mkR).
    pose proof (LbA_HEmpL.land_odd_even bc ltac:(lia)) as LOE.
    xrun_at (PropExec.mkFP F2 fc2) asegs R2 0xf371c m (seg_rom asegs) HR2' HK2 20%nat [LbA_HNextPrime.NP_A; E_RA] (SCR [true; true; false] [] []) 50%N.
    { clear - E2 Hbc3 BCR LOE. unfold np_arg in E2. split_scs; try sc_auto1.
      all: cbn [sc_denot]; evs; rewrite ?w_addm by lia; try replace (2 * bc + 1 + -1) with (2 * bc) by lia;
           rewrite ?w_and by lia; rewrite ?LOE; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia. }
    readback HR'0 (msteps_full asegs _ _ Hms0 FHF2) HR2 HRe2.
    rreg HR'0 1%bv G1. rreg HR'0 10%bv G10b. rreg HR'0 23%bv G23b. rreg HR'0 26%bv G26b.
    assert (G23b' : getr R'0 23 = LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) by (rewrite G23b, HR2; reflexivity).
    rewrite G1, G10b, G23b', G26b in HRe2. clear G23b.
    eapply (sr_blk_eq H HH); [exact KR2 | exact VIS2 | exact FHF2 | exact Hms0 | exact HRe2 |].
    intros msF3 mo3 KR3 MP3 VIS3.
    eapply (stage_np s msF3 mo3 m F2 fc2); [exact VIS3 | exact FZ2 | exact KR3 | | lia | right; exact Hsz].
    destruct LP as (MPx & LPr). split; [|exact LPr].
    eapply (ah_mpres_trans H HH); [exact MPx | eapply (ah_mpres_trans H HH); [exact MP1 | eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3]]].
  Qed.

  Lemma lf_grow2 : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y6 y7 y11 y12 y14 y15 y16 y17 y19 y21 y24 y26 y28 y29 y30 y31 : word) (errv' : word) (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1)
                             (Z_to_bv 64 1) y11 y12 (Z_to_bv 64 (obj + 32)) y14 y15 y16 y17
                             (Z_to_bv 64 SHBASE) y19 s4 y21 s6 (Z_to_bv 64 bc) y24 (Z_to_bv 64 p) y26 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_BD0) fc None m (seg_rom asegs) ->
    frm_zero fc -> fholds (PropExec.mkFP F fc) 15 one32 -> fholds (PropExec.mkFP F fc) 14 (ieee (Zlength ents + 1)) ->
    as_AKREL H s (mkCfg msF mo) -> LPRE s mo m errv' LB' LBm p -> bc < 3 -> (bc = 0 \/ Zlength ents = bc) ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y6 y7 y11 y12 y14 y15 y16 y17 y19 y21 y24 y26 y28 y29 y30 y31 errv' LB' LBm p VIS FRZ H15 H14 KR LP Hbc3 GROW.
    pose proof LP as LP0. dLP LP0.
    pose proof (LbA_HFind.BSEQ_boundA bc (u_bseq U)) as BCR. pose proof (u_load U) as ULD.
    assert (Hbc02 : bc = 0 \/ bc = 2).
    { pose proof (u_bseq U) as Hin. unfold BSEQ in Hin. repeat (destruct Hin as [Hin|Hin]; [lia|]). destruct Hin. }
    assert (Hsz : Zlength ents = bc) by (destruct GROW as [G|G]; [unfold Zlength in *; lia | exact G]).
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose proof RS as RS0. destruct RS0 as (R264 & R312 & R336 & R384 & R400 & R440 & R448 & R784 & R976).
    remember (mkR y1 (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1)
                  (Z_to_bv 64 1) y11 y12 (Z_to_bv 64 (obj + 32)) y14 y15 y16 y17
                  (Z_to_bv 64 SHBASE) y19 s4 y21 s6 (Z_to_bv 64 bc) y24 (Z_to_bv 64 p) y26 s11 y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 obj]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32); (10%bv, ELit 1); (23%bv, ELit bc); (18%bv, ELit SHBASE)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]). apply Forall_nil. }
    assert (HK : know_ok asegs E m [KWord (SA (EVar 32) 384) 8 (EAlu ALU_ADD (EVar 33) (ELit 8)); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 1040)]).
    { unfold know_ok.
      apply Forall_cons; [| apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - SPL SPH; lia | apply Forall_nil]].
      eapply (kword_of_rw_cells _ _ _ _ _ 0%nat (C8 (Z_to_bv 64 (obj + 8))));
        [ exact R384 | reflexivity | reflexivity | lia
        | unfold SymExec3Sound.SX2S.estart; HLib.evs; rewrite ?HLib.u64_of_Z by lia; cbn [SymExec3.SX2.a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
        | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
        | cbn [cbytes]; evs; rewrite w_add by lia; reflexivity ]. }
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    destruct Hbc02 as [B0 | B2].
    -
      rewrite B0 in HR.
      xrun_at (PropExec.mkFP F fc) asegs R E_BD0 m (seg_rom asegs) HR HK 20%nat [E_INS; E_FDIV] (SCR [] [] []) 50%N.
      { clear - E SPL SPH. split_scs; try sc_auto1; sc_dj. }
      readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
      rreg HR' 10%bv G10. rreg HR' 24%bv G24. rreg HR' 26%bv G26.
      rreg HR' 2%bv G2. rreg HR' 9%bv G9. rreg HR' 18%bv G18. rreg HR' 23%bv G23.
      change (getr R' 18 = Z_to_bv 64 SHBASE) in G18. rewrite (w_add obj 8) in G24 by lia.
      rewrite G10, G24, G26, G2, G9, G18, G23 in HRe.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply (ahh_evt_then H HH _ _ s msF1 _ mo1 KR1 VIS1
                (gr_fpN E_FDIV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (seg_rom asegs) (Zlength ents)
                   F_f3704 F_f3708 ltac:(unfold E_FDIV; lia) ltac:(unfold E_FDIV; lia) ltac:(unfold Zlength; lia) ltac:(lia) FRZ H15 H14)).
      intros msF2 mo2 KR2 MP2 (F2 & fc2 & VIS2 & FZ2).
      change (E_FDIV + 8) with 0xf371c in VIS2. rewrite Hsz, B0 in VIS2. change (0 + 1) with 1 in VIS2.
      remember (mkR y1 (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1)
                    (Z_to_bv 64 1) (getr R' 11) y12 (Z_to_bv 64 (obj + 32)) y14 y15 y16 y17
                    (Z_to_bv 64 SHBASE) y19 s4 y21 s6 (Z_to_bv 64 0) (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p) (Z_to_bv 64 1) s11 y28 y29 y30 y31)
        as R2 eqn:HR2.
      pose (E2 := Eseed R2 []).
      assert (HR2' : regs_ok E2 (srs sr_id [(26%bv, ELit 1); (10%bv, ELit 1)]) R2).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R2; evs; reflexivity] |]). apply Forall_nil. }
      assert (HK2 : know_ok asegs E2 m []) by constructor.
      assert (FHF2 : rfull R2) by (rewrite HR2; apply rfull_mkR).
      xrun_at (PropExec.mkFP F2 fc2) asegs R2 0xf371c m (seg_rom asegs) HR2' HK2 20%nat [LbA_HNextPrime.NP_A; E_RA] (SCR [] [] []) 50%N.
      { split_scs; try sc_auto1. }
      readback HR'0 (msteps_full asegs _ _ Hms0 FHF2) HR2 HRe2.
      rreg HR'0 10%bv G10b. rreg HR'0 26%bv G26b. rewrite G10b, G26b in HRe2. clear G10b G26b.
      eapply (sr_blk_eq H HH); [exact KR2 | exact VIS2 | exact FHF2 | exact Hms0 | exact HRe2 |].
      intros msF3 mo3 KR3 MP3 VIS3.
      assert (BN : n = 2) by (rewrite B0; reflexivity).
      eapply (stage_ra s msF3 mo3 m F2 fc2); [rewrite BN; exact VIS3 | exact FZ2 | exact KR3 | | exact GROW].
      destruct LP as (MPx & LPr). split; [|exact LPr].
      eapply (ah_mpres_trans H HH); [exact MPx | eapply (ah_mpres_trans H HH); [exact MP1 | eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3]]].
    -
      rewrite B2 in HR.
      xrun_at (PropExec.mkFP F fc) asegs R E_BD0 m (seg_rom asegs) HR HK 20%nat [E_INS; E_FDIV] (SCR [] [] []) 50%N.
      { clear - E SPL SPH. split_scs; try sc_auto1; sc_dj. }
      readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
      rreg HR' 10%bv G10. rreg HR' 24%bv G24. rreg HR' 26%bv G26.
      rreg HR' 2%bv G2. rreg HR' 9%bv G9. rreg HR' 18%bv G18. rreg HR' 23%bv G23.
      change (getr R' 18 = Z_to_bv 64 SHBASE) in G18. rewrite (w_add obj 8) in G24 by lia.
      rewrite G10, G24, G26, G2, G9, G18, G23 in HRe.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply (ahh_evt_then H HH _ _ s msF1 _ mo1 KR1 VIS1
                (gr_fpN E_FDIV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (seg_rom asegs) (Zlength ents)
                   F_f3704 F_f3708 ltac:(unfold E_FDIV; lia) ltac:(unfold E_FDIV; lia) ltac:(unfold Zlength; lia) ltac:(lia) FRZ H15 H14)).
      intros msF2 mo2 KR2 MP2 (F2 & fc2 & VIS2 & FZ2).
      change (E_FDIV + 8) with 0xf371c in VIS2. rewrite Hsz, B2 in VIS2. change (2 + 1) with 3 in VIS2.
      remember (mkR y1 (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1)
                    (Z_to_bv 64 3) (getr R' 11) y12 (Z_to_bv 64 (obj + 32)) y14 y15 y16 y17
                    (Z_to_bv 64 SHBASE) y19 s4 y21 s6 (Z_to_bv 64 2) (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p) (Z_to_bv 64 5) s11 y28 y29 y30 y31)
        as R2 eqn:HR2.
      pose (E2 := Eseed R2 []).
      assert (HR2' : regs_ok E2 (srs sr_id [(26%bv, ELit 5); (10%bv, ELit 3)]) R2).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R2; evs; reflexivity] |]). apply Forall_nil. }
      assert (HK2 : know_ok asegs E2 m []) by constructor.
      assert (FHF2 : rfull R2) by (rewrite HR2; apply rfull_mkR).
      xrun_at (PropExec.mkFP F2 fc2) asegs R2 0xf371c m (seg_rom asegs) HR2' HK2 20%nat [LbA_HNextPrime.NP_A; E_RA] (SCR [] [] []) 50%N.
      { split_scs; try sc_auto1. }
      readback HR'0 (msteps_full asegs _ _ Hms0 FHF2) HR2 HRe2.
      rreg HR'0 1%bv G1. rreg HR'0 10%bv G10b. rreg HR'0 23%bv G23b. rreg HR'0 26%bv G26b.
      assert (G23b' : getr R'0 23 = LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) by (rewrite G23b, HR2; reflexivity).
      rewrite G1, G10b, G23b', G26b in HRe2. clear G10b G23b G26b.
      eapply (sr_blk_eq H HH); [exact KR2 | exact VIS2 | exact FHF2 | exact Hms0 | exact HRe2 |].
      intros msF3 mo3 KR3 MP3 VIS3.
      assert (BN : np_arg bc = 5) by (rewrite B2; reflexivity).
      eapply (stage_np s msF3 mo3 m F2 fc2); [rewrite BN, B2; exact VIS3 | exact FZ2 | exact KR3 | | lia | exact GROW].
      destruct LP as (MPx & LPr). split; [|exact LPr].
      eapply (ah_mpres_trans H HH); [exact MPx | eapply (ah_mpres_trans H HH); [exact MP1 | eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3]]].
  Qed.

  Definition srLF : list expr := srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32); (18%bv, ELit SHBASE)].
  Definition KNLF : list kentry :=
    [KWord (SA (EVar 32) 400) 8 (EAlu ALU_ADD (EVar 33) (ELit 24)); KWord (SA (EVar 32) 312) 8 (EAlu ALU_ADD (EVar 33) (ELit 32));
     KRange (EVar 33) 7233536 (2 ^ 47 - 40); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 1040)].
  Definition SCR_LF := SCR [] [EVar 34] [].

  Lemma stage_lf : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y24 y26 y28 y29 y30 y31 : word) (errv' : word) (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 SHBASE) y19 s4 y21 s6 (Z_to_bv 64 bc) y24 (Z_to_bv 64 p) y26 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_LF) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> LPRE s mo m errv' LB' LBm p ->
    (bc <> 0 -> y26 = Z_to_bv 64 (hmod key bc)) ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y24 y26 y28 y29 y30 y31 errv' LB' LBm p VIS FRZ KR LP Y26.
    pose proof LP as LP0. dLP LP0.
    pose proof (LbA_HFind.BSEQ_boundA bc (u_bseq U)) as BCR. pose proof (u_load U) as ULD.
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose proof (LbA_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    destruct (u_hdr U) as [Cbl Cbc Cp1 Csz Cmlf Cdef].
    assert (GZO : gz m obj 40) by (apply LbA_HEmpI.gzA; [exact ADH | reflexivity]).
    assert (SZ0 : 0 <= Zlength ents) by (unfold Zlength; lia).
    pose proof RS as RS0. destruct RS0 as (R264 & R312 & R336 & R384 & R400 & R440 & R448 & R784 & R976).
    remember (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 SHBASE) y19 s4 y21 s6 (Z_to_bv 64 bc) y24 (Z_to_bv 64 p) y26 s11 y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 obj; Z_to_bv 64 (Zlength ents)]).
    assert (HR : regs_ok E srLF R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]). apply Forall_nil. }
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    assert (Hrd_sz : sc_denot asegs m E (SCReadBase (SA (EVar 33) 24) 8 false (EVar 34))).
    { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Csz); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
    assert (HK : know_ok asegs E m (kn_fix 20 [E_FLW] SCR_LF E_LF srLF KNLF 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells _ _ _ _ _ 0%nat (C8 (Z_to_bv 64 (obj + 24))));
          [ exact R400 | reflexivity | reflexivity | lia
          | unfold SymExec3Sound.SX2S.estart; HLib.evs; rewrite ?HLib.u64_of_Z by lia; cbn [SymExec3.SX2.a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | cbn [cbytes]; evs; rewrite w_add by lia; reflexivity ]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells _ _ _ _ _ 0%nat (C8 (Z_to_bv 64 (obj + 32))));
          [ exact R312 | reflexivity | reflexivity | lia
          | unfold SymExec3Sound.SX2S.estart; HLib.evs; rewrite ?HLib.u64_of_Z by lia; cbn [SymExec3.SX2.a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | cbn [cbytes]; evs; rewrite w_add by lia; reflexivity ]. }
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - OB3 Ho1; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - SPL SPH; lia|].
      clear - GZO Ho0 Ho1 OB3. know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R E_LF m (seg_rom asegs) HR HK 20%nat [E_FLW] SCR_LF 50%N.
    { clear - E Hrd_sz GZO Ho0 Ho1 OB3 BCR KR32 ZLEN SZ0 SPL SPH.
      split_scs; first [exact Hrd_sz | sc_shdj | sc_dj | sc_auto1]. }
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 5%bv G5. rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 13%bv G13. rreg HR' 19%bv G19.
    rreg HR' 2%bv G2. rreg HR' 9%bv G9. rreg HR' 18%bv G18.
    change (getr R' 18 = Z_to_bv 64 SHBASE) in G18.
    rewrite (w_add obj 24) in G5 by lia. change (getr R' 5 = LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) in G5.
    rewrite (w_add obj 32) in G19 by lia. change (getr R' 19 = LbA_NtD.rShe (Z_to_bv 64 (obj + 32))) in G19.
    rewrite (w_add obj 32) in G13 by lia.
    rewrite G5, G10, G11, G13, G19, G2, G9, G18 in HRe. clear G5 G10 G11 G13 G19 G2 G9 G18.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.

    pose proof (LbA_HEmpL.bseq_lt24 bc (u_bseq U) Hlast) as BC24.
    unfold cell4, cellw in Cmlf.
    assert (BS0 : bc = 0 -> Zlength ents = 0) by (clear - ULD SZ0; lia).
    assert (Ho0' : 0 <= obj) by (clear - Ho0; lia).
    eapply (ahh_evt_then H HH _ _ s msF1 _ mo1 KR1 VIS1
              (lf_fpN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (seg_rom asegs) obj (Zlength ents) bc
                 SZ0 ZLEN BC24 BS0 Ho0' Ho1 (proj2 Cmlf) FRZ)).
    intros msF2 mo2 KR2 MP2 (F2 & fc2 & VIS2 & FZ2 & H15 & H14).
    assert (LP2 : LPRE s mo2 m errv' LB' LBm p).
    { destruct LP as (MPx & REST). split; [|exact REST].
      eapply (ah_mpres_trans H HH); [exact MPx | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2]]. }
    destruct (bc <? Zlength ents + 1) eqn:CMP.
    -
      apply Z.ltb_lt in CMP. assert (Hsz : Zlength ents = bc) by (clear - CMP ULD; lia).
      destruct (Z.le_gt_cases 3 bc) as [Hbc3 | Hbc3].
      + eapply (lf_grow3 s msF2 mo2 m F2 fc2); [exact VIS2 | exact FZ2 | exact H15 | exact H14 | exact KR2 | exact LP2 | exact Hbc3 | exact Hsz].
      + eapply (lf_grow2 s msF2 mo2 m F2 fc2); [exact VIS2 | exact FZ2 | exact H15 | exact H14 | exact KR2 | exact LP2 | clear - Hbc3; lia | right; exact Hsz].
    -
      apply Z.ltb_ge in CMP. assert (Hbc : bc <> 0) by (clear - CMP SZ0; lia).
      rewrite (Y26 Hbc) in VIS2.
      eapply (lf_nogrow s msF2 mo2 m F2 fc2); [exact VIS2 | exact FZ2 | exact KR2 | exact LP2 | exact Hbc | clear - CMP; lia].
  Qed.
End NtG.
