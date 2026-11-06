(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HExec HLFrame HStep HSysStep TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsStack0 AsWalk CXXRep RtA_Iface LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_Own LbA_MILB
  LbA_PrsStmt LbA_ContStmt LbA_HEmpStmt LbA_HKit LbA_VecT LbA_NtStmt LbA_NtK LbA_NtD LbA_NtI.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_HFind LbA_HEmpD LbA_HEmpI LbA_HEmpS LbA_HEmpI2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E_J2 : Z := 0xf3ca8.

Definition srT : list expr := srs sr_id [(25%bv, EVar 32); (10%bv, EVar 33); (12%bv, EVar 34); (24%bv, ELit SHBASE)].
Definition KNT : list kentry := [KWr (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 33)) (EVar 34)) 0) (ELit 8)].

Section NtI2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.
  Variables (gp tp s0 s3 s4 s6 s7 s9 s11 : word) (S1 : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj key keyp v784 : Z) (ents : list ent).
  Variables (bl bc lo B shi : Z) (m0 : mem) (mo0 : Model).

  Abbreviation IPREx := (IPRE H tp s3 s7 s9 S1 sk0 LB0 LF obj key keyp v784 ents bl bc lo B shi m0 mo0).
  Abbreviation QIx := (QI H gp tp s0 s3 s4 s6 s7 s9 s11 S1 sk0 LB0 LF obj key v784 ents bl bc lo B shi m0 mo0).

  Lemma front_post : forall (s : as_St H) (msF : machine_state) (mo : Model) (m M2 : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y23 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z) (ents2 : list ent) (rehashed : bool) (j904 : word) (W : list (Z * Z)),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 y15 y16 y17
                             y18 s3 s4 y21 s6 y23 (Z_to_bv 64 SHBASE) (Z_to_bv 64 p) (Z_to_bv 64 v784) s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_END) fc None M2 (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPREx s mo m errv' LB' LBm' p bl2 bc2 ents2 rehashed j904 ->
    munch W m M2 -> wmono asegs m M2 -> mem_grows m M2 -> mem_inv asegs M2 -> stk asegs M2 lo (S1 + 1040) ->
    Forall (fun iv => iv = (p, p + 8) \/ iv = (obj + 16, obj + 24) \/ (bl2 <= fst iv /\ snd iv <= bl2 + 8 * bc2)) W ->
    rw_cells asegs M2 p [C8 (Z_to_bv 64 (hdaddr ents2))] -> rw_cells asegs M2 (obj + 16) [C8 (Z_to_bv 64 p)] ->
    (forall i, 0 <= i < bc2 -> exists b', cell8 ASEGS M2 (bl2 + 8 * i) b' /\ bucket_ok obj bc2 ((p, (key, (0, 0, 0))) :: ents2) i b') ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m M2 F fc y1 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y23 y28 y29 y30 y31
      errv' LB' LBm' p bl2 bc2 ents2 rehashed j904 W VIS FRZ KR IP MU2 WM2 MG2 MI2 ST2 FW Cn2 Cs2 CB2.
    destruct IP as (MP & WS & RS & SPL & SPH & V64 & MI & ST & ERR & RA & TPV & ACL & LOS & LFO & U2 & SH2 & PERM2 & BC2 & LOAD & KR32 & AD & WR
                    & P0 & P1 & P16 & PO & PA & NC & ADP & CR3 & CR4 & RH & PE & PM & OWN & XP & RF & AC & S0 & AL).
    pose proof (LbA_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (u_obj_lo U2) as Ho0. pose proof (u_obj_hi U2) as Ho1. pose proof (u_obj_al U2) as Hoal.
    pose proof (u_bl_lo U2 BC2) as Hbl0. pose proof (u_bl_hi U2) as Hbl1. pose proof (u_bl_obj U2 BC2) as Hblo.
    pose proof (LbA_HFind.BSEQ_boundA bc2 (u_bseq U2)) as BCR.
    destruct (u_hdr U2) as [Cbl Cbc Cp1 Csz Cmlf Cdef].
    destruct SH2 as [SHb SHn]. unfold HStmts.t3a, HStmts.t3b, HStmts.t3c in SHb, SHn. cbn [Datatypes.fst Datatypes.snd] in SHb, SHn.
    assert (ZL : Zlength ents2 = Zlength ents) by (unfold Zlength; rewrite (Permutation_length PERM2); reflexivity).
    assert (ZL0 : 0 <= Zlength ents) by (unfold Zlength; lia).
    pose proof (ncells_split _ _ _ _ _ _ _ _ NC) as (NC0 & N8 & N16 & N20 & N24 & N28).
    pose proof PO as PO'. unfold apart in PO', Hblo.
    assert (INBL : In (bl2, 8 * bc2) (umap_blocks 32 bl2 bc2 ents2))
      by (unfold umap_blocks; apply in_app_iff; left; destruct (Z.eqb_spec bc2 0); [lia | left; reflexivity]).
    assert (PBL : p + 32 <= bl2 \/ bl2 + 8 * bc2 <= p) by (pose proof (PA bl2 (8 * bc2) INBL) as Hap; unfold apart in Hap; exact Hap).

    assert (INM : forall q n, In (q, n) (lbl LBm') -> exists qi, In (qi, q, n) LBm' /\ In (qi, q, n) LB'
                   /\ 0 < q /\ q mod 16 = 0 /\ AIMG_TOP <= q /\ q + n <= aceil /\ aapp q n).
    { intros q n Hq. destruct (lbl_in_inv LBm' q n Hq) as (qi & Qi).
      assert (QiL : In (qi, q, n) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact Qi).
      pose proof (ah_blocks H HH _ _ _ _ RH QiL) as (B0 & B16 & Bn & BI & BC & BF & BA).
      cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in B0, B16, Bn, BI, BC, BF, BA.
      exists qi. repeat split; assumption. }
    destruct (INM p 32 (Permutation_in _ (Permutation_sym PM) (or_introl eq_refl))) as (qp & QPm & QPl & _ & _ & PIM & PCE & PAPP).
    destruct (INM bl2 (8 * bc2) (Permutation_in _ (Permutation_sym PM) (or_intror INBL))) as (qbl & QBm & QBl & _ & _ & BIM & BCE & BAPP).
    unfold AIMG_TOP in PIM, BIM.
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).

    assert (FWX : Forall (fun iv => aclient_write_ok H LB' iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv
                        /\ (snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) /\ wmix LBm' S1 (nt_X S1 obj) iv
                        /\ 0x6e6000 <= fst iv /\ snd iv <= aceil
                        /\ (snd iv <= obj + 24 \/ obj + 32 <= fst iv) /\ (snd iv <= p + 8 \/ p + 32 <= fst iv)) W).
    { eapply Forall_impl; [|exact FW]. intros iv [-> | [-> | (Hl & Hh)]].
      - destruct (blk_win H HH LF s LB' m qp p 32 p (p + 8) RH QPl ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4 & W5).
        split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
        split; [right; right; exists qp, p, 32; split; [exact QPm | cbn; lia]|].
        cbn [Datatypes.fst Datatypes.snd]. lia.
      - destruct (LbA_HEmpD.obj_window_ok H HH LF obj LB' m (obj + 16) (obj + 24) RF LFO ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4).
        split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|].
        split; [unfold aapp, aapp_lo, aapp_hi in VA; cbn [Datatypes.fst Datatypes.snd]; lia|].
        split; [right; left; intros a Ha; cbn [rin_ivs nt_X Datatypes.fst Datatypes.snd] in *; left; lia|].
        cbn [Datatypes.fst Datatypes.snd]. unfold AFS_SIZE in *. lia.
      - destruct iv as [a1 a2]. cbn [Datatypes.fst Datatypes.snd] in Hl, Hh |- *.
        destruct (blk_win H HH LF s LB' m qbl bl2 (8 * bc2) a1 a2 RH QBl Hl Hh) as (W1 & W2 & W3 & W4 & W5).
        split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
        split; [right; right; exists qbl, bl2, (8 * bc2); split; [exact QBm | cbn; lia]|].
        lia. }
    assert (F1 : Forall (aclient_write_ok H LB') W) by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 X)).
    assert (F2 : Forall (afs_write_ok H LF) W) by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 (proj2 X))).
    assert (F3 : Forall aconst_ok W) by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 (proj2 (proj2 X)))).
    assert (F4 : Forall stack0_ok W) by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 (proj2 (proj2 (proj2 X))))).
    assert (FAPP : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W)
      by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 (proj2 (proj2 (proj2 (proj2 X)))))).
    assert (FMIX : Forall (wmix LBm' S1 (nt_X S1 obj)) W)
      by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 X))))))).
    assert (FDJ : forall a n, (a + n <= 0x6e6000 \/ aceil <= a \/ (obj + 24 <= a /\ a + n <= obj + 32) \/ (p + 8 <= a /\ a + n <= p + 32)) ->
                  disjoint_from W a n).
    { intros a n Hc. apply LbA_HEmpI2.dj_of_forall. eapply Forall_impl; [|exact FWX].
      intros iv (_ & _ & _ & _ & _ & _ & X1 & X2 & X3 & X4). lia. }
    destruct (client_frame H HH s LB' LF B W m M2 RH RF AC RA MU2 WM2 F1 F2 F3) as (RH2 & RF2 & AC2 & RA2).
    assert (S02 : stack0 M2 lo shi) by (eapply stack0_transport; [exact S0 | exact MU2 | exact WM2 | exact F4]).
    assert (ERR2 : rw_cells asegs M2 (errno_addr tp) [C4 errv']).
    { subst tp. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
      eapply rw_cells_transport; [exact ERR | exact MU2 | exact WM2 | apply FDJ; left; cbn; unfold ATP; lia]. }
    assert (WS2 : WSLOTS s7 s9 S1 obj M2 (Z_to_bv 64 (p / 8 + SHBASE)) s3 (Z_to_bv 64 (obj / 8)) j904).
    { destruct WS as (W816 & W880 & W904 & W1032). unfold WSLOTS. split; [|split; [|split]];
        (eapply rw_cells_transport; [eassumption | exact MU2 | exact WM2 | apply FDJ; right; left; cbn; lia]). }
    assert (R4002 : rw_cells asegs M2 (S1 + 400) [C8 (Z_to_bv 64 (obj + 24))]).
    { destruct RS as (_ & _ & _ & _ & R400 & _). eapply rw_cells_transport; [exact R400 | exact MU2 | exact WM2 | apply FDJ; right; left; cbn; lia]. }
    assert (ADO2 : addressable M2 obj 40)
      by (eapply addressable_transport; [exact AD | exact MU2 | exact WM2 | apply LbA_HEmpI.dsh_app; [exact FAPP | lia | lia | lia]]).
    assert (XP2 : xpres H LB0 S1 (nt_X S1 obj) m0 M2).
    { eapply (xpres_munch_mixed H HH s LB' LB0 LBm' S1 (nt_X S1 obj) W m0 m M2);
        [exact XP | exact RH | exact PE | lia | exact MU2 | exact WM2 | exact FMIX]. }
    assert (CSZ2 : rw_cells asegs M2 (obj + 24) [C8 (Z_to_bv 64 (Zlength ents))]).
    { rewrite <- ZL. eapply rw_cells_transport; [exact (rw_cells_of_cellw8 m (obj + 24) _ Csz ltac:(unfold AIMG_TOP; lia) ltac:(lia)) | exact MU2 | exact WM2 |].
      apply FDJ. right; right; left. cbn. lia. }
    assert (N82 : rw_cells asegs M2 (p + 8) [C8 (Z_to_bv 64 key)])
      by (eapply rw_cells_transport; [exact N8 | exact MU2 | exact WM2 | apply FDJ; right; right; right; cbn; lia]).
    assert (N162 : rw_cells asegs M2 (p + 16) [C4 (Z_to_bv 64 key)])
      by (eapply rw_cells_transport; [exact N16 | exact MU2 | exact WM2 | apply FDJ; right; right; right; cbn; lia]).
    assert (N202 : rw_cells asegs M2 (p + 20) [C4 (Z_to_bv 64 0)])
      by (eapply rw_cells_transport; [exact N20 | exact MU2 | exact WM2 | apply FDJ; right; right; right; cbn; lia]).
    assert (N242 : rw_cells asegs M2 (p + 24) [C4 (Z_to_bv 64 0)])
      by (eapply rw_cells_transport; [exact N24 | exact MU2 | exact WM2 | apply FDJ; right; right; right; cbn; lia]).
    assert (N282 : rw_cells asegs M2 (p + 28) [C4 (Z_to_bv 64 0)])
      by (eapply rw_cells_transport; [exact N28 | exact MU2 | exact WM2 | apply FDJ; right; right; right; cbn; lia]).
    assert (HFP : forall a, umap_foot 32 obj bl2 bc2 ents2 a -> ~ (p <= a < p + 32)).
    { intros a [Ha | [[Hbc Ha] | (q & Hq & Hqa)]] Hpa'.
      - lia.
      - lia.
      - apply in_map_iff in Hq. destruct Hq as ([z [k v]] & Hz & Hin). cbn in Hz. subst z.
        pose proof (PA q 32 ltac:(unfold umap_blocks; apply in_app_iff; right; apply in_map_iff; exists (q, (k, v)); split; [reflexivity | exact Hin])) as Hap.
        unfold apart in Hap. lia. }
    assert (HFR : forall a, umap_foot 32 obj bl2 bc2 ents2 a -> 0 <= a < 2 ^ 47).
    { intros a [Ha | [[Hbc Ha] | (q & Hq & Hqa)]]; [lia | lia |].
      apply in_map_iff in Hq. destruct Hq as ([z [k v]] & Hz & Hin). cbn in Hz. subst z.
      destruct (u_node U2 q k v Hin) as (_ & Hq0 & Hq1 & _). lia. }
    pose proof (proj1 Cp1) as Hfr.
    assert (HU : forall M', munch [(obj + 24, obj + 32)] M2 M' -> wmono asegs M2 M' ->
                   rw_cells asegs M' (obj + 24) [C8 (Z_to_bv 64 (Zlength ents + 1))] ->
                   umapx MI_A 32 (nval32 ASEGS) (lbl LB') M' obj bl2 bc2 ((p, (key, (0, 0, 0))) :: ents2)).
    { intros M' MU' WM' CS'.
      exact (ins_umapx (lbl LB') m M2 obj key p bl2 bc2 [] ents2 U2 BC2 ltac:(cbn [app]; rewrite ZL; lia) KR32 (lbl_in _ _ _ _ QPl) P0 P1 P16 PO PA MG2
        ltac:(intros a Ha Hnp Hnb; cbn [LbA_NtK.lasta] in Hnp; pose proof (HFR a Ha) as Hr; pose proof (HFP a Ha) as Hnp';
              apply MU2; rewrite u64_of_Z by lia; apply LbA_HEmpI2.out_of_forall; eapply Forall_impl; [|exact FW];
              intros iv [-> | [-> | (Hl & Hh)]]; cbn [Datatypes.fst Datatypes.snd]; lia)
        (cellw8_of_rw_cells M2 p (hdaddr ents2) Cn2 Hfr ltac:(lia))
        (cellw8_of_rw_cells M2 (p + 8) key N82 ltac:(lia) ltac:(lia))
        (cellw4_of_rw_cells M2 (p + 16) key N162 KR32 ltac:(lia))
        (cellw4_of_rw_cells M2 (p + 20) 0 N202 ltac:(lia) ltac:(lia))
        (cellw4_of_rw_cells M2 (p + 24) 0 N242 ltac:(lia) ltac:(lia))
        (cellw4_of_rw_cells M2 (p + 28) 0 N282 ltac:(lia) ltac:(lia))
        (cellw8_of_rw_cells M2 (obj + 16) p Cs2 ltac:(lia) ltac:(lia))
        CB2 M' MU'
        (LbA_HEmpI.grows_of_munch_cell M2 M' (obj + 24) _ ltac:(replace (obj + 24 + 8) with (obj + 32) by lia; exact MU') CS'
           ltac:(unfold AIMG_TOP; lia) ltac:(lia))
        ltac:(cbn [app]; rewrite ZL; exact (cellw8_of_rw_cells M' (obj + 24) (Zlength ents + 1) CS' ltac:(lia) ltac:(lia)))). }
    assert (SH2' : umap_sh M2 32 (bl2, bc2, (p, (key, (0, 0, 0))) :: ents2)).
    { unfold umap_sh, HStmts.t3a, HStmts.t3b, HStmts.t3c. cbn [Datatypes.fst Datatypes.snd]. split.
      - intros Hbc. eapply addressable_transport; [exact (SHb Hbc) | exact MU2 | exact WM2 | apply LbA_HEmpI.dsh_app; [exact FAPP | lia | lia | lia]].
      - intros q k v [Hin | Hin].
        + injection Hin as E1 E2 E3. subst q. eapply addressable_transport; [exact ADP | exact MU2 | exact WM2 | apply LbA_HEmpI.dsh_app; [exact FAPP | lia | lia | lia]].
        + destruct (u_node U2 q k v Hin) as (_ & Hq0 & Hq1 & _).
          eapply addressable_transport; [exact (SHn q k v Hin) | exact MU2 | exact WM2 | apply LbA_HEmpI.dsh_app; [exact FAPP | lia | lia | lia]]. }
    assert (NDR : forall q k v, In (q, (k, v)) ((p, (key, (0, 0, 0))) :: ents2) -> 0 <= q /\ q + 32 <= 2 ^ 47).
    { intros q k v [Hin | Hin]; [injection Hin as E1 E2 E3; subst q; lia|]. destruct (u_node U2 q k v Hin) as (_ & Hq0 & Hq1 & _); lia. }
    assert (PM2 : Permutation (lbl LBm') (umap_blocks 32 bl2 bc2 ((p, (key, (0, 0, 0))) :: ents2))).
    { unfold umap_blocks in PM |- *. cbn [map fst] in PM |- *. eapply perm_trans; [exact PM|]. apply Permutation_middle. }
    unfold QI.
    eapply (stage_end H HH gp tp s0 s3 s4 s6 s7 s9 s11 S1 sk0 LB0 LF obj key v784 ents bl bc lo B shi m0 mo0
              s msF mo M2 F fc) with (LB' := LB') (LBm' := LBm') (p := p) (bl' := bl2) (bc' := bc2)
            (l1 := []) (l2 := ents2) (rehashed := rehashed);
      [ exact VIS | exact FRZ | exact KR | exact MP | exact WS2 | exact R4002
      | exact SPL | exact SPH | exact V64 | exact MI2 | exact ST2 | exact ERR2 | exact RA2 | exact TPV
      | exact LFO | exact Hoal | exact CSZ2 | lia | exact HU | exact SH2' | intros _; lia | exact NDR | exact PIM | exact P16 | exact ADO2
      | exact (wr_at_wmono _ _ _ _ WR WM2) | apply perm_skip; exact PERM2
      | exact CR3 | exact CR4 | exact RH2 | exact PE | exact PM2 | exact (lb_own_wmono _ _ _ OWN WM2) | exact XP2
      | exact RF2 | exact AC2 | exact S02 | exact ACL | exact LOS | exact AL ].
  Qed.

  Lemma front_tail : forall (s : as_St H) (msF : machine_state) (mo : Model) (m M1 : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y6 y7 y11 y13 y14 y15 y16 y17 y18 y21 y23 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z) (fn k1 : Z) (v1 : Z * Z * Z) (rest : list ent) (rehashed : bool) (j904 : word),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (hmod k1 bc2)) y11
                             (Z_to_bv 64 bl2) y13 y14 y15 y16 y17 y18 s3 s4 y21 s6 y23 (Z_to_bv 64 SHBASE) (Z_to_bv 64 p) (Z_to_bv 64 v784) s11
                             y28 y29 y30 y31)
                        F (Z_to_bv 64 E_J2) fc None M1 (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPREx s mo m errv' LB' LBm' p bl2 bc2 ((fn, (k1, v1)) :: rest) rehashed j904 ->
    munch [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * hmod key bc2, bl2 + 8 * hmod key bc2 + 8)] m M1 -> wmono asegs m M1 ->
    mem_grows m M1 -> mem_inv asegs M1 -> stk asegs M1 lo (S1 + 1040) ->
    rw_cells asegs M1 p [C8 (Z_to_bv 64 fn)] -> rw_cells asegs M1 (obj + 16) [C8 (Z_to_bv 64 p)] ->
    rw_cells asegs M1 (bl2 + 8 * hmod key bc2) [C8 (Z_to_bv 64 (obj + 16))] ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m M1 F fc y1 y6 y7 y11 y13 y14 y15 y16 y17 y18 y21 y23 y28 y29 y30 y31
      errv' LB' LBm' p bl2 bc2 fn k1 v1 rest rehashed j904 VIS FRZ KR IP MU1 WM1 MG1 MI1 ST1 Cn1 Cs1 Cb1.
    pose proof IP as IP0.
    destruct IP0 as (MP & WS & RS & SPL & SPH & V64 & MI & ST & ERR & RA & TPV & ACL & LOS & LFO & U2 & SH2 & PERM2 & BC2 & LOAD & KR32 & AD & WR
                     & P0 & P1 & P16 & PO & PA & NC & ADP & CR3 & CR4 & RH & PE & PM & OWN & XP & RF & AC & S0 & AL).
    pose proof (LbA_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (u_obj_lo U2) as Ho0. pose proof (u_obj_hi U2) as Ho1.
    pose proof (u_bl_lo U2 BC2) as Hbl0. pose proof (u_bl_hi U2) as Hbl1. pose proof (u_bl_obj U2 BC2) as Hblo. unfold apart in Hblo.
    pose proof (LbA_HFind.BSEQ_boundA bc2 (u_bseq U2)) as BCR.
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
    { apply LbA_HEmpI.gzA; [| rewrite Z.mul_comm, Z_mod_mult; reflexivity].
      eapply addressable_transport; [exact (SHb BC2) | exact MU1 | exact WM1 | apply LbA_HEmpI.dsh_app; [exact FAPP1 | lia | lia | lia]]. }
    assert (WRK : wr_at asegs M1 (bl2 + 8 * idx2) 8)
      by exact (LbA_HEmpD.wr_at_subE M1 bl2 (8 * bc2) (bl2 + 8 * idx2) 8 (wr_at_wmono _ _ _ _ WRB WM1) ltac:(lia) ltac:(lia) ltac:(lia)).
    remember (mkR y1 (Z_to_bv 64 S1) gp tp (LbA_NtD.rShe (Z_to_bv 64 (obj + 24))) y6 y7 s0 (Z_to_bv 64 S1) (Z_to_bv 64 idx2) y11
                  (Z_to_bv 64 bl2) y13 y14 y15 y16 y17 y18 s3 s4 y21 s6 y23 (Z_to_bv 64 SHBASE) (Z_to_bv 64 p) (Z_to_bv 64 v784) s11
                  y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 idx2; Z_to_bv 64 bl2]).
    assert (HR : regs_ok E srT R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]).
      apply Forall_nil. }
    assert (HK : know_ok asegs E M1 (kn_fix 20 [E_END] (SCR [] [] []) E_J2 srT KNT 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WRK | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R E_J2 M1 (seg_rom asegs) HR HK 20%nat [E_END] (SCR [] [] []) 50%N.
    { split_scs; try sc_auto1; try sc_shdj; try sc_dj.
      eapply (sc_flat _ _ _ _ (bl2 + 8 * idx2)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | cbn; lia | lia | cbn; lia]. }
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
    assert (ST2 : stk asegs M2 lo (S1 + 1040)) by (subst M2; apply stk_mem_denot; exact ST1).
    assert (Cb2 : rw_cells asegs M2 bk2 [C8 (Z_to_bv 64 p)]) by (subst M2; rwc_new Hlf WRK).
    assert (Cn2 : rw_cells asegs M2 p [C8 (Z_to_bv 64 fn)])
      by (eapply rw_cells_transport; [exact Cn1 | exact MU12 | exact WM12 | cbn [disjoint_from cells_size csize Z.of_nat]; subst bk2; lia]).
    assert (Cs2 : rw_cells asegs M2 (obj + 16) [C8 (Z_to_bv 64 p)])
      by (eapply rw_cells_transport; [exact Cs1 | exact MU12 | exact WM12 | cbn [disjoint_from cells_size csize Z.of_nat]; subst bk2; lia]).
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 25%bv G25. rreg HR' 24%bv G24. rreg HR' 10%bv G10. rreg HR' 12%bv G12.
    change (Z_to_bv 64 2147450880) with (Z_to_bv 64 SHBASE) in G24. rewrite G25, G24, G10, G12 in HRe.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (front_post s msF1 mo1 m M2 F fc) with
      (W := [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * idx, bl2 + 8 * idx + 8); (bk2, bk2 + 8)]) (ents2 := (fn, (k1, v1)) :: rest);
      [ exact VIS1 | exact FRZ | exact KR1 | | | | | | | | | | ].
    -
      destruct IP as (MPx & IPr). split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP1] | exact IPr].
    - exact (LbA_HEmpI2.munch_app_trans [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * idx, bl2 + 8 * idx + 8)] [(bk2, bk2 + 8)] m M1 M2 MU1 MU12).
    - exact (wmono_trans asegs _ _ _ WM1 WM12).
    - exact (mem_grows_trans _ _ _ MG1 MG12).
    - exact MI2.
    - exact ST2.
    - apply Forall_cons; [left; reflexivity|]. apply Forall_cons; [right; left; reflexivity|].
      apply Forall_cons; [right; right; cbn; lia|]. apply Forall_cons; [right; right; cbn; subst bk2; lia | apply Forall_nil].
    - exact Cn2.
    - exact Cs2.
    -
      intros i Hi. destruct (Z.eq_dec i idx2) as [->|Hne2].
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
