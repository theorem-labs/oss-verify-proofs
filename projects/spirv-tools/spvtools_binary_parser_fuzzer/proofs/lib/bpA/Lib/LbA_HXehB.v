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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts HRehashModel.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HExec HLFrame HStep HSysStep TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsStack0 AsWalk CXXRep RtA_Iface LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_Own LbA_MILB
  LbA_PrsStmt LbA_ContStmt LbA_HEmpStmt LbA_HRehStmt LbA_HKit LbA_VecT LbA_HXmpS LbA_HXmpD LbA_HXmpI LbA_HXmpR LbA_HXmpNd
  LbA_HRehK LbA_HXehD LbA_HXehL LbA_HXehE.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_HFind LbA_TopKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HWord.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition R_NEWRET : Z := 0xfb128.
Definition R_DRET : Z := 0xfb168.

Lemma agree_of_apres {HCEIL : HeapCeil} (H : asr) : forall LB SP m m' a k,
  apres H LB SP m m' -> aclient_range H LB SP a k -> 0 <= a -> a + k <= 2 ^ 64 -> agree_on m m' a k.
Proof.
  intros LB SP m m' a k AP CR Ha Hak i Hi.
  destruct (AP (a + i) ltac:(lia) (aclient_range_addr H _ _ _ _ (a + i) CR ltac:(lia))) as [E _]. exact E.
Qed.

Definition srC : list expr := srs sr_id [(9%bv, EVar 33); (2%bv, EVar 34); (8%bv, EVar 35); (18%bv, EVar 36); (21%bv, EVar 37); (19%bv, EVar 38); (20%bv, ELit SHBASE)].
Definition KNC : list kentry := [KRange (EVar 33) 7233536 (2 ^ 47); KWord (SA (EVar 37) 0) 1 (ELit 0); KWr (SA (EVar 33) 8) (ELit 8)].

Definition srB : list expr := srs sr_id [(10%bv, EVar 32); (9%bv, EVar 33); (2%bv, EVar 34); (8%bv, EVar 35); (18%bv, EVar 36); (20%bv, ELit SHBASE)].
Definition KNB0 : list kentry := [KRange (EVar 33) 7233536 (2 ^ 47); KWr (SA (EVar 33) 0) (ELit 8)].
Definition KNB1 : list kentry := [KRange (EVar 33) 7233536 (2 ^ 47); KWr (SA (EVar 33) 0) (ELit 8); KRange (EVar 37) 1 (2 ^ 47)].
Lemma sh_wordR : forall x, 0 <= x < 2 ^ 64 ->
  alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 2147450880) = Z_to_bv 64 (x / 8 + SHBASE).
Proof.
  intros x Hx. rewrite HWord.w_srl by lia. change (2 ^ 3) with 8.
  assert (0 <= x / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold SHBASE. rewrite w_add by lia. reflexivity.
Qed.
Lemma lbl_perm_splitR : forall (LBs : list block) (l1 l2 : list (Z * Z)),
  Permutation (lbl LBs) (l1 ++ l2) -> exists L1 L2, Permutation LBs (L1 ++ L2) /\ lbl L1 = l1 /\ lbl L2 = l2.
Proof.
  intros LBs l1 l2 P. apply Permutation_sym in P. unfold lbl in P.
  apply Permutation_map_inv in P. destruct P as (l3 & E & P3).
  symmetry in E. apply map_eq_app in E. destruct E as (L1 & L2 & E3 & E1 & E2). subst l3.
  exists L1, L2. split; [exact P3|]. split; [exact E1 | exact E2].
Qed.
Definition keptC : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section RehB.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHB : asan_rt_hyps_bp H.
  Let HH : asan_rt_hyps H := rt_bp_base H HHB.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (spz : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj bl bc : Z) (ents : list (Z * (Z * Z))).
  Variables (lo B shi : Z) (m0 : mem) (mo0 : Model).
  Variables (LBe : list block).
  #[local] Notation n := (bseq_next bc).
  #[local] Notation ent := (Z * (Z * Z))%type.
  #[local] Notation addr := (HRehashModel.addr Z).
  #[local] Notation hkey := (HRehashModel.hkey Z).
  #[local] Notation sent := (obj + 16).

  Hypothesis U0 : umapx MI_A 24 (nval24 ASEGS) (lbl LBe) m0 obj bl bc ents.
  Hypothesis Hlast : bc <> BSEQ_LAST.
  Hypothesis AL0 : ICM (8 * n) <= as_AL H sk0.
  Hypothesis OCE : obj + 40 <= aceil.
  Hypothesis LFO : map_live_frame LF obj.
  Hypothesis ACL : aceil <= lo.
  Hypothesis LOR : lo <= spz - AREH_STACK.
  Hypothesis TPV : tp = Z_to_bv 64 ATP.
  Hypothesis SPB : spz <= B.
  Hypothesis BR : B < 2 ^ 64.
  Hypothesis SHI : spz <= shi.
  #[local] Opaque bseq_next.
  Abbreviation QRx := (QR H ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bc ents lo B shi m0 mo0).

  Lemma stage_c : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (errv : word) (LB' LBn : list block) (pid : bptr) (p : Z) (junk : list byte),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 (spz - 64)) gp tp y5 y6 y7 (Z_to_bv 64 n) (Z_to_bv 64 obj) y10 y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 (8 * n)) (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 SHBASE) (Z_to_bv 64 (obj / 8 + SHBASE))
                             s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 R_DRET) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    RFRAME ra s0 s1 s2 s3 s4 s5 spz m -> spz mod 16 = 0 -> 2 ^ 45 <= spz - 64 -> spz <= 2 ^ 47 -> bv_unsigned ra mod 2 = 0 ->
    mem_inv asegs m -> stk asegs m lo spz -> rw_cells asegs m (errno_addr tp) [C4 errv] -> as_rauxv_ok H m B ->
    (forall e, In e ents -> agree_on m0 m (addr e) 24) -> agree_on m0 m (obj + 16) 24 ->
    cell8 ASEGS m obj p ->
    rw_cells asegs m p [CB (Z.to_nat (8 * n)) junk] ->
    addressable m p (8 * n) -> addressable m obj 40 -> (forall e, In e ents -> addressable m (addr e) 24) ->
    wr_at asegs m obj 40 ->
    as_RHEAP H s LB' m -> Permutation LB' (LB0 ++ (pid, p, 8 * n) :: LBn) -> Permutation (lbl LBn) (map (fun e : ent => (addr e, 24)) ents) ->
    lb_own ((pid, p, 8 * n) :: LBn) m ->
    xpres H LB0 spz [(obj, obj + 40)] m0 m -> as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_AL H s >= as_AL H sk0 - ICM (8 * n) ->
    as_SR H QRx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 errv LB' LBn pid p junk
      VIS FRZ KR MP FR SP16 SPL SPH RAE MI ST ERR RA NODES HDR24 Cbl PBLK ADP ADH ADN WRH RH PE PM OWN XP RF AC S0 AL.
    destruct (bseq_next_factsE bc (u_bseq U0) Hlast) as (HnB & Hbcn & Hn28 & _).
    pose proof (LbA_HFind.BSEQ_boundA bc (u_bseq U0)) as Hbc0.
    assert (Hn0 : 0 < n) by lia.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof LOR as LOR'. unfold AREH_STACK, AOPNEW_STACK, AMALLOC_STACK in LOR'.
    pose proof (u_obj_lo U0) as Ho0. pose proof (u_obj_hi U0) as Ho1. pose proof (u_obj_al U0) as Hoal.
    pose proof (obj_place H HH LF obj m RF LFO) as (OAPP & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof OAPP as HoA. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in HoA.
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    assert (INP : In (pid, p, 8 * n) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; left; reflexivity).
    pose proof (ah_blocks H HH _ _ _ _ RH INP) as (Hp0 & Hp16 & _ & HpI & HpC & HpF & HpA).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Hp0, Hp16, HpI, HpC, HpF, HpA. unfold AIMG_TOP in HpI.
    assert (HPO : apart p (8 * n) obj 40) by (unfold apart; unfold AFS_SIZE in *; clear - HpF OB1 OB2 Hn0; lia).
    assert (GZh : gz m obj 40) by (apply gzA; [exact ADH | reflexivity]).
    unfold RFRAME in FR.

    remember (mkR y1 (Z_to_bv 64 (spz - 64)) gp tp y5 y6 y7 (Z_to_bv 64 n) (Z_to_bv 64 obj) y10 y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 (8 * n)) (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 SHBASE) (Z_to_bv 64 (obj / 8 + SHBASE))
                  s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 obj; Z_to_bv 64 (spz - 64); Z_to_bv 64 n; Z_to_bv 64 (8 * n); Z_to_bv 64 (obj / 8 + SHBASE); Z_to_bv 64 (obj + 8)]).
    assert (HR : regs_ok E srC R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]). apply Forall_nil. }
    assert (Hrd_b : sc_denot asegs m E (SCReadBase (SA (EVar 33) 0) 8 false (EVar 32))).
    { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbl); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
    assert (HK : know_ok asegs E m (kn_fix 20 [AASAN_MEMSET] (SCR [] [EVar 32] []) R_DRET srC KNC 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - OB3 Ho1; lia|].
      apply Forall_cons; [eapply (kshadow0_reg E m (EVar 37) obj); [evs; reflexivity | lia | pose proof (gz_at m obj 40 0 GZh ltac:(lia)) as X0; rewrite Z.add_0_r in X0; exact X0]|].
      apply Forall_cons; [eapply (kwr_of_wr_at asegs E m obj 40); [exact WRH | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]|].
      clear - GZh Ho0 Ho1 OB3. know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R R_DRET m (seg_rom asegs) HR HK 30%nat [AASAN_MEMSET] (SCR [] [EVar 32] []) 50%N.
    { split_scs; first [ exact Hrd_b | sc_shdj | solve [sc_auto1]
                       | (clear - E HoA Ho0 Ho1; cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [edenot a_base a_off];
                          rewrite ?u64_of_Z by (unfold SHBASE; Z.div_mod_to_equations; lia); unfold SHBASE; Z.div_mod_to_equations; lia) ]. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (MU1 : munch [(obj + 8, obj + 16)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
    assert (Cbc1 : rw_cells asegs M1 (obj + 8) [C8 (Z_to_bv 64 n)]).
    { subst M1. rwc_new Hlf (wr_at_subE m obj 40 (obj + 8) 8 WRH ltac:(lia) ltac:(lia) ltac:(lia)). }
    destruct (obj_window_ok H HH LF obj LB' m (obj + 8) (obj + 16) RF LFO ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4).
    destruct (client_frame H HH s LB' LF B [(obj + 8, obj + 16)] m M1 RH RF AC RA MU1 WM1
               (Forall_cons _ _ _ W1 (Forall_nil _)) (Forall_cons _ _ _ W2 (Forall_nil _)) (Forall_cons _ _ _ W3 (Forall_nil _)))
      as (RH1 & RF1 & AC1 & RA1).
    assert (S01 : stack0 M1 lo shi) by (eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact (Forall_cons _ _ _ W4 (Forall_nil _))]).
    assert (XP1 : xpres H LB0 spz [(obj, obj + 40)] m0 M1).
    { eapply (xpres_munch_mixed H HH s LB' LB0 ((pid, p, 8 * n) :: LBn) spz [(obj, obj + 40)] [(obj + 8, obj + 16)] m0 m M1);
        [exact XP | exact RH | exact PE | lia | exact MU1 | exact WM1 |].
      apply Forall_cons; [right; left; intros a Ha; cbn [rin_ivs Datatypes.fst Datatypes.snd] in *; left; lia | apply Forall_nil]. }
    assert (DSH : forall A k, 0 <= A -> 0 <= k -> A + k <= 2 ^ 47 -> disjoint_from [(obj + 8, obj + 16)] (sh A) (nsh k)).
    { intros A k HA Hk HAk. apply dsh_app; [| exact HA | exact Hk | exact HAk]. apply Forall_cons; [cbn [fst snd]; unfold ALOWSH_LO, AHI_LO; clear - HoA; lia | apply Forall_nil]. }
    assert (ADP1 : addressable M1 p (8 * n)) by (eapply addressable_transport; [exact ADP | exact MU1 | exact WM1 | apply DSH; lia]).
    assert (ADH1 : addressable M1 obj 40) by (eapply addressable_transport; [exact ADH | exact MU1 | exact WM1 | apply DSH; lia]).
    assert (ADN1 : forall e, In e ents -> addressable M1 (addr e) 24).
    { intros e He. destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _). eapply addressable_transport; [exact (ADN e He) | exact MU1 | exact WM1 | apply DSH; lia]. }
    assert (FR1 : RFRAME ra s0 s1 s2 s3 s4 s5 spz M1).
    { unfold RFRAME. eapply rw_cells_transport; [exact FR | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Z.of_nat]; clear - OCE ACL LOR'; lia]. }
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
    { assert (EA : errno_addr tp = 7093876) by (rewrite TPV; unfold errno_addr; rewrite u64_of_Z by (unfold ATP; lia); reflexivity).
      rewrite EA in ERR |- *. eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Z.of_nat]; clear - OB3; lia]. }
    assert (PBLK1 : rw_cells asegs M1 p [CB (Z.to_nat (8 * n)) junk]).
    { eapply rw_cells_transport; [exact PBLK | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - HPO; unfold apart in HPO; lia]. }
    assert (NODES1 : forall e, In e ents -> agree_on m0 M1 (addr e) 24).
    { intros e He. destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _).
      destruct (u_node U0 (addr e) (hkey e) (snd (snd e)) ltac:(destruct e as [q [k v]]; exact He)) as (_ & _ & _ & _ & _ & _ & _ & _ & Heo & _).
      eapply agree_on_trans; [exact (NODES e He)|]. eapply agree_of_munch; [exact MU1 | | lia | lia]. intros z Hz. cbn. clear - Hz Heo. unfold apart in Heo. lia. }
    assert (HDR241 : agree_on m0 M1 (obj + 16) 24).
    { eapply agree_on_trans; [exact HDR24|]. eapply agree_of_munch; [exact MU1 | | lia | lia]. intros z Hz. cbn. clear - Hz. lia. }
    assert (Cbl1 : cell8 ASEGS M1 obj p).
    { eapply cellw_agree; [exact Cbl | | lia | cbn; lia]. eapply agree_of_munch; [exact MU1 | | lia | lia]. intros z Hz. cbn. clear - Hz. lia. }
    assert (OWN1 : lb_own ((pid, p, 8 * n) :: LBn) M1) by exact (lb_own_wmono _ _ _ OWN WM1).
    assert (WRH1 : wr_at asegs M1 obj 40) by exact (wr_at_wmono _ _ _ _ WRH WM1).

    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 1%bv G1. rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 12%bv G12.
    rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 18%bv G18. rreg HR' 19%bv G19. rreg HR' 20%bv G20. rreg HR' 21%bv G21.
    change (getr R' 20 = Z_to_bv 64 SHBASE) in G20.
    rewrite G1, G10, G11, G12, G2, G8, G9, G18, G19, G20, G21 in HRe.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.

    pose proof (ah_blk_shvis H HH _ _ _ _ _ _ RH1 INP) as SVP.
    destruct (blk_win H HH LF s LB' M1 pid p (8 * n) p (p + 8 * n) RH1 INP ltac:(lia) ltac:(lia)) as (P1 & P2 & P3 & P4 & P5).
    eapply (ahh_evt_then H HH (amemset_post (Z_to_bv 64 R_MS) (Z_to_bv 64 (spz - 64)) gp tp (Z_to_bv 64 n) (Z_to_bv 64 obj) (Z_to_bv 64 (8 * n))
              (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 SHBASE) (Z_to_bv 64 (obj / 8 + SHBASE)) s6 s7 s8 s9 s10 s11
              F fc (Z_to_bv 64 p) (Z_to_bv 64 (8 * n)) 0 lo M1)); [exact KR1 | exact VIS1 | |].
    { eapply (ah_memset H HH); [reflexivity | lia | | | | | exact ACL | | exact MI1 | exact AC1 | | | |];
        rewrite ?u64_of_Z by lia.
      - exact PBLK1.
      - eapply addressable_accessible; [exact ADP1 | lia | lia | unfold AAPP_HI; lia].
      - exact SVP.
      - exact (proj1 (stk_split asegs M1 lo (spz - 64) spz ST1 ltac:(clear - ACL LOR'; lia))).
      - unfold AINTRIN_STACK. clear - LOR'. lia.
      - lia.
      - unfold in_app_mem. unfold aapp, aapp_lo, aapp_hi in HpA. rewrite ASHADOW_BASE_val. unfold ALOWSH_LO, AHI_LO, AAPP_HI in *. clear - HpA HpC ACF2 Hp0. lia.
      - exact P3.
      - left. clear - HpC ACL. lia. }
    intros msF2 mo2 KR2 MP2 POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & VIS2 & MU2 & WM2 & MI2 & ST2 & ZER & AC2).
    assert (U64p : bv_unsigned (Z_to_bv 64 p) = p) by (apply u64_of_Z; lia).
    assert (U64n : bv_unsigned (Z_to_bv 64 (8 * n)) = 8 * n) by (apply u64_of_Z; lia).
    assert (U64s : bv_unsigned (Z_to_bv 64 (spz - 64)) = spz - 64) by (apply u64_of_Z; lia).
    rewrite ?U64p, ?U64n, ?U64s in MU2. rewrite ?U64p, ?U64n, ?U64s in ST2. rewrite ?U64p, ?U64n, ?U64s in ZER.
    rewrite (ret_pc_even R_MS ltac:(unfold R_MS; lia) eq_refl) in VIS2.

    assert (WA : aclient_write_ok H LB' (spz - 64 - AINTRIN_STACK, spz - 64) /\ afs_write_ok H LF (spz - 64 - AINTRIN_STACK, spz - 64)
                 /\ aconst_ok (spz - 64 - AINTRIN_STACK, spz - 64) /\ stack0_ok (spz - 64 - AINTRIN_STACK, spz - 64)).
    { unfold AINTRIN_STACK. split; [left; cbn; clear - ACL LOR'; lia|].
      split; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; clear - FB1 FB2 ACL LOR' ACF1; unfold AIMG_TOP in FB1; lia|].
      split; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d4c00 by reflexivity; clear - SPL; lia | right; left; clear - SPL; lia]|].
      left. cbn. unfold AHI_LO. clear - SPL. lia. }
    destruct WA as (WA1 & WA2 & WA3 & WA4).
    destruct (client_frame H HH s LB' LF B _ M1 m2 RH1 RF1 AC1 RA1 MU2 WM2
               (Forall_cons _ _ _ P1 (Forall_cons _ _ _ WA1 (Forall_nil _)))
               (Forall_cons _ _ _ P2 (Forall_cons _ _ _ WA2 (Forall_nil _)))
               (Forall_cons _ _ _ P3 (Forall_cons _ _ _ WA3 (Forall_nil _)))) as (RH2 & RF2 & _ & RA2).
    assert (S02 : stack0 m2 lo shi) by (eapply stack0_transport; [exact S01 | exact MU2 | exact WM2 | exact (Forall_cons _ _ _ P4 (Forall_cons _ _ _ WA4 (Forall_nil _)))]).
    assert (XP2 : xpres H LB0 spz [(obj, obj + 40)] m0 m2).
    { eapply (xpres_munch_mixed H HH s LB' LB0 ((pid, p, 8 * n) :: LBn) spz [(obj, obj + 40)] _ m0 M1 m2);
        [exact XP1 | exact RH1 | exact PE | lia | exact MU2 | exact WM2 |].
      apply Forall_cons; [right; right; exists pid, p, (8 * n); split; [left; reflexivity | cbn; lia]|].
      apply Forall_cons; [left; cbn; unfold AINTRIN_STACK; clear - ACL LOR'; lia | apply Forall_nil]. }
    assert (DSH2 : forall A k, 0 <= A -> 0 <= k -> A + k <= 2 ^ 47 -> disjoint_from [(p, p + 8 * n); (spz - 64 - AINTRIN_STACK, spz - 64)] (sh A) (nsh k)).
    { intros A k HA Hk HAk. apply dsh_app; [| exact HA | exact Hk | exact HAk]. unfold ALOWSH_LO, AHI_LO, AINTRIN_STACK.
      pose proof HpA as HpA'. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in HpA'.
      apply Forall_cons; [cbn [fst snd]; clear - HpA'; lia|]. apply Forall_cons; [cbn [fst snd]; clear - SPL; lia | apply Forall_nil]. }
    assert (ADP2 : addressable m2 p (8 * n)) by (eapply addressable_transport; [exact ADP1 | exact MU2 | exact WM2 | apply DSH2; lia]).
    assert (ADH2 : addressable m2 obj 40) by (eapply addressable_transport; [exact ADH1 | exact MU2 | exact WM2 | apply DSH2; lia]).
    assert (ADN2 : forall e, In e ents -> addressable m2 (addr e) 24).
    { intros e He. destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _). eapply addressable_transport; [exact (ADN1 e He) | exact MU2 | exact WM2 | apply DSH2; lia]. }
    assert (FR2 : RFRAME ra s0 s1 s2 s3 s4 s5 spz m2).
    { unfold RFRAME in FR1 |- *. eapply rw_cells_transport; [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Z.of_nat]; unfold AINTRIN_STACK; clear - HpC ACL LOR'; lia]. }
    assert (ERR2 : rw_cells asegs m2 (errno_addr tp) [C4 errv]).
    { assert (EA : errno_addr tp = 7093876) by (rewrite TPV; unfold errno_addr; rewrite u64_of_Z by (unfold ATP; lia); reflexivity).
      rewrite EA in ERR1 |- *. eapply rw_cells_transport; [exact ERR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Z.of_nat]; unfold AINTRIN_STACK; clear - HpI SPL; lia]. }
    assert (OUT2 : forall a k, 0 <= a -> a + k <= aceil -> apart a k p (8 * n) -> agree_on M1 m2 a k).
    { intros a k Ha Hak Hap. eapply agree_of_munch; [exact MU2 | | lia | clear - Hak ACF2; lia]. intros z Hz. cbn. unfold apart in Hap. unfold AINTRIN_STACK. clear - Hz Hap Hak ACL LOR'. lia. }
    assert (NODES2 : forall e, In e ents -> agree_on m0 m2 (addr e) 24).
    { intros e He. destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _).
      destruct (lbl_in_inv LBn (addr e) 24 (Permutation_in _ (Permutation_sym PM) (in_map (fun e0 : ent => (addr e0, 24)) _ _ He))) as (q & Hq).
      assert (HqL : In (q, addr e, 24) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; right; exact Hq).
      pose proof (ah_blocks H HH _ _ _ _ RH HqL) as (_ & _ & _ & _ & QC & _). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in QC.
      assert (Hne : pid <> q).
      { intros <-. pose proof (ah_nodup H HH _ _ _ RH) as NDB.
        assert (ND1 : List.NoDup (map blk_id (LB0 ++ (pid, p, 8 * n) :: LBn))) by (eapply Permutation_NoDup; [apply Permutation_map; exact PE | exact NDB]).
        rewrite map_app in ND1. apply NoDup_app_remove_l in ND1. cbn [map blk_id Datatypes.fst] in ND1.
        inversion ND1 as [|z l Hni Hnd]; subst. apply Hni. apply (in_map blk_id) in Hq. exact Hq. }
      pose proof (ah_disj H HH _ _ _ _ _ RH INP HqL Hne) as D. cbn [blk_addr blk_size blk_id Datatypes.fst Datatypes.snd] in D.
      eapply agree_on_trans; [exact (NODES1 e He) | apply OUT2; [lia | exact QC | unfold apart; clear - D; lia]]. }
    assert (HDR242 : agree_on m0 m2 (obj + 16) 24).
    { eapply agree_on_trans; [exact HDR241 | apply OUT2; [lia | lia | clear - HPO; unfold apart in *; lia]]. }
    assert (Cbl2 : cell8 ASEGS m2 obj p) by (eapply cellw_agree; [exact Cbl1 | apply OUT2; [lia | lia | clear - HPO; unfold apart in *; lia] | lia | cbn; lia]).
    assert (Cbc2 : cell8 ASEGS m2 (obj + 8) n).
    { apply (cellw8_of_rw_cells m2 (obj + 8) n); [| lia | lia].
      eapply rw_cells_transport; [exact Cbc1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Z.of_nat]; unfold AINTRIN_STACK; clear - HPO OCE ACL LOR'; unfold apart in HPO; lia]. }
    assert (OWN2 : lb_own ((pid, p, 8 * n) :: LBn) m2) by exact (lb_own_wmono _ _ _ OWN1 WM2).
    assert (WRH2 : wr_at asegs m2 obj 40) by exact (wr_at_wmono _ _ _ _ WRH1 WM2).
    eapply (stage_post H HHB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc ents lo B shi m0 mo0 LBe
              U0 Hlast OCE LFO ACL LOR TPV s msF2 mo2 m2 F fc);
      [ exact VIS2 | exact FRZ | exact KR2 | eapply (ah_mpres_trans H HH); [exact MP | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2]]
      | exact FR2 | exact SP16 | exact SPL | exact SPH | exact RAE | exact MI2 | | exact ERR2 | exact RA2
      | exact NODES2 | exact HDR242 | exact Cbl2 | exact Cbc2 | exact ZER | exact ADP2 | exact ADH2 | exact ADN2 | exact WRH2
      | exact RH2 | exact PE | exact PM | exact OWN2 | exact XP2 | exact RF2 | exact AC2 | exact S02 | exact AL ].

    pose proof (stk_release asegs m2 lo (spz - 56) _ ltac:(eapply LbA_TopKit.stk_wmono; [exact (proj1 (stk_split asegs M1 lo (spz - 56) spz ST1 ltac:(clear - ACL LOR'; lia))) | exact WM2 | clear - ACL ACF1; lia]) FR2 ltac:(lia)) as X.
    cbn [cells_size csize] in X. replace (spz - 56 + Z.of_nat (8 + (8 + (8 + (8 + (8 + (8 + (8 + 0)))))))) with spz in X by lia. exact X.
  Qed.

  Lemma stage_b : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y21 y28 y29 y30 y31 : word) (errv : word) (LB LBm : list block) (pid : bptr) (p : Z) (junk : list byte),
    as_VIS H s msF = MS (mkR (Z_to_bv 64 R_NEWRET) (Z_to_bv 64 (spz - 64)) gp tp y5 y6 y7 (Z_to_bv 64 n) (Z_to_bv 64 obj) (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 (8 * n)) y19 (Z_to_bv 64 SHBASE) y21 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 R_NEWRET) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    RFRAME ra s0 s1 s2 s3 s4 s5 spz m -> spz mod 16 = 0 -> 2 ^ 45 <= spz - 64 -> spz <= 2 ^ 47 -> bv_unsigned ra mod 2 = 0 ->
    mem_inv asegs m -> stk asegs m lo spz -> rw_cells asegs m (errno_addr tp) [C4 errv] -> as_rauxv_ok H m B ->
    (forall e, In e ents -> agree_on m0 m (addr e) 24) -> agree_on m0 m obj 40 ->
    (bc <> 0 -> addressable m bl (8 * bc)) -> addressable m obj 40 -> (forall e, In e ents -> addressable m (addr e) 24) ->
    wr_at asegs m obj 40 ->
    as_RHEAP H s ((pid, p, 8 * n) :: LB) m -> ~ In pid (map blk_id LB) ->
    Permutation LB (LB0 ++ LBm) -> Permutation (lbl LBm) (umap_blocks 24 bl bc ents) -> lb_own LBm m ->
    rw_cells asegs m p [CB (Z.to_nat (8 * n)) junk] -> addressable m p (8 * n) ->
    xpres H LB0 spz [(obj, obj + 40)] m0 m -> as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_AL H s >= as_AL H sk0 - ICM (8 * n) ->
    trace_ok (as_TR H) APC0_FREE [R_DRET] ->
    as_SR H QRx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y21 y28 y29 y30 y31 errv LB LBm pid p junk
      VIS FRZ KR MP FR SP16 SPL SPH RAE MI ST ERR RA NODES HDR ADB ADH ADN WRH RH NIP PE PM OWN PBLK ADP XP RF AC S0 AL TRK.
    destruct (bseq_next_factsE bc (u_bseq U0) Hlast) as (HnB & Hbcn & Hn28 & _).
    pose proof (LbA_HFind.BSEQ_boundA bc (u_bseq U0)) as Hbc0.
    assert (Hn0 : 0 < n) by lia.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof LOR as LOR'. unfold AREH_STACK, AOPNEW_STACK, AMALLOC_STACK in LOR'.
    pose proof (u_obj_lo U0) as Ho0. pose proof (u_obj_hi U0) as Ho1. pose proof (u_obj_al U0) as Hoal.
    pose proof (obj_place H HH LF obj m RF LFO) as (OAPP & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof OAPP as HoA. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in HoA.
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    pose proof (ah_blocks H HH _ _ _ _ RH (or_introl eq_refl)) as (Hp0 & Hp16 & _ & HpI & HpC & HpF & HpA).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Hp0, Hp16, HpI, HpC, HpF, HpA. unfold AIMG_TOP in HpI.
    assert (HPO : apart p (8 * n) obj 40) by (unfold apart; unfold AFS_SIZE in *; clear - HpF OB1 OB2 Hn0; lia).
    assert (GZh : gz m obj 40) by (apply gzA; [exact ADH | reflexivity]).
    destruct (u_hdr U0) as [Cbl0 Cbc0 _ _ _ _].
    assert (Cbl : cell8 ASEGS m obj bl) by (eapply cellw_agree; [exact Cbl0 | eapply agree_on_sub; [exact HDR | lia | cbn; lia] | lia | cbn; lia]).
    assert (Cbc : cell8 ASEGS m (obj + 8) bc) by (eapply cellw_agree; [exact Cbc0 | eapply agree_on_sub; [exact HDR | lia | cbn; lia] | lia | cbn; lia]).
    pose proof (u_bl_hi U0) as Hbl1.
    unfold RFRAME in FR.
    remember (mkR (Z_to_bv 64 R_NEWRET) (Z_to_bv 64 (spz - 64)) gp tp y5 y6 y7 (Z_to_bv 64 n) (Z_to_bv 64 obj) (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 (8 * n)) y19 (Z_to_bv 64 SHBASE) y21 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) as R eqn:HR0.
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 obj; Z_to_bv 64 (spz - 64); Z_to_bv 64 n; Z_to_bv 64 (8 * n); Z_to_bv 64 bl; Z_to_bv 64 bc]).
    assert (HR : regs_ok E srB R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]). apply Forall_nil. }
    assert (KQ1 : kentry_ok asegs E m (KRange (EVar 33) 7233536 (2 ^ 47))) by (cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - OB3 Ho1; lia).
    assert (KW : kentry_ok asegs E m (KWr (SA (EVar 33) 0) (ELit 8))).
    { eapply (kwr_of_wr_at asegs E m obj 40); [exact WRH | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }

    assert (POST1 : forall lg, log_flat E lg -> log_ivs E lg = [(obj, obj + 8)] ->
              let M1 := mem_denot E m lg in
              munch [(obj, obj + 8)] m M1 /\ wmono asegs m M1 /\ stk asegs M1 lo spz
              /\ as_RHEAP H s ((pid, p, 8 * n) :: LB) M1 /\ as_RFS H LF M1 /\ ACONST M1 /\ as_rauxv_ok H M1 B /\ stack0 M1 lo shi
              /\ xpres H LB0 spz [(obj, obj + 40)] m0 M1
              /\ addressable M1 p (8 * n) /\ addressable M1 obj 40 /\ (forall e, In e ents -> addressable M1 (addr e) 24) /\ (bc <> 0 -> addressable M1 bl (8 * bc))
              /\ rw_cells asegs M1 (spz - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\ rw_cells asegs M1 (errno_addr tp) [C4 errv]
              /\ rw_cells asegs M1 p [CB (Z.to_nat (8 * n)) junk]
              /\ (forall e, In e ents -> agree_on m0 M1 (addr e) 24) /\ agree_on m0 M1 (obj + 16) 24 /\ cell8 ASEGS M1 (obj + 8) bc
              /\ lb_own LBm M1 /\ wr_at asegs M1 obj 40).
    { intros lg Hlf LI M1.
      assert (MU1 : munch [(obj, obj + 8)] m M1) by (subst M1; rewrite <- LI; apply munch_log; exact Hlf).
      assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
      destruct (obj_window_ok H HH LF obj ((pid, p, 8 * n) :: LB) m obj (obj + 8) RF LFO ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4).
      destruct (client_frame H HH s ((pid, p, 8 * n) :: LB) LF B [(obj, obj + 8)] m M1 RH RF AC RA MU1 WM1
                 (Forall_cons _ _ _ W1 (Forall_nil _)) (Forall_cons _ _ _ W2 (Forall_nil _)) (Forall_cons _ _ _ W3 (Forall_nil _)))
        as (RH1 & RF1 & AC1 & RA1).
      assert (DSH : forall A k, 0 <= A -> 0 <= k -> A + k <= 2 ^ 47 -> disjoint_from [(obj, obj + 8)] (sh A) (nsh k)).
      { intros A k HA Hk HAk. apply dsh_app; [| exact HA | exact Hk | exact HAk]. apply Forall_cons; [cbn [fst snd]; unfold ALOWSH_LO, AHI_LO; clear - HoA; lia | apply Forall_nil]. }
      assert (HIN : forall a k, 0 <= a -> a + k <= 2 ^ 64 -> (a + k <= obj \/ obj + 8 <= a) -> agree_on m M1 a k).
      { intros a k Ha Hak Hd. eapply agree_of_munch; [exact MU1 | | lia | lia]. intros z Hz. cbn. clear - Hz Hd. lia. }
      split; [exact MU1|]. split; [exact WM1|]. split; [subst M1; apply stk_mem_denot; exact ST|].
      split; [exact RH1|]. split; [exact RF1|]. split; [exact AC1|]. split; [exact RA1|].
      split; [eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact (Forall_cons _ _ _ W4 (Forall_nil _))]|].
      split.
      { eapply (xpres_munch_mixed H HH s ((pid, p, 8 * n) :: LB) LB0 ((pid, p, 8 * n) :: LBm) spz [(obj, obj + 40)] [(obj, obj + 8)] m0 m M1);
          [exact XP | exact RH | eapply perm_trans; [apply perm_skip; exact PE | apply Permutation_middle] | lia | exact MU1 | exact WM1 |].
        apply Forall_cons; [right; left; intros a Ha; cbn [rin_ivs Datatypes.fst Datatypes.snd] in *; left; lia | apply Forall_nil]. }
      split; [eapply addressable_transport; [exact ADP | exact MU1 | exact WM1 | apply DSH; lia]|].
      split; [eapply addressable_transport; [exact ADH | exact MU1 | exact WM1 | apply DSH; lia]|].
      split; [intros e He; destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _); eapply addressable_transport; [exact (ADN e He) | exact MU1 | exact WM1 | apply DSH; lia]|].
      split; [intros Hbc; pose proof (u_bl_lo U0 Hbc); eapply addressable_transport; [exact (ADB Hbc) | exact MU1 | exact WM1 | apply DSH; lia]|].
      split; [eapply rw_cells_transport; [exact FR | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Z.of_nat]; clear - OCE ACL LOR'; lia]|].
      split.
      { assert (EA : errno_addr tp = 7093876) by (rewrite TPV; unfold errno_addr; rewrite u64_of_Z by (unfold ATP; lia); reflexivity).
        rewrite EA in ERR |- *. eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Z.of_nat]; clear - OB3; lia]. }
      split; [eapply rw_cells_transport; [exact PBLK | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - HPO; unfold apart in HPO; lia]|].
      split.
      { intros e He. destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _).
        destruct (u_node U0 (addr e) (hkey e) (snd (snd e)) ltac:(destruct e as [q [k v]]; exact He)) as (_ & _ & _ & _ & _ & _ & _ & _ & Heo & _).
        eapply agree_on_trans; [exact (NODES e He) | apply HIN; [lia | lia | clear - Heo; unfold apart in Heo; lia]]. }
      split; [eapply agree_on_trans; [eapply agree_on_sub; [exact HDR | lia | lia] | apply HIN; lia]|].
      split; [eapply cellw_agree; [exact Cbc | apply HIN; [lia | lia | cbn; lia] | lia | cbn; lia]|].
      split; [exact (lb_own_wmono _ _ _ OWN WM1) | exact (wr_at_wmono _ _ _ _ WRH WM1)]. }
    destruct (u_blive U0) as [[Hbc Hbl] | [Hbc INB]].
    -
      pose proof (ents_nil_of_bc0 _ _ _ _ _ _ U0 Hbc) as HE.
      assert (Hrd_bl : sc_denot asegs m E (SCReadBase (SA (EVar 33) 0) 8 false (ELit 0))).
      { rewrite Hbl in Cbl. eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbl); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
      assert (HK : know_ok asegs E m (kn_fix 20 [AOPDEL2; R_DRET] (SCR [] [ELit 0] []) R_NEWRET srB KNB0 50)).
      { kn_eval. unfold know_ok. apply Forall_cons; [exact KQ1|]. apply Forall_cons; [exact KW|]. clear - GZh Ho0 Ho1 OB3. know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R R_NEWRET m (seg_rom asegs) HR HK 30%nat [AOPDEL2; R_DRET] (SCR [] [ELit 0] []) 50%N.
      { split_scs; first [exact Hrd_bl | sc_shdj | solve [sc_auto1] | sc_dj]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms;
          destruct (POST1 lg Hlf ltac:(unfold log_ivs; cbn [map e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off a_base Z.of_nat]; f_equal; f_equal; lia))
            as (MU1 & WM1 & ST1 & RH1 & RF1 & AC1 & RA1 & S01 & XP1 & ADP1 & ADH1 & ADN1 & _ & FR1 & ERR1 & PBLK1 & NODES1 & HDR241 & Cbc1 & OWN1 & WRH1)
        end end.
      assert (Cbl1 : cell8 ASEGS M1 obj p).
      { apply (cellw8_of_rw_cells M1 obj p); [| lia | lia]. subst M1. rwc_new Hlf (wr_at_subE m obj 40 obj 8 WRH ltac:(lia) ltac:(lia) ltac:(lia)). }
      readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
      rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 12%bv G12. rreg HR' 19%bv G19. rreg HR' 21%bv G21.
      rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 18%bv G18. rreg HR' 20%bv G20.
      change (getr R' 20 = Z_to_bv 64 SHBASE) in G20.
      rewrite (w_add obj 8) in G19 by lia. rewrite (sh_wordR obj) in G21 by lia.
      rewrite G10, G11, G12, G19, G21, G2, G8, G9, G18, G20 in HRe.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.

      assert (PMn : Permutation (lbl LBm) (map (fun e : ent => (addr e, 24)) ents)).
      { unfold umap_blocks in PM. rewrite Hbc in PM. cbn [Z.eqb app] in PM. exact PM. }
      eapply (stage_c s msF1 mo1 M1 F fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ errv ((pid, p, 8 * n) :: LB) LBm pid p junk);
        [ exact VIS1 | exact FRZ | exact KR1 | eapply (ah_mpres_trans H HH); [exact MP | exact MP1]
        | exact FR1 | exact SP16 | exact SPL | exact SPH | exact RAE | exact (msteps_mem_inv asegs _ _ Hms MI) | exact ST1 | exact ERR1 | exact RA1
        | exact NODES1 | exact HDR241 | exact Cbl1 | exact PBLK1 | exact ADP1 | exact ADH1 | exact ADN1 | exact WRH1
        | exact RH1 | eapply perm_trans; [apply perm_skip; exact PE | apply Permutation_middle]
        | exact PMn | apply lb_own_cons; [cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]; exact (own_of_rw_cells _ _ _ _ PBLK1 ltac:(lia)) | exact OWN1]
        | exact XP1 | exact RF1 | exact AC1 | exact S01 | exact AL ].
    -
      pose proof (u_bl_lo U0 Hbc) as Hbl0.
      unfold umap_blocks in PM. destruct (Z.eqb_spec bc 0) as [|_]; [lia|].
      destruct (lbl_perm_splitR LBm _ _ PM) as (LBk & LBn & PS & EK & EN).
      assert (EKq : exists qb, LBk = [(qb, bl, 8 * bc)]).
      { destruct LBk as [|[[q A] N] [|b LBk']]; cbn in EK; try discriminate EK. injection EK as -> ->. exists q. reflexivity. }
      destruct EKq as (qb & ->). cbn [app] in PS.
      assert (PMn : Permutation (lbl LBn) (map (fun e : ent => (addr e, 24)) ents)) by (rewrite EN; apply Permutation_refl).
      assert (INQm : In (qb, bl, 8 * bc) LBm) by (apply (Permutation_in _ (Permutation_sym PS)); left; reflexivity).
      assert (INQL : In (qb, bl, 8 * bc) LB) by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact INQm).
      assert (INQ : In (qb, bl, 8 * bc) ((pid, p, 8 * n) :: LB)) by (right; exact INQL).
      assert (Hqp : pid <> qb) by (intros ->; apply NIP; apply (in_map blk_id) in INQL; exact INQL).
      assert (PE1 : Permutation ((pid, p, 8 * n) :: LB) ((LB0 ++ [(pid, p, 8 * n)]) ++ (qb, bl, 8 * bc) :: LBn)).
      { rewrite <- app_assoc. cbn [app]. eapply perm_trans; [apply perm_skip; eapply perm_trans; [exact PE | apply Permutation_app_head; exact PS] | apply Permutation_middle]. }
      pose proof (u_bl_obj U0 Hbc) as Hblo.
      assert (Hrd_bl : sc_denot asegs m E (SCReadBase (SA (EVar 33) 0) 8 false (EVar 37))).
      { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbl); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
      assert (Hrd_bc : sc_denot asegs m E (SCReadBase (SA (EVar 33) 8) 8 false (EVar 38))).
      { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbc); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
      assert (HK : know_ok asegs E m (kn_fix 20 [AOPDEL2; R_DRET] (SCR [] [EVar 37; EVar 38] []) R_NEWRET srB KNB1 50)).
      { kn_eval. unfold know_ok. apply Forall_cons; [exact KQ1|]. apply Forall_cons; [exact KW|].
        apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - Hbl0 Hbl1 Hbc0; lia|].
        clear - GZh Ho0 Ho1 OB3. know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R R_NEWRET m (seg_rom asegs) HR HK 40%nat [AOPDEL2; R_DRET] (SCR [] [EVar 37; EVar 38] []) 50%N.
      { split_scs; first [exact Hrd_bl | exact Hrd_bc | sc_shdj | solve [sc_auto1] | sc_dj]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms;
          destruct (POST1 lg Hlf ltac:(unfold log_ivs; cbn [map e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off a_base Z.of_nat]; f_equal; f_equal; lia))
            as (MU1 & WM1 & ST1 & RH1 & RF1 & AC1 & RA1 & S01 & XP1 & ADP1 & ADH1 & ADN1 & ADB1 & FR1 & ERR1 & PBLK1 & NODES1 & HDR241 & Cbc1 & OWN1 & WRH1)
        end end.
      assert (Cbl1 : cell8 ASEGS M1 obj p).
      { apply (cellw8_of_rw_cells M1 obj p); [| lia | lia]. subst M1. rwc_new Hlf (wr_at_subE m obj 40 obj 8 WRH ltac:(lia) ltac:(lia) ltac:(lia)). }
      assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
      readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
      rreg HR' 1%bv G1. rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 19%bv G19. rreg HR' 21%bv G21.
      rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 18%bv G18. rreg HR' 20%bv G20.
      change (getr R' 20 = Z_to_bv 64 SHBASE) in G20.
      rewrite (w_add obj 8) in G19 by lia. rewrite (sh_wordR obj) in G21 by lia. rewrite (w_mul 8 bc) in G11 by lia.
      rewrite G1, G10, G11, G19, G21, G2, G8, G9, G18, G20 in HRe.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.

      destruct (rw_cells_of_own LBm M1 (qb, bl, 8 * bc) OWN1 INQm ltac:(cbn [blk_addr Datatypes.fst Datatypes.snd]; pose proof (ah_blocks H HH _ _ _ _ RH1 INQ) as (_ & _ & _ & BI & _); exact BI) ltac:(cbn [blk_size Datatypes.snd]; lia)) as (obs & OBS).
      cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in OBS.
      eapply (ah_seq H HH).
      { eapply (ah_opdel2 H HH) with (p := qb) (A := bl) (n := 8 * bc) (LB := (pid, p, 8 * n) :: LB) (lo := lo) (B := B) (errv := errv) (CH := [])
          (bs := obs) (sbs := shadow_of (8 * bc));
          [ exact VIS1 | exact RH1 | exact KR1 | exact INQ | rewrite (proj1 (rt_bp_cost H HHB)); clear - AL AL0; lia
          | exact OBS | exact (proj2 (ADB1 Hbc)) | apply shadow_of_length; lia
          | exact RA1 | rewrite u64_of_Z by lia; lia
          | rewrite u64_of_Z by lia; exact (proj1 (stk_split asegs M1 lo (spz - 64) spz ST1 ltac:(clear - ACL LOR'; lia)))
          | exact ACL | rewrite u64_of_Z by lia; unfold AFREE_STACK; clear - LOR'; lia
          | exact ERR1 | exact MI1 | exact TPV | rewrite u64_of_Z by lia; clear - SP16; Z.div_mod_to_equations; lia
          | exact AC1 | apply (ah_chain_nil H HH); left; rewrite u64_of_Z by lia; clear - Hn28 ACF1; lia
          | cbn [map]; rewrite u64_of_Z by (unfold R_DRET; lia); exact TRK
          | reflexivity ]. }
      intros [msF2 mo2] POST.
      destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & s'
                        & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & AP2 & RH2 & AC2 & AL2).
      cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
      rewrite u64_of_Z in ST2, AP2 by lia.
      first [rewrite (ret_pc_even R_DRET ltac:(unfold R_DRET; lia) eq_refl) in VIS2 | rewrite (ret_pc_even 1028456 ltac:(lia) eq_refl) in VIS2].
      rewrite (proj1 (rt_bp_cost H HHB)) in AL2.

      pose proof (ah_lb_remove H HH) as (LR1 & LR2 & LR3).
      assert (LRE : as_lb_remove H qb ((pid, p, 8 * n) :: LB) = (pid, p, 8 * n) :: as_lb_remove H qb LB) by (apply LR2; cbn; exact Hqp).
      rewrite LRE in AP2, RH2.
      assert (NDL : List.NoDup (map blk_id ((pid, p, 8 * n) :: LB))) by exact (ah_nodup H HH _ _ _ RH1).
      pose proof (lb_remove_perm_app H HH _ _ LBn qb bl (8 * bc) NDL PE1) as PE2. rewrite LRE, <- app_assoc in PE2. cbn [app] in PE2.
      assert (INC2 : forall b, In b (LB0 ++ (pid, p, 8 * n) :: LBn) -> In b ((pid, p, 8 * n) :: as_lb_remove H qb LB)) by (intros b Hb; exact (Permutation_in _ (Permutation_sym PE2) Hb)).
      assert (XPA : xpres H ((pid, p, 8 * n) :: as_lb_remove H qb LB) (spz - 64) [] M1 m2) by exact (xpres_of_apres H _ _ [] _ _ AP2).

      assert (CRO : aclient_range H ((pid, p, 8 * n) :: as_lb_remove H qb LB) (spz - 64) obj 40).
      { right; right; right; right; left. unfold AFS_SIZE in *. clear - OB1 OB2. lia. }
      assert (CRN : forall e, In e ents -> aclient_range H ((pid, p, 8 * n) :: as_lb_remove H qb LB) (spz - 64) (addr e) 24).
      { intros e He. destruct (lbl_in_inv LBn (addr e) 24 (Permutation_in _ (Permutation_sym PMn) (in_map (fun e0 : ent => (addr e0, 24)) _ _ He))) as (q & Hq).
        right; right; left. exists (q, addr e, 24). split; [apply INC2; apply in_or_app; right; right; exact Hq | cbn; lia]. }
      assert (CRP : aclient_range H ((pid, p, 8 * n) :: as_lb_remove H qb LB) (spz - 64) p (8 * n)).
      { right; right; left. exists (pid, p, 8 * n). split; [left; reflexivity | cbn; lia]. }
      assert (ST2' : stk asegs m2 lo spz).
      { apply (stk_merge asegs m2 lo (spz - 64) spz); [exact ST2 | | clear - ACL LOR'; lia].
        eapply (apres_stk H); [exact AP2 | exact (proj2 (stk_split asegs M1 lo (spz - 64) spz ST1 ltac:(clear - ACL LOR'; lia))) | lia]. }
      assert (FR2 : RFRAME ra s0 s1 s2 s3 s4 s5 spz m2) by (unfold RFRAME; eapply (apres_rw_cells H); [exact AP2 | exact FR1 | left; lia]).
      assert (NODES2 : forall e, In e ents -> agree_on m0 m2 (addr e) 24).
      { intros e He. destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _).
        eapply agree_on_trans; [exact (NODES1 e He) | eapply (agree_of_apres H); [exact AP2 | exact (CRN e He) | lia | lia]]. }
      assert (HDR242 : agree_on m0 m2 (obj + 16) 24).
      { eapply agree_on_trans; [exact HDR241 | eapply (agree_of_apres H); [exact AP2 | | lia | lia]]. right; right; right; right; left. unfold AFS_SIZE in *. clear - OB1 OB2. lia. }
      assert (Cbl2 : cell8 ASEGS m2 obj p).
      { eapply cellw_agree; [exact Cbl1 | eapply (agree_of_apres H); [exact AP2 | | lia | cbn; lia] | lia | cbn; lia]. right; right; right; right; left. unfold AFS_SIZE in *. clear - OB1 OB2. cbn. lia. }
      assert (PBLK2 : rw_cells asegs m2 p [CB (Z.to_nat (8 * n)) junk]).
      { eapply (apres_rw_cells H); [exact AP2 | exact PBLK1 |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact CRP. }
      assert (ADP2 : addressable m2 p (8 * n)) by (eapply (apres_addressable H); [exact AP2 | exact ADP1 | left; reflexivity]).
      assert (ADN2 : forall e, In e ents -> addressable m2 (addr e) 24).
      { intros e He. destruct (lbl_in_inv LBn (addr e) 24 (Permutation_in _ (Permutation_sym PMn) (in_map (fun e0 : ent => (addr e0, 24)) _ _ He))) as (q & Hq).
        eapply (apres_addressable H); [exact AP2 | exact (ADN1 e He) | apply INC2; apply in_or_app; right; right; exact Hq]. }
      assert (ADH2 : addressable m2 obj 40).
      { destruct ADH1 as [Hn40 SH40]. split; [exact Hn40|]. eapply (apres_SHAD H); [exact AP2 | exact SH40 |].
        rewrite shadow_of_length by lia. right; right; right; right; right; left.
        unfold sh, nsh. rewrite ASHADOW_BASE_val. unfold AFS_SIZE in *. clear - OB1 OB2 Hoal FB3. Z.div_mod_to_equations. lia. }
      assert (WRH2 : wr_at asegs m2 obj 40).
      { eapply xpres_wr_at; [exact XPA | exact WRH1 |]. split; [exact CRO | apply Forall_nil]. }
      assert (RF2 : as_RFS H LF m2) by exact (RFS_via_apres H HH LF _ _ M1 m2 RF1 AP2).
      assert (S02 : stack0 m2 lo shi) by (eapply (stack0_xpres H); [exact XPA | exact S01 | apply Forall_nil]).
      assert (XP2 : xpres H LB0 spz [(obj, obj + 40)] m0 m2).
      { eapply xpres_trans; [exact XP1|]. eapply (xpres_weaken H); [exact XPA | lia | intros b Hb; apply INC2; apply in_or_app; left; exact Hb | intros a Ha; destruct Ha]. }
      assert (OWN2 : lb_own ((pid, p, 8 * n) :: LBn) m2).
      { apply lb_own_cons; [cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]; exact (own_of_rw_cells _ _ _ _ PBLK2 ltac:(lia))|].
        eapply (lb_own_apres H); [eapply lb_own_incl; [| exact OWN1]; intros b Hb; apply (Permutation_in _ (Permutation_sym PS)); right; exact Hb | exact AP2 |].
        intros b Hb. apply INC2. apply in_or_app. right. right. exact Hb. }
      eapply (stage_c s' msF2 mo2 m2 F fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ errv ((pid, p, 8 * n) :: as_lb_remove H qb LB) LBn pid p junk);
        [ exact VIS2 | exact FRZ | exact KR2 | eapply (ah_mpres_trans H HH); [exact MP | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2]]
        | exact FR2 | exact SP16 | exact SPL | exact SPH | exact RAE | exact MI2 | exact ST2' | exact ERR2 | exact RA2
        | exact NODES2 | exact HDR242 | exact Cbl2 | exact PBLK2 | exact ADP2 | exact ADH2 | exact ADN2 | exact WRH2
        | exact RH2 | exact PE2 | exact PMn | exact OWN2 | exact XP2 | exact RF2 | exact AC2 | exact S02 | clear - AL AL2; lia ].
  Qed.
End RehB.
