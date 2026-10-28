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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablGrammar TablFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmInit LbB_PmFin LbB_PmExit2 LbB_DiagStmt LbB_PmDS LbB_PmGlue LbB_PmOL.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RtOwn LbB_DStat LbB_TablStmt LbB_ContStmt LbB_PmLeaf LbB_PmLeafW LbB_PmLH LbB_PmVops LbB_PmVup LbB_PmU2K LbB_PmVC1 LbB_PmVC2 LbB_PmVC3 LbB_PmVP2 LbB_PmVS LbB_PmWG LbB_PmWV4 LbB_PmWPT.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmU2A_F LbB_PmU2A_P LbB_PmU2B_F LbB_PmU2B_S LbB_PmU2C LbB_PmU2Dm LbB_PmU2E LbB_PmU2F LbB_PmU2G LbB_PmU2Dz LbB_PmU2Lz LbB_PiStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma ih_rt_vc2 : rt_subb RT_VC2 RT_F07C8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ih_rt_f0884 : rt_subb RT_F0884 (rt_keepK VC2_KEPT RT_F07C8 ++ RT_VC2R) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ih_tbl_f0884 : tbl_subb TBL_F0884 (vc2_tbl TBL_F07C8) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ih_ck_f07c8 : tbl_closed TBL_F07C8 = true /\ keys_ok (map fst TBL_F07C8) = true /\ keys_nonneg (map fst TBL_F07C8) = true
  /\ tbl_closed FTBL_F07C8 = true /\ fkeys_ok (map fst FTBL_F07C8) = true.
Proof. vm_compute. repeat split. Qed.
Lemma ih_ck_f08ec : tbl_closed TBL_F08EC = true /\ keys_ok (map fst TBL_F08EC) = true /\ keys_nonneg (map fst TBL_F08EC) = true
  /\ tbl_closed [] = true /\ fkeys_ok [] = true.
Proof. vm_compute. repeat split. Qed.
Lemma ih_rt_vc1 : rt_subb RT_VC1 RT_F0950 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ih_rt_f0a20 : rt_subb RT_F0A20 (rt_keepK VC1_KEPT RT_F0950 ++ RT_VC1R) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ih_tbl_f0a20 : tbl_subb TBL_F0A20 (vc1_tbl TBL_F08EC) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ih_ck_f0fb0 : tbl_closed TBL_F0FB0 = true /\ keys_ok (map fst TBL_F0FB0) = true /\ keys_nonneg (map fst TBL_F0FB0) = true
  /\ tbl_closed [] = true /\ fkeys_ok [] = true.
Proof. vm_compute. repeat split. Qed.
Lemma ih_rt_vc3 : rt_subb RT_VC3 RT_F0FB0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ih_rt_f1090 : rt_subb RT_F1090 (rt_keepK VC3_KEPT RT_F0FB0 ++ RT_VC3R) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ih_tbl_f1090 : tbl_subb TBL_F1090 (vc3_tbl TBL_F0FB0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ih_rt_f0920 : rt_subb RT_F0920 (rt_keepK V4_KEPT RT_F091C) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ih_osh : obj_sh_ok [OB_INST; OB_FIRST_WORD] 9120 4 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ih_z224 : forall m A, rw_cells asegs m A [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m A [C2 (Z_to_bv 64 0)] /\ rw_cells asegs m (A + 2) [C2 (Z_to_bv 64 0)]
  /\ rw_cells asegs m (A + 4) [C4 (Z_to_bv 64 0)].
Proof.
  intros m A Z0. apply rw_cells_zero_split224 in Z0.
  change [C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    with ([C2 (Z_to_bv 64 0)] ++ [C2 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 0)]) in Z0.
  apply rw_cells_appA in Z0 as [Z1 Z0]. apply rw_cells_appA in Z0 as [Z2 Z3].
  change (Z.of_nat (cells_size [C2 (Z_to_bv 64 0)])) with 2 in Z2, Z3.
  replace (A + 2 + 2) with (A + 4) in Z3 by lia.
  split; [exact Z1 | split; [exact Z2 | exact Z3]].
Qed.

Lemma ih_z44 : forall m A, rw_cells asegs m A [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m A [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m (A + 4) [C4 (Z_to_bv 64 0)].
Proof.
  intros m A Z0. apply rw_cells_zero_split44 in Z0.
  change [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] with ([C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 0)]) in Z0.
  apply rw_cells_appA in Z0 as [Z1 Z2].
  change (Z.of_nat (cells_size [C4 (Z_to_bv 64 0)])) with 4 in Z2.
  split; [exact Z1 | exact Z2].
Qed.

Definition ih_apart (X : list (Z * Z)) (cells : list (Z * Z)) : bool :=
  forallb (fun kn : Z * Z => forallb (fun on : Z * Z => (fst kn + snd kn <=? fst on) || (fst on + snd on <=? fst kn))%bool X) cells.

Lemma ih_apart_in : forall X cells k n, ih_apart X cells = true -> In (k, n) cells ->
  forallb (fun on : Z * Z => (k + n <=? fst on) || (fst on + snd on <=? k))%bool X = true.
Proof. intros X cells k n Hc Hin. exact (proj1 (forallb_forall _ _) Hc (k, n) Hin). Qed.

Definition IH_IFR : list (Z * Z) := [(9040, 8); (9048, 2); (9052, 4); (9056, 4); (9060, 4); (9064, 8); (9072, 8)].
Definition IH_ICTX : list (Z * Z) := [(10112, 8); (9120, 4); (9136, 2); (9050, 2); (9616, 8)].

Section U2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.
  Hypothesis HOWN : rt_own H.
  Hypothesis HTL : tabl_leavesA.
  Hypothesis V4S : v4slow_stmt H V32_SLOW_CREF.
  Hypothesis PTS : push_types_stmtA H.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.
  Hypothesis HU16 : put_u16_stmtA H LINV ds_repA.
  Hypothesis HPDIAG0 : pdiag0_stmtA H LINV ds_repA.

  Lemma HHm : asan_rt_hyps H.
  Proof. exact (proj1 HHbp). Qed.

  Record ihk (w : pmwA H) (c0 c : pmc) : Prop := MKIHK {
    k_widx  : c_widx c = c_widx c0;
    k_ic    : c_icount c + 4 <= c_widx c;
    k_end   : c_endian c = c_reqconv c /\ (c_endian c = 0 \/ c_endian c = 1);
    k_macct : pi_macct c;
    k_nodes : pi_nodes c + 1 <= c_widx c + 3;
    k_lacc  : pi_lacc c;
    k_lt    : c_widx c < wa_n w
  }.

  Lemma ihk_v1 : forall w c0 c v, ihk w c0 c -> ihk w c0 (set_v1A c v).
  Proof. intros w c0 c v [A B C D E F G]. exact (MKIHK w c0 (set_v1A c v) A B C D E F G). Qed.

  Lemma ihk_v2 : forall w c0 c v, ihk w c0 c -> ihk w c0 (set_v2A c v).
  Proof. intros w c0 c v [A B C D E F G]. exact (MKIHK w c0 (set_v2A c v) A B C D E F G). Qed.

  Lemma ih_ifr_keep : forall (w : pmwA H) X m m', ifrA H w m -> ffkeepX w X m m' -> ih_apart X IH_IFR = true -> ifrA H w m'.
  Proof.
    intros w X m m' (ext & tid & rid & D1 & D2 & D3 & D4 & D5 & D6 & D7 & R1 & R2 & R3) K B.
    exists ext, tid, rid.
    do 7 (split; [eapply (ffkeepX_cell w X m m'); [exact K | eassumption | lia | cbn; lia | eapply (ih_apart_in X IH_IFR); [exact B | cbn; tauto]]|]).
    split; [exact R1|]. split; [exact R2 | exact R3].
  Qed.

  Lemma ih_ictx_keep : forall (w : pmwA H) X m m' I, ictxA H w m I -> ffkeepX w X m m' -> ih_apart X IH_ICTX = true ->
    ictxA H w m' I.
  Proof.
    intros w X m m' I (D1 & D2 & D3 & D4 & D5) K B.
    split; [| split; [| split; [| split]]];
      (eapply (ffkeepX_cell w X m m'); [exact K | eassumption | lia | cbn; lia | eapply (ih_apart_in X IH_ICTX); [exact B | cbn; tauto]]).
  Qed.

  Lemma ih_ifr0 : forall (w : pmwA H) s LB LBs m mo c ins tbl TB spal,
    PMXAT H LINV w s LB LBs m mo c ins tbl FTBL_F07C8 TB spal -> ifrA H w m.
  Proof.
    intros w s LB LBs m mo c ins tbl TB spal X.
    pose proof (xa_fslots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as FS. unfold fslots_ok in FS. rewrite Forall_forall in FS.
    assert (Z0 : rw_cells asegs m (wa_ff w + 9040) [C8 (Z_to_bv 64 0)]) by exact (FS (9040, ELit 0) ltac:(inlist)).
    assert (Z1 : rw_cells asegs m (wa_ff w + 9048) [C8 (Z_to_bv 64 0)]) by exact (FS (9048, ELit 0) ltac:(inlist)).
    assert (Z2 : rw_cells asegs m (wa_ff w + 9056) [C8 (Z_to_bv 64 0)]) by exact (FS (9056, ELit 0) ltac:(inlist)).
    assert (Z3 : rw_cells asegs m (wa_ff w + 9064) [C8 (Z_to_bv 64 0)]) by exact (FS (9064, ELit 0) ltac:(inlist)).
    assert (Z4 : rw_cells asegs m (wa_ff w + 9072) [C8 (Z_to_bv 64 0)]) by exact (FS (9072, ELit 0) ltac:(inlist)).
    destruct (ih_z224 m _ Z1) as (Y1 & _ & Y3). destruct (ih_z44 m _ Z2) as (Y4 & Y5).
    replace (wa_ff w + 9048 + 4) with (wa_ff w + 9052) in Y3 by lia.
    replace (wa_ff w + 9056 + 4) with (wa_ff w + 9060) in Y5 by lia.
    exists 0, 0, 0. refine (conj Z0 (conj Y1 (conj Y3 (conj Y4 (conj Y5 (conj Z3 (conj Z4 _))))))). lia.
  Qed.

  Lemma ih_f0fb0 : forall (w : pmwA H) c0 s LB LBs m mo c msF R F fc fw d l (Q : config -> Prop),
    pmw_okA H w -> U2HK H LINV w c0 F fc Q -> ihk w c0 c -> wa_words w <> 0 /\ 5 <= wa_n w ->
    Zlen (t3b (c_v2 c)) <= 1 -> ifrA H w m ->
    HS_F0FB0 H LINV w s LB LBs m mo c msF R F fc fw d l -> as_SR H Q (mkCfg msF mo).
  Proof.
    intros w c0 s LB LBs m mo c msF R F fc fw d l Q OK UK KC HW V2 IFR HS.
    destruct HS as [X0 Htr Hbsz Hbud Hv1 KR0 VIS0 RF0 FZ0 HT0 G3 G4 Hwlt Hio Hfwr Hwc0 Hfw Hwc Hop Hd Hid Hg].
    assert (ICX : ictxA H w m (PmODefsS1.ICTX (c_widx c) fw (fw / 2 ^ 16) (fw mod 2 ^ 16) d l)).
    { split; [exact Hio | split; [exact Hfw | split; [exact Hwc | split; [exact Hop | exact Hd]]]]. }
    destruct ih_ck_f0fb0 as (T1 & T2 & T3 & T4 & T5).
    eapply (pm_vclear3 H HHbp LINV LINV_frame w s LB LBs m mo (c_F0FB0 c) S_INSTR TBL_F0FB0 [] [] 0 msF R F fc Q
              OK X0 KR0 VIS0 RF0 T1 T2 T3 T4 T5 (regs_tbl_sub w [] R RT_F0FB0 RT_VC3 HT0 ih_rt_vc3)).
    intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2 HT2 FK2.
    pose proof (regs_tbl_sub w [] R2 _ RT_F1090 (regs_tbl_app w [] R2 _ _ (regs_keepK w [] R R2 RT_F0FB0 VC3_KEPT HT0 KEEP2) HT2)
                  ih_rt_f1090) as HT2'.
    assert (G3' : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inlist)); exact G3).
    assert (G4' : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inlist)); exact G4).
    assert (D2 : rw_cells asegs m2 (wa_ff w + 9616) [C8 (Z_to_bv 64 d)]) by exact (FK2 9616 [C8 (Z_to_bv 64 d)] ltac:(lia) ltac:(cbn; lia) Hd).
    pose proof (ih_ifr_keep w [] m m2 IFR (ffkeepX_nil w m m2 FK2) ltac:(vm_compute; reflexivity)) as IFR2.
    pose proof (ih_ictx_keep w [] m m2 _ ICX (ffkeepX_nil w m m2 FK2) ltac:(vm_compute; reflexivity)) as ICX2.
    eapply (pm_u2f H HHbp LINV LINV_frame HTL w s LB LBs m2 mo2 _ msF2 R2 F fc (vc3_tbl TBL_F0FB0) d (fw mod 2 ^ 16) Q
              OK X2 (tbl_incl _ _ ih_tbl_f1090) KR2 VIS2 RF2 HT2' G3' G4' D2 Hid).
    intros msF3 mo3 m3 R3 sp_p l' KR3 VIS3 RF3 X3 HT3 G33 G43 G13 G23 G103 G113 CL3 Hg' SP3 FK3.
    pose proof (ih_ifr_keep w _ m2 m3 IFR2 FK3 ltac:(vm_compute; reflexivity)) as IFR3.
    pose proof (ih_ictx_keep w _ m2 m3 _ ICX2 FK3 ltac:(vm_compute; reflexivity)) as ICX3.
    destruct KC as [Kw Kic Kend Kmac Knodes Klacc Klt].
    destruct Klacc as (L1 & L2 & L3).
    apply (pm_u2g H HHbp LINV LINV_frame LINV_cl LINV_relro HOWN PTS w s LB LBs m3 mo3 _ msF3 R3 F fc (c_widx c) fw d sp_p l' Q
             OK X3 KR3 VIS3 RF3 FZ0 HT3 G33 G43 G13 G23 G103 G113 CL3 Hg' SP3).
    - exact Htr.
    - intros q k Hin. rewrite c_blocks_v3xs in Hin. exact (Hbsz q k Hin).
    - exact (pm_bud_v3xs _ _ _ Hbud).
    - reflexivity.
    - exact Kic.
    - exact Kend.
    - exact HW.
    - exact Kmac.
    - exact Knodes.
    - exact L1.
    - exact L2.
    - exact L3.
    - exact Hv1.
    - exact V2.
    - reflexivity.
    - exact Hfwr.
    - exact Hwc0.
    - exact Hid.
    - exact ICX3.
    - exact IFR3.
    - intros I s' LB' LBs' m' mo' c' msF' R' HOL Hio' _ _ _ _.
      apply (UK I s' LB' LBs' m' mo' c' msF' R' HOL). rewrite Hio'. exact Kw.
  Qed.

  Lemma ih_f0a6c : forall (w : pmwA H) c0 s LB LBs m mo c msF R F fc fw r (Q : config -> Prop),
    pmw_okA H w -> EXITKA H LINV w (c_widx c0) Q -> U2HK H LINV w c0 F fc Q -> ihk w c0 c -> wa_words w <> 0 /\ 5 <= wa_n w ->
    Zlen (t3b (c_v2 c)) <= 1 -> ifrA H w m ->
    HS_F0A6C H LINV w s LB LBs m mo c msF R F fc fw r -> as_SR H Q (mkCfg msF mo).
  Proof.
    intros w c0 s LB LBs m mo c msF R F fc fw r Q OK EK UK KC HW V2 IFR HS.
    destruct (Z.eq_dec r 0) as [Hr | Hr].
    - eapply (pm_u2e H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc fw r Q OK HS Hr (k_lt _ _ _ KC)).
      intros msF1 mo1 m1 R1 d l HB FK.
      exact (ih_f0fb0 w c0 s LB LBs m1 mo1 c msF1 R1 F fc fw d l Q OK UK KC HW V2
               (ih_ifr_keep w _ m m1 IFR FK ltac:(vm_compute; reflexivity)) HB).
    - exact (pm_u2lz H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HU16 HPDIAG0 w s LB LBs m mo c msF R F fc fw r (c_widx c0) Q
               OK HS Hr EK).
  Qed.

  Lemma ih_f0a44 : forall (w : pmwA H) c0 s LB LBs m mo c msF R F fc fw (Q : config -> Prop),
    pmw_okA H w -> EXITKA H LINV w (c_widx c0) Q -> U2HK H LINV w c0 F fc Q -> ihk w c0 c -> wa_words w <> 0 /\ 5 <= wa_n w ->
    Zlen (t3b (c_v2 c)) <= 1 -> ifrA H w m ->
    HS_F0A44 H LINV w s LB LBs m mo c msF R F fc fw -> as_SR H Q (mkCfg msF mo).
  Proof.
    intros w c0 s LB LBs m mo c msF R F fc fw Q OK EK UK KC HW V2 IFR HS.
    destruct (Z.eq_dec (fw / 2 ^ 16) 0) as [Hz | Hz].
    - exact (pm_u2dz H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HU16 HPDIAG0 w s LB LBs m mo c msF R F fc fw (c_widx c0) Q
               OK HS Hz EK).
    - eapply (pm_u2dm H HHbp LINV LINV_frame HTL w s LB LBs m mo c msF R F fc fw Q OK HS Hz).
      intros msF1 mo1 m1 R1 r HC FK.
      exact (ih_f0a6c w c0 s LB LBs m1 mo1 c msF1 R1 F fc fw r Q OK EK UK KC HW V2
               (ih_ifr_keep w _ m m1 IFR FK ltac:(vm_compute; reflexivity)) HC).
  Qed.

  Lemma ih_f0950 : forall (w : pmwA H) c0 s LB LBs m mo c msF R F fc r (Q : config -> Prop),
    pmw_okA H w -> EXITKA H LINV w (c_widx c0) Q -> U2HK H LINV w c0 F fc Q -> ihk w c0 c -> wa_words w <> 0 /\ 5 <= wa_n w ->
    Zlen (t3b (c_v2 c)) <= 1 -> ifrA H w m ->
    c_tr c = [] -> (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> pm_bud (wa_n w) c -> frm_zero fc ->
    0 <= r < 2 ^ 32 -> rw_cells asegs m (wa_ff w + 9120) [C4 (Z_to_bv 64 (sx32A r))] ->
    HS_F0950 H LINV w s LB LBs m mo c [] 0 msF R F fc -> as_SR H Q (mkCfg msF mo).
  Proof.
    intros w c0 s LB LBs m mo c msF R F fc r Q OK EK UK KC HW V2 IFR Htr Hbsz Hbud FZ Hr FW HS.
    destruct HS as [X0 KR0 VIS0 RF0 HT0 G3 G4 _].
    destruct ih_ck_f08ec as (T1 & T2 & T3 & T4 & T5).
    eapply (pm_vclear1 H HHbp LINV LINV_frame w s LB LBs m mo c [OB_INST; OB_FIRST_WORD] TBL_F08EC [] [] 0 msF R F fc Q
              OK X0 KR0 VIS0 RF0 T1 T2 T3 T4 T5 (regs_tbl_sub w [] R RT_F0950 RT_VC1 HT0 ih_rt_vc1)).
    intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2 HT2 FK2.
    pose proof (pmxa_restrict H HHm LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_F0A20 [] OK X2
                  (tbl_incl _ _ ih_tbl_f0a20) (incl_refl _)) as X2r.
    pose proof (regs_tbl_sub w [] R2 _ RT_F0A20 (regs_tbl_app w [] R2 _ _ (regs_keepK w [] R R2 RT_F0950 VC1_KEPT HT0 KEEP2) HT2)
                  ih_rt_f0a20) as HT2'.
    assert (G3' : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inlist)); exact G3).
    assert (G4' : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inlist)); exact G4).
    assert (FW2 : rw_cells asegs m2 (wa_ff w + 9120) [C4 (Z_to_bv 64 (sx32A r))]) by exact (FK2 9120 [C4 (Z_to_bv 64 (sx32A r))] ltac:(lia) ltac:(cbn; lia) FW).
    pose proof (ih_ifr_keep w [] m m2 IFR (ffkeepX_nil w m m2 FK2) ltac:(vm_compute; reflexivity)) as IFR2.
    assert (Hbsz2 : forall q k, In (q, k) (c_blocks (set_v1A c (t3a (c_v1 c), 0, t3c (c_v1 c)))) -> k <= 2 ^ 40).
    { intros q k Hin. rewrite c_blocks_v1cnt in Hin. exact (Hbsz q k Hin). }
    eapply (pm_u2c H HHbp LINV LINV_frame HTL w s LB LBs m2 mo2 _ msF2 R2 F fc r Q OK X2r Htr Hbsz2 (pm_bud_v1cnt _ _ _ Hbud)
              eq_refl KR2 VIS2 RF2 FZ HT2' G3' G4' Hr FW2).
    intros msF3 mo3 m3 R3 HS3 FK3.
    exact (ih_f0a44 w c0 s LB LBs m3 mo3 _ msF3 R3 F fc r Q OK EK UK (ihk_v1 w c0 c _ KC) HW V2
             (ih_ifr_keep w _ m2 m3 IFR2 FK3 ltac:(vm_compute; reflexivity)) HS3).
  Qed.

  Lemma ih_f0884 : forall (w : pmwA H) c0 s LB LBs m mo c msF R F fc r (Q : config -> Prop),
    pmw_okA H w -> EXITKA H LINV w (c_widx c0) Q -> U2HK H LINV w c0 F fc Q -> ihk w c0 c -> wa_words w <> 0 /\ 5 <= wa_n w ->
    ifrA H w m -> c_tr c = [] -> (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> pm_bud (wa_n w) c -> frm_zero fc ->
    0 <= r < 2 ^ 32 -> rw_cells asegs m (wa_ff w + 9120) [C4 (Z_to_bv 64 (sx32A r))] -> t3b (c_v2 c) = [] ->
    PMXAT H LINV w s LB LBs m mo c [OB_INST; OB_FIRST_WORD] TBL_F0884 [] [] 0 ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf0884) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_F0884 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w c0 s LB LBs m mo c msF R F fc r Q OK EK UK KC HW IFR Htr Hbsz Hbud FZ Hr FW Hv2 X KR VIS RF HT G3 G4.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof Hbud as BD. destruct BD as (_ & _ & _ & _ & _ & HV2 & _).
    destruct (Z.lt_ge_cases 0 (t3c (c_v2 c))) as [Hcap | Hcap].
    - assert (HL : Zlen (t3b (c_v2 c)) < t3c (c_v2 c)) by (rewrite Hv2; exact Hcap).
      eapply (pm_u2b_F H HHbp LINV LINV_frame w s LB LBs m mo c [] 0 msF R F fc Q OK X KR VIS RF HT G3 G4 HL).
      intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G31 G41 G10 G11 G12 G13 G22 G23 FK1.
      pose proof (FK1 9120 [C4 (Z_to_bv 64 (sx32A r))] ltac:(lia) ltac:(cbn; lia) FW) as FW1.
      eapply (pm_vpush2 H HHbp LINV LINV_frame w s LB LBs m1 mo1 c [] 0 msF1 R1 F fc r Q OK X1 KR1 VIS1 RF1 HT1 G31 G41
                G10 G11 G12 G13 G22 G23 HL (rw_cells_C4_sx32A m1 _ r Hr FW1) Hr).
      intros msF2 mo2 m2 R2 HS2 FK2.
      pose proof (ffkeep_trans w m m1 m2 FK1 FK2) as FK12.
      assert (V2 : Zlen (t3b (c_v2 (set_v2A c (t3a (c_v2 c), t3b (c_v2 c) ++ [r], t3c (c_v2 c))))) <= 1).
      { change (Zlen (t3b (c_v2 c) ++ [r]) <= 1). rewrite Hv2. cbn [app]. change (Zlen [r]) with 1. lia. }
      assert (Hbsz2 : forall q k, In (q, k) (c_blocks (set_v2A c (t3a (c_v2 c), t3b (c_v2 c) ++ [r], t3c (c_v2 c)))) -> k <= 2 ^ 40).
      { intros q k Hin. rewrite c_blocks_v2xs in Hin. exact (Hbsz q k Hin). }
      exact (ih_f0950 w c0 s LB LBs m2 mo2 _ msF2 R2 F fc r Q OK EK UK (ihk_v2 w c0 c _ KC) HW V2
               (ih_ifr_keep w [] m m2 IFR (ffkeepX_nil w m m2 FK12) ltac:(vm_compute; reflexivity))
               Htr Hbsz2 (pm_bud_v2xs _ _ _ Hbud) FZ Hr (FK12 9120 [C4 (Z_to_bv 64 (sx32A r))] ltac:(lia) ltac:(cbn; lia) FW) HS2).
    - assert (Hc0 : t3c (c_v2 c) = 0) by lia.
      assert (HE : Zlen (t3b (c_v2 c)) = t3c (c_v2 c)) by (rewrite Hv2, Hc0; reflexivity).
      eapply (pm_u2b_S H HHbp LINV LINV_frame w s LB LBs m mo c [] 0 msF R F fc Q OK X KR VIS RF HT G3 G4 HE).
      intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G31 G41 G231 FK1.
      pose proof (FK1 9120 [C4 (Z_to_bv 64 (sx32A r))] ltac:(lia) ltac:(cbn; lia) FW) as FW1.
      assert (G11 : PropExec.getr R1 1%bv = Z_to_bv 64 0xf0920) by rtf HT1.
      assert (G21 : PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w)) by rtf HT1.
      assert (G101 : PropExec.getr R1 10%bv = Z_to_bv 64 (wa_p w + 240)) by rtf HT1.
      assert (G111 : PropExec.getr R1 11%bv = Z_to_bv 64 (wa_ff w + 9120)) by rtf HT1.
      assert (TRO : trace_ok (as_TR H) APC0_FREE [v4_del_ra V32_SLOW_CREF]).
      { pose proof (wk_tr H w OK) as TR. unfold pm_tr_ok, PM_DEL_RAS in TR.
        exact (proj1 (Forall_forall _ _) TR (v4_del_ra V32_SLOW_CREF) ltac:(inlist)). }
      assert (BALL : forall b'' xs'', pm_bud (wa_n w) (set_v2A c (b'', xs'', vgrow (t3c (c_v2 c))))).
      { intros b'' xs''. apply pm_bud_v2cap; [exact Hbud|]. rewrite Hc0. unfold vgrow. rewrite Z.max_r by lia. lia. }
      destruct ih_ck_f08ec as (_ & _ & T3 & _ & T5).
      eapply (pm_v4slow2 H HHbp LINV LINV_cl HOWN V32_SLOW_CREF V4S w s LB LBs m1 mo1 c [OB_INST; OB_FIRST_WORD] TBL_F08EC [] [] 0
                msF1 R1 F fc 0xf0920 9120 r Q OK X1 T3 T5 KR1 VIS1 RF1 G11 eq_refl ltac:(lia) G21 G41 G101 G111 HE ih_osh
                ltac:(lia) ltac:(lia) eq_refl (rw_cells_C4_sx32A m1 _ r Hr FW1) Hr ltac:(cbn [v4_xmax V32_SLOW_CREF]; lia) BALL TRO).
      intros msF2 mo2 m2 R2 s2 pid pid' b' KR2 VIS2 RF2 X2 KEEP2 G102 ABR BUD2 KP2.
      pose proof (regs_tbl_sub w [] R2 _ RT_F0920 (regs_keepK w [] R1 R2 RT_F091C V4_KEPT HT1 KEEP2) ih_rt_f0920) as HT2.
      assert (G32 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inlist)); exact G31).
      assert (G42 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inlist)); exact G41).
      assert (G10' : PropExec.getr R2 10%bv
                     = Z_to_bv 64 (t3a (c_v2 (set_v2A c (b', t3b (c_v2 c) ++ [r], vgrow (t3c (c_v2 c)))))
                                   + 4 * Zlen (t3b (c_v2 (set_v2A c (b', t3b (c_v2 c) ++ [r], vgrow (t3c (c_v2 c)))))))).
      { rewrite G102. change (Z_to_bv 64 (b' + 4 * (t3c (c_v2 c) + 1)) = Z_to_bv 64 (b' + 4 * Zlen (t3b (c_v2 c) ++ [r]))).
        rewrite Hv2, Hc0. reflexivity. }
      assert (HP : 0 < Zlen (t3b (c_v2 (set_v2A c (b', t3b (c_v2 c) ++ [r], vgrow (t3c (c_v2 c))))))).
      { change (0 < Zlen (t3b (c_v2 c) ++ [r])). rewrite Hv2. cbn [app]. change (Zlen [r]) with 1. lia. }
      eapply (pm_u2b_SR H HHbp LINV LINV_frame w s2 _ _ m2 mo2 _ [] 0 msF2 R2 F fc Q OK X2 KR2 VIS2 RF2 HT2 G32 G42 G10' HP).
      intros msF3 mo3 m3 R3 HS3 FK3.
      pose proof (ffkeep_trans w m m1 m2 FK1 KP2) as FK12.
      pose proof (ffkeep_trans w m m2 m3 FK12 FK3) as FK13.
      assert (V2 : Zlen (t3b (c_v2 (set_v2A c (b', t3b (c_v2 c) ++ [r], vgrow (t3c (c_v2 c)))))) <= 1).
      { change (Zlen (t3b (c_v2 c) ++ [r]) <= 1). rewrite Hv2. cbn [app]. change (Zlen [r]) with 1. lia. }
      assert (Hbsz2 : forall q k, In (q, k) (c_blocks (set_v2A c (b', t3b (c_v2 c) ++ [r], vgrow (t3c (c_v2 c))))) -> k <= 2 ^ 40).
      { intros q k Hin. destruct (c_blocks_v2_in c _ _ _ q k Hin) as [Hin' | ->]; [exact (Hbsz q k Hin')|].
        rewrite Hc0. unfold vgrow. rewrite Z.max_r by lia. lia. }
      exact (ih_f0950 w c0 s2 _ _ m3 mo3 _ msF3 R3 F fc r Q OK EK UK (ihk_v2 w c0 c _ KC) HW V2
               (ih_ifr_keep w [] m m3 IFR (ffkeepX_nil w m m3 FK13) ltac:(vm_compute; reflexivity))
               Htr Hbsz2 BUD2 FZ Hr (FK13 9120 [C4 (Z_to_bv 64 (sx32A r))] ltac:(lia) ltac:(cbn; lia) FW) HS3).
  Qed.

  Lemma ih_f07c8 : forall (w : pmwA H) c0 s LB LBs m mo msF R F fc r (Q : config -> Prop),
    pmw_okA H w -> EXITKA H LINV w (c_widx c0) Q -> U2HK H LINV w c0 F fc Q -> ihk w c0 (c_F06BC c0) ->
    wa_words w <> 0 /\ 5 <= wa_n w ->
    c_tr c0 = [] -> (forall q k, In (q, k) (c_blocks c0) -> k <= 2 ^ 40) -> pm_bud (wa_n w) c0 ->
    HS_F07C8 H LINV w s LB LBs m mo c0 msF R F fc r -> as_SR H Q (mkCfg msF mo).
  Proof.
    intros w c0 s LB LBs m mo msF R F fc r Q OK EK UK KC HW Htr Hbsz Hbud HS.
    destruct HS as [X0 KR0 VIS0 RF0 FZ0 HT0 G3 G4 Hr A0 FW].
    pose proof (ih_ifr0 w _ _ _ _ _ _ _ _ _ _ X0) as IFR.
    destruct ih_ck_f07c8 as (T1 & T2 & T3 & T4 & T5).
    eapply (pm_vclear2 H HHbp LINV LINV_frame w s LB LBs m mo (c_F06BC c0) [OB_INST; OB_FIRST_WORD] TBL_F07C8 FTBL_F07C8 [] 0
              msF R F fc Q OK X0 KR0 VIS0 RF0 T1 T2 T3 T4 T5 (regs_tbl_sub w [] R RT_F07C8 RT_VC2 HT0 ih_rt_vc2)).
    intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2 HT2 FK2.
    pose proof (pmxa_restrict H HHm LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_F0884 [] OK X2
                  (tbl_incl _ _ ih_tbl_f0884) (incl_nil_l _)) as X2r.
    pose proof (regs_tbl_sub w [] R2 _ RT_F0884 (regs_tbl_app w [] R2 _ _ (regs_keepK w [] R R2 RT_F07C8 VC2_KEPT HT0 KEEP2) HT2)
                  ih_rt_f0884) as HT2'.
    assert (G3' : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inlist)); exact G3).
    assert (G4' : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inlist)); exact G4).
    assert (Hbsz1 : forall q k, In (q, k) (c_blocks (set_v2A (c_F06BC c0) (t3a (c_v2 (c_F06BC c0)), [], t3c (c_v2 (c_F06BC c0)))))
                                -> k <= 2 ^ 40).
    { intros q k Hin. rewrite c_blocks_v2xs in Hin. unfold c_F06BC in Hin. rewrite c_blocks_scal in Hin. exact (Hbsz q k Hin). }
    pose proof (pm_bud_v2xs (wa_n w) (c_F06BC c0) [] (pm_bud_scal _ c0 _ _ _ _ Hbud)) as Hbud1.
    exact (ih_f0884 w c0 s LB LBs m2 mo2 _ msF2 R2 F fc r Q OK EK UK (ihk_v2 w c0 _ _ KC) HW
             (ih_ifr_keep w [] m m2 IFR (ffkeepX_nil w m m2 FK2) ltac:(vm_compute; reflexivity))
             Htr Hbsz1 Hbud1 FZ0 Hr (FK2 9120 [C4 (Z_to_bv 64 (sx32A r))] ltac:(lia) ltac:(cbn; lia) FW) eq_refl X2r KR2 VIS2 RF2 HT2' G3' G4').
  Qed.

  Lemma pm_ihead : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PI0A H LINV w s LB LBs m mo c msF R F fc -> EXITKA H LINV w (c_widx c) Q ->
    U2HK H LINV w c F fc Q -> as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q OK P0 EK UK.
    pose proof P0 as P0c.
    destruct P0c as [X0 KR0 VIS0 RF0 FZ0 HT0 G3 G4 Htr Hbsz Hic Hend Hw Hbud Hacc Hlt Ha0].
    destruct Hacc as (Hn & Hm & Hl).
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (S1 & _).
    assert (KC : ihk w c (c_F06BC c)).
    { refine (MKIHK w c (c_F06BC c) eq_refl _ Hend Hm Hn Hl Hlt). cbn. lia. }
    assert (K : forall msF1 mo1 m1 R1 (r : Z), HS_F07C8 H LINV w s LB LBs m1 mo1 c msF1 R1 F fc r -> as_SR H Q (mkCfg msF1 mo1)).
    { intros msF1 mo1 m1 R1 r HS. exact (ih_f07c8 w c s LB LBs m1 mo1 msF1 R1 F fc r Q OK EK UK KC Hw Htr Hbsz Hbud HS). }
    destruct (granule_split (c_widx c) (wa_n w) ltac:(lia)) as [HG | HG].
    - exact (pm_u2a_F H HHbp LINV LINV_frame HTL w s LB LBs m mo c msF R F fc Q OK P0 HG K).
    - exact (pm_u2a_P H HHbp LINV LINV_frame HTL w s LB LBs m mo c msF R F fc Q OK P0 HG K).
  Qed.
End U2.
