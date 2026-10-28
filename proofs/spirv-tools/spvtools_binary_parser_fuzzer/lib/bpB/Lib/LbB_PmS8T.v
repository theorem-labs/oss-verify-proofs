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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts StrLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require PmStep5S1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmVup LbB_PmExit2 LbB_PmGlue LbB_PmU2K LbB_PmLH LbB_PmLeaf LbB_DiagStmt LbB_PmDS LbB_ContStmt LbB_PmVops LbB_PmU2 LbB_DStat LbB_TablStmt LbB_PmOL LbB_PmOLX LbB_HEmpStmt LbB_PmWM3 LbB_PmWEx LbB_PmU3L LbB_PmU3XK LbB_PmU6R LbB_StrPb LbB_MkStr LbB_PmStr LbB_PmStrD LbB_PmStrI LbB_PmS8K LbB_PmS8a LbB_PmS8b LbB_PmS8d LbB_PmS8i LbB_PmS8g LbB_PmS8 LbB_DtK LbB_DRep LbB_StrPbR LbB_PmStrX LbB_PmS8n LbB_PmS8nl.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require PmArm_StrLibS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac inlistT := cbn; repeat (first [left; reflexivity | right]).

Lemma b8_mod256 : forall x, b8 x = b8 (x mod 256).
Proof.
  intros x. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. symmetry. apply Zmod_mod.
Qed.

Section STK.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma wr_sub : forall m a n a' n', wr_at asegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at asegs m a' n'.
Proof.
  exact LbB_DRep.wr_at_sub.
Qed.

  Lemma str_hdr_short : forall (w : pmwA H) LB m cs, wr_at asegs m (wa_ff w) 16384 -> 0 <= wa_ff w ->
    strA LB m (wa_ff w + 5936) SShort cs ->
    rw_cells asegs m (wa_ff w + 5936) [C1 (b8 (2 * Zlen cs))] /\ 0 <= Zlen cs <= 22.
Proof.
    intros w LB m cs W F0 S.
    destruct (strA_short_facts LB m (wa_ff w + 5936) cs S) as (HL & HF & _).
    unfold SSO_CAP in HL. split; [|exact HL].
    pose proof (rw_cells_of_fld1 m (wa_ff w + 5936) (2 * Zlen cs) HF
                  (LbB_DRep.wr_at_sub m (wa_ff w) 16384 (wa_ff w + 5936) 1 W ltac:(lia) ltac:(lia) ltac:(lia))) as R.
    rewrite u64_of_Z in R by lia. exact R.
  Qed.

  Lemma str_hdr_long : forall (w : pmwA H) LB m d asz cs, wr_at asegs m (wa_ff w) 16384 -> 0 <= wa_ff w -> asz < 2 ^ 62 ->
    strA LB m (wa_ff w + 5936) (SLong d asz) cs ->
    exists b0, rw_cells asegs m (wa_ff w + 5936) [C1 (b8 b0)] /\ (0 <= b0 < 256 /\ b0 mod 2 = 1)
      /\ rw_cells asegs m (wa_ff w + 5944) [C8 (Z_to_bv 64 (Zlen cs))]
      /\ rw_cells asegs m (wa_ff w + 5936) [C8 (Z_to_bv 64 (asz + 1))]
      /\ rw_cells asegs m (wa_ff w + 5952) [C8 (Z_to_bv 64 d)] /\ 0 <= d < 2 ^ 64 /\ 0 <= Zlen cs < asz.
Proof.
    intros w LB m d asz cs W F0 HA S.
    unfold strA, str_rep in S. cbn [str_cap str_data] in S.
    destruct S as (Hs & Hs' & _ & HL & (Hd0 & _ & Hda & Ha8 & Ha46 & _ & _ & FA & FB & FC) & _).
    unfold SSO_CAP in Ha46.
    assert (WS : forall k n, 0 <= k -> k + n <= 16384 -> 0 <= n -> wr_at asegs m (wa_ff w + k) n).
    { intros k n Hk Hkn Hn. exact (LbB_DRep.wr_at_sub m (wa_ff w) 16384 (wa_ff w + k) n W ltac:(lia) ltac:(lia) Hn). }
    exists ((asz + 1) mod 256). split.
    { pose proof (rw_cells_of_fld1 m (wa_ff w + 5936) (asz + 1) (fldA8_byte0 m (wa_ff w + 5936) (asz + 1) FA)
                    (WS 5936 1 ltac:(lia) ltac:(lia) ltac:(lia))) as R.
      rewrite u64_of_Z in R by lia. rewrite b8_mod256 in R. exact R. }
    split; [split; [apply Z.mod_pos_bound; lia | Z.div_mod_to_equations; lia]|].
    replace (wa_ff w + 5936 + 8) with (wa_ff w + 5944) in FB by lia.
    replace (wa_ff w + 5936 + 16) with (wa_ff w + 5952) in FC by lia.
    split; [exact (rw_cells_of_fld8 m _ _ FB (WS 5944 8 ltac:(lia) ltac:(lia) ltac:(lia)))|].
    split; [exact (rw_cells_of_fld8 m _ _ FA (WS 5936 8 ltac:(lia) ltac:(lia) ltac:(lia)))|].
    split; [exact (rw_cells_of_fld8 m _ _ FC (WS 5952 8 ltac:(lia) ltac:(lia) ltac:(lia)))|].
    lia.
  Qed.

  Lemma str_keep_munch : forall W LB m m' p sb pid cs,
    strA LB m p sb cs -> spb_blk LB m sb pid -> munch W m m' -> wmono asegs m m' ->
    disjoint_from W p 24 ->
    (forall d asz, sb = SLong d asz -> disjoint_from W d asz /\ disjoint_from W (sh d) (nsh asz)) ->
    strA LB m' p sb cs /\ spb_blk LB m' sb pid.
Proof.
    intros W LB m m' p sb pid cs S B MU WM DJ DL.
    assert (S' := S). unfold strA, str_rep in S'.
    destruct S' as (Hs & Hs' & _ & HL & HM & _).
    split.
    - unfold strA in *. eapply str_frame; [exact S|].
      intros a Ha. apply MU. unfold str_fp, zwin in Ha.
      destruct sb as [|d asz]; cbn [str_cap] in HL, HM, Ha.
      + destruct Ha as [Ha|[]]. rewrite u64_of_Z by lia. exact (disjoint_outside W p 24 a DJ ltac:(lia)).
      + destruct HM as (Hd0 & _ & Hda & _ & Ha46 & _). destruct (DL d asz eq_refl) as [DJd _].
        destruct Ha as [Ha|Ha]; rewrite u64_of_Z by lia.
        * exact (disjoint_outside W p 24 a DJ ltac:(lia)).
        * exact (disjoint_outside W d asz a DJd ltac:(lia)).
    - destruct sb as [|d asz]; cbn [spb_blk] in *; [exact I|].
      destruct B as [HIN HSH]. split; [exact HIN|].
      destruct HM as (_ & _ & _ & _ & Ha46 & _). unfold SSO_CAP in Ha46.
      destruct (DL d asz eq_refl) as [_ DJs].
      assert (AD : addressable m d asz) by (split; [lia | exact HSH]).
      exact (proj2 (addressable_transport W m m' d asz AD MU WM DJs)).
  Qed.

  Lemma str_bytes_at : forall LB m p sb cs, strA LB m p sb cs -> bytes_at asegs m (str_data p sb) (str_bytes cs).
Proof.
    intros LB m p sb cs S. unfold strA, str_rep in S.
    destruct S as (Hs & Hs' & _ & HL & HM & HC & _).
    assert (B : 0 <= str_data p sb /\ str_data p sb + Zlen cs < 2 ^ 63).
    { destruct sb as [|d asz]; cbn [str_data str_cap] in *; unfold SSO_CAP in *; [lia|].
      destruct HM as (Hd0 & _ & Hda & _). lia. }
    unfold Zlen in B.
    apply LbB_Conv.bytes_at_of_rdn; rewrite ?str_bytes_length; [lia | lia |].
    apply fld_str_rdn; [lia | unfold Zlen; lia | exact HC].
  Qed.

  Lemma shdrA_keepX : forall (w : pmwA H) X m m' sb, shdrA H w m sb -> ffkeepX w X m m' ->
    forallb (fun on : Z * Z => (5936 + 24 <=? fst on) || (fst on + snd on <=? 5936))%bool X = true -> shdrA H w m' sb.
Proof.
    intros w X m m' sb SH K FB.
    assert (KX : forall k cs, 5936 <= k -> k + Z.of_nat (cells_size cs) <= 5960 ->
              rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m' (wa_ff w + k) cs).
    { intros k cs Hk Hn C. apply (K k cs ltac:(lia) ltac:(lia)); [|exact C].
      apply Forall_forall. intros on Hin. rewrite forallb_forall in FB. pose proof (FB on Hin) as E. cbv beta in E.
      apply Bool.orb_true_iff in E. destruct E as [E|E]; apply Z.leb_le in E; lia. }
    destruct sb as [|d asz]; cbn [shdrA] in *.
    - destruct SH as (b0 & B0 & Hb). exists b0.
      split; [exact (KX 5936 [C1 (b8 b0)] ltac:(lia) ltac:(cbn; lia) B0) | exact Hb].
    - destruct SH as (b0 & cp & B0 & Hb & Ho & CP & DP & Hd). exists b0, cp.
      split; [exact (KX 5936 [C1 (b8 b0)] ltac:(lia) ltac:(cbn; lia) B0)|]. split; [exact Hb|]. split; [exact Ho|].
      split; [exact (KX 5936 [C8 (Z_to_bv 64 cp)] ltac:(lia) ltac:(cbn; lia) CP)|].
      split; [exact (KX 5952 [C8 (Z_to_bv 64 d)] ltac:(lia) ltac:(cbn; lia) DP) | exact Hd].
  Qed.
End STK.

Definition STR_X : list (Z * Z) := [(5936, 24); (116, 4); (114, 2)].

Section TOP.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.
  Hypothesis HOWN : rt_own H.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.
  Hypothesis HU16 : put_u16_stmtA H LINV ds_repA.
  Hypothesis HU64 : put_u64_stmtA H LINV ds_repA.
  Hypothesis HPDIAG0 : pdiag0_stmtA H LINV ds_repA.
  Hypothesis HEX : exhausted_stmtA H LINV.
  Hypothesis HMS : mkstr_stmtA H.
  Hypothesis HITG : import_type_get_stmtA.
  #[local] Notation ent := (Z * (Z * Z))%type (only parsing).

  Lemma HHt : asan_rt_hyps H.
Proof.
  exact (proj1 HHbp).
Qed.

  Definition badimp_stmt : Prop :=
    forall (w : pmwA H) s LB LBs m mo c msF R F fc (sb : sbuf) (pid : bptr) (cs : list Z) (ty : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_STR TBL_EEF44 [] ->
    c_tr c = tr_of sb -> pm_bud (wa_n w) c -> (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf31d8) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8C -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 0 ->
    strA LB m (wa_ff w + 5936) sb cs -> spb_blk LB m sb pid -> Forall (fun c => c <> 0) cs -> Zlen cs < 262140 ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
    (forall (s1 : as_St H) (LB1 LBs1 : list block) msF1 mo1 m1 R1 F1 fc1 (spal1 : Z),
       as_AKREL H s1 (mkCfg msF1 mo1) -> as_VIS H s1 msF1 = MS R1 F1 (Z_to_bv 64 0xf4164) fc1 None m1 (seg_rom asegs) -> rfull R1 ->
       frm_zero fc1 ->
       PMXAT H LINV w s1 LB1 LBs1 m1 mo1 c S_STR TBL_EEF44 [] [] spal1 -> 0 <= spal1 <= 2 ^ 24 ->
       regs_tbl w R1 RT_S8D0 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       PropExec.getr R1 23%bv = Z_to_bv 64 (sx32A (2 ^ 32 - 4)) ->
       shdrA H w m1 sb -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).

  Definition badimpL_stmt : Prop :=
    forall (w : pmwA H) s LB LBs m mo c msF R F fc (d asz : Z) (pid : bptr) (cs : list Z) (ty : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_STR TBL_EEF44 [] ->
    c_tr c = tr_of (SLong d asz) -> pm_bud (wa_n w) c -> (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf31d8) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8C -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 0 ->
    strA LB m (wa_ff w + 5936) (SLong d asz) cs -> spb_blk LB m (SLong d asz) pid -> Forall (fun c => c <> 0) cs -> Zlen cs < 262140 ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
    (forall (s1 : as_St H) (LB1 LBs1 : list block) msF1 mo1 m1 R1 F1 fc1 (spal1 : Z),
       as_AKREL H s1 (mkCfg msF1 mo1) -> as_VIS H s1 msF1 = MS R1 F1 (Z_to_bv 64 0xf4164) fc1 None m1 (seg_rom asegs) -> rfull R1 ->
       frm_zero fc1 ->
       PMXAT H LINV w s1 LB1 LBs1 m1 mo1 c S_STR TBL_EEF44 [] [] spal1 -> 0 <= spal1 <= 2 ^ 24 ->
       regs_tbl w R1 RT_S8D0 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       PropExec.getr R1 23%bv = Z_to_bv 64 (sx32A (2 ^ 32 - 4)) ->
       shdrA H w m1 (SLong d asz) -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Lemma HBADL : badimpL_stmt.
Proof.
    unfold badimpL_stmt.
    intros w s LB LBs m mo c msF R F fc d asz pid cs ty Q OK X0 Htr BUD Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 G10_0
           HS SB NZ HLEN TY K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & _).
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as FW. change (fsz PM_FCLASS) with 16384 in FW.
    assert (HS' := HS). unfold strA, str_rep in HS'. cbn [str_cap str_data] in HS'.
    destruct HS' as (Hs & Hs' & _ & HL & (Hd0 & _ & Hda & _ & Ha46 & _) & _).
    unfold SSO_CAP in Ha46.
    assert (INCB : In (d, asz) (c_blocks c)).
    { unfold c_blocks. rewrite Htr. cbn [tr_of]. do 6 (apply in_or_app; right). left. reflexivity. }
    pose proof (Hbsz d asz INCB) as Hasz.
    destruct (str_hdr_long H w LB m d asz cs FW ltac:(lia) ltac:(lia) HS) as (b0 & B0 & HB0R & SZ & CP & DP & HDPR & HSZR).
    destruct SB as [HINLB HSH].
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    assert (UQ : forall (L : list block) x y, List.NoDup (map blk_id L) -> In x L -> In y L ->
                 (blk_id x <> blk_id y -> False) -> x = y).
    { induction L as [|b L IH]; intros x y ND Hx Hy NE; [destruct Hx|].
      cbn [map] in ND. apply NoDup_cons_iff in ND as [NI ND'].
      destruct Hx as [Ex|Hx]; destruct Hy as [Ey|Hy].
      - subst x y. reflexivity.
      - exfalso. apply NE. intros E. apply NI. subst x. rewrite E. apply in_map. exact Hy.
      - exfalso. apply NE. intros E. apply NI. subst y. rewrite <- E. apply in_map. exact Hx.
      - exact (IH x y ND' Hx Hy NE). }
    assert (HIN : In (pid, d, asz) LBs).
    { apply (Permutation_in _ (Permutation_sym OWN2)) in INCB.
      unfold lbl in INCB. apply in_map_iff in INCB. destruct INCB as ([[q a] n] & Eb & Hb).
      cbn [fst snd] in Eb. inversion Eb. subst a n.
      assert (HbLB : In (q, d, asz) LB).
      { apply (Permutation_in _ (Permutation_sym OWN1)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
      assert (E : (pid, d, asz) = (q, d, asz)).
      { apply (UQ LB _ _ (ah_nodup H HHt _ _ _ RH) HINLB HbLB). intros NE.
        pose proof (ah_disj H HHt _ _ _ _ _ RH HINLB HbLB NE) as D.
        cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in D. lia. }
      rewrite E. exact Hb. }
    assert (HT0' : regs_tbl w R RT_S8C0).
    { unfold RT_S8C0. apply Forall_app. split; [exact HT0|]. constructor; [|constructor]. cbn [fst snd]. rewrite G10_0. reflexivity. }
    eapply (pm_s8n_l H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 w s LB LBs m mo c msF R F fc
              b0 (Zlen cs) (asz + 1) d ty asz pid (str_bytes cs) Q
              OK X0 I Hbsz KR0 VIS0 RF0 FZ0 HT0' G3_0 G4_0 BUD B0 HB0R SZ ltac:(lia) CP DP HDPR TY HIN ltac:(lia)
              ltac:(rewrite str_bytes_length; unfold Zlen; rewrite Nat2Z.id; reflexivity)
              (str_bytes_at LB m _ _ cs HS) HSH).
    intros s1 LB1 LBs1 msF1 mo1 m1 R1 F1 fc1 tbl1 spal1 KR1 VIS1 RF1 FZ1 X1 INC SP1 HT1 G3_1 G4_1 E23 B1 CP1 DP1 TY1.
    apply (K s1 LB1 LBs1 msF1 mo1 m1 R1 F1 fc1 spal1 KR1 VIS1 RF1 FZ1
             (pmxa_restrict H HHt LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X1 INC (incl_refl _)) SP1
             HT1 G3_1 G4_1 E23).
    - cbn [shdrA]. exists b0, (asz + 1). split; [exact B1|]. split; [exact (proj1 HB0R)|]. split; [exact (proj2 HB0R)|].
      split; [exact CP1|]. split; [exact DP1 | exact HDPR].
    - exact TY1.
  Qed.

  Lemma badimp_short : forall (w : pmwA H) s LB LBs m mo c msF R F fc (pid : bptr) (cs : list Z) (ty : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_STR TBL_EEF44 [] ->
    c_tr c = tr_of SShort -> pm_bud (wa_n w) c -> (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf31d8) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8C -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 0 ->
    strA LB m (wa_ff w + 5936) SShort cs ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
    (forall (s1 : as_St H) (LB1 LBs1 : list block) msF1 mo1 m1 R1 F1 fc1 (spal1 : Z),
       as_AKREL H s1 (mkCfg msF1 mo1) -> as_VIS H s1 msF1 = MS R1 F1 (Z_to_bv 64 0xf4164) fc1 None m1 (seg_rom asegs) -> rfull R1 ->
       frm_zero fc1 ->
       PMXAT H LINV w s1 LB1 LBs1 m1 mo1 c S_STR TBL_EEF44 [] [] spal1 -> 0 <= spal1 <= 2 ^ 24 ->
       regs_tbl w R1 RT_S8D0 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       PropExec.getr R1 23%bv = Z_to_bv 64 (sx32A (2 ^ 32 - 4)) ->
       shdrA H w m1 SShort -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
Proof.
    intros w s LB LBs m mo c msF R F fc pid cs ty Q OK X0 Htr BUD Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 G10_0 HS TY K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & _).
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as FW. change (fsz PM_FCLASS) with 16384 in FW.
    destruct (str_hdr_short H w LB m cs FW ltac:(lia) HS) as (B0 & HL).
    destruct (rw_cells_of_wr_hi m (wa_ff w + 5937) 23
                (LbB_DRep.wr_at_sub m (wa_ff w) 16384 (wa_ff w + 5937) 23 FW ltac:(lia) ltac:(lia) ltac:(lia))
                ltac:(unfold AFS_HDR in Q4; lia) ltac:(lia)) as (bs23 & BS).
    assert (HT0' : regs_tbl w R RT_S8C0).
    { unfold RT_S8C0. apply Forall_app. split; [exact HT0|]. constructor; [|constructor]. cbn [fst snd]. rewrite G10_0. reflexivity. }
    eapply (pm_s8n_s H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 w s LB LBs m mo c msF R F fc (Zlen cs) ty bs23 Q
              OK X0 I Hbsz KR0 VIS0 RF0 FZ0 HT0' G3_0 G4_0 BUD B0 HL BS TY).
    intros s1 LB1 LBs1 msF1 mo1 m1 R1 F1 fc1 tbl1 spal1 KR1 VIS1 RF1 FZ1 X1 INC SP1 HT1 G3_1 G4_1 E23 B1 TY1.
    apply (K s1 LB1 LBs1 msF1 mo1 m1 R1 F1 fc1 spal1 KR1 VIS1 RF1 FZ1
             (pmxa_restrict H HHt LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X1 INC (incl_refl _)) ltac:(lia)
             HT1 G3_1 G4_1 E23).
    - cbn [shdrA]. exists (2 * Zlen cs). split; [exact B1|]. split; [lia|].
      rewrite Z.mul_comm. apply Z.mod_mul. lia.
    - exact TY1.
  Qed.

  Lemma ffk_mono : forall (w : pmwA H) X m m', ffkeepX w X m m' -> incl X STR_X -> ffkeepX w STR_X m m'.
Proof.
  intros w X m m' K I. exact (ffkeepX_mono w X STR_X m m' K I).
Qed.
  Lemma ffk_tr : forall (w : pmwA H) m1 m2 m3, ffkeepX w STR_X m1 m2 -> ffkeepX w STR_X m2 m3 -> ffkeepX w STR_X m1 m3.
Proof.
  intros w m1 m2 m3 A B. exact (ffkeepX_trans w STR_X STR_X STR_X m1 m2 m3 A B (incl_refl _) (incl_refl _)).
Qed.
  Lemma set_tr_nil_back : forall c tr, c_tr c = [] -> set_trA (set_trA c tr) [] = c.
Proof.
  intros c tr E. destruct c; cbn in E; subst; reflexivity.
Qed.
  Lemma err_m4 : Z_to_bv 64 (2 ^ 64 - 4) = Z_to_bv 64 (sx32A (2 ^ 32 - 4)).
Proof.
  change (sx32A (2 ^ 32 - 4)) with (2 ^ 64 - 4). reflexivity.
Qed.

  Theorem arm_STR_AX : forall t, (t = 11 \/ t = 48) -> arm_stmtAX H LINV t 0xf1e48.
Proof.
    intros t Ht w s LB LBs m mo c msF R F fc I tbl wv Q OK HAE IT TC TK TN PK CK AACC.
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q22 & Q25 & Q18 & Q21 & PO & C176).
    destruct OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP IC FR Hic Hend Hw MAC V3R].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (ipure_ranges I IP) as [IWC IOP].
    pose proof (pmxa_restrict H HHt LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X0 IT (incl_refl _)) as X0r.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (SC1 & SC2 & SC3).
    pose proof IP as (_ & _ & _ & _ & _ & _ & IO0).
    assert (IXa : incl [(5936, 24)] STR_X) by (intros x Hx; unfold STR_X; cbn in Hx |- *; tauto).
    assert (IXb : incl [(116, 4); (114, 2)] STR_X) by (intros x Hx; unfold STR_X; cbn in Hx |- *; tauto).

    assert (PKW : forall c1 s1 LB1 LBs1 m1 mo1 msF1 R1 F1 fc1 (spal1 nw : Z),
      as_AKREL H s1 (mkCfg msF1 mo1) -> as_VIS H s1 msF1 = MS R1 F1 (Z_to_bv 64 OL_PUSHK) fc1 None m1 (seg_rom asegs) -> rfull R1 -> frm_zero fc1 ->
      PMXAT H LINV w s1 LB1 LBs1 m1 mo1 c1 S_OPER TBL_EEF44 [] [] spal1 -> 0 <= spal1 <= PM_STRK * nw ->
      regs_tbl w R1 RT_PUSHK -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
      (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) ->
      rw_cells asegs m1 (wa_ff w + 114) [C2 (Z_to_bv 64 nw)] -> 1 <= nw < 2 ^ 16 ->
      rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 11)] -> ffkeepX w STR_X m m1 ->
      c_tr c1 = [] -> pm_bud (wa_n w) c1 -> (forall q k, In (q, k) (c_blocks c1) -> k <= 2 ^ 40) ->
      (c1 = c \/ (i_op I = OP_EXT_INST_IMPORT /\ exists tt, c1 = set_m3A c tt
                   /\ Zlength (t3c (c_m3 c)) <= Zlength (t3c tt) <= Zlength (t3c (c_m3 c)) + 1 /\ macctA c1)) ->
      as_SR H Q (mkCfg msF1 mo1)).
    { intros c1 s1 LB1 LBs1 m1 mo1 msF1 R1 F1 fc1 spal1 nw KR1 VIS1 RF1 FZ1 X1 SP1 HT1 G3_1 G4_1 KX1 C114 Hnw C116 FK1 Htr1 BUD1 Hbsz1 CR1.
      assert (IC1 : ictxA H w m1 I) by (eapply (ictxA_ffkeepX H w m m1); [exact IC | exact FK1 | vm_compute; reflexivity]).
      assert (FR1 : ifrA H w m1) by (eapply (ifrA_ffkeepX H w m m1); [exact FR | exact FK1 | vm_compute; reflexivity]).
      pose proof PO as (K112 & _ & _ & K120 & K124 & K128).
      assert (C112 : rw_cells asegs m1 (wa_ff w + 112) [C2 (Z_to_bv 64 (c_widx c - i_io I))])
        by (apply (ffkeepX_cell w STR_X m m1 112 _ FK1 K112); [lia | cbn; lia | vm_compute; reflexivity]).
      assert (C120 : rw_cells asegs m1 (wa_ff w + 120) [C4 (Z_to_bv 64 0)])
        by (apply (ffkeepX_cell w STR_X m m1 120 _ FK1 K120); [lia | cbn; lia | vm_compute; reflexivity]).
      assert (C124 : rw_cells asegs m1 (wa_ff w + 124) [C4 (Z_to_bv 64 0)])
        by (apply (ffkeepX_cell w STR_X m m1 124 _ FK1 K124); [lia | cbn; lia | vm_compute; reflexivity]).
      assert (C128 : rw_cells asegs m1 (wa_ff w + 128) [C4 (Z_to_bv 64 0)])
        by (apply (ffkeepX_cell w STR_X m m1 128 _ FK1 K128); [lia | cbn; lia | vm_compute; reflexivity]).
      pose proof (popnd_mdef H w m1 _ _ _ _ _ _ OK C112 C114 C116 C120 C124 C128) as MD1.
      assert (Q22_1 : PropExec.getr R1 22%bv = Z_to_bv 64 (i_op I)) by (rewrite (KX1 22%bv ltac:(inlistT)); exact Q22).
      assert (Q25_1 : PropExec.getr R1 25%bv = Z_to_bv 64 (i_io I)) by (rewrite (KX1 25%bv ltac:(inlistT)); exact Q25).
      assert (Q18_1 : PropExec.getr R1 18%bv = Z_to_bv 64 t) by (rewrite (KX1 18%bv ltac:(inlistT)); exact Q18).
      destruct CR1 as [-> | (Hop & tt & -> & Hm3 & MA1)].
      - apply (PK s1 LB1 LBs1 m1 mo1 c msF1 R1 F1 fc1 TBL_EEF44 nw [] spal1).
        + constructor; assumption.
        + exact SP1.
        + apply incl_refl.
        + exact Q22_1.
        + exact Q25_1.
        + exists t. split; [exact Q18_1 | lia].
        + exact C114.
        + left; exact Hnw.
        + exists (c_widx c - i_io I), 11. split; [exact C112 | exact C116].
        + exact MD1.
        + reflexivity.
        + reflexivity.
        + reflexivity.
        + lia.
        + rewrite app_nil_r. reflexivity.
        + exact PmZw.seed_free_nil.
        + rewrite PmZw.Zlen_nil. lia.
        + left; reflexivity.
        + reflexivity.
        + left; reflexivity.
        + left; reflexivity.
        + intros [].
      - apply (PK s1 LB1 LBs1 m1 mo1 (set_m3A c tt) msF1 R1 F1 fc1 TBL_EEF44 nw [] spal1).
        + constructor; try assumption.
          pose proof MAC as (_ & _ & _ & _ & M2ok). destruct MA1 as (A1 & A2 & A3 & A4).
          exact (conj A1 (conj A2 (conj A3 (conj A4 M2ok)))).
        + exact SP1.
        + apply incl_refl.
        + exact Q22_1.
        + exact Q25_1.
        + exists t. split; [exact Q18_1 | lia].
        + exact C114.
        + left; exact Hnw.
        + exists (c_widx c - i_io I), 11. split; [exact C112 | exact C116].
        + exact MD1.
        + reflexivity.
        + reflexivity.
        + reflexivity.
        + unfold LbB_PiStmt.pi_nodes. cbn [set_m3A c_m1 c_m2 c_m3].
          try unfold Zlen in *; try unfold HRep.Zlength in *; try unfold Zlength in *; lia.
        + rewrite app_nil_r. reflexivity.
        + exact PmZw.seed_free_nil.
        + rewrite PmZw.Zlen_nil. lia.
        + left; reflexivity.
        + reflexivity.
        + left; reflexivity.
        + right. pose proof AACC as (_ & _ & A3). destruct (A3 Hop) as [E|E]; [unfold OT_RESULT_ID in E; lia|].
          split; [exact E|]. split; [exact Hop|]. cbn [set_m3A c_m3].
          try unfold Zlen in *; try unfold HRep.Zlength in *; try unfold Zlength in *; lia.
        + intros []. }

    assert (K1 : forall sb c1 s1 LB1 LBs1 m1 mo1 msF1 R1 F1 fc1 (nw : Z),
      as_AKREL H s1 (mkCfg msF1 mo1) -> as_VIS H s1 msF1 = MS R1 F1 (Z_to_bv 64 0xf4164) fc1 None m1 (seg_rom asegs) -> rfull R1 -> frm_zero fc1 ->
      PMXAT H LINV w s1 LB1 LBs1 m1 mo1 (set_trA c1 (tr_of sb)) S_STR TBL_EEF44 [] [] 0 ->
      c_tr c1 = [] -> pm_bud (wa_n w) (set_trA c1 (tr_of sb)) -> (forall q k, In (q, k) (c_blocks (set_trA c1 (tr_of sb))) -> k <= 2 ^ 40) ->
      0 <= pm_phi_blocks (tr_of sb) <= PM_STRK * nw ->
      regs_tbl w R1 RT_S8D1 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
      (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) ->
      shdrA H w m1 sb ->
      rw_cells asegs m1 (wa_ff w + 114) [C2 (Z_to_bv 64 nw)] -> 1 <= nw < 2 ^ 16 ->
      rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 11)] -> ffkeepX w STR_X m m1 ->
      (c1 = c \/ (i_op I = OP_EXT_INST_IMPORT /\ exists tt, c1 = set_m3A c tt
                   /\ Zlength (t3c (c_m3 c)) <= Zlength (t3c tt) <= Zlength (t3c (c_m3 c)) + 1 /\ macctA c1)) ->
      as_SR H Q (mkCfg msF1 mo1)).
    { intros sb c1 s1 LB1 LBs1 m1 mo1 msF1 R1 F1 fc1 nw KR1 VIS1 RF1 FZ1 X1 Htr1 BUD1 Hbsz1 PHI1 HT1 G3_1 G4_1 KX1 SH1 C114 Hnw C116 FK1 CR1.
      eapply (str_dtor H HHbp LINV LINV_frame LINV_cl HOWN true w s1 LB1 LBs1 m1 mo1 _ msF1 R1 F1 fc1 0 11 sb Q
                OK X1 eq_refl BUD1 Hbsz1 KR1 VIS1 RF1 FZ1 HT1 G3_1 G4_1 SH1 C116 ltac:(unfold PM_STRK, PM_RESERVE in *; lia)).
      intros s2 LB2 LBs2 msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 BUD2 HT2 G3_2 G4_2 KX2 FK2.
      rewrite (set_tr_nil_back c1 _ Htr1) in X2, BUD2.
      assert (Hbszc1 : forall q k, In (q, k) (c_blocks c1) -> k <= 2 ^ 40).
      { intros q k Hin. apply (Hbsz1 q k). rewrite (c_blocks_set_tr c1 _ Htr1). apply in_or_app. left. exact Hin. }
      apply (PKW c1 s2 LB2 LBs2 m2 mo2 msF2 R2 F1 fc1 _ nw KR2 VIS2 RF2 FZ1 X2 ltac:(lia) HT2 G3_2 G4_2).
      - intros rr Hrr. rewrite (KX2 rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inlistT)). exact (KX1 rr Hrr).
      - exact (FK2 114 [C2 (Z_to_bv 64 nw)] ltac:(lia) ltac:(cbn; lia) C114).
      - exact Hnw.
      - exact (FK2 116 [C4 (Z_to_bv 64 11)] ltac:(lia) ltac:(cbn; lia) C116).
      - exact (ffkeepX_trans w STR_X [] STR_X m m1 m2 FK1 (ffkeepX_nil w m1 m2 FK2) (incl_refl _) (fun x (Hx : In x []) => match Hx with end)).
      - exact Htr1.
      - exact BUD2.
      - exact Hbszc1.
      - exact CR1. }

    assert (K0 : forall sb s1 LB1 LBs1 m1 mo1 msF1 R1 F1 fc1 (spal1 ty e : Z),
      as_AKREL H s1 (mkCfg msF1 mo1) -> as_VIS H s1 msF1 = MS R1 F1 (Z_to_bv 64 0xf4164) fc1 None m1 (seg_rom asegs) -> rfull R1 -> frm_zero fc1 ->
      PMXAT H LINV w s1 LB1 LBs1 m1 mo1 (set_trA c (tr_of sb)) S_STR TBL_EEF44 [] [] spal1 ->
      pm_bud (wa_n w) (set_trA c (tr_of sb)) -> (forall q k, In (q, k) (c_blocks (set_trA c (tr_of sb))) -> k <= 2 ^ 40) ->
      spal1 + pm_phi_blocks (tr_of sb) <= PM_RESERVE ->
      regs_tbl w R1 RT_S8D0 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
      PropExec.getr R1 23%bv = Z_to_bv 64 (sx32A e) -> 0 < e < 2 ^ 32 ->
      shdrA H w m1 sb -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
      as_SR H Q (mkCfg msF1 mo1)).
    { intros sb s1 LB1 LBs1 m1 mo1 msF1 R1 F1 fc1 spal1 ty e KR1 VIS1 RF1 FZ1 X1 BUD1 Hbsz1 SP1 HT1 G3_1 G4_1 G23_1 He SH1 TY1.
      eapply (str_dtor H HHbp LINV LINV_frame LINV_cl HOWN false w s1 LB1 LBs1 m1 mo1 _ msF1 R1 F1 fc1 spal1 ty sb Q
                OK X1 eq_refl BUD1 Hbsz1 KR1 VIS1 RF1 FZ1 HT1 G3_1 G4_1 SH1 TY1 SP1).
      intros s2 LB2 LBs2 msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 BUD2 HT2 G3_2 G4_2 KX2 FK2.
      rewrite (set_tr_nil_back c _ Htr) in X2, BUD2.
      apply (CK s2 LB2 LBs2 m2 mo2 c msF2 R2 F1 fc1 TBL_EEF44 _ e X2 (incl_refl _) Htr BUD2 Hbsz KR2 VIS2 RF2 FZ1 HT2 G3_2 G4_2); [| exact He].
      rewrite (KX2 23%bv ltac:(inlistT)). exact G23_1. }

    eapply (pm_s8a H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 (proj1 Hw)).
    intros msFa moa ma Ra KRa VISa RFa Xa HTa G3a G4a G1a G2a G10a G11a G12a G13a G21a FKa KXa.
    eapply (pm_mkstr H HHbp LINV LINV_cl HOWN HMS w s LB LBs ma moa c _ TBL_EEF44 [] msFa Ra F fc 0xf1edc 5936 Q OK Xa
              ltac:(vm_compute; reflexivity) ltac:(reflexivity) Htr BUD (proj1 Hw) KRa VISa RFa G1a ltac:(reflexivity) ltac:(lia)
              G2a G4a G10a G11a G12a ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(reflexivity) (Forall_nil _)).
    intros msFb mob mb Rb sS LBb sb pid ws KRb VISb RFb Xb BUDb KEEPb HZws HSb SBb HSBb FKb.
    assert (HTb : regs_tbl w Rb RT_S8B) by (exact (regs_keep w [] Ra Rb RT_S8CALL HTa KEEPb)).
    assert (G3b : PropExec.getr Rb 3%bv = wa_gp w) by (rewrite (KEEPb 3%bv ltac:(inlistT)); exact G3a).
    assert (G4b : PropExec.getr Rb 4%bv = wa_tp w) by (rewrite (KEEPb 4%bv ltac:(inlistT)); exact G4a).
    assert (KXb : forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr Rb rr = PropExec.getr R rr).
    { intros rr Hrr. rewrite (KEEPb rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inlistT)). exact (KXa rr Hrr). }
    assert (G21b : PropExec.getr Rb 21%bv = Z_to_bv 64 (wa_n w - c_widx c)) by (rewrite (KEEPb 21%bv ltac:(inlistT)); exact G21a).
    assert (G22b : PropExec.getr Rb 22%bv = Z_to_bv 64 (i_op I)) by (rewrite (KXb 22%bv ltac:(inlistT)); exact Q22).
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ Xb) as FWb. change (fsz PM_FCLASS) with 16384 in FWb.
    assert (Hbszb : forall q k, In (q, k) (c_blocks (set_trA c (tr_of sb))) -> k <= 2 ^ 40).
    { intros q k Hin. rewrite (c_blocks_set_tr c _ Htr) in Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hbsz q k Hin)|].
      pose proof BUDb as (_ & _ & _ & _ & _ & _ & _ & _ & BT). pose proof (BT (q, k) Hin) as Hk. cbn [snd] in Hk. lia. }
    assert (PHIb : 0 <= pm_phi_blocks (tr_of sb) <= 2 ^ 30).
    { rewrite pm_phi_tr_of. destruct sb as [|d asz]; [lia|].
      destruct HSBb as (_ & _ & A1 & A2 & A3).
      destruct (Z.ltb_spec 64512 asz); [|lia].
      destruct A2 as [A2|A2]; lia. }
    assert (FKmb : ffkeepX w [(5936, 24)] m mb).
    { intros k cs Hk0 Hn0 Fx C. apply (FKb k cs Hk0 Hn0); [| exact (FKa k cs Hk0 Hn0 (Forall_nil _) C)].
      apply Forall_inv in Fx. cbn [fst snd] in Fx. lia. }
    assert (TYb : rw_cells asegs mb (wa_ff w + 116) [C4 (Z_to_bv 64 t)]).
    { pose proof PO as (_ & _ & K116 & _).
      exact (ffkeepX_cell w _ m mb 116 _ FKmb K116 ltac:(lia) ltac:(cbn; lia) ltac:(vm_compute; reflexivity)). }
    assert (SHb : shdrA H w mb sb).
    { destruct sb as [|d asz].
      - destruct (str_hdr_short H w LBb mb (ms_chars ws) FWb ltac:(lia) HSb) as (C0 & HL).
        exists (2 * Zlen (ms_chars ws)). split; [exact C0|]. split; [lia|]. apply even2_mod.
      - destruct HSBb as (_ & _ & A1 & _).
        destruct (str_hdr_long H w LBb mb d asz (ms_chars ws) FWb ltac:(lia) ltac:(lia) HSb) as (b0 & C0 & Hb0 & _ & CCP & CDP & Hd & _).
        exists b0, (asz + 1). exact (conj C0 (conj (proj1 Hb0) (conj (proj2 Hb0) (conj CCP (conj CDP Hd))))). }

    assert (KEX : forall msF1 mo1 m1 R1, as_AKREL H sS (mkCfg msF1 mo1) -> as_VIS H sS msF1 = MS R1 F (Z_to_bv 64 AEXHAUSTED) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXA H LINV w sS LBb (spb_own sb pid ++ LBs) m1 mo1 (set_trA c (tr_of sb)) S_STR TBL_EEF44 [] -> regs_tbl w R1 RT_S8C ->
       PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf2dec ->
       PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 8%bv = Z_to_bv 64 (wa_sp0 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 (wa_p w) ->
       PropExec.getr R1 11%bv = PropExec.getr Rb 25%bv -> PropExec.getr R1 12%bv = PropExec.getr Rb 22%bv -> PropExec.getr R1 13%bv = PropExec.getr Rb 18%bv ->
       m1 = mb -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr Rb rr) -> as_SR H Q (mkCfg msF1 mo1)).
    { intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 G1_1 G2_1 G8_1 G10_1 G11_1 G12_1 G13_1 EM1 KX1. subst m1.
      assert (G11 : PropExec.getr R1 11%bv = Z_to_bv 64 (i_io I)) by (rewrite G11_1, (KXb 25%bv ltac:(inlistT)); exact Q25).
      assert (G12 : PropExec.getr R1 12%bv = Z_to_bv 64 (i_op I)) by (rewrite G12_1; exact G22b).
      assert (G13 : PropExec.getr R1 13%bv = Z_to_bv 64 t) by (rewrite G13_1, (KXb 18%bv ltac:(inlistT)); exact Q18).
      eapply (pm_exhausted H HHbp LINV HEX w sS LBb _ mb mo1 _ _ TBL_EEF44 [] 0 msF1 R1 F fc 0xf2dec (i_io I) (i_op I) t Q
                OK X1 ltac:(vm_compute; reflexivity) ltac:(reflexivity) KR1 VIS1 RF1 FZ0 G1_1 ltac:(reflexivity) ltac:(lia)
                G2_1 G8_1 G4_1 G10_1 G11 G12 G13 ltac:(lia) IOP ltac:(lia) ltac:(unfold PM_RESERVE; lia) ltac:(inlistT)).
      intros msF2 mo2 m2 R2 F2 fc2 s2 LB2 KR2 VIS2 RF2 FZ2 X2 KEEP2 G10_2 KC2.
      assert (HT2 : regs_tbl w R2 RT_S8C) by (exact (regs_keep w [] R1 R2 RT_S8C HT1 KEEP2)).
      assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inlistT)); exact G3_1).
      assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inlistT)); exact G4_1).
      eapply (pm_s8x H HHbp LINV LINV_frame w s2 LB2 _ m2 mo2 _ msF2 R2 F2 fc2 _ Q OK X2 Logic.I Hbszb KR2 VIS2 RF2 FZ2 HT2 G3_2 G4_2).
      intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 G23_3 EM3. subst m3.
      apply (K0 _ s2 LB2 _ m2 mo3 msF3 R3 F2 fc2 _ t (2 ^ 32 - 4) KR3 VIS3 RF3 FZ2 X3 BUDb Hbszb ltac:(unfold PM_RESERVE; lia) HT3 G3_3 G4_3).
      - rewrite G23_3, G10_2. exact err_m4.
      - lia.
      - exact (shdrA_keep H w mb m2 _ SHb KC2).
      - exact (KC2 116 [C4 (Z_to_bv 64 t)] ltac:(lia) ltac:(cbn; lia) TYb). }

    assert (KIMP : i_op I = 11 -> Zlen (ms_chars ws) < 262140 ->
       forall msF1 mo1 m1 R1, as_AKREL H sS (mkCfg msF1 mo1) -> as_VIS H sS msF1 = MS R1 F (Z_to_bv 64 AT_IMPORT_TYPE_GET) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXA H LINV w sS LBb (spb_own sb pid ++ LBs) m1 mo1 (set_trA c (tr_of sb)) S_STR TBL_EEF44 [] -> regs_tbl w R1 RT_S8C ->
       PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf31d8 ->
       PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 8%bv = Z_to_bv 64 (wa_sp0 w) ->
       PropExec.getr R1 10%bv = Z_to_bv 64 (str_data (wa_ff w + 5936) sb) ->
       rw_cells asegs m1 (wa_ff w + 114) [C2 (Z_to_bv 64 (Zlen (ms_chars ws) / 4 + 1))] -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 11)] ->
       ffkeepX w [(116, 4); (114, 2)] mb m1 -> munch (s8b_wins (wa_ff w)) mb m1 -> wmono asegs mb m1 ->
       (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr Rb rr) -> as_SR H Q (mkCfg msF1 mo1)).
    { intros OP HLT msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 G1_1 G2_1 G8_1 G10_1 C114 C116 FK1 MU1 WM1 KX1.
      pose proof (wk_stack H w OK) as (WS1 & WS2 & _).
      pose proof (wk_s1 H w OK) as (WS3 & _).
      pose proof (xp_geom H HHt w OK) as (XG1 & XG2 & XG3 & XG4 & XG5 & XG6 & _).
      assert (SHq : forall a, sh a = a / 8 + SHBASE) by (intros a; clear - Q13; unfold sh in *; lia).
      pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ Xb) as RHb.
      assert (DJp : forall W, (W = s8b_wins (wa_ff w) \/ W = [(wa_s1 w - IT_STACK, wa_s1 w)]) -> disjoint_from W (wa_ff w + 5936) 24).
      { intros W HW. clear - HW Q3 Q6 Q13 BND WS1 WS2 WS3. rewrite Q13 in Q6. unfold SHBASE, APM_STACK in *.
        destruct HW as [-> | ->]; unfold s8b_wins, IT_STACK, AINTRIN_STACK; cbn [disjoint_from]; repeat split; Z.div_mod_to_equations; lia. }
      assert (DLk : forall W, (W = s8b_wins (wa_ff w) \/ W = [(wa_s1 w - IT_STACK, wa_s1 w)]) ->
                 forall d asz, sb = SLong d asz -> disjoint_from W d asz /\ disjoint_from W (sh d) (nsh asz)).
      { intros W HW d asz Esb. subst sb. destruct HSBb as (INb & _).
        pose proof (ah_blocks H HHt _ _ _ (pid, d, asz) RHb INb) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
        cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
        rewrite (SHq d). unfold nsh.
        clear - HW R0 R16 Rn RI RC RF RAPP XG1 XG2 XG6 BND AC1 AC2 Q3 WS1 WS2 WS3.
        unfold aapp, aapp_lo, aapp_hi in RAPP, XG6.
        unfold ALOWSH_LO, AHI_LO, AIMG_TOP, SHBASE, APM_STACK, AFS_HDR in *.
        destruct HW as [-> | ->]; unfold s8b_wins, IT_STACK, AINTRIN_STACK; cbn [disjoint_from];
          destruct RAPP as [[? ?]|[? ?]]; destruct XG6 as [[? ?]|[? ?]]; repeat split; Z.div_mod_to_equations; lia. }
      destruct (str_keep_munch _ LBb mb m1 _ sb pid _ HSb SBb MU1 WM1 (DJp _ (or_introl eq_refl)) (DLk _ (or_introl eq_refl)))
        as (HS1 & SB1).
      eapply (pm_import H HHbp LINV LINV_frame HITG w sS LBb _ m1 mo1 _ _ TBL_EEF44 [] [] 0 msF1 R1 F fc 0xf31d8 sb pid (ms_chars ws) Q
                OK X1 ltac:(vm_compute; reflexivity) ltac:(reflexivity) KR1 VIS1 RF1 G1_1 ltac:(reflexivity) ltac:(lia) G2_1 G10_1
                HS1 SB1 ltac:(vm_compute; reflexivity) (PmArm_StrLibS1.ms_chars_nz ws) ltac:(lia)).
      intros msF3 mo3 m3 R3 r KR3 VIS3 RF3 X3 KEEP3 MU3 WM3 Hr G10_3.
      destruct (str_keep_munch _ LBb m1 m3 _ sb pid _ HS1 SB1 MU3 WM3 (DJp _ (or_intror eq_refl)) (DLk _ (or_intror eq_refl)))
        as (HS3 & SB3).
      assert (FK3 : ffkeepX w [] m1 m3).
      { apply (ffkeepX_munch w [] _ m1 m3 MU3 WM3). apply Forall_cons; [left; cbn [fst] | apply Forall_nil].
        clear - Q3 WS1 WS2 WS3. unfold IT_STACK, AINTRIN_STACK, APM_STACK in *. lia. }
      assert (HT3 : regs_tbl w R3 RT_S8C) by (exact (regs_keep w [] R1 R3 RT_S8C HT1 KEEP3)).
      assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (KEEP3 3%bv ltac:(inlistT)); exact G3_1).
      assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (KEEP3 4%bv ltac:(inlistT)); exact G4_1).
      assert (C114_3 : rw_cells asegs m3 (wa_ff w + 114) [C2 (Z_to_bv 64 (Zlen (ms_chars ws) / 4 + 1))])
        by (exact (FK3 114 [C2 (Z_to_bv 64 (Zlen (ms_chars ws) / 4 + 1))] ltac:(lia) ltac:(cbn; lia) (Forall_nil _) C114)).
      assert (C116_3 : rw_cells asegs m3 (wa_ff w + 116) [C4 (Z_to_bv 64 11)])
        by (exact (FK3 116 [C4 (Z_to_bv 64 11)] ltac:(lia) ltac:(cbn; lia) (Forall_nil _) C116)).
      assert (FKm3 : ffkeepX w STR_X m m3).
      { exact (ffkeepX_trans w STR_X [] STR_X m m1 m3 (ffkeepX_trans w _ _ STR_X m mb m1 FKmb FK1 IXa IXb) FK3
                 (incl_refl _) (fun x (Hx : In x []) => match Hx with end)). }
      assert (KX3 : forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R3 rr = PropExec.getr R rr).
      { intros rr Hrr. rewrite (KEEP3 rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inlistT)), (KX1 rr Hrr).
        exact (KXb rr Hrr). }
      assert (SH3 : shdrA H w m3 sb).
      { apply (shdrA_keepX H w [] m1 m3 sb); [| exact FK3 | reflexivity].
        exact (shdrA_keepX H w _ mb m1 sb SHb FK1 ltac:(vm_compute; reflexivity)). }
      destruct (Z.eq_dec r 0) as [Rz | Rnz].
      - subst r.
        destruct sb as [|d asz].
        + eapply (badimp_short w sS LBb _ m3 mo3 _ msF3 R3 F fc pid (ms_chars ws) 11 Q
                    OK X3 eq_refl BUDb Hbszb KR3 VIS3 RF3 FZ0 HT3 G3_3 G4_3 G10_3 HS3 C116_3).
          intros s4 LB4 LBs4 msF4 mo4 m4 R4 F4 fc4 spal4 KR4 VIS4 RF4 FZ4 X4 SP4 HT4 G3_4 G4_4 G23_4 SH4 TY4.
          exact (K0 SShort s4 LB4 LBs4 m4 mo4 msF4 R4 F4 fc4 spal4 11 (2 ^ 32 - 4) KR4 VIS4 RF4 FZ4 X4 BUDb Hbszb
                   ltac:(unfold PM_RESERVE; lia) HT4 G3_4 G4_4 G23_4 ltac:(lia) SH4 TY4).
        + eapply (HBADL w sS LBb _ m3 mo3 _ msF3 R3 F fc d asz pid (ms_chars ws) 11 Q
                    OK X3 eq_refl BUDb Hbszb KR3 VIS3 RF3 FZ0 HT3 G3_3 G4_3 G10_3 HS3 SB3 (PmArm_StrLibS1.ms_chars_nz ws) HLT C116_3).
          intros s4 LB4 LBs4 msF4 mo4 m4 R4 F4 fc4 spal4 KR4 VIS4 RF4 FZ4 X4 SP4 HT4 G3_4 G4_4 G23_4 SH4 TY4.
          exact (K0 (SLong d asz) s4 LB4 LBs4 m4 mo4 msF4 R4 F4 fc4 spal4 11 (2 ^ 32 - 4) KR4 VIS4 RF4 FZ4 X4 BUDb Hbszb
                   ltac:(unfold PM_RESERVE; lia) HT4 G3_4 G4_4 G23_4 ltac:(lia) SH4 TY4).
      - pose proof (ifrA_ffkeepX H w m m3 STR_X FR FKm3 ltac:(vm_compute; reflexivity)) as FR3.
        destruct FR3 as (ext & tid & rid & _ & _ & _ & _ & C9060 & _ & _ & _ & _ & Hrid).
        assert (MACb : macctA (set_trA c (tr_of sb))).
        { pose proof MAC as (M1 & M2 & M3 & M4 & _). exact (conj M1 (conj M2 (conj M3 M4))). }
        assert (Ht11 : t = OT_LITERAL_STRING).
        { pose proof AACC as (_ & _ & A3). destruct (A3 OP) as [E|E]; [unfold OT_RESULT_ID in E; lia | exact E]. }
        assert (ACC3 : 3 * (Zlength (t3c (c_m3 (set_trA c (tr_of sb)))) + 1) <= wa_n w + 3).
        { pose proof AACC as (_ & A2 & _). destruct (A2 Ht11 OP) as (A21 & _). cbn [set_trA c_m3].
          try unfold Zlen in *; try unfold HRep.Zlength in *; try unfold Zlength in *; lia. }
        eapply (str_import_ok H HHbp LINV LINV_frame LINV_cl LINV_relro HOWN w sS LBb _ m3 mo3 _ msF3 R3 F fc r rid Q
                  OK X3 Hbszb BUDb MACb KR3 VIS3 RF3 FZ0 HT3 G3_3 G4_3 G10_3 ltac:(lia) C9060 Hrid ACC3).
        intros s4 LB4 LBs4 msF4 mo4 m4 R4 F4 fc4 tt KR4 VIS4 RF4 FZ4 X4 BUD4 Hbsz4 MAC4 Htt HT4 G3_4 G4_4 KX4 FK4.
        apply (K1 sb (set_m3A c tt) s4 LB4 LBs4 m4 mo4 msF4 R4 F4 fc4 (Zlen (ms_chars ws) / 4 + 1) KR4 VIS4 RF4 FZ4 X4 Htr BUD4 Hbsz4).
        + rewrite pm_phi_tr_of. unfold PM_STRK. unfold Zlen in *. destruct sb as [|d asz]; [Z.div_mod_to_equations; lia|].
          destruct HSBb as (_ & _ & _ & ASZ2 & _).
          destruct (Z.ltb_spec 64512 asz); [|Z.div_mod_to_equations; lia].
          destruct ASZ2 as [A2|A2]; [lia|]. Z.div_mod_to_equations; lia.
        + exact HT4.
        + exact G3_4.
        + exact G4_4.
        + intros rr Hrr. rewrite (KX4 rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inlistT)). exact (KX3 rr Hrr).
        + exact (shdrA_keepX H w [] m3 m4 sb SH3 FK4 eq_refl).
        + exact (FK4 114 [C2 (Z_to_bv 64 (Zlen (ms_chars ws) / 4 + 1))] ltac:(lia) ltac:(cbn; lia) (Forall_nil _) C114_3).
        + unfold Zlen in *. Z.div_mod_to_equations; lia.
        + exact (FK4 116 [C4 (Z_to_bv 64 11)] ltac:(lia) ltac:(cbn; lia) (Forall_nil _) C116_3).
        + exact (ffkeepX_trans w STR_X [] STR_X m m3 m4 FKm3 FK4 (incl_refl _) (fun x (Hx : In x []) => match Hx with end)).
        + right. split; [exact OP|]. exists tt. split; [reflexivity|]. split; [exact Htt | exact MAC4]. }

    destruct sb as [|d asz].
    - destruct (str_hdr_short H w LBb mb (ms_chars ws) FWb ltac:(lia) HSb) as (C0b & HLb).
      destruct (Z.eq_dec (4 * (wa_n w - c_widx c)) (Zlen (ms_chars ws))) as [EX|NEX].
      + exact (pm_s8b_sx H HHbp LINV LINV_frame w sS LBb _ mb mob _ msFb Rb F fc (Zlen (ms_chars ws)) (i_op I) Q
                 OK Xb Logic.I Hbszb KRb VISb RFb FZ0 HTb G3b G4b C0b HLb G21b G22b IOP EX KEX).
      + destruct (Z.eq_dec (i_op I) 11) as [OP|NOP].
        * eapply (pm_s8b_si H HHbp LINV LINV_frame w sS LBb _ mb mob _ msFb Rb F fc (Zlen (ms_chars ws)) (i_op I) Q
                    OK Xb Logic.I Hbszb KRb VISb RFb FZ0 HTb G3b G4b C0b HLb G21b G22b IOP NEX OP).
          intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 G1_1 G2_1 G8_1 G10_1 C114 C116 FK1 MU1 WM1 KX1.
          apply (KIMP OP ltac:(lia) msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 G1_1 G2_1 G8_1); try assumption.
          rewrite G10_1. cbn [str_data]. f_equal; lia.
        * eapply (pm_s8b_sp H HHbp LINV LINV_frame w sS LBb _ mb mob _ msFb Rb F fc (Zlen (ms_chars ws)) (i_op I) Q
                    OK Xb Logic.I Hbszb KRb VISb RFb FZ0 HTb G3b G4b C0b HLb G21b G22b IOP NEX NOP).
          intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 KX1 C114 C116 FK1.
          apply (PKW _ sS LBb _ m1 mo1 msF1 R1 F fc 0 (Zlen (ms_chars ws) / 4 + 1) KR1 VIS1 RF1 FZ0 X1
                   ltac:(unfold PM_STRK; Z.div_mod_to_equations; lia) HT1 G3_1 G4_1).
          -- intros rr Hrr. rewrite (KX1 rr Hrr). exact (KXb rr Hrr).
          -- exact C114.
          -- Z.div_mod_to_equations; lia.
          -- exact C116.
          -- exact (ffkeepX_trans w _ _ STR_X m mb m1 FKmb FK1 IXa IXb).
          -- reflexivity.
          -- exact BUDb.
          -- exact Hbszb.
          -- left. cbn [tr_of]. rewrite <- Htr. apply set_trA_id.
    - destruct HSBb as (INb & NINb & ASZb & ASZb2 & CLb).
      destruct (str_hdr_long H w LBb mb d asz (ms_chars ws) FWb ltac:(lia) ltac:(lia) HSb)
        as (b0 & C0b & Hb0 & CSZb & CCPb & CDPb & Hd & HLb).
      assert (SZb : 0 <= Zlen (ms_chars ws) < 2 ^ 28) by lia.
      destruct (Z.eq_dec (Zlen (ms_chars ws)) (4 * (wa_n w - c_widx c))) as [EX|NEX].
      + exact (pm_s8b_lx H HHbp LINV LINV_frame w sS LBb _ mb mob _ msFb Rb F fc b0 (Zlen (ms_chars ws)) (asz + 1) d (i_op I) Q
                 OK Xb Logic.I Hbszb KRb VISb RFb FZ0 HTb G3b G4b C0b Hb0 CSZb SZb CCPb CDPb Hd G21b G22b IOP EX KEX).
      + destruct (Z_lt_dec (Zlen (ms_chars ws)) 262140) as [LT|GE].
        * destruct (Z.eq_dec (i_op I) 11) as [OP|NOP].
          -- exact (pm_s8b_li H HHbp LINV LINV_frame w sS LBb _ mb mob _ msFb Rb F fc b0 (Zlen (ms_chars ws)) (asz + 1) d (i_op I) Q
                      OK Xb Logic.I Hbszb KRb VISb RFb FZ0 HTb G3b G4b C0b Hb0 CSZb SZb CCPb CDPb Hd G21b G22b IOP NEX LT OP (KIMP OP LT)).
          -- eapply (pm_s8b_lq H HHbp LINV LINV_frame w sS LBb _ mb mob _ msFb Rb F fc b0 (Zlen (ms_chars ws)) (asz + 1) d (i_op I) Q
                       OK Xb Logic.I Hbszb KRb VISb RFb FZ0 HTb G3b G4b C0b Hb0 CSZb SZb CCPb CDPb Hd G21b G22b IOP NEX LT NOP).
             intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 C114 C116 FK1 MU1 WM1 KX1.
             apply (K1 (SLong d asz) c sS LBb _ m1 mo1 msF1 R1 F fc (Zlen (ms_chars ws) / 4 + 1) KR1 VIS1 RF1 FZ0 X1 Htr BUDb Hbszb).
             ++ rewrite pm_phi_tr_of. unfold PM_STRK. destruct (Z.ltb_spec 64512 asz); [|Z.div_mod_to_equations; lia].
                destruct ASZb2 as [A2|A2]; [lia|]. Z.div_mod_to_equations; lia.
             ++ exact HT1.
             ++ exact G3_1.
             ++ exact G4_1.
             ++ intros rr Hrr. rewrite (KX1 rr Hrr). exact (KXb rr Hrr).
             ++ exact (shdrA_keepX H w _ mb m1 _ SHb FK1 ltac:(vm_compute; reflexivity)).
             ++ exact C114.
             ++ Z.div_mod_to_equations; lia.
             ++ exact C116.
             ++ exact (ffkeepX_trans w _ _ STR_X m mb m1 FKmb FK1 IXa IXb).
             ++ left; reflexivity.
        * eapply (pm_s8b_lg H HHbp LINV LINV_frame w sS LBb _ mb mob _ msFb Rb F fc b0 (Zlen (ms_chars ws)) (asz + 1) d (i_op I) Q
                    OK Xb Logic.I Hbszb KRb VISb RFb FZ0 HTb G3b G4b C0b Hb0 CSZb SZb CCPb CDPb Hd G21b G22b IOP NEX ltac:(lia)).
          intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 G21_1 EM1 KX1. subst m1.
          eapply (pm_s8g H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HU16 HU64 HPDIAG0 w sS LBb _ mb mo1 _ msF1 R1 F fc
                    (Zlen (ms_chars ws) / 4 + 1) b0 (asz + 1) d t Q OK X1 Logic.I Hbszb KR1 VIS1 RF1 FZ0 HT1 G3_1 G4_1 G21_1
                    ltac:(Z.div_mod_to_equations; lia) BUDb C0b CCPb CDPb TYb).
          intros s2 LB2 LBs2 msF2 mo2 m2 R2 F2 fc2 tbl2 spal2 KR2 VIS2 RF2 FZ2 X2 IT2 SP2 HT2 G3_2 G4_2 G23_2 C0_2 CCP2 CDP2 TY2.
          pose proof (pmxa_restrict H HHt LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X2 IT2 (incl_refl _)) as X2r.
          apply (K0 (SLong d asz) s2 LB2 LBs2 m2 mo2 msF2 R2 F2 fc2 spal2 t (2 ^ 32 - 4) KR2 VIS2 RF2 FZ2 X2r BUDb Hbszb
                   ltac:(unfold PM_RESERVE; lia) HT2 G3_2 G4_2 G23_2 ltac:(lia)); [| exact TY2].
          exists b0, (asz + 1). exact (conj C0_2 (conj (proj1 Hb0) (conj (proj2 Hb0) (conj CCP2 (conj CDP2 Hd))))).
Qed.
End TOP.
