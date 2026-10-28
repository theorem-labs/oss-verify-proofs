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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1 PmArm_MaskS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmGlue LbB_PmU2K LbB_PmLH LbB_PmLeaf LbB_PmLeafW LbB_DiagStmt LbB_PmDS LbB_ContStmt LbB_PmVup LbB_PmWG LbB_PmWPT LbB_DStat LbB_TablStmt LbB_PmOL LbB_PmPD LbB_PmSL LbB_RtOwn LbB_PmU3XK LbB_PmU5K LbB_PmU5Ma LbB_PmU5Mb LbB_PmU5Mc LbB_PmU5Md LbB_PiStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac inlM := cbn; repeat (first [left; reflexivity | right]).

Definition mask_etA (t : Z) : Z :=
  if t =? 43 then 35 else if t =? 44 then 40 else if t =? 78 then 77 else if t =? 87 then 86
  else if t =? 92 then 91 else if t =? 104 then 103 else t.

Definition MASK_XS : list (Z * Z) := [(116, 4); (7984, 8); (8480, 16); (8512, 8); (8544, 16)].

Lemma mask_facts : forall t, In t PmHyps.MASK_TYPES -> t <> OT_RESULT_ID /\ t <> OT_LITERAL_INTEGER /\ t <> OT_LITERAL_STRING.
Proof.
  intros t H. unfold OT_RESULT_ID, OT_LITERAL_INTEGER, OT_LITERAL_STRING. unfold PmHyps.MASK_TYPES in H. cbn [In] in H.
  repeat (destruct H as [<-|H]; [repeat split; discriminate|]). destruct H.
Qed.
Lemma mask_etA_range : forall t, 0 <= t < 2 ^ 31 -> 0 <= mask_etA t < 2 ^ 31.
Proof.
  intros t Ht. unfold mask_etA.
  repeat match goal with |- context [if ?x =? ?y then _ else _] => destruct (Z.eqb_spec x y) end; lia.
Qed.
Lemma mask_in_tabl : forall t, In t PmHyps.MASK_TYPES -> In t TablFacts.MASK_TYPES.
Proof. intros t H. exact H. Qed.

Lemma regs_tbl_litM {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) R r z,
  PropExec.getr R r = Z_to_bv 64 z -> PropExec.getr R r = edenot (Eseed bvmap_empty (wenv_vals w ++ [])) (ELit z).
Proof. intros w R r z Hr. rewrite Hr. reflexivity. Qed.
Lemma regs_tbl_snoc_lit {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) R RT r z,
  regs_tbl w R RT -> PropExec.getr R r = Z_to_bv 64 z -> regs_tbl w R (RT ++ [(r, ELit z)]).
Proof.
  intros w R RT r z HT Hr. apply regs_tbl_app; [exact HT|].
  apply Forall_cons; [cbn [fst snd]; exact (regs_tbl_litM w R r z Hr) | apply Forall_nil].
Qed.

Lemma mask_rem_range : forall word j, 0 <= j <= 31 -> 0 <= word mod 2 ^ (j + 1) < 2 ^ 32 /\ 0 <= word mod 2 ^ j < 2 ^ 32.
Proof.
  intros word j Hj.
  pose proof (Z.mod_pos_bound word (2 ^ (j + 1)) ltac:(apply Z.pow_pos_nonneg; lia)) as B1.
  pose proof (Z.mod_pos_bound word (2 ^ j) ltac:(apply Z.pow_pos_nonneg; lia)) as B2.
  assert (P1 : 2 ^ (j + 1) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  assert (P2 : 2 ^ j <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  split; [clear - B1 P1 | clear - B2 P2]; lia.
Qed.
Lemma mask_rem_step : forall word j, 0 <= word -> 0 <= j ->
  (Z.testbit word j = false -> word mod 2 ^ (j + 1) = word mod 2 ^ j)
  /\ (Z.testbit word j = true -> word mod 2 ^ (j + 1) - 2 ^ j = word mod 2 ^ j).
Proof.
  intros word j Hw Hj. pose proof (mod_pow2_step word j Hw Hj) as S.
  split; intros TB; rewrite TB in S; cbv iota in S; rewrite S; ring.
Qed.
Lemma mask_rem_bit : forall word j, 0 <= j -> Z.testbit (word mod 2 ^ (j + 1)) j = Z.testbit word j.
Proof. intros word j Hj. apply testbit_mod_pow2. lia. Qed.
Lemma mask_rem0 : forall word, word mod 2 ^ 0 = 0.
Proof. intros word. change (2 ^ 0) with 1. apply Z.mod_1_r. Qed.
Lemma mask_lui31 : Z_to_bv 64 18446744071562067968 = Z_to_bv 64 (sx32A (2 ^ 31)).
Proof. apply f_equal. vm_compute. reflexivity. Qed.

Record MASKG (n : Z) (c c' : pmc) (L : list Z) : Prop := MkMASKG {
  mg_tr   : c_tr c' = [];
  mg_bsz  : forall q k, In (q, k) (c_blocks c') -> k <= 2 ^ 40;
  mg_bud  : pm_bud n c';
  mg_widx : c_widx c' = c_widx c;
  mg_v1   : c_v1 c' = c_v1 c;
  mg_v2   : c_v2 c' = c_v2 c;
  mg_m1   : c_m1 c' = c_m1 c;
  mg_m2   : c_m2 c' = c_m2 c;
  mg_m3   : c_m3 c' = c_m3 c;
  mg_ic   : c_icount c' = c_icount c;
  mg_en   : c_endian c' = c_endian c;
  mg_rq   : c_reqconv c' = c_reqconv c;
  mg_v3   : t3b (c_v3 c') = t3b (c_v3 c) ++ L;
  mg_sf   : seed_free L;
  mg_nr   : ~ In OT_RESULT_ID L;
  mg_rg   : Forall (fun x => 0 <= x < 2 ^ 31) L
}.

Lemma msg_init : forall n c, c_tr c = [] -> (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> pm_bud n c -> MASKG n c c [].
Proof.
  intros n c Htr Hbsz BUD. constructor; try reflexivity; try assumption.
  - rewrite app_nil_r. reflexivity.
  - exact PmZw.seed_free_nil.
  - intros [].
  - apply Forall_nil.
Qed.

Lemma msg_push : forall n c c1 L b8 cap8 ll t v,
  MASKG n c c1 L -> g_operand TG t v = Some ll ->
  pm_bud n (set_v3A c1 (b8, push_types ll (t3b (c_v3 c1)), cap8)) ->
  exists l2, Zlen l2 <= Zlen ll /\ MASKG n c (set_v3A c1 (b8, push_types ll (t3b (c_v3 c1)), cap8)) (L ++ l2).
Proof.
  intros n c c1 L b8 cap8 ll t v [Htr Hbsz BUD Ewidx Ev1 Ev2 Em1 Em2 Em3 Eic Een Erq Ev3 SF NR RG] GX BUD8.
  pose proof TG_ok as GOK. pose proof (proj1 (proj2 tg_rid1)) as RIDX.
  destruct (PmZw.push_types_split ll (t3b (c_v3 c1))) as (l2 & El2 & Ll2 & Sub2).
  assert (LR : Forall (fun x => 0 <= x < 2 ^ 31) ll).
  { apply Forall_forall. intros x Hx. eapply (go_range _ GOK ll x); [right; left; exists t, v; exact GX | exact Hx]. }
  exists l2. split; [exact Ll2|].
  pose proof (pm_bud_v3bound _ _ BUD8) as CAP8. cbn [set_v3A c_v3 t3c snd] in CAP8.
  constructor.
  - exact Htr.
  - intros q k Hin. destruct (c_blocks_v3_in c1 _ _ _ _ _ Hin) as [Hin'| ->]; [exact (Hbsz _ _ Hin') | clear - CAP8; lia].
  - exact BUD8.
  - exact Ewidx.
  - exact Ev1.
  - exact Ev2.
  - exact Em1.
  - exact Em2.
  - exact Em3.
  - exact Eic.
  - exact Een.
  - exact Erq.
  - cbn [set_v3A c_v3 t3b fst snd]. rewrite El2, Ev3, <- app_assoc. reflexivity.
  - apply PmZw.seed_free_app; [exact SF|]. intros tt Htt. exact (go_operand_zw _ GOK t v ll GX tt (Sub2 tt Htt)).
  - intros Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (NR Hin) | exact (RIDX t v ll GX (Sub2 _ Hin))].
  - apply Forall_app. split; [exact RG|]. apply Forall_forall. intros x Hx. exact (proj1 (Forall_forall _ _) LR x (Sub2 x Hx)).
Qed.

Section U5M.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.
  Hypothesis HPDIAG0 : pdiag0_stmtA H LINV ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV ds_repA.
  Hypothesis HTL : tabl_leavesA.
  Hypothesis HPT : push_types_stmtA H.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.
  Hypothesis HOWN : rt_own H.

  Lemma HHe5 : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Definition cells_apartM (X : list (Z * Z)) (cells : list (Z * Z)) : bool :=
    forallb (fun kn : Z * Z => forallb (fun on : Z * Z => (fst kn + snd kn <=? fst on) || (fst on + snd on <=? fst kn))%bool X) cells.

  Lemma cells_apart_inM : forall X cells k n, cells_apartM X cells = true -> In (k, n) cells ->
    forallb (fun on : Z * Z => (k + n <=? fst on) || (fst on + snd on <=? k))%bool X = true.
  Proof. intros X cells k n Hc Hin. exact (proj1 (forallb_forall _ _) Hc (k, n) Hin). Qed.

  Definition ICTX_CELLSM : list (Z * Z) := [(10112, 8); (9120, 4); (9136, 2); (9050, 2); (9616, 8)].
  Lemma ictxA_ffkeepM : forall (w : pmwA H) m m' I X,
    ictxA H w m I -> ffkeepX w X m m' -> cells_apartM X ICTX_CELLSM = true -> ictxA H w m' I.
  Proof.
    intros w m m' I X (D1 & D2 & D3 & D4 & D5) K B.
    split; [| split; [| split; [| split]]];
      (eapply (ffkeepX_cell w X m m'); [exact K | eassumption | lia | cbn; lia | eapply (cells_apart_inM X ICTX_CELLSM); [exact B | cbn; tauto]]).
  Qed.

  Definition IFR_CELLSM : list (Z * Z) := [(9040, 8); (9048, 2); (9052, 4); (9056, 4); (9060, 4); (9064, 8); (9072, 8)].
  Lemma ifrA_ffkeepM : forall (w : pmwA H) m m' X,
    ifrA H w m -> ffkeepX w X m m' -> cells_apartM X IFR_CELLSM = true -> ifrA H w m'.
  Proof.
    intros w m m' X (ext & tid & rid & D1 & D2 & D3 & D4 & D5 & D6 & D7 & R1 & R2 & R3) K B.
    exists ext, tid, rid.
    do 7 (split; [eapply (ffkeepX_cell w X m m'); [exact K | eassumption | lia | cbn; lia | eapply (cells_apart_inM X IFR_CELLSM); [exact B | cbn; tauto]]|]).
    split; [exact R1|]. split; [exact R2 | exact R3].
  Qed.

  Lemma mdef_appM : forall m a n1 n2, mdef m a n1 -> mdef m (a + n1) n2 -> 0 <= n1 -> mdef m a (n1 + n2).
  Proof.
    intros m a n1 n2 D1 D2 Hn i Hi. destruct (Z.lt_ge_cases i n1); [apply D1; lia|].
    replace (a + i) with (a + n1 + (i - n1)) by lia. apply D2. lia.
  Qed.
  Lemma popnd_mdefM : forall (w : pmwA H) m (v0 v1 v2 v3 v4 v5 : word), pmw_okA H w ->
    rw_cells asegs m (wa_ff w + 112) [C2 v0] -> rw_cells asegs m (wa_ff w + 114) [C2 v1] -> rw_cells asegs m (wa_ff w + 116) [C4 v2] ->
    rw_cells asegs m (wa_ff w + 120) [C4 v3] -> rw_cells asegs m (wa_ff w + 124) [C4 v4] -> rw_cells asegs m (wa_ff w + 128) [C4 v5] ->
    mdef m (wa_ff w + 112) 20.
  Proof.
    intros w m v0 v1 v2 v3 v4 v5 OK C0 C1 C2' C3 C4' C5.
    pose proof (pm_geom H w OK) as G. cbn zeta in G. destruct G as (_ & _ & _ & Q4 & _). unfold AFS_HDR in Q4.
    assert (D : forall k c, rw_cells asegs m (wa_ff w + k) [c] -> 0 <= k -> mdef m (wa_ff w + k) (Z.of_nat (csize c))).
    { intros k c C Hk. pose proof (mdef_of_rw_cells m _ _ C ltac:(lia)) as D. cbn [cells_size] in D. rewrite Nat.add_0_r in D. exact D. }
    pose proof (D 112 _ C0 ltac:(lia)) as D0. pose proof (D 114 _ C1 ltac:(lia)) as D1.
    pose proof (D 116 _ C2' ltac:(lia)) as D2. pose proof (D 120 _ C3 ltac:(lia)) as D3.
    pose proof (D 124 _ C4' ltac:(lia)) as D4. pose proof (D 128 _ C5 ltac:(lia)) as D5.
    cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ] in D0, D1, D2, D3, D4, D5.
    change 20 with (2 + (2 + (4 + (4 + (4 + 4))))).
    apply mdef_appM; [exact D0 | | lia]. replace (wa_ff w + 112 + 2) with (wa_ff w + 114) by lia.
    apply mdef_appM; [exact D1 | | lia]. replace (wa_ff w + 114 + 2) with (wa_ff w + 116) by lia.
    apply mdef_appM; [exact D2 | | lia]. replace (wa_ff w + 116 + 4) with (wa_ff w + 120) by lia.
    apply mdef_appM; [exact D3 | | lia]. replace (wa_ff w + 120 + 4) with (wa_ff w + 124) by lia.
    apply mdef_appM; [exact D4 | | lia]. replace (wa_ff w + 124 + 4) with (wa_ff w + 128) by lia.
    exact D5.
  Qed.

  Lemma popndA_ffkeepM : forall (w : pmwA H) m m' X off t, pmw_okA H w ->
    popndA H w m off t -> ffkeepX w X m m' -> cells_apartM X [(112, 20)] = true ->
    popndA H w m' off t /\ mdef m' (wa_ff w + 112) 20.
  Proof.
    intros w m m' X off t OK (P0 & P1 & P2 & P3 & P4 & P5) K B.
    assert (KK : forall k cs, rw_cells asegs m (wa_ff w + k) cs -> 112 <= k -> k + Z.of_nat (cells_size cs) <= 132 -> rw_cells asegs m' (wa_ff w + k) cs).
    { intros k cs C Hk Hkn. apply (K k cs ltac:(lia) ltac:(lia)); [| exact C].
      apply Forall_forall. intros on Hin. pose proof (cells_apart_inM X [(112, 20)] 112 20 B ltac:(left; reflexivity)) as Q.
      pose proof (proj1 (forallb_forall _ _) Q on Hin) as Q'. cbn beta in Q'.
      apply Bool.orb_true_iff in Q'. destruct Q' as [Q'|Q']; apply Z.leb_le in Q'; lia. }
    pose proof (KK 112 _ P0 ltac:(lia) ltac:(cbn; lia)) as K0. pose proof (KK 114 _ P1 ltac:(lia) ltac:(cbn; lia)) as K1.
    pose proof (KK 116 _ P2 ltac:(lia) ltac:(cbn; lia)) as K2. pose proof (KK 120 _ P3 ltac:(lia) ltac:(cbn; lia)) as K3.
    pose proof (KK 124 _ P4 ltac:(lia) ltac:(cbn; lia)) as K4. pose proof (KK 128 _ P5 ltac:(lia) ltac:(cbn; lia)) as K5.
    split; [exact (conj K0 (conj K1 (conj K2 (conj K3 (conj K4 K5)))))|].
    exact (popnd_mdefM w m' _ _ _ _ _ _ OK K0 K1 K2 K3 K4 K5).
  Qed.

  Lemma pmxa_restrictM : forall w s LB LBs m mo c ins tbl ftbl TB spal tbl' ftbl',
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    incl tbl' tbl -> incl ftbl' ftbl -> PMXAT H LINV w s LB LBs m mo c ins tbl' ftbl' TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal tbl' ftbl' OK X It If.
    eapply (pmxa_munch H HHe5 LINV LINV_frame w s LB LBs m mo c ins tbl ftbl TB spal m [] tbl' ftbl' OK X (munch_refl [] m)
              (wmono_refl asegs m) (fun x Hx => Hx) (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
              (Forall_nil _) (Forall_nil _) I I It); [| exact If |].
    - apply Forall_forall. intros ke _. exact I.
    - apply Forall_forall. intros ke _. exact I.
  Qed.

  Lemma ff_cell4_junkM : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal k,
    PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> pmw_okA H w -> 0 <= k -> k + 4 <= 16384 ->
    exists x, 0 <= x < 2 ^ 32 /\ rw_cells asegs m (wa_ff w + k) [C4 (Z_to_bv 64 x)].
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal k X OK Hk Hk4.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    destruct (ff_junk H LINV w s LB LBs m mo c ins tbl ftbl TB spal k 4 X ltac:(unfold AIMG_TOP, AFS_HDR in *; lia) Hk ltac:(lia) ltac:(lia))
      as (bs & RB).
    change (Z.to_nat 4) with 4%nat in RB.
    assert (L : length bs = 4%nat).
    { destruct RB as [[WF _] _]. destruct WF as [C _]. cbn in C. exact C. }
    destruct (cb4_as_c4 m _ bs L RB) as [C R]. exists (bytes_le_to_Z bs). split; [exact R | exact C].
  Qed.

  Lemma popndA_set_typeM : forall (w : pmwA H) m m' off t (t' : Z),
    popndA H w m off t -> ffkeepX w [(116, 4)] m m' -> rw_cells asegs m' (wa_ff w + 116) [C4 (Z_to_bv 64 t')] ->
    popndA H w m' off t'.
  Proof.
    intros w m m' off t t' (P0 & P1 & P2 & P3 & P4 & P5) K C.
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact P0 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact P1 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [exact C|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact P3 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact P4 | lia | cbn; lia | vm_compute; reflexivity]|].
    eapply (ffkeepX_cell w _ m m'); [exact K | exact P5 | lia | cbn; lia | vm_compute; reflexivity].
  Qed.

  Record MASKC (w : pmwA H) (I : ictxR) (c : pmc) (t : Z) (m0 : mem) (fc : bv 32) (Q : config -> Prop) : Prop := MkMASKC {
    mc_ok   : pmw_okA H w;
    mc_in   : In t PmHyps.MASK_TYPES;
    mc_t    : 0 <= t < 2 ^ 31;
    mc_fz   : frm_zero fc;
    mc_ip   : ipureA I;
    mc_ictx : ictxA H w m0 I;
    mc_ifr  : ifrA H w m0;
    mc_ic   : c_icount c + 4 <= i_io I;
    mc_end  : c_endian c = c_reqconv c /\ (c_endian c = 0 \/ c_endian c = 1);
    mc_w    : wa_words w <> 0 /\ 5 <= wa_n w;
    mc_acc  : pi_macct c;
    mc_v3r  : Forall (fun t => 0 <= t < 2 ^ 31) (t3b (c_v3 c));
    mc_len  : Zlen (t3b (c_v3 c)) <= 127 * (c_widx c - i_io I) + 2;
    mc_w1   : i_io I + 1 <= c_widx c < wa_n w;
    mc_w2   : c_widx c < i_io I + i_iwc I;
    mc_pk   : PUSHKA H LINV w I Q c t;
    mc_ck   : CHECKKA H LINV w Q;
    mc_trc  : trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF];
    mc_trr  : trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF]
  }.

  Lemma mask_budm : forall w I c t m0 fc Q c1 (L ll : list Z), MASKC w I c t m0 fc Q ->
    MASKG (wa_n w) c c1 L -> Zlen L <= 96 -> Zlen ll <= 3 ->
    forall b'' xs'' cap'', 0 <= cap'' <= capmax (Zlen (t3b (c_v3 c1))) (t3c (c_v3 c1)) (Zlen ll) ->
      pm_bud (wa_n w) (set_v3A c1 (b'', xs'', cap'')).
  Proof.
    intros w I c t m0 fc Q c1 L ll MC SG HL Hll b'' xs'' cap'' Hc.
    destruct MC as [OK HIn Ht31 FZ0 IP IC0 FR0 Hic Hend Hw MAC V3R Hlen Hw1 Hw2 PK CK TRC TRR].
    destruct SG as [Htr Hbsz BUD Ewidx Ev1 Ev2 Em1 Em2 Em3 Eic Een Erq Ev3 SF NR RG].
    apply pm_bud_v3cap; [exact BUD|].
    pose proof (pm_bud_v3bound _ _ BUD) as CAPB.
    unfold capmax in Hc. rewrite Ev3, PmZw.Zlen_app in Hc.
    pose proof (ipure_ranges I IP) as [IWC IOP].
    clear - Hc CAPB Hll HL Hlen Hw2 IWC Hw1. lia.
  Qed.

  Lemma mask_pushk : forall w I c t m0 F fc Q, MASKC w I c t m0 fc Q ->
    forall s9 LB9 LBs9 m9 mo9 c9 msF9 R9 L9,
      PMXA H LINV w s9 LB9 LBs9 m9 mo9 c9 S_OPER TBL_EEF44 [] -> as_AKREL H s9 (mkCfg msF9 mo9) ->
      as_VIS H s9 msF9 = MS R9 F (Z_to_bv 64 OL_PUSHK) fc None m9 (seg_rom asegs) -> rfull R9 ->
      regs_tbl w R9 RT_PUSHK -> PropExec.getr R9 3%bv = wa_gp w -> PropExec.getr R9 4%bv = wa_tp w ->
      PropExec.getr R9 22%bv = Z_to_bv 64 (i_op I) -> PropExec.getr R9 25%bv = Z_to_bv 64 (i_io I) ->
      PropExec.getr R9 18%bv = Z_to_bv 64 t ->
      MASKG (wa_n w) c c9 L9 -> Zlen L9 <= 125 ->
      ffkeepX w MASK_XS m0 m9 -> popndA H w m9 (c_widx c - i_io I) (mask_etA t) ->
      as_SR H Q (mkCfg msF9 mo9).
  Proof.
    intros w I c t m0 F fc Q MC s9 LB9 LBs9 m9 mo9 c9 msF9 R9 L9 X9 KR9 VIS9 RF9 HT9 G3_9 G4_9 Q22 Q25 Q18 SG HL FK9 PO9.
    destruct MC as [OK HIn Ht31 FZ0 IP IC0 FR0 Hic Hend Hw MAC V3R Hlen Hw1 Hw2 PK CK TRC TRR].
    destruct SG as [Htr Hbsz BUD Ewidx Ev1 Ev2 Em1 Em2 Em3 Eic Een Erq Ev3 SF NR RG].
    pose proof (mask_facts t HIn) as Ht36.
    destruct (popndA_ffkeepM w m9 m9 [] _ _ OK PO9 (ffkeepX_refl w [] m9) eq_refl) as [_ MD9].
    destruct PO9 as (K112 & K114 & K116 & _).
    eapply (PK s9 LB9 LBs9 m9 mo9 c9 msF9 R9 F fc TBL_EEF44 1 L9).
    - constructor; try assumption;
        first [ eapply (ictxA_ffkeepM w m0 m9); [exact IC0 | exact FK9 | vm_compute; reflexivity]
              | eapply (ifrA_ffkeepM w m0 m9); [exact FR0 | exact FK9 | vm_compute; reflexivity]
              | (rewrite Eic; exact Hic)
              | (rewrite Een, Erq; exact Hend)
              | (unfold pi_macct in *; rewrite Em1, Em2, Em3; exact MAC)
              | (rewrite Ev3; apply Forall_app; split; [exact V3R | exact RG]) ].
    - apply incl_refl.
    - exact Q22.
    - exact Q25.
    - exists t. split; [exact Q18 | lia].
    - exact K114.
    - left; lia.
    - exists (c_widx c - i_io I), (mask_etA t). split; [exact K112 | exact K116].
    - exact MD9.
    - exact Ewidx.
    - exact Ev1.
    - exact Ev2.
    - unfold pi_nodes. rewrite Em1, Em2, Em3. lia.
    - exact Ev3.
    - exact SF.
    - exact HL.
    - right. exact Ht36.
    - exact Em2.
    - left; exact Em1.
    - left; exact Em3.
    - exact NR.
  Qed.

  Lemma mask_exitA : forall w I c t m0 F fc Q, MASKC w I c t m0 fc Q ->
    forall s1 LB1 LBs1 m1 mo1 c1 msF1 R1 L,
      PMXA H LINV w s1 LB1 LBs1 m1 mo1 c1 [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> as_AKREL H s1 (mkCfg msF1 mo1) ->
      as_VIS H s1 msF1 = MS R1 F (Z_to_bv 64 0xf18ac) fc None m1 (seg_rom asegs) -> rfull R1 ->
      regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
      PropExec.getr R1 22%bv = Z_to_bv 64 (i_op I) -> PropExec.getr R1 25%bv = Z_to_bv 64 (i_io I) ->
      PropExec.getr R1 18%bv = Z_to_bv 64 t ->
      MASKG (wa_n w) c c1 L -> Zlen L <= 96 ->
      ffkeepX w MASK_XS m0 m1 -> popndA H w m1 (c_widx c - i_io I) (mask_etA t) ->
      as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros w I c t m0 F fc Q MC s1 LB1 LBs1 m1 mo1 c1 msF1 R1 L X1 KR1 VIS1 RF1 HT1 G3_1 G4_1 Q22 Q25 Q18 SG HL FK1 PO1.
    pose proof MC as MC'. destruct MC' as [OK HIn Ht31 FZ0 IP IC0 FR0 Hic Hend Hw MAC V3R Hlen Hw1 Hw2 PK CK TRC TRR].
    pose proof SG as SG'. destruct SG' as [Htr1 Hbsz1 BUD1 _ _ _ _ _ _ _ _ _ _ _ _ _].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    assert (Ht32 : 0 <= t < 2 ^ 32) by (clear - Ht31; lia).
    assert (I1 : incl [(8512, 8)] MASK_XS) by (intros x Hx; clear - Hx; cbn in Hx |- *; tauto).
    assert (I2 : incl [(8544, 16)] MASK_XS) by (intros x Hx; clear - Hx; cbn in Hx |- *; tauto).
    destruct (ff_cell4_junkM w _ _ _ _ _ _ _ _ _ _ _ 176 X1 OK ltac:(clear; lia) ltac:(clear; lia)) as (xj & Hxj & Cj).
    destruct (Z.eq_dec xj 0) as [X0|XN].
    2: {
      eapply (pm_u5m_xnz H HHbp LINV LINV_frame w s1 LB1 LBs1 m1 mo1 c1 msF1 R1 F fc xj Q OK X1 Htr1 Hbsz1 KR1 VIS1 RF1 FZ0 HT1 G3_1 G4_1 Cj Hxj XN).
      intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 HT2 G3_2 G4_2 KX2 EM. subst m2.
      eapply (mask_pushk w I c t m0 F fc Q MC s1 LB1 LBs1 m1 mo2 c1 msF2 R2 L X2 KR2 VIS2 RF2 HT2 G3_2 G4_2);
        [ rewrite (KX2 22%bv ltac:(inlM)); exact Q22 | rewrite (KX2 25%bv ltac:(inlM)); exact Q25
        | rewrite (KX2 18%bv ltac:(inlM)); exact Q18 | exact SG | clear - HL; lia | exact FK1 | exact PO1 ]. }
    subst xj.

    eapply (pm_u5m_w0a H HHbp LINV LINV_frame w s1 LB1 LBs1 m1 mo1 c1 msF1 R1 F fc Q OK X1 Htr1 Hbsz1 KR1 VIS1 RF1 FZ0 HT1 G3_1 G4_1 Cj).
    intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 HT2 G3_2 G4_2 Gra2 G2_2 G10_2 G11_2 G12_2 CE2 FK2 KX2.
    rewrite Q18 in G10_2.
    assert (MD2 : mdef m2 (wa_ff w + 8512) 8) by (exact (mdef_of_rw_cells m2 _ _ CE2 ltac:(unfold AIMG_TOP, AFS_HDR in *; lia))).
    assert (G11' : PropExec.getr R2 11%bv = Z_to_bv 64 (sx32A 0)) by (exact G11_2).
    assert (H00 : 0 <= 0 < 2 ^ 32) by (clear; lia).
    assert (Hra2 : 0 <= 0xf1af8 < 2 ^ 64) by (clear; lia).
    eapply (pm_lookup H HHe5 LINV LINV_frame _ _ _ _ (tla_lookup_operand HTL) t 0 8512 w s1 LB1 LBs1 m2 mo2 c1 _ TBL_EEF44 [] [] 0
              msF2 R2 F fc 0xf1af8 Q [] OK X2 KR2 VIS2 RF2 G2_2 Gra2 eq_refl Hra2 G10_2 Ht32
              ltac:(intros Hn2; discriminate Hn2) ltac:(intros _; exact (conj G11' (conj H00 G12_2))) eq_refl);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | apply incl_refl | reflexivity | reflexivity | exact MD2 |].
    intros msF3 mo3 m3 R3 r KR3 VIS3 RF3 X3 KEEP3 MU3 WM3 Gr Hr Hiff Hfound Hmiss.
    assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (KEEP3 3%bv ltac:(inlM)); exact G3_2).
    assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (KEEP3 4%bv ltac:(inlM)); exact G4_2).
    pose proof (regs_keep w [] R2 R3 RT_ML HT2 KEEP3) as HT3. change (rt_keep RT_ML) with RT_ML in HT3.
    assert (FK3 : ffkeepX w [(8512, 8)] m2 m3).
    { apply (ffkeepX_munch w _ _ _ _ MU3 WM3). apply Forall_cons; [left; cbn [fst]; unfold TL_STACK; lia|].
      cbn [offs_wins map]. apply Forall_cons; [right; right; apply Exists_cons_hd; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (FK13 : ffkeepX w [(8512, 8)] m1 m3) by (exact (ffkeepX_trans w _ _ _ m1 m2 m3 FK2 FK3 (incl_refl _) (incl_refl _))).
    assert (FK03 : ffkeepX w MASK_XS m0 m3) by (exact (ffkeepX_trans w MASK_XS [(8512, 8)] MASK_XS m0 m1 m3 FK1 FK13 (incl_refl _) I1)).
    destruct (popndA_ffkeepM w m1 m3 _ _ _ OK PO1 FK13 ltac:(vm_compute; reflexivity)) as [PO3 _].
    assert (Q22_3 : PropExec.getr R3 22%bv = Z_to_bv 64 (i_op I))
      by (rewrite (KEEP3 22%bv ltac:(inlM)), (KX2 22%bv ltac:(inlM)); exact Q22).
    assert (Q25_3 : PropExec.getr R3 25%bv = Z_to_bv 64 (i_io I))
      by (rewrite (KEEP3 25%bv ltac:(inlM)), (KX2 25%bv ltac:(inlM)); exact Q25).
    assert (Q18_3 : PropExec.getr R3 18%bv = Z_to_bv 64 t)
      by (rewrite (KEEP3 18%bv ltac:(inlM)), (KX2 18%bv ltac:(inlM)); exact Q18).
    destruct (Z.eq_dec r 0) as [R0|RN0].
    2: {
      eapply (pm_u5m_w0n H HHbp LINV LINV_frame w s1 LB1 LBs1 m3 mo3 c1 msF3 R3 F fc r Q OK X3 Htr1 Hbsz1 KR3 VIS3 RF3 FZ0 HT3 G3_3 G4_3 Gr (conj RN0 Hr)).
      intros msF4 mo4 m4 R4 KR4 VIS4 RF4 X4 HT4 G3_4 G4_4 KX4 FK4.
      assert (FK04 : ffkeepX w MASK_XS m0 m4) by (exact (ffkeepX_trans w MASK_XS [] MASK_XS m0 m3 m4 FK03 FK4 (incl_refl _) (incl_nil_l _))).
      destruct (popndA_ffkeepM w m3 m4 _ _ _ OK PO3 FK4 ltac:(vm_compute; reflexivity)) as [PO4 _].
      eapply (mask_pushk w I c t m0 F fc Q MC s1 LB1 LBs1 m4 mo4 c1 msF4 R4 L X4 KR4 VIS4 RF4 HT4 G3_4 G4_4);
        [ rewrite (KX4 22%bv ltac:(inlM)); exact Q22_3 | rewrite (KX4 25%bv ltac:(inlM)); exact Q25_3
        | rewrite (KX4 18%bv ltac:(inlM)); exact Q18_3 | exact SG | clear - HL; lia | exact FK04 | exact PO4 ]. }

    destruct (Hfound R0) as (d & CDd & HOD).
    assert (HTf : regs_tbl w R3 RT_MLF).
    { unfold RT_MLF. apply regs_tbl_snoc_lit; [exact HT3 | rewrite Gr, R0; reflexivity]. }
    eapply (pm_u5m_w0f H HHbp LINV LINV_frame HTL w s1 LB1 LBs1 m3 mo3 c1 msF3 R3 F fc d t Q OK X3 Htr1 Hbsz1 KR3 VIS3 RF3 FZ0 HTf G3_3 G4_3 CDd HOD).
    intros msF7 mo7 m7 R7 sp_p ll KR7 VIS7 RF7 X7 HT7 G3_7 G4_7 Gra7 G2_7 G10_7 G11_7 CS7 GX SPN FK7 KX7.
    pose proof (tg_mask_len t 0 ll (mask_in_tabl t HIn) GX) as LL.
    pose proof TG_ok as GOK.
    assert (LR : Forall (fun t => 0 <= t < 2 ^ 31) ll).
    { apply Forall_forall. intros x Hx. eapply (go_range _ GOK ll x); [right; left; exists t, 0; exact GX | exact Hx]. }
    assert (Hra7 : 0 <= 0xf1b34 < 2 ^ 64) by (clear; lia).
    assert (LL48 : Zlen ll <= 48) by (clear - LL; lia).
    eapply (pm_push_types H HHbp LINV LINV_cl LINV_relro HOWN HPT w s1 LB1 LBs1 m7 mo7 c1 _ TBL_EEF44 [] [] 0 msF7 R7 F fc 0xf1b34 8544 sp_p ll Q
              OK X7 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) KR7 VIS7 RF7 Gra7 eq_refl Hra7 G2_7 G4_7 G10_7 G11_7
              ltac:(vm_compute; reflexivity) ltac:(clear; lia) ltac:(clear; lia) eq_refl CS7 SPN LL48 LR
              (mask_budm w I c t m0 fc Q c1 L ll MC SG HL LL) TRC TRR).
    intros msF8 mo8 m8 R8 s8 LB8 LBs8 b8 cap8 KR8 VIS8 RF8 X8 KEEP8 BUD8 CAPR8 GROW8 CELLS8.
    destruct (msg_push (wa_n w) c c1 L b8 cap8 ll t 0 SG GX BUD8) as (l2 & Ll2 & SG8).
    set (c8 := set_v3A c1 (b8, push_types ll (t3b (c_v3 c1)), cap8)) in *.
    pose proof SG8 as SG8'. destruct SG8' as [Htr8 Hbsz8 _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (rewrite (KEEP8 3%bv ltac:(inlM)); exact G3_7).
    assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (rewrite (KEEP8 4%bv ltac:(inlM)); exact G4_7).
    pose proof (regs_keepK w [] R7 R8 RT_ML V4_KEPT HT7 KEEP8) as HT8.
    replace (rt_keepK V4_KEPT RT_ML) with RT_ML in HT8 by (vm_compute; reflexivity).
    assert (FK8 : ffkeepX w [] m7 m8) by (intros k0 cs Hk0 Hkn0 _ C; exact (CELLS8 k0 cs Hk0 Hkn0 C)).
    eapply (pm_u5m_w0t H HHbp LINV LINV_frame w s8 LB8 LBs8 m8 mo8 c8 msF8 R8 F fc Q OK X8 Htr8 Hbsz8 KR8 VIS8 RF8 FZ0 HT8 G3_8 G4_8).
    intros msF9 mo9 m9 R9 KR9 VIS9 RF9 X9 HT9 G3_9 G4_9 KX9 FK9.
    assert (FK39 : ffkeepX w [(8544, 16)] m3 m9).
    { apply (ffkeepX_trans w [(8544, 16)] [] _ m3 m7 m9 FK7); [| intros x Hx; exact Hx | apply incl_nil_l].
      exact (ffkeepX_trans w _ _ _ m7 m8 m9 FK8 FK9 (incl_nil_l _) (incl_nil_l _)). }
    assert (FK09 : ffkeepX w MASK_XS m0 m9) by (exact (ffkeepX_trans w MASK_XS [(8544, 16)] MASK_XS m0 m3 m9 FK03 FK39 (incl_refl _) I2)).
    destruct (popndA_ffkeepM w m3 m9 _ _ _ OK PO3 FK39 ltac:(vm_compute; reflexivity)) as [PO9 _].
    eapply (mask_pushk w I c t m0 F fc Q MC s8 LB8 LBs8 m9 mo9 c8 msF9 R9 (L ++ l2) X9 KR9 VIS9 RF9 HT9 G3_9 G4_9);
      [ rewrite (KX9 22%bv ltac:(inlM)), (KEEP8 22%bv ltac:(inlM)), (KX7 22%bv ltac:(inlM)); exact Q22_3
      | rewrite (KX9 25%bv ltac:(inlM)), (KEEP8 25%bv ltac:(inlM)), (KX7 25%bv ltac:(inlM)); exact Q25_3
      | rewrite (KX9 18%bv ltac:(inlM)), (KEEP8 18%bv ltac:(inlM)), (KX7 18%bv ltac:(inlM)); exact Q18_3
      | exact SG8 | rewrite PmZw.Zlen_app; clear - HL Ll2 LL; lia | exact FK09 | exact PO9 ].
  Qed.

  Lemma mask_loopA : forall w I c t m0 F fc Q (word : Z), MASKC w I c t m0 fc Q -> 0 <= word < 2 ^ 32 ->
    forall (k : nat) s1 LB1 LBs1 m1 mo1 c1 msF1 R1 L,
      Z.of_nat k <= 31 ->
      PMXA H LINV w s1 LB1 LBs1 m1 mo1 c1 [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> as_AKREL H s1 (mkCfg msF1 mo1) ->
      as_VIS H s1 msF1 = MS R1 F (Z_to_bv 64 0xf186c) fc None m1 (seg_rom asegs) -> rfull R1 ->
      regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
      PropExec.getr R1 22%bv = Z_to_bv 64 (i_op I) -> PropExec.getr R1 25%bv = Z_to_bv 64 (i_io I) ->
      PropExec.getr R1 18%bv = Z_to_bv 64 t ->
      PropExec.getr R1 23%bv = Z_to_bv 64 (sx32A (2 ^ Z.of_nat k)) ->
      PropExec.getr R1 21%bv = Z_to_bv 64 (sx32A (word mod 2 ^ (Z.of_nat k + 1))) ->
      word mod 2 ^ (Z.of_nat k + 1) <> 0 ->
      MASKG (wa_n w) c c1 L -> Zlen L <= 3 * (31 - Z.of_nat k) ->
      ffkeepX w MASK_XS m0 m1 -> popndA H w m1 (c_widx c - i_io I) (mask_etA t) ->
      as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros w I c t m0 F fc Q word MC Hword k.
    pose proof MC as MC'. destruct MC' as [OK HIn Ht31 FZ0 IP IC0 FR0 Hic Hend Hw MAC V3R Hlen Hw1 Hw2 PK CK TRC TRR].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    assert (Ht32 : 0 <= t < 2 ^ 32) by (clear - Ht31; lia).
    pose proof (mask_etA_range t Ht31) as HET.
    assert (I1 : incl [(7984, 8)] MASK_XS) by (intros x Hx; clear - Hx; cbn in Hx |- *; tauto).
    assert (I2 : incl [(8480, 16)] MASK_XS) by (intros x Hx; clear - Hx; cbn in Hx |- *; tauto).
    pose proof TG_ok as GOK.
    induction k as [kk IH] using (well_founded_induction Wf_nat.lt_wf).
    intros s1 LB1 LBs1 m1 mo1 c1 msF1 R1 L Hk X1 KR1 VIS1 RF1 HT1 G3_1 G4_1 Q22 Q25 Q18 Q23 Q21 Hrem SG HL FK1 PO1.
    remember (Z.of_nat kk) as j eqn:Ej in *.
    assert (Hj : 0 <= j <= 31) by (clear - Ej Hk; lia).
    pose proof (pow2_range32A j Hj) as Hpj.
    destruct (mask_rem_range word j Hj) as [Hremr Hlowr].
    destruct (mask_rem_step word j ltac:(clear - Hword; lia) ltac:(clear - Hj; lia)) as [STEP0 STEP1].
    pose proof (mask_rem_bit word j ltac:(clear - Hj; lia)) as Hbit.
    pose proof SG as SG'. destruct SG' as [Htr1 Hbsz1 BUD1 _ _ _ _ _ _ _ _ _ _ _ _ _].

    assert (TAIL : forall s2 LB2 LBs2 m2 mo2 c2 msF2 R2 L2,
      PMXA H LINV w s2 LB2 LBs2 m2 mo2 c2 [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> as_AKREL H s2 (mkCfg msF2 mo2) ->
      as_VIS H s2 msF2 = MS R2 F (Z_to_bv 64 0xf1864) fc None m2 (seg_rom asegs) -> rfull R2 ->
      regs_tbl w R2 RT_ML -> PropExec.getr R2 3%bv = wa_gp w -> PropExec.getr R2 4%bv = wa_tp w ->
      PropExec.getr R2 22%bv = Z_to_bv 64 (i_op I) -> PropExec.getr R2 25%bv = Z_to_bv 64 (i_io I) ->
      PropExec.getr R2 18%bv = Z_to_bv 64 t ->
      PropExec.getr R2 23%bv = Z_to_bv 64 (sx32A (2 ^ j)) ->
      PropExec.getr R2 21%bv = Z_to_bv 64 (sx32A (word mod 2 ^ j)) ->
      MASKG (wa_n w) c c2 L2 -> Zlen L2 <= 3 * (32 - j) ->
      ffkeepX w MASK_XS m0 m2 -> popndA H w m2 (c_widx c - i_io I) (mask_etA t) ->
      as_SR H Q (mkCfg msF2 mo2)).
    { intros s2 LB2 LBs2 m2 mo2 c2 msF2 R2 L2 X2 KR2 VIS2 RF2 HT2 G3_2 G4_2 Q22b Q25b Q18b Q23b Q21b SG2 HL2 FK2 PO2.
      pose proof SG2 as SG2'. destruct SG2' as [Htr2 Hbsz2 _ _ _ _ _ _ _ _ _ _ _ _ _ _].
      destruct (Z.eq_dec (word mod 2 ^ j) 0) as [Z0|ZN].
      -
        assert (HTz : regs_tbl w R2 RT_MLZ).
        { unfold RT_MLZ. apply regs_tbl_snoc_lit; [exact HT2 | rewrite Q21b, Z0; reflexivity]. }
        eapply (pm_u5m_lte H HHbp LINV LINV_frame w s2 LB2 LBs2 m2 mo2 c2 msF2 R2 F fc Q OK X2 Htr2 Hbsz2 KR2 VIS2 RF2 FZ0 HTz G3_2 G4_2).
        intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 EM KX3. subst m3.
        eapply (mask_exitA w I c t m0 F fc Q MC s2 LB2 LBs2 m2 mo3 c2 msF3 R3 L2 X3 KR3 VIS3 RF3 HT3 G3_3 G4_3);
          [ rewrite (KX3 22%bv ltac:(inlM)); exact Q22b | rewrite (KX3 25%bv ltac:(inlM)); exact Q25b
          | rewrite (KX3 18%bv ltac:(inlM)); exact Q18b | exact SG2 | clear - HL2 Hj; lia | exact FK2 | exact PO2 ].
      -
        assert (Hj1 : 1 <= j).
        { destruct (Z.eq_dec j 0) as [E0|NE0]; [| clear - NE0 Hj; lia]. exfalso. apply ZN. rewrite E0. apply mask_rem0. }
        eapply (pm_u5m_ltm H HHbp LINV LINV_frame w s2 LB2 LBs2 m2 mo2 c2 msF2 R2 F fc j (word mod 2 ^ j) Q OK X2 Htr2 Hbsz2 KR2 VIS2 RF2 FZ0 HT2 G3_2 G4_2
                  Q23b Q21b Hj Hlowr Hj1 ZN).
        intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 G23_3 G21_3 EM KX3. subst m3.
        destruct kk as [|kk']; [exfalso; clear - Ej Hj1; cbn in Ej; lia|].
        assert (EJ : Z.of_nat kk' = j - 1) by (clear - Ej; lia).
        apply (IH kk' ltac:(clear; lia) s2 LB2 LBs2 m2 mo3 c2 msF3 R3 L2 ltac:(clear - EJ Hj; lia) X3 KR3 VIS3 RF3 HT3 G3_3 G4_3).
        + rewrite (KX3 22%bv ltac:(inlM)); exact Q22b.
        + rewrite (KX3 25%bv ltac:(inlM)); exact Q25b.
        + rewrite (KX3 18%bv ltac:(inlM)); exact Q18b.
        + rewrite EJ. exact G23_3.
        + rewrite EJ. replace (j - 1 + 1) with j by (clear; lia). rewrite G21_3. exact Q21b.
        + rewrite EJ. replace (j - 1 + 1) with j by (clear; lia). exact ZN.
        + exact SG2.
        + rewrite EJ. clear - HL2. lia.
        + exact FK2.
        + exact PO2. }
    assert (TBD : Z.testbit word j = true \/ Z.testbit word j = false) by (destruct (Z.testbit word j); [left | right]; reflexivity).
    destruct TBD as [TB|TB].
    2: {
      pose proof (STEP0 TB) as Erem.
      assert (TBr : Z.testbit (word mod 2 ^ (j + 1)) j = false) by (rewrite Hbit; exact TB).
      eapply (pm_u5m_lhc H HHbp LINV LINV_frame w s1 LB1 LBs1 m1 mo1 c1 msF1 R1 F fc j (word mod 2 ^ (j + 1)) Q OK X1 Htr1 Hbsz1 KR1 VIS1 RF1 FZ0 HT1 G3_1 G4_1
                Q23 Q21 Hj Hremr TBr).
      intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 HT2 G3_2 G4_2 G23_2 G21_2 EM KX2. subst m2.
      apply (TAIL s1 LB1 LBs1 m1 mo2 c1 msF2 R2 L X2 KR2 VIS2 RF2 HT2 G3_2 G4_2).
      + rewrite (KX2 22%bv ltac:(inlM)); exact Q22.
      + rewrite (KX2 25%bv ltac:(inlM)); exact Q25.
      + rewrite (KX2 18%bv ltac:(inlM)); exact Q18.
      + rewrite G23_2. exact Q23.
      + rewrite G21_2, Q21, Erem. reflexivity.
      + exact SG.
      + clear - HL. lia.
      + exact FK1.
      + exact PO1. }

    pose proof (STEP1 TB) as Erem.
    assert (TBr : Z.testbit (word mod 2 ^ (j + 1)) j = true) by (rewrite Hbit; exact TB).
    eapply (pm_u5m_lhs H HHbp LINV LINV_frame w s1 LB1 LBs1 m1 mo1 c1 msF1 R1 F fc j (word mod 2 ^ (j + 1)) Q OK X1 Htr1 Hbsz1 KR1 VIS1 RF1 FZ0 HT1 G3_1 G4_1
              Q23 Q21 Hj Hremr TBr).
    intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 HT2 G3_2 G4_2 Gra2 G2_2 G10_2 G11_2 G12_2 G23_2 G21_2 CE2 FK2 KX2.
    rewrite Q18 in G10_2. rewrite Q23 in G11_2, G23_2. rewrite Q21 in G21_2.
    assert (MD2 : mdef m2 (wa_ff w + 7984) 8) by (exact (mdef_of_rw_cells m2 _ _ CE2 ltac:(unfold AIMG_TOP, AFS_HDR in *; lia))).
    assert (Hpj32 : 0 <= 2 ^ j < 2 ^ 32) by (clear - Hpj; lia).
    assert (Hra2 : 0 <= 0xf188c < 2 ^ 64) by (clear; lia).
    eapply (pm_lookup H HHe5 LINV LINV_frame _ _ _ _ (tla_lookup_operand HTL) t (2 ^ j) 7984 w s1 LB1 LBs1 m2 mo2 c1 _ TBL_EEF44 [] [] 0
              msF2 R2 F fc 0xf188c Q [] OK X2 KR2 VIS2 RF2 G2_2 Gra2 eq_refl Hra2 G10_2 Ht32
              ltac:(intros Hn2; discriminate Hn2) ltac:(intros _; exact (conj G11_2 (conj Hpj32 G12_2))) eq_refl);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | apply incl_refl | reflexivity | reflexivity | exact MD2 |].
    intros msF3 mo3 m3 R3 r KR3 VIS3 RF3 X3 KEEP3 MU3 WM3 Gr Hr Hiff Hfound Hmiss.
    assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (KEEP3 3%bv ltac:(inlM)); exact G3_2).
    assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (KEEP3 4%bv ltac:(inlM)); exact G4_2).
    pose proof (regs_keep w [] R2 R3 RT_ML HT2 KEEP3) as HT3. change (rt_keep RT_ML) with RT_ML in HT3.
    assert (FK3 : ffkeepX w [(7984, 8)] m2 m3).
    { apply (ffkeepX_munch w _ _ _ _ MU3 WM3). apply Forall_cons; [left; cbn [fst]; unfold TL_STACK; lia|].
      cbn [offs_wins map]. apply Forall_cons; [right; right; apply Exists_cons_hd; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (FK13 : ffkeepX w [(7984, 8)] m1 m3) by (exact (ffkeepX_trans w _ _ _ m1 m2 m3 FK2 FK3 (incl_refl _) (incl_refl _))).
    assert (FK03 : ffkeepX w MASK_XS m0 m3) by (exact (ffkeepX_trans w MASK_XS [(7984, 8)] MASK_XS m0 m1 m3 FK1 FK13 (incl_refl _) I1)).
    destruct (popndA_ffkeepM w m1 m3 _ _ _ OK PO1 FK13 ltac:(vm_compute; reflexivity)) as [PO3 _].
    assert (Q22_3 : PropExec.getr R3 22%bv = Z_to_bv 64 (i_op I))
      by (rewrite (KEEP3 22%bv ltac:(inlM)), (KX2 22%bv ltac:(inlM)); exact Q22).
    assert (Q25_3 : PropExec.getr R3 25%bv = Z_to_bv 64 (i_io I))
      by (rewrite (KEEP3 25%bv ltac:(inlM)), (KX2 25%bv ltac:(inlM)); exact Q25).
    assert (Q18_3 : PropExec.getr R3 18%bv = Z_to_bv 64 t)
      by (rewrite (KEEP3 18%bv ltac:(inlM)), (KX2 18%bv ltac:(inlM)); exact Q18).
    assert (G23_3 : PropExec.getr R3 23%bv = Z_to_bv 64 (sx32A (2 ^ j))) by (rewrite (KEEP3 23%bv ltac:(inlM)); exact G23_2).
    assert (G21_3 : PropExec.getr R3 21%bv = Z_to_bv 64 (sx32A (word mod 2 ^ (j + 1)))) by (rewrite (KEEP3 21%bv ltac:(inlM)); exact G21_2).
    destruct (Z.eq_dec r 0) as [R0|RN0].
    2: {
      destruct PO3 as (_ & _ & C116 & _).
      exact (pm_u5m_d H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 HU32 HTL LINV_relro w s1 LB1 LBs1 m3 mo3 c1 msF3 R3 F fc r (mask_etA t) j Q
               OK X3 Htr1 Hbsz1 KR3 VIS3 RF3 FZ0 HT3 G3_3 G4_3 Gr (conj RN0 Hr) G23_3 Hj C116 HET BUD1 CK). }

    destruct (Hfound R0) as (d & CDd & HOD).
    assert (HTf : regs_tbl w R3 RT_MLF).
    { unfold RT_MLF. apply regs_tbl_snoc_lit; [exact HT3 | rewrite Gr, R0; reflexivity]. }
    eapply (pm_u5m_lf H HHbp LINV LINV_frame HTL w s1 LB1 LBs1 m3 mo3 c1 msF3 R3 F fc d t j (word mod 2 ^ (j + 1)) Q OK X3 Htr1 Hbsz1 KR3 VIS3 RF3 FZ0 HTf G3_3 G4_3
              CDd HOD G23_3 G21_3 Hj Hremr TBr).
    intros msF7 mo7 m7 R7 sp_p ll KR7 VIS7 RF7 X7 HT7 G3_7 G4_7 Gra7 G2_7 G10_7 G11_7 CS7 GX SPN FK7 G23_7 G21_7 KX7.
    rewrite G23_3 in G23_7. rewrite Erem in G21_7.
    pose proof (tg_mask_len t (2 ^ j) ll (mask_in_tabl t HIn) GX) as LL.
    assert (LR : Forall (fun t => 0 <= t < 2 ^ 31) ll).
    { apply Forall_forall. intros x Hx. eapply (go_range _ GOK ll x); [right; left; exists t, (2 ^ j); exact GX | exact Hx]. }
    assert (Hra7 : 0 <= 0xf1858 < 2 ^ 64) by (clear; lia).
    assert (LL48 : Zlen ll <= 48) by (clear - LL; lia).
    assert (HL96 : Zlen L <= 96) by (clear - HL Hj; lia).
    eapply (pm_push_types H HHbp LINV LINV_cl LINV_relro HOWN HPT w s1 LB1 LBs1 m7 mo7 c1 _ TBL_EEF44 [] [] 0 msF7 R7 F fc 0xf1858 8480 sp_p ll Q
              OK X7 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) KR7 VIS7 RF7 Gra7 eq_refl Hra7 G2_7 G4_7 G10_7 G11_7
              ltac:(vm_compute; reflexivity) ltac:(clear; lia) ltac:(clear; lia) eq_refl CS7 SPN LL48 LR
              (mask_budm w I c t m0 fc Q c1 L ll MC SG HL96 LL) TRC TRR).
    intros msF8 mo8 m8 R8 s8 LB8 LBs8 b8 cap8 KR8 VIS8 RF8 X8 KEEP8 BUD8 CAPR8 GROW8 CELLS8.
    destruct (msg_push (wa_n w) c c1 L b8 cap8 ll t (2 ^ j) SG GX BUD8) as (l2 & Ll2 & SG8).
    set (c8 := set_v3A c1 (b8, push_types ll (t3b (c_v3 c1)), cap8)) in *.
    pose proof SG8 as SG8'. destruct SG8' as [Htr8 Hbsz8 _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (rewrite (KEEP8 3%bv ltac:(inlM)); exact G3_7).
    assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (rewrite (KEEP8 4%bv ltac:(inlM)); exact G4_7).
    pose proof (regs_keepK w [] R7 R8 RT_ML V4_KEPT HT7 KEEP8) as HT8.
    replace (rt_keepK V4_KEPT RT_ML) with RT_ML in HT8 by (vm_compute; reflexivity).
    assert (FK8 : ffkeepX w [] m7 m8) by (intros k0 cs Hk0 Hkn0 _ C; exact (CELLS8 k0 cs Hk0 Hkn0 C)).
    eapply (pm_u5m_lr H HHbp LINV LINV_frame w s8 LB8 LBs8 m8 mo8 c8 msF8 R8 F fc Q OK X8 Htr8 Hbsz8 KR8 VIS8 RF8 FZ0 HT8 G3_8 G4_8).
    intros msF9 mo9 m9 R9 KR9 VIS9 RF9 X9 HT9 G3_9 G4_9 G23_9 G21_9 FK9 KX9.
    assert (FK39 : ffkeepX w [(8480, 16)] m3 m9).
    { apply (ffkeepX_trans w [(8480, 16)] [] _ m3 m7 m9 FK7); [| intros x Hx; exact Hx | apply incl_nil_l].
      exact (ffkeepX_trans w _ _ _ m7 m8 m9 FK8 FK9 (incl_nil_l _) (incl_nil_l _)). }
    assert (FK09 : ffkeepX w MASK_XS m0 m9) by (exact (ffkeepX_trans w MASK_XS [(8480, 16)] MASK_XS m0 m3 m9 FK03 FK39 (incl_refl _) I2)).
    destruct (popndA_ffkeepM w m3 m9 _ _ _ OK PO3 FK39 ltac:(vm_compute; reflexivity)) as [PO9 _].
    apply (TAIL s8 LB8 LBs8 m9 mo9 c8 msF9 R9 (L ++ l2) X9 KR9 VIS9 RF9 HT9 G3_9 G4_9).
    + rewrite (KX9 22%bv ltac:(inlM)), (KEEP8 22%bv ltac:(inlM)), (KX7 22%bv ltac:(inlM)); exact Q22_3.
    + rewrite (KX9 25%bv ltac:(inlM)), (KEEP8 25%bv ltac:(inlM)), (KX7 25%bv ltac:(inlM)); exact Q25_3.
    + rewrite (KX9 18%bv ltac:(inlM)), (KEEP8 18%bv ltac:(inlM)), (KX7 18%bv ltac:(inlM)); exact Q18_3.
    + rewrite G23_9, (KEEP8 23%bv ltac:(inlM)). exact G23_7.
    + rewrite G21_9, (KEEP8 21%bv ltac:(inlM)). exact G21_7.
    + exact SG8.
    + rewrite PmZw.Zlen_app. clear - HL Ll2 LL. lia.
    + exact FK09.
    + exact PO9.
  Qed.

  Theorem arm_MASK_A : forall t, In t PmHyps.MASK_TYPES -> arm_stmtA H LINV t 0xf14cc.
  Proof.
    intros t HIn w s LB LBs m mo c msF R F fc I tbl wv Q OK HAE IT TC TK TN PK CK AACC.
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q22 & Q25 & Q18 & Q21 & PO & C176).
    destruct OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP IC FR Hic Hend Hw MAC V3R].
    pose proof (pmxa_restrictM w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X0 IT (incl_refl _)) as X0r.
    pose proof (wk_tr H w OK) as TR. unfold pm_tr_ok, PM_DEL_RAS in TR.
    assert (TRR : trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF]) by exact (proj1 (Forall_forall _ _) TR (v4_del_ra VOT_SLOW_RREF) ltac:(inlM)).
    assert (TRC : trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF]) by exact (proj1 (Forall_forall _ _) TR (v4_del_ra VOT_SLOW_CREF) ltac:(inlM)).
    pose proof PO as PO'. destruct PO' as (_ & _ & C116 & _).
    assert (MC : MASKC w I c t m fc Q).
    { constructor; assumption. }
    pose proof (msg_init (wa_n w) c Htr Hbsz BUD) as SG0.

    assert (KONT : forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) ->
      as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 ->
      PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML ->
      PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv ->
      rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 (mask_etA t))] -> ffkeepX w [(116, 4)] m m1 ->
      (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) ->
      as_SR H Q (mkCfg msF1 mo1)).
    { intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 G21_1 CT1 FK1 KX1.
      pose proof (popndA_set_typeM w m m1 _ _ _ PO FK1 CT1) as PO1.
      assert (FK01 : ffkeepX w MASK_XS m m1).
      { apply (ffkeepX_mono w [(116, 4)] MASK_XS m m1 FK1). intros x Hx; clear - Hx; cbn in Hx |- *; tauto. }
      rewrite Q21 in G21_1.
      assert (Q22_1 : PropExec.getr R1 22%bv = Z_to_bv 64 (i_op I)) by (rewrite (KX1 22%bv ltac:(inlM)); exact Q22).
      assert (Q25_1 : PropExec.getr R1 25%bv = Z_to_bv 64 (i_io I)) by (rewrite (KX1 25%bv ltac:(inlM)); exact Q25).
      assert (Q18_1 : PropExec.getr R1 18%bv = Z_to_bv 64 t) by (rewrite (KX1 18%bv ltac:(inlM)); exact Q18).
      destruct (Z.eq_dec wv 0) as [W0|WN].
      -
        assert (HTz : regs_tbl w R1 RT_MLZ).
        { unfold RT_MLZ. apply regs_tbl_snoc_lit; [exact HT1 | rewrite G21_1, W0; reflexivity]. }
        eapply (pm_u5m_l0z H HHbp LINV LINV_frame w s LB LBs m1 mo1 c msF1 R1 F fc Q OK X1 Htr Hbsz KR1 VIS1 RF1 FZ0 HTz G3_1 G4_1).
        intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 HT2 G3_2 G4_2 EM KX2. subst m2.
        eapply (mask_exitA w I c t m F fc Q MC s LB LBs m1 mo2 c msF2 R2 [] X2 KR2 VIS2 RF2 HT2 G3_2 G4_2);
          [ rewrite (KX2 22%bv ltac:(inlM)); exact Q22_1 | rewrite (KX2 25%bv ltac:(inlM)); exact Q25_1
          | rewrite (KX2 18%bv ltac:(inlM)); exact Q18_1 | exact SG0 | rewrite PmZw.Zlen_nil; clear; lia | exact FK01 | exact PO1 ].
      -
        assert (Hwv : 0 < wv < 2 ^ 32) by (clear - Hword WN; lia).
        eapply (pm_u5m_l0 H HHbp LINV LINV_frame w s LB LBs m1 mo1 c msF1 R1 F fc wv Q OK X1 Htr Hbsz KR1 VIS1 RF1 FZ0 HT1 G3_1 G4_1 G21_1 Hwv).
        intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 HT2 G3_2 G4_2 G23_2 G21_2 EM KX2. subst m2.
        assert (E32 : wv mod 2 ^ (Z.of_nat 31 + 1) = wv).
        { change (Z.of_nat 31 + 1) with 32. apply Z.mod_small. clear - Hword. lia. }
        eapply (mask_loopA w I c t m F fc Q wv MC Hword 31%nat s LB LBs m1 mo2 c msF2 R2 [] ltac:(cbn; clear; lia)
                  X2 KR2 VIS2 RF2 HT2 G3_2 G4_2).
        + rewrite (KX2 22%bv ltac:(inlM)); exact Q22_1.
        + rewrite (KX2 25%bv ltac:(inlM)); exact Q25_1.
        + rewrite (KX2 18%bv ltac:(inlM)); exact Q18_1.
        + rewrite G23_2. change (Z.of_nat 31) with 31. exact mask_lui31.
        + rewrite E32, G21_2. exact G21_1.
        + rewrite E32. exact WN.
        + exact SG0.
        + rewrite PmZw.Zlen_nil. cbn. clear. lia.
        + exact FK01.
        + exact PO1. }

    assert (HTt : forall z, t = z -> regs_tbl w R (RT_M0 z)).
    { intros z <-. unfold RT_M0. apply regs_tbl_snoc_lit; [exact HT0 | exact Q18]. }
    unfold PmHyps.MASK_TYPES in HIn. cbn [In] in HIn.
    destruct HIn as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]]]]]]];
      pose proof (HTt _ (eq_sym E)) as HTz; subst t;
      lazymatch type of KONT with context [mask_etA ?z] => let v := eval vm_compute in (mask_etA z) in change (mask_etA z) with v in KONT end.
    - exact (pm_u5m_1_35 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 C116 KONT).
    - exact (pm_u5m_1_36 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 C116 KONT).
    - exact (pm_u5m_1_37 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 C116 KONT).
    - exact (pm_u5m_1_38 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 C116 KONT).
    - exact (pm_u5m_1_39 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 C116 KONT).
    - exact (pm_u5m_1_40 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 C116 KONT).
    - exact (pm_u5m_1_43 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 KONT).
    - exact (pm_u5m_1_44 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 KONT).
    - exact (pm_u5m_1_56 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 C116 KONT).
    - exact (pm_u5m_1_61 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 C116 KONT).
    - exact (pm_u5m_1_77 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 C116 KONT).
    - exact (pm_u5m_1_78 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 KONT).
    - exact (pm_u5m_1_87 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 KONT).
    - exact (pm_u5m_1_89 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 C116 KONT).
    - exact (pm_u5m_1_90 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 C116 KONT).
    - exact (pm_u5m_1_91 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 C116 KONT).
    - exact (pm_u5m_1_92 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 KONT).
    - exact (pm_u5m_1_103 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 C116 KONT).
    - exact (pm_u5m_1_104 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 KONT).
  Qed.
End U5M.
