From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_FKit LbB_Own LbB_PmBase LbB_Call LbB_Bridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_SR LbB_WoGen LbB_WoDefs LbB_WoKit LbB_PiStmt LbB_PiInit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRepFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BllocRep BG_Free6.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoBP LbB_PmExit.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition bp_phc (st : stateC) (words n : Z) : Prop :=
  st_words st = words /\ st_nwords st = n /\
  st_m1 st = (0, 0, []) /\ st_m2 st = (0, 0, []) /\ st_m3 st = (0, 0, []) /\
  t3a (st_v1 st) = t3b (st_v1 st) /\ t3a (st_v2 st) = t3b (st_v2 st) /\ t3a (st_v3 st) = t3b (st_v3 st) /\
  t3a (st_v1 st) <> 0 /\ t3a (st_v2 st) <> 0 /\ t3a (st_v3 st) <> 0 /\
  t3c (st_v1 st) = t3a (st_v1 st) + 500 /\ t3c (st_v2 st) = t3a (st_v2 st) + 100 /\ t3c (st_v3 st) = t3a (st_v3 st) + 100.

Lemma bp_phc_ste : forall st words n e, pi_hdr (bp_ste st 0) words n e -> bp_phc st words n.
Proof.
  intros st words n e (Hw & Hn & _ & _ & _ & _ & _ & Hm1 & Hm2 & Hm3 & E1 & E2 & E3 & N1 & N2 & N3 & C1 & C2 & C3).
  cbn [bp_ste st_words st_nwords st_m1 st_m2 st_m3 st_v1 st_v2 st_v3] in *.
  unfold bp_phc. repeat split; assumption.
Qed.

Lemma bp_phc_st5 : forall st words n e, pi_hdr (bp_st5 st) words n e -> bp_phc st words n.
Proof.
  intros st words n e (Hw & Hn & _ & _ & _ & _ & _ & Hm1 & Hm2 & Hm3 & E1 & E2 & E3 & N1 & N2 & N3 & C1 & C2 & C3).
  cbn [bp_st5 st_words st_nwords st_m1 st_m2 st_m3 st_v1 st_v2 st_v3] in *.
  unfold bp_phc. repeat split; assumption.
Qed.

Lemma bp_phc_blocks : forall st words n, bp_phc st words n ->
  state_blocks st = [(t3a (st_v1 st), 500); (t3a (st_v2 st), 100); (t3a (st_v3 st), 100)].
Proof.
  intros [w0 n0 d0 wi ic en fl m1 m2 m3 [[b1 e1] c1] [[b2 e2] c2] [[b3 e3] c3]] words n
         (_ & _ & Hm1 & Hm2 & Hm3 & E1 & E2 & E3 & N1 & N2 & N3 & C1 & C2 & C3).
  cbn [st_m1 st_m2 st_m3 st_v1 st_v2 st_v3 t3a t3b t3c fst snd] in *. subst m1 m2 m3 c1 c2 c3.
  unfold state_blocks, vec_blocks, umap_blocks.
  cbn [st_m1 st_m2 st_m3 st_v1 st_v2 st_v3 t3a t3b t3c fst snd Z.eqb map app].
  destruct (Z.eqb_spec b1 0); [contradiction|]. destruct (Z.eqb_spec b2 0); [contradiction|].
  destruct (Z.eqb_spec b3 0); [contradiction|].
  cbn [app]. repeat f_equal; lia.
Qed.

Lemma bp_phc_vsteps : forall st words n, bp_phc st words n -> st_vsteps st.
Proof.
  intros st words n (_ & _ & _ & _ & _ & E1 & E2 & E3 & _).
  unfold st_vsteps. split; [|split]; exists 0; split; lia.
Qed.

Definition bp_pfoot (p : Z) (c : parserC) (a : Z) : Prop :=
  parser_foot p c a \/ (pc_cons c + 32 <= a < pc_cons c + 40)
  \/ (sh p <= a < sh p + nsh PARSER_SIZE) \/ (sh (pc_cons c) <= a < sh (pc_cons c) + nsh 48)
  \/ (exists b, In b (state_blocks (pc_state c)) /\ sh (fst b) <= a < sh (fst b) + nsh (snd b)).

Lemma state_rep_moveA : forall LB LB' m m' st c,
  @state_rep AC_A ASEGS LY_A MI_A (lbl LB) m st c -> 0 < st -> st + 240 <= 2 ^ 47 ->
  (forall a, state_foot st c a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (forall b, In b (state_blocks c) -> In b (lbl LB')) ->
  @state_rep AC_A ASEGS LY_A MI_A (lbl LB') m' st c.
Proof.
  intros LB LB' m m' st c SR Hlo Hhi HM HL.
  pose proof (state_rep_keepA LB m m' st c SR Hlo Hhi HM) as SR'.
  destruct SR' as [W0 W1 W2 W3 W4 W5 W6 Sm1 Sm2 Sm3 Sv1 Sv2 Sv3 Sdef Sal Snd].
  unfold state_blocks in HL.
  constructor; try assumption.
  - eapply (umapx_agree ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (nval24_agree ASEGS) ltac:(lia));
      [exact Sm1 | intros a _; reflexivity | intros p n Hp _; apply HL; rewrite !in_app_iff; tauto].
  - eapply (umapx_agree ASEGS LY_A MI_A 32 (Z * Z * Z)%type (nval32 ASEGS) (nval32_agree ASEGS) ltac:(lia));
      [exact Sm2 | intros a _; reflexivity | intros p n Hp _; apply HL; rewrite !in_app_iff; tauto].
  - eapply (umapx_agree ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (nval24_agree ASEGS) ltac:(lia));
      [exact Sm3 | intros a _; reflexivity | intros p n Hp _; apply HL; rewrite !in_app_iff; tauto].
  - destruct Sv1 as [B E C BLK]. constructor; [exact B | exact E | exact C |].
    destruct BLK as [Z0|(Hb & Hin & Hr)]; [left; exact Z0 | right]. split; [exact Hb|]. split; [|exact Hr].
    apply HL. rewrite !in_app_iff. right; right; right; left.
    unfold vec_blocks. rewrite (proj2 (Z.eqb_neq _ _) Hb). left. reflexivity.
  - destruct Sv2 as [B E C BLK]. constructor; [exact B | exact E | exact C |].
    destruct BLK as [Z0|(Hb & Hin & Hr)]; [left; exact Z0 | right]. split; [exact Hb|]. split; [|exact Hr].
    apply HL. rewrite !in_app_iff. right; right; right; right; left.
    unfold vec_blocks. rewrite (proj2 (Z.eqb_neq _ _) Hb). left. reflexivity.
  - destruct Sv3 as [B E C BLK]. constructor; [exact B | exact E | exact C |].
    destruct BLK as [Z0|(Hb & Hin & Hr)]; [left; exact Z0 | right]. split; [exact Hb|]. split; [|exact Hr].
    apply HL. rewrite !in_app_iff. right; right; right; right; right.
    unfold vec_blocks. rewrite (proj2 (Z.eqb_neq _ _) Hb). left. reflexivity.
Qed.

Lemma parser_repA_move : forall LB LB' m m' p c,
  parser_repA LB m p c -> 0 <= pc_cons c -> pc_cons c + 48 < 2 ^ 64 ->
  (forall a, parser_foot p c a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (forall a, pc_cons c + 32 <= a < pc_cons c + 40 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (forall b, In b (state_blocks (pc_state c)) -> In b (lbl LB')) ->
  parser_repA LB' m' p c.
Proof.
  intros LB LB' m m' p c PR Hc0 Hc1 HM HC HL.
  pose proof (parser_repA_keep LB m m' p c PR Hc0 Hc1 HM HC) as PR'.
  destruct PR' as [Pcons Puser Phdr Pins Phunk Pst Pdef Pal Prange Pconsf Pconsm Pconsd].
  unfold parser_repA. constructor; try assumption.
  eapply state_rep_moveA; [exact Pst | unfold ST_OFF; lia | unfold ST_OFF, PARSER_SIZE in *; lia | intros a _; reflexivity | exact HL].
Qed.

Section WDP.
  Context {HCEIL : HeapCeil}.

  Lemma parser_sh_keep : forall m m' p c words n,
    parser_sh m p c -> bp_phc (pc_state c) words n ->
    BllocRep.agree_on (bp_pfoot p c) m m' -> parser_sh m' p c.
  Proof.
    intros m m' p c words n (PA & CA & SSH) PH AG.
    assert (SHk : forall A sbs, SHAD m A sbs -> (forall a, sh A <= a < sh A + Z.of_nat (length sbs) -> bp_pfoot p c a) ->
                  SHAD m' A sbs).
    { intros A sbs (A0 & A8 & U) HF. split; [exact A0|]. split; [exact A8|].
      exact (BG_Free6.u8arr_pteq (bp_pfoot p c) m m' AG (sh A) sbs U HF). }
    pose proof PH as (_ & _ & Hm1 & Hm2 & Hm3 & E1 & E2 & E3 & N1 & N2 & N3 & C1 & C2 & C3).
    pose proof (bp_phc_blocks _ _ _ PH) as SB.
    assert (L500 : Z.of_nat (length (cc_gen 500 0)) = nsh 500) by (vm_compute; reflexivity).
    assert (L100 : Z.of_nat (length (cc_gen 100 0)) = nsh 100) by (vm_compute; reflexivity).
    destruct SSH as (U1 & U2 & U3 & VS1 & VS2 & VS3).
    unfold parser_sh. split; [|split].
    - destruct PA as [Hn S]. split; [exact Hn|]. apply SHk; [exact S|]. intros a Ha. right; right; left.
      rewrite shadow_of_length in Ha by (unfold PARSER_SIZE; lia). exact Ha.
    - destruct CA as [Hn S]. split; [exact Hn|]. apply SHk; [exact S|]. intros a Ha. right; right; right; left.
      rewrite shadow_of_length in Ha by lia. exact Ha.
    - unfold state_sh. split; [|split; [|split; [|split; [|split]]]].
      + rewrite Hm1. unfold umap_sh. cbn [t3a t3b t3c fst snd]. split; [intros C; exfalso; apply C; reflexivity | intros q k v []].
      + rewrite Hm2. unfold umap_sh. cbn [t3a t3b t3c fst snd]. split; [intros C; exfalso; apply C; reflexivity | intros q k v []].
      + rewrite Hm3. unfold umap_sh. cbn [t3a t3b t3c fst snd]. split; [intros C; exfalso; apply C; reflexivity | intros q k v []].
      + intros Hb. pose proof (VS1 Hb) as S.
        replace (t3c (st_v1 (pc_state c)) - t3a (st_v1 (pc_state c))) with 500 in * by lia.
        replace (t3b (st_v1 (pc_state c)) - t3a (st_v1 (pc_state c))) with 0 in * by lia.
        apply SHk; [exact S|]. intros a Ha. right; right; right; right.
        exists (t3a (st_v1 (pc_state c)), 500). split; [rewrite SB; left; reflexivity|].
        cbn [fst snd]. rewrite L500 in Ha. exact Ha.
      + intros Hb. pose proof (VS2 Hb) as S.
        replace (t3c (st_v2 (pc_state c)) - t3a (st_v2 (pc_state c))) with 100 in * by lia.
        replace (t3b (st_v2 (pc_state c)) - t3a (st_v2 (pc_state c))) with 0 in * by lia.
        apply SHk; [exact S|]. intros a Ha. right; right; right; right.
        exists (t3a (st_v2 (pc_state c)), 100). split; [rewrite SB; right; left; reflexivity|].
        cbn [fst snd]. rewrite L100 in Ha. exact Ha.
      + intros Hb. pose proof (VS3 Hb) as S.
        replace (t3c (st_v3 (pc_state c)) - t3a (st_v3 (pc_state c))) with 100 in * by lia.
        replace (t3b (st_v3 (pc_state c)) - t3a (st_v3 (pc_state c))) with 0 in * by lia.
        apply SHk; [exact S|]. intros a Ha. right; right; right; right.
        exists (t3a (st_v3 (pc_state c)), 100). split; [rewrite SB; right; right; left; reflexivity|].
        cbn [fst snd]. rewrite L100 in Ha. exact Ha.
  Qed.

  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.

  Lemma bp_al_err : forall (w : piw H) s s' st cost,
    bp_al H w s st -> as_AL H s' >= as_AL H s - cost -> cost <= PM_RESERVE ->
    as_AL H s' >= as_AL H (pw_s0 H w) - po_cost (pw_n H w).
  Proof.
    intros w s s' st cost (A1 & A2 & A3) AL Hc.
    pose proof (pm_prog_bounds (pi_c0 st)) as PB. unfold pm_phi, pm_cap in *. lia.
  Qed.

  Lemma bp_err_core : forall (w : piw H) s LB LBs m c s' LB' m',
    as_RHEAP H s LB m -> bp_pp H w LB LBs m c -> bp_phc (pc_state c) (pw_words H w) (pw_n H w) -> 0 <= pw_n H w ->
    pc_cons c + 48 < 2 ^ 64 -> mdef m (pw_p H w) PARSER_SIZE ->
    as_AL H s' >= as_AL H (pw_s0 H w) - po_cost (pw_n H w) ->
    Permutation LB' LB -> BllocRep.agree_on (bp_pfoot (pw_p H w) c) m m' ->
    as_RHEAP H s' LB' m' -> lb_own LBs m' -> mem_inv asegs m' ->
    (exists errv : word, rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    as_rauxv_ok H m' (pw_B H w) -> ACONST m' -> stack0 m' (pw_lo H w) (pw_shi H w) -> LINV m' ->
    pi_err H LINV w s' LB' LBs m' c.
  Proof.
    intros w s LB LBs m c s' LB' m' RH PP PH Hn HCB MD AL PM AG RH' OWN' MI' ER' RA' AC' S0' LI'.
    destruct PP as (PR & PSH & HC & HU & HD & (SO1 & SO2) & OWN & CW).
    pose proof (bp_phc_blocks _ _ _ PH) as SB.
    pose proof aceil_facts as ACF.
    pose proof PR as [_ _ _ _ _ _ _ _ PRg _ _ _].
    pose proof CW as (CW0 & CW1 & _).
    assert (BR : forall b, In b (state_blocks (pc_state c)) -> In b (lbl LB)).
    { intros b Hb. apply (Permutation_in _ (Permutation_sym SO2)) in Hb.
      destruct b as [A n]. destruct (lbl_in_inv LBs A n Hb) as (pid & Hin).
      apply (lbl_in LB pid A n). apply (Permutation_in _ (Permutation_sym SO1)). apply in_or_app. right. exact Hin. }
    assert (BRng : forall A n, In (A, n) (state_blocks (pc_state c)) -> 0 < A /\ A + n <= aceil).
    { intros A n Hb. destruct (lbl_in_inv LB A n (BR _ Hb)) as (pid & Hin).
      pose proof (ah_blocks H HH _ _ _ _ RH Hin) as (B0 & _ & _ & _ & B1 & _). cbn in B0, B1. lia. }
    assert (AGf : forall a, parser_foot (pw_p H w) c a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a Ha. refine (AG a (or_introl Ha) _).
      unfold PARSER_SIZE in PRg.
      destruct Ha as [Ha|[Ha|(b & Hb & Ha)]]; [unfold PARSER_SIZE in Ha; lia | unfold ST_OFF in Ha; lia |].
      destruct b as [A n]. destruct (BRng A n Hb). cbn [fst snd] in Ha. lia. }
    assert (AGc : forall a, pc_cons c + 32 <= a < pc_cons c + 40 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a Ha. refine (AG a (or_intror (or_introl Ha)) _). rewrite HC in Ha. lia. }
    assert (BRp : forall b, In b (state_blocks (pc_state c)) -> In b (lbl LB')).
    { intros b Hb. pose proof (BR b Hb) as Hb'. unfold lbl in Hb' |- *.
      exact (Permutation_in _ (Permutation_map _ (Permutation_sym PM)) Hb'). }
    pose proof SO2 as SO2'. rewrite SB in SO2'.
    assert (MEAS : pm_meas_ok (pw_n H w) LBs).
    { unfold pm_meas_ok. rewrite lb_small_lbl, nlarge_lbl, <- length_lbl.
      rewrite (fold_perm _ _ _ SO2'), (fold_perm (fun x => nlg (snd x)) _ _ SO2'), (Permutation_length SO2').
      cbn [fold_right snd length]. unfold nsmall, nlg, po_small, po_cnt, po_large. cbn -[Z.div].
      assert (0 <= pw_n H w / 2) by (apply Z.div_pos; lia). assert (0 <= pw_n H w / 3) by (apply Z.div_pos; lia). lia. }
    destruct MEAS as (M1 & M2 & M3).
    pose proof PH as (Hw & Hnw & _).
    unfold pi_err.
    split; [exact RH'|].
    split; [split; [eapply Permutation_trans; [exact PM | exact SO1] | exact SO2]|].
    split; [exact OWN'|].
    split; [eapply parser_repA_move; [exact PR | rewrite HC; lia | exact HCB | exact AGf | exact AGc | exact BRp]|].
    split; [exact (parser_sh_keep m m' (pw_p H w) c _ _ PSH PH AG)|].
    split; [exact HC|]. split; [exact HU|].
    split; [exact Hw|]. split; [exact Hnw|].
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact (bp_phc_vsteps _ _ _ PH)|].
    split; [intros q k Hqk; rewrite SB in Hqk; destruct Hqk as [E|[E|[E|[]]]]; injection E; intros; lia|].
    split; [exact MI'|]. split; [exact ER'|]. split; [exact RA'|]. split; [exact AC'|]. split; [exact S0'|].
    split; [exact LI'|]. split; [exact AL|].
    intros i Hi. unfold PARSER_SIZE in PRg, Hi.
    pose proof (AG (pw_p H w + i) ltac:(left; left; unfold PARSER_SIZE; lia) ltac:(lia)) as E.
    unfold wa in E. rewrite E. apply MD. unfold PARSER_SIZE. exact Hi.
  Qed.

  Lemma bp_pfresh_err : forall (w : piw H) s LB LBs m c s' LB' m' cost,
    as_RHEAP H s LB m -> bp_pfresh H w s LB LBs m c -> 0 <= pw_n H w -> pc_cons c + 48 < 2 ^ 64 -> mdef m (pw_p H w) PARSER_SIZE ->
    as_AL H s' >= as_AL H s - cost -> cost <= PM_RESERVE ->
    Permutation LB' LB -> BllocRep.agree_on (bp_pfoot (pw_p H w) c) m m' ->
    as_RHEAP H s' LB' m' -> lb_own LBs m' -> mem_inv asegs m' ->
    (exists errv : word, rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    as_rauxv_ok H m' (pw_B H w) -> ACONST m' -> stack0 m' (pw_lo H w) (pw_shi H w) -> LINV m' ->
    pi_err H LINV w s' LB' LBs m' c.
  Proof.
    intros w s LB LBs m c s' LB' m' cost RH (PP & (HDR & _) & AL0 & _) Hn HCB MD AL Hc PM AG RH' OWN' MI' ER' RA' AC' S0' LI'.
    exact (bp_err_core w s LB LBs m c s' LB' m' RH PP (bp_phc_ste _ _ _ _ HDR) Hn HCB MD
             (bp_al_err w s s' _ cost AL0 AL Hc) PM AG RH' OWN' MI' ER' RA' AC' S0' LI').
  Qed.

  Lemma bp_ploop_err : forall LF e ff (w : piw H) s LB LBs m c s' LB' m' cost,
    as_RHEAP H s LB m -> bp_ploop H LF e ff w s LB LBs m c -> 0 <= pw_n H w -> pc_cons c + 48 < 2 ^ 64 -> mdef m (pw_p H w) PARSER_SIZE ->
    as_AL H s' >= as_AL H s - cost -> cost <= PM_RESERVE ->
    Permutation LB' LB -> BllocRep.agree_on (bp_pfoot (pw_p H w) c) m m' ->
    as_RHEAP H s' LB' m' -> lb_own LBs m' -> mem_inv asegs m' ->
    (exists errv : word, rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    as_rauxv_ok H m' (pw_B H w) -> ACONST m' -> stack0 m' (pw_lo H w) (pw_shi H w) -> LINV m' ->
    pi_err H LINV w s' LB' LBs m' c.
  Proof.
    intros LF e ff w s LB LBs m c s' LB' m' cost RH (ee & _ & PP & HDR & AL0 & _) Hn HCB MD AL Hc PM AG RH' OWN' MI' ER' RA' AC' S0' LI'.
    exact (bp_err_core w s LB LBs m c s' LB' m' RH PP (bp_phc_st5 _ _ _ _ HDR) Hn HCB MD
             (bp_al_err w s s' _ cost AL0 AL Hc) PM AG RH' OWN' MI' ER' RA' AC' S0' LI').
  Qed.
End WDP.
