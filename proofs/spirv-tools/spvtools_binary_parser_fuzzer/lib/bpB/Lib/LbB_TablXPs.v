(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_DStat LbB_ContStmt LbB_ContV4 LbB_ContVot LbB_TablStmt LbB_TablOS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_RGl LbB_TablPT4 LbB_TablPT6 LbB_TablPT8 LbB_TablPT9 LbB_TablPT11 LbB_TablXP1 LbB_TablXPk1 LbB_TablXPk2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition XCS : list reg := [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition xs_wf (s : xsite) : Prop :=
     (xs_c s = VOT_SLOW_CREF \/ xs_c s = VOT_SLOW_RREF)
  /\ 0 <= xs_lit s < 2 ^ 31
  /\ (xs_setslots s = true -> xs_src s = 32)
  /\ (xs_setslots s = false -> xs_src s = 8 * xs_tk s /\ 6 <= xs_tk s <= 30)
  /\ (xs_pk s = 0 \/ 5 <= xs_pk s < 32) /\ (xs_fk s = 0 \/ 5 <= xs_fk s < 32) /\ (xs_tk s = 0 \/ 5 <= xs_tk s < 32)
  /\ (forall g b' e' c' E, xs_rout s (XG (g_SP g) (g_S1 g) (g_ff g) (g_v g) b' e' c') E = xs_rout s g E)
  /\ (forall g, Forall (fun rz : rrole => In (fst rz) XCS) (xs_rmid s g))
  /\ (forall g, Forall (fun rz : rrole => In (fst rz) XCS) (xs_rmid' s g))
  /\ 0 <= xs_sra s < 2 ^ 32 /\ xs_sra s mod 2 = 0 /\ 0 <= xs_ara s < 2 ^ 32 /\ xs_ara s mod 2 = 0.

Lemma RPl_mkR : forall l R x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  Forall (fun rz : rrole => In (fst rz) XCS) l -> RPl l R ->
  RPl l (mkR x1 (getr R 2) (getr R 3) (getr R 4) x5 x6 x7 (getr R 8) (getr R 9) x10 x11 x12 x13 x14 x15 x16 x17
             (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)
             x28 x29 x30 x31).
Proof.
  intros. eapply RPl_kept; [exact H0 | | exact H].
  intros r Hr. cbn in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; reflexivity.
Qed.

Lemma RPl_sp : forall g l R, RPl (xcommon g ++ l) R -> getr R 2 = Z_to_bv 64 (g_S1 g).
Proof. intros g l R RP. unfold xcommon in RP. cbn [app] in RP. apply RPl_cons in RP as [X _]. exact X. Qed.

Lemma xcommon_XCS : forall g, Forall (fun rz : rrole => In (fst rz) XCS) (xcommon g).
Proof. intros g. unfold xcommon. repeat (apply Forall_cons; [cbn; tauto|]). apply Forall_nil. Qed.

Lemma vec32A_set_endW : forall LB' m m' v b xs cap W, vec32A LB' m v b xs cap -> AIMG_TOP <= v ->
  munch ((v + 8, v + 16) :: W) m m' -> disjoint_from W v 24 -> disjoint_from W b (4 * Zlen xs) ->
  rw_cells asegs m' (v + 8) [C8 (Z_to_bv 64 (b + 4 * Zlen xs))] -> vec32A LB' m' v b xs cap.
Proof.
  intros LB' m m' v b xs cap W VEC VT MU D1 D2 HC. pose proof VEC as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2 & FE).
  pose proof (mdef_of_rw_cells_hi _ _ _ HC ltac:(lia)) as MD. cbn [cells_size csize] in MD.
  assert (AG : forall lo n, v <= lo -> lo + n <= v + 8 \/ v + 16 <= lo -> lo + n <= v + 24 -> 0 <= n -> agree_on (zwin lo (lo + n)) m m').
  { intros lo n H1 H2 H3 H4 a Ha. unfold zwin in Ha. apply MU. rewrite unsigned_lit by lia. cbn [outside]. split; [lia |].
    eapply disjoint_outside; [exact D1 | lia]. }
  unfold vec32A, vec32. split; [exact Hv|]. split; [exact Hv'|].
  split.
  { intros i Hi. destruct (Z_lt_le_dec i 8) as [L|L]; [|destruct (Z_lt_le_dec i 16) as [L'|L']].
    - rewrite (MU (Z_to_bv 64 (v + i))); [apply HD; lia|]. rewrite unsigned_lit by lia. cbn [outside]. split; [lia |].
      eapply disjoint_outside; [exact D1 | lia].
    - replace (v + i) with (v + 8 + (i - 8)) by lia. apply MD. lia.
    - rewrite (MU (Z_to_bv 64 (v + i))); [apply HD; lia|]. rewrite unsigned_lit by lia. cbn [outside]. split; [lia |].
      eapply disjoint_outside; [exact D1 | lia]. }
  split; [exact Hlen|]. split; [exact Hb|].
  split; [eapply fld_agree; [lia | cbn; lia | exact F0 | apply (AG v 8); cbn; lia]|].
  split; [exact (fld_of_rw_cells8 m' (v + 8) _ HC ltac:(lia))|].
  split; [eapply fld_agree; [lia | cbn; lia | exact F2 | apply (AG (v + 16) 8); cbn; lia]|].
  intros i Hi. destruct (FE i Hi) as [Hr HF]. split; [exact Hr|].
  destruct Hb as [[-> ->]|(Hb0 & Hal & Hc0 & Hbc & HIn & Hdj)]; [lia|].
  eapply fld_agree; [lia | cbn; lia | exact HF |].
  intros a Ha. unfold zwin in Ha. cbn in Ha. apply MU. rewrite unsigned_lit by lia. cbn [outside]. split; [lia |].
  eapply disjoint_outside; [exact D2 | lia].
Qed.

Lemma vec32A_pushW : forall LBi m m' v b xs cap x W,
  vec32A LBi m v b xs cap -> Zlen xs < cap -> 0 < b -> (v + 24 <= b \/ b + 4 * cap <= v) -> AIMG_TOP <= v ->
  munch ((b + 4 * Zlen xs, b + 4 * Zlen xs + 4) :: (v + 8, v + 16) :: W) m m' ->
  disjoint_from W v 24 -> disjoint_from W b (4 * Zlen xs) ->
  rw_cells asegs m' (b + 4 * Zlen xs) [C4 (Z_to_bv 64 x)] -> rw_cells asegs m' (v + 8) [C8 (Z_to_bv 64 (b + 4 * Zlen xs + 4))] ->
  0 <= x < 2 ^ 32 ->
  vec32A LBi m' v b (xs ++ [x]) cap.
Proof.
  intros LBi m m' v b xs cap x W VEC LC B0 DJ VT MU D1 D2 CX CE XR.
  pose proof VEC as (Hv & Hv' & HD & Hlen & Hb & F0 & F8 & F16 & FE).
  destruct Hb as [(E0 & _)|(_ & B16 & Cp & BC & _)]; [lia|].
  assert (AG : forall lo n, 0 <= lo -> 0 <= n -> lo + n <= 2 ^ 63 ->
               (lo + n <= b + 4 * Zlen xs \/ b + 4 * Zlen xs + 4 <= lo) -> (lo + n <= v + 8 \/ v + 16 <= lo) -> disjoint_from W lo n ->
               agree_on (zwin lo (lo + n)) m m').
  { intros lo n H1 H2 H3 K1 K2 K3 a Ha. unfold zwin in Ha. apply MU. rewrite unsigned_lit by lia. cbn [outside].
    split; [lia|]. split; [lia|]. eapply disjoint_outside; [exact K3 | lia]. }
  eapply (vec32A_push LBi m m' v b xs cap x VEC LC).
  - intros i Hi. destruct (Z_lt_le_dec i 8) as [L|L]; [|destruct (Z_lt_le_dec i 16) as [L'|L']].
    + rewrite (MU (Z_to_bv 64 (v + i))); [apply HD; lia|]. rewrite unsigned_lit by lia. cbn [outside].
      split; [lia|]. split; [lia|]. eapply disjoint_outside; [exact D1 | lia].
    + pose proof (mdef_of_rw_cells_hi _ _ _ CE ltac:(unfold AIMG_TOP in *; lia)) as MD8. cbn [cells_size csize] in MD8.
      replace (v + i) with (v + 8 + (i - 8)) by lia. apply MD8. lia.
    + rewrite (MU (Z_to_bv 64 (v + i))); [apply HD; lia|]. rewrite unsigned_lit by lia. cbn [outside].
      split; [lia|]. split; [lia|]. eapply disjoint_outside; [exact D1 | lia].
  - unfold fldA. eapply fld_agree; [lia | cbn; lia | exact F0 | apply (AG v 8); [lia | lia | lia | lia | lia | eapply vt_dj_sub; [exact D1 | lia | lia]]].
  - replace (b + 4 * (Zlen xs + 1)) with (b + 4 * Zlen xs + 4) by lia. apply fld_of_rw_cells8; [exact CE | lia].
  - unfold fldA. eapply fld_agree; [lia | cbn; lia | exact F16 | apply (AG (v + 16) 8); [lia | lia | lia | lia | lia | eapply vt_dj_sub; [exact D1 | lia | lia]]].
  - intros i Hi. destruct (FE i Hi) as [_ Fi]. unfold fldA. eapply fld_agree; [lia | cbn; lia | exact Fi |].
    apply (AG (b + 4 * i) 4); [lia | lia | lia | lia | lia | eapply vt_dj_sub; [exact D2 | lia | lia]].
  - apply fld_of_rw_cells4; [exact CX | lia].
  - exact XR.
Qed.

Section XPs.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Lemma xg_ok_of : forall (e : xpent H) ys mL sL LBi bi capi pidi, xpre H e -> as_RHEAP H sL LBi mL ->
    xvec H e ys mL LBi bi capi pidi -> xg_ok (xg e bi capi ys).
  Proof.
    intros e ys mL sL LBi bi capi pidi P RH PV.
    pose proof (rt_bp_base H HH) as HB.
    pose proof (xgeoP_of H e P) as G.
    destruct G as (SP16 & S45 & S132 & S1S & S1L & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SH0 & SH1 & SH2 & SH3 & FB & PB
                   & V8 & VB & VL & VF & VFL & VFP & SV1 & SV2 & TR & TP).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    destruct (xvec_blk H HB e ys mL sL LBi bi capi pidi RH PV) as (LEN & BK & DJV).
    unfold xg_ok. cbn [g_SP g_S1 g_ff g_v g_b g_e g_c xg].
    split; [exact S132|]. split; [exact S45|]. split; [exact S1S|]. split; [exact SPH|]. split; [exact F64|].
    split; [clear - FL; lia|]. split; [clear - FH CE LO; lia|]. split; [exact FB|]. split; [exact V8|].
    split; [clear - VB; lia|]. split; [clear - VB; lia|]. split; [clear - VB; lia|]. split; [clear - VL CE LO; lia|]. split; [exact VF|].
    destruct BK as [(C0 & B0)|(C0 & HIn & (A0 & A16 & An & AI & ACe & AF & AP))].
    - subst bi. split; [lia|]. split; [clear - LEN; lia|]. split; [clear - LEN; lia|]. split; [clear - S45 C0; lia|].
      split; [clear - LEN; Z.div_mod_to_equations; lia|]. split; [intros _; clear - C0; lia|].
      intros X. exfalso. exact (X eq_refl).
    - assert (B8 : bi mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
      assert (E4 : (bi + 4 * Zlen ys) mod 4 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
      pose proof (vt_band_of_aapp _ _ AP) as BB.
      split; [clear - A0; lia|]. split; [clear - LEN; lia|]. split; [clear - LEN; lia|]. split; [clear - ACe CE LO; lia|].
      split; [exact E4|]. split; [intros X; exfalso; clear - X A0; lia|].
      intros _. split; [clear - AI; unfold AIMG_TOP in AI; lia|]. split; [exact B8|].
      split; [clear - BB; lia|]. split; [exact (DJV ltac:(clear - A0; lia))|].
      clear - AF P3 P4. unfold AFS_SIZE in *. lia.
  Qed.

  Lemma xok0_slots : forall (e : xpent H) LBi, xpre H e -> xok0 H e LBi (xS1 e + 16, xS1 e + 32).
  Proof.
    intros e LBi P. pose proof (rt_bp_base H HH) as HB.
    pose proof (xgeoP_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & _ & SH1 & SH2 & _ & _ & _ & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    assert (AK : aceil <= xS1 e + 16) by (clear - CE LO; lia).
    destruct (stack_window_ok H LBi (xLF e) (xS1 e + 16) (xS1 e + 32) AK FS2) as (W1 & W2 & W3).
    pose proof (sh_lt_2_45 (x_ff e + 256) ltac:(lia)) as SB.
    unfold xok0. cbn [fst snd].
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
    split; [left; cbn [fst]; unfold AHI_LO; lia|].
    unfold ATP. lia.
  Qed.

  Lemma xwa_ok : forall s (e : xpent H) LBi bi capi ys, xs_wf s -> xpre H e ->
    Forall (xok0 H e LBi) (xwa s (xg e bi capi ys))
    /\ Forall (fun iv : Z * Z => (x_ff e <= fst iv /\ snd iv <= x_ff e + 256) \/ (sh (x_ff e) <= fst iv /\ snd iv <= sh (x_ff e) + 32)
                                  \/ (xS1 e <= fst iv /\ snd iv <= xSP e)) (xwa s (xg e bi capi ys))
    /\ Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= xSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (xXE H e) a))
              (xwa s (xg e bi capi ys)).
  Proof.
    intros s e LBi bi capi ys WF P. pose proof (rt_bp_base H HH) as HB.
    pose proof (xgeoP_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    destruct WF as (_ & _ & WS1 & WS2 & WPK & WFK & WTK & _).
    assert (FKW : forall k, (k = 0 \/ 5 <= k < 32) ->
              Forall (xok0 H e LBi) (fkw (xg e bi capi ys) k)
              /\ Forall (fun iv : Z * Z => (x_ff e <= fst iv /\ snd iv <= x_ff e + 256) \/ (sh (x_ff e) <= fst iv /\ snd iv <= sh (x_ff e) + 32)
                                            \/ (xS1 e <= fst iv /\ snd iv <= xSP e)) (fkw (xg e bi capi ys) k)
              /\ Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= xSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (xXE H e) a))
                        (fkw (xg e bi capi ys) k)).
    { intros k Hk. unfold fkw. cbn [g_ff xg]. destruct (Z.eqb_spec k 0) as [K0|K0].
      - split; [apply Forall_nil|]. split; apply Forall_nil.
      - split; [apply Forall_cons; [exact (proj1 (xok0_shb H e LBi k P ltac:(lia) ltac:(lia))) | apply Forall_nil]|].
        split; [apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_nil]|].
        apply Forall_cons; [|apply Forall_nil]. right. intros a Ha. cbn [fst snd] in Ha. apply xXE_frm. right; left. lia. }
    destruct (FKW _ WPK) as (K1 & K2 & K3). destruct (FKW _ WTK) as (K4 & K5 & K6).
    unfold xwa. destruct (xs_setslots s).
    - cbn [g_S1 g_ff xg]. split; [|split].
      + apply Forall_cons; [exact (xok0_slots e LBi P)|]. apply Forall_app. split; assumption.
      + apply Forall_cons; [right; right; cbn [fst snd]; lia|]. apply Forall_app. split; assumption.
      + apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_app. split; assumption.
    - destruct (WS2 eq_refl) as (SRC & TK1 & TK2). cbn [g_S1 g_ff xg]. split; [|split].
      + apply Forall_cons; [|apply Forall_app; split; assumption].
        replace (x_ff e + xs_src s + 4) with (x_ff e + xs_src s + 4) by lia.
        exact (proj1 (xok0_frm H e LBi (x_ff e + xs_src s) 4 P ltac:(lia) ltac:(lia) ltac:(lia))).
      + apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_app. split; assumption.
      + apply Forall_cons; [|apply Forall_app; split; assumption]. right. intros a Ha. cbn [fst snd] in Ha. apply xXE_frm. left. lia.
  Qed.

  Lemma xrout_geo : forall s (e : xpent H) bi capi ys b' c' E R, xs_wf s ->
    RPl (xcommon (xg e bi capi ys) ++ xs_rout s (xg e bi capi ys) E) R ->
    RPl (xcommon (XG (xSP e) (xS1 e) (x_ff e) (x_v e) b' E c') ++ xs_rout s (XG (xSP e) (xS1 e) (x_ff e) (x_v e) b' E c') E) R.
  Proof.
    intros s e bi capi ys b' c' E R WF RP. destruct WF as (_ & _ & _ & _ & _ & _ & _ & ST & _).
    apply RPl_app in RP as [RP1 RP2]. apply RPl_app. split.
    - exact RP1.
    - rewrite <- (ST (xg e bi capi ys) b' E c') in RP2. exact RP2.
  Qed.

  Lemma xstep_fast : forall s (e : xpent H) ys sv msF mo (Q : config -> Prop) R mL sL LBi bi capi pidi eL,
    xs_wf s -> site_runs s -> xpre H e -> XV e ->
    (xs_setslots s = true -> x_t e = xs_lit s) -> (xs_setslots s = false -> sv = Some (xs_sv s)) ->
    as_VIS H sL msF = MS R (x_F e) (Z_to_bv 64 (xs_pc s)) (x_fc e) None mL (seg_rom asegs) -> rfull R ->
    getr R 3 = x_gp e -> getr R 4 = x_tp e -> RPl (xcommon (xg e bi capi ys) ++ xs_rin s (xg e bi capi ys)) R ->
    as_AKREL H sL (mkCfg msF mo) -> as_MPRES H (x_mo e) mo ->
    xmem H e ys sv mL sL LBi bi capi pidi eL -> Zlen ys < capi ->
    (forall cf', xat H e (xs_nx s) (fun g => xs_rout s g (g_e g)) (ys ++ [xs_lit s]) (Some (xs_sv s)) cf' -> as_SR H Q cf') ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros s e ys sv msF mo Q R mL sL LBi bi capi pidi eL WF RUNS P XVH HT HSV VIS HF G3 G4 RP KR MP PM LC K.
    pose proof (rt_bp_base H HH) as HB.
    destruct RUNS as (RA & RB & _).
    destruct PM as (PF & SL & PV & XP & AL).
    pose proof PF as (MI & AC & ST & _ & _ & _ & _ & CL & _ & WF256 & WS32 & _ & _ & KC & _ & RH & _).
    pose proof (xgeoP_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CEl & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & _ & FS2 & _ & SHF1 & SHF2 & _ & FB & _
                   & V8 & VB & VL & VF & _ & _ & SV1 & SV2 & TR & TP).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    destruct (xvec_blk H HB e ys mL sL LBi bi capi pidi RH PV) as (LEN & BK & DJV).
    destruct BK as [(C0 & B0)|(C0 & HIn & ABR)]; [lia|].
    pose proof ABR as (A0 & A16 & An & AI & ACe & AF & AP).
    assert (B16 : 16 <= bi) by (clear - A0 A16; Z.div_mod_to_equations; lia).
    assert (B8 : bi mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
    pose proof PV as (VEC & SH & AD & WV & OB & GR).
    destruct (xcap_bound H e LBi bi capi pidi P XVH GR) as (CB1 & CB2 & CB3).
    assert (CB : 4 * capi <= 2 ^ 26) by (unfold vgrow in CB2; lia).
    specialize (DJV ltac:(lia)).
    pose proof (xg_ok_of e ys mL sL LBi bi capi pidi P RH PV) as GOK.
    pose proof VEC as (_ & _ & _ & _ & _ & F0 & F8 & F16 & _).
    assert (GZ : gz mL (x_v e) 24) by (intros j Hj; eapply sh0_of_addressable; [exact AD | change (8 * (24 / 8)) with 24; lia]).
    assert (W16 : wr_at asegs mL (xS1 e + 16) 16).
    { pose proof (wr_at_of_stk asegs mL (x_lo e) (xSP e) ST) as W. destruct W as (W1 & W2 & W).
      split; [lia|]. split; [lia|]. intros i Hi. replace (xS1 e + 16 + i) with (x_lo e + (xS1 e + 16 - x_lo e + i)) by lia. apply W. lia. }
    assert (W128 : wr_at asegs mL (x_ff e + 32) 128) by (eapply vt_wr_sub; [exact WF256 | lia | lia | lia]).
    assert (SLc : xs_setslots s = false -> xslotc (xs_sv s) (xg e bi capi ys) mL).
    { intros E0. rewrite (HSV E0) in SL. exact SL. }

    destruct (RA R (x_F e) (x_fc e) mL (seg_rom asegs) (xg e bi capi ys) RP GOK F0 F8 F16 GZ W16 SLc WS32 W128)
      as (R1 & M1 & pc1 & RUN1 & K13 & K14 & MU1 & WM1 & SK1 & MI1 & SL1 & SRC1 & TK1 & PK1 & BR).
    cbn [g_e g_c g_b g_v g_ff g_S1 g_SP xg] in BR.
    replace (bi + 4 * Zlen ys <? bi + 4 * capi) with true in BR by (symmetry; apply Z.ltb_lt; lia).
    destruct BR as (Epc & L1 & L10 & L11 & L12 & L13 & RP1). subst pc1.
    destruct (xwa_ok s e LBi bi capi ys WF P) as (OKA & FRA & XEA).
    assert (PF1 : xframe H e M1 sL LBi eL).
    { eapply (xframe_munch H HB e mL M1 sL LBi eL); [exact P | exact PF | exact MU1 | exact WM1 | exact (MI1 MI) | exact (SK1 _ _ ST) | exact OKA]. }
    pose proof (xvec_frm H HB e ys mL M1 sL LBi bi capi pidi _ P RH PV MU1 WM1 FRA) as PV1.
    assert (XP1 : xpres H (x_LB e) (xSP e) (xXE H e) (x_m e) M1).
    { pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RH0 & _).
      eapply (xpres_trans H); [exact XP|].
      eapply (xpres_of_munch H (x_s e) (x_LB e) (xSP e) (xXE H e) _ (x_m e) mL M1); [exact HB | exact RH0 | exact MU1 | exact WM1 | exact XEA]. }
    clear PF SL PV XP MU1 WM1 SK1 MI1 GZ W16 W128 SLc.
    eapply (sr_blk H HB); [exact KR | exact VIS | exact HF | exact RUN1 |].
    intros msF1 mo1 KR1 MP1 VIS1.

    destruct PV1 as (VEC1 & SH1 & AD1 & WV1 & OB1 & _).
    pose proof PF1 as (MI1 & AC1 & ST1 & _ & _ & _ & _ & CL1 & _ & _ & WS1 & _ & _ & KC1 & _ & RH1 & OW1).
    eapply (ahh_evt_then H HB); [exact KR1 | exact VIS1 | |].
    { eapply (rt_bp_annot H HH) with (beg := bi) (len := 4 * capi) (oldmid := 4 * Zlen ys) (newmid := 4 * Zlen ys + 4) (lo := x_lo e);
        [ exact L10 | exact L11 | exact L12 | rewrite L13; f_equal; lia | exact B8 | lia | lia | lia | exact AP
        | unfold AAPP_HI; lia | exact (SH1 C0)
        | rewrite (RPl_sp _ _ _ RP1); cbn [g_S1 xg]; rewrite u64_of_Z by lia;
          exact (proj1 (stk_split asegs M1 (x_lo e) (xS1 e) (xSP e) ST1 ltac:(lia)))
        | exact CEl
        | rewrite (RPl_sp _ _ _ RP1); cbn [g_S1 xg]; rewrite u64_of_Z by lia; unfold AINTRIN_STACK; lia
        | exact MI1 | exact AC1
        | unfold in_app_mem; destruct (vt_band_of_aapp _ _ AP) as [X|X]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia ]. }
    intros msF2 mo2 KR2 MP2 POST.
    destruct POST as (u0 & u1 & u2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & u3 & u4 & u5 & u6 & m2 & VIS2 & MU2 & WM2 & MI2 & ST2 & SH2 & AC2).
    pose proof WF as WF'. vhide WF'. destruct WF as (WC & WL & WSS1 & WSS2 & WPK & WFK & WTK & WRO & WMID & WMID' & SRA & SRA2 & ARA & ARA2).
    clear WC WPK WTK WRO WMID' SRA SRA2.
    rewrite L1 in VIS2. rewrite (ret_pc_even (xs_ara s) ltac:(lia) ARA2) in VIS2.
    rewrite (RPl_sp _ _ _ RP1) in MU2, ST2. cbn [g_S1 xg] in MU2, ST2.
    rewrite u64_of_Z in MU2, ST2 by lia. unfold AINTRIN_STACK in MU2.

    destruct (xok0_sh H e LBi pidi bi capi P HIn ABR C0) as [OKa OKas].
    destruct (xok0_stk H e LBi 4096 P ltac:(unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK; lia))
      as [OKb OKbs].
    assert (SHB : sh bi + nsh (4 * capi) <= sh (bi + 4 * capi) + 1) by (clear; unfold sh, nsh; Z.div_mod_to_equations; lia).
    pose proof (sh_lt_2_45 (bi + 4 * capi) ltac:(lia)) as SHB2.
    assert (ST2f : stk asegs m2 (x_lo e) (xSP e)).
    { apply (stk_merge asegs m2 (x_lo e) (xS1 e) (xSP e)); [exact ST2 | | lia].
      eapply stk_transport_disjoint; [exact (proj2 (stk_split asegs M1 (x_lo e) (xS1 e) (xSP e) ST1 ltac:(lia))) | exact MU2 | exact WM2 |].
      cbn. split; [lia|]. split; [lia | exact I]. }
    assert (PF2 : xframe H e m2 sL LBi eL).
    { eapply (xframe_munch H HB e M1 m2 sL LBi eL); [exact P | exact PF1 | exact MU2 | exact WM2 | exact MI2 | exact ST2f
        | apply Forall_cons; [exact OKa | apply Forall_cons; [exact OKb | apply Forall_nil]]]. }
    assert (SL2 : xslotc (xs_sv s) (xg e bi capi ys) m2).
    { pose proof (xslot_keep H e (Some (xs_sv s)) M1 m2 _ SL1 MU2 WM2
                    ltac:(apply Forall_cons; [exact OKas | apply Forall_cons; [exact OKbs | apply Forall_nil]])) as X. exact X. }
    assert (DVS : sh (x_v e) + nsh 24 <= sh bi \/ sh bi + nsh (4 * capi) <= sh (x_v e)).
    { destruct (pt_sh_apart (x_v e) 24 bi (4 * capi) ltac:(destruct VB; lia) ltac:(lia) ltac:(lia) ltac:(lia) V8 B8 ltac:(lia)) as [X|X];
      [left | right]; lia. }
    change (nsh 24) with 3 in DVS.
    assert (SRC2 : rw_cells asegs m2 (x_ff e + xs_src s) [C4 (Z_to_bv 64 (xs_lit s))]).
    { assert (SRC1' : rw_cells asegs M1 (x_ff e + xs_src s) [C4 (Z_to_bv 64 (xs_lit s))]).
      { destruct (xs_setslots s) eqn:ES; [|exact (SRC1 eq_refl)]. rewrite (WSS1 eq_refl). rewrite <- (HT eq_refl). exact CL1. }
      assert (SR : 32 <= xs_src s /\ xs_src s + 4 <= 248).
      { destruct (xs_setslots s) eqn:ES; [rewrite (WSS1 eq_refl); lia | destruct (WSS2 eq_refl) as (X1 & X2 & X3); lia]. }
      eapply rw_cells_transport; [exact SRC1' | exact MU2 | exact WM2 |]. cbn.
      split; [destruct (pt_app_sh (x_ff e + xs_src s) 4 bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct FB; [left|right]; lia)); lia|].
      split; [lia | exact I]. }
    assert (VEC2 : vec32A LBi m2 (x_v e) bi ys capi).
    { eapply (vec32A_munch LBi M1 m2 (x_v e) bi ys capi _ VEC1 MU2).
      - cbn. split; [destruct (pt_app_sh (x_v e) 24 bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VB; [left|right]; lia)); lia|].
        split; [destruct VL; lia | exact I].
      - cbn. split; [destruct (pt_app_sh bi (4 * Zlen ys) bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(lia)
                                 ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left|right]; lia)); lia|].
        split; [lia | exact I]. }
    assert (AD2 : addressable m2 (x_v e) 24).
    { eapply addressable_transport; [exact AD1 | exact MU2 | exact WM2 |]. change (nsh 24) with 3. cbn.
      split; [lia|]. split; [pose proof (sh_lt_2_45 (x_v e + 24) ltac:(destruct VB; lia)) as X;
                              assert (sh (x_v e) + 3 <= sh (x_v e + 24) + 1) by (clear; unfold sh; Z.div_mod_to_equations; lia); lia | exact I]. }
    assert (XP2 : xpres H (x_LB e) (xSP e) (xXE H e) (x_m e) m2).
    { eapply (xpres_trans H); [exact XP1|].
      eapply (xp_xstep H HB e LBi bi capi pidi sL M1 M1 m2 _ P GR RH1 C0 MU2 WM2).
      apply Forall_cons; [right; left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
      right; right; left. cbn [fst snd]. lia. }
    clear MU2 ST2 OKa OKas OKb OKbs.

    pose proof PF2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WS2f & _ & _ & _ & _ & RH2 & OW2).
    destruct (vt_slot_shk m2 bi capi (Zlen ys) SH2 A16 ltac:(lia) ltac:(lia) LC) as (j & SJ & JC).
    assert (JC' : j = 0 \/ ((bi + 4 * Zlen ys) mod 8 = 0 /\ 4 <= j < 8)).
    { destruct JC as [J|J]; [left; exact J|]. right.
      assert (M4 : (bi + 4 * Zlen ys) mod 8 = 0 \/ (bi + 4 * Zlen ys) mod 8 = 4) by (clear - B8; Z.div_mod_to_equations; lia).
      clear - J M4. lia. }
    assert (WE2 : wr_at asegs m2 (bi + 4 * Zlen ys) 4).
    { unfold lb_own in OW2. rewrite Forall_forall in OW2. pose proof (OW2 _ HIn) as W. cbn [blk_addr blk_size fst snd] in W.
      eapply vt_wr_sub; [exact W | lia | lia | lia]. }
    assert (WV2 : wr_at asegs m2 (x_v e + 8) 8).
    { eapply vt_wr_sub; [exact (wr_at_wmono _ _ _ _ WV1 WM2) | lia | lia | lia]. }
    assert (WV2' : wr_at asegs m2 (x_v e) 24) by exact (wr_at_wmono _ _ _ _ WV1 WM2).
    set (R3 := mkR (Z_to_bv 64 (xs_ara s)) (getr R1 2) (getr R1 3) (getr R1 4) u0 u1 u2 (getr R1 8) (getr R1 9) d0 d1 d2 d3 d4 d5 d6 d7
                   (getr R1 18) (getr R1 19) (getr R1 20) (getr R1 21) (getr R1 22) (getr R1 23) (getr R1 24) (getr R1 25)
                   (getr R1 26) (getr R1 27) u3 u4 u5 u6) in VIS2.
    assert (HF3 : rfull R3) by apply rfull_mkR.
    assert (RP3 : RPl (xcommon (xg e bi capi ys) ++ xs_rmid s (xg e bi capi ys)) R3).
    { apply RPl_mkR; [|exact RP1]. apply Forall_app. split; [apply xcommon_XCS | apply WMID]. }
    destruct (RB R3 (x_F e) (x_fc e) m2 (seg_rom asegs) (xg e bi capi ys) j RP3 GOK ltac:(cbn [g_e g_c xg]; lia) SRC2
                ltac:(cbn [g_e xg]; exact SJ) ltac:(cbn [g_e xg]; exact JC') SL2
                ltac:(cbn [g_v xg]; eapply sh0_of_addressable; [exact AD2 | change (8 * (24 / 8)) with 24; lia])
                ltac:(cbn [g_e xg]; exact WE2) ltac:(cbn [g_v xg]; exact WV2) ltac:(cbn [g_ff xg]; exact WS2f))
      as (R4 & M3 & RUN3 & K43 & K44 & MU3 & WM3 & SK3 & MI3 & CX3 & CV3 & FK3 & RP4).
    cbn [g_e g_v g_ff g_S1 g_SP g_b g_c xg] in MU3, CX3, CV3, FK3, RP4.
    eapply (sr_blk H HB); [exact KR2 | exact VIS2 | exact HF3 | exact RUN3 |].
    intros msF3 mo3 KR3 MP3 VIS3.
    pose proof (msteps_full asegs _ _ RUN3 HF3) as HF4. cbn [ms_regs] in HF4.
    rewrite <- (rfull_eq R4 HF4) in VIS3.
    apply K. exists R4, M3, sL, LBi, bi, capi, pidi, eL.
    split; [exact VIS3|]. split; [exact HF4|].
    split; [rewrite K43; change (getr R3 3) with (getr R1 3); rewrite K13; exact G3|].
    split; [rewrite K44; change (getr R3 4) with (getr R1 4); rewrite K14; exact G4|].
    assert (ZL : Zlen (ys ++ [xs_lit s]) = Zlen ys + 1) by (unfold Zlen; rewrite length_app; cbn [length]; lia).
    split.
    { unfold xg. rewrite ZL. replace (bi + 4 * (Zlen ys + 1)) with (bi + 4 * Zlen ys + 4) by lia.
      exact (xrout_geo s e bi capi ys bi (bi + 4 * capi) (bi + 4 * Zlen ys + 4) R4
               ltac:(destruct WF' as [X]; exact X) RP4). }
    split; [exact KR3|].
    split; [eapply (ah_mpres_trans H HB); [exact MP|]; eapply (ah_mpres_trans H HB); [exact MP1|];
            eapply (ah_mpres_trans H HB); [exact MP2 | exact MP3]|].

    destruct (xok0_slot H e LBi pidi bi capi (bi + 4 * Zlen ys) P HIn ABR ltac:(lia) ltac:(lia)) as [OKc OKcs].
    destruct (xok0_hdr H HB e LBi bi capi pidi P GR) as [OKd OKds].
    assert (FKW : Forall (xok0 H e LBi) (fkw (xg e bi capi ys) (xs_fk s)) /\ Forall (xsl_ok H e) (fkw (xg e bi capi ys) (xs_fk s))
                  /\ disjoint_from (fkw (xg e bi capi ys) (xs_fk s)) (x_v e) 24
                  /\ disjoint_from (fkw (xg e bi capi ys) (xs_fk s)) bi (4 * Zlen ys)
                  /\ disjoint_from (fkw (xg e bi capi ys) (xs_fk s)) (sh bi) (nsh (4 * capi))
                  /\ disjoint_from (fkw (xg e bi capi ys) (xs_fk s)) (sh (x_v e)) 3
                  /\ Forall (fun iv : Z * Z => (bi <= fst iv /\ snd iv <= bi + 4 * capi) \/ (sh bi <= fst iv /\ snd iv <= sh bi + nsh (4 * capi))
                              \/ (aceil <= fst iv /\ snd iv <= xSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (xXE H e) a))
                            (fkw (xg e bi capi ys) (xs_fk s))).
    { unfold fkw. cbn [g_ff xg]. destruct (Z.eqb_spec (xs_fk s) 0) as [K0|K0].
      - repeat (split; [first [apply Forall_nil | exact I]|]). apply Forall_nil.
      - assert (K5 : 5 <= xs_fk s) by (clear - WFK K0; lia). assert (K32 : xs_fk s < 32) by (clear - WFK K0; lia).
        destruct (xok0_shb H e LBi (xs_fk s) P K5 K32) as [Y1 Y2].
        pose proof (sh_lt_2_45 (x_ff e + 256) ltac:(lia)) as SB.
        assert (FF8 : x_ff e mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
        assert (D1 : x_v e + 24 <= sh (x_ff e) \/ sh (x_ff e) + 32 <= x_v e).
        { destruct (pt_app_sh (x_v e) 24 (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VB; [left | right]; lia)) as [X|X];
            change (nsh 256) with 32 in X; lia. }
        assert (D2 : bi + 4 * capi <= sh (x_ff e) \/ sh (x_ff e) + 32 <= bi).
        { destruct (pt_app_sh bi (4 * capi) (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia)
                     ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left|right]; lia)) as [X|X];
            change (nsh 256) with 32 in X; lia. }
        assert (D3 : sh bi + nsh (4 * capi) <= sh (x_ff e) \/ sh (x_ff e) + 32 <= sh bi).
        { destruct (pt_sh_apart bi (4 * capi) (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) B8 FF8
                     ltac:(clear - AF P3 P4; unfold AFS_SIZE, AFS_HDR in *; lia)) as [X|X]; change (nsh 256) with 32 in X; lia. }
        assert (D4 : sh (x_v e) + nsh 24 <= sh (x_ff e) \/ sh (x_ff e) + nsh 256 <= sh (x_v e)).
        { apply pt_sh_apart; [destruct VB; lia | lia | lia | lia | exact V8 | exact FF8 | clear - VF; lia]. }
        change (nsh 256) with 32 in D4. change (nsh 24) with 3 in D4.
        split; [apply Forall_cons; [exact Y1 | apply Forall_nil]|].
        split; [apply Forall_cons; [exact Y2 | apply Forall_nil]|].
        split; [clear - D1 K5 K32; cbn; split; [lia | exact I]|]. split; [clear - D2 LEN K5 K32; cbn; split; [lia | exact I]|].
        split; [clear - D3 K5 K32; cbn; split; [lia | exact I]|]. split; [clear - D4 K5 K32; cbn; split; [lia | exact I]|].
        apply Forall_cons; [|apply Forall_nil]. right; right; right. intros a Ha. cbn [fst snd] in Ha. apply xXE_frm. right; left. clear - Ha WFK. lia. }
    destruct FKW as (FK1 & FK2 & FK3d & FK4 & FK5 & FK6 & FK7).
    split.
    { eapply (xframe_munch H HB e m2 M3 sL LBi eL); [exact P | exact PF2 | exact MU3 | exact WM3 | exact (MI3 MI2) | exact (SK3 _ _ ST2f) |].
      apply Forall_cons; [exact OKc|]. apply Forall_cons; [exact OKd | exact FK1]. }
    split.
    { cbn [xslotP]. eapply (xslot_keep H e (Some (xs_sv s)) m2 M3 _ SL2 MU3 WM3).
      apply Forall_cons; [exact OKcs|]. apply Forall_cons; [exact OKds | exact FK2]. }
    split.
    { split; [eapply (vec32A_pushW LBi m2 M3 (x_v e) bi ys capi (xs_lit s) _ VEC2 LC ltac:(lia) DJV ltac:(destruct VB; unfold AIMG_TOP; lia)
                                  MU3 FK3d FK4 CX3 CV3 ltac:(lia))|].
      split.
      { intros _. rewrite ZL. replace (4 * (Zlen ys + 1)) with (4 * Zlen ys + 4) by lia.
        eapply SHAD_transport; [exact SH2 | exact MU3 | exact WM3 |].
        rewrite cc_gen_length by lia. cbn [disjoint_from].
        split; [destruct (pt_app_sh (bi + 4 * Zlen ys) 4 bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(lia)
                            ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left|right]; lia)); lia|].
        split; [destruct (pt_app_sh (x_v e + 8) 8 bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VB; [left|right]; lia)); lia|].
        exact FK5. }
      split.
      { eapply addressable_transport; [exact AD2 | exact MU3 | exact WM3 |]. change (nsh 24) with 3. cbn [disjoint_from].
        split; [destruct (pt_app_sh (bi + 4 * Zlen ys) 4 (x_v e) 24 ltac:(destruct VB; lia) ltac:(lia) ltac:(destruct VB; lia)
                            ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left|right]; lia)) as [X|X];
                change (nsh 24) with 3 in X; lia|].
        split; [destruct (pt_app_sh (x_v e + 8) 8 (x_v e) 24 ltac:(destruct VB; lia) ltac:(lia) ltac:(destruct VB; lia)
                            ltac:(destruct VB; [left|right]; lia)) as [X|X]; change (nsh 24) with 3 in X; lia|].
        exact FK6. }
      split; [exact (wr_at_wmono _ _ _ _ WV2' WM3)|].
      split; [exact OB1 | exact GR]. }
    split; [|exact AL].
    eapply (xpres_trans H); [exact XP2|].
    eapply (xp_xstep H HB e LBi bi capi pidi sL m2 m2 M3 _ P GR RH2 C0 MU3 WM3).
    apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|exact FK7].
    right; right; right. intros a Ha. cbn [fst snd] in Ha. unfold xXE. cbn [rin_ivs fst snd]. left. lia.
  Qed.
End XPs.
