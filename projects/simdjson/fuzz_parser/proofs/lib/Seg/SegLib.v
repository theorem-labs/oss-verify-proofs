(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require PropExec CatSim AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosFxSound PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import FP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegFPSteps SegFP SegExplore SegTmpl SegGhost SegProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import AxSymExec3.AX2. Import AxSymExec3Sound.AX2S. Import AX2F. Import SX. Import ST. Import SP.

Module SLib.
Section S.
Variable segs : list Segment.
Variable GP : nat -> list word -> (word -> option byte) -> Prop.
Variable gfp : nat -> list expr -> list SG.gwin.
Variable gvc : SG.vc -> bool.
Hypothesis HGF : SG.gp_frameP GP gfp.
Hypothesis HGV : forall c, gvc c = true -> SG.vc_holds segs GP c.

Definition xpost (P : prog) (E : env) (m : word -> option byte) (rom : word -> option byte) (ms' : machine_state) : Prop :=
  exists X E' m' R' (F' : bvmap 5 word) (fc' : bv 32), In X (p_ex P) /\ ms' = MS R' F' (Z_to_bv 64 (t_pc X)) fc' None m' rom
    /\ frm0 fc'
    /\ rfull R' /\ regs_ok E' (t_regs X) R' /\ know_ok segs E' m' (t_know X) /\ SG.gholds GP E' m' (t_ghost X)
    /\ gagree (p_G P) E E' /\ eb E' = eb E
    /\ (forall x : word, outside_wins E (p_W P) (bv_unsigned x) -> m' x = m x)
    /\ wmono segs m m' /\ mem_inv segs m' /\ (forall lo hi, stk segs m lo hi -> stk segs m' lo hi).

Theorem prog_evt : forall P IT fuel rr hints T,
  pcheck segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT ->
  (forall TA, In TA (p_xt P) -> ext_ok segs GP P TA) ->
  (forall Sm, In Sm (p_cs P) -> summ_ok segs GP Sm) ->
  In T (p_tm P ++ p_xt P) ->
  forall E m rom R (F : bvmap 5 word) (fc : bv 32),
  aw_genuine E (p_A P) ->
  rfull R -> regs_ok E (t_regs T) R -> know_ok segs E m (t_know T) -> SG.gholds GP E m (t_ghost T) -> mem_inv segs m -> frm0 fc ->
  ExecF.evtF segs (fp_of (p_A P) E) (xpost P E m rom) (MS R F (Z_to_bv 64 (t_pc T)) fc None m rom).
Proof.
  intros P IT fuel rr hints T Hc HIT HEXT HCS HinT E m rom R F fc HAG HF HR HK HG MI HZ.
  assert (HT : tm_okF segs T E m rom (MS R F (Z_to_bv 64 (t_pc T)) fc None m rom)).
  { split; [exact HZ|]. split; [exact HF|]. exists R. cbn [tstate s_pc s_regs s_log s_know mem_denot].
    split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK]. }
  destruct (pcheck_sound segs GP gfp gvc HGF HGV P IT fuel rr hints Hc HIT HEXT HCS T E m rom _ HinT HAG HT HG)
    as (ms' & HmsF & X & E' & m' & HinX & HX & HGX & Hg & Hb & FR).
  pose proof (ExecF.mstepsF_msteps segs _ _ _ HmsF) as Hms.
  destruct HX as (HZ' & _ & R' & Hms' & HR' & _ & HK'). cbn [tstate s_pc s_regs s_log s_know mem_denot] in Hms', HR', HK'.
  assert (Hms2 : ms' = MS R' (ms_fregs ms') (Z_to_bv 64 (t_pc X)) (ms_fcsr ms') None m' rom).
  { rewrite Hms' at 1. destruct ms'; reflexivity. }
  pose proof (msteps_wrel segs _ _ Hms) as HW. rewrite Hms2 in HW. cbn [ms_mem MS] in HW.
  exists ms'. split; [exact HmsF|].
  exists X, E', m', R', (ms_fregs ms'), (ms_fcsr ms'). split; [exact HinX|]. split; [exact Hms2|]. split; [exact HZ'|].
  split; [rewrite Hms2 in Hms; exact (msteps_rfull segs _ _ Hms HF)|]. split; [exact HR'|]. split; [exact HK'|]. split; [exact HGX|].
  split; [exact Hg|]. split; [exact Hb|]. split; [exact FR|].
  split; [exact (wrel_wmono segs _ _ HW)|]. split; [exact (wrel_mem_inv segs _ _ HW MI)|].
  exact (wrel_stk segs _ _ HW).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sum_post (S : summ) (E : env) (M rom : word -> option byte) (ms' : machine_state) : Prop :=
  exists X E' M' R' (F' : bvmap 5 word) (fc' : bv 32), In X (sm_post S) /\ ms' = MS R' F' (Z_to_bv 64 (t_pc X)) fc' None M' rom
    /\ frm0 fc' /\ rfull R' /\ regs_ok E' (t_regs X) R' /\ know_ok segs E' M' (t_know X) /\ SG.gholds GP E' M' (t_ghost X)
    /\ gagree (sm_G S) E E' /\ eb E' = eb E /\ (forall x : word, outside_wins E (sm_W S) (bv_unsigned x) -> M' x = M x).

Definition summ_lib (S : summ) : Prop :=
  forall E M rom R (F : bvmap 5 word) (fc : bv 32),
    aw_genuine E (sm_A S) -> rfull R -> regs_ok E (t_regs (sm_pre S)) R -> know_ok segs E M (t_know (sm_pre S)) ->
    SG.gholds GP E M (t_ghost (sm_pre S)) -> frm0 fc ->
    ExecF.evtF segs (fp_of (sm_A S) E) (sum_post S E M rom) (MS R F (Z_to_bv 64 (t_pc (sm_pre S))) fc None M rom).

Theorem summ_of_lib : forall S, summ_lib S -> summ_ok segs GP S.
Proof.
  intros S HL E M rom ms HAG (HZ & HRF & HT) HG.
  destruct HT as (R & Hms & HR & _ & HK). cbn [tstate s_pc s_regs s_log s_know mem_denot] in Hms, HR, HK.
  assert (Hms2 : ms = MS R (ms_fregs ms) (Z_to_bv 64 (t_pc (sm_pre S))) (ms_fcsr ms) None M rom).
  { rewrite Hms at 1. destruct ms; reflexivity. }
  rewrite Hms2 in HRF. cbn [ms_regs MS] in HRF.
  destruct (HL E M rom R (ms_fregs ms) (ms_fcsr ms) HAG HRF HR HK HG HZ) as (ms' & Hrun & X & E' & M' & R' & F' & fc' & HinX & Hms' & HZ' & HRF' & HR' & HK' & HG' & Hg & Hb & FR).
  rewrite <- Hms2 in Hrun.
  exists ms', X, E', M'. split; [exact Hrun|]. split; [exact HinX|].
  split.
  { rewrite Hms'. split; [exact HZ'|]. split; [exact HRF'|]. exists R'. cbn [tstate s_pc s_regs s_log s_know mem_denot SFP.fx_of ms_fregs ms_fcsr MS].
    split; [reflexivity|]. split; [exact HR'|]. split; [exact I | exact HK']. }
  split; [exact HG'|]. split; [exact Hg|]. split; [exact Hb | exact FR].
Qed.

(* [comment removed for export] *)
Lemma rng_fp_of : forall W E w, aw_genuine E (Some W) -> In w W ->
  ExecF.rng (fp_of (Some W) E) (fst (awin_den E w)) (snd (awin_den E w) - fst (awin_den E w)).
Proof.
  intros W E w HG Hw. pose proof (HG w Hw) as G. split; [lia|]. split; [lia|].
  intros b j Hb Hj. exists w. split; [exact Hw|]. lia.
Qed.

(* [comment removed for export] *)
Corollary prog_evt0 : forall P IT fuel rr hints T,
  pcheck segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT -> p_A P = None ->
  (forall TA, In TA (p_xt P) -> ext_ok segs GP P TA) ->
  (forall Sm, In Sm (p_cs P) -> summ_ok segs GP Sm) ->
  In T (p_tm P ++ p_xt P) ->
  forall E m rom R (F : bvmap 5 word) (fc : bv 32),
  rfull R -> regs_ok E (t_regs T) R -> know_ok segs E m (t_know T) -> SG.gholds GP E m (t_ghost T) -> mem_inv segs m -> frm0 fc ->
  evt segs (xpost P E m rom) (MS R F (Z_to_bv 64 (t_pc T)) fc None m rom).
Proof.
  intros P IT fuel rr hints T Hc HIT HA HEXT HCS HinT E m rom R F fc HF HR HK HG MI HZ.
  apply (ExecF.evtF_evt segs (fp_of (p_A P) E)).
  apply (prog_evt P IT fuel rr hints T Hc HIT HEXT HCS HinT E m rom R F fc); try assumption. rewrite HA. exact I.
Qed.

(* [comment removed for export] *)
Corollary prog_evtF : forall P IT fuel rr hints T WA,
  pcheck segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT -> p_A P = Some WA ->
  (forall TA, In TA (p_xt P) -> ext_ok segs GP P TA) ->
  (forall Sm, In Sm (p_cs P) -> summ_ok segs GP Sm) ->
  In T (p_tm P ++ p_xt P) ->
  forall (RNG : ExecF.footprint) E m rom R (F : bvmap 5 word) (fc : bv 32),
  (forall w, In w WA -> ExecF.rng RNG (fst (awin_den E w)) (snd (awin_den E w) - fst (awin_den E w))) ->
  rfull R -> regs_ok E (t_regs T) R -> know_ok segs E m (t_know T) -> SG.gholds GP E m (t_ghost T) -> mem_inv segs m -> frm0 fc ->
  ExecF.evtF segs RNG (xpost P E m rom) (MS R F (Z_to_bv 64 (t_pc T)) fc None m rom).
Proof.
  intros P IT fuel rr hints T WA Hc HIT HA HEXT HCS HinT RNG E m rom R F fc HRNG HF HR HK HG MI HZ.
  assert (HAG : aw_genuine E (p_A P)).
  { rewrite HA. intros w Hw. destruct (HRNG w Hw) as (A & B & _). lia. }
  eapply ExecF.evtF_weaken; [|exact (prog_evt P IT fuel rr hints T Hc HIT HEXT HCS HinT E m rom R F fc HAG HF HR HK HG MI HZ)].
  rewrite HA. intros b j (w & Hw & L & U). destruct (HRNG w Hw) as (_ & _ & H). apply H; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section H.
Variable hmH : (word -> option byte) -> Prop.
Variable hmA : Z -> Prop.
Variable hmC : Z -> Z -> Prop.
Variable hmR : (word -> option byte) -> Prop.
Hypothesis HMC_sub : forall lo hi lo' hi', hmC lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> hmC lo' hi'.
Hypothesis HMF : forall E W M M', wins_client hmC E W -> hmH M -> PIosRegs.wrel segs M M' ->
  (forall x : word, outside_wins E W (bv_unsigned x) -> M' x = M x) -> hmH M'.

Definition xpostH (P : prog) (E : env) (m : word -> option byte) (rom : word -> option byte) (ms' : machine_state) : Prop :=
  exists X E' m' R' (F' : bvmap 5 word) (fc' : bv 32), In X (p_ex P) /\ ms' = MS R' F' (Z_to_bv 64 (t_pc X)) fc' None m' rom
    /\ frm0 fc'
    /\ rfull R' /\ regs_ok E' (t_regs X) R' /\ know_ok segs E' m' (t_know X) /\ SG.gholds GP E' m' (t_ghost X)
    /\ gagree (p_G P) E E' /\ eb E' = eb E
    /\ hmH m' /\ frame_ok hmA E (p_W P) (p_PS P) m m'
    /\ wmono segs m m' /\ mem_inv segs m' /\ (forall lo hi, stk segs m lo hi -> stk segs m' lo hi).

Theorem prog_evtH : forall P IT fuel rr hints T (Cnd : env -> Prop),
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT ->
  (forall TA, In TA (p_xt P) -> ext_okH segs GP hmH hmA hmR P Cnd TA) ->
  (forall Sm, In Sm (p_cs P) -> summ_okH segs GP hmH hmA hmC hmR Sm) ->
  (forall E E2, gagree (p_G P) E E2 -> eb E = eb E2 -> Cnd E -> Cnd E2) ->
  (forall E, Cnd E -> wins_client hmC E (p_W P)) ->
  (forall E, Cnd E -> forall w, In w (p_CR P) -> forall z, (fst (win_den E w) <= z < snd (win_den E w))%Z -> hmA z) ->
  (forall E M0, Cnd E -> hmH M0 -> know_ok segs E M0 (p_IK P)) ->
  In T (p_tm P ++ p_xt P) ->
  forall E m rom R (F : bvmap 5 word) (fc : bv 32),
  hmR rom -> aw_genuine E (p_A P) -> Cnd E -> hmH m ->
  rfull R -> regs_ok E (t_regs T) R -> know_ok segs E m (t_know T) -> SG.gholds GP E m (t_ghost T) -> mem_inv segs m -> frm0 fc ->
  ExecF.evtF segs (fp_of (p_A P) E) (xpostH P E m rom) (MS R F (Z_to_bv 64 (t_pc T)) fc None m rom).
Proof.
  intros P IT fuel rr hints T Cnd Hc HIT HEXT HCS HCG HCW HCR HIK HinT E m rom R F fc HRom HAG HCnd HHM HF HR HK HG MI HZ.
  assert (HT : tm_okF segs T E m rom (MS R F (Z_to_bv 64 (t_pc T)) fc None m rom)).
  { split; [exact HZ|]. split; [exact HF|]. exists R. cbn [tstate s_pc s_regs s_log s_know mem_denot].
    split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK]. }
  destruct (pcheck_soundH segs GP gfp gvc HGF HGV hmH hmA hmC hmR HMC_sub HMF P IT fuel rr hints Cnd Hc HIT HEXT HCS HCG HCW HCR HIK
              T E m rom _ HinT HRom HAG HCnd HHM HT HG)
    as (ms' & HmsF & X & E' & m' & HinX & HX & HGX & Hg & Hb & HH & FR).
  pose proof (ExecF.mstepsF_msteps segs _ _ _ HmsF) as Hms.
  destruct HX as (HZ' & _ & R' & Hms' & HR' & _ & HK'). cbn [tstate s_pc s_regs s_log s_know mem_denot] in Hms', HR', HK'.
  assert (Hms2 : ms' = MS R' (ms_fregs ms') (Z_to_bv 64 (t_pc X)) (ms_fcsr ms') None m' rom).
  { rewrite Hms' at 1. destruct ms'; reflexivity. }
  pose proof (msteps_wrel segs _ _ Hms) as HW. rewrite Hms2 in HW. cbn [ms_mem MS] in HW.
  exists ms'. split; [exact HmsF|].
  exists X, E', m', R', (ms_fregs ms'), (ms_fcsr ms'). split; [exact HinX|]. split; [exact Hms2|]. split; [exact HZ'|].
  split; [rewrite Hms2 in Hms; exact (msteps_rfull segs _ _ Hms HF)|]. split; [exact HR'|]. split; [exact HK'|]. split; [exact HGX|].
  split; [exact Hg|]. split; [exact Hb|]. split; [exact HH|]. split; [exact FR|].
  split; [exact (wrel_wmono segs _ _ HW)|]. split; [exact (wrel_mem_inv segs _ _ HW MI)|].
  exact (wrel_stk segs _ _ HW).
Qed.

(* [comment removed for export] *)
Theorem prog_evtHF : forall (hmF : ExecF.footprint) P IT fuel rr hints T (Cnd : env -> Prop),
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT ->
  (forall TA, In TA (p_xt P) -> ext_okHF segs GP hmH hmA hmR hmF P Cnd TA) ->
  (forall Sm, In Sm (p_cs P) -> summ_okHF segs GP hmH hmA hmC hmR hmF Sm) ->
  (forall E E2, gagree (p_G P) E E2 -> eb E = eb E2 -> Cnd E -> Cnd E2) ->
  (forall E, Cnd E -> wins_client hmC E (p_W P)) ->
  (forall E, Cnd E -> forall w, In w (p_CR P) -> forall z, (fst (win_den E w) <= z < snd (win_den E w))%Z -> hmA z) ->
  (forall E M0, Cnd E -> hmH M0 -> know_ok segs E M0 (p_IK P)) ->
  In T (p_tm P ++ p_xt P) ->
  forall E m rom R (F : bvmap 5 word) (fc : bv 32),
  hmR rom -> aw_genuine E (p_A P) -> Cnd E -> hmH m ->
  rfull R -> regs_ok E (t_regs T) R -> know_ok segs E m (t_know T) -> SG.gholds GP E m (t_ghost T) -> mem_inv segs m -> frm0 fc ->
  ExecF.evtF segs (fpu hmF (p_A P) E) (xpostH P E m rom) (MS R F (Z_to_bv 64 (t_pc T)) fc None m rom).
Proof.
  intros hmF P IT fuel rr hints T Cnd Hc HIT HEXT HCS HCG HCW HCR HIK HinT E m rom R F fc HRom HAG HCnd HHM HF HR HK HG MI HZ.
  assert (HT : tm_okF segs T E m rom (MS R F (Z_to_bv 64 (t_pc T)) fc None m rom)).
  { split; [exact HZ|]. split; [exact HF|]. exists R. cbn [tstate s_pc s_regs s_log s_know mem_denot].
    split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK]. }
  destruct (pcheck_soundHF segs GP gfp gvc HGF HGV hmH hmA hmC hmR HMC_sub HMF hmF P IT fuel rr hints Cnd Hc HIT HEXT HCS HCG HCW HCR HIK
              T E m rom _ HinT HRom HAG HCnd HHM HT HG)
    as (ms' & HmsF & X & E' & m' & HinX & HX & HGX & Hg & Hb & HH & FR).
  pose proof (ExecF.mstepsF_msteps segs _ _ _ HmsF) as Hms.
  destruct HX as (HZ' & _ & R' & Hms' & HR' & _ & HK'). cbn [tstate s_pc s_regs s_log s_know mem_denot] in Hms', HR', HK'.
  assert (Hms2 : ms' = MS R' (ms_fregs ms') (Z_to_bv 64 (t_pc X)) (ms_fcsr ms') None m' rom).
  { rewrite Hms' at 1. destruct ms'; reflexivity. }
  pose proof (msteps_wrel segs _ _ Hms) as HW. rewrite Hms2 in HW. cbn [ms_mem MS] in HW.
  exists ms'. split; [exact HmsF|].
  exists X, E', m', R', (ms_fregs ms'), (ms_fcsr ms'). split; [exact HinX|]. split; [exact Hms2|]. split; [exact HZ'|].
  split; [rewrite Hms2 in Hms; exact (msteps_rfull segs _ _ Hms HF)|]. split; [exact HR'|]. split; [exact HK'|]. split; [exact HGX|].
  split; [exact Hg|]. split; [exact Hb|]. split; [exact HH|]. split; [exact FR|].
  split; [exact (wrel_wmono segs _ _ HW)|]. split; [exact (wrel_mem_inv segs _ _ HW MI)|].
  exact (wrel_stk segs _ _ HW).
Qed.

(* [comment removed for export] *)
Theorem prog_evtHS : forall (hmF : ExecF.footprint) (hmS : Z -> Z -> Prop)
  (HMS_mono : forall s n s' n', hmS s n -> (s - n <= s' - n')%Z -> (s' <= s)%Z -> hmS s' n') P IT fuel rr hints T (Cnd : env -> Prop),
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT ->
  (forall TA, In TA (p_xt P) -> ext_okHF segs GP hmH hmA hmR hmF P Cnd TA) ->
  (forall Sm, In Sm (p_cs P) -> summ_okHS segs GP hmH hmA hmC hmR hmF hmS Sm) ->
  (forall E E2, gagree (p_G P) E E2 -> eb E = eb E2 -> Cnd E -> Cnd E2) ->
  (forall E, Cnd E -> wins_client hmC E (p_W P)) ->
  (forall E, Cnd E -> forall w, In w (p_CR P) -> forall z, (fst (win_den E w) <= z < snd (win_den E w))%Z -> hmA z) ->
  (forall E M0, Cnd E -> hmH M0 -> know_ok segs E M0 (p_IK P)) ->
  (forall E, Cnd E -> hs_ok hmS E (p_PS P) (p_W P)) ->
  In T (p_tm P ++ p_xt P) ->
  forall E m rom R (F : bvmap 5 word) (fc : bv 32),
  hmR rom -> aw_genuine E (p_A P) -> Cnd E -> hmH m ->
  rfull R -> regs_ok E (t_regs T) R -> know_ok segs E m (t_know T) -> SG.gholds GP E m (t_ghost T) -> mem_inv segs m -> frm0 fc ->
  ExecF.evtF segs (fpu hmF (p_A P) E) (xpostH P E m rom) (MS R F (Z_to_bv 64 (t_pc T)) fc None m rom).
Proof.
  intros hmF hmS HMSm P IT fuel rr hints T Cnd Hc HIT HEXT HCS HCG HCW HCR HIK HSTK HinT E m rom R F fc HRom HAG HCnd HHM HF HR HK HG MI HZ.
  assert (HT : tm_okF segs T E m rom (MS R F (Z_to_bv 64 (t_pc T)) fc None m rom)).
  { split; [exact HZ|]. split; [exact HF|]. exists R. cbn [tstate s_pc s_regs s_log s_know mem_denot].
    split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK]. }
  destruct (pcheck_soundHS segs GP gfp gvc HGF HGV hmH hmA hmC hmR HMC_sub HMF hmF hmS HMSm P IT fuel rr hints Cnd Hc HIT HEXT HCS HCG HCW HCR HIK
              HSTK T E m rom _ HinT HRom HAG HCnd HHM HT HG)
    as (ms' & HmsF & X & E' & m' & HinX & HX & HGX & Hg & Hb & HH & FR).
  pose proof (ExecF.mstepsF_msteps segs _ _ _ HmsF) as Hms.
  destruct HX as (HZ' & _ & R' & Hms' & HR' & _ & HK'). cbn [tstate s_pc s_regs s_log s_know mem_denot] in Hms', HR', HK'.
  assert (Hms2 : ms' = MS R' (ms_fregs ms') (Z_to_bv 64 (t_pc X)) (ms_fcsr ms') None m' rom).
  { rewrite Hms' at 1. destruct ms'; reflexivity. }
  pose proof (msteps_wrel segs _ _ Hms) as HW. rewrite Hms2 in HW. cbn [ms_mem MS] in HW.
  exists ms'. split; [exact HmsF|].
  exists X, E', m', R', (ms_fregs ms'), (ms_fcsr ms'). split; [exact HinX|]. split; [exact Hms2|]. split; [exact HZ'|].
  split; [rewrite Hms2 in Hms; exact (msteps_rfull segs _ _ Hms HF)|]. split; [exact HR'|]. split; [exact HK'|]. split; [exact HGX|].
  split; [exact Hg|]. split; [exact Hb|]. split; [exact HH|]. split; [exact FR|].
  split; [exact (wrel_wmono segs _ _ HW)|]. split; [exact (wrel_mem_inv segs _ _ HW MI)|].
  exact (wrel_stk segs _ _ HW).
Qed.

(* [comment removed for export] *)
Definition sum_postH (S : summ) (E : env) (M rom : word -> option byte) (ms' : machine_state) : Prop :=
  exists X E' M' R' (F' : bvmap 5 word) (fc' : bv 32), In X (sm_post S) /\ ms' = MS R' F' (Z_to_bv 64 (t_pc X)) fc' None M' rom
    /\ frm0 fc' /\ rfull R' /\ regs_ok E' (t_regs X) R' /\ know_ok segs E' M' (t_know X) /\ SG.gholds GP E' M' (t_ghost X)
    /\ gagree (sm_G S) E E' /\ eb E' = eb E /\ hmH M' /\ frame_ok hmA E (sm_W S) (sm_PS S) M M'.

Definition summ_libH (S : summ) : Prop :=
  forall E M rom R (F : bvmap 5 word) (fc : bv 32),
    hmR rom -> aw_genuine E (sm_A S) -> wins_client hmC E (sm_W S) -> hmH M ->
    rfull R -> regs_ok E (t_regs (sm_pre S)) R -> know_ok segs E M (t_know (sm_pre S)) ->
    SG.gholds GP E M (t_ghost (sm_pre S)) -> frm0 fc ->
    ExecF.evtF segs (fp_of (sm_A S) E) (sum_postH S E M rom) (MS R F (Z_to_bv 64 (t_pc (sm_pre S))) fc None M rom).

Theorem summ_of_libH : forall S, summ_libH S -> summ_okH segs GP hmH hmA hmC hmR S.
Proof.
  intros S HL E M rom ms HRom HAG HWC HHM (HZ & HRF & HT) HG.
  destruct HT as (R & Hms & HR & _ & HK). cbn [tstate s_pc s_regs s_log s_know mem_denot] in Hms, HR, HK.
  assert (Hms2 : ms = MS R (ms_fregs ms) (Z_to_bv 64 (t_pc (sm_pre S))) (ms_fcsr ms) None M rom).
  { rewrite Hms at 1. destruct ms; reflexivity. }
  rewrite Hms2 in HRF. cbn [ms_regs MS] in HRF.
  destruct (HL E M rom R (ms_fregs ms) (ms_fcsr ms) HRom HAG HWC HHM HRF HR HK HG HZ)
    as (ms' & Hrun & X & E' & M' & R' & F' & fc' & HinX & Hms' & HZ' & HRF' & HR' & HK' & HG' & Hg & Hb & HH & FR).
  rewrite <- Hms2 in Hrun.
  exists ms', X, E', M'. split; [exact Hrun|]. split; [exact HinX|].
  split.
  { rewrite Hms'. split; [exact HZ'|]. split; [exact HRF'|]. exists R'. cbn [tstate s_pc s_regs s_log s_know mem_denot SFP.fx_of ms_fregs ms_fcsr MS].
    split; [reflexivity|]. split; [exact HR'|]. split; [exact I | exact HK']. }
  split; [exact HG'|]. split; [exact Hg|]. split; [exact Hb|]. split; [exact HH | exact FR].
Qed.
End H.

End S.
End SLib.
