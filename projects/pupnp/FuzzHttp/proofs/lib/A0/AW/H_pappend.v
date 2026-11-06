(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HApxF HttpRepA AWKit AWAuto HObjA HCount HObjK HObjF H2KitA HPrepA H_membuffer_append H_phdr_seg H_phdr H_pent_seg H_pent_kit H_presp H_pparse_stmt H_pparse_seg H_pparse_kit H_pappend_stmt.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.

Definition at_mappend (lo P SRC n : Z) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' j,
    ms' = MS (mkR (wz 0x8b2fc) (wz (q - 32)) gp tp t0 t1 t2 (wz P) (wz 2147450880) (wz (P + 400)) (wz SRC) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz membuffer_append_entryA) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (q - 32) /\ asan_env asegs m'
    /\ rw_cells asegs m' (q - 32) [CB 8 j; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma pappend_prefix : forall (lo P SRC n : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 32 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  evt asegs (at_mappend lo P SRC n ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz P) (wz SRC) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz parser_append_entryA) fc None m (seg_rom asegs)).
Proof.
  intros lo P SRC n ra q gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0. unfold parser_append_entryA.
  a0_prologue AE0 [(lo, q)]%Z m.
  carve_frame 32%nat ST.
  step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
  step. step. step. step. step. step.
  env_now AE0 MU WM.
  apply evt_done. unfold at_mappend, membuffer_append_entryA. do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [assumption| exact FR].
Qed.

#[using="Type"] Lemma pappend_tail : forall (lo P : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 x9 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 j
    (F : bvmap 5 word) fc m,
  stk asegs m lo (q - 32) -> rw_cells asegs m (q - 32) [CB 8 j; C8 s1; C8 s0; C8 ra] -> alloc_ceiling <= lo -> lo <= q - 32 -> q < 2^64 -> mem_inv asegs m ->
  evt asegs (fun ms' => stk asegs m lo q /\ exists u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
               ms' = MS (mkR ra (wz q) gp tp u0 u1 u2 s0 s1 (wz P) v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                        F (wz parser_parse_entryA) fc None m (seg_rom asegs))
    (MS (mkR (wz 0x8b2fc) (wz (q - 32)) gp tp t0 t1 t2 (wz P) x9 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x8b2fc) fc None m (seg_rom asegs)).
Proof.
  intros lo P ra q gp tp t0 t1 t2 s0 s1 x9 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 j F fc m.
  intros ST FR CLO LO QHI MI.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(lo, q)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  replace (q - 32) with (q + -32) in * by lia.
  step. lit_branch.
  step. step. step. step. step.
  step.
  release_to q.
  apply evt_done. split; [exact ST|]. unfold parser_parse_entryA. do 14 eexists. reflexivity.
Qed.

Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation PS := (aps FI AI).
Local Notation pstA := (pstA FI AI).

Section KEEP.
Variables (q lo P : Z) (st : fsstate FI) (mws ws : list word) (LBK : BL).
Hypothesis MWL : length mws = 22%nat.
Hypothesis WSL : length ws = 66%nat.
Local Notation ekeep := (H_pparse_kit.ekeep FI AI q lo P st LBK).
Local Notation WM32 := [(P + 400, P + 432)]%Z.

#[using="mws ws MWL WSL"] Lemma parser_keep_msg : forall (OB LB LB' : BL) m m' (t : pstA) A' len' cap' ok' bs',
  ekeep WM32 OB m m' ->
  bsub FI AI (hl_blocks FI AI (pa_ns FI AI t) (pa_hs FI AI t) ++ okbA FI AI (pa_sok FI AI t) (pa_SA FI AI t) (pa_scap FI AI t)) OB ->
  (forall b, In b (okbA FI AI (pa_sok FI AI t) (pa_SA FI AI t) (pa_scap FI AI t)) -> In b LB') ->
  p_parserA FI AI m LB P t ->
  p_msg FI AI m' LB' P A' len' cap' ok' bs' -> 0 <= pa_cur FI AI t <= len' ->
  p_parserA FI AI m' LB' P (pa_set_msg FI AI t A' len' cap' ok' bs').
Proof.
  intros OB LB LB' m m' t A' len' cap' ok' bs' EK SUB SIN (PSC & _ & _ & PMETH & PURI & PRS & PSM & PVER & PHL & PENT & PCTL & PURL & UBO) PMSG' CUR'.
  assert (DJ : forall X n, P <= X -> (X + n <= P + 400 \/ P + 432 <= X) -> disjoint_from WM32 X n) by (intros X n H1 H2; cbn [disjoint_from]; split; [lia| exact I]).
  unfold p_parserA, pa_set_msg. cbn [pa_cur pa_A pa_len pa_cap pa_okm pa_bs pa_meth pa_uc pa_rm pa_sc pa_SA pa_slen pa_scap pa_sok pa_sbs pa_isreq pa_maj pa_min pa_ns pa_hs pa_X pa_ebw pa_elw pa_err pa_hack pa_pos pa_entp pa_clen pa_csz pa_esp pa_ub pa_UB].
  split; [exact (H_pparse_kit.ek_scan FI AI q lo P st mws MWL LBK ws WSL _ _ m m' _ EK (DJ (P + 480) 20 ltac:(lia) ltac:(lia)) PSC)|].
  split; [exact PMSG'|]. split; [exact CUR'|].
  split; [exact (H_pparse_kit.ek_methw FI AI q lo P st mws MWL LBK ws WSL _ _ m m' _ EK (DJ P 8 ltac:(lia) ltac:(lia)) PMETH)|].
  split; [exact (H_pparse_kit.ek_uri FI AI q lo P st mws MWL LBK ws WSL _ _ m m' _ EK (DJ (P + 8) 216 ltac:(lia) ltac:(lia)) PURI)|].
  split; [exact (H_pparse_kit.ek_rs FI AI q lo P st mws MWL LBK ws WSL _ _ m m' _ _ EK (DJ (P + 224) 8 ltac:(lia) ltac:(lia)) PRS)|].
  split.
  { pose proof (H_pparse_kit.ek_smsg FI AI q lo P st mws MWL LBK ws WSL _ _ LB m m' _ _ _ _ _ EK (DJ (P + 232) 32 ltac:(lia) ltac:(lia))
                  ltac:(intros b Hb; apply SUB; apply in_or_app; right; exact Hb) PSM) as (MBC & OWN & R1 & R2).
    split; [exact MBC|]. split; [| split; [exact R1| exact R2]].
    destruct (pa_sok FI AI t) as [k|]; cbn [mownA] in OWN |- *; [| exact OWN]. destruct OWN as [_ BLK]. split; [apply SIN; left; reflexivity| exact BLK]. }
  split; [exact (H_pparse_kit.ek_ver FI AI q lo P st mws MWL LBK ws WSL _ _ m m' _ _ _ EK (DJ (P + 264) 24 ltac:(lia) ltac:(lia)) PVER)|].
  split; [apply (H_pparse_kit.ek_hlist FI AI q lo P st mws MWL LBK ws WSL _ _ m m' _ _ _ EK PHL); [intros b Hb; apply SUB; apply in_or_app; left; exact Hb| exact (DJ (P + 288) 96 ltac:(lia) ltac:(lia))]|].
  split; [exact (H_pparse_kit.ek_ent FI AI q lo P st mws MWL LBK ws WSL _ _ m m' _ _ EK (DJ (P + 384) 16 ltac:(lia) ltac:(lia)) PENT)|].
  split; [exact (H_pparse_kit.ek_ctl FI AI q lo P st mws MWL LBK ws WSL _ _ m m' _ _ _ _ _ _ _ EK (DJ (P + 440) 40 ltac:(lia) ltac:(lia)) PCTL)|].
  split; [exact (H_pparse_kit.ek_url FI AI q lo P st mws MWL LBK ws WSL _ _ m m' _ EK (DJ (P + 432) 8 ltac:(lia) ltac:(lia)) PURL)| exact UBO].
Qed.
End KEEP.

Hypothesis PP : pparse_stmt_A FI AI J.

#[using="Type"] Lemma pp_side_msg : forall (t : pstA) A1 c1 o1 b1 A2 c2 o2 b2 L,
  pp_sideA FI AI (pa_set_msg FI AI t A1 L c1 o1 b1) -> pp_sideA FI AI (pa_set_msg FI AI t A2 L c2 o2 b2).
Proof. intros t A1 c1 o1 b1 A2 c2 o2 b2 L H. exact H. Qed.

#[using="IC AC ASL AMS PP"] Theorem pappend_spec_A : pappend_stmt_A FI AI J.
Proof.
  unfold pappend_stmt_A.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB LBK st P lo gmax canary ws mws cslack GL t ras SRC n src.
  intros HR RF FCO AE ST CLO LO QAL QTOP MI PLB PHI PAL SHWP PAR SIDE CAPB BUD PBUD BSUB ND WSL WSOK MTOK GMX GLOK GERM STAT ZST SHZ SHR FPC TR1 TR2 SRCB LEN NZK S0 MSRC SHWS SRCHI DJS -> -> ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  assert (N0 : 0 <= n) by (rewrite <- LEN; lia).
  unfold LMAX_A in CAPB.

  assert (PFS : FSB FI <= P /\ P + 504 <= FSB FI + A0_FS_SIZE /\ 0x609000 <= P).
  { destruct PLB as (g & Hg & G1 & G2). pose proof (live_wf FI st m RF) as LW. rewrite Forall_forall in LW. destruct (LW g Hg) as (_ & GLO & GHI & _).
    pose proof (fsb_ok FI) as (B1 & _). unfold ff_size in *. clear - G1 G2 GLO GHI B1. lia. }
  destruct PFS as (PFS1 & PFS2 & PLO).
  assert (POK : H_pparse_seg.pq_okA FI q lo P st) by (unfold H_pparse_seg.pq_okA; repeat split; try assumption; lia).
  pose proof MTOK as (MWL & _).
  pose proof PAR as (PSC & PMSG & CUR & _). destruct PMSG as (MBC & OWN & HLC & HCP & NUL).

  set (HB := hl_blocks FI AI (pa_ns FI AI t) (pa_hs FI AI t)) in *.
  set (RB := okbA FI AI (pa_sok FI AI t) (pa_SA FI AI t) (pa_scap FI AI t) ++ pa_UB FI AI t) in *.
  assert (PBE : pa_blocks FI AI t = HB ++ okbA FI AI (pa_okm FI AI t) (pa_A FI AI t) (pa_cap FI AI t) ++ RB) by reflexivity.
  pose proof ND as ND0. rewrite PBE in ND0.
  apply nd_app in ND0. destruct ND0 as (NDP & IDK & NDK).
  apply nd_app in NDP. destruct NDP as (NDH & IDH & NDMR).
  apply nd_app in NDMR. destruct NDMR as (NDM & IDM & NDR).
  apply idj_app_l in IDK. destruct IDK as (IDK1 & IDK23). apply idj_app_l in IDK23. destruct IDK23 as (IDK2 & IDK3).
  apply idj_app_r in IDH. destruct IDH as (IDH1 & IDH2).
  assert (KEEP : forall b, In b (HB ++ RB ++ LBK) -> In b (lb_keepA FI AI (pa_okm FI AI t) LB)).
  { intros b Hb. assert (BIN : In b LB).
    { apply BSUB. rewrite PBE. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; apply in_or_app; left; exact Hb|].
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hb| apply in_or_app; right; exact Hb]. }
    destruct (pa_okm FI AI t) as [k|] eqn:EOK; cbn [lb_keepA]; [| exact BIN].
    apply (in_lb_remove FI AI); [exact BIN|]. cbn [okbA] in IDH1, IDM, IDK2.
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (IDH1 b _ Hb ltac:(left; reflexivity))|].
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [intros E; exact (IDM _ b ltac:(left; reflexivity) Hb (eq_sym E))| intros E; exact (IDK2 _ b ltac:(left; reflexivity) Hb (eq_sym E))]. }
  assert (KSUB : bsub FI AI LBK LB) by (intros b Hb; apply BSUB; apply in_or_app; right; exact Hb).
  assert (OSUB : bsub FI AI (HB ++ RB) LB).
  { intros b Hb. apply BSUB. rewrite PBE. apply in_or_app. left. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply in_or_app; right; exact Hb]. }

  eapply (aj_evt FI AI J). { eapply (pappend_prefix lo P SRC n); try eassumption; lia. }
  intros ms' (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & jf & -> & MU1 & WM1 & MI1 & ST1 & AE1 & FR1).
  assert (BIV1 : Forall (blk_iv FI AI LB) [(lo, q)]) by (constructor; [left; cbn; lia| constructor]).
  destruct (H_pparse_kit.ekeep_munch FI AI ASL AMS q lo P st m POK RF mws MWL LBK ws s LB HR KSUB WSL [(lo, q)]%Z [] [] (HB ++ RB) s LB m m1 MU1 WM1) as (EK1 & HR1).
  { constructor; [| constructor]. unfold H_pparse_kit.ecls. cbn [fst snd]. split; [lia| left; lia]. }
  { constructor. } { constructor. } { exact HR. } { intros b []. } { exact OSUB. } { exact KSUB. } { intros a b []. } { intros a b []. }
  pose proof (rfake_blk_write FI AI s LB st m m1 _ HR RF MU1 WM1 ltac:(constructor; [split; [left; cbn; lia| cbn; lia]| constructor])) as RF1.
  pose proof (shw_frame _ m m1 P 504 SHWP MU1 (app_ivs_blk FI AI s LB m _ HR BIV1)) as SHWP1.
  pose proof (shw_frame _ m m1 SRC n SHWS MU1 (app_ivs_blk FI AI s LB m _ HR BIV1)) as SHWS1.
  assert (SUBk : forall b, In b (lb_keepA FI AI (pa_okm FI AI t) LB) -> In b LB) by (intros b Hb; eapply (lb_keepA_sub FI AI); exact Hb).
  destruct (msrcA_lo FI AI s LB LBK q st m SRC n HR KSUB RF MSRC ltac:(lia) N0) as (_ & SLO & _).
  pose proof (bytes_at_transport asegs _ m m1 _ _ SRCB MU1 ltac:(cbn [disjoint_from]; rewrite LEN; split; [lia| exact I])) as SRCB1.
  pose proof (rw_cells_transport asegs _ m m1 _ _ MBC MU1 WM1 ltac:(unfold mbuf_cells; cbn [disjoint_from cells_size csize Nat.add]; lia)) as MBC1.
  assert (OWN1 : mownA FI AI m1 LB (pa_A FI AI t) (pa_cap FI AI t) (pa_okm FI AI t) (pa_bs FI AI t)).
  { destruct (pa_okm FI AI t) as [k|]; cbn [mownA] in OWN |- *; [| exact OWN]. destruct OWN as [HIN BLK]. split; [exact HIN|].
    destruct (am_block_range FI AI s LB m _ HR HIN) as (R1 & R2 & R3 & R4 & _). cbn [blk_addr blk_size fst snd] in *.
    eapply rw_cells_transport; [exact BLK| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia]. }

  eapply (aj_bind FI AI J).
  { eapply (membuffer_append_spec_A IC FI AI J AC ASL AMS) with (lo := lo) (q := q - 32) (st := st) (ok := pa_okm FI AI t) (MB := P + 400) (SRC := SRC) (n := n)
      (A := pa_A FI AI t) (len := pa_len FI AI t) (cap := pa_cap FI AI t) (src := src) (bs := pa_bs FI AI t);
      [ exact HR1 | exact RF1 | exact AE1 | exact ST1 | exact CLO | unfold A0_RT_STACK; lia | clear - QAL; Z.div_mod_to_equations; lia | lia | exact MI1
      | exact MBC1 | exact HLC | lia | exact BUD | exact OWN1
      | right; right; apply (lb_sub _ P 504 _ _ PLB); lia | lia | clear - PAL; Z.div_mod_to_equations; lia
      | eapply shw_sub; [exact SHWP1| lia| lia| lia]
      | exact SRCB1 | exact LEN | exact S0
      | eapply (msrcA_weaken FI AI); [exact MSRC| lia| intros b Hb; apply KEEP; apply in_or_app; right; apply in_or_app; right; exact Hb| intros g Hg; exact Hg]
      | exact SHWS1 | exact SRCHI | replace (P + 400 + 32) with (P + 432) by lia; exact DJS | reflexivity | reflexivity | reflexivity ]. }
  intros s' LB' ms' PO. unfold membuffer_append_post_A in PO.
  destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & A' & cap' & ok' & bs' & -> & MI2 & ST2 & AE2 & RF2 & APX & HR2 & ALT & MBC2 & B1 & B2 & OWN2 & FN1 & FN2).
  replace (P + 400 + 32) with (P + 432) in APX by lia.

  assert (FR2 : rw_cells asegs m2 (q - 32) [CB 8 jf; C8 s1; C8 s0; C8 ra]).
  { eapply (apx_rw_cells FI AI); [exact APX| exact FR1| apply aclient_range_above; lia| cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I]]. }
  pose proof (apxF_of_apx FI AI [(P + 400, P + 432)]%Z _ _ (q - 32) (q - 32) st st m1 m1 m2 APX RF1 ltac:(lia) (fun b Hb => Hb) (fun g Hg => Hg)) as APF1.
  assert (SHWP2 : shw m2 P 504).
  { apply (shw_apxF_lb FI AI _ _ _ st m1 m2 P 504 SHWP1 APF1 RF1 PLB). intros a Ha. cbn [outside]. split; [| exact I].
    pose proof (fsb_ok FI) as (G1 & G2 & _ & G4 & G5). unfold sh, SHADOW_OFF in Ha. clear - Ha PFS1 PFS2 G1 G2 G4 G5 ACR. Z.div_mod_to_equations. lia. }

  assert (EK2 : H_pparse_kit.ekeep FI AI q lo P st LBK [(P + 400, P + 432)]%Z (HB ++ RB) m1 m2).
  { apply (H_pparse_kit.ekeep_apxF FI AI ASL AMS q lo P st m POK RF mws MWL LBK ws WSL [(P + 400, P + 432)]%Z [(P + 400, P + 432)]%Z [] (HB ++ RB)
             (lb_keepA FI AI (pa_okm FI AI t) LB) s LB (q - 32) st m1 m2 APF1).
    - lia.
    - lia.
    - intros g Hg; exact Hg.
    - constructor; [| constructor]. unfold H_pparse_kit.acls. cbn [fst snd]. split; [lia| left; cbn [inside]; left; lia].
    - constructor; [| constructor]. left. unfold H_pparse_seg.inP. cbn [fst snd]. lia.
    - constructor; [| constructor]. unfold pparse_WA. cbn [inside fst snd]. left. lia.
    - exact HR1.
    - intros b [].
    - intros b Hb. apply KEEP. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply in_or_app; left; exact Hb].
    - exact OSUB.
    - intros b Hb. apply KEEP. apply in_or_app; right; apply in_or_app; right; exact Hb.
    - exact KSUB.
    - intros a b [].
    - intros a b [].
    - exact SHWP2. }
  pose proof (H_pparse_kit.ekeep_trans FI AI q lo P st LBK _ _ m m1 m2
                (H_pparse_kit.ekeep_weaken FI AI q lo P st LBK [] [(P + 400, P + 432)]%Z _ m m1 EK1 (fun a k _ => I)) EK2) as EK.

  replace (ret_pc (Z_to_bv 64 0x8b2fc)) with (Z_to_bv 64 0x8b2fc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply (aj_evt FI AI J). { eapply (pappend_tail lo P ra q gp (wz A0_TP)) with (s0 := s0) (s1 := s1) (j := jf); [exact ST2| exact FR2| exact CLO| lia| lia| exact MI2]. }
  intros ms' (ST3 & u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & ->).
  destruct EK as (EKC & _ & _ & _ & _ & APXF & FPK). pose proof (H_pparse_kit.ekeep_trans FI AI q lo P st LBK _ _ m m1 m2
                (H_pparse_kit.ekeep_weaken FI AI q lo P st LBK [] [(P + 400, P + 432)]%Z _ m m1 EK1 (fun a k _ => I)) EK2) as EK.
  set (ta := pa_set_msg FI AI t A' (pa_len FI AI t + n) cap' ok' bs').
  assert (APD : pappended FI AI s LB t n src s' LB' ta).
  { exists A', cap', ok', bs'. split; [reflexivity|]. split; [exact ALT|]. split; [lia|]. split; [exact FN1| exact FN2]. }

  assert (LBS : length (firstn (Z.to_nat (pa_len FI AI t)) (pa_bs FI AI t)) = Z.to_nat (pa_len FI AI t)).
  { destruct (pa_okm FI AI t) as [k|]; cbn [mownA] in OWN.
    - destruct OWN as [_ [[WF _] _]]. cbn in WF. destruct WF as (W0 & _). rewrite firstn_length_le; [reflexivity| rewrite W0; lia].
    - destruct OWN as (_ & _ & ->). rewrite NUL. reflexivity. }
  assert (NTH : forall (l : list byte) i x, nth_error (firstn (S i) l) i = Some x -> nth_error l i = Some x).
  { clear. induction l as [|y l IH]; intros [|i] x H; cbn in *; try discriminate; [exact H| exact (IH i x H)]. }
  assert (PMSG2 : p_msg FI AI m2 LB' P A' (pa_len FI AI t + n) cap' ok' bs').
  { unfold p_msg. split; [exact MBC2|]. split; [exact OWN2|]. split; [lia|]. split; [unfold LMAX_A; lia|].
    assert (NC : n = 0 \/ 1 <= n) by lia. destruct NC as [N00|N1].
    - destruct NZK as [N1|EOK]; [exfalso; lia|]. destruct ALT as [(-> & _)|(k' & _ & _ & _ & HC1 & _)]; [| exfalso; lia].
      rewrite EOK in *. lia.
    - specialize (FN2 ltac:(lia)). destruct ok' as [k'|].
      + apply NTH. replace (S (Z.to_nat (pa_len FI AI t + n))) with (Z.to_nat (pa_len FI AI t + n + 1)) by lia. rewrite FN2.
        rewrite nth_error_app2 by (rewrite LBS; lia). rewrite LBS. rewrite nth_error_app2 by lia.
        replace (Z.to_nat (pa_len FI AI t + n) - Z.to_nat (pa_len FI AI t) - length src)%nat with 0%nat by lia. reflexivity.
      + exfalso. cbn [mownA] in OWN2. destruct OWN2 as (_ & _ & ->). rewrite firstn_nil in FN2. destruct (firstn _ (pa_bs FI AI t)); destruct src; discriminate. }

  assert (KEEP' : forall b, In b (HB ++ RB ++ LBK) -> In b LB').
  { intros b Hb. pose proof (KEEP b Hb) as Hk. destruct ALT as [(_ & -> & _)|(k' & _ & -> & _)]; [exact (SUBk b Hk)| right; exact Hk]. }
  assert (PAR2 : p_parserA FI AI m2 LB' P ta).
  { apply (parser_keep_msg q lo P st mws ws LBK MWL WSL (HB ++ RB) LB LB' m m2 t A' (pa_len FI AI t + n) cap' ok' bs' EK).
    - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply in_or_app; left; exact Hb].
    - intros b Hb. apply KEEP'. apply in_or_app; right; apply in_or_app; left; apply in_or_app; left; exact Hb.
    - exact PAR.
    - exact PMSG2.
    - lia. }
  assert (PBE2 : pa_blocks FI AI ta = HB ++ okbA FI AI ok' A' cap' ++ RB) by reflexivity.
  assert (BN2 : bsub FI AI (pa_blocks FI AI ta ++ LBK) LB' /\ NoDup (map blk_id (pa_blocks FI AI ta ++ LBK))).
  { rewrite PBE2. destruct ALT as [(-> & -> & -> & -> & _)|(k' & -> & ELB & _)].
    - rewrite <- PBE. split; [exact BSUB| exact ND].
    - pose proof (am_blocks_nodup FI AI s' LB' m2 HR2) as NDL. rewrite ELB in NDL. apply nd_cons in NDL. destruct NDL as (IDN & _).
      assert (IDN' : idj [(k', A', cap' + 1)] (HB ++ RB ++ LBK)) by (eapply idj_sub_r; [exact IDN| exact KEEP]).
      apply idj_app_r in IDN'. destruct IDN' as (IDN1 & IDN23). apply idj_app_r in IDN23. destruct IDN23 as (IDN2 & IDN3).
      cbn [okbA]. split.
      + intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| apply KEEP'; apply in_or_app; right; apply in_or_app; right; exact Hb].
        apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply KEEP'; apply in_or_app; left; exact Hb|].
        apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [destruct Hb as [<-|[]]; rewrite ELB; left; reflexivity| apply KEEP'; apply in_or_app; right; apply in_or_app; left; exact Hb].
      + apply nd_app. split; [| split; [| exact NDK]].
        * apply nd_app. split; [exact NDH|]. split; [apply idj_app_r; split; [apply idj_sym; exact IDN1| exact IDH2]|].
          change ([(k', A', cap' + 1)] ++ RB) with ((k', A', cap' + 1) :: RB). apply nd_cons. split; [exact IDN2| exact NDR].
        * apply idj_app_l. split; [exact IDK1|]. apply idj_app_l. split; [exact IDN3| exact IDK3]. }
  destruct BN2 as (BSUB2 & ND2).
  assert (STAT2 : pp_statA m2 gmax canary ws mws cslack GL).
  { apply (H_pparse_kit.ek_ppstat FI AI q lo P st canary POK mws MWL LBK gmax ws cslack GL WSL GLOK [(P + 400, P + 432)]%Z (HB ++ RB) m m2 mws EK).
    - constructor; [| constructor]. left. unfold H_pparse_seg.inP. cbn [fst snd]. lia.
    - exact MWL.
    - exact STAT.
    - destruct STAT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (ev & CE) & _ & CG & CC).
      assert (LOWC : forall a cs, a0_static a (a + Z.of_nat (cells_size cs)) -> a + Z.of_nat (cells_size cs) <= 0x609000 -> rw_cells asegs m a cs -> rw_cells asegs m2 a cs).
      { intros a cs HS HX C. apply (EKC a cs); [right; split; [exact HS| exact HX]| cbn [disjoint_from]; split; [lia| exact I]| exact C]. }
      exists ev. unfold H_vfm_GX.clow. unfold A0_ERRNO, A0_got_ssp, A0_ssp_guard in *.
      split; [apply LOWC; [unfold a0_static; cbn [cells_size csize Nat.add]; split; [lia| env_band]| cbn; lia| exact CE]|].
      split; [apply LOWC; [unfold a0_static; cbn [cells_size csize Nat.add]; split; [lia| env_band]| cbn; lia| exact CG]|].
      apply LOWC; [unfold a0_static; cbn [cells_size csize Nat.add]; split; [lia| env_band]| cbn; lia| exact CC]. }

  destruct FPK as (FPK & _ & SHZK & SHRK).
  pose proof (SHZK SHZ) as SHZ2. pose proof (SHRK SHR) as SHR2. pose proof (FPK ras _ FPC) as FPC2.

  eapply (aj_mono FI AI J).
  { eapply (PP ra q gp u0 u1 u2 s0 s1 (wz P) w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F_ fc m2 s' LB' LBK st P lo gmax canary ws mws cslack GL ta ras);
      [ exact HR2 | exact RF2 | exact FCO | exact AE2 | exact ST3 | exact CLO | exact LO | exact QAL | exact QTOP | exact MI2
      | exact PLB | exact PHI | exact PAL | exact SHWP2 | exact PAR2
      | exact (pp_side_msg t _ _ _ _ A' cap' ok' bs' _ SIDE)
      | exact BSUB2 | exact ND2
      | exact (PBUD s' LB' ta APD)
      | exact WSL | exact WSOK | exact MTOK | exact GMX | exact GLOK | exact GERM | exact STAT2 | exact ZST | exact SHZ2 | exact SHR2 | exact FPC2 | exact TR1 | exact TR2 | reflexivity ]. }
  intros s'' LB'' ms' PO. unfold pappend_post_A. exists s', LB', ta, m2. split; [exact APD|]. split; [exact APXF| exact PO].
Qed.

End W.

