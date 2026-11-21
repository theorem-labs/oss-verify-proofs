(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps Harness CMonad CMonadX ProgAC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface AUri_kit Stdio_kit CProto CProtoX.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2ABlob UwAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import U2AObj U2AClient U2AIface U2AGlue U2AIfaceS InfABase InfAIface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2cA_glue.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import U1AGlue U2cA_pre U2cA_inv U2cA_tail U2cA HarnA_walk CPostX AHarnessIface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section Harn.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Notation FB1 F := (mkABlock (ABFake 0) F 64).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis AI_fake_flag : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells asegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Hypothesis AI_fake_release : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
Hypothesis SM0 : SM0_stmt AI fflag rng_fs.
Hypothesis SM2 : SM2_stmt AI fflag rng_fs.
Hypothesis INIT : inflateInit_stmtA AI.
Hypothesis INF_W : inflate_stmtA AI rng_fs true.
Hypothesis INF_N : inflate_stmtA AI rng_fs false.
Hypothesis END : forall withwin, inflateEnd_stmtA AI withwin.
Hypothesis OBC : exists iv, In iv CI /\ fst iv <= A_OUTBUF /\ A_OUTBUF + 262144 <= snd iv.
Hypothesis VCL : exists iv, In iv CI /\ fst iv <= 141152 /\ 141160 <= snd iv.
Hypothesis TABC1 : exists iv, In iv CI /\ fst iv <= 141376 /\ 152288 <= snd iv.
Hypothesis TABC2 : exists iv, In iv CI /\ fst iv <= 149216 /\ 149568 <= snd iv.
Hypothesis CI_LO : forall iv, In iv CI -> 32768 <= fst iv.

Theorem harness_closed : fuzz_oneA_stmt AI rng_fs.
Proof.
  unfold fuzz_oneA_stmt.
  intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB D payload lo rstk
         AH LBHB PAT PBY PFO D16 N26 HINV ST LOC LOS SP0 SP16 RCL RGLO RGHI RGRLO ES0 MI FRM0 TPE EA0 EA1 ERA HUL RSTK RIMG RISH RFS RRNG OK.
  subst a0 a1.
  set (n := zlength payload) in *. set (SPA := bv_unsigned sp - 96 - bv_unsigned sp mod 32).
  assert (N0 : 0 <= n) by (unfold n, zlength; lia).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP & _).
  unfold AHARNESS_STACK in LOS.
  assert (SPAB : bv_unsigned sp - 112 <= SPA <= bv_unsigned sp - 96 /\ SPA mod 32 = 0) by (unfold SPA; Z.div_mod_to_equations; lia).
  assert (SPTOP : bv_unsigned sp + 32 <= al_top L).
  { unfold al_top. pose proof (PlacementSearch.page_round_up_Z_ge (al_sp0 L - 0xa0)) as X. lia. }
  assert (SPT : bv_unsigned sp + 16 < KEND) by (unfold KEND; lia).
  assert (LOSH : lo <= bv_unsigned sp - H_STACK) by (unfold H_STACK, UC_STACK; lia).
  assert (RSTK' : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
  assert (USPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
  destruct HINV as (TSH & VSH & SHOB & OBB).
  destruct HUL as (UI0 & UIN1 & UIN2 & UF1 & UF2).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as ART. unfold artcells in ART. destruct ART as (_ & GOT & _ & _ & SHB & SUAR & _).
  eapply implMAC_evtF.
  { eapply (h_pre ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n lo SPA RNG LOSH LOC SP16 SPT eq_refl RSTK' RIMG);
      [exact ST| exact MI| exact GOT| exact SHB| exact (u2_img_of_aheap AI _ _ _ _ _ AH)| exact SUAR]. }
  cbv beta. intros ms1 (m1 & jA & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
  assert (AH1 : AHEAP AI L RNG (aps_m s) LB m1).
  { eapply (AI_frame AI _ _ _ _ m m1 _ AH MU1 WM1). constructor; [cbn [fst snd]; apply acr_stack; lia| constructor]. }
  assert (AG1 : magree asegs (fun a => outside [(bv_unsigned sp - 112, bv_unsigned sp)] a) m m1) by exact (magree_of_munch asegs _ m m1 MU1 WM1).
  assert (NOFAKE : forall c Fx nx, ~ In (mkABlock (ABFake c) Fx nx) LB).
  { intros c Fx nx IN. destruct (LBHB _ IN) as (p & A & k & E). discriminate E. }
  pose proof SM0 as SM0'. unfold SM0_stmt, sm_stmt in SM0'.
  eapply implMAC_evtF.
  { unfold ASM0. eapply SM0';
      [exact AH1| intros Fa na Fb nb X _; exfalso; exact (NOFAKE _ _ _ X)| exact MI1| rewrite USPA; exact STL1| exact LOC| rewrite USPA; unfold SM_STACK; lia| rewrite USPA; lia
      | exact TPE| exact RSTK| exact RIMG| exact RFS]. }
  cbv beta. unfold sm_post. rewrite USPA.
  intros ms2 (F1 & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & j0 & j1 & j2 & junk
              & -> & MI2 & STL2 & PRES & AH2 & F128 & FBK & FTOP & FF2 & FSH2 & RF & RSF).
  change (64 / 8) with 8 in RSF. rewrite shadE in RSF.
  pose proof (ablk_lin _ _ FBK) as (FL1 & FL2 & FL3 & FL4). unfold AIMG_HI in FL1.
  assert (F8 : F1 mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (FIN2 : In (FB1 F1) (FB1 F1 :: LB)) by (left; reflexivity).
  assert (SUB2 : forall b, In b LB -> In b (FB1 F1 :: LB)) by (intros b Hb; right; exact Hb).
  assert (FNI : ~ In (FB1 F1) LB) by apply NOFAKE.
  assert (FRB2 : rw_cells asegs m2 (bv_unsigned sp + -64) (HFRB ra s0 s1 s2 s3 s4 s5 s6)).
  { eapply aheap_pres_rw_cells; [exact PRES| exact FRB1|]. left. left. unfold HFRB. cbn [cells_size csize Nat.add]. lia. }
  assert (FRA2 : rw_cells asegs m2 SPA [CB 32 jA]).
  { eapply aheap_pres_rw_cells; [exact PRES| exact FRA1|]. left. left. cbn [cells_size csize Nat.add]. lia. }
  assert (STG2 : stk asegs m2 (SPA + 32) (bv_unsigned sp + -64)) by (eapply aheap_pres_stk; [exact PRES| exact STG1| lia| lia]).
  replace (ret_pc (Z_to_bv 64 0x8c980)) with (Z_to_bv 64 0x8c980) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* uncompress loads the shadow base through the GOT, so h_hdr takes the runtime cells of m2 *)
  pose proof (AI_rtcells AI _ _ _ _ _ AH2) as ART2. unfold artcells in ART2. destruct ART2 as (_ & GOT2 & _ & _ & SHB2 & _).
  eapply implMAC_evtF.
  { eapply (h_hdr ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n lo SPA RNG LOSH LOC SP16 SPT eq_refl RSTK' RIMG F1 (fflag L 0 F1) F128 FBK RF RSF);
      [exact STL2| exact MI2| exact GOT2| exact SHB2| exact FRA2| exact FF2| exact FSH2| unfold n in *; lia]. }
  cbv beta. intros ms3 (m3 & y5 & y6 & y7 & y14 & j16 & j8 & -> & MU3 & WM3 & MI3 & STL3 & WF3 & FRA3 & FH3 & FFL3 & FSH3 & FDL3).
  (* uncompress's 48-byte frame at SPA - 48: [sp+0; sourceLen; got; s1; s0; ra] *)
  assert (USPW : bv_unsigned (Z_to_bv 64 (SPA + -48)) = SPA + -48) by (apply unsigned_lit; lia).
  pose proof WF3 as WFx. unfold WFR in WFx.
  rw_split WFx 1%nat WLO3 WR1. rw_split WR1 1%nat SLC3 WR2. rw_split WR2 1%nat DLC3 WTOP3.
  unfold h_hdrW in MU3.
  set (SHF := Z.shiftr F1 3 + 2147450880) in *.
  assert (BSF : 2148285440 <= SHF /\ SHF + 8 <= 17594333495296)
    by (unfold SHF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  assert (AG3 : magree asegs (fun a => outside [(SPA - 48, SPA + 32); (F1, F1 + 64); (SHF, Z.shiftr F1 3 + 2147450888)] a) m2 m3)
    by exact (magree_of_munch asegs _ m2 m3 MU3 WM3).
  assert (AH3 : AHEAP AI L RNG (aps_m s) (FB1 F1 :: LB) m3).
  { eapply (AI_frame AI _ _ _ _ m2 m3 _ AH2 MU3 WM3).
    constructor; [cbn [fst snd]; apply acr_stack; lia|].
    constructor; [cbn [fst snd]; eapply (acr_fake AI _ 0 F1 64); [exact FIN2| lia| lia]|].
    constructor; [cbn [fst snd]; replace (Z.shiftr F1 3 + 2147450888) with (Z.shiftr F1 3 + 2147450880 + 8) by lia;
                  apply (acr_fake_sh AI _ 0 F1 64 F1 8); [exact FIN2| exact F8| lia| lia| lia]| constructor]. }
  assert (FRB3 := FRB2). eapply rw_cells_transport in FRB3; [| exact MU3| exact WM3| unfold HFRB, SHF; cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia].
  assert (STG3 : stk asegs m3 (SPA + 32) (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact STG2| exact MU3| exact WM3| unfold SHF; cbn [disjoint_from]; repeat split; try exact I; lia]).
  assert (LBH : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)).
  { intros b Hb. destruct (LBHB _ Hb) as (p & A & k & ->). destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hb) as (_ & (X & _) & _). exact X. }
  assert (LBH1 : forall b, In b (FB1 F1 :: LB) -> ablk (ab_addr b) (ab_addr b + ab_size b)) by (intros b [<-|Hb]; [exact FBK| exact (LBH _ Hb)]).
  assert (PAY : (exists pd, In (HB pd D n) LB /\ 0 < n) \/ (n = 0 /\ D = 0x60aca0)).
  { destruct PAT as [(p & PI & PN)|(-> & ->)]; [left; exists p; split; [exact PI| exact PN]| right; split; reflexivity]. }
  assert (PAY1 : (exists pd, In (HB pd D n) (FB1 F1 :: LB) /\ 0 < n) \/ (n = 0 /\ D = 0x60aca0)).
  { destruct PAY as [(p & PI & PN)|X]; [left; exists p; split; [right; exact PI| exact PN]| right; exact X]. }
  assert (N26' : 0 <= n < 67108864) by lia.
  assert (PLEN : Z.of_nat (length payload) = n) by reflexivity.
  assert (US3 : ustatics D payload m3).
  { eapply (ustatics_agree sp D F1 n payload [] PLEN N26' ltac:(cbn; lia));
      [| eapply (ustatics_agree sp D F1 n payload [] PLEN N26' ltac:(cbn; lia));
         [| eapply (ustatics_agree sp D F1 n payload [] PLEN N26' ltac:(cbn; lia)); [| exact (conj VSH (conj TSH (conj OBB (conj SHOB PBY))))]]].
    - eapply magree_mono; [exact AG3|]. intros a U. cbn [outside].
      pose proof (uset_below AI L RNG sp m s LB D F1 n payload [] AH PAY N26' ltac:(cbn; lia) a U).
      pose proof (uset_outside_fake AI L sp LB D F1 n payload [] PAY D16 N26' ltac:(cbn; lia) RNG _ (FB1 F1 :: LB) m2 0 F1 64 a AH2 SUB2 FIN2 FBK U).
      pose proof (uset_outside_fsh sp LB D F1 n payload [] LBH PAY N26' ltac:(cbn; lia) F1 64 a FBK F8 ltac:(lia) ltac:(reflexivity) U) as X. change (64 / 8) with 8 in X.
      fold SHF in X. repeat split; try exact I; lia.
    - intros a Ha U. apply PRES; [exact Ha|]. apply (uset_client AI sp LB D F1 n payload [] PAY N26' OBC VCL TABC1 TABC2 ltac:(cbn; lia)); [auto| exact U].
    - eapply magree_mono; [exact AG1|]. intros a U. cbn [outside].
      pose proof (uset_below AI L RNG sp m s LB D F1 n payload [] AH PAY N26' ltac:(cbn; lia) a U). repeat split; try exact I; lia. }
  pose proof US3 as (VSH3 & TSH3 & OBB3 & SHOB3 & PBY3).
  (* uncompress2's destLen (&got = SPA - 32) and sourceLen (SPA - 40) are both on uncompress's stack
     frame now, so their shadow bytes come from the clean stack region, as the one 1.3.1 sourceLen slot did *)
  pose proof (shclean_hull _ _ _ _ _ (rclean_shclean _ _ RCL)) as (HU1 & HU2 & HU3 & HU4 & HU5 & HU6). unfold KEND in HU6.
  assert (SHSTK : forall X, X mod 8 = 0 -> SPA + -48 <= X <= SPA + -8 ->
            shadow_bytes m3 (Z.shiftr X 3 + 2147450880) (Z.shiftr X 3 + 2147450880 + 1) (fun _ => 0)).
  { intros X X8 XB.
    assert (ESW : shad (X + 8) = shad X + 1) by (rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    assert (SHS0 : shadow_bytes m (Z.shiftr X 3 + 2147450880) (Z.shiftr X 3 + 2147450880 + 1) (fun _ => 0)).
    { rewrite <- shadE, <- ESW. eapply (unpoisoned_core_zero m (r_lo rstk) (r_hi rstk)); [exact (shclean_unpoisoned _ _ _ _ _ (rclean_shclean _ _ RCL))| lia| lia| exact X8| Z.div_mod_to_equations; lia| lia]. }
    assert (BSW : 2147450880 <= Z.shiftr X 3 + 2147450880 /\ Z.shiftr X 3 + 2147450880 + 1 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (SHSEP : SHF + 8 <= Z.shiftr X 3 + 2147450880)
      by (unfold SHF; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; pose proof LOSH as LOSH'; unfold H_STACK, UC_STACK in LOSH'; Z.div_mod_to_equations; lia).
    eapply shadow_bytes_munch; [| exact MU3| cbn [disjoint_from]; pose proof FBK as FBK'; unfold ablk, AIMG_HI, KLS in FBK';
                                             pose proof LOSH as LOSH'; unfold H_STACK, UC_STACK in LOSH'; repeat split; try exact I; lia].
    eapply (stk_sh_pres AI LB SPA m1 m2 X 1); [exact PRES| exact X8| lia| lia|].
    eapply shadow_bytes_munch; [exact SHS0| exact MU1| cbn [disjoint_from]; pose proof LOSH as LOSH'; unfold H_STACK, UC_STACK in LOSH'; repeat split; try exact I; lia]. }
  assert (RSSTK : forall X, X mod 8 = 0 -> SPA + -48 <= X <= SPA + -8 -> rng RNG (Z.shiftr X 3 + 2147450880) 1).
  { intros X X8 XB. unfold rrng in RRNG. eapply rng_sub'; [exact RRNG|]. rewrite <- shadE.
    assert (ESW : shad (X + 8) = shad X + 1) by (rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    pose proof (shad_mono (r_rlo rstk) X ltac:(lia)). pose proof (shad_mono (X + 8) (r_rhi rstk) ltac:(lia)). lia. }
  assert (PFACTS : unpoisoned m3 D (D + n) /\ rng RNG D n /\ rng RNG (Z.shiftr D 3 + 2147450880) (n / 8 + 1)).
  { destruct PAY1 as [(pd & PDI & NPOS)|(N0' & DE)].
    - destruct (AI_block AI _ _ _ _ _ _ _ _ AH3 PDI) as (_ & (PBK & _) & RDB & _ & ABS & _ & _ & (RLO & RHI & RL1 & RL2 & RL3 & RL4 & RL5 & _)).
      pose proof (ablk_lin _ _ PBK) as (PL1 & PL2 & PL3 & PL4).
      split; [apply ablock_unpoisoned; [exact ABS| Z.div_mod_to_equations; lia| lia| lia| lia]|]. split; [exact RDB|].
      eapply rng_sub'; [exact RL5|]. rewrite shadE. unfold shlen. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      clear - RL1 RL2 RL3 RL4 PL2 NPOS. Z.div_mod_to_equations. lia.
    - rewrite N0', DE. split; [split; [lia| split; [lia| intros G HG; exfalso; lia]]|].
      split; [eapply rng_sub'; [exact RIMG| lia]|]. change (Z.shiftr 6335648 3 + 2147450880) with 2148242836. change (0 / 8 + 1) with 1.
      eapply rng_sub'; [exact RISH| lia]. }
  destruct PFACTS as (UNP3 & RD & RSD).
  assert (ROB : rng RNG A_OUTBUF 262144) by (unfold A_OUTBUF; eapply rng_sub'; [exact RIMG| lia]).
  assert (RSOB : rng RNG 2148242840 32768) by (eapply rng_sub'; [exact RISH| lia]).
  (* uncompress keeps s0 = destLen = F1 + 32, a fake-frame address below sp, so the unwind chain
     from uncompress2 stops at once (HU lists [..; 0x8cfbc], the return into uncompress) *)
  assert (UC3 : forall k, (2 <= k)%nat -> uchain m3 (al_top L) AMALLOC_PC (SPA + -48) (bv_unsigned (Z_to_bv 64 (F1 + 32))) k []).
  { intros k _. apply uchain_data. rewrite unsigned_lit by lia. lia. }
  assert (URA : bv_unsigned (Z_to_bv 64 0x8d00c) = 0x8d00c) by (apply unsigned_lit; lia).
  assert (ESLp : SPA + -40 = bv_unsigned (Z_to_bv 64 (SPA + -48)) + 8) by (rewrite USPW; lia).
  pose proof (uc_body AI fflag rng_fs AI_fake_flag AI_fake_release SM2 INIT rng_fs_mono INF_W INF_N END L RNG
                      (Z_to_bv 64 0x8d00c) (Z_to_bv 64 (SPA + -48)) gp tp (Z_to_bv 64 (F1 + 32)) (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 F1) (Z_to_bv 64 n) (Z_to_bv 64 D) (Z_to_bv 64 SHF)
                      (Z_to_bv 64 F1) s7 s8 s9 s10 s11 F fc m3 s (FB1 F1 :: LB) D F1 lo n (SPA + -48 - 160 - (SPA + -48) mod 32) payload []
                      (SPA + -40) ESLp) as UCB.
  rewrite USPW, URA in UCB. replace (SPA + -48 + 16) with (SPA + -32) in UCB by lia.
  eapply implMAC_post_evtF.
  { eapply UCB;
      [exact AH3| exact FIN2| exact F128| exact FBK| exact LBH1
      | intros Fa na Fb nb [E|E] [E'|E']; [congruence| exfalso; exact (NOFAKE _ _ _ E')| exfalso; exact (NOFAKE _ _ _ E)| exfalso; exact (NOFAKE _ _ _ E)]
      | intros Fx nx [E|E]; [discriminate E| exact (NOFAKE _ _ _ E)]
      | exact DLC3| exact SLC3| apply SHSTK; [Z.div_mod_to_equations; lia| lia]| apply SHSTK; [Z.div_mod_to_equations; lia| lia]| exact RF
      | apply RSSTK; [Z.div_mod_to_equations; lia| lia]| apply RSSTK; [Z.div_mod_to_equations; lia| lia]
      | exact PAY1| exact PBY3| exact PFO| exact PLEN| exact D16| exact N26'| exact UNP3| exact RD| exact RSD| exact OBB3| exact SHOB3| exact OBC| exact ROB| exact RSOB
      | exact VSH3| exact TSH3| exact VCL| exact TABC1| exact TABC2| exact STL3| exact LOC| unfold UC_STACK; lia| Z.div_mod_to_equations; lia| lia| exact MI3| exact TPE
      | reflexivity| unfold AMALLOC_PC; lia| rewrite unsigned_lit by lia; lia| exact UC3| cbn [length]; lia| exact UI0| exact UIN1| exact UIN2| exact UF1| exact UF2| exact RSTK| exact RIMG| exact RISH| exact RFS| exact OK]. }
  intros r s' RNG' ms' (-> & FIN). unfold uc_final in FIN. rewrite USPW in FIN. try replace (SPA + -48 + 16) with (SPA + -32) in FIN by lia.
  destruct FIN as (FPL & av & q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4 & -> & MI4 & ST4 & RS4 & AH4 & PF4 & (obr4 & OBB4) & (slv4 & SLC4) & (dlv4 & DLC4)).
  (* uncompress2 may write only got (SPA - 32) and sourceLen (SPA - 40) of uncompress's frame; the
     frame's other slots, the whole fake block F1 (destLen = F1 + 32 included) and its shadow are kept *)
  assert (HK : forall a, (SPA + -24 <= a < 2^47 \/ SPA + -48 <= a < SPA + -40 \/ F1 <= a < F1 + 64 \/ SHF <= a < SHF + 8) ->
               uc_PF AI (Z_to_bv 64 (SPA + -48)) (FB1 F1 :: LB) (SPA + -40) a).
  { intros a KP. unfold uc_PF, uc_WRf. rewrite USPW. split.
    - destruct KP as [K|[K|[K|K]]].
      + left. lia.
      + left. lia.
      + right. right. left. exists (FB1 F1). split; [exact FIN2| cbn [ab_addr ab_size]; lia].
      + right. right. right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
        right. right. exists 0, F1, 64. split; [exact FIN2|]. unfold ASHOFF. unfold SHF in K. revert K. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
        intros K. Z.div_mod_to_equations. lia.
    - intros (iv & Hiv & Hr). cbn [In] in Hiv. unfold A_OUTBUF in Hiv.
      destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; destruct KP as [K|[K|[K|K]]]; try lia;
        (apply (ablk_clear_band _ _ a FBK); [unfold KLS; lia| lia]). }
  assert (KX : forall A N, (forall a, A <= a < A + N -> SPA + -24 <= a < 2^47 \/ SPA + -48 <= a < SPA + -40 \/ F1 <= a < F1 + 64 \/ SHF <= a < SHF + 8) ->
               forall a, A <= a < A + N -> uc_PF AI (Z_to_bv 64 (SPA + -48)) (FB1 F1 :: LB) (SPA + -40) a).
  { intros A N HA a Ha. apply HK. apply HA. exact Ha. }
  assert (FRA4 : rw_cells asegs m4 SPA (HFRA F1 j16)).
  { eapply rw_cells_magree; [exact PF4| exact FRA3|]. apply KX. unfold HFRA; cbn [cells_size csize Nat.add]. intros a Ha. left. lia. }
  assert (FRB4 : rw_cells asegs m4 (bv_unsigned sp + -64) (HFRB ra s0 s1 s2 s3 s4 s5 s6)).
  { eapply rw_cells_magree; [exact PF4| exact FRB3|]. apply KX. unfold HFRB; cbn [cells_size csize Nat.add]. intros a Ha. left. lia. }
  assert (STG4 : stk asegs m4 (SPA + 32) (bv_unsigned sp + -64)).
  { eapply stk_magree; [exact PF4| exact STG3|]. intros a Ha. apply HK. left. lia. }
  assert (FH4 : rw_cells asegs m4 F1 HFHD).
  { eapply rw_cells_magree; [exact PF4| exact FH3|]. apply KX. unfold HFHD; cbn [cells_size csize Nat.add]. intros a Ha. right. right. left. lia. }
  assert (FDL4 : rw_cells asegs m4 (F1 + 32) [C8 (Z_to_bv 64 262144)]).
  { eapply rw_cells_magree; [exact PF4| exact FDL3|]. apply KX. cbn [cells_size csize Nat.add]. intros a Ha. right. right. left. lia. }
  assert (FFL4 : rw_cells asegs m4 (F1 + 56) [C8 (Z_to_bv 64 (fflag L 0 F1))]).
  { eapply rw_cells_magree; [exact PF4| exact FFL3|]. apply KX. cbn [cells_size csize Nat.add]. intros a Ha. right. right. left. lia. }
  assert (FSH4 : rw_cells asegs m4 SHF HFSH).
  { eapply rw_cells_magree; [exact PF4| exact FSH3|]. apply KX. unfold HFSH; cbn [cells_size csize Nat.add]. intros a Ha. right. right. right. lia. }
  assert (WLO4 : rw_cells asegs m4 (SPA + -48) [CB 8 j8]).
  { eapply rw_cells_magree; [exact PF4| exact WLO3|]. apply KX. cbn [cells_size csize Nat.add]. intros a Ha. right. left. lia. }
  assert (WTOP4 : rw_cells asegs m4 (SPA + -24) [C8 (Z_to_bv 64 SPA); C8 sp; C8 (Z_to_bv 64 0x8ca28)]).
  { eapply rw_cells_magree; [exact PF4| exact WTOP3|]. apply KX. cbn [cells_size csize Nat.add]. intros a Ha. left. lia. }
  assert (WF4 : rw_cells asegs m4 (SPA + -48) [CB 8 j8; C8 slv4; C8 dlv4; C8 (Z_to_bv 64 SPA); C8 sp; C8 (Z_to_bv 64 0x8ca28)]).
  { rw_join WLO4 SLC4 WFa. rw_join WFa DLC4 WFb. rw_join WFb WTOP4 WFj. exact WFj. }
  destruct (AI_fake_flag _ _ _ _ _ 0 F1 64 AH4 FIN2) as (FLC4 & RG & GB & GTOP & GBL & GCI).
  set (FLG := fflag L 0 F1) in *.
  pose proof (ablk_lin _ _ GB) as (GB1 & GB2 & GB3 & GB4). unfold AIMG_HI in GB1.
  assert (GF : FLG + 1 <= F1 \/ F1 + 64 <= FLG).
  { pose proof (GBL (FB1 F1) FIN2) as X. cbn [ab_addr ab_size] in X. exact X. }
  assert (RF' : rng RNG' F1 64) by (eapply rng_fp_le; [exact FPL| exact RF]).
  assert (RSF' : rng RNG' SHF 8) by (eapply rng_fp_le; [exact FPL| exact RSF]).
  assert (RSTK4 : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPL| exact RSTK']).
  assert (RIMG4 : rng_aimg RNG') by (eapply rng_fp_le; [exact FPL| exact RIMG]).
  assert (RFRM4 : rng RNG' (SPA - 48) 80) by (eapply rng_sub'; [exact RSTK4| lia]).
  replace (ret_pc (Z_to_bv 64 0x8d00c)) with (Z_to_bv 64 0x8d00c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply evtF_mono.
  { eapply (h_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n lo SPA RNG' LOSH LOC SP16 SPT eq_refl RSTK4 RIMG4 F1 FLG F128 FBK RF' RSF' RFRM4 GB GF RG);
      [exact ST4| exact STG4| exact MI4| exact WF4| exact FRA4| exact FRB4| exact FH4| exact FDL4| exact FFL4| exact FLC4| exact FSH4]. }
  cbv beta. intros ms5 (mp & m5 & z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & -> & MUp & WMp & MIp & MU5 & WM5 & MI5 & ST5 & FLC5).
  assert (AHp : AHEAP AI L RNG' (aps_m s') (FB1 F1 :: LB) mp).
  { eapply (AI_frame AI _ _ _ _ m4 mp _ AH4 MUp WMp).
    constructor; [cbn [fst snd]; apply (acr_fake_sh AI _ 0 F1 64 F1 8); [exact FIN2| exact F8| lia| lia| lia]|].
    constructor; [cbn [fst snd]; eapply (acr_fake AI _ 0 F1 64); [exact FIN2| lia| lia]| constructor]. }
  assert (EQ5 : m5 = write_to_mem mp (wa FLG) [Z_to_bv 8 0]).
  { apply uc_mem_eq_single; [lia| lia| exact MU5|]. apply uc_byte_of_c1; [exact FLC5| lia]. }
  assert (AH5 : AHEAP AI L RNG' (aps_m s') LB m5).
  { rewrite EQ5. unfold FLG. apply (AI_fake_release L RNG' (aps_m s') LB mp 0 F1 64 AHp). }
  set (HP := fun a => aclient_addr CI LB (bv_unsigned sp) a /\ ~ (0x60acc0 <= a < 0x60acc0 + 262144)).
  assert (TSP : ATOP <= bv_unsigned sp) by lia.
  assert (OUT : forall a, aclient_addr CI LB (bv_unsigned sp) a ->
                  ~ (lo <= a < bv_unsigned sp) /\ ~ (F1 <= a < F1 + 64) /\ ~ (SHF <= a < SHF + 8) /\ a <> FLG /\ 32768 <= a).
  { intros a HC.
    split; [exact (client_outside_stk AI L RNG sp m s LB D F1 n payload [] AH N26' ltac:(cbn; lia) a lo ltac:(lia) HC)|].
    split; [exact (client_outside_blk AI L RNG _ (FB1 F1 :: LB) LB m2 (FB1 F1) (bv_unsigned sp) a AH2 FIN2 FNI SUB2 FBK TSP HC)|].
    split; [exact (client_outside_fsh AI L RNG _ (FB1 F1 :: LB) LB m2 0 F1 64 (bv_unsigned sp) a AH2 FIN2 FNI SUB2 LBH FBK F8 eq_refl ltac:(lia) TSP HC)|].
    split; [exact (client_outside_flag AI L RNG' _ (FB1 F1 :: LB) LB m4 FLG (bv_unsigned sp) a AH4 SUB2 GB GBL GCI TSP HC)|].
    destruct HC as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - lia.
    - pose proof (CI_LO iv Hiv). lia.
    - pose proof (AI_block_bounds AI _ _ _ _ _ b AH Hb) as (X & _). unfold AIMG_HI in X. lia.
    - rewrite shad_div. unfold ASHOFF.
      assert (0 <= a'); [| Z.div_mod_to_equations; lia].
      destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_lo AI iv Hiv); lia|].
      exfalso. exact (NOFAKE _ _ _ Hb'). }
  assert (AGF : magree asegs HP m m5).
  { eapply magree_trans; [| eapply magree_trans; [| eapply magree_trans; [| eapply magree_trans; [| eapply magree_trans]]]].
    - eapply magree_mono; [exact AG1|]. intros a [HC _]. destruct (OUT a HC) as (O1 & _). cbn [outside]. split; [lia| exact I].
    - intros a Ha [HC _]. apply PRES; [exact Ha|]. eapply (aclient_addr_weaken AI LB LB SPA (bv_unsigned sp)); [auto| lia| exact HC].
    - eapply magree_mono; [exact AG3|]. intros a [HC _]. destruct (OUT a HC) as (O1 & O2 & O3 & _). cbn [outside]. unfold SHF in *. repeat split; try exact I; lia.
    - eapply magree_mono; [exact PF4|]. intros a [HC NB]. destruct (OUT a HC) as (O1 & O2 & O3 & O4 & O5). unfold uc_PF, uc_WRf. rewrite USPW. split.
      + eapply (aclient_addr_weaken AI (FB1 F1 :: LB) LB (SPA + -48) (bv_unsigned sp)); [exact SUB2| lia| exact HC].
      + intros (iv & Hiv & Hr). cbn [In] in Hiv. unfold A_OUTBUF in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia.
    - eapply magree_mono; [exact (magree_of_munch asegs _ m4 mp MUp WMp)|]. intros a [HC _]. destruct (OUT a HC) as (O1 & O2 & O3 & _).
      cbn [outside]. repeat split; try exact I; lia.
    - eapply magree_mono; [exact (magree_of_munch asegs _ mp m5 MU5 WM5)|]. intros a [HC _]. destruct (OUT a HC) as (_ & _ & _ & O4 & _).
      cbn [outside]. split; [lia| exact I]. }
  assert (SHP : forall sa sb f, shadow_bytes m sa sb f -> (forall a, sa <= a < sb -> uset D n a /\ 2147450880 <= a) -> shadow_bytes m5 sa sb f).
  { intros sa sb f SB HR. eapply shadow_bytes_magree; [exact AGF| exact SB|]. intros a Ha. destruct (HR a Ha) as [U LOa]. split; [| lia].
    apply (uset_client AI sp LB D F1 n payload [] PAY N26' OBC VCL TABC1 TABC2 ltac:(cbn; lia)); [auto| exact U]. }
  assert (OBB5 : rw_cells asegs m5 0x60acc0 [CB (Z.to_nat 262144) obr4]).
  { unfold A_OUTBUF in OBB4. eapply rw_cells_transport; [eapply rw_cells_transport; [exact OBB4| exact MUp| exact WMp|]| exact MU5| exact WM5|];
      cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia. }
  unfold fuzz_oneA_post. split; [exact FPL|].
  exists z5, z6, z7, z11, z12, z13, z14, z15, z16, z17, z28, z29, z30, z31, F, fc, m5.
  split; [reflexivity|]. split; [lia|]. split; [exact MI5|]. split; [exact FRM0|]. split; [exact ST5|].
  split; [intros a Ha HC NB; exact (AGF a Ha (conj HC NB))|].
  split.
  { intros a Ha. rewrite !shad_div in Ha. unfold ASHOFF in Ha.
    assert (A0 : 0 <= a < 2^64) by (Z.div_mod_to_equations; lia).
    destruct (AGF a A0) as [E _]; [| exact E]. split; [| lia].
    right. right. right. exists (8 * (a - ASHOFF) + 7). split; [left; unfold ASHOFF; Z.div_mod_to_equations; lia|].
    rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
  split; [exact AH5|].
  split; [| exact RS4].
  unfold harness_invA.
  split.
  { unfold u2_tabsh in *. destruct TSH as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10).
    split; [apply (SHP _ _ _ T1); intros a Ha; split; [right; left; lia| lia]|].
    split; [apply (SHP _ _ _ T2); intros a Ha; split; [right; left; lia| lia]|].
    split; [apply (SHP _ _ _ T3); intros a Ha; split; [right; left; lia| lia]|].
    split; [apply (SHP _ _ _ T4); intros a Ha; split; [right; left; lia| lia]|].
    split; [apply (SHP _ _ _ T5); intros a Ha; split; [right; right; left; lia| lia]|].
    split; [apply (SHP _ _ _ T6); intros a Ha; split; [right; right; left; lia| lia]|].
    split; [apply (SHP _ _ _ T7); intros a Ha; split; [right; right; left; lia| lia]|].
    split; [apply (SHP _ _ _ T8); intros a Ha; split; [right; right; left; lia| lia]|].
    split; [apply (SHP _ _ _ T9); intros a Ha; split; [right; right; left; lia| lia]|].
    apply (SHP _ _ _ T10); intros a Ha; split; [right; right; left; lia| lia]. }
  split; [unfold ver_sh in *; apply (SHP _ _ _ VSH); intros a Ha; split; [left; lia| lia]|].
  split; [apply (SHP _ _ _ SHOB); intros a Ha; split; [do 3 right; left; lia| lia]|].
  exists obr4. exact OBB5.
Qed.
End Harn.
End CANSEC1.
