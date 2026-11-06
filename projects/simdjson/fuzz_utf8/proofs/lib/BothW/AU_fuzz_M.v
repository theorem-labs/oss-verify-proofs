(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessU ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg RtCells AProto ABase MonadF AMalloc_iface AAtexit_iface ABytes.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_fuzz_A AU_fuzz_B AU_vutf8 AU_first_A AU_first_M AU_fuzz_F.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac pick_in := (left; reflexivity) + (right; pick_in).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
Ltac box H := lazymatch type of H with ?P => change P with (bx P) in H end.
Ltac ub H T := pose proof H as T; unfold bx in T.
(* [comment removed for export] *)
Ltac xrw H MU WM :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
    lazymatch type of H with rw_cells _ _ ?A ?cs =>
      apply (rw_cells_transport bsegs W mo mn A cs) in H; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul FZRB shcells1 repeat Datatypes.length]; lia] end end.
Ltac xrwc H MU WM CS :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
    lazymatch type of H with rw_cells _ _ ?A ?cs =>
      apply (rw_cells_transport bsegs W mo mn A cs) in H; [| exact MU| exact WM| rewrite CS; cbn [disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ]; lia] end end.
Ltac xst H MU WM :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
    lazymatch type of H with stk _ _ ?loq ?hiq =>
      apply (stk_transport_disjoint bsegs W mo mn loq hiq) in H; [| exact MU| exact WM| cbn [disjoint_from]; lia] end end.
Ltac ag_of_hpr H := lazymatch type of H with aheap_pres ?CI ?LB ?SP ?m ?m' => change (aheap_pres CI LB SP m m') with (magree bsegs (aclient_addr CI LB SP) m m') in H end.
Ltac xag H AG tac :=
  lazymatch type of AG with magree _ ?P ?mo ?mn =>
    lazymatch type of H with
    | rw_cells _ _ ?A ?cs => apply (rw_cells_magree bsegs P mo mn A cs AG) in H; [| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul FZRB shcells1 repeat Datatypes.length]; intros ? ?; tac]
    | stk _ _ ?loq ?hiq => apply (stk_magree bsegs P mo mn loq hiq AG) in H; [| intros ? ?; tac]
    end end.

(* [comment removed for export] *)
Ltac xall MU WM :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
    repeat match goal with
    | H : rw_cells _ mo ?A ?cs |- _ =>
        apply (rw_cells_transport bsegs W mo mn A cs) in H;
        [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul fst snd FZRB shcells1]; lia]
    | H : stk _ mo ?loq ?hiq |- _ =>
        apply (stk_transport_disjoint bsegs W mo mn loq hiq) in H; [| exact MU| exact WM| cbn [disjoint_from]; lia]
    | H : wr_at _ mo ?A ?n |- _ => apply (wr_at_transport bsegs mo mn A n) in H; [| exact WM]
    end end.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma sh16_of_words : forall m F,
  rw_cells bsegs m (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> rw_cells bsegs m (shad F) (repeat (C1 B00) 16).
Proof. intros m F H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.
Lemma shcells1_all_C1 : forall c, In c shcells1 -> exists v, c = C1 v.
Proof. intros c H. unfold shcells1 in H. cbn [In] in H. repeat (destruct H as [<-|H]; [eexists; reflexivity|]). destruct H. Qed.

Section M.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (fflag : alayout -> Z -> Z -> Z) (rng_fs : alayout -> footprint -> Prop).
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis SM1 : stack_malloc_1_stmt AI fflag rng_fs.
  Hypothesis AI_fake_flag : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
    rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
    /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
    /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
    /\ ~ in_ranges CI (fflag L cls F).
  Hypothesis AI_fake_release : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
    AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).

  (* [comment removed for export] *)
  Variables (L : alayout) (RNG : footprint).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (s : APS) (LB : list ablock) (D : Z) (payload : list Z) (lo : Z).
  Hypothesis AH : AHEAP AI L RNG (aps_m s) LB m0.
  Hypothesis HLB : forall b, In b LB -> exists p A n, b = HB p A n.
  Hypothesis PAY : payload_atA LB D payload.
  Hypothesis BY : bytes_at bsegs m0 D (map (Z_to_bv 8) payload).
  Hypothesis D16 : D mod 16 = 0.
  Hypothesis SZB : zlength payload < 2^26.
  Hypothesis HI : harness_invA m0.
  Hypothesis CLS : client_static s LB m0.
  Hypothesis ST : stk bsegs m0 lo (bv_unsigned sp).
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= bv_unsigned sp - AHARNESS_STACK.
  Hypothesis SPG : bv_unsigned sp + 208 = al_sp0 L.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis MI : mem_inv bsegs m0.
  Hypothesis FRM : frm0 fc.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RFS : rng_fs L RNG.

  Notation SP := (bv_unsigned sp).
  Notation SZ := (zlength payload).
  Let SPA : Z := SP - 192 - (SP - 192) mod 32.
  Notation FB1 F := (mkABlock (ABFake 1) F 128).

  Lemma geom : SP - 208 <= SPA <= SP - 192 /\ SPA mod 32 = 0 /\ SP + 16 <= al_top L /\ al_top L <= 2^47 /\ (ATOP - 160 <= al_bot L <= ATOP + 3936)
               /\ al_bot L + 0x800000 = al_top L /\ 0 <= SZ.
  Proof.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (L1 & L2 & L3 & L4 & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (harness_top L SP SPG ltac:(lia)) as [T1 T2].
    subst SPA. unfold zlength in *. repeat split; try lia; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pag_outside : forall RNGx st LBF mx F a,
    AHEAP AI L RNGx st LBF mx -> In (FB1 F) LBF -> (forall b, In b LB -> In b LBF) -> ablk F (F + 128) ->
    aclient_addr CI LB SP a ->
    (a < lo \/ SP <= a) /\ ~ (F <= a < F + 128) /\ ~ (shad F <= a < shad F + 16).
  Proof.
    intros RNGx st LBF mx F a AHx HF INCL FH Ha. pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
    pose proof geom as (SPAB & SPA32 & TOP & TOP47 & CBOT & LBT & _). unfold AHARNESS_STACK in LOS.
    pose proof (fun b Hb => AI_block_bounds AI _ _ _ _ _ b AHx Hb) as BB. cbv beta in BB.
    pose proof (BB _ HF) as BF. cbn [ab_addr ab_size] in BF.
    unfold AIMG_HI, KHIGH in *. rewrite !shad_div. unfold ASHOFF.
    pose proof LOS as LOS'. pose proof BOT as BOT'.
    destruct Ha as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - clear - X BF LOS' BOT' CBOT FH. Z.div_mod_to_equations. lia.
    - pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. clear - H Hr BF LOS' BOT' CBOT FH. Z.div_mod_to_equations. lia.
    - destruct (HLB _ Hb) as (p & A & N & ->). cbn in Hr.
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AHx (INCL _ Hb) HF ltac:(discriminate)) as DJ. cbn [ab_addr ab_size] in DJ.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AHx (INCL _ Hb)) as (_ & (R1 & R2 & R3 & R4) & _).
      pose proof (ablk_lin _ _ R1) as (R1a & R1b & R1c & R1d). unfold AIMG_HI in R1a. band_ind R1 bR1.
      clear - Hr DJ R1a R1b R1c R2 R3 R4 bR1r bR1hi bR1lo BF LOS' BOT' CBOT FH2 FH3. Z.div_mod_to_equations. lia.
    - assert (A47 : 0 <= a' < 2^47 /\ (ATOP <= a' \/ a' < 7151616)).
      { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [atop_facts; lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia|].
        destruct (HLB _ Hb') as (p & A & N & E'). discriminate. }
      rewrite shad_div. unfold ASHOFF.
      split; [| split].
      + clear - A47 BF LOS' BOT' CBOT. atop_facts. Z.div_mod_to_equations. lia.
      + intros X. eapply (ablk_clear_band _ _ _ FH); [| exact X]. unfold KLS. clear - A47. Z.div_mod_to_equations. lia.
      + clear - A47 BF LOS' BOT' CBOT FH2 FH3. Z.div_mod_to_equations. lia.
  Qed.

  Lemma pag_client : forall LB' sp' a, aclient_addr CI LB SP a -> (forall b, In b LB -> In b LB') -> sp' <= SP -> aclient_addr CI LB' sp' a.
  Proof. intros LB' sp' a Ha INCL LE. eapply aclient_addr_mono_sp; [eapply aclient_addr_mono_lb; [exact Ha| exact INCL]| exact LE]. Qed.

  (* [comment removed for export] *)
  Lemma sh_client : forall LB' sp' F a, In (FB1 F) LB' -> F mod 8 = 0 -> 0 <= F -> shad F <= a < shad F + 16 -> aclient_addr CI LB' sp' a.
  Proof.
    intros LB' sp' F a HIN F8 F0 Ha. right; right; right. exists (F + 8 * (a - shad F)). split.
    - right; right. exists 1, F, 128. split; [exact HIN| lia].
    - rewrite !shad_div in *. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition PW (a : Z) : Prop := aclient_addr CI LB SP a /\ outside client_wr a.

  Definition fzfr (RNGc : footprint) (sc : APS) (LBc : list ablock) (F : Z) (m : amem) (c80 : list cell) : Prop :=
       mem_inv bsegs m /\ stk bsegs m lo (SPA + 32) /\ stk bsegs m (SPA + 80) (SP + -104)
    /\ rw_cells bsegs m (SP + -104) (FZRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ (exists l72, rw_cells bsegs m (SPA + 32) [CB 8 l72]) /\ rw_cells bsegs m (SPA + 40) c80
    /\ (exists l64, rw_cells bsegs m (SPA + 56) [C8 (Z_to_bv 64 SZ); CB 8 l64; C8 (Z_to_bv 64 F)])
    /\ rw_cells bsegs m F [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1f51a); C8 (Z_to_bv 64 0xb131c)]
    /\ rw_cells bsegs m (F + 120) [C8 (Z_to_bv 64 (fflag L 1 F))]
    /\ rw_cells bsegs m (shad F) shcells1
    /\ client_img m /\ client_sh m /\ client_static sc LBc m
    /\ magree bsegs PW m0 m
    /\ AHEAP AI L RNGc (aps_m sc) (FB1 F :: LBc) m
    /\ F mod 128 = 0 /\ ablk F (F + 128) /\ F + 128 <= ATOP /\ rng RNG F 128 /\ rng RNG (shad F) 16.

  Lemma payload_bounds : 0 <= D /\ D + SZ <= ATOP.
  Proof.
    destruct PAY as [(pD & HIN & _)|[EP ED]].
    - destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN) as (_ & (B1 & B2 & B3 & B4) & _). pose proof (ablk_lin _ _ B1) as (B1a & B1b & B1c & B1d). lia.
    - rewrite ED, EP. unfold AEMPTY, zlength. cbn. atop_facts. lia.
  Qed.

  Lemma payload_pos : 0 < D.
  Proof.
    destruct PAY as [(pD & HIN & _)|[EP ED]].
    - destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN) as (_ & (B1 & B2 & B3 & B4) & _). pose proof (ablk_lin _ _ B1) as (B1a & B1b & B1c & B1d). unfold AIMG_HI in B1a. lia.
    - rewrite ED. unfold AEMPTY. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_head : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    evtF bsegs RNG (fun ms => exists (F : Z) (m : amem) (l80 l88 : list byte) (x1 x5 x6 x7 y10 y11 y12 y13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        ms = MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) y10 y11 y12 y13 x14 x15 x16 x17
                     s2 (Z_to_bv 64 D) (Z_to_bv 64 F) s5 s6 s7 s8 (Z_to_bv 64 ASHOFF) (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) x28 x29 x30 x31)
                FR (Z_to_bv 64 (match aps_cl s with Some _ => 0xb143c | None => 0xb1648 end)) fc None m (seg_rom bsegs)
        /\ fzfr RNG s LB F m [CB 8 l80; CB 8 l88])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 SZ) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 AFUZZ_ENTRY) fc None m0 (seg_rom bsegs)).
  Proof.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
    pose proof geom as (SPAB & SPA32 & TOP & TOP47 & CBOT & LBT & SZ0).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold AHARNESS_STACK in LOS. pose proof CBOT as CBOT'. atop_facts.
    pose proof payload_bounds as DB.
    destruct HI as [IG0 USH0]. pose proof IG0 as (GSU & _ & _).
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH) as (GOT0 & RIC0 & REAL0 & SHB0 & SUA0 & INI0 & LAY0).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (f_pro ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc D SZ lo SPA);
        first [exact ST| exact MI| exact GOT0| exact SHB0| exact GSU| exact SUA0| reflexivity| exact RI| exact SP16| eapply rng_sub'; [exact RSTK| lia]| unfold AHARNESS_STACK in *; lia]. }
    cbv beta. intros ms1 (m1 & ya1 & ya2 & l32 & l80 & l88 & l64 & l72 & -> & MU1 & WM1 & MI1 & FRB1 & ST1 & STG1 & FRA1).
    assert (NOF1 : forall F' n', ~ In (mkABlock (ABFake 1) F' n') LB) by (intros F' n' Hin; destruct (HLB _ Hin) as (p' & A' & n'' & E'); discriminate).
    assert (AH1 : AHEAP AI L RNG (aps_m s) LB m1).
    { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [left; left; cbn; lia| constructor]. }
    assert (FW1 : Forall wfar [(SP - 208, SP)]) by (constructor; [apply wfar_high; cbn; lia| constructor]).
    pose proof (client_img_munch32 _ _ _ IG0 MU1 WM1 FW1) as IG1. pose proof (client_sh_munch32 _ _ _ USH0 MU1 FW1) as USH1.
    assert (CLS1 : client_static s LB m1).
    { eapply client_static_munch32; [exact CLS| exact MU1| exact WM1| exact FW1|]. intros p' V' _ HIN'.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN') as (_ & (Q1 & Q2 & Q3 & Q4) & _). cbn [disjoint_from]. lia. }
    clear FW1. box MU1. box WM1.
    (* [comment removed for export] *)
    destruct (stk_split bsegs _ lo SPA (SPA + 32) ST1 ltac:(lia)) as [STL1 STU1]. clear ST1.
    eapply evtF_cut.
    { eapply SM1; first [exact AH1| exact NOF1| exact MI1| exact BOT| exact TP| exact RSTK| exact RI| exact RFS| rewrite unsigned_lit by lia; first [exact STL1| unfold SM1_STACK; lia]]. }
    cbv beta. intros ms2 PO. destruct PO as (F & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & j0 & j1 & j2 & junk & -> & MI2 & ST2 & HPR2 & AH2 & F128 & FH & FC & FFC & SHW & RF & RSF).
    rewrite ?unsigned_lit in ST2, HPR2 by lia. retlit.
    assert (INCL2 : forall b, In b LB -> In b (FB1 F :: LB)) by (intros b Hb; right; exact Hb).
    assert (AG2 : magree bsegs (aclient_addr CI LB SP) m0 m2).
    { ub MU1 T1. ub WM1 T2. eapply magree_trans.
      - eapply magree_mono; [eapply magree_of_munch; [exact T1| exact T2]|]. intros a Ha. cbn.
        destruct (pag_outside _ _ _ _ F a AH2 ltac:(left; reflexivity) INCL2 FH Ha) as (O1 & _). lia.
      - ag_of_hpr HPR2. eapply magree_mono; [exact HPR2|]. intros a Ha. eapply pag_client; [exact Ha| intros b Hb; exact Hb| lia]. }
    clear MU1 WM1.
    assert (CLS2 : client_static s LB m2) by (eapply (client_static_pres AI IMG_CI); [exact HPR2| exact CLS1]).
    assert (USH2 : client_sh m2) by (eapply (client_sh_pres AI IMG_CI); [exact HPR2| exact USH1]).
    assert (IG2 : client_img m2) by (eapply (client_img_pres AI IMG_CI); [exact IG1| exact HPR2| exact AH2| exact MI2]).
    ag_of_hpr HPR2. xag FRB1 HPR2 ltac:(left; lia). xag STU1 HPR2 ltac:(left; lia). xag STG1 HPR2 ltac:(left; lia). xag FRA1 HPR2 ltac:(left; lia). clear STL1 MI1 AH1 CLS1 USH1 IG1 HPR2.
    pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1. band_ind FH bFH.
    assert (BSF : 2148328448 <= shad F /\ shad F + 16 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    pose proof (stk_merge bsegs m2 lo SPA (SPA + 32) ST2 STU1 ltac:(lia)) as ST2'. clear ST2 STU1.
    (* [comment removed for export] *)
    assert (FSP : rw_cells bsegs m2 F [C8 j0; C8 j1; C8 j2] /\ rw_cells bsegs m2 (F + 120) [C8 (Z_to_bv 64 (fflag L 1 F))]).
    { change [C8 j0; C8 j1; C8 j2; CB 96 junk; C8 (Z_to_bv 64 (fflag L 1 F))] with ([C8 j0; C8 j1; C8 j2] ++ [CB 96 junk] ++ [C8 (Z_to_bv 64 (fflag L 1 F))]) in FFC.
      apply (proj1 (rw_cells_app _ _ _ _ _)) in FFC. destruct FFC as [X1 X2]. apply (proj1 (rw_cells_app _ _ _ _ _)) in X2. destruct X2 as [_ X3].
      cbn [cells_size csize Nat.add] in X3. split; [exact X1|]. replace (F + 120) with (F + Z.of_nat 24 + Z.of_nat 96) by lia. exact X3. }
    destruct FSP as [HDR2 FLP2]. clear FFC.
    (* [comment removed for export] *)
    assert (GRD2 : exists g gi, rw_cells bsegs m2 AVEC_GUARD [C1 g; C1 gi] /\ (g = Z_to_bv 8 0 \/ g = Z_to_bv 8 1)
                   /\ (if bv_eqb g (Z_to_bv 8 0) then 0xb1648 else 0xb143c) = match aps_cl s with Some _ => 0xb143c | None => 0xb1648 end).
    { pose proof CLS2 as (_ & _ & CLS2'). destruct (aps_cl s) as [p|].
      - destruct CLS2' as (V2 & HINV2 & _ & _ & G2 & _). exists (Z_to_bv 8 1), (Z_to_bv 8 1). split; [exact G2|]. split; [right; reflexivity| reflexivity].
      - destruct CLS2' as (_ & G2 & _). exists (Z_to_bv 8 0), (Z_to_bv 8 0). split; [exact G2|]. split; [left; reflexivity| reflexivity]. }
    destruct GRD2 as (g & gi & GRD2 & GV & GPC).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply f_hdr with (lo := lo) (SPA := SPA) (g := g) (gi := gi);
        first [exact FRA1| exact MI2| exact HDR2| apply sh16_of_words; exact SHW| exact GRD2| exact GV| exact FH| exact F128| exact RF| exact RSF
              | reflexivity| exact RI| exact SP16| eapply rng_sub'; [exact RSTK| lia]| unfold AHARNESS_STACK in *; lia]. }
    cbv beta. intros ms3 (m3 & y10 & y11 & y12 & y13 & y14 & -> & MU3 & WM3 & MI3 & FRA3 & HDR3 & SH3).
    rewrite GPC.
    assert (INF : In (FB1 F) (FB1 F :: LB)) by (left; reflexivity).
    assert (FW3 : Forall wfar [(SPA + 72, SPA + 80); (F, F + 24); (shad F, shad F + 12)]) by fw_far.
    pose proof (client_img_munch32 _ _ _ IG2 MU3 WM3 FW3) as IG3. pose proof (client_sh_munch32 _ _ _ USH2 MU3 FW3) as USH3.
    assert (CLS3 : client_static s LB m3).
    { eapply client_static_munch32; [exact CLS2| exact MU3| exact WM3| exact FW3|]. intros p' V' _ HIN'.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 ltac:(right; exact HIN')) as (_ & (Q1 & Q2 & Q3 & Q4) & _).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(right; exact HIN') INF ltac:(discriminate)) as D0. cbn in D0.
      pose proof (ablk_lin _ _ Q1) as (Q1a & Q1b & Q1c & Q1d). unfold AIMG_HI in Q1a. band_ind Q1 bQ1. cbn [disjoint_from]. lia. }
    clear IG2 USH2 CLS2 FW3.
    xrw FRB1 MU3 WM3. xrw FLP2 MU3 WM3. pose proof ST2' as STL3. pose proof STG1 as STG3. xst STL3 MU3 WM3. xst STG3 MU3 WM3.
    assert (AH3 : AHEAP AI L RNG (aps_m s) (FB1 F :: LB) m3).
    { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
      constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
      - left; left. lia.
      - right; left. exists (FB1 F). split; [left; reflexivity| cbn; lia].
      - right; right. right; right. exists 1, F, 128. split; [left; reflexivity|].
        rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    assert (AG3 : magree bsegs (aclient_addr CI LB SP) m0 m3).
    { eapply magree_trans; [exact AG2|]. eapply magree_mono; [eapply magree_of_munch; [exact MU3| exact WM3]|]. intros a Ha. cbn.
      destruct (pag_outside _ _ _ _ F a AH2 ltac:(left; reflexivity) INCL2 FH Ha) as (O1 & O2 & O3). lia. }
    clear AH2 AG2 MU3 WM3 MI2.
    change [CB 8 l32; CB 8 l80; CB 8 l88; C8 (Z_to_bv 64 SZ); CB 8 l64; C8 (Z_to_bv 64 F)]
      with ([CB 8 l32] ++ [CB 8 l80; CB 8 l88] ++ [C8 (Z_to_bv 64 SZ); CB 8 l64; C8 (Z_to_bv 64 F)]) in FRA3.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in FRA3. destruct FRA3 as [FRA3a FRA3b]. cbn [cells_size csize Nat.add] in FRA3b.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in FRA3b. destruct FRA3b as [FRA3b FRA3c]. cbn [cells_size csize Nat.add] in FRA3c.
    apply evtF_done. exists F, m3, l80, l88. do 16 eexists. split; [reflexivity|].
    unfold fzfr. split; [exact MI3|]. split; [exact STL3|]. split; [exact STG3|]. split; [exact FRB1|]. split; [exists l32; exact FRA3a|].
    split; [replace (SPA + 40) with (SPA + 32 + Z.of_nat 8) by lia; exact FRA3b|].
    split; [exists l64; replace (SPA + 56) with (SPA + 32 + Z.of_nat 8 + Z.of_nat 16) by lia; exact FRA3c|]. split; [exact HDR3|]. split; [exact FLP2|]. split; [exact SH3|].
    split; [exact IG3|]. split; [exact USH3|]. split; [exact CLS3|]. split; [eapply magree_mono; [exact AG3| intros a [Ha _]; exact Ha]|]. split; [exact AH3|].
    split; [exact F128|]. split; [exact FH|]. split; [lia|]. split; [exact RF| exact RSF].
  Qed.

  (* [comment removed for export] *)
  Definition fz_tail_post (RNGc : footprint) (sc : APS) (LBc : list ablock) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo SP
      /\ magree bsegs PW m0 m'
      /\ AHEAP AI L RNGc (aps_m sc) LBc m'
      /\ harness_invA m' /\ client_static sc LBc m'.

  Lemma fz_tail : forall (p : AsanCtrl.aptr) (RNGc : footprint) (sc : APS) (LBc : list ablock) (F : Z) (m3 : amem) (c80 : list cell)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x28 x29 x30 x31 : word),
    aps_cl sc = Some p -> fp_le RNG RNGc ->
    (forall b, In b LB -> In b LBc) -> (forall b, In b LBc -> exists q A n, b = HB q A n) ->
    fzfr RNGc sc LBc F m3 c80 -> cells_size c80 = 16%nat ->
    evtF bsegs RNGc (fz_tail_post RNGc sc LBc)
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 D) (Z_to_bv 64 F) x21 x22 x23 x24 (Z_to_bv 64 ASHOFF) (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0xb143c) fc None m3 (seg_rom bsegs)).
  Proof.
    intros until x31. intros CL FLE INCL HLBc (MI3 & STL3 & STG3 & FRB1 & [l72 FRA3a] & FRA3b & [l64 LSZ3] & HDR3 & FLP2 & SH3 & IG3 & USH3 & CLS3 & AG3 & AH3 & F128 & FH & FC & RF0 & RSF0) CS80.
    pose proof geom as (SPAB & SPA32 & TOP & TOP47 & CBOT & LBT & SZ0).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold AHARNESS_STACK in LOS. pose proof CBOT as CBOT'. atop_facts.
    pose proof payload_bounds as DB.
    pose proof (rng_fp_le _ _ _ _ FLE RF0) as RF. pose proof (rng_fp_le _ _ _ _ FLE RSF0) as RSF. pose proof (rng_fp_le _ _ _ _ FLE RSTK) as RSTKc.
    pose proof (rng_fp_le _ _ _ _ FLE RI) as RIc. pose proof (rng_fp_le _ _ _ _ FLE RISH) as RISHc.
    pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1. band_ind FH bFH.
    assert (BSF : 2148328448 <= shad F /\ shad F + 16 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    assert (INF : In (FB1 F) (FB1 F :: LBc)) by (left; reflexivity).
    assert (INCL2 : forall b, In b LB -> In b (FB1 F :: LBc)) by (intros b Hb; right; apply INCL; exact Hb).
    unfold shcells1 in SH3.
    (* [comment removed for export] *)
    pose proof CLS3 as (_ & _ & CLS3'). rewrite CL in CLS3'. destruct CLS3' as (V & HINV & VB3 & VEC3 & _ & _ & _ & _ & _ & SGL3 & _).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH3 ltac:(right; exact HINV)) as (_ & (VR1 & VR2 & VR3 & VR4) & RV & RSV & VSH & _).
    pose proof (ablk_lin _ _ VR1) as (VR1a & VR1b & VR1c & VR1d). unfold AIMG_HI in VR1a.
    assert (UNV : unpoisoned m3 V (V + 8)) by (apply (ablock_unpoisoned _ _ _ VSH); first [lia| clear - VR4; Z.div_mod_to_equations; lia]).
    eapply evtF_cut.
    { eapply f_load with (lo := lo) (SPA := SPA) (V := V);
        first [exact MI3| exact DB| exact FRA3a| exact LSZ3| exact VEC3| exact VB3| exact SGL3| exact IG3| exact USH3| exact UNV| exact VR1| exact RV
              | (eapply rng_sub'; [exact RSV| rewrite shlenE; lia])
              | reflexivity| exact RIc| exact RISHc| exact SP16| (clear - VR4; Z.div_mod_to_equations; lia)| eapply rng_sub'; [exact RSTKc| lia]| unfold AHARNESS_STACK in *; lia]. }
    cbv beta. intros ms4 (m4 & y14 & -> & MU4 & WM4 & MI4 & FRA4).
    assert (FW4 : Forall wfar [(SPA + 32, SPA + 40)]) by fw_far.
    pose proof (client_img_munch32 _ _ _ IG3 MU4 WM4 FW4) as IG4. pose proof (client_sh_munch32 _ _ _ USH3 MU4 FW4) as USH4.
    assert (CLS4 : client_static sc LBc m4).
    { eapply client_static_munch32; [exact CLS3| exact MU4| exact WM4| exact FW4|]. intros p' V' _ HIN'.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH3 ltac:(right; exact HIN')) as (_ & (Q1 & Q2 & Q3 & Q4) & _). cbn [disjoint_from]. lia. }
    clear IG3 USH3 CLS3 FW4 VB3 VEC3 SGL3 UNV.
    xrw FRB1 MU4 WM4. xrw FLP2 MU4 WM4. xrw HDR3 MU4 WM4. unfold shcells1 in SH3. xrw SH3 MU4 WM4. xrwc FRA3b MU4 WM4 CS80. xrw LSZ3 MU4 WM4. xst STL3 MU4 WM4. xst STG3 MU4 WM4.
    assert (AH4 : AHEAP AI L RNGc (aps_m sc) (FB1 F :: LBc) m4).
    { eapply (AI_frame AI); [exact AH3| exact MU4| exact WM4|]. constructor; [left; left; cbn; lia| constructor]. }
    assert (AG4 : magree bsegs PW m0 m4).
    { eapply magree_trans; [exact AG3|]. eapply magree_mono; [eapply magree_of_munch; [exact MU4| exact WM4]|]. intros a [Ha _]. cbn.
      destruct (pag_outside _ _ _ _ F a AH3 ltac:(left; reflexivity) INCL2 FH Ha) as (O1 & O2 & O3). lia. }
    clear AH3 AG3 MU4 WM4 MI3.
    (* [comment removed for export] *)
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH4) as (GOT4 & _ & _ & SHB4 & _).
    assert (BY4 : bytes_at bsegs m4 D (map (Z_to_bv 8) payload)).
    { eapply bytes_at_magree; [exact AG4| exact BY|]. rewrite length_map. intros a Ha.
      destruct PAY as [(pD & HIN & _)|[EP ED]]; [| exfalso; rewrite EP in Ha; cbn in Ha; lia].
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 ltac:(right; apply INCL; exact HIN)) as (_ & (PB1 & _) & _). pose proof (ablk_lin _ _ PB1) as (PB1a & _). unfold AIMG_HI in PB1a.
      split; [right; right; left; exists (HB pD D SZ); split; [exact HIN| cbn; unfold zlength in *; lia]| unfold client_wr; cbn [outside]; lia]. }
    assert (PF : unpoisoned m4 D (D + SZ) /\ rng RNGc D SZ /\ rng RNGc (shad D) (nshad SZ)).
    { destruct PAY as [(pD & HIN & _)|[EP ED]].
      - destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 ltac:(right; apply INCL; exact HIN)) as (_ & (B1 & B2 & B3 & B4) & RD & RSD & BSH & _).
        pose proof (ablk_lin _ _ B1) as (B1a & B1b & B1c & B1d).
        split; [apply (ablock_unpoisoned _ _ _ BSH); first [lia| clear - B4; Z.div_mod_to_equations; lia]|]. split; [exact RD|]. rewrite <- shlen_nshad. exact RSD.
      - rewrite EP, ED. unfold zlength, AEMPTY. cbn [length Z.of_nat]. rewrite Z.add_0_r.
        split; [apply unpoisoned_nil; lia|]. split; [eapply rng_sub'; [exact RIc| lia]|]. eapply rng_sub'; [exact RISHc| vm_compute; split; discriminate]. }
    destruct PF as (UD4 & RD4 & RSD4).
    destruct (stk_split bsegs _ lo SPA (SPA + 32) STL3 ltac:(lia)) as [STL4 STM4]. clear STL3.
    eapply evtF_cut.
    { eapply validate_utf8_proofB with (D := D) (pl := payload) (lo := lo);
        first [exact payload_pos| exact BY4| exact UD4| exact GOT4| exact SHB4| exact RIc| exact RD4| exact RSD4| exact MI4| reflexivity
              | rewrite unsigned_lit by lia; first [exact STL4| (eapply rng_sub'; [exact RSTKc| lia])| unfold VUTF8_STACK, KHIGH, KEND in *; lia]
              | (clear - D16; Z.div_mod_to_equations; lia)| unfold VUTF8_STACK, KHIGH, KEND in *; lia]. }
    cbv beta. intros ms5 PO. destruct PO as (v5 & v6 & v7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & v28 & v29 & v30 & v31 & m5 & -> & A0V & MU5 & WM5 & MI5 & ST5).
    rewrite ?unsigned_lit in MU5, ST5 by lia. retlit.
    assert (FW5 : Forall wfar [(SPA - 112, SPA)]) by fw_far.
    pose proof (client_img_munch32 _ _ _ IG4 MU5 WM5 FW5) as IG5. pose proof (client_sh_munch32 _ _ _ USH4 MU5 FW5) as USH5.
    assert (CLS5 : client_static sc LBc m5).
    { eapply client_static_munch32; [exact CLS4| exact MU5| exact WM5| exact FW5|]. intros p' V' _ HIN'.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 ltac:(right; exact HIN')) as (_ & (Q1 & Q2 & Q3 & Q4) & _). cbn [disjoint_from]. lia. }
    clear IG4 USH4 CLS4 FW5 BY4 UD4.
    xrw FRB1 MU5 WM5. xrw FLP2 MU5 WM5. xrw HDR3 MU5 WM5. xrw SH3 MU5 WM5. xrwc FRA3b MU5 WM5 CS80. xrw LSZ3 MU5 WM5. xrw FRA4 MU5 WM5. xst STM4 MU5 WM5. xst STG3 MU5 WM5.
    assert (AH5 : AHEAP AI L RNGc (aps_m sc) (FB1 F :: LBc) m5).
    { eapply (AI_frame AI); [exact AH4| exact MU5| exact WM5|]. constructor; [left; left; cbn; lia| constructor]. }
    assert (AG5 : magree bsegs PW m0 m5).
    { eapply magree_trans; [exact AG4|]. eapply magree_mono; [eapply magree_of_munch; [exact MU5| exact WM5]|]. intros a [Ha _]. cbn.
      destruct (pag_outside _ _ _ _ F a AH4 ltac:(left; reflexivity) INCL2 FH Ha) as (O1 & O2 & O3). lia. }
    clear AH4 AG4 MU5 WM5 MI4.
    (* [comment removed for export] *)
    destruct (AI_fake_flag _ _ _ _ _ _ _ _ AH5 ltac:(left; reflexivity)) as (FLC & RG & GH & GC & GBL & GCI).
    pose proof (GBL _ ltac:(left; reflexivity)) as GF. cbn [ab_addr ab_size] in GF.
    pose proof (ablk_lin _ _ GH) as (GH1 & GH2 & GH3 & GH4). unfold AIMG_HI in GH1. band_ind GH bGH.
    pose proof (stk_merge bsegs m5 lo SPA (SPA + 32) ST5 STM4 ltac:(lia)) as STL5. clear ST5 STM4.
    assert (FRA5 : rw_cells bsegs m5 (SPA + 32) ([C8 (Z_to_bv 64 AVEC)] ++ c80 ++ [C8 (Z_to_bv 64 SZ); CB 8 l64; C8 (Z_to_bv 64 F)])).
    { apply (proj2 (rw_cells_app bsegs m5 (SPA + 32) [C8 (Z_to_bv 64 AVEC)] _)). split; [exact FRA4|].
      cbn [cells_size csize Nat.add]. replace (SPA + 32 + Z.of_nat 8) with (SPA + 40) by lia.
      apply (proj2 (rw_cells_app bsegs m5 (SPA + 40) c80 _)). split; [exact FRA3b|]. rewrite CS80. replace (SPA + 40 + Z.of_nat 16) with (SPA + 56) by lia. exact LSZ3. }
    assert (CSA : cells_size ([C8 (Z_to_bv 64 AVEC)] ++ c80 ++ [C8 (Z_to_bv 64 SZ); CB 8 l64; C8 (Z_to_bv 64 F)]) = 48%nat) by (rewrite !cells_size_app, CS80; reflexivity).
    eapply evtF_cut.
    { eapply f_epi with (lo := lo) (SPA := SPA) (V := V) (F := F) (FLG := fflag L 1 F);
        first [exact SH3| exact CSA| reflexivity| apply shcells1_all_C1| exact HDR3| exact FLP2| exact FLC| exact FRB1| exact FRA5| exact STL5| exact STG3| exact MI5
              | exact RF| exact RSF| exact RG| exact F128| exact FH| exact GH| exact VR1| exact GC| exact SP16| lia
              | eapply rng_sub'; [exact RSTKc| lia]| unfold AHARNESS_STACK in *; lia]. }
    cbv beta. intros ms' (mp & m' & y11 & y12 & -> & MU6 & WM6 & MIp & MU7 & WM7 & MI' & ST' & FLC').
    (* [comment removed for export] *)
    assert (AHp : AHEAP AI L RNGc (aps_m sc) (FB1 F :: LBc) mp).
    { eapply (AI_frame AI); [exact AH5| exact MU6| exact WM6|]. constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - right; right. right; right. exists 1, F, 128. split; [left; reflexivity|].
        rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
      - right; left. exists (FB1 F). split; [left; reflexivity| cbn; lia]. }
    pose proof (AI_fake_release _ _ _ _ _ _ _ _ AHp) as AHr.
    rewrite <- (mem_eq_single mp m' (fflag L 1 F) (Z_to_bv 8 0) ltac:(lia) ltac:(lia) MU7 (byte_of_c1 _ _ _ FLC' ltac:(lia))) in AHr.
    assert (AG' : magree bsegs PW m0 m').
    { eapply magree_trans; [exact AG5|]. eapply magree_trans.
      - eapply magree_mono; [eapply magree_of_munch; [exact MU6| exact WM6]|]. intros a [Ha _]. cbn.
        destruct (pag_outside _ _ _ _ F a AH5 ltac:(left; reflexivity) INCL2 FH Ha) as (O1 & O2 & O3). lia.
      - eapply magree_mono; [eapply magree_of_munch; [exact MU7| exact WM7]|]. intros a [Ha _]. cbn.
        pose proof (fun b Hb => AI_block_bounds AI _ _ _ _ _ b AH5 Hb) as BB. cbv beta in BB. unfold AIMG_HI in BB.
        destruct Ha as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
        + lia.
        + split; [| exact I]. assert (a <> fflag L 1 F) by (intros ->; apply GCI; exists iv; split; assumption). lia.
        + pose proof (GBL _ ltac:(right; apply INCL; exact Hb)). lia.
        + assert (A47 : 0 <= a' < 2^47) by (destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia| destruct (HLB _ Hb') as (p' & A'' & N' & E'); discriminate]).
          rewrite shad_div. unfold ASHOFF. split; [| exact I]. intros X'. eapply (ablk_clear_band _ _ _ GH); [| exact X']. unfold KLS. clear - A47. Z.div_mod_to_equations. lia. }
    assert (FW6 : Forall wfar [(shad F, shad F + 16); (F, F + 8)]) by fw_far.
    assert (FW7 : Forall wfar [(fflag L 1 F, fflag L 1 F + 1)]) by fw_far.
    assert (DV : forall W, (W = [(shad F, shad F + 16); (F, F + 8)] \/ W = [(fflag L 1 F, fflag L 1 F + 1)]) ->
                 forall p' V', aps_cl sc = Some p' -> In (HB p' V' 8) LBc -> disjoint_from W V' 8).
    { intros W HW p' V' _ HIN'.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH5 ltac:(right; exact HIN')) as (_ & (Q1 & Q2 & Q3 & Q4) & _).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH5 ltac:(right; exact HIN') INF ltac:(discriminate)) as D0. cbn in D0.
      pose proof (GBL _ ltac:(right; exact HIN')) as D1. cbn [ab_addr ab_size] in D1.
      pose proof (ablk_lin _ _ Q1) as (Q1a & Q1b & Q1c & Q1d). unfold AIMG_HI in Q1a. band_ind Q1 bQ1.
      destruct HW as [-> | ->]; cbn [disjoint_from]; lia. }
    apply evtF_done. unfold fz_tail_post. do 14 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|].
    split; [exact AHr|].
    split. { split; [exact (client_img_munch32 _ _ _ (client_img_munch32 _ _ _ IG5 MU6 WM6 FW6) MU7 WM7 FW7)| exact (client_sh_munch32 _ _ _ (client_sh_munch32 _ _ _ USH5 MU6 FW6) MU7 FW7)]. }
    eapply client_static_munch32; [eapply client_static_munch32; [exact CLS5| exact MU6| exact WM6| exact FW6| apply DV; left; reflexivity]| exact MU7| exact WM7| exact FW7| apply DV; right; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma astk_of_agree : forall m', magree bsegs PW m0 m' -> astk_shadow_pres SP m0 m'.
  Proof.
    intros m' AG' a Ha. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof geom as (SPAB & SPA32 & TOP & TOP47 & CBOT & LBT & SZ0). unfold AHARNESS_STACK in LOS. pose proof LOS as LOS'. pose proof BOT as BOT'. atop_facts.
    rewrite <- (shad_unshad a). apply AG'; [rewrite shad_unshad; rewrite !shad_div in Ha; unfold ASHOFF in *; Z.div_mod_to_equations; lia|].
    split.
    - right; right; right. exists (8 * (a - ASHOFF)). split; [| reflexivity]. left. pose proof ATOP_al16. rewrite !shad_div in Ha. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
    - rewrite shad_unshad. rewrite !shad_div in Ha. unfold ASHOFF in Ha. unfold client_wr. cbn [outside]. Z.div_mod_to_equations. lia.
  Qed.

  Notation POST := (fuzz_oneU_post AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m0).

  (* [comment removed for export] *)
  Theorem fz_later : forall (p : AsanCtrl.aptr) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    aps_cl s = Some p ->
    implMA RNG (fuzz_oneA AAllocAsan payload) s POST
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 SZ) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (Z_to_bv 64 AFUZZ_ENTRY) fc None m0 (seg_rom bsegs)).
  Proof.
    intros p t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CL.
    (* [comment removed for export] *)
    apply implMA_fold. unfold fuzz_oneA. rewrite (HarnessU.fuzz_one_later _ _ _ _ payload s p CL). apply (implMA_unfold RNG (mret 0) s).
    apply implMA_ret.
    eapply evtF_cut; [apply fz_head|]. cbv beta. intros ms (F & m3 & l80 & l88 & x1 & x5 & x6 & x7 & y10 & y11 & y12 & y13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & -> & FZ).
    rewrite CL.
    eapply evtF_cut.
    { eapply (fz_tail p RNG s LB F m3); [exact CL| apply fp_le_refl| intros b Hb; exact Hb| exact HLB| exact FZ| reflexivity]. }
    cbv beta. intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MI' & ST' & AG' & AHr & HI' & CLS').
    apply evtF_done. unfold fuzz_oneU_post. split; [apply fp_le_refl|].
    do 14 eexists. exists FR, fc, m', LB. split; [reflexivity|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact FRM|]. split; [exact ST'|].
    split; [exact AG'|]. split; [apply astk_of_agree; exact AG'|]. split; [exact AHr|]. split; [exact HI'|]. split; [exact CLS'|].
    split; [reflexivity|]. rewrite CL. split; [reflexivity|]. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Hypothesis RSI : rsi_stmt AI.
  Hypothesis ACXA : acxa_atexit_stmt.
  Variable rstk : region.
  Hypothesis RC : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : bv_unsigned sp <= r_hi rstk.
  Hypothesis RRLO : ATOP <= r_rlo rstk.
  Hypothesis RR : rrng RNG rstk.
  Hypothesis HUL : HU L.
  Hypothesis ROK : aps_ok L s.
  (* [comment removed for export] *)
  Hypothesis AI_lsan : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells bsegs m 0x6afb18 [C4 (Z_to_bv 64 0)].
  Hypothesis AI_frame_lsan : forall L RNG st LB m m' W, AHEAP AI L RNG st LB m -> munch W m m' -> wmono bsegs m m' ->
    Forall (fun iv => aclient_range CI LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ iv = (0x6afb18, 0x6afb1c)) W ->
    rw_cells bsegs m' 0x6afb18 [C4 (Z_to_bv 64 0)] -> AHEAP AI L RNG st LB m'.

  Theorem fz_first : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    aps_cl s = None ->
    implMA RNG (fuzz_oneA AAllocAsan payload) s POST
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 SZ) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (Z_to_bv 64 AFUZZ_ENTRY) fc None m0 (seg_rom bsegs)).
  Proof.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CL.
    pose proof geom as (SPAB & SPA32 & TOP & TOP47 & CBOT & LBT & SZ0).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold AHARNESS_STACK in LOS. pose proof CBOT as CBOT'. atop_facts.
    apply implMA_fold. unfold fuzz_oneA. rewrite (HarnessU.fuzz_one_first _ _ _ _ payload s CL).
    apply (implMA_unfold RNG _ s).
    eapply implMA_evtF; [apply fz_head|]. cbv beta. intros ms (F & m3 & l80 & l88 & x1 & x5 & x6 & x7 & y10 & y11 & y12 & y13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & -> & FZ).
    rewrite CL.
    destruct FZ as (MI3 & STL3 & STG3 & FRB & [l72 FRA3a] & FRA3b & [l64 LSZ3] & HDR3 & FLP & SH3 & IG3 & USH3 & CLS3 & AG3 & AH3 & F128 & FH & FC & RF & RSF).
    destruct CLS3 as (AR3 & AT3 & CLS3'). rewrite CL in CLS3'. destruct CLS3' as (VEC & GRD & G1 & IL & G2 & ARR & SGL & G3 & WSH).
    pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1. band_ind FH bFH.
    assert (BSF : 2148328448 <= shad F /\ shad F + 16 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    assert (INCL2 : forall b, In b LB -> In b (FB1 F :: LB)) by (intros b Hb; right; exact Hb).
    (* [comment removed for export] *)
    pose proof FRA3b as LOC3. clear FRA3b.
    eapply implMA_evtF.
    { eapply f_w1 with (SPA := SPA) (F := F) (l40 := l80) (l48 := l88); first [exact MI3| exact GRD| exact LOC3| exact RI| (eapply rng_sub'; [exact RSTK| lia])| lia]. }
    cbv beta. intros ms4 (m4 & z11 & z12 & -> & MU4 & WM4 & MI4 & GRD4 & LOC4).
    unfold AVEC_GUARD, AVEC, AFALLBACK, guard0, w0, shcells1 in *.
    assert (AH4 : AHEAP AI L RNG (aps_m s) (FB1 F :: LB) m4).
    { eapply (AI_frame AI); [exact AH3| exact MU4| exact WM4|]. constructor; [left; left; cbn; lia| constructor; [| constructor]].
      left; right; left. exists (0x6ad7a0, 0x6ad7a2). split; [apply IMG_CI; unfold client_ranges; cbn [In]; tauto| cbn; lia]. }
    assert (AG4 : magree bsegs PW m0 m4).
    { eapply magree_trans; [exact AG3|].
      eapply magree_mono; [eapply magree_of_munch; [exact MU4| exact WM4]|]. intros a [Ha OW]. cbn [outside].
      destruct (pag_outside _ _ _ _ F a AH3 ltac:(left; reflexivity) INCL2 FH Ha) as (O1 & O2 & O3). unfold client_wr in OW. cbn [outside] in OW. lia. }
    assert (USH4 : client_sh m4).
    { eapply client_sh_munch_gen; [exact USH3| exact MU4|]. intros X HX. unfold client_sh_addrs in HX. cbn [In] in HX. cbn [outside].
      repeat (destruct HX as [<-|HX]; [rewrite shad_div; unfold ASHOFF; cbn; lia|]). destruct HX. }
    assert (IG4 : client_img m4) by (eapply client_img_munch_gen; [exact IG3| exact MU4| exact WM4| cbn; lia| cbn; lia]).
    assert (AR4 : atexit_rt m4) by (eapply atexit_rt_munch_gen; [exact AR3| exact MU4| exact WM4| cbn; lia| cbn; lia]).
    assert (AT4 : ATEXIT (client_tbl s) m4) by (eapply ATEXIT_munch_gen; [exact AT3| exact MU4| exact WM4| cbn; lia]).
    clear GRD LOC3 AG3 IG3 USH3 AR3 AT3. xall MU4 WM4. clear MU4 WM4 AH3 MI3.
    (* [comment removed for export] *)
    destruct (stk_split bsegs _ lo SPA (SPA + 32) STL3 ltac:(lia)) as [STL4 STM4]. clear STL3.
    assert (UST : unpoisoned m4 (SPA - 216) (SPA - 176) /\ rng RNG (shad (SPA - 216)) 5).
    { destruct RC as [(UN & (HL1 & HL2 & HL3) & _ & _) RLT]. split.
      - eapply unpoisoned_agree; [eapply unpoisoned_sub; [exact UN| lia| lia]|]. intros sx Hs.
        rewrite <- (shad_unshad sx). rewrite !shad_div in Hs. unfold ASHOFF in Hs.
        apply AG4; [rewrite shad_unshad; unfold ASHOFF; Z.div_mod_to_equations; lia|]. split.
        + right; right; right. exists (8 * (sx - ASHOFF)). split; [| reflexivity]. left. unfold ASHOFF. Z.div_mod_to_equations. lia.
        + rewrite shad_unshad. unfold client_wr. cbn [outside]. Z.div_mod_to_equations. lia.
      - eapply rng_sub'; [exact RR|]. unfold hull64 in *. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    destruct UST as [UST RSS].
    apply implMA_bind_assoc. eapply implMA_bind.
    { eapply RSI with (lo := lo) (LBc := FB1 F :: LB);
        rewrite ?unsigned_lit by lia;
        first [exact AH4| exact MI4| exact STL4| exact BOT| exact TP| reflexivity| exact HUL| exact RSTK| exact RI| exact RISH| exact ROK| exact IG4| exact USH4
              | exact VEC| exact G1| exact IL| exact G2| exact ARR| exact SGL| exact G3| exact WSH| exact UST| exact RSS
              | unfold RSI_STACK; lia| (clear - SPA32; Z.div_mod_to_equations; lia)]. }
    cbv beta. intros p sx RNG5 ms5 PO.
    destruct PO as (FLE5 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m5 & V & -> & MI5 & ST5 & AG45 & SO5 & VR & AH5 & VB5 & VEC5 & SS5).
    rewrite ?unsigned_lit in ST5, AG45 by lia. retlit.
    (* [comment removed for export] *)
    assert (INF : In (FB1 F) (FB1 F :: LB)) by (left; reflexivity).
    Ltac p5out := unfold RSI_W, RSI_IMGW, AVEC; cbn [outside]; lia.
    Ltac p5 INF IMG_CI :=
      first [ split; [left; lia| p5out]
            | split; [right; right; left; eexists; split; [exact INF| cbn; lia]| p5out]
            | split; [eapply sh_client; [exact INF| Z.div_mod_to_equations; lia| lia| lia]| p5out]
            | split; [right; left; eexists; split; [apply IMG_CI; unfold client_ranges; pick_in| cbn; lia]| p5out] ].
    repeat match goal with
    | Hc : rw_cells _ m4 ?A ?cs |- _ =>
        lazymatch A with 7001952 => fail | 7002208 => fail | 7002240 => fail | 7002272 => fail | 7002304 => fail | 7002336 => fail | 7002432 => fail | _ => idtac end;
        apply (rw_cells_magree bsegs _ m4 m5 A cs AG45) in Hc;
        [| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul FZRB]; intros ? ?; p5 INF IMG_CI]
    | Hs : stk _ m4 ?loq ?hiq |- _ => lazymatch loq with lo => fail | _ => idtac end; apply (stk_magree bsegs _ m4 m5 loq hiq AG45) in Hs; [| intros ? ?; p5 INF IMG_CI]
    end.
    Ltac p5img IMG_CI := cbv beta; split; [right; left; eexists; split; [apply IMG_CI; unfold client_ranges; pick_in| cbn; lia]| p5out].
    assert (USH5 : client_sh m5).
    { eapply client_sh_magree; [exact USH4| exact AG45|]. intros X HX. unfold client_sh_addrs in HX. cbn [In] in HX. cbv beta.
      repeat (destruct HX as [<-|HX];
        [split; [right; right; right; eexists; split; [| reflexivity]; right; left; eexists; split; [apply IMG_CI; unfold client_ranges; pick_in| cbn; lia]
                | rewrite shad_div; unfold ASHOFF; cbn; p5out]|]). destruct HX. }
    assert (IG5 : client_img m5) by (eapply (client_img_magree AI); [exact IG4| exact AG45| intros a Ha; p5img IMG_CI| exact AH5| exact MI5]).
    assert (AR5 : atexit_rt m5) by (eapply atexit_rt_magree; [exact AR4| exact AG45|]; intros a [Ha|Ha]; p5img IMG_CI).
    assert (AT5 : ATEXIT (client_tbl s) m5) by (eapply ATEXIT_magree; [exact AT4| exact AG45|]; intros a Ha; p5img IMG_CI).
    assert (AG5 : magree bsegs PW m0 m5).
    { eapply magree_trans; [exact AG4|]. eapply magree_mono; [exact AG45|]. intros a [Ha OW]. split.
      - eapply pag_client; [exact Ha| exact INCL2| lia].
      - unfold client_wr in OW. cbn [outside] in OW. p5out. }
    clear AG45 AG4 USH4 AR4 AT4 IG4 UST VEC G1 IL G2 ARR SGL G3 WSH AH4 MI4 STL4.
    (* [comment removed for export] *)
    apply implMA_updb. set (sc := a_set_cl AAllocAsan (Some p) sx).
    assert (CLc : aps_cl sc = Some p) by reflexivity.
    assert (SOc : aps_rest sc = aps_rest s) by (rewrite <- SO5; reflexivity).
    assert (AH5c : AHEAP AI L RNG5 (aps_m sc) (HB p V 8 :: FB1 F :: LB) m5) by exact AH5.
    clear AH5. apply implMA_ret.
    pose proof (rng_fp_le _ _ _ _ FLE5 RSTK) as RSTK5. pose proof (rng_fp_le _ _ _ _ FLE5 RI) as RI5.
    (* [comment removed for export] *)
    eapply evtF_cut; [eapply f_w2 with (SPA := SPA) (F := F); exact MI5|]. cbv beta. intros ms6 ->.
    unfold client_tbl in AT5. rewrite CL in AT5.
    destruct (atexit_main_split _ AT5) as (xf3 & xf4 & xa3 & xa4 & fj & aj & REST & SLOT & F34 & A34). clear AT5.
    pose proof REST as (FIN & LOCK & HEAD & _).
    destruct AR5 as (REAL & (cdt & thr & sec & tm1 & LIBC)).
    eapply evtF_cut.
    { pose proof (AI_rtcells AI _ _ _ _ _ AH5c) as (_ & _ & _ & _ & _ & _ & INI5 & _).
      eapply ACXA with (lo := lo) (cdt := cdt) (thr := thr) (sec := sec) (tm1 := tm1) (f4 := xf3) (f5 := xf4) (a04 := xa3) (a05 := xa4);
        rewrite ?unsigned_lit by lia;
        first [exact ST5| exact INI5| exact (atexit_got_of_aheap AI _ _ _ _ _ AH5c MI5)| exact (AI_lsan _ _ _ _ _ AH5c)| exact REAL| exact LIBC| exact FIN| exact LOCK| exact SLOT| exact HEAD
              | exact F34| exact A34| exact MI5| exact TP| exact RI5| (eapply rng_sub'; [exact RSTK5| lia])| unfold KHIGH; lia]. }
    cbv beta. intros ms7 PO. destruct PO as (e0 & e1 & e2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & e3 & e4 & e5 & e6 & m6 & -> & MU6 & WM6 & MI6 & ST6 & CNT6 & SLOT6 & F6 & A6).
    rewrite !unsigned_lit in MU6 by lia. rewrite !unsigned_lit in ST6 by lia. retlit.
    assert (INF5 : In (FB1 F) (HB p V 8 :: FB1 F :: LB)) by (right; left; reflexivity).
    assert (INCL5 : forall b, In b LB -> In b (HB p V 8 :: FB1 F :: LB)) by (intros b Hb; right; right; exact Hb).
    pose proof VR as (VH & _ & VTOP & V16). pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    assert (AH6 : AHEAP AI L RNG5 (aps_m sc) (HB p V 8 :: FB1 F :: LB) m6).
    { eapply AI_frame_lsan; [exact AH5c| exact MU6| exact WM6| | exact CNT6].
      constructor; [left; left; left; cbn; lia|]. constructor; [right; reflexivity|].
      repeat (constructor; [left; left; right; left; exists (0x6cfb58, 0x6cfd78); split; [apply IMG_CI; unfold client_ranges; cbn [In]; tauto| cbn; lia]|]). constructor. }
    assert (AG6 : magree bsegs PW m0 m6).
    { eapply magree_trans; [exact AG5|]. eapply magree_mono; [eapply magree_of_munch; [exact MU6| exact WM6]|]. intros a [Ha OW]. cbn [outside].
      destruct (pag_outside _ _ _ _ F a AH5c INF5 INCL5 FH Ha) as (O1 & _). unfold client_wr in OW. cbn [outside] in OW. lia. }
    assert (USH6 : client_sh m6).
    { eapply client_sh_munch_gen; [exact USH5| exact MU6|]. intros X HX. unfold client_sh_addrs in HX. cbn [In] in HX. cbn [outside].
      repeat (destruct HX as [<-|HX]; [rewrite shad_div; unfold ASHOFF; cbn; lia|]). destruct HX. }
    assert (IG6 : client_img m6) by (eapply client_img_munch_gen; [exact IG5| exact MU6| exact WM6| cbn; lia| cbn; lia]).
    assert (REST6 : atx_rest fj aj m6) by (eapply atx_rest_transport; [exact REST| exact MU6| exact WM6| cbn; lia| cbn; lia| cbn; lia| cbn; lia| cbn; lia]).
    assert (AT6 : ATEXIT (client_tbl sc) m6).
    { unfold client_tbl. rewrite CLc. eapply atexit_run_join; [exact REST6| exact SLOT6| exact F6| exact A6]. }
    destruct SS5 as (G1 & IL & G2 & ARR & SGL & G3).
    clear SLOT F34 A34 FIN LOCK HEAD REST USH5 AG5 CNT6 SLOT6 F6 A6.
    unfold guard1, w0, AFALLBACK, AFALLBACK_VT, AVEC in *.
    xall MU6 WM6. clear MU6 WM6 AH5c MI5 ST5.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply f_w3 with (SPA := SPA) (F := F); first [exact MI6| exact GRD4| exact LOC4| exact RI5| (eapply rng_sub'; [exact RSTK5| lia])| lia]. }
    cbv beta. intros ms8 (m7 & w1 & w10 & w11 & -> & MU7 & WM7 & MI7 & GRD7 & LOC7).
    unfold AVEC_GUARD in MU7.
    assert (AH7 : AHEAP AI L RNG5 (aps_m sc) (HB p V 8 :: FB1 F :: LB) m7).
    { eapply (AI_frame AI); [exact AH6| exact MU7| exact WM7|]. constructor; [| constructor].
      left; right; left. exists (0x6ad7a0, 0x6ad7a2). split; [apply IMG_CI; unfold client_ranges; cbn [In]; tauto| cbn; lia]. }
    assert (AG7 : magree bsegs PW m0 m7).
    { eapply magree_trans; [exact AG6|]. eapply magree_mono; [eapply magree_of_munch; [exact MU7| exact WM7]|]. intros a [Ha OW]. cbn [outside].
      unfold client_wr in OW. cbn [outside] in OW. lia. }
    assert (USH7 : client_sh m7).
    { eapply client_sh_munch_gen; [exact USH6| exact MU7|]. intros X HX. unfold client_sh_addrs in HX. cbn [In] in HX. cbn [outside].
      repeat (destruct HX as [<-|HX]; [rewrite shad_div; unfold ASHOFF; cbn; lia|]). destruct HX. }
    assert (IG7 : client_img m7) by (eapply client_img_munch_gen; [exact IG6| exact MU7| exact WM7| cbn; lia| cbn; lia]).
    assert (AT7 : ATEXIT (client_tbl sc) m7) by (eapply ATEXIT_munch_gen; [exact AT6| exact MU7| exact WM7| cbn; lia]).
    clear GRD4 LOC4 USH6 AT6 AG6 REST6. xall MU7 WM7. clear MU7 WM7 AH6 MI6.
    (* [comment removed for export] *)
    pose proof (stk_merge bsegs m7 lo SPA (SPA + 32) ST6 STM4 ltac:(lia)) as STL7.
    pose proof LOC7 as C80.
    assert (AH7' : AHEAP AI L RNG5 (aps_m sc) (FB1 F :: HB p V 8 :: LB) m7) by (eapply (AI_perm AI); [apply Permutation.perm_swap| exact AH7]).
    eapply evtF_cut.
    { eapply (fz_tail p RNG5 sc (HB p V 8 :: LB) F m7 [C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F)]); [exact CLc| exact FLE5| intros b Hb; right; exact Hb| | | reflexivity].
      - intros b [<-|Hb]; [eexists _, _, _; reflexivity| apply HLB; exact Hb].
      - unfold fzfr. split; [exact MI7|]. split; [exact STL7|]. split; [exact STG3|]. split; [exact FRB|]. split; [exists l72; exact FRA3a|]. split; [exact C80|]. split; [exists l64; exact LSZ3|].
        split; [exact HDR3|]. split; [exact FLP|]. split; [exact SH3|]. split; [exact IG7|]. split; [exact USH7|].
        split. { split; [split; [exact REAL| exists cdt, thr, sec, tm1; exact LIBC]|]. split; [exact AT7|]. rewrite CLc. exists V. split; [left; reflexivity|].
                 unfold AVEC, AVEC_GUARD, AFALLBACK, AFALLBACK_VT, guard1, w0.
                 split; [exact VB5|]. split; [exact VEC5|]. split; [exact GRD7|]. split; [exact G1|]. split; [exact IL|]. split; [exact G2|]. split; [exact ARR|]. split; [exact SGL| exact G3]. }
        split; [exact AG7|]. split; [exact AH7'|]. split; [exact F128|]. split; [exact FH|]. split; [lia|]. split; [exact RF| exact RSF]. }
    cbv beta. intros ms' (k0 & k1 & k2 & n1 & n2 & n3 & n4 & n5 & n6 & n7 & k3 & k4 & k5 & k6 & m' & -> & MI' & ST' & AG' & AHr & HI' & CLS').
    apply evtF_done. unfold fuzz_oneU_post. split; [exact FLE5|].
    do 14 eexists. exists FR, fc, m', (HB p V 8 :: LB). split; [reflexivity|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact FRM|]. split; [exact ST'|].
    split; [exact AG'|]. split; [apply astk_of_agree; exact AG'|]. split; [exact AHr|]. split; [exact HI'|]. split; [exact CLS'|].
    split; [exact SOc|]. rewrite CL. exists p, V. split; [reflexivity| exact CLc].
  Qed.
End M.

(* [comment removed for export] *)
Section Final.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (fflag : alayout -> Z -> Z -> Z) (rng_fs : alayout -> footprint -> Prop).
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis SM1 : stack_malloc_1_stmt AI fflag rng_fs.
  Hypothesis AI_fake_flag : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
    rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
    /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
    /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
    /\ ~ in_ranges CI (fflag L cls F).
  Hypothesis AI_fake_release : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
    AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
  Hypothesis RSI : rsi_stmt AI.
  Hypothesis ACXA : acxa_atexit_stmt.
  Hypothesis AI_lsan : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells bsegs m 0x6afb18 [C4 (Z_to_bv 64 0)].
  Hypothesis AI_frame_lsan : forall L RNG st LB m m' W, AHEAP AI L RNG st LB m -> munch W m m' -> wmono bsegs m m' ->
    Forall (fun iv => aclient_range CI LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ iv = (0x6afb18, 0x6afb1c)) W ->
    rw_cells bsegs m' 0x6afb18 [C4 (Z_to_bv 64 0)] -> AHEAP AI L RNG st LB m'.

  Theorem fuzz_oneU_proof : fuzz_oneU_stmt AI rng_fs.
  Proof.
    unfold fuzz_oneU_stmt. intros until rstk.
    intros AH HLB PAY BY FA D16 SZB HI CLS ST BOT LOS SPG SP16 RC RLO RHI RRLO S0E MI FRM TP -> -> RAE HUL RSTK RI RISH RFS RR ROK.
    destruct (aps_cl s) as [p|] eqn:CL.
    - eapply (fz_later AI fflag rng_fs IMG_CI SM1 AI_fake_flag AI_fake_release); eassumption.
    - eapply (fz_first AI fflag rng_fs IMG_CI SM1 AI_fake_flag AI_fake_release); eassumption.
  Qed.
End Final.
End CANSEC1.
