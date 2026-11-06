(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CatSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge Mem Cells Step Frame SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF Shadow StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AU_consts AU_iface AU_kit AU_parts_iface AU_client_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib SegBridge.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit PIosKitA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import APS2_iface A2Lib PA2_kz PA2_exit PA2_xlib PA2_tail.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require PA2_t0c A2D_defs A2D_cert A2D_sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Import ITree.Exc.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

Section CANSEC. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma xsf_regsD : forall (ZL : list Z) (E' : env) (R' : bvmap 5 word),
  SP.gagree 35 (mkEZ ZL) E' -> eb (mkEZ ZL) = eb E' -> rfull R' -> regs_ok E' (ST.t_regs A2D_defs.XSF) R' ->
  exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31,
    R' = mkR (Z_to_bv 64 0xa8500) (Z_to_bv 64 (16 * nth 1 ZL 0 + -384 - 16 * nth 29 ZL 0)) (Z_to_bv 64 (nth 2 ZL 0)) (Z_to_bv 64 (nth 3 ZL 0))
             x5 x6 x7 (Z_to_bv 64 (16 * nth 1 ZL 0)) (Z_to_bv 64 (16 * nth 1 ZL 0 + -384 - 16 * nth 29 ZL 0))
             (Z_to_bv 64 (2048 * nth 28 ZL 0)) (Z_to_bv 64 1312) x12 x13 x14 x15 x16 x17 x18
             (Z_to_bv 64 (256 * nth 28 ZL 0 + 2147450880)) x20 x21 x22 (edenot E' (EVar 35)) x24 x25 x26 x27 x28 x29 x30 x31.
Proof.
  intros ZL E' R' Hg Hb HF HR.
  change (ST.t_regs A2D_defs.XSF) with (ST.t_regs A2_defs.XSF) in HR.
  exact (xsf_regs ZL E' R' Hg Hb HF HR).
Qed.

Lemma xsf_kfactsD : forall (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
    (T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z) (rest : list Z) (E' : env) (m3 : amem),
  SP.gagree 35 (mkEZ (PA2_t0c.ZL_t0'' zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11
                             T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest)) E' ->
  eb (mkEZ (PA2_t0c.ZL_t0'' zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11
                   T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest)) = eb E' ->
  know_ok asegs E' m3 (ST.t_know A2D_defs.XSF) ->
  0 <= 16 * SP16 < M64 ->
  0 <= u (edenot E' (EVar 35)) <= 63
  /\ (forall k, 0 <= k < 13 -> bytes_at asegs m3 (16 * SP16 - 8 - 8 * k)
                 (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [zra; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11] 0)))).
Proof.
  intros until m3. intros Hg Hb HK HSP.
  split.
  - pose proof (know_nth _ _ _ _ 0 _ HK eq_refl) as K. cbn [kentry_ok] in K. cbv [A2D_defs.V] in K. exact K.
  - intros k Hk.
    assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
    destruct Hk' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]];
    match goal with |- bytes_at _ _ (16 * SP16 - 8 - 8 * ?k) _ =>
      let j := eval vm_compute in (Z.to_nat (2 + k)) in
      pose proof (know_nth _ _ _ _ j _ HK eq_refl) as K;
      lazymatch type of K with kentry_ok _ _ _ (KWord (SA ?b ?kk) ?w ?v) =>
        pose proof (kx_word_g asegs 35 _ E' m3 b kk w v Hg Hb eq_refl eq_refl eq_refl K) as B end; cbn [zden nth PA2_t0c.ZL_t0'' app] in B;
      rewrite (Z.mod_small (16 * SP16)) in B by lia;
      let o := eval vm_compute in (-8 - 8 * k) in
      replace (16 * SP16 - 8 - 8 * k) with (16 * SP16 + o) by lia; exact B
    end.
Qed.

(* [comment removed for export] *)
Lemma a2d_munch : forall (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
    (T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z) (rest : list Z) (m m' : amem),
  8608 <= 16 * SP16 <= 2 ^ 47 -> 0 <= 8 * T8 /\ 8 * T8 + 96 < M64 -> 0 <= 8 * TB8 /\ 8 * TB8 + 8 * CAPT < M64 -> 0 <= CAPT ->
  0 <= 8 * SB8 /\ 8 * SB8 + CAPS < M64 -> 0 <= CAPS -> 0 <= 8 * OC8 /\ 8 * OC8 + 8192 < M64 -> 0 <= 8 * IA8 /\ 8 * IA8 + 1024 < M64 ->
  0 <= 2048 * F11 /\ 2048 * F11 + 2048 < M64 -> 0 <= 256 * F11 + 2147450880 /\ 256 * F11 + 2147450880 + 256 < M64 ->
  0 <= PB <= 1 ->
  (forall x : word, SP.outside_wins (mkEZ (PA2_t0c.ZL_t0'' zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11
                                         T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest))
                        (SP.p_W A2D_defs.A2D) (u x) -> m' x = m x) ->
  munch [(16 * SP16 - 8608, 16 * SP16); (8 * T8 + 24, 8 * T8 + 28); (8 * T8 + 88, 8 * T8 + 96); (8 * TB8, 8 * TB8 + 8 * CAPT);
         (8 * SB8, 8 * SB8 + CAPS); (8 * OC8, 8 * OC8 + 8192); (8 * IA8, 8 * IA8 + 1024); (2048 * F11, 2048 * F11 + 2048);
         (256 * F11 + 2147450880, 256 * F11 + 2147450880 + 256)] m m'.
Proof.
  intros until m'. intros H1 H2 H3 H3' H4 H4' H5 H6 H7 H8 HPB FR x Hx. apply FR. unfold SP.outside_wins.
  cbn [SP.p_W A2D_defs.A2D SP.PGCA SP.PGH SP.PGX].
  pose proof (u_rngE x). cbn [outside] in Hx.
  cbv [A2D_defs.vSP A2D_defs.vSP16 A2D_defs.vTHIS A2D_defs.vT8 A2D_defs.vTBASE A2D_defs.vTB8 A2D_defs.vCAPT A2D_defs.vSBASE A2D_defs.vSB8
       A2D_defs.vCAPS A2D_defs.vOCB A2D_defs.vOC8 A2D_defs.vIAB A2D_defs.vIA8 A2D_defs.vF A2D_defs.vF11 A2D_defs.vSHF A2D_defs.V A2D_defs.mul
       A2D_defs.add A2D_defs.vSPA A2D_defs.vPB A2D_defs.sub].
  repeat constructor; cbn [SP.win_den]; rewrite ?u_zden by reflexivity; cbn [zden nth PA2_t0c.ZL_t0'' app];
    rewrite ?(Z.mod_small _ M64) by lia; lia.
Qed.

Section XDG.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis SF5 : stack_free_5_stmt AI fflag.
  Variables (L : alayout) (RNG RNG6 : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (s sD : APS) (LB : list ablock) (lo : Z) (m m6 : amem)
            (THIS TPA ntp SBA nsb AOC AIA : Z) (pim ptp psb poc pia : AsanCtrl.aptr) (nim noc nia : Z) (F SPAX : Z).
  Hypothesis Ith : In (HB pim THIS nim) LB.
  Hypothesis Hnim : 96 <= nim.
  Hypothesis Itp : In (HB ptp TPA ntp) LB.
  Hypothesis Isb : In (HB psb SBA nsb) LB.
  Hypothesis Ioc : In (HB poc AOC noc) LB.
  Hypothesis Hnoc : 8192 <= noc.
  Hypothesis Iia : In (HB pia AIA nia) LB.
  Hypothesis Hnia : 1024 <= nia.
  Hypothesis NO5 : forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB.
  Hypothesis Hlo1 : ATOP + 4096 <= lo.
  Hypothesis Hlo2 : lo <= u sp - 8608.
  Hypothesis Hsp16 : u sp mod 16 = 0.
  Hypothesis Hsp47 : u sp <= 2^47.
  Hypothesis HSPA32 : SPAX mod 32 = 0.
  Hypothesis HSPA : 384 <= u sp - SPAX <= 415.
  Hypothesis HFm : F mod 2048 = 0.
  Hypothesis HFb : ablk F (F + 2048).
  Hypothesis HFt : F + 2048 <= ATOP.
  Hypothesis HSHF : forall a, aclient_addr CI LB SPAX a -> a < shad F \/ shad F + 256 <= a.
  (* [comment removed for export] *)
  Variables (SP16 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z) (restD : list Z).
  Local Notation ZLD := (PA2_t0c.ZL_t0'' (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9)
                          (u s10) (u s11) T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG restD).
  Hypothesis E_SP : u sp = 16 * SP16.
  Hypothesis E_T8 : THIS = 8 * T8.
  Hypothesis E_TB8 : TPA = 8 * TB8.
  Hypothesis E_CAPT : ntp = 8 * CAPT.
  Hypothesis E_SB8 : SBA = 8 * SB8.
  Hypothesis E_CAPS : nsb = CAPS.
  Hypothesis E_OC8 : AOC = 8 * OC8.
  Hypothesis E_IA8 : AIA = 8 * IA8.
  Hypothesis E_F11 : F = 2048 * F11.
  Hypothesis E_PB : u sp - 384 - SPAX = 16 * PB.
  Hypothesis E_FLAG : FLAG = fflag L 5 F.
  Hypothesis B_T : 0 <= THIS /\ THIS + 96 < M64.
  Hypothesis B_TB : 0 <= TPA /\ TPA + ntp < M64 /\ 0 <= ntp.
  Hypothesis B_SB : 0 <= SBA /\ SBA + nsb < M64 /\ 0 <= nsb.
  Hypothesis B_OC : 0 <= AOC /\ AOC + 8192 < M64.
  Hypothesis B_IA : 0 <= AIA /\ AIA + 1024 < M64.
  (* [comment removed for export] *)
  Variables (E6 : env) (D : ST.tmpl) (R6 FR6 : bvmap 5 word) (fc6 : bv 32).
  Hypothesis Hg6 : SP.gagree 35 (mkEZ ZLD) E6.
  Hypothesis Hb6 : eb E6 = eb (mkEZ ZLD).
  Hypothesis HinD : In D (SP.p_tm A2D_defs.A2D).
  Hypothesis HF6 : rfull R6.
  Hypothesis HRD : regs_ok E6 (ST.t_regs D) R6.
  Hypothesis HKD : know_ok asegs E6 m6 (ST.t_know D).
  Hypothesis HFLD : In (KWord (SA A2D_defs.vF 2040) 8 A2D_defs.vFLAG) (ST.t_know D).
  Hypothesis HFWD : In (KWr (SA A2D_defs.vF 0) (ELit 2048)) (ST.t_know D).
  Hypothesis HZ6 : frm0 fc6.
  Hypothesis AWG6 : SX.aw_genuine E6 (SP.p_A A2D_defs.A2D).
  Hypothesis FPL6 : fp_le (SX.fp_of (SP.p_A A2D_defs.A2D) E6) RNG6.
  Hypothesis AH6 : AHEAP AI L RNG6 (aps_m sD) (mkABlock (ABFake 5) F 2048 :: LB) m6.
  Hypothesis MI6 : mem_inv asegs m6.
  Hypothesis STK6 : stk asegs m6 lo (u sp).
  Hypothesis PW6 : aheap_pres_W CI LB (u sp) (s2_winA THIS TPA ntp SBA nsb AOC AIA) m m6.
  Hypothesis RNGS6 : rng RNG6 lo (u sp - lo).
  Hypothesis FPLR : fp_le RNG RNG6.
  Hypothesis APSD : aps_rest sD = aps_rest s.

  Lemma xd_tail :
    evtF asegs RNG6 (s2_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo (s2_winA THIS TPA ntp SBA nsb AOC AIA) m tt sD RNG6)
      (MS R6 FR6 (Z_to_bv 64 (ST.t_pc D)) fc6 None m6 (seg_rom asegs)).
  Proof using All.
    atop_facts. pose proof (u_rngE sp) as Rsp.
    pose proof (AI_layout AI _ _ _ _ _ AH6) as (_ & _ & HTOP & _).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply evtF_weaken; [exact FPL6|].
      exact (SLib.prog_evt asegs A2D_sound.GP0a2d (fun _ _ => []) (fun _ => false) A2D_sound.GP0a2d_frame A2D_sound.GP0a2d_vc
               A2D_defs.A2D A2D_defs.A2D_IT 4000 false [] D A2D_cert.a2d_cert (SP.itab_ranges_sound asegs _) ltac:(intros TA []) ltac:(intros Sm [])
               ltac:(apply in_or_app; left; exact HinD) E6 m6 (seg_rom asegs) R6 FR6 fc6 AWG6 HF6 HRD HKD
               ltac:(unfold SG.gholds; apply Forall_forall; intros; exact I) MI6 HZ6). }
    intros ms7 (X & E7 & m7 & R7 & F7 & fc7 & HinX & -> & HZ7 & HF7 & HR7 & HK7 & HG7 & Hg7 & Hb7 & FR7 & WM7 & MI7 & STK7).
    cbn [SP.p_ex A2D_defs.A2D SP.PGCA SP.PGX] in HinX. destruct HinX as [<-|[]].
    assert (Hg7' : SP.gagree 35 (mkEZ ZLD) E7) by (eapply SP.gagree_trans; [exact Hg6 | exact Hg7]).
    assert (Hb7' : eb (mkEZ ZLD) = eb E7) by congruence.
    (* [comment removed for export] *)
    assert (FR7' : forall x : word, SP.outside_wins (mkEZ ZLD) (SP.p_W A2D_defs.A2D) (u x) -> m7 x = m6 x).
    { intros x Hx. apply FR7. eapply SP.outside_wins_gagree; [exact Hg6 | exact (eq_sym Hb6) | reflexivity | exact Hx]. }
    assert (Hsp47' : u sp <= 2 ^ 47) by lia.
    pose proof (a2d_munch (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                  T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG restD m6 m7
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(unfold ablk, AIMG_HI, KLS in HFb; lia) ltac:(unfold ablk, AIMG_HI, KLS in HFb; lia) ltac:(lia) FR7') as MU.
    assert (ESF : shad F = 256 * F11 + SH) by (rewrite shad_div; unfold ASHOFF; rewrite E_F11; clear; Z.div_mod_to_equations; lia).
    rewrite <- E_SP, <- E_T8, <- E_TB8, <- E_CAPT, <- E_SB8, <- E_CAPS, <- E_OC8, <- E_IA8, <- E_F11, <- ESF in MU.
    (* [comment removed for export] *)
    assert (AH7 : AHEAP AI L RNG6 (aps_m sD) (mkABlock (ABFake 5) F 2048 :: LB) m7).
    { eapply (AI_frame AI); [exact AH6 | exact MU | exact WM7 |].
      assert (FF : shad F - ASHOFF = F / 8) by (rewrite shad_div; lia).
      repeat apply Forall_cons; [ .. | apply Forall_nil]; cbn [fst snd].
      + left; left. lia.
      + right; left. exists (HB pim THIS nim). split; [right; exact Ith | cbn; lia].
      + right; left. exists (HB pim THIS nim). split; [right; exact Ith | cbn; lia].
      + right; left. exists (HB ptp TPA ntp). split; [right; exact Itp | cbn; lia].
      + right; left. exists (HB psb SBA nsb). split; [right; exact Isb | cbn; lia].
      + right; left. exists (HB poc AOC noc). split; [right; exact Ioc | cbn; lia].
      + right; left. exists (HB pia AIA nia). split; [right; exact Iia | cbn; lia].
      + left; right; right. exists 5, F, 2048. split; [left; reflexivity | lia].
      + right; right. right; right. exists 5, F, 2048. split; [left; reflexivity|].
        replace (shad F + 256 - shad F) with 256 by ring. rewrite FF. clear - HFm; Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
    assert (PW7 : aheap_pres_W CI LB (u sp) (s2_winA THIS TPA ntp SBA nsb AOC AIA) m m7).
    { eapply aheap_pres_W_trans; [exact PW6|]. eapply (aheap_pres_W_of_munch CI LB (u sp) _ _ m6 m7 MU WM7).
      intros a Ha Hc Hout.
      assert (HSX : a < shad F \/ shad F + 256 <= a).
      { apply HSHF. destruct Hc as [X|[X|[X|X]]]; [left; lia | right; left; exact X | right; right; left; exact X | right; right; right; exact X]. }
      assert (SF : KLS <= shad F < 0x10007fff8000) by (apply shad_band1; unfold ablk, AIMG_HI, KLS, KEND in *; lia).
      assert (HO3 : ~ (u sp - 8608 <= a < u sp) /\ ~ (F <= a < F + 2048)).
      { destruct Hc as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
        - lia.
        - pose proof (AI_aci_img AI iv Hiv). unfold ablk, AIMG_HI in *. lia.
        - pose proof (AI_block_bounds AI _ _ _ _ _ b AH6 (or_intror Hb)) as BB.
          assert (NE : b <> mkABlock (ABFake 5) F 2048) by (intros ->; exact (NO5 F 2048 Hb)).
          pose proof (AI_blocks_disjoint AI _ _ _ _ _ b (mkABlock (ABFake 5) F 2048) AH6 (or_intror Hb) (or_introl eq_refl) NE) as DJ.
          cbn [ab_addr ab_size] in DJ. lia.
        - assert (A47 : 0 <= a' < KEND).
          { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; unfold KEND;
              [lia | pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia |].
            pose proof (AI_block_bounds AI _ _ _ _ _ _ AH6 (or_intror Hb')) as BB. cbn [ab_addr ab_size] in BB. unfold AIMG_HI in BB. lia. }
          pose proof (shad_band1 a' (proj1 A47) (proj2 A47)) as SB. unfold ablk, KLS in *. lia. }
      unfold s2_winA in Hout. cbn [outside] in Hout |- *. destruct Hout as (O1 & O2 & O3 & O4 & O5 & O6 & _).
      destruct HO3 as [O7 O8]. repeat split; try assumption; lia. }
    (* [comment removed for export] *)
    destruct (xsf_regsD ZLD E7 R7 Hg7' Hb7' HF7 HR7)
      as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x20 & x21 & x22 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->).
    destruct (xsf_kfactsD (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG restD E7 m7 Hg7' Hb7' HK7 ltac:(lia))
      as (HRC & SAVED).
    rewrite <- E_SP in SAVED.
    cbn [nth PA2_t0c.ZL_t0'' app].
    replace (16 * SP16 + -384 - 16 * PB) with SPAX by lia. rewrite <- E_SP, <- E_F11. rewrite !Z_to_bv_bv_unsigned.
    change (Z_to_bv 64 (ST.t_pc A2D_defs.XSF)) with (Z_to_bv 64 ASTKFREE5).
    rewrite <- (Z_to_bv_bv_unsigned (edenot E7 (EVar 35))).
    (* [comment removed for export] *)
    assert (EF : edenot E6 A2D_defs.vF = Z_to_bv 64 F).
    { rewrite <- (SP.edenot_gagree 35 (mkEZ ZLD) E6 A2D_defs.vF Hg6 (eq_sym Hb6) eq_refl), zden_ok by reflexivity.
      cbn [zden nth PA2_t0c.ZL_t0'' app A2D_defs.vF A2D_defs.vF11 A2D_defs.V A2D_defs.mul]. rewrite <- E_F11. reflexivity. }
    assert (EV : edenot E6 A2D_defs.vFLAG = Z_to_bv 64 (fflag L 5 F)).
    { rewrite <- (SP.edenot_gagree 35 (mkEZ ZLD) E6 A2D_defs.vFLAG Hg6 (eq_sym Hb6) eq_refl).
      cbn [edenot ev mkEZ nth PA2_t0c.ZL_t0'' app A2D_defs.vFLAG A2D_defs.V]. rewrite E_FLAG. reflexivity. }
    assert (HFL6 : rw_cells asegs m6 (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))]).
    { pose proof (SB.kx_word asegs E6 m6 A2D_defs.vF 2040 8 A2D_defs.vFLAG (proj1 (Forall_forall _ _) HKD _ HFLD)) as B.
      pose proof (kx_wr_g asegs 35 ZLD E6 m6 A2D_defs.vF 0 (ELit 2048) Hg6 (eq_sym Hb6) eq_refl eq_refl eq_refl
                    (proj1 (Forall_forall _ _) HKD _ HFWD)) as W.
      cbn [zden nth PA2_t0c.ZL_t0'' app A2D_defs.vF A2D_defs.vF11 A2D_defs.V A2D_defs.mul] in W. rewrite <- E_F11 in W.
      rewrite (Z.mod_small F), (Z.mod_small 2048), Z.add_0_r in W by (unfold ablk, AIMG_HI, KLS in HFb; lia).
      rewrite EF, EV, u_Z_to_bv, Z.mod_small in B by (unfold ablk, AIMG_HI, KLS in HFb; lia).
      apply rw8_of; [exact B|]. apply (wr_at_sub m6 F 2048 (F + 2040) 8 W); lia. }
    assert (HFL7 : rw_cells asegs m7 (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))]).
    { pose proof (know_nth _ _ _ _ 1 _ HK7 eq_refl) as K.
      assert (EF7 : edenot E7 A2D_defs.vF = Z_to_bv 64 F) by (rewrite <- EF; symmetry; apply (SP.edenot_gagree 35 E6 E7); [exact Hg7 | exact (eq_sym Hb7) | reflexivity]).
      assert (EV7 : edenot E7 A2D_defs.vFLAG = Z_to_bv 64 (fflag L 5 F)) by (rewrite <- EV; symmetry; apply (SP.edenot_gagree 35 E6 E7); [exact Hg7 | exact (eq_sym Hb7) | reflexivity]).
      pose proof (SB.kx_rw8 asegs E7 m6 m7 A2D_defs.vF 2040 A2D_defs.vFLAG (Z_to_bv 64 (fflag L 5 F)) K) as X.
      rewrite EF7, EV7, u_Z_to_bv, Z.mod_small in X by (unfold ablk, AIMG_HI, KLS in HFb; lia).
      exact (X HFL6 WM7). }
    eapply (xsf_tail AI fflag SF5 L RNG RNG6 s sD LB m m7 lo (s2_winA THIS TPA ntp SBA nsb AOC AIA) F SPAX (u (edenot E7 (EVar 35))));
      [ exact AH7 | exact MI7 | exact (STK7 _ _ STK6) | exact Hlo1 | lia | exact Hsp16 | exact Hsp47' | exact HSPA | exact HSPA32 | exact HFL7
      | exact SAVED | exact HRC | exact RNGS6 | exact PW7 | exact FPLR | exact APSD | exact HZ7 ].
  Qed.
End XDG.
End CANSEC.
