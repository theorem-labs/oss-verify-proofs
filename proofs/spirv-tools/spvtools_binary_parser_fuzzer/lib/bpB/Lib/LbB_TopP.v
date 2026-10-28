(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvB_FuzzStmt LbB_PrsStmt LbB_DStat LbB_SR LbB_Conv LbB_Ctx LbB_RG2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TopDefs LbB_TopKit LbB_TopH2 LbB_TopT1 LbB_TopP1 LbB_TopT LbB_TopC.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section TopP.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.
  Hypothesis HPO : binary_parse_stmtA H LINV_P5.
  Hypothesis HTR : po_tr_ok H.

  Definition cut_P9 (e : hent H) (c : config) : Prop :=
    exists (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (F' : bvmap 5 word) (fc' : bv 32)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m' : mem) (n P : Z) (pv pc : bptr)
           (A : Z) (j1 j2 : list byte),
      as_VIS H sk (cfg_ms c) = MS (mkR x1 (Z_to_bv 64 (eS1 e)) (e_gp e) (e_tp e) x5 x6 x7 (Z_to_bv 64 (eSP e)) (Z_to_bv 64 (eS1 e))
                                       x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                  F' (Z_to_bv 64 0xe8be0) fc' None m' (seg_rom asegs)
      /\ as_AKREL H sk c /\ as_MPRES H (e_mo e) (cfg_model c)
      /\ FPSteps.frm_zero fc'
      /\ hinv H e ff fp XSc sk LBk m'
      /\ rw_cells asegs m' (eS1 e + 24) (top_fr A ff) /\ rw_cells asegs m' (eS1 e + 80) (top_vd ff (e_D e))
      /\ n = e_N e / 4 /\ as_AL H sk >= as_AL H (e_s e) - ICM 64 - ICM (4 * n)
      /\ (exists j, rw_cells asegs m' (sh ff + 4) [CB 313 j])
      /\ rw_cells asegs m' (ff + 2672) [C8 (wz P); C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))]
      /\ SHAD m' (ff + 2672) (repeat (b8 0) 3)
      /\ rw_cells asegs m' A [C4 (wz RG_ENV); CB 44 j1; C8 (wz 0); CB 8 j2] /\ addressable m' A CTX_SZ
      /\ vec_st H e LBk m' n P pv pc A.

  Lemma seg_P9 : forall (e : hent H) (c : config), hpre H e -> cut_P9 e c -> as_SR H (hpost H e) c.
  Proof.
    intros e [msF mo] HP CT.
    destruct CT as (ff & fp & XSc & sk & LBk & F' & fc' & x1 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21
                    & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m' & n & P & pv & pc & A & j1 & j2 & VIS & KR & MP & FZ & HI
                    & CFR & CVD & HNn & AL & (j & CJ) & CV & SV & CC & CA & VEC).
    cbn [cfg_ms cfg_model] in VIS, MP.
    pose proof (rt_bp_base H HH) as HB.
    pose proof (eS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    pose proof (hpre_geo H e HP) as (_ & LO & SSHI & SHIH & SP16 & TP).
    pose proof (hinv_ff H _ _ _ _ _ _ _ HI) as FFR.
    pose proof (hframe_facts H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    pose proof HP as (_ & _ & _ & NR & _ & _ & _ & _ & BS & BC & BL & _ & SPB & BB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LFL
                      & _ & _ & _ & PF & _ & ALs).
    set (SP := eSP e) in *. set (S1 := eS1 e) in *. set (lo := e_lo e) in *.
    assert (Hn : 0 <= n < 2 ^ 24) by (rewrite HNn; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).

    assert (INc : In (pc, A, 64) LBk).
    { destruct VEC as [(_ & _ & PERM) | (_ & PERM & _)]; apply (Permutation_in _ (Permutation_sym PERM)); [left | right; left]; reflexivity. }
    pose proof (ah_blocks H HB _ _ _ _ (hinv_rh H _ _ _ _ _ _ _ HI) INc) as (C0 & C16 & Cn & CI & CCe & CF & CAPP). cbn in C0, C16, Cn, CI, CCe, CF, CAPP.
    assert (PR : 0 <= P /\ P + 4 * n <= 2 ^ 47).
    { destruct VEC as [(N0 & P0 & _) | (NR1 & PERM & _)]; [subst n P; lia|].
      assert (INv : In (pv, P, 4 * n) LBk) by (apply (Permutation_in _ (Permutation_sym PERM)); left; reflexivity).
      pose proof (ah_blocks H HB _ _ _ _ (hinv_rh H _ _ _ _ _ _ _ HI) INv) as (V0 & _ & _ & _ & VC & _). cbn in V0, VC. lia. }

    eapply (ahh_evt_then H HB); [exact KR | exact VIS | |].
    pose proof CFR as CFA. unfold top_fr in CFA.
    change [C8 (wz A); C8 (wz (sh ff + 4)); C8 (wz ff); C8 (wz (sh ff)); C8 (wz ff)]
      with ([C8 (wz A)] ++ [C8 (wz (sh ff + 4)); C8 (wz ff); C8 (wz (sh ff)); C8 (wz ff)]) in CFA.
    apply rw_cells_app in CFA as [CFA _].
    pose proof CVD as CFV. unfold top_vd in CFV.
    change [C8 (wz (ff + 2672)); C8 (wz (e_D e))] with ([C8 (wz (ff + 2672))] ++ [C8 (wz (e_D e))]) in CFV.
    apply rw_cells_app in CFV as [CFV _].
    { exact (hPO1 x1 (e_gp e) (e_tp e) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F' fc' m' SP S1
                  (ff + 2672) A P n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) CFA CFV CV). }
    intros msF1 mo1 KR1 MP1 VIS1. hnf in VIS1.
    pose proof (hchain_call H HB e ff fp XSc sk LBk m' HP HI) as (CHN & CHU).
    destruct (hinv_er H e ff fp XSc sk LBk m' HI) as (errv & ER).
    pose proof (hinv_rf H _ _ _ _ _ _ _ HI) as RF.

    assert (BUD : lb_small LBk + po_small n <= RT_SMALL_MAX /\ Z.of_nat (length LBk) + po_cnt n <= RT_CNT_MAX
                  /\ nlarge LBk + po_large n <= RT_LARGE_MAX).
    { pose proof (po_mono n (2 ^ 24) ltac:(lia)) as (M1 & M2 & M3 & _).
      unfold TOP_SMALL, TOP_CNT, TOP_LARGE in BS, BC, BL.
      pose proof (nsmall_bounds (4 * n) ltac:(lia)) as NS1. pose proof (nlg_bounds (4 * n)) as NL1.
      assert (NS2 : nsmall (4 * n) <= 64512) by (unfold nsmall; destruct (Z.leb_spec (4 * n) 64512); lia).
      assert (N64 : nsmall 64 = 64) by reflexivity. assert (L64 : nlg 64 = 0) by reflexivity.
      destruct VEC as [VE|VE].
      - destruct VE as (_ & _ & PERM).
        rewrite (lb_small_perm _ _ PERM), (nlarge_perm _ _ PERM), (Permutation_length PERM). cbn [length].
        rewrite lb_small_cons, nlarge_cons. cbn [blk_size snd]. rewrite N64, L64.
        split; [lia|]. split; lia.
      - destruct VE as (_ & PERM & _).
        rewrite (lb_small_perm _ _ PERM), (nlarge_perm _ _ PERM), (Permutation_length PERM). cbn [length].
        rewrite !lb_small_cons, !nlarge_cons. cbn [blk_size snd]. rewrite N64, L64.
        split; [lia|]. split; lia. }
    destruct BUD as (BU1 & BU2 & BU3).
    assert (ALp : po_cost n <= as_AL H sk).
    { unfold top_cost in ALs. rewrite <- HNn in ALs. lia. }
    eapply (ah_seq H HB).
    { eapply (HPO (Z_to_bv 64 TOP_PO_RA) (Z_to_bv 64 S1)) with (ctx := A) (env := RG_ENV) (words := P) (n := n) (lo := lo) (B := e_B e)
          (shi := e_shi e) (errv := errv) (LB := LBk) (LF := (6, ff, fp) :: e_LF e) (CH := (SP, bv_unsigned (e_ra e)) :: e_CH e) (s := sk);
        rewrite ?HLib.u64_of_Z by lia;
        [exact VIS1 | exact FZ | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | intros X; discriminate X
        | exists pc, j1, j2; split; [exact INc|]; split; [exact CC|]; split; [exact CA | unfold RG_ENV; lia]
        | exact Hn | | exact (hinv_rh H _ _ _ _ _ _ _ HI) | exact KR1 | exact BU1 | exact BU2 | exact BU3
        | exact (hinv_ra H _ _ _ _ _ _ _ HI) | lia | exact BB | clear - S32; Z.div_mod_to_equations; lia
        | exact (proj1 (stk_split asegs m' lo S1 SP (hinv_stk H _ _ _ _ _ _ _ HI) ltac:(lia))) | exact CE | unfold APO_STACK, APM_STACK; lia
        | exact ER | exact (hinv_mi H _ _ _ _ _ _ _ HI) | exact TP | unfold TOP_PO_RA; vm_compute; reflexivity | exact (hlinv H HB e ff fp XSc sk LBk m' HP HI)
        | exact (hinv_ac H _ _ _ _ _ _ _ HI) | exact RF | cbn [length]; unfold PO_FRAMES, AFS_MAXLIVE_BP in *; lia
        | exact (hinv_s0 H _ _ _ _ _ _ _ HI) | lia | rewrite HLib.u64_of_Z by lia; exact CHN | | exact CHU | exact HTR | exact ALp].
      - destruct VEC as [(N0 & P0 & _) | (NR1 & PERM & (bs & CB) & ADP)]; [left; split; assumption | right].
        assert (INv : In (pv, P, 4 * n) LBk) by (apply (Permutation_in _ (Permutation_sym PERM)); left; reflexivity).
        pose proof (ah_blocks H HB _ _ _ _ (hinv_rh H _ _ _ _ _ _ _ HI) INv) as (V0 & V16 & Vn & VI & VC & VF & VAPP). cbn in V0, V16, Vn, VI, VC, VF, VAPP.
        exists pv, (4 * n). split; [exact INv|]. split; [lia|]. split; [lia|]. split; [exact V16|]. split; [lia|].
        split; [apply mdef_of_wr_at; [eapply rw_cells_wr_at; [exact CB | cbn [cells_size csize]; lia] | unfold AIMG_TOP in VI; lia]|].
        rewrite cc_gen_full. exact (proj2 ADP).
      - rewrite HLib.u64_of_Z by (unfold TOP_PO_RA; lia).
        eapply pf_ok_call; [exact PF|]. intros pp Hpp. unfold TOP_PF. apply in_or_app. right. exact Hpp. }
    intros [msF2 mo2] P2.
    destruct P2 as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & errv' & s' & LB' & XS & Fr2 & fc2
                    & VIS2 & FZ2 & KR2 & MP2 & MI2 & ST2 & ER2 & RA2 & RH2 & PERM2 & FSX & XP2 & RF2 & AC2 & S02 & LV2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, MP2. rewrite HLib.u64_of_Z in ST2, XP2 by lia.
    rewrite (ret_pc_even TOP_PO_RA ltac:(unfold TOP_PO_RA; lia) eq_refl) in VIS2.
    assert (INC : forall b, In b (e_LB e) -> In b LBk).
    { intros b Hb. destruct VEC as [(_ & _ & PERM) | (_ & PERM & _)]; apply (Permutation_in _ (Permutation_sym PERM)); [right | right; right]; exact Hb. }
    assert (HI2 : hinv H e ff fp (XSc ++ XS) s' LB' m2).
    {
      eapply (hinv_sr_gen H HB e ff fp XSc XS ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XS) sk LBk LBk s' LB' m' m2 HP HI INC XP2 FSX); [| exact RF2 | exact RH2 | exact AC2 | exact MI2 | exact ST2
        | exists errv'; exact ER2 | exact RA2 | exact LV2].
      apply Forall_cons; [right; right; right; reflexivity|]. apply Forall_forall. intros iv Hiv. left. exact Hiv. }

    assert (XSF : forall iv, In iv XS -> (snd iv <= ff \/ ff + 4096 <= fst iv) /\ (snd iv <= sh ff \/ sh ff + 512 <= fst iv)).
    { intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FSX iv Hiv) as FSi.
      destruct (fsw_ok H HB e ff fp m2 iv RF2 FFR CE FSi) as (_ & _ & _ & _ & D1 & D2 & _). split; [exact D1 | exact D2]. }
    assert (XSB : forall p A0 k iv, In (p, A0, k) LBk -> In iv XS -> (A0 + k <= fst iv \/ snd iv <= A0) /\ (sh A0 + nsh k <= fst iv \/ snd iv <= sh A0)).
    { intros p A0 k iv IN Hiv. pose proof (proj1 (Forall_forall _ _) FSX iv Hiv) as FSi.
      pose proof (ah_blocks H HB _ _ _ _ (hinv_rh H _ _ _ _ _ _ _ HI) IN) as (D0 & D16 & Dn & DI & DC & DF & DAPP). cbn in D0, D16, Dn, DI, DC, DF, DAPP.
      pose proof (fsobj_block H HB _ _ _ ((6, ff, fp) :: e_LF e) p A0 k (hinv_rh H _ _ _ _ _ _ _ HI) IN) as FO.
      split.
      - exact (fsobj_scratch H HB _ A0 k m2 iv RF2 FO ltac:(lia) Dn ltac:(unfold AAPP_HI; lia) DAPP FSi).
      - exact (fsobj_scratch_sh H HB _ A0 k m2 iv RF2 FO ltac:(lia) Dn ltac:(unfold AAPP_HI; lia) FSi). }
    assert (XCF : forall A0 k, ff <= A0 -> A0 + k <= ff + 4096 -> 0 <= k -> xclient_range H LBk S1 ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XS) A0 k).
    { intros A0 k K1 K2 K3. split; [right; right; right; right; left; unfold AFS_SIZE in *; lia|].
      apply Forall_cons; [cbn [fst snd]; right; pose proof (hframe_facts H _ _ _ FFR) as (G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & G9' & G10' & G11' & G12' & G13' & G14' & G15' & G16'); unfold RtB_Td.ATDLOC; lia|].
      apply Forall_forall. intros iv Hiv. destruct (XSF iv Hiv) as [D1 _]. lia. }
    assert (XCS : forall A0 k, sh ff <= A0 -> A0 + k <= sh ff + 512 -> 0 <= k -> xclient_range H LBk S1 ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XS) A0 k).
    { intros A0 k K1 K2 K3. split; [right; right; right; right; right; left; lia|].
      apply Forall_cons; [cbn [fst snd]; right; pose proof (hframe_facts H _ _ _ FFR) as (G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & G9' & G10' & G11' & G12' & G13' & G14' & G15' & G16'); unfold RtB_Td.ATDLOC; lia|].
      apply Forall_forall. intros iv Hiv. destruct (XSF iv Hiv) as [_ D2]. lia. }
    assert (XCB : forall p A0 k a kk, In (p, A0, k) LBk -> A0 <= a -> a + kk <= A0 + k -> 0 <= kk -> xclient_range H LBk S1 ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XS) a kk).
    { intros p A0 k a kk IN K1 K2 K3. split; [eapply (aclient_range_block H); [exact IN | exact K1 | exact K2]|].
      apply Forall_cons.
      { cbn [fst snd]. right. pose proof (ah_blocks H HB _ _ _ _ (hinv_rh H _ _ _ _ _ _ _ HI) IN) as (D0 & D16 & Dn & DI & _). cbn in DI. unfold RtB_Td.ATDLOC, AIMG_TOP in *. lia. }
      apply Forall_forall. intros iv Hiv. destruct (XSB p A0 k iv IN Hiv) as [D1 _]. lia. }
    assert (XCBs : forall p A0 k, In (p, A0, k) LBk -> 0 <= A0 -> 0 <= k -> xclient_range H LBk S1 ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XS) (sh A0) (nsh k)).
    { intros p A0 k IN K1 K2. split; [exact (aclient_range_block_sh H LBk S1 p A0 k IN)|].
      apply Forall_cons; [cbn [fst snd]; right; unfold sh; rewrite ASHADOW_BASE_val; unfold RtB_Td.ATDLOC; clear - K1; Z.div_mod_to_equations; lia|].
      apply Forall_forall. intros iv Hiv. destruct (XSB p A0 k iv IN Hiv) as [_ D2]. lia. }
    assert (XCT : forall A0 k, S1 <= A0 -> 0 <= k -> xclient_range H LBk S1 ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XS) A0 k).
    { intros A0 k K1 K2. split; [left; exact K1|].
      apply Forall_cons; [cbn [fst snd]; right; unfold RtB_Td.ATDLOC; lia|].
      apply Forall_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FSX iv Hiv) as FSi.
      destruct (fsw_ok H HB e ff fp m2 iv RF2 FFR CE FSi) as (_ & _ & _ & _ & _ & _ & D & _). right. fold lo in D. lia. }
    apply (seg_CD H HH); [exact HP|].
    exists ff, fp, (XSc ++ XS), s', LB', Fr2, fc2, (Z_to_bv 64 TOP_PO_RA), t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7,
      x19, x20, x21, x22, x23, x24, x25, x26, x27, t3, t4, t5, t6, m2, n, P, pv, pc, A, j1, j2.
    cbn [cfg_ms cfg_model]. split; [exact VIS2|]. split; [exact KR2|].
    split; [exact (ah_mpres_trans H HB (e_mo e) mo mo2 MP (ah_mpres_trans H HB mo mo1 mo2 MP1 MP2))|].
    split; [exact FZ2|]. split; [exact HI2|].
    split; [unfold top_cost; rewrite <- HNn; lia|].
    split; [exists j; eapply xpres_rw_cells; [exact XP2 | exact CJ | apply XCS; cbn; lia]|].
    split; [eapply xpres_rw_cells; [exact XP2 | exact CV | apply XCF; cbn; lia]|].
    split.
    { destruct SV as (S1a & S1b & U). split; [exact S1a|]. split; [exact S1b|].
      replace (sh (ff + 2672)) with (sh ff + 334) in * by (rewrite <- (sh_add8 ff 334); f_equal).
      destruct U as (UB & UW). split.
      - eapply xpres_bytes_at; [exact XP2 | exact UB | rewrite repeat_length; apply XCS; cbn; lia].
      - eapply xpres_wr_at; [exact XP2 | exact UW | rewrite repeat_length; apply XCS; cbn; lia]. }
    split; [eapply xpres_rw_cells; [exact XP2 | exact CFR | apply XCT; lia]|].
    split; [eapply xpres_rw_cells; [exact XP2 | exact CVD | apply XCT; lia]|].
    split; [eapply xpres_rw_cells; [exact XP2 | exact CC | eapply XCB; [exact INc | lia | cbn; lia | cbn; lia]]|].
    split.
    { destruct CA as (CA0 & CS0 & CS1 & (UB & UW)). split; [exact CA0|]. split; [exact CS0|]. split; [exact CS1|].
      unfold CTX_SZ in *.
      assert (XC := XCBs pc A 64 INc ltac:(lia) ltac:(lia)). split.
      - eapply xpres_bytes_at; [exact XP2 | exact UB | rewrite shadow_of_length by lia; exact XC].
      - eapply xpres_wr_at; [exact XP2 | exact UW | rewrite shadow_of_length by lia; exact XC]. }
    destruct VEC as [(N0 & P0 & PERM) | (NR1 & PERM & (bs & CB) & ADP)].
    - left. split; [exact N0|]. split; [exact P0|]. exact (perm_trans PERM2 PERM).
    - right. split; [exact NR1|]. split; [exact (perm_trans PERM2 PERM)|].
      assert (INv : In (pv, P, 4 * n) LBk) by (apply (Permutation_in _ (Permutation_sym PERM)); left; reflexivity).
      split.
      + exists bs. eapply xpres_rw_cells; [exact XP2 | exact CB | eapply XCB; [exact INv | lia | | ]].
        * destruct CB as [[[X _] _] _]. cbn [cells_size csize]. rewrite Nat.add_0_r. lia.
        * lia.
      + destruct ADP as (AD0 & AS0 & AS1 & (UB & UW)). split; [exact AD0|]. split; [exact AS0|]. split; [exact AS1|].
        assert (XC := XCBs pv P (4 * n) INv ltac:(lia) ltac:(lia)). split.
        * eapply xpres_bytes_at; [exact XP2 | exact UB | rewrite shadow_of_length by lia; exact XC].
        * eapply xpres_wr_at; [exact XP2 | exact UW | rewrite shadow_of_length by lia; exact XC].
  Qed.
End TopP.
