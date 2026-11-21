(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit U2AObj U2ABlob InfAGlue InfPure.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BCall U2BGlue U2BIface InfBBase InfBGlueE InfBKit InfBIface InfB_pro InfB_epi.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BKit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import StrFun RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

From Stdlib Require Import FunctionalExtensionality.

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma retrule_val : forall vin have out left rv, 0 <= vin -> 0 <= have -> 0 <= out -> 0 <= left -> 0 <= rv ->
  Z.land (Z.lor (Z.b2z (18446744073709551612 <? 1)) (Z.b2z (Z.lor (Z.lxor vin have) (Z.lxor out left) <? 1))) (Z.b2z (rv <? 1))
  = if ((vin =? have) && (out =? left) && (rv =? 0))%bool then 1 else 0.
Proof.
  intros vin have out left rv H1 H2 H3 H4 H5.
  assert (LX : forall a b, 0 <= a -> 0 <= b -> (Z.lxor a b = 0 <-> a = b)) by (intros; apply Z.lxor_eq_0_iff).
  assert (N1 : 0 <= Z.lxor vin have) by (apply Z.lxor_nonneg; lia).
  assert (N2 : 0 <= Z.lxor out left) by (apply Z.lxor_nonneg; lia).
  assert (N3 : 0 <= Z.lor (Z.lxor vin have) (Z.lxor out left)) by (apply Z.lor_nonneg; lia).
  pose proof (Z.lor_eq_0_iff (Z.lxor vin have) (Z.lxor out left)) as LO.
  change (18446744073709551612 <? 1) with false. cbn [Z.b2z]. rewrite Z.lor_0_l.
  destruct (Z.eqb_spec vin have) as [E1|E1]; destruct (Z.eqb_spec out left) as [E2|E2]; destruct (Z.eqb_spec rv 0) as [E3|E3]; cbn [andb];
    destruct (Z.ltb_spec (Z.lor (Z.lxor vin have) (Z.lxor out left)) 1) as [Q|Q]; destruct (Z.ltb_spec rv 1) as [Q2|Q2]; cbn [Z.b2z];
    try reflexivity; exfalso;
    first [ lia
          | apply E1, LX; [lia| lia|]; apply LO; lia
          | apply E2, LX; [lia| lia|]; apply LO; lia
          | assert (Z.lor (Z.lxor vin have) (Z.lxor out left) = 0) by (apply LO; split; apply LX; lia); lia ].
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section R.
  Variables (RNG : footprint) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).

  Lemma inf_retrule : forall (SPA Zs F0 S : Z) (vin out left have rv : Z) (v0 v8 v16 v24 v240 vret v328 vput v512 vnext j544 j552 : word)
      (x1 x2 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x18 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : amem)
      (K : forall (rc' : Z) (y10 y11 y12 : word),
         (rc' = rv \/ rc' = 18446744073709551611) -> (rc' = 0 -> vin <> have \/ out <> left) ->
         evtF bsegs RNG POST
           (MS (mkR x1 x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 SPA) y10 y11 y12 x13 x14 x15 x16 (Z_to_bv 64 have)
                    x18 (Z_to_bv 64 0) x20 x21 x26 x23 x24 x25 (Z_to_bv 64 rc') x27 x28 x29 x30 x31)
               FR (Z_to_bv 64 0x93a38) fc None m (seg_rom bsegs))),
    0 <= vin < 4294967296 -> 0 <= have < 4294967296 -> 0 <= out < 4294967296 -> 0 <= left < 4294967296 -> 0 <= rv < 18446744073709551616 ->
    rng RNG SPA 568 ->
    rw_cells bsegs m SPA (inf_locals S Zs F0 v0 v8 v16 v24 v240 vret v328 (Z_to_bv 64 vin) (Z_to_bv 64 out) vput (Z_to_bv 64 left) v512 vnext j544 j552) ->
    evtF bsegs RNG POST
      (MS (mkR x1 x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 have)
               x18 (Z_to_bv 64 0) x20 x21 x26 x23 x24 x25 (Z_to_bv 64 rv) x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x93a00) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros K RVIN RHAVE ROUT RLEFT RRV RFRM FRM.
    unfold inf_locals in FRM.
    do 12 zs.
    setreg 10 (Z_to_bv 64 (if ((vin =? have) && (out =? left) && (rv =? 0))%bool then 1 else 0)) ltac:(rewrite retrule_val by lia; reflexivity).
    destruct ((vin =? have) && (out =? left) && (rv =? 0))%bool eqn:NP.
    -
      zs. zs.
      rewrite <- (Z_to_bv_mod64 (-5)). change ((-5) mod 2 ^ 64) with 18446744073709551611.
      eapply K; [right; reflexivity| intros X; discriminate X].
    - zs.
      eapply K; [left; reflexivity|]. intros ->.
      destruct (Z.eqb_spec vin have) as [E1|E1]; [| left; exact E1]. destruct (Z.eqb_spec out left) as [E2|E2]; [| right; exact E2].
      cbn in NP. discriminate NP.
  Qed.

  Lemma inf_uwret : forall (SPA Zs F0 S : Z) (v0 v8 v16 v24 v240 vret v328 vin vout vput vleft v512 vnext j544 j552 : word)
      (x1 x2 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : amem)
      (K : evtF bsegs RNG POST
           (MS (mkR (Z_to_bv 64 F0) x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 SPA) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x23
                    x18 x19 x20 x23 x22 x21 x24 x25 x26 x27 x28 x29 x30 x31)
               FR (Z_to_bv 64 0x93a00) fc None m (seg_rom bsegs))),
    rng RNG SPA 568 ->
    rw_cells bsegs m SPA (inf_locals S Zs F0 v0 v8 v16 v24 v240 vret v328 vin vout vput vleft v512 vnext j544 j552) ->
    evtF bsegs RNG POST
      (MS (mkR x1 x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 SPA) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x23 x22 x21 x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x939a4) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros K RFRM FRM. unfold inf_locals in FRM.
    do 3 zs. exact K.
  Qed.
End R.

Section F.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Notation FB0 F := (mkABlock (ABFake 0) F 64).
  Hypothesis AI_fake_flag : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
    rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
    /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
    /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
    /\ ~ in_ranges CI (fflag L cls F).
  Hypothesis AI_fake_release : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
    AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).

  Variables (L : alayout) (RNG : footprint) (stA : astate) (LBr : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (m0 : amem) (payload : list Z).
  Notation SP := (bv_unsigned sp).

  Local Ltac dj12 := cbn [disjoint_from]; repeat split; try exact I; lia.

  Lemma inf_fin_epi : forall (cx : ictx) (SPA Zs F0 lo Fu : Z) (st : ist) (rc' : Z) (lf cf wf fo fw : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word)
      (h0 h1 h2 : word) (jk : list byte) (c0 c1 c2 c3 c4 c5 c6 c7 : bv 8)
      (x2 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word) (m : amem),
    inf_ctx cx (ILAY SP SPA Zs F0 lo) AI RNG (FB0 F0 :: LBr) -> no_live 0 LBr -> atmost1_c2 LBr -> strm_home LBr Fu Zs ->
    (c_w cx <> 0 -> c_q cx + c_n cx <= c_w cx \/ c_w cx + 32768 <= c_q cx) ->
    Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    rng RNG F0 64 -> rng RNG (Z.shiftr F0 3 + 2147450880) 8 ->
    sinv cx st lf cf -> inf_arr_ok cx wf fo -> 0 <= rc' < 18446744073709551616 -> (rc' = 0 -> M2 cx st < M2e cx) ->
    inf_vis cx (ILAY SP SPA Zs F0 lo) st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) zti (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (c_osz cx - t_cout st))
            zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st)) back was pad m ->
    inf_hid cx (ILAY SP SPA Zs F0 lo) AI L RNG stA (FB0 F0 :: LBr) LBr m0 fw (inf_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
            [C8 h0; C8 h1; C8 h2; CB 32 jk; C8 (Z_to_bv 64 (fflag L 0 F0))] [C1 c0; C1 c1; C1 c2; C1 c3; C1 c4; C1 c5; C1 c6; C1 c7] m ->
    evtF bsegs RNG (inf_ret AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc stA LBr cx Fu Zs lo payload m0)
      (MS (mkR (Z_to_bv 64 F0) x2 gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x24 x21 x26 x23 (Z_to_bv 64 (Z.shiftr F0 3 + 2147450880)) x25 (Z_to_bv 64 rc') (Z_to_bv 64 F0) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x93a38) fc None m (seg_rom bsegs)).
  Proof using AI_fake_flag AI_fake_release.
    intros until m. intros CTX NOL AM1 SHOME PAYW PAYR PLEN RF0 RSF0 SI ARR RRC M2C VIS HID.
    change (ibx (c_w cx <> 0 -> c_q cx + c_n cx <= c_w cx \/ c_w cx + 32768 <= c_q cx)) in PAYW.
    pose proof HID as (AH & _).
    pose proof (inf_facts AI L RNG stA _ cx _ m AH CTX) as LIN0.
    destruct (AI_fake_flag L RNG stA _ m 0 F0 64 AH ltac:(left; reflexivity)) as (FLC & RFLG & GB & GTOP & GBL & GCI).
    set (FLG := fflag L 0 F0) in *.
    pose proof SI as (RN & _ & _ & _). unfold IDefs.RNG in RN. cbv zeta in RN. destruct RN as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & _).
    pose proof CTX as (S16 & SB & (ps & HPS & PAYH) & _ & RZ & RSZ & HF0 & F064 & F0B & RS & RSS & OBE & OSZ & OCI & ROB & ROBS & WDC
                     & D1 & NR & D16 & RD & RSD & LOC & LOS & SPAR & SPA32 & SP16 & SPT & RSTK & RI & RISH & RSFU & TABC1 & TABC2 & LBABLK).
    cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
    pose proof VIS as (FRM & STRM & SSC & LENS & WORK & CODES & TAIL & OUT & PAYB & STK & MI & MNE & BKOK).
    cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
    destruct HID as (_ & SHZ & SHS & SHO & WIN & UNP & SAVED & _ & FK & _ & FKSH & _ & SUBL & CAG & SHLF & SHDF & SHOR & SHO6
                     & IT1 & IT2 & IT3 & IT4 & IT5 & IT6 & GAP & (obr & OBR) & WFU).
    cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
    unfold inf_locals in FRM. apply rw_cells_forget in FRM. destruct FRM as [jB FRB]. cbn [cells_size csize Nat.add] in FRB.
    atop_facts. unfold KEND in SPT.
    assert (ESPA : SPA = (SP - 672) - (SP - 672) mod 32) by (Z.div_mod_to_equations; lia).
    assert (F0TOP : F0 + 64 <= ATOP) by (pose proof (AI_block_bounds AI _ _ _ _ _ _ AH HF0) as (_ & _ & X); exact X).
    assert (GF : FLG + 1 <= F0 \/ F0 + 64 <= FLG) by (exact (GBL _ HF0)).
    eapply evtF_mono;
      [ eapply (inf_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo SPA RNG ltac:(lia) LOC SP16 ltac:(unfold KEND; lia) ESPA RSTK RI
                   F0 FLG F064 F0B F0TOP GB GTOP GF RF0 RSF0 RFLG);
         [exact STK| exact GAP| exact MI| exact FRB| exact SAVED| exact FK| exact FLC| exact FKSH] |].
    cbv beta. intros ms' (mp & m' & q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31
                          & -> & MU1 & WM1 & MIp & MU2 & WM2 & MI' & ST' & FLC').
    destruct LIN0 as (Fu' & ZSE & FU256 & HFU & (S1 & S2 & bS & BS0 & BS1 & BS2) & (U1 & U2 & bU & BU0 & BU1 & BU2) & (F1 & F2 & bF & BF0 & BF1 & BF2)
                     & DL1 & DL2 & (bD & BD0 & BD1 & BD2) & (cSU & CSU0 & CSU1 & CSU2) & (cSF & CSF0 & CSF1 & CSF2) & (cUF & CUF0 & CUF1 & CUF2)
                     & (cSD & CSD0 & CSD1 & CSD2) & (cUD & CUD0 & CUD1 & CUD2) & (cFD & CFD0 & CFD1 & CFD2)).
    cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
    destruct SHOME as (HFUr & ZSE2 & FUr256 & FUB). assert (Fu' = Fu) by lia. subst Fu'.
    pose proof (ablk_lin _ _ GB) as (GB1 & GB2 & GB3 & GB4). unfold AIMG_HI in GB1.
    destruct (ablk_ind _ _ GB) as (bG & BG0 & BG1 & BG2). unfold KLS in BG1.
    pose proof (GBL _ HPS) as GS. pose proof (GBL _ HFU) as GU. cbn [ab_addr ab_size] in GS, GU, GF.
    assert (GD : FLG + 1 <= c_q cx \/ c_q cx + c_n cx <= FLG).
    { destruct PAYH as [(pd & HPD & _)|(N0 & DE)]; [exact (GBL _ HPD)| lia]. }
    assert (GOB : FLG + 1 <= c_ob cx \/ c_ob cx + 262144 <= FLG).
    { destruct OCI as (iv & OCI1 & OCI2 & OCI3). destruct (Z_lt_le_dec FLG (c_ob cx)) as [X|X]; [left; lia|].
      destruct (Z_lt_le_dec FLG (c_ob cx + 262144)) as [Y|Y]; [| right; lia]. exfalso. apply GCI. exists iv. split; [exact OCI1| lia]. }
    assert (F8 : F0 mod 8 = 0) by (clear - F064; Z.div_mod_to_equations; lia).
    assert (Z8 : Zs mod 8 = 0) by (clear - ZSE2 FUr256; Z.div_mod_to_equations; lia).
    unfold A_OUTBUF in OBE.
    assert (O8 : c_ob cx mod 8 = 0) by (rewrite OBE; reflexivity).
    pose (W12 := [(Z.shiftr F0 3 + 2147450880, Z.shiftr F0 3 + 2147450880 + 8); (F0, F0 + 8); (FLG, FLG + 1)]).
    assert (MU12 : munch W12 m m').
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]];
        intros x Hx; clear - Hx; unfold W12 in *; cbn [outside] in *; tauto. }
    pose proof (wmono_trans bsegs _ _ _ WM1 WM2) as WM12.
    assert (AHp : AHEAP AI L RNG stA (FB0 F0 :: LBr) mp).
    { eapply (AI_frame AI _ _ _ _ m mp _ AH MU1 WM1).
      constructor; [cbn [fst snd]; eapply (acr_fake_sh AI _ 0 F0 64 F0 8); [exact HF0| exact F8| lia| lia| lia]|].
      constructor; [cbn [fst snd]; eapply acr_fake; [exact HF0| lia| lia]| constructor]. }
    assert (EQ : m' = write_to_mem mp (wa FLG) [Z_to_bv 8 0]).
    { apply inf_mem_eq_single; [lia| lia| exact MU2|]. apply inf_byte_of_c1; [exact FLC'| lia]. }
    assert (AH' : AHEAP AI L RNG stA LBr m') by (rewrite EQ; subst FLG; apply (AI_fake_release L RNG stA LBr mp 0 F0 64 AHp)).
    assert (OUT12 : forall a, aclient_addr CI LBr SP a -> outside W12 a).
    { intros a HC.
      destruct (inf_client_outside AI L RNG stA LBr m F0 FLG lo SP a AH ltac:(intros b Hb; apply LBABLK; right; exact Hb) F0B F8 GB GBL GCI LOC ltac:(lia) HC)
        as (O1 & O2 & O3 & O4).
      unfold W12. cbn [outside]. repeat split; try exact I; lia. }
    assert (CAG' : client_agree AI LBr SP (inf_WR cx (ILAY SP 0 Zs 0 lo)) m0 m').
    { eapply client_agree_trans; [exact CAG|]. eapply (client_agree_munch AI LBr _ _ W12 m m' MU12 WM12). intros a _ HC _. exact (OUT12 a HC). }
    clear OUT12 CAG.
    assert (SHFU : shad Fu = Z.shiftr Zs 3 + 2147450880 - 4)
      by (rewrite shad_div; unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - ZSE2 FUr256; Z.div_mod_to_equations; lia).
    assert (DJU : disjoint_from W12 (shad (c_q cx)) (shad (c_q cx + c_n cx - 1) + 1 - shad (c_q cx))).
    { unfold W12. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      clear - F8 F1 F2 BF0 BF1 BF2 DL1 DL2 BD0 BD1 BD2 CFD0 CFD1 CFD2 GB1 GB3 BG0 BG1 BG2 GD D1 NR H. repeat split; try exact I; Z.div_mod_to_equations; lia. }
    destruct (shr3_lin8 F0 ltac:(lia) F8) as (qF & EQF & QF). destruct (shr3_lin8 Zs ltac:(lia) Z8) as (qZ & EQZ & QZ).
    destruct (shr3_lin8 (c_ob cx) ltac:(lia) O8) as (qO & EQO & QO).
    unfold W12 in *. clear W12. rewrite ?EQF, ?EQZ, ?EQO in *.
    exists rc', st, lf, cf, wf, fo, zti, zto, zmsg, zopq, zdt, zadl, zres, zp1, zp2, zp3, havedict, dmax, check, total, back, was, pad.
    exists q5, q6, q7, q11, q12, q13, q14, q15, q16, q17, q28, q29, q30, q31, m'.
    split; [reflexivity|]. split; [exact RRC|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AH'|]. split; [exact CAG'|].
    split.
    {
      unfold inf_objs, strm_sh. rewrite ?EQZ, ?EQO.
      split; [split; [exact HFUr| split; [exact ZSE2| split; [exact FUr256| exact FUB]]]|].
      split.
      { split; [eapply shadow_bytes_munch; [exact SHZ| exact MU12| dj12]|]. split; [exact RZ|].
        rewrite SHFU.
        split; [eapply wr_at_transport; [exact WFU| exact WM12]| exact RSFU]. }
      split.
      { exists ps. split; [destruct HPS as [X|X]; [discriminate X| exact X]|].
        destruct PAYH as [(pd & HPD & NP & PNE)|(N0 & DE)]; [left; exists pd; split; [destruct HPD as [X|X]; [discriminate X| exact X]| split; assumption]| right; split; assumption]. }
      split.
      { destruct WDC as [W0|(_ & _ & (pw & HPW) & _)]; [left; exact W0| right; exists pw; destruct HPW as [X|X]; [discriminate X| exact X]]. }
      split; [exact NOL|]. split; [exact OBE|]. split; [exact OSZ|]. split; [exact OCI|].
      split; [eapply shadow_bytes_munch; [exact SHO| exact MU12| dj12]|].
      split; [exact ROB|]. split; [exact ROBS|]. split; [exact D1|]. split; [exact NR|]. split; [exact D16|]. split; [exact PAYR|]. split; [exact PLEN|].
      split; [eapply unpoisoned_munch; [exact UNP| exact MU12| exact DJU]|]. split; [exact RD|]. split; [exact RSD|].
      split.
      { unfold u2_tabsh.
      split; [eapply shadow_bytes_munch; [exact SHLF| exact MU12| dj12]|]. split; [eapply shadow_bytes_munch; [exact SHDF| exact MU12| dj12]|].
      split; [eapply shadow_bytes_munch; [exact SHOR| exact MU12| dj12]|]. split; [eapply shadow_bytes_munch; [exact SHO6| exact MU12| dj12]|].
      split; [eapply shadow_bytes_munch; [exact IT1| exact MU12| dj12]|]. split; [eapply shadow_bytes_munch; [exact IT2| exact MU12| dj12]|].
      split; [eapply shadow_bytes_munch; [exact IT3| exact MU12| dj12]|]. split; [eapply shadow_bytes_munch; [exact IT4| exact MU12| dj12]|].
      split; [eapply shadow_bytes_munch; [exact IT5| exact MU12| dj12]|]. eapply shadow_bytes_munch; [exact IT6| exact MU12| dj12]. }
      split; [exact AM1|]. split; [intros b Hb; apply LBABLK; right; exact Hb|]. split; [exact TABC1|]. split; [exact TABC2| exact PAYW]. }
    split; [apply ainv_of_sinv; exact SI|]. split; [exact MNE|].
    split.
    {
      assert (DJA : forall A N, 0 <= N ->
                (Zs <= A /\ A + N <= Zs + 112) \/ (c_p cx <= A /\ A + N <= c_p cx + 7176) \/ (c_ob cx <= A /\ A + N <= c_ob cx + 262144)
                \/ (c_q cx <= A /\ A + N <= c_q cx + c_n cx) ->
                disjoint_from [(qF + 2147450880, qF + 2147450880 + 8); (F0, F0 + 8); (FLG, FLG + 1)] A N).
      { clear - QF F1 F2 BF0 BF1 BF2 GB1 GB3 BG0 BG1 BG2 GF GS GU GD GOB S1 S2 BS0 BS1 BS2 U1 U2 BU0 BU1 BU2 ZSE2 CSF0 CSF1 CSF2 CUF0 CUF1 CUF2
                CFD0 CFD1 CFD2 DL1 DL2 BD0 BD1 BD2 OBE H.
        intros A N HN HR. cbn [disjoint_from]. repeat split; try exact I; lia. }
      unfold inf_emem. cbv zeta.
      split; [eapply rw_cells_transport; [exact STRM| exact MU12| exact WM12|]; unfold strm_cells; cbn [cells_size csize Nat.add];
              apply DJA; [clear; lia| left; clear; lia]|].
      split; [eapply rw_cells_transport; [exact SSC| exact MU12| exact WM12|]; unfold istate_cells; cbn [cells_size csize Nat.add];
              apply DJA; [clear; lia| right; left; clear; lia]|].
      split; [unfold f16arr in LENS |- *; eapply u16arr_transport; [exact LENS| exact MU12| exact WM12|]; rewrite fws_length;
              apply DJA; [clear; lia| right; left; clear; lia]|].
      split; [unfold f16arr in WORK |- *; eapply u16arr_transport; [exact WORK| exact MU12| exact WM12|]; rewrite fws_length;
              apply DJA; [clear; lia| right; left; clear; lia]|].
      split; [unfold f32arr in CODES |- *; eapply u32arr_transport; [exact CODES| exact MU12| exact WM12|]; rewrite fws_length;
              apply DJA; [clear; lia| right; left; clear; lia]|].
      split; [eapply rw_cells_transport; [exact TAIL| exact MU12| exact WM12|]; unfold itail_cells; cbn [cells_size csize Nat.add];
              apply DJA; [clear; lia| right; left; clear; lia]|].
      split; [unfold f8arr in OUT |- *; eapply u8arr_transport; [exact OUT| exact MU12| exact WM12|]; rewrite map_length, seq_length, Z2Nat.id by (clear - OSZ; lia);
              apply DJA; [clear - OSZ; lia| right; right; left; clear - OSZ; lia]|].
      split; [eapply bytes_at_transport; [exact PAYB| exact MU12|]; rewrite map_length, PLEN;
              apply DJA; [clear - NR; lia| right; right; right; clear; lia]|].
      split; [exact ARR|].
      split.
      { exists obr. eapply rw_cells_transport; [exact OBR| exact MU12| exact WM12|]. cbn [cells_size csize Nat.add].
        rewrite Nat.add_0_r, Z2Nat.id by (clear - OSZ; lia). apply DJA; [clear - OSZ; lia| right; right; left; clear - OSZ; lia]. }
      split; [| exact BKOK].
      intros WN. destruct (WIN WN) as (_ & FW). exists fw.
      destruct WDC as [W0|(W16 & WB & (pw & HPW) & _)]; [contradiction|].
      pose proof (ablk_lin _ _ WB) as (WB1 & WB0 & WB3 & WB4). unfold AIMG_HI in WB1.
      destruct (ablk_ind _ _ WB) as (bW & BW0 & BW1 & BW2). unfold KLS in BW1.
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH HPW HF0 ltac:(discriminate)) as DWF. cbn [ab_addr ab_size] in DWF.
      pose proof (GBL _ HPW) as GW. cbn [ab_addr ab_size] in GW.
      unfold f8arr in FW |- *. eapply u8arr_transport; [exact FW| exact MU12| exact WM12|]. rewrite map_length, seq_length.
      clear - QF F1 F2 BF0 BF1 BF2 GB1 GB3 BG0 BG1 BG2 WB1 WB0 WB3 WB4 BW0 BW1 BW2 DWF GW H.
      cbn [disjoint_from]. repeat split; try exact I; lia. }
    split; [exact M2C| eapply leave_wm; exact SI].
  Qed.

  Lemma inf_fin : forall (cx : ictx) (SPA Zs F0 lo Fu : Z) (st : ist) (rv : Z) (lf cf wf fo fw : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word)
      (h0 h1 h2 : word) (jk : list byte) (c0 c1 c2 c3 c4 c5 c6 c7 : bv 8)
      (x2 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x18 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word) (m : amem),
    inf_ctx cx (ILAY SP SPA Zs F0 lo) AI RNG (FB0 F0 :: LBr) -> no_live 0 LBr -> atmost1_c2 LBr -> strm_home LBr Fu Zs ->
    (c_w cx <> 0 -> c_q cx + c_n cx <= c_w cx \/ c_w cx + 32768 <= c_q cx) ->
    Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    0 <= c_cin0 cx <= c_n cx ->
    rng RNG F0 64 -> rng RNG (Z.shiftr F0 3 + 2147450880) 8 ->
    sinv cx st lf cf -> inf_arr_ok cx wf fo -> 0 <= rv < 18446744073709551616 ->
    inf_vis cx (ILAY SP SPA Zs F0 lo) st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) zti (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (c_osz cx - t_cout st))
            zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st)) back was pad m ->
    inf_hid cx (ILAY SP SPA Zs F0 lo) AI L RNG stA (FB0 F0 :: LBr) LBr m0 fw (inf_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
            [C8 h0; C8 h1; C8 h2; CB 32 jk; C8 (Z_to_bv 64 (fflag L 0 F0))] [C1 c0; C1 c1; C1 c2; C1 c3; C1 c4; C1 c5; C1 c6; C1 c7] m ->
    evtF bsegs RNG (inf_ret AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc stA LBr cx Fu Zs lo payload m0)
      (MS (mkR (Z_to_bv 64 F0) x2 gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (c_n cx - t_cin st))
               x18 (Z_to_bv 64 0) x24 x21 x26 x23 (Z_to_bv 64 (Z.shiftr F0 3 + 2147450880)) x25 (Z_to_bv 64 rv) (Z_to_bv 64 F0) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x93a00) fc None m (seg_rom bsegs)).
  Proof using AI_fake_flag AI_fake_release.
    intros until m. intros CTX NOL AM1 SHOME PAYW PAYR PLEN CIN0 RF0 RSF0 SI ARR RRV VIS HID.
    pose proof SI as (RN & _ & _ & _). unfold IDefs.RNG in RN. cbv zeta in RN. destruct RN as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & _).
    pose proof CTX as (S16 & SB & _ & _ & RZ & RSZ & HF0 & F064 & F0B & RS & RSS & OBE & OSZ & OCI & ROB & ROBS & WDC
                     & D1 & NR & D16 & RD & RSD & LOC & LOS & SPAR & SPA32 & SP16 & SPT & RSTK & RI & RISH & RSFU & TABC1 & TABC2 & LBABLK).
    pose proof VIS as (FRM & _). cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
    eapply (inf_retrule RNG gp tp FR fc _ SPA Zs F0 (c_p cx) (c_n cx - c_cin0 cx) (t_out st) (c_osz cx - t_cout st) (c_n cx - t_cin st) rv);
      [| lia| lia| lia| lia| exact RRV| eapply rng_sub'; [exact RSTK| lia]| exact FRM].
    intros rc' y10 y11 y12 RCV PROGRESS.
    eapply (inf_fin_epi cx SPA Zs F0 lo Fu st rc' lf cf wf fo fw); try eassumption.
    - destruct RCV as [->| ->]; lia.
    - intros RC0. eapply leave_progress; [exact SI| exact CIN0| lia|]. apply PROGRESS. exact RC0.
  Qed.
End F.
End CANSEC1.
