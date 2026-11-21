(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AShadow U2AArr InfPure.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj U2BIface U2BGlue InfBBase InfBIface InfBGlueE InfBGlueU InfPureB_leave.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition hidP (P : Prop) : Prop := P.

Section CANSEC1. Context {rc : runConstT}.
Section T.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Notation FB0 F := (mkABlock (ABFake 0) F 64).

  Lemma uw_rebuild : forall (L : alayout) (RNG RNG' : footprint) (stA stA' : astate) (LBr LBr' : list ablock) (m0 : amem) (payload : list Z)
      (cx : ictx) (SP SPA Zs F0 lo Fu : Z) (st : ist) (lf cf wf fo fw : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word)
      (saved fk fksh : list cell) (m2 m' : amem) (W' wn' wh' : Z) (wbytes' : list byte),
    inf_ctx cx (ILAY SP SPA Zs F0 lo) AI RNG (FB0 F0 :: LBr) -> sinv cx st lf cf ->
    inf_vis cx (ILAY SP SPA Zs F0 lo) st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) zti (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (c_osz cx - t_cout st))
            zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st)) back was pad m2 ->
    inf_hid cx (ILAY SP SPA Zs F0 lo) AI L RNG stA (FB0 F0 :: LBr) LBr m0 fw saved fk fksh m2 ->
    strm_home LBr Fu Zs -> Z.of_nat (length payload) = c_n cx ->
    fp_le RNG RNG' -> W' <> 0 -> (c_w cx = W' \/ c_w cx = 0) ->
    (exists pw, In (HB pw W' 32768) LBr') -> (forall b, In b LBr -> In b LBr') ->
    (forall b, In b LBr' -> In b LBr \/ exists pw, b = HB pw W' 32768) ->
    0 <= wh' <= 32768 -> 0 <= wn' < 32768 -> (wh' < 32768 -> wn' = wh') ->
    (c_q cx + c_n cx <= W' \/ W' + 32768 <= c_q cx) ->
    mem_inv bsegs m' -> stk bsegs m' lo SPA ->
    client_agree AI (FB0 F0 :: LBr) SPA [(c_p cx + 68, c_p cx + 96); (W', W' + 32768)] m2 m' ->
    AHEAP AI L RNG' stA' (FB0 F0 :: LBr') m' ->
    rw_cells bsegs m' (c_p cx) (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 (t_mode st)) (Z_to_bv 64 (t_last st)) (Z_to_bv 64 5) havedict
                                       (Z_to_bv 64 (t_flags st)) dmax check total (Z_to_bv 64 0) (Z_to_bv 64 15) (Z_to_bv 64 32768)
                                       (Z_to_bv 64 wh') (Z_to_bv 64 wn') (Z_to_bv 64 W') (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st))
                                       (Z_to_bv 64 (t_length st)) (Z_to_bv 64 (t_offset st)) (Z_to_bv 64 (t_extra st))
                                       (Z_to_bv 64 (cp_addrA (c_p cx) (t_lc st))) (Z_to_bv 64 (cp_addrA (c_p cx) (t_dc st)))
                                       (Z_to_bv 64 (t_lb st)) (Z_to_bv 64 (t_db st)) (Z_to_bv 64 (t_ncode st)) (Z_to_bv 64 (t_nlen st))
                                       (Z_to_bv 64 (t_ndist st)) (Z_to_bv 64 (t_shave st)) (Z_to_bv 64 (c_p cx + 1384 + 4 * t_nx st))) ->
    rw_cells bsegs m' W' [CB (Z.to_nat 32768) wbytes'] ->
    inf_ctx (with_win cx W') (ILAY SP SPA Zs F0 lo) AI RNG' (FB0 F0 :: LBr')
    /\ sinv (with_win cx W') (set_win st wh' wn') lf cf
    /\ inf_vis (with_win cx W') (ILAY SP SPA Zs F0 lo) (set_win st wh' wn') lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) zti (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (c_osz cx - t_cout st))
            zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st)) back was pad m'
    /\ inf_hid (with_win cx W') (ILAY SP SPA Zs F0 lo) AI L RNG' stA' (FB0 F0 :: LBr') LBr' m0
               (fun i => bv_unsigned (nth (Z.to_nat i) wbytes' (Z_to_bv 8 0))) saved fk fksh m'.
  Proof.
    intros until wbytes'. intros CTX SI VIS HID SHOME PLEN FPLE WN WOLD (pw & HPW) SUBR NEWR WH1 WN1 WHN DWP MI' STK' CAGU AH' SSC' WBLOB.
    destruct CTX as (S16 & SB & (ps & HPS & PAYH) & _ & RZ & RSZ & HF0 & F064 & F0B & RS & RSS & OBE & OSZ & OCI & ROB & ROBS & WDC
                     & D1 & NR & D16 & RD & RSD & LOC & LOS & SPAR & SPA32 & SP16 & SPT & RSTK & RI & RISH & RSFU & TABC1 & TABC2 & LBABLK).
    cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
    destruct VIS as (FRM & STRM & SSC & LENS & WORK & CODES & TAIL & OUT & PAYB & STK & MI & MNE & BKOK). cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
    destruct HID as (AH & SHZ & SHS & SHO & WIN & UNP & SAVED & SZ1 & FK & SZ2 & FKSH & SZ3 & SUBL & CAG & SHLF & SHDF & SHOR & SHO6
                     & IT1 & IT2 & IT3 & IT4 & IT5 & IT6 & GAP & (obr & OBR) & WFU).
    cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
    destruct SHOME as (HFUr & ZSE & FU256 & FUB).
    atop_facts. unfold KEND in SPT. unfold A_OUTBUF in OBE.
    assert (SUB' : forall b, In b (FB0 F0 :: LBr) -> In b (FB0 F0 :: LBr')) by (intros b [E|Hb]; [left; exact E| right; apply SUBR; exact Hb]).
    assert (HPW' : In (HB pw W' 32768) (FB0 F0 :: LBr')) by (right; exact HPW).
    assert (HPS' : In (HB ps (c_p cx) 7176) (FB0 F0 :: LBr')) by (apply SUB'; exact HPS).
    assert (HFU : In (mkABlock (ABFake 2) Fu 256) (FB0 F0 :: LBr)) by (right; exact HFUr).
    assert (HFU' : In (mkABlock (ABFake 2) Fu 256) (FB0 F0 :: LBr')) by (apply SUB'; exact HFU).
    assert (HF0' : In (FB0 F0) (FB0 F0 :: LBr')) by (left; reflexivity).
    pose proof (AI_block AI _ _ _ _ _ pw W' 32768 AH' HPW') as (_ & (WB & _ & WB3 & W16) & RW & RSW0 & BSHW & _).
    pose proof (ablk_lin _ _ WB) as (WB1 & WB2 & _ & WB4). unfold AIMG_HI in WB1.
    pose proof (AI_block AI _ _ _ _ _ ps (c_p cx) 7176 AH' HPS') as (_ & _ & _ & _ & BSHS & _).
    pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). unfold AIMG_HI in SB1.
    pose proof (ablk_lin _ _ FUB) as (FUB1 & FUB2 & FUB3 & FUB4). unfold AIMG_HI in FUB1.
    pose proof (ablk_lin _ _ F0B) as (F0B1 & F0B2 & F0B3 & F0B4). unfold AIMG_HI in F0B1.
    assert (DISW : forall b, In b (FB0 F0 :: LBr') -> b <> HB pw W' 32768 -> ab_addr b + ab_size b <= W' \/ W' + 32768 <= ab_addr b).
    { intros b Hb NE. pose proof (AI_blocks_disjoint AI _ _ _ _ _ b (HB pw W' 32768) AH' Hb HPW' NE) as X. cbn [ab_addr ab_size] in X. lia. }
    pose proof (DISW _ HFU' ltac:(discriminate)) as DWU. pose proof (DISW _ HF0' ltac:(discriminate)) as DWF. cbn [ab_addr ab_size] in DWU, DWF.
    assert (DWS : c_p cx + 7176 <= W' \/ W' + 32768 <= c_p cx).
    { destruct (N.eq_dec ps pw) as [E|NE].
      - subst ps. pose proof (hb_same_id _ pw (c_p cx) 7176 W' 32768 (AI_hb_ids AI _ _ _ _ _ AH') HPS' HPW') as Q. inversion Q.
      - pose proof (DISW _ HPS' ltac:(intros Q; inversion Q; contradiction)) as X. cbn [ab_addr ab_size] in X. exact X. }
    pose proof (ablk_disj_band _ _ WB) as BW. pose proof (ablk_disj_band _ _ SB) as BS. unfold KLS in BW, BS.
    assert (DISS : forall b, In b (FB0 F0 :: LBr) -> b <> HB ps (c_p cx) 7176 -> ab_addr b + ab_size b <= c_p cx \/ c_p cx + 7176 <= ab_addr b).
    { intros b Hb NE. pose proof (AI_blocks_disjoint AI _ _ _ _ _ b (HB ps (c_p cx) 7176) AH Hb HPS NE) as X. cbn [ab_addr ab_size] in X. lia. }
    pose proof (DISS _ HFU ltac:(discriminate)) as DSU. pose proof (DISS _ HF0 ltac:(discriminate)) as DSF. cbn [ab_addr ab_size] in DSU, DSF.
    assert (DSD : c_q cx + c_n cx <= c_p cx \/ c_p cx + 7176 <= c_q cx).
    { destruct PAYH as [(pd & HPD & NP & PNE)|(N0 & DE)]; [| lia].
      pose proof (DISS _ HPD ltac:(intros E; inversion E; contradiction)) as X. cbn [ab_addr ab_size] in X. exact X. }
    destruct OCI as (ivO & OCI1 & OCI2 & OCI3). destruct TABC1 as (ivT1 & T11 & T12 & T13). destruct TABC2 as (ivT2 & T21 & T22 & T23).
    set (PU := fun a : Z => aclient_addr CI (FB0 F0 :: LBr) SPA a /\ ~ in_ranges [(c_p cx + 68, c_p cx + 96); (W', W' + 32768)] a).
    assert (NWR : forall a, (a < c_p cx + 68 \/ c_p cx + 96 <= a) -> (a < W' \/ W' + 32768 <= a) ->
                            ~ in_ranges [(c_p cx + 68, c_p cx + 96); (W', W' + 32768)] a).
    { intros a H1 H2 (iv & [E|[E|[]]] & Hr); subst iv; cbn [fst snd] in Hr; lia. }
    assert (PK : forall a, SPA <= a < SP -> PU a).
    { intros a Ha. split; [left; clear - Ha SPT; lia| apply NWR; [clear - Ha SB3 H LOC LOS; lia| clear - Ha WB3 H LOC LOS; lia]]. }
    assert (PZ : forall a, Fu <= a < Fu + 256 -> PU a).
    { intros a Ha. split; [right; right; left; exists (mkABlock (ABFake 2) Fu 256); split; [exact HFU| cbn [ab_addr ab_size]; exact Ha]|].
      apply NWR; [clear - Ha DSU; lia| clear - Ha DWU; lia]. }
    assert (PS : forall a, c_p cx + 96 <= a < c_p cx + 7176 -> PU a).
    { intros a Ha. split; [right; right; left; exists (HB ps (c_p cx) 7176); split; [exact HPS| cbn [ab_addr ab_size]; clear - Ha; lia]|].
      apply NWR; [clear - Ha; lia| clear - Ha DWS; lia]. }
    assert (PO : forall a, c_ob cx <= a < c_ob cx + 262144 -> PU a).
    { intros a Ha. split; [right; left; exists ivO; split; [exact OCI1| clear - Ha OCI2 OCI3; lia]|].
      apply NWR; [clear - Ha OBE SB1; lia| clear - Ha OBE WB1; lia]. }
    assert (PF : forall a, F0 <= a < F0 + 64 -> PU a).
    { intros a Ha. split; [right; right; left; exists (FB0 F0); split; [exact HF0| cbn [ab_addr ab_size]; exact Ha]|].
      apply NWR; [clear - Ha DSF; lia| clear - Ha DWF; lia]. }
    assert (PSHX : forall a' a, 0 <= a' < 2 ^ 47 -> a = shad a' ->
                   ((ATOP <= a' < 2 ^ 47) \/ in_ranges CI a' \/ in_fake (FB0 F0 :: LBr) a') -> PU a).
    { intros a' a R47 -> HC. split; [right; right; right; exists a'; split; [exact HC| reflexivity]|].
      pose proof (shad_in_band a' R47) as SBD. unfold KLS in SBD. apply NWR; [clear - SBD BS; lia| clear - SBD BW; lia]. }
    assert (PSHF : forall c F n s1 s2, In (mkABlock (ABFake c) F n) (FB0 F0 :: LBr) -> F <= 8 * (s1 - 2147450880) -> 8 * (s2 - 2147450880) <= F + n ->
                   forall a, s1 <= a < s2 -> PU a).
    { intros c F n s1 s2 Hb H1 H2 a Ha.
      pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hb) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3. unfold AIMG_HI in B1.
      apply (PSHX (8 * (a - ASHOFF)) a); [unfold ASHOFF; clear - Ha H1 H2 B1 B3 H; lia| symmetry; apply shad_unshad|].
      right. right. exists c, F, n. split; [exact Hb| unfold ASHOFF; clear - Ha H1 H2; lia]. }
    assert (PSHC : forall iv s1 s2, In iv CI -> fst iv <= 8 * (s1 - 2147450880) -> 8 * (s2 - 2147450880) <= snd iv ->
                   forall a, s1 <= a < s2 -> PU a).
    { intros iv s1 s2 Hiv H1 H2 a Ha. pose proof (AI_aci_img AI iv Hiv) as I1. pose proof (AI_aci_lo AI iv Hiv) as I2. unfold AIMG_HI in I1.
      apply (PSHX (8 * (a - ASHOFF)) a); [unfold ASHOFF; clear - Ha H1 H2 I1 I2; lia| symmetry; apply shad_unshad|].
      right. left. exists iv. split; [exact Hiv| unfold ASHOFF; clear - Ha H1 H2; lia]. }
    unfold client_agree in CAGU. fold PU in CAGU.
    clear DWU DWF DWS DSU DSF BW BS DISW DISS.
    change (hidP (c_q cx + c_n cx <= c_p cx \/ c_p cx + 7176 <= c_q cx)) in DSD. change (hidP (c_q cx + c_n cx <= W' \/ W' + 32768 <= c_q cx)) in DWP.
    change (hidP (c_w cx = W' \/ c_w cx = 0)) in WOLD. change (hidP (wh' < 32768 -> wn' = wh')) in WHN.
    assert (Z8 : Zs mod 8 = 0) by (clear - ZSE FU256; Z.div_mod_to_equations; lia).
    assert (F8 : F0 mod 8 = 0) by (clear - F064; Z.div_mod_to_equations; lia).
    assert (S8 : c_p cx mod 8 = 0) by (clear - S16; Z.div_mod_to_equations; lia).
    assert (W8 : W' mod 8 = 0) by (clear - W16; Z.div_mod_to_equations; lia).
    assert (O8 : c_ob cx mod 8 = 0) by (rewrite OBE; reflexivity).
    destruct (shr3_lin8 Zs ltac:(lia) Z8) as (qZ & EQZ & QZ). destruct (shr3_lin8 F0 ltac:(lia) F8) as (qF & EQF & QF).
    destruct (shr3_lin8 (c_ob cx) ltac:(lia) O8) as (qO & EQO & QO).
    assert (FRM' := rw_cells_magree bsegs PU m2 m' SPA _ CAGU FRM).
    assert (STRM' := rw_cells_magree bsegs PU m2 m' Zs _ CAGU STRM).
    assert (TAIL' := rw_cells_magree bsegs PU m2 m' (c_p cx + 7160) _ CAGU TAIL).
    assert (SAVED' := rw_cells_magree bsegs PU m2 m' (SP + -104) _ CAGU SAVED).
    assert (FK' := rw_cells_magree bsegs PU m2 m' F0 _ CAGU FK).
    assert (FKSH' := rw_cells_magree bsegs PU m2 m' (Z.shiftr F0 3 + 2147450880) _ CAGU FKSH).
    assert (OBR' := rw_cells_magree bsegs PU m2 m' (c_ob cx + c_osz cx) _ CAGU OBR).
    unfold inf_locals in FRM'. unfold strm_cells in STRM'. unfold itail_cells in TAIL'. rewrite SZ1 in SAVED'. rewrite SZ2 in FK'. rewrite SZ3 in FKSH'.
    cbn [cells_size csize Nat.add] in FRM', STRM', TAIL', OBR'. rewrite Nat.add_0_r, Z2Nat.id in OBR' by (clear - OSZ; lia).
    specialize (FRM' ltac:(intros a Ha; apply PK; clear - Ha SPAR; lia)).
    specialize (STRM' ltac:(intros a Ha; apply PZ; clear - Ha ZSE; lia)).
    specialize (TAIL' ltac:(intros a Ha; apply PS; clear - Ha; lia)).
    specialize (SAVED' ltac:(intros a Ha; apply PK; clear - Ha SPAR; lia)).
    specialize (FK' ltac:(intros a Ha; apply PF; clear - Ha; lia)).
    specialize (FKSH' ltac:(intros a Ha; rewrite EQF in Ha; apply (PSHF 0 F0 64 (qF + 2147450880) (qF + 2147450880 + 8) HF0); [clear - QF; lia| clear - QF; lia| exact Ha])).
    specialize (OBR' ltac:(intros a Ha; apply PO; clear - Ha OSZ; lia)).
    assert (LENS' : f16arr bsegs m' (c_p cx + 168) 320 lf).
    { destruct LENS as [HB HW]. split; [eapply bytes_at_magree; [exact CAGU| exact HB|]| eapply wr_at_magree; [exact CAGU| exact HW|]];
        rewrite ?u16s_length, ?fws_length; intros a Ha; apply PS; clear - Ha; lia. }
    assert (WORK' : f16arr bsegs m' (c_p cx + 808) 288 wf).
    { destruct WORK as [HB HW]. split; [eapply bytes_at_magree; [exact CAGU| exact HB|]| eapply wr_at_magree; [exact CAGU| exact HW|]];
        rewrite ?u16s_length, ?fws_length; intros a Ha; apply PS; clear - Ha; lia. }
    assert (CODES' : f32arr bsegs m' (c_p cx + 1384) 1444 cf).
    { destruct CODES as [HB HW]. split; [eapply bytes_at_magree; [exact CAGU| exact HB|]| eapply wr_at_magree; [exact CAGU| exact HW|]];
        rewrite ?u32s_length, ?fws_length; intros a Ha; apply PS; clear - Ha; lia. }
    assert (OUT' : f8arr bsegs m' (c_ob cx) (Z.to_nat (c_osz cx)) fo).
    { destruct OUT as [HB HW]. split; [eapply bytes_at_magree; [exact CAGU| exact HB|]| eapply wr_at_magree; [exact CAGU| exact HW|]];
        rewrite ?length_map, ?length_seq; intros a Ha; apply PO; clear - Ha OSZ; lia. }
    assert (PAYB' : bytes_at bsegs m' (c_q cx) (map (Z_to_bv 8) payload)).
    { destruct PAYH as [(pd & HPD & NP & PNE)|(N0 & DE)].
      - eapply bytes_at_magree; [exact CAGU| exact PAYB|]. rewrite length_map, PLEN. intros a Ha.
        split; [right; right; left; exists (HB pd (c_q cx) (c_n cx)); split; [exact HPD| cbn [ab_addr ab_size]; exact Ha]|].
        apply NWR; [unfold hidP in DSD; clear - Ha DSD; lia| unfold hidP in DWP; clear - Ha DWP; lia].
      - destruct payload as [|c pl]; [| cbn [length] in PLEN; lia]. cbn [map]. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia. }
    assert (GAP' : stk bsegs m' (SPA + 568) (SP + -104)) by (eapply stk_magree; [exact CAGU| exact GAP|]; intros a Ha; apply PK; clear - Ha SPAR; lia).
    assert (WFU' : wr_at bsegs m' (Z.shiftr Zs 3 + 2147450880 - 4) 32).
    { eapply wr_at_magree; [exact CAGU| exact WFU|]. rewrite EQZ. intros a Ha.
      apply (PSHF 2 Fu 256 (qZ + 2147450880 - 4) (qZ + 2147450880 - 4 + 32) HFU); [clear - QZ ZSE; lia| clear - QZ ZSE; lia| exact Ha]. }
    assert (SHZ' : shadow_bytes m' (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0)).
    { eapply shadow_bytes_magree; [exact CAGU| exact SHZ|]. rewrite EQZ. intros a Ha.
      apply (PSHF 2 Fu 256 (qZ + 2147450880) (qZ + 2147450880 + 14) HFU); [clear - QZ ZSE; lia| clear - QZ ZSE; lia| exact Ha]. }
    assert (SHO' : shadow_bytes m' (Z.shiftr (c_ob cx) 3 + 2147450880) (Z.shiftr (c_ob cx) 3 + 2147450880 + 32768) (fun _ => 0)).
    { eapply shadow_bytes_magree; [exact CAGU| exact SHO|]. rewrite EQO. intros a Ha.
      apply (PSHC ivO (qO + 2147450880) (qO + 2147450880 + 32768) OCI1); [clear - QO OCI2; lia| clear - QO OCI3; lia| exact Ha]. }
    assert (TABX : forall q1 q2 f, ((2147468552 <= q1 /\ q2 <= 2147469916) \/ (2147469532 <= q1 /\ q2 <= 2147469576)) ->
                   shadow_bytes m2 q1 q2 f -> shadow_bytes m' q1 q2 f).
    { intros q1 q2 f HR SB0. eapply shadow_bytes_magree; [exact CAGU| exact SB0|]. intros a Ha.
      destruct HR as [HR|HR]; [apply (PSHC ivT1 q1 q2 T11); [clear - HR T12; lia| clear - HR T13; lia| exact Ha]
                              | apply (PSHC ivT2 q1 q2 T21); [clear - HR T22; lia| clear - HR T23; lia| exact Ha]]. }
    assert (SHS' : shadow_bytes m' (Z.shiftr (c_p cx) 3 + 2147450880) (Z.shiftr (c_p cx) 3 + 2147450880 + 897) (fun _ => 0)).
    { change 897 with (7176 / 8). apply ablock_sh0; [exact BSHS| reflexivity| lia| lia| lia]. }
    assert (SHW' : shadow_bytes m' (Z.shiftr W' 3 + 2147450880) (Z.shiftr W' 3 + 2147450880 + 4096) (fun _ => 0)).
    { change 4096 with (32768 / 8). apply ablock_sh0; [exact BSHW| reflexivity| lia| lia| lia]. }
    assert (UNP' : unpoisoned m' (c_q cx) (c_q cx + c_n cx)).
    { destruct PAYH as [(pd & HPD & NP & PNE)|(N0 & DE)].
      - pose proof (AI_block AI _ _ _ _ _ pd (c_q cx) (c_n cx) AH' (SUB' _ HPD)) as (_ & _ & _ & _ & BSHD & _).
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AH HPD) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
        apply ablock_unpoisoned; [exact BSHD| clear - D16; Z.div_mod_to_equations; lia| clear - D1; lia| clear - NR; lia| clear - B3 H; lia].
      - destruct UNP as (U1 & U2 & _). split; [exact U1|]. split; [exact U2|]. intros G HG. exfalso. clear - HG N0. lia. }
    assert (WSZ' : wsz (with_win cx W') = 32768).
    { unfold wsz, with_win. cbn [c_w]. destruct (Z.eqb_spec W' 0); [contradiction| reflexivity]. }
    split.
    {
      unfold inf_ctx, with_win. cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc l_SP l_SPA l_Zs l_F0 l_lo].
      split; [exact S16|]. split; [exact SB|].
      split. { exists ps. split; [exact HPS'|]. destruct PAYH as [(pd & HPD & NP & PNE)|ND]; [left; exists pd; split; [apply SUB'; exact HPD| split; assumption]| right; exact ND]. }
      split; [exists Fu; split; [exact HFU'| split; [exact ZSE| split; [exact FU256| exact FUB]]]|].
      split; [eapply rng_fp_le; [exact FPLE| exact RZ]|]. split; [eapply rng_fp_le; [exact FPLE| exact RSZ]|].
      split; [exact HF0'|]. split; [exact F064|]. split; [exact F0B|].
      split; [eapply rng_fp_le; [exact FPLE| exact RS]|]. split; [eapply rng_fp_le; [exact FPLE| exact RSS]|].
      split; [exact OBE|]. split; [exact OSZ|]. split; [exists ivO; split; [exact OCI1| split; [exact OCI2| exact OCI3]]|].
      split; [eapply rng_fp_le; [exact FPLE| exact ROB]|]. split; [eapply rng_fp_le; [exact FPLE| exact ROBS]|].
      split. { right. split; [exact W16|]. split; [exact WB|]. split; [exists pw; exact HPW'|]. split; [exact RW|].
               eapply rng_sub'; [exact RSW0|]. rewrite shadE. change (shlen (32768 + 7)) with 4096. lia. }
      split; [exact D1|]. split; [exact NR|]. split; [exact D16|].
      split; [eapply rng_fp_le; [exact FPLE| exact RD]|]. split; [eapply rng_fp_le; [exact FPLE| exact RSD]|].
      split; [exact LOC|]. split; [exact LOS|]. split; [exact SPAR|]. split; [exact SPA32|]. split; [exact SP16|]. split; [unfold KEND; exact SPT|].
      split; [eapply rng_fp_le; [exact FPLE| exact RSTK]|]. split; [eapply rng_fp_le; [exact FPLE| exact RI]|]. split; [eapply rng_fp_le; [exact FPLE| exact RISH]|].
      split; [eapply rng_fp_le; [exact FPLE| exact RSFU]|].
      split; [exists ivT1; split; [exact T11| split; [exact T12| exact T13]]|]. split; [exists ivT2; split; [exact T21| split; [exact T22| exact T23]]|].
      intros b [<-|Hb]; [cbn [ab_addr ab_size]; exact F0B|].
      destruct (NEWR b Hb) as [X|(pw' & ->)]; [apply LBABLK; right; exact X| cbn [ab_addr ab_size]; exact WB]. }
    split; [unfold hidP in WHN; apply sinv_with_win; assumption|].
    split.
    {
      unfold inf_vis, with_win, set_win. cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc l_SP l_SPA l_Zs l_F0 l_lo
        t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext].
      fold (with_win cx W'). rewrite WSZ'.
      split; [exact FRM'|]. split; [exact STRM'|]. split; [exact SSC'|]. split; [exact LENS'|]. split; [exact WORK'|]. split; [exact CODES'|].
      split; [exact TAIL'|]. split; [exact OUT'|]. split; [exact PAYB'|]. split; [exact STK'|]. split; [exact MI'|]. split; [exact MNE| exact BKOK]. }
    unfold inf_hid, with_win. cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc l_SP l_SPA l_Zs l_F0 l_lo].
    split; [exact AH'|]. split; [exact SHZ'|]. split; [exact SHS'|]. split; [exact SHO'|].
    split; [intros _; split; [exact SHW'| apply blob_f8arr; exact WBLOB]|].
    split; [exact UNP'|]. split; [exact SAVED'|]. split; [exact SZ1|]. split; [exact FK'|]. split; [exact SZ2|]. split; [exact FKSH'|]. split; [exact SZ3|].
    split; [intros b Hb; right; exact Hb|].
    split.
    {
      unfold client_agree in CAG |- *. unfold inf_WR in CAG |- *.
      cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc l_SP l_SPA l_Zs l_F0 l_lo] in CAG |- *.
      assert (NOTW : forall a, ~ in_ranges [(Zs, Zs + 112); (c_p cx, c_p cx + 7176); (c_ob cx, c_ob cx + c_osz cx); (W', W' + 32768); (0, 32768)] a ->
                     forall b, In b LBr' -> ab_addr b <= a < ab_addr b + ab_size b -> In b LBr).
      { intros a HN b Hb Hr. destruct (NEWR b Hb) as [X|(pw' & ->)]; [exact X|]. exfalso. apply HN.
        exists (W', W' + 32768). split; [right; right; right; left; reflexivity| exact Hr]. }
      assert (CLI : forall a, aclient_addr CI LBr' SP a ->
                     ~ in_ranges [(Zs, Zs + 112); (c_p cx, c_p cx + 7176); (c_ob cx, c_ob cx + c_osz cx); (W', W' + 32768); (0, 32768)] a ->
                     aclient_addr CI LBr SP a).
      { intros a HC HN. destruct HC as [X|[X|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
        - left; exact X.
        - right; left; exact X.
        - right; right; left. exists b. split; [exact (NOTW a HN b Hb Hr)| exact Hr].
        - right; right; right. exists a'. split; [| reflexivity].
          destruct Ha' as [X|[X|(c & A & k & Hb & Hr)]]; [left; exact X| right; left; exact X| right; right].
          exists c, A, k. split; [| exact Hr]. destruct (NEWR _ Hb) as [X|(pw' & E)]; [exact X| discriminate E]. }
      eapply magree_trans.
      - eapply magree_mono; [exact CAG|]. intros a (HC & HN). split; [exact (CLI a HC HN)|].
        intros (iv & Hiv & Hr). apply HN. unfold hidP in WOLD.
        destruct Hiv as [<-|[<-|[<-|[<-|[<-|[]]]]]].
        + exists (Zs, Zs + 112). split; [left; reflexivity| exact Hr].
        + exists (c_p cx, c_p cx + 7176). split; [right; left; reflexivity| exact Hr].
        + exists (c_ob cx, c_ob cx + c_osz cx). split; [right; right; left; reflexivity| exact Hr].
        + destruct WOLD as [E|E]; rewrite E in Hr.
          * exists (W', W' + 32768). split; [right; right; right; left; reflexivity| exact Hr].
          * exists (0, 32768). split; [right; right; right; right; left; reflexivity| exact Hr].
        + exists (0, 32768). split; [right; right; right; right; left; reflexivity| exact Hr].
      - eapply magree_mono; [exact CAGU|]. intros a (HC & HN). unfold PU. split.
        + pose proof (CLI a HC HN) as HC'. destruct HC' as [X|[X|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
          * left. clear - X SPAR. lia.
          * right; left; exact X.
          * right; right; left. exists b. split; [right; exact Hb| exact Hr].
          * right; right; right. exists a'. split; [| reflexivity].
            destruct Ha' as [X|[X|(c & A & k & Hb & Hr)]]; [left; exact X| right; left; exact X| right; right]. exists c, A, k. split; [right; exact Hb| exact Hr].
        + intros (iv & [<-|[<-|[]]] & Hr); apply HN; cbn [fst snd] in Hr.
          * exists (c_p cx, c_p cx + 7176). split; [right; left; reflexivity| cbn [fst snd]; clear - Hr; lia].
          * exists (W', W' + 32768). split; [right; right; right; left; reflexivity| exact Hr]. }
    split; [apply TABX; [left; lia| exact SHLF]|]. split; [apply TABX; [left; lia| exact SHDF]|].
    split; [apply TABX; [left; lia| exact SHOR]|]. split; [apply TABX; [left; lia| exact SHO6]|].
    split; [apply TABX; [right; lia| exact IT1]|]. split; [apply TABX; [right; lia| exact IT2]|].
    split; [apply TABX; [right; lia| exact IT3]|]. split; [apply TABX; [right; lia| exact IT4]|].
    split; [apply TABX; [right; lia| exact IT5]|]. split; [apply TABX; [right; lia| exact IT6]|].
    split; [exact GAP'|]. split; [exists obr; exact OBR'| exact WFU'].
  Qed.
End T.
End CANSEC1.
