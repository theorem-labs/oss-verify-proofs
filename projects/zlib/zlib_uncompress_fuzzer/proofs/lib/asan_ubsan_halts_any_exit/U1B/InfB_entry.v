(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2ABlob InfPure InfPure_entry.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BObj U2BIface U2BGlue InfBBase InfBIface InfBGlueE InfB_pro InfB_hdr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section T.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis SM0 : SM0_stmt AI fflag rng_fs.
  Hypothesis AI_fake_flag : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
    rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
    /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
    /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
    /\ ~ in_ranges CI (fflag L cls F).
  Notation FB0 F := (mkABlock (ABFake 0) F 64).

  Lemma inf_entry : forall (L : alayout) (RNG : footprint)
      (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (FR : bvmap 5 word) (fc : bv 32) (m : amem) (stA : astate) (LB : list ablock) (cx : ictx) (Fu Zs lo : Z) (payload : list Z)
      (st : ist) (lf cf wf fo : Z -> Z)
      (zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word) (POST : machine_state -> Prop)
      (K : forall (F0 SPA : Z) (fw : Z -> Z) (jk : list byte) (v0 v8 v16 v24 v240 v328 v512 j544 j552 : word)
                  (y6 y7 y10 y11 y12 y13 y14 y16 y19 y21 y22 y23 y26 y28 y29 y30 y31 : word) (m1 : amem),
         inf_ctx cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) AI RNG (FB0 F0 :: LB) ->
         rng RNG F0 64 -> rng RNG (Z.shiftr F0 3 + 2147450880) 8 ->
         SPA = (bv_unsigned sp - 672) - (bv_unsigned sp - 672) mod 32 ->
         inf_vis cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) (st_load cx st) lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552
                 (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) zti (Z_to_bv 64 (c_ob cx + t_cout st))
                 (Z_to_bv 64 (c_osz cx - t_cout st)) zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total
                 (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st)) back was pad m1 ->
         inf_hid cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) AI L RNG stA (FB0 F0 :: LB) LB m fw
                 (inf_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) (F0_cells jk (Z_to_bv 64 (fflag L 0 F0))) F0_shadow m1 ->
         evtF bsegs RNG POST (DISP_MS cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) gp tp FR fc (st_load cx st) y6 y7 y10 y11 y12 y13 y14 y16 y19 y21 y22 y23 y26 y28 y29 y30 y31 m1)),
    AHEAP AI L RNG stA LB m ->
    inf_objs AI RNG LB cx Fu Zs payload m ->
    ainv cx st lf cf -> t_mode st <> MEM -> c_cin0 cx = t_cin st -> c_cout0 cx = t_cout st -> c_W0 cx = Wm cx st ->
    inf_emem cx Zs st lf cf wf fo payload zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m ->
    u2_img m ->
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - INF_STACK ->
    bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 < al_top L ->
    mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
    evtF bsegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Zs) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 A_INFLATE) fc None m (seg_rom bsegs)).
  Proof using SM0 AI_fake_flag.
    intros until POST. intros K AH OBJ AINV MNE CIN0 COUT0 CW0 EM UIMG ST LOC LOS SP16 TOPS MI TP RSTK0 RI RISH RFS.
    set (SP := bv_unsigned sp) in *.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. change (2 ^ Z.of_N 64) with (2^64) in RSP. fold SP in RSP.
    atop_facts. unfold INF_STACK in LOS.
    set (SPA := (SP - 672) - (SP - 672) mod 32).
    assert (SPAB : SP - 688 <= SPA <= SP - 672 /\ SPA mod 32 = 0) by (subst SPA; Z.div_mod_to_equations; lia).
    assert (SPT : SP + 16 < KEND) by (unfold KEND; lia).
    assert (RSTK : rng RNG lo (SP - lo)) by (eapply rng_sub'; [exact RSTK0| lia]).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (USPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (AI_rtcells AI _ _ _ _ _ AH) as ART. unfold artcells in ART.
    destruct ART as (_ & GOT & _ & _ & SHB & SUAR & _).
    eapply evtF_cut.
    { eapply (inf_pro ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc Zs lo SPA RNG ltac:(fold SP; lia) LOC SP16 SPT eq_refl RSTK RI);
        [exact ST| exact MI| exact GOT| exact SHB| exact UIMG| exact SUAR]. }
    cbv beta. intros ms1 (m1 & jA & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1). fold SP in MU1, FRB1, STG1.
    assert (AH1 : AHEAP AI L RNG stA LB m1).
    { eapply (AI_frame AI _ _ _ _ m m1 _ AH MU1 WM1). constructor; [cbn [fst snd]; apply acr_stack; lia| constructor]. }
    destruct OBJ as (SHOME & SSH & BLK & WBLK & NOL & OBE & OSZ & OCI & SHO & ROB & ROBS & D1 & NR & D16 & PAYR & PLEN & UNP & RD & RSD & TSH & AM1 & LBA & TABC1 & TABC2 & _).
    pose proof SM0 as SM0'. unfold SM0_stmt, sm_stmt in SM0'.
    eapply evtF_cut.
    { unfold ASM0. eapply SM0';
        [exact AH1| exact NOL| exact MI1| rewrite USPA; exact STL1| exact LOC| rewrite USPA; unfold SM_STACK; lia| rewrite USPA; lia
        | exact TP| exact RSTK0| exact RI| exact RFS]. }
    cbv beta. unfold sm_post. rewrite USPA.
    intros ms2 (F0 & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & j0 & j1 & j2 & jk
                & -> & MI2 & STL2 & PRES & AH2 & F064 & F0B & F0TOP & FF2 & FSH2 & RF0 & RSF0).
    change (Z.to_nat (64 - 32)) with 32%nat in FF2. change (64 / 8) with 8 in RSF0. rewrite shadE in RSF0, FSH2.
    pose proof (ablk_lin _ _ F0B) as (F0B1 & F0B2 & F0B3 & F0B4). unfold AIMG_HI in F0B1.
    assert (F8 : F0 mod 8 = 0) by (clear - F064; Z.div_mod_to_equations; lia).
    destruct SHOME as (HFU & ZSE & FU256 & FUB). destruct SSH as (SHZ & RZ & WFU & RSFU).
    pose proof (ablk_lin _ _ FUB) as (FUB1 & FUB2 & FUB3 & FUB4). unfold AIMG_HI in FUB1.
    assert (Z8 : Zs mod 8 = 0) by (clear - ZSE FU256; Z.div_mod_to_equations; lia).
    assert (SHFU : shad Fu = Z.shiftr Zs 3 + 2147450880 - 4)
      by (rewrite shad_div; unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - ZSE FU256; Z.div_mod_to_equations; lia).
    destruct BLK as (ps & HPS & PAYH).
    assert (HPS2 : In (HB ps (c_p cx) 7176) (FB0 F0 :: LB)) by (right; exact HPS).
    pose proof (AI_block AI _ _ _ _ _ ps (c_p cx) 7176 AH2 HPS2) as (_ & (SB & _ & _ & S16) & RS & RSS0 & BSHS & _).
    pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). unfold AIMG_HI in SB1.
    assert (RSS : rng RNG (Z.shiftr (c_p cx) 3 + 2147450880) 897).
    { eapply rng_sub'; [exact RSS0|]. rewrite shadE. change (shlen (7176 + 7)) with 897. lia. }
    assert (SHS2 : shadow_bytes m2 (Z.shiftr (c_p cx) 3 + 2147450880) (Z.shiftr (c_p cx) 3 + 2147450880 + 897) (fun _ => 0)).
    { change 897 with (7176 / 8). apply ablock_sh0; [exact BSHS| reflexivity| lia| lia| lia]. }
    assert (WDC : c_w cx = 0 \/ (c_w cx mod 16 = 0 /\ ablk (c_w cx) (c_w cx + 32768) /\ (exists pw, In (HB pw (c_w cx) 32768) (FB0 F0 :: LB))
                                 /\ rng RNG (c_w cx) 32768 /\ rng RNG (Z.shiftr (c_w cx) 3 + 2147450880) 4096)).
    { destruct WBLK as [W0|(pw & HPW)]; [left; exact W0| right].
      pose proof (AI_block AI _ _ _ _ _ pw (c_w cx) 32768 AH2 ltac:(right; exact HPW)) as (_ & (WB & _ & _ & W16) & RW & RSW0 & _).
      split; [exact W16|]. split; [exact WB|]. split; [exists pw; right; exact HPW|]. split; [exact RW|].
      eapply rng_sub'; [exact RSW0|]. rewrite shadE. change (shlen (32768 + 7)) with 4096. lia. }
    assert (LBA2 : forall b, In b (FB0 F0 :: LB) -> ablk (ab_addr b) (ab_addr b + ab_size b)).
    { intros b [<-|Hb]; [cbn [ab_addr ab_size]; exact F0B| apply LBA; exact Hb]. }
    assert (CTX : inf_ctx cx (ILAY SP SPA Zs F0 lo) AI RNG (FB0 F0 :: LB)).
    { unfold inf_ctx. cbn [l_SP l_SPA l_Zs l_F0 l_lo].
      split; [exact S16|]. split; [exact SB|].
      split. { exists ps. split; [exact HPS2|]. destruct PAYH as [(pd & HPD & NP & PNE)|ND]; [left; exists pd; split; [right; exact HPD| split; assumption]| right; exact ND]. }
      split; [exists Fu; split; [right; exact HFU| split; [exact ZSE| split; [exact FU256| exact FUB]]]|].
      split; [exact RZ|].
      split. { eapply rng_sub'; [exact RSFU|]. rewrite SHFU. lia. }
      split; [left; reflexivity|]. split; [exact F064|]. split; [exact F0B|]. split; [exact RS|]. split; [exact RSS|].
      split; [exact OBE|]. split; [exact OSZ|]. split; [exact OCI|]. split; [exact ROB|]. split; [exact ROBS|]. split; [exact WDC|].
      split; [exact D1|]. split; [exact NR|]. split; [exact D16|]. split; [exact RD|]. split; [exact RSD|].
      split; [exact LOC|]. split; [lia|]. split; [lia|]. split; [exact (proj2 SPAB)|]. split; [exact SP16|]. split; [exact SPT|].
      split; [exact RSTK|]. split; [exact RI|]. split; [exact RISH|].
      split; [rewrite <- SHFU; exact RSFU|]. split; [exact TABC1|]. split; [exact TABC2| exact LBA2]. }
    destruct EM as (STRM & SSC & LENS & WORK & CODES & TAIL & OUT & PAYB & ARR & (obr & OBR) & WINB & BKE).
    cbv zeta in STRM, SSC, LENS, WORK, CODES, TAIL, OUT, PAYB, OBR.
    unfold A_OUTBUF in OBE.
    destruct OCI as (ivO & OCI1 & OCI2 & OCI3). destruct TABC1 as (ivT1 & T11 & T12 & T13). destruct TABC2 as (ivT2 & T21 & T22 & T23).
    assert (DTOP : c_q cx + c_n cx <= ATOP /\ 6341024 <= c_q cx).
    { destruct PAYH as [(pd & HPD & NP & PNE)|(N0 & DE)]; [| lia].
      pose proof (AI_block_bounds AI _ _ _ _ _ _ AH HPD) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3. unfold AIMG_HI in B1. lia. }
    assert (DJS : forall A N, 0 <= N -> A + N <= ATOP -> disjoint_from [(SP - 704, SP)] A N).
    { clear - H LOC LOS. intros A N HN HA. cbn [disjoint_from]. split; [lia| exact I]. }
    assert (DJSH : forall s1 s2, s1 <= s2 -> s2 <= 17594333528064 -> disjoint_from [(SP - 704, SP)] s1 (s2 - s1)).
    { clear - H LOC LOS. intros s1 s2 H1 H2. cbn [disjoint_from]. split; [lia| exact I]. }
    assert (CRZ : forall A N, Zs <= A -> A + N <= Zs + 112 -> aclient_range CI LB SPA A N).
    { intros A N H1 H2. replace N with (A + N - A) by lia. eapply acrS_fake; [exact HFU| lia| lia]. }
    assert (CRS : forall A N, c_p cx <= A -> A + N <= c_p cx + 7176 -> aclient_range CI LB SPA A N).
    { intros A N H1 H2. replace N with (A + N - A) by lia. eapply (acrS_block AI LB SPA (HB ps (c_p cx) 7176)); [exact HPS| cbn; lia| cbn; lia]. }
    assert (CRO : forall A N, c_ob cx <= A -> A + N <= c_ob cx + 262144 -> aclient_range CI LB SPA A N).
    { intros A N H1 H2. replace N with (A + N - A) by lia. eapply acr_ci; [exact OCI1| lia| lia]. }
    assert (CRK : forall A N, SPA <= A -> A + N <= SP -> aclient_range CI LB SPA A N).
    { intros A N H1 H2. replace N with (A + N - A) by lia. apply acrS_stack; lia. }
    assert (STRM2 : rw_cells bsegs m2 Zs (strm_cells (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) zti (Z_to_bv 64 (c_ob cx + t_cout st))
                                                   (Z_to_bv 64 (c_osz cx - t_cout st)) zto zmsg (Z_to_bv 64 (c_p cx)) (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE)
                                                   zopq zdt zadl zres zp1 zp2 zp3)).
    { eapply aheap_pres_rw_cells; [exact PRES| eapply rw_cells_transport; [exact STRM| exact MU1| exact WM1|]|];
        unfold strm_cells; cbn [cells_size csize Nat.add]; [apply DJS; lia| apply CRZ; lia]. }
    assert (SSC2 : rw_cells bsegs m2 (c_p cx) (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 (t_mode st)) (Z_to_bv 64 (t_last st)) (Z_to_bv 64 5) havedict
                                       (Z_to_bv 64 (t_flags st)) dmax check total (Z_to_bv 64 0) (Z_to_bv 64 15) (Z_to_bv 64 (wsz cx))
                                       (Z_to_bv 64 (t_whave st)) (Z_to_bv 64 (t_wnext st)) (Z_to_bv 64 (c_w cx))
                                       (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st))
                                       (Z_to_bv 64 (t_length st)) (Z_to_bv 64 (t_offset st)) (Z_to_bv 64 (t_extra st))
                                       (Z_to_bv 64 (cp_addrA (c_p cx) (t_lc st))) (Z_to_bv 64 (cp_addrA (c_p cx) (t_dc st)))
                                       (Z_to_bv 64 (t_lb st)) (Z_to_bv 64 (t_db st)) (Z_to_bv 64 (t_ncode st)) (Z_to_bv 64 (t_nlen st))
                                       (Z_to_bv 64 (t_ndist st)) (Z_to_bv 64 (t_shave st)) (Z_to_bv 64 (c_p cx + 1384 + 4 * t_nx st)))).
    { eapply aheap_pres_rw_cells; [exact PRES| eapply rw_cells_transport; [exact SSC| exact MU1| exact WM1|]|];
        unfold istate_cells; cbn [cells_size csize Nat.add]; [apply DJS; lia| apply CRS; lia]. }
    assert (LENS2 : f16arr bsegs m2 (c_p cx + 168) 320 lf).
    { eapply aheap_pres_f16arr; [exact PRES| unfold f16arr in *; eapply u16arr_transport; [exact LENS| exact MU1| exact WM1|]; rewrite fws_length; apply DJS; lia| apply CRS; lia]. }
    assert (WORK2 : f16arr bsegs m2 (c_p cx + 808) 288 wf).
    { eapply aheap_pres_f16arr; [exact PRES| unfold f16arr in *; eapply u16arr_transport; [exact WORK| exact MU1| exact WM1|]; rewrite fws_length; apply DJS; lia| apply CRS; lia]. }
    assert (CODES2 : f32arr bsegs m2 (c_p cx + 1384) 1444 cf).
    { eapply aheap_pres_f32arr; [exact PRES| unfold f32arr in *; eapply u32arr_transport; [exact CODES| exact MU1| exact WM1|]; rewrite fws_length; apply DJS; lia| apply CRS; lia]. }
    assert (TAIL2 : rw_cells bsegs m2 (c_p cx + 7160) (itail_cells (Z_to_bv 64 1) back was pad)).
    { eapply aheap_pres_rw_cells; [exact PRES| eapply rw_cells_transport; [exact TAIL| exact MU1| exact WM1|]|];
        unfold itail_cells; cbn [cells_size csize Nat.add]; [apply DJS; lia| apply CRS; lia]. }
    assert (OUT2 : f8arr bsegs m2 (c_ob cx) (Z.to_nat (c_osz cx)) fo).
    { eapply aheap_pres_f8arr; [exact PRES| unfold f8arr in *; eapply u8arr_transport; [exact OUT| exact MU1| exact WM1|]; rewrite length_map, length_seq; apply DJS; lia
                               | apply CRO; lia]. }
    assert (OBR2 : rw_cells bsegs m2 (c_ob cx + c_osz cx) [CB (Z.to_nat (262144 - c_osz cx)) obr]).
    { eapply aheap_pres_rw_cells; [exact PRES| eapply rw_cells_transport; [exact OBR| exact MU1| exact WM1|]|];
        cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; [apply DJS; lia| apply CRO; lia]. }
    assert (PAYB2 : bytes_at bsegs m2 (c_q cx) (map (Z_to_bv 8) payload)).
    { destruct PAYH as [(pd & HPD & NP & PNE)|(N0 & DE)].
      - eapply aheap_pres_bytes_at; [exact PRES| eapply bytes_at_transport; [exact PAYB| exact MU1|]|]; rewrite length_map, PLEN; [apply DJS; lia|].
        replace (c_n cx) with (c_q cx + c_n cx - c_q cx) by lia. eapply (acrS_block AI LB SPA (HB pd (c_q cx) (c_n cx))); [exact HPD| cbn; lia| cbn; lia].
      - destruct payload as [|c pl]; [| cbn [length] in PLEN; lia]. cbn [map]. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia. }
    assert (FRB2 : rw_cells bsegs m2 (SP + -104) (inf_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { eapply aheap_pres_rw_cells; [exact PRES| exact FRB1|]. unfold inf_SAVED. cbn [cells_size csize Nat.add]. apply CRK; lia. }
    assert (FRA2 : rw_cells bsegs m2 SPA (chop (repeat SH8 71) jA)).
    { eapply aheap_pres_rw_cells; [exact PRES| exact FRA1|].
      replace (Z.of_nat (cells_size (chop (repeat SH8 71) jA))) with 568 by (cbn [chop chop1 shape_size repeat cells_size csize Nat.add]; reflexivity). apply CRK; lia. }
    assert (STG2 : stk bsegs m2 (SPA + 568) (SP + -104)) by (eapply aheap_pres_stk; [exact PRES| exact STG1| lia| lia]).
    assert (SHZ2 : shadow_bytes m2 (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0)).
    { eapply (fake_sh_pres AI LB _ m1 m2 2 Fu 256 Zs 14); [exact PRES| exact HFU| exact Z8| lia| lia| lia| lia|].
      eapply shadow_bytes_munch; [exact SHZ| exact MU1|]. apply DJSH; [lia|].
      rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - FUB3 H ZSE FUB2. Z.div_mod_to_equations. lia. }
    assert (O8 : c_ob cx mod 8 = 0) by (rewrite OBE; reflexivity).
    assert (SHO2 : shadow_bytes m2 (Z.shiftr (c_ob cx) 3 + 2147450880) (Z.shiftr (c_ob cx) 3 + 2147450880 + 32768) (fun _ => 0)).
    { eapply (sh_pres_range AI LB SPA m1 m2); [exact PRES| |].
      - eapply acr_ci_sh; [exact OCI1| |]; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - OCI2 OCI3 OBE; Z.div_mod_to_equations; lia.
      - eapply shadow_bytes_munch; [exact SHO| exact MU1|]. apply DJSH; [lia|]. rewrite OBE. change (Z.shiftr 6341056 3) with 792632. lia. }
    assert (TSH2 : u2_tabsh m2).
    { assert (X : forall q1 q2 f, q1 <= q2 -> (2147468552 <= q1 /\ q2 <= 2147469916) \/ (2147469532 <= q1 /\ q2 <= 2147469576) ->
                  shadow_bytes m q1 q2 f -> shadow_bytes m2 q1 q2 f).
      { intros q1 q2 f L12 HR SB0. eapply (sh_pres_range AI LB SPA m1 m2); [exact PRES| |].
        - destruct HR as [HR|HR]; [eapply acr_ci_sh; [exact T11| lia| lia]| eapply acr_ci_sh; [exact T21| lia| lia]].
        - eapply shadow_bytes_munch; [exact SB0| exact MU1|]. apply DJSH; lia. }
      destruct TSH as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10). unfold u2_tabsh.
      split; [apply X; [lia| lia| exact A1]|]. split; [apply X; [lia| lia| exact A2]|]. split; [apply X; [lia| lia| exact A3]|].
      split; [apply X; [lia| lia| exact A4]|]. split; [apply X; [lia| lia| exact A5]|]. split; [apply X; [lia| lia| exact A6]|].
      split; [apply X; [lia| lia| exact A7]|]. split; [apply X; [lia| lia| exact A8]|]. split; [apply X; [lia| lia| exact A9]|].
      apply X; [lia| lia| exact A10]. }
    assert (UNP2 : unpoisoned m2 (c_q cx) (c_q cx + c_n cx)).
    { destruct PAYH as [(pd & HPD & NP & PNE)|(N0 & DE)].
      - pose proof (AI_block AI _ _ _ _ _ pd (c_q cx) (c_n cx) AH2 ltac:(right; exact HPD)) as (_ & (DB & _ & _ & _) & _ & _ & BSHD & _).
        apply ablock_unpoisoned; [exact BSHD| clear - D16; Z.div_mod_to_equations; lia| lia| lia| lia].
      - destruct UNP as (U1 & U2 & _). split; [exact U1|]. split; [exact U2|]. intros G HG. exfalso. lia. }
    assert (WFU2 : wr_at bsegs m2 (Z.shiftr Zs 3 + 2147450880 - 4) 32).
    { rewrite <- SHFU. change 32 with (256 / 8).
      eapply (fake_shwr_pres AI LB SPA m1 m2 2 Fu 256); [exact PRES| exact HFU| clear - FU256; Z.div_mod_to_equations; lia| lia| reflexivity| lia|].
      eapply wr_at_transport; [exact WFU| exact WM1]. }
    assert (WIN2 : exists fw, c_w cx <> 0 -> shadow_bytes m2 (Z.shiftr (c_w cx) 3 + 2147450880) (Z.shiftr (c_w cx) 3 + 2147450880 + 4096) (fun _ => 0)
                                             /\ f8arr bsegs m2 (c_w cx) (Z.to_nat 32768) fw).
    { destruct (Z.eq_dec (c_w cx) 0) as [W0|WN]; [exists (fun _ => 0); intros X; contradiction|].
      destruct (WINB WN) as (fw & FW). exists fw. intros _.
      destruct WBLK as [W0|(pw & HPW)]; [contradiction|].
      pose proof (AI_block AI _ _ _ _ _ pw (c_w cx) 32768 AH2 ltac:(right; exact HPW)) as (_ & (WB & _ & WB3 & W16) & _ & _ & BSHW & _).
      pose proof (ablk_lin _ _ WB) as (WB1 & WB2 & _ & WB4). unfold AIMG_HI in WB1.
      split.
      - change 4096 with (32768 / 8). apply ablock_sh0; [exact BSHW| reflexivity| lia| lia| lia].
      - eapply aheap_pres_f8arr; [exact PRES| unfold f8arr in *; eapply u8arr_transport; [exact FW| exact MU1| exact WM1|]; rewrite length_map, length_seq; apply DJS; lia|].
        replace (Z.of_nat (Z.to_nat 32768)) with (c_w cx + 32768 - c_w cx) by lia.
        eapply (acrS_block AI LB SPA (HB pw (c_w cx) 32768)); [exact HPW| cbn; lia| cbn; lia]. }
    destruct WIN2 as (fw & WIN2).
    replace (ret_pc (Z_to_bv 64 581136)) with (Z_to_bv 64 581136) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    replace sp with (Z_to_bv 64 SP) by (subst SP; apply Z_to_bv_bv_unsigned).
    eapply (inf_hdr1 AI L RNG stA (FB0 F0 :: LB) gp tp FR fc POST cx (ILAY SP SPA Zs F0 lo) st lf cf wf fo payload
                     zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad);
      [| exact CTX| exact AH2| exact AINV| | exact FRA2| exact FF2| exact FSH2| exact RF0| exact RSF0| exact SHZ2| exact SHS2| exact STL2| exact MI2].
    2:{ unfold inf_emem. cbv zeta.
        split; [exact STRM2|]. split; [exact SSC2|]. split; [exact LENS2|]. split; [exact WORK2|]. split; [exact CODES2|]. split; [exact TAIL2|].
        split; [exact OUT2|]. split; [exact PAYB2|]. split; [exact ARR|]. split; [exists obr; exact OBR2|].
        split; [intros WN; exists fw; exact (proj2 (WIN2 WN))| exact BKE]. }
    cbn [l_SP l_SPA l_Zs l_F0 l_lo].
    intros v0 v8 v16 v24 v240 v328 v512 j544 j552 y6 y7 y10 y11 y12 y13 y14 y16 y19 y21 y22 y23 y26 y28 y29 y30 y31 m3 FRM3 SSC3 FK3 FKSH3 MU3 WM3 MI3 STK3.
    assert (HF0 : In (FB0 F0) (FB0 F0 :: LB)) by (left; reflexivity).
    assert (DIS : forall b, In b LB -> ab_addr b + ab_size b <= F0 \/ F0 + 64 <= ab_addr b).
    { intros b Hb. pose proof (AI_blocks_nodup AI _ _ _ _ _ AH2) as ND. inversion ND as [|x l NI0 N3]. subst.
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ b (FB0 F0) AH2 ltac:(right; exact Hb) HF0 ltac:(intros E; apply NI0; rewrite <- E; exact Hb)) as X.
      cbn [ab_addr ab_size] in X. lia. }
    pose proof (DIS _ HFU) as DFU. pose proof (DIS _ HPS) as DFS. cbn [ab_addr ab_size] in DFU, DFS.
    assert (DFD : c_q cx + c_n cx <= F0 \/ F0 + 64 <= c_q cx).
    { destruct PAYH as [(pd & HPD & _)|(N0 & DE)]; [pose proof (DIS _ HPD) as X; cbn [ab_addr ab_size] in X; exact X| lia]. }
    assert (DFW : c_w cx = 0 \/ (c_w cx + 32768 <= F0 \/ F0 + 64 <= c_w cx)).
    { destruct WBLK as [W0|(pw & HPW)]; [left; exact W0| right; pose proof (DIS _ HPW) as X; cbn [ab_addr ab_size] in X; exact X]. }
    pose proof (ablk_disj_band _ _ F0B) as BF0. pose proof (ablk_disj_band _ _ FUB) as BFU. pose proof (ablk_disj_band _ _ SB) as BS.
    assert (BD : c_q cx + c_n cx <= KLS \/ 0x10007fff8000 <= c_q cx).
    { destruct PAYH as [(pd & HPD & _)|(N0 & DE)]; [pose proof (ablk_disj_band _ _ (LBA _ HPD)) as X; cbn [ab_addr ab_size] in X; exact X| unfold KLS; lia]. }
    assert (BW : c_w cx = 0 \/ (c_w cx + 32768 <= KLS \/ 0x10007fff8000 <= c_w cx)).
    { destruct WDC as [W0|(_ & WB & _)]; [left; exact W0| right; exact (ablk_disj_band _ _ WB)]. }
    unfold KLS in BF0, BFU, BS, BD, BW.
    destruct (shr3_lin8 F0 ltac:(lia) F8) as (qF & EQF & QF).
    assert (DSS : forall b, In b LB -> b <> HB ps (c_p cx) 7176 -> ab_addr b + ab_size b <= c_p cx \/ c_p cx + 7176 <= ab_addr b).
    { intros b Hb NE. pose proof (AI_blocks_disjoint AI _ _ _ _ _ b (HB ps (c_p cx) 7176) AH Hb HPS NE) as X. cbn [ab_addr ab_size] in X. lia. }
    pose proof (DSS _ HFU ltac:(discriminate)) as DSU. cbn [ab_addr ab_size] in DSU.
    assert (DSD : c_q cx + c_n cx <= c_p cx \/ c_p cx + 7176 <= c_q cx).
    { destruct PAYH as [(pd & HPD & NP & PNE)|(N0 & DE)]; [| lia].
      pose proof (DSS _ HPD ltac:(intros E; inversion E; contradiction)) as X. cbn [ab_addr ab_size] in X. exact X. }
    assert (HQ : 8 * qF = F0 /\ 6811648 <= F0 /\ F0 + 64 <= ATOP) by lia.
    assert (DJ_Z : forall A N, 0 <= N -> Zs <= A -> A + N <= Zs + 112 -> disjoint_from (hdr_W (c_p cx) SPA F0 lo) A N).
    { unfold hdr_W. rewrite EQF. clear - HQ DFU BFU ZSE FUB1 FUB3 DSU H LOC.
      intros A N HN H1 H2. cbn [disjoint_from]. repeat split; try exact I; lia. }
    assert (DJ_S1 : forall A N, 0 <= N -> c_p cx <= A -> A + N <= c_p cx + 8 -> disjoint_from (hdr_W (c_p cx) SPA F0 lo) A N).
    { unfold hdr_W. rewrite EQF. clear - HQ DFS BS SB1 SB3 H LOC.
      intros A N HN H1 H2. cbn [disjoint_from]. repeat split; try exact I; lia. }
    assert (DJ_S2 : forall A N, 0 <= N -> c_p cx + 12 <= A -> A + N <= c_p cx + 7176 -> disjoint_from (hdr_W (c_p cx) SPA F0 lo) A N).
    { unfold hdr_W. rewrite EQF. clear - HQ DFS BS SB1 SB3 H LOC.
      intros A N HN H1 H2. cbn [disjoint_from]. repeat split; try exact I; lia. }
    assert (DJ_O : forall A N, 0 <= N -> c_ob cx <= A -> A + N <= c_ob cx + 262144 -> disjoint_from (hdr_W (c_p cx) SPA F0 lo) A N).
    { unfold hdr_W. rewrite EQF. clear - HQ OBE SB1 H LOC.
      intros A N HN H1 H2. cbn [disjoint_from]. repeat split; try exact I; lia. }
    assert (DJ_D : forall A N, 0 <= N -> c_q cx <= A -> A + N <= c_q cx + c_n cx -> disjoint_from (hdr_W (c_p cx) SPA F0 lo) A N).
    { unfold hdr_W. rewrite EQF. clear - HQ DFD BD DTOP DSD H LOC D1 NR.
      intros A N HN H1 H2. cbn [disjoint_from]. repeat split; try exact I; lia. }
    assert (DJ_K : forall A N, 0 <= N -> SPA + 568 <= A -> A + N <= SP -> disjoint_from (hdr_W (c_p cx) SPA F0 lo) A N).
    { unfold hdr_W. rewrite EQF. clear - HQ SB3 SPAB LOS H LOC.
      intros A N HN H1 H2. cbn [disjoint_from]. repeat split; try exact I; lia. }
    assert (DJHq : forall q1 q2 Xlo Xhi, q1 <= q2 -> Xlo <= 8 * (q1 - 2147450880) + 7 -> 8 * (q2 - 1 - 2147450880) <= Xhi - 1 ->
              0 <= Xlo -> Xhi <= ATOP -> (Xhi <= F0 \/ F0 + 64 <= Xlo) -> (q1 < q2 -> Xlo < Xhi) ->
              disjoint_from (hdr_W (c_p cx) SPA F0 lo) q1 (q2 - q1)).
    { unfold hdr_W. rewrite EQF.
      clear - HQ BF0 BS SB1 SB3 H LOC LOS SPAB.
      intros q1 q2 Xlo Xhi L12 HL HH X0 XT DX NE. cbn [disjoint_from]. repeat split; try exact I; lia. }
    assert (AH3 : AHEAP AI L RNG stA (FB0 F0 :: LB) m3).
    { eapply (AI_frame AI _ _ _ _ m2 m3 _ AH2 MU3 WM3). unfold hdr_W.
      constructor; [cbn [fst snd]; eapply acr_fake; [exact HF0| lia| lia]|].
      constructor; [cbn [fst snd]; eapply (acr_fake_sh AI _ 0 F0 64 F0 8); [exact HF0| exact F8| lia| lia| lia]|].
      constructor; [cbn [fst snd]; apply acr_stack; lia|].
      constructor; [cbn [fst snd]; eapply (acr_block AI _ (HB ps (c_p cx) 7176)); [exact HPS2| cbn; lia| cbn; lia]| constructor]. }
    destruct (AI_fake_flag L RNG stA _ m2 0 F0 64 AH2 HF0) as (_ & _ & GB & _ & GBL & GCI).
    eapply (K F0 SPA fw jk v0 v8 v16 v24 v240 v328 v512 j544 j552); [exact CTX| exact RF0| exact RSF0| reflexivity| |].
    -
      unfold inf_vis. cbn [l_SP l_SPA l_Zs l_F0 l_lo]. unfold st_load.
      cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext].
      rewrite CIN0.
      split; [exact FRM3|].
      split; [eapply rw_cells_transport; [exact STRM2| exact MU3| exact WM3|]; unfold strm_cells; cbn [cells_size csize Nat.add]; apply DJ_Z; lia|].
      split; [exact SSC3|].
      split; [unfold f16arr in *; eapply u16arr_transport; [exact LENS2| exact MU3| exact WM3|]; rewrite fws_length; apply DJ_S2; lia|].
      split; [unfold f16arr in *; eapply u16arr_transport; [exact WORK2| exact MU3| exact WM3|]; rewrite fws_length; apply DJ_S2; lia|].
      split; [unfold f32arr in *; eapply u32arr_transport; [exact CODES2| exact MU3| exact WM3|]; rewrite fws_length; apply DJ_S2; lia|].
      split; [eapply rw_cells_transport; [exact TAIL2| exact MU3| exact WM3|]; unfold itail_cells; cbn [cells_size csize Nat.add]; apply DJ_S2; lia|].
      split; [unfold f8arr in *; eapply u8arr_transport; [exact OUT2| exact MU3| exact WM3|]; rewrite length_map, length_seq; apply DJ_O; lia|].
      split; [eapply bytes_at_transport; [exact PAYB2| exact MU3|]; rewrite length_map, PLEN; apply DJ_D; lia|].
      split; [exact STK3|]. split; [exact MI3|].
      split; [unfold mode_load; destruct (Z.eqb_spec (t_mode st) TYPE) as [E|E]; [cbv; discriminate| exact MNE]|].
      unfold back_ok in BKE |- *. cbn [t_mode]. unfold mode_load. destruct (Z.eqb_spec (t_mode st) TYPE) as [E|E]; [| exact BKE].
      split; intros X; exfalso; cbv in X; discriminate X.
    -
      assert (S8 : c_p cx mod 8 = 0) by (clear - S16; Z.div_mod_to_equations; lia).
      destruct (shr3_lin8 Zs ltac:(lia) Z8) as (qZ & EQZ & QZ). destruct (shr3_lin8 (c_p cx) ltac:(lia) S8) as (qS & EQS & QS).
      destruct (shr3_lin8 (c_ob cx) ltac:(lia) O8) as (qO & EQO & QO).
      assert (DXZ : Zs + 112 <= F0 \/ F0 + 64 <= Zs) by (clear - DFU ZSE; lia).
      assert (DXS : c_p cx + 7176 <= F0 \/ F0 + 64 <= c_p cx) by (clear - DFS; lia).
      assert (DXO : c_ob cx + 262144 <= F0 \/ F0 + 64 <= c_ob cx) by (clear - OBE HQ; lia).
      assert (WIN3 : c_w cx <> 0 -> shadow_bytes m3 (Z.shiftr (c_w cx) 3 + 2147450880) (Z.shiftr (c_w cx) 3 + 2147450880 + 4096) (fun _ => 0)
                                     /\ f8arr bsegs m3 (c_w cx) (Z.to_nat 32768) fw).
      { intros WN. destruct (WIN2 WN) as (SHW & FW).
        destruct WDC as [W0|(W16 & WB & (pw & HPW) & _)]; [contradiction|]. destruct DFW as [W0|DFW]; [contradiction|]. destruct BW as [W0|BW]; [contradiction|].
        pose proof (ablk_lin _ _ WB) as (WB1 & WB2 & WB3 & WB4). unfold AIMG_HI in WB1.
        assert (W8 : c_w cx mod 8 = 0) by (clear - W16; Z.div_mod_to_equations; lia).
        destruct (shr3_lin8 (c_w cx) ltac:(lia) W8) as (qW & EQW & QW).
        assert (DSW : c_w cx + 32768 <= c_p cx \/ c_p cx + 7176 <= c_w cx).
        { destruct HPW as [X|HPW]; [discriminate X|]. destruct (N.eq_dec pw ps) as [E|NE].
          - subst pw. pose proof (hb_same_id LB ps (c_w cx) 32768 (c_p cx) 7176 (AI_hb_ids AI _ _ _ _ _ AH) HPW HPS) as Q. inversion Q.
          - pose proof (DSS _ HPW ltac:(intros Q; inversion Q; contradiction)) as X. cbn [ab_addr ab_size] in X. exact X. }
        split.
        - eapply shadow_bytes_munch; [exact SHW| exact MU3|]. rewrite EQW.
          apply (DJHq _ _ (c_w cx) (c_w cx + 32768)); [clear; lia| clear - QW; lia| clear - QW; lia| clear - WB2; lia| exact WB3| exact DFW| clear; lia].
        - unfold f8arr in *. eapply u8arr_transport; [exact FW| exact MU3| exact WM3|]. rewrite length_map, length_seq.
          unfold hdr_W. rewrite EQF. clear - HQ DFW BW WB1 WB3 DSW H LOC.
          cbn [disjoint_from]. repeat split; try exact I; lia. }
      assert (UNP3 : unpoisoned m3 (c_q cx) (c_q cx + c_n cx)).
      { eapply unpoisoned_munch; [exact UNP2| exact MU3|].
        apply (DJHq _ _ (c_q cx) (c_q cx + c_n cx)); [| | | clear - D1; lia| exact (proj1 DTOP)| exact DFD|];
          rewrite !shad_div; unfold ASHOFF; clear - D1 NR D16; Z.div_mod_to_equations; lia. }
      clear DFU DFS DFD DFW BF0 BFU BS BD BW DSU DSD DSS DIS WDC WIN2.
      (* [U14B] A2 2026-11-12: the upper bound covers every 1.4 table shadow of inf_hid (InfBBase: the last ends at 2147469924) *)
      assert (TABQ : forall q1 q2 f, q1 < q2 -> 2147468552 <= q1 -> q2 <= 2147469916 -> shadow_bytes m2 q1 q2 f -> shadow_bytes m3 q1 q2 f).
      { intros q1 q2 f L12 B1 B2 SB0. eapply shadow_bytes_munch; [exact SB0| exact MU3|].
        apply (DJHq q1 q2 (8 * (q1 - 2147450880)) (8 * (q2 - 2147450880))); [clear - L12; lia| clear; lia| clear; lia| clear - B1; lia| clear - B2 H; lia
                                                                         | left; clear - B2 HQ; lia| clear; lia]. }
      destruct TSH2 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
      unfold inf_hid. cbn [l_SP l_SPA l_Zs l_F0 l_lo].
      split; [exact AH3|].
      split. { eapply shadow_bytes_munch; [exact SHZ2| exact MU3|]. rewrite EQZ.
               apply (DJHq _ _ Zs (Zs + 112)); [clear; lia| clear - QZ; lia| clear - QZ; lia| clear - FUB2 ZSE; lia| clear - FUB3 ZSE; lia| exact DXZ| clear; lia]. }
      split. { eapply shadow_bytes_munch; [exact SHS2| exact MU3|]. rewrite EQS.
               apply (DJHq _ _ (c_p cx) (c_p cx + 7176)); [clear; lia| clear - QS; lia| clear - QS; lia| clear - SB2; lia| exact SB3| exact DXS| clear; lia]. }
      split. { eapply shadow_bytes_munch; [exact SHO2| exact MU3|]. rewrite EQO.
               apply (DJHq _ _ (c_ob cx) (c_ob cx + 262144)); [clear; lia| clear - QO; lia| clear - QO; lia| clear - OBE; lia| clear - OBE H; lia| exact DXO| clear; lia]. }
      split; [exact WIN3|]. split; [exact UNP3|].
      split; [eapply rw_cells_transport; [exact FRB2| exact MU3| exact WM3|]; unfold inf_SAVED; cbn [cells_size csize Nat.add]; apply DJ_K; clear - SPAB; lia|].
      split; [reflexivity|]. split; [exact FK3|]. split; [reflexivity|]. split; [exact FKSH3|]. split; [reflexivity|].
      split; [intros b Hb; right; exact Hb|].
      split.
      {
        eapply client_agree_trans; [| eapply client_agree_trans].
        - eapply (client_agree_munch AI LB _ _ _ m m1 MU1 WM1). intros a Ha HC _.
          destruct (aclient_addr_cases AI L RNG stA LB m SP a AH HC) as [X|[X|[(b & Hb & X)|X]]]; cbn [outside]; unfold AIMG_HI, KLS in *.
          + split; [clear - X; lia| exact I].
          + split; [clear - X H LOC LOS; lia| exact I].
          + pose proof (AI_block_bounds AI _ _ _ _ _ b AH Hb) as (B1 & B2 & B3). split; [clear - X B3 H LOC LOS; lia| exact I].
          + split; [clear - X H LOC LOS; lia| exact I].
        - eapply (client_agree_pres AI LB LB SP SPA); [exact PRES| clear - SPAB; lia| auto].
        - eapply (client_agree_munch AI LB _ _ _ m2 m3 MU3 WM3). intros a Ha HC HN.
          destruct (inf_client_outside AI L RNG stA LB m2 F0 (fflag L 0 F0) lo SP a AH2 LBA F0B F8 GB GBL GCI LOC ltac:(clear - LOS; lia) HC) as (O1 & O2 & O3 & O4).
          assert (NS : ~ (c_p cx <= a < c_p cx + 7176)).
          { intros X. apply HN. exists (c_p cx, c_p cx + 7176). split; [right; left; reflexivity| exact X]. }
          unfold hdr_W. cbn [outside]. clear - O1 O2 O3 NS SPAB. repeat split; try exact I; lia. }
      split; [apply TABQ; [lia| lia| lia| exact A1]|]. split; [apply TABQ; [lia| lia| lia| exact A2]|].
      split; [apply TABQ; [lia| lia| lia| exact A3]|]. split; [apply TABQ; [lia| lia| lia| exact A4]|].
      split; [apply TABQ; [lia| lia| lia| exact A5]|]. split; [apply TABQ; [lia| lia| lia| exact A6]|].
      split; [apply TABQ; [lia| lia| lia| exact A7]|]. split; [apply TABQ; [lia| lia| lia| exact A8]|].
      split; [apply TABQ; [lia| lia| lia| exact A9]|]. split; [apply TABQ; [lia| lia| lia| exact A10]|].
      split; [eapply stk_transport_disjoint; [exact STG2| exact MU3| exact WM3|]; apply DJ_K; clear - SPAB; lia|].
      split; [exists obr; eapply rw_cells_transport; [exact OBR2| exact MU3| exact WM3|]; cbn [cells_size csize Nat.add];
              rewrite Nat.add_0_r, Z2Nat.id by (clear - OSZ; lia); apply DJ_O; clear - OSZ; lia|].
      eapply wr_at_transport; [exact WFU2| exact WM3].
  Qed.
End T.
End CANSEC1.
