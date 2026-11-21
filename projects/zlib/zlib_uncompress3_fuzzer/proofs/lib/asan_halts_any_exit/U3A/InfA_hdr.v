(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2ABlob U2AStore InfAGlue InfPure InfPure_entry.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfAIface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).

  Lemma inf_hdr2 : forall (SP SPA Zs F0 lo S D n osz cin cout hold bits mode : Z)
      (zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 : word)
      (last wrap havedict flags dmax check total head wbits wsize whave wnext window
       length offset extra lencode distcode lenbits distbits ncode nlen ndist have next : word)
      (x11 x19 x20 x26 x27 x28 x29 x31 j480 j488 j496 j504 j512 j520 : word) (jB : list byte) (m : amem)
      (* the continuation is stated at InfABase's 1.4 DISP_MS registers *)
      (K : forall (v0 v8 v16 v240 v504 j512 j520 : word) (y5 y6 y11 y12 y13 y14 y15 y16 y17 y22 y23 y26 : word) (m' : amem),
         rw_cells asegs m' SPA (inf_locals S Zs F0 v0 v8 v16 v240 (Z_to_bv 64 0) (Z_to_bv 64 (n - cin)) (Z_to_bv 64 (osz - cout))
                                             (Z_to_bv 64 (6336512 + cout)) (Z_to_bv 64 (D + cin)) v504 j512 j520) ->
         munch [(lo, SPA + 536)] m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' lo SPA ->
         evtF asegs RNG POST
           (MS (mkR (Z_to_bv 64 (S + 8)) (Z_to_bv 64 SPA) gp tp y5 y6 (Z_to_bv 64 (S + 56)) (Z_to_bv 64 SP) (Z_to_bv 64 SPA) (Z_to_bv 64 F0) y11 y12 y13 y14 y15 y16 y17
                    (Z_to_bv 64 Zs) (Z_to_bv 64 bits) (Z_to_bv 64 hold) (Z_to_bv 64 2147450880) y22 y23 (Z_to_bv 64 (Z.shiftr F0 3 + 2147450880)) (Z_to_bv 64 F0)
                    y26 (Z_to_bv 64 (n - cin)) (Z_to_bv 64 (S + 28)) (Z_to_bv 64 (osz - cout))
                    (Z_to_bv 64 (Z.shiftr (S + 8) 3 + 2147450880)) (Z_to_bv 64 (S + 108)))
               FR (Z_to_bv 64 0x8e2dc) fc None m' (seg_rom asegs))),
    lo + 8192 <= SPA -> SP - 656 <= SPA <= SP - 640 -> SP + 16 < 140737488355328 -> 17594333528064 <= lo ->
    Zs mod 8 = 0 -> S mod 8 = 0 -> 0 <= Zs -> Zs + 112 <= lo -> 0 <= S -> S + 7176 <= lo ->
    0 <= cin <= n -> n < 67108864 -> 0 <= cout <= osz -> osz <= 262144 -> 0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> 0 <= D -> D + n <= lo ->
    rng RNG SPA 536 -> rng RNG Zs 112 -> rng RNG (Z.shiftr Zs 3 + 2147450880) 14 -> rng RNG S 7176 -> rng RNG (Z.shiftr S 3 + 2147450880) 897 ->
    (* at 1.4 the walk before 0x8e0b0 has stored only frame slots 472 (16209) and 528 (F0); next_in
       goes to slot 496 inside this walk (0x8e110 sd t2,496(s1)) *)
    rw_cells asegs m SPA [CB 472 jB] ->
    rw_cells asegs m (SPA + 472) [C8 (Z_to_bv 64 16209); C8 j480; C8 j488; C8 j496; C8 j504; C8 j512; C8 j520; C8 (Z_to_bv 64 F0)] ->
    rw_cells asegs m Zs (strm_cells (Z_to_bv 64 (D + cin)) (Z_to_bv 64 (n - cin)) zti (Z_to_bv 64 (6336512 + cout)) (Z_to_bv 64 (osz - cout)) zto zmsg
                                    (Z_to_bv 64 S) (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) zopq zdt zadl zres zp1 zp2 zp3) ->
    rw_cells asegs m S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 mode) last wrap havedict flags dmax check total head wbits wsize whave wnext window
                                     (Z_to_bv 64 hold) (Z_to_bv 64 bits) length offset extra lencode distcode lenbits distbits ncode nlen ndist have next) ->
    shadow_bytes m (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0) ->
    shadow_bytes m (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0) ->
    stk asegs m lo SPA -> mem_inv asegs m ->
    evtF asegs RNG POST
      (* the 1.4 state at 0x8e0b0, read off probe PgHdrB1 (reg_val x1..x31 where inf_hdr1's walk
         reaches 0x8e0b0, both branches): ra = S+8, t2 = next_in, a1 free (the mode), a2 = 16209, a3 = TYPE, a4 = S, s5 = SHB,
         s6 = 0, s7 = -2, s8 / s9 = the fake frame, t5 = the mode shadow *)
      (MS (mkR (Z_to_bv 64 (S + 8)) (Z_to_bv 64 SPA) gp tp (Z_to_bv 64 (6336512 + cout)) (Z_to_bv 64 (Z.shiftr Zs 3 + 2147450880)) (Z_to_bv 64 (D + cin)) (Z_to_bv 64 SP) (Z_to_bv 64 SPA)
               (Z_to_bv 64 F0) x11 (Z_to_bv 64 16209) (Z_to_bv 64 16191) (Z_to_bv 64 S) (Z_to_bv 64 (Zs + 24)) (Z_to_bv 64 (Z.shiftr (Zs + 24) 3 + 2147450880)) (Z_to_bv 64 (Zs + 8))
               (Z_to_bv 64 Zs) x19 x20 (Z_to_bv 64 2147450880) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) (Z_to_bv 64 (Z.shiftr F0 3 + 2147450880)) (Z_to_bv 64 F0)
               x26 x27 x28 x29 (Z_to_bv 64 (Z.shiftr (S + 8) 3 + 2147450880)) x31)
          FR (Z_to_bv 64 0x8e0e0) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros K LOS SPAR SPT LO0 Z8 S8 Z0 ZL S0 SL CIN NR COUT OSZ BITS HOLD D0 DL RFRM RZ RSZ RS RSS FRA1 FRA2 STRM SSC SHZ SHS STK MI.
    unfold strm_cells, istate_cells, A_ZCALLOC, A_ZCFREE in *.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40.
    apply (rw_cells_chop asegs _ SPA 472 jB (repeat SH8 59)) in FRA1; [| reflexivity].
    cbn [chop chop1 shape_size repeat] in FRA1. chop_names FRA1.
    rw_join FRA1 FRA2 FRM.
    pose (W := [(lo, SPA + 536)]).
    assert (DJZ : disjoint_from W (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14 - (Z.shiftr Zs 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite ?Z.shiftr_div_pow2 by lia. change (2^3) with 8. repeat split; try exact I; Z.div_mod_to_equations; lia. }
    assert (DJS : disjoint_from W (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite ?Z.shiftr_div_pow2 by lia. change (2^3) with 8. repeat split; try exact I; Z.div_mod_to_equations; lia. }
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM. subst W.
    zrunb [0x8e2dc].
    eapply K; [| exact MU| exact WM| eassumption| eassumption].
    unfold inf_locals. exact FRM.
    (* v240 is a vestige binder at 1.4 *)
    Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.


  Definition F0_cells (jk : list byte) (flagp : word) : list cell :=
    [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 95894); C8 (Z_to_bv 64 581232); CB 32 jk; C8 flagp].
  Definition F0_shadow : list cell :=
    [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
     C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 4);
     C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)].
  Definition hdr_W (S SPA F0 lo : Z) : list (Z * Z) :=
    [(F0, F0 + 64); (Z.shiftr F0 3 + 2147450880, Z.shiftr F0 3 + 2147450880 + 8); (lo, SPA + 536); (S + 8, S + 12)].

  Lemma inf_hdr1 : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (payload : list Z)
      (zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (jA : list byte) (j0 j1 j2 flagp : word) (jk : list byte) (m : amem)
      (K : forall (v0 v8 v16 v240 v504 j512 j520 : word) (y1 y5 y6 y11 y12 y13 y14 y15 y16 y17 y21 y27 : word) (m' : amem),
         rw_cells asegs m' (l_SPA ly) (inf_locals (c_p cx) (l_Zs ly) (l_F0 ly) v0 v8 v16 v240 (Z_to_bv 64 0) (Z_to_bv 64 (c_n cx - t_cin st))
                                                  (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (c_q cx + t_cin st)) v504 j512 j520) ->
         rw_cells asegs m' (c_p cx) (istate_cells (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (mode_load (t_mode st))) (Z_to_bv 64 (t_last st)) (Z_to_bv 64 5) havedict
                                       (Z_to_bv 64 (t_flags st)) dmax check total (Z_to_bv 64 0) (Z_to_bv 64 15) (Z_to_bv 64 (wsz cx))
                                       (Z_to_bv 64 (t_whave st)) (Z_to_bv 64 (t_wnext st)) (Z_to_bv 64 (c_w cx))
                                       (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st))
                                       (Z_to_bv 64 (t_length st)) (Z_to_bv 64 (t_offset st)) (Z_to_bv 64 (t_extra st))
                                       (Z_to_bv 64 (cp_addrA (c_p cx) (t_lc st))) (Z_to_bv 64 (cp_addrA (c_p cx) (t_dc st)))
                                       (Z_to_bv 64 (t_lb st)) (Z_to_bv 64 (t_db st)) (Z_to_bv 64 (t_ncode st)) (Z_to_bv 64 (t_nlen st))
                                       (Z_to_bv 64 (t_ndist st)) (Z_to_bv 64 (t_shave st)) (Z_to_bv 64 (c_p cx + 1384 + 4 * t_nx st))) ->
         rw_cells asegs m' (l_F0 ly) (F0_cells jk flagp) -> rw_cells asegs m' (Z.shiftr (l_F0 ly) 3 + 2147450880) F0_shadow ->
         munch (hdr_W (c_p cx) (l_SPA ly) (l_F0 ly) (l_lo ly)) m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' (l_lo ly) (l_SPA ly) ->
         evtF asegs RNG POST (DISP_MS cx ly gp tp FR fc (st_load cx st) y1 y5 y6 y11 y12 y13 y14 y15 y16 y17 y21 y27 m')),
    inf_ctx cx ly AI RNG LB -> AHEAP AI L RNG stA LB m ->
    ainv cx st lf cf ->
    inf_emem cx (l_Zs ly) st lf cf wf fo payload zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m ->
    rw_cells asegs m (l_SPA ly) (chop (repeat SH8 67) jA) ->
    rw_cells asegs m (l_F0 ly) [C8 j0; C8 j1; C8 j2; CB 32 jk; C8 flagp] ->
    rw_cells asegs m (Z.shiftr (l_F0 ly) 3 + 2147450880) [C8 (Z_to_bv 64 0)] ->
    rng RNG (l_F0 ly) 64 -> rng RNG (Z.shiftr (l_F0 ly) 3 + 2147450880) 8 ->
    shadow_bytes m (Z.shiftr (l_Zs ly) 3 + 2147450880) (Z.shiftr (l_Zs ly) 3 + 2147450880 + 14) (fun _ => 0) ->
    shadow_bytes m (Z.shiftr (c_p cx) 3 + 2147450880) (Z.shiftr (c_p cx) 3 + 2147450880 + 897) (fun _ => 0) ->
    stk asegs m (l_lo ly) (l_SPA ly) -> mem_inv asegs m ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 (l_F0 ly)) x11 x12 x13 x14 x15 x16 x17
               (* the 1.4 prologue leaves SHB in s5 and 0 in s6 (InfA_pro; 1.3.1: 0 in s5, SHB in s9) *)
               (Z_to_bv 64 (l_Zs ly)) x19 x20 (Z_to_bv 64 2147450880) (Z_to_bv 64 0) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8dee4) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros K CTX AH AINV EM FRA FK FKSH RF RFS SHZ SHS STK MI.
    pose proof (inf_facts AI L RNG stA LB cx ly m AH CTX) as LIN0.
    destruct LIN0 as (Fu & ZSE & FU256 & HFU & (S1 & S2 & bS & BS0 & BS1 & BS2) & (U1 & U2 & bU & BU0 & BU1 & BU2) & (F1 & F2 & bF & BF0 & BF1 & BF2)
                     & DL1 & DL2 & (bD & BD0 & BD1 & BD2) & (cSU & CSU0 & CSU1 & CSU2) & (cSF & CSF0 & CSF1 & CSF2) & (cUF & CUF0 & CUF1 & CUF2)
                     & (cSD & CSD0 & CSD1 & CSD2) & (cUD & CUD0 & CUD1 & CUD2) & (cFD & CFD0 & CFD1 & CFD2)).
    destruct CTX as (S16 & SB & _ & _ & RZ & RSZ & HF0 & F064 & F0B & RS & RSS & OBE & OSZ & OCI & ROB & ROBS & WDC
                     & D1 & NR & D16 & RD & RSD & LOC & LOS & SPAR & SPA32 & SP16 & SPT & RSTK & RI & RISH & RSFU & TABC1 & TABC2 & LBABLK).
    hide_or WDC.
    pose proof EM as (STRM & SSC & _).
    pose proof AINV as (RN & _ & MO). pose proof (proj1 MO) as REACH.
    destruct cx as [u S D n OB osz Wd cin0 cout0 W0 K0 zc]. destruct ly as [SP SPA Zs F0 lo].
    destruct st as [mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
    icx_cbn. cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
    unfold IDefs.RNG in RN. icx_cbn. destruct RN as (RN1 & RN2 & RN3 & RN4 & RN5 & RN6 & RN7 & RN8 & RN9 & _).
    unfold strm_cells, istate_cells, itail_cells, A_ZCALLOC, A_ZCFREE in STRM, SSC. icx_cbn. cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
    unfold hdr_W, F0_cells, F0_shadow in K.
    atop_facts. unfold KEND in SPT. subst OB. unfold A_OUTBUF in *.
    assert (Z8 : Zs mod 8 = 0) by (subst Zs; Z.div_mod_to_equations; lia).
    assert (S8 : S mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (RFRM : rng RNG SPA 536) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (MODER : 16180 <= mode <= 16211) by (unfold reach in REACH; cbv [HEAD DICTID MEM] in REACH; lia).
    pose proof (pow2_le_40 bits ltac:(lia)) as P40.
    cbn [chop chop1 shape_size repeat] in FRA. chop_names FRA.
    pose (W := [(F0, F0 + 64); (Z.shiftr F0 3 + 2147450880, Z.shiftr F0 3 + 2147450880 + 8); (lo, SPA + 536); (S + 8, S + 12)]).
    assert (BSF : 2147450880 <= Z.shiftr F0 3 + 2147450880 /\ Z.shiftr F0 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (DJZ6 : disjoint_from W (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14 - (Z.shiftr Zs 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite ?Z.shiftr_div_pow2 by lia. change (2^3) with 8. repeat split; try exact I; Z.div_mod_to_equations; lia. }
    assert (DJS6 : disjoint_from W (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite ?Z.shiftr_div_pow2 by lia. change (2^3) with 8. repeat split; try exact I; Z.div_mod_to_equations; lia. }
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM. subst W.
    apply shadow8_c1s in FKSH. unfold c1z in FKSH.
    zrunb [0x8df8c].
    zrunb [0x8e2dc].
    unfold istate_cells in K. icx_cbn. cbn [l_SP l_SPA l_Zs l_F0 l_lo] in K.
    assert (SUBW : sub_fp [(lo, SPA + 536)] [(F0, F0 + 64); (Z.shiftr F0 3 + 2147450880, Z.shiftr F0 3 + 2147450880 + 8); (lo, SPA + 536); (S + 8, S + 12)])
      by (intros x Hx; cbn [outside] in *; tauto).
    zbr0 KT.
    -
      rw_split FRA 59%nat FRA1 FRA2. apply rw_cells_forget in FRA1. destruct FRA1 as [jB FRA1]. cbn [cells_size csize Nat.add] in FRA1.
      pose proof (sh0_mu _ _ _ _ _ SHZ MU DJZ6) as SHZ1. pose proof (sh0_mu _ _ _ _ _ SHS MU DJS6) as SHS1.
      eapply (inf_hdr2 SP SPA Zs F0 lo S D n osz cin cout hold bits mode); try eassumption; try lia.
      intros until m'. intros FRM' MU2 WM2 MI2 STK2.
      eapply K; [exact FRM'| | | | eapply munch_trans; [exact MU| eapply munch_weaken; [exact SUBW| exact MU2]]
                | eapply wmono_trans; [exact WM| exact WM2]| exact MI2| exact STK2].
      + replace (mode_load mode) with mode by (unfold mode_load; destruct (Z.eqb_spec mode TYPE) as [E|E]; [exfalso; cbv [TYPE] in E; lia| reflexivity]).
        eapply rw_cells_transport; [exact SSC| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add disjoint_from]. lia.
      + eapply rw_cells_transport; [exact FK| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add disjoint_from]. lia.
      + eapply rw_cells_transport; [exact FKSH| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add disjoint_from]. lia.
    -
      zrunb [0x8e0e0].
      rw_split FRA 59%nat FRA1 FRA2. apply rw_cells_forget in FRA1. destruct FRA1 as [jB FRA1]. cbn [cells_size csize Nat.add] in FRA1.
      pose proof (sh0_mu _ _ _ _ _ SHZ MU DJZ6) as SHZ1. pose proof (sh0_mu _ _ _ _ _ SHS MU DJS6) as SHS1.
      eapply (inf_hdr2 SP SPA Zs F0 lo S D n osz cin cout hold bits 16192); try eassumption; try lia.
      intros until m'. intros FRM' MU2 WM2 MI2 STK2.
      eapply K; [exact FRM'| | | | eapply munch_trans; [exact MU| eapply munch_weaken; [exact SUBW| exact MU2]]
                | eapply wmono_trans; [exact WM| exact WM2]| exact MI2| exact STK2].
      + replace (mode_load mode) with 16192 by (unfold mode_load; destruct (Z.eqb_spec mode TYPE) as [E|E]; [reflexivity| exfalso; cbv [TYPE] in E; lia]).
        eapply rw_cells_transport; [exact SSC| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add disjoint_from]. lia.
      + eapply rw_cells_transport; [exact FK| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add disjoint_from]. lia.
      + eapply rw_cells_transport; [exact FKSH| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add disjoint_from]. lia.
  Qed.
End S.
End CANSEC1.
