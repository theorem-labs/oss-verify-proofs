(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit I_asan_memcpy.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2ABlob UwAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U1A Require Import U2AObj U2AClient U2ACall U2AIface U2AIfaceS UwA_copy.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac znorm ::=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?e)] => first [ rewrite (sx32_small e) by lia | rewrite (sx32_sint e) by lia ]
  | |- context [zx32 (Z_to_bv 64 ?e)] => rewrite (zx32_small e) by lia
  | |- context [bv_swrap 32 (?e + ?l)] =>
      is_Zlit l;
      let big := eval vm_compute in (9223372036854775808 <=? l) in
      lazymatch big with true => idtac end;
      let k := eval vm_compute in (18446744073709551616 - l) in
      change l with (18446744073709551616 - k); rewrite (swrap32_sublit e k) by lia
  | |- context [bv_swrap 32 ?e] => rewrite (swrap32_small e) by lia
  | |- context [?e mod 4294967296] => rewrite (Z.mod_small e 4294967296) by lia
  end.

Ltac uw_side WB W8 SHW SHO MU DJW DJO WRO WRW WM RWH RISH RSTK RW RI WHULL lo :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- app_blk ?a _ => first [ eapply ablk_app_blk; [eapply ablk_sub; [exact WB| lia| lia]| lia]
                             | unfold app_blk, KLOW, KHIGH, KEND; lia ]
  | |- unpoisoned _ ?a _ =>
      first [ eapply (unp_of_sh0 _ _ 4096); [exact (sh0_mu _ _ _ _ _ SHW MU DJW)| exact W8| lia| lia| lia| lia| lia]
            | eapply (unp_of_sh0 _ 6335680 32768); [exact (sh0_mu _ _ _ _ _ SHO MU DJO)| reflexivity| lia| lia| lia| lia| lia] ]
  | |- wr_at _ _ (shad 6335680) _ => replace (shad (6335680 + 262144) - shad 6335680) with 32768 by (rewrite !shad_div; reflexivity);
                                      first [exact WRO| eapply wr_at_transport; [exact WRO| exact WM]]
  | |- wr_at _ _ (shad _) _ => first [exact WRW| eapply wr_at_transport; [exact WRW| exact WM]]
  | |- rng _ (shad 6335680) _ => replace (shad (6335680 + 262144) - shad 6335680) with 32768 by (rewrite !shad_div; reflexivity);
                                  eapply rng_sub'; [exact RISH| rewrite shad_div; unfold ASHOFF; lia]
  | |- rng _ (shad _) _ => exact RWH
  | |- rng _ ?l _ => first [ constr_eq l lo; eapply rng_sub'; [exact RSTK| lia]
                           | eapply rng_sub'; [exact RW| lia]
                           | eapply rng_sub'; [exact RI| lia] ]
  | |- _ /\ _ => first [ repeat split; first [reflexivity| lia]
                       | destruct WHULL as (H1 & H2 & H3 & H4 & H5 & H6); repeat split; first [lia| Z.div_mod_to_equations; lia] ]
  | |- _ => first [ assumption | unfold KHIGH, KEND in *; lia ]
  end.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (Fu Zs S lo : Z) (RNG : footprint).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOS : lo <= SP - (112 + 4096).
  Hypothesis LOC : ATOP + 4096 <= lo.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis ZSE : Zs = Fu + 32.
  Hypothesis FU256 : Fu mod 256 = 0.
  Hypothesis FUB : ablk Fu (Fu + 256).
  Hypothesis SB : ablk S (S + 7176).
  Hypothesis S16 : S mod 16 = 0.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RZ : rng RNG Zs 112.
  Hypothesis RSZ : rng RNG (Z.shiftr Zs 3 + 2147450880) 14.
  Hypothesis RS : rng RNG S 7176.
  Hypothesis RSS : rng RNG (Z.shiftr S 3 + 2147450880) 897.

  Notation FRc j8 := (CB 8 j8 :: uw_FR ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  Section Entry.
  Variables (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : amem) (cout copy mode : Z).
  Variables (next_in avail_in total_in next_out avail_out total_out msg opaque data_type adler reserved p1 p2 p3 : word).
  Variables (last wrap havedict flags dmax check total head hold bits
             length offset extra lencode distcode lenbits distbits ncode nlen ndist have next : word).
  Hypothesis ST : stk asegs m lo SP.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis STRM : rw_cells asegs m Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg (Z_to_bv 64 S)
                                    (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) opaque data_type adler reserved p1 p2 p3).
  Hypothesis SHZ : shadow_bytes m (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0).
  Hypothesis SHS : shadow_bytes m (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0).

  Local Ltac uw_setup :=
    unfold A_UPDATEWINDOW, A_ZCALLOC, A_ZCFREE, AMALLOC_SYM, strm_cells, istate_cells, uw_FR in *;
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP; unfold KEND in SPT;
    atop_facts; pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4); unfold AIMG_HI in FB1;
    pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4); unfold AIMG_HI in SB1;
    assert (Z8 : Zs mod 8 = 0) by (subst Zs; Z.div_mod_to_equations; lia);
    assert (S8 : S mod 8 = 0) by (Z.div_mod_to_equations; lia).

  Lemma uw_preO : forall (Wd wn wh : Z), 0 < Wd < 2^64 ->
    rw_cells asegs m S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 mode) last wrap havedict flags dmax check total head (Z_to_bv 64 15)
                                     (Z_to_bv 64 32768) (Z_to_bv 64 wh) (Z_to_bv 64 wn)
                                     (Z_to_bv 64 Wd) hold bits length offset extra lencode distcode lenbits distbits ncode nlen ndist have next) ->
    evtF asegs RNG (fun ms' => exists m' (j8 : list byte),
        ms' = MS (mkR ra (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (S + 72)) (Z_to_bv 64 (6335680 + cout))
                     (Z_to_bv 64 32768) (Z_to_bv 64 Wd) (Z_to_bv 64 (Zs + 56)) (Z_to_bv 64 0) a4 a5 a6 a7
                     (Z_to_bv 64 copy) (Z_to_bv 64 (S + 88)) s4 (Z_to_bv 64 2147450880) (Z_to_bv 64 S)
                     (Z_to_bv 64 (Z.shiftr (S + 72) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (S + 88) 3 + 2147450880)) s9 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 0x937e0) fc None m' (seg_rom asegs)
        /\ munch [(SP - 112, SP)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (SP + -112)
        /\ rw_cells asegs m' (SP + -112) (FRc j8))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Zs) (Z_to_bv 64 (6335680 + cout)) (Z_to_bv 64 copy) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 A_UPDATEWINDOW) fc None m (seg_rom asegs)).
  Proof using All.
    intros Wd wn wh WDR SSC. uw_setup.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose (W := [(SP - 112, SP)]).
    assert (DJZ : disjoint_from W (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14 - (Z.shiftr Zs 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, SB. Z.div_mod_to_equations. lia. }
    assert (DJS : disjoint_from W (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, SB. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM. subst W.
    zstep.
    carve_frame 112%nat ST.
    zrunb [0x937e0].
    apply evtF_done. eexists _, _. split; [reflexivity|].
    replace (SP - 112) with (SP + -112) by lia.
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR0].
  Qed.

  Lemma uw_preN : forall (wsize whave wnext : word),
    rw_cells asegs m S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 mode) last wrap havedict flags dmax check total head (Z_to_bv 64 15)
                                     wsize whave wnext
                                     (Z_to_bv 64 0) hold bits length offset extra lencode distcode lenbits distbits ncode nlen ndist have next) ->
    evtF asegs RNG (fun ms' => exists m' (j8 : list byte) (a4' : word),
        ms' = MS (mkR (Z_to_bv 64 0x93750) (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (6335680 + cout))
                     (Z_to_bv 64 32768) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 A_ZCALLOC) a4' a5 a6 a7
                     (Z_to_bv 64 copy) (Z_to_bv 64 (S + 88)) s4 (Z_to_bv 64 2147450880) (Z_to_bv 64 S)
                     s7 (Z_to_bv 64 (Z.shiftr (S + 88) 3 + 2147450880)) s9 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 AMALLOC_SYM) fc None m' (seg_rom asegs)
        /\ munch [(SP - 112, SP)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (SP + -112)
        /\ rw_cells asegs m' (SP + -112) (FRc j8))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Zs) (Z_to_bv 64 (6335680 + cout)) (Z_to_bv 64 copy) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 A_UPDATEWINDOW) fc None m (seg_rom asegs)).
  Proof using All.
    intros wsize whave wnext SSC. uw_setup.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose (W := [(SP - 112, SP)]).
    assert (DJZ : disjoint_from W (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14 - (Z.shiftr Zs 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, SB. Z.div_mod_to_equations. lia. }
    assert (DJS : disjoint_from W (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, SB. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM. subst W.
    zstep.
    carve_frame 112%nat ST.
    zrunb [0x9374c].
    zs.
    zs. zs. zs. zs.
    apply evtF_done. eexists _, _, _. split; [reflexivity|].
    replace (SP - 112) with (SP + -112) by lia.
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR0].
  Qed.
  End Entry.

  Lemma uw_midN : forall (u5 u6 u7 b1 b2 b3 b4 b5 b6 b7 u28 u29 u30 u31 v0 v4 v7 v9 v10 v11 : word) m (Wd cout copy mode : Z)
      (last wrap havedict flags dmax check total head wsize whave wnext hold bits
       length offset extra lencode distcode lenbits distbits ncode nlen ndist have next : word),
    0 < Wd < 2^64 ->
    stk asegs m lo (SP + -112) -> mem_inv asegs m ->
    rw_cells asegs m S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 mode) last wrap havedict flags dmax check total head (Z_to_bv 64 15)
                                     (Z_to_bv 64 0) whave wnext
                                     (Z_to_bv 64 0) hold bits length offset extra lencode distcode lenbits distbits ncode nlen ndist have next) ->
    shadow_bytes m (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0) ->
    evtF asegs RNG (fun ms' => exists m' (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        ms' = MS (mkR (Z_to_bv 64 0x93750) (Z_to_bv 64 (SP + -112)) gp tp x5 x6 x7 (Z_to_bv 64 (S + 72)) (Z_to_bv 64 (6335680 + cout))
                     x10 x11 x12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 copy) (Z_to_bv 64 (S + 88)) v4 (Z_to_bv 64 2147450880) (Z_to_bv 64 S)
                     (Z_to_bv 64 (Z.shiftr (S + 72) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (S + 88) 3 + 2147450880)) v9 v10 v11 x28 x29 x30 x31)
                 FR (Z_to_bv 64 0x937e0) fc None m' (seg_rom asegs)
        /\ munch [(S + 68, S + 96)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (SP + -112)
        /\ rw_cells asegs m' S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 mode) last wrap havedict flags dmax check total head (Z_to_bv 64 15)
                                     (Z_to_bv 64 32768) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                     (Z_to_bv 64 Wd) hold bits length offset extra lencode distcode lenbits distbits ncode nlen ndist have next))
      (MS (mkR (Z_to_bv 64 0x93750) (Z_to_bv 64 (SP + -112)) gp tp u5 u6 u7 v0 (Z_to_bv 64 (6335680 + cout))
               (Z_to_bv 64 Wd) b1 b2 b3 b4 b5 b6 b7
               (Z_to_bv 64 copy) (Z_to_bv 64 (S + 88)) v4 (Z_to_bv 64 2147450880) (Z_to_bv 64 S)
               v7 (Z_to_bv 64 (Z.shiftr (S + 88) 3 + 2147450880)) v9 v10 v11 u28 u29 u30 u31)
          FR (Z_to_bv 64 0x93750) fc None m (seg_rom asegs)).
  Proof using All.
    intros until next. intros WDR ST MI SSC SHS.
    unfold istate_cells in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). unfold AIMG_HI in SB1.
    assert (S8 : S mod 8 = 0) by (Z.div_mod_to_equations; lia).
    pose (W := [(S + 68, S + 96)]).
    assert (DJS : disjoint_from W (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in SB. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM. subst W.
    zrunb [0x937e0].
    apply evtF_done. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption| exact SSC].
  Qed.
End S.
End CANSEC1.
