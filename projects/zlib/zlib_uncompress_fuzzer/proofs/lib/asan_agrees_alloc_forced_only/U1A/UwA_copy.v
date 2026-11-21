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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U1A Require Import U2AObj U2AClient U2ACall U2AIface U2AIfaceS.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac key_assumption :=
  lazymatch goal with
  | |- rw_cells ?segs ?m ?A _ => match goal with H : rw_cells segs m A _ |- _ => exact H end
  | |- shadow_bytes ?m ?A _ _ => match goal with H : shadow_bytes m A _ _ |- _ => exact H end
  | |- wr_at ?segs ?m ?A _ => match goal with H : wr_at segs m A _ |- _ => exact H end
  | |- stk ?segs ?m _ _ => match goal with H : stk segs m _ _ |- _ => exact H end
  | |- mem_inv ?segs ?m => match goal with H : mem_inv segs m |- _ => exact H end
  end.
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

Lemma uw_next_full : forall wn wh copy, 32768 <= copy -> uw_next 32768 wn wh copy = (0, 32768).
Proof. intros wn wh copy H. unfold uw_next. change (32768 =? 0) with false. cbv iota. destruct (Z.leb_spec 32768 copy); [reflexivity| lia]. Qed.
Lemma uw_next_wrap : forall wn wh copy, copy < 32768 -> 32768 - wn < copy ->
  uw_next 32768 wn wh copy = (copy - (32768 - wn), 32768).
Proof.
  intros wn wh copy H1 H2. unfold uw_next. change (32768 =? 0) with false. cbv iota.
  destruct (Z.leb_spec 32768 copy); [lia|]. rewrite Z.min_l by lia.
  destruct (Z.eqb_spec (copy - (32768 - wn)) 0); [lia| reflexivity].
Qed.
Lemma uw_next_nowrap : forall wn wh copy, copy < 32768 -> copy <= 32768 - wn ->
  uw_next 32768 wn wh copy = ((if wn + copy =? 32768 then 0 else wn + copy), (if wh <? 32768 then wh + copy else wh)).
Proof.
  intros wn wh copy H1 H2. unfold uw_next. change (32768 =? 0) with false. cbv iota.
  destruct (Z.leb_spec 32768 copy); [lia|]. rewrite Z.min_r by lia.
  rewrite Z.sub_diag. reflexivity.
Qed.

Lemma sel_val : forall x, 0 <= x < 4294967296 ->
  Z.land ((Z.b2z (Z.lxor x 32768 <? 1) + -1) mod 18446744073709551616) x = if x =? 32768 then 0 else x.
Proof.
  intros x Hx. destruct (Z.eqb_spec x 32768) as [->|NE].
  - reflexivity.
  - assert (L0 : 0 <= Z.lxor x 32768) by (apply Z.lxor_nonneg; lia).
    assert (L1 : Z.lxor x 32768 <> 0) by (intros E; apply Z.lxor_eq in E; lia).
    destruct (Z.ltb_spec (Z.lxor x 32768) 1); [lia|]. cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

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

  Variables (Wd WLO WHI : Z).
  Hypothesis WB : ablk Wd (Wd + 32768).
  Hypothesis W16 : Wd mod 16 = 0.
  Hypothesis RW : rng RNG Wd 32768.
  Hypothesis SEPW : S + 7176 <= Wd \/ Wd + 32768 <= S.
  Hypothesis WHULL : WLO <= Wd /\ Wd + 32768 <= WHI /\ WLO mod 64 = 0 /\ WHI mod 64 = 0 /\ 0 <= WLO /\ WHI <= KEND.
  Hypothesis RWH : rng RNG (shad WLO) (shad WHI - shad WLO).
  Hypothesis RISH : rng_aimg_sh RNG.

  Notation BODY pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 v4 v9 v10 v11 x28 x29 x30 x31 cout copy mm :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -112)) gp tp x5 x6 x7 (Z_to_bv 64 (S + 72)) (Z_to_bv 64 (6335680 + cout)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 copy) (Z_to_bv 64 (S + 88)) v4 (Z_to_bv 64 2147450880) (Z_to_bv 64 S)
             (Z_to_bv 64 (Z.shiftr (S + 72) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (S + 88) 3 + 2147450880)) v9 v10 v11 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition uw_cW : list (Z * Z) := [(lo, SP); (S + 68, S + 96); (Wd, Wd + 32768)].
  Definition uw_FR : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma uw_copy : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 v4 v9 v10 v11 x28 x29 x30 x31 : word) m (cout copy mode wn wh : Z) (j8 : list byte)
      (last wrap havedict flags dmax check total head hold bits
       length offset extra lencode distcode lenbits distbits ncode nlen ndist have next : word) (wbytes obs : list byte),
    stk asegs m lo (SP + -112) -> mem_inv asegs m ->
    rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
    rw_cells asegs m (SP + -112) (CB 8 j8 :: uw_FR) ->
    rw_cells asegs m S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 mode) last wrap havedict flags dmax check total head (Z_to_bv 64 15)
                                     (Z_to_bv 64 32768) (Z_to_bv 64 wh) (Z_to_bv 64 wn)
                                     (Z_to_bv 64 Wd) hold bits length offset extra lencode distcode lenbits distbits ncode nlen ndist have next) ->
    rw_cells asegs m Wd [CB (Z.to_nat 32768) wbytes] ->
    rw_cells asegs m 6335680 [CB (Z.to_nat 262144) obs] ->
    shadow_bytes m (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0) ->
    shadow_bytes m (Z.shiftr Wd 3 + 2147450880) (Z.shiftr Wd 3 + 2147450880 + 4096) (fun _ => 0) ->
    shadow_bytes m (Z.shiftr 6335680 3 + 2147450880) (Z.shiftr 6335680 3 + 2147450880 + 32768) (fun _ => 0) ->
    wr_at asegs m (shad WLO) (shad WHI - shad WLO) ->
    wr_at asegs m (shad 6335680) 32768 ->
    0 <= copy <= cout -> cout <= 262144 -> 0 <= wn < 32768 -> 0 <= wh <= 32768 ->
    evtF asegs RNG (fun ms' => exists (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m' (wbytes' : list byte),
        ms' = MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 FR (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch uw_cW m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo SP
        /\ rw_cells asegs m' S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 mode) last wrap havedict flags dmax check total head (Z_to_bv 64 15)
                                     (Z_to_bv 64 32768) (Z_to_bv 64 (snd (uw_next 32768 wn wh copy))) (Z_to_bv 64 (fst (uw_next 32768 wn wh copy)))
                                     (Z_to_bv 64 Wd) hold bits length offset extra lencode distcode lenbits distbits ncode nlen ndist have next)
        /\ rw_cells asegs m' Wd [CB (Z.to_nat 32768) wbytes'])
      (BODY 0x937e0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 v4 v9 v10 v11 x28 x29 x30 x31 cout copy m).
  Proof using All.
    intros until obs. intros ST MI GOT RIC SHB INI LAY REAL FR0 SSC WBLK OBLK SHS SHW SHO WRW WRO CPY COUT WN WH.
    unfold uw_cW, uw_FR, istate_cells in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). unfold AIMG_HI in SB1.
    pose proof (ablk_lin _ _ WB) as (WB1 & WB2 & WB3 & WB4). unfold AIMG_HI in WB1.
    assert (S8 : S mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (W8 : Wd mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose (W := [(lo, SP); (S + 68, S + 96); (Wd, Wd + 32768)]).
    assert (DJS : disjoint_from W (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, SB, WB. Z.div_mod_to_equations. lia. }
    assert (DJW : disjoint_from W (Z.shiftr Wd 3 + 2147450880) (Z.shiftr Wd 3 + 2147450880 + 4096 - (Z.shiftr Wd 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, SB, WB. Z.div_mod_to_equations. lia. }
    assert (DJO : disjoint_from W (Z.shiftr 6335680 3 + 2147450880) (Z.shiftr 6335680 3 + 2147450880 + 32768 - (Z.shiftr 6335680 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. change (Z.shiftr 6335680 3) with 791960. unfold ablk, AIMG_HI, KLS in FUB, SB, WB. lia. }
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM. subst W.
    zrunb [0x93840; 0x93864; 0x938b8].
    zbr K.
    -
      zrunb [0x938b8].
      destruct (blob_src asegs _ _ _ _ (cout - 32768) 32768 OBLK ltac:(lia) ltac:(lia) ltac:(lia)) as (src & SRC & SRCL).
      replace (6335680 + (cout - 32768)) with (6335680 + cout - 32768) in SRC by lia.
      zs.
      callq (asan_memcpy_callz 6335680 (6335680 + 262144) WLO WHI RNG).
      all: lazymatch goal with
           | |- bytes_at _ _ _ _ => exact SRC
           | |- length _ = _ => exact SRCL
           | |- rw_cells _ _ _ [CB _ _] => exact WBLK
           | |- stk _ _ _ _ => exact ST
           | |- mem_inv _ _ => exact MI
           | |- _ => uw_side WB W8 SHW SHO MU DJW DJO WRO WRW WM RWH RISH RSTK RW RI WHULL lo
           end.
      zrunb [0x93998].
      lazymatch goal with H : stk asegs _ lo (SP + -112) |- _ => rename H into STK end.
      release_frame FR0 STK (bv_unsigned sp).
      zstep.
      apply evtF_done. do 14 eexists. eexists _, _. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [first [key_assumption | eassumption]|]. split; [exact STK|].
      rewrite (uw_next_full wn wh copy K).
      split; [first [key_assumption | eassumption]| first [key_assumption | eassumption]].
    -
      zrunb [0x93840; 0x93864].
      zbr K2.
      +
        zrunb [0x93840].
        destruct (blob_src asegs _ _ _ _ (cout - copy) (32768 - wn) OBLK ltac:(lia) ltac:(lia) ltac:(lia)) as (src & SRC & SRCL).
        replace (6335680 + (cout - copy)) with (6335680 + cout - copy) in SRC by lia.
        destruct (blob_split3 asegs _ _ _ _ wn (32768 - wn) WBLK ltac:(lia) ltac:(lia) ltac:(lia)) as (b1 & b2 & b3 & WPRE & WTGT & WSUF).
        clear WBLK.
        zs.
        callq (asan_memcpy_callz 6335680 (6335680 + 262144) WLO WHI RNG).
        all: lazymatch goal with
             | |- bytes_at _ _ _ _ => exact SRC
             | |- length _ = _ => exact SRCL
             | |- rw_cells _ _ _ [CB _ _] => exact WTGT
             | |- stk _ _ _ _ => exact ST
             | |- mem_inv _ _ => exact MI
             | |- _ => uw_side WB W8 SHW SHO MU DJW DJO WRO WRW WM RWH RISH RSTK RW RI WHULL lo
             end.
        pose proof (blob_join3 asegs _ Wd 32768 wn (32768 - wn) _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WPRE PC0 WSUF) as WBLK.
        clear WPRE PC0 WSUF POST.
        zrunb [0x93864].
        destruct (blob_src asegs _ _ _ _ (cout - (copy - (32768 - wn))) (copy - (32768 - wn)) OBLK ltac:(lia) ltac:(lia) ltac:(lia)) as (src2 & SRC2 & SRCL2).
        replace (6335680 + (cout - (copy - (32768 - wn)))) with (6335680 + cout - (copy - (32768 - wn))) in SRC2 by lia.
        destruct (blob_split3 asegs _ _ _ _ 0 (copy - (32768 - wn)) WBLK ltac:(lia) ltac:(lia) ltac:(lia)) as (c1 & c2 & c3 & WPRE & WTGT & WSUF).
        rewrite Z.add_0_r in WTGT. clear WBLK.
        zs.
        callq (asan_memcpy_callz 6335680 (6335680 + 262144) WLO WHI RNG).
        all: lazymatch goal with
             | |- bytes_at _ _ _ _ => exact SRC2
             | |- length _ = _ => exact SRCL2
             | |- rw_cells _ _ _ [CB _ _] => exact WTGT
             | |- stk _ _ _ _ => eassumption
             | |- mem_inv _ _ => eassumption
             | |- _ => uw_side WB W8 SHW SHO MU DJW DJO WRO WRW WM RWH RISH RSTK RW RI WHULL lo
             end.
        rewrite <- (Z.add_0_r Wd) in PC0 at 1.
        pose proof (blob_join3 asegs _ Wd 32768 0 (copy - (32768 - wn)) _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WPRE PC0 WSUF) as WBLK.
        clear WPRE PC0 WSUF.
        zrunb [0x93998].
        lazymatch goal with H : stk asegs _ lo (SP + -112) |- _ => rename H into STK end.
        release_frame FR0 STK (bv_unsigned sp).
        zstep.
        apply evtF_done. do 14 eexists. eexists _, _. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [first [key_assumption | eassumption]|]. split; [exact STK|].
        rewrite (uw_next_wrap wn wh copy ltac:(lia) K2). cbn [fst snd].
        split; [first [key_assumption | eassumption]| exact WBLK].
      +
        zrunb [0x93840].
        destruct (blob_src asegs _ _ _ _ (cout - copy) copy OBLK ltac:(lia) ltac:(lia) ltac:(lia)) as (src & SRC & SRCL).
        replace (6335680 + (cout - copy)) with (6335680 + cout - copy) in SRC by lia.
        destruct (blob_split3 asegs _ _ _ _ wn copy WBLK ltac:(lia) ltac:(lia) ltac:(lia)) as (b1 & b2 & b3 & WPRE & WTGT & WSUF).
        clear WBLK.
        zs.
        callq (asan_memcpy_callz 6335680 (6335680 + 262144) WLO WHI RNG).
        all: lazymatch goal with
             | |- bytes_at _ _ _ _ => exact SRC
             | |- length _ = _ => exact SRCL
             | |- rw_cells _ _ _ [CB _ _] => exact WTGT
             | |- stk _ _ _ _ => eassumption
             | |- mem_inv _ _ => eassumption
             | |- _ => uw_side WB W8 SHW SHO MU DJW DJO WRO WRW WM RWH RISH RSTK RW RI WHULL lo
             end.
        pose proof (blob_join3 asegs _ Wd 32768 wn copy _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WPRE PC0 WSUF) as WBLK.
        clear WPRE PC0 WSUF POST.
        zrunb [0x93930].
        rewrite (sel_val (wn + copy)) by lia.
        zrunb [0x93998].
        zbr K3.
        *
          zrunb [0x93998].
          lazymatch goal with H : stk asegs _ lo (SP + -112) |- _ => rename H into STK end.
          release_frame FR0 STK (bv_unsigned sp).
          zstep.
          apply evtF_done. do 14 eexists. eexists _, _. split; [reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [first [key_assumption | eassumption]|]. split; [exact STK|].
          rewrite (uw_next_nowrap wn wh copy ltac:(lia) ltac:(lia)). cbn [fst snd].
          destruct (Z.ltb_spec wh 32768) as [C|C]; [exfalso; lia|].
          split; [first [key_assumption | eassumption]| exact WBLK].
        *
          zrunb [0x93998].
          lazymatch goal with H : stk asegs _ lo (SP + -112) |- _ => rename H into STK end.
          release_frame FR0 STK (bv_unsigned sp).
          zstep.
          apply evtF_done. do 14 eexists. eexists _, _. split; [reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [first [key_assumption | eassumption]|]. split; [exact STK|].
          rewrite (uw_next_nowrap wn wh copy ltac:(lia) ltac:(lia)). cbn [fst snd].
          destruct (Z.ltb_spec wh 32768) as [C|C]; [| exfalso; lia].
          split; [first [key_assumption | eassumption]| exact WBLK].
  Qed.
End S.
End CANSEC1.
