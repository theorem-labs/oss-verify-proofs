(* reloc-zl14c b1d40bce5356adf766ae213f6c20f572 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AObj U2AClient U2AIface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (Fu Zs S Wd lo : Z) (RNG : footprint).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOS : lo <= SP - (64 + 4096).
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

  Definition end_W : list (Z * Z) := [(SP - 64, SP); (Zs, Zs + 112)].
  Definition end_FR : list cell := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Notation BODY pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 v6 x28 x29 x30 x31 mm :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -64)) gp tp x5 x6 x7 (Z_to_bv 64 (Zs + 56)) (Z_to_bv 64 (Zs + 72)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (Zs + 80)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (Zs + 56) 3 + 2147450880))
             (Z_to_bv 64 (Z.shiftr (Zs + 72) 3 + 2147450880)) v6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Section Entry.
  Variables (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : amem) (mode : Z).
  Variables (next_in avail_in total_in next_out avail_out total_out msg opaque data_type adler reserved p1 p2 p3 : word).
  Variables (last wrap havedict flags dmax check total head wbits wsize whave wnext hold bits
             length offset extra lencode distcode lenbits distbits ncode nlen ndist have next : word).
  Hypothesis ST : stk asegs m lo SP.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis STRM : rw_cells asegs m Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg (Z_to_bv 64 S)
                                    (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) opaque data_type adler reserved p1 p2 p3).
  Hypothesis SSC : rw_cells asegs m S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 mode) last wrap havedict flags dmax check total head wbits wsize whave wnext
                                     (Z_to_bv 64 Wd) hold bits length offset extra lencode distcode lenbits distbits ncode nlen ndist have next).
  Hypothesis MODE : 16180 <= mode <= 16211.
  Hypothesis SHZ : shadow_bytes m (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0).
  Hypothesis SHS : shadow_bytes m (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0).

  Local Ltac end_setup :=
    unfold end_W, end_FR, A_INFLATEEND, A_ZCALLOC, A_ZCFREE, AFREE_SYM, strm_cells, istate_cells in *;
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP; unfold KEND in SPT;
    atop_facts; pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4); unfold AIMG_HI in FB1;
    pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4); unfold AIMG_HI in SB1;
    assert (Z8 : Zs mod 8 = 0) by (subst Zs; Z.div_mod_to_equations; lia);
    assert (S8 : S mod 8 = 0) by (Z.div_mod_to_equations; lia).

  (* [comment removed for export] *)
  Lemma end_preW : 0 < Wd < 2^64 ->
    evtF asegs RNG (fun ms' => exists m' (x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        ms' = BODY AFREE_SYM (Z_to_bv 64 0x93f88) x5 x6 x7 (Z_to_bv 64 Wd) (Z_to_bv 64 Wd) opaque (Z_to_bv 64 A_ZCFREE) x14 x15 x16 x17
                   (Z_to_bv 64 Zs) x28 x29 x30 x31 m'
        /\ munch end_W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (SP + -64)
        /\ rw_cells asegs m' (SP + -64) end_FR
        /\ rw_cells asegs m' Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg (Z_to_bv 64 S)
                                    (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) opaque data_type adler reserved p1 p2 p3))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Zs) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 A_INFLATEEND) fc None m (seg_rom asegs)).
  Proof using All.
    intros WDR. end_setup.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose (W := [(SP - 64, SP); (Zs, Zs + 112)]).
    assert (DJZ : disjoint_from W (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14 - (Z.shiftr Zs 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, SB. Z.div_mod_to_equations. lia. }
    assert (DJS : disjoint_from W (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, SB. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM. subst W.
    zstep. (* [comment removed for export] *)
    carve_frame 64%nat ST.
    zrunb [0x93f84].
    zs. zs. zs. (* [comment removed for export] *)
    apply evtF_done. eexists _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|].
    replace (SP - 64) with (SP + -64) by lia.
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR0| exact STRM].
  Qed.

  (* [comment removed for export] *)
  Lemma end_preNW : Wd = 0 ->
    evtF asegs RNG (fun ms' => exists m' (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        ms' = BODY AFREE_SYM (Z_to_bv 64 0x93fbc) x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 S) (Z_to_bv 64 A_ZCFREE) x13 x14 x15 x16 x17
                   s6 x28 x29 x30 x31 m'
        /\ munch end_W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (SP + -64)
        /\ rw_cells asegs m' (SP + -64) end_FR
        /\ rw_cells asegs m' Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg (Z_to_bv 64 S)
                                    (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) opaque data_type adler reserved p1 p2 p3))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Zs) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 A_INFLATEEND) fc None m (seg_rom asegs)).
  Proof using All.
    intros WD0. subst Wd. end_setup.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose (W := [(SP - 64, SP); (Zs, Zs + 112)]).
    assert (DJZ : disjoint_from W (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14 - (Z.shiftr Zs 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, SB. Z.div_mod_to_equations. lia. }
    assert (DJS : disjoint_from W (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, SB. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM. subst W.
    zstep. (* [comment removed for export] *)
    carve_frame 64%nat ST.
    zrunb [0x93fb8].
    zs. zs. zs. (* [comment removed for export] *)
    apply evtF_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|].
    replace (SP - 64) with (SP + -64) by lia.
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR0| exact STRM].
  Qed.
  End Entry.

  (* [comment removed for export] *)
  Lemma end_mid : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m
      (next_in avail_in total_in next_out avail_out total_out msg opaque data_type adler reserved p1 p2 p3 : word),
    stk asegs m lo (SP + -64) -> mem_inv asegs m ->
    rw_cells asegs m Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg (Z_to_bv 64 S)
                                    (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) opaque data_type adler reserved p1 p2 p3) ->
    shadow_bytes m (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0) ->
    evtF asegs RNG (fun ms' => exists (y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        ms' = BODY AFREE_SYM (Z_to_bv 64 0x93fbc) y5 y6 y7 (Z_to_bv 64 S) (Z_to_bv 64 S) (Z_to_bv 64 A_ZCFREE) y13 y14 y15 y16 y17
                   (Z_to_bv 64 Zs) y28 y29 y30 y31 m)
      (BODY 0x93f88 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 Zs) x28 x29 x30 x31 m).
  Proof using All.
    intros until p3. intros ST MI STRM SHZ.
    unfold A_ZCALLOC, A_ZCFREE, AFREE_SYM, strm_cells in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    assert (Z8 : Zs mod 8 = 0) by (subst Zs; Z.div_mod_to_equations; lia).
    zrunb [0x93fb8].
    zs. zs. zs.
    apply evtF_done. eexists _, _, _, _, _, _, _, _, _, _, _, _. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma end_fin : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 v6 x28 x29 x30 x31 : word) m
      (next_in avail_in total_in next_out avail_out total_out msg state opaque data_type adler reserved p1 p2 p3 : word),
    stk asegs m lo (SP + -64) -> mem_inv asegs m ->
    rw_cells asegs m (SP + -64) end_FR ->
    rw_cells asegs m Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg state
                                    (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) opaque data_type adler reserved p1 p2 p3) ->
    shadow_bytes m (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0) ->
    evtF asegs RNG (fun ms' => exists (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m',
        ms' = MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 FR (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch end_W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo SP
        /\ rw_cells asegs m' Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg (Z_to_bv 64 0)
                                    (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) opaque data_type adler reserved p1 p2 p3))
      (BODY 0x93fbc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 v6 x28 x29 x30 x31 m).
  Proof using All.
    intros until p3. intros ST MI FR0 STRM SHZ.
    unfold end_W, end_FR, A_ZCALLOC, A_ZCFREE, strm_cells in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    assert (Z8 : Zs mod 8 = 0) by (subst Zs; Z.div_mod_to_equations; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose (W := [(SP - 64, SP); (Zs, Zs + 112)]).
    assert (DJZ : disjoint_from W (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14 - (Z.shiftr Zs 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM. subst W.
    zrunb [0x93ff4].
    lazymatch goal with H : stk asegs _ lo (SP + -64) |- _ => rename H into STK end.
    release_frame FR0 STK (bv_unsigned sp).
    zstep. (* [comment removed for export] *)
    apply evtF_done. do 14 eexists. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK| exact STRM].
  Qed.
End S.
End CANSEC1.
