(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit U2ABlob ItAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BObj U2BClient U2BCall U2BGlue U2BIface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import StrFun RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Section CANSEC1. Context {rc : runConstT}.
Lemma c1z4_sh0 : forall m s, rw_cells bsegs m s [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  0x67f000 <= s -> shadow_bytes m s (s + 4) (fun _ => 0).
Proof.
  intros m s [[_ Hb] _] Hs. cbn [cells_bytes cbytes app] in Hb.
  apply (shadow_bytes_of_bytes_at bsegs m s _ (fun _ => 0) Hb); [apply no_image_asan; exact Hs|].
  intros i Hi. cbn [length] in Hi. do 4 (destruct i as [|i]; [reflexivity|]). lia.
Qed.
Lemma zero32_f16arr : forall m A, rw_cells bsegs m A [CB 32 (repeat (Z_to_bv 8 0) 32)] -> f16arr bsegs m A 16 (fun _ => 0).
Proof.
  intros m A [[_ Hb] Hw]. cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb. split; [exact Hb | exact Hw].
Qed.
Lemma any32_f16arr : forall m A (bs : list byte), rw_cells bsegs m A [CB 32 bs] -> exists f, f16arr bsegs m A 16 f.
Proof.
  intros m A bs H.
  apply (rw_cells_chop bsegs m A 32 bs (repeat SH2 16)) in H; [| reflexivity].
  cbn [chop chop1 shape_size repeat] in H.
  lazymatch type of H with rw_cells _ _ _ [C2 ?w0; C2 ?w1; C2 ?w2; C2 ?w3; C2 ?w4; C2 ?w5; C2 ?w6; C2 ?w7; C2 ?w8; C2 ?w9; C2 ?w10; C2 ?w11; C2 ?w12; C2 ?w13; C2 ?w14; C2 ?w15] =>
    exists (c2f [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15]);
    exact (f16arr_of_cells bsegs m A [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15] H)
  end.
Qed.

Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (lo SPA : Z) (RNG : footprint).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOS : lo <= SP - 288.
  Hypothesis LOC : ATOP + 4096 <= lo.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis ESPA : SPA = (SP - 256) - (SP - 256) mod 32.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.

  Definition it_SAVED : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma it_pro : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SP -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m -> u2_img m -> rt_suar m ->
    evtF bsegs RNG (fun ms' => exists m' (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v128 v136 v144 : word) (q11 : word),
        ms' = MS (mkR (Z_to_bv 64 0x96ab8) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 160) q11 (Z_to_bv 64 1)
                     a3 a4 a5 a6 a7 s2 a4 (Z_to_bv 64 2147450880) a5 a1 a0 s8 a2 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 ASM2) fc None m' (seg_rom bsegs)
        /\ munch [(SP - 288, SP)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SP + -104) it_SAVED
        /\ rw_cells bsegs m' SPA [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72; C8 v80; C8 v88; C8 v96; C8 v104; C8 v112; C8 a3; C8 v128; C8 v136; C8 v144]
        /\ stk bsegs m' lo SPA /\ stk bsegs m' (SPA + 152) (SP + -104))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 A_ITABLE) fc None m (seg_rom bsegs)).
  Proof using All.
    intros until m. intros ST MI GOT SHB (GSU & GZC) SUA. unfold rt_suar in SUA.
    unfold A_ITABLE, AGOT_SUAR, ASUAR, AGOT_ZCALLOC, ASM2, it_SAVED in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts.
    assert (SPAB : SP - 272 <= SPA <= SP - 256 /\ SPA mod 32 = 0) by (rewrite ESPA; Z.div_mod_to_equations; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 288, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep.
    carve_frame 104%nat ST. carve_frame 152%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_down by lia.
    replace ((SP + -256) - (SP + -256) mod 2^5) with SPA by (rewrite ESPA; change (2^5) with 32; replace (SP + -256) with (SP - 256) by lia; reflexivity).
    release_frame FR1 ST (SP + -104).
    destruct (stk_split bsegs _ lo (SPA + 152) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (SPA + 152) 152 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 152) with 152 in STL, FRA. replace (SPA + 152 - 152) with SPA in STL, FRA by lia.
    apply (rw_cells_chop bsegs _ SPA 152 jA (repeat SH8 19)) in FRA; [| reflexivity].
    cbn [chop chop1 shape_size repeat] in FRA. chop_names FRA.
    zrunb [0x48914].
    apply evtF_done. eexists. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact FR0|].
    split; [exact FRA| split; [exact STL| exact STG]].
  Qed.

  Variables (F PB WK LP : Z).
  Hypothesis F256 : F mod 256 = 0.
  Hypothesis FB : ablk F (F + 256).
  Hypothesis FTOP : F + 256 <= ATOP.
  Hypothesis LOS2 : lo <= SP - 288 - 2208.
  Hypothesis RF : rng RNG F 256.
  Hypothesis RSF : rng RNG (shad F) 32.

  Notation SHF := (Z.shiftr F 3 + 2147450880).
  Definition it_shcells : list cell :=
    [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); c1z; c1z; c1z; c1z;
     C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602); c1z; c1z; c1z; c1z;
     C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); c1z; c1z; c1z; c1z;
     c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z].

  Lemma it_hdr : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) m
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 : word) (j0 j1 j2 flagw : word) (junk : list byte),
    stk bsegs m lo SPA -> mem_inv bsegs m ->
    rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
    rw_cells bsegs m SPA [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72; C8 v80; C8 v88; C8 v96; C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144] ->
    rw_cells bsegs m F [C8 j0; C8 j1; C8 j2; CB 224 junk; C8 flagw] ->
    rw_cells bsegs m (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    evtF bsegs RNG (fun ms' => exists m' (q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word) (jb8 jb32 jb120 : list byte) (of : Z -> Z),
        ms' = MS (mkR q1 (Z_to_bv 64 SPA) gp tp q5 q6 q7 sp (Z_to_bv 64 SPA) q10 q11 q12 q13 q14 q15 q16 q17
                     (Z_to_bv 64 F) (Z_to_bv 64 PB) (Z_to_bv 64 2147450880) (Z_to_bv 64 WK) (Z_to_bv 64 LP) x23 (Z_to_bv 64 (F + 32))
                     x25 (Z_to_bv 64 SHF) (Z_to_bv 64 F) q28 q29 q30 q31)
                 FR (Z_to_bv 64 0x96b90) fc None m' (seg_rom bsegs)
        /\ munch [(lo, SPA + 152); (F, F + 256); (SHF, SHF + 32)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SPA
        /\ rw_cells bsegs m' SPA [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72; C8 v80; C8 v88; C8 v96; C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 (Z_to_bv 64 F)]
        /\ rw_cells bsegs m' F [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 123631); C8 (Z_to_bv 64 617012); CB 8 jb8]
        /\ f16arr bsegs m' (F + 32) 16 (fun _ => 0)
        /\ rw_cells bsegs m' (F + 64) [CB 32 jb32]
        /\ f16arr bsegs m' (F + 96) 16 of
        /\ rw_cells bsegs m' (F + 128) [CB 120 jb120; C8 flagw]
        /\ rw_cells bsegs m' SHF it_shcells)
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 F) x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 PB) (Z_to_bv 64 2147450880) (Z_to_bv 64 WK) (Z_to_bv 64 LP) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x96ab8) fc None m (seg_rom bsegs)).
  Proof using All.
    intros until junk. intros ST MI GOT RIC SHBS INI LAY REAL FRM FF FSH.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof (ablk_lin _ _ FB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    assert (SPAB : SP - 272 <= SPA <= SP - 256 /\ SPA mod 32 = 0) by (rewrite ESPA; Z.div_mod_to_equations; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (F8 : F mod 8 = 0) by (Z.div_mod_to_equations; lia).
    rewrite shadE in FSH, RSF.
    assert (BSF : 2147450880 <= SHF /\ SHF + 32 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (DSF : SHF + 32 <= F \/ F + 256 <= SHF)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold ablk, AIMG_HI, KLS in FB; Z.div_mod_to_equations; lia).
    apply shadow32_c1s in FSH. unfold c1z in FSH.
    pose proof (munch_refl [(lo, SPA + 152); (F, F + 256); (SHF, SHF + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zs. zs. zs. zbr KF.
    zrunb [0x96b8c].
    lazymatch goal with H : rw_cells bsegs _ F _ |- _ => rename H into FF2 end.
    rw_split FF2 3%nat FH FREST. rw_split FREST 1%nat FBLOB FFLAG.
    apply (rw_cells_chop bsegs _ (F + 24) 224 junk [SHB 8; SHB 32; SHB 32; SHB 32; SHB 120]) in FBLOB; [| reflexivity].
    cbn [chop chop1 shape_size] in FBLOB. chop_names FBLOB.
    rw_split FBLOB 1%nat FB8 FREST2. rw_split FREST2 1%nat FCNT FREST3. rw_split FREST3 1%nat FMID FREST4. rw_split FREST4 1%nat FOFF FTAIL.
    lazymatch goal with H : rw_cells bsegs _ SHF _ |- _ => rename H into FSH2 end.
    pose proof FSH2 as FSHK.
    rw_split FSHK 4%nat FS0 FSR. rw_split FSR 4%nat FS4 FSR2. clear FS0 FSR2.
    apply c1z4_sh0 in FS4; [| lia].
    replace (Z.shiftr F 3 + 2147450884) with (Z.shiftr (F + 32) 3 + 2147450880) in FS4 by (rewrite (shr3_off F 32 F8); change (32 / 8) with 4; lia).
    zs.
    callq (asan_memset_callz F (F + 256) RNG).
    all: lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- rw_cells _ _ _ [CB _ _] => exact FCNT
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- rw_cells _ _ _ _ => assumption
         | |- rng_aimg _ => exact RI
         | |- rng _ ?l _ => first [ constr_eq l lo; eapply rng_sub'; [exact RSTK| lia]
                                  | eapply rng_sub'; [exact RF| lia]
                                  | replace (shad (F + 256) - shad F) with 32 by (rewrite !shad_div; Z.div_mod_to_equations; lia); rewrite shadE; exact RSF ]
         | |- wr_at _ _ _ _ => replace (shad (F + 256) - shad F) with 32 by (rewrite !shad_div; Z.div_mod_to_equations; lia); rewrite shadE;
                               destruct FSH2 as [_ WFS]; exact WFS
         | |- app_blk _ _ => eapply ablk_app_blk; [eapply ablk_sub; [exact FB| lia| lia]| lia]
         | |- unpoisoned _ _ _ => eapply (unp_of_sh0 _ (F + 32) 4); [exact FS4| Z.div_mod_to_equations; lia| lia| lia| lia| lia| lia]
         | |- _ => first [ unfold KHIGH, KEND in *; lia | unfold KHIGH, KEND; Z.div_mod_to_equations; lia ]
         end.
    lazymatch goal with H : rw_cells bsegs _ (F + 32) [CB _ _] |- _ => rename H into FCNT2 end.
    lazymatch goal with H : rw_cells bsegs _ (F + 96) [CB _ _] |- _ => rename H into FOFF2 end.
    lazymatch goal with H : rw_cells bsegs _ F _ |- _ => rename H into FH2 end.
    lazymatch goal with H : rw_cells bsegs _ (F + 24) _ |- _ => rename H into FB82 end.
    lazymatch goal with H : rw_cells bsegs _ (F + 128) _ |- _ => rename H into FTAIL2 end.
    lazymatch goal with H : rw_cells bsegs _ (F + 248) _ |- _ => rename H into FFLAG2 end.
    lazymatch goal with H : rw_cells bsegs _ SHF _ |- _ => rename H into FSH3 end.
    lazymatch goal with H : rw_cells bsegs _ SPA _ |- _ => rename H into FRM2 end.
    apply zero32_f16arr in FCNT2.
    destruct (any32_f16arr _ _ _ FOFF2) as [of OFFS].
    rw_join FH2 FB82 FHDR. rw_join FTAIL2 FFLAG2 FTL.
    replace (ret_pc (Z_to_bv 64 617360)) with (Z_to_bv 64 617360) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evtF_done. eexists. do 16 eexists. do 3 eexists. exists of. split; [reflexivity|].
    replace (Z.shiftr F 3 + 2147450912) with (SHF + 32) by lia.
    split; [exact MU|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact FRM2|]. split; [exact FHDR|]. split; [exact FCNT2|]. split; [eassumption|]. split; [exact OFFS|].
    split; [exact FTL| exact FSH3].
  Qed.
End S.
End CANSEC1.
