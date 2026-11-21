(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* [U14B] A2 2026-11-12: draft from G2's U2A twin by tools/g2b_u2.py; G2's reloc tag was *)
(* [U14B-unc2] A2 2026-11-12: carried to unc2's combined image by tools/merge3_u2.sh: ours = my unc text (U1B, built at unc c31)
   moved by tools/t12.py (the measured unc -> unc2 combined image map), base = G's unc ASan twin moved the same
   way, theirs = G2's unc2 ASan twin moved by tools/g2b_u2.py.
   Any comment above or below that names the unc merge describes the unc text this one was carried from. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit I_asan_memset.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2ABlob UwAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BCall U2BGlue U2BIface U2BIfaceS U2BKit_p04.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (D F1 lo SPA : Z) (RNG : footprint).
  Notation SP := (bv_unsigned sp).
  (* 1.4: uncompress (48-byte frame, no fake frame) passes &got = SP + 16 as destLen and &sourceLen = SP + 8 *)
  Notation DL := (SP + 16).
  Variable SL : Z.
  Hypothesis ESL : SL = SP + 8.
  Definition UC_STACK : Z := 192 + 672 + 4096 + 4096 + 4096.
  Hypothesis LOS : lo <= SP - UC_STACK.
  Hypothesis LOC : ATOP + 4096 <= lo.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 48 < KEND.
  Hypothesis ESPA : SPA = SP - 160 - SP mod 32.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Local Ltac acc_hint ::=
    lazymatch goal with
    | |- acc_in _ (Z_to_bv 64 (SPA + _)%Z, _) => solve_acc_with RSTK
    | |- acc_in _ (Z_to_bv 64 SPA, _) => solve_acc_with RSTK
    | |- _ => acc_hint_sh
    end.

  Definition UFRB : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma uspa_props : SP - 176 <= SPA <= SP - 160 /\ SPA mod 32 = 0 /\ (SP + -160) - (SP + -160) mod 2^5 = SPA.
  Proof. rewrite ESPA. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

  Lemma uc_pre : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SP -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m -> u2_img m -> rt_suar m ->
    evtF bsegs RNG (fun ms' => exists m' (jA : list byte),
        ms' = MS (mkR (Z_to_bv 64 0x8ce18) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 192) (Z_to_bv 64 892344)
                     (Z_to_bv 64 1) (Z_to_bv 64 SL) a4 a5 a6 a7
                     s2 (Z_to_bv 64 DL) (Z_to_bv 64 SL) s5 (Z_to_bv 64 D) (Z_to_bv 64 6341696) s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 ASM2) fc None m' (seg_rom bsegs)
        /\ munch [(SP - 176, SP)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SP + -104) UFRB /\ rw_cells bsegs m' SPA [CB 56 jA]
        /\ stk bsegs m' lo SPA /\ stk bsegs m' (SPA + 56) (SP + -104))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 6341696) (Z_to_bv 64 DL) (Z_to_bv 64 D) (Z_to_bv 64 SL) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 A_UNCOMPRESS2) fc None m (seg_rom bsegs)).
  Proof using All.
    intros until m. intros ST MI GOT SHB (GSU & GZC) SUA. unfold rt_suar in SUA.
    unfold A_UNCOMPRESS2, UC_STACK, AGOT_SUAR, ASUAR, ASM2, UFRB in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts.
    pose proof uspa_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 176, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep.
    carve_frame 104%nat ST. carve_frame 56%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_down by lia. rewrite ESPA'.
    release_frame FR1 ST (SP + -104).
    destruct (stk_split bsegs _ lo (SPA + 56) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (SPA + 56) 56 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 56) with 56 in STL, FRA. replace (SPA + 56 - 56) with SPA in STL, FRA by lia.
    zrung [0x8ce14].
    zs.
    apply evtF_done. eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR0|]. split; [exact FRA|]. split; [exact STL| exact STG].
  Qed.

  Variables (Fu FLG : Z).
  Hypothesis FU256 : Fu mod 256 = 0.
  Hypothesis FUB : ablk Fu (Fu + 256).
  Hypothesis RFU : rng RNG Fu 256.
  Hypothesis RSFU : rng RNG (Z.shiftr Fu 3 + 2147450880) 32.
  Hypothesis F1128 : F1 mod 128 = 0.
  Hypothesis F1B : ablk F1 (F1 + 128).
  Hypothesis RDLC : rng RNG DL 8.
  Hypothesis RSDL : rng RNG (Z.shiftr DL 3 + 2147450880) 1.
  Hypothesis RSSL : rng RNG (Z.shiftr SL 3 + 2147450880) 1.
  Hypothesis RSLC : rng RNG SL 8.
  Hypothesis SEPF : F1 + 128 <= Fu \/ Fu + 256 <= F1.

  Definition c1z32 : list cell := Eval cbv in repeat (C1 (Z_to_bv 8 0)) 32.
  (* 1.4 uncompress2_z: the aligned frame holds the fake-frame pointer (+48), the destLen shadow address (+8), destLen
     (+16) and dest (+24); the fake frame header descriptor is 0x1d201; the fake frame holds only the z_stream (shadow
     bytes 4 .. 17), with left redzone f1 x4 and right redzone f3 x6; *destLen is not cleared at this point. *)
  Definition UFRA (j8 j16 : list byte) : list cell :=
    (* [U14B] A2 2026-11-12: the COMBINED 1.4 image keeps the shadow address of sourceLen in slot 16 (0x8cf60 sd a3,16(s1));
       the ASan 1.4 image keeps destLen there (dis/unc2-asan14-both14-r1.txt) *)
    [CB 8 j8; C8 (Z_to_bv 64 (Z.shiftr DL 3 + 2147450880)); C8 (Z_to_bv 64 (Z.shiftr SL 3 + 2147450880)); C8 (Z_to_bv 64 6341696); CB 16 j16; C8 (Z_to_bv 64 Fu)].
  Definition UFHD : list cell := [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 119297); C8 (Z_to_bv 64 576924)].
  Definition UFSH : list cell :=
    [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
     C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603);
     C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Definition uc_hdrW : list (Z * Z) :=
    [(lo, SPA + 56); (Fu, Fu + 256); (Z.shiftr Fu 3 + 2147450880, Z.shiftr Fu 3 + 2147450912)].
  Definition strm_shape : list cshape := [SHB 8; SH8; SH4; SH4; SH8; SH8; SH4; SH4; SH8; SH8; SH8; SH8; SH8; SH8; SH4; SH4; SH8; SH8; SHB 104].

  Lemma uc_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (n0 : Z) (j0 j1 j2 : word) (junk jA : list byte),
    stk bsegs m lo SPA -> mem_inv bsegs m ->
    rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
    rw_cells bsegs m SPA [CB 56 jA] ->
    rw_cells bsegs m Fu [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (256 - 32)) junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad Fu) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    rw_cells bsegs m DL [C8 (Z_to_bv 64 262144)] -> rw_cells bsegs m SL [C8 (Z_to_bv 64 n0)] ->
    shadow_bytes m (Z.shiftr DL 3 + 2147450880) (Z.shiftr DL 3 + 2147450880 + 1) (fun _ => 0) ->
    shadow_bytes m (Z.shiftr SL 3 + 2147450880) (Z.shiftr SL 3 + 2147450880 + 1) (fun _ => 0) ->
    0 <= n0 < 2^32 -> 0 < D < 2^64 ->
    evtF bsegs RNG (fun ms' => exists m' (y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (j8 j16 : list byte)
                                     (p1 ti no ao p2 to msg state dt p3 adler reserved : word),
        ms' = MS (mkR (Z_to_bv 64 0x8cf80) (Z_to_bv 64 SPA) gp tp y5 y6 y7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (Fu + 32)) (Z_to_bv 64 141152) (Z_to_bv 64 112)
                     (* [U14B] A2 2026-11-12: the COMBINED 1.4 image: s3 = destLen, s5 = *destLen (0x8cf78 ld s5,0(s3)); the ASan 1.4
                        image has *destLen in s3 and shadow(sourceLen) in s5 *)
                     y13 y14 y15 y16 y17 (Z_to_bv 64 Fu) (Z_to_bv 64 DL) (Z_to_bv 64 SL) (Z_to_bv 64 262144) (Z_to_bv 64 D) (Z_to_bv 64 (Fu + 32))
                     (Z_to_bv 64 (Z.shiftr Fu 3 + 2147450880)) (Z_to_bv 64 Fu) (Z_to_bv 64 2147450880) (Z_to_bv 64 n0) y28 y29 y30 y31)
                 FR (Z_to_bv 64 A_INFLATEINIT) fc None m' (seg_rom bsegs)
        /\ munch uc_hdrW m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo SPA
        /\ rw_cells bsegs m' SPA (UFRA j8 j16) /\ rw_cells bsegs m' Fu UFHD /\ rw_cells bsegs m' (Fu + 248) [C8 (Z_to_bv 64 FLG)]
        /\ rw_cells bsegs m' (Z.shiftr Fu 3 + 2147450880) UFSH
        /\ rw_cells bsegs m' DL [C8 (Z_to_bv 64 262144)] /\ rw_cells bsegs m' SL [C8 (Z_to_bv 64 n0)]
        /\ rw_cells bsegs m' (Fu + 32) (strm_cells (Z_to_bv 64 D) (Z_to_bv 64 0) ti no ao to msg state (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                                  dt adler reserved p1 p2 p3))
      (MS (mkR (Z_to_bv 64 0x8ce18) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 Fu) x11 x12 x13 x14 x15 x16 x17
               s2 (Z_to_bv 64 DL) (Z_to_bv 64 SL) s5 (Z_to_bv 64 D) (Z_to_bv 64 6341696) s8 s9 (Z_to_bv 64 2147450880) s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8ce18) fc None m (seg_rom bsegs)).
  Proof using All.
    intros until jA. intros ST MI GOT RIC SHB INI LAY REAL FRA FFR FSH DLC SLC SHD SHSL N0 DNZ.
    assert (DEQ : bv_eqb (Z_to_bv 64 D) (Z_to_bv 64 0) = false)
      by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
    unfold UC_STACK, uc_hdrW, UFRA, UFHD, UFSH, A_INFLATEINIT, strm_cells in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof uspa_props as (SPAB & SPA32 & ESPA').
    pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    pose proof (ablk_lin _ _ F1B) as (DB1 & DB2 & DB3 & DB4). unfold AIMG_HI in DB1.
    assert (F8 : Fu mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    rw_split FFR 3%nat FHD FREST. rw_split FREST 1%nat FBLOB FFLG.
    pose proof (conj GOT (conj RIC (conj SHB (conj INI (conj LAY REAL))))) as RTB. clear GOT RIC SHB INI LAY REAL.
    rewrite shadE in FSH.
    eapply (rw_cells_recast bsegs _ _ _ c1z32) in FSH; [| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity].
    unfold c1z32 in FSH.
    assert (BSF : 2147450880 <= Z.shiftr Fu 3 + 2147450880 /\ Z.shiftr Fu 3 + 2147450880 + 32 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (BSD : 2147450880 <= Z.shiftr DL 3 + 2147450880 /\ Z.shiftr DL 3 + 2147450880 + 1 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (BSL : 2147450880 <= Z.shiftr SL 3 + 2147450880 /\ Z.shiftr SL 3 + 2147450880 + 1 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    pose (W := [(lo, SPA + 56); (Fu, Fu + 256); (Z.shiftr Fu 3 + 2147450880, Z.shiftr Fu 3 + 2147450912)]).
    assert (DJD : disjoint_from W (Z.shiftr DL 3 + 2147450880) (Z.shiftr DL 3 + 2147450880 + 1 - (Z.shiftr DL 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, F1B. Z.div_mod_to_equations. lia. }
    assert (DJL : disjoint_from W (Z.shiftr SL 3 + 2147450880) (Z.shiftr SL 3 + 2147450880 + 1 - (Z.shiftr SL 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB, F1B. Z.div_mod_to_equations. lia. }
    band_ind FUB bU. band_ind F1B b1.
    destruct (sepI F1 128 Fu 256 SEPF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (cF & CF0 & CF1 & CF2).
    clear SEPF.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM. subst W.
    zrung [0x8cf50].
    (* 1.4: the (sourceLen != 0 && source == NULL) test at 0x8cf54: source = D > 0 *)
    assert (C0 : negb (bv_eqb (Z_to_bv 64 (Z.land 0 (Z.b2z (0 <? n0)))) (Z_to_bv 64 0)) = false).
    { rewrite Z.land_0_l. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. }
    rewrite ?C0. cbv iota. clear C0 DEQ.
    zrung [0x8cf50].
    apply (rw_cells_chop bsegs _ _ _ junk strm_shape) in FBLOB; [| vm_compute; reflexivity].
    cbn [chop chop1 shape_size strm_shape] in FBLOB. chop_names FBLOB.
    rw_split FBLOB 1%nat FPAD FSTRM0. rw_split FSTRM0 17%nat FSTRM FTAIL.
    replace (Fu + 24 + 8) with (Fu + 32) in * by lia. clear FPAD FTAIL.
    zrung [0x8cf68].
    destruct RTB as (GOT & RIC & SHB & INI & LAY & REAL).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (TRT : forall Ax csx, rw_cells bsegs m Ax csx -> 0x10000 <= Ax -> Ax + Z.of_nat (cells_size csx) <= 0x67f000 -> rw_cells bsegs mc Ax csx)
        by (intros Ax csx HCx H1x H2x; eapply rw_cells_transport; [exact HCx| exact MU| exact WM|]; cbn [disjoint_from]; lia) end.
    apply TRT in GOT; [| lia| cbn [cells_size csize Nat.add]; lia]. apply TRT in RIC; [| lia| cbn [cells_size csize Nat.add]; lia].
    apply TRT in SHB; [| lia| cbn [cells_size csize Nat.add]; lia]. apply TRT in INI; [| lia| cbn [cells_size csize Nat.add]; lia].
    apply TRT in LAY; [| lia| cbn [cells_size csize Nat.add]; lia]. apply TRT in REAL; [| lia| cbn [cells_size csize Nat.add]; lia].
    clear TRT.
    assert (ESZ : Z.shiftr (Fu + 32) 3 + 2147450880 = Z.shiftr Fu 3 + 2147450880 + 4)
      by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (SHZ : shadow_bytes mc (Z.shiftr (Fu + 32) 3 + 2147450880) (Z.shiftr (Fu + 32) 3 + 2147450880 + 14) (fun _ => 0)) end.
    { pose proof FSH as FS'. rw_split FS' 4%nat FSa FSr. rw_split FSr 14%nat FSz FSt.
      eapply (rw_cells_recast bsegs _ _ _ [CB (Z.to_nat 14) (repeat (Z_to_bv 8 0) (Z.to_nat 14))]) in FSz; [| cbn; split; [reflexivity| exact I]| vm_compute; reflexivity| reflexivity].
      rewrite ESZ. replace (Z.shiftr Fu 3 + 2147450880 + 4) with (Z.shiftr Fu 3 + 2147450884) by lia.
      apply (shadow_bytes_of_rw_cells_repeat bsegs _ _ 14 0 FSz); [lia|]. apply no_image_asan. lia. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => assert (WSF : wr_at bsegs mc (shad Fu) 32) end.
    { rewrite shadE. eapply rw_cells_wr_at; [exact FSH|]. cbn [cells_size csize]. lia. }
    rw_split FSTRM 10%nat STRM1 STRM2. rw_split STRM2 3%nat STRMM STRM3.
    apply rw_cells_forget in STRMM. destruct STRMM as [jm STRMM]. cbn [cells_size csize Nat.add] in STRMM.
    replace (Fu + 32 + 64) with (Fu + 96) in * by lia.
    zs.
    callq (asan_memset_callz Fu (Fu + 256) RNG).
    all: lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- rw_cells _ _ _ [CB _ _] => exact STRMM
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => eassumption
         | |- rw_cells _ _ _ _ => assumption
         | |- rng_aimg _ => exact RI
         | |- rng _ ?l _ => first [ constr_eq l lo; eapply rng_sub'; [exact RSTK| lia]
                                  | eapply rng_sub'; [exact RFU| lia]
                                  | replace (shad (Fu + 256) - shad Fu) with 32 by (rewrite !shad_div; Z.div_mod_to_equations; lia); rewrite shadE; exact RSFU ]
         | |- wr_at _ _ _ _ => replace (shad (Fu + 256) - shad Fu) with 32 by (rewrite !shad_div; Z.div_mod_to_equations; lia); exact WSF
         | |- app_blk _ _ => eapply ablk_app_blk; [eapply ablk_sub; [exact FUB| lia| lia]| lia]
         | |- unpoisoned _ _ _ => eapply (unp_of_sh0 _ (Fu + 32) 14); [exact SHZ| Z.div_mod_to_equations; lia| lia| lia| lia| lia| lia]
         | |- _ => first [ unfold KHIGH, KEND in *; lia | unfold KHIGH, KEND; Z.div_mod_to_equations; lia ]
         end.
    lazymatch goal with H : rw_cells bsegs _ (Fu + 96) [CB _ _] |- _ => rename H into STRMM end.
    eapply (rw_cells_recast bsegs _ _ _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in STRMM; [| cbn; tauto| reflexivity| reflexivity].
    rw_join STRMM STRM3 STRM2'. rw_join STRM1 STRM2' STRM. cbn [app] in STRM.
    zrung [0x8cf7c].
    zs.
    apply evtF_done. do 13 eexists. do 14 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [exact FRA|]. split; [exact FHD|]. split; [exact FFLG|]. split; [exact FSH|]. split; [exact DLC|]. split; [exact SLC| exact STRM].
  Qed.
End S.
End CANSEC1.
