(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* [U14B-unc2] A2 2026-11-12: carried to unc2's combined image by tools/merge3_u2.sh: ours = my unc text (U1B, built at unc c31)
   moved by tools/t12.py (the measured unc -> unc2 combined image map), base = G's unc ASan twin moved the same
   way, theirs = G2's unc2 ASan twin moved by tools/g2b_u2.py.
   Any comment above or below that names the unc merge describes the unc text this one was carried from. *)
(* [U14B] A2 2026-11-12: the 1.4 uncompress chain.  This text is a 3-way merge (tools/merge3.sh run hw1): the view's
   text, the 1.3.1 ASan twin as base, and G's 1.4 ASan twin U1A/HarnA_walk moved to the combined image by tools/g2b.py (the harness code sits at a constant
   +0x88, the uncompress wrapper maps in five runs); all 7 conflicts take G's side. *)
(* [U14B-unc3] A1 2026-11-12: carried to unc3's combined image by tools/merge3_u3.sh: ours = A2's unc2 text (a2/frozen/unc2-both-c7 U2B, built at unc2 c7) moved by tools/t23.py (the measured unc2 -> unc3 combined image map), base = unc2 ASan twin moved by tools/g2b_e.py u2 and t23, theirs = unc3 ASan twin moved by tools/g2b_e.py u3; conflicts resolved by hand (marked [U14B-unc3]). A comment that names the unc or unc2 merge describes the text this one was carried from. *)
(*: HarnB_walk for unc2 at 1.4.  h_pre and the fake-frame header
   part of h_hdr are unc2's own (the harness code did not change from 1.3.1: frame 96 with ra, s0 .. s7; ASan class-1
   fake frame of 128 bytes with destLen at F1 + 32 and sourceLen at F1 + 64).  At 1.4 the call at 0x8ccf4 enters the
   uncompress2 wrapper (0x8d370), which calls uncompress2_z (A_UNCOMPRESS2 = 0x8cec0) with ra = 0x8d3f0, as unc C46 walks unc's uncompress wrapper.  unc2's wrapper: frame 64 (ra, s0 .. s3 at sp+56 .. sp+24), s0 = destLen,
   s1 = sourceLen, s2 / s3 = their shadow bytes (both checked), the copies at sp+16 (destLen) and sp+8 (sourceLen);
   after the call it stores both copies back. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Arr Bytes ZBridge Tac InitMem SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AShadow U2AKit U2AObj U2ABlob UwAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj U2BClient U2BCall U2BGlue U2BIface U2BIfaceS U2cB_pre U2cB_epi U2BKit_p04.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import RunDraw StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import InfPure InfPure_w7 InfAGlue.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import InfBBase InfBKit InfB_w7base InfB_w7tab InfB_w7pull.

Definition u3_front (payload : list Z) : Z * Z * Z * Z :=
  match payload with
  | [] => (0, 8, 1, 1)
  | [b0] => (1, b0, 1, 1)
  | [b0; m0] => (2, b0, m0, 1)
  | b0 :: m0 :: m1 :: _ => (3, b0, m0, m1)
  end.
Lemma u3_front_range : forall payload k b0 m0 m1, Forall (fun c => 0 <= c < 256) payload -> u3_front payload = (k, b0, m0, m1) ->
  0 <= k <= 3 /\ k <= Z.of_nat (length payload) /\ 0 <= b0 < 256 /\ 0 <= m0 < 256 /\ 0 <= m1 < 256.
Proof.
  intros payload k b0 m0 m1 PR E. destruct payload as [|c0 [|c1 [|c2 r]]]; cbn in E; inversion E; subst; clear E.
  - cbn. lia.
  - inversion PR; subst. cbn [length]. lia.
  - inversion PR as [|? ? P0 PR1]; subst. inversion PR1; subst. cbn [length]. lia.
  - inversion PR as [|? ? P0 PR1]; subst. inversion PR1 as [|? ? P1 PR2]; subst. inversion PR2; subst. cbn [length]. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section F.
  Variables (RNG : footprint).
  Lemma h_front : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 m : amem)
      (W : list (Z * Z)) (D n : Z) (payload : list Z),
    bytes_at bsegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = n ->
    unpoisoned m0 D (D + n) -> munch W m0 m -> disjoint_from W (shad D) (shad (D + n - 1) + 1 - shad D) ->
    rng RNG D n -> rng RNG (Z.shiftr D 3 + 2147450880) (n / 8 + 1) ->
    D mod 16 = 0 -> 1 <= D -> D + n <= ATOP -> 0 <= n < 67108864 ->
    evtF bsegs RNG (fun ms' => exists (k b0 m0' m1 : Z) (y10 y11 y13 : word),
        u3_front payload = (k, b0, m0', m1) /\
        ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 (Z_to_bv 64 b0) y13 (Z_to_bv 64 m0') (Z_to_bv 64 m1) x16 x17 x18
                      (Z_to_bv 64 (D + k)) (Z_to_bv 64 (n - k)) x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26 x27 x28 x29 x30 x31)
                 FR (Z_to_bv 64 0x8cc84) fc None m (seg_rom bsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
               (Z_to_bv 64 D) (Z_to_bv 64 n) x21 x22 (Z_to_bv 64 2147450880) x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8cc40) fc None m (seg_rom bsegs)).
  Proof.
    intros until payload. intros PAYB PAYR PLEN UNP MU DJP RD RSD D16 D1 DTOP NR.
    atop_facts.
    zs. zbr KN.
    -
      assert (EP : payload = []) by (destruct payload; [reflexivity| cbn [length] in PLEN; lia]).
      zs. zs. zs.
      apply evtF_done. exists 0, 8, 1, 1. do 3 eexists. split; [rewrite EP; reflexivity|].
      replace (D + 0) with D by lia. replace (n - 0) with n by lia. reflexivity.
    -
      destruct (pull_facts RNG W m0 m D n payload 0 UNP MU DJP RD RSD PAYB PAYR PLEN D16 D1 ltac:(lia)) as (b & RDB & CK & ACP & RDP & ACB & BZR).
      replace (D + 0) with D in * by lia.
      (* [U14B-unc3] A1 2026-11-12: h_front's proof body is the view's own combined text (the 1.3.1 combined walk, moved; old
         text aside/U3B/HarnB_walk.v.u2 l.61-106): the combined harness front has UBSan pointer checks before each byte
         load (0x8cc7c, 0x8cdc8, 0x8ce04; a1/dis/harn3-asan14-both14-r1.txt l.363, 447, 462) that ASan walk
         does not have. The statement is the same in both texts. *)
      zrung [0x8cc58].
      zs. rewrite sxb_sval.
      ck_branchJ 12 0x8cc60 CK.
      zs. cbv beta. rewrite (bz_val payload 0 PAYR).
      zs. zs. zbr K1.
      +
        destruct (pull_facts RNG W m0 m D n payload 1 UNP MU DJP RD RSD PAYB PAYR PLEN D16 D1 ltac:(lia)) as (b1 & RDB1 & CK1 & ACP1 & RDP1 & ACB1 & BZR1).
        zrung [0x8cda4].
        zs. rewrite sxb_sval.
        ck_branchJ 13 0x8cdac CK1.
        zs. cbv beta. rewrite (bz_val payload 1 PAYR).
        zs. zs. zs. zbr K2.
        *
          destruct (pull_facts RNG W m0 m D n payload 2 UNP MU DJP RD RSD PAYB PAYR PLEN D16 D1 ltac:(lia)) as (b2 & RDB2 & CK2 & ACP2 & RDP2 & ACB2 & BZR2).
          zrung [0x8cddc].
          zs. rewrite sxb_sval.
          ck_branchJ 13 0x8cde4 CK2.
          zs. cbv beta. rewrite (bz_val payload 2 PAYR).
          zs. zs. zs.
          apply evtF_done. exists 3, (bz payload 0), (bz payload 1), (bz payload 2). do 3 eexists.
          split; [destruct payload as [|c0 [|c1 [|c2 r]]]; cbn [length] in PLEN; try lia; reflexivity|].
          replace (n + -3) with (n - 3) by lia. reflexivity.
        *
          zs. zs. zs. zs.
          apply evtF_done. exists 2, (bz payload 0), (bz payload 1), 1. do 3 eexists.
          split; [destruct payload as [|c0 [|c1 [|c2 r]]]; cbn [length] in PLEN; try lia; reflexivity|].
          replace (n - 2) with 0 by lia. reflexivity.
      +
        zs. zs. zs. zs.
        apply evtF_done. exists 1, (bz payload 0), 1, 1. do 3 eexists.
        split; [destruct payload as [|c0 [|c1 r]]; cbn [length] in PLEN; try lia; reflexivity|].
        replace (n - 1) with 0 by lia. reflexivity.
  Qed.
End F.
End CANSEC1.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (D n lo SPA : Z) (RNG : footprint).
  Notation SP := (bv_unsigned sp).
  (* 1.4: the uncompress2 wrapper's 64-byte frame lies below the harness's *)
  Definition H_STACK : Z := 128 + 64 + UC_STACK.
  Hypothesis LOS : lo <= SP - H_STACK.
  Hypothesis LOC : ATOP + 4096 <= lo.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis ESPA : SPA = SP - 96 - SP mod 32.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Local Ltac acc_hint ::=
    lazymatch goal with
    | |- acc_in _ (Z_to_bv 64 (SPA + _)%Z, _) => solve_acc_with RSTK
    | |- acc_in _ (Z_to_bv 64 SPA, _) => solve_acc_with RSTK
    | |- _ => acc_hint_sh
    end.

  Definition HFRB : list cell := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma hspa_props : SP - 112 <= SPA <= SP - 96 /\ SPA mod 32 = 0 /\ (SP + -96) - (SP + -96) mod 2^5 = SPA.
  Proof. rewrite ESPA. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.
  Lemma h_pre : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SP -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m -> u2_img m -> rt_suar m ->
    evtF bsegs RNG (fun ms' => exists m' (jA : list byte),
        ms' = MS (mkR (Z_to_bv 64 0x8cba0) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 96) (Z_to_bv 64 892600)
                     (Z_to_bv 64 1) a3 a4 a5 a6 a7
                     s2 (Z_to_bv 64 D) (Z_to_bv 64 n) s5 s6 (Z_to_bv 64 2147450880) s8 s9 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 ASM1) fc None m' (seg_rom bsegs)
        /\ munch [(SP - 112, SP)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SP + -72) HFRB /\ rw_cells bsegs m' SPA [CB 24 jA]
        /\ stk bsegs m' lo SPA /\ stk bsegs m' (SPA + 24) (SP + -72))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 A_HARNESS) fc None m (seg_rom bsegs)).
  Proof using All.
    intros until m. intros ST MI GOT SHB (GSU & GZC) SUA. unfold rt_suar in SUA.
    unfold A_HARNESS, H_STACK, UC_STACK, AGOT_SUAR, ASUAR, ASM1, HFRB in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts.
    pose proof hspa_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 112, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep. (* add sp,sp,-96 *)
    carve_frame 72%nat ST. carve_frame 24%nat ST.
    zstep. (* sd zero,0(sp) *)
    do 9 zstep. (* sd ra, s0 .. s7 *)
    zstep. (* add s0,sp,96 *)
    zstep. (* and sp,sp,-32 *)
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_down by lia. rewrite ESPA'.
    release_frame FR1 ST (SP + -72).
    destruct (stk_split bsegs _ lo (SPA + 24) (SP + -72) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (SPA + 24) 24 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 24) with 24 in STL, FRA. replace (SPA + 24 - 24) with SPA in STL, FRA by lia.
    zrung [0x8cb9c].
    zs. (* jal __asan_stack_malloc_1 *)
    apply evtF_done. eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR0|]. split; [exact FRA|]. split; [exact STL| exact STG].
  Qed.

  Variables (F1 FLG : Z).
  Hypothesis F1128 : F1 mod 128 = 0.
  Hypothesis F1B : ablk F1 (F1 + 128).
  Hypothesis RF1 : rng RNG F1 128.
  Hypothesis RSF1 : rng RNG (Z.shiftr F1 3 + 2147450880) 16.

  Definition c1z16 : list cell := Eval cbv in repeat (C1 (Z_to_bv 8 0)) 16.
  Definition HFRA (j16 : list byte) : list cell := [CB 16 j16; C8 (Z_to_bv 64 F1)].
  Definition HFHD : list cell := [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 123597); C8 (Z_to_bv 64 576316)].
  Definition HFSH : list cell :=
    [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  (* 1.4: the wrapper's frame at SPA - 64 when it calls uncompress2_z: sp+0 not written, the sourceLen copy, the
     destLen copy, then the saved s3, s2 = F1, s1 = SPA, s0 = sp and ra = 0x8ccf8.  unc3: the harness passes
     source D + k and sourceLen n - k (s3 / s4), and destLen dl from the input prefix *)
  Definition WFR (j8 : list byte) (k dl : Z) : list cell :=
    [CB 8 j8; C8 (Z_to_bv 64 (n - k)); C8 (Z_to_bv 64 dl); C8 (Z_to_bv 64 (D + k)); C8 (Z_to_bv 64 F1); C8 (Z_to_bv 64 SPA); C8 sp;
     C8 (Z_to_bv 64 0x8ccc0)].
  Definition h_hdrW : list (Z * Z) := [(SPA - 64, SPA + 24); (F1, F1 + 128); (Z.shiftr F1 3 + 2147450880, Z.shiftr F1 3 + 2147450896)].
  Definition hfr_shape : list cshape := [SHB 8; SH8; SHB 24; SH8; SHB 48].

  (* 1.4: from the stack_malloc_1 return (0x8cbd8) through the fake-frame header, the call of the uncompress2 wrapper
     (0x8ccf4 -> 0x8d370), its prologue and both shadow checks, to uncompress2_z's entry (A_UNCOMPRESS2) with
     ra = 0x8d3f0, a1 = &(destLen copy) (sp + 16), a3 = &(sourceLen copy) (sp + 8), s0 / s1 = destLen / sourceLen
     (F1 + 32 / F1 + 64), s2 / s3 = their shadow bytes *)
  Lemma h_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (j0 j1 j2 : word) (junk jA : list byte) (payload : list Z),
    stk bsegs m lo SPA -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m ->
    rw_cells bsegs m SPA [CB 24 jA] ->
    rw_cells bsegs m F1 [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (128 - 32)) junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad F1) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    0 <= n < 67108864 ->
    bytes_at bsegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = n ->
    unpoisoned m D (D + n) -> rng RNG D n -> rng RNG (Z.shiftr D 3 + 2147450880) (n / 8 + 1) ->
    D mod 16 = 0 -> 1 <= D -> D + n <= ATOP ->
    disjoint_from h_hdrW D n -> disjoint_from h_hdrW (shad D) (shad (D + n - 1) + 1 - shad D) ->
    evtF bsegs RNG (fun ms' => exists m' (y5 y6 y7 y14 y15 : word) (j16 j8 : list byte) (k b0 mu0 mu1 : Z),
        u3_front payload = (k, b0, mu0, mu1) /\
        ms' = MS (mkR (Z_to_bv 64 0x8d3b8) (Z_to_bv 64 (SPA + -64)) gp tp y5 y6 y7 (Z_to_bv 64 (F1 + 32)) (Z_to_bv 64 (F1 + 64))
                     (Z_to_bv 64 6341952) (Z_to_bv 64 (SPA + -48)) (Z_to_bv 64 (D + k)) (Z_to_bv 64 (SPA + -56)) y14 y15 x16 x17
                     (Z_to_bv 64 (Z.shiftr F1 3 + 2147450880 + 4)) (Z_to_bv 64 (Z.shiftr F1 3 + 2147450880 + 8)) (Z_to_bv 64 (n - k))
                     (Z_to_bv 64 (Z.shiftr F1 3 + 2147450880)) (Z_to_bv 64 F1) (Z_to_bv 64 2147450880)
                     s8 s9 s10 s11 x28 x29 x30 x31)
                 FR (Z_to_bv 64 A_UNCOMPRESS2) fc None m' (seg_rom bsegs)
        /\ munch h_hdrW m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (SPA + -64)
        /\ rw_cells bsegs m' (SPA + -64) (WFR j8 k (Z.min (b0 * mu0 * mu1) 262144))
        /\ rw_cells bsegs m' SPA (HFRA j16) /\ rw_cells bsegs m' F1 HFHD /\ rw_cells bsegs m' (F1 + 120) [C8 (Z_to_bv 64 FLG)]
        /\ rw_cells bsegs m' (Z.shiftr F1 3 + 2147450880) HFSH
        /\ rw_cells bsegs m' (F1 + 32) [C8 (Z_to_bv 64 (Z.min (b0 * mu0 * mu1) 262144))] /\ rw_cells bsegs m' (F1 + 64) [C8 (Z_to_bv 64 (n - k))])
      (MS (mkR (Z_to_bv 64 0x8cba0) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 F1) x11 x12 x13 x14 x15 x16 x17
               s2 (Z_to_bv 64 D) (Z_to_bv 64 n) s5 s6 (Z_to_bv 64 2147450880) s8 s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8cba0) fc None m (seg_rom bsegs)).
  Proof using All.
    intros until payload. intros ST MI GOT SHB FRA FFR FSH N0 PAYB PAYR PLEN UNP RD RSD D16 D1 DTOP DJB DJP.
    unfold H_STACK, UC_STACK, h_hdrW, HFRA, HFHD, HFSH, WFR, A_UNCOMPRESS2 in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof hspa_props as (SPAB & SPA32 & ESPA').
    pose proof (ablk_lin _ _ F1B) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    assert (F8 : F1 mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    rw_split FFR 3%nat FHD FREST. rw_split FREST 1%nat FBLOB FFLG.
    rewrite shadE in FSH.
    eapply (rw_cells_recast bsegs _ _ _ c1z16) in FSH; [| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity].
    unfold c1z16 in FSH.
    assert (BSF : 2147450880 <= Z.shiftr F1 3 + 2147450880 /\ Z.shiftr F1 3 + 2147450880 + 16 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    band_ind F1B bU.
    pose (W := [(SPA - 64, SPA + 24); (F1, F1 + 128); (Z.shiftr F1 3 + 2147450880, Z.shiftr F1 3 + 2147450896)]).
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM. subst W.
    apply (rw_cells_chop bsegs _ _ _ junk hfr_shape) in FBLOB; [| vm_compute; reflexivity].
    cbn [chop chop1 shape_size hfr_shape] in FBLOB. chop_names FBLOB.
    rw_split FBLOB 1%nat FPAD FR1'. rw_split FR1' 1%nat FDL FR2'. rw_split FR2' 1%nat FMID FR3'. rw_split FR3' 1%nat FSL FTAIL.
    pose proof PAYB as PAYB0. lazymatch type of PAYB0 with ?T => change T with (bxu T) in PAYB0 end. clear PAYB.
    lazymatch type of UNP with ?T => change T with (bxu T) in UNP end.
    lazymatch type of DJB with ?T => change T with (bxu T) in DJB end. lazymatch type of DJP with ?T => change T with (bxu T) in DJP end.
    zrung [0x8cc40].
    unfold bxu in PAYB0, UNP, DJB, DJP.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => set (mc := mx) in * end.
    assert (PAYBc : bytes_at bsegs mc D (map (Z_to_bv 8) payload)) by (eapply bytes_at_transport; [exact PAYB0| exact MU| rewrite length_map, PLEN; exact DJB]).
    eapply evtF_cut; [eapply (h_front RNG) with (m0 := m) (W := [(SPA - 64, SPA + 24); (F1, F1 + 128); (Z.shiftr F1 3 + 2147450880, Z.shiftr F1 3 + 2147450896)]) (payload := payload);
      [exact PAYBc| exact PAYR| exact PLEN| exact UNP| exact MU| exact DJP| exact RD| exact RSD| exact D16| exact D1| exact DTOP| exact N0]|].
    cbv beta. intros ms1 (k & b0 & mu0 & mu1 & y10 & y11 & y13 & EFR & ->).
    destruct (u3_front_range _ _ _ _ _ PAYR EFR) as (K3 & KL & B0R & M0R & M1R).
    zrung [0x8cc9c].
    assert (P2 : 0 <= b0 * mu0 <= 65025) by nia.
    rewrite (Z.mod_small (b0 * mu0)) by lia.
    assert (P3 : 0 <= b0 * mu0 * mu1 <= 16581375) by nia.
    remember (b0 * mu0 * mu1) as LL eqn:ELL.
    (* the destLen / sourceLen shadow bytes the 1.4 wrapper checks: SHF + 4 / SHF + 8 *)
    assert (ESD : Z.shiftr (F1 + 32) 3 + 2147450880 = Z.shiftr F1 3 + 2147450880 + 4)
      by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (ESS : Z.shiftr (F1 + 64) 3 + 2147450880 = Z.shiftr F1 3 + 2147450880 + 8)
      by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    (* [U14B-unc3] A1 2026-11-12: the combined 1.4 wrapper checks the alignment of destLen (0x8d390 and a1,a1,7; 0x8d394 bnez)
       and of sourceLen (0x8d3c4 / 0x8d3c8) before it loads them. In this
       context (after the h_front cut) zrung left the first branch open (c7: "pc is not a literal" at the last zs), so the
       two facts are stated and rewritten by hand below. *)
    assert (EA32 : (F1 + 32) mod 8 = 0) by (clear - F8; Z.div_mod_to_equations; lia).
    assert (EA64 : (F1 + 64) mod 8 = 0) by (clear - F8; Z.div_mod_to_equations; lia).
    zs. zbr KC.
    -
      zrung [0x8ccbc].
      zs. (* jal uncompress2 (0x8d370), ra = 0x8ccf8 *)
      zstep. (* 1.4: add sp,sp,-64 *)
      carve_frame 64%nat ST.
      zrung [0x8d374]. rewrite ?EA32. zrung [0x8d374].
      try rewrite ESD.
      zrung [0x8d39c]. rewrite ?EA64. zrung [0x8d39c].
      try rewrite ESS.
      zrung [0x8d3b4].
      zs. (* jal uncompress2_z (0x8cec0), ra = 0x8d3f0 *)
      apply evtF_done. do 8 eexists. exists k, b0, mu0, mu1. split; [exact EFR|]. split; [reflexivity|].
      rewrite <- ELL. rewrite Z.min_l by lia.
      split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|].
      split; [exact FRA|]. split; [exact FHD|]. split; [exact FFLG|]. split; [exact FSH|]. split; [exact FDL| exact FSL].
    -
      zrung [0x8ccbc].
      zs. (* jal uncompress2 (0x8d370), ra = 0x8ccf8 *)
      zstep. (* 1.4: add sp,sp,-64 *)
      carve_frame 64%nat ST.
      zrung [0x8d374]. rewrite ?EA32. zrung [0x8d374].
      try rewrite ESD.
      zrung [0x8d39c]. rewrite ?EA64. zrung [0x8d39c].
      try rewrite ESS.
      zrung [0x8d3b4].
      zs. (* jal uncompress2_z (0x8cec0), ra = 0x8d3f0 *)
      apply evtF_done. do 8 eexists. exists k, b0, mu0, mu1. split; [exact EFR|]. split; [reflexivity|].
      rewrite <- ELL. rewrite Z.min_r by lia.
      split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|].
      split; [exact FRA|]. split; [exact FHD|]. split; [exact FFLG|]. split; [exact FSH|]. split; [exact FDL| exact FSL].
  Qed.

  Hypothesis RFRM : rng RNG (SPA - 64) 88.
  Hypothesis GB : ablk FLG (FLG + 1).
  Hypothesis GF : FLG + 1 <= F1 \/ F1 + 128 <= FLG.
  Hypothesis RG : rng RNG FLG 1.
  Notation SHF := (Z.shiftr F1 3 + 2147450880).

  (* 1.4: from uncompress2_z's return into the wrapper (0x8d3f0): the sourceLen shadow check, *sourceLen = its copy,
     the destLen shadow check, *destLen = its copy, the 64-byte frame's restore and ret to 0x8ccf8, then the harness
     epilogue as before *)
  Lemma h_epi : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 v4 x28 x29 x30 x31 slv dlv dv sv w3 : word) m (j16 j8 : list byte),
    stk bsegs m lo (SPA + -64) -> stk bsegs m (SPA + 24) (SP + -72) -> mem_inv bsegs m ->
    rw_cells bsegs m (SPA + -64) [CB 8 j8; C8 slv; C8 dlv; C8 w3; C8 (Z_to_bv 64 F1); C8 (Z_to_bv 64 SPA); C8 sp;
                                  C8 (Z_to_bv 64 0x8ccc0)] ->
    rw_cells bsegs m SPA (HFRA j16) ->
    rw_cells bsegs m (SP + -72) HFRB ->
    rw_cells bsegs m F1 HFHD ->
    rw_cells bsegs m (F1 + 32) [C8 dv] ->
    rw_cells bsegs m (F1 + 64) [C8 sv] ->
    rw_cells bsegs m (F1 + 120) [C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m SHF HFSH ->
    evtF bsegs RNG (fun ms' => exists (mp m' : amem) (q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
        ms' = MS (mkR ra sp gp tp q5 q6 q7 s0 s1 (Z_to_bv 64 0) q11 q12 q13 q14 q15 q16 q17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                 FR (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ munch [(SHF, SHF + 16); (F1, F1 + 72)] m mp /\ wmono bsegs m mp /\ mem_inv bsegs mp
        /\ munch [(FLG, FLG + 1)] mp m' /\ wmono bsegs mp m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SP /\ rw_cells bsegs m' FLG [C1 (Z_to_bv 8 0)])
      (MS (mkR x1 (Z_to_bv 64 (SPA + -64)) gp tp x5 x6 x7 (Z_to_bv 64 (F1 + 32)) (Z_to_bv 64 (F1 + 64)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 (SHF + 8)) v4 (Z_to_bv 64 SHF) (Z_to_bv 64 F1) (Z_to_bv 64 2147450880)
               s8 s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8d3b8) fc None m (seg_rom bsegs)).
  Proof using All.
    intros until j8. intros STL STG MI WF FRA FRB FH FDL FSL FFL FLC FSH.
    unfold HFRA, HFRB, HFHD, HFSH, H_STACK, UC_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof (ablk_lin _ _ F1B) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    pose proof (ablk_lin _ _ GB) as (GB1 & GB2 & GB3 & GB4). unfold AIMG_HI in GB1.
    pose proof hspa_props as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    assert (F8 : F1 mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (BSF : 2147450880 <= SHF /\ SHF + 16 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    band_ind F1B bU. band_ind GB bG.
    destruct (sepI FLG 1 F1 128 GF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (cG & CG0 & CG1 & CG2). clear GF.
    pose proof (munch_refl [(SHF, SHF + 16); (F1, F1 + 72)] m) as MU1. pose proof (wmono_refl bsegs m) as WM1.
    zrung [0x8cd20].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv bsegs mx |- _ => pose proof MIx as MIp; change (mem_inv bsegs mx) with (bxu (mem_inv bsegs mx)) in MIp end end.
    lazymatch type of MU1 with ?T => change T with (bxu T) in MU1 end.
    lazymatch type of WM1 with ?T => change T with (bxu T) in WM1 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(FLG, FLG + 1)] mx) as MU2; pose proof (wmono_refl bsegs mx) as WM2 end.
    zs. (* ld a0,120(s2) *)
    zs. (* sb zero,0(a0) *)
    zs. zs. zs. (* j; li a0,0; add sp,s0,-96 *)
    do 9 zs. zs. zs.
    (* the frames: the wrapper's (SPA - 64), the harness's aligned area (SPA), its register save (SP - 72) *)
    lazymatch goal with H : rw_cells bsegs _ (SPA + -64) _ |- _ => rename H into WF2 end.
    lazymatch goal with H : rw_cells bsegs _ SPA _ |- _ => rename H into FRA2 end.
    lazymatch goal with H : rw_cells bsegs _ (SP + -72) _ |- _ => rename H into FRB2 end.
    lazymatch goal with H : stk bsegs _ lo (SPA + -64) |- _ => rename H into STL2 end.
    lazymatch goal with H : stk bsegs _ (SPA + 24) (SP + -72) |- _ => rename H into STG2 end.
    eapply stk_release in WF2; [| exact STL2| lia]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in WF2.
    replace (SPA + -64 + Z.of_nat 64) with SPA in WF2 by (change (Z.of_nat 64) with 64; lia).
    eapply stk_release in FRA2; [| exact WF2| lia]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRA2.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (stk_merge bsegs mx lo (SPA + 24) (SP + -72) FRA2 STG2 ltac:(lia)) as ST2 end.
    release_frame FRB2 ST2 (bv_unsigned sp).
    apply evtF_done. unfold bxu in MU1, WM1, MIp.
    replace (Z.shiftr F1 3 + 2147450896) with (SHF + 16) by lia.
    eexists _, _. do 14 eexists. split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MIp|].
    split; [exact MU2|]. split; [exact WM2|]. split; [eassumption|]. split; [exact ST2| eassumption].
  Qed.
End S.
End CANSEC1.
