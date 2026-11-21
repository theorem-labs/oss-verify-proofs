(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* [U14B-unc2] A2 2026-11-12: carried to unc2's combined image by tools/merge3_u2.sh: ours = my unc text (U1B, built at unc c31)
   moved by tools/t12.py (the measured unc -> unc2 combined image map), base = G's unc ASan twin moved the same
   way, theirs = G2's unc2 ASan twin moved by tools/g2b_u2.py.
   Any comment above or below that names the unc merge describes the unc text this one was carried from. *)
(* [U14B] A2 2026-11-12: the 1.4 uncompress chain.  This text is a 3-way merge (tools/merge3.sh run loop1): the view's
   text (1.3.1 combined), the 1.3.1 ASan twin as base, and G's 1.4 ASan twin U1A/U2cA_loop moved to the combined image by tools/g2b.py; all 16 conflicts take G's side (tools/resolve.py), then the
   combined image's registers by hand (marked [U14B]): s3 = destLen, s5 = left, the return code in s6, and frame slot
   16 = shadow(sourceLen).  The comment below is G's and names the ASan registers. *)
(* The 1.4 uncompress2_z loop (0x8d138 .. 0x8d228): after inflateInit
   returns at 0x8cfb8 the code stores dest (from the frame cell SPA + 24) to next_out, then sets avail_out and avail_in
   from left (s3) and len (s11) against max (s6 = 0xffffffff), and calls inflate from two sites (ra 0x8d1d0 after the
   avail_in refill, ra 0x8d18c otherwise). Both sites merge at 0x8d1d4 on a zero return and leave to 0x8d1e0 on a
   nonzero one. The exit path stores *sourceLen -= len + avail_in and *destLen -= left + avail_out (through the frame
   cells SPA + 8 and SPA + 16, with their shadow checks) and calls inflateEnd with ra 0x8d22c.
   Register file in the loop: s2 = Fu, s3 = left, s4 = SL, s5 = shadow SL, s6 = max, s7 = Zs, s8 = shadow Fu, s9 = Fu,
   s10 = the shadow offset, s11 = len. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit I_asan_memset.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2ABlob UwAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BCall U2BGlue U2BIface U2BIfaceS U2cB_pre U2BKit_p04.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (gp tp sp : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (D F1 Fu S lo SPA : Z) (RNG : footprint).
  Notation SP := (bv_unsigned sp).
  Variable SL : Z.
  Hypothesis ESL : SL = SP + 8.
  Notation DL := (SP + 16).
  Notation Zs := (Fu + 32).
  Hypothesis FU256 : Fu mod 256 = 0.
  Hypothesis FUB : ablk Fu (Fu + 256).
  Hypothesis RFU : rng RNG Fu 256.
  Hypothesis RSFU : rng RNG (Z.shiftr Fu 3 + 2147450880) 32.

  (* the 1.4 loop register file; v10 rides in s6 (D before the loop, max in it) *)
  Notation LOOP pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 len v10 left x28 x29 x30 x31 mm :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             (* [U14B] A2 2026-11-12: the COMBINED 1.4 image: s3 = destLen, s5 = left (0x8d194 mv a0,s5; 0x8d1a4 sub s5,s5,a0);
                the ASan 1.4 image has left in s3 and shadow(sourceLen) in s5 (dis/unc2-asan14-both14-r1.txt) *)
             (Z_to_bv 64 Fu) (Z_to_bv 64 DL) (Z_to_bv 64 SL) (Z_to_bv 64 left) v10 (Z_to_bv 64 Zs)
             (Z_to_bv 64 (Z.shiftr Fu 3 + 2147450880)) (Z_to_bv 64 Fu) (Z_to_bv 64 2147450880) (Z_to_bv 64 len) x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Lemma uc_first : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (n0 : Z) (j8 j16 : list byte)
      (ti no ao to msg state za zf opq dt adler reserved p1 p2 p3 : word),
    mem_inv bsegs m ->
    rw_cells bsegs m SPA (UFRA sp SL Fu j8 j16) ->
    rw_cells bsegs m Zs (strm_cells (Z_to_bv 64 D) (Z_to_bv 64 0) ti no ao to msg state za zf opq dt adler reserved p1 p2 p3) ->
    shadow_bytes m (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0) ->
    0 <= n0 < 67108864 ->
    rng RNG SPA 56 -> ATOP + 4096 <= SPA -> SPA + 56 <= SP ->
    evtF bsegs RNG (fun ms' => exists m',
        ms' = LOOP A_INFLATE (Z_to_bv 64 0x8d198) x5 x6 x7 (Z_to_bv 64 Zs) (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17 0 (Z_to_bv 64 4294967295) 0 x28 x29 x30 x31 m'
        /\ munch [(Fu + 32, Fu + 144)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' Zs (strm_cells (Z_to_bv 64 D) (Z_to_bv 64 n0) ti (Z_to_bv 64 6341696) (Z_to_bv 64 262144) to msg state za zf opq dt adler reserved p1 p2 p3))
      (LOOP 0x8cf80 (Z_to_bv 64 0x8cf80) x5 x6 x7 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 n0 (Z_to_bv 64 D) 262144 x28 x29 x30 x31 m).
  Proof using All.
    intros until p3. intros MI FRA STRM SHZ N0 RFRM SPA1 SPA2. unfold UFRA, strm_cells, A_INFLATE in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    atop_facts. pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    assert (Z8 : Zs mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (F8 : Fu mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (DJZ : disjoint_from [(Fu + 32, Fu + 144)] (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14 - (Z.shiftr Zs 3 + 2147450880))).
    { cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB. Z.div_mod_to_equations. lia. }
    band_ind FUB bU.
    pose proof (munch_refl [(Fu + 32, Fu + 144)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zrung [0x8d194].
    zs.
    try replace (n0 - n0) with 0 by lia. try replace (262144 - 262144) with 0 by lia.
    apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact STRM].
  Qed.

  Lemma uc_ret0 : forall (rapc : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m,
    rapc = 0x8d154 \/ rapc = 0x8d198 ->
    evtF bsegs RNG (fun ms' => ms' = LOOP 0x8d19c (Z_to_bv 64 rapc) x5 x6 x7 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 0 (Z_to_bv 64 4294967295) 0 x28 x29 x30 x31 m)
      (LOOP rapc (Z_to_bv 64 rapc) x5 x6 x7 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 0 (Z_to_bv 64 4294967295) 0 x28 x29 x30 x31 m).
  Proof using All.
    intros until m. intros [->| ->].
    - zs. apply evtF_done. reflexivity.
    - zs. apply evtF_done. reflexivity.
  Qed.

  Lemma uc_retN : forall (rapc rcode : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m,
    rapc = 0x8d154 \/ rapc = 0x8d198 -> rcode <> 0 -> 0 <= rcode < 2^64 ->
    evtF bsegs RNG (fun ms' => ms' = LOOP 0x8d1a8 (Z_to_bv 64 rapc) x5 x6 x7 (Z_to_bv 64 rcode) x11 x12 x13 x14 x15 x16 x17 0 (Z_to_bv 64 4294967295) 0 x28 x29 x30 x31 m)
      (LOOP rapc (Z_to_bv 64 rapc) x5 x6 x7 (Z_to_bv 64 rcode) x11 x12 x13 x14 x15 x16 x17 0 (Z_to_bv 64 4294967295) 0 x28 x29 x30 x31 m).
  Proof using All.
    intros until m. intros [->| ->] NZ RR.
    - zs. zbr K. zs. apply evtF_done. reflexivity.
    - zs. zbr K. apply evtF_done. reflexivity.
  Qed.

  Lemma uc_next : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (avin avout : Z)
      (ni ti no to msg state za zf opq dt adler reserved p1 p2 p3 : word),
    mem_inv bsegs m ->
    rw_cells bsegs m Zs (strm_cells ni (Z_to_bv 64 avin) ti no (Z_to_bv 64 avout) to msg state za zf opq dt adler reserved p1 p2 p3) ->
    0 <= avin <= 67108864 -> 0 <= avout <= 262144 ->
    evtF bsegs RNG (fun ms' => exists m' (rapc : Z) (y10' : word),
        (rapc = 0x8d154 \/ rapc = 0x8d198)
        /\ ms' = LOOP A_INFLATE (Z_to_bv 64 rapc) x5 x6 x7 (Z_to_bv 64 Zs) (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17 0 (Z_to_bv 64 4294967295) 0 x28 x29 x30 x31 m'
        /\ munch [(Fu + 32, Fu + 144)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' Zs (strm_cells ni (Z_to_bv 64 avin) ti no (Z_to_bv 64 avout) to msg state za zf opq dt adler reserved p1 p2 p3))
      (LOOP 0x8d19c x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 0 (Z_to_bv 64 4294967295) 0 x28 x29 x30 x31 m).
  Proof using All.
    intros until p3. intros MI STRM AVI AVO. unfold strm_cells, A_INFLATE in *.
    atop_facts. pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    band_ind FUB bU.
    pose proof (munch_refl [(Fu + 32, Fu + 144)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zrung [0x8d150; 0x8d194].
    zbr KO.
    all: zrung [0x8d150; 0x8d194].
    all: try zbr KI.
    all: zrung [0x8d150; 0x8d194].
    all: zs.
    all: try replace (0 - 0) with 0 by lia.
    all: apply evtF_done;
         first [ (eexists _, 0x8d154, (Z_to_bv 64 0); split; [left; reflexivity|]; split; [reflexivity|])
               | (eexists _, 0x8d198, (Z_to_bv 64 0); split; [right; reflexivity|]; split; [reflexivity|]) ];
         split; [exact MU|]; split; [exact WM|]; split; [eassumption|].
    all: first [ exact STRM
               | (assert (avin = 0) by lia; subst avin; exact STRM)
               | (assert (avout = 0) by lia; subst avout; exact STRM)
               | (assert (avout = 0) by lia; assert (avin = 0) by lia; subst avout avin; exact STRM) ].
  Qed.

  Hypothesis RSDL : rng RNG (Z.shiftr DL 3 + 2147450880) 1.
  Hypothesis RSSL : rng RNG (Z.shiftr SL 3 + 2147450880) 1.
  Hypothesis RFRM : rng RNG SPA 56.
  Hypothesis SPAR : ATOP + 4096 <= SPA /\ SPA + 56 <= SP.
  Hypothesis SPT : SP + 48 <= 2^47.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis RSLC : rng RNG SL 8.
  Hypothesis RDLC : rng RNG DL 8.

  (* 1.4 exit: from the loop exit at 0x8d1e0 (a0 = the nonzero inflate return) to the inflateEnd call. *)
  Lemma uc_exit : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (rcode : Z) (j8 j16 : list byte)
      (ni ai ti no ao to msg state za zf opq dt adler reserved p1 p2 p3 dlv slv : word),
    mem_inv bsegs m ->
    rw_cells bsegs m SPA (UFRA sp SL Fu j8 j16) ->
    rw_cells bsegs m Zs (strm_cells ni ai ti no ao to msg state za zf opq dt adler reserved p1 p2 p3) ->
    rw_cells bsegs m DL [C8 dlv] -> rw_cells bsegs m SL [C8 slv] ->
    shadow_bytes m (Z.shiftr DL 3 + 2147450880) (Z.shiftr DL 3 + 2147450880 + 1) (fun _ => 0) ->
    shadow_bytes m (Z.shiftr SL 3 + 2147450880) (Z.shiftr SL 3 + 2147450880 + 1) (fun _ => 0) ->
    0 <= rcode < 2^64 ->
    evtF bsegs RNG (fun ms' => exists m' (slv' dlv' y11 y12 q27 : word),
        ms' = MS (mkR (Z_to_bv 64 0x8d1f4) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 Zs) y11 y12 x13 x14 x15 x16 x17
                     (* [U14B] A2 2026-11-12: the COMBINED 1.4 image at the inflateEnd call: s3 = destLen, s5 = left = 0, and the
                        inflate return code in s6 (0x8d1ec mv s6,a0, over max); ASan: left in s3, the code in s5, max in s6 *)
                     (Z_to_bv 64 Fu) (Z_to_bv 64 DL) (Z_to_bv 64 SL) (Z_to_bv 64 0) (Z_to_bv 64 rcode) (Z_to_bv 64 Zs)
                     (Z_to_bv 64 (Z.shiftr Fu 3 + 2147450880)) (Z_to_bv 64 Fu) (Z_to_bv 64 2147450880) q27 x28 x29 x30 x31)
                 FR (Z_to_bv 64 A_INFLATEEND) fc None m' (seg_rom bsegs)
        /\ munch [(DL, DL + 8); (SL, SL + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' DL [C8 dlv'] /\ rw_cells bsegs m' SL [C8 slv'])
      (LOOP 0x8d1a8 x1 x5 x6 x7 (Z_to_bv 64 rcode) x11 x12 x13 x14 x15 x16 x17 0 (Z_to_bv 64 4294967295) 0 x28 x29 x30 x31 m).
  Proof using All.
    intros until slv. intros MI FRA STRM DLC SLC SHD SHSL RC. unfold strm_cells, UFRA, A_INFLATEEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    atop_facts. pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    pose proof SPAR as (SPA1 & SPA2).
    assert (SP8 : SP mod 8 = 0) by (Z.div_mod_to_equations; lia).
    pose (W := [(DL, DL + 8); (SL, SL + 8)]).
    assert (DJD : disjoint_from W (Z.shiftr DL 3 + 2147450880) (Z.shiftr DL 3 + 2147450880 + 1 - (Z.shiftr DL 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite ESL. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold KLS. Z.div_mod_to_equations. lia. }
    assert (DJL : disjoint_from W (Z.shiftr SL 3 + 2147450880) (Z.shiftr SL 3 + 2147450880 + 1 - (Z.shiftr SL 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite ESL. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold KLS. Z.div_mod_to_equations. lia. }
    band_ind FUB bU.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM. subst W.
    zrung [0x8d1f0].
    zs.
    apply evtF_done. do 6 eexists. split; [reflexivity|]. split; [try replace (SP + 24) with (DL + 8) by lia; exact MU|].
    split; [exact WM|]. split; [eassumption|].
    split; eassumption.
  Qed.
End S.
End CANSEC1.
