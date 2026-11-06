(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA Arr Walk Image SysStep.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.openssl.punycode.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanRehashModel AsanRegModel.
From OSSVerify.Proofs.openssl.punycode.lib.B Require R_memiszero.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Shadow R_arrkit.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import Layout RT_iface R_small R_cache_defs F_memset X_atexit X_gdefs X_unregi XR_rehash XR_kit XR_probe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation TABA := 0x5e76c0%Z (only parsing).

Section Iter.
Variables (fp n : Z) (gp tp s3 s10 : word) (F : bvmap 5 word) (fc : bv 32).

(* [comment removed for export] *)
Definition st_entry (i : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 t3 t4 t5 t6 : word) (pc : Z) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 (fp - 0x10f0)) gp tp t0 t1 t2 (Z_to_bv 64 fp) (Z_to_bv 64 TABA) a0 a1 a2 a3 a4 a5 a6 a7
          s2 s3 (Z_to_bv 64 0x6a3a78) (Z_to_bv 64 1) s6 s7 (Z_to_bv 64 0x6a1278) (Z_to_bv 64 0x6a12f0) s10 (Z_to_bv 64 i) t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Lemma reg_head : forall (i g beg size swr odr : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 t3 t4 t5 t6 : word) (m : mem),
  0 <= i < 2 ^ 24 -> g = TABA + 64 * i ->
  ro_cells bsegs m g [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 swr)] ->
  ro_cells bsegs m (g + 56) [C8 (Z_to_bv 64 odr)] ->
  0x10000 <= beg -> beg mod 8 = 0 -> 0 <= swr -> swr mod 8 = 0 -> beg + swr <= 0xbfd000 -> 0 <= odr < 2 ^ 64 ->
  rw_cells bsegs m 0x6a4758 [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x6a1290 [C4 (Z_to_bv 64 1)] -> ro_cells bsegs m 0x6a12dc [C4 (Z_to_bv 64 2)] ->
  ro_cells bsegs m 0x6a3a78 [C8 (Z_to_bv 64 0x7fff8000)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = st_entry i (Z_to_bv 64 0x1a445c) t0' t1' t2' (Z_to_bv 64 beg) (Z_to_bv 64 swr) (Z_to_bv 64 odr) (Z_to_bv 64 (-1)) a4' a5' a6' a7'
                     s2 (Z_to_bv 64 g) s7 t3' t4' t5' t6' (if odr =? RGM.ODR_NONE then 0x1a4870 else 0x1a46dc) m'
      /\ munch [] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m')
    (st_entry i ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 t3 t4 t5 t6 0x1a4458 m).
Proof.
  intros until m. intros Hi Hg REC RODR B0 B8 S0 S8 BT HO AI RG DO SHC MI. unfold st_entry in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  xstep.
  call asan_inited_spec; [exact AI| exact MI|].
  xsteps_to 0x1a446c%Z.
  rewrite (Z.shiftl_mul_pow2 i 6) by lia.
  lazymatch goal with |- context [Z_to_bv 64 (?tb + i * 2 ^ 6)] => replace (tb + i * 2 ^ 6) with g by lia end.
  xsteps_to 0x1a44a8%Z.
  xstep. fold_closed_regs. ifT.
  xstep. rewrite (land_7 beg ltac:(lia)), B8. xstep.
  xstep. xstep. rewrite (land_7 swr S0), S8. xstep.
  xsteps_to 0x1a46d8%Z.
  xstep.
  rewrite bv_eqb_Z, (unsigned_lit odr) by lia. change (bv_unsigned (Z_to_bv 64 (-1))) with RGM.ODR_NONE.
  apply evt_done. do 12 eexists. split; [| split; [exact MU| split; [exact WM| assumption]]].
  destruct (odr =? RGM.ODR_NONE); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma reg_poison : forall (i g beg size swr : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s7 t3 t4 t5 t6 : word) (m : mem),
  TABA <= g -> g + 64 <= 0x6a03c0 -> 0x80177a00 <= fp + -4304 -> fp < 2 ^ 47 ->
  ro_cells bsegs m g [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 swr)] ->
  0x10000 <= beg -> beg mod 8 = 0 -> swr mod 8 = 0 -> 1 <= size -> RGM.rup8 size <= swr -> swr < 0x80000 -> beg + swr <= 0xbfd000 ->
  ro_cells bsegs m 0x6a3a78 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells bsegs m 0x6a12cd [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x5e4190 [C8 (Z_to_bv 64 0x563738)] ->
  ro_cells bsegs m (fp + -4304) [C8 (Z_to_bv 64 0x5e4190)] ->
  stk bsegs m SHW_LO SHW_HI ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word) (m' : mem),
      ms' = st_entry i ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' (Z_to_bv 64 g) s7 t3' t4' t5' t6' 0x1a49fc m'
      /\ munch [(0x7fff8000 + beg / 8, 0x7fff8000 + (beg + swr) / 8)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' SHW_LO SHW_HI)
    (st_entry i ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 g) s7 t3 t4 t5 t6 0x1a4878 m).
Proof.
  intros until m. intros G0 G1 FP0 FP1 REC B0 B8 S8 Z1 RU SW BT SHC PP MSC MP SCW MI.
  unfold st_entry in *.
  pose proof (munch_refl [(0x7fff8000 + beg / 8, 0x7fff8000 + (beg + swr) / 8)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  xsteps_to 0x1a4890%Z. change (- (4096)) with (-4096).
  xsteps_to 0x1a48c8%Z.
  assert (E64 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551615 = x)
    by (intros x Hx; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; exact Hx).
  set (al := RGM.rup8 size) in *.
  assert (ALF : al mod 8 = 0 /\ size <= al < size + 8) by (unfold al, RGM.rup8; Z.div_mod_to_equations; lia).
  assert (EA : Z.land (Z.land (size + 7) 18446744073709551615) 18446744073709551608 = al)
    by (rewrite (E64 (size + 7)) by lia; rewrite R_memiszero.land_m8 by lia; reflexivity).
  rewrite !EA.
  assert (ED : Z.land (al + beg) 18446744073709551615 ≫ 3 + 2147450880 = 2147450880 + (beg + al) / 8)
    by (rewrite (E64 (al + beg)) by lia; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; replace (al + beg) with (beg + al) by lia; lia).
  rewrite !ED.
  assert (EN : 2147450880 + Z.land (beg + swr + -8) 18446744073709551615 ≫ 3 + - Z.land (2147450880 + (beg + al) / 8) 18446744073709551615 + 1 = (swr - al) / 8).
  { rewrite (E64 (beg + swr + -8)) by lia. rewrite (E64 (2147450880 + (beg + al) / 8)) by (Z.div_mod_to_equations; lia).
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  rewrite EN.
  xstep.
  assert (N0 : 0 <= (swr - al) / 8) by (Z.div_mod_to_equations; lia).
  assert (SL0 : 0x7fffa000 <= 2147450880 + (beg + al) / 8) by (Z.div_mod_to_equations; lia).
  assert (SH0 : 2147450880 + (beg + al) / 8 + (swr - al) / 8 <= 0x80177a00) by (Z.div_mod_to_equations; lia).
  destruct (stk_window _ _ _ (2147450880 + (beg + al) / 8) ((swr - al) / 8) SCW SL0 SH0 N0) as (SA & (junk & DST) & SB). clear SCW.
  call memset_callZ; [exact DST| assumption| lia| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia| lia|].
  pose proof (stk_unwindow _ _ _ _ ((swr - al) / 8) _ SA POST ltac:(cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; reflexivity)
                SB SL0 SH0) as SCW.
  clear SA SB POST.
  xstep. xstep.
  assert (EUs : bv_unsigned (Z_to_bv 64 size) = size) by (apply unsigned_lit; lia).
  assert (EUa : bv_unsigned (Z_to_bv 64 al) = al) by (apply unsigned_lit; lia).
  rewrite bv_eqb_Z, EUs, EUa.
  destruct (Z.eqb_spec size al) as [EQ|NE].
  - (* [comment removed for export] *)
    apply evt_done. do 18 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact SCW].
  - xstep. rewrite (land_7 size ltac:(lia)).
    assert (SM : size mod 8 <> 0) by (unfold al, RGM.rup8 in *; Z.div_mod_to_equations; lia).
    xstep.
    assert (EUm : bv_unsigned (Z_to_bv 64 (size mod 8)) = size mod 8) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
    rewrite bv_eqb_Z, EUm. change (bv_unsigned z64) with 0. rewrite (proj2 (Z.eqb_neq _ _) SM). cbn [negb].
    xsteps_to 0x1a49f8%Z.
    assert (EP : Z.land (beg + Z.land size 18446744073709551608) 18446744073709551615 ≫ 3 + 2147450880 = 2147450880 + (beg + size / 8 * 8) / 8).
    { rewrite R_memiszero.land_m8 by lia. rewrite (E64 (beg + size / 8 * 8)) by (Z.div_mod_to_equations; lia).
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia. }
    rewrite EP.
    assert (PL0 : 0x7fffa000 <= 2147450880 + (beg + size / 8 * 8) / 8) by (Z.div_mod_to_equations; lia).
    assert (PH0 : 2147450880 + (beg + size / 8 * 8) / 8 + 1 <= 0x80177a00) by (Z.div_mod_to_equations; lia).
    destruct (stk_window _ _ _ (2147450880 + (beg + size / 8 * 8) / 8) 1 SCW PL0 PH0 ltac:(lia)) as (SA & (junk1 & DST1) & SB). clear SCW.
    change (Z.to_nat 1) with 1%nat in DST1.
    remember (2147450880 + (beg + size / 8 * 8) / 8) as PB eqn:EPB.
    assert (EUpb : bv_unsigned (Z_to_bv 64 PB) = PB) by (apply unsigned_lit; lia).
    assert (EUpb1 : bv_unsigned (Z_to_bv 64 (PB + 1)) = PB + 1) by (apply unsigned_lit; lia).
    assert (EV : Z_to_bv 64 (Z.land (Z.land (0 + - (1)) 18446744073709551615) (size mod 8)) = zxb (Z_to_bv 8 (size mod 8))).
    { change (Z.land (0 + - (1)) 18446744073709551615) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
      rewrite (Z.mod_small (size mod 8)) by (Z.div_mod_to_equations; lia).
      unfold zxb. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. symmetry. apply Z.mod_small. Z.div_mod_to_equations. lia. }
    rewrite EV.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa (le1 (?f ?b))) _) =>
      change (le1 (f b)) with (le1 (zxb b)) end.
    rewrite le1_zxb.
    mem_after_store.
    lazymatch goal with DST' : rw_cells bsegs ?mm PB ?cs |- _ =>
      pose proof (stk_unwindow mm _ _ PB 1 cs SA DST' ltac:(reflexivity) SB ltac:(lia) ltac:(lia)) as SCW end.
    apply evt_done. do 18 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| exact SCW].
Qed.

(* [comment removed for export] *)
Lemma reg_addlist : forall (i g lend cur CEND lsize first : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s7 t3 t4 t5 t6 : word) (m : mem),
  0 <= i -> i + 1 < n -> TABA + 64 * n <= 0x6a03c0 -> g = TABA + 64 * i ->
  ro_cells bsegs m (g + 40) [C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x5e41d0 [C8 (Z_to_bv 64 8)] ->
  ro_cells bsegs m (fp + -4272) [C8 (Z_to_bv 64 n)] ->
  stk bsegs m (fp - 0x10f0 - 32) (fp - 0x10f0) -> 0x80177a00 <= fp - 0x10f0 - 32 -> fp < 2 ^ 47 ->
  rw_cells bsegs m LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 cur)] -> 0 < cur -> cur + 16 <= CEND -> CEND <= lend -> lend < 2 ^ 47 ->
  stk bsegs m cur CEND -> (CEND <= 0x10000 \/ 0xbfd000 <= cur) ->
  (CEND <= fp - 0x10f0 - 32 \/ fp <= cur) ->
  rw_cells bsegs m 0x6a12f8 [C8 (Z_to_bv 64 lsize); C8 (Z_to_bv 64 first)] -> 1 <= lsize -> lsize + 1 < 2 ^ 63 ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = st_entry (i + 1) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 g) s7 t3' t4' t5' t6' 0x1a4458 m'
      /\ munch [(fp - 0x10f0 - 32, fp - 0x10f0); (0x6a12f8, 0x6a1308); (LLA + 8, LLA + 16); (cur, cur + 16)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' (fp - 0x10f0 - 32) (fp - 0x10f0)
      /\ rw_cells bsegs m' LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 (cur + 16))]
      /\ stk bsegs m' (cur + 16) CEND
      /\ rw_cells bsegs m' 0x6a12f8 [C8 (Z_to_bv 64 (lsize + 1)); C8 (Z_to_bv 64 cur)])
    (st_entry i ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 g) s7 t3 t4 t5 t6 0x1a49fc m).
Proof.
  intros until m. intros Hi Hin Hn Hg RDYN AL NS FRS SPlo FPhi LLC C0 CR CE LE AST AI AFR HDR LS1 LS2 MI.
  unfold st_entry in *.
  pose proof (munch_refl [(fp - 0x10f0 - 32, fp - 0x10f0); (0x6a12f8, 0x6a1308); (0x725cc8 + 8, 0x725cc8 + 16); (cur, cur + 16)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  xstep. xstep. xstep. xstep. xstep. xstep.
  assert (SPR : fp - 0x10f0 < 2 ^ 63) by lia.
  call (lla_alloc16_spec (fp - 0x10f0)); [reflexivity| reflexivity| exact FRS| lia| unfold SEGTOP_A; lia| exact SPR| exact AL| exact LLC| lia| lia| lia| assumption|].
  destruct (stk_window _ _ _ cur 16 AST ltac:(lia) ltac:(lia) ltac:(lia)) as (SA & (junkn & NODE) & SB). clear AST SA.
  change (Z.to_nat 16) with 16%nat in NODE.
  assert (EUc : bv_unsigned (Z_to_bv 64 cur) = cur) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 lsize) = lsize) by (apply unsigned_lit; lia).
  xsteps_to 0x1a4a2c%Z. xstep.
  xstep. xstep. xstep. xstep. change (- (4096)) with (-4096). xstep.
  assert (EUi : bv_unsigned (Z_to_bv 64 (i + 1)) = i + 1) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  xstep.
  apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [assumption|]. split; [assumption|]. split; [exact SB| exact HDR].
Qed.

(* [comment removed for export] *)
Lemma reg_ind : forall (i g odr B N ne p lend cur CEND : Z) (ks : list Z) (nws : list word)
    (ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s2 s7 t3 t4 t5 t6 : word) (m : mem),
  TABA <= g -> g + 64 <= 0x6a03c0 ->
  ro_cells bsegs m (g + 56) [C8 (Z_to_bv 64 odr)] -> 0xbd6a20 <= odr < 0xbda496 ->
  RGM.probe_ins N ks odr (RGM.hash0 N odr) 1 (Z.to_nat N) = Some p ->
  RGM.no_grow N ne = true ->
  8 <= N <= 2 ^ 20 -> 0 <= ne -> Forall (fun k => 0 <= k < 2 ^ 64) ks ->
  rw_cells bsegs m 0x6a1328 [C8 (Z_to_bv 64 MAPA)] ->
  rw_cells bsegs m MAPA [C8 (Z_to_bv 64 B); C4 (Z_to_bv 64 ne); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 N)] ->
  u64arr bsegs m B nws -> keys_rep (Z.to_nat N) nws ks ->
  0 < B -> B + 32 * N <= 2 ^ 47 -> (B + 32 * N <= 0x10000 \/ 0xbfd000 <= B) ->
  (B + 32 * N <= cur \/ CEND <= B) -> (B + 32 * N <= fp - 0x10f0 - 32 \/ fp <= B) ->
  rw_cells bsegs m odr [C1 (Z_to_bv 8 0)] ->
  ro_cells bsegs m 0x6a32dc [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x5e41d0 [C8 (Z_to_bv 64 8)] ->
  stk bsegs m (fp + -4264) (fp + -4256) ->
  stk bsegs m (fp - 0x10f0 - 32) (fp - 0x10f0) -> 0x80177a00 <= fp - 0x10f0 - 32 -> fp < 2 ^ 47 ->
  rw_cells bsegs m LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 cur)] -> 0 < cur -> cur + 16 <= CEND -> CEND <= lend -> lend < 2 ^ 47 ->
  stk bsegs m cur CEND -> (CEND <= 0x10000 \/ 0xbfd000 <= cur) ->
  (CEND <= fp - 0x10f0 - 32 \/ fp <= cur) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (nws' : list word) (m' : mem),
      ms' = st_entry i ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 g) (Z_to_bv 64 (B + 32 * p)) t3' t4' t5' t6' 0x1a4878 m'
      /\ munch [(fp + -4264, fp + -4256); (fp - 0x10f0 - 32, fp - 0x10f0); (MAPA + 8, MAPA + 12); (B + 32 * p, B + 32 * p + 32);
                (odr, odr + 1); (LLA + 8, LLA + 16); (cur, cur + 16)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' (fp + -4264) (fp + -4256)
      /\ stk bsegs m' (fp - 0x10f0 - 32) (fp - 0x10f0)
      /\ rw_cells bsegs m' MAPA [C8 (Z_to_bv 64 B); C4 (Z_to_bv 64 (ne + 1)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 N)]
      /\ u64arr bsegs m' B nws' /\ keys_rep (Z.to_nat N) nws' (RGM.upd ks (Z.to_nat p) odr)
      /\ rw_cells bsegs m' odr [C1 (Z_to_bv 8 1)]
      /\ rw_cells bsegs m' LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 (cur + 16))]
      /\ stk bsegs m' (cur + 16) CEND)
    (st_entry i ra t0 t1 t2 a0 a1 (Z_to_bv 64 odr) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 g) s7 t3 t4 t5 t6 0x1a46dc m).
Proof.
  intros until m. intros G0 G1 RODR HO PI NG HN Hne KF MPC MAP NA KR B0 BT BI BC BF IND CP AL KSS FRS SPlo FPhi LLC C0 CR CE LE AST AI AFR MI.
  unfold st_entry in *.
  pose proof (munch_refl [(fp + -4264, fp + -4256); (fp - 0x10f0 - 32, fp - 0x10f0); (0x6a1358 + 8, 0x6a1358 + 12); (B + 32 * p, B + 32 * p + 32);
                          (odr, odr + 1); (0x725cc8 + 8, 0x725cc8 + 16); (cur, cur + 16)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (HLn : length nws = (4 * Z.to_nat N)%nat) by (destruct KR as (L & _); exact L).
  assert (EUo : bv_unsigned (Z_to_bv 64 odr) = odr) by (apply unsigned_lit; lia).
  xstep. xstep. xstep. xstep. xstep. change (- (4264)) with (-4264).
  destruct (stk_window _ _ _ (fp + -4264) 8 KSS ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (junkk & KS) & _). clear KSS.
  change (Z.to_nat 8) with 8%nat in KS.
  xstep. xstep.
  xstep. xstep. xstep. change (- (4264)) with (-4264). xstep.
  call (fac_spec B N ne odr p (fp + -4264) (fp - 0x10f0) 0x1a482c ks nws);
    [exact PI| exact NG| exact HN| exact Hne| exact KF| lia| exact KS| exact MAP| exact NA| exact KR| exact FRS| exact B0| exact BT
    | unfold SEGTOP_A; lia| unfold SEGTOP_A; lia| lia| lia| lia| lia| reflexivity| assumption|].
  rename PC0 into NA1, PC1 into KR1, PC2 into V1, PC3 into FRS1, PC4 into Hp0, POST into Hp1, PC into MAP1.
  lazymatch type of KR1 with keys_rep _ ?w _ => set (nws1 := w) in * end.
  assert (HLn1 : length nws1 = (4 * Z.to_nat N)%nat) by (destruct KR1 as (L & _); exact L).
  xstep. xstep. xstep. xstep.
  xstep.
  xstep. xstep. xstep. xstep. xstep. xstep.
  assert (SPR : fp - 0x10f0 < 2 ^ 63) by lia.
  call (lla_alloc16_spec (fp - 0x10f0)); [reflexivity| reflexivity| exact FRS1| lia| unfold SEGTOP_A; lia| exact SPR| exact AL| exact LLC| lia| lia| lia| assumption|].
  rename PC into FRS2, POST into LLC2.
  destruct (stk_window _ _ _ cur 16 AST ltac:(lia) ltac:(lia) ltac:(lia)) as (SA & (junkn & NODE) & SB). clear AST SA.
  change (Z.to_nat 16) with 16%nat in NODE.
  assert (EUc : bv_unsigned (Z_to_bv 64 cur) = cur) by (apply unsigned_lit; lia).
  xstep.
  (* [comment removed for export] *)
  lazymatch goal with NAx : u64arr bsegs ?mm B nws1 |- _ =>
    pose proof (u64arr_read bsegs mm B nws1 (4 * p + 1) _ (Z_to_bv 64 (B + 32 * p + 8)) NAx V1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  xstep. clear RD.
  xstep. xstep.
  (* [comment removed for export] *)
  lazymatch goal with NAx : u64arr bsegs ?mm B ?xs |- _ =>
    pose proof (u64arr_store_ok bsegs mm B _ (4 * p + 1) (wa (B + 8 * (4 * p + 1))) NAx ltac:(rewrite ?upd_length, HLn1; lia) eq_refl) as SOK;
    pose proof (u64arr_write bsegs mm B _ (4 * p + 1) (Z_to_bv 64 1) NAx ltac:(rewrite ?upd_length, HLn1; lia)) as NA2 end.
  replace (B + 8 * (4 * p + 1)) with (B + 32 * p + 8) in SOK, NA2 by lia.
  zstep. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) => change bs with (le8 (Z_to_bv 64 1)) end. clear NA1. store_done.
  lazymatch goal with NAx : u64arr bsegs ?mm B ?xs |- _ =>
    pose proof (u64arr_store_ok bsegs mm B _ (4 * p + 2) (wa (B + 8 * (4 * p + 2))) NAx ltac:(rewrite ?upd_length, HLn1; lia) eq_refl) as SOK;
    pose proof (u64arr_write bsegs mm B _ (4 * p + 2) (Z_to_bv 64 cur) NAx ltac:(rewrite ?upd_length, HLn1; lia)) as NA3 end.
  replace (B + 8 * (4 * p + 2)) with (B + 32 * p + 16) in SOK, NA3 by lia.
  zstep. clear NA2. store_done.
  lazymatch goal with NAx : u64arr bsegs ?mm B ?xs |- _ =>
    pose proof (u64arr_store_ok bsegs mm B _ (4 * p + 3) (wa (B + 8 * (4 * p + 3))) NAx ltac:(rewrite ?upd_length, HLn1; lia) eq_refl) as SOK;
    pose proof (u64arr_write bsegs mm B _ (4 * p + 3) (Z_to_bv 64 cur) NAx ltac:(rewrite ?upd_length, HLn1; lia)) as NA4 end.
  replace (B + 8 * (4 * p + 3)) with (B + 32 * p + 24) in SOK, NA4 by lia.
  zstep. clear NA3. store_done.
  xstep.
  call can_poison_spec; [exact CP| assumption|].
  xstep. xstep.
  lazymatch goal with KSx : rw_cells bsegs ?mm (fp + -4264) [C8 _] |- _ =>
    pose proof (stk_of_rw_cells bsegs mm (fp + -4264) _ KSx) as KSS; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in KSS end.
  replace (fp + -4264 + 8) with (fp + -4256) in KSS by lia.
  apply evt_done. do 16 eexists.
  eexists (upd (upd (upd nws1 (Z.to_nat (4 * p + 1)) (Z_to_bv 64 1)) (Z.to_nat (4 * p + 2)) (Z_to_bv 64 cur)) (Z.to_nat (4 * p + 3)) (Z_to_bv 64 cur)).
  eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact KSS|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [do 3 (apply keys_rep_set_val; [| apply mod4_ne; lia]); exact KR1|].
  split; [assumption|]. split; [assumption| exact SB].
Qed.

End Iter.
