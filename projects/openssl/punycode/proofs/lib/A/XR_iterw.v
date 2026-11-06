(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA Arr Walk Image SysStep.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.openssl.punycode.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanRehashModel AsanRegModel.
From OSSVerify.Proofs.openssl.punycode.lib.A Require R_memiszero.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Layout Shadow RT_iface R_arrkit R_small R_cache_defs F_memset X_atexit X_gdefs X_unregi XR_rehash XR_kit XR_probe XR_iter.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


Section IterW.
Variables (fp n : Z) (gp tp s3 s10 : word) (F : bvmap 5 word) (fc : bv 32).
Local Notation st_entry := (XR_iter.st_entry fp gp tp s3 s10 F fc) (only parsing).

(* [comment removed for export] *)
Lemma reg_iter_common : forall (i g beg size swr lend cur CEND lsize first : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 t3 t4 t5 t6 : word) (m : mem),
  0 <= i -> i + 1 < n -> TABA + 64 * n <= 0x66d480 -> g = TABA + 64 * i ->
  ro_cells asegs m g [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 swr)] ->
  ro_cells asegs m (g + 40) [C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m (g + 56) [C8 (Z_to_bv 64 RGM.ODR_NONE)] ->
  0x10000 <= beg -> beg mod 8 = 0 -> swr mod 8 = 0 -> 1 <= size -> RGM.rup8 size <= swr -> swr < 0x80000 -> beg + swr <= 0xbca000 ->
  rw_cells asegs m 0x671818 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x66e350 [C4 (Z_to_bv 64 1)] -> ro_cells asegs m 0x66e39c [C4 (Z_to_bv 64 2)] -> ro_cells asegs m 0x66e38d [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x670b38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m 0x67039c [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x5ab7d0 [C8 (Z_to_bv 64 0x52a8ec)] ->
  ro_cells asegs m 0x5ab810 [C8 (Z_to_bv 64 8)] ->
  ro_cells asegs m (fp + -4272) [C8 (Z_to_bv 64 n)] ->
  ro_cells asegs m (fp + -4304) [C8 (Z_to_bv 64 0x5ab7d0)] ->
  stk asegs m (fp - 0x10f0 - 32) (fp - 0x10f0) -> 0x80171400 <= fp - 0x10f0 - 32 -> fp < 2 ^ 47 ->
  stk asegs m SHW_LO SHW_HI ->
  rw_cells asegs m LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 cur)] -> 0 < cur -> cur + 16 <= CEND -> CEND <= lend -> lend < 2 ^ 47 ->
  stk asegs m cur CEND -> (CEND <= 0x10000 \/ 0xbca000 <= cur) -> (CEND <= SHW_LO \/ SHW_HI <= cur) ->
  (CEND <= fp - 0x10f0 - 32 \/ fp <= cur) ->
  rw_cells asegs m 0x66e3b8 [C8 (Z_to_bv 64 lsize); C8 (Z_to_bv 64 first)] -> 1 <= lsize -> lsize + 1 < 2 ^ 63 ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word) (m' : mem),
      ms' = st_entry (i + 1) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' (Z_to_bv 64 g) s7 t3' t4' t5' t6' 0x1a9548 m'
      /\ munch [(fp - 0x10f0 - 32, fp - 0x10f0); (0x7fff8000 + beg / 8, 0x7fff8000 + (beg + swr) / 8); (0x66e3b8, 0x66e3c8); (LLA + 8, LLA + 16); (cur, cur + 16)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' (fp - 0x10f0 - 32) (fp - 0x10f0) /\ stk asegs m' SHW_LO SHW_HI
      /\ rw_cells asegs m' LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 (cur + 16))]
      /\ stk asegs m' (cur + 16) CEND
      /\ rw_cells asegs m' 0x66e3b8 [C8 (Z_to_bv 64 (lsize + 1)); C8 (Z_to_bv 64 cur)])
    (st_entry i ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 t3 t4 t5 t6 0x1a9548 m).
Proof.
  intros until m. intros Hi Hin Hn Hg REC RDYN RODR B0 B8 S8 Z1 RU SW BT AIN RG DO PP SHC CP MSC AL NS MP FRS SPlo FPhi SCW LLC C0 CR CE LE AST AI ASH AFR HDR LS1 LS2 MI.
  pose proof (munch_refl [(fp - 0x10f0 - 32, fp - 0x10f0); (0x7fff8000 + beg / 8, 0x7fff8000 + (beg + swr) / 8); (0x66e3b8, 0x66e3c8);
                          (0x6f2d88 + 8, 0x6f2d88 + 16); (cur, cur + 16)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  unfold XR_iter.st_entry.
  assert (S0 : 0 <= swr) by (unfold RGM.rup8 in RU; Z.div_mod_to_equations; lia).
  call (reg_head fp gp tp s3 s10 F fc i g beg size swr RGM.ODR_NONE); [lia| exact Hg| exact REC| exact RODR| lia| exact B8| exact S0| exact S8| lia| unfold RGM.ODR_NONE; lia
        | exact AIN| exact RG| exact DO| exact SHC| exact MI|].
  change (RGM.ODR_NONE =? RGM.ODR_NONE) with true. cbv iota. unfold XR_iter.st_entry.
  xstep.
  call can_poison_spec; [exact CP| assumption|].
  xstep.
  call (reg_poison fp gp tp s3 s10 F fc i g beg size swr); [lia| lia| lia| exact FPhi| eassumption| exact B0| exact B8| exact S8| exact Z1| exact RU| exact SW| exact BT
        | eassumption| eassumption| eassumption| eassumption| eassumption| assumption|].
  unfold XR_iter.st_entry.
  call (reg_addlist fp n gp tp s3 s10 F fc i g lend cur CEND lsize first); [exact Hi| exact Hin| exact Hn| exact Hg| eassumption| eassumption| eassumption
        | eassumption| exact SPlo| exact FPhi| eassumption| exact C0| exact CR| exact CE| exact LE| eassumption| exact AI| exact AFR
        | eassumption| exact LS1| exact LS2| assumption|].
  apply evt_done. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma reg_iter_ind : forall (i g beg size swr odr B N ne p lend cur CEND lsize first : Z) (ks : list Z) (nws : list word)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 t3 t4 t5 t6 : word) (m : mem),
  0 <= i -> i + 1 < n -> TABA + 64 * n <= 0x66d480 -> g = TABA + 64 * i ->
  ro_cells asegs m g [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 swr)] ->
  ro_cells asegs m (g + 40) [C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m (g + 56) [C8 (Z_to_bv 64 odr)] -> 0xba3ae0 <= odr < 0xba7556 ->
  0x10000 <= beg -> beg mod 8 = 0 -> swr mod 8 = 0 -> 1 <= size -> RGM.rup8 size <= swr -> swr < 0x80000 -> beg + swr <= 0xbca000 ->
  RGM.probe_ins N ks odr (RGM.hash0 N odr) 1 (Z.to_nat N) = Some p ->
  RGM.no_grow N ne = true ->
  8 <= N <= 2 ^ 20 -> 0 <= ne -> Forall (fun k => 0 <= k < 2 ^ 64) ks ->
  rw_cells asegs m 0x66e3e8 [C8 (Z_to_bv 64 MAPA)] ->
  rw_cells asegs m MAPA [C8 (Z_to_bv 64 B); C4 (Z_to_bv 64 ne); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 N)] ->
  u64arr asegs m B nws -> keys_rep (Z.to_nat N) nws ks ->
  0 < B -> B + 32 * N <= 2 ^ 47 -> (B + 32 * N <= 0x10000 \/ 0xbca000 <= B) -> (B + 32 * N <= SHW_LO \/ SHW_HI <= B) ->
  (B + 32 * N <= cur \/ CEND <= B) -> (B + 32 * N <= fp - 0x10f0 - 32 \/ fp <= B) ->
  rw_cells asegs m odr [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x671818 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x66e350 [C4 (Z_to_bv 64 1)] -> ro_cells asegs m 0x66e39c [C4 (Z_to_bv 64 2)] -> ro_cells asegs m 0x66e38d [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x670b38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m 0x67039c [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x5ab7d0 [C8 (Z_to_bv 64 0x52a8ec)] ->
  ro_cells asegs m 0x5ab810 [C8 (Z_to_bv 64 8)] ->
  ro_cells asegs m (fp + -4272) [C8 (Z_to_bv 64 n)] ->
  ro_cells asegs m (fp + -4304) [C8 (Z_to_bv 64 0x5ab7d0)] ->
  stk asegs m (fp + -4264) (fp + -4256) ->
  stk asegs m (fp - 0x10f0 - 32) (fp - 0x10f0) -> 0x80171400 <= fp - 0x10f0 - 32 -> fp < 2 ^ 47 ->
  stk asegs m SHW_LO SHW_HI ->
  rw_cells asegs m LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 cur)] -> 0 < cur -> cur + 32 <= CEND -> CEND <= lend -> lend < 2 ^ 47 ->
  stk asegs m cur CEND -> (CEND <= 0x10000 \/ 0xbca000 <= cur) -> (CEND <= SHW_LO \/ SHW_HI <= cur) ->
  (CEND <= fp - 0x10f0 - 32 \/ fp <= cur) ->
  rw_cells asegs m 0x66e3b8 [C8 (Z_to_bv 64 lsize); C8 (Z_to_bv 64 first)] -> 1 <= lsize -> lsize + 1 < 2 ^ 63 ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word) (nws' : list word) (m' : mem),
      ms' = st_entry (i + 1) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' (Z_to_bv 64 g) (Z_to_bv 64 (B + 32 * p)) t3' t4' t5' t6' 0x1a9548 m'
      /\ munch [(fp + -4264, fp + -4256); (fp - 0x10f0 - 32, fp - 0x10f0); (0x7fff8000 + beg / 8, 0x7fff8000 + (beg + swr) / 8);
                (0x66e3b8, 0x66e3c8); (LLA + 8, LLA + 16); (cur, cur + 32); (odr, odr + 1); (MAPA + 8, MAPA + 12); (B + 32 * p, B + 32 * p + 32)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' (fp + -4264) (fp + -4256)
      /\ stk asegs m' (fp - 0x10f0 - 32) (fp - 0x10f0) /\ stk asegs m' SHW_LO SHW_HI
      /\ rw_cells asegs m' LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 (cur + 32))]
      /\ stk asegs m' (cur + 32) CEND
      /\ rw_cells asegs m' 0x66e3b8 [C8 (Z_to_bv 64 (lsize + 1)); C8 (Z_to_bv 64 (cur + 16))]
      /\ rw_cells asegs m' MAPA [C8 (Z_to_bv 64 B); C4 (Z_to_bv 64 (ne + 1)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 N)]
      /\ u64arr asegs m' B nws' /\ keys_rep (Z.to_nat N) nws' (RGM.upd ks (Z.to_nat p) odr)
      /\ rw_cells asegs m' odr [C1 (Z_to_bv 8 1)] /\ 0 <= p < N)
    (st_entry i ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 t3 t4 t5 t6 0x1a9548 m).
Proof.
  intros until m. intros Hi Hin Hn Hg REC RDYN RODR HO B0 B8 S8 Z1 RU SW BT PI NG HN Hne KF MPC MAP NA KR HB0 HBT BI BSH BC BF IND
         AIN RG DO PP SHC CP MSC AL NS MP KSS FRS SPlo FPhi SCW LLC C0 CR CE LE AST AI ASH AFR HDR LS1 LS2 MI.
  pose proof (munch_refl [(fp + -4264, fp + -4256); (fp - 0x10f0 - 32, fp - 0x10f0); (0x7fff8000 + beg / 8, 0x7fff8000 + (beg + swr) / 8);
                          (0x66e3b8, 0x66e3c8); (0x6f2d88 + 8, 0x6f2d88 + 16); (cur, cur + 32); (odr, odr + 1); (0x66e418 + 8, 0x66e418 + 12);
                          (B + 32 * p, B + 32 * p + 32)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (HLn : length nws = (4 * Z.to_nat N)%nat) by (destruct KR as (L & _); exact L).
  assert (Hp : 0 <= p < N).
  { apply (probe_ins_range (Z.to_nat N) N ks odr (RGM.hash0 N odr) 1 p); [lia| | lia| exact PI].
    unfold RGM.hash0. apply land_mask_range; [lia| apply Z.mod_pos_bound; lia]. }
  unfold XR_iter.st_entry.
  assert (S0 : 0 <= swr) by (unfold RGM.rup8 in RU; Z.div_mod_to_equations; lia).
  call (reg_head fp gp tp s3 s10 F fc i g beg size swr odr); [lia| exact Hg| exact REC| exact RODR| lia| exact B8| exact S0| exact S8| lia| lia
        | exact AIN| exact RG| exact DO| exact SHC| exact MI|].
  replace (odr =? RGM.ODR_NONE) with false by (symmetry; apply Z.eqb_neq; unfold RGM.ODR_NONE; lia). cbv iota. unfold XR_iter.st_entry.
  call (reg_ind fp gp tp s3 s10 F fc i g odr B N ne p lend cur CEND ks nws); [lia| lia| eassumption| exact HO| exact PI| exact NG| exact HN| exact Hne| exact KF
        | eassumption| eassumption| eassumption| exact KR| exact HB0| exact HBT| exact BI| lia| exact BF| eassumption| eassumption| eassumption
        | eassumption| eassumption| exact SPlo| exact FPhi| eassumption| exact C0| lia| exact CE| exact LE| eassumption| exact AI| exact AFR| assumption|].
  unfold XR_iter.st_entry.
  lazymatch goal with KRx : keys_rep _ ?w (RGM.upd _ _ _) |- _ => assert (HLn' : length w = (4 * Z.to_nat N)%nat) by (destruct KRx as (L & _); exact L) end.
  assert (SHL : 0x7fffa000 <= 0x7fff8000 + beg / 8) by (Z.div_mod_to_equations; lia).
  assert (SHH : 0x7fff8000 + (beg + swr) / 8 <= 0x80171400) by (Z.div_mod_to_equations; lia).
  call (reg_poison fp gp tp s3 s10 F fc i g beg size swr); [lia| lia| lia| exact FPhi| eassumption| exact B0| exact B8| exact S8| exact Z1| exact RU| exact SW| exact BT
        | eassumption| eassumption| eassumption| eassumption| eassumption| assumption|].
  unfold XR_iter.st_entry.
  call (reg_addlist fp n gp tp s3 s10 F fc i g lend (cur + 16) CEND lsize first); [exact Hi| exact Hin| exact Hn| exact Hg| eassumption| eassumption| eassumption
        | eassumption| exact SPlo| exact FPhi| eassumption| lia| lia| exact CE| exact LE| eassumption| lia| lia
        | eassumption| exact LS1| exact LS2| assumption|].
  apply evt_done. do 19 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [replace (cur + 32) with (cur + 16 + 16) by lia; assumption|].
  split; [replace (cur + 32) with (cur + 16 + 16) by lia; assumption|].
  split; [assumption|]. split; [assumption|].
  split; [eassumption|]. split; [eassumption|]. split; [assumption| exact Hp].
Qed.
End IterW.
