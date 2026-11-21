(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import F_malloc_free F_malloc_enframe MallocBlocks MallocHINV MallocFacts_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocKit_A MallocKit_B MallocKit_B2 MallocModel_B MallocKit_B3 MallocFacts_Bpres F_mm_syscalls.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_free.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_free.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_free.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_free.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocKit_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocKit_B2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocModel_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocFacts_Bpres OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_mm_syscalls OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_free.F_ntf OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_free.F_free_C OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_free.F_free_K OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_free.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RMallocRep RMallocTree RMallocKit_B RMallocKit_B2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_get_meta RF_mm_syscalls.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocKit_B2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RMallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_get_meta OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_mm_syscalls.

Module RF_free_A.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import F_malloc_free F_malloc_fast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RMallocRep RMallocTree RMallocKit_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_get_meta.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RMallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_get_meta.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := unfold alloc_ceiling, UNIT, IB in *; lia.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import CeilWin.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma zx32_wz x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma meta_word_sc2 mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 5) 126 = 2 * m_sizeclass mr.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros (LI & FB & SCR & ML).
  assert (E : 126 = Z.ldiff (Z.ones 7) (Z.ones 1)) by reflexivity. rewrite E, land_ldiff_distr.
  rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  change (2^7) with 128. change (2^1) with 2. change (2^5) with 32. unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
  rewrite Z.div_add, (Z.div_small (m_last_idx mr)) by lia.
  replace (0 + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr)) with ((m_freeable mr + 2 * m_sizeclass mr) + m_maplen mr * 128) by lia.
  rewrite Z.mod_add, Z.mod_small by lia.
  replace (m_freeable mr + 2 * m_sizeclass mr) with (m_freeable mr + m_sizeclass mr * 2) by lia.
  rewrite Z.div_add, Z.div_small by lia. lia.
Qed.

Lemma meta_word_pg mr : mw_ok mr -> meta_word mr - meta_word mr mod 4096 = 4096 * m_maplen mr.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros (LI & FB & SCR & ML). unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
  rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

Definition rfhead_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st1 : mstate) (g : aptr) (idx li : Z) : machine_state -> Prop :=
  fun ms' => exists x1 x5 x6 x7 junk m',
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
                  (wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (li + 1) - 1))) (Z_to_bv 64 0x5a894) x5 x6 x7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x20898) fc None m' (seg_rom psegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells psegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rmrep st1 m'.

Lemma rfree_head3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
    (m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (b3 lo8 hi E rsv : Z),
  let po := snd p in
  let idx := Z.land b3 31 in
  let mr := get_meta_rec st g in
  let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
  rmrep st m0 -> mem_inv psegs m0 -> ticks_ok st ->
  stk psegs m0 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  rw_cells psegs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono psegs m m0 ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  meta_slot st g ->
  cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  0 <= b3 < 256 ->
  r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
  0 <= rsv <= E - (r_base r + po) -> bytes_at psegs m0 (E - rsv) [b8 0] -> bytes_at psegs m0 E [b8 0] ->
  (forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
  evt psegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
                (Z_to_bv 64 E) a3 (wz rsv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20848) fc None m0 (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until rsv. intros po idx mr st1 MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL HK3 HK2 HK1 LI FBL SC ML B3 ELO EHI RSV RB0r RE0 HCLR.
  pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (IDX : 0 <= idx < 32).
  { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  unfold UNIT, IB, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  pose proof (munch_refl [(r_base r + po - 3, r_base r + po)]%Z m0) as MU. pose proof (wmono_refl psegs m0) as WM.
  pose proof (bytes_at_read psegs m0 _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. cbn [firstn skipn Z.to_nat] in RDr. rewrite Z.add_0_r in RDr.
  pose proof (bytes_at_read psegs m0 _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. cbn [firstn skipn Z.to_nat] in RDe. rewrite Z.add_0_r in RDe.
  st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
  st1. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
  st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
  change (Z_to_bv 64 E) with (wa E).
  st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
  st1. st1. st1. st1. st1. st1.
  rewrite (unsigned_lit idx) by lia. rewrite sllw1_word' by lia. rewrite (wz_unsigned (meta_word mr)) by (unfold meta_word; lia).
  pose proof MR1 as (_ & _ & _ & _ & _ & SH1). destruct (SH1 (fst p) r Hr Hk) as [HWr _]. clear SH1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (SOK3 : store_ok psegs mX (wa (bv_unsigned a0 + -3)) 1 = true)
      by (replace (bv_unsigned a0 + -3) with (r_base r + (po - 3)) by lia; apply (wr_at_store_ok psegs mX _ _ (po - 3) 1 HWr); cbn; lia) end.
  st1.
  pose proof (rmrep_wr8 st _ (aadd p (-3)) 255 r MR1 TK Hr Hk ltac:(cbn; lia)
                ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR2.
  cbn [aadd snd] in MR2. fold po in MR2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -3))) [b8 255])
      by (rewrite le1_neg1; f_equal; unfold wa; f_equal; lia) end.
  store_done.
  pose proof (ticks_ok_wr8 st (aadd p (-3)) 255 TK) as TK2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof MR2 as (_ & _ & _ & _ & _ & SH2); destruct (SH2 (fst p) r Hr Hk) as [HWr2 _]; clear SH2;
    assert (SOK2 : store_ok psegs mX (wa (bv_unsigned a0 + -2)) 2 = true)
      by (replace (bv_unsigned a0 + -2) with (r_base r + (po - 2)) by lia; apply (wr_at_store_ok psegs mX _ _ (po - 2) 2 HWr2); cbn; lia) end.
  st1.
  pose proof (rmrep_wr16 _ _ (aadd p (-2)) 0 r MR2 TK2 Hr Hk ltac:(cbn; lia) ltac:(cbn; lia)
                ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR3.
  cbn [aadd snd] in MR3. fold po in MR3. fold st1 in MR3.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -2))) (le2 (wz 0)))
      by (f_equal; unfold wa; f_equal; lia) end.
  store_done. clear MR2 TK2 HWr HWr2.
  st1. rewrite (all_word (meta_word mr)) by (unfold meta_word; lia).
  replace (meta_word mr mod 32) with (m_last_idx mr) by (unfold meta_word; Z.div_mod_to_equations; lia).
  st1.
  apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
  2:{ cbn [ivs_covered]. split; [|exact I].
      intros x Hx. right. right. exists (fst p), r.
      assert (CASES : x - r_base r = po - 3 \/ x - r_base r = po - 2 \/ x - r_base r = po - 1) by lia.
      destruct CASES as [E1|[E1|E1]]; [exists b3| exists lo8| exists hi]; rewrite E1; (split; [exact Hr|]); (split; [exact Hk|]); (split; [lia|]); assumption. }
  apply evt_done. unfold rfhead_post.
  assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
  do 6 eexists.
  split; [reflexivity|].
  split; [eapply rpres_except_trans; [exact PE0| exact MU]|]. split; [exact WM0|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. exact MR3.
Qed.

Lemma rfree_head2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
    (m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (base : aptr) (b3 lo8 hi r32 : Z),
  let po := snd p in
  let idx := Z.land b3 31 in
  let mr := get_meta_rec st g in
  let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
  let stride := get_stride mr in
  let E := conc st base + UNIT + stride * idx + stride - IB in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  rmrep st m0 -> mem_inv psegs m0 -> ticks_ok st ->
  stk psegs m0 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  rw_cells psegs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono psegs m m0 ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  meta_slot st g -> m_mem mr = Some base -> fst base = fst p -> 0 <= snd base ->
  cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
  0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  0 <= b3 < 256 -> idx <= m_last_idx mr ->
  UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at psegs m0 (E - 4) (le4 (wz r32)) /\ bytes_at psegs m0 (E - 5) [b8 0]) ->
  rsv <= E - (r_base r + po) -> bytes_at psegs m0 (E - rsv) [b8 0] -> bytes_at psegs m0 E [b8 0] ->
  (forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
  evt psegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
                (Z_to_bv 64 stride) (wz b3) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20800) fc None m0 (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until r32. intros po idx mr st1 stride E rsv0 rsv MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL Hmem FB SB0 HK3 HK2 HK1
         AV FRD LI FBL SC ML B3 Hidx S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
  pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (IDX : 0 <= idx < 32).
  { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
  assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  unfold UNIT, IB, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
  pose proof (rmrep_meta_chunk st m0 g MR1 MSL) as MM.
  fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  st1. st1. st1. st1. st1. st1. st1. cbn [oconc].
  replace (conc st base + stride + stride * idx + 12) with E by (unfold E; lia).
  fold rsv0.
  st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
  -
    replace (Z_to_bv 64 rsv0) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).
    assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
    subst mr.
    eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
      [exact MR1| exact MI| exact TK| exact ST| unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
      | exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
  -
    destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
    pose proof (bytes_at_read psegs m0 _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RD4.
    cbn [skipn Z.to_nat] in RD4. rewrite firstn_all2 in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
    replace (E - 4) with (conc st base + stride + stride * idx + 8) in RD4 by (unfold E; lia).
    pose proof (bytes_at_read psegs m0 _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. cbn [firstn skipn Z.to_nat] in RD5. rewrite Z.add_0_r in RD5.
    replace (E - 5) with (conc st base + stride + stride * idx + 7) in RD5 by (unfold E; lia).
    st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }
    st1.
    rewrite zx32_wz by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }
    st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
    replace (wz r32) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
    assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
    subst mr.
    eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
      [exact MR1| exact MI| exact TK| exact ST| unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
      | exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
Qed.

Lemma rfree_head : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (lo : Z) st (p : aptr) r g gh ar (b3 lo8 hi r32 : Z),
  let sh := get_shadow st (fst p) in
  let po := snd p in
  let off16 := lo8 + 256 * hi in
  let idx := Z.land b3 31 in
  let base := aadd p (- (UNIT * off16) - UNIT) in
  let mr := get_meta_rec st g in
  let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
  let stride := get_stride mr in
  let E := conc st base + UNIT + stride * idx + stride - IB in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  rmrep st m -> mem_inv psegs m -> ticks_ok st ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
  16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
  cell_read sh (po - 2) = Known lo8 -> cell_read sh (po - 1) = Known hi ->
  (s_groups st) !! base = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
  m_mem mr = Some base ->
  (s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
  0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
  (m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
  (48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
  (m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->
  (m_maplen mr = 0 \/ m_last_idx mr <> 0 -> m_sizeclass mr < 48) ->
  UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at psegs m (E - 4) (le4 (wz r32)) /\ bytes_at psegs m (E - 5) [b8 0]) ->
  rsv <= E - (r_base r + po) -> bytes_at psegs m (E - rsv) [b8 0] -> bytes_at psegs m E [b8 0] ->
  (forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
  c_init_done (ctx st) <> 0 ->
  evt psegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until r32. intros sh po off16 idx base mr st1 stride E rsv0 rsv MR MI TK ST LO SLO Hr Hk HP AL P16 PLO PHI HK4 HK3 HK2 HK1 Hgh Hg MSL G0 Hmem Har Hchk
         AV FRD SE LI FBL SC ML Hidx Hav Hfr Hsc Hsc63 Hml SC48 S16 ELO EHI BIG RSVLE RB0r RE0 HCLR INI.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MUs.
  pose proof (wmono_refl psegs m) as WM.
  assert (IDX : 0 <= idx < 32).
  { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) HK3) as [_ B3].
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  assert (FB : fst base = fst p) by reflexivity.
  assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
  assert (SB0 : 0 <= snd base) by (unfold base; cbn; unfold UNIT; lia).
  revert BIG RB0r RE0.
  unfold rfree_entry, UNIT, IB, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. intros BIG RB0r RE0.
  st1. if_cases K0; zify_cond K0. { exfalso. lia. }
  carve_frame 48%nat ST.
  st1. st1. st1. st1. st1. st1. st1.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM |]; intros l h [E1|[]]; inversion E1; subst; unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia) end.
  eapply evt_cut.
  { eapply rget_meta_spec with (st := st) (p := p) (r := r) (g := g) (gh := gh) (ar := ar) (b3 := b3) (lo := lo8) (hi := hi).
    all: try eassumption. all: try lia. }
  intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
  replace (ret_pc (Z_to_bv 64 0x207b8)) with (Z_to_bv 64 0x207b8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (rmrep_meta_chunk st mX g MR1 MSL) as MM;
    destruct (rmrep_shadow_read st mX (fst p) r (po - 3) b3 MR1 Hr Hk ltac:(lia) HK3) as [R3 _] end.
  fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  replace (r_base r + (po - 3)) with (bv_unsigned a0 + -3) in R3 by lia.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (MW : mw_ok mr) by (unfold mw_ok; lia).
  pose proof (meta_word_range mr MW) as MWR. pose proof (meta_word_maplen mr MW) as MW12.
  pose proof (meta_word_last_idx mr MW) as MW31. pose proof (meta_word_sc2 mr MW) as MWS. pose proof (meta_word_pg mr MW) as MWP.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (K2 : forall a4v a5v a6v, evt psegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR (Z_to_bv 64 0x207b8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
                (Z_to_bv 64 stride) (wz b3) a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20800) fc None mX (seg_rom psegs))) end.
  { intros a4v a5v a6v.
    lazymatch type of MUs with munch ?W _ _ => assert (DJ : forall A n, A + n <= lo -> disjoint_from W A n) by (intros A n HA; cbn; lia) end.
    lazymatch type of MUs with munch ?W m ?mY =>
      assert (PE0 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m mY)
        by (apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp)) W); [exact MUs| exact WM|];
            cbn [ivs_covered]; split; [|exact I]; intros x Hx; apply rfree_fp_stack; lia) end.
    subst rsv rsv0 E stride mr.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    eapply (rfree_head2 ra sp gp tp t0 t1 t2 s0 s1 a0 a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ F fc m mX _ lo st p r g base b3 lo8 hi r32) end;
      [exact MR1| assumption| exact TK| exact ST| ulia| ulia| exact FR| exact PE0| exact WM| exact Hr| exact Hk| exact HP| exact AL| ulia| ulia
      | exact MSL| exact Hmem| exact FB| exact SB0| exact HK3| exact HK2| exact HK1| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia
      | intros Hb3; destruct (BIG Hb3) as (X1 & X2 & X3 & X4); split; [exact X1|]; split; [exact X2|]; split;
          (eapply bytes_at_transport; [eassumption| exact MUs| apply DJ; cbn; try rewrite length_le4; ulia])
      | ulia
      | exact RB0r
      | exact RE0
      | exact HCLR]. }
  st1. st1. st1. st1. fold idx. rewrite MW12.
  assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (KS : forall a2v a4v, (m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
    evt psegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR (Z_to_bv 64 0x207b8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 gw (wz (meta_word mr))
                a2v (wz b3) a4v ga5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x207e4) fc None mX (seg_rom psegs))) end.
  { intros a2v a4v COND. specialize (SC48 COND).
    assert (STR : stride = 16 * size_class (m_sizeclass mr)).
    { unfold stride, get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
      rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
    assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    st1. st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite MWS. st1. st1.
    replace (77690 + m_sizeclass mr * 2) with (77690 + 2 * m_sizeclass mr) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (RS' : ov_read_bytes psegs mX (Z_to_bv 64 (77690 + 2 * m_sizeclass mr)) 2 = Some (le2 (wz (size_class (m_sizeclass mr))))) end.
    { replace (Z_to_bv 64 (77690 + 2 * m_sizeclass mr)) with (wa (RSIZE_CLASSES + 2 * m_sizeclass mr)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
      apply rsize_classes_read; [assumption| lia]. }
    pose proof (size_class_range (m_sizeclass mr) ltac:(lia)) as SZ.
    st1. try rewrite (Z.mod_small (size_class (m_sizeclass mr))) by lia.
    st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (Z_to_bv 64 (size_class (m_sizeclass mr) * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
    rewrite Egw. apply K2. }
  st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  - apply KS. left. exact Km.
  -
    st1. rewrite MW31. st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
    + apply KS. right. exact Kl.
    +
      st1. st1. rewrite land_pgmask by lia. rewrite MWP. st1. st1.
      replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 stride).
      2:{ unfold stride, get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
      rewrite Egw. apply K2.
Qed.
End WithCeiling0.
End RF_free_A.


Module RF_free_B.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import F_malloc_free F_malloc_fast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RMallocRep RMallocTree RMallocKit_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_get_meta.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RMallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_get_meta.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rfree_fp_meta0 : forall st st0 m lo sp q a, rmrep st m -> meta_slot st q -> s_regions st0 = s_regions st ->
  conc st q <= a < conc st q + 40 -> rfree_fp st0 lo sp a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st st0 m lo sp q a MR (ar & arr & k & Har & Hk & Eq) ER Ha. pose proof MR as (WF & _).
  destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
  pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  eapply rfree_fp_region; [rewrite ER; exact Hra | exact NK | lia].
Qed.

Definition rftriv_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (C : Z -> Prop) (m : word -> option byte) (st' : mstate) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ rpres_except C m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rmrep st' m'.

Lemma rfree_triv : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st0 st : mstate) (g : aptr) (idx : Z),
  let mr := get_meta_rec st g in
  let st' := upd_meta g (m_set_freed (m_freed mr + bit idx)) st in
  rmrep st m -> mem_inv psegs m -> meta_slot st g ->
  s_regions st = s_regions st0 -> s_areas st = s_areas st0 ->
  0 <= m_freed mr < 2^32 -> 0 <= m_avail mr < 2^32 -> 0 <= m_last_idx mr < 32 -> 0 <= idx <= m_last_idx mr ->
  Z.testbit (m_freed mr) idx = false -> Z.testbit (m_avail mr) idx = false ->
  m_freed mr <> 0 -> Z.lor (m_freed mr) (m_avail mr) + bit idx <> mask_upto (m_last_idx mr) ->
  rw_cells psegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk psegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt psegs (rftriv_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (rfree_fp st0 lo (bv_unsigned sp)) m st')
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
               (wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (m_last_idx mr + 1) - 1))) (Z_to_bv 64 0x5a894) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20898) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until idx. intros mr st' MR MI MSL ER EA HF HA HL HI TF TA Hfz Hall FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
  pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
  clearbody gw.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
  pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
  pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
  unfold RNEED_LOCKS, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  step. step. rewrite !sx32_wz_sxv by lia.
  step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
  rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
  pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.
  step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
  rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
  rewrite (Z.land_comm _ (sxv (2 ^ idx))).
  rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).
  step. if_true.
  st1.
  step. if_cases K2; zify_cond K2.
  { exfalso. apply Hfz. apply (proj1 (sxv_zero (m_freed mr) ltac:(lia))). first [exact K2 | rewrite wz_unsigned in K2 by assumption; exact K2]. }
  clear K2.
  step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
  rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
  rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
  pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
  step. if_cases K3; zify_cond K3.
  { exfalso. apply Hall. unfold bit, mask_upto. apply (proj1 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    rewrite !wz_unsigned in K3 by apply sxv_range. exact K3. }
  clear K3 RSUM.
  step. rewrite (wz_unsigned (sxv (2 ^ idx))), (wz_unsigned (sxv (m_freed mr))) by assumption.
  rewrite (Z.add_comm (sxv (m_freed mr)) (sxv (2 ^ idx))). rewrite addw_word.
  step. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
  clear K4 RL.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (MR' : rmrep st' mX) end.
  { unfold st'. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WM |].
    rewrite HG in MM.
    eapply rw_cells_congr; [ | | | exact MM].
    - unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
      unfold bit. rewrite (free_store_val (m_freed mr) idx) by (assumption || lia). reflexivity.
    - reflexivity.
    - cbn. tauto. }
  clear MUg MM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z mX) as MUs;
    pose proof (wmono_refl psegs mX) as WMs end.
  step. step. step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st' mX)
      by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia]) end.
  clear MR' MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU; [|exact WM|].
  2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
      - intros x Hx. apply rfree_fp_stack. lia.
      - intros x Hx. eapply (rfree_fp_meta0 st st0 m lo (bv_unsigned sp) g); [exact MR | exact MSL | symmetry; exact ER | lia]. }
  finish.
Qed.

Lemma rfree_tocall : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate) (g : aptr) (idx : Z),
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv psegs m -> meta_slot st g ->
  0 <= m_freed mr < 2^32 -> 0 <= m_avail mr < 2^32 -> 0 <= m_last_idx mr < 32 -> 0 <= idx <= m_last_idx mr ->
  Z.testbit (m_freed mr) idx = false -> Z.testbit (m_avail mr) idx = false ->
  (m_freed mr = 0 \/ Z.lor (m_freed mr) (m_avail mr) + bit idx = mask_upto (m_last_idx mr)) ->
  evt psegs (fun ms' => exists x2 x3 x4 x5 x6 x7,
       ms' = MS (mkR (Z_to_bv 64 0x20908) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
                     (Z_to_bv 64 (conc st g)) (Z_to_bv 64 idx) x2 x3 x4 x5 x6 x7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20a70) fc None m (seg_rom psegs))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
               (wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (m_last_idx mr + 1) - 1))) (Z_to_bv 64 0x5a894) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20898) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until idx. intros mr MR MI MSL HF HA HL HI TF TA HNT.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _).
  pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
  replace (Z_to_bv 64 (conc st g)) with gw by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  clearbody gw.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
  pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
  pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
  unfold RNEED_LOCKS, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  step. step. rewrite !sx32_wz_sxv by lia.
  step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
  rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
  pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.
  step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
  rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
  rewrite (Z.land_comm _ (sxv (2 ^ idx))).
  rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).
  step. if_true. st1.
  step. if_cases K2; zify_cond K2.
  -
    st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
    st1. st1.
    apply evt_done. do 6 eexists. reflexivity.
  -
    step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
    rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
    rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
    pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
    step. if_cases K3; zify_cond K3.
    + st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
      st1. st1.
      apply evt_done. do 6 eexists. reflexivity.
    + exfalso. destruct HNT as [Hz|Hall].
      * apply K2. rewrite ?wz_unsigned by apply sxv_range. rewrite Hz. reflexivity.
      * apply K3. rewrite ?wz_unsigned by apply sxv_range.
        apply (proj2 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
        unfold bit, mask_upto in Hall. exact Hall.
Qed.
End WithCeiling0.
End RF_free_B.


Module RF_free_C.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_malloc_free.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_free.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_malloc_free OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_free.F_free_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RMallocRep RMallocTree RMallocKit_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_get_meta RF_mm_syscalls.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RMallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_get_meta OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_mm_syscalls.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition rffin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (W : list (Z * Z)) (m : word -> option byte) (st : mstate) (errv : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch W m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st m'.

Lemma rfree_fin0 : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv psegs m ->
  rw_cells psegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  stk psegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt psegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m st errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz 0) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20908) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until errv. intros TP MR MI FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
  unfold RMLOCK, RNEED_LOCKS, RATP, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. subst tp.
  rewrite (unsigned_lit 238736) in ERR by lia. change (238736 + -164) with 238572 in ERR.
  st1. st1. st1. st1.
  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x2091c)) with (Z_to_bv 64 0x2091c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  rewrite (unsigned_lit 238736) by lia. change (238736 + -164) with 238572. exact ERR.
Qed.

Definition rfmun_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (junk : list byte) (m : word -> option byte) (st : mstate) (errv bw lw : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x20938) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw bw lw a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 (errno_addr tp)) (sx32 errv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmunmap_entry) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells psegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st m'.

Lemma rfree_tomunmap : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo len : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv psegs m -> 0 < len < 2^64 ->
  rw_cells psegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  stk psegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt psegs (rfmun_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo junk m st errv bw (wz len))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz len) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20908) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until errv. intros TP MR MI HL FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
  unfold RMLOCK, RNEED_LOCKS, RATP, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. subst tp.
  rewrite (unsigned_lit 238736) in ERR by lia. change (238736 + -164) with 238572 in ERR.
  st1. st1. st1. st1.
  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x2091c)) with (Z_to_bv 64 0x2091c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  st1. if_cases K; zify_cond K. { exfalso. rewrite wz_unsigned in K by lia. lia. }
  st1. st1. st1. st1.
  replace (ret_pc (Z_to_bv 64 0x20924)) with (Z_to_bv 64 0x20924) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia]) end.
  apply evt_done. unfold rfmun_post. do 14 eexists. split; [rewrite (unsigned_lit 238736) by lia; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
  split; [rewrite (unsigned_lit 238736) by lia; change (238736 + -164) with 238572; exact ERR| exact MR2].
Qed.

Lemma rerrno_avoids_repfoot : forall st m a, rmrep st m -> 238572 <= a < 238576 -> ~ rrepfoot st a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m a MR Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
  - unfold RCTX in C. lia.
  - unfold RMLOCK in C. lia.
  - unfold RNEED_LOCKS in C. lia.
  - unfold RPAGE_SIZE in C. lia.
  - destruct C as (ak & ar & Hak & Hin).
    destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len ra)). lia.
  - destruct C as (b & gh & Hb & Hin).
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len rb)). lia.
  - destruct C as (rid & r & v & Hr & Hk & Hin & HC).
    destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. lia.
  - unfold RGOT_SSP in C. lia.
  - unfold RSSP_GUARD in C. lia.
Qed.

Lemma rmrep_transport_frame_errno : forall st m m' (sp : Z),
  rmrep st m -> munch [(sp - 48, sp); (238572, 238576)]%Z m m' -> wmono psegs m m' -> alloc_ceiling <= sp - 48 -> rmrep st m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m m' sp MR MU WM HS. eapply rmrep_transport_unowned; [exact MR | exact MU | exact WM |].
  apply ivs_avoid_cons; [| apply ivs_avoid_cons; [| apply ivs_avoid_nil]].
  - intros a Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in HS; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
    intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    + unfold RCTX in C. lia.
    + unfold RMLOCK in C. lia.
    + unfold RNEED_LOCKS in C. lia.
    + unfold RPAGE_SIZE in C. lia.
    + destruct C as (ak & ar & Hak & Hin).
      destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
    + destruct C as (b & gh & Hb & Hin).
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
    + destruct C as (rid & r & v & Hr & Hk & Hin & HC).
      destruct (WR _ _ Hr) as (_ & _ & _ & RBC & _). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
    + unfold RGOT_SSP in C. lia.
    + unfold RSSP_GUARD in C. lia.
  - intros a Ha. eapply rerrno_avoids_repfoot; [exact MR | exact Ha].
Qed.

Lemma rfree_fin1 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv psegs m ->
  rw_cells psegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  le4 ew = le4 errv ->
  rw_cells psegs m (errno_addr tp) [C4 e'] ->
  stk psegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt psegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp); (238572, 238576)]%Z m st errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (errno_addr tp)) ew s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20938) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until errv. intros TP MR MI FR EW ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (238572, 238576)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  unfold RATP, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. subst tp.
  rewrite (unsigned_lit 238736) in ERR by lia. change (238736 + -164) with 238572 in ERR.
  rewrite (unsigned_lit 238736) by lia. change (238736 + -164) with 238572.
  st1.
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX) by (eapply (rmrep_transport_frame_errno st m mX (bv_unsigned sp)); [exact MR | exact MU | exact WM | unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  rewrite (unsigned_lit 238736) by lia. change (238736 + -164) with 238572.
  eapply rw_cells_congr; [| | | exact ERR]; [cbn [cells_bytes cbytes app]; rewrite EW; reflexivity| reflexivity| cbn; tauto].
Qed.
End WithCeiling0.
End RF_free_C.


Module RF_ntf_E.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_malloc_free F_malloc_fast MallocModel_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocModel_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocModel_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocKit_A3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_malloc_free OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_malloc_fast OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocModel_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocModel_B.F_ntf_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocModel_B.F_ntf_C OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocKit_A3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RMallocRep RMallocTree RMallocKit_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RMallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RF_ntf_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame psegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write psegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write psegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv psegs mX |- _ =>
      apply (mem_inv_store psegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition rat9c_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc : Z) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists a3 a4 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x20c34) fc None m' (seg_rom psegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells psegs m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

Lemma rntf_deqself : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g : aptr) (sc lo : Z),
  rmrep st m -> mem_inv psegs m -> meta_slot st g -> 0 <= sc < 48 ->
  m_next (get_meta_rec st g) = Some g ->
  rw_cells psegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
               (deq_mid (LActive sc) g st) g sc fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20c2c) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros MR MI MSL SC GN FR FRL ST LO LOLE.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  unfold RCTX, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  st1.
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok psegs _ _ (actives st) sc (Z_to_bv 64 (370576 + sc * 8 + 80)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc None MR SC) as MR2; unfold RCTX in MR2 end.
  clear ACTS.
  rraw_store_finish (370576 + 80 + 8 * sc) (le8 (pw st None)) FR ST MU WM SOK.
  assert (EQ : deq_mid (LActive sc) g st = set_active sc None st).
  { unfold deq_mid. rewrite GN, optr_eqb_refl. reflexivity. }
  rewrite EQ.
  apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
  split.
  { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. repeat split; intros x Hx.
    + apply rfree_fp_stack. lia.
    + apply rfree_fp_ctx. unfold RCTX. lia. }
  split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.

Lemma rntf_deq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g nx pv : aptr) (sc lo : Z),
  rmrep st m -> mem_inv psegs m -> meta_slot st g -> 0 <= sc < 48 ->
  m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv ->
  nx <> g -> pv <> g -> meta_slot st nx -> meta_slot st pv ->
  (active st sc = None \/ exists q, active st sc = Some q /\ meta_slot st q) ->
  a2 = pw st (active st sc) ->
  rw_cells psegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
               (deq_mid (LActive sc) g st) g sc fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20ba8) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros MR MI MSL SC GN GP NEn NEp MSn MSp ACT HA2 FR FRL ST LO LOLE.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  pose proof (rmeta_slot_bounds st m nx MR MSn) as NB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  unfold RCTX, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (370576, 370576 + 928)]%Z m) as MU.
  rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. clear CH.
  rmeta_open (conc st pv) MUp WMp.
  rmeta_chunk MR MSp CH.
  st1.
  rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 GP GN.
  set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
  assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
  assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).
  rmeta_chunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. st1. clear CH.
  rmeta_open (conc st nx) MUn WMn.
  rmeta_chunk MR1 MSn1 CH.
  st1.
  rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 GP GN.
  set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
  assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
  pose proof (rmrep_active_read st2 _ sc (wa (RCTX + 80 + 8 * sc)) MR2 SC eq_refl) as RDA. unfold RCTX in RDA.
  replace (wa (370576 + 80 + 8 * sc)) with (Z_to_bv 64 (370576 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
  assert (HACT : active st2 sc = active st sc) by reflexivity. rewrite HACT in RDA.
  assert (HPW : forall q, pw st2 q = pw st q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
  st1. clear RDA.
  assert (EQmid : deq_mid (LActive sc) g st =
                  if optr_eqb (active st sc) (Some g) then set_active sc (Some nx) st2 else st2).
  { unfold deq_mid. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head].
    rewrite !upd_meta_put. fold st1. fold st2. rewrite HACT. reflexivity. }
  st1. if_cases K; zify_cond K.
  -
    assert (HA : optr_eqb (active st sc) (Some g) = false).
    { destruct (active st sc) as [q|]; [|reflexivity]. cbn [optr_eqb]. apply aptr_eqb_neq. intros ->. apply K.
      unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
    rewrite HA in EQmid. rewrite <- EQmid in MR2. subst a2.
    apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSn | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
  -
    assert (HA : active st sc = Some g).
    { destruct ACT as [A0|(q & Aq & MSq)].
      - exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
      - rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
        pose proof (rmeta_slot_bounds st m q MR MSq) as QB. rewrite ?unsigned_lit in K by lia.
        rewrite (rconc_meta_inj st m g q MR MSL MSq ltac:(lia)). reflexivity. }
    rewrite HA, optr_eqb_refl in EQmid.
    rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
    unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite GN, GP in CH. cbn [oconc] in CH.
    st1. clear CH. st1.
    pose proof MR2 as (_ & (_ & ACTS & _) & _).
    pose proof (u64arr_store_ok psegs _ _ (actives st2) sc (Z_to_bv 64 (370576 + sc * 8 + 80)) ACTS
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
    clear ACTS.
    rraw_store_finish (370576 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) FR ST MU WM SOK.
    rewrite <- EQmid in MR3. subst a2.
    apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSn | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR3].
Qed.

Lemma land_mod_pow2 a b n : 0 <= n -> (Z.land a b) mod 2^n = Z.land (a mod 2^n) (b mod 2^n).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Hn. rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
  destruct (Z.testbit a k), (Z.testbit b k), (Z.testbit (Z.ones n) k); reflexivity.
Qed.

Lemma act_mask_le4 f y z : 0 <= f < 2^32 -> 1 <= y <= 2^32 -> z mod 2^32 = (y - 1) mod 2^32 ->
  le4 (Z_to_bv 64 (Z.land (sxv f) (bv_unsigned (Z_to_bv 64 z)))) = le4 (wz (Z.land f (y - 1))).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Hf Hy Hz. apply le4_congr.
  pose proof (sxv_range f). rewrite (unsigned_lit_wrap z). pose proof (Z.mod_pos_bound z (2^64) ltac:(lia)).
  assert (R1 : 0 <= Z.land (sxv f) (z mod 2^64) < 2^64) by (apply land_range64; lia).
  assert (R2 : 0 <= Z.land f (y - 1) < 2^32).
  { split; [apply Z.land_nonneg; lia|]. pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)). lia. }
  rewrite unsigned_lit, wz_unsigned by lia.
  rewrite land_mod_pow2, sxv_mod32, mod64_mod32, Hz by lia.
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

Definition rat00_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x20c98) fc None m' (seg_rom psegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells psegs m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

Lemma rntf_postdeq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) stm (g : aptr) (sc lo : Z) (an : bool),
  let st1 := upd_meta g clr_links stm in
  rmrep stm m -> mem_inv psegs m -> meta_slot stm g -> 0 <= sc < 48 ->
  (if an then bv_unsigned a2 = conc stm g else bv_unsigned a2 <> conc stm g) ->
  (an = true -> forall a, active st1 sc = Some a ->
     meta_slot st1 a /\ a <> g /\ m_avail (get_meta_rec st1 a) = 0 /\ 0 <= m_freed (get_meta_rec st1 a) < 2^32
     /\ exists ba gh, m_mem (get_meta_rec st1 a) = Some ba /\ (s_groups st1) !! ba = Some gh /\ 0 <= g_active_idx gh <= 31) ->
  rw_cells psegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rat00_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 F fc lo stm m (pd_st an st1 sc) g fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc stm g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20c34) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until an. intros st1 MR MI MSL SC HA2 HACT FR FRL ST LO LOLE.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ a2) as A2R. change (bv_modulus 64) with (2^64) in A2R.
  pose proof (rmeta_slot_bounds stm m g MR MSL) as GB.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  unfold RCTX, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  pose proof (munch_refl [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m) as MU.
  rmeta_open (conc stm g) MUg WMg.
  rmeta_chunk MR MSL CH.
  st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st1 mX)
      by (unfold st1; rewrite upd_meta_put; eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WMg |];
          eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | first [ cbn [cells_wf cell_wf meta_cells ctx_head_cells ctx_tail_cells rctx_head_cells]; solve [repeat split] | cbn; tauto ]]);
    clear MUg WMg CH
  end.
  assert (COV : forall m', munch [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m m' -> wmono psegs m m' ->
                 rpres_except (rfree_fp stm lo (bv_unsigned sp)) m m').
  { intros m' MU' WM'. apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU'; [exact MU'|exact WM'|].
    cbn [ivs_covered]. repeat split; intros x Hx; (eapply rfree_fp_meta; [exact MR | exact MSL | lia]). }
  assert (MSg1 : meta_slot st1 g) by (unfold st1; rewrite upd_meta_put; apply meta_slot_put_meta; exact MSL).
  assert (Hconc : forall q, conc st1 q = conc stm q) by (intros; reflexivity).
  st1. if_cases K; zify_cond K.
  -
    destruct an. { exfalso. apply K. rewrite ?unsigned_lit by lia. lia. }
    cbn [pd_st].
    apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR1].
  -
    destruct an. 2:{ exfalso. apply HA2. rewrite ?unsigned_lit in K by lia. lia. }
    cbn [pd_st].
    pose proof (rmrep_active_read st1 _ sc (wa (RCTX + 80 + 8 * sc)) MR1 SC eq_refl) as RDA. unfold RCTX in RDA.
    assert (HPW : forall q, pw st1 q = pw stm q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
    replace (wa (370576 + 80 + 8 * sc)) with (Z_to_bv 64 (370576 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
    st1. clear RDA.
    st1. destruct (active st1 sc) as [a|] eqn:HA1.
    + destruct (HACT eq_refl a eq_refl) as (MSa & NEa & AV0 & FRR & ba & gh & Hmem & Hgh & AI).
      pose proof (rmeta_slot_bounds st1 _ a MR1 MSa) as AB. rewrite !Hconc in AB.
      munch_grow MU (conc stm a, conc stm a + 40).
      unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
      rmeta_chunk MR1 MSa CHa. rewrite AV0, Hmem in CHa. cbn [oconc] in CHa.
      st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. rewrite ?unsigned_lit by lia. reflexivity. } clear K3.
      st1.
      destruct (rmrep_group_read st1 _ ba gh MR1 Hgh) as [_ (w8 & RD8 & Hw8)].
      rewrite Hconc in RD8.
      st1.
      pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
      assert (MOD8 : bv_unsigned w8 mod 32 = g_active_idx gh).
      { rewrite <- Hw8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }
      st1. st1. unfold zxb. rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite MOD8.
      set (y := 2 ^ (g_active_idx gh + 1)).
      st1. st1. rewrite negw_word.
      clear CHa. rmeta_open (conc stm a) MUa WMa.
      rmeta_chunk MR1 MSa CHa. rewrite Hmem in CHa. cbn [oconc] in CHa.
      pose proof (sxv_range (m_freed (get_meta_rec st1 a))) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range y) as RY1.
      st1. rewrite sx32_wz_sxv by lia.
      st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
      assert (AMO : amo_aligned AW (Z_to_bv 64 (conc stm a + 28)) = true).
      { apply amo_aligned_intro; [lia|]. Z.div_mod_to_equations. lia. }
      amo_step AMO. rewrite ?sx32_wz_sxv by lia.
      st1. if_false.
      amo_step AMO.
      st1. if_false.
      st1. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. st1. if_false.
      st1. st1. st1.
      set (f := m_freed (get_meta_rec st1 a)) in *.
      assert (AI31 : Z.land (g_active_idx gh) 31 = g_active_idx gh).
      { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
      assert (ACT : act_of st1 a = y - 1).
      { unfold act_of. rewrite Hmem. cbn [default]. unfold group_active_idx, get_group. rewrite Hgh, AI31. unfold mask_upto, y. reflexivity. }
      assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
      assert (Y1 : 1 <= y <= 2^32).
      { unfold y. split; [pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh + 1)); lia| apply Z.pow_le_mono_r; lia]. }
      pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
      pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
      pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
        assert (MR2 : rmrep (act_st st1 a (act_of st1 a)) mX)
      end.
      { unfold act_st. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [exact MR1 | exact MSa | exact MUa | exact WMa |].
        eapply rw_cells_congr; [ | | | exact CHa]; [ | reflexivity | first [ cbn [cells_wf cell_wf meta_cells ctx_head_cells ctx_tail_cells rctx_head_cells]; solve [repeat split] | cbn; tauto ]].
        unfold meta_cells. unfold pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen oconc].
        fold f. rewrite E1. rewrite (act_mask_le4 f y) ; [| lia | exact Y1 | rewrite <- Zplus_mod_idemp_l, swrap32_mod32, Zplus_mod_idemp_l; reflexivity].
        rewrite !le4_sxv by lia. rewrite Hmem. cbn [oconc]. reflexivity. }
      clear MUa WMa CHa.
      apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
      split. { apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
               cbn [ivs_covered]. repeat split; intros x Hx.
               - eapply rfree_fp_meta; [exact MR | exact MSL | lia].
               - eapply rfree_fp_meta; [exact MR | exact MSa | lia].
               - eapply rfree_fp_meta; [exact MR | exact MSL | lia]. }
      split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
      unfold pd_st. rewrite ?HA1. exact MR2.
    +
      unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. rewrite ?unsigned_lit by lia. reflexivity. } clear K2.
      apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
      split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
      unfold pd_st. rewrite ?HA1. exact MR1.
Qed.
End WithCeiling0.
End RF_ntf_E.

Module RF_ntf_D.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_malloc_free F_malloc_fast MallocModel_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocModel_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocKit_A3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_malloc_free OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_malloc_fast OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocModel_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocModel_B.F_ntf_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocKit_A3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RMallocRep RMallocTree RMallocKit_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RMallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RF_ntf_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_free.RF_ntf_E.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma testbit_false_ge a n : 0 <= a < 2^n -> 0 <= n -> forall k, n <= k -> Z.testbit a k = false.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Ha Hn k Hk. destruct (Z.eq_dec a 0) as [->|NE]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|].
  assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma lor_lxor_ones64 a b : 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  Z.lor (Z.lxor a 18446744073709551615) (Z.lxor b 18446744073709551615) = Z.lxor (Z.land a b) 18446744073709551615.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Ha Hb. change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, !Z.lxor_spec, Z.land_spec.
  destruct (Z.lt_ge_cases n 64) as [L|G].
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit a n), (Z.testbit b n); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite (testbit_false_ge a 64), (testbit_false_ge b 64) by lia. reflexivity.
Qed.

Lemma usage_sub_word u w : 0 <= u < 2^64 -> 0 <= w < 2^64 ->
  Z_to_bv 64 (u + Z.lor (bv_unsigned (Z_to_bv 64 (Z.lxor w 18446744073709551615))) 18446744073709551584)
  = wz (u - (Z.land w 31 + 1)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Hu Hw.
  assert (HX : 0 <= Z.lxor w 18446744073709551615 < 2^64) by (rewrite zb_lxor_ones by lia; lia).
  rewrite unsigned_lit by lia.
  change 18446744073709551584 with (Z.lxor 31 18446744073709551615).
  rewrite lor_lxor_ones64 by lia.
  assert (HL : 0 <= Z.land w 31 < 32).
  { split; [apply Z.land_nonneg; lia|]. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  rewrite zb_lxor_ones by lia. unfold wz.
  rewrite <- (Z_to_bv_mod64 (u + _)), <- (Z_to_bv_mod64 (u - _)). f_equal.
  replace (u + (18446744073709551615 - Z.land w 31)) with ((u - (Z.land w 31 + 1)) + 1 * 2^64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Definition rfg_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc W : Z) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists a3 a4 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (wz W) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x20ccc) fc None m' (seg_rom psegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells psegs m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

Lemma rntf_fg : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g : aptr) (lo : Z),
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv psegs m -> meta_slot st g ->
  mw_ok mr ->
  (m_sizeclass mr < 48 -> 0 <= usage st (m_sizeclass mr) < 2^64) ->
  rw_cells psegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rfg_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
               (fg_usage_st st g) g (m_sizeclass mr) (meta_word mr) fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20c98) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros mr MR MI MSL MW UR FR FRL ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  pose proof (meta_word_range mr MW) as MWR.
  pose proof MW as (LI & FB & SCR & ML).
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  unfold RCTX, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
    replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
      with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  rmeta_chunk MR MSL CH. fold mr in CH.
  st1. st1. st1. rewrite MW2. st1. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  -
    clear CH.
    unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. unfold rfg_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split; [apply rpres_except_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|exact MR].
  - unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
    specialize (UR ltac:(lia)).
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (370576, 370576 + 928)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    pose proof (rmrep_usage_read st m (m_sizeclass mr) (wa (RCTX + 464 + 8 * m_sizeclass mr)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
    st1. rewrite ?(unsigned_lit (m_sizeclass mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    st1.
    replace (wa (370576 + 464 + 8 * m_sizeclass mr)) with (Z_to_bv 64 (370576 + m_sizeclass mr * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
    st1. clear RDU.
    st1. st1. st1.
    rewrite (usage_sub_word (usage st (m_sizeclass mr)) (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).
    pose proof MR as (_ & (_ & _ & USG & _) & _).
    pose proof (u64arr_store_ok psegs _ _ (usages st) (m_sizeclass mr) (Z_to_bv 64 (370576 + m_sizeclass mr * 8 + 464)) USG
                  ltac:(rewrite usages_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_usage st mX (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    clear USG.
    rraw_store_finish (370576 + 464 + 8 * m_sizeclass mr) (le8 (wz (usage st (m_sizeclass mr) - (m_last_idx mr + 1)))) FR ST MU WM SOK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (CH' : rw_cells psegs mX (conc st g) (meta_cells st mr)) end.
    { pose proof (rmrep_meta_chunk _ _ _ MR2 (meta_slot_set_usage _ _ _ _ MSL)) as X.
      rewrite conc_set_usage, rec_set_usage in X. fold mr in X.
      replace (meta_cells (set_usage (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) st) mr) with (meta_cells st mr) in X; [exact X|].
      unfold meta_cells, pw. rewrite !oconc_set_usage. reflexivity. }
    clear CH. unfold meta_cells in CH'.
    st1. clear CH'.
    apply evt_done. unfold rfg_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.
End WithCeiling0.
End RF_ntf_D.

Module RF_ntf_F.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_malloc_free F_malloc_fast MallocModel_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocModel_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_ntf_H.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocKit_A3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_malloc_free OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_malloc_fast OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocModel_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocModel_B.F_ntf_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_ntf_H.F_ntf_F OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocKit_A3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RMallocRep RMallocTree RMallocKit_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RMallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_free.RF_free_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RF_ntf_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_free.RF_ntf_E.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rntf_seq : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st0 st (g p : aptr) (sc ns lo : Z),
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv psegs m -> meta_slot st g -> mw_ok mr ->
  sc = m_sizeclass mr -> m_mem mr = Some p -> 0 <= ns < 256 ->
  fm_facts st g ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  s_regions st = s_regions st0 -> s_shadow st = s_shadow st0 -> s_groups st = s_groups st0 ->
  munch [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)] m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
               (fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen mr * 4096)))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (Z_to_bv 64 ns) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20d2c) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros mr MR MI MSL MW HSC Hmem NS FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof FR as [[[LJ _] _] _]. cbn in LJ.
  unfold RCTX, rntf_frame, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  st1. rewrite ?(unsigned_lit sc) by lia. st1.
  pose proof MR as (_ & (_ & _ & _ & _ & _ & C6) & _).
  pose proof (rw_cells_store_ok_at psegs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (370576 + 912)) C6 eq_refl eq_refl
                ltac:(unfold wa; f_equal; lia)) as SOK.
  clear C6.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_seq st mX ns MR NS) as MR1; unfold RCTX in MR1 end.
  rraw_store_finish (370576 + 912) [b8 ns] FR ST MU WM SOK.
  set (st1 := upd_ctx (set_seq ns) st) in MR1.
  st1.
  assert (JOIN : forall m2 (a1' : word),
    rmrep (seq_st ns sc st) m2 -> mem_inv psegs m2 ->
    munch [(bv_unsigned sp - 96, bv_unsigned sp); (370576, 370576 + 928)] m0 m2 -> wmono psegs m0 m2 ->
    stk psegs m2 lo (bv_unsigned sp + -96) -> rw_cells psegs m2 (bv_unsigned sp + -96) [CB 48 junk; C8 rr_guard; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 raw] ->
    evt psegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
                 (fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen (get_meta_rec st g) * 4096)))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1' (Z_to_bv 64 ns) (Z_to_bv 64 31) a4 a5 a6 a7 (Z_to_bv 64 370576) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20d44) fc None m2 (seg_rom psegs))).
  { intros m2 a1' MR2 MI2 MU2 WM2 ST2 FR2.
    assert (MS2 : meta_slot (seq_st ns sc st) g) by (unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); exact MSL).
    rmeta_chunk MR2 MS2 CH.
    assert (Hc2 : forall q, conc (seq_st ns sc st) q = conc st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
    assert (Hr2 : forall q, get_meta_rec (seq_st ns sc st) q = get_meta_rec st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
    assert (Ho2 : forall q, oconc (seq_st ns sc st) q = oconc st q) by (intros [q|]; [apply Hc2|reflexivity]).
    rewrite !Hc2, !Hr2, !Ho2 in CH. rewrite Hmem in CH. cbn [oconc] in CH.
    st1. st1. st1. st1. clear CH.
    rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW).
    replace (4096 * m_maplen (get_meta_rec st g)) with (m_maplen (get_meta_rec st g) * 4096) by lia.
    replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc (seq_st ns sc st) g)) by (f_equal; apply Hc2).
    eapply evt_mono.
    { eapply (rntf_fm ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 junk raw s0o s1o s2o s3o (seq_st ns sc st) g lo);
        first [exact MR2 | exact MI2 | exact MS2 | exact S1 | exact FR2 | exact ST2 | unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia | lia | idtac].
      unfold seq_st. rewrite record_seq_eq. destruct (sc_in_seq_range sc); repeat apply fm_facts_ctx; try reflexivity; exact FMF. }
    intros ms' PO. unfold rntf_ret_post in PO |- *.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & m' & -> & PE & WM' & MI' & ST' & MR').
    do 14 eexists. split; [reflexivity|].
    split.
    { eapply rpres_except_trans.
      - apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU2; [exact MU2|exact WM2|].
        cbn [ivs_covered]. repeat split; intros x Hx; [apply rfree_fp_stack; lia | apply rfree_fp_ctx; unfold RCTX; lia].
      - eapply rpres_except_mono; [exact PE|]. intros a Ha.
        eapply (rfree_fp_mono st0 (seq_st ns sc st) lo (bv_unsigned sp) (bv_unsigned sp) a); try exact Ha; try lia;
          unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); cbn; rewrite <- ?ER, <- ?ES, <- ?EG; try reflexivity; auto. }
    split; [eapply wmono_trans; [exact WM2|exact WM']|]. split; [exact MI'|]. split; [exact ST'|exact MR']. }
  if_cases K; zify_cond K.
  -
    assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K).
    eapply JOIN; try eassumption. unfold seq_st. rewrite record_seq_eq, NR. exact MR1.
  - assert (SR : sc_in_seq_range sc = true).
    { destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
    assert (SR' : 7 <= sc < 39).
    { unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }
    st1.
    pose proof MR1 as (_ & (_ & _ & _ & US & _) & _).
    pose proof (u8arr_store_ok psegs _ _ (unmap_seqs st1) (sc - 7) (Z_to_bv 64 (370576 + (sc + -7) + 848)) US
                  ltac:(rewrite unmap_seqs_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    clear US.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_unmap_seq st1 mX (sc - 7) ns MR1 ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    rraw_store_finish (370576 + 848 + (sc - 7)) [b8 ns] FR ST MU WM SOK.
    eapply JOIN; try eassumption.
    unfold seq_st. rewrite record_seq_eq, SR. unfold st1 in MR2.
    match type of MR2 with rmrep ?S _ => replace (upd_ctx _ (upd_ctx (set_seq ns) st)) with S; [exact MR2|] end.
    unfold upd_ctx. cbn. reflexivity.
Qed.

Lemma zeros32_cells : cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] = zeros 32.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). vm_compute. reflexivity. Qed.

Lemma rntf_top : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st0 st (g p : aptr) (sc lo : Z),
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv psegs m -> meta_slot st g -> mw_ok mr ->
  sc = m_sizeclass mr -> m_mem mr = Some p -> m_maplen mr <> 0 ->
  0 <= c_seq (ctx st) < 256 ->
  fm_facts st g ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  s_regions st = s_regions st0 -> s_shadow st = s_shadow st0 -> s_groups st = s_groups st0 ->
  munch [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)] m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
               (fm_st (record_seq sc (step_seq st)) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen mr * 4096)))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (wz (meta_word mr)) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20ccc) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros mr MR MI MSL MW HSC Hmem HML SEQ FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_maplen _ MW) as M12.
  pose proof FR as [[[LJ _] _] _]. cbn in LJ.
  unfold RCTX, rntf_frame, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  st1. rewrite M12. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. 2:{ exfalso. lia. } clear K.
  pose proof (rmrep_seq_read st m (wa (RCTX + 912)) MR eq_refl) as RDS. unfold RCTX, wa in RDS.
  st1. clear RDS. st1.
  st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
  -
    st1.
    replace (record_seq sc (step_seq st)) with (seq_st (c_seq (ctx st) + 1) sc st).
    2:{ unfold seq_st. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m junk raw s0o s1o s2o s3o st0 st g p sc (c_seq (ctx st) + 1) lo);
      first [exact MR | exact MI | exact MSL | exact MW | exact HSC | exact Hmem | exact FMF | exact S1 | exact ER | exact ES | exact EG | exact MU | exact WM | exact FR | exact ST | unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia].
  -
    pose proof MR as (_ & (_ & _ & _ & US & _) & _).
    pose proof (rw_cells_of_u8arr psegs m _ _ US) as UB. rewrite unmap_seqs_length in UB. clear US. unfold RCTX in UB.
    replace (370576 + 848) with 371424 in UB by reflexivity.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(370576 + 848, 370576 + 880)]%Z mX) as MUz; pose proof (wmono_refl psegs mX) as WMz end.
    st1. st1. st1. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (UA' : u8arr psegs mX (RCTX + 848) (zeros 32))
        by (apply (u8arr_of_rw_cells psegs mX _ 32); unfold RCTX; eapply rw_cells_congr; [| | | exact UB]; [exact zeros32_cells| reflexivity| cbn; tauto]) end.
    clear UB.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRz : rmrep stz mX) end.
    { eapply (rmrep_ctx_frameW st stz m _ _ MR MUz WMz); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - left. unfold stz. rewrite unmap_seqs_empty. exact UA'.
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
        unfold ctx_tail_cells, brk_word, ctx, stz. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity. }
    st1. st1.
    replace (record_seq sc (step_seq st)) with (seq_st 1 sc stz).
    2:{ unfold seq_st, stz. rewrite (step_seq_eq st). fold (ctx st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
    replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc stz g)) by reflexivity.
    replace (conc st p) with (conc stz p) by reflexivity.
    change (get_meta_rec st g) with (get_meta_rec stz g).
    eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 _ junk raw s0o s1o s2o s3o st0 stz g p sc 1 lo);
      first [exact MRz | assumption | exact MSL | exact MW | exact HSC | exact Hmem | exact S1 | exact ER | exact ES | exact EG | exact FR | exact ST | unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia
            | apply fm_facts_ctx; [reflexivity| exact FMF] ].
Qed.
End WithCeiling0.
End RF_ntf_F.

Module RF_ntf_G.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_malloc_free F_malloc_fast MallocModel_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocModel_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocKit_A3 MallocKit_B3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_malloc_free OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_malloc_fast OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocModel_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocModel_B.F_ntf_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocKit_A3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocKit_B3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RMallocRep RMallocTree RMallocKit_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_get_meta.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RMallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_get_meta OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RF_ntf_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_free.RF_ntf_E.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition rnest_call_post (sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g p : aptr) (G1 idx : Z) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x20cf8) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (conc st p)) s1 (Z_to_bv 64 G1) (Z_to_bv 64 idx) a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 RCTX) (Z_to_bv 64 (conc st g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x20a70) fc None m' (seg_rom psegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells psegs m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

Lemma rntf_nest_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g p base1 g1 : aptr) (ghp gh1 : ghdr) (ar1 : area) (b3 lo8 hi8 off16 lo : Z),
  let mr := get_meta_rec st g in
  let mr1 := get_meta_rec st g1 in
  let idx1 := Z.land b3 31 in
  rmrep st m -> mem_inv psegs m -> meta_slot st g -> mw_ok mr -> m_maplen mr = 0 -> m_mem mr = Some p ->
  (s_groups st) !! p = Some ghp ->
  (forall o, 0 <= o < 12 -> exists h, cell_read (get_shadow st (fst p)) (snd p + o) = Unknown h) ->
  bytes_at psegs m (conc st p - 4) [b8 0; b8 b3; b8 lo8; b8 hi8] ->
  0 <= b3 < 256 -> 0 <= lo8 < 256 -> 0 <= hi8 < 256 -> off16 = lo8 + 256 * hi8 ->
  base1 = aadd p (- (UNIT * off16) - UNIT) ->
  (s_groups st) !! base1 = Some gh1 -> g_meta gh1 = Some g1 -> meta_slot st g1 -> m_mem mr1 = Some base1 ->
  0 <= m_avail mr1 < 2^32 -> 0 <= m_freed mr1 < 2^32 -> 0 <= m_last_idx mr1 < 32 -> 0 <= m_freeable mr1 < 2 ->
  0 <= m_sizeclass mr1 < 64 -> 0 <= m_maplen mr1 < 2^40 ->
  (s_areas st) !! (area_of g1) = Some ar1 -> a_check ar1 = c_secret (ctx st) -> 0 <= c_secret (ctx st) < 2^64 ->
  c_init_done (ctx st) <> 0 ->
  idx1 <= m_last_idx mr1 -> Z.testbit (m_avail mr1) idx1 = false -> Z.testbit (m_freed mr1) idx1 = false ->
  (m_sizeclass mr1 < 48 -> size_class (m_sizeclass mr1) * idx1 <= off16 < size_class (m_sizeclass mr1) * (idx1 + 1)) ->
  (48 <= m_sizeclass mr1 -> m_sizeclass mr1 = 63) ->
  (m_maplen mr1 <> 0 -> off16 <= m_maplen mr1 * 256 - 1) ->
  rw_cells psegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rnest_call_post sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (grp_del st g p) g p (conc st g1) idx1 fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 (wz (meta_word mr)) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20ccc) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros mr mr1 idx1 MR MI MSL MW HML Hmem Hp UNK HDR B3 LO8 HI8 O16 Hb1 Hgh1 Hg1 MS1 Hmem1
         AV1 FR1 LI1 FB1 SC1 ML1 Har1 Hchk SEC INI Hidx Hav Hfr Hsc Hsc63 Hml FR FRL ST LO LOLE. subst mr mr1.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_maplen _ MW) as M12.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose proof (rmeta_slot_bounds st m g1 MR MS1) as G1B.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (rgroup_conc st p ghp WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC).
  destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RFr). pose proof (round_up_pg_ge (r_len r)) as RU.
  pose proof (rreserved_disjoint _ _ RFr) as (Dr1 & Dr2 & Dr3 & Dr4).
  destruct (WG base1 gh1 Hgh1) as (rb & Hrb & _ & Bb0 & Bb1 & BbA). rewrite Hb1 in Hrb. cbn [aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. clear Hrb.
  assert (HBc : conc st base1 = conc st p - 16 * off16 - 16).
  { rewrite Hb1. rewrite conc_aadd by (cbn; rewrite Hr; eauto). unfold UNIT. lia. }
  rewrite Hb1 in Bb0. cbn [aadd snd] in Bb0.
  pose proof MS1 as (a & ara & k & Ha & Hkk & Eg).
  destruct (WA a ara Ha) as (rg & Hrg & Sa0 & Sa1 & AAL & ANG & ALR).
  destruct (WR (fst a) rg Hrg) as (RgB0 & RgBAL & _ & RgBC & RFa).
  assert (HG : conc st g1 = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  assert (Hao : area_of g1 = a).
  { rewrite Eg. unfold AREA_HDR, META_SIZE. apply area_of_slot; [exact AAL | unfold NSLOTS in Hkk; lia]. }
  assert (HGm : conc st g1 mod 4096 = AREA_HDR + META_SIZE * k).
  { rewrite HG. apply page_off_mod; [exact RgBAL | exact AAL | unfold AREA_HDR, META_SIZE, NSLOTS in *; lia]. }
  assert (P16m : conc st p mod 16 = 0) by (rewrite Cp; apply base16_mod; assumption).
  unfold RCTX, AREA_HDR, META_SIZE, NSLOTS, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  assert (HAeq : r_base rg + snd a = conc st g1 - conc st g1 mod 4096) by lia.
  change (frozen (conc st p mod 16 = 0)) in P16m.
  change (frozen (r_base rg + snd a = conc st g1 - conc st g1 mod 4096)) in HAeq.
  clear HGm AAL RBAL RgBAL SpA BbA.
  destruct GB as (GB0 & GB1 & GB2 & _). destruct G1B as (G1B0 & G1B1 & G1B2 & _).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st p, conc st p + 8)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  st1. rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite M12, HML. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
  rmeta_chunk MR MSL CH. rewrite Hmem in CH. cbn [oconc] in CH.
  st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (rmrep_group_read st mX base1 gh1 MR Hgh1) as [RG _];
    pose proof (rmrep_meta_chunk st mX g1 MR MS1) as MM;
    pose proof (rmrep_area_check_read st mX (area_of g1) ar1 MR Har1) as RA;
    pose proof (rmrep_ctx_secret_read st mX MR) as RC;
    pose proof (bytes_at_read psegs mX _ _ 0 1 HDR ltac:(lia) ltac:(cbn; lia)) as R4;
    pose proof (bytes_at_read psegs mX _ _ 1 1 HDR ltac:(lia) ltac:(cbn; lia)) as R3;
    pose proof (bytes_at_read psegs mX _ _ 2 2 HDR ltac:(lia) ltac:(cbn; lia)) as R2
  end.
  rewrite Hg1 in RG. unfold pw in RG. cbn [oconc] in RG.
  unfold meta_cells in MM. rewrite Hmem1 in MM. unfold pw in MM. cbn [oconc] in MM. unfold meta_word in MM.
  rewrite Hchk in RA. rewrite Hao, (conc_region' st a rg Hrg) in RA. unfold RCTX in RC.
  rewrite (rsec_init _ _ INI) in RC. rewrite <- (wz_mod64 (c_secret (ctx st) + bv_unsigned rr_secret)) in RA, RC.
  change (firstn 1 (skipn (Z.to_nat 0) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 0] in R4.
  change (firstn 1 (skipn (Z.to_nat 1) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 b3] in R3.
  change (firstn 2 (skipn (Z.to_nat 2) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 lo8; b8 hi8] in R2.
  replace (conc st p - 4 + 0) with (conc st p - 4) in R4 by lia.
  replace (conc st p - 4 + 1) with (conc st p - 3) in R3 by lia.
  replace (conc st p - 4 + 2) with (conc st p - 2) in R2 by lia.
  rewrite <- (le2_lohi lo8 hi8) in R2 by lia. rewrite <- O16 in R2.
  st1.
  eapply evt_cut.
  { eapply (rget_meta_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (conc st p) (conc st g1) (conc st base1) (r_base rg + snd a) b3 off16
            (m_avail (get_meta_rec st g1)) (m_freed (get_meta_rec st g1)) (m_last_idx (get_meta_rec st g1)) (m_freeable (get_meta_rec st g1))
            (m_sizeclass (get_meta_rec st g1)) (m_maplen (get_meta_rec st g1)) ((c_secret (ctx st) + bv_unsigned rr_secret) mod 2^64)).
    all: lazymatch goal with
         | |- ov_read_bytes _ _ (wa (_ - 4)) 1 = _ => exact R4
         | |- ov_read_bytes _ _ (wa (_ - 3)) 1 = _ => exact R3
         | |- ov_read_bytes _ _ (wa (_ - 2)) 2 = _ => exact R2
         | |- ov_read_bytes _ _ (wa (conc _ _)) 8 = _ => exact RG
         | |- ov_read_bytes _ _ (wa 370576) 8 = _ => exact RC
         | |- ov_read_bytes _ _ (wa RCTX) 8 = _ => exact RC
         | |- ov_read_bytes _ _ (wa (r_base _ + snd _)) 8 = _ => exact RA
         | |- rw_cells _ _ (conc _ _) _ => exact MM
         | |- _ -> ov_read_bytes _ _ _ 2 = _ => intros Hlt; apply rsize_classes_read; [assumption | lia]
         | |- _ => idtac
         end.
    all: first [ exact P16m | exact HAeq | exact Hidx | exact Hav | exact Hfr | exact Hsc | exact Hsc63 | exact Hml
               | apply rsec_range
               | lazymatch goal with |- bv_unsigned (Z_to_bv 64 _) = _ => solve [unfold wz; rewrite ?unsigned_lit by lia; lia] end
               | solve [unfold UNIT in *; lia]
               | lia | unfold wz; rewrite ?unsigned_lit by lia; lia | unfold UNIT in *; lia ]. }
  intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
  replace (ret_pc (Z_to_bv 64 0x20ce4)) with (Z_to_bv 64 0x20ce4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  st1.
  unfold wa in R3. unfold wz. replace (conc st p - 3) with (conc st p + -3) in R3 by lia.
  st1.
  clear CH MM RG RA RC R4 R2.
  pose proof MR as (_ & _ & _ & _ & GR0 & _). destruct (GR0 p ghp Hp) as (w8 & RWp & _). clear GR0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (rw_cells_store_ok_at psegs mX _ _ 0 (C8 (pw st (g_meta ghp))) 8 (Z_to_bv 64 (conc st p)) RWp eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK end.
  clear RWp.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_group_hdr_zero st mX p ghp (le8 (Z_to_bv 64 0)) ltac:(eassumption) Hp UNK (length_le8 _)) as MR2
  end.
  rraw_store_finish (conc st p) (le8 (Z_to_bv 64 0)) FR ST MU WM SOK.
  apply (rmrep_grp_del_eq st _ g p) in MR2.
  st1. st1.
  apply evt_done. unfold rnest_call_post. do 14 eexists.
  split. { unfold idx1. rewrite ?zxb_b8 by lia. unfold wz. rewrite ?(wz_unsigned b3), ?(unsigned_lit b3) by lia.
           cbv delta [mkR]. unfold RCTX. reflexivity. }
  split.
  { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. repeat split; intros x Hx.
    + apply rfree_fp_stack. lia.
    + eapply rfree_fp_group; [exact Hp | lia]. }
  split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
Qed.

Lemma rntf_nest_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) (st0 st : mstate) (g : aptr) (lo : Z),
  rmrep st m -> mem_inv psegs m -> meta_slot st g -> fm_facts st g ->
  conc st g = conc st0 g ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  rw_cells psegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (fm_st st g) a0 a1)
      (MS (mkR (Z_to_bv 64 0x20cf8) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) (Z_to_bv 64 (conc st0 g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20cf8) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros MR MI MSL FMF Hcg S1 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  st1. st1. st1.
  rewrite <- Hcg.
  eapply (rntf_fm _ sp gp tp _ _ _ s0 s1 a1 a0 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m junk raw s0o s1o s2o s3o st g lo);
    first [exact MR | assumption | exact MSL | exact FMF | exact S1 | exact FR | exact ST | unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia].
Qed.
End WithCeiling0.
End RF_ntf_G.

Module RF_ntf_H.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_malloc_free F_malloc_fast MallocModel_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocModel_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_ntf_H.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_ntf_H MallocKit_A3 MallocKit_B3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_malloc_free OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_malloc_fast OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocModel_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocModel_B.F_ntf_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_ntf_H.F_ntf_F OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_ntf_H OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocKit_A3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocKit_B3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RMallocRep RMallocTree RMallocKit_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RMallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_free.RF_free_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RF_ntf_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section POST.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (st : mstate) (g : aptr) (i : Z) (m1 : word -> option byte).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation HD := (pw st (active st sc)).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation PHEAD := (Z_to_bv 64 (RCTX + sc * 8)).
Definition RAT (pc : Z) (R : bvmap 5 word) (ms' : machine_state) : Prop := ms' = MS R F (Z_to_bv 64 pc) fc None m1 (seg_rom psegs).

Definition rentry_cases (ms' : machine_state) : Prop :=
  (ntf_cond st g i = false /\ mask <> 0 /\
   exists t0 t1 t2 a0 a2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
     RAT 0x20df0 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD a0 SELF a2 a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/
  (ntf_cond st g i = false /\ mask = 0 /\
   exists t0 t1 t2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
     RAT 0x20bd4 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/
  (ntf_cond st g i = true /\ m_next mr = None /\
   exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
     RAT 0x20c98 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G a1 a2 a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/
  (ntf_cond st g i = true /\ m_next mr = Some g /\ sc < 48 /\
   exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
     RAT 0x20c2c (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/
  (ntf_cond st g i = true /\ sc < 48 /\
   exists nx, m_next mr = Some nx /\ nx <> g /\
   exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6,
     RAT 0x20ba8 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms').
End POST.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (g : aptr) (i lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists m1 junk,
    rentry_cases ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i m1 ms'
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono psegs m m1 /\ mem_inv psegs m1
    /\ stk psegs m1 lo (bv_unsigned sp + -96)
    /\ rw_cells psegs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra)
    /\ rmrep st m1.

Lemma meta_word_sc52 mr : mw_ok mr ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros MW. pose proof (meta_word_range mr MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
  replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
    with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma meta_word_mod32 mr : mw_ok mr -> meta_word mr mod 32 = m_last_idx mr.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros MW. pose proof MW as (LI & FB & SCR & ML). unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section ENTRY.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (st : mstate) (g : aptr) (i lo : Z).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation maskw := (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr))).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation POST := (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m).

Hypothesis EH : entry_hyps st g i.
Hypothesis MI0 : mem_inv psegs m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 96.

Definition rmid_ctx (m1 : word -> option byte) (junk : list byte) : Prop :=
  munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono psegs m m1 /\ mem_inv psegs m1
  /\ stk psegs m1 lo (bv_unsigned sp + -96) /\ rw_cells psegs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) /\ rmrep st m1.

Lemma rmaskw_zero : maskw = 0 <-> mask = 0.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). apply lor_sxv_zero; [apply (eh_freed _ _ _ EH) | apply (eh_avail _ _ _ EH)]. Qed.
Lemma rmaskw_range : 0 <= maskw < 2^64.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). apply lor_range64; apply sxv_range. Qed.

Ltac rpost_common MU WM MI ST FR MR m1 junk :=
  apply evt_done; exists m1, junk; split; [| exact (conj MU (conj WM (conj MI (conj ST (conj FR MR)))))].


Lemma rntf_notall : forall (t0 t1 t2 a4 a5 a6 a7 s2x t3 t4 t5 t6 : word) m1 junk,
  rmid_ctx m1 junk -> ntf_cond st g i = false ->
  evt psegs POST
    (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20bcc) fc None m1 (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros (MU & WM & MI & ST & FR & MR) HC.
  pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
  pose proof (rmeta_slot_bounds st m1 g MR (eh_slot _ _ _ EH)) as (GB0 & GB1 & GB2 & _). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  st1. rewrite ?(unsigned_lit (conc st g)) by lia.
  st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; unmask64 K.
  -
    rpost_common MU WM MI ST FR MR m1 junk.
    left. split; [exact HC|]. split; [intros E; apply K, MZ, E|].
    do 14 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
  -
    assert (M0 : mask = 0) by (apply MZ; lia).
    rpost_common MU WM MI ST FR MR m1 junk.
    right; left. split; [exact HC|]. split; [exact M0|].
    do 12 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.

Lemma rntf_fge : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m1 junk,
  rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> okay_to_free st g = true ->
  evt psegs POST
    (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20b84) fc None m1 (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros (MU & WM & MI & ST & FR & MR) HALL OKT.
  pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
  pose proof MW as (LI & FB & SCR & ML).
  pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _).
  unfold RCTX, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
  assert (HC : ntf_cond st g i = true) by (rewrite ntf_cond_unfold, HALLb, OKT; reflexivity).
  assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
  { intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _).
    split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
  rmeta_chunk MR MSL CH.
  st1. clear CH.
  destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
  - destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
    st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. { exfalso. lia. }
    specialize (G50 HC ltac:(congruence)).
    st1. st1. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia. 2:{ exfalso. lia. }
    st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
    pose proof (rmrep_active_read st m1 sc (wa (RCTX + 80 + 8 * sc)) MR ltac:(lia) eq_refl) as RDA. unfold RCTX in RDA.
    replace (wa (370576 + 80 + 8 * sc)) with (Z_to_bv 64 (370576 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
    st1. clear RDA.
    st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
    + pose proof (NINJ ltac:(lia)) as ->.
      rpost_common MU WM MI ST FR MR m1 junk.
      do 3 right; left. split; [exact HC|]. split; [exact NX|]. split; [lia|].
      do 12 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
    + assert (NE : nx <> g) by (intros ->; apply K5; reflexivity).
      rpost_common MU WM MI ST FR MR m1 junk.
      do 4 right. split; [exact HC|]. split; [lia|]. exists nx. split; [exact NX|]. split; [exact NE|].
      do 11 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
  - st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. 2:{ exfalso. lia. }
    rpost_common MU WM MI ST FR MR m1 junk.
    do 2 right; left. split; [exact HC|]. split; [exact NX|].
    do 14 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.

Lemma rntf_okchk : forall (t0 t1 t2 a4 a6 a7 t3 t4 t5 t6 : word) m1 junk,
  rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> m_freeable mr <> 0 ->
  evt psegs POST
    (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 (Z_to_bv 64 (meta_word mr)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20ad4) fc None m1 (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros MC HALL FRNZ. pose proof MC as (MU & WM & MI & ST & FR & MR).
  pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
  pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
  pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_range _ MW) as MWR. pose proof (meta_word_lt4096 _ MW) as M4.
  pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
  assert (FRZ : (m_freeable mr =? 0) = false) by (apply Z.eqb_neq; lia).
  st1. st1. st1.
  st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  {
    eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
    rewrite okf_unfold, FRZ. replace (48 <=? sc) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  assert (SC48 : sc < 48) by lia. clear K2.
  assert (NB48 : (48 <=? sc) = false) by (apply Z.leb_gt; lia).
  specialize (USG SC48).
  pose proof (size_class_range sc ltac:(lia)) as SZ.
  assert (RS' : ov_read_bytes psegs m1 (Z_to_bv 64 (77690 + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))).
  { replace (Z_to_bv 64 (77690 + 2 * sc)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
    apply rsize_classes_read; [assumption| lia]. }
  st1. rewrite (meta_word_last_idx _ MW). st1. rewrite (meta_word_maplen _ MW). st1. st1.
  assert (K690 : forall (t0' : word),
    m_maplen mr <> 0 ->
    evt psegs POST
      (MS (mkR ra sp' gp tp t0' t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (get_stride mr)) (Z_to_bv 64 77690) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 370576) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20b28) fc None m1 (seg_rom psegs))).
  { intros t0' MLNZ.
    assert (MLF : (m_maplen mr =? 0) = false) by (apply Z.eqb_neq; exact MLNZ).
    assert (GSR : 0 < get_stride mr < 2^64).
    { unfold get_stride. destruct (m_last_idx mr =? 0), (m_maplen mr =? 0); cbn [andb negb]; unfold UNIT; lia. }
    st1. rewrite ?(unsigned_lit sc), ?(Z.shiftl_mul_pow2 sc 1) by lia. change (2 ^ 1) with 2. st1.
    replace (77690 + sc * 2) with (77690 + 2 * sc) by lia.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
    st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
    { eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
      rewrite okf_unfold, FRZ, NB48. cbn [orb].
      replace (get_stride mr <? UNIT * size_class sc) with true by (symmetry; apply Z.ltb_lt; unfold UNIT; lia). reflexivity. }
    assert (STRF : (get_stride mr <? UNIT * size_class sc) = false) by (apply Z.ltb_ge; unfold UNIT; lia).
    assert (OKF : okay_to_free st g =
              if negb (optr_eqb (m_next mr) (Some g)) then true
              else if negb (is_bouncing sc st) then true
              else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false).
    { rewrite okf_unfold, FRZ, NB48, STRF, MLF. reflexivity. }
    rmeta_chunk MR MSL CH.
    st1. clear CH.
    assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
    { intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _).
      split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
    destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
    2:{ st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia. 2:{ exfalso. lia. }
        eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF. reflexivity. }
    destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
    st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia.
    { assert (NE : nx <> g) by (intros ->; apply K6; reflexivity).
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF.
      cbn [optr_eqb]. rewrite (aptr_eqb_neq nx g NE). reflexivity. }
    pose proof (NINJ ltac:(lia)) as Enx. subst nx.
    rewrite optr_eqb_refl in OKF. cbn [negb] in OKF.
    st1. rewrite ?(unsigned_lit sc) by lia. st1.
    st1. if_cases K7; zify_cond K7.
    { assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K7).
      unfold is_bouncing in OKF. rewrite NR in OKF. cbn [andb negb] in OKF.
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
    assert (SR : sc_in_seq_range sc = true).
    { destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
    assert (SR' : 7 <= sc < 39).
    { unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }
    unfold is_bouncing in OKF. rewrite SR in OKF. cbn [andb] in OKF.
    st1.
    pose proof (rmrep_bounces_read st m1 (sc - 7) (wa (RCTX + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB. unfold RCTX, wa in RDB.
    pose proof (BND (sc - 7)) as BR.
    replace (Z_to_bv 64 (370576 + 880 + (sc - 7))) with (Z_to_bv 64 (370576 + (sc + -7) + 880)) in RDB by (f_equal; lia).
    st1. clear RDB. st1.
    st1. if_cases K8; zify_cond K8; rewrite ?b8_unsigned, ?unsigned_lit in K8 by lia.
    { replace (100 <=? bounces st (sc - 7)) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [negb] in OKF.
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
    replace (100 <=? bounces st (sc - 7)) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [negb] in OKF.
    st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
    pose proof (rmrep_usage_read st m1 sc (wa (RCTX + 464 + 8 * sc)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
    replace (wa (370576 + 464 + 8 * sc)) with (Z_to_bv 64 (370576 + sc * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
    st1. clear RDU.
    st1. rewrite ?(unsigned_lit (m_last_idx mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1.
    st1. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
    { replace (9 * (m_last_idx mr + 1) <=? usage st sc) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [andb] in OKF.
      assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
      eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC). }
    replace (9 * (m_last_idx mr + 1) <=? usage st sc) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [andb] in OKF.
    st1. st1. if_cases K10; zify_cond K10; rewrite ?unsigned_lit in K10 by lia.
    - replace (m_last_idx mr + 1 <? 20) with false in OKF by (symmetry; apply Z.ltb_ge; lia).
      assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
      eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC).
    - replace (m_last_idx mr + 1 <? 20) with true in OKF by (symmetry; apply Z.ltb_lt; lia).
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
  assert (K678 :
    (m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
    evt psegs POST
      (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (meta_word mr)) (Z_to_bv 64 77690) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 370576) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20b10) fc None m1 (seg_rom psegs))).
  { intros COND.
    assert (STR : get_stride mr = 16 * size_class sc).
    { unfold get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
      rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
    assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 _ MW). st1.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
    st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
    - eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
      rewrite okf_unfold, FRZ, NB48. cbn [orb].
      replace (m_maplen mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      destruct (get_stride mr <? UNIT * size_class sc); reflexivity.
    - replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 (get_stride mr)) by (rewrite STR; f_equal; lia).
      apply K690. lia. }
  st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  { apply K678. left. lia. }
  st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
  { apply K678. right. lia. }
  st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW). st1.
  st1. if_cases Km2; zify_cond Km2; rewrite ?unsigned_lit in Km2 by lia. 2:{ exfalso. lia. }
  replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 (get_stride mr)).
  2:{ unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
  apply K690. lia.
Qed.

Lemma rntf_entry : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rmrep st m -> stk psegs m lo (bv_unsigned sp) ->
  evt psegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 G (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20a70) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until t6. intros MR ST.
  pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
  pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_range _ MW) as MWR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (GB0 & GB1 & GB2 & _).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof rmaskw_range as MWR'.
  pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5) & _).
  unfold RGOT_SSP, RSSP_GUARD, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. unfold wz in G4.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  st1. carve_frame 96%nat ST. st1. st1. st1. st1. st1.
  st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia]) end.
  clear MR G4 G5.
  lazymatch goal with H : rw_cells psegs _ (bv_unsigned sp + -96) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.
  rmeta_chunk MR1 MSL CH.
  st1. st1. st1. rewrite ?sx32_wz_sxv by lia. st1.
  st1. rewrite ?(unsigned_lit i) by lia. rewrite (sllw1_word i) by lia.
  st1. rewrite ?(unsigned_lit (meta_word mr)) by lia.
  st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
  st1. rewrite (meta_word_freeable _ MW).
  st1. rewrite (meta_word_sc52 _ MW).
  clear CH.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MC : rmid_ctx mX junk48) by (split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST|]; split; [exact FR|exact MR1]) end.
  st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { assert (HC : ntf_cond st g i = false).
    { rewrite ntf_cond_unfold, okf_unfold. replace (m_freeable mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia). apply andb_false_r. }
    eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC). }
  st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite ?(unsigned_lit (Z.lor _ _)) by (apply lor_range64; apply sxv_range).
  rewrite addw_word. replace (maskw + sxv (2 ^ i)) with (sxv (2 ^ i) + maskw) by lia.
  st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 _ MW).
  st1. rewrite addiw_m1_word.
  pose proof (sxv_range (sxv (2 ^ i) + maskw)) as R1. pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as R2.
  st1. if_cases K2; zify_cond K2; rewrite ?wz_unsigned in K2 by (apply sxv_range).
  - assert (HC : ntf_cond st g i = false).
    { rewrite ntf_cond_unfold. replace (mask + bit i =? mask_upto (m_last_idx mr)) with false; [reflexivity|].
      symmetry. apply Z.eqb_neq. unfold bit, mask_upto. intros E. apply K2.
      apply (proj2 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))). exact E. }
    eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC).
  -
    apply (proj1 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))) in K2.
    eapply (rntf_okchk t0 t1 t2 _ _ _ t3 t4 t5 t6 _ junk48 MC); [unfold bit, mask_upto; exact K2 | lia].
Qed.
End ENTRY.
End WithCeiling0.
End RF_ntf_H.

Module RF_ntf.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocBlocks MallocFacts_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocKit_B MallocKit_B2 MallocModel_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocModel_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocModel_B.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocKit_B2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocModel_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocModel_B.F_ntf_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocModel_B.F_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocKit_B3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_ntf_H.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_ntf_H.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_free.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.MallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_ntf_H.F_ntf_F OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_ntf_H OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_free.F_ntf.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocFacts_Bpres.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RMallocRep RMallocTree RMallocKit_B RMallocKit_B2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocKit_B2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RMallocKit_B3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_get_meta.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_get_meta OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RF_ntf_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_free.RF_ntf_D OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_free.RF_ntf_E OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_free.RF_ntf_F OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_free.RF_ntf_G OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_free.RF_ntf_H.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition rntf_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (LB : list block) (Zs : list aptr) (lo : Z) (m o : word -> option byte)
    (st' : mstate) (mi : mapinfo) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp) /\ rmrep st' m'
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m'
    /\ (exists c, KINV st' LB c) /\ ZINV st' Zs /\ ntf_frame st st' /\ ntf_result st' mi a0 a1 /\ oracle_ok o m' st'.


Lemma rpres_except_entry st lo (sp : word) m m1 :
  munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m1 -> wmono psegs m m1 -> lo <= bv_unsigned sp - 96 ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m m1.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros MU WM LOLE. apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
  cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rfree_fp_stack. lia.
Qed.

Lemma roracle_ok_pres o m m' st lo (sp : Z) (mw : word -> option byte) :
  oracle_ok o m st -> rmrep st mw -> alloc_ceiling <= lo -> rpres_except (rfree_fp st lo sp) m m' -> oracle_ok o m' st.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros OK MR LO PE rid r q h Hr Hk Hq M8 Hc.
  rewrite (OK rid r q h Hr Hk Hq M8 Hc).
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
  unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  symmetry. apply (PE (r_base r + q)); [lia|].
  intros [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - destruct A as (rid' & r' & Hr' & Hk' & Hin).
    destruct (N.eq_dec rid' rid) as [->|NE]; [rewrite Hr in Hr'; assert (r' = r) by congruence; subst r'; exact (Hk' Hk)|].
    pose proof (lr_lo_group r Hk). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
  - destruct A as (b & gh & Hb & Hin).
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RbB0 & _).
    destruct (WR (fst b) rb Hrb) as (_ & RbAL & _).
    assert (Cm : conc st b mod 16 = 0) by (rewrite Cb; apply base16_mod; assumption).
    Z.div_mod_to_equations. lia.
  - destruct A as (rid' & r' & v & Hr' & Hk' & Hin & HC).
    destruct (N.eq_dec rid' rid) as [->|NE].
    + rewrite Hr in Hr'. assert (r' = r) by congruence. subst r'. replace (r_base r + q - r_base r) with q in HC by lia. rewrite Hc in HC. discriminate.
    + pose proof (lr_lo_group r Hk). pose proof (lr_lo_group r' Hk'). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
Qed.

Lemma rfree_fp_frame st st' lo (sp sp' : Z) a : ntf_frame st st' -> sp' <= sp -> rfree_fp st' lo sp' a -> rfree_fp st lo sp a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros FR HS H. eapply (rfree_fp_mono st st' lo sp sp' a (nf_regions _ _ FR) (nf_shadow _ _ FR) (nf_groups _ _ FR) HS H).
Qed.

Lemma rfree_fp_same st st' lo (sp : Z) a :
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
  rfree_fp st' lo sp a -> rfree_fp st lo sp a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros ER ES EG H. eapply (rfree_fp_mono st st' lo sp sp a ER ES); [rewrite EG; auto| lia| exact H]. Qed.

Lemma rfree_fp_lt st mw lo (sp : Z) a : rmrep st mw -> alloc_ceiling <= lo -> lo <= sp -> rfree_fp st lo sp a -> a < sp.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros MR LO LS H. pose proof MR as (WF & _). pose proof WF as (_ & WR & _ & _ & _).
  unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  destruct H as [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - destruct A as (rid & r & Hr & _ & Hin). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in RC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
  - destruct A as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in RC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
  - destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in RC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
Qed.

Lemma rknown_byte st m (q : aptr) r v :
  rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  cell_read (get_shadow st (fst q)) (snd q) = Known v ->
  bytes_at psegs m (conc st q + 0) [b8 v] /\ 0 <= v < 256.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros MR Hr Hk Ho Hc. rewrite (conc_region' st q r Hr), Z.add_0_r.
  pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst q) r Hr Hk) as [_ HB]. apply HB; auto.
Qed.

Lemma rimplT_queue {R} o h g st0 (k : mstate -> Malloc.M R) bail s Q ms :
  (m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None -> rimplT o (k (queue_st h g st0)) s Q ms) ->
  rimplT o (queue h g st0 k bail) s Q ms.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros H. unfold queue. apply rimplT_guard. intros G1. apply rimplT_guard. intros G2.
  assert (N : m_next (get_meta_rec st0 g) = None) by (destruct (m_next _); [discriminate|reflexivity]).
  assert (P : m_prev (get_meta_rec st0 g) = None) by (destruct (m_prev _); [discriminate|reflexivity]).
  specialize (H N P). unfold queue_st, fm_link, fm_single in H. destruct (get_head st0 h); exact H.
Qed.

Lemma rntf_frame_size junk (s3 s2 s1 s0 ra : word) : cells_size (rntf_frame junk s3 s2 s1 s0 ra) = 96%nat.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). reflexivity. Qed.

Section NTF.
Variables (gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.

Lemma rntf_q_intro (Zs : list aptr) (ra sp s0 s1 s2 s3 : word) st stX st' (m mX : word -> option byte) mi a0v a1v ms' :
  rntf_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo stX mX st' a0v a1v ms' ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m mX ->
  (forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
  (exists c, KINV st' LB c) -> ZINV st' Zs -> ntf_frame st st' -> ntf_result st' mi a0v a1v ->
  oracle_ok o mX stX -> rmrep stX mX -> s_regions st' = s_regions stX -> s_shadow st' = s_shadow stX ->
  rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros RP PE FP KI ZI FR RES OOK MRX ER ES.
  destruct RP as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & PE' & WM' & MI' & ST' & MR').
  unfold rntf_q. do 16 eexists. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|].
  split. { eapply rpres_except_trans; [exact PE|]. eapply rpres_except_mono; [exact PE'|]. exact FP. }
  split; [exact KI|]. split; [exact ZI|]. split; [exact FR|]. split; [exact RES|].
  eapply oracle_ok_frame; [| exact ER | exact ES]. eapply roracle_ok_pres; [exact OOK | exact MRX | exact LO | exact PE'].
Qed.

Theorem rntf_implT : forall (fuel : nat) (R : Type) (k : mstate -> mapinfo -> Malloc.M R) (bail : Malloc.M R)
    (s : PState) (Q : R -> PState -> machine_state -> Prop)
    (ra sp s0 s1 s2 s3 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
    (st : mstate) (g p : aptr) (i c : Z) (Zs : list aptr),
  KINV st LB c -> LPRE st LB c g p i -> ZINV st Zs -> c_init_done (ctx st) <> 0 ->
  rmrep st m -> mem_inv psegs m -> oracle_ok o m st ->
  stk psegs m lo (bv_unsigned sp) -> lo + 96 * Z.of_nat fuel <= bv_unsigned sp ->
  (forall st' mi ms', rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms' -> rimplT o (k st' mi) s Q ms') ->
  rimplT o (nontrivial_free dec_hdr fuel st g i k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x20a70) fc None m (seg_rom psegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  induction fuel as [|f IH]; intros until Zs; intros KI LP ZI INI MR MI OOK ST DEPTH KH.
  { cbn [nontrivial_free]. apply rimplT_undef. }
  rewrite ntf_unfold. cbv zeta.
  pose proof (lpre_gmeta _ _ _ _ _ _ KI LP) as GO. pose proof (gmeta_mw _ _ _ GO) as MW.
  pose proof (lp_hosts _ _ _ _ _ _ LP) as HOSTS. pose proof (lp_i _ _ _ _ _ _ LP) as HI.
  pose proof (go_slot _ _ _ GO) as MSL.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (LOLE : lo <= bv_unsigned sp - 96) by lia.
  set (ms0 := MS _ _ _ _ _ _ _).
  assert (ENTRY : entry_hyps st g i ->
    evt psegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m) ms0).
  { intros EH. subst ms0. eapply rntf_entry; eauto. }
  assert (EH0 : forall (G50 : ntf_cond st g i = true -> m_next (get_meta_rec st g) <> None -> m_sizeclass (get_meta_rec st g) < 48)
                       (G51 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 -> m_sizeclass (get_meta_rec st g) < 48)
                       (G1 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 ->
                             m_next (get_meta_rec st g) <> None -> active st (m_sizeclass (get_meta_rec st g)) = Some g),
             entry_hyps st g i).
  { intros. constructor; auto.
    - exact (go_avail _ _ _ GO).
    - exact (go_freed _ _ _ GO).
    - pose proof (go_sc _ _ _ GO). lia.
    - intros nx NX. exact (proj1 (kinv_next _ _ _ _ _ KI NX)).
    - intros h HA. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI HA))).
    - split; [intros j; apply (ki_cx _ _ _ KI)|]. intros _. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP). }
  destruct (ntf_cond st g i) eqn:HC.
  -
    assert (FG2 : forall stX m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 : word) ms2,
      KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
      munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 ->
      rfg_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 F fc lo stX m2 (fg_usage_st stX g) g
              (m_sizeclass (get_meta_rec stX g)) (meta_word (get_meta_rec stX g)) (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
      (forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
      wmono psegs m m2 -> oracle_ok o m2 stX ->
      data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) -> (exists mw, rmrep stX mw) ->
      rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms2).
    { intros stX m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 ms2 KIX ZIX LPX FRX GNX PRE FGP FPX WM2 OOK2 DATX [mw MRW].
      assert (INIX : c_init_done (ctx stX) <> 0) by (pose proof (nf_amc _ _ FRX) as E; unfold amc in E; injection E; intros; congruence).
      pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX. pose proof (gmeta_mw _ _ _ GOX) as MWX.
      pose proof (lp_hosts _ _ _ _ _ _ LPX) as HOSTSX.
      unfold rfg_post in FGP. destruct FGP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
      set (stU := fg_usage_st stX g) in *.
      assert (INIU : c_init_done (ctx stU) <> 0) by (unfold stU, fg_usage_st; cbv zeta; destruct (m_sizeclass (get_meta_rec stX g) <? 48); exact INIX).
      assert (RU : get_meta_rec stU g = get_meta_rec stX g) by (unfold stU; apply fg_usage_rec).
      assert (CU : forall q, conc stU q = conc stX q) by (intros; unfold stU; apply conc_fg_usage).
      rewrite free_group_unfold. cbv zeta. fold stU. rewrite (go_mem _ _ _ GOX).
      rewrite <- RU. fold (grp_del stU g p). set (stG := grp_del stU g p).
      assert (ALLFREE : forall j, 0 <= j <= m_last_idx (get_meta_rec stX g) -> j <> i -> slot_free (get_meta_rec stX g) j).
      { destruct (data_of_fields _ _ g DATX) as (_ & EA & EF & EL & _).
        unfold slot_free. rewrite EA, EF, EL. intros j Hj NE.
        unfold ntf_cond in HC. apply andb_true_iff in HC. destruct HC as [HALL _]. apply Z.eqb_eq in HALL.
        pose proof (lp_nonfree _ _ _ _ _ _ LP) as NF. unfold slot_free in NF.
        apply (all_free_of_mask (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) i (m_last_idx (get_meta_rec st g)));
          try lia; try exact HALL.
        - exact (go_freed _ _ _ GO). - exact (go_avail _ _ _ GO). - pose proof (go_li _ _ _ GO); lia.
        - destruct (Z.testbit (m_freed (get_meta_rec st g)) i); tauto.
        - destruct (Z.testbit (m_avail (get_meta_rec st g)) i); tauto. }
      assert (KIU : KINV stU LB (m_sizeclass (get_meta_rec stX g) + 1)) by (unfold stU; eapply KINV_fg_usage; eauto).
      assert (LPU : LPRE stU LB c g p i) by (unfold stU; apply LPRE_fg_usage; exact LPX).
      assert (GD := KINV_grp_del stU LB _ g p KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact GNX)).
      rewrite RU in GD. specialize (GD ltac:(intros j Hj; destruct (Z.eq_dec j i) as [->|NE];
          [ split; [rewrite <- RU; exact (lp_nogroup _ _ _ _ _ _ LPU) | rewrite <- RU; exact (lp_noblock _ _ _ _ _ _ LPU)]
          | pose proof (free_slot_clear stU LB _ g p j KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact Hj) ltac:(rewrite RU; apply ALLFREE; [exact Hj| exact NE])) as FC;
            rewrite RU in FC; exact FC ])).
      fold stG in GD. destruct GD as (KIG & NGM & NSL).
      assert (MRG : rmrep stG m3) by (unfold stG; apply rmrep_grp_del_eq; apply rmrep_del_group; exact MR3).
      assert (FRG : ntf_frame st stG) by (unfold stG, stU; apply frame_grp_del; apply frame_fg_usage; exact FRX).
      assert (MSG : meta_slot stG g) by (unfold stG, stU; unfold meta_slot; rewrite grp_del_areas, fg_usage_areas; exact (go_slot _ _ _ GOX)).
      pose proof MWX as MWU. rewrite <- RU in MWU. pose proof GNX as GNU. rewrite <- RU in GNU.
      pose proof (go_mem _ _ _ GOX) as MEMU. rewrite <- RU in MEMU.
      replace (conc stX g) with (conc stG g) by (unfold stG; rewrite conc_grp_del; apply CU).
      change (get_meta_rec stU g) with (get_meta_rec stG g) in *.
      destruct (negb (m_maplen (get_meta_rec stG g) =? 0)) eqn:HML.
      -
        assert (MLNZ : m_maplen (get_meta_rec stG g) <> 0) by (intros E; rewrite E in HML; discriminate).
        rewrite free_meta_eq.
        eapply rimplT_evt.
        { eapply (rntf_top ra sp gp tp _ _ _ s0 _ ra _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 m3 junk ra s0 s1 s2 s3 stG stG g p _ lo);
            first [exact MRG | exact MI3 | exact MSG | exact MWU | exact MEMU | exact MLNZ | exact FR3 | exact ST3 | exact LO | exact LOLE | reflexivity
                  | apply munch_refl | apply wmono_refl | idtac].
          - pose proof (ki_cx _ _ _ KIG) as (SQ & _). exact SQ.
          - intros hd Hhd. eapply (kinv_fm_facts_raw stG LB _ g KIG); [exact GNU| exact Hhd]. }
        intros ms3 RP. apply KH.
        eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stG _ m m3); try exact RP.
        + destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
            (eapply rpres_except_mono; [exact PE3| exact FPX]).
        + intros a Ha. apply FPX. eapply (rfree_fp_frame stX stG lo (bv_unsigned sp) (bv_unsigned sp)); [| lia | exact Ha].
          unfold stG, stU. apply frame_grp_del. apply frame_fg_usage. apply frame_refl.
        + eexists. apply KINV_fm; [apply KINV_seq; exact KIG| | | |].
          * unfold meta_slot. replace (s_areas (record_seq _ (step_seq stG))) with (s_areas stG); [exact MSG|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * intros [b Hb]. apply NGM. exists b. unfold hosts in *.
            replace (s_groups (record_seq _ (step_seq stG))) with (s_groups stG) in Hb; [exact Hb|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * replace (get_meta_rec (record_seq _ (step_seq stG)) g) with (get_meta_rec stG g); [exact GNU|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * intros sx j. replace (s_slots (record_seq _ (step_seq stG))) with (s_slots stG); [apply NSL|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
        + apply ZINV_fm. apply ZINV_seq. unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
        +
          pose proof (KINV_seq _ _ _ (m_sizeclass (get_meta_rec stG g)) KIG) as KIS.
          pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6 & SR7 & SR8).
          set (stS := record_seq _ (step_seq stG)) in *.
          assert (GNS : m_next (get_meta_rec stS g) = None) by (unfold get_meta_rec; rewrite SR6; exact GNU).
          unfold fm_st. apply frame_queue.
          * apply frame_put_meta; [apply frame_seq; exact FRG| right; exact (hosts_is_gm _ _ _ HOSTS)].
          * apply links_put_meta0; [exact (ki_links _ _ _ KIS)| exact GNS].
          * cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 stS))) with (c_free_meta_head (ctx stS)).
            intros hd Hhd. destruct (kinv_free_head stS LB _ hd KIS Hhd) as (_ & NX' & _).
            rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; exact (NX' GNS)| exact NX'].
          * right; exact (hosts_is_gm _ _ _ HOSTS).
        +
          pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & FS2 & FS3 & _).
          destruct (go_region _ _ _ GOX) as (r & Hr & Kr & _ & _ & _ & TOP). rewrite <- RU in TOP.
          change (get_meta_rec stU g) with (get_meta_rec stG g) in TOP. destruct (TOP MLNZ) as [SND LEN].
          pose proof (go_maplen _ _ _ GOX) as MLR. rewrite <- RU in MLR. change (get_meta_rec stU g) with (get_meta_rec stG g) in MLR.
          unfold ntf_result. split; [| split; [reflexivity| split; [lia| split; [exact SND| split]]]].
          * unfold wz. f_equal. unfold conc, get_region. rewrite FS1, SR1. reflexivity.
          * exists r. rewrite FS1, SR1. unfold stG, stU. rewrite grp_del_regions, fg_usage_regions. auto.
          * intros b' gh Hb' E. rewrite FS3, SR3 in Hb'. unfold stG in Hb'. rewrite grp_del_groups in Hb'.
            apply lookup_delete_Some in Hb'. destruct Hb' as [NE Hb']. unfold stU in Hb'. rewrite fg_usage_groups in Hb'.
            apply NE. symmetry. eapply (top_region_clear stX LB c g p i KIX LPX); [rewrite <- RU; exact MLNZ | exact ALLFREE | exact Hb' | exact E].
        + eapply (oracle_ok_frame o m3 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
          eapply (roracle_ok_pres o m2 m3 stX lo (bv_unsigned sp)); [exact OOK2 | exact MRW | exact LO | exact PE3].
        + exact MRG.
        + pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & _). rewrite FS1, SR1. reflexivity.
        + pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (_ & SR2 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (_ & FS2 & _). rewrite FS2, SR2. reflexivity.
      -
        assert (MLZ : m_maplen (get_meta_rec stG g) = 0) by (destruct (Z.eqb_spec (m_maplen (get_meta_rec stG g)) 0); [assumption| discriminate]).
        pose proof (go_nest _ _ _ GOX) as NEST. rewrite <- RU in NEST. change (get_meta_rec stU g) with (get_meta_rec stG g) in NEST.
        destruct (NEST MLZ) as (g1 & i1 & b1 & SL1 & HB1 & FB1 & PSS & I1 & NF1 & LT1 & v3 & lo8 & hi8 & K3 & V31 & K2 & K1 & OFF).
        clear NEST.
        pose proof (ki_gmetas _ _ _ KIX b1 g1 HB1) as GO1.
        destruct (go_region _ _ _ GOX) as (r & Hr & Kr & SP0 & SP16 & SPAN & _).
        destruct (go_region _ _ _ GO1) as (r1 & Hr1 & _ & SB0 & SB16 & SPAN1 & _).
        rewrite FB1, Hr in Hr1. assert (r1 = r) by congruence. subst r1.
        assert (SNDP : snd p = sstart_of (get_meta_rec stX g1) i1) by (rewrite PSS, slot_start'_eq; reflexivity).
        assert (B1LT : snd b1 + 16 <= snd p).
        { rewrite SNDP. unfold sstart_of. rewrite (go_mem _ _ _ GO1). cbn [default id fst snd].
          pose proof (go_stride _ _ _ GO1) as [S16 _].
          assert (0 <= get_stride (get_meta_rec stX g1) * i1) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia). unfold UNIT in *. lia. }
        assert (NEb1 : b1 <> p) by (intros E; rewrite E in B1LT; lia).
        assert (HB1U : hosts stU b1 g1) by (unfold hosts in *; unfold stU; rewrite fg_usage_groups; exact HB1).
        assert (HB1G : hosts stG b1 g1) by (apply (proj2 (hosts_grp_del stU g p b1 g1)); split; [exact NEb1| exact HB1U]).
        pose proof (ki_h0 _ _ _ KIX g1 b1 i1 HB1 I1) as K4. rewrite <- SNDP, FB1 in K4.
        assert (PR : 0 <= snd p - 4 /\ snd p < round_up_pg (r_len r)).
        { split; [lia|]. pose proof (go_li _ _ _ GOX) as LIX. pose proof (go_stride _ _ _ GOX) as [S16 _].
          rewrite <- RU in LIX, S16. change (get_meta_rec stU g) with (get_meta_rec stG g) in LIX, S16.
          unfold sstart_of in SPAN. rewrite <- RU in SPAN. change (get_meta_rec stU g) with (get_meta_rec stG g) in SPAN.
          rewrite MEMU in SPAN. cbn [default id snd] in SPAN.
          assert (0 <= get_stride (get_meta_rec stG g) * (m_last_idx (get_meta_rec stG g) + 1)) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
          unfold UNIT, IB in *. lia. }
        destruct (rknown_byte stX mw (fst p, snd p - 4) r 0 MRW Hr Kr ltac:(cbn; lia) K4) as [_ _].
        unfold dec_hdr, get_meta. apply rimplT_guard. intros P16.
        apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
        assert (ESH : forall q, rdv pans_mem o stG q = rdv pans_mem o stX q).
        { intros q. unfold rdv. unfold get_shadow. unfold stG, stU. rewrite grp_del_shadow, fg_usage_shadow.
          unfold conc, get_region. rewrite grp_del_regions, fg_usage_regions. reflexivity. }
        rewrite !ESH.
        rewrite (rdv_known o stX (aadd p (-4)) 0) by (cbn [aadd fst snd]; replace (snd p + -4) with (snd p - 4) by lia; exact K4).
        rewrite (rdv_known o stX (aadd p (-3)) v3) by (cbn [aadd fst snd]; replace (snd p + -3) with (snd p - 3) by lia; exact K3).
        rewrite (rdv_known o stX (aadd p (-2)) lo8) by (cbn [aadd fst snd]; replace (snd p + -2) with (snd p - 2) by lia; exact K2).
        rewrite (rdv_known o stX (aadd (aadd p (-2)) 1) hi8) by (cbn [aadd fst snd]; replace (snd p + -2 + 1) with (snd p - 1) by lia; exact K1).
        cbn [Z.eqb negb].
        set (off16 := lo8 + 256 * hi8).
        assert (EB : aadd p (- (UNIT * off16) - UNIT) = b1).
        { unfold aadd, UNIT, off16. rewrite <- FB1. apply injective_projections; cbn; [reflexivity| lia]. }
        rewrite EB. unfold get_group.
        replace (s_groups stG !! b1) with (s_groups stX !! b1).
        2:{ unfold stG, stU. rewrite grp_del_groups, lookup_delete_ne, fg_usage_groups by congruence. reflexivity. }
        destruct HB1 as [ai1 Hgh1]. rewrite Hgh1. cbn [g_meta].
        apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
        apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
        assert (EU1 : get_meta_rec stU g1 = get_meta_rec stX g1) by (unfold stU; apply fg_usage_rec).
        change (get_meta_rec stG g1) with (get_meta_rec stU g1) in G11, G12, G13, G14, G15, G16, G17 |- *.
        rewrite ?EU1 in G11. rewrite ?EU1 in G12. rewrite ?EU1 in G13. rewrite ?EU1 in G14. rewrite ?EU1 in G16. rewrite ?EU1 in G17. rewrite ?EU1.
        destruct (s_areas stG !! area_of g1) as [ar1|] eqn:AR1; [|discriminate].
        apply Z.eqb_eq in G15. change (c_secret (ctx stG)) with (c_secret (ctx stU)) in G15.
        apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
        assert (ERU : s_regions stU = s_regions stX) by (unfold stU; apply fg_usage_regions).
        assert (ESU : s_shadow stU = s_shadow stX) by (unfold stU; apply fg_usage_shadow).
        assert (KB : forall k v, 1 <= k <= 4 -> cell_read (get_shadow stX (fst p)) (snd p - k) = Known v ->
                   bytes_at psegs m3 (conc stU p - k) [b8 v] /\ 0 <= v < 256).
        { intros kk v Hk Hc. destruct (rknown_byte stU m3 (fst p, snd p - kk) r v MR3 ltac:(cbn; rewrite ERU; exact Hr) Kr ltac:(cbn; lia)
                   ltac:(cbn; unfold get_shadow; rewrite ESU; exact Hc)) as [B V].
          cbn [fst snd] in B. rewrite (conc_region' stU (fst p, snd p - kk) r) in B by (cbn; rewrite ERU; exact Hr). cbn [snd] in B.
          rewrite (conc_region' stU p r) by (rewrite ERU; exact Hr). split; [| exact V].
          replace (r_base r + snd p - kk) with (r_base r + (snd p - kk) + 0) by lia. exact B. }
        destruct (KB 4 0 ltac:(lia) K4) as [Y4 _]. destruct (KB 3 v3 ltac:(lia) K3) as [Y3 R3].
        destruct (KB 2 lo8 ltac:(lia) K2) as [Y2 R2]. destruct (KB 1 hi8 ltac:(lia) K1) as [Y1 R1]. clear KB.
        assert (HDR : bytes_at psegs m3 (conc stU p - 4) [b8 0; b8 v3; b8 lo8; b8 hi8]).
        { change [b8 0; b8 v3; b8 lo8; b8 hi8] with ([b8 0] ++ ([b8 v3] ++ ([b8 lo8] ++ [b8 hi8]))).
          apply bytes_at_app. split; [exact Y4|]. apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1) with (conc stU p - 3) by lia; exact Y3|].
          apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1 + 1) with (conc stU p - 2) by lia; exact Y2|].
          cbn. replace (conc stU p - 4 + 1 + 1 + 1) with (conc stU p - 1) by lia. exact Y1. }
        destruct HOSTSX as [aig Hghp].
        eapply rimplT_evt.
        { eapply (rntf_nest_call ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stU g p b1 g1 (mkGhdr (Some g) aig) (mkGhdr (Some g1) ai1) ar1 v3 lo8 hi8 off16 lo).
          all: first [exact MR3 | exact MI3 | exact MWU | exact MLZ | exact MEMU | exact HDR | exact FR3 | exact ST3 | exact LO | exact LOLE
                     | exact R3 | exact R2 | exact R1 | exact AR1 | exact G15 | exact INIU | apply rntf_frame_size | idtac].
          all: try reflexivity.
          all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GO1)).
          all: rewrite ?EU1.
          all: try exact (go_mem _ _ _ GO1); try exact (go_avail _ _ _ GO1); try exact (go_freed _ _ _ GO1);
               try exact G12; try exact G13; try exact G14; try exact (proj2 (proj2 (proj2 (ki_cx _ _ _ KIU)))).
          all: try (pose proof (go_li _ _ _ GO1); pose proof (go_freeable _ _ _ GO1); pose proof (go_sc _ _ _ GO1); pose proof (go_maplen _ _ _ GO1); lia).
          all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GOX)).
          all: try (unfold stU; rewrite fg_usage_groups; first [exact Hghp | exact Hgh1]).
          all: try (symmetry; exact EB).
          all: match goal with
               | |- forall _, _ <= _ < 12 -> _ => intros oo Ho; unfold get_shadow; rewrite ESU; exact (ki_unk _ _ _ KIX p _ oo Hghp Ho)
               | |- _ < 48 -> _ => intros Hsc; apply Z.ltb_lt in Hsc; rewrite Hsc in G16; apply andb_true_iff in G16; destruct G16 as [G16a G16b];
                                   apply Z.leb_le in G16a; apply Z.ltb_lt in G16b; fold off16 in G16a, G16b; lia
               | |- _ <> 0 -> _ => intros Hml; destruct (Z.eqb_spec (m_maplen (get_meta_rec stX g1)) 0); [lia|]; cbn [negb] in G17; apply Z.leb_le in G17;
                                   fold off16 in G17; unfold UNIT in G17;
                                   replace (m_maplen (get_meta_rec stX g1) * 4096) with (m_maplen (get_meta_rec stX g1) * 256 * 16) in G17 by lia;
                                   rewrite Z.div_mul in G17 by lia; lia
               | |- ?G => idtac "NCGOAL" G; fail
               end. }
        intros ms3 NC. unfold rnest_call_post in NC.
        destruct NC as (z0 & z1 & z2 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
        fold stG in MR4.
        pose proof (bv_unsigned_in_range _ sp) as SPR'.
        assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp - 96) by (unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in LO; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; rewrite unsigned_lit; lia).
        rewrite V31. replace (conc stU g1) with (conc stG g1) by reflexivity.
        eapply (IH R _ bail s Q (Z_to_bv 64 0x20cf8) (Z_to_bv 64 (bv_unsigned sp + -96)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 stG g1 b1 i1 (m_sizeclass (get_meta_rec stX g) + 1) (g :: Zs)).
        + exact KIG.
        + constructor.
          * exact HB1G.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact I1.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact NF1.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS. unfold stG. rewrite grp_del_groups. apply lookup_delete_eq.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS.
            apply Forall_forall. intros blk Hblk E. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ KIX) blk Hblk) as BK.
            pose proof (bk_nogroup _ _ BK) as NG. rewrite E, Hghp in NG. discriminate.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1.
            pose proof LT1 as LT1'. first [rewrite RU in LT1' | change (get_meta_rec stG g) with (get_meta_rec stU g) in LT1'; rewrite RU in LT1']. lia.
        + unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
        + exact INIU.
        + exact MR4.
        + exact MI4.
        + apply (oracle_ok_frame o m4 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
          eapply (roracle_ok_pres o m2 m4 stX lo (bv_unsigned sp) mw); [exact OOK2 | exact MRW | exact LO |].
          eapply rpres_except_trans; [exact PE3|]. eapply rpres_except_mono; [exact PE4|].
          intros a Ha. eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha].
        + rewrite SPU. exact ST4.
        + rewrite SPU. lia.
        +
          intros st3 mi ms5 NQ. rewrite free_meta_eq.
          unfold rntf_q in NQ. rewrite SPU in NQ.
          destruct NQ as (u0 & u1 & u2 & ra0' & ra1' & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m5 & -> & MI5 & ST5 & MR5 & PE5 & [c3 KI3] & ZI3 & FR35 & RES5 & OOK5).
          replace (ret_pc (Z_to_bv 64 0x20cf8)) with (Z_to_bv 64 0x20cf8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
          assert (RG3 : get_meta_rec st3 g = get_meta_rec stG g).
          { apply (nf_metas _ _ FR35). intros [L|L]; [exact (L GNU)| exact (NGM L)]. }
          assert (NGM3 : ~ is_gm st3 g).
          { intros [b [ai Hb]]. apply NGM. exists b, ai. apply (nf_groups _ _ FR35). exact Hb. }
          eapply rimplT_evt.
          { eapply (rntf_nest_ret sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 junk ra s0 s1 s2 s3 stU st3 g lo);
              first [exact MR5 | exact MI5 | exact LO | exact LOLE | reflexivity | idtac].
            - unfold meta_slot. rewrite (nf_areas _ _ FR35). exact MSG.
            - intros hd Hhd. eapply (kinv_fm_facts_raw st3 LB c3 g KI3); [rewrite RG3; exact GNU| exact Hhd].
            - unfold conc, get_region. rewrite (nf_regions _ _ FR35). reflexivity.
            - eapply rpres_except_rw_cells; [exact PE5 | exact FR4 |].
              intros a Ha Hfp. pose proof (rfree_fp_lt stG m4 lo (bv_unsigned sp - 96) a MR4 LO ltac:(lia) Hfp). lia.
            - exact ST5. }
          intros ms6 RP. apply KH.
          pose proof (frame_trans _ _ _ FRG FR35) as FR03.
          pose proof (fm_shape st3 g) as (FS1 & FS2 & FS3 & FS4 & FS5 & FS6).
          eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st3 _ m m5); try exact RP.
          * destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
              (eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE3| exact FPX]|]);
              (eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE4| intros a Ha; apply FPX; eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha]]|]);
              (eapply rpres_except_mono; [exact PE5| intros a Ha; eapply (rfree_fp_frame st stG lo (bv_unsigned sp) (bv_unsigned sp - 96)); [exact FRG| lia| exact Ha]]).
          * intros a Ha. eapply (rfree_fp_frame st st3 lo (bv_unsigned sp) (bv_unsigned sp)); [exact FR03| lia| exact Ha].
          * exists c3. apply KINV_fm; [exact KI3| unfold meta_slot; rewrite (nf_areas _ _ FR35); exact MSG| exact NGM3| rewrite RG3; exact GNU|].
            intros sx j Hs. apply (NSL sx j). apply (nf_slots _ _ FR35). exact Hs.
          * apply ZINV_fm. exact ZI3.
          * unfold fm_st. apply frame_queue.
            -- apply frame_put_meta; [exact FR03| right; exact (hosts_is_gm _ _ _ HOSTS)].
            -- apply links_put_meta0; [exact (ki_links _ _ _ KI3)| rewrite RG3; exact GNU].
            -- cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 st3))) with (c_free_meta_head (ctx st3)).
               intros hd Hhd. destruct (kinv_free_head st3 LB _ hd KI3 Hhd) as (_ & NX' & _).
               rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; apply NX'; rewrite RG3; exact GNU| exact NX'].
            -- right; exact (hosts_is_gm _ _ _ HOSTS).
          * destruct mi as [[bb len]|]; [| exact RES5].
            destruct RES5 as (A0 & A1 & LEN & SND & (rr & Hrr & Krr & Lrr) & NOG).
            unfold ntf_result. split; [rewrite A0; unfold wz; f_equal; unfold conc, get_region; rewrite FS1; reflexivity|].
            split; [exact A1|]. split; [exact LEN|]. split; [exact SND|]. split; [exists rr; rewrite FS1; auto|].
            intros b' gh Hb'. rewrite FS3 in Hb'. exact (NOG b' gh Hb').
          * exact OOK5.
          * exact MR5.
          * exact FS1.
          * exact FS2. }
    assert (FGX : forall stX m4 junk (z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 : word) ms4,
      KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
      data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) ->
      s_regions stX = s_regions st -> s_shadow stX = s_shadow st -> s_groups stX = s_groups st ->
      (m_sizeclass (get_meta_rec stX g) < 48 -> 0 <= usage stX (m_sizeclass (get_meta_rec stX g)) < 2^64) ->
      rpres_except (rfree_fp st lo (bv_unsigned sp)) m m4 -> wmono psegs m m4 -> mem_inv psegs m4 ->
      stk psegs m4 lo (bv_unsigned sp + -96) -> rw_cells psegs m4 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) -> rmrep stX m4 ->
      ms4 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp z0 z1 z2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
               F (Z_to_bv 64 0x20c98) fc None m4 (seg_rom psegs) ->
      rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms4).
    { intros stX m4 junk z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 ms4 KIX ZIX LPX FRX GNX DATX ERX ESX EGX USX PE4 WM4 MI4 ST4 FR4 MR4 ->.
      pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX.
      assert (CX : conc st g = conc stX g) by (unfold conc, get_region; rewrite ERX; reflexivity). rewrite CX.
      eapply rimplT_evt.
      { eapply (rntf_fg ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m4 _ stX g lo);
          first [exact MR4 | exact MI4 | exact (go_slot _ _ _ GOX) | exact (gmeta_mw _ _ _ GOX) | exact USX | exact FR4 | apply rntf_frame_size | exact ST4 | exact LO | exact LOLE]. }
      intros ms5 FGP.
      eapply (FG2 stX m4 junk); [exact KIX | exact ZIX | exact LPX | exact FRX | exact GNX | right; exact PE4 | exact FGP | | exact WM4 | | exact DATX | exists m4; exact MR4].
      - intros a Ha. eapply (rfree_fp_same st stX); eauto.
      - apply (oracle_ok_frame o m4 st stX); [| exact ERX | exact ESX].
        eapply (roracle_ok_pres o m m4 st lo (bv_unsigned sp) m); [exact OOK | exact MR | exact LO | exact PE4]. }
    destruct (m_next (get_meta_rec st g)) as [nx|] eqn:NX.
    +
      apply rimplT_guard. intros SC48b. apply Z.ltb_lt in SC48b. cbv zeta.
      set (sc := m_sizeclass (get_meta_rec st g)) in *.
      set (an := optr_eqb (active st sc) (Some g)).
      set (stm := deq_mid (LActive sc) g st).
      set (st1 := dequeue (LActive sc) g st).
      assert (E1 : st1 = upd_meta g clr_links stm) by (unfold st1, stm; apply dequeue_mid).
      pose proof (deq_mid_shape st (LActive sc) g) as SBLm. fold stm in SBLm.
      pose proof (sbl_dequeue st (LActive sc) g) as SBL1. fold st1 in SBL1.
      assert (KI1 : KINV st1 LB c) by (unfold st1; eapply (KINV_dequeue st LB c g p sc nx); eauto).
      assert (ZI1 : ZINV st1 Zs) by (unfold st1; apply ZINV_dequeue; exact ZI).
      assert (LP1 : LPRE st1 LB c g p i) by (eapply LPRE_sbl; [exact SBL1| exact LP]).
      assert (FR1' : ntf_frame st st1).
      { unfold st1. apply frame_dequeue; [apply frame_refl| exact (ki_links _ _ _ KI)| right; exact (hosts_is_gm _ _ _ HOSTS)]. }
      destruct (kinv_next _ _ _ _ _ KI NX) as (MSnx & Pnx & Nnx & pv & PV & MSpv & Npv & NEpv).
      pose proof (dequeue_shape st g sc nx pv NX PV) as DS. cbv zeta in DS. fold st1 in DS.
      destruct DS as (DSdata & GN1 & GP1 & _).
      assert (DQ2 : forall m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 : word) ms2,
        munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 -> wmono psegs m m2 ->
        rat9c_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 (pw st (active st sc)) x5 x6 x7 x3 x4 x8 x9 F fc lo st m2 stm g sc
                   (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
        rimplT o (match an, active st1 sc with
                 | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail
                 | _, _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail
                 end) s Q ms2).
      { intros m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 ms2 PRE WM2 AP.
        unfold rat9c_post in AP. destruct AP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
        assert (PE03 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
        { destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE3]| eapply rpres_except_trans; [exact PE0| exact PE3]]. }
        assert (HA3 : if an then bv_unsigned (pw st (active st sc)) = conc stm g else bv_unsigned (pw st (active st sc)) <> conc stm g).
        { pose proof (rmeta_slot_bounds st m g MR MSL) as (B0 & B1 & _). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in B1; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
          rewrite (conc_sbl _ _ g SBLm). subst an. destruct (active st sc) as [h|] eqn:Hh; cbn [optr_eqb].
          - destruct (aptr_eqb_spec' h g); [subst; unfold pw, wz; cbn [oconc]; rewrite unsigned_lit by lia; reflexivity|].
            pose proof (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))) as MSh. pose proof (rmeta_slot_bounds st m h MR MSh) as (C0 & C1 & _). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in C1; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
            unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. intros E. apply n. apply (rconc_meta_inj st m g h MR MSL MSh). exact E.
          - unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. lia. }
        assert (PDQ : forall (avz : an = true -> forall a, active st1 sc = Some a -> m_avail (get_meta_rec st1 a) = 0),
          evt psegs (rat00_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 x2 x3 x4 x8 x9 F fc lo stm m3 (pd_st an st1 sc) g (rntf_frame junk s3 s2 s1 s0 ra))
            (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x20c34) fc None m3 (seg_rom psegs))).
        { intros avz. rewrite <- (conc_sbl _ _ g SBLm). rewrite E1.
          eapply (rntf_postdeq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stm g sc lo an);
            first [exact MR3 | exact MI3 | exact HA3 | exact FR3 | apply rntf_frame_size | exact ST3 | exact LO | exact LOLE | idtac].
          - eapply meta_slot_sbl; [exact SBLm| exact MSL].
          - pose proof (go_sc _ _ _ GO). subst sc. lia.
          - rewrite <- E1. intros AN a A1. specialize (avz AN a A1).
            destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
            destruct GMa as [ba Hba]. pose proof (ki_gmetas _ _ _ KI1 ba a Hba) as GOa.
            destruct Hba as [ai Hgh]. pose proof (ki_grps _ _ _ KI1 ba _ Hgh) as (g' & Eg' & AI). cbn in Eg', AI. inversion Eg'; subst g'.
            split; [exact MSa|]. split; [intros ->; exact (Na GN1)|]. split; [exact avz|]. split; [exact (go_freed _ _ _ GOa)|].
            exists ba, (mkGhdr (Some a) ai). split; [exact (go_mem _ _ _ GOa)|]. split; [exact Hgh|]. cbn. pose proof (go_li _ _ _ GOa). lia. }
        assert (AVK : forall a, an = true -> active st1 sc = Some a ->
                 rimplT o (activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail) s Q
                   (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x20c34) fc None m3 (seg_rom psegs))).
        { intros a AN A1. apply rimplT_guard. intros AV0. apply Z.eqb_eq in AV0. cbv zeta.
          change (upd_meta a _ st1) with (act_st st1 a (act_of st1 a)).
          set (stA := act_st st1 a (act_of st1 a)).
          destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
          assert (NEa : a <> g) by (intros ->; exact (Na GN1)).
          eapply rimplT_evt; [apply PDQ; intros _ a' A1'; rewrite A1 in A1'; inversion A1'; subst; exact AV0|].
          intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
          assert (EP : pd_st an st1 sc = stA) by (unfold pd_st; rewrite AN, A1; reflexivity). rewrite EP in MR4.
          rewrite (conc_sbl _ _ g SBLm).
          eapply (FGX stA m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4.
          - unfold stA. apply KINV_act; [exact KI1| exact GMa| exact AV0| apply act_of_nonneg].
          - unfold stA. apply ZINV_act. exact ZI1.
          - unfold stA, act_st. apply LPRE_upd_other; [exact NEa| exact LP1].
          - unfold stA. apply frame_act; [exact FR1'| eapply (LG_frame st st1 a FR1'); left; exact Na].
          - unfold stA. rewrite act_st_rec_other by congruence. exact GN1.
          - unfold stA. rewrite act_st_rec_other by congruence. apply DSdata.
          - unfold stA. rewrite act_st_regions. apply (sbl_regions _ _ SBL1).
          - unfold stA. rewrite act_st_shadow. apply (sbl_shadow _ _ SBL1).
          - unfold stA. rewrite act_st_groups. apply (sbl_groups _ _ SBL1).
          - unfold stA. rewrite act_st_rec_other by congruence. intros Hsc. unfold usage. cbn [ctx act_st upd_meta put_meta set_metas s_ctx].
            change (default 0 (c_usage (s_ctx st1) !! m_sizeclass (get_meta_rec st1 g))) with (usage st1 (m_sizeclass (get_meta_rec st1 g))).
            apply (ki_usage _ _ _ KI1). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
          - eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
          - eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
        assert (NOACT : (an = false \/ active st1 sc = None) ->
                 rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail) s Q
                   (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x20c34) fc None m3 (seg_rom psegs))).
        { intros NA.
          eapply rimplT_evt; [apply PDQ; intros AN a' A1'; exfalso; destruct NA as [NA|NA]; congruence|].
          intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
          assert (EP : pd_st an st1 sc = st1) by (unfold pd_st; destruct NA as [-> | NA]; [reflexivity| rewrite NA; destruct an; reflexivity]).
          rewrite EP in MR4.
          rewrite (conc_sbl _ _ g SBLm).
          eapply (FGX st1 m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4; try exact KI1; try exact ZI1; try exact LP1; try exact FR1'; try exact GN1.
          - apply DSdata.
          - apply (sbl_regions _ _ SBL1).
          - apply (sbl_shadow _ _ SBL1).
          - apply (sbl_groups _ _ SBL1).
          - intros Hsc. rewrite (sbl_usage _ _ SBL1). apply (ki_usage _ _ _ KI). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
          - eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
          - eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
        destruct an eqn:AN; [destruct (active st1 sc) as [a|] eqn:A1; [apply (AVK a eq_refl eq_refl)| apply NOACT; right; reflexivity] | apply NOACT; left; reflexivity]. }
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence| exact SC48b]|].
      intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
      destruct CASES as [D|[D|[D|[D|D]]]];
        try (exfalso; destruct D as (D1 & D2 & D3); congruence).
      *
        destruct D as (_ & NXg & _ & x0 & x1 & x2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
        assert (Enx : nx = g) by congruence.
        eapply rimplT_evt.
        { eapply (rntf_deqself ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g sc lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - rewrite NX, Enx. reflexivity. }
        intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
      *
        destruct D as (_ & _ & nx' & NX' & NE & x0 & x1 & x2 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
        assert (Enx : nx' = nx) by congruence. subst nx'.
        eapply rimplT_evt.
        { eapply (rntf_deq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g nx pv sc lo);
            first [exact MR1 | exact MI1 | exact MSL | exact NX | exact PV | exact NE | exact MSnx | exact MSpv | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | reflexivity | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - apply NEpv. exact NE.
          - destruct (active st sc) as [h|] eqn:Hh; [right| left; reflexivity]. exists h. split; [reflexivity|].
            exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))). }
        intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
    +
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
      intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
      destruct CASES as [D|[D|[D|[D|D]]]];
        try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as (nx0 & D3 & _); congruence).
      destruct D as (_ & _ & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
      eapply (FGX st m1 junk); [exact KI | exact ZI | exact LP | apply frame_refl | exact NX | reflexivity | reflexivity | reflexivity | reflexivity
                               | | eapply rpres_except_entry; eauto | exact WM | exact MI1 | exact ST1 | exact FR1 | exact MR1 | reflexivity].
      intros Hsc. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP).
  - destruct (Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) =? 0) eqn:HM.
    +
      apply Z.eqb_eq in HM.
      apply rimplT_guard. intros SC48. apply Z.ltb_lt in SC48.
      assert (QTAIL : forall m1 junk stq (x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x : word),
        munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 -> wmono psegs m m1 ->
        stq = (if optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g) then st else queue_st (LActive (m_sizeclass (get_meta_rec st g))) g st) ->
        (active st (m_sizeclass (get_meta_rec st g)) <> Some g -> m_next (get_meta_rec st g) = None /\ m_prev (get_meta_rec st g) = None) ->
        forall ms2, rqpath_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) (wz (sxv (2 ^ i))) s2x s3 s4 s5 s6 s7 s8 s9 s10 s11
                      x0 x1 x2 x6 x7 x3 x4 x5 x8 F fc lo st g m1 stq (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
        rimplT o (k (aor_st stq g i) None) s Q ms2).
      { intros m1 junk stq x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x MU WM Estq GNP ms2 QP.
        assert (SBL : same_but_links st stq) by (rewrite Estq; destruct (optr_eqb _ _); [apply sbl_refl| apply sbl_queue]).
        assert (ZIq : ZINV stq Zs) by (apply (ZINV_sbl st stq Zs SBL); exact ZI).
        assert (KIq : KINV stq LB c).
        { rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [exact KI|].
          apply (KINV_queue st LB c g p _ KI HOSTS eq_refl ltac:(pose proof (go_sc _ _ _ GO); lia)).
          - apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
          - apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
          - intros E. rewrite E, optr_eqb_refl in HA. discriminate. }
        assert (FRq : ntf_frame st stq).
        { rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [apply frame_refl|].
          apply frame_queue; [apply frame_refl| apply (ki_links _ _ _ KI)| | right; exact (hosts_is_gm _ _ _ HOSTS)].
          cbn [get_head]. intros hd Hhd. exact (proj1 (proj2 (proj2 (kinv_active _ _ _ _ _ KI Hhd)))). }
        unfold rqpath_post in QP. cbv beta in QP.
        destruct QP as (qa0 & qa2 & qa3 & qa5 & m2 & -> & PE2 & WM2 & MI2 & ST2 & FR2 & MR2).
        pose proof (LPRE_sbl _ _ _ _ _ _ _ SBL LP) as LPq.
        rewrite <- (conc_sbl st stq g SBL).
        eapply rimplT_evt.
        { eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 junk ra s0 s1 s2 s3 stq g i lo);
            first [exact MR2 | exact MI2 | reflexivity | exact FR2 | exact ST2 | exact LO | exact LOLE | idtac].
          - eapply meta_slot_sbl; [exact SBL| exact MSL].
          - pose proof (go_li _ _ _ GO). lia.
          - destruct (data_of_fields st stq g (sbl_data _ _ SBL g)) as (_ & _ & -> & _). exact (go_freed _ _ _ GO). }
        intros ms3 RP. apply KH.
        eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stq _ m m2); try exact RP.
        * eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
        * intros a Ha. eapply (rfree_fp_frame st stq lo (bv_unsigned sp) (bv_unsigned sp)); [exact FRq| lia| exact Ha].
        * exists c. apply (KINV_aor _ _ _ _ _ _ KIq LPq).
        * apply ZINV_aor. exact ZIq.
        * apply frame_aor; [exact FRq| right; exact (hosts_is_gm _ _ _ HOSTS)].
        * exact eq_refl.
        * apply (oracle_ok_frame o m2 st stq); [| exact (sbl_regions _ _ SBL) | exact (sbl_shadow _ _ SBL)].
          eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO|].
          eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
        * exact MR2.
        * reflexivity.
        * reflexivity. }
      destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; cbn [negb].
      *
        assert (HAct : active st (m_sizeclass (get_meta_rec st g)) = Some g).
        { destruct (active st _) as [h|]; [|discriminate]. cbn in HA. apply aptr_eqb_eq in HA. congruence. }
        eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence | lia | exact HAct]|].
        intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
        destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
        destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
        eapply rimplT_evt.
        { eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - right. exists g. split; [exact HAct| exact MSL].
          - intros NE. exfalso. exact (NE HAct).
          - intros hd Hhd NE. exfalso. apply NE. congruence. }
        intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
        eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros NE; exfalso; exact (NE HAct)| exact QP].
      *
        assert (HAct : active st (m_sizeclass (get_meta_rec st g)) <> Some g).
        { intros E. rewrite E in HA. cbn in HA. rewrite aptr_eqb_refl in HA. discriminate. }
        apply rimplT_queue. intros GN GPV.
        eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence | lia]|].
        intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
        destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as [D3 _]; congruence).
        destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
        eapply rimplT_evt.
        { eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - destruct (active st (m_sizeclass (get_meta_rec st g))) as [h|] eqn:Hh; [right| left; reflexivity].
            exists h. split; [reflexivity|]. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))).
          - intros _. split; assumption.
          - intros hd Hhd NE. destruct (kinv_active _ _ _ _ _ KI Hhd) as (_ & Shd & Nhd & _ & _ & pv & Ppv & Spv & Npv).
            split; [exact Shd|]. exists pv. split; [exact Ppv|]. split; [| exact Spv]. intros ->. rewrite GN in Npv. discriminate. }
        intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
        eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros _; split; assumption| exact QP].
    +
      apply Z.eqb_neq in HM.
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
      intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
      destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
      destruct D as (_ & _ & x0 & x1 & x2 & y0 & y2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
      eapply rimplT_evt.
      { eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 junk ra s0 s1 s2 s3 st g i lo);
          first [exact MR1 | exact MI1 | exact MSL | reflexivity | exact FR1 | exact ST1 | exact LO | exact LOLE | idtac].
        - pose proof (go_li _ _ _ GO). lia.
        - exact (go_freed _ _ _ GO). }
      intros ms2 RP. apply KH.
      eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st _ m m1); try exact RP.
      * eapply rpres_except_entry; eauto.
      * auto.
      * exists c. apply (KINV_aor _ _ _ _ _ _ KI LP).
      * apply ZINV_aor. exact ZI.
      * apply frame_aor; [apply frame_refl| right; exact (hosts_is_gm _ _ _ HOSTS)].
      * exact eq_refl.
      * eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO| eapply rpres_except_entry; eauto].
      * exact MR1.
      * reflexivity.
      * reflexivity.
Qed.
End NTF.
End WithCeiling0.
End RF_ntf.


Module RF_free_K.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import F_malloc_free MallocBlocks MallocFacts_B MallocKit_B MallocModel_B MallocKit_B3 MallocFacts_Bpres.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require F_free.
Export OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc.F_free.F_free_K.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RMallocRep RMallocTree RMallocKit_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require RF_ntf_C.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_ntf_C.RMallocKit_B3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Local Open Scope Z_scope.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rfree_fp_hdr_st st pf lo (sp sp' : Z) a : ticks_ok st ->
  (forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
  sp' <= sp -> rfree_fp (hdr_st st pf) lo sp' a -> rfree_fp st lo sp a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros TK HK HS H. destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
  - right; left. exact H.
  - right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
    exists rid, r, w. auto.
Qed.


Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

Lemma rdrop_regions : s_regions st' = delete rid (s_regions st). Proof. reflexivity. Qed.
Lemma rdrop_shadow : s_shadow st' = delete rid (s_shadow st). Proof. reflexivity. Qed.
Lemma rconc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rpw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite rconc_drop by exact H. reflexivity. Qed.
Lemma rget_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rrec_drop q : get_meta_rec st' q = get_meta_rec st q. Proof. reflexivity. Qed.

Lemma rmeta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). destruct (PM q) as (P1 & P2 & P3).
  unfold meta_cells. rewrite !rpw_drop by assumption. reflexivity.
Qed.

Lemma rctx_head_cells_drop : rctx_head_cells st' = rctx_head_cells st.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold rctx_head_cells. change (ctx st') with (ctx st).
  rewrite !rpw_drop by assumption. reflexivity.
Qed.
Lemma ractives_drop : actives st' = actives st.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
  change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply rpw_drop. apply PA.
Qed.
Lemma rctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
  destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (rconc_drop (brid, boff)) by exact PB. reflexivity.
Qed.

Lemma rmrep_drop_region m : rmrep st m -> rmrep st' m.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros MR. pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact Hres|]. split; [|split; [|split]].
    + intros k r Hk. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. apply (WR k r). tauto.
    + intros k1 r1 k2 r2 H1 H2 NE. cbn [st' drop_region s_regions set_shadow set_regions] in H1, H2.
      apply lookup_delete_Some in H1. apply lookup_delete_Some in H2. apply (DJ k1 r1 k2 r2); tauto.
    + intros a ar Ha. destruct (PAR a ar Ha) as [Pa _]. destruct (WA a ar Ha) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_areas]. rewrite lookup_delete_ne by congruence. auto.
    + intros b gh Hb. destruct (PG b gh Hb) as [Pb _]. destruct (WG b gh Hb) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_groups]. rewrite lookup_delete_ne by congruence. auto.
  - unfold rmrep_ctx. rewrite rctx_head_cells_drop, ractives_drop, rctx_tail_cells_drop.
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st). exact CX.
  - exact GL.
  - intros a ar Ha. destruct (PAR a ar Ha) as [Pa Pn]. destruct (AR a ar Ha) as (A1 & A2 & A3).
    unfold rarea_rep. rewrite (rconc_drop a) by exact Pa. rewrite rpw_drop by exact Pn. split; [exact A1|]. split; [| exact A3].
    intros k Hk. rewrite rrec_drop, rmeta_cells_drop. apply A2. exact Hk.
  - intros b gh Hb. destruct (PG b gh Hb) as [Pb Pm]. destruct (GR b gh Hb) as (w8 & R & Hw). exists w8.
    rewrite (rconc_drop b) by exact Pb. rewrite rpw_drop by exact Pm. auto.
  - intros k r Hk Kr. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
    unfold rshadow_rep. rewrite rget_shadow_drop by congruence. exact (SH k r Hk Kr).
Qed.
End DROP.

Lemma rptrs_in_norid st2 LB c rid r m :
  KINV st2 LB c -> ZINV st2 [] -> rmrep st2 m ->
  (s_regions st2) !! rid = Some r -> r_kind r = RKGroup ->
  (forall b gh, (s_groups st2) !! b = Some gh -> fst b <> rid) ->
  ci_mptrs st2 ->
  ptrs_in (fun x => x <> rid) st2.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros K ZI MR Hr Kr NOG (M1 & M2 & M3 & M4 & M5).
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
  { intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
    rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
  assert (OM : forall p, (forall q, p = Some q -> meta_slot st2 q) -> optr_in (fun x => x <> rid) p).
  { intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
  pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
  unfold ptrs_in. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
  - apply OM. intros h Hh. exact (proj1 (kinv_free_head st2 LB c h K Hh)).
  - apply NGr. exact M1.
  - apply NGr. exact M2.
  - apply NGr. exact M3.
  - apply NGr. exact M4.
  - intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st2 LB c sc a K Ha))).
  - destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB; try exact I.
    intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
  - intros g. split; [| split].
    + apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
    + apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
    + destruct (m_mem (get_meta_rec st2 g)) as [b|] eqn:MB; cbn; [| exact I].
      destruct (ZI g b MB) as [[ai Hb]|[]]. exact (NOG b _ Hb).
  - intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
    intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
  - intros b gh Hb. split; [exact (NOG b gh Hb)|].
    destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
    assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
    exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.
End WithCeiling0.
End RF_free_K.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_free.RF_free_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_free.RF_free_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_free.RF_free_C OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_free.RF_ntf OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP.RF_free.RF_free_K.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition rfree_end (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (LB' : list block) (m : mem) (errv : word) (s : PState)
    (st' : mstate) (s' : PState) : machine_state -> Prop :=
  fun ms' => s' = s /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st' m'
    /\ rpres_except (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st' a \/ 238572 <= a < 238576) m m'
    /\ (forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r')
    /\ (forall blk', In blk' LB' -> exists r', (s_regions st') !! (fst (blk_slot blk')) = Some r')
    /\ c_brk (ctx st') = c_brk (ctx st)
    /\ (forall brid boff, c_brk (ctx st) = BrkLive brid boff -> (s_regions st') !! brid = (s_regions st) !! brid).

Lemma rerrno_not_free_fp st m lo (sp : Z) a : rmrep st m -> alloc_ceiling <= lo -> 238572 <= a < 238576 -> ~ rfree_fp st lo sp a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros MR LO Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in LO; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  intros [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - destruct A as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
  - destruct A as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
Qed.

Lemma rmrep_after_munmap st2 rid r2 m4 m5 (slo shi : Z) :
  rmrep (drop_region rid st2) m4 -> rmrep st2 m4 ->
  (s_regions st2) !! rid = Some r2 -> r_kind r2 = RKGroup ->
  munch [(slo, shi); (238572, 238576); (r_base r2, r_base r2 + round_up_pg (r_len r2))]%Z m4 m5 ->
  alloc_ceiling <= slo ->
  rmrep (drop_region rid st2) m5.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros MRd MR Hr Kr MU LO. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in LO; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  pose proof (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  eapply rmrep_transport_agree'; [exact MRd|]. intros a Ha HF. apply MU. rewrite wa_unsigned by lia.
  assert (LOW : a < alloc_ceiling /\ ~ (238572 <= a < 238576) /\ ~ (r_base r2 <= a < r_base r2 + round_up_pg (r_len r2))).
  { destruct HF as [HF|HF].
    - split; [| split].
      + destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
        * unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold RMallocRep.RPAGE_SIZE in C; lia.
        * destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc (drop_region rid st2) ak ar (proj1 MRd) Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & _ & _ & _ & RC). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in RC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
        * destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc (drop_region rid st2) b gh (proj1 MRd) Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in RC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
        * destruct C as (k & rk & v & Hk & _ & Hin & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [_ Hk].
          destruct (WR _ _ Hk) as (_ & _ & _ & RC & _). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in RC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
        * unfold RGOT_SSP in C; lia. * unfold RSSP_GUARD in C; lia.
      + intros Hea. exact (rerrno_avoids_repfoot _ _ a MRd Hea HF).
      + intros Hin. destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
        * unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold RMallocRep.RPAGE_SIZE in C; lia.
        * destruct C as (ak & ar & Hak & Ha'). cbn [drop_region s_areas set_shadow set_regions] in Hak.
          destruct (WA ak ar Hak) as (ra & Hra & Sa0 & Sa1 & _ & NK & ALR).
          assert (NE : fst ak <> rid) by (intros E; rewrite E, Hr in Hra; assert (ra = r2) by congruence; subst; exact (NK Kr)).
          rewrite (rconc_drop st2 rid ak NE) in Ha'. rewrite (conc_region' st2 ak ra Hra) in Ha'.
          pose proof (lr_lo_group r2 Kr). destruct (DJ _ _ _ _ Hra Hr NE); lia.
        * destruct C as (b & gh & Hb & Ha'). cbn [drop_region s_groups set_shadow set_regions] in Hb.
          destruct (WG b gh Hb) as (rb & Hrb & Krb & Sb0 & Sb1 & _).
          assert (NE : fst b <> rid).
          { intros E. pose proof (proj1 MRd) as (_ & _ & _ & _ & WG'). destruct (WG' b gh Hb) as (rb' & Hrb' & _).
            cbn [drop_region s_regions set_shadow set_regions] in Hrb'. rewrite E, lookup_delete_eq in Hrb'. discriminate. }
          rewrite (rconc_drop st2 rid b NE) in Ha'. rewrite (conc_region' st2 b rb Hrb) in Ha'.
          pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
        * destruct C as (k & rk & v & Hk & Kk & Ha' & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
          pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia.
        * unfold RGOT_SSP in C. lia.
        * unfold RSSP_GUARD in C. lia.
    - destruct HF as (k & rk & Hk & Kk & Ha'). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
      destruct (WR _ _ Hk) as (_ & _ & _ & RC & RFk). pose proof (rreserved_disjoint _ _ RFk) as (?&?&?&?). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in RC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
      split; [lia|]. split; [lia|].
      pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia. }
  destruct LOW as (L1 & L2 & L3). cbn [outside]. split; [lia|]. split; [exact L2|]. split; [exact L3| exact I].
Qed.

Lemma byte_zero_list (x : byte) : bv_unsigned x = 0 -> [x] = [b8 0].
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros Hx. f_equal. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 x). rewrite Hx. reflexivity. Qed.

Lemma bytes4_range (x0 x1 x2 x3 : byte) :
  0 <= bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3 < 2^32.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
  pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
  unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *. lia.
Qed.

Lemma le4_of_bytes (x0 x1 x2 x3 : byte) :
  le4 (wz (bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3)) = [x0; x1; x2; x3].
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
  pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
  unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *.
  rewrite le4_bytes by lia. unfold b8.
  f_equal; [|f_equal; [|f_equal; [|f_equal]]];
    (apply bv_eq; rewrite Z_to_bv_unsigned;
     match goal with |- bv_wrap 8 ?a = _ => change (bv_wrap 8 a) with (a mod 256)%Z end;
     Z.div_mod_to_equations; lia).
Qed.

Lemma shiftr5_ge v : 0 <= v < 256 -> 5 <= Z.shiftr v 5 -> 160 <= v.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
Lemma shiftr5_lt v : 0 <= v < 256 -> Z.shiftr v 5 < 5 -> v < 160.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
Lemma shiftr5_range v : 0 <= v < 256 -> 0 <= Z.shiftr v 5 < 8.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros Hv. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

Section FREE.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis TP : tp = Z_to_bv 64 RATP.

Theorem rlibc_free_implT : forall (ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (s : PState)
    (st : mstate) (blk : block) (off : Z) (errv : word),
  CINV st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  rmrep st m -> mem_inv psegs m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 8192 ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  a0 = Z_to_bv 64 (blk_addr blk) ->
  c_init_done (ctx st) <> 0 ->
  rimplT m (free st (Some (aadd (blk_slot blk) (UNIT * off)))) s
        (rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB blk) m errv s)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rfree_entry) fc None m (seg_rom psegs)).
Proof using LO TP.
  intros until errv. intros C Hin Hoff HA MR MI ST SLO ERR A0 INI.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (KINV_of_CINV _ _ C) as K0.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as ->.
  { rewrite HA in OA. unfold UNIT in OA. lia. }
  clear OA.
  set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *. set (LB' := lbrm LB blk) in *.
  pose proof (ci_gmetas _ _ C b g HB) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
  rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  destruct (ki_slts _ _ _ K0 _ _ _ SL) as (GMg & Ec & _). fold c0 in Ec.
  destruct HK as (v3 & lo8 & hi & C3 & V31 & C2 & C1 & OFF). fold c0 in C3, C2, C1, OFF.
  cbn [aadd fst snd] in C3, C2, C1, OFF.
  assert (Fp : fst pf = fst b) by (unfold pf; cbn; symmetry; exact FB).
  assert (Cp : conc st pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; exact Hr).
  assert (Cc : conc st c0 = r_base r + snd c0) by (apply conc_region'; rewrite <- FB; exact Hr).
  assert (Sp : snd pf = snd c0 + 16 * off) by (unfold pf, UNIT; cbn; lia).
  assert (HAp : blk_addr blk = r_base r + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
  assert (Sc : snd c0 = snd b + 16 + get_stride (get_meta_rec st g) * i).
  { rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
  pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (ETP : bv_unsigned tp + -164 = 238572) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  pose proof LO as LOv. unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in LOv; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
  { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
  assert (SI0 : 0 <= get_stride (get_meta_rec st g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SIL : get_stride (get_meta_rec st g) * (i + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
  unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
  assert (P16m : snd pf mod 16 = 0).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. unfold UNIT, IB in *. clear - SIM B16 Hoff. Z.div_mod_to_equations. lia. }
  assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. set (stq := get_stride (get_meta_rec st g)) in *.
    unfold UNIT, IB in *.
    assert (16 * off + 16 <= stq) by (clear - OS SZ SM Hoff S16; Z.div_mod_to_equations; lia).
    rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
  assert (HAR : 0 <= r_base r + snd pf /\ r_base r + snd pf + 16 <= 2^64) by (unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; pose proof (round_up_pg_ge (r_len r)); lia).
  assert (DRr : r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x5b000 <= r_base r) by (apply (rreserved_disjoint1 _ _ RF); lia).
  clear SIM SM B16 RBAL AL. change (frozen (snd pf mod 16 = 0)) in P16m.
  assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
  { unfold aadd. apply injective_projections; cbn; [exact Fp| unfold UNIT in *; lia]. }
  destruct HB as [ai Hgh].
  assert (Cb : conc st b = r_base r + snd b) by (apply conc_region'; exact Hr).
  pose proof (shiftr5_range v3) as SR5.
  destruct (rmrep_shadow_read st m (fst c0) r (snd c0 + UNIT * off - 3) v3 MR ltac:(rewrite <- FB; exact Hr) Kr ltac:(unfold UNIT, IB in *; lia) C3) as [_ V3R].
  assert (RDB : forall q : aptr, fst q = fst b -> 0 <= snd q < round_up_pg (r_len r) ->
            exists x : byte, bytes_at psegs m (r_base r + snd q) [x] /\ rdv pans_mem m st q = bv_unsigned x).
  { intros q Fq Hq.
    assert (Hrq : s_regions st !! fst q = Some r) by (rewrite Fq; exact Hr).
    destruct (SH _ r Hr Kr) as [WRr _].
    assert (W1 : wr_at psegs m (r_base r + snd q) 1).
    { destruct WRr as (W0 & Wn & W). split; [lia|]. split; [pose proof (round_up_pg_ge (r_len r)); unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia|].
      intros j Hj. replace (r_base r + snd q + j) with (r_base r + (snd q + j)) by lia. apply W. lia. }
    destruct (rwr_at_bytes_exist m _ 1 W1 ltac:(lia) ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) as (bs & L & B).
    destruct bs as [|x [|]]; try discriminate. exists x. split; [exact B|].
    eapply (rrdv_cur m st m q r x MR Hrq Kr Hq); [intros; reflexivity| exact B]. }
  unfold free.
  eapply (rimplT_bind m (free_hdr st pf) _ s
           (fun r1 s' ms' => s' = s /\ r1 = Some (hdr_st st pf, g, i) /\
              rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')).
  { unfold free_hdr, get_meta. apply rimplT_guard. intros _.
    apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
    rewrite (rdv_known m st (aadd pf (-4)) 0) by (cbn [aadd fst snd]; replace (snd pf + -4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia); exact OK).
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    rewrite (rdv_known m st (aadd pf (-2)) lo8) by (cbn [aadd fst snd]; replace (snd pf + -2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia); exact C2).
    rewrite (rdv_known m st (aadd (aadd pf (-2)) 1) hi) by (cbn [aadd fst snd]; replace (snd pf + -2 + 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia); exact C1).
    cbn [Z.eqb negb]. rewrite EB. unfold get_group. rewrite Hgh. cbn [g_meta].
    apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
    destruct (s_areas st !! area_of g) as [ar|] eqn:AR1; [| apply rimplT_guard; intros; discriminate].
    apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
    unfold slot_start. rewrite (go_mem _ _ _ GO). cbv beta zeta.
    apply Z.eqb_eq in G15. apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
    rewrite V31 in G12, G13, G14, G16.
    set (e := aadd (aadd b (UNIT + get_stride (get_meta_rec st g) * Z.land v3 31)) (get_stride (get_meta_rec st g) - IB)).
    assert (Fe : fst e = fst b) by reflexivity.
    assert (Se : snd e = snd b + 16 + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - 4).
    { unfold e. cbn [aadd snd]. rewrite V31. unfold UNIT, IB. lia. }
    pose proof (go_sc _ _ _ GO) as GSC.
    assert (WALK : forall r32 : Z,
      (160 <= v3 -> Z.shiftr v3 5 = 5 /\ 5 <= r32 < 2^32
          /\ bytes_at psegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 4) (le4 (wz r32))
          /\ bytes_at psegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 5) [b8 0]) ->
      (if 160 <=? v3 then r32 else Z.shiftr v3 5) <= conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf) ->
      bytes_at psegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (if 160 <=? v3 then r32 else Z.shiftr v3 5)) [b8 0] ->
      bytes_at psegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB) [b8 0] ->
      evt psegs (fun ms' => s = s /\ Some (hdr_st st pf, g, i) = Some (hdr_st st pf, g, i) /\
                 rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom psegs))).
    { intros r32 BIG RSVLE RB0r RE0.
      eapply evt_mono.
      { eapply (rfree_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st pf r g (mkGhdr (Some g) ai) ar v3 lo8 hi r32);
          first [exact MR | exact MI | exact TK | exact ST | exact LO | exact Kr | idtac].
        all: rewrite ?EB, ?V31.
        - lia.
        - rewrite Fp. exact Hr.
        - rewrite A0, HAp. apply unsigned_lit. lia.
        - exact P16m.
        - rewrite Sp, Sc. lia.
        - unfold pf in OFF |- *. cbn [aadd snd] in OFF |- *. lia.
        - exact PHI.
        - replace (snd pf - 4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia). unfold pf; cbn [aadd fst]. exact OK.
        - replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C3.
        - replace (snd pf - 2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C2.
        - replace (snd pf - 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C1.
        - exact Hgh.
        - reflexivity.
        - exact (go_slot _ _ _ GO).
        - destruct (go_slot _ _ _ GO) as (a & ara & k & Ha & Hk & ->). destruct (WA a ara Ha) as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. lia.
        - exact (go_mem _ _ _ GO).
        - exact AR1.
        - exact G15.
        - exact (go_avail _ _ _ GO).
        - exact (go_freed _ _ _ GO).
        - exact (proj2 (proj2 (proj2 (ki_cx _ _ _ K0)))).
        - lia.
        - rewrite (go_freeable _ _ _ GO). lia.
        - lia.
        - pose proof (go_maplen _ _ _ GO). lia.
        - exact G12.
        - exact G13.
        - exact G14.
        - intros Hsc. apply Z.ltb_lt in Hsc. rewrite Hsc in G16. apply andb_true_iff in G16. destruct G16 as [G16a G16b].
          apply Z.leb_le in G16a. apply Z.ltb_lt in G16b. lia.
        - intros Hsc. destruct (Z.ltb_spec (m_sizeclass (get_meta_rec st g)) 48); [lia|]. apply Z.eqb_eq in G16. exact G16.
        - intros Hml. destruct (Z.eqb_spec (m_maplen (get_meta_rec st g)) 0); [lia|]. cbn [negb] in G17. apply Z.leb_le in G17.
          unfold UNIT in G17.
          replace (m_maplen (get_meta_rec st g) * 4096) with (m_maplen (get_meta_rec st g) * 256 * 16) in G17 by lia.
          rewrite Z.div_mul in G17 by lia. lia.
        - lia.
        - exact S16.
        - rewrite Cb, Sp, Sc. unfold UNIT, IB in *. lia.
        - rewrite Cb. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia.
        - exact BIG.
        - exact RSVLE.
        - exact RB0r.
        - exact RE0.
        - intros b' gh' Hb' Fb'. specialize (HD b' gh' Hb' ltac:(rewrite Fb', Fp; exact FB)).
          rewrite (conc_region' st b' r) in HD by (rewrite Fb', Fp; exact Hr). unfold IB in HD.
          clear - HD HAp SZ. lia.
        - exact INI. }
      intros ms' FP. split; [reflexivity|]. split; [reflexivity|]. unfold hdr_st. rewrite <- V31. exact FP. }
    assert (EQE : forall k, r_base r + snd (aadd e (- k)) = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - k).
    { intros k. cbn [aadd snd]. rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (EQE0 : r_base r + snd e = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (ERNG : snd e + 1 <= round_up_pg (r_len r) /\ snd pf <= snd e /\ 16 <= snd e).
    { rewrite Se, Sp, Sc. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia. }
    assert (DIFF : snd e - snd pf = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf)).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    
    unfold get_nominal_size. apply rimplT_rd8. cbv zeta.
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    apply rimplT_if; intros HR5.
    -
      apply Z.leb_le in HR5.
      apply rimplT_guard; intros G20. apply Z.eqb_eq in G20.
      apply rimplT_rd32. 
      destruct (RDB (aadd e (-4)) Fe ltac:(cbn [aadd snd]; lia)) as (x0 & BX0 & RX0). rewrite RX0. 
      destruct (RDB (aadd (aadd e (-4)) 1) Fe ltac:(cbn [aadd snd]; lia)) as (x1 & BX1 & RX1). rewrite RX1. 
      destruct (RDB (aadd (aadd e (-4)) 2) Fe ltac:(cbn [aadd snd]; lia)) as (x2 & BX2 & RX2). rewrite RX2.
      destruct (RDB (aadd (aadd e (-4)) 3) Fe ltac:(cbn [aadd snd]; lia)) as (x3 & BX3 & RX3). rewrite RX3.
      pose proof (bytes4_range x0 x1 x2 x3) as U32. pose proof (le4_of_bytes x0 x1 x2 x3) as LE4.
      set (r32 := bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3) in *.
      apply rimplT_guard; intros G21. apply Z.leb_le in G21.
      apply rimplT_rd8. destruct (RDB (aadd e (-5)) Fe ltac:(cbn [aadd snd]; lia)) as (x5 & BX5 & RX5). rewrite RX5.
      apply rimplT_guard; intros G25. apply Z.eqb_eq in G25.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8. destruct (RDB (aadd e (- r32)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8. destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_ge v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = true) by (apply Z.leb_le; exact V160).
      
      apply (WALK r32).
      + intros _. split; [exact G20|]. split; [lia|]. split.
        * rewrite <- (EQE 4). rewrite LE4. change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))).
          apply bytes_at_app. split; [exact BX0|]. apply bytes_at_app. split; [cbn [length Z.of_nat Pos.of_succ_nat]; cbn [aadd snd] in BX1 |- *; replace (r_base r + (snd e + -4) + 1) with (r_base r + (snd e + -4 + 1)) by lia; exact BX1|].
          apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; cbn [aadd snd] in BX2, BX3 |- *.
          -- replace (r_base r + (snd e + -4) + 1 + 1) with (r_base r + (snd e + -4 + 2)) by lia. exact BX2.
          -- replace (r_base r + (snd e + -4) + 1 + 1 + 1) with (r_base r + (snd e + -4 + 3)) by lia. exact BX3.
        * rewrite <- (EQE 5), <- (byte_zero_list x5 G25). exact BX5.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE r32), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe.
    -
      apply Z.leb_gt in HR5.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8. destruct (RDB (aadd e (- Z.shiftr v3 5)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8. destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_lt v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = false) by (apply Z.leb_gt; exact V160).
      
      apply (WALK 0).
      + intros H. exfalso. clear -H V160. lia.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE (Z.shiftr v3 5)), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe. }

  intros r1 s' ms1 (-> & -> & FH). cbv beta iota.
  destruct FH as (x1 & x5 & x6 & x7 & junk & m1 & -> & PE1 & WM1 & MI1 & ST1 & FR1 & MR1).
  set (st1 := hdr_st st pf) in *.
  assert (TK1 : ticks_ok st1) by (unfold st1; apply ticks_ok_hdr_st; exact TK).
  assert (MSL1 : meta_slot st1 g) by (exact (go_slot _ _ _ GO)).
  assert (HK123 : forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w).
  { intros k Hk. unfold pf; cbn [aadd fst snd].
    assert (CS : k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct CS as [-> |[-> | ->]];
      [exists hi; replace (snd c0 + UNIT * off - 1) with (snd c0 + UNIT * off - 1) by lia
      |exists lo8|exists v3];
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3]; f_equal; unfold UNIT; lia. }
  assert (FP1 : forall a, rfree_fp st1 lo (bv_unsigned sp - 48) a -> rfree_fp st lo (bv_unsigned sp) a).
  { intros a Ha. eapply (rfree_fp_hdr_st st pf lo (bv_unsigned sp) (bv_unsigned sp - 48) a TK HK123); [lia| exact Ha]. }
  assert (ERR1 : rw_cells psegs m1 (errno_addr tp) [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE1 | exact ERR |]. cbn [cells_size csize Nat.add]. intros a Ha.
    rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
  assert (TF : Z.testbit (m_freed (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_freed (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; left; exact E| reflexivity]. }
  assert (TA : Z.testbit (m_avail (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_avail (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; right; exact E| reflexivity]. }
  assert (BLKR : forall stX blk', s_regions stX = s_regions st -> In blk' (lbrm LB blk) -> exists r', s_regions stX !! fst (blk_slot blk') = Some r').
  { intros stX blk' ERX Hb'. rewrite ERX. unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hb' _].
    destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hb') as [(r' & Hr' & _) _ _]. exists r'. exact Hr'. }
  unfold free_tail. cbv zeta. change (get_meta_rec st1 g) with (get_meta_rec st g).
  apply rimplT_guard. intros _.
  apply rimplT_if; intros HC.
  -
    apply negb_true_iff in HC. apply orb_false_iff in HC. destruct HC as [Hfz Hall]. apply Z.eqb_neq in Hfz. apply Z.eqb_neq in Hall.
    apply rimplT_ret.
    eapply evt_mono.
    { eapply (rfree_triv ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 junk lo st st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact Hfz | exact Hall | exact FR1 | exact ST1 | exact LO | reflexivity | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    intros ms' TPo. unfold rftriv_post in TPo.
    destruct TPo as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & PE' & WM' & MI' & ST' & MR').
    split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE' | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
             rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
    split; [exact MR'|].
    split. { eapply rpres_except_mono; [eapply rpres_except_trans; [exact PE1| exact PE']|]. intros a Ha. left. exact Ha. }
    split; [intros rid r' H; exact H|].
    split; [intros blk' Hb'; apply (BLKR _ blk' eq_refl Hb')|].
    split; reflexivity.
  -
    
    assert (HNT : m_freed (get_meta_rec st g) = 0 \/ Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) + bit i = mask_upto (m_last_idx (get_meta_rec st g))).
    { apply negb_false_iff in HC. apply orb_true_iff in HC. destruct HC as [HC|HC]; apply Z.eqb_eq in HC; auto. }
    eapply rimplT_evt.
    { eapply (rfree_tocall ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact HNT | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    intros ms2 (y2 & y3 & y4 & y5 & y6 & y7 & ->).
    assert (HLB : forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk).
    { intros b' Hb'. unfold LB', lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [H1 H2]. split; [exact H1|].
      intros E. rewrite E, aptr_eqb_refl in H2. exact H2. }
    assert (K1 : KINV st1 LB' 0).
    { unfold st1. eapply (KINV_hdr_st st LB LB' 0 pf blk r C Hin); [| exact HLB | rewrite Fp, FB; reflexivity | rewrite Fp; exact Hr | symmetry; exact HAp | exact P16m].
      unfold LB', lbrm. apply (KINV_filter_slot st LB 0 (fun s => negb (aptr_eqb s (blk_slot blk)))). exact K0. }
    assert (L1 : LPRE st1 LB' 0 g b i).
    { unfold LB', lbrm. apply (LPRE_intro st1 LB 0 g b i blk); [exact (ki_slts _ _ _ K0) | exists ai; exact Hgh | exact SL | exact NFR | exact NG | pose proof (go_sc _ _ _ GO); change (get_meta_rec st1 g) with (get_meta_rec st g); lia]. }
    assert (Z1 : ZINV st1 []) by (unfold st1; apply ZINV_hdr_st; apply (ZINV_of_CINV _ _ C)).
    assert (OOK1 : oracle_ok m m1 st1).
    { unfold st1. apply oracle_ok_hdr_st; [exact TK|]. eapply (roracle_ok_pres m m m1 st lo (bv_unsigned sp) m); [apply oracle_ok_refl | exact MR | exact LO | exact PE1]. }
    change (wz (conc st g)) with (Z_to_bv 64 (conc st1 g)). change (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc st1 g)).
    eapply (rntf_implT gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc m LB' lo LO);
      [exact K1 | exact L1 | exact Z1 | exact INI | exact MR1 | exact MI1 | exact OOK1 | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; unfold FUEL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; lia |].
    
    intros st2 mi ms3 NQ. unfold rntf_q in NQ.
    destruct NQ as (u0 & u1 & u2 & a0v & a1v & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m3 & -> & MI3 & ST3 & MR3 & PE3 & [c3 KI3] & ZI3 & FR3 & RES3 & OOK3).
    rewrite unsigned_lit in ST3, PE3 by lia.
    replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in PE3 by lia.
    replace (ret_pc (Z_to_bv 64 0x20908)) with (Z_to_bv 64 0x20908) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (PE13 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
    { eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_mono; [exact PE3| exact FP1]. }
    assert (FR3' : rw_cells psegs m3 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact FR1 |]. cbn [cells_size csize Nat.add length]. intros a Ha Hfp.
      pose proof (rfree_fp_lt st1 m1 lo (bv_unsigned sp - 48) a MR1 LO ltac:(lia) Hfp). lia. }
    assert (ERR3 : rw_cells psegs m3 (errno_addr tp) [C4 errv]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
      rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR1 | exact LO | lia]. }
    pose proof (nf_regions _ _ FR3) as ER3. change (s_regions st1) with (s_regions st) in ER3.
    pose proof (nf_brk _ _ FR3) as EB3. change (ctx st1) with (ctx st) in EB3.
    destruct mi as [[bm len]|].
    +
      cbv beta iota.
      destruct RES3 as (-> & -> & LEN & SND & (r2 & Hr2 & Kr2 & Lr2) & NOG).
      replace (negb (len =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
      pose proof Hr2 as Hr2'. rewrite ER3 in Hr2'.
      destruct (WR _ _ Hr2') as (R2B0 & R2AL & R2L & R2C & R2F). unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec.Malloc.MCEIL in R2C; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
      assert (R2D : r_base r2 + round_up_pg (r_len r2) <= 0x10000 \/ 0x5b000 <= r_base r2) by (apply (rreserved_disjoint1 _ _ R2F); lia).
      assert (CB2 : conc st2 bm = r_base r2) by (rewrite (conc_region' st2 bm r2 Hr2); lia).
      pose proof (round_up_pg_ge (r_len r2)) as RU2.
      eapply rimplT_evt.
      { eapply (rfree_tomunmap sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra (wz (conc st2 bm)) _ _ F fc m3 junk lo len st2 errv);
          first [exact TP | exact MR3 | exact MI3 | exact LEN | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
      intros ms4 FM. unfold rfmun_post in FM.
      destruct FM as (w0 & w1 & w2 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4 & ERR4 & MR4).
      eapply (rimplT_munmap m (conc st2 bm) len _ s).
      { eapply rmunmap_spec.
        - rewrite unsigned_lit by lia. exact ST4.
        - exact ERR4.
        - exact MI4.
        - unfold wz. reflexivity.
        - unfold wz. reflexivity.
        - lia.
        - rewrite Lr2, mmap_len_round. lia.
        - lia.
        - rewrite unsigned_lit by lia. lia.
        - rewrite ETP, unsigned_lit by lia. lia.
        - rewrite Lr2, mmap_len_round, unsigned_lit by lia. lia.
        - rewrite ETP, Lr2, mmap_len_round. lia.
        - rewrite TP; unfold RATP; rewrite unsigned_lit by lia. lia. }
      intros a ms5 MP. cbv beta. unfold rmunmap_post in MP.
      destruct MP as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m5 & -> & MU5 & _ & MI5 & ST5 & ERR5 & ERNG).
      rewrite (munmap_ok_range_val a ERNG).
      apply rimplT_ret.
      replace (ret_pc (Z_to_bv 64 0x20938)) with (Z_to_bv 64 0x20938) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      rewrite unsigned_lit in MU5, ST5 by lia. rewrite Lr2, mmap_len_round, ETP in MU5.
      assert (AMC2 : amc (ctx st2) = amc (ctx st)) by (rewrite (nf_amc _ _ FR3); reflexivity).
      assert (MP2 : ci_mptrs st2) by (eapply (ci_mptrs_frame st st2 (ci_mp _ _ C) AMC2); [rewrite (nf_areas _ _ FR3); reflexivity| exact ER3]).
      assert (NOG' : forall b' gh, s_groups st2 !! b' = Some gh -> fst b' <> fst bm) by (intros b' gh Hb'; exact (NOG b' gh Hb')).
      pose proof (rptrs_in_norid st2 LB' c3 (fst bm) r2 m4 KI3 ZI3 MR4 Hr2 Kr2 NOG' MP2) as PTR.
      pose proof (rmrep_drop_region st2 (fst bm) PTR m4 MR4) as MRd4.
      assert (MRd5 : rmrep (drop_region (fst bm) st2) m5).
      { eapply (rmrep_after_munmap st2 (fst bm) r2 m4 m5); [exact MRd4 | exact MR4 | exact Hr2 | exact Kr2 | rewrite <- CB2; exact MU5 | lia]. }
      assert (FR5 : rw_cells psegs m5 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rrw_cells_agree'; [exact FR4|]. cbn [cells_size csize Nat.add length]. intros x Hx. apply MU5. rewrite wa_unsigned by lia.
        rewrite ?ETP. cbn [outside]. repeat split; lia. }
      eapply evt_mono.
      { eapply (rfree_fin1 sp gp tp z0 z1 z2 s0 s1 (munmap_ret a) z3 z4 z5 z6 z7 z8 z9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z10 z11 z12 z13 _ ra (sx32 errv) (wz (conc st2 bm)) (wz len) (rg_errno a errv) F fc m5 junk lo (drop_region (fst bm) st2) errv);
          first [exact TP | exact MRd5 | exact MI5 | exact FR5 | apply le4_sx32 | exact ERR5 | exact ST5 | exact LO | lia]. }
      intros ms' FIN. unfold rffin_post in FIN.
      destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
      split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      {
        assert (DR : forall x, r_base r2 <= x < r_base r2 + round_up_pg (r_len r2) -> DROPPED st (drop_region (fst bm) st2) x).
        { intros x Hx. exists (fst bm), r2. split; [exact Hr2'|]. split; [| split; [exact Kr2| exact Hx]].
          cbn [drop_region s_regions set_shadow set_regions]. apply lookup_delete_eq. }
        eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m3 m4 MU4)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 238572 <= a < 238576)); [| exact NC].
          cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m4 m5 MU5)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 238572 <= a < 238576)); [| exact NC].
          cover_intervals ltac:(fun y Hy => lazymatch type of Hy with context [238572%Z] => right; right; lia | context [conc] => right; left; apply DR; lia | _ => left; apply rfree_fp_stack; lia end). }
        eapply (rpres_except_of_munch_nw _ _ m5 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 238572 <= a < 238576)); [| exact NC].
        cover_intervals ltac:(fun y Hy => lazymatch type of Hy with context [238572%Z] => right; right; lia | _ => left; apply rfree_fp_stack; lia end). }
      split.
      { intros rid r' H. cbn [drop_region s_regions set_shadow set_regions] in H. apply lookup_delete_Some in H. destruct H as [_ H]. rewrite <- ER3. exact H. }
      split.
      { intros blk' Hb'. pose proof (proj1 (List.Forall_forall _ _) (ki_blks _ _ _ KI3) blk' Hb') as BK'.
        destruct BK' as [(g' & i' & bb & SL' & HB' & FB' & _) _ _].
        destruct (go_region _ _ _ (ki_gmetas _ _ _ KI3 bb g' HB')) as (rr & Hrr & _).
        exists rr. cbn [drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne; [rewrite <- FB'; exact Hrr|].
        intros E. destruct HB' as [ai' Hbb]. apply (NOG bb _ Hbb). rewrite E. exact FB'. }
      split; [exact EB3|].
      intros brid boff HB0. cbn [drop_region s_regions set_shadow set_regions ctx s_ctx].
      rewrite <- EB3 in HB0. destruct (ki_bk _ _ _ KI3 brid boff HB0) as (rb & Hrb & Krb).
      rewrite lookup_delete_ne; [rewrite ER3; reflexivity |].
      intros E. rewrite <- E, Hr2 in Hrb. assert (rb = r2) by congruence. subst rb. rewrite Kr2 in Krb. discriminate.
    +
      
      cbv beta iota. cbn in RES3. subst a1v.
      apply rimplT_ret.
      eapply evt_mono.
      { eapply (rfree_fin0 sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra a0v _ _ F fc m3 junk lo st2 errv);
          first [exact TP | exact MR3 | exact MI3 | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
      intros ms' FIN. unfold rffin_post in FIN.
      destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
      split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply (rpres_except_of_munch_nw _ _ m3 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st2 a \/ 238572 <= a < 238576)); [| exact NC].
        cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
      split; [intros rid r' H; rewrite <- ER3; exact H|].
      split; [intros blk' Hb'; apply (BLKR st2 blk' ER3 Hb')|].
      split; [exact EB3|].
      intros brid boff _. rewrite ER3. reflexivity.
Qed.
End FREE.
End WithCeiling0.
