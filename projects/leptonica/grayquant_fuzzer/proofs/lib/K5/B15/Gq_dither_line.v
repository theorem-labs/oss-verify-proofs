(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit LeptB_guard LeptB_guard2.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Gq_dither_l1 Gq_dither_l0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_ditherToBinaryLineLow : Z := 0x9e2d8.

Notation DLL_W usp lined nl bufs1 bufs2 n1 := [(usp - 64, usp); (lined, lined + nl); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)]%Z (only parsing).
Notation ONE := (Z_to_bv 64 1) (only parsing).

(* [comment removed for export] *)
Definition ditherToBinaryLineLow_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (usp lo lined nl bufs1 bufs2 n1 : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (bs1' bs2' : list byte) (wl' : list word),
    ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (DLL_W usp lined nl bufs1 bufs2 n1) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo usp
    /\ u8arr asegs m' bufs1 bs1' /\ Z.of_nat (length bs1') = n1 /\ acc asegs m' bufs1 n1
    /\ u8arr asegs m' bufs2 bs2' /\ Z.of_nat (length bs2') = n1 /\ acc asegs m' bufs2 n1
    /\ u32arr asegs m' lined wl' /\ 4 * Z.of_nat (length wl') = nl /\ acc asegs m' lined nl.



(* [comment removed for export] *)
Lemma slt_xor_lt : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 ->
  (Z.lxor x 9223372036854775808 <? Z.lxor y 9223372036854775808) = (x <? y).
Proof.
  intros x y Hx Hy.
  assert (E : forall v, 0 <= v < 2^63 -> Z.lxor v 9223372036854775808 = v + 9223372036854775808).
  { intros v Hv. symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    change 9223372036854775808 with (2^63). rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec 63 n) as [<-|NE]; [| apply andb_false_r].
    rewrite andb_true_r. destruct (Z.eq_dec v 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite !E by assumption.
  destruct (Z.ltb_spec x y); destruct (Z.ltb_spec (x + 9223372036854775808) (y + 9223372036854775808)); lia.
Qed.
Ltac w1_guard HW :=
  rewrite (Z.mod_small (_ - 1) 18446744073709551616) by (clear - HW; lia);
  rewrite (slt_xor_lt (_ - 1) _) by (clear - HW; lia);
  match goal with |- context [?w - 1 <? ?w] => replace (w - 1 <? w) with true by (symmetry; apply Z.ltb_lt; clear; lia) end;
  cbn [Z.b2z]; change (Z.lxor 1 1) with 0.


(* [comment removed for export] *)
Lemma sgtz_mask : forall x, 0 <= x < 2^63 ->
  Z.land ((0 - Z.b2z (9223372036854775808 <? Z.lxor x 9223372036854775808)) mod 18446744073709551616) x = x.
Proof.
  intros x Hx.
  assert (E : Z.lxor x 9223372036854775808 = x + 9223372036854775808).
  { symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    change 9223372036854775808 with (2^63). rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec 63 n) as [<-|NE]; [| apply andb_false_r].
    rewrite andb_true_r. destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite E. destruct (Z.eq_dec x 0) as [->|NZ]; [reflexivity|].
  replace (9223372036854775808 <? x + 9223372036854775808) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [Z.b2z]. change ((0 - 1) mod 18446744073709551616) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Ltac fix_tripcount r W HW :=
  reg_val (Z_to_bv 5 r) ltac:(fun v => lazymatch v with Z_to_bv 64 ?e =>
    replace e with (W - 1) by (symmetry; apply sgtz_mask; clear - HW; lia) end).

(* [comment removed for export] *)
Lemma acc_transport : forall W (m m' : mem) A N,
  acc asegs m A N -> munch W m m' -> (forall i, 0 <= i < N -> disjoint_from W (shad (A + i)) 1) -> acc asegs m' A N.
Proof.
  intros W m m' A N H MU D i Hi. destruct (H i Hi) as (b & Hb & OK). exists b. split; [| exact OK].
  eapply (bytes_at_transport asegs W m m'); [exact Hb | exact MU |]. cbn [length Z.of_nat Pos.to_nat Pos.iter_op Nat.add]. exact (D i Hi).
Qed.

(* [comment removed for export] *)
Lemma dll_finish : forall (ra gp tp t0 t1 t2 s0e s1e a1 a4 a5 s2e s3e s4e s5e s6e s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0 s1 s2 s3 s4 s5 s6 : word) F fc (m0 m : mem)
    (usp lo lined nl bufs1 bufs2 n1 w : Z) (bs1 bs2 : list byte) (wl : list word),
  dl_geom2 lined nl bufs1 bufs2 n1 w ->
  munch (DLL_W usp lined nl bufs1 bufs2 n1) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  rw_cells asegs m (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0] ->
  stk asegs m lo (usp + -64) -> lo <= usp - 64 -> usp <= 2^47 -> 0x10007fff8000 <= lo ->
  lined + nl <= lo -> bufs1 + n1 <= lo -> bufs2 + n1 <= lo ->
  evt asegs (ditherToBinaryLineLow_post ra0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 usp lo lined nl bufs1 bufs2 n1)
    (MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 lined) a1 (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) a4 a5 (Z_to_bv 64 (w - 1))
             (Z_to_bv 64 SHB) s2e s3e s4e s5e s6e s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9e8ec) fc None m (seg_rom asegs)).
Proof.
  intros until wl. intros GEO MU WM MI UB UBL ACCB UC UCL ACCC UL ULL ACCL FR ST LO UHI LOH LLO BLO CLO.
  pose proof GEO as ((HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & L0 & LA4 & LNHI & LSH & LSEG & SEP)
                     & C0 & C8 & CHI & CSH & CSEG & SEP2 & SEP3).
  unfold SEGTOP_A, SHB in *.
  eapply evt_cut.
  { eapply dl0_last; eassumption. }
  intros ms' PO. unfold dl0_end in PO.
  destruct PO as (t0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & s2' & s3' & s4' & s5' & s6' & m' & bs1' & bs2' & wl' & -> & MU' & WM' & MI'
                  & UB' & UBL' & ACCB' & UC' & UCL' & ACCC' & UL' & ULL' & ACCL').
  clear MI UB UBL ACCB UC UCL ACCC UL ULL ACCL.
  lazymatch type of MU' with munch _ ?mo _ => transport_after_call asegs mo m' MU' WM' end.
  clear MU' WM'.
  idtac "MARK finish: transported".
  lwalk (@nil Z).
  idtac "MARK finish: epilogue walked".
  apply evt_done. unfold ditherToBinaryLineLow_post.
  do 15 eexists. exists m', bs1', bs2', wl'.
  split; [reflexivity|].
  repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Lemma dll_finish1 : forall (ra gp tp t1 t2 s0e s1e a1 a4 a5 a6 s2e s3e s4e s5e s6e s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0 s1 s2 s3 s4 s5 s6 : word) F fc (m0 m : mem)
    (usp lo lined nl bufs1 bufs2 n1 w : Z) (bs1 bs2 : list byte) (wl : list word),
  dl_geom2 lined nl bufs1 bufs2 n1 w ->
  munch (DLL_W usp lined nl bufs1 bufs2 n1) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  rw_cells asegs m (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0] ->
  stk asegs m lo (usp + -64) -> lo <= usp - 64 -> usp <= 2^47 -> 0x10007fff8000 <= lo ->
  lined + nl <= lo -> bufs1 + n1 <= lo -> bufs2 + n1 <= lo ->
  evt asegs (ditherToBinaryLineLow_post ra0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 usp lo lined nl bufs1 bufs2 n1)
    (MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp (Z_to_bv 64 (w - 1)) t1 t2 s0e s1e (Z_to_bv 64 lined) a1 (Z_to_bv 64 bufs1) (Z_to_bv 64 (w - 1)) a4 a5 a6
             (Z_to_bv 64 SHB) s2e s3e s4e s5e s6e s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9e4dc) fc None m (seg_rom asegs)).
Proof.
  intros until wl. intros GEO MU WM MI UB UBL ACCB UC UCL ACCC UL ULL ACCL FR ST LO UHI LOH LLO BLO CLO.
  pose proof GEO as ((HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & L0 & LA4 & LNHI & LSH & LSEG & SEP)
                     & C0 & C8 & CHI & CSH & CSEG & SEP2 & SEP3).
  unfold SEGTOP_A, SHB in *.
  assert (GEO1 : dl_geom lined nl bufs1 n1 w) by exact (proj1 GEO).
  eapply evt_cut.
  { eapply dl1_last; eassumption. }
  intros ms' PO. unfold dl1_end in PO.
  destruct PO as (s0' & s1' & a0' & a1' & a2' & a4' & s2' & s3' & m' & bs1' & wl' & -> & MU' & WM' & MI'
                  & UB' & UBL' & ACCB' & UL' & ULL' & ACCL').
  (* [comment removed for export] *)
  pose proof (acc_transport _ _ _ bufs2 n1 ACCC MU' ltac:(intros i Hi; cbn [disjoint_from]; unfold shad, SHB; clear - Hi LSH BSH CHI C0; Z.div_mod_to_equations; lia)) as ACCC'.
  clear MI UB UBL ACCB UL ULL ACCL ACCC.
  lazymatch type of MU' with munch _ ?mo _ => transport_after_call asegs mo m' MU' WM' end.
  clear MU' WM'.
  idtac "MARK finish1: transported".
  lwalk (@nil Z).
  idtac "MARK finish1: epilogue walked".
  apply evt_done. unfold ditherToBinaryLineLow_post.
  do 15 eexists.
  lazymatch goal with UCx : u8arr asegs m' bufs2 ?b2 |- _ => exists m', bs1', b2, wl' end.
  split; [reflexivity|].
  repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Lemma ditherToBinaryLineLow_evt : forall (ra gp tp t0 t1 t2 s0 s1 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo : Z) (lined nl bufs1 bufs2 n1 w : Z) (bs1 bs2 : list byte) (wl : list word),
  dl_geom2 lined nl bufs1 bufs2 n1 w ->
  mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo usp -> lo <= usp - 64 -> usp <= 2^47 -> 0x10007fff8000 <= lo ->
  lined + nl <= lo -> bufs1 + n1 <= lo -> bufs2 + n1 <= lo ->
  evt asegs (ditherToBinaryLineLow_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m usp lo lined nl bufs1 bufs2 n1)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 lined) (Z_to_bv 64 w) (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) a4 a5 (Z_to_bv 64 0) a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_ditherToBinaryLineLow) fc None m (seg_rom asegs)).
Proof.
  intros until wl. intros GEO MI UB UBL ACCB UC UCL ACCC UL ULL ACCL G1 G2 ST LO UHI LOH LLO BLO CLO.
  pose proof GEO as ((HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & L0 & LA4 & LNHI & LSH & LSEG & SEP)
                     & C0 & C8 & CHI & CSH & CSEG & SEP2 & SEP3).
  unfold e_ditherToBinaryLineLow, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl (DLL_W usp lined nl bufs1 bufs2 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0x9e314].           (* [comment removed for export] *)
  idtac "MARK at dispatch".
  swrap32_fix. replace (w + -1) with (w - 1) by (clear; lia).
  w1_guard HW.               (* [comment removed for export] *)
  lwalk [0x9e57c; 0x9ea88].  (* [comment removed for export] *)
  idtac "MARK at blez".
  lstep.
  destruct (Z.eq_dec w 1) as [W1|W2].
  - (* [comment removed for export] *)
    brT.
    idtac "MARK w = 1 at 0x9ea64".
    fix_tripcount 16 w HW.
    eapply dll_finish; try eassumption; lia.
  - (* [comment removed for export] *)
    brF.
    lwalk [0x9e5e0].
    idtac "MARK at loop head".
    fix_tripcount 16 w HW.
    replace (0 <? bufs1) with true by (symmetry; apply Z.ltb_lt; clear - B0; lia).
    replace (0 <? bufs2) with true by (symmetry; apply Z.ltb_lt; clear - C0; lia).
    cbn [Z.b2z].
    assert (Q1 : Z.of_nat (Z.to_nat (w - 1)) = w - 1 - 0) by (clear - HW; lia).
    assert (Q3 : (1 <= Z.to_nat (w - 1))%nat) by (clear - HW W2; lia).
    eapply evt_cut.
    { eapply (dl0_pixels (Z.to_nat (w - 1)) 0); try eassumption. clear - HW; lia. }
    intros ms' PO. unfold dl0_exit in PO.
    destruct PO as (s1' & a1' & s2' & s3' & s4' & s5' & s6' & m' & bs1' & bs2' & wl' & -> & MU' & WM' & MI'
                    & UB' & UBL' & ACCB' & UC' & UCL' & ACCC' & UL' & ULL' & ACCL').
    clear MI UB UBL ACCB UC UCL ACCC UL ULL ACCL G1 G2.
    lazymatch type of MU' with munch _ ?mo _ => transport_after_call asegs mo m' MU' WM' end.
    clear MU' WM'.
    idtac "MARK after loop".
    unfold SHB. eapply dll_finish; try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma ditherToBinaryLineLow1_evt : forall (ra gp tp t0 t1 t2 s0 s1 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo : Z) (lined nl bufs1 bufs2 n1 w : Z) (bs1 bs2 : list byte) (wl : list word),
  dl_geom2 lined nl bufs1 bufs2 n1 w ->
  mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo usp -> lo <= usp - 64 -> usp <= 2^47 -> 0x10007fff8000 <= lo ->
  lined + nl <= lo -> bufs1 + n1 <= lo -> bufs2 + n1 <= lo ->
  evt asegs (ditherToBinaryLineLow_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m usp lo lined nl bufs1 bufs2 n1)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 lined) (Z_to_bv 64 w) (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) a4 a5 (Z_to_bv 64 1) a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_ditherToBinaryLineLow) fc None m (seg_rom asegs)).
Proof.
  intros until wl. intros GEO MI UB UBL ACCB UC UCL ACCC UL ULL ACCL G1 G2 ST LO UHI LOH LLO BLO CLO.
  pose proof GEO as ((HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & L0 & LA4 & LNHI & LSH & LSEG & SEP)
                     & C0 & C8 & CHI & CSH & CSEG & SEP2 & SEP3).
  unfold e_ditherToBinaryLineLow, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl (DLL_W usp lined nl bufs1 bufs2 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0x9e314].
  idtac "MARK1 at dispatch".
  swrap32_fix. replace (w + -1) with (w - 1) by (clear; lia).
  w1_guard HW.
  lwalk [0x9e328; 0x9ea88].  (* [comment removed for export] *)
  idtac "MARK1 at blez".
  lstep.
  destruct (Z.eq_dec w 1) as [W1|W2].
  - brT.
    idtac "MARK1 w = 1 at 0x9e654".
    fix_tripcount 13 w HW.
    eapply dll_finish1; try eassumption; lia.
  - brF.
    lwalk [0x9e394].
    idtac "MARK1 at loop head".
    fix_tripcount 13 w HW.
    replace (0 <? bufs1) with true by (symmetry; apply Z.ltb_lt; clear - B0; lia).
    replace (0 <? lined) with true by (symmetry; apply Z.ltb_lt; clear - L0; lia).
    cbn [Z.b2z].
    assert (Q1 : Z.of_nat (Z.to_nat (w - 1)) = w - 1 - 0) by (clear - HW; lia).
    assert (Q3 : (1 <= Z.to_nat (w - 1))%nat) by (clear - HW W2; lia).
    assert (GEO1 : dl_geom lined nl bufs1 n1 w) by exact (proj1 GEO).
    eapply evt_cut.
    { eapply (dl1_pixels (Z.to_nat (w - 1)) 0); try eassumption. clear - HW; lia. }
    intros ms' PO. unfold dl1_exit in PO.
    destruct PO as (s0' & s1' & a1' & s2' & s3' & m' & bs1' & wl' & -> & MU' & WM' & MI' & UB' & UBL' & ACCB' & UL' & ULL' & ACCL').
    pose proof (acc_transport _ _ _ bufs2 n1 ACCC MU' ltac:(intros i Hi; cbn [disjoint_from]; unfold shad, SHB; clear - Hi LSH BSH CHI C0; Z.div_mod_to_equations; lia)) as ACCC'.
    clear MI UB UBL ACCB UL ULL ACCL G1 G2 ACCC.
    lazymatch type of MU' with munch _ ?mo _ => transport_after_call asegs mo m' MU' WM' end.
    clear MU' WM'.
    idtac "MARK1 after loop".
    unfold SHB. eapply dll_finish1; try eassumption; lia.
Qed.
