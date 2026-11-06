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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit LeptB_guard LeptB_guard2 Gq_guardx.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Gq_dither2_l1 Gq_dither2_l0 Gq_dither2_l0last.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_ditherTo2bppLineLow : Z := 0xa362c.

Notation D2LL_W usp lined nl bufs1 bufs2 n1 := [(usp - 112, usp); (lined, lined + nl); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)]%Z (only parsing).
Notation ONE := (Z_to_bv 64 1) (only parsing).

(* [comment removed for export] *)
Definition ditherTo2bppLineLow_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (usp lo lined nl bufs1 bufs2 n1 : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (bs1' bs2' : list byte) (wl' : list word),
    ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (D2LL_W usp lined nl bufs1 bufs2 n1) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
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
Ltac reg_equate r newv :=
  lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    let p := eval vm_compute in (bv_key r) in
    let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
    lazymatch v with Some ?x =>
      replace (MS R F pc fc rv m ro) with (MS (@bvmap_set 5 word r newv R) F pc fc rv m ro)
        by (replace newv with x by (first [reflexivity | f_equal; lia]); norm_regset; reflexivity);
      norm_regset
    end
  end.

(* [comment removed for export] *)
Lemma d2ll_finish1 : forall (ra gp tp t0 t1 t2 s0e s1e a1 a3 a5 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t4 t5 t6 : word)
    (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (jb : list byte) F fc (m0 m : mem)
    (usp lo lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (bs1 bs2 : list byte) (wl tw : list word),
  d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  munch (D2LL_W usp lined nl bufs1 bufs2 n1) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  u32arr asegs m ta tw -> Z.of_nat (length tw) = 256 -> acc asegs m ta 1024 ->
  rw_cells asegs m (usp + -112) (CB 8 jb :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0]) ->
  stk asegs m lo (usp + -112) -> lo <= usp - 112 -> usp <= 2^47 -> 0x10007fff8000 <= lo ->
  lined + nl <= lo -> bufs1 + n1 <= lo -> bufs2 + n1 <= lo ->
  evt asegs (ditherTo2bppLineLow_post ra0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 usp lo lined nl bufs1 bufs2 n1)
    (MS (mkR ra (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 lined) a1 (Z_to_bv 64 bufs1) a3 (Z_to_bv 64 ta) a5 (Z_to_bv 64 (w - 1)) a7
             s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e (Z_to_bv 64 SHB) t4 t5 t6)
        F (Z_to_bv 64 0xa38a8) fc None m (seg_rom asegs)).
Proof.
  intros until tw. intros GEO MU WM MI UB UBL ACCB UC UCL ACCC UL ULL ACCL UT UTL ACCT FR ST LO UHI LOH LLO BLO CLO.
  (* [comment removed for export] *)
  unfold SEGTOP_A, SHB in *.
  eapply evt_cut.
  { eapply d2l1_last; eassumption. }
  intros ms' PO. unfold d2l_end in PO.
  destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & s10' & s11' & t3' & t4' & t5' & t6'
                  & m' & bs1' & bs2' & wl' & -> & MU' & WM' & MI' & UB' & UBL' & ACCB' & UC' & UCL' & ACCC' & UL' & ULL' & ACCL').
  clear MI UB UBL ACCB UC UCL ACCC UL ULL ACCL UT UTL ACCT.
  lazymatch type of MU' with munch _ ?mo _ => transport_after_call asegs mo m' MU' WM' end.
  clear MU' WM'.
  idtac "MARK finish1: transported".
  lwalk (@nil Z).
  idtac "MARK finish1: epilogue walked".
  apply evt_done. unfold ditherTo2bppLineLow_post.
  do 15 eexists. exists m', bs1', bs2', wl'.
  split; [reflexivity|].
  repeat (split; [assumption|]). assumption.
Qed.


(* [comment removed for export] *)
Lemma d2ll_finish0 : forall (ra gp tp t0 t1 t2 s0e s1e a1 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t5 t6 : word)
    (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (jb : list byte) F fc (m0 m : mem)
    (usp lo lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (bs1 bs2 : list byte) (wl tw t38w : list word),
  d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  munch (D2LL_W usp lined nl bufs1 bufs2 n1) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  u32arr asegs m ta tw -> Z.of_nat (length tw) = 256 -> acc asegs m ta 1024 ->
  u32arr asegs m t38 t38w -> Z.of_nat (length t38w) = 256 -> acc asegs m t38 1024 -> Forall tsmall t38w ->
  rw_cells asegs m (usp + -112) (CB 8 jb :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0]) ->
  stk asegs m lo (usp + -112) -> lo <= usp - 112 -> usp <= 2^47 -> 0x10007fff8000 <= lo ->
  lined + nl <= lo -> bufs1 + n1 <= lo -> bufs2 + n1 <= lo ->
  evt asegs (ditherTo2bppLineLow_post ra0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 usp lo lined nl bufs1 bufs2 n1)
    (MS (mkR ra (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 lined) a1 (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) (Z_to_bv 64 ta) (Z_to_bv 64 t38) a6 a7
             s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e (Z_to_bv 64 SHB) (Z_to_bv 64 (w - 1)) t5 t6)
        F (Z_to_bv 64 0xa3cec) fc None m (seg_rom asegs)).
Proof.
  intros until t38w. intros GEO MU WM MI UB UBL ACCB UC UCL ACCC UL ULL ACCL UT UTL ACCT U38 U38L ACC38 T38S FR ST LO UHI LOH LLO BLO CLO.
  (* [comment removed for export] *)
  unfold SEGTOP_A, SHB in *.
  eapply evt_cut.
  { eapply d2l0_last; eassumption. }
  intros ms' PO. unfold d2l_end in PO.
  destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & s10' & s11' & t3' & t4' & t5' & t6'
                  & m' & bs1' & bs2' & wl' & -> & MU' & WM' & MI' & UB' & UBL' & ACCB' & UC' & UCL' & ACCC' & UL' & ULL' & ACCL').
  clear MI UB UBL ACCB UC UCL ACCC UL ULL ACCL UT UTL ACCT U38 U38L ACC38 T38S.
  lazymatch type of MU' with munch _ ?mo _ => transport_after_call asegs mo m' MU' WM' end.
  clear MU' WM'.
  idtac "MARK finish0: transported".
  lwalk (@nil Z).
  idtac "MARK finish0: epilogue walked".
  apply evt_done. unfold ditherTo2bppLineLow_post.
  do 15 eexists. exists m', bs1', bs2', wl'.
  split; [reflexivity|].
  repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Lemma ditherTo2bppLineLow1_evt : forall (ra gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo : Z) (lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (bs1 bs2 : list byte) (wl tw t38w : list word),
  d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  u32arr asegs m ta tw -> Z.of_nat (length tw) = 256 -> acc asegs m ta 1024 ->
  u32arr asegs m t38 t38w -> Z.of_nat (length t38w) = 256 -> acc asegs m t38 1024 -> Forall tsmall t38w ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo usp -> lo <= usp - 112 -> usp <= 2^47 -> 0x10007fff8000 <= lo ->
  lined + nl <= lo -> bufs1 + n1 <= lo -> bufs2 + n1 <= lo -> ta + 1024 <= lo -> t38 + 1024 <= lo -> t14 + 1024 <= lo ->
  evt asegs (ditherTo2bppLineLow_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m usp lo lined nl bufs1 bufs2 n1)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 lined) (Z_to_bv 64 w) (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) (Z_to_bv 64 ta) (Z_to_bv 64 t38) a6 ONE
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_ditherTo2bppLineLow) fc None m (seg_rom asegs)).
Proof.
  intros until t38w. intros GEO MI UB UBL ACCB UC UCL ACCC UL ULL ACCL UT UTL ACCT U38 U38L ACC38 T38S G1 G2 ST LO UHI LOH LLO BLO CLO TLO T38LO T14LO.
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & C0 & C8 & CHI & CSH & CSEG & L0 & LA4 & LNHI & LSH & LSEG
                   & TA0 & TA8 & TAHI & TASH & TASEG & T380 & T388 & T38HI & T38SH & T38SEG & T140 & T148 & T14HI & T14SH & T14SEG
                   & SEP1 & SEP2 & SEP12 & SEPT1 & SEPT2 & SEPT3 & SEP81 & SEP82 & SEP83 & SEP41 & SEP42 & SEP43).
  unfold e_ditherTo2bppLineLow, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl (D2LL_W usp lined nl bufs1 bufs2 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  lwalk [0xa367c].           (* [comment removed for export] *)
  swrap32_fix. replace (w + -1) with (w - 1) by (clear; lia).
  w1_guard HW.               (* [comment removed for export] *)
  lwalk [0xa3690; 0xa3eac].  (* [comment removed for export] *)
  lstep.
  destruct (Z.eq_dec w 1) as [W1|W2].
  - (* [comment removed for export] *)
    brT.
    fix_tripcount 16 w HW.
    eapply d2ll_finish1; try eassumption; lia.
  - (* [comment removed for export] *)
    brF.
    lwalk [0xa36cc].
    fix_tripcount 16 w HW.
    replace (0 <? lined) with true by (symmetry; apply Z.ltb_lt; clear - L0; lia).
    replace (0 <? ta) with true by (symmetry; apply Z.ltb_lt; clear - TA0; lia).
    replace (0 <? t38) with true by (symmetry; apply Z.ltb_lt; clear - T380; lia).
    cbn [Z.b2z].
    (* [comment removed for export] *)
    reg_equate (Z_to_bv 5 6) (Z_to_bv 64 (bufs1 + 1 + 0)).
    reg_equate (Z_to_bv 5 20) (Z_to_bv 64 (bufs1 + 0)).
    reg_equate (Z_to_bv 5 21) (Z_to_bv 64 (w - 1 - 0)).
    assert (Q1 : Z.of_nat (Z.to_nat (w - 1)) = w - 1 - 0) by (clear - HW; lia).
    assert (Q3 : (1 <= Z.to_nat (w - 1))%nat) by (clear - HW W2; lia).
    eapply evt_cut.
    { eapply (d2l1_pixels (Z.to_nat (w - 1)) 0); try eassumption. clear - HW; lia. }
    intros ms' PO. unfold d2l1_exit in PO.
    destruct PO as (a1' & a3' & s6' & s7' & s8' & s9' & s10' & m' & bs1' & wl' & -> & MU' & WM' & MI' & UB' & UBL' & ACCB' & UL' & ULL' & ACCL' & UT' & U38').
    (* [comment removed for export] *)
    pose proof (acc_transport _ _ _ bufs2 n1 ACCC MU' ltac:(intros i Hi; unpark LSH; unpark BSH; cbn [disjoint_from]; unfold shad, SHB; clear - Hi LSH BSH CHI C0; Z.div_mod_to_equations; lia)) as ACCC'.
    pose proof (acc_transport _ _ _ ta 1024 ACCT MU' ltac:(intros i Hi; unpark LSH; unpark BSH; cbn [disjoint_from]; unfold shad, SHB; clear - Hi LSH BSH TAHI TA0; Z.div_mod_to_equations; lia)) as ACCT'.
    clear MI UB UBL ACCB UL ULL ACCL UT U38 ACC38 ACCC ACCT G1 G2.
    unpark SEP2. unpark SEP12.
    lazymatch type of MU' with munch _ ?mo _ => transport_after_call asegs mo m' MU' WM' end.
    clear MU' WM'.
    idtac "MARK1 after loop".
    eapply d2ll_finish1; try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma ditherTo2bppLineLow0_evt : forall (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo : Z) (lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (bs1 bs2 : list byte) (wl tw t38w t14w : list word),
  d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  u32arr asegs m ta tw -> Z.of_nat (length tw) = 256 -> acc asegs m ta 1024 ->
  u32arr asegs m t38 t38w -> Z.of_nat (length t38w) = 256 -> acc asegs m t38 1024 -> Forall tsmall t38w ->
  u32arr asegs m t14 t14w -> Z.of_nat (length t14w) = 256 -> acc asegs m t14 1024 -> Forall tsmall t14w ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo usp -> lo <= usp - 112 -> usp <= 2^47 -> 0x10007fff8000 <= lo ->
  lined + nl <= lo -> bufs1 + n1 <= lo -> bufs2 + n1 <= lo -> ta + 1024 <= lo -> t38 + 1024 <= lo -> t14 + 1024 <= lo ->
  evt asegs (ditherTo2bppLineLow_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m usp lo lined nl bufs1 bufs2 n1)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 lined) (Z_to_bv 64 w) (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 t14) (Z_to_bv 64 0)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_ditherTo2bppLineLow) fc None m (seg_rom asegs)).
Proof.
  intros until t14w. intros GEO MI UB UBL ACCB UC UCL ACCC UL ULL ACCL UT UTL ACCT U38 U38L ACC38 T38S U14 U14L ACC14 T14S G1 G2 ST LO UHI LOH LLO BLO CLO TLO T38LO T14LO.
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & C0 & C8 & CHI & CSH & CSEG & L0 & LA4 & LNHI & LSH & LSEG
                   & TA0 & TA8 & TAHI & TASH & TASEG & T380 & T388 & T38HI & T38SH & T38SEG & T140 & T148 & T14HI & T14SH & T14SEG
                   & SEP1 & SEP2 & SEP12 & SEPT1 & SEPT2 & SEPT3 & SEP81 & SEP82 & SEP83 & SEP41 & SEP42 & SEP43).
  unfold e_ditherTo2bppLineLow, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl (D2LL_W usp lined nl bufs1 bufs2 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  lwalk [0xa367c].           (* [comment removed for export] *)
  swrap32_fix. replace (w + -1) with (w - 1) by (clear; lia).
  w1_guard HW.               (* [comment removed for export] *)
  lwalk [0xa399c; 0xa3eac].  (* [comment removed for export] *)
  lstep.
  destruct (Z.eq_dec w 1) as [W1|W2].
  - (* [comment removed for export] *)
    brT.
    fix_tripcount 29 w HW.
    eapply d2ll_finish0; try eassumption; lia.
  - (* [comment removed for export] *)
    brF.
    lwalk [0xa39c0].
    fix_tripcount 29 w HW.
    replace (0 <? lined) with true by (symmetry; apply Z.ltb_lt; clear - L0; lia).
    replace (0 <? ta) with true by (symmetry; apply Z.ltb_lt; clear - TA0; lia).
    cbn [Z.b2z].
    assert (Q1 : Z.of_nat (Z.to_nat (w - 1)) = w - 1 - 0) by (clear - HW; lia).
    assert (Q3 : (1 <= Z.to_nat (w - 1))%nat) by (clear - HW W2; lia).
    eapply evt_cut.
    { eapply (d2l0_pixels (Z.to_nat (w - 1)) 0); try eassumption. clear - HW; lia. }
    intros ms' PO. unfold d2l0_exit in PO.
    destruct PO as (ra' & t0' & t1' & t2' & a1' & a7' & s3' & s6' & s7' & s8' & s9' & s10' & s11' & m' & bs1' & bs2' & wl' & -> & MU' & WM' & MI'
                    & UB' & UBL' & ACCB' & UC' & UCL' & ACCC' & UL' & ULL' & ACCL' & UT' & U38' & U14').
    (* [comment removed for export] *)
    pose proof (acc_transport _ _ _ ta 1024 ACCT MU' ltac:(intros i Hi; unpark LSH; unpark BSH; unpark CSH; cbn [disjoint_from]; unfold shad, SHB; clear - Hi LSH BSH CSH TAHI TA0; Z.div_mod_to_equations; lia)) as ACCT'.
    pose proof (acc_transport _ _ _ t38 1024 ACC38 MU' ltac:(intros i Hi; unpark LSH; unpark BSH; unpark CSH; cbn [disjoint_from]; unfold shad, SHB; clear - Hi LSH BSH CSH T38HI T380; Z.div_mod_to_equations; lia)) as ACC38'.
    clear MI UB UBL ACCB UC UCL ACCC UL ULL ACCL UT U38 U14 ACCT ACC38 ACC14 U14' U14L T14S G1 G2.
    lazymatch type of MU' with munch _ ?mo _ => transport_after_call asegs mo m' MU' WM' end.
    clear MU' WM'.
    idtac "MARK0 after loop".
    eapply d2ll_finish0; try eassumption; lia.
Qed.
