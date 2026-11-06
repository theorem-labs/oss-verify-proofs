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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_trans Gq_dither2_l1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


Notation D2L0_W lined nl bufs1 bufs2 n1 := [(lined, lined + nl); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)]%Z (only parsing).
Notation CMASK := (Z_to_bv 64 (-1073741824)) (only parsing).
Notation MASK28 := (Z_to_bv 64 268435455) (only parsing).

(* [comment removed for export] *)
Definition d2l0_exit (sp gp tp s0 s1 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (tw t38w t14w : list word) : machine_state -> Prop :=
  fun ms' => exists (ra' a0' a1' a2' a3' a4' s5' t3' t4' t5' t6' : word) (m' : mem) (bs1' bs2' : list byte) (wl' : list word),
    ms' = MS (mkR ra' sp gp tp (Z_to_bv 64 (bufs1 + (w - 1))) (Z_to_bv 64 0) (Z_to_bv 64 (bufs2 + (w - 1))) s0 s1 a0' a1' a2' a3' a4'
                  (Z_to_bv 64 lined) (Z_to_bv 64 (2 * (w - 1))) (Z_to_bv 64 (w - 1))
                  (Z_to_bv 64 t14) (Z_to_bv 64 30) (Z_to_bv 64 SHB) s5' CMASK MASK28 (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 bufs2) s11
                  t3' t4' t5' t6')
             F (Z_to_bv 64 0x9e970) fc None m' (seg_rom asegs)
    /\ munch (D2L0_W lined nl bufs1 bufs2 n1) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' bufs1 bs1' /\ Z.of_nat (length bs1') = n1 /\ acc asegs m' bufs1 n1
    /\ u8arr asegs m' bufs2 bs2' /\ Z.of_nat (length bs2') = n1 /\ acc asegs m' bufs2 n1
    /\ u32arr asegs m' lined wl' /\ 4 * Z.of_nat (length wl') = nl /\ acc asegs m' lined nl
    /\ u32arr asegs m' ta tw /\ acc asegs m' ta 1024 /\ u32arr asegs m' t38 t38w /\ acc asegs m' t38 1024 /\ u32arr asegs m' t14 t14w /\ acc asegs m' t14 1024.

(* [comment removed for export] *)
Lemma d2_tabs_carry : forall (m m' : mem) (lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (tw t38w t14w : list word),
  d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  munch (D2L0_W lined nl bufs1 bufs2 n1) m m' -> wmono asegs m m' ->
  u32arr asegs m ta tw -> Z.of_nat (length tw) = 256 -> acc asegs m ta 1024 ->
  u32arr asegs m t38 t38w -> Z.of_nat (length t38w) = 256 -> acc asegs m t38 1024 ->
  u32arr asegs m t14 t14w -> Z.of_nat (length t14w) = 256 -> acc asegs m t14 1024 ->
  u32arr asegs m' ta tw /\ acc asegs m' ta 1024 /\ u32arr asegs m' t38 t38w /\ acc asegs m' t38 1024 /\ u32arr asegs m' t14 t14w /\ acc asegs m' t14 1024.
Proof.
  intros until t14w. intros GEO MU WM UT UTL ACCT U38 U38L ACC38 U14 U14L ACC14.
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & C0 & C8 & CHI & CSH & CSEG & L0 & LA4 & LNHI & LSH & LSEG
                   & TA0 & TA8 & TAHI & TASH & TASEG & T380 & T388 & T38HI & T38SH & T38SEG & T140 & T148 & T14HI & T14SH & T14SEG
                   & SEP1 & SEP2 & SEP12 & SEPT1 & SEPT2 & SEPT3 & SEP81 & SEP82 & SEP83 & SEP41 & SEP42 & SEP43).
  unfold SEGTOP_A, SHB in *.
  assert (DT : disjoint_from (D2L0_W lined nl bufs1 bufs2 n1) ta (4 * Z.of_nat (length tw))) by (rewrite UTL; cbn [disjoint_from]; clear - SEPT1 SEPT2 SEPT3; lia).
  assert (D38 : disjoint_from (D2L0_W lined nl bufs1 bufs2 n1) t38 (4 * Z.of_nat (length t38w))) by (rewrite U38L; cbn [disjoint_from]; clear - SEP81 SEP82 SEP83; lia).
  assert (D14 : disjoint_from (D2L0_W lined nl bufs1 bufs2 n1) t14 (4 * Z.of_nat (length t14w))) by (rewrite U14L; cbn [disjoint_from]; clear - SEP41 SEP42 SEP43; lia).
  assert (ST : forall a, 0 < a -> a + 1024 <= 2^47 -> disjoint_from (D2L0_W lined nl bufs1 bufs2 n1) (shad a) (shad (a + 1024 - 1) + 1 - shad a)).
  { intros a A0 AHI. unfold shad, SHB. cbn [disjoint_from]. clear - A0 AHI LSH BSH CSH L0 B0 C0 LHI HW WN. Z.div_mod_to_equations. lia. }
  split; [exact (u32arr_transport asegs _ m m' ta tw UT MU WM DT)|].
  split; [exact (acc_transport _ m m' ta 1024 ACCT MU ltac:(lia) (ST ta TA0 TAHI))|].
  split; [exact (u32arr_transport asegs _ m m' t38 t38w U38 MU WM D38)|].
  split; [exact (acc_transport _ m m' t38 1024 ACC38 MU ltac:(lia) (ST t38 T380 T38HI))|].
  split; [exact (u32arr_transport asegs _ m m' t14 t14w U14 MU WM D14)|].
  exact (acc_transport _ m m' t14 1024 ACC14 MU ltac:(lia) (ST t14 T140 T14HI)).
Qed.
Lemma d2_tabs_u32 : forall (m m' : mem) (lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (tw t38w t14w : list word),
  d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  munch (D2L0_W lined nl bufs1 bufs2 n1) m m' -> wmono asegs m m' ->
  u32arr asegs m ta tw -> Z.of_nat (length tw) = 256 ->
  u32arr asegs m t38 t38w -> Z.of_nat (length t38w) = 256 ->
  u32arr asegs m t14 t14w -> Z.of_nat (length t14w) = 256 ->
  u32arr asegs m' ta tw /\ u32arr asegs m' t38 t38w /\ u32arr asegs m' t14 t14w.
Proof.
  intros until t14w. intros GEO MU WM UT UTL U38 U38L U14 U14L.
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & C0 & C8 & CHI & CSH & CSEG & L0 & LA4 & LNHI & LSH & LSEG
                   & TA0 & TA8 & TAHI & TASH & TASEG & T380 & T388 & T38HI & T38SH & T38SEG & T140 & T148 & T14HI & T14SH & T14SEG
                   & SEP1 & SEP2 & SEP12 & SEPT1 & SEPT2 & SEPT3 & SEP81 & SEP82 & SEP83 & SEP41 & SEP42 & SEP43).
  assert (DT : disjoint_from (D2L0_W lined nl bufs1 bufs2 n1) ta (4 * Z.of_nat (length tw))) by (rewrite UTL; cbn [disjoint_from]; clear - SEPT1 SEPT2 SEPT3; lia).
  assert (D38 : disjoint_from (D2L0_W lined nl bufs1 bufs2 n1) t38 (4 * Z.of_nat (length t38w))) by (rewrite U38L; cbn [disjoint_from]; clear - SEP81 SEP82 SEP83; lia).
  assert (D14 : disjoint_from (D2L0_W lined nl bufs1 bufs2 n1) t14 (4 * Z.of_nat (length t14w))) by (rewrite U14L; cbn [disjoint_from]; clear - SEP41 SEP42 SEP43; lia).
  split; [exact (u32arr_transport asegs _ m m' ta tw UT MU WM DT)|].
  split; [exact (u32arr_transport asegs _ m m' t38 t38w U38 MU WM D38)|].
  exact (u32arr_transport asegs _ m m' t14 t14w U14 MU WM D14).
Qed.

Lemma d2l0_pixels : forall (k : nat) (j : Z)
    (ra sp gp tp s0 s1 a0 a1 a2 a3 a4 s5 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (bs1 bs2 : list byte) (wl tw t38w t14w : list word),
  Z.of_nat k = w - 1 - j -> 0 <= j -> (1 <= k)%nat -> d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  u32arr asegs m ta tw -> Z.of_nat (length tw) = 256 -> acc asegs m ta 1024 ->
  u32arr asegs m t38 t38w -> Z.of_nat (length t38w) = 256 -> acc asegs m t38 1024 ->
  u32arr asegs m t14 t14w -> Z.of_nat (length t14w) = 256 -> acc asegs m t14 1024 ->
  evt asegs (d2l0_exit sp gp tp s0 s1 s11 F fc m lined nl bufs1 bufs2 n1 ta t38 t14 w tw t38w t14w)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (bufs1 + j)) (Z_to_bv 64 (w - 1 - j)) (Z_to_bv 64 (bufs2 + j)) s0 s1 a0 a1 a2 a3 a4
             (Z_to_bv 64 lined) (Z_to_bv 64 (2 * j)) (Z_to_bv 64 j)
             (Z_to_bv 64 t14) (Z_to_bv 64 30) (Z_to_bv 64 SHB) s5 CMASK MASK28 (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 bufs2) s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x9e724) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp s0 s1 a0 a1 a2 a3 a4 s5 s11 t3 t4 t5 t6 F fc m lined nl bufs1 bufs2 n1 ta t38 t14 w bs1 bs2 wl tw t38w t14w
    HK HJ HK1 GEO MI UB UBL ACCB UC UCL ACCC UL ULL ACCL UT UTL ACCT U38 U38L ACC38 U14 U14L ACC14.
  { lia. }
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & C0 & C8 & CHI & CSH & CSEG & L0 & LA4 & LNHI & LSH & LSEG
                   & TA0 & TA8 & TAHI & TASH & TASEG & T380 & T388 & T38HI & T38SH & T38SEG & T140 & T148 & T14HI & T14SH & T14SEG
                   & SEP1 & SEP2 & SEP12 & SEPT1 & SEPT2 & SEPT3 & SEP81 & SEP82 & SEP83 & SEP41 & SEP42 & SEP43).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (D2L0_W lined nl bufs1 bufs2 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  (* [comment removed for export] *)
  assert (CONT : forall (ra' a0' a1' a2' a3' a4' s5' t3' t4' t5' t6' : word) (mm : mem) (bs1' bs2' : list byte) (wl' : list word),
    munch (D2L0_W lined nl bufs1 bufs2 n1) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    u8arr asegs mm bufs1 bs1' -> Z.of_nat (length bs1') = n1 -> acc asegs mm bufs1 n1 ->
    u8arr asegs mm bufs2 bs2' -> Z.of_nat (length bs2') = n1 -> acc asegs mm bufs2 n1 ->
    u32arr asegs mm lined wl' -> 4 * Z.of_nat (length wl') = nl -> acc asegs mm lined nl ->
    evt asegs (d2l0_exit sp gp tp s0 s1 s11 F fc m lined nl bufs1 bufs2 n1 ta t38 t14 w tw t38w t14w)
      (MS (mkR ra' sp gp tp (Z_to_bv 64 (bufs1 + j + 1)) (Z_to_bv 64 (w - 1 - j)) (Z_to_bv 64 (bufs2 + j + 1)) s0 s1 a0' a1' a2' a3' a4'
             (Z_to_bv 64 lined) (Z_to_bv 64 (2 * j)) (Z_to_bv 64 j)
             (Z_to_bv 64 t14) (Z_to_bv 64 30) (Z_to_bv 64 2147450880) s5' (Z_to_bv 64 (-1073741824)) (Z_to_bv 64 268435455) (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 bufs2) s11
             t3' t4' t5' t6')
          F (Z_to_bv 64 0x9e8bc) fc None mm (seg_rom asegs))).
  { intros ra' a0' a1' a2' a3' a4' s5' t3' t4' t5' t6' mm bs1' bs2' wl' MU1 WM1 MI1 UB1 UBL1 ACCB1 UC1 UCL1 ACCC1 UL1 ULL1 ACCL1.
    destruct (d2_tabs_carry m mm _ _ _ _ _ _ _ _ _ _ _ _ GEO MU1 WM1 UT UTL ACCT U38 U38L ACC38 U14 U14L ACC14) as (UT1 & ACCT1 & U381 & ACC381 & U141 & ACC141).
    clear MI UB UBL ACCB UC UCL ACCC UL ULL ACCL MU WM UT ACCT U38 ACC38 U14 ACC14.
    lwalk [0x9e724; 0x9e970].
    replace (bufs1 + j + 1) with (bufs1 + (j + 1)) by lia. replace (bufs2 + j + 1) with (bufs2 + (j + 1)) by lia.
    replace (2 * j + 2) with (2 * (j + 1)) by lia. replace (w - 1 - j + -1) with (w - 1 - (j + 1)) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w - 1) by lia. rewrite EJ in *. replace (w - 1 - (w - 1)) with 0 by lia.
      brF. lwalk [0x9e724; 0x9e970].
      apply evt_done. unfold d2l0_exit, SHB. do 11 eexists. exists mm, bs1', bs2', wl'. split; [reflexivity|].
      repeat (split; [assumption|]). assumption.
    - brT.
      eapply evt_cut.
      + eapply (IH (j + 1)) with (bs1 := bs1') (bs2 := bs2') (wl := wl') (w := w) (n1 := n1) (nl := nl); try eassumption; try lia.
      + intros ms' PO. apply evt_done. unfold d2l0_exit in PO |- *.
        destruct PO as (ra'' & a0'' & a1'' & a2'' & a3'' & a4'' & s5'' & t3'' & t4'' & t5'' & t6'' & m' & bs1'' & bs2'' & wl'' & E & MU' & WM' & R).
        exists ra'', a0'', a1'', a2'', a3'', a4'', s5'', t3'', t4'', t5'', t6'', m', bs1'', bs2'', wl''.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R]. }
  (* [comment removed for export] *)
  pose proof (lxor3_eq (bufs1 + j)) as LX0. pose proof (lxor3_eq (bufs1 + j + 1)) as LX1.
  pose proof (lxor3_eq (bufs2 + j)) as LX2. pose proof (lxor3_eq (bufs2 + j + 1)) as LX3.
  assert (IDX0 : 0 <= Z.lxor (bufs1 + j) 3 - bufs1 < n1) by (rewrite LX0; clear - HJ HK HW WN N4 B8; Z.div_mod_to_equations; lia).
  assert (IDX1 : 0 <= Z.lxor (bufs1 + j + 1) 3 - bufs1 < n1) by (rewrite LX1; clear - HJ HK HW WN N4 B8; Z.div_mod_to_equations; lia).
  assert (IDX2 : 0 <= Z.lxor (bufs2 + j) 3 - bufs2 < n1) by (rewrite LX2; clear - HJ HK HW WN N4 C8; Z.div_mod_to_equations; lia).
  assert (IDX3 : 0 <= Z.lxor (bufs2 + j + 1) 3 - bufs2 < n1) by (rewrite LX3; clear - HJ HK HW WN N4 C8; Z.div_mod_to_equations; lia).
  assert (TAIL : forall (z1 z2 z3 : Z) (ra' s5' t4' t5' t6' : word) (mm : mem) (bs1' bs2' : list byte) (wl' : list word),
    munch (D2L0_W lined nl bufs1 bufs2 n1) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    u8arr asegs mm bufs1 bs1' -> Z.of_nat (length bs1') = n1 -> acc asegs mm bufs1 n1 ->
    u8arr asegs mm bufs2 bs2' -> Z.of_nat (length bs2') = n1 -> acc asegs mm bufs2 n1 ->
    u32arr asegs mm lined wl' -> 4 * Z.of_nat (length wl') = nl -> acc asegs mm lined nl ->
    evt asegs (d2l0_exit sp gp tp s0 s1 s11 F fc m lined nl bufs1 bufs2 n1 ta t38 t14 w tw t38w t14w)
      (MS (mkR ra' sp gp tp (Z_to_bv 64 (bufs1 + j + 1)) (Z_to_bv 64 (w - 1 - j)) (Z_to_bv 64 (bufs2 + j + 1)) s0 s1
             (Z_to_bv 64 (Z.lxor (bufs1 + j + 1) 3)) (Z_to_bv 64 (Z.lxor (bufs2 + j) 3)) (Z_to_bv 64 (Z.lxor (bufs2 + j + 1) 3))
             (Z_to_bv 64 z3) (Z_to_bv 64 z2)
             (Z_to_bv 64 lined) (Z_to_bv 64 (2 * j)) (Z_to_bv 64 j)
             (Z_to_bv 64 t14) (Z_to_bv 64 30) (Z_to_bv 64 2147450880) s5' (Z_to_bv 64 (-1073741824)) (Z_to_bv 64 268435455) (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 bufs2) s11
             (Z_to_bv 64 z1) t4' t5' t6')
          F (Z_to_bv 64 0x9e880) fc None mm (seg_rom asegs))).
  { intros z1 z2 z3 ra' s5' t4' t5' t6' mm bs1' bs2' wl' MU1 WM1 MI1 UB1 UBL1 ACCB1 UC1 UCL1 ACCC1 UL1 ULL1 ACCL1.
    clear MI UB UBL ACCB UC UCL ACCC UL ULL ACCL MU WM UT ACCT U38 ACC38 U14 ACC14.
    lwalk [0x9e890; 0x9e970].
    remember (Z.lxor (bufs1 + j + 1) 3 - bufs1) as ix1 eqn:EIX1.
    unpark BSH. unpark SEP1. unpark SEP12.
    arr_sb bufs1 ix1 (Z.lxor (bufs1 + j + 1) 3).
    park_disj.
    lwalk [0x9e8a4; 0x9e970].
    remember (Z.lxor (bufs2 + j) 3 - bufs2) as ix2 eqn:EIX2.
    unpark CSH. unpark SEP2. unpark SEP12.
    arr_sb bufs2 ix2 (Z.lxor (bufs2 + j) 3).
    park_disj.
    lwalk [0x9e8b8; 0x9e970].
    remember (Z.lxor (bufs2 + j + 1) 3 - bufs2) as ix3 eqn:EIX3.
    unpark CSH. unpark SEP2. unpark SEP12.
    arr_sb bufs2 ix3 (Z.lxor (bufs2 + j + 1) 3).
    park_disj.
    eapply CONT; eassumption. }
  hide UT. hide U38. hide U14.
  (* [comment removed for export] *)
  lwalk [0x9e970; 0x9e880].
  replace (Z.land (j / 16) 268435455) with (j / 16)
    by (change 268435455 with (Z.ones 28); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; clear - HJ HK HW; Z.div_mod_to_equations; lia).
  replace (lined + j / 16 * 4) with (lined + 4 * (j / 16)) by (clear; lia).
  replace (Z.land (lined + 4 * (j / 16)) 18446744073709551615) with (lined + 4 * (j / 16))
    by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); symmetry; apply Z.mod_small; clear - HJ HK HW WL L4 L0 LNHI; Z.div_mod_to_equations; lia).
  assert (ULW : Z.of_nat (length wl) = nl / 4) by (clear - ULL L4; Z.div_mod_to_equations; lia).
  assert (JL : 0 <= j / 16 < nl / 4) by (clear - HJ HK HW WL L4; Z.div_mod_to_equations; lia).
  lwalk [0x9e970; 0x9e880].
  (* [comment removed for export] *)
  destruct UB as [HB WB].
  destruct (bytes_at_read1 m bufs1 bs1 (Z.lxor (bufs1 + j) 3 - bufs1) HB ltac:(lia)) as (ov & R).
  replace (bufs1 + (Z.lxor (bufs1 + j) 3 - bufs1)) with (Z.lxor (bufs1 + j) 3) in R by lia.
  lstep. clear R.
  assert (UB : u8arr asegs m bufs1 bs1) by (split; assumption).
  clear HB WB.
  pose proof (bv_unsigned_in_range 8 ov) as OVR. unfold bv_modulus in OVR. change (2 ^ Z.of_N 8) with 256 in OVR.
  set (oz := bv_unsigned ov) in *.
  lwalk [0x9e970; 0x9e880].
  (* [comment removed for export] *)
  replace (ta + oz * 4) with (ta + 4 * oz) by (clear; lia).
  destruct (u32arr_nth wl (j / 16) ltac:(lia)) as (dv & NTHD).
  pose proof (u32arr_read asegs m lined wl (j / 16) dv _ UL NTHD ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9e970; 0x9e880].
  destruct (u32arr_nth tw oz ltac:(lia)) as (tv & NTHT).
  pose proof UT as UTc. unfold hid in UTc.
  pose proof (u32arr_read asegs m ta tw oz tv _ UTc NTHT ltac:(lia) eq_refl) as R.
  lstep. clear R UTc.
  lwalk [0x9e970; 0x9e880; 0x9e7a4].
  (* [comment removed for export] *)
  gen_zreg 11.
  clear ULL.
  unpark LSH. unpark SEP1. unpark SEP2.
  arr_sw lined (j / 16) (lined + 4 * (j / 16)).
  park_disj.
  lazymatch goal with H : Z.of_nat (length ?ws) = nl / 4 |- _ => assert (ULL : 4 * Z.of_nat (length ws) = nl) by (rewrite H; clear - L4; Z.div_mod_to_equations; lia) end.
  (* [comment removed for export] *)
  lwalk [0x9e970; 0x9e880].
  lazymatch goal with UBx : u8arr asegs ?mm bufs1 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof UBx as [HB WB];
    destruct (bytes_at_read1 mm bufs1 bsx (Z.lxor (bufs1 + j + 1) 3 - bufs1) HB ltac:(lia)) as (rv & R) end.
  replace (bufs1 + (Z.lxor (bufs1 + j + 1) 3 - bufs1)) with (Z.lxor (bufs1 + j + 1) 3) in R by lia.
  lstep. clear R HB WB.
  lwalk [0x9e970; 0x9e880].
  lazymatch goal with UCx : u8arr asegs ?mm bufs2 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof UCx as [HB WB];
    destruct (bytes_at_read1 mm bufs2 bsx (Z.lxor (bufs2 + j) 3 - bufs2) HB ltac:(lia)) as (bvv & R) end.
  replace (bufs2 + (Z.lxor (bufs2 + j) 3 - bufs2)) with (Z.lxor (bufs2 + j) 3) in R by lia.
  lstep. clear R HB WB.
  lwalk [0x9e970; 0x9e880].
  lazymatch goal with UCx : u8arr asegs ?mm bufs2 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof UCx as [HB WB];
    destruct (bytes_at_read1 mm bufs2 bsx (Z.lxor (bufs2 + j + 1) 3 - bufs2) HB ltac:(lia)) as (dvv & R) end.
  replace (bufs2 + (Z.lxor (bufs2 + j + 1) 3 - bufs2)) with (Z.lxor (bufs2 + j + 1) 3) in R by lia.
  lstep. clear R HB WB.
  replace (t38 + oz * 4) with (t38 + 4 * oz) by (clear; lia).
  lwalk [0x9e970; 0x9e880].
  (* [comment removed for export] *)
  destruct (u32arr_nth t38w oz ltac:(lia)) as (pv & NTHP).
  lazymatch goal with MUx : munch _ m ?mc, WMx : wmono asegs m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof U38 as U38c; unfold hid in U38c;
    apply (fun H => u32arr_transport asegs _ m mc t38 t38w H MUx WMx) in U38c;
    [ pose proof (u32arr_read asegs mc t38 t38w oz pv _ U38c NTHP ltac:(lia) eq_refl) as R
    | rewrite U38L; cbn [disjoint_from]; clear - SEP81 SEP82 SEP83; unfold parked in *; lia ] end.
  lstep. clear R U38c.
  replace (t14 + oz * 4) with (t14 + 4 * oz) by (clear; lia).
  lwalk [0x9e970; 0x9e880].
  destruct (u32arr_nth t14w oz ltac:(lia)) as (qv & NTHQ).
  lazymatch goal with MUx : munch _ m ?mc, WMx : wmono asegs m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof U14 as U14c; unfold hid in U14c;
    apply (fun H => u32arr_transport asegs _ m mc t14 t14w H MUx WMx) in U14c;
    [ pose proof (u32arr_read asegs mc t14 t14w oz qv _ U14c NTHQ ltac:(lia) eq_refl) as R
    | rewrite U14L; cbn [disjoint_from]; clear - SEP41 SEP42 SEP43; unfold parked in *; lia ] end.
  lstep. clear R U14c.
  pose proof (bv_unsigned_in_range 8 rv) as RVR. unfold bv_modulus in RVR. change (2 ^ Z.of_N 8) with 256 in RVR.
  pose proof (bv_unsigned_in_range 8 bvv) as BVR. unfold bv_modulus in BVR. change (2 ^ Z.of_N 8) with 256 in BVR.
  pose proof (bv_unsigned_in_range 8 dvv) as DVR. unfold bv_modulus in DVR. change (2 ^ Z.of_N 8) with 256 in DVR.
  lwalk [0x9e970; 0x9e880].
  (* [comment removed for export] *)
  let rec go _ := (lwalk [0x9e970; 0x9e880]; first [ eapply TAIL; eassumption | let H := fresh "BR" in brfork H; [go tt | go tt] ]) in go tt.
Qed.

(* [comment removed for export] *)
Definition d2l0_end (ra sp gp tp t0 t1 t2 s0 s1 s2 s5 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lined nl bufs1 bufs2 n1 ta t38 t14 : Z) (tw t38w t14w : list word) : machine_state -> Prop :=
  fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' : word) (m' : mem) (bs1' bs2' : list byte) (wl' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' (Z_to_bv 64 bufs1)
                  s2 (Z_to_bv 64 30) (Z_to_bv 64 SHB) s5 CMASK MASK28 (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 bufs2) s11
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x9ea64) fc None m' (seg_rom asegs)
    /\ munch (D2L0_W lined nl bufs1 bufs2 n1) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' bufs1 bs1' /\ Z.of_nat (length bs1') = n1 /\ acc asegs m' bufs1 n1
    /\ u8arr asegs m' bufs2 bs2' /\ Z.of_nat (length bs2') = n1 /\ acc asegs m' bufs2 n1
    /\ u32arr asegs m' lined wl' /\ 4 * Z.of_nat (length wl') = nl /\ acc asegs m' lined nl
    /\ u32arr asegs m' ta tw /\ acc asegs m' ta 1024 /\ u32arr asegs m' t38 t38w /\ acc asegs m' t38 1024 /\ u32arr asegs m' t14 t14w /\ acc asegs m' t14 1024.

(* [comment removed for export] *)
Lemma d2l0_lastcol : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a3 a4 a6 a7 s2 s5 s11 t3 t4 t5 t6 : word) F fc (m0 m : mem)
    (sa lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (bs1 bs2 : list byte) (wl tw t38w t14w : list word),
  d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  munch (D2L0_W lined nl bufs1 bufs2 n1) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  u32arr asegs m0 ta tw -> Z.of_nat (length tw) = 256 -> acc asegs m ta 1024 ->
  u32arr asegs m0 t38 t38w -> Z.of_nat (length t38w) = 256 -> acc asegs m t38 1024 ->
  u32arr asegs m0 t14 t14w -> Z.of_nat (length t14w) = 256 -> acc asegs m t14 1024 ->
  rw_cells asegs m (sa + 136) [C8 (Z_to_bv 64 bufs1)] ->
  evt asegs (d2l0_end ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 sa) s2 s5 s11 t3 t4 t5 t6 F fc m0 lined nl bufs1 bufs2 n1 ta t38 t14 tw t38w t14w)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 sa) a0 a1 (Z_to_bv 64 (w - 1)) a3 a4 (Z_to_bv 64 lined) a6 a7
             s2 (Z_to_bv 64 30) (Z_to_bv 64 SHB) s5 CMASK MASK28 (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 bufs2) s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x9e974) fc None m (seg_rom asegs)).
Proof.
  intros until t14w. intros GEO MU WM MI UB UBL ACCB UC UCL ACCC UL ULL ACCL UT UTL ACCT U38 U38L ACC38 U14 U14L ACC14 CA.
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & C0 & C8 & CHI & CSH & CSEG & L0 & LA4 & LNHI & LSH & LSEG
                   & TA0 & TA8 & TAHI & TASH & TASEG & T380 & T388 & T38HI & T38SH & T38SEG & T140 & T148 & T14HI & T14SH & T14SEG
                   & SEP1 & SEP2 & SEP12 & SEPT1 & SEPT2 & SEPT3 & SEP81 & SEP82 & SEP83 & SEP41 & SEP42 & SEP43).
  unfold SEGTOP_A, SHB in *.
  park_disj.
  hide UT. hide U38. hide U14.
  pose proof (lxor3_eq (bufs1 + (w - 1))) as LX0. pose proof (lxor3_eq (bufs2 + (w - 1))) as LX2.
  assert (IDX0 : 0 <= Z.lxor (bufs1 + (w - 1)) 3 - bufs1 < n1) by (rewrite LX0; clear - HW WN N4 B8; Z.div_mod_to_equations; lia).
  assert (IDX2 : 0 <= Z.lxor (bufs2 + (w - 1)) 3 - bufs2 < n1) by (rewrite LX2; clear - HW WN N4 C8; Z.div_mod_to_equations; lia).
  lwalk [0x9ea64].
  change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by (clear; lia). change (2 ^ 64) with 18446744073709551616.
  rewrite (srliw_idx (w - 1) 16) by (clear - HW; lia).
  replace (lined + (w - 1) / 16 * 4) with (lined + 4 * ((w - 1) / 16)) by (clear; lia).
  replace ((lined + 4 * ((w - 1) / 16)) mod 18446744073709551616) with (lined + 4 * ((w - 1) / 16))
    by (symmetry; apply Z.mod_small; clear - HW WL L4 L0 LNHI; Z.div_mod_to_equations; lia).
  assert (ULW : Z.of_nat (length wl) = nl / 4) by (clear - ULL L4; Z.div_mod_to_equations; lia).
  assert (JL : 0 <= (w - 1) / 16 < nl / 4) by (clear - HW WL L4; Z.div_mod_to_equations; lia).
  lwalk [0x9ea64].
  destruct UB as [HB WB].
  destruct (bytes_at_read1 m bufs1 bs1 (Z.lxor (bufs1 + (w - 1)) 3 - bufs1) HB ltac:(lia)) as (ov & R).
  replace (bufs1 + (Z.lxor (bufs1 + (w - 1)) 3 - bufs1)) with (Z.lxor (bufs1 + (w - 1)) 3) in R by lia.
  lstep. clear R.
  assert (UB : u8arr asegs m bufs1 bs1) by (split; assumption).
  clear HB WB.
  pose proof (bv_unsigned_in_range 8 ov) as OVR. unfold bv_modulus in OVR. change (2 ^ Z.of_N 8) with 256 in OVR.
  set (oz := bv_unsigned ov) in *.
  lwalk [0x9ea64].
  replace (ta + oz * 4) with (ta + 4 * oz) by (clear; lia).
  destruct (u32arr_nth wl ((w - 1) / 16) ltac:(lia)) as (dv & NTHD).
  pose proof (u32arr_read asegs m lined wl ((w - 1) / 16) dv _ UL NTHD ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9ea64].
  destruct (u32arr_nth tw oz ltac:(lia)) as (tv & NTHT).
  lazymatch goal with MUx : munch _ m0 ?mc, WMx : wmono asegs m0 ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof UT as UTc; unfold hid in UTc;
    apply (fun H => u32arr_transport asegs _ m0 mc ta tw H MUx WMx) in UTc;
    [ pose proof (u32arr_read asegs mc ta tw oz tv _ UTc NTHT ltac:(lia) eq_refl) as R
    | rewrite UTL; cbn [disjoint_from]; clear - SEPT1 SEPT2 SEPT3; unfold parked in *; lia ] end.
  lstep. clear R UTc.
  lwalk [0x9ea64; 0x9e9fc].
  gen_zreg 11.
  clear ULL.
  unpark LSH. unpark SEP1. unpark SEP2.
  arr_sw lined ((w - 1) / 16) (lined + 4 * ((w - 1) / 16)).
  park_disj.
  lazymatch goal with H : Z.of_nat (length ?ws) = nl / 4 |- _ => assert (ULL : 4 * Z.of_nat (length ws) = nl) by (rewrite H; clear - L4; Z.div_mod_to_equations; lia) end.
  lwalk [0x9ea64].
  lazymatch goal with UCx : u8arr asegs ?mm bufs2 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof UCx as [HB WB];
    destruct (bytes_at_read1 mm bufs2 bsx (Z.lxor (bufs2 + (w - 1)) 3 - bufs2) HB ltac:(lia)) as (bvv & R) end.
  replace (bufs2 + (Z.lxor (bufs2 + (w - 1)) 3 - bufs2)) with (Z.lxor (bufs2 + (w - 1)) 3) in R by lia.
  lstep. clear R HB WB.
  replace (t38 + oz * 4) with (t38 + 4 * oz) by (clear; lia).
  lwalk [0x9ea64].
  destruct (u32arr_nth t38w oz ltac:(lia)) as (pv & NTHP).
  lazymatch goal with MUx : munch _ m0 ?mc, WMx : wmono asegs m0 ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof U38 as U38c; unfold hid in U38c;
    apply (fun H => u32arr_transport asegs _ m0 mc t38 t38w H MUx WMx) in U38c;
    [ pose proof (u32arr_read asegs mc t38 t38w oz pv _ U38c NTHP ltac:(lia) eq_refl) as R
    | rewrite U38L; cbn [disjoint_from]; clear - SEP81 SEP82 SEP83; unfold parked in *; lia ] end.
  lstep. clear R U38c.
  pose proof (bv_unsigned_in_range 8 bvv) as BVR. unfold bv_modulus in BVR. change (2 ^ Z.of_N 8) with 256 in BVR.
  lwalk [0x9ea64; 0x9ea50].
  (* [comment removed for export] *)
  unfold hid in UT, U38, U14.
  lwalk [0x9ea64; 0x9ea60].
  let H := fresh "BR" in brfork H.
  - lwalk [0x9ea64; 0x9ea60]. let H := fresh "BR" in brfork H.
    + lwalk [0x9ea64; 0x9ea60].
      gen_zreg 11.
      remember (Z.lxor (bufs2 + (w - 1)) 3 - bufs2) as ix2 eqn:EIX2.
      unpark CSH. unpark SEP2. unpark SEP12.
      arr_sb bufs2 ix2 (Z.lxor (bufs2 + (w - 1)) 3).
      park_disj.
      apply evt_done. unfold d2l0_end. do 7 eexists.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
        lazymatch goal with UBx : u8arr asegs mm bufs1 ?b1, UCx : u8arr asegs mm bufs2 ?b2, ULx : u32arr asegs mm lined ?wlx, MUx : munch _ m0 mm, WMx : wmono asegs m0 mm |- _ =>
          exists mm, b1, b2, wlx;
          destruct (d2_tabs_u32 m0 mm _ _ _ _ _ _ _ _ _ _ _ _ GEO MUx WMx UT UTL U38 U38L U14 U14L) as (UTf & U38f & U14f)
        end end.
      split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
    + lwalk [0x9ea64; 0x9ea60].
      gen_zreg 11.
      remember (Z.lxor (bufs2 + (w - 1)) 3 - bufs2) as ix2 eqn:EIX2.
      unpark CSH. unpark SEP2. unpark SEP12.
      arr_sb bufs2 ix2 (Z.lxor (bufs2 + (w - 1)) 3).
      park_disj.
      apply evt_done. unfold d2l0_end. do 7 eexists.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
        lazymatch goal with UBx : u8arr asegs mm bufs1 ?b1, UCx : u8arr asegs mm bufs2 ?b2, ULx : u32arr asegs mm lined ?wlx, MUx : munch _ m0 mm, WMx : wmono asegs m0 mm |- _ =>
          exists mm, b1, b2, wlx;
          destruct (d2_tabs_u32 m0 mm _ _ _ _ _ _ _ _ _ _ _ _ GEO MUx WMx UT UTL U38 U38L U14 U14L) as (UTf & U38f & U14f)
        end end.
      split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  - lwalk [0x9ea64; 0x9ea60]. let H := fresh "BR" in brfork H.
    + lwalk [0x9ea64; 0x9ea60].
      gen_zreg 11.
      remember (Z.lxor (bufs2 + (w - 1)) 3 - bufs2) as ix2 eqn:EIX2.
      unpark CSH. unpark SEP2. unpark SEP12.
      arr_sb bufs2 ix2 (Z.lxor (bufs2 + (w - 1)) 3).
      park_disj.
      apply evt_done. unfold d2l0_end. do 7 eexists.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
        lazymatch goal with UBx : u8arr asegs mm bufs1 ?b1, UCx : u8arr asegs mm bufs2 ?b2, ULx : u32arr asegs mm lined ?wlx, MUx : munch _ m0 mm, WMx : wmono asegs m0 mm |- _ =>
          exists mm, b1, b2, wlx;
          destruct (d2_tabs_u32 m0 mm _ _ _ _ _ _ _ _ _ _ _ _ GEO MUx WMx UT UTL U38 U38L U14 U14L) as (UTf & U38f & U14f)
        end end.
      split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
    + lwalk [0x9ea64; 0x9ea60].
      gen_zreg 11.
      remember (Z.lxor (bufs2 + (w - 1)) 3 - bufs2) as ix2 eqn:EIX2.
      unpark CSH. unpark SEP2. unpark SEP12.
      arr_sb bufs2 ix2 (Z.lxor (bufs2 + (w - 1)) 3).
      park_disj.
      apply evt_done. unfold d2l0_end. do 7 eexists.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
        lazymatch goal with UBx : u8arr asegs mm bufs1 ?b1, UCx : u8arr asegs mm bufs2 ?b2, ULx : u32arr asegs mm lined ?wlx, MUx : munch _ m0 mm, WMx : wmono asegs m0 mm |- _ =>
          exists mm, b1, b2, wlx;
          destruct (d2_tabs_u32 m0 mm _ _ _ _ _ _ _ _ _ _ _ _ GEO MUx WMx UT UTL U38 U38L U14 U14L) as (UTf & U38f & U14f)
        end end.
      split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
Qed.

(* [comment removed for export] *)
Definition d2l0_lend (sp gp tp s0 s1 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lined nl bufs1 bufs2 n1 ta t38 t14 : Z) (tw t38w t14w : list word) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s2' s5' t3' t4' t5' t6' : word) (m' : mem) (bs1' bs2' : list byte) (wl' : list word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' (Z_to_bv 64 bufs1)
                  s2' (Z_to_bv 64 30) (Z_to_bv 64 SHB) s5' CMASK MASK28 (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 bufs2) s11
                  t3' t4' t5' t6')
             F (Z_to_bv 64 0x9ea64) fc None m' (seg_rom asegs)
    /\ munch (D2L0_W lined nl bufs1 bufs2 n1) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' bufs1 bs1' /\ Z.of_nat (length bs1') = n1 /\ acc asegs m' bufs1 n1
    /\ u8arr asegs m' bufs2 bs2' /\ Z.of_nat (length bs2') = n1 /\ acc asegs m' bufs2 n1
    /\ u32arr asegs m' lined wl' /\ 4 * Z.of_nat (length wl') = nl /\ acc asegs m' lined nl
    /\ u32arr asegs m' ta tw /\ acc asegs m' ta 1024 /\ u32arr asegs m' t38 t38w /\ acc asegs m' t38 1024 /\ u32arr asegs m' t14 t14w /\ acc asegs m' t14 1024.

(* [comment removed for export] *)
Lemma d2l0_line : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a6 a7 s5 s9 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (sa lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (bs1 bs2 : list byte) (wl tw t38w t14w : list word),
  d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  u32arr asegs m ta tw -> Z.of_nat (length tw) = 256 -> acc asegs m ta 1024 ->
  u32arr asegs m t38 t38w -> Z.of_nat (length t38w) = 256 -> acc asegs m t38 1024 ->
  u32arr asegs m t14 t14w -> Z.of_nat (length t14w) = 256 -> acc asegs m t14 1024 ->
  rw_cells asegs m (sa + 56) [C8 (Z_to_bv 64 (w - 1))] -> rw_cells asegs m (sa + 64) [C8 (Z_to_bv 64 (w - 1))] ->
  rw_cells asegs m (sa + 72) [C8 (Z_to_bv 64 t38)] -> rw_cells asegs m (sa + 80) [C8 (Z_to_bv 64 w)] ->
  rw_cells asegs m (sa + 136) [C8 (Z_to_bv 64 bufs1)] -> rw_cells asegs m (sa + 152) [C8 (Z_to_bv 64 t14)] ->
  0 < sa -> sa + 160 <= 2^47 -> lined + nl <= sa -> bufs1 + n1 <= sa -> bufs2 + n1 <= sa ->
  evt asegs (d2l0_lend sp gp tp s0 (Z_to_bv 64 sa) s11 F fc m lined nl bufs1 bufs2 n1 ta t38 t14 tw t38w t14w)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 sa) a0 a1 a2 a3 a4 (Z_to_bv 64 lined) a6 a7
             (Z_to_bv 64 bufs1) (Z_to_bv 64 30) (Z_to_bv 64 SHB) s5 CMASK MASK28 (Z_to_bv 64 ta) s9 (Z_to_bv 64 bufs2) s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x9e6fc) fc None m (seg_rom asegs)).
Proof.
  intros until t14w. intros GEO MI UB UBL ACCB UC UCL ACCC UL ULL ACCL UT UTL ACCT U38 U38L ACC38 U14 U14L ACC14 C56 C64 C72 C80 C136 C152 SA0 SAHI LSA BSA CSA.
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & C0 & C8 & CHI & CSH & CSEG & L0 & LA4 & LNHI & LSH & LSEG
                   & TA0 & TA8 & TAHI & TASH & TASEG & T380 & T388 & T38HI & T38SH & T38SEG & T140 & T148 & T14HI & T14SH & T14SEG
                   & SEP1 & SEP2 & SEP12 & SEPT1 & SEPT2 & SEPT3 & SEP81 & SEP82 & SEP83 & SEP41 & SEP42 & SEP43).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (D2L0_W lined nl bufs1 bufs2 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  (* [comment removed for export] *)
  assert (FIN : forall (ra' t0' t1' t2' a0' a1' a3' a4' a6' a7' s2' s5' t3' t4' t5' t6' : word) (mc : mem) (bs1' bs2' : list byte) (wl' : list word),
    munch (D2L0_W lined nl bufs1 bufs2 n1) m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    u8arr asegs mc bufs1 bs1' -> Z.of_nat (length bs1') = n1 -> acc asegs mc bufs1 n1 ->
    u8arr asegs mc bufs2 bs2' -> Z.of_nat (length bs2') = n1 -> acc asegs mc bufs2 n1 ->
    u32arr asegs mc lined wl' -> 4 * Z.of_nat (length wl') = nl -> acc asegs mc lined nl ->
    acc asegs mc ta 1024 -> acc asegs mc t38 1024 -> acc asegs mc t14 1024 ->
    evt asegs (d2l0_lend sp gp tp s0 (Z_to_bv 64 sa) s11 F fc m lined nl bufs1 bufs2 n1 ta t38 t14 tw t38w t14w)
      (MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 sa) a0' a1' (Z_to_bv 64 (w - 1)) a3' a4' (Z_to_bv 64 lined) a6' a7'
               s2' (Z_to_bv 64 30) (Z_to_bv 64 2147450880) s5' (Z_to_bv 64 (-1073741824)) (Z_to_bv 64 268435455) (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 bufs2) s11
               t3' t4' t5' t6')
          F (Z_to_bv 64 0x9e974) fc None mc (seg_rom asegs))).
  { intros ra' t0' t1' t2' a0' a1' a3' a4' a6' a7' s2' s5' t3' t4' t5' t6' mc bs1' bs2' wl' MU1 WM1 MI1 UB1 UBL1 ACCB1 UC1 UCL1 ACCC1 UL1 ULL1 ACCL1 ACCT1 ACC381 ACC141.
    assert (C136' : rw_cells asegs mc (sa + 136) [Cells.C8 (Z_to_bv 64 bufs1)]).
    { eapply rw_cells_transport; [exact C136 | exact MU1 | exact WM1 |]. cbn. clear - LSA BSA CSA. lia. }
    eapply evt_cut.
    { eapply (d2l0_lastcol ra' sp gp tp t0' t1' t2' s0 a0' a1' a3' a4' a6' a7' s2' s5' s11 t3' t4' t5' t6' F fc m mc) with (bs1 := bs1') (bs2 := bs2') (wl := wl');
        try eassumption. }
    intros ms' PO. apply evt_done. unfold d2l0_end in PO. unfold d2l0_lend.
    destruct PO as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & m' & bs1'' & bs2'' & wl'' & E & R).
    exists ra', t0', t1', t2', b0, b1, b2, b3, b4, b5, b6, s2', s5', t3', t4', t5', t6', m', bs1'', bs2'', wl''.
    split; [exact E| exact R]. }
  lwalk [0x9e708; 0x9e964].
  destruct (Z.eq_dec w 1) as [W1|W2].
  - (* [comment removed for export] *)
    brT.
    lwalk [0x9e974].
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (w - 1)) by (f_equal; clear - W1; lia).
    eapply FIN; try eassumption.
  - (* [comment removed for export] *)
    brF.
    lwalk [0x9e724].
    eapply evt_cut.
    { eapply evt_eq.
      2:{ eapply (d2l0_pixels (Z.to_nat (w - 1)) 0) with (bs1 := bs1) (bs2 := bs2) (wl := wl) (n1 := n1) (nl := nl);
            try eassumption; clear - HW W2; lia. }
      replace (bufs1 + 0) with bufs1 by (clear; lia). replace (bufs2 + 0) with bufs2 by (clear; lia).
      replace (2 * 0) with 0 by (clear; lia). replace (w - 1 - 0) with (w - 1) by (clear; lia).
      reflexivity. }
    intros ms' PO. unfold d2l0_exit in PO.
    destruct PO as (ra' & a0' & a1' & a2' & a3' & a4' & s5' & t3' & t4' & t5' & t6' & m' & bs1' & bs2' & wl' & -> & MU' & WM' & MI'
                    & UB' & UBL' & ACCB' & UC' & UCL' & ACCC' & UL' & ULL' & ACCL' & UT' & ACCT' & U38' & ACC38' & U14' & ACC14').
    assert (C64' : rw_cells asegs m' (sa + 64) [Cells.C8 (Z_to_bv 64 (w - 1))]).
    { eapply rw_cells_transport; [exact C64 | exact MU' | exact WM' |]. cbn. clear - LSA BSA CSA. lia. }
    clear MI UB UBL ACCB UC UCL ACCC UL ULL ACCL ACCT ACC38 ACC14 MU WM C56 C64 C72 C80 C152.
    lwalk [0x9e974].
    eapply FIN; try eassumption.
Qed.
