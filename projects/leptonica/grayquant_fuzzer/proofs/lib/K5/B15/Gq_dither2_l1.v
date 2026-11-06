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
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation D2L1_W lined nl bufs1 n1 := [(lined, lined + nl); (bufs1, bufs1 + n1)]%Z (only parsing).
Notation ONE := (Z_to_bv 64 1) (only parsing).

(* [comment removed for export] *)
Definition d2_geom (lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) : Prop :=
  1 <= w <= 20000 /\ w <= n1 /\ n1 mod 4 = 0 /\ n1 <= 2^20 /\ w <= 4 * nl /\ nl mod 4 = 0 /\ 0 < nl <= 2^20
  /\ 0 < bufs1 /\ bufs1 mod 8 = 0 /\ bufs1 + n1 <= 2^47 /\ (bufs1 + n1 <= 0x7fff7000 \/ 0x10007fff8000 <= bufs1) /\ (bufs1 + n1 <= 0x10000 \/ SEGTOP_A <= bufs1)
  /\ 0 < bufs2 /\ bufs2 mod 8 = 0 /\ bufs2 + n1 <= 2^47 /\ (bufs2 + n1 <= 0x7fff7000 \/ 0x10007fff8000 <= bufs2) /\ (bufs2 + n1 <= 0x10000 \/ SEGTOP_A <= bufs2)
  /\ 0 < lined /\ lined mod 4 = 0 /\ lined + nl <= 2^47 /\ (lined + nl <= 0x7fff7000 \/ 0x10007fff8000 <= lined) /\ (lined + nl <= 0x10000 \/ SEGTOP_A <= lined)
  /\ 0 < ta /\ ta mod 8 = 0 /\ ta + 1024 <= 2^47 /\ (ta + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= ta) /\ (ta + 1024 <= 0x10000 \/ SEGTOP_A <= ta)
  /\ 0 < t38 /\ t38 mod 8 = 0 /\ t38 + 1024 <= 2^47 /\ (t38 + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= t38) /\ (t38 + 1024 <= 0x10000 \/ SEGTOP_A <= t38)
  /\ 0 < t14 /\ t14 mod 8 = 0 /\ t14 + 1024 <= 2^47 /\ (t14 + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= t14) /\ (t14 + 1024 <= 0x10000 \/ SEGTOP_A <= t14)
  /\ (bufs1 + n1 <= lined \/ lined + nl <= bufs1) /\ (bufs2 + n1 <= lined \/ lined + nl <= bufs2) /\ (bufs2 + n1 <= bufs1 \/ bufs1 + n1 <= bufs2)
  /\ (ta + 1024 <= lined \/ lined + nl <= ta) /\ (ta + 1024 <= bufs1 \/ bufs1 + n1 <= ta) /\ (ta + 1024 <= bufs2 \/ bufs2 + n1 <= ta)
  /\ (t38 + 1024 <= lined \/ lined + nl <= t38) /\ (t38 + 1024 <= bufs1 \/ bufs1 + n1 <= t38) /\ (t38 + 1024 <= bufs2 \/ bufs2 + n1 <= t38)
  /\ (t14 + 1024 <= lined \/ lined + nl <= t14) /\ (t14 + 1024 <= bufs1 \/ bufs1 + n1 <= t14) /\ (t14 + 1024 <= bufs2 \/ bufs2 + n1 <= t14).

(* [comment removed for export] *)
Definition tsmall (w : word) : Prop := bv_unsigned (sx32 w) <= 65535 \/ 2^64 - 65536 <= bv_unsigned (sx32 w).

(* [comment removed for export] *)
Definition d2l1_exit (ra sp gp tp a0 a2 a4 a5 a6 s11 t3 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lined nl bufs1 n1 ta t38 w : Z) (tw t38w : list word) : machine_state -> Prop :=
  fun ms' => exists (a1' a3' s6' s7' s8' s9' s10' : word) (m' : mem) (bs' : list byte) (wl' : list word),
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (bufs1 + 1 + (w - 1))) (Z_to_bv 64 3) (Z_to_bv 64 30) (Z_to_bv 64 2)
                  a0 a1' a2 a3' a4 a5 a6 (Z_to_bv 64 (2 * (w - 1)))
                  (Z_to_bv 64 268435455) ONE (Z_to_bv 64 (bufs1 + (w - 1))) (Z_to_bv 64 0) s6' s7' s8' s9' s10' s11
                  t3 ONE ONE (Z_to_bv 64 (-1073741824)))
             F (Z_to_bv 64 0xa38a8) fc None m' (seg_rom asegs)
    /\ munch (D2L1_W lined nl bufs1 n1) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' bufs1 bs' /\ Z.of_nat (length bs') = n1 /\ acc asegs m' bufs1 n1
    /\ u32arr asegs m' lined wl' /\ 4 * Z.of_nat (length wl') = nl /\ acc asegs m' lined nl
    /\ u32arr asegs m' ta tw /\ u32arr asegs m' t38 t38w.

Lemma d2l1_pixels : forall (k : nat) (j : Z)
    (ra sp gp tp a1 a3 s6 s7 s8 s9 s10 s11 : word) F fc (m : mem)
    (lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (bs : list byte) (wl tw t38w : list word),
  Z.of_nat k = w - 1 - j -> 0 <= j -> (1 <= k)%nat -> d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  mem_inv asegs m -> u8arr asegs m bufs1 bs -> Z.of_nat (length bs) = n1 -> acc asegs m bufs1 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  u32arr asegs m ta tw -> Z.of_nat (length tw) = 256 -> acc asegs m ta 1024 ->
  u32arr asegs m t38 t38w -> Z.of_nat (length t38w) = 256 -> acc asegs m t38 1024 -> Forall tsmall t38w ->
  evt asegs (d2l1_exit ra sp gp tp (Z_to_bv 64 lined) (Z_to_bv 64 bufs1) (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 (w - 1)) s11 (Z_to_bv 64 SHB) F fc m lined nl bufs1 n1 ta t38 w tw t38w)
    (MS (mkR ra sp gp tp (Z_to_bv 64 j) (Z_to_bv 64 (bufs1 + 1 + j)) (Z_to_bv 64 3) (Z_to_bv 64 30) (Z_to_bv 64 2)
             (Z_to_bv 64 lined) a1 (Z_to_bv 64 bufs1) a3 (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (2 * j))
             (Z_to_bv 64 268435455) ONE (Z_to_bv 64 (bufs1 + j)) (Z_to_bv 64 (w - 1 - j)) s6 s7 s8 s9 s10 s11
             (Z_to_bv 64 SHB) ONE ONE (Z_to_bv 64 (-1073741824)))
        F (Z_to_bv 64 0xa36cc) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp a1 a3 s6 s7 s8 s9 s10 s11 F fc m lined nl bufs1 bufs2 n1 ta t38 t14 w bs wl tw t38w
    HK HJ HK1 GEO MI UB UBL ACCB UL ULL ACCL UT UTL ACCT U38 U38L ACC38 T38S.
  { lia. }
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & C0 & C8 & CHI & CSH & CSEG & L0 & LA4 & LNHI & LSH & LSEG
                   & TA0 & TA8 & TAHI & TASH & TASEG & T380 & T388 & T38HI & T38SH & T38SEG & T140 & T148 & T14HI & T14SH & T14SEG
                   & SEP1 & SEP2 & SEP12 & SEPT1 & SEPT2 & SEPT3 & SEP81 & SEP82 & SEP83 & SEP41 & SEP42 & SEP43).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (D2L1_W lined nl bufs1 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  (* [comment removed for export] *)
  assert (CONT : forall (a1' a3' s6' s7' s8' s9' s10' : word) (mm : mem) (bs' : list byte) (wl' : list word),
    munch (D2L1_W lined nl bufs1 n1) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    u8arr asegs mm bufs1 bs' -> Z.of_nat (length bs') = n1 -> acc asegs mm bufs1 n1 ->
    u32arr asegs mm lined wl' -> 4 * Z.of_nat (length wl') = nl -> acc asegs mm lined nl ->
    u32arr asegs mm ta tw -> acc asegs mm ta 1024 -> u32arr asegs mm t38 t38w -> acc asegs mm t38 1024 ->
    evt asegs (d2l1_exit ra sp gp tp (Z_to_bv 64 lined) (Z_to_bv 64 bufs1) (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 (w - 1)) s11 (Z_to_bv 64 2147450880) F fc m lined nl bufs1 n1 ta t38 w tw t38w)
      (MS (mkR ra sp gp tp (Z_to_bv 64 j) (Z_to_bv 64 (bufs1 + 1 + j)) (Z_to_bv 64 3) (Z_to_bv 64 30) (Z_to_bv 64 2)
             (Z_to_bv 64 lined) a1' (Z_to_bv 64 bufs1) a3' (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (2 * j))
             (Z_to_bv 64 268435455) ONE (Z_to_bv 64 (bufs1 + j)) (Z_to_bv 64 (w - 1 - j)) s6' s7' s8' s9' s10' s11
             (Z_to_bv 64 2147450880) ONE ONE (Z_to_bv 64 (-1073741824)))
          F (Z_to_bv 64 0xa3824) fc None mm (seg_rom asegs))).
  { intros a1' a3' s6' s7' s8' s9' s10' mm bs' wl' MU1 WM1 MI1 UB1 UBL1 ACCB1 UL1 ULL1 ACCL1 UT1 ACCT1 U381 ACC381.
    clear MI UB UBL ACCB UL ULL ACCL MU WM UT ACCT U38 ACC38.
    lwalk [0xa36cc; 0xa38a8; 0xa3eac].
    replace (bufs1 + 1 + j + 1) with (bufs1 + 1 + (j + 1)) by lia. replace (2 * j + 2) with (2 * (j + 1)) by lia.
    replace (bufs1 + j + 1) with (bufs1 + (j + 1)) by lia. replace (w - 1 - j + -1) with (w - 1 - (j + 1)) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w - 1) by lia. rewrite EJ in *. replace (w - 1 - (w - 1)) with 0 by lia.
      brF. lwalk [0xa36cc; 0xa38a8; 0xa3eac].
      apply evt_done. unfold d2l1_exit, SHB. do 7 eexists. exists mm, bs', wl'. split; [reflexivity|].
      repeat (split; [assumption|]). assumption.
    - brT.
      eapply evt_cut.
      + eapply (IH (j + 1)) with (bs := bs') (wl := wl') (w := w) (n1 := n1) (nl := nl) (bufs2 := bufs2) (t14 := t14); try eassumption; try lia.
      + intros ms' PO. apply evt_done. unfold d2l1_exit in PO |- *.
        destruct PO as (a1'' & a3'' & s6'' & s7'' & s8'' & s9'' & s10'' & m' & bs'' & wl'' & E & MU' & WM' & R).
        exists a1'', a3'', s6'', s7'', s8'', s9'', s10'', m', bs'', wl''.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R]. }
  (* [comment removed for export] *)
  pose proof (lxor3_eq (bufs1 + 1 + j)) as LX1.
  assert (IDX1 : 0 <= Z.lxor (bufs1 + 1 + j) 3 - bufs1 < n1) by (rewrite LX1; clear - HJ HK HW WN N4 B8; Z.div_mod_to_equations; lia).
  assert (STORE : forall (z3 : Z) (s6' s8' s9' s10' : word) (mm : mem) (bs' : list byte) (wl' : list word),
    munch (D2L1_W lined nl bufs1 n1) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    u8arr asegs mm bufs1 bs' -> Z.of_nat (length bs') = n1 -> acc asegs mm bufs1 n1 ->
    u32arr asegs mm lined wl' -> 4 * Z.of_nat (length wl') = nl -> acc asegs mm lined nl ->
    u32arr asegs mm ta tw -> acc asegs mm ta 1024 -> u32arr asegs mm t38 t38w -> acc asegs mm t38 1024 ->
    evt asegs (d2l1_exit ra sp gp tp (Z_to_bv 64 lined) (Z_to_bv 64 bufs1) (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 (w - 1)) s11 (Z_to_bv 64 2147450880) F fc m lined nl bufs1 n1 ta t38 w tw t38w)
      (MS (mkR ra sp gp tp (Z_to_bv 64 j) (Z_to_bv 64 (bufs1 + 1 + j)) (Z_to_bv 64 3) (Z_to_bv 64 30) (Z_to_bv 64 2)
             (Z_to_bv 64 lined) (Z_to_bv 64 (Z.lxor (bufs1 + 1 + j) 3)) (Z_to_bv 64 bufs1) (Z_to_bv 64 z3) (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (2 * j))
             (Z_to_bv 64 268435455) ONE (Z_to_bv 64 (bufs1 + j)) (Z_to_bv 64 (w - 1 - j)) s6' (Z_to_bv 64 (Z.lxor (bufs1 + 1 + j) 3 / 8 + 2147450880)) s8' s9' s10' s11
             (Z_to_bv 64 2147450880) ONE ONE (Z_to_bv 64 (-1073741824)))
          F (Z_to_bv 64 0xa3818) fc None mm (seg_rom asegs))).
  { intros z3 s6' s8' s9' s10' mm bs' wl' MU1 WM1 MI1 UB1 UBL1 ACCB1 UL1 ULL1 ACCL1 UT1 ACCT1 U381 ACC381.
    clear MI UB UBL ACCB UL ULL ACCL MU WM UT ACCT U38 ACC38.
    lwalk [0xa3820; 0xa3eac].
    remember (Z.lxor (bufs1 + 1 + j) 3 - bufs1) as ix eqn:EIX.   (* [comment removed for export] *)
    unpark SEP1. unpark SEPT2. unpark SEP82. unpark BSH.
    arr_sb bufs1 ix (Z.lxor (bufs1 + 1 + j) 3).
    park SEP1. park SEPT2. park SEP82. park BSH.
    eapply CONT; eassumption. }
  (* [comment removed for export] *)
  replace (Z.land (j / 16) 268435455) with (j / 16)
    by (change 268435455 with (Z.ones 28); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; clear - HJ HK HW; Z.div_mod_to_equations; lia) || idtac.
  lwalk [0xa38a8; 0xa3eac].
  replace (Z.land (j / 16) 268435455) with (j / 16)
    by (change 268435455 with (Z.ones 28); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; clear - HJ HK HW; Z.div_mod_to_equations; lia).
  replace (lined + j / 16 * 4) with (lined + 4 * (j / 16)) by (clear; lia).
  assert (ULW : Z.of_nat (length wl) = nl / 4) by (clear - ULL L4; Z.div_mod_to_equations; lia).
  assert (JL : 0 <= j / 16 < nl / 4) by (clear - HJ HK HW WL L4; Z.div_mod_to_equations; lia).
  lwalk [0xa38a8; 0xa3eac].
  replace (bufs1 + 1 + j + -1) with (bufs1 + j) by lia.
  pose proof (lxor3_eq (bufs1 + j)) as LX0.
  assert (IDX0 : 0 <= Z.lxor (bufs1 + j) 3 - bufs1 < n1) by (rewrite LX0; clear - HJ HK HW WN N4 B8; Z.div_mod_to_equations; lia).
  destruct UB as [HB WB].
  destruct (bytes_at_read1 m bufs1 bs (Z.lxor (bufs1 + j) 3 - bufs1) HB ltac:(lia)) as (ov & R).
  replace (bufs1 + (Z.lxor (bufs1 + j) 3 - bufs1)) with (Z.lxor (bufs1 + j) 3) in R by lia.
  lstep. clear R.
  assert (UB : u8arr asegs m bufs1 bs) by (split; assumption).
  clear HB WB.
  (* [comment removed for export] *)
  pose proof (bv_unsigned_in_range 8 ov) as OVR. unfold bv_modulus in OVR. change (2 ^ Z.of_N 8) with 256 in OVR.
  set (oz := bv_unsigned ov) in *.
  lwalk [0xa38a8; 0xa3eac].
  replace (ta + oz * 4) with (ta + 4 * oz) by (clear; lia).
  lwalk [0xa38a8; 0xa3eac].
  (* [comment removed for export] *)
  destruct (u32arr_nth wl (j / 16) ltac:(lia)) as (dv & NTHD).
  pose proof (u32arr_read asegs m lined wl (j / 16) dv _ UL NTHD ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0xa38a8; 0xa3eac].
  destruct (u32arr_nth tw oz ltac:(lia)) as (tv & NTHT).
  pose proof (u32arr_read asegs m ta tw oz tv _ UT NTHT ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0xa38a8; 0xa3eac].
  (* [comment removed for export] *)
  clear ULL.
  unpark SEP1. unpark SEPT1. unpark SEP81. unpark LSH.
  arr_sw lined (j / 16) (lined + 4 * (j / 16)).
  park SEP1. park SEPT1. park SEP81. park LSH.
  lazymatch goal with H : Z.of_nat (length ?ws) = nl / 4 |- _ => assert (ULL : 4 * Z.of_nat (length ws) = nl) by (rewrite H; clear - L4; Z.div_mod_to_equations; lia) end.
  (* [comment removed for export] *)
  lwalk [0xa38a8; 0xa3eac].
  lazymatch goal with UBx : u8arr asegs ?mm bufs1 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof UBx as [HB WB];
    destruct (bytes_at_read1 mm bufs1 bsx (Z.lxor (bufs1 + 1 + j) 3 - bufs1) HB ltac:(lia)) as (rv & R) end.
  replace (bufs1 + (Z.lxor (bufs1 + 1 + j) 3 - bufs1)) with (Z.lxor (bufs1 + 1 + j) 3) in R by lia.
  lstep. clear R HB WB.
  replace (t38 + oz * 4) with (t38 + 4 * oz) by (clear; lia).
  lwalk [0xa38a8; 0xa3eac].
  destruct (u32arr_nth t38w oz ltac:(lia)) as (pv & NTHP).
  lazymatch goal with U : u32arr asegs ?mm t38 t38w |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read asegs mm t38 t38w oz pv _ U NTHP ltac:(lia) eq_refl) as R end.
  lstep. clear R.
  pose proof (proj1 (Forall_forall tsmall t38w) T38S pv (nth_error_In _ _ NTHP)) as PVS. unfold tsmall in PVS.
  pose proof (bv_unsigned_in_range 8 rv) as RVR. unfold bv_modulus in RVR. change (2 ^ Z.of_N 8) with 256 in RVR.
  lwalk [0xa38a8; 0xa3eac; 0xa3818].
  (* [comment removed for export] *)
  brfork SG.
  - (* [comment removed for export] *)
    lwalk [0xa38a8; 0xa3eac; 0xa3818].
    eapply STORE; eassumption.
  - (* [comment removed for export] *)
    lwalk [0xa38a8; 0xa3eac; 0xa3818].
    pose proof (bv_unsigned_in_range 64 (sx32 pv)) as PVR. unfold bv_modulus in PVR. change (2 ^ Z.of_N 64) with (2^64) in PVR.
    rewrite (bv_swrap_small 32 (bv_unsigned rv + bv_unsigned (sx32 pv))) by (change (bv_half_modulus 32) with (2^31); clear - PVS SG RVR PVR; lia).
    lwalk [0xa38a8; 0xa3eac; 0xa3818].
    brfork MX.
    + eapply STORE; eassumption.
    + lwalk [0xa38a8; 0xa3eac; 0xa3818].
      eapply STORE; eassumption.
Qed.

(* [comment removed for export] *)
Definition d2l_end (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (W : list (Z * Z)) (lined nl bufs1 bufs2 n1 : Z) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
                    (m' : mem) (bs1' bs2' : list byte) (wl' : list word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
             F (Z_to_bv 64 0xa3e70) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' bufs1 bs1' /\ Z.of_nat (length bs1') = n1 /\ acc asegs m' bufs1 n1
    /\ u8arr asegs m' bufs2 bs2' /\ Z.of_nat (length bs2') = n1 /\ acc asegs m' bufs2 n1
    /\ u32arr asegs m' lined wl' /\ 4 * Z.of_nat (length wl') = nl /\ acc asegs m' lined nl.

(* [comment removed for export] *)
Lemma d2l1_last : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) F fc (m : mem)
    (lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (bs bs2 : list byte) (wl tw : list word),
  d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  mem_inv asegs m -> u8arr asegs m bufs1 bs -> Z.of_nat (length bs) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  u32arr asegs m ta tw -> Z.of_nat (length tw) = 256 -> acc asegs m ta 1024 ->
  evt asegs (d2l_end sp gp tp F fc m (D2L1_W lined nl bufs1 n1) lined nl bufs1 bufs2 n1)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 lined) a1 (Z_to_bv 64 bufs1) a3 (Z_to_bv 64 ta) a5 (Z_to_bv 64 (w - 1)) a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SHB) t4 t5 t6)
        F (Z_to_bv 64 0xa38a8) fc None m (seg_rom asegs)).
Proof.
  intros until tw. intros GEO MI UB UBL ACCB UB2 UBL2 ACCB2 UL ULL ACCL UT UTL ACCT.
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & C0 & C8 & CHI & CSH & CSEG & L0 & LA4 & LNHI & LSH & LSEG
                   & TA0 & TA8 & TAHI & TASH & TASEG & T380 & T388 & T38HI & T38SH & T38SEG & T140 & T148 & T14HI & T14SH & T14SEG
                   & SEP1 & SEP2 & SEP12 & SEPT1 & SEPT2 & SEPT3 & SEP81 & SEP82 & SEP83 & SEP41 & SEP42 & SEP43).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (D2L1_W lined nl bufs1 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  pose proof (lxor3_eq (bufs1 + (w - 1))) as LX0.
  assert (IDX0 : 0 <= Z.lxor (bufs1 + (w - 1)) 3 - bufs1 < n1) by (rewrite LX0; clear - HW WN N4 B8; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  lwalk [0xa3908; 0xa3e70; 0xa3eac].
  rewrite (srliw_idx (w - 1) 16) by (clear - HW; lia).
  replace (lined + (w - 1) / 16 * 4) with (lined + 4 * ((w - 1) / 16)) by (clear; lia).
  assert (ULW : Z.of_nat (length wl) = nl / 4) by (clear - ULL L4; Z.div_mod_to_equations; lia).
  assert (JL : 0 <= (w - 1) / 16 < nl / 4) by (clear - HW WL L4; Z.div_mod_to_equations; lia).
  lwalk [0xa3908; 0xa3e70; 0xa3eac].
  destruct UB as [HB WB].
  destruct (bytes_at_read1 m bufs1 bs (Z.lxor (bufs1 + (w - 1)) 3 - bufs1) HB ltac:(lia)) as (ov & R).
  replace (bufs1 + (Z.lxor (bufs1 + (w - 1)) 3 - bufs1)) with (Z.lxor (bufs1 + (w - 1)) 3) in R by lia.
  lstep. clear R.
  assert (UB : u8arr asegs m bufs1 bs) by (split; assumption).
  clear HB WB.
  pose proof (bv_unsigned_in_range 8 ov) as OVR. unfold bv_modulus in OVR. change (2 ^ Z.of_N 8) with 256 in OVR.
  set (oz := bv_unsigned ov) in *.
  lwalk [0xa3e70; 0xa3eac].
  replace (ta + bv_unsigned ov * 4) with (ta + 4 * oz) by (subst oz; clear; lia).
  destruct (u32arr_nth wl ((w - 1) / 16) ltac:(lia)) as (dv & NTHD).
  pose proof (u32arr_read asegs m lined wl ((w - 1) / 16) dv _ UL NTHD ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0xa3e70; 0xa3eac].
  destruct (u32arr_nth tw oz ltac:(lia)) as (tv & NTHT).
  pose proof (u32arr_read asegs m ta tw oz tv _ UT NTHT ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0xa3e70; 0xa3eac; 0xa3984].
  clear ULL.
  unpark SEP1. unpark SEP2. unpark SEPT1. unpark LSH.
  arr_sw lined ((w - 1) / 16) (lined + 4 * ((w - 1) / 16)).
  park SEP1. park SEP2. park SEPT1. park LSH.
  lazymatch goal with H : Z.of_nat (length ?ws) = nl / 4 |- _ => assert (ULL : 4 * Z.of_nat (length ws) = nl) by (rewrite H; clear - L4; Z.div_mod_to_equations; lia) end.
  lwalk [0xa3e70; 0xa3eac].
  apply evt_done. unfold d2l_end. do 28 eexists.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
    lazymatch goal with UBx : u8arr asegs mm bufs1 ?bsx, UB2x : u8arr asegs mm bufs2 ?bs2x, ULx : u32arr asegs mm lined ?wlx |- _ => exists mm, bsx, bs2x, wlx end end.
  split; [reflexivity|].
  repeat (split; [assumption|]). assumption.
Qed.
