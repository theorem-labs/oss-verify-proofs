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
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.



Notation DL1_W lined nl bufs1 n1 := [(lined, lined + nl); (bufs1, bufs1 + n1)]%Z (only parsing).

(* [comment removed for export] *)
Definition dl_geom (lined nl bufs1 n1 w : Z) : Prop :=
  1 <= w <= 20000 /\ w <= n1 /\ n1 mod 4 = 0 /\ n1 <= 2^20 /\ w <= 8 * nl /\ nl mod 4 = 0 /\ 0 < nl <= 2^20
  /\ 0 < bufs1 /\ bufs1 mod 8 = 0 /\ bufs1 + n1 <= 2^47 /\ (bufs1 + n1 <= 0x7fff7000 \/ 0x10007fff8000 <= bufs1) /\ (bufs1 + n1 <= 0x10000 \/ SEGTOP_A <= bufs1)
  /\ 0 < lined /\ lined mod 4 = 0 /\ lined + nl <= 2^47 /\ (lined + nl <= 0x7fff7000 \/ 0x10007fff8000 <= lined) /\ (lined + nl <= 0x10000 \/ SEGTOP_A <= lined)
  /\ (bufs1 + n1 <= lined \/ lined + nl <= bufs1).

Definition dl1_exit (ra sp gp tp s0r s1 a0 a2 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (t0 t1 t2 t3 t4 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lined nl bufs1 n1 w : Z) : machine_state -> Prop :=
  fun ms' => exists (a1' t5' t6' s0' : word) (m' : mem) (bs' : list byte) (wl' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' s1 a0 a1' a2 (Z_to_bv 64 (w - 1)) a4 a5 (Z_to_bv 64 (w - 1)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5' t6')
             F (Z_to_bv 64 0x9d31c) fc None m' (seg_rom asegs)
    /\ munch (DL1_W lined nl bufs1 n1) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' bufs1 bs' /\ Z.of_nat (length bs') = n1 /\ acc asegs m' bufs1 n1
    /\ u32arr asegs m' lined wl' /\ 4 * Z.of_nat (length wl') = nl /\ acc asegs m' lined nl.


Lemma dl1_pixels : forall (k : nat) (j : Z)
    (ra sp gp tp s0 s1 a1 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t5 t6 : word) F fc (m : mem)
    (lined nl bufs1 n1 w : Z) (bs : list byte) (wl : list word),
  Z.of_nat k = w - 1 - j -> 0 <= j -> (1 <= k)%nat -> dl_geom lined nl bufs1 n1 w ->
  mem_inv asegs m -> u8arr asegs m bufs1 bs -> Z.of_nat (length bs) = n1 -> acc asegs m bufs1 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  evt asegs (dl1_exit ra sp gp tp s0 s1 (Z_to_bv 64 lined) (Z_to_bv 64 bufs1) a4 a5 (Z_to_bv 64 SHB) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t0 (Z_to_bv 64 (bufs1 + 1)) (Z_to_bv 64 134217727) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (-2147483648)) F fc m lined nl bufs1 n1 w)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 (bufs1 + 1)) (Z_to_bv 64 134217727) s0 s1 (Z_to_bv 64 lined) a1 (Z_to_bv 64 bufs1) (Z_to_bv 64 j) a4 a5 (Z_to_bv 64 j)
             (Z_to_bv 64 SHB) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (-2147483648)) t5 t6)
        F (Z_to_bv 64 0x9cf48) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp s0 s1 a1 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t5 t6 F fc m lined nl bufs1 n1 w bs wl
    HK HJ HK1 GEO MI UB UBL ACCB UL ULL ACCL.
  { lia. }
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & L0 & LA4 & LNHI & LSH & LSEG & SEP).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (DL1_W lined nl bufs1 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  assert (CONT : forall (a1' t5' t6' s0' : word) (mm : mem) (bs' : list byte) (wl' : list word),
    munch (DL1_W lined nl bufs1 n1) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    u8arr asegs mm bufs1 bs' -> Z.of_nat (length bs') = n1 -> acc asegs mm bufs1 n1 ->
    u32arr asegs mm lined wl' -> 4 * Z.of_nat (length wl') = nl -> acc asegs mm lined nl ->
    evt asegs (dl1_exit ra sp gp tp s0 s1 (Z_to_bv 64 lined) (Z_to_bv 64 bufs1) a4 a5 (Z_to_bv 64 2147450880) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t0 (Z_to_bv 64 (bufs1 + 1)) (Z_to_bv 64 134217727) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (-2147483648)) F fc m lined nl bufs1 n1 w)
      (MS (mkR ra sp gp tp t0 (Z_to_bv 64 (bufs1 + 1)) (Z_to_bv 64 134217727) s0' s1 (Z_to_bv 64 lined) a1' (Z_to_bv 64 bufs1) (Z_to_bv 64 j) a4 a5 (Z_to_bv 64 j)
             (Z_to_bv 64 2147450880) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (-2147483648)) t5' t6')
          F (Z_to_bv 64 0x9cf3c) fc None mm (seg_rom asegs))).
  { intros a1' t5' t6' s0' mm bs' wl' MU1 WM1 MI1 UB1 UBL1 ACCB1 UL1 ULL1 ACCL1.
    clear MI UB UBL ACCB UL ULL ACCL MU WM.
    lwalk [0x9cf48; 0x9d31c].
    destruct k as [|k].
    - assert (EJ : j + 1 = w - 1) by lia. rewrite EJ in *.
      brT. apply evt_done. unfold dl1_exit, SHB. do 4 eexists. exists mm, bs', wl'. split; [reflexivity|].
      repeat (split; [assumption|]). assumption.
    - brF.
      eapply evt_cut.
      + eapply (IH (j + 1)) with (bs := bs') (wl := wl') (w := w) (n1 := n1) (nl := nl); try eassumption; try lia.
      + intros ms' PO. apply evt_done. unfold dl1_exit in PO |- *.
        destruct PO as (a1'' & t5'' & t6'' & s0'' & m' & bs'' & wl'' & E & MU' & WM' & R).
        exists a1'', t5'', t6'', s0'', m', bs'', wl''.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R]. }
  (* [comment removed for export] *)
  pose proof (lxor3_eq (bufs1 + 1 + j)) as LX1.
  assert (STORE : forall (z5 : Z) (t6' s0' : word) (mm : mem) (bs' : list byte) (wl' : list word),
    munch (DL1_W lined nl bufs1 n1) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    u8arr asegs mm bufs1 bs' -> Z.of_nat (length bs') = n1 -> acc asegs mm bufs1 n1 ->
    u32arr asegs mm lined wl' -> 4 * Z.of_nat (length wl') = nl -> acc asegs mm lined nl ->
    evt asegs (dl1_exit ra sp gp tp s0 s1 (Z_to_bv 64 lined) (Z_to_bv 64 bufs1) a4 a5 (Z_to_bv 64 2147450880) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t0 (Z_to_bv 64 (bufs1 + 1)) (Z_to_bv 64 134217727) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (-2147483648)) F fc m lined nl bufs1 n1 w)
      (MS (mkR ra sp gp tp t0 (Z_to_bv 64 (bufs1 + 1)) (Z_to_bv 64 134217727) s0' s1 (Z_to_bv 64 lined) (Z_to_bv 64 (Z.lxor (bufs1 + 1 + j) 3)) (Z_to_bv 64 bufs1) (Z_to_bv 64 j) a4 a5 (Z_to_bv 64 j)
             (Z_to_bv 64 2147450880) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (-2147483648)) (Z_to_bv 64 z5) t6')
          F (Z_to_bv 64 0x9cf28) fc None mm (seg_rom asegs))).
  { intros z5 t6' s0' mm bs' wl' MU1 WM1 MI1 UB1 UBL1 ACCB1 UL1 ULL1 ACCL1.
    clear MI UB UBL ACCB UL ULL ACCL MU WM.
    lwalk [0x9cf38; 0x9d510].
    assert (IDX1 : 0 <= Z.lxor (bufs1 + 1 + j) 3 - bufs1 < n1) by (rewrite LX1; clear - HJ HK HW WN N4 B8; Z.div_mod_to_equations; lia).
    remember (Z.lxor (bufs1 + 1 + j) 3 - bufs1) as ix eqn:EIX.   (* [comment removed for export] *)
    arr_sb bufs1 ix (Z.lxor (bufs1 + 1 + j) 3).
    eapply CONT; eassumption. }
  (* [comment removed for export] *)
  pose proof (lxor3_eq (bufs1 + j)) as LX0.
  assert (IDX0 : 0 <= Z.lxor (bufs1 + j) 3 - bufs1 < n1) by (rewrite LX0; clear - HJ HK HW WN N4 B8; Z.div_mod_to_equations; lia).
  lwalk [0x9cf60; 0x9d500].
  destruct UB as [HB WB].
  destruct (bytes_at_read1 m bufs1 bs (Z.lxor (bufs1 + j) 3 - bufs1) HB ltac:(lia)) as (bv & R).
  replace (bufs1 + (Z.lxor (bufs1 + j) 3 - bufs1)) with (Z.lxor (bufs1 + j) 3) in R by lia.
  lstep. clear R.
  assert (UB : u8arr asegs m bufs1 bs) by (split; assumption).
  clear HB WB.
  lwalk [0x9cfdc; 0x9cf6c].
  brfork SG.
  - (* [comment removed for export] *)
    lwalk [0x9cf3c; 0x9cf08; 0x9d4f8].
    brfork CL1; [solve [eapply CONT; eassumption]|].
    lwalk [0x9cf3c; 0x9cf08; 0x9d4f8].
    (* [comment removed for export] *)
    lazymatch goal with K : shk ?mm ?b ?X |- _ =>
      assert (KY : shk mm b (Z.lxor X 3))
        by (unfold shk, shad in *; replace (Z.lxor X 3 / 8) with (X / 8) by (pose proof (lxor3_eq X) as LXx; rewrite LXx; clear; Z.div_mod_to_equations; lia); exact K);
      clear K end.
    assert (IDX1 : 0 <= Z.lxor (bufs1 + 1 + j) 3 - bufs1 < n1) by (rewrite LX1; clear - HJ HK HW WN N4 B8; Z.div_mod_to_equations; lia).
    shbr_inv.
    destruct UB as [HB WB].
    destruct (bytes_at_read1 m bufs1 bs (Z.lxor (bufs1 + 1 + j) 3 - bufs1) HB ltac:(lia)) as (rv & R).
    replace (bufs1 + (Z.lxor (bufs1 + 1 + j) 3 - bufs1)) with (Z.lxor (bufs1 + 1 + j) 3) in R by lia.
    lstep. clear R.
    assert (UB : u8arr asegs m bufs1 bs) by (split; assumption).
    clear HB WB.
    lwalk [0x9cf28].
    eapply STORE; eassumption.
  - (* [comment removed for export] *)
    lwalk [0x9cf8c; 0x9d508].
    replace (Z.land (j / 32) 134217727) with (j / 32)
      by (change 134217727 with (Z.ones 27); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; clear - HJ HK HW; Z.div_mod_to_equations; lia).
    replace (lined + j / 32 * 4) with (lined + 4 * (j / 32)) by (clear; lia).
    assert (ULW : Z.of_nat (length wl) = nl / 4) by (clear - ULL L4; Z.div_mod_to_equations; lia).
    assert (JL : 0 <= j / 32 < nl / 4) by (clear - HJ HK HW WL L4; Z.div_mod_to_equations; lia).
    lwalk [0x9cf8c; 0x9d508].
    destruct (u32arr_nth wl (j / 32) ltac:(lia)) as (dv & NTHD).
    pose proof (u32arr_read asegs m lined wl (j / 32) dv _ UL NTHD ltac:(lia) eq_refl) as R.
    lstep. clear R.
    lwalk [0x9cf98].
    clear ULL.
    arr_sw lined (j / 32) (lined + 4 * (j / 32)).
    lazymatch goal with H : Z.of_nat (length ?ws) = nl / 4 |- _ => assert (ULL : 4 * Z.of_nat (length ws) = nl) by (rewrite H; clear - L4; Z.div_mod_to_equations; lia) end.
    lwalk [0x9cf3c; 0x9cfb8; 0x9d038].
    brfork CL2; [solve [eapply CONT; eassumption]|].
    (* [comment removed for export] *)
    assert (IDX1 : 0 <= Z.lxor (bufs1 + 1 + j) 3 - bufs1 < n1) by (rewrite LX1; clear - HJ HK HW WN N4 B8; Z.div_mod_to_equations; lia).
    lwalk [0x9cfb8; 0x9d038].
    lazymatch goal with UBx : u8arr asegs ?mm bufs1 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof UBx as [HB WB];
      destruct (bytes_at_read1 mm bufs1 bsx (Z.lxor (bufs1 + 1 + j) 3 - bufs1) HB ltac:(lia)) as (rv & R) end.
    replace (bufs1 + (Z.lxor (bufs1 + 1 + j) 3 - bufs1)) with (Z.lxor (bufs1 + 1 + j) 3) in R by lia.
    lstep. clear R HB WB.
    lwalk [0x9cf28; 0x9cfd4].
    brfork MX.
    + eapply STORE; eassumption.
    + lwalk [0x9cf28].
      eapply STORE; eassumption.
Qed.

(* [comment removed for export] *)
Definition dl1_end (ra sp gp tp t0 t1 t2 s1 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lined nl bufs1 n1 : Z) : machine_state -> Prop :=
  fun ms' => exists (s0' a0' a1' a2' a3' a5' : word) (m' : mem) (bs' : list byte) (wl' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' s1 a0' a1' a2' a3' a4 a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9d474) fc None m' (seg_rom asegs)
    /\ munch (DL1_W lined nl bufs1 n1) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' bufs1 bs' /\ Z.of_nat (length bs') = n1 /\ acc asegs m' bufs1 n1
    /\ u32arr asegs m' lined wl' /\ 4 * Z.of_nat (length wl') = nl /\ acc asegs m' lined nl.

(* [comment removed for export] *)
Lemma dl1_last : forall (ra sp gp tp t1 t2 s0 s1 a1 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (lined nl bufs1 n1 w : Z) (bs : list byte) (wl : list word),
  dl_geom lined nl bufs1 n1 w ->
  mem_inv asegs m -> u8arr asegs m bufs1 bs -> Z.of_nat (length bs) = n1 -> acc asegs m bufs1 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  evt asegs (dl1_end ra sp gp tp (Z_to_bv 64 (w - 1)) t1 t2 s1 a4 a6 (Z_to_bv 64 SHB) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lined nl bufs1 n1)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (w - 1)) t1 t2 s0 s1 (Z_to_bv 64 lined) a1 (Z_to_bv 64 bufs1) a3 a4 a5 a6
             (Z_to_bv 64 SHB) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9d31c) fc None m (seg_rom asegs)).
Proof.
  intros until wl. intros GEO MI UB UBL ACCB UL ULL ACCL.
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & L0 & LA4 & LNHI & LSH & LSEG & SEP).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (DL1_W lined nl bufs1 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (lxor3_eq (bufs1 + (w - 1))) as LX0.
  assert (IDX0 : 0 <= Z.lxor (bufs1 + (w - 1)) 3 - bufs1 < n1) by (rewrite LX0; clear - HW WN N4 B8; Z.div_mod_to_equations; lia).
  lwalk [0x9d334; 0x9d49c].
  destruct UB as [HB WB].
  destruct (bytes_at_read1 m bufs1 bs (Z.lxor (bufs1 + (w - 1)) 3 - bufs1) HB ltac:(lia)) as (bv & R).
  replace (bufs1 + (Z.lxor (bufs1 + (w - 1)) 3 - bufs1)) with (Z.lxor (bufs1 + (w - 1)) 3) in R by lia.
  lstep. clear R.
  assert (UB : u8arr asegs m bufs1 bs) by (split; assumption).
  clear HB WB.
  lwalk [0x9d33c; 0x9d474].
  brfork SG.
  - (* [comment removed for export] *)
    apply evt_done. unfold dl1_end. do 6 eexists. exists m, bs, wl. split; [reflexivity|].
    repeat (split; [assumption|]). assumption.
  - (* [comment removed for export] *)
    do 3 lstep.
    replace (bv_wrap 32 (w - 1)) with (w - 1) by (unfold bv_wrap, bv_modulus; symmetry; apply Z.mod_small; clear - HW; lia).
    rewrite (Z.shiftr_div_pow2 (w - 1) 5) by (clear; lia). change (2 ^ 5) with 32.
    rewrite (swrap32_small ((w - 1) / 32)) by (clear - HW; Z.div_mod_to_equations; lia).
    replace (((w - 1) / 32) mod 18446744073709551616) with ((w - 1) / 32) by (symmetry; apply Z.mod_small; clear - HW; Z.div_mod_to_equations; lia).
    rewrite (Z.shiftl_mul_pow2 ((w - 1) / 32) 2) by (clear; lia). change (2 ^ 2) with 4.
    replace (lined + (w - 1) / 32 * 4) with (lined + 4 * ((w - 1) / 32)) by (clear; lia).
    assert (ULW : Z.of_nat (length wl) = nl / 4) by (clear - ULL L4; Z.div_mod_to_equations; lia).
    assert (JL : 0 <= (w - 1) / 32 < nl / 4) by (clear - HW WL L4; Z.div_mod_to_equations; lia).
    lwalk [0x9d358; 0x9d4b0].
    destruct (u32arr_nth wl ((w - 1) / 32) ltac:(lia)) as (dv & NTHD).
    pose proof (u32arr_read asegs m lined wl ((w - 1) / 32) dv _ UL NTHD ltac:(lia) eq_refl) as R.
    lstep. clear R.
    lwalk [0x9d368].
    clear ULL.
    arr_sw lined ((w - 1) / 32) (lined + 4 * ((w - 1) / 32)).
    lazymatch goal with H : Z.of_nat (length ?ws) = nl / 4 |- _ => assert (ULL : 4 * Z.of_nat (length ws) = nl) by (rewrite H; clear - L4; Z.div_mod_to_equations; lia) end.
    lwalk [0x9d474].
    apply evt_done. unfold dl1_end. do 6 eexists.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
      lazymatch goal with UBx : u8arr asegs mm bufs1 ?bsx, ULx : u32arr asegs mm lined ?wlx |- _ => exists mm, bsx, wlx end end.
    split; [reflexivity|].
    repeat (split; [assumption|]). assumption.
Qed.
