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

Notation D2L1_W lined nl bufs1 n1 := [(lined, lined + nl); (bufs1, bufs1 + n1)]%Z (only parsing).
Notation CMASK := (Z_to_bv 64 (-1073741824)) (only parsing).

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
Definition d2l1_exit (ra sp gp tp s0 s1 s2 s7 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lined nl bufs1 n1 ta t38 w : Z) (tw t38w : list word) : machine_state -> Prop :=
  fun ms' => exists (t2' a0' a1' t3' t4' t5' : word) (m' : mem) (bs' : list byte) (wl' : list word),
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 30) (Z_to_bv 64 (bufs1 + (w - 1))) t2' s0 s1 a0' a1' (Z_to_bv 64 lined) (Z_to_bv 64 (2 * (w - 1))) (Z_to_bv 64 (w - 1))
                  CMASK (Z_to_bv 64 268435455) (Z_to_bv 64 0)
                  s2 (Z_to_bv 64 bufs1) (Z_to_bv 64 SHB) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 w) s7 (Z_to_bv 64 ta) (Z_to_bv 64 t38) s10 s11
                  t3' t4' t5' t6)
             F (Z_to_bv 64 0x9ec98) fc None m' (seg_rom asegs)
    /\ munch (D2L1_W lined nl bufs1 n1) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' bufs1 bs' /\ Z.of_nat (length bs') = n1 /\ acc asegs m' bufs1 n1
    /\ u32arr asegs m' lined wl' /\ 4 * Z.of_nat (length wl') = nl /\ acc asegs m' lined nl
    /\ u32arr asegs m' ta tw /\ acc asegs m' ta 1024 /\ u32arr asegs m' t38 t38w /\ acc asegs m' t38 1024.
(* [comment removed for export] *)
Ltac gen_zreg r :=
  reg_val (Z_to_bv 5 r) ltac:(fun v => lazymatch v with
    | Z_to_bv 64 ?e => tryif is_var e then idtac else (let z := fresh "zv" in let E := fresh "Ezv" in remember e as z eqn:E in |- *; clear E)
    | _ => idtac end).

Lemma d2l1_pixels : forall (k : nat) (j : Z)
    (ra sp gp tp t2 s0 s1 a0 a1 s2 s7 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (bs : list byte) (wl tw t38w : list word),
  Z.of_nat k = w - 1 - j -> 0 <= j -> (1 <= k)%nat -> d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  mem_inv asegs m -> u8arr asegs m bufs1 bs -> Z.of_nat (length bs) = n1 -> acc asegs m bufs1 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  u32arr asegs m ta tw -> Z.of_nat (length tw) = 256 -> acc asegs m ta 1024 ->
  u32arr asegs m t38 t38w -> Z.of_nat (length t38w) = 256 -> acc asegs m t38 1024 ->
  evt asegs (d2l1_exit ra sp gp tp s0 s1 s2 s7 s10 s11 t6 F fc m lined nl bufs1 n1 ta t38 w tw t38w)
    (MS (mkR ra sp gp tp (Z_to_bv 64 30) (Z_to_bv 64 (bufs1 + j)) t2 s0 s1 a0 a1 (Z_to_bv 64 lined) (Z_to_bv 64 (2 * j)) (Z_to_bv 64 j)
             CMASK (Z_to_bv 64 268435455) (Z_to_bv 64 (w - 1 - j))
             s2 (Z_to_bv 64 bufs1) (Z_to_bv 64 SHB) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 w) s7 (Z_to_bv 64 ta) (Z_to_bv 64 t38) s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x9eb3c) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t2 s0 s1 a0 a1 s2 s7 s10 s11 t3 t4 t5 t6 F fc m lined nl bufs1 bufs2 n1 ta t38 t14 w bs wl tw t38w
    HK HJ HK1 GEO MI UB UBL ACCB UL ULL ACCL UT UTL ACCT U38 U38L ACC38.
  { lia. }
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & C0 & C8 & CHI & CSH & CSEG & L0 & LA4 & LNHI & LSH & LSEG
                   & TA0 & TA8 & TAHI & TASH & TASEG & T380 & T388 & T38HI & T38SH & T38SEG & T140 & T148 & T14HI & T14SH & T14SEG
                   & SEP1 & SEP2 & SEP12 & SEPT1 & SEPT2 & SEPT3 & SEP81 & SEP82 & SEP83 & SEP41 & SEP42 & SEP43).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (D2L1_W lined nl bufs1 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  (* [comment removed for export] *)
  assert (CONT : forall (t2' a0' a1' t3' t4' t5' : word) (mm : mem) (bs' : list byte) (wl' : list word),
    munch (D2L1_W lined nl bufs1 n1) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    u8arr asegs mm bufs1 bs' -> Z.of_nat (length bs') = n1 -> acc asegs mm bufs1 n1 ->
    u32arr asegs mm lined wl' -> 4 * Z.of_nat (length wl') = nl -> acc asegs mm lined nl ->
    u32arr asegs mm ta tw -> acc asegs mm ta 1024 -> u32arr asegs mm t38 t38w -> acc asegs mm t38 1024 ->
    evt asegs (d2l1_exit ra sp gp tp s0 s1 s2 s7 s10 s11 t6 F fc m lined nl bufs1 n1 ta t38 w tw t38w)
      (MS (mkR ra sp gp tp (Z_to_bv 64 30) (Z_to_bv 64 (bufs1 + j + 1)) t2' s0 s1 a0' a1' (Z_to_bv 64 lined) (Z_to_bv 64 (2 * j)) (Z_to_bv 64 j)
             (Z_to_bv 64 (-1073741824)) (Z_to_bv 64 268435455) (Z_to_bv 64 (w - 1 - j))
             s2 (Z_to_bv 64 bufs1) (Z_to_bv 64 2147450880) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 w) s7 (Z_to_bv 64 ta) (Z_to_bv 64 t38) s10 s11
             t3' t4' t5' t6)
          F (Z_to_bv 64 0x9ec24) fc None mm (seg_rom asegs))).
  { intros t2' a0' a1' t3' t4' t5' mm bs' wl' MU1 WM1 MI1 UB1 UBL1 ACCB1 UL1 ULL1 ACCL1 UT1 ACCT1 U381 ACC381.
    clear MI UB UBL ACCB UL ULL ACCL MU WM UT ACCT U38 ACC38.
    lwalk [0x9eb3c; 0x9ec98].
    replace (bufs1 + j + 1) with (bufs1 + (j + 1)) by lia. replace (2 * j + 2) with (2 * (j + 1)) by lia.
    replace (w - 1 - j + -1) with (w - 1 - (j + 1)) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w - 1) by lia. rewrite EJ in *. replace (w - 1 - (w - 1)) with 0 by lia.
      brF. lwalk [0x9eb3c; 0x9ec98].
      apply evt_done. unfold d2l1_exit, SHB. do 6 eexists. exists mm, bs', wl'. split; [reflexivity|].
      repeat (split; [assumption|]). assumption.
    - brT.
      eapply evt_cut.
      + eapply (IH (j + 1)) with (bs := bs') (wl := wl') (w := w) (n1 := n1) (nl := nl) (bufs2 := bufs2) (t14 := t14); try eassumption; try lia.
      + intros ms' PO. apply evt_done. unfold d2l1_exit in PO |- *.
        destruct PO as (t2'' & a0'' & a1'' & t3'' & t4'' & t5'' & m' & bs'' & wl'' & E & MU' & WM' & R).
        exists t2'', a0'', a1'', t3'', t4'', t5'', m', bs'', wl''.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R]. }
  (* [comment removed for export] *)
  pose proof (lxor3_eq (bufs1 + j + 1)) as LX1.
  assert (IDX1 : 0 <= Z.lxor (bufs1 + j + 1) 3 - bufs1 < n1) by (rewrite LX1; clear - HJ HK HW WN N4 B8; Z.div_mod_to_equations; lia).
  assert (STORE : forall (z : Z) (t2' t3' t4' t5' : word) (mm : mem) (bs' : list byte) (wl' : list word),
    munch (D2L1_W lined nl bufs1 n1) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    u8arr asegs mm bufs1 bs' -> Z.of_nat (length bs') = n1 -> acc asegs mm bufs1 n1 ->
    u32arr asegs mm lined wl' -> 4 * Z.of_nat (length wl') = nl -> acc asegs mm lined nl ->
    u32arr asegs mm ta tw -> acc asegs mm ta 1024 -> u32arr asegs mm t38 t38w -> acc asegs mm t38 1024 ->
    evt asegs (d2l1_exit ra sp gp tp s0 s1 s2 s7 s10 s11 t6 F fc m lined nl bufs1 n1 ta t38 w tw t38w)
      (MS (mkR ra sp gp tp (Z_to_bv 64 30) (Z_to_bv 64 (bufs1 + j + 1)) t2' s0 s1 (Z_to_bv 64 (Z.lxor (bufs1 + j + 1) 3)) (Z_to_bv 64 z)
             (Z_to_bv 64 lined) (Z_to_bv 64 (2 * j)) (Z_to_bv 64 j)
             (Z_to_bv 64 (-1073741824)) (Z_to_bv 64 268435455) (Z_to_bv 64 (w - 1 - j))
             s2 (Z_to_bv 64 bufs1) (Z_to_bv 64 2147450880) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 w) s7 (Z_to_bv 64 ta) (Z_to_bv 64 t38) s10 s11
             t3' t4' t5' t6)
          F (Z_to_bv 64 0x9ec10) fc None mm (seg_rom asegs))).
  { intros z t2' t3' t4' t5' mm bs' wl' MU1 WM1 MI1 UB1 UBL1 ACCB1 UL1 ULL1 ACCL1 UT1 ACCT1 U381 ACC381.
    clear MI UB UBL ACCB UL ULL ACCL MU WM UT ACCT U38 ACC38.
    lwalk [0x9ec20; 0x9ec98].
    remember (Z.lxor (bufs1 + j + 1) 3 - bufs1) as ix eqn:EIX.
    unpark SEP1. unpark SEPT2. unpark SEP82. unpark BSH.
    arr_sb bufs1 ix (Z.lxor (bufs1 + j + 1) 3).
    park SEP1. park SEPT2. park SEP82. park BSH.
    eapply CONT; eassumption. }
  (* [comment removed for export] *)
  lwalk [0x9ec98; 0x9ec10].
  replace (Z.land (j / 16) 268435455) with (j / 16)
    by (change 268435455 with (Z.ones 28); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; clear - HJ HK HW; Z.div_mod_to_equations; lia).
  replace (lined + j / 16 * 4) with (lined + 4 * (j / 16)) by (clear; lia).
  replace ((lined + 4 * (j / 16)) mod 18446744073709551616) with (lined + 4 * (j / 16))
    by (symmetry; apply Z.mod_small; clear - HJ HK HW WL L4 L0 LNHI; Z.div_mod_to_equations; lia).
  assert (ULW : Z.of_nat (length wl) = nl / 4) by (clear - ULL L4; Z.div_mod_to_equations; lia).
  assert (JL : 0 <= j / 16 < nl / 4) by (clear - HJ HK HW WL L4; Z.div_mod_to_equations; lia).
  lwalk [0x9ec98; 0x9ec10].
  (* [comment removed for export] *)
  pose proof (lxor3_eq (bufs1 + j)) as LX0.
  assert (IDX0 : 0 <= Z.lxor (bufs1 + j) 3 - bufs1 < n1) by (rewrite LX0; clear - HJ HK HW WN N4 B8; Z.div_mod_to_equations; lia).
  destruct UB as [HB WB].
  destruct (bytes_at_read1 m bufs1 bs (Z.lxor (bufs1 + j) 3 - bufs1) HB ltac:(lia)) as (ov & R).
  replace (bufs1 + (Z.lxor (bufs1 + j) 3 - bufs1)) with (Z.lxor (bufs1 + j) 3) in R by lia.
  lstep. clear R.
  assert (UB : u8arr asegs m bufs1 bs) by (split; assumption).
  clear HB WB.
  pose proof (bv_unsigned_in_range 8 ov) as OVR. unfold bv_modulus in OVR. change (2 ^ Z.of_N 8) with 256 in OVR.
  set (oz := bv_unsigned ov) in *.
  lwalk [0x9ec98; 0x9ec10].
  replace (ta + bv_unsigned ov * 4) with (ta + 4 * oz) by (subst oz; clear; lia).
  (* [comment removed for export] *)
  destruct (u32arr_nth wl (j / 16) ltac:(lia)) as (dv & NTHD).
  pose proof (u32arr_read asegs m lined wl (j / 16) dv _ UL NTHD ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9ec98; 0x9ec10].
  destruct (u32arr_nth tw oz ltac:(lia)) as (tv & NTHT).
  pose proof (u32arr_read asegs m ta tw oz tv _ UT NTHT ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9ec98; 0x9ec10].
  (* [comment removed for export] *)
  gen_zreg 11.                                   (* [comment removed for export] *)
  clear ULL.
  unpark SEP1. unpark SEPT1. unpark SEP81. unpark LSH.
  arr_sw lined (j / 16) (lined + 4 * (j / 16)).
  park SEP1. park SEPT1. park SEP81. park LSH.
  lazymatch goal with H : Z.of_nat (length ?ws) = nl / 4 |- _ => assert (ULL : 4 * Z.of_nat (length ws) = nl) by (rewrite H; clear - L4; Z.div_mod_to_equations; lia) end.
  (* [comment removed for export] *)
  lwalk [0x9ec98; 0x9ec10].
  lazymatch goal with UBx : u8arr asegs ?mm bufs1 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof UBx as [HB WB];
    destruct (bytes_at_read1 mm bufs1 bsx (Z.lxor (bufs1 + j + 1) 3 - bufs1) HB ltac:(lia)) as (rv & R) end.
  replace (bufs1 + (Z.lxor (bufs1 + j + 1) 3 - bufs1)) with (Z.lxor (bufs1 + j + 1) 3) in R by lia.
  lstep. clear R HB WB.
  replace (t38 + bv_unsigned ov * 4) with (t38 + 4 * oz) by (subst oz; clear; lia).
  lwalk [0x9ec98; 0x9ec10].
  destruct (u32arr_nth t38w oz ltac:(lia)) as (pv & NTHP).
  lazymatch goal with U : u32arr asegs ?mm t38 t38w |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read asegs mm t38 t38w oz pv _ U NTHP ltac:(lia) eq_refl) as R end.
  lstep. clear R.
  pose proof (bv_unsigned_in_range 8 rv) as RVR. unfold bv_modulus in RVR. change (2 ^ Z.of_N 8) with 256 in RVR.
  lwalk [0x9ec98; 0x9ec10].
  (* [comment removed for export] *)
  brfork MX.
  - lwalk [0x9ec98; 0x9ec10].
    brfork SG.
    + lwalk [0x9ec98; 0x9ec10]. eapply STORE; eassumption.
    + lwalk [0x9ec98; 0x9ec10]. eapply STORE; eassumption.
  - lwalk [0x9ec98; 0x9ec10].
    brfork SG.
    + lwalk [0x9ec98; 0x9ec10]. eapply STORE; eassumption.
    + lwalk [0x9ec98; 0x9ec10]. eapply STORE; eassumption.
Qed.

(* [comment removed for export] *)
Definition d2l1_end (ra sp gp tp s0 s1 s2 s7 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lined nl bufs1 n1 ta t38 w : Z) (tw t38w : list word) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' : word) (m' : mem) (bs' : list byte) (wl' : list word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 (Z_to_bv 64 bufs1) (Z_to_bv 64 SHB) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 w) s7 (Z_to_bv 64 ta) (Z_to_bv 64 t38) s10 s11
                  t3' t4' t5' t6)
             F (Z_to_bv 64 0x9ed24) fc None m' (seg_rom asegs)
    /\ munch (D2L1_W lined nl bufs1 n1) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' bufs1 bs' /\ Z.of_nat (length bs') = n1 /\ acc asegs m' bufs1 n1
    /\ u32arr asegs m' lined wl' /\ 4 * Z.of_nat (length wl') = nl /\ acc asegs m' lined nl
    /\ u32arr asegs m' ta tw /\ acc asegs m' ta 1024 /\ u32arr asegs m' t38 t38w /\ acc asegs m' t38 1024.

(* [comment removed for export] *)
Lemma d2l1_lastpx : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a7 s2 s7 s10 s11 t3 t4 t5 t6 : word) F fc (m0 m : mem)
    (lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (bs : list byte) (wl tw t38w : list word),
  d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  munch (D2L1_W lined nl bufs1 n1) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  u8arr asegs m bufs1 bs -> Z.of_nat (length bs) = n1 -> acc asegs m bufs1 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  u32arr asegs m ta tw -> Z.of_nat (length tw) = 256 -> acc asegs m ta 1024 ->
  u32arr asegs m t38 t38w -> Z.of_nat (length t38w) = 256 -> acc asegs m t38 1024 ->
  evt asegs (d2l1_end ra sp gp tp s0 s1 s2 s7 s10 s11 t6 F fc m0 lined nl bufs1 n1 ta t38 w tw t38w)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 lined) a3 a4 a5 (Z_to_bv 64 bufs1) a7
             s2 (Z_to_bv 64 bufs1) (Z_to_bv 64 SHB) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 w) s7 (Z_to_bv 64 ta) (Z_to_bv 64 t38) s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x9ec9c) fc None m (seg_rom asegs)).
Proof.
  intros until t38w. intros GEO MU WM MI UB UBL ACCB UL ULL ACCL UT UTL ACCT U38 U38L ACC38.
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & C0 & C8 & CHI & CSH & CSEG & L0 & LA4 & LNHI & LSH & LSEG
                   & TA0 & TA8 & TAHI & TASH & TASEG & T380 & T388 & T38HI & T38SH & T38SEG & T140 & T148 & T14HI & T14SH & T14SEG
                   & SEP1 & SEP2 & SEP12 & SEPT1 & SEPT2 & SEPT3 & SEP81 & SEP82 & SEP83 & SEP41 & SEP42 & SEP43).
  unfold SEGTOP_A, SHB in *.
  park_disj.
  pose proof (lxor3_eq (bufs1 + (w - 1))) as LX0.
  assert (IDX0 : 0 <= Z.lxor (bufs1 + (w - 1)) 3 - bufs1 < n1) by (rewrite LX0; clear - HW WN N4 B8; Z.div_mod_to_equations; lia).
  lwalk [0x9ed24].
  rewrite (srliw_idx (w - 1) 16) by (clear - HW; lia).
  replace (lined + (w - 1) / 16 * 4) with (lined + 4 * ((w - 1) / 16)) by (clear; lia).
  replace ((lined + 4 * ((w - 1) / 16)) mod 18446744073709551616) with (lined + 4 * ((w - 1) / 16))
    by (symmetry; apply Z.mod_small; clear - HW WL L4 L0 LNHI; Z.div_mod_to_equations; lia).
  assert (ULW : Z.of_nat (length wl) = nl / 4) by (clear - ULL L4; Z.div_mod_to_equations; lia).
  assert (JL : 0 <= (w - 1) / 16 < nl / 4) by (clear - HW WL L4; Z.div_mod_to_equations; lia).
  lwalk [0x9ed24].
  destruct UB as [HB WB].
  destruct (bytes_at_read1 m bufs1 bs (Z.lxor (bufs1 + (w - 1)) 3 - bufs1) HB ltac:(lia)) as (ov & R).
  replace (bufs1 + (Z.lxor (bufs1 + (w - 1)) 3 - bufs1)) with (Z.lxor (bufs1 + (w - 1)) 3) in R by lia.
  lstep. clear R.
  assert (UB : u8arr asegs m bufs1 bs) by (split; assumption).
  clear HB WB.
  pose proof (bv_unsigned_in_range 8 ov) as OVR. unfold bv_modulus in OVR. change (2 ^ Z.of_N 8) with 256 in OVR.
  set (oz := bv_unsigned ov) in *.
  lwalk [0x9ed24].
  replace (ta + bv_unsigned ov * 4) with (ta + 4 * oz) by (subst oz; clear; lia).
  destruct (u32arr_nth wl ((w - 1) / 16) ltac:(lia)) as (dv & NTHD).
  pose proof (u32arr_read asegs m lined wl ((w - 1) / 16) dv _ UL NTHD ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9ed24].
  destruct (u32arr_nth tw oz ltac:(lia)) as (tv & NTHT).
  pose proof (u32arr_read asegs m ta tw oz tv _ UT NTHT ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9ed24; 0x9ed20].
  gen_zreg 11.
  clear ULL.
  unpark SEP1. unpark SEP2. unpark SEPT1. unpark SEP81. unpark LSH.
  arr_sw lined ((w - 1) / 16) (lined + 4 * ((w - 1) / 16)).
  park SEP1. park SEP2. park SEPT1. park SEP81. park LSH.
  lazymatch goal with H : Z.of_nat (length ?ws) = nl / 4 |- _ => assert (ULL : 4 * Z.of_nat (length ws) = nl) by (rewrite H; clear - L4; Z.div_mod_to_equations; lia) end.
  apply evt_done. unfold d2l1_end. do 14 eexists.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
    lazymatch goal with UBx : u8arr asegs mm bufs1 ?bsx, ULx : u32arr asegs mm lined ?wlx |- _ => exists mm, bsx, wlx end end.
  split; [reflexivity|].
  repeat (split; [first [eassumption | eapply munch_trans; eassumption | eapply wmono_trans; eassumption] |]). eassumption.
Qed.

(* [comment removed for export] *)
Lemma d2l1_line : forall (ra sp gp tp t0 t1 t2 s0 a0 a3 a4 a5 a6 a7 s2 s7 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (sa lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (bs : list byte) (wl tw t38w : list word),
  d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  mem_inv asegs m -> u8arr asegs m bufs1 bs -> Z.of_nat (length bs) = n1 -> acc asegs m bufs1 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  u32arr asegs m ta tw -> Z.of_nat (length tw) = 256 -> acc asegs m ta 1024 ->
  u32arr asegs m t38 t38w -> Z.of_nat (length t38w) = 256 -> acc asegs m t38 1024 ->
  rw_cells asegs m (sa + 136) [C8 (Z_to_bv 64 bufs1)] ->
  0 < sa -> sa + 144 <= 2^47 -> (sa + 144 <= lined \/ lined + nl <= sa + 136) -> (sa + 144 <= bufs1 \/ bufs1 + n1 <= sa + 136) ->
  evt asegs (d2l1_end ra sp gp tp s0 (Z_to_bv 64 sa) s2 s7 s10 s11 t6 F fc m lined nl bufs1 n1 ta t38 w tw t38w)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 sa) a0 (Z_to_bv 64 2) (Z_to_bv 64 lined) a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 bufs1) (Z_to_bv 64 SHB) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 w) s7 (Z_to_bv 64 ta) (Z_to_bv 64 t38) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9eb14) fc None m (seg_rom asegs)).
Proof.
  intros until t38w. intros GEO MI UB UBL ACCB UL ULL ACCL UT UTL ACCT U38 U38L ACC38 CA SA0 SAHI SAL SAB.
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & C0 & C8 & CHI & CSH & CSEG & L0 & LA4 & LNHI & LSH & LSEG
                   & TA0 & TA8 & TAHI & TASH & TASEG & T380 & T388 & T38HI & T38SH & T38SEG & T140 & T148 & T14HI & T14SH & T14SEG
                   & SEP1 & SEP2 & SEP12 & SEPT1 & SEPT2 & SEPT3 & SEP81 & SEP82 & SEP83 & SEP41 & SEP42 & SEP43).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (D2L1_W lined nl bufs1 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  lstep.
  destruct (Z.eq_dec w 1) as [W1|W2].
  - (* [comment removed for export] *)
    brT.
    lwalk [0x9ec9c].
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (w - 1)) by (f_equal; clear - W1; lia).
    eapply d2l1_lastpx; try eassumption.
  - (* [comment removed for export] *)
    brF.
    lwalk [0x9eb3c].
    replace ((w - 1) * 4294967296 / 4294967296) with (w - 1) by (symmetry; apply Z.div_mul; clear; lia).
    eapply evt_cut.
    { eapply evt_eq.
      2:{ eapply (d2l1_pixels (Z.to_nat (w - 1)) 0) with (bs := bs) (wl := wl) (bufs2 := bufs2) (t14 := t14) (n1 := n1) (nl := nl);
            try eassumption; clear - HW W2; lia. }
      replace (bufs1 + 0) with bufs1 by (clear; lia). replace (2 * 0) with 0 by (clear; lia). replace (w - 1 - 0) with (w - 1) by (clear; lia).
      reflexivity. }
    intros ms' PO. unfold d2l1_exit in PO.
    destruct PO as (t2' & a0' & a1' & t3' & t4' & t5' & m' & bs' & wl' & -> & MU' & WM' & MI' & UB' & UBL' & ACCB' & UL' & ULL' & ACCL' & UT' & ACCT' & U38' & ACC38').
    (* [comment removed for export] *)
    assert (CA' : rw_cells asegs m' (sa + 136) [Cells.C8 (Z_to_bv 64 bufs1)]).
    { eapply rw_cells_transport; [exact CA | exact MU' | exact WM' |].
      unpark SAL. unpark SAB. cbn. clear - SAL SAB. lia. }
    clear MI UB UBL ACCB UL ULL ACCL UT ACCT U38 ACC38 CA MU WM.
    lwalk [0x9ec9c].
    eapply d2l1_lastpx; try eassumption.
Qed.
