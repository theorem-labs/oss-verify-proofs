(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit GmL_k3h_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition e3h_rowend (sp gp tp s0 s1 a0 a2 a3 a4 s3 s4 s5 s6 s8 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (datas datad n w h wa ha : Z) (bss : list byte) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a1' a5' a6' a7' s2' s7' s11' t3' t4' t5' t6' : word) (m' : mem) (bsd' : list byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0 a1' a2 a3 a4 a5' a6' a7' s2' s3 s4 s5 s6 s7' s8 s9 (Z_to_bv 64 SHB) s11' t3' t4' t5' t6')
             F (Z_to_bv 64 0xa700c) fc None m' (seg_rom asegs)
    /\ munch [(datad, datad + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' datad bsd' /\ Z.of_nat (length bsd') = n
    /\ bytes_at asegs m' datas bss /\ acc asegs m' datas n /\ acc asegs m' datad n
    /\ rw_cells asegs m' wa [C4 (Z_to_bv 64 w)] /\ rw_cells asegs m' ha [C4 (Z_to_bv 64 h)].

Lemma e3h_cols : forall (k : nat) (t : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (datas datad n w h wa ha qs qd li wpl : Z) (bss bsd : list byte),
  (1 <= k)%nat -> 0 <= t -> 8 * (t + Z.of_nat k - 1) + 9 < w -> w <= 8 * (t + Z.of_nat k - 1) + 17 -> w <= 4 * wpl -> wpl <= 5000 ->
  datas = 8 * qs -> 0 < qs -> 0 <= li -> 4 * li + 4 * wpl <= n -> datas + n <= 2^47 ->
  hid (datas + n <= 0x7fff7000 \/ 0x10007fff8000 <= datas) ->
  datad = 8 * qd -> 0 < qd -> datad + n <= 2^47 ->
  hid (datad + n <= 0x7fff7000 \/ 0x10007fff8000 <= datad) -> hid (datad + n <= 0x10000 \/ SEGTOP_A <= datad) ->
  hid (datas + n <= datad \/ datad + n <= datas) ->
  0 < wa -> wa + 4 <= 2^47 -> hid (wa + 4 <= datad \/ datad + n <= wa) ->
  0 < ha -> ha + 4 <= 2^47 -> hid (ha + 4 <= datad \/ datad + n <= ha) ->
  bytes_at asegs m datas bss -> Z.of_nat (length bss) = n -> acc asegs m datas n ->
  u8arr asegs m datad bsd -> Z.of_nat (length bsd) = n -> acc asegs m datad n ->
  rw_cells asegs m wa [C4 (Z_to_bv 64 w)] -> rw_cells asegs m ha [C4 (Z_to_bv 64 h)] -> mem_inv asegs m ->
  evt asegs (e3h_rowend sp gp tp s0 s1 a0 a2 a3 a4 (Z_to_bv 64 wa) s4 (Z_to_bv 64 (datas + 4 * li)) (Z_to_bv 64 (datad + 4 * li)) s8 s9 F fc m
                        datas datad n w h wa ha bss)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (8 * t)) (Z_to_bv 64 wa) s4 (Z_to_bv 64 (datas + 4 * li))
             (Z_to_bv 64 (datad + 4 * li)) s7 s8 s9 (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa702c) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros t ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 s11 t3 t4 t5 t6 F fc m
    datas datad n w h wa ha qs qd li wpl bss bsd
    HK HT HTW HTE HW WPL D8 D0 LI LN DHI DSH E8 E0 EHI ESH ESEG SEP W0 WHI WSEP H0 HHI HSEP HB HBL ACCS UA UAL ACCD WC HC MI.
  { lia. }
  subst datas datad.
  pose proof (munch_refl [(8 * qd, 8 * qd + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  k3hwalk (8 * qs) bss HB (8 * qd) [0xa7298].
  lwalk (@nil Z). sx32_fix.
  destruct k as [|k].
  - (* [comment removed for export] *)
    brF. lwalk [0xa700c].
    apply evt_done. unfold e3h_rowend. do 15 eexists. eexists. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UA|]. split; [exact UAL|].
    split; [exact HB|]. split; [exact ACCS|]. split; [exact ACCD|]. split; [exact WC| exact HC].
  - brT.
    replace (8 * t + 8) with (8 * (t + 1)) by lia.
    eapply evt_cut.
    + eapply (IH (t + 1)) with (qs := qs) (qd := qd) (wpl := wpl) (bss := bss); try eassumption; try reflexivity; try lia.
    + intros ms' PO. apply evt_done. unfold e3h_rowend in PO |- *.
      destruct PO as (ra' & t0' & t1' & t2' & a1' & a5' & a6' & a7' & s2' & s7' & s11' & t3' & t4' & t5' & t6' & m' & bsd' & E & MU' & WM' & R).
      exists ra', t0', t1', t2', a1', a5', a6', a7', s2', s7', s11', t3', t4', t5', t6', m', bsd'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition e3h_exit (sp gp tp s0 s1 a0 s3 s4 s8 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad n : Z)
    : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s5' s6' s7' s11' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2' s3 s4 s5' s6' s7' s8 s9 (Z_to_bv 64 SHB) s11' t3' t4' t5' t6')
             F (Z_to_bv 64 0xa7404) fc None m' (seg_rom asegs)
    /\ munch [(datad, datad + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

Lemma e3h_rows : forall (k : nat) (i : Z) (K : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a5 a6 a7 s2 s7 s8 s9 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (datas datad n w h wa ha qs qd wpl : Z) (bss bsd : list byte),
  Z.of_nat k = h - i -> 0 <= i -> (1 <= k)%nat -> 0 < w <= 4 * wpl -> wpl <= 5000 -> 0 < h <= 20000 -> n = 4 * (wpl * h) ->
  (10 <= w -> (1 <= K)%nat /\ 8 * (Z.of_nat K - 1) + 9 < w <= 8 * (Z.of_nat K - 1) + 17) ->
  datas = 8 * qs -> 0 < qs -> datas + n <= 2^47 -> hid (datas + n <= 0x7fff7000 \/ 0x10007fff8000 <= datas) ->
  datad = 8 * qd -> 0 < qd -> datad + n <= 2^47 ->
  hid (datad + n <= 0x7fff7000 \/ 0x10007fff8000 <= datad) -> hid (datad + n <= 0x10000 \/ SEGTOP_A <= datad) ->
  hid (datas + n <= datad \/ datad + n <= datas) ->
  0 < wa -> wa + 4 <= 2^47 -> hid (wa + 4 <= datad \/ datad + n <= wa) ->
  0 < ha -> ha + 4 <= 2^47 -> hid (ha + 4 <= datad \/ datad + n <= ha) ->
  bytes_at asegs m datas bss -> Z.of_nat (length bss) = n -> acc asegs m datas n ->
  u8arr asegs m datad bsd -> Z.of_nat (length bsd) = n -> acc asegs m datad n ->
  rw_cells asegs m wa [C4 (Z_to_bv 64 w)] -> rw_cells asegs m ha [C4 (Z_to_bv 64 h)] -> mem_inv asegs m ->
  evt asegs (e3h_exit sp gp tp s0 s1 a0 (Z_to_bv 64 wa) (Z_to_bv 64 ha) s8 s9 F fc m datad n)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 i) (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 10) a5 a6 a7 s2 (Z_to_bv 64 wa) (Z_to_bv 64 ha)
             (Z_to_bv 64 (datas + 4 * (wpl * i))) (Z_to_bv 64 (datad + 4 * (wpl * i))) s7 s8 s9 (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa7020) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a5 a6 a7 s2 s7 s8 s9 s11 t3 t4 t5 t6 F fc m
    datas datad n w h wa ha qs qd wpl bss bsd
    HK HI HK1 HW WPL HH EN HKK D8 D0 DHI DSH E8 E0 EHI ESH ESEG SEP W0 WHI WSEP H0 HHI HSEP HB HBL ACCS UA UAL ACCD WC HC MI.
  { lia. }
  assert (NL : wpl * i + wpl <= wpl * h) by nia.
  assert (NL0 : 0 <= wpl * i) by nia.
  (* [comment removed for export] *)
  assert (ROWEND : forall (ra' t0' t1' t2' a1' a5' a6' a7' s2' s7' s11' t3' t4' t5' t6' : word) (m1 : mem) (bsd1 : list byte),
    munch [(datad, datad + n)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    u8arr asegs m1 datad bsd1 -> Z.of_nat (length bsd1) = n ->
    bytes_at asegs m1 datas bss -> acc asegs m1 datas n -> acc asegs m1 datad n ->
    rw_cells asegs m1 wa [C4 (Z_to_bv 64 w)] -> rw_cells asegs m1 ha [C4 (Z_to_bv 64 h)] ->
    evt asegs (e3h_exit sp gp tp s0 s1 a0 (Z_to_bv 64 wa) (Z_to_bv 64 ha) s8 s9 F fc m datad n)
      (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0 a1' (Z_to_bv 64 i) (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 10) a5' a6' a7' s2' (Z_to_bv 64 wa) (Z_to_bv 64 ha)
               (Z_to_bv 64 (datas + 4 * (wpl * i))) (Z_to_bv 64 (datad + 4 * (wpl * i))) s7' s8 s9 (Z_to_bv 64 SHB) s11' t3' t4' t5' t6')
          F (Z_to_bv 64 0xa700c) fc None m1 (seg_rom asegs))).
  { intros ra' t0' t1' t2' a1' a5' a6' a7' s2' s7' s11' t3' t4' t5' t6' m1 bsd1 MU1 WM1 MI1 UA1 UAL1 HB1 ACCS1 ACCD1 WC1 HC1.
    lwalk [0xa7020; 0xa7404]. sx32_fix.
    replace (datas + 4 * (wpl * i) + wpl * 4) with (datas + 4 * (wpl * (i + 1))) by lia.
    replace (datad + 4 * (wpl * i) + wpl * 4) with (datad + 4 * (wpl * (i + 1))) by lia.
    destruct k as [|k].
    - assert (EI : i + 1 = h) by lia. rewrite EI in *.
      brT. apply evt_done. unfold e3h_exit. do 20 eexists. eexists. split; [reflexivity|].
      split; [exact MU1|]. split; [exact WM1| exact MI1].
    - brF.
      eapply evt_cut.
      + eapply (IH (i + 1) K) with (qs := qs) (qd := qd) (bss := bss) (bsd := bsd1) (w := w) (h := h); try eassumption; try lia.
      + intros ms' PO. apply evt_done. unfold e3h_exit in PO |- *.
        destruct PO as (ra2 & t02 & t12 & t22 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & s22 & s52 & s62 & s72 & s112 & t32 & t42 & t52 & t62 & m' & E & MU' & WM' & MI').
        exists ra2, t02, t12, t22, a12, a22, a32, a42, a52, a62, a72, s22, s52, s62, s72, s112, t32, t42, t52, t62, m'.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact MI']. }
  lwalk (@nil Z). sx32_fix.
  destruct (Z.ltb_spec w 10) as [WLT|WGE].
  - (* [comment removed for export] *)
    brT. eapply ROWEND with (m1 := m) (bsd1 := bsd); try eassumption; [apply munch_refl | apply wmono_refl].
  - brF. lwalk [0xa702c].
    destruct (HKK WGE) as (HK0 & HKa & HKb).
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (8 * 0)) by reflexivity.
    eapply evt_cut.
    + eapply (e3h_cols K 0) with (qs := qs) (qd := qd) (wpl := wpl) (li := wpl * i) (bss := bss) (bsd := bsd) (w := w) (h := h) (wa := wa) (ha := ha);
        try eassumption; try lia.
    + intros ms' PO. unfold e3h_rowend in PO.
      destruct PO as (ra' & t0' & t1' & t2' & a1' & a5' & a6' & a7' & s2' & s7' & s11' & t3' & t4' & t5' & t6' & m' & bsd' & E & MU' & WM' & MI' & UA' & UAL' & HB' & ACCS' & ACCD' & WC' & HC').
      subst ms'.
      eapply ROWEND with (m1 := m') (bsd1 := bsd'); eassumption.
Qed.
