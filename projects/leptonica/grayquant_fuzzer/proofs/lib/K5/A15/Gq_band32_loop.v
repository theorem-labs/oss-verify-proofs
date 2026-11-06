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

Notation B32_W datad n := [(datad, datad + n)]%Z (only parsing).

(* [comment removed for export] *)
Definition band32_row_exit (sp gp tp s0 s1 a0 a6 s2 s4 s5 s7 s8 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (datas datad wpls wpld w h i wa ha : Z) (ws : list word) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' a2' a3' t3' t4' t5' : word) (m' : mem) (wd' : list word),
    ms' = MS (mkR (Z_to_bv 64 datad) sp gp tp t0' t1' (Z_to_bv 64 (datad + 4 * (i * wpld))) s0 s1
                  a0 (Z_to_bv 64 wpld) a2' a3' (Z_to_bv 64 i) (Z_to_bv 64 (4 * wpls)) a6 (Z_to_bv 64 (datas + 4 * (i * wpls)))
                  s2 (Z_to_bv 64 wa) s4 s5 (Z_to_bv 64 (datas + 4 * (i * wpls))) s7 s8 s9 s10 (Z_to_bv 64 SHB)
                  t3' t4' t5' (Z_to_bv 64 ha))
             F (Z_to_bv 64 0xa0cec) fc None m' (seg_rom asegs)
    /\ munch (B32_W datad (4 * (wpld * h))) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datas ws /\ acc asegs m' datas (4 * (wpls * h))
    /\ u32arr asegs m' datad wd' /\ Z.of_nat (length wd') = wpld * h /\ acc asegs m' datad (4 * (wpld * h))
    /\ rw_cells asegs m' wa [C4 (Z_to_bv 64 w)] /\ rw_cells asegs m' ha [C4 (Z_to_bv 64 h)].

Lemma band32_pixels : forall (k : nat) (j : Z)
    (sp gp tp s0 s1 a0 a3 a6 s2 s4 s5 s7 s8 s9 s10 t4 t5 : word) F fc (m : mem)
    (datas datad wpls wpld w h i wa ha : Z) (ws wd : list word),
  Z.of_nat k = w - j -> 0 <= j -> (1 <= k)%nat -> 0 < w <= 20000 -> w <= wpls -> w <= 32 * wpld -> 0 < wpls <= 2^20 -> 0 < wpld <= 2^20 ->
  0 < h <= 2^20 -> 0 <= i < h -> wpls * h <= 2^24 -> wpld * h <= 2^24 ->
  0 < datas -> datas mod 8 = 0 -> datas + 4 * (wpls * h) <= 2^47 -> (datas + 4 * (wpls * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datas) ->
  (datas + 4 * (wpls * h) <= 0x10000 \/ SEGTOP_A <= datas) ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * (wpld * h) <= 2^47 -> (datad + 4 * (wpld * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * (wpld * h) <= 0x10000 \/ SEGTOP_A <= datad) ->
  (datas + 4 * (wpls * h) <= datad \/ datad + 4 * (wpld * h) <= datas) ->
  0 < wa -> wa + 4 <= 2^47 -> (wa + 4 <= datad \/ datad + 4 * (wpld * h) <= wa) ->
  0 < ha -> ha + 4 <= 2^47 -> (ha + 4 <= datad \/ datad + 4 * (wpld * h) <= ha) ->
  u32arr asegs m datas ws -> Z.of_nat (length ws) = wpls * h -> acc asegs m datas (4 * (wpls * h)) ->
  u32arr asegs m datad wd -> Z.of_nat (length wd) = wpld * h -> acc asegs m datad (4 * (wpld * h)) ->
  rw_cells asegs m wa [C4 (Z_to_bv 64 w)] -> rw_cells asegs m ha [C4 (Z_to_bv 64 h)] -> mem_inv asegs m ->
  evt asegs (band32_row_exit sp gp tp s0 s1 a0 a6 s2 s4 s5 s7 s8 s9 s10 F fc m datas datad wpls wpld w h i wa ha ws)
    (MS (mkR (Z_to_bv 64 datad) sp gp tp (Z_to_bv 64 j) (Z_to_bv 64 j) (Z_to_bv 64 (datad + 4 * (i * wpld))) s0 s1
             a0 (Z_to_bv 64 wpld) (Z_to_bv 64 (datas + 4 * (i * wpls + j))) a3 (Z_to_bv 64 i) (Z_to_bv 64 (4 * wpls)) a6
             (Z_to_bv 64 (datas + 4 * (i * wpls)))
             s2 (Z_to_bv 64 wa) s4 s5 (Z_to_bv 64 (datas + 4 * (i * wpls))) s7 s8 s9 s10 (Z_to_bv 64 SHB)
             (Z_to_bv 64 (datas + 4 * (i * wpls + j))) t4 t5 (Z_to_bv 64 ha))
        F (Z_to_bv 64 0xa0d50) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j sp gp tp s0 s1 a0 a3 a6 s2 s4 s5 s7 s8 s9 s10 t4 t5 F fc m datas datad wpls wpld w h i wa ha ws wd
    HK HJ HK1 HW WS WD WPLS WPLD HH HI SH DH S0 S8 SHI SSH SSEG D0 D8 DHI DSH DSEG SEP W0 WHI WSEP H0 HHI HSEP UAS UASL ACCS UA UAL ACCD WC HC MI.
  { lia. }
  assert (NS : i * wpls + wpls <= wpls * h) by (clear - HI WPLS; nia).
  assert (NS0 : 0 <= i * wpls) by (clear - HI WPLS; nia).
  assert (ND : i * wpld + wpld <= wpld * h) by (clear - HI WPLD; nia).
  assert (ND0 : 0 <= i * wpld) by (clear - HI WPLD; nia).
  assert (JD : 0 <= j / 32 < wpld) by (clear - HJ HK WD HW; Z.div_mod_to_equations; lia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (B32_W datad (4 * (wpld * h))) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  assert (CONT : forall (a3' t4' t5' : word) (mm : mem) (wd' : list word),
    munch (B32_W datad (4 * (wpld * h))) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    u32arr asegs mm datas ws -> acc asegs mm datas (4 * (wpls * h)) ->
    u32arr asegs mm datad wd' -> Z.of_nat (length wd') = wpld * h -> acc asegs mm datad (4 * (wpld * h)) ->
    rw_cells asegs mm wa [C4 (Z_to_bv 64 w)] -> rw_cells asegs mm ha [C4 (Z_to_bv 64 h)] ->
    evt asegs (band32_row_exit sp gp tp s0 s1 a0 a6 s2 s4 s5 s7 s8 s9 s10 F fc m datas datad wpls wpld w h i wa ha ws)
      (MS (mkR (Z_to_bv 64 datad) sp gp tp (Z_to_bv 64 j) (Z_to_bv 64 j) (Z_to_bv 64 (datad + 4 * (i * wpld))) s0 s1
               a0 (Z_to_bv 64 wpld) (Z_to_bv 64 (datas + 4 * (i * wpls + j))) a3' (Z_to_bv 64 i) (Z_to_bv 64 (4 * wpls)) a6
               (Z_to_bv 64 (datas + 4 * (i * wpls)))
               s2 (Z_to_bv 64 wa) s4 s5 (Z_to_bv 64 (datas + 4 * (i * wpls))) s7 s8 s9 s10 (Z_to_bv 64 SHB)
               (Z_to_bv 64 (datas + 4 * (i * wpls + j))) t4' t5' (Z_to_bv 64 ha))
          F (Z_to_bv 64 0xa0d38) fc None mm (seg_rom asegs))).
  { intros a3' t4' t5' mm wd' MU1 WM1 MI1 UAS1 ACCS1 UA1 UAL1 ACCD1 WC1 HC1.
    clear UAS ACCS UA UAL ACCD WC HC MI MU WM.
    lwalk [0xa0d50; 0xa0cec]. sx32_fix.
    replace (datas + 4 * (i * wpls + j) + 4) with (datas + 4 * (i * wpls + (j + 1))) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w) by lia. rewrite EJ in *.
      brT. apply evt_done. unfold band32_row_exit. do 7 eexists. exists mm, wd'. split; [reflexivity|].
      repeat (split; [assumption|]). assumption.
    - brF.
      eapply evt_cut.
      + eapply (IH (j + 1)) with (ws := ws) (wd := wd') (h := h); try eassumption; try lia.
      + intros ms' PO. apply evt_done. unfold band32_row_exit in PO |- *.
        destruct PO as (t0' & t1' & a2' & a3'' & t3' & t4'' & t5'' & m' & wd'' & E & MU' & WM' & R).
        exists t0', t1', a2', a3'', t3', t4'', t5'', m', wd''.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R]. }
  (* [comment removed for export] *)
  lwalk [0xa0d60; 0xa0dc8].
  destruct (u32arr_nth ws (i * wpls + j) ltac:(lia)) as (wv & NTH).
  pose proof (u32arr_read asegs m datas ws (i * wpls + j) wv _ UAS NTH ltac:(lia) eq_refl) as R.
  lstep. clear R.
  (* [comment removed for export] *)
  lwalk [0xa0d38; 0xa0d28; 0xa0e58].
  brfork B1; [solve [eapply CONT; eassumption]|].
  lwalk [0xa0d38; 0xa0d28; 0xa0e58].
  brfork B2; [solve [eapply CONT; eassumption]|].
  lwalk [0xa0d38; 0xa0d28; 0xa0e58].
  brfork B3; [solve [eapply CONT; eassumption]|].
  lwalk [0xa0d38; 0xa0d28; 0xa0e58].
  brfork B4; [solve [eapply CONT; eassumption]|].
  lwalk [0xa0d38; 0xa0d28; 0xa0e58].
  brfork B5; [solve [eapply CONT; eassumption]|].
  lwalk [0xa0d38; 0xa0d28; 0xa0e58].
  brfork B6; [solve [eapply CONT; eassumption]|].
  lwalk [0xa0d38; 0xa0d28; 0xa0e58].
  (* [comment removed for export] *)
  rewrite !(srliw_idx j 32) by lia.
  replace (datad + 4 * (i * wpld) + j / 32 * 4) with (datad + 4 * (i * wpld + j / 32)) by lia.
  rewrite (Z.mod_small (datad + 4 * (i * wpld + j / 32)) 18446744073709551616) by lia.
  lwalk [0xa0d28; 0xa0e58].
  destruct (u32arr_nth wd (i * wpld + j / 32) ltac:(lia)) as (dv & NTHD).
  pose proof (u32arr_read asegs m datad wd (i * wpld + j / 32) dv _ UA NTHD ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0xa0d34].
  arr_sw datad (i * wpld + j / 32) (datad + 4 * (i * wpld + j / 32)).
  eapply CONT; eassumption.
  Qed.

(* [comment removed for export] *)
Definition band32_exit (sp gp tp s0 s1 a0 a6 s2 s4 s5 s7 s8 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (datas datad wpls wpld w h wa ha : Z) (ws : list word) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a2' a3' a7' s6' t3' t4' t5' : word) (m' : mem) (wd' : list word),
    ms' = MS (mkR (Z_to_bv 64 datad) sp gp tp t0' t1' t2' s0 s1
                  a0 (Z_to_bv 64 wpld) a2' a3' (Z_to_bv 64 h) (Z_to_bv 64 (4 * wpls)) a6 a7'
                  s2 (Z_to_bv 64 wa) s4 s5 s6' s7 s8 s9 s10 (Z_to_bv 64 SHB)
                  t3' t4' t5' (Z_to_bv 64 ha))
             F (Z_to_bv 64 0xa0dd4) fc None m' (seg_rom asegs)
    /\ munch (B32_W datad (4 * (wpld * h))) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datas ws /\ acc asegs m' datas (4 * (wpls * h))
    /\ u32arr asegs m' datad wd' /\ Z.of_nat (length wd') = wpld * h /\ acc asegs m' datad (4 * (wpld * h))
    /\ rw_cells asegs m' wa [C4 (Z_to_bv 64 w)] /\ rw_cells asegs m' ha [C4 (Z_to_bv 64 h)].

Lemma band32_rows : forall (k : nat) (i : Z)
    (sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a6 s2 s4 s5 s7 s8 s9 s10 t3 t4 t5 : word) F fc (m : mem)
    (datas datad wpls wpld w h wa ha : Z) (ws wd : list word),
  Z.of_nat k = h - i -> 0 <= i -> (1 <= k)%nat -> 0 < w <= 20000 -> w <= wpls -> w <= 32 * wpld -> 0 < wpls <= 2^20 -> 0 < wpld <= 2^20 ->
  0 < h <= 2^20 -> wpls * h <= 2^24 -> wpld * h <= 2^24 ->
  0 < datas -> datas mod 8 = 0 -> datas + 4 * (wpls * h) <= 2^47 -> (datas + 4 * (wpls * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datas) ->
  (datas + 4 * (wpls * h) <= 0x10000 \/ SEGTOP_A <= datas) ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * (wpld * h) <= 2^47 -> (datad + 4 * (wpld * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * (wpld * h) <= 0x10000 \/ SEGTOP_A <= datad) ->
  (datas + 4 * (wpls * h) <= datad \/ datad + 4 * (wpld * h) <= datas) ->
  0 < wa -> wa + 4 <= 2^47 -> (wa + 4 <= datad \/ datad + 4 * (wpld * h) <= wa) ->
  0 < ha -> ha + 4 <= 2^47 -> (ha + 4 <= datad \/ datad + 4 * (wpld * h) <= ha) ->
  u32arr asegs m datas ws -> Z.of_nat (length ws) = wpls * h -> acc asegs m datas (4 * (wpls * h)) ->
  u32arr asegs m datad wd -> Z.of_nat (length wd) = wpld * h -> acc asegs m datad (4 * (wpld * h)) ->
  rw_cells asegs m wa [C4 (Z_to_bv 64 w)] -> rw_cells asegs m ha [C4 (Z_to_bv 64 h)] -> mem_inv asegs m ->
  evt asegs (band32_exit sp gp tp s0 s1 a0 a6 s2 s4 s5 s7 s8 s9 s10 F fc m datas datad wpls wpld w h wa ha ws)
    (MS (mkR (Z_to_bv 64 datad) sp gp tp t0 t1 t2 s0 s1
             a0 (Z_to_bv 64 wpld) a2 a3 (Z_to_bv 64 i) (Z_to_bv 64 (4 * wpls)) a6 (Z_to_bv 64 (datas + 4 * (i * wpls)))
             s2 (Z_to_bv 64 wa) s4 s5 (Z_to_bv 64 (datas + 4 * (i * wpls))) s7 s8 s9 s10 (Z_to_bv 64 SHB)
             t3 t4 t5 (Z_to_bv 64 ha))
        F (Z_to_bv 64 0xa0d00) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a6 s2 s4 s5 s7 s8 s9 s10 t3 t4 t5 F fc m datas datad wpls wpld w h wa ha ws wd
    HK HI HK1 HW WS WD WPLS WPLD HH SH DH S0 S8 SHI SSH SSEG D0 D8 DHI DSH DSEG SEP W0 WHI WSEP H0 HHI HSEP UAS UASL ACCS UA UAL ACCD WC HC MI.
  { lia. }
  assert (NS0 : 0 <= i * wpls) by (clear - HI WPLS; nia).
  assert (ND0 : 0 <= i * wpld <= 2^24) by (clear - HI HK HH WPLD DH; nia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (B32_W datad (4 * (wpld * h))) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0xa0d50; 0xa0cec].
  rewrite (sx32_small w) by lia.
  brF.
  lwalk [0xa0d50; 0xa0cec].
  (* [comment removed for export] *)
  assert (Q1 : Z.of_nat (Z.to_nat w) = w - 0) by (clear - HW; lia).
  assert (Q3 : (1 <= Z.to_nat w)%nat) by (clear - HW; lia).
  assert (Q4 : 0 <= i < h) by (clear - HI HK; lia).
  eapply evt_cut.
  { epose proof (band32_pixels (Z.to_nat w) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m datas datad wpls wpld w h i wa ha ws wd
                 Q1 ltac:(lia) Q3 HW WS WD WPLS WPLD HH Q4 SH DH S0 S8 SHI SSH SSEG D0 D8 DHI DSH DSEG SEP W0 WHI WSEP H0 HHI HSEP UAS UASL ACCS UA UAL ACCD WC HC MI) as ZR.
  unfold SHB in ZR.
  replace (datas + 4 * (i * wpls + 0)) with (datas + 4 * (i * wpls)) in ZR by (clear; lia).
  replace (datad + 4 * (i * wpld)) with (datad + i * wpld * 4) in ZR at 1 by (clear; lia).
  exact ZR.
  }
  intros ms' PO. unfold band32_row_exit in PO.
  destruct PO as (t0' & t1' & a2' & a3' & t3' & t4' & t5' & m' & wd' & -> & MU' & WM' & MI' & UAS' & ACCS' & UA' & UAL' & ACCD' & WC' & HC').
  clear UAS ACCS UA UAL ACCD WC HC MI.
  lwalk [0xa0d00; 0xa0dd4].
  rewrite (sx32_small h) by lia.
  replace (datas + 4 * (i * wpls) + 4 * wpls) with (datas + 4 * ((i + 1) * wpls)) by lia.
  destruct k as [|k].
  - assert (EI : i + 1 = h) by lia. rewrite EI in *.
  brT. apply evt_done. unfold band32_exit. do 10 eexists. exists m', wd'. split; [reflexivity|].
  split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')|].
  repeat (split; [assumption|]). assumption.
  - brF.
  eapply evt_cut.
  + eapply (IH (i + 1)) with (ws := ws) (wd := wd') (w := w); try eassumption; try lia.
  + intros ms' PO. apply evt_done. unfold band32_exit in PO |- *.
  destruct PO as (t0'' & t1'' & t2'' & a2'' & a3'' & a7'' & s6'' & t3'' & t4'' & t5'' & m'' & wd'' & E & MU'' & WM'' & R).
  exists t0'', t1'', t2'', a2'', a3'', a7'', s6'', t3'', t4'', t5'', m'', wd''.
  split; [exact E|]. split; [exact (munch_trans _ _ _ _ (munch_trans _ _ _ _ MU MU') MU'')|]. split; [exact (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ WM WM') WM'')| exact R].
Qed.
