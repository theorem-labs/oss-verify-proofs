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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Gq_rgb.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Notation D32_W datad n sa fr :=
  [(datad, datad + n); (sa - 16, sa); (fr + 176, fr + 176 + 4); (fr + 192, fr + 192 + 4); (fr + 208, fr + 208 + 4); (sa + 16, sa + 160)]%Z (only parsing).



(* [comment removed for export] *)
Definition d32_slots (c16 c24 c32 c40 : word) (wpld datad wpls : Z) (l80 : word) (l88 i : Z) (l104 : word) (fr : Z) : list cell :=
  [C8 c16; C8 c24; C8 c32; C8 c40; C8 (Z_to_bv 64 wpld); C8 (Z_to_bv 64 datad); C8 (Z_to_bv 64 (4 * wpls)); C8 (Z_to_bv 64 (fr + 48));
   C8 l80; C8 (Z_to_bv 64 l88); C8 (Z_to_bv 64 i); C8 l104;
   C8 (Z_to_bv 64 (fr + 112)); C8 (Z_to_bv 64 (fr + 96)); C8 (Z_to_bv 64 (fr + 80)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 (fr + 32))].
(* [comment removed for export] *)
Definition d32_fcells (w h : Z) (dw r1 g1 b1 r2 g2 b2 rv gv bv : word) (p : list (list byte)) : list cell :=
  [C4 (Z_to_bv 64 w); CB 12 (nth 0 p []); C4 (Z_to_bv 64 h); CB 12 (nth 1 p []); C4 dw; CB 12 (nth 2 p []);
   C4 r1; CB 12 (nth 3 p []); C4 g1; CB 12 (nth 4 p []); C4 b1; CB 12 (nth 5 p []);
   C4 r2; CB 12 (nth 6 p []); C4 g2; CB 12 (nth 7 p []); C4 b2; CB 12 (nth 8 p []);
   C4 rv; CB 12 (nth 9 p []); C4 gv; CB 12 (nth 10 p []); C4 bv].

(* [comment removed for export] *)
Definition d32_geom (lo sa fr datas datad wpls wpld w h : Z) : Prop :=
  0 < w <= 20000 /\ w <= wpls /\ w <= 32 * wpld /\ 0 < wpls <= 2^20 /\ 0 < wpld <= 2^20 /\ 0 < h <= 2^20
  /\ wpls * h <= 2^24 /\ wpld * h <= 2^24
  /\ 0 < datas /\ datas mod 8 = 0 /\ datas + 4 * (wpls * h) <= 2^47 /\ (datas + 4 * (wpls * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datas)
  /\ (datas + 4 * (wpls * h) <= 0x10000 \/ SEGTOP_A <= datas)
  /\ 0 < datad /\ datad mod 8 = 0 /\ datad + 4 * (wpld * h) <= 2^47 /\ (datad + 4 * (wpld * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datad)
  /\ (datad + 4 * (wpld * h) <= 0x10000 \/ SEGTOP_A <= datad)
  /\ (datas + 4 * (wpls * h) <= datad \/ datad + 4 * (wpld * h) <= datas)
  /\ 0 < fr /\ fr mod 8 = 0 /\ SEGTOP_A <= fr /\ (fr + 224 <= 0x7fff7000 \/ 0x10007fff8000 <= fr)
  /\ (fr + 224 <= datad \/ datad + 4 * (wpld * h) <= fr) /\ (fr + 224 <= datas \/ datas + 4 * (wpls * h) <= fr)
  /\ fr + 224 <= lo /\ datad + 4 * (wpld * h) <= lo /\ datas + 4 * (wpls * h) <= lo
  /\ 0x10007fff8000 <= lo /\ lo <= sa - 16 /\ sa mod 8 = 0 /\ sa + 160 <= 2^47.

(* [comment removed for export] *)
Definition d32_row_exit (sp gp tp t2 s0 s1 s2 s3 s4 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo sa fr datas datad wpls wpld w h : Z) (ws : list word) (c16 c24 c32 c40 l80 l104 : word) (l88 i : Z)
    (dw r1 g1 b1 r2 g2 b2 : word) (p : list (list byte)) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' a0' a1' a2' a4' a5' a6' a7' s5' s7' s8' s9' : word) (m' : mem) (wd' : list word) (rv' gv' bv' : word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' (Z_to_bv 64 SHB) a4' a5' a6' a7'
                  s2 s3 s4 s5' s6 s7' s8' s9' s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa10f8) fc None m' (seg_rom asegs)
    /\ munch (D32_W datad (4 * (wpld * h)) sa fr) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo sa
    /\ ro_cells asegs m' g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)]
    /\ ro_cells asegs m' g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)]
    /\ u32arr asegs m' datas ws /\ acc asegs m' datas (4 * (wpls * h))
    /\ u32arr asegs m' datad wd' /\ Z.of_nat (length wd') = wpld * h /\ acc asegs m' datad (4 * (wpld * h))
    /\ rw_cells asegs m' (sa + 16) (d32_slots c16 c24 c32 c40 wpld datad wpls l80 l88 i l104 fr)
    /\ rw_cells asegs m' (fr + 32) (d32_fcells w h dw r1 g1 b1 r2 g2 b2 rv' gv' bv' p)
    /\ acc asegs m' (fr + 176) 4 /\ acc asegs m' (fr + 192) 4 /\ acc asegs m' (fr + 208) 4.

(* [comment removed for export] *)
Local Ltac gen_reg r :=
  reg_val (Z_to_bv 5 r) ltac:(fun v => tryif is_var v then idtac else (let d := fresh "dw" in let E := fresh "E" in remember v as d eqn:E; clear E)).

Lemma discr32_pixels : forall (k : nat) (j : Z)
    (ra gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem)
    (lo sa fr datas datad wpls wpld w h : Z) (ws wd : list word) (c16 c24 c32 c40 l80 : word) (l88 i : Z)
    (dw r1 g1 b1 r2 g2 b2 rv gv bv : word) (p : list (list byte)),
  Z.of_nat k = w - j -> 0 <= j -> (1 <= k)%nat -> 0 <= i < h -> d32_geom lo sa fr datas datad wpls wpld w h ->
  mem_inv asegs m -> stk asegs m lo sa ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  u32arr asegs m datas ws -> Z.of_nat (length ws) = wpls * h -> acc asegs m datas (4 * (wpls * h)) ->
  u32arr asegs m datad wd -> Z.of_nat (length wd) = wpld * h -> acc asegs m datad (4 * (wpld * h)) ->
  rw_cells asegs m (sa + 16) (d32_slots c16 c24 c32 c40 wpld datad wpls l80 l88 i (Z_to_bv 64 (datad + 4 * (i * wpld))) fr) ->
  rw_cells asegs m (fr + 32) (d32_fcells w h dw r1 g1 b1 r2 g2 b2 rv gv bv p) ->
  acc asegs m (fr + 176) 4 -> acc asegs m (fr + 192) 4 -> acc asegs m (fr + 208) 4 ->
  evt asegs (d32_row_exit (Z_to_bv 64 sa) gp tp t2 s0 (Z_to_bv 64 sa) (Z_to_bv 64 (fr + 192)) (Z_to_bv 64 (fr + 208)) (Z_to_bv 64 (fr + 160))
               (Z_to_bv 64 (fr + 176)) (Z_to_bv 64 (fr + 128)) (Z_to_bv 64 (fr + 144)) t3 t4 t5 t6 F fc
               m lo sa fr datas datad wpls wpld w h ws c16 c24 c32 c40 l80 (Z_to_bv 64 (datad + 4 * (i * wpld))) l88 i dw r1 g1 b1 r2 g2 b2 p)
    (MS (mkR ra (Z_to_bv 64 sa) gp tp t0 t1 t2 s0 (Z_to_bv 64 sa) a0 a1 a2 (Z_to_bv 64 SHB) a4 a5 a6 a7
             (Z_to_bv 64 (fr + 192)) (Z_to_bv 64 (fr + 208)) (Z_to_bv 64 (fr + 160)) (Z_to_bv 64 (datas + 4 * (i * wpls + j)))
             (Z_to_bv 64 (fr + 176)) (Z_to_bv 64 j) (Z_to_bv 64 j) (Z_to_bv 64 (datas + 4 * (i * wpls + j)))
             (Z_to_bv 64 (fr + 128)) (Z_to_bv 64 (fr + 144)) t3 t4 t5 t6)
        F (Z_to_bv 64 0xa1198) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 F fc m lo sa fr datas datad wpls wpld w h ws wd
    c16 c24 c32 c40 l80 l88 i dw r1 g1 b1 r2 g2 b2 rv gv bv p
    HK HJ HK1 HI GEO MI ST G1 G2 UAS UASL ACCS UA UAL ACCD SL FA ARV AGV ABV.
  { lia. }
  pose proof GEO as (HW & WS & WD & WPLS & WPLD & HH & SH & DH & S0 & S8 & SHI & SSH & SSEG & D0 & D8 & DHI & DSH & DSEG & SEP
                     & FR0 & FR8 & FRSEG & FRSH & FRD & FRS & FRLO & DLO & SLO & LOH & LOS & SA8 & SAHI).
  assert (NS : i * wpls + wpls <= wpls * h) by (clear - HI WPLS; nia).
  assert (NS0 : 0 <= i * wpls) by (clear - HI WPLS; nia).
  assert (ND : i * wpld + wpld <= wpld * h) by (clear - HI WPLD; nia).
  assert (ND0 : 0 <= i * wpld) by (clear - HI WPLD; nia).
  assert (JD : 0 <= j / 32 < wpld) by (clear - HJ HK WD HW; Z.div_mod_to_equations; lia).
  unfold d32_slots in SL. unfold d32_fcells in FA.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl (D32_W datad (4 * (wpld * h)) sa fr) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  assert (CONT : forall (ra' t0' t1' a0' a1' a2' a4' a5' a6' a7' : word) (mm : mem) (wd' : list word) (rv' gv' bv' : word),
    munch (D32_W datad (4 * (wpld * h)) sa fr) m mm -> wmono asegs m mm -> mem_inv asegs mm -> stk asegs mm lo sa ->
    ro_cells asegs mm 931248 [C8 (Z_to_bv 64 979384)] -> ro_cells asegs mm 979384 [C8 (Z_to_bv 64 2147450880)] ->
    u32arr asegs mm datas ws -> acc asegs mm datas (4 * (wpls * h)) ->
    u32arr asegs mm datad wd' -> Z.of_nat (length wd') = wpld * h -> acc asegs mm datad (4 * (wpld * h)) ->
    rw_cells asegs mm (sa + 16)
      [C8 c16; C8 c24; C8 c32; C8 c40; C8 (Z_to_bv 64 wpld); C8 (Z_to_bv 64 datad); C8 (Z_to_bv 64 (4 * wpls)); C8 (Z_to_bv 64 (fr + 48));
       C8 l80; C8 (Z_to_bv 64 l88); C8 (Z_to_bv 64 i); C8 (Z_to_bv 64 (datad + 4 * (i * wpld)));
       C8 (Z_to_bv 64 (fr + 112)); C8 (Z_to_bv 64 (fr + 96)); C8 (Z_to_bv 64 (fr + 80)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 (fr + 32))] ->
    rw_cells asegs mm (fr + 32) (d32_fcells w h dw r1 g1 b1 r2 g2 b2 rv' gv' bv' p) ->
    acc asegs mm (fr + 176) 4 -> acc asegs mm (fr + 192) 4 -> acc asegs mm (fr + 208) 4 ->
    evt asegs (d32_row_exit (Z_to_bv 64 sa) gp tp t2 s0 (Z_to_bv 64 sa) (Z_to_bv 64 (fr + 192)) (Z_to_bv 64 (fr + 208)) (Z_to_bv 64 (fr + 160))
               (Z_to_bv 64 (fr + 176)) (Z_to_bv 64 (fr + 128)) (Z_to_bv 64 (fr + 144)) t3 t4 t5 t6 F fc
               m lo sa fr datas datad wpls wpld w h ws c16 c24 c32 c40 l80 (Z_to_bv 64 (datad + 4 * (i * wpld))) l88 i dw r1 g1 b1 r2 g2 b2 p)
      (MS (mkR ra' (Z_to_bv 64 sa) gp tp t0' t1' t2 s0 (Z_to_bv 64 sa) a0' a1' a2' (Z_to_bv 64 2147450880) a4' a5' a6' a7'
             (Z_to_bv 64 (fr + 192)) (Z_to_bv 64 (fr + 208)) (Z_to_bv 64 (fr + 160)) (Z_to_bv 64 (datas + 4 * (i * wpls + j)))
             (Z_to_bv 64 (fr + 176)) (Z_to_bv 64 j) (Z_to_bv 64 j) (Z_to_bv 64 (datas + 4 * (i * wpls + j)))
             (Z_to_bv 64 (fr + 128)) (Z_to_bv 64 (fr + 144)) t3 t4 t5 t6)
          F (Z_to_bv 64 0xa117c) fc None mm (seg_rom asegs))).
  { intros ra' t0' t1' a0' a1' a2' a4' a5' a6' a7' mm wd' rv' gv' bv' MU1 WM1 MI1 ST1 G11 G21 UAS1 ACCS1 UA1 UAL1 ACCD1 SL1 FA1 ARV1 AGV1 ABV1.
    clear MI ST G1 G2 UAS ACCS UA UAL ACCD SL FA ARV AGV ABV MU WM.
    unfold d32_fcells in FA1.
    lwalk [0xa1198; 0xa10f8]. sx32_fix.
    replace (datas + 4 * (i * wpls + j) + 4) with (datas + 4 * (i * wpls + (j + 1))) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w) by lia. rewrite EJ in *.
      brT. apply evt_done. unfold d32_row_exit, d32_slots, d32_fcells, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB.
      do 14 eexists. exists mm, wd', rv', gv', bv'. split; [reflexivity|].
      repeat (split; [assumption|]). assumption.
    - brF.
      eapply evt_cut.
      + eapply (IH (j + 1)) with (ws := ws) (wd := wd') (h := h) (lo := lo) (l88 := l88) (c16 := c16) (c24 := c24) (c32 := c32) (c40 := c40) (l80 := l80)
                                 (dw := dw) (r1 := r1) (g1 := g1) (b1 := b1) (r2 := r2) (g2 := g2) (b2 := b2) (rv := rv') (gv := gv') (bv := bv') (p := p);
          try eassumption; try lia.
      + intros ms' PO. apply evt_done. unfold d32_row_exit in PO |- *.
        destruct PO as (ra'' & t0'' & t1'' & a0'' & a1'' & a2'' & a4'' & a5'' & a6'' & a7'' & s5'' & s7'' & s8'' & s9'' & m' & wd'' & rv'' & gv'' & bv'' & E & MU' & WM' & R).
        exists ra'', t0'', t1'', a0'', a1'', a2'', a4'', a5'', a6'', a7'', s5'', s7'', s8'', s9'', m', wd'', rv'', gv'', bv''.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R]. }
  (* [comment removed for export] *)
  lwalk [0xa11a8; 0xa12c8].
  destruct (u32arr_nth ws (i * wpls + j) ltac:(lia)) as (wv & NTH).
  pose proof (u32arr_read asegs m datas ws (i * wpls + j) wv _ UAS NTH ltac:(lia) eq_refl) as R.
  lstep. clear R.
  park_disj. unfold parked in FRD, FRS.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  lwalk [0xa11bc; 0x96658; 0x9666c; 0x96680].
  (* [comment removed for export] *)
  lwalk [0xa1204].
  gen_reg 10. gen_reg 11. gen_reg 12. gen_reg 13. gen_reg 14. gen_reg 15. gen_reg 16. gen_reg 17. gen_reg 5. gen_reg 6.
  lwalk [0xa1274; 0xa125c].
  gen_reg 10. gen_reg 11. gen_reg 12. gen_reg 13. gen_reg 14. gen_reg 15. gen_reg 16.
  lwalk [0xa1288].
  gen_reg 10. gen_reg 11.
  lwalk [0xa117c; 0xa128c; 0xa1574].
  (* [comment removed for export] *)
  brfork B1; [solve [eapply CONT; eassumption]|].
  lwalk [0xa1168; 0xa1574].
  (* [comment removed for export] *)
  rewrite !(srliw_idx j 32) by lia.
  replace (datad + 4 * (i * wpld) + j / 32 * 4) with (datad + 4 * (i * wpld + j / 32)) by lia.
  rewrite (Z.mod_small (datad + 4 * (i * wpld + j / 32)) 18446744073709551616) by lia.
  unfold parked in DSH, DSEG.
  lwalk [0xa1168; 0xa1574].
  lazymatch goal with UAx : u32arr asegs ?mm datad ?wdx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (u32arr_nth wdx (i * wpld + j / 32) ltac:(lia)) as (dv & NTHD);
    pose proof (u32arr_read asegs mm datad wdx (i * wpld + j / 32) dv _ UAx NTHD ltac:(lia) eq_refl) as R end.
  lstep. clear R.
  lwalk [0xa1178].
  unfold parked in SEP.
  arr_sw datad (i * wpld + j / 32) (datad + 4 * (i * wpld + j / 32)).
  eapply CONT; eassumption.
Qed.

(* [comment removed for export] *)
Definition d32_exit (sp gp tp t2 s0 s1 s2 s3 s4 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo sa fr datas datad wpls wpld w h : Z) (ws : list word) (c16 c24 c32 c40 : word)
    (dw r1 g1 b1 r2 g2 b2 : word) (p : list (list byte)) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' a0' a1' a2' a4' a5' a6' a7' s5' s7' s8' s9' : word) (m' : mem) (wd' : list word) (rv' gv' bv' l80' l104' : word)
                    (l88' i' : Z),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' (Z_to_bv 64 SHB) a4' a5' a6' a7'
                  s2 s3 s4 s5' s6 s7' s8' s9' s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa1518) fc None m' (seg_rom asegs)
    /\ munch (D32_W datad (4 * (wpld * h)) sa fr) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo sa
    /\ ro_cells asegs m' g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)]
    /\ ro_cells asegs m' g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)]
    /\ u32arr asegs m' datas ws /\ acc asegs m' datas (4 * (wpls * h))
    /\ u32arr asegs m' datad wd' /\ Z.of_nat (length wd') = wpld * h /\ acc asegs m' datad (4 * (wpld * h))
    /\ rw_cells asegs m' (sa + 16) (d32_slots c16 c24 c32 c40 wpld datad wpls l80' l88' i' l104' fr)
    /\ rw_cells asegs m' (fr + 32) (d32_fcells w h dw r1 g1 b1 r2 g2 b2 rv' gv' bv' p)
    /\ acc asegs m' (fr + 176) 4 /\ acc asegs m' (fr + 192) 4 /\ acc asegs m' (fr + 208) 4.

Lemma discr32_rows : forall (k : nat) (i : Z)
    (ra gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 : word) F fc (m : mem)
    (lo sa fr datas datad wpls wpld w h : Z) (ws wd : list word) (c16 c24 c32 c40 l80 l104 : word)
    (dw r1 g1 b1 r2 g2 b2 rv gv bv : word) (p : list (list byte)),
  Z.of_nat k = h - i -> 0 <= i -> (1 <= k)%nat -> d32_geom lo sa fr datas datad wpls wpld w h ->
  mem_inv asegs m -> stk asegs m lo sa ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  u32arr asegs m datas ws -> Z.of_nat (length ws) = wpls * h -> acc asegs m datas (4 * (wpls * h)) ->
  u32arr asegs m datad wd -> Z.of_nat (length wd) = wpld * h -> acc asegs m datad (4 * (wpld * h)) ->
  rw_cells asegs m (sa + 16) (d32_slots c16 c24 c32 c40 wpld datad wpls l80 (datas + 4 * (i * wpls)) i l104 fr) ->
  rw_cells asegs m (fr + 32) (d32_fcells w h dw r1 g1 b1 r2 g2 b2 rv gv bv p) ->
  acc asegs m (fr + 176) 4 -> acc asegs m (fr + 192) 4 -> acc asegs m (fr + 208) 4 ->
  evt asegs (d32_exit (Z_to_bv 64 sa) gp tp t2 s0 (Z_to_bv 64 sa) (Z_to_bv 64 (fr + 192)) (Z_to_bv 64 (fr + 208)) (Z_to_bv 64 (fr + 160))
               (Z_to_bv 64 (fr + 176)) (Z_to_bv 64 (fr + 128)) (Z_to_bv 64 (fr + 144)) t3 t4 t5 t6 F fc
               m lo sa fr datas datad wpls wpld w h ws c16 c24 c32 c40 dw r1 g1 b1 r2 g2 b2 p)
    (MS (mkR ra (Z_to_bv 64 sa) gp tp t0 t1 t2 s0 (Z_to_bv 64 sa) a0 a1 a2 (Z_to_bv 64 SHB) a4 a5 a6 a7
             (Z_to_bv 64 (fr + 192)) (Z_to_bv 64 (fr + 208)) (Z_to_bv 64 (fr + 160)) s5
             (Z_to_bv 64 (fr + 176)) s7 s8 (Z_to_bv 64 (datas + 4 * (i * wpls)))
             (Z_to_bv 64 (fr + 128)) (Z_to_bv 64 (fr + 144)) t3 t4 t5 t6)
        F (Z_to_bv 64 0xa1128) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 F fc m lo sa fr datas datad wpls wpld w h ws wd
    c16 c24 c32 c40 l80 l104 dw r1 g1 b1 r2 g2 b2 rv gv bv p
    HK HI HK1 GEO MI ST G1 G2 UAS UASL ACCS UA UAL ACCD SL FA ARV AGV ABV.
  { lia. }
  pose proof GEO as (HW & WS & WD & WPLS & WPLD & HH & SH & DH & S0 & S8 & SHI & SSH & SSEG & D0 & D8 & DHI & DSH & DSEG & SEP
                     & FR0 & FR8 & FRSEG & FRSH & FRD & FRS & FRLO & DLO & SLO & LOH & LOS & SA8 & SAHI).
  assert (NS0 : 0 <= i * wpls) by (clear - HI WPLS; nia).
  assert (ND0 : 0 <= i * wpld <= 2^24) by (clear - HI HK HH WPLD DH; nia).
  unfold d32_slots in SL. unfold d32_fcells in FA.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl (D32_W datad (4 * (wpld * h)) sa fr) m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj. unfold parked in FRD, FRS.
  lwalk [0xa1198; 0xa10f8].
  rewrite (sx32_small w) by lia.
  brF.
  lwalk [0xa1198; 0xa10f8].
  (* [comment removed for export] *)
  replace (datad + i * wpld * 4) with (datad + 4 * (i * wpld)) in * by (clear; lia).
  assert (Q1 : Z.of_nat (Z.to_nat w) = w - 0) by (clear - HW; lia).
  assert (Q3 : (1 <= Z.to_nat w)%nat) by (clear - HW; lia).
  assert (Q4 : 0 <= i < h) by (clear - HI HK; lia).
  eapply evt_cut.
  { lazymatch goal with MIx : mem_inv asegs ?mm, STx : stk asegs ?mm lo sa, G1x : ro_cells asegs ?mm 931248 _, G2x : ro_cells asegs ?mm 979384 _,
        UASx : u32arr asegs ?mm datas ws, ACCSx : acc asegs ?mm datas _, UAx : u32arr asegs ?mm datad ?wdx, ACCDx : acc asegs ?mm datad _,
        SLx : rw_cells asegs ?mm (sa + 16) _, FAx : rw_cells asegs ?mm (fr + 32) _,
        ARVx : acc asegs ?mm (fr + 176) 4, AGVx : acc asegs ?mm (fr + 192) 4, ABVx : acc asegs ?mm (fr + 208) 4
        |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      epose proof (discr32_pixels (Z.to_nat w) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm lo sa fr datas datad wpls wpld w h ws wdx
                     c16 c24 c32 c40 _ (datas + 4 * (i * wpls)) i dw r1 g1 b1 r2 g2 b2 rv gv bv p
                     Q1 ltac:(lia) Q3 Q4 GEO MIx STx G1x G2x UASx UASL ACCSx UAx UAL ACCDx SLx FAx ARVx AGVx ABVx) as ZR end.
    unfold SHB in ZR.
    replace (datas + 4 * (i * wpls + 0)) with (datas + 4 * (i * wpls)) in ZR by (clear; lia).
    exact ZR. }
  intros ms' PO. unfold d32_row_exit in PO.
  destruct PO as (ra' & t0' & t1' & a0' & a1' & a2' & a4' & a5' & a6' & a7' & s5' & s7' & s8' & s9' & m' & wd' & rv' & gv' & bv' & -> & MU' & WM' & MI' & ST'
                  & G1' & G2' & UAS' & ACCS' & UA' & UAL' & ACCD' & SL' & FA' & ARV' & AGV' & ABV').
  lazymatch type of MU' with munch _ ?mo _ =>
    lazymatch goal with MUo : munch _ m mo, WMo : wmono asegs m mo |- _ =>
      pose proof (munch_trans _ _ _ _ MUo MU') as MUc; pose proof (wmono_trans asegs _ _ _ WMo WM') as WMc; clear MUo WMo MU' WM' end;
    repeat match goal with
    | H : rw_cells asegs mo _ _ |- _ => clear H | H : u32arr asegs mo _ _ |- _ => clear H | H : acc asegs mo _ _ |- _ => clear H
    | H : ro_cells asegs mo _ _ |- _ => clear H | H : stk asegs mo _ _ |- _ => clear H | H : mem_inv asegs mo |- _ => clear H end end.
  unfold d32_slots, d32_fcells, SHB, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  lwalk [0xa1128; 0xa1518].
  rewrite (sx32_small h) by lia.
  replace (datas + 4 * (i * wpls) + 4 * wpls) with (datas + 4 * ((i + 1) * wpls)) in * by (clear; lia).
  destruct k as [|k].
  - assert (EI : i + 1 = h) by lia. rewrite EI in *.
    brT. apply evt_done. unfold d32_exit, d32_slots, d32_fcells, SHB, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address.
    do 14 eexists. lazymatch goal with |- exists (m' : mem), _ => idtac end.
    eexists. exists wd', rv', gv', bv'. do 4 eexists.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
    repeat (split; [eassumption|]). eassumption.
  - brF.
    eapply evt_cut.
    + eapply (IH (i + 1)) with (ws := ws) (wd := wd') (w := w) (lo := lo) (dw := dw) (r1 := r1) (g1 := g1) (b1 := b1) (r2 := r2) (g2 := g2) (b2 := b2)
                               (rv := rv') (gv := gv') (bv := bv') (p := p) (c16 := c16) (c24 := c24) (c32 := c32) (c40 := c40);
        try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold d32_exit in PO |- *.
      destruct PO as (ra'' & t0'' & t1'' & a0'' & a1'' & a2'' & a4'' & a5'' & a6'' & a7'' & s5'' & s7'' & s8'' & s9'' & m'' & wd'' & rv'' & gv'' & bv'' & l80'' & l104'' & l88'' & i'' & E & MU'' & WM'' & R).
      exists ra'', t0'', t1'', a0'', a1'', a2'', a4'', a5'', a6'', a7'', s5'', s7'', s8'', s9'', m'', wd'', rv'', gv'', bv'', l80'', l104'', l88'', i''.
      split; [exact E|].
      lazymatch goal with MUx : munch _ m ?mx, WMx : wmono asegs m ?mx |- _ =>
        split; [exact (munch_trans _ _ _ _ MUx MU'')|]; split; [exact (wmono_trans asegs _ _ _ WMx WM'')| exact R] end.
Qed.
