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

(* [comment removed for export] *)
Definition thr_pix_exit (ra sp gp tp t1 t2 s0 a1 a4 s2 s3 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (datat datad qtab wpl w h i pw sb : Z) (wt qws : list word) : machine_state -> Prop :=
  fun ms' => exists (t0' a0' a6' a7' : word) (m' : mem) (wd' : list word),
    ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 (Z_to_bv 64 sb) a0' a1 (Z_to_bv 64 w) (Z_to_bv 64 (datat + 4 * (i * wpl) + w)) a4 (Z_to_bv 64 (datad + 4 * (i * wpl) + w)) a6' a7'
                  s2 s3 s4 (Z_to_bv 64 pw) s6 s7 s8 s9 s10 (Z_to_bv 64 SHB) t3 t4 t5 t6)
             F (Z_to_bv 64 0xa002c) fc None m' (seg_rom asegs)
    /\ munch [(datad, datad + 4 * (wpl * h))] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datat wt /\ acc asegs m' datat (4 * (wpl * h))
    /\ u32arr asegs m' qtab qws /\ acc asegs m' qtab 1024
    /\ u32arr asegs m' datad wd' /\ Z.of_nat (length wd') = wpl * h /\ acc asegs m' datad (4 * (wpl * h))
    /\ rw_cells asegs m' pw [C4 (Z_to_bv 64 w)] /\ rw_cells asegs m' (sb + 144) [C8 (Z_to_bv 64 qtab)].

Lemma thr_pix : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) F fc (m : mem)
    (datat datad qtab wpl w h i pw sb : Z) (wt wd qws : list word),
  Z.of_nat k = w - j -> 0 <= j -> (1 <= k)%nat -> 0 < w <= 20000 -> wpl = (w * 8 + 31) / 32 ->
  0 < h <= 20000 -> 0 <= i < h -> 4 * (wpl * h) <= 0x4000000 ->
  0 < datat -> datat mod 8 = 0 -> datat + 4 * (wpl * h) <= 2^47 -> (datat + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datat) ->
  (datat + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= datat) ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * (wpl * h) <= 2^47 -> (datad + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= datad) ->
  0 < qtab -> qtab mod 8 = 0 -> qtab + 1024 <= 2^47 -> (qtab + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= qtab) -> (qtab + 1024 <= 0x10000 \/ SEGTOP_A <= qtab) ->
  (datat + 4 * (wpl * h) <= datad \/ datad + 4 * (wpl * h) <= datat) ->
  (qtab + 1024 <= datad \/ datad + 4 * (wpl * h) <= qtab) ->
  0 < pw -> pw + 4 <= 2^47 -> (pw + 4 <= datad \/ datad + 4 * (wpl * h) <= pw) ->
  0 < sb -> sb mod 8 = 0 -> sb + 152 <= 2^47 -> (sb + 152 <= datad \/ datad + 4 * (wpl * h) <= sb + 144) ->
  u32arr asegs m datat wt -> Z.of_nat (length wt) = wpl * h -> acc asegs m datat (4 * (wpl * h)) ->
  u32arr asegs m datad wd -> Z.of_nat (length wd) = wpl * h -> acc asegs m datad (4 * (wpl * h)) ->
  u32arr asegs m qtab qws -> Z.of_nat (length qws) = 256 -> acc asegs m qtab 1024 ->
  rw_cells asegs m pw [C4 (Z_to_bv 64 w)] -> rw_cells asegs m (sb + 144) [C8 (Z_to_bv 64 qtab)] -> mem_inv asegs m ->
  evt asegs (thr_pix_exit ra sp gp tp t1 t2 s0 a1 a4 s2 s3 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m datat datad qtab wpl w h i pw sb wt qws)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 sb) a0 a1 (Z_to_bv 64 j) (Z_to_bv 64 (datat + 4 * (i * wpl) + j)) a4
             (Z_to_bv 64 (datad + 4 * (i * wpl) + j)) a6 a7 s2 s3 s4 (Z_to_bv 64 pw) s6 s7 s8 s9 s10 (Z_to_bv 64 SHB) t3 t4 t5 t6)
        F (Z_to_bv 64 0xa0054) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m datat datad qtab wpl w h i pw sb wt wd qws
    HK HJ HK1 HW EWPL HH HI RSB S0 S8 SHI SSH SSEG D0 D8 DHI DSH DSEG G0 G8 GHI GSH GSEG SEP SEPG W0 WHI WSEP B0 B8 BHI BSEP
    UAS UASL ACCS UA UAL ACCD UAGM UAGL ACCG WC QC MI.
  { lia. }
  assert (WPL4 : w <= 4 * wpl /\ 4 * wpl <= w + 3 /\ 0 < wpl <= 5000) by (rewrite EWPL; clear - HW; Z.div_mod_to_equations; lia).
  assert (NS : i * wpl + wpl <= wpl * h) by (clear - HI WPL4; nia).
  assert (NS0 : 0 <= i * wpl) by (clear - HI WPL4; nia).
  assert (JW : 0 <= j < w) by (clear - HK HJ HK1; lia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl [(datad, datad + 4 * (wpl * h))] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (lxor3_eq (datat + 4 * (i * wpl) + j)) as LXS.
  pose proof (lxor3_eq (datad + 4 * (i * wpl) + j)) as LXD.
  pose proof (proj1 UAS) as HBS.
  assert (HBL : Z.of_nat (length (u32s wt)) = 4 * (wpl * h)) by (rewrite u32s_length; clear - UASL; lia).
  park_disj.
  idtac "MARK pix start".
  lwalk [0xa0068; 0xa002c].
  destruct (bytes_at_read1 m datat (u32s wt) (Z.lxor (datat + 4 * (i * wpl) + j) 3 - datat) HBS ltac:(lia)) as (vb & R).
  replace (datat + (Z.lxor (datat + 4 * (i * wpl) + j) 3 - datat)) with (Z.lxor (datat + 4 * (i * wpl) + j) 3) in R by lia.
  lstep. clear R.
  idtac "MARK pix byte read".
  lwalk [0xa0094; 0xa002c].
  assert (VBR : 0 <= bv_unsigned vb < 256) by (pose proof (bv_unsigned_in_range 8 vb) as Q; unfold bv_modulus in Q; change (2 ^ Z.of_N 8) with 256 in Q; exact Q).
  replace (bv_unsigned vb * 4) with (4 * bv_unsigned vb) by (clear; lia).
  set (ix := bv_unsigned vb) in *.
  rewrite !(Z.mod_small (qtab + 4 * ix) 18446744073709551616) by (clear - VBR G0 GHI; lia).
  lwalk [0xa0094; 0xa002c].
  destruct (u32arr_nth qws ix ltac:(lia)) as (q1 & NTH1).
  pose proof (u32arr_read asegs m qtab qws ix q1 _ UAGM NTH1 ltac:(lia) eq_refl) as R.
  lstep. clear R.
  idtac "MARK pix table read".
  lwalk [0xa00a0; 0xa002c].
  lazymatch goal with U : u32arr asegs ?mm datad ?wsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_u8arr mm datad wsx U) as UA8;
    assert (UAL8 : Z.of_nat (length (u32s wsx)) = 4 * (wpl * h)) by (rewrite u32s_length; clear - UAL; lia);
    clear U UAL end.
  unfold sx32.
  unpark DSH. unpark SEP. unpark SEPG. unpark WSEP. unpark BSEP.
  replace (Z.lxor (datad + 4 * (i * wpl) + j) 3) with (datad + (4 * (i * wpl) + j + 3 - 2 * ((datad + 4 * (i * wpl) + j) mod 4))) by (clear - LXD; lia).
  arr_sb datad (4 * (i * wpl) + j + 3 - 2 * ((datad + 4 * (i * wpl) + j) mod 4)) (datad + (4 * (i * wpl) + j + 3 - 2 * ((datad + 4 * (i * wpl) + j) mod 4))).
  park DSH. park SEP. park SEPG. park WSEP. park BSEP.
  lazymatch goal with U : u8arr asegs ?mm datad ?bsx |- _ =>
    destruct (u8arr_u32arr mm datad bsx (wpl * h) U UAL8) as (wd1 & UA & UAL); clear U UAL8 end.
  idtac "MARK pix byte stored".
  lwalk [0xa0054; 0xa00b4; 0xa002c].
  lstep.
  rewrite !(sx32_small w) by (clear - HW; lia).
  destruct k as [|k].
  - assert (EJ : j + 1 = w) by lia.
    brF. lwalk [0xa002c].
    apply evt_done. unfold thr_pix_exit.
    do 4 eexists. lazymatch goal with UAx : u32arr asegs ?mm datad ?wdx |- _ => exists mm, wdx end.
    replace (datat + 4 * (i * wpl) + j + 1) with (datat + 4 * (i * wpl) + w) by (clear - EJ; lia).
    replace (datad + 4 * (i * wpl) + j + 1) with (datad + 4 * (i * wpl) + w) by (clear - EJ; lia).
    replace (j + 1) with w by (clear - EJ; lia).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. repeat (split; [assumption|]). eassumption.
  - assert (LT : j + 1 < w) by lia.
    brT.
    replace (datat + 4 * (i * wpl) + j + 1) with (datat + 4 * (i * wpl) + (j + 1)) by (clear; lia).
    replace (datad + 4 * (i * wpl) + j + 1) with (datad + 4 * (i * wpl) + (j + 1)) by (clear; lia).
    eapply evt_cut.
    + eapply (IH (j + 1)) with (wt := wt) (qws := qws) (h := h) (w := w) (qtab := qtab) (sb := sb) (pw := pw) (datat := datat) (datad := datad) (wpl := wpl) (i := i); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold thr_pix_exit in PO |- *.
      destruct PO as (t0' & a0' & a6' & a7' & m' & wd' & E & MU' & WM' & R).
      exists t0', a0', a6', a7', m', wd'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Ltac row_xport H MU WM side :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
  lazymatch type of H with rw_cells _ ma ?A ?cs =>
    let D := fresh "DJ" in
    assert (D : disjoint_from W A (Z.of_nat (cells_size cs))) by (cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; side);
    apply (fun h => rw_cells_transport asegs W ma mb A cs h MU WM D) in H; clear D
  end end.

(* [comment removed for export] *)
Definition thr_rows_exit (ra sp gp tp t1 t2 s0 s2 s3 s6 s7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (datat datad qtab wpl w h pw ph sb : Z) (wt qws : list word) : machine_state -> Prop :=
  fun ms' => exists (t0' a0' a2' a3' a5' a6' a7' s4' s8' : word) (m' : mem) (wd' : list word),
    ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 (Z_to_bv 64 sb) a0' (Z_to_bv 64 h) a2' a3' (Z_to_bv 64 (4 * wpl)) a5' a6' a7'
                  s2 s3 s4' (Z_to_bv 64 pw) s6 s7 s8' (Z_to_bv 64 (4 * wpl)) (Z_to_bv 64 ph) (Z_to_bv 64 SHB) t3 t4 t5 t6)
             F (Z_to_bv 64 0xa00e4) fc None m' (seg_rom asegs)
    /\ munch [(datad, datad + 4 * (wpl * h))] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datat wt /\ acc asegs m' datat (4 * (wpl * h))
    /\ u32arr asegs m' qtab qws /\ acc asegs m' qtab 1024
    /\ u32arr asegs m' datad wd' /\ Z.of_nat (length wd') = wpl * h /\ acc asegs m' datad (4 * (wpl * h))
    /\ rw_cells asegs m' pw [C4 (Z_to_bv 64 w)] /\ rw_cells asegs m' ph [C4 (Z_to_bv 64 h)] /\ rw_cells asegs m' (sb + 144) [C8 (Z_to_bv 64 qtab)].

Lemma thr_rows : forall (k : nat) (i : Z)
    (ra sp gp tp t0 t1 t2 s0 a0 a2 a3 a5 a6 a7 s2 s3 s6 s7 t3 t4 t5 t6 : word) F fc (m : mem)
    (datat datad qtab wpl w h pw ph sb : Z) (wt wd qws : list word),
  Z.of_nat k = h - i -> 0 <= i -> (1 <= k)%nat -> 0 < w <= 20000 -> wpl = (w * 8 + 31) / 32 ->
  0 < h <= 20000 -> 4 * (wpl * h) <= 0x4000000 ->
  0 < datat -> datat mod 8 = 0 -> datat + 4 * (wpl * h) <= 2^47 -> (datat + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datat) ->
  (datat + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= datat) ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * (wpl * h) <= 2^47 -> (datad + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= datad) ->
  0 < qtab -> qtab mod 8 = 0 -> qtab + 1024 <= 2^47 -> (qtab + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= qtab) -> (qtab + 1024 <= 0x10000 \/ SEGTOP_A <= qtab) ->
  (datat + 4 * (wpl * h) <= datad \/ datad + 4 * (wpl * h) <= datat) ->
  (qtab + 1024 <= datad \/ datad + 4 * (wpl * h) <= qtab) ->
  0 < pw -> pw + 4 <= 2^47 -> (pw + 4 <= datad \/ datad + 4 * (wpl * h) <= pw) ->
  0 < ph -> ph + 4 <= 2^47 -> (ph + 4 <= datad \/ datad + 4 * (wpl * h) <= ph) ->
  0 < sb -> sb mod 8 = 0 -> sb + 152 <= 2^47 -> (sb + 152 <= datad \/ datad + 4 * (wpl * h) <= sb + 144) ->
  u32arr asegs m datat wt -> Z.of_nat (length wt) = wpl * h -> acc asegs m datat (4 * (wpl * h)) ->
  u32arr asegs m datad wd -> Z.of_nat (length wd) = wpl * h -> acc asegs m datad (4 * (wpl * h)) ->
  u32arr asegs m qtab qws -> Z.of_nat (length qws) = 256 -> acc asegs m qtab 1024 ->
  rw_cells asegs m pw [C4 (Z_to_bv 64 w)] -> rw_cells asegs m ph [C4 (Z_to_bv 64 h)] -> rw_cells asegs m (sb + 144) [C8 (Z_to_bv 64 qtab)] -> mem_inv asegs m ->
  evt asegs (thr_rows_exit ra sp gp tp t1 t2 s0 s2 s3 s6 s7 t3 t4 t5 t6 F fc m datat datad qtab wpl w h pw ph sb wt qws)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 sb) a0 (Z_to_bv 64 i) a2 a3 (Z_to_bv 64 (4 * wpl)) a5 a6 a7
             s2 s3 (Z_to_bv 64 (datat + 4 * (i * wpl))) (Z_to_bv 64 pw) s6 s7 (Z_to_bv 64 (datad + 4 * (i * wpl))) (Z_to_bv 64 (4 * wpl)) (Z_to_bv 64 ph) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        F (Z_to_bv 64 0xa0040) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp t0 t1 t2 s0 a0 a2 a3 a5 a6 a7 s2 s3 s6 s7 t3 t4 t5 t6 F fc m datat datad qtab wpl w h pw ph sb wt wd qws
    HK HI HK1 HW EWPL HH RSB S0 S8 SHI SSH SSEG D0 D8 DHI DSH DSEG G0 G8 GHI GSH GSEG SEP SEPG W0 WHI WSEP P0 PHI PSEP B0 B8 BHI BSEP
    UAS UASL ACCS UA UAL ACCD UAGM UAGL ACCG WC HC QC MI.
  { lia. }
  assert (WPL4 : w <= 4 * wpl /\ 4 * wpl <= w + 3 /\ 0 < wpl <= 5000) by (rewrite EWPL; clear - HW; Z.div_mod_to_equations; lia).
  assert (HIH : 0 <= i < h) by (clear - HK HI HK1; lia).
  assert (NS : i * wpl + wpl <= wpl * h) by (clear - HIH WPL4; nia).
  assert (NS0 : 0 <= i * wpl) by (clear - HIH WPL4; nia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl [(datad, datad + 4 * (wpl * h))] m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  idtac "MARK rows start".
  (* [comment removed for export] *)
  lwalk [0xa0054; 0xa002c; 0xa00e4].
  rewrite !(sx32_small w) by (clear - HW; lia).
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota| symmetry] end.
  2:{ change z64 with (Z_to_bv 64 0). rewrite bv_lts_zero_l. rewrite unsigned_lit by (clear - HW; lia). clear - HW.
      replace (0 <? w) with true by (symmetry; apply Z.ltb_lt; lia). replace (w <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  lwalk [0xa0054; 0xa002c; 0xa00e4].
  idtac "MARK rows at pix".
  (* [comment removed for export] *)
  assert (Q1 : Z.of_nat (Z.to_nat w) = w - 0) by (clear - HW; lia).
  assert (Q3 : (1 <= Z.to_nat w)%nat) by (clear - HW; lia).
  lazymatch goal with |- evt _ _ (MS _ ?FF _ ?ffc None ?mm _) =>
    epose proof (thr_pix (Z.to_nat w) 0 ra sp gp tp _ t1 t2 s0 _ (Z_to_bv 64 i) (Z_to_bv 64 (4 * wpl)) _ _ s2 s3 (Z_to_bv 64 (datat + 4 * (i * wpl))) s6 s7
                   (Z_to_bv 64 (datad + 4 * (i * wpl))) (Z_to_bv 64 (4 * wpl)) (Z_to_bv 64 ph) t3 t4 t5 t6 FF ffc mm datat datad qtab wpl w h i pw sb wt wd qws
                   Q1 ltac:(clear; lia) Q3 HW EWPL HH HIH RSB S0 S8 SHI ltac:(unpark SSH; exact SSH) ltac:(unpark SSEG; unfold SEGTOP_A; exact SSEG)
                   D0 D8 DHI ltac:(unpark DSH; exact DSH) ltac:(unpark DSEG; unfold SEGTOP_A; exact DSEG)
                   G0 G8 GHI ltac:(unpark GSH; exact GSH) ltac:(unpark GSEG; unfold SEGTOP_A; exact GSEG)
                   ltac:(unpark SEP; exact SEP) ltac:(unpark SEPG; exact SEPG) W0 WHI ltac:(unpark WSEP; exact WSEP) B0 B8 BHI ltac:(unpark BSEP; exact BSEP)
                   UAS UASL ACCS UA UAL ACCD UAGM UAGL ACCG WC QC MI) as ZR end.
  unfold SHB in ZR.
  replace (datat + 4 * (i * wpl) + 0) with (datat + 4 * (i * wpl)) in ZR by (clear; lia).
  replace (datad + 4 * (i * wpl) + 0) with (datad + 4 * (i * wpl)) in ZR by (clear; lia).
  eapply evt_cut; [exact ZR|]. clear ZR.
  idtac "MARK rows pix applied".
  intros ms1 PO1. unfold thr_pix_exit in PO1.
  destruct PO1 as (t0a & a0a & a6a & a7a & ma & wda & -> & MUa & WMa & MIa & UASa & ACCSa & UAGMa & ACCGa & UAa & UALa & ACCDa & WCa & QCa).
  row_xport HC MUa WMa ltac:(repeat split; try exact I; clear - PSEP; unpark PSEP; lia).
  clear UAS ACCS UAGM ACCG UA UAL ACCD WC QC MI.
  (* [comment removed for export] *)
  lwalk [0xa0040; 0xa003c; 0xa00e4]. lstep.
  rewrite !(sx32_small h) by (clear - HH; lia).
  replace (datat + 4 * (i * wpl) + 4 * wpl) with (datat + 4 * ((i + 1) * wpl)) by (clear; lia).
  replace (datad + 4 * (i * wpl) + 4 * wpl) with (datad + 4 * ((i + 1) * wpl)) by (clear; lia).
  idtac "MARK rows branch".
  destruct k as [|k].
  - assert (EI : i + 1 = h) by lia.
    brT. lwalk [0xa00e4].
    apply evt_done. unfold thr_rows_exit.
    rewrite EI.
    do 9 eexists. exists ma, wda.
    split; [reflexivity|]. split; [exact MUa|]. split; [exact WMa|]. repeat (split; [assumption|]). assumption.
  - assert (LT : i + 1 < h) by lia.
    brF.
    eapply evt_cut.
    + eapply (IH (i + 1)) with (wt := wt) (qws := qws) (h := h) (w := w) (qtab := qtab) (sb := sb) (pw := pw) (ph := ph) (datat := datat) (datad := datad) (wpl := wpl);
        try eassumption; try lia; try (unpark_all; unfold SEGTOP_A; assumption).
    + intros ms' PO. apply evt_done. unfold thr_rows_exit in PO |- *.
      destruct PO as (t0' & a0' & a2' & a3' & a5' & a6' & a7' & s4' & s8' & m' & wd' & E & MU' & WM' & R).
      exists t0', a0', a2', a3', a5', a6', a7', s4', s8', m', wd'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MUa MU')|]. split; [exact (wmono_trans asegs _ _ _ WMa WM')| exact R].
Qed.
