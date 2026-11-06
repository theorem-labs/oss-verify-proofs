(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Pm_selloop_defs PmL_sel_loop.
Import ListNotations.
Open Scope Z_scope.

Theorem sel_rows_ok : sel_rows_stmt.
Proof.
  unfold sel_rows_stmt.
  intros ra sp gp tp t1 t2 s0 a0 a1 a7 s2 s5 s9 s10 s11 t4 F fc m s1v fr data w h d wpl idx c40 bs
    HD HW HH HWPL HRS HIDX D0 D16 DHI DSH DSEG UA UAL ACC FR0 FR64 FRHI FRD S0 S16 SHI SD CW CH CX1 CIDX CSP MI.
  assert (DR : 1 <= d <= 8) by (cbn [In] in HD; lia).
  assert (WPL : 0 < wpl <= 2^20) by (subst wpl; clear - HW DR; split; [apply Z.div_str_pos; nia| apply Z.div_le_upper_bound; nia]).
  assert (GEO : sel_geo data (4 * (wpl * h)) fr s1v).
  { unfold sel_geo. repeat split; first [assumption | lia | (Z.div_mod_to_equations; lia)]. }
  assert (COMMON : forall RP : Z -> Z -> mem -> Prop, sel_row_stmt RP d -> RP data (4 * (wpl * h)) m ->
    evt asegs
      (sel_exit sp gp tp (Z_to_bv 64 2) s0 (Z_to_bv 64 s1v) (Z_to_bv 64 85) (Z_to_bv 64 400) (Z_to_bv 64 3) (Z_to_bv 64 1)
                s2 (Z_to_bv 64 2147450880) (Z_to_bv 64 d) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48)) (Z_to_bv 64 399) s9
                (Z_to_bv 64 4) (Z_to_bv 64 wpl) (Z_to_bv 64 8) F fc m data (4 * (wpl * h)))
      (MS (mkR ra sp gp tp (Z_to_bv 64 2) t1 t2 s0 (Z_to_bv 64 s1v) a0 a1 (Z_to_bv 64 35) (Z_to_bv 64 85) (Z_to_bv 64 400)
               (Z_to_bv 64 3) (Z_to_bv 64 1) a7 s2 (Z_to_bv 64 2147450880) (Z_to_bv 64 d) s5 (Z_to_bv 64 (fr + 32))
               (Z_to_bv 64 (fr + 48)) (Z_to_bv 64 399) s9 s10 s11 (Z_to_bv 64 4) t4 (Z_to_bv 64 wpl) (Z_to_bv 64 8))
          F (Z_to_bv 64 SEL_HEAD) fc None m (seg_rom asegs))).
  { intros RP ROW RPm.
    eapply evt_mono.
    - eapply (sel_rows_gen RP d ROW (Z.to_nat 50) 35) with (m0 := m) (w := w) (h := h) (x1 := 278) (idx := idx) (c40 := c40)
               (sidx := Z_to_bv 64 2) (wpl := wpl) (rsz := 4 * (wpl * h)) (y2p1 := 85) (x2p1 := 400) (data := data) (fr := fr) (s1v := s1v);
        try eassumption; try lia; try reflexivity.
      + apply munch_refl.
      + apply wmono_refl.
      + unfold sel_inv. repeat (split; [assumption|]). assumption.
    - intros ms' (ra' & t1' & t2' & a0' & a1' & a2' & a7' & s5' & s10' & s11' & t4' & m' & -> & MU' & WM' & INV').
      unfold sel_exit. exists ra', t1', t2', a0', a1', a2', a7', s5', s10', s11', t4', m'.
      split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. destruct INV' as (_ & _ & MI' & _). exact MI'. }
  cbn [In] in HD. destruct HD as [<-|[<-|[<-|[<-|[]]]]].
  - apply (COMMON rp32 sel_row1). destruct (u8arr_u32arr m data bs (wpl * h) UA UAL) as (ws & UW & UWL). exists ws. split; [exact UW| lia].
  - apply (COMMON rp32 sel_row2). destruct (u8arr_u32arr m data bs (wpl * h) UA UAL) as (ws & UW & UWL). exists ws. split; [exact UW| lia].
  - apply (COMMON rp32 sel_row4). destruct (u8arr_u32arr m data bs (wpl * h) UA UAL) as (ws & UW & UWL). exists ws. split; [exact UW| lia].
  - apply (COMMON rp8 sel_row8). exists bs. split; [exact UA| exact UAL].
Qed.
