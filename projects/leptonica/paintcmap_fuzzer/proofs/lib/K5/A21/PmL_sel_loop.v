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
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition sel_inv (RP : Z -> Z -> mem -> Prop) (data rsz fr s1v w h x1 idx : Z) (c40 sidx : word) (m : mem) : Prop :=
  RP data rsz m /\ acc asegs m data rsz /\ mem_inv asegs m
  /\ rw_cells asegs m (fr + 32) [C4 (Z_to_bv 64 w)] /\ rw_cells asegs m (fr + 48) [C4 (Z_to_bv 64 h)]
  /\ rw_cells asegs m (fr + 64) [C4 (Z_to_bv 64 x1)] /\ rw_cells asegs m (fr + 128) [C4 (Z_to_bv 64 idx)]
  /\ rw_cells asegs m (s1v + 24) [C8 (Z_to_bv 64 data); C8 (Z_to_bv 64 (fr + 64)); C8 c40; C8 (Z_to_bv 64 (fr + 128)); C8 sidx].

(* [comment removed for export] *)
Definition sel_geo (data rsz fr s1v : Z) : Prop :=
  0 < data /\ data mod 8 = 0 /\ data + rsz <= 2^47 /\ (data + rsz <= 0x7fff7000 \/ 0x10007fff8000 <= data)
  /\ (data + rsz <= 0x10000 \/ SEGTOP_A <= data)
  /\ 0 < fr /\ fr mod 8 = 0 /\ fr + 256 <= 2^47 /\ (fr + 256 <= data \/ data + rsz <= fr)
  /\ 0 < s1v /\ s1v mod 8 = 0 /\ s1v + 64 <= 2^47 /\ data + rsz <= s1v.

(* [comment removed for export] *)
Definition sel_rowend (RP : Z -> Z -> mem -> Prop) (sp gp tp s0 s2 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem)
    (data rsz fr s1v w h x1 idx : Z) (c40 sidx : word) (d wpl i y2p1 x2p1 : Z) (ra s8 : word) : machine_state -> Prop :=
  fun ms' => exists (t1' t2' a0' a1' a7' s5' s10' s11' t4' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 2) t1' t2' s0 (Z_to_bv 64 s1v) a0' a1' (Z_to_bv 64 i) (Z_to_bv 64 y2p1) (Z_to_bv 64 x2p1)
                  (Z_to_bv 64 3) (Z_to_bv 64 1) a7' s2 (Z_to_bv 64 SHB) (Z_to_bv 64 d) s5' (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48))
                  s8 s9 s10' s11' (Z_to_bv 64 4) t4' (Z_to_bv 64 wpl) (Z_to_bv 64 8))
             F (Z_to_bv 64 0x935e8) fc None m' (seg_rom asegs)
    /\ munch [(data, data + rsz)] m0 m' /\ wmono asegs m0 m' /\ sel_inv RP data rsz fr s1v w h x1 idx c40 sidx m'.

(* [comment removed for export] *)
Definition sel_row_stmt (RP : Z -> Z -> mem -> Prop) (d : Z) : Prop :=
  forall (k : nat) (j : Z) (sp gp tp t1 t2 s0 a0 a1 s2 s5 s9 t4 : word) (s8 : word) F fc (m0 m : mem)
         (data rsz fr s1v w h x1 idx wpl li i y2p1 x2p1 : Z) (c40 sidx : word),
  Z.of_nat k = x2p1 - j -> 0 <= j -> (1 <= k)%nat -> x2p1 <= 2^20 ->
  0 < w <= 2^20 -> 0 <= idx < 2^31 -> (w * d + 31) / 32 <= wpl -> 0 <= li -> 4 * (li + wpl) <= rsz -> rsz <= 2^30 ->
  sel_geo data rsz fr s1v ->
  munch [(data, data + rsz)] m0 m -> wmono asegs m0 m -> sel_inv RP data rsz fr s1v w h x1 idx c40 sidx m ->
  evt asegs (sel_rowend RP sp gp tp s0 s2 s9 F fc m0 data rsz fr s1v w h x1 idx c40 sidx d wpl i y2p1 x2p1 (Z_to_bv 64 (data + 4 * li)) s8)
    (MS (mkR (Z_to_bv 64 (data + 4 * li)) sp gp tp (Z_to_bv 64 2) t1 t2 s0 (Z_to_bv 64 s1v) a0 a1 (Z_to_bv 64 i) (Z_to_bv 64 y2p1) (Z_to_bv 64 x2p1)
             (Z_to_bv 64 3) (Z_to_bv 64 1) (Z_to_bv 64 (2 * j)) s2 (Z_to_bv 64 SHB) (Z_to_bv 64 d) s5 (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48))
             s8 s9 (Z_to_bv 64 j) (Z_to_bv 64 (4 * j)) (Z_to_bv 64 4) t4 (Z_to_bv 64 wpl) (Z_to_bv 64 8))
        F (Z_to_bv 64 0x9363c) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition rp8 (data rsz : Z) (m : mem) : Prop := exists bs : list byte, u8arr asegs m data bs /\ Z.of_nat (length bs) = rsz.
Definition rp32 (data rsz : Z) (m : mem) : Prop := exists ws : list word, u32arr asegs m data ws /\ 4 * Z.of_nat (length ws) = rsz.

(* [comment removed for export] *)
Ltac sel_next_tac IH :=
  lwalk [0x9363c; 0x935e8]; swrap32_fix;
  lazymatch goal with |- context [Z_to_bv 64 (4 * ?j + 4)] =>
    replace (4 * j + 4) with (4 * (j + 1)) by lia; replace (2 * j + 2) with (2 * (j + 1)) by lia;
    lazymatch goal with
    | HK : Z.of_nat (S ?k) = ?x2p1 - j |- _ =>
        destruct k as [|k];
        [ replace (j + 1) with x2p1 by lia;
          brT; apply evt_done; unfold sel_rowend; do 9 eexists; eexists; split; [reflexivity|]; split; [eassumption|]; split; eassumption
        | brF; eapply (IH (j + 1)); try eassumption; try lia ]
    end
  end.

(* [comment removed for export] *)
Lemma sel_row8 : sel_row_stmt rp8 8.
Proof.
  unfold sel_row_stmt.
  induction k as [|k IH]; intros j sp gp tp t1 t2 s0 a0 a1 s2 s5 s9 t4 s8 F fc m0 m data rsz fr s1v w h x1 idx wpl li i y2p1 x2p1 c40 sidx
    HK HJ HK1 HX2 HW HIDX HWPL HLI HROW HRSZ GEO MU WM INV.
  { lia. }
  (* [comment removed for export] *)
  assert (NEXT : forall (t1' t2' a0' a1' s5' t4' : word) (m1 : mem),
    munch [(data, data + rsz)] m0 m1 -> wmono asegs m0 m1 -> sel_inv rp8 data rsz fr s1v w h x1 idx c40 sidx m1 ->
    evt asegs (sel_rowend rp8 sp gp tp s0 s2 s9 F fc m0 data rsz fr s1v w h x1 idx c40 sidx 8 wpl i y2p1 x2p1 (Z_to_bv 64 (data + 4 * li)) s8)
      (MS (mkR (Z_to_bv 64 (data + 4 * li)) sp gp tp (Z_to_bv 64 2) t1' t2' s0 (Z_to_bv 64 s1v) a0' a1' (Z_to_bv 64 i) (Z_to_bv 64 y2p1) (Z_to_bv 64 x2p1)
               (Z_to_bv 64 3) (Z_to_bv 64 1) (Z_to_bv 64 (2 * j)) s2 (Z_to_bv 64 SHB) (Z_to_bv 64 8) s5' (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48))
               s8 s9 (Z_to_bv 64 j) (Z_to_bv 64 (4 * j)) (Z_to_bv 64 4) t4' (Z_to_bv 64 wpl) (Z_to_bv 64 8))
          F (Z_to_bv 64 0x9362c) fc None m1 (seg_rom asegs))).
  { intros t1' t2' a0' a1' s5' t4' m1 MU1 WM1 INV1. clear MU WM INV. sel_next_tac IH. }
  pose proof GEO as (D0 & D8 & DHI & DSH & DSEG & FR0 & FR8 & FRHI & FRD & S0 & S8 & SHI & SD).
  pose proof INV as ((bs & UA & UAL) & ACC & MI & CW & CH & CX1 & CIDX & CSP).
  unfold SEGTOP_A in *.
  lwalk (@nil Z). sx32_fix.
  brfork JW.
  - (* [comment removed for export] *) apply NEXT; assumption.
  - rewrite !signed_lit64 in JW by lia.
    assert (W4 : w <= 4 * wpl) by (clear - HWPL; Z.div_mod_to_equations; lia).
    pose proof (lxor3_eq (data + 4 * li + j)) as LX.
    lwalk (@nil Z).
    (* [comment removed for export] *)
    set (o := Z.lxor (data + 4 * li + j) 3 - data).
    assert (HO : 0 <= o < rsz) by (unfold o; lia).
    replace (Z.lxor (data + 4 * li + j) 3) with (data + o) by (unfold o; lia).
    clearbody o. clear LX.
    pose proof UA as [HB _].
    destruct (bytes_at_read1 m data bs o HB ltac:(lia)) as (bv & R).
    lstep. clear R HB. lwalk (@nil Z).
    if_cases Hcmp; clear Hcmp; [apply NEXT; assumption|].
    lwalk (@nil Z). sx32_fix.
    arr_sb data o (data + o).
    apply NEXT; [exact MU| exact WM|].
    unfold sel_inv, rp8. split; [eexists; split; [exact UA| exact UAL]|]. repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Lemma sel_row4 : sel_row_stmt rp32 4.
Proof.
  unfold sel_row_stmt.
  induction k as [|k IH]; intros j sp gp tp t1 t2 s0 a0 a1 s2 s5 s9 t4 s8 F fc m0 m data rsz fr s1v w h x1 idx wpl li i y2p1 x2p1 c40 sidx
    HK HJ HK1 HX2 HW HIDX HWPL HLI HROW HRSZ GEO MU WM INV.
  { lia. }
  assert (NEXT : forall (t1' t2' a0' a1' s5' t4' : word) (m1 : mem),
    munch [(data, data + rsz)] m0 m1 -> wmono asegs m0 m1 -> sel_inv rp32 data rsz fr s1v w h x1 idx c40 sidx m1 ->
    evt asegs (sel_rowend rp32 sp gp tp s0 s2 s9 F fc m0 data rsz fr s1v w h x1 idx c40 sidx 4 wpl i y2p1 x2p1 (Z_to_bv 64 (data + 4 * li)) s8)
      (MS (mkR (Z_to_bv 64 (data + 4 * li)) sp gp tp (Z_to_bv 64 2) t1' t2' s0 (Z_to_bv 64 s1v) a0' a1' (Z_to_bv 64 i) (Z_to_bv 64 y2p1) (Z_to_bv 64 x2p1)
               (Z_to_bv 64 3) (Z_to_bv 64 1) (Z_to_bv 64 (2 * j)) s2 (Z_to_bv 64 SHB) (Z_to_bv 64 4) s5' (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48))
               s8 s9 (Z_to_bv 64 j) (Z_to_bv 64 (4 * j)) (Z_to_bv 64 4) t4' (Z_to_bv 64 wpl) (Z_to_bv 64 8))
          F (Z_to_bv 64 0x9362c) fc None m1 (seg_rom asegs))).
  { intros t1' t2' a0' a1' s5' t4' m1 MU1 WM1 INV1. clear MU WM INV. sel_next_tac IH. }
  pose proof GEO as (D0 & D8 & DHI & DSH & DSEG & FR0 & FR8 & FRHI & FRD & S0 & S8 & SHI & SD).
  pose proof INV as ((ws & UA & UAL4) & ACC & MI & CW & CH & CX1 & CIDX & CSP).
  assert (UAL : Z.of_nat (length ws) = rsz / 4) by (clear - UAL4; Z.div_mod_to_equations; lia).
  assert (R4 : rsz = 4 * (rsz / 4)) by (clear - UAL4; Z.div_mod_to_equations; lia).
  clear UAL4. set (nw := rsz / 4) in *. clearbody nw.
  unfold SEGTOP_A in *.
  lwalk (@nil Z). sx32_fix.
  brfork JW.
  - (* [comment removed for export] *) apply NEXT; assumption.
  - rewrite !signed_lit64 in JW by lia.
    assert (JQ : 0 <= j / 8 < wpl) by (clear - HWPL JW HJ; Z.div_mod_to_equations; lia).
    lwalk [0x9377c]. lstep. rewrite (srliw_idx j 8) by lia.
    set (q := j / 8) in *. clearbody q.
    lwalk (@nil Z).
    replace (data + 4 * li + q * 4) with (data + 4 * (li + q)) by lia.
    destruct (u32arr_nth ws (li + q) ltac:(lia)) as (wv & NTH).
    pose proof (u32arr_read asegs m data ws (li + q) wv _ UA NTH ltac:(lia) eq_refl) as R.
    lstep. clear R NTH.
    lwalk (@nil Z).
    if_cases Hcmp; clear Hcmp; [apply NEXT; assumption|].
    lwalk (@nil Z).
    arr_sw data (li + q) (data + 4 * (li + q)).
    lwalk [0x9362c].
    apply NEXT; [exact MU| exact WM|].
    unfold sel_inv, rp32. split; [eexists; split; [exact UA| lia]|]. repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Lemma sel_row2 : sel_row_stmt rp32 2.
Proof.
  unfold sel_row_stmt.
  induction k as [|k IH]; intros j sp gp tp t1 t2 s0 a0 a1 s2 s5 s9 t4 s8 F fc m0 m data rsz fr s1v w h x1 idx wpl li i y2p1 x2p1 c40 sidx
    HK HJ HK1 HX2 HW HIDX HWPL HLI HROW HRSZ GEO MU WM INV.
  { lia. }
  assert (NEXT : forall (t1' t2' a0' a1' s5' t4' : word) (m1 : mem),
    munch [(data, data + rsz)] m0 m1 -> wmono asegs m0 m1 -> sel_inv rp32 data rsz fr s1v w h x1 idx c40 sidx m1 ->
    evt asegs (sel_rowend rp32 sp gp tp s0 s2 s9 F fc m0 data rsz fr s1v w h x1 idx c40 sidx 2 wpl i y2p1 x2p1 (Z_to_bv 64 (data + 4 * li)) s8)
      (MS (mkR (Z_to_bv 64 (data + 4 * li)) sp gp tp (Z_to_bv 64 2) t1' t2' s0 (Z_to_bv 64 s1v) a0' a1' (Z_to_bv 64 i) (Z_to_bv 64 y2p1) (Z_to_bv 64 x2p1)
               (Z_to_bv 64 3) (Z_to_bv 64 1) (Z_to_bv 64 (2 * j)) s2 (Z_to_bv 64 SHB) (Z_to_bv 64 2) s5' (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48))
               s8 s9 (Z_to_bv 64 j) (Z_to_bv 64 (4 * j)) (Z_to_bv 64 4) t4' (Z_to_bv 64 wpl) (Z_to_bv 64 8))
          F (Z_to_bv 64 0x9362c) fc None m1 (seg_rom asegs))).
  { intros t1' t2' a0' a1' s5' t4' m1 MU1 WM1 INV1. clear MU WM INV. sel_next_tac IH. }
  pose proof GEO as (D0 & D8 & DHI & DSH & DSEG & FR0 & FR8 & FRHI & FRD & S0 & S8 & SHI & SD).
  pose proof INV as ((ws & UA & UAL4) & ACC & MI & CW & CH & CX1 & CIDX & CSP).
  assert (UAL : Z.of_nat (length ws) = rsz / 4) by (clear - UAL4; Z.div_mod_to_equations; lia).
  assert (R4 : rsz = 4 * (rsz / 4)) by (clear - UAL4; Z.div_mod_to_equations; lia).
  clear UAL4. set (nw := rsz / 4) in *. clearbody nw.
  unfold SEGTOP_A in *.
  lwalk (@nil Z). sx32_fix.
  brfork JW.
  - (* [comment removed for export] *) apply NEXT; assumption.
  - rewrite !signed_lit64 in JW by lia.
    assert (JQ : 0 <= j / 16 < wpl) by (clear - HWPL JW HJ; Z.div_mod_to_equations; lia).
    lwalk [0x93658]. lstep. rewrite (srliw_idx j 16) by lia.
    set (q := j / 16) in *. clearbody q.
    lwalk (@nil Z).
    replace (data + 4 * li + q * 4) with (data + 4 * (li + q)) by lia.
    destruct (u32arr_nth ws (li + q) ltac:(lia)) as (wv & NTH).
    pose proof (u32arr_read asegs m data ws (li + q) wv _ UA NTH ltac:(lia) eq_refl) as R.
    lstep. clear R NTH.
    lwalk (@nil Z).
    if_cases Hcmp; clear Hcmp; [apply NEXT; assumption|].
    lwalk (@nil Z).
    arr_sw data (li + q) (data + 4 * (li + q)).
    lwalk [0x9362c].
    apply NEXT; [exact MU| exact WM|].
    unfold sel_inv, rp32. split; [eexists; split; [exact UA| lia]|]. repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Lemma sel_row1 : sel_row_stmt rp32 1.
Proof.
  unfold sel_row_stmt.
  induction k as [|k IH]; intros j sp gp tp t1 t2 s0 a0 a1 s2 s5 s9 t4 s8 F fc m0 m data rsz fr s1v w h x1 idx wpl li i y2p1 x2p1 c40 sidx
    HK HJ HK1 HX2 HW HIDX HWPL HLI HROW HRSZ GEO MU WM INV.
  { lia. }
  assert (NEXT : forall (t1' t2' a0' a1' s5' t4' : word) (m1 : mem),
    munch [(data, data + rsz)] m0 m1 -> wmono asegs m0 m1 -> sel_inv rp32 data rsz fr s1v w h x1 idx c40 sidx m1 ->
    evt asegs (sel_rowend rp32 sp gp tp s0 s2 s9 F fc m0 data rsz fr s1v w h x1 idx c40 sidx 1 wpl i y2p1 x2p1 (Z_to_bv 64 (data + 4 * li)) s8)
      (MS (mkR (Z_to_bv 64 (data + 4 * li)) sp gp tp (Z_to_bv 64 2) t1' t2' s0 (Z_to_bv 64 s1v) a0' a1' (Z_to_bv 64 i) (Z_to_bv 64 y2p1) (Z_to_bv 64 x2p1)
               (Z_to_bv 64 3) (Z_to_bv 64 1) (Z_to_bv 64 (2 * j)) s2 (Z_to_bv 64 SHB) (Z_to_bv 64 1) s5' (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48))
               s8 s9 (Z_to_bv 64 j) (Z_to_bv 64 (4 * j)) (Z_to_bv 64 4) t4' (Z_to_bv 64 wpl) (Z_to_bv 64 8))
          F (Z_to_bv 64 0x9362c) fc None m1 (seg_rom asegs))).
  { intros t1' t2' a0' a1' s5' t4' m1 MU1 WM1 INV1. clear MU WM INV. sel_next_tac IH. }
  pose proof GEO as (D0 & D8 & DHI & DSH & DSEG & FR0 & FR8 & FRHI & FRD & S0 & S8 & SHI & SD).
  pose proof INV as ((ws & UA & UAL4) & ACC & MI & CW & CH & CX1 & CIDX & CSP).
  assert (UAL : Z.of_nat (length ws) = rsz / 4) by (clear - UAL4; Z.div_mod_to_equations; lia).
  assert (R4 : rsz = 4 * (rsz / 4)) by (clear - UAL4; Z.div_mod_to_equations; lia).
  clear UAL4. set (nw := rsz / 4) in *. clearbody nw.
  unfold SEGTOP_A in *.
  lwalk (@nil Z). sx32_fix.
  brfork JW.
  - (* [comment removed for export] *) apply NEXT; assumption.
  - rewrite !signed_lit64 in JW by lia.
    assert (JQ : 0 <= j / 32 < wpl) by (clear - HWPL JW HJ; Z.div_mod_to_equations; lia).
    lwalk [0x9371c]. lstep. rewrite (srliw_idx j 32) by lia.
    set (q := j / 32) in *. clearbody q.
    lwalk (@nil Z).
    replace (data + 4 * li + q * 4) with (data + 4 * (li + q)) by lia.
    destruct (u32arr_nth ws (li + q) ltac:(lia)) as (wv & NTH).
    pose proof (u32arr_read asegs m data ws (li + q) wv _ UA NTH ltac:(lia) eq_refl) as R.
    lstep. clear R NTH.
    lwalk (@nil Z).
    if_cases Hcmp; clear Hcmp; [apply NEXT; assumption|].
    lwalk (@nil Z). sx32_fix.
    brfork IDX0.
    + (* [comment removed for export] *)
      lwalk (@nil Z).
      arr_sw data (li + q) (data + 4 * (li + q)).
      lwalk [0x9362c].
      apply NEXT; [exact MU| exact WM|].
      unfold sel_inv, rp32. split; [eexists; split; [exact UA| lia]|]. repeat (split; [assumption|]). assumption.
    + (* [comment removed for export] *)
      lwalk (@nil Z).
      arr_sw data (li + q) (data + 4 * (li + q)).
      lwalk [0x9362c].
      apply NEXT; [exact MU| exact WM|].
      unfold sel_inv, rp32. split; [eexists; split; [exact UA| lia]|]. repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Definition sel_exit_g (RP : Z -> Z -> mem -> Prop) (sp gp tp s0 s2 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem)
    (data rsz fr s1v w h x1 idx : Z) (c40 sidx : word) (d wpl y2p1 x2p1 : Z) (s8 : word) : machine_state -> Prop :=
  fun ms' => exists (ra' t1' t2' a0' a1' a2' a7' s5' s10' s11' t4' : word) (m' : mem),
    ms' = MS (mkR ra' sp gp tp (Z_to_bv 64 2) t1' t2' s0 (Z_to_bv 64 s1v) a0' a1' a2' (Z_to_bv 64 y2p1) (Z_to_bv 64 x2p1)
                  (Z_to_bv 64 3) (Z_to_bv 64 1) a7' s2 (Z_to_bv 64 SHB) (Z_to_bv 64 d) s5' (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48))
                  s8 s9 s10' s11' (Z_to_bv 64 4) t4' (Z_to_bv 64 wpl) (Z_to_bv 64 8))
             F (Z_to_bv 64 0x935b8) fc None m' (seg_rom asegs)
    /\ munch [(data, data + rsz)] m0 m' /\ wmono asegs m0 m' /\ sel_inv RP data rsz fr s1v w h x1 idx c40 sidx m'.

Lemma sel_rows_gen : forall (RP : Z -> Z -> mem -> Prop) (d : Z), sel_row_stmt RP d ->
  forall (k : nat) (i : Z) (ra sp gp tp t1 t2 s0 a0 a1 a7 s2 s5 s9 s10 s11 t4 : word) F fc (m0 m : mem)
         (data rsz fr s1v w h x1 idx wpl y2p1 x2p1 : Z) (c40 sidx : word),
  Z.of_nat k = y2p1 - i -> 0 <= i -> (1 <= k)%nat -> y2p1 <= 2^20 ->
  0 <= x1 -> x1 < x2p1 -> x2p1 <= 2^20 ->
  0 < w <= 2^20 -> 0 <= idx < 2^31 -> (w * d + 31) / 32 <= wpl -> 0 < wpl <= 2^20 -> 0 < h <= 2^20 -> rsz = 4 * (wpl * h) -> rsz <= 2^30 ->
  sel_geo data rsz fr s1v ->
  munch [(data, data + rsz)] m0 m -> wmono asegs m0 m -> sel_inv RP data rsz fr s1v w h x1 idx c40 sidx m ->
  evt asegs (sel_exit_g RP sp gp tp s0 s2 s9 F fc m0 data rsz fr s1v w h x1 idx c40 sidx d wpl y2p1 x2p1 (Z_to_bv 64 (x2p1 - 1)))
    (MS (mkR ra sp gp tp (Z_to_bv 64 2) t1 t2 s0 (Z_to_bv 64 s1v) a0 a1 (Z_to_bv 64 i) (Z_to_bv 64 y2p1) (Z_to_bv 64 x2p1)
             (Z_to_bv 64 3) (Z_to_bv 64 1) a7 s2 (Z_to_bv 64 SHB) (Z_to_bv 64 d) s5 (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48))
             (Z_to_bv 64 (x2p1 - 1)) s9 s10 s11 (Z_to_bv 64 4) t4 (Z_to_bv 64 wpl) (Z_to_bv 64 8))
        F (Z_to_bv 64 0x935f4) fc None m (seg_rom asegs)).
Proof.
  intros RP d ROW.
  induction k as [|k IH]; intros i ra sp gp tp t1 t2 s0 a0 a1 a7 s2 s5 s9 s10 s11 t4 F fc m0 m data rsz fr s1v w h x1 idx wpl y2p1 x2p1 c40 sidx
    HK HI HK1 HY2 HX1 HX12 HX2 HW HIDX HWPL WPL HH HRS HRSZ GEO MU WM INV.
  { lia. }
  (* [comment removed for export] *)
  assert (CONT : forall (ra' t1' t2' a0' a1' a7' s5' s10' s11' t4' : word) (m1 : mem),
    munch [(data, data + rsz)] m0 m1 -> wmono asegs m0 m1 -> sel_inv RP data rsz fr s1v w h x1 idx c40 sidx m1 ->
    evt asegs (sel_exit_g RP sp gp tp s0 s2 s9 F fc m0 data rsz fr s1v w h x1 idx c40 sidx d wpl y2p1 x2p1 (Z_to_bv 64 (x2p1 - 1)))
      (MS (mkR ra' sp gp tp (Z_to_bv 64 2) t1' t2' s0 (Z_to_bv 64 s1v) a0' a1' (Z_to_bv 64 i) (Z_to_bv 64 y2p1) (Z_to_bv 64 x2p1)
               (Z_to_bv 64 3) (Z_to_bv 64 1) a7' s2 (Z_to_bv 64 SHB) (Z_to_bv 64 d) s5' (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48))
               (Z_to_bv 64 (x2p1 - 1)) s9 s10' s11' (Z_to_bv 64 4) t4' (Z_to_bv 64 wpl) (Z_to_bv 64 8))
          F (Z_to_bv 64 0x935e8) fc None m1 (seg_rom asegs))).
  { intros ra' t1' t2' a0' a1' a7' s5' s10' s11' t4' m1 MU1 WM1 INV1. clear MU WM INV.
    lwalk [0x935f4; 0x935b8]. swrap32_fix.
    destruct k as [|k].
    - replace (i + 1) with y2p1 by lia.
      brT. apply evt_done. unfold sel_exit_g. do 11 eexists. exists m1. split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1| exact INV1].
    - brF. eapply (IH (i + 1)); try eassumption; try lia. }
  pose proof GEO as (D0 & D8 & DHI & DSH & DSEG & FR0 & FR8 & FRHI & FRD & S0 & S8 & SHI & SD).
  pose proof INV as (RPm & ACC & MI & CW & CH & CX1 & CIDX & CSP).
  unfold SEGTOP_A in *.
  lwalk (@nil Z). sx32_fix.
  brfork IGE.
  - (* [comment removed for export] *) apply CONT; assumption.
  - rewrite !signed_lit64 in IGE by lia.
    lwalk [0x9363c]. sx32_fix. lwalk [0x9363c].
    assert (NL0 : 0 <= i * wpl) by nia.
    assert (NL : 4 * (i * wpl + wpl) <= rsz) by nia.
    rewrite (Z.mod_small (i * wpl)) by nia.
    replace (data + i * wpl * 4) with (data + 4 * (i * wpl)) by lia.
    replace (x1 * 2) with (2 * x1) by lia. replace (x1 * 4) with (4 * x1) by lia.
    eapply evt_cut.
    { eapply (ROW (Z.to_nat (x2p1 - x1)) x1) with (li := i * wpl) (m0 := m0) (w := w) (h := h) (x1 := x1) (idx := idx) (c40 := c40) (sidx := sidx);
        try eassumption; try lia. }
    intros ms' (t1' & t2' & a0' & a1' & a7' & s5' & s10' & s11' & t4' & m' & -> & MU' & WM' & INV').
    apply CONT; assumption.
Qed.
