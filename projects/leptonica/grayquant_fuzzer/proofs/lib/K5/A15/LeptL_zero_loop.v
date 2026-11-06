(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


Notation ZERO_W pe := [(pe, pe + 4)]%Z (only parsing).

(* [comment removed for export] *)
Definition zero_exit (ra sp gp tp s2 s3 s4 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (pe wpl h : Z)
    : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' (Z_to_bv 64 h) (Z_to_bv 64 wpl) a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 (Z_to_bv 64 SHB) (Z_to_bv 64 (pe / 8 + SHB)) (Z_to_bv 64 pe) s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0xa18c0) (frm_clear fc) None m' (seg_rom asegs)
    /\ munch (ZERO_W pe) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' pe [C4 y].

(* [comment removed for export] *)
Definition zero_words_next (ra sp gp tp s2 s3 s4 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (data wpl h pe wd fw eb i : Z) : machine_state -> Prop :=
  fun ms' => exists (a3' t4' t5' t6' : word),
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (32 - eb)) (Z_to_bv 64 fw) (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 h) (Z_to_bv 64 wpl)
                  (Z_to_bv 64 pe) (Z_to_bv 64 data) (Z_to_bv 64 (data + 4 * (i * wpl + fw))) a3'
                  (Z_to_bv 64 i) (Z_to_bv 64 wd) (Z_to_bv 64 32) (Z_to_bv 64 eb)
                  s2 s3 s4 (Z_to_bv 64 SHB) (Z_to_bv 64 (pe / 8 + SHB)) (Z_to_bv 64 pe) s8 s9 s10 s11
                  (Z_to_bv 64 (data + 4 * (i * wpl))) t4' t5' t6')
             F (Z_to_bv 64 0xa17cc) (frm_clear fc) None m (seg_rom asegs).

Lemma zero_words : forall (k : nat) (j : Z)
    (ra sp gp tp s2 s3 s4 s8 s9 s10 s11 t5 t6 : word) F fc (m : mem) (data wpl h pe wd fw eb i c : Z) (bs : list byte) (x : word),
  Z.of_nat k = fw - j -> c = fw - j -> 0 <= j -> (1 <= k)%nat -> fw <= wpl -> 0 <= i < h -> 0 < wpl <= 2^20 -> 0 < h <= 2^20 ->
  0 < data -> data mod 8 = 0 -> data + 4 * (wpl * h) <= 2^47 -> (data + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  0 < pe -> pe mod 4 = 0 -> pe + 4 <= 2^47 -> (pe + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= pe) ->
  bytes_at asegs m data bs -> Z.of_nat (length bs) = 4 * (wpl * h) -> rw_cells asegs m pe [C4 x] ->
  acc asegs m data (4 * (wpl * h)) -> acc asegs m pe 4 -> mem_inv asegs m ->
  evt asegs (fun ms' => zero_words_next ra sp gp tp s2 s3 s4 s8 s9 s10 s11 F fc m data wpl h pe wd fw eb i ms'
                        \/ zero_exit ra sp gp tp s2 s3 s4 s8 s9 s10 s11 F fc m pe wpl h ms')
    (MS (mkR ra sp gp tp (Z_to_bv 64 (32 - eb)) (Z_to_bv 64 fw) (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 h) (Z_to_bv 64 wpl)
             (Z_to_bv 64 pe) (Z_to_bv 64 data) (Z_to_bv 64 (data + 4 * (i * wpl + j))) (Z_to_bv 64 (data + 4 * (i * wpl + j)))
             (Z_to_bv 64 i) (Z_to_bv 64 wd) (Z_to_bv 64 32) (Z_to_bv 64 eb)
             s2 s3 s4 (Z_to_bv 64 SHB) (Z_to_bv 64 (pe / 8 + SHB)) (Z_to_bv 64 pe) s8 s9 s10 s11
             (Z_to_bv 64 (data + 4 * (i * wpl))) (Z_to_bv 64 c) t5 t6)
        F (Z_to_bv 64 0xa1790) (frm_clear fc) None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp s2 s3 s4 s8 s9 s10 s11 t5 t6 F fc m data wpl h pe wd fw eb i c bs x
    HK -> HJ HK1 FW HI WPL HH D0 D8 DHI DSH P0 P4 PHI PSH HB HBL PEC ACCD ACCP MI.
  { lia. }
  assert (NL : i * wpl + wpl <= wpl * h) by nia.
  assert (NL0 : 0 <= i * wpl) by nia.
  pose proof (munch_refl (ZERO_W pe) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk (@nil Z).
  destruct (bytes_at_read4w m data bs (4 * (i * wpl + j)) HB ltac:(lia) ltac:(lia)) as (wv & R).
  lstep. clear R.
  lwalk (@nil Z).
  brfork NZ.
  - (* [comment removed for export] *)
    lwalk [0xa18c0].
    apply evt_done. right. unfold zero_exit. do 16 eexists. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. eassumption.
  - lwalk [0xa1790; 0xa17cc]. swrap32_fix.
    replace (data + 4 * (i * wpl + j) + 4) with (data + 4 * (i * wpl + (j + 1))) by lia.
    replace (fw - j + -1) with (fw - (j + 1)) by lia.
    destruct k as [|k].
    + assert (EJ : j + 1 = fw) by lia. rewrite EJ in *. rewrite Z.sub_diag.
      brF. lwalk [0xa17cc].
      apply evt_done. left. unfold zero_words_next. do 4 eexists. reflexivity.
    + brT.
      eapply evt_mono; [eapply (IH (j + 1)) with (bs := bs) (x := x); try eassumption; try reflexivity; try lia|].
      cbv beta. intros ms' P. exact P.
Qed.

(* [comment removed for export] *)
Lemma zero_rows : forall (k : nat) (i : Z)
    (ra sp gp tp a2 a3 s2 s3 s4 s8 s9 s10 s11 t4 t5 t6 : word) F fc (m : mem) (data wpl h pe wd fw eb : Z) (bs : list byte) (x : word),
  Z.of_nat k = h - i -> 0 <= i -> (1 <= k)%nat ->
  0 <= wd < 2^31 -> 0 <= eb < 32 -> (wd < 32 -> fw = 0) -> (32 <= wd -> 1 <= fw) -> fw <= wpl -> (eb <> 0 -> fw + 1 <= wpl) ->
  0 < wpl <= 2^20 -> 0 < h <= 2^20 -> wpl * h <= 2^24 ->
  0 < data -> data mod 8 = 0 -> data + 4 * (wpl * h) <= 2^47 -> (data + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  0 < pe -> pe mod 4 = 0 -> pe + 4 <= 2^47 -> (pe + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= pe) ->
  bytes_at asegs m data bs -> Z.of_nat (length bs) = 4 * (wpl * h) -> rw_cells asegs m pe [C4 x] ->
  acc asegs m data (4 * (wpl * h)) -> acc asegs m pe 4 -> mem_inv asegs m ->
  evt asegs (zero_exit ra sp gp tp s2 s3 s4 s8 s9 s10 s11 F fc m pe wpl h)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (32 - eb)) (Z_to_bv 64 fw) (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 h) (Z_to_bv 64 wpl)
             (Z_to_bv 64 pe) (Z_to_bv 64 data) a2 a3
             (Z_to_bv 64 i) (Z_to_bv 64 wd) (Z_to_bv 64 32) (Z_to_bv 64 eb)
             s2 s3 s4 (Z_to_bv 64 SHB) (Z_to_bv 64 (pe / 8 + SHB)) (Z_to_bv 64 pe) s8 s9 s10 s11
             (Z_to_bv 64 (data + 4 * (i * wpl))) t4 t5 t6)
        F (Z_to_bv 64 0xa1778) (frm_clear fc) None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp a2 a3 s2 s3 s4 s8 s9 s10 s11 t4 t5 t6 F fc m data wpl h pe wd fw eb bs x
    HK HI HK1 WD EB FW0 FW1 FW FWE WPL HH WH D0 D8 DHI DSH P0 P4 PHI PSH HB HBL PEC ACCD ACCP MI.
  { lia. }
  assert (NL : i * wpl + wpl <= wpl * h) by nia.
  assert (NL0 : 0 <= i * wpl) by nia.
  pose proof (munch_refl (ZERO_W pe) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  assert (ROWEND : forall (a2' a3' t4' t5' t6' : word),
    evt asegs (zero_exit ra sp gp tp s2 s3 s4 s8 s9 s10 s11 F fc m pe wpl h)
      (MS (mkR ra sp gp tp (Z_to_bv 64 (32 - eb)) (Z_to_bv 64 fw) (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 h) (Z_to_bv 64 wpl)
               (Z_to_bv 64 pe) (Z_to_bv 64 data) a2' a3'
               (Z_to_bv 64 i) (Z_to_bv 64 wd) (Z_to_bv 64 32) (Z_to_bv 64 eb)
               s2 s3 s4 (Z_to_bv 64 SHB) (Z_to_bv 64 (pe / 8 + SHB)) (Z_to_bv 64 pe) s8 s9 s10 s11
               (Z_to_bv 64 (data + 4 * (i * wpl))) t4' t5' t6')
          F (Z_to_bv 64 0xa17ec) (frm_clear fc) None m (seg_rom asegs))).
  { intros. lwalk [0xa1778; 0xa18c0].
    replace (data + 4 * (i * wpl) + wpl * 4) with (data + 4 * ((i + 1) * wpl)) by lia.
    destruct k as [|k].
    - assert (EI : i + 1 = h) by lia. rewrite EI in *.
      brF. lwalk [0xa18c0].
      apply evt_done. unfold zero_exit. do 16 eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact PEC.
    - brT. eapply (IH (i + 1)) with (bs := bs) (x := x); try eassumption; try lia. }
  (* [comment removed for export] *)
  assert (TAIL : forall (a3' t4' t5' t6' : word),
    evt asegs (zero_exit ra sp gp tp s2 s3 s4 s8 s9 s10 s11 F fc m pe wpl h)
      (MS (mkR ra sp gp tp (Z_to_bv 64 (32 - eb)) (Z_to_bv 64 fw) (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 h) (Z_to_bv 64 wpl)
               (Z_to_bv 64 pe) (Z_to_bv 64 data) (Z_to_bv 64 (data + 4 * (i * wpl + fw))) a3'
               (Z_to_bv 64 i) (Z_to_bv 64 wd) (Z_to_bv 64 32) (Z_to_bv 64 eb)
               s2 s3 s4 (Z_to_bv 64 SHB) (Z_to_bv 64 (pe / 8 + SHB)) (Z_to_bv 64 pe) s8 s9 s10 s11
               (Z_to_bv 64 (data + 4 * (i * wpl))) t4' t5' t6')
          F (Z_to_bv 64 0xa17cc) (frm_clear fc) None m (seg_rom asegs))).
  { intros. lwalk (@nil Z).
    destruct (Z.eq_dec eb 0) as [E0|EN].
    - brT. apply ROWEND.
    - brF. lwalk (@nil Z).
      destruct (bytes_at_read4w m data bs (4 * (i * wpl + fw)) HB ltac:(lia) ltac:(lia)) as (wv & R).
      lstep. clear R.
      lwalk (@nil Z).
      brfork NZ.
      + lwalk [0xa18c0].
        apply evt_done. unfold zero_exit. do 16 eexists. eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. eassumption.
      + apply ROWEND. }
  lwalk (@nil Z).
  destruct (Z.ltb_spec wd 32) as [WLT|WGE].
  - (* [comment removed for export] *)
    brT. rewrite (FW0 WLT) in *.
    replace (data + i * wpl * 4) with (data + 4 * (i * wpl + 0)) by lia.
    apply TAIL.
  - brF. lwalk [0xa1790].
    replace (data + i * wpl * 4) with (data + 4 * (i * wpl + 0)) by lia.
    replace (Z_to_bv 64 (data + 4 * (i * wpl))) with (Z_to_bv 64 (data + 4 * (i * wpl + 0))) at 1 by (f_equal; lia).
    eapply evt_cut.
    + eapply (zero_words (Z.to_nat fw) 0) with (bs := bs) (x := x) (wd := wd) (eb := eb) (h := h); try eassumption; try lia.
    + cbv beta. intros ms' [P|P].
      * destruct P as (a3' & t4' & t5' & t6' & ->). apply TAIL.
      * apply evt_done. exact P.
Qed.
