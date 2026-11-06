(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptB_guard LeptL_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation PAD_W data n := [(data, data + n)]%Z (only parsing).

Definition padbits_exit (ra sp gp tp s0 s1 a3 a6 s2 s3 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (data wpl h fw ha : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 wpl) a1' a2' a3 (Z_to_bv 64 1) (Z_to_bv 64 (4 * fw)) a6 (Z_to_bv 64 0)
                  s2 s3 s4 (Z_to_bv 64 data) s6 s7 s8 s9 s10 (Z_to_bv 64 SHB) t3 t4 t5 t6)
             F (Z_to_bv 64 0x972d8) (frm_clear fc) None m' (seg_rom asegs)
    /\ munch (PAD_W data (4 * (wpl * h))) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' data ws' /\ Z.of_nat (length ws') = wpl * h /\ rw_cells asegs m' ha [C4 (Z_to_bv 64 h)].

Lemma padbits_rows : forall (k : nat) (i : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a6 s2 s3 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) F fc (m : mem)
    (data wpl h fw ha : Z) (ws : list word),
  Z.of_nat k = h - i -> 0 <= i -> (1 <= k)%nat -> 0 <= fw < wpl -> 0 < wpl <= 2^20 -> 0 < h <= 2^20 -> wpl * h <= 2^24 ->
  0 < data -> data mod 8 = 0 -> data + 4 * (wpl * h) <= 2^47 -> (data + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  (data + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= data) ->
  0 < ha -> ha + 4 <= 2^47 -> (ha + 4 <= data \/ data + 4 * (wpl * h) <= ha) ->
  u32arr asegs m data ws -> Z.of_nat (length ws) = wpl * h -> acc asegs m data (4 * (wpl * h)) ->
  rw_cells asegs m ha [C4 (Z_to_bv 64 h)] -> mem_inv asegs m ->
  evt asegs (padbits_exit ra sp gp tp s0 s1 a3 a6 s2 s3 (Z_to_bv 64 ha) s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m data wpl h fw ha)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 wpl) a1 (Z_to_bv 64 i) a3 (Z_to_bv 64 1) (Z_to_bv 64 (4 * fw)) a6 (Z_to_bv 64 0)
             s2 s3 (Z_to_bv 64 ha) (Z_to_bv 64 data) s6 s7 s8 s9 s10 (Z_to_bv 64 SHB) t3 t4 t5 t6)
        F (Z_to_bv 64 0x971ec) (frm_clear fc) None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a6 s2 s3 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m data wpl h fw ha ws
    HK HI HK1 FW WPL HH WH D0 D8 DHI DSH DSEG H0 HHI HSEP UA UAL ACC HC MI.
  { lia. }
  assert (NL : i * wpl + wpl <= wpl * h) by nia.
  assert (NL0 : 0 <= i * wpl) by nia.
  unfold SEGTOP_A in *.
  pose proof (munch_refl (PAD_W data (4 * (wpl * h))) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  assert (STORE : forall (t1' t2' : word),
    evt asegs (padbits_exit ra sp gp tp s0 s1 a3 a6 s2 s3 (Z_to_bv 64 ha) s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m data wpl h fw ha)
      (MS (mkR ra sp gp tp (Z_to_bv 64 ((data + 4 * (i * wpl + fw)) / 8)) t1' t2' s0 s1 (Z_to_bv 64 wpl) (Z_to_bv 64 (data + 4 * (i * wpl + fw))) (Z_to_bv 64 i)
               a3 (Z_to_bv 64 1) (Z_to_bv 64 (4 * fw)) a6 (Z_to_bv 64 0)
               s2 s3 (Z_to_bv 64 ha) (Z_to_bv 64 data) s6 s7 s8 s9 s10 (Z_to_bv 64 SHB) t3 t4 t5 t6)
          F (Z_to_bv 64 0x97284) (frm_clear fc) None m (seg_rom asegs))).
  { intros.
    gwalk [0x97290].
    arr_sw data (i * wpl + fw) (data + 4 * (i * wpl + fw)).
    gwalk [0x971ec; 0x972d8]. sx32_fix. swrap_fix.
    destruct k as [|k].
    - assert (EI : i + 1 = h) by lia. rewrite EI in *.
      brF. gwalk [0x972d8]. apply evt_done. unfold padbits_exit. do 5 eexists. exists m0, aws. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UA|]. split; [exact UAL| assumption].
    - brT.
      eapply evt_cut.
      + eapply (IH (i + 1)) with (ws := aws) (fw := fw); try eassumption; try lia.
      + intros ms' PO. apply evt_done. unfold padbits_exit in PO |- *.
        destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & m' & ws' & E & MU' & WM' & R).
        exists t0'', t1'', t2'', a1'', a2'', m', ws'.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R]. }
  gwalk [0x9723c].
  replace ((i * wpl + 0) mod 18446744073709551616 * 4 + data + 4 * fw) with (data + 4 * (i * wpl + fw)) by (rewrite Z.mod_small by nia; lia).
  gwalk (@nil Z).
  destruct (u32arr_nth ws (i * wpl + fw) ltac:(lia)) as (wv & NTH).
  pose proof (u32arr_read asegs m data ws (i * wpl + fw) wv _ UA NTH ltac:(lia) eq_refl) as R.
  brfork VAL.
  - (* [comment removed for export] *)
    gwalk [0x9727c]. lstep. clear R. gwalk [0x97284]. apply STORE.
  - (* [comment removed for export] *)
    gwalk [0x97260]. lstep. clear R. gwalk [0x97284]. apply STORE.
Qed.
