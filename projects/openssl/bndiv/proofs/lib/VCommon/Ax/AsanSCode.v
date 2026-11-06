(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import
  PropExec CatSim CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg LibWritev LibWritevCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSBase AsanSWord AsanSMemchr AsanSRipA AsanWWritev AsanWSw AsanWStdio.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem memchr_sum_ck (segs : list Segment) (cfg : SpuriousCfg) (b cM cH : Z) :
  words_ok segs b MEMCHR_WORDS = true ->
  pair_ok segs b 0x58 13 13 cM = true -> pair_ok segs b 0x60 14 14 cH = true ->
  (0 <= cM < 2 ^ 40)%Z -> (0 <= cH < 2 ^ 40)%Z ->
  forall (ms : machine_state) (model : Model) (T : TSet) (s : word) (bs : list byte) (n : Z),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw b 0 -> m_halted model = None ->
  rg ms 10 = s -> rg ms 11 = w0 -> rg ms 12 = Z_to_bv 64 n ->
  cstr segs (ms_mem ms) s bs ->
  (forall j, (Z.of_nat (length bs) < j < WE s bs)%Z -> exists x, bat segs (ms_mem ms) (s + Z_to_bv 64 j) = Some x) ->
  (bv_unsigned s + WE s bs <= 2 ^ 64)%Z ->
  no_lazy model (bv_unsigned s) (bv_unsigned s + WE s bs) ->
  (Z.of_nat (length bs) + 8 <= n < 2 ^ 64)%Z ->
  cell8 segs (ms_mem ms) cM Mc -> cell8 segs (ms_mem ms) cH Hc ->
  no_lazy model cM (cM + 8) -> no_lazy model cH (cH + 8) ->
  (bv_unsigned (rg ms 1) mod 2 = 0)%Z ->
  (forall ms', FR MCLOB ms ms' -> ms_pc_val ms' = rg ms 1 -> rg ms' 10 = s + Z_to_bv 64 (Z.of_nat (length bs)) ->
     realizes_cfg segs cfg (mkCfg ms' model) T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros HW HPM HPH HcMr HcHr.
  destruct (pair_ok_sound _ _ _ _ _ _ HPM ltac:(lia)) as (wam & wlm & iam & ilm & HFam & HEam & HDam & HFlm & HElm & HDlm & HAM).
  destruct (pair_ok_sound _ _ _ _ _ _ HPH ltac:(lia)) as (wah & wlh & iah & ilh & HFah & HEah & HDah & HFlh & HElh & HDlh & HAH).
  assert (Eam : Z_to_bv 32 (bv_unsigned wam) = wam) by apply Z_to_bv_bv_unsigned.
  assert (Elm : Z_to_bv 32 (bv_unsigned wlm) = wlm) by apply Z_to_bv_bv_unsigned.
  assert (Eah : Z_to_bv 32 (bv_unsigned wah) = wah) by apply Z_to_bv_bv_unsigned.
  assert (Elh : Z_to_bv 32 (bv_unsigned wlh) = wlh) by apply Z_to_bv_bv_unsigned.
  rewrite <- Eam in HFam, HEam, HDam. rewrite <- Elm in HFlm, HElm, HDlm.
  rewrite <- Eah in HFah, HEah, HDah. rewrite <- Elh in HFlh, HElh, HDlh.
  exact (memchr_sum segs cfg b cM cH (bv_unsigned wam) (bv_unsigned wlm) (bv_unsigned wah) (bv_unsigned wlh) iam iah ilm ilh HW
           HFam HFlm HFah HFlh HEam HElm HEah HElh HDam HDlm HDah HDlh HAM HAH ltac:(lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma swcode_ck (segs : list Segment) (b sr : Z) :
  words_ok segs b SW_WORDS = true -> words_ok segs sr SR_WORDS = true ->
  jal_ok segs b 0x8c 1 sr = true -> jal_ok segs b 0x114 1 sr = true ->
  (0 <= b /\ b + 0x200 <= 2 ^ 47 /\ 0 <= sr /\ sr + 0x40 <= 2 ^ 47 /\ b mod 4 = 0)%Z ->
  exists (wj1 wj2 : Z) (ij1 ij2 : bv 21), SWCode segs b sr wj1 wj2 ij1 ij2.
Proof.
  intros HW HR HJ1 HJ2 Hbnd.
  destruct (jal_ok_sound _ _ _ _ _ HJ1) as (w1 & i1 & HF1 & HE1 & HD1 & HT1).
  destruct (jal_ok_sound _ _ _ _ _ HJ2) as (w2 & i2 & HF2 & HE2 & HD2 & HT2).
  assert (E1 : Z_to_bv 32 (bv_unsigned w1) = w1) by apply Z_to_bv_bv_unsigned.
  assert (E2 : Z_to_bv 32 (bv_unsigned w2) = w2) by apply Z_to_bv_bv_unsigned.
  rewrite <- E1 in HF1, HE1, HD1. rewrite <- E2 in HF2, HE2, HD2.
  exists (bv_unsigned w1), (bv_unsigned w2), i1, i2.
  constructor; [exact HW | exact HR | exact HF1 | exact HE1 | exact HD1 | exact HT1 | exact HF2 | exact HE2 | exact HD2 | exact HT2 | exact Hbnd].
Qed.

Theorem stdio_write_loop_ck :
  forall (segs : list Segment) (cfg : SpuriousCfg) (b sr : Z),
  (exists (wj1 wj2 : Z) (ij1 ij2 : bv 21), SWCode segs b sr wj1 wj2 ij1 ij2) ->
  forall (ms : machine_state) (model : Model) (K : TSet) (fd f iovp : Z)
         (ents : list (word * word)) (bss : list (list byte)),
  ms_svc_pending ms = None -> ms_rom ms = seg_rom segs -> ms_pc_val ms = pcw b 0x88 ->
  m_halted model = None ->
  rg ms 17 = Z_to_bv 64 66 -> rg ms 10 = Z_to_bv 64 fd ->
  rg ms 11 = Z_to_bv 64 iovp -> rg ms 19 = Z_to_bv 64 iovp ->
  rg ms 12 = Z_to_bv 64 (Z.of_nat (length ents)) -> rg ms 18 = Z_to_bv 64 (Z.of_nat (length ents)) ->
  rg ms 22 = Z_to_bv 64 (iovs_total ents) -> rg ms 9 = Z_to_bv 64 f ->
  (length ents = 1 \/ length ents = 2)%nat -> (1 <= iovs_total ents <= 2 ^ 30)%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) -> (0 < fd < 2 ^ 31)%Z ->
  rdn segs (ms_mem ms) (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
  (0 <= f)%Z -> (f + 124 <= 2 ^ 47)%Z ->
  (0 <= iovp)%Z -> (iovp + 16 * Z.of_nat (length ents) <= TASK_SIZE)%Z ->
  iov_array segs (ms_mem ms) (Z_to_bv 64 iovp) ents ->
  iov_bufs segs (ms_mem ms) ents bss ->
  iov_bufs_ok ents ->
  store_ok segs (ms_mem ms) (Z_to_bv 64 iovp) (16 * length ents) = true ->
  (f + 124 <= iovp \/ iovp + 16 * Z.of_nat (length ents) <= f + 120)%Z ->
  bufs_disj iovp (iovp + 16 * Z.of_nat (length ents)) ents ->
  no_lazy model iovp (iovp + 16 * Z.of_nat (length ents)) ->
  no_lazy model (f + 120) (f + 124) ->
  iov_nl model ents ->
  (forall ms', SWF ms ms' iovp (iovp + 16 * Z.of_nat (length ents)) -> ms_pc_val ms' = pcw b 0x94 ->
     rg ms' 10 = rg ms' 22 -> (1 <= bv_unsigned (rg ms' 10) <= iovs_total ents)%Z ->
     realizes_cfg segs cfg (mkCfg ms' model) K) ->
  realizes_cfg segs cfg (mkCfg ms model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (concat bss)) K).
Proof.
  intros segs cfg b sr (wj1 & wj2 & ij1 & ij2 & HC). exact (stdio_write_loop segs cfg b sr wj1 wj2 ij1 ij2 HC).
Qed.
