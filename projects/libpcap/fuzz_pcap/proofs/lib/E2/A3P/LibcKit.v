(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge Mem Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase RtCells I_asan_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Import GIA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

(* [comment removed for export] *)
#[using="Type"] Lemma arenaA_wmono : forall RNG (m m' : mem) A n, arenaA RNG m A n -> wmono asegs m m' -> arenaA RNG m' A n.
Proof.
  intros RNG m m' A n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W & R) WM. exists RLO, RHI.
  repeat (split; [assumption|]). split; [eapply wr_at_transport; eassumption| exact R].
Qed.
#[using="Type"] Lemma mobjA_wmono : forall RNG (m m' : mem) A n, mobjA RNG m A n -> wmono asegs m m' -> unpoisoned m' A (A + n) -> mobjA RNG m' A n.
Proof.
  intros RNG m m' A n (H0 & H1 & _ & H3 & AR & BL) WM U.
  split; [exact H0|]. split; [exact H1|]. split; [exact U|]. split; [exact H3|]. split; [eapply arenaA_wmono; eassumption| exact BL].
Qed.
#[using="Type"] Lemma aobjA_wmono : forall RNG (m m' : mem) A n, aobjA RNG m A n -> wmono asegs m m' -> unpoisoned m' A (A + n) -> aobjA RNG m' A n.
Proof.
  intros RNG m m' A n (H0 & H1 & _ & H3 & H4 & AR & BL) WM U.
  split; [exact H0|]. split; [exact H1|]. split; [exact U|]. split; [exact H3|]. split; [exact H4|].
  split; [eapply arenaA_wmono; eassumption| exact BL].
Qed.

(* [comment removed for export] *)
Definition ro_bytes_at_any__stmt : Prop := forall (m m' : mem) A bs, mem_inv asegs m -> mem_inv asegs m' -> bytes_at asegs m A bs ->
  0x10000 <= A -> A + Z.of_nat (length bs) <= 0xa4000 -> bytes_at asegs m' A bs.
Section Sz4.
Variables m m' A bs : ltac2:(SecDiet.SzSec.tyM 'ro_bytes_at_any__stmt "vvvv" @m).
#[using="Type"] Lemma ro_bytes_at_any__body : ltac2:(SecDiet.SzSec.bodyP 'ro_bytes_at_any__stmt "vvvv").
Proof.
  intros MI MI' (H0 & H1 & HB) HA HB2.
 split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  assert (RO : ro_addr asegs (wa (A + Z.of_nat i)) = true)
    by (rewrite a_ro_addr, wa_unsigned by lia; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  destruct (m' (wa (A + Z.of_nat i))) eqn:E'; [pose proof (MI' _ _ E'); congruence|].
  destruct (m (wa (A + Z.of_nat i))) eqn:E; [pose proof (MI _ _ E); congruence| reflexivity].
Qed.
End Sz4.
#[using="Type"] Lemma ro_bytes_at_any : ltac:(let t := eval cbv delta [ro_bytes_at_any__stmt] in ro_bytes_at_any__stmt in exact t).
Proof. intros m m' A bs. ltac2:(SecDiet.SzSec.closeP 'ro_bytes_at_any__body "vvvv"). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma disjoint_from_above : forall W A n hi, Forall (fun iv : Z * Z => hi <= fst iv) W -> A + n <= hi -> disjoint_from W A n.
Proof.
  induction W as [|[wl wh] W IH]; intros A n hi FW Hn; cbn [disjoint_from]; [exact I|].
  apply Forall_cons_iff in FW as [F1 F2]. cbn [fst] in F1. split; [left; lia| eapply IH; eassumption].
Qed.
Definition artcells_munch__stmt : Prop := forall W (m m' : mem), artcells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> artcells m'.
Section Sz6.
Variables W m m' : ltac2:(SecDiet.SzSec.tyM 'artcells_munch__stmt "vvv" @W).
#[using="Type"] Lemma artcells_munch__body : ltac2:(SecDiet.SzSec.bodyP 'artcells_munch__stmt "vvv").
Proof.
  intros RT MU WM FW.
 unfold artcells in *.
  repeat match goal with
  | H : _ /\ _ |- _ /\ _ => let H1 := fresh "C" in destruct H as [H1 H]; split;
        [ eapply rw_cells_transport; [exact H1 | exact MU | exact WM | eapply disjoint_from_above; [exact FW | unfold AIMG_HI; cbn; lia]] | ]
  end.
  eapply rw_cells_transport; [exact RT | exact MU | exact WM | eapply disjoint_from_above; [exact FW | unfold AIMG_HI; cbn; lia]].
Qed.
End Sz6.
#[using="Type"] Lemma artcells_munch : ltac:(let t := eval cbv delta [artcells_munch__stmt] in artcells_munch__stmt in exact t).
Proof. intros W m m'. ltac2:(SecDiet.SzSec.closeP 'artcells_munch__body "vvv"). Qed.

(* [comment removed for export] *)
Definition asan_memcpy_specZ__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo Dst Src n : Z) (src junk : list byte),
  a0 = Z_to_bv 64 Dst -> a1 = Z_to_bv 64 Src -> a2 = Z_to_bv 64 n ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo + 2224 <= bv_unsigned sp -> ATOP + 4096 <= lo ->
  artcells m ->
  bytes_at asegs m Src src -> length src = Z.to_nat n -> 0 <= n <= 2^40 ->
  rw_cells asegs m Dst [CB (Z.to_nat n) junk] ->
  (Src + n <= Dst \/ Dst + n <= Src) ->
  mobjA RNG m Src n -> mobjA RNG m Dst n -> Src + n <= ATOP -> Dst + n <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Dst) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp); (Dst, Dst + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Dst [CB (Z.to_nat n) src] /\ bytes_at asegs m' Src src)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x54964) fc None m (seg_rom asegs)).
Section Sz7.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Dst Src n src junk : ltac2:(SecDiet.SzSec.tyM 'asan_memcpy_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma asan_memcpy_specZ__body : ltac2:(SecDiet.SzSec.bodyP 'asan_memcpy_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros -> -> -> MI ST BU LO RT SRC LEN Hn DST SEP OS OD TS TD RIMG RSTK.
  destruct OS as (S0 & S47 & SUNP & SRNG & (RLO1 & RHI1 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18) & SAPP).
  destruct OD as (D0 & D47 & DUNP & DRNG & (RLO2 & RHI2 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28) & DAPP).
  destruct RT as (_ & GOT & GRIC & RMEM & SHB & _ & INI & LAY & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  assert (E0 : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (E1 : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evtF_mono.
  - eapply (asan_memcpy_spec RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo src junk RLO1 RHI1 RLO2 RHI2); rewrite ?E0, ?E1, ?E2;
      first [ assumption | unfold KHIGH, KEND in *; lia ].
  - cbv beta. intros ms' PO. unfold asan_memcpy_post in PO. rewrite ?E0, ?E1, ?E2 in PO. exact PO.
Qed.
End Sz7.
#[using="Type"] Lemma asan_memcpy_specZ : ltac:(let t := eval cbv delta [asan_memcpy_specZ__stmt] in asan_memcpy_specZ__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Dst Src n src junk. ltac2:(SecDiet.SzSec.closeP 'asan_memcpy_specZ__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.I_asan_memcpy.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

(* [comment removed for export] *)
#[using="Type"] Lemma arenaA_wmono : forall RNG (m m' : mem) A n, arenaA RNG m A n -> wmono asegs m m' -> arenaA RNG m' A n.
Proof.
  intros RNG m m' A n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W & R) WM. exists RLO, RHI.
  repeat (split; [assumption|]). split; [eapply wr_at_transport; eassumption| exact R].
Qed.
#[using="Type"] Lemma mobjA_wmono : forall RNG (m m' : mem) A n, mobjA RNG m A n -> wmono asegs m m' -> unpoisoned m' A (A + n) -> mobjA RNG m' A n.
Proof.
  intros RNG m m' A n (H0 & H1 & _ & H3 & AR & BL) WM U.
  split; [exact H0|]. split; [exact H1|]. split; [exact U|]. split; [exact H3|]. split; [eapply arenaA_wmono; eassumption| exact BL].
Qed.
#[using="Type"] Lemma aobjA_wmono : forall RNG (m m' : mem) A n, aobjA RNG m A n -> wmono asegs m m' -> unpoisoned m' A (A + n) -> aobjA RNG m' A n.
Proof.
  intros RNG m m' A n (H0 & H1 & _ & H3 & H4 & AR & BL) WM U.
  split; [exact H0|]. split; [exact H1|]. split; [exact U|]. split; [exact H3|]. split; [exact H4|].
  split; [eapply arenaA_wmono; eassumption| exact BL].
Qed.

(* [comment removed for export] *)
Definition ro_bytes_at_any__stmt : Prop := forall (m m' : mem) A bs, mem_inv asegs m -> mem_inv asegs m' -> bytes_at asegs m A bs ->
  0x10000 <= A -> A + Z.of_nat (length bs) <= 0xa5000 -> bytes_at asegs m' A bs.
Section Sz4.
Variables m m' A bs : ltac2:(SecDiet.SzSec.tyM 'ro_bytes_at_any__stmt "vvvv" @m).
#[using="Type"] Lemma ro_bytes_at_any__body : ltac2:(SecDiet.SzSec.bodyP 'ro_bytes_at_any__stmt "vvvv").
Proof.
  intros MI MI' (H0 & H1 & HB) HA HB2.
 split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  assert (RO : ro_addr asegs (wa (A + Z.of_nat i)) = true)
    by (rewrite a_ro_addr, wa_unsigned by lia; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  destruct (m' (wa (A + Z.of_nat i))) eqn:E'; [pose proof (MI' _ _ E'); congruence|].
  destruct (m (wa (A + Z.of_nat i))) eqn:E; [pose proof (MI _ _ E); congruence| reflexivity].
Qed.
End Sz4.
#[using="Type"] Lemma ro_bytes_at_any : ltac:(let t := eval cbv delta [ro_bytes_at_any__stmt] in ro_bytes_at_any__stmt in exact t).
Proof. intros m m' A bs. ltac2:(SecDiet.SzSec.closeP 'ro_bytes_at_any__body "vvvv"). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma disjoint_from_above : forall W A n hi, Forall (fun iv : Z * Z => hi <= fst iv) W -> A + n <= hi -> disjoint_from W A n.
Proof.
  induction W as [|[wl wh] W IH]; intros A n hi FW Hn; cbn [disjoint_from]; [exact I|].
  apply Forall_cons_iff in FW as [F1 F2]. cbn [fst] in F1. split; [left; lia| eapply IH; eassumption].
Qed.
Definition artcells_munch__stmt : Prop := forall W (m m' : mem), artcells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> artcells m'.
Section Sz6.
Variables W m m' : ltac2:(SecDiet.SzSec.tyM 'artcells_munch__stmt "vvv" @W).
#[using="Type"] Lemma artcells_munch__body : ltac2:(SecDiet.SzSec.bodyP 'artcells_munch__stmt "vvv").
Proof.
  intros RT MU WM FW.
 unfold artcells in *.
  repeat match goal with
  | H : _ /\ _ |- _ /\ _ => let H1 := fresh "C" in destruct H as [H1 H]; split;
        [ eapply rw_cells_transport; [exact H1 | exact MU | exact WM | eapply disjoint_from_above; [exact FW | unfold AIMG_HI; cbn; lia]] | ]
  end.
  eapply rw_cells_transport; [exact RT | exact MU | exact WM | eapply disjoint_from_above; [exact FW | unfold AIMG_HI; cbn; lia]].
Qed.
End Sz6.
#[using="Type"] Lemma artcells_munch : ltac:(let t := eval cbv delta [artcells_munch__stmt] in artcells_munch__stmt in exact t).
Proof. intros W m m'. ltac2:(SecDiet.SzSec.closeP 'artcells_munch__body "vvv"). Qed.

(* [comment removed for export] *)
Definition asan_memcpy_specZ__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo Dst Src n : Z) (src junk : list byte),
  a0 = Z_to_bv 64 Dst -> a1 = Z_to_bv 64 Src -> a2 = Z_to_bv 64 n ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo + 2224 <= bv_unsigned sp -> ATOP + 4096 <= lo ->
  artcells m ->
  bytes_at asegs m Src src -> length src = Z.to_nat n -> 0 <= n <= 2^40 ->
  rw_cells asegs m Dst [CB (Z.to_nat n) junk] ->
  (Src + n <= Dst \/ Dst + n <= Src) ->
  mobjA RNG m Src n -> mobjA RNG m Dst n -> Src + n <= ATOP -> Dst + n <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Dst) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp); (Dst, Dst + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Dst [CB (Z.to_nat n) src] /\ bytes_at asegs m' Src src)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x549cc) fc None m (seg_rom asegs)).
Section Sz7.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Dst Src n src junk : ltac2:(SecDiet.SzSec.tyM 'asan_memcpy_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma asan_memcpy_specZ__body : ltac2:(SecDiet.SzSec.bodyP 'asan_memcpy_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros -> -> -> MI ST BU LO RT SRC LEN Hn DST SEP OS OD TS TD RIMG RSTK.
  destruct OS as (S0 & S47 & SUNP & SRNG & (RLO1 & RHI1 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18) & SAPP).
  destruct OD as (D0 & D47 & DUNP & DRNG & (RLO2 & RHI2 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28) & DAPP).
  destruct RT as (_ & GOT & GRIC & RMEM & SHB & _ & INI & LAY & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  assert (E0 : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (E1 : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evtF_mono.
  - eapply (asan_memcpy_spec RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo src junk RLO1 RHI1 RLO2 RHI2); rewrite ?E0, ?E1, ?E2;
      first [ assumption | unfold KHIGH, KEND in *; lia ].
  - cbv beta. intros ms' PO. unfold asan_memcpy_post in PO. rewrite ?E0, ?E1, ?E2 in PO. exact PO.
Qed.
End Sz7.
#[using="Type"] Lemma asan_memcpy_specZ : ltac:(let t := eval cbv delta [asan_memcpy_specZ__stmt] in asan_memcpy_specZ__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Dst Src n src junk. ltac2:(SecDiet.SzSec.closeP 'asan_memcpy_specZ__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
