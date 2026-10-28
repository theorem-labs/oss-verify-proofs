(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Notation isbyte := (fun v : Z => 0 <= v < 256).

(* [comment removed for export] *)
Definition fd_hyps (SPV lo DST cap SRCI ni DT tl : Z) : Prop :=
  0 <= tl <= 9
  /\ 4096 <= DST /\ 0 <= cap <= 65536 /\ DST + cap < 2^47
  /\ 4096 <= SRCI /\ 0 <= ni <= 65536 /\ SRCI + ni < 2^47
  /\ 4096 <= DT /\ DT + 4 + 4 * 2^tl < 2^47
  /\ 4096 <= lo /\ lo <= SPV - 160 /\ SPV < 2^47
  /\ (DST + cap <= lo \/ SPV <= DST) /\ (SRCI + ni <= lo \/ SPV <= SRCI) /\ (DT + 4 + 4 * 2^tl <= lo \/ SPV <= DT)
  /\ (DST + cap <= SRCI \/ SRCI + ni <= DST) /\ (DST + cap <= DT \/ DT + 4 + 4 * 2^tl <= DST).
Ltac open_fh HY := pose proof HY as (TLR & DSTL & CAPR & DSTH & SRCL & NIR & SRCH & DTL & DTH & LO0 & LOS & SPR & OFFDST & OFFSRC & OFFDT & DSTSRC & DSTDT).

(* [comment removed for export] *)
Definition fd_tbl (tl fast : Z) (tb : list Z) : Prop :=
  Z.of_nat (length tb) = 4 * 2^tl /\ Forall isbyte tb /\ forall u, 0 <= u < 2^tl -> fse_cell_ok tl fast tb u.

(* [comment removed for export] *)
Definition fc_nb (tb : list Z) (st : Z) : Z := Znth (4 * st + 3) tb.
Definition fc_sy (tb : list Z) (st : Z) : Z := Znth (4 * st + 2) tb.
Definition fc_nx (tb : list Z) (st : Z) : Z := Znth (4 * st) tb + 256 * Znth (4 * st + 1) tb.

Lemma fd_cell : forall tl fast tb st, fd_tbl tl fast tb -> 0 <= tl -> 0 <= st < 2^tl ->
  0 <= fc_nb tb st <= tl /\ (fast = 1 -> 1 <= fc_nb tb st) /\ 0 <= fc_nx tb st /\ fc_nx tb st + 2^(fc_nb tb st) <= 2^tl
  /\ 0 <= fc_sy tb st < 256 /\ 0 <= Znth (4 * st) tb < 256 /\ 0 <= Znth (4 * st + 1) tb < 256.
Proof.
  intros tl fast tb st (L & BY & OK) TL HS. specialize (OK st HS). unfold fse_cell_ok in OK. cbv zeta in OK.
  unfold fc_nb, fc_sy, fc_nx. destruct OK as (A & B & C & D).
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|].
  split; [apply (Forall_Znth _ tb (4 * st + 2) BY); lia|]. split; [apply (Forall_Znth _ tb (4 * st) BY); lia| apply (Forall_Znth _ tb (4 * st + 1) BY); lia].
Qed.

(* [comment removed for export] *)
Definition FD (s0 s1 s2 s3 s4 s5 s6 s7 ra0 : word) (m : fmem) (SPV lo DST cap WK wksz SRCI DT : Z) (srci : list byte) (tb : list Z)
    (out : list byte) (m1 : fmem) : Prop :=
  u8arr usegs m1 DST out /\ Z.of_nat (length out) = cap
  /\ stk usegs m1 WK (WK + wksz)
  /\ bytes_at usegs m1 SRCI srci
  /\ bytes_at usegs m1 (DT + 4) (map (Z_to_bv 8) tb)
  /\ stk usegs m1 lo (SPV + -160)
  /\ (exists j0 msv tlw, rw_cells usegs m1 (SPV + -160) [CB 8 j0; C4 msv; C4 tlw])
  /\ (exists a b, rw_cells usegs m1 (SPV + -144) [C8 a; C8 b])
  /\ (exists a b, rw_cells usegs m1 (SPV + -128) [C8 a; C8 b])
  /\ (exists c b pad p s l, rw_cells usegs m1 (SPV + -112) [C8 c; C4 b; CB 4 pad; C8 p; C8 s; C8 l])
  /\ rw_cells usegs m1 (SPV + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0]
  /\ mem_inv usegs m1 /\ munch [(DST, DST + cap); (WK, WK + wksz); (SPV - 384, SPV)] m m1 /\ wmono usegs m m1.
Ltac open_fd I := destruct I as (OUT & OLEN & WKS & SRCB & CELB & STK & (fj0 & fmsv & ftlw & F0) & (f2a & f2b & FS2) & (f1a & f1b & FS1)
                                 & (fbc & fbb & fbpad & fbp & fbs & fbl & FBD) & FSAV & MI & MU & WM).
Ltac close_fd := unfold FD; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
                 split; [do 3 eexists; eassumption|]; split; [do 2 eexists; eassumption|]; split; [do 2 eexists; eassumption|];
                 split; [do 6 eexists; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

(* [comment removed for export] *)
Lemma fc_nx_rd : forall m A (tb : list Z) st a, bytes_at usegs m A (map (Z_to_bv 8) tb) ->
  0 <= st -> 4 * st + 2 <= Z.of_nat (length tb) ->
  0 <= Znth (4 * st) tb < 256 -> 0 <= Znth (4 * st + 1) tb < 256 -> a = wa (A + 4 * st) ->
  ov_read_bytes usegs m a 2 = Some (le2 (Z_to_bv 64 (fc_nx tb st))).
Proof.
  intros m A tb st a B HS HL B0 B1 ->.
  rewrite (bytes_at_read usegs m A _ (4 * st) 2 B) by (rewrite ?length_map; lia). f_equal.
  rewrite (le2_Z (fc_nx tb st) (fc_nx tb st) eq_refl). unfold ZdSeqTable.zle2, fc_nx.
  replace ((Znth (4 * st) tb + 256 * Znth (4 * st + 1) tb) mod 256) with (Znth (4 * st) tb) by (Z.div_mod_to_equations; lia).
  replace (((Znth (4 * st) tb + 256 * Znth (4 * st + 1) tb) / 256) mod 256) with (Znth (4 * st + 1) tb) by (Z.div_mod_to_equations; lia).
  rewrite skipn_map, firstn_map.
  unfold Znth. replace (Z.to_nat (4 * st + 1)) with (S (Z.to_nat (4 * st))) by lia.
  assert (LT : (S (Z.to_nat (4 * st)) < length tb)%nat) by lia.
  revert LT. generalize (Z.to_nat (4 * st)). clear. intros k. revert tb. induction k as [|k IH]; intros tb LT.
  - destruct tb as [|x [|y t]]; cbn [length] in LT; try lia. reflexivity.
  - destruct tb as [|x t]; cbn [length] in LT; [lia|]. cbn [skipn nth]. apply IH. lia.
Qed.

(* [comment removed for export] *)
Ltac ldnb CELB DT tb st :=
  let a := cur_mem_addr in
  let RDc := fresh "RDc" in
  pose proof (u8ro_znth usegs _ (DT + 4) tb (4 * st + 3) a CELB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDc;
  zstep; cbv beta; fold (fc_nb tb st); rewrite (byte_lit (fc_nb tb st)) by lia; clear RDc.
Ltac ldsy CELB DT tb st :=
  let a := cur_mem_addr in
  let RDc := fresh "RDc" in
  pose proof (u8ro_znth usegs _ (DT + 4) tb (4 * st + 2) a CELB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDc;
  zstep; cbv beta; fold (fc_sy tb st); rewrite (byte_lit (fc_sy tb st)) by lia; clear RDc.
Ltac ldnx CELB DT tb st :=
  let a := cur_mem_addr in
  let RDc := fresh "RDc" in
  pose proof (fc_nx_rd _ (DT + 4) tb st a CELB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDc;
  zstep; rewrite (zx16_u (fc_nx tb st)) by lia; clear RDc.
Ltac ldmask MI nb :=
  let a := cur_mem_addr in
  let RDc := fresh "RDc" in
  pose proof (fbitmask_rd _ nb a MI ltac:(lia) ltac:(unfold wa, FBITMASK; f_equal; lia)) as RDc;
  zstep; clear RDc.

(* [comment removed for export] *)
Lemma fast_bits_lt : forall x nb, 0 <= x < 2^64 -> 1 <= nb <= 63 ->
  0 <= Z.shiftr x ((bv_swrap 32 (0 - nb) mod 18446744073709551616) mod 64) < 2^nb.
Proof.
  intros x nb Hx Hn. rewrite (swrap32_small (0 - nb)) by lia.
  replace ((0 - nb) mod 18446744073709551616) with (18446744073709551616 - nb) by (apply Z.mod_unique with (q := -1); lia).
  replace ((18446744073709551616 - nb) mod 64) with (64 - nb) by (apply Z.mod_unique with (q := 288230376151711743); lia).
  rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia| apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|]. rewrite <- Z.pow_add_r by lia. replace (64 - nb + nb) with 64 by lia. lia.
Qed.
