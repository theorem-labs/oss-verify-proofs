(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_blk_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Notation zlenF l := (FseNCount.Zlength l).

(* [comment removed for export] *)
Definition bf_hyps (SPV lo DT NC BASE BITS W maxSV tl : Z) (k : seq_kind) (wlen : nat) (norm : list Z) : Prop :=
  5 <= tl <= kind_maxLog k /\ 0 <= maxSV <= kind_max k /\ maxSV + 1 <= zlenF norm
  /\ (forall i, 0 <= i <= maxSV -> -1 <= Znth i norm)
  /\ wsum (firstn (Z.to_nat (maxSV + 1)) norm) = 2^tl
  /\ 626 <= Z.of_nat wlen
  /\ 4096 <= DT /\ DT + 8 + 8 * 2^tl < 2^47 /\ 4096 <= W /\ W + Z.of_nat wlen < 2^47
  /\ 4096 <= NC /\ NC + 2 * zlenF norm < 2^47 /\ 4096 <= BASE < 2^47 /\ 4096 <= BITS < 2^47
  /\ lo <= SPV - 128 /\ 0 <= lo /\ 0 <= SPV < 2^47
  /\ (DT + (8 + 8 * 2^tl) <= lo \/ SPV <= DT) /\ (W + Z.of_nat wlen <= lo \/ SPV <= W)
  /\ (NC + 2 * zlenF norm <= lo \/ SPV <= NC) /\ (BASE + 212 <= lo \/ SPV <= BASE) /\ (BITS + 53 <= lo \/ SPV <= BITS)
  /\ (DT + (8 + 8 * 2^tl) <= W \/ W + Z.of_nat wlen <= DT)
  /\ (DT + (8 + 8 * 2^tl) <= NC \/ NC + 2 * zlenF norm <= DT) /\ (W + Z.of_nat wlen <= NC \/ NC + 2 * zlenF norm <= W)
  /\ (DT + (8 + 8 * 2^tl) <= BASE \/ BASE + 212 <= DT) /\ (DT + (8 + 8 * 2^tl) <= BITS \/ BITS + 53 <= DT)
  /\ (W + Z.of_nat wlen <= BASE \/ BASE + 212 <= W) /\ (W + Z.of_nat wlen <= BITS \/ BITS + 53 <= W).
Ltac open_bh HY := pose proof HY as (TLR & MSVR & NLEN & NGE & NSUM & WLEN & DTL & DTH & WL & WH & NCL & NCH & BASER & BITSR & LOS & LO0 & SPR
                                     & OFFDT & OFFW & OFFNC & OFFBASE & OFFBITS & DTW & DTNC & WNC & DTBASE & DTBITS & WBASE & WBITS).

(* [comment removed for export] *)
Definition BF (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : fmem) (SPV lo DT NC BASE BITS W tl : Z) (k : seq_kind)
    (wlen : nat) (norm : list Z) (h0 h1 w8 w16 : word) (cells : list seqsym) (symNext spread : list Z) (m1 : fmem) : Prop :=
  rw_cells usegs m1 DT [C4 h0; C4 h1]
  /\ u8arr usegs m1 (DT + 8) (cellsB cells) /\ zlenF cells = 2^tl
  /\ u8arr usegs m1 W (u16s (map (Z_to_bv 64) symNext)) /\ zlenF symNext = 53
  /\ u8arr usegs m1 (W + 106) (map (Z_to_bv 8) spread) /\ zlenF spread = Z.of_nat wlen - 106
  /\ bytes_at usegs m1 NC (u16s (map (Z_to_bv 64) norm))
  /\ bytes_at usegs m1 BASE (u32s (map (Z_to_bv 64) (kind_base k)))
  /\ bytes_at usegs m1 BITS (map (Z_to_bv 8) (kind_bits k))
  /\ stk usegs m1 lo (SPV + -128)
  /\ (exists j0, rw_cells usegs m1 (SPV + -128)
        [CB 8 j0; C8 w8; C8 w16; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
  /\ mem_inv usegs m1 /\ munch [(DT, DT + 8 + 8 * 2^tl); (W, W + Z.of_nat wlen); (SPV - 128, SPV)] m m1 /\ wmono usegs m m1.
Ltac open_bf I := destruct I as (HDR & CEL & CLEN & SNX & SNLEN & SPRD & SPLEN & NCB & BASEB & BITSB & STK & (j0 & FR) & MI & MU & WM).
Ltac close_bf := split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
                 split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
                 split; [eassumption|]; split; [eexists; eassumption|]; split; [eassumption|]; split; eassumption.

(* [comment removed for export] *)
Definition bf_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DT W tl : Z) (wlen : nat) (lo : Z) (m : fmem) (t : seq_table) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' wb',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DT, DT + 8 + 8 * 2^tl); (W, W + Z.of_nat wlen); (SPV - 128, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ u8arr usegs m' DT (map (Z_to_bv 8) (seq_table_bytes t))
    /\ u8arr usegs m' W wb' /\ length wb' = wlen.

Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map, ?cellsB_length,
                                  ?FseLemmas.upd_nat_length, ?FseLemmas.Zupd_length, ?set_cell_length, ?set_base_length in *.

(* [comment removed for export] *)
Definition hidden (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change (hidden T) in H end.
Ltac unhide := repeat match goal with H : hidden _ |- _ => unfold hidden in H end.
Ltac hide_not_mentioning X :=
  repeat match goal with
         | H : ?P \/ ?Q |- _ =>
             lazymatch P with context [X] => fail | _ => lazymatch Q with context [X] => fail | _ => hide H end end
         end.
Ltac base_var A := lazymatch A with ?X + _ => X | _ => A end.

(* [comment removed for export] *)
Ltac cst CEL u off kk lem md :=
  lazymatch type of CEL with u8arr ?segs ?mx ?A (cellsB ?cells) =>
    let a := cur_mem_addr in
    let SOK := fresh "SOK" in
    pose proof (u8arr_storen_ok segs mx A _ (8 * u + off) kk a CEL ltac:(lia) ltac:(rewrite cellsB_length, ?set_cell_length, ?set_base_length; lia) ltac:(addr_tac)) as SOK;
    zstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mx (Z_to_bv 64 ?E) ?bs) _) =>
      let C2 := fresh "CEL" in
      pose proof (u8arr_writen segs mx A _ (8 * u + off) bs CEL ltac:(lia) ltac:(rewrite cellsB_length, ?set_cell_length, ?set_base_length; simpl_sizes; lia)) as C2;
      replace (wa (A + (8 * u + off))) with (wa E) in C2 by (f_equal; lia);
      lazymatch bs with
      | _ (Z_to_bv 64 ?x) =>
          rewrite (lem cells u x (x mod md)) in C2 by (unfold FseNCount.Zlength; rewrite ?set_cell_length, ?set_base_length; first [ lia | rewrite Z.mod_mod by lia; reflexivity ])
      end;
      clear CEL; let X := base_var A in hide_not_mentioning X; store_done; unhide; rename C2 into CEL
    end
  end.

(* [comment removed for export] *)
Ltac snst SNX s x v :=
  lazymatch type of SNX with u8arr ?segs ?mx ?Wb (u16s (map (Z_to_bv 64) ?l)) =>
    let SOK := fresh "SOK" in
    pose proof (u16arr_store_ok segs mx Wb _ s (wa (Wb + 2 * s)) SNX ltac:(rewrite length_map; lia) eq_refl) as SOK;
    zstep;
    let S2 := fresh "SNX" in
    pose proof (u16arr_write segs mx Wb _ s (Z_to_bv 64 x) SNX ltac:(rewrite length_map; lia)) as S2;
    clear SNX; hide_not_mentioning Wb; store_done; unhide;
    rewrite (u16s_upd_Z l (Z.to_nat s) x v) in S2 by (first [ reflexivity | rewrite Z.mod_mod by lia; reflexivity ]);
    rename S2 into SNX
  end.

(* [comment removed for export] *)
Lemma bf_size_rng : forall SPV lo DT NC BASE BITS W maxSV tl k wlen norm,
  bf_hyps SPV lo DT NC BASE BITS W maxSV tl k wlen norm -> 5 <= tl <= 9 /\ 32 <= 2^tl <= 512 /\ maxSV <= 52.
Proof.
  intros until norm. intros HY. open_bh HY.
  assert (TL9 : 5 <= tl <= 9) by (destruct k; cbn [kind_maxLog] in *; lia).
  assert (2^5 <= 2^tl) by (apply Z.pow_le_mono_r; lia). assert (2^tl <= 2^9) by (apply Z.pow_le_mono_r; lia).
  change (2^5) with 32 in *. change (2^9) with 512 in *. split; [exact TL9|]. split; [lia|]. destruct k; cbn [kind_max] in *; lia.
Qed.
