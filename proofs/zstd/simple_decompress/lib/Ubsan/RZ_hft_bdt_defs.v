(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqBuild ZdSeqBuildThm ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdSeqBuildW4.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_hft_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Notation zlenF l := (FseNCount.Zlength l).
Notation isbyte := (fun v : Z => 0 <= v < 256).

(* [comment removed for export] *)
Definition bd_hyps (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z) : Prop :=
  5 <= tl <= 9 /\ 0 <= maxSV <= 255 /\ maxSV + 1 <= zlenF norm
  /\ (forall i, 0 <= i <= maxSV -> -1 <= Znth i norm)
  /\ pws norm (maxSV + 1) = 2^tl
  /\ 2 * (maxSV + 1) + 2^tl + 8 <= wlen /\ wlen < 2^32
  /\ 4096 <= DT /\ DT + 4 + 4 * 2^tl < 2^47 /\ 4096 <= W /\ W + wlen < 2^47
  /\ 4096 <= NC /\ NC + 2 * zlenF norm < 2^47
  /\ 4096 <= lo /\ lo <= SPV - 96 /\ SPV < 2^47
  /\ (DT + 4 + 4 * 2^tl <= lo \/ SPV <= DT) /\ (W + wlen <= lo \/ SPV <= W) /\ (NC + 2 * zlenF norm <= lo \/ SPV <= NC)
  /\ (DT + 4 + 4 * 2^tl <= W \/ W + wlen <= DT) /\ (DT + 4 + 4 * 2^tl <= NC \/ NC + 2 * zlenF norm <= DT)
  /\ (W + wlen <= NC \/ NC + 2 * zlenF norm <= W).
Ltac open_bh HY := pose proof HY as (TLR & MSVR & NLEN & NGE & NSUM & WLEN & WLEN32 & DTL & DTH & WL & WH & NCL & NCH & LO0 & LOS & SPR
                                     & OFFDT & OFFW & OFFNC & DTW & DTNC & WNC).

(* [comment removed for export] *)
Definition BD (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : fmem) (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z)
    (h0 h1 : word) (tb sn sp : list Z) (m1 : fmem) : Prop :=
  rw_cells usegs m1 DT [C2 h0; C2 h1]
  /\ u8arr usegs m1 (DT + 4) (map (Z_to_bv 8) tb) /\ zlenF tb = 4 * 2^tl /\ Forall isbyte tb
  /\ u8arr usegs m1 W (u16s (map (Z_to_bv 64) sn)) /\ zlenF sn = maxSV + 1
  /\ u8arr usegs m1 (W + 2 * (maxSV + 1)) (map (Z_to_bv 8) sp) /\ zlenF sp = wlen - 2 * (maxSV + 1) /\ Forall isbyte sp
  /\ bytes_at usegs m1 NC (u16s (map (Z_to_bv 64) norm))
  /\ stk usegs m1 lo (SPV + -96)
  /\ rw_cells usegs m1 (SPV + -96) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0]
  /\ mem_inv usegs m1 /\ munch [(DT, DT + 4 + 4 * 2^tl); (W, W + wlen); (SPV - 96, SPV)] m m1 /\ wmono usegs m m1.
Ltac open_bd I := destruct I as (HDR & CEL & CLEN & CBY & SNX & SNLEN & SPRD & SPLEN & SPBY & NCB & STK & FR & MI & MU & WM).
Ltac close_bd := split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
                 split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
                 split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map,
                                  ?FseLemmas.upd_nat_length, ?FseLemmas.Zupd_length in *.

(* [comment removed for export] *)
Definition hidden (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change (hidden T) in H end.
Ltac unhide := repeat match goal with H : hidden _ |- _ => unfold hidden in H end.
Ltac hide_not_mentioning X :=
  repeat match goal with
         | H : ?P \/ ?Q |- _ =>
             lazymatch P with context [X] => fail | _ => lazymatch Q with context [X] => fail | _ => hide H end end
         end.

Lemma Forall_Zupd : forall (P : Z -> Prop) i v (l : list Z), Forall P l -> P v -> Forall P (Zupd i v l).
Proof.
  intros P i v l F Hv. unfold Zupd. generalize (Z.to_nat i). intros n. revert n.
  induction F as [|x t Hx Ht IH]; intros [|n]; cbn [upd_nat]; constructor; auto.
Qed.

(* [comment removed for export] *)
Lemma le2_of_bytes : forall bs : list byte, length bs = 2%nat -> le2 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le2, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR.
  change (256 ^ Z.of_nat 2) with 65536 in HR. rewrite <- bytes_le_to_Z_le_val in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
Lemma cb2_as_c2 : forall segs m A pre j post,
  rw_cells segs m A (pre ++ CB 2 j :: post) -> exists w, rw_cells segs m A (pre ++ C2 w :: post).
Proof.
  intros segs m A pre j post H. exists (le_bytes_to_word j).
  pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [WF1 [WFJ WF2]]. cbn in WFJ.
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact WF1|]. split; [exact I| exact WF2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite le2_of_bytes by exact WFJ. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bd_size_rng : forall SPV lo DT NC W wlen maxSV tl norm,
  bd_hyps SPV lo DT NC W wlen maxSV tl norm -> 32 <= 2^tl <= 512 /\ 16 <= 2^(tl - 1) <= 256 /\ 2^(tl - 1) * 2 = 2^tl.
Proof.
  intros until norm. intros HY. open_bh HY.
  assert (2^5 <= 2^tl) by (apply Z.pow_le_mono_r; lia). assert (2^tl <= 2^9) by (apply Z.pow_le_mono_r; lia).
  assert (2^4 <= 2^(tl - 1)) by (apply Z.pow_le_mono_r; lia). assert (2^(tl - 1) <= 2^8) by (apply Z.pow_le_mono_r; lia).
  change (2^5) with 32 in *. change (2^9) with 512 in *. change (2^4) with 16 in *. change (2^8) with 256 in *.
  split; [lia|]. split; [lia|]. replace tl with (Z.succ (tl - 1)) at 2 by lia. rewrite Z.pow_succ_r by lia. lia.
Qed.

(* [comment removed for export] *)
Ltac tbst CEL i v :=
  lazymatch type of CEL with u8arr ?segs ?mx ?A (map (Z_to_bv 8) ?buf) =>
    u8_sok CEL i; zstep;
    let X := lazymatch A with ?B + _ => B | _ => A end in
    hide_not_mentioning X;
    u8_store CEL i v; [ | unhide ]
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
