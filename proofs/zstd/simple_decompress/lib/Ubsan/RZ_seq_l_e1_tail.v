(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_rkit RZ_seq_l_xat RZ_seq_l_md_at RZ_seq_l_lx_at RZ_seq_l_e1_at seqL2_kit_ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac e1_rsplit L :=
  lazymatch L with
  | CB _ (seql_ring_bytes _ _ _) :: ?post => constr:((@nil cell, post))
  | ?c :: ?rest => let r := e1_rsplit rest in lazymatch r with (?pre, ?post) => constr:((c :: pre, post)) end
  end.
Ltac e1_take k L :=
  lazymatch k with
  | O => constr:((@nil cell, L))
  | S ?k' => lazymatch L with ?c :: ?rest => let r := e1_take k' rest in lazymatch r with (?pre, ?post) => constr:((c :: pre, post)) end end
  end.

Lemma e1_tail_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P -> LEND = y_DCTX P + 95908 ->
  seql_at_err P OEND LLO LEND LOCV -> (forall K', 1 <= K' < K -> md_head P OEND LLO LEND LOCV K') -> lx_done P OEND LLO LEND LOCV -> e1_tail P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK HXE CONT1 CONT2 CONT3. unfold e1_tail.
  intros m1 c0 c128 c176 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP r sn cidx dll dml dof raddr x1 x5 x8 x9 x10 x11 x15 x17 x21 x22 x23 x24 x29 x30 INV HR HSN HCI HDL HDM HDO HRING RES HRA.
  pose proof (seql_linv_frame P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold seql_at_err in CONT1. unfold lx_done in CONT3.
  assert (CONT2' : forall K', 1 <= K' < K -> forall Ks, Ks = K' -> md_head P OEND LLO LEND LOCV Ks) by (intros K' HK' Ks ->; apply CONT2; exact HK').
  clear CONT2. rename CONT2' into CONT2. unfold md_head in CONT2.
  pose proof INV as ((jpad & jseq & FR) & _).
  destruct RES as (LF & HOE). destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  pose proof (seql_ring_ok_upd 8 rl rm ro cidx dll dml dof HRING HDL HDM HDO) as HRING2.
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, L1, L2, L6, HK, HSN, HRA, HXE, CONT1, CONT2, CONT3, TRANS |- *.
  sd_static_open ST. subst LEND.
  assert (RG : 0 <= sn < 98047 /\ 1 <= nbSeq <= 98047 /\ 0 <= r < 2^47 /\ 4096 <= OP < 2^47) by (clear - S1 S2 S3 S4 S5 S6 S7 S16 HK HR HSN L1 HOE; lia).
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  lazymatch type of FR with rw_cells _ ?mm ?A ?L => let rs := e1_rsplit L in lazymatch rs with (?pre, ?post) => apply (seql_ring_open mm A pre post rl rm ro) in FR end end.
  cbn [seql_ring_cells app] in FR.
  assert (CASES : cidx = 0 \/ cidx = 1 \/ cidx = 2 \/ cidx = 3 \/ cidx = 4 \/ cidx = 5 \/ cidx = 6 \/ cidx = 7) by (clear - HCI; lia).
  destruct CASES as [C|[C|[C|[C|[C|[C|[C|C]]]]]]].
  all: subst cidx; subst raddr.
  all: (try hold CONT1; try hold CONT2; try hold CONT3; try hold HK; try hold ST0; try hold INV; try hold TRANS; try hold HRING; try hold HRING2; try hold HSN; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML).
  all: kx_autoLx [0x18464; 0x19ca8; 0x1ac04] 60%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange sn 0 98047; KZRange nbSeq 1 98047; KZRange r 0 (2^47); KZRange OP 4096 (2^47); KZWr (SPV - 688) 688]
    [(SPV - 688, 688)].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end). all: kx_mem.
  all: (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in HK; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in HRING; try unfold held in HRING2; try unfold held in HSN; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: lazymatch type of FR with rw_cells _ ?mm ?A ?L =>
    let len := eval cbn [length] in (length L) in let n := eval compute in (Nat.sub len 27) in
    let p := e1_take n L in lazymatch p with (?pre, ?rest) =>
    let q := e1_take 24%nat rest in lazymatch q with (?mid, ?post) =>
      lazymatch type of HRING2 with seql_ring_ok _ ?rl2 ?rm2 ?ro2 => apply (seql_ring_close mm A pre post rl2 rm2 ro2) in FR end end end end.
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18464) _ _ _ _) =>
        eapply (CONT2 (K - 1) ltac:(lia) (K - 1) eq_refl); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | unfold seql_lfacts; cbn [y_DST y_tLL y_tOF y_tML y_SEQ y_sq y_nbSeq]; split; [lia|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia| exact L7] | lia | exact HRING2]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x19ca8) _ _ _ _) =>
        eapply CONT3 with (BND := 100 + 100 * (nbSeq - (K - 1)) + 90); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | unfold seql_lfacts; cbn [y_DST y_tLL y_tOF y_tML y_SEQ y_sq y_nbSeq]; split; [lia|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia| exact L7] | lia | eapply seql_ring_ok_le; [exact HRING2 | lia] ]
    end.
Qed.
