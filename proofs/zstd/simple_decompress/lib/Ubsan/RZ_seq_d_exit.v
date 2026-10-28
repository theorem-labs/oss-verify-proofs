(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_last RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_lbase2 RZ_seq_d_lkit2 RZ_seq_d_lbase3 seqL2_kit_ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqd_rw_mid : forall m A pre c mid post post' n1 n2,
  rw_cells usegs m A (pre ++ c :: mid ++ post) -> cells_size pre = n1 -> cells_size mid = n2 ->
  cells_wf post' -> cells_bytes post' = cells_bytes post ->
  rw_cells usegs m A (CB n1 (cells_bytes pre) :: c :: CB n2 (cells_bytes mid) :: post').
Proof.
  intros m A pre c mid post post' n1 n2 RW S1 S2 WP EP. pose proof RW as [[WF _] _].
  apply cells_wf_app in WF. destruct WF as [W1 WF]. cbn [cells_wf] in WF. destruct WF as [WC WF].
  apply cells_wf_app in WF. destruct WF as [W2 _].
  eapply rw_cells_recell; [exact RW| |].
  - cbn [cells_wf cell_wf]. rewrite !cells_bytes_length by assumption.
    split; [exact S1|]. split; [exact WC|]. split; [exact S2|exact WP].
  - cbn [cells_bytes cbytes]. rewrite cells_bytes_app. cbn [cells_bytes]. rewrite cells_bytes_app, EP. reflexivity.
Qed.

Ltac seqd_btake n L :=
  lazymatch n with
  | O => constr:((@nil cell, L))
  | _ => lazymatch L with ?c :: ?rest =>
           let s := lazymatch c with C8 _ => constr:(8%nat) | C4 _ => constr:(4%nat) | C2 _ => constr:(2%nat) | C1 _ => constr:(1%nat) | CB ?k _ => k end in
           let n' := eval compute in (Nat.sub n s) in
           let r := seqd_btake n' rest in lazymatch r with (?pre, ?post) => constr:((c :: pre, post)) end end
  end.

(* [comment removed for export] *)
Lemma seqd_linv_rep : forall P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqd_static P OEND LEND -> seqd_sep P -> seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall m2 r0' r1' r2' j0 jpad jseq,
  munch [(q_DCTX P + 26684, q_DCTX P + 26684 + 12)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  rw_cells usegs m2 (q_DCTX P + 26684) [C4 r0'; C4 r1'; C4 r2'] ->
  rw_cells usegs m2 (q_SPV P + -352) (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad jseq) ->
  seqd_xinv P m2 (seqd_fe P) /\ rdbl usegs m2 (q_LITP P) (LEND + 32) /\
  (exists jpre, rw_cells usegs m2 (q_SPV P + -352) (CB 248 jpre :: seqd_saved P)) /\
  (exists jpre jmid, rw_cells usegs m2 (q_SPV P + -352) (CB 32 jpre :: C8 (Z_to_bv 64 (q_DST P)) :: CB 208 jmid :: seqd_saved P)).
Proof.
  intros P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST SEP INV m2 r0' r1' r2' j0 jpad jseq MUL WML MI2 REP2 FR2.
  destruct INV as (_ & _ & _ & _ & _ & LIT & XI).
  assert (FRX : exists jpre jmid, rw_cells usegs m2 (q_SPV P + -352) (CB 32 jpre :: C8 (Z_to_bv 64 (q_DST P)) :: CB 208 jmid :: seqd_saved P)).
  { clear - FR2. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
    cbn [seqd_frame seqd_saved q_SPV q_DST] in *.
    lazymatch type of FR2 with rw_cells ?sg ?mm ?A ?L =>
      let r1 := seqd_btake 32%nat L in lazymatch r1 with (?pre, ?c :: ?rest) =>
      let r2 := seqd_btake 208%nat rest in lazymatch r2 with (?mid, ?post) =>
        change (rw_cells sg mm A (pre ++ c :: mid ++ post)) in FR2;
        exists (cells_bytes pre), (cells_bytes mid);
        apply (seqd_rw_mid mm A pre c mid post);
        [exact FR2 | reflexivity | reflexivity | cbn [cells_wf cell_wf]; repeat split | cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity]
      end end end. }
  destruct FRX as (jpre & jmid & FRX).
  pose proof (rw_cells_forget _ _ _ 3%nat 248%nat FRX eq_refl) as FRY. cbn [firstn skipn] in FRY.
  split; [|split; [|split; [eexists; exact FRY | exists jpre, jmid; exact FRX]]]; clear FRX FRY FR2.
  - destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
    cbn [seqd_static seqd_xinv q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
    sd_static_open ST. unfold held in *.
    destruct XI as (_ & HH3 & BUF & STK & MU & WM & MI1).
    unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy in *.
    split; [exists r0', r1', r2'; exact REP2|].
    split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [lia|exact I]]|].
    split; [eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S32; lia|exact I]]|].
    split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S27 S18; lia|exact I]]|].
    split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|].
    split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
  - eapply rdbl_transport; [exact LIT | exact MUL |]. intros x Hx. left. cbn [outside]. split; [|exact I].
    clear - ST SEP Hx. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqd_static seqd_sep q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *. sd_static_open ST. unfold held in *.
    destruct SEP as (_ & _ & _ & _ & _ & _ & _ & S8'). unfold apart, WILDCOPY_OVERLENGTH, DCTX_entropy_rep, DCTX_litExtraBuffer in S8'.
    clear - S8' S8 Hx. lia.
Qed.

Lemma seqd_exit : forall P OEND LEND K, seqd_static P OEND LEND -> seqd_ranges P -> seqd_sep P -> at_exit P OEND LEND K.
Proof.
  intros P OEND LEND K ST RG0 SEP0. unfold at_exit.
  intros m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 INV HOP L2 HBC.
  pose proof (p_lastcopy P) as PLAST. pose proof (p_exit P) as PEXIT.
  pose proof (seqd_linv_rep P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST SEP0 INV) as REPL.
  pose proof (seqd_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as ((j0 & jpad & jseq & FR) & _ & _ & _ & _ & _ & XI).
  assert (REPX : exists r0' r1' r2', rw_cells usegs m1 (q_DCTX P + 26684) [C4 r0'; C4 r1'; C4 r2']).
  { clear - XI. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqd_xinv q_DCTX] in *. destruct XI as (X & _). unfold DCTX_entropy_rep in X. exact X. }
  destruct REPX as (r0' & r1' & r2' & REP). clear XI.
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_frame seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in ST, FR, REP, HOP, L2, PLAST, PEXIT, REPL |- *.
  sd_static_open ST.
  assert (MUL : munch [(DCTX + 26684, DCTX + 26684 + 12)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= LEND < 2^47 /\ 4096 <= OEND < 2^47 /\ 4096 <= DCTX < 2^47 /\
               0 <= LEND - LP <= 2^47 /\ 0 <= OEND - OP <= 2^47 /\ 0 <= bc <= 2147483647)
    by (clear - HOP L2 S1 S2 S3 S4 S5 S6 S7 S9 S11 S19 S20 HBC; lia).
  assert (DJ : SPV - 352 + 352 <= DCTX + 26684 \/ DCTX + 26684 + 12 <= SPV - 352) by (unfold held in S27; clear - S27 S18; lia).
  ((try hold PLAST; try hold PEXIT; try hold REPL; try hold ST0; try hold INV; try hold RG0; try hold SEP0; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1d6e4; 0x1d6b0; 0x1d724] 60%nat
    [KZRange SPV 544 (2^47); KZRange DCTX 4096 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47);
     KZRange OEND 4096 (2^47); KZRange bc 0 2147483647; KZRange (LEND - LP) 0 (2^47); KZRange (OEND - OP) 0 (2^47);
     KZWr (SPV - 352) 352; KZWr (DCTX + 26684) 12; KZDisj (SPV - 352) 352 (DCTX + 26684) 12]
    [(SPV - 352, 352)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in PLAST; try unfold held in PEXIT; try unfold held in REPL; try unfold held in ST0; try unfold held in INV; try unfold held in RG0; try unfold held in SEP0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _) _ (Z_to_bv 64 0x1d6e4) _ _ ?mm _) =>
          (assert (MIc : mem_inv usegs mm) by assumption; destruct (REPL mm _ _ _ _ _ _ MUL WMl MIc REP FR) as (XI2 & LIT2 & (jpre & FRX) & _);
           eapply (PEXIT mm jpre r); [exact RG0 | exact XI2 | exact FRX | lia | left; reflexivity])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d6b0) _ _ ?mm _) =>
          (assert (MIc : mem_inv usegs mm) by assumption; destruct (REPL mm _ _ _ _ _ _ MUL WMl MIc REP FR) as (XI2 & LIT2 & _ & (jpre & jmid & FRX));
           eapply (PLAST _ jpre jmid); [exact RG0 | exact SEP0 | exact XI2 | exact FRX | lia | lia | lia | intros Z0; exfalso; lia | intros _; lia | lia | lia | eapply rdbl_sub; [exact LIT2 | lia | lia] | unfold held in S12; lia | unfold held in S26; unfold off_stack; lia])
      end).
Qed.
