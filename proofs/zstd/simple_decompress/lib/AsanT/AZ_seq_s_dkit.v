(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_lkit2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sqs2_post (P : ssq) (OEND LLO LEND LOCV : Z) (c152 c160 c168 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP OP n llv : Z)
    (gp tp x20 x25 x27 : word) (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
  fun ms' => exists (m2 : amem) (c0 c8 c200 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x18 x19 x22 x23 x24 x28 x29 x30 : word),
    ms' = MS (mkR x1 (Z_to_bv 64 (v_FRB P)) gp tp x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 (OP + n)) x17
               x18 x19 x20 (Z_to_bv 64 2147450880) x22 x23 x24 x25 (Z_to_bv 64 (llv - n)) x27 x28 x29 x30 (Z_to_bv 64 (v_DCTX P + 29896)))
             F (Z_to_bv 64 0x90f88) fc None m2 (seg_rom bsegs) /\
    sqs_linv P OEND LLO LEND LOCV m2 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP.

Ltac sqs2_ar := solve [lia | kx_bv_ranges; kx_lia_pruned].
Ltac sqs2_ms := repeat lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal
  | |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => f_equal
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; sqs2_ar
  end.
Ltac sqs2_done c0 c8 c200 :=
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR ?r1 _ _ _ ?r5 ?r6 ?r7 _ _ ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 _ ?r17 ?r18 ?r19 _ _ ?r22 ?r23 ?r24 _ _ _ ?r28 ?r29 ?r30 _) _ _ _ _ ?mm _) =>
      apply evtF_done; unfold sqs2_post;
      exists mm, c0, c8, c200, r1, r5, r6, r7, r10, r11, r12, r13, r14, r15, r17, r18, r19, r22, r23, r24, r28, r29, r30;
      split; [sqs2_ms|]
  end.

Lemma sqs2_rg : forall P OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  v_B0 P <= LLO /\ LEND + 32 <= v_B1 P /\ v_lo P <= v_FRB P - 2224 /\ v_FRB P + 384 <= 2^47 /\
  (v_B1 P <= v_lo P \/ v_FRB P <= v_B0 P) /\ v_FF P + 256 <= v_FRB P /\ KHIGH <= v_FRB P.
Proof.
  intros P OEND LLO LEND LOCV ST HLOC.
  apply (sqs_rg_k _ _ _ _ _ ST); intros RG1 RG2 RG3 RG4 RG5 RG6 RG7 RG8 RG9 RG10 RG11 RG12 RG13 RG14.
  split; [|split; [|split; [|split; [|split; [|split; [clear - RG8; lia | unfold KHIGH; clear - RG7; lia]]]]]].
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  all: cbn [v_B0 v_B1 v_FF v_FRB v_lo] in *; sd_static_open ST; unfold held in S24, S42.
  - clear - S1 S2 S3 S4 S5 S6 S7 S42 HLOC; lia.
  - clear - S1 S2 S3 S4 S5 S6 S7 S42 HLOC; lia.
  - clear - S17 S18 S47; lia.
  - clear - S17 S18 S47; lia.
  - clear - S17 S18 S47 S24; lia.
Qed.

Ltac sqs2_bufs ST INV :=
  pose proof (sqs_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6);
  pose proof (sqs_copy_asan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (ART & AST & APP);
  pose proof (sqs_linv_buf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as BUFS;
  pose proof (sqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI;
  apply (sqs_buf_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV); intros BUFB UBUF RBUF RBUFS GRAN U32 R32 RS32 U64 R64 RS64 TBG;
  clear GRAN U32 R32 RS32 U64 R64 RS64 TBG.

Lemma sqs2_bl : forall (k : nat) P OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c0 c8 c152 c160 c168 c200 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word)
         (LP OP n llv X Y E16 : Z) (gp tp x1 x5 x6 x7 x12 x13 x14 x15 x18 x20 x22 x24 x25 x27 x28 x29 x30 : word) (F : bvmap 5 word) (fc : bv 32),
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  v_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND ->
  X - LP = Y - OP -> OP <= Y -> Y < OP + n -> E16 = OP + n -> OP + n - Y <= Z.of_nat k ->
  evtF bsegs (v_RNG P) (sqs2_post P OEND LLO LEND LOCV c152 c160 c168 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n llv gp tp x20 x25 x27 F fc)
    (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) gp tp x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) (Z_to_bv 64 X) (Z_to_bv 64 Y) x12 x13 x14 x15 (Z_to_bv 64 E16) (Z_to_bv 64 n)
             x18 (Z_to_bv 64 X) x20 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 Y) x24 x25 (Z_to_bv 64 llv) x27 x28 x29 x30 (Z_to_bv 64 (v_DCTX P + 29896)))
        F (Z_to_bv 64 0x90ea4) fc None m1 (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros P OEND LLO LEND LOCV ST HLOC m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n llv X Y E16
    gp tp x1 x5 x6 x7 x12 x13 x14 x15 x18 x20 x22 x24 x25 x27 x28 x29 x30 F fc INV HOP HLLO HLE HOE HXY HY1 HY2 HE16 HK; [exfalso; lia|].
  subst E16. pose proof ST as ST0.
  sqs2_bufs ST INV.
  pose proof (sqs2_rg _ _ _ _ _ ST HLOC) as (RGL1 & RGL2 & _).
  destruct (APP (v_B0 P) (v_B1 P - v_B0 P) ltac:(lia) ltac:(right; lia)) as (ABB & _ & _).
  unfold app_blk in ABB. try unfold KLOW in ABB. try unfold KHIGH in ABB. try unfold KEND in ABB. clear APP.
  assert (MUL : munch [(Y, Y + 1); (v_FRB P - 2224, v_FRB P)] m1 m1) by apply munch_refl.
  assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  kx_autoFLAx [KAUnp X 1; KAUnp Y 1; KAApp Y 1] [0x90ea4; 0x90f88] 40%nat
    [KZRange X 4096 (2^47 - 1); KZRange Y 4096 (2^47 - 1); KZRange (OP + n) 0 (2^47); KZRange (OP + n - Y) 1 (2^47); KZWr Y 1]
    [(X, 1)] [(X, 1); (Y, 1)].
  all: try kx_z. all: try kx_acc RBUF. all: try sqs_aclose.
  all: kx_mem.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x90ea4) _ _ ?m2 _) =>
           eapply IH; [exact ST0 | exact HLOC | eapply BUFS; [exact MUL | exact WMl | first [exact KXMI | exact MI] | exact BUF | exact STK | sqs2_ar | sqs2_ar] | sqs2_ar ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x90f88) _ _ ?m2 _) =>
           sqs2_done c0 c8 c200; eapply BUFS; [exact MUL | exact WMl | first [exact KXMI | exact MI] | exact BUF | exact STK | sqs2_ar | sqs2_ar]
       end.
Qed.

Lemma sqs2_tl : forall (k : nat) P OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c0 c8 c152 c160 c168 c200 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word)
         (LP OP n llv X Y K E16 : Z) (gp tp x1 x5 x6 x7 x13 x14 x15 x18 x20 x22 x24 x25 x27 x28 x29 x30 : word) (F : bvmap 5 word) (fc : bv 32),
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  v_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND ->
  X - LP = Y - OP -> OP <= Y -> Y + K = OP + n -> 0 < K -> E16 = OP + n -> K <= Z.of_nat k ->
  evtF bsegs (v_RNG P) (sqs2_post P OEND LLO LEND LOCV c152 c160 c168 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n llv gp tp x20 x25 x27 F fc)
    (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) gp tp x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) (Z_to_bv 64 K) (Z_to_bv 64 X) (Z_to_bv 64 Y) x13 x14 x15 (Z_to_bv 64 E16) (Z_to_bv 64 n)
             x18 (Z_to_bv 64 X) x20 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 Y) x24 x25 (Z_to_bv 64 llv) x27 x28 x29 x30 (Z_to_bv 64 (v_DCTX P + 29896)))
        F (Z_to_bv 64 0x90f24) fc None m1 (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros P OEND LLO LEND LOCV ST HLOC m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n llv X Y K E16
    gp tp x1 x5 x6 x7 x13 x14 x15 x18 x20 x22 x24 x25 x27 x28 x29 x30 F fc INV HOP HLLO HLE HOE HXY HY1 HYK HK0 HE16 HK; [exfalso; lia|].
  subst E16. pose proof ST as ST0.
  sqs2_bufs ST INV.
  pose proof (sqs2_rg _ _ _ _ _ ST HLOC) as (RGL1 & RGL2 & _).
  destruct (APP (v_B0 P) (v_B1 P - v_B0 P) ltac:(lia) ltac:(right; lia)) as (ABB & _ & _).
  unfold app_blk in ABB. try unfold KLOW in ABB. try unfold KHIGH in ABB. try unfold KEND in ABB. clear APP.
  assert (MUL : munch [(Y, Y + 1); (v_FRB P - 2224, v_FRB P)] m1 m1) by apply munch_refl.
  assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  kx_autoFLAx [KAUnp X 1; KAUnp Y 1; KAApp Y 1] [0x90f24; 0x90f88] 40%nat
    [KZRange X 4096 (2^47 - 1); KZRange Y 4096 (2^47 - 1); KZRange K 1 (2^47); KZRange (OP + n) 0 (2^47); KZWr Y 1]
    [(X, 1)] [(X, 1); (Y, 1)].
  all: try kx_z. all: try kx_acc RBUF. all: try sqs_aclose.
  all: kx_mem.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x90f24) _ _ ?m2 _) =>
           eapply IH; [exact ST0 | exact HLOC | eapply BUFS; [exact MUL | exact WMl | first [exact KXMI | exact MI] | exact BUF | exact STK | sqs2_ar | sqs2_ar] | sqs2_ar ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x90f88) _ _ ?m2 _) =>
           sqs2_done c0 c8 c200; eapply BUFS; [exact MUL | exact WMl | first [exact KXMI | exact MI] | exact BUF | exact STK | sqs2_ar | sqs2_ar]
       end.
Qed.

Lemma sqs2_ffsz : forall P cw bc ptr sLL sOF sML p0 p1 p2 jpad, cells_size (sqs_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad) = 256%nat.
Proof. intros. destruct P. reflexivity. Qed.

Ltac sqs2_call ST tinv INV2 :=
  eapply evtF_cut;
  [ eapply sqs_copy_spec; [exact ST | tinv | sqs2_ar | sqs2_ar | sqs2_ar | left; split; sqs2_ar]
  | let ms' := fresh "ms'" in let PO := fresh "PO" in
    intros ms' PO; destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & INV2);
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia | reflexivity])
    end ].
Ltac sqs2_fclose TRANS MUL WMl FR FRF :=
  eapply TRANS;
  [ eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros ?x ?Hx; lia
  | exact WMl
  | assumption
  | rewrite sqs_frame_split; unfold sqs_fr_k1, sqs_fr_k2, sqs_fr_k3, sqs_fr_k4; cbn [app]; exact FR
  | eapply rw_cells_transport_pw; [exact FRF | exact MUL | exact WMl | intros ?x ?Hx; rewrite sqs2_ffsz in Hx; cbn [outside]; lia] ].

Lemma sqs2_wx : forall P OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c152 c160 c168 c200 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word)
         (LP OP n llv L22 E23 : Z) (gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x24 x25 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  sqs_linv P OEND LLO LEND LOCV m1 x25 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  c8 = Z_to_bv 64 (OP + n) -> c200 = Z_to_bv 64 n ->
  v_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND -> 32 <= n -> L22 = n - 32 -> E23 = OP + n - 32 ->
  evtF bsegs (v_RNG P) (sqs2_post P OEND LLO LEND LOCV c152 c160 c168 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n llv gp tp x20 x25 x27 F fc)
    (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) gp tp x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17
             x18 (Z_to_bv 64 LP) x20 (Z_to_bv 64 2147450880) (Z_to_bv 64 L22) (Z_to_bv 64 E23) x24 (Z_to_bv 64 OP) (Z_to_bv 64 llv) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x90e84) fc None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV ST HLOC m1 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n llv L22 E23
    gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x24 x25 x27 x28 x29 x30 x31 F fc INV E8 E200 HOP HLLO HLE HOE HN HL22 HE23.
  subst c8 c200 L22 E23. pose proof ST as ST0. pose proof INV as INV0.
  pose proof (sqs_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6).
  pose proof (sqs2_rg _ _ _ _ _ ST HLOC) as (RGL1 & RGL2 & RGLO & RGF47 & RGBL & RGFF & RGKH).
  apply (sqs_rg_k _ _ _ _ _ ST); intros RG1 RG2 RG3 RG4 RG5 RG6 RG7 RG8 RG9 RG10 RG11 RG12 RG13 RG14.
  apply (sqs_lopen_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV); intros jpad jseq FR FRF LENJ LENS SQB MI0 UFF USEQ RSQ RSQS.
  rewrite sqs_frame_split in FR. unfold sqs_fr_k1, sqs_fr_k2, sqs_fr_k3, sqs_fr_k4 in FR. cbn [app] in FR.
  clear FRF. hold INV0.
  kx_autoFLAx (@nil kza) [0x90f24] 20%nat
    [KZRange (v_FRB P) 4096 (2^47 - 384); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange n 32 (2^47); KZRange (n - 32) 0 (2^47)]
    [(v_FRB P, 280)] (@nil (Z * Z)).
  all: try kx_z. all: try kx_acc RG10. all: try sqs_aclose. all: kx_mem.
  unfold held in INV0.
  replace (Z_to_bv 64 (n + OP + -32)) with (Z_to_bv 64 (OP + n - 32)) by (f_equal; lia).
  replace (Z_to_bv 64 (LP + n + -32)) with (Z_to_bv 64 (LP + n - 32)) by (f_equal; lia).
  eapply (sqs2_tl 32%nat) with (X := LP + n - 32) (Y := OP + n - 32) (K := 32); [exact ST0 | exact HLOC | exact INV0 | sqs2_ar ..].
Qed.

Lemma sqs2_wl : forall (k : nat) P OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c152 c160 c168 c200 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word)
         (LP OP n llv D S L22 E23 : Z) (gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  sqs_linv P OEND LLO LEND LOCV m1 x25 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  c8 = Z_to_bv 64 (OP + n) -> c200 = Z_to_bv 64 n ->
  v_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND ->
  OP + 16 <= D -> D + 32 < OP + n -> S = LP + (D - OP) + 16 -> L22 = n - 32 -> E23 = OP + n - 32 -> OP + n - D <= Z.of_nat k ->
  evtF bsegs (v_RNG P) (sqs2_post P OEND LLO LEND LOCV c152 c160 c168 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n llv gp tp x20 x25 x27 F fc)
    (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) gp tp x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 D) (Z_to_bv 64 LP) x20 (Z_to_bv 64 2147450880) (Z_to_bv 64 L22) (Z_to_bv 64 E23) (Z_to_bv 64 S) (Z_to_bv 64 OP) (Z_to_bv 64 llv) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x90e58) fc None m1 (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros P OEND LLO LEND LOCV ST HLOC m1 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n llv D S L22 E23
    gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x27 x28 x29 x30 x31 F fc INV E8 E200 HOP HLLO HLE HOE HD1 HD2 HS HL22 HE23 HK; [exfalso; lia|].
  subst S L22 E23. pose proof ST as ST0.
  pose proof (sqs_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6).
  kx_autoFLAx (@nil kza) (@nil Z) 10%nat
    [KZRange D 4096 (2^47); KZRange (LP + (D - OP) + 16) 4096 (2^47); KZRange (OP + n - 32) 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
  all: try kx_z. all: kx_mem.
  sqs2_call ST0 ltac:(exact INV) INV2.
  kx_autoFLAx (@nil kza) (@nil Z) 10%nat
    [KZRange D 4096 (2^47); KZRange (LP + (D - OP) + 16) 4096 (2^47); KZRange (OP + n - 32) 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
  all: try kx_z. all: kx_mem.
  sqs2_call ST0 ltac:(exact INV2) INV3.
  kx_autoFLAx (@nil kza) [0x90e58; 0x90e84] 10%nat
    [KZRange D 4096 (2^47); KZRange (LP + (D - OP) + 16) 4096 (2^47); KZRange (OP + n - 32) 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
  all: try kx_z. all: kx_mem.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x90e58) _ _ _ _) =>
           eapply IH; [exact ST0 | exact HLOC | exact INV3 | first [eassumption | sqs2_ar] ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x90e84) _ _ _ _) =>
           eapply sqs2_wx; [exact ST0 | exact HLOC | exact INV3 | first [eassumption | sqs2_ar] ..]
       end.
Qed.

Lemma sqs2_w48 : forall P OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c152 c160 c168 c200 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word)
         (LP OP n llv L22 E23 : Z) (gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x24 x25 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  sqs_linv P OEND LLO LEND LOCV m1 x25 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  c8 = Z_to_bv 64 (OP + n) -> c200 = Z_to_bv 64 n ->
  v_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND -> 32 <= n -> L22 = n - 32 -> E23 = OP + n - 32 ->
  evtF bsegs (v_RNG P) (sqs2_post P OEND LLO LEND LOCV c152 c160 c168 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n llv gp tp x20 x25 x27 F fc)
    (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) gp tp x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17
             x18 (Z_to_bv 64 LP) x20 (Z_to_bv 64 2147450880) (Z_to_bv 64 L22) (Z_to_bv 64 E23) x24 (Z_to_bv 64 OP) (Z_to_bv 64 llv) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x90e48) fc None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV ST HLOC m1 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n llv L22 E23
    gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x24 x25 x27 x28 x29 x30 x31 F fc INV E8 E200 HOP HLLO HLE HOE HN HL22 HE23.
  subst L22 E23. pose proof ST as ST0.
  pose proof (sqs_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6).
  kx_autoFLAx (@nil kza) [0x90e58; 0x90e84] 20%nat
    [KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange n 32 (2^47); KZRange (n - 32) 0 (2^47); KZRange (OP + n - 32) 4096 (2^47)]
    (@nil (Z * Z)) (@nil (Z * Z)).
  all: try kx_z. all: kx_mem.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x90e58) _ _ _ _) =>
           eapply (sqs2_wl (Z.to_nat n)); [exact ST0 | exact HLOC | exact INV | first [eassumption | reflexivity | sqs2_ar] ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x90e84) _ _ _ _) =>
           eapply sqs2_wx; [exact ST0 | exact HLOC | exact INV | first [eassumption | reflexivity | sqs2_ar] ..]
       end.
Qed.

Lemma sqs2_wild : forall P OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c152 c160 c168 c200 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word)
         (LP OP n llv E16 E23 : Z) (gp tp x1 x5 x6 x7 x11 x12 x13 x14 x15 x18 x20 x22 x24 x25 x27 x28 x29 x30 : word) (F : bvmap 5 word) (fc : bv 32),
  sqs_linv P OEND LLO LEND LOCV m1 x25 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  v_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND -> 32 <= n -> E16 = OP + n -> E23 = OP + n - 32 ->
  evtF bsegs (v_RNG P) (sqs2_post P OEND LLO LEND LOCV c152 c160 c168 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n llv gp tp x20 x25 x27 F fc)
    (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) gp tp x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) (Z_to_bv 64 OP) x11 x12 x13 x14 x15 (Z_to_bv 64 E16) (Z_to_bv 64 n)
             x18 (Z_to_bv 64 LP) x20 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 E23) x24 x25 (Z_to_bv 64 llv) x27 x28 x29 x30 (Z_to_bv 64 (v_DCTX P + 29896)))
        F (Z_to_bv 64 0x90e2c) fc None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV ST HLOC m1 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n llv E16 E23
    gp tp x1 x5 x6 x7 x11 x12 x13 x14 x15 x18 x20 x22 x24 x25 x27 x28 x29 x30 F fc INV HOP HLLO HLE HOE HN HE16 HE23.
  subst E16 E23. pose proof ST as ST0.
  pose proof (sqs_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6).
  pose proof (sqs2_rg _ _ _ _ _ ST HLOC) as (RGL1 & RGL2 & RGLO & RGF47 & RGBL & RGFF & RGKH).
  apply (sqs_rg_k _ _ _ _ _ ST); intros RG1 RG2 RG3 RG4 RG5 RG6 RG7 RG8 RG9 RG10 RG11 RG12 RG13 RG14.
  pose proof (sqs_linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  apply (sqs_lopen_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV); intros jpad jseq FR FRF LENJ LENS SQB MI0 UFF USEQ RSQ RSQS.
  rewrite sqs_frame_split in FR. unfold sqs_fr_k1, sqs_fr_k2, sqs_fr_k3, sqs_fr_k4 in FR. cbn [app] in FR.
  hold FRF. hold TRANS.
  assert (MUL : munch [(v_FRB P, v_FRB P + 280)] m1 m1) by apply munch_refl.
  assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  kx_autoFLAx [KAApp (v_FRB P) 280] (@nil Z) 20%nat
    [KZRange (v_FRB P) 4096 (2^47 - 384); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange n 32 (2^47); KZRange (OP + n - 32) 4096 (2^47); KZWr (v_FRB P) 280]
    [(v_FRB P, 280)] [(v_FRB P, 280)].
  all: try kx_z. all: try kx_acc RG10. all: try sqs_aclose. all: kx_mem.
  unfold held in FRF, TRANS.
  sqs2_call ST0 ltac:(sqs2_fclose TRANS MUL WMl FR FRF) INV2.
  eapply sqs2_w48; [exact ST0 | exact HLOC | exact INV2 | first [reflexivity | eassumption | sqs2_ar] ..].
Qed.

Lemma sqs2_site : forall P OEND LLO LEND LOCV (m1 : amem) (c0 c8 c152 c160 c168 c200 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP OP n llv : Z)
         (gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x18 x20 x22 x24 x25 x27 x28 x29 x30 : word) (F : bvmap 5 word) (fc : bv 32),
  sqs_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  v_DST P <= OP -> 0 < n -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND ->
  evtF bsegs (v_RNG P) (sqs2_post P OEND LLO LEND LOCV c152 c160 c168 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n llv gp tp x20 x25 x27 F fc)
    (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) gp tp x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 n)
             x18 (Z_to_bv 64 LP) x20 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 OP) x24 x25 (Z_to_bv 64 llv) x27 x28 x29 x30 (Z_to_bv 64 (v_DCTX P + 29896)))
        F (Z_to_bv 64 0x90dfc) fc None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n llv
    gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x18 x20 x22 x24 x25 x27 x28 x29 x30 F fc ST HLOC INV HOP HN HLLO HLE HOE.
  pose proof ST as ST0. pose proof INV as INV0.
  pose proof (sqs_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6).
  pose proof (sqs2_rg _ _ _ _ _ ST HLOC) as (RGL1 & RGL2 & RGLO & RGF47 & RGBL & RGFF & RGKH).
  apply (sqs_rg_k _ _ _ _ _ ST); intros RG1 RG2 RG3 RG4 RG5 RG6 RG7 RG8 RG9 RG10 RG11 RG12 RG13 RG14.
  pose proof (sqs_linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  apply (sqs_lopen_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV); intros jpad jseq FR FRF LENJ LENS SQB MI0 UFF USEQ RSQ RSQS.
  rewrite sqs_frame_split in FR. unfold sqs_fr_k1, sqs_fr_k2, sqs_fr_k3, sqs_fr_k4 in FR. cbn [app] in FR.
  hold FRF. hold TRANS. hold INV0.
  assert (MUL : munch [(v_FRB P, v_FRB P + 280)] m1 m1) by apply munch_refl.
  assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  kx_autoFLAx [KAApp (v_FRB P) 280] [0x90ea4; 0x90f24; 0x90e2c] 30%nat
    [KZRange (v_FRB P) 4096 (2^47 - 384); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange n 1 (2^47); KZRange (OP + n) 4096 (2^47); KZWr (v_FRB P) 280]
    [(v_FRB P, 280)] [(v_FRB P, 280)].
  all: try kx_z. all: try kx_acc RG10. all: try sqs_aclose. all: kx_mem.
  all: unfold held in FRF, TRANS, INV0.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x90ea4) _ _ _ _) =>
           eapply (sqs2_bl (Z.to_nat n)); [exact ST0 | exact HLOC | exact INV0 | sqs2_ar ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x90f24) _ _ _ _) =>
           eapply (sqs2_tl (Z.to_nat n)); [exact ST0 | exact HLOC | sqs2_fclose TRANS MUL WMl FR FRF | sqs2_ar ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x90e2c) _ _ _ _) =>
           eapply sqs2_wild; [exact ST0 | exact HLOC | sqs2_fclose TRANS MUL WMl FR FRF | sqs2_ar ..]
       end.
Qed.

End CANSEC1.
