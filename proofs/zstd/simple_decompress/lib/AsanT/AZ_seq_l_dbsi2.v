From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_lkit2 AZ_seq_l_v_la.
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

Definition sqd2_post (P : slq) (OEND LLO LEND LOCV : Z) (c8 c16 c24 c32 c88 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c336 c352 c368 c376 cw : word)
    (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP OP n : Z) (gp tp x8 x21 x22 x27 : word) (F : bvmap 5 word) (fc : bv 32)
    : machine_state -> Prop :=
  fun ms' => exists (m2 : amem) (c96 c328 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x24 x26 x28 x29 x30 : word),
    ms' = MS (mkR x1 (Z_to_bv 64 (l_FRB P)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 (OP + n)) x17
               (Z_to_bv 64 2147450880) (Z_to_bv 64 (OP + n)) (Z_to_bv 64 n) x21 x22 x23 x24 (Z_to_bv 64 (LP + n)) x26 x27 x28 x29 x30
               (Z_to_bv 64 (l_DCTX P + 30368)))
             F (Z_to_bv 64 0x8d290) fc None m2 (seg_rom bsegs) /\
    sql_linv P OEND LLO LEND LOCV m2 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP.

Ltac sqd2_ar := solve [lia | kx_bv_ranges; kx_lia_pruned].
Ltac sqd2_ms := repeat lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal
  | |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => f_equal
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; sqd2_ar
  end.
Ltac sqd2_done c96 c328 :=
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR ?r1 _ _ _ ?r5 ?r6 ?r7 _ _ ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 _ ?r17 _ _ _ _ _ ?r23 ?r24 _ ?r26 _ ?r28 ?r29 ?r30 _) _ _ _ _ ?mm _) =>
      apply evtF_done; unfold sqd2_post;
      exists mm, c96, c328, r1, r5, r6, r7, r10, r11, r12, r13, r14, r15, r17, r23, r24, r26, r28, r29, r30;
      split; [sqd2_ms|]
  end.

Lemma sqd2_rg : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  l_B0 P <= LLO /\ LEND + 32 <= l_B1 P /\ l_lo P <= l_FRB P - 2224 /\ l_FRB P + 672 <= 2^47 /\
  (l_B1 P <= l_lo P \/ l_FRB P <= l_B0 P) /\ l_FF P + 256 <= l_FRB P /\ KHIGH <= l_FRB P.
Proof.
  intros P OEND LLO LEND LOCV ST HLOC.
  apply (sql_rg_k _ _ _ _ _ ST); intros RG1 RG2 RG3 RG4 RG5 RG6 RG7 RG8 RG9 RG10 RG11 RG12 RG13 RG14.
  split; [|split; [|split; [|split; [|split; [|split; [clear - RG8; lia | unfold KHIGH; clear - RG7; lia]]]]]].
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  all: cbn [l_B0 l_B1 l_FF l_FRB l_lo] in *; sd_static_open ST; unfold held in S24, S42.
  - clear - S1 S2 S3 S4 S5 S6 S7 S42 HLOC; lia.
  - clear - S1 S2 S3 S4 S5 S6 S7 S42 HLOC; lia.
  - clear - S17 S18 S47; lia.
  - clear - S17 S18 S47; lia.
  - clear - S17 S18 S47 S24; lia.
Qed.

Ltac sqd2_bufs ST INV :=
  pose proof (sql_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6);
  pose proof (sql_copy_asan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (ART & AST & APP);
  pose proof (sql_linv_buf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as BUFS;
  pose proof (sql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI;
  apply (sql_buf_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV); intros BUFB UBUF RBUF RBUFS GRAN U32 R32 RS32 U64 R64 RS64 TBG;
  clear GRAN U32 R32 RS32 U64 R64 RS64 TBG.

Lemma sqd2_bl : forall (k : nat) P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z)
         (LP OP n X Y E16 : Z) (gp tp x1 x5 x6 x7 x8 x12 x13 x14 x15 x17 x21 x22 x23 x24 x26 x27 x28 x29 x30 : word) (F : bvmap 5 word) (fc : bv 32),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  l_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND ->
  X - LP = Y - OP -> OP <= Y -> Y < OP + n -> E16 = OP + n -> OP + n - Y <= Z.of_nat k ->
  evtF bsegs (l_RNG P) (sqd2_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n gp tp x8 x21 x22 x27 F fc)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (l_FRB P)) (Z_to_bv 64 X) (Z_to_bv 64 Y) x12 x13 x14 x15 (Z_to_bv 64 E16) x17
             (Z_to_bv 64 2147450880) (Z_to_bv 64 Y) (Z_to_bv 64 n) x21 x22 x23 x24 (Z_to_bv 64 X) x26 x27 x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368)))
        F (Z_to_bv 64 0x8d1c4) fc None m1 (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros P OEND LLO LEND LOCV ST HLOC m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n X Y E16
    gp tp x1 x5 x6 x7 x8 x12 x13 x14 x15 x17 x21 x22 x23 x24 x26 x27 x28 x29 x30 F fc INV HOP HLLO HLE HOE HXY HY1 HY2 HE16 HK; [exfalso; lia|].
  subst E16. pose proof ST as ST0.
  sqd2_bufs ST INV.
  pose proof (sqd2_rg _ _ _ _ _ ST HLOC) as (RGL1 & RGL2 & _).
  destruct (APP (l_B0 P) (l_B1 P - l_B0 P) ltac:(lia) ltac:(right; lia)) as (ABB & _ & _).
  unfold app_blk in ABB. try unfold KLOW in ABB. try unfold KHIGH in ABB. try unfold KEND in ABB. clear APP.
  assert (MUL : munch [(Y, Y + 1); (l_FRB P - 2224, l_FRB P)] m1 m1) by apply munch_refl.
  assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  kx_autoFLAx [KAUnp X 1; KAUnp Y 1; KAApp Y 1] [0x8d1c4; 0x8d290] 40%nat
    [KZRange X 4096 (2^47 - 1); KZRange Y 4096 (2^47 - 1); KZRange (OP + n) 0 (2^47); KZRange (OP + n - Y) 1 (2^47); KZWr Y 1]
    [(X, 1)] [(X, 1); (Y, 1)].
  all: try kx_z. all: try kx_acc RBUF. all: try sql_aclose.
  all: kx_mem.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8d1c4) _ _ ?m2 _) =>
           eapply IH; [exact ST0 | exact HLOC | eapply BUFS; [exact MUL | exact WMl | first [exact KXMI | exact MI] | exact BUF | exact STK | sqd2_ar | sqd2_ar] | sqd2_ar ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8d290) _ _ ?m2 _) =>
           sqd2_done c96 c328; eapply BUFS; [exact MUL | exact WMl | first [exact KXMI | exact MI] | exact BUF | exact STK | sqd2_ar | sqd2_ar]
       end.
Qed.

Lemma sqd2_tl : forall (k : nat) P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z)
         (LP OP n X Y K E16 E19 : Z) (gp tp x1 x5 x6 x7 x8 x13 x14 x15 x17 x21 x22 x23 x26 x27 x28 x29 x30 : word) (F : bvmap 5 word) (fc : bv 32),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  l_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND ->
  X - LP = Y - OP -> OP <= Y -> Y + K = OP + n -> 0 < K -> E16 = OP + n -> E19 = OP + n -> K <= Z.of_nat k ->
  evtF bsegs (l_RNG P) (sqd2_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n gp tp x8 x21 x22 x27 F fc)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (l_FRB P)) (Z_to_bv 64 K) (Z_to_bv 64 X) (Z_to_bv 64 Y) x13 x14 x15 (Z_to_bv 64 E16) x17
             (Z_to_bv 64 2147450880) (Z_to_bv 64 E19) (Z_to_bv 64 n) x21 x22 x23 (Z_to_bv 64 Y) (Z_to_bv 64 X) x26 x27 x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368)))
        F (Z_to_bv 64 0x8d234) fc None m1 (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros P OEND LLO LEND LOCV ST HLOC m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n X Y K E16 E19
    gp tp x1 x5 x6 x7 x8 x13 x14 x15 x17 x21 x22 x23 x26 x27 x28 x29 x30 F fc INV HOP HLLO HLE HOE HXY HY1 HYK HK0 HE16 HE19 HK; [exfalso; lia|].
  subst E16 E19. pose proof ST as ST0.
  sqd2_bufs ST INV.
  pose proof (sqd2_rg _ _ _ _ _ ST HLOC) as (RGL1 & RGL2 & _).
  destruct (APP (l_B0 P) (l_B1 P - l_B0 P) ltac:(lia) ltac:(right; lia)) as (ABB & _ & _).
  unfold app_blk in ABB. try unfold KLOW in ABB. try unfold KHIGH in ABB. try unfold KEND in ABB. clear APP.
  assert (MUL : munch [(Y, Y + 1); (l_FRB P - 2224, l_FRB P)] m1 m1) by apply munch_refl.
  assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  kx_autoFLAx [KAUnp X 1; KAUnp Y 1; KAApp Y 1] [0x8d234; 0x8d290] 40%nat
    [KZRange X 4096 (2^47 - 1); KZRange Y 4096 (2^47 - 1); KZRange K 1 (2^47); KZWr Y 1]
    [(X, 1)] [(X, 1); (Y, 1)].
  all: try kx_z. all: try kx_acc RBUF. all: try sql_aclose.
  all: kx_mem.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8d234) _ _ ?m2 _) =>
           eapply IH; [exact ST0 | exact HLOC | eapply BUFS; [exact MUL | exact WMl | first [exact KXMI | exact MI] | exact BUF | exact STK | sqd2_ar | sqd2_ar] | sqd2_ar ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8d290) _ _ ?m2 _) =>
           sqd2_done c96 c328; eapply BUFS; [exact MUL | exact WMl | first [exact KXMI | exact MI] | exact BUF | exact STK | sqd2_ar | sqd2_ar]
       end.
Qed.

Lemma sqd2_ffsz : forall P cw bc ptr sLL sOF sML p0 p1 p2 jpad, cells_size (sql_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad) = 256%nat.
Proof. intros. destruct P. reflexivity. Qed.

Ltac sqd2_call ST tinv INV2 :=
  eapply evtF_cut;
  [ eapply sql_copy_spec; [exact ST | tinv | sqd2_ar | sqd2_ar | sqd2_ar | left; split; sqd2_ar]
  | let ms' := fresh "ms'" in let PO := fresh "PO" in
    intros ms' PO; destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & INV2);
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia | reflexivity])
    end ].
Ltac sqd2_fclose TRANS MUL WMl FR LENJ LENS FRF :=
  eapply TRANS;
  [ eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros ?x ?Hx; lia
  | exact WMl
  | assumption
  | eapply sql_fr_ula; [exact FR | exact LENJ | exact LENS]
  | eapply rw_cells_transport_pw; [exact FRF | exact MUL | exact WMl | intros ?x ?Hx; rewrite sqd2_ffsz in Hx; cbn [outside]; lia] ].

Lemma sqd2_wx : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z)
         (LP OP n E24 : Z) (gp tp x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  c96 = Z_to_bv 64 (OP + n) -> c328 = Z_to_bv 64 (n - 32) ->
  l_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND -> 32 <= n -> E24 = OP + n - 32 ->
  evtF bsegs (l_RNG P) (sqd2_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n gp tp x8 x21 x22 x27 F fc)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) (Z_to_bv 64 n) x21 x22 x23 (Z_to_bv 64 E24) (Z_to_bv 64 LP) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8cf2c) fc None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV ST HLOC m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n E24
    gp tp x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x26 x27 x28 x29 x30 x31 F fc INV E96 E328 HOP HLLO HLE HOE HN HE24.
  subst c96 c328 E24. pose proof ST as ST0. pose proof INV as INV0.
  pose proof (sql_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6).
  pose proof (sqd2_rg _ _ _ _ _ ST HLOC) as (RGL1 & RGL2 & RGLO & RGF47 & RGBL & RGFF & RGKH).
  apply (sql_rg_k _ _ _ _ _ ST); intros RG1 RG2 RG3 RG4 RG5 RG6 RG7 RG8 RG9 RG10 RG11 RG12 RG13 RG14.
  apply (sql_lopen_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV); intros jpad jseq FR FRF LENJ LENS SQB MI0 UFF USEQ RSQ RSQS.
  apply sql_fr_vla in FR. clear FRF.
  kx_autoFLAx (@nil kza) [0x8d234] 20%nat
    [KZRange (l_FRB P) 4096 (2^47 - 672); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange n 32 (2^47); KZRange (n - 32) 0 (2^47)]
    [(l_FRB P, 568)] (@nil (Z * Z)).
  all: try kx_z. all: try kx_acc RG10. all: try sql_aclose. all: kx_mem.
  eapply (sqd2_tl 32%nat); [exact ST0 | exact HLOC | exact INV0 | sqd2_ar ..].
Qed.

Lemma sqd2_wl : forall (k : nat) P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z)
         (LP OP n D S E24 : Z) (gp tp x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  c96 = Z_to_bv 64 (OP + n) -> c328 = Z_to_bv 64 (n - 32) ->
  l_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND ->
  OP + 16 <= D -> D + 32 < OP + n -> S = LP + (D - OP) + 16 -> E24 = OP + n - 32 -> OP + n - D <= Z.of_nat k ->
  evtF bsegs (l_RNG P) (sqd2_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n gp tp x8 x21 x22 x27 F fc)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) (Z_to_bv 64 n) x21 x22 (Z_to_bv 64 D) (Z_to_bv 64 E24) (Z_to_bv 64 LP) (Z_to_bv 64 S) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8cf00) fc None m1 (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros P OEND LLO LEND LOCV ST HLOC m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n D S E24
    gp tp x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x27 x28 x29 x30 x31 F fc INV E96 E328 HOP HLLO HLE HOE HD1 HD2 HS HE24 HK; [exfalso; lia|].
  subst S E24. pose proof ST as ST0.
  pose proof (sql_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6).
  kx_autoFLAx (@nil kza) (@nil Z) 10%nat
    [KZRange D 4096 (2^47); KZRange (LP + (D - OP) + 16) 4096 (2^47); KZRange (OP + n - 32) 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
  all: try kx_z. all: kx_mem.
  sqd2_call ST0 ltac:(exact INV) INV2.
  kx_autoFLAx (@nil kza) (@nil Z) 10%nat
    [KZRange D 4096 (2^47); KZRange (LP + (D - OP) + 16) 4096 (2^47); KZRange (OP + n - 32) 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
  all: try kx_z. all: kx_mem.
  sqd2_call ST0 ltac:(exact INV2) INV3.
  kx_autoFLAx (@nil kza) [0x8cf00; 0x8cf2c] 10%nat
    [KZRange D 4096 (2^47); KZRange (LP + (D - OP) + 16) 4096 (2^47); KZRange (OP + n - 32) 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
  all: try kx_z. all: kx_mem.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8cf00) _ _ _ _) =>
           eapply IH; [exact ST0 | exact HLOC | exact INV3 | first [eassumption | sqd2_ar] ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8cf2c) _ _ _ _) =>
           eapply sqd2_wx; [exact ST0 | exact HLOC | exact INV3 | first [eassumption | sqd2_ar] ..]
       end.
Qed.

Lemma sqd2_w88 : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z)
         (LP OP n L23 E24 : Z) (gp tp x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  c96 = Z_to_bv 64 (OP + n) ->
  l_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND -> 32 <= n -> L23 = n - 32 -> E24 = OP + n - 32 ->
  evtF bsegs (l_RNG P) (sqd2_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n gp tp x8 x21 x22 x27 F fc)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) (Z_to_bv 64 n) x21 x22 (Z_to_bv 64 L23) (Z_to_bv 64 E24) (Z_to_bv 64 LP) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8ceec) fc None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV ST HLOC m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n L23 E24
    gp tp x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x26 x27 x28 x29 x30 x31 F fc INV E96 HOP HLLO HLE HOE HN HL23 HE24.
  subst L23 E24. pose proof ST as ST0.
  pose proof (sql_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6).
  pose proof (sqd2_rg _ _ _ _ _ ST HLOC) as (RGL1 & RGL2 & RGLO & RGF47 & RGBL & RGFF & RGKH).
  apply (sql_rg_k _ _ _ _ _ ST); intros RG1 RG2 RG3 RG4 RG5 RG6 RG7 RG8 RG9 RG10 RG11 RG12 RG13 RG14.
  pose proof (sql_linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  apply (sql_lopen_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV); intros jpad jseq FR FRF LENJ LENS SQB MI0 UFF USEQ RSQ RSQS.
  apply sql_fr_vla in FR. hold FRF. hold TRANS.
  assert (MUL : munch [(l_FRB P, l_FRB P + 568)] m1 m1) by apply munch_refl.
  assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  kx_autoFLAx [KAApp (l_FRB P) 568] [0x8cf00; 0x8cf2c] 20%nat
    [KZRange (l_FRB P) 4096 (2^47 - 672); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange n 32 (2^47); KZRange (n - 32) 0 (2^47); KZWr (l_FRB P) 568]
    [(l_FRB P, 568)] [(l_FRB P, 568)].
  all: try kx_z. all: try kx_acc RG10. all: try sql_aclose. all: kx_mem.
  all: unfold held in FRF, TRANS.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8cf00) _ _ _ _) =>
           eapply (sqd2_wl (Z.to_nat n)); [exact ST0 | exact HLOC | sqd2_fclose TRANS MUL WMl FR LENJ LENS FRF | first [eassumption | reflexivity | sqd2_ar] ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8cf2c) _ _ _ _) =>
           eapply sqd2_wx; [exact ST0 | exact HLOC | sqd2_fclose TRANS MUL WMl FR LENJ LENS FRF | first [eassumption | reflexivity | sqd2_ar] ..]
       end.
Qed.

Lemma sqd2_wild : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z)
         (LP OP n E16 E24 : Z) (gp tp x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x17 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  l_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND -> 32 <= n -> E16 = OP + n -> E24 = OP + n - 32 ->
  evtF bsegs (l_RNG P) (sqd2_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n gp tp x8 x21 x22 x27 F fc)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 E16) x17
             (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) (Z_to_bv 64 n) x21 x22 x23 (Z_to_bv 64 E24) (Z_to_bv 64 LP) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8ced4) fc None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV ST HLOC m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n E16 E24
    gp tp x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x17 x21 x22 x23 x26 x27 x28 x29 x30 x31 F fc INV HOP HLLO HLE HOE HN HE16 HE24.
  subst E16 E24. pose proof ST as ST0.
  pose proof (sql_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6).
  pose proof (sqd2_rg _ _ _ _ _ ST HLOC) as (RGL1 & RGL2 & RGLO & RGF47 & RGBL & RGFF & RGKH).
  apply (sql_rg_k _ _ _ _ _ ST); intros RG1 RG2 RG3 RG4 RG5 RG6 RG7 RG8 RG9 RG10 RG11 RG12 RG13 RG14.
  pose proof (sql_linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  apply (sql_lopen_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV); intros jpad jseq FR FRF LENJ LENS SQB MI0 UFF USEQ RSQ RSQS.
  apply sql_fr_vla in FR. hold FRF. hold TRANS.
  assert (MUL : munch [(l_FRB P, l_FRB P + 568)] m1 m1) by apply munch_refl.
  assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  kx_autoFLAx [KAApp (l_FRB P) 568] (@nil Z) 20%nat
    [KZRange (l_FRB P) 4096 (2^47 - 672); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange n 32 (2^47); KZRange (OP + n - 32) 4096 (2^47); KZWr (l_FRB P) 568]
    [(l_FRB P, 568)] [(l_FRB P, 568)].
  all: try kx_z. all: try kx_acc RG10. all: try sql_aclose. all: kx_mem.
  unfold held in FRF, TRANS.
  sqd2_call ST0 ltac:(sqd2_fclose TRANS MUL WMl FR LENJ LENS FRF) INV2.
  eapply sqd2_w88; [exact ST0 | exact HLOC | exact INV2 | first [reflexivity | eassumption | sqd2_ar] ..].
Qed.

Lemma sqd2_site : forall P OEND LLO LEND LOCV (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word)
         (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP OP n : Z)
         (gp tp x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x26 x27 x28 x29 x30 : word) (F : bvmap 5 word) (fc : bv 32),
  sql_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  l_DST P <= OP -> 0 < n -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND ->
  evtF bsegs (l_RNG P) (sqd2_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n gp tp x8 x21 x22 x27 F fc)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) (Z_to_bv 64 n) x21 x22 x23 x24 (Z_to_bv 64 LP) x26 x27 x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368)))
        F (Z_to_bv 64 0x8ceac) fc None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n
    gp tp x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x26 x27 x28 x29 x30 F fc ST HLOC INV HOP HN HLLO HLE HOE.
  pose proof ST as ST0.
  pose proof (sql_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6).
  kx_autoFLAx (@nil kza) [0x8d1c4; 0x8d234; 0x8ced4] 20%nat
    [KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange n 1 (2^47); KZRange (OP + n) 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
  all: try kx_z. all: kx_mem.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8d1c4) _ _ _ _) =>
           eapply (sqd2_bl (Z.to_nat n)); [exact ST0 | exact HLOC | exact INV | sqd2_ar ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8d234) _ _ _ _) =>
           eapply (sqd2_tl (Z.to_nat n)); [exact ST0 | exact HLOC | exact INV | sqd2_ar ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ced4) _ _ _ _) =>
           eapply sqd2_wild; [exact ST0 | exact HLOC | exact INV | sqd2_ar ..]
       end.
Qed.

End CANSEC1.
