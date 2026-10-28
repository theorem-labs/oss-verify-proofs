From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_lkit2 AZ_seq_l_v_lt.
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

Definition sqd1_post (P : slq) (OEND LLO LEND LOCV : Z) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 : word) (raddr : Z)
    (c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP OP n : Z)
    : machine_state -> Prop :=
  fun ms' => exists (m2 : amem) (c304 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x25 x26 x28 x29 x30 : word),
    ms' = (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 raddr) x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 (OP + n)) (Z_to_bv 64 (OP + n)) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) x23 (Z_to_bv 64 (LP + n)) x25 x26 (Z_to_bv 64 n) x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x8b6c0) (l_fc P) None m2 (seg_rom bsegs)) /\
    sql_linv P OEND LLO LEND LOCV m2 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 (Z_to_bv 64 raddr) c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP.

Ltac sqd1_regs := repeat match goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal
  | |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => f_equal
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; solve [lia | kx_bv_ranges; kx_lia_pruned]
  end.
Ltac sqd1_done c304 :=
  lazymatch goal with |- evtF _ _ _ (MS (mkR ?r1 _ _ _ ?r5 ?r6 ?r7 _ _ ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 _ ?r17 _ _ _ _ _ ?r23 _ ?r25 ?r26 _ ?r28 ?r29 ?r30 _) _ _ _ _ ?mm _) =>
    apply evtF_done; unfold sqd1_post; exists mm, c304, r1, r5, r6, r7, r10, r11, r12, r13, r14, r15, r17, r23, r25, r26, r28, r29, r30;
    split; [sqd1_regs|]
  end.
Ltac sqd1_ar := solve [lia | kx_bv_ranges; kx_lia_pruned].

Lemma sqd1_bl : forall (k : nat) P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP OP n raddr X Y : Z) (x1 x5 x6 x7 x12 x13 x14 x15 x17 x23 x25 x26 x28 x29 x30 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 (Z_to_bv 64 raddr) c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  l_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND ->
  X - LP = Y - OP -> OP <= Y -> Y < OP + n -> OP + n - Y <= Z.of_nat k ->
  evtF bsegs (l_RNG P) (sqd1_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 raddr c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) (Z_to_bv 64 X) (Z_to_bv 64 Y) x12 x13 x14 x15 (Z_to_bv 64 raddr) x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 Y) (Z_to_bv 64 (OP + n)) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) x23 (Z_to_bv 64 X) x25 x26 (Z_to_bv 64 n) x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x8b5e8) (l_fc P) None m1 (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros P OEND LLO LEND LOCV ST HLOC m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n raddr X Y x1 x5 x6 x7 x12 x13 x14 x15 x17 x23 x25 x26 x28 x29 x30
    INV HOP HLLO HLE HOE HXY HY1 HY2 HK; [exfalso; lia|].
  pose proof ST as ST0.
  pose proof (sql_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6).
  pose proof (sql_copy_asan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (ART & AST & APP).
  pose proof (sql_linv_buf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as BUFS.
  pose proof (sql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  apply (sql_buf_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV); intros BUFB UBUF RBUF RBUFS GRAN U32 R32 RS32 U64 R64 RS64 TBG.
  clear GRAN U32 R32 RS32 U64 R64 RS64 TBG.
  assert (RGL : l_B0 P <= LLO /\ LEND + 32 <= l_B1 P).
  { clear - ST HLOC. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in *. sd_static_open ST. unfold held in *. destruct (S71 HLOC) as (ELLO & ELEND & _).
    clear - S1 S2 S3 S4 S5 S6 S7 S9 S11 S17 S18 S42 S47 HLOC ELLO ELEND. lia. }
  assert (RGB0 : l_B0 P < l_B1 P) by lia.
  destruct (APP (l_B0 P) (l_B1 P - l_B0 P) ltac:(lia) ltac:(right; lia)) as (ABB & _ & _).
  unfold app_blk in ABB. try unfold KLOW in ABB. try unfold KHIGH in ABB. try unfold KEND in ABB.
  clear APP.
  assert (MUL : munch [(Y, Y + 1); (l_FRB P - 2224, l_FRB P)] m1 m1) by apply munch_refl.
  assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  kx_autoFLAx [KAUnp X 1; KAUnp Y 1; KAApp Y 1] [0x8b5e8; 0x8b6c0] 40%nat
    [KZRange X 4096 (2^47 - 1); KZRange Y 4096 (2^47 - 1); KZRange (OP + n) 0 (2^47); KZRange (OP + n - Y) 1 (2^47); KZWr Y 1]
    [(X, 1)] [(X, 1); (Y, 1)].
  all: try kx_z. all: try kx_acc RBUF. all: try sql_aclose.
  all: kx_mem.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8b5e8) _ _ ?m2 _) =>
           eapply IH; [exact ST0 | exact HLOC | eapply BUFS; [exact MUL | exact WMl | first [exact KXMI | exact MI] | exact BUF | exact STK | sqd1_ar | sqd1_ar] | sqd1_ar ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8b6c0) _ _ ?m2 _) =>
           sqd1_done c304; eapply BUFS; [exact MUL | exact WMl | first [exact KXMI | exact MI] | exact BUF | exact STK | sqd1_ar | sqd1_ar]
       end.
Qed.

Lemma sqd1_tl : forall (k : nat) P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP OP n raddr X Y K : Z) (x1 x5 x6 x7 x13 x14 x15 x17 x23 x26 x28 x29 x30 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 (Z_to_bv 64 raddr) c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  l_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND ->
  X - LP = Y - OP -> OP <= Y -> Y + K = OP + n -> 0 < K -> K <= Z.of_nat k ->
  evtF bsegs (l_RNG P) (sqd1_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 raddr c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) (Z_to_bv 64 K) (Z_to_bv 64 X) (Z_to_bv 64 Y) x13 x14 x15 (Z_to_bv 64 raddr) x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 (OP + n)) (Z_to_bv 64 (OP + n)) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) x23 (Z_to_bv 64 X) (Z_to_bv 64 Y) x26 (Z_to_bv 64 n) x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x8b664) (l_fc P) None m1 (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros P OEND LLO LEND LOCV ST HLOC m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n raddr X Y K x1 x5 x6 x7 x13 x14 x15 x17 x23 x26 x28 x29 x30
    INV HOP HLLO HLE HOE HXY HY1 HYK HK0 HK; [exfalso; lia|].
  pose proof ST as ST0.
  pose proof (sql_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6).
  pose proof (sql_copy_asan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (ART & AST & APP).
  pose proof (sql_linv_buf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as BUFS.
  pose proof (sql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  apply (sql_buf_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV); intros BUFB UBUF RBUF RBUFS GRAN U32 R32 RS32 U64 R64 RS64 TBG.
  clear GRAN U32 R32 RS32 U64 R64 RS64 TBG.
  assert (RGL : l_B0 P <= LLO /\ LEND + 32 <= l_B1 P).
  { clear - ST HLOC. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in *. sd_static_open ST. unfold held in *. destruct (S71 HLOC) as (ELLO & ELEND & _).
    clear - S1 S2 S3 S4 S5 S6 S7 S9 S11 S17 S18 S42 S47 HLOC ELLO ELEND. lia. }
  assert (RGB0 : l_B0 P < l_B1 P) by lia.
  destruct (APP (l_B0 P) (l_B1 P - l_B0 P) ltac:(lia) ltac:(right; lia)) as (ABB & _ & _).
  unfold app_blk in ABB. try unfold KLOW in ABB. try unfold KHIGH in ABB. try unfold KEND in ABB.
  clear APP.
  assert (MUL : munch [(Y, Y + 1); (l_FRB P - 2224, l_FRB P)] m1 m1) by apply munch_refl.
  assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  kx_autoFLAx [KAUnp X 1; KAUnp Y 1; KAApp Y 1] [0x8b664; 0x8b6c0] 40%nat
    [KZRange X 4096 (2^47 - 1); KZRange Y 4096 (2^47 - 1); KZRange K 1 (2^47); KZWr Y 1]
    [(X, 1)] [(X, 1); (Y, 1)].
  all: try kx_z. all: try kx_acc RBUF. all: try sql_aclose.
  all: kx_mem.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8b664) _ _ ?m2 _) =>
           eapply IH; [exact ST0 | exact HLOC | eapply BUFS; [exact MUL | exact WMl | first [exact KXMI | exact MI] | exact BUF | exact STK | sqd1_ar | sqd1_ar] | sqd1_ar ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8b6c0) _ _ ?m2 _) =>
           sqd1_done c304; eapply BUFS; [exact MUL | exact WMl | first [exact KXMI | exact MI] | exact BUF | exact STK | sqd1_ar | sqd1_ar]
       end.
Qed.

Ltac sqd1_eq := first [rewrite Z2Nat.id by lia | idtac]; solve [reflexivity | lia | f_equal; sqd1_ar | sqd1_ar].
Ltac sqd1_mi := lazymatch goal with |- mem_inv ?sg ?mm => match goal with H : mem_inv sg mm |- _ => exact H end end.
Ltac sqd1_call ST INV INV2 m2 :=
  eapply evtF_cut; [eapply sql_copy_spec; [exact ST | exact INV | sqd1_ar | lia | sqd1_ar | left; split; sqd1_ar] |];
  let ms2 := fresh "ms" in intros ms2 (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & INV2);
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?a)] => replace (ret_pc (Z_to_bv 64 a)) with (Z_to_bv 64 a) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.

Lemma sqd1_blg : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP OP n raddr X Y A19 A20 A24 : Z) (x1 x5 x6 x7 x12 x13 x14 x15 x17 x23 x25 x26 x28 x29 x30 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 (Z_to_bv 64 raddr) c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  l_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND ->
  X - LP = Y - OP -> OP <= Y -> Y < OP + n -> A19 = Y -> A20 = OP + n -> A24 = X ->
  evtF bsegs (l_RNG P) (sqd1_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 raddr c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) (Z_to_bv 64 X) (Z_to_bv 64 Y) x12 x13 x14 x15 (Z_to_bv 64 raddr) x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 A19) (Z_to_bv 64 A20) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) x23 (Z_to_bv 64 A24) x25 x26 (Z_to_bv 64 n) x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x8b5e8) (l_fc P) None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV ST HLOC m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n raddr X Y A19 A20 A24 x1 x5 x6 x7 x12 x13 x14 x15 x17 x23 x25 x26 x28 x29 x30
    INV HOP HLLO HLE HOE HXY HY1 HY2 H19 H20 H24.
  subst A19 A20 A24.
  eapply (sqd1_bl (Z.to_nat (OP + n - Y))); try eassumption. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma sqd1_tlg : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP OP n raddr X Y K A19 A20 A24 A25 : Z) (x1 x5 x6 x7 x13 x14 x15 x17 x23 x26 x28 x29 x30 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 (Z_to_bv 64 raddr) c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  l_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND ->
  X - LP = Y - OP -> OP <= Y -> Y + K = OP + n -> 0 < K -> A19 = OP + n -> A20 = OP + n -> A24 = X -> A25 = Y ->
  evtF bsegs (l_RNG P) (sqd1_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 raddr c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) (Z_to_bv 64 K) (Z_to_bv 64 X) (Z_to_bv 64 Y) x13 x14 x15 (Z_to_bv 64 raddr) x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 A19) (Z_to_bv 64 A20) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) x23 (Z_to_bv 64 A24) (Z_to_bv 64 A25) x26 (Z_to_bv 64 n) x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x8b664) (l_fc P) None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV ST HLOC m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n raddr X Y K A19 A20 A24 A25 x1 x5 x6 x7 x13 x14 x15 x17 x23 x26 x28 x29 x30
    INV HOP HLLO HLE HOE HXY HY1 HYK HK0 H19 H20 H24 H25.
  subst A19 A20 A24 A25.
  eapply (sqd1_tl (Z.to_nat K)); try eassumption. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma sqd1_wx : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP OP n raddr A20 B : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 (Z_to_bv 64 raddr) c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  l_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND -> 32 <= n ->
  c304 = Z_to_bv 64 (n - 32) -> A20 = OP + n -> B = OP + n - 32 ->
  evtF bsegs (l_RNG P) (sqd1_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 raddr c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) (Z_to_bv 64 A20) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) x23 (Z_to_bv 64 LP) (Z_to_bv 64 B) x26 (Z_to_bv 64 n) x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8b380) (l_fc P) None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV ST HLOC m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n raddr A20 B x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x28 x29 x30 x31
    INV HOP HLLO HLE HOE HN HC H20 HB.
  subst c304 A20 B.
  pose proof ST as ST0. pose proof INV as INV0.
  pose proof (sql_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6).
  clear BUF LIT STK.
  apply (sql_rg_k _ _ _ _ _ ST); intros RG1 RG2 RG3 RG4 RG5 RG6 RG7 RG8 RG9 RG10 RG11 RG12 RG13 RG14.
  apply (sql_lopen_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV); intros jpad jseq FR FRF L16 LJ SQB MI UFL USEQ RSQ RSQS.
  apply sql_fr_vlt in FR. clear FRF SQB INV.
  kx_autoFLAx (@nil kza) [0x8b664] 20%nat
    [KZRange (l_FRB P) 4096 (2^47); KZRange OP 4096 (2^47 - 1); KZRange LP 4096 (2^47 - 1); KZRange n 32 (2^47)]
    [(l_FRB P, 568)] (@nil (Z * Z)).
  all: try kx_z. all: try sql_aclose.
  all: kx_mem.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8b664) _ _ _ _) =>
           eapply sqd1_tlg; [exact ST0 | exact HLOC | exact INV0 | sqd1_eq ..]
       end.
Qed.

Lemma sqd1_wl : forall (k : nat) P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP OP n raddr D S A20 B : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 (Z_to_bv 64 raddr) c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  l_DST P <= OP -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND ->
  c304 = Z_to_bv 64 (n - 32) -> A20 = OP + n -> B = OP + n - 32 -> S = LP + (D - OP) + 16 ->
  OP + 16 <= D -> D < OP + n - 32 -> OP + n - 32 - D <= Z.of_nat k ->
  evtF bsegs (l_RNG P) (sqd1_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 raddr c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) (Z_to_bv 64 A20) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 S) (Z_to_bv 64 LP) (Z_to_bv 64 B) (Z_to_bv 64 D) (Z_to_bv 64 n) x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8b354) (l_fc P) None m1 (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros P OEND LLO LEND LOCV ST HLOC m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n raddr D S A20 B x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
    INV HOP HLLO HLE HOE HC H20 HB HS HD1 HD2 HK; [exfalso; lia|].
  subst c304 A20 B S.
  pose proof ST as ST0.
  pose proof (sql_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6).
  clear BUF LIT STK.
  kx_autoFLAx (@nil kza) (@nil Z) 10%nat
    [KZRange OP 4096 (2^47 - 1); KZRange LP 4096 (2^47 - 1); KZRange n 32 (2^47); KZRange D 4096 (2^47 - 1)]
    (@nil (Z * Z)) (@nil (Z * Z)).
  all: try kx_z. all: kx_mem.
  sqd1_call ST0 INV INV2 m2.
  kx_autoFLAx (@nil kza) (@nil Z) 10%nat
    [KZRange OP 4096 (2^47 - 1); KZRange LP 4096 (2^47 - 1); KZRange n 32 (2^47); KZRange D 4096 (2^47 - 1)]
    (@nil (Z * Z)) (@nil (Z * Z)).
  all: try kx_z. all: kx_mem.
  sqd1_call ST0 INV2 INV3 m3.
  kx_autoFLAx (@nil kza) [0x8b354; 0x8b380] 10%nat
    [KZRange OP 4096 (2^47 - 1); KZRange LP 4096 (2^47 - 1); KZRange n 32 (2^47); KZRange D 4096 (2^47 - 1)]
    (@nil (Z * Z)) (@nil (Z * Z)).
  all: try kx_z. all: kx_mem.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8b354) _ _ _ _) =>
           eapply IH; [exact ST0 | exact HLOC | exact INV3 | sqd1_eq ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8b380) _ _ _ _) =>
           eapply sqd1_wx; [exact ST0 | exact HLOC | exact INV3 | sqd1_eq ..]
       end.
Qed.

Lemma sqd1_main : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP OP n raddr : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x23 x25 x26 x28 x29 x30 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 (Z_to_bv 64 raddr) c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  l_DST P <= OP -> 0 < n -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND ->
  evtF bsegs (l_RNG P) (sqd1_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 raddr c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 raddr) x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) x20 (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) x23 (Z_to_bv 64 LP) x25 x26 (Z_to_bv 64 n) x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x8b304) (l_fc P) None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV ST HLOC m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP n raddr x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x23 x25 x26 x28 x29 x30
    INV HOP HN0 HLLO HLE HOE.
  pose proof ST as ST0. pose proof INV as INV0.
  pose proof (sql_copy_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & LIT & STK & CF1 & CF2 & CF3 & CF4 & CF5 & CF6).
  clear BUF LIT STK.
  kx_autoFLAx (@nil kza) [0x8b5e8; 0x8b664] 30%nat
    [KZRange OP 4096 (2^47 - 1); KZRange LP 4096 (2^47 - 1); KZRange n 1 (2^47)]
    (@nil (Z * Z)) (@nil (Z * Z)).
  all: try kx_z. all: kx_mem.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8b5e8) _ _ _ _) =>
           eapply sqd1_blg; [exact ST0 | exact HLOC | exact INV0 | sqd1_eq ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8b664) _ _ _ _) =>
           eapply sqd1_tlg; [exact ST0 | exact HLOC | exact INV0 | sqd1_eq ..]
       | |- _ => idtac
       end.
  assert (HN32 : 32 <= n) by sqd1_ar.
  sqd1_call ST0 INV0 INV2 m2.
  clear INV INV0.
  apply (sql_rg_k _ _ _ _ _ ST0); intros RG1 RG2 RG3 RG4 RG5 RG6 RG7 RG8 RG9 RG10 RG11 RG12 RG13 RG14.
  apply (sql_lopen_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST0 INV2); intros jpad jseq FR FRF L16 LJ SQB MI UFL USEQ RSQ RSQS.
  apply sql_fr_vlt in FR. clear SQB.
  assert (SZF : Z.of_nat (cells_size (sql_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad)) = 256) by (destruct P; reflexivity).
  hold FRF.
  assert (MUL : munch [(l_FRB P, l_FRB P + 568); (l_FF P, l_FF P + 256)] m2 m2) by apply munch_refl.
  assert (MULf : munch [(l_FRB P, l_FRB P + 568)] m2 m2) by apply munch_refl.
  assert (WMl : wmono bsegs m2 m2) by apply wmono_refl.
  assert (AFR : l_FRB P + 568 <= KXKEND /\ KXSHHI <= l_FRB P).
  { unfold KXKEND, KXSHHI. clear - ST0 RG7. destruct P. sd_static_open ST0. unfold held in *. cbn in *. lia. }
  kx_autoFLAx [KAApp (l_FRB P) 568] [0x8b354; 0x8b380] 10%nat
    [KZRange (l_FRB P) 4096 (2^47); KZWr (l_FRB P) 568; KZRange OP 4096 (2^47 - 1); KZRange LP 4096 (2^47 - 1); KZRange n 32 (2^47)]
    [(l_FRB P, 568)] [(l_FRB P, 568)].
  all: try kx_z. all: try sql_aclose.
  all: kx_mem.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => destruct AFR as [AF1 AF2]; solve [lia] end).
  all: unfold held in FRF.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8b354) _ _ ?m3 _) =>
           assert (FRF3 : rw_cells bsegs m3 (l_FF P) (sql_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad))
             by (eapply rw_cells_transport; [exact FRF | exact MULf | exact WMl | rewrite SZF; cbn [disjoint_from]; split; [lia | exact I]]);
           eapply (sqd1_wl (Z.to_nat n)); [exact ST0 | exact HLOC
             | eapply (sql_linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST0 INV2);
               [exact MUL | exact WMl | sqd1_mi | apply sql_fr_ult; [exact FR | exact L16 | exact LJ] | exact FRF3]
             | sqd1_eq ..]
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8b380) _ _ ?m3 _) =>
           assert (FRF3 : rw_cells bsegs m3 (l_FF P) (sql_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad))
             by (eapply rw_cells_transport; [exact FRF | exact MULf | exact WMl | rewrite SZF; cbn [disjoint_from]; split; [lia | exact I]]);
           eapply sqd1_wx; [exact ST0 | exact HLOC
             | eapply (sql_linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST0 INV2);
               [exact MUL | exact WMl | sqd1_mi | apply sql_fr_ult; [exact FR | exact L16 | exact LJ] | exact FRF3]
             | sqd1_eq ..]
       end.
Qed.

End CANSEC1.
