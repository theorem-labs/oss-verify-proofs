(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_kx AZ_globals AZ_globalsR AZ_huf_iface AZ_seq_bit_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import ZdWalkKit ZdDctxRep ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AMalloc_iface AFake_iface AFakeK_iface AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit
     AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_ibase AZ_seq_d_ad_at AZ_seq_d_iat AZ_seq_d_ikit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
Ltac kx_pull ::= kx_pull1; kx_pull1.
Ltac kx_lia ::= kx_bv_ranges; solve [kx_lia_pruned].

Section CANSEC1. Context {rc : runConstT}.

Definition sq_inl_initfse_D2_stmt : Prop :=
  forall P OEND LLO LEND LOCV, sqd_static P OEND LLO LEND LOCV -> ai_I5 P OEND LLO LEND LOCV -> ai_I3 P OEND LLO LEND LOCV.

Definition sq_inl_initfse_D2_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s5 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (BD T SEQ DCTX NT n B tl : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 a6 a7 s4 m' cw' bc' jpad' ptr' st,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 SEQ) (Z_to_bv 64 BD) s8 s9
                  (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 DCTX) t3 t4 t5 t6)
             F (Z_to_bv 64 0x937d8) fc None m' (seg_rom bsegs)
    /\ munch [(BD, BD + 40); (BD + 56, BD + 72)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' BD (sbd_cells cw' bc' jpad' ptr' SEQ)
    /\ rw_cells bsegs m' (BD + 56) [C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 (T + 8))]
    /\ a0 = Z_to_bv 64 (NT + 4) /\ a1 = Z_to_bv 64 (SEQ + 8) /\ a3 = Z_to_bv 64 NT /\ s4 = Z_to_bv 64 SBITMASK
    /\ 0 <= st < 2^tl /\ 0 <= bc' <= B + 9 /\ bit_okS SEQ n bc' ptr'.

Definition sq_inl_initfse_D2_walk_stmt : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s5 s8 s9 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (BD T SEQ DCTX NT B bc ptr : Z) (cw st0 tb0 : word) (jpad sqb : list byte)
         (k : seq_kind) (t : seq_table),
  rw_cells bsegs m BD (sbd_cells cw bc jpad ptr SEQ) -> rw_cells bsegs m (BD + 56) [C8 st0; C8 tb0] ->
  rw_cells bsegs m (DCTX + 8) [C8 (Z_to_bv 64 NT)] ->
  bytes_at bsegs m T (map (Z_to_bv 8) (seq_table_bytes t)) -> seq_table_ok k t ->
  bytes_at bsegs m SEQ sqb ->
  4096 <= BD -> BD + 72 < 2^47 -> 4096 <= T -> T + 8 * (1 + 2^(st_log t)) <= 2^47 ->
  4096 <= SEQ -> SEQ + Z.of_nat (length sqb) < 2^47 -> 1 <= Z.of_nat (length sqb) ->
  4096 <= DCTX -> DCTX + 16 < 2^47 -> 4096 <= NT -> NT + 8 < 2^47 ->
  BD mod 8 = 0 -> T mod 4 = 0 -> DCTX mod 8 = 0 -> NT mod 4 = 0 ->
  (BD + 72 <= SEQ \/ SEQ + Z.of_nat (length sqb) <= BD) -> (BD + 72 <= T \/ T + 8 * (1 + 2^(st_log t)) <= BD) ->
  (BD + 72 <= DCTX + 8 \/ DCTX + 16 <= BD) ->
  0 <= bc <= B -> B <= 82 -> bit_okS SEQ (Z.of_nat (length sqb)) bc ptr ->
  app_blk BD (BD + 40) -> rng RNG BD 40 -> app_blk (BD + 56) (BD + 72) -> rng RNG (BD + 56) 16 ->
  aro RNG m (DCTX + 8) 8 -> aro RNG m NT 8 ->
  aro RNG m SEQ (Z.of_nat (length sqb)) -> aro RNG m T (8 * (1 + 2^(st_log t))) -> aro_client RNG m ->
  art m -> mem_inv bsegs m ->
  evtF bsegs RNG (sq_inl_initfse_D2_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s5 s8 s9 t3 t4 t5 t6 F fc BD T SEQ DCTX NT (Z.of_nat (length sqb)) B (st_log t) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (T + 4)) (Z_to_bv 64 (SEQ + 8)) a2 (Z_to_bv 64 T) a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 0x22180) s5 (Z_to_bv 64 SEQ) (Z_to_bv 64 BD) s8 s9 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 DCTX) t3 t4 t5 t6)
        F (Z_to_bv 64 0x9363c) fc None m (seg_rom bsegs)).

Ltac ifd_side RGST RGB RGS RGT16 RGM RGTP RGNT RGNTS RGTPS RGSS RGTS16 RGMS :=
  try kx_cell_lit;
  try (lazymatch goal with |- _ /\ _ /\ _ /\ rdn _ _ _ _ = Some _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
  try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGST | kx_acc RGB | kx_acc RGS | kx_acc RGT16 | kx_acc RGM | kx_acc RGTP | kx_acc RGNT
                                                   | kx_acc RGNTS | kx_acc RGTPS | kx_acc RGSS | kx_acc RGTS16 | kx_acc RGMS] end);
  try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end);
  try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => try kx_side_pre;
       lazymatch goal with |- _ /\ _ /\ (?A + _ <= ?B \/ _) =>
         let X := base_of A in let Y := base_of B in unhide_related X Y;
         repeat match goal with H : hidden _ |- _ => clear H end; repeat split; lia end end).

Ltac sq_inl_initfse_D2_close :=
  apply evtF_done; unfold sq_inl_initfse_D2_post, sbd_cells;
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [match goal with H : rw_cells _ _ ?B (C8 _ :: C4 _ :: _) |- rw_cells _ _ ?B2 _ => constr_eq B B2; exact H end|];
  split; [match goal with H : rw_cells _ _ ?S [C8 _; C8 _] |- rw_cells _ _ ?S2 _ => constr_eq S S2; exact H end|];
  do 4 (split; [first [reflexivity | (unfold SBITMASK; reflexivity) | (f_equal; lia) | idtac]|]);
  split; [apply sland_mask_lt; lia|]; split; [lia|]; unfold bit_okS; intros; lia.

Lemma sq_inl_initfse_D2_walk : sq_inl_initfse_D2_walk_stmt.
Proof.
  unfold sq_inl_initfse_D2_walk_stmt. intros until t.
  intros HBD HST HTP TB OK SQB R1 R2 R3 R4 R5 R5b R6 R7 R8 R9 R10 A1 A3 A4 A5 DJ1 DJ2 DJ3 RB RBB IB APB RGB APS RGST AROTP ARONT AROS AROT ACL ART MI.
  pose proof (seq_rdn_log bsegs m T k t TB OK) as RL. pose proof (seq_tl_range k t OK) as RT.
  remember (st_log t) as tl eqn:Etl.
  pose proof (sbitmask_know m tl MI ltac:(clear - RT; lia)) as BK. unfold SBITMASK in BK. change (0x22180) with 139648 in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROS as (US & RGS & RGSS). destruct AROT as (UT & RGT & RGTS).
  destruct AROTP as (UTP & RGTP & RGTPS). destruct ARONT as (UNT & RGNT & RGNTS).
  pose proof (aro_client_at RNG m 139648 128 ACL ltac:(cbn [ACLIENT_RO In]; tauto)) as (UM & RGM & RGMS).
  assert (BDB : BD + 40 <= 0x7fff8000 \/ 0x10007fff8000 <= BD) by (unfold app_blk, KLOW, KHIGH, KEND in APB; clear - APB; lia).
  assert (SPB2 : BD + 72 <= 0x7fff8000 \/ 0x10007fff8000 <= BD + 56) by (unfold app_blk, KLOW, KHIGH, KEND in APS; clear - APS; lia).
  assert (MU : munch [(BD, BD + 40); (BD + 56, BD + 72)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (T16 : 16 <= 8 * (1 + 2^tl)) by (clear - RP; lia).
  assert (RGT16 : rng RNG T 16) by (eapply rng_sub'; [exact RGT | clear - T16; lia]).
  assert (RGTS16 : rng RNG (shad T) (shspan T 16))
    by (pose proof (shspan_sub T (8 * (1 + 2^tl)) T 16 ltac:(lia) ltac:(lia) ltac:(clear - T16; lia)) as [SS1 SS2];
        eapply rng_sub'; [exact RGTS | split; [exact SS1 | exact SS2]]).
  clear UT RGT RGTS.
  unfold sbd_cells in HBD. unfold bit_okS in IB.
  clear TB ACL APB APS.
  assert (CASES : 65 <= bc + tl \/ (bc + tl <= 64 /\ ptr = SEQ) \/
                  (bc + tl <= 64 /\ 8 <= n /\ SEQ + 8 <= ptr <= SEQ + n - 8) \/
                  (bc + tl <= 64 /\ 8 <= n /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + n - 8 /\ (bc + tl) / 8 <= ptr - SEQ) \/
                  (bc + tl <= 64 /\ 8 <= n /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + n - 8 /\ ptr - SEQ < (bc + tl) / 8)).
  { clear - IB RT RB.
    destruct (Z_le_gt_dec (bc + tl) 64) as [Bq|Bq]; [|left; lia]. destruct (IB ltac:(lia)) as [E|(N8 & R)]; [right; left; lia|].
    destruct (Z_le_gt_dec (SEQ + 8) ptr); [right; right; left; lia|]. destruct (Z.eq_dec ptr SEQ); [right; left; lia|].
    destruct (Z_le_gt_dec ((bc + tl) / 8) (ptr - SEQ)); [right; right; right; left; lia | right; right; right; right; lia]. }
  hide DJ1. hide DJ2. hide DJ3.
  destruct CASES as [C|[C|[C|[C|C]]]].
  - kx_autoFLAx [KAUnp SEQ n; KAUnp 139648 128; KAUnp (DCTX + 8) 8; KAUnp NT 8; KAApp BD 40; KAApp (BD + 56) 16] [0x937d8] 400%nat
      [KZRange bc 0 82; KZRange (bc + tl) 65 91; KZRange n 1 (2^47);
       KZRange BD 4096 (2^47 - 72); KZRange DCTX 4096 (2^47 - 16); KZRange NT 4096 (2^47 - 8); KZAlign NT 4; KZAlign DCTX 8;
       KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign T 4;
       KZWord (T + 4) 4 tl; KZWord (139648 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr (BD + 56) 16; KZDisj BD 40 (BD + 56) 16; KZDisj BD 40 SEQ n; KZDisj (BD + 56) 16 SEQ n;
       KZDisj BD 40 T 16; KZDisj (BD + 56) 16 T 16; KZDisj BD 40 (DCTX + 8) 8; KZDisj (BD + 56) 16 (DCTX + 8) 8]
      [(SEQ, n); (BD, 40); (BD + 56, 16); (DCTX + 8, 8)] [(BD, 40); (BD + 56, 16)].
    all: ifd_side RGST RGB RGS RGT16 RGM RGTP RGNT RGNTS RGTPS RGSS RGTS16 RGMS.
    all: unhide.
    all: kx_mem.
    all: kx_abs.
    all: kx_mkR_fold.
    all: sq_inl_initfse_D2_close.
  - destruct C as (C1 & C2). subst ptr.
    kx_autoFLAx [KAUnp SEQ n; KAUnp 139648 128; KAUnp (DCTX + 8) 8; KAUnp NT 8; KAApp BD 40; KAApp (BD + 56) 16] [0x937d8] 400%nat
      [KZRange bc 0 64; KZRange (bc + tl) 0 64; KZRange n 1 (2^47);
       KZRange BD 4096 (2^47 - 72); KZRange DCTX 4096 (2^47 - 16); KZRange NT 4096 (2^47 - 8); KZAlign NT 4; KZAlign DCTX 8;
       KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign T 4;
       KZWord (T + 4) 4 tl; KZWord (139648 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr (BD + 56) 16; KZDisj BD 40 (BD + 56) 16; KZDisj BD 40 SEQ n; KZDisj (BD + 56) 16 SEQ n;
       KZDisj BD 40 T 16; KZDisj (BD + 56) 16 T 16; KZDisj BD 40 (DCTX + 8) 8; KZDisj (BD + 56) 16 (DCTX + 8) 8]
      [(SEQ, n); (BD, 40); (BD + 56, 16); (DCTX + 8, 8)] [(BD, 40); (BD + 56, 16)].
    all: ifd_side RGST RGB RGS RGT16 RGM RGTP RGNT RGNTS RGTPS RGSS RGTS16 RGMS.
    all: unhide.
    all: kx_mem.
    all: kx_abs.
    all: kx_mkR_fold.
    all: sq_inl_initfse_D2_close.
  - destruct C as (C1 & C2 & C3).
    assert (QR : exists q r d, bc + tl = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 8 <= d /\ d + 8 <= n)
      by (exists ((bc + tl) / 8), ((bc + tl) mod 8), (ptr - SEQ); clear - C1 C3 RB RT; lia).
    destruct QR as (q & r & d & EQ & -> & Q1 & Q2 & Q3 & Q4).
    assert (EB : bc = 8 * q + r - tl) by (clear - EQ; lia). subst bc.
    kx_autoFLAx [KAUnp SEQ n; KAUnp 139648 128; KAUnp (DCTX + 8) 8; KAUnp NT 8; KAApp BD 40; KAApp (BD + 56) 16] [0x937d8] 400%nat
      [KZRange n 16 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange (8 * q + r - tl) 0 64; KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
       KZRange BD 4096 (2^47 - 72); KZRange DCTX 4096 (2^47 - 16); KZRange NT 4096 (2^47 - 8); KZAlign NT 4; KZAlign DCTX 8;
       KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign T 4;
       KZWord (T + 4) 4 tl; KZWord (139648 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr (BD + 56) 16; KZDisj BD 40 (BD + 56) 16; KZDisj BD 40 SEQ n; KZDisj (BD + 56) 16 SEQ n;
       KZDisj BD 40 T 16; KZDisj (BD + 56) 16 T 16; KZDisj BD 40 (DCTX + 8) 8; KZDisj (BD + 56) 16 (DCTX + 8) 8]
      [(SEQ, n); (BD, 40); (BD + 56, 16); (DCTX + 8, 8)] [(BD, 40); (BD + 56, 16)].
    all: ifd_side RGST RGB RGS RGT16 RGM RGTP RGNT RGNTS RGTPS RGSS RGTS16 RGMS.
    all: unhide.
    all: kx_mem.
    all: kx_abs.
    all: kx_mkR_fold.
    all: sq_inl_initfse_D2_close.
  - destruct C as (C1 & C2 & C3 & C4 & QD).
    assert (QR : exists q r d, bc + tl = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 1 <= d <= 7 /\ d + 8 <= n /\ q <= d)
      by (exists ((bc + tl) / 8), ((bc + tl) mod 8), (ptr - SEQ); clear - C1 C3 C4 QD RB RT; lia).
    clear QD. destruct QR as (q & r & d & EQ & -> & Q1 & Q2 & Q3 & Q4 & QD).
    assert (EB : bc = 8 * q + r - tl) by (clear - EQ; lia). subst bc.
    kx_autoFLAx [KAUnp SEQ n; KAUnp 139648 128; KAUnp (DCTX + 8) 8; KAUnp NT 8; KAApp BD 40; KAApp (BD + 56) 16] [0x937d8] 400%nat
      [KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange (8 * q + r - tl) 0 64; KZRange d 1 7; KZRange (d - q) 0 7; KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
       KZRange BD 4096 (2^47 - 72); KZRange DCTX 4096 (2^47 - 16); KZRange NT 4096 (2^47 - 8); KZAlign NT 4; KZAlign DCTX 8;
       KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign T 4;
       KZWord (T + 4) 4 tl; KZWord (139648 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr (BD + 56) 16; KZDisj BD 40 (BD + 56) 16; KZDisj BD 40 SEQ n; KZDisj (BD + 56) 16 SEQ n;
       KZDisj BD 40 T 16; KZDisj (BD + 56) 16 T 16; KZDisj BD 40 (DCTX + 8) 8; KZDisj (BD + 56) 16 (DCTX + 8) 8]
      [(SEQ, n); (BD, 40); (BD + 56, 16); (DCTX + 8, 8)] [(BD, 40); (BD + 56, 16)].
    all: ifd_side RGST RGB RGS RGT16 RGM RGTP RGNT RGNTS RGTPS RGSS RGTS16 RGMS.
    all: unhide.
    all: kx_mem.
    all: kx_abs.
    all: kx_mkR_fold.
    all: sq_inl_initfse_D2_close.
  - destruct C as (C1 & C2 & C3 & C4 & QD).
    assert (QR : exists q r d, bc + tl = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 1 <= d <= 7 /\ d + 8 <= n /\ d < q)
      by (exists ((bc + tl) / 8), ((bc + tl) mod 8), (ptr - SEQ); clear - C1 C3 C4 QD RB RT; lia).
    clear QD. destruct QR as (q & r & d & EQ & -> & Q1 & Q2 & Q3 & Q4 & QD).
    assert (EB : bc = 8 * q + r - tl) by (clear - EQ; lia). subst bc.
    kx_autoFLAx [KAUnp SEQ n; KAUnp 139648 128; KAUnp (DCTX + 8) 8; KAUnp NT 8; KAApp BD 40; KAApp (BD + 56) 16] [0x937d8] 400%nat
      [KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange (8 * q + r - tl) 0 64; KZRange d 1 7; KZRange (q - d) 1 8; KZRange (n - d) 8 (2^47);
       KZRange BD 4096 (2^47 - 72); KZRange DCTX 4096 (2^47 - 16); KZRange NT 4096 (2^47 - 8); KZAlign NT 4; KZAlign DCTX 8;
       KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign T 4;
       KZWord (T + 4) 4 tl; KZWord (139648 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr (BD + 56) 16; KZDisj BD 40 (BD + 56) 16; KZDisj BD 40 SEQ n; KZDisj (BD + 56) 16 SEQ n;
       KZDisj BD 40 T 16; KZDisj (BD + 56) 16 T 16; KZDisj BD 40 (DCTX + 8) 8; KZDisj (BD + 56) 16 (DCTX + 8) 8]
      [(SEQ, n); (BD, 40); (BD + 56, 16); (DCTX + 8, 8)] [(BD, 40); (BD + 56, 16)].
    all: ifd_side RGST RGB RGS RGT16 RGM RGTP RGNT RGNTS RGTPS RGSS RGTS16 RGMS.
    all: unhide.
    all: kx_mem.
    all: kx_abs.
    all: kx_mkR_fold.
    all: sq_inl_initfse_D2_close.
Qed.

Ltac ifd_goal_at A := lazymatch goal with |- rw_cells ?sg ?mm ?A0 ?cs => replace A0 with A by (rewrite <- !Z.add_assoc; reflexivity) end.
Ltac ifd_at H A := lazymatch type of H with rw_cells ?sg ?mm _ ?cs => change (rw_cells sg mm A cs) in H end.

Theorem sq_inl_initfse_D2_proof : sq_inl_initfse_D2_stmt.
Proof.
  unfold sq_inl_initfse_D2_stmt. intros P OEND LLO LEND LOCV ST I5K.
  unfold ai_I3. intros m1 ja jb jc jd jpad j88 p0 p1 p2 cw bc ptr sLL x1 x12 x14 x15 x16 x17 x21 INV BC BOK SLL.
  unfold ai_I5 in I5K.
  pose proof sq_inl_initfse_D2_walk as W. unfold sq_inl_initfse_D2_walk_stmt in W.
  pose proof (sqd_iasan_now P OEND LLO LEND LOCV m1 _ _ ST INV) as ASN.
  pose proof (sqd_itbl_asan P OEND LLO LEND LOCV m1 _ _ ST INV) as (ATL & ATO & ATM).
  pose proof (sqd_itbl_logs P OEND LLO LEND LOCV m1 _ _ ST INV) as (_ & _ & _ & TLL & TLO & TLM).
  pose proof (sqd_iinv_mi P OEND LLO LEND LOCV m1 _ _ INV) as MI.
  pose proof ST as ST0. pose proof INV as INV0.
  destruct INV as (FR0 & FF0 & PT & TBL & TBO & TBM & SQB & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqd_iregsB sqd_ifrB sqd_iffB sqd_iffC sqd_iffD sqd_asan w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m
       w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf
       w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8
       w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in *.
  pose proof ST as STc. sd_static_open STc.
  cbv beta iota in S13, S14, S15, S17, S18, S19, S20, S21, S22, S23, S44, S45, S46, S47, S49, S50, S51, S54, S56, S58, S59, S60, S61, OKLL, OKOF, OKML.
  try unfold held in *.
  destruct S61 as (AST & TPE & ATLx & SPT & ED8 & FRBR & FRBM & FFa & FFb & FFc & ESHF & RFF & RSHF & _).
  destruct ASN as (ARD & AHD & ASQ & ATBL & ACL & AOUT & ALT & ALH & AZS & ART).
  destruct (seq_tbl_len K_LL tLL OKLL) as (_ & TRL). destruct (seq_tbl_len K_OF tOF OKOF) as (_ & TRO).
  destruct (seq_tbl_len K_ML tML OKML) as (_ & TRM). cbn [kind_maxLog] in TRL, TRO, TRM.
  assert (LN : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (rewrite length_map; reflexivity).
  assert (PL9 : 1 <= 2 ^ st_log tLL <= 512) by (clear - TRL; split; [pose proof (Z.pow_pos_nonneg 2 (st_log tLL)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  assert (PO8 : 1 <= 2 ^ st_log tOF <= 256) by (clear - TRO; split; [pose proof (Z.pow_pos_nonneg 2 (st_log tOF)); lia | change 256 with (2^8); apply Z.pow_le_mono_r; lia]).
  assert (PM9 : 1 <= 2 ^ st_log tML <= 512) by (clear - TRM; split; [pose proof (Z.pow_pos_nonneg 2 (st_log tML)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  assert (FF4096 : 4096 <= FF) by (clear - S49; lia).
  assert (DJ1 : FF + 32 + 72 <= SEQ \/ SEQ + Z.of_nat (length (map (Z_to_bv 8) sq)) <= FF + 32) by (rewrite LN; clear - S56; lia).
  assert (DJ2 : FF + 32 + 72 <= OFT \/ OFT + 8 * (1 + 2 ^ st_log tOF) <= FF + 32) by (clear - S59 PO8; lia).
  assert (DJ3 : FF + 32 + 72 <= DCTX + 8 \/ DCTX + 16 <= FF + 32) by (clear - S54; lia).
  unfold dctx_ptrs in PT.
  change (rw_cells bsegs m1 DCTX ([C8 (Z_to_bv 64 LLT)] ++ [C8 (Z_to_bv 64 MLT); C8 (Z_to_bv 64 OFT); C8 huf])) in PT.
  apply rw_cells_app in PT as (_ & PT2).
  change (rw_cells bsegs m1 (DCTX + 8) ([C8 (Z_to_bv 64 MLT)] ++ [C8 (Z_to_bv 64 OFT); C8 huf])) in PT2.
  apply rw_cells_app in PT2 as (PT3 & _).
  destruct (sqd_cbst32 m1 FF (CB 32 jfh :: [C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8))] ++ [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8))]) j88 [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))] FF0) as (w1 & w2 & j' & FF1).
  change (rw_cells bsegs m1 FF ([CB 32 jfh] ++ ([C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8))] ++ ([C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8))] ++ ([C8 w1; C8 w2] ++ (CB 16 j' :: [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))])))))) in FF1.
  apply rw_cells_app in FF1 as (FA & FF2). apply rw_cells_app in FF2 as (FB & FF3). apply rw_cells_app in FF3 as (FL & FF4).
  apply rw_cells_app in FF4 as (FC & FD).
  ifd_at FB (FF + 32). ifd_at FL (FF + 32 + 40). ifd_at FC (FF + 32 + 40 + 16). ifd_at FD (FF + 32 + 40 + 16 + 16).
  replace (FF + 32 + 40 + 16) with (FF + 32 + 56) in FC by (rewrite <- !Z.add_assoc; reflexivity).
  replace (FF + 32 + 40 + 16 + 16) with (FF + 32 + 56 + 16) in FD by (rewrite <- !Z.add_assoc; reflexivity).
  assert (RGB40 : rng RNG (FF + 32) 40) by (eapply rng_sub'; [exact RFF | clear - FF4096; lia]).
  assert (RGS16 : rng RNG (FF + 32 + 56) 16) by (eapply rng_sub'; [exact RFF | clear - FF4096; lia]).
  assert (AROD : aro RNG m1 (DCTX + 8) 8).
  { destruct (ARD ltac:(clear - ED8; unfold DCTX_SIZEOF; lia)) as (_ & UD & RD & RDS).
    eapply aro_sub; [split; [exact UD | split; [exact RD | exact RDS]] | clear - ED8; lia | clear - ED8; lia | clear - ED8; unfold DCTX_SIZEOF; lia]. }
  assert (ARON : aro RNG m1 MLT 8) by (eapply aro_sub; [exact ATM | clear - PM9; lia | clear - PM9; lia | clear - PM9; lia]).
  assert (AROQ : aro RNG m1 SEQ (Z.of_nat (length (map (Z_to_bv 8) sq)))).
  { rewrite LN. destruct (ASQ ltac:(clear - S15; lia)) as (_ & UQ & RQ & RQS). split; [exact UQ | split; [exact RQ | exact RQS]]. }
  assert (IB : bit_okS SEQ (Z.of_nat (length (map (Z_to_bv 8) sq))) bc ptr) by (unfold bit_okS; rewrite LN; exact BOK).
  assert (APB : app_blk (FF + 32) (FF + 32 + 40)) by (unfold app_blk, KLOW, KHIGH, KEND; clear - S49 S50 S18 S17; lia).
  assert (APS : app_blk (FF + 32 + 56) (FF + 32 + 72)) by (unfold app_blk, KLOW, KHIGH, KEND; clear - S49 S50 S18 S17; lia).
  eapply evtF_cut.
  { eapply W with (m := m1) (BD := FF + 32) (T := OFT) (SEQ := SEQ) (DCTX := DCTX) (NT := MLT) (B := 73) (bc := bc) (ptr := ptr) (cw := cw)
                   (st0 := w1) (tb0 := w2) (jpad := jpad) (sqb := map (Z_to_bv 8) sq) (k := K_OF) (t := tOF).
    all: try eassumption.
    all: try rewrite LN.
    all: clear - FF4096 S50 S18 S17 S21 S22 S23 S13 S14 S15 S19 S20 FFc S44 S45 S46 ED8 BC PL9 PO8 PM9; lia. }
  intros ms' PO. unfold sq_inl_initfse_D2_post in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y20 & m' & cw' & bc' & jpad' & ptr' & st' & -> & MU & WM & MI' & HBD' & HST' & E0 & E1 & E3 & E4 & STB & BCB & BOK').
  subst y0 y1 y3 y20.
  assert (FA' : rw_cells bsegs m' FF [CB 32 jfh])
    by (eapply rw_cells_transport; [exact FA | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia]).
  assert (FL' : rw_cells bsegs m' (FF + 32 + 40) [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8))])
    by (eapply rw_cells_transport; [exact FL | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia]).
  assert (FD' : rw_cells bsegs m' (FF + 32 + 56 + 16) (CB 16 j' :: [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))]))
    by (eapply rw_cells_transport; [exact FD | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia]).
  assert (FR' := rw_cells_transport bsegs _ _ _ _ _ FR0 MU WM).
  specialize (FR' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  assert (MUL : munch [(FRB, FRB + 216); (FF, FF + 256)] m1 m').
  { eapply munch_weaken; [|exact MU]. unfold sub_fp. intros z Hz. cbn [outside] in *. destruct Hz as (H1 & H2 & _). repeat split; clear - H2; lia. }
  assert (FFN : rw_cells bsegs m' FF ([CB 32 jfh] ++ (sbd_cells cw' bc' jpad' ptr' SEQ ++ ([C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8))] ++ ([C8 (Z_to_bv 64 st'); C8 (Z_to_bv 64 (OFT + 8))] ++ (CB 16 j' :: [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))])))))).
  { apply rw_cells_app. split; [exact FA'|]. apply rw_cells_app. split; [exact HBD'|]. apply rw_cells_app. split; [exact FL'|].
    apply rw_cells_app. split; [ifd_goal_at (FF + 32 + 56); exact HST'|]. ifd_goal_at (FF + 32 + 56 + 16). exact FD'. }
  eapply (I5K m' ja jb jc jd jpad' j' p0 p1 p2 cw' bc' ptr' sLL st' x1 y2 y4 y5 y6 y7 x21).
  - eapply (sqd_iinv_frame _ OEND LLO LEND LOCV m1 _ _ ST0 INV0 m' _ _ MUL WM MI' FR' FFN).
  - clear - BCB; lia.
  - unfold bit_ok. unfold bit_okS in BOK'. rewrite LN in BOK'. exact BOK'.
  - exact SLL.
  - exact STB.
Qed.


End CANSEC1.
