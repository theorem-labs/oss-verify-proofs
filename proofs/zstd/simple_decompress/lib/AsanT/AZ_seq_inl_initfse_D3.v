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

Definition sq_inl_initfse_D3_stmt : Prop :=
  forall P OEND LLO LEND LOCV, sqd_static P OEND LLO LEND LOCV -> ai_I7 P OEND LLO LEND LOCV -> ai_I5 P OEND LLO LEND LOCV.

Definition sq_inl_initfse_D3_post (ra sp gp tp t0 t1 t2 s0 s2 s3 s5 s8 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (FRB BD T SEQ n B tl OE DS : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 a6 a7 s9 m' cw' bc' jpad' ptr' st w120,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 FRB) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 AG_blk_BIT_mask) s5 (Z_to_bv 64 SEQ) (Z_to_bv 64 BD) s8 s9
                  (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x93970) fc None m' (seg_rom bsegs)
    /\ munch [(BD, BD + 40); (BD + 72, BD + 88); (FRB, FRB + 56); (FRB + 96, FRB + 128)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' BD (sbd_cells cw' bc' jpad' ptr' SEQ)
    /\ rw_cells bsegs m' (BD + 72) [C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 (T + 8))]
    /\ rw_cells bsegs m' FRB [C8 t5; C8 t4; C8 t3; C8 t2; C8 t1; C8 t0; C8 (Z_to_bv 64 OE)]
    /\ rw_cells bsegs m' (FRB + 96) [C8 (Z_to_bv 64 DS); C8 (Z_to_bv 64 AG_blk_BIT_mask); C8 t6; C8 w120]
    /\ s9 = Z_to_bv 64 DS /\ w120 = Z_to_bv 64 (OE - 32)
    /\ 0 <= st < 2^tl /\ 0 <= bc' <= B + 9 /\ bit_okS SEQ n bc' ptr'.

Definition sq_inl_initfse_D3_walk_stmt : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 a2 a4 a5 a6 a7 s2 s3 s5 s8 s9 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (FRB BD T SEQ OE DS B bc ptr : Z)
         (cw st0 tb0 f0 f1 f2 f3 f4 f5 g0 g1 g2 : word) (jpad sqb : list byte) (k : seq_kind) (t : seq_table),
  rw_cells bsegs m BD (sbd_cells cw bc jpad ptr SEQ) -> rw_cells bsegs m (BD + 72) [C8 st0; C8 tb0] ->
  rw_cells bsegs m FRB [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 f5; C8 (Z_to_bv 64 OE)] ->
  rw_cells bsegs m (FRB + 96) [C8 (Z_to_bv 64 DS); C8 g0; C8 g1; C8 g2] ->
  bytes_at bsegs m T (map (Z_to_bv 8) (seq_table_bytes t)) -> seq_table_ok k t ->
  bytes_at bsegs m SEQ sqb ->
  4096 <= BD -> BD + 88 < 2^47 -> 4096 <= T -> T + 8 * (1 + 2^(st_log t)) <= 2^47 ->
  4096 <= SEQ -> SEQ + Z.of_nat (length sqb) < 2^47 -> 1 <= Z.of_nat (length sqb) ->
  4096 <= FRB -> FRB + 128 < 2^47 -> 4096 <= OE -> OE < 2^47 ->
  BD mod 8 = 0 -> T mod 4 = 0 -> FRB mod 8 = 0 ->
  (BD + 88 <= SEQ \/ SEQ + Z.of_nat (length sqb) <= BD) -> (BD + 88 <= T \/ T + 8 * (1 + 2^(st_log t)) <= BD) ->
  (FRB + 128 <= SEQ \/ SEQ + Z.of_nat (length sqb) <= FRB) -> (FRB + 128 <= T \/ T + 8 * (1 + 2^(st_log t)) <= FRB) ->
  (FRB + 128 <= BD \/ BD + 88 <= FRB) ->
  0 <= bc <= B -> B <= 82 -> bit_okS SEQ (Z.of_nat (length sqb)) bc ptr ->
  app_blk BD (BD + 40) -> rng RNG BD 40 -> app_blk (BD + 72) (BD + 88) -> rng RNG (BD + 72) 16 ->
  app_blk FRB (FRB + 56) -> rng RNG FRB 56 -> app_blk (FRB + 96) (FRB + 128) -> rng RNG (FRB + 96) 32 ->
  aro RNG m SEQ (Z.of_nat (length sqb)) -> aro RNG m T (8 * (1 + 2^(st_log t))) -> aro_client RNG m ->
  art m -> mem_inv bsegs m ->
  evtF bsegs RNG (sq_inl_initfse_D3_post ra sp gp tp t0 t1 t2 s0 s2 s3 s5 s8 s11 t3 t4 t5 t6 F fc FRB BD T SEQ (Z.of_nat (length sqb)) B (st_log t) OE DS m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 FRB) (Z_to_bv 64 (T + 4)) (Z_to_bv 64 (SEQ + 8)) a2 (Z_to_bv 64 T) a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 AG_blk_BIT_mask) s5 (Z_to_bv 64 SEQ) (Z_to_bv 64 BD) s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x937d8) fc None m (seg_rom bsegs)).

Ltac ifd3_side RGST RGB RGS RGT16 RGM RGF1 RGF2 RGSS RGTS16 RGMS :=
  try kx_cell_lit;
  try (lazymatch goal with |- _ /\ _ /\ _ /\ rdn _ _ _ _ = Some _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
  try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGST | kx_acc RGB | kx_acc RGS | kx_acc RGT16 | kx_acc RGM | kx_acc RGF1 | kx_acc RGF2
                                                   | kx_acc RGSS | kx_acc RGTS16 | kx_acc RGMS] end);
  try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end);
  try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => try kx_side_pre;
       lazymatch goal with |- _ /\ _ /\ (?A + _ <= ?B \/ _) =>
         let X := base_of A in let Y := base_of B in unhide_related X Y;
         repeat match goal with H : hidden _ |- _ => clear H end; repeat split; lia end end).

Ltac sq_inl_initfse_D3_close :=
  apply evtF_done; unfold sq_inl_initfse_D3_post, sbd_cells;
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [match goal with H : rw_cells _ _ ?B (C8 _ :: C4 _ :: _) |- rw_cells _ _ ?B2 _ => constr_eq B B2; exact H end|];
  split; [match goal with H : rw_cells _ _ ?S [C8 _; C8 _] |- rw_cells _ _ ?S2 _ => constr_eq S S2; exact H end|];
  split; [match goal with H : rw_cells _ _ ?S [C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] |- rw_cells _ _ ?S2 _ => constr_eq S S2; exact H end|];
  split; [match goal with H : rw_cells _ _ ?S [C8 _; C8 _; C8 _; C8 _] |- rw_cells _ _ ?S2 _ => constr_eq S S2; exact H end|];
  do 2 (split; [first [reflexivity | (f_equal; lia) | (apply sqd_zbv_eqm; Z.div_mod_to_equations; lia)]|]);
  split; [apply sland_mask_lt; lia|]; split; [lia|]; unfold bit_okS; intros; lia.

Lemma sq_inl_initfse_D3_walk : sq_inl_initfse_D3_walk_stmt.
Proof.
  unfold sq_inl_initfse_D3_walk_stmt. intros until t.
  intros HBD HST HFA HFD TB OK SQB R1 R2 R3 R4 R5 R5b R6 R7 R8 R9 R10 A1 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5 RB RBB IB
         APB RGB APS RGST APF1 RGF1 APF2 RGF2 AROS AROT ACL ART MI.
  pose proof (seq_rdn_log bsegs m T k t TB OK) as RL. pose proof (seq_tl_range k t OK) as RT.
  remember (st_log t) as tl eqn:Etl.
  pose proof (sbitmask_know m tl MI ltac:(clear - RT; lia)) as BK. unfold SBITMASK in BK. change (0x22180) with 139648 in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROS as (US & RGS & RGSS). destruct AROT as (UT & RGT & RGTS).
  pose proof (aro_client_at RNG m 139648 128 ACL ltac:(cbn [ACLIENT_RO In]; tauto)) as (UM & RGM & RGMS).
  assert (BDB : BD + 40 <= 0x7fff8000 \/ 0x10007fff8000 <= BD) by (unfold app_blk, KLOW, KHIGH, KEND in APB; clear - APB; lia).
  assert (SPB2 : BD + 88 <= 0x7fff8000 \/ 0x10007fff8000 <= BD + 72) by (unfold app_blk, KLOW, KHIGH, KEND in APS; clear - APS; lia).
  assert (FRB1 : FRB + 56 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB) by (unfold app_blk, KLOW, KHIGH, KEND in APF1; clear - APF1; lia).
  assert (FRB2 : FRB + 128 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 96) by (unfold app_blk, KLOW, KHIGH, KEND in APF2; clear - APF2; lia).
  assert (MU : munch [(BD, BD + 40); (BD + 72, BD + 88); (FRB, FRB + 56); (FRB + 96, FRB + 128)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (T16 : 16 <= 8 * (1 + 2^tl)) by (clear - RP; lia).
  assert (RGT16 : rng RNG T 16) by (eapply rng_sub'; [exact RGT | clear - T16; lia]).
  assert (RGTS16 : rng RNG (shad T) (shspan T 16))
    by (pose proof (shspan_sub T (8 * (1 + 2^tl)) T 16 ltac:(lia) ltac:(lia) ltac:(clear - T16; lia)) as [SS1 SS2];
        eapply rng_sub'; [exact RGTS | split; [exact SS1 | exact SS2]]).
  clear UT RGT RGTS.
  unfold sbd_cells in HBD. unfold bit_okS in IB.
  clear TB ACL APB APS APF1 APF2.
  assert (CASES : 65 <= bc + tl \/ (bc + tl <= 64 /\ ptr = SEQ) \/
                  (bc + tl <= 64 /\ 8 <= n /\ SEQ + 8 <= ptr <= SEQ + n - 8) \/
                  (bc + tl <= 64 /\ 8 <= n /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + n - 8 /\ (bc + tl) / 8 <= ptr - SEQ) \/
                  (bc + tl <= 64 /\ 8 <= n /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + n - 8 /\ ptr - SEQ < (bc + tl) / 8)).
  { clear - IB RT RB.
    destruct (Z_le_gt_dec (bc + tl) 64) as [Bq|Bq]; [|left; lia]. destruct (IB ltac:(lia)) as [E|(N8 & R)]; [right; left; lia|].
    destruct (Z_le_gt_dec (SEQ + 8) ptr); [right; right; left; lia|]. destruct (Z.eq_dec ptr SEQ); [right; left; lia|].
    destruct (Z_le_gt_dec ((bc + tl) / 8) (ptr - SEQ)); [right; right; right; left; lia | right; right; right; right; lia]. }
  hide DJ1. hide DJ2. hide DJ3. hide DJ4. hide DJ5.
  destruct CASES as [C|[C|[C|[C|C]]]].
  - kx_autoFLAx [KAUnp SEQ n; KAUnp 139648 128; KAApp BD 40; KAApp (BD + 72) 16; KAApp FRB 56; KAApp (FRB + 96) 32] [0x93970] 400%nat
      [KZRange bc 0 82; KZRange (bc + tl) 65 91; KZRange n 1 (2^47);
       KZRange BD 4096 (2^47 - 88); KZRange FRB 4096 (2^47 - 128); KZRange OE 4096 (2^47);
       KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign T 4; KZAlign FRB 8;
       KZWord (T + 4) 4 tl; KZWord (139648 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr (BD + 72) 16; KZWr FRB 56; KZWr (FRB + 96) 32;
       KZDisj BD 40 (BD + 72) 16; KZDisj BD 40 SEQ n; KZDisj (BD + 72) 16 SEQ n; KZDisj BD 40 T 16; KZDisj (BD + 72) 16 T 16;
       KZDisj FRB 56 (FRB + 96) 32; KZDisj FRB 56 SEQ n; KZDisj (FRB + 96) 32 SEQ n; KZDisj FRB 56 T 16; KZDisj (FRB + 96) 32 T 16;
       KZDisj FRB 56 BD 40; KZDisj FRB 56 (BD + 72) 16; KZDisj (FRB + 96) 32 BD 40; KZDisj (FRB + 96) 32 (BD + 72) 16]
      [(SEQ, n); (BD, 40); (BD + 72, 16); (FRB, 56); (FRB + 96, 32)] [(BD, 40); (BD + 72, 16); (FRB, 56); (FRB + 96, 32)].
    all: ifd3_side RGST RGB RGS RGT16 RGM RGF1 RGF2 RGSS RGTS16 RGMS.
    all: unhide.
    all: kx_mem.
    all: kx_abs.
    all: kx_mkR_fold.
    all: sq_inl_initfse_D3_close.
  - destruct C as (C1 & C2). subst ptr.
    kx_autoFLAx [KAUnp SEQ n; KAUnp 139648 128; KAApp BD 40; KAApp (BD + 72) 16; KAApp FRB 56; KAApp (FRB + 96) 32] [0x93970] 400%nat
      [KZRange bc 0 64; KZRange (bc + tl) 0 64; KZRange n 1 (2^47);
       KZRange BD 4096 (2^47 - 88); KZRange FRB 4096 (2^47 - 128); KZRange OE 4096 (2^47);
       KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign T 4; KZAlign FRB 8;
       KZWord (T + 4) 4 tl; KZWord (139648 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr (BD + 72) 16; KZWr FRB 56; KZWr (FRB + 96) 32;
       KZDisj BD 40 (BD + 72) 16; KZDisj BD 40 SEQ n; KZDisj (BD + 72) 16 SEQ n; KZDisj BD 40 T 16; KZDisj (BD + 72) 16 T 16;
       KZDisj FRB 56 (FRB + 96) 32; KZDisj FRB 56 SEQ n; KZDisj (FRB + 96) 32 SEQ n; KZDisj FRB 56 T 16; KZDisj (FRB + 96) 32 T 16;
       KZDisj FRB 56 BD 40; KZDisj FRB 56 (BD + 72) 16; KZDisj (FRB + 96) 32 BD 40; KZDisj (FRB + 96) 32 (BD + 72) 16]
      [(SEQ, n); (BD, 40); (BD + 72, 16); (FRB, 56); (FRB + 96, 32)] [(BD, 40); (BD + 72, 16); (FRB, 56); (FRB + 96, 32)].
    all: ifd3_side RGST RGB RGS RGT16 RGM RGF1 RGF2 RGSS RGTS16 RGMS.
    all: unhide.
    all: kx_mem.
    all: kx_abs.
    all: kx_mkR_fold.
    all: sq_inl_initfse_D3_close.
  - destruct C as (C1 & C2 & C3).
    assert (QR : exists q r d, bc + tl = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 8 <= d /\ d + 8 <= n)
      by (exists ((bc + tl) / 8), ((bc + tl) mod 8), (ptr - SEQ); clear - C1 C3 RB RT; lia).
    destruct QR as (q & r & d & EQ & -> & Q1 & Q2 & Q3 & Q4).
    assert (EB : bc = 8 * q + r - tl) by (clear - EQ; lia). subst bc.
    kx_autoFLAx [KAUnp SEQ n; KAUnp 139648 128; KAApp BD 40; KAApp (BD + 72) 16; KAApp FRB 56; KAApp (FRB + 96) 32] [0x93970] 400%nat
      [KZRange n 16 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange (8 * q + r - tl) 0 64; KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
       KZRange BD 4096 (2^47 - 88); KZRange FRB 4096 (2^47 - 128); KZRange OE 4096 (2^47);
       KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign T 4; KZAlign FRB 8;
       KZWord (T + 4) 4 tl; KZWord (139648 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr (BD + 72) 16; KZWr FRB 56; KZWr (FRB + 96) 32;
       KZDisj BD 40 (BD + 72) 16; KZDisj BD 40 SEQ n; KZDisj (BD + 72) 16 SEQ n; KZDisj BD 40 T 16; KZDisj (BD + 72) 16 T 16;
       KZDisj FRB 56 (FRB + 96) 32; KZDisj FRB 56 SEQ n; KZDisj (FRB + 96) 32 SEQ n; KZDisj FRB 56 T 16; KZDisj (FRB + 96) 32 T 16;
       KZDisj FRB 56 BD 40; KZDisj FRB 56 (BD + 72) 16; KZDisj (FRB + 96) 32 BD 40; KZDisj (FRB + 96) 32 (BD + 72) 16]
      [(SEQ, n); (BD, 40); (BD + 72, 16); (FRB, 56); (FRB + 96, 32)] [(BD, 40); (BD + 72, 16); (FRB, 56); (FRB + 96, 32)].
    all: ifd3_side RGST RGB RGS RGT16 RGM RGF1 RGF2 RGSS RGTS16 RGMS.
    all: unhide.
    all: kx_mem.
    all: kx_abs.
    all: kx_mkR_fold.
    all: sq_inl_initfse_D3_close.
  - destruct C as (C1 & C2 & C3 & C4 & QD).
    assert (QR : exists q r d, bc + tl = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 1 <= d <= 7 /\ d + 8 <= n /\ q <= d)
      by (exists ((bc + tl) / 8), ((bc + tl) mod 8), (ptr - SEQ); clear - C1 C3 C4 QD RB RT; lia).
    clear QD. destruct QR as (q & r & d & EQ & -> & Q1 & Q2 & Q3 & Q4 & QD).
    assert (EB : bc = 8 * q + r - tl) by (clear - EQ; lia). subst bc.
    kx_autoFLAx [KAUnp SEQ n; KAUnp 139648 128; KAApp BD 40; KAApp (BD + 72) 16; KAApp FRB 56; KAApp (FRB + 96) 32] [0x93970] 400%nat
      [KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange (8 * q + r - tl) 0 64; KZRange d 1 7; KZRange (d - q) 0 7; KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
       KZRange BD 4096 (2^47 - 88); KZRange FRB 4096 (2^47 - 128); KZRange OE 4096 (2^47);
       KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign T 4; KZAlign FRB 8;
       KZWord (T + 4) 4 tl; KZWord (139648 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr (BD + 72) 16; KZWr FRB 56; KZWr (FRB + 96) 32;
       KZDisj BD 40 (BD + 72) 16; KZDisj BD 40 SEQ n; KZDisj (BD + 72) 16 SEQ n; KZDisj BD 40 T 16; KZDisj (BD + 72) 16 T 16;
       KZDisj FRB 56 (FRB + 96) 32; KZDisj FRB 56 SEQ n; KZDisj (FRB + 96) 32 SEQ n; KZDisj FRB 56 T 16; KZDisj (FRB + 96) 32 T 16;
       KZDisj FRB 56 BD 40; KZDisj FRB 56 (BD + 72) 16; KZDisj (FRB + 96) 32 BD 40; KZDisj (FRB + 96) 32 (BD + 72) 16]
      [(SEQ, n); (BD, 40); (BD + 72, 16); (FRB, 56); (FRB + 96, 32)] [(BD, 40); (BD + 72, 16); (FRB, 56); (FRB + 96, 32)].
    all: ifd3_side RGST RGB RGS RGT16 RGM RGF1 RGF2 RGSS RGTS16 RGMS.
    all: unhide.
    all: kx_mem.
    all: kx_abs.
    all: kx_mkR_fold.
    all: sq_inl_initfse_D3_close.
  - destruct C as (C1 & C2 & C3 & C4 & QD).
    assert (QR : exists q r d, bc + tl = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 1 <= d <= 7 /\ d + 8 <= n /\ d < q)
      by (exists ((bc + tl) / 8), ((bc + tl) mod 8), (ptr - SEQ); clear - C1 C3 C4 QD RB RT; lia).
    clear QD. destruct QR as (q & r & d & EQ & -> & Q1 & Q2 & Q3 & Q4 & QD).
    assert (EB : bc = 8 * q + r - tl) by (clear - EQ; lia). subst bc.
    kx_autoFLAx [KAUnp SEQ n; KAUnp 139648 128; KAApp BD 40; KAApp (BD + 72) 16; KAApp FRB 56; KAApp (FRB + 96) 32] [0x93970] 400%nat
      [KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange (8 * q + r - tl) 0 64; KZRange d 1 7; KZRange (q - d) 1 8; KZRange (n - d) 8 (2^47);
       KZRange BD 4096 (2^47 - 88); KZRange FRB 4096 (2^47 - 128); KZRange OE 4096 (2^47);
       KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign T 4; KZAlign FRB 8;
       KZWord (T + 4) 4 tl; KZWord (139648 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr (BD + 72) 16; KZWr FRB 56; KZWr (FRB + 96) 32;
       KZDisj BD 40 (BD + 72) 16; KZDisj BD 40 SEQ n; KZDisj (BD + 72) 16 SEQ n; KZDisj BD 40 T 16; KZDisj (BD + 72) 16 T 16;
       KZDisj FRB 56 (FRB + 96) 32; KZDisj FRB 56 SEQ n; KZDisj (FRB + 96) 32 SEQ n; KZDisj FRB 56 T 16; KZDisj (FRB + 96) 32 T 16;
       KZDisj FRB 56 BD 40; KZDisj FRB 56 (BD + 72) 16; KZDisj (FRB + 96) 32 BD 40; KZDisj (FRB + 96) 32 (BD + 72) 16]
      [(SEQ, n); (BD, 40); (BD + 72, 16); (FRB, 56); (FRB + 96, 32)] [(BD, 40); (BD + 72, 16); (FRB, 56); (FRB + 96, 32)].
    all: ifd3_side RGST RGB RGS RGT16 RGM RGF1 RGF2 RGSS RGTS16 RGMS.
    all: unhide.
    all: kx_mem.
    all: kx_abs.
    all: kx_mkR_fold.
    all: sq_inl_initfse_D3_close.
Qed.

Ltac ifd3_goal_at A := lazymatch goal with |- rw_cells ?sg ?mm ?A0 ?cs => replace A0 with A by (rewrite <- !Z.add_assoc; reflexivity) end.
Ltac ifd3_at H A := lazymatch type of H with rw_cells ?sg ?mm _ ?cs => change (rw_cells sg mm A cs) in H end.

Theorem sq_inl_initfse_D3_proof : sq_inl_initfse_D3_stmt.
Proof.
  unfold sq_inl_initfse_D3_stmt. intros P OEND LLO LEND LOCV ST I7K.
  unfold ai_I5. intros m1 ja jb jc jd jpad j104 p0 p1 p2 cw bc ptr sLL sOF x1 x12 x14 x15 x16 x17 x21 INV BC BOK SLL SOF.
  unfold ai_I7, ad_head in I7K.
  pose proof sq_inl_initfse_D3_walk as W. unfold sq_inl_initfse_D3_walk_stmt in W.
  pose proof (sqd_iasan_now P OEND LLO LEND LOCV m1 _ _ ST INV) as ASN.
  pose proof (sqd_itbl_asan P OEND LLO LEND LOCV m1 _ _ ST INV) as (_ & _ & ATM).
  pose proof (sqd_iinv_mi P OEND LLO LEND LOCV m1 _ _ INV) as MI.
  pose proof ST as ST0. pose proof INV as INV0.
  destruct INV as (FR0 & FF0 & PT & TBL & TBO & TBM & SQB & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqd_iregsB sqd_ifrB sqd_iffB sqd_iffC sqd_iffD sqd_asan w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m
       w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf
       w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8
       w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in *.
  pose proof ST as STc. sd_static_open STc.
  cbv beta iota in S1, S2, S3, S4, S5, S6, S7, S8, S13, S14, S15, S17, S18, S23, S46, S47, S48, S50, S51, S53, S61, OKML.
  try unfold held in *.
  destruct S61 as (AST & TPE & ATLx & SPT & ED8 & FRBR & FRBM & FFa & FFb & FFc & ESHF & RFF & RSHF & _).
  destruct AST as (AST1 & RSTK & RAI).
  destruct ASN as (ARD & AHD & ASQ & ATBL & ACL & AOUT & ALT & ALH & AZS & ART).
  destruct (seq_tbl_len K_ML tML OKML) as (_ & TRM). cbn [kind_maxLog] in TRM.
  assert (LN : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (rewrite length_map; reflexivity).
  assert (PM9 : 1 <= 2 ^ st_log tML <= 512) by (clear - TRM; split; [pose proof (Z.pow_pos_nonneg 2 (st_log tML)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  assert (FF4096 : 4096 <= FF) by (clear - S49; lia).
  assert (DJ1 : FF + 32 + 88 <= SEQ \/ SEQ + Z.of_nat (length (map (Z_to_bv 8) sq)) <= FF + 32) by (rewrite LN; clear - S56; lia).
  assert (DJ2 : FF + 32 + 88 <= MLT \/ MLT + 8 * (1 + 2 ^ st_log tML) <= FF + 32) by (clear - S60 PM9; lia).
  assert (DJ3 : FRB + 128 <= SEQ \/ SEQ + Z.of_nat (length (map (Z_to_bv 8) sq)) <= FRB) by (rewrite LN; clear - S25 S18 S47; lia).
  assert (DJ4 : FRB + 128 <= MLT \/ MLT + 8 * (1 + 2 ^ st_log tML) <= FRB) by (clear - S30 S18 S47 PM9; lia).
  assert (DJ5 : FRB + 128 <= FF + 32 \/ FF + 32 + 88 <= FRB) by (clear - S50 S18 S47; lia).
  destruct (sqd_cb16_words m1 FF (CB 32 jfh :: [C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8))] ++ [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8))]) j104 [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))] FF0) as (w1 & w2 & FF1).
  change (rw_cells bsegs m1 FF ([CB 32 jfh] ++ ([C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8))] ++ ([C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8))] ++ ([C8 w1; C8 w2] ++ [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))]))))) in FF1.
  apply rw_cells_app in FF1 as (FA & FF2). apply rw_cells_app in FF2 as (FB & FF3). apply rw_cells_app in FF3 as (FL & FF4).
  apply rw_cells_app in FF4 as (FC & FD).
  ifd3_at FB (FF + 32). ifd3_at FL (FF + 32 + 40). ifd3_at FC (FF + 32 + 40 + 32). ifd3_at FD (FF + 32 + 40 + 32 + 16).
  replace (FF + 32 + 40 + 32) with (FF + 32 + 72) in FC by (rewrite <- !Z.add_assoc; reflexivity).
  replace (FF + 32 + 40 + 32 + 16) with (FF + 32 + 72 + 16) in FD by (rewrite <- !Z.add_assoc; reflexivity).
  destruct (sqd_cbst48 m1 FRB [] ja [C8 (Z_to_bv 64 OEND); C8 (Z_to_bv 64 FF); C8 dend; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (FF + 120)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST);
             CB 24 jb; C8 (Z_to_bv 64 PFX); CB 24 jc; CB 16 j224; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 LLO); CB 24 jd] FR0) as (f0 & f1 & ja1 & FR1).
  cbn [app] in FR1.
  lazymatch type of FR1 with rw_cells _ _ _ (?c0 :: ?c1 :: CB 32 ?j :: ?rest) =>
    destruct (sqd_cbst32 m1 FRB [c0; c1] j rest FR1) as (f2 & f3 & ja2 & FR2) end.
  cbn [app] in FR2.
  lazymatch type of FR2 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: CB 16 ?j :: ?rest) =>
    destruct (sqd_cb16_words m1 FRB [c0; c1; c2; c3] j rest FR2) as (f4 & f5 & FR3) end.
  cbn [app] in FR3.
  lazymatch type of FR3 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: CB 24 ?j :: ?rest) =>
    destruct (sqd_cb24_words m1 FRB [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12] j rest FR3) as (g0 & g1 & g2 & FR4) end.
  cbn [app] in FR4.
  lazymatch type of FR4 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: CB 24 ?j :: ?rest) =>
    destruct (sqd_cb24_words m1 FRB [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16] j rest FR4) as (c24w & c208w & c216w & FR5) end.
  cbn [app] in FR5.
  change (rw_cells bsegs m1 FRB ([C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 f5; C8 (Z_to_bv 64 OEND)] ++
           ([C8 (Z_to_bv 64 FF); C8 dend; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (FF + 120)); C8 (Z_to_bv 64 FF)] ++
            ([C8 (Z_to_bv 64 DST); C8 g0; C8 g1; C8 g2] ++
             [C8 (Z_to_bv 64 PFX); C8 c24w; C8 c208w; C8 c216w; CB 16 j224; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 LLO); CB 24 jd])))) in FR5.
  apply rw_cells_app in FR5 as (RA & FR6). apply rw_cells_app in FR6 as (RM & FR7). apply rw_cells_app in FR7 as (RD & RR).
  ifd3_at RM (FRB + 56). ifd3_at RD (FRB + 56 + 40). ifd3_at RR (FRB + 56 + 40 + 32).
  replace (FRB + 56 + 40) with (FRB + 96) in RD by (rewrite <- !Z.add_assoc; reflexivity).
  replace (FRB + 56 + 40 + 32) with (FRB + 128) in RR by (rewrite <- !Z.add_assoc; reflexivity).
  assert (RGB40 : rng RNG (FF + 32) 40) by (eapply rng_sub'; [exact RFF | clear - FF4096; lia]).
  assert (RGS16 : rng RNG (FF + 32 + 72) 16) by (eapply rng_sub'; [exact RFF | clear - FF4096; lia]).
  assert (RGF1 : rng RNG FRB 56) by (eapply rng_sub'; [exact RSTK | clear - S18 S47; lia]).
  assert (RGF2 : rng RNG (FRB + 96) 32) by (eapply rng_sub'; [exact RSTK | clear - S18 S47; lia]).
  assert (AROQ : aro RNG m1 SEQ (Z.of_nat (length (map (Z_to_bv 8) sq)))).
  { rewrite LN. destruct (ASQ ltac:(clear - S15; lia)) as (_ & UQ & RQ & RQS). split; [exact UQ | split; [exact RQ | exact RQS]]. }
  assert (IB : bit_okS SEQ (Z.of_nat (length (map (Z_to_bv 8) sq))) bc ptr) by (unfold bit_okS; rewrite LN; exact BOK).
  assert (APB : app_blk (FF + 32) (FF + 32 + 40)) by (unfold app_blk, KLOW, KHIGH, KEND; clear - S49 S50 S18 S17; lia).
  assert (APS : app_blk (FF + 32 + 72) (FF + 32 + 88)) by (unfold app_blk, KLOW, KHIGH, KEND; clear - S49 S50 S18 S17; lia).
  assert (APF1 : app_blk FRB (FRB + 56)) by (unfold app_blk, KLOW, KHIGH, KEND; clear - S53 S17 S18 S47; lia).
  assert (APF2 : app_blk (FRB + 96) (FRB + 128)) by (unfold app_blk, KLOW, KHIGH, KEND; clear - S53 S17 S18 S47; lia).
  eapply evtF_cut.
  { eapply W with (m := m1) (FRB := FRB) (BD := FF + 32) (T := MLT) (SEQ := SEQ) (OE := OEND) (DS := DST) (B := 82) (bc := bc) (ptr := ptr) (cw := cw)
                   (st0 := w1) (tb0 := w2) (f0 := f0) (f1 := f1) (f2 := f2) (f3 := f3) (f4 := f4) (f5 := f5) (g0 := g0) (g1 := g1) (g2 := g2)
                   (jpad := jpad) (sqb := map (Z_to_bv 8) sq) (k := K_ML) (t := tML).
    all: try eassumption.
    all: try rewrite LN.
    all: clear - FF4096 S1 S2 S3 S4 S5 S6 S7 S13 S14 S15 S17 S18 S23 S46 S47 S48 S50 S51 BC PM9; lia. }
  intros ms' PO. unfold sq_inl_initfse_D3_post in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y25 & m' & cw' & bc' & jpad' & ptr' & st' & w120 & -> & MU & WM & MI' & HBD' & HST' & HFA' & HFD' & E25 & E120 & STB & BCB & BOK').
  subst y25 w120.
  assert (FA' : rw_cells bsegs m' FF [CB 32 jfh])
    by (eapply rw_cells_transport; [exact FA | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia]).
  assert (FL' : rw_cells bsegs m' (FF + 32 + 40) [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8))])
    by (eapply rw_cells_transport; [exact FL | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia]).
  assert (FD' : rw_cells bsegs m' (FF + 32 + 72 + 16) [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))])
    by (eapply rw_cells_transport; [exact FD | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia]).
  assert (RM' : rw_cells bsegs m' (FRB + 56) [C8 (Z_to_bv 64 FF); C8 dend; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (FF + 120)); C8 (Z_to_bv 64 FF)])
    by (eapply rw_cells_transport; [exact RM | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia]).
  assert (RR' : rw_cells bsegs m' (FRB + 128) [C8 (Z_to_bv 64 PFX); C8 c24w; C8 c208w; C8 c216w; CB 16 j224; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 LLO); CB 24 jd])
    by (eapply rw_cells_transport; [exact RR | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia]).
  assert (MUL : munch [(FRB, FRB + 216); (FF, FF + 256)] m1 m').
  { eapply munch_weaken; [|exact MU]. unfold sub_fp. intros z Hz. cbn [outside] in Hz |- *. destruct Hz as (H1 & H2 & _). repeat split; clear - H1 H2; lia. }
  lazymatch type of HFA' with rw_cells _ _ _ ?la =>
  lazymatch type of HFD' with rw_cells _ _ _ ?lc =>
    assert (FRN : rw_cells bsegs m' FRB (la ++ ([C8 (Z_to_bv 64 FF); C8 dend; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (FF + 120)); C8 (Z_to_bv 64 FF)] ++
                    (lc ++ [C8 (Z_to_bv 64 PFX); C8 c24w; C8 c208w; C8 c216w; CB 16 j224; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 LLO); CB 24 jd]))))
  end end.
  { apply rw_cells_app. split; [exact HFA'|]. apply rw_cells_app. split; [exact RM'|].
    apply rw_cells_app. split; [ifd3_goal_at (FRB + 96); exact HFD'|]. ifd3_goal_at (FRB + 128). exact RR'. }
  assert (FFN : rw_cells bsegs m' FF ([CB 32 jfh] ++ (sbd_cells cw' bc' jpad' ptr' SEQ ++ ([C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8))] ++
                ([C8 (Z_to_bv 64 st'); C8 (Z_to_bv 64 (MLT + 8))] ++ [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))]))))).
  { apply rw_cells_app. split; [exact FA'|]. apply rw_cells_app. split; [exact HBD'|]. apply rw_cells_app. split; [exact FL'|].
    apply rw_cells_app. split; [ifd3_goal_at (FF + 32 + 72); exact HST'|]. ifd3_goal_at (FF + 32 + 72 + 16). exact FD'. }
  eapply (I7K m' c24w c24w c24w c208w c216w cw' bc' ptr' sLL sOF st' p0 p1 p2 LLO DST).
  - eapply sqd_iinv_linv. eapply sqd_iinv_eq2.
    + eapply (sqd_iinv_frame _ OEND LLO LEND LOCV m1 _ _ ST0 INV0 m' _ _ MUL WM MI' FRN FFN).
    + cbn [app sqd_frame]. sqd_cells_eq.
    + cbn [app sbd_cells sqd_ffr]. reflexivity.
  - unfold sqd_lfacts. cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq w_nbSeq].
    split; [clear - S4; lia|]. split; [clear - S8; lia|]. split; [exact SLL|]. split; [exact SOF|]. split; [exact STB|].
    split; [clear - BCB; lia|]. unfold bit_ok. unfold bit_okS in BOK'. rewrite LN in BOK'. exact BOK'.
Qed.

End CANSEC1.
