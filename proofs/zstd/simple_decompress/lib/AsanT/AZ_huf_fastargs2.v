(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_huf_iface AZ_huf_iface3 AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_lbkit AZ_huf_fakit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac kx_lia ::= kx_lia_fast.
#[local] Ltac kx_path_hyp E zs nz KXA BR ::= kx_rr_dedup; kx_path_hyp_fast E zs nz KXA BR.
(* [comment removed for export] *)
#[local] Ltac kxl_lia ::= first [ kxl_hyp | solve [kxl_lia_small] | kx_lia ].
#[local] Ltac kxl_rd_exact ::=
  first [ kxl_hyp
        | lazymatch goal with
          | |- rd_at ?segs ?m ?A ?N =>
              match goal with
              | H : rw_cells segs m A _ |- _ => apply (kxl_rd_rw segs m A _ N H); reflexivity
              | H : ro_cells segs m A _ |- _ => apply (kxl_rd_ro segs m A _ N H); reflexivity
              | H : bytes_at segs m A ?bs, L : Z.of_nat (length ?bs) = _ |- _ =>
                  apply (rd_at_sub segs m A (Z.of_nat (length bs)) A N (rd_at_bytes_at segs m A bs H)); [apply Z.le_refl | rewrite L; apply Z.le_refl]
              end
          end ].
Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.

Definition fa_args_cells1 (DST dsz SRC n b0 b1 b2 b3 b4 b5 : Z) (ajunk : list byte) : list cell :=
  [C8 (Z_to_bv 64 (b0 + (256 * b1 + SRC) + -2));
   C8 (Z_to_bv 64 (b0 + (256 * b1 + (b2 + (256 * b3 + SRC))) + -2));
   C8 (Z_to_bv 64 (b0 + (256 * b1 + (b2 + (256 * b3 + (b4 + (256 * b5 + SRC))))) + -2));
   C8 (Z_to_bv 64 (n + SRC + -8)); C8 (Z_to_bv 64 DST);
   C8 (Z_to_bv 64 (DST + (dsz + 3) / 4));
   C8 (Z_to_bv 64 (DST + 2 * ((dsz + 3) / 4)));
   C8 (Z_to_bv 64 (DST + 3 * ((dsz + 3) / 4)));
   CB 56 ajunk;
   C8 (Z_to_bv 64 (SRC + 6));
   C8 (Z_to_bv 64 (SRC + (b0 + 256 * b1) + 6));
   C8 (Z_to_bv 64 (SRC + (b0 + (256 * b1 + (b2 + 256 * b3))) + 6));
   C8 (Z_to_bv 64 (SRC + (b0 + (256 * b1 + (b2 + (256 * b3 + (b4 + 256 * b5))))) + 6))].

Definition fa_tail1_stmt : Prop :=
  forall (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x8 x9 x11 x12 x18 x19 : word) (F : bvmap 5 word) (fc : bv 32)
         (m m1 : amem) (SPV ARGS DST dsz SRC n DT lo b0 b1 b2 b3 b4 b5 c1 : Z) (src dth ajunk fjunk : list byte),
  4096 <= lo -> lo <= SPV + -48 -> SPV < 2 ^ 47 -> ARGS mod 8 = 0 -> DT mod 4 = 0 -> zlen src = n -> zlen dth = 4 ->
  4096 <= ARGS -> ARGS + 152 < 2 ^ 47 -> (ARGS + 152 <= lo \/ SPV <= ARGS) ->
  4096 <= SRC -> SRC + n < 2 ^ 47 -> (SRC + n <= lo \/ SPV <= SRC) -> n < 2 ^ 32 ->
  4096 <= DT -> DT + 4 < 2 ^ 47 -> (DT + 4 <= lo \/ SPV <= DT) -> 4096 <= DST -> 0 <= dsz < 2 ^ 32 -> DST + dsz < 2 ^ 47 ->
  (ARGS + 152 <= SRC \/ SRC + n <= ARGS) -> (ARGS + 152 <= DT \/ DT + 4 <= ARGS) ->
  app_blk ARGS (ARGS + 152) ->
  unpoisoned m ARGS (ARGS + 152) -> rng RNG ARGS 152 -> rng RNG (shad ARGS) (shspan ARGS 152) ->
  unpoisoned m SRC (SRC + n) -> rng RNG SRC n -> rng RNG (shad SRC) (shspan SRC n) ->
  unpoisoned m DT (DT + 4) -> rng RNG DT 4 -> rng RNG (shad DT) (shspan DT 4) ->
  17594333495296 <= lo -> rng RNG lo (SPV - lo) -> rng_aimg RNG ->
  0 <= b0 <= 255 -> 0 <= b1 <= 255 -> 0 <= b2 <= 255 -> 0 <= b3 <= 255 -> 0 <= b4 <= 255 -> 0 <= b5 <= 255 ->
  8 <= b0 + 256 * b1 -> 8 <= b2 + 256 * b3 -> 8 <= b4 + 256 * b5 ->
  b0 + (256 * b1 + (b2 + (256 * b3 + (b4 + 256 * b5)))) + 6 <= n ->
  8 <= n - (b0 + 256 * b1) - (b2 + 256 * b3) - (b4 + 256 * b5) - 6 ->
  1 <= dsz -> 10 <= n ->
  nth_error dth 2 = Some (Z_to_bv 8 11) ->
  DST + 3 * ((dsz + 3) / 4) < DST + dsz ->
  0 <= c1 <= 8 ->
  bytes_at bsegs m1 SRC src -> bytes_at bsegs m1 DT dth ->
  munch [(ARGS, ARGS + 152); (SPV + -48, SPV)] m m1 -> wmono bsegs m m1 ->
  stk bsegs m1 lo SPV -> stk bsegs m1 lo (SPV + -48) ->
  rw_cells bsegs m1 (SPV + -48) [CB 8 fjunk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv bsegs m1 ->
  rw_cells bsegs m1 ARGS (fa_args_cells1 DST dsz SRC n b0 b1 b2 b3 b4 b5 ajunk) ->
  evtF bsegs RNG (fast_args_post3A ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV ARGS DST dsz SRC n DT lo m dth)
    (MS (mkR ra (Z_to_bv 64 (SPV + -48)) gp tp
            (Z_to_bv 64 (b0 + (256 * b1 + (b2 + (256 * b3 + (b4 + (256 * b5 + SRC))))) + -2))
            (Z_to_bv 64 (b0 + (256 * b1 + SRC) + -2)) (Z_to_bv 64 2147450880) x8
            x9 (Z_to_bv 64 ARGS) x11
            x12 (Z_to_bv 64 SRC) (Z_to_bv 64 c1)
            (Z_to_bv 64 DT)
            (Z_to_bv 64 (b0 + (256 * b1 + (b2 + (256 * b3 + SRC))) + -2))
            (Z_to_bv 64 (n + SRC + -8))
            x18
            x19 s4 s5 s6 s7 s8 s9 s10 s11
            (Z_to_bv 64 (DST + dsz)) (Z_to_bv 64 (n + SRC))
            (Z_to_bv 64 (SRC + (b0 + (256 * b1 + (b2 + (256 * b3 + (b4 + 256 * b5))))) + 6))
            (Z_to_bv 64 (SRC + (b0 + (256 * b1 + (b2 + 256 * b3))) + 6)))
        F (Z_to_bv 64 0xaa42c) fc None m1 (seg_rom bsegs)).

Lemma fa_tail1 : fa_tail1_stmt.
Proof.
  unfold fa_tail1_stmt.
  intros RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x8 x9 x11 x12 x18 x19 F fc m m1 SPV ARGS DST dsz SRC n DT lo b0 b1 b2 b3 b4 b5 c1 src dth ajunk fjunk.
  intros LO0 LO SPB AA DA SRCL DTL A0 A1 A2 S0 S1 S2 N32 D0 D1 D2 O0 O1 O2 DJ1 DJ2 APA UA RA RAS US RS RSS UD RD RDS KLO RSTK RI.
  intros KXRR KXRR0 KXRR1 KXRR2 KXRR4 KXRR5 KXBR3 KXBR4 KXBR5 KXBR7 L4 DZ KXBR HLOG KF HC1 SRCB DTB MU WM STK0 STK FR KXMI AC.
  unfold fa_args_cells1 in AC.
  assert (ARB : ARGS + 152 <= 0x7fff8000 \/ 0x10007fff8000 <= ARGS) by (unfold app_blk, KLOW, KHIGH, KEND in APA; clear - APA; lia).
  assert (L1 : 8 <= b0 + 256 * b1 <= 65535) by (clear - KXRR KXRR0 KXBR3; lia).
  assert (L2 : 8 <= b2 + 256 * b3 <= 65535) by (clear - KXRR1 KXRR2 KXBR4; lia).
  assert (L3 : 8 <= b4 + 256 * b5 <= 65535) by (clear - KXRR4 KXRR5 KXBR5; lia).
  pose proof (rng_shspanZ _ _ _ RAS) as RAz. pose proof (rng_shspanZ _ _ _ RSS) as RSz. pose proof (rng_shspanZ _ _ _ RDS) as RDz.
  assert (RSTKf : rng RNG (SPV - 48) 48) by (eapply rng_sub; [exact RSTK | clear - LO LO0; lia | clear - LO LO0; lia]).
  fa_carry UA US UD SPV.
  assert (GF0 : (17594333495296 <= SPV <= 140737488355328) /\ (4096 <= ARGS <= 140737488355176) /\ (4096 <= SRC <= 140737488355328) /\
                (0 <= n <= 4294967296) /\ (4096 <= SRC + n <= 140737488355328) /\ (4096 <= DT <= 140737488355324) /\
                (4096 <= DST <= 140737488355328) /\ (0 <= dsz <= 4294967296) /\ (4096 <= DST + dsz <= 140737488355328))
    by (clear - KLO LO SPB A0 A1 S0 S1 SRCL N32 D0 D1 O0 O1 O2; lia).
  destruct GF0 as (GS1 & GS2 & GS3 & GS4 & GS5 & GS6 & GS7 & GS8 & GS9).
  (* [comment removed for export] *)
  assert (ZS1 : 0 <= ARGS - 0 < 2 ^ 64 /\ 0 <= 152 < 2 ^ 64 /\ 0 <= ARGS < 2 ^ 64) by (clear - GS2; lia).
  assert (ZS2 : 0 <= SPV + -48 - -48 < 2 ^ 64 /\ 0 <= 48 < 2 ^ 64 /\ 0 <= SPV + -48 < 2 ^ 64) by (clear - GS1; lia).
  assert (ZS2' : 0 <= SPV - 48 - -48 < 2 ^ 64 /\ 0 <= 48 < 2 ^ 64 /\ 0 <= SPV - 48 < 2 ^ 64) by (clear - GS1; lia).
  assert (ZS3 : 0 <= SRC - 0 < 2 ^ 64 /\ 0 <= n < 2 ^ 64 /\ 0 <= SRC < 2 ^ 64) by (clear - GS3 GS4 GS5; lia).
  assert (ZS4 : 0 <= DT - 0 < 2 ^ 64 /\ 0 <= 4 < 2 ^ 64 /\ 0 <= DT < 2 ^ 64) by (clear - GS6; lia).
  assert (ZS5 : 0 <= ARGS < 2 ^ 64) by (clear - GS2; lia).
  assert (ZS6 : 0 <= DT < 2 ^ 64) by (clear - GS6; lia).
  assert (ZS7 : SPV + -48 + 48 <= SRC \/ SRC + n <= SPV + -48) by (clear - S2 LO; lia).
  assert (ZS8 : SPV + -48 + 48 <= DT \/ DT + 4 <= SPV + -48) by (clear - D2 LO; lia).
  assert (ZS9 : SPV + -48 + 48 <= ARGS \/ ARGS + 152 <= SPV + -48) by (clear - A2 LO; lia).
  (* [comment removed for export] *)
  clear UAc USc UDc UAz USz UDz. fa_carry UA US UD SPV.
  kx_join_begin HJ2.
  { fa_facts b0 b1 b2 b3 b4 b5 c1. Time fa_autoA [0xaa564] b0 b1 b2 b3 b4 b5 c1.
    all: [> kx_read_ranges; kx_mem ..].
    all: [> fa_keep_lb KXA HC1 ..].
    all: [> fa_fix_a4 KR2 ..].
    Time all: [> fa_join HJ2 [6%nat; 8%nat; 9%nat; 11%nat; 12%nat; 18%nat; 19%nat; 31%nat] ..]. }
  kx_join_endF.
  clear UAc USc UDc UAz USz UDz. fa_carry UA US UD SPV.
  kx_join_begin HJ3.
  { fa_amt c2 HC2. fa_facts b0 b1 b2 b3 b4 b5 c2. Time fa_autoA [0xaa69c] b0 b1 b2 b3 b4 b5 c2.
    all: [> kx_read_ranges; kx_mem ..].
    all: [> fa_keep_lb KXA HC2 ..].
    all: [> fa_fix_a4 KR3 ..].
    Time all: [> fa_join HJ3 [6%nat; 8%nat; 9%nat; 11%nat; 12%nat; 16%nat; 18%nat; 19%nat; 30%nat; 31%nat] ..]. }
  kx_join_endF.
  clear UAc USc UDc UAz USz UDz. fa_carry UA US UD SPV.
  kx_join_begin HJ4.
  { fa_amt c3 HC3. fa_facts b0 b1 b2 b3 b4 b5 c3. Time fa_autoA [0xaa7d4] b0 b1 b2 b3 b4 b5 c3.
    all: [> kx_read_ranges; kx_mem ..].
    all: [> fa_keep_lb KXA HC3 ..].
    all: [> fa_fix_a4 KR4 ..].
    Time all: [> fa_join HJ4 [5%nat; 6%nat; 8%nat; 9%nat; 11%nat; 12%nat; 16%nat; 18%nat; 19%nat; 29%nat; 30%nat; 31%nat] ..]. }
  kx_join_endF.
  (* [comment removed for export] *)
  clear UAc USc UDc UAz USz UDz. fa_carry UA US UD SPV.
  fa_amt c4 HC4. fa_facts b0 b1 b2 b3 b4 b5 c4. Time fa_autoA (@nil Z) b0 b1 b2 b3 b4 b5 c4.
  kx_mem.
  fa_keep_lb KXA HC4. unfold kx_keep in *.
  zstep.
  rewrite ?(Z.mod_small (dsz + 3) (2^64)) in * by lia.
  match goal with FRx : rw_cells bsegs ?mm (SPV + -48) _, STx : stk bsegs ?mm lo (SPV + -48) |- _ => release_frame FRx STx SPV end.
  apply evtF_done; unfold fast_args_post3A; repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  left. split; [reflexivity|].
  exists (b0 + 256 * b1), (b2 + 256 * b3), (b4 + 256 * b5). do 4 eexists.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact KF|].
  split.
  { match goal with H : rw_cells bsegs ?mm ARGS ?cs |- rw_cells bsegs ?mm ARGS ?cs' =>
      replace cs' with cs; [exact H|]; unfold fast_args_cells;
      repeat (apply f_equal2; [first [reflexivity | (do 2 apply f_equal; lia)]|]); reflexivity end. }
  split; [exact HLOG|].
  repeat split; apply lb_to_mod512;
    lazymatch goal with |- LB 8 (bv_unsigned ?w) => lazymatch goal with KB : LBW 8 w |- _ => exact KB end end.
Time Qed.
End CANSEC1.
