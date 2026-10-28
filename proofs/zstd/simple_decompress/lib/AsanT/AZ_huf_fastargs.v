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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_huf_iface AZ_huf_iface3 AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_lbkit AZ_huf_fakit AZ_huf_fastargs2.
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

Lemma fast_args_proof3A : fast_args_stmt3A.
Proof.
  unfold fast_args_stmt3A, APHUF_FASTARGS.
  intros until junk. intros MI STK LO0 LO SPB AC AA DA SRCB SRCL DTB DTL A0 A1 A2 S0 S1 S2 N32 D0 D1 D2 O0 O1 O2 DJ1 DJ2 APA AROA AROS AROD ART AST.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  destruct AROA as (UA & RA & RAS). destruct AROS as (US & RS & RSS). destruct AROD as (UD & RD & RDS).
  assert (ARB : ARGS + 152 <= 0x7fff8000 \/ 0x10007fff8000 <= ARGS) by (unfold app_blk, KLOW, KHIGH, KEND in APA; clear - APA; lia).
  assert (MU : munch [(ARGS, ARGS + 152); (SPV - 48, SPV)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  pose proof STK as STK0.
  carve_frame 48%nat STK.
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
  Time kx_autoFLA (GOT, SHB) [KAUnp ARGS 152; KAUnp SRC n; KAUnp DT 4; KAApp ARGS 152; KAApp (SPV - 48) 48] [0xaa274] 400%nat
    [KZRange SPV 17594333495296 140737488355328; KZRange ARGS 4096 140737488355176; KZRange SRC 4096 140737488355328; KZRange n 0 4294967296; KZRange (SRC + n) 4096 140737488355328;
     KZRange DT 4096 140737488355324; KZRange DST 4096 140737488355328; KZRange dsz 0 4294967296; KZRange (DST + dsz) 4096 140737488355328;
     KZAlign ARGS 8; KZAlign DT 4;
     KZWr ARGS 152; KZWr (SPV + -48) 48;
     KZDisj ARGS 152 SRC n; KZDisj ARGS 152 DT 4; KZDisj (SPV + -48) 48 SRC n; KZDisj (SPV + -48) 48 DT 4; KZDisj (SPV + -48) 48 ARGS 152]
    [(SRC, n); (DT, 4); (SPV + -48, 48); (ARGS, 152)] [(SRC, n); (DT, 4); (SPV - 48, 48); (ARGS, 152)].
  (* [comment removed for export] *)
  all: [> try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end ..].
  all: try clear GOT RIC SHB INI LAY REAL.
  all: [> lazymatch goal with
          | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaa424) _ _ _ _) => fa_ret0 FR STK SPV MU WM AC
          | _ => idtac
          end ..].
  (* [comment removed for export] *)
  lazymatch goal with KB : Z.land (bv_unsigned (ev KXE ?k)) 16711680 = 720896 |- _ => kx_read_eq k RDH end.
  rewrite (rdval_bytes_at bsegs m DT dth 0 4 true DTB ltac:(lia) ltac:(change (Z.to_nat 0) with 0%nat; lia)) in RDH.
  assert (HLOG : nth_error dth 2 = Some (Z_to_bv 8 11)).
  { apply (a_hdr_log11 dth DTL). rewrite <- RDH.
    lazymatch goal with KB : Z.land (bv_unsigned (ev KXE _)) 16711680 = 720896 |- _ => exact KB end. }
  clear RDH.
  (* [comment removed for export] *)
  kx_read_ranges. kx_mem.
  remember (bv_unsigned (ev KXE 36)) as b0 eqn:E0. remember (bv_unsigned (ev KXE 37)) as b1 eqn:E1.
  remember (bv_unsigned (ev KXE 40)) as b2 eqn:E2. remember (bv_unsigned (ev KXE 41)) as b3 eqn:E3.
  remember (bv_unsigned (ev KXE 45)) as b4 eqn:E4. remember (bv_unsigned (ev KXE 46)) as b5 eqn:E5.
  clear E0 E1 E2 E3 E4 E5.
  assert (L1 : 8 <= b0 + 256 * b1 <= 65535) by lia.
  assert (L2 : 8 <= b2 + 256 * b3 <= 65535) by lia.
  assert (L3 : 8 <= b4 + 256 * b5 <= 65535) by lia.
  assert (L4 : 8 <= n - (b0 + 256 * b1) - (b2 + 256 * b3) - (b4 + 256 * b5) - 6) by lia.
  assert (DZ : 1 <= dsz) by lia.
  repeat (match goal with H : ?T |- _ => lazymatch T with context [KXE] => clear H end end).
  (* [comment removed for export] *)
  clear UAc USc UDc UAz USz UDz. fa_carry UA US UD SPV. fa_facts b0 b1 b2 b3 b4 b5 0.
  kx_join_begin HJ1.
  { Time fa_autoA [0xaa42c] b0 b1 b2 b3 b4 b5 0.
    all: [> lazymatch goal with
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaa424) _ _ _ _) => fa_ret0 FR STK SPV MU WM AC
            | _ => idtac
            end ..].
    all: [> rewrite ?(Z.mod_small (dsz + 3) (2^64)) in * by lia ..].
    all: [> kx_fact KF (DST + 3 * ((dsz + 3) / 4) < DST + dsz) ..].
    all: [> kx_read_ranges; kx_mem ..].
    all: [> fa_fix_a4 KR1 ..].
    Time all: [> fa_join HJ1 [8%nat; 9%nat; 11%nat; 12%nat; 18%nat; 19%nat] ..]. }
  kx_join_endF.
  (* [comment removed for export] *)
  fa_amt c1 HC1.
  rewrite ?(Z.mod_small (dsz + 3) (2^64)) in * by (clear - GS8 DZ; lia).
  lazymatch goal with
  | ACx : rw_cells _ ?mc ARGS _, FRx : rw_cells _ ?mc (SPV + -48) _, MUx : munch _ m ?mc, WMx : wmono _ m ?mc,
    SBx : bytes_at _ ?mc SRC src, DBx : bytes_at _ ?mc DT dth, MIx : mem_inv _ ?mc, SKa : stk _ ?mc lo SPV, SKb : stk _ ?mc lo (SPV + -48) |- _ =>
      eapply (fa_tail1 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ _ F fc m mc SPV ARGS DST dsz SRC n DT lo b0 b1 b2 b3 b4 b5 c1 src dth _ _);
      first [ exact ACx | exact FRx | exact MUx | exact WMx | exact SBx | exact DBx | exact MIx | exact SKa | exact SKb | assumption
            | lazymatch goal with |- ?G => idtac "fa_tail1 LEFT:" G; fail end ]
  end.
Time Qed.
End CANSEC1.
