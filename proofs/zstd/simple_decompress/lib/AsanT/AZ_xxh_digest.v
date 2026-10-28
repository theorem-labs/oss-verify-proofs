(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_frame_iface AZ_kx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma xd_disjoint_from_above : forall W A n K, Forall (fun iv : Z * Z => K <= fst iv) W -> A + n <= K -> disjoint_from W A n.
Proof.
  induction W as [|[lo' hi'] W IH]; intros A n K HW HA; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [lia|]. eapply IH; eassumption.
Qed.
Lemma xd_art_transport : forall W m m', art m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => 0xd1740 <= fst iv) W -> art m'.
Proof.
  intros W m m' (GOT & RIC & SHB & INI & LAY & REAL) MU WM HW.
  unfold art. repeat split.
  all: first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply xd_disjoint_from_above; [exact HW| cbn; lia]]
             | eapply ro_cells_transport; [eassumption| exact MU| eapply xd_disjoint_from_above; [exact HW| cbn; lia]] ].
Qed.

Section DIGEST.
  Variables (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV S8 lo : Z) (st : list byte).
  Hypothesis STB : bytes_at bsegs m (8 * S8) st.
  Hypothesis STL : zlen st = 88.
  Hypothesis R0 : 0x625000 <= 8 * S8.
  Hypothesis R1 : 8 * S8 + 88 <= 2^47.
  Hypothesis SA : 8 * S8 + 88 <= 0x7fff7000 \/ 0x10007fff8000 <= 8 * S8.
  Hypothesis ST : stk bsegs m lo SPV.
  Hypothesis KLO : 17594333495296 <= lo.
  Hypothesis LO : lo <= SPV - 64.
  Hypothesis SPV47 : SPV < 2^47.
  Hypothesis SS : 8 * S8 + 88 <= lo \/ SPV <= 8 * S8.
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis US : unpoisoned m (8 * S8) (8 * S8 + 88).
  Hypothesis RS : rng RNG (8 * S8) 88.
  Hypothesis RSS : rng RNG (2147450880 + S8) 11.
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis ATR : 140735332483072 <= ATOP <= 140737479966720.

  Notation POST := (zd_xxh_digest_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV lo m).
  (* [comment removed for export] *)
  Notation STf pc mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 (SPV + -32)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition FIN (m1 : amem) : Prop :=
    (exists j, rw_cells bsegs m1 (SPV + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]) /\ stk bsegs m1 lo (SPV + -32) /\
    munch [(SPV - 64, SPV)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ bytes_at bsegs m1 (8 * S8) st /\
    unpoisoned m1 (8 * S8) (8 * S8 + 88).

  Lemma FIN_zero : forall m1, FIN m1 -> forall i, 0 <= i < 11 -> m1 (wa (2147450880 + S8 + i)) = Some (Z_to_bv 8 0).
  Proof. intros m1 (_ & _ & _ & _ & _ & _ & U) i Hi. exact (unp_zero_win m1 S8 88 U i ltac:(lia)). Qed.

  (* [comment removed for export] *)
  Lemma f_epi : forall m1 (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FIN m1 -> evtF bsegs RNG POST (STf 0xb004c m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    intros until x31. intros ((j & FR) & ST1 & MU1 & WM1 & MI1 & SB1 & U1).
    kx_autoFLx [] 40%nat [KZRange SPV 4096 (2^47); KZWr (SPV - 32) 32] [(SPV - 32, 32)] [(SPV - 32, 32)].
    all: try kx_cell_lit. all: try kx_z.
    all: kx_mem. all: zstep.
    all: release_frame FR ST1 SPV.
    all: apply evtF_done; unfold zd_xxh_digest_postA; do 15 eexists; exists m1.
    all: split; [reflexivity|]. all: split; [exact MU1|]. all: split; [exact WM1|]. all: split; [exact MI1| exact ST1].
  Qed.

  (* [comment removed for export] *)
  Lemma f_l1 : forall (n : nat) m1 p r (x6 x7 x8 x9 x12 x13 x15 x16 x17 x28 x29 x30 x31 : word),
    r <= Z.of_nat n -> 0 <= p -> 1 <= r -> p + r <= 32 -> FIN m1 ->
    evtF bsegs RNG POST (STf 0xafffc m1 (Z_to_bv 64 r) x6 x7 x8 x9 (Z_to_bv 64 (8 * S8 + 40 + p)) (Z_to_bv 64 (8 * S8 + 40 + p))
                             x12 x13 (Z_to_bv 64 2147450880) x15 x16 x17 x28 x29 x30 x31).
  Proof.
    induction n as [|n IH]; intros until x31; intros RN RP RR RPR FI; [exfalso; lia|].
    pose proof FI as ((j & FR) & ST1 & MU1 & WM1 & MI1 & SB1 & U1).
    pose proof (FIN_zero m1 FI) as ZW.
    kx_autoFLx [0xafffc; 0xb004c] 40%nat
      [KZRange S8 (0x625000 / 8) (2^44); KZRange p 0 32; KZRange r 1 32; KZRange (32 - p - r) 0 32; KZZero (2147450880 + S8) 11]
      [(8 * S8, 88)] [(8 * S8, 88); (2147450880 + S8, 11)].
    all: try kx_z. all: try kx_sh_acc RSS. all: try kx_sh_rd_any. all: try kx_sh_dead0_any. all: try kx_acc RI.
    all: try (split; [lia|]; split; [lia| exact ZW]).
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 720892) _ _ _ _) =>
             replace (8 * S8 + p + 41) with (8 * S8 + 40 + (p + 1)) by lia;
             eapply (IH m1 (p + 1) (r + -1)); try lia; exact FI
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 720972) _ _ _ _) => apply f_epi; exact FI
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma f_l4 : forall m1 k r (x6 x7 x8 x9 x11 x12 x13 x15 x16 x17 x28 x29 x30 x31 : word),
    0 <= k <= 3 -> 0 <= r <= 7 -> 8 * k + r <= 31 -> FIN m1 ->
    evtF bsegs RNG POST (STf 0xaff74 m1 (Z_to_bv 64 r) x6 x7 x8 x9 (Z_to_bv 64 (8 * S8 + 40 + 8 * k)) x11 x12 x13
                             (Z_to_bv 64 2147450880) x15 x16 x17 x28 x29 x30 x31).
  Proof.
    intros until x31. intros RK RR RKR FI.
    pose proof FI as ((j & FR) & ST1 & MU1 & WM1 & MI1 & SB1 & U1).
    pose proof (FIN_zero m1 FI) as ZW.
    kx_autoFLx [0xafffc; 0xb004c] 60%nat
      [KZRange S8 (0x625000 / 8) (2^44); KZRange k 0 3; KZRange r 0 7; KZRange (31 - 8 * k - r) 0 31;
       KZZero (2147450880 + S8) 11; KZImg 0x10310 0x10320]
      [(8 * S8, 88)] [(8 * S8, 88); (2147450880 + S8, 11)].
    all: try kx_z. all: try kx_sh_acc RSS. all: try kx_sh_rd_any. all: try kx_sh_dead0_any. all: try kx_acc RI.
    all: try (split; [lia|]; split; [lia| exact ZW]).
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 720892) _ _ _ _) =>
             first [ replace (8 * S8 + 8 * k + 40) with (8 * S8 + 40 + 8 * k) by lia;
                     eapply (f_l1 (Z.to_nat r) m1 (8 * k) r); try lia; exact FI
                   | replace (8 * S8 + 8 * k + 44) with (8 * S8 + 40 + (8 * k + 4)) by lia;
                     eapply (f_l1 (Z.to_nat r) m1 (8 * k + 4) (r + -4)); try lia; exact FI ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 720972) _ _ _ _) => apply f_epi; exact FI
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma f_l8 : forall (n : nat) m1 k r (x6 x7 x8 x9 x13 x15 x16 x17 x29 x30 x31 : word),
    r <= Z.of_nat n -> 0 <= k -> 8 <= r -> 8 * k + r <= 31 -> FIN m1 ->
    evtF bsegs RNG POST (STf 0xafe9c m1 (Z_to_bv 64 r) x6 x7 x8 x9 (Z_to_bv 64 (8 * S8 + 40 + 8 * k))
                             (Z_to_bv 64 (2147450880 + S8 + 5 + k)) (Z_to_bv 64 (8 * S8 + 40 + 8 * k)) x13
                             (Z_to_bv 64 2147450880) x15 x16 x17 (Z_to_bv 64 7) x29 x30 x31).
  Proof.
    induction n as [|n IH]; intros until x31; intros RN RK RR RKR FI; [exfalso; lia|].
    pose proof FI as ((j & FR) & ST1 & MU1 & WM1 & MI1 & SB1 & U1).
    pose proof (FIN_zero m1 FI) as ZW.
    kx_autoFLx [0xafe9c; 0xaff74] 60%nat
      [KZRange S8 (0x625000 / 8) (2^44); KZRange k 0 2; KZRange r 8 31; KZRange (31 - 8 * k - r) 0 31;
       KZZero (2147450880 + S8) 11]
      [(8 * S8, 88)] [(8 * S8, 88); (2147450880 + S8, 11)].
    all: try kx_z. all: try kx_sh_acc RSS. all: try kx_sh_rd_any. all: try kx_sh_dead0_any. all: try kx_acc RI.
    all: try (split; [lia|]; split; [lia| exact ZW]).
    all: try replace (8 * S8 + 8 * k + 48) with (8 * S8 + 40 + 8 * (k + 1)) by lia.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 720540) _ _ _ _) =>
             replace (S8 + k + 2147450886) with (2147450880 + S8 + 5 + (k + 1)) by lia;
             eapply (IH m1 (k + 1) (r + -8)); try lia; exact FI
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 720756) _ _ _ _) =>
             eapply (f_l4 m1 (k + 1) (r + -8)); try lia; exact FI
         end.
  Qed.

  (* [comment removed for export] *)
  Hypothesis ART : art m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma d_main : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (8 * S8)) a1 a2 a3 a4 a5 a6 a7
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 APZD_XXH_DIGEST) fc None m (seg_rom bsegs)).
  Proof.
    intros until t6.
    pose proof ART as (GOT & RIC & SHB & INI & LAY & REAL).
    assert (MU : munch [(SPV - 64, SPV)] m m) by apply munch_refl. assert (WM : wmono bsegs m m) by apply wmono_refl.
    pose proof (unp_zero_win m S8 88 US) as ZW0.
    pose proof ST as ST0. pose proof MI as MI0. pose proof STB as STB0. pose proof US as US0.
    carve_frame 32%nat ST0.
    unfold APZD_XXH_DIGEST.
    kx_autoFLx [0xafe9c; 0xaff74] 200%nat
      [KZRange SPV 4096 (2^47); KZRange S8 (0x625000 / 8) (2^44); KZWr (SPV - 32) 32; KZZero (2147450880 + S8) 11;
       KZDisj (8 * S8) 88 (SPV - 32) 32; KZImg 0x10310 0x103e8]
      [(SPV - 32, 32); (8 * S8, 88)] [(SPV - 32, 32); (8 * S8, 88); (2147450880 + S8, 11)].
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI. all: try kx_sh_acc RSS. all: try kx_sh_rd_any. all: try kx_sh_dead0_any.
    all: try (split; [lia|]; split; [lia| intros i Hi; apply ZW0; change (88 / 8) with 11; lia]).
    all: kx_mem.
    all: assert (FI : FIN m0)
           by (split; [eexists; eassumption|]; split; [eassumption|]; split; [exact MU|]; split; [exact WM|];
               split; [exact KXMI|]; split; [eassumption|];
               eapply unpoisoned_munch; [exact US0 | exact MU | cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF;
                 repeat split; Z.div_mod_to_equations; lia]).
    all: lazymatch goal with
         | |- context [Z.land ?X 31] =>
             assert (RT : 0 <= Z.land X 31 <= 31)
               by (replace (Z.land X 31) with (X mod 32)
                     by (symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity);
                   pose proof (Z.mod_pos_bound X 32 ltac:(lia)); lia);
             set (r := Z.land X 31) in *
         | |- evtF _ _ _ (MS (mkR _ _ _ _ ?X5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
             rewrite <- (Z_to_bv_bv_unsigned X5);
             assert (RT : 0 <= bv_unsigned X5 <= 31) by (pose proof (bv_unsigned_in_range 64 X5); lia);
             set (r := bv_unsigned X5) in *
         end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 720540) _ _ _ _) =>
             replace (8 * S8 + 40) with (8 * S8 + 40 + 8 * 0) by lia;
             replace (S8 + 2147450885) with (2147450880 + S8 + 5 + 0) by lia;
             eapply (f_l8 (Z.to_nat r) m0 0 r); try lia; exact FI
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 720756) _ _ _ _) =>
             replace (8 * S8 + 40) with (8 * S8 + 40 + 8 * 0) by lia;
             eapply (f_l4 m0 0 r); try lia; exact FI
         end.
  Qed.
End DIGEST.

Lemma zd_xxh_digest_proofA : zd_xxh_digest_stmtA.
Proof.
  intros RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV STA st lo.
  intros SB SL STA0 STA8 STA1 ST LO SPV47 SS ARS ART AST MI ->.
  destruct (ARS ltac:(lia)) as (ABS & US & RS & RSS). clear ARS.
  pose proof AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  assert (SA : STA + 88 <= 0x7fff7000 \/ 0x10007fff8000 <= STA) by (unfold ablk, AIMG_HI, KLS in ABS; lia).
  assert (SAL : 0x625000 <= STA) by (unfold ablk, AIMG_HI, KLS in ABS; lia).
  assert (S8E : STA = 8 * (STA / 8)) by (Z.div_mod_to_equations; lia).
  set (S8 := STA / 8) in *. clearbody S8. subst STA.
  assert (RSS' : rng RNG (2147450880 + S8) 11).
  { eapply rng_sub; [exact RSS | |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia. }
  apply (d_main RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV S8 lo st); try assumption; lia.
Qed.
End CANSEC1.
