(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk PropExec MState.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdWalkKit ZdCellKit SepHide.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_initds AZ_hft_dsym.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC2. Context {rc : runConstT}.
(* [comment removed for export] *)
Local Ltac kxa_unpZ ::=
  lazymatch goal with
  | |- unpZ ?mm ?lo1 ?hi1 =>
      first [ kxa_hyp
            | match goal with
              | U : unpoisoned mm ?X ?hi0 |- _ =>
                  lazymatch lo1 with context [X] => apply (unpoisoned_unpZ mm X hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia] end
              end
            | match goal with
              | U : unpoisoned mm ?lo0 ?hi0 |- _ => apply (unpoisoned_unpZ mm lo0 hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia]
              end
            | kxa_unp_hook ]
  end.
Local Ltac kxa_rng0 ::=
  kxa_norm;
  lazymatch goal with
  | |- rng ?RG (KXSHLO + ?A / 8) (shspanZ ?A ?n) =>
      first [ match goal with
              | H : rng RG (shad ?X) ?N0 |- _ =>
                  lazymatch A with context [X] =>
                    apply (shad_shspan_rng RG A n (shad X) N0 H);
                    [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
                  end
              end
            | match goal with
              | H : rng RG (shad ?A0) ?N0 |- _ =>
                  apply (shad_shspan_rng RG A n (shad A0) N0 H);
                  [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
              | H : rng RG ?A0 ?N0 |- _ =>
                  apply (shad_shspan_rng RG A n A0 N0 H);
                  [ rewrite shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
              end
            | lazymatch RG with
              | (fun _ _ => True) => split; [unfold KXSHLO; kx_lia | split; [unfold KXSHLO, shspanZ; Z.div_mod_to_equations; lia | intros; exact I]]
              end
            | kxa_rng_hook ]
  end.
(* [comment removed for export] *)
Ltac kx_abs_hyp H :=
  repeat match type of H with
         | context [ev ?E ?j] => let b := fresh "rb" in set (b := ev E j) in *; clearbody b
         | context [edenot ?E ?e] => let b := fresh "rw" in set (b := edenot E e) in *; clearbody b
         end.

Theorem fse_dsym_proofA : fse_dsym_stmtA.
Proof.
  unfold fse_dsym_stmtA, fse_dsym_stmtA_at, APFSE_DSYM. intros fast. intros until tb.
  intros MI STK LO0 LOS SPR STC SR BDC BCR CELB TBLEN TBBY TBOK FR01 TLR A1 A2 A3 R1 R2 R3 R4 R5 R6 D1 D2 D3 O1 O2 O3 ART AST AROC AROS AROB AROT APS APB.
  pose proof ART as ART0. destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  destruct AROS as (US & RS & RSS). destruct AROB as (UB & RB & RSB). destruct AROT as (UT & RT & RST).
  assert (ABM : aro RNG m 140512 128). { apply (aro_client_at _ _ _ _ AROC). cbn [ACLIENT_RO In]. do 30 right. left. reflexivity. }
  destruct ABM as (UBM & RBM & RSBM).
  assert (BAS : ST + 16 <= 0x7fff8000 \/ 0x10007fff8000 <= ST) by (destruct APS as [_ X]; unfold KLOW, KHIGH, KEND in X; clear - X; lia).
  assert (BAB : BD + 40 <= 0x7fff8000 \/ 0x10007fff8000 <= BD) by (destruct APB as [_ X]; unfold KLOW, KHIGH, KEND in X; clear - X; lia).
  unfold bitd_cells in BDC.
  assert (MU : munch [(ST, ST + 16); (BD, BD + 40); (SPV - 16, SPV)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (P2 : 1 <= 2^tl <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
  assert (TBV : fd_tblv tl fast tb) by (split; [exact TBLEN | split; [exact FR01 | split; [exact TBBY | exact TBOK]]]).
  destruct (fd_cell tl fast tb st TBV ltac:(lia) SR) as (NBR & _ & NX0 & NXB & SYR & B0R & B1R).
  assert (TBLEN2 : zlen (map (Z_to_bv 8) tb) = 4 * 2^tl) by (rewrite length_map; lia).
  carve_frame 16%nat STK.
  (* [comment removed for export] *)
  kx_autoFLAc (FR, STC, BDC, GOT, SHB) [KAApp (SPV - 16) 16; KAUnp ST 16; KAUnp BD 40; KAUnp (DT + 4) (4 * 2^tl); KAApp ST 16; KAApp BD 40] [0xb23ec] 80%nat
    [KZRange SPV (0x10007fff8000 + 16) (2^47); KZRange ST 4096 (2^47 - 24); KZRange BD 4096 (2^47 - 48); KZRange DT 4092 (2^47 - 8);
     KZRange st 0 4095; KZRange tl 0 12; KZRange (2^tl) 1 4096; KZRange (2^tl - st) 1 4096; KZRange bc 0 4096; KZRange (DT + 4 + 4 * 2^tl) 0 (2^47);
     KZAlign ST 8; KZAlign BD 8; KZAlign DT 4;
     KZWr (SPV - 16) 16; KZWr BD 40; KZWr ST 16; KZDisj (SPV - 16) 16 (DT + 4) (4 * 2^tl); KZDisj BD 40 (DT + 4) (4 * 2^tl); KZDisj ST 16 (DT + 4) (4 * 2^tl);
     KZDisj BD 40 ST 16; KZDisj (SPV - 16) 16 ST 16; KZDisj (SPV - 16) 16 BD 40]
    [(DT + 4, 4 * 2^tl)] [(SPV - 16, 16); (ST, 16); (BD, 40); (DT + 4, 4 * 2^tl)].
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb247c) _ _ _ _) => kx_trap_fast | _ => idtac end.
  all: try kx_cell_lit. all: try kx_acc RSTK. all: try kx_acc RS. all: try kx_acc RB. all: try kx_acc RT. all: try kx_acc RI. all: try kx_z.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ ?x5 _ _ _ _ _ _ _ _ _ _ ?x16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      lazymatch x16 with ev ?E ?j => kx_read_eq j RDNX end;
      lazymatch x5 with ev ?E ?j => kx_read_eq j RDW2 end
    end.
  replace (DT + 4 * st + 4) with (DT + 4 + 4 * st) in RDNX by lia.
  rewrite (fd_rd2 m (DT + 4) tb (4 * st)) in RDNX; [| exact CELB | exact TBBY | lia | lia].
  replace (DT + 4 * st + 6) with (DT + 4 + (4 * st + 2)) in RDW2 by lia.
  rewrite (fd_rd2 m (DT + 4) tb (4 * st + 2)) in RDW2; [| exact CELB | exact TBBY | lia | lia].
  replace (4 * st + 2 + 1) with (4 * st + 3) in RDW2 by lia.
  change (Znth (4 * st) tb + 256 * Znth (4 * st + 1) tb) with (fc_nx tb st) in RDNX.
  change (Znth (4 * st + 2) tb) with (fc_sy tb st) in RDW2. change (Znth (4 * st + 3) tb) with (fc_nb tb st) in RDW2.
  set (nb := fc_nb tb st) in *. set (nx := fc_nx tb st) in *. set (sy := fc_sy tb st) in *. clearbody nb nx sy.
  kx_gen_regsF [11%nat; 6%nat].
  kx_mem.
  rewrite RDNX, RDW2 in *. clear RDNX RDW2.
  rewrite ?(unsigned_lit nx), ?(unsigned_lit (sy + 256 * nb)) in * by (clear - NBR NX0 NXB SYR TLR P2; lia).
  kx_tidy_run.
  zstep. zstep. rewrite (cell_word nx (sy + 256 * nb)) by (clear - NBR NX0 NXB SYR TLR P2; lia).
  zstep. rewrite (cell_hi29 nx sy nb) by (clear - NBR NX0 NXB SYR TLR P2; lia).
  zstep. if_cases G; zify_cond G; [ exfalso; clear - G; lia | clear G ].
  zstep.
  replace (Z.shiftr ((Z.shiftl (sy + 256 * nb) 16) mod 18446744073709551616) 24) with nb by (symmetry; change 18446744073709551616 with (2^64); apply sn_nb; clear - NBR SYR TLR; lia).
  replace (ST mod 18446744073709551616 / 8 + 2147450880) with (2147450880 + ST / 8) by (rewrite Z.mod_small by (clear - R1 R2; lia); clear; lia).
  replace ((BD + 8) mod 18446744073709551616 / 8 + 2147450880) with (2147450880 + (BD + 8) / 8) by (rewrite Z.mod_small by (clear - R3 R4; lia); clear; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (fbitmask_know mm nb KXMI ltac:(clear - NBR TLR; lia)) as BK end. unfold FBITMASK in BK.
  assert (M1 : 1 <= 2^nb <= 2^tl) by (split; [pose proof (Z.pow_pos_nonneg 2 nb ltac:(lia) ltac:(clear - NBR; lia)); lia | apply Z.pow_le_mono_r; clear - NBR; lia]).
  (* [comment removed for export] *)
  assert (AW : aappW [(ST, ST + 16); (BD, BD + 40); (SPV + -16, SPV)]).
  { unfold aappW. destruct APS as [_ XS]; destruct APB as [_ XB]. unfold KLOW, KLS, KHIGH, KEND in *.
    repeat (constructor; [cbn [fst snd]; clear - XS XB KLO LOS; lia|]). constructor. }
  Ltac unp_tr U MU AW := eapply unpoisoned_munch; [exact U | exact MU | apply aappW_shadow_disjoint; [exact AW | | | |]; rewrite ?shad_div; unfold ASHOFF, KEND; Z.div_mod_to_equations; lia].
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (US' : unpoisoned mm ST (ST + 16)) by unp_tr US MU AW;
    assert (UB' : unpoisoned mm BD (BD + 40)) by unp_tr UB MU AW;
    assert (UBM' : unpoisoned mm 140512 (140512 + 128)) by unp_tr UBM MU AW end.
  clear US UB UT UBM.
  kx_autoFLAc (FR, STC, BDC)
      [KAApp (SPV - 16) 16; KAUnp ST 16; KAUnp BD 40; KAUnp 140512 128; KAApp ST 16; KAApp BD 40; KAShp (2147450880 + ST / 8) ST; KAShp (2147450880 + (BD + 8) / 8) (BD + 8)]
      (@nil Z) 60%nat
      [KZRange SPV (0x10007fff8000 + 16) (2^47); KZRange ST 4096 (2^47 - 24); KZRange BD 4096 (2^47 - 48); KZRange DT 4092 (2^47 - 8);
       KZRange st 0 4095; KZRange tl 0 12; KZRange (2^tl) 1 4096; KZRange bc 0 4096; KZRange nb 0 12; KZRange nx 0 4095; KZRange sy 0 255; KZRange (2^nb) 1 4096;
       KZAlign ST 8; KZAlign BD 8; KZWord (140512 + 4 * nb) 4 (2^nb - 1);
       KZWr (SPV - 16) 16; KZWr BD 40; KZWr ST 16;
       KZDisj BD 40 ST 16; KZDisj (SPV - 16) 16 ST 16; KZDisj (SPV - 16) 16 BD 40; KZImg 0x224e0 0x22560]
      (@nil (Z * Z)) [(SPV - 16, 16); (ST, 16); (BD, 40); (140512, 128)].
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb247c) _ _ _ _) => kx_trap_fast | _ => idtac end.
  all: try kx_cell_lit. all: try kx_acc RSTK. all: try kx_acc RS. all: try kx_acc RB. all: try kx_acc RBM. all: try kx_acc RI. all: try kx_z.
  kx_gen_regsF [6%nat; 7%nat; 17%nat].
  clear US' UB' UBM' RS RSS RB RSB RT RST RBM RSBM GOT RIC SHB INI LAY REAL BK.
  kx_mem. kx_tidy_run.
  lazymatch type of STC with context [Z.land ?x ?msk] => set (b := Z.land x msk) in * end.
  assert (LB : 0 <= b < 2^nb) by (subst b; apply fuland_mask_lt; clear - NBR TLR; lia). clearbody b.
  zstep.
  apply stk_of_rw_cells in FR; cbn [cells_size csize Nat.add length firstn] in FR.
  lazymatch type of FR with stk _ ?mm _ ?h =>
    assert (STK' : stk bsegs mm lo SPV) by (eapply (stk_merge bsegs mm lo (SPV + -16) SPV STK); [|clear - LOS; lia]; replace SPV with h at 2 by (clear - LOS; lia); exact FR) end.
  apply evtF_done. unfold fse_dsym_postA, bitd_cells. do 16 eexists. exists (nx + b), (bc + nb).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STK'|].
  split; [exact STC|]. split; [clear - LB NX0 NXB; lia|]. split; [| clear - NBR; lia].
  replace (bc + nb) with (nb + bc) by (clear; lia). exact BDC.
Qed.
End CANSEC2.
