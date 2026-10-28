(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk PropExec MState.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdWalkKit ZdCellKit SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_initds.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Notation FSE_INITDS_STACK_A := 16 (only parsing).

Section CANSEC2. Context {rc : runConstT}.
(* [comment removed for export] *)
Ltac ids_base t := lazymatch t with context [?x] => x | _ => t end.
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
Lemma fse_initds_c2 : fse_initds_atA (fun bc tl ptr SRC n => bc + tl <= 64 /\ ptr = SRC).
Proof.
  unfold fse_initds_atA, APFSE_INITDS. intros until junk.
  intros KC MI STK LO0 LOS SPR STC BDC FOK BC2 SRCB SRCL DTC TLR A1 A2 A3 R1 R2 R3 R4 R5 R6 R7 R8 D1 D2 D3 D4 D5 OF1 OF2 OF3 OF4
         ART AST AROC AST16 ABD40 ADT4 ASRC APS APB.
  destruct FOK as (BCR & BOK).
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL). destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  destruct AST16 as (UST & RST & RSST). destruct ABD40 as (UBD & RBD & RSBD). destruct ADT4 as (UDT & RDT & RSDT).
  assert (ABM : aro RNG m 140896 128). { apply (aro_client_at _ _ _ _ AROC). cbn [ACLIENT_RO In]. do 30 right. left. reflexivity. }
  destruct ABM as (UBM & RBM & RSBM).
  assert (BAS : ST + 16 <= 0x7fff8000 \/ 0x10007fff8000 <= ST) by (destruct APS as [_ X]; unfold KLOW, KHIGH, KEND in X; clear - X; lia).
  assert (BAB : BD + 40 <= 0x7fff8000 \/ 0x10007fff8000 <= BD) by (destruct APB as [_ X]; unfold KLOW, KHIGH, KEND in X; clear - X; lia).

  unfold bitd_cells in BDC. destruct (cb16_as_c8c8A m ST junk STC) as (w0 & w1 & HST). clear STC.
  pose proof (fbitmask_know m tl MI ltac:(lia)) as BK. unfold FBITMASK in BK.
  assert (RP : 1 <= 2^tl <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
  assert (MUL : munch [(ST, ST + 16); (BD, BD + 40); (SPV - 16, SPV)] m m) by apply munch_refl. assert (WMl : wmono bsegs m m) by apply wmono_refl.
  carve_frame 16%nat STK.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  clear BOK.
  (* [comment removed for export] *)
  Ltac rs_rdS H :=
    kx_side_pre;
    lazymatch goal with
    | KXA : atoms_ok ?zs ?E |- rd_ok ?segs ?mm _ ?a ?nn =>
        let nz := kx_len zs in let P := kx_rd_fact segs mm H in
        eapply (kx_rd_ok segs mm E a nn _ _ P); kx_estarts E zs nz KXA; rewrite ?length_map; kx_lia
    end.
  (* [comment removed for export] *)
  Ltac kx_abs_hyp H :=
    repeat match type of H with
           | context [ev ?E ?j] => let b := fresh "rb" in set (b := ev E j) in *; clearbody b
           | context [edenot ?E ?e] => let b := fresh "rw" in set (b := edenot E e) in *; clearbody b
           end.
  rename KC into C.
  (* [comment removed for export] *)
    destruct C as (C1 & C2). subst ptr.
    kx_autoFLAc (HST, BDC, DTC, FR, GOT, SHB)
      [KAUnp ST 16; KAUnp BD 40; KAUnp DT 4; KAUnp 140896 128; KAApp ST 16; KAApp BD 40; KAApp (SPV - 16) 16]
      (@nil Z) 330%nat
      ([KZRange bc 0 64; KZRange (bc + tl) 0 64; KZRange n 0 (2^47)] ++ [KZRange SPV (0x10007fff8000 + 16) (2^47 - 1); KZRange BD 4096 (2^47 - 41); KZRange ST 4096 (2^47 - 17); KZRange DT 4096 (2^47 - 5);
            KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange tl 0 12; KZRange (2^tl) 1 4096;
            KZAlign BD 8; KZAlign ST 8; KZAlign DT 4;
            KZWord (140896 + 4 * tl) 4 (2^tl - 1);
            KZWr BD 40; KZWr ST 16; KZWr (SPV - 16) 16;
            KZDisj BD 40 ST 16; KZDisj BD 40 SRC n; KZDisj ST 16 SRC n; KZDisj (SPV - 16) 16 SRC n; KZDisj (SPV - 16) 16 BD 40; KZDisj (SPV - 16) 16 ST 16;
            KZDisj BD 40 DT 4; KZDisj ST 16 DT 4; KZDisj (SPV - 16) 16 DT 4; KZImg 0x22660 0x226e0])
      (@nil (Z * Z)) [(ST, 16); (BD, 40); (DT, 4); (SPV - 16, 16); (140896, 128)].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb208c) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: try kx_acc RSRC. all: try kx_acc RI.
    all: try (rs_rdS SRCB). all: try kx_z.
    all: clear GOT RIC SHB INI LAY REAL UST UBD UDT UBM RST RSST RBD RSBD RDT RSDT RBM RSBM BK; try clear USRC RSRC RSSRC.
    all: kx_mem. all: kx_gen_regsF [7%nat; 29%nat]; kx_abs_hyp BDC; kx_tidy_run.
    all: zstep.
    all: apply stk_of_rw_cells in FR; cbn [cells_size csize Nat.add] in FR.
    all: assert (STK' : stk bsegs _ lo SPV) by (eapply (stk_merge bsegs _ lo (SPV + -16) SPV STK); [|clear - LOS; lia]; replace SPV with (SPV + -16 + Z.of_nat 16) at 2 by (clear; lia); exact FR).
    all: apply evtF_done; unfold fse_initds_postA, bitd_cells; do 20 eexists;
         split; [reflexivity|]; split; [exact MUL|]; split; [exact WMl|]; split; [eassumption|]; split; [exact STK'|];
         split; [exact HST|]; split; [apply fuland_mask_lt; clear - TLR; lia|]; split; [exact BDC|];
         split; [unfold fbit_ok; split; [first [clear - C BCR TLR BC2 | clear - C1 BCR TLR BC2 Q1 Q2 Q3 Q4 QD | clear - C1 BCR TLR BC2 Q1 Q2 Q3 Q4 | clear - C1 BCR TLR BC2]; lia | intros FBC] | split; [first [clear - C | clear - C1 Q1 Q2 Q3 Q4 QD | clear - C1 Q1 Q2 | clear - C1]; lia| exact DTC]].
    left. reflexivity.
Qed.
End CANSEC2.
