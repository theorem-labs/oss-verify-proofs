(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdSeqBuildWU ZdSeqBuildW3 ZdSeqBuildW4 SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_blk_iface AZ_kx AZ_bfse_defs AZ_bfse_p2a.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit AZ_bfse_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.
Section P2C.
  Variables (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
            (SPV lo DT NC BASE BITS W wlen maxSV tl : Z) (k : seq_kind) (norm : list Z).
  Hypothesis HY : bfA_hyps RNG SPV lo DT NC BASE BITS W wlen maxSV tl k norm.
  Hypothesis UDT : unpoisoned m DT (DT + 8 + 8 * 2^tl).
  Hypothesis UW : unpoisoned m W (W + wlen).
  Hypothesis UNC : unpoisoned m NC (NC + 2 * zlen norm).
  Hypothesis UBA : unpoisoned m BASE (BASE + 4 * (kind_max k + 1)).
  Hypothesis UBI : unpoisoned m BITS (BITS + (kind_max k + 1)).
  Hypothesis ART0 : art m.
  Notation BFm := (BFA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC BASE BITS W wlen maxSV tl k norm).
  (* [comment removed for export] *)
  Local Ltac kx_lia_bf :=
    lazymatch goal with
    | |- context [_ + _ <= _ \/ _] => first [ kx_sep_unhide7 DT NC SPV lo W BASE BITS; lia | lia | kx_bv_ranges; lia ]
    | |- _ => first [ lia | kx_bv_ranges; lia ]
    end.
  Local Ltac kx_lia ::= kx_lia_bf.
  Local Ltac kxl_lia ::= kx_lia_bf.
  (* [comment removed for export] *)
  Local Ltac kxa_unpZ ::=
    lazymatch goal with
    | |- unpZ ?mm ?lo1 ?hi1 =>
        first [ kxa_hyp
              | let X := kxk_sbase7 DT NC SPV lo W BASE BITS lo1 in
                lazymatch goal with
                | U : unpoisoned mm X ?hi0 |- _ => apply (unpoisoned_unpZ mm X hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia]
                end
              | match goal with
                | U : unpoisoned mm ?lo0 ?hi0 |- _ => apply (unpoisoned_unpZ mm lo0 hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia]
                end
              | kxa_unp_hook ]
    end.
  Local Ltac kxl_rng ::=
    first [ kxl_hyp
          | lazymatch goal with
            | |- rng ?RG ?A ?N =>
                let X := kxk_sbase7 DT NC SPV lo W BASE BITS A in
                lazymatch goal with H : rng RG X ?N0 |- _ => apply (rng_sub' RG X N0 A N H); solve [kx_lia] end
            end
          | lazymatch goal with
            | |- rng ?RG ?A ?N => match goal with H : rng RG ?A0 ?N0 |- _ => apply (rng_sub' RG A0 N0 A N H); solve [kxl_lia_small] end
            end
          | kx_rng ].
  Local Ltac kxa_rng0 ::=
    kxa_norm;
    lazymatch goal with
    | |- rng ?RG (KXSHLO + ?A / 8) (shspanZ ?A ?n) =>
        first [ let X := kxk_sbase7 DT NC SPV lo W BASE BITS A in
                lazymatch goal with
                | H : rng RG (shad X) ?N0 |- _ =>
                    apply (shad_shspan_rng RG A n (shad X) N0 H);
                    [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
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
  Local Ltac bf_reunp :=
    repeat match goal with H : unpoisoned ?mx _ _ |- _ => lazymatch mx with m => fail | _ => clear H end end;
    lazymatch goal with
    | MU : munch _ m ?m2 |- _ =>
        pose proof (bf_unp_dtM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT m2 MU) as UDT1;
        pose proof (bf_unp_wM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UW m2 MU) as UW1;
        pose proof (bf_unp_ncM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UNC m2 MU) as UNC1;
        pose proof (bf_unp_baM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UBA m2 MU) as UBA1;
        pose proof (bf_unp_biM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UBI m2 MU) as UBI1
    end.
  (* [comment removed for export] *)
  Local Ltac bf_gc :=
    lazymatch goal with
    | CEL : u8arr _ _ (DT + 8) (map _ ?cb), SNX : u8arr _ _ W (u16s (map _ ?snl)), SPRD : u8arr _ _ (W + 106) (map _ ?spl) |- _ =>
      let cur := constr:((cb, snl, spl)) in
      repeat match goal with
      | H : zlen ?l = _ |- _ =>
          let l0 := lazymatch l with u16s (map _ ?c) => c | u32s (map _ ?c) => c | map _ ?c => c | _ => l end in
          first [ is_var l0; fail 1
                | lazymatch cur with context [l0] => fail | _ => idtac end;
                  lazymatch l0 with
                  | kind_base _ => fail | kind_bits _ => fail
                  | flat_map seqsym_bytes ?c => is_var c; fail
                  | _ => clear H
                  end ]
      end
    | |- _ => idtac
    end.
  (* [comment removed for export] *)
  Local Ltac bf_dropUL := repeat match goal with H : zlen (map (Z_to_bv 8) (Zupd _ _ _)) = _ |- _ => clear H end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Tactic Notation "bf_have" constr(T) "by" tactic3(tac) := first [ match goal with H : T |- _ => idtac end | assert T by tac ].
  Local Ltac bf_lens :=
    bf_gc;
    (* [comment removed for export] *)
    try match goal with C : zlen (set_cell _ _ ?c0) = _ |- _ =>
           first [ match goal with H : zlen c0 = _ |- _ => idtac end
                 | let n := fresh "CLENb" in pose proof C as n; rewrite !set_cell_length2 in n ] end;
    try match goal with C : zlen (set_base _ _ ?c0) = _ |- _ =>
           lazymatch c0 with
           | set_base _ _ _ => fail
           | _ => first [ match goal with H : zlen c0 = _ |- _ => idtac end
                        | let n := fresh "CLENb" in pose proof C as n; rewrite !set_base_length2 in n ] end end;
    try match goal with C : zlen (Zupd _ _ ?c0) = _ |- _ =>
           lazymatch c0 with
           | Zupd _ _ _ => fail
           | _ => first [ match goal with H : zlen c0 = _ |- _ => idtac end
                        | let n := fresh "SNLENb" in pose proof C as n; rewrite !Zupd_length2 in n ] end end;
    lazymatch goal with
    | CEL : u8arr _ _ (DT + 8) (map _ ?cb), SNX : u8arr _ _ W (u16s (map _ ?sn)), SPRD : u8arr _ _ (W + 106) (map _ ?sp) |- _ =>
        bf_have (zlen cb = 8 * 2^tl) by (rewrite ?Zupd_length2, sqb_len, ?set_base_length2, ?set_cell_length2; lia);
        bf_have (zlen (map (Z_to_bv 8) cb) = 8 * 2^tl) by (rewrite length_map, ?Zupd_length2, sqb_len, ?set_base_length2, ?set_cell_length2; lia);
        bf_have (zlen sn = 53) by (rewrite ?Zupd_length2; assumption);
        bf_have (zlen (u16s (map (Z_to_bv 64) sn)) = 106) by (rewrite u16s_length, length_map, ?Zupd_length2; lia);
        bf_have (zlen sp = wlen - 106) by (rewrite ?Zupd_length2, ?write8_length2, ?lay_step_length2, ?lay_k_length2, ?write8_length2, ?Zupd_length2; assumption);
        bf_have (zlen (map (Z_to_bv 8) sp) = wlen - 106)
          by (first [ rewrite length_map; assumption
                    | rewrite length_map, ?Zupd_length2, ?write8_length2, ?lay_step_length2, ?lay_k_length2, ?write8_length2, ?Zupd_length2; assumption ])
    end.
  Local Ltac bf_consts :=
    try match goal with H : zlen (kind_base k) = _ |- _ => clear H end; try match goal with H : zlen (kind_bits k) = _ |- _ => clear H end;
    pose proof (kind_lens k) as (LKB & LKBI);
    assert (LNC : zlen (u16s (map (Z_to_bv 64) norm)) = 2 * zlen norm) by (rewrite u16s_length, length_map; lia);
    assert (LBA4 : zlen (u32s (map (Z_to_bv 64) (kind_base k))) = 4 * (kind_max k + 1)) by (rewrite u32s_length, length_map; lia);
    assert (LBI1 : zlen (map (Z_to_bv 8) (kind_bits k)) = kind_max k + 1) by (rewrite length_map; lia);
    try match goal with H : 0 <= kind_max k <= 52 |- _ => clear H end; pose proof (kind_max_range k) as KM.
  Local Ltac bf_open I :=
    open_hy HY; open_bf I; unfold KHIGH in *; bf_reunp;
    pose proof (bf_bands _ _ _ _ _ _ _ _ _ _ _ _ _ HY) as (BDT & BW & BSP & B5 & B6 & B7 & B8);
    hide_all_disj;
    pose proof (bfA_size_rng _ _ _ _ _ _ _ _ _ _ _ _ _ HY) as (SZ & LLR & LL2);
    bf_consts; bf_lens.
  (* [comment removed for export] *)
  Local Ltac bf_reopen I :=
    repeat match goal with
           | H : rw_cells _ _ _ _ |- _ => clear H | H : u8arr _ _ _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H
           | H : stk _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H
           | H : wmono _ _ _ |- _ => clear H | H : Z.of_nat (length _) = _ |- _ => clear H | H : Forall _ _ |- _ => clear H
           | H : list byte |- _ => clear H
           end;
    open_bf I; bf_reunp; bf_consts; bf_lens.
  (* [comment removed for export] *)
  Notation KZB := [KZRange SPV (0x10007fff8000 + 176) (2^47); KZRange maxSV 0 52; KZRange tl 5 9; KZRange (2^tl) 32 512; KZRange (2^(tl - 1)) 16 256;
     KZRange NC 4096 (2^47); KZRange DT 4096 (2^47); KZRange W 4096 (2^47); KZRange BASE 4096 (2^47 - 212); KZRange BITS 4096 (2^47 - 53);
     KZRange wlen 626 (2^47); KZRange (zlen norm) 1 (2^46); KZRange (kind_max k) 0 52;
     KZRange (NC + 2 * zlen norm) 0 (2^47); KZRange (W + wlen) 0 (2^47 - 8); KZRange (DT + 8 + 8 * 2^tl) 0 (2^47 - 8);
     KZAlign DT 4; KZAlign W 2; KZAlign NC 2; KZAlign BASE 4] (only parsing).
  Notation POST t := (bfA_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W wlen tl lo m t).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -144)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).


  Notation STEP := (fse_tablestep (2^tl)).
  Notation KK := 72340172838076673.
  Notation SP0 := (W + 106).
  Variables (w16 w24 : word).
  Notation BFm' xh0 xh1 := (BFm xh0 xh1 (Z_to_bv 64 (2^tl / 8 + 3)) (Z_to_bv 64 (W + 121)) w16 w24) (only parsing).

  (* [comment removed for export] *)
  Notation STP pc mm j position xra xa0 xa1 xa2 xa5 xs5 xs6 xs7 xs8 xs9 xs10 xs11 :=
    (ST pc mm xra (Z_to_bv 64 (2^tl)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 (2 * STEP)) (Z_to_bv 64 (W + 107)) xa0 xa1 (Z_to_bv 64 STEP)
        (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) (Z_to_bv 64 tl) (Z_to_bv 64 W) (Z_to_bv 64 j) xa2 xa5 xs5 xs6
        (Z_to_bv 64 DT) xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (DT + 8)) (Z_to_bv 64 (2^tl + -1)) (Z_to_bv 64 SP0) (Z_to_bv 64 position)).
  (* [comment removed for export] *)
  Notation ST3J mm xra xs0 xs1 xa0 xa1 xa2 xa7 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (ST 0x884a0 mm xra (Z_to_bv 64 (2^tl)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (2^tl)) xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) (Z_to_bv 64 tl) (Z_to_bv 64 W) xa7
        xs2 xs3 xs4 xs5 (Z_to_bv 64 DT) xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).

  Lemma bf_step_rng2A : 19 <= STEP < 1048576.
  Proof. destruct (bfA_size_rng _ _ _ _ _ _ _ _ _ _ _ _ _ HY) as (SZ & _). unfold fse_tablestep. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma bf_place_bodyA : forall (t : seq_table) m1 h0 h1 cells sn sp j position xra xa0 xa1 xa2 xa5 xs5 xs6 xs7 xs8 xs9 xs10 xs11,
    BFm' h0 h1 cells sn sp m1 -> 0 <= j -> j + 2 <= 2^tl -> 0 <= position < 2^tl ->
    (forall m2 ya0 ya1 ya2 ya5,
       BFm' h0 h1 (set_base ((position + STEP) mod 2^tl) (Znth (j + 1) sp) (set_base (position mod 2^tl) (Znth j sp) cells)) sn sp m2 ->
       j + 2 < 2^tl ->
       evtF bsegs RNG (POST t) (STP 0x886e8 m2 (j + 2) ((position + 2 * STEP) mod 2^tl) xra ya0 ya1 ya2 ya5 xs5 xs6 xs7 xs8 xs9 xs10 xs11)) ->
    (forall m2 ys0 ys1 ya0 ya1 ya2 ya7 ys2 ys3 y31,
       BFm' h0 h1 (set_base ((position + STEP) mod 2^tl) (Znth (j + 1) sp) (set_base (position mod 2^tl) (Znth j sp) cells)) sn sp m2 ->
       j + 2 = 2^tl ->
       evtF bsegs RNG (POST t) (ST3J m2 xra ys0 ys1 ya0 ya1 ya2 ya7 ys2 ys3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (DT + 8)) (Z_to_bv 64 (2^tl + -1)) (Z_to_bv 64 SP0) y31)) ->
    evtF bsegs RNG (POST t) (STP 0x886e8 m1 j position xra xa0 xa1 xa2 xa5 xs5 xs6 xs7 xs8 xs9 xs10 xs11).
  Proof.
    intros until xs11; intros I HJ HJF HP KH KE; bf_open I.
    pose proof bf_step_rng2A as STEPR.
    assert (PR1 : 0 <= (position + STEP) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    assert (PR2 : 0 <= (position + 2 * STEP) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    remember ((position + STEP) mod 2^tl) as pos1 eqn:EPOS1. remember ((position + 2 * STEP) mod 2^tl) as pos2 eqn:EPOS2.
    (* [comment removed for export] *)
    assert (HP1 : hidden (pos1 = (position + STEP) mod 2^tl)) by exact EPOS1.
    assert (HP2 : hidden (pos2 = (position + 2 * STEP) mod 2^tl)) by exact EPOS2. clear EPOS1 EPOS2.
    assert (LAND : forall x, 0 <= x -> Z.land x (2^tl + -1) = x mod 2^tl)
      by (intros x Hx; replace (2^tl + -1) with (Z.ones tl) by (rewrite Z.ones_equiv; lia); apply Z.land_ones; lia).
    assert (SB0 : 0 <= Znth j sp < 256) by (apply (Forall_Znth _ sp j SPBY); lia).
    assert (SB1 : 0 <= Znth (j + 1) sp < 256) by (apply (Forall_Znth _ sp (j + 1) SPBY); lia).
    (* [comment removed for export] *)
    kx_autoFLAc (FR, HDR) [KAUnp (SP0 + j) 2] [0x88700] 12%nat
      (KZB ++ [KZRange j 0 511; KZRange (2^tl - j) 2 512; KZRange position 0 511; KZRange (SP0 + j) 4096 (2^47 - 16); KZRange (wlen - 108 - j) 0 (2^47)])
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem. all: kx_tidy_run.
    rewrite ?(Z.mod_small position (2^64)) by lia. rewrite ?(Z.mod_small (2^tl + -1) (2^64)) by lia. rewrite (LAND position) by lia.
    rewrite (Z.mod_small position (2^tl)) by lia.
    (* [comment removed for export] *)
    bf_lens.
    kx_autoFLAc (FR, HDR) [KAUnp (DT + 8 + 8 * position + 4) 4; KAApp (DT + 8 + 8 * position + 4) 4] [0x88724] 30%nat
      (KZB ++ [KZRange j 0 511; KZRange (2^tl - j) 2 512; KZRange position 0 511; KZRange (2^tl - position) 1 512; KZRange (8 * 2^tl - 8 * position) 8 4096;
               KZRange (SP0 + j) 4096 (2^47 - 16); KZRange (wlen - 108 - j) 0 (2^47); KZRange (DT + 8 + 8 * position + 4) 4096 (2^47 - 8);
               KZWr (DT + 8 + 8 * position + 4) 4; KZDisj (DT + 8 + 8 * position + 4) 4 NC (2 * zlen norm); KZDisj (DT + 8 + 8 * position + 4) 4 (SPV - 144) 144;
               KZDisj (DT + 8 + 8 * position + 4) 4 W 106; KZDisj (DT + 8 + 8 * position + 4) 4 SP0 (wlen - 106);
               KZDisj (DT + 8 + 8 * position + 4) 4 DT 8;
               KZDisj (DT + 8 + 8 * position + 4) 4 BASE (4 * (kind_max k + 1)); KZDisj (DT + 8 + 8 * position + 4) 4 BITS (kind_max k + 1)])
      [(SP0 + j, 2)] [(SP0 + j, 2); (DT + 8 + 8 * position + 4, 4)].
    all: try kx_z. all: try kx_acc RW. all: try kx_acc RDT.
    all: try (kx_side_pre; unfold hidden in BDT; Z.div_mod_to_equations; lia).
    kx_read_reg 18 RD.
    rewrite (rdval_u8Zb bsegs _ SP0 sp j _ SPRD) in RD; [| lia | lia | exact SPBY].
    kxk_keep CEL. kx_mem. rewrite RD in *. kx_tidy_run. bf_reunp.
    rewrite ?(unsigned_lit (Znth j sp)) in * by lia.
    erewrite (sqb_base4 cells position (Znth j sp)) in CEL by lia.
    try kx_gen_regsF [10%nat; 11%nat; 19%nat].
    (* [comment removed for export] *)
    bf_lens.
    kx_autoFLAc (FR, HDR) [KAUnp (SP0 + j) 2] [0x88740] 12%nat
      (KZB ++ [KZRange j 0 511; KZRange (2^tl - j) 2 512; KZRange position 0 511; KZRange STEP 19 1048575; KZRange (SP0 + j) 4096 (2^47 - 16); KZRange (wlen - 108 - j) 0 (2^47)])
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem. all: kx_tidy_run.
    match goal with |- context [Z.land ?a ?b] =>
      replace (Z.land a b) with pos1 by (unfold hidden in HP1; rewrite ?Z.mod_small by lia; rewrite LAND by lia; rewrite HP1; f_equal; lia) end.
    (* [comment removed for export] *)
    bf_lens.
    kx_autoFLAc (FR, HDR) [KAUnp (DT + 8 + 8 * pos1 + 4) 4; KAApp (DT + 8 + 8 * pos1 + 4) 4] [0x88764] 30%nat
      (KZB ++ [KZRange j 0 511; KZRange (2^tl - j) 2 512; KZRange pos1 0 511; KZRange (2^tl - pos1) 1 512; KZRange (8 * 2^tl - 8 * pos1) 8 4096;
               KZRange position 0 511;
               KZRange (SP0 + j) 4096 (2^47 - 16); KZRange (wlen - 108 - j) 0 (2^47); KZRange (DT + 8 + 8 * pos1 + 4) 4096 (2^47 - 8);
               KZWr (DT + 8 + 8 * pos1 + 4) 4; KZDisj (DT + 8 + 8 * pos1 + 4) 4 NC (2 * zlen norm); KZDisj (DT + 8 + 8 * pos1 + 4) 4 (SPV - 144) 144;
               KZDisj (DT + 8 + 8 * pos1 + 4) 4 W 106; KZDisj (DT + 8 + 8 * pos1 + 4) 4 SP0 (wlen - 106);
               KZDisj (DT + 8 + 8 * pos1 + 4) 4 DT 8;
               KZDisj (DT + 8 + 8 * pos1 + 4) 4 BASE (4 * (kind_max k + 1)); KZDisj (DT + 8 + 8 * pos1 + 4) 4 BITS (kind_max k + 1)])
      [(SP0 + j, 2)] [(SP0 + j, 2); (DT + 8 + 8 * pos1 + 4, 4)].
    all: try kx_z. all: try kx_acc RW. all: try kx_acc RDT.
    all: try (kx_side_pre; unfold hidden in BDT; Z.div_mod_to_equations; lia).
    kx_read_reg 18 RD1.
    rewrite (rdval_u8Zb bsegs _ SP0 sp (j + 1) _ SPRD) in RD1; [| lia | lia | exact SPBY].
    kxk_keep CEL. kx_mem. rewrite RD1 in *. kx_tidy_run. bf_reunp.
    rewrite ?(unsigned_lit (Znth (j + 1) sp)) in * by lia.
    erewrite (sqb_base4 (set_base position (Znth j sp) cells) pos1 (Znth (j + 1) sp)) in CEL by (rewrite ?set_base_length2; lia).
    try kx_gen_regsF [10%nat; 11%nat; 19%nat].
    (* [comment removed for export] *)
    bf_lens.
    kx_autoFLAc FR (@nil kza) [0x886e8; 0x884a0] 10%nat (KZB ++ [KZRange j 0 511; KZRange (2^tl - j) 2 512; KZRange position 0 511; KZRange STEP 19 1048575])
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z. all: try kx_acc RSTK. all: kx_mem. all: kx_tidy_run.
    all: match goal with |- context [Z.land ?a ?b] =>
           replace (Z.land a b) with pos2 by (unfold hidden in HP2; rewrite ?Z.mod_small by lia; rewrite LAND by lia; rewrite HP2; f_equal; lia) end.
    all: assert (CLEN2 : zlen (set_base pos1 (Znth (j + 1) sp) (set_base position (Znth j sp) cells)) = 2^tl) by (rewrite !set_base_length2; exact CLEN).
    all: replace (set_base position (Znth j sp) cells) with (set_base (position mod 2^tl) (Znth j sp) cells) in CEL, CLEN2
           by (rewrite Z.mod_small by lia; reflexivity).
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x886e8) _ _ _ _) =>
             eapply KH; [close_bf | lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x884a0) _ _ _ _) =>
             eapply KE; [close_bf | lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_place_loopA : forall (t : seq_table) (f : nat) m1 h0 h1 cells sn sp j position xra xa0 xa1 xa2 xa5 xs5 xs6 xs7 xs8 xs9 xs10 xs11,
    BFm' h0 h1 cells sn sp m1 -> 0 <= j -> j + 2 * Z.of_nat (S f) = 2^tl -> 0 <= position < 2^tl ->
    (forall m2 cells' p' ys0 ys1 ya0 ya1 ya2 ya7 ys2 ys3 y31,
       place_fast (S f) (2^tl) STEP sp j position cells = (cells', p') ->
       BFm' h0 h1 cells' sn sp m2 ->
       evtF bsegs RNG (POST t) (ST3J m2 xra ys0 ys1 ya0 ya1 ya2 ya7 ys2 ys3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (DT + 8)) (Z_to_bv 64 (2^tl + -1)) (Z_to_bv 64 SP0) y31)) ->
    evtF bsegs RNG (POST t) (STP 0x886e8 m1 j position xra xa0 xa1 xa2 xa5 xs5 xs6 xs7 xs8 xs9 xs10 xs11).
  Proof.
    intros t f. induction f as [|f IH]; intros until xs11; intros I HJ HJF HP KP3.
    - eapply bf_place_bodyA; [exact I | exact HJ | lia | exact HP | intros; exfalso; lia |].
      intros m2 ys0 ys1 ya0 ya1 ya2 ya7 ys2 ys3 y31 I2 _. eapply KP3; [| exact I2]. cbn [place_fast]. reflexivity.
    - eapply bf_place_bodyA; [exact I | exact HJ | lia | exact HP | |].
      + intros m2 ya0 ya1 ya2 ya5 I2 LT.
        eapply (IH m2 h0 h1 _ sn sp (j + 2) ((position + 2 * STEP) mod 2^tl)); [exact I2 | lia | lia | apply Z.mod_pos_bound; pose proof bf_step_rng2A; open_hy HY; lia |].
        intros m3 cells' p' zs0 zs1 za0 za1 za2 za7 zs2 zs3 z31 PF I3. eapply KP3; [| exact I3].
        cbn [place_fast]. exact PF.
      + intros; exfalso; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_fastA : forall (t : seq_table) m1 h0 h1 w0 w8 cells sn sp xra x5 xs0 xs1 xa0 xa1 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs10 xs11 x31,
    BFm h0 h1 w0 w8 w16 w24 cells sn sp m1 -> nsum norm (maxSV + 1) = 2^tl ->
    (forall m2 spread1 pos1 cells2 p2 yra ys0 ys1 ya0 ya1 ya2 ya7 ys2 ys3 ys4 ys5 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31,
       lay_symbols (Z.to_nat (maxSV + 1)) norm 0 0 sp = (spread1, pos1) ->
       place_fast (Z.to_nat (2^tl / 2)) (2^tl) STEP spread1 0 0 cells = (cells2, p2) ->
       BFm' h0 h1 cells2 sn spread1 m2 ->
       evtF bsegs RNG (POST t) (ST3J m2 yra ys0 ys1 ya0 ya1 ya2 ya7 ys2 ys3 ys4 ys5 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31)) ->
    evtF bsegs RNG (POST t)
      (ST 0x88264 m1 xra x5 (Z_to_bv 64 2147450880) (Z_to_bv 64 (2^tl)) xs0 xs1 xa0 xa1 (Z_to_bv 64 (2^tl / 8))
          (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) xa5 (Z_to_bv 64 W) xa7 xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 NC) (Z_to_bv 64 (maxSV + 1)) xs10 xs11 (Z_to_bv 64 (DT + 8)) (Z_to_bv 64 (2^tl + -1)) (Z_to_bv 64 SP0) x31).
  Proof.
    intros until x31; intros I HNL KP3. bf_open I.
    pose proof bf_step_rng2A as STEPR.
    (* [comment removed for export] *)
    kx_autoFLAc FR [KAApp (SPV - 144) 144] [0x882b0] 20%nat
      (KZB ++ [KZWr (SPV - 144) 144; KZDisj (SPV - 144) 144 NC (2 * zlen norm); KZDisj (SPV - 144) 144 (DT + 8) (8 * 2^tl);
               KZDisj (SPV - 144) 144 DT 8; KZDisj (SPV - 144) 144 W 106; KZDisj (SPV - 144) 144 SP0 (wlen - 106);
               KZDisj (SPV - 144) 144 BASE (4 * (kind_max k + 1)); KZDisj (SPV - 144) 144 BITS (kind_max k + 1)])
      [(SPV - 144, 144)] [(SPV - 144, 144)].
    all: try kx_z. all: try kx_acc RSTK. all: kx_mem. all: kx_tidy_run. all: bf_reunp.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (I1 : BFm' h0 h1 cells sn sp mx) by close_bf end.
    eapply (bf_lay_loopA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT UW UNC UBA UBI w16 w24 t (Z.to_nat maxSV) _ h0 h1 cells sn sp 0 0);
      [exact I1 | lia | lia | reflexivity | exact HNL |].
    intros m2 spread1 pos1 yra ys0 ys1 ya0 ya1 ya2 ya5 ya6 ya7 ys5 ys7 ys8 ys9 ys10 ys11 y31 LSY I2.
    replace (S (Z.to_nat maxSV)) with (Z.to_nat (maxSV + 1)) in LSY by lia.
    clear I1. bf_reopen I2.
    (* [comment removed for export] *)
    kx_autoFLAc FR (@nil kza) [0x886e8] 16%nat (KZB ++ [KZRange (2^tl / 8) 4 64; KZRange (2^tl / 2) 16 256])
      [(SPV - 144, 144)] [(SPV - 144, 144)].
    all: try kx_z. all: try kx_acc RSTK. all: kx_mem. all: kx_tidy_run.
    rewrite ?(Z.mod_small (2^tl) (2^64)) by lia. rewrite ?(Z.mod_small (2^tl) 4294967296) by lia.
    lazymatch goal with |- _ => let v := StepF.reg_val 12 in lazymatch v with Z_to_bv 64 ?e => replace e with STEP by (unfold fse_tablestep; lia) end end.
    lazymatch goal with |- _ => let v := StepF.reg_val 8 in lazymatch v with Z_to_bv 64 ?e => replace e with (2 * STEP) by (unfold fse_tablestep; lia) end end.
    eapply (bf_place_loopA t (Z.to_nat (2^tl / 2 - 1)) m2 h0 h1 cells sn spread1 0 0); [close_bf | lia | | lia |].
    { rewrite <- LL2, Z.div_mul by lia. lia. }
    intros m3 cells2 p2 zs0 zs1 za0 za1 za2 za7 zs2 zs3 z31 PF I3.
    replace (S (Z.to_nat (2^tl / 2 - 1))) with (Z.to_nat (2^tl / 2)) in PF by (assert (1 <= 2^tl / 2) by (Z.div_mod_to_equations; lia); lia).
    eapply KP3; [exact LSY | exact PF | exact I3].
  Qed.
End P2C.
End CANSEC1.
