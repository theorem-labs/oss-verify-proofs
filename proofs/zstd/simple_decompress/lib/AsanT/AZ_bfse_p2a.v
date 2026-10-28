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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_blk_iface AZ_kx AZ_bfse_defs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit AZ_bfse_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
Lemma sv_b0 : forall s, 0 <= s < 256 -> (72340172838076673 * s) mod 256 = s.
Proof. intros s Hs. pose proof (sv_byte s 0 Hs ltac:(lia)) as H. rewrite Z.shiftr_0_r, Z.mul_comm in H. exact H. Qed.
Lemma sv_bd : forall s j D, 0 <= s < 256 -> 0 <= j < 8 -> D = 2^(8 * j) -> ((72340172838076673 * s) mod 2^64 / D) mod 256 = s.
Proof.
  intros s j D Hs Hj ->. rewrite (Z.mod_small (72340172838076673 * s) (2^64)) by lia.
  rewrite <- (Z.shiftr_div_pow2 _ (8 * j)) by lia. rewrite Z.mul_comm. apply sv_byte; lia.
Qed.
(* [comment removed for export] *)
Lemma zupd8_wr8m : forall (sp : list Z) p s i0 i1 i2 i3 i4 i5 i6 i7,
  i0 = p + 4 -> i1 = p + 5 -> i2 = p + 6 -> i3 = p + 7 -> i4 = p -> i5 = p + 1 -> i6 = p + 2 -> i7 = p + 3 ->
  Zupd i7 s (Zupd i6 s (Zupd i5 s (Zupd i4 s (Zupd i3 s (Zupd i2 s (Zupd i1 s (Zupd i0 s sp))))))) = wr8m sp p s.
Proof. intros; subst; reflexivity. Qed.
(* [comment removed for export] *)
Ltac sv_vals s :=
  repeat match goal with
  | H : hidden (?x = (72340172838076673 * s) mod 256) |- _ => unfold hidden in H; rewrite (sv_b0 s) in H by lia; subst x
  | H : hidden (?x = ((72340172838076673 * s) mod 2^64 / ?D) mod 256) |- _ =>
      unfold hidden in H;
      let j := lazymatch D with
               | 256 => constr:(1) | 65536 => constr:(2) | 16777216 => constr:(3) | 4294967296 => constr:(4)
               | 1099511627776 => constr:(5) | 281474976710656 => constr:(6) | 72057594037927936 => constr:(7) end in
      rewrite (sv_bd s j D) in H by (first [reflexivity | lia]); subst x
  end.

(* [comment removed for export] *)
Definition lay_step (norm : list Z) (s pos : Z) (spread : list Z) : list Z :=
  lay_more (Z.to_nat (Znth s norm / 8 + 1)) (write8 spread pos s) pos s 8 (Znth s norm).
Lemma lay_symbols_S : forall f norm s pos spread,
  lay_symbols (S f) norm s pos spread = lay_symbols f norm (s + 1) (pos + Znth s norm) (lay_step norm s pos spread).
Proof. reflexivity. Qed.
Lemma lay_step_length : forall norm s pos spread, length (lay_step norm s pos spread) = length spread.
Proof. intros. unfold lay_step. rewrite lay_more_length. apply write8_length. Qed.
Lemma lay_step_length2 : forall norm s pos spread, Z.of_nat (length (lay_step norm s pos spread)) = Z.of_nat (length spread).
Proof. intros. rewrite lay_step_length. reflexivity. Qed.
Lemma lay_k_length2 : forall j l p s, Z.of_nat (length (lay_k j l p s)) = Z.of_nat (length l).
Proof. intros. rewrite lay_k_length. reflexivity. Qed.
Lemma write8_length2 : forall l p s, Z.of_nat (length (write8 l p s)) = Z.of_nat (length l).
Proof. intros. rewrite write8_length. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT}.
Section P2A.
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
  (* [comment removed for export] *)
  Variables (w16 w24 : word).
  Notation BFm' xh0 xh1 := (BFm xh0 xh1 (Z_to_bv 64 (2^tl / 8 + 3)) (Z_to_bv 64 (W + 121)) w16 w24) (only parsing).

  (* [comment removed for export] *)
  Notation STL pc mm s pos xra xs0 xs1 xa0 xa1 xa2 xa5 xa6 xa7 xs5 xs7 xs8 xs9 xs10 xs11 x31 :=
    (ST pc mm xra (Z_to_bv 64 s) (Z_to_bv 64 2147450880) (Z_to_bv 64 (2^tl)) xs0 xs1 xa0 xa1 xa2
        (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) xa5 xa6 xa7 (Z_to_bv 64 (s * KK)) (Z_to_bv 64 (W + 114)) (Z_to_bv 64 pos) xs5 (Z_to_bv 64 16843009)
        xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (DT + 8)) (Z_to_bv 64 (2^tl + -1)) (Z_to_bv 64 SP0) x31).
  Notation STLH pc mm s pos xra xs0 xs1 xa0 xa1 xa2 xa5 xa6 xa7 xs5 xs7 xs10 xs11 x31 :=
    (STL pc mm s pos xra xs0 xs1 xa0 xa1 xa2 xa5 xa6 xa7 xs5 xs7 (Z_to_bv 64 NC) (Z_to_bv 64 (maxSV + 1)) xs10 xs11 x31).
  Notation STLT pc mm s pos n xra xs0 xs1 xa0 xa1 xa2 xa7 xs5 xs8 xs9 xs10 xs11 x31 :=
    (STL pc mm s pos xra xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 NC) (Z_to_bv 64 (maxSV + 1)) xa7 xs5 (Z_to_bv 64 n) xs8 xs9 xs10 xs11 x31).
  (* [comment removed for export] *)
  Notation STLX pc mm pos xra xs0 xs1 xa0 xa1 xa2 xa5 xa6 xa7 xs5 xs7 xs8 xs9 xs10 xs11 x31 :=
    (STL pc mm (maxSV + 1) pos xra xs0 xs1 xa0 xa1 xa2 xa5 xa6 xa7 xs5 xs7 xs8 xs9 xs10 xs11 x31).
  (* [comment removed for export] *)
  Notation SVB s D := (Z_to_bv 64 ((KK * s) mod 2^64 / D)).
  (* [comment removed for export] *)
  Notation STLI pc mm s pos i xa1 xa2 :=
    (ST pc mm (SVB s 16777216) (Z_to_bv 64 s) (Z_to_bv 64 2147450880) (Z_to_bv 64 (2^tl)) (SVB s 65536) (Z_to_bv 64 (SP0 + pos + i))
        (Z_to_bv 64 (SP0 + pos + i)) xa1 xa2 (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) (Z_to_bv 64 NC) (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 (SP0 + pos + i + 7))
        (Z_to_bv 64 (s * KK)) (Z_to_bv 64 (W + 114)) (Z_to_bv 64 pos) (SVB s 256) (Z_to_bv 64 16843009) (Z_to_bv 64 (Znth s norm))
        (SVB s 72057594037927936) (SVB s 281474976710656) (SVB s 1099511627776) (SVB s 4294967296) (Z_to_bv 64 (DT + 8)) (Z_to_bv 64 (2^tl + -1)) (Z_to_bv 64 SP0) (Z_to_bv 64 i)).

  (* [comment removed for export] *)
  Lemma bf_nolowA : nsum norm (maxSV + 1) = 2^tl -> forall i, 0 <= i <= maxSV -> 0 <= Znth i norm <= 2^tl.
  Proof.
    intros HNL i Hi. open_hy HY. destruct (bfA_size_rng _ _ _ _ _ _ _ _ _ _ _ _ _ HY) as (SZ & _).
    pose proof (low_step norm maxSV tl TLR NLEN NGE i Hi) as LS.
    pose proof (low_mono norm maxSV tl TLR NLEN NGE 0 i ltac:(lia) ltac:(lia)) as L0.
    pose proof (low_mono norm maxSV tl TLR NLEN NGE (i + 1) (maxSV + 1) ltac:(lia) ltac:(lia)) as L1.
    change (FseReadSound.pws norm 0) with 0 in L0. change (nsum norm 0) with 0 in L0.
    rewrite NSUM, HNL in L1.
    pose proof (nsum_S norm tl TLR i ltac:(unfold FseNCount.Zlength in *; lia)) as NS.
    pose proof (nsum_mono norm maxSV tl TLR NLEN (i + 1) (maxSV + 1) ltac:(lia) ltac:(lia)) as NM.
    pose proof (nsum_nonneg norm maxSV tl TLR NLEN i ltac:(lia)) as NN.
    pose proof (NGE i Hi). destruct (Z.eqb_spec (Znth i norm) (-1)); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_lay_inner_bodyA : forall (t : seq_table) m1 h0 h1 cells sn sp s pos i xa1 xa2,
    BFm' h0 h1 cells sn sp m1 -> 0 <= s <= maxSV -> 0 <= pos -> 8 <= i -> i < Znth s norm -> pos + Znth s norm <= 2^tl ->
    (forall m2 ya1 ya2, BFm' h0 h1 cells sn (write8 sp (pos + i) s) m2 -> i + 8 < Znth s norm ->
       evtF bsegs RNG (POST t) (STLI 0x88354 m2 s pos (i + 8) ya1 ya2)) ->
    (forall m2 yra ys0 ys1 ya0 ya1 ya2 ya7 ys5 ys8 ys9 ys10 ys11 y31, BFm' h0 h1 cells sn (write8 sp (pos + i) s) m2 -> Znth s norm <= i + 8 ->
       evtF bsegs RNG (POST t) (STLT 0x88290 m2 s pos (Znth s norm) yra ys0 ys1 ya0 ya1 ya2 ya7 ys5 ys8 ys9 ys10 ys11 y31)) ->
    evtF bsegs RNG (POST t) (STLI 0x88354 m1 s pos i xa1 xa2).
  Proof.
    intros until xa2; intros I HS HP HI8 HIN HPN KH KT; bf_open I.
    set (p := pos + i) in *.
    replace (SP0 + pos + i) with (SP0 + p) by lia. replace (SP0 + pos + i + 7) with (SP0 + p + 7) by lia.
    kx_autoFLAc (FR, HDR) [KAUnp (SP0 + p) 8; KAApp (SP0 + p) 8] [0x88354; 0x88290] 40%nat
      (KZB ++ [KZRange s 0 52; KZRange p 8 520; KZRange i 8 512; KZRange (Znth s norm - i) 1 512; KZRange (Znth s norm) 9 512;
               KZRange (SP0 + p) 4096 (2^47 - 16); KZRange (wlen - 114 - p) 0 (2^47); KZRange (KK * s) 0 (2^64 - 1);
               KZWr (SP0 + p) 8; KZDisj (SP0 + p) 8 NC (2 * zlen norm); KZDisj (SP0 + p) 8 (SPV - 144) 144;
               KZDisj (SP0 + p) 8 (DT + 8) (8 * 2^tl); KZDisj (SP0 + p) 8 DT 8; KZDisj (SP0 + p) 8 W 106;
               KZDisj (SP0 + p) 8 BASE (4 * (kind_max k + 1)); KZDisj (SP0 + p) 8 BITS (kind_max k + 1)])
      (@nil (Z * Z)) [(SP0 + p, 8)].
    all: try kx_z. all: try kx_acc RW.
    all: kxk_keepg SPRD. all: kx_mem. all: kx_tidy_run. all: bf_reunp.
    all: sv_vals s.
    all: erewrite (zupd8_wr8m sp p s) in * by lia.
    all: rewrite (wr8m_eq sp p s) in * by (unfold FseNCount.Zlength; lia).
    all: assert (SPBY' : Forall isbyte (write8 sp p s)) by (apply write8_bytes; [lia| exact SPBY]).
    all: bf_lens.
    all: try kx_gen_regsF [11%nat; 12%nat].
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x88354) _ _ _ _) =>
             kx_setreg 10 (SP0 + pos + (i + 8)); kx_setreg 17 (SP0 + pos + (i + 8) + 7); kx_setreg 9 (SP0 + pos + (i + 8)); kx_setreg 31 (i + 8);
             eapply KH; [close_bf | lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x88290) _ _ _ _) =>
             eapply KT; [close_bf | lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_lay_innerA : forall (t : seq_table) (f : nat) m1 h0 h1 cells sn sp s pos i xa1 xa2,
    BFm' h0 h1 cells sn sp m1 -> 0 <= s <= maxSV -> 0 <= pos -> 8 <= i ->
    i + 8 * Z.of_nat f < Znth s norm -> Znth s norm <= i + 8 * Z.of_nat (S f) -> pos + Znth s norm <= 2^tl ->
    (forall m2 yra ys0 ys1 ya0 ya1 ya2 ya7 ys5 ys8 ys9 ys10 ys11 y31, BFm' h0 h1 cells sn (lay_k (S f) sp (pos + i) s) m2 ->
       evtF bsegs RNG (POST t) (STLT 0x88290 m2 s pos (Znth s norm) yra ys0 ys1 ya0 ya1 ya2 ya7 ys5 ys8 ys9 ys10 ys11 y31)) ->
    evtF bsegs RNG (POST t) (STLI 0x88354 m1 s pos i xa1 xa2).
  Proof.
    intros t f. induction f as [|f IH]; intros until xa2; intros I HS HP HI8 HF1 HF2 HPN KT.
    - eapply bf_lay_inner_bodyA; [exact I | exact HS | exact HP | exact HI8 | lia | exact HPN | |].
      + intros; exfalso; lia.
      + intros m2 yra ys0 ys1 ya0 ya1 ya2 ya7 ys5 ys8 ys9 ys10 ys11 y31 I2 _. eapply KT. cbn [lay_k]. exact I2.
    - eapply bf_lay_inner_bodyA; [exact I | exact HS | exact HP | exact HI8 | lia | exact HPN | |].
      + intros m2 ya1 ya2 I2 LT.
        eapply (IH m2 h0 h1 cells sn (write8 sp (pos + i) s) s pos (i + 8)); [exact I2 | exact HS | exact HP | lia | lia | lia | exact HPN |].
        intros m3 yra ys0 ys1 ya0 ya1' ya2' ya7 ys5 ys8 ys9 ys10 ys11 y31 I3. eapply KT.
        replace (pos + (i + 8)) with (pos + i + 8) in I3 by lia. cbn [lay_k] in *. exact I3.
      + intros; exfalso; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_lay_bodyA : forall (t : seq_table) m1 h0 h1 cells sn sp s pos xra xs0 xs1 xa0 xa1 xa2 xa5 xa6 xa7 xs5 xs7 xs10 xs11 x31,
    BFm' h0 h1 cells sn sp m1 -> 0 <= s <= maxSV -> 0 <= pos -> 0 <= Znth s norm -> pos + Znth s norm <= 2^tl ->
    (forall m2 yra ys0 ys1 ya0 ya1 ya2 ya7 ys5 ys8 ys9 ys10 ys11 y31, BFm' h0 h1 cells sn (lay_step norm s pos sp) m2 ->
       evtF bsegs RNG (POST t) (STLT 0x88290 m2 s pos (Znth s norm) yra ys0 ys1 ya0 ya1 ya2 ya7 ys5 ys8 ys9 ys10 ys11 y31)) ->
    evtF bsegs RNG (POST t) (STLH 0x882b0 m1 s pos xra xs0 xs1 xa0 xa1 xa2 xa5 xa6 xa7 xs5 xs7 xs10 xs11 x31).
  Proof.
    intros until x31; intros I HS HP HN HPN KT; bf_open I.
    set (n := Znth s norm) in *.
    kx_autoFLAc (FR, HDR) [KAUnp (NC + 2 * s) 2; KAUnp (SP0 + pos) 8; KAApp (SP0 + pos) 8] [0x88290; 0x88354] 60%nat
      (KZB ++ [KZRange s 0 52; KZRange (maxSV - s) 0 52; KZRange (NC + 2 * s) 4096 (2^47 - 2); KZRange (2 * zlen norm - 2 * s) 2 (2^47);
               KZRange pos 0 512; KZRange (2^tl - pos) 0 512;
               KZRange (SP0 + pos) 4096 (2^47 - 16); KZRange (wlen - 114 - pos) 0 (2^47); KZRange (KK * s) 0 (2^64 - 1);
               KZWr (SP0 + pos) 8; KZDisj (SP0 + pos) 8 NC (2 * zlen norm); KZDisj (SP0 + pos) 8 (SPV - 144) 144;
               KZDisj (SP0 + pos) 8 (DT + 8) (8 * 2^tl); KZDisj (SP0 + pos) 8 DT 8; KZDisj (SP0 + pos) 8 W 106;
               KZDisj (SP0 + pos) 8 BASE (4 * (kind_max k + 1)); KZDisj (SP0 + pos) 8 BITS (kind_max k + 1)])
      [(NC + 2 * s, 2)] [(NC + 2 * s, 2); (SP0 + pos, 8)].
    all: try kx_z. all: try kx_acc RNC. all: try kx_acc RW. all: try kx_acc RSTK.
    all: kx_read_reg 23 RD; rewrite (rdval_s16Z bsegs m1 NC norm s) in RD by first [exact NCB | lia].
    all: kxk_keepg SPRD. all: kx_mem. all: rewrite RD in *. all: kx_tidy_run. all: bf_reunp.
    all: fold n.
    all: rewrite ?(unsigned_lit (Znth s norm)) in * by lia. all: rewrite ?(signed_lit (Znth s norm)) in * by lia. all: fold n in KXBR.
    all: sv_vals s.
    all: erewrite (zupd8_wr8m sp pos s) in * by lia.
    all: rewrite (wr8m_eq sp pos s) in * by (unfold FseNCount.Zlength; lia).
    all: assert (SPBY' : Forall isbyte (write8 sp pos s)) by (apply write8_bytes; [lia| exact SPBY]).
    all: bf_lens.
    all: try kx_gen_regsF [11%nat; 12%nat].
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x88290) _ _ _ _) =>     (* [comment removed for export] *)
             assert (LS : lay_step norm s pos sp = write8 sp pos s)
               by (unfold lay_step; fold n; rewrite (lay_more_k 0 _ (write8 sp pos s) pos s 8 n) by lia; reflexivity);
             eapply KT; rewrite LS; close_bf
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x88354) _ _ _ _) =>     (* [comment removed for export] *)
             kx_setreg 10 (SP0 + pos + 8); kx_setreg 17 (SP0 + pos + 8 + 7); kx_setreg 9 (SP0 + pos + 8);
             assert (LS : lay_step norm s pos sp = lay_k (S (Z.to_nat ((n - 9) / 8))) (write8 sp pos s) (pos + 8) s)
               by (unfold lay_step; fold n;
                   assert (Z.of_nat (Z.to_nat ((n - 9) / 8)) = (n - 9) / 8) by (rewrite Z2Nat.id; [reflexivity| apply Z.div_pos; lia]);
                   apply lay_more_k; [ | | right ]; Z.div_mod_to_equations; lia);
             (* [comment removed for export] *)
             eapply (bf_lay_innerA t (Z.to_nat ((n - 9) / 8)) _ h0 h1 cells sn (write8 sp pos s) s pos 8);
             [close_bf | exact HS | exact HP | lia | clear - KXBR HN HPN SZ; Z.div_mod_to_equations; lia
             | clear - KXBR HN HPN SZ; Z.div_mod_to_equations; lia | exact HPN
             | intros; eapply KT; rewrite LS; eassumption]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_lay_loopA : forall (t : seq_table) (f : nat) m1 h0 h1 cells sn sp s pos xra xs0 xs1 xa0 xa1 xa2 xa5 xa6 xa7 xs5 xs7 xs10 xs11 x31,
    BFm' h0 h1 cells sn sp m1 -> 0 <= s -> s + Z.of_nat (S f) = maxSV + 1 -> pos = nsum norm s -> nsum norm (maxSV + 1) = 2^tl ->
    (forall m2 spread' pos' yra ys0 ys1 ya0 ya1 ya2 ya5 ya6 ya7 ys5 ys7 ys8 ys9 ys10 ys11 y31,
       lay_symbols (S f) norm s pos sp = (spread', pos') -> BFm' h0 h1 cells sn spread' m2 ->
       evtF bsegs RNG (POST t) (STLX 0x886b8 m2 pos' yra ys0 ys1 ya0 ya1 ya2 ya5 ya6 ya7 ys5 ys7 ys8 ys9 ys10 ys11 y31)) ->
    evtF bsegs RNG (POST t) (STLH 0x882b0 m1 s pos xra xs0 xs1 xa0 xa1 xa2 xa5 xa6 xa7 xs5 xs7 xs10 xs11 x31).
  Proof.
    intros t f. induction f as [|f IH]; intros until x31; intros I HS HSF HPOS HNL KE.
    all: assert (HF : 0 <= Znth s norm /\ 0 <= pos /\ pos + Znth s norm <= 2^tl /\ pos + Znth s norm = nsum norm (s + 1))
      by (pose proof (bf_nolowA HNL s ltac:(lia)) as HN; open_hy HY;
          pose proof (nsum_S norm tl TLR s ltac:(unfold FseNCount.Zlength in *; lia)) as NS;
          pose proof (nsum_mono norm maxSV tl TLR NLEN (s + 1) (maxSV + 1) ltac:(lia) ltac:(lia)) as NM;
          pose proof (nsum_nonneg norm maxSV tl TLR NLEN s ltac:(lia)) as NN; lia).
    all: destruct HF as (HN0 & HP0 & HPN & HPS).
    all: eapply bf_lay_bodyA; [exact I | lia | exact HP0 | exact HN0 | exact HPN |]; intros m2 yra ys0 ys1 ya0 ya1 ya2 ya7 ys5 ys8 ys9 ys10 ys11 y31 I2.
    all: clear I; pose proof I2 as I3; bf_open I2.
    all: kx_autoFLAc FR (@nil kza) [0x882b0; 0x886b8] 12%nat
           (KZB ++ [KZRange s 0 52; KZRange (maxSV - s) 0 52; KZRange pos 0 512; KZRange (Znth s norm) 0 512; KZRange (KK * s) 0 (2^64 - 1)])
           (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z. all: try kx_acc RSTK. all: kx_mem. all: kx_tidy_run.
    all: try (exfalso; lia).
    - kx_setreg 5 (maxSV + 1). kx_setreg 18 ((maxSV + 1) * KK). kx_setreg 20 (pos + Znth s norm).
      eapply KE; [| exact I3]. rewrite lay_symbols_S. reflexivity.
    - kx_setreg 5 (s + 1). kx_setreg 18 ((s + 1) * KK). kx_setreg 20 (pos + Znth s norm).
      eapply (IH m2 h0 h1 cells sn (lay_step norm s pos sp) (s + 1) (pos + Znth s norm)); [exact I3 | lia | lia | lia | exact HNL |].
      intros m3 spread' pos' zra zs0 zs1 za0 za1 za2 za5 za6 za7 zs5 zs7 zs8 zs9 zs10 zs11 z31 LSY I4. eapply KE; [| exact I4].
      rewrite lay_symbols_S. exact LSY.
  Qed.
End P2A.
End CANSEC1.
