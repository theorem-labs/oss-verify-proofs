(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdSeqBuildWU ZdSeqBuildW3 SepHide.
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

Section CANSEC1. Context {rc : runConstT}.
Section P2.
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
  Local Ltac bf_lens :=
    bf_gc;
    (* [comment removed for export] *)
    try match goal with C : zlen (set_cell _ _ ?c0) = _ |- _ =>
           first [ match goal with H : zlen c0 = _ |- _ => idtac end
                 | let n := fresh "CLENb" in pose proof C as n; rewrite !set_cell_length2 in n ] end;
    try match goal with C : zlen (Zupd _ _ ?c0) = _ |- _ =>
           lazymatch c0 with
           | Zupd _ _ _ => fail
           | _ => first [ match goal with H : zlen c0 = _ |- _ => idtac end
                        | let n := fresh "SNLENb" in pose proof C as n; rewrite !Zupd_length2 in n ] end end;
    lazymatch goal with
    | CEL : u8arr _ _ (DT + 8) (map _ ?cb), SNX : u8arr _ _ W (u16s (map _ ?sn)), SPRD : u8arr _ _ (W + 106) (map _ ?sp) |- _ =>
        first [ assert (zlen cb = 8 * 2^tl) by assumption
              | assert (zlen cb = 8 * 2^tl) by (rewrite ?Zupd_length2, sqb_len, ?set_base_length2, ?set_cell_length2; lia) ];
        first [ assert (zlen (map (Z_to_bv 8) cb) = 8 * 2^tl) by assumption
              | assert (zlen (map (Z_to_bv 8) cb) = 8 * 2^tl) by (rewrite length_map, ?Zupd_length2, sqb_len, ?set_base_length2, ?set_cell_length2; lia) ];
        first [ assert (zlen sn = 53) by assumption | assert (zlen sn = 53) by (rewrite ?Zupd_length2; assumption) ];
        first [ assert (zlen (u16s (map (Z_to_bv 64) sn)) = 106) by assumption
              | assert (zlen (u16s (map (Z_to_bv 64) sn)) = 106) by (rewrite u16s_length, length_map, ?Zupd_length2; lia) ];
        first [ assert (zlen sp = wlen - 106) by assumption
              | assert (zlen sp = wlen - 106) by (rewrite ?Zupd_length2, ?write8_length, ?Zupd_length2; assumption) ];
        first [ assert (zlen (map (Z_to_bv 8) sp) = wlen - 106) by assumption
              | assert (zlen (map (Z_to_bv 8) sp) = wlen - 106) by (rewrite length_map, ?Zupd_length2, ?write8_length, ?Zupd_length2; assumption) ]
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
  (* [comment removed for export] *)
  Notation STC pc mm high xpos xa0 xa5 xi xa2 xs5 x28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29 :=
    (ST pc mm xra xpos (Z_to_bv 64 2147450880) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 high) xi
        x28 x29 xa2 (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) (Z_to_bv 64 tl) (Z_to_bv 64 W) xa5
        xs5 xs6 xs7 xs8 (Z_to_bv 64 DT) xs9 (Z_to_bv 64 NC) (Z_to_bv 64 (maxSV + 1)) xs10 xs11
        (Z_to_bv 64 (DT + 8)) (Z_to_bv 64 (2^tl + -1)) (Z_to_bv 64 STEP) xa0).

  Lemma bf_step_rngA : 0 <= STEP < 1048576.
  Proof. destruct (bfA_size_rng _ _ _ _ _ _ _ _ _ _ _ _ _ HY) as (SZ & _). unfold fse_tablestep. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma bf_skipA : forall (t : seq_table) (fu : nat) m1 high p xa0 xa5 xi xa2 xs5 x28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29,
    0 <= high < 2^tl -> 0 <= p < 2^tl ->
    skip_low fu (2^tl) STEP high ((p + STEP) mod 2^tl) <= high ->
    (forall y28, evtF bsegs RNG (POST t)
       (STC 0x88468 m1 high (Z_to_bv 64 (skip_low fu (2^tl) STEP high ((p + STEP) mod 2^tl))) xa0 xa5 xi xa2 xs5 y28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29)) ->
    evtF bsegs RNG (POST t) (STC 0x8845c m1 high (Z_to_bv 64 p) xa0 xa5 xi xa2 xs5 x28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29).
  Proof.
    intros t fu. induction fu as [|fu IH]; intros until x29; intros HH HP SK KONT.
    all: pose proof bf_step_rngA as HST; open_hy HY; destruct (bfA_size_rng _ _ _ _ _ _ _ _ _ _ _ _ _ HY) as (SZ & LLR & LL2).
    all: assert (QR : 0 <= (p + STEP) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    all: zstep; rewrite (FseWalkKit.swrap32_small (STEP + p)) by lia; zstep;
         replace (2^tl + -1) with (Z.ones tl) by (rewrite Z.ones_equiv; lia); rewrite (Z.land_ones (STEP + p) tl) by lia;
         replace (STEP + p) with (p + STEP) by lia;
         replace (Z.ones tl) with (2^tl + -1) by (rewrite Z.ones_equiv; lia).
    all: zstep; if_cases K; zify_cond K.
    - exfalso. cbn [skip_low] in SK. lia.
    - cbn [skip_low] in SK, KONT. apply KONT.
    - cbn [skip_low] in SK, KONT. destruct (Z.ltb_spec high ((p + STEP) mod 2^tl)); [|lia].
      eapply (IH m1 high ((p + STEP) mod 2^tl)); [exact HH | exact QR | exact SK | exact KONT].
    - cbn [skip_low] in SK, KONT. destruct (Z.ltb_spec high ((p + STEP) mod 2^tl)); [lia|]. apply KONT.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_slow_nextA : forall (t : seq_table) m1 high s xpos xa0 xi xa2 xs5 x28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29,
    0 <= s <= maxSV ->
    (s + 1 < maxSV + 1 -> evtF bsegs RNG (POST t) (STC 0x88414 m1 high xpos xa0 (Z_to_bv 64 (s + 1)) xi xa2 xs5 x28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29)) ->
    (s + 1 = maxSV + 1 -> forall y28, evtF bsegs RNG (POST t)
         (STC 0x884a0 m1 high (Z_to_bv 64 (2^tl)) xa0 (Z_to_bv 64 (maxSV + 1)) xi xa2 xs5 y28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29)) ->
    evtF bsegs RNG (POST t) (STC 0x8840c m1 high xpos xa0 (Z_to_bv 64 s) xi xa2 xs5 x28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29).
  Proof.
    intros until x29; intros HS KH KE. open_hy HY.
    destruct (bfA_size_rng _ _ _ _ _ _ _ _ _ _ _ _ _ HY) as (SZ & _).
    zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (s + 1) with (maxSV + 1) by lia. zstep. zstep. rewrite (Z.mod_small (2^tl)) by lia. eapply KE. lia.
    - apply KH. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_place_nA : forall (t : seq_table) (kk : nat) m1 h0 h1 w0 w8 w16 w24 cells sn sp high s i n position
                             xa2 xs5 x28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29,
    BFm h0 h1 w0 w8 w16 w24 cells sn sp m1 ->
    0 <= s <= maxSV -> 0 <= i -> i + Z.of_nat (S kk) = n -> n <= 2^tl -> 0 <= position < 2^tl -> 0 <= high < 2^tl ->
    (forall m2 cells' position' ya2 ys5 y28,
       place_n (S kk) (2^tl) STEP high s position cells = (cells', position') ->
       BFm h0 h1 w0 w8 w16 w24 cells' sn sp m2 -> 0 <= position' < 2^tl ->
       evtF bsegs RNG (POST t)
         (STC 0x88470 m2 high (Z_to_bv 64 position') (Z_to_bv 64 n) (Z_to_bv 64 s) (Z_to_bv 64 n) ya2 ys5 y28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29)) ->
    evtF bsegs RNG (POST t)
      (STC 0x88438 m1 high (Z_to_bv 64 position) (Z_to_bv 64 n) (Z_to_bv 64 s) (Z_to_bv 64 i) xa2 xs5 x28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29).
  Proof.
    intros t kk. induction kk as [|kk IH]; intros until x29; intros I HS HI HIN HN HP HH KONT; bf_open I.
    all: pose proof bf_step_rngA as HST.
    (* [comment removed for export] *)
    all: kx_autoFLAc (FR, HDR) [KAUnp (DT + 8 + 8 * position + 4) 4; KAApp (DT + 8 + 8 * position + 4) 4] [0x8845c] 20%nat
           (KZB ++ [KZRange position 0 511; KZRange (2^tl - position) 1 512; KZRange s 0 52; KZRange i 0 512; KZRange n 0 512;
                    KZRange (DT + 8 + 8 * position + 4) 4096 (2^47 - 8); KZRange (8 * 2^tl - 8 * position) 8 4096;
                    KZWr (DT + 8 + 8 * position + 4) 4; KZDisj (DT + 8 + 8 * position + 4) 4 NC (2 * zlen norm);
                    KZDisj (DT + 8 + 8 * position + 4) 4 (SPV - 144) 144; KZDisj (DT + 8 + 8 * position + 4) 4 W 106;
                    KZDisj (DT + 8 + 8 * position + 4) 4 (W + 106) (wlen - 106); KZDisj (DT + 8 + 8 * position + 4) 4 DT 8;
                    KZDisj (DT + 8 + 8 * position + 4) 4 BASE (4 * (kind_max k + 1)); KZDisj (DT + 8 + 8 * position + 4) 4 BITS (kind_max k + 1)])
           (@nil (Z * Z)) [(DT + 8 + 8 * position + 4, 4)].
    all: try kx_z. all: try kx_acc RDT.
    all: try (kx_side_pre; unfold hidden in BDT; Z.div_mod_to_equations; lia).
    all: kxk_keep CEL. all: kx_mem. all: kx_tidy_run. all: bf_reunp.
    all: try kx_gen_regsF [10%nat; 18%nat].
    all: erewrite (sqb_base4 cells position s) in CEL by lia.
    all: assert (CLEN' : zlen (set_base position s cells) = 2^tl) by (rewrite set_base_length2; exact CLEN).
    all: bf_lens.
    (* [comment removed for export] *)
    all: assert (QR : 0 <= (position + STEP) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    all: pose proof (skip_low_term tl high ((position + STEP) mod 2^tl) TLR ltac:(lia) QR) as SKT.
    all: eapply (bf_skipA t (Z.to_nat (2^tl)) _ high position); [lia | exact HP | exact SKT |]; intros y28.
    all: fold (next_pos (2^tl) STEP high position).
    all: assert (NPR : 0 <= next_pos (2^tl) STEP high position < 2^tl).
    all: try (unfold next_pos; split; [|lia];
              assert (SLN : forall f q, 0 <= q -> 0 <= skip_low f (2^tl) STEP high q)
                by (induction f as [|f IHf]; intros q Hq; cbn [skip_low]; [exact Hq| destruct (high <? q); [apply IHf; apply Z.mod_pos_bound; lia | exact Hq]]);
              apply SLN; lia).
    all: zstep; rewrite (FseWalkKit.swrap32_small (i + 1)) by lia; zstep; if_cases K; zify_cond K.
    - exfalso; lia.
    - replace (i + 1) with n by lia.
      eapply KONT; [cbn [place_n]; reflexivity | close_bf | exact NPR].
    - eapply (IH _ h0 h1 w0 w8 w16 w24 (set_base position s cells) sn sp high s (i + 1) n (next_pos (2^tl) STEP high position));
        [close_bf | exact HS | lia | lia | exact HN | exact NPR | exact HH |].
      intros m2 cells' position' ya2' ys5' y28' PN I2 HP2. eapply KONT; [| exact I2 | exact HP2].
      cbn [place_n]. exact PN.
    - exfalso; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_slow_bodyA : forall (t : seq_table) m1 h0 h1 w0 w8 w16 w24 cells sn sp high s position xa0 xi xa2 xs5 x28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29,
    BFm h0 h1 w0 w8 w16 w24 cells sn sp m1 -> 0 <= s <= maxSV -> 0 <= position < 2^tl -> high + 1 = nsum norm (maxSV + 1) ->
    (forall m2 cells' p' ya0 yi ya2 ys5 y28,
       place_n (Z.to_nat (Znth s norm)) (2^tl) STEP high s position cells = (cells', p') ->
       s + 1 < maxSV + 1 -> BFm h0 h1 w0 w8 w16 w24 cells' sn sp m2 -> 0 <= p' < 2^tl ->
       evtF bsegs RNG (POST t) (STC 0x88414 m2 high (Z_to_bv 64 p') ya0 (Z_to_bv 64 (s + 1)) yi ya2 ys5 y28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29)) ->
    (forall m2 cells' p' ya0 ya5 yi ya2 ys5 y28,
       place_n (Z.to_nat (Znth s norm)) (2^tl) STEP high s position cells = (cells', p') ->
       s + 1 = maxSV + 1 -> BFm h0 h1 w0 w8 w16 w24 cells' sn sp m2 -> 0 <= p' < 2^tl ->
       evtF bsegs RNG (POST t) (STC 0x884a0 m2 high (Z_to_bv 64 (2^tl)) ya0 ya5 yi ya2 ys5 y28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29)) ->
    evtF bsegs RNG (POST t) (STC 0x88414 m1 high (Z_to_bv 64 position) xa0 (Z_to_bv 64 s) xi xa2 xs5 x28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29).
  Proof.
    intros until x29; intros I HS HP HHN KN KE. bf_open I.
    pose proof bf_step_rngA as HST.
    assert (NR : -1 <= Znth s norm <= 2^tl).
    { pose proof (NGE s ltac:(lia)). pose proof (count_le_size norm maxSV tl TLR NLEN NGE NSUM s ltac:(lia)) as CL.
      unfold weight in CL. destruct (Z.eqb_spec (Znth s norm) (-1)); lia. }
    (* [comment removed for export] *)
    assert (HHI : high < 2^tl).
    { pose proof (low_mono norm maxSV tl TLR NLEN NGE 0 (maxSV + 1) ltac:(lia) ltac:(lia)) as LM.
      change (pws norm 0) with 0 in LM. change (nsum norm 0) with 0 in LM. rewrite NSUM in LM. lia. }
    (* [comment removed for export] *)
    kx_autoFLAc (FR, HDR) [KAUnp (NC + 2 * s) 2] [0x88434; 0x8840c] 20%nat
      (KZB ++ [KZRange s 0 52; KZRange (maxSV - s) 0 52; KZRange (NC + 2 * s) 4096 (2^47 - 2); KZRange (2 * zlen norm - 2 * s) 2 (2^47)])
      [(NC + 2 * s, 2)] (@nil (Z * Z)).
    all: try kx_z. all: try kx_acc RNC.
    all: kx_read_reg 31 RD; rewrite (rdval_s16Z bsegs m1 NC norm s) in RD by first [exact NCB | lia]; rewrite RD in *.
    all: kx_mem. all: kx_tidy_run. all: bf_reunp.
    all: try kx_gen_regsF [10%nat].
    - (* [comment removed for export] *)
      assert (NLE : Znth s norm <= 0).
      { destruct (Z_lt_le_dec 0 (Znth s norm)) as [Hp|Hn]; [|exact Hn]. exfalso. rewrite (unsigned_lit (Znth s norm)) in KXBR by lia.
        apply Bool.andb_false_iff in KXBR. destruct KXBR as [K|K]; apply Z.ltb_ge in K; lia. }
      assert (N0 : Z.to_nat (Znth s norm) = 0%nat) by lia.
      eapply (bf_slow_nextA t); [exact HS | |].
      + intros LT. eapply KN; [rewrite N0; reflexivity | exact LT | close_bf | exact HP].
      + intros EQ ?. eapply KE; [rewrite N0; reflexivity | exact EQ | close_bf | exact HP].
    - (* [comment removed for export] *)
      assert (NPOS : 0 < Znth s norm).
      { (* [comment removed for export] *)
        destruct (Z.eq_dec (Znth s norm) (-1)) as [E|NE].
        - exfalso. rewrite E in KXBR1. vm_compute in KXBR1. discriminate KXBR1.
        - rewrite (unsigned_lit (Znth s norm)) in KXBR0 by lia. exact KXBR0. }
      assert (HR : 0 <= high < 2^tl).
      { split; [| exact HHI]. pose proof (nsum_S norm tl TLR s ltac:(unfold FseNCount.Zlength in *; lia)) as N1.
        pose proof (nsum_mono norm maxSV tl TLR NLEN (s + 1) (maxSV + 1) ltac:(lia) ltac:(lia)) as N2.
        pose proof (nsum_nonneg norm maxSV tl TLR NLEN s ltac:(lia)) as N3. lia. }
      zstep.
      eapply (bf_place_nA t (Z.to_nat (Znth s norm - 1)) _ h0 h1 w0 w8 w16 w24 cells sn sp high s 0 (Znth s norm) position);
        [close_bf | exact HS | lia | lia | lia | exact HP | exact HR |].
      intros m2 cells' position' ya2 ys5 y28 PN I2 HP2.
      replace (S (Z.to_nat (Znth s norm - 1))) with (Z.to_nat (Znth s norm)) in PN by lia.
      (* [comment removed for export] *)
      zstep.
      eapply (bf_slow_nextA t); [exact HS | |].
      + intros LT. eapply KN; [exact PN | exact LT | exact I2 | exact HP2].
      + intros EQ ?. eapply KE; [exact PN | exact EQ | exact I2 | exact HP2].
  Qed.

  (* [comment removed for export] *)
  Lemma bf_slow_loopA : forall (t : seq_table) (f : nat) m1 h0 h1 w0 w8 w16 w24 cells sn sp high s position xa0 xi xa2 xs5 x28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29,
    BFm h0 h1 w0 w8 w16 w24 cells sn sp m1 ->
    0 <= s -> s + Z.of_nat (S f) = maxSV + 1 -> 0 <= position < 2^tl -> high + 1 = nsum norm (maxSV + 1) ->
    (forall m2 cells' p' ya0 ya5 yi ya2 ys5 y28,
       spread_slow (S f) norm (2^tl) STEP high s position cells = (cells', p') ->
       BFm h0 h1 w0 w8 w16 w24 cells' sn sp m2 ->
       evtF bsegs RNG (POST t) (STC 0x884a0 m2 high (Z_to_bv 64 (2^tl)) ya0 ya5 yi ya2 ys5 y28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29)) ->
    evtF bsegs RNG (POST t) (STC 0x88414 m1 high (Z_to_bv 64 position) xa0 (Z_to_bv 64 s) xi xa2 xs5 x28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29).
  Proof.
    intros t f. induction f as [|f IH]; intros until x29; intros I HS HSF HP HHN KONT.
    - eapply bf_slow_bodyA; [exact I | lia | exact HP | exact HHN | |].
      + intros; exfalso; lia.
      + intros m2 cells' p' ya0 ya5 yi ya2 ys5 y28 PN _ I2 HP2. eapply KONT; [| exact I2].
        cbn [spread_slow]. rewrite PN. reflexivity.
    - eapply bf_slow_bodyA; [exact I | lia | exact HP | exact HHN | |].
      + intros m2 cells' p' ya0 yi ya2 ys5 y28 PN LT I2 HP2.
        eapply (IH m2 h0 h1 w0 w8 w16 w24 cells' sn sp high (s + 1) p'); [exact I2 | lia | lia | exact HP2 | exact HHN |].
        intros m3 cells'' p'' ya0' ya5' yi' ya2' ys5' y28' SS I3. eapply KONT; [| exact I3].
        change (spread_slow (S (S f)) norm (2^tl) STEP high s position cells)
          with (let '(c1, p1) := place_n (Z.to_nat (Znth s norm)) (2^tl) STEP high s position cells in
                spread_slow (S f) norm (2^tl) STEP high (s + 1) p1 c1).
        rewrite PN. exact SS.
      + intros; exfalso; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_slowA : forall (t : seq_table) m1 h0 h1 w0 w8 w16 w24 cells sn sp high xra x5 xs1 xa0 x29 xa7 xs2 xs6 xs7 xs8 xs9 xs10 xs11 x30 x31,
    BFm h0 h1 w0 w8 w16 w24 cells sn sp m1 -> high + 1 = nsum norm (maxSV + 1) ->
    (forall m2 cells' p' ya0 ya5 yi ya2 ys5 y28,
       spread_slow (Z.to_nat (maxSV + 1)) norm (2^tl) STEP high 0 0 cells = (cells', p') ->
       BFm h0 h1 w0 w8 w16 w24 cells' sn sp m2 ->
       evtF bsegs RNG (POST t) (STC 0x884a0 m2 high (Z_to_bv 64 (2^tl)) ya0 ya5 yi ya2 ys5 y28 xra xs6 xs7 xs8 xs9 xs10 xs11 x29)) ->
    evtF bsegs RNG (POST t)
      (ST 0x883f4 m1 xra x5 (Z_to_bv 64 2147450880) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 high) xs1 xa0 x29 (Z_to_bv 64 (2^tl / 8))
          (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) (Z_to_bv 64 tl) (Z_to_bv 64 W) xa7 xs2 xs6 xs7 xs8 (Z_to_bv 64 DT) xs9 (Z_to_bv 64 NC) (Z_to_bv 64 (maxSV + 1)) xs10 xs11 (Z_to_bv 64 (DT + 8)) (Z_to_bv 64 (2^tl + -1)) x30 x31).
  Proof.
    intros until x31; intros I HHN KONT. bf_open I.
    kx_autoFLAc FR (@nil kza) [0x88414] 20%nat (KZB ++ []) (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z. all: try kx_acc RSTK. all: kx_mem. all: kx_tidy_run.
    lazymatch goal with |- _ => let v := StepF.reg_val 30 in lazymatch v with Z_to_bv 64 ?e =>
      replace e with STEP by (unfold fse_tablestep; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia) end end.
    eapply (bf_slow_loopA t (Z.to_nat maxSV) _ h0 h1 w0 w8 w16 w24 cells sn sp high 0 0); [close_bf | lia | lia | lia | exact HHN |].
    intros m2 cells' p' ya0 ya5 yi ya2 ys5 y28 SS I2. eapply KONT; [| exact I2].
    replace (Z.to_nat (maxSV + 1)) with (S (Z.to_nat maxSV)) by lia. exact SS.
  Qed.
End P2.
End CANSEC1.
