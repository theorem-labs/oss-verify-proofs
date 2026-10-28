(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdSeqBuildWU SepHide.
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
Section P3.
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


  (* [comment removed for export] *)
  Lemma bf_epiA : forall m1 fast w0 w8 w16 w24 cells sn sp xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    BFm (Z_to_bv 64 fast) (Z_to_bv 64 tl) w0 w8 w16 w24 cells sn sp m1 -> 0 <= fast <= 1 ->
    evtF bsegs RNG (POST (mkST fast tl cells))
      (ST 0x8867c m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I HF. pose proof (bf_wk_stkA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY _ _ _ _ _ _ _ _ _ _ I) as (WKS & DTS). bf_open I.
    kx_autoFLAc FR [KAApp (SPV - 144) 144] (@nil Z) 20%nat (KZB ++ [KZRange fast 0 1; KZWr (SPV - 144) 144]) [(SPV - 144, 144)] [(SPV - 144, 144)].
    all: try kx_z. all: try kx_acc RSTK.
    all: kx_mem. all: zstep.
    release_frame FR STK SPV.
    apply evtF_done. unfold bfA_post.
    do 15 eexists. exists m1. exists (u16s (map (Z_to_bv 64) sn) ++ map (Z_to_bv 8) sp).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
    split; [apply (table_u8arr bsegs m1 DT fast tl cells HDR CEL)|].
    split.
    - apply u8arr_app. split; [exact SNX|]. rewrite u16s_length, length_map.
      replace (W + Z.of_nat (2 * length sn)) with (W + 106) by lia. exact SPRD.
    - rewrite length_app, u16s_length, !length_map. lia.
  Qed.

  (* [comment removed for export] *)
  Notation ST3 pc mm u xra xa0 xa1 xa2 xa5 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 :=
    (ST pc mm xra (Z_to_bv 64 (2^tl - u)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 16843009) xa5
        xa0 xa1 xa2 (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) (Z_to_bv 64 tl) (Z_to_bv 64 W) xa7
        xs6 xs7 x28 xs5 (Z_to_bv 64 DT) x29 xs8 xs9 xs10 xs11 (Z_to_bv 64 (8 * u)) (Z_to_bv 64 1431655765) (Z_to_bv 64 858993459) (Z_to_bv 64 252645135)).

  (* [comment removed for export] *)
  Lemma bf_p3_bodyA : forall (t : seq_table) m1 h0 h1 w0 w8 w16 w24 u cells sn sp xra xa0 xa1 xa2 xa5 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29,
    BFm h0 h1 w0 w8 w16 w24 cells sn sp m1 -> 0 <= u < 2^tl ->
    good norm maxSV (ss_base (cell_nth cells u)) ->
    1 <= Znth (ss_base (cell_nth cells u)) sn < 2 * 2^tl ->
    (forall m2 ya0 ya1 ya2 ya5 ya7 ys5 ys6 ys7 y28,
       BFm h0 h1 w0 w8 w16 w24 (set_cell u (build_one tl (kind_base k) (kind_bits k) (ss_base (cell_nth cells u)) (Znth (ss_base (cell_nth cells u)) sn)) cells)
           (Zupd (ss_base (cell_nth cells u)) ((Znth (ss_base (cell_nth cells u)) sn + 1) mod 2^16) sn) sp m2 ->
       evtF bsegs RNG (POST t) (ST3 0x885fc m2 (u + 1) xra ya0 ya1 ya2 ya5 ya7 ys5 ys6 ys7 xs8 xs9 xs10 xs11 y28 x29)) ->
    evtF bsegs RNG (POST t) (ST3 0x884c4 m1 u xra xa0 xa1 xa2 xa5 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29).
  Proof.
    intros until x29; intros I HU GU NSR KONT. bf_open I.
    set (sym := ss_base (cell_nth cells u)) in *.
    assert (SYR : 0 <= sym <= maxSV) by (destruct GU; lia).
    set (ns := Znth sym sn) in *.
    pose proof (kind_bits_bytes k) as FBITS. pose proof (kind_base_small k) as FBASE.
    pose proof (Forall_Znth _ _ sym FBITS ltac:(lia)) as RBITS. pose proof (Forall_Znth _ _ sym FBASE ltac:(lia)) as RBASE. cbv beta in RBITS, RBASE.
    (* [comment removed for export] *)
    kx_autoFLAc (FR, HDR) [KAUnp (DT + 8 * u + 12) 4] [0x884e0] 20%nat
      (KZB ++ [KZRange u 0 511; KZRange (2^tl - u) 1 512; KZRange (DT + 8 * u + 12) 4096 (2^47 - 8); KZRange (8 * 2^tl - 8 * u) 8 4096])
      [(DT + 8 * u + 12, 4)] [(DT + 8 * u + 12, 4)].
    all: try kx_z. all: try kx_acc RDT. all: try kx_acc RSTK.
    kx_read_reg 19 RD.
    rewrite (rdval_sqb_base bsegs m1 (DT + 8) cells u _ CEL) in RD by lia.
    fold sym in RD. rewrite (Z.mod_small sym 4294967296) in RD by lia.
    rewrite RD. kx_tidy_run. try kx_gen_regsF [12%nat].
    lazymatch goal with |- _ => let v := StepF.reg_val 18 in lazymatch v with Z_to_bv 64 ?e =>
      replace e with (0x7fff8000 + (DT + 8 * u + 12) / 8) by (rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia) end end.
    (* [comment removed for export] *)
    bf_lens. kx_autoFLAc (FR, HDR) [KAUnp (W + 2 * sym) 2] [0x884fc] 30%nat
      (KZB ++ [KZRange u 0 511; KZRange sym 0 52; KZRange (maxSV - sym) 0 52; KZRange (W + 2 * sym) 4096 (2^47 - 8)])
      [(W + 2 * sym, 2)] [(W + 2 * sym, 2)].
    all: try kx_z. all: try kx_acc RW. all: try kx_acc RSTK.
    kx_read_reg 17 RD2.
    rewrite (rdval_u16Z bsegs m1 W sn sym _ (proj1 SNX)) in RD2 by lia. fold ns in RD2. rewrite (Z.mod_small ns 65536) in RD2 by lia.
    rewrite RD2. kx_tidy_run. try kx_gen_regsF [10%nat].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    bf_lens. kx_autoFLAc (FR, HDR) [KAUnp (W + 2 * sym) 2; KAApp (W + 2 * sym) 2; KAUnp (DT + 8 * u + 11) 1] [0x88518] 30%nat
      (KZB ++ [KZRange u 0 511; KZRange (2^tl - u) 1 512; KZRange sym 0 52; KZRange (maxSV - sym) 0 52; KZRange ns 1 65535;
               KZRange (W + 2 * sym) 4096 (2^47 - 8); KZRange (DT + 8 * u + 11) 4096 (2^47 - 8); KZRange (8 * 2^tl - 8 * u) 8 4096;
               KZWr (W + 2 * sym) 2; KZDisj (W + 2 * sym) 2 NC (2 * zlen norm); KZDisj (W + 2 * sym) 2 (SPV - 144) 144;
               KZDisj (W + 2 * sym) 2 (DT + 8) (8 * 2^tl); KZDisj (W + 2 * sym) 2 DT 8; KZDisj (W + 2 * sym) 2 (W + 106) (wlen - 106);
               KZDisj (W + 2 * sym) 2 BASE (4 * (kind_max k + 1)); KZDisj (W + 2 * sym) 2 BITS (kind_max k + 1)])
      (@nil (Z * Z)) [(W + 2 * sym, 2); (DT + 8 * u + 11, 1)].
    all: try kx_z. all: try kx_acc RW. all: try kx_acc RDT.
    kxk_keep CEL. kxk_keepg_ix SNX [sym]. kx_mem. kx_tidy_run. bf_reunp. try kx_gen_regsF [10%nat; 20%nat].
    try rewrite (unsigned_lit ns) in * by lia.
    (* [comment removed for export] *)
    zstep. zstep. zstep. set (sa := Z.lor ns (ns ≫ 1)). zstep. zstep. set (sb := Z.lor sa (sa ≫ 2)). zstep. zstep. set (sc := Z.lor sb (sb ≫ 4)).
    zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := StepF.reg_val 10 in lazymatch v with Z_to_bv 64 ?e => change e with (smear16 ns) end end.
    rewrite (smear16_ok ns) by lia.
    set (L := Z.log2 ns) in *.
    assert (HL : 0 <= L <= 10).
    { subst L. split; [apply Z.log2_nonneg|]. assert (Z.log2 ns < 11); [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2^11) with 2048. lia. }
    do 15 zstep.
    lazymatch goal with |- _ => let v := StepF.reg_val 10 in lazymatch v with Z_to_bv 64 ?e =>
      replace e with L by (clear - HL; clearbody L;
        assert (C : L = 0 \/ L = 1 \/ L = 2 \/ L = 3 \/ L = 4 \/ L = 5 \/ L = 6 \/ L = 7 \/ L = 8 \/ L = 9 \/ L = 10) by lia;
        destruct C as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]; rewrite E; vm_compute; reflexivity) end end.
    assert (LTL : L <= tl).
    { subst L. assert (Z.log2 ns < tl + 1); [|lia]. apply Z.log2_lt_pow2; [lia|]. rewrite Z.pow_add_r by lia. lia. }
    zstep.                                                     (* [comment removed for export] *)
    rewrite (FseWalkKit.swrap32_small (tl - L)) by lia.
    subst sa sb sc.
    lazymatch goal with |- _ => let v := StepF.reg_val 21 in lazymatch v with Z_to_bv 64 ?e =>
      replace e with ((DT + 8 * u + 8) / 8) by (rewrite ?Z.shiftr_div_pow2 by lia; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia) end end.
    (* [comment removed for export] *)
    bf_lens. kx_autoFLAc (FR, HDR) [KAUnp (DT + 8 * u + 8) 2; KAApp (DT + 8 * u + 8) 8; KAShp (0x7fff8000 + (DT + 8 * u + 8) / 8) (DT + 8 * u + 8)] [0x88590] 20%nat
      (KZB ++ [KZRange u 0 511; KZRange (2^tl - u) 1 512; KZRange L 0 10; KZRange (tl - L) 0 9;
               KZRange (DT + 8 * u + 8) 4096 (2^47 - 8); KZRange (8 * 2^tl - 8 * u) 8 4096;
               KZWr (DT + 8 * u + 8) 8; KZDisj (DT + 8 * u + 8) 8 NC (2 * zlen norm); KZDisj (DT + 8 * u + 8) 8 (SPV - 144) 144;
               KZDisj (DT + 8 * u + 8) 8 W 106; KZDisj (DT + 8 * u + 8) 8 (W + 106) (wlen - 106); KZDisj (DT + 8 * u + 8) 8 DT 8;
               KZDisj (DT + 8 * u + 8) 8 BASE (4 * (kind_max k + 1)); KZDisj (DT + 8 * u + 8) 8 BITS (kind_max k + 1)])
      (@nil (Z * Z)) [(DT + 8 * u + 8, 8)].
    all: try kx_z. all: try kx_acc RDT.
    all: try (kx_side_pre; unfold hidden in BDT; Z.div_mod_to_equations; lia).
    kxk_keepg CEL. kx_mem. kx_tidy_run. bf_reunp. try kx_gen_regsF [21%nat].
    (* [comment removed for export] *)
    zstep. rewrite (shiftl_mod32 ns (tl - L)) by lia.
    pose proof (shl_hb_range ns tl ltac:(lia) ltac:(lia) LTL) as NSB. fold L in NSB.
    rewrite (FseWalkKit.swrap32_small (ns * 2^(tl - L))) by lia.
    zstep.                                                     (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    rewrite ?(Z.mod_small (2^tl) 18446744073709551616) by lia.
    rewrite (FseWalkKit.swrap32_small (ns * 2^(tl - L) - 2^tl)) by lia.
    set (nxt := ns * 2^(tl - L) - 2^tl) in *.
    (* [comment removed for export] *)
    bf_lens. kx_autoFLAc (FR, HDR) [KAUnp (BITS + sym) 1; KAUnp (DT + 8 * u + 10) 1; KAApp (DT + 8 * u + 8) 8] [0x885cc] 40%nat
      (KZB ++ [KZRange u 0 511; KZRange (2^tl - u) 1 512; KZRange sym 0 52; KZRange (maxSV - sym) 0 52; KZRange (kind_max k - sym) 0 52; KZRange nxt 0 511;
               KZRange (DT + 8 * u + 8) 4096 (2^47 - 8); KZRange (BITS + sym) 4096 (2^47 - 1); KZRange (8 * 2^tl - 8 * u) 8 4096;
               KZWr (DT + 8 * u + 8) 8; KZDisj (DT + 8 * u + 8) 8 NC (2 * zlen norm); KZDisj (DT + 8 * u + 8) 8 (SPV - 144) 144;
               KZDisj (DT + 8 * u + 8) 8 W 106; KZDisj (DT + 8 * u + 8) 8 (W + 106) (wlen - 106); KZDisj (DT + 8 * u + 8) 8 DT 8;
               KZDisj (DT + 8 * u + 8) 8 BASE (4 * (kind_max k + 1)); KZDisj (DT + 8 * u + 8) 8 BITS (kind_max k + 1)])
      [(BITS + sym, 1)] [(DT + 8 * u + 8, 8); (BITS + sym, 1)].
    all: try kx_z. all: try kx_acc RDT. all: try kx_acc RBI.
    kx_read_reg 12 RD3.
    rewrite (rdval_u8s bsegs _ BITS (kind_bits k) sym _ BITSB) in RD3; [| lia | lia | exact FBITS].
    kxk_keepg CEL. kx_mem. rewrite RD3 in *. kx_tidy_run. bf_reunp. try kx_gen_regsF [10%nat; 17%nat; 20%nat].
    try rewrite (unsigned_lit (Znth sym (kind_bits k))) in * by lia.
    (* [comment removed for export] *)
    bf_lens. kx_autoFLAc (FR, HDR) [KAUnp (BASE + 4 * sym) 4; KAUnp (DT + 8 * u + 12) 4; KAApp (DT + 8 * u + 8) 8; KAShp (0x7fff8000 + (DT + 8 * u + 12) / 8) (DT + 8 * u + 12)] [0x885fc] 40%nat
      (KZB ++ [KZRange u 0 511; KZRange (2^tl - u) 1 512; KZRange sym 0 52; KZRange (maxSV - sym) 0 52; KZRange (kind_max k - sym) 0 52;
               KZRange (DT + 8 * u + 8) 4096 (2^47 - 8); KZRange (DT + 8 * u + 12) 4096 (2^47 - 8); KZRange (BASE + 4 * sym) 4096 (2^47 - 4); KZRange (8 * 2^tl - 8 * u) 8 4096;
               KZWr (DT + 8 * u + 8) 8; KZDisj (DT + 8 * u + 8) 8 NC (2 * zlen norm); KZDisj (DT + 8 * u + 8) 8 (SPV - 144) 144;
               KZDisj (DT + 8 * u + 8) 8 W 106; KZDisj (DT + 8 * u + 8) 8 (W + 106) (wlen - 106); KZDisj (DT + 8 * u + 8) 8 DT 8;
               KZDisj (DT + 8 * u + 8) 8 BASE (4 * (kind_max k + 1)); KZDisj (DT + 8 * u + 8) 8 BITS (kind_max k + 1)])
      [(BASE + 4 * sym, 4)] [(DT + 8 * u + 8, 8); (BASE + 4 * sym, 4)].
    all: try kx_z. all: try kx_acc RDT. all: try kx_acc RBA.
    all: try (kx_side_pre; unfold hidden in BDT; Z.div_mod_to_equations; lia).
    kx_read_reg 12 RD4.
    rewrite (rdval_u32s bsegs _ BASE (kind_base k) sym _ true BASEB) in RD4; [| lia | lia | exact RBASE].
    kxk_keepg CEL. kx_mem. rewrite RD4 in *. kx_tidy_run. bf_reunp. try kx_gen_regsF [10%nat; 12%nat; 17%nat].
    (* [comment removed for export] *)
    repeat match goal with E : hidden (?v = _) |- _ => unfold hidden in E; subst v end.
    rewrite ?(unsigned_lit (Znth sym (kind_base k))), ?(unsigned_lit (Znth sym (kind_bits k))), ?(unsigned_lit ns) in CEL by lia.
    try rewrite (unsigned_lit ns) in SNX by lia.
    assert (SNLEN' : zlen (Zupd sym ((ns + 1) mod 65536) sn) = 53) by (rewrite Zupd_length2; exact SNLEN).
    (* [comment removed for export] *)
    erewrite (sqb_cell8 cells u) in CEL by lia.
    assert (CE : {| ss_next := nxt; ss_nbAdd := Znth sym (kind_bits k); ss_nbBits := -1 * L + tl; ss_base := Znth sym (kind_base k) |}
                 = build_one tl (kind_base k) (kind_bits k) sym ns).
    { unfold build_one. fold L. subst nxt. rewrite (Z.mod_small (tl - L) 256) by lia.
      rewrite (Z.mod_small (ns * 2 ^ (tl - L) - 2 ^ tl) (2^16)) by (change (2^16) with 65536; lia). f_equal; lia. }
    rewrite CE in CEL. clear CE.
    assert (CLEN' : zlen (set_cell u (build_one tl (kind_base k) (kind_bits k) sym ns) cells) = 2^tl) by (rewrite set_cell_length2; exact CLEN).
    change ((ns + 1) mod 65536) with ((ns + 1) mod 2^16) in SNX, SNLEN'.
    kx_setreg 28 (8 * (u + 1)). kx_setreg 5 (2^tl - (u + 1)).
    eapply KONT. close_bf.
  Qed.

End P3.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
