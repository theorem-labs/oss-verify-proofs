(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdSeqBuildWU ZdSeqBuildW3 ZdSeqBuildW4 ZdSeqBuildW5 ZdSeqBuildW6 SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_blk_iface AZ_kx AZ_bfse_defs AZ_bfse_p1 AZ_bfse_p3 AZ_bfse_p3b AZ_bfse_p2 AZ_bfse_p2a AZ_bfse_p2c.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit AZ_bfse_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
Lemma rw_cells_C4_congr : forall segs m A x v rest,
  x mod 2^32 = v mod 2^32 -> rw_cells segs m A (C4 (Z_to_bv 64 x) :: rest) -> rw_cells segs m A (C4 (Z_to_bv 64 v) :: rest).
Proof.
  intros segs m A x v rest E [[WF B] WR]. split; [split; [exact WF|]| exact WR].
  cbn [cells_bytes cbytes] in *. rewrite (le4_Z x v E) in B. rewrite (le4_Z v v eq_refl). exact B.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section G.
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
  Notation SP0 := (W + 106).

  (* [comment removed for export] *)
  Notation ST1X pc mm high fast xa0 xa1 xa5 x5 x31 :=
    (ST pc mm ra x5 (Z_to_bv 64 2147450880) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 high) (Z_to_bv 64 fast)
        xa0 xa1 (Z_to_bv 64 (NC + 2 * (maxSV + 1))) (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) xa5 (Z_to_bv 64 W) (Z_to_bv 64 (W + 2 * (maxSV + 1)))
        (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 (2^(tl - 1))) (Z_to_bv 64 65535) (Z_to_bv 64 (NC + 2 * (maxSV + 1))) (Z_to_bv 64 (W + 2 * (maxSV + 1))) (Z_to_bv 64 (maxSV + 1 - (maxSV + 1))) (Z_to_bv 64 NC) (Z_to_bv 64 (maxSV + 1))
        s10 s11 (Z_to_bv 64 (DT + 8)) (Z_to_bv 64 (2^tl + -1)) (Z_to_bv 64 SP0) x31).

  (* [comment removed for export] *)
  Definition bf_tableA (cells0 : list seqsym) (sn0 sp0 : list Z) : seq_table :=
    fst (fst (build_fse_table (kind_base k) (kind_bits k) norm maxSV tl cells0 sn0 sp0)).

  (* [comment removed for export] *)
  Lemma bf_after1A : forall m1 h0 h1 w0 w8 w16 w24 cells0 sn0 sp0 cells1 sn1 high fast xa0 xa1 xa5 x5 x31,
    zlen cells0 = 2^tl -> zlen sn0 = 53 -> zlen sp0 = wlen - 106 ->
    lowprob (Z.to_nat (maxSV + 1)) norm (2^(tl - 1)) 0 cells0 sn0 (2^tl - 1) 1 = (cells1, sn1, high, fast) ->
    BFm h0 h1 w0 w8 w16 w24 cells1 sn1 sp0 m1 -> 0 <= fast <= 1 ->
    evtF bsegs RNG (POST (bf_tableA cells0 sn0 sp0)) (ST1X 0x88224 m1 high fast xa0 xa1 xa5 x5 x31).
  Proof.
    intros until x31; intros HC0 HN0 HSP0 LP I HF. bf_open I.
    pose proof (p12_after1 norm maxSV tl TLR ltac:(lia) NLEN NGE NSUM cells0 sn0 cells1 sn1 high fast HC0 ltac:(unfold FseNCount.Zlength; lia) LP)
      as (HHN & HHR & C1 & N1 & S1 & AG1).
    (* [comment removed for export] *)
    kx_autoFLAc (FR, HDR) [KAUnp DT 8; KAApp DT 8; KAApp (SPV - 144) 144] [0x883f4; 0x88264] 30%nat
      (KZB ++ [KZRange fast 0 1; KZRange DT 4096 (2^47 - 16);
               KZWr DT 8; KZDisj DT 8 NC (2 * zlen norm); KZDisj DT 8 (SPV - 144) 144; KZDisj DT 8 (DT + 8) (8 * 2^tl);
               KZDisj DT 8 W 106; KZDisj DT 8 SP0 (wlen - 106);
               KZDisj DT 8 BASE (4 * (kind_max k + 1)); KZDisj DT 8 BITS (kind_max k + 1)])
      [(SPV - 144, 144)] [(DT, 8)].
    all: try kx_z. all: try kx_acc RSTK. all: try kx_acc RDT.
    all: try (kx_side_pre; unfold hidden in BDT; Z.div_mod_to_equations; lia).
    all: kx_mem. all: kx_tidy_run. all: try kx_gen_regsF [11%nat; 17%nat]. all: bf_reunp.
    all: rewrite ?(Z.mod_small (2^tl) (2^64)) by lia.
    all: lazymatch goal with |- _ => let v := StepF.reg_val 12 in lazymatch v with Z_to_bv 64 ?e =>
           replace e with (2^tl / 8) by (rewrite ?Z.shiftr_div_pow2 by lia; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia) end end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x883f4) _ _ ?mx _) =>   (* [comment removed for export] *)
             assert (NH : high <> 2^tl - 1) by (intros E; rewrite E in KXBR; rewrite Z.mod_small in KXBR by lia; lia);
             eapply (bf_slowA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT UW UNC UBA UBI
                       (bf_tableA cells0 sn0 sp0) mx (Z_to_bv 64 fast) (Z_to_bv 64 tl) w0 w8 w16 w24 cells1 sn1 sp0 high);
             [ close_bf | exact HHN |];
             intros m2 cells2 p2 ya0 ya5' yi ya2' ys5 y28 SS I2;
             destruct (p12_slow norm maxSV tl TLR ltac:(lia) NLEN NGE NSUM cells0 sn0 cells1 sn1 high fast HC0 ltac:(unfold FseNCount.Zlength; lia) LP NH cells2 p2 SS)
               as (C2 & G2);
             destruct (build_cells (Z.to_nat (2^tl)) tl (kind_base k) (kind_bits k) 0 cells2 sn1) as [cellsF snF] eqn:BC;
             assert (ET : bf_tableA cells0 sn0 sp0 = mkST fast tl cellsF)
               by (unfold bf_tableA, build_fse_table; rewrite LP; destruct (Z.eqb_spec high (2^tl - 1)) as [E|_]; [exfalso; exact (NH E)|];
                   rewrite SS; cbn [fst]; rewrite BC; reflexivity);
             rewrite ET;
             eapply (bf_p3A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT UW UNC UBA UBI);
             [ exact I2 | exact HF | exact G2 | exact S1 | exact BC ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x88264) _ _ ?mx _) =>   (* [comment removed for export] *)
             assert (EH : high = 2^tl - 1) by lia;
             eapply (bf_fastA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT UW UNC UBA UBI w16 w24
                       (bf_tableA cells0 sn0 sp0) mx (Z_to_bv 64 fast) (Z_to_bv 64 tl) w0 w8 cells1 sn1 sp0);
             [ close_bf | lia |];
             intros m2 spread1 pos1 cells2 p2 yra ys0 ys1 ya0 ya1 ya2' ya7' ys2 ys3 ys4 ys5' ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31 LSY PF I2;
             destruct (p12_fast norm maxSV tl TLR ltac:(lia) NLEN NGE NSUM cells0 sn0 sp0 cells1 sn1 high fast HC0 ltac:(unfold FseNCount.Zlength; lia)
                         ltac:(unfold FseNCount.Zlength; lia) LP EH spread1 pos1 cells2 p2 LSY PF) as (C2 & G2);
             destruct (build_cells (Z.to_nat (2^tl)) tl (kind_base k) (kind_bits k) 0 cells2 sn1) as [cellsF snF] eqn:BC;
             assert (ET : bf_tableA cells0 sn0 sp0 = mkST fast tl cellsF)
               by (unfold bf_tableA, build_fse_table; rewrite LP; destruct (Z.eqb_spec high (2^tl - 1)) as [_|NE]; [|exfalso; exact (NE EH)];
                   rewrite LSY, PF; cbn [fst]; rewrite BC; reflexivity);
             rewrite ET;
             eapply (bf_p3A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT UW UNC UBA UBI);
             [ exact I2 | exact HF | exact G2 | exact S1 | exact BC ]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_mainA : forall (xt0 xt1 xt2 xa7 xt3 xt4 xt5 xt6 : word) ha hb cells0 sn0 sp0,
    rw_cells bsegs m DT [C4 ha; C4 hb] ->
    u8arr bsegs m (DT + 8) (map (Z_to_bv 8) (flat_map seqsym_bytes cells0)) -> zlen cells0 = 2^tl ->
    u8arr bsegs m W (u16s (map (Z_to_bv 64) sn0)) -> zlen sn0 = 53 ->
    u8arr bsegs m (W + 106) (map (Z_to_bv 8) sp0) -> zlen sp0 = wlen - 106 -> Forall isbyte sp0 ->
    bytes_at bsegs m NC (u16s (map (Z_to_bv 64) norm)) ->
    bytes_at bsegs m BASE (u32s (map (Z_to_bv 64) (kind_base k))) ->
    bytes_at bsegs m BITS (map (Z_to_bv 8) (kind_bits k)) ->
    stk bsegs m lo SPV -> mem_inv bsegs m ->
    evtF bsegs RNG (POST (bf_tableA cells0 sn0 sp0))
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp xt0 xt1 xt2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 NC) (Z_to_bv 64 maxSV) (Z_to_bv 64 BASE) (Z_to_bv 64 BITS)
               (Z_to_bv 64 tl) (Z_to_bv 64 W) xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x88060) fc None m (seg_rom bsegs)).
  Proof.
    intros until sp0; intros HDR CEL CLEN SNX SNLEN SPRD SPLEN SPBY NCB BASEB BITSB STK0 MI.
    pose proof ART0 as ART1. destruct ART1 as (GOT & RIC & SHB & INI & LAY & REAL).
    open_hy HY. unfold KHIGH in *. pose proof (bf_bands _ _ _ _ _ _ _ _ _ _ _ _ _ HY) as (BDT & BW & BSP & B5 & B6 & B7 & B8). hide_all_disj.
    pose proof (bfA_size_rng _ _ _ _ _ _ _ _ _ _ _ _ _ HY) as (SZ & LLR & LL2). bf_consts.
    assert (MU : munch [(DT, DT + 8 + 8 * 2^tl); (W, W + wlen); (SPV - 176, SPV)] m m) by apply munch_refl.
    assert (WM : wmono bsegs m m) by apply wmono_refl.
    bf_lens.
    carve_frame 144%nat STK0.
    apply (rw_cells_split_CB bsegs _ _ [] 144 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    (* [comment removed for export] *)
    kx_autoFLAc (FR, GOT, SHB) [KAApp (SPV - 144) 144] [0x880b8] 50%nat
      (KZB ++ [KZWr (SPV - 144) 144; KZDisj (SPV - 144) 144 NC (2 * zlen norm); KZDisj (SPV - 144) 144 (DT + 8) (8 * 2^tl);
               KZDisj (SPV - 144) 144 DT 8; KZDisj (SPV - 144) 144 W 106; KZDisj (SPV - 144) 144 SP0 (wlen - 106);
               KZDisj (SPV - 144) 144 BASE (4 * (kind_max k + 1)); KZDisj (SPV - 144) 144 BITS (kind_max k + 1)])
      [(SPV - 144, 144)] [(SPV - 144, 144)].
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RSTK. all: try kx_acc RI.
    all: kx_mem. all: kx_tidy_run.
    (* [comment removed for export] *)
    zstep. rewrite (sllw_pow2 tl) by lia.
    (* [comment removed for export] *)
    kx_autoFLAc FR [KAApp (SPV - 144) 144] [0x88124] 30%nat
      (KZB ++ [KZWr (SPV - 144) 144; KZDisj (SPV - 144) 144 NC (2 * zlen norm); KZDisj (SPV - 144) 144 (DT + 8) (8 * 2^tl);
               KZDisj (SPV - 144) 144 DT 8; KZDisj (SPV - 144) 144 W 106; KZDisj (SPV - 144) 144 SP0 (wlen - 106);
               KZDisj (SPV - 144) 144 BASE (4 * (kind_max k + 1)); KZDisj (SPV - 144) 144 BITS (kind_max k + 1)])
      [(SPV - 144, 144)] [(SPV - 144, 144)].
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RSTK. all: try kx_acc RI.
    all: kx_mem. all: kx_tidy_run.
    (* [comment removed for export] *)
    zstep. rewrite (shiftl_mod32 65536 (tl + -1)) by lia.
    replace (tl + -1) with (tl - 1) by lia. rewrite (FseWalkKit.swrap32_small (65536 * 2^(tl - 1))) by lia.
    zstep. zstep. zstep.
    rewrite (signed_lit (65536 * 2^(tl - 1))) by lia.
    rewrite (Z.shiftr_div_pow2 (65536 * 2^(tl - 1)) 16) by lia. change (2^16) with 65536. rewrite (Z.mul_comm 65536), Z.div_mul by lia.
    rewrite (Z.shiftr_div_pow2 (4294967296 * maxSV + 4294967296) 32) by lia. change (2^32) with 4294967296.
    replace ((4294967296 * maxSV + 4294967296) / 4294967296) with (maxSV + 1) by (Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    kx_autoFLAc FR [KAApp (SPV - 144) 144] [0x88150] 10%nat
      (KZB ++ [KZWr (SPV - 144) 144; KZDisj (SPV - 144) 144 NC (2 * zlen norm); KZDisj (SPV - 144) 144 (DT + 8) (8 * 2^tl);
               KZDisj (SPV - 144) 144 DT 8; KZDisj (SPV - 144) 144 W 106; KZDisj (SPV - 144) 144 SP0 (wlen - 106);
               KZDisj (SPV - 144) 144 BASE (4 * (kind_max k + 1)); KZDisj (SPV - 144) 144 BITS (kind_max k + 1)])
      [(SPV - 144, 144)] [(SPV - 144, 144)].
    all: try kx_z. all: try kx_acc RSTK. all: kx_mem. all: kx_tidy_run.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 bsegs _ _ [] j post FR) as [w0 FR1] end. cbn [app] in FR1. clear FR.
    lazymatch type of FR1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 bsegs _ _ [c0; c1; c2; c3] j post FR1) as [w8 FR] end. cbn [app] in FR. clear FR1.
    bf_reunp.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (I : BFm ha hb w0 w8 (Z_to_bv 64 0) (Z_to_bv 64 0) cells0 sn0 sp0 mx) by close_bf;
      pose proof (bf_p1_0A RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DT NC BASE BITS W wlen maxSV tl k norm HY UDT UW UNC UBA UBI
                    (bf_tableA cells0 sn0 sp0) (Z.to_nat maxSV) mx ha hb w0 w8 (Z_to_bv 64 0) (Z_to_bv 64 0) cells0 sn0 sp0 (2^tl + -1) 1) as P1 end.
    replace (NC + 2 * 0) with NC in P1 by lia. replace (W + 2 * 0) with W in P1 by lia. replace (maxSV + 1 - 0) with (maxSV + 1) in P1 by lia.
    eapply P1; [exact I | lia | lia | lia |].
    intros m3 cells1 sn1 high fast ya0 ya1 ya5 y5 y31 LP I2 HF.
    replace (S (Z.to_nat maxSV)) with (Z.to_nat (maxSV + 1)) in LP by lia.
    replace (2^tl + -1) with (2^tl - 1) in LP by lia.
    eapply (bf_after1A m3 _ _ w0 w8 (Z_to_bv 64 0) (Z_to_bv 64 0) cells0 sn0 sp0 cells1 sn1 high fast); [exact CLEN | exact SNLEN | exact SPLEN | exact LP | exact I2 | exact HF].
  Qed.
End G.

(* [comment removed for export] *)
Ltac conj_spine := first [ simple apply conj; [ | conj_spine ] | idtac ].

(* [comment removed for export] *)
Theorem zd_buildfse_proofA : zd_buildfse_stmtA.
Proof.
  unfold zd_buildfse_stmtA, APZD_BUILDFSE, off_stack, apart. intros until norm.
  intros DTA DTLEN WA WLEN NCB TLR MSVR NLEN NGE NSUM BASEB BITSB DTL DTH WL WH NCL NCH BASER BITSR STK LOS LO0 SPR
         OFFDT OFFW OFFNC OFFBASE OFFBITS DTW DTNC WNC DTBASE DTBITS WBASE WBITS ADT AW ANC ABA ABI ART AST BAH BIH DT4 W2 NC2 BASE4 MI -> -> -> -> -> -> ->.
  assert (TL9 : 5 <= tl <= 9) by (destruct k; cbn [kind_maxLog] in TLR; lia).
  assert (SZ : 32 <= 2^tl <= 512).
  { assert (2^5 <= 2^tl) by (apply Z.pow_le_mono_r; lia). assert (2^tl <= 2^9) by (apply Z.pow_le_mono_r; lia).
    change (2^5) with 32 in *. change (2^9) with 512 in *. lia. }
  pose proof (kind_lens k) as (LKB & LKBI). pose proof (kind_max_range k) as KM.
  unfold FseNCount.Zlength in NLEN, NCH, OFFNC, DTNC, WNC, ANC.
  set (wlen := Z.of_nat (length wb0)) in *.
  destruct (ADT ltac:(lia)) as (ABDT & UDT & RDT & RSDT). clear ADT.
  replace (DT + (8 + 8 * 2^tl)) with (DT + 8 + 8 * 2^tl) in * by lia.
  destruct (AW ltac:(lia)) as (ABW & UW & RW & RSW). clear AW.
  destruct (ANC ltac:(lia)) as (ABNC & UNC & RNC & RSNC). clear ANC.
  rewrite LKB in ABA. rewrite LKBI in ABI.
  destruct ABA as (UBA & RBA & RSBA). destruct ABI as (UBI & RBI & RSBI).
  destruct AST as (KLO & RSTK & RI).
  assert (HY : bfA_hyps RNG SPV lo DT NC BASE BITS W wlen maxSV tl k norm).
  { unfold bfA_hyps, pws. conj_spine.
    all: first [ assumption | exact NSUM | lia
               | clear - OFFDT SZ; lia | clear - OFFW; lia | clear - OFFNC; lia | clear - OFFBASE; lia | clear - OFFBITS; lia
               | clear - DTW; lia | clear - DTNC; lia | clear - WNC; lia | clear - DTBASE; lia | clear - DTBITS; lia
               | clear - WBASE; lia | clear - WBITS; lia ]. }
  (* [comment removed for export] *)
  rewrite <- (firstn_skipn 8 dt0) in DTA. apply u8arr_app in DTA. destruct DTA as [HDRU CELU].
  assert (LH : length (firstn 8 dt0) = 8%nat) by (rewrite firstn_length; lia).
  rewrite LH in CELU. change (Z.of_nat 8) with 8 in CELU.
  apply rw_cells_of_u8arr in HDRU. rewrite LH in HDRU. destruct (cb8_as_c4s _ _ _ _ HDRU) as (ha & hb & HDR).
  destruct (cells_of_bytes (Z.to_nat (2^tl)) (skipn 8 dt0) ltac:(rewrite skipn_length; lia)) as (cells0 & LC0 & EC0).
  rewrite <- EC0 in CELU. unfold cellsB in CELU.
  (* [comment removed for export] *)
  rewrite <- (firstn_skipn 106 wb0) in WA. apply u8arr_app in WA. destruct WA as [SNU SPU].
  assert (LS : length (firstn 106 wb0) = 106%nat) by (rewrite firstn_length; lia).
  rewrite LS in SPU. change (Z.of_nat 106) with 106 in SPU.
  destruct (u16s_of_bytes 53 (firstn 106 wb0) LS) as (sn0 & LN0 & _ & EN0). rewrite EN0 in SNU.
  rewrite <- (bytes_of_unsigned (skipn 106 wb0)) in SPU.
  eapply evtF_mono.
  - eapply (bf_mainA RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DT NC BASE BITS W wlen maxSV tl k norm
              HY UDT UW UNC UBA UBI ART t0 t1 t2 a7 t3 t4 t5 t6 ha hb cells0 sn0 (map bv_unsigned (skipn 106 wb0)));
      [exact HDR | exact CELU | lia | exact SNU | lia | exact SPU
      | rewrite length_map, length_skipn; lia | apply bytes_unsigned_range
      | exact NCB | exact BASEB | exact BITSB | exact STK | exact MI].
  - intros ms' (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & wb' & -> & MU & WM & MI' & STK' & TB & WB' & LWB).
    unfold zd_buildfse_postA. do 15 eexists. exists m'. eexists. exists wb'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    split; [exact TB|].
    assert (OK : seq_table_ok k (bf_tableA maxSV tl k norm cells0 sn0 (map bv_unsigned (skipn 106 wb0)))).
    { unfold bf_tableA. apply (build_fse_table_ok_wsum k norm maxSV tl); try assumption; unfold FseNCount.Zlength; try lia.
      rewrite length_map, length_skipn. lia. }
    split; [| split; [exact OK | split; [exact WB' | lia]]].
    unfold bf_tableA, build_fse_table.
    destruct (lowprob _ _ _ _ _ _ _ _) as [[[c1 n1] h1] f1].
    destruct (if h1 =? 2 ^ tl - 1 then _ else _) as [c2 sp2].
    destruct (build_cells _ _ _ _ _ _ _) as [c3 n3]. reflexivity.
Qed.
End CANSEC1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
