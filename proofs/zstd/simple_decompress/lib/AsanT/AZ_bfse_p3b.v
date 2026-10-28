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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_blk_iface AZ_kx AZ_bfse_defs AZ_bfse_p3.
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
  Notation ST3 pc mm u xra xa0 xa1 xa2 xa5 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 :=
    (ST pc mm xra (Z_to_bv 64 (2^tl - u)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 16843009) xa5
        xa0 xa1 xa2 (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) (Z_to_bv 64 tl) (Z_to_bv 64 W) xa7
        xs6 xs7 x28 xs5 (Z_to_bv 64 DT) x29 xs8 xs9 xs10 xs11 (Z_to_bv 64 (8 * u)) (Z_to_bv 64 1431655765) (Z_to_bv 64 858993459) (Z_to_bv 64 252645135)).

  (* [comment removed for export] *)
  Lemma bf_p3_loopA : forall (f : nat) m1 fast w0 w8 w16 w24 u cells sn sp cellsF snF xra xa0 xa1 xa2 xa5 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29,
    BFm (Z_to_bv 64 fast) (Z_to_bv 64 tl) w0 w8 w16 w24 cells sn sp m1 -> 0 <= fast <= 1 ->
    0 <= u -> u + Z.of_nat (S f) = 2^tl ->
    (forall v, u <= v < 2^tl -> good norm maxSV (ss_base (cell_nth cells v))) ->
    (forall s, good norm maxSV s -> snext0 norm s <= Znth s sn <= snext0 norm s + u) ->
    build_cells (S f) tl (kind_base k) (kind_bits k) u cells sn = (cellsF, snF) ->
    evtF bsegs RNG (POST (mkST fast tl cellsF)) (ST3 0x884c4 m1 u xra xa0 xa1 xa2 xa5 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29).
  Proof.
    induction f as [|f IH]; intros until x29; intros I HF HU HUF GOODC SNB BC; bf_open I.
    all: assert (GU := GOODC u ltac:(lia)).
    all: assert (NSR : 1 <= Znth (ss_base (cell_nth cells u)) sn < 2 * 2^tl)
           by (pose proof (SNB _ GU); pose proof (snext0_good norm maxSV tl TLR NLEN NGE NSUM _ GU); lia).
    - eapply (bf_p3_bodyA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT UW UNC UBA UBI) with (u := u) (w16 := w16) (w24 := w24); [close_bf | lia | exact GU | exact NSR |].
      intros m2 ya0 ya1 ya2 ya5 ya7 ys5 ys6 ys7 y28 I2.
      cbn [build_cells] in BC. injection BC as <- <-.
      bf_reopen I2.
      kx_autoFLAc FR (@nil kza) [0x884c4; 0x8867c] 10%nat (KZB ++ [KZRange u 0 511; KZRange (2^tl - (u + 1)) 0 0]) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try kx_z. all: kx_mem. all: try (exfalso; lia).
      eapply (bf_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT UW UNC UBA UBI m2 fast w0 w8 w16 w24); [close_bf | exact HF].
    - eapply (bf_p3_bodyA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT UW UNC UBA UBI) with (u := u) (w16 := w16) (w24 := w24); [close_bf | lia | exact GU | exact NSR |].
      intros m2 ya0 ya1 ya2 ya5 ya7 ys5 ys6 ys7 y28 I2.
      set (sym := ss_base (cell_nth cells u)) in *. set (ns := Znth sym sn) in *.
      assert (E : build_cells (S (S f)) tl (kind_base k) (kind_bits k) u cells sn
                  = build_cells (S f) tl (kind_base k) (kind_bits k) (u + 1)
                      (set_cell u (build_one tl (kind_base k) (kind_bits k) sym ns) cells) (Zupd sym ((ns + 1) mod 2^16) sn)) by reflexivity.
      rewrite E in BC. clear E.
      bf_reopen I2.
      kx_autoFLAc FR (@nil kza) [0x884c4; 0x8867c] 10%nat (KZB ++ [KZRange u 0 511; KZRange (2^tl - (u + 1)) 1 512]) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try kx_z. all: kx_mem. all: try (exfalso; lia).
      eapply (IH _ fast w0 w8 w16 w24 (u + 1)); [close_bf | exact HF | lia | lia | | | exact BC].
      + intros v Hv. rewrite cell_nth_set_cell_other by lia. apply GOODC. lia.
      + intros s GS.
        assert (SYR : 0 <= sym <= 52) by (destruct GU; lia).
        rewrite (Znth_Zupd_eq tl TLR) by (unfold FseNCount.Zlength; destruct GS; lia).
        pose proof (SNB s GS) as B. destruct (Z.eqb_spec s sym) as [->|NE].
        * fold ns in B. rewrite Z.mod_small by (change (2^16) with 65536; lia). lia.
        * lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_p3A : forall m1 fast w0 w8 w16 w24 cells sn sp cellsF snF xra xs0 xs1 xa0 xa1 xa2 xa7 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    BFm (Z_to_bv 64 fast) (Z_to_bv 64 tl) w0 w8 w16 w24 cells sn sp m1 -> 0 <= fast <= 1 ->
    (forall v, 0 <= v < 2^tl -> good norm maxSV (ss_base (cell_nth cells v))) ->
    (forall s, 0 <= s <= maxSV -> Znth s sn = snext0 norm s) ->
    build_cells (Z.to_nat (2^tl)) tl (kind_base k) (kind_bits k) 0 cells sn = (cellsF, snF) ->
    evtF bsegs RNG (POST (mkST fast tl cellsF))
      (ST 0x884a0 m1 xra (Z_to_bv 64 (2^tl)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (2^tl)) xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 BASE) (Z_to_bv 64 BITS)
          (Z_to_bv 64 tl) (Z_to_bv 64 W) xa7 xs2 xs3 xs4 xs5 (Z_to_bv 64 DT) xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HF GOODC SN0 BC. bf_open I.
    kx_autoFLAc FR (@nil kza) [0x884c4] 25%nat (KZB ++ []) (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z. all: try kx_acc RSTK. all: kx_mem. all: kx_tidy_run.
    replace (Z.to_nat (2^tl)) with (S (Z.to_nat (2^tl - 1))) in BC by lia.
    epose proof (bf_p3_loopA (Z.to_nat (2^tl - 1)) _ fast w0 w8 w16 w24 0 cells sn sp cellsF snF) as L.
    replace (2^tl - 0) with (2^tl) in L by lia. replace (8 * 0) with 0 in L by lia.
    eapply L; [close_bf | exact HF | lia | lia | | | exact BC].
    - intros v Hv. apply GOODC. lia.
    - intros s GS. rewrite SN0 by (destruct GS; lia). lia.
  Qed.
End P3.
End CANSEC1.
