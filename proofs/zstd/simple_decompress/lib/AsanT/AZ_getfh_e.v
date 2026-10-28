(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit ZdFrameW ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_frame_iface AZ_libc_iface AZ_kx AZ_getfh_a.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
(* [comment removed for export] *)
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation zlen l := (Z.of_nat (length l)).
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Notation SHB := 2147450880.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma unp_sh_rd0 : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n -> 0 <= X -> X + n <= 2^47 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr p 3 + SHB)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m X n p U H1 H2 H3 H4.
  pose proof (unp_shadow_zero m X n p U H1 H2) as B.
  assert (C : rw_cells bsegs m (shad p) [C1 (Z_to_bv 8 0)]).
  { apply rw_cells_C1_of_byte; [| | exact B]; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia. }
  pose proof (rw_cells_read bsegs m (shad p) [C1 (Z_to_bv 8 0)] 0 (C1 (Z_to_bv 8 0)) C eq_refl) as RD.
  rewrite Z.add_0_r in RD. unfold shad, ASHOFF in RD. rewrite Z.add_comm in RD. exact RD.
Qed.

Section GF.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 m2 m3 : amem) (SPV SPA ZFH SRC : Z) (src : list Z) (off size lo FF SHF FLG : Z) (jF : list byte).
  (* [comment removed for export] *)
  Hypothesis OK : all_bytes src.
  Hypothesis OFF0 : 0 <= off.
  Hypothesis N5 : 5 <= size.
  Hypothesis OFS : off + size <= zlen src.
  Hypothesis Z8 : ZFH mod 8 = 0.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPA - 2208 /\ SPV - 144 <= SPA <= SPV - 128 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  Hypothesis G_zfh : ablk ZFH (ZFH + 48) /\ (ZFH + 48 <= lo \/ SPV <= ZFH).
  Hypothesis G_src : ablk SRC (SRC + zlen src) /\ (SRC + zlen src <= lo \/ SPV <= SRC) /\ (ZFH + 48 <= SRC \/ SRC + zlen src <= ZFH).
  Hypothesis G_ff : ablk FF (FF + 64) /\ FF mod 64 = 0 /\ FF + 64 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 64 <= al_fake L + FAKESZ
                    /\ (ZFH + 48 <= FF \/ FF + 64 <= ZFH) /\ (SRC + zlen src <= FF \/ FF + 64 <= SRC).
  Hypothesis G_flg : FLG = fflag L 0 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB0 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG)
                     /\ (ZFH + 48 <= FLG \/ FLG + 1 <= ZFH).
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_src : rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src)).
  Hypothesis R_zfh : rng RNG ZFH 48 /\ rng RNG (shad ZFH) (shspan ZFH 48).
  Hypothesis R_ff : rng RNG FF 64 /\ rng RNG SHF 8 /\ rng RNG FLG 1.
  Hypothesis R_tbl : rng RNG 136800 32 /\ rng RNG (shad 136800) (shspan 136800 32) /\ rng RNG 136864 32 /\ rng RNG (shad 136864) (shspan 136864 32).
  (* [comment removed for export] *)
  Hypothesis LBH : ablkLB LB.
  Hypothesis AINZ : ainblk LB ZFH 48.
  Hypothesis AH2 : AHEAP AI L RNG st (FB0 FF :: LB) m2.
  Hypothesis FFR2 : ffr_pres [] LB m0 m2.
  Hypothesis MU23 : munch [(ZFH, ZFH + 48); (SPA - 2208, SPA + 32); (FF, FF + 24); (SHF, SHF + 8)] m2 m3.
  Hypothesis WM23 : wmono bsegs m2 m3.
  Hypothesis MU03 : munch ([(ZFH, ZFH + 48); (SPV - 4320, SPV)] ++ fake_area L) m0 m3.
  Hypothesis WM03 : wmono bsegs m0 m3.

  Notation WB := [(ZFH, ZFH + 48)].
  Notation WX := [(ZFH, ZFH + 48); (FF, FF + 8); (SHF, SHF + 8); (FLG, FLG + 1)].
  Notation POST := (zd_getfh_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV ZFH src off size lo m0).

  Notation fhd := (Znth (off + 4) src).
  Notation sseg := (fhd_singleSegment fhd).
  Notation dcode := (fhd_dictIDSizeCode fhd).
  Notation fcsid := (fhd_fcsID fhd).
  Notation P1 := (off + 5 + (if fhd_singleSegment fhd =? 0 then 1 else 0)).
  Notation P2 := (off + 5 + (if fhd_singleSegment fhd =? 0 then 1 else 0) + did_fieldSize (fhd_dictIDSizeCode fhd)).
  Notation DID := (fh_read_dictID src P1 dcode).
  Notation FCS := (fh_read_fcs src P2 fcsid sseg).
  Notation WS := (if fhd_singleSegment fhd =? 0 then wl_windowSize (Znth (off + 5) src) else FCS).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 FF) (Z_to_bv 64 ZFH) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 size) (Z_to_bv 64 0) (Z_to_bv 64 FF)
             (Z_to_bv 64 SHF) (Z_to_bv 64 SHB) (Z_to_bv 64 5) s11 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Notation XINV := (AZ_getfh_a.XINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m3 SPV SPA ZFH SRC src lo FF SHF FLG jF).
  Notation MINV := (AZ_getfh_a.MINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m3 SPV SPA ZFH SRC src lo FF SHF FLG jF).
  Notation MAINP := (AZ_getfh_a.MAINP src off size).
  Ltac xinv_i SAV FRA STL STG XF XS XL US UZ UT1 UT2 MU WM MI :=
    split; [exact SAV|]; split; [eexists; exact FRA|]; split; [exact STL|]; split; [exact STG|];
    split; [exact XF|]; split; [exact XS|]; split; [exact XL|]; split; [exact US|]; split; [exact UZ|];
    split; [exact UT1|]; split; [exact UT2|]; split; [exact MU|]; split; [exact WM| exact MI].
  Ltac xinv_e XI SAV jA FRA STL STG XF XS XL US UZ UT1 UT2 MU WM MI :=
    destruct XI as (SAV & [jA FRA] & STL & STG & XF & XS & XL & US & UZ & UT1 & UT2 & MU & WM & MI).
  (* [comment removed for export] *)
  Hypothesis PEXIT : forall m1 cs r res (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    XINV m1 -> rw_cells bsegs m1 ZFH cs -> cells_size cs = 48%nat ->
    get_frame_header src off size = res ->
    Z_to_bv 64 r = Z_to_bv 64 (fh_retval res) ->
    (forall h, res = FH_ok h -> cs = zfh_cells h) ->
    evtF bsegs RNG POST (STpc 0x83378 m1 x1 x5 x6 x7 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Hypothesis PMAGIC : forall m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x28 x29 x30 x31 : word),
    MINV m1 (Z0A (Z_to_bv 64 0)) -> le32 src off = ZD_MAGICNUMBER ->
    evtF bsegs RNG POST (STpc 0x83514 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 (Z_to_bv 64 5) x16 x17 x28 x29 x30 x31).

  Ltac gf_src_hold :=
    repeat match goal with
    | H : rw_cells bsegs _ _ _ |- _ => fk_hold H
    | H : stk bsegs _ _ _ |- _ => fk_hold H
    | H : munch _ _ _ |- _ => fk_hold H
    | H : wmono bsegs _ _ |- _ => fk_hold H
    | H : unpoisoned _ ZFH _ |- _ => fk_hold H
    | H : unpoisoned _ 136800 _ |- _ => fk_hold H
    | H : unpoisoned _ 136864 _ |- _ => fk_hold H
    | H : rng RNG ZFH _ |- _ => fk_hold H
    | H : rng RNG (shad ZFH) _ |- _ => fk_hold H
    | H : _ \/ _ |- _ => fk_hold H
    | H : ffr_pres _ _ _ _ |- _ => fk_hold H
    | H : AHEAP _ _ _ _ _ _ |- _ => fk_hold H
    | H : ablk _ _ /\ _ |- _ => fk_hold H                 (* [comment removed for export] *)
    | H : _ = fflag _ _ _ /\ _ |- _ => fk_hold H          (* [comment removed for export] *)
    | H : ATOP + 4096 <= _ /\ _ |- _ => fk_hold H
    end.
  Ltac gf_unhold := unfold fk_held in *.
  (* [comment removed for export] *)
  Ltac gf_hold_all :=
    repeat match goal with H : ?T |- _ =>
      lazymatch T with
      | fk_held _ => fail
      | (0 <= Znth _ _ < 256)%Z => fail
      | bytes_at _ _ _ _ => fail
      | mem_inv _ _ => fail
      | (0 <= _ + _ /\ _ /\ _)%Z => fail
      | all_bytes _ => fail
      | rng _ _ _ => fail
      | (rng _ _ _ /\ _) => fail
      | unpoisoned _ _ _ => fail
      | stk _ _ _ _ => fail
      | _ => lazymatch type of T with Prop => fk_hold H end
      end
    end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac keep_byte_facts := repeat match goal with H : ?T |- _ => lazymatch T with (0 <= Znth _ _ < 256)%Z => fail | _ => clear H end end.
  Ltac lor2add_sideF := keep_byte_facts; first [ lia | split; lia | Z.div_mod_to_equations; lia ].
  Ltac lor2add1F x y :=
    first [ rewrite (lor_add_disj 8 x y) by lor2add_sideF | rewrite (lor_add_disj 16 x y) by lor2add_sideF
          | rewrite (lor_add_disj 24 x y) by lor2add_sideF | rewrite (lor_add_disj 32 x y) by lor2add_sideF
          | rewrite (lor_add_disj 40 x y) by lor2add_sideF | rewrite (lor_add_disj 48 x y) by lor2add_sideF
          | rewrite (lor_add_disj 56 x y) by lor2add_sideF ].
  Ltac lor2addF := match goal with |- context [Z.lor ?x ?y] => first [ lor2add1F x y | rewrite (Z.lor_comm x y); lor2add1F y x ] end.
  Ltac clear_hyps := repeat match goal with H : _ |- _ => clear H end.
  Ltac shl2mulF :=
    repeat match goal with
    | |- context [Z.shiftl ?x ?k] => is_Zlit_zb k; rewrite (Z.shiftl_mul_pow2 x k) by (clear_hyps; lia);
          let v := eval vm_compute in (2^k) in change (2^k) with v
    end.
  (* [comment removed for export] *)
  Ltac zlbF SB OK IB i :=
    lazymatch type of SB with
    | bytes_at ?segs ?m ?SRC (map (Z_to_bv 8) ?src) =>
        let RD := fresh "RD" in
        assert (RD : ov_read_bytes segs m (Z_to_bv 64 (SRC + i)) 1 = Some [Z_to_bv 8 (Znth i src)])
          by (eapply zd_src_rd; [exact SB | clear - IB; lia | reflexivity]);
        first [ assert (0 <= Znth i src < 256) by assumption | let RB := fresh "RB" in assert (RB : 0 <= Znth i src < 256) by (apply OK) ];
        zstep; cbv beta; rewrite (byte_lit8 (Znth i src)) by assumption; clear RD; shl2mulF; repeat lor2addF
    end.
  Ltac zsF := zstep; shl2mulF; repeat lor2addF.

  (* [comment removed for export] *)
  Ltac gf_src_run p k STOP FUEL :=
    kx_autoFA [KAUnp (SRC + off + p) k; KAApp (SRC + off + p) k] [STOP] FUEL
      [KZRange SRC 6443008 (2^47); KZRange off 0 (2^47); KZRange p 4 24] [] [];
    [ .. | kx_mem; gf_unhold ].
  (* [comment removed for export] *)
  Ltac zlbsF SB OK IB i :=
    lazymatch type of SB with
    | bytes_at ?segs ?m ?SRC (map (Z_to_bv 8) ?src) =>
        let RD := fresh "RD" in
        assert (RD : ov_read_bytes segs m (Z_to_bv 64 (SRC + i)) 1 = Some [Z_to_bv 8 (Znth i src)])
          by (eapply zd_src_rd; [exact SB | clear - IB; lia | reflexivity]);
        first [ assert (0 <= Znth i src < 256) by assumption | let RB := fresh "RB" in assert (RB : 0 <= Znth i src < 256) by (apply OK) ];
        step; unfold sxb; rewrite (byte_sig8 (Znth i src)) by assumption; clear RD
    end.
  (* [comment removed for export] *)
  Ltac gf_src_run0 k STOP FUEL :=
    kx_autoFA [KAUnp (SRC + off) k; KAApp (SRC + off) k] [STOP] FUEL
      [KZRange SRC 6443008 (2^47); KZRange off 0 (2^47)] [] [];
    [ .. | kx_mem; gf_unhold ].


  (* [comment removed for export] *)
  Lemma xinv_transport : forall ma mb, XINV ma -> bytes_at bsegs ma SRC (map (Z_to_bv 8) src) -> munch WB ma mb -> wmono bsegs ma mb ->
    mem_inv bsegs mb -> XINV mb /\ bytes_at bsegs mb SRC (map (Z_to_bv 8) src).
  Proof.
    clear - G_lo G_zfh G_src G_ff G_flg. intros ma mb XIa SBa MUab WMab MIb.
    destruct XIa as (SAV' & [jA' FRA'] & STL' & STG' & XF' & XS' & XL' & US' & UZ' & UT1' & UT2' & MU' & WM' & MI').
    destruct G_lo as (G1 & G2 & G3 & G4 & G5 & G6). destruct G_zfh as (Z1 & Z2). destruct G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    destruct G_flg as (L0 & L1 & L2 & L3 & L4 & L5). destruct G_src as (S1' & S2' & S3').
    pose proof ATOP_range as ATR'. unfold ATOP_MIN, ATOP_MAX in ATR'.
    pose proof (fk_ablk_lits _ _ Z1) as ZL'. pose proof (fk_ablk_lits _ _ F1) as FL'. pose proof (fk_ablk_lits _ _ S1') as SL'.
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity).
    split; [| eapply bytes_at_transport; [exact SBa | exact MUab | rewrite length_map; cbn; clear - S3'; lia]].
    split; [eapply rw_cells_transport; [exact SAV' | exact MUab | exact WMab | cbn; clear - Z2 G2 G3; lia]|].
    split; [exists jA'; eapply rw_cells_transport; [exact FRA' | exact MUab | exact WMab | cbn; clear - Z2 G2 G3; lia]|].
    split; [eapply stk_transport_disjoint; [exact STL' | exact MUab | exact WMab | cbn; clear - Z2 G2 G3; lia]|].
    split; [eapply stk_transport_disjoint; [exact STG' | exact MUab | exact WMab | cbn; clear - Z2 G2 G3; lia]|].
    split; [eapply rw_cells_transport; [exact XF' | exact MUab | exact WMab | cbn; clear - F7; lia]|].
    split; [eapply rw_cells_transport; [exact XS' | exact MUab | exact WMab | cbn; rewrite ESHF; clear - ZL' FL' ATR'; Z.div_mod_to_equations; lia]|].
    split; [eapply rw_cells_transport; [exact XL' | exact MUab | exact WMab | cbn; clear - L5; lia]|].
    split; [eapply unpoisoned_munch; [exact US' | exact MUab | cbn [disjoint_from];
            pose proof (shad_mono SRC (SRC + zlen src - 1)); rewrite !shad_div in *; unfold ASHOFF in *; clear - H ZL' SL' ATR'; Z.div_mod_to_equations; lia]|].
    split; [eapply unpoisoned_munch; [exact UZ' | exact MUab | cbn [disjoint_from];
            pose proof (shad_mono ZFH (ZFH + 48 - 1)); rewrite !shad_div in *; unfold ASHOFF in *; clear - H ZL' ATR'; Z.div_mod_to_equations; lia]|].
    split; [eapply unpoisoned_munch; [exact UT1' | exact MUab | cbn; rewrite !shad_div; unfold ASHOFF; clear - ZL'; Z.div_mod_to_equations; lia]|].
    split; [eapply unpoisoned_munch; [exact UT2' | exact MUab | cbn; rewrite !shad_div; unfold ASHOFF; clear - ZL'; Z.div_mod_to_equations; lia]|].
    split; [exact (munch_trans _ _ _ _ MU' MUab)|]. split; [exact (wmono_trans _ _ _ _ WM' WMab)| exact MIb].
  Qed.

  (* [comment removed for export] *)
  Ltac gf_run SL p k STOP :=
    gf_unhold; gf_src_hold; unfold fk_held in SL;
    kx_autoFA [KAUnp (SRC + off + p) k; KAApp (SRC + off + p) k] [STOP] 40%nat [KZRange SRC 6443008 (2^47); KZRange off 0 (2^47)] [] [];
    [ .. | kx_mem; gf_unhold ].
  (* [comment removed for export] *)
  Ltac zfh_sh UZ RZ2 k :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (unp_sh_rd0 mm ZFH 48 (ZFH + k) UZ ltac:(clear; lia) ltac:(gf_unhold; clear - Z8; Z.div_mod_to_equations; lia)
                  ltac:(gf_unhold; clear - G_zfh; pose proof (fk_ablk_lits _ _ (proj1 G_zfh)); lia)
                  ltac:(gf_unhold; clear - G_zfh; pose proof (fk_ablk_lits _ _ (proj1 G_zfh)); pose proof ATOP_range as AA; unfold ATOP_MIN, ATOP_MAX in AA; lia)) as RDz;
    assert (RTz : rng RNG ((ZFH + k) ≫ 3 + SHB) 1)
      by (eapply rng_sub'; [exact RZ2|]; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8;
          unfold shspan; rewrite shad_div; unfold ASHOFF; gf_unhold; clear - Z8; Z.div_mod_to_equations; lia)
    end.
  (* [comment removed for export] *)
  Ltac zfh_sh0 UZ RZ2 :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (unp_sh_rd0 mm ZFH 48 ZFH UZ ltac:(clear; lia) ltac:(gf_unhold; clear - Z8; Z.div_mod_to_equations; lia)
                  ltac:(gf_unhold; clear - G_zfh; pose proof (fk_ablk_lits _ _ (proj1 G_zfh)); lia)
                  ltac:(gf_unhold; clear - G_zfh; pose proof (fk_ablk_lits _ _ (proj1 G_zfh)); pose proof ATOP_range as AA; unfold ATOP_MIN, ATOP_MAX in AA; lia)) as RDz;
    assert (RTz : rng RNG (ZFH ≫ 3 + SHB) 1)
      by (eapply rng_sub'; [exact RZ2|]; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8;
          unfold shspan; rewrite shad_div; unfold ASHOFF; gf_unhold; clear - Z8; Z.div_mod_to_equations; lia)
    end.

  (* [comment removed for export] *)
  Lemma p_top : forall m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    MINV m1 (Z0A (Z_to_bv 64 0)) ->
    evtF bsegs RNG POST (STpc 0x834ac m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    intros m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 MV.
    pose proof MV as (SB1 & ZC1 & XI).
    xinv_e XI SAV jA FRA STL STG XF XS XL US UZ UT1 UT2 MU WM MI. clear SAV jA FRA STL STG XF XS XL MU WM UT1 UT2.
    destruct G_src as (S1 & S2 & S3). destruct R_src as (RS1 & RS2). destruct R_zfh as (RZ1 & RZ2).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (fk_ablk_lits _ _ S1) as SL. pose proof (fk_ablk_lits _ _ (proj1 G_zfh)) as ZL.
    pose proof (OK (off + 4)) as RF. pose proof (OK (off + 5)) as RWL.
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    assert (SRr : 6443008 <= SRC /\ SRC + zlen src + 8 <= 2^47) by (clear - SL ATR; lia).
    assert (RSZ : 5 <= size < 18446744073709551616) by (clear - N5 OFS SRr DB OFF0; lia).
    assert (SZ5 : (size <? ZD_FRAMEHEADERSIZE_PREFIX) = false) by (apply Z.ltb_ge; unfold ZD_FRAMEHEADERSIZE_PREFIX; clear - N5; lia).
    (* [comment removed for export] *)
    gf_run SL 0 4 0x834e0.
    try rewrite (Z.mod_small (SRC + off) (2^64)) by (clear - SRr OFF0 OFS N5; lia).
    try rewrite (Z.mod_small (SRC + off + 3) (2^64)) by (clear - SRr OFF0 OFS N5; lia).
    gf_src_hold. assert (IB : 0 <= off + 0 /\ off + 5 <= zlen src /\ 0 <= SRC) by lia. gf_hold_all.
    zlbF SB1 OK IB (off + 1). zlbF SB1 OK IB off. zlbF SB1 OK IB (off + 2). zlbsF SB1 OK IB (off + 3).
    do 8 zsF.
    rewrite sx_le32_form by assumption.
    replace (Znth off src + 256 * Znth (off + 1) src + 65536 * Znth (off + 2) src + 16777216 * Znth (off + 3) src) with (le32 src off) by (rewrite le32_bytes; reflexivity).
    pose proof (le32_range src OK off) as RM. change (2^32) with 4294967296 in RM. pose proof (zsx32_range _ RM) as RMX.
    zsF. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (NM : le32 src off <> ZD_MAGICNUMBER).
      { intros E. apply K. rewrite E. reflexivity. }
      zsF. rewrite srliw4_zsx32 by exact RM.
      zsF. zsF. zsF. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        assert (RES : get_frame_header src off size = FH_ret (ZERR ZE_prefix_unknown)).
        { unfold get_frame_header. rewrite SZ5. cbv zeta. replace (le32 src off =? ZD_MAGICNUMBER) with false by (symmetry; apply Z.eqb_neq; exact NM).
          unfold is_skippable_magic. replace (le32 src off / 16 =? 25481893) with false by (symmetry; apply Z.eqb_neq; exact K1). reflexivity. }
        gf_unhold. destruct MV as (_ & _ & XI0).
        zsF. zsF. eapply (PEXIT _ _ (-10) _); [exact XI0 | exact ZC1 | reflexivity | exact RES | apply Z_to_bv_eqm; reflexivity | ].
        intros h E. discriminate E.
      + assert (RES : get_frame_header src off size = if size <? 8 then FH_ret 8 else FH_ok (mkFH (le32 src (off + 4)) 0 0 1 8 (le32 src off - ZD_MAGIC_SKIPPABLE_START) 0)).
        { unfold get_frame_header. rewrite SZ5. cbv zeta. replace (le32 src off =? ZD_MAGICNUMBER) with false by (symmetry; apply Z.eqb_neq; exact NM).
          unfold is_skippable_magic. rewrite K1, Z.eqb_refl. reflexivity. }
        unfold fk_held in RSZ.
        zsF. zsF. if_cases K2; zify_cond K2.
        * (* [comment removed for export] *)
          replace (size <? 8) with true in RES by (symmetry; apply Z.ltb_lt; clear - K2; lia).
          gf_unhold. destruct MV as (_ & _ & XI0).
          eapply (PEXIT _ _ 8 _); [exact XI0 | exact ZC1 | reflexivity | exact RES | reflexivity | ].
          intros h E. discriminate E.
        * replace (size <? 8) with false in RES by (symmetry; apply Z.ltb_ge; clear - K2; lia).
          (* [comment removed for export] *)
          unfold fk_held in ZL, UZ, RZ1, RZ2.
          zsF. zfh_sh UZ RZ2 20. zsF. zsF. zsF. clear RDz RTz.
          try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity. zsF. if_false.
          zsF.
          fk_hold SB1. unfold fk_held in ZC1. unfold Z0A in ZC1.
          pose proof (munch_refl WB m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
          try clear KXMI. zsF.
          unfold fk_held in MV, SB1. destruct MV as (_ & _ & XI0).
          pose proof (xinv_transport _ _ XI0 SB1 MUL WML MI) as [XIm SBm].
          fk_hold XI0. fk_hold SB1. clear US UZ.
          pose proof XIm as XIm'. xinv_e XIm' SAVm jAm FRAm STLm STGm XFm XSm XLm USm UZm UT1m UT2m MUm WMm MIm.
          clear SAVm jAm FRAm STLm STGm XFm XSm XLm UT1m UT2m MUm WMm MIm. try clear KXE KXA KXRD KXK.
          (* [comment removed for export] *)
          gf_unhold; gf_src_hold; unfold fk_held in SL.
          kx_autoFA [KAShp ((SRC + off) / 8 + SHB) (SRC + off); KAShp ((SRC + off + 3) / 8 + SHB) (SRC + off + 3); KAUnp (SRC + off) 4; KAApp (SRC + off) 4]
                    [0x83684] 40%nat [KZRange SRC 6443008 (2^47); KZRange off 0 (2^47)] [] []; [ .. | kx_mem; gf_unhold ].
          try clear KXMI. gf_hold_all. unfold fk_held in ZL, UZm, RZ1, RZ2.
          (* [comment removed for export] *)
          zsF. zsF. zsF. zfh_sh UZm RZ2 28. zsF. clear RDz RTz.
          zlbF SBm OK IB off. zlbF SBm OK IB (off + 1). zlbF SBm OK IB (off + 2). zlbsF SBm OK IB (off + 3).
          try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity. zsF. if_false.
          do 11 zsF.
          rewrite sx_le32_form by assumption.
          replace (Znth off src + 256 * Znth (off + 1) src + 65536 * Znth (off + 2) src + 16777216 * Znth (off + 3) src) with (le32 src off) by (rewrite le32_bytes; reflexivity).
          replace (Z_to_bv 64 (zsx32 (le32 src off) + -407710288)) with (Z_to_bv 64 (le32 src off - ZD_MAGIC_SKIPPABLE_START))
            by (unfold fk_held in K1; rewrite zsx32_small by (clear - K1 RM; Z.div_mod_to_equations; lia); f_equal; unfold ZD_MAGIC_SKIPPABLE_START; clear; lia).
          clear SBm USm UZm XIm. unfold fk_held in ZC1, MUL, WML.
          zsF.
          unfold fk_held in XI0, SB1. pose proof (xinv_transport _ _ XI0 SB1 MUL WML MI) as [XIm SBm]. fk_hold XI0. fk_hold SB1.
          pose proof XIm as XIm'. xinv_e XIm' SAVm jAm FRAm STLm STGm XFm XSm XLm USm UZm UT1m UT2m MUm WMm MIm.
          clear SAVm jAm FRAm STLm STGm XFm XSm XLm UT1m UT2m MUm WMm MIm.
          (* [comment removed for export] *)
          zsF. zfh_sh UZm RZ2 24.
          zsF. zsF. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity. if_false.
          zsF.                                                        (* [comment removed for export] *)
          clear SBm USm UZm XIm. unfold fk_held in ZC1, MUL, WML.
          zsF.
          unfold fk_held in XI0, SB1. pose proof (xinv_transport _ _ XI0 SB1 MUL WML MI) as [XIm SBm]. fk_hold XI0. fk_hold SB1.
          pose proof XIm as XIm'. xinv_e XIm' SAVm jAm FRAm STLm STGm XFm XSm XLm USm UZm UT1m UT2m MUm WMm MIm.
          clear SAVm jAm FRAm STLm STGm XFm XSm XLm UT1m UT2m MUm WMm MIm. try clear KXE KXA KXRD KXK.
          (* [comment removed for export] *)
          assert (W8 : off + 8 <= zlen src) by (gf_unhold; clear - K2 OFS; lia).
          gf_run SL 4 4 0x83714.
          try clear KXMI. gf_hold_all. unfold fk_held in ZL, UZm, RZ1, RZ2.
          assert (IB8 : 0 <= off + 4 /\ off + 8 <= zlen src /\ 0 <= SRC) by (unfold fk_held in IB, W8; clear - IB W8; lia).
          zsF. zsF. zfh_sh0 UZm RZ2. zsF. clear RDz RTz. zsF. if_false.
          zlbF SBm OK IB8 (off + 5). zlbF SBm OK IB8 (off + 4). zlbF SBm OK IB8 (off + 6). zlbF SBm OK IB8 (off + 7).
          do 6 zsF.
          let w := getreg 11 in replace w with (Z_to_bv 64 (le32 src (off + 4)))
            by (f_equal; rewrite le32_bytes; replace (off + 4 + 1) with (off + 5) by (clear; lia); replace (off + 4 + 2) with (off + 6) by (clear; lia);
                replace (off + 4 + 3) with (off + 7) by (clear; lia); clear; lia).
          clear SBm USm UZm XIm. unfold fk_held in ZC1, MUL, WML.
          zsF.                                                        (* [comment removed for export] *)
          unfold fk_held in XI0, SB1. pose proof (xinv_transport _ _ XI0 SB1 MUL WML MI) as [XIm SBm].
          zsF. gf_unhold.
          eapply (PEXIT _ _ 0 _); [exact XIm | exact ZC1 | reflexivity | exact RES | reflexivity | ].
          intros h E. injection E as <-. reflexivity.
    - (* [comment removed for export] *)
      apply (proj1 (zsx32_eq_lit (le32 src off) 4247762216 RM ltac:(clear; lia))) in K.
      gf_unhold. apply PMAGIC; [exact MV | exact K].
  Qed.
End GF.
End CANSEC1.
