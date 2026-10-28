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
     AZ_frame_iface AZ_libc_iface AZ_kx AZ_globals AZ_globalsR AZ_findfsi_a.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation zlen l := (Z.of_nat (length l)).
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Notation SHB := 2147450880.
Notation BF1 := (Z_to_bv 8 18446744073709551601).
Notation BF2 := (Z_to_bv 8 18446744073709551602).
Notation BF3 := (Z_to_bv 8 18446744073709551603).
Notation BF8 := (Z_to_bv 8 18446744073709551608).
Notation B00 := (Z_to_bv 8 0).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition FSH0 : list cell :=
  [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF8; C1 BF8;
   C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00].

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

Section FS.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 : amem) (SPV SPA FSIP SRC : Z) (src : list Z) (off size lo FF SHF FLG : Z).
  (* [comment removed for export] *)
  Hypothesis OK : all_bytes src.
  Hypothesis OFF0 : 0 <= off.
  Hypothesis N5 : 5 <= size.
  Hypothesis N40 : size < 1099511627776.
  Hypothesis OFS : off + size <= zlen src.
  Hypothesis SRCE : SRC + zlen src < 2^64.
  Hypothesis F8 : FSIP mod 8 = 0.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPA - 4320 /\ SPV - 176 <= SPA <= SPV - 160 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  (* [comment removed for export] *)
  Hypothesis G_fsip : (17594333495296 <= FSIP /\ FSIP + 32 <= 2^47) /\ SPV <= FSIP.
  Hypothesis G_src : ablk SRC (SRC + zlen src) /\ (SRC + zlen src <= lo \/ SPV <= SRC) /\ (FSIP + 24 <= SRC \/ SRC + zlen src <= FSIP).
  Hypothesis G_ff : ablk FF (FF + 256) /\ FF mod 256 = 0 /\ FF + 256 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 256 <= al_fake L + FAKESZ
                    /\ (FSIP + 24 <= FF \/ FF + 256 <= FSIP) /\ (SRC + zlen src <= FF \/ FF + 256 <= SRC).
  Hypothesis G_flg : FLG = fflag L 2 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB2 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG)
                     /\ (FSIP + 24 <= FLG \/ FLG + 1 <= FSIP).
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_src : rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src)).
  Hypothesis R_fsip : rng RNG FSIP 24 /\ rng RNG (shad FSIP) (shspan FSIP 24).
  Hypothesis R_ff : rng RNG FF 256 /\ rng RNG SHF 32 /\ rng RNG FLG 1.
  Hypothesis LBH : ablkLB LB.

  Notation WR := [(FSIP, FSIP + 24)].
  Notation POST := (zd_findfsi_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV FSIP src off size lo m0).
  Notation RES := (find_frame_size_info src off size).

  Notation BINV := (AZ_findfsi_a.BINV AI L RNG st LB m0 SPV FSIP FF).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 SHF) (Z_to_bv 64 FF) (Z_to_bv 64 SHB) x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition EINV (m1 : amem) : Prop :=
    BINV m1 /\ rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ (exists jA, rw_cells bsegs m1 SPA [CB 48 jA; C8 (Z_to_bv 64 FF)])
    /\ stk bsegs m1 lo SPA /\ stk bsegs m1 (SPA + 56) (SPV + -104)
    /\ (exists j, rw_cells bsegs m1 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1a711); C8 (Z_to_bv 64 0x840b4); CB 224 j; C8 (Z_to_bv 64 FLG)])
    /\ rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m1 SHF FSH0
    /\ bytes_at bsegs m1 SRC (map (Z_to_bv 8) src) /\ unpoisoned m1 SRC (SRC + zlen src) /\ unpoisoned m1 FSIP (FSIP + 24)
    /\ (exists j24, rw_cells bsegs m1 FSIP [CB 24 j24]) /\ aro_client RNG m1.

  (* [comment removed for export] *)
  Hypothesis PFSK : forall m1 jfr w0 shb j0 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
    BINV m1 ->
    rw_cells bsegs m1 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m1 SPA [CB 56 jfr] -> stk bsegs m1 lo SPA -> stk bsegs m1 (SPA + 56) (SPV + -104) ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 248) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m1 SHF [CB 32 shb] ->
    rw_cells bsegs m1 FSIP [CB 8 j0; C8 (Z_to_bv 64 (fsi_csize RES)); C8 (Z_to_bv 64 (fsi_bound RES))] ->
    evtF bsegs RNG POST (STpc 0x84310 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) x19 x20 x21 x22 x23 x24 x28 x29 x30 x31).
  (* [comment removed for export] *)
  Hypothesis PGEN : forall m1 (x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x22 x23 x24 x28 x29 x30 x31 : word),
    EINV m1 -> ((ZD_SKIPPABLEHEADERSIZE <=? size) && is_skippable_magic (le32 src off)) = false ->
    evtF bsegs RNG POST (STpc 0x84374 m1 x1 x5 x6 x7 x10 x11 x12 (Z_to_bv 64 0) x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 FSIP) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 size)
                              x22 x23 x24 x28 x29 x30 x31).

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


  Ltac fs_hold :=
    repeat match goal with
    | H : rw_cells bsegs _ _ _ |- _ => fk_hold H
    | H : stk bsegs _ _ _ |- _ => fk_hold H
    | H : AZ_findfsi_a.BINV _ _ _ _ _ _ _ _ _ _ |- _ => fk_hold H
    | H : unpoisoned _ FSIP _ |- _ => fk_hold H
    | H : rng RNG FSIP _ |- _ => fk_hold H
    | H : rng RNG (shad FSIP) _ |- _ => fk_hold H
    | H : aro_client _ _ |- _ => fk_hold H
    | H : _ \/ _ |- _ => fk_hold H
    | H : exists _, _ |- _ => fk_hold H
    end.
  (* [comment removed for export] *)
  Ltac fs_run SL p k STOP :=
    gf_unhold; fs_hold; unfold fk_held in SL;
    kx_autoFA [KAUnp (SRC + off + p) k; KAApp (SRC + off + p) k] [STOP] 40%nat [KZRange SRC 6443008 (2^47); KZRange off 0 (2^47)] [] [];
    [ .. | kx_mem; gf_unhold ].
  (* [comment removed for export] *)
  Ltac fsip_sh UP RP2 k :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (unp_sh_rd0 mm FSIP 24 (FSIP + k) UP ltac:(clear; lia) ltac:(gf_unhold; clear - F8; Z.div_mod_to_equations; lia)
                  ltac:(gf_unhold; clear - G_fsip; lia) ltac:(gf_unhold; clear - G_fsip; lia)) as RDz;
    assert (RTz : rng RNG ((FSIP + k) ≫ 3 + SHB) 1)
      by (eapply rng_sub'; [exact RP2|]; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8;
          unfold shspan; rewrite shad_div; unfold ASHOFF; gf_unhold; clear - F8; Z.div_mod_to_equations; lia)
    end.
  Ltac fsip_sh0 UP RP2 :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (unp_sh_rd0 mm FSIP 24 FSIP UP ltac:(clear; lia) ltac:(gf_unhold; clear - F8; Z.div_mod_to_equations; lia)
                  ltac:(gf_unhold; clear - G_fsip; lia) ltac:(gf_unhold; clear - G_fsip; lia)) as RDz;
    assert (RTz : rng RNG (FSIP ≫ 3 + SHB) 1)
      by (eapply rng_sub'; [exact RP2|]; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8;
          unfold shspan; rewrite shad_div; unfold ASHOFF; gf_unhold; clear - F8; Z.div_mod_to_equations; lia)
    end.

  (* [comment removed for export] *)
  Ltac fsip_up UP MUL :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (UPc : unpoisoned mm FSIP (FSIP + 24))
        by (eapply unpoisoned_munch; [exact UP | exact MUL | cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF;
              gf_unhold; clear - G_fsip; Z.div_mod_to_equations; lia])
    end.

  (* [comment removed for export] *)
  Lemma p_skst : forall m1 v (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x28 x29 x30 x31 : word),
    EINV m1 -> ((ZD_SKIPPABLEHEADERSIZE <=? size) && is_skippable_magic (le32 src off)) = true ->
    Z_to_bv 64 v = Z_to_bv 64 (read_skippable_frame_size src off size) ->
    evtF bsegs RNG POST (STpc 0x842dc m1 x1 x5 x6 x7 x10 (Z_to_bv 64 v) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 FSIP) x20 (Z_to_bv 64 size)
                              x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros m1 v x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x28 x29 x30 x31
           (BI & SAV & [jA FRA] & STL & STG & [jH XH] & XL & XS & SB1 & US & UP & [j24 FC] & ARO) SK EV.
    assert (ER : RES = FSI 0 (read_skippable_frame_size src off size) 0) by (unfold find_frame_size_info; rewrite SK; reflexivity).
    pose proof G_lo as (G1 & G2 & G3 & G4 & G5 & G6). pose proof G_fsip as (P1 & P2). pose proof G_ff as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8').
    pose proof G_flg as (L0 & L1 & L2 & L3 & L4 & L5). pose proof R_fsip as (RP1 & RP2). pose proof G_src as (S1 & S2 & S3).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof P1 as PL. pose proof (fk_ablk_lits _ _ F1) as FL.
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity).
    assert (PSH : FSIP + 24 <= SHF \/ SHF + 32 <= FSIP) by (rewrite ESHF; clear - PL FL ATR; Z.div_mod_to_equations; lia).
    apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FC; [| reflexivity]. cbn [mk_CB_cells app] in FC.
    destruct BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    pose proof (munch_refl [(FSIP, FSIP + 24)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    fk_hold SB1. fk_hold US. fk_hold ARO. fk_hold AH1. fk_hold FFR1. fk_hold MU1. fk_hold WM1. fk_hold S2. fk_hold S3. fk_hold F8'. fk_hold L3. fk_hold L4.
    fk_hold XS. fk_hold SAV.
    rewrite EV.
    zsF.                                                         (* [comment removed for export] *)
    zsF. fsip_up UP MUL. fsip_sh UPc RP2 8. zsF. zsF. zsF. clear RDz RTz UPc. zsF. if_false.
    zsF.                                                         (* [comment removed for export] *)
    zsF. fsip_up UP MUL. fsip_sh UPc RP2 16. zsF. zsF. zsF. clear RDz RTz UPc. zsF. if_false.
    zsF.                                                         (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mC end.
    gf_unhold.
    apply (rw_cells_merge bsegs _ FSIP [] [C8 (Z_to_bv 64 0)] _) in FC. cbn [app cells_size csize Nat.add cells_bytes cbytes] in FC.
    destruct (rw_cells_forget _ _ _ _ FRA) as [jfr FRA']. cbn [cells_size csize Nat.add] in FRA'.
    apply (rw_cells_transport bsegs _ _ _ _ _ XS MUL) in WML as XS1; [| unfold FSH0; cbn; clear - PSH; lia].
    apply (rw_cells_transport bsegs _ _ _ _ _ SAV MUL) in WML as SAV1; [| unfold FSAVED; cbn; clear - P2 G2 G3; lia].
    clear XS SAV. destruct (rw_cells_forget _ _ _ _ XS1) as [shb XS']. unfold FSH0 in XS'. cbn [cells_size csize Nat.add length] in XS'.
    apply (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3)] _)) in XH. destruct XH as [XM XH]. cbn [cells_size csize Nat.add] in XH.
    apply (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x1a711); C8 (Z_to_bv 64 0x840b4); CB 224 jH] _)) in XH. destruct XH as [_ XP].
    cbn [cells_size csize Nat.add] in XP. replace (FF + Z.of_nat 8 + Z.of_nat 240) with (FF + 248) in XP by (clear; lia).
    eapply (PFSK mC jfr _ shb _); [| exact SAV1 | exact FRA' | exact STL | exact STG | exact XM | exact XP | exact XL | exact XS' | rewrite ER; cbn [fsi_csize fsi_bound]; exact FC].
    split; [| split; [| split; [| split; [exact (wmono_trans _ _ _ _ WM1 WML) | assumption]]]].
    - eapply (AI_frame AI); [exact AH1 | exact MUL | exact WML |].
      constructor; [cbn [fst snd]; left; left; clear - P1 P2 G1 G2 G3; lia | constructor].
    - eapply ffr_pres_trans; [exact FFR1|]. apply ffr_pres_mono_nil1.
      eapply (fk_ffr_fin AI L RNG st LB m1 m1 mC 2 FF 256 SHF 0 [] [(FSIP, FSIP + 24)]);
        [ exact AH1 | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia
        | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - P1 P2 G1 G2 G3; lia] | constructor]
        | constructor
        | apply ffr_pres_refl
        | cbn [app]; eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
        | exact WML ].
    - eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MUL]. unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma p_sk1 : forall m1 v (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x28 x29 x30 x31 : word),
    EINV m1 -> ((ZD_SKIPPABLEHEADERSIZE <=? size) && is_skippable_magic (le32 src off)) = true ->
    Z_to_bv 64 v = Z_to_bv 64 (read_skippable_frame_size src off size) ->
    evtF bsegs RNG POST (STpc 0x842cc m1 x1 x5 x6 x7 x10 (Z_to_bv 64 v) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 FSIP) x20 (Z_to_bv 64 size)
                              x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros m1 v x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x28 x29 x30 x31 EI SK EV.
    pose proof EI as (BI & SAV & [jA FRA] & STL & STG & [jH XH] & XL & XS & SB1 & US & UP & [j24 FC] & ARO).
    pose proof G_fsip as (P1 & P2). pose proof R_fsip as (RP1 & RP2). pose proof P1 as PL.
    destruct BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    fs_hold. unfold fk_held in PL, RP2.
    zsF. zsF. fsip_sh0 UP RP2. zsF. clear RDz RTz. zsF. if_false.
    gf_unhold. apply p_skst; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma p_top : forall m1 (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x22 x23 x24 x28 x29 x30 x31 : word),
    EINV m1 ->
    evtF bsegs RNG POST (STpc 0x84200 m1 x1 x5 x6 x7 (Z_to_bv 64 8) x11 x12 (Z_to_bv 64 0) x14 x15 x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 FSIP) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 size)
                              x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros m1 x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x22 x23 x24 x28 x29 x30 x31 EI.
    pose proof EI as (BI & SAV & [jA FRA] & STL & STG & [jH XH] & XL & XS & SB1 & US & UP & [j24 FC] & ARO).
    pose proof G_src as (S1 & S2 & S3). pose proof R_src as (RS1 & RS2).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (fk_ablk_lits _ _ S1) as SL.
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    assert (SRr : 6443008 <= SRC /\ SRC + zlen src + 8 <= 2^47) by (clear - SL ATR; lia).
    assert (RSZ : 5 <= size < 18446744073709551616) by (clear - N5 N40; lia).
    destruct BI as (AH1 & FFR1 & MU1 & WM1 & MI).
    zsF. if_cases K8; zify_cond K8.
    { (* [comment removed for export] *)
      gf_unhold. apply PGEN; [exact EI|].
      unfold ZD_SKIPPABLEHEADERSIZE. replace (8 <=? size) with false by (symmetry; apply Z.leb_gt; clear - K8; lia). reflexivity. }
    zsF. if_false.
    (* [comment removed for export] *)
    fs_run SL 0 4 0x8422c.
    fs_hold. assert (IB : 0 <= off + 0 /\ off + 8 <= zlen src /\ 0 <= SRC) by (unfold fk_held in K8; clear - K8 OFS OFF0 DB; lia). gf_hold_all.
    zlbF SB1 OK IB (off + 1). zlbF SB1 OK IB off. zlbF SB1 OK IB (off + 2). zlbF SB1 OK IB (off + 3).
    do 8 zsF.
    match goal with |- context [Z.shiftr ?e 4] => replace e with (le32 src off) by (rewrite le32_bytes; clear; lia) end.
    pose proof (le32_range src OK off) as RM. change (2^32) with 4294967296 in RM.
    rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^4) with 16.
    zsF. zsF. if_cases KS; zify_cond KS.
    { (* [comment removed for export] *)
      gf_unhold. apply PGEN; [exact EI|].
      unfold is_skippable_magic. replace (le32 src off / 16 =? 25481893) with false by (symmetry; apply Z.eqb_neq; clear - KS; lia). apply andb_false_r. }
    assert (SK : ((ZD_SKIPPABLEHEADERSIZE <=? size) && is_skippable_magic (le32 src off)) = true).
    { unfold ZD_SKIPPABLEHEADERSIZE, is_skippable_magic. unfold fk_held in K8. replace (8 <=? size) with true by (symmetry; apply Z.leb_le; clear - K8; lia).
      rewrite KS, Z.eqb_refl. reflexivity. }
    (* [comment removed for export] *)
    try clear KXE KXA KXRD KXK KXMI.
    fs_run SL 4 4 0x8428c.
    try clear KXMI. gf_hold_all.
    zlbF SB1 OK IB (off + 5). zlbF SB1 OK IB (off + 4). zlbF SB1 OK IB (off + 6). zlbF SB1 OK IB (off + 7).
    do 6 zsF.
    let w := getreg 10 in replace w with (Z_to_bv 64 (le32 src (off + 4)))
      by (f_equal; rewrite le32_bytes; replace (off + 4 + 1) with (off + 5) by (clear; lia); replace (off + 4 + 2) with (off + 6) by (clear; lia);
          replace (off + 4 + 3) with (off + 7) by (clear; lia); clear; lia).
    pose proof (le32_range src OK (off + 4)) as RS. change (2^32) with 4294967296 in RS.
    set (s32 := le32 src (off + 4)) in *.
    assert (RSK : read_skippable_frame_size src off size =
                  if 4294967287 <? s32 then ZERR ZE_frameParameter_unsupported else if size <? 8 + s32 then ZERR ZE_srcSize_wrong else 8 + s32).
    { unfold read_skippable_frame_size, ZD_SKIPPABLEHEADERSIZE. unfold fk_held in K8. replace (size <? 8) with false by (symmetry; apply Z.ltb_ge; clear - K8; lia).
      cbv zeta. fold s32. pose proof (skippable_wrap_iff s32 ltac:(change (2^32) with 4294967296; clear - RS; lia)) as WI.
      unfold ZD_SKIPPABLEHEADERSIZE in WI. rewrite WI. reflexivity. }
    unfold fk_held in RSZ.
    zsF. zsF. if_cases KA; zify_cond KA.
    - (* [comment removed for export] *)
      zsF. zsF. zsF. zsF. zsF. if_cases KW; zify_cond KW.
      + gf_unhold. eapply (p_sk1 _ (-72)); [exact EI | exact SK |].
        rewrite RSK. replace (4294967287 <? s32) with false by (symmetry; apply Z.ltb_ge; clear - KW; lia).
        replace (size <? 8 + s32) with true by (symmetry; apply Z.ltb_lt; clear - KA; lia). apply Z_to_bv_eqm. reflexivity.
      + (* [comment removed for export] *)
        zsF. pose proof G_fsip as (P1 & P2). pose proof R_fsip as (RP1 & RP2). pose proof P1 as PL. unfold fk_held in UP, RP2.
        zsF. zsF. fsip_sh0 UP RP2. zsF. clear RDz RTz. zsF. if_true.
        gf_unhold. eapply (p_skst _ (-14)); [exact EI | exact SK |].
        rewrite RSK. replace (4294967287 <? s32) with true by (symmetry; apply Z.ltb_lt; clear - KW; lia). apply Z_to_bv_eqm. reflexivity.
    - zsF. zsF. zsF. zsF. if_cases KW; zify_cond KW.
      + (* [comment removed for export] *)
        zsF. pose proof G_fsip as (P1 & P2). pose proof R_fsip as (RP1 & RP2). pose proof P1 as PL. unfold fk_held in UP, RP2.
        zsF. zsF. fsip_sh0 UP RP2. zsF. clear RDz RTz. zsF. if_true.
        gf_unhold. eapply (p_skst _ (-14)); [exact EI | exact SK |].
        rewrite RSK. replace (4294967287 <? s32) with true by (symmetry; apply Z.ltb_lt; clear - KW; lia). apply Z_to_bv_eqm. reflexivity.
      + gf_unhold. eapply (p_sk1 _ (s32 + 8)); [exact EI | exact SK |].
        rewrite RSK. replace (4294967287 <? s32) with false by (symmetry; apply Z.ltb_ge; clear - KW; lia).
        replace (size <? 8 + s32) with false by (symmetry; apply Z.ltb_ge; clear - KA; lia). f_equal. clear; lia.
  Qed.
End FS.
End CANSEC1.
