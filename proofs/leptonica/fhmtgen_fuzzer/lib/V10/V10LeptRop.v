(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptStderr V10LeptBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL7a.
Import V10CL7a.V10LeptRop_iface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10_code_fhB V10_code_fhB V10_code_fhB V10_code_fhB.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptRopLow V10LeptRopUni.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].


(* [comment removed for export] *)
Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM, u_Z2bv by lia; rewrite EQ; reflexivity).
Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].

Section FrameKit.
Context {fx : FPState}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
Definition RLF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
    (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
    (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
    (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)))
    (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)))
    (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (getr regs 27)).

Lemma rdn_RLF_above : forall m s ret regs (a : Z) (n : nat), (112 <= s)%Z -> (s <= a)%Z -> (a + Z.of_nat n < 2 ^ 64)%Z ->
  rdn SEGS (RLF m s ret regs) (Z_to_bv 64 a) n = rdn SEGS m (Z_to_bv 64 a) n.
Proof.
  intros m s ret regs a n Hs Ha Hn. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. unfold RLF.
  rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
Qed.

Lemma RLF_outside : forall m s ret regs (a : word), (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 112 <= u a < s)%Z -> RLF m s ret regs a = m a.
Proof.
  intros m s ret regs a Hs Hs64 Ha. unfold RLF. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Definition rlcells (M : word -> option byte) (s : Z) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) /\
  rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v1) /\
  rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v2) /\
  rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v3) /\
  rdn SEGS M (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v4) /\
  rdn SEGS M (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v5) /\
  rdn SEGS M (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v6) /\
  rdn SEGS M (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v7) /\
  rdn SEGS M (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v8) /\
  rdn SEGS M (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v9) /\
  rdn SEGS M (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v10) /\
  rdn SEGS M (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 v11).

Lemma rlcells_RLF : forall m s ret regs, (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rlcells (RLF m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27).
Proof. intros m s ret regs Hs Hs64. unfold rlcells, RLF. repeat split; rdn_chain. Qed.

Lemma rlcells_frame : forall M M' s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11, (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rlcells M s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 -> (forall x : word, (s - 104 <= u x < s)%Z -> M' x = M x) -> rlcells M' s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11.
Proof.
  intros M M' s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 Hs Hs64 (C & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) E.
  unfold rlcells. repeat split;
    [rewrite <- C | rewrite <- C0 | rewrite <- C1 | rewrite <- C2 | rewrite <- C3 | rewrite <- C4 | rewrite <- C5 | rewrite <- C6 | rewrite <- C7 | rewrite <- C8 | rewrite <- C9 | rewrite <- C10 | rewrite <- C11];
    (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx; apply E; lia).
Qed.

End FrameKit.

Section PRSegs.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Notation w4 x := (word_to_le_bytes 4 x) (only parsing).

(* [comment removed for export] *)
Definition PRM (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) (w h d : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (RLF m s ret regs)
    (Z_to_bv 64 (s - 108)) (w4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 112)) (w4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 116)) (w4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 108)) (w4 (Z_to_bv 64 w))) (Z_to_bv 64 (s - 112)) (w4 (Z_to_bv 64 h))) (Z_to_bv 64 (s - 116)) (w4 (Z_to_bv 64 d)).

(* [comment removed for export] *)
Lemma pr_A : forall regs m (s pixd op : Z) (v : pixv) (ret syw : word),
  (224 <= s)%Z -> (s mod 16 = 0)%Z -> (pixd mod 8 = 0)%Z -> (s + 8 < 2 ^ 64)%Z -> (1 <= pixd)%Z -> (pixd + 64 <= s - 224 \/ s + 8 <= pixd)%Z -> PIXat m pixd v ->
  (0 <= p_w v < 2 ^ 31)%Z -> (0 <= p_h v < 2 ^ 31)%Z -> (0 <= p_d v < 2 ^ 31)%Z -> (0 <= op < 2 ^ 31)%Z -> (op <> 10)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 224)) 224 = true ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 syw) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 15 = Z_to_bv 64 op ->
  exists regs',
    msteps SEGS (mkst regs (0x1e488 : word) m rom) (mkst regs' (0x1e500 : word) (PRM m s ret regs (p_w v) (p_h v) (p_d v)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 224) /\ getr regs' 19 = Z_to_bv 64 op /\ getr regs' 20 = Z_to_bv 64 pixd /\ getr regs' 21 = syw
    /\ getr regs' 25 = getr regs 16 /\ getr regs' 22 = getr regs 17 /\ getr regs' 27 = getr regs 14 /\ getr regs' 18 = getr regs 11
    /\ getr regs' 9 = getr regs 12 /\ getr regs' 8 = getr regs 13
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 25; 27]%list) regs regs'.
Proof.
  intros regs m s pixd op v ret syw Hs Hs16 ALd8 Hs64 Hp DJ PX Hw Hh Hd Hop Hop10 SOK Rsy H2 H1 H10 H15.
  assert (SL108 : ((s - 108) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
  assert (SL112 : ((s - 112) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
  assert (SL116 : ((s - 116) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]). pose proof PX as (Hp0 & Hp64 & _).
  eexists. split.
  - zv F_1e38c D_1e38c (Z_to_bv 64 (s - 224)).
    stepST F_1e390 D_1e390 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_1e394 D_1e394 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_1e398 D_1e398 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_1e39c D_1e39c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_1e3a0 D_1e3a0 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepST F_1e3a4 D_1e3a4 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
    stepST F_1e3a8 D_1e3a8 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
    stepST F_1e3ac D_1e3ac (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
    stepST F_1e3b0 D_1e3b0 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
    stepST F_1e3b4 D_1e3b4 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
    stepST F_1e3b8 D_1e3b8 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
    stepST F_1e3bc D_1e3bc (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
    stepST F_1e3c0 D_1e3c0 (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
    stepb_ft F_1e3c4 D_1e3c4 ltac:(condZ).
    sn F_1e3c8 D_1e3c8. sn F_1e3cc D_1e3cc.
    stepb_ft F_1e3d0 D_1e3d0 ltac:(condZ).
    sn F_1e3d4 D_1e3d4. sn F_1e3d8 D_1e3d8. sn F_1e3dc D_1e3dc. sn F_1e3e0 D_1e3e0. sn F_1e3e4 D_1e3e4. sn F_1e3e8 D_1e3e8.
    stepLD F_1e3ec D_1e3ec (word_to_le_bytes 8 syw) syw ltac:(addr_norm; rewrite ?Z.sub_0_r; repeat rdn_peel1; exact Rsy) ltac:(apply bytes_le_to_Z_8).
    zv F_1e3f0 D_1e3f0 (Z_to_bv 64 (s - 108)). zv F_1e3f4 D_1e3f4 (Z_to_bv 64 (s - 112)). zv F_1e3f8 D_1e3f8 (Z_to_bv 64 (s - 116)).
    sn F_1e3fc D_1e3fc. sn F_1e400 D_1e400.
    (* [comment removed for export] *)
    zand F_1636c D_1636c andi_3 SL108.
    stepb_ft F_16370 D_16370 ltac:(condZ).
    stepb_ft F_16374 D_16374 ltac:(condR).
    stepST F_16378 D_16378 (Z_to_bv 64 (s - 108)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    zand F_1637c D_1637c andi_3 SL112.
    stepb_ft F_16380 D_16380 ltac:(condZ).
    stepb_ft F_16384 D_16384 ltac:(condR).
    stepST F_16388 D_16388 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    zand F_1638c D_1638c andi_3 SL116.
    stepb_ft F_16390 D_16390 ltac:(condZ).
    stepb_ft F_16394 D_16394 ltac:(condR).
    stepST F_16398 D_16398 (Z_to_bv 64 (s - 116)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    stepb_ft F_1639c D_1639c ltac:(condZ).
    zand F_163a0 D_163a0 andi_7 ALd8.
    stepb_ft F_163a4 D_163a4 ltac:(condZ).
    sn F_163a8 D_163a8.
    stepb_ft F_163ac D_163ac ltac:(condR).
    stepLD F_163b0 D_163b0 (Z_to_le_bytes 4 (p_w v)) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; rewrite ?Z.add_0_r; repeat rdn_peel1; exact (PIX_rd_w SEGS _ _ _ PX)) ltac:(apply lez4; lia).
    rewrite (v_lw_small (p_w v)) by lia.
    stepST F_163b4 D_163b4 (Z_to_bv 64 (s - 108)) (Z_to_bv 64 (p_w v)) ltac:(sok_in SOK).
    stepb_ft F_163b8 D_163b8 ltac:(condZ).
    sn F_163bc D_163bc.
    stepb_ft F_163c0 D_163c0 ltac:(condR).
    stepLD F_163c4 D_163c4 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
    rewrite (v_lw_small (p_h v)) by lia.
    stepST F_163c8 D_163c8 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 (p_h v)) ltac:(sok_in SOK).
    stepb_ft F_163cc D_163cc ltac:(condZ).
    sn F_163d0 D_163d0.
    stepb_ft F_163d4 D_163d4 ltac:(condR).
    stepLD F_163d8 D_163d8 (Z_to_le_bytes 4 (p_d v)) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_d SEGS _ _ _ PX)) ltac:(apply lez4; lia).
    rewrite (v_lw_small (p_d v)) by lia.
    stepST F_163dc D_163dc (Z_to_bv 64 (s - 116)) (Z_to_bv 64 (p_d v)) ltac:(sok_in SOK).
    sn F_163e0 D_163e0.
    stepret F_163e4 D_163e4 (0x1e500 : word) ltac:(bveq).
    unfold PRM, RLF. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma pr_Bu : forall regs m (s pixd op dx dy dw dh : Z) (v : pixv),
  (224 <= s)%Z -> (s mod 16 = 0)%Z -> (pixd mod 8 = 0)%Z -> (s + 8 < 2 ^ 64)%Z -> (1 <= pixd)%Z -> (pixd + 64 <= s - 224 \/ s + 8 <= pixd)%Z -> PIXat m pixd v ->
  (0 <= p_w v < 2 ^ 31)%Z -> (0 <= p_h v < 2 ^ 31)%Z -> (0 <= p_d v < 2 ^ 31)%Z -> (0 <= p_wpl v < 2 ^ 31)%Z -> (0 <= p_data v < 2 ^ 64)%Z -> (op = 0 \/ op = 15)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 224)) 16 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_h v))) ->
  rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_d v))) ->
  getr regs 2 = Z_to_bv 64 (s - 224) -> getr regs 19 = Z_to_bv 64 op -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 27 = Z_to_bv 64 dh ->
  getr regs 18 = Z_to_bv 64 dx -> getr regs 9 = Z_to_bv 64 dy -> getr regs 8 = Z_to_bv 64 dw ->
  exists regs',
    msteps SEGS (mkst regs (0x1e500 : word) m rom)
                (mkst regs' (0x1e724 : word) (wbytes (wbytes m (Z_to_bv 64 (s - 224)) (word_to_le_bytes 8 (Z_to_bv 64 dh))) (Z_to_bv 64 (s - 216)) (word_to_le_bytes 8 (Z_to_bv 64 op))) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 224) /\ getr regs' 1 = Z_to_bv 64 0x1e568
    /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 11 = Z_to_bv 64 (p_w v) /\ getr regs' 12 = Z_to_bv 64 (p_h v) /\ getr regs' 13 = Z_to_bv 64 (p_d v)
    /\ getr regs' 14 = Z_to_bv 64 (p_wpl v) /\ getr regs' 15 = Z_to_bv 64 dx /\ getr regs' 16 = Z_to_bv 64 dy /\ getr regs' 17 = Z_to_bv 64 dw
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24]%list) regs regs'.
Proof.
  intros regs m s pixd op dx dy dw dh v Hs Hs16 ALd8 Hs64 Hp DJ PX Hw Hh Hd Hwpl Hdata Hop SOK Rw Rh Rd R2 R19 R20 R27 R18 R9 R8.
  pose proof PX as (Hp0 & Hp64 & _).
  eexists; (split; [
    sn F_1e404 D_1e404;
    stepb_ft F_1e408 D_1e408 ltac:(condZ);
    sn F_1e40c D_1e40c; sn F_1e410 D_1e410; sn F_1e414 D_1e414;
    stepiv F_1e418 D_1e418 (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; destruct Hop as [-> | ->]; apply bv_eq; vm_compute; reflexivity);
    stepb_ft F_1e41c D_1e41c ltac:(condZ);
    sn F_1e420 D_1e420; sn F_1e424 D_1e424;
    stepb_ft F_17180 D_17180 ltac:(condZ);
    zand F_17184 D_17184 andi_7 ALd8;
    stepb_ft F_17188 D_17188 ltac:(condR);
    stepLD F_1718c D_1718c (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v)) ltac:(addr_norm; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia);
    stepret F_17190 D_17190 (0x1e524 : word) ltac:(bveq);
    stepLD F_1e428 D_1e428 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia);
    rewrite (v_lw_small (p_w v)) by lia;
    stepLD F_1e42c D_1e42c (word_to_le_bytes 4 (Z_to_bv 64 (p_h v))) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia);
    rewrite (v_lw_small (p_h v)) by lia;
    stepLD F_1e430 D_1e430 (word_to_le_bytes 4 (Z_to_bv 64 (p_d v))) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; exact Rd) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia);
    rewrite (v_lw_small (p_d v)) by lia;
    sn F_1e434 D_1e434; sn F_1e438 D_1e438; sn F_1e43c D_1e43c;
    stepb_ft F_16014 D_16014 ltac:(condZ);
    zand F_16018 D_16018 andi_7 ALd8;
    stepb_ft F_1601c D_1601c ltac:(condR);
    stepLD F_16020 D_16020 (Z_to_le_bytes 4 (p_wpl v)) (Z_to_bv 64 (p_wpl v)) ltac:(addr_norm; exact (PIX_rd_wpl SEGS _ _ _ PX)) ltac:(apply lez4; lia);
    rewrite (v_lw_small (p_wpl v)) by lia;
    stepret F_16024 D_16024 (0x1e53c : word) ltac:(bveq);
    sn F_1e440 D_1e440;
    stepST F_1e444 D_1e444 (Z_to_bv 64 (s - 224)) (Z_to_bv 64 dh) ltac:(sok_in SOK);
    stepST F_1e448 D_1e448 (Z_to_bv 64 (s - 216)) (Z_to_bv 64 op) ltac:(sok_in SOK);
    sn F_1e44c D_1e44c; sn F_1e450 D_1e450; sn F_1e454 D_1e454; sn F_1e458 D_1e458; sn F_1e45c D_1e45c; sn F_1e460 D_1e460; sn F_1e464 D_1e464;
    sn F_1e468 D_1e468;
    apply mst_refl
  | repeat split; gres; pin; try reflexivity; solve_regs_agree ]).
Qed.

(* [comment removed for export] *)
Lemma pr_C : forall regs m (s : Z) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  (224 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> rlcells m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 -> getr regs 2 = Z_to_bv 64 (s - 224) ->
  exists regs',
    msteps SEGS (mkst regs (0x1e568 : word) m rom) (mkst regs' ret m rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2 /\ getr regs' 19 = v3 /\ getr regs' 20 = v4 /\ getr regs' 21 = v5 /\ getr regs' 22 = v6 /\ getr regs' 23 = v7 /\ getr regs' 24 = v8 /\ getr regs' 25 = v9 /\ getr regs' 26 = v10 /\ getr regs' 27 = v11
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros regs m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 Hs Hs64 Hret (C & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) R2. eexists. split.
  - sn F_1e46c D_1e46c. sn F_1e470 D_1e470.
    stepLD8 F_1e5ec D_1e5ec ret. stepLD8 F_1e5f0 D_1e5f0 v0. stepLD8 F_1e5f4 D_1e5f4 v1. stepLD8 F_1e5f8 D_1e5f8 v2.
    stepLD8 F_1e5fc D_1e5fc v3. stepLD8 F_1e600 D_1e600 v4. stepLD8 F_1e604 D_1e604 v5. stepLD8 F_1e608 D_1e608 v6.
    stepLD8 F_1e60c D_1e60c v7. stepLD8 F_1e610 D_1e610 v8. stepLD8 F_1e614 D_1e614 v9. stepLD8 F_1e618 D_1e618 v10.
    stepLD8 F_1e61c D_1e61c v11.
    zv F_1e620 D_1e620 (Z_to_bv 64 s).
    stepret F_1e624 D_1e624 ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Definition PSM (m : word -> option byte) (s : Z) (vd vs : pixv) (dh sx sy : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 120)) (w4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 124)) (w4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 128)) (w4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 120)) (w4 (Z_to_bv 64 (p_w vs)))) (Z_to_bv 64 (s - 124)) (w4 (Z_to_bv 64 (p_h vs)))) (Z_to_bv 64 (s - 128)) (w4 (Z_to_bv 64 (p_d vs))))
    (Z_to_bv 64 (s - 136)) (word_to_le_bytes 8 (Z_to_bv 64 (p_w vd)))) (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (Z_to_bv 64 (p_h vd))))
    (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (Z_to_bv 64 (p_d vd)))) (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (Z_to_bv 64 (p_data vd))))
    (Z_to_bv 64 (s - 192)) (word_to_le_bytes 8 (Z_to_bv 64 (p_h vs)))) (Z_to_bv 64 (s - 184)) (word_to_le_bytes 8 (Z_to_bv 64 (p_wpl vs))))
    (Z_to_bv 64 (s - 176)) (word_to_le_bytes 8 (Z_to_bv 64 sx))) (Z_to_bv 64 (s - 168)) (word_to_le_bytes 8 (Z_to_bv 64 sy)))
    (Z_to_bv 64 (s - 224)) (word_to_le_bytes 8 (Z_to_bv 64 dh))) (Z_to_bv 64 (s - 216)) (word_to_le_bytes 8 (Z_to_bv 64 12)))
    (Z_to_bv 64 (s - 208)) (word_to_le_bytes 8 (Z_to_bv 64 (p_data vs)))) (Z_to_bv 64 (s - 200)) (word_to_le_bytes 8 (Z_to_bv 64 (p_w vs))).

Lemma pr_Bs : forall regs m (s pixd pixs dx dy dw dh sx sy : Z) (vd vs : pixv),
  (224 <= s)%Z -> (s mod 16 = 0)%Z -> (pixd mod 8 = 0)%Z -> (pixs mod 8 = 0)%Z -> (s + 8 < 2 ^ 64)%Z -> (1 <= pixd)%Z -> (pixd + 64 <= s - 224 \/ s + 8 <= pixd)%Z -> PIXat m pixd vd ->
  (1 <= pixs)%Z -> (pixs + 64 <= s - 224 \/ s + 8 <= pixs)%Z -> PIXat m pixs vs -> p_d vs = p_d vd ->
  (0 <= p_w vd < 2 ^ 31)%Z -> (0 <= p_h vd < 2 ^ 31)%Z -> (0 <= p_d vd < 2 ^ 31)%Z -> (0 <= p_wpl vd < 2 ^ 31)%Z -> (0 <= p_data vd < 2 ^ 64)%Z ->
  (0 <= p_w vs < 2 ^ 31)%Z -> (0 <= p_h vs < 2 ^ 31)%Z -> (0 <= p_wpl vs < 2 ^ 31)%Z -> (0 <= p_data vs < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 224)) 108 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w vd))) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_h vd))) ->
  rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_d vd))) ->
  getr regs 2 = Z_to_bv 64 (s - 224) -> getr regs 19 = Z_to_bv 64 12 -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 25 = Z_to_bv 64 pixs ->
  getr regs 27 = Z_to_bv 64 dh -> getr regs 18 = Z_to_bv 64 dx -> getr regs 9 = Z_to_bv 64 dy -> getr regs 8 = Z_to_bv 64 dw ->
  getr regs 22 = Z_to_bv 64 sx -> getr regs 21 = Z_to_bv 64 sy ->
  exists regs',
    msteps SEGS (mkst regs (0x1e500 : word) m rom) (mkst regs' (0x1efe8 : word) (PSM m s vd vs dh sx sy) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 224) /\ getr regs' 1 = Z_to_bv 64 0x1e688
    /\ getr regs' 10 = Z_to_bv 64 (p_data vd) /\ getr regs' 11 = Z_to_bv 64 (p_w vd) /\ getr regs' 12 = Z_to_bv 64 (p_h vd) /\ getr regs' 13 = Z_to_bv 64 (p_d vd)
    /\ getr regs' 14 = Z_to_bv 64 (p_wpl vd) /\ getr regs' 15 = Z_to_bv 64 dx /\ getr regs' 16 = Z_to_bv 64 dy /\ getr regs' 17 = Z_to_bv 64 dw
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17; 20; 23; 24; 26]%list) regs regs'.
Proof.
  intros regs m s pixd pixs dx dy dw dh sx sy vd vs Hs Hs16 ALd8 ALs8 Hs64 Hp DJ PX Hps DJs PXs Edd Hw Hh Hd Hwpl Hdata Hsw Hsh Hswpl Hsdata SOK Rw Rh Rd
    R2 R19 R20 R25 R27 R18 R9 R8 R22 R21.
  assert (SL120 : ((s - 120) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
  assert (SL124 : ((s - 124) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
  assert (SL128 : ((s - 128) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
  pose proof PX as (Hp0 & Hp64 & _). pose proof PXs as (Hps0 & Hps64 & _).
  assert (Hsd : (0 <= p_d vs < 2 ^ 31)%Z) by (rewrite Edd; exact Hd).
  eexists. split.
  - sn F_1e404 D_1e404.
    stepb_ft F_1e408 D_1e408 ltac:(condZ).
    sn F_1e40c D_1e40c. sn F_1e410 D_1e410. sn F_1e414 D_1e414.
    stepiv F_1e418 D_1e418 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
    stepb_tk F_1e41c D_1e41c ltac:(condZ).
    stepb_ft F_1e4d8 D_1e4d8 ltac:(condZ).
    sn F_1e4dc D_1e4dc.
    zv F_1e4e0 D_1e4e0 (Z_to_bv 64 (s - 120)). zv F_1e4e4 D_1e4e4 (Z_to_bv 64 (s - 124)). zv F_1e4e8 D_1e4e8 (Z_to_bv 64 (s - 128)).
    sn F_1e4ec D_1e4ec.
    zand F_1636c D_1636c andi_3 SL120.
    stepb_ft F_16370 D_16370 ltac:(condZ).
    stepb_ft F_16374 D_16374 ltac:(condR).
    stepST F_16378 D_16378 (Z_to_bv 64 (s - 120)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    zand F_1637c D_1637c andi_3 SL124.
    stepb_ft F_16380 D_16380 ltac:(condZ).
    stepb_ft F_16384 D_16384 ltac:(condR).
    stepST F_16388 D_16388 (Z_to_bv 64 (s - 124)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    zand F_1638c D_1638c andi_3 SL128.
    stepb_ft F_16390 D_16390 ltac:(condZ).
    stepb_ft F_16394 D_16394 ltac:(condR).
    stepST F_16398 D_16398 (Z_to_bv 64 (s - 128)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    stepb_ft F_1639c D_1639c ltac:(condZ).
    zand F_163a0 D_163a0 andi_7 ALs8.
    stepb_ft F_163a4 D_163a4 ltac:(condZ).
    sn F_163a8 D_163a8.
    stepb_ft F_163ac D_163ac ltac:(condR).
    stepLD F_163b0 D_163b0 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs)) ltac:(addr_norm; rewrite ?Z.add_0_r; repeat rdn_peel1; exact (PIX_rd_w SEGS _ _ _ PXs)) ltac:(apply lez4; lia).
    rewrite (v_lw_small (p_w vs)) by lia.
    stepST F_163b4 D_163b4 (Z_to_bv 64 (s - 120)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
    stepb_ft F_163b8 D_163b8 ltac:(condZ).
    sn F_163bc D_163bc.
    stepb_ft F_163c0 D_163c0 ltac:(condR).
    stepLD F_163c4 D_163c4 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_h SEGS _ _ _ PXs)) ltac:(apply lez4; lia).
    rewrite (v_lw_small (p_h vs)) by lia.
    stepST F_163c8 D_163c8 (Z_to_bv 64 (s - 124)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
    stepb_ft F_163cc D_163cc ltac:(condZ).
    sn F_163d0 D_163d0.
    stepb_ft F_163d4 D_163d4 ltac:(condR).
    stepLD F_163d8 D_163d8 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_d SEGS _ _ _ PXs)) ltac:(apply lez4; lia).
    rewrite (v_lw_small (p_d vs)) by lia.
    stepST F_163dc D_163dc (Z_to_bv 64 (s - 128)) (Z_to_bv 64 (p_d vs)) ltac:(sok_in SOK).
    sn F_163e0 D_163e0.
    stepret F_163e4 D_163e4 (0x1e5ec : word) ltac:(bveq).
    stepLD F_1e4f0 D_1e4f0 (word_to_le_bytes 4 (Z_to_bv 64 (p_d vd))) (Z_to_bv 64 (p_d vd)) ltac:(addr_norm; repeat rdn_peel1; exact Rd) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia).
    rewrite (v_lw_small (p_d vd)) by lia.
    stepLD F_1e4f4 D_1e4f4 (word_to_le_bytes 4 (Z_to_bv 64 (p_d vs))) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_d vs)))); zlen; unorm; lia) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia).
    rewrite (v_lw_small (p_d vs)) by lia.
    stepb_ft F_1e4f8 D_1e4f8 ltac:(rewrite Edd; condZ).
    sn F_1e4fc D_1e4fc. sn F_1e500 D_1e500.
    stepb_ft F_17180 D_17180 ltac:(condZ).
    zand F_17184 D_17184 andi_7 ALd8.
    stepb_ft F_17188 D_17188 ltac:(condR).
    stepLD F_1718c D_1718c (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
    stepret F_17190 D_17190 (0x1e600 : word) ltac:(bveq).
    stepLD F_1e504 D_1e504 (word_to_le_bytes 4 (Z_to_bv 64 (p_w vd))) (Z_to_bv 64 (p_w vd)) ltac:(addr_norm; repeat rdn_peel1; exact Rw) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia).
    rewrite (v_lw_small (p_w vd)) by lia.
    stepST F_1e508 D_1e508 (Z_to_bv 64 (s - 136)) (Z_to_bv 64 (p_w vd)) ltac:(sok_in SOK).
    stepLD F_1e50c D_1e50c (word_to_le_bytes 4 (Z_to_bv 64 (p_h vd))) (Z_to_bv 64 (p_h vd)) ltac:(addr_norm; repeat rdn_peel1; exact Rh) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia).
    rewrite (v_lw_small (p_h vd)) by lia.
    stepST F_1e510 D_1e510 (Z_to_bv 64 (s - 144)) (Z_to_bv 64 (p_h vd)) ltac:(sok_in SOK).
    stepLD F_1e514 D_1e514 (word_to_le_bytes 4 (Z_to_bv 64 (p_d vd))) (Z_to_bv 64 (p_d vd)) ltac:(addr_norm; repeat rdn_peel1; exact Rd) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia).
    rewrite (v_lw_small (p_d vd)) by lia.
    stepST F_1e518 D_1e518 (Z_to_bv 64 (s - 152)) (Z_to_bv 64 (p_d vd)) ltac:(sok_in SOK).
    stepST F_1e51c D_1e51c (Z_to_bv 64 (s - 160)) (Z_to_bv 64 (p_data vd)) ltac:(sok_in SOK).
    sn F_1e520 D_1e520. sn F_1e524 D_1e524.
    stepb_ft F_16014 D_16014 ltac:(condZ).
    zand F_16018 D_16018 andi_7 ALd8.
    stepb_ft F_1601c D_1601c ltac:(condR).
    stepLD F_16020 D_16020 (Z_to_le_bytes 4 (p_wpl vd)) (Z_to_bv 64 (p_wpl vd)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_wpl SEGS _ _ _ PX)) ltac:(apply lez4; lia).
    rewrite (v_lw_small (p_wpl vd)) by lia.
    stepret F_16024 D_16024 (0x1e624 : word) ltac:(bveq).
    sn F_1e528 D_1e528. sn F_1e52c D_1e52c. sn F_1e530 D_1e530.
    stepb_ft F_17180 D_17180 ltac:(condZ).
    zand F_17184 D_17184 andi_7 ALs8.
    stepb_ft F_17188 D_17188 ltac:(condR).
    stepLD F_1718c D_1718c (Z_to_le_bytes 8 (p_data vs)) (Z_to_bv 64 (p_data vs)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_data SEGS _ _ _ PXs)) ltac:(apply lez8; lia).
    stepret F_17190 D_17190 (0x1e630 : word) ltac:(bveq).
    stepLD F_1e534 D_1e534 (word_to_le_bytes 4 (Z_to_bv 64 (p_w vs))) (Z_to_bv 64 (p_w vs)) ltac:(addr_norm; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_w vs)))); zlen; unorm; lia) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia).
    rewrite (v_lw_small (p_w vs)) by lia.
    stepLD F_1e538 D_1e538 (word_to_le_bytes 4 (Z_to_bv 64 (p_h vs))) (Z_to_bv 64 (p_h vs)) ltac:(addr_norm; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_h vs)))); zlen; unorm; lia) ltac:(apply bytes_le_to_Z_4; rewrite u_Z2bv by lia; lia).
    rewrite (v_lw_small (p_h vs)) by lia.
    sn F_1e53c D_1e53c. sn F_1e540 D_1e540. sn F_1e544 D_1e544.
    stepb_ft F_16014 D_16014 ltac:(condZ).
    zand F_16018 D_16018 andi_7 ALs8.
    stepb_ft F_1601c D_1601c ltac:(condR).
    stepLD F_16020 D_16020 (Z_to_le_bytes 4 (p_wpl vs)) (Z_to_bv 64 (p_wpl vs)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_wpl SEGS _ _ _ PXs)) ltac:(apply lez4; lia).
    rewrite (v_lw_small (p_wpl vs)) by lia.
    stepret F_16024 D_16024 (0x1e644 : word) ltac:(bveq).
    stepST F_1e548 D_1e548 (Z_to_bv 64 (s - 192)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
    stepST F_1e54c D_1e54c (Z_to_bv 64 (s - 184)) (Z_to_bv 64 (p_wpl vs)) ltac:(sok_in SOK).
    stepST F_1e550 D_1e550 (Z_to_bv 64 (s - 176)) (Z_to_bv 64 sx) ltac:(sok_in SOK).
    stepST F_1e554 D_1e554 (Z_to_bv 64 (s - 168)) (Z_to_bv 64 sy) ltac:(sok_in SOK).
    stepST F_1e558 D_1e558 (Z_to_bv 64 (s - 224)) (Z_to_bv 64 dh) ltac:(sok_in SOK).
    stepST F_1e55c D_1e55c (Z_to_bv 64 (s - 216)) (Z_to_bv 64 12) ltac:(sok_in SOK).
    stepST F_1e560 D_1e560 (Z_to_bv 64 (s - 208)) (Z_to_bv 64 (p_data vs)) ltac:(sok_in SOK).
    stepST F_1e564 D_1e564 (Z_to_bv 64 (s - 200)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
    stepLD8 F_1e568 D_1e568 (Z_to_bv 64 (p_data vd)). stepLD8 F_1e56c D_1e56c (Z_to_bv 64 (p_w vd)).
    stepLD8 F_1e570 D_1e570 (Z_to_bv 64 (p_h vd)). stepLD8 F_1e574 D_1e574 (Z_to_bv 64 (p_d vd)).
    sn F_1e578 D_1e578. sn F_1e57c D_1e57c. sn F_1e580 D_1e580. sn F_1e584 D_1e584.
    sn F_1e588 D_1e588.
    unfold PSM. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma pr_J : forall regs m, exists regs', msteps SEGS (mkst regs (0x1e688 : word) m rom) (mkst regs' (0x1e568 : word) m rom)
  /\ regs_agree (fun r => In r []%list) regs regs'.
Proof. intros regs m. eexists. split; [sn F_1e58c D_1e58c; apply mst_refl | solve_regs_agree]. Qed.

Lemma PRM_outside : forall m s ret regs w h d (a : word), (224 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 224 <= u a < s)%Z -> PRM m s ret regs w h d a = m a.
Proof.
  intros m s ret regs w h d a Hs Hs64 Ha. unfold PRM, RLF. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
Qed.
Lemma PSM_outside : forall m s vd vs dh sx sy (a : word), (224 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 224 <= u a < s)%Z -> PSM m s vd vs dh sx sy a = m a.
Proof.
  intros m s vd vs dh sx sy a Hs Hs64 Ha. unfold PSM. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma PRM_above : forall m s ret regs w h d (a : word), (224 <= s)%Z -> (s < 2 ^ 64)%Z -> (s - 104 <= u a)%Z -> PRM m s ret regs w h d a = RLF m s ret regs a.
Proof.
  intros m s ret regs w h d a Hs Hs64 Ha. unfold PRM. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
Qed.
Lemma PSM_above : forall m s vd vs dh sx sy (a : word), (224 <= s)%Z -> (s < 2 ^ 64)%Z -> (s - 104 <= u a)%Z -> PSM m s vd vs dh sx sy a = m a.
Proof.
  intros m s vd vs dh sx sy a Hs Hs64 Ha. unfold PSM. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
Qed.
End PRSegs.

(* [comment removed for export] *)
Section RopW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma hdr_kept : forall C A m md (s' p datad nd : Z) (m1 m' : word -> option byte),
  Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some 64%Z -> live A (Z_to_bv 64 datad) = Some nd -> Z_to_bv 64 p <> Z_to_bv 64 datad ->
  (0 <= p < 2 ^ 64)%Z -> (0 <= datad < 2 ^ 64)%Z -> (0 < nd)%Z -> (s' <= c_top C)%Z ->
  (forall a : word, ~ scratch C s' a -> ~ (datad <= u a < datad + nd)%Z -> m' a = m1 a) ->
  (forall a : word, ~ win C a -> m1 a = m a) ->
  forall x : word, (p <= u x < p + 64)%Z -> m' x = m x.
Proof.
  intros C A m md s' p datad nd m1 m' CK HW Lp Ld NE Hp Hdd Hnd Hs' FT OUT x Hx.
  destruct (blk_byte C A m md (Z_to_bv 64 p) 64 x CK HW Lp ltac:(rewrite u_Z2bv by lia; lia)) as (_ & _ & _ & NW & _).
  rewrite FT; [apply OUT; exact NW | intros X; apply NW; unfold scratch, win in *; pose proof CK as [T1 T2 T3 T4 T5]; lia |].
  pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lp Ld NE) as D.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (H1 & _). pose proof (round16_ge 64 ltac:(lia)).
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (H2 & _). pose proof (round16_ge nd H2).
  rewrite !u_Z2bv in D by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma WP_range : forall C Ar A m0 m m' md (s lo : Z), Cok C -> W C A m md -> POSTM C Ar s m0 m -> sub_live Ar A ->
  (c_top C - LSTK <= lo)%Z -> (s <= c_top C)%Z -> (forall a : word, ~ (lo <= u a < s)%Z -> m' a = m a) -> mem_grows m m' ->
  W C A m' md /\ POSTM C Ar s m0 m'.
Proof.
  intros C Ar A m0 m m' md s lo CK HW PM SUB Hlo Hs OUT GR. split.
  - apply (W_local C A m md m' s CK HW Hs); [| exact GR]. intros a NE. left. unfold scratch.
    destruct (Z_lt_ge_dec (u a) lo); [exfalso; apply NE; apply OUT; lia|]. destruct (Z_lt_ge_dec (u a) s); [lia | exfalso; apply NE; apply OUT; lia].
  - eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C Ar A _ _ _ SUB). exact (POSTM_range C A m md m' lo s s CK HW OUT Hlo ltac:(lia) Hs).
Qed.
Ltac grows_chain := repeat (eapply mem_grows_trans; [| apply wbytes_grows]); apply mem_grows_refl.

(* [comment removed for export] *)
Lemma pix_facts : forall C A m md (pix : Z) (v : pixv), Cok C -> W C A m md -> PIXat m pix v -> rop_shape (p_w v) (p_h v) (p_d v) (p_wpl v) ->
  live A (Z_to_bv 64 pix) = Some 64%Z ->
  (1 <= pix)%Z /\ (pix + 64 <= alloc_top (c_vm C))%Z /\ (0 <= p_data v < 2 ^ 64)%Z /\ (1 <= p_wpl v <= 20000)%Z.
Proof.
  intros C A m md pix v CK HW PX (Hd & Hw & Hh & Ew & Hsz) Lp. pose proof PX as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [G T]. rewrite u_Z2bv in G, T by lia.
  assert (DV : dval (p_d v)) by (unfold dval; lia). pose proof (wpl_of_range (p_w v) (p_d v) ltac:(lia) DV) as R. rewrite <- Ew in R.
  pose proof (wf_data _ WF). repeat split; lia.
Qed.

Theorem pixRasterop_src_W : pixRasterop_src_contract.
Proof.
  unfold pixRasterop_src_contract.
  intros C Ar A m md regs s pixd dx dy dw dh pixs sx sy vd vs ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rsy
    PXd PXs Edd SHd SHs RCd RCs ALd ALs Lpd Lps NEpd NEps Ld Ld0 Ld00 Ls NEsd HK.
  unfold PC_pixRasterop. replace (Z_to_bv 64 0x1e488) with (0x1e488 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ROP_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  destruct (pix_facts C A m md pixd vd CK HW PXd SHd Lpd) as (Gpd & TOPpd & Hdatad & Hwpld).
  destruct (pix_facts C A m md pixs vs CK HW PXs SHs Lps) as (Gps & TOPps & Hdatas & Hwpls).
  assert (ALd8 : (pixd mod 8 = 0)%Z) by (pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lpd) as (_ & X16 & _); rewrite u_Z2bv in X16 by lia; apply mod16_mod8; exact X16).
  assert (ALs8 : (pixs mod 8 = 0)%Z) by (pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & X16 & _); rewrite u_Z2bv in X16 by lia; apply mod16_mod8; exact X16).
  pose proof SHd as (Hdd & Hwd & Hhd & _ & Hszd). pose proof SHs as (_ & Hws & Hhs & _ & _).
  destruct RCd as (Hdx0 & Hdy0 & Hdw1 & Hdh1 & Hdxw & Hdyh). pose proof RCs as (Hsx0 & Hsy0 & _ & _ & Hsxw & Hsyh).
  set (nd := (4 * (p_wpl vd * p_h vd))%Z) in *.
  assert (Hnd : (0 < nd)%Z) by (subst nd; clear - Hwpld Hhd; nia).
  (* [comment removed for export] *)
  destruct (pr_A al_rom regs m s pixd 12 vd ret (Z_to_bv 64 sy) ltac:(lia) Hs16 ALd8 ltac:(lia) ltac:(lia) ltac:(lia) PXd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 224) 224 CK HW ltac:(lia) ltac:(cbn; lia)) Rsy H2 H1 H10 H15)
    as (r1 & RUN1 & Q2 & Q19 & Q20 & Q21 & Q25 & Q22 & Q27 & Q18 & Q9 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := PRM m s ret regs (p_w vd) (p_h vd) (p_d vd)).
  assert (WP1 : W C A M1 md /\ POSTM C Ar s m M1)
    by (apply (WP_range C Ar A m m M1 md s (s - 224) CK HW (POSTM_refl _ _ _ _) SUB); [lia | lia | intros a Ha; subst M1; apply PRM_outside; lia | subst M1; unfold PRM, RLF; grows_chain]).
  destruct WP1 as [HW1 PM1].
  assert (OUT1 : forall a : word, ~ (s - 224 <= u a < s)%Z -> M1 a = m a) by (intros a Ha; subst M1; apply PRM_outside; lia).
  assert (PXd1 : PIXat M1 pixd vd) by (apply (PIXat_frame m); [exact PXd | intros x Hx; apply OUT1; lia]).
  assert (PXs1 : PIXat M1 pixs vs) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  assert (Rw1 : rdn SEGS M1 (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w vd))))
    by (subst M1; unfold PRM; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_w vd)))); zlen; unorm; lia).
  assert (Rh1 : rdn SEGS M1 (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_h vd))))
    by (subst M1; unfold PRM; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_h vd)))); zlen; unorm; lia).
  assert (Rd1 : rdn SEGS M1 (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_d vd))))
    by (subst M1; unfold PRM; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_d vd)))); zlen; unorm; lia).
  pose proof (rlcells_RLF m s ret regs ltac:(lia) ltac:(lia)) as CE0.
  assert (CE1 : rlcells M1 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { apply (rlcells_frame (RLF m s ret regs) M1 s); [lia | lia | exact CE0 |]. intros x Hx. subst M1. apply PRM_above; lia. }
  (* [comment removed for export] *)
  destruct (pr_Bs al_rom r1 M1 s pixd pixs dx dy dw dh sx sy vd vs ltac:(lia) Hs16 ALd8 ALs8 ltac:(lia) ltac:(lia) ltac:(lia) PXd1 ltac:(lia) ltac:(lia) PXs1 Edd
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hdatad ltac:(lia) ltac:(lia) ltac:(lia) Hdatas
              (W_sok_win C A M1 md (s - 224) 108 CK HW1 ltac:(lia) ltac:(cbn; lia)) Rw1 Rh1 Rd1
              Q2 Q19 Q20 ltac:(rewrite Q25; exact H16) ltac:(rewrite Q27; exact H14) ltac:(rewrite Q18; exact H11) ltac:(rewrite Q9; exact H12)
              ltac:(rewrite Q8; exact H13) ltac:(rewrite Q22; exact H17) Q21)
    as (r2 & RUN2 & P2 & P1 & P10 & P11 & P12 & P13 & P14 & P15 & P16' & P17 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  set (M2 := PSM M1 s vd vs dh sx sy).
  assert (WP2 : W C A M2 md /\ POSTM C Ar s m M2)
    by (apply (WP_range C Ar A m M1 M2 md s (s - 224) CK HW1 PM1 SUB); [lia | lia | intros a Ha; subst M2; apply PSM_outside; lia | subst M2; unfold PSM; clearbody M1; grows_chain]).
  destruct WP2 as [HW2 PM2].
  assert (OUT2 : forall a : word, ~ (s - 224 <= u a < s)%Z -> M2 a = m a) by (intros a Ha; subst M2; rewrite PSM_outside by lia; apply OUT1; exact Ha).
  assert (CE2 : rlcells M2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { apply (rlcells_frame M1 M2 s); [lia | lia | exact CE1 |]. intros x Hx. subst M2. apply PSM_above; lia. }
  (* [comment removed for export] *)
  replace (0x1efe8 : word) with (Z_to_bv 64 PC_rasteropLow) by (apply bv_eq; reflexivity).
  apply (V10LeptRopLow.rasteropLow_W C Ar A M2 md r2 (s - 224)%Z (p_data vd) (p_w vd) (p_h vd) (p_d vd) (p_wpl vd) dx dy dw dh (p_data vs) (p_w vs) (p_h vs) (p_wpl vs) sx sy
           (Z_to_bv 64 0x1e688) S CK HW2 SUB P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ROPLOW_STACK; lia) ltac:(lia) P1
           ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 P13 P14 P15 P16' P17).
  1-8: repeat match goal with |- context [Z_to_bv 64 (?b - 224 + ?k)%Z] => let c := eval cbv in (224 - k)%Z in replace (b - 224 + k)%Z with (b - c)%Z by lia end;
       subst M2; unfold PSM; rdn_chain.
  - exact Hdatad. - exact Hdatas. - exact SHd. - rewrite <- Edd. exact SHs.
  - repeat split; lia. - exact RCs. - exact ALd. - exact ALs.
  - exact Ld. - exact Ld0. - exact Ld00. - exact Ls. - exact NEsd.
  - intros m3 r3 HW3 CS3 PM3 FT3.
    replace (Z_to_bv 64 0x1e688) with (0x1e688 : word) by (apply bv_eq; reflexivity).
    destruct (pr_J al_rom r3 m3) as (r4 & RUN4 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
    destruct (blk_range C A m md (Z_to_bv 64 (p_data vd)) nd CK HW Ld Hnd) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
    assert (CE3 : rlcells m3 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
    { apply (rlcells_frame M2 m3 s); [lia | lia | exact CE2 |]. intros x Hx. apply FT3; [unfold scratch; lia | lia]. }
    destruct (pr_C al_rom r4 m3 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ltac:(lia) ltac:(lia) Hret CE3 ltac:(csr; reflexivity))
      as (r5 & RUN5 & Z2 & Z1 & Z10 & Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
    apply (HK m3 r5 HW3).
    + apply cs_kept_intro; first [ rewrite Z2; symmetry; exact H2 | assumption | csr; reflexivity ].
    + eapply POSTM_trans; [exact PM2 | eapply POSTM_mono; [| exact PM3]; lia].
    + apply (PIXat_frame m); [exact PXd|].
      apply (hdr_kept C A m md (s - 224) pixd (p_data vd) nd M2 m3 CK HW Lpd Ld NEpd ltac:(lia) Hdatad Hnd ltac:(lia) FT3).
      intros a NW. apply OUT2. intros X. apply NW. unfold win. lia.
    + apply (PIXat_frame m); [exact PXs|].
      apply (hdr_kept C A m md (s - 224) pixs (p_data vd) nd M2 m3 CK HW Lps Ld NEps ltac:(lia) Hdatad Hnd ltac:(lia) FT3).
      intros a NW. apply OUT2. intros X. apply NW. unfold win. lia.
    + intros a NS ND. transitivity (M2 a).
      * apply FT3; [intros X; apply NS; unfold scratch in *; lia | exact ND].
      * apply OUT2. intros X. apply NS. unfold scratch. lia.
    + exact Z10.
Qed.

Theorem pixRasterop_uni_W : rasteropUniLow_contract -> pixRasterop_uni_contract.
Proof.
  intros UNI. unfold pixRasterop_uni_contract.
  intros C Ar A m md regs s pixd dx dy dw dh op v syw ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 Rsy
    PX SH RC Hop Lp NEp Ld Ld0 Ld00 HK.
  unfold PC_pixRasterop. replace (Z_to_bv 64 0x1e488) with (0x1e488 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ROP_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  destruct (pix_facts C A m md pixd v CK HW PX SH Lp) as (Gp & TOPp & Hdata & Hwpl).
  assert (ALd8 : (pixd mod 8 = 0)%Z) by (pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & X16 & _); rewrite u_Z2bv in X16 by lia; apply mod16_mod8; exact X16).
  pose proof SH as (Hd & Hw & Hh & _ & Hsz).
  set (nd := (4 * (p_wpl v * p_h v))%Z) in *.
  assert (Hnd : (0 < nd)%Z) by (subst nd; clear - Hwpl Hh; nia).
  destruct (pr_A al_rom regs m s pixd op v ret syw ltac:(lia) Hs16 ALd8 ltac:(lia) ltac:(lia) ltac:(lia) PX ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 224) 224 CK HW ltac:(lia) ltac:(cbn; lia)) Rsy H2 H1 H10 H15)
    as (r1 & RUN1 & Q2 & Q19 & Q20 & Q21 & Q25 & Q22 & Q27 & Q18 & Q9 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := PRM m s ret regs (p_w v) (p_h v) (p_d v)).
  assert (WP1 : W C A M1 md /\ POSTM C Ar s m M1)
    by (apply (WP_range C Ar A m m M1 md s (s - 224) CK HW (POSTM_refl _ _ _ _) SUB); [lia | lia | intros a Ha; subst M1; apply PRM_outside; lia | subst M1; unfold PRM, RLF; grows_chain]).
  destruct WP1 as [HW1 PM1].
  assert (OUT1 : forall a : word, ~ (s - 224 <= u a < s)%Z -> M1 a = m a) by (intros a Ha; subst M1; apply PRM_outside; lia).
  assert (PX1 : PIXat M1 pixd v) by (apply (PIXat_frame m); [exact PX | intros x Hx; apply OUT1; lia]).
  assert (Rw1 : rdn SEGS M1 (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))))
    by (subst M1; unfold PRM; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_w v)))); zlen; unorm; lia).
  assert (Rh1 : rdn SEGS M1 (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_h v))))
    by (subst M1; unfold PRM; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_h v)))); zlen; unorm; lia).
  assert (Rd1 : rdn SEGS M1 (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_d v))))
    by (subst M1; unfold PRM; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_d v)))); zlen; unorm; lia).
  pose proof (rlcells_RLF m s ret regs ltac:(lia) ltac:(lia)) as CE0.
  assert (CE1 : rlcells M1 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { apply (rlcells_frame (RLF m s ret regs) M1 s); [lia | lia | exact CE0 |]. intros x Hx. subst M1. apply PRM_above; lia. }
  destruct (pr_Bu al_rom r1 M1 s pixd op dx dy dw dh v ltac:(lia) Hs16 ALd8 ltac:(lia) ltac:(lia) ltac:(lia) PX1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hdata Hop
              (W_sok_win C A M1 md (s - 224) 16 CK HW1 ltac:(lia) ltac:(cbn; lia)) Rw1 Rh1 Rd1
              Q2 Q19 Q20 ltac:(rewrite Q27; exact H14) ltac:(rewrite Q18; exact H11) ltac:(rewrite Q9; exact H12) ltac:(rewrite Q8; exact H13))
    as (r2 & RUN2 & P2 & P1 & P10 & P11 & P12 & P13 & P14 & P15 & P16' & P17 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  set (M2 := wbytes (wbytes M1 _ _) _ _).
  assert (WP2 : W C A M2 md /\ POSTM C Ar s m M2) by (subst M2; wp_win CK).
  destruct WP2 as [HW2 PM2].
  assert (OUT2 : forall a : word, ~ (s - 224 <= u a < s)%Z -> M2 a = m a).
  { intros a Ha. subst M2. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). apply OUT1. exact Ha. }
  assert (CE2 : rlcells M2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { apply (rlcells_frame M1 M2 s); [lia | lia | exact CE1 |]. intros x Hx. subst M2.
    rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity. }
  replace (0x1e724 : word) with (Z_to_bv 64 PC_rasteropUniLow) by (apply bv_eq; reflexivity).
  apply (UNI C Ar A M2 md r2 (s - 224)%Z (p_data v) (p_w v) (p_h v) (p_d v) (p_wpl v) dx dy dw dh op (Z_to_bv 64 0x1e568) S CK HW2 SUB P2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ROPUNI_STACK; lia) ltac:(lia) P1
           ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 P13 P14 P15 P16' P17).
  1-2: repeat match goal with |- context [Z_to_bv 64 (?b - 224 + ?k)%Z] => let c := eval cbv in (224 - k)%Z in replace (b - 224 + k)%Z with (b - c)%Z by lia end;
       subst M2; rdn_chain.
  - exact Hdata. - exact SH. - exact RC. - exact Hop. - exact Ld. - exact Ld0. - exact Ld00.
  - intros m3 r3 HW3 CS3 PM3 FT3.
    replace (Z_to_bv 64 0x1e568) with (0x1e568 : word) by (apply bv_eq; reflexivity).
    destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) nd CK HW Ld Hnd) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
    assert (CE3 : rlcells m3 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
    { apply (rlcells_frame M2 m3 s); [lia | lia | exact CE2 |]. intros x Hx. apply FT3; [unfold scratch; lia | lia]. }
    destruct (pr_C al_rom r3 m3 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ltac:(lia) ltac:(lia) Hret CE3 ltac:(csr; reflexivity))
      as (r5 & RUN5 & Z2 & Z1 & Z10 & Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
    apply (HK m3 r5 HW3).
    + apply cs_kept_intro; first [ rewrite Z2; symmetry; exact H2 | assumption | csr; reflexivity ].
    + eapply POSTM_trans; [exact PM2 | eapply POSTM_mono; [| exact PM3]; lia].
    + apply (PIXat_frame m); [exact PX|].
      apply (hdr_kept C A m md (s - 224) pixd (p_data v) nd M2 m3 CK HW Lp Ld NEp ltac:(lia) Hdata Hnd ltac:(lia) FT3).
      intros a NW. apply OUT2. intros X. apply NW. unfold win. lia.
    + intros a NS ND. transitivity (M2 a).
      * apply FT3; [intros X; apply NS; unfold scratch in *; lia | exact ND].
      * apply OUT2. intros X. apply NS. unfold scratch. lia.
    + exact Z10.
Qed.

End RopW.



(* [comment removed for export] *)
Section RopClosed.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.

Theorem rasteropUniLow_closed : rasteropUniLow_contract.
Proof. exact V10LeptRopUni.rasteropUniLow_W. Qed.

Theorem pixRasterop_uni_closed : pixRasterop_uni_contract.
Proof. exact (pixRasterop_uni_W rasteropUniLow_closed). Qed.

End RopClosed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
