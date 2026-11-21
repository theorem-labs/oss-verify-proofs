(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (11 recorded proofs replaced by written proofs (ablk_img, ablk_top, ablk_kend and 8 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ABase () := "C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3appc59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00c59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW5ABase8ablk_linC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C45stdpp;list_basics4list;list_filterC35stdpp4base6FilterC46Stdlib5Lists4List8flat_mapC59OSSVerify5KrLib4LibA6Shadow4KENDC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subc59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW5ABase3KLSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow7app_blkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic3notK46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib4LibA6Shadow8shad_divC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow6HSH_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow6HSH_HIC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib5BothW5ABase4wclrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indI47Corelib5Lists7ListDef6Forall00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00i59OSSVerify5KrLib5BothW5ABase6uchain00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib5BothW5ABase6uchain01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib5Lists4List9nth_errorC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegk59OSSVerify5KrLib5BothW5ABase6uchain02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib5Arith8PeanoNat3Nat4predC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegk59OSSVerify5KrLib5BothW5ABase6uchain03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW5ABase:uchain_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_lt".
Import ListNotations.
Open Scope Z_scope.

Notation amem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AMALLOC_SYM : Z := 0x5242c.    (* [comment removed for export] *)
Definition AFREE_SYM : Z := 0x52428.      (* [comment removed for export] *)
Definition AMALLOC_PC : Z := 0x526c8.     (* [comment removed for export] *)
Definition AFREE_PC : Z := 0x52568.       (* [comment removed for export] *)
Definition AMALLOC_STACK : Z := 4096.     (* [comment removed for export] *)
Definition AFREE_STACK : Z := 4096.
Definition ATP : Z := 0x5ed290.           (* [comment removed for export] *)
Definition AERRNO : Z := ATP - 164.       (* [comment removed for export] *)
Definition AREQMAX : Z := 2^29 + 2^10.    (* [comment removed for export] *)
Definition UDEPTH : nat := 28%nat.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AIMG_LO : Z := 0x10000.
Definition AIMG_HI : Z := 0x60f000.
Definition ARELRO_LO : Z := 0xb1000.
Definition ARELRO_HI : Z := 0xb3000.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition KLS : Z := 0x7fff7000.
Definition sclr (a n : Z) : Prop := a + n <= KLS \/ 0x10007fff8000 <= a.
Definition iclr (a n : Z) : Prop := 4096 <= a /\ (a + n <= AIMG_LO \/ AIMG_HI <= a).
Section ABLK. Context {rc : runConstT}.
Definition ablk (lo hi : Z) : Prop := (AIMG_HI <= lo /\ hi <= KLS) \/ (0x10007fff8000 <= lo /\ hi <= ATOP).

Lemma ablk_sub : forall lo hi lo' hi', ablk lo hi -> lo <= lo' -> hi' <= hi -> ablk lo' hi'.
Proof. intros lo hi lo' hi' H A B. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
(* [comment removed for export] *)
Lemma ablk_lin : forall lo hi, ablk lo hi -> AIMG_HI <= lo /\ 0 <= lo /\ hi <= ATOP /\ hi + 8 <= 2^47.
Proof. intros lo hi H. atop_facts. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
Lemma ablk_img : forall lo hi, ablk lo hi -> AIMG_HI <= lo.
Proof. intros lo hi H. apply ablk_lin in H. tauto. Qed.
Lemma ablk_top : forall lo hi, ablk lo hi -> hi <= ATOP.
Proof. intros lo hi H. apply ablk_lin in H. tauto. Qed.
Lemma ablk_kend : forall lo hi, ablk lo hi -> hi + 8 <= KEND.
Proof. intros lo hi H. apply ablk_lin in H. unfold KEND. tauto. Qed.
Lemma ablk_sclr : forall lo hi, ablk lo hi -> sclr lo (hi - lo).
Proof. intros lo hi H. unfold ablk, sclr in *. lia. Qed.
Lemma ablk_iclr : forall lo hi, ablk lo hi -> iclr lo (hi - lo).
Proof. intros lo hi H. unfold ablk, iclr, AIMG_HI, AIMG_LO in *. lia. Qed.
(* [comment removed for export] *)
Lemma ablk_app_blk : forall lo hi, ablk lo hi -> lo <= hi -> app_blk lo hi.
Proof. intros lo hi H LE. atop_facts. unfold ablk, app_blk, AIMG_HI, KLS, KLOW, KHIGH, KEND in *. lia. Qed.
(* [comment removed for export] *)
Lemma ablk_clear_band : forall lo hi a, ablk lo hi -> KLS <= a < 0x10007fff8000 -> ~ (lo <= a < hi).
Proof. intros lo hi a H B. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
Lemma ablk_disj_band : forall lo hi, ablk lo hi -> hi <= KLS \/ 0x10007fff8000 <= lo.
Proof. intros lo hi H. unfold ablk in H. lia. Qed.
(* [comment removed for export] *)
Lemma ablk_shad : forall lo hi, ablk lo hi -> lo <= hi ->
  (shad AIMG_HI <= shad lo /\ shad hi <= shad KLS) \/ (HSH_LO <= shad lo /\ shad hi < HSH_HI).
Proof.
  intros lo hi H LE. atop_facts. rewrite !shad_div. unfold ablk, AIMG_HI, KLS, ASHOFF, HSH_LO, HSH_HI in *.
  Z.div_mod_to_equations; lia.
Qed.
Lemma ablk_shad_lin : forall lo hi, ablk lo hi -> lo <= hi -> shad AIMG_HI <= shad lo /\ shad hi < HSH_HI.
Proof.
  intros lo hi H LE. atop_facts. rewrite !shad_div. unfold ablk, AIMG_HI, KLS, ASHOFF, HSH_HI in *.
  Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Lemma ablk_shad_disj : forall lo hi, ablk lo hi -> lo <= hi -> hi <= shad lo \/ shad (hi + 7) + 1 <= lo.
Proof.
  intros lo hi H LE. atop_facts. rewrite !shad_div. unfold ablk, AIMG_HI, KLS, ASHOFF in *.
  Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Definition wclr (iv : Z * Z) : Prop := AIMG_HI <= fst iv /\ sclr (fst iv) (snd iv - fst iv).
Lemma wclr_high : forall lo hi, 0x10007fff8000 <= lo -> wclr (lo, hi).
Proof. intros lo hi H. unfold wclr, sclr, AIMG_HI. cbn [fst snd]. lia. Qed.
Lemma wclr_ablk : forall lo hi a b, ablk lo hi -> lo <= a -> b <= hi -> wclr (a, b).
Proof. intros lo hi a b H A B. unfold wclr, sclr, ablk, AIMG_HI, KLS in *. cbn [fst snd]. lia. Qed.
Lemma wclr_outside_band : forall W x, Forall wclr W -> KLS <= x < 0x10007fff8000 -> outside W x.
Proof.
  intros W x FW Hx. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l H1 H2]; subst.
  unfold wclr, sclr in H1. cbn [fst snd] in H1. cbn. split; [lia| apply IH; exact H2].
Qed.
Lemma wclr_outside_img : forall W x, Forall wclr W -> x < AIMG_HI -> outside W x.
Proof.
  intros W x FW Hx. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l H1 H2]; subst.
  unfold wclr in H1. cbn [fst snd] in H1. cbn. split; [lia| apply IH; exact H2].
Qed.
Lemma wclr_disjoint_band : forall W a n, Forall wclr W -> KLS <= a -> a + n <= 0x10007fff8000 -> disjoint_from W a n.
Proof.
  intros W a n FW H1 H2. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l F1 F2]; subst.
  unfold wclr, sclr in F1. cbn [fst snd] in F1. cbn. split; [lia| apply IH; exact F2].
Qed.
Lemma wclr_disjoint_img : forall W a n, Forall wclr W -> a + n <= AIMG_HI -> disjoint_from W a n.
Proof.
  intros W a n FW H. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l F1 F2]; subst.
  unfold wclr in F1. cbn [fst snd] in F1. cbn. split; [lia| apply IH; exact F2].
Qed.
(* [comment removed for export] *)
Lemma shad_in_band : forall a, 0 <= a < 2^47 -> KLS + 4096 <= shad a < 0x10007fff8000.
Proof. intros a H. rewrite shad_div. unfold KLS, ASHOFF. Z.div_mod_to_equations. lia. Qed.
End ABLK.

(* [comment removed for export] *)
Definition artcells (m : amem) : Prop :=
     rw_cells bsegs m 0xb2108 [C8 (Z_to_bv 64 0x149da0)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb2118 [C8 (Z_to_bv 64 0x14be28); C8 (Z_to_bv 64 0xb7af8); C8 (Z_to_bv 64 0xba2f8);
                                C8 (Z_to_bv 64 0xbafe8); C8 (Z_to_bv 64 0xbaff0); C8 (Z_to_bv 64 0xbafe0)]   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb2c90 [C8 (Z_to_bv 64 0xbafd9)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb3fa0 [C8 (Z_to_bv 64 0xab458); C8 (Z_to_bv 64 0xab85c)]         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xba2f8 [C8 (Z_to_bv 64 0x7fff8000)]                                 (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xba300 [C4 (Z_to_bv 64 1)]                                          (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbafd8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbafe0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb9b5c [C1 (Z_to_bv 8 1)]                                           (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbaffc [C4 (Z_to_bv 64 30)]                                         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x149da0 [C8 (Z_to_bv 64 4096)]                                       (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x14be48 [C8 (Z_to_bv 64 0x1e00010000)]                               (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x14bea0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb3e98 [C8 (Z_to_bv 64 0xaada8); C8 (Z_to_bv 64 0xa7c98)]         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb3f50 [C8 (Z_to_bv 64 0xabce4)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb3e78 [C8 (Z_to_bv 64 0xb0b5c)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb3e80 [C8 (Z_to_bv 64 0xa7a10)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb3f50 [C8 (Z_to_bv 64 0xabce4)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb3e68 [C8 (Z_to_bv 64 0xab35c)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x14be78 [C8 (Z_to_bv 64 4294967296)]                                 (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x14bf20 [C8 (Z_to_bv 64 0x101010101010101)]                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb7b58 [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x149d98 [C4 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Definition in_ranges (l : list (Z * Z)) (a : Z) : Prop := exists iv, In iv l /\ fst iv <= a < snd iv.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AINSTANCE : Z := 0xb6c98.     (* [comment removed for export] *)
Definition AFLAGS : Z := 0xb7af8.        (* [comment removed for export] *)
Definition ACFLAGS : Z := 0x14be28.       (* [comment removed for export] *)
Definition AINITED : Z := 0xbafd8.       (* [comment removed for export] *)
Definition ACANPOISON : Z := 0xb9b5c.    (* [comment removed for export] *)
Definition AMCTXSZ : Z := 0xbaffc.       (* [comment removed for export] *)
Definition ASHBASE : Z := 0xba2f8.       (* [comment removed for export] *)
Definition AMIDBEG : Z := 0xbafe8.       (* [comment removed for export] *)
Definition AMIDEND : Z := 0xbaff0.       (* [comment removed for export] *)
Definition AHIGHEND : Z := 0xbafe0.      (* [comment removed for export] *)
Definition AREALMEMSET : Z := 0xb3fa8.   (* [comment removed for export] *)
Definition AMEMSET : Z := 0xab85c.
Definition APGSZ : Z := 0x149da0.         (* [comment removed for export] *)
Definition ATSDI : Z := 0xb9b60.         (* [comment removed for export] *)
Definition ATSDK : Z := 0xb9b64.         (* [comment removed for export] *)
Definition ATP88 : Z := 0x5ed238.         (* [comment removed for export] *)
Definition ATSD : Z := 0x60e638.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition GOT_PGSZ : Z := 0xb2108.      (* [comment removed for export] *)
Definition GOT_CFLAGS : Z := 0xb2118.    (* [comment removed for export] *)
Definition GOT_FLAGS : Z := 0xb2120.     (* [comment removed for export] *)
Definition GOT_SHBASE : Z := 0xb2128.    (* [comment removed for export] *)
Definition GOT_MIDBEG : Z := 0xb2130.    (* [comment removed for export] *)
Definition GOT_MIDEND : Z := 0xb2138.    (* [comment removed for export] *)
Definition GOT_HIGHEND : Z := 0xb2140.   (* [comment removed for export] *)
Definition GOT_REALMEMSET : Z := 0xb2148. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Record alayout := mkALayout {
  al_V : nat -> Z;            (* [comment removed for export] *)
  al_w : bool;                (* [comment removed for export] *)
  al_U : list (list Z)        (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition al_sp0 (L : alayout) : Z := 32768 * al_V L 0%nat + 16 * al_V L 6%nat.       (* [comment removed for export] *)
Definition al_top (L : alayout) : Z := page_round_up_Z (al_sp0 L - 0xa0).              (* [comment removed for export] *)
Definition al_bot (L : alayout) : Z := al_top L - 0x800000.                             (* [comment removed for export] *)
Definition al_t (L : alayout) : Z := 4096 * al_V L 240%nat.                             (* [comment removed for export] *)
Definition al_ctx (L : alayout) : Z := 4096 * al_V L 241%nat.                           (* [comment removed for export] *)
Definition al_space_beg (L : alayout) : Z := 4096 * (al_V L 221%nat - al_V L 222%nat) + 0x10000.
Definition al_ptr_array (L : alayout) : Z := 4096 * al_V L 239%nat.
Definition al_nodes (L : alayout) : Z := 4096 * al_V L 485%nat.                         (* [comment removed for export] *)
Definition al_store (L : alayout) : Z := 4096 * al_V L 486%nat.                         (* [comment removed for export] *)
Definition al_fake (L : alayout) : Z := 4096 * al_V L 406%nat.                          (* [comment removed for export] *)
Definition AUMAX : Z := 4096.                                                           (* [comment removed for export] *)

Inductive abkind := ABHeap (p : aptr) | ABFake (cls : Z).
Record ablock := mkABlock { ab_kind : abkind; ab_addr : Z; ab_size : Z }.
Notation HB p A n := (mkABlock (ABHeap p) A n).

Definition in_block (LB : list ablock) (a : Z) : Prop :=
  exists b, In b LB /\ ab_addr b <= a < ab_addr b + ab_size b.
Definition in_fake (LB : list ablock) (a : Z) : Prop :=
  exists cls A n, In (mkABlock (ABFake cls) A n) LB /\ A <= a < A + n.

Definition abkind_eqb (k k' : abkind) : bool :=
  match k, k' with
  | ABHeap p, ABHeap p' => (p =? p')%N
  | ABFake c, ABFake c' => c =? c'
  | _, _ => false
  end.
Definition lb_remove (p : aptr) (LB : list ablock) : list ablock :=
  filter (fun b => negb (abkind_eqb (ab_kind b) (ABHeap p))) LB.
(* [comment removed for export] *)
Definition hb_ids (LB : list ablock) : list aptr :=
  flat_map (fun b => match ab_kind b with ABHeap p => [p] | ABFake _ => [] end) LB.

(* [comment removed for export] *)
Definition ablock_range {rc : runConstT} (A n : Z) : Prop :=
  ablk A (A + n) /\ 0 <= n /\ A + n <= ATOP /\ A mod 16 = 0.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ablock_shadow (m : amem) (A n : Z) : Prop :=
  forall g, 0 <= g -> 8 * g < n ->
    m (wa (shad A + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? n then 0 else n - 8 * g)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive uchain (m : amem) (top pc : Z) : Z -> Z -> nat -> list Z -> Prop :=
| uc_stop : forall prev frame k,
    ~ (prev < frame /\ frame < top - 16 /\ frame mod 8 = 0 /\ (0 < k)%nat) ->
    uchain m top pc prev frame k []
| uc_lowpc : forall prev frame k fp ra,
    prev < frame -> frame < top - 16 -> frame mod 8 = 0 -> (0 < k)%nat ->
    bytes_at bsegs m (frame - 16) (le8 (Z_to_bv 64 fp)) ->
    bytes_at bsegs m (frame - 8) (le8 (Z_to_bv 64 ra)) ->
    0 <= ra < 4096 ->
    uchain m top pc prev frame k []
| uc_step : forall prev frame k fp ra tr,
    prev < frame -> frame < top - 16 -> frame mod 8 = 0 -> (0 < k)%nat ->
    bytes_at bsegs m (frame - 16) (le8 (Z_to_bv 64 fp)) ->
    bytes_at bsegs m (frame - 8) (le8 (Z_to_bv 64 ra)) ->
    4096 <= ra < 2^64 -> 0 <= fp < 2^64 ->
    uchain m top pc frame fp (if ra =? pc then k else Nat.pred k) tr ->
    uchain m top pc prev frame k ((if ra =? pc then [] else [ra]) ++ tr).

(* [comment removed for export] *)
Lemma uchain_frame : forall m m' top pc prev frame k tr,
  uchain m top pc prev frame k tr ->
  (forall a, frame - 16 <= a < top -> m' (wa a) = m (wa a)) ->
  uchain m' top pc prev frame k tr.
Proof.
  intros m m' top pc prev frame k tr H. induction H as [prev frame k Hn | prev frame k fp ra H1 H2 H3 H4 B1 B2 Hra | prev frame k fp ra tr H1 H2 H3 H4 B1 B2 Hra Hfp HC IH]; intros HM.
  - apply uc_stop. exact Hn.
  - eapply uc_lowpc; eauto.
    + destruct B1 as (X & Y & B). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
    + destruct B2 as (X & Y & B). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
  - eapply uc_step; eauto.
    + destruct B1 as (X & Y & B). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
    + destruct B2 as (X & Y & B). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
    + destruct (Z_lt_le_dec frame fp) as [LT|GE].
      * apply IH. intros a Ha. apply HM. lia.
      * (* [comment removed for export] *)
        inversion HC; subst; [apply uc_stop; assumption | exfalso; lia | exfalso; lia].
Qed.

