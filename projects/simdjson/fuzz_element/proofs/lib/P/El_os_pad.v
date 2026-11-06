(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue F_memset Pj_steps Pj_loc_defs Pj_loc_kit Pj_os_defs Pj_os_kit El_os_defs El_os_xsputn.
From OSSVerify.simdjson.fuzz_element.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Ltac br_is b tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (symmetry; tac) end; cbv_concl_iota.
Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc end.
Ltac show_reg k :=
  lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
    let v := eval cbv beta iota delta [tget] in (tget p R) in
    idtac "x" k "=" v
  end.

Lemma rw_cells_CB_prefix : forall m A (n : nat) (bs : list byte) (k : Z),
  rw_cells psegs m A [CB n bs] -> (0 <= k)%Z -> (k <= Z.of_nat n)%Z -> exists bs', rw_cells psegs m A [CB (Z.to_nat k) bs'].
Proof.
  intros m A n bs k H Hk Hn.
  destruct (rw_cells_CB_cut3 m A n bs 0 k ltac:(lia) Hk ltac:(lia) H) as (b1 & b2 & b3 & _ & X & _).
  replace (A + 0)%Z with A in X by lia. exists b2. exact X.
Qed.

Lemma ltu_ZZ : forall x y, (0 <= x < 2^64)%Z -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y mod 2^64)%Z.
Proof. intros x y Hx. rewrite bv_ltu_Z, unsigned_lit_wrap, unsigned_lit_wrap, (Z.mod_small x) by lia. reflexivity. Qed.
Lemma eqb_ZZ : forall x y, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x mod 2^64 =? y mod 2^64)%Z.
Proof. intros x y. rewrite bv_eqb_Z, !unsigned_lit_wrap. reflexivity. Qed.
Lemma lts_small : forall x y, (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y)%Z.
Proof.
  intros x y Hx Hy. rewrite bv_lts_lxor, !unsigned_lit by lia. rewrite !zb_lxor_pow2_small by lia.
  destruct (Z.ltb_spec x y), (Z.ltb_spec (x + 2^63) (y + 2^63)); lia.
Qed.

Lemma le1_Z : forall x, le1 (Z_to_bv 64 x) = [Z_to_bv 8 x].
Proof.
  intros x. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. apply bv_wrap_bv_wrap. cbv; congruence.
Qed.
Ltac sbZ := rewrite le1_Z; mem_after_store.

Definition pad_ns (L W : Z) : Z := if (L <? W)%Z then (W - L)%Z else 0%Z.
Lemma pad_ns_eq : forall L W, (0 <= L < 2^63)%Z -> (0 <= W < 2^63)%Z ->
  Z.land ((0 - Z.b2z (Z.lxor L 9223372036854775808 <? Z.lxor W 9223372036854775808)) mod 18446744073709551616)
         ((W - L) mod 18446744073709551616) = pad_ns L W.
Proof.
  intros L W HL HW. unfold pad_ns. change 9223372036854775808%Z with (2^63)%Z. rewrite !zb_lxor_pow2_small by lia.
  destruct (Z.ltb_spec L W); destruct (Z.ltb_spec (L + 2^63) (W + 2^63)); try lia; cbn [Z.b2z].
  - rewrite (Z.mod_small (W - L)) by lia. change ((0 - 1) mod 18446744073709551616)%Z with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
  - apply Z.land_0_l.
Qed.

Ltac bru b := br_is b ltac:(rewrite ?ltu_ZZ, ?eqb_ZZ by lia; cbn [negb Z.modulo Z.pow Z.pow_pos Pos.iter Z.mul];
                             first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia
                                   | apply negb_true_iff; first [apply Z.ltb_ge; lia | apply Z.eqb_neq; lia]
                                   | apply negb_false_iff; first [apply Z.ltb_lt; lia | apply Z.eqb_eq; lia]]).

Definition strnc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo D n c : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (D, D + 24)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' D [C1 (Z_to_bv 8 (2 * n))]
    /\ rw_cells psegs m' (D + 1) [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))]
    /\ rw_cells psegs m' (D + 1 + n) [C1 (Z_to_bv 8 0)]
    /\ exists rest, rw_cells psegs m' (D + 1 + n + 1) [CB (Z.to_nat (22 - n)) rest].

Lemma strnc_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo D n c : Z) (j : list byte),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z -> (0x105000 <= lo)%Z ->
  rw_cells psegs m D [CB 24 j] -> (bv_unsigned sp <= D)%Z -> (D + 24 < 2^62)%Z ->
  (1 <= n < 23)%Z -> (0 <= c < 256)%Z -> mem_inv psegs m ->
  evt psegs (strnc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo D n c m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 c) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_STRNC) fc None m (seg_rom psegs)).
Proof.
  intros until j. intros ST LO LOLO DST RD RD2 RN RC MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (D, D + 24)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.

  destruct (rw_cells_CB_cut3 m D 24 j 1 n ltac:(lia) ltac:(lia) ltac:(lia) DST) as (b1 & b2 & b3 & X1 & X2 & X3).
  change (Z.to_nat 1) with 1%nat in X1.
  replace (24 - Z.to_nat 1 - Z.to_nat n)%nat with (Z.to_nat (23 - n)) in X3 by lia.
  destruct (rw_cells_CB_cut3 m (D + 1 + n)%Z (Z.to_nat (23 - n)) b3 1 (22 - n) ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) X3) as (b4 & b5 & b6 & X4 & X5 & _).
  change (Z.to_nat 1) with 1%nat in X4. clear X3 DST.
  carve_frame 48%nat ST.
  do 10 lstep.
  bru false.
  do 4 lstep.
  bru false.
  lstep.
  lstep.
  sbZ.
  lstep.
  lstep.
  bru true.
  do 3 lstep.
  lstep.
  call_sp (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (D + 1) c n b2)%Z;
    [exact X2 | assumption | lia | lia | lia | lia |].
  rename POST into X2. rewrite (Z.mod_small c 256) in X2 by lia.
  lstep.
  set (E1 := (D + 1 + n)%Z) in *.
  lstep.
  subst E1.
  do 8 lstep.
  release_frame FR ST (bv_unsigned sp).
  replace (Z.shiftl n 1) with (2 * n)%Z in X1 by (rewrite Z.shiftl_mul_pow2; lia).
  unfold strnc_post. sys_finish. eexists; exact X5.
Qed.

Lemma land1_double : forall x, (0 <= x < 100)%Z -> Z.land (bv_unsigned (Z_to_bv 8 (2 * x))) 1 = 0%Z.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8%N) with 256%Z. rewrite Z.mod_small by lia.
  change (Z.land (2 * x) 1)%Z with (Z.land (2 * x) (Z.ones 1))%Z. rewrite Z.land_ones by lia.
  rewrite Z.pow_1_r, Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma strobj_forget : forall m D n (a z : byte) (b2 rest : list byte),
  (1 <= n < 23)%Z ->
  rw_cells psegs m D [C1 a] -> rw_cells psegs m (D + 1) [CB (Z.to_nat n) b2] ->
  rw_cells psegs m (D + 1 + n) [C1 z] -> rw_cells psegs m (D + 1 + n + 1) [CB (Z.to_nat (22 - n)) rest] ->
  exists jo, rw_cells psegs m D [CB 24 jo].
Proof.
  intros m D n a z b2 rest Hn H1 H2 H3 H4.
  assert (H12 : rw_cells psegs m D ([C1 a] ++ [CB (Z.to_nat n) b2])) by (apply Startup_glue.rw_cells_app; split; [exact H1 | exact H2]).
  assert (H123 : rw_cells psegs m D (([C1 a] ++ [CB (Z.to_nat n) b2]) ++ [C1 z])).
  { apply Startup_glue.rw_cells_app; split; [exact H12 |].
    replace (D + Z.of_nat (cells_size ([C1 a] ++ [CB (Z.to_nat n) b2])))%Z with (D + 1 + n)%Z by (cbn [cells_size csize app]; lia). exact H3. }
  assert (H1234 : rw_cells psegs m D ((([C1 a] ++ [CB (Z.to_nat n) b2]) ++ [C1 z]) ++ [CB (Z.to_nat (22 - n)) rest])).
  { apply Startup_glue.rw_cells_app; split; [exact H123 |].
    replace (D + Z.of_nat (cells_size (([C1 a] ++ [CB (Z.to_nat n) b2]) ++ [C1 z])))%Z with (D + 1 + n + 1)%Z by (cbn [cells_size csize app]; lia). exact H4. }
  destruct (rw_cells_forget psegs m D _ H1234) as [jo H].
  replace (cells_size ((([C1 a] ++ [CB (Z.to_nat n) b2]) ++ [C1 z]) ++ [CB (Z.to_nat (22 - n)) rest])) with 24%nat in H by (cbn [cells_size csize app]; lia).
  exists jo. exact H.
Qed.

Definition os_pad_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo OS flags fill : Z) (j148 j284 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 pb (pp ep : Z) dum m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OS) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (OS + 40, OS + 128); (OS + 160, OS + 168)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' OS (sb_cells pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) /\ PUTINV OS pp ep
    /\ rw_cells psegs m' (OS + 136) (ios_cellsX OS 0xcad28 flags 0 fill j148 j284).

Definition os_pad_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS OB L P W flags fill pp ep : Z) (pb : word) (dum bs j148 j284 : list byte),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 160)%Z -> (0x105000 <= lo)%Z ->
  rw_cells psegs m OS (sb_cells pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) -> PUTINV OS pp ep ->
  rw_cells psegs m (OS + 136) (ios_cellsX OS 0xcad28 flags W fill j148 j284) ->
  (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z ->
  bytes_at psegs m OB bs -> Z.of_nat (length bs) = L -> (0 <= P <= L)%Z -> (0 <= OB)%Z -> (OB + L < 2^62)%Z ->
  (OB + L <= lo \/ OS + 288 <= OB \/ (bv_unsigned sp <= OB /\ OB + L <= OS))%Z ->
  (0 <= W < 23)%Z -> (0 <= fill < 256)%Z -> (0 <= flags < 2^32)%Z ->
  rw_cells psegs m 0xcacd8 [C8 (Z_to_bv 64 0x76930); C8 (Z_to_bv 64 0x3e254); C8 (Z_to_bv 64 8)] -> mem_inv psegs m ->
  evt psegs (os_pad_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS flags fill j148 j284 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OS) (Z_to_bv 64 OB) (Z_to_bv 64 (OB + P)) (Z_to_bv 64 (OB + L))
               (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 fill) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_PAD) fc None m (seg_rom psegs)).

Section Pad.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo OS OB L P W flags fill : Z) (bs j148 j284 : list byte) (m0 : word -> option byte).
Hypothesis LO : (lo <= bv_unsigned sp - 160)%Z.
Hypothesis LOLO : (0x105000 <= lo)%Z.
Hypothesis RO : (bv_unsigned sp <= OS)%Z.
Hypothesis RO2 : (OS + 288 < 2^62)%Z.
Hypothesis RP : (0 <= P <= L)%Z.
Hypothesis ROB : (0 <= OB)%Z.
Hypothesis ROB2 : (OB + L < 2^62)%Z.
Hypothesis SEP : (OB + L <= lo \/ OS + 288 <= OB \/ (bv_unsigned sp <= OB /\ OB + L <= OS))%Z.
Hypothesis RW : (0 <= W < 23)%Z.
Hypothesis RF : (0 <= fill < 256)%Z.
Hypothesis RFL : (0 <= flags < 2^32)%Z.
Hypothesis SRC0 : bytes_at psegs m0 OB bs.
Hypothesis LBS : length bs = Z.to_nat L.

Notation POST := (os_pad_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS flags fill j148 j284 m0).
Notation WP := [(bv_unsigned sp - 160, bv_unsigned sp); (OS + 40, OS + 128); (OS + 160, OS + 168)]%Z.

Notation FRAME := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Notation SBC pb pp ep dum := [C8 (Z_to_bv 64 0xcac78); C8 (Z_to_bv 64 0xe24c8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                              C8 pb; C8 (Z_to_bv 64 pp); C8 (Z_to_bv 64 ep); CB 64 dum] (only parsing).

Lemma pad_k3 : forall (pb : word) (pp ep : Z) (dum jo : list byte) (m : word -> option byte)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word),
  PUTINV OS pp ep ->
  munch WP m0 m -> wmono psegs m0 m -> mem_inv psegs m ->
  stk psegs m lo (bv_unsigned sp + -96) ->
  rw_cells psegs m (bv_unsigned sp + -96) [CB 24 jo] -> rw_cells psegs m (bv_unsigned sp + -72) FRAME ->
  rw_cells psegs m OS (SBC pb pp ep dum) ->
  rw_cells psegs m (OS + 136) (ios_cellsX OS 0xcad28 flags W fill j148 j284) ->
  evt psegs POST
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 OS) (Z_to_bv 64 (OS + 136)) a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3ee08) fc None m (seg_rom psegs)).
Proof using LO LOLO RO RO2 RW RF RFL SRC0 LBS.
  intros until t6. intros PI MU WM MI ST SO FR SB IOS.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  unfold ios_cellsX in IOS.
  lstep.
  do 2 lstep.
  do 11 lstep.
  glueZ SO FR. release_frame SO ST (bv_unsigned sp).
  unfold os_pad_post, ios_cellsX. sys_finish; eassumption.
Qed.

Lemma pad_k2 : forall (pb : word) (pp ep : Z) (dum jo : list byte) (m : word -> option byte)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 x23 t3 t4 t5 t6 : word),
  PUTINV OS pp ep ->
  munch WP m0 m -> wmono psegs m0 m -> mem_inv psegs m ->
  stk psegs m lo (bv_unsigned sp + -96) ->
  rw_cells psegs m (bv_unsigned sp + -96) [CB 24 jo] -> rw_cells psegs m (bv_unsigned sp + -72) FRAME ->
  rw_cells psegs m OS (SBC pb pp ep dum) ->
  rw_cells psegs m (OS + 136) (ios_cellsX OS 0xcad28 flags W fill j148 j284) ->
  rw_cells psegs m 0xcacd8 [C8 (Z_to_bv 64 0x76930); C8 (Z_to_bv 64 0x3e254); C8 (Z_to_bv 64 8)] ->
  evt psegs POST
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 OS) (Z_to_bv 64 (OS + 136)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (OB + P)) (Z_to_bv 64 (OB + L)) x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3ede4) fc None m (seg_rom psegs)).
Proof using LO LOLO RO RO2 RP ROB ROB2 SEP RW RF RFL SRC0 LBS.
  intros until t6. intros PI MU WM MI ST SO FR SB IOS VT.
  pose proof (bytes_at_sub m OB bs P (L - P) (bytes_at_transport _ _ _ _ _ _ SRC0 MU ltac:(rewrite LBS; cbv [disjoint_from fst snd]; repeat split; lia))
                ltac:(lia) ltac:(lia) ltac:(rewrite LBS; lia)) as SRC2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  lstep.
  replace (OB + L - (OB + P))%Z with (L - P)%Z by lia.
  lstep.
  destruct (Z.eq_dec P L) as [PL|PL].
  -
    br_is true ltac:(rewrite bv_lts_zero_l, unsigned_lit by lia; cbn [negb]; apply negb_true_iff, andb_false_iff; left; apply Z.ltb_ge; lia).
    eapply pad_k3; eassumption.
  - br_is false ltac:(rewrite bv_lts_zero_l, unsigned_lit by lia; cbn [negb]; apply negb_false_iff, andb_true_iff; split; apply Z.ltb_lt; lia).
    do 5 lstep.
    lstep.
    call_sp (os_xsputnX_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OS (OB + P)%Z (L - P)%Z (L - P)%Z pp ep);
      [exact ST | lia | lia | exact SB | exact PI | lia | lia | exact SRC2 | rewrite firstn_length_le by (rewrite length_skipn, LBS; lia); lia | lia | lia | lia | lia | exact VT | assumption |].
    rename PC into ST. rename PC0 into SB. rename POST into PI'. unfold sb_cells in SB.
    lstep.
    bru false.
    eapply pad_k3; eassumption.
Qed.

Lemma pad_k1 : forall (pb : word) (pp ep : Z) (dum jo : list byte) (m : word -> option byte)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  PUTINV OS pp ep ->
  munch WP m0 m -> wmono psegs m0 m -> mem_inv psegs m ->
  stk psegs m lo (bv_unsigned sp + -96) ->
  rw_cells psegs m (bv_unsigned sp + -96) [CB 24 jo] -> rw_cells psegs m (bv_unsigned sp + -72) FRAME ->
  rw_cells psegs m OS (SBC pb pp ep dum) ->
  rw_cells psegs m (OS + 136) (ios_cellsX OS 0xcad28 flags W fill j148 j284) ->
  rw_cells psegs m 0xcacd8 [C8 (Z_to_bv 64 0x76930); C8 (Z_to_bv 64 0x3e254); C8 (Z_to_bv 64 8)] ->
  evt psegs POST
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 OS) (Z_to_bv 64 (OS + 136)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (OB + P)) (Z_to_bv 64 (OB + L)) (Z_to_bv 64 OB) (Z_to_bv 64 fill) (Z_to_bv 64 P) (Z_to_bv 64 W) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3ed6c) fc None m (seg_rom psegs)).
Proof using LO LOLO RO RO2 RP ROB ROB2 SEP RW RF RFL SRC0 LBS.
  intros until t6. intros PI MU WM MI ST SO FR SB IOS VT.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  lstep.
  replace (OB + L - OB)%Z with L by lia.
  do 4 lstep.
  rewrite (pad_ns_eq L W) by lia.
  lstep.
  destruct (Z.ltb_spec L W) as [LW|LW].
  2:{
    replace (pad_ns L W) with 0%Z by (unfold pad_ns; destruct (Z.ltb_spec L W); lia).
    if_true.
    eapply pad_k2; eassumption. }
  replace (pad_ns L W) with (W - L)%Z by (unfold pad_ns; destruct (Z.ltb_spec L W); lia).
  br_is false ltac:(rewrite bv_lts_zero_l, unsigned_lit by lia; cbn [negb]; apply negb_false_iff, andb_true_iff; split; apply Z.ltb_lt; lia).
  do 3 lstep.
  lstep.

  set (E2 := (bv_unsigned sp + -96)%Z) in |- *. unfold E2 at 1.
  call_sp (strnc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo E2 (W - L)%Z fill jo);
    [exact ST | lia | lia | exact SO | subst E2; lia | subst E2; lia | lia | lia | assumption |].
  subst E2.
  rename PC into ST. rename PC0 into Y1. rename PC1 into Y2. rename PC2 into Y3. rename POST into Y4. destruct Y4 as [rest Y4].
  do 2 lstep.
  lstep.
  rewrite (land1_double (W - L)) by lia. bru true.
  lstep.
  do 4 lstep.
  lstep.
  pose proof (rw_cells_bytes_at _ _ _ _ Y2) as Y2'. cbn [cells_bytes cbytes app] in Y2'. rewrite app_nil_r in Y2'.
  replace (bv_unsigned sp + -96 + 1)%Z with (bv_unsigned sp + -95)%Z in Y2' by lia.
  call_sp (os_xsputnX_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OS (bv_unsigned sp + -95)%Z (W - L)%Z (W - L)%Z pp ep);
      [exact ST | lia | lia | exact SB | exact PI | lia | lia | exact Y2' | rewrite repeat_length; lia | lia | lia | lia | lia | exact VT | assumption |].
  try clear Y2'.
  rename PC into ST. rename PC0 into SB. rename POST into PI'. unfold sb_cells in SB.
  do 3 lstep.
  lstep.
  rewrite (land1_double (W - L)) by lia. bru true.
  lstep.
  bru false.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (strobj_forget mm (bv_unsigned sp + -96)%Z (W - L)%Z _ _ _ _ ltac:(lia) Y1 Y2 Y3 Y4) as [jo' SO'] end.
  clear Y1 Y2 Y3 Y4.
  eapply pad_k2; eassumption.
Qed.
End Pad.

Theorem os_pad_proof : os_pad_stmt.
Proof.
  unfold os_pad_stmt. intros until j284. intros ST LO LOLO SB PI IOS RO RO2 SRC LBS0 RP ROB ROB2 SEP RW RF RFL VT MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (LBS : length bs = Z.to_nat L) by lia.
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  pose proof (conj SRC I) as SRCbox. clear SRC.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (OS + 40, OS + 128); (OS + 160, OS + 168)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  unfold sb_cells in SB. unfold ios_cellsX in IOS.
  carve_frame 72%nat ST.
  carve_frame 24%nat ST.
  replace (bv_unsigned sp - 72 - 24)%Z with (bv_unsigned sp + -96)%Z in FR0 by lia.
  replace (bv_unsigned sp - 72 - 24)%Z with (bv_unsigned sp + -96)%Z in ST by lia.
  do 11 lstep.
  bru false.
  do 8 lstep.
  replace (OB + P - OB)%Z with P by lia.
  lstep.
  destruct (Z.eq_dec P 0) as [P0|P1].
  -
    subst P. if_true.
    eapply pad_k1; try eassumption; try lia. exact (proj1 SRCbox).
  - br_is false ltac:(rewrite bv_lts_zero_l, unsigned_lit by lia; cbn [negb]; apply negb_false_iff, andb_true_iff; split; apply Z.ltb_lt; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (bytes_at_sub mm OB bs 0 P (bytes_at_transport _ _ _ _ _ _ (proj1 SRCbox) MU ltac:(rewrite LBS; cbv [disjoint_from fst snd]; repeat split; lia))
                    ltac:(lia) ltac:(lia) ltac:(rewrite LBS; lia)) as SRC1 end.
    replace (OB + 0)%Z with OB in SRC1 by lia.
    do 5 lstep.
    lstep.
    call_sp (os_xsputnX_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OS OB P P pp ep);
      [exact ST | lia | lia | exact SB | exact PI | lia | lia | exact SRC1 | rewrite firstn_length_le by (rewrite length_skipn, LBS; lia); lia | lia | lia | lia | lia | exact VT | assumption |].
    rename PC into ST. rename PC0 into SB. rename POST into PI'. unfold sb_cells in SB.
    lstep.
    bru false.
    eapply pad_k1; try eassumption; try lia. exact (proj1 SRCbox).
Qed.
