(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation DT2_W tv t38 t14 := [(tv, tv + 1024); (t38, t38 + 1024); (t14, t14 + 1024)]%Z (only parsing).
Notation ONE := (Z_to_bv 64 1) (only parsing).
Notation ZERO := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition dt2_geom (tv t38 t14 sa : Z) : Prop :=
  0 < tv /\ tv mod 16 = 0 /\ tv + 1024 <= 2^47 /\ (tv + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= tv) /\ (tv + 1024 <= 0x10000 \/ SEGTOP_A <= tv)
  /\ 0 < t38 /\ t38 mod 16 = 0 /\ t38 + 1024 <= 2^47 /\ (t38 + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= t38) /\ (t38 + 1024 <= 0x10000 \/ SEGTOP_A <= t38)
  /\ 0 < t14 /\ t14 mod 16 = 0 /\ t14 + 1024 <= 2^47 /\ (t14 + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= t14) /\ (t14 + 1024 <= 0x10000 \/ SEGTOP_A <= t14)
  /\ (tv + 1024 <= t38 \/ t38 + 1024 <= tv) /\ (tv + 1024 <= t14 \/ t14 + 1024 <= tv) /\ (t38 + 1024 <= t14 \/ t14 + 1024 <= t38)
  /\ 0 < sa /\ sa mod 8 = 0 /\ sa + 128 <= 2^47 /\ (sa + 128 <= tv \/ tv + 1024 <= sa) /\ (sa + 128 <= t38 \/ t38 + 1024 <= sa) /\ (sa + 128 <= t14 \/ t14 + 1024 <= sa).

(* [comment removed for export] *)
Definition dt2_cells (m : mem) (sa tv t38 : Z) : Prop :=
  rw_cells asegs m (sa + 56) [C8 (Z_to_bv 64 250)] /\ rw_cells asegs m (sa + 112) [C8 (Z_to_bv 64 tv); C8 (Z_to_bv 64 t38)].

(* [comment removed for export] *)
Notation DT2_R ra0 sp gp tp s0 sa a0 a1 i s2 s5 s8 s9 s10 t14 :=
  (mkR ONE sp gp tp ZERO ZERO ZERO s0 (Z_to_bv 64 sa) a0 a1 (Z_to_bv 64 (4 * i)) (Z_to_bv 64 i) ONE ONE ONE (Z_to_bv 64 1024)
       s2 (Z_to_bv 64 SHB) (Z_to_bv 64 (3 * i + 4)) s5 (Z_to_bv 64 5) ONE s8 s9 s10 (Z_to_bv 64 t14)
       (Z_to_bv 64 (3 + 253 * i)) (Z_to_bv 64 (87 - i)) ONE (Z_to_bv 64 (i + 2))) (only parsing).

(* [comment removed for export] *)
Definition tsmall (w : word) : Prop := bv_unsigned (sx32 w) <= 65535 \/ 2^64 - 65536 <= bv_unsigned (sx32 w).
Definition small_upto (ws : list word) (i : Z) : Prop :=
  forall (k : Z) (w : word), 0 <= k < i -> nth_error ws (Z.to_nat k) = Some w -> tsmall w.
Lemma small_upto_0 : forall ws, small_upto ws 0.
Proof. intros ws k w Hk E. lia. Qed.
Lemma small_upto_upd : forall (ws : list word) (i : Z) (v : word),
  small_upto ws i -> 0 <= i < Z.of_nat (length ws) -> tsmall v -> small_upto (upd ws (Z.to_nat i) v) (i + 1).
Proof.
  intros ws i v B Hi Hv k w Hk E.
  destruct (Z.eq_dec k i) as [->|NE].
  - rewrite nth_error_upd_same in E by lia. congruence.
  - rewrite nth_error_upd_other in E by lia. eapply B; [| exact E]. lia.
Qed.
Lemma small_upto_forall : forall (ws : list word) (n : Z), Z.of_nat (length ws) = n -> small_upto ws n -> Forall tsmall ws.
Proof.
  intros ws n L B. apply Forall_forall. intros w Hin.
  destruct (In_nth_error _ _ Hin) as (k & E).
  assert (Hk : (k < length ws)%nat).
  { destruct (Nat.lt_ge_cases k (length ws)) as [H|H]; [exact H|]. apply nth_error_None in H. congruence. }
  apply (B (Z.of_nat k) w); [lia|]. rewrite Nat2Z.id. exact E.
Qed.

Lemma tsmall_small : forall x, 0 <= x <= 65535 -> tsmall (Z_to_bv 64 x).
Proof.
  intros x Hx. unfold tsmall, sx32. left. rewrite (unsigned_lit x) by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia). rewrite unsigned_lit by lia. lia.
Qed.
Lemma tsmall_neg : forall x, 0 <= x <= 65535 -> tsmall (Z_to_bv 64 (0 - x)).
Proof.
  intros x Hx. unfold tsmall, sx32. destruct (Z.eq_dec x 0) as [->|NZ].
  - left. change (0 - 0) with 0. rewrite (unsigned_lit 0) by lia.
    rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia). rewrite unsigned_lit by lia. lia.
  - right. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap. change (bv_modulus 64) with 18446744073709551616.
    change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
    replace ((0 - x) mod 18446744073709551616) with (18446744073709551616 - x) by (symmetry; Z.div_mod_to_equations; lia).
    replace ((18446744073709551616 - x + 2147483648) mod 4294967296) with (2147483648 - x) by (symmetry; Z.div_mod_to_equations; lia).
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616. Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Lemma tsmall_srliw : forall x d, 0 <= x < 2^31 -> 0 < d -> x <= 65535 -> tsmall (Z_to_bv 64 (bv_swrap 32 (bv_wrap 32 x / d))).
Proof.
  intros x d Hx Hd Hs. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. rewrite (Z.mod_small x) by lia.
  assert (R : 0 <= x / d <= x).
  { split; [apply Z.div_pos; lia|]. destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.div_0_l; lia|]. apply Z.div_le_upper_bound; nia. }
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia). apply tsmall_small. lia.
Qed.
(* [comment removed for export] *)
Lemma tsmall_neg_srliw : forall x d, 0 <= x < 2^31 -> 0 < d -> x <= 65535 ->
  tsmall (Z_to_bv 64 (0 - bv_swrap 32 (bv_wrap 32 x / d) mod 18446744073709551616)).
Proof.
  intros x d Hx Hd Hs. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. rewrite (Z.mod_small x) by lia.
  assert (R : 0 <= x / d <= x).
  { split; [apply Z.div_pos; lia|]. destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.div_0_l; lia|]. apply Z.div_le_upper_bound; nia. }
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia). rewrite Z.mod_small by lia. apply tsmall_neg. lia.
Qed.
(* [comment removed for export] *)
Lemma tsmall_neg_div : forall y d, 281474976710656 <= d -> tsmall (Z_to_bv 64 (0 - y mod 18446744073709551616 / d)).
Proof.
  intros y d Hd. apply tsmall_neg.
  pose proof (Z.mod_pos_bound y 18446744073709551616 ltac:(lia)) as [M0 M1].
  split; [apply Z.div_pos; lia|].
  apply Z.lt_succ_r. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Ltac small_val_tac :=
  first [ assumption
        | apply tsmall_srliw; lia
        | apply tsmall_neg_srliw; lia
        | apply tsmall_neg_div; lia
        | apply tsmall_neg; lia
        | apply tsmall_small; lia ].

(* [comment removed for export] *)
Ltac arr_sws A idx E SR :=
  lazymatch goal with
  | UA : u32arr asegs ?mm A ?ws, UAL : Z.of_nat (length ?ws) = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SOK := fresh "SOK" in
    pose proof (u32arr_store_ok asegs mm A ws idx (wa E) UA ltac:(lia) ltac:(f_equal; lia)) as SOK;
    zstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm (Z_to_bv 64 ?E') (le4 ?v)) _) =>
      let N := fresh "UA" in
      assert (N : u32arr asegs (write_to_mem mm (wa E') (le4 v)) A (upd ws (Z.to_nat idx) v))
        by (replace E' with (A + 4 * idx) by lia; apply (u32arr_write asegs mm A ws idx v UA); lia);
      let B := fresh "SU" in
      assert (B : small_upto (upd ws (Z.to_nat idx) v) (idx + 1)) by (apply (small_upto_upd ws idx v SR); [lia | small_val_tac]);
      clear SR; rename B into SR;
      clear UA; store_done; rename N into UA;
      rewrite <- (upd_length ws (Z.to_nat idx) v) in UAL;
      let ws' := fresh "aws" in set (ws' := upd ws (Z.to_nat idx) v) in *; clearbody ws'; try clear ws
    end
  end.

(* [comment removed for export] *)
Definition dt2_exit (sp gp tp s0 s2 s5 s8 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (sa tv t38 t14 : Z) : machine_state -> Prop :=
  fun ms' => exists (a0' a1' a2' a3' s4' s10' t3' t4' t6' : word) (m' : mem) (ws1 ws2 ws3 : list word),
    ms' = MS (mkR (Z_to_bv 64 1) sp gp tp (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) s0 (Z_to_bv 64 sa) a0' a1' a2' a3'
                  (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1024) s2 (Z_to_bv 64 SHB) s4' s5 (Z_to_bv 64 5) (Z_to_bv 64 1) s8 s9 s10' (Z_to_bv 64 t14)
                  t3' t4' (Z_to_bv 64 1) t6')
             F (Z_to_bv 64 0xa0168) fc None m' (seg_rom asegs)
    /\ munch (DT2_W tv t38 t14) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' tv ws1 /\ Z.of_nat (length ws1) = 256 /\ acc asegs m' tv 1024
    /\ u32arr asegs m' t38 ws2 /\ Z.of_nat (length ws2) = 256 /\ acc asegs m' t38 1024 /\ Forall tsmall ws2
    /\ u32arr asegs m' t14 ws3 /\ Z.of_nat (length ws3) = 256 /\ acc asegs m' t14 1024 /\ Forall tsmall ws3
    /\ dt2_cells m' sa tv t38.
(* [comment removed for export] *)
Lemma dt2_tail : forall (i : Z) (sp gp tp s0 s2 s5 s8 s9 s10 : word) (v : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (sa tv t38 t14 : Z) (ws1 ws2 ws3 : list word) (Q : machine_state -> Prop),
  0 <= i <= 255 -> dt2_geom tv t38 t14 sa ->
  munch (DT2_W tv t38 t14) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  u32arr asegs m tv ws1 -> Z.of_nat (length ws1) = 256 -> acc asegs m tv 1024 ->
  u32arr asegs m t38 ws2 -> Z.of_nat (length ws2) = 256 -> acc asegs m t38 1024 ->
  u32arr asegs m t14 ws3 -> Z.of_nat (length ws3) = 256 -> acc asegs m t14 1024 ->
  small_upto ws2 (i + 1) -> small_upto ws3 i -> tsmall v ->
  dt2_cells m sa tv t38 ->
  (forall (a1' : word) (m' : mem) (ws3' : list word),
      munch (DT2_W tv t38 t14) m0 m' -> wmono asegs m0 m' -> mem_inv asegs m' ->
      u32arr asegs m' tv ws1 -> acc asegs m' tv 1024 -> u32arr asegs m' t38 ws2 -> acc asegs m' t38 1024 ->
      u32arr asegs m' t14 ws3' -> Z.of_nat (length ws3') = 256 -> acc asegs m' t14 1024 ->
      small_upto ws2 (i + 1) -> small_upto ws3' (i + 1) ->
      dt2_cells m' sa tv t38 ->
      evt asegs Q (MS (DT2_R ra0 sp gp tp s0 sa (Z_to_bv 64 (t14 + 4 * i)) a1' (i + 1) s2 s5 s8 s9 s10 t14) F (Z_to_bv 64 0x9f8e8) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (DT2_R ra0 sp gp tp s0 sa (Z_to_bv 64 (t14 + 4 * i)) v i s2 s5 s8 s9 s10 t14) F (Z_to_bv 64 0x9f8cc) fc None m (seg_rom asegs)).
Proof.
  intros i sp gp tp s0 s2 s5 s8 s9 s10 v F fc m0 m sa tv t38 t14 ws1 ws2 ws3 Q HI GEO MU WM MI UA1 UAL1 ACC1 UA2 UAL2 ACC2 UA3 UAL3 ACC3 SR2 SR3 TV [CW CT] CONT.
  pose proof GEO as (V0 & V16 & VHI & VSH & VSEG & W0 & W16 & WHI & WSH & WSEG & X0 & X16 & XHI & XSH & XSEG & D12 & D13 & D23 & CA0 & CA8 & CAHI & CD1 & CD2 & CD3).
  unfold SEGTOP_A, SHB in *.
  park_disj.
  arr_sws t14 i (t14 + 4 * i) SR3.
  lwalk [0x9f8e8].
  replace (4 * i + 4) with (4 * (i + 1)) by (clear; lia).
  replace (i + 3) with (i + 1 + 2) by (clear; lia).
  replace (3 * i + 7) with (3 * (i + 1) + 4) by (clear; lia).
  replace (87 - i + -1) with (87 - (i + 1)) by (clear; lia).
  replace (3 + 253 * i + 253) with (3 + 253 * (i + 1)) by (clear; lia).
  eapply CONT; try eassumption.
  all: lazymatch goal with
       | |- munch _ _ _ => eapply munch_trans; eassumption
       | |- wmono _ _ _ => eapply wmono_trans; eassumption
       | |- dt2_cells _ _ _ _ => split; assumption
       | |- ?g => idtac "LEFT:" g end.
Qed.
(* [comment removed for export] *)
Lemma dt2_round : forall (i : Z) (sp gp tp s0 a0 a1 s2 s5 s8 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (sa tv t38 t14 : Z) (ws1 ws2 ws3 : list word) (Q : machine_state -> Prop),
  0 <= i <= 255 -> dt2_geom tv t38 t14 sa ->
  munch (DT2_W tv t38 t14) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  u32arr asegs m tv ws1 -> Z.of_nat (length ws1) = 256 -> acc asegs m tv 1024 ->
  u32arr asegs m t38 ws2 -> Z.of_nat (length ws2) = 256 -> acc asegs m t38 1024 ->
  u32arr asegs m t14 ws3 -> Z.of_nat (length ws3) = 256 -> acc asegs m t14 1024 ->
  small_upto ws2 i -> small_upto ws3 i ->
  dt2_cells m sa tv t38 ->
  (forall (a0' a1' s10' : word) (m' : mem) (ws1' ws2' ws3' : list word),
      munch (DT2_W tv t38 t14) m0 m' -> wmono asegs m0 m' -> mem_inv asegs m' ->
      u32arr asegs m' tv ws1' -> Z.of_nat (length ws1') = 256 -> acc asegs m' tv 1024 ->
      u32arr asegs m' t38 ws2' -> Z.of_nat (length ws2') = 256 -> acc asegs m' t38 1024 ->
      u32arr asegs m' t14 ws3' -> Z.of_nat (length ws3') = 256 -> acc asegs m' t14 1024 ->
      small_upto ws2' (i + 1) -> small_upto ws3' (i + 1) ->
      dt2_cells m' sa tv t38 ->
      evt asegs Q (MS (DT2_R ra0 sp gp tp s0 sa a0' a1' (i + 1) s2 s5 s8 s9 s10' t14) F (Z_to_bv 64 0x9f8e8) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (DT2_R ra0 sp gp tp s0 sa a0 a1 i s2 s5 s8 s9 s10 t14) F (Z_to_bv 64 0x9f8ec) fc None m (seg_rom asegs)).
Proof.
  intros i sp gp tp s0 a0 a1 s2 s5 s8 s9 s10 F fc m0 m sa tv t38 t14 ws1 ws2 ws3 Q HI GEO MU WM MI UA1 UAL1 ACC1 UA2 UAL2 ACC2 UA3 UAL3 ACC3 SR2 SR3 [CW CT] CONT.
  pose proof GEO as (V0 & V16 & VHI & VSH & VSEG & W0 & W16 & WHI & WSH & WSEG & X0 & X16 & XHI & XSH & XSEG & D12 & D13 & D23 & CA0 & CA8 & CAHI & CD1 & CD2 & CD3).
  unfold SEGTOP_A, SHB in *.
  (* [comment removed for export] *)
  assert (TL : forall (a11 s101 : word) (m1 : mem) (ws1x ws2x : list word),
      munch (DT2_W tv t38 t14) m0 m1 -> wmono asegs m0 m1 -> mem_inv asegs m1 ->
      u32arr asegs m1 tv ws1x -> Z.of_nat (length ws1x) = 256 -> acc asegs m1 tv 1024 ->
      u32arr asegs m1 t38 ws2x -> Z.of_nat (length ws2x) = 256 -> acc asegs m1 t38 1024 ->
      u32arr asegs m1 t14 ws3 -> acc asegs m1 t14 1024 -> small_upto ws2x (i + 1) -> tsmall a11 -> dt2_cells m1 sa tv t38 ->
      evt asegs Q (MS (DT2_R ra0 sp gp tp s0 sa (Z_to_bv 64 (t14 + 4 * i)) a11 i s2 s5 s8 s9 s101 t14) F (Z_to_bv 64 0x9f8cc) fc None m1 (seg_rom asegs))).
  { intros a11 s101 m1 ws1x ws2x MU1 WM1 MI1 UA1x UAL1x ACC1x UA2x UAL2x ACC2x UA3x ACC3x SR2x TVx CX.
    eapply (dt2_tail i) with (m0 := m0) (ws1 := ws1x) (ws2 := ws2x) (ws3 := ws3); try eassumption.
    intros a1' m' ws3' MU' WM' MI' UA1' ACC1' UA2' ACC2' UA3' UAL3' ACC3' SR2' SR3' CX'.
    eapply CONT; eassumption. }
  assert (TL48 : forall (a01 a11 s101 : word) (m1 : mem) (ws1x ws2x ws3x : list word),
      munch (DT2_W tv t38 t14) m0 m1 -> wmono asegs m0 m1 -> mem_inv asegs m1 ->
      u32arr asegs m1 tv ws1x -> Z.of_nat (length ws1x) = 256 -> acc asegs m1 tv 1024 ->
      u32arr asegs m1 t38 ws2x -> Z.of_nat (length ws2x) = 256 -> acc asegs m1 t38 1024 ->
      u32arr asegs m1 t14 ws3x -> Z.of_nat (length ws3x) = 256 -> acc asegs m1 t14 1024 -> small_upto ws2x (i + 1) -> small_upto ws3x (i + 1) -> dt2_cells m1 sa tv t38 ->
      evt asegs Q (MS (DT2_R ra0 sp gp tp s0 sa a01 a11 i s2 s5 s8 s9 s101 t14) F (Z_to_bv 64 0x9f8d0) fc None m1 (seg_rom asegs))).
  { intros a01 a11 s101 m1 ws1x ws2x ws3x MU1 WM1 MI1 UA1x UAL1x ACC1x UA2x UAL2x ACC2x UA3x UAL3x ACC3x SR2x SR3x [CWx CTx].
    clear MU WM MI UA1 UAL1 ACC1 UA2 UAL2 ACC2 UA3 UAL3 ACC3 SR2 SR3 CW CT TL.
    park_disj.
    lwalk [0x9f8e8].
    replace (4 * i + 4) with (4 * (i + 1)) by (clear; lia).
    replace (i + 3) with (i + 1 + 2) by (clear; lia).
    replace (3 * i + 7) with (3 * (i + 1) + 4) by (clear; lia).
    replace (87 - i + -1) with (87 - (i + 1)) by (clear; lia).
    replace (3 + 253 * i + 253) with (3 + 253 * (i + 1)) by (clear; lia).
    eapply CONT; try eassumption. split; assumption. }
  clear CONT.
  park_disj.
  lwalk [0x9f8cc; 0x9f8d0].
  brfork R1.
  - (* [comment removed for export] *)
    lwalk [0x9f9c4; 0x9f8cc; 0x9f8d0].
    arr_sw tv i (tv + 4 * i).
    lwalk [0x9f9f0; 0x9f8cc; 0x9f8d0].
    arr_sws t38 i (t38 + 4 * i) SR2.
    lwalk [0x9fa18; 0x9f8cc; 0x9f8d0].
    arr_sws t14 i (t14 + 4 * i) SR3.
    lwalk [0x9f8d0; 0x9f8cc].
    eapply TL48; try eassumption. all: first [assumption | split; assumption].
  - lwalk [0x9f8cc; 0x9f8d0]. brfork R2.
    + (* [comment removed for export] *)
      lwalk [0x9f8cc; 0x9f8d0]. brfork R3.
      * (* [comment removed for export] *)
        lwalk [0x9f8cc; 0x9f8d0]. brfork R4.
        -- (* [comment removed for export] *)
           lwalk [0x9f8cc; 0x9f8d0]. brfork R5.
           ++ (* [comment removed for export] *)
              lwalk [0x9f8cc; 0x9f8d0]. brfork R6.
              ** (* [comment removed for export] *)
                 lwalk [0x9fd1c; 0x9fdb4; 0x9f8cc; 0x9f8d0].
                 brfork R7.
                 --- (* [comment removed for export] *)
                     lwalk [0x9fdb4; 0x9f8cc; 0x9f8d0].
                     arr_sw tv i (tv + 4 * i).
                     lwalk [0x9fde8; 0x9f8cc; 0x9f8d0].
                     arr_sws t38 i (t38 + 4 * i) SR2.
                     lwalk [0x9fe10; 0x9f8cc; 0x9f8d0].
                     arr_sws t14 i (t14 + 4 * i) SR3.
                     lwalk [0x9f8d0; 0x9f8cc].
                     eapply TL48; try eassumption. all: first [assumption | split; assumption].
                 --- (* [comment removed for export] *)
                     lwalk [0x9fd1c; 0x9f8cc; 0x9f8d0].
                     arr_sw tv i (tv + 4 * i).
                     lwalk [0x9fd60; 0x9f8cc; 0x9f8d0].
                     arr_sws t38 i (t38 + 4 * i) SR2.
                     lwalk [0x9f8cc; 0x9f8d0].
                     eapply TL; try eassumption. all: first [small_val_tac | split; assumption].
              ** (* [comment removed for export] *)
                 lwalk [0x9fc70; 0x9f8cc; 0x9f8d0].
                 arr_sw tv i (tv + 4 * i).
                 lwalk [0x9fcac; 0x9f8cc; 0x9f8d0].
                 arr_sws t38 i (t38 + 4 * i) SR2.
                 lwalk [0x9f8cc; 0x9f8d0].
                 eapply TL; try eassumption. all: first [small_val_tac | split; assumption].
           ++ (* [comment removed for export] *)
              lwalk [0x9fbbc; 0x9f8cc; 0x9f8d0].
              arr_sw tv i (tv + 4 * i).
              lwalk [0x9fc00; 0x9f8cc; 0x9f8d0].
              arr_sws t38 i (t38 + 4 * i) SR2.
              lwalk [0x9f8cc; 0x9f8d0].
              eapply TL; try eassumption. all: first [small_val_tac | split; assumption].
        -- (* [comment removed for export] *)
           lwalk [0x9fb10; 0x9f8cc; 0x9f8d0].
           arr_sw tv i (tv + 4 * i).
           lwalk [0x9fb4c; 0x9f8cc; 0x9f8d0].
           arr_sws t38 i (t38 + 4 * i) SR2.
           lwalk [0x9f8cc; 0x9f8d0].
           eapply TL; try eassumption. all: first [small_val_tac | split; assumption].
      * (* [comment removed for export] *)
        lwalk [0x9fa5c; 0x9f8cc; 0x9f8d0].
        arr_sw tv i (tv + 4 * i).
        lwalk [0x9fa9c; 0x9f8cc; 0x9f8d0].
        arr_sws t38 i (t38 + 4 * i) SR2.
        lwalk [0x9f8cc; 0x9f8d0].
        eapply TL; try eassumption. all: first [small_val_tac | split; assumption].
    + (* [comment removed for export] *)
      lwalk [0x9f928; 0x9f8cc; 0x9f8d0].
      arr_sw tv i (tv + 4 * i).
      lwalk [0x9f960; 0x9f8cc; 0x9f8d0].
      arr_sws t38 i (t38 + 4 * i) SR2.
      lwalk [0x9f8cc; 0x9f8d0].
      eapply TL; try eassumption. all: first [small_val_tac | split; assumption].
Qed.
(* [comment removed for export] *)
Lemma dt2_tables : forall (k : nat) (i : Z) (sp gp tp s0 a0 a1 s2 s5 s8 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (sa tv t38 t14 : Z) (ws1 ws2 ws3 : list word),
  Z.of_nat k = 256 - i -> 0 <= i -> (1 <= k)%nat -> dt2_geom tv t38 t14 sa ->
  munch (DT2_W tv t38 t14) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  u32arr asegs m tv ws1 -> Z.of_nat (length ws1) = 256 -> acc asegs m tv 1024 ->
  u32arr asegs m t38 ws2 -> Z.of_nat (length ws2) = 256 -> acc asegs m t38 1024 ->
  u32arr asegs m t14 ws3 -> Z.of_nat (length ws3) = 256 -> acc asegs m t14 1024 ->
  small_upto ws2 i -> small_upto ws3 i ->
  dt2_cells m sa tv t38 ->
  evt asegs (dt2_exit sp gp tp s0 s2 s5 s8 s9 F fc m0 sa tv t38 t14)
    (MS (DT2_R ra0 sp gp tp s0 sa a0 a1 i s2 s5 s8 s9 s10 t14) F (Z_to_bv 64 0x9f8ec) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i sp gp tp s0 a0 a1 s2 s5 s8 s9 s10 F fc m0 m sa tv t38 t14 ws1 ws2 ws3 HK HI HK1 GEO MU WM MI UA1 UAL1 ACC1 UA2 UAL2 ACC2 UA3 UAL3 ACC3 SR2 SR3 CX.
  { exfalso. lia. }
  eapply dt2_round with (m0 := m0); try eassumption; [clear - HK HI; lia|].
  intros a0' a1' s10' m' ws1' ws2' ws3' MU' WM' MI' UA1' UAL1' ACC1' UA2' UAL2' ACC2' UA3' UAL3' ACC3' SR2' SR3' CX'.
  clear MU WM MI UA1 UAL1 ACC1 UA2 UAL2 ACC2 UA3 UAL3 ACC3 SR2 SR3 CX.
  unfold SHB in *. destruct CX' as [CW' CT'].
  destruct k as [|k].
  - (* [comment removed for export] *)
    assert (EI : i + 1 = 256) by (clear - HK; lia).
    lwalk [0xa0168; 0x9f8ec].
    apply evt_done. unfold dt2_exit.
    pose proof (small_upto_forall ws2' 256 UAL2' ltac:(rewrite <- EI; exact SR2')) as F2.
    pose proof (small_upto_forall ws3' 256 UAL3' ltac:(rewrite <- EI; exact SR3')) as F3.
    do 9 eexists. exists m', ws1', ws2', ws3'.
    split; [reflexivity|].
    repeat (split; [assumption|]). all: try assumption. all: try (split; assumption).
  - lwalk [0xa0168; 0x9f8ec].
    replace (i + 3) with (i + 1 + 2) by (clear; lia).
    eapply (IH (i + 1)) with (m0 := m0); try eassumption; first [clear - HK HI; lia | split; assumption].
Qed.
