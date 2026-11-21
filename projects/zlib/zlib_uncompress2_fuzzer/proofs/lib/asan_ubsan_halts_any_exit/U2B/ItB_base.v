(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes Image ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AArr ItAKit UbFit2.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma zx16_small : forall e, 0 <= e < 65536 -> zx16 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e H. unfold zx16. rewrite unsigned_lit by lia. change (2 ^ 16) with 65536. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma sx16_small : forall e, 0 <= e < 32768 -> sx16 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e H. unfold sx16. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 16) with 65536. change (65536 / 2) with 32768.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma shl1_2x : forall v, Z.shiftl v 1 = 2 * v.
Proof. intros v. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. lia. Qed.
Lemma shl2_4x : forall v, Z.shiftl v 2 = 4 * v.
Proof. intros v. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia. Qed.

Lemma zbv_congr : forall x y, (x - y) mod 18446744073709551616 = 0 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  apply Z.mod_divide in H; [|lia]. destruct H as [q Hq].
  replace x with (y + q * 18446744073709551616) by lia. apply Z.mod_add. lia.
Qed.
Lemma zbv_sub_mod : forall a b, Z_to_bv 64 (a mod 18446744073709551616 - b mod 18446744073709551616) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply zbv_congr.
  rewrite (Z.mod_eq a 18446744073709551616), (Z.mod_eq b 18446744073709551616) by lia.
  replace (a - 18446744073709551616 * (a / 18446744073709551616) - (b - 18446744073709551616 * (b / 18446744073709551616)) - (a - b))
    with ((b / 18446744073709551616 - a / 18446744073709551616) * 18446744073709551616) by lia.
  apply Z.mod_mul. lia.
Qed.
Lemma zbv_sub_mod_l : forall a b, Z_to_bv 64 (a mod 18446744073709551616 - b) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply zbv_congr. rewrite (Z.mod_eq a 18446744073709551616) by lia.
  replace (a - 18446744073709551616 * (a / 18446744073709551616) - b - (a - b)) with ((- (a / 18446744073709551616)) * 18446744073709551616) by lia.
  apply Z.mod_mul. lia.
Qed.

Definition A_LBASE : Z := 0x246e0.
Definition A_LEXT  : Z := 0x24740.
Definition A_DBASE : Z := 0x247a0.
Definition A_DEXT  : Z := 0x24800.

Section WithSegs.
Variable segs : list Segment.
Lemma u16ro_read : forall m A ws (i : Z) w a,
  bytes_at segs m A (u16s ws) -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 2 * i) ->
  ov_read_bytes segs m a 2 = Some (le2 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u16s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (2 * i)%Z with (Z.of_nat (2 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u16s ws) (2 * Z.to_nat i) 2 Hb).
  2:{ rewrite Eu, !length_app, length_le2, Hlu. lia. }
  rewrite Eu, skipn_app, (skipn_all2 (u16s pre)), Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, (firstn_all2 (le2 w)) by (rewrite length_le2; lia).
  rewrite length_le2, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
Lemma f16ro_read : forall m A n f (i : Z) a,
  bytes_at segs m A (u16s (fws f n)) -> 0 <= i < Z.of_nat n -> a = wa (A + 2 * i) ->
  ov_read_bytes segs m a 2 = Some (le2 (Z_to_bv 64 (f i))).
Proof.
  intros m A n f i a Hb Hi Ea. eapply (u16ro_read m A (fws f n) i); [exact Hb| | lia| exact Ea].
  rewrite fws_nth by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma f16ro_read_lo : forall m A n f (i : Z) a,
  bytes_at segs m A (u16s (fws f n)) -> 0 <= i < Z.of_nat n -> a = wa (A + 2 * i) ->
  ov_read_bytes segs m a 1 = Some (le1 (Z_to_bv 64 (f i))).
Proof.
  intros m A n f i a Hb Hi ->.
  assert (Hn : nth_error (fws f n) (Z.to_nat i) = Some (Z_to_bv 64 (f i))) by (rewrite fws_nth by lia; rewrite Z2Nat.id by lia; reflexivity).
  destruct (u16s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (2 * i)%Z with (Z.of_nat (2 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u16s (fws f n)) (2 * Z.to_nat i) 1 Hb).
  2:{ rewrite Eu, !length_app, length_le2, Hlu. lia. }
  rewrite Eu, skipn_app, (skipn_all2 (u16s pre)), Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app. rewrite length_le2. change (1 - 2)%nat with 0%nat. rewrite firstn_O, app_nil_r. reflexivity.
Qed.
End WithSegs.

Lemma lbase_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m A_LBASE (u16s (fws (arr_get lbase_a) 31)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold A_LBASE; lia | rewrite u16s_length, fws_length; unfold A_LBASE; cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma lext_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m A_LEXT (u16s (fws (arr_get lext_a) 31)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold A_LEXT; lia | rewrite u16s_length, fws_length; unfold A_LEXT; cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma dbase_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m A_DBASE (u16s (fws (arr_get dbase_a) 32)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold A_DBASE; lia | rewrite u16s_length, fws_length; unfold A_DBASE; cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma dext_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m A_DEXT (u16s (fws (arr_get dext_a) 32)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold A_DEXT; lia | rewrite u16s_length, fws_length; unfold A_DEXT; cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma lbase_read : forall m i a, mem_inv bsegs m -> 0 <= i < 31 -> a = wa (149216 + 2 * i) ->
  ov_read_bytes bsegs m a 2 = Some (le2 (Z_to_bv 64 (arr_get lbase_a i))).
Proof. intros m i a MI Hi Ha. apply (f16ro_read bsegs m A_LBASE 31 (arr_get lbase_a) i a (lbase_bytes m MI)); [lia| exact Ha]. Qed.
Lemma lext_read : forall m i a, mem_inv bsegs m -> 0 <= i < 31 -> a = wa (149312 + 2 * i) ->
  ov_read_bytes bsegs m a 2 = Some (le2 (Z_to_bv 64 (arr_get lext_a i))).
Proof. intros m i a MI Hi Ha. apply (f16ro_read bsegs m A_LEXT 31 (arr_get lext_a) i a (lext_bytes m MI)); [lia| exact Ha]. Qed.
Lemma dbase_read : forall m i a, mem_inv bsegs m -> 0 <= i < 32 -> a = wa (149408 + 2 * i) ->
  ov_read_bytes bsegs m a 2 = Some (le2 (Z_to_bv 64 (arr_get dbase_a i))).
Proof. intros m i a MI Hi Ha. apply (f16ro_read bsegs m A_DBASE 32 (arr_get dbase_a) i a (dbase_bytes m MI)); [lia| exact Ha]. Qed.
Lemma dext_read : forall m i a, mem_inv bsegs m -> 0 <= i < 32 -> a = wa (149504 + 2 * i) ->
  ov_read_bytes bsegs m a 2 = Some (le2 (Z_to_bv 64 (arr_get dext_a i))).
Proof. intros m i a MI Hi Ha. apply (f16ro_read bsegs m A_DEXT 32 (arr_get dext_a) i a (dext_bytes m MI)); [lia| exact Ha]. Qed.

Definition tabsh_f (s0 : Z) (last : Z) (v : Z) : Z -> Z := fun s => if Z.eqb s (s0 + last) then v else 0.
Definition it_tabsh (m : word -> option byte) : Prop :=
  shadow_bytes m 2147469532 (2147469532 + 8) (tabsh_f 2147469532 7 6)
  /\ shadow_bytes m 2147469544 (2147469544 + 8) (tabsh_f 2147469544 7 6)
  /\ shadow_bytes m 2147469556 (2147469556 + 8) (fun _ => 0)
  /\ shadow_bytes m 2147469568 (2147469568 + 8) (fun _ => 0).

Lemma tab62_check : forall (m : word -> option byte) T s0 j,
  shadow_bytes m s0 (s0 + 8) (tabsh_f s0 7 6) -> T mod 8 = 0 -> 0 <= T -> s0 = T / 8 + 2147450880 -> 0 <= j < 31 ->
  exists b : byte,
    ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr (T + 2 * j) 3 + 2147450880)) 1 = Some [b] /\
    (sval b = 0 \/ (0 < sval b <= 7 /\ (T + 2 * j) mod 8 + 2 - 1 < sval b)).
Proof.
  intros m T s0 j SB T8 T0 ES Hj.
  assert (EA : Z.shiftr (T + 2 * j) 3 + 2147450880 = s0 + j / 4).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. subst s0. Z.div_mod_to_equations. lia. }
  rewrite EA.
  exists (Z_to_bv 8 (tabsh_f s0 7 6 (s0 + j / 4))). split.
  - apply (ov_read1_of_shadow_bytes bsegs m s0 (s0 + 8) _ (s0 + j / 4) SB). Z.div_mod_to_equations. lia.
  - unfold tabsh_f. destruct (Z.eqb_spec (s0 + j / 4) (s0 + 7)) as [E|NE].
    + right. rewrite sval_lit by lia. split; [lia|]. Z.div_mod_to_equations. lia.
    + left. apply sval_zero.
Qed.
Lemma tab64_check : forall (m : word -> option byte) T s0 j,
  shadow_bytes m s0 (s0 + 8) (fun _ => 0) -> T mod 8 = 0 -> 0 <= T -> s0 = T / 8 + 2147450880 -> 0 <= j < 32 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr (T + 2 * j) 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m T s0 j SB T8 T0 ES Hj.
  assert (EA : Z.shiftr (T + 2 * j) 3 + 2147450880 = s0 + j / 4).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. subst s0. Z.div_mod_to_equations. lia. }
  rewrite EA. apply (ov_read1_of_shadow_bytes bsegs m s0 (s0 + 8) (fun _ => 0) (s0 + j / 4) SB). Z.div_mod_to_equations. lia.
Qed.

Lemma it_tabsh_mu : forall W (m1 m : word -> option byte),
  it_tabsh m1 -> munch W m1 m -> disjoint_from W 2147469532 44 -> it_tabsh m.
Proof.
  intros W m1 m (A & B & C & D) MU DJ. unfold it_tabsh.
  split; [|split; [|split]].
  - apply (shadow_bytes_munch W m1 m _ _ _ A MU). eapply djf_sub; [exact DJ | lia | lia].
  - apply (shadow_bytes_munch W m1 m _ _ _ B MU). eapply djf_sub; [exact DJ | lia | lia].
  - apply (shadow_bytes_munch W m1 m _ _ _ C MU). eapply djf_sub; [exact DJ | lia | lia].
  - apply (shadow_bytes_munch W m1 m _ _ _ D MU). eapply djf_sub; [exact DJ | lia | lia].
Qed.

Notation amem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.

Definition bst (SP SPA S F PB LP TY : Z) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word) (pc : Z) (m : amem) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
          (Z_to_bv 64 F) (Z_to_bv 64 PB) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 808)) (Z_to_bv 64 LP) (Z_to_bv 64 TY)
          (Z_to_bv 64 (F + 32)) x25 (Z_to_bv 64 (Z.shiftr F 3 + 2147450880)) (Z_to_bv 64 F) x28 x29 x30 x31)
     FR (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Definition itb_W (SPA S F PB : Z) : list (Z * Z) :=
  [(SPA, SPA + 152); (F + 32, F + 64); (F + 96, F + 128); (PB, PB + 4); (S + 160, S + 168);
   (S + 808, S + 1384); (S + 1384, S + 7160)].

Definition frm19 (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 : word) : list cell :=
  [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72; C8 v80; C8 v88; C8 v96; C8 v104; C8 v112;
   C8 v120; C8 v128; C8 v136; C8 v144].

Definition itb_ctx (RNG : footprint) (SP SPA S F PB top : Z) (m1 : amem) : Prop :=
  (F mod 8 = 0 /\ S mod 8 = 0 /\ 6811648 <= S /\ S + 7176 <= top /\ 6811648 <= F /\ F + 256 <= top /\ top <= SPA /\
   SPA + 152 <= SP /\ SP <= 2 ^ 47 /\ (S + 7176 <= F \/ F + 256 <= S) /\ S + 136 <= PB <= S + 140 /\ PB mod 4 = 0) /\
  (rng RNG SPA 152 /\ rng RNG F 256 /\ rng RNG S 7176 /\ rng RNG (Z.shiftr S 3 + 2147450880) 897 /\
   rng RNG (Z.shiftr F 3 + 2147450880) 32 /\ rng_aimg RNG /\ rng RNG 2147469532 44) /\
  (shadow_bytes m1 (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0) /\
   shadow_bytes m1 (Z.shiftr F 3 + 2147450880 + 4) (Z.shiftr F 3 + 2147450880 + 8) (fun _ => 0) /\
   shadow_bytes m1 (Z.shiftr F 3 + 2147450880 + 12) (Z.shiftr F 3 + 2147450880 + 16) (fun _ => 0) /\
   it_tabsh m1) /\
  (disjoint_from (itb_W SPA S F PB) (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880)) /\
   disjoint_from (itb_W SPA S F PB) (Z.shiftr F 3 + 2147450880 + 4) (Z.shiftr F 3 + 2147450880 + 8 - (Z.shiftr F 3 + 2147450880 + 4)) /\
   disjoint_from (itb_W SPA S F PB) (Z.shiftr F 3 + 2147450880 + 12) (Z.shiftr F 3 + 2147450880 + 16 - (Z.shiftr F 3 + 2147450880 + 12)) /\
   disjoint_from (itb_W SPA S F PB) 2147469532 44).

Definition itb_inv (SPA S F PB : Z) (m1 m : amem)
    (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 : word)
    (cnt offs lf wf cf : Z -> Z) (next bitsw : word) : Prop :=
  mem_inv bsegs m /\ munch (itb_W SPA S F PB) m1 m /\ wmono bsegs m1 m /\
  rw_cells bsegs m SPA (frm19 v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144) /\
  f16arr bsegs m (F + 32) 16 cnt /\ f16arr bsegs m (F + 96) 16 offs /\
  f16arr bsegs m (S + 168) 320 lf /\ f16arr bsegs m (S + 808) 288 wf /\ f32arr bsegs m (S + 1384) 1444 cf /\
  rw_cells bsegs m (S + 160) [C8 next] /\ rw_cells bsegs m PB [C4 bitsw].

End CANSEC1.

Ltac open_ctx CX :=
  let CX' := fresh "CXc" in pose proof CX as CX';
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  and_elim CX' 4%nat; intros G1 G2 G3 G4;
  and_elim G1 12%nat; intros F8 S8 SLO STOP FLO FTOP TOPS SPAS SPHI SEPFS PBR PB4;
  and_elim G2 7%nat; intros RFRM RF RS RSS RSF RI RTS;
  and_elim G3 4%nat; intros SHS SHC SHO SHT;
  and_elim G4 4%nat; intros DJS DJC DJO DJT;
  unfold itb_W in DJS, DJC, DJO, DJT.
Ltac open_inv H :=
  destruct H as (MI & MU & WM & FRM & CNT & OFFS & LENS & WORK & CDS & NEXT & BITS);
  unfold itb_W in MU; unfold frm19 in FRM.

Lemma fupd_arr_set : forall (a : arr) i v j, 0 <= i < arr_len a -> fupd (arr_get a) i v j = arr_get (arr_set a i v) j.
Proof.
  intros a i v j H. unfold fupd. destruct (Z.eqb_spec j i) as [->|NE].
  - rewrite arr_get_set_same by exact H. reflexivity.
  - rewrite arr_get_set_other by (intros E; apply NE; symmetry; exact E). reflexivity.
Qed.
Ltac close_inv := unfold itb_inv, itb_W, frm19; do 10 (split; [assumption|]); assumption.

Ltac ubg :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
      replace (if c then a else b) with b
        by (let K := fresh "K" in destruct c eqn:K; [exfalso; zify_cond K; rewrite ?fub_land7, ?fub_land3, ?fub_land1 in K; rewrite ?lnot64 in K by lia; first [ lia | Z.div_mod_to_equations; lia ] | reflexivity])
  | |- _ => idtac
  end.
