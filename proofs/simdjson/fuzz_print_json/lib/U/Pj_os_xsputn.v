(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import F_memcpy F_memmove_t2 F_memcmp Pj_steps Pj_loc_defs Pj_loc_kit Pj_os_defs Pj_os_kit.
From OssFuzzTheorems.simdjson.fuzz_print_json.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Ltac br_is b tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (symmetry; tac) end; cbv_concl_iota.
Ltac show_reg k :=
  lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
    let v := eval cbv beta iota delta [tget] in (tget p R) in
    idtac "x" k "=" v
  end.
Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc end.

Lemma rw_cells_CB_cut3 : forall m A (n : nat) (bs : list byte) (a k : Z),
  (0 <= a)%Z -> (0 <= k)%Z -> (a + k <= Z.of_nat n)%Z -> rw_cells usegs m A [CB n bs] ->
  exists b1 b2 b3,
    rw_cells usegs m A [CB (Z.to_nat a) b1] /\ rw_cells usegs m (A + a) [CB (Z.to_nat k) b2]
    /\ rw_cells usegs m (A + a + k) [CB (n - Z.to_nat a - Z.to_nat k) b3].
Proof.
  intros m A n bs a k Ha Hk Hn H.
  apply (rw_cells_split_CB usegs _ _ [] n bs [] [Z.to_nat a; Z.to_nat k; (n - Z.to_nat a - Z.to_nat k)%nat]) in H; [|cbn; lia].
  cbn [mk_CB_cells app] in H.
  apply (proj1 (Startup_glue.rw_cells_app usegs m A [_] [_; _])) in H. destruct H as [H1 H].
  apply (proj1 (Startup_glue.rw_cells_app usegs m _ [_] [_])) in H. destruct H as [H2 H3].
  cbn [cells_size csize Nat.add] in H2, H3. rewrite ?Nat.add_0_r in H2, H3. rewrite ?Z2Nat.id in H2, H3 by lia.
  replace (A + a + Z.of_nat (Z.to_nat k + 0))%Z with (A + a + k)%Z in H3 by lia.
  do 3 eexists. split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

Lemma rw_cells_CB_join3 : forall m A (n1 n2 n3 n : nat) (b1 b2 b3 : list byte) A2 A3,
  rw_cells usegs m A [CB n1 b1] -> rw_cells usegs m A2 [CB n2 b2] -> rw_cells usegs m A3 [CB n3 b3] ->
  A2 = (A + Z.of_nat n1)%Z -> A3 = (A2 + Z.of_nat n2)%Z -> (n1 + n2 + n3 = n)%nat ->
  exists bs, rw_cells usegs m A [CB n bs].
Proof.
  intros m A n1 n2 n3 n b1 b2 b3 A2 A3 H1 H2 H3 -> -> E.
  assert (H23 : rw_cells usegs m (A + Z.of_nat n1) ([CB n2 b2] ++ [CB n3 b3])).
  { apply Startup_glue.rw_cells_app. split; [exact H2|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact H3. }
  assert (H123 : rw_cells usegs m A ([CB n1 b1] ++ [CB n2 b2; CB n3 b3])).
  { apply Startup_glue.rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact H23. }
  apply rw_cells_forget in H123. cbn [app cells_size csize Nat.add] in H123.
  replace (n1 + (n2 + (n3 + 0)))%nat with n in H123 by lia. exact H123.
Qed.

Lemma bytes_at_sub : forall m A (bs : list byte) (i k : Z), bytes_at usegs m A bs -> (0 <= i)%Z -> (0 <= k)%Z -> (i + k <= Z.of_nat (length bs))%Z ->
  bytes_at usegs m (A + i) (firstn (Z.to_nat k) (skipn (Z.to_nat i) bs)).
Proof.
  intros m A bs i k H Hi Hk Hl.
  rewrite <- (firstn_skipn (Z.to_nat i) bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia. rewrite Z2Nat.id in H by lia.
  rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat i) bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Definition mm_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at usegs m' Src src.

Lemma memmove_far_Z : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Dst Src N : Z) (src junk : list byte),
  bytes_at usegs m Src src -> length src = Z.to_nat N -> rw_cells usegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (1 <= N < 2^63)%Z -> (0 <= Src)%Z -> (Src + N < 2^63)%Z -> (0 <= Dst)%Z -> (Dst + N < 2^63)%Z -> mem_inv usegs m ->
  evt usegs (mm_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MEMMOVE_T2) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros BA LEN DC SEP HN HS HS2 HD HD2 MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply memmove_far_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA| exact LEN| exact DC| exact SEP| lia| exact MI]. }
  intros ms' P. unfold memcpy_post, mm_postZ in *. rewrite ED, ES, EN in P. exact P.
Qed.

Lemma lts_small : forall x y, (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y)%Z.
Proof.
  intros x y Hx Hy. rewrite bv_lts_lxor, !unsigned_lit by lia. rewrite !zb_lxor_pow2_small by lia.
  destruct (Z.ltb_spec x y), (Z.ltb_spec (x + 2^63) (y + 2^63)); lia.
Qed.

Section Loop.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo OS S N CAP : Z) (bs : list byte) (m0 : word -> option byte).
Hypothesis LO : (lo <= bv_unsigned sp - 64)%Z.
Hypothesis LOLO : (0x110000 <= lo)%Z.
Hypothesis RO : (bv_unsigned sp <= OS)%Z.
Hypothesis RO2 : (OS + 288 < 2^62)%Z.
Hypothesis RN : (0 <= N <= CAP)%Z.
Hypothesis RS : (0 <= S)%Z.
Hypothesis RS2 : (S + CAP < 2^62)%Z.
Hypothesis SEP : (S + CAP <= lo \/ OS + 288 <= S)%Z.
Hypothesis LBS : length bs = Z.to_nat CAP.

Definition PUTINV (pp ep : Z) : Prop := (pp = 0 /\ ep = 0)%Z \/ (ep = OS + 128 /\ OS + 64 <= pp <= OS + 128)%Z.
Notation POST := (os_xsputn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS N m0).
Notation W := [(bv_unsigned sp - 64, bv_unsigned sp); (OS + 40, OS + 128)]%Z.

Lemma xsputn_exit : forall (pp ep : Z) (pb : word) (dum jf : list byte) (m : word -> option byte)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x9 x18 x19 x20 x21 t3 t4 t5 t6 : word),
  munch W m0 m -> wmono usegs m0 m -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp + -64) ->
  rw_cells usegs m (bv_unsigned sp + -64) [CB 8 jf; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells usegs m OS [C8 (Z_to_bv 64 0xd5f08); C8 (Z_to_bv 64 0xed828); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                       C8 pb; C8 (Z_to_bv 64 pp); C8 (Z_to_bv 64 ep)] ->
  rw_cells usegs m (OS + 64) [CB 64 dum] ->
  evt usegs POST
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 N) x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x826a8) fc None m (seg_rom usegs)).
Proof using LO LOLO RO RO2 RN RS RS2 SEP LBS.
  intros until t6. intros MU WM MI ST FR SBH DUM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  do 10 lstep.
  release_frame FR ST (bv_unsigned sp).
  glueZ SBH DUM.
  unfold os_xsputn_post, sb_cells. sys_finish; eassumption.
Qed.

Lemma xsputn_loop : forall (k : nat) (done pp ep : Z) (pb : word) (dum jf : list byte) (m : word -> option byte)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word),
  (N - done <= Z.of_nat k)%Z -> (0 <= done < N)%Z -> PUTINV pp ep ->
  munch W m0 m -> wmono usegs m0 m -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp + -64) ->
  rw_cells usegs m (bv_unsigned sp + -64) [CB 8 jf; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells usegs m OS [C8 (Z_to_bv 64 0xd5f08); C8 (Z_to_bv 64 0xed828); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                       C8 pb; C8 (Z_to_bv 64 pp); C8 (Z_to_bv 64 ep)] ->
  rw_cells usegs m (OS + 64) [CB 64 dum] ->
  bytes_at usegs m S bs ->
  rw_cells usegs m 0xd5f68 [C8 (Z_to_bv 64 0x825f8); C8 (Z_to_bv 64 0x3d9b0); C8 (Z_to_bv 64 8)] ->
  evt usegs POST
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 done) (Z_to_bv 64 N) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (S + done)) (Z_to_bv 64 OS) x20 (Z_to_bv 64 (-1)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x82648) fc None m (seg_rom usegs)).
Proof using LO LOLO RO RO2 RN RS RS2 SEP LBS.
  induction k as [|k IH]; intros done pp ep pb dum jf m x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6
    HK HD PI MU WM MI ST FR SBH DUM SRC VT; [lia|].
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  do 2 lstep.
  lstep.
  destruct (Z_lt_dec pp ep) as [LT|GE].
  2:{
    br_is true ltac:(rewrite bv_ltu_Z, !unsigned_lit by lia; apply negb_true_iff, Z.ltb_ge; lia).
    pose proof (ro_C1_of_bytes m (S + done) _ (bytes_at_nth m S bs done SRC ltac:(lia))) as CB0.
    assert (EU1 : bv_unsigned (Z_to_bv 64 (S + done)) = (S + done)%Z) by (apply unsigned_lit; lia).
    set (cs := (S + done)%Z) in *.
    set (b := nth (Z.to_nat done) bs (Z_to_bv 8 0)) in *.
    do 5 lstep.
    lstep.
    do 2 lstep.
    br_is false ltac:(rewrite bv_ltu_Z, !unsigned_lit by lia; change (bv_unsigned (Z_to_bv 64 (-64))) with 18446744073709551552%Z; apply negb_false_iff, Z.ltb_lt; lia).
    do 9 lstep.
    assert (RB : (0 <= bv_unsigned b < 256)%Z) by (pose proof (bv_unsigned_in_range 8 b) as X; unfold bv_modulus in X; cbn in X; lia).
    replace ((bv_unsigned b + 1) mod 18446744073709551616 <? 1)%Z with false by (symmetry; apply Z.ltb_ge; rewrite Z.mod_small by lia; lia).
    cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616)%Z with 18446744073709551615%Z.
    replace (Z.land 18446744073709551615 (bv_unsigned b)) with (bv_unsigned b)
      by (symmetry; rewrite Z.land_comm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
    lstep.
    lstep.
    br_is false ltac:(rewrite bv_eqb_Z, unsigned_lit by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615%Z; apply Z.eqb_neq; lia).
    do 2 lstep.
    lstep.
    subst cs.
    destruct (Z_lt_dec (done + 1) N) as [MORE|LAST].
    + br_is true ltac:(rewrite lts_small by lia; apply Z.ltb_lt; lia).
      replace (S + done + 1)%Z with (S + (done + 1))%Z by lia.
      eapply (IH (done + 1)%Z (OS + 64)%Z (OS + 128)%Z); try eassumption; [lia | lia | right; lia].
    + br_is false ltac:(rewrite lts_small by lia; apply Z.ltb_ge; lia).
      lstep.
      replace (done + 1)%Z with N by lia.
      eapply xsputn_exit; eassumption. }

  br_is false ltac:(rewrite bv_ltu_Z, !unsigned_lit by lia; apply negb_false_iff, Z.ltb_lt; lia).
  destruct PI as [[-> ->]|[-> PPR]]; [lia|].
  do 2 lstep.
  lstep.
  assert (CONT : forall (kz : Z) (y11 : word) (mm : word -> option byte), (1 <= kz <= N - done)%Z -> (kz <= OS + 128 - pp)%Z -> mm = m ->
    evt usegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 done) (Z_to_bv 64 N) (Z_to_bv 64 pp) y11 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (S + done)) (Z_to_bv 64 OS) (Z_to_bv 64 kz) (Z_to_bv 64 (-1)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x82664) fc None mm (seg_rom usegs))).
  { intros kz y11 mm K1 K2 ->.
    lstep.
    br_is false ltac:(rewrite bv_eqb_Z, unsigned_lit by lia; change (bv_unsigned z64) with 0%Z; apply Z.eqb_neq; lia).
    do 2 lstep.
    lstep.
    destruct (rw_cells_CB_cut3 m (OS + 64) 64 dum (pp - (OS + 64)) kz ltac:(lia) ltac:(lia) ltac:(lia) DUM) as (d1 & d2 & d3 & D1 & D2 & D3).
    replace (OS + 64 + (pp - (OS + 64)))%Z with pp in D2, D3 by lia.
    pose proof (bytes_at_sub m S bs done kz SRC ltac:(lia) ltac:(lia) ltac:(rewrite LBS; lia)) as SUB.
    clear DUM.
    change 852604%Z with MEMMOVE_T2.
    eapply evt_cut.
    { eapply (memmove_far_Z) with (Dst := pp) (Src := (S + done)%Z) (N := kz) (junk := d2);
        [exact SUB | rewrite firstn_length_le; [reflexivity | rewrite skipn_length, LBS; lia] | exact D2 | lia | lia | lia | lia | lia | lia | assumption]. }
    post_call usegs m.
    rename PC into D2. clear POST.
    do 2 lstep.
    do 4 lstep.
    lstep.
    lazymatch type of D2 with rw_cells _ ?mx _ _ =>
      destruct (rw_cells_CB_join3 mx (OS + 64) _ _ _ 64 _ _ _ pp (pp + kz)%Z D1 D2 D3 ltac:(lia) ltac:(lia) ltac:(lia)) as (dum' & DUM) end.
    clear D1 D2 D3.
    destruct (Z_lt_dec (kz + done) N) as [MORE|LAST].
    + br_is false ltac:(rewrite lts_small by lia; apply negb_false_iff, Z.ltb_lt; lia).
      replace (kz + done)%Z with (done + kz)%Z by lia.
      replace (S + done + kz)%Z with (S + (done + kz))%Z by lia.
      eapply (IH (done + kz)%Z (pp + kz)%Z (OS + 128)%Z); try eassumption; [lia | lia | right; lia].
    + br_is true ltac:(rewrite lts_small by lia; apply negb_true_iff, Z.ltb_ge; lia).
      replace (kz + done)%Z with N by lia.
      eapply xsputn_exit; eassumption. }
  destruct (Z_lt_dec (N - done) (OS + 128 - pp)) as [SM|BG].
  - br_is true ltac:(rewrite lts_small by lia; apply Z.ltb_lt; lia).
    eapply (CONT (N - done)%Z); [lia | lia | reflexivity].
  - br_is false ltac:(rewrite lts_small by lia; apply Z.ltb_ge; lia).
    lstep.
    eapply (CONT (OS + 128 - pp)%Z); [lia | lia | reflexivity].
Qed.

End Loop.

Theorem os_xsputn_proof : os_xsputn_stmt.
Proof.
  unfold os_xsputn_stmt. intros until bs. intros ST LO LOLO SBF RO RO2 SRC RN RS RS2 SEP VT MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (OS + 40, OS + 128)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  assert (LBS : length bs = Z.to_nat CAP) by (destruct SRC as [[[L _] _] _]; exact L).
  assert (SRB : bytes_at usegs m S bs) by (destruct SRC as [[_ B] _]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B; exact B).
  unfold sb_cells in SBF.
  takeZ SBF 8%nat (OS + 64)%Z SBH. rename SBF into DUM.
  carve_frame 64%nat ST.
  do 8 lstep.
  lstep.
  destruct (Z.eq_dec N 0) as [N0|N1].
  - subst N. if_true.
    lstep.
    eapply (xsputn_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS S 0 CAP bs m) with (pp := 0%Z) (ep := 0%Z); try eassumption; lia.
  - br_is false ltac:(rewrite bv_lts_zero_l, unsigned_lit by lia; cbn [negb]; apply negb_false_iff, andb_true_iff; split; apply Z.ltb_lt; lia).
    do 6 lstep.
    replace S with (S + 0)%Z at 2 by lia.
    eapply (xsputn_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS S N CAP bs m) with (k := Z.to_nat N) (done := 0%Z) (pp := 0%Z) (ep := 0%Z);
      try eassumption; try lia; left; lia.
Qed.
