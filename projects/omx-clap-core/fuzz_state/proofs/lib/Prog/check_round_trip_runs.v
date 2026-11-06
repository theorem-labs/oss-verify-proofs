(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import strlen_c strcmp_c bcmp_c pj_object_c pj_get_c
  pj_get_str_c check_round_trip_loops.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec WriterSpecFacts B64Canon HState.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct.
Import ListNotations.
Open Scope Z_scope.

Lemma crt_r0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 336 <= bv_unsigned sp -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x138f4) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp t0 t1 t2 s0 s1
                    a1 a2 a2 a3 a4 a5 a6 a7 s2 a2 a1 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14d10) fc None m' (seg_rom rsegs) /\
      rw_cells rsegs m' (bv_unsigned sp + -88)
        [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
      munch [(bv_unsigned sp + -336, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x138ac) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO MI.
  pose proof (munch_refl [(bv_unsigned sp + -336, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 88%nat ST.
  do 18 zstep.
  apply evt_done. exists m0. split; [reflexivity|].
  exact (conj FR (conj MU (conj WM MI))).
Qed.

Lemma crt_land_m4 : forall a, 0 <= a < 2 ^ 64 -> Z.land a 18446744073709551612 = a / 4 * 4.
Proof.
  intros a Ha. replace 18446744073709551612 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 2))) by reflexivity.
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma crt_div3 : forall x, 0 <= x < 2 ^ 61 ->
  Z.land (Z.shiftl (Z.shiftr (x * 12297829382473034411) 64 mod 18446744073709551616) 1 mod 18446744073709551616)
    18446744073709551612 = x / 3 * 4.
Proof.
  intros x Hx. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 1) with 2.
  assert (H : 2 * (x / 3) <= x * 12297829382473034411 / 18446744073709551616 <= 2 * (x / 3) + 1)
    by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (x * 12297829382473034411 / 18446744073709551616)) by lia.
  rewrite (Z.mod_small (x * 12297829382473034411 / 18446744073709551616 * 2)) by lia.
  rewrite crt_land_m4 by lia.
  Z.div_mod_to_equations; lia.
Qed.

Lemma crt_r1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (l : Z),
  s3 = Z_to_bv 64 l -> 0 <= l < 2 ^ 60 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists a1' : word,
      ms' = MS (mkR (Z_to_bv 64 0x13918) sp gp tp t0 t1 t2 a0 s1
                    (Z_to_bv 64 ((l + 2) / 3 * 4 + 1)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
                    (Z_to_bv 64 ((l + 2) / 3 * 4)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x16594) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x138f4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m l
    -> Hl MI.
  do 9 zstep.
  rewrite (crt_div3 (l + 2)) by lia.
  apply evt_done. eexists. reflexivity.
Qed.

Lemma crt_r2 : strlen_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t : Z) (tb slack : list byte),
  s5 = Z_to_bv 64 t -> 0 <= t < 2 ^ 64 ->
  bytes_at rsegs m t (tb ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) tb ->
  (- (t + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x1392c) sp gp tp t0' t1' t2' s0 a0
                    (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.of_nat (length tb))) + 1)) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x16594) fc None m' (seg_rom rsegs) /\
      munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13918) fc None m (seg_rom rsegs)).
Proof.
  intros STRLEN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    t tb slack -> Ht TB NZ SL MI.
  do 3 zstep.
  eapply evt_cut.
  { eapply STRLEN; [rewrite unsigned_lit by lia; exact TB | exact NZ | rewrite unsigned_lit by lia; exact SL | exact MI]. }
  intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m1 & -> & MU & WM & MI1 & _).
  replace (ret_pc (Z_to_bv 64 0x13924)) with (Z_to_bv 64 0x13924) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  do 2 zstep.
  apply evt_done. do 14 eexists. exists m1. split; [reflexivity|]. exact (conj MU (conj WM MI1)).
Qed.

Lemma crt_enc_nz : forall bs, bytes_ok bs -> ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) (b64_enc bs)).
Proof.
  intros bs Hb H. apply in_map_iff in H as (c & E & Hc).
  pose proof (proj1 (Forall_forall _ _) (b64_enc_chars bs Hb) c Hc) as Hr. cbv beta in Hr.
  assert (U : bv_unsigned (Z_to_bv 8 c) = c).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. }
  rewrite E in U. change (bv_unsigned (Z_to_bv 8 0)) with 0 in U. lia.
Qed.

Lemma crt_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Ltac crt_if :=
  repeat match goal with
  | |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (crt_eqb_lit x y) by lia
  | |- context [Z.eqb ?x ?y] => first [ rewrite (proj2 (Z.eqb_neq x y)) by lia | rewrite (proj2 (Z.eqb_eq x y)) by lia ]
  end; cbv iota.

Ltac zb := zstep; try crt_if; first [ if_true | if_false | idtac ].

Ltac crt_call SPEC tac :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC; tac | post_call segs m ] end.

Lemma crt_zs_ok : forall l : list byte, bytes_ok (map bv_unsigned l).
Proof.
  intros l. unfold bytes_ok. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (c & <- & _).
  pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma crt_r3d : strcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q want : Z) (eb : list byte),
  s0 = Z_to_bv 64 q -> s1 = Z_to_bv 64 want -> 0 <= q < 2 ^ 64 -> 0 <= want < 2 ^ 64 ->
  bv_unsigned sp + 16 <= 2 ^ 64 ->
  bytes_at rsegs m q (eb ++ [Z_to_bv 8 0]) -> bytes_at rsegs m want (eb ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) eb ->
  evt rsegs (fun ms' => exists a2' a3' : word,
      ms' = MS (mkR (Z_to_bv 64 0x13b64) sp gp tp t0 t1 t2 s0 s1 s0 (Z_to_bv 64 (bv_unsigned sp + 8))
                    a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14e90) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b48) fc None m (seg_rom rsegs)).
Proof.
  intros STRCMP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m q want eb -> -> Hq Hw Hsp TX WT NZ.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 3 zstep.
  eapply evt_cut.
  { eapply STRCMP; [rewrite unsigned_lit by lia; exact TX | exact NZ | rewrite unsigned_lit by lia; exact WT | exact NZ]. }
  intros ms' (r & x11 & x12 & x13 & -> & HR).
  assert (R0 : r = Z_to_bv 64 0) by (apply HR; reflexivity). subst r.
  replace (ret_pc (Z_to_bv 64 0x13b54)) with (Z_to_bv 64 0x13b54) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  do 4 zb.
  apply evt_done. do 2 eexists. reflexivity.
Qed.


Lemma crt_r3 : strlen_contract -> strcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (q want same b t l : Z) (db tb slq j8 jw js : list byte),
  s0 = Z_to_bv 64 q -> s1 = Z_to_bv 64 want -> a0 = Z_to_bv 64 same -> s3 = Z_to_bv 64 l -> s4 = Z_to_bv 64 b ->
  s5 = Z_to_bv 64 t -> s6 = Z_to_bv 64 ((l + 2) / 3 * 4) ->
  0 < q < 2 ^ 64 -> 0 < want < 2 ^ 64 -> 0 < same < 2 ^ 64 -> 0 <= b -> 0 <= t ->
  bv_unsigned sp + 16 <= 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned sp + 8) [CB 8 j8] ->
  bytes_at rsegs m q (map (Z_to_bv 8) (b64_enc (map bv_unsigned db)) ++ Z_to_bv 8 0 :: slq) ->
  (- (q + (l + 2) / 3 * 4 + 1)) mod 8 <= Z.of_nat (length slq) ->
  rw_cells rsegs m want [CB (Z.to_nat ((l + 2) / 3 * 4 + 1)) jw] ->
  rw_cells rsegs m same [CB (S (length tb)) js] ->
  bytes_at rsegs m b db -> Z.of_nat (length db) = l -> l < 2 ^ 60 ->
  bytes_at rsegs m t (tb ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) tb -> b64_dec (zs tb) = Some (map bv_unsigned db) ->
  want + ((l + 2) / 3 * 4 + 1) <= b \/ b + l <= want ->
  want + ((l + 2) / 3 * 4 + 1) <= q \/ q + ((l + 2) / 3 * 4 + 1) + Z.of_nat (length slq) <= want ->
  same + Z.of_nat (length tb) + 1 <= t \/ t + Z.of_nat (length tb) + 1 <= same ->
  same + Z.of_nat (length tb) + 1 <= q \/ q + ((l + 2) / 3 * 4 + 1) + Z.of_nat (length slq) <= same ->
  same + Z.of_nat (length tb) + 1 <= want \/ want + ((l + 2) / 3 * 4 + 1) <= same ->
  want + ((l + 2) / 3 * 4 + 1) <= t \/ t + Z.of_nat (length tb) + 1 <= want ->
  q + ((l + 2) / 3 * 4 + 1) + Z.of_nat (length slq) <= bv_unsigned sp + 8 ->
  want + ((l + 2) / 3 * 4 + 1) <= bv_unsigned sp + 8 -> same + Z.of_nat (length tb) + 1 <= bv_unsigned sp + 8 ->
  b + l <= bv_unsigned sp + 8 -> t + Z.of_nat (length tb) + 1 <= bv_unsigned sp + 8 ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' s5' s7' s8' s9' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x13b64) sp gp tp t0' t1' t2' s0 s1 s0 (Z_to_bv 64 (bv_unsigned sp + 8))
                    a2' a3' a4' a5' a6' a7' (Z_to_bv 64 same) s3 s4 s5' s6 s7' s8' s9' s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x14e90) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp + 8, bv_unsigned sp + 16); (want, want + ((l + 2) / 3 * 4 + 1));
             (same, same + Z.of_nat (length tb) + 1)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1392c) fc None m (seg_rom rsegs)).
Proof.
  intros STRLEN STRCMP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m q want same b t l db tb slq j8 jw js -> -> -> -> -> -> -> Hq Hw Hs Hb Ht Hsp R8 TXT SLQ RW RS DATA HN HL
    TB NZ DEC D1 D2 D3 D4 D5 D6 E1 E2 E3 E4 E5 MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (HEB : Z.of_nat (length (map (Z_to_bv 8) (b64_enc (map bv_unsigned db)))) = (l + 2) / 3 * 4).
  { rewrite length_map, enc_len_Z, length_map. rewrite HN. reflexivity. }
  assert (HZ : Z.of_nat (Z.to_nat ((l + 2) / 3 * 4 + 1)) = (l + 2) / 3 * 4 + 1).
  { rewrite Z2Nat.id; [reflexivity | Z.div_mod_to_equations; lia]. }
  pose proof (munch_refl [(bv_unsigned sp + 8, bv_unsigned sp + 16); (want, want + ((l + 2) / 3 * 4 + 1));
             (same, same + Z.of_nat (length tb) + 1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 zb.
  crt_call crt_expected_text ltac:(first [exact HN | exact HL | exact DATA | exact RW | exact D1 | exact MI]).
  zb. do 2 zstep.
  crt_call STRLEN ltac:(first [rewrite unsigned_lit by lia; exact TXT | apply crt_enc_nz, crt_zs_ok |
    rewrite unsigned_lit by lia; rewrite HEB; exact SLQ | assumption]).
  zb.
  crt_call crt_canonical ltac:(first [exact NZ | exact TB | exact RS | exact D3 | assumption]).
  match goal with H : rw_cells _ _ want _ |- _ => destruct H as [[_ WB] _] end.
  cbn [cells_bytes cbytes] in WB. rewrite app_nil_r in WB.
  replace (map (Z_to_bv 8) (b64_enc (map bv_unsigned db)) ++ Z_to_bv 8 0 :: slq)
    with ((map (Z_to_bv 8) (b64_enc (map bv_unsigned db)) ++ [Z_to_bv 8 0]) ++ slq) in TXT
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in TXT. destruct TXT as [TXT _].
  destruct (Z.eq_dec (Z.of_nat (length (b64_strip (map bv_unsigned tb))) mod 4) 0) as [H4|H4].
  - match goal with H : rw_cells _ _ same _ |- _ => destruct H as [[_ SB] _] end.
    cbn [cells_bytes cbytes] in SB. apply bytes_at_app in SB. destruct SB as [SB _].
    assert (EQ : map (Z_to_bv 8) (b64_strip (map bv_unsigned tb)) = map (Z_to_bv 8) (b64_enc (map bv_unsigned db))).
    { f_equal. apply (canonical_enc (zs tb)); [exact DEC | exact H4]. }
    rewrite EQ in SB.
    zb. do 3 zstep.
    eapply evt_cut.
    { eapply STRCMP; [rewrite unsigned_lit by lia; exact TXT | apply crt_enc_nz, crt_zs_ok |
        rewrite unsigned_lit by lia; exact SB | apply crt_enc_nz, crt_zs_ok]. }
    intros ms' (r & y11 & y12 & y13 & -> & HR).
    assert (R0 : r = Z_to_bv 64 0) by (apply HR; reflexivity). subst r.
    replace (ret_pc (Z_to_bv 64 0x13b44)) with (Z_to_bv 64 0x13b44) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zb.
    eapply evt_mono; [eapply crt_r3d; [exact STRCMP | reflexivity | reflexivity | lia | lia | exact Hsp | exact TXT |
      exact WB | apply crt_enc_nz, crt_zs_ok] |].
    intros ms' (a2' & a3' & ->). do 17 eexists. eexists. split; [reflexivity|].
    split; [eassumption|]. split; eassumption.
  - zb.
    eapply evt_mono; [eapply crt_r3d; [exact STRCMP | reflexivity | reflexivity | lia | lia | exact Hsp | exact TXT |
      exact WB | apply crt_enc_nz, crt_zs_ok] |].
    intros ms' (a2' & a3' & ->). do 17 eexists. eexists. split; [reflexivity|].
    split; [eassumption|]. split; eassumption.
Qed.

Lemma crt_mm_refl : forall (l : list byte) n, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|a l] H; cbn in *; try reflexivity; try lia.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

Definition crt_obj : list byte := le4 (Z_to_bv 64 6) ++ repeat (Z_to_bv 8 0) 52.

Lemma crt_r4t : pj_object_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (x : word) (j16 : list byte),
  rw_cells rsegs m (bv_unsigned sp + 8) [C8 x; CB 8 j16] ->
  wr_at rsegs m (bv_unsigned sp + 136) 56 -> wr_at rsegs m (bv_unsigned sp + 192) 56 ->
  bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
  bv_unsigned sp + 336 <= 2 ^ 64 ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x13bb0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (bv_unsigned sp + 80))
                    (Z_to_bv 64 0x1037a) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3' t4' t5' t6')
               F (Z_to_bv 64 0x14890) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned sp + 16, bv_unsigned sp + 24);
             (bv_unsigned sp + 136, bv_unsigned sp + 248)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo (bv_unsigned sp) /\
      bytes_at rsegs m' (bv_unsigned sp + 136) crt_obj /\ bytes_at rsegs m' (bv_unsigned sp + 192) crt_obj)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b8c) fc None m (seg_rom rsegs)).
Proof.
  intros PJO ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo x j16 R8 W1 W2 Hal ST Hlo Hsp MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned sp + 16, bv_unsigned sp + 24);
             (bv_unsigned sp + 136, bv_unsigned sp + 248)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 3 zstep.
  crt_call PJO ltac:(first [reflexivity | lia | exact W2 | exact Hal | exact ST | right; lia | exact MI |
    Z.div_mod_to_equations; lia]).
  do 2 zstep.
  crt_call PJO ltac:(first [reflexivity | lia | exact W1 | exact Hal | eassumption | right; lia |
    Z.div_mod_to_equations; lia]).
  do 4 zstep.
  apply evt_done. do 13 eexists. eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma crt_r4 : bcmp_contract -> pj_object_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (back b l lo : Z) (db j16 : list byte),
  a0 = Z_to_bv 64 back -> s3 = Z_to_bv 64 l -> s4 = Z_to_bv 64 b ->
  0 < back < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= l < 2 ^ 60 -> Z.of_nat (length db) = l ->
  bytes_at rsegs m back db -> bytes_at rsegs m b db ->
  rw_cells rsegs m (bv_unsigned sp + 8) [C8 (Z_to_bv 64 l); CB 8 j16] ->
  wr_at rsegs m (bv_unsigned sp + 136) 56 -> wr_at rsegs m (bv_unsigned sp + 192) 56 ->
  bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
  bv_unsigned sp + 336 <= 2 ^ 64 ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x13bb0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (bv_unsigned sp + 80))
                    (Z_to_bv 64 0x1037a) a2' a3' a4' a5' a6' a7' s2 s3 s4 (Z_to_bv 64 back) s6 s7 s8 s9 s10 s11
                    t3' t4' t5' t6')
               F (Z_to_bv 64 0x14890) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned sp + 16, bv_unsigned sp + 24);
             (bv_unsigned sp + 136, bv_unsigned sp + 248)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo (bv_unsigned sp) /\
      bytes_at rsegs m' (bv_unsigned sp + 136) crt_obj /\ bytes_at rsegs m' (bv_unsigned sp + 192) crt_obj)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b64) fc None m (seg_rom rsegs)).
Proof.
  intros BCMP PJO ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m back b l lo db j16 -> -> -> Hbk Hb Hl HN BK DB R8 W1 W2 Hal ST Hlo Hsp MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 4 zb.
  destruct (Z.eq_dec l 0) as [L0|L0].
  - subst l. zb.
    eapply (crt_r4t PJO); eassumption.
  - zb. do 4 zstep.
    eapply evt_cut.
    { eapply BCMP with (v := 0); [rewrite unsigned_lit by lia; exact BK | rewrite unsigned_lit by lia; exact DB |
        rewrite unsigned_lit by lia; apply crt_mm_refl; lia | exact MI]. }
    intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m1 & -> & MU & WM & MI1 & _ & _).
    replace (ret_pc (Z_to_bv 64 0x13b88)) with (Z_to_bv 64 0x13b88) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zb.
    eapply evt_mono; [eapply (crt_r4t PJO) with (lo := lo) (x := Z_to_bv 64 l) (j16 := j16) (m := m1) |].
    + apply (rw_cells_transport rsegs [] m m1); [exact R8 | exact MU | exact WM | exact I].
    + exact (wr_at_transport rsegs m m1 _ _ W1 WM).
    + exact (wr_at_transport rsegs m m1 _ _ W2 WM).
    + exact Hal.
    + apply (stk_transport_disjoint rsegs [] m m1); [exact ST | exact MU | exact WM | exact I].
    + exact Hlo.
    + exact Hsp.
    + exact MI1.
    + intros ms' (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & m2 & -> & MU2 & WM2 & PO).
      do 13 eexists. exists m2. split; [reflexivity|].
      split; [|split; [exact (wmono_trans rsegs m m1 m2 WM WM2) | exact PO]].
      apply (munch_trans _ m m1 m2); [| exact MU2]. eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside].
      intros; exact I.
Qed.

Lemma crt_r5 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 -> bv_unsigned sp + 336 <= 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13bc8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 192)) (Z_to_bv 64 0x1036e) (Z_to_bv 64 (bv_unsigned sp + 80)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14718) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13bb0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m -> Hsp.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 6 zb. apply evt_done. reflexivity.
Qed.

Lemma crt_r6 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 -> bv_unsigned sp + 336 <= 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13bdc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 80)) (Z_to_bv 64 0x102f8) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14890) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13bc8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m -> Hsp.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 5 zb. apply evt_done. reflexivity.
Qed.

Lemma crt_r7 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 -> bv_unsigned sp + 336 <= 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13bf4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 192)) (Z_to_bv 64 0x102ba) (Z_to_bv 64 (bv_unsigned sp + 80)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14718) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13bdc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m -> Hsp.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 6 zb. apply evt_done. reflexivity.
Qed.

Lemma crt_r8 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 -> bv_unsigned sp + 336 <= 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13c08) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 80)) (Z_to_bv 64 0x103c5) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14890) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13bf4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m -> Hsp.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 5 zb. apply evt_done. reflexivity.
Qed.

Lemma crt_r9 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 -> bv_unsigned sp + 336 <= 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13c20) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 136)) (Z_to_bv 64 0x102aa) (Z_to_bv 64 (bv_unsigned sp + 80)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14718) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c08) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m -> Hsp.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 6 zb. apply evt_done. reflexivity.
Qed.

Lemma crt_r10 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 -> bv_unsigned sp + 336 <= 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13c34) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 80)) (Z_to_bv 64 0x102b3) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14890) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c20) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m -> Hsp.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 5 zb. apply evt_done. reflexivity.
Qed.

Lemma crt_r11 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 -> bv_unsigned sp + 336 <= 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13c4c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 136)) (Z_to_bv 64 0x102c2) (Z_to_bv 64 (bv_unsigned sp + 80)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14718) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c34) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m -> Hsp.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 6 zb. apply evt_done. reflexivity.
Qed.

Lemma crt_r12 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 -> bv_unsigned sp + 336 <= 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13c5c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 80)) s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14890) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c4c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m -> Hsp.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 4 zb. apply evt_done. reflexivity.
Qed.

Lemma crt_r13 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 -> bv_unsigned sp + 336 <= 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13c74) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 136)) (Z_to_bv 64 0x103fc) (Z_to_bv 64 (bv_unsigned sp + 80)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14718) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c5c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m -> Hsp.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 6 zb. apply evt_done. reflexivity.
Qed.

Lemma crt_r14 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 -> bv_unsigned sp + 336 <= 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13c8c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 192)) (Z_to_bv 64 0x102f8) (Z_to_bv 64 (bv_unsigned sp + 136)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14718) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c74) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m -> Hsp.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 6 zb. apply evt_done. reflexivity.
Qed.

Lemma crt_r15 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 -> bv_unsigned sp + 336 <= 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13c9c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 192)) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14928) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c8c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m -> Hsp.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 4 zb. apply evt_done. reflexivity.
Qed.

Lemma crt_r16 : strlen_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (doc slack : list byte),
  a0 = Z_to_bv 64 p -> 0 < p < 2 ^ 64 -> bv_unsigned sp + 336 <= 2 ^ 64 ->
  bytes_at rsegs m p (doc ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) doc ->
  (- (p + Z.of_nat (length doc) + 1)) mod 8 <= Z.of_nat (length slack) -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x13cb8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 p)
                    (Z_to_bv 64 (Z.of_nat (length doc))) (Z_to_bv 64 (bv_unsigned sp + 24)) a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 (Z_to_bv 64 p) s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1428c) fc None m' (seg_rom rsegs) /\
      munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c9c) fc None m (seg_rom rsegs)).
Proof.
  intros STRLEN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p doc slack -> Hp Hsp TX NZ SL MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 3 zb.
  eapply evt_cut.
  { eapply STRLEN; [rewrite unsigned_lit by lia; exact TX | exact NZ | rewrite unsigned_lit by lia; exact SL | exact MI]. }
  intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m1 & -> & MU & WM & MI1 & _).
  replace (ret_pc (Z_to_bv 64 0x13ca8)) with (Z_to_bv 64 0x13ca8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  do 4 zstep.
  apply evt_done. do 12 eexists. exists m1. split; [reflexivity|]. exact (conj MU (conj WM MI1)).
Qed.

Definition CRT_STATE : list Z := [115; 116; 97; 116; 101].
Definition CRT_BYTES : list Z := [98; 121; 116; 101; 115].

Lemma crt_lit : forall m a (s : list Z), mem_inv rsegs m -> Forall (fun c => 0 < c < 256) s ->
  0 <= a -> a + Z.of_nat (length s) + 1 <= 2 ^ 64 ->
  (forall i, (i < length (s ++ [0%Z]))%nat ->
     ro_addr rsegs (wa (a + Z.of_nat i)) = true /\
     seg_rom rsegs (wa (a + Z.of_nat i)) = nth_error (map (Z_to_bv 8) (s ++ [0])) i) ->
  pj_cbytes rsegs m a s.
Proof.
  intros m a s MI HF H0 H1 H. split; [exact HF|]. split; [exact H0|].
  split; [rewrite length_map, length_app; cbn [length]; lia|].
  intros i Hi. rewrite length_map in Hi. destruct (H i Hi) as [Hro Hr].
  unfold mrd. destruct (m (wa (a + Z.of_nat i))) as [b|] eqn:E; [|exact Hr].
  rewrite (MI _ b E) in Hro. discriminate.
Qed.

Lemma crt_cb_state : forall m, mem_inv rsegs m -> pj_cbytes rsegs m 0x102f8 CRT_STATE.
Proof.
  intros m MI. apply crt_lit; [exact MI | unfold CRT_STATE; repeat constructor; lia | lia | cbn; lia |].
  intros i Hi. cbn [length CRT_STATE app] in Hi.
  do 6 (destruct i as [|i]; [split; vm_compute; reflexivity|]). lia.
Qed.

Lemma crt_cb_bytes : forall m, mem_inv rsegs m -> pj_cbytes rsegs m 0x103fc CRT_BYTES.
Proof.
  intros m MI. apply crt_lit; [exact MI | unfold CRT_BYTES; repeat constructor; lia | lia | cbn; lia |].
  intros i Hi. cbn [length CRT_BYTES app] in Hi.
  do 6 (destruct i as [|i]; [split; vm_compute; reflexivity|]). lia.
Qed.

Lemma crt_first_uniq : forall {X : Type} (ms : list (list Z * X)) k i i' v v',
  nth_error ms i = Some (k, v) -> (forall j nm u, (j < i)%nat -> nth_error ms j = Some (nm, u) -> nm <> k) ->
  nth_error ms i' = Some (k, v') -> (forall j nm u, (j < i')%nat -> nth_error ms j = Some (nm, u) -> nm <> k) ->
  i = i' /\ v = v'.
Proof.
  intros X ms k i i' v v' H1 F1 H2 F2.
  destruct (Nat.lt_trichotomy i i') as [L|[E|L]].
  - exfalso. exact (F2 i k v L H1 eq_refl).
  - subst i'. rewrite H1 in H2. injection H2 as ->. split; reflexivity.
  - exfalso. exact (F1 i' k v' L H2 eq_refl).
Qed.

Lemma crt_obj_kids : forall m lblk p ms D i nm v,
  pj_node rsegs m lblk p (JObj ms) D -> nth_error ms i = Some (nm, v) ->
  exists kids cap, pj_u64 rsegs m (p + 24) kids /\ Z.of_nat i < cap /\ lblk kids (56 * cap).
Proof.
  intros m lblk p ms D i nm v H Hi. cbn [pj_node tag] in H.
  destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & _ & Hn & Hc & Hk & _).
  assert (Hl : (i < length ms)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  destruct Hh as (_ & _ & _ & _ & Hkids & _).
  exists kids, cap. split; [exact Hkids|].
  destruct Hk as [(C0 & _) | (C & L & _)]; [lia|]. split; [lia | exact L].
Qed.

Lemma crt_r17 : pj_get_contract -> pj_get_str_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lblk : Z -> Z -> Prop)
    (lo : Z) (ms ms2 : list (list Z * jv)) (D : list (Z * Z)) (i j : nat) (s : list Z),
  a0 = Z_to_bv 64 0 -> bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> 0x55000 <= lo ->
  lo + 64 <= bv_unsigned sp -> bv_unsigned sp + 336 <= 2 ^ 64 ->
  pj_node rsegs m lblk (bv_unsigned sp + 24) (JObj ms) D ->
  nth_error ms i = Some (CRT_STATE, JObj ms2) ->
  (forall j' nm u, (j' < i)%nat -> nth_error ms j' = Some (nm, u) -> nm <> CRT_STATE) ->
  nth_error ms2 j = Some (CRT_BYTES, JStr s) ->
  (forall j' nm u, (j' < j)%nat -> nth_error ms2 j' = Some (nm, u) -> nm <> CRT_BYTES) ->
  (forall a n, lblk a n -> 0 < a /\ a mod 8 = 0 /\ a + n <= 2 ^ 47 /\ a + n <= lo) ->
  (forall a n, In (a, n) D -> lblk a n) ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' z n,
      ms' = MS (mkR (Z_to_bv 64 0x13ce4) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 z)
                    (Z_to_bv 64 (bv_unsigned sp + 16)) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3' t4' t5' t6')
               F (Z_to_bv 64 0x14e90) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo (bv_unsigned sp) /\ pj_node rsegs m' lblk (bv_unsigned sp + 24) (JObj ms) D /\
      pj_cstr rsegs m' lblk z n s /\ In (z, n) D)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13cb8) fc None m (seg_rom rsegs)).
Proof.
  intros PJG PJGS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lblk lo ms ms2 D i j s -> Hal ST Hlo Hlo2 Hsp ND Hi Fi Hj Fj LB LD MI.
  unfold pj_get_contract in PJG. unfold pj_get_str_contract in PJGS.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  destruct (crt_obj_kids m lblk _ ms D i _ _ ND Hi) as (kids & cap & HK & Hic & LK).
  destruct (LB _ _ LK) as (LK1 & _ & LK3 & LK4).
  zb. do 4 zstep.
  eapply evt_cut.
  { eapply PJG with (lblk := lblk) (o := bv_unsigned sp + 24) (k := 0x102f8) (kname := CRT_STATE) (t := JObj ms)
      (D := D) (lo := lo).
    - reflexivity.
    - reflexivity.
    - right. exact ND.
    - apply crt_cb_state. exact MI.
    - intros a n Hl. destruct (LB a n Hl) as (H1 & H2 & H3 & H4). split; [lia|]. split; [exact H2|].
      split; [lia|]. cbn [disjoint_from]. split; [lia | exact I].
    - exact Hal.
    - exact ST.
    - lia.
    - cbn [disjoint_from CRT_STATE length Z.of_nat]. split; [lia|]. split; [lia | exact I].
    - exact MI. }
  intros ms' (u0 & u1 & u2 & r & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m1 & -> & MU1 & WM1 &
    MI1 & ST1 & _ & RES1).
  destruct RES1 as [(E0 & _) | (_ & ND1 & z & -> & HR)]; [lia|].
  cbn [pj_get_res] in HR.
  destruct HR as [(ABS & _) | (i' & v & kids' & Di & Hi' & Fi' & HK' & -> & NDz & INC)].
  { exfalso. exact (ABS CRT_STATE (JObj ms2) (nth_error_In _ _ Hi) eq_refl). }
  destruct (crt_first_uniq ms CRT_STATE i i' _ _ Hi Fi Hi' Fi') as [<- <-].
  assert (HK1 : pj_u64 rsegs m1 (bv_unsigned sp + 24 + 24) kids).
  { destruct HK as [HKr HKb]. split; [exact HKr|].
    apply (bytes_at_transport rsegs [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 _ _ HKb MU1).
    rewrite length_le8. cbn [disjoint_from]. split; [lia | exact I]. }
  pose proof (pj_u64_uniq rsegs _ _ _ _ HK1 HK') as <-.
  replace (ret_pc (Z_to_bv 64 0x13ccc)) with (Z_to_bv 64 0x13ccc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  do 3 zstep.
  eapply evt_cut.
  { eapply PJGS with (lblk := lblk) (o := kids + 56 * Z.of_nat i) (k := 0x103fc) (kname := CRT_BYTES) (t := JObj ms2)
      (D := Di) (lo := lo).
    - reflexivity.
    - reflexivity.
    - right. exact NDz.
    - apply crt_cb_bytes. exact MI1.
    - intros a n Hl. destruct (LB a n Hl) as (H1 & H2 & H3 & H4). split; [lia|]. split; [exact H2|].
      split; [lia|]. cbn [disjoint_from]. split; [lia | exact I].
    - exact Hal.
    - exact ST1.
    - lia.
    - cbn [disjoint_from CRT_BYTES length Z.of_nat]. split; [lia|]. split; [lia | exact I].
    - exact MI1. }
  intros ms' (w0 & w1 & w2 & r2 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m2 & -> & MU2 & WM2 &
    MI2 & ST2 & _ & RES2).
  destruct RES2 as [(E0 & _) | (_ & ND2 & z2 & -> & HR2)]; [lia|].
  cbn [pj_get_str_res] in HR2.
  destruct HR2 as [(ABS & _) | (j' & v2 & kids2 & Hj' & Fj' & HK2 & HV)].
  { exfalso. exact (ABS CRT_BYTES (JStr s) (nth_error_In _ _ Hj) eq_refl). }
  destruct (crt_first_uniq ms2 CRT_BYTES j j' _ _ Hj Fj Hj' Fj') as [<- <-].
  destruct HV as (_ & n & CS & HIn).
  pose proof CS as (LZ & LN & _). destruct (LB _ _ LZ) as (Z1 & _ & Z3 & Z4).
  replace (ret_pc (Z_to_bv 64 0x13cd8)) with (Z_to_bv 64 0x13cd8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  zb. do 2 zstep.
  apply evt_done. do 13 eexists. exists m2, z2, n. split; [reflexivity|].
  split.
  { apply (munch_trans _ m m1 m2); [|exact MU2]. eapply munch_weaken; [|exact MU1].
    intros x Hx. cbn [outside] in Hx |- *. split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs m m1 m2 WM1 WM2)|].
  split; [exact MI2|]. split; [exact ST2|].
  split.
  { apply (pj_node_munch rsegs [(bv_unsigned sp - 64, bv_unsigned sp)] m1 lblk m2 lblk _ _ _ ND1 LD MU2).
    intros x [Hx | ([ba bk] & Hb & Hx)]; cbn [outside]; (split; [|exact I]).
    - lia.
    - unfold pj_holds in Hx. cbn [fst snd] in Hx. destruct (LB _ _ (LD _ _ Hb)) as (_ & _ & _ & B4). lia. }
  split; [exact CS | exact (INC _ HIn)].
Qed.

Lemma crt_r18 : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (back b l : Z) (db : list byte),
  a0 = Z_to_bv 64 back -> s3 = Z_to_bv 64 l -> s4 = Z_to_bv 64 b ->
  0 < back < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= l < 2 ^ 60 -> Z.of_nat (length db) = l ->
  bytes_at rsegs m back db -> bytes_at rsegs m b db ->
  ro_cells rsegs m (bv_unsigned sp + 16) [C8 (Z_to_bv 64 l)] ->
  bv_unsigned sp + 336 <= 2 ^ 64 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x13d14) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 back) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 (Z_to_bv 64 back) s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x141c4) fc None m' (seg_rom rsegs) /\
      munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ce4) fc None m (seg_rom rsegs)).
Proof.
  intros BCMP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m back b l db -> -> -> Hbk Hb Hl HN BK DB R16 Hsp MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  do 4 zb.
  destruct (Z.eq_dec l 0) as [L0|L0].
  - subst l. zb. do 2 zstep.
    apply evt_done. do 14 eexists. exists m. split; [reflexivity|]. exact (conj MU (conj WM MI)).
  - zb. do 4 zstep.
    eapply evt_cut.
    { eapply BCMP with (v := 0); [rewrite unsigned_lit by lia; exact BK | rewrite unsigned_lit by lia; exact DB |
        rewrite unsigned_lit by lia; apply crt_mm_refl; lia | exact MI]. }
    intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m1 & -> & MU1 & WM1 & MI1 & _ & _).
    replace (ret_pc (Z_to_bv 64 0x13d08)) with (Z_to_bv 64 0x13d08) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zb. do 2 zstep.
    apply evt_done. do 14 eexists. exists m1. split; [reflexivity|]. exact (conj MU1 (conj WM1 MI1)).
Qed.

Lemma crt_r19 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13d1c) sp gp tp t0 t1 t2 s0 s1 s6 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x141c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d14) fc None m (seg_rom rsegs)).
Proof. intros. do 2 zstep. apply evt_done. reflexivity. Qed.

Lemma crt_r20 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bv_unsigned sp + 336 <= 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13d24) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 24))
                                      a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x145a4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d1c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Hsp.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 2 zstep. apply evt_done. reflexivity.
Qed.

Lemma crt_r21 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bv_unsigned sp + 336 <= 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13d2c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 192))
                                      a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x145a4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d24) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Hsp.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 2 zstep. apply evt_done. reflexivity.
Qed.

Lemma crt_r22 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13d34) sp gp tp t0 t1 t2 s0 s1 s5 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x141c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d2c) fc None m (seg_rom rsegs)).
Proof. intros. do 2 zstep. apply evt_done. reflexivity. Qed.

Lemma crt_r23 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13d3c) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x141c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d34) fc None m (seg_rom rsegs)).
Proof. intros. do 2 zstep. apply evt_done. reflexivity. Qed.

Lemma crt_r24 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13d44) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x16454) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d3c) fc None m (seg_rom rsegs)).
Proof. intros. do 2 zstep. apply evt_done. reflexivity. Qed.

Lemma crt_r25 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13d4c) sp gp tp t0 t1 t2 s0 s1 s2 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x16454) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d44) fc None m (seg_rom rsegs)).
Proof. intros. do 2 zstep. apply evt_done. reflexivity. Qed.

Lemma crt_r26 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 : word),
  rw_cells rsegs m (bv_unsigned sp + 248)
    [C8 xs9; C8 xs8; C8 xs7; C8 xs6; C8 xs5; C8 xs4; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  bv_unsigned sp + 336 <= 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + 336)) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7
                                      xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 s10 s11 t3 t4 t5 t6)
               F (ret_pc xra) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d4c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 FR Hsp.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (rw_cells_bound rsegs m _ _ FR) as RB. cbn [cells_size csize Nat.add] in RB.
  do 13 zstep.
  apply evt_done. reflexivity.
Qed.
