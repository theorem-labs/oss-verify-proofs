(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import VerbsMem number_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma cw_ret : forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp ra0 s00 s01 s02 s03 s04 s05 s06 s07 s08 : word),
  rw_cells rsegs m (bv_unsigned sp + -80)
    [C8 s08; C8 s07; C8 s06; C8 s05; C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  (352 <= bv_unsigned sp)%Z ->
  evt rsegs
    (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s00 s01 a0 a1 a2 a3 a4 a5 a6 a7
                              s02 s03 s04 s05 s06 s07 s08 s9 s10 s11 t3 t4 t5 t6)
                         F (ret_pc ra0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -352)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17dd8) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp ra0 s00 s01 s02 s03 s04 s05 s06 s07 s08 FR SPR.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 12 step.
  apply evt_done. reflexivity.
Qed.

Lemma cw_ret2 : forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp ra0 s00 s01 s02 s03 s04 s05 s06 s07 s08 : word),
  rw_cells rsegs m (bv_unsigned sp + -80)
    [C8 s08; C8 s07; C8 s06; C8 s05; C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  (352 <= bv_unsigned sp)%Z ->
  evt rsegs
    (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s00 s01 a0 a1 a2 a3 a4 a5 a6 a7
                              s02 s03 s04 s05 s06 s07 s08 s9 s10 s11 t3 t4 t5 t6)
                         F (ret_pc ra0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -352)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17dcc) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp ra0 s00 s01 s02 s03 s04 s05 s06 s07 s08 FR SPR.
  step. exact (cw_ret ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp ra0 s00 s01 s02 s03 s04 s05 s06 s07 s08 FR SPR).
Qed.

Lemma cw_rej : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x17dd8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-902)) a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x15f34) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17dd0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step. apply evt_done. reflexivity.
Qed.

Lemma read_all : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  cbn [skipn Z.of_nat] in R. rewrite Z.add_0_r, firstn_all in R. exact R.
Qed.

Lemma cw_acc : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : word -> option byte) (sp : word) (id ntok : Z),
  bytes_at rsegs m (bv_unsigned sp + -84) (le4 (Z_to_bv 64 id)) ->
  (-2^31 <= id < 2^31)%Z -> (2 <= ntok <= 64)%Z ->
  (352 <= bv_unsigned sp)%Z ->
  evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x17dcc) (Z_to_bv 64 (bv_unsigned sp + -352)) gp tp t0 t1 t2
                              (Z_to_bv 64 ntok) s1 (Z_to_bv 64 id) (Z_to_bv 64 (bv_unsigned sp + -340))
                              (Z_to_bv 64 (ntok - 2)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x16e1c) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -352)) gp tp t0 t1 t2 (Z_to_bv 64 ntok) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17dbc) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp id ntok HI IDR NR SPR.
  pose proof (bytes_at_bound _ _ _ _ HI) as IB. rewrite length_le4 in IB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (read_all _ _ _ HI) as RD. rewrite length_le4 in RD.
  do 4 step.
  assert (A0 : sx32 (Z_to_bv 64 id) = Z_to_bv 64 id).
  { unfold sx32. rewrite unsigned_lit_wrap. f_equal.
    change (bv_swrap 32 ?z) with ((z + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31)%Z. Z.div_mod_to_equations. lia. }
  assert (A2 : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 ntok) + -2)) = Z_to_bv 64 (ntok - 2)).
  { rewrite unsigned_lit by lia. change (bv_swrap 32 ?z) with ((z + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31)%Z.
    rewrite Z.mod_small by lia. f_equal. lia. }
  rewrite A0, A2. apply evt_done. reflexivity.
Qed.

Lemma tle : forall bs : list byte, Z_to_le_bytes (length bs) (le_val (map bv_unsigned bs)) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length map le_val Z_to_le_bytes].
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8)%Z with 256%Z in Rb.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as Rv.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8)%Z. change (2^8)%Z with 256%Z.
    rewrite (Z.mul_comm 256), Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8)%Z with 256%Z.
    rewrite (Z.mul_comm 256), Z.div_add, Z.div_small, Z.add_0_l by lia. exact IH.
Qed.

Lemma le4_of : forall bs : list byte, length bs = 4%nat -> le4 (Z_to_bv 64 (le_val (map bv_unsigned bs))) = bs.
Proof.
  intros bs L. unfold le4. pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as R.
  rewrite length_map, L in R. change (256 ^ Z.of_nat 4)%Z with (2^32)%Z in R.
  rewrite unsigned_lit by lia. rewrite <- L. apply tle.
Qed.

Lemma errno_cell : forall m, wr_at rsegs m 0x3441c 4 -> exists ev, rw_cells rsegs m 0x3441c [C4 ev].
Proof.
  intros m W.
  set (f := fun i : nat => match mrd rsegs m (wa (0x3441c + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
  set (bs := [f 0%nat; f 1%nat; f 2%nat; f 3%nat]).
  assert (L : length bs = 4%nat) by reflexivity.
  exists (Z_to_bv 64 (le_val (map bv_unsigned bs))).
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, le4_of by exact L.
    split; [lia|]. split; [rewrite L; lia|]. intros i Hi. rewrite L in Hi.
    assert (C : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat) by lia.
    destruct C as [-> | [-> | [-> | ->]]]; cbn [nth_error bs]; unfold f;
      (destruct (mrd rsegs m _) as [b|] eqn:E; [reflexivity|]); exfalso; revert E; unfold mrd;
      (destruct (m _); [discriminate|]); vm_compute; discriminate.
  - exact W.
Qed.

Lemma rwc_split : forall m A B cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) -> B = (A + Z.of_nat (cells_size cs1))%Z ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A B cs1 cs2 [[Hwf Hb] (H0 & H1 & H2)] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app in H1, H2.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply H2. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply H2. lia.
Qed.

Lemma cb_split : forall m A (n1 n2 : nat) bs, rw_cells rsegs m A [CB (n1 + n2) bs] ->
  exists j1 j2, rw_cells rsegs m A [CB n1 j1] /\ rw_cells rsegs m (A + Z.of_nat n1) [CB n2 j2].
Proof.
  intros m A n1 n2 bs H.
  apply (rw_cells_split_CB rsegs m A [] (n1 + n2) bs [] [n1; n2]) in H; [|cbn; lia].
  cbn [mk_CB_cells app] in H.
  apply (rwc_split m A (A + Z.of_nat n1) [CB n1 (firstn n1 bs)] [CB n2 (firstn n2 (skipn n1 bs))]) in H;
    [|cbn [cells_size csize]; lia].
  do 2 eexists. exact H.
Qed.

Lemma cb_parts : forall m A n bs, rw_cells rsegs m A [CB n bs] ->
  bytes_at rsegs m A bs /\ length bs = n /\ wr_at rsegs m A (Z.of_nat n).
Proof.
  intros m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. cbn [cells_bytes cbytes] in Hb.
  rewrite app_nil_r in Hb. split; [exact Hb|]. split; [tauto|]. cbn [cells_size csize] in Hw.
  rewrite Nat.add_0_r in Hw. exact Hw.
Qed.

Definition le4s (vs : list Z) : list byte := concat (map (fun v => le4 (Z_to_bv 64 v)) vs).
Definition le8s (ps : list Z) : list byte := concat (map (fun p => le8 (Z_to_bv 64 p)) ps).

Lemma length_le4s : forall vs, length (le4s vs) = (4 * length vs)%nat.
Proof.
  induction vs as [|v vs IH]; [reflexivity|]. unfold le4s in *. cbn [map concat].
  rewrite length_app, length_le4, IH. cbn [length]. lia.
Qed.

Lemma length_le8s : forall ps, length (le8s ps) = (8 * length ps)%nat.
Proof.
  induction ps as [|p ps IH]; [reflexivity|]. unfold le8s in *. cbn [map concat].
  rewrite length_app, length_le8, IH. cbn [length]. lia.
Qed.

Lemma le4s_app : forall vs v, le4s (vs ++ [v]) = le4s vs ++ le4 (Z_to_bv 64 v).
Proof. intros vs v. unfold le4s. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r. reflexivity. Qed.

Definition wd_ok (m0 : word -> option byte) (lo p : Z) (w : list byte) : Prop :=
  cstr0_at m0 p w /\ (4096 <= p)%Z /\ (Z.of_nat (length w) <= 8192)%Z /\ (p + Z.of_nat (length w) + 1 <= lo)%Z /\
  (0x3441c + 4 <= p \/ p + Z.of_nat (length w) + 1 <= 0x3441c)%Z.

Definition cw_resp (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (ms : machine_state) : Prop :=
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  exists t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 t3 t4 t5 t6,
    ms = MS (mkR (Z_to_bv 64 0x17dd8) (Z_to_bv 64 (bv_unsigned sp + -352)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (-902))
                 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x15f34) fc None m (seg_rom rsegs).

Definition cw_call (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (id : Z) (ids : list Z) (m : word -> option byte) (ms : machine_state) : Prop :=
  bytes_at rsegs m (bv_unsigned sp + -340) (le4s ids) /\
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  exists t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 t3 t4 t5 t6,
    ms = MS (mkR (Z_to_bv 64 0x17dcc) (Z_to_bv 64 (bv_unsigned sp + -352)) gp tp t0 t1 t2 x8 x9
                 (Z_to_bv 64 id) (Z_to_bv 64 (bv_unsigned sp + -340)) (Z_to_bv 64 (Z.of_nat (length ids)))
                 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x16e1c) fc None m (seg_rom rsegs).

Definition cw_lpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (id : Z) (vs : list Z) (ws : list (list byte)) (m0 : word -> option byte) (ms : machine_state) : Prop :=
  exists m, munch [(bv_unsigned sp - 752, bv_unsigned sp); (0x3441c, 0x3441c + 4)]%Z m0 m /\ wmono rsegs m0 m /\
    mem_inv rsegs m /\
    ((Verbs.numbers_m ws = None /\ cw_resp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ms) \/
     (exists ids, Verbs.numbers_m ws = Some ids /\
        cw_call ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc id (vs ++ ids) m ms)).

Ltac fix_ret :=
  lazymatch goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (apply bv_eq; vm_compute; reflexivity)
  end.

Ltac dj := cbn [disjoint_from]; rewrite ?length_app, ?length_le8, ?length_le4, ?length_le4s, ?length_le8s;
  cbn [length]; repeat split; lia.

Ltac cond_by b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b;
      [ cbv iota
      | symmetry; unfold bv_eqb, bv_ltu, bv_leu; fold_lit_ux; rewrite ?unsigned_lit_wrap;
        change 7%Z with (Z.ones 3); rewrite ?Z.land_ones by lia;
        repeat match goal with
               | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y)
               | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y)
               end;
        cbn [negb]; first [reflexivity | exfalso; Z.div_mod_to_equations; lia] ]
  end.

Lemma numbers_cons : forall w ws, Verbs.numbers_m (w :: ws) =
  match Verbs.number_m w, Verbs.numbers_m ws with Some v, Some vs => Some (v :: vs) | _, _ => None end.
Proof. reflexivity. Qed.

Lemma cw_loop : number_contract ->
  forall ws ps vs (r : nat) junk (m m0 : word -> option byte)
    (sp ra gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r s5r s6r s7r s8r s9 s10 s11 t3 t4 t5 t6
     ra0 s00 s01 s02 s03 s04 s05 s06 s07 s08 can : word) (F : bvmap 5 word) (fc : bv 32) (lo id ntok tok q : Z),
  ws <> [] -> length ps = length ws ->
  bytes_at rsegs m0 q (le8s ps) -> (bv_unsigned sp <= q)%Z ->
  q = (tok + 16 + 8 * Z.of_nat (length vs))%Z -> (0 <= tok)%Z -> (tok + 8 * ntok < 2^63)%Z ->
  Forall2 (wd_ok m0 lo) ps ws ->
  ssp_at m0 can -> wr_at rsegs m0 0x3441c 4 -> tp = Z_to_bv 64 0x344c0 ->
  munch [(bv_unsigned sp - 752, bv_unsigned sp); (0x3441c, 0x3441c + 4)]%Z m0 m -> wmono rsegs m0 m ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -352) ->
  (0x54738 <= lo)%Z -> (lo + 752 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2^63)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  bytes_at rsegs m (bv_unsigned sp + -340) (le4s vs) ->
  rw_cells rsegs m (bv_unsigned sp + -340 + 4 * Z.of_nat (length vs)) [CB (4 * r) junk] ->
  (length ws <= r)%nat -> (length vs + r = 64)%nat ->
  bytes_at rsegs m (bv_unsigned sp + -84) (le4 (Z_to_bv 64 id)) -> (-2^31 <= id < 2^31)%Z ->
  rw_cells rsegs m (bv_unsigned sp + -80)
    [C8 s08; C8 s07; C8 s06; C8 s05; C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  ntok = (2 + Z.of_nat (length vs) + Z.of_nat (length ws))%Z -> (ntok <= 64)%Z ->
  s0r = Z_to_bv 64 ntok -> s1r = Z_to_bv 64 tok -> s2r = Z_to_bv 64 (4 * Z.of_nat (length vs)) ->
  s3r = Z_to_bv 64 (bv_unsigned sp + -340) -> s4r = Z_to_bv 64 (2 ^ 64 - 1 - tok) ->
  s5r = Z_to_bv 64 (16 + 8 * Z.of_nat (length vs)) -> s6r = Z_to_bv 64 (65 - Z.of_nat (length vs)) ->
  s7r = Z_to_bv 64 (2 ^ 64 - 1 - (bv_unsigned sp + -340)) -> s8r = Z_to_bv 64 67 ->
  evt rsegs (cw_lpost ra0 sp gp tp s00 s01 s02 s03 s04 s05 s06 s07 s08 s9 s10 s11 F fc id vs ws m0)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -352)) gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7
             s2r s3r s4r s5r s6r s7r s8r s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x17d88) fc None m (seg_rom rsegs)).
Proof.
  intros NUM ws. unfold number_contract in NUM. induction ws as [|w ws IH];
    intros ps vs r junk m m0 sp ra gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r s5r s6r s7r s8r
      s9 s10 s11 t3 t4 t5 t6 ra0 s00 s01 s02 s03 s04 s05 s06 s07 s08 can F fc lo id ntok tok q
      NE LP HT QS QE T0 T63 HW HSSP HE TP MU WM MI ST LO1 LO2 SPH SPA HV HF HR HL HI IDR HS NT N64
      E0 E1 E2 E3 E4 E5 E6 E7 E8; [congruence|].
  destruct ps as [|p ps]; [discriminate|]. cbn [length] in LP. injection LP as LP.
  inversion HW as [|p' w' ps' ws' HW1 HWr]; subst p' w' ps' ws'. clear HW.
  destruct HW1 as (HWc & HW4 & HWl & HWlo & HWe).
  subst s0r s1r s2r s3r s4r s5r s6r s7r s8r tp.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ HT) as BT. rewrite length_le8s in BT. cbn [length] in BT.
  unfold le8s in HT. cbn [map concat] in HT. apply bytes_at_app in HT. destruct HT as [HT0 HTr].
  rewrite length_le8 in HTr. fold (le8s ps) in HTr.
  assert (HT0m : bytes_at rsegs m q (le8 (Z_to_bv 64 p))) by (eapply bytes_at_transport; [exact HT0 | exact MU | dj]).
  pose proof (read_all _ _ _ HT0m) as RDp. rewrite length_le8 in RDp.
  cbn [length] in NT, HR.
  step. cond_by false.
  step. cond_by false.
  step. cond_by false.
  do 4 step.
  assert (UP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -340 + 4 * Z.of_nat (length vs))) =
               (bv_unsigned sp + -340 + 4 * Z.of_nat (length vs))%Z) by (apply unsigned_lit; lia).
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -352)) = (bv_unsigned sp + -352)%Z)
    by (apply unsigned_lit; lia).
  assert (UTP : bv_unsigned (Z_to_bv 64 214208) = 214208%Z) by (apply unsigned_lit; lia).
  destruct r as [|r']; [exfalso; cbn [length] in HR; lia|].
  replace (4 * S r')%nat with (4 + 4 * r')%nat in HF by lia.
  destruct (cb_split _ _ _ _ _ HF) as (j1 & j2 & HO & HF2). clear HF.
  destruct (cb_parts _ _ _ _ HO) as (HOb & HOl & HOw).
  destruct (errno_cell m (wr_at_transport rsegs m0 m _ _ HE WM)) as [ev HEV].
  assert (HWm : cstr0_at m p w).
  { destruct HWc as [Hb Hz]. split; [|exact Hz]. eapply bytes_at_transport; [exact Hb | exact MU | dj]. }
  assert (HSm : ssp_at m can).
  { destruct HSSP as [G1 G2]. unfold ssp_at, SSP_GOT, SSP_GUARD in *.
    split; (eapply bytes_at_transport; [eassumption | exact MU | dj]). }
  eapply evt_cut.
  { eapply NUM with (lo := lo) (can := can) (ev := ev) (wd := w) (ob := j1); rewrite ?UP, ?U1, ?USP, ?UTP.
    all: first [ exact HWm | exact HOb | exact HOl | exact HOw | exact HEV | exact HSm | exact MI | exact ST
               | cbv beta delta [off_lo SSP_GOT SSP_GUARD NUMBER_K]; lia ]. }
  intros ms' PO. unfold number_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
                  & EMS & MUn & WMn & MIn & STn & OUT).
  subst ms'. rewrite U1, USP, UTP in MUn. rewrite USP in STn. rewrite U1 in OUT. unfold NUMBER_K in MUn.
  fix_ret.
  assert (MW : munch [(bv_unsigned sp - 752, bv_unsigned sp); (0x3441c, 0x3441c + 4)]%Z m0 m1).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUn].
    intros x Hx. cbn [outside] in *. repeat split; try exact I; lia. }
  pose proof (wmono_trans rsegs _ _ _ WM WMn) as WM1.
  assert (HV1 : bytes_at rsegs m1 (bv_unsigned sp + -340) (le4s vs))
    by (eapply bytes_at_transport; [exact HV | exact MUn | dj]).
  assert (HF3 : rw_cells rsegs m1 (bv_unsigned sp + -340 + 4 * Z.of_nat (length vs) + Z.of_nat 4) [CB (4 * r') j2])
    by (eapply rw_cells_transport; [exact HF2 | exact MUn | exact WMn | cbn [cells_size csize]; dj]).
  assert (HI1 : bytes_at rsegs m1 (bv_unsigned sp + -84) (le4 (Z_to_bv 64 id)))
    by (eapply bytes_at_transport; [exact HI | exact MUn | dj]).
  assert (HS1 : rw_cells rsegs m1 (bv_unsigned sp + -80)
                  [C8 s08; C8 s07; C8 s06; C8 s05; C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0])
    by (eapply rw_cells_transport; [exact HS | exact MUn | exact WMn | cbn [cells_size csize]; dj]).
  clear HF2 HV HI HS HO HOb HOw HEV MU WM ST HWm HSm.
  destruct (Verbs.number_m w) as [v|] eqn:NW.
  - step. if_false. do 5 step.
    assert (S6 : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (65 - Z.of_nat (length vs))) + -1)) =
                 Z_to_bv 64 (65 - Z.of_nat (length (vs ++ [v])))).
    { rewrite unsigned_lit by lia. change (bv_swrap 32 ?z) with ((z + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31)%Z.
      rewrite Z.mod_small by lia. f_equal. rewrite length_app. cbn [length]. lia. }
    rewrite S6.
    assert (A0E : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 ntok) +
                     bv_unsigned (Z_to_bv 64 (65 - Z.of_nat (length (vs ++ [v])))))) =
                  Z_to_bv 64 (ntok + 64 - Z.of_nat (length vs))).
    { rewrite length_app. cbn [length]. rewrite (unsigned_lit ntok), unsigned_lit by lia.
      change (bv_swrap 32 ?z) with ((z + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31)%Z.
      rewrite Z.mod_small by lia. f_equal. lia. }
    rewrite A0E.
    assert (HV2 : bytes_at rsegs m1 (bv_unsigned sp + -340) (le4s (vs ++ [v]))).
    { rewrite le4s_app. apply bytes_at_app. split; [exact HV1|]. rewrite length_le4s.
      replace (bv_unsigned sp + -340 + Z.of_nat (4 * length vs))%Z
        with (bv_unsigned sp + -340 + 4 * Z.of_nat (length vs))%Z by lia. exact OUT. }
    destruct ws as [|w' ws'].
    + cbn [length] in NT, HR. cond_by false.
      eapply evt_mono; [eapply cw_acc with (id := id) (ntok := ntok) (s0 := s00);
        [exact HI1 | exact IDR | cbn [length] in NT; lia | lia] |].
      intros ms' EM. cbv beta in EM. unfold cw_lpost. exists m1. split; [exact MW|]. split; [exact WM1|].
      split; [exact MIn|]. right. exists [v]. split; [cbn [Verbs.numbers_m]; rewrite NW; reflexivity|].
      unfold cw_call. split; [exact HV2|]. split; [exact HS1|]. subst ms'.
      replace (ntok - 2)%Z with (Z.of_nat (length (vs ++ [v]))) by (rewrite length_app; cbn [length] in *; lia).
      do 21 eexists. reflexivity.
    + cbn [length] in HR, NT.
      cond_by true.
      replace (bv_unsigned sp + -340 + 4 * Z.of_nat (length vs) + Z.of_nat 4)%Z
        with (bv_unsigned sp + -340 + 4 * Z.of_nat (length (vs ++ [v])))%Z in HF3
        by (rewrite length_app; cbn [length]; lia).
      eapply evt_mono.
      { eapply (IH ps (vs ++ [v]) r' j2 m1 m0) with (lo := lo) (id := id) (ntok := ntok) (tok := tok)
          (q := (q + 8)%Z) (can := can).
        all: try first [ discriminate | reflexivity | eassumption ].
        all: first [ (f_equal; rewrite ?length_app; cbn [length] in *; lia)
                   | (rewrite ?length_app; cbn [length] in *; lia) ]. }
      intros ms' PO. unfold cw_lpost in PO |- *. destruct PO as (mm & MUm & WMm & MIm & [[NN RR]|(ids & NS & CC)]).
      * exists mm. split; [exact MUm|]. split; [exact WMm|]. split; [exact MIm|]. left.
        split; [rewrite numbers_cons, NW, NN; reflexivity | exact RR].
      * exists mm. split; [exact MUm|]. split; [exact WMm|]. split; [exact MIm|]. right. exists (v :: ids).
        split; [rewrite numbers_cons, NW, NS; reflexivity|]. rewrite <- app_assoc in CC. exact CC.
  - step. if_true.
    eapply evt_mono; [apply cw_rej |].
    intros ms' EM. cbv beta in EM. unfold cw_lpost. exists m1. split; [exact MW|]. split; [exact WM1|].
    split; [exact MIn|].
    left. split; [rewrite numbers_cons, NW; reflexivity|].
    unfold cw_resp. split; [exact HS1|]. subst ms'. do 23 eexists. reflexivity.
Qed.

Lemma signed_nat : forall z, (0 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite unsigned_lit by lia.
  change (bv_swrap 64 ?x) with ((x + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63)%Z. rewrite Z.mod_small by lia. lia.
Qed.

Lemma number_range : forall w v, Verbs.number_m w = Some v -> (-1000000 <= v <= 1000000)%Z.
Proof.
  intros w v H. unfold Verbs.number_m in H.
  destruct (Verbs.signed_digits (Verbs.dropw Verbs.is_space w)) as [z|]; [|discriminate].
  destruct ((-1000000 <=? z) && (z <=? 1000000))%Z eqn:E; [|discriminate].
  injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1, E2. lia.
Qed.

Lemma cw_not : forall x, (0 <= x < 2 ^ 64)%Z -> Z.lxor x 18446744073709551615 = (2 ^ 64 - 1 - x)%Z.
Proof.
  intros x Hx.
  replace (2 ^ 64 - 1 - x)%Z with (Z.lnot x mod 2 ^ 64)%Z.
  2: { unfold Z.lnot. replace (Z.pred (- x)) with ((2 ^ 64 - 1 - x) + (-1) * 2 ^ 64)%Z by lia.
       rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  change 18446744073709551615%Z with (Z.ones 64).
  apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec.
  destruct (Z.lt_ge_cases n 64) as [L|L].
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia. rewrite Z.ones_spec_low by lia.
    apply xorb_true_r.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite Z.ones_spec_high by lia. rewrite xorb_false_r.
    rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia.
Qed.

Definition cw_out (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (args : list (list byte)) (m0 : word -> option byte) (ms : machine_state) : Prop :=
  exists m, munch [(bv_unsigned sp - 752, bv_unsigned sp); (0x3441c, 0x3441c + 4)]%Z m0 m /\ wmono rsegs m0 m /\
    mem_inv rsegs m /\
    ((Verbs.chain_words_m args = Verbs.reject /\ cw_resp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ms) \/
     (exists id ids, Verbs.chain_words_m args = Verbs.SCall (Verbs.sup_chain id ids) /\
        cw_call ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc id ids m ms)).

Lemma cw_run : number_contract ->
  forall (tks : list (list byte)) (ps : list Z) (m0 : word -> option byte)
    (sp ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 can : word)
    (F : bvmap 5 word) (fc : bv 32) (tok : Z),
  length ps = length tks -> (1 <= length tks <= 64)%nat ->
  bytes_at rsegs m0 tok (le8s ps) -> (bv_unsigned sp <= tok)%Z -> (tok mod 8 = 0)%Z ->
  (tok + 8 * Z.of_nat (length tks) < 2 ^ 63)%Z ->
  Forall2 (wd_ok m0 (bv_unsigned sp - 752)) ps tks ->
  ssp_at m0 can -> wr_at rsegs m0 0x3441c 4 -> tp = Z_to_bv 64 0x344c0 ->
  mem_inv rsegs m0 -> stk rsegs m0 (bv_unsigned sp - 752) (bv_unsigned sp) ->
  (0x54738 + 752 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2^63)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  evt rsegs (cw_out ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (tl tks) m0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 tok) (Z_to_bv 64 (Z.of_nat (length tks))) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x17d0c) fc None m0 (seg_rom rsegs)).
Proof.
  intros NUM tks ps m0 sp ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 can
    F fc tok LP NT HT TS TM T63 HW HSSP HE TP MI ST LO SPH SPA.
  subst tp.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ HT) as BT. rewrite length_le8s in BT.
  pose proof (munch_refl [(bv_unsigned sp - 752, bv_unsigned sp); (0x3441c, 0x3441c + 4)]%Z m0) as MU.
  pose proof (wmono_refl rsegs m0) as WM.
  carve_frame 352%nat ST.
  pose proof (conj HT HE) as KEEP.
  do 11 zstep. rename m1 into m.
  pose proof (rwc_split _ _ (bv_unsigned sp + -80) [_] _ FR) as X.
  specialize (X ltac:(cbn [cells_size csize Nat.add]; lia)). destruct X as [FR1 FRs]. clear FR.
  destruct (cb_split _ _ 12 260 _ FR1) as (j0 & j1 & FR0 & FR2). clear FR1.
  destruct (cb_split _ _ 256 4 _ FR2) as (jids & jid & FRi & FRd). clear FR2.
  do 3 zstep.
  if_cases K; zify_cond K; rewrite ?signed_nat in K by lia.
  - eapply evt_mono; [apply cw_rej |].
    intros ms' EM. cbv beta in EM. exists m. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    left. split.
    + destruct tks as [|w0 [|w1 [|w2 r]]]; cbn [length] in K, NT; try lia; reflexivity.
    + unfold cw_resp. split; [exact FRs|]. subst ms'. do 23 eexists. reflexivity.
  - assert (L3 : (3 <= length tks)%nat) by lia.
    destruct tks as [|w0 [|w1 [|w2 ws]]]; cbn [length] in L3; try lia. clear L3.
    destruct ps as [|p0 [|p1 [|p2 ps]]]; cbn [length] in LP; try discriminate.
    inversion HW as [|p0' w0' ps0' ws0' HW0 HWa]; subst p0' w0' ps0' ws0'. clear HW.
    inversion HWa as [|p1' w1' ps1' ws1' HW1 HWr]; subst p1' w1' ps1' ws1'. clear HWa.
    destruct HW1 as (HWc & HW4 & HWl & HWlo & HWe).
    unfold le8s in HT. cbn [map concat] in HT. apply bytes_at_app in HT. destruct HT as [_ HT].
    rewrite length_le8 in HT. apply bytes_at_app in HT. destruct HT as [HTp1 _].
    destruct KEEP as [HT0 HE0].
    unfold le8s in HT0. cbn [map concat] in HT0. apply bytes_at_app in HT0. destruct HT0 as [_ HT0].
    rewrite length_le8 in HT0. apply bytes_at_app in HT0. destruct HT0 as [_ HTr].
    rewrite length_le8 in HTr. fold (le8s (p2 :: ps)) in HTr.
    replace (tok + Z.of_nat 8 + Z.of_nat 8)%Z with (tok + 16)%Z in HTr by lia.
    pose proof (read_all _ _ _ HTp1) as RD1. rewrite length_le8 in RD1.
    change (tok + Z.of_nat 8)%Z with (tok + 8)%Z in RD1.
    cbn [length] in NT, T63.
    assert (UT : bv_unsigned (Z_to_bv 64 tok) = tok) by (apply unsigned_lit; lia).
    do 3 zstep. cond_by false. do 3 zstep. cond_by false.
    do 3 zstep.
    assert (UP : bv_unsigned (Z_to_bv 64 p1) = p1) by (apply unsigned_lit; lia).
    assert (U1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -84)) = (bv_unsigned sp + -84)%Z) by (apply unsigned_lit; lia).
    assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -352)) = (bv_unsigned sp + -352)%Z)
      by (apply unsigned_lit; lia).
    assert (U3 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -340)) = (bv_unsigned sp + -340)%Z)
      by (apply unsigned_lit; lia).
    assert (UTP : bv_unsigned (Z_to_bv 64 214208) = 214208%Z) by (apply unsigned_lit; lia).
    replace (bv_unsigned sp + -352 + Z.of_nat 12 + Z.of_nat 256)%Z with (bv_unsigned sp + -84)%Z in FRd by lia.
    destruct (cb_parts _ _ _ _ FRd) as (HOb & HOl & HOw).
    destruct (errno_cell m HE) as [ev HEV].
    assert (HWm : cstr0_at m p1 w1).
    { destruct HWc as [Hb Hz]. split; [|exact Hz]. eapply bytes_at_transport; [exact Hb | exact MU | dj]. }
    assert (HSm : ssp_at m can).
    { destruct HSSP as [G1 G2]. unfold ssp_at, SSP_GOT, SSP_GUARD in *.
      split; (eapply bytes_at_transport; [eassumption | exact MU | dj]). }
    eapply evt_cut.
    { eapply NUM with (lo := (bv_unsigned sp - 752)%Z) (can := can) (ev := ev) (wd := w1) (ob := jid);
        rewrite ?UP, ?U1, ?USP, ?UTP.
      all: first [ exact HWm | exact HOb | exact HOl | exact HOw | exact HEV | exact HSm | exact MI | exact ST
                 | cbv beta delta [off_lo SSP_GOT SSP_GUARD NUMBER_K]; lia ]. }
    intros ms' PO. unfold number_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
                    & EMS & MUn & WMn & MIn & STn & OUT).
    subst ms'. rewrite U1, USP, UTP in MUn. rewrite USP in STn. rewrite U1 in OUT. unfold NUMBER_K in MUn.
    fix_ret.
    assert (MW : munch [(bv_unsigned sp - 752, bv_unsigned sp); (0x3441c, 0x3441c + 4)]%Z m0 m1).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUn].
      intros x Hx. cbn [outside] in *. repeat split; try exact I; lia. }
    pose proof (wmono_trans rsegs _ _ _ WM WMn) as WM1.
    assert (HS1 : rw_cells rsegs m1 (bv_unsigned sp + -80)
                    [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact FRs | exact MUn | exact WMn | cbn [cells_size csize]; dj]).
    replace (bv_unsigned sp + -352 + Z.of_nat 12)%Z with (bv_unsigned sp + -340 + 4 * Z.of_nat (length (@nil Z)))%Z
      in FRi by (cbn [length]; lia).
    assert (HF1 : rw_cells rsegs m1 (bv_unsigned sp + -340 + 4 * Z.of_nat (length (@nil Z))) [CB (4 * 64) jids])
      by (eapply rw_cells_transport; [exact FRi | exact MUn | exact WMn | cbn [cells_size csize length]; dj]).
    clear FRs FRi FR0 FRd HOb HOw HEV HWm HSm.
    destruct (Verbs.number_m w1) as [v|] eqn:NW1.
    + step. if_false. do 7 step.
      rewrite UT, U3, !cw_not by lia.
      pose proof (number_range _ _ NW1) as VR.
      eapply evt_mono.
      { eapply (cw_loop NUM (w2 :: ws) (p2 :: ps) [] 64 jids m1 m0) with (lo := (bv_unsigned sp - 752)%Z) (id := v)
          (ntok := Z.of_nat (length (w0 :: w1 :: w2 :: ws))) (tok := tok) (q := (tok + 16)%Z) (can := can).
        all: try first [ discriminate | reflexivity | eassumption ].
        all: first [ exact HTr | exact HE0 | (f_equal; cbn [length] in *; lia) | (cbn [length] in *; lia)
                   | (split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn in Hi; lia) ]. }
      intros ms' PO. unfold cw_lpost in PO. destruct PO as (mm & MUm & WMm & MIm & [[NN RR]|(ids & NS & CC)]).
      * exists mm. split; [exact MUm|]. split; [exact WMm|]. split; [exact MIm|]. left.
        split; [cbn [tl Verbs.chain_words_m]; rewrite NW1, NN; reflexivity | exact RR].
      * exists mm. split; [exact MUm|]. split; [exact WMm|]. split; [exact MIm|]. right. exists v, ids.
        split; [cbn [tl Verbs.chain_words_m]; rewrite NW1, NS; reflexivity | exact CC].
    + step. if_true.
      eapply evt_mono; [apply cw_rej |].
      intros ms' EM. cbv beta in EM. exists m1. split; [exact MW|]. split; [exact WM1|]. split; [exact MIn|].
      left. split; [cbn [tl Verbs.chain_words_m]; rewrite NW1; reflexivity|].
      unfold cw_resp. split; [exact HS1|]. subst ms'. do 23 eexists. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB
  RecSeq RecTail RecAnsB VerbsB chain_words_c sup_chain_c sup_resp_c xmalloc_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require rec_shape_of_c snprintf_c.
Local Open Scope Z_scope.

Lemma cw_forall2 : forall {X Y : Type} (P : X -> Y -> Prop) xs ys, length xs = length ys ->
  (forall i x y, nth_error xs i = Some x -> nth_error ys i = Some y -> P x y) -> Forall2 P xs ys.
Proof.
  intros X Y P xs. induction xs as [|x xs IH]; intros [|y ys] L H; cbn [length] in L; try discriminate; constructor.
  - exact (H 0%nat x y eq_refl eq_refl).
  - apply IH; [lia|]. intros i x' y' E1 E2. exact (H (S i) x' y' E1 E2).
Qed.

Lemma cw_len_tl : forall {X : Type} (l : list X), length (tl l) = (length l - 1)%nat.
Proof. intros X [|x l]; cbn [tl length]; lia. Qed.

Lemma cw_numbers : forall ws ids, Verbs.numbers_m ws = Some ids ->
  length ids = length ws /\ Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids.
Proof.
  induction ws as [|w ws IH]; intros ids H.
  - cbn in H. injection H as <-. split; [reflexivity | constructor].
  - rewrite numbers_cons in H. destruct (Verbs.number_m w) as [v|] eqn:E; [|discriminate].
    destruct (Verbs.numbers_m ws) as [vs|] eqn:E2; [|discriminate]. injection H as <-.
    destruct (IH vs eq_refl) as [L F]. split; [cbn [length]; rewrite L; reflexivity|].
    constructor; [|exact F]. pose proof (number_range _ _ E). lia.
Qed.

Lemma cw_scall : forall args id ids, Verbs.chain_words_m args = Verbs.SCall (Verbs.sup_chain id ids) ->
  -2 ^ 31 <= id < 2 ^ 31 /\ S (length ids) = length args /\ (1 <= length ids)%nat /\
  Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids.
Proof.
  intros args id ids H. destruct args as [|a [|r rest]]; cbn [Verbs.chain_words_m] in H;
    try (unfold Verbs.reject in H; discriminate).
  destruct (Verbs.number_m a) as [v|] eqn:E1; [|unfold Verbs.reject in H; discriminate].
  destruct (Verbs.numbers_m (r :: rest)) as [vs|] eqn:E2; [|unfold Verbs.reject in H; discriminate].
  injection H as <- <-. destruct (cw_numbers _ _ E2) as [L F].
  pose proof (number_range _ _ E1). rewrite L. cbn [length] in *.
  split; [lia|]. split; [reflexivity|]. split; [lia | exact F].
Qed.

Lemma cw_le_bytes : forall (B : malloc_syms) m a bs, le_at B m a bs -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at (ms_segs B) m a bs.
Proof.
  unfold le_at, blk_data. intros B m a bs H Ha Hb. split; [exact Ha|]. split; [exact Hb|]. intros i Hi.
  pose proof (H (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. exact E.
Qed.

Lemma cw_bytes_le : forall (B : malloc_syms) m a bs, bytes_at (ms_segs B) m a bs -> le_at B m a bs.
Proof.
  unfold le_at, blk_data. intros B m a bs H i Hi. replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia.
  apply (mbyte_of_bytes_at _ _ _ _ _ H). lia.
Qed.

Lemma cw_dec_tail : forall r, Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) r ->
  (length (concat (map (fun j => SPACE :: dec j) r)) <= 12 * length r)%nat.
Proof.
  induction r as [|j r IH]; intros F; [cbn; lia|]. inversion F as [|x l Hj Fr]; subst.
  cbn [map concat]. rewrite length_app. cbn [length]. pose proof (dec_length j Hj). specialize (IH Fr). lia.
Qed.

Lemma cw_dec_list : forall ids, Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids ->
  (length (dec_list ids) <= 12 * length ids)%nat.
Proof.
  intros [|i r] F; [cbn; lia|]. inversion F as [|x l Hi Fr]; subst.
  unfold dec_list. rewrite length_app. pose proof (dec_length i Hi). pose proof (cw_dec_tail r Fr). cbn [length]. lia.
Qed.

Lemma cw_t_len : forall R id ids, (r_refuse R <> 0 -> declared (r_code R) = true) ->
  (length (snd (sup_chain_m R id ids)) <= 16)%nat.
Proof.
  intros R id ids HD. unfold sup_chain_m, rec_stub, rec_answer.
  assert (E1 : forall fn A, r_refuse (rec_record R fn A) = r_refuse R)
    by (intros fn A; unfold rec_record; destruct (Nat.ltb _ _); reflexivity).
  assert (E2 : forall fn A, r_code (rec_record R fn A) = r_code R)
    by (intros fn A; unfold rec_record; destruct (Nat.ltb _ _); reflexivity).
  rewrite E1, E2. destruct (r_refuse R =? 0) eqn:E; cbn [hand_back snd].
  - apply Nat.leb_le. vm_compute. reflexivity.
  - apply Z.eqb_neq in E. pose proof (declared_range _ (HD E)). pose proof (resp_length (r_code R) ltac:(lia)). lia.
Qed.

Lemma cw_f18 : forall m can, ssp_at m can -> f18_words rsegs m.
Proof.
  intros m can [H1 H2]. unfold f18_words. split.
  - split; [split; [cbn; split; exact I|]|].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H1.
    + split; [unfold snprintf_c.GOT_GUARD; lia|]. split; [cbn; unfold snprintf_c.GOT_GUARD; lia|].
      intros i Hi. cbn in Hi. exact (proj1 (guard_wview m i Hi)).
  - exists can. split; [split; [cbn; split; exact I|]|].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H2.
    + split; [unfold snprintf_c.GUARD; lia|]. split; [cbn; unfold snprintf_c.GUARD; lia|].
      intros i Hi. cbn in Hi. exact (proj2 (guard_wview m i Hi)).
Qed.

Lemma cw_ssp_of_f18 : forall (B : malloc_syms) m, ms_segs B = rsegs -> f18_words rsegs m -> exists can, ssp_b B m can.
Proof.
  intros B m SG [[[_ H1] _] (can & [[_ H2] _])]. exists can.
  cbn [cells_bytes cbytes] in H1, H2. rewrite app_nil_r in H1, H2. rewrite <- SG in H1, H2.
  split; [exact (cw_bytes_le B m _ _ H1) | exact (cw_bytes_le B m _ _ H2)].
Qed.

Section CW.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis TP : ms_tp B = 0x344c0.
Hypothesis EOFF : ms_errno_off B = -164.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis ERRNO_NO : errno_unowned B API.
Hypothesis RELRO_IMG : forall a, in_globals frame_RELRO a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RELRO_NO : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.
Hypothesis NUM : number_contract.
Hypothesis SCH : sup_chain_contract B API.
Hypothesis SRESP : sup_resp_contract B API.

Lemma cw_rjr_blk : forall K S E O L A mem md L' A' mem' md' a k i,
  rjr B (aa_MR API) K S E (fun pn => In pn O) L A mem md L' A' mem' md' ->
  In (a, k) (blocks L A) -> ~ In (a, k) O -> 0 <= i < k ->
  mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i).
Proof.
  intros K S E O L A mem md L' A' mem' md' a k i RJ Hin Hn Hi.
  unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & Ep & Hp). cbn in Ep. injection Ep as <- <-.
  destruct RJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HKP & _). exact (HKP p k' i Hp Hn Hi).
Qed.

Lemma cw_rjr_free : forall K S E gone L A mem md L' A' mem' md' a,
  rjr B (aa_MR API) K S E gone L A mem md L' A' mem' md' ->
  alloc_ceiling <= a < 2 ^ 64 -> ~ (S - K <= a < S) -> ~ (errno_addr B <= a < errno_addr B + 4) -> ~ E a ->
  mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a.
Proof.
  intros K S E gone L A mem md L' A' mem' md' a RJ Ha H1 H2 H3.
  destruct RJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
  exact (proj1 (HF a (or_introl Ha) H1 H2 H3)).
Qed.

Lemma cw_toks : forall K S E O L A mem md L' A' mem' md' tok ptrs tks cb ncb,
  rjr B (aa_MR API) K S E (fun pn => In pn O) L A mem md L' A' mem' md' ->
  toks_at B mem tok ptrs tks cb ncb -> In (cb, ncb) (blocks L A) -> ~ In (cb, ncb) O ->
  S <= tok -> tok + 8 * Z.of_nat (length tks) < 2 ^ 63 -> alloc_ceiling <= S - K ->
  errno_addr B + 4 <= S - K -> (forall a, E a -> a < S - K) ->
  toks_at B mem' tok ptrs tks cb ncb.
Proof.
  intros K S E O L A mem md L' A' mem' md' tok ptrs tks cb ncb RJ (TM & TL & TA & TW) INB NOB ST T63 AS ES EW.
  pose proof (rjr_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ RJ) as RB.
  split; [exact TM|]. split; [exact TL|]. split.
  - intros i Hi. rewrite <- (TA i Hi).
    assert (Hi' : 0 <= i < 8 * Z.of_nat (length tks)).
    { change (concat (map (fun p => Mem.le8 (Z_to_bv 64 p)) ptrs)) with (le8s ptrs) in Hi.
      rewrite length_le8s, TL in Hi. lia. }
    apply (cw_rjr_free K S E _ L A mem md L' A' mem' md' (tok + i) RJ); [lia | lia | lia |].
    intros H. specialize (EW _ H). lia.
  - intros j p w Hp Hw. destruct (TW j p w Hp Hw) as (W1 & W2 & W3 & W4 & W5 & W6).
    split; [|split; [exact W2 | split; [exact W3 | split; [exact W4 | split; [exact W5 | exact W6]]]]].
    unfold le_at, blk_data in W1 |- *. intros i Hi. rewrite <- (W1 i Hi).
    rewrite length_app in Hi. cbn [length] in Hi.
    replace (p + i) with (cb + (p + i - cb)) by lia.
    apply (cw_rjr_blk K S E O L A mem md L' A' mem' md' cb ncb (p + i - cb) RJ INB NOB). lia.
Qed.

Lemma cw_mid : forall L A regs mem md R O m1 can,
  call_pre_k B (aa_MR API) CW_K L A regs mem md ->
  munch [(spZ regs - 752, spZ regs); (0x3441c, 0x3441c + 4)] mem m1 -> wmono rsegs mem m1 ->
  g_rec_rep (ms_segs B) L A mem R O -> ssp_b B mem can ->
  Mem.bytes_at (ms_segs B) mem rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes ->
  aa_MR API L A m1 md /\
  rjr B (aa_MR API) CW_K (spZ regs) cw_writes (fun pn => In pn O) L A mem md L A m1 md /\
  g_rec_rep (ms_segs B) L A m1 R O /\ ssp_at m1 can /\
  Mem.bytes_at (ms_segs B) m1 rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes.
Proof using SEGS TP EOFF AX ERRNO_NO.
  intros L A regs mem md R O m1 can PRE MU WM REP SSP GSH.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  assert (EA : errno_addr B = 0x3441c) by (unfold errno_addr; rewrite TP, EOFF; reflexivity).
  assert (ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling) by lia.
  assert (KV : CW_K = 12864) by reflexivity.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  rewrite SEGS in HWS, HERR.
  set (W := [(spZ regs - 752, spZ regs); (0x3441c, 0x3441c + 4)]) in MU.
  assert (OUTW : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 752 <= a < spZ regs) -> ~ (0x3441c <= a < 0x3441c + 4) ->
                 Frame.outside W a)
    by (intros a _ H1 H2; unfold W; cbn [Frame.outside]; repeat split; try exact I; lia).
  assert (EIMG : forall a, 0x3441c <= a < 0x3441c + 4 -> in_img B a).
  { intros a Ha. apply (in_img_found B SEGS); [lia|].
    assert (C : a = 0x3441c \/ a = 0x3441c + 1 \/ a = 0x3441c + 2 \/ a = 0x3441c + 3) by lia.
    repeat (destruct C as [C|C]; [subst a; intro F; vm_compute in F; discriminate F|]).
    subst a. intro F. vm_compute in F. discriminate F. }
  assert (OWN : forall a, owned B L A a -> Frame.outside W a).
  { intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
    apply OUTW; [lia | lia |]. intros He. apply (ERRNO_NO L A mem md a HMR); [rewrite EA; exact He | exact Ho]. }
  assert (BLK : forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> Frame.outside W (ptr_addr L p + i)).
  { intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (_ & H4 & Hc & _).
    apply OUTW; [lia | lia |]. intros He. exact (ax_blocks_img AX L A mem md p n i HMR Hin Hi (EIMG _ He)). }
  assert (MR1 : aa_MR API L A m1 md).
  { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho). eapply munch_mbyte; [exact MU | lia | exact (OWN a Ho)].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho).
      eapply munch_present; [exact MU | lia | exact (OWN a Ho) | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (Hp & H4 & Hc & _).
      eapply munch_present; [exact MU | lia | exact (BLK p n i Hin Hi) | exact Hp].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  assert (P0 : call_post_rec B (aa_MR API) 752 L A regs mem md (fun _ => False) (fun _ => False) L A regs m1 md).
  { split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|]. split; [apply layout_le_refl|].
    split; [intros; reflexivity|]. split; [intros r _; reflexivity|].
    split; [exists (m_vmmaps md); apply with_vmmaps_self'|].
    split.
    { intros a Ha _ _ NS _.
      assert (Ra : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | pose proof (in_img_low B SEGS a Ha); lia]).
      assert (OW : Frame.outside W a).
      { apply OUTW; [exact Ra | intros H; apply NS; left; exact H | intros H; apply NS; right; rewrite EA; exact H]. }
      split; [exact (munch_mbyte _ _ _ _ _ MU Ra OW) | exact (munch_writable _ _ _ _ _ MU Ra OW)]. }
    split.
    { intros p n i Hin _ _ Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (_ & H4 & Hc & _).
      exact (munch_mbyte _ _ _ _ (ptr_addr L p + i) MU ltac:(lia) (BLK p n i Hin Hi)). }
    intros a [Ha|Ha]; rewrite SEGS; apply WM; [apply HWS; lia | apply HERR; exact Ha]. }
  assert (RJ0 : rjr B (aa_MR API) CW_K (spZ regs) cw_writes (fun pn => In pn O) L A mem md L A mem md)
    by (apply rjr_init; [exact PRE | lia]).
  assert (RJ1 : rjr B (aa_MR API) CW_K (spZ regs) cw_writes (fun pn => In pn O) L A mem md L A m1 md).
  { eapply (rjr_post B (aa_MR API) SEGS LAWS AX ERRNO_LOW); [exact RJ0 | exact P0 | lia | lia | | | | lia |].
    - intros a [].
    - intros p n _ _ _ F. exact F.
    - intros p n _ H1 H2. contradiction.
    - intros HI. specialize (HAUX HI). destruct HAUX as (av & ar & W1 & W2 & W3 & W4 & B1 & B2 & B3 & B4 & L1 & L2).
      exists av, ar.
      assert (LIB : forall k, (k < 8)%nat ->
                0 <= ms_libc B + 8 + Z.of_nat k < 2 ^ 64 /\ Frame.outside W (ms_libc B + 8 + Z.of_nat k)).
      { intros k Hk. assert (SO : owned B L A (ms_libc B + 8 + Z.of_nat k)) by (right; unfold static_owned; lia).
        destruct (owned_low B _ LAWS _ _ _ _ _ HMR SO). split; [lia | exact (OWN _ SO)]. }
      split; [exact (word_mem_munch _ _ _ _ _ _ MU LIB W1)|].
      split; [intros k Hk; apply (word_mem_munch _ _ _ _ _ _ MU); [|exact (W2 k Hk)];
              intros k' Hk'; split; [lia | apply OUTW; lia]|].
      split; [apply (word_mem_munch _ _ _ _ _ _ MU); [|exact W3]; intros k' Hk'; split; [lia | apply OUTW; lia]|].
      split; [apply (word_mem_munch _ _ _ _ _ _ MU); [|exact W4]; intros k' Hk'; split; [lia | apply OUTW; lia]|].
      lia. }
  assert (REP1 : g_rec_rep (ms_segs B) L A m1 R O).
  { unfold g_rec_rep in REP |- *. eapply (rec_rep_frame _ _ _ L A mem R O L A m1 REP).
    - intros a Ha. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha.
      assert (OW : Frame.outside W a) by (apply OUTW; lia).
      split; [exact (munch_mbyte _ _ _ _ a MU ltac:(lia) OW) | exact (proj1 (munch_writable _ _ _ _ a MU ltac:(lia) OW))].
    - intros p n i Hin Hi. pose proof (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hin) as Hb.
      unfold blocks in Hb. apply in_map_iff in Hb as ([p' n'] & Ep & Hp). cbn in Ep. injection Ep as <- <-.
      destruct (mr_blocks B _ LAWS L A mem md p' n' i HMR Hp Hi) as (_ & H4 & Hc & _).
      exact (munch_mbyte _ _ _ _ (ptr_addr L p' + i) MU ltac:(lia) (BLK p' n' i Hp Hi)).
    - intros pn Hin. exact (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hin). }
  assert (SS1 : ssp_at m1 can).
  { destruct SSP as [G1 G2]. unfold SSP_GOT_B, SSP_GUARD_B in G1, G2.
    pose proof (cw_le_bytes B mem _ _ G1 ltac:(lia) ltac:(rewrite Mem.length_le8; lia)) as G1'.
    pose proof (cw_le_bytes B mem _ _ G2 ltac:(lia) ltac:(rewrite Mem.length_le8; lia)) as G2'.
    unfold ssp_at, SSP_GOT, SSP_GUARD. rewrite SEGS in G1', G2'.
    split; [apply (bytes_at_transfer rsegs mem); [exact G1'|] | apply (bytes_at_transfer rsegs mem); [exact G2'|]];
      intros i Hi; rewrite Mem.length_le8 in Hi; (apply (munch_mbyte _ _ _ _ _ MU); [lia | apply OUTW; lia]). }
  assert (GL : length rec_shape_of_c.g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  assert (GSH1 : Mem.bytes_at (ms_segs B) m1 rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes).
  { apply (bytes_at_transfer (ms_segs B) mem); [exact GSH|]. intros i Hi. rewrite GL in Hi.
    apply (munch_mbyte _ _ _ _ _ MU); [unfold rec_shape_of_c.G_SHAPES; lia | apply OUTW; unfold rec_shape_of_c.G_SHAPES; lia]. }
  split; [exact MR1|]. split; [exact RJ1|]. split; [exact REP1|]. split; [exact SS1 | exact GSH1].
Qed.

Theorem chain_words_holds : chain_words_contract B API.
Proof using SEGS TP EOFF AX CTX ERRNO_NO RELRO_IMG RELRO_NO NUM SCH SRESP.
  unfold chain_words_contract, CHAIN_WORDS, CW_MALLOCS, CW_REQ.
  intros L A regs mem md b R O tok cb ncb ntok ptrs tks can PRE RA FZ A0 A1 INB NOB TKS NTK NR V0 SPT TOKB OUTS
    ECB EGD REP RDECL SSP GSH RES ROOM.
  subst ntok.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof wx_apart_rsegs as WX.
  assert (EA : errno_addr B = 0x3441c) by (unfold errno_addr; rewrite TP, EOFF; reflexivity).
  assert (ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling) by lia.
  assert (KV : CW_K = 12864) by reflexivity.
  assert (RK : 0 <= SUP_RESP_K <= 12512) by (split; apply Z.leb_le; vm_compute; reflexivity).
  destruct PRE as [PREK HTS].
  pose proof PREK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  pose proof TKS as (TM & TLEN & TA & TW).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  change (bv_unsigned (getr regs 2)) with (bv_unsigned sp) in SPT.
  assert (RSP : 0 <= bv_unsigned sp < 2 ^ 64)
    by (pose proof (bv_unsigned_in_range 64 sp) as H; unfold bv_modulus in H; exact H).
  rewrite SEGS in RA, HWS, HERR.
  assert (ROOML : sb_live b + 7 <= sb_cap b).
  { unfold room_slots, sb_n in ROOM. cbn [sb_live sb_bytes sb_cap] in ROOM. lia. }
  assert (TB0 : bytes_at rsegs (normalize rsegs mem) tok (le8s ptrs)).
  { apply (bytes_at_normalize rsegs mem tok _ RA). rewrite <- SEGS.
    apply cw_le_bytes; [exact TA | lia | rewrite length_le8s, TLEN; lia]. }
  assert (WD0 : Forall2 (wd_ok (normalize rsegs mem) (bv_unsigned sp - 752)) ptrs tks).
  { apply cw_forall2; [exact TLEN|]. intros i p w Hp Hw.
    destruct (TW i p w Hp Hw) as (W1 & W2 & W3 & W4 & W5 & W6).
    destruct (block_facts B _ LAWS L A mem md cb ncb 0 HMR INB ltac:(lia)) as (_ & C1 & C2 & _).
    assert (LW : Z.of_nat (length (w ++ [Z_to_bv 8 0])) = Z.of_nat (length w) + 1)
      by (rewrite length_app; cbn [length]; lia).
    split; [split|].
    - apply (bytes_at_normalize rsegs mem p _ RA). rewrite <- SEGS. apply cw_le_bytes; [exact W1 | lia | rewrite LW; lia].
    - exact W2.
    - split; [lia|]. split; [exact W3|]. split; [lia|]. lia. }
  assert (SS0 : ssp_at (normalize rsegs mem) can).
  { destruct SSP as [G1 G2]. unfold SSP_GOT_B, SSP_GUARD_B in G1, G2. unfold ssp_at, SSP_GOT, SSP_GUARD.
    pose proof (cw_le_bytes B mem _ _ G1 ltac:(lia) ltac:(rewrite Mem.length_le8; lia)) as G1'.
    pose proof (cw_le_bytes B mem _ _ G2 ltac:(lia) ltac:(rewrite Mem.length_le8; lia)) as G2'.
    rewrite SEGS in G1', G2'.
    split; [exact (bytes_at_normalize rsegs mem _ _ RA G1') | exact (bytes_at_normalize rsegs mem _ _ RA G2')]. }
  assert (EW0 : wr_at rsegs (normalize rsegs mem) 0x3441c 4).
  { split; [lia|]. split; [lia|]. intros i Hi.
    assert (W : writable_at rsegs mem (0x3441c + i)) by (apply HERR; rewrite EA; lia).
    unfold writable_at in W. unfold wview, mrd in W |- *. rewrite normalize_rw; [exact W|].
    assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct C as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity. }
  assert (ST0 : stk rsegs (normalize rsegs mem) (bv_unsigned sp - 752) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E].
    assert (NE : normalize rsegs mem (wa a) = mem (wa a)) by (apply normalize_rw; unfold wa; apply ro_addr_hi; lia).
    unfold wview, mrd. rewrite NE. unfold wa. rewrite E. split; [discriminate | exists bb; reflexivity]. }
  assert (R10 : reg_get regs 10 = Z_to_bv 64 tok) by exact A0.
  assert (R11 : reg_get regs 11 = Z_to_bv 64 (Z.of_nat (length tks))) by exact A1.
  assert (R4 : reg_get regs 4 = Z_to_bv 64 0x344c0) by (rewrite <- TP; exact HTP).
  change (getr regs 1) with (reg_get regs 1) in HRA.
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. rewrite R10, R11.
    eapply (evt_normalize rsegs); [exact WX | exact RA |].
    eapply (cw_run NUM) with (ps := ptrs) (can := can);
      [exact TLEN | lia | exact TB0 | exact SPT | exact TM | lia | exact WD0 | exact SS0 | exact EW0 | exact R4
      | apply mem_inv_normalize | exact ST0 | lia | exact H63 | exact HAL]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (m1n & MU1n & WM1n & MI1n & [[CWR RESP1] | (id & ids & CWC & CALL1)]).
  - destruct RESP1 as (FRn & t0' & t1' & t2' & x8 & x9 & a1' & a2' & a3' & a4' & a5' & a6' & a7'
      & x18 & x19 & x20 & x21 & x22 & x23 & x24 & t3' & t4' & t5' & t6' & ->).
    destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
    revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
    pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mem RA) MR1r RO1 MU1n) as MU1.
    pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mem RA) MR1r RO1 WM1n) as WM1.
    pose proof (ro_agree_same rsegs _ _ RA RO1) as RA1.
    pose proof (rw_cells_rel rsegs _ _ _ _ MR1r FRn) as FR1.
    destruct (cw_mid L A regs mem md R O m1 can PREK MU1 WM1 REP SSP GSH) as (MR1 & RJ1 & REP1 & SS1 & GSH1).
    change (spZ regs) with (bv_unsigned sp) in RJ1.
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x17dd8) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp + -352))
      by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_10 : getr R1 10 = Z_to_bv 64 (-902))
      by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
    assert (SP1 : spZ R1 = bv_unsigned sp + -352) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
    pose proof (resp_length (-902) ltac:(lia)) as RL.
    rewrite <- SEGS.
    eapply SR_bind.
    { eapply (SRESP L A R1 m1 md (-902) b).
      - split; [|rewrite SP1; lia].
        eapply (call_pre_k_of_rjr B (aa_MR API)); [exact RJ1 | rewrite E1_1; apply bv_eq; vm_compute; reflexivity
          | | lia | rewrite SP1; lia | rewrite SP1; lia | rewrite E1_4; exact HTP].
        rewrite SP1. replace (bv_unsigned sp + -352) with (bv_unsigned sp + (-22) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      - exact E1_10.
      - lia.
      - rewrite SEGS. exact RA1.
      - exact FZ.
      - rewrite SEGS. exact (cw_f18 m1 can SS1).
      - exact RES.
      - apply (room_slots_mono _ (sb_n b 6) _ 8194); [|lia | exact ROOM].
        unfold sb_le, sb_malloc, sb_n, SB_REQ. cbn [sb_live sb_bytes sb_cap]. lia. }
    intros c2 RET.
    destruct RET as (fx2 & L2 & A2 & R2 & m2 & md2 & q & -> & FK & POST & A0' & QNZ & QAL & FRESH
      & (b1 & b2 & BL2 & BL1) & BK & UB & BQ & RT & RA2 & F182 & INIT2 & LEN2 & RES2).
    pose proof POST as (HMR2 & HWF2 & HBD2 & HLE2 & HST2 & HP2 & HVM2 & HFR2 & HBK2 & HSC2).
    assert (RJ2 : rjr B (aa_MR API) CW_K (bv_unsigned sp) cw_writes (fun pn => In pn O) L A mem md L2 A2 m2 md2).
    { eapply (rjr_post B (aa_MR API) SEGS LAWS AX ERRNO_LOW);
        [exact RJ1 | exact (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST) | | | | | | exact LEN2 |].
      - rewrite SP1. lia.
      - rewrite SP1. lia.
      - intros a [].
      - intros p n _ _ _ F. exact F.
      - intros p n Hp _ Hn. exfalso. exact (Hn (UB p n Hp)).
      - intros H. rewrite INIT2 in H. discriminate. }
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -80)
                    [C8 (reg_get regs 24); C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21);
                     C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                     C8 (reg_get regs 8); C8 (reg_get regs 1)]).
    { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
      assert (Ha : alloc_ceiling <= bv_unsigned sp + -80 + i < 2 ^ 64) by lia.
      assert (N1 : ~ owned B L A (bv_unsigned sp + -80 + i))
        by (intros Ho; destruct (owned_low B _ LAWS _ _ _ _ _ MR1 Ho); lia).
      assert (N2 : ~ owned B L2 A2 (bv_unsigned sp + -80 + i))
        by (intros Ho; destruct (owned_low B _ LAWS _ _ _ _ _ HMR2 Ho); lia).
      assert (NS : ~ scratch_k B SUP_RESP_K R1 (bv_unsigned sp + -80 + i))
        by (unfold scratch_k; rewrite SP1; intros [H|H]; lia).
      destruct (HFR2 _ (or_introl Ha) N1 N2 NS (fun F => F)) as [E W]. split; [exact E | apply W]. }
    destruct (mr_model _ _ LAWS _ _ _ _ HMR2) as (Hh2 & Hl2 & _).
    assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp + -352))
      by exact (eq_trans (HP2 2 ltac:(unfold callee_saved; lia)) E1_2).
    rewrite E1_1, SEGS.
    eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E2_2. eapply cw_ret; [exact FR2 | lia]. }
    intros ms3 (can3 & Q3 & EQ3). subst can3.
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    assert (E3_10 : getr R3 10 = Z_to_bv 64 q) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; exact A0').
    assert (PR3 : regs_preserved regs R3).
    { eapply (preserved_chain (fun r => (r =? 2) || (r =? 8) || (r =? 9) || ((18 <=? r) && (r <=? 24)))
                regs R1 R2 R3 _ _ X1 HP2 X3).
      - intros r Hr O0. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O0 | split; reflexivity]|]).
        subst r. split; reflexivity.
      - intros r Hr O0. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O0 | reflexivity]|]).
        subst r. discriminate O0. }
    assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
    rewrite RP. rewrite <- SEGS.
    set (n := Z.of_nat (length (resp (-902))) + 1) in *.
    apply SR_ret.
    exists fx2, L2, A2, R3, m2, md2, O, 1%nat, q, n.
    split; [reflexivity|].
    split; [exact FK|].
    split.
    { apply (rjr_final B (aa_MR API) CTX CW_K cw_writes (fun pn => In pn O)); [exact PREK | exact RJ2 | exact PR3 |].
      intros a k G. exact (in_map fst O (a, k) G). }
    split; [exact RA2|].
    split.
    { unfold VerbsRun.chain_run. rewrite CWR. cbn [Verbs.reject sup_resp_m].
      change Verbs.err_invalid_operation with (-902).
      split; [exact (RT R O REP1)|]. split; [apply cw_bytes_le; exact BQ | unfold n; lia]. }
    split; [exact E3_10|].
    split; [rewrite BL2; apply in_or_app; right; left; reflexivity|].
    split.
    { intros HO. pose proof (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP1 HO) as Hb. rewrite BL1 in Hb.
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR2 BL2 Hb) as Dj. unfold n in Dj. lia. }
    split.
    { intros [a k] Hin _. rewrite BL1 in Hin.
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR2 BL2 Hin) as Dj. cbn [fst snd]. lia. }
    split.
    { apply (cw_toks CW_K (bv_unsigned sp) cw_writes O L A mem md L2 A2 m2 md2 tok ptrs tks cb ncb RJ2 TKS INB NOB);
        [lia | lia | lia | lia |]. intros a Ha. unfold cw_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha. lia. }
    split; [intros pn Hin _; rewrite BL2; rewrite BL1 in Hin; apply in_mid_inv; exact Hin|].
    split.
    { intros pn Hin. rewrite BL2 in Hin. destruct (pair_dec pn (q, n)) as [E|NE]; [right; right; exact E|].
      pose proof (in_mid_other b1 b2 _ pn Hin NE) as H'. rewrite <- BL1 in H'.
      destruct (In_dec pair_dec pn O) as [HO|HO]; [right; left; exact HO | left; split; assumption]. }
    split; [intros pn _ HO; exact HO|].
    split; [exact LEN2|].
    split.
    { intros a k i Hin Hn Hi. apply (cw_rjr_blk _ _ _ O L A mem md L2 A2 m2 md2 a k i RJ2 Hin); [|exact Hi].
      intros G. apply Hn. exists k. exact G. }
    split; [rewrite SEGS in F182; exact (cw_ssp_of_f18 B m2 SEGS F182)|].
    split.
    { assert (GL : length rec_shape_of_c.g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
      apply (bytes_at_transfer (ms_segs B) m1); [exact GSH1|]. intros i Hi. rewrite GL in Hi.
      assert (RL0 : in_globals frame_RELRO (rec_shape_of_c.G_SHAPES + i))
        by (exists 0x226b0, 1680; split; [left; reflexivity | unfold rec_shape_of_c.G_SHAPES; lia]).
      destruct (RELRO_IMG _ RL0) as (Hi1 & _ & _ & Hi4).
      assert (NS : ~ scratch_k B SUP_RESP_K R1 (rec_shape_of_c.G_SHAPES + i)).
      { unfold scratch_k. rewrite SP1. intros [H|H]; [unfold rec_shape_of_c.G_SHAPES in H; lia | exact (Hi4 H)]. }
      exact (proj1 (HFR2 _ (or_intror Hi1) (RELRO_NO _ _ _ _ _ MR1 RL0) (RELRO_NO _ _ _ _ _ HMR2 RL0) NS (fun F => F))). }
    split; [lia|].
    apply (res_ok_slots_le A2 (sb_malloc b n)); [| | exact RES2].
    + unfold sb_le, sb_malloc, sb_n, SB_REQ. cbn [sb_live sb_bytes sb_cap]. unfold n. lia.
    + unfold sb_n. cbn [sb_live sb_bytes sb_cap]. lia.
  - destruct CALL1 as (IDSn & FRn & t0' & t1' & t2' & x8 & x9 & a3' & a4' & a5' & a6' & a7'
      & x18 & x19 & x20 & x21 & x22 & x23 & x24 & t3' & t4' & t5' & t6' & ->).
    destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
    revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
    pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mem RA) MR1r RO1 MU1n) as MU1.
    pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mem RA) MR1r RO1 WM1n) as WM1.
    pose proof (ro_agree_same rsegs _ _ RA RO1) as RA1.
    pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ MR1r) IDSn) as IDS1.
    pose proof (rw_cells_rel rsegs _ _ _ _ MR1r FRn) as FR1.
    destruct (cw_mid L A regs mem md R O m1 can PREK MU1 WM1 REP SSP GSH) as (MR1 & RJ1 & REP1 & SS1 & GSH1).
    change (spZ regs) with (bv_unsigned sp) in RJ1.
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    destruct (cw_scall _ _ _ CWC) as (IDR & LIDS & L1IDS & FIDS).
    rewrite cw_len_tl in LIDS.
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x17dcc) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp + -352))
      by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_10 : getr R1 10 = Z_to_bv 64 id) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_11 : getr R1 11 = Z_to_bv 64 (bv_unsigned sp + -340))
      by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_12 : getr R1 12 = Z_to_bv 64 (Z.of_nat (length ids)))
      by (rewrite (getr_of_eqv _ _ 12 X1 eq_refl); simp_regs; reflexivity).
    assert (SP1 : spZ R1 = bv_unsigned sp + -352) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
    pose proof (cw_t_len R id ids RDECL) as TL16.
    pose proof (dec_length id IDR) as D1.
    pose proof (dec_length (Z.of_nat (length ids)) ltac:(lia)) as D2.
    pose proof (cw_dec_list ids FIDS) as D3.
    rewrite <- SEGS.
    eapply SR_bind.
    { eapply (SCH L A R1 m1 md id (bv_unsigned sp + -340) ids R O b).
      - split; [|rewrite SP1; lia].
        eapply (call_pre_k_of_rjr B (aa_MR API)); [exact RJ1 | rewrite E1_1; apply bv_eq; vm_compute; reflexivity
          | | unfold SUP_CHAIN_K; lia | rewrite SP1; unfold SUP_CHAIN_K; lia | rewrite SP1; lia | rewrite E1_4; exact HTP].
        rewrite SP1. replace (bv_unsigned sp + -352) with (bv_unsigned sp + (-22) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      - exact E1_10.
      - exact IDR.
      - exact E1_11.
      - exact E1_12.
      - lia.
      - exact FIDS.
      - lia.
      - replace (bv_unsigned sp + -340) with (bv_unsigned sp + (-85) * 4) by ring. rewrite Z.mod_add by lia.
        Z.div_mod_to_equations. lia.
      - rewrite SEGS. unfold le32. exact IDS1.
      - right. rewrite SP1. lia.
      - left. rewrite SP1. split; lia.
      - intros a Ha. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE. lia.
      - exact GSH1.
      - exact REP1.
      - rewrite SEGS. exact RA1.
      - exact FZ.
      - rewrite SEGS. exact (cw_f18 m1 can SS1).
      - exact RES.
      - apply (room_slots_mono _ (sb_n b 6) _ 8194); [|lia | exact ROOM].
        unfold sb_mallocs, sup_chain_sizes. cbn [fold_left]. unfold sb_le, sb_malloc, sb_n, SB_REQ.
        cbn [sb_live sb_bytes sb_cap]. lia. }
    intros c2 RET.
    destruct RET as (fx2 & L2 & A2 & R2 & m2 & md2 & R' & O' & t & q & SCM & -> & FK & POST & A0' & REP2 & OWN2
      & INQ & FRQ & NQO & BQ & OK2 & BIN2 & DIS2 & GSH2 & RA2 & F182 & INIT2 & LEN2 & LE2 & RS2).
    pose proof POST as (HMR2 & HWF2 & HBD2 & HLE2 & HST2 & HP2 & HVM2 & HFR2 & HBK2 & HSC2).
    rewrite SCM in TL16. cbn [snd] in TL16.
    assert (RES2 : res_ok_slots A2 (sb_mallocs b (sup_chain_sizes id ids t))).
    { apply (res_ok_slots_le A2 _ _ LE2); [|exact RS2].
      unfold sb_mallocs, sup_chain_sizes. cbn [fold_left]. unfold sb_malloc. cbn [sb_live sb_bytes sb_cap]. lia. }
    assert (RJ2 : rjr B (aa_MR API) CW_K (bv_unsigned sp) cw_writes (fun pn => In pn O) L A mem md L2 A2 m2 md2).
    { eapply (rjr_post B (aa_MR API) SEGS LAWS AX ERRNO_LOW); [exact RJ1 | exact POST | | | | | | exact LEN2 |].
      - rewrite SP1. unfold SUP_CHAIN_K. lia.
      - rewrite SP1. lia.
      - intros a Ha _. split; [unfold cw_writes; unfold rec_area in Ha; tauto|].
        unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Ha. lia.
      - intros p n Hp Hg Hn Hx. apply in_map_iff in Hx as ([a j] & Ea & Hj). cbn [fst] in Ea. subst a.
        assert (EJ : n = j).
        { apply (blocks_same_addr B _ LAWS L A mem md (ptr_addr L p)); [exact HMR | apply user_in_blocks; exact Hp
            | exact (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hj) | lia | exact (rec_rep_pos _ _ _ _ _ _ _ _ _ REP Hj)]. }
        subst j. exact (Hg Hj).
      - intros p n Hp _ Hn. destruct (In_dec pair_dec (ptr_addr L p, n) O) as [H|H]; [exact H|].
        exfalso. exact (Hn (proj1 (OK2 p n Hp H))).
      - intros H. rewrite INIT2 in H. discriminate. }
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -80)
                    [C8 (reg_get regs 24); C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21);
                     C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                     C8 (reg_get regs 8); C8 (reg_get regs 1)]).
    { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
      assert (Ha : alloc_ceiling <= bv_unsigned sp + -80 + i < 2 ^ 64) by lia.
      assert (N1 : ~ owned B L A (bv_unsigned sp + -80 + i))
        by (intros Ho; destruct (owned_low B _ LAWS _ _ _ _ _ MR1 Ho); lia).
      assert (N2 : ~ owned B L2 A2 (bv_unsigned sp + -80 + i))
        by (intros Ho; destruct (owned_low B _ LAWS _ _ _ _ _ HMR2 Ho); lia).
      assert (NS : ~ scratch_k B SUP_CHAIN_K R1 (bv_unsigned sp + -80 + i))
        by (unfold scratch_k; rewrite SP1; unfold SUP_CHAIN_K; intros [H|H]; lia).
      assert (NRA : ~ rec_area (bv_unsigned sp + -80 + i)) by (unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE; lia).
      destruct (HFR2 _ (or_introl Ha) N1 N2 NS NRA) as [E W]. split; [exact E | apply W]. }
    destruct (mr_model _ _ LAWS _ _ _ _ HMR2) as (Hh2 & Hl2 & _).
    assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp + -352))
      by exact (eq_trans (HP2 2 ltac:(unfold callee_saved; lia)) E1_2).
    rewrite E1_1, SEGS.
    eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E2_2. eapply cw_ret2; [exact FR2 | lia]. }
    intros ms3 (can3 & Q3 & EQ3). subst can3.
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    assert (E3_10 : getr R3 10 = Z_to_bv 64 q) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; exact A0').
    assert (PR3 : regs_preserved regs R3).
    { eapply (preserved_chain (fun r => (r =? 2) || (r =? 8) || (r =? 9) || ((18 <=? r) && (r <=? 24)))
                regs R1 R2 R3 _ _ X1 HP2 X3).
      - intros r Hr O0. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O0 | split; reflexivity]|]).
        subst r. split; reflexivity.
      - intros r Hr O0. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O0 | reflexivity]|]).
        subst r. discriminate O0. }
    assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
    rewrite RP. rewrite <- SEGS.
    apply SR_ret.
    exists fx2, L2, A2, R3, m2, md2, O', 6%nat, q, (Z.of_nat (length t) + 1).
    split; [reflexivity|].
    split; [exact FK|].
    split.
    { apply (rjr_final B (aa_MR API) CTX CW_K cw_writes (fun pn => In pn O)); [exact PREK | exact RJ2 | exact PR3 |].
      intros a k G. exact (in_map fst O (a, k) G). }
    split; [exact RA2|].
    split.
    { unfold VerbsRun.chain_run. rewrite CWC. cbn [VerbsRun.run_call]. rewrite SCM. cbn beta iota.
      split; [exact REP2|]. split; [apply cw_bytes_le; exact BQ | lia]. }
    split; [exact E3_10|].
    split; [exact INQ|].
    split; [intros HO; apply NQO; exact (in_map fst O' _ HO)|].
    split.
    { intros [a k] Hin HO. cbn [fst snd]. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & Ep & Hp).
      cbn [fst snd] in Ep. injection Ep as <- <-. pose proof (DIS2 p k' Hp HO). lia. }
    split.
    { apply (cw_toks CW_K (bv_unsigned sp) cw_writes O L A mem md L2 A2 m2 md2 tok ptrs tks cb ncb RJ2 TKS INB NOB);
        [lia | lia | lia | lia |]. intros a Ha. unfold cw_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha. lia. }
    split.
    { intros [a k] Hin HO. unfold blocks in Hin |- *. apply in_map_iff in Hin as ([p k'] & Ep & Hp).
      cbn [fst snd] in Ep. injection Ep as <- <-. destruct (OK2 p k' Hp HO) as (H1 & H2 & _).
      apply in_map_iff. exists (p, k'). cbn [fst snd]. rewrite H2. split; [reflexivity | exact H1]. }
    split; [exact BIN2|].
    split; [intros pn Hin HO HO'; destruct (OWN2 pn HO') as [H|H]; [exact (HO H) | exact (H Hin)]|].
    split; [exact LEN2|].
    split.
    { intros a k i Hin Hn Hi. apply (cw_rjr_blk _ _ _ O L A mem md L2 A2 m2 md2 a k i RJ2 Hin); [|exact Hi].
      intros G. apply Hn. exists k. exact G. }
    split; [rewrite SEGS in F182; exact (cw_ssp_of_f18 B m2 SEGS F182)|].
    split; [exact GSH2|].
    split; [lia|].
    apply (res_ok_slots_le A2 (sb_mallocs b (sup_chain_sizes id ids t))); [| | exact RES2].
    + unfold sb_mallocs, sup_chain_sizes. cbn [fold_left]. unfold sb_le, sb_malloc, sb_n, SB_REQ.
      cbn [sb_live sb_bytes sb_cap]. lia.
    + unfold sb_n. cbn [sb_live sb_bytes sb_cap]. lia.
Qed.

End CW.
