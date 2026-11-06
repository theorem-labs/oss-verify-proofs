(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec SeqExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg AsanAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanImgScan AsanImg.
Import ListNotations.

Module AsanSegs.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanImgScan AsanImg.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma find_seg1 : forall x, 0x3e000 <= x < 0xda000 -> find_segment ASEGS x 1 = Some AsanUbsan_segment_001.
Proof.
  intros x H. unfold AsanUbsan.M.loaded_segments, AsanUbsan_loaded_segments.
  cbn [find_segment seg_base seg_size AsanUbsan_segment_000 AsanUbsan_segment_001]. cbn [Z.of_N].
  replace (x + 1 <=? 65536 + 188416) with false by leb_false.
  replace (253952 <=? x) with true by leb_true. replace (x + 1 <=? 253952 + 638976) with true by leb_true.
  rewrite !andb_false_r. reflexivity.
Qed.
Lemma Hseg_img : forall x, 0x10000 <= x < 0x63c000 -> find_segment ASEGS x 1 <> None.
Proof.
  intros x H.
  destruct (Z_lt_le_dec x 0x3e000); [rewrite (find_seg0 x ltac:(lia)); discriminate|].
  destruct (Z_lt_le_dec x 0xda000); [rewrite (find_seg1 x ltac:(lia)); discriminate|].
  destruct (Z_lt_le_dec x 0xe0000); [rewrite (find_seg2 x ltac:(lia)); discriminate|].
  rewrite (find_seg3 x ltac:(lia)); discriminate.
Qed.
(* [comment removed for export] *)
Lemma Hseg_asan : forall x, 0x10000 <= x < 0x61a000 (* [comment removed for export] *) -> find_segment ASEGS x 1 <> None.
Proof. intros x H. apply Hseg_img. lia. Qed.
(* [comment removed for export] *)
End AsanSegs.

Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition rk (r : Z) : positive := bv_key (Z_to_bv 5 r).
Definition SP : lin := ladd (ladd (ladd (lscale 32768 (lvar 1)) (lscale 4096 (lvar 2))) (lscale 64 (lvar 3))) (lscale 16 (lvar 4)).
Definition ARGC := lvar 5. Definition ENVC := lvar 6. Definition P1 := lvar 8.
Definition UID := lvar 9. Definition HW := lvar 10. Definition LEN0 := lvar 11.
Definition BRK : lin := lscale 4096 (lvar 16).
Definition ENVP : lin := ladd (laddc SP 16) (lscale 8 ARGC).
Definition AUXV : lin := ladd (laddc ENVP 8) (lscale 8 ENVC).
Definition P0 : lin := laddc AUXV 160.
Definition PGSP : lin := ladd (lscale 32768 (lvar 1)) (lscale 4096 (lvar 2)).
Definition RANDP : lin := laddc (ladd PGSP (ladd (lscale 64 (lvar 7)) (lscale 8 (lvar 15)))) (-8).
Definition wb (l : lin) : list bval := st_bytes l (is_const l) 0 8.
Definition AUXC : list bval :=
  wb (lconst 3) ++ wb (lconst 0x10040) ++ wb (lconst 4) ++ wb (lconst 56) ++ wb (lconst 5) ++ wb (lconst 11) ++
  wb (lconst 16) ++ wb HW ++ wb (lconst 6) ++ wb (lconst 4096) ++ wb (lconst 11) ++ wb UID ++ wb (lconst 12) ++ wb UID ++
  wb (lconst 23) ++ wb (lconst 0) ++ wb (lconst 25) ++ wb RANDP ++ wb (lconst 0) ++ wb (lconst 0).
Definition RG_STK : list region :=
  [ RGz (laddc SP (-8388608)) 8388608 RZ TEmpty;
    RGz SP 8 RW (put_bytes TEmpty 0 (wb ARGC));
    RG (laddc SP 8) (laddc (lscale 8 ARGC) 8) RW (put_bytes TEmpty 0 (wb P0 ++ wb P1));
    RGz AUXV 160 RW (put_bytes TEmpty 0 AUXC);
    RGz RANDP 16 RW (put_bytes TEmpty 0 (st_bytes (lvar 12) None 0 8 ++ st_bytes (lvar 13) None 0 8)) ].
Definition RG0 : list region := RG_STK ++ IMG_RGS.
(* [comment removed for export] *)
Definition F0c (olo ohi xlo : Z) : list fact :=
  [FRange (ladd (lscale 64 (lvar 3)) (lscale 16 (lvar 4))) olo ohi; FRange (lvar 1) 0xfffeffff 0xffffffff; FRange (lvar 2) 0 7;
   FRange (lvar 3) 0 66; FRange (lvar 4) 0 3; FRange ARGC 1 1024; FRange ENVC 0 256; FRange (lsub (ladd (lscale 8 (lvar 7)) (lvar 15)) (ladd (ladd (lscale 8 (lvar 3)) (lscale 2 (lvar 4))) (ladd ARGC ENVC))) 24 300000;
   FRange (lvar 7) xlo 40000; FRange (lvar 15) 0 7; FRange LEN0 0 131071;
   FRange (lsub (ladd (lscale 64 (lvar 7)) (lscale 8 (lvar 15))) (ladd (lscale 64 (lvar 3)) (lscale 16 (lvar 4)))) 192 2300000; FRange UID 0 0xfffffffe; FRange (lvar 14) 0x7fff8000 0x800000000;
   FRange (lsub (lscale 512 (lvar 14)) (ladd (lscale 4096 (lvar 1)) (lscale 512 (lvar 2)))) 512 0x200000;
   FRange (lsub (lscale 512 (lvar 14)) (ladd (ladd (lscale 4096 (lvar 1)) (lscale 512 (lvar 2))) (ladd (lscale 8 (lvar 7)) (lvar 15)))) 1 514;
   FRange (lvar 16) 0x63c 0x8063c].
Definition S0c (olo ohi xlo : Z) : sst := SST (Z.of_N AsanUbsan.M.init_pc) (tset (rk 2) SP TEmpty) RG0 (F0c olo ohi xlo) 17 RNone.
(* [comment removed for export] *)
Definition F0 : list fact := F0c 176 4080 5.
Definition S0 : sst := S0c 176 4080 5.
Definition M0 : smodel := SM [] [] [] None BRK BRK SP [(ENVP, laddc (lscale 8 ENVC) 8); (P0, lsub RANDP P0)] [].

(* [comment removed for export] *)
Lemma SP_eq : SP = LIN 0 [(1%positive, 32768); (2%positive, 4096); (3%positive, 64); (4%positive, 16)]. Proof. vm_compute. reflexivity. Qed.

Abbreviation APH := AsanUbsan.M.phdrs.

(* [comment removed for export] *)
Lemma shr_mod_lo : forall x s, 0 <= s -> s + 8 <= 64 -> Z.shiftr (x mod 2 ^ 64) s mod 2 ^ 8 = Z.shiftr x s mod 2 ^ 8.
Proof.
  intros x s H1 H2. apply Z.bits_inj'. intros n Hn. destruct (Z.lt_ge_cases n 8) as [Hl|Hg].
  - rewrite !Z.mod_pow2_bits_low by exact Hl. rewrite !Z.shiftr_spec by exact Hn. apply Z.mod_pow2_bits_low. lia.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma shr_div_hi : forall x s, 0 <= s -> Z.shiftr (x / 2 ^ 64) s = Z.shiftr x (64 + s).
Proof. intros x s H. rewrite <- Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_shiftr by lia. reflexivity. Qed.

Lemma ext_lo : forall (r : bv 128) s, (Z.of_N s + 8 <= 64)%Z ->
  bv_extract s 8 r = bv_extract s 8 (Z_to_bv 64 (bv_unsigned r mod 2 ^ 64)).
Proof.
  intros r s Hs. apply bv_eq. rewrite !bv_extract_unsigned, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite (Z.mod_small (bv_unsigned r mod 2 ^ 64)) by (apply Z.mod_pos_bound; lia).
  change (Z.of_N 8) with 8. symmetry. apply shr_mod_lo; lia.
Qed.
Lemma ext_hi : forall (r : bv 128) s, (Z.of_N s + 8 <= 64)%Z ->
  bv_extract (64 + s) 8 r = bv_extract s 8 (Z_to_bv 64 (bv_unsigned r / 2 ^ 64)).
Proof.
  intros r s Hs. apply bv_eq. rewrite !bv_extract_unsigned, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  pose proof (bv_unsigned_in_range _ r) as Rr. unfold bv_modulus in Rr. change (2 ^ Z.of_N 128) with (2 ^ 64 * 2 ^ 64) in Rr.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite (Z.mod_small (bv_unsigned r / 2 ^ 64)).
  2: { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite shr_div_hi by lia. rewrite N2Z.inj_add. reflexivity.
Qed.

Lemma rnd_lo : forall r : bv 128, firstn 8 (at_random_bytes r) = word_le8 (Z_to_bv 64 (bv_unsigned r mod 2 ^ 64)).
Proof.
  intros r. cbn [at_random_bytes firstn]. unfold word_le8.
  repeat (f_equal; [apply ext_lo; cbn; lia|]). f_equal. apply ext_lo; cbn; lia.
Qed.
Lemma rnd_hi : forall r : bv 128, firstn 8 (skipn 8 (at_random_bytes r)) = word_le8 (Z_to_bv 64 (bv_unsigned r / 2 ^ 64)).
Proof.
  intros r. cbn [at_random_bytes firstn skipn]. unfold word_le8.
  repeat (f_equal; [first [apply (ext_hi r 0%N) | apply (ext_hi r 8%N) | apply (ext_hi r 16%N) | apply (ext_hi r 24%N) | apply (ext_hi r 32%N)
                          | apply (ext_hi r 40%N) | apply (ext_hi r 48%N) | apply (ext_hi r 56%N)]; cbn; lia|]).
  f_equal. apply (ext_hi r 56%N). cbn; lia.
Qed.

(* [comment removed for export] *)
Definition cbs (R : region) : option (Z * Z) :=
  match is_const (rg_base R), is_const (rg_size R) with Some a, Some n => Some (a, n) | _, _ => None end.
Fixpoint cdisj_b (rgs : list region) : bool :=
  match rgs with
  | [] => true
  | R :: rs => match cbs R with
               | Some (a, n) => (forallb (fun R' => match cbs R' with Some (a', n') => (Z.leb (a + n) a' || Z.leb (a' + n') a)%bool | None => false end) rs
                                 && cdisj_b rs)%bool
               | None => false
               end
  end.
Lemma cbs_sound : forall E R a n, cbs R = Some (a, n) -> bv_unsigned (lden E (rg_base R)) = a /\ rsz E R = n.
Proof.
  intros E R a n H. unfold cbs in H. destruct (is_const (rg_base R)) as [a0|] eqn:Ha; [|discriminate].
  destruct (is_const (rg_size R)) as [n0|] eqn:Hn; [|discriminate]. injection H as <- <-.
  split; [apply is_const_u; exact Ha | unfold rsz; apply is_const_u; exact Hn].
Qed.
Lemma cdisj_sound : forall E rgs, cdisj_b rgs = true -> rgs_disj E rgs.
Proof.
  intros E rgs. induction rgs as [|R rs IH]; intros H; cbn [rgs_disj]; [exact I|]. cbn [cdisj_b] in H.
  destruct (cbs R) as [[a n]|] eqn:Hc; [|discriminate]. apply andb_prop in H as [H1 H2]. split; [|exact (IH H2)].
  rewrite Forall_forall. rewrite forallb_forall in H1. intros R' HR'. specialize (H1 R' HR').
  destruct (cbs R') as [[a' n']|] eqn:Hc'; [|discriminate]. destruct (cbs_sound E R a n Hc) as [A1 S1]. destruct (cbs_sound E R' a' n' Hc') as [A2 S2].
  unfold rg_disj. rewrite A1, S1, A2, S2. apply orb_prop in H1 as [H1|H1]; apply Z.leb_le in H1; lia.
Qed.
Lemma rgs_disj_app : forall E l1 l2, rgs_disj E l1 -> rgs_disj E l2 -> (forall R1 R2, In R1 l1 -> In R2 l2 -> rg_disj E R1 R2) ->
  rgs_disj E (l1 ++ l2).
Proof.
  intros E l1 l2. induction l1 as [|R l1 IH]; intros H1 H2 H3; [exact H2|]. destruct H1 as [Hx Hl1]. cbn [app rgs_disj]. split.
  - apply Forall_app. split; [exact Hx|]. rewrite Forall_forall. intros R2 HR2. apply H3; [left; reflexivity | exact HR2].
  - apply IH; [exact Hl1 | exact H2 |]. intros R1 R2 HR1 HR2. apply H3; [right; exact HR1 | exact HR2].
Qed.
Lemma img_cdisj : cdisj_b IMG_RGS = true. Proof. vm_compute. reflexivity. Qed.
Lemma img_low : forallb (fun R => match cbs R with Some (a, n) => (Z.leb 0x10000 a && Z.leb (a + n) 0x63c000 && Z.ltb 0 n)%bool | None => false end) IMG_RGS = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma length_st_bytes' : forall v z j n, length (st_bytes v z j n) = n.
Proof. intros v z j n. revert j. induction n as [|n IH]; intros j; [reflexivity | cbn [st_bytes length]; rewrite IH; reflexivity]. Qed.
Lemma length_wb : forall l, length (wb l) = 8%nat. Proof. intros l. apply length_st_bytes'. Qed.

Lemma flat_wb_nth : forall ls k i, (i < 8)%nat ->
  nth_error (flat_map wb ls) (8 * k + i) = match nth_error ls k with Some l => nth_error (wb l) i | None => None end.
Proof.
  induction ls as [|l ls IH]; intros k i Hi.
  - cbn [flat_map]. rewrite !nth_error_nil. reflexivity.
  - cbn [flat_map]. destruct k as [|k].
    + rewrite Nat.mul_0_r, Nat.add_0_l. rewrite nth_error_app1 by (rewrite length_wb; exact Hi). reflexivity.
    + rewrite nth_error_app2 by (rewrite length_wb; lia). rewrite length_wb.
      replace (8 * Datatypes.S k + i - 8)%nat with (8 * k + i)%nat by lia. exact (IH k i Hi).
Qed.

Lemma tget_put0 : forall (bvs : list bval) p v, tget p (put_bytes TEmpty 0 bvs) = Some v ->
  Zpos p - 1 < Z.of_nat (length bvs) /\ nth_error bvs (Z.to_nat (Zpos p - 1)) = Some v.
Proof.
  intros bvs p v H. rewrite put_bytes_spec in H by lia.
  destruct (Z.leb 0 (Zpos p - 1) && Z.ltb (Zpos p - 1) (0 + Z.of_nat (length bvs)))%bool eqn:Hc; [|rewrite tget_empty in H; discriminate].
  apply andb_prop in Hc as [_ Hc]. apply Z.ltb_lt in Hc. split; [lia|]. rewrite Z.sub_0_r in H. exact H.
Qed.

Lemma wb_den : forall E l i v, nth_error (wb l) i = Some v -> nth_error (word_le8 (lden E l)) i = Some (bden E v).
Proof.
  intros E l i v H. rewrite n_to_le_8_spec. unfold word_to_le_bytes.
  exact (st_bytes_ok E l (lden E l) SZ8 eq_refl i v H).
Qed.

Section Words.
Variable segs : list Segment.
#[using="Type"] Lemma rg_tracked_words : forall E m (A : Z) ls (ws : list word),
  length ls = length ws ->
  (forall k l w, nth_error ls k = Some l -> nth_error ws k = Some w -> lden E l = w) ->
  (forall k w i b, nth_error ws k = Some w -> nth_error (word_le8 w) i = Some b ->
     rd1 segs m (Z_to_bv 64 (A + (8 * Z.of_nat k + Z.of_nat i))) = Some b) ->
  forall p v, tget p (put_bytes TEmpty 0 (flat_map wb ls)) = Some v ->
    Zpos p - 1 < 8 * Z.of_nat (length ls) /\ rd1 segs m (Z_to_bv 64 (A + (Zpos p - 1))) = Some (bden E v).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m A ls ws Hl Hv Hm p v Hp. destruct (tget_put0 _ p v Hp) as [Hlt Hn].
  assert (Hlen : length (flat_map wb ls) = (8 * length ls)%nat).
  { clear. induction ls as [|l ls IH]; [reflexivity|]. cbn [flat_map length]. rewrite length_app, length_wb, IH. lia. }
  rewrite Hlen in Hlt. split; [lia|].
  set (o := Z.to_nat (Zpos p - 1)) in *.
  assert (Ho : o = (8 * (o / 8) + o mod 8)%nat) by (apply Nat.div_mod; lia).
  rewrite Ho in Hn. rewrite flat_wb_nth in Hn by (apply Nat.mod_upper_bound; lia).
  destruct (nth_error ls (o / 8)) as [l|] eqn:Hk; [|discriminate].
  destruct (nth_error ws (o / 8)) as [w|] eqn:Hw.
  - pose proof (Hv _ _ _ Hk Hw) as Hlw. pose proof (wb_den E l _ v Hn) as Hb. rewrite Hlw in Hb.
    pose proof (Hm _ _ _ _ Hw Hb) as X. replace (A + (Zpos p - 1)) with (A + (8 * Z.of_nat (o / 8) + Z.of_nat (o mod 8))); [exact X|].
    assert (Z.of_nat o = Zpos p - 1) by (unfold o; rewrite Z2Nat.id by lia; reflexivity). rewrite Ho in H. lia.
  - exfalso. apply nth_error_None in Hw. rewrite <- Hl in Hw. assert (Hlt' : (o / 8 < length ls)%nat) by (apply nth_error_Some; rewrite Hk; discriminate). lia.
Qed.
End Words.

(* [comment removed for export] *)
Lemma res_eq : segments_reserved ASEGS =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x2e000); (Z_to_bv 64 0x3e000, Z_to_bv 64 0x9c000);
   (Z_to_bv 64 0xda000, Z_to_bv 64 0x6000); (Z_to_bv 64 0xe0000, Z_to_bv 64 0x55c000)].
Proof. vm_compute. reflexivity. Qed.
Lemma covered_of : forall l x c, In c l -> B c <= x < B c + S c -> covered l x = true.
Proof. intros l x c Hc Hx. unfold covered. apply existsb_exists. exists c. split; [exact Hc|]. unfold in_iv, in_rng. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma covered_res : forall x, 0x10000 <= x < 0x63c000 -> covered (segments_reserved ASEGS) x = true.
Proof.
  intros x Hx. rewrite res_eq.
  destruct (Z_lt_ge_dec x 0x3e000); [apply (covered_of _ _ (Z_to_bv 64 0x10000, Z_to_bv 64 0x2e000)); [left; reflexivity|]|].
  { unfold B, S; cbn [fst snd]. rewrite !u_small64 by (unfold two64; lia). lia. }
  destruct (Z_lt_ge_dec x 0xda000); [apply (covered_of _ _ (Z_to_bv 64 0x3e000, Z_to_bv 64 0x9c000)); [right; left; reflexivity|]|].
  { unfold B, S; cbn [fst snd]. rewrite !u_small64 by (unfold two64; lia). lia. }
  destruct (Z_lt_ge_dec x 0xe0000); [apply (covered_of _ _ (Z_to_bv 64 0xda000, Z_to_bv 64 0x6000)); [right; right; left; reflexivity|]|].
  { unfold B, S; cbn [fst snd]. rewrite !u_small64 by (unfold two64; lia). lia. }
  apply (covered_of _ _ (Z_to_bv 64 0xe0000, Z_to_bv 64 0x55c000)); [right; right; right; left; reflexivity|].
  unfold B, S; cbn [fst snd]. rewrite !u_small64 by (unfold two64; lia). lia.
Qed.

Lemma ld_word_le8 : forall w, ld_word SZ8 true (word_le8 w) = w.
Proof.
  intros w. apply bv_eq. unfold ld_word, le_bytes_to_word. rewrite bv_extract_unsigned, Z_to_bv_unsigned, bytes_le_n_to_le_8.
  unfold bv_wrap, bv_modulus. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r, Z.mod_mod by lia. apply Z.mod_small. apply bv_unsigned_in_range.
Qed.

Section Entry.
Variables (sp brk0 mb : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
Let av := in_argv inp.
Let ev := in_envp inp.
Let uid := in_uid inp.
Let hw := in_hwcap inp.
Let bsb := build_stack_bytes APH sp av ev uid hw draw.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk ASEGS brk0.
Hypothesis Hfit : entry_stack_fits sp av ev.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hid : valid_id uid.

Definition usp : Z := bv_unsigned sp.
Definition RP : Z := bv_unsigned (at_random_ptr sp av ev).
(* [comment removed for export] *)
Definition PG : Z := usp / 4096 - (if usp mod 4096 <=? 160 then 1 else 0).
Definition OFS : Z := usp - 4096 * PG.
Definition DD : Z := RP + 8 - 4096 * PG.
Definition PTOP : Z := entry_page_top sp bsb.
Definition vals : list word :=
  [ Z_to_bv 64 0;
    Z_to_bv 64 (PG / 8); Z_to_bv 64 (PG mod 8); Z_to_bv 64 (OFS / 64); Z_to_bv 64 ((OFS mod 64) / 16);
    Z_to_bv 64 (Z.of_nat (length av)); Z_to_bv 64 (Z.of_nat (length ev)); Z_to_bv 64 (DD / 64);
    (if Nat.leb 2 (length av) then cat_argv_ptr sp av ev 1 else Z_to_bv 64 0);
    uid; hw; Z_to_bv 64 (Z.of_nat (length (nth 0 av []))); Z_to_bv 64 (bv_unsigned (ed_random draw) mod 2 ^ 64);
    Z_to_bv 64 (bv_unsigned (ed_random draw) / 2 ^ 64); Z_to_bv 64 (PTOP / 4096); Z_to_bv 64 ((DD mod 64) / 8);
    Z_to_bv 64 (bv_unsigned brk0 / 4096) ].
Definition E0 : valu := fun p => List.nth (Pos.to_nat p) vals (Z_to_bv 64 0).

(* [comment removed for export] *)
#[using="Type"] Lemma uZ : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. LiaFast.lf_pins LiaFast.u0. intros z H. apply u_small64. unfold two64. lia. Qed.

#[using="inp av ev Hsp Hfit Hva Hve"] Lemma usp_b : 0x7fff80000000 <= usp < 0x800000000000 /\ usp mod 16 = 0.
Proof. LiaFast.lf_pins (fun (inp av ev Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0).
  destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in *. unfold entry_stack_fits in Hfit.
  pose proof (entry_stack_span_bound av ev Hva Hve) as Hs. unfold entry_stack_span in Hfit.
  pose proof (total_arg_bytes_nonneg av). pose proof (total_arg_bytes_nonneg ev). unfold sp_window_hi, auxv_size in *. unfold usp. lia.
Qed.
#[using="Hva"] Lemma argc_b : 1 <= Z.of_nat (length av) <= 1024. Proof. LiaFast.lf_pins (fun (Hva : LiaFast.U) => LiaFast.u0). destruct Hva as [[H1 H2] _]. lia. Qed.
#[using="Hve"] Lemma envc_b : 0 <= Z.of_nat (length ev) <= 256. Proof. LiaFast.lf_pins (fun (Hve : LiaFast.U) => LiaFast.u0). destruct Hve as [H1 _]. lia. Qed.
#[using="Hva Hve"] Lemma bsb_b : Z.of_nat (length bsb) <= 2240000. Proof. LiaFast.lf_pins (fun (Hva Hve : LiaFast.U) => LiaFast.u0). exact (lay_bsb_len APH sp draw av ev uid hw Hva Hve). Qed.
#[using="Hsp Hfit Hva Hve"] Lemma rp_b : RP + 16 = usp + Z.of_nat (length bsb) /\ RP mod 8 = 0 /\ usp + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 184 <= RP.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0).
  destruct usp_b as (U1 & U3). destruct Hsp as (H1 & H2 & H3).
  destruct (at_random_off ASEGS APH sp draw av ev uid hw Hva Hve H2) as (off & Hp & Hl & Hm & _).
  pose proof (auxv_off_bound APH sp draw av ev uid hw) as Hao. unfold auxv_off in Hao. pose proof bsb_b as Hb.
  assert (HR : RP = usp + Z.of_nat off).
  { unfold RP. rewrite Hp. unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with 18446744073709551616. rewrite Z.add_mod_idemp_r by lia. apply Z.mod_small. unfold usp in *. fold bsb in Hl. lia. }
  fold bsb in Hl, Hao. split; [lia|]. split.
  - rewrite HR. rewrite Z.add_mod by lia. replace (usp mod 8) with 0 by (unfold usp; rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2; reflexivity); rewrite H3; reflexivity).
    rewrite Hm. reflexivity.
  - lia.
Qed.
#[using="Hfit"] Lemma ptop_b : usp + Z.of_nat (length bsb) <= PTOP <= 0x800000000000 /\ PTOP mod 4096 = 0 /\ PTOP < usp + Z.of_nat (length bsb) + 4096.
Proof. LiaFast.lf_pins (fun (Hfit : LiaFast.U) => LiaFast.u0).
  pose proof (entry_page_top_within_window APH sp av ev uid hw draw Hfit) as Hw. fold bsb in Hw.
  pose proof (entry_page_top_ge sp bsb) as Hg. unfold PTOP. unfold sp_window_hi in Hw. unfold entry_block_top in Hg.
  unfold entry_page_top, page_round_up_Z, page_size in *. unfold entry_block_top in *. unfold usp.
  set (z := bv_unsigned sp + Z.of_nat (length bsb)) in *.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hb.
  split; [lia|]. split; [apply Z_mod_mult | lia].
Qed.

(* [comment removed for export] *)
Definition V1 : Z := PG / 8.
Definition V2 : Z := PG mod 8.
Definition V3 : Z := OFS / 64.
Definition V4 : Z := (OFS mod 64) / 16.
#[using="inp av ev Hsp Hfit Hva Hve"] Lemma ofs_b : usp = 4096 * PG + OFS /\ OFS mod 16 = 0 /\
  OFS = usp mod 4096 + (if usp mod 4096 <=? 160 then 4096 else 0) /\ 176 <= OFS <= 4256 /\ 0x7fff7ffff <= PG.
Proof. LiaFast.lf_pins (fun (inp av ev Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0).
  destruct usp_b as (U1 & U2). unfold OFS, PG.
  pose proof (Z.div_mod usp 4096 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)) as M1.
  assert (M16 : usp mod 4096 mod 16 = 0) by (rewrite Z.mod_mod_divide by (exists 256; reflexivity); exact U2).
  assert (Hpg : 0x7fff80 <= usp / 4096 / 8) by (rewrite Z.div_div by lia; apply Z.div_le_lower_bound; lia).
  destruct (usp mod 4096 <=? 160) eqn:Hc; [apply Z.leb_le in Hc | apply Z.leb_gt in Hc].
  - split; [lia|]. split; [replace (usp - 4096 * (usp / 4096 - 1)) with (usp mod 4096 + 16 * 256) by lia; rewrite Z.add_mod, M16 by lia; reflexivity|].
    split; [lia|]. split; [|lia]. lia.
  - split; [lia|]. split; [replace (usp - 4096 * (usp / 4096 - 0)) with (usp mod 4096) by lia; exact M16|].
    split; [lia|]. split; [|lia]. lia.
Qed.

(* [comment removed for export] *)
Variables (olo ohi xlo : Z).
Hypothesis HC : olo <= OFS <= ohi.
Hypothesis Hxlo : 0 <= olo /\ 64 * xlo <= 200 + olo.
Hypothesis Hlim : 0 <= lim.
Definition AC : Z := Z.of_nat (length av).
Definition EC : Z := Z.of_nat (length ev).
Definition LB : Z := Z.of_nat (length bsb).
Definition DX : Z := DD / 64.
Definition DY : Z := (DD mod 64) / 8.
Definition TG : Z := PTOP / 4096.
Definition BP : Z := bv_unsigned brk0 / 4096.
Definition L0 : Z := Z.of_nat (length (nth 0 av [])).
#[using="Type"] Lemma rtop : reserved_top (segments_reserved ASEGS) = 0x63c000. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Hbrk"] Lemma brk_b : 0x63c000 <= bv_unsigned brk0 <= 0x63c000 + 2 ^ 31 /\ bv_unsigned brk0 mod 4096 = 0.
Proof. LiaFast.lf_pins (fun (Hbrk : LiaFast.U) => LiaFast.u0). destruct Hbrk as (B1 & B2 & B3). rewrite rtop in B1, B2. unfold brk_aslr_max, page_size in *. lia. Qed.
#[using="Hbrk"] Lemma bp_b : 0x63c <= BP <= 0x8063c.
Proof. LiaFast.lf_pins (fun (Hbrk : LiaFast.U) => LiaFast.u0). destruct brk_b as [B1 _]. unfold BP. split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia. Qed.

#[using="draw uid hw bsb Hsp Hfit Hva Hve"] Lemma dd_b : 8 + OFS + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 184 <= DD <= 8192 + 2240000 /\ DD mod 8 = 0.
Proof. LiaFast.lf_pins (fun (draw uid hw bsb Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0).
  destruct rp_b as (R1 & R2 & R3). pose proof bsb_b. destruct usp_b as (U1 & U2). destruct ofs_b as (O1 & O2 & O3 & O4 & O5).
  unfold DD. split; [clear - R1 R3 H O1 O4 U1; lia|].
  replace (RP + 8 - 4096 * PG) with (RP + 8 * (1 - 512 * PG)) by ring. rewrite Z.add_mod by lia. rewrite R2, Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="inp av ev Hsp Hfit Hva Hve HC"] Lemma rel_sp : usp = 4096 * PG + OFS /\ 4096 * PG = 32768 * V1 + 4096 * V2 /\ OFS = 64 * V3 + 16 * V4 /\
  olo <= OFS <= ohi /\ 176 <= OFS <= 4256 /\ 0 <= V2 < 8 /\ 0 <= V3 < 67 /\ 0 <= V4 < 4 /\ 0x7fff80000000 <= usp < 0x800000000000.
Proof. LiaFast.lf_pins (fun (inp av ev Hsp Hfit Hva Hve HC : LiaFast.U) => LiaFast.u0).
  destruct usp_b as (U1 & U2). destruct ofs_b as (O1 & O2 & O3 & O4 & O5). unfold V1, V2, V3, V4.
  assert (E2 : PG = 8 * (PG / 8) + PG mod 8) by (apply Z.div_mod; lia).
  assert (E3 : OFS = 64 * (OFS / 64) + OFS mod 64) by (apply Z.div_mod; lia).
  assert (E4 : OFS mod 64 = 16 * (OFS mod 64 / 16)).
  { rewrite (Z.div_mod (OFS mod 64) 16) at 1 by lia. rewrite Z.mod_mod_divide by (exists 4; reflexivity). rewrite O2. ring. }
  pose proof (Z.mod_pos_bound PG 8 ltac:(lia)) as M2. pose proof (Z.mod_pos_bound OFS 64 ltac:(lia)) as M3.
  assert (B3 : 0 <= OFS / 64 < 67) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (B4 : 0 <= OFS mod 64 / 16 < 4) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  split; [exact O1|]. split; [clear - E2; lia|]. split; [clear - E3 E4; lia|].
  split; [exact HC|]. split; [exact O4|]. split; [exact M2|]. split; [exact B3|]. split; [exact B4|]. exact U1.
Qed.

#[using="Hsp Hfit Hva Hve"] Lemma rel_rp : DD = 64 * DX + 8 * DY /\ 0 <= DY < 8 /\ DD = RP + 8 - 4096 * PG /\ RP + 16 = usp + LB /\
  usp + 8 * AC + 8 * EC + 184 <= RP /\ 0 <= LB <= 2240000 /\ 1 <= AC <= 1024 /\ 0 <= EC <= 256.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0).
  destruct dd_b as (D1 & D2). destruct rp_b as (R1 & R2 & R3). pose proof bsb_b as B. pose proof argc_b as A. pose proof envc_b as Ev.
  assert (E5 : DD = 64 * DX + 8 * DY).
  { unfold DX, DY. pose proof (Z.div_mod DD 64 ltac:(lia)) as Q1. pose proof (Z.div_mod (DD mod 64) 8 ltac:(lia)) as Q2.
    assert (Q3 : DD mod 64 mod 8 = 0) by (rewrite Z.mod_mod_divide by (exists 8; reflexivity); exact D2). rewrite Q3 in Q2. clear - Q1 Q2. lia. }
  assert (B6 : 0 <= DY < 8) by (unfold DY; pose proof (Z.mod_pos_bound DD 64 ltac:(lia)); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold LB, AC, EC. split; [exact E5|]. split; [exact B6|]. split; [reflexivity|]. split; [exact R1|]. split; [exact R3|].
  split; [lia|]. split; [exact A | exact Ev].
Qed.

#[using="Hfit"] Lemma rel_top : usp + LB <= PTOP <= 0x800000000000 /\ PTOP = 4096 * TG /\ PTOP < usp + LB + 4096.
Proof. LiaFast.lf_pins (fun (Hfit : LiaFast.U) => LiaFast.u0).
  destruct ptop_b as (P1 & P2 & P3). unfold LB, TG. split; [exact P1|]. split; [|exact P3].
  pose proof (Z.div_mod PTOP 4096 ltac:(lia)) as Q. rewrite P2 in Q. lia.
Qed.

#[using="Hsp Hfit Hva Hve"] Lemma vz1 : vz E0 1 = V1.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0).
  change (vz E0 1) with (bv_unsigned (Z_to_bv 64 V1)). destruct usp_b. destruct ofs_b as (O1 & _ & _ & O4 & O5). apply uZ. unfold V1.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
#[using="Type"] Lemma vz2 : vz E0 2 = V2.
Proof. LiaFast.lf_pins LiaFast.u0. change (vz E0 2) with (bv_unsigned (Z_to_bv 64 V2)). apply uZ. unfold V2. pose proof (Z.mod_pos_bound PG 8 ltac:(lia)). lia. Qed.
#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma vz3 : vz E0 3 = V3.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0). change (vz E0 3) with (bv_unsigned (Z_to_bv 64 V3)). apply uZ. destruct rel_sp as (_ & _ & _ & _ & _ & _ & B & _). lia. Qed.
#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma vz4 : vz E0 4 = V4.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0). change (vz E0 4) with (bv_unsigned (Z_to_bv 64 V4)). apply uZ. destruct rel_sp as (_ & _ & _ & _ & _ & _ & _ & B & _). lia. Qed.
#[using="Hva"] Lemma vz5 : vz E0 5 = AC.
Proof. LiaFast.lf_pins (fun (Hva : LiaFast.U) => LiaFast.u0). change (vz E0 5) with (bv_unsigned (Z_to_bv 64 AC)). apply uZ. pose proof argc_b. unfold AC. lia. Qed.
#[using="Hve"] Lemma vz6 : vz E0 6 = EC.
Proof. LiaFast.lf_pins (fun (Hve : LiaFast.U) => LiaFast.u0). change (vz E0 6) with (bv_unsigned (Z_to_bv 64 EC)). apply uZ. pose proof envc_b. unfold EC. lia. Qed.
#[using="Hsp Hfit Hva Hve"] Lemma vz7 : vz E0 7 = DX.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0). change (vz E0 7) with (bv_unsigned (Z_to_bv 64 DX)). apply uZ. destruct dd_b as [D1 _]. unfold DX. destruct ofs_b as (_ & _ & _ & O4 & _). split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
#[using="Type"] Lemma vz9 : vz E0 9 = bv_unsigned uid. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma vz10 : vz E0 10 = bv_unsigned hw. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Hva"] Lemma vz11 : vz E0 11 = L0.
Proof. LiaFast.lf_pins (fun (Hva : LiaFast.U) => LiaFast.u0). change (vz E0 11) with (bv_unsigned (Z_to_bv 64 L0)). apply uZ. pose proof (valid_argv_str_len av 0 Hva ltac:(pose proof argc_b; lia)). unfold L0. lia. Qed.
#[using="Hsp Hfit Hva Hve"] Lemma vz14 : vz E0 14 = TG.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0). change (vz E0 14) with (bv_unsigned (Z_to_bv 64 TG)). apply uZ. destruct rel_top as ((P1 & P1b) & P2 & _). destruct usp_b. destruct rel_rp as (_ & _ & _ & _ & _ & HLB & _). lia. Qed.
#[using="Hsp Hfit Hva Hve"] Lemma vz15 : vz E0 15 = DY.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0). change (vz E0 15) with (bv_unsigned (Z_to_bv 64 DY)). apply uZ. destruct rel_rp as (_ & B & _). lia. Qed.
#[using="Hbrk"] Lemma vz16 : vz E0 16 = BP.
Proof. LiaFast.lf_pins (fun (Hbrk : LiaFast.U) => LiaFast.u0). change (vz E0 16) with (bv_unsigned (Z_to_bv 64 BP)). apply uZ. pose proof bp_b. lia. Qed.

Ltac sgn_clean := repeat match goal with |- context [sgn64 ?k] => let v := eval vm_compute in (sgn64 k) in change (sgn64 k) with v end.
Ltac vz_clean := rewrite ?vz1, ?vz2, ?vz3, ?vz4, ?vz5, ?vz6, ?vz7, ?vz9, ?vz10, ?vz11, ?vz14, ?vz15, ?vz16.
(* [comment removed for export] *)
Ltac fu := match goal with |- context [bv_unsigned (lden E0 ?f)] =>
  let v := eval vm_compute in f in change f with v; rewrite (u_izl E0 v); [|unfold izl; cbn [tsumz l_c l_t]; sgn_clean; vz_clean; unfold M64] end;
  unfold izl; cbn [tsumz l_c l_t]; sgn_clean; vz_clean.

#[using="Hsp Hbrk Hfit Hva Hve Hid HC Hxlo"] Theorem F0_ok : Forall (fact_ok E0) (F0c olo ohi xlo).
Proof. LiaFast.lf_pins (fun (Hsp Hbrk Hfit Hva Hve Hid HC Hxlo : LiaFast.U) => LiaFast.u0).
  pose proof rel_sp as (S1 & S2 & S3 & S4 & S4b & S5 & S6 & S7 & S8). pose proof rel_rp as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  pose proof rel_top as (T1 & T2 & T3). pose proof bp_b as B.
  assert (Hu : 0 <= bv_unsigned uid <= 0xfffffffe) by (unfold valid_id in Hid; pose proof (bv_unsigned_in_range _ uid) as Ub; unfold bv_modulus in Ub; lia).
  assert (HL : 0 <= L0 <= 131071) by (unfold L0; pose proof (valid_argv_str_len av 0 Hva ltac:(pose proof argc_b; lia)); lia).
  clearbody av ev uid hw bsb.
  unfold F0c. repeat (apply Forall_cons). all: try (constructor; fail).
  all: cbn [fact_ok]; fu; clear - S1 S2 S3 S4 S4b S5 S6 S7 S8 R1 R2 R3 R4 R5 R6 R7 R8 T1 T2 T3 B Hu HL Hxlo; lia.
Qed.

(* [comment removed for export] *)
Definition stk : word -> option byte := stack_to_mem sp (entry_stack_image APH sp av ev uid hw draw).
Definition m0 : word -> option byte := ms_mem (init_machine_state ASEGS AsanUbsan.M.init_pc APH sp draw av ev uid hw).

#[using="Type"] Lemma m0_eq : forall x, m0 x = match stk x with Some b => Some b | None =>
    if ((usp - stack_max_size <=? bv_unsigned x) && (bv_unsigned x <? usp))%bool then Some (Z_to_bv 8 0) else None end.
Proof. LiaFast.lf_pins LiaFast.u0. intros x. reflexivity. Qed.

#[using="Type"] Lemma len_img : length (entry_stack_image APH sp av ev uid hw draw) = (length bsb + entry_slack_len sp bsb)%nat.
Proof. LiaFast.lf_pins LiaFast.u0. unfold entry_stack_image. cbv zeta. rewrite length_app, length_entry_slack. reflexivity. Qed.

#[using="Type"] Lemma stk_below : forall x, bv_unsigned x < usp -> stk x = None.
Proof. LiaFast.lf_pins LiaFast.u0. intros x Hx. unfold stk, stack_to_mem. replace (bv_unsigned sp <=? bv_unsigned x) with false by (symmetry; apply Z.leb_gt; unfold usp in Hx; lia). reflexivity. Qed.

#[using="Type"] Lemma stk_in : forall x, usp <= bv_unsigned x < usp + Z.of_nat (length bsb) ->
  stk x = nth_error bsb (Z.to_nat (bv_unsigned x - usp)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x Hx. unfold stk, stack_to_mem. unfold usp in *.
  replace (bv_unsigned sp <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
  replace (bv_unsigned x - bv_unsigned sp <? Z.of_nat (length (entry_stack_image APH sp av ev uid hw draw))) with true
    by (symmetry; apply Z.ltb_lt; rewrite len_img; lia).
  unfold entry_stack_image. cbv zeta. apply nth_error_app1. lia.
Qed.

#[using="Type"] Lemma m0_in : forall x, usp <= bv_unsigned x < usp + Z.of_nat (length bsb) -> exists b, m0 x = Some b /\ stk x = Some b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x Hx. rewrite m0_eq. rewrite (stk_in x Hx). destruct (nth_error bsb (Z.to_nat (bv_unsigned x - usp))) as [b|] eqn:Hb.
  - exists b. split; reflexivity.
  - exfalso. apply nth_error_None in Hb. lia.
Qed.

#[using="Type"] Lemma m0_win : forall x, usp - 8388608 <= bv_unsigned x < usp -> m0 x = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x Hx. rewrite m0_eq, (stk_below x ltac:(lia)). unfold stack_max_size.
  replace (usp - 8 * 1024 * 1024 <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
  replace (bv_unsigned x <? usp) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

#[using="Type"] Lemma m0_low : forall x, bv_unsigned x < usp - 8388608 -> m0 x = None.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x Hx. rewrite m0_eq, (stk_below x ltac:(lia)). unfold stack_max_size.
  replace (usp - 8 * 1024 * 1024 <=? bv_unsigned x) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

#[using="Type"] Lemma zbv_add1' : forall x : Z, (Z_to_bv 64 x + 1)%bv = Z_to_bv 64 (x + 1).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned (1%bv : bv 64)) with 1. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_rd1' : forall m (a : Z) n bs, 0 <= a -> a + Z.of_nat n <= two64 ->
  rdn ASEGS m (Z_to_bv 64 a) n = Some bs ->
  forall j b, nth_error bs j = Some b -> rd1 ASEGS m (Z_to_bv 64 (a + Z.of_nat j)) = Some b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n. revert a. induction n as [|n IH]; intros a bs Ha Hn H j b Hj; cbn [rdn] in H.
  - injection H as <-. destruct j; discriminate.
  - unfold rd1. destruct (m (Z_to_bv 64 a)) as [b0|] eqn:Hm.
    + rewrite zbv_add1' in H. destruct (rdn ASEGS m (Z_to_bv 64 (a + 1)) n) as [r|] eqn:Hr; [|discriminate].
      injection H as <-. destruct j as [|j]; cbn [nth_error] in Hj.
      * injection Hj as <-. rewrite Z.add_0_r, Hm. reflexivity.
      * pose proof (IH (a + 1) r ltac:(lia) ltac:(lia) Hr j b Hj) as Hx. unfold rd1 in Hx.
        replace (a + Z.of_nat (Datatypes.S j)) with (a + 1 + Z.of_nat j) by lia. exact Hx.
    + destruct (seg_rom ASEGS (Z_to_bv 64 a)) as [b0|] eqn:Hs; [|discriminate].
      rewrite zbv_add1' in H. destruct (rdn ASEGS m (Z_to_bv 64 (a + 1)) n) as [r|] eqn:Hr; [|discriminate].
      injection H as <-. destruct j as [|j]; cbn [nth_error] in Hj.
      * injection Hj as <-. rewrite Z.add_0_r, Hm. exact Hs.
      * pose proof (IH (a + 1) r ltac:(lia) ltac:(lia) Hr j b Hj) as Hx. unfold rd1 in Hx.
        replace (a + Z.of_nat (Datatypes.S j)) with (a + 1 + Z.of_nat j) by lia. exact Hx.
Qed.

#[using="Hsp Hfit Hva Hve"] Lemma stk_rd : forall (a : Z) n bs, usp <= a -> a + Z.of_nat n <= usp + Z.of_nat (length bsb) ->
  rdn ASEGS stk (Z_to_bv 64 a) n = Some bs ->
  forall j b, nth_error bs j = Some b -> m0 (Z_to_bv 64 (a + Z.of_nat j)) = Some b.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0).
  intros a n bs H1 H2 Hr j b Hj. pose proof (nth_error_Some bs j) as Hs. rewrite Hj in Hs.
  pose proof (rdn_length ASEGS stk n (Z_to_bv 64 a) bs Hr) as Hl.
  assert (Hjn : (j < n)%nat) by (rewrite <- Hl; apply Hs; discriminate).
  destruct usp_b as (U1 & _). pose proof bsb_b as Hbb. pose proof (rdn_rd1' stk a n bs ltac:(lia) ltac:(unfold two64; lia) Hr j b Hj) as Hrd.
  assert (Ux : bv_unsigned (Z_to_bv 64 (a + Z.of_nat j)) = a + Z.of_nat j) by (apply uZ; lia).
  destruct (m0_in (Z_to_bv 64 (a + Z.of_nat j)) ltac:(rewrite Ux; lia)) as (b' & Hm & Hst).
  unfold rd1 in Hrd. rewrite Hst in Hrd. injection Hrd as <-. exact Hm.
Qed.

(* [comment removed for export] *)
Ltac rels_ctx := pose proof rel_sp as (S1 & S2 & S3 & S4 & S4b & S5 & S6 & S7 & S8); pose proof rel_rp as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8);
  pose proof rel_top as (T1 & T2 & T3).
Ltac fl := rels_ctx; fu; lia.
#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma u_SP : bv_unsigned (lden E0 SP) = usp. Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0). fl. Qed.
#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma u_win : bv_unsigned (lden E0 (laddc SP (-8388608))) = usp - 8388608. Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0). fl. Qed.
#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma u_SP8 : bv_unsigned (lden E0 (laddc SP 8)) = usp + 8. Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0). fl. Qed.
#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma u_ASZ : bv_unsigned (lden E0 (laddc (lscale 8 ARGC) 8)) = 8 * AC + 8. Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0). fl. Qed.
#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma u_ENVP : bv_unsigned (lden E0 ENVP) = usp + 8 * AC + 16. Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0). fl. Qed.
#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma u_ESZ : bv_unsigned (lden E0 (laddc (lscale 8 ENVC) 8)) = 8 * EC + 8. Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0). fl. Qed.
#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma u_AUXV : bv_unsigned (lden E0 AUXV) = usp + 8 * AC + 8 * EC + 24. Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0). fl. Qed.
#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma u_P0 : bv_unsigned (lden E0 P0) = usp + 8 * AC + 8 * EC + 184. Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0). fl. Qed.
#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma u_RANDP : bv_unsigned (lden E0 RANDP) = RP. Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0). fl. Qed.
#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma u_STR : bv_unsigned (lden E0 (lsub RANDP P0)) = RP - (usp + 8 * AC + 8 * EC + 184). Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0). fl. Qed.
#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma u_PNL1 : bv_unsigned (lden E0 (laddc (ladd P0 LEN0) 1)) = usp + 8 * AC + 8 * EC + 184 + L0 + 1.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0).
  assert (HL0 : 0 <= L0 <= 131071) by (unfold L0; pose proof (valid_argv_str_len av 0 Hva ltac:(pose proof argc_b; lia)); lia). fl.
Qed.
#[using="Hbrk"] Lemma u_BRK : bv_unsigned (lden E0 BRK) = bv_unsigned brk0.
Proof. LiaFast.lf_pins (fun (Hbrk : LiaFast.U) => LiaFast.u0).
  pose proof brk_b as (B1 & B2). fu; [|unfold BP; pose proof (Z.div_mod (bv_unsigned brk0) 4096 ltac:(lia)); lia].
  unfold BP. pose proof (Z.div_mod (bv_unsigned brk0) 4096 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma uw : forall x, 0 <= x < 0x800000000000 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof. LiaFast.lf_pins LiaFast.u0. intros x H. apply uZ. lia. Qed.
#[using="Hsp Hfit Hva Hve"] Lemma blk_top : usp + Z.of_nat (length bsb) <= 0x800000000000.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0). destruct rel_top as ((P1 & P2) & _). destruct rel_rp as (_ & _ & _ & _ & _ & _ & _). unfold LB in *. lia. Qed.

#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma rg_win : rg_ok ASEGS E0 m0 (RGz (laddc SP (-8388608)) 8388608 RZ TEmpty).
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0).
  unfold rg_ok. rewrite rsz_RGz by (unfold two64; lia). cbn [RGz rg_base rg_kind rg_cont]. rewrite u_win.
  destruct usp_b as (U1 & _). split; [lia|]. split; [unfold two64; lia|]. split.
  - intros i Hi. rewrite tget_empty. pose proof (m0_win (Z_to_bv 64 (usp - 8388608 + i)) ltac:(rewrite uw by lia; lia)) as Hm.
    unfold rd1, wview. rewrite Hm. split; [split; discriminate | intros _; reflexivity].
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Hsp Hfit Hva Hve"] Lemma blk_rw : forall x, usp <= x < usp + Z.of_nat (length bsb) ->
  rd1 ASEGS m0 (Z_to_bv 64 x) <> None /\ wview ASEGS m0 (Z_to_bv 64 x) <> None.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0).
  intros x Hx. pose proof blk_top. destruct (m0_in (Z_to_bv 64 x) ltac:(rewrite uw by (destruct usp_b; lia); lia)) as (b & Hm & _).
  unfold rd1, wview. rewrite Hm. split; discriminate.
Qed.

#[using="Type"] Lemma len_word_AC : Z_to_bv 64 AC = len_word av. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma rg_argc : rg_ok ASEGS E0 m0 (RGz SP 8 RW (put_bytes TEmpty 0 (wb ARGC))).
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0).
  pose proof blk_top as Bt. pose proof rel_rp as (_ & _ & _ & R4 & R5 & R6 & R7 & R8). destruct usp_b as (U1 & _).
  unfold rg_ok. rewrite rsz_RGz by (unfold two64; lia). cbn [RGz rg_base rg_kind rg_cont]. rewrite u_SP.
  split; [lia|]. split; [unfold two64; lia|]. split.
  - intros i Hi. apply blk_rw. unfold LB, AC, EC in *. lia.
  - intros p v Hp. change (wb ARGC) with (flat_map wb [ARGC]) in Hp.
    destruct (rg_tracked_words ASEGS E0 m0 usp [ARGC] [len_word av] eq_refl) with (p := p) (v := v) as [Hl Hr]; [ | | exact Hp | ].
    + intros [|k] l w Hk Hw; [|destruct k; discriminate]. injection Hk as <-. injection Hw as <-.
      unfold ARGC. rewrite lden_lvar. reflexivity.
    + intros [|k] w i b Hw Hb; [|destruct k; discriminate]. injection Hw as <-.
      assert (Hrd : rdn ASEGS stk (Z_to_bv 64 usp) 8 = Some (word_le8 (len_word av))).
      { unfold usp. rewrite (Z_to_bv_bv_unsigned 64 sp). exact (read_argc APH ASEGS sp av ev uid hw draw ltac:(change (build_stack_bytes APH sp av ev uid hw draw) with bsb; unfold LB, usp in *; lia)). }
      pose proof (nth_error_Some (word_le8 (len_word av)) i) as Hs. rewrite Hb in Hs. rewrite length_n_to_le_8 in Hs.
      replace (usp + (8 * Z.of_nat 0 + Z.of_nat i)) with (usp + Z.of_nat i) by lia.
      unfold rd1. rewrite (stk_rd usp 8 _ ltac:(lia) ltac:(unfold LB in *; lia) Hrd i b Hb). reflexivity.
    + split; [cbn in Hl; lia | exact Hr].
Qed.

#[using="Type"] Lemma addr_nat : forall n : nat, (usp + Z.of_nat n <= 0x800000000000) -> (sp + nat_to_word n)%bv = Z_to_bv 64 (usp + Z.of_nat n).
Proof. LiaFast.lf_pins LiaFast.u0. intros n H. rewrite word_add_nat. reflexivity. Qed.

#[using="draw uid hw Hsp Hva Hve"] Lemma u_argv0 : bv_unsigned (cat_argv_ptr sp av ev 0) = usp + 8 * AC + 8 * EC + 184.
Proof. LiaFast.lf_pins (fun (draw uid hw Hsp Hva Hve : LiaFast.U) => LiaFast.u0).
  destruct Hsp as (H1 & H2 & _). rewrite (u_cat_argv_ptr APH sp draw av ev uid hw Hva Hve H1 H2 0 ltac:(pose proof argc_b; lia)).
  unfold cat_struct_size, auxv_size. change (total_arg_bytes_nat (firstn 0 av)) with 0%nat. unfold usp, AC, EC. lia.
Qed.

#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma rg_argv : rg_ok ASEGS E0 m0 (RG (laddc SP 8) (laddc (lscale 8 ARGC) 8) RW (put_bytes TEmpty 0 (wb P0 ++ wb P1))).
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0).
  pose proof blk_top as Bt. pose proof rel_rp as (_ & _ & _ & R4 & R5 & R6 & R7 & R8). destruct usp_b as (U1 & _).
  unfold rg_ok, rsz. cbn [rg_base rg_size rg_kind rg_cont]. rewrite u_SP8, u_ASZ.
  split; [lia|]. split; [unfold two64; lia|]. split.
  - intros i Hi. apply blk_rw. unfold LB, AC, EC in *. lia.
  - intros p v Hp. change (wb P0 ++ wb P1) with (flat_map wb [P0; P1]) in Hp.
    destruct (rg_tracked_words ASEGS E0 m0 (usp + 8) [P0; P1] [cat_argv_ptr sp av ev 0; E0 8%positive] eq_refl) with (p := p) (v := v) as [Hl Hr];
      [ | | exact Hp | ].
    + intros [|[|k]] l w Hk Hw; [ | | destruct k; discriminate]; injection Hk as <-; injection Hw as <-.
      * apply bv_eq. rewrite u_P0, u_argv0. reflexivity.
      * unfold P1. rewrite lden_lvar. reflexivity.
    + assert (Hb2 : usp + Z.of_nat (length (build_stack_bytes APH sp av ev uid hw draw)) < 2 ^ 64).
      { change (build_stack_bytes APH sp av ev uid hw draw) with bsb. unfold LB in *. lia. }
      intros [|[|k]] w i b Hw Hb; [ | | destruct k; discriminate]; injection Hw as <-.
      * pose proof (read_argv_ptr_k APH ASEGS sp av ev 0 uid hw draw ltac:(unfold AC in *; lia) Hb2) as Hrd.
        rewrite addr_nat in Hrd by (unfold LB in *; lia). cbn [Nat.mul Nat.add Z.of_nat] in Hrd.
        replace (usp + 8 + (8 * Z.of_nat 0 + Z.of_nat i)) with ((usp + 8) + Z.of_nat i) by lia.
        pose proof (nth_error_Some (word_le8 (cat_argv_ptr sp av ev 0)) i) as Hs. rewrite Hb, length_n_to_le_8 in Hs.
        unfold rd1. rewrite (stk_rd (usp + 8) 8 _ ltac:(lia) ltac:(unfold LB, AC, EC in *; lia) Hrd i b Hb). reflexivity.
      * replace (usp + 8 + (8 * Z.of_nat 1 + Z.of_nat i)) with ((usp + 16) + Z.of_nat i) by lia.
        pose proof (nth_error_Some (word_le8 (E0 8%positive)) i) as Hs. rewrite Hb, length_n_to_le_8 in Hs.
        assert (Hrd : rdn ASEGS stk (Z_to_bv 64 (usp + 16)) 8 = Some (word_le8 (E0 8%positive))).
        { change (E0 8%positive) with (if Nat.leb 2 (length av) then cat_argv_ptr sp av ev 1 else Z_to_bv 64 0).
          destruct (Nat.leb 2 (length av)) eqn:Hl2.
          - apply Nat.leb_le in Hl2. pose proof (read_argv_ptr_k APH ASEGS sp av ev 1 uid hw draw ltac:(lia) Hb2) as Hrd.
            rewrite addr_nat in Hrd by (unfold LB in *; lia). exact Hrd.
          - apply Nat.leb_gt in Hl2. destruct Hsp as (_ & H2 & _).
            pose proof (read_argv_null ASEGS APH sp draw av ev uid hw Hva Hve H2) as Hrd.
            assert (Hl1 : length av = 1%nat) by (pose proof argc_b; unfold AC in *; lia). rewrite Hl1 in Hrd.
            rewrite addr_nat in Hrd by (unfold LB in *; lia). exact Hrd. }
        unfold rd1. rewrite (stk_rd (usp + 16) 8 _ ltac:(lia) ltac:(unfold LB, AC, EC in *; lia) Hrd i b Hb). reflexivity.
    + split; [cbn in Hl; lia | exact Hr].
Qed.

Definition LSA : list lin := [lconst 3; lconst 0x10040; lconst 4; lconst 56; lconst 5; lconst 11; lconst 16; HW; lconst 6; lconst 4096;
  lconst 11; UID; lconst 12; UID; lconst 23; lconst 0; lconst 25; RANDP; lconst 0; lconst 0].
#[using="Type"] Lemma AUXC_eq : AUXC = flat_map wb LSA. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma map_LSA : List.map (lden E0) LSA = auxv_words APH (at_random_ptr sp av ev) uid hw.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0).
  assert (HR : lden E0 RANDP = at_random_ptr sp av ev) by (apply bv_eq; rewrite u_RANDP; reflexivity).
  assert (HH : lden E0 HW = hw) by (unfold HW; rewrite lden_lvar; reflexivity).
  assert (HU : lden E0 UID = uid) by (unfold UID; rewrite lden_lvar; reflexivity).
  unfold LSA. cbn [List.map]. rewrite HR, HH, HU, !lden_lconst. reflexivity.
Qed.

#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma rg_auxv : rg_ok ASEGS E0 m0 (RGz AUXV 160 RW (put_bytes TEmpty 0 AUXC)).
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0).
  pose proof blk_top as Bt. pose proof rel_rp as (_ & _ & _ & R4 & R5 & R6 & R7 & R8). destruct usp_b as (U1 & _).
  unfold rg_ok. rewrite rsz_RGz by (unfold two64; lia). cbn [RGz rg_base rg_kind rg_cont]. rewrite u_AUXV.
  split; [lia|]. split; [unfold two64; lia|]. split.
  - intros i Hi. apply blk_rw. unfold LB, AC, EC in *. lia.
  - intros p v Hp. rewrite AUXC_eq in Hp.
    destruct (rg_tracked_words ASEGS E0 m0 (usp + 8 * AC + 8 * EC + 24) LSA (auxv_words APH (at_random_ptr sp av ev) uid hw)
                (eq_refl : length LSA = length (auxv_words APH (at_random_ptr sp av ev) uid hw))) with (p := p) (v := v) as [Hl Hr];
      [ | | exact Hp | ].
    + intros k l w Hk Hw. rewrite <- map_LSA in Hw. rewrite nth_error_map, Hk in Hw. injection Hw as <-. reflexivity.
    + intros k w i b Hw Hb. destruct Hsp as (_ & H2 & _).
      assert (Hk : (k < 20)%nat) by (rewrite <- (length_auxv_words APH (at_random_ptr sp av ev) uid hw); apply nth_error_Some; rewrite Hw; discriminate).
      pose proof (read_auxv_word ASEGS APH sp draw av ev uid hw Hva Hve H2 k Hk) as Hrd.
      rewrite (nth_error_nth _ _ _ Hw) in Hrd. unfold auxv_off in Hrd.
      rewrite addr_nat in Hrd by (unfold LB, AC, EC in *; lia).
      replace (usp + Z.of_nat (8 + 8 * (length av + 1) + 8 * (length ev + 1) + 8 * k)) with ((usp + 8 * AC + 8 * EC + 24) + 8 * Z.of_nat k) in Hrd
        by (unfold AC, EC; lia).
      pose proof (nth_error_Some (word_le8 w) i) as Hs. rewrite Hb, length_n_to_le_8 in Hs.
      replace (usp + 8 * AC + 8 * EC + 24 + (8 * Z.of_nat k + Z.of_nat i)) with ((usp + 8 * AC + 8 * EC + 24 + 8 * Z.of_nat k) + Z.of_nat i) by lia.
      unfold rd1. rewrite (stk_rd (usp + 8 * AC + 8 * EC + 24 + 8 * Z.of_nat k) 8 _ ltac:(unfold AC, EC in *; lia) ltac:(unfold LB, AC, EC in *; lia) Hrd i b Hb). reflexivity.
    + split; [cbn in Hl; lia | exact Hr].
Qed.

#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma rg_rand : rg_ok ASEGS E0 m0 (RGz RANDP 16 RW (put_bytes TEmpty 0 (st_bytes (lvar 12) None 0 8 ++ st_bytes (lvar 13) None 0 8))).
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0).
  pose proof blk_top as Bt. pose proof rel_rp as (_ & _ & _ & R4 & R5 & R6 & R7 & R8). destruct usp_b as (U1 & U2).
  unfold rg_ok. rewrite rsz_RGz by (unfold two64; lia). cbn [RGz rg_base rg_kind rg_cont]. rewrite u_RANDP.
  split; [lia|]. split; [unfold two64; lia|]. split.
  - intros i Hi. apply blk_rw. unfold LB, AC, EC in *. lia.
  - intros p v Hp. change (st_bytes (lvar 12) None 0 8 ++ st_bytes (lvar 13) None 0 8) with (flat_map wb [lvar 12; lvar 13]) in Hp.
    destruct (rg_tracked_words ASEGS E0 m0 RP [lvar 12; lvar 13] [E0 12%positive; E0 13%positive] eq_refl) with (p := p) (v := v) as [Hl Hr];
      [ | | exact Hp | ].
    + intros [|[|k]] l w Hk Hw; [ | | destruct k; discriminate]; injection Hk as <-; injection Hw as <-; apply lden_lvar.
    + destruct Hsp as (H1 & H2 & H3).
      destruct (rnd_facts ASEGS APH sp draw av ev uid hw Hva Hve H1 H2 H3) as (_ & _ & _ & _ & Hrd).
      intros [|[|k]] w i b Hw Hb; [ | | destruct k; discriminate]; injection Hw as <-.
      * assert (X : rdn ASEGS stk (Z_to_bv 64 RP) 8 = Some (word_le8 (E0 12%positive))).
        { change (E0 12%positive) with (Z_to_bv 64 (bv_unsigned (ed_random draw) mod 2 ^ 64)). rewrite <- rnd_lo.
          pose proof (Hrd 0%nat 8%nat ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
        pose proof (nth_error_Some (word_le8 (E0 12%positive)) i) as Hs. rewrite Hb, length_n_to_le_8 in Hs.
        replace (RP + (8 * Z.of_nat 0 + Z.of_nat i)) with (RP + Z.of_nat i) by lia.
        unfold rd1. rewrite (stk_rd RP 8 _ ltac:(unfold LB in *; lia) ltac:(unfold LB in *; lia) X i b Hb). reflexivity.
      * assert (X : rdn ASEGS stk (Z_to_bv 64 (RP + Z.of_nat 8)) 8 = Some (word_le8 (E0 13%positive))).
        { change (E0 13%positive) with (Z_to_bv 64 (bv_unsigned (ed_random draw) / 2 ^ 64)). rewrite <- rnd_hi.
          exact (Hrd 8%nat 8%nat ltac:(lia)). }
        pose proof (nth_error_Some (word_le8 (E0 13%positive)) i) as Hs. rewrite Hb, length_n_to_le_8 in Hs.
        replace (RP + (8 * Z.of_nat 1 + Z.of_nat i)) with ((RP + Z.of_nat 8) + Z.of_nat i) by lia.
        unfold rd1. rewrite (stk_rd (RP + Z.of_nat 8) 8 _ ltac:(unfold LB in *; lia) ltac:(unfold LB in *; cbn; lia) X i b Hb). reflexivity.
    + split; [cbn in Hl; lia | exact Hr].
Qed.

#[using="Hsp Hfit Hva Hve olo ohi HC"] Theorem rgs0_disj : rgs_disj E0 RG0.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0).
  pose proof rel_rp as (_ & _ & _ & R4 & R5 & R6 & R7 & R8). destruct usp_b as (U1 & U2).
  unfold RG0. apply rgs_disj_app; [ | exact (cdisj_sound E0 _ img_cdisj) | ].
  - unfold RG_STK. cbn [rgs_disj].
    repeat match goal with |- _ /\ _ => split | |- Forall _ (_ :: _) => apply Forall_cons | |- Forall _ [] => apply Forall_nil | |- True => exact I end.
    all: unfold rg_disj, rsz; cbn [RGz rg_base rg_size]; rewrite ?u_win, ?u_SP, ?u_SP8, ?u_ASZ, ?u_AUXV, ?u_RANDP, ?lden_lconst, ?uw by lia;
      clear - R4 R5 R6 R7 R8 U1; lia.
  - intros R1 R2 HR1 HR2. pose proof img_low as Hl. rewrite forallb_forall in Hl. specialize (Hl R2 HR2).
    destruct (cbs R2) as [[a n]|] eqn:Hc; [|discriminate]. destruct (cbs_sound E0 R2 a n Hc) as [A2 S2].
    apply andb_prop in Hl as [Hl H3]. apply andb_prop in Hl as [H1 H2]. apply Z.leb_le in H1, H2.
    unfold rg_disj. rewrite A2, S2. right.
    unfold RG_STK in HR1. cbn [In] in HR1. unfold rsz.
    destruct HR1 as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [RGz rg_base rg_size]; rewrite ?u_win, ?u_SP, ?u_AUXV, ?u_RANDP, ?u_SP8; lia.
Qed.

#[using="Hsp Hfit Hva Hve olo ohi HC"] Theorem regs0_ok : regs_ok E0 (tset (rk 2) SP TEmpty) (ms_regs (init_machine_state ASEGS AsanUbsan.M.init_pc APH sp draw av ev uid hw)).
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0).
  intros r. unfold getr. destruct (bv_eqb r 0) eqn:Hr0.
  - apply bv_eqb_eq in Hr0. subst r. change (rkey (0%bv : reg)) with xH. reflexivity.
  - assert (Hk1 : rkey r <> xH) by (intros Hk; apply rkey_1 in Hk; subst r; discriminate).
    unfold reg_get, bvmap_get.
    change (ms_regs (init_machine_state ASEGS AsanUbsan.M.init_pc APH sp draw av ev uid hw)) with (tset 3 sp (tset 11 (Z_to_bv 64 0) TEmpty)).
    change (tset (rk 2) SP TEmpty) with (tset 3 SP TEmpty). change (bv_key r) with (rkey r).
    set (k := rkey r) in *. unfold rget.
    destruct (Pos.eqb k 3) eqn:E3.
    + apply Pos.eqb_eq in E3. rewrite E3. cbn [tget tset]. apply bv_eq. rewrite u_SP. reflexivity.
    + destruct (Pos.eqb k 11) eqn:E11.
      * apply Pos.eqb_eq in E11. rewrite E11. reflexivity.
      * apply Pos.eqb_neq in E3, E11. rewrite (tget_tset_other 3 k), (tget_tset_other 11 k), tget_empty by congruence.
        destruct k as [q|q|]; [| |congruence]; rewrite tget_tset_other by congruence; rewrite tget_empty; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hsp Hfit Hva Hve"] Lemma rdn_m0 : forall (a : Z) n, usp <= a -> a + Z.of_nat n <= usp + Z.of_nat (length bsb) ->
  rdn ASEGS m0 (Z_to_bv 64 a) n = rdn ASEGS stk (Z_to_bv 64 a) n.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0).
  intros a n H1 H2. pose proof blk_top as Bt. destruct usp_b as (U1 & _).
  apply (FxChStart.rdn_ext ASEGS m0 stk n a); [lia | unfold two64; lia|]. intros i Hi.
  destruct (m0_in (Z_to_bv 64 (a + i)) ltac:(rewrite uw by lia; lia)) as (b & Hm & Hs). rewrite Hm, Hs. reflexivity.
Qed.

#[using="bsb Hsp Hfit Hva Hve"] Lemma envp_words : forall i, (i < length ev)%nat ->
  exists bs, ov_read_bytes ASEGS m0 (Z_to_bv 64 (usp + 8 * AC + 16 + 8 * Z.of_nat i)) 8 = Some bs /\ ld_word SZ8 true bs <> Z_to_bv 64 0.
Proof. LiaFast.lf_pins (fun (bsb Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0).
  intros i Hi. pose proof blk_top as Bt. pose proof rel_rp as (_ & _ & _ & R4 & R5 & R6 & R7 & R8). destruct Hsp as (H1 & H2 & _).
  pose proof (read_envp_ptr_k ASEGS APH sp draw av ev uid hw Hva Hve H2 i Hi) as Hr. unfold envp_off in Hr.
  rewrite addr_nat in Hr by (unfold LB, AC, EC in *; lia).
  replace (usp + Z.of_nat (8 + 8 * (length av + 1) + 8 * i)) with (usp + 8 * AC + 16 + 8 * Z.of_nat i) in Hr by (unfold AC; lia).
  exists (word_le8 (cat_envp_ptr sp av ev i)). split.
  - rewrite ov_rdn, rdn_m0 by (unfold LB, AC, EC in *; lia). exact Hr.
  - rewrite ld_word_le8. intros He. apply (cat_envp_ptr_nz APH sp draw av ev uid hw Hva Hve H1 H2 i Hi). rewrite He. reflexivity.
Qed.

#[using="bsb Hsp Hfit Hva Hve"] Lemma envp_null : exists bs, ov_read_bytes ASEGS m0 (Z_to_bv 64 (usp + 8 * AC + 16 + 8 * EC)) 8 = Some bs /\ ld_word SZ8 true bs = Z_to_bv 64 0.
Proof. LiaFast.lf_pins (fun (bsb Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0).
  pose proof blk_top as Bt. pose proof rel_rp as (_ & _ & _ & R4 & R5 & R6 & R7 & R8). destruct Hsp as (H1 & H2 & _).
  pose proof (read_envp_null ASEGS APH sp draw av ev uid hw Hva Hve H2) as Hr. unfold envp_off in Hr.
  rewrite addr_nat in Hr by (unfold LB, AC, EC in *; lia).
  replace (usp + Z.of_nat (8 + 8 * (length av + 1) + 8 * length ev)) with (usp + 8 * AC + 16 + 8 * EC) in Hr by (unfold AC, EC; lia).
  exists (word_le8 (Z_to_bv 64 0)). split; [rewrite ov_rdn, rdn_m0 by (unfold LB, AC, EC in *; lia); exact Hr | apply ld_word_le8].
Qed.

#[using="Type"] Lemma rd1_m0_stk : forall x, usp <= bv_unsigned x -> rd1 ASEGS m0 x = rd1 ASEGS stk x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x Hx. unfold rd1. rewrite m0_eq. destruct (stk x) as [b|] eqn:Hs; [reflexivity|].
  replace (bv_unsigned x <? usp) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity.
Qed.

#[using="draw uid hw Hfit Hva"] Lemma argv0_top : usp + 8 * AC + 8 * EC + 184 + Z.of_nat (length (nth 0 av [])) + 1 <= 0x800000000000.
Proof. LiaFast.lf_pins (fun (draw uid hw Hfit Hva : LiaFast.U) => LiaFast.u0).
  pose proof Hfit as Hf. unfold entry_stack_fits, entry_stack_span, sp_window_hi, auxv_size in Hf.
  pose proof (total_arg_bytes_nonneg ev) as He.
  assert (Ha : Z.of_nat (length (nth 0 av [])) + 1 <= total_arg_bytes av).
  { destruct Hva as [[Hl _] _]. destruct av as [|a rest]; [cbn in Hl; lia|]. cbn [nth]. unfold total_arg_bytes. cbn [fold_right].
    pose proof (total_arg_bytes_nonneg rest) as Hr. unfold total_arg_bytes in Hr. lia. }
  unfold usp, AC, EC. lia.
Qed.

#[using="draw uid hw Hsp Hfit Hva Hve"] Lemma rp_str : usp + 8 * AC + 8 * EC + 184 + Z.of_nat (length (nth 0 av [])) + 1 <= RP.
Proof. LiaFast.lf_pins (fun (draw uid hw Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0).
  destruct usp_b as (U1 & _). pose proof argc_b as Ab. pose proof envc_b as Eb.
  destruct Hva as (_ & Hta & _). destruct Hve as (_ & Hte & _). rewrite total_arg_bytes_Z in Hta, Hte.
  assert (Ha : (length (nth 0 av []) + 1 <= total_arg_bytes_nat av)%nat).
  { destruct av as [|a rest]; [cbn in Ab; lia|]. cbn [nth total_arg_bytes_nat fold_right]. lia. }
  unfold RP, at_random_ptr. cbv zeta. rewrite word_add_nat. unfold nat_to_word.
  rewrite !length_flatten_strings. unfold auxv_size.
  set (len := (8 + (length av + 1) * 8 + (length ev + 1) * 8 + 160 + total_arg_bytes_nat av + total_arg_bytes_nat ev)%nat).
  set (pad := Z.to_nat ((8 - Z.of_nat len mod 8) mod 8)).
  assert (Hp8 : (pad < 8)%nat) by (unfold pad; pose proof (Z.mod_pos_bound (8 - Z.of_nat len mod 8) 8 ltac:(lia)); lia).
  rewrite uZ; [unfold len, AC, EC, usp in *; lia|]. unfold len, usp in *. lia.
Qed.

#[using="bsb Hsp Hfit Hva Hve"] Lemma argv0_byte : forall j, (j <= length (nth 0 av []))%nat ->
  rd1 ASEGS m0 (Z_to_bv 64 (usp + 8 * AC + 8 * EC + 184 + Z.of_nat j)) = Some (nth j (nth 0 av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (bsb Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0).
  intros j Hj. pose proof blk_top as Bt. pose proof rel_rp as (_ & _ & _ & R4 & R5 & R6 & R7 & R8). destruct usp_b as (U1 & _).
  assert (Hb2 : usp + Z.of_nat (length (build_stack_bytes APH sp av ev uid hw draw)) < 2 ^ 64).
  { change (build_stack_bytes APH sp av ev uid hw draw) with bsb. unfold LB in *. lia. }
  pose proof (read_argv_byte_k APH ASEGS sp av ev 0 j uid hw draw ltac:(pose proof argc_b; unfold AC in *; lia) Hj Hb2) as Hr.
  rewrite word_add_nat, u_argv0 in Hr.
  pose proof (valid_argv_str_len av 0 Hva ltac:(pose proof argc_b; unfold AC in *; lia)) as Hl0.
  pose proof argv0_top as Atop.
  rewrite rd1_m0_stk by (rewrite uw by (unfold AC, EC in *; lia); lia).
  pose proof (rdn_rd1' stk (usp + 8 * AC + 8 * EC + 184 + Z.of_nat j) 1 _ ltac:(lia) ltac:(unfold two64, AC, EC in *; lia) Hr O _ eq_refl) as X.
  rewrite Z.add_0_r in X. exact X.
Qed.

#[using="Hva"] Lemma argv0_nz : forall j, (j < length (nth 0 av []))%nat -> nth j (nth 0 av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) <> Z_to_bv 8 0.
Proof. LiaFast.lf_pins (fun (Hva : LiaFast.U) => LiaFast.u0).
  intros j Hj He. destruct Hva as (_ & _ & _ & Hnz & _). rewrite Forall_forall in Hnz.
  assert (Hin : In (nth 0 av []) av) by (apply nth_In; pose proof argc_b; unfold AC in *; lia).
  apply (Hnz _ Hin). rewrite app_nth1 in He by exact Hj. rewrite <- He. apply nth_In. exact Hj.
Qed.
#[using="Type"] Lemma argv0_nul : nth (length (nth 0 av [])) (nth 0 av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof. LiaFast.lf_pins LiaFast.u0. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

(* [comment removed for export] *)
Definition ms0 : machine_state := init_machine_state ASEGS AsanUbsan.M.init_pc APH sp draw av ev uid hw.
Definition model0 : Model := init_model (segments_reserved ASEGS) brk0 mb sp lim inp.

#[using="Type"] Lemma lazy0 : m_vm_lazy model0 = []. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma H0_false : forall x, Hof E0 M0 model0 x = false.
Proof. LiaFast.lf_pins LiaFast.u0. intros x. unfold Hof, mkH. rewrite lazy0. reflexivity. Qed.

#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma rgs0_ok : Forall (rg_ok ASEGS E0 m0) RG0.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0).
  unfold RG0. apply Forall_app. split.
  - unfold RG_STK. repeat apply Forall_cons; [exact rg_win | exact rg_argc | exact rg_argv | exact rg_auxv | exact rg_rand | apply Forall_nil].
  - apply img_rgs_ok. intros x Hx. apply m0_low. destruct usp_b. rewrite uw by lia. lia.
Qed.

#[using="Type"] Lemma state_wf0 : state_wf (S0c olo ohi xlo) = true. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Hsp Hbrk Hfit Hva Hve Hid HC Hxlo"] Theorem sden_entry : sden ASEGS E0 (S0c olo ohi xlo) (restrict (Hof E0 M0 model0) ms0).
Proof. LiaFast.lf_pins (fun (Hsp Hbrk Hfit Hva Hve Hid HC Hxlo : LiaFast.U) => LiaFast.u0).
  apply sden0_sden; [exact state_wf0|]. unfold sden0. cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr ms0 init_machine_state S0c s_pc s_regs s_rgs s_facts s_resv].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact regs0_ok|]. split.
  - rewrite Forall_forall. intros R HR. apply (rg_ok_frame ASEGS E0 m0); [pose proof rgs0_ok as Hg; rewrite Forall_forall in Hg; exact (Hg R HR)|].
    intros x _. unfold mrestrict. rewrite H0_false. reflexivity.
  - split; [exact rgs0_disj|]. split; [exact F0_ok|]. unfold frm_zero. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma rl_stk : forall R, In R RG_STK -> rl_ok E0 model0 R.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0).
  pose proof rel_rp as (_ & _ & _ & R4 & R5 & R6 & R7 & R8). destruct usp_b as (U1 & U2).
  assert (Hat : alloc_top (m_vmmaps model0) = usp - 8388608) by reflexivity. pose proof blk_top as Bt.
  intros R HR. unfold rl_ok, uE. cbv zeta.
  unfold RG_STK in HR. cbn [In] in HR. unfold rsz.
  destruct HR as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [RGz rg_base rg_size]; rewrite ?u_win, ?u_SP, ?u_AUXV, ?u_RANDP, ?u_SP8, ?u_ASZ, ?lden_lconst, ?uw by lia;
    (split; [unfold AC, EC, LB in *; lia|]); left; intros w Hw; unfold app_pt; pose proof (atop_pg_le (m_vmmaps model0)) as Hpg; rewrite Hat in Hpg;
    (split; [right; lia|]); (split; [unfold in_shadow, SH_LO, SH_HI; apply andb_false_iff; right; apply Z.ltb_ge; lia | unfold AC, EC, LB in *; lia]).
Qed.

#[using="Type"] Lemma rl_img : forall R, In R IMG_RGS -> rl_ok E0 model0 R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R HR. pose proof img_low as Hl. rewrite forallb_forall in Hl. specialize (Hl R HR).
  destruct (cbs R) as [[a n]|] eqn:Hc; [|discriminate]. destruct (cbs_sound E0 R a n Hc) as [A2 S2].
  apply andb_prop in Hl as [Hl H3]. apply andb_prop in Hl as [H1 H2]. apply Z.leb_le in H1, H2. apply Z.ltb_lt in H3.
  unfold rl_ok, uE. cbv zeta. rewrite A2, S2. split; [lia|]. left. intros w Hw. unfold app_pt.
  split; [left; change (vm_reserved (m_vmmaps model0) ++ vm_maps (m_vmmaps model0)) with (segments_reserved ASEGS ++ []); rewrite app_nil_r; apply covered_res; lia|].
  split; [unfold in_shadow, SH_LO, SH_HI; apply andb_false_iff; left; apply Z.leb_gt; lia | lia].
Qed.

#[using="Type"] Lemma img_out : forall w, 0x63c000 <= w < 0x800000000000 -> outside E0 IMG_RGS (Z_to_bv 64 w).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros w Hw. unfold outside. rewrite Forall_forall. intros R HR. pose proof img_low as Hl. rewrite forallb_forall in Hl. specialize (Hl R HR).
  destruct (cbs R) as [[a n]|] eqn:Hc; [|discriminate]. destruct (cbs_sound E0 R a n Hc) as [A2 S2].
  apply andb_prop in Hl as [Hl H3]. apply andb_prop in Hl as [H1 H2]. apply Z.leb_le in H2. rewrite A2, S2, uw by lia. right. lia.
Qed.

#[using="Hsp Hfit Hva Hve olo ohi HC"] Lemma frz0 : forall p, In p (sm_frz M0) -> forall w, uE E0 (fst p) <= w < uE E0 (fst p) + uE E0 (snd p) ->
  alloc_top (m_vmmaps model0) <= w < 0x800000000000 /\ outside E0 RG0 (Z_to_bv 64 w) /\ ms_mem ms0 (Z_to_bv 64 w) = m0 (Z_to_bv 64 w).
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0).
  pose proof rel_rp as (_ & _ & _ & R4 & R5 & R6 & R7 & R8). destruct usp_b as (U1 & U2). pose proof blk_top as Bt.
  assert (Hat : alloc_top (m_vmmaps model0) = usp - 8388608) by reflexivity.
  intros p Hp w Hw. rewrite Hat. cbn [sm_frz M0 In] in Hp.
  destruct Hp as [<-|[<-|[]]]; cbn [fst snd] in Hw; unfold uE in Hw; rewrite ?u_ENVP, ?u_ESZ, ?u_P0, ?u_STR in Hw;
    (split; [unfold AC, EC, LB in *; lia|]); (split; [|reflexivity]);
    unfold RG0, outside; apply Forall_app; (split; [|apply img_out; unfold AC, EC, LB in *; lia]);
    unfold RG_STK; repeat apply Forall_cons; try apply Forall_nil; unfold rsz; cbn [RGz rg_base rg_size];
    rewrite ?u_win, ?u_SP, ?u_AUXV, ?u_RANDP, ?u_SP8, ?u_ASZ, ?lden_lconst, ?uw by (unfold AC, EC, LB in *; lia); unfold AC, EC, LB in *; lia.
Qed.

(* [comment removed for export] *)
#[using="Hsp Hbrk Hfit Hva Hve Hid HC Hxlo Hlim"] Theorem den_entry : DEN ASEGS lim model0 m0 E0 (S0c olo ohi xlo) M0 ms0 model0.
Proof. LiaFast.lf_pins (fun (Hsp Hbrk Hfit Hva Hve Hid HC Hxlo Hlim : LiaFast.U) => LiaFast.u0).
  constructor.
  - exact sden_entry.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - apply Forall_nil.
  - constructor; cbn; try (intros p Hp; destruct Hp); [constructor | ]. change (allowA E0 M0) with (@nil (Z * Z)). cbn. exact Hlim.
  - intros a Ha. rewrite H0_false in Ha. discriminate.
  - reflexivity.
  - reflexivity.
  - change (sm_sp M0) with SP. apply bv_eq. rewrite u_SP. reflexivity.
  - split; [exact (init_sp_ok_init_model _ brk0 mb sp lim inp Hsp) | destruct Hsp as (_ & H2 & _); exact H2].
  - change (sm_brk M0) with BRK. apply bv_eq. rewrite u_BRK. reflexivity.
  - change (sm_sbrk M0) with BRK. apply bv_eq. rewrite u_BRK. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - apply Forall_nil.
  - split; apply ivs_wf_nil.
  - exact I.
  - intros x Hx. discriminate.
  - apply Forall_nil.
  - intros x Hx. rewrite lazy0 in Hx. discriminate.
  - intros w Hw. discriminate.
  - intros w Hw. discriminate.
  - intros w Hw. discriminate.
  - unfold RG0. apply Forall_app. split; rewrite Forall_forall; [exact rl_stk | exact rl_img].
  - repeat split.
  - reflexivity.
  - exact frz0.
  - rom_tac.
  - apply own_nil. reflexivity.
  - change (blob_of model0) with (@nil (word * word)). apply blob_ok_nil. reflexivity.   (* [comment removed for export] *)
Qed.

End Entry.
(* [comment removed for export] *)
