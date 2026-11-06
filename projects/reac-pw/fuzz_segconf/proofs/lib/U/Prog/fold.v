(** fold (UBSan build, 0x151a4, 148 bytes, a leaf): proof of [fold_contract] (U/Prog/fold_c.v). Written new.
    The plain build has no fold function (clang inlines it into m_file) and the contract family
    states no plain contract, so there is no plain walk.

    Code (image 1696d6c34ffd, unstripped twin afc060e3cc9c):
      0x151a4 addi a3,a3,-1; 0x151a8 bltu a1,a3 -> 0x151b0; 0x151ac mv a1,a3   (k = min(n, cap - 1))
      0x151b0 beqz a1 -> KZERO
      0x151b4-0x151cc a4 = 0; a3 = ~out; a5 = (s <> 0); a6 = a7 = s; t0 = out; t1 = k
      LOOP 0x151d0 bltu a6,a0 -> TRAP; seqz/xor/beqz (s + i = 0) -> TRAP; 0x151e0 beqz a0 -> TRAP;
           0x151e4 bltu a3,a4 -> TRAP; 0x151e8 lbu t2,0(a7); a4++; t1--; a7++;
           t2 += 32 (t2 - 'A' <u 26) (0x151f8-0x15204); 0x15208 sb t2,0(t0); t0++; a6++; 0x15214 bnez t1 -> LOOP
      0x15218 bltu a3,a1 -> TRAP
      TAIL 0x1521c add a2,a2,a1; 0x15220 sb zero,0(a2); 0x15224 mv a0,a1; ret
      KZERO 0x1522c not a3,a2; 0x15230 bgeu a3,a1 -> TAIL.  TRAP 0x15234 unimp
    The traps are not reached: s <> 0 and s + n <= 2^64 (bytes_at), out + k + 1 <= 2^64 (wr_at), i < k <= n.
    The byte the loop stores is SegModel.lower of the byte it loads ([fo_byte]); the loop invariant [fo_mem] holds
    the folded prefix at out, so after the NUL out holds zb (fold_out l cap ++ [0]). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import fold_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Lists *)
Lemma fo_firstn1 : forall {A} (x : list A) i d, (i < length x)%nat -> firstn 1 (skipn i x) = [nth i x d].
Proof.
  intros A x. induction x as [|a x IH]; intros i d H.
  - cbn in H. lia.
  - destruct i as [|i].
    + reflexivity.
    + cbn [skipn nth]. apply IH. cbn in H. lia.
Qed.

Lemma fo_firstn_S : forall {A} (x : list A) i d, (i < length x)%nat -> firstn (S i) x = firstn i x ++ [nth i x d].
Proof.
  intros A x. induction x as [|a x IH]; intros i d H.
  - cbn in H. lia.
  - destruct i as [|i].
    + reflexivity.
    + cbn in H. change (firstn (S (S i)) (a :: x)) with (a :: firstn (S i) x).
      change (firstn (S i) (a :: x)) with (a :: firstn i x). change (nth (S i) (a :: x) d) with (nth i x d).
      rewrite (IH i d) by lia. reflexivity.
Qed.

Lemma fo_nth_firstn : forall {A} (x : list A) k i d, (i < k)%nat -> nth i (firstn k x) d = nth i x d.
Proof.
  intros A x. induction x as [|a x IH]; intros k i d H.
  - destruct k; reflexivity.
  - destruct k as [|k]; [lia|]. destruct i as [|i]; [reflexivity|].
    cbn [firstn nth]. apply IH. lia.
Qed.

Lemma fo_map_nth : forall {A B} (f : A -> B) (x : list A) i d d', (i < length x)%nat ->
  nth i (map f x) d' = f (nth i x d).
Proof.
  intros A B f x. induction x as [|a x IH]; intros i d d' H.
  - cbn in H. lia.
  - destruct i as [|i]; [reflexivity|]. cbn [map nth]. apply IH. cbn in H. lia.
Qed.

Lemma fo_zb0 : forall x, zb (x ++ [0]) = zb x ++ [ZERO].
Proof. intros x. unfold zb. rewrite map_app. reflexivity. Qed.

(** ** The byte the loop stores *)
Lemma fo_le1 : forall z, 0 <= z < 2^64 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z Hz. rewrite <- (le1_zxb (Z_to_bv 8 z)). unfold le1, zxb.
  pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 z)) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R.
  rewrite (unsigned_lit z) by lia. rewrite (unsigned_lit (bv_unsigned (Z_to_bv 8 z))) by lia.
  rewrite Z_to_bv_unsigned. change (bv_wrap 8 z) with (z mod 2^8).
  symmetry. apply Z_to_le_bytes_mod. cbn. lia.
Qed.

(** `addi t3,t2,-0x41; sltiu t3,t3,0x1a; slli t3,t3,5; add t2,t2,t3; sb t2`, as the steps leave it: lower. *)
Lemma fo_byte : forall b : byte,
  le1 (Z_to_bv 64 (bv_unsigned (zxb b) +
                   Z.shiftl (bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b) + -65)) 26)) 5))
  = [Z_to_bv 8 (lower (bv_unsigned b))].
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R.
  unfold zxb, v_sltiu. rewrite (unsigned_lit (bv_unsigned b)) by lia.
  rewrite unsigned_lit_wrap. replace (bv_wrap 64 26) with 26 by reflexivity.
  lazymatch goal with |- context [if ?c then _ else _] => destruct c eqn:E end; cbv iota.
  - rewrite (unsigned_lit 1) by lia. change (Z.shiftl 1 5) with 32.
    rewrite fo_le1 by lia. apply (f_equal (fun z => [Z_to_bv 8 z])).
    apply Z.ltb_lt in E. unfold lower.
    destruct (Z.leb_spec 65 (bv_unsigned b)); destruct (Z.leb_spec (bv_unsigned b) 90); cbn [andb];
      Z.div_mod_to_equations; lia.
  - rewrite (unsigned_lit 0) by lia. change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r.
    rewrite fo_le1 by lia. apply (f_equal (fun z => [Z_to_bv 8 z])).
    apply Z.ltb_ge in E. unfold lower.
    destruct (Z.leb_spec 65 (bv_unsigned b)); destruct (Z.leb_spec (bv_unsigned b) 90); cbn [andb];
      Z.div_mod_to_equations; lia.
Qed.

(** `snez a5,a0` with a0 = s <> 0. *)
Lemma fo_snez : forall s, 0 < s < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 s) = Z_to_bv 64 1.
Proof.
  intros s Hs. rewrite v_sltu_b2z. rewrite (unsigned_lit 0), (unsigned_lit s) by lia.
  replace (0 <? s) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(** A register equation at the loop entry: the literals, ~out and snez. *)
Ltac fo_weq := rewrite ?fo_snez by lia; rewrite ?unsigned_lit by lia; rewrite ?zb_lxor_ones by lia;
  first [reflexivity | f_equal; lia].

(** The trap `seqz t2,a6; xor t2,a5,t2; beqz t2` with a5 = 1 and a6 = s + i >= 1. *)
Ltac fo_k2 H := exfalso; zify_cond H;
  lazymatch type of H with context [Z.ltb ?x 1] => rewrite (proj2 (Z.ltb_ge x 1)) in H by lia end;
  cbn in H; first [discriminate H | lia].

Section Fold.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (lo sx ox cp : Z) (l : list byte).

Local Abbreviation FO := (fold_out l cp).
Local Abbreviation KK := (Z.of_nat (length (fold_out l cp))).
Local Abbreviation NN := (Z.of_nat (length l)).

Hypothesis HS0 : 0 < sx.
Hypothesis HSx : sx < 2^64.
Hypothesis HB : bytes_at rsegs m0 sx l.
Hypothesis HC1 : 1 <= cp.
Hypothesis HC64 : cp < 2^64.
Hypothesis HW0 : wr_at rsegs m0 ox (KK + 1).
Hypothesis HSO : sx + NN <= ox \/ ox + KK + 1 <= sx.
Hypothesis HST : stk rsegs m0 lo (bv_unsigned sp).
Hypothesis HMI : mem_inv rsegs m0.

Local Abbreviation Post :=
  (ret_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc KK m0 [(ox, ox + KK + 1)] lo
     (fun m' => bytes_at rsegs m' ox (zb (FO ++ [0])))).

Local Abbreviation FoSt pc mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
  (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Lemma fo_Kmin : KK = Z.min NN (cp - 1).
Proof. unfold fold_out, h_fold, zs. rewrite length_map, length_firstn, length_map. lia. Qed.

Lemma fo_bounds : 0 <= sx /\ sx + NN <= 2^64 /\ 0 <= ox /\ ox + KK + 1 <= 2^64 /\ KK = Z.min NN (cp - 1).
Proof.
  pose proof (bytes_at_bound _ _ _ _ HB) as B. pose proof HW0 as (W1 & W2 & _). pose proof fo_Kmin. lia.
Qed.

(** Byte i of the folded text is lower of byte i of the input. *)
Lemma fo_nth : forall i, (i < length FO)%nat -> nth i FO 0 = lower (bv_unsigned (nth i l ZERO)).
Proof.
  intros i Hi. pose proof fo_bounds as BD.
  assert (H1 : (i < Z.to_nat cp - 1)%nat) by lia.
  assert (H2 : (i < length l)%nat) by lia.
  unfold fold_out, h_fold, zs.
  rewrite (fo_map_nth lower _ i 0 0) by (rewrite length_firstn, length_map; lia).
  rewrite fo_nth_firstn by exact H1.
  rewrite (fo_map_nth bv_unsigned l i ZERO 0) by exact H2.
  reflexivity.
Qed.

Lemma fo_snoc : forall i, (i < length FO)%nat ->
  zb (firstn (S i) FO) = zb (firstn i FO) ++ [Z_to_bv 8 (lower (bv_unsigned (nth i l ZERO)))].
Proof.
  intros i Hi. rewrite (fo_firstn_S FO i 0 Hi). unfold zb. rewrite map_app. cbn [map].
  rewrite (fo_nth i Hi). reflexivity.
Qed.

(** The memory between the steps: the input, the folded prefix pre at out, out's bytes writable, the footprint
    [out, out + k + 1), the writable view, mem_inv and the stack region. *)
Definition fo_mem (m : word -> option byte) (pre : list byte) : Prop :=
  bytes_at rsegs m sx l /\ bytes_at rsegs m ox pre /\ wr_at rsegs m ox (KK + 1) /\
  munch [(ox, ox + KK + 1)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\ stk rsegs m lo (bv_unsigned sp).

Lemma fo_mem0 : fo_mem m0 [].
Proof.
  pose proof fo_bounds as BD. unfold fo_mem.
  split; [exact HB|]. split; [apply bytes_at_nil; lia|]. split; [exact HW0|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact HMI | exact HST].
Qed.

Lemma fo_mem_load : forall m pre i, fo_mem m pre -> (i < length l)%nat ->
  ov_read_bytes rsegs m (wa (sx + Z.of_nat i)) 1 = Some [nth i l ZERO].
Proof.
  intros m pre i (HBm & _) Hi.
  rewrite (bytes_at_read rsegs m sx l (Z.of_nat i) 1 HBm) by lia.
  rewrite Nat2Z.id. f_equal. apply fo_firstn1. exact Hi.
Qed.

Lemma fo_mem_store_ok : forall m pre a, fo_mem m pre -> a = ox + Z.of_nat (length pre) ->
  Z.of_nat (length pre) <= KK -> store_ok rsegs m (wa a) 1 = true.
Proof.
  intros m pre a (_ & _ & HWm & _) -> HL.
  apply (wr_at_store_ok rsegs m ox (KK + 1) (Z.of_nat (length pre)) 1 HWm); lia.
Qed.

Lemma fo_mem_store : forall m pre a b, fo_mem m pre -> a = ox + Z.of_nat (length pre) ->
  Z.of_nat (length pre) <= KK -> fo_mem (write_to_mem m (Z_to_bv 64 a) [b]) (pre ++ [b]).
Proof.
  intros m pre a b (HBm & HPm & HWm & MUm & WMm & MIm & STm) Ea HL.
  pose proof fo_bounds as BD.
  change (Z_to_bv 64 a) with (wa a).
  unfold fo_mem.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - apply bytes_at_write_other; [exact HBm | lia | cbn [length]; lia | cbn [length]; lia].
  - apply bytes_at_app. split.
    + apply bytes_at_write_other; [exact HPm | lia | cbn [length]; lia | cbn [length]; lia].
    + rewrite <- Ea. apply bytes_at_write_same; [lia | cbn [length]; lia].
  - apply wr_at_write. exact HWm.
  - apply munch_write; [exact MUm | lia | cbn [length]; lia | cbn [inside length]; left; lia].
  - apply wmono_write. exact WMm.
  - apply mem_inv_store; [exact MIm|]. cbn [length]. subst a.
    apply (wr_at_store_ok rsegs m ox (KK + 1) (Z.of_nat (length pre)) 1 HWm); lia.
  - apply stk_write; [exact STm | lia | cbn [length]; lia].
Qed.

(** TAIL 0x1521c: `add a2,a2,a1; sb zero,0(a2); mv a0,a1; ret` with a1 = k and the whole folded text at out. *)
Lemma fo_tail : forall m (x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  x11 = Z_to_bv 64 KK -> fo_mem m (zb FO) ->
  evt rsegs Post (FoSt 0x1521c m x5 x6 x7 x10 x11 (Z_to_bv 64 ox) x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  intros m x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 E11 HM. subst x11.
  pose proof fo_bounds as BD.
  assert (HL : length (zb FO) = length FO) by (unfold zb; apply length_map).
  pose proof (fo_mem_store_ok m (zb FO) (ox + KK) HM ltac:(rewrite HL; reflexivity) ltac:(rewrite HL; lia))
    as HS.
  step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
    replace bs with [ZERO] by (first [reflexivity | vm_compute; reflexivity]) end.
  pose proof (fo_mem_store m (zb FO) (ox + KK) ZERO HM ltac:(rewrite HL; reflexivity) ltac:(rewrite HL; lia))
    as HM'.
  step. step.
  destruct HM' as (_ & HP' & _ & MU' & WM' & MI' & ST').
  apply evt_done. unfold ret_post.
  do 15 eexists. split; [reflexivity|].
  split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|].
  cbv beta. rewrite fo_zb0. exact HP'.
Qed.

(** KZERO 0x1522c (k = 0): `not a3,a2; bgeu a3,a1` is taken (~out >= k), to TAIL. *)
Lemma fo_kzero : forall m (x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  x11 = Z_to_bv 64 KK -> fo_mem m (zb FO) ->
  evt rsegs Post (FoSt 0x1522c m x5 x6 x7 x10 x11 (Z_to_bv 64 ox) x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  intros m x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 E11 HM. subst x11.
  pose proof fo_bounds as BD.
  step. step. if_cases K1; cbv iota.
  - eapply fo_tail; [reflexivity | exact HM].
  - exfalso. zify_cond K1. rewrite zb_lxor_ones in K1 by lia. lia.
Qed.

(** 0x15218, after the loop: the check `bltu ~out,k` is not taken, then TAIL. *)
Lemma fo_fin : forall m (x5 x6 x7 x10 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  fo_mem m (zb FO) ->
  evt rsegs Post (FoSt 0x15218 m x5 x6 x7 x10 (Z_to_bv 64 KK) (Z_to_bv 64 ox) (Z_to_bv 64 (18446744073709551615 - ox))
                    x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  intros m x5 x6 x7 x10 x14 x15 x16 x17 x28 x29 x30 x31 HM. pose proof fo_bounds as BD.
  step. if_cases K1; cbv iota; [exfalso; zify_cond K1; Z.div_mod_to_equations; lia|].
  eapply fo_tail; [reflexivity | exact HM].
Qed.

(** LOOP 0x151d0 with i bytes folded and j = k - i left: t0 = out + i, t1 = k - i, a1 = k, a3 = ~out, a4 = i,
    a5 = 1, a6 = a7 = s + i; the first i folded bytes at out. *)
Lemma fo_loop : forall j i m (x5 x6 x7 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  (i + j = length FO)%nat -> (0 < j)%nat ->
  x5 = Z_to_bv 64 (ox + Z.of_nat i) -> x6 = Z_to_bv 64 (KK - Z.of_nat i) -> x11 = Z_to_bv 64 KK ->
  x13 = Z_to_bv 64 (18446744073709551615 - ox) -> x14 = Z_to_bv 64 (Z.of_nat i) -> x15 = Z_to_bv 64 1 ->
  x16 = Z_to_bv 64 (sx + Z.of_nat i) -> x17 = Z_to_bv 64 (sx + Z.of_nat i) ->
  fo_mem m (zb (firstn i FO)) ->
  evt rsegs Post (FoSt 0x151d0 m x5 x6 x7 (Z_to_bv 64 sx) x11 (Z_to_bv 64 ox) x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  induction j as [|j IH];
    intros i m x5 x6 x7 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hij Hj E5 E6 E11 E13 E14 E15 E16 E17 HM; [lia|].
  subst x5 x6 x11 x13 x14 x15 x16 x17.
  pose proof fo_bounds as BD.
  assert (Hi : (i < length FO)%nat) by lia.
  assert (HiL : (i < length l)%nat) by lia.
  assert (HLp : length (zb (firstn i FO)) = i) by (unfold zb; rewrite length_map, length_firstn; lia).
  pose proof (fo_mem_load m _ i HM HiL) as HR.
  pose proof (fo_mem_store_ok m _ (ox + Z.of_nat i) HM ltac:(rewrite HLp; reflexivity) ltac:(rewrite HLp; lia))
    as HW.
  step. if_cases K1; cbv iota; [exfalso; zify_cond K1; Z.div_mod_to_equations; lia|].
  step. step. step. if_cases K2; cbv iota; [fo_k2 K2|].
  step. if_cases K3; cbv iota; [exfalso; zify_cond K3; Z.div_mod_to_equations; lia|].
  step. if_cases K4; cbv iota; [exfalso; zify_cond K4; Z.div_mod_to_equations; lia|].
  step. step. step. step. step. step. step. step.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
    replace bs with [Z_to_bv 8 (lower (bv_unsigned (nth i l ZERO)))]
      by (first [apply fo_byte | symmetry; apply fo_byte]) end.
  pose proof (fo_mem_store m _ (ox + Z.of_nat i) (Z_to_bv 8 (lower (bv_unsigned (nth i l ZERO)))) HM
                ltac:(rewrite HLp; reflexivity) ltac:(rewrite HLp; lia)) as HM'.
  rewrite <- (fo_snoc i Hi) in HM'.
  clear HR HW.
  step. step. step.
  if_cases K5; cbv iota.
  - zify_cond K5.
    eapply (IH (S i)); first [exact HM' | lia | fo_weq].
  - zify_cond K5.
    replace (S i) with (length FO) in HM' by lia. rewrite firstn_all in HM'.
    eapply fo_fin. exact HM'.
Qed.

(** The whole function from its entry. *)
Lemma fo_body : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sx) (Z_to_bv 64 NN) (Z_to_bv 64 ox) (Z_to_bv 64 cp)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x151a4) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6. pose proof fo_bounds as BD. pose proof fo_mem0 as M0.
  step. step. if_cases K1; cbv iota.
  - (* n <u cap - 1: k = n *)
    zify_cond K1.
    step. if_cases K2; cbv iota.
    + zify_cond K2. eapply fo_kzero; [fo_weq|].
      replace FO with (@nil Z)
        by (first [symmetry; apply length_zero_iff_nil; lia | apply length_zero_iff_nil; lia]).
      exact M0.
    + zify_cond K2. do 7 step.
      eapply (fo_loop (length FO) 0%nat); first [exact M0 | lia | fo_weq].
  - (* k = cap - 1 *)
    zify_cond K1.
    step. step. if_cases K2; cbv iota.
    + zify_cond K2. eapply fo_kzero; [fo_weq|].
      replace FO with (@nil Z)
        by (first [symmetry; apply length_zero_iff_nil; lia | apply length_zero_iff_nil; lia]).
      exact M0.
    + zify_cond K2. do 7 step.
      eapply (fo_loop (length FO) 0%nat); first [exact M0 | lia | fo_weq].
Qed.

End Fold.

Theorem fold_holds : fold_contract.
Proof.
  unfold fold_contract, fold_pre, FOLD_STACK, FOLD, stack_ok, apart.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo l
    (HC1 & HS0 & HB & HN & _ & HW & _ & HSO & (HST & _ & _ & _) & MI).
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. pose proof (bv_unsigned_in_range 64 a3) as Ra3.
  change (bv_modulus 64) with (2^64) in Ra0, Ra3.
  rewrite <- HN in HSO.
  pose proof (Z_to_bv_bv_unsigned a1) as Ea1. rewrite <- HN in Ea1. rewrite <- Ea1. clear Ea1.
  pose proof (Z_to_bv_bv_unsigned a0) as Ea0. pose proof (Z_to_bv_bv_unsigned a2) as Ea2.
  pose proof (Z_to_bv_bv_unsigned a3) as Ea3.
  set (sx := bv_unsigned a0) in *. set (ox := bv_unsigned a2) in *. set (cp := bv_unsigned a3) in *.
  rewrite <- Ea0, <- Ea2, <- Ea3. clearbody sx ox cp. clear Ea0 Ea2 Ea3.
  eapply fo_body; first [eassumption | lia].
Qed.
