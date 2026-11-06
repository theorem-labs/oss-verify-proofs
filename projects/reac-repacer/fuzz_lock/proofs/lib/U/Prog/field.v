(* Walk of reac-repacer's static [field] (src/repace_conf.c:87-99 at 3ac1cf10) in fuzz_lock.ubsan, 0x13490.
   The walk of lib/Prog/field.v, with the UBSan checks; the trap [unimp] at 0x1353c is reached from four branches
   and none is taken:
   - 0x13494 [bnez a3], a3 = p & 7: pp mod 8 = 0 (al8);
   - 0x134b0 [beqz a3], a3 = s + i, i < len: 0 < s and s + len < 2^64;
   - 0x134f8 [beqz a4], a4 = s + o + j, o + j < len: the same;
   - 0x13524 [bnez a1], a1 = at & 7: ap mod 8 = 0 (al8).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import StrFun LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import field_c.
Import ListNotations.
Open Scope Z_scope.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

Lemma firstn1_skipn : forall {X} (l : list X) i b, nth_error l i = Some b -> firstn 1 (skipn i l) = [b].
Proof.
  intros X l; induction l as [|c l IH]; intros [|i] b N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - apply IH; exact N.
Qed.

Lemma rdb : forall m A l (i : nat) b, bytes_at rsegs m A l -> nth_error l i = Some b ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat i)) 1 = Some [b].
Proof.
  intros m A l i b BL N. pose proof (nth_error_Some l i) as NS. rewrite N in NS.
  assert (Hi : (i < length l)%nat) by (apply NS; discriminate).
  rewrite (bytes_at_ov_read rsegs m A l i 1 BL ltac:(lia)). f_equal. apply firstn1_skipn. exact N.
Qed.

Lemma skipn_nth : forall {X} (l : list X) i b, nth_error l i = Some b -> skipn i l = b :: skipn (S i) l.
Proof.
  intros X l; induction l as [|c l IH]; intros [|i] b N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - apply IH; exact N.
Qed.

(* the separator test the compiler emits: c > 32 is no separator, else bit c of 0x100002200 *)
Definition sep_mach (c : Z) : bool :=
  if bv_ltu (Z_to_bv 64 32) (Z_to_bv 64 c) then false
  else negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294976000 (bv_unsigned (Z_to_bv 64 c) mod 64)))) 1))
                    (Z_to_bv 64 0)).

Lemma sep_mach_ok : forall c, 0 <= c < 256 -> sep_mach c = is_sep c.
Proof.
  intros c Hc.
  pose proof (brute256_ok (fun c => Bool.eqb (sep_mach c) (is_sep c)) ltac:(vm_compute; reflexivity) c Hc) as H.
  apply Bool.eqb_prop in H. exact H.
Qed.

Lemma sep_hi : forall b : byte, bv_ltu (Z_to_bv 64 32) (Z_to_bv 64 (bv_unsigned b)) = true -> is_sep (bz b) = false.
Proof.
  intros b H. pose proof (byte_range b) as R. rewrite <- (sep_mach_ok (bz b) R). unfold sep_mach, bz. rewrite H. reflexivity.
Qed.

Lemma sep_lo : forall b : byte, bv_ltu (Z_to_bv 64 32) (Z_to_bv 64 (bv_unsigned b)) = false ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294976000 (bv_unsigned (Z_to_bv 64 (bv_unsigned b)) mod 64)))) 1))
         (Z_to_bv 64 0) = negb (is_sep (bz b)).
Proof.
  intros b H. pose proof (byte_range b) as R. rewrite <- (sep_mach_ok (bz b) R). unfold sep_mach, bz. rewrite H.
  rewrite Bool.negb_involutive. reflexivity.
Qed.

(* UBSan alignment check [andi r,x,7; bnez r -> trap] on an 8-byte aligned x *)
Lemma al8 : forall z, 0 <= z < 2^64 -> z mod 8 = 0 ->
  negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 z)) 7)) (Z_to_bv 64 0)) = false.
Proof.
  intros z Hz H8. rewrite (unsigned_lit z) by lia.
  pose proof (Z.land_ones z 3 ltac:(lia)) as LO. change (Z.ones 3) with 7 in LO. change (2 ^ 3) with 8 in LO.
  rewrite LO, H8. vm_compute. reflexivity.
Qed.

Section F.
Variables (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (pp ap s : Z) (l J : list byte).
Hypothesis Hs : 0 < s.
Hypothesis He : s + Z.of_nat (length l) < 2^64.
Hypothesis BL : bytes_at rsegs m s l.
Hypothesis CP : rw_cells rsegs m pp [C8 (Z_to_bv 64 s)].
Hypothesis CA : rw_cells rsegs m ap [CB 8 J].
Hypothesis DPA : pp + 8 <= ap \/ ap + 8 <= pp.
Hypothesis P8 : pp mod 8 = 0.
Hypothesis A8 : ap mod 8 = 0.
Hypothesis MI : mem_inv rsegs m.

Local Notation ST pc t0 a1 a3 a4 a5 a6 a7 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pp) a1 (Z_to_bv 64 ap) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Local Notation E := (s + Z.of_nat (length l)).
Local Notation Q := (field_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m pp ap s l).

Lemma byte_at : forall i, (i < length l)%nat -> exists b, nth_error l i = Some b.
Proof. intros i Hi. destruct (nth_error l i) eqn:N; [eexists; reflexivity|]. apply nth_error_None in N. lia. Qed.

(* 0x13520: andi a1,a2,7; bnez a1 (trap); sd a3,0(a2); sub a1,a4,a3; sd a4,0(a0); mv a0,a1; ret *)
Lemma fin : forall (t0 a1 a5 a6 a7 : word) (v3 v4 : Z),
  v3 = s + Z.of_nat (fld_s l) -> v4 = s + Z.of_nat (fld_s l + fld_n l) -> v4 < 2^64 ->
  evt rsegs Q (ST 0x13520 t0 a1 (Z_to_bv 64 v3) (Z_to_bv 64 v4) a5 a6 a7).
Proof.
  intros t0 a1 a5 a6 a7 v3 v4 -> -> Hb.
  pose proof (cells_at_bound rsegs m ap _ (proj1 CA)) as BA. cbn [cells_size csize] in BA.
  pose proof (munch_refl [(pp, pp + 8); (ap, ap + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof MI as MI0.
  step. step. if_false_by (al8 ap ltac:(lia) A8).
  step. step. step. step. step.
  rewrite !unsigned_lit by lia.
  replace (s + Z.of_nat (fld_s l + fld_n l) - (s + Z.of_nat (fld_s l))) with (Z.of_nat (fld_n l)) by lia.
  apply evt_done. do 9 eexists. split; [reflexivity|].
  do 4 (split; [eassumption|]). eassumption.
Qed.

(* the loop of repace_conf.c:90-91, at 0x134b0 *)
Lemma loop1 : forall k (i : nat) (t0 a6 a7 : word) (v1 v3 v4 v5 : Z),
  (i + S k = length l)%nat -> sep_run l = (i + sep_run (skipn i l))%nat ->
  v1 = E -> v3 = s + Z.of_nat i -> v4 = 32 -> v5 = 4294976000 ->
  (forall (a6' : word) (w3 : Z), w3 = s + Z.of_nat (sep_run l) ->
     evt rsegs Q (ST 0x134d4 t0 (Z_to_bv 64 E) (Z_to_bv 64 w3) (Z_to_bv 64 32) (Z_to_bv 64 4294976000) a6' a7)) ->
  evt rsegs Q (ST 0x134b0 t0 (Z_to_bv 64 v1) (Z_to_bv 64 v3) (Z_to_bv 64 v4) (Z_to_bv 64 v5) a6 a7).
Proof.
  induction k as [|k IH]; intros i t0 a6 a7 v1 v3 v4 v5 Hk Hsr -> -> -> -> K.
  all: destruct (byte_at i ltac:(lia)) as [b Nb].
  all: pose proof (rdb m s l i b BL Nb) as R; pose proof (skipn_nth l i b Nb) as SK.
  all: rewrite SK in Hsr; cbn [sep_run] in Hsr.
  (* 0x134b0 beqz a3 (trap): s + i <> 0 *)
  all: step; br false.
  all: step; unfold zxb; step.
  all: destruct (bv_ltu (Z_to_bv 64 32) (Z_to_bv 64 (bv_unsigned b))) eqn:C1; cbv iota.
  1, 3: (apply K; pose proof (sep_hi b C1) as NS; rewrite NS in Hsr; lia).
  all: step; step; step; rewrite (sep_lo b C1).
  all: destruct (is_sep (bz b)) eqn:SB; cbn [negb]; cbv iota.
  2, 4: (apply K; lia).
  - step. step. br false. step. apply K.
    assert (skipn (S i) l = []) by (apply skipn_all2; lia). rewrite H in Hsr. cbn in Hsr. uns. lia.
  - step. step. br true.
    eapply (IH (S i)); [lia | rewrite Hsr; lia | reflexivity | uns; lia | reflexivity | reflexivity | exact K].
Qed.

(* the loop of repace_conf.c:93-94, at 0x134f8; o separators were skipped, j bytes of the field read *)
Lemma loop2 : forall (o : nat) k (j : nat) (t0 : word) (v1 v3 v4 v5 v6 v7 : Z),
  (o + j + S k = length l)%nat -> tok_run (skipn o l) = (j + tok_run (skipn (o + j) l))%nat ->
  v1 = Z.of_nat (S k) -> v3 = s + Z.of_nat o -> v4 = s + Z.of_nat (o + j) -> v5 = 32 -> v6 = E -> v7 = 4294976000 ->
  (forall (t0' a1' : word) (w4 : Z), w4 = s + Z.of_nat (o + tok_run (skipn o l)) ->
     evt rsegs Q (ST 0x13520 t0' a1' (Z_to_bv 64 (s + Z.of_nat o)) (Z_to_bv 64 w4) (Z_to_bv 64 32) (Z_to_bv 64 E)
                    (Z_to_bv 64 4294976000))) ->
  evt rsegs Q (ST 0x134f8 t0 (Z_to_bv 64 v1) (Z_to_bv 64 v3) (Z_to_bv 64 v4) (Z_to_bv 64 v5) (Z_to_bv 64 v6) (Z_to_bv 64 v7)).
Proof.
  intros o. induction k as [|k IH]; intros j t0 v1 v3 v4 v5 v6 v7 Hk Htr -> -> -> -> -> -> K.
  all: destruct (byte_at (o + j) ltac:(lia)) as [b Nb].
  all: pose proof (rdb m s l (o + j) b BL Nb) as R; pose proof (skipn_nth l (o + j) b Nb) as SK.
  all: rewrite SK in Htr; cbn [tok_run] in Htr.
  (* 0x134f8 beqz a4 (trap): s + o + j <> 0 *)
  all: step; br false.
  all: step; unfold zxb; step.
  all: destruct (bv_ltu (Z_to_bv 64 32) (Z_to_bv 64 (bv_unsigned b))) eqn:C1; cbv iota.
  1, 3: pose proof (sep_hi b C1) as NS; rewrite NS in Htr.
  3, 4: step; step; step; rewrite (sep_lo b C1); destruct (is_sep (bz b)) eqn:SB; cbn [negb]; cbv iota.
  (* k = 0: last byte of [p, end) *)
  - step. step. step. br false. step. apply K.
    assert (skipn (S (o + j)) l = []) by (apply skipn_all2; lia). rewrite H in Htr. cbn in Htr. uns. lia.
  - step. step. step. br true.
    eapply (IH (S j)); [lia | rewrite Htr; replace (o + S j)%nat with (S (o + j)) by lia; lia
                       | uns; lia | reflexivity | uns; lia | reflexivity | reflexivity | reflexivity | exact K].
  - apply K. lia.
  - step. step. step. br false. step. apply K.
    assert (skipn (S (o + j)) l = []) by (apply skipn_all2; lia). rewrite H in Htr. cbn in Htr. uns. lia.
  - apply K. lia.
  - step. step. step. br true.
    eapply (IH (S j)); [lia | rewrite Htr; replace (o + S j)%nat with (S (o + j)) by lia; lia
                       | uns; lia | reflexivity | uns; lia | reflexivity | reflexivity | reflexivity | exact K].
Qed.

End F.

Theorem field_holds : field_contract.
Proof.
  unfold field_contract, FIELD.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m pp ap s l J
    Hs He BL CP CA DPA P8 A8 MI.
  pose proof (sep_run_le l) as SL.
  pose proof (tok_run_le (skipn (sep_run l) l)) as TL. rewrite length_skipn in TL.
  pose proof (cells_at_bound rsegs m pp _ (proj1 CP)) as BP. cbn [cells_size csize] in BP.
  assert (FIN : forall (t0 a1 a5 a6 a7 : word) (v3 v4 : Z),
            v3 = s + Z.of_nat (fld_s l) -> v4 = s + Z.of_nat (fld_s l + fld_n l) ->
            evt rsegs (field_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m pp ap s l)
              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pp) a1 (Z_to_bv 64 ap) (Z_to_bv 64 v3) (Z_to_bv 64 v4)
                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13520) fc None m (seg_rom rsegs))).
  { intros. eapply fin; eauto. subst. unfold fld_s, fld_n. lia. }
  (* the separators run *)
  assert (AFTER1 : forall (a4' a5' a6' : word) (v1 w3 : Z), v1 = s + Z.of_nat (length l) -> w3 = s + Z.of_nat (sep_run l) ->
            evt rsegs (field_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m pp ap s l)
              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pp) (Z_to_bv 64 v1) (Z_to_bv 64 ap)
                       (Z_to_bv 64 w3) a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x134d4) fc None m (seg_rom rsegs))).
  { intros a4' a5' a6' v1 w3 -> ->.
    step. step.
    destruct (Nat.eq_dec (sep_run l) (length l)) as [EQ|NE].
    - br true. eapply FIN; [reflexivity|]. unfold fld_s, fld_n.
      rewrite EQ, skipn_all2 by lia. cbn. lia.
    - br false. do 7 step.
      eapply loop2 with (o := sep_run l) (k := (length l - sep_run l - 1)%nat) (j := 0%nat).
      all: lazymatch goal with
           | |- forall _ : word, _ => intros t0' a1' w4 ->; eapply FIN; reflexivity
           | |- tok_run _ = _ => rewrite Nat.add_0_r; lia
           | |- _ = _ + Z.of_nat (_ + 0) => uns; rewrite Nat.add_0_r; reflexivity
           | _ => first [ eassumption | lia | reflexivity | (uns; lia) ]
           end. }
  (* 0x13490 andi a3,a0,7; 0x13494 bnez a3 (trap): pp mod 8 = 0 *)
  step. step. if_false_by (al8 pp ltac:(lia) P8).
  destruct (Nat.eq_dec (length l) 0) as [L0|L0].
  - step. step. br true.
    eapply AFTER1; [reflexivity | lia].
  - step. step. br false. step. step. step. step.
    eapply loop1 with (k := (length l - 1)%nat) (i := 0%nat).
    all: first [ intros a6' w3 Hw3; eapply AFTER1; [reflexivity | exact Hw3] | eassumption | reflexivity | lia ].
Qed.
