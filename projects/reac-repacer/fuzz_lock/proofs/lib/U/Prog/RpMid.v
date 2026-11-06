(* Walk of reac-repacer's rp_lock_lookup in fuzz_lock.ubsan: one line from p = line, 0x133a4-0x13404
   (repace_conf.c:125-130). Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import StrFun LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import DigitsMach field_c digits_c
  strlen_c memchr_c bcmp_c rp_lock_lookup_c RpLib RpDec.
Import ListNotations.
Open Scope Z_scope.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

Ltac unsi := repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      lazymatch e with context [bv_unsigned _] => fail | _ => rewrite (unsigned_lit e) by lia end
  end.

Lemma fld_le : forall l, (fld_s l + fld_n l <= length l)%nat.
Proof.
  intros l. unfold fld_s, fld_n. pose proof (sep_run_le l) as H1. pose proof (tok_run_le (skipn (sep_run l) l)) as H2.
  rewrite length_skipn in H2. lia.
Qed.

Lemma memchr_res_fact : forall A c n (buf : list byte), 0 < A -> A + Z.of_nat (length buf) <= 2^64 ->
  n = Z.of_nat (length buf) ->
  (0 <= memchr_res A c n buf < 2^64) /\ (memchr_res A c n buf = 0 <-> is_some (find_byte c buf) = false).
Proof.
  intros A c n buf HA HL ->. unfold memchr_res. rewrite Nat2Z.id, firstn_all.
  destruct (find_byte c buf) eqn:E.
  - apply find_byte_lt in E. split; [lia|]. split; intros H; [lia | discriminate].
  - split; [lia|]. tauto.
Qed.

Lemma bytes_skip' : forall m A (bs : list byte) k A' bs', bytes_at rsegs m A bs -> (k <= length bs)%nat ->
  A' = A + Z.of_nat k -> bs' = skipn k bs -> bytes_at rsegs m A' bs'.
Proof. intros m A bs k A' bs' H Hk -> ->. apply bytes_skip; assumption. Qed.

Section R.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (tx pa rate lo b std : Z) (T P SL : list byte).
Hypothesis Htx : 0 < tx.
Hypothesis HtxE : tx + Z.of_nat (length T) < 2^64.
Hypothesis Hpa : 0 < pa.
Hypothesis HPb : pa + Z.of_nat (length P + 1 + length SL) <= 2^64.
Hypothesis Hrate : rate = 44100 \/ rate = 48000 \/ rate = 96000.
Hypothesis HSTD : std_period rate = std.
Hypothesis Hstd : std = 272109 \/ std = 250000 \/ std = 125000.
Hypothesis Hb : b + 160 = bv_unsigned sp.
Hypothesis Hb8 : b mod 8 = 0.
Hypothesis Hlo : 0 <= lo <= b.
Hypothesis DT : tx + Z.of_nat (length T) <= b \/ b + 160 <= tx.
Hypothesis DP : pa + Z.of_nat (length P + 1 + length SL) <= b \/ b + 160 <= pa.

Local Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Local Notation Q := (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (lock_lookup T P rate)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_FRAME, bv_unsigned sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp)).

(* the registers in the loop: s0 rate, s1 -1, s2 the line, s3 strlen(port), s4 found, s10 stop, s11 '#' *)
Local Notation LS pc mm xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 vs2 vs4 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 :=
  (MS (mkR xra (Z_to_bv 64 b) gp tp xt0 xt1 xt2 (Z_to_bv 64 rate) (Z_to_bv 64 (-1)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           vs2 (Z_to_bv 64 (Z.of_nat (length P))) vs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (tx + Z.of_nat (length T)))
           (Z_to_bv 64 35) xt3 xt4 xt5 xt6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Local Notation INV0 m := (RpLib.INV0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 tx pa lo b std T P SL m).
Local Notation INV m := (RpLib.INV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 tx pa lo b std T P SL m).

Ltac slot := first [ eapply c8_cb; eassumption | eapply cb_ex; eassumption ].
Ltac mk_inv0 := refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); assumption.
Ltac mk_inv := refine (conj _ (conj _ (conj _ (conj _ _)))); [mk_inv0 | slot | slot | slot | slot].
Hypothesis BC : bcmp_contract.
Hypothesis MC : memchr_contract.

Lemma fld_at' : forall l k k', k = k' -> fld l k = (k' + fld_s (skipn k' l), fld_n (skipn k' l))%nat.
Proof. intros l k k' ->. apply fld_at. Qed.

Ltac dec1e l o :=
  eapply (rp_dec1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 tx pa rate lo b std T P SL
            Htx HtxE Hpa HPb Hrate HSTD Hstd Hb Hb8 Hlo DT DP BC l o (fld_s l) (fld_n l)
            (fld_s l + fld_n l + fld_s (skipn (fld_s l + fld_n l) l))%nat (fld_n (skipn (fld_s l + fld_n l) l))
            (fld_s l + fld_n l + (fld_s (skipn (fld_s l + fld_n l) l) + fld_n (skipn (fld_s l + fld_n l) l))
             + fld_s (skipn (fld_s l + fld_n l + (fld_s (skipn (fld_s l + fld_n l) l)
                                                  + fld_n (skipn (fld_s l + fld_n l) l))) l))%nat
            (fld_n (skipn (fld_s l + fld_n l + (fld_s (skipn (fld_s l + fld_n l) l)
                                                + fld_n (skipn (fld_s l + fld_n l) l))) l))).

Ltac dec1 l o := dec1e l o;
  [ rewrite fld_at; reflexivity | rewrite fld_at; reflexivity | apply fld_at'; lia | lia | lia | lia
  | rewrite ?Z.add_0_r; unsi; eapply proj1; eapply memchr_res_fact; lia
  | rewrite ?Z.add_0_r; unsi; eapply proj2; eapply memchr_res_fact; lia
  | idtac | idtac | idtac | lia | lia | lia
  | first [ eassumption | subst l; apply bytes_sub; [assumption | lia] ]
  | mk_inv0 | eassumption | eassumption | eassumption | eassumption | idtac ];
  [ lia | lia | lia | ].

(* 0x133a4: sd p; has_nul = memchr(line, 0, end - line); three fields; line = lf ? lf + 1 : stop *)
Lemma rp_mid : forall (o len : nat) (fnd e6 lfz : Z) (m : word -> option byte)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xs9 xt3 xt4 xt5 xt6 : word),
  (o + len <= length T)%nat -> (o < length T)%nat -> e6 = tx + Z.of_nat o + Z.of_nat len ->
  (lfz = 0 /\ (o + len = length T)%nat) \/ (lfz = tx + Z.of_nat o + Z.of_nat len /\ (o + len < length T)%nat) ->
  INV m ->
  (forall (m' : word -> option byte) (v2 v4 : Z)
          (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys7 ys8 ys9 yt3 yt4 yt5 yt6 : word),
     v2 = (if lfz =? 0 then tx + Z.of_nat (length T) else lfz + 1) ->
     v4 = upd P rate (firstn len (skipn o T)) fnd -> INV m' ->
     evt rsegs Q (LS 0x1343c m' yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 v2) (Z_to_bv 64 v4)
                     ys5 ys6 ys7 ys8 ys9 yt3 yt4 yt5 yt6)) ->
  evt rsegs Q (LS 0x133a4 m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (tx + Z.of_nat o))
                  (Z_to_bv 64 fnd) xs5 (Z_to_bv 64 e6) (Z_to_bv 64 lfz) xs8 xs9 xt3 xt4 xt5 xt6).
Proof using All.
  intros o len fnd e6 lfz m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xs9 xt3 xt4 xt5 xt6
    Hol Ho -> LF I K.
  pose proof MC as MCu. unfold memchr_contract in MCu.
  destruct I as (I0 & [J18 C18] & [J20 C20] & [J28 C28] & [J30 C30]).
  destruct I0 as (BT & BP & FHL & FS & ST & MU & WM & MI).
  remember (firstn len (skipn o T)) as l eqn:HLdef.
  assert (Ll : length l = len) by (subst l; rewrite length_firstn, length_skipn; lia).
  assert (BL : bytes_at rsegs m (tx + Z.of_nat o) l) by (subst l; apply bytes_sub; [exact BT | lia]).
  pose proof (bytes_at_bound _ _ _ _ BT) as BTb.
  pose proof (bnd_sp sp) as Rsp.
  pose proof (fld_le l) as FL1b.
  pose proof (fld_le (skipn (fld_s l + fld_n l) l)) as FL2b. rewrite length_skipn in FL2b.
  pose proof (fld_le (skipn (fld_s l + fld_n l + (fld_s (skipn (fld_s l + fld_n l) l)
                                                    + fld_n (skipn (fld_s l + fld_n l) l))) l)) as FL3b.
  rewrite length_skipn in FL3b.
  (* 0x133a4 sd s2,0x30(sp) *)
  step.
  (* 0x133a8 sub a2,s6,s2; mv a0,s2; mv a1,zero; jal memchr *)
  step. step. step. step.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply MCu with (buf := l);
      [ rewrite unsigned_lit by lia; rewrite ?Z.add_0_r; exact BL
      | apply memchr_ok_len; unsi; lia
      | exact MI ]
    | post_call segs mm ] end.
  repeat match goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end.
  (* 0x133b8 mv s9,a0 *)
  step.
  (* field(&p, end, &name): 0x133bc addi a0,sp,0x30; addi a2,sp,0x28; mv a1,s6; jal field *)
  step. step. step. step.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply field_call with (s := tx + Z.of_nat o) (l := l) (J := J28);
      [ rewrite Ll; lia | lia | lia | exact BL | exact C30 | exact C28 | lia | lia | lia | assumption ]
    | post_call segs mm ] end.
  rename PC into C30. rename POST into C28.
  (* 0x133cc mv s8,a0; field(&p, end, &per_at) *)
  step. step. step. step. step.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply field_call with (s := tx + Z.of_nat o + Z.of_nat (fld_s l + fld_n l))
                        (l := skipn (fld_s l + fld_n l) l) (J := J20);
      [ rewrite length_skipn; lia | lia | rewrite length_skipn; lia
      | eapply (bytes_skip' _ _ _ (fld_s l + fld_n l)); [exact BL | lia | reflexivity | reflexivity]
      | exact C30 | exact C20 | lia | lia | lia | assumption ]
    | post_call segs mm ] end.
  rename PC into C30. rename POST into C20.
  (* 0x133e0 mv s5,a0; field(&p, end, &lab_at) *)
  step. step. step. step. step.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply field_call
                        with (s := tx + Z.of_nat o + Z.of_nat (fld_s l + fld_n l)
                                   + Z.of_nat (fld_s (skipn (fld_s l + fld_n l) l) + fld_n (skipn (fld_s l + fld_n l) l)))
                        (l := skipn (fld_s l + fld_n l + (fld_s (skipn (fld_s l + fld_n l) l)
                                                          + fld_n (skipn (fld_s l + fld_n l) l))) l) (J := J18);
      [ rewrite length_skipn; lia | lia | rewrite length_skipn; lia
      | eapply (bytes_skip' _ _ _ (fld_s l + fld_n l + (fld_s (skipn (fld_s l + fld_n l) l)
                                                          + fld_n (skipn (fld_s l + fld_n l) l))));
        [exact BL | lia | lia | reflexivity]
      | exact C30 | exact C18 | lia | lia | lia | assumption ]
    | post_call segs mm ] end.
  rename PC into C30. rename POST into C18.
  (* 0x133f4 mv s6,a0; mv s2,s10; beqz s7 *)
  step. step. step.
  destruct LF as [[LZ LE] | [LZ LE]]; subst lfz.
  - br true. dec1 l o.
    intros m' v4 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys7 ys8 ys9 yt3 yt4 yt5 yt6 H4 HI.
    eapply K; [rewrite Z.eqb_refl; lia | exact H4 | exact HI].
  - (* 0x133fc beqz s7; 0x13400 beq s7,s1 (UBSan overflow check of lf + 1, trap at 0x1348c): lf < 2^64 - 1 *)
    br false. step. br false.
    (* 0x13404 addi s2,s7,1 *)
    step.
    dec1 l o.
    intros m' v4 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys7 ys8 ys9 yt3 yt4 yt5 yt6 H4 HI.
    eapply K; [rewrite (proj2 (Z.eqb_neq _ 0)) by lia; lia | exact H4 | exact HI].
Qed.

End R.
