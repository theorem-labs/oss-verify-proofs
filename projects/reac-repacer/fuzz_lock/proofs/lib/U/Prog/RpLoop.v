(* Walk of reac-repacer's rp_lock_lookup in fuzz_lock.ubsan: the loop over the lines, 0x13384 / 0x1343c
   (repace_conf.c:122-144). Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import StrFun LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import DigitsMach field_c digits_c
  strlen_c memchr_c bcmp_c rp_lock_lookup_c RpLib RpDec RpMid.
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

Lemma memchr_res_val : forall A c n (buf : list byte), n = Z.of_nat (length buf) ->
  memchr_res A c n buf = match find_byte c buf with Some i => A + Z.of_nat i | None => 0 end.
Proof. intros A c n buf ->. unfold memchr_res. rewrite Nat2Z.id, firstn_all. reflexivity. Qed.

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

Ltac mid o len := eapply (rp_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 tx pa rate lo b std T P SL
                      Htx HtxE Hpa HPb Hrate HSTD Hstd Hb Hb8 Hlo DT DP BC MC o len).

(* 0x13384: lf = memchr(line, '\n', stop - line); end = lf ? lf : stop *)
Lemma rp_head : forall (o : nat) (fnd : Z) (m : word -> option byte)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word),
  (o < length T)%nat -> INV m ->
  (forall (m' : word -> option byte) (o' : nat) (v4 : Z)
          (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys7 ys8 ys9 yt3 yt4 yt5 yt6 : word),
     (o < o')%nat -> (o' <= length T)%nat ->
     (forall f, lk (S f) P rate (skipn o T) fnd = lk f P rate (skipn o' T) v4) -> INV m' ->
     evt rsegs Q (LS 0x1343c m' yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (tx + Z.of_nat o'))
                     (Z_to_bv 64 v4) ys5 ys6 ys7 ys8 ys9 yt3 yt4 yt5 yt6)) ->
  evt rsegs Q (LS 0x13384 m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (tx + Z.of_nat o))
                  (Z_to_bv 64 fnd) xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6).
Proof using All.
  intros o fnd m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 Ho I K.
  pose proof MC as MCu. unfold memchr_contract in MCu.
  destruct I as (I0 & [J18 C18] & [J20 C20] & [J28 C28] & [J30 C30]).
  destruct I0 as (BT & BP & FHL & FS & ST & MU & WM & MI).
  pose proof (bytes_at_bound _ _ _ _ BT) as BTb.
  pose proof (bnd_sp sp) as Rsp.
  assert (BS : bytes_at rsegs m (tx + Z.of_nat o) (skipn o T)) by (apply bytes_skip; [exact BT | lia]).
  assert (LS0 : length (skipn o T) = (length T - o)%nat) by (rewrite length_skipn; lia).
  assert (NE : skipn o T <> []) by (intros E; rewrite E in LS0; cbn in LS0; lia).
  (* 0x13384 sub a2,s10,s2; li a1,10; mv a0,s2; jal memchr *)
  step. step. step. step.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply MCu with (buf := skipn o T);
      [ rewrite unsigned_lit by lia; rewrite ?Z.add_0_r; exact BS
      | apply memchr_ok_len; unsi; lia
      | exact MI ]
    | post_call segs mm ] end.
  repeat match goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end.
  unsi. rewrite (memchr_res_val _ _ _ (skipn o T)) by lia. change (10 mod 256) with 10.
  destruct (find_byte 10 (skipn o T)) as [j|] eqn:FB.
  - pose proof (find_byte_lt _ _ _ FB) as Hj.
    (* 0x13394 mv s7,a0; mv s6,s10; beqz a0; mv s6,s7 *)
    step. step. step. br false. step.
    mid o j; [ | | | right; split; [lia | lia] | mk_inv | ].
    1-3: lia.
    intros m' v2 v4 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys7 ys8 ys9 yt3 yt4 yt5 yt6 H2 H4 HI.
    replace v2 with (tx + Z.of_nat (o + S j)) by (rewrite H2, (proj2 (Z.eqb_neq _ 0)) by lia; lia).
    eapply K; [lia | lia | | exact HI].
    intros f. rewrite lk_cons by exact NE. rewrite FB, skipn_skipn.
    replace (S j + o)%nat with (o + S j)%nat by lia. rewrite H4. reflexivity.
  - (* 0x13394 mv s7,a0; mv s6,s10; beqz a0 *)
    step. step. step. br true.
    mid o (length T - o)%nat; [ | | | left; split; [lia | lia] | mk_inv | ].
    1-3: lia.
    intros m' v2 v4 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys7 ys8 ys9 yt3 yt4 yt5 yt6 H2 H4 HI.
    replace v2 with (tx + Z.of_nat (length T)) by (rewrite H2; reflexivity).
    eapply K; [lia | lia | | exact HI].
    intros f. rewrite lk_cons by exact NE. rewrite FB.
    replace (skipn (length T) T) with (@nil byte) by (symmetry; apply skipn_all2; lia). rewrite lk_nil.
    rewrite H4. rewrite firstn_all2 by lia. reflexivity.
Qed.

Ltac head o := eapply (rp_head o).

(* the loop of repace_conf.c:122-143: at 0x13384 the line starts at tx + o, found = fnd *)
Lemma rp_loop : forall (Kn o : nat) (fnd : Z) (fuel : nat) (m : word -> option byte)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word),
  (length T - o <= Kn)%nat -> (o < length T)%nat -> (length (skipn o T) <= fuel)%nat ->
  lock_lookup T P rate = lk fuel P rate (skipn o T) fnd -> INV m ->
  evt rsegs Q (LS 0x13384 m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (tx + Z.of_nat o))
                  (Z_to_bv 64 fnd) xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6).
Proof using All.
  induction Kn as [|Kn IH];
    intros o fnd fuel m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6
      HK Ho Hfu HLL I; [lia|].
  head o; [exact Ho | exact I |].
  intros m' o' v4 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys7 ys8 ys9 yt3 yt4 yt5 yt6 Ho1 Ho2 Hlk I'.
  pose proof (bytes_at_bound _ _ _ _ (proj1 (proj1 I'))) as BTb.
  pose proof (bnd_sp sp) as Rsp.
  rewrite length_skipn in Hfu.
  destruct fuel as [|f]; [lia|].
  (* 0x1343c bltu s2,s10 *)
  step.
  destruct (Nat.ltb_spec o' (length T)) as [Lt|Ge].
  - br true.
    eapply (IH o' v4 f); [lia | exact Lt | rewrite length_skipn; lia | rewrite HLL; apply Hlk | exact I'].
  - br false.
    (* 0x13440 j 0x132ec *)
    step.
    destruct I' as (I0 & [J18 C18] & [J20 C20] & [J28 C28] & [J30 C30]).
    destruct I0 as (BT & BP & FHL & FS & ST & MU & WM & MI).
    pose proof (rw_app2 _ _ _ _ _ C28 C30 ltac:(cbn; lia)) as F40.
    pose proof (rw_app2 _ _ _ _ _ C20 F40 ltac:(cbn; lia)) as F32.
    pose proof (rw_app2 _ _ _ _ _ C18 F32 ltac:(cbn; lia)) as F24.
    pose proof (rw_app2 _ _ _ _ _ FHL F24 ltac:(cbn; lia)) as FR.
    eapply (rp_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 tx pa rate lo b T P SL
              Htx Hpa HPb Hb Hlo DP);
      [ | exact FR | reflexivity | exact FS | exact ST | exact MU | exact WM | exact MI ].
    rewrite HLL, Hlk. replace (skipn o' T) with (@nil byte) by (symmetry; apply skipn_all2; lia).
    rewrite lk_nil. reflexivity.
Qed.

End R.
