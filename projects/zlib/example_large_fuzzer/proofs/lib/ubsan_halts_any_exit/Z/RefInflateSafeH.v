(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sacc :=
  cbn [is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize
       is_whave is_wnext is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode
       is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes
       is_sane is_back is_was is_self_blk is_reqwrap is_reqbits
       iset_mode iset_last iset_wrap iset_havedict iset_flags iset_dmax iset_check iset_total iset_head iset_wbits
       iset_wsize iset_whave iset_wnext iset_window iset_window_blk iset_hold iset_bits iset_length iset_offset
       iset_extra iset_lencode iset_distcode iset_lenbits iset_distbits iset_ncode iset_nlen iset_ndist iset_have
       iset_next iset_lens iset_work iset_codes iset_sane iset_back iset_was iset_self_blk iset_reqwrap iset_reqbits
       ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret
       irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret
       ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler
       ic_data_type ic_msg
       icset_next_in icset_avail_in icset_outbuf icset_next_out icset_avail_out icset_total_in icset_total_out
       icset_adler icset_data_type icset_msg
       w_s w_c w_r wset_s wset_c wset_r fst snd].
Ltac sacc_in H :=
  cbn [is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize
       is_whave is_wnext is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode
       is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes
       is_sane is_back is_was is_self_blk is_reqwrap is_reqbits
       iset_mode iset_last iset_wrap iset_havedict iset_flags iset_dmax iset_check iset_total iset_head iset_wbits
       iset_wsize iset_whave iset_wnext iset_window iset_window_blk iset_hold iset_bits iset_length iset_offset
       iset_extra iset_lencode iset_distcode iset_lenbits iset_distbits iset_ncode iset_nlen iset_ndist iset_have
       iset_next iset_lens iset_work iset_codes iset_sane iset_back iset_was iset_self_blk iset_reqwrap iset_reqbits
       ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret
       irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret
       ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler
       ic_data_type ic_msg
       icset_next_in icset_avail_in icset_outbuf icset_next_out icset_avail_out icset_total_in icset_total_out
       icset_adler icset_data_type icset_msg
       w_s w_c w_r wset_s wset_c wset_r fst snd] in H.

Ltac mred :=
  cbv beta iota delta [MF WF rank Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Pos.compare_cont andb orb
                       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
                       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC].
Ltac mred_in H :=
  cbv beta iota delta [MF WF rank Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Pos.compare_cont andb orb
                       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
                       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in H.

Section Rules.
  Context {A B : Type}.

  Lemma POST_bind : forall w0 (m : AM A) (f : A -> AM B) w,
    match m w with
    | ARun a w' => POST w0 (f a w')
    | ALeave w' => WINV w'
    | ARet _ w' => WINV w' /\ INV (w_s w')
    end ->
    POST w0 (abind m f w).
  Proof. intros w0 m f w H. unfold abind. destruct (m w); exact H. Qed.

  Lemma POST_ARun : forall w0 (a : A) w', WINV w' -> PHI w' < PHI w0 -> POST w0 (ARun a w').
  Proof. intros. split; assumption. Qed.

End Rules.

Lemma gs_eq : forall A (f : inflate_state -> A) s c r, gs f (mkW s c r) = ARun (f s) (mkW s c r). Proof. reflexivity. Qed.

Lemma gr_eq : forall A (f : iregs -> A) s c r, gr f (mkW s c r) = ARun (f r) (mkW s c r). Proof. reflexivity. Qed.
Lemma us_eq : forall f s c r, us f (mkW s c r) = ARun tt (mkW (f s) c r). Proof. reflexivity. Qed.
Lemma uc_eq : forall f s c r, uc f (mkW s c r) = ARun tt (mkW s (f c) r). Proof. reflexivity. Qed.
Lemma ur_eq : forall f s c r, ur f (mkW s c r) = ARun tt (mkW s c (f r)). Proof. reflexivity. Qed.
Lemma aret_eq : forall A (a : A) w, aret a w = ARun a w. Proof. reflexivity. Qed.
Lemma aleave_eq : forall A w, @aleave A w = ALeave w. Proof. reflexivity. Qed.
Lemma areturn_eq : forall A rc w, @areturn A rc w = ARet rc w. Proof. reflexivity. Qed.
Lemma aget_eq : forall w, aget w = ARun w w. Proof. reflexivity. Qed.
Lemma amodify_eq : forall f w, amodify f w = ARun tt (f w). Proof. reflexivity. Qed.
Lemma BITS_eq : forall n s c r, BITS n (mkW s c r) = ARun (BITSv (ir_hold r) n) (mkW s c r). Proof. reflexivity. Qed.
Lemma HOLD_eq : forall s c r, HOLD (mkW s c r) = ARun (ir_hold r) (mkW s c r). Proof. reflexivity. Qed.
Lemma DROPBITS_eq : forall n s c r,
  DROPBITS n (mkW s c r) = ARun tt (mkW s c (irset_bits (irset_hold r (Z.shiftr (ir_hold r) n)) (wrap32 (ir_bits r - n)))).
Proof. reflexivity. Qed.
Lemma INITBITS_eq : forall s c r, INITBITS (mkW s c r) = ARun tt (mkW s c (irset_bits (irset_hold r 0) 0)). Proof. reflexivity. Qed.
Lemma BYTEBITS_eq : forall s c r,
  BYTEBITS (mkW s c r) = ARun tt (mkW s c (irset_bits (irset_hold r (Z.shiftr (ir_hold r) (Z.land (ir_bits r) 7))) (wrap32 (ir_bits r - Z.land (ir_bits r) 7)))).
Proof. reflexivity. Qed.
Lemma set_mode_eq : forall m s c r, set_mode m (mkW s c r) = ARun tt (mkW (iset_mode s m) c r). Proof. reflexivity. Qed.
Lemma set_msg_eq : forall m s c r, set_msg m (mkW s c r) = ARun tt (mkW s (icset_msg c m) r). Proof. reflexivity. Qed.
Lemma go_bad_eq : forall m s c r, go_bad m (mkW s c r) = ARun tt (mkW (iset_mode s BAD) (icset_msg c m) r). Proof. reflexivity. Qed.
Lemma set_adler_check_eq : forall v s c r, set_adler_check v (mkW s c r) = ARun tt (mkW (iset_check s v) (icset_adler c v) r).
Proof. reflexivity. Qed.

Ltac pstep lem := apply POST_bind; rewrite lem.

Lemma rank_le3 : forall m, rank m <= 3. Proof. intros m. pose proof (rank_range m). lia. Qed.

Definition pulled (r r' : iregs) : Prop :=
  exists k, 0 <= k
  /\ ir_next r' = ir_next r + k /\ ir_have r' = ir_have r - k /\ 0 <= ir_have r'
  /\ ir_bits r' = ir_bits r + 8 * k /\ ir_hold r' mod 2 ^ ir_bits r = ir_hold r /\ 0 <= ir_hold r' < 2 ^ ir_bits r'
  /\ ir_put r' = ir_put r /\ ir_left r' = ir_left r /\ ir_in r' = ir_in r /\ ir_out r' = ir_out r /\ ir_ret r' = ir_ret r.

Lemma pulled_refl : forall r, 0 <= ir_have r -> HB (ir_hold r) (ir_bits r) -> pulled r r.
Proof.
  intros r Hhv [Hb Hh]. exists 0. repeat split; try lia. apply Z.mod_small. lia.
Qed.

Lemma pulled_trans : forall r1 r2 r3, 0 <= ir_bits r1 -> pulled r1 r2 -> pulled r2 r3 -> pulled r1 r3.
Proof.
  intros r1 r2 r3 Hb0 (k1 & Hk1 & N1 & H1 & P1 & B1 & M1 & R1 & Q1 & L1 & I1 & O1 & T1)
         (k2 & Hk2 & N2 & H2 & P2 & B2 & M2 & R2 & Q2 & L2 & I2 & O2 & T2).
  exists (k1 + k2). repeat split; try lia.
  rewrite <- M1, <- M2. rewrite B1. symmetry. apply (mod_down (ir_bits r1) (ir_bits r1 + 8 * k1)); [lia|].
  rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Definition pullr (c : icall) (r : iregs) : iregs :=
  mkIR (ir_next r + 1) (wrap32 (ir_have r - 1)) (ir_put r) (ir_left r)
       (wrap64 (ir_hold r + shl64 (arr_get (ic_input c) (ir_next r)) (ir_bits r))) (wrap32 (ir_bits r + 8))
       (ir_in r) (ir_out r) (ir_ret r).

Lemma PULLBYTE_eq : forall s c r,
  PULLBYTE (mkW s c r) = if ir_have r =? 0 then ALeave (mkW s c r) else ARun tt (mkW s c (pullr c r)).
Proof. reflexivity. Qed.

Lemma pullr_facts : forall c r,
  0 < ir_have r -> ir_have r <= arr_len (ic_input c) -> arr_len (ic_input c) < 2 ^ 32 ->
  0 <= ir_bits r <= 55 -> 0 <= ir_hold r < 2 ^ ir_bits r ->
  0 <= arr_get (ic_input c) (ir_next r) < 256 ->
  ir_next (pullr c r) = ir_next r + 1 /\ ir_have (pullr c r) = ir_have r - 1
  /\ ir_put (pullr c r) = ir_put r /\ ir_left (pullr c r) = ir_left r
  /\ ir_hold (pullr c r) = ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r
  /\ ir_bits (pullr c r) = ir_bits r + 8
  /\ ir_in (pullr c r) = ir_in r /\ ir_out (pullr c r) = ir_out r /\ ir_ret (pullr c r) = ir_ret r
  /\ 0 <= ir_hold (pullr c r) < 2 ^ (ir_bits r + 8)
  /\ ir_hold (pullr c r) mod 2 ^ ir_bits r = ir_hold r.
Proof.
  intros c r Hh Hhl Hn Hb Hho Hby. unfold pullr. cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
  assert (Hp : 2 ^ ir_bits r * 2 ^ 8 = 2 ^ (ir_bits r + 8)) by (rewrite <- Z.pow_add_r by lia; reflexivity).
  assert (Hp2 : 2 ^ (ir_bits r + 8) <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  assert (Hsh : shl64 (arr_get (ic_input c) (ir_next r)) (ir_bits r) = arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r).
  { unfold shl64. rewrite Z.shiftl_mul_pow2 by lia. apply wrap64_id. change (2^64) with (2 * 2 ^ 63). nia. }
  rewrite Hsh.
  assert (Hsum : 0 <= ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r < 2 ^ (ir_bits r + 8)) by nia.
  rewrite (wrap64_id (ir_hold r + _)) by (change (2^64) with (2 * 2 ^ 63); lia).
  assert (Hm : (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) mod 2 ^ ir_bits r = ir_hold r).
  { rewrite Z.mod_add by (apply Z.pow_nonzero; lia). apply Z.mod_small. lia. }
  rewrite !wrap32_id by lia.
  repeat split; try reflexivity; try lia.
Qed.

Section RegsFacts.
  Variable c : icall.

  Lemma REGS_pullr : forall r, REGS c r -> 0 < ir_have r -> ir_bits r <= 55 ->
    REGS c (pullr c r) /\ pulled r (pullr c r) /\ ir_bits (pullr c r) = ir_bits r + 8 /\ ir_have (pullr c r) = ir_have r - 1.
  Proof.
    intros r HR Hh Hb.
    destruct HR as (N0 & H0 & NH & P0 & L0 & PL & [Bb Bh] & IN & LI & LO).
    destruct (pullr_facts c r Hh ltac:(lia) LI ltac:(lia) Bh (IN _)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
    split; [|split; [|split; [exact E6|exact E2]]].
    - unfold REGS, HB. rewrite E1, E2, E3, E4, E6. repeat split; try lia; apply IN.
    - exists 1. rewrite E1, E2, E3, E4, E6, E7, E8, E9, E11. repeat split; try lia.
  Qed.
End RegsFacts.

Lemma NEEDBITS_k_S : forall k n s c r,
  NEEDBITS_k (S k) n (mkW s c r)
  = if ir_bits r <? n then
      if ir_have r =? 0 then ALeave (mkW s c r) else NEEDBITS_k k n (mkW s c (pullr c r))
    else ARun tt (mkW s c r).
Proof.
  intros.
  change (NEEDBITS_k (S k) n (mkW s c r))
    with (abind (gr ir_bits) (fun bits => if bits <? n then abind PULLBYTE (fun _ => NEEDBITS_k k n) else aret tt) (mkW s c r)).
  unfold abind at 1. cbn [gr w_r]. destruct (ir_bits r <? n); [|reflexivity].
  unfold abind. rewrite PULLBYTE_eq. destruct (ir_have r =? 0); reflexivity.
Qed.

Section Needbits.
  Variable c : icall.

  Lemma NEEDBITS_k_spec : forall k n s r,
    REGS c r -> 0 <= n <= 48 -> n <= ir_bits r + 8 * Z.of_nat k ->
    (exists r', NEEDBITS_k k n (mkW s c r) = ARun tt (mkW s c r')
                /\ REGS c r' /\ pulled r r' /\ n <= ir_bits r' /\ (ir_bits r' = ir_bits r \/ ir_bits r' < n + 8))
    \/ (exists r', NEEDBITS_k k n (mkW s c r) = ALeave (mkW s c r')
                   /\ REGS c r' /\ pulled r r' /\ ir_bits r' < n /\ ir_have r' = 0).
  Proof.
    induction k as [|k IH]; intros n s r HR Hn Hk.
    - left. exists r. cbn [Z.of_nat] in Hk.
      pose proof HR as (_ & H0 & _ & _ & _ & _ & HBr & _ & _ & _).
      split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|exact HBr]|]. lia.
    - rewrite NEEDBITS_k_S. pose proof HR as (N0 & H0 & NH & P0 & L0 & PL & [Bb Bh] & IN & LI & LO).
      destruct (Z.ltb_spec (ir_bits r) n) as [LT|GE].
      + destruct (Z.eqb_spec (ir_have r) 0) as [Z0|NZ].
        * right. exists r. split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|split; assumption]|]. lia.
        * destruct (REGS_pullr c r HR ltac:(lia) ltac:(lia)) as (HR1 & HP1 & B1 & _).
          rewrite Nat2Z.inj_succ in Hk.
          destruct (IH n s (pullr c r) HR1 Hn ltac:(lia)) as [(r' & E & HR' & HP' & Hn' & Hb')|(r' & E & HR' & HP' & Hb' & Hh')].
          -- left. exists r'. split; [exact E|]. split; [exact HR'|]. split; [exact (pulled_trans r (pullr c r) r' ltac:(lia) HP1 HP')|].
             split; [exact Hn'|]. right. lia.
          -- right. exists r'. split; [exact E|]. split; [exact HR'|]. split; [exact (pulled_trans r (pullr c r) r' ltac:(lia) HP1 HP')|]. lia.
      + left. exists r. split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|split; assumption]|]. lia.
  Qed.

  Lemma NEEDBITS_spec : forall n s r,
    REGS c r -> 0 <= n <= 48 ->
    (exists r', NEEDBITS n (mkW s c r) = ARun tt (mkW s c r')
                /\ REGS c r' /\ pulled r r' /\ n <= ir_bits r' /\ (ir_bits r' = ir_bits r \/ ir_bits r' < n + 8))
    \/ (exists r', NEEDBITS n (mkW s c r) = ALeave (mkW s c r')
                   /\ REGS c r' /\ pulled r r' /\ ir_bits r' < n /\ ir_have r' = 0).
  Proof.
    intros n s r HR Hn. unfold NEEDBITS. apply NEEDBITS_k_spec; [exact HR|exact Hn|].
    pose proof HR as (_ & _ & _ & _ & _ & _ & [Bb _] & _ & _ & _). cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  Qed.
End Needbits.

Lemma BITSv_mod : forall h n, 0 <= h -> 0 <= n <= 32 -> BITSv h n = h mod 2 ^ n.
Proof.
  intros h n Hh Hn. unfold BITSv, zmask, wrap32.
  rewrite Z.shiftl_1_l. change 4294967295 with (Z.ones 32).
  replace (2 ^ n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia).
  rewrite !Z.land_ones by lia.
  rewrite (Z.mod_small (Z.ones n)) by (rewrite Z.ones_equiv; pose proof (pow2_le n 32 ltac:(lia)); pose proof (pow2_pos n ltac:(lia)); lia).
  rewrite Z.land_ones by lia. apply Z.mod_mod_divide. apply pow2_divide. lia.
Qed.

Lemma DECODE_k_O : forall p index need s c r,
  DECODE_k O p index need (mkW s c r) = ARun (code_at s p (index (ir_hold r))) (mkW s c r).
Proof. reflexivity. Qed.
Lemma DECODE_k_S : forall k p index need s c r,
  DECODE_k (S k) p index need (mkW s c r)
  = if need (code_at s p (index (ir_hold r))) <=? ir_bits r then ARun (code_at s p (index (ir_hold r))) (mkW s c r)
    else if ir_have r =? 0 then ALeave (mkW s c r) else DECODE_k k p index need (mkW s c (pullr c r)).
Proof.
  intros. cbn [DECODE_k]. unfold abind, HOLD, gr, gs. cbn [w_r w_s].
  destruct (need (code_at s p (index (ir_hold r))) <=? ir_bits r); [reflexivity|].
  rewrite PULLBYTE_eq. destruct (ir_have r =? 0); reflexivity.
Qed.

Section Decode.
  Variable c : icall.
  Variable s : inflate_state.
Variable p : codeptr.
Variable ty : codetype.
Variable root : Z.
Variable used : Z.
  Hypothesis HT : TBLg ty (code_at s p) root used.

  Let HR15 := T_root ty (code_at s p) root used HT.

  Lemma pulled_mod : forall r r' b, pulled r r' -> 0 <= ir_hold r < 2 ^ ir_bits r -> 0 <= b <= ir_bits r ->
    ir_hold r' mod 2 ^ b = ir_hold r mod 2 ^ b.
  Proof.
    intros r r' b (k & Hk & _ & _ & _ & B & M & _) Hh Hb.
    apply (mod_down b (ir_bits r)); [lia|]. rewrite M. symmetry. apply Z.mod_small. lia.
  Qed.

  Lemma DECODE1_k_spec : forall k r,
    REGS c r -> 15 < ir_bits r + 8 * Z.of_nat k ->
    (exists r' here, DECODE_k k p (fun hold => BITSv hold root) code_bits (mkW s c r) = ARun here (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ here = code_at s p (ir_hold r' mod 2 ^ root)
       /\ code_bits here <= ir_bits r' /\ (ir_bits r' = ir_bits r \/ ir_bits r' < code_bits here + 8))
    \/ (exists r', DECODE_k k p (fun hold => BITSv hold root) code_bits (mkW s c r) = ALeave (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ ir_have r' = 0 /\ ir_bits r' < rneedg (code_at s p) root (ir_hold r')).
  Proof.
    induction k as [|k IH]; intros r HR Hk; pose proof HR as (N0 & H0 & NH & P0 & L0 & PL & [Bb Bh] & IN & LI & LO).
    - left. rewrite DECODE_k_O. rewrite (BITSv_mod (ir_hold r) root) by lia.
      eexists r, _. split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|split; assumption]|].
      split; [reflexivity|]. cbn [Z.of_nat] in Hk.
      pose proof (rneedg_range ty (code_at s p) root used HT (ir_hold r)) as RR. unfold rneedg in RR. lia.
    - rewrite DECODE_k_S. rewrite (BITSv_mod (ir_hold r) root) by lia.
      pose proof (rneedg_range ty (code_at s p) root used HT (ir_hold r)) as RR. unfold rneedg in RR.
      destruct (Z.leb_spec (code_bits (code_at s p (ir_hold r mod 2 ^ root))) (ir_bits r)) as [LE|GT].
      + left. eexists r, _. split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|split; assumption]|].
        split; [reflexivity|]. lia.
      + destruct (Z.eqb_spec (ir_have r) 0) as [Z0|NZ].
        * right. exists r. split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|split; assumption]|].
          split; [exact Z0|]. unfold rneedg. lia.
        * destruct (REGS_pullr c r HR ltac:(lia) ltac:(lia)) as (HR1 & HP1 & B1 & _).
          rewrite Nat2Z.inj_succ in Hk.
          assert (MONO : forall r', pulled r r' -> ir_bits r < rneedg (code_at s p) root (ir_hold r')).
          { intros r' HP'. apply (rneedg_mono ty (code_at s p) root used HT (ir_hold r)); [lia| |unfold rneedg; lia].
            apply (pulled_mod r r'); [exact HP'|lia|lia]. }
          destruct (IH (pullr c r) HR1 ltac:(lia)) as [(r' & here & E & HR' & HP' & Eh & Hle & Hb')|(r' & E & HR' & HP' & Hh' & Hb')].
          -- left. exists r', here. split; [exact E|]. split; [exact HR'|].
             pose proof (pulled_trans r (pullr c r) r' ltac:(lia) HP1 HP') as HP.
             split; [exact HP|]. split; [exact Eh|]. split; [exact Hle|]. right.
             pose proof (MONO r' HP) as M. unfold rneedg in M. rewrite <- Eh in M. lia.
          -- right. exists r'. split; [exact E|]. split; [exact HR'|].
             split; [exact (pulled_trans r (pullr c r) r' ltac:(lia) HP1 HP')|]. split; [exact Hh'|exact Hb'].
  Qed.

  Lemma DECODE1_spec : forall r, REGS c r ->
    (exists r' here, DECODE1 p root (mkW s c r) = ARun here (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ here = code_at s p (ir_hold r' mod 2 ^ root)
       /\ code_bits here <= ir_bits r' /\ (ir_bits r' = ir_bits r \/ ir_bits r' < code_bits here + 8))
    \/ (exists r', DECODE1 p root (mkW s c r) = ALeave (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ ir_have r' = 0 /\ ir_bits r' < rneedg (code_at s p) root (ir_hold r')).
  Proof.
    intros r HR. unfold DECODE1. apply DECODE1_k_spec; [exact HR|].
    pose proof HR as (_ & _ & _ & _ & _ & _ & [Bb _] & _ & _ & _). cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  Qed.

  Definition subix (last h : Z) : Z := code_val last + h mod 2 ^ (code_bits last + code_op last) / 2 ^ code_bits last.

  Lemma DECODE2_k_spec : forall k r last,
    REGS c r -> 15 < ir_bits r + 8 * Z.of_nat k ->
    last = code_at s p (ir_hold r mod 2 ^ root) -> is_linkb last = true -> code_bits last <= ir_bits r ->
    (exists r' here, DECODE_k k p (fun hold => code_val last + Z.shiftr (BITSv hold (code_bits last + code_op last)) (code_bits last))
                                  (fun here => wrap32 (code_bits last + code_bits here)) (mkW s c r) = ARun here (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ here = code_at s p (subix last (ir_hold r'))
       /\ 1 <= code_bits here <= 15 - root
       /\ code_bits last + code_bits here <= ir_bits r' /\ (ir_bits r' = ir_bits r \/ ir_bits r' < code_bits last + code_bits here + 8))
    \/ (exists r', DECODE_k k p (fun hold => code_val last + Z.shiftr (BITSv hold (code_bits last + code_op last)) (code_bits last))
                            (fun here => wrap32 (code_bits last + code_bits here)) (mkW s c r) = ALeave (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ ir_have r' = 0 /\ ir_bits r' < lneedg (code_at s p) root (ir_hold r')).
  Proof.
    induction k as [|k IH]; intros r last HR Hk El HL Hlb; pose proof HR as (N0 & H0 & NH & P0 & L0 & PL & [Bb Bh] & IN & LI & LO).
    - pose proof (ridx_range ty (code_at s p) root used HT (ir_hold r)) as XR.
      destruct (root_cell ty (code_at s p) root used HT _ XR) as (_ & RL & _). rewrite <- El in RL.
      destruct (RL HL) as (Lb & Lop & Lv1 & Lv2).
      assert (IX : forall h, 0 <= h -> code_val last + Z.shiftr (BITSv h (code_bits last + code_op last)) (code_bits last) = subix last h).
      { intros h Hh. unfold subix. rewrite Z.shiftr_div_pow2 by lia. rewrite BITSv_mod by lia. reflexivity. }
      assert (SUB : forall h, 0 <= h -> 1 <= code_bits (code_at s p (subix last h)) <= 15 - root).
      { intros h Hh. unfold subix. rewrite El.
        apply (sub_cell ty (code_at s p) root used HT); [exact XR|rewrite <- El; exact HL|]. rewrite <- El. apply subidx_range; lia. }
      left. rewrite DECODE_k_O. rewrite IX by lia.
      eexists r, _. split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|split; assumption]|].
      split; [reflexivity|]. split; [apply SUB; lia|]. cbn [Z.of_nat] in Hk. pose proof (SUB (ir_hold r) ltac:(lia)). lia.
    - pose proof (ridx_range ty (code_at s p) root used HT (ir_hold r)) as XR.
      destruct (root_cell ty (code_at s p) root used HT _ XR) as (_ & RL & _). rewrite <- El in RL.
      destruct (RL HL) as (Lb & Lop & Lv1 & Lv2).
      assert (IX : forall h, 0 <= h -> code_val last + Z.shiftr (BITSv h (code_bits last + code_op last)) (code_bits last) = subix last h).
      { intros h Hh. unfold subix. rewrite Z.shiftr_div_pow2 by lia. rewrite BITSv_mod by lia. reflexivity. }
      assert (SUB : forall h, 0 <= h -> 1 <= code_bits (code_at s p (subix last h)) <= 15 - root).
      { intros h Hh. unfold subix. rewrite El.
        apply (sub_cell ty (code_at s p) root used HT); [exact XR|rewrite <- El; exact HL|]. rewrite <- El. apply subidx_range; lia. }

      assert (LN : forall r', pulled r r' -> lneedg (code_at s p) root (ir_hold r') = code_bits last + code_bits (code_at s p (subix last (ir_hold r')))).
      { intros r' HP'. unfold lneedg.
        rewrite (pulled_mod r r' root HP' ltac:(lia) ltac:(lia)). rewrite <- El, HL. reflexivity. }
      rewrite DECODE_k_S. rewrite IX by lia.
      pose proof (SUB (ir_hold r) ltac:(lia)) as SB.
      rewrite (wrap32_id (code_bits last + _)) by lia.
      destruct (Z.leb_spec (code_bits last + code_bits (code_at s p (subix last (ir_hold r)))) (ir_bits r)) as [LE|GT].
      + left. eexists r, _. split; [reflexivity|]. split; [exact HR|]. split; [apply pulled_refl; [lia|split; assumption]|].
        split; [reflexivity|]. split; [exact SB|]. lia.
      + destruct (Z.eqb_spec (ir_have r) 0) as [Z0|NZ].
        * right. exists r. split; [reflexivity|]. split; [exact HR|].
          assert (HP0 : pulled r r) by (apply pulled_refl; [lia|split; assumption]).
          split; [exact HP0|]. split; [exact Z0|]. rewrite (LN r HP0). lia.
        * destruct (REGS_pullr c r HR ltac:(lia) ltac:(lia)) as (HR1 & HP1 & B1 & _).
          rewrite Nat2Z.inj_succ in Hk.
          assert (MONO : forall r', pulled r r' -> ir_bits r < lneedg (code_at s p) root (ir_hold r')).
          { intros r' HP'. apply (lneedg_mono ty (code_at s p) root used HT (ir_hold r)); [lia| |].
            - apply (pulled_mod r r'); [exact HP'|lia|lia].
            - rewrite (LN r ltac:(apply pulled_refl; [lia|split; assumption])). lia. }
          assert (El1 : last = code_at s p (ir_hold (pullr c r) mod 2 ^ root)).
          { rewrite (pulled_mod r (pullr c r) root HP1 ltac:(lia) ltac:(lia)). exact El. }
          destruct (IH (pullr c r) last HR1 ltac:(lia) El1 HL ltac:(lia))
            as [(r' & here & E & HR' & HP' & Eh & Hsb & Hle & Hb')|(r' & E & HR' & HP' & Hh' & Hb')].
          -- left. exists r', here. split; [exact E|]. split; [exact HR'|].
             pose proof (pulled_trans r (pullr c r) r' ltac:(lia) HP1 HP') as HP.
             split; [exact HP|]. split; [exact Eh|]. split; [exact Hsb|]. split; [exact Hle|]. right.
             pose proof (MONO r' HP) as M. rewrite (LN r' HP) in M. rewrite <- Eh in M. lia.
          -- right. exists r'. split; [exact E|]. split; [exact HR'|].
             split; [exact (pulled_trans r (pullr c r) r' ltac:(lia) HP1 HP')|]. split; [exact Hh'|exact Hb'].
  Qed.

  Lemma DECODE2_spec : forall r last,
    REGS c r -> last = code_at s p (ir_hold r mod 2 ^ root) -> is_linkb last = true -> code_bits last <= ir_bits r ->
    (exists r' here, DECODE2 p last (mkW s c r) = ARun here (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ here = code_at s p (subix last (ir_hold r'))
       /\ 1 <= code_bits here <= 15 - root
       /\ code_bits last + code_bits here <= ir_bits r' /\ (ir_bits r' = ir_bits r \/ ir_bits r' < code_bits last + code_bits here + 8))
    \/ (exists r', DECODE2 p last (mkW s c r) = ALeave (mkW s c r')
       /\ REGS c r' /\ pulled r r' /\ ir_have r' = 0 /\ ir_bits r' < lneedg (code_at s p) root (ir_hold r')).
  Proof.
    intros r last HR El HL Hlb. unfold DECODE2. apply DECODE2_k_spec; try assumption.
    pose proof HR as (_ & _ & _ & _ & _ & _ & [Bb _] & _ & _ & _). cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  Qed.
End Decode.
