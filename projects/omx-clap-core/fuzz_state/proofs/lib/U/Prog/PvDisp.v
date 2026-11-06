From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct PjIn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import ReaderRes PvDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require skip_ws_c.
Import ListNotations.
Open Scope Z_scope.

Lemma eqb0_word : forall z, -2 ^ 64 < z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = (z =? 0).
Proof.
  intros z Hz. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec z 0) as [E|E]; [subst z; reflexivity|].
  apply Z.eqb_neq. intro E2. apply E. Z.div_mod_to_equations. lia.
Qed.

Lemma eqbm1_word : forall z, 0 <= z < 2 ^ 62 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 (-1)) = false.
Proof.
  intros z Hz. unfold bv_eqb. rewrite !unsigned_lit_wrap. apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Lemma byte_lt : forall c : byte, 0 <= bv_unsigned c < 256.
Proof. intros c. pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Lemma ws_rest : forall l : list byte, zb (skipn (skip_ws_c.ws_len l) l) = skip (zb l).
Proof.
  unfold zb. induction l as [|b l IH]; [reflexivity|].
  cbn [skip_ws_c.ws_len map skip].
  change (skip_ws_c.ws b) with (ws (bv_unsigned b)).
  destruct (ws (bv_unsigned b)); [exact IH | reflexivity].
Qed.

Lemma rest_at_ws : forall (tb : list byte) text p, text <= p ->
  rest_at tb text (p + Z.of_nat (skip_ws_c.ws_len (skipn (Z.to_nat (p - text)) tb))) = skip (rest_at tb text p).
Proof.
  intros tb text p Hp. unfold rest_at.
  replace (Z.to_nat (p + Z.of_nat (skip_ws_c.ws_len (skipn (Z.to_nat (p - text)) tb)) - text))
    with (skip_ws_c.ws_len (skipn (Z.to_nat (p - text)) tb) + Z.to_nat (p - text))%nat by lia.
  rewrite <- skipn_skipn. apply ws_rest.
Qed.

Lemma rest_at_cons : forall (tb : list byte) text P c rest,
  text <= P -> skipn (Z.to_nat (P - text)) tb = c :: rest ->
  rest_at tb text P = bv_unsigned c :: rest_at tb text (P + 1).
Proof.
  intros tb text P c rest HP SK. unfold rest_at, zb. rewrite SK. cbn [map]. f_equal.
  replace (Z.to_nat (P + 1 - text)) with (1 + Z.to_nat (P - text))%nat by lia.
  rewrite <- skipn_skipn, SK. reflexivity.
Qed.

Lemma rest_at_nil : forall (tb : list byte) text P,
  Z.of_nat (length tb) <= P - text -> rest_at tb text P = [].
Proof. intros tb text P H. unfold rest_at, zb. rewrite skipn_all2 by lia. reflexivity. Qed.

Lemma rest_at_read : forall m (tb : list byte) text P c rest,
  bytes_at rsegs m text tb -> text <= P -> skipn (Z.to_nat (P - text)) tb = c :: rest ->
  ov_read_bytes rsegs m (wa P) 1 = Some [c].
Proof.
  intros m tb text P c rest H HP SK.
  pose proof (length_skipn (Z.to_nat (P - text)) tb) as L. rewrite SK in L. cbn [length] in L.
  replace P with (text + (P - text)) at 1 by lia.
  rewrite (bytes_at_read rsegs m text tb (P - text) 1 H) by lia. rewrite SK. reflexivity.
Qed.

Lemma rest_at_some : forall (tb : list byte) text P,
  text <= P < text + Z.of_nat (length tb) ->
  exists c rest, skipn (Z.to_nat (P - text)) tb = c :: rest.
Proof.
  intros tb text P HP. destruct (skipn (Z.to_nat (P - text)) tb) as [|c rest] eqn:SK; [|eauto].
  exfalso. pose proof (length_skipn (Z.to_nat (P - text)) tb) as L. rewrite SK in L. cbn [length] in L. lia.
Qed.

Lemma stk_call : forall m m' lo hi A n bs, stk rsegs m lo hi -> munch [(A, A + n)] m m' -> wmono rsegs m m' ->
  bytes_at rsegs m' A bs -> Z.of_nat (length bs) = n -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi A n bs (H1 & H2 & H) MU WM (B1 & B2 & B) L. split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Z_lt_le_dec a A) as [LA|LA]; [|destruct (Z_lt_le_dec a (A + n)) as [LB|LB]].
  - exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. cbn [outside]. rewrite wa_unsigned by lia.
    split; [lia | exact I].
  - specialize (B (Z.to_nat (a - A)) ltac:(lia)). replace (A + Z.of_nat (Z.to_nat (a - A))) with a in B by lia.
    rewrite B. destruct (nth_error bs (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. cbn [outside]. rewrite wa_unsigned by lia.
    split; [lia | exact I].
Qed.

Lemma rw_cells_cons : forall m A c cs,
  rw_cells rsegs m A (c :: cs) -> rw_cells rsegs m A [c] /\ rw_cells rsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs [[[Hc Hcs] Hb] (Ha & Hn & Hw)].
  cbn [cells_bytes] in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb1 Hb2].
  rewrite (cbytes_length c Hc) in Hb2. cbn [cells_size] in Hn, Hw.
  split; split.
  - split; [cbn; tauto|]. cbn [cells_bytes]. rewrite app_nil_r. exact Hb1.
  - split; [lia|]. split; [cbn [cells_size]; lia|]. intros i Hi. apply Hw. cbn [cells_size] in Hi. lia.
  - split; [exact Hcs | exact Hb2].
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia.
    apply Hw. lia.
Qed.

Lemma pj_zero_transport : forall W m m' v,
  pj_zero rsegs m v -> munch W m m' -> wmono rsegs m m' -> disjoint_from W v 56 -> pj_zero rsegs m' v.
Proof.
  intros W m m' v ((A & S) & B) MU WM D.
  split; [split; [exact A|] |].
  - eapply stk_transport_disjoint; [exact S | exact MU | exact WM | replace (v + 56 - v) with 56 by lia; exact D].
  - eapply bytes_at_transport; [exact B | exact MU | rewrite repeat_length; exact D].
Qed.

Lemma z256_cases : forall (f : Z -> bool) x, 0 <= x < 256 ->
  forallb f (map Z.of_nat (seq 0 256)) = true -> f x = true.
Proof.
  intros f x R A. rewrite forallb_forall in A. apply A.
  apply in_map_iff. exists (Z.to_nat x). split; [lia | apply in_seq; lia].
Qed.

Lemma eqb_byte : forall (c : byte) k, 0 <= k < 2 ^ 64 -> bv_eqb (zxb c) (Z_to_bv 64 k) = (bv_unsigned c =? k).
Proof.
  intros c k Hk. pose proof (byte_lt c) as R. unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma lts_109 : forall c : byte, bv_lts (Z_to_bv 64 109) (zxb c) = (109 <? bv_unsigned c).
Proof.
  intros c. unfold zxb. apply Bool.eqb_prop.
  exact (z256_cases (fun x => Bool.eqb (bv_lts (Z_to_bv 64 109) (Z_to_bv 64 x)) (109 <? x)) _ (byte_lt c)
    ltac:(vm_compute; reflexivity)).
Qed.

Lemma ltu_digit58 : forall c : byte,
  bv_ltu (Z_to_bv 64 (bv_unsigned (zxb c) + -58)) (Z_to_bv 64 (-10)) = negb (digit (bv_unsigned c)).
Proof.
  intros c. unfold zxb. apply Bool.eqb_prop.
  exact (z256_cases (fun x => Bool.eqb (bv_ltu (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + -58)) (Z_to_bv 64 (-10)))
    (negb (digit x))) _ (byte_lt c) ltac:(vm_compute; reflexivity)).
Qed.

Lemma ltu_digit48 : forall c : byte,
  bv_ltu (Z_to_bv 64 (bv_unsigned (zxb c) + -48)) (Z_to_bv 64 10) = digit (bv_unsigned c).
Proof.
  intros c. unfold zxb. apply Bool.eqb_prop.
  exact (z256_cases (fun x => Bool.eqb (bv_ltu (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + -48)) (Z_to_bv 64 10))
    (digit x)) _ (byte_lt c) ltac:(vm_compute; reflexivity)).
Qed.

Lemma ltu_43 : forall c : byte,
  bv_ltu (Z_to_bv 64 58) (Z_to_bv 64 (bv_unsigned (zxb c) + -43)) =
  negb ((43 <=? bv_unsigned c) && (bv_unsigned c <=? 101)).
Proof.
  intros c. unfold zxb. apply Bool.eqb_prop.
  exact (z256_cases (fun x => Bool.eqb (bv_ltu (Z_to_bv 64 58) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + -43)))
    (negb ((43 <=? x) && (x <=? 101)))) _ (byte_lt c) ltac:(vm_compute; reflexivity)).
Qed.

Definition num5 (x : Z) : bool := (x =? 43) || (x =? 45) || (x =? 46) || (x =? 69) || (x =? 101).

Lemma mask_num : forall c : byte, 43 <= bv_unsigned c <= 101 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 288230376218820621
    (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb c) + -43)) mod 64)))) 1)) (Z_to_bv 64 0) = negb (num5 (bv_unsigned c)).
Proof.
  intros c Hc. unfold zxb.
  pose proof (z256_cases (fun x => implb ((43 <=? x) && (x <=? 101))
    (Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 288230376218820621
       (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + -43)) mod 64)))) 1)) (Z_to_bv 64 0))
       (negb (num5 x)))) _ (byte_lt c) ltac:(vm_compute; reflexivity)) as H.
  cbv beta in H.
  replace ((43 <=? bv_unsigned c) && (bv_unsigned c <=? 101)) with true in H
    by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
  apply Bool.eqb_prop. exact H.
Qed.

Lemma numch_split : forall x, 0 <= x < 256 ->
  numch x = digit x || ((43 <=? x) && (x <=? 101) && num5 x).
Proof.
  intros x R. apply Bool.eqb_prop.
  exact (z256_cases (fun x => Bool.eqb (numch x) (digit x || ((43 <=? x) && (x <=? 101) && num5 x))) x R
    ltac:(vm_compute; reflexivity)).
Qed.

Lemma span_len_cons : forall b r, numch b = true ->
  length (fst (span numch (b :: r))) = S (length (fst (span numch r))).
Proof. intros b r H. cbn [span]. rewrite H. destruct (span numch r). reflexivity. Qed.

Lemma span_len_nil : forall b r, numch b = false -> length (fst (span numch (b :: r))) = 0%nat.
Proof. intros b r H. cbn [span]. rewrite H. reflexivity. Qed.

Lemma span_fst_len : forall (f : Z -> bool) (l : list Z), (length (fst (span f l)) <= length l)%nat.
Proof.
  intros f l. induction l as [|b r IH]; cbn [span]; [cbn; lia|].
  destruct (f b); [destruct (span f r) as [a z]; cbn in *; lia | cbn; lia].
Qed.

Lemma rest_at_len : forall (tb : list byte) text P,
  length (rest_at tb text P) = (length tb - Z.to_nat (P - text))%nat.
Proof. intros tb text P. unfold rest_at, zb. rewrite length_map, length_skipn. reflexivity. Qed.

Lemma num_tok_eq : forall b y, num_tok (b :: y) =
  match skipn (if b =? 45 then 1%nat else 0%nat) (b :: y) with
  | [] => None
  | c :: z =>
    if negb (digit c) then None
    else if (c =? 48) && match z with c1 :: _ => digit c1 | [] => false end then None
    else let (a, r) := span numch z in Some (firstn (if b =? 45 then 1%nat else 0%nat) (b :: y) ++ c :: a, r)
  end.
Proof. reflexivity. Qed.

Lemma frame_keep : forall m lo A junk cs,
  stk rsegs m lo A -> rw_cells rsegs m A (CB 16 junk :: cs) -> lo <= A ->
  stk rsegs m lo (A + 16) /\ rw_cells rsegs m (A + 16) cs.
Proof.
  intros m lo A junk cs ST FR HL. apply rw_cells_cons in FR. destruct FR as [F1 F2].
  split; [exact (stk_release rsegs m lo A [CB 16 junk] ST F1 HL) | exact F2].
Qed.

Lemma pv_ret : forall (rx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x3 x4 : word)
    (F : bvmap 5 word) (fc : bv 32) (m mm : word -> option byte) (q text len p d : Z) (tb : list byte) (v lo P : Z)
    (junk : list byte),
  pj_in_ok rsegs mm q text len P d tb -> rest_at tb text P = skip (rest_at tb text p) ->
  (rest_at tb text P = [] \/ exists b y, rest_at tb text P = b :: y /\ other_b b /\ num_tok (b :: y) = None) ->
  pj_zero rsegs m v ->
  stk rsegs mm lo (bv_unsigned sp + -64) ->
  rw_cells rsegs mm (bv_unsigned sp + -64) [CB 16 junk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(bv_unsigned sp + -64, bv_unsigned sp); (q, q + 8)] m mm -> wmono rsegs m mm ->
  lo + 64 <= bv_unsigned sp ->
  disjoint_from [(q, q + 24); (text, text + len); (v, v + 56)] (bv_unsigned sp - 64) 64 ->
  disjoint_from [(text, text + len); (q, q + 24)] v 56 ->
  evt rsegs (pv_disp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m q text len p d tb v lo)
    (MS (mkR rx (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 v) (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (-1)) x3 x4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1461c) fc None mm (seg_rom rsegs)).
Proof.
  intros rx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x3 x4 F fc m mm
    q text len p d tb v lo P junk PJ RP NT PZ ST FR MU WM LO SD VD.
  pose proof (pj_in_ok_bounds rsegs _ _ _ _ _ _ _ PJ) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  cbn [disjoint_from] in SD, VD.
  pose proof (rw_cells_bound rsegs _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  do 9 step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold pv_disp_post. exists P, mm. do 3 eexists. exists (Z_to_bv 64 0). do 11 eexists.
  split; [lia|]. split; [exact RP|]. split; [exact PJ|]. split; [exact WM|].
  left. split; [exact NT|]. split; [exact MU|]. split; [exact ST|].
  split; [eapply pj_zero_transport; [exact PZ | exact MU | exact WM | cbn [disjoint_from]; lia]|].
  reflexivity.
Qed.

Lemma num_scan : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (text len : Z) (tb : list byte) (n : nat)
    (a5 a6 : word) (S : Z),
  Z.to_nat (text + len - S) = n -> text <= S < text + len -> 0 < text -> text + len < 2 ^ 62 ->
  Z.of_nat (length tb) = len -> bytes_at rsegs mm text tb ->
  evt rsegs (fun ms' => exists a5' a6' : word,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (text + len)) (Z_to_bv 64 10) (Z_to_bv 64 58)
                    (Z_to_bv 64 288230376218820621) a5' a6' a7 s2 s3
                    (Z_to_bv 64 (S + Z.of_nat (length (fst (span numch (rest_at tb text S))))))
                    s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x146e8) fc None mm (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (text + len)) (Z_to_bv 64 10) (Z_to_bv 64 58)
             (Z_to_bv 64 288230376218820621) a5 a6 a7 s2 s3 (Z_to_bv 64 S) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x146bc) fc None mm (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm text len tb n.
  induction n as [|n IH]; intros a5 a6 S HN HS HT HE HL HB; [lia|].
  destruct (rest_at_some tb text S ltac:(lia)) as (c & rest & SK).
  pose proof (rest_at_read mm tb text S c rest HB ltac:(lia) SK) as RB.
  pose proof (rest_at_cons tb text S c rest ltac:(lia) SK) as RC.
  pose proof (byte_lt c) as CR.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  assert (EXIT : numch (bv_unsigned c) = false -> forall a5' a6' : word,
    evt rsegs QQ
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (text + len)) (Z_to_bv 64 10) (Z_to_bv 64 58)
               (Z_to_bv 64 288230376218820621) a5' a6' a7 s2 s3 (Z_to_bv 64 S) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x146e8) fc None mm (seg_rom rsegs))).
  { intros NC a5' a6'. apply evt_done. exists a5', a6'.
    rewrite RC, (span_len_nil _ _ NC). cbn [Z.of_nat]. rewrite Z.add_0_r. reflexivity. }
  assert (CONT : numch (bv_unsigned c) = true -> forall a5' a6' : word,
    evt rsegs QQ
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (text + len)) (Z_to_bv 64 10) (Z_to_bv 64 58)
               (Z_to_bv 64 288230376218820621) a5' a6' a7 s2 s3 (Z_to_bv 64 S) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x146dc) fc None mm (seg_rom rsegs))).
  { intros NC a5' a6'.
    assert (LS : S + Z.of_nat (length (fst (span numch (rest_at tb text S)))) =
                 S + 1 + Z.of_nat (length (fst (span numch (rest_at tb text (S + 1))))))
      by (rewrite RC, (span_len_cons _ _ NC); lia).
    step. step.
    if_cases HC; unfold bv_eqb in HC; rewrite !unsigned_lit in HC by lia.
    - apply negb_true_iff, Z.eqb_neq in HC. unfold QQ. rewrite LS.
      apply IH; [lia | lia | exact HT | exact HE | exact HL | exact HB].
    - apply negb_false_iff, Z.eqb_eq in HC. step.
      apply evt_done. exists a5', a6'. rewrite LS.
      rewrite (rest_at_nil tb text (S + 1)) by lia.
      replace (S + 1 + Z.of_nat (length (fst (span numch [])))) with (text + len) by (cbn; lia). reflexivity. }
  step. step. step.
  if_cases HG; rewrite ltu_digit48 in HG.
  - apply CONT. unfold numch. rewrite HG. reflexivity.
  - step. step.
    if_cases HH; rewrite ltu_43 in HH.
    + apply EXIT. rewrite numch_split by lia. rewrite HG. apply negb_true_iff in HH. rewrite HH. reflexivity.
    + pose proof HH as HH'. apply negb_false_iff in HH'. apply andb_true_iff in HH'. destruct HH' as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2.
      step. step. step.
      if_cases HM; rewrite mask_num in HM by lia.
      * apply EXIT. rewrite numch_split by lia. rewrite HG. apply negb_true_iff in HM. rewrite HM.
        apply negb_false_iff in HH. rewrite HH. reflexivity.
      * apply CONT. rewrite numch_split by lia. rewrite HG. apply negb_false_iff in HM. rewrite HM.
        apply negb_false_iff in HH. rewrite HH. reflexivity.
Qed.

Lemma pv_num : forall (rx ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m mm : word -> option byte) (q text len p d : Z) (tb : list byte) (v lo P : Z)
    (junk : list byte) (c : byte) (y : list Z),
  pj_in_ok rsegs mm q text len P d tb -> rest_at tb text P = skip (rest_at tb text p) ->
  rest_at tb text P = bv_unsigned c :: y -> other_b (bv_unsigned c) -> P < text + len ->
  pj_zero rsegs m v ->
  stk rsegs mm lo (bv_unsigned sp + -64) ->
  rw_cells rsegs mm (bv_unsigned sp + -64) [CB 16 junk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(bv_unsigned sp + -64, bv_unsigned sp); (q, q + 8)] m mm -> wmono rsegs m mm ->
  lo + 64 <= bv_unsigned sp ->
  disjoint_from [(q, q + 24); (text, text + len); (v, v + 56)] (bv_unsigned sp - 64) 64 ->
  disjoint_from [(text, text + len); (q, q + 24)] v 56 ->
  evt rsegs (pv_disp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m q text len p d tb v lo)
    (MS (mkR rx (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 v) (Z_to_bv 64 q) (Z_to_bv 64 P)
             (Z_to_bv 64 (text + len)) (zxb c) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x145c0) fc None mm (seg_rom rsegs)).
Proof.
  intros rx ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mm
    q text len p d tb v lo P junk c y PJ RP RC OB HP PZ ST FR MU WM LO SD VD.
  pose proof (pj_in_ok_bounds rsegs _ _ _ _ _ _ _ PJ) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof PJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PT & _ & _).
  pose proof (rw_cells_bound rsegs _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof SD as SD'. pose proof VD as VD'. cbn [disjoint_from] in SD', VD'.
  pose proof (pj_zero_transport _ _ _ _ PZ MU WM ltac:(cbn [disjoint_from]; lia)) as PZm.
  pose proof (byte_lt c) as CR.
  destruct (rest_at_some tb text P ltac:(lia)) as (c0 & r0 & SK0).
  pose proof (rest_at_cons tb text P c0 r0 ltac:(lia) SK0) as RC0. rewrite RC in RC0. injection RC0 as _ EY.
  assert (J01 : 0 <= (if bv_unsigned c =? 45 then 1 else 0) <= 1) by (destruct (_ =? _); lia).
  remember (P + (if bv_unsigned c =? 45 then 1 else 0)) as S0 eqn:HS0.
  assert (KJ : skipn (if bv_unsigned c =? 45 then 1%nat else 0%nat) (bv_unsigned c :: y) = rest_at tb text S0).
  { subst S0. destruct (bv_unsigned c =? 45); cbn [skipn].
    - rewrite EY. reflexivity.
    - rewrite Z.add_0_r. symmetry. exact RC. }
  assert (K0 : forall a2' a3' : word,
    evt rsegs (pv_disp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m q text len p d tb v lo)
      (MS (mkR rx (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 v) (Z_to_bv 64 q) (Z_to_bv 64 P)
               (Z_to_bv 64 (text + len)) a2' a3' a4 a5 a6 a7 s2 s3 (Z_to_bv 64 S0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x145d8) fc None mm (seg_rom rsegs))).
  { intros a2' a3'.
    step. step.
    if_cases HS; rewrite bv_ltu_Z, !unsigned_lit in HS by lia.
    { apply negb_true_iff, Z.ltb_ge in HS.
      eapply pv_ret; [exact PJ | exact RP | | exact PZ | exact ST | exact FR | exact MU | exact WM | exact LO | exact SD | exact VD].
      right. exists (bv_unsigned c), y. split; [exact RC|]. split; [exact OB|].
      rewrite num_tok_eq, KJ, (rest_at_nil tb text S0) by lia. reflexivity. }
    apply negb_false_iff, Z.ltb_lt in HS.
    destruct (rest_at_some tb text S0 ltac:(lia)) as (c2 & z2 & SK2).
    pose proof (rest_at_read mm tb text S0 c2 z2 PT ltac:(lia) SK2) as RB2.
    pose proof (rest_at_cons tb text S0 c2 z2 ltac:(lia) SK2) as RC2.
    pose proof (byte_lt c2) as CR2.
    step. step. step. step.
    if_cases HD; rewrite ltu_digit58 in HD.
    { eapply pv_ret; [exact PJ | exact RP | | exact PZ | exact ST | exact FR | exact MU | exact WM | exact LO | exact SD | exact VD].
      right. exists (bv_unsigned c), y. split; [exact RC|]. split; [exact OB|].
      rewrite num_tok_eq, KJ, RC2. cbv beta iota zeta. rewrite HD. reflexivity. }
    apply negb_false_iff in HD.
    assert (NC2 : numch (bv_unsigned c2) = true) by (unfold numch; rewrite HD; reflexivity).
    assert (K : ((bv_unsigned c2 =? 48) && match rest_at tb text (S0 + 1) with c1 :: _ => digit c1 | [] => false end) = false ->
      forall a2'' a3'' a4' : word,
      evt rsegs (pv_disp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m q text len p d tb v lo)
        (MS (mkR rx (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 v) (Z_to_bv 64 q) (Z_to_bv 64 P)
                 (Z_to_bv 64 (text + len)) a2'' a3'' a4' a5 a6 a7 (Z_to_bv 64 (-1)) s3 (Z_to_bv 64 S0)
                 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x146a0) fc None mm (seg_rom rsegs))).
    { intros NZ a2'' a3'' a4'.
      do 7 step.
      eapply evt_cut.
      { eapply num_scan with (S := S0) (n := Z.to_nat (text + len - S0)); [reflexivity | lia | lia | lia | exact B7 | exact PT]. }
      intros ms' (a5' & a6' & ->).
      destruct (span numch (rest_at tb text (S0 + 1))) as [a r] eqn:SP.
      assert (LS : S0 + Z.of_nat (length (fst (span numch (rest_at tb text S0)))) = S0 + 1 + Z.of_nat (length a)).
      { rewrite RC2, (span_len_cons _ _ NC2), SP. cbn [fst]. lia. }
      assert (XB : S0 + 1 + Z.of_nat (length a) <= text + len).
      { rewrite <- LS. pose proof (span_fst_len numch (rest_at tb text S0)) as H1.
        pose proof (rest_at_len tb text S0) as H2. lia. }
      rewrite LS.
      step. step. step.
      rewrite !(unsigned_lit (S0 + 1 + Z.of_nat (length a))), !(unsigned_lit P) by lia.
      assert (LT : Z.of_nat (length (firstn (if bv_unsigned c =? 45 then 1%nat else 0%nat) (bv_unsigned c :: y)
                                      ++ bv_unsigned c2 :: a)) = S0 + 1 + Z.of_nat (length a) - P).
      { rewrite length_app, length_firstn. cbn [length]. subst S0. destruct (bv_unsigned c =? 45); lia. }
      destruct (frame_keep mm lo _ _ _ ST FR ltac:(lia)) as [STk FRk].
      apply evt_done. unfold pv_disp_post. exists P, mm. do 3 eexists. exists (Z_to_bv 64 0). do 11 eexists.
      split; [lia|]. split; [exact RP|]. split; [exact PJ|]. split; [exact WM|].
      right; right; right; right.
      exists (bv_unsigned c), y,
        (firstn (if bv_unsigned c =? 45 then 1%nat else 0%nat) (bv_unsigned c :: y) ++ bv_unsigned c2 :: a), r.
      split; [exact RC|]. split; [exact OB|].
      split; [rewrite num_tok_eq, KJ, RC2; cbv beta iota zeta; rewrite HD, NZ, SP; reflexivity|].
      split; [exact MU|].
      split; [replace (bv_unsigned sp - 48) with (bv_unsigned sp + -64 + 16) by lia; exact STk|].
      split; [replace (bv_unsigned sp - 48) with (bv_unsigned sp + -64 + 16) by lia; exact FRk|].
      split; [exact PZm|].
      rewrite LT. replace (P + (S0 + 1 + Z.of_nat (length a) - P)) with (S0 + 1 + Z.of_nat (length a)) by lia.
      reflexivity. }
    step. step.
    if_cases HZ; rewrite eqb_byte in HZ by lia.
    { apply negb_true_iff in HZ. apply K. rewrite HZ. reflexivity. }
    apply negb_false_iff in HZ.
    step. step.
    if_cases HX; [rewrite eqbm1_word in HX by lia; discriminate HX|].
    step. step.
    if_cases HE; rewrite bv_ltu_Z, !unsigned_lit in HE by lia.
    { apply negb_true_iff, Z.ltb_ge in HE. apply K. rewrite (rest_at_nil tb text (S0 + 1)) by lia. apply andb_false_r. }
    apply negb_false_iff, Z.ltb_lt in HE.
    destruct (rest_at_some tb text (S0 + 1) ltac:(lia)) as (c3 & z3 & SK3).
    pose proof (rest_at_read mm tb text (S0 + 1) c3 z3 PT ltac:(lia) SK3) as RB3.
    pose proof (rest_at_cons tb text (S0 + 1) c3 z3 ltac:(lia) SK3) as RC3.
    step. step. step. step.
    if_cases HF; rewrite ltu_digit48 in HF.
    { apply negb_true_iff in HF. apply K. rewrite RC3. cbv beta iota zeta. rewrite HF. apply andb_false_r. }
    apply negb_false_iff in HF.
    step.
    eapply pv_ret; [exact PJ | exact RP | | exact PZ | exact ST | exact FR | exact MU | exact WM | exact LO | exact SD | exact VD].
    right. exists (bv_unsigned c), y. split; [exact RC|]. split; [exact OB|].
    rewrite num_tok_eq, KJ, RC2, RC3. cbv beta iota zeta. rewrite HD, HZ, HF. reflexivity. }
  step. step. step.
  if_cases HM; rewrite eqb_byte in HM by lia.
  - apply negb_true_iff in HM.
    assert (ES : S0 = P) by (rewrite HS0, HM; apply Z.add_0_r).
    rewrite ES in K0. apply K0.
  - apply negb_false_iff in HM.
    step. step.
    if_cases HX; [rewrite eqbm1_word in HX by lia; discriminate HX|].
    step.
    assert (ES : S0 = P + 1) by (rewrite HS0, HM; reflexivity).
    rewrite ES in K0. apply K0.
Qed.

Lemma stk_store_ok : forall m lo hi a n,
  stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi -> store_ok rsegs m (wa a) n = true.
Proof.
  intros m lo hi a n (H1 & H2 & H) Ha Hn.
  replace (wa a) with (wa (a + 0)) by (rewrite Z.add_0_r; reflexivity).
  apply (wr_at_store_ok rsegs m a (Z.of_nat n) 0 n); [|lia|lia].
  split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma pv_ac : forall (rx ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m mm : word -> option byte) (q text len p d : Z) (tb : list byte) (v lo P : Z)
    (junk : list byte),
  v <> 0 ->
  pj_in_ok rsegs mm q text len P d tb -> rest_at tb text P = skip (rest_at tb text p) ->
  pj_zero rsegs m v ->
  stk rsegs mm lo (bv_unsigned sp + -64) ->
  rw_cells rsegs mm (bv_unsigned sp + -64) [CB 16 junk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(bv_unsigned sp + -64, bv_unsigned sp); (q, q + 8)] m mm -> wmono rsegs m mm ->
  lo + 64 <= bv_unsigned sp ->
  disjoint_from [(q, q + 24); (text, text + len); (v, v + 56)] (bv_unsigned sp - 64) 64 ->
  disjoint_from [(text, text + len); (q, q + 24)] v 56 ->
  evt rsegs (pv_disp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m q text len p d tb v lo)
    (MS (mkR rx (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 v) (Z_to_bv 64 q) (Z_to_bv 64 P)
             (Z_to_bv 64 (text + len)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1451c) fc None mm (seg_rom rsegs)).
Proof.
  intros rx ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mm
    q text len p d tb v lo P junk VN PJ RP PZ ST FR MU WM LO SD VD.
  pose proof (pj_in_ok_bounds rsegs _ _ _ _ _ _ _ PJ) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof PJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PT & _ & _).
  pose proof (rw_cells_bound rsegs _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof SD as SD'. pose proof VD as VD'. cbn [disjoint_from] in SD', VD'.
  pose proof (pj_zero_transport _ _ _ _ PZ MU WM ltac:(cbn [disjoint_from]; lia)) as PZm.
  step.
  if_cases HA; rewrite bv_ltu_Z, !unsigned_lit in HA by lia.
  { apply negb_true_iff, Z.ltb_ge in HA. step.
    eapply pv_ret; [exact PJ | exact RP | | exact PZ | exact ST | exact FR | exact MU | exact WM | exact LO | exact SD | exact VD].
    left. apply rest_at_nil. lia. }
  apply negb_false_iff, Z.ltb_lt in HA.
  step.
  if_cases HZ0; rewrite eqb0_word in HZ0 by lia.
  { apply Z.eqb_eq in HZ0. lia. }
  destruct (rest_at_some tb text P ltac:(lia)) as (c & rest & SK).
  pose proof (rest_at_read mm tb text P c rest PT ltac:(lia) SK) as RB.
  pose proof (rest_at_cons tb text P c rest ltac:(lia) SK) as RC.
  pose proof (byte_lt c) as CR.
  step. step. step.
  if_cases HB; rewrite lts_109 in HB.
  - apply Z.ltb_lt in HB.
    step. step.
    if_cases HN; rewrite eqb_byte in HN by lia.
    { apply Z.eqb_eq in HN.
      do 14 step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold pv_disp_post. exists P, mm. do 3 eexists.
      exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0). do 8 eexists.
      split; [lia|]. split; [exact RP|]. split; [exact PJ|]. split; [exact WM|].
      right; right; left. exists (bv_unsigned c), (rest_at tb text (P + 1)), 0x102fe, 0.
      split; [exact RC|]. split; [right; right; split; [exact HN | split; reflexivity]|].
      split; [exact MU|]. split; [exact ST|]. split; [exact PZm|]. reflexivity. }
    apply Z.eqb_neq in HN.
    step. step.
    if_cases HT; rewrite eqb_byte in HT by lia.
    { apply Z.eqb_eq in HT.
      do 13 step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold pv_disp_post. exists P, mm. do 3 eexists.
      exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0). do 8 eexists.
      split; [lia|]. split; [exact RP|]. split; [exact PJ|]. split; [exact WM|].
      right; right; left. exists (bv_unsigned c), (rest_at tb text (P + 1)), 0x1033c, 2.
      split; [exact RC|]. split; [left; split; [exact HT | split; reflexivity]|].
      split; [exact MU|]. split; [exact ST|]. split; [exact PZm|]. reflexivity. }
    apply Z.eqb_neq in HT.
    step. step.
    if_cases HO; rewrite eqb_byte in HO by lia.
    { apply negb_true_iff, Z.eqb_neq in HO.
      eapply pv_num; [exact PJ | exact RP | exact RC | unfold other_b; lia | lia | exact PZ | exact ST | exact FR
                     | exact MU | exact WM | exact LO | exact SD | exact VD]. }
    apply negb_false_iff, Z.eqb_eq in HO.
    do 12 step. release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold pv_disp_post. exists P, mm. do 3 eexists.
    exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0). do 9 eexists.
    split; [lia|]. split; [exact RP|]. split; [exact PJ|]. split; [exact WM|].
    right; left. exists true, (rest_at tb text (P + 1)).
    split; [rewrite RC, HO; reflexivity|]. split; [exact MU|]. split; [exact ST|]. split; [exact PZm|]. reflexivity.
  - apply Z.ltb_ge in HB.
    step. step.
    if_cases HQ; rewrite eqb_byte in HQ by lia.
    { apply Z.eqb_eq in HQ.
      pose proof PZm as ((VA & VST) & VZ). pose proof VST as (V0 & V1 & _).
      assert (HLv : Z.land v 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact VA).
      pose proof (stk_store_ok mm v (v + 56) v 4 VST ltac:(lia) ltac:(cbn; lia)) as HSv.
      step.
      if_cases HV; rewrite eqb0_word in HV by lia.
      { apply Z.eqb_eq in HV. lia. }
      step. step.
      if_cases HL; rewrite (unsigned_lit v), HLv in HL by lia.
      { vm_compute in HL. discriminate HL. }
      step. step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) => remember mm2 as m2 eqn:Hm2 end.
      destruct (frame_keep mm lo _ _ _ ST FR ltac:(lia)) as [STk FRk].
      apply evt_done. unfold pv_disp_post. exists P, m2. do 3 eexists. exists (Z_to_bv 64 0). do 11 eexists.
      split; [lia|]. split; [exact RP|].
      split; [subst m2; apply pj_in_ok_write_other;
              [exact PJ | lia | rewrite length_le4; lia | rewrite length_le4; cbn [disjoint_from]; lia]|].
      split; [subst m2; apply wmono_write; exact WM|].
      right; right; right; left. exists (rest_at tb text (P + 1)).
      split; [rewrite RC, HQ; reflexivity|].
      split; [subst m2; apply munch_write;
              [eapply munch_weaken; [|exact MU]; intros z Hz; cbn [outside] in Hz |- *; tauto
              | lia | rewrite length_le4; lia | cbn [inside]; rewrite length_le4; lia]|].
      split; [subst m2; replace (bv_unsigned sp - 48) with (bv_unsigned sp + -64 + 16) by lia;
              apply stk_write; [exact STk | lia | rewrite length_le4; lia]|].
      split; [subst m2; replace (bv_unsigned sp - 48) with (bv_unsigned sp + -64 + 16) by lia;
              apply rw_cells_frame; [exact FRk | lia | rewrite length_le4; lia
                                    | rewrite length_le4; cbn [cells_size csize Nat.add]; lia]|].
      split; [subst m2; split; [exact VA | apply stk_write; [exact VST | lia | rewrite length_le4; lia]]|].
      split; [subst m2; apply bytes_at_write_same; rewrite ?length_le4; lia|].
      split; [subst m2; apply bytes_at_write_other;
              [apply (pj_zero_sub rsegs mm v 4 52 VZ); lia | lia | rewrite length_le4; lia
              | rewrite length_le4, repeat_length; lia]|].
      reflexivity. }
    apply Z.eqb_neq in HQ.
    step. step.
    if_cases HK; rewrite eqb_byte in HK by lia.
    { apply Z.eqb_eq in HK.
      do 11 step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold pv_disp_post. exists P, mm. do 3 eexists.
      exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0). do 9 eexists.
      split; [lia|]. split; [exact RP|]. split; [exact PJ|]. split; [exact WM|].
      right; left. exists false, (rest_at tb text (P + 1)).
      split; [rewrite RC, HK; reflexivity|]. split; [exact MU|]. split; [exact ST|]. split; [exact PZm|]. reflexivity. }
    apply Z.eqb_neq in HK.
    step. step.
    if_cases HF; rewrite eqb_byte in HF by lia.
    { apply negb_true_iff, Z.eqb_neq in HF.
      eapply pv_num; [exact PJ | exact RP | exact RC | unfold other_b; lia | lia | exact PZ | exact ST | exact FR
                     | exact MU | exact WM | exact LO | exact SD | exact VD]. }
    apply negb_false_iff, Z.eqb_eq in HF.
    do 14 step. release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold pv_disp_post. exists P, mm. do 3 eexists.
    exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0). do 8 eexists.
    split; [lia|]. split; [exact RP|]. split; [exact PJ|]. split; [exact WM|].
    right; right; left. exists (bv_unsigned c), (rest_at tb text (P + 1)), 0x10298, 1.
    split; [exact RC|]. split; [right; left; split; [exact HF | split; reflexivity]|].
    split; [exact MU|]. split; [exact ST|]. split; [exact PZm|]. reflexivity.
Qed.

Theorem pv_disp : skip_ws_c.skip_ws_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q text len p d : Z) (tb : list byte) (v lo : Z),
  a0 = Z_to_bv 64 q -> a1 = Z_to_bv 64 v -> v <> 0 ->
  pj_in_ok rsegs m q text len p d tb ->
  pj_zero rsegs m v ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp ->
  disjoint_from [(q, q + 24); (text, text + len); (v, v + 56)] (bv_unsigned sp - 64) 64 ->
  disjoint_from [(text, text + len); (q, q + 24)] v 56 ->
  evt rsegs (pv_disp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m q text len p d tb v lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x144e4) fc None m (seg_rom rsegs)).
Proof.
  intros HSW ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    q text len p d tb v lo E0 E1 VN PJ PZ ST LO SD VD.
  unfold skip_ws_c.skip_ws_contract, skip_ws_c.SKIP_WS in HSW.
  subst a0 a1.
  pose proof (pj_in_ok_bounds rsegs m q text len p d tb PJ) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof SD as SD'. pose proof VD as VD'. cbn [disjoint_from] in SD', VD'.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  carve_frame 64%nat ST.
  do 7 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (PJx : pj_in_ok rsegs mm q text len p d tb)
      by (eapply pj_in_ok_transport; [exact PJ | exact MU | exact WM | cbn [disjoint_from]; lia | cbn [disjoint_from]; lia]);
    assert (MUw : munch [(bv_unsigned sp + -64, bv_unsigned sp); (q, q + 8)] m mm)
      by (eapply munch_weaken; [|exact MU]; intros z Hz; cbn [outside] in Hz |- *; tauto)
  end.
  do 3 step.
  eapply evt_cut.
  { eapply HSW with (q := q) (text := text) (len := len) (p := p) (d := d) (txt := tb); [reflexivity | exact PJx]. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> &
              MU2 & WM2 & _ & PJ2).
  rewrite ret_pc_even by first [lia | reflexivity].
  pose proof (rest_at_ws tb text p (proj1 B4)) as RP.
  remember (p + Z.of_nat (skip_ws_c.ws_len (skipn (Z.to_nat (p - text)) tb))) as P eqn:HP.
  pose proof PJ2 as (PB2 & _).
  pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FR2.
  assert (ST2 : stk rsegs m2 lo (bv_unsigned sp + -64))
    by (eapply stk_call; [exact ST | exact MU2 | exact WM2 | exact PB2 | rewrite length_le8; reflexivity]).
  assert (MU3 : munch [(bv_unsigned sp + -64, bv_unsigned sp); (q, q + 8)] m m2)
    by (eapply munch_trans; [exact MUw | eapply munch_weaken; [|exact MU2]; intros z Hz; cbn [outside] in Hz |- *; tauto]).
  assert (WM3 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  pose proof (pj_in_ok_bounds rsegs _ _ _ _ _ _ _ PJ2) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
  pose proof (pj_in_ok_rd_p rsegs _ _ _ _ _ _ _ PJ2) as RQ.
  pose proof (pj_in_ok_rd_end rsegs _ _ _ _ _ _ _ PJ2) as RE.
  assert (HLq : Z.land q 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact B8).
  step. step.
  if_cases HA; rewrite (unsigned_lit q), HLq in HA by lia.
  { vm_compute in HA. discriminate HA. }
  step. step.
  eapply pv_ac; [exact VN | exact PJ2 | exact RP | exact PZ | exact ST2 | exact FR2 | exact MU3 | exact WM3 | exact LO
                | exact SD | exact VD].
Qed.
