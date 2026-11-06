From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strlen_c memcpy_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require joined_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Definition NUL : byte := Z_to_bv 8 0.
Abbreviation jn := joined_c.join_need.
Abbreviation jsp := RecFacts.join_sp.

Lemma jn_fold : forall l c, fold_right (fun w acc => Z.of_nat (length w) + 1 + acc) c l = jn l + c.
Proof. unfold joined_c.join_need. induction l as [|x l IH]; intros c; cbn [fold_right]; [lia|]. rewrite IH. lia. Qed.

Lemma jn_app1 : forall l w, jn (l ++ [w]) = jn l + Z.of_nat (length w) + 1.
Proof. intros l w. unfold joined_c.join_need at 1. rewrite fold_right_app. cbn [fold_right]. rewrite jn_fold. lia. Qed.

Lemma jn_cons : forall w l, jn (w :: l) = Z.of_nat (length w) + 1 + jn l.
Proof. reflexivity. Qed.

Lemma jn_nonneg : forall l, 0 <= jn l.
Proof. induction l as [|w l IH]; [cbn; lia|]. rewrite jn_cons. lia. Qed.

Lemma jn_firstn_le : forall l k, jn (firstn k l) <= jn l.
Proof.
  induction l as [|w l IH]; intros k.
  - rewrite firstn_nil. lia.
  - destruct k as [|k].
    + pose proof (jn_nonneg (w :: l)). change (firstn 0 (w :: l)) with (@nil (list byte)). change (jn []) with 0. lia.
    + change (firstn (S k) (w :: l)) with (w :: firstn k l). rewrite !jn_cons. specialize (IH k). lia.
Qed.

Lemma firstn_S_nth : forall {X} (l : list X) k d, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l d].
Proof.
  intros X l. induction l as [|x l IH]; intros k d Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [length] in Hk.
  change (firstn (S (S k)) (x :: l)) with (x :: firstn (S k) l). rewrite (IH k d) by lia. reflexivity.
Qed.

Lemma jsp_cons2 : forall x y l, jsp (x :: y :: l) = x ++ RecFacts.SPACE :: jsp (y :: l).
Proof. reflexivity. Qed.

Lemma jsp_app1 : forall l w,
  jsp (l ++ [w]) = match l with [] => w | _ :: _ => jsp l ++ RecFacts.SPACE :: w end.
Proof.
  induction l as [|x l IH]; intros w; [reflexivity|].
  destruct l as [|y l']; [reflexivity|].
  change ((x :: y :: l') ++ [w]) with (x :: y :: (l' ++ [w])).
  rewrite jsp_cons2. change (y :: l' ++ [w]) with ((y :: l') ++ [w]). rewrite IH.
  rewrite jsp_cons2. rewrite <- app_assoc. reflexivity.
Qed.

Lemma jsp_len : forall l, l <> [] -> Z.of_nat (length (jsp l)) + 1 = jn l.
Proof.
  induction l as [|x l IH]; intros NE; [congruence|].
  destruct l as [|y l'].
  - cbn [RecFacts.join_sp]. rewrite jn_cons. cbn. lia.
  - rewrite jsp_cons2, jn_cons, length_app. cbn [length]. rewrite <- IH by discriminate. lia.
Qed.

Lemma jsp_len_le : forall l, Z.of_nat (length (jsp l)) <= jn l.
Proof. intros [|x l]; [cbn; lia|]. rewrite <- (jsp_len (x :: l)) by discriminate. lia. Qed.

Lemma sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma rd_bytes : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r in R. cbn [skipn] in R. rewrite firstn_all in R. exact R.
Qed.

Lemma rd8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof. intros m a v H. rewrite <- (length_le8 v). apply rd_bytes. exact H. Qed.

Lemma rd4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof. intros m a v H. rewrite <- (length_le4 v). apply rd_bytes. exact H. Qed.

Lemma bytes_at_munch : forall Y m m' a bs, bytes_at rsegs m a bs -> munch Y m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> outside Y x) -> bytes_at rsegs m' a bs.
Proof.
  intros Y m m' a bs (H1 & H2 & H) MU O. split; [exact H1|]. split; [exact H2|].
  intros i Hi. specialize (H i Hi). unfold mrd in *. rewrite (MU (wa (a + Z.of_nat i))); [exact H|].
  rewrite wa_unsigned by lia. apply O. lia.
Qed.

Lemma rw_cells_munch : forall Y m m' a cs, rw_cells rsegs m a cs -> munch Y m m' -> wmono rsegs m m' ->
  (forall x, a <= x < a + Z.of_nat (cells_size cs) -> outside Y x) -> rw_cells rsegs m' a cs.
Proof.
  intros Y m m' a cs [[Hwf Hb] Hw] MU WM O. split; [split; [exact Hwf|]|].
  - apply (bytes_at_munch Y m); [exact Hb | exact MU|]. rewrite cells_bytes_length by exact Hwf. exact O.
  - exact (wr_at_transport rsegs m m' a _ Hw WM).
Qed.

Lemma stk_munch : forall Y m m' lo hi, stk rsegs m lo hi -> munch Y m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside Y x) -> stk rsegs m' lo hi.
Proof. intros Y m m' lo hi S MU WM O. apply (stk_transport rsegs Y m m' lo hi S MU WM). intros x Hx. left. apply O. exact Hx. Qed.

Definition sub_out (X Y : list ivl) : Prop := forall x, outside X x -> outside Y x.

Definition apart (X : list ivl) (a n : Z) : Prop := forall x, a <= x < a + n -> outside X x.

Lemma sub_out_nil : forall X, sub_out X [].
Proof. intros X x _. exact I. Qed.

Lemma sub_out_refl : forall X, sub_out X X.
Proof. intros X x H. exact H. Qed.

Definition wrd (m : word -> option byte) (X : list ivl) (arr : Z) (wp : list Z) (ws : list (list byte)) : Prop :=
  forall k, (k < length ws)%nat ->
    bytes_at rsegs m (arr + 8 * Z.of_nat k) (le8 (Z_to_bv 64 (nth k wp 0))) /\
    apart X (arr + 8 * Z.of_nat k) 8 /\
    ~ In NUL (nth k ws []) /\
    exists slack, bytes_at rsegs m (nth k wp 0) (nth k ws [] ++ NUL :: slack) /\
      (- (nth k wp 0 + Z.of_nat (length (nth k ws [])) + 1)) mod 8 <= Z.of_nat (length slack) /\
      apart X (nth k wp 0) (Z.of_nat (length (nth k ws [] ++ NUL :: slack))).

Definition hdr (m : word -> option byte) (X : list ivl) (W arr : Z) (n : nat) : Prop :=
  bytes_at rsegs m (W + 24) (le4 (Z_to_bv 64 (Z.of_nat n))) /\ bytes_at rsegs m (W + 16) (le8 (Z_to_bv 64 arr)) /\
  apart X (W + 16) 16.

Lemma wrd_munch : forall X Y m m' arr wp ws, wrd m X arr wp ws -> munch Y m m' -> sub_out X Y -> wrd m' X arr wp ws.
Proof.
  intros X Y m m' arr wp ws H MU SB k Hk.
  destruct (H k Hk) as (B1 & D1 & NN & sl & B2 & P & D2).
  split; [| split; [exact D1|]; split; [exact NN|]; exists sl; split; [| split; [exact P | exact D2]]].
  - apply (bytes_at_munch Y m); [exact B1 | exact MU|]. rewrite length_le8. intros x Hx.
    apply SB. apply D1. lia.
  - apply (bytes_at_munch Y m); [exact B2 | exact MU|]. intros x Hx.
    apply SB. apply D2. lia.
Qed.

Lemma hdr_munch : forall X Y m m' W arr n, hdr m X W arr n -> munch Y m m' -> sub_out X Y -> hdr m' X W arr n.
Proof.
  intros X Y m m' W arr n (B1 & B2 & D) MU SB. split; [|split; [|exact D]].
  - apply (bytes_at_munch Y m); [exact B1 | exact MU|]. rewrite length_le4. intros x Hx.
    apply SB. apply D. lia.
  - apply (bytes_at_munch Y m); [exact B2 | exact MU|]. rewrite length_le8. intros x Hx.
    apply SB. apply D. lia.
Qed.

Lemma munch_nil_any : forall X m m', munch [] m m' -> munch X m m'.
Proof. intros X m m' H x _. apply H. exact I. Qed.

Lemma land7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma wrap_small : forall z, 0 <= z < 2 ^ 64 -> bv_wrap 64 z = z.
Proof. intros z Hz. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Hz. Qed.

Lemma signed_small : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite unsigned_lit by lia. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia.
Qed.

(* Simplify the unsigned/signed view of 64-bit literals whose range lia proves, then decide a branch or
   slt/sltu condition by lia. *)
Ltac zsm := repeat first [
    match goal with |- context [bv_wrap 64 ?z] => rewrite (wrap_small z) by lia end
  | match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end
  | match goal with |- context [bv_signed (Z_to_bv 64 ?z)] => rewrite (signed_small z) by lia end
  | match goal with |- context [Z.land ?x 7] => rewrite (land7 x) by lia end
  | rewrite Z.lxor_0_r | rewrite Z.lxor_0_l ].
Ltac bc := unfold c_ltu, c_eq, c_lts, bv_ltu, bv_eqb, bv_lts, bv_leu; cbn [negb]; zsm; fold_lit_ux; solve_cond_rec.
Ltac fix_ifs := unfold v_sltiu, v_sltu, v_slt, v_slti;
  repeat match goal with |- context [if ?c then _ else _] =>
    first [ replace c with true by (symmetry; bc) | replace c with false by (symmetry; bc) ]; cbv iota end.
Ltac st := step; fix_ifs.

Definition post1 (sp gp tp s0 s1 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ws : list (list byte)) (m0 : word -> option byte) (lo : Z) (cs : list cell) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x153d4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (jn ws + 1)) a1 a2 a3 a4 a5 a6 a7
                  x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x18c10) fc None m' (seg_rom rsegs)
    /\ munch [] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ rw_cells rsegs m' lo cs.

Lemma loop1 : strlen_contract -> forall (ws : list (list byte)) (j : nat)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m m0 : word -> option byte) (X : list ivl) (arr : Z) (wp : list Z) (lo : Z) (cs : list cell)
    (k : nat) (s3w : word),
  (k + S j = length ws)%nat -> s3w = Z_to_bv 64 arr ->
  wrd m X arr wp ws -> 0 < arr -> arr mod 8 = 0 -> arr + 8 * Z.of_nat (length ws) < 2 ^ 64 -> jn ws + 1 <= 2 ^ 28 ->
  rw_cells rsegs m lo cs -> munch [] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs (post1 sp gp tp s0 s1 s8 s9 s10 s11 F fc ws m0 lo cs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (jn (firstn k ws))) s3w (Z_to_bv 64 (Z.of_nat (S j))) (Z_to_bv 64 1)
             (Z_to_bv 64 (arr + 8 * Z.of_nat k)) (Z_to_bv 64 (arr + 8 * Z.of_nat k)) s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x15388) fc None m (seg_rom rsegs)).
Proof.
  intros SLEN ws j. induction j as [|j IH];
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m0 X arr wp lo cs
      k s3w HK ->  WR A0 A8 A1 NEED FR MU WM MI;
    (destruct (WR k ltac:(lia)) as (BA & DA & NN & sl & BW & PAD & DW);
     pose proof (rd8 _ _ _ BA) as RA;
     pose proof (bytes_at_bound _ _ _ _ BW) as BWB; rewrite length_app in BWB; cbn [length] in BWB;
     pose proof (jn_firstn_le ws (S k)) as JNS;
     rewrite (firstn_S_nth ws k []) in JNS by lia; rewrite jn_app1 in JNS;
     pose proof (jn_nonneg (firstn k ws)) as JN0;
     st; st; st; st; st; st; st; step; step;
     eapply evt_cut;
     [ eapply SLEN with (str := nth k ws []) (slack := sl);
       [ rewrite unsigned_lit by lia; exact BW | exact NN | rewrite unsigned_lit by lia; exact PAD | exact MI ]
     | ];
     intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
       & -> & MU1 & WM1 & MI1 & BW1);
     rewrite (ret_pc_even 86956) by (first [lia | reflexivity]);
     cbv delta [mkR];
     assert (MU01 : munch [] m0 m1) by (eapply munch_trans; [exact MU | exact MU1]);
     assert (WM01 : wmono rsegs m0 m1) by (eapply wmono_trans; [exact WM | exact WM1]);
     assert (FR1 : rw_cells rsegs m1 lo cs)
       by (apply (rw_cells_munch [] m); [exact FR | exact MU1 | exact WM1 | intros; exact I]);
     st; st; st; st; st; st).
  - assert (FS : firstn (S k) ws = ws) by (apply firstn_all2; lia).
    rewrite (firstn_S_nth ws k []) in FS by lia.
    assert (JNW : jn ws = jn (firstn k ws) + Z.of_nat (length (nth k ws [])) + 1)
      by (rewrite <- FS at 1; rewrite jn_app1; reflexivity).
    st. st. st.
    replace (Z_to_bv 64 (jn (firstn k ws) + Z.of_nat (length (nth k ws [])) + 2)) with (Z_to_bv 64 (jn ws + 1))
      by (f_equal; lia).
    apply evt_done. unfold post1.
    do 21 eexists. split; [reflexivity|].
    split; [exact MU01|]. split; [exact WM01|]. split; [exact MI1 | exact FR1].
  - replace (Z_to_bv 64 (arr + 8 * Z.of_nat k + 8)) with (Z_to_bv 64 (arr + 8 * Z.of_nat (S k))) by (f_equal; lia).
    replace (Z_to_bv 64 (jn (firstn k ws) + Z.of_nat (length (nth k ws [])) + 1)) with (Z_to_bv 64 (jn (firstn (S k) ws)))
      by (rewrite (firstn_S_nth ws k []) by lia; rewrite jn_app1; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat (S (S j)) + -1)) with (Z_to_bv 64 (Z.of_nat (S j))) by (f_equal; lia).
    eapply IH with (m := m1) (m0 := m0) (X := X) (arr := arr) (wp := wp) (lo := lo) (cs := cs) (k := S k);
      [lia | reflexivity | exact (wrd_munch X [] m m1 arr wp ws WR MU1 (sub_out_nil X)) | eassumption.. ].
Qed.

Definition mid1 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (W outp : Z) (ws : list (list byte)) (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x153d4) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 (Z_to_bv 64 outp)
                  (Z_to_bv 64 W) (Z_to_bv 64 (jn ws + 1)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x18c10) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp - 80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma run1 : strlen_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (W outp arr : Z) (wp : list Z) (ws : list (list byte)),
  stk rsegs m (bv_unsigned sp - 80) (bv_unsigned sp) -> 80 <= bv_unsigned sp ->
  hdr m [(bv_unsigned sp - 80, bv_unsigned sp)] W arr (length ws) ->
  wrd m [(bv_unsigned sp - 80, bv_unsigned sp)] arr wp ws ->
  Z.of_nat (length ws) < 2 ^ 31 -> 0 < arr -> arr mod 8 = 0 -> arr + 8 * Z.of_nat (length ws) < 2 ^ 64 ->
  0 <= W -> W mod 8 = 0 -> W + 32 <= 2 ^ 64 -> 0 <= outp < 2 ^ 64 -> jn ws + 1 <= 2 ^ 28 ->
  mem_inv rsegs m ->
  evt rsegs (mid1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W outp ws m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 W) (Z_to_bv 64 outp) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15324) fc None m (seg_rom rsegs)).
Proof.
  intros SLEN ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m W outp arr
    wp ws ST SP80 HD WR NLT A0 A8 A1 W0 W8 W1 O1 NEED MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 80%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 80%nat junk [] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 11 step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (hdr_munch _ _ m m1 _ _ _ HD MU (sub_out_refl _)) as HD1.
  pose proof (wrd_munch _ _ m m1 _ _ _ WR MU (sub_out_refl _)) as WR1.
  destruct HD1 as (H24 & H16 & HDA).
  pose proof (rd4 _ _ _ H24) as R24. pose proof (rd8 _ _ _ H16) as R16.
  st. st. st. st. st.
  rewrite (sx32_small (Z.of_nat (length ws))) by lia.
  step.
  replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) in * by lia.
  if_cases HB; zify_cond HB.
  - apply andb_false_iff in HB.
    assert (N0 : length ws = 0%nat) by (destruct HB as [HB|HB]; apply Z.ltb_ge in HB; lia).
    destruct ws as [|w ws']; [|cbn in N0; discriminate].
    step. step.
    apply evt_done. unfold mid1. do 21 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact FR].
  - assert (NPOS : (0 < length ws)%nat) by lia.
    st. st. st. st. st. st. st. st.
    replace (Z.land 18446744073709551615 (bv_unsigned (Z_to_bv 64 (Z.of_nat (length ws)))))
      with (Z.of_nat (S (Nat.pred (length ws)))).
    2:{ rewrite unsigned_lit by lia. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64).
        rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. lia. }
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (jn (firstn 0 ws))) by reflexivity.
    replace (Z_to_bv 64 arr) with (Z_to_bv 64 (arr + 8 * Z.of_nat 0)) by (f_equal; lia).
    eapply evt_mono.
    { eapply (loop1 SLEN ws (Nat.pred (length ws))) with (m0 := m1) (k := 0%nat) (arr := arr);
        [lia | f_equal; lia | eassumption.. | apply munch_refl | apply wmono_refl | eassumption]. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & x18' & x19' & x20' & x21' & x22' & x23'
      & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & FR').
    unfold mid1. do 21 eexists. split; [reflexivity|].
    split; [exact (munch_trans _ _ _ _ MU (munch_nil_any _ _ _ MU'))|].
    split; [exact (wmono_trans _ _ _ _ WM WM')|]. split; [exact MI' | exact FR'].
Qed.

Definition X2 (res N outp : Z) : list ivl := [(res, res + N); (outp, outp + 8)].

Definition dstp (m : word -> option byte) (res N : Z) (pre : list byte) : Prop :=
  exists junk, Z.of_nat (length pre + length junk) = N /\ bytes_at rsegs m res (pre ++ junk) /\ wr_at rsegs m res N.

Lemma dstp_munch : forall Y m m' res N pre, dstp m res N pre -> munch Y m m' -> wmono rsegs m m' ->
  apart Y res N -> dstp m' res N pre.
Proof.
  intros Y m m' res N pre (junk & HL & HB & HW) MU WM AP.
  exists junk. split; [exact HL|]. split.
  - apply (bytes_at_munch Y m); [exact HB | exact MU |]. intros x Hx. apply AP. rewrite length_app in Hx. lia.
  - exact (wr_at_transport rsegs m m' res N HW WM).
Qed.

Lemma dstp_store_ok : forall m res N pre, dstp m res N pre -> Z.of_nat (length pre) < N ->
  store_ok rsegs m (wa (res + Z.of_nat (length pre))) 1 = true.
Proof. intros m res N pre (junk & HL & HB & HW) LT. apply (wr_at_store_ok rsegs m res N); [exact HW | lia | lia]. Qed.

Lemma dstp_store1 : forall m res N pre bs, dstp m res N pre -> Z.of_nat (length pre) < N -> length bs = 1%nat ->
  dstp (write_to_mem m (wa (res + Z.of_nat (length pre))) bs) res N (pre ++ bs).
Proof.
  intros m res N pre bs (junk & HL & HB & HW) LT L1.
  destruct junk as [|j junk]; [rewrite Nat.add_0_r in HL; lia|].
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
  exists junk. split; [rewrite length_app, L1; cbn [length] in HL; lia|].
  split; [|apply wr_at_write; exact HW].
  apply bytes_at_app in HB as [HB1 HB2].
  rewrite <- app_assoc. apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact HB1 | lia | rewrite L1; lia | rewrite L1; lia].
  - apply bytes_at_app. split.
    + apply bytes_at_write_same; [lia | rewrite L1; lia].
    + change (j :: junk) with ([j] ++ junk) in HB2. apply bytes_at_app in HB2 as [_ HB3].
      cbn [length] in HB3. rewrite L1.
      apply bytes_at_write_other; [exact HB3 | lia | rewrite L1; lia | rewrite L1; lia].
Qed.

Lemma dstp_drop : forall m res N pre x, dstp m res N (pre ++ x) -> dstp m res N pre.
Proof.
  intros m res N pre x (junk & HL & HB & HW). exists (x ++ junk).
  rewrite length_app in HL. split; [rewrite length_app; lia|]. rewrite app_assoc. split; [exact HB | exact HW].
Qed.

Lemma dstp_cells : forall m res N pre (l : nat), dstp m res N pre -> Z.of_nat (length pre) + Z.of_nat l <= N ->
  exists junk1, rw_cells rsegs m (res + Z.of_nat (length pre)) [CB l junk1].
Proof.
  intros m res N pre l (junk & HL & HB & HW) LE.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB.
  apply bytes_at_app in HB as [_ HB2].
  exists (firstn l junk).
  assert (LJ : length (firstn l junk) = l) by (rewrite length_firstn; lia).
  split; [split|].
  - cbn. split; [exact LJ | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite <- (firstn_skipn l junk) in HB2.
    apply bytes_at_app in HB2. exact (proj1 HB2).
  - cbn [cells_size csize]. rewrite Nat.add_0_r. destruct HW as (W1 & W2 & W3). split; [lia|]. split; [lia|].
    intros i Hi. replace (res + Z.of_nat (length pre) + i) with (res + (Z.of_nat (length pre) + i)) by ring.
    apply W3. lia.
Qed.

Lemma dstp_cpy : forall m m' res N pre src, dstp m res N pre ->
  Z.of_nat (length pre) + Z.of_nat (length src) <= N ->
  munch [(res + Z.of_nat (length pre), res + Z.of_nat (length pre) + Z.of_nat (length src))] m m' ->
  wmono rsegs m m' -> bytes_at rsegs m' (res + Z.of_nat (length pre)) src ->
  dstp m' res N (pre ++ src).
Proof.
  intros m m' res N pre src (junk & HL & HB & HW) LE MU WM BS.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB.
  exists (skipn (length src) junk).
  split; [rewrite length_app, length_skipn; lia|].
  split; [|exact (wr_at_transport rsegs m m' res N HW WM)].
  apply bytes_at_app in HB as [HB1 HB2].
  rewrite <- (firstn_skipn (length src) junk) in HB2. apply bytes_at_app in HB2 as [_ HB3].
  rewrite firstn_length_le in HB3 by lia.
  rewrite <- app_assoc. apply bytes_at_app. split.
  - apply (bytes_at_munch _ m m' _ _ HB1 MU). intros x Hx. cbn. split; [lia | exact I].
  - apply bytes_at_app. split; [exact BS|].
    apply (bytes_at_munch _ m m' _ _ HB3 MU). intros x Hx. cbn. split; [lia | exact I].
Qed.

Lemma dstp_bytes : forall m res N pre, dstp m res N pre -> bytes_at rsegs m res pre.
Proof. intros m res N pre (junk & _ & HB & _). apply bytes_at_app in HB. exact (proj1 HB). Qed.

Lemma dstp_write_other : forall m res N pre a bs, dstp m res N pre -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  res + N <= a \/ a + Z.of_nat (length bs) <= res -> dstp (write_to_mem m (wa a) bs) res N pre.
Proof.
  intros m res N pre a bs (junk & HL & HB & HW) A0 A1 D. exists junk. split; [exact HL|].
  split; [|apply wr_at_write; exact HW].
  apply bytes_at_write_other; [exact HB | lia | lia |]. rewrite length_app. lia.
Qed.

Ltac mstore_norm :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?E) ?bs) _) =>
      change (write_to_mem mm (Z_to_bv 64 E) bs) with (write_to_mem mm (wa E) bs)
  end.

Lemma store_pack : forall X m0 m a bs, munch X m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  store_ok rsegs m (wa a) (length bs) = true -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  inside X a (Z.of_nat (length bs)) ->
  munch X m0 (write_to_mem m (wa a) bs) /\ wmono rsegs m0 (write_to_mem m (wa a) bs) /\
  mem_inv rsegs (write_to_mem m (wa a) bs).
Proof.
  intros X m0 m a bs MU WM MI HS A0 A1 IN. split; [apply munch_write; assumption|].
  split; [apply wmono_write; exact WM|]. apply mem_inv_store; assumption.
Qed.

Lemma le1_0 : le1 (Z_to_bv 64 0) = [NUL].
Proof. reflexivity. Qed.

Lemma le1_32 : le1 (Z_to_bv 64 32) = [RecFacts.SPACE].
Proof. reflexivity. Qed.

Lemma apart_hd_sep : forall lo hi W a n, apart ((lo, hi) :: W) a n -> lo < hi -> 0 < n -> a + n <= lo \/ hi <= a.
Proof.
  intros lo hi W a n AP LH N0.
  destruct (Z.le_gt_cases (a + n) lo) as [E|E]; [left; exact E|].
  destruct (Z.le_gt_cases hi a) as [E'|E']; [right; exact E'|].
  exfalso. pose proof (AP (Z.max a lo) ltac:(lia)) as H. cbn [outside] in H. destruct H as [H _]. apply H. lia.
Qed.

Ltac out_tac := unfold X2; cbn [outside]; repeat split; try exact I; lia.

Definition post2 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (res N outp : Z) (pre : list byte) (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (X2 res N outp) m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
    /\ bytes_at rsegs m' res (pre ++ [NUL]) /\ bytes_at rsegs m' outp (le8 (Z_to_bv 64 (Z.of_nat (length pre)))).

Definition exit2 (Pst : machine_state -> Prop) (sp gp tp s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (outp res N : Z) (pre : list byte) : Prop :=
  forall ra t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x23 x24 t3 t4 t5 t6 m,
    a0 = Z_to_bv 64 (res + Z.of_nat (length pre)) ->
    munch (X2 res N outp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> dstp m res N pre ->
    evt rsegs Pst (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 outp) x9 a0 a1 a2 a3 a4 a5 a6 a7
                         (Z_to_bv 64 res) x19 (Z_to_bv 64 (Z.of_nat (length pre))) x21 x22 x23 x24 s9 s10 s11
                         t3 t4 t5 t6)
                      F (Z_to_bv 64 0x154a8) fc None m (seg_rom rsegs)).

Lemma tail2 : forall (sp1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 gp tp s9 s10 s11 : word) F fc m0 (outp res N : Z)
    (pre : list byte),
  rw_cells rsegs m0 (bv_unsigned sp1) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wr_at rsegs m0 outp 8 -> outp mod 8 = 0 ->
  0 <= res -> Z.of_nat (length pre) + 1 <= N -> res + N <= bv_unsigned sp1 -> bv_unsigned sp1 + 80 <= outp ->
  outp + 8 <= 2 ^ 64 ->
  exit2 (post2 ra (Z_to_bv 64 (bv_unsigned sp1 + 80)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc res N outp pre m0)
        sp1 gp tp s9 s10 s11 F fc m0 outp res N pre.
Proof.
  intros sp1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 gp tp s9 s10 s11 F fc m0 outp res N pre FR0 WO0 OA R0 LP RS SO O8.
  unfold exit2. intros ra' t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x23 x24 t3 t4 t5 t6 m -> MU WM MI DP.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP.
  assert (FR : rw_cells rsegs m (bv_unsigned sp1)
                 [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_munch (X2 res N outp) m0); [exact FR0 | exact MU | exact WM |].
    intros x Hx. cbn [cells_size csize Nat.add] in Hx. out_tac. }
  assert (WO : wr_at rsegs m outp 8) by exact (wr_at_transport rsegs m0 m outp 8 WO0 WM).
  pose proof (dstp_store_ok m res N pre DP ltac:(lia)) as HS.
  clear FR0 WO0.
  st. step.
  mstore_norm. rewrite le1_0.
  destruct (store_pack (X2 res N outp) m0 m (res + Z.of_nat (length pre)) [NUL] MU WM MI HS ltac:(lia)
    ltac:(cbn [length]; lia) ltac:(unfold X2; cbn [inside length]; left; lia)) as (MU1 & WM1 & MI1).
  assert (DP1 : dstp (write_to_mem m (wa (res + Z.of_nat (length pre))) [NUL]) res N (pre ++ [NUL]))
    by (apply dstp_store1; [exact DP | lia | reflexivity]).
  assert (FR1 : rw_cells rsegs (write_to_mem m (wa (res + Z.of_nat (length pre))) [NUL]) (bv_unsigned sp1)
                  [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    by (apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]).
  pose proof (wr_at_write rsegs m outp 8 (wa (res + Z.of_nat (length pre))) [NUL] WO) as WO1.
  remember (write_to_mem m (wa (res + Z.of_nat (length pre))) [NUL]) as m1 eqn:Em1.
  clear Em1 MU WM MI DP FR WO HS.
  pose proof (wr_at_store_ok rsegs m1 outp 8 0 8 WO1 ltac:(lia) ltac:(lia)) as HS2. rewrite Z.add_0_r in HS2.
  st. step.
  mstore_norm.
  destruct (store_pack (X2 res N outp) m0 m1 outp (le8 (Z_to_bv 64 (Z.of_nat (length pre)))) MU1 WM1 MI1 HS2 ltac:(lia)
    ltac:(rewrite length_le8; lia) ltac:(unfold X2; cbn [inside]; rewrite length_le8; right; left; lia))
    as (MU2 & WM2 & MI2).
  assert (DP2 : dstp (write_to_mem m1 (wa outp) (le8 (Z_to_bv 64 (Z.of_nat (length pre))))) res N (pre ++ [NUL]))
    by (apply dstp_write_other; [exact DP1 | lia | rewrite length_le8; lia | rewrite length_le8; lia]).
  assert (FR2 : rw_cells rsegs (write_to_mem m1 (wa outp) (le8 (Z_to_bv 64 (Z.of_nat (length pre)))))
                  (bv_unsigned sp1) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    by (apply rw_cells_frame; [exact FR1 | lia | rewrite length_le8; lia |
                               cbn [cells_size csize Nat.add]; rewrite length_le8; lia]).
  assert (BO : bytes_at rsegs (write_to_mem m1 (wa outp) (le8 (Z_to_bv 64 (Z.of_nat (length pre))))) outp
                 (le8 (Z_to_bv 64 (Z.of_nat (length pre)))))
    by (apply bytes_at_write_same; [lia | rewrite length_le8; lia]).
  remember (write_to_mem m1 (wa outp) (le8 (Z_to_bv 64 (Z.of_nat (length pre))))) as m2 eqn:Em2.
  clear Em2 MU1 WM1 MI1 DP1 FR1 WO1 HS2.
  do 13 step.
  apply evt_done. unfold post2. do 15 eexists. split; [reflexivity|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact (dstp_bytes _ _ _ _ DP2) | exact BO].
Qed.

Definition stat2 (m0 : word -> option byte) (W arr outp res N : Z) (wp : list Z) (ws : list (list byte)) : Prop :=
  hdr m0 (X2 res N outp) W arr (length ws) /\ wrd m0 (X2 res N outp) arr wp ws /\
  Z.of_nat (length ws) < 2 ^ 31 /\ 0 < arr /\ arr mod 8 = 0 /\ arr + 8 * Z.of_nat (length ws) < 2 ^ 64 /\
  0 <= W /\ W + 32 <= 2 ^ 64 /\ 0 <= res /\ res + N < 2 ^ 64 /\ N = jn ws + 1 /\ jn ws + 1 <= 2 ^ 28.

Definition head2 (Pst : machine_state -> Prop) (sp gp tp s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (W outp res N : Z) (ws : list (list byte)) (k : nat) : Prop :=
  forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 m,
    munch (X2 res N outp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> dstp m res N (jsp (firstn k ws)) ->
    evt rsegs Pst (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 outp) (Z_to_bv 64 W) a0 a1 a2 a3 a4 a5 a6 a7
                         (Z_to_bv 64 res) x19 (Z_to_bv 64 (Z.of_nat (length (jsp (firstn k ws)))))
                         (Z_to_bv 64 (8 * Z.of_nat k)) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (2 ^ 64 - 1 - res))
                         (Z_to_bv 64 32) s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x153fc) fc None m (seg_rom rsegs)).

Lemma jsp_step : forall ws k, (k < length ws)%nat ->
  jsp (firstn (S k) ws) =
  match k with O => nth k ws [] | S _ => jsp (firstn k ws) ++ RecFacts.SPACE :: nth k ws [] end.
Proof.
  intros ws k Hk. rewrite (firstn_S_nth ws k []) by exact Hk. rewrite jsp_app1.
  destruct k as [|k]; [reflexivity|].
  destruct (firstn (S k) ws) as [|x l] eqn:E; [|reflexivity].
  exfalso. apply (f_equal (@length _)) in E. rewrite length_firstn in E. cbn [length] in E. lia.
Qed.

Lemma lxor_ones64 : forall a, 0 <= a < 2 ^ 64 -> Z.lxor a (Z.ones 64) = Z.ones 64 - a.
Proof.
  intros a Ha.
  assert (L : Z.land a (Z.lxor a (Z.ones 64)) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n 64) as [Hl|Hg].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit a n); reflexivity.
    - assert (T : Z.testbit a n = false)
        by (rewrite <- (Z.mod_small a (2 ^ 64)) by lia; apply Z.mod_pow2_bits_high; lia).
      rewrite T. reflexivity. }
  pose proof (Z.add_nocarry_lxor a (Z.lxor a (Z.ones 64)) L) as E.
  rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in E. lia.
Qed.

Lemma copy2 : memcpy_contract -> forall (Pst : machine_state -> Prop) sp gp tp s9 s10 s11 F fc m0 W arr outp res N wp ws
    (k : nat) (pre : list byte) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m,
  stat2 m0 W arr outp res N wp ws -> (k < length ws)%nat ->
  pre ++ nth k ws [] = jsp (firstn (S k) ws) ->
  munch (X2 res N outp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> dstp m res N pre ->
  ((S k < length ws)%nat -> head2 Pst sp gp tp s9 s10 s11 F fc m0 W outp res N ws (S k)) ->
  ((S k = length ws)%nat -> exit2 Pst sp gp tp s9 s10 s11 F fc m0 outp res N (jsp ws)) ->
  evt rsegs Pst (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 outp) (Z_to_bv 64 W) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 res) (Z_to_bv 64 (Z.of_nat (length (nth k ws [])))) (Z_to_bv 64 (Z.of_nat (length pre)))
                       (Z_to_bv 64 (8 * Z.of_nat k)) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (2 ^ 64 - 1 - res))
                       (Z_to_bv 64 32) s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x15444) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY Pst sp gp tp s9 s10 s11 F fc m0 W arr outp res N wp ws k pre ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
    t3 t4 t5 t6 m ST HK PRE MU WM MI DP NEXT EXIT.
  unfold head2 in NEXT. unfold exit2 in EXIT.
  pose proof ST as (HD & WR & NLT & A0 & A8 & A1 & W0 & W1 & R0 & R1 & EN & NEED).
  pose proof (wrd_munch _ _ m0 m _ _ _ WR MU (sub_out_refl _)) as WR1.
  destruct (WR1 k HK) as (BA & DA & NN & sl & BW & PAD & DW).
  pose proof (rd8 _ _ _ BA) as RA.
  pose proof (hdr_munch _ _ m0 m _ _ _ HD MU (sub_out_refl _)) as (H24a & H16a & HDAa).
  pose proof (rd8 _ _ _ H16a) as R16.
  pose proof (bytes_at_bound _ _ _ _ BW) as BWB. rewrite length_app in BWB. cbn [length] in BWB.
  assert (LP : Z.of_nat (length pre) + Z.of_nat (length (nth k ws [])) = Z.of_nat (length (jsp (firstn (S k) ws))))
    by (rewrite <- PRE, length_app; lia).
  pose proof (jsp_len_le (firstn (S k) ws)) as JL. pose proof (jn_firstn_le ws (S k)) as JF.
  destruct (dstp_cells m res N pre (length (nth k ws [])) DP ltac:(lia)) as [junk1 DC].
  assert (SRC : bytes_at rsegs m (nth k wp 0) (nth k ws [])) by (apply bytes_at_app in BW; exact (proj1 BW)).
  assert (SEP : nth k wp 0 + Z.of_nat (length (nth k ws [])) <= res + Z.of_nat (length pre) \/
                res + Z.of_nat (length pre) + Z.of_nat (length (nth k ws [])) <= nth k wp 0).
  { destruct (Nat.eq_dec (length (nth k ws [])) 0) as [Z0|Z0]; [rewrite Z0; lia|].
    assert (AP : apart (X2 res N outp) (nth k wp 0) (Z.of_nat (length (nth k ws [])))).
    { intros x Hx. apply DW. rewrite length_app. cbn [length]. lia. }
    destruct (apart_hd_sep res (res + N) [(outp, outp + 8)] _ _ AP ltac:(lia) ltac:(lia)) as [S|S]; lia. }
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
  do 15 st.
  eapply evt_cut.
  { eapply MCPY with (src := nth k ws []) (junk := junk1).
    - rewrite unsigned_lit by lia. exact SRC.
    - rewrite unsigned_lit by lia. rewrite Nat2Z.id. reflexivity.
    - rewrite !unsigned_lit by lia. rewrite Nat2Z.id. exact DC.
    - rewrite !unsigned_lit by lia. lia.
    - exact MI. }
  intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1
    & DST1 & SRC1).
  rewrite (ret_pc_even 87168) by (first [lia | reflexivity]).
  cbv delta [mkR].
  rewrite !unsigned_lit in MU1, DST1 by lia. rewrite Nat2Z.id in DST1.
  assert (DP1 : dstp m1 res N (pre ++ nth k ws [])).
  { apply (dstp_cpy m m1 res N pre (nth k ws []) DP ltac:(lia) MU1 WM1).
    destruct DST1 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  rewrite PRE in DP1.
  assert (MU01 : munch (X2 res N outp) m0 m1).
  { apply (munch_trans _ m0 m m1 MU). refine (munch_weaken _ _ m m1 _ MU1).
    intros x Hx. unfold X2 in Hx. cbn [outside] in Hx |- *. split; [lia | exact I]. }
  assert (WM01 : wmono rsegs m0 m1) by exact (wmono_trans _ _ _ _ WM WM1).
  pose proof (hdr_munch _ _ m0 m1 _ _ _ HD MU01 (sub_out_refl _)) as (H24 & H16 & HDA).
  pose proof (rd4 _ _ _ H24) as R24.
  clear MU WM MI DP DC SRC1 DST1 MU1 WM1 WR1 BA DA BW RA R16 H24a H16a HDAa.
  step.
  rewrite (sx32_small (Z.of_nat (length ws))) by lia.
  step. step. step. step.
  if_cases HB; zify_cond HB; rewrite !signed_small in HB by lia.
  - replace (Z_to_bv 64 (8 * Z.of_nat k + 8)) with (Z_to_bv 64 (8 * Z.of_nat (S k))) by (f_equal; lia).
    replace (Z_to_bv 64 (Z.of_nat k + 1)) with (Z_to_bv 64 (Z.of_nat (S k))) by (f_equal; lia).
    replace (Z_to_bv 64 (Z.of_nat (length pre) + Z.of_nat (length (nth k ws []))))
      with (Z_to_bv 64 (Z.of_nat (length (jsp (firstn (S k) ws))))) by (f_equal; lia).
    eapply (NEXT ltac:(lia)); [exact MU01 | exact WM01 | exact MI1 | exact DP1].
  - assert (SK : S k = length ws) by lia.
    assert (FA : firstn (S k) ws = ws) by (apply firstn_all2; lia).
    rewrite FA in DP1, LP.
    replace (Z_to_bv 64 (Z.of_nat (length pre) + Z.of_nat (length (nth k ws []))))
      with (Z_to_bv 64 (Z.of_nat (length (jsp ws)))) by (f_equal; lia).
    pose proof (jsp_len_le ws) as JLW.
    st. step. step.
    eapply (EXIT SK); [first [reflexivity | f_equal; lia] | exact MU01 | exact WM01 | exact MI1 | exact DP1].
Qed.

Lemma iter2 : strlen_contract -> memcpy_contract -> forall (Pst : machine_state -> Prop) sp gp tp s9 s10 s11 F fc m0
    W arr outp res N wp ws (k : nat),
  stat2 m0 W arr outp res N wp ws -> (k < length ws)%nat ->
  ((S k < length ws)%nat -> head2 Pst sp gp tp s9 s10 s11 F fc m0 W outp res N ws (S k)) ->
  ((S k = length ws)%nat -> exit2 Pst sp gp tp s9 s10 s11 F fc m0 outp res N (jsp ws)) ->
  head2 Pst sp gp tp s9 s10 s11 F fc m0 W outp res N ws k.
Proof.
  intros SLEN MCPY Pst sp gp tp s9 s10 s11 F fc m0 W arr outp res N wp ws k ST HK NEXT EXIT.
  unfold head2 at 1.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 m MU WM MI DP.
  pose proof ST as (HD & WR & NLT & A0 & A8 & A1 & W0 & W1 & R0 & R1 & EN & NEED).
  pose proof (wrd_munch _ _ m0 m _ _ _ WR MU (sub_out_refl _)) as WR1.
  pose proof (hdr_munch _ _ m0 m _ _ _ HD MU (sub_out_refl _)) as (H24 & H16 & HDA).
  pose proof (rd8 _ _ _ H16) as R16.
  destruct (WR1 k HK) as (BA & DA & NN & sl & BW & PAD & DW).
  pose proof (rd8 _ _ _ BA) as RA.
  pose proof (bytes_at_bound _ _ _ _ BW) as BWB. rewrite length_app in BWB. cbn [length] in BWB.
  pose proof (jn_firstn_le ws (S k)) as JNS.
  rewrite (firstn_S_nth ws k []) in JNS by lia. rewrite jn_app1 in JNS.
  pose proof (jn_nonneg (firstn k ws)) as JN0.
  pose proof (jsp_len_le (firstn k ws)) as JL0.
  do 12 st.
  eapply evt_cut.
  { eapply SLEN with (str := nth k ws []) (slack := sl);
      [ rewrite unsigned_lit by lia; exact BW | exact NN | rewrite unsigned_lit by lia; exact PAD | exact MI ]. }
  intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & BW1).
  rewrite (ret_pc_even 87084) by (first [lia | reflexivity]).
  cbv delta [mkR].
  assert (MU01 : munch (X2 res N outp) m0 m1) by exact (munch_trans _ _ _ _ MU (munch_nil_any _ _ _ MU1)).
  assert (WM01 : wmono rsegs m0 m1) by exact (wmono_trans _ _ _ _ WM WM1).
  assert (DP1 : dstp m1 res N (jsp (firstn k ws)))
    by (apply (dstp_munch [] m); [exact DP | exact MU1 | exact WM1 | intros x _; exact I]).
  clear MU WM MI DP MU1 WM1 BW1 WR1 BA DA BW H24 H16 HDA R16 RA.
  step. step.
  if_cases HB; zify_cond HB; rewrite ?unsigned_lit in HB by lia.
  - assert (K0 : k = 0%nat) by lia.
    eapply (copy2 MCPY Pst sp gp tp s9 s10 s11 F fc m0 W arr outp res N wp ws k (jsp (firstn k ws)));
      [exact ST | exact HK | | exact MU01 | exact WM01 | exact MI1 | exact DP1 | exact NEXT | exact EXIT].
    subst k. rewrite (jsp_step ws 0 HK). reflexivity.
  - assert (KP : (0 < k)%nat) by lia.
    st. step. step.
    pose proof (dstp_store_ok m1 res N _ DP1 ltac:(lia)) as HS.
    step.
    mstore_norm. rewrite le1_32.
    destruct (store_pack (X2 res N outp) m0 m1 (res + Z.of_nat (length (jsp (firstn k ws)))) [RecFacts.SPACE]
      MU01 WM01 MI1 HS ltac:(lia) ltac:(cbn [length]; lia) ltac:(unfold X2; cbn [inside length]; left; lia))
      as (MU2 & WM2 & MI2).
    assert (DP2 : dstp (write_to_mem m1 (wa (res + Z.of_nat (length (jsp (firstn k ws))))) [RecFacts.SPACE]) res N
                    (jsp (firstn k ws) ++ [RecFacts.SPACE]))
      by (apply dstp_store1; [exact DP1 | lia | reflexivity]).
    remember (write_to_mem m1 (wa (res + Z.of_nat (length (jsp (firstn k ws))))) [RecFacts.SPACE]) as m2 eqn:Em2.
    clear Em2 MU01 WM01 MI1 DP1 HS.
    replace (Z_to_bv 64 (Z.of_nat (length (jsp (firstn k ws))) + 1))
      with (Z_to_bv 64 (Z.of_nat (length (jsp (firstn k ws) ++ [RecFacts.SPACE]))))
      by (f_equal; rewrite length_app; cbn [length]; lia).
    eapply (copy2 MCPY Pst sp gp tp s9 s10 s11 F fc m0 W arr outp res N wp ws k
              (jsp (firstn k ws) ++ [RecFacts.SPACE]));
      [exact ST | exact HK | | exact MU2 | exact WM2 | exact MI2 | exact DP2 | exact NEXT | exact EXIT].
    rewrite (jsp_step ws k HK). destruct k as [|k']; [lia|]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma loop2 : strlen_contract -> memcpy_contract -> forall (Pst : machine_state -> Prop) sp gp tp s9 s10 s11 F fc m0
    W arr outp res N wp ws,
  stat2 m0 W arr outp res N wp ws ->
  exit2 Pst sp gp tp s9 s10 s11 F fc m0 outp res N (jsp ws) ->
  forall j k, (k + S j = length ws)%nat -> head2 Pst sp gp tp s9 s10 s11 F fc m0 W outp res N ws k.
Proof.
  intros SLEN MCPY Pst sp gp tp s9 s10 s11 F fc m0 W arr outp res N wp ws ST EXIT j.
  induction j as [|j IH]; intros k HK.
  - apply (iter2 SLEN MCPY Pst sp gp tp s9 s10 s11 F fc m0 W arr outp res N wp ws k ST ltac:(lia));
      [intros H; exfalso; lia | intros _; exact EXIT].
  - apply (iter2 SLEN MCPY Pst sp gp tp s9 s10 s11 F fc m0 W arr outp res N wp ws k ST ltac:(lia));
      [intros _; apply IH; lia | intros H; exfalso; lia].
Qed.

Lemma run2 : strlen_contract -> memcpy_contract -> forall ra (sp1 : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7
    x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6 F fc m (rv s0 s1 s2 s3 s4 s5 s6 s7 s8 : word)
    (W arr outp res : Z) wp ws,
  rw_cells rsegs m (bv_unsigned sp1) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rv] ->
  wr_at rsegs m outp 8 -> outp mod 8 = 0 ->
  stat2 m W arr outp res (jn ws + 1) wp ws ->
  dstp m res (jn ws + 1) [] ->
  0 < res -> res + (jn ws + 1) <= bv_unsigned sp1 -> bv_unsigned sp1 + 80 <= outp -> outp + 8 <= 2 ^ 64 ->
  mem_inv rsegs m ->
  evt rsegs (post2 rv (Z_to_bv 64 (bv_unsigned sp1 + 80)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               res (jn ws + 1) outp (jsp ws) m)
    (MS (mkR ra sp1 gp tp t0 t1 t2 (Z_to_bv 64 outp) (Z_to_bv 64 W) (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x153d4) fc None m (seg_rom rsegs)).
Proof.
  intros SLEN MCPY ra sp1 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6 F fc
    m rv s0 s1 s2 s3 s4 s5 s6 s7 s8 W arr outp res wp ws FR WO OA ST DP R0 RS SO O8 MI.
  pose proof ST as (HD & WR & NLT & A0 & A8 & A1 & W0 & W1 & R0' & R1 & EN & NEED).
  pose proof (munch_refl (X2 res (jn ws + 1) outp) m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (jn_nonneg ws) as JN.
  pose proof (jsp_len_le ws) as JL.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP.
  pose proof (tail2 sp1 rv s0 s1 s2 s3 s4 s5 s6 s7 s8 gp tp s9 s10 s11 F fc m outp res (jn ws + 1) (jsp ws)
                FR WO OA ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as EXIT.
  st. step.
  pose proof (dstp_store_ok m res _ [] DP ltac:(cbn [length Z.of_nat]; lia)) as HS.
  cbn [length Z.of_nat] in HS. rewrite Z.add_0_r in HS.
  step.
  mstore_norm. rewrite le1_0.
  destruct (store_pack (X2 res (jn ws + 1) outp) m m res [NUL] MU WM MI HS ltac:(lia) ltac:(cbn [length]; lia)
    ltac:(unfold X2; cbn [inside length]; left; lia)) as (MU1 & WM1 & MI1).
  pose proof (dstp_store1 m res (jn ws + 1) [] [NUL] DP ltac:(cbn [length Z.of_nat]; lia) eq_refl) as DP1.
  cbn [length Z.of_nat] in DP1. rewrite Z.add_0_r in DP1.
  apply (dstp_drop _ _ _ [] [NUL]) in DP1.
  remember (write_to_mem m (wa res) [NUL]) as m1 eqn:Em1.
  clear Em1 HS.
  pose proof (hdr_munch _ _ m m1 _ _ _ HD MU1 (sub_out_refl _)) as (H24 & _ & _).
  pose proof (rd4 _ _ _ H24) as R24.
  step.
  rewrite (sx32_small (Z.of_nat (length ws))) by lia.
  step.
  if_cases HB2; unfold bv_lts in HB2; rewrite !signed_small in HB2 by lia.
  - apply Bool.negb_true_iff, Z.ltb_ge in HB2.
    assert (N0 : length ws = 0%nat) by lia.
    destruct ws as [|w ws']; [|cbn in N0; discriminate].
    step. step.
    unfold exit2 in EXIT.
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (Z.of_nat (length (jsp [])))) by reflexivity.
    eapply EXIT; [f_equal; cbn; lia | exact MU1 | exact WM1 | exact MI1 | exact DP1].
  - apply Bool.negb_false_iff, Z.ltb_lt in HB2.
    step. step. step. step. step.
    replace (Z.lxor (bv_unsigned (Z_to_bv 64 res)) 18446744073709551615) with (2 ^ 64 - 1 - res).
    2:{ rewrite unsigned_lit by lia. change 18446744073709551615 with (Z.ones 64).
        rewrite lxor_ones64 by lia. rewrite Z.ones_equiv. lia. }
    pose proof (loop2 SLEN MCPY _ sp1 gp tp s9 s10 s11 F fc m W arr outp res (jn ws + 1) wp ws ST EXIT
                  (Nat.pred (length ws)) 0 ltac:(lia)) as L.
    unfold head2 in L.
    eapply L; [exact MU1 | exact WM1 | exact MI1 | exact DP1].
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsB.
Local Open Scope Z_scope.

Lemma ceil8 : forall x, x + (- x) mod 8 = 8 * ((x + 7) / 8).
Proof. intros x. Z.div_mod_to_equations. lia. Qed.

Lemma ceil8_le : forall x c, x <= c -> c mod 8 = 0 -> 8 * ((x + 7) / 8) <= c.
Proof. intros x c H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma ceil8_ge : forall x, x <= 8 * ((x + 7) / 8).
Proof. intros x. Z.div_mod_to_equations. lia. Qed.

Lemma ceil8_mono : forall x y, x <= y -> 8 * ((x + 7) / 8) <= 8 * ((y + 7) / 8).
Proof. intros x y H. apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.div_le_mono; lia. Qed.

Lemma wrd_build : forall (m : word -> option byte) (X : list ivl) (bl : list (Z * Z)) arr wp ws,
  (forall q sz, In (q, sz) bl -> 0 <= q /\ 8 * ((q + sz + 7) / 8) <= 2 ^ 64) ->
  (forall q sz x, In (q, sz) bl -> q <= x < 8 * ((q + sz + 7) / 8) -> present m x /\ outside X x) ->
  (exists q sz, In (q, sz) bl /\ q <= arr /\ arr + 8 * Z.of_nat (length ws) <= q + sz) ->
  (forall k, (k < length ws)%nat -> exists q sz, In (q, sz) bl /\ q <= nth k wp 0 /\
       nth k wp 0 + (Z.of_nat (length (nth k ws [])) + 1) <= q + sz) ->
  (forall k, (k < length ws)%nat ->
     bytes_at rsegs m (arr + 8 * Z.of_nat k) (le8 (Z_to_bv 64 (nth k wp 0))) /\
     ~ In NUL (nth k ws []) /\ bytes_at rsegs m (nth k wp 0) (nth k ws [] ++ [NUL])) ->
  wrd m X arr wp ws.
Proof.
  intros m X bl arr wp ws RNG PX (qa & sa & Ia & Qa1 & Qa2) WB WK k Hk.
  destruct (WK k Hk) as (BA & NN & BW).
  pose proof (ceil8_ge (qa + sa)) as CA.
  split; [exact BA|]. split.
  { intros x Hx. refine (proj2 (PX qa sa x Ia _)). lia. }
  split; [exact NN|].
  destruct (WB k Hk) as (q & sz & Iq & Q1 & Q2).
  pose proof (RNG _ _ Iq) as (Rq1 & Rq2).
  pose proof (bytes_at_bound _ _ _ _ BW) as BWB. rewrite length_app in BWB. cbn [length] in BWB.
  pose proof (ceil8 (nth k wp 0 + Z.of_nat (length (nth k ws [])) + 1)) as CE.
  pose proof (Z.mod_pos_bound (- (nth k wp 0 + Z.of_nat (length (nth k ws [])) + 1)) 8 ltac:(lia)) as SB.
  pose proof (ceil8_mono (nth k wp 0 + Z.of_nat (length (nth k ws [])) + 1) (q + sz) ltac:(lia)) as MO.
  destruct (present_rw_cells rsegs m (nth k wp 0 + Z.of_nat (length (nth k ws [])) + 1)
              (Z.to_nat ((- (nth k wp 0 + Z.of_nat (length (nth k ws [])) + 1)) mod 8)) ltac:(lia) ltac:(lia))
    as [sl [[Hwf Hb] _]].
  { intros i Hi. refine (proj1 (PX q sz _ Iq _)). lia. }
  cbn in Hwf. destruct Hwf as [Lsl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  exists sl. split; [|split].
  - replace (nth k ws [] ++ NUL :: sl) with ((nth k ws [] ++ [NUL]) ++ sl) by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BW|]. rewrite length_app. cbn [length].
    replace (nth k wp 0 + Z.of_nat (length (nth k ws []) + 1))
      with (nth k wp 0 + Z.of_nat (length (nth k ws [])) + 1) by lia.
    exact Hb.
  - rewrite Lsl. lia.
  - intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. refine (proj2 (PX q sz x Iq _)). lia.
Qed.

Lemma hdr_norm : forall m X W arr n, ro_agree rsegs m -> hdr m X W arr n -> hdr (normalize rsegs m) X W arr n.
Proof.
  intros m X W arr n RO (B1 & B2 & D). split; [exact (bytes_at_normalize rsegs m _ _ RO B1)|].
  split; [exact (bytes_at_normalize rsegs m _ _ RO B2) | exact D].
Qed.

Lemma wrd_norm : forall m X arr wp ws, ro_agree rsegs m -> wrd m X arr wp ws -> wrd (normalize rsegs m) X arr wp ws.
Proof.
  intros m X arr wp ws RO H k Hk. destruct (H k Hk) as (B1 & D1 & NN & sl & B2 & P & D2).
  split; [exact (bytes_at_normalize rsegs m _ _ RO B1)|]. split; [exact D1|]. split; [exact NN|].
  exists sl. split; [exact (bytes_at_normalize rsegs m _ _ RO B2)|]. split; [exact P | exact D2].
Qed.

Lemma dstp_norm : forall m res N pre, ro_agree rsegs m -> dstp m res N pre ->
  (forall i, 0 <= i < N -> ro_addr rsegs (wa (res + i)) = false) -> dstp (normalize rsegs m) res N pre.
Proof.
  intros m res N pre RO (junk & HL & HB & HW) Hro. exists junk. split; [exact HL|].
  split; [exact (bytes_at_normalize rsegs m _ _ RO HB)|].
  exact (wr_at_norm rsegs m _ res N (mem_rel_normalize rsegs m RO) HW Hro).
Qed.

Section J.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALLOC_PC : ms_malloc B = 0x18c10.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis MALLOC : malloc_contract B API.
Hypothesis BSP : block_slack_present B API.
Hypothesis SLEN : strlen_contract.
Hypothesis MCPY : memcpy_contract.

Lemma bytes_of_le : forall m a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> VerbsB.le_at B m a bs ->
  bytes_at rsegs m a bs.
Proof using SEGS.
  intros m a bs H1 H2 H. apply bytes_at_of_mbyte; [lia | lia |]. intros i Hi.
  unfold VerbsB.le_at, blk_data in H. rewrite <- SEGS.
  specialize (H (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id in H. exact H.
Qed.

Lemma le_of_bytes : forall m a bs, bytes_at rsegs m a bs -> VerbsB.le_at B m a bs.
Proof using SEGS.
  intros m a bs H i Hi. rewrite SEGS. replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia.
  apply (mbyte_of_bytes_at _ _ _ _ _ H). lia.
Qed.

Lemma block_range : forall L A mem md q k, aa_MR API L A mem md -> In (q, k) (blocks L A) ->
  4096 <= q /\ q + k <= alloc_ceiling.
Proof.
  intros L A mem md q k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbn in E. injection E as <- <-. exact (mr_blocks_range B _ (aa_laws API) L A mem md p k' HM Hp).
Qed.

Lemma le_at_kept : forall L A m m' a bs,
  (forall q sz i, In (q, sz) (blocks L A) -> 0 <= i < sz -> mbyte (ms_segs B) m' (q + i) = mbyte (ms_segs B) m (q + i)) ->
  (exists q sz, In (q, sz) (blocks L A) /\ q <= a /\ a + Z.of_nat (length bs) <= q + sz) ->
  VerbsB.le_at B m a bs -> VerbsB.le_at B m' a bs.
Proof.
  intros L A m m' a bs KP (q & sz & Iq & H1 & H2) H.
  apply (blk_data_kept B m m' a bs); [|exact H]. intros i Hi.
  replace (a + i) with (q + (a + i - q)) by ring. apply (KP q sz); [exact Iq | lia].
Qed.

Theorem joined_holds : joined_c.joined_contract B API.
Proof using SEGS MALLOC_PC ERRNO_LOW MALLOC BSP SLEN MCPY.
  unfold joined_c.joined_contract.
  intros L A regs mem md b W arr outp wp ws PRE RO AW AO WV WPL W8 A8 SPW W32 NEED SPO O8 ODIS OWR OAL ONO RES ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof MALLOC as MAL. unfold malloc_contract in MAL. rewrite SEGS, MALLOC_PC in MAL.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold joined_c.JOINED_FRAME in *. change ALLOC_STACK with 8192 in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  destruct WV as (LWP & NLT & L24 & L16 & WK).
  pose proof WPL as (ARRB & WB).
  rewrite SEGS in RO, HWS, HERR, OWR.
  pose proof (jn_nonneg ws) as JN. pose proof (jsp_len_le ws) as JL.
  pose proof (ceil8_le alloc_ceiling alloc_ceiling ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as AC8.
  pose proof ARRB as (qa & sa & Ia & Qa1 & Qa2).
  pose proof (block_range L A mem md _ _ HMR Ia) as (Ra1 & Ra2).
  assert (BR0 : forall q sz, In (q, sz) (blocks L A) -> 0 <= q /\ 8 * ((q + sz + 7) / 8) <= alloc_ceiling).
  { intros q sz Hin. destruct (block_range L A mem md q sz HMR Hin) as [H1 H2].
    pose proof (ceil8_le (q + sz) alloc_ceiling H2 ltac:(Z.div_mod_to_equations; lia)). lia. }
  assert (PR0 : forall q sz x, In (q, sz) (blocks L A) -> q <= x < 8 * ((q + sz + 7) / 8) -> present mem x).
  { intros q sz x Hin Hx. destruct (Z_lt_ge_dec x (q + sz)) as [D|D].
    - replace x with (q + (x - q)) by ring.
      exact (proj1 (block_facts B _ LAWS _ _ _ _ _ _ (x - q) HMR Hin ltac:(lia))).
    - exact (BSP L A mem md q sz x HMR Hin ltac:(lia)). }
  assert (WBOUND : forall k, (k < length ws)%nat -> 4096 <= nth k wp 0 /\
            nth k wp 0 + (Z.of_nat (length (nth k ws [])) + 1) <= alloc_ceiling).
  { intros k Hk. destruct (WB k Hk) as (q & sz & Iq & H1 & H2). destruct (block_range L A mem md q sz HMR Iq). lia. }
  assert (HD0 : hdr mem [(bv_unsigned sp - 80, bv_unsigned sp)] W arr (length ws)).
  { split; [|split].
    - apply bytes_of_le; [lia | rewrite length_le4; lia | exact L24].
    - apply bytes_of_le; [lia | rewrite length_le8; lia | exact L16].
    - intros x Hx. cbn [outside]. split; [lia | exact I]. }
  assert (WR0 : wrd mem [(bv_unsigned sp - 80, bv_unsigned sp)] arr wp ws).
  { apply (wrd_build mem _ (blocks L A)).
    - intros q sz Hin. destruct (BR0 q sz Hin). lia.
    - intros q sz x Hin Hx. split; [exact (PR0 q sz x Hin Hx)|]. destruct (BR0 q sz Hin).
      cbn [outside]. split; [lia | exact I].
    - exact ARRB.
    - exact WB.
    - intros k Hk. destruct (WK k Hk) as (LA & NN & LW). destruct (WBOUND k Hk) as [P1 P2].
      split; [|split].
      + apply bytes_of_le; [lia | rewrite length_le8; lia | exact LA].
      + exact NN.
      + apply bytes_of_le; [lia | rewrite length_app; cbn [length]; lia | exact LW]. }
  assert (ST : stk rsegs mem (bv_unsigned sp - 80) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (Wa : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact Wa|].
    destruct (writable_hi_present mem a ltac:(lia) Wa) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 W) by exact AW. rewrite R10.
    assert (R11 : reg_get regs 11 = Z_to_bv 64 outp) by exact AO. rewrite R11.
    unfold joined_c.JOINED.
    apply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO |].
    eapply (run1 SLEN);
      [ apply stk_normalize; [exact ST | lia] | lia | apply hdr_norm; [exact RO | exact HD0]
      | apply wrd_norm; [exact RO | exact WR0] | exact NLT | lia | exact A8 | lia | lia | exact W8 | lia | lia
      | exact NEED | apply mem_inv_normalize ]. }
  intros ms1 (can1 & (st1 & Q1 & REL1 & ROS1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & x18' & x19' & x20' & x21' & x22' & x23'
    & t3' & t4' & t5' & t6' & m1' & -> & MU1' & WM1' & MI1' & FR1').
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL1) as [CAN1 HR1].
  remember (ms_mem can1) as m1 eqn:Em1. subst can1. clear Em1.
  assert (RN0 : mem_rel rsegs mem (normalize rsegs mem)) by (apply mem_rel_normalize; exact RO).
  pose proof (munch_rel rsegs _ _ _ _ _ RN0 HR1 ROS1 MU1') as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ RN0 HR1 ROS1 WM1') as WM1.
  pose proof (ro_agree_same rsegs _ _ RO ROS1) as RO1.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ HR1 FR1') as FR1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x153d4) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 80))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 outp) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 W) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 (jn ws + 1))
    by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 80) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 80 <= a < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 80, bv_unsigned sp)] a) by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
  assert (MR1 : aa_MR API L A m1 md).
  { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (Hp & H4 & Hc & _).
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  eapply SR_bind.
  { eapply (MAL L A R1 m1 md (jn ws + 1) b); [ | exact RO1 | exact E1_10 | exact RES | exact ROOM].
    split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
    split; [rewrite E1_1; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite SP1; replace (bv_unsigned sp - 80) with (bv_unsigned sp + (-5) * 16) by ring;
            rewrite Z.mod_add by lia; exact HAL|].
    split; [rewrite SP1; change ALLOC_STACK with 8192; lia|].
    split; [rewrite SP1; lia|].
    split; [intros a Ha; rewrite SP1 in Ha; change ALLOC_STACK with 8192 in Ha; rewrite SEGS; apply WM1; apply HWS; lia|].
    split; [rewrite E1_4; exact HTP|].
    split; [intros a Ha; rewrite SEGS; apply WM1; apply HERR; exact Ha|].
    intros HI. specialize (HAUX HI). rewrite SP1.
    destruct HAUX as (av & ar & W1 & W2 & W3 & W4 & B1 & B2 & B3 & B4 & L1 & L2).
    exists av, ar.
    split.
    { eapply word_mem_munch; [exact MU1 | | exact W1]. intros k Hk.
      assert (SO : owned B L A (ms_libc B + 8 + Z.of_nat k)) by (right; unfold static_owned; lia).
      destruct (owned_low B _ LAWS _ _ _ _ _ HMR SO). split; [lia | apply OUT1; lia]. }
    split.
    { intros k Hk. eapply word_mem_munch; [exact MU1 | | exact (W2 k Hk)]. intros k' Hk'.
      split; [lia | apply OUT1; lia]. }
    split.
    { eapply word_mem_munch; [exact MU1 | | exact W3]. intros k Hk. split; [lia | apply OUT1; lia]. }
    split.
    { eapply word_mem_munch; [exact MU1 | | exact W4]. intros k Hk. split; [lia | apply OUT1; lia]. }
    lia. }
  intros c2 RET.
  destruct RET as (L' & A' & R2 & m2 & md2 & d & -> & POST & A0' & NZ & AL & FRESH & BLK & KEPT & RO2 & GK & UBK
    & INIT & RLEN & RES').
  rewrite SEGS in RO2.
  destruct POST as (HMR' & HWF' & HBD' & HLE & HSTAB & HPRES & HVM & HFRAME & HBLKS & HSCR).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR') as (Hh2 & Hl2 & Hmat2).
  destruct BLK as (b1 & b2 & BLK1 & BLK2).
  pose proof FRESH as (FR_lo & FR_hi & FR_img).
  assert (INB : In (d, jn ws + 1) (blocks L' A')) by (rewrite BLK1; apply in_or_app; right; left; reflexivity).
  assert (INO : forall q sz, In (q, sz) (blocks L A) -> In (q, sz) (blocks L' A')).
  { intros q sz Hq. rewrite BLK2 in Hq. rewrite BLK1. apply in_app_iff in Hq as [Hq|Hq];
      apply in_app_iff; [left; exact Hq | right; right; exact Hq]. }
  assert (NOWN : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
  { intros a Ha. split; intros Ho;
      [destruct (owned_low B _ LAWS _ _ _ _ _ HMR Ho) | destruct (owned_low B _ LAWS _ _ _ _ _ HMR' Ho)]; lia. }
  assert (HI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8272 <= a < bv_unsigned sp - 80) ->
     mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
     (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha Hs. destruct (NOWN a (proj1 Ha)) as [N1 N2].
    apply HFRAME; [left; exact Ha | exact N1 | exact N2 | | intros F; exact F].
    unfold scratch_k. rewrite SP1. change ALLOC_STACK with 8192. intros [H|H]; lia. }
  assert (HIM : forall a, bv_unsigned sp <= a < 2 ^ 64 ->
     mbyte (ms_segs B) m2 a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha. destruct (HI2 a ltac:(lia) ltac:(lia)) as [E W2'].
    pose proof (munch_mbyte (ms_segs B) _ _ _ a MU1 ltac:(lia) (OUT1 a ltac:(lia) ltac:(lia))) as E01.
    pose proof (munch_writable (ms_segs B) _ _ _ a MU1 ltac:(lia) (OUT1 a ltac:(lia) ltac:(lia))) as W01.
    split; [rewrite E, E01; reflexivity | rewrite W01, W2'; tauto]. }
  assert (BKP : forall q sz i, In (q, sz) (blocks L A) -> 0 <= i < sz ->
     mbyte (ms_segs B) m2 (q + i) = mbyte (ms_segs B) mem (q + i)).
  { intros q sz i Hq Hi. destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hq Hi) as (_ & Hlo & Hhi & _).
    rewrite (KEPT q sz i Hq (fun F => F) Hi).
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  eassert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 80) _).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    rewrite <- SEGS. destruct (HI2 (bv_unsigned sp - 80 + i) ltac:(lia) ltac:(lia)) as [E Wq].
    split; [exact E | apply Wq]. }
  assert (WO2 : wr_at rsegs m2 outp 8).
  { split; [lia|]. split; [lia|]. intros i Hi.
    pose proof (proj1 (proj2 (HIM (outp + i) ltac:(lia))) ltac:(rewrite SEGS; exact (OWR i Hi))) as Wq.
    rewrite SEGS in Wq. exact Wq. }
  assert (HD2 : hdr m2 (X2 d (jn ws + 1) outp) W arr (length ws)).
  { split; [|split].
    - apply bytes_of_le; [lia | rewrite length_le4; lia |].
      apply (blk_data_kept B mem m2 _ _); [|exact L24]. intros i Hi. rewrite length_le4 in Hi.
      exact (proj1 (HIM (W + 24 + i) ltac:(lia))).
    - apply bytes_of_le; [lia | rewrite length_le8; lia |].
      apply (blk_data_kept B mem m2 _ _); [|exact L16]. intros i Hi. rewrite length_le8 in Hi.
      exact (proj1 (HIM (W + 16 + i) ltac:(lia))).
    - intros x Hx. out_tac. }
  assert (WR2 : wrd m2 (X2 d (jn ws + 1) outp) arr wp ws).
  { apply (wrd_build m2 _ (blocks L A)).
    - intros q sz Hin. destruct (BR0 q sz Hin). lia.
    - intros q sz x Hin Hx. destruct (BR0 q sz Hin) as [Q0 Q8]. split.
      + destruct (Z_lt_ge_dec x (q + sz)) as [D|D].
        * replace x with (q + (x - q)) by ring.
          exact (proj1 (block_facts B _ LAWS _ _ _ _ _ _ (x - q) HMR' (INO q sz Hin) ltac:(lia))).
        * exact (BSP L' A' m2 md2 q sz x HMR' (INO q sz Hin) ltac:(lia)).
      + assert (Hq' : In (q, sz) (b1 ++ b2)) by (rewrite <- BLK2; exact Hin).
        pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR' BLK1 Hq') as Dj.
        assert (D8 : d mod 8 = 0) by (Z.div_mod_to_equations; lia).
        destruct Dj as [Dj|Dj].
        * pose proof (ceil8_le (q + sz) d Dj D8). out_tac.
        * out_tac.
    - exact ARRB.
    - exact WB.
    - intros k Hk. destruct (WK k Hk) as (LA & NN & LW). destruct (WBOUND k Hk) as [P1 P2].
      split; [|split].
      + apply bytes_of_le; [lia | rewrite length_le8; lia |].
        apply (le_at_kept L A mem m2 _ _ BKP); [|exact LA].
        exists qa, sa. split; [exact Ia|]. rewrite length_le8. lia.
      + exact NN.
      + apply bytes_of_le; [lia | rewrite length_app; cbn [length]; lia |].
        apply (le_at_kept L A mem m2 _ _ BKP); [|exact LW].
        destruct (WB k Hk) as (q & sz & Iq & H1 & H2). exists q, sz. split; [exact Iq|].
        rewrite length_app. cbn [length]. lia. }
  destruct (present_rw_cells rsegs m2 d (Z.to_nat (jn ws + 1)) ltac:(lia) ltac:(lia)) as [junk2 DC2].
  { intros i Hi. exact (proj1 (block_facts B _ LAWS _ _ _ _ _ _ i HMR' INB ltac:(lia))). }
  assert (DP2 : dstp m2 d (jn ws + 1) []).
  { destruct DC2 as [[Hwf Hb] Hw]. exists junk2. cbn in Hwf. destruct Hwf as [Lj _].
    split; [cbn [length Nat.add]; lia|]. split.
    - cbn [cells_bytes cbytes app] in Hb |- *. rewrite app_nil_r in Hb. exact Hb.
    - cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. rewrite Z2Nat.id in Hw by lia. exact Hw. }
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 80))
    by exact (eq_trans (HPRES 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_8 : reg_get R2 8 = Z_to_bv 64 outp) by exact (eq_trans (HPRES 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (E2_9 : reg_get R2 9 = Z_to_bv 64 W) by exact (eq_trans (HPRES 9 ltac:(unfold callee_saved; lia)) E1_9).
  assert (E2_10 : reg_get R2 10 = Z_to_bv 64 d) by exact A0'.
  rewrite E1_1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2_2, E2_8, E2_9, E2_10, SEGS.
    apply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO2 |].
    eapply (run2 SLEN MCPY) with (sp1 := Z_to_bv 64 (bv_unsigned sp - 80)) (arr := arr) (wp := wp).
    - rewrite unsigned_lit by lia.
      apply rw_cells_normalize; [exact RO2 | exact FR2 | intros i Hi; cbn in Hi; apply ro_addr_hi; lia].
    - apply (wr_at_norm rsegs m2); [apply mem_rel_normalize; exact RO2 | exact WO2 | intros i Hi; apply ro_addr_hi; lia].
    - exact OAL.
    - split; [apply hdr_norm; [exact RO2 | exact HD2]|]. split; [apply wrd_norm; [exact RO2 | exact WR2]|].
      repeat split; lia.
    - apply dstp_norm; [exact RO2 | exact DP2 |]. intros i Hi.
      apply (ro_addr_out B SEGS); [lia | apply FR_img; lia].
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - apply mem_inv_normalize. }
  intros ms3 (can3 & (st3 & Q3 & REL3 & ROS3) & EQ3). unfold post2 in Q3.
  destruct Q3 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3'
    & -> & MU3' & WM3' & MI3' & BR3' & BO3').
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL3) as [CAN3 HR3].
  remember (ms_mem can3) as m3 eqn:Em3. subst can3. clear Em3.
  assert (RN2 : mem_rel rsegs m2 (normalize rsegs m2)) by (apply mem_rel_normalize; exact RO2).
  pose proof (munch_rel rsegs _ _ _ _ _ RN2 HR3 ROS3 MU3') as MU3.
  pose proof (wmono_rel rsegs _ _ _ _ RN2 HR3 ROS3 WM3') as WM3.
  pose proof (ro_agree_same rsegs _ _ RO2 ROS3) as RO3.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ HR3) BR3') as BR3.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ HR3) BO3') as BO3.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite RP.
  assert (SPEQ : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 80)) + 80) = sp).
  { rewrite unsigned_lit by lia. replace (bv_unsigned sp - 80 + 80) with (bv_unsigned sp) by ring.
    apply Z_to_bv_bv_unsigned. }
  assert (OUT3 : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + (jn ws + 1)) -> ~ (outp <= a < outp + 8) ->
            outside (X2 d (jn ws + 1) outp) a) by (intros a _ H1 H2; unfold X2; cbn [outside]; tauto).
  assert (MR3 : aa_MR API L' A' m3 md2).
  { eapply (mr_frame B _ LAWS L' A' m2 m3 md2 md2 HMR').
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR' Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU3 | lia | apply OUT3; [lia | | lia]].
      intros Hin. apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (a - d) HMR' INB ltac:(lia))))).
      replace (d + (a - d)) with a by ring. exact Ho.
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR' Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU3 | lia | apply OUT3; [lia | | lia] | exact Hp].
      intros Hin. apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (a - d) HMR' INB ltac:(lia))))).
      replace (d + (a - d)) with a by ring. exact Ho.
    - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L' A' m2 md2 p n i HMR' Hin Hi) as (Hp & H4 & Hc & _).
      destruct (Z_le_gt_dec d (ptr_addr L' p + i)) as [D1|D1];
        [destruct (Z_lt_ge_dec (ptr_addr L' p + i) (d + (jn ws + 1))) as [D2|D2]|].
      + apply (present_of_writable_out B SEGS m3 (ptr_addr L' p + i) ltac:(lia)).
        * replace (ptr_addr L' p + i) with (d + (ptr_addr L' p + i - d)) by ring. apply FR_img. lia.
        * destruct Hp as [bb Eb]. apply WM3. unfold wview. rewrite Eb. discriminate.
      + eapply munch_present; [exact MU3 | lia | apply OUT3; lia | exact Hp].
      + eapply munch_present; [exact MU3 | lia | apply OUT3; lia | exact Hp].
    - reflexivity.
    - exact Hh2.
    - exact Hl2.
    - exact Hmat2. }
  apply SR_ret.
  exists L', A', R3, m3, md2, d.
  split; [reflexivity|].
  split.
  { split; [exact MR3|]. split; [exact HWF'|]. split; [exact HBD'|]. split; [exact HLE|]. split; [exact HSTAB|].
    split.
    { eapply (preserved_chain (fun r => (r =? 2) || (r =? 8) || (r =? 9) || ((18 <=? r) && (r <=? 24)))
                regs R1 R2 R3 _ _ X1 HPRES X3).
      - intros r Hr O. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O | split; reflexivity]|]).
        subst r. split; reflexivity.
      - intros r Hr O. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct C as [C|C]; [subst r; exact SPEQ|].
        repeat (destruct C as [C|C]; [subst r; first [discriminate O | reflexivity]|]).
        subst r. discriminate O. }
    split; [exact HVM|].
    split.
    { intros a HA NO1 NO2 NS NE.
      unfold joined_c.joined_writes in NE.
      assert (AR : 0 <= a < 2 ^ 64) by (destruct HA as [HA|HA]; [lia | pose proof (in_img_low B SEGS a HA); lia]).
      assert (NSP : ~ (bv_unsigned sp - 8272 <= a < bv_unsigned sp)).
      { intro H. apply NS. left. unfold spZ. change (getr regs 2) with sp. lia. }
      assert (NER : ~ (errno_addr B <= a < errno_addr B + 4)) by (intro H; apply NS; right; exact H).
      pose proof (munch_mbyte (ms_segs B) _ _ _ a MU1 AR (OUT1 a AR ltac:(lia))) as E01.
      pose proof (munch_writable (ms_segs B) _ _ _ a MU1 AR (OUT1 a AR ltac:(lia))) as W01.
      assert (H12 : mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
                    (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
      { apply HFRAME; [exact HA | exact NO1 | exact NO2 | | intros F; exact F].
        unfold scratch_k. rewrite SP1. change ALLOC_STACK with 8192. intros [H|H]; [lia | exact (NER H)]. }
      pose proof (munch_mbyte (ms_segs B) _ _ _ a MU3 AR (OUT3 a AR ltac:(tauto) ltac:(tauto))) as E23.
      pose proof (munch_writable (ms_segs B) _ _ _ a MU3 AR (OUT3 a AR ltac:(tauto) ltac:(tauto))) as W23.
      split; [rewrite E23, (proj1 H12), E01; reflexivity | rewrite W01, (proj2 H12), W23; tauto]. }
    split.
    { intros p n i Hin Hin' Hi.
      destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (_ & Hlo & Hhi & _).
      assert (INA : In (ptr_addr L p, n) (b1 ++ b2)).
      { rewrite <- BLK2. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hin). }
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR' BLK1 INA) as Dj.
      rewrite (munch_mbyte _ _ _ _ (ptr_addr L p + i) MU3 ltac:(lia)
                 (OUT3 (ptr_addr L p + i) ltac:(lia) ltac:(lia) ltac:(lia))).
      rewrite (HBLKS p n i Hin Hin' Hi).
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    intros a Ha. unfold scratch_k, spZ in Ha. change (getr regs 2) with sp in Ha.
    rewrite SEGS. apply WM3. rewrite <- SEGS.
    destruct Ha as [Ha|Ha].
    - destruct (Z_lt_ge_dec a (bv_unsigned sp - 80)) as [D|D].
      + apply HSCR. unfold scratch_k. rewrite SP1. change ALLOC_STACK with 8192. left. lia.
      + destruct (NOWN a ltac:(lia)) as [N1 N2].
        apply (proj1 (proj2 (HFRAME a ltac:(left; lia) N1 N2 ltac:(unfold scratch_k; rewrite SP1;
                 change ALLOC_STACK with 8192; intros [H|H]; lia) (fun F => F)))).
        rewrite SEGS. apply WM1. apply HWS. lia.
    - apply HSCR. right. exact Ha. }
  split; [rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity|].
  split; [exact NZ|]. split; [exact FRESH|].
  split; [exists b1, b2; split; [exact BLK1 | exact BLK2]|].
  split; [apply le_of_bytes; exact BR3|].
  split; [apply le_of_bytes; exact BO3|].
  split.
  { intros q k i Hq _ Hi.
    destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hq Hi) as (_ & Hlo & Hhi & _).
    assert (Hq' : In (q, k) (b1 ++ b2)) by (rewrite <- BLK2; exact Hq).
    pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR' BLK1 Hq') as Dj.
    rewrite (munch_mbyte _ _ _ _ (q + i) MU3 ltac:(lia) (OUT3 (q + i) ltac:(lia) ltac:(lia) ltac:(lia))).
    rewrite (KEPT q k i Hq (fun F => F) Hi).
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split; [exact RO3|].
  split; [exact UBK|]. split; [exact INIT|]. split; [exact RLEN | exact RES'].
Qed.

End J.
