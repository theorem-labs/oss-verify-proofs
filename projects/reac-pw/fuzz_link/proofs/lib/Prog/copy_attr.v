(* copy_attr (reac_link_alias.c:25-36), PLAIN build: the walk of its contract
   (lib/Prog/copy_attr_c.v) on the plain image, 31 instructions at 0x1637c.
   - out = NULL: `beqz a1` before the prologue goes straight to the ret; nothing is stored.
   - n = 0: the prologue stores ra, s0-s3 in [sp-40, sp), `beqz a2` goes to the epilogue.
   - otherwise: len = rta_len - 4 (`lhu`, `addi -4`), s = a + 4; k = strnlen(s, len), which is
     nul_at of the payload (strnlen_res_full); `bltu` caps k at n - 1; memcpy(out, s, k) on the
     first k bytes of the out buffer; `sb zero` writes the NUL at out + k. The out buffer is split
     into [k][1][n-k-1] cells before memcpy and joined again at the end (ca_final), which gives
     both the C string and the buffer's rw_cells.
   The Post's (l, pay) are the Pre's: u16_at with l < 2^16 fixes l (u16_same) and bytes_at with
   the same length fixes pay (bytes_at_same). Pre, Wr and Post are read out of the contract
   (ca_pre, ca_wr, ca_post), so the walk states nothing of its own. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf copy_attr_c strnlen_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun.
Local Open Scope Z_scope.

Lemma find_byte0_nul : forall l : list byte,
  match find_byte 0 l with Some i => i | None => length l end = nul_at l.
Proof.
  induction l as [|b l IH]; cbn; [reflexivity|].
  unfold bz. destruct (bv_unsigned b =? 0); [reflexivity|].
  destruct (find_byte 0 l); rewrite <- IH; reflexivity.
Qed.

Lemma strnlen_res_full : forall pay : list byte,
  strnlen_res (Z.of_nat (length pay)) pay = Z.of_nat (nul_at pay).
Proof.
  intros pay. unfold strnlen_res. rewrite Nat2Z.id, firstn_all.
  rewrite <- find_byte0_nul. destruct (find_byte 0 pay); reflexivity.
Qed.

Lemma memchr_ok_full : forall S (pay : list byte), memchr_ok S 0 (Z.of_nat (length pay)) pay.
Proof.
  intros S pay. unfold memchr_ok. destruct (find_byte 0 (firstn _ pay)); [left|]; lia.
Qed.

Lemma list_eq_nth_error : forall l l' : list byte, length l = length l' ->
  (forall i, (i < length l)%nat -> nth_error l i = nth_error l' i) -> l = l'.
Proof.
  induction l as [|x l IH]; intros [|y l'] HL H; cbn in HL; try lia; [reflexivity|].
  pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn in H0. injection H0 as ->.
  f_equal. apply IH; [lia|]. intros i Hi. exact (H (S i) ltac:(cbn; lia)).
Qed.

Lemma bytes_at_same : forall m a (bs bs' : list byte),
  bytes_at rsegs m a bs -> bytes_at rsegs m a bs' -> length bs = length bs' -> bs = bs'.
Proof.
  intros m a bs bs' (_ & _ & H) (_ & _ & H') HL.
  apply list_eq_nth_error; [exact HL|]. intros i Hi.
  rewrite <- (H i Hi), <- (H' i ltac:(lia)). reflexivity.
Qed.

Lemma u16_same : forall m a l l', u16_at m a l -> u16_at m a l' ->
  0 <= l < 65536 -> 0 <= l' < 65536 -> l = l'.
Proof.
  intros m a l l' H H' R R'. unfold u16_at in H, H'.
  pose proof (bytes_at_same _ _ _ _ H H' ltac:(rewrite !length_le2; reflexivity)) as E.
  apply (f_equal bytes_le_to_Z) in E. rewrite !bytes_le_to_Z_le2 in E.
  unfold wz in E. rewrite !unsigned_lit in E by lia. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma stk_transport_rw : forall m m' lo hi A n cs,
  stk rsegs m lo hi -> munch [(A, A + n)] m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' A cs -> n <= Z.of_nat (cells_size cs) -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi A n cs (H1 & H2 & H) Hm Hw Hc Hn.
  pose proof (stk_of_rw_cells rsegs m' A cs Hc) as (_ & _ & Hs).
  split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hwx [b Hb]].
  assert (Hin : A <= x < A + Z.of_nat (cells_size cs) \/ ~ (A <= x < A + n)) by lia.
  destruct Hin as [Hin|Hout]; [apply Hs; exact Hin|].
  split; [apply Hw; exact Hwx|]. exists b. unfold mrd in *. rewrite Hm; [exact Hb|].
  rewrite wa_unsigned by lia. cbn [outside]. split; [exact Hout|exact I].
Qed.

Lemma rw_cells_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ H] _]. exact H. Qed.

Lemma rw_cells_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (Ha1 & Hl1 & H1)] [[W2 B2] (Ha2 & Hl2 & H2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))) as [Lt|Ge]; [apply H1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply H2. lia.
Qed.

(* the out buffer after the NUL store: the k copied bytes, the NUL cell, the untouched tail *)
Lemma ca_final : forall m (A k n : Z) (src j4 : list byte) (b0 : byte),
  0 <= k -> k + 1 <= n ->
  rw_cells rsegs m A [CB (Z.to_nat k) src] ->
  rw_cells rsegs m (A + k) [C1 b0] ->
  rw_cells rsegs m (A + k + 1) [CB (Z.to_nat n - Z.to_nat k - 1) j4] ->
  bytes_at rsegs m A (src ++ [b0]) /\ exists junk, rw_cells rsegs m A [CB (Z.to_nat n) junk].
Proof.
  intros m A k n src j4 b0 Hk Hkn H1 H2 H3.
  replace (A + k + 1) with (A + k + Z.of_nat (cells_size [C1 b0])) in H3 by (cbn [cells_size csize]; lia).
  pose proof (rw_cells_join _ _ _ _ H2 H3) as H23.
  replace (A + k) with (A + Z.of_nat (cells_size [CB (Z.to_nat k) src])) in H23 by (cbn [cells_size csize]; lia).
  pose proof (rw_cells_join _ _ _ _ H1 H23) as H.
  split.
  - apply rw_cells_bytes in H. rewrite !cells_bytes_app in H. cbn [cells_bytes cbytes] in H.
    rewrite !app_nil_r, app_assoc in H. apply bytes_at_app in H. exact (proj1 H).
  - destruct (rw_cells_forget rsegs _ _ _ H) as [junk HJ]. exists junk.
    replace (Z.to_nat n) with (cells_size ([CB (Z.to_nat k) src] ++ [C1 b0] ++ [CB (Z.to_nat n - Z.to_nat k - 1) j4]))
      by (rewrite !cells_size_app; cbn [cells_size csize]; lia).
    exact HJ.
Qed.

Definition keep (P : Prop) : Prop := P.

Ltac rp_tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hc := fresh "Hc" in
  intros r Hr; unfold callee_saved in Hr;
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [reflexivity..|];
  assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.

Lemma u16_read : forall m a v, bytes_at rsegs m a (le2 v) -> ov_read_bytes rsegs m (wa a) 2 = Some (le2 v).
Proof.
  intros m a v H. pose proof (bytes_at_ov_read rsegs m a (le2 v) 0 2 H ltac:(rewrite length_le2; lia)) as R.
  change (a + Z.of_nat 0) with (a + 0) in R. rewrite Z.add_0_r in R.
  change (skipn 0 (le2 v)) with (le2 v) in R. rewrite firstn_all2 in R by (rewrite length_le2; lia).
  exact R.
Qed.

Lemma rw_cells_CB_split2 : forall m A (n k : nat) junk,
  rw_cells rsegs m A [CB n junk] -> (k <= n)%nat ->
  rw_cells rsegs m A [CB k (firstn k junk)] /\
  rw_cells rsegs m (A + Z.of_nat k) [CB (n - k) (skipn k junk)].
Proof.
  intros m A n k junk [[Hwf Hb] Hw] Hk. cbn in Hwf. destruct Hwf as [HL _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  rewrite <- (firstn_skipn k junk) in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb1 Hb2].
  rewrite length_firstn in Hb2. replace (Nat.min k (length junk)) with k in Hb2 by lia.
  destruct Hw as (Ha & Hl & Hw).
  split; split.
  - split; [cbn; rewrite length_firstn; split; [lia|exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb1.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [cbn; rewrite length_skipn; split; [lia|exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb2.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply Hw. lia.
Qed.

Lemma arg_same : forall r1 r2 i, getr_same r1 r2 -> arg r1 i = arg r2 i.
Proof. intros r1 r2 i E. unfold arg. exact (f_equal (@bv_unsigned 64) (E _)). Qed.

Lemma spZ_same : forall r1 r2, getr_same r1 r2 -> spZ r1 = spZ r2.
Proof.
  intros r1 r2 E. unfold spZ, YK11.getr. pose proof E as E'. unfold getr_same, getr in E'.
  rewrite E'. reflexivity.
Qed.

Definition ca_pre := ltac:(let t := eval cbv delta [copy_attr_contract] in copy_attr_contract in
  lazymatch t with leaf _ _ ?P _ _ => exact P end).
Definition ca_wr := ltac:(let t := eval cbv delta [copy_attr_contract] in copy_attr_contract in
  lazymatch t with leaf _ _ _ ?W _ => exact W end).
Definition ca_post := ltac:(let t := eval cbv delta [copy_attr_contract] in copy_attr_contract in
  lazymatch t with leaf _ _ _ _ ?Q => exact Q end).

Lemma copy_attr_walk : strnlen_contract -> memcpy_contract -> leaf_walk COPY_ATTR 80 ca_pre ca_wr ca_post.
Proof.
  intros SC MC. unfold leaf_walk, COPY_ATTR, ca_pre, ca_wr, ca_post.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  cbv beta zeta. intros HP MI ST LO SP.
  rewrite mkR_a0, mkR_a1, mkR_a2, mkR_sp in HP.
  rewrite mkR_a0, mkR_a1, mkR_a2, mkR_sp.
  destruct HP as (l0 & pay0 & HU & HL & HB & HLen & HA0 & HAW & HFR & HOUT).
  unfold RTA_HDR in *.
  pose proof (zr_word a0) as Ra0. pose proof (zr_word a1) as Ra1. pose proof (zr_word a2) as Ra2.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Ra0, Ra1, Ra2, Rsp.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  assert (HB0 : keep (bytes_at rsegs m (bv_unsigned a0 + 4) pay0)) by exact HB.
  pose proof HU as HU0. unfold u16_at in HU.
  zstep. if_cases K1; zify_cond K1.
  - (* out = NULL: straight to the ret *)
    zstep.
    apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [rp_tac|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|].
    split; [intros _; reflexivity|]. split; [intros _; apply munch_refl|].
    split; intros H; exfalso; lia.
  - destruct (Z.eq_dec (bv_unsigned a2) 0) as [N0|N1].
    + (* n = 0: prologue, beqz a2, epilogue *)
      pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + bv_unsigned a2)] m) as MU.
      pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU2.
      pose proof (wmono_refl rsegs m) as WM.
      carve_frame 48%nat ST.
      do 8 zstep. if_cases K2; zify_cond K2; [|exfalso; lia].
      do 6 zstep.
      release_frame FR ST (bv_unsigned sp).
      zstep.
      apply evt_done. do 2 eexists. split; [reflexivity|].
      split; [rp_tac|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      split; [intros H; exfalso; lia|]. split; [intros _; exact MU2|].
      split; intros _ H; exfalso; lia.
    + (* out <> NULL, n >= 1 *)
      destruct (HOUT K1 ltac:(lia)) as (HAF & HSEP & jk & HJ). clear HOUT. unfold apart_frame in HAF.
      rewrite mkR_sp in HAF.
      pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + bv_unsigned a2)] m) as MU.
      pose proof (wmono_refl rsegs m) as WM.
      carve_frame 48%nat ST.
      do 8 zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u16_read mm (bv_unsigned a0) (wz l0) HU) as HR end.
      unfold wa in HR. rewrite Z_to_bv_bv_unsigned in HR.
      assert (ZX : zx16 (wz l0) = Z_to_bv 64 l0)
        by (unfold zx16, wz; f_equal; rewrite unsigned_lit by lia; apply Z.mod_small; lia).
      zstep. rewrite ZX.
      do 4 zstep.
      assert (U48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48)
        by (apply unsigned_lit; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply SC with (lo := lo) (buf := pay0);
          [ exact HB
          | match goal with |- memchr_ok _ _ ?n _ => replace n with (Z.of_nat (length pay0)) by lia end;
            apply memchr_ok_full
          | lia | lia
          | rewrite U48; exact ST
          | rewrite U48; lia
          | rewrite U48; lia
          | exact MI ]
        | unfold strnlen_post; post_call rsegs mm ] end.
      rewrite ?U48 in *.
      match goal with H : stk rsegs _ lo _ |- _ => rename H into ST end.
      match goal with |- context [strnlen_res ?n pay0] => replace n with (Z.of_nat (length pay0)) by lia end.
      rewrite strnlen_res_full. pose proof (nul_at_le pay0) as NL.
      zstep. zstep. if_cases K3; zify_cond K3;
      [ remember (Z.of_nat (nul_at pay0)) as k eqn:Ek
      | zstep; remember (bv_unsigned a2 + -1) as k eqn:Ek ];
      assert (KM : k = Z.min (Z.of_nat (nul_at pay0)) (bv_unsigned a2 - 1)) by lia; clear Ek K3.
      all: do 4 zstep.
      all: assert (Kr : 0 <= k <= bv_unsigned a2 - 1) by lia.
      all: assert (UK : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
      all: assert (U4 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 4)) = bv_unsigned a0 + 4)
             by (apply unsigned_lit; lia).
      all: destruct (rw_cells_CB_split2 _ _ _ (Z.to_nat k) _ HJ ltac:(lia)) as [HJ1 HJ2].
      all: destruct (rw_cells_CB_split2 _ _ _ 1 _ HJ2 ltac:(lia)) as [HJ3 HJ4].
      all: clear HJ HJ2.
      all: rewrite Z2Nat.id in HJ3, HJ4 by lia.
      all: change (Z.of_nat 1) with 1 in HJ4.
      all: pose proof HB as HBs.
      all: rewrite <- (firstn_skipn (Z.to_nat k) pay0) in HBs.
      all: apply bytes_at_app in HBs.
      all: destruct HBs as [HSRC _].
      all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply MC with (src := firstn (Z.to_nat k) pay0) (junk := firstn (Z.to_nat k) jk);
          [ rewrite U4; exact HSRC
          | rewrite UK, length_firstn; lia
          | rewrite UK; exact HJ1
          | rewrite U4, UK; lia
          | assumption ]
        | ] end.
      all: intros ms' PO; destruct_exs PO; destruct PO as [E [MUc [WMc [MIc [RWc BAc]]]]]; subst ms'.
      all: pose proof (stk_transport_rw _ _ _ _ _ _ _ ST MUc WMc RWc
                         ltac:(cbn [cells_size csize]; rewrite UK; lia)) as ST2.
      all: clear ST; rename ST2 into ST.
      all: lazymatch type of MUc with munch _ ?m1 ?m2 =>
             transport_after_call rsegs m1 m2 MUc WMc;
             try match goal with H : mem_inv rsegs m1 |- _ => clear H end end.
      all: clear MUc WMc.
      all: rewrite UK in RWc.
      all: replace (ret_pc (Z_to_bv 64 91092)) with (Z_to_bv 64 91092)
             by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      all: zstep.
      all: remember (bv_unsigned a1 + k) as q eqn:Eq in *.
      all: zstep.
      all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
             change bs with [Z_to_bv 8 0] end; mem_after_store.
      all: do 6 zstep.
      all: release_frame FR ST (bv_unsigned sp).
      all: zstep.
      all: apply evt_done; do 2 eexists; split; [reflexivity|].
      all: split; [rp_tac|].
      all: split; [exact MU|]. all: split; [exact WM|]. all: split; [assumption|]. all: split; [exact ST|].
      all: split; [intros H; exfalso; lia|]. all: split; [intros H; exfalso; lia|].
      all: subst q.
      all: destruct (ca_final _ (bv_unsigned a1) k (bv_unsigned a2) _ _ _ ltac:(lia) ltac:(lia) RWc HJ3 HJ4)
             as [HBY HRW].
      all: split; [|intros _ _; exact HRW].
      all: intros _ _ l pay Hu Hl Hb Hlen.
      all: assert (l = l0) by (eapply u16_same; [exact Hu | exact HU0 | lia | lia]).
      all: subst l.
      all: assert (pay = pay0) by (eapply bytes_at_same; [exact Hb | exact HB0 | lia]).
      all: subst pay.
      all: assert (CT : cut_text pay0 (bv_unsigned a2) = firstn (Z.to_nat k) pay0)
             by (unfold cut_text; rewrite <- KM; reflexivity).
      all: split; [rewrite CT; exact HBY|].
      all: intros Hin; apply cut_text_nonul in Hin; apply Hin; reflexivity.
Qed.

Theorem copy_attr_holds : strnlen_contract -> memcpy_contract -> copy_attr_contract.
Proof.
  intros SC MC. unfold copy_attr_contract. apply leaf_intro.
  - intros r1 r2 m E H. assert (E' : getr_same r2 r1) by (intros r; symmetry; apply E).
    cbv beta in *. unfold apart_frame in *.
    rewrite (arg_same r2 r1 0 E'), (arg_same r2 r1 1 E'), (arg_same r2 r1 2 E'), (spZ_same r2 r1 E').
    exact H.
  - intros r1 r2 m E. cbv beta. rewrite (arg_same r1 r2 1 E), (arg_same r1 r2 2 E). reflexivity.
  - intros r1 r2 m q1 q2 m' E _ H. assert (E' : getr_same r2 r1) by (intros r; symmetry; apply E).
    cbv beta in *.
    rewrite (arg_same r2 r1 0 E'), (arg_same r2 r1 1 E'), (arg_same r2 r1 2 E'), (spZ_same r2 r1 E').
    exact H.
  - exact (copy_attr_walk SC MC).
Qed.

Print Assumptions copy_attr_holds.
