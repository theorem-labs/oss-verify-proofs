(** check_declared (plain build, 0x14acc, 48-byte frame): proof of [check_declared_contract] (check_declared_c.v)
    from the contract of its callee strcmp (strcmp_c.v, 0x1ebf8).

    Code (image 3776ca44d75c):
      0x14acc-0x14ae4  frame of 48: ra s0 s1 s2 s3 s4 at sp+40 .. sp+0
      0x14ae8 bne a0,a1 -> abort; s3 = n; 0x14af0 bne a3,a5 -> abort; s0 = cap; s1 = tab; 0x14afc blez s3 -> GUARD
      LOOP 0x14b08 (s2 = mt + 20 i, s4 = tab + 18 i, s3 = n - i): lhu a0,16(s4); lw a1,16(s2); bne a1,a0 -> abort;
           strcmp(s4, s2); bnez a0 -> abort; s3 -= 1; s2 += 20; s4 += 18; bnez s3 -> LOOP
      GUARD 0x14b34: s1 = tab + 18 cap; a1 = 17; a0 = 0x5a;
           0x14b48 lbu a2,0(s1); bne a2,a0 -> 0x14b60; a3 = (a1 <> 0); a1 -= 1; s1 += 1; bnez a3 -> 0x14b48
      0x14b60 bne a2,0x5a -> abort; 0x14b68 restore; ret.
    The premise (vlans_are, the guard entry in memory) makes every branch to the `jal abort` at 0x14b88 dead: the
    answers and lengths agree, each entry's vid agrees (lhu of a value below 65536 equals the sign-extended lw of the
    same value), each entry's parents are equal byte strings (SegModel.strcmp = 0 on NUL-free strings, so strcmp
    returns 0), and the 18 guard bytes are 0x5a. strcmp writes no memory, so the walk runs on one memory after the
    prologue. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec strcmp_c check_declared_c.
Import ListNotations.
Open Scope Z_scope.

(** ** The model: strcmp on NUL-free strings *)
Lemma zs_inj : forall l l' : list byte, zs l = zs l' -> l = l'.
Proof.
  unfold zs. induction l as [|x l IH]; intros [|y l'] H; cbn [map] in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma zs_nonul : forall l : list byte, ~ In (Z_to_bv 8 0) l -> ~ In 0 (zs l).
Proof.
  intros l H Hin. unfold zs in Hin. apply in_map_iff in Hin as (b & Hb & Hin). apply H.
  replace (Z_to_bv 8 0) with b; [exact Hin|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.

Lemma sm_strcmp_eq : forall s t, ~ In 0 s -> ~ In 0 t -> SegModel.strcmp s t = 0 -> s = t.
Proof.
  induction s as [|a s IH]; intros [|b t] Hs Ht H; cbn [SegModel.strcmp] in H.
  - reflexivity.
  - exfalso. apply Ht. left. lia.
  - exfalso. apply Hs. left. lia.
  - revert H. destruct (Z.eqb_spec a b) as [E|E]; destruct (Z.eqb_spec a 0) as [E0|E0]; cbn [andb negb]; intros H.
    + exfalso. apply Hs. left. lia.
    + subst b. f_equal. apply IH; [intros X; apply Hs; right; exact X | intros X; apply Ht; right; exact X | exact H].
    + exfalso. lia.
    + exfalso. lia.
Qed.

(** SegModel.strcmp of two NUL-free byte strings is 0 exactly when they are equal (the name and statement of
    Spec/SegBridge.v's bridge_strcmp, which has not landed). *)
Lemma bridge_strcmp : forall sx sy : list byte, ~ In (Z_to_bv 8 0) sx -> ~ In (Z_to_bv 8 0) sy ->
  SegModel.strcmp (zs sx) (zs sy) = 0 <-> sx = sy.
Proof.
  intros sx sy Hx Hy. split.
  - intros H. apply zs_inj. apply sm_strcmp_eq; [apply zs_nonul; exact Hx | apply zs_nonul; exact Hy | exact H].
  - intros ->. apply strcmp_refl.
Qed.

(** A C string field: its first [length s + 1] bytes are the string's bytes and the NUL. *)
Lemma cstr_split : forall cap s f, cstr_enc cap s f ->
  exists sx, firstn (S (length s)) f = sx ++ [Z_to_bv 8 0] /\ zs sx = s /\ ~ In (Z_to_bv 8 0) sx.
Proof.
  intros cap s f (Hl & Hs & Hn & Hz).
  assert (Zp : zs (firstn (S (length s)) f) = s ++ [0]) by (unfold zs in *; rewrite <- firstn_map; exact Hz).
  assert (NE : firstn (S (length s)) f <> []).
  { intros E. rewrite E in Zp. cbn in Zp. destruct s; discriminate. }
  destruct (exists_last NE) as (sx & b & E).
  rewrite E in Zp. unfold zs in Zp. rewrite map_app in Zp. cbn [map] in Zp.
  apply app_inj_tail in Zp as [Z1 Z2].
  exists sx. split; [rewrite E; repeat f_equal; apply bv_eq; rewrite Z2; reflexivity|].
  split; [exact Z1|].
  intros Hin. apply Hn. rewrite <- Z1. unfold zs. apply in_map_iff. exists (Z_to_bv 8 0). split; [reflexivity|exact Hin].
Qed.

(** ** Byte views *)
Lemma fld_fld : forall a n b k (l : list byte), (a + n <= k)%nat ->
  firstn n (skipn a (firstn k (skipn b l))) = firstn n (skipn (b + a) l).
Proof.
  intros a n b k l H. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Nat.min n (k - a)) with n by lia. rewrite (Nat.add_comm a b). reflexivity.
Qed.

Section Bytes.
Variable segs : list Segment.

Lemma bat_sub : forall m a (l : list byte) k n, bytes_at segs m a l -> (k + n <= length l)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk.
  rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H as [_ H].
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H as [H _].
  rewrite firstn_length_le in H by lia. exact H.
Qed.

(** Entry i of the reader's table: the vid's two bytes at tab + 18 i + 16, and the parent's string with its NUL at
    tab + 18 i. *)
Lemma rtab_entry : forall m tab gt bt i, bytes_at segs m tab bt -> rtab_enc gt bt -> (i < length gt)%nat ->
  ov_read_bytes segs m (wa (tab + 18 * Z.of_nat i + 16)) 2 = Some (le2 (Z_to_bv 64 (snd (nth i gt ([], 0))))) /\
  0 <= snd (nth i gt ([], 0)) < 65536 /\
  exists sx, bytes_at segs m (tab + 18 * Z.of_nat i) (sx ++ [Z_to_bv 8 0]) /\ zs sx = fst (nth i gt ([], 0)) /\
             ~ In (Z_to_bv 8 0) sx.
Proof.
  intros m tab gt bt i HB [HL HE] Hi.
  destruct (HE i Hi) as (L18 & HC & HV & H2).
  split; [|split; [exact HV|]].
  - rewrite <- H2. unfold fld. rewrite fld_fld by lia.
    replace (tab + 18 * Z.of_nat i + 16) with (tab + Z.of_nat (18 * i + 16)) by lia.
    apply (bytes_at_ov_read segs m tab bt (18 * i + 16) 2 HB). lia.
  - pose proof HC as (_ & Hlt & _).
    destruct (cstr_split 16 _ _ HC) as (sx & E & Z1 & N1).
    exists sx. split; [|split; [exact Z1 | exact N1]].
    rewrite <- E. unfold fld. rewrite fld_fld by lia. rewrite firstn_firstn, Nat.add_0_r.
    replace (Nat.min (S (length (fst (nth i gt ([], 0))))) 16) with (S (length (fst (nth i gt ([], 0))))) by lia.
    replace (tab + 18 * Z.of_nat i) with (tab + Z.of_nat (18 * i)) by lia.
    apply bat_sub; [exact HB | lia].
Qed.

(** Entry i of the model's table: the vid's four bytes at mt + 20 i + 16, and the parent's string with its NUL at
    mt + 20 i. *)
Lemma mtab_entry : forall m mt wt bm i, bytes_at segs m mt bm -> mtab_enc wt bm -> (i < length wt)%nat ->
  ov_read_bytes segs m (wa (mt + 20 * Z.of_nat i + 16)) 4 = Some (le4 (Z_to_bv 64 (snd (nth i wt ([], 0))))) /\
  0 <= snd (nth i wt ([], 0)) < 2 ^ 32 /\
  exists sy, bytes_at segs m (mt + 20 * Z.of_nat i) (sy ++ [Z_to_bv 8 0]) /\ zs sy = fst (nth i wt ([], 0)) /\
             ~ In (Z_to_bv 8 0) sy.
Proof.
  intros m mt wt bm i HB [HL HE] Hi.
  destruct (HE i Hi) as (L20 & HC & HV & H4).
  split; [|split; [exact HV|]].
  - rewrite <- H4. unfold fld. rewrite fld_fld by lia.
    replace (mt + 20 * Z.of_nat i + 16) with (mt + Z.of_nat (20 * i + 16)) by lia.
    apply (bytes_at_ov_read segs m mt bm (20 * i + 16) 4 HB). lia.
  - pose proof HC as (_ & Hlt & _).
    destruct (cstr_split 16 _ _ HC) as (sy & E & Z1 & N1).
    exists sy. split; [|split; [exact Z1 | exact N1]].
    rewrite <- E. unfold fld. rewrite fld_fld by lia. rewrite firstn_firstn, Nat.add_0_r.
    replace (Nat.min (S (length (fst (nth i wt ([], 0))))) 16) with (S (length (fst (nth i wt ([], 0))))) by lia.
    replace (mt + 20 * Z.of_nat i) with (mt + Z.of_nat (20 * i)) by lia.
    apply bat_sub; [exact HB | lia].
Qed.

(** Byte j of the guard entry. *)
Lemma guard_read : forall m a j, bytes_at segs m a GUARD_BYTES -> (j < 18)%nat ->
  ov_read_bytes segs m (wa (a + Z.of_nat j)) 1 = Some [Z_to_bv 8 90].
Proof.
  intros m a j H Hj.
  rewrite (bytes_at_ov_read segs m a GUARD_BYTES j 1 H) by (unfold GUARD_BYTES; rewrite repeat_length; lia).
  unfold GUARD_BYTES. rewrite skipn_repeat_gen. replace (18 - j)%nat with (S (17 - j)) by lia. reflexivity.
Qed.
End Bytes.

(** ** The premise vlans_are *)
Lemma forallb2_nth : forall {A B} (P : A -> B -> bool) l1 l2 da db i, forallb2 P l1 l2 = true ->
  (i < length l1)%nat -> P (nth i l1 da) (nth i l2 db) = true.
Proof.
  intros A B P. induction l1 as [|x l1 IH]; intros [|y l2] da db i H Hi; cbn [forallb2 length] in *;
    try discriminate; try lia.
  apply andb_prop in H as [H1 H2]. destruct i as [|i]; cbn [nth]; [exact H1|]. apply IH; [exact H2 | lia].
Qed.

Lemma vlans_are_spec : forall gv gt wv wt cap, vlans_are (gv, gt) (wv, wt) cap = true ->
  gv = wv /\ length gt = length wt /\ Z.of_nat (length gt) <= cap /\
  forall i, (i < length gt)%nat -> snd (nth i gt ([], 0)) = snd (nth i wt ([], 0)) /\
                                  SegModel.strcmp (fst (nth i gt ([], 0))) (fst (nth i wt ([], 0))) = 0.
Proof.
  intros gv gt wv wt cap H. unfold vlans_are in H. cbn [fst snd] in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.leb_le in H4.
  split; [exact H1|]. split; [exact H2|]. split; [exact H4|].
  intros i Hi. pose proof (forallb2_nth _ _ _ ([], 0) ([], 0) i H3 Hi) as P. cbn beta in P.
  apply andb_prop in P as [P1 P2]. apply Z.eqb_eq in P1. apply Z.eqb_eq in P2. split; assumption.
Qed.

(** ** Words *)
Lemma zx16_small : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma sx32_small : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia). reflexivity.
Qed.

(** ** The walk *)
Section Walk.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (Sp lo tab mt cap : Z) (gt wt : list (list Z * Z)) (bt bm : list byte).
Hypothesis HSC : strcmp_contract.
Hypothesis HBT : bytes_at rsegs m0 tab bt.
Hypothesis HET : rtab_enc gt bt.
Hypothesis HBM : bytes_at rsegs m0 mt bm.
Hypothesis HEM : mtab_enc wt bm.
Hypothesis HG : bytes_at rsegs m0 (tab + 18 * cap) GUARD_BYTES.
Hypothesis HL : length gt = length wt.
Hypothesis HC : Z.of_nat (length gt) <= cap.
Hypothesis HC40 : 0 <= cap < 40.
Hypothesis HE : forall i, (i < length gt)%nat -> snd (nth i gt ([], 0)) = snd (nth i wt ([], 0)) /\
  SegModel.strcmp (fst (nth i gt ([], 0))) (fst (nth i wt ([], 0))) = 0.
Hypothesis HAT : tab + 18 * (cap + 1) <= lo \/ Sp <= tab.
Hypothesis HAM : mt + 20 * (cap + 1) <= lo \/ Sp <= mt.
Hypothesis Hlo : 0 <= lo.
Hypothesis HK : lo + 48 <= Sp.
Hypothesis HS : Sp < 2 ^ 64.

Local Abbreviation Post :=
  (ret_void rsegs ra (Z_to_bv 64 Sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 [(Sp - 48, Sp)] lo
     (fun _ => True)).

(** The frame between the prologue and the epilogue. *)
Definition frm (m : word -> option byte) : Prop :=
  rw_cells rsegs m (Sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk rsegs m lo (Sp + -48) /\ munch [(Sp - 48, Sp)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m.

Lemma bt_len : length bt = (18 * length gt)%nat.
Proof. destruct HET as [L _]. exact L. Qed.
Lemma bm_len : length bm = (20 * length wt)%nat.
Proof. destruct HEM as [L _]. exact L. Qed.

Lemma frm_bt : forall m, frm m -> bytes_at rsegs m tab bt.
Proof.
  intros m (_ & _ & MU & _ & _). eapply bytes_at_transport; [exact HBT | exact MU |].
  cbn [disjoint_from]. split; [|exact I]. rewrite bt_len. lia.
Qed.

Lemma frm_bm : forall m, frm m -> bytes_at rsegs m mt bm.
Proof.
  intros m (_ & _ & MU & _ & _). eapply bytes_at_transport; [exact HBM | exact MU |].
  cbn [disjoint_from]. split; [|exact I]. rewrite bm_len. lia.
Qed.

Lemma frm_g : forall m, frm m -> bytes_at rsegs m (tab + 18 * cap) GUARD_BYTES.
Proof.
  intros m (_ & _ & MU & _ & _). eapply bytes_at_transport; [exact HG | exact MU |].
  cbn [disjoint_from]. split; [|exact I]. change (Z.of_nat (length GUARD_BYTES)) with 18. lia.
Qed.

(** The exit 0x14b68: restore ra and s0-s4, return. *)
Lemma epi : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
  frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x14b68) fc None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (FR & ST & MU & WM & MI).
  do 8 step.
  apply evt_done. unfold ret_void.
  exists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m.
  split; [unfold mkR; repeat f_equal; lia|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [|exact I].
  pose proof (stk_release rsegs m lo (Sp + -48) _ ST FR ltac:(lia)) as R. cbn [cells_size csize Nat.add] in R.
  rewrite unsigned_lit by lia. replace (Sp + -48 + Z.of_nat 48) with Sp in R by lia. exact R.
Qed.

(** The guard loop 0x14b48 at byte j of tab[cap] (k = 17 - j bytes after it): s1 = tab + 18 cap + j, a0 = 0x5a,
    a1 = k. Every byte is 0x5a, so the loop runs to its 18th byte and the check at 0x14b64 falls through. *)
Lemma gloop : forall k j m (x1 x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 w9 w10 w11 : word),
  (j + k = 17)%nat -> w9 = Z_to_bv 64 (tab + 18 * cap + Z.of_nat j) -> w10 = Z_to_bv 64 90 ->
  w11 = Z_to_bv 64 (Z.of_nat k) -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -48)) gp tp x5 x6 x7 x8 w9 w10 w11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x14b48) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros j m x1 x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 w9 w10 w11
    Hjk E9 E10 E11 FRM; subst w9 w10 w11;
    pose proof (guard_read rsegs m (tab + 18 * cap) j (frm_g m FRM) ltac:(lia)) as RD.
  - step. step. if_cases K; cbv iota; [exfalso; vm_compute in K; discriminate K|].
    step. step. step. step.
    if_cases K2; cbv iota; [exfalso; first [vm_compute in K2; discriminate K2 | zify_cond K2; lia]|].
    step. step. if_cases K3; cbv iota; [exfalso; vm_compute in K3; discriminate K3|].
    eapply epi. exact FRM.
  - step. step. if_cases K; cbv iota; [exfalso; vm_compute in K; discriminate K|].
    step. step. step. step.
    if_cases K2; cbv iota; [|exfalso; zify_cond K2; lia].
    eapply (IH (S j)); [lia | f_equal; lia | reflexivity | f_equal; lia | exact FRM].
Qed.

(** 0x14b34, after the entry loop: s1 = tab + 18 cap, a1 = 17, a0 = 0x5a, then the guard loop at byte 0. *)
Lemma post_loop : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
  frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -48)) gp tp x5 x6 x7 (Z_to_bv 64 cap) (Z_to_bv 64 tab) x10 x11 x12 x13 x14 x15 x16
             x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x14b34) fc None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 FRM.
  do 5 step.
  eapply (gloop 17 0); [lia | | reflexivity | reflexivity | exact FRM].
  rewrite ?(unsigned_lit cap) by lia. f_equal. lia.
Qed.

(** The entry loop 0x14b08 at entry i (k = n - i entries left): s2 = mt + 20 i, s3 = k, s4 = tab + 18 i. The vids
    agree and strcmp returns 0, so neither abort branch is taken. *)
Lemma mloop : forall k i m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 w18 w19 w20 : word),
  (i + k = length gt)%nat -> (0 < k)%nat ->
  w18 = Z_to_bv 64 (mt + 20 * Z.of_nat i) -> w19 = Z_to_bv 64 (Z.of_nat k) ->
  w20 = Z_to_bv 64 (tab + 18 * Z.of_nat i) -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -48)) gp tp x5 x6 x7 (Z_to_bv 64 cap) (Z_to_bv 64 tab) x10 x11 x12 x13 x14 x15 x16
             x17 w18 w19 w20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x14b08) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros i m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 w18 w19 w20
    Hik Hk E18 E19 E20 FRM; [lia|].
  subst w18 w19 w20.
  assert (Hi : (i < length gt)%nat) by lia. assert (Hiw : (i < length wt)%nat) by lia.
  destruct (HE i Hi) as [EV ES].
  destruct (rtab_entry rsegs m tab gt bt i (frm_bt m FRM) HET Hi) as (RD1 & RV1 & sx & BX & ZX & NX).
  destruct (mtab_entry rsegs m mt wt bm i (frm_bm m FRM) HEM Hiw) as (RD2 & RV2 & sy & BY & ZY & NY).
  pose proof (bytes_at_bound _ _ _ _ HBT) as TB. pose proof (bytes_at_bound _ _ _ _ HBM) as MB.
  rewrite bt_len in TB. rewrite bm_len in MB.
  step. step.
  rewrite (zx16_small _ RV1). rewrite (sx32_small (snd (nth i wt ([], 0)))) by lia.
  step.
  if_cases K; cbv iota; [exfalso; zify_cond K; lia|].
  step. step. step.
  eapply evt_cut.
  { eapply HSC with (sx := sx) (sy := sy); rewrite ?unsigned_lit by lia; assumption. }
  intros ms' (r & y11 & y12 & y13 & -> & Hr).
  rewrite ret_pc_even by (try lia; reflexivity).
  assert (R0 : r = Z_to_bv 64 0).
  { apply Hr. apply bridge_strcmp; [exact NX | exact NY |]. rewrite ZX, ZY. exact ES. }
  subst r.
  step. if_cases K2; cbv iota; [exfalso; vm_compute in K2; discriminate K2|].
  step. step. step. step.
  if_cases K3; cbv iota.
  - zify_cond K3. eapply (IH (S i)); [lia | lia | f_equal; lia | f_equal; lia | f_equal; lia | exact FRM].
  - eapply post_loop. exact FRM.
Qed.

(** The whole function from its entry. *)
Lemma body : forall (t0 t1 t2 a0 a7 t3 t4 t5 t6 : word),
  stk rsegs m0 lo Sp -> mem_inv rsegs m0 ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 a0 a0 (Z_to_bv 64 tab) (Z_to_bv 64 (Z.of_nat (length gt)))
             (Z_to_bv 64 mt) (Z_to_bv 64 (Z.of_nat (length gt))) (Z_to_bv 64 cap) a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14acc) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a7 t3 t4 t5 t6 ST MI.
  (* The prologue's stores transport (and so replace) the section hypotheses the loops need: take them first. *)
  pose proof (mloop (length gt) 0) as LP. pose proof post_loop as PL.
  pose proof (munch_refl [(Sp - 48, Sp)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  destruct (stk_carve rsegs m0 lo Sp 48 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
  change (Z.of_nat 48) with 48 in ST1, FR.
  replace (Sp - 48) with (Sp + -48) in ST1, FR by lia.
  do 7 step.
  step. if_cases K; cbv iota; [exfalso; unfold bv_eqb in K; rewrite Z.eqb_refl in K; cbn [negb] in K; discriminate K|].
  step. step.
  if_cases K1; cbv iota; [exfalso; unfold bv_eqb in K1; rewrite Z.eqb_refl in K1; cbn [negb] in K1; discriminate K1|].
  step. step. step.
  if_cases K2; cbv iota.
  - eapply PL. refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
  - zify_cond K2. step. step.
    eapply LP; [lia | lia | f_equal; lia | reflexivity | f_equal; lia |].
    refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
Qed.

End Walk.

Theorem check_declared_holds : strcmp_contract -> check_declared_contract.
Proof.
  intros HSC. unfold check_declared_contract, check_declared_pre, CHECK_DECLARED, CHECK_DECLARED_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo gv wv
    gt wt (Hgot & Hwant & Hgv & Hwv & Hcap & Htab0 & Htab16 & HRT & HG & HAT & Hn & Hmt0 & Hmt16 & HMT & HAM & Hwl &
           Hmn & HV & HST & MI).
  destruct HRT as (bt & HBT & HET). destruct HMT as (bm & HBM & HEM).
  destruct HST as (ST & HK & _ & _).
  destruct (vlans_are_spec _ _ _ _ _ HV) as (Egw & HL & HC & HE).
  unfold guard_at, RVLAN_SIZE in HG. unfold apart, RVLAN_SIZE, MVLAN_SIZE in HAT, HAM.
  assert (E01 : a1 = a0) by (apply bv_eq; rewrite Hgot, Hwant, Egw; reflexivity).
  assert (E35 : a5 = a3) by (apply bv_eq; rewrite Hn, Hmn, HL; reflexivity).
  subst a1 a5.
  pose proof (u64_range sp) as Rsp. pose proof (proj1 ST) as Hlo.
  rewrite <- (Z_to_bv_lit_self a3), Hn.
  pose proof (Z_to_bv_lit_self sp) as Esp. pose proof (Z_to_bv_lit_self a2) as Ea2.
  pose proof (Z_to_bv_lit_self a4) as Ea4. pose proof (Z_to_bv_lit_self a6) as Ea6.
  set (Sp := bv_unsigned sp) in *. set (tab := bv_unsigned a2) in *. set (mt := bv_unsigned a4) in *.
  set (cap := bv_unsigned a6) in *.
  rewrite <- Esp, <- Ea2, <- Ea4, <- Ea6. clearbody Sp tab mt cap. clear Esp Ea2 Ea4 Ea6.
  eapply body; first [eassumption | lia].
Qed.
