(** check_declared (UBSan build, 0x14e0c, 96-byte frame): proof of [check_declared_contract]
    (U/Prog/check_declared_c.v) from the contract of its callee strcmp (U/Prog/strcmp_c.v, 0x1f594).

    Code (image 1696d6c34ffd):
      0x14e0c-0x14e38  frame of 96: ra s0-s9 at sp+88 .. sp+8 (sp+0 .. sp+8 not written)
      0x14e3c bne a0,a1 -> abort; 0x14e40 bne a3,a5 -> abort; s1 = cap; s0 = tab; s3 = ~tab; 0x14e50 blez a3 -> GUARD
      s2 = mt; s4 = 0; s5 = 0; s6 = ~mt; s7 = tab & 1; s8 = 18 n; s9 = mt & 3
      LOOP 0x14e74 (s5 = 18 i, s4 = 20 i): bltu s3,s5 -> trap; bnez s7 -> trap; bltu s6,s4 -> trap; bnez s9 -> trap;
           lhu a2,16(tab + s5); lw a3,16(mt + s4); bne a3,a2 -> abort; strcmp(tab + s5, mt + s4); bnez a0 -> abort;
           s5 += 18; s4 += 20; bne s8,s5 -> LOOP
      GUARD 0x14eac: a0 = 18 cap; bltu s3,a0 -> trap; s0 = tab + 18 cap; a1 = ~s0; a2 = 17; a3 = 0;
           0x14ecc bltu a1,a3 -> trap; lbu a5,0(s0 + a3); bne a5,0x5a -> 0x14ee8; a3 += 1; bne a4,a2 -> 0x14ecc
      0x14ee8 bne a5,0x5a -> abort; 0x14ef0 restore; ret.
    The abort branches (`jal abort` at 0x14f28) are dead as in the plain walk (Prog/check_declared.v). The traps
    (`unimp` at 0x14f24) are dead too: tab and mt are 16-aligned, and every pointer the loops form lies inside the
    tables or the guard entry, which bytes_at keeps below 2^64, so no `bltu ~p, off` is taken. The lemmas on the
    model and the byte views are the plain walk's, repeated here so this file does not load the plain image. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import strcmp_c check_declared_c.
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

(** The alignment checks: the low bits of a 16-aligned address are 0. *)
Lemma land1_16 : forall t, t mod 16 = 0 -> Z.land t 1 = 0.
Proof.
  intros t H. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  Z.div_mod_to_equations. lia.
Qed.

Lemma land3_16 : forall t, t mod 16 = 0 -> Z.land t 3 = 0.
Proof.
  intros t H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
  Z.div_mod_to_equations. lia.
Qed.

(** A register equation at a loop entry: unfold the literals, ~x and the alignment masks. *)
Ltac weq := rewrite ?unsigned_lit by lia; rewrite ?zb_lxor_ones by lia; rewrite ?land1_16, ?land3_16 by assumption;
  first [reflexivity | f_equal; lia].

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
Hypothesis HT16 : tab mod 16 = 0.
Hypothesis HM16 : mt mod 16 = 0.
Hypothesis HL : length gt = length wt.
Hypothesis HC : Z.of_nat (length gt) <= cap.
Hypothesis HC40 : 0 <= cap < 40.
Hypothesis HE : forall i, (i < length gt)%nat -> snd (nth i gt ([], 0)) = snd (nth i wt ([], 0)) /\
  SegModel.strcmp (fst (nth i gt ([], 0))) (fst (nth i wt ([], 0))) = 0.
Hypothesis HAT : tab + 18 * (cap + 1) <= lo \/ Sp <= tab.
Hypothesis HAM : mt + 20 * (cap + 1) <= lo \/ Sp <= mt.
Hypothesis Hlo : 0 <= lo.
Hypothesis HK : lo + 96 <= Sp.
Hypothesis HS : Sp < 2 ^ 64.

Local Abbreviation Post :=
  (ret_void rsegs ra (Z_to_bv 64 Sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 [(Sp - 96, Sp)] lo
     (fun _ => True)).

(** The frame between the prologue and the epilogue (its first 8 bytes are not written). *)
Definition frm (m : word -> option byte) : Prop :=
  (exists j, rw_cells rsegs m (Sp + -96)
               [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
  stk rsegs m lo (Sp + -96) /\ munch [(Sp - 96, Sp)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m.

Lemma bt_len : length bt = (18 * length gt)%nat.
Proof. destruct HET as [L _]. exact L. Qed.
Lemma bm_len : length bm = (20 * length wt)%nat.
Proof. destruct HEM as [L _]. exact L. Qed.

(** The tables and the guard entry lie inside the address space. *)
Lemma bounds : 0 <= tab /\ tab + 18 * Z.of_nat (length gt) <= 2 ^ 64 /\ tab + 18 * cap + 18 <= 2 ^ 64 /\
  0 <= mt /\ mt + 20 * Z.of_nat (length gt) <= 2 ^ 64.
Proof.
  pose proof (bytes_at_bound _ _ _ _ HG) as GB. change (Z.of_nat (length GUARD_BYTES)) with 18 in GB.
  pose proof (bytes_at_bound _ _ _ _ HBT) as TB. pose proof (bytes_at_bound _ _ _ _ HBM) as MB.
  rewrite bt_len in TB. rewrite bm_len, <- HL in MB. lia.
Qed.

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

(** The exit 0x14ef0: restore ra and s0-s9, return. *)
Lemma epi : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
                      x28 x29 x30 x31 : word),
  frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -96)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x14ef0) fc None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31
    ((j & FR) & ST & MU & WM & MI).
  do 13 step.
  apply evt_done. unfold ret_void.
  exists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m.
  split; [unfold mkR; repeat f_equal; lia|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [|exact I].
  pose proof (stk_release rsegs m lo (Sp + -96) _ ST FR ltac:(lia)) as R. cbn [cells_size csize Nat.add] in R.
  rewrite unsigned_lit by lia. replace (Sp + -96 + Z.of_nat 96) with Sp in R by lia. exact R.
Qed.

(** The guard loop 0x14ecc at byte j of tab[cap] (k = 17 - j bytes after it): s0 = tab + 18 cap, a0 = 0x5a,
    a1 = ~s0, a2 = 17, a3 = j. Every byte is 0x5a and s0 + j does not wrap, so the loop runs to its 18th byte. *)
Lemma gloop : forall k j m (x1 x5 x6 x7 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31
                         w8 w10 w11 w12 w13 : word),
  (j + k = 17)%nat -> w8 = Z_to_bv 64 (tab + 18 * cap) -> w10 = Z_to_bv 64 90 ->
  w11 = Z_to_bv 64 (18446744073709551615 - (tab + 18 * cap)) -> w12 = Z_to_bv 64 17 ->
  w13 = Z_to_bv 64 (Z.of_nat j) -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -96)) gp tp x5 x6 x7 w8 x9 w10 w11 w12 w13 x14 x15 x16 x17 x18 x19 x20
             x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x14ecc) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros j m x1 x5 x6 x7 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31
    w8 w10 w11 w12 w13 Hjk E8 E10 E11 E12 E13 FRM; subst w8 w10 w11 w12 w13;
    pose proof (guard_read rsegs m (tab + 18 * cap) j (frm_g m FRM) ltac:(lia)) as RD;
    pose proof bounds as BD.
  - step. if_cases K; cbv iota; [exfalso; zify_cond K; lia|].
    step. step. step. step. if_cases K1; cbv iota; [exfalso; vm_compute in K1; discriminate K1|].
    step. step. if_cases K2; cbv iota; [exfalso; zify_cond K2; lia|].
    step. step. if_cases K3; cbv iota; [exfalso; vm_compute in K3; discriminate K3|].
    eapply epi. exact FRM.
  - step. if_cases K; cbv iota; [exfalso; zify_cond K; lia|].
    step. step. step. step. if_cases K1; cbv iota; [exfalso; vm_compute in K1; discriminate K1|].
    step. step. if_cases K2; cbv iota; [|exfalso; zify_cond K2; lia].
    eapply (IH (S j)); [lia | reflexivity | reflexivity | reflexivity | reflexivity | f_equal; lia | exact FRM].
Qed.

(** 0x14eac, after the entry loop: a0 = 18 cap, the trap check on tab + 18 cap, then the guard loop at byte 0. *)
Lemma post_loop : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31
                           w19 : word),
  w19 = Z_to_bv 64 (18446744073709551615 - tab) -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 tab) (Z_to_bv 64 cap) x10 x11 x12 x13 x14 x15
             x16 x17 x18 w19 x20 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x14eac) fc None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 w19 E19 FRM.
  subst w19. pose proof bounds as BD.
  step. step. rewrite ?(unsigned_lit cap) by lia.
  step. if_cases K; cbv iota; [exfalso; zify_cond K; lia|].
  do 5 step.
  eapply (gloop 17 0); [lia | weq | reflexivity | weq | reflexivity | reflexivity | exact FRM].
Qed.

(** The entry loop 0x14e74 at entry i (k = n - i entries left): s3 = ~tab, s4 = 20 i, s5 = 18 i, s6 = ~mt,
    s7 = tab & 1 = 0, s8 = 18 n, s9 = mt & 3 = 0. No trap is taken, the vids agree and strcmp returns 0. *)
Lemma mloop : forall k i m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
                         w19 w20 w21 w22 w23 w24 w25 : word),
  (i + k = length gt)%nat -> (0 < k)%nat ->
  w19 = Z_to_bv 64 (18446744073709551615 - tab) -> w20 = Z_to_bv 64 (20 * Z.of_nat i) ->
  w21 = Z_to_bv 64 (18 * Z.of_nat i) -> w22 = Z_to_bv 64 (18446744073709551615 - mt) -> w23 = Z_to_bv 64 0 ->
  w24 = Z_to_bv 64 (18 * Z.of_nat (length gt)) -> w25 = Z_to_bv 64 0 -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 tab) (Z_to_bv 64 cap) x10 x11 x12 x13 x14 x15
             x16 x17 (Z_to_bv 64 mt) w19 w20 w21 w22 w23 w24 w25 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x14e74) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros i m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
    w19 w20 w21 w22 w23 w24 w25 Hik Hk E19 E20 E21 E22 E23 E24 E25 FRM; [lia|].
  subst w19 w20 w21 w22 w23 w24 w25.
  assert (Hi : (i < length gt)%nat) by lia. assert (Hiw : (i < length wt)%nat) by lia.
  destruct (HE i Hi) as [EV ES].
  destruct (rtab_entry rsegs m tab gt bt i (frm_bt m FRM) HET Hi) as (RD1 & RV1 & sx & BX & ZX & NX).
  destruct (mtab_entry rsegs m mt wt bm i (frm_bm m FRM) HEM Hiw) as (RD2 & RV2 & sy & BY & ZY & NY).
  pose proof bounds as BD.
  step. if_cases K; cbv iota; [exfalso; zify_cond K; lia|].
  step. if_cases K0; cbv iota; [exfalso; vm_compute in K0; discriminate K0|].
  step. if_cases K1; cbv iota; [exfalso; zify_cond K1; lia|].
  step. if_cases K2; cbv iota; [exfalso; vm_compute in K2; discriminate K2|].
  step. step. step. step.
  rewrite (zx16_small _ RV1). rewrite (sx32_small (snd (nth i wt ([], 0)))) by lia.
  step. if_cases K3; cbv iota; [exfalso; zify_cond K3; lia|].
  step.
  eapply evt_cut.
  { eapply HSC with (sx := sx) (sy := sy); rewrite ?unsigned_lit by lia; assumption. }
  intros ms' (r & y11 & y12 & y13 & -> & Hr).
  rewrite ret_pc_even by (try lia; reflexivity).
  assert (R0 : r = Z_to_bv 64 0).
  { apply Hr. apply bridge_strcmp; [exact NX | exact NY |]. rewrite ZX, ZY. exact ES. }
  subst r.
  step. if_cases K4; cbv iota; [exfalso; vm_compute in K4; discriminate K4|].
  step. step. step.
  if_cases K5; cbv iota.
  - zify_cond K5.
    eapply (IH (S i)); [lia | lia | reflexivity | f_equal; lia | f_equal; lia | reflexivity | reflexivity |
                        reflexivity | reflexivity | exact FRM].
  - eapply post_loop; [reflexivity | exact FRM].
Qed.

(** The whole function from its entry. *)
Lemma body : forall (t0 t1 t2 a0 a7 t3 t4 t5 t6 : word),
  stk rsegs m0 lo Sp -> mem_inv rsegs m0 ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 a0 a0 (Z_to_bv 64 tab) (Z_to_bv 64 (Z.of_nat (length gt)))
             (Z_to_bv 64 mt) (Z_to_bv 64 (Z.of_nat (length gt))) (Z_to_bv 64 cap) a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14e0c) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a7 t3 t4 t5 t6 ST MI.
  (* The prologue's stores transport (and so replace) the section hypotheses the loops need: take them first. *)
  pose proof (mloop (length gt) 0) as LP. pose proof post_loop as PL. pose proof bounds as BD.
  pose proof (munch_refl [(Sp - 96, Sp)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  destruct (stk_carve rsegs m0 lo Sp 96 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
  change (Z.of_nat 96) with 96 in ST1, FR.
  replace (Sp - 96) with (Sp + -96) in ST1, FR by lia.
  do 12 step.
  step. if_cases K; cbv iota; [exfalso; unfold bv_eqb in K; rewrite Z.eqb_refl in K; cbn [negb] in K; discriminate K|].
  step.
  if_cases K1; cbv iota; [exfalso; unfold bv_eqb in K1; rewrite Z.eqb_refl in K1; cbn [negb] in K1; discriminate K1|].
  step. step. step. step.
  if_cases K2; cbv iota.
  - eapply PL; [weq|]. split; [eexists; eassumption|]. refine (conj _ (conj _ (conj _ _))); eassumption.
  - zify_cond K2. do 8 step.
    eapply LP; [lia | lia | weq | weq | weq | weq | weq | weq | weq |].
    split; [eexists; eassumption|]. refine (conj _ (conj _ (conj _ _))); eassumption.
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
