(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/mbedtls/fuzz_pkcs7/lib/Lib/Asn1Aux.v; 1278 of its 1342 lines of code are new or changed and 385 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel RcLeaf RcLeafLib RcParse CtrlParsed.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_classify_c classify_core_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_ctrl_parse_c bcmp_c reac_ctrl_checksum_verify_c memset_c reac_ports_parse_c.
Import ListNotations.
Open Scope Z_scope.

Lemma cc_wr_split : forall m A n1 n2, wr_at rsegs m A (n1 + n2) -> 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 (H1 & H2 & H) P1 P2. split.
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
Qed.

Lemma cc_wr_join : forall m A n1 n2, wr_at rsegs m A n1 -> wr_at rsegs m (A + n1) n2 -> 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2).
Proof.
  intros m A n1 n2 (H1 & H2 & H) (G1 & G2 & G) P1 P2. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z.ltb_spec0 i n1); [apply H; lia|].
  replace (A + i) with (A + n1 + (i - n1)) by lia. apply G. lia.
Qed.

Lemma cc_rw_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app, Nat2Z.inj_add in Hw.
  apply cc_wr_split in Hw; [| lia | lia]. destruct Hw as [V1 V2].
  rewrite cells_bytes_length in B2 by exact W1.
  split; (split; [split|]); assumption.
Qed.

Lemma cc_rw_app : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] V1] [[W2 B2] V2].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app, Nat2Z.inj_add. apply cc_wr_join; [exact V1 | exact V2 | lia | lia].
Qed.

Lemma cc_rw_conv : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] V] W' EB ES. split; [split|].
  - exact W'.
  - rewrite EB. exact B.
  - rewrite ES. exact V.
Qed.

Lemma cc_rw_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ B] _]. exact B. Qed.

Lemma cc_rw_nil : forall m, rw_cells rsegs m 0 [CB 0 []].
Proof.
  intros m. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn. apply bytes_at_nil. lia.
  - cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma cc_stk_rel : forall m lo A cs B, stk rsegs m lo A -> rw_cells rsegs m A cs -> lo <= A ->
  B = A + Z.of_nat (cells_size cs) -> stk rsegs m lo B.
Proof. intros m lo A cs B HS R H ->. eapply stk_release; eassumption. Qed.

Definition cc_lock (FB U : list byte) (len lk : Z) (L : option (list byte)) (lkA : Z) (nL : nat) (LKb : list byte)
    : Prop :=
  match cm_lock FB len U L with
  | None => lkA = 0 /\ nL = 0%nat /\ LKb = []
  | Some Lb' => lkA = lk /\ nL = 12%nat /\ LKb = Lb'
  end.

Lemma cc_lock_fin : forall m FB U len lk L lkA nL LKb, cc_lock FB U len lk L lkA nL LKb ->
  rw_cells rsegs m lkA [CB nL LKb] ->
  match cm_lock FB len U L with None => True | Some Lb' => rw_cells rsegs m lk [CB 12 Lb'] end.
Proof.
  intros m FB U len lk L lkA nL LKb H R. unfold cc_lock in H.
  destruct (cm_lock FB len U L); [destruct H as (-> & -> & ->); exact R | exact I].
Qed.

Notation ccW sp o lk L :=
  ((bv_unsigned sp - 192, bv_unsigned sp) :: (o, o + 24) :: match L with None => [] | Some _ => [(lk, lk + 12)] end).

Lemma cc_fin : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo lk len o : Z) (FB U OB : list byte) (L : option (list byte))
    (xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 : word)
    (m : word -> option byte) (w q : list byte),
  xsp = Z_to_bv 64 (bv_unsigned sp + -112) -> xs5 = Z_to_bv 64 (cm_ret FB len U L) ->
  0 <= lo -> lo + 192 <= bv_unsigned sp ->
  stk rsegs m lo (bv_unsigned sp + -112) ->
  rw_cells rsegs m (bv_unsigned sp + -112) [CB 12 w] ->
  rw_cells rsegs m (bv_unsigned sp + -100) [CB 36 q] ->
  rw_cells rsegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch (ccW sp o lk L) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m o [CB 24 (cm_out FB len U L OB)] ->
  match cm_lock FB len U L with None => True | Some Lb' => rw_cells rsegs m lk [CB 12 Lb'] end ->
  evt rsegs (classify_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk len o FB U OB L)
    (MS (mkR xra xsp gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11
             xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x1538c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk len o FB U OB L
    xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 m w q
    ESP ES5 Hlo HloS ST FW FQ FS MU WM MI HO HL.
  subst xsp xs5.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  do 11 step.
  pose proof (cc_stk_rel _ _ _ _ (bv_unsigned sp + -100) ST FW ltac:(lia) ltac:(cbn; lia)) as ST1.
  pose proof (cc_stk_rel _ _ _ _ (bv_unsigned sp + -64) ST1 FQ ltac:(lia) ltac:(cbn; lia)) as ST2.
  pose proof (cc_stk_rel _ _ _ _ (bv_unsigned sp) ST2 FS ltac:(lia) ltac:(cbn; lia)) as ST3.
  apply evt_done. unfold classify_core_post.
  do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST3|]. split; [exact HO | exact HL].
Qed.

Lemma cc_join : forall m A cs1 cs2 B n bs, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> n = (cells_size cs1 + cells_size cs2)%nat ->
  bs = cells_bytes cs1 ++ cells_bytes cs2 -> rw_cells rsegs m A [CB n bs].
Proof.
  intros m A cs1 cs2 B n bs H1 H2 -> -> ->.
  pose proof (cc_rw_app m A cs1 cs2 H1 H2) as H.
  pose proof (proj1 (proj1 H1)) as W1. pose proof (proj1 (proj1 H2)) as W2.
  eapply cc_rw_conv; [exact H | | | ].
  - cbn [cells_wf cell_wf]. split; [| exact I]. rewrite length_app, !cells_bytes_length by assumption. reflexivity.
  - cbn [cells_bytes cbytes]. rewrite cells_bytes_app, app_nil_r. reflexivity.
  - cbn [cells_size csize]. rewrite cells_size_app. lia.
Qed.

Definition sgA (F : list byte) (len : Z) : list byte :=
  src F ++ [zb 0; zb 0] ++ le4 (Z_to_bv 64 (role F (dkind F len))).
Definition sgD (F : list byte) : list byte :=
  match sdecl F with Some (i, o) => [zb 1; zb i; zb o] | None => [zb 0; zb 0; zb 0] end.
Definition sgS (F : list byte) : list byte := [zb 0; zb (slots F); zb 0; zb 0; zb 0].

Lemma sight_parts : forall F len, sight F len = sgA F len ++ sgD F ++ sgS F ++ le4 (Z_to_bv 64 (geo len)).
Proof. intros F len. unfold sight, sgA, sgD, sgS. rewrite <- !app_assoc. reflexivity. Qed.

Lemma cc_div36 : forall x, 0 <= x < 2^64 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr (x * 16397105843297379215) 64))) 5 = x / 36.
Proof.
  intros x Hx.
  assert (H64 : 0 <= Z.shiftr (x * 16397105843297379215) 64 < 2^64).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite (unsigned_lit _ H64). rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
  change (2 ^ 64 * 2 ^ 5) with 590295810358705651712.
  assert (E : x = 36 * (x / 36) + x mod 36) by (apply Z.div_mod; lia).
  pose proof (Z.mod_pos_bound x 36 ltac:(lia)) as Hr.
  symmetry. apply Z.div_unique with (r := x * 16397105843297379215 - 590295810358705651712 * (x / 36)); [left | ]; lia.
Qed.

Lemma cc_geo_val : forall x, 0 <= x < 2^64 ->
  Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0)
      (Z_to_bv 64 (x - bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned
         (Z_to_bv 64 (Z.shiftr (x * 16397105843297379215) 64))) 5)) * 36))))) + -1)))
    (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr (x * 16397105843297379215) 64))) 5)))
  = if x mod 36 =? 0 then x / 36 else 0.
Proof.
  intros x Hx. rewrite cc_div36 by exact Hx.
  assert (Hq : 0 <= x / 36 < 2^64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (unsigned_lit (x / 36)) by exact Hq.
  rewrite (unsigned_lit (x / 36 * 36)) by lia.
  replace (x - x / 36 * 36) with (x mod 36) by (rewrite (Z.mod_eq x 36) by lia; lia).
  pose proof (Z.mod_pos_bound x 36 ltac:(lia)) as Hr.
  unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit (x mod 36)) by lia.
  change (bv_unsigned (Z_to_bv 64 0)) with 0.
  destruct (Z.eqb_spec (x mod 36) 0) as [E|E].
  - rewrite E. change (0 <? 0) with false. change (0 =? 0) with true. cbv iota.
    change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + -1))) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. exact Hq.
  - replace (0 <? x mod 36) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (x mod 36 =? 0) with false by (symmetry; apply Z.eqb_neq; exact E). cbv iota.
    change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) + -1))) with 0. apply Z.land_0_l.
Qed.

Lemma cc_geo_le4 : forall len, 52 <= len < 2^64 ->
  le4 (Z_to_bv 64 (if (len + -52) mod 36 =? 0 then (len + -52) / 36 else 0)) = le4 (Z_to_bv 64 (geo len)).
Proof.
  intros len H. unfold geo. replace (52 <=? len) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
  replace (len - 52) with (len + -52) by lia.
  destruct ((len + -52) mod 36 =? 0); [|reflexivity].
  assert (Hq : 0 <= (len + -52) / 36 < 2^64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold le4. rewrite (unsigned_lit ((len + -52) / 36)) by exact Hq.
  rewrite (unsigned_lit (((len + -52) / 36) mod 2^32)) by (pose proof (Z.mod_pos_bound ((len + -52)/36) (2^32)); lia).
  symmetry. apply Z_to_le_bytes_mod. cbn. lia.
Qed.

Lemma cc_geo0 : forall len, len < 52 -> geo len = 0.
Proof. intros len H. unfold geo. replace (52 <=? len) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. Qed.

Lemma cc_geo : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo lk len o : Z) (FB U OB : list byte) (L : option (list byte))
    (xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 : word)
    (m : word -> option byte) (w q j4 : list byte) (lkA : Z) (nL : nat) (LKb : list byte),
  xsp = Z_to_bv 64 (bv_unsigned sp + -112) -> xs0 = Z_to_bv 64 o -> xs1 = Z_to_bv 64 len ->
  cm_ret FB len U L = 0 -> cm_out FB len U L OB = sight FB len -> cc_lock FB U len lk L lkA nL LKb ->
  0 <= lo -> lo + 192 <= bv_unsigned sp -> 50 <= len < 2^64 -> 0 < o -> o + 24 <= 2^64 ->
  o + 24 <= bv_unsigned sp - 192 \/ bv_unsigned sp <= o ->
  lkA + Z.of_nat nL <= o \/ o + 24 <= lkA ->
  lkA + Z.of_nat nL <= bv_unsigned sp - 192 \/ bv_unsigned sp <= lkA ->
  stk rsegs m lo (bv_unsigned sp + -112) ->
  rw_cells rsegs m (bv_unsigned sp + -112) [CB 12 w] ->
  rw_cells rsegs m (bv_unsigned sp + -100) [CB 36 q] ->
  rw_cells rsegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch (ccW sp o lk L) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m o [CB 20 (sgA FB len ++ sgD FB ++ sgS FB)] -> rw_cells rsegs m (o + 20) [CB 4 j4] ->
  rw_cells rsegs m lkA [CB nL LKb] ->
  evt rsegs (classify_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk len o FB U OB L)
    (MS (mkR xra xsp gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11
             xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x15348) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk len o FB U OB L
    xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 m w q j4 lkA nL LKb
    ESP ES0 ES1 HR HO HLK Hlo HloS Hlen Ho Hoa Hof HLo HLf ST FW FQ FS MU WM MI O20 O4 RL.
  subst xsp xs0 xs1.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  assert (UL : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  step. step.
  destruct (Z.ltb_spec len 52) as [Hs|Hs].
  - if_false. step. step. step. step.
    eapply cc_fin; [reflexivity | rewrite HR; reflexivity | lia | lia | exact ST | exact FW | exact FQ | exact FS
                   | exact MU | exact WM | exact MI | | eapply cc_lock_fin; eassumption].
    rewrite HO. eapply cc_join; [exact O20 | exact O4 | cbn; lia | reflexivity | ].
    rewrite sight_parts, cc_geo0 by exact Hs. cbn [cells_bytes cbytes]. rewrite !app_nil_r, <- !app_assoc. reflexivity.
  - if_true. do 11 step.
    rewrite (unsigned_lit (len + -52)) by lia. rewrite cc_geo_val by lia.
    step. step.
    eapply cc_fin; [reflexivity | rewrite HR; reflexivity | lia | lia | exact ST | exact FW | exact FQ | exact FS
                   | exact MU | exact WM | exact MI | | eapply cc_lock_fin; eassumption].
    rewrite HO. eapply cc_join; [exact O20 | exact O4 | cbn; lia | reflexivity | ].
    rewrite sight_parts, <- (cc_geo_le4 len) by lia. cbn [cells_bytes cbytes]. rewrite !app_nil_r, <- !app_assoc.
    reflexivity.
Qed.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Lemma cc_sub : forall m A (bs : list byte) k n, bytes_at rsegs m A bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m A bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Init.Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma cc_rw_wr : forall m A n bs, rw_cells rsegs m A [CB n bs] -> wr_at rsegs m A (Z.of_nat n).
Proof. intros m A n bs [_ W]. cbn [cells_size csize] in W. rewrite Nat.add_0_r in W. exact W. 
Qed.

Lemma cc_flat : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof. intros m A cs H. apply (rw_cells_merge rsegs m A [] cs []). cbn [app]. rewrite app_nil_r. exact H. 
Qed.

Lemma cc_rw3 : forall m q a b c, bytes_at rsegs m q (le4 a) -> bytes_at rsegs m (q + 4) (le4 b) ->
  bytes_at rsegs m (q + 8) (le4 c) -> wr_at rsegs m q 12 -> rw_cells rsegs m q [C4 a; C4 b; C4 c].
Proof.
  intros m q a b c A B C W. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact A|].
    rewrite length_le4. apply bytes_at_app. split; [exact B|].
    rewrite length_le4. replace (q + Z.of_nat 4 + Z.of_nat 4) with (q + 8) by lia. exact C.
  - exact W.
Qed.

Lemma cc_sx32 : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal. rewrite bv_swrap32_eq. rewrite Z.mod_small by lia. lia.
Qed.

Lemma cc_pok : forall p q bs, p <> 0 -> q <> 0 -> ports_ok p q bs = decl bs.
Proof.
  intros p q bs Hp Hq. unfold ports_ok. rewrite (proj2 (Z.eqb_neq p 0) Hp), (proj2 (Z.eqb_neq q 0) Hq). reflexivity.
Qed.

Lemma cc_o20 : forall m o FB len D, rw_cells rsegs m o [CB 12 (sgA FB len)] -> rw_cells rsegs m (o + 12) D ->
  rw_cells rsegs m (o + 15) [CB 5 (sgS FB)] -> cells_size D = 3%nat -> cells_bytes D = sgD FB ->
  rw_cells rsegs m o [CB 20 (sgA FB len ++ sgD FB ++ sgS FB)].
Proof.
  intros m o FB len D H1 H2 H3 SD BD.
  assert (H12 : rw_cells rsegs m o [CB 15 (sgA FB len ++ sgD FB)]).
  { eapply cc_join; [exact H1 | exact H2 | cbn; lia | rewrite SD; reflexivity
                    | cbn [cells_bytes cbytes]; rewrite BD, app_nil_r; reflexivity]. }
  eapply cc_join; [exact H12 | exact H3 | cbn; lia | reflexivity
                  | cbn [cells_bytes cbytes]; rewrite !app_nil_r, app_assoc; reflexivity].
Qed.

Ltac cc_to_geo O20 :=
  eapply cc_geo; [reflexivity | reflexivity | reflexivity | eassumption | eassumption | eassumption
                 | lia | lia | lia | lia | lia | lia | lia | lia
                 | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
                 | exact O20 | eassumption | eassumption].

Lemma cc_ports : reac_ports_parse_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo lk f len o : Z) (FB U OB : list byte) (L : option (list byte))
    (xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 : word)
    (m : word -> option byte) (w q j4 : list byte) (lkA : Z) (nL : nat) (LKb : list byte),
  xsp = Z_to_bv 64 (bv_unsigned sp + -112) -> xs0 = Z_to_bv 64 o -> xs1 = Z_to_bv 64 len -> xs2 = Z_to_bv 64 f ->
  cm_ret FB len U L = 0 -> cm_out FB len U L OB = sight FB len -> cc_lock FB U len lk L lkA nL LKb ->
  bv_unsigned sp mod 16 = 0 ->
  0 <= lo -> lo + 192 <= bv_unsigned sp -> 50 <= len < 2^64 -> 0 < o -> o + 24 <= 2^64 ->
  o + 24 <= bv_unsigned sp - 192 \/ bv_unsigned sp <= o ->
  0 < f -> length FB = 50%nat -> f + 50 <= bv_unsigned sp - 192 \/ bv_unsigned sp <= f ->
  o + 24 <= f \/ f + 50 <= o ->
  lkA + Z.of_nat nL <= o \/ o + 24 <= lkA ->
  lkA + Z.of_nat nL <= bv_unsigned sp - 192 \/ bv_unsigned sp <= lkA ->
  stk rsegs m lo (bv_unsigned sp + -112) ->
  rw_cells rsegs m (bv_unsigned sp + -112) [CB 12 w] ->
  rw_cells rsegs m (bv_unsigned sp + -100) [CB 36 q] ->
  rw_cells rsegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch (ccW sp o lk L) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m f FB ->
  rw_cells rsegs m o [CB 12 (sgA FB len)] -> rw_cells rsegs m (o + 12) [CB 3 [zb 0; zb 0; zb 0]] ->
  rw_cells rsegs m (o + 15) [CB 5 (sgS FB)] -> rw_cells rsegs m (o + 20) [CB 4 j4] ->
  rw_cells rsegs m lkA [CB nL LKb] ->
  evt rsegs (classify_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk len o FB U OB L)
    (MS (mkR xra xsp gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11
             xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x15314) fc None m (seg_rom rsegs)).
Proof.
  intros PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk f len o FB U OB L
    xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 m w q j4 lkA nL LKb
    ESP ES0 ES1 ES2 HR HO HLK Hsp16 Hlo HloS Hlen Ho Hoa Hof Hf HFB Hff Hfo HLo HLf ST FW FQ FS MU WM MI FBm
    O12 OD OS O4 RL.
  subst xsp xs0 xs1 xs2.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bytes_at_bound _ _ _ _ FBm) as Hfb. rewrite HFB in Hfb. change (Z.of_nat 50) with 50 in Hfb.
  pose proof (cc_sub m f FB 18 20 FBm ltac:(lia)) as PB. change (f + Z.of_nat 18) with (f + 18) in PB.
  pose proof (cc_rw_wr _ _ _ _ FW) as WQ. change (Z.of_nat 12) with 12 in WQ.
  assert (LP : length (fld FB 18 20) = 20%nat) by (unfold fld; rewrite length_firstn, length_skipn, HFB; reflexivity).
  assert (NI : 0 <= n_in (fld FB 18 20) <= 12)
    by (unfold n_in; pose proof (rcl_cnt_range is_in (fld FB 18 20) 12); lia).
  assert (NO : 0 <= n_out (fld FB 18 20) <= 12)
    by (unfold n_out; pose proof (rcl_cnt_range is_out (fld FB 18 20) 12); lia).
  step. step. step.
  eapply evt_cut.
  { eapply PP with (p := f + 18) (q := bv_unsigned sp + -112) (bs := fld FB 18 20);
      [reflexivity | reflexivity | lia | lia | intros _ _; split; [exact LP | exact PB]
      | intros _ _; split; [Z.div_mod_to_equations; lia | split; [exact WQ | lia]]]. }
  intros ms' PO. unfold reac_ports_parse_post in PO.
  destruct PO as (t0' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & PO). subst ms'.
  rewrite (ret_pc_even 86816) by (first [lia | reflexivity]).
  rewrite cc_pok in PO |- * by lia.
  destruct (decl (fld FB 18 20)) eqn:HD.
  - destruct PO as (B1 & B2 & B3 & MUc & WMc & MIc). specialize (MIc MI).
    transport_after_call rsegs m m' MUc WMc. clear MUc WMc MI. rename MIc into MI.
    pose proof (cc_rw3 _ _ _ _ _ B1 B2 B3 WQ) as FW. clear B1 B2 B3.
    assert (UI : 0 <= 4 * n_in (fld FB 18 20) < 2^31) by lia.
    assert (UO : 0 <= 4 * n_out (fld FB 18 20) < 2^31) by lia.
    assert (UI' : bv_unsigned (Z_to_bv 64 (4 * n_in (fld FB 18 20))) = 4 * n_in (fld FB 18 20)) by (apply unsigned_lit; lia).
    assert (UO' : bv_unsigned (Z_to_bv 64 (4 * n_out (fld FB 18 20))) = 4 * n_out (fld FB 18 20)) by (apply unsigned_lit; lia).
    step. if_false. step. rewrite (cc_sx32 _ UI). step. step.
    destruct (Z.leb_spec (4 * n_in (fld FB 18 20)) 40) as [Ci|Ci].
    + if_false. step. rewrite (cc_sx32 _ UO). step.
      destruct (Z.leb_spec (4 * n_out (fld FB 18 20)) 40) as [Co|Co].
      * if_false. step. step. step. step.
        apply cc_flat in FW. cbn [cells_size csize Nat.add] in FW.
        pose proof (cc_o20 _ _ _ _ _ O12 OD OS eq_refl) as O20.
        cc_to_geo (O20 ltac:(unfold sgD, sdecl; cbv zeta; rewrite HD;
                             rewrite (proj2 (Z.leb_le _ _) Ci), (proj2 (Z.leb_le _ _) Co); cbn [andb cells_bytes cbytes app];
                             rewrite UI', UO'; reflexivity)).
      * if_true.
        apply cc_flat in FW. cbn [cells_size csize Nat.add] in FW.
        pose proof (cc_o20 _ _ _ _ _ O12 OD OS eq_refl) as O20.
        cc_to_geo (O20 ltac:(unfold sgD, sdecl; cbv zeta; rewrite HD;
                             rewrite (proj2 (Z.leb_le _ _) Ci), (proj2 (Z.leb_gt _ _) Co); reflexivity)).
    + if_true.
      apply cc_flat in FW. cbn [cells_size csize Nat.add] in FW.
      pose proof (cc_o20 _ _ _ _ _ O12 OD OS eq_refl) as O20.
      cc_to_geo (O20 ltac:(unfold sgD, sdecl; cbv zeta; rewrite HD, (proj2 (Z.leb_gt _ _) Ci); reflexivity)).
  - subst m'. step. if_true.
    pose proof (cc_o20 _ _ _ _ _ O12 OD OS eq_refl) as O20.
    cc_to_geo (O20 ltac:(unfold sgD, sdecl; cbv zeta; rewrite HD; reflexivity)).
Qed.

Lemma cc_rd : forall m f FB (i : nat), bytes_at rsegs m f FB -> (i < length FB)%nat ->
  ov_read_bytes rsegs m (wa (f + Z.of_nat i)) 1 = Some [nth i FB (zb 0)].
Proof. intros m f FB i H Hi. apply rcl_rd with (bs := FB); [exact H|]. apply nth_error_nth'. exact Hi. Qed.

Lemma cc_zb_ub : forall b : byte, zb (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. unfold zb. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma cc_slots0 : forall F, fb F 16 <> 207 \/ fb F 17 <> 234 \/ fb F 22 <> 1 \/ fb F 23 <> 3 \/ fb F 24 <> 13 \/
  fb F 25 <> 1 \/ fb F 26 <> 4 -> slots F = 0.
Proof.
  intros F H. unfold slots.
  destruct H as [H|[H|[H|[H|[H|[H|H]]]]]]; rewrite (proj2 (Z.eqb_neq _ _) H);
    rewrite ?andb_false_r, ?andb_false_l; reflexivity.
Qed.

Lemma cc_slots1 : forall F, fb F 16 = 207 -> fb F 17 = 234 -> fb F 22 = 1 -> fb F 23 = 3 -> fb F 24 = 13 ->
  fb F 25 = 1 -> fb F 26 = 4 -> slots F = fb F 33.
Proof. intros F E1 E2 E3 E4 E5 E6 E7. unfold slots. rewrite E1, E2, E3, E4, E5, E6, E7. reflexivity. Qed.

Lemma cc_o12 : forall m o FB len, rw_cells rsegs m o [CB 6 (src FB)] -> rw_cells rsegs m (o + 6) [CB 2 [zb 0; zb 0]] ->
  rw_cells rsegs m (o + 8) [C4 (Z_to_bv 64 (role FB (dkind FB len)))] -> rw_cells rsegs m o [CB 12 (sgA FB len)].
Proof.
  intros m o FB len H1 H2 H3.
  assert (H12 : rw_cells rsegs m o [CB 8 (src FB ++ [zb 0; zb 0])]).
  { eapply cc_join; [exact H1 | exact H2 | cbn; lia | reflexivity | cbn [cells_bytes cbytes]; rewrite !app_nil_r; reflexivity]. }
  eapply cc_join; [exact H12 | exact H3 | cbn; lia | reflexivity | ].
  unfold sgA. cbn [cells_bytes cbytes]. rewrite !app_nil_r, <- app_assoc. reflexivity.
Qed.

Lemma cc_os0 : forall m o F, slots F = 0 -> rw_cells rsegs m (o + 15) [CB 5 [zb 0; zb 0; zb 0; zb 0; zb 0]] ->
  rw_cells rsegs m (o + 15) [CB 5 (sgS F)].
Proof. intros m o F E H. unfold sgS. rewrite E. exact H. Qed.

Lemma cc_os1 : forall m o F a b c, rw_cells rsegs m (o + 15) [CB 1 a; C1 b; CB 3 c] -> a = [zb 0] ->
  c = [zb 0; zb 0; zb 0] -> zb (slots F) = b -> rw_cells rsegs m (o + 15) [CB 5 (sgS F)].
Proof.
  intros m o F a b c H -> -> E. eapply cc_rw_conv; [exact H | split; [reflexivity | exact I] | | reflexivity].
  unfold sgS. rewrite E. reflexivity.
Qed.

Ltac cc_to_ports PP O12 OS :=
  eapply (cc_ports PP); [reflexivity | reflexivity | reflexivity | reflexivity | eassumption | eassumption | eassumption
                        | lia | lia | lia | lia | lia | lia | lia | lia | eassumption | lia | lia | lia | lia
                        | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
                        | eassumption | exact O12 | eassumption | exact OS | eassumption | eassumption].

Lemma cc_tail : reac_ports_parse_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo lk f len o : Z) (FB U OB : list byte) (L : option (list byte))
    (xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 : word)
    (m : word -> option byte) (w q j4r j4 : list byte) (lkA : Z) (nL : nat) (LKb : list byte),
  xsp = Z_to_bv 64 (bv_unsigned sp + -112) -> xs0 = Z_to_bv 64 o -> xs1 = Z_to_bv 64 len -> xs2 = Z_to_bv 64 f ->
  xa0 = Z_to_bv 64 (role FB (dkind FB len)) ->
  cm_ret FB len U L = 0 -> cm_out FB len U L OB = sight FB len -> cc_lock FB U len lk L lkA nL LKb ->
  bv_unsigned sp mod 16 = 0 ->
  0 <= lo -> lo + 192 <= bv_unsigned sp -> 50 <= len < 2^64 -> 0 < o -> o + 24 <= 2^64 ->
  o + 24 <= bv_unsigned sp - 192 \/ bv_unsigned sp <= o ->
  0 < f -> length FB = 50%nat -> f + 50 <= bv_unsigned sp - 192 \/ bv_unsigned sp <= f ->
  o + 24 <= f \/ f + 50 <= o ->
  lkA + Z.of_nat nL <= o \/ o + 24 <= lkA ->
  lkA + Z.of_nat nL <= bv_unsigned sp - 192 \/ bv_unsigned sp <= lkA ->
  stk rsegs m lo (bv_unsigned sp + -112) ->
  rw_cells rsegs m (bv_unsigned sp + -112) [CB 12 w] ->
  rw_cells rsegs m (bv_unsigned sp + -100) [CB 36 q] ->
  rw_cells rsegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch (ccW sp o lk L) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m f FB ->
  rw_cells rsegs m o [CB 6 (src FB)] -> rw_cells rsegs m (o + 6) [CB 2 [zb 0; zb 0]] ->
  rw_cells rsegs m (o + 8) [CB 4 j4r] -> rw_cells rsegs m (o + 12) [CB 3 [zb 0; zb 0; zb 0]] ->
  rw_cells rsegs m (o + 15) [CB 5 [zb 0; zb 0; zb 0; zb 0; zb 0]] -> rw_cells rsegs m (o + 20) [CB 4 j4] ->
  rw_cells rsegs m lkA [CB nL LKb] ->
  evt rsegs (classify_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk len o FB U OB L)
    (MS (mkR xra xsp gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11
             xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x152ac) fc None m (seg_rom rsegs)).
Proof.
  intros PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk f len o FB U OB L
    xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 m w q j4r j4 lkA nL LKb
    ESP ES0 ES1 ES2 EA0 HR HO HLK Hsp16 Hlo HloS Hlen Ho Hoa Hof Hf HFB Hff Hfo HLo HLf ST FW FQ FS MU WM MI FBm
    O6 O2 O4r OD OS O4 RL.
  subst xsp xs0 xs1 xs2 xa0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bytes_at_bound _ _ _ _ FBm) as Hfb. rewrite HFB in Hfb. change (Z.of_nat 50) with 50 in Hfb.
  assert (UL : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  step. step. step. if_false.
  pose proof (cc_o12 _ _ _ _ O6 O2 O4r) as O12. clear O6 O2 O4r.
  pose proof (cc_rd _ f FB 16 FBm ltac:(lia)) as R16. pose proof (cc_rd _ f FB 17 FBm ltac:(lia)) as R17.
  pose proof (cc_rd _ f FB 22 FBm ltac:(lia)) as R22. pose proof (cc_rd _ f FB 23 FBm ltac:(lia)) as R23.
  pose proof (cc_rd _ f FB 24 FBm ltac:(lia)) as R24. pose proof (cc_rd _ f FB 25 FBm ltac:(lia)) as R25.
  pose proof (cc_rd _ f FB 26 FBm ltac:(lia)) as R26. pose proof (cc_rd _ f FB 33 FBm ltac:(lia)) as R33.
  change (Z.of_nat 16) with 16 in R16. change (Z.of_nat 17) with 17 in R17.
  change (Z.of_nat 22) with 22 in R22. change (Z.of_nat 23) with 23 in R23.
  change (Z.of_nat 24) with 24 in R24. change (Z.of_nat 25) with 25 in R25.
  change (Z.of_nat 26) with 26 in R26. change (Z.of_nat 33) with 33 in R33.
  assert (Z16 : bv_unsigned (zxb (nth 16 FB (zb 0))) = fb FB 16) by (unfold zxb, fb; apply unsigned_lit; pose proof (byte_range (nth 16 FB (zb 0))); lia).
  assert (Z17 : bv_unsigned (zxb (nth 17 FB (zb 0))) = fb FB 17) by (unfold zxb, fb; apply unsigned_lit; pose proof (byte_range (nth 17 FB (zb 0))); lia).
  assert (Z22 : bv_unsigned (zxb (nth 22 FB (zb 0))) = fb FB 22) by (unfold zxb, fb; apply unsigned_lit; pose proof (byte_range (nth 22 FB (zb 0))); lia).
  assert (Z23 : bv_unsigned (zxb (nth 23 FB (zb 0))) = fb FB 23) by (unfold zxb, fb; apply unsigned_lit; pose proof (byte_range (nth 23 FB (zb 0))); lia).
  assert (Z24 : bv_unsigned (zxb (nth 24 FB (zb 0))) = fb FB 24) by (unfold zxb, fb; apply unsigned_lit; pose proof (byte_range (nth 24 FB (zb 0))); lia).
  assert (Z25 : bv_unsigned (zxb (nth 25 FB (zb 0))) = fb FB 25) by (unfold zxb, fb; apply unsigned_lit; pose proof (byte_range (nth 25 FB (zb 0))); lia).
  assert (Z26 : bv_unsigned (zxb (nth 26 FB (zb 0))) = fb FB 26) by (unfold zxb, fb; apply unsigned_lit; pose proof (byte_range (nth 26 FB (zb 0))); lia).
  step. step. step. destruct (Z.eqb_spec (fb FB 16) 207) as [E16|N16].
  2: { if_true. cc_to_ports PP O12 (cc_os0 _ _ FB (cc_slots0 FB ltac:(tauto)) OS). }
  if_false. step. step. step. destruct (Z.eqb_spec (fb FB 17) 234) as [E17|N17].
  2: { if_true. cc_to_ports PP O12 (cc_os0 _ _ FB (cc_slots0 FB ltac:(tauto)) OS). }
  if_false. step. step. step. destruct (Z.eqb_spec (fb FB 22) 1) as [E22|N22].
  2: { if_true. cc_to_ports PP O12 (cc_os0 _ _ FB (cc_slots0 FB ltac:(tauto)) OS). }
  if_false. step. step. step. destruct (Z.eqb_spec (fb FB 23) 3) as [E23|N23].
  2: { if_true. cc_to_ports PP O12 (cc_os0 _ _ FB (cc_slots0 FB ltac:(tauto)) OS). }
  if_false. step. step. step. destruct (Z.eqb_spec (fb FB 24) 13) as [E24|N24].
  2: { if_true. cc_to_ports PP O12 (cc_os0 _ _ FB (cc_slots0 FB ltac:(tauto)) OS). }
  if_false. step. step. step. destruct (Z.eqb_spec (fb FB 25) 1) as [E25|N25].
  2: { if_true. cc_to_ports PP O12 (cc_os0 _ _ FB (cc_slots0 FB ltac:(tauto)) OS). }
  if_false. step. step. step. destruct (Z.eqb_spec (fb FB 26) 4) as [E26|N26].
  2: { if_true. cc_to_ports PP O12 (cc_os0 _ _ FB (cc_slots0 FB ltac:(tauto)) OS). }
  if_false. step. step.
  pose proof (cc_slots1 FB E16 E17 E22 E23 E24 E25 E26) as SL.
  pose proof (cc_os1 _ _ FB _ _ _ OS eq_refl eq_refl
    ltac:(rewrite SL; unfold fb, zxb, zb; rewrite unsigned_lit by (pose proof (byte_range (nth 33 FB (Z_to_bv 8 0))); lia);
          reflexivity)) as OS'.
  cc_to_ports PP O12 OS'.
Qed.

Lemma cc_rw_split2 : forall m A cs1 cs2 B, rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof. intros m A cs1 cs2 B H ->. apply cc_rw_split. exact H. Qed.

Lemma cc_zero_split : forall m o, rw_cells rsegs m (o + 6) [CB 18 (repeat (Z_to_bv 8 0) 18)] ->
  rw_cells rsegs m (o + 6) [CB 2 [zb 0; zb 0]] /\ rw_cells rsegs m (o + 8) [CB 4 [zb 0; zb 0; zb 0; zb 0]] /\
  rw_cells rsegs m (o + 12) [CB 3 [zb 0; zb 0; zb 0]] /\
  rw_cells rsegs m (o + 15) [CB 5 [zb 0; zb 0; zb 0; zb 0; zb 0]] /\
  rw_cells rsegs m (o + 20) [CB 4 [zb 0; zb 0; zb 0; zb 0]].
Proof.
  intros m o H.
  assert (H' : rw_cells rsegs m (o + 6) ([CB 2 [zb 0; zb 0]] ++ [CB 4 [zb 0; zb 0; zb 0; zb 0]] ++
    [CB 3 [zb 0; zb 0; zb 0]] ++ [CB 5 [zb 0; zb 0; zb 0; zb 0; zb 0]] ++ [CB 4 [zb 0; zb 0; zb 0; zb 0]])).
  { eapply cc_rw_conv; [exact H | cbn; repeat split | reflexivity | reflexivity]. }
  destruct (cc_rw_split2 _ _ _ _ (o + 8) H' ltac:(cbn; lia)) as [A1 H2].
  destruct (cc_rw_split2 _ _ _ _ (o + 12) H2 ltac:(cbn; lia)) as [A2 H3].
  destruct (cc_rw_split2 _ _ _ _ (o + 15) H3 ltac:(cbn; lia)) as [A3 H4].
  destruct (cc_rw_split2 _ _ _ _ (o + 20) H4 ltac:(cbn; lia)) as [A4 A5].
  split; [exact A1 | split; [exact A2 | split; [exact A3 | split; [exact A4 | exact A5]]]].
Qed.

Lemma cc_o24_split : forall m o Y, rw_cells rsegs m o [CB 24 Y] ->
  exists Y6 Y18, rw_cells rsegs m o [CB 6 Y6] /\ rw_cells rsegs m (o + 6) [CB 18 Y18].
Proof.
  intros m o Y H. apply (rw_cells_split_CB rsegs m o [] 24 Y [] [6; 18]%nat) in H; [|reflexivity].
  cbn [app mk_CB_cells] in H.
  destruct (cc_rw_split2 _ _ [CB 6 _] [CB 18 _] (o + 6) H ltac:(cbn; lia)) as [A B].
  eexists; eexists; split; eassumption.
Qed.

Lemma cc_stk_after : forall m m' lo hi a n bs, stk rsegs m lo hi -> munch [(a, a + n)] m m' -> wmono rsegs m m' ->
  bytes_at rsegs m' a bs -> Z.of_nat (length bs) = n -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi a n bs (H1 & H2 & H) MU WM B Hn. split; [lia|]. split; [lia|].
  intros x Hx. destruct (H x Hx) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  destruct B as (Ba & Bl & Bn).
  destruct (Z.leb_spec a x) as [L1|L1]; [destruct (Z.ltb_spec x (a + n)) as [L2|L2] |].
  - pose proof (Bn (Z.to_nat (x - a)) ltac:(lia)) as E. replace (a + Z.of_nat (Z.to_nat (x - a))) with x in E by lia.
    rewrite E. destruct (nth_error bs (Z.to_nat (x - a))) eqn:N; [eexists; reflexivity|].
    apply nth_error_None in N. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. cbn [outside]. rewrite wa_unsigned by lia. split; [lia | exact I].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. cbn [outside]. rewrite wa_unsigned by lia. split; [lia | exact I].
Qed.

Lemma cc_lbw2 : forall b0 b1 : byte, bv_unsigned (le_bytes_to_word [b0; b1]) = bv_unsigned b0 + 256 * bv_unsigned b1.
Proof.
  intros. unfold le_bytes_to_word. rewrite bytes_le_to_Z_le_val. cbn [map le_val].
  pose proof (byte_range b0). pose proof (byte_range b1). rewrite unsigned_lit by lia. lia.
Qed.

Lemma cc_lh_unsigned : forall b0 b1 : byte,
  bv_unsigned (sext 64 (bv_extract 0 16 (le_bytes_to_word [b0; b1]))) mod 2^16 = bv_unsigned b0 + 256 * bv_unsigned b1.
Proof.
  intros. rewrite sext_small, Z_to_bv_unsigned, signed_of_extract by reflexivity. rewrite cc_lbw2.
  pose proof (byte_range b0). pose proof (byte_range b1).
  unfold bv_swrap. change (bv_half_modulus 16) with (2^15). change (bv_wrap 16 ?x) with (x mod 2^16).
  change (bv_wrap 64 ?x) with (x mod 2^64).
  Z.div_mod_to_equations. lia.
Qed.

Lemma cc_le2_lh : forall w : list byte, length w = 2%nat -> le2 (sext 64 (bv_extract 0 16 (le_bytes_to_word w))) = w.
Proof.
  intros w Hl. destruct w as [|b0 [|b1 [|]]]; try (cbn in Hl; discriminate).
  unfold le2. rewrite <- (Z_to_le_bytes_mod 2 _ 16) by (cbn; lia). rewrite cc_lh_unsigned.
  replace (bv_unsigned b0 + 256 * bv_unsigned b1) with (bytes_le_to_Z [b0; b1])
    by (rewrite bytes_le_to_Z_le_val; cbn [map le_val]; lia).
  exact (Z_to_le_bytes_to_Z [b0; b1]).
Qed.

Lemma cc_src6 : forall F, length F = 50%nat -> length (src F) = 6%nat.
Proof. intros F H. unfold src, fld. rewrite length_firstn, length_skipn, H. reflexivity. Qed.

Lemma cc_src_conv : forall m o Sb w1 w2, rw_cells rsegs m o [C4 w1; C2 w2] -> length Sb = 6%nat ->
  w1 = sext 64 (bv_extract 0 32 (le_bytes_to_word (firstn 4 (skipn 0 Sb)))) ->
  w2 = sext 64 (bv_extract 0 16 (le_bytes_to_word (firstn 2 (skipn 4 Sb)))) -> rw_cells rsegs m o [CB 6 Sb].
Proof.
  intros m o Sb w1 w2 H HS -> ->. eapply cc_rw_conv; [exact H | split; [exact HS | exact I] | | reflexivity].
  cbn [cells_bytes cbytes]. rewrite !app_nil_r.
  rewrite le4_lw by (rewrite length_firstn, length_skipn, HS; reflexivity).
  rewrite cc_le2_lh by (rewrite length_firstn, length_skipn, HS; reflexivity).
  rewrite (firstn_all2 (n := 2) (skipn 4 Sb)) by (rewrite length_skipn, HS; apply Nat.le_refl).
  cbn [skipn]. symmetry. apply firstn_skipn.
Qed.

Lemma cc_bc01 : forall F, 0 <= (if cp_bcast F then 1 else 0) < 2^31.
Proof. intros F. destruct (cp_bcast F); lia. Qed.

Lemma cc_seqz_bc : forall F, v_sltiu (Z_to_bv 64 (if cp_bcast F then 1 else 0)) 1 = Z_to_bv 64 (if cp_bcast F then 0 else 1).
Proof. intros F. destruct (cp_bcast F); reflexivity. Qed.

Lemma cc_zx16 : forall z, 0 <= z < 65536 -> zx16 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma cc_role_hi : forall F k, 10 <= k -> role F k = 0.
Proof.
  intros F k Hk. unfold role.
  repeat match goal with |- context [k =? ?c] => replace (k =? c) with false by (symmetry; apply Z.eqb_neq; lia) end.
  reflexivity.
Qed.

Lemma cc_role5 : forall F t, tag F = t ->
  role F 5 = if (fb F 22 =? 0) && ((t =? 256) || (t =? 770) || (t =? 1280)) then 1 else 2.
Proof. intros F t <-. reflexivity. Qed.

Ltac cc_to_tail PP FQ RE :=
  apply cc_flat in FQ; cbn [cells_size csize Nat.add] in FQ;
  eapply (cc_tail PP); [reflexivity | reflexivity | reflexivity | reflexivity | RE
                       | eassumption | eassumption | eassumption
                       | lia | lia | lia | lia | lia | lia | lia | lia | eassumption | lia | lia | lia | lia
                       | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
                       | eassumption | eassumption
                       | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
                       | eassumption].

Ltac cc_memset MEMS Y18 O18 :=
  eapply evt_cut;
  [ eapply MEMS with (junk := Y18);
    [ rewrite (unsigned_lit (_ + 6)) by lia; change (Z.to_nat (bv_unsigned (Z_to_bv 64 18))) with 18%nat; exact O18
    | eassumption ]
  | ];
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO; unfold memset_post in PO;
  let m2 := fresh "m" in let Eq := fresh "Eq" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in
  let MIc := fresh "MIc" in let RVc := fresh "RVc" in
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MIc & RVc);
  subst ms';
  rewrite (unsigned_lit (_ + 6)) in MUc, RVc by lia;
  change (bv_unsigned (Z_to_bv 64 18)) with 18 in MUc, RVc;
  change (Z.to_nat 18) with 18%nat in RVc;
  change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RVc;
  lazymatch goal with
  | ST : stk rsegs ?m ?lo ?hi |- _ =>
      let ST2 := fresh "ST" in
      pose proof (cc_stk_after _ _ _ _ _ _ _ ST MUc WMc (cc_rw_bytes _ _ _ RVc) eq_refl) as ST2;
      transport_after_call rsegs m m2 MUc WMc; clear MUc WMc;
      try clear ST; rename ST2 into ST;
      lazymatch goal with MI : mem_inv rsegs m |- _ => clear MI; rename MIc into MI end
  end.

Lemma cc_J : memset_contract -> reac_ports_parse_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo lk f len o : Z) (FB U OB : list byte) (L : option (list byte))
    (xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 : word)
    (m : word -> option byte) (w Y D6 X6 X1 X6' : list byte) (k tg : Z) (lkA : Z) (nL : nat) (LKb : list byte),
  xsp = Z_to_bv 64 (bv_unsigned sp + -112) -> xs0 = Z_to_bv 64 o -> xs1 = Z_to_bv 64 len -> xs2 = Z_to_bv 64 f ->
  xs3 = Z_to_bv 64 (bv_unsigned sp + -96) ->
  dkind FB len = k -> 1 <= k <= 13 -> (k = 5 -> tag FB = tg) -> 0 <= tg < 65536 ->
  cm_ret FB len U L = 0 -> cm_out FB len U L OB = sight FB len -> cc_lock FB U len lk L lkA nL LKb ->
  bv_unsigned sp mod 16 = 0 ->
  0 <= lo -> lo + 192 <= bv_unsigned sp -> 50 <= len < 2^64 -> 0 < o -> o + 24 <= 2^64 ->
  o + 24 <= bv_unsigned sp - 192 \/ bv_unsigned sp <= o ->
  0 < f -> length FB = 50%nat -> f + 50 <= bv_unsigned sp - 192 \/ bv_unsigned sp <= f ->
  o + 24 <= f \/ f + 50 <= o ->
  lkA + Z.of_nat nL <= o \/ o + 24 <= lkA ->
  lkA + Z.of_nat nL <= bv_unsigned sp - 192 \/ bv_unsigned sp <= lkA ->
  stk rsegs m lo (bv_unsigned sp + -112) ->
  rw_cells rsegs m (bv_unsigned sp + -112) [CB 12 w] ->
  rw_cells rsegs m (bv_unsigned sp + -100)
    [C4 (Z_to_bv 64 k); CB 6 (src FB); CB 6 D6; C4 (Z_to_bv 64 (if cp_bcast FB then 1 else 0)); CB 6 X6;
     CB 1 [nth 22 FB (zb 0)];
     CB 1 X1; C2 (Z_to_bv 64 tg); CB 6 X6'] ->
  rw_cells rsegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch (ccW sp o lk L) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m f FB -> rw_cells rsegs m o [CB 24 Y] -> rw_cells rsegs m lkA [CB nL LKb] ->
  evt rsegs (classify_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk len o FB U OB L)
    (MS (mkR xra xsp gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11
             xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x1522c) fc None m (seg_rom rsegs)).
Proof.
  intros MEMS PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk f len o FB U OB L
    xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6
    m w Y D6 X6 X1 X6' k tg lkA nL LKb
    ESP ES0 ES1 ES2 ES3 Hk Hk13 Htg Htgr HR HO HLK Hsp16 Hlo HloS Hlen Ho Hoa Hof Hf HFB Hff Hfo HLo HLf
    ST FW FQ FS MU WM MI FBm O24 RL.
  subst xsp xs0 xs1 xs2 xs3.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bytes_at_bound _ _ _ _ FBm) as Hfb. rewrite HFB in Hfb. change (Z.of_nat 50) with 50 in Hfb.
  destruct (cc_o24_split _ _ _ O24) as (Y6 & Y18 & O6 & O18). clear O24.
  step. rewrite (cc_sx32 k) by lia.
  step. step. step. step.
  cc_memset MEMS Y18 O18.
  rewrite (ret_pc_even 86592) by (first [lia | reflexivity]).
  destruct (cc_zero_split _ _ RVc) as (O2 & O4r & OD & OS & O4). clear RVc.
  step. step. step. step. step. step.
  apply (cc_src_conv _ _ (src FB)) in O6; [ | exact (cc_src6 FB HFB) | reflexivity | reflexivity].
  assert (UK : bv_unsigned (Z_to_bv 64 (k + -1)) = k - 1) by (apply unsigned_lit; lia).
  step.
  destruct (Z.ltb_spec 9 k) as [Kh|Kl].
  { if_true. step. step.
    cc_to_tail PP FQ ltac:(rewrite Hk, cc_role_hi by lia; reflexivity). }
  if_false.
  assert (K9 : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9) by lia.
  destruct K9 as [E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]; rewrite E in *; clear E.
  - do 8 step. step. rewrite (cc_sx32 _ (cc_bc01 FB)). step. rewrite cc_seqz_bc.
    cc_to_tail PP FQ ltac:(rewrite Hk; reflexivity).
  - do 8 step. cc_to_tail PP FQ ltac:(rewrite Hk; reflexivity).
  - do 8 step. cc_to_tail PP FQ ltac:(rewrite Hk; reflexivity).
  - do 8 step. cc_to_tail PP FQ ltac:(rewrite Hk; reflexivity).
  - specialize (Htg eq_refl).
    assert (Z22 : bv_unsigned (zxb (nth 22 FB (zb 0))) = fb FB 22)
      by (unfold zxb, fb; apply unsigned_lit; pose proof (byte_range (nth 22 FB (zb 0))); lia).
    assert (UT : bv_unsigned (Z_to_bv 64 tg) = tg) by (apply unsigned_lit; lia).
    do 8 step. step. step.
    destruct (Z.eqb_spec (fb FB 22) 0) as [E22|N22].
    + if_true. step. rewrite (cc_zx16 tg Htgr). step. step. step.
      destruct (Z.eqb_spec tg 256) as [T1|T1].
      { if_true. cc_to_tail PP FQ ltac:(rewrite Hk, (cc_role5 FB tg Htg), E22, T1; reflexivity). }
      if_false. step. step.
      destruct (Z.eqb_spec tg 770) as [T2|T2].
      { if_true. cc_to_tail PP FQ ltac:(rewrite Hk, (cc_role5 FB tg Htg), E22, T2; reflexivity). }
      if_false. step. step.
      destruct (Z.eqb_spec tg 1280) as [T3|T3].
      { if_true. cc_to_tail PP FQ ltac:(rewrite Hk, (cc_role5 FB tg Htg), E22, T3; reflexivity). }
      if_false. step. step. step.
      cc_to_tail PP FQ ltac:(rewrite Hk, (cc_role5 FB tg Htg), E22, (proj2 (Z.eqb_neq _ _) T1),
                               (proj2 (Z.eqb_neq _ _) T2), (proj2 (Z.eqb_neq _ _) T3); reflexivity).
    + if_false. step. step.
      cc_to_tail PP FQ ltac:(rewrite Hk, (cc_role5 FB tg Htg), (proj2 (Z.eqb_neq _ _) N22); reflexivity).
  - do 8 step. cc_to_tail PP FQ ltac:(rewrite Hk; reflexivity).
  - do 8 step. step. step. cc_to_tail PP FQ ltac:(rewrite Hk; reflexivity).
  - do 8 step. step. step. cc_to_tail PP FQ ltac:(rewrite Hk; reflexivity).
  - do 8 step. step. step. cc_to_tail PP FQ ltac:(rewrite Hk; reflexivity).
Qed.


Lemma cc_A : memset_contract -> reac_ports_parse_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo lk f len o : Z) (FB U OB : list byte) (L : option (list byte))
    (xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 : word)
    (m : word -> option byte) (w Y D6 X6 X1 X6' : list byte) (k tg : Z) (lkA : Z) (nL : nat) (LKb : list byte),
  xsp = Z_to_bv 64 (bv_unsigned sp + -112) -> xs0 = Z_to_bv 64 o -> xs1 = Z_to_bv 64 len -> xs2 = Z_to_bv 64 f ->
  xs3 = Z_to_bv 64 (bv_unsigned sp + -96) ->
  dkind FB len = k -> k = 1 ->
  cm_ret FB len U L = 0 -> cm_out FB len U L OB = sight FB len -> cc_lock FB U len lk L lkA nL LKb ->
  bv_unsigned sp mod 16 = 0 ->
  0 <= lo -> lo + 192 <= bv_unsigned sp -> 50 <= len < 2^64 -> 0 < o -> o + 24 <= 2^64 ->
  o + 24 <= bv_unsigned sp - 192 \/ bv_unsigned sp <= o ->
  0 < f -> length FB = 50%nat -> f + 50 <= bv_unsigned sp - 192 \/ bv_unsigned sp <= f ->
  o + 24 <= f \/ f + 50 <= o ->
  lkA + Z.of_nat nL <= o \/ o + 24 <= lkA ->
  lkA + Z.of_nat nL <= bv_unsigned sp - 192 \/ bv_unsigned sp <= lkA ->
  stk rsegs m lo (bv_unsigned sp + -112) ->
  rw_cells rsegs m (bv_unsigned sp + -112) [CB 12 w] ->
  rw_cells rsegs m (bv_unsigned sp + -100)
    [C4 (Z_to_bv 64 k); CB 6 (src FB); CB 6 D6; C4 (Z_to_bv 64 (if cp_bcast FB then 1 else 0)); CB 6 X6;
     CB 1 [nth 22 FB (zb 0)];
     CB 1 X1; C2 (Z_to_bv 64 tg); CB 6 X6'] ->
  rw_cells rsegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch (ccW sp o lk L) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m f FB -> rw_cells rsegs m o [CB 24 Y] -> rw_cells rsegs m lkA [CB nL LKb] ->
  evt rsegs (classify_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk len o FB U OB L)
    (MS (mkR xra xsp gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11
             xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x15284) fc None m (seg_rom rsegs)).
Proof.
  intros MEMS PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk f len o FB U OB L
    xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6
    m w Y D6 X6 X1 X6' k tg lkA nL LKb
    ESP ES0 ES1 ES2 ES3 Hk K1 HR HO HLK Hsp16 Hlo HloS Hlen Ho Hoa Hof Hf HFB Hff Hfo HLo HLf
    ST FW FQ FS MU WM MI FBm O24 RL.
  subst xsp xs0 xs1 xs2 xs3. rewrite K1 in *. clear K1.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bytes_at_bound _ _ _ _ FBm) as Hfb. rewrite HFB in Hfb. change (Z.of_nat 50) with 50 in Hfb.
  destruct (cc_o24_split _ _ _ O24) as (Y6 & Y18 & O6 & O18). clear O24.
  step. step. step. step.
  cc_memset MEMS Y18 O18.
  rewrite (ret_pc_even 86676) by (first [lia | reflexivity]).
  destruct (cc_zero_split _ _ RVc) as (O2 & O4r & OD & OS & O4). clear RVc.
  step. step. step. step.
  apply (cc_src_conv _ _ (src FB)) in O6; [ | exact (cc_src6 FB HFB) | reflexivity | reflexivity].
  step. rewrite (cc_sx32 _ (cc_bc01 FB)). step. rewrite cc_seqz_bc.
  cc_to_tail PP FQ ltac:(rewrite Hk; reflexivity).
Qed.

Lemma cc_m1_k0 : forall F len U L O, dkind F len = 0 ->
  cm_ret F len U L = -1 /\ cm_out F len U L O = O /\ cm_lock F len U L = L.
Proof.
  intros F len U L O H. unfold cm_ret, cm_out, cm_lock, classify_model. cbv zeta. rewrite H.
  split; [|split]; reflexivity.
Qed.

Lemma cc_m1_eq : forall F len U L O, dkind F len <> 0 -> bytes_eqb (src F) U = true ->
  cm_ret F len U L = -1 /\ cm_out F len U L O = O /\ cm_lock F len U L = L.
Proof.
  intros F len U L O H E. unfold cm_ret, cm_out, cm_lock, classify_model. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) H), E. split; [|split]; reflexivity.
Qed.

Lemma cc_m1_sum : forall F len U L O, dkind F len <> 0 -> bytes_eqb (src F) U = false -> dkind F len <> 1 ->
  fsum F <> 0 -> cm_ret F len U L = -1 /\ cm_out F len U L O = O /\ cm_lock F len U L = L.
Proof.
  intros F len U L O H0 E H1 Sb. unfold cm_ret, cm_out, cm_lock, classify_model. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) H0), E, (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) Sb).
  split; [|split]; reflexivity.
Qed.

Lemma cc_m1_lock : forall F len U Lb O, dkind F len = 1 -> bytes_eqb (src F) U = false -> lv Lb <> 0 ->
  bytes_eqb (lm Lb) (src F) = false ->
  cm_ret F len U (Some Lb) = -1 /\ cm_out F len U (Some Lb) O = O /\ cm_lock F len U (Some Lb) = Some Lb.
Proof.
  intros F len U Lb O H E V B. unfold cm_ret, cm_out, cm_lock, classify_model. cbv beta iota zeta.
  rewrite H, E, (proj2 (Z.eqb_neq _ _) V), B. split; [|split]; reflexivity.
Qed.

Lemma cc_okJ : forall F len U L O lk lkA nL LKb, dkind F len <> 0 -> bytes_eqb (src F) U = false ->
  (dkind F len = 1 \/ fsum F = 0) ->
  (forall Lb, L = Some Lb -> dkind F len = 1 -> lv Lb <> 0 -> bytes_eqb (lm Lb) (src F) = true) ->
  match L with
  | None => lkA = 0 /\ nL = 0%nat /\ LKb = []
  | Some Lb => lkA = lk /\ nL = 12%nat /\ LKb = (if negb (dkind F len =? 1) && (lv Lb =? 0) then latch F Lb else Lb)
  end ->
  cm_ret F len U L = 0 /\ cm_out F len U L O = sight F len /\ cc_lock F U len lk L lkA nL LKb.
Proof.
  intros F len U L O lk lkA nL LKb H0 E HS HL HM. unfold cc_lock, cm_ret, cm_out, cm_lock, classify_model. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) H0), E.
  replace (negb (dkind F len =? 1) && negb (fsum F =? 0)) with false
    by (destruct HS as [HS|HS]; rewrite HS; [reflexivity | cbn [Z.eqb negb]; rewrite andb_false_r; reflexivity]).
  destruct L as [Lb|]; [| split; [reflexivity | split; [reflexivity | exact HM]]].
  cbv beta iota in HM |- *.
  destruct (Z.eqb_spec (dkind F len) 1) as [K1|K1].
  - destruct (Z.eqb_spec (lv Lb) 0) as [V|V].
    + cbn [negb andb]. split; [reflexivity | split; [reflexivity | exact HM]].
    + rewrite (HL Lb eq_refl K1 V). cbn [negb andb]. split; [reflexivity | split; [reflexivity | exact HM]].
  - cbn [negb andb]. split; [reflexivity | split; [reflexivity | exact HM]].
Qed.

Definition cc_L (L : option (list byte)) (lk lkA : Z) (nL : nat) (LKb : list byte) : Prop :=
  match L with
  | None => lk = 0 /\ lkA = 0 /\ nL = 0%nat /\ LKb = []
  | Some Lb => 0 < lk /\ lk mod 4 = 0 /\ lkA = lk /\ nL = 12%nat /\ LKb = Lb
  end.

Ltac cc_exit_m1 CM FQ LKT :=
  let R := fresh "CR" in let O := fresh "CO" in let K := fresh "CK" in destruct CM as (R & O & K);
  apply cc_flat in FQ; cbn [cells_size csize Nat.add] in FQ;
  eapply cc_fin; [reflexivity | rewrite R; reflexivity | lia | lia | eassumption | eassumption | eassumption
                 | eassumption | eassumption | eassumption | eassumption | rewrite O; eassumption | rewrite K; LKT ].

Ltac cc_to_J MEMS PP OK :=
  let A := fresh "JA" in let B := fresh "JB" in let C := fresh "JC" in
  destruct OK as (A & B & C);
  eapply (cc_J MEMS PP); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
                         | eassumption | lia | eassumption | lia | exact A | exact B | exact C
                         | lia | lia | lia | lia | lia | lia | lia | lia | eassumption | lia | lia | lia | lia
                         | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
                         | eassumption | eassumption | eassumption | eassumption].

Ltac cc_to_A MEMS PP OK :=
  let A := fresh "JA" in let B := fresh "JB" in let C := fresh "JC" in
  destruct OK as (A & B & C);
  eapply (cc_A MEMS PP); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
                         | eassumption | reflexivity | exact A | exact B | exact C
                         | lia | lia | lia | lia | lia | lia | lia | lia | eassumption | lia | lia | lia | lia
                         | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
                         | eassumption | eassumption | eassumption | eassumption].

Lemma cc_memcmp : forall n (l r : list byte) v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  -256 < v < 256 /\ (v = 0 <-> map bv_unsigned l = map bv_unsigned r).
Proof.
  induction n as [|n IH]; intros [|a l] [|b r] v Hl Hr H; cbn [length memcmp_model map] in *; try discriminate.
  - injection H as <-. split; [lia| tauto].
  - injection Hl as Hl. injection Hr as Hr.
    pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
    change (bv_modulus 8) with 256 in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
    + destruct (IH l r v Hl Hr H) as [Hv Hi]. split; [exact Hv|]. rewrite Hi, E.
      split; [intros ->; reflexivity | intros Hc; injection Hc as Hc; exact Hc].
    + injection H as <-. split; [lia|]. split; [lia | intros Hc; injection Hc as Hc _; contradiction].
Qed.

Lemma cc_beqb : forall a b, bytes_eqb a b = true <-> map bv_unsigned a = map bv_unsigned b.
Proof.
  intros a b. unfold bytes_eqb. destruct (list_eq_dec Z.eq_dec (map bv_unsigned a) (map bv_unsigned b)) as [E|E];
    split; intros H; try reflexivity; try exact E; try discriminate; contradiction.
Qed.

Lemma cc_q_src : forall m A v Sb rest, rw_cells rsegs m A (C4 v :: CB 6 Sb :: rest) -> bytes_at rsegs m (A + 4) Sb.
Proof.
  intros m A v Sb rest H. apply cc_rw_bytes in H. cbn [cells_bytes cbytes] in H.
  apply bytes_at_app in H as [_ H]. rewrite length_le4 in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma cc_lw0 : forall w : list byte, length w = 4%nat -> bytes_le_to_Z w = 0 ->
  bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word w))) = 0.
Proof.
  intros w Hl H. destruct w as [|b0 [|b1 [|b2 [|b3 [|]]]]]; try (cbn in Hl; discriminate).
  rewrite lw_unsigned4. rewrite bytes_le_to_Z_le_val in H. cbn [map le_val] in H.
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  Z.div_mod_to_equations. lia.
Qed.

Lemma cc_lw1 : forall w : list byte, length w = 4%nat -> bytes_le_to_Z w <> 0 ->
  bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word w))) <> 0.
Proof.
  intros w Hl H. destruct w as [|b0 [|b1 [|b2 [|b3 [|]]]]]; try (cbn in Hl; discriminate).
  rewrite lw_unsigned4. rewrite bytes_le_to_Z_le_val in H. cbn [map le_val] in H.
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  Z.div_mod_to_equations. lia.
Qed.

Lemma cc_src_bytes : forall Sb, length Sb = 6%nat ->
  le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word (firstn 4 (skipn 0 Sb))))) ++
  le2 (sext 64 (bv_extract 0 16 (le_bytes_to_word (firstn 2 (skipn 4 Sb))))) = Sb.
Proof.
  intros Sb HS. rewrite le4_lw by (rewrite length_firstn, length_skipn, HS; reflexivity).
  rewrite cc_le2_lh by (rewrite length_firstn, length_skipn, HS; reflexivity).
  rewrite (firstn_all2 (n := 2) (skipn 4 Sb)) by (rewrite length_skipn, HS; apply Nat.le_refl).
  cbn [skipn]. apply firstn_skipn.
Qed.

Lemma cc_latch_conv : forall m A Sb Lb, length Sb = 6%nat -> length Lb = 12%nat ->
  rw_cells rsegs m A [C4 (sext 64 (bv_extract 0 32 (le_bytes_to_word (firstn 4 (skipn 0 Sb)))));
                      C2 (sext 64 (bv_extract 0 16 (le_bytes_to_word (firstn 2 (skipn 4 Sb)))));
                      CB 2 (firstn 2 (skipn 2 (skipn 4 Lb))); C4 (Z_to_bv 64 1)] ->
  rw_cells rsegs m A [CB 12 (Sb ++ fld Lb 6 2 ++ le4 (Z_to_bv 64 1))].
Proof.
  intros m A Sb Lb HS HL H. eapply cc_rw_conv; [exact H | split; [|exact I] | | reflexivity].
  - cbn [cell_wf]. rewrite !length_app, HS, length_le4. unfold fld. rewrite length_firstn, length_skipn, HL.
    reflexivity.
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r. rewrite (app_assoc (le4 _) (le2 _)), (cc_src_bytes Sb HS).
    f_equal. f_equal. unfold fld. rewrite skipn_skipn. reflexivity.
Qed.

Lemma cc_le4_small : forall k, 0 <= k < 256 -> le4 (Z_to_bv 64 k) = [Z_to_bv 8 k; cp_z; cp_z; cp_z].
Proof.
  intros k Hk. unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  replace (Z.shiftr k 8) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  reflexivity.
Qed.

Lemma cc_src_list : forall F, length F = 50%nat ->
  src F = [cp_b F 6; cp_b F 7; cp_b F 8; cp_b F 9; cp_b F 10; cp_b F 11].
Proof. intros F H. do 12 (destruct F as [|? F]; [cbn in H; discriminate|]). reflexivity. Qed.

Lemma cc_le2_tag : forall F, le2 (Z_to_bv 64 (tag F)) = [cp_b F 35; cp_b F 34].
Proof.
  intros F. unfold tag, fb, cp_b, cp_z, zb.
  set (a := nth 34 F (Z_to_bv 8 0)). set (b := nth 35 F (Z_to_bv 8 0)).
  pose proof (byte_range a) as Ra. pose proof (byte_range b) as Rb.
  unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  replace (256 * bv_unsigned a + bv_unsigned b) with (bv_unsigned b + bv_unsigned a * 2^8) by lia.
  apply f_equal2; [| apply f_equal2; [| reflexivity]].
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8).
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8).
    rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia.
    rewrite Z.add_0_l. apply Z.mod_small. lia.
Qed.

Lemma cc_qcells : forall m q len FB, cp_hdr len FB = true -> length FB = 50%nat ->
  rw_cells rsegs m q [CB 36 (snd (ctrlparse len FB))] ->
  exists D6 X6 X1 tg X6', 0 <= tg < 65536 /\ (dkind FB len = 5 -> tag FB = tg) /\
    rw_cells rsegs m q [C4 (Z_to_bv 64 (dkind FB len)); CB 6 (src FB); CB 6 D6;
      C4 (Z_to_bv 64 (if cp_bcast FB then 1 else 0)); CB 6 X6; CB 1 [nth 22 FB (zb 0)]; CB 1 X1;
      C2 (Z_to_bv 64 tg); CB 6 X6'].
Proof.
  intros m q len FB HE HL H.
  assert (DK : dkind FB len = cp_kind FB) by (unfold dkind, ctrlparse; rewrite HE; reflexivity).
  unfold ctrlparse in H. rewrite HE in H. cbn [snd] in H.
  pose proof (cp_kind_range FB) as KR.
  exists [cp_b FB 0; cp_b FB 1; cp_b FB 2; cp_b FB 3; cp_b FB 4; cp_b FB 5],
         [cp_b FB 14; cp_b FB 15; cp_b FB 18; cp_b FB 19; cp_b FB 21; cp_b FB 20], [cp_z],
         (if cp_rec FB then tag FB else 0),
         ((if cp_kind FB =? 6 then [cp_b FB 36; cp_b FB 37; cp_b FB 38] else [cp_z; cp_z; cp_z]) ++ [cp_z; cp_z; cp_z]).
  split; [|split].
  - destruct (cp_rec FB); [|lia]. unfold tag, fb.
    pose proof (byte_range (nth 34 FB (zb 0))). pose proof (byte_range (nth 35 FB (zb 0))). lia.
  - intros K5. destruct (ctrlparse_rec len FB (or_introl K5)) as (_ & R & _). rewrite R. reflexivity.
  - eapply cc_rw_conv; [exact H | | | reflexivity].
    + rewrite (cc_src_list FB HL). cbn [cells_wf cell_wf]. destruct (cp_kind FB =? 6); repeat split.
    + cbn [cells_bytes cbytes]. rewrite DK, (cc_src_list FB HL), (cc_le4_small (cp_kind FB)) by lia.
      replace (le2 (Z_to_bv 64 (if cp_rec FB then tag FB else 0)))
        with (if cp_rec FB then [cp_b FB 35; cp_b FB 34] else [cp_z; cp_z])
        by (destruct (cp_rec FB); [symmetry; apply cc_le2_tag | reflexivity]).
      unfold cp_struct. destruct (cp_rec FB), (cp_bcast FB), (cp_kind FB =? 6); reflexivity.
Qed.

Lemma cc_parse : reac_ctrl_parse_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sb f len q : Z) (FB junk : list byte)
    (Q : machine_state -> Prop),
  a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 q -> sp = Z_to_bv 64 Sb ->
  0 <= f < 2^64 -> 0 <= len < 2^64 -> 0 < q -> q + 36 <= 2^64 -> Sb < 2^64 -> Sb mod 16 = 0 -> 80 <= Sb ->
  stk rsegs m (Sb - 80) Sb -> mem_inv rsegs m -> length FB = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= Sb - 80 \/ Sb <= f) /\ bytes_at rsegs m f FB /\
                (q + 36 <= f \/ f + 50 <= q)) ->
  q mod 4 = 0 -> rw_cells rsegs m q [CB 36 junk] -> (q + 36 <= Sb - 80 \/ Sb <= q) ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch [(q, q + 36); (Sb - 80, Sb)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (Sb - 80) Sb ->
     (dkind FB len = 0 /\ exists j, rw_cells rsegs m' q [CB 36 j]) \/
     (1 <= dkind FB len <= 13 /\ 50 <= len /\
      exists D6 X6 X1 tg X6', 0 <= tg < 65536 /\ (dkind FB len = 5 -> tag FB = tg) /\
        rw_cells rsegs m' q [C4 (Z_to_bv 64 (dkind FB len)); CB 6 (src FB); CB 6 D6;
          C4 (Z_to_bv 64 (if cp_bcast FB then 1 else 0)); CB 6 X6; CB 1 [nth 22 FB (zb 0)]; CB 1 X1;
          C2 (Z_to_bv 64 tg); CB 6 X6']) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (dkind FB len)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x15bf0) fc None m (seg_rom rsegs)).
Proof.
  intros PARSE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sb f len q FB junk Q E0 E1 E2 ESP Hf Hn Hq Hq36 HS HS16 HS80 ST MI HL HF Hq4 RQ Hqs K.
  eapply evt_cut.
  { eapply (PARSE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                  F fc m f len q Sb FB junk);
      [exact E0 | exact E1 | exact E2 | exact ESP | exact Hf | exact Hn | lia | exact HS | exact HS16 | exact HS80
      | exact ST | exact MI | exact HL | | | ].
    - intros H50. destruct (HF H50) as (A1 & A2 & A3 & _). unfold REAC_CTRL_PARSE_K. lia.
    - intros i Hi. destruct (Z_lt_le_dec len 50) as [Hs|Hb].
      + exfalso. unfold cp_rd in Hi. rewrite (proj2 (Z.leb_gt 50 len) Hs) in Hi. exact Hi.
      + destruct (HF Hb) as (_ & _ & _ & (_ & _ & B) & _). apply B. rewrite HL.
        pose proof (cp_rd_lt39 _ _ _ Hi) as H39. apply (Nat.lt_trans _ 39); [exact H39 | apply Nat.ltb_lt; reflexivity].
    - intros _. split; [exact Hq4|]. split; [lia|]. split; [exact RQ|]. split; [unfold REAC_CTRL_PARSE_K; lia|].
      intros H50. destruct (HF H50) as (_ & _ & _ & _ & D). exact D. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & MI' & ST' & R).
  subst ms'.
  unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MU, ST'.
  rewrite (proj2 (Z.eqb_neq q 0)) in MU by lia. cbn [app] in MU.
  specialize (R ltac:(lia)).
  apply K; [exact MU | exact WM | exact MI' | exact ST' |].
  destruct (cp_hdr len FB) eqn:HE.
  - right. assert (H50 : 50 <= len) by (apply cp_hdr_spec in HE; tauto).
    assert (DK : dkind FB len = cp_kind FB) by (unfold dkind, ctrlparse; rewrite HE; reflexivity).
    split; [rewrite DK; apply cp_kind_range|]. split; [exact H50|].
    exact (cc_qcells _ _ _ _ HE HL R).
  - left. assert (DK : dkind FB len = 0) by (unfold dkind, ctrlparse; rewrite HE; reflexivity).
    split; [exact DK | eexists; exact R].
Qed.

Ltac cc_lkt L HLL RL :=
  destruct L as [?Lb|]; [unfold cc_L in HLL; destruct HLL as (_ & _ & ? & ? & ?); subst; exact RL | exact I].

Lemma cc_k1 : bcmp_contract -> memset_contract -> reac_ports_parse_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo lk f len o : Z) (FB U OB : list byte) (L : option (list byte))
    (xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 : word)
    (m : word -> option byte) (w D6 X6 X1 X6' : list byte) (k tg : Z) (lkA : Z) (nL : nat) (LKb : list byte),
  xsp = Z_to_bv 64 (bv_unsigned sp + -112) -> xs0 = Z_to_bv 64 o -> xs1 = Z_to_bv 64 len -> xs2 = Z_to_bv 64 f ->
  xs3 = Z_to_bv 64 (bv_unsigned sp + -96) -> xs4 = Z_to_bv 64 lk -> xs5 = Z_to_bv 64 (-1) ->
  dkind FB len = k -> k = 1 -> (k = 5 -> tag FB = tg) -> 0 <= tg < 65536 ->
  bytes_eqb (src FB) U = false -> cc_L L lk lkA nL LKb ->
  bv_unsigned sp mod 16 = 0 ->
  0 <= lo -> lo + 192 <= bv_unsigned sp -> 50 <= len < 2^64 -> 0 < o -> o + 24 <= 2^64 ->
  o + 24 <= bv_unsigned sp - 192 \/ bv_unsigned sp <= o ->
  0 < f -> length FB = 50%nat -> f + 50 <= bv_unsigned sp - 192 \/ bv_unsigned sp <= f ->
  o + 24 <= f \/ f + 50 <= o ->
  lkA + Z.of_nat nL <= o \/ o + 24 <= lkA ->
  lkA + Z.of_nat nL <= bv_unsigned sp - 192 \/ bv_unsigned sp <= lkA ->
  lkA + Z.of_nat nL <= f \/ f + 50 <= lkA -> 0 <= lkA -> lkA + Z.of_nat nL <= 2^64 ->
  stk rsegs m lo (bv_unsigned sp + -112) ->
  rw_cells rsegs m (bv_unsigned sp + -112) [CB 12 w] ->
  rw_cells rsegs m (bv_unsigned sp + -100)
    [C4 (Z_to_bv 64 k); CB 6 (src FB); CB 6 D6; C4 (Z_to_bv 64 (if cp_bcast FB then 1 else 0)); CB 6 X6;
     CB 1 [nth 22 FB (zb 0)]; CB 1 X1; C2 (Z_to_bv 64 tg); CB 6 X6'] ->
  rw_cells rsegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch (ccW sp o lk L) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m f FB -> rw_cells rsegs m o [CB 24 OB] -> rw_cells rsegs m lkA [CB nL LKb] ->
  evt rsegs (classify_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk len o FB U OB L)
    (MS (mkR xra xsp gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11
             xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x151d8) fc None m (seg_rom rsegs)).
Proof.
  intros BC MEMS PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk f len o FB U OB L
    xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6
    m w D6 X6 X1 X6' k tg lkA nL LKb
    ESP ES0 ES1 ES2 ES3 ES4 ES5 Hk K1 Htg Htgr HU HLL Hsp16 Hlo HloS Hlen Ho Hoa Hof Hf HFB Hff Hfo HLo HLf HLfb
    HLa HLb ST FW FQ FS MU WM MI FBm O24 RL.
  subst xsp xs0 xs1 xs2 xs3 xs4 xs5. rewrite K1 in *. clear K1.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bytes_at_bound _ _ _ _ FBm) as Hfb. rewrite HFB in Hfb. change (Z.of_nat 50) with 50 in Hfb.
  assert (K0 : dkind FB len <> 0) by lia.
  destruct L as [Lb|].
  - destruct HLL as (Hlk & Hlk4 & E1 & E2 & E3). subst lkA nL LKb.
    assert (UL : bv_unsigned (Z_to_bv 64 lk) = lk) by (apply unsigned_lit; lia).
    pose proof (rw_cells_CB_length rsegs _ _ _ _ RL) as HL12.
    pose proof (cc_rw_bytes _ _ _ RL) as LB. cbn [cells_bytes cbytes] in LB. rewrite app_nil_r in LB.
    pose proof (cc_sub _ _ _ 0 6 LB ltac:(rewrite HL12; apply Nat.leb_le; reflexivity)) as LM.
    rewrite Z.add_0_r in LM. clear LB.
    step. if_false. step. step.
    destruct (Z.eqb_spec (lv Lb) 0) as [V|V].
    + pose proof (cc_lw0 (firstn 4 (skipn 8 Lb)) ltac:(rewrite length_firstn, length_skipn, HL12; reflexivity) V)
        as V0.
      if_true.
      cc_to_J MEMS PP (cc_okJ FB len U (Some Lb) OB lk lk 12%nat Lb K0 HU (or_introl Hk)
                         ltac:(intros Lb' E' _ V'; injection E' as <-; contradiction)
                         ltac:(rewrite Hk; split; [reflexivity | split; reflexivity])).
    + pose proof (cc_lw1 (firstn 4 (skipn 8 Lb)) ltac:(rewrite length_firstn, length_skipn, HL12; reflexivity) V)
        as V1.
      if_false. step. step. step. step.
      pose proof (cc_q_src _ _ _ _ _ FQ) as QS.
      replace (bv_unsigned sp + -100 + 4) with (bv_unsigned sp + -96) in QS by lia.
      assert (LL6 : length (lm Lb) = 6%nat) by (unfold lm, fld; rewrite length_firstn, length_skipn, HL12; reflexivity).
      destruct (memcmp_model_total (lm Lb) (src FB) 6) as [v Hv];
        [rewrite LL6; apply Nat.le_refl | rewrite (cc_src6 FB HFB); apply Nat.le_refl |].
      destruct (cc_memcmp 6 _ _ v LL6 (cc_src6 FB HFB) Hv) as [Rv Iv].
      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply BC; [ rewrite UL; exact LM | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; exact QS
                     | change (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) with 6%nat; exact Hv | assumption ]
        | post_call segs mm ] end.
      repeat match goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end.
      step.
      if_cases HC; zify_cond HC; rewrite ?unsigned_lit_wrap in HC.
      * assert (v = 0) by (clear - HC Rv; Z.div_mod_to_equations; lia). subst v.
        assert (EQ : bytes_eqb (lm Lb) (src FB) = true) by (apply cc_beqb; apply Iv; reflexivity).
        cc_to_J MEMS PP (cc_okJ FB len U (Some Lb) OB lk lk 12%nat Lb K0 HU (or_introl Hk)
                           ltac:(intros Lb' E' _ _; injection E' as <-; exact EQ)
                           ltac:(rewrite Hk; split; [reflexivity | split; reflexivity])).
      * assert (v <> 0) by (clear - HC Rv; Z.div_mod_to_equations; lia).
        assert (NE : bytes_eqb (lm Lb) (src FB) = false).
        { destruct (bytes_eqb (lm Lb) (src FB)) eqn:B; [|reflexivity]. apply cc_beqb, Iv in B. contradiction. }
        step.
        cc_exit_m1 (cc_m1_lock FB len U Lb OB Hk HU V NE) FQ ltac:(exact RL).
  - destruct HLL as (E0 & E1 & E2 & E3). subst lk lkA nL LKb.
    step. if_true.
    cc_to_A MEMS PP (cc_okJ FB len U None OB 0 0 0%nat [] K0 HU (or_introl Hk)
                       ltac:(intros Lb' E'; discriminate) ltac:(split; [reflexivity | split; reflexivity])).
Qed.

Lemma cc_fsum : forall F, fsum F = blocksum (fld F 18 32).
Proof. intros F. reflexivity. Qed.

Lemma cc_kn : reac_ctrl_checksum_verify_contract -> memset_contract -> reac_ports_parse_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo lk f len o : Z) (FB U OB : list byte) (L : option (list byte))
    (xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 : word)
    (m : word -> option byte) (w D6 X6 X1 X6' : list byte) (k tg : Z) (lkA : Z) (nL : nat) (LKb : list byte),
  xsp = Z_to_bv 64 (bv_unsigned sp + -112) -> xs0 = Z_to_bv 64 o -> xs1 = Z_to_bv 64 len -> xs2 = Z_to_bv 64 f ->
  xs3 = Z_to_bv 64 (bv_unsigned sp + -96) -> xs4 = Z_to_bv 64 lk -> xs5 = Z_to_bv 64 (-1) ->
  dkind FB len = k -> k <> 1 -> 1 <= k <= 13 -> (k = 5 -> tag FB = tg) -> 0 <= tg < 65536 ->
  bytes_eqb (src FB) U = false -> cc_L L lk lkA nL LKb ->
  bv_unsigned sp mod 16 = 0 ->
  0 <= lo -> lo + 192 <= bv_unsigned sp -> 50 <= len < 2^64 -> 0 < o -> o + 24 <= 2^64 ->
  o + 24 <= bv_unsigned sp - 192 \/ bv_unsigned sp <= o ->
  0 < f -> length FB = 50%nat -> f + 50 <= bv_unsigned sp - 192 \/ bv_unsigned sp <= f ->
  o + 24 <= f \/ f + 50 <= o ->
  lkA + Z.of_nat nL <= o \/ o + 24 <= lkA ->
  lkA + Z.of_nat nL <= bv_unsigned sp - 192 \/ bv_unsigned sp <= lkA ->
  lkA + Z.of_nat nL <= f \/ f + 50 <= lkA -> 0 <= lkA -> lkA + Z.of_nat nL <= 2^64 ->
  stk rsegs m lo (bv_unsigned sp + -112) ->
  rw_cells rsegs m (bv_unsigned sp + -112) [CB 12 w] ->
  rw_cells rsegs m (bv_unsigned sp + -100)
    [C4 (Z_to_bv 64 k); CB 6 (src FB); CB 6 D6; C4 (Z_to_bv 64 (if cp_bcast FB then 1 else 0)); CB 6 X6;
     CB 1 [nth 22 FB (zb 0)]; CB 1 X1; C2 (Z_to_bv 64 tg); CB 6 X6'] ->
  rw_cells rsegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch (ccW sp o lk L) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m f FB -> rw_cells rsegs m o [CB 24 OB] -> rw_cells rsegs m lkA [CB nL LKb] ->
  evt rsegs (classify_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk len o FB U OB L)
    (MS (mkR xra xsp gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11
             xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x151fc) fc None m (seg_rom rsegs)).
Proof.
  intros CHK MEMS PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo lk f len o FB U OB L
    xra xsp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6
    m w D6 X6 X1 X6' k tg lkA nL LKb
    ESP ES0 ES1 ES2 ES3 ES4 ES5 Hk Kn1 Hk13 Htg Htgr HU HLL Hsp16 Hlo HloS Hlen Ho Hoa Hof Hf HFB Hff Hfo HLo HLf
    HLfb HLa HLb ST FW FQ FS MU WM MI FBm O24 RL.
  subst xsp xs0 xs1 xs2 xs3 xs4 xs5.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bytes_at_bound _ _ _ _ FBm) as Hfb. rewrite HFB in Hfb. change (Z.of_nat 50) with 50 in Hfb.
  assert (K0 : dkind FB len <> 0) by lia. assert (Kn : dkind FB len <> 1) by lia.
  pose proof (cc_sub _ f FB 18 32 FBm ltac:(rewrite HFB; apply Nat.leb_le; reflexivity)) as CB32.
  change (f + Z.of_nat 18) with (f + 18) in CB32.
  step. step.
  eapply evt_cut.
  { eapply CHK with (p := f) (bs := fld FB 18 32);
      [lia | lia | reflexivity | unfold fld; rewrite length_firstn, length_skipn, HFB; reflexivity | exact CB32]. }
  intros ms' (a1' & a2' & a3' & E). subst ms'.
  rewrite (ret_pc_even 86532) by (first [lia | reflexivity]).
  step.
  destruct (Z.eqb_spec (fsum FB) 0) as [S0|S1].
  2: { pose proof S1 as S1'. rewrite cc_fsum in S1'. rewrite (proj2 (Z.eqb_neq _ _) S1'). if_true.
       cc_exit_m1 (cc_m1_sum FB len U L OB K0 HU Kn S1) FQ ltac:(cc_lkt L HLL RL). }
  pose proof S0 as S0'. rewrite cc_fsum in S0'. rewrite S0'. if_false.
  destruct L as [Lb|].
  - destruct HLL as (Hlk & Hlk4 & E1 & E2 & E3). subst lkA nL LKb.
    assert (UL : bv_unsigned (Z_to_bv 64 lk) = lk) by (apply unsigned_lit; lia).
    pose proof (rw_cells_CB_length rsegs _ _ _ _ RL) as HL12.
    step. if_false. step. step.
    destruct (Z.eqb_spec (lv Lb) 0) as [V|V].
    + pose proof (cc_lw0 (firstn 4 (skipn 8 Lb)) ltac:(rewrite length_firstn, length_skipn, HL12; reflexivity) V)
        as V0.
      if_false. step. step. step. step. step. step.
      apply (cc_latch_conv _ _ _ _ (cc_src6 FB HFB) HL12) in RL.
      cc_to_J MEMS PP (cc_okJ FB len U (Some Lb) OB lk lk 12%nat (latch FB Lb) K0 HU (or_intror S0)
                         ltac:(intros Lb' _ K1'; contradiction)
                         ltac:(rewrite (proj2 (Z.eqb_neq _ _) Kn), V; split; [reflexivity | split; reflexivity])).
    + pose proof (cc_lw1 (firstn 4 (skipn 8 Lb)) ltac:(rewrite length_firstn, length_skipn, HL12; reflexivity) V)
        as V1.
      if_true.
      cc_to_J MEMS PP (cc_okJ FB len U (Some Lb) OB lk lk 12%nat Lb K0 HU (or_intror S0)
                         ltac:(intros Lb' _ K1'; contradiction)
                         ltac:(rewrite (proj2 (Z.eqb_neq _ _) Kn), (proj2 (Z.eqb_neq _ _) V);
                               split; [reflexivity | split; reflexivity])).
  - destruct HLL as (E0 & E1 & E2 & E3). subst lk lkA nL LKb.
    step. if_true.
    cc_to_J MEMS PP (cc_okJ FB len U None OB 0 0 0%nat [] K0 HU (or_intror S0)
                       ltac:(intros Lb' E'; discriminate) ltac:(split; [reflexivity | split; reflexivity])).
Qed.

Ltac cc_pro :=
  lazymatch goal with ST : stk rsegs _ _ _ |- _ => carve_frame 112%nat ST end;
  do 18 step;
  lazymatch goal with FR : rw_cells rsegs _ (bv_unsigned ?sp + -112) _ |- _ =>
    let F48 := fresh "F48" in let FS := fresh "FS" in let FW := fresh "FW" in let FQ0 := fresh "FQ0" in
    destruct (cc_rw_split2 _ _ [CB 48 _] _ (bv_unsigned sp + -64) FR ltac:(cbn; lia)) as [F48 FS]; clear FR;
    apply (rw_cells_split_CB rsegs _ _ [] 48 _ [] [12; 36]%nat) in F48; [|reflexivity];
    cbn [app mk_CB_cells] in F48;
    destruct (cc_rw_split2 _ _ [CB 12 _] [CB 36 _] (bv_unsigned sp + -100) F48 ltac:(cbn; lia)) as [FW FQ0];
    clear F48;
    lazymatch goal with ST : stk rsegs _ ?lo (bv_unsigned sp + -112) |- _ =>
      let STl := fresh "STl" in let STh := fresh "STh" in
      destruct (stk_split rsegs _ lo (bv_unsigned sp + -112 - 80) (bv_unsigned sp + -112) ST ltac:(lia)) as [STl STh];
      clear ST
    end
  end.

Ltac cc_after_parse :=
  let t0' := fresh "t0'" in let t1' := fresh "t1'" in let t2' := fresh "t2'" in let a1' := fresh "a1'" in
  let a2' := fresh "a2'" in let a3' := fresh "a3'" in let a4' := fresh "a4'" in let a5' := fresh "a5'" in
  let a6' := fresh "a6'" in let a7' := fresh "a7'" in let t3' := fresh "t3'" in let t4' := fresh "t4'" in
  let t5' := fresh "t5'" in let t6' := fresh "t6'" in let m' := fresh "m" in
  let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIc" in let STc := fresh "STc" in
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MUc WMc MIc STc ?KQ;
  lazymatch type of MUc with munch _ ?m1 _ =>
    transport_after_call rsegs m1 m' MUc WMc; clear MUc WMc;
    lazymatch goal with H : mem_inv rsegs m1 |- _ => clear H end
  end;
  match goal with STl : stk rsegs _ ?lo ?mid |- _ =>
    lazymatch type of STc with stk _ _ ?mid' _ => constr_eq mid mid' end;
    let ST := fresh "ST" in pose proof (stk_merge rsegs _ lo _ _ STl STc ltac:(lia)) as ST; clear STl STc
  end;
  rewrite (ret_pc_even 86444) by (first [lia | reflexivity]).

Theorem classify_core_holds : reac_ctrl_parse_contract -> bcmp_contract -> reac_ctrl_checksum_verify_contract ->
  memset_contract -> reac_ports_parse_contract -> classify_core_contract.
Proof.
  intros PARSE BC CHK MEMS PP. unfold classify_core_contract, classify_core_spec, CLASSIFY_CORE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo lk f len u o FB U OB L E0 E1 E2 E3 E4 PRE.
  unfold classify_core_pre, CLASSIFY_CORE_K, disj in PRE.
  destruct PRE as (Hsp16 & ST & HloS & Hlen & Hf & HFB & HF & HU6 & UB & Hud & Ho & Ho4 & O24 & Hod & Hou & HL & MI).
  subst a0 a1 a2 a3 a4.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (rw_cells_bound _ _ _ _ O24) as HOB. cbn [cells_size csize Nat.add] in HOB.
  change (Z.of_nat 24) with 24 in HOB.
  pose proof (bytes_at_bound _ _ _ _ UB) as HUB. rewrite HU6 in HUB. change (Z.of_nat 6) with 6 in HUB.
  pose proof ST as (Hlo & _ & _).
  assert (LS : exists lkA nL LKb, cc_L L lk lkA nL LKb /\ rw_cells rsegs m lkA [CB nL LKb] /\ 0 <= lkA /\
     lkA + Z.of_nat nL <= 2^64 /\ (lkA + Z.of_nat nL <= bv_unsigned sp - 192 \/ bv_unsigned sp <= lkA) /\
     (lkA + Z.of_nat nL <= o \/ o + 24 <= lkA) /\ (50 <= len -> lkA + Z.of_nat nL <= f \/ f + 50 <= lkA)).
  { destruct L as [Lb|].
    - destruct HL as (Hlk & Hlk4 & RL & D1 & D2 & D3 & D4).
      pose proof (rw_cells_bound _ _ _ _ RL) as HRB. cbn [cells_size csize Nat.add] in HRB.
      change (Z.of_nat 12) with 12 in HRB.
      exists lk, 12%nat, Lb. split; [split; [exact Hlk | split; [exact Hlk4 | split; [reflexivity | split; reflexivity]]]|].
      split; [exact RL|]. change (Z.of_nat 12) with 12.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros H50. specialize (D4 H50). lia.
    - exists 0, 0%nat, []. split; [split; [exact HL | split; [reflexivity | split; reflexivity]]|].
      split; [apply cc_rw_nil|]. change (Z.of_nat 0) with 0.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros _. lia. }
  destruct LS as (lkA & nL & LKb & HLL & RL & HLa & HLb & HLf & HLo & HLfb). clear HL.
  pose proof (munch_refl (ccW sp o lk L) m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct (Z_lt_le_dec len 50) as [Hs|Hb].
  - cc_pro.
    eapply (cc_parse PARSE) with (Sb := bv_unsigned sp + -112) (f := f) (len := len) (q := bv_unsigned sp + -100)
      (FB := FB);
      [reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | lia
      | Z.div_mod_to_equations; lia | lia | eassumption | eassumption | exact HFB | intros; lia
      | Z.div_mod_to_equations; lia | eassumption | lia | ].
    cc_after_parse.
    destruct KQ as [(K0 & j & FQ) | (Kr & H50 & _)]; [| lia].
    step. step. rewrite K0. if_true.
    cc_exit_m1 (cc_m1_k0 FB len U L OB K0) FQ ltac:(cc_lkt L HLL RL).
  - destruct (HF Hb) as (Hf0 & FBm & Hff & Hfo). specialize (HLfb Hb).
    pose proof (bytes_at_bound _ _ _ _ FBm) as Hfb. rewrite HFB in Hfb. change (Z.of_nat 50) with 50 in Hfb.
    cc_pro.
    eapply (cc_parse PARSE) with (Sb := bv_unsigned sp + -112) (f := f) (len := len) (q := bv_unsigned sp + -100)
      (FB := FB);
      [reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | lia
      | Z.div_mod_to_equations; lia | lia | eassumption | eassumption | exact HFB
      | intros _; split; [lia | split; [lia | split; [lia | split; [eassumption | lia]]]]
      | Z.div_mod_to_equations; lia | eassumption | lia | ].
    cc_after_parse.
    destruct KQ as [(K0 & j & FQ) | (Kr & H50 & D6 & X6 & X1 & tg & X6' & Htgr & Htg & FQ)].
    { step. step. rewrite K0. if_true.
      cc_exit_m1 (cc_m1_k0 FB len U L OB K0) FQ ltac:(cc_lkt L HLL RL). }
    set (k := dkind FB len) in *. assert (Hk : dkind FB len = k) by reflexivity. clearbody k.
    assert (UK : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
    step. step. if_false.
    step. step. step. step. step.
    pose proof (cc_q_src _ _ _ _ _ FQ) as QS.
    replace (bv_unsigned sp + -100 + 4) with (bv_unsigned sp + -96) in QS by lia.
    destruct (memcmp_model_total (src FB) U 6) as [v Hv];
      [rewrite (cc_src6 FB HFB); apply Nat.le_refl | rewrite HU6; apply Nat.le_refl |].
    destruct (cc_memcmp 6 _ _ v (cc_src6 FB HFB) HU6 Hv) as [Rv Iv].
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply BC; [ rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; exact QS
                   | rewrite (unsigned_lit u) by lia; exact UB
                   | change (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) with 6%nat; exact Hv | assumption ]
      | post_call segs mm ] end.
    repeat match goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end.
    step.
    if_cases HC; zify_cond HC; rewrite ?unsigned_lit_wrap in HC.
    + assert (v = 0) by (clear - HC Rv; Z.div_mod_to_equations; lia). subst v.
      assert (EQ : bytes_eqb (src FB) U = true) by (apply cc_beqb; apply Iv; reflexivity).
      cc_exit_m1 (cc_m1_eq FB len U L OB ltac:(lia) EQ) FQ ltac:(cc_lkt L HLL RL).
    + assert (v <> 0) by (clear - HC Rv; Z.div_mod_to_equations; lia).
      assert (HU : bytes_eqb (src FB) U = false).
      { destruct (bytes_eqb (src FB) U) eqn:B; [|reflexivity]. apply cc_beqb, Iv in B. contradiction. }
      step. rewrite (cc_sx32 k) by lia. step. step.
      destruct (Z.eqb_spec k 1) as [K1|K1].
      * if_false.
        eapply (cc_k1 BC MEMS PP);
          [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | eassumption | exact K1 | eassumption | lia | exact HU | eassumption
          | lia | lia | lia | lia | lia | lia | lia | lia | eassumption | lia | lia | lia | lia | lia | lia | lia
          | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
          | eassumption | eassumption | eassumption].
      * if_true.
        eapply (cc_kn CHK MEMS PP);
          [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | eassumption | exact K1 | lia | eassumption | lia | exact HU | eassumption
          | lia | lia | lia | lia | lia | lia | lia | lia | eassumption | lia | lia | lia | lia | lia | lia | lia
          | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
          | eassumption | eassumption | eassumption].
Qed.

Lemma cc_cm_ok_inv : forall F len U L, cm_ret F len U L = 0 ->
  dkind F len <> 0 /\ bytes_eqb (src F) U = false /\ (dkind F len = 1 \/ fsum F = 0).
Proof.
  intros F len U L H. unfold cm_ret, classify_model in H. cbv zeta in H. revert H.
  destruct (Z.eqb_spec (dkind F len) 0) as [K|K]; [cbn; intros H; discriminate H|].
  destruct (bytes_eqb (src F) U); [cbn; intros H; discriminate H|].
  destruct (Z.eqb_spec (dkind F len) 1) as [K1|K1]; [intros _; split; [exact K | split; [reflexivity | left; exact K1]]|].
  destruct (Z.eqb_spec (fsum F) 0) as [Sb|Sb]; [intros _; split; [exact K | split; [reflexivity | right; exact Sb]]|].
  cbn. intros H. discriminate H.
Qed.

Lemma cc_zb_small : forall z, 0 <= z < 256 -> bv_unsigned (zb z) = z.
Proof. intros z Hz. unfold zb. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma classify_model_facts : forall FB len U L,
  cm_ret FB len U L = 0 -> length FB = 50%nat ->
  sighting_ok (sight FB len) /\ bytes_eqb (src FB) U = false /\ 50 <= len /\
  fu (sight FB len) 20 4 = geo len /\ (dkind FB len = 1 \/ fsum FB = 0).
Proof.
  intros FB len U L H HL. destruct (cc_cm_ok_inv _ _ _ _ H) as (K0 & E & KS).
  assert (H50 : 50 <= len).
  { unfold dkind, ctrlparse in K0. destruct (cp_hdr len FB) eqn:HE; [apply cp_hdr_spec in HE; tauto | cbn in K0; lia]. }
  assert (R : 0 <= role FB (dkind FB len) <= 2)
    by (unfold role; repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia).
  assert (G : 0 <= geo len < 2^32)
    by (unfold geo; destruct (_ && _); [apply Z.mod_pos_bound; lia | lia]).
  assert (LA : length (sgA FB len) = 12%nat) by (unfold sgA; rewrite !length_app, (cc_src6 _ HL), length_le4; reflexivity).
  assert (LD : length (sgD FB) = 3%nat) by (unfold sgD; destruct (sdecl FB) as [[? ?]|]; reflexivity).
  assert (LS : length (sgS FB) = 5%nat) by reflexivity.
  split; [|split; [exact E | split; [exact H50 | split; [|exact KS]]]].
  - unfold sighting_ok. split; [|split].
    + rewrite sight_parts, !length_app, LA, LD, LS, length_le4. reflexivity.
    + unfold fu, fld, sight. rewrite app_assoc.
      replace 8%nat with (length (src FB ++ [zb 0; zb 0])) by (rewrite length_app, (cc_src6 FB HL); reflexivity).
      rewrite skipn_app_exact. rewrite firstn_app_len by (rewrite length_le4; reflexivity).
      rewrite bytes_le_to_Z_le4, unsigned_lit by lia. rewrite Z.mod_small by lia.
      unfold s32. rewrite (proj2 (Z.ltb_lt _ _)) by lia. lia.
    + assert (N : forall j, (j < 3)%nat -> nth (12 + j) (sight FB len) (zb 0) = nth j (sgD FB) (zb 0)).
      { intros j Hj. rewrite sight_parts. rewrite app_nth2 by lia. rewrite LA.
        replace (12 + j - 12)%nat with j by lia. apply app_nth1. lia. }
      pose proof (N 0%nat ltac:(lia)) as N0. pose proof (N 1%nat ltac:(lia)) as N1. pose proof (N 2%nat ltac:(lia)) as N2.
      cbn [Nat.add] in N0, N1, N2. unfold fb. rewrite N0, N1, N2.
      unfold sgD. destruct (sdecl FB) as [[i o]|] eqn:SD; [|left; reflexivity].
      unfold sdecl in SD. cbv zeta in SD.
      destruct (decl (fld FB 18 20) && (4 * n_in (fld FB 18 20) <=? 40) && (4 * n_out (fld FB 18 20) <=? 40)) eqn:C;
        [|discriminate].
      injection SD as <- <-. apply andb_true_iff in C as [C C3]. apply andb_true_iff in C as [_ C2].
      apply Z.leb_le in C2, C3.
      assert (Ni : 0 <= n_in (fld FB 18 20)) by (unfold n_in; pose proof (rcl_cnt_range is_in (fld FB 18 20) 12); lia).
      assert (No : 0 <= n_out (fld FB 18 20)) by (unfold n_out; pose proof (rcl_cnt_range is_out (fld FB 18 20) 12); lia).
      right. cbn [nth]. rewrite !cc_zb_small by lia. lia.
  - unfold fu, fld. rewrite sight_parts, !app_assoc.
    replace 20%nat with (length ((sgA FB len ++ sgD FB) ++ sgS FB)) by (rewrite !length_app, LA, LD, LS; reflexivity).
    rewrite skipn_app_exact. rewrite firstn_all2 by (rewrite length_le4; lia).
    rewrite bytes_le_to_Z_le4, unsigned_lit by lia. apply Z.mod_small. lia.
Qed.

Lemma cc_len12 : forall F len, dkind F len <> 0 -> (12 < length F)%nat.
Proof.
  intros F len H. unfold dkind, ctrlparse in H. destruct (cp_hdr len F) eqn:HE; [|cbn in H; lia].
  apply cp_hdr_spec in HE as (_ & H12 & _). unfold cp_v, cp_b in H12.
  destruct (Nat.lt_ge_cases 12 (length F)) as [Hl|Hl]; [exact Hl|].
  rewrite nth_overflow in H12 by exact Hl. change (bv_unsigned cp_z) with 0 in H12. lia.
Qed.

Lemma classify_lock_preserved : forall FB len U Lb Lb',
  lock_ok Lb -> cm_lock FB len U (Some Lb) = Some Lb' -> lock_ok Lb'.
Proof.
  intros FB len U Lb Lb' HL H. unfold cm_lock, classify_model in H. cbv beta iota zeta in H. revert H.
  destruct (Z.eqb_spec (dkind FB len) 0) as [K0|K0]; [cbn; intros H; injection H as <-; exact HL|].
  destruct (bytes_eqb (src FB) U); [cbn; intros H; injection H as <-; exact HL|].
  destruct (negb (dkind FB len =? 1) && negb (fsum FB =? 0)); [cbn; intros H; injection H as <-; exact HL|].
  destruct ((dkind FB len =? 1) && negb (lv Lb =? 0) && negb (bytes_eqb (lm Lb) (src FB)));
    [cbn; intros H; injection H as <-; exact HL|].
  cbn [snd]. intros H. injection H as <-.
  destruct (negb (dkind FB len =? 1) && (lv Lb =? 0)); [|exact HL].
  pose proof (cc_len12 FB len K0) as L12. destruct HL as [HL _].
  assert (LS : length (src FB) = 6%nat) by (unfold src, fld; rewrite length_firstn, length_skipn; lia).
  assert (LF : length (fld Lb 6 2) = 2%nat) by (unfold fld; rewrite length_firstn, length_skipn; lia).
  unfold lock_ok, latch. split.
  - rewrite !length_app, LS, LF, length_le4. reflexivity.
  - right. unfold fu, fld at 1. rewrite app_assoc.
    replace 8%nat with (length (src FB ++ fld Lb 6 2)) by (rewrite length_app, LS, LF; reflexivity).
    rewrite skipn_app_exact. rewrite firstn_all2 by (rewrite length_le4; lia). reflexivity.
Qed.
