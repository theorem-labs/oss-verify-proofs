(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import InitMem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AKit ECH_AsKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma zx32_lit : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma sx32_lit : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. apply (sx32_wz x Hx). Qed.

(* [comment removed for export] *)
Lemma bio_flags_byte : forall m a B, rw_cells asegs m a (bio_cells B) ->
  ov_read_bytes asegs m (wa (a + 48)) 1 = Some [b8 (bio_flags B mod 256)].
Proof.
  intros m a B [[_ HB] _]. replace (a + 48) with (a + Z.of_nat 48) by lia.
  rewrite (bytes_at_ov_read asegs m a (cells_bytes (bio_cells B)) 48 1 HB) by (cbn; lia).
  cbn. f_equal. f_equal. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (256 * 2^56).
  rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.mod_add, Z.mod_mod by lia. reflexivity.
Qed.
Lemma land_mod256_128 : forall f, 0 <= f -> Z.land (f mod 256) 128 = Z.land f 128.
Proof.
  intros f Hf. change 256 with (2^8). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lxor_top7 : forall n, 0 <= n < 2^63 -> Z.lxor n 9223372036854775808 = n + 9223372036854775808.
Proof.
  intros n Hn. symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec k 63) as [->|NE].
  - rewrite (Z.bits_above_log2 n 63); [reflexivity| lia|].
    destruct (Z.eq_dec n 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - replace (Z.testbit 9223372036854775808 k) with false; [apply Bool.andb_false_r|].
    symmetry. change 9223372036854775808 with (2^63). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
Lemma sgtz_mask : forall n, 0 < n < 2^63 ->
  Z.land ((0 + - Z.b2z (9223372036854775808 <? Z.lxor n 9223372036854775808)) mod 18446744073709551616) n = n.
Proof.
  intros n Hn. rewrite lxor_top7 by lia.
  replace (9223372036854775808 <? n + 9223372036854775808) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  change ((0 + - (1)) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma sgtz_mask_as : forall n, 0 < n < 2^63 ->
  Z.land (Z.land (0 - Z.b2z (9223372036854775808 <? Z.lxor n 9223372036854775808)) 18446744073709551615) n = n.
Proof.
  intros n Hn. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  replace (0 - Z.b2z (9223372036854775808 <? Z.lxor n 9223372036854775808)) with (0 + - Z.b2z (9223372036854775808 <? Z.lxor n 9223372036854775808)) by lia.
  apply sgtz_mask. exact Hn.
Qed.

(* [comment removed for export] *)
Lemma rdonly_off0 : forall f, 0 <= f < 2^31 -> Z.land f 512 = 512 ->
  Z.land (Z.shiftr (Z.lxor f 18446744073709551615) 6) 8 = 0.
Proof.
  intros f Hf H9. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.shiftr_spec, Z.lxor_spec, Z.bits_0 by lia.
  destruct (Z.eq_dec n 3) as [->|NE].
  - cbn [Z.add]. change 18446744073709551615 with (Z.ones 64). rewrite Z.ones_spec_low by lia.
    assert (B9 : Z.testbit f 9 = true).
    { apply (f_equal (fun z => Z.testbit z 9)) in H9. rewrite Z.land_spec in H9. change (Z.testbit 512 9) with true in H9.
      rewrite Bool.andb_true_r in H9. exact H9. }
    cbn [Z.add Pos.add Pos.succ] in *. rewrite ?B9. try reflexivity.
    all: try (replace (Z.testbit f (3 + 6)) with true by (symmetry; exact B9); reflexivity).
  - replace (Z.testbit 8 n) with false; [apply Bool.andb_false_r|].
    symmetry. destruct (Z.eq_dec n 0) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 1) as [->|]; [reflexivity|].
    destruct (Z.eq_dec n 2) as [->|]; [reflexivity|].
    apply Z.bits_above_log2; [lia|]. cbn. lia.
Qed.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.
  Lemma ACONST_stack_frame7 : forall m m' lo hi, ACONST m -> munch [(lo, hi)] m m' -> wmono asegs m m' -> aceil <= lo -> ACONST m'.
  Proof.
    intros m m' lo hi AC MU WM CE. eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    constructor; [| constructor]. apply aconst_ok_high; cbn [fst snd]; acb; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
  Qed.
End HCW.

(* [comment removed for export] *)
Ltac membio_tac :=
  unfold MEMBIO, mb_after_bread, mb_after_read, mb_advance, mb_with_hdr, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, BIO_FLAGS_MEM_RDONLY, BIO_FLAGS_RETRY_MASK;
  cbn [mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid];
  repeat lazymatch goal with |- _ /\ _ => split end;
  try assumption; try lia;
  try (unfold bio_cells, membio_bio, buf_cells, wz;
       cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite bm_len bm_data bm_max bm_flags
            mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid];
       first [assumption | rewrite ?Z.add_0_r; assumption]).

(* [comment removed for export] *)
Ltac extm MU WM MUc WMc :=
  lazymatch type of MU with munch ?Wfull ?mpre ?mmid =>
  lazymatch type of MUc with munch ?Wc mmid ?mpost =>
    let T := fresh "MUx" in
    assert (T : munch Wfull mpre mpost)
      by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [|exact MUc];
          let xa := fresh "xa" in let Hxa := fresh "Hxa" in
          intros xa Hxa; cbn [outside MEMBIO_foot sub_fp] in Hxa |- *; unfold BIO_SIZE, BUFMEM_SIZE, BIOBUFMEM_SIZE in Hxa |- *; lia);
    clear MU MUc; rename T into MU;
    let T2 := fresh "WMx" in pose proof (wmono_trans _ _ _ _ WM WMc) as T2; clear WM WMc; rename T2 into WM
  end end.

(* [comment removed for export] *)
Definition hidden (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change (hidden T) in H end.
Ltac unhide H := unfold hidden in H.


(* [comment removed for export] *)
Ltac norm_addr H :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?a ?cs => let v := eval vm_compute in a in change (rw_cells segs m v cs) in H
  | bytes_at ?segs ?m ?a ?bs => let v := eval vm_compute in a in change (bytes_at segs m v bs) in H
  end.
Ltac land_exs PO :=
  let T := type of PO in let T' := eval hnf in T in
  lazymatch T' with
  | ex _ => let v := fresh "v" in destruct PO as [v PO]; land_exs PO
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac alandx MU WM :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO; land_exs PO; destruct_ands PO; subst ms';
  lazymatch type of MU with munch _ _ ?mmid =>
    match goal with MUc : munch _ mmid ?mpost |- _ =>
      match goal with WMc : wmono _ mmid mpost |- _ =>
        rewrite ?unsigned_lit in MUc by lia;
        repeat match goal with H : context [bv_unsigned (Z_to_bv 64 _)] |- _ =>
          lazymatch type of H with munch _ _ _ => fail | hidden _ => fail | id _ => fail | _ => rewrite ?unsigned_lit in H by lia end end;
        carry MUc WMc; extm MU WM MUc WMc
      end
    end
  end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    repeat match goal with H : mem_inv _ ?mx |- _ => lazymatch mx with mc => fail | _ => clear H end end;
    repeat match goal with H : stale _ |- _ => clear H end;
    try (lazymatch goal with _ : stk _ mc _ _ |- _ => idtac end;
         match goal with H : stk _ mc _ _ |- _ => rename H into ST end)
  end;
  try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end);
  repeat match goal with H : ?v = Z_to_bv 64 _ |- _ => is_var v; subst v end.

(* [comment removed for export] *)
Ltac aland_open MU :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO; land_exs PO; destruct_ands PO; subst ms';
  lazymatch type of MU with munch _ _ ?mmid =>
    match goal with X : munch _ mmid ?mpost |- _ =>
      match goal with Y : wmono _ mmid mpost |- _ =>
        rewrite ?unsigned_lit in X by lia; rename X into MUc; rename Y into WMc
      end
    end
  end;
  repeat match goal with X : context [bv_unsigned (Z_to_bv 64 _)] |- _ =>
    lazymatch type of X with munch _ _ _ => fail | hidden _ => fail | id _ => fail | _ => rewrite ?unsigned_lit in X by lia end end.
Ltac carry1_core MUc WMc H :=
  lazymatch type of MUc with munch ?W ?m0 ?m1 =>
  lazymatch type of H with
  | rw_cells ?segs m0 ?A ?cs => apply (fun HH => @rw_cells_transport segs W m0 m1 A cs HH MUc WMc) in H; [| cbn; lia]
  | bytes_at ?segs m0 ?A ?bs => apply (fun HH => @bytes_at_transport segs W m0 m1 A bs HH MUc) in H; [| cbn; lia]
  | stk ?segs m0 ?lo ?hi => apply (fun HH => @stk_transport_disjoint segs W m0 m1 lo hi HH MUc WMc) in H; [| cbn; lia]
  end end.
Tactic Notation "carry1" constr(MUc) constr(WMc) hyp(H) := carry1_core MUc WMc H.
Ltac rehide F := lazymatch type of F with hidden _ => idtac | ?T => change (hidden T) in F end.
(* [comment removed for export] *)
Ltac carry1k_core MUc WMc H tac :=
  lazymatch type of MUc with munch ?W ?m0 ?m1 =>
  lazymatch type of H with
  | rw_cells ?segs m0 ?A ?cs =>
      let T := fresh "CT" in
      assert (T : rw_cells segs m1 A cs) by (tac; apply (fun HH => @rw_cells_transport segs W m0 m1 A cs HH MUc WMc); [exact H| cbn; lia]);
      clear H; rename T into H
  | bytes_at ?segs m0 ?A ?bs =>
      let T := fresh "CT" in
      assert (T : bytes_at segs m1 A bs) by (tac; apply (fun HH => @bytes_at_transport segs W m0 m1 A bs HH MUc); [exact H| cbn; lia]);
      clear H; rename T into H
  | stk ?segs m0 ?lo ?hi =>
      let T := fresh "CT" in
      assert (T : stk segs m1 lo hi) by (tac; apply (fun HH => @stk_transport_disjoint segs W m0 m1 lo hi HH MUc WMc); [exact H| cbn; lia]);
      clear H; rename T into H
  end end.
Tactic Notation "carry1k" constr(MUc) constr(WMc) hyp(H) "by" tactic3(tac) := carry1k_core MUc WMc H tac.
Tactic Notation "carry1" constr(MUc) constr(WMc) hyp(H) "using" hyp(F) := unfold hidden in F; carry1_core MUc WMc H; rehide F.
Tactic Notation "carry1" constr(MUc) constr(WMc) hyp(H) "using" hyp(F) hyp(G) := unfold hidden in F, G; carry1_core MUc WMc H; rehide F; rehide G.
Ltac aland_close MU WM MUc WMc :=
  lazymatch type of MUc with munch _ ?m0 ?m1 =>
    repeat match goal with
           | X : rw_cells _ m0 _ _ |- _ => clear X
           | X : bytes_at _ m0 _ _ |- _ => clear X
           | X : stk _ m0 _ _ |- _ => clear X
           | X : mem_inv _ m0 |- _ => clear X
           end;
    extm MU WM MUc WMc;
    try (lazymatch goal with _ : stk _ m1 _ _ |- _ => idtac end;
         match goal with X : stk _ m1 _ _ |- _ => rename X into ST end)
  end;
  try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end);
  repeat match goal with X : ?v = Z_to_bv 64 _ |- _ => is_var v; subst v end.

Section HCW2.
  Context {HCEIL : HeapCeil}.
  (* [comment removed for export] *)
  Lemma addressable_across_stack : forall m m' lo hi A n, addressable m A n -> aapp A n ->
    munch [(lo, hi)] m m' -> wmono asegs m m' -> aceil <= lo -> addressable m' A n.
  Proof.
    intros m m' lo hi A n AD AP MU WM CE. eapply addressable_transport; [exact AD| exact MU| exact WM|].
    pose proof (sh_aapp_range A n AP ltac:(destruct AD; lia)) as (S1 & S2 & S3). unfold AHI_LO in S3. pose proof aceil_range. cbn. lia.
  Qed.
  Lemma MEMBIO_shad_across_stack : forall H LB m0 m m' lo hi a R, MEMBIO H LB m0 a R -> MEMBIO_shad m a R ->
    munch [(lo, hi)] m m' -> wmono asegs m m' -> aceil <= lo -> MEMBIO_shad m' a R.
  Proof.
    intros H LB m0 m m' lo hi a R MB (S1 & S2 & S3 & S4) MU WM CE.
    destruct MB as (_ & _ & _ & _ & _ & _ & _ & _ & RB1 & RB2 & RB3 & RB4 & _).
    pose proof RB1 as (_ & _ & _ & _ & _ & _ & AP1). pose proof RB2 as (_ & _ & _ & _ & _ & _ & AP2).
    pose proof RB3 as (_ & _ & _ & _ & _ & _ & AP3). pose proof RB4 as (_ & _ & _ & _ & _ & _ & AP4).
    split; [| split; [| split]]; (eapply addressable_across_stack; [eassumption| eassumption| exact MU| exact WM| exact CE]).
  Qed.
  (* [comment removed for export] *)
  Lemma accessible_across2 : forall W m m' A n,
    accessible m A n -> munch W m m' -> Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) W -> accessible m' A n.
  Proof.
    intros W m m' A n ACC MU HW. eapply accessible_transport; [exact ACC| exact MU|].
    intros x Hx. destruct ACC as (Q0 & Q1 & _).
    assert (SX : ASHADOW_BASE <= sh x < AHI_LO).
    { split; [unfold sh; Z.div_mod_to_equations; lia|].
      pose proof (sh_nsh_high x 1 ltac:(lia) ltac:(lia) ltac:(lia)) as K. unfold nsh in K. change ((1 + 7) / 8) with 1 in K. lia. }
    clear - HW SX. induction W as [|[lo hi] W IH]; [exact I|]. cbn. pose proof (Forall_inv HW) as K1. cbn in K1.
    split; [lia| exact (IH (Forall_inv_tail HW))].
  Qed.
  (* [comment removed for export] *)
  Lemma shvis_across2 : forall W m m' lo hi,
    shvis m lo hi -> munch W m m' -> wmono asegs m m' -> 0 <= lo -> lo <= hi <= AAPP_HI ->
    Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) W -> shvis m' lo hi.
  Proof.
    intros W m m' lo hi SV MU WM L0 LH HW. eapply shvis_transport; [exact SV| exact MU| exact WM|].
    pose proof (hull_lo_le lo L0) as (A1 & A2 & A3). pose proof (hull_hi_ge hi ltac:(lia)) as (B1 & B2 & B3).
    assert (S1 : ASHADOW_BASE <= sh (hull_lo lo)) by (unfold sh; Z.div_mod_to_equations; lia).
    assert (HH2 : hull_hi hi <= AAPP_HI) by (unfold hull_hi, AAPP_HI in *; Z.div_mod_to_equations; lia).
    assert (S2 : sh (hull_hi hi) <= AHI_LO) by (unfold sh, AHI_LO, AAPP_HI in *; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    clear - HW S1 S2. induction W as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv HW) as K1. cbn in K1.
    split; [lia| exact (IH (Forall_inv_tail HW))].
  Qed.
  (* [comment removed for export] *)
  Lemma ACONST_memrd : forall m m' lo hi out oe a bm, ACONST m ->
    munch [(lo, hi); (out, oe); (a, a + 128); (bm, bm + 32)] m m' -> wmono asegs m m' -> aceil <= lo ->
    aconst_ok (out, oe) -> aapp a 128 -> aapp bm 32 -> ACONST m'.
  Proof.
    intros m m' lo hi out oe a bm AC MU WM CE OK APa APbm. eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    constructor. { apply aconst_ok_high; cbn [fst snd]; acb; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia. }
    constructor; [exact OK|]. constructor. { eapply aconst_ok_aapp; [exact APa| cbn; lia| cbn; lia]. }
    constructor; [| constructor]. eapply aconst_ok_aapp; [exact APbm| cbn; lia| cbn; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma addressable_across2 : forall W m m' A n, addressable m A n -> aapp A n ->
    munch W m m' -> wmono asegs m m' -> Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) W -> addressable m' A n.
  Proof.
    intros W m m' A n AD AP MU WM HW. eapply addressable_transport; [exact AD| exact MU| exact WM|].
    pose proof (sh_aapp_range A n AP ltac:(destruct AD; lia)) as (S1 & S2 & S3).
    pose proof (aapp_bounds A n AP ltac:(destruct AD; lia)) as (B1 & _ & _ & B4 & _).
    assert (S0 : ASHADOW_BASE <= sh A) by (unfold sh; Z.div_mod_to_equations; lia).
    clear - HW S0 S2 S3. induction W as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv HW) as K1. cbn in K1.
    split; [lia| exact (IH (Forall_inv_tail HW))].
  Qed.
  Lemma MEMBIO_shad_across2 : forall H LB W m0 m m' a R, MEMBIO H LB m0 a R -> MEMBIO_shad m a R ->
    munch W m m' -> wmono asegs m m' -> Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) W -> MEMBIO_shad m' a R.
  Proof.
    intros H LB W m0 m m' a R MB (S1 & S2 & S3 & S4) MU WM HW.
    destruct MB as (_ & _ & _ & _ & _ & _ & _ & _ & RB1 & RB2 & RB3 & RB4 & _).
    pose proof RB1 as (_ & _ & _ & _ & _ & _ & AP1). pose proof RB2 as (_ & _ & _ & _ & _ & _ & AP2).
    pose proof RB3 as (_ & _ & _ & _ & _ & _ & AP3). pose proof RB4 as (_ & _ & _ & _ & _ & _ & AP4).
    split; [| split; [| split]]; (eapply addressable_across2; [eassumption| eassumption| exact MU| exact WM| exact HW]).
  Qed.
  (* [comment removed for export] *)
  Lemma accessible_across_stack : forall m m' lo hi A n, accessible m A n -> munch [(lo, hi)] m m' -> aceil <= lo -> accessible m' A n.
  Proof.
    intros m m' lo hi A n ACC MU CE. eapply accessible_across; [exact ACC| exact MU|].
    constructor; [| constructor]. right. cbn. pose proof aceil_range. unfold AHI_LO. lia.
  Qed.
End HCW2.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Z_to_le_bytes_of_bytes : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
  assert (Hnn : 0 <= bytes_le_to_Z bs).
  { clear IH. induction bs as [|c cs IHc]; cbn; [lia|]. apply Z.lor_nonneg. split; [apply bv_unsigned_in_range|]. apply Z.shiftl_nonneg. exact IHc. }
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
    rewrite (Z.land_ones (bv_unsigned b) 8) by lia. rewrite Z.mod_small by lia.
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0; [rewrite Z.lor_0_r; reflexivity|].
    symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8).
    + rewrite Z.shiftl_spec_low by lia. reflexivity.
    + rewrite Z.ones_spec_high by lia. apply andb_false_r.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_eq_0 (bv_unsigned b) 8); [rewrite Z.lor_0_l; exact IH | lia |].
    destruct (Z.eq_dec (bv_unsigned b) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma bytes_le_to_Z_bound8 : forall bs, length bs = 8%nat -> 0 <= bytes_le_to_Z bs < 2^64.
Proof.
  intros bs L. pose proof (bytes_le_to_Z_bound bs) as B. pose proof (bytes_le_to_Z_nonneg bs) as B0. rewrite L in B.
  change (2 ^ (8 * Z.of_nat 8)) with (2^64) in B. lia.
Qed.
Lemma le8_wz_of_bytes : forall bs, length bs = 8%nat -> le8 (wz (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, wz. rewrite unsigned_lit by (apply bytes_le_to_Z_bound8; exact L).
  rewrite <- L. apply Z_to_le_bytes_of_bytes.
Qed.
(* [comment removed for export] *)
Lemma rw_cells_CB8_C8 : forall segs m A pre bs post,
  rw_cells segs m A (pre ++ CB 8 bs :: post) -> rw_cells segs m A (pre ++ C8 (wz (bytes_le_to_Z bs)) :: post).
Proof.
  intros segs m A pre bs post [[Hwf Hb] Hw].
  pose proof Hwf as W0. apply cells_wf_app in W0. destruct W0 as [_ [L _]]. cbn in L.
  split; [split|].
  - apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [W1 [_ W3]]. split; [exact W1|]. split; [exact I| exact W3].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le8_wz_of_bytes by exact L. exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma land_m32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x - x mod 32.
Proof.
  intros x Hx. change 18446744073709551584 with (Z.ones 64 - Z.ones 5).
  replace (Z.ones 64 - Z.ones 5) with (Z.lxor (Z.ones 64) (Z.ones 5)) by reflexivity.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.lxor_spec.
  assert (E : x - x mod 32 = Z.shiftl (Z.shiftr x 5) 5).
  { rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia. }
  rewrite E. destruct (Z.lt_ge_cases i 5) as [L|L].
  - rewrite Z.shiftl_spec_low, (Z.ones_spec_low 5), (Z.ones_spec_low 64) by lia. cbn. apply andb_false_r.
  - rewrite Z.shiftl_spec_high, Z.shiftr_spec, (Z.ones_spec_high 5) by lia. replace (i - 5 + 5) with i by lia.
    destruct (Z.lt_ge_cases i 64) as [M|M].
    + rewrite (Z.ones_spec_low 64) by lia. cbn. apply andb_true_r.
    + rewrite (Z.ones_spec_high 64) by lia. cbn. rewrite andb_false_r.
      symmetry. apply Z.bits_above_log2; [lia|]. destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|].
      apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia| lia].
Qed.

(* [comment removed for export] *)
Lemma hull_lo_ge_aligned : forall B a, B mod 64 = 0 -> B <= a -> B <= hull_lo a.
Proof. intros B a HB Ha. unfold hull_lo. Z.div_mod_to_equations. nia. Qed.
Lemma hull_hi_le_aligned : forall B b, B mod 64 = 0 -> 0 <= b <= B -> hull_hi b <= B.
Proof. intros B b HB Hb. unfold hull_hi. Z.div_mod_to_equations. nia. Qed.

Section FF.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Lemma relro_cell7 : forall m A cs, arelro_lib m -> 0x571000 <= A -> A + Z.of_nat (cells_size cs) <= 0x5ea000 ->
    cells_wf cs -> rw_bytes_b asegs A (cells_bytes cs) = true -> rw_cells asegs m A cs.
  Proof.
    intros m A cs RL HA HB WF RB. pose proof (cells_bytes_length cs WF) as L.
    apply (arw_cells_recut m A [CB (length (cells_bytes cs)) (cells_bytes cs)] cs); [| exact WF| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
    apply none_on_rw_cells; [| exact RB| lia| rewrite L; lia].
    intros a Ha. apply RL. rewrite L in Ha. lia.
  Qed.
  Lemma acc8_of_C1_7 : forall m A, rw_cells asegs m (sh A) [C1 (b8 0)] -> 0 <= A -> A mod 8 = 0 -> A + 8 <= AAPP_HI -> accessible m A 8.
  Proof.
    intros m A RC HA HM HT.
    assert (AD : addressable m A 8).
    { split; [lia|]. change (shadow_of 8) with [b8 0]. apply (SHAD_of_rw_cells m A 1); [exact HA| exact HM|].
      pose proof (rw_cells_merge asegs m (sh A) [] [C1 (b8 0)] []) as M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
      apply M. exact RC. }
    eapply addressable_accessible; [exact AD| lia| lia| exact HT].
  Qed.
  Lemma arelro_across7 : forall W m m', arelro_lib m -> munch W m m' -> Forall (fun iv : Z * Z => snd iv <= 0x571000 \/ 0x5ea000 <= fst iv) W -> arelro_lib m'.
  Proof.
    intros W m m' RL MU FW i Hi. rewrite <- (RL i Hi). unfold wa. apply MU. rewrite unsigned_lit by lia.
    clear - FW Hi. induction W as [|[lo hi] W IH]; [exact I|]. cbn. pose proof (Forall_inv FW) as K. cbn in K.
    split; [lia| exact (IH (Forall_inv_tail FW))].
  Qed.

  (* [comment removed for export] *)
  Lemma fs_scratch_below_ceil : forall LF m iv, as_RFS H LF m -> fs_scratch H LF iv -> snd iv <= aceil.
  Proof.
    intros LF m iv R [->|(k & ff & fp & FF & E)].
    - cbn [fst snd]. destruct (proj1 (ah_RFS_range H HH _ _ R)) as (F1 & F2 & F3 & F4). unfold AFS_FLAGS, AFS_SIZE in *. lia.
    - pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      pose proof (fsz_pos k ltac:(lia)). acb.
      destruct E as [-> |[-> | ->]]; cbn [fst snd]; [lia| lia|].
      assert (SH : sh ff + fshn k <= sh aceil) by (rewrite fshn_nsh by lia; pose proof (sh_aapp_range ff (fsz k) ltac:(eapply aapp_sub; [exact P9| unfold AFS_HDR in *; lia| lia]) ltac:(lia)); lia).
      unfold sh in *. rewrite ASHADOW_BASE_val in *. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fsobj_scratch_hull : forall LF O n m iv,
    as_RFS H LF m -> fsobj H LF O n -> 0 <= O -> 0 <= n -> O + n <= AAPP_HI -> fs_scratch H LF iv ->
    sh (hull_hi (O + n)) <= fst iv \/ snd iv <= sh (hull_lo O).
  Proof.
    intros LF O n m iv R OB HO Hn Htop SC.
    pose proof (hull_lo_le O HO) as (A1 & A2 & A3). pose proof (hull_hi_ge (O + n) ltac:(lia)) as (B1 & B2 & B3).
    assert (S1 : ASHADOW_BASE <= sh (hull_lo O)) by (unfold sh; Z.div_mod_to_equations; lia).
    assert (HH2 : hull_hi (O + n) <= AAPP_HI) by (unfold hull_hi, AAPP_HI in *; Z.div_mod_to_equations; lia).
    assert (S2 : sh (hull_hi (O + n)) <= AHI_LO) by (unfold sh, AHI_LO, AAPP_HI in *; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    destruct (proj1 (ah_RFS_range H HH _ _ R)) as (F1 & F2 & F3 & F4). acb.
    destruct SC as [->|(k & ff & fp & FF & E)].
    - cbn [fst snd]. pose proof (aapp_not_shadowland _ _ F4). unfold AFS_FLAGS, AFS_SIZE, ALOWSH_LO, AHI_LO in *. rewrite ASHADOW_BASE_val in *. lia.
    - pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      pose proof (fsz_pos k ltac:(lia)) as FP. pose proof (aapp_not_shadowland _ _ P9) as NSF.
      destruct E as [-> |[-> | ->]]; cbn [fst snd].
      + unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, ALOWSH_LO, AHI_LO in *. rewrite ASHADOW_BASE_val in *. lia.
      + unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, ALOWSH_LO, AHI_LO in *. rewrite ASHADOW_BASE_val in *. lia.
      + (* [comment removed for export] *)
        assert (SHK : sh ff + fshn k = sh (ff + fsz k)).
        { replace (fsz k) with (8 * fshn k) by (unfold fsz, fshn; lia). symmetry. apply sh_add8. }
        rewrite SHK.
        destruct OB as [[OB|OB]|(f & IN & D1 & D2)].
        * left. apply sh_mono. eapply Z.le_trans; [apply (hull_hi_le_aligned (as_FSB H)); [Z.div_mod_to_equations; lia| lia]|]. unfold AFS_HDR in *; lia.
        * right. apply sh_mono. eapply Z.le_trans; [| apply (hull_lo_ge_aligned (as_FSB H + AFS_SIZE)); [unfold AFS_SIZE; Z.div_mod_to_equations; lia| lia]]. lia.
        * destruct FF as (_ & _ & D). destruct (D f IN) as [DJ NF].
          pose proof (proj2 (ah_RFS_range H HH _ _ R) f IN) as (K' & Q1 & Q2 & Q3 & Q4). pose proof (fsz_pos (ff_class f) ltac:(lia)) as FP'.
          assert (FA' : exists q, fsz (ff_class f) = 64 * q). { unfold fsz. exists (2 ^ ff_class f). lia. }
          destruct FA' as [q Hq].
          assert (DV : (64 | fsz (ff_class f))) by (exists q; lia).
          assert (DA : (64 | ff_addr f)).
          { apply (Z.divide_trans _ (fsz (ff_class f))); [exact DV|]. apply Z.mod_divide; [lia| exact Q3]. }
          assert (AL1 : ff_addr f mod 64 = 0) by (apply Z.mod_divide; [lia| exact DA]).
          assert (AL2 : (ff_addr f + fsz (ff_class f)) mod 64 = 0) by (apply Z.mod_divide; [lia|]; apply Z.divide_add_r; [exact DA| exact DV]).
          pose proof (hull_lo_ge_aligned _ _ AL1 D1) as G1. pose proof (hull_hi_le_aligned _ (O + n) AL2 ltac:(lia)) as G2.
          destruct DJ as [DJ|DJ].
          -- right. apply sh_mono. lia.
          -- left. apply sh_mono. lia.
  Qed.
End FF.

(* [comment removed for export] *)
Ltac nsw_tac :=
  repeat (constructor; [cbn [fst snd]; pose proof aceil_range; unfold in_app_mem, AHI_LO, ALOWSH_LO, AAPP_HI in *; rewrite ?ASHADOW_BASE_val in *; lia |]); constructor.

(* [comment removed for export] *)
Ltac membio_open m a R MB BL SH AC :=
  let MB0 := fresh "MB0" in
  pose proof MB as MB0;
  destruct MB0 as (BC & BBC & BMC & RPC & I1 & I2 & I3 & I4 & RB1 & RB2 & RB3 & RB4 & POSR & LENR & BUFP & BUFH & FLR & RDO & AEOF & NUMR & NRD & NRD2 & NXT & PRV);
  pose proof RB1 as (AP & AAL & _ & AH & _ & _ & AAP); pose proof RB2 as (BBP & BBAL & _ & BBH & _ & _ & BBAP);
  pose proof RB3 as (BMP & BMAL & _ & BMH & _ & _ & BMAP); pose proof RB4 as (RPP & RPAL & _ & RPH & _ & _ & RPAP);
  destruct BL as (BL1 & BL2 & BL3 & BL4); destruct SH as (SHa & SHbb & SHbm & SHrp);
  unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, BIO_FLAGS_MEM_RDONLY, BIO_CTRL_EOF, BIO_CTRL_PUSH, AIMG_TOP in *;
  unfold bio_cells, membio_bio, wz in BC;
  cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC;
  unfold wz in BBC; unfold buf_cells, wz in BMC, RPC; cbn [bm_len bm_data bm_max bm_flags] in BMC, RPC;
  pose proof (ACONST_shbase _ AC) as [GSB SHB]; unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB; rewrite ASHADOW_BASE_val in SHB;
  pose proof (aapp_not_shadowland _ _ AAP) as NSa; pose proof (aapp_not_shadowland _ _ BBAP) as NSbb;
  pose proof (aapp_not_shadowland _ _ BMAP) as NSbm; pose proof (aapp_not_shadowland _ _ RPAP) as NSrp;
  pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (_ & _ & AHIa & _); pose proof (aapp_bounds _ _ BBAP ltac:(lia)) as (_ & _ & AHIbb & _);
  pose proof (aapp_bounds _ _ BMAP ltac:(lia)) as (_ & _ & AHIbm & _); pose proof (aapp_bounds _ _ RPAP ltac:(lia)) as (_ & _ & AHIrp & _);
  unfold AAPP_HI in AHIa, AHIbb, AHIbm, AHIrp;
  assert (ACCa : id (accessible m a 128)) by (unfold id; eapply addressable_accessible; [exact SHa| lia| lia| unfold AAPP_HI; lia]);
  assert (ACCbb : id (accessible m (mb_bb R) 16)) by (unfold id; eapply addressable_accessible; [exact SHbb| lia| lia| unfold AAPP_HI; lia]);
  assert (ACCbm : id (accessible m (mb_bm R) 32)) by (unfold id; eapply addressable_accessible; [exact SHbm| lia| lia| unfold AAPP_HI; lia]);
  assert (ACCrp : id (accessible m (mb_rp R) 32)) by (unfold id; eapply addressable_accessible; [exact SHrp| lia| lia| unfold AAPP_HI; lia]).

(* [comment removed for export] *)
Ltac membio_reacc MU :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of MU with munch ?W _ mx =>
      let NSW := fresh "NSW" in
      assert (NSW : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) W)
        by (repeat (constructor; [cbn [fst snd]; pose proof aceil_range; unfold in_app_mem, AHI_LO, ALOWSH_LO, AAPP_HI in *; rewrite ?ASHADOW_BASE_val in *; lia |]); constructor);
      repeat match goal with A : id (accessible ?m0 ?x ?n) |- _ =>
               tryif constr_eq m0 mx then fail else
                 (let T := fresh "ACC" in
                  assert (T : id (accessible mx x n)) by (unfold id in A |- *; eapply accessible_across2; [exact A| exact MU| exact NSW]);
                  clear A; rename T into A)
             end;
      clear NSW
  end end.

Ltac ubal_side H := first [ (revert H; clear; intros H; lia) | (lazymatch goal with |- 0 <= _ < _ => lia end) ].
Ltac ubal_any :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    first
    [ lazymatch R with context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] =>
        match goal with H : _ mod _ = 0 |- _ => rewrite (al8u x) by ubal_side H end end
    | lazymatch R with context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 3] =>
        match goal with H : _ mod _ = 0 |- _ => rewrite (al4u x) by ubal_side H end end
    | lazymatch R with context [Z.land ?x 7] =>
        match goal with H : _ mod _ = 0 |- _ => rewrite (al8 x) by ubal_side H end end
    | lazymatch R with context [Z.land ?x 3] =>
        match goal with H : _ mod _ = 0 |- _ => rewrite (al4 x) by ubal_side H end end
    | idtac ]
  end.
Ltac ltu0 :=
  lazymatch goal with |- evt _ _ (MS _ _ (if bv_ltu ?x (Z_to_bv 64 0) then _ else _) _ _ _ _) =>
    replace (bv_ltu x (Z_to_bv 64 0)) with false
      by (rewrite bv_ltu_Z; symmetry; apply Z.ltb_ge; rewrite (unsigned_lit 0) by lia; pose proof (aword_range x); lia);
    cbv iota end.
