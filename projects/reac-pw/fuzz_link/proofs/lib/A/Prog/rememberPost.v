(* remember (image A, fuzz_link.asan 0x89db4): the byte algebra of its Post. Facts about byte lists and the A
   views only, with no symbolic run and no journal in them; the walk lib/A/Prog/remember.v applies them at
   `pa_segs`.
   - the A view and the byte read (`ambyte_of_aview`, `aview_of_ambyte`);
   - the marks block read as link_spec.v's `mk_names` (`amk_names_length`, `amk_names_nth`), the slot each
     wrapper_strcmp of the loop reads (`amk_slot_cstr`, `amk_slot_len`) and the count word m->n (`amk_n_val`);
   - the two return paths that leave the block as it was (`rem_marks_kept`, `rem_post_kept`, with
     `remember_hit` / `remember_full`);
   - the append path (`rem_marks_after_a`): the end memory read back as a list (LinkWalk.v `abytes_of`), its
     count word is n + 1 (the store at +0xc8), slot n holds the name and its NUL (snprintf), every other byte is
     the byte it was.
   The plain build's lib/Prog/remember_aux.v `rem_marks_after` and lib/Prog/mk_marks.v are the model; they are
   not importable on image A, so the list lemmas this file needs are proved again here.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem model_decide_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk remember_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ==========================================================================
   1. Byte lists: C strings, existsb, remember
   ========================================================================== *)

Lemma rp_byte_zero : forall b : byte, bz b = 0 -> b = zb 0.
Proof.
  intros b E. apply bv_eq. unfold bz in E. rewrite E. unfold zb. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* a byte list with a NUL holds its C string, then the NUL *)
Lemma rp_cstr_split : forall l, (nul_at l < length l)%nat ->
  exists rest, l = cstr l ++ [zb 0] ++ rest /\ ~ In (zb 0) (cstr l).
Proof.
  induction l as [|b l IH]; intros H; [cbn in H; lia|].
  unfold cstr in *. cbn [nul_at length] in *.
  destruct (Z.eqb_spec (bz b) 0) as [E|E].
  - exists l. cbn [firstn app]. rewrite (rp_byte_zero b E). split; [reflexivity | intros []].
  - destruct (IH ltac:(lia)) as (rest & Hl & Hn). exists rest.
    cbn [firstn app]. split; [f_equal; exact Hl|].
    intros [Hb|Hin]; [apply E; rewrite Hb; reflexivity | exact (Hn Hin)].
Qed.

Lemma cstr_app_nul : forall s rest, ~ In (zb 0) s -> cstr (s ++ [zb 0] ++ rest) = s.
Proof.
  induction s as [|b s IH]; intros rest Hn; unfold cstr in *; cbn [app nul_at firstn].
  - reflexivity.
  - assert (Hb : bz b <> 0) by (intros E; apply Hn; left; apply rp_byte_zero; exact E).
    replace (bz b =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb). cbn [firstn].
    f_equal. apply IH. intros H; apply Hn; right; exact H.
Qed.

Lemma nul_at_app_nul : forall s rest, ~ In (zb 0) s -> nul_at (s ++ [zb 0] ++ rest) = length s.
Proof.
  induction s as [|b s IH]; intros rest Hn; cbn [app nul_at length].
  - reflexivity.
  - assert (Hb : bz b <> 0) by (intros E; apply Hn; left; apply rp_byte_zero; exact E).
    replace (bz b =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb).
    change (S (nul_at (s ++ [zb 0] ++ rest)) = S (length s)).
    f_equal. apply IH. intros H; apply Hn; right; exact H.
Qed.

Lemma rp_cstr_length : forall l, (length (cstr l) <= nul_at l)%nat.
Proof. intros l. unfold cstr. rewrite length_firstn. lia. Qed.

Lemma existsb_none : forall (l : list (list byte)) x,
  (forall j, (j < length l)%nat -> nth_error l j <> Some x) -> existsb (fun y => bl_eqb y x) l = false.
Proof.
  induction l as [|y l IH]; intros x H; [reflexivity|]. cbn [existsb].
  destruct (bl_eqb y x) eqn:E.
  - exfalso. apply bl_eqb_iff in E. subst y. apply (H 0%nat); [cbn; lia | reflexivity].
  - cbn [orb]. apply IH. intros j Hj. apply (H (S j)). cbn; lia.
Qed.

Lemma existsb_some : forall (l : list (list byte)) x j, nth_error l j = Some x ->
  existsb (fun y => bl_eqb y x) l = true.
Proof.
  induction l as [|y l IH]; intros x j H; [destruct j; discriminate|]. cbn [existsb].
  destruct j as [|j]; cbn in H.
  - injection H as ->. rewrite bl_eqb_refl. reflexivity.
  - rewrite (IH x j H). apply orb_true_r.
Qed.

(* the two paths of `remember` that keep the list *)
Lemma remember_hit : forall l nm, existsb (fun y => bl_eqb y nm) l = true -> remember l nm = l.
Proof. intros l nm H. unfold remember. rewrite H. reflexivity. Qed.

Lemma remember_full : forall l nm, Z.of_nat (length l) = MARKS_MAX -> remember l nm = l.
Proof.
  intros l nm H. unfold remember. destruct (existsb (fun x => bl_eqb x nm) l); [reflexivity|].
  rewrite H, Z.ltb_irrefl. reflexivity.
Qed.

(* the append path of `remember`, for a name of at most 15 bytes *)
Lemma remember_miss : forall l nm, existsb (fun y => bl_eqb y nm) l = false ->
  Z.of_nat (length l) < MARKS_MAX -> (length nm <= 15)%nat -> remember l nm = l ++ [nm].
Proof.
  intros l nm Ex Hl Ln. unfold remember. rewrite Ex.
  replace (Z.of_nat (length l) <? MARKS_MAX) with true by (symmetry; apply Z.ltb_lt; exact Hl).
  rewrite firstn_all2 by exact Ln. reflexivity.
Qed.

(* ==========================================================================
   2. The marks block as a byte list (link_spec.v mk_n / mk_names / marks_wf)
   ========================================================================== *)

Lemma amk_names_length : forall gbs, length (mk_names gbs) = Z.to_nat (mk_n gbs).
Proof. intros gbs. unfold mk_names. rewrite length_map, length_seq. reflexivity. Qed.

Lemma amk_names_nth : forall gbs i, (i < Z.to_nat (mk_n gbs))%nat ->
  nth_error (mk_names gbs) i = Some (cstr (slice gbs (MK_NAME + MARK_LEN * Z.of_nat i) MARK_LEN)).
Proof.
  intros gbs i Hi. unfold mk_names. rewrite nth_error_map, nth_error_seq.
  replace (i <? Z.to_nat (mk_n gbs))%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). reflexivity.
Qed.

Lemma amk_n_range : forall gbs, marks_wf gbs -> 0 <= mk_n gbs <= MARKS_MAX.
Proof. intros gbs [H _]. exact H. Qed.

(* the list's length is the count word *)
Lemma amk_n_names : forall gbs, marks_wf gbs -> mk_n gbs = Z.of_nat (length (mk_names gbs)).
Proof. intros gbs [H _]. rewrite amk_names_length. lia. Qed.

Lemma amk_slot_len : forall gbs i, marks_wf gbs -> 0 <= i < mk_n gbs ->
  (length (cstr (slice gbs (MK_NAME + MARK_LEN * i) MARK_LEN)) < 16)%nat.
Proof.
  intros gbs i [_ T] Hi. specialize (T i Hi).
  pose proof (rp_cstr_length (slice gbs (MK_NAME + MARK_LEN * i) MARK_LEN)) as L.
  change (Z.to_nat MARK_LEN) with 16%nat in T. lia.
Qed.

(* ==========================================================================
   3. The A views
   ========================================================================== *)

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

Lemma ambyte_of_aview : forall (W : world segs) (m : word -> option byte) a v,
  0 <= v < 256 -> aview segs (w_H W) m a = Some v ->
  mbyte segs (mrestrict (w_H W) m) a = Some (Z_to_bv 8 v).
Proof.
  intros W m a v _ H. unfold aview in H.
  destruct (mbyte segs (mrestrict (w_H W) m) a) as [b|]; cbn [option_map] in H; [|discriminate].
  injection H as <-. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma aview_of_ambyte : forall (W : world segs) (m : word -> option byte) a b,
  mbyte segs (mrestrict (w_H W) m) a = Some b -> aview segs (w_H W) m a = Some (bv_unsigned b).
Proof. intros W m a b H. unfold aview. rewrite H. reflexivity. Qed.

(* the count word m->n, as the +0x48 load reads it *)
Lemma amk_n_val : forall (m : word -> option byte) p gbs,
  amarks_at segs m p gbs -> val_mem segs m p 4 (mk_n gbs).
Proof.
  intros m p gbs ((HAB & _) & HL). unfold MK_SIZE in HL.
  unfold mk_n, fld_u32, MK_N. change (rdn gbs 0 4) with (rdn gbs 0 (Z.of_nat 4)).
  replace p with (p + 0) by lia.
  apply val_mem_of_abytes; [exact HAB | lia | lia].
Qed.

(* the slot the loop's wrapper_strcmp reads is a C string inside its 16 bytes *)
Lemma amk_slot_cstr : forall (m : word -> option byte) p gbs i,
  amarks_at segs m p gbs -> marks_wf gbs -> 0 <= i < mk_n gbs ->
  acstr_at segs m (p + (MK_NAME + MARK_LEN * i)) (cstr (slice gbs (MK_NAME + MARK_LEN * i) MARK_LEN)).
Proof.
  intros m p gbs i ((HAB & _) & HL) [R T] Hi.
  specialize (T i Hi). unfold MARKS_MAX in R. unfold MK_SIZE in HL.
  unfold MK_NAME, MARK_LEN in *. change (Z.to_nat 16) with 16%nat in T.
  destruct HAB as (Hp & Hpl & Hnth).
  assert (LS : length (slice gbs (4 + 16 * i) 16) = 16%nat) by (rewrite lw_slice_length by lia; reflexivity).
  set (s := slice gbs (4 + 16 * i) 16) in *.
  destruct (rp_cstr_split s ltac:(lia)) as (rest & E & N).
  assert (LC : (length (cstr s ++ [zb 0]) <= 16)%nat).
  { rewrite <- LS. rewrite E at 2. rewrite app_assoc, !length_app. lia. }
  split; [|exact N].
  split; [lia|]. split; [lia|].
  intros k Hk.
  assert (Hk' : nth_error (cstr s ++ [zb 0]) k = nth_error s k).
  { rewrite E at 2. rewrite app_assoc. symmetry. apply nth_error_app1. exact Hk. }
  rewrite Hk'. unfold s. rewrite lw_slice_nth by lia.
  rewrite <- Hnth by lia. f_equal. lia.
Qed.

(* ==========================================================================
   4. The two paths that leave the block as it was (a hit, or 32 names kept)
   ========================================================================== *)

Lemma rem_marks_kept : forall (m m2 : word -> option byte) p gbs,
  amarks_at segs m p gbs ->
  (forall a, p <= a < p + MK_SIZE -> mbyte segs m2 a = mbyte segs m a) ->
  (forall a, p <= a < p + MK_SIZE -> writable_at segs m2 a) ->
  amarks_at segs m2 p gbs.
Proof.
  intros m m2 p gbs ((HAB & _) & HL) HEQ HWR2.
  destruct HAB as (Hp & Hpl & Hnth).
  split; [|exact HL]. split.
  - split; [exact Hp|]. split; [exact Hpl|].
    intros i Hi. rewrite HEQ by lia. exact (Hnth i Hi).
  - intros i Hi. apply HWR2. lia.
Qed.

Lemma rem_post_kept : forall (m m2 : word -> option byte) p gbs (nm : list byte),
  amarks_at segs m p gbs -> marks_wf gbs ->
  (existsb (fun y => bl_eqb y nm) (mk_names gbs) = true \/ mk_n gbs = MARKS_MAX) ->
  (forall a, p <= a < p + MK_SIZE -> mbyte segs m2 a = mbyte segs m a) ->
  (forall a, p <= a < p + MK_SIZE -> writable_at segs m2 a) ->
  exists gbs', amarks_at segs m2 p gbs' /\ marks_wf gbs'
    /\ mk_names gbs' = remember (mk_names gbs) nm
    /\ mk_n gbs' = Z.of_nat (length (remember (mk_names gbs) nm)).
Proof.
  intros m m2 p gbs nm HM HWF HC HEQ HWR2.
  assert (REM : remember (mk_names gbs) nm = mk_names gbs).
  { destruct HC as [Hh|Hf]; [exact (remember_hit _ _ Hh)|].
    apply remember_full. rewrite <- (amk_n_names gbs HWF). exact Hf. }
  exists gbs. split; [exact (rem_marks_kept m m2 p gbs HM HEQ HWR2)|].
  split; [exact HWF|]. rewrite REM. split; [reflexivity|]. exact (amk_n_names gbs HWF).
Qed.

(* ==========================================================================
   5. THE APPEND: m->n := n + 1, then slot n := the name and its NUL
   ========================================================================== *)

Lemma rem_marks_after_a : forall (m m2 : word -> option byte) p gbs (nm : list byte) n,
  amarks_at segs m p gbs -> marks_wf gbs -> mk_n gbs = n -> 0 <= n <= 31 -> ~ In (zb 0) nm ->
  (length nm <= 15)%nat -> existsb (fun y => bl_eqb y nm) (mk_names gbs) = false ->
  val_mem segs m2 p 4 (n + 1) ->
  (forall j, 0 <= j <= Z.of_nat (length nm) ->
     mbyte segs m2 (p + (MK_NAME + MARK_LEN * n) + j) = nth_error (nm ++ [zb 0]) (Z.to_nat j)) ->
  (forall a, p <= a < p + MK_SIZE -> ~ (p <= a < p + 4) ->
     ~ (p + (MK_NAME + MARK_LEN * n) <= a <= p + (MK_NAME + MARK_LEN * n) + Z.of_nat (length nm)) ->
     mbyte segs m2 a = mbyte segs m a) ->
  (forall a, p <= a < p + MK_SIZE -> writable_at segs m2 a) ->
  exists gbs', amarks_at segs m2 p gbs' /\ marks_wf gbs'
    /\ mk_names gbs' = remember (mk_names gbs) nm
    /\ mk_n gbs' = Z.of_nat (length (remember (mk_names gbs) nm)).
Proof.
  intros m m2 p gbs nm n HM HWF En Hn Nn Ln Ex HV HNM HOUT HWR2.
  (* NEVER `cbn` on a goal that holds `slice` / `rdn` of a 516-byte list. *)
  assert (PW32 : 2 ^ (8 * Z.of_nat 4) = 4294967296) by reflexivity.
  destruct HM as ((HAB & _) & HL).
  pose proof HAB as (Hp & Hpl & Hnth).
  unfold MK_SIZE in HL, HOUT, HWR2. unfold MK_NAME, MARK_LEN in HNM, HOUT.
  assert (HLN : length gbs = 516%nat) by lia.
  set (off := 4 + 16 * n) in *.
  assert (Eoff : off = 4 + 16 * n) by reflexivity.
  assert (Hoff : 4 <= off /\ off + 16 <= 516) by lia.
  (* every byte of the 516 is present in m2 *)
  assert (HSOME : forall i, (i < 516)%nat -> exists b, mbyte segs m2 (p + Z.of_nat i) = Some b).
  { intros i Hi.
    destruct (Nat.lt_ge_cases i 4) as [H4|H4].
    { exists (Z_to_bv 8 (le_byte (n + 1) 4 i)). exact (HV i H4). }
    destruct (Z_le_gt_dec off (Z.of_nat i)) as [Hlo|Hlo];
      [destruct (Z_le_gt_dec (Z.of_nat i) (off + Z.of_nat (length nm))) as [Hhi|Hhi]|].
    - replace (p + Z.of_nat i) with (p + off + (Z.of_nat i - off)) by lia.
      rewrite (HNM (Z.of_nat i - off) ltac:(lia)).
      destruct (nth_error (nm ++ [zb 0]) (Z.to_nat (Z.of_nat i - off))) as [b|] eqn:Eb; [exists b; reflexivity|].
      exfalso. apply nth_error_None in Eb. rewrite length_app in Eb. cbn [length] in Eb. lia.
    - rewrite (HOUT (p + Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(lia)), (Hnth i ltac:(lia)).
      destruct (nth_error gbs i) as [b|] eqn:Eb; [exists b; reflexivity|].
      exfalso. apply nth_error_None in Eb. lia.
    - rewrite (HOUT (p + Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(lia)), (Hnth i ltac:(lia)).
      destruct (nth_error gbs i) as [b|] eqn:Eb; [exists b; reflexivity|].
      exfalso. apply nth_error_None in Eb. lia. }
  set (bs' := abytes_of segs m2 p 516).
  assert (HL' : length bs' = 516%nat) by (unfold bs'; apply abytes_of_length).
  assert (HAB' : abytes segs m2 p bs').
  { unfold bs'. apply abytes_of_abytes; [lia | lia | exact HSOME]. }
  pose proof HAB' as (_ & _ & Hnth').
  (* the bytes the run did not write are the bytes they were *)
  assert (HN : forall i, (i < 516)%nat -> (4 <= i)%nat ->
    ~ (off <= Z.of_nat i <= off + Z.of_nat (length nm)) -> nth_error bs' i = nth_error gbs i).
  { intros i Hi H4 Hs. rewrite <- (Hnth' i ltac:(lia)), <- (Hnth i ltac:(lia)).
    apply HOUT; lia. }
  (* the count word: n + 1 *)
  assert (N' : mk_n bs' = n + 1).
  { unfold mk_n, fld_u32, MK_N. change 4 with (Z.of_nat 4).
    apply (rdn_of_vals bs' 0 4%nat (n + 1)); [lia | rewrite HL'; lia | rewrite PW32; lia |].
    intros kk Hkk. change (Z.to_nat 0 + kk)%nat with kk.
    rewrite <- (Hnth' kk ltac:(lia)). exact (HV kk Hkk). }
  (* the old slots *)
  assert (OLD : forall i, 0 <= i < n -> slice bs' (4 + 16 * i) 16 = slice gbs (4 + 16 * i) 16).
  { intros i Hi. apply lw_list_ext.
    - rewrite !lw_slice_length by lia. reflexivity.
    - intros k Hk. rewrite lw_slice_length in Hk by lia.
      rewrite !lw_slice_nth by lia. apply HN; lia. }
  (* the new slot: the name, its NUL, then what was there *)
  assert (NEW : exists rest, slice bs' off 16 = nm ++ [zb 0] ++ rest).
  { set (s' := slice bs' off 16).
    assert (LS : length s' = 16%nat) by (unfold s'; rewrite lw_slice_length by lia; reflexivity).
    exists (skipn (S (length nm)) s').
    rewrite <- (firstn_skipn (S (length nm)) s') at 1. rewrite app_assoc. f_equal.
    apply lw_list_ext.
    - rewrite length_firstn, length_app, LS. cbn [length]. lia.
    - intros k Hk. rewrite length_firstn, LS in Hk.
      rewrite lw_nth_error_firstn by lia. unfold s'. rewrite lw_slice_nth by lia.
      rewrite <- (Hnth' (Z.to_nat off + k)%nat ltac:(lia)).
      replace (p + Z.of_nat (Z.to_nat off + k)%nat) with (p + off + Z.of_nat k) by lia.
      rewrite (HNM (Z.of_nat k) ltac:(lia)). rewrite Nat2Z.id. reflexivity. }
  destruct NEW as (rest & NEW).
  assert (CNEW : cstr (slice bs' off 16) = nm) by (rewrite NEW; exact (cstr_app_nul nm rest Nn)).
  assert (ZNEW : nul_at (slice bs' off 16) = length nm) by (rewrite NEW; exact (nul_at_app_nul nm rest Nn)).
  assert (LN : length (mk_names gbs) = Z.to_nat n) by (rewrite amk_names_length, En; reflexivity).
  assert (REM : remember (mk_names gbs) nm = mk_names gbs ++ [nm]).
  { apply remember_miss; [exact Ex | rewrite LN; unfold MARKS_MAX; lia | exact Ln]. }
  assert (NAMES : mk_names bs' = mk_names gbs ++ [nm]).
  { unfold mk_names. rewrite N', En. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
    rewrite seq_S, map_app. cbn [map Nat.add]. f_equal.
    - apply map_ext_in. intros i Hi. apply in_seq in Hi. cbv beta. unfold MK_NAME, MARK_LEN.
      rewrite OLD by lia. reflexivity.
    - unfold MK_NAME, MARK_LEN. rewrite Z2Nat.id by lia. change (4 + 16 * n) with off. rewrite CNEW. reflexivity. }
  exists bs'.
  split.
  { split; [|rewrite HL'; reflexivity]. split; [exact HAB'|].
    intros i Hi. apply HWR2. rewrite HL' in Hi. lia. }
  rewrite REM. split; [|split; [exact NAMES|]].
  - split; [rewrite N'; unfold MARKS_MAX; lia|].
    intros i Hi. rewrite N' in Hi. unfold MK_NAME, MARK_LEN. change (Z.to_nat 16) with 16%nat.
    destruct (Z.eq_dec i n) as [->|Hne]; [change (4 + 16 * n) with off; rewrite ZNEW; lia|].
    rewrite OLD by lia. destruct HWF as [_ T]. rewrite En in T.
    specialize (T i ltac:(lia)). unfold MK_NAME, MARK_LEN in T. exact T.
  - rewrite N', length_app, LN. cbn [length]. lia.
Qed.
End r.

Print Assumptions rem_marks_after_a.
Print Assumptions rem_post_kept.
Print Assumptions amk_slot_cstr.
Print Assumptions ambyte_of_aview.
