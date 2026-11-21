(** * Spec.PngModel.StepReach — the premise-discharge layer for [step_ok]
    (2026-08-19, Q4 discharge lap; an earlier development run).

    Turns [InflateThy.step_ok_covered]'s named side conditions into
    theorems at reachable states:

    - the FIXED-table half of the live-table contract is proved outright
      ([vm_compute] over [lenfix]/[distfix] + the [tbl_of_list] default
      analysis) — [fixed_len_tbl_side] closes the fixed-block path;
    - [ReachSt] is the reachability invariant (unconditional core +
      mode-conditioned block), and [step_ok_reachable] is the dispatch:
      it discharges EVERY premise of [step_ok_covered] except the two
      in-call tail obligations of the TABLE chain, which are carried
      through as premises.  Their elimination is the knot lap (the
      TABLE-chain arms re-proved with THREADED callee premises, fed by
      the it_model output contracts); the dynamic-table instances of
      [LenTblSide] are the same lap's other half — see the lap report
      for the exact residual surface (sub-table coverage, the DISTS
      analogues of the LENS ptr/prov program, chain-fit assembly).

    Ownership: an earlier development run (with InflateThy.v). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ZBitsIn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtItTotal.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtLenProv.
(* (D') a5 665p (fork): TblPD's home is the header-light leaf cand6-prep/CfgBitsTblLeaf.v 29291912
   (an earlier development run's CfgBitsTbl body + CfgBits8Defs 's four table Definitions, minimal header; a5 665p: CfgBitsTbl
   Requires (Export) the leaf at r2).  The r2 module NAME is not fixed: RE-KEY this Require line at the bits8-v1 r2 landing. *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import CfgBitsTblLeaf.
(* W9: the leaf-positivity theory for [rc_leafpos] -- ItGTblLeafPos (LeafPosE/LeafPosT,
   it_model_leafpos for DISTS) and its generalisation ItGTblLeafPosX (LENS / CODES / any type, codes_wb, fixed tables). *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ItGTblLeafPos ItGTblLeafPosX.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require ItGSubCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require ItGTblSortWin.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** * The fixed-table half of the live-table contract (Q4 discharge lap)

    [inflate.c:245-290] [fixedtables] installs [lenfix]/[distfix] with
    [lenbits = 9] / [distbits = 5].  Every clause of [if_wf_tbl] +
    [LcSide] + [TblSide] is DECIDABLE over the two literal tables, so this
    half of the discharge is a [vm_compute] over the 512 + 32 entries plus
    one analysis of [tbl_of_list]'s out-of-range default ([mkCode 0 0 0]:
    its [op] is literal-shaped, so every conditional clause is exempt; the
    one clause it genuinely participates in — [dc_chains 0 = true] — jumps
    to index 0, whose entry is a distance base, and the pair fits). *)

Definition code_of3 (t : Z * Z * Z) : Code :=
  let '(op, b, v) := t in mkCode op b v.

Lemma tbl_of_list_eq : forall l i,
  tbl_of_list l i = code_of3 (nth (Z.to_nat i) l (0, 0, 0)).
Proof. reflexivity. Qed.

(** Scoped transport: a boolean check that holds on every LIST entry holds
    at every in-range index of the table function. *)
Lemma tbl_of_list_below :
  forall (Pb : Code -> bool) l,
    forallb (fun t => Pb (code_of3 t)) l = true ->
    forall i, 0 <= i < Z.of_nat (length l) -> Pb (tbl_of_list l i) = true.
Proof.
  intros Pb l Hall i Hi. rewrite tbl_of_list_eq.
  apply (proj1 (forallb_forall _ _) Hall).
  apply nth_In. lia.
Qed.

(** Unscoped transport, when the default passes the check too. *)
Lemma tbl_of_list_all :
  forall (Pb : Code -> bool) l,
    forallb (fun t => Pb (code_of3 t)) l = true ->
    Pb (code_of3 (0, 0, 0)) = true ->
    forall i, Pb (tbl_of_list l i) = true.
Proof.
  intros Pb l Hall Hd i. rewrite tbl_of_list_eq.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)) as [Hlt|Hge].
  - apply (proj1 (forallb_forall _ _) Hall). apply nth_In. exact Hlt.
  - rewrite nth_overflow by exact Hge. exact Hd.
Qed.

(** ** The boolean checkers, with their soundness bridges *)

Definition chk_wid115 (e : Code) : bool :=
  (1 <=? c_bits e) && (c_bits e <=? 15).
Lemma chk_wid115_sound : forall e, chk_wid115 e = true -> 1 <= c_bits e <= 15.
Proof.
  intros e H. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Definition chk_wid015 (e : Code) : bool :=
  (0 <=? c_bits e) && (c_bits e <=? 15).
Lemma chk_wid015_sound : forall e, chk_wid015 e = true -> 0 <= c_bits e <= 15.
Proof.
  intros e H. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Definition chk_lext5 (e : Code) : bool :=
  if Z.eqb (Z.land (c_op e) 16) 0 then true else Z.land (c_op e) 15 <=? 5.
Lemma chk_lext5_sound : forall e, chk_lext5 e = true ->
  Z.land (c_op e) 16 <> 0 -> Z.land (c_op e) 15 <= 5.
Proof.
  intros e H Hne. unfold chk_lext5 in H.
  destruct (Z.eqb (Z.land (c_op e) 16) 0) eqn:E.
  - apply Z.eqb_eq in E. contradiction.
  - apply Z.leb_le in H. exact H.
Qed.

Definition chk_dext13 (e : Code) : bool :=
  if Z.eqb (Z.land (c_op e) 16) 0 then true else Z.land (c_op e) 15 <=? 13.
Lemma chk_dext13_sound : forall e, chk_dext13 e = true ->
  Z.land (c_op e) 16 <> 0 -> Z.land (c_op e) 15 <= 13.
Proof.
  intros e H Hne. unfold chk_dext13 in H.
  destruct (Z.eqb (Z.land (c_op e) 16) 0) eqn:E.
  - apply Z.eqb_eq in E. contradiction.
  - apply Z.leb_le in H. exact H.
Qed.

Definition chk_tblside (e : Code) : bool :=
  (0 <=? c_bits e) && (c_bits e <=? 15)
  && (0 <=? c_val e) && (c_val e <? 65536).
Lemma chk_tblside_sound : forall e, chk_tblside e = true ->
  (0 <= c_bits e <= 15) /\ (0 <= c_val e < 65536).
Proof.
  intros e H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  apply Z.ltb_lt in H4. lia.
Qed.

Definition chk_lcside (e : Code) : bool :=
  (0 <=? c_bits e)
  && (if Z.eqb (Z.land (c_op e) 32) 0 then true else 1 <=? c_bits e)
  && (if Z.eqb (c_op e) 0 then true
      else if negb (Z.eqb (Z.land (c_op e) 32) 0) then true
      else if negb (Z.eqb (Z.land (c_op e) 64) 0) then true
      else 1 <=? c_val e).
Lemma chk_lcside_sound : forall e, chk_lcside e = true ->
  (0 <= c_bits e)
  /\ (Z.land (c_op e) 32 <> 0 -> 1 <= c_bits e)
  /\ (c_op e <> 0 -> Z.land (c_op e) 32 = 0 -> Z.land (c_op e) 64 = 0 ->
        1 <= c_val e).
Proof.
  intros e H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1.
  split; [lia|]. split.
  - intros Hne.
    destruct (Z.eqb (Z.land (c_op e) 32) 0) eqn:E;
      [apply Z.eqb_eq in E; contradiction|].
    apply Z.leb_le in H2. lia.
  - intros Hop H32 H64.
    destruct (Z.eqb (c_op e) 0) eqn:E0;
      [apply Z.eqb_eq in E0; contradiction|].
    rewrite H32, H64 in H3. cbn in H3.
    apply Z.leb_le in H3. lia.
Qed.

Definition chk_nochain_l (e : Code) : bool := negb (lc_chains (c_op e)).
Definition chk_nochain_d (e : Code) : bool := negb (dc_chains (c_op e)).

(** ** The list-level facts, one [vm_compute] each *)

Lemma lenfix_len : Z.of_nat (length lenfix_list) = 512.
Proof. vm_compute. reflexivity. Qed.
Lemma distfix_len : Z.of_nat (length distfix_list) = 32.
Proof. vm_compute. reflexivity. Qed.

Lemma lenfix_chk_wid : forallb (fun t => chk_wid115 (code_of3 t)) lenfix_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lenfix_chk_lext : forallb (fun t => chk_lext5 (code_of3 t)) lenfix_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lenfix_chk_lenok : forallb (fun t => lc_len_okb (code_of3 t)) lenfix_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lenfix_chk_nochain : forallb (fun t => chk_nochain_l (code_of3 t)) lenfix_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lenfix_chk_lcside : forallb (fun t => chk_lcside (code_of3 t)) lenfix_list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma distfix_chk_wid : forallb (fun t => chk_wid015 (code_of3 t)) distfix_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma distfix_chk_dext : forallb (fun t => chk_dext13 (code_of3 t)) distfix_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma distfix_chk_nochain : forallb (fun t => chk_nochain_d (code_of3 t)) distfix_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma distfix_chk_tblside : forallb (fun t => chk_tblside (code_of3 t)) distfix_list = true.
Proof. vm_compute. reflexivity. Qed.

(** the default passes the unscoped checks *)
Lemma default_wid015 : chk_wid015 (code_of3 (0,0,0)) = true.
Proof. reflexivity. Qed.
Lemma default_dext : chk_dext13 (code_of3 (0,0,0)) = true.
Proof. reflexivity. Qed.
Lemma default_tblside : chk_tblside (code_of3 (0,0,0)) = true.
Proof. reflexivity. Qed.
Lemma default_lcside : chk_lcside (code_of3 (0,0,0)) = true.
Proof. reflexivity. Qed.
Lemma default_nochain_l : chk_nochain_l (code_of3 (0,0,0)) = true.
Proof. reflexivity. Qed.

(** ** Table-level facts *)

Lemma lenfix_wid_below : forall i, 0 <= i < 512 -> 1 <= c_bits (lenfix i) <= 15.
Proof.
  intros i Hi. apply chk_wid115_sound.
  apply (tbl_of_list_below _ _ lenfix_chk_wid). rewrite lenfix_len. lia.
Qed.

Lemma lenfix_lext_below : forall i, 0 <= i < 512 ->
  Z.land (c_op (lenfix i)) 16 <> 0 -> Z.land (c_op (lenfix i)) 15 <= 5.
Proof.
  intros i Hi. apply chk_lext5_sound.
  apply (tbl_of_list_below _ _ lenfix_chk_lext). rewrite lenfix_len. lia.
Qed.

Lemma lenfix_lenok_below : forall i, 0 <= i < 512 -> lc_len_ok (lenfix i).
Proof.
  intros i Hi. apply lc_len_okb_sound.
  apply (tbl_of_list_below _ _ lenfix_chk_lenok). rewrite lenfix_len. lia.
Qed.

Lemma lenfix_nochain : forall i, lc_chains (c_op (lenfix i)) = false.
Proof.
  intros i.
  pose proof (tbl_of_list_all _ _ lenfix_chk_nochain default_nochain_l i) as H.
  unfold chk_nochain_l in H. apply negb_true_iff in H. exact H.
Qed.

Lemma lenfix_lcside_all : forall i,
  (0 <= c_bits (lenfix i))
  /\ (Z.land (c_op (lenfix i)) 32 <> 0 -> 1 <= c_bits (lenfix i))
  /\ (c_op (lenfix i) <> 0 -> Z.land (c_op (lenfix i)) 32 = 0 ->
        Z.land (c_op (lenfix i)) 64 = 0 -> 1 <= c_val (lenfix i)).
Proof.
  intros i. apply chk_lcside_sound.
  apply (tbl_of_list_all _ _ lenfix_chk_lcside default_lcside).
Qed.

Lemma distfix_wid_all : forall i, 0 <= c_bits (distfix i) <= 15.
Proof.
  intros i. apply chk_wid015_sound.
  apply (tbl_of_list_all _ _ distfix_chk_wid default_wid015).
Qed.

Lemma distfix_dext_all : forall i,
  Z.land (c_op (distfix i)) 16 <> 0 -> Z.land (c_op (distfix i)) 15 <= 13.
Proof.
  intros i. apply chk_dext13_sound.
  apply (tbl_of_list_all _ _ distfix_chk_dext default_dext).
Qed.

Lemma distfix_tblside : TblSide distfix.
Proof.
  intros i. apply chk_tblside_sound.
  apply (tbl_of_list_all _ _ distfix_chk_tblside default_tblside).
Qed.

(** [distfix]'s in-range entries never chain; the OUT-OF-RANGE default
    ([op = 0]) IS [dc_chains]-shaped, and its jump target is index 0
    ([c_val 0 + if_low 0 s = 0]), whose entry is a distance base — so the
    two-level and fit facts hold THROUGH the default rather than despite
    it. *)
Lemma if_low_0 : forall s, if_low 0 s = 0.
Proof.
  intros s. unfold if_low. cbn. apply Z.land_0_r.
Qed.

Lemma distfix_inrange_nochain : forall i, 0 <= i < 32 ->
  dc_chains (c_op (distfix i)) = false.
Proof.
  intros i Hi.
  pose proof (tbl_of_list_below _ _ distfix_chk_nochain i
                ltac:(rewrite distfix_len; lia)) as H.
  unfold chk_nochain_d in H. apply negb_true_iff in H. exact H.
Qed.

(** For an ARBITRARY index (negatives clamp to entry 0 via [Z.to_nat]),
    every [distfix] read is either a checked in-list entry (never
    [dc_chains]-shaped) or the out-of-range default. *)
Lemma distfix_nochain_or_default : forall i,
  dc_chains (c_op (distfix i)) = false \/ distfix i = mkCode 0 0 0.
Proof.
  intros i. unfold distfix. rewrite tbl_of_list_eq.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length distfix_list)) as [Hlt|Hge].
  - left.
    pose proof (proj1 (forallb_forall _ _) distfix_chk_nochain
                  (nth (Z.to_nat i) distfix_list (0,0,0))
                  (nth_In _ _ Hlt)) as H.
    unfold chk_nochain_d in H. apply negb_true_iff in H.
    exact H.
  - right. rewrite nth_overflow by exact Hge. reflexivity.
Qed.

Lemma lenfix_nochain_all : forall i,
  lc_chains (c_op (lenfix i)) = false.
Proof. exact lenfix_nochain. Qed.

Lemma distfix_chain_fit : chain_fit dc_chains distfix 31.
Proof.
  intros v x s _ Hch.
  destruct (distfix_nochain_or_default v) as [Hnc|Hd].
  - rewrite Hnc in Hch. discriminate.
  - rewrite Hd. cbn [c_bits c_op c_val].
    rewrite if_low_0.
    assert (H0 : c_bits (distfix (0 + 0)) = 5) by (vm_compute; reflexivity).
    rewrite H0. lia.
Qed.

Lemma distfix_two_level_gen : forall v s,
  dc_chains (c_op (distfix v)) = true ->
  dc_chains (c_op (distfix (c_val (distfix v)
                            + if_low (c_op (distfix v)) s))) = false.
Proof.
  intros v s Hch.
  destruct (distfix_nochain_or_default v) as [Hnc|Hd].
  - rewrite Hnc in Hch. discriminate.
  - rewrite Hd. cbn [c_op c_val].
    rewrite if_low_0.
    vm_compute (dc_chains (c_op (distfix (0 + 0)))). reflexivity.
Qed.

Lemma lenfix_chain_fit : chain_fit lc_chains lenfix 511.
Proof.
  intros v x s _ Hch. rewrite lenfix_nochain in Hch. discriminate.
Qed.

(** ** The state-level bundle at the fixed configuration

    [fixedtables] ([inflate.c:245-290], transcribed at [Inflate.v]) writes
    exactly this configuration; TYPEDO's fixed arm is its only producer. *)
Definition fixed_cfg (st : IState) : Prop :=
  t_lencode (s_tab st) = TRlenfix
  /\ t_lenbits (s_tab st) = 9
  /\ t_distcode (s_tab st) = TRdistfix
  /\ t_distbits (s_tab st) = 5.

Lemma fixed_lcode_eq : forall q, t_lencode (s_tab (q_st q)) = TRlenfix ->
  a_lcode (len_args q) = lenfix.
Proof.
  intros q H. cbn [len_args a_lcode]. rewrite H. reflexivity.
Qed.

Lemma fixed_dcode_eq : forall q, t_distcode (s_tab (q_st q)) = TRdistfix ->
  a_dcode (len_args q) = distfix.
Proof.
  intros q H. cbn [len_args a_dcode]. rewrite H. reflexivity.
Qed.

Lemma fixed_lcode_index_range :
  forall q, fixed_cfg (q_st q) -> lcode_index_range 512 (if_ctx (len_args q)).
Proof.
  intros q (Hlc & Hlb & Hdc & Hdb). split.
  - intros s. cbn [if_ctx f_lmask len_args a_lenbits]. rewrite Hlb.
    pose proof (land_ones_range (f_hold s) 9 ltac:(lia)) as H.
    change (2 ^ 9) with 512 in H. exact H.
  - intros v s Hv Hch. exfalso.
    revert Hch. cbn [if_ctx f_lcode]. rewrite (fixed_lcode_eq q Hlc).
    rewrite lenfix_nochain. discriminate.
Qed.

Lemma fixed_lcode_upto :
  forall q, fixed_cfg (q_st q) ->
    lcode_len_bounded_upto (if_ctx (len_args q)) 512.
Proof.
  intros q (Hlc & Hlb & Hdc & Hdb) v Hv.
  cbn [if_ctx f_lcode]. rewrite (fixed_lcode_eq q Hlc).
  apply lenfix_lenok_below. exact Hv.
Qed.

Theorem fixed_if_wf_tbl :
  forall q, fixed_cfg (q_st q) -> if_wf_tbl (len_args q).
Proof.
  intros q Hcfg. pose proof Hcfg as (Hlc & Hlb & Hdc & Hdb).
  pose proof (fixed_lcode_eq q Hlc) as EL.
  pose proof (fixed_dcode_eq q Hdc) as ED.
  split.
  { exists 512.
    split; [exact (fixed_lcode_upto q Hcfg)|].
    split; [exact (fixed_lcode_index_range q Hcfg)|].
    split.
    - rewrite EL. exact lenfix_wid_below.
    - rewrite EL. exact lenfix_lext_below. }
  split; [rewrite ED; exact distfix_wid_all|].
  split.
  { rewrite EL.
    replace (f_lmask (if_ctx (len_args q))) with 511;
      [exact lenfix_chain_fit|].
    cbn [if_ctx f_lmask len_args a_lenbits]. rewrite Hlb. reflexivity. }
  split.
  { rewrite ED.
    replace (f_dmask (if_ctx (len_args q))) with 31;
      [exact distfix_chain_fit|].
    cbn [if_ctx f_dmask len_args a_distbits]. rewrite Hdb. reflexivity. }
  rewrite ED. exact distfix_dext_all.
Qed.

Theorem fixed_lcside :
  forall q, fixed_cfg (q_st q) ->
    LcSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))).
Proof.
  intros q (Hlc & _ & _ & _).
  rewrite Hlc.
  assert (E : tbl_of (q_st q) TRlenfix = lenfix) by reflexivity.
  rewrite E.
  split; [intros i; exact (proj1 (lenfix_lcside_all i))|].
  split; [intros i; exact (proj1 (proj2 (lenfix_lcside_all i)))|].
  intros i. exact (proj2 (proj2 (lenfix_lcside_all i))).
Qed.

Theorem fixed_tblside_d :
  forall q, fixed_cfg (q_st q) ->
    TblSide (tbl_of (q_st q) (t_distcode (s_tab (q_st q)))).
Proof.
  intros q (_ & _ & Hdc & _). rewrite Hdc.
  assert (E : tbl_of (q_st q) TRdistfix = distfix) by reflexivity.
  rewrite E. exact distfix_tblside.
Qed.

Theorem fixed_two_levels :
  forall q, fixed_cfg (q_st q) ->
    lcode_two_level (if_ctx (len_args q))
    /\ dcode_two_level (if_ctx (len_args q)).
Proof.
  intros q (Hlc & Hlb & Hdc & Hdb).
  pose proof (fixed_lcode_eq q Hlc) as EL.
  pose proof (fixed_dcode_eq q Hdc) as ED.
  split.
  - intros v x s _ Hch. exfalso. revert Hch.
    cbn [if_ctx f_lcode]. rewrite EL. rewrite lenfix_nochain. discriminate.
  - intros v x s _ Hch. revert Hch.
    cbn [if_ctx f_dcode]. rewrite ED.
    apply distfix_two_level_gen.
Qed.

Theorem fixed_lcode_len_bounded :
  forall q, fixed_cfg (q_st q) -> lcode_len_bounded (if_ctx (len_args q)).
Proof.
  intros q Hcfg. exists 512.
  split; [exact (fixed_lcode_upto q Hcfg)|].
  exact (fixed_lcode_index_range q Hcfg).
Qed.

(** ** The masked-root op-shape discrimination clause (rootshape wave,
    q7-decode 2026-08-20).  Text identical to [GtDecHsel.lcode_root_opshape]
    (the consumer's landed spelling; convertible constants). *)

Definition lcode_root_opshape (t : ztbl) (rb : Z) : Prop :=
  forall x,
    c_op (t (Z.land x (Z.shiftl 1 rb - 1))) <> 0 ->
    Z.land (c_op (t (Z.land x (Z.shiftl 1 rb - 1)))) 240 <> 0 ->
    Z.land (c_op (t (Z.land x (Z.shiftl 1 rb - 1)))) 32 = 0 ->
    Z.land (c_op (t (Z.land x (Z.shiftl 1 rb - 1)))) 64 = 0 ->
    Z.land (c_op (t (Z.land x (Z.shiftl 1 rb - 1)))) 16 <> 0.

(** Reflective fixed-table arm (copy of the GtDecHsel family; provenance:
    q7-decode rootshape wave). *)
Definition chk_root_opshape (e : Code) : bool :=
  (c_op e =? 0) || (Z.land (c_op e) 240 =? 0)
  || negb (Z.land (c_op e) 32 =? 0) || negb (Z.land (c_op e) 64 =? 0)
  || negb (Z.land (c_op e) 16 =? 0).

Lemma chk_root_opshape_sound : forall e, chk_root_opshape e = true ->
  c_op e <> 0 -> Z.land (c_op e) 240 <> 0 -> Z.land (c_op e) 32 = 0 ->
  Z.land (c_op e) 64 = 0 -> Z.land (c_op e) 16 <> 0.
Proof.
  intros e H Hop H240 H32 H64. unfold chk_root_opshape in H.
  repeat (apply orb_prop in H; destruct H as [H|H]).
  - apply Z.eqb_eq in H. contradiction.
  - apply Z.eqb_eq in H. contradiction.
  - rewrite negb_true_iff in H. apply Z.eqb_neq in H. congruence.
  - rewrite negb_true_iff in H. apply Z.eqb_neq in H. congruence.
  - rewrite negb_true_iff in H. apply Z.eqb_neq in H. exact H.
Qed.

Lemma lenfix_root_chk :
  forallb (fun t => chk_root_opshape (code_of3 t)) lenfix_list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma default_root_opshape : chk_root_opshape (code_of3 (0, 0, 0)) = true.
Proof. reflexivity. Qed.

Lemma lenfix_root_opshape : lcode_root_opshape lenfix 9.
Proof.
  intros x. apply chk_root_opshape_sound.
  unfold lenfix.
  apply (tbl_of_list_all _ _ lenfix_root_chk default_root_opshape).
Qed.

Theorem fixed_root_opshape :
  forall q, fixed_cfg (q_st q) ->
    lcode_root_opshape (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                       (t_lenbits (s_tab (q_st q))).
Proof.
  intros q (Hlc & Hlb & _ & _).
  rewrite Hlc, Hlb.
  assert (E : tbl_of (q_st q) TRlenfix = lenfix) by reflexivity.
  rewrite E. exact lenfix_root_opshape.
Qed.

(** * The reachability layer: [ReachSt] and the dispatch (Q4 discharge lap)

    [ReachSt] is the state invariant the discharge carries; its clauses
    are exactly the named side conditions of [step_ok_covered], grouped as
    an unconditional core plus the mode-conditioned block.  The live-table
    bundle [LenTblSide] appears mode-conditioned on the five LEN-side
    modes: unconditionally it would be UNINHABITABLE at header-time states
    (the initial codes array is all-zero, exactly the defect the
    relativisation lap repaired), and no mode outside the five reads the
    tables. *)

Definition LenTblSide (q : InfSt) : Prop :=
  if_wf_tbl (len_args q)
  /\ LcSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
  /\ TblSide (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
  /\ lcode_two_level (if_ctx (len_args q))
  /\ dcode_two_level (if_ctx (len_args q))
  /\ lcode_len_bounded (if_ctx (len_args q))
  /\ 1 <= t_lenbits (s_tab (q_st q)) <= 15
  /\ 1 <= t_distbits (s_tab (q_st q)) <= 15
  /\ lcode_root_opshape (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
       (t_lenbits (s_tab (q_st q))).

(** The fixed configuration inhabits the whole bundle — closing the
    fixed-block path of the discharge outright. *)
Theorem fixed_len_tbl_side :
  forall q, fixed_cfg (q_st q) -> LenTblSide q.
Proof.
  intros q Hcfg. pose proof Hcfg as (Hlc & Hlb & Hdc & Hdb).
  split; [exact (fixed_if_wf_tbl q Hcfg)|].
  split; [exact (fixed_lcside q Hcfg)|].
  split; [exact (fixed_tblside_d q Hcfg)|].
  split; [exact (proj1 (fixed_two_levels q Hcfg))|].
  split; [exact (proj2 (fixed_two_levels q Hcfg))|].
  split; [exact (fixed_lcode_len_bounded q Hcfg)|].
  split; [rewrite Hlb; lia|].
  split; [rewrite Hdb; lia|].
  exact (fixed_root_opshape q Hcfg).
Qed.

(** The unconditional core. *)
Record ReachCore (q : InfSt) : Prop := mkReachCore {
  rc_pos    : q_pos q;
  rc_bits39 : br_bits (q_br q) <= 39;
  rc_bytes  : forall j, 0 <= br_in (q_br q) j < 256;
  rc_hold   : 0 <= br_hold (q_br q);
  rc_win    : forall j, 0 <= w_win (s_win (q_st q)) j < 256;
  rc_wnext  : 0 <= w_wnext (s_win (q_st q)) <= w_wsize (s_win (q_st q));
  rc_whave  : 0 <= w_whave (s_win (q_st q)) <= w_wsize (s_win (q_st q));
  rc_sane   : t_sane (s_tab (q_st q)) = 1;
  rc_len0   : 0 <= u_length (s_cur (q_st q));
  (* pres repair 2026-08-19 (pres lane): the plain [br_have] cap is NOT
     step-closed -- [if_finish] returns whole accumulator bytes to
     [avail_in] (the R9 +5 in-overshoot), so only the input-BIT budget
     survives a fast-path trip; the plain cap is recovered at each
     consuming site from [q_pos]'s [0 <= br_bits].  Bound = 8x the u32
     give-back ceiling 2^32 - 6 (CAP relaxation, pres lane — the 2^24 it
     first carried was headroom). *)
  rc_inbud  : 8 * br_have (q_br q) + br_bits (q_br q) <= 34359738320;
  rc_leftu32 : o_left (q_ob q) <= 4294967295;
  rc_lens   : lens_ok (b_lens (s_bld (q_st q)));
  rc_bhave  : 0 <= b_have (s_bld (q_st q));
  rc_bnlen  : 0 <= b_nlen (s_bld (q_st q));
  rc_bndist : 0 <= b_ndist (s_bld (q_st q));
  (* chain repair 2026-08-19: the pointwise ambient invariant of the codes
     array — what the build-record contracts assume of unwritten slots.
     Discharge: an earlier development run's per-write preservation lemmas. *)
  rc_amb    : amb_ok (t_codes (s_tab (q_st q)));
  (* re-entry lap 2026-08-20 (pres lane, q7 G2 audit): [uw] copies OUTPUT
     bytes into the window at [inf_leave], so [rc_win] transfers across a
     leave only if the output surface is itself byte-bounded.  Table-wide
     over the zarr: within-call preservation is frame + the writer walks;
     the driver supplies fresh-buffer bytes at init and each re-entry. *)
  rc_outb   : forall j, 0 <= o_buf (q_ob q) j < 256;
  (* re-entry lap 2026-08-20 (pres lane): [uw]'s contiguous branch needs
     [whave + copy <= wsize] to re-derive [rc_whave]; the saturation
     disjunction (window full, or fill-aligned) is the invariant zlib
     maintains — established at reset (0 = 0), frame within a call
     ([set_whave]/[set_wnext] appear only in [uw] and reset). *)
  rc_wcoup  : w_whave (s_win (q_st q)) = w_wsize (s_win (q_st q))
              \/ w_whave (s_win (q_st q)) = w_wnext (s_win (q_st q));
  (* re-entry lap G2 (pres lane, 2026-08-20): [inf_leave]'s writeback
     copies the WRITTEN region [q_out - o_left] into the window ([uw]),
     and its [u32 (copy - dist)] is exact only under a u32 bound on the
     written count.  [q_out] is written only at CHECK's snapshot restart
     ([qset_out _ (o_left _)]) and at LOAD/init, so both clauses are
     frame almost everywhere. *)
  rc_out0   : o_left (q_ob q) <= q_out q;
  rc_outcap : q_out q <= 4294967295;
  (* A1.2 (2026-09-02, an earlier development run; shape (B) of q7's RULING-RC-NEXT-BITS-SHAPE-B,
     a5 APPEND 640 = the spelling OF RECORD, byte-identical to this row): buffered bits are bounded by
     8 x the bytes consumed THIS call ([q_in q - br_have (q_br q)] is
     [inf_leave_tail]'s own [consumed], Inflate.v:1807) plus the carried
     ceiling 39 ([rc_bits39] at the previous leave).  Preserved by PULLBYTE
     (+8 bits, -1 have), DROPBITS/INITBITS (bits down) and the fast path's
     give-back (both sides move by 8*(bits>>3)); at every entry [consumed = 0]
     so the row is [s_bits st0 <= 39] -- 0 at reset, <= 39 at re-entry by
     [leave_boundary].  LAST field: the 16-name prefix destructs in GtDecHsel /
     GtDecCost stay valid. *)
  rc_next_bits : br_bits (q_br q) <= 8 * (q_in q - br_have (q_br q)) + 39;
  (* HOLDCLEAN (2026-09-03, an earlier development run): q7 RULING P1-F4-HOLD
     (ii) as AMENDED by ADDENDUM 1 SR -- the HOME of the
     unconditional hold row is ReachCore (an earlier development run F-P3R-4 ; l1's
     adversary read ), appended at the tail (append-anchor law; a5
     rules position/arity).  Spelled as P4's HOLDCLEAN body VERBATIM
     (ResumeDefs r13 :320); ZBitsIn.br_wf's row 2 (ZBitsIn.v:120) spells the
     same fact as [< Z.shiftl 1 (br_bits b)] -- the ONE bridge is
     [holdclean_shiftl] below (Z.shiftl_1_l).  The accumulator holds exactly
     [br_bits] valid bits: INITBITS re-establishes it (0 < 2^0), PULLBYTE
     preserves it for a byte < 256, DROPBITS(n) preserves it under the
     [n <= bits] every drop site gets from [inf_nb_ok] / the fetch guards /
     BYTEBITS's [n = bits & 7], and the fast path re-establishes it by the
     exit mask (InflateFast.if_finish :495 = inffast.c:293).  Entry copies
     the leave's hold/bits ([StepPres.leave_boundary_hc]); reset gives
     hold = 0, bits = 0.  Supply = [StepPres.hc_close] at every
     [reach_core_build] site.  LAST field: the prefix destructs in
     core_of_reach / GtDecHsel / GtDecCost stay valid. *)
  rc_holdclean : br_hold (q_br q) < 2 ^ br_bits (q_br q);
  (* W9 / rc_leafpos (2026-09-03, an earlier development run; MEASURE-dcside.md ; q7's rm_off1
     supplier of record, replacing the withdrawn bit-32 DcSide): every LEAF of the codes array
     (op & 240 <> 0) that is not an invalid marker (op & 64 = 0) has a positive value -- the
     fact the DIST arm's [set_offset] needs (1 <= new offset).  Spelled over the WHOLE array
     ([ItGTblLeafPos.LeafPosT], the tree's own predicate) because [inf_decode_ok_facts] yields
     an unbounded index.  Established: init [tnone] ([leafpos_tnone]); the three [set_codes]
     writers (CODELENS LENS/DISTS, LENLENS CODES) by [it_model_leafpos_wf] + [leafpos_codes_wb]
     over the predecessor's row; frame everywhere else.  Supply = [StepPres.lp_close] (reached
     through [hc_close]) at every [reach_core_build] site.  Position PROVISIONAL: appended
     after rc_holdclean (append-anchor law; a5 rules position/arity). *)
  rc_leafpos : LeafPosT (t_codes (s_tab (q_st q)));
  (* W9 / rc_walloc0 (2026-09-03, q7's ask for w-tie-seat3's LEN fast-noalloc leg; MEASURE-walloc0.md
     ): a window that was never allocated has size 0 -- true at every ReachSt constructor
     (gzctl_state0 :2472; inflateReset zeroes wsize :1954), FRAME at every inf_step arm (only
     [set_wbits] touches [s_win] in a call), vacuous after [uw] (alloc := true, [uw_alloc_true]).
     Read at M_LEN via ReachSt for [len_args]'s [a_wsize := w_wsize] under the IFPRE floor guard.
     Position PROVISIONAL: LAST (a5 rules). *)
  rc_walloc0 : w_alloc (s_win (q_st q)) = false -> w_wsize (s_win (q_st q)) = 0
}.
(* A1.2 NOTE: dec-u's asked ReachCore row
   [rc_next_bits : br_bits (q_br q) <= 8 * br_next (q_br q)] is NOT cut here.
   MEASURED FALSE at the tree's own re-entry states: [StepPres.reach_reenter_ask1]
   re-enters with [g_next_in := 0] on a fresh buffer while [s_bits] carries up to
   39 leave bits, so [bits <= 8 * next] fails whenever carried bits > 0.
   Within one call it IS preserved (pull +8/+1, drop, INITBITS, if_finish
   give-back); the honest form needs a driver entry premise -- see the bed's
   MEASURE.md.  Statement-tier item for TL / a5 / dec-u / q7.
   UPDATE (q7 RULING-RC-NEXT-BITS-SHAPE-B ): the call-relative shape (B)
   IS cut as the LAST [ReachCore] field [rc_next_bits] above ((a5 APPEND 640 spelled it; identity line APPEND 645 carried to the local-ubk pair)). *)

(** The mode-conditioned block (each clause = a [step_ok_covered]
    premise's source; the LEN-side table bundle covers the five modes
    that read the live tables). *)
(** (D'') a5 WORDS (STOP #7, fork): what the LEN/DIST decode sites need beyond [TblPD] --
    every level-2 pointer has a POSITIVE width ([SubGuardGen] for [inf_decode_le14]) and root + sub widths total <= 15 (the
    level-2 FetchLeave bound); the dist table has no [op = 0] root entry.  WIDTH SOURCE OF RECORD (ruled): ItGSubCover.SubEntry
    ([1 <= c_bits e <= 15 - root]) + RootPtr ([c_bits e = root], [1 <= c_op e]) via [it_covers_all] at the CODELENS install
    ([tblwid_installed] below), vm_compute on lenfix / distfix at TYPEDO ([fix_tblwid]). *)
Definition TblWid (t : ztbl) (rb : Z) : Prop :=
  forall i, 0 <= i < 2 ^ rb -> Z.land (c_op (t i)) 240 = 0 -> c_op (t i) <> 0 ->
    0 < c_op (t i) /\ (forall j, 0 <= j < 2 ^ c_op (t i) -> c_bits (t i) + c_bits (t (c_val (t i) + j)) <= 15).
Definition TblWidSide (q : InfSt) : Prop :=
  TblWid (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) (t_lenbits (s_tab (q_st q)))
  /\ TblWid (tbl_of (q_st q) (t_distcode (s_tab (q_st q)))) (t_distbits (s_tab (q_st q)))
  /\ (forall i, 0 <= i < 2 ^ t_distbits (s_tab (q_st q)) ->
        c_op (tbl_of (q_st q) (t_distcode (s_tab (q_st q))) i) <> 0).

(** cand13 (TL rm_off1 / rc_leafpos REPLACE; text VERBATIM from
    tiematch/PLAN-rm_off1-ADDENDUM-1.md §6, q7's ruling pending): every level-2 entry reachable from a pointer-shaped root entry
    of the DIST table is LEAF-shaped ([op & 0xf0 <> 0]).  Source of truth = [ItGSubCover.it_covers_all]: every written sub entry is
    [SubEntry ty root e] whose [LeafShape] conj 1-2 give, for CT_DISTS, [c_op e <> 0 /\ (c_op e = 0 \/ land 16 <> 0 \/ land 64 <> 0)];
    established at the CODELENS install ([dsub_installed] below) and by evaluation on distfix at TYPEDO ([fix_dsub]); framed
    everywhere else ([StepPres.dist_sub_frame]).  Consumed by [inf_decode_dist_leaf240] (below): a successful dist decode returns a
    LEAF, hence with [rc_leafpos] the non-BAD branch has [1 <= c_val h] — the DIST-side supply of [rm_off1]. *)
Definition DistSubLeaf (t : ztbl) (rb : Z) : Prop :=
  forall i, 0 <= i < 2 ^ rb -> Z.land (c_op (t i)) 240 = 0 -> 0 < c_op (t i) ->
    forall j, 0 <= j < 2 ^ (c_op (t i)) -> Z.land (c_op (t (c_val (t i) + j))) 240 <> 0.
Definition DistSubSide (q : InfSt) : Prop :=
  DistSubLeaf (tbl_of (q_st q) (t_distcode (s_tab (q_st q)))) (t_distbits (s_tab (q_st q))).

Record ReachMode (q : InfSt) : Prop := mkReachMode {
  rm_match  : q_mode q = M_MATCH -> match_side q;
  rm_len1   : q_mode q = M_LENEXT \/ q_mode q = M_DIST \/ q_mode q = M_DISTEXT ->
              1 <= u_length (s_cur (q_st q));
  rm_extra  : q_mode q = M_LENEXT \/ q_mode q = M_DISTEXT ->
              0 <= u_extra (s_cur (q_st q)) <= 15;
  rm_offext : q_mode q = M_DISTEXT ->
              0 <= u_offset (s_cur (q_st q))
              /\ u_offset (s_cur (q_st q))
                 + Z.shiftl 1 (u_extra (s_cur (q_st q))) <= 4294967296;
  (* pres repair 2026-08-19 (pres lane): MATCH's successor length is
     [u32 (length - cw3)], so keeping [1 <= length] across MATCH->MATCH
     needs an upper bound.  Two tiers: at LENEXT the bound is the table
     value cap (65535); LENEXT's own add of [bits_of u_extra] < 2^15
     (under [rm_extra]) lands below 98304. *)
  rm_lenub  : (q_mode q = M_LENEXT -> u_length (s_cur (q_st q)) <= 65535)
              /\ (q_mode q = M_DIST \/ q_mode q = M_DISTEXT
                  \/ q_mode q = M_MATCH ->
                  u_length (s_cur (q_st q)) <= 98303);
  (* pres repair 2026-08-19 (pres lane, per an earlier development run design note):
     antecedent widened from the five consuming modes to the whole
     LEN-loop SCC -- MATCH and LIT re-enter M_LEN with tables untouched,
     so step-closure needs the clause at those modes too. *)
  rm_tblL   : q_mode q = M_LEN \/ q_mode q = M_LEN_
              \/ q_mode q = M_LENEXT \/ q_mode q = M_DIST
              \/ q_mode q = M_DISTEXT \/ q_mode q = M_MATCH
              \/ q_mode q = M_LIT ->
              LenTblSide q;
  rm_tblCL  : q_mode q = M_CODELENS ->
              TblSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q))));
  (* Where nlen/ndist live in [1,288]/[1,32]: written by TABLE's own
     5-bit reads (+257/+1, gated at 286/30), read by the two build arms.
     TABLE itself needs no bound — [reach_TABLE] constructs it. *)
  rm_bldrng : q_mode q = M_LENLENS \/ q_mode q = M_CODELENS ->
              0 < b_nlen (s_bld (q_st q)) <= 288
              /\ 0 < b_ndist (s_bld (q_st q)) <= 32;
  (* pres-b3 repair (an earlier development run's exotic-CODES hole): the CODES build's
     guard needs the lenlens scratch <= 7 below 19, and multi-block
     streams leave the PREVIOUS block's code lengths (up to 15) in those
     slots — so carry the WRITTEN-PREFIX form: 3-bit-valued up to
     [b_have].  Cross-call honest (a mid-LENLENS leave stores exactly the
     written prefix); vacuous at the in-call TABLE entry (b_have = 0). *)
  rm_lens7  : q_mode q = M_LENLENS ->
              forall h, 0 <= h < b_have (s_bld (q_st q)) ->
              0 <= b_lens (s_bld (q_st q)) (inf_order h) <= 7;
  (* A1.2 (TL NOTICE-RULING-BATCH-ADDENDUM-A1 2026-09-02, q7/dec-u rider (a)):
     the home of the [u_back] bounds the body statements LENEXT_BODY_STMT
     (<= 30) and DIST_BODY_STMT (<= 45) carried as premises.  Measured at
     [Inflate.v]: LEN sets back := 0 then += nb (one or two table entries,
     each [c_bits <= 15] by [TblSide], so nb <= 30); LENEXT += extra (<= 15);
     DIST += nb (<= 30); DISTEXT += extra.  Tightest bounds the landed table
     contracts support: 30 / 45 / 75 (a root+sub <= 15 total is NOT a row of
     [LenTblSide], so 15/30/45 is not provable from the packs).  Lower bound
     0 from [inf_decode_ok_facts] ([0 <= nb]) and [rm_extra]. *)
  rm_back   : (q_mode q = M_LENEXT -> 0 <= u_back (s_cur (q_st q)) <= 30)
              /\ (q_mode q = M_DIST -> 0 <= u_back (s_cur (q_st q)) <= 45)
              /\ (q_mode q = M_DISTEXT -> 0 <= u_back (s_cur (q_st q)) <= 75);
  (* F-B3 (a5 ARITY RULING APPEND 657, q7 concurs, 2026-09-02): the TABLE arm's
     own reads -- [Inflate.v] [inf_TABLE] :1358-1366: nlen = 5 bits + 257,
     ndist = 5 bits + 1, TOO_MANY rejects 286 < nlen || 30 < ndist -- give the
     tight bounds at every LENLENS/CODELENS state.  [b_nlen]/[b_ndist] are
     written only there (:1364) and at reset (zeros, mode HEAD); LENLENS and
     CODELENS write [b_have]/[b_lens] only; a leave carries [s_bld] into the
     re-entry ([inf_st0] keeps [g_st]).  [rm_bldrng] (loose 0..288 / 0..32)
     STAYS as landed; this field is the tightening the tie ladders carried
     internally.  LAST field: appended after [rm_back]; positional prefix
     patterns over [ReachMode] stay valid. *)
  rm_nlen257 : q_mode q = M_LENLENS \/ q_mode q = M_CODELENS ->
              257 <= b_nlen (s_bld (q_st q)) <= 286
              /\ 1 <= b_ndist (s_bld (q_st q)) <= 30;
  (* (D') -- an earlier development run (fork), texts VERBATIM; provenance a5 665m (rc_tblpd home =
     ReachMode, text = q4's rm_tblpd) / a5 663 (sub-level source = an earlier development run's CfgBitsTbl) / a5 659 (ONE definition of
     TblPD: the leaf's) / q7 F6 (bits <= 14 at LEN).  [TblPD t root] (CfgBitsTblLeaf 29291912) = root-level
     prefix-determinism + positive root widths within [root] + the sub-table half (every level-2 pointer owns a
     prefix-deterministic sub-table of positive widths).  Sources at the cut: CODELENS install -> [it_tblpd_wf] on each
     accepted build (db_ok's it_wf/it_model/o_ret rows) transported through [codes_wb] ([tblpd_installed_len/dist]
     below); LENLENS's CODES build -> [rm_tblpdCL] the same way ([tblpd_codes_wb0]); TYPEDO's fixed tables ->
     [fix_tblpd].  Antecedent = the LEN-SCC (the seven modes that read the live tables; = rm_tblL's set). *)
  rm_tblpd : q_mode q = M_LEN \/ q_mode q = M_LEN_ \/ q_mode q = M_LENEXT \/ q_mode q = M_DIST \/ q_mode q = M_DISTEXT
             \/ q_mode q = M_MATCH \/ q_mode q = M_LIT ->
             TblPD (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) (t_lenbits (s_tab (q_st q)))
             /\ TblPD (tbl_of (q_st q) (t_distcode (s_tab (q_st q)))) (t_distbits (s_tab (q_st q)));
  (* the codes table at CODELENS (same [tbl_of] expression as [rm_tblCL]); a5 665p adopting q4's STOP #5 proposal *)
  rm_tblpdCL : q_mode q = M_CODELENS ->
               TblPD (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) (t_lenbits (s_tab (q_st q)))
               (* a5 STOP #8: the CODES root bound belongs with the CODELENS table row (it_model root <= root0 = 7) *)
               /\ t_lenbits (s_tab (q_st q)) <= 7;
  (* the bit-count row, 12-mode antecedent = the minimal step-closed set (q4 STOP #5, MEASURE-dprime : LIT->LEN
     and MATCH->LEN copy [q_br]; TYPE..CODELENS feed LEN_ with unchanged or dropped bits); REPLACES a5 665m's
     single-mode rm_lenbits14.  Decode side: [inf_decode_le14] (entry <= 14 -> post <= 13 over TblPD + SubGuardGen);
     NEEDBITS side: [inf_nb_ok_le] (no pull keeps the count, a pull ends below n + 8); fast path: if_finish's
     [bits mod 8] ([if_model_pres]'s 0 <= y_bits <= 7).  LAST field (a5 665p order: rm_tblpd, rm_tblpdCL, rm_bits14). *)
  rm_bits14 : q_mode q = M_TYPE \/ q_mode q = M_TYPEDO \/ q_mode q = M_TABLE \/ q_mode q = M_LENLENS \/ q_mode q = M_CODELENS
              \/ q_mode q = M_LEN_ \/ q_mode q = M_LEN \/ q_mode q = M_LENEXT \/ q_mode q = M_DIST \/ q_mode q = M_DISTEXT
              \/ q_mode q = M_MATCH \/ q_mode q = M_LIT ->
              br_bits (q_br q) <= 14;
  (* (D'') a5 WORDS STOP #6 (fork an earlier development run): the entry arms into rm_bits14's set -- HEAD (wrap = 0) -> TYPEDO, DICT ->
     TYPE, HCRC (flags & 0x200 = 0) -> TYPE, COPY_/COPY (length = 0) -> TYPE, and the gzip chain EXLEN -> EXTRA -> NAME -> COMMENT
     -> HCRC -- copy a bit count established by the INITBITS/BYTEBITS of a PREVIOUS step, so it is a reachability row, not an
     arm fact.  Text = RECEIPT-q4f-cand6.md §STOP6 VERBATIM (a5 signed on that md5); the flag-conditioned guards are
     exactly the pulling arms' branch conditions, so `= 0` is spelled only where the machine holds 0 (PLANTED-POSITIVES-rm_bits0.md
     : all five conjuncts pass; HEAD/EXLEN/HCRC re-entries after a partial NEEDBITS(16) pull hold 8 bits and are excluded
     by their guards).  Established by the INITBITS before each mode; preserved by br_consume / the whole-byte pulls. *)
  rm_bits0 : (q_mode q = M_HEAD -> h_wrap (s_hdr (q_st q)) = 0 -> br_bits (q_br q) = 0)
           /\ (q_mode q = M_EXLEN -> Z.land (h_flags (s_hdr (q_st q))) 1024 = 0 -> br_bits (q_br q) = 0)
           /\ (q_mode q = M_EXTRA \/ q_mode q = M_NAME \/ q_mode q = M_COMMENT -> br_bits (q_br q) = 0)
           /\ (q_mode q = M_HCRC -> Z.land (h_flags (s_hdr (q_st q))) 512 = 0 -> br_bits (q_br q) = 0)
           /\ (q_mode q = M_DICT \/ q_mode q = M_COPY_ \/ q_mode q = M_COPY -> br_bits (q_br q) = 0);
  (* (D'') a5 WORDS STOP #7: the width row over rm_tblpd's antecedent (the LEN-SCC); LAST field. *)
  rm_tblwid : q_mode q = M_LEN \/ q_mode q = M_LEN_ \/ q_mode q = M_LENEXT \/ q_mode q = M_DIST \/ q_mode q = M_DISTEXT
              \/ q_mode q = M_MATCH \/ q_mode q = M_LIT ->
              TblWidSide q;
  (* q7 ASK, home for l1's F-A4 (cross-call re-entry at DISTEXT must supply tie-x's V3 s3(c)
     `u_offset < 65536`).  SUPPLY: the only way a state with q_mode = M_DISTEXT is REACHED is DIST's non-BAD branch
     (Inflate.v inf_DIST: offset := c_val h, then fallthrough into inf_DISTEXT whose NEEDBITS(extra) may LEAVE with offset
     unchanged) -- pres_DIST's Hval : 0 <= c_val h < 65536 (LenTblSide's TblSide on the dist table via inf_decode_ok_facts);
     inf_DISTEXT's NBOk path leaves the mode (MATCH), its NBLeave keeps offset; InflateFast has no M_DISTEXT state; reset is HEAD;
     cross-call re-entry frames s_cur (reach_mode_st_any).  LAST field (append-anchor; a5 positions).  Statements gaining the
     premise: StepPres.reach_mode_distext and StepPres.pres_DISTEXT (LAST binder each). *)
  rm_off16 : q_mode q = M_DISTEXT -> u_offset (s_cur (q_st q)) < 65536;
  (* cand13 (TL ; PLAN-rm_off1 §1-§2 / ADDENDUM-1 §6, texts VERBATIM; q7's ruling on the rows
     pending — re-keyed on their word).  rm_dsub: the DIST table's level-2 entries are leaf-shaped (antecedent = rm_tblL / rm_tblpd /
     rm_tblwid's LEN-SCC set; the guard [0 < c_op] matches TblWid's conclusion for pointer-shaped root entries and is what
     [inf_decode_dist_leaf240] consumes).  rm_off1: the offset is positive at DISTEXT and MATCH — DIST's non-BAD branch sets
     [offset := c_val h] with [1 <= c_val h] ([dist_offset_pos]: rc_leafpos + rm_dsub + the branch's [land 64 = 0]); DISTEXT adds
     [bits_of extra >= 0]; MATCH's partial copies keep the offset; every other mode is vacuous; leaves / re-entries frame [s_cur].
     BOTH conjuncts (MEASURE-offrows item 2): a leave at DISTEXT re-enters at DISTEXT, so the MATCH conjunct alone is not
     step-closed.  Discharges tie-x's MATCH_OFF1_STMT premise via [StepPres.match_off1_of_reach].  LAST fields (append-anchor law;
     a5-2 rules position/arity).  rm_wrote0 (2026-09-11; a5-2 row 2147 / q7 R1810 / TL ; token VERBATIM): at
     HEAD nothing has been written in this call -- [q_out] is re-seated to [avail_out] at every entry ([inf_st0]) and the HEAD arm
     writes no output; the row-12 HEAD leaves consume it through [StepPres.reach_mode_hdr0]'s LAST binder.  LAST field. *)
  rm_dsub   : q_mode q = M_LEN \/ q_mode q = M_LEN_ \/ q_mode q = M_LENEXT \/ q_mode q = M_DIST \/ q_mode q = M_DISTEXT
              \/ q_mode q = M_MATCH \/ q_mode q = M_LIT ->
              DistSubLeaf (tbl_of (q_st q) (t_distcode (s_tab (q_st q)))) (t_distbits (s_tab (q_st q)));
  rm_off1   : (q_mode q = M_DISTEXT -> 1 <= u_offset (s_cur (q_st q)))
              /\ (q_mode q = M_MATCH -> 1 <= u_offset (s_cur (q_st q)));
  rm_wrote0 : q_mode q = M_HEAD -> q_out q - o_left (q_ob q) = 0;
  (* T2 res-t2 09-15 (q7 R2083 section 2 / R2085): the four CODES-table rows at M_CODELENS, rm_tblCL0..3, appended LAST after rm_wrote0 (the LAST law); suppliers at a CODES build = Spec/PngModel/CodesBuildRows.codes_build_rows. *)
  rm_tblCL0 : q_mode q = M_CODELENS -> t_lencode (s_tab (q_st q)) = TRcodes 0;
  rm_tblCL1 : q_mode q = M_CODELENS -> 1 <= t_lenbits (s_tab (q_st q));
  rm_tblCL2 : q_mode q = M_CODELENS -> 2 ^ t_lenbits (s_tab (q_st q)) <= t_next (s_tab (q_st q));
  rm_tblCL3 : q_mode q = M_CODELENS -> forall i, 0 <= i < 2 ^ t_lenbits (s_tab (q_st q)) -> 0 <= c_op (t_codes (s_tab (q_st q)) i) < 256
}.

Definition ReachSt (q : InfSt) : Prop := ReachCore q /\ ReachMode q.

(** ** The dispatch: [ReachSt] discharges every [step_ok_covered] premise
    except the two in-call tail obligations of the TABLE chain, which are
    carried through (their elimination is the knot lap: the TABLE-chain
    arms re-proved with THREADED callee premises, fed by the it_model
    output contracts — see the lap report). *)
Theorem step_ok_reachable :
  forall c q,
    ReachSt q ->
    (q_mode q = M_TABLE \/ q_mode q = M_LENLENS ->
       forall q', q_mode q' = M_CODELENS -> q_pos q' ->
         arm_ok q' (inf_CODELENS c q')) ->
    (q_mode q = M_CODELENS ->
       forall q', q_mode q' = M_LEN_ -> q_pos q' ->
         arm_ok q' (inf_LEN_ q')) ->
    step_ok c q.
Proof.
  intros c q (Hcore & Hmode) HCL HLEN.
  destruct Hcore as [Hpos Hbits Hbytes Hhold Hwin Hwnext Hwhave Hsane
                     Hlen0 Hinbud Hleft24 Hlens Hbhave Hbnlen Hbndist
                     Hamb].
  destruct Hmode as [Hmatch Hlen1 Hextra Hoffext Hlenub HtblL HtblCL
                     Hbldrng Hlens7].
  assert (Hhave24 : br_have (q_br q) <= 4294967290)
    by (destruct Hpos as (_ & Hb0 & _); lia).
  apply step_ok_covered.
  - exact Hpos.
  - exact Hlen0.
  - exact Hmatch.
  - intros _. split; [intros j; exact (proj1 (Hbytes j)) | exact Hhold].
  - intros Hm. split; [exact (Hlen1 Hm) | exact (proj1 Hwnext)].
  - exact Hextra.
  - intros Hm.
    assert (HL : LenTblSide q).
    { apply HtblL.
      destruct Hm as [Hm|Hm]; [right; right; left; exact Hm
                              | right; right; right; left; exact Hm]. }
    exact (proj1 (proj2 (proj2 HL))).
  - exact Hoffext.
  - intros Hm.
    assert (HL : LenTblSide q).
    { apply HtblL.
      destruct Hm as [Hm|Hm]; [left; exact Hm | right; left; exact Hm]. }
    destruct HL as (Htbl & Hlcs & Htds & Hlt & Hdt & Hlbnd & Hlb & Hdb & Hroot0).
    split.
    { intros Hgate.
      apply andb_prop in Hgate as [G1 G2].
      apply Z.leb_le in G1. apply Z.leb_le in G2.
      pose proof Hpos as (Hh & Hb & Hl).
      assert (Hb40 : 0 <= a_bits (len_args q) <= 40)
        by (cbn [len_args a_bits]; lia).
      split.
      { split; [exact G1|]. split; [exact G2|].
        split; [exact Hb40|].
        split; [exact Hlb|]. split; [exact Hdb|].
        split; [exact Hsane|].
        split; [exact Hwhave|]. split; [exact Hwnext|].
        split; [exact Hbytes|]. split; [exact Hwin|].
        split; [exact Hlt|]. split; [exact Hdt|]. exact Hlbnd. }
      split; [exact Htbl|].
      split; [exact Hhave24 | exact Hleft24]. }
    split; [exact Hlcs|]. split; [exact Htds|]. exact (proj1 Hwnext).
  - intros _. exact Hlens.
  - exact HCL.
  - intros Hm.
    split; [exact (HtblCL Hm)|].
    split; [exact Hbhave|]. split; [exact Hbnlen|].
    split; [exact Hbndist|].
    exact (HLEN Hm).
Qed.

(** * Environment walks for the knot lap (an earlier development run)

    The landed cl/ll walks state budget/lens facts; the knot's threading
    additionally needs, through the same loops: [br_in] constancy, the
    accumulator's nonnegativity, and the 39-bit reader cap.  All three are
    routine inductions over the same skeletons. *)

(** ** [inf_nb] *)

Lemma inf_nb_go_bits39 :
  forall f n b b',
    n <= 32 -> br_bits b <= 39 ->
    inf_nb_go f n b = NBOk b' -> br_bits b' <= 39.
Proof.
  induction f as [|f IH]; intros n b b' Hn Hb H; cbn [inf_nb_go] in H.
  - destruct (Z.ltb (br_bits b) n); [discriminate|].
    injection H as <-. exact Hb.
  - destruct (Z.ltb (br_bits b) n) eqn:E; [|injection H as <-; exact Hb].
    apply Z.ltb_lt in E.
    unfold br_pullbyte in H.
    destruct (Z.eqb (br_have b) 0); [discriminate|].
    apply IH in H; [exact H | exact Hn |].
    cbn [br_bits]. lia.
Qed.

Lemma inf_nb_bits39 :
  forall n b b',
    n <= 32 -> br_bits b <= 39 ->
    inf_nb n b = NBOk b' -> br_bits b' <= 39.
Proof. intros n b b'; apply inf_nb_go_bits39. Qed.

(** ** [inf_fetch] / [inf_fetch2] *)

Lemma inf_fetch_go_in :
  forall f t nb b h b',
    inf_fetch_go f t nb b = FetchOk h b' -> br_in b' = br_in b.
Proof.
  induction f as [|f IH]; intros t nb b h b' H; cbn [inf_fetch_go] in H;
    [discriminate|].
  destruct (Z.leb (c_bits (t (br_bits_of nb b))) (br_bits b));
    [now injection H as <- <-|].
  unfold br_pullbyte in H.
  destruct (Z.eqb (br_have b) 0); [discriminate|].
  apply IH in H. rewrite H. reflexivity.
Qed.

Lemma inf_fetch_in :
  forall t nb b h b',
    inf_fetch t nb b = FetchOk h b' -> br_in b' = br_in b.
Proof. intros t nb b h b'; apply inf_fetch_go_in. Qed.

Lemma inf_fetch_go_hold :
  forall f t nb b h b',
    0 <= br_hold b -> 0 <= br_bits b -> (forall j, 0 <= br_in b j) ->
    inf_fetch_go f t nb b = FetchOk h b' -> 0 <= br_hold b'.
Proof.
  induction f as [|f IH]; intros t nb b h b' Hh Hb Hin H;
    cbn [inf_fetch_go] in H; [discriminate|].
  destruct (Z.leb (c_bits (t (br_bits_of nb b))) (br_bits b));
    [now injection H as <- <-|].
  unfold br_pullbyte in H.
  destruct (Z.eqb (br_have b) 0); [discriminate|].
  apply IH in H; [exact H| | |].
  - cbn [br_hold]. pose proof (Hin (br_next b)).
    pose proof (Z.shiftl_nonneg (br_in b (br_next b)) (br_bits b)). lia.
  - cbn [br_bits]. lia.
  - cbn [br_in]. exact Hin.
Qed.

Lemma inf_fetch_hold :
  forall t nb b h b',
    0 <= br_hold b -> 0 <= br_bits b -> (forall j, 0 <= br_in b j) ->
    inf_fetch t nb b = FetchOk h b' -> 0 <= br_hold b'.
Proof. intros t nb b h b'; apply inf_fetch_go_hold. Qed.

Lemma inf_fetch_go_bits39 :
  forall f t nb b h b',
    (forall i, c_bits (t i) <= 15) ->
    br_bits b <= 39 ->
    inf_fetch_go f t nb b = FetchOk h b' -> br_bits b' <= 39.
Proof.
  induction f as [|f IH]; intros t nb b h b' Ht Hb H;
    cbn [inf_fetch_go] in H; [discriminate|].
  destruct (Z.leb (c_bits (t (br_bits_of nb b))) (br_bits b)) eqn:E;
    [now injection H as <- <-|].
  apply Z.leb_gt in E.
  pose proof (Ht (br_bits_of nb b)).
  unfold br_pullbyte in H.
  destruct (Z.eqb (br_have b) 0); [discriminate|].
  apply IH in H; [exact H | exact Ht |].
  cbn [br_bits]. lia.
Qed.

Lemma inf_fetch_bits39 :
  forall t nb b h b',
    (forall i, c_bits (t i) <= 15) ->
    br_bits b <= 39 ->
    inf_fetch t nb b = FetchOk h b' -> br_bits b' <= 39.
Proof. intros t nb b h b'; apply inf_fetch_go_bits39. Qed.

Lemma inf_fetch2_go_in :
  forall f t lst b h b',
    inf_fetch2_go f t lst b = FetchOk h b' -> br_in b' = br_in b.
Proof.
  induction f as [|f IH]; intros t lst b h b' H; cbn [inf_fetch2_go] in H;
    [discriminate|].
  match type of H with
  | context[Z.leb ?a ?bb] => destruct (Z.leb a bb)
  end; [now injection H as <- <-|].
  unfold br_pullbyte in H.
  destruct (Z.eqb (br_have b) 0); [discriminate|].
  apply IH in H. rewrite H. reflexivity.
Qed.

Lemma inf_fetch2_in :
  forall t lst b h b',
    inf_fetch2 t lst b = FetchOk h b' -> br_in b' = br_in b.
Proof. intros t lst b h b'; apply inf_fetch2_go_in. Qed.

Lemma inf_fetch2_go_hold :
  forall f t lst b h b',
    0 <= br_hold b -> 0 <= br_bits b -> (forall j, 0 <= br_in b j) ->
    inf_fetch2_go f t lst b = FetchOk h b' -> 0 <= br_hold b'.
Proof.
  induction f as [|f IH]; intros t lst b h b' Hh Hb Hin H;
    cbn [inf_fetch2_go] in H; [discriminate|].
  match type of H with
  | context[Z.leb ?a ?bb] => destruct (Z.leb a bb)
  end; [now injection H as <- <-|].
  unfold br_pullbyte in H.
  destruct (Z.eqb (br_have b) 0); [discriminate|].
  apply IH in H; [exact H| | |].
  - cbn [br_hold]. pose proof (Hin (br_next b)).
    pose proof (Z.shiftl_nonneg (br_in b (br_next b)) (br_bits b)). lia.
  - cbn [br_bits]. lia.
  - cbn [br_in]. exact Hin.
Qed.

Lemma inf_fetch2_hold :
  forall t lst b h b',
    0 <= br_hold b -> 0 <= br_bits b -> (forall j, 0 <= br_in b j) ->
    inf_fetch2 t lst b = FetchOk h b' -> 0 <= br_hold b'.
Proof. intros t lst b h b'; apply inf_fetch2_go_hold. Qed.

Lemma inf_fetch2_go_bits39 :
  forall f t lst b h b',
    c_bits lst <= 15 ->
    (forall i, c_bits (t i) <= 15) ->
    br_bits b <= 39 ->
    inf_fetch2_go f t lst b = FetchOk h b' -> br_bits b' <= 39.
Proof.
  induction f as [|f IH]; intros t lst b h b' Hl Ht Hb H;
    cbn [inf_fetch2_go] in H; [discriminate|].
  match type of H with
  | context[Z.leb ?a ?bb] => destruct (Z.leb a bb) eqn:E
  end; [now injection H as <- <-|].
  apply Z.leb_gt in E.
  pose proof (Ht (c_val lst
                  + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b)
                      (c_bits lst))) as Hix.
  unfold br_pullbyte in H.
  destruct (Z.eqb (br_have b) 0); [discriminate|].
  apply IH in H; [exact H | exact Hl | exact Ht |].
  cbn [br_bits]. lia.
Qed.

Lemma inf_fetch2_bits39 :
  forall t lst b h b',
    c_bits lst <= 15 ->
    (forall i, c_bits (t i) <= 15) ->
    br_bits b <= 39 ->
    inf_fetch2 t lst b = FetchOk h b' -> br_bits b' <= 39.
Proof. intros t lst b h b'; apply inf_fetch2_go_bits39. Qed.

(** ** [inf_decode]: composition of the two fetches and two drops *)

Lemma dropbits_in : forall n b, br_in (br_dropbits n b) = br_in b.
Proof. reflexivity. Qed.

Lemma dropbits_hold_nonneg : forall n b,
  0 <= br_hold b -> 0 <= br_hold (br_dropbits n b).
Proof.
  intros n b H. cbn [br_dropbits br_hold]. apply Z.shiftr_nonneg. exact H.
Qed.

Lemma inf_decode_env :
  forall sub t rb b h b2 nb,
    (forall i, 0 <= c_bits (t i) <= 15) ->
    0 <= br_hold b -> 0 <= br_bits b -> (forall j, 0 <= br_in b j) ->
    br_bits b <= 39 ->
    inf_decode sub t rb b = DecOk h b2 nb ->
    br_in b2 = br_in b /\ 0 <= br_hold b2 /\ br_bits b2 <= 39.
Proof.
  intros sub t rb b h b2 nb Ht Hh Hb Hin H39 H. unfold inf_decode in H.
  assert (Htu : forall i, c_bits (t i) <= 15)
    by (intros i; exact (proj2 (Ht i))).
  destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Ef;
    [|discriminate|discriminate].
  pose proof (inf_fetch_in _ _ _ _ _ Ef) as Fin.
  pose proof (inf_fetch_hold _ _ _ _ _ Hh Hb Hin Ef) as Fh.
  pose proof (inf_fetch_bits39 _ _ _ _ _ Htu H39 Ef) as F39.
  pose proof (inf_fetch_ok_bits _ _ _ _ _ Ef) as Fcov.
  destruct (inf_fetch_go_entry _ _ _ _ _ _ Ef) as (i0 & ->).
  destruct (sub (t i0)).
  - destruct (inf_fetch2 t (t i0) b0) as [h1 b1|b1|] eqn:Ef2;
      [|discriminate|discriminate].
    pose proof (inf_fetch2_in _ _ _ _ _ Ef2) as F2in.
    assert (Hin0 : forall j, 0 <= br_in b0 j)
      by (intros j; rewrite Fin; apply Hin).
    assert (Hb0 : 0 <= br_bits b0)
      by (pose proof (proj1 (Ht i0)); lia).
    pose proof (inf_fetch2_hold _ _ _ _ _ Fh Hb0 Hin0 Ef2) as F2h.
    pose proof (inf_fetch2_bits39 _ _ _ _ _ (Htu i0) Htu F39 Ef2) as F239.
    destruct (inf_fetch2_go_entry _ _ _ _ _ _ Ef2) as (i1 & ->).
    pose proof (proj1 (Ht i0)) as W0. pose proof (proj1 (Ht i1)) as W1.
    injection H as <- <- <-.
    cbn [br_dropbits br_in br_hold br_bits].
    split; [rewrite F2in; exact Fin|].
    split; [do 2 apply Z.shiftr_nonneg; exact F2h|].
    lia.
  - pose proof (proj1 (Ht i0)) as W0.
    injection H as <- <- <-.
    cbn [br_dropbits br_in br_hold br_bits].
    split; [exact Fin|].
    split; [apply Z.shiftr_nonneg; exact Fh|].
    lia.
Qed.

(** ** [cl_step] / [cl_loop] / [ll_go]: the same three clauses *)

Lemma inf_nb_env :
  forall n b b',
    n <= 32 ->
    0 <= br_hold b -> 0 <= br_bits b -> (forall j, 0 <= br_in b j) ->
    br_bits b <= 39 ->
    inf_nb n b = NBOk b' ->
    br_in b' = br_in b /\ 0 <= br_hold b' /\ br_bits b' <= 39.
Proof.
  intros n b b' Hn Hh Hb Hin H39 H.
  split; [exact (inf_nb_in _ _ _ H)|].
  split; [exact (inf_nb_hold _ _ _ Hh Hb Hin H)|].
  exact (inf_nb_bits39 _ _ _ Hn H39 H).
Qed.

Definition br_env (b b' : BR) : Prop :=
  br_in b' = br_in b /\ 0 <= br_hold b' /\ br_bits b' <= 39
  /\ 0 <= br_bits b'.

Lemma cl_step_env :
  forall t nb tot s,
    TblSide t ->
    0 <= br_have (cl_br s) -> 0 <= br_bits (cl_br s) ->
    0 <= br_hold (cl_br s) -> (forall j, 0 <= br_in (cl_br s) j) ->
    br_bits (cl_br s) <= 39 ->
    match cl_step t nb tot s with
    | ClCont s' | ClDone s' | ClBad s' _ =>
        br_env (cl_br s) (cl_br s')
    | ClLeave _ => True
    | ClFuel => False
    end.
Proof.
  intros t nb tot s Htbl Hh Hb Hhold Hin H39. unfold br_env. unfold cl_step.
  assert (Ht2 : forall i, 0 <= c_bits (t i) <= 15)
    by (intros i; exact (proj1 (Htbl i))).
  assert (Htu : forall i, c_bits (t i) <= 15)
    by (intros i; exact (proj2 (Ht2 i))).
  destruct (Z.leb tot (cl_have s)); cbv beta iota.
  { repeat split; try assumption; lia. }
  destruct (inf_fetch t nb (cl_br s)) as [h b|b|] eqn:Ef; cbv beta iota.
  2:{ exact I. }
  2:{ exfalso. exact (inf_fetch_no_fuel _ _ _ Hh Ef). }
  destruct (inf_fetch_go_entry _ _ _ _ _ _ Ef) as (i0 & Hhe).
  assert (Hcb : 0 <= c_bits h <= 15) by (rewrite Hhe; exact (Ht2 i0)).
  pose proof (inf_fetch_ok_bits _ _ _ _ _ Ef) as Hble.
  pose proof (inf_fetch_in _ _ _ _ _ Ef) as Fin.
  pose proof (inf_fetch_hold _ _ _ _ _ Hhold Hb Hin Ef) as Fh.
  pose proof (inf_fetch_bits39 _ _ _ _ _ Htu H39 Ef) as F39.
  destruct (Z.ltb (c_val h) 16) eqn:Ev16.
  { cbn [cl_br cl_lens cl_have].
    rewrite dropbits_in, dropbits_bits.
    split; [exact Fin|].
    split; [apply dropbits_hold_nonneg; exact Fh|].
    split; lia. }
  destruct (inf_nb (if Z.eqb (c_val h) 16 then c_bits h + 2
                    else if Z.eqb (c_val h) 17 then c_bits h + 3
                    else c_bits h + 7) b) as [b'|b'] eqn:Enb; [|exact I].
  assert (Hneed : (if Z.eqb (c_val h) 16 then c_bits h + 2
                   else if Z.eqb (c_val h) 17 then c_bits h + 3
                   else c_bits h + 7) <= 32)
    by (destruct (Z.eqb (c_val h) 16); destruct (Z.eqb (c_val h) 17); lia).
  assert (Hinb : forall j, 0 <= br_in b j)
    by (intros j; rewrite Fin; apply Hin).
  destruct (inf_nb_env _ _ _ Hneed Fh ltac:(lia) Hinb F39 Enb)
    as (Nin & Nh & N39).
  pose proof (inf_nb_ok _ _ _ Enb) as Nok.
  cbv zeta.
  destruct (Z.eqb (c_val h) 16) eqn:E16v; cbv beta iota.
  { destruct (Z.eqb (cl_have s) 0); cbv beta iota.
    { cbn [cl_br cl_lens cl_have].
      rewrite dropbits_in, dropbits_bits.
      repeat split; try lia.
      - rewrite Nin. exact Fin.
      - apply dropbits_hold_nonneg. exact Nh. }
    destruct (Z.ltb tot (cl_have s
                + (3 + br_bits_of 2 (br_dropbits (c_bits h) b'))));
      cbv beta iota;
      cbn [cl_br cl_lens cl_have];
      rewrite !dropbits_in, !dropbits_bits;
      (repeat split; try lia);
      [ rewrite Nin; exact Fin
      | do 2 apply dropbits_hold_nonneg; exact Nh
      | rewrite Nin; exact Fin
      | do 2 apply dropbits_hold_nonneg; exact Nh ]. }
  destruct (Z.eqb (c_val h) 17) eqn:E17v; cbv beta iota.
  { destruct (Z.ltb tot (cl_have s
                + (3 + br_bits_of 3 (br_dropbits (c_bits h) b'))));
      cbv beta iota;
      cbn [cl_br cl_lens cl_have];
      rewrite !dropbits_in, !dropbits_bits;
      (repeat split; try lia);
      [ rewrite Nin; exact Fin
      | do 2 apply dropbits_hold_nonneg; exact Nh
      | rewrite Nin; exact Fin
      | do 2 apply dropbits_hold_nonneg; exact Nh ]. }
  destruct (Z.ltb tot (cl_have s
              + (11 + br_bits_of 7 (br_dropbits (c_bits h) b'))));
    cbv beta iota;
    cbn [cl_br cl_lens cl_have];
    rewrite !dropbits_in, !dropbits_bits;
    (repeat split; try lia);
    [ rewrite Nin; exact Fin
    | do 2 apply dropbits_hold_nonneg; exact Nh
    | rewrite Nin; exact Fin
    | do 2 apply dropbits_hold_nonneg; exact Nh ].
Qed.

Lemma br_env_trans : forall b0 b1 b2,
  br_env b0 b1 -> br_env b1 b2 -> br_env b0 b2.
Proof.
  intros b0 b1 b2 (I1 & H1 & B1 & N1) (I2 & H2 & B2 & N2).
  split; [rewrite I2; exact I1|]. split; [exact H2|].
  split; [exact B2 | exact N2].
Qed.

Lemma cl_loop_env :
  forall m t nb tot s r,
    TblSide t ->
    0 <= br_have (cl_br s) -> 0 <= br_bits (cl_br s) ->
    0 <= br_hold (cl_br s) -> (forall j, 0 <= br_in (cl_br s) j) ->
    br_bits (cl_br s) <= 39 ->
    lens_ok (cl_lens s) ->
    cl_loop m t nb tot s = Some r ->
    match r with
    | ClDone s' | ClBad s' _ => br_env (cl_br s) (cl_br s')
    | _ => True
    end.
Proof.
  induction m as [|m IH]; intros t nb tot s r Htbl Hh Hb Hhold Hin H39 Hlens H;
    [cbn [cl_loop] in H; discriminate|].
  rewrite cl_loop_S in H.
  pose proof (cl_step_env t nb tot s Htbl Hh Hb Hhold Hin H39) as HE.
  pose proof (cl_step_walk t nb tot s Htbl Hh Hb Hlens) as HW.
  destruct (cl_step t nb tot s) as [s1|s1|s1 m1|s1|] eqn:ES.
  - destruct HE as (E1 & E2 & E3 & E4).
    destruct HW as (W1 & W2 & W3 & W4).
    assert (Hin1 : forall j, 0 <= br_in (cl_br s1) j)
      by (intros j; rewrite E1; apply Hin).
    pose proof (IH t nb tot s1 r Htbl W2 W3 E2 Hin1 E3 W4 H) as HR.
    destruct r as [s'|s'|s' m2|s'|]; try exact HR.
    + refine (br_env_trans _ _ _ _ HR).
      split; [exact E1|]. split; [exact E2|]. split; [exact E3 | exact E4].
    + refine (br_env_trans _ _ _ _ HR).
      split; [exact E1|]. split; [exact E2|]. split; [exact E3 | exact E4].
  - injection H as H; subst r. cbv beta iota. exact HE.
  - injection H as H; subst r. cbv beta iota. exact HE.
  - injection H as H; subst r. cbv beta iota. exact I.
  - contradiction HE.
Qed.

Lemma ll_go_env :
  forall f ncode have lens b,
    0 <= br_have b -> 0 <= br_bits b -> 0 <= br_hold b ->
    (forall j, 0 <= br_in b j) -> br_bits b <= 39 ->
    match ll_go f ncode have lens b with
    | LlOk _ _ b' => br_env b b'
    | LlLeave _ _ _ => True
    end.
Proof.
  induction f as [|f IH]; intros ncode have lens b Hh Hb Hhold Hin H39;
    cbn [ll_go].
  - repeat split; try assumption; lia.
  - destruct (Z.ltb have ncode); cbv beta iota;
      [|repeat split; try assumption; lia].
    destruct (inf_nb 3 b) as [b'|b'] eqn:Enb; cbv beta iota; [|exact I].
    destruct (inf_nb_env 3 b b' ltac:(lia) Hhold Hb Hin H39 Enb)
      as (Nin & Nh & N39).
    pose proof (inf_nb_ok _ _ _ Enb) as N3.
    pose proof (inf_nb_bud _ _ _ Enb) as (NB & NBmono & NHave).
    specialize (NHave Hh).
    assert (Hin' : forall j, 0 <= br_in (br_dropbits 3 b') j)
      by (intros j; rewrite dropbits_in, Nin; apply Hin).
    pose proof (IH ncode (have + 1)
                  (zset lens (inf_order have) (br_bits_of 3 b'))
                  (br_dropbits 3 b')
                  ltac:(rewrite dropbits_have; lia)
                  ltac:(rewrite dropbits_bits; lia)
                  ltac:(apply dropbits_hold_nonneg; exact Nh)
                  Hin'
                  ltac:(rewrite dropbits_bits; lia)) as HR.
    destruct (ll_go f ncode (have + 1)
                (zset lens (inf_order have) (br_bits_of 3 b'))
                (br_dropbits 3 b')) as [hv ls b2|hv ls b2]; [|exact I].
    refine (br_env_trans _ _ _ _ HR).
    unfold br_env. rewrite dropbits_in, dropbits_bits.
    split; [exact Nin|].
    split; [apply dropbits_hold_nonneg; exact Nh|].
    split; lia.
Qed.

(** * HOLDCLEAN support

    The reader-side supply for [rc_holdclean] (q7 RULING P1-F4-HOLD
    (ii) as amended by ADDENDUM 1 SR(2); l1's primitive
    table ): every primitive that writes the accumulator keeps
    [br_hold < 2 ^ br_bits] -- INITBITS re-establishes it, PULLBYTE
    preserves it for a byte < 256, DROPBITS(n) preserves it iff [n <= bits]
    (the premise Inflate.v's drop sites get from [inf_nb_ok] / the fetch
    guards / BYTEBITS's [n = bits & 7]) -- so the reader loops ([inf_nb],
    the fetches, [inf_decode]) and the two table walks ([cl_loop], [ll_go])
    transport it.  [br_hc] pairs the row with the [0 <= bits] every pull
    needs ([q_pos]'s second clause); the byte bound rides along because a
    pull reads [br_in]. *)

Definition br_hc (b : BR) : Prop :=
  0 <= br_bits b /\ br_hold b < 2 ^ br_bits b.

(** The ONE spelling bridge to [ZBitsIn.br_wf]'s row 2 (ZBitsIn.v:120),
    which spells the same fact as [br_hold b < Z.shiftl 1 (br_bits b)]. *)
Lemma holdclean_shiftl :
  forall b, br_hold b < 2 ^ br_bits b <-> br_hold b < Z.shiftl 1 (br_bits b).
Proof. intros b. rewrite Z.shiftl_1_l. reflexivity. Qed.

Lemma br_wf_hc : forall b, br_wf b -> br_hc b.
Proof.
  intros b (Hbits & Hhold & _ & _). split; [lia|].
  apply holdclean_shiftl. exact (proj2 Hhold).
Qed.

Lemma hc_of : forall b, br_hc b -> br_hold b < 2 ^ br_bits b.
Proof. intros b [_ H]. exact H. Qed.

Lemma hc_of_core : forall q, ReachCore q -> br_hc (q_br q).
Proof.
  intros q HC. split.
  - exact (proj1 (proj2 (rc_pos q HC))).
  - exact (rc_holdclean q HC).
Qed.

Lemma shiftr_lt_pow2 :
  forall h w n, h < 2 ^ w -> 0 <= n <= w -> Z.shiftr h n < 2 ^ (w - n).
Proof.
  intros h w n Hh Hn. rewrite Z.shiftr_div_pow2 by lia.
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  rewrite <- Z.pow_add_r by lia. replace (n + (w - n)) with w by lia.
  exact Hh.
Qed.

Lemma land7_range_hc : forall x, 0 <= x -> 0 <= Z.land x 7 <= x.
Proof.
  intros x Hx.
  replace (Z.land x 7) with (x mod 8)
    by (replace 7 with (Z.ones 3) by reflexivity;
        symmetry; apply Z.land_ones; lia).
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  pose proof (Z.div_mod x 8 ltac:(lia)).
  pose proof (Z.div_pos x 8 Hx ltac:(lia)).
  lia.
Qed.

Lemma initbits_hc : forall b, br_hc (br_initbits b).
Proof.
  intros b. split; cbn [br_initbits br_bits br_hold]; [lia | reflexivity].
Qed.

Lemma dropbits_hc :
  forall n b, br_hc b -> 0 <= n <= br_bits b -> br_hc (br_dropbits n b).
Proof.
  intros n b [Hb Hh] Hn. split; cbn [br_dropbits br_bits br_hold].
  - lia.
  - apply shiftr_lt_pow2; [exact Hh | lia].
Qed.

Lemma bytebits_hc : forall b, br_hc b -> br_hc (br_bytebits b).
Proof.
  intros b Hhc. unfold br_bytebits. apply dropbits_hc; [exact Hhc|].
  destruct Hhc as [Hb _]. exact (land7_range_hc (br_bits b) Hb).
Qed.

Lemma pullbyte_hc :
  forall b b', (forall j, 0 <= br_in b j < 256) -> br_hc b ->
    br_pullbyte b = Some b' ->
    br_hc b' /\ (forall j, 0 <= br_in b' j < 256).
Proof.
  intros b b' Hin [Hb Hh] Hp. unfold br_pullbyte in Hp.
  destruct (Z.eqb (br_have b) 0); [discriminate|]. injection Hp as <-.
  unfold br_hc. cbn [br_bits br_hold br_in]. split; [split; [lia|] | exact Hin].
  rewrite Z.shiftl_mul_pow2 by exact Hb. rewrite Z.pow_add_r by lia.
  change (2 ^ 8) with 256.
  pose proof (Z.pow_pos_nonneg 2 (br_bits b) ltac:(lia) Hb) as Hpos.
  pose proof (Hin (br_next b)) as Hbyte.
  assert (Hm : br_in b (br_next b) * 2 ^ br_bits b <= 255 * 2 ^ br_bits b)
    by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

(** ** [inf_nb] *)
Definition nb_br (r : NB) : BR := match r with NBOk b | NBLeave b => b end.

Lemma inf_nb_go_hc :
  forall f n b r, (forall j, 0 <= br_in b j < 256) -> br_hc b ->
    inf_nb_go f n b = r ->
    br_hc (nb_br r) /\ (forall j, 0 <= br_in (nb_br r) j < 256).
Proof.
  induction f as [|f IH]; intros n b r Hin Hhc H; cbn [inf_nb_go] in H.
  - destruct (Z.ltb (br_bits b) n); subst r; exact (conj Hhc Hin).
  - destruct (Z.ltb (br_bits b) n); [|subst r; exact (conj Hhc Hin)].
    destruct (br_pullbyte b) as [b1|] eqn:Ep; [|subst r; exact (conj Hhc Hin)].
    destruct (pullbyte_hc b b1 Hin Hhc Ep) as (H1 & In1).
    exact (IH n b1 r In1 H1 H).
Qed.

Lemma inf_nb_hc :
  forall n b r, (forall j, 0 <= br_in b j < 256) -> br_hc b ->
    inf_nb n b = r -> br_hc (nb_br r).
Proof.
  intros n b r Hin Hhc H. exact (proj1 (inf_nb_go_hc _ _ _ _ Hin Hhc H)).
Qed.

(** ** [inf_fetch] / [inf_fetch2] *)
Definition fetch_br (r : Fetch) : option BR :=
  match r with FetchOk _ b | FetchLeave b => Some b | FetchFuel => None end.

Lemma inf_fetch_go_hc :
  forall f t nb b r, (forall j, 0 <= br_in b j < 256) -> br_hc b ->
    inf_fetch_go f t nb b = r ->
    forall b', fetch_br r = Some b' ->
    br_hc b' /\ (forall j, 0 <= br_in b' j < 256).
Proof.
  induction f as [|f IH]; intros t nb b r Hin Hhc H b' Hr;
    cbn [inf_fetch_go] in H.
  - subst r. discriminate.
  - destruct (Z.leb (c_bits (t (br_bits_of nb b))) (br_bits b)).
    + subst r. cbn [fetch_br] in Hr. injection Hr as <-. exact (conj Hhc Hin).
    + destruct (br_pullbyte b) as [b1|] eqn:Ep.
      * destruct (pullbyte_hc b b1 Hin Hhc Ep) as (H1 & In1).
        exact (IH t nb b1 r In1 H1 H b' Hr).
      * subst r. cbn [fetch_br] in Hr. injection Hr as <-. exact (conj Hhc Hin).
Qed.

Lemma inf_fetch2_go_hc :
  forall f t lst b r, (forall j, 0 <= br_in b j < 256) -> br_hc b ->
    inf_fetch2_go f t lst b = r ->
    forall b', fetch_br r = Some b' ->
    br_hc b' /\ (forall j, 0 <= br_in b' j < 256).
Proof.
  induction f as [|f IH]; intros t lst b r Hin Hhc H b' Hr;
    cbn [inf_fetch2_go] in H.
  - subst r. discriminate.
  - match type of H with
    | context[Z.leb ?a ?bb] => destruct (Z.leb a bb)
    end.
    + subst r. cbn [fetch_br] in Hr. injection Hr as <-. exact (conj Hhc Hin).
    + destruct (br_pullbyte b) as [b1|] eqn:Ep.
      * destruct (pullbyte_hc b b1 Hin Hhc Ep) as (H1 & In1).
        exact (IH t lst b1 r In1 H1 H b' Hr).
      * subst r. cbn [fetch_br] in Hr. injection Hr as <-. exact (conj Hhc Hin).
Qed.

(** ** [inf_decode] *)
Definition dec_br (r : Dec) : option BR :=
  match r with DecOk _ b _ | DecLeave b => Some b | DecFuel => None end.

Lemma inf_decode_hc :
  forall sub t rb b r,
    (forall i, 0 <= c_bits (t i)) ->
    (forall j, 0 <= br_in b j < 256) -> br_hc b ->
    inf_decode sub t rb b = r ->
    forall b', dec_br r = Some b' -> br_hc b'.
Proof.
  intros sub t rb b r Ht Hin Hhc H b' Hr. unfold inf_decode in H.
  destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Ef; cbv beta iota in H.
  - destruct (inf_fetch_go_hc _ _ _ _ _ Hin Hhc Ef b0 eq_refl) as (H0 & In0).
    pose proof (inf_fetch_ok_bits _ _ _ _ _ Ef) as Hle0.
    destruct (inf_fetch_go_entry _ _ _ _ _ _ Ef) as (i0 & Hhe0).
    assert (Hc0 : 0 <= c_bits h0) by (rewrite Hhe0; apply Ht).
    destruct (sub h0); cbv beta iota in H.
    + destruct (inf_fetch2 t h0 b0) as [h1 b1|b1|] eqn:Ef2; cbv beta iota in H.
      * destruct (inf_fetch2_go_hc _ _ _ _ _ In0 H0 Ef2 b1 eq_refl) as (H1 & In1).
        pose proof (inf_fetch2_ok_bits _ _ _ _ _ Ef2) as Hle1.
        destruct (inf_fetch2_go_entry _ _ _ _ _ _ Ef2) as (i1 & Hhe1).
        assert (Hc1 : 0 <= c_bits h1) by (rewrite Hhe1; apply Ht).
        subst r. cbn [dec_br] in Hr. injection Hr as <-.
        apply dropbits_hc; [apply dropbits_hc; [exact H1 | lia] |].
        rewrite dropbits_bits. lia.
      * subst r. cbn [dec_br] in Hr. injection Hr as <-.
        exact (proj1 (inf_fetch2_go_hc _ _ _ _ _ In0 H0 Ef2 b1 eq_refl)).
      * subst r. discriminate.
    + subst r. cbn [dec_br] in Hr. injection Hr as <-.
      apply dropbits_hc; [exact H0 | lia].
  - subst r. cbn [dec_br] in Hr. injection Hr as <-.
    exact (proj1 (inf_fetch_go_hc _ _ _ _ _ Hin Hhc Ef b0 eq_refl)).
  - subst r. discriminate.
Qed.

(** ** [cl_step] / [cl_loop] *)
Definition cl_br_of (r : ClStep) : option BR :=
  match r with
  | ClCont s | ClDone s | ClBad s _ | ClLeave s => Some (cl_br s)
  | ClFuel => None
  end.

Lemma cl_step_hc :
  forall t nb tot s,
    (forall i, 0 <= c_bits (t i)) ->
    (forall j, 0 <= br_in (cl_br s) j < 256) -> br_hc (cl_br s) ->
    forall b', cl_br_of (cl_step t nb tot s) = Some b' ->
    br_hc b' /\ (forall j, 0 <= br_in b' j < 256).
Proof.
  intros t nb tot s Ht Hin Hhc b' Hr. unfold cl_step in Hr.
  destruct (Z.leb tot (cl_have s)); cbv beta iota in Hr.
  { cbn [cl_br_of] in Hr. injection Hr as <-. exact (conj Hhc Hin). }
  destruct (inf_fetch t nb (cl_br s)) as [h b|b|] eqn:Ef; cbv beta iota in Hr;
    [ | cbn [cl_br_of cl_br] in Hr; injection Hr as <-;
        exact (inf_fetch_go_hc _ _ _ _ _ Hin Hhc Ef b eq_refl)
      | discriminate ].
  destruct (inf_fetch_go_hc _ _ _ _ _ Hin Hhc Ef b eq_refl) as (Hb & Inb).
  pose proof (inf_fetch_ok_bits _ _ _ _ _ Ef) as Hle.
  destruct (inf_fetch_go_entry _ _ _ _ _ _ Ef) as (i0 & Hhe).
  assert (Hc0 : 0 <= c_bits h) by (rewrite Hhe; apply Ht).
  destruct (Z.ltb (c_val h) 16); cbv beta iota in Hr.
  { cbn [cl_br_of cl_br] in Hr. injection Hr as <-.
    split; [apply dropbits_hc; [exact Hb | lia] | exact Inb]. }
  cbv zeta in Hr.
  destruct (inf_nb (if Z.eqb (c_val h) 16 then c_bits h + 2
                    else if Z.eqb (c_val h) 17 then c_bits h + 3
                    else c_bits h + 7) b) as [b1|b1] eqn:Enb; cbv beta iota in Hr.
  2:{ cbn [cl_br_of cl_br] in Hr. injection Hr as <-.
      exact (inf_nb_go_hc _ _ _ _ Inb Hb Enb). }
  destruct (inf_nb_go_hc _ _ _ _ Inb Hb Enb) as (H1 & In1).
  cbn [nb_br] in H1, In1.
  pose proof (inf_nb_ok _ _ _ Enb) as Nok.
  assert (Hb2 : br_hc (br_dropbits (c_bits h) b1)).
  { apply dropbits_hc; [exact H1|]. split; [exact Hc0|].
    destruct (Z.eqb (c_val h) 16); [lia|].
    destruct (Z.eqb (c_val h) 17); lia. }
  assert (In2 : forall j, 0 <= br_in (br_dropbits (c_bits h) b1) j < 256)
    by (intros j; rewrite dropbits_in; apply In1).
  destruct (Z.eqb (c_val h) 16) eqn:E16; cbv beta iota in Hr.
  { destruct (Z.eqb (cl_have s) 0); cbv beta iota in Hr.
    { cbn [cl_br_of cl_br] in Hr. injection Hr as <-. exact (conj Hb2 In2). }
    match type of Hr with
    | context[Z.ltb ?a ?bb] => destruct (Z.ltb a bb)
    end; cbv beta iota in Hr; cbn [cl_br_of cl_br] in Hr; injection Hr as <-;
      (split; [apply dropbits_hc; [exact Hb2 | rewrite dropbits_bits; lia]
             | intros j; rewrite dropbits_in; apply In2]). }
  destruct (Z.eqb (c_val h) 17) eqn:E17; cbv beta iota in Hr.
  { match type of Hr with
    | context[Z.ltb ?a ?bb] => destruct (Z.ltb a bb)
    end; cbv beta iota in Hr; cbn [cl_br_of cl_br] in Hr; injection Hr as <-;
      (split; [apply dropbits_hc; [exact Hb2 | rewrite dropbits_bits; lia]
             | intros j; rewrite dropbits_in; apply In2]). }
  match type of Hr with
  | context[Z.ltb ?a ?bb] => destruct (Z.ltb a bb)
  end; cbv beta iota in Hr; cbn [cl_br_of cl_br] in Hr; injection Hr as <-;
    (split; [apply dropbits_hc; [exact Hb2 | rewrite dropbits_bits; lia]
           | intros j; rewrite dropbits_in; apply In2]).
Qed.

Lemma cl_loop_hc :
  forall m t nb tot s r,
    (forall i, 0 <= c_bits (t i)) ->
    (forall j, 0 <= br_in (cl_br s) j < 256) -> br_hc (cl_br s) ->
    cl_loop m t nb tot s = Some r ->
    forall b', cl_br_of r = Some b' -> br_hc b'.
Proof.
  induction m as [|m IH]; intros t nb tot s r Ht Hin Hhc H b' Hr;
    [cbn [cl_loop] in H; discriminate|].
  rewrite cl_loop_S in H.
  destruct (cl_step t nb tot s) as [s1|s1|s1 m1|s1|] eqn:ES.
  - destruct (cl_step_hc t nb tot s Ht Hin Hhc (cl_br s1)) as (H1 & In1);
      [rewrite ES; reflexivity|].
    exact (IH t nb tot s1 r Ht In1 H1 H b' Hr).
  - injection H as H; subst r. cbn [cl_br_of] in Hr. injection Hr as <-.
    exact (proj1 (cl_step_hc t nb tot s Ht Hin Hhc (cl_br s1)
                    ltac:(rewrite ES; reflexivity))).
  - injection H as H; subst r. cbn [cl_br_of] in Hr. injection Hr as <-.
    exact (proj1 (cl_step_hc t nb tot s Ht Hin Hhc (cl_br s1)
                    ltac:(rewrite ES; reflexivity))).
  - injection H as H; subst r. cbn [cl_br_of] in Hr. injection Hr as <-.
    exact (proj1 (cl_step_hc t nb tot s Ht Hin Hhc (cl_br s1)
                    ltac:(rewrite ES; reflexivity))).
  - injection H as H; subst r. discriminate.
Qed.

(** ** [ll_go] *)
Definition ll_br (r : LlRes) : BR :=
  match r with LlOk _ _ b | LlLeave _ _ b => b end.

Lemma ll_go_hc :
  forall f ncode have lens b,
    (forall j, 0 <= br_in b j < 256) -> br_hc b ->
    br_hc (ll_br (ll_go f ncode have lens b)).
Proof.
  induction f as [|f IH]; intros ncode have lens b Hin Hhc; cbn [ll_go].
  - exact Hhc.
  - destruct (Z.ltb have ncode); cbv beta iota; [|exact Hhc].
    destruct (inf_nb 3 b) as [b'|b'] eqn:Enb; cbv beta iota.
    2:{ exact (proj1 (inf_nb_go_hc _ _ _ _ Hin Hhc Enb)). }
    destruct (inf_nb_go_hc _ _ _ _ Hin Hhc Enb) as (H1 & In1).
    cbn [nb_br] in H1, In1.
    pose proof (inf_nb_ok _ _ _ Enb) as N3.
    apply IH; [intros j; rewrite dropbits_in; apply In1
              | apply dropbits_hc; [exact H1 | lia]].
Qed.

(** ** [br_have] monotonicity (pullbyte-only loops never grow [have]) *)

Lemma inf_nb_have_mono :
  forall n b b', inf_nb n b = NBOk b' -> br_have b' <= br_have b.
Proof.
  intros n b b' H. unfold inf_nb in H.
  revert b H. generalize (Z.to_nat n) as f. induction f as [|f IH];
    intros b H; cbn [inf_nb_go] in H.
  - destruct (Z.ltb (br_bits b) n); [discriminate|].
    injection H as <-. lia.
  - destruct (Z.ltb (br_bits b) n); [|injection H as <-; lia].
    unfold br_pullbyte in H.
    destruct (Z.eqb (br_have b) 0); [discriminate|].
    apply IH in H. cbn [br_have] in H. lia.
Qed.

Lemma inf_fetch_go_have_mono :
  forall f t nb b h b',
    inf_fetch_go f t nb b = FetchOk h b' -> br_have b' <= br_have b.
Proof.
  induction f as [|f IH]; intros t nb b h b' H; cbn [inf_fetch_go] in H;
    [discriminate|].
  destruct (Z.leb (c_bits (t (br_bits_of nb b))) (br_bits b));
    [injection H as <- <-; lia|].
  unfold br_pullbyte in H.
  destruct (Z.eqb (br_have b) 0); [discriminate|].
  apply IH in H. cbn [br_have] in H. lia.
Qed.

Lemma inf_fetch_have_mono :
  forall t nb b h b',
    inf_fetch t nb b = FetchOk h b' -> br_have b' <= br_have b.
Proof. intros t nb b h b'; apply inf_fetch_go_have_mono. Qed.

Lemma cl_step_have_mono :
  forall t nb tot s,
    match cl_step t nb tot s with
    | ClCont s' | ClDone s' | ClBad s' _ =>
        br_have (cl_br s') <= br_have (cl_br s)
    | _ => True
    end.
Proof.
  intros t nb tot s. unfold cl_step.
  destruct (Z.leb tot (cl_have s)); cbv beta iota; [lia|].
  destruct (inf_fetch t nb (cl_br s)) as [h b|b|] eqn:Ef; cbv beta iota;
    [|exact I|exact I].
  pose proof (inf_fetch_have_mono _ _ _ _ _ Ef) as Fm.
  destruct (Z.ltb (c_val h) 16).
  { cbn [cl_br]. rewrite dropbits_have. lia. }
  destruct (inf_nb (if Z.eqb (c_val h) 16 then c_bits h + 2
                    else if Z.eqb (c_val h) 17 then c_bits h + 3
                    else c_bits h + 7) b) as [b'|b'] eqn:Enb; [|exact I].
  pose proof (inf_nb_have_mono _ _ _ Enb) as Nm.
  cbv zeta.
  destruct (Z.eqb (c_val h) 16); cbv beta iota.
  { destruct (Z.eqb (cl_have s) 0); cbv beta iota.
    { cbn [cl_br]. rewrite dropbits_have. lia. }
    destruct (Z.ltb tot (cl_have s
                + (3 + br_bits_of 2 (br_dropbits (c_bits h) b'))));
      cbv beta iota; cbn [cl_br]; rewrite !dropbits_have; lia. }
  destruct (Z.eqb (c_val h) 17); cbv beta iota.
  { destruct (Z.ltb tot (cl_have s
                + (3 + br_bits_of 3 (br_dropbits (c_bits h) b'))));
      cbv beta iota; cbn [cl_br]; rewrite !dropbits_have; lia. }
  destruct (Z.ltb tot (cl_have s
              + (11 + br_bits_of 7 (br_dropbits (c_bits h) b'))));
    cbv beta iota; cbn [cl_br]; rewrite !dropbits_have; lia.
Qed.

Lemma cl_loop_have_mono :
  forall m t nb tot s r,
    cl_loop m t nb tot s = Some r ->
    match r with
    | ClDone s' | ClBad s' _ =>
        br_have (cl_br s') <= br_have (cl_br s)
    | _ => True
    end.
Proof.
  induction m as [|m IH]; intros t nb tot s r H;
    [cbn [cl_loop] in H; discriminate|].
  rewrite cl_loop_S in H.
  pose proof (cl_step_have_mono t nb tot s) as HS.
  destruct (cl_step t nb tot s) as [s1|s1|s1 m1|s1|] eqn:ES.
  - pose proof (IH t nb tot s1 r H) as HR.
    destruct r as [s'|s'|s' m2|s'|]; try exact I; lia.
  - injection H as H; subst r. cbv beta iota. exact HS.
  - injection H as H; subst r. cbv beta iota. exact HS.
  - injection H as H; subst r. cbv beta iota. exact I.
  - injection H as H; subst r. cbv beta iota. exact I.
Qed.

Lemma ll_go_have_mono :
  forall f ncode have lens b,
    match ll_go f ncode have lens b with
    | LlOk _ _ b' => br_have b' <= br_have b
    | LlLeave _ _ _ => True
    end.
Proof.
  induction f as [|f IH]; intros ncode have lens b; cbn [ll_go]; [lia|].
  destruct (Z.ltb have ncode); cbv beta iota; [|lia].
  destruct (inf_nb 3 b) as [b'|b'] eqn:Enb; cbv beta iota; [|exact I].
  pose proof (inf_nb_have_mono _ _ _ Enb) as Nm.
  pose proof (IH ncode (have + 1)
                (zset lens (inf_order have) (br_bits_of 3 b'))
                (br_dropbits 3 b')) as HR.
  destruct (ll_go f ncode (have + 1)
              (zset lens (inf_order have) (br_bits_of 3 b'))
              (br_dropbits 3 b')) as [hv ls b2|hv ls b2]; [|exact I].
  rewrite dropbits_have in HR. lia.
Qed.

(** ** The input-bit budget [8*have + bits] (pres lane, 2026-08-19)

    [br_pullbyte] conserves it and every drop shrinks it, so the two
    LENLENS/CODELENS loops never create input bits -- the walk facts
    [rc_inbud]'s preservation reads.  Crib: the [_have_mono] family
    above; the BR-level halves ([inf_nb_bud]/[inf_fetch_bud]) are
    landed in [InflateThy]. *)

Lemma cl_step_inbud :
  forall t nb tot s,
    (forall i, 0 <= c_bits (t i)) ->
    match cl_step t nb tot s with
    | ClCont s' | ClDone s' | ClBad s' _ =>
        8 * br_have (cl_br s') + br_bits (cl_br s')
          <= 8 * br_have (cl_br s) + br_bits (cl_br s)
    | _ => True
    end.
Proof.
  intros t nb tot s Hw. unfold cl_step.
  destruct (Z.leb tot (cl_have s)); cbv beta iota; [lia|].
  destruct (inf_fetch t nb (cl_br s)) as [h b|b|] eqn:Ef; cbv beta iota;
    [|exact I|exact I].
  destruct (inf_fetch_go_entry _ _ _ _ _ _ Ef) as (i0 & Hhe).
  assert (Hcb : 0 <= c_bits h) by (rewrite Hhe; exact (Hw i0)).
  apply inf_fetch_bud in Ef as (E0 & _).
  destruct (Z.ltb (c_val h) 16).
  { cbn [cl_br]. rewrite dropbits_have, dropbits_bits. lia. }
  destruct (inf_nb (if Z.eqb (c_val h) 16 then c_bits h + 2
                    else if Z.eqb (c_val h) 17 then c_bits h + 3
                    else c_bits h + 7) b) as [b'|b'] eqn:Enb; [|exact I].
  apply inf_nb_bud in Enb as (E1 & _ & _).
  cbv zeta.
  destruct (Z.eqb (c_val h) 16); cbv beta iota.
  { destruct (Z.eqb (cl_have s) 0); cbv beta iota.
    { cbn [cl_br]. rewrite !dropbits_have, !dropbits_bits. lia. }
    destruct (Z.ltb tot (cl_have s
                + (3 + br_bits_of 2 (br_dropbits (c_bits h) b'))));
      cbv beta iota; cbn [cl_br]; rewrite !dropbits_have, !dropbits_bits;
      lia. }
  destruct (Z.eqb (c_val h) 17); cbv beta iota.
  { destruct (Z.ltb tot (cl_have s
                + (3 + br_bits_of 3 (br_dropbits (c_bits h) b'))));
      cbv beta iota; cbn [cl_br]; rewrite !dropbits_have, !dropbits_bits;
      lia. }
  destruct (Z.ltb tot (cl_have s
              + (11 + br_bits_of 7 (br_dropbits (c_bits h) b'))));
    cbv beta iota; cbn [cl_br]; rewrite !dropbits_have, !dropbits_bits;
    lia.
Qed.

Lemma cl_loop_inbud :
  forall m t nb tot s r,
    (forall i, 0 <= c_bits (t i)) ->
    cl_loop m t nb tot s = Some r ->
    match r with
    | ClDone s' | ClBad s' _ =>
        8 * br_have (cl_br s') + br_bits (cl_br s')
          <= 8 * br_have (cl_br s) + br_bits (cl_br s)
    | _ => True
    end.
Proof.
  induction m as [|m IH]; intros t nb tot s r Hw H;
    [cbn [cl_loop] in H; discriminate|].
  rewrite cl_loop_S in H.
  pose proof (cl_step_inbud t nb tot s Hw) as HS.
  destruct (cl_step t nb tot s) as [s1|s1|s1 m1|s1|] eqn:ES.
  - pose proof (IH t nb tot s1 r Hw H) as HR.
    destruct r as [s'|s'|s' m2|s'|]; try exact I; lia.
  - injection H as H; subst r. cbv beta iota. exact HS.
  - injection H as H; subst r. cbv beta iota. exact HS.
  - injection H as H; subst r. cbv beta iota. exact I.
  - injection H as H; subst r. cbv beta iota. exact I.
Qed.

Lemma ll_go_inbud :
  forall f ncode have lens b,
    match ll_go f ncode have lens b with
    | LlOk _ _ b' =>
        8 * br_have b' + br_bits b' <= 8 * br_have b + br_bits b
    | LlLeave _ _ _ => True
    end.
Proof.
  induction f as [|f IH]; intros ncode have lens b; cbn [ll_go]; [lia|].
  destruct (Z.ltb have ncode); cbv beta iota; [|lia].
  destruct (inf_nb 3 b) as [b'|b'] eqn:Enb; cbv beta iota; [|exact I].
  apply inf_nb_bud in Enb as (E1 & _ & _).
  pose proof (IH ncode (have + 1)
                (zset lens (inf_order have) (br_bits_of 3 b'))
                (br_dropbits 3 b')) as HR.
  destruct (ll_go f ncode (have + 1)
              (zset lens (inf_order have) (br_bits_of 3 b'))
              (br_dropbits 3 b')) as [hv ls b2|hv ls b2]; [|exact I].
  rewrite dropbits_have, dropbits_bits in HR. lia.
Qed.

(** ** The lenlens scratch is 3-bit-valued on its written prefix
    (pres-b3): what discharges [dyn_amb_wb]'s CODES guard.  [zset] is
    pointwise and every write is in [0,7], so NO injectivity of
    [inf_order] is needed for preservation — only coverage of [0,19)
    at the end (one [vm_compute] over the literal permutation). *)

Lemma ct_lens_ne_codes : CT_LENS = CT_CODES -> False.
Proof. discriminate. Qed.
Lemma ct_dists_ne_codes : CT_DISTS = CT_CODES -> False.
Proof. discriminate. Qed.

Definition inf_order_cover_chk : bool :=
  forallb (fun i => existsb
                      (fun h => Z.eqb (inf_order (Z.of_nat h)) (Z.of_nat i))
                      (seq 0 19))
          (seq 0 19).

Lemma inf_order_cover_chk_true : inf_order_cover_chk = true.
Proof. vm_compute. reflexivity. Qed.

Lemma inf_order_covers :
  forall i, 0 <= i < 19 -> exists h, 0 <= h < 19 /\ inf_order h = i.
Proof.
  intros i Hi.
  pose proof inf_order_cover_chk_true as Hc.
  unfold inf_order_cover_chk in Hc.
  rewrite forallb_forall in Hc.
  specialize (Hc (Z.to_nat i) ltac:(apply in_seq; lia)).
  apply existsb_exists in Hc as (h & Hhin & Hb).
  apply in_seq in Hhin. apply Z.eqb_eq in Hb.
  rewrite Z2Nat.id in Hb by lia.
  exists (Z.of_nat h). split; [lia | exact Hb].
Qed.

Lemma ll_go_le7 :
  forall f ncode have lens b,
    (forall h, 0 <= h < have -> 0 <= lens (inf_order h) <= 7) ->
    match ll_go f ncode have lens b with
    | LlOk hv ls _ =>
        have <= hv
        /\ (forall h, 0 <= h < hv -> 0 <= ls (inf_order h) <= 7)
    | LlLeave _ _ _ => True
    end.
Proof.
  induction f as [|f IH]; intros ncode have lens b Hpre; cbn [ll_go].
  - split; [lia | exact Hpre].
  - destruct (Z.ltb have ncode); cbv beta iota;
      [|split; [lia | exact Hpre]].
    destruct (inf_nb 3 b) as [b'|b'] eqn:Enb; cbv beta iota; [|exact I].
    pose proof (bits_of_range 3 b' ltac:(lia)) as Hb3.
    change (2 ^ 3) with 8 in Hb3.
    pose proof (IH ncode (have + 1)
                  (zset lens (inf_order have) (br_bits_of 3 b'))
                  (br_dropbits 3 b')) as HR.
    lapply HR.
    2:{ intros h Hh. unfold zset.
        destruct (Z.eqb_spec (inf_order h) (inf_order have)) as [E|NE];
          [lia|].
        apply Hpre.
        assert (h <> have) by (intro; subst; congruence).
        lia. }
    clear HR; intros HR.
    destruct (ll_go f ncode (have + 1)
                (zset lens (inf_order have) (br_bits_of 3 b'))
                (br_dropbits 3 b')) as [hv ls b2|hv ls b2]; [|exact I].
    destruct HR as (Hge & Hp). split; [lia | exact Hp].
Qed.

Lemma ll_zero_le7 :
  forall f have lens,
    (forall h, 0 <= h < have -> 0 <= lens (inf_order h) <= 7) ->
    19 - have <= Z.of_nat f ->
    forall h, 0 <= h < 19 ->
      0 <= snd (ll_zero f have lens) (inf_order h) <= 7.
Proof.
  induction f as [|f IH]; intros have lens Hpre Hf h Hh;
    cbn [ll_zero snd].
  - apply Hpre. cbn [Z.of_nat] in Hf. lia.
  - destruct (Z.ltb_spec have 19) as [Hlt|Hge]; cbv beta iota.
    + apply IH; [| lia | exact Hh].
      intros h' Hh'. unfold zset.
      destruct (Z.eqb_spec (inf_order h') (inf_order have)) as [E|NE];
        [lia|].
      apply Hpre.
      assert (h' <> have) by (intro; subst; congruence).
      lia.
    + cbn [snd]. apply Hpre. lia.
Qed.

(** * The knot: TABLE -> LENLENS -> CODELENS -> LEN_ with discharged tails
    (2026-08-19, Q4 discharge lap, knot half; an earlier development run; TL-confirmed
    shape).

    THE ONE RESIDUAL: [DynTblOk] below — a record, one field per
    consumer-facing conjunct of the dynamic live-table contract, so the
    inhabitation lap can discharge and a census can name fields
    individually.  The former working names [dyn_tbl_contract] /
    [dyn_codes_tblside] are RETIRED into fields of this record; there is
    no other residual naming.

    INHABITATION NOTES, per the TL relay from the libpng farm:
    - [dyn_wf_tbl]/[dyn_lcside]/[dyn_two_l]: the LENS side has
      [GtLenProv]'s provenance program (ProvT/LenTblProv derivable) and
      [GtPtrProv.ptr_model_wf]; what neither provides is COVERAGE of the
      sub-table range [2^o_bits, o_used) ("every index below used is
      written by THIS build") — confirmed to have NO farm-side source
      (it_covers_root_pos is a bound on the ROOT range; used_ge_root_block
      is the boundary only; a bound at an index is not coverage of an
      index).  Discharge will be our own derivation from [it_model]'s
      fill loop, likely alongside the GtLenProv machinery.
    - [dyn_tblside_d]/[dyn_two_d] and the DISTS half of [dyn_wf_tbl]:
      the ptr/prov machinery is CT_LENS-scoped by construction (the arm
      census reads [x_extra c = lext]); the DISTS analogues are
      structural, unported, and confirmed absent farm-side.
    - [chain_fit] (both sides, inside [dyn_wf_tbl]): assembly from
      [GtLenProv]'s proven [PtrWidthAlong] is unbuilt.
    - [dyn_codes_tblside]: width/value bounds of a CT_CODES build's
      read-back — nearest to closable from provenance alone.
    - [dyn_lenbits]/[dyn_distbits]: [o_bits] range on accepted builds
      ([it_pre] clamps root to [1,15]; the empty arm returns 1). *)

(** The two accepted builds of one CODELENS trip, as data + equations.
    [db_cs] is the codes array BEFORE the builds; the LENS build lands at
    offset 0, the DISTS build at [o_used] of the first. *)
Record DynBuild : Type := mkDynBuild {
  db_cs    : ztbl;
  db_lens  : zarr;
  db_nlen  : Z;
  db_ndist : Z;
  db_o1    : ItOut;
  db_o2    : ItOut
}.

Definition db_ok (d : DynBuild) : Prop :=
  amb_ok (db_cs d)
  /\ it_wf CT_LENS (db_lens d) (db_nlen d) 9
  /\ it_model CT_LENS (db_lens d) (db_nlen d) 9
       (fun i => db_cs d (0 + i)) = Some (db_o1 d)
  /\ o_ret (db_o1 d) = 0
  /\ it_wf CT_DISTS (fun i => db_lens d (i + db_nlen d)) (db_ndist d) 6
  /\ it_model CT_DISTS (fun i => db_lens d (i + db_nlen d)) (db_ndist d) 6
       (fun i => codes_wb (db_cs d) 0 (o_tbl (db_o1 d))
                   ((0 + o_used (db_o1 d)) + i)) = Some (db_o2 d)
  /\ o_ret (db_o2 d) = 0.

(** The state shape CODELENS installs from an accepted pair. *)
Definition db_installed (d : DynBuild) (q' : InfSt) : Prop :=
  t_lencode (s_tab (q_st q')) = TRcodes 0
  /\ t_lenbits (s_tab (q_st q')) = o_bits (db_o1 d)
  /\ t_distcode (s_tab (q_st q')) = TRcodes (0 + o_used (db_o1 d))
  /\ t_distbits (s_tab (q_st q')) = o_bits (db_o2 d)
  /\ t_codes (s_tab (q_st q'))
     = codes_wb (codes_wb (db_cs d) 0 (o_tbl (db_o1 d)))
         (0 + o_used (db_o1 d)) (o_tbl (db_o2 d)).

(** THE residual record. *)
Record DynTblOk : Prop := mkDynTblOk {
  dyn_codes_tblside :
    forall lens codes root0 cs o,
      amb_ok cs ->
      it_wf CT_CODES lens codes root0 ->
      it_model CT_CODES lens codes root0 (fun i => cs (0 + i)) = Some o ->
      o_ret o = 0 ->
      TblSide (fun i => codes_wb cs 0 (o_tbl o) (0 + i));
  (* amb_ok preservation through ONE build (any ctype, offset k): the
     written region by entry-shape provenance, the rest by [amb_ok cs]
     and the o_tbl/t0 frame fact of the fill.  NO acceptance premise
     (pres repair 2026-08-19): CODELENS/LENLENS install [codes_wb]
     BEFORE testing the build's return, so the qbad successors of
     REJECTED builds consume this too. *)
  dyn_amb_wb :
    forall ty lens codes root0 cs k o,
      amb_ok cs ->
      it_wf ty lens codes root0 ->
      (* pres-b3 guard (an earlier development run): it_enough never caps CT_CODES, so an
         it_wf-legal CODES call with root0 below the max length opens
         unbounded sub-table windows and a u16-wrapped pointer val can be
         0 while op-live, breaking [amb_ok]'s val-positivity in the
         WRITTEN table.  The cap makes CODES open no windows at all;
         the real LENLENS call discharges it from the 3-bit write walk. *)
      (ty = CT_CODES -> forall i, 0 <= i < codes -> lens i <= root0) ->
      it_model ty lens codes root0 (fun i => cs (k + i)) = Some o ->
      amb_ok (codes_wb cs k (o_tbl o));
  dyn_wf_tbl :
    forall d q', db_ok d -> db_installed d q' -> if_wf_tbl (len_args q');
  dyn_lcside :
    forall d q', db_ok d -> db_installed d q' ->
      LcSide (tbl_of (q_st q') (t_lencode (s_tab (q_st q'))));
  dyn_tblside_d :
    forall d q', db_ok d -> db_installed d q' ->
      TblSide (tbl_of (q_st q') (t_distcode (s_tab (q_st q'))));
  dyn_two_l :
    forall d q', db_ok d -> db_installed d q' ->
      lcode_two_level (if_ctx (len_args q'));
  dyn_two_d :
    forall d q', db_ok d -> db_installed d q' ->
      dcode_two_level (if_ctx (len_args q'));
  dyn_lenbits : forall d, db_ok d -> 1 <= o_bits (db_o1 d) <= 15;
  dyn_distbits : forall d, db_ok d -> 1 <= o_bits (db_o2 d) <= 15;
  (* rootshape wave (q7-decode): the masked-root op-shape clause at the
     installed LEN view; inhabitation = RootEntry projection of the
     landed coverage (DynTblOkHolds). *)
  dyn_root_opshape :
    forall d q', db_ok d -> db_installed d q' ->
      lcode_root_opshape (tbl_of (q_st q') (t_lencode (s_tab (q_st q'))))
        (t_lenbits (s_tab (q_st q')))
}.

(** [if_wf_tbl]'s bundled package IS the length bound. *)
Lemma wf_tbl_len_bounded :
  forall a, if_wf_tbl a -> lcode_len_bounded (if_ctx a).
Proof.
  intros a ((n & Hup & Hir & _ & _) & _).
  exists n. split; [exact Hup | exact Hir].
Qed.

(** The unconditional core the knot threads (a projection of [ReachCore]
    that the constructed tail states can carry). *)
Definition CoreFacts (q : InfSt) : Prop :=
  q_pos q
  /\ br_bits (q_br q) <= 39
  /\ (forall j, 0 <= br_in (q_br q) j < 256)
  /\ (forall j, 0 <= w_win (s_win (q_st q)) j < 256)
  /\ 0 <= w_wnext (s_win (q_st q)) <= w_wsize (s_win (q_st q))
  /\ 0 <= w_whave (s_win (q_st q)) <= w_wsize (s_win (q_st q))
  /\ t_sane (s_tab (q_st q)) = 1
  /\ 8 * br_have (q_br q) + br_bits (q_br q) <= 34359738320
  /\ o_left (q_ob q) <= 4294967295
  /\ 0 <= br_hold (q_br q)
  /\ amb_ok (t_codes (s_tab (q_st q))).

Lemma core_of_reach : forall q, ReachCore q -> CoreFacts q.
Proof.
  intros q [Hpos Hbits Hbytes Hhold Hwin Hwnext Hwhave Hsane Hlen0 Hh24
            Hl24 Hlens Hbh Hbn Hbd Hamb].
  split; [exact Hpos|]. split; [exact Hbits|]. split; [exact Hbytes|].
  split; [exact Hwin|]. split; [exact Hwnext|]. split; [exact Hwhave|].
  split; [exact Hsane|]. split; [exact Hh24|]. split; [exact Hl24|].
  split; [exact Hhold|]. exact Hamb.
Qed.

(** The discharged bottom of the chain: LEN_ from the threaded facts. *)
Lemma tail_LEN_ok :
  forall q', q_mode q' = M_LEN_ -> CoreFacts q' -> LenTblSide q' ->
    arm_ok q' (inf_LEN_ q').
Proof.
  intros q' Hm (Hpos & Hbits & Hbytes & Hwin & Hwnext & Hwhave & Hsane
                & Hh24 & Hl24 & Hhold & Hamb) HL.
  destruct HL as (Htbl & Hlcs & Htds & Hlt & Hdt & Hlbnd & Hlb & Hdb & Hroot0).
  apply arm_LEN_; try assumption.
  2:{ exact (proj1 Hwnext). }
  - intros Hgate.
    apply andb_prop in Hgate as [G1 G2].
    apply Z.leb_le in G1. apply Z.leb_le in G2.
    pose proof Hpos as (Hh & Hb & Hl).
    assert (Hb40 : 0 <= a_bits (len_args q') <= 40)
      by (cbn [len_args a_bits]; lia).
    split.
    { split; [exact G1|]. split; [exact G2|].
      split; [exact Hb40|].
      split; [exact Hlb|]. split; [exact Hdb|].
      split; [exact Hsane|].
      split; [exact Hwhave|]. split; [exact Hwnext|].
      split; [exact Hbytes|]. split; [exact Hwin|].
      split; [exact Hlt|]. split; [exact Hdt|]. exact Hlbnd. }
    split; [exact Htbl|].
    split; [lia | exact Hl24].
Qed.

(** [bsimp] plus the table/build projections the tail states read. *)
Ltac ksimp :=
  bsimp;
  cbn [t_sane t_lencode t_lenbits t_distcode t_distbits t_codes t_next
       b_lens b_have b_nlen b_ndist].

Section Knot.

Variable Hdyn : DynTblOk.

(** [inf_CODELENS] with the LEN_ tail DISCHARGED: where the landed
    [arm_CODELENS] carries the tail as a quantified premise (the coverage
    ledger, retention convention), this one hands the constructed state to
    [tail_LEN_ok], with the table bundle produced by [Hdyn] at the
    [DynBuild] the arm itself just accepted. *)
(* RSS cure C1' (ca2-b1 / F47, 2026-09-08): measured by one-conjunct probes, the two CoreFacts conjuncts whose goal projects the
   constructed state's TABLE (t_sane / t_codes through eight nested set_* on s_tab) cost 30 s and ~1.4 GiB EACH under `ksimp` (cbn refolding the setter
   chain) and 1.5 s / 0.47 GiB under the bare `exact` (lazy conversion); the two `ksimp` calls are dropped, nothing else moves. *)
Lemma reach_CODELENS :
  forall c q,
    q_mode q = M_CODELENS ->
    CoreFacts q ->
    lens_ok (b_lens (s_bld (q_st q))) ->
    0 <= b_have (s_bld (q_st q)) ->
    0 < b_nlen (s_bld (q_st q)) <= 288 ->
    0 < b_ndist (s_bld (q_st q)) <= 32 ->
    TblSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) ->
    arm_ok q (inf_CODELENS c q).
Proof.
  intros c q Hm Hcore Hlens Hhave Hnlen Hndist Htl.
  pose proof Hcore as (Hp & H39 & Hbytes & Hwinb & Hwnext & Hwhave & Hsane
                       & Hh24 & Hl24 & Hhold & Hamb).
  pose proof Hp as (Hh & Hb & Hl).
  assert (Hnlen0 : 0 <= b_nlen (s_bld (q_st q))) by lia.
  assert (Hndist0 : 0 <= b_ndist (s_bld (q_st q))) by lia.
  unfold inf_CODELENS. cbv zeta beta.
  destruct (cl_loop_at_codelens_fuel
              (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
              (t_lenbits (s_tab (q_st q)))
              (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
              {| cl_have := b_have (s_bld (q_st q));
                 cl_lens := b_lens (s_bld (q_st q));
                 cl_br := q_br q |}
              ltac:(cbn [cl_br]; lia) ltac:(cbn [cl_have]; lia))
    as (r & Hr & Hexit).
  rewrite Hr. cbv beta iota.
  pose proof (cl_loop_walk
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r Htl Hh Hb Hlens Hr) as HW.
  cbn [cl_br cl_lens cl_have] in HW.
  pose proof (cl_loop_env
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r Htl Hh Hb Hhold
                (fun j => proj1 (Hbytes j)) H39 Hlens Hr) as HE.
  cbn [cl_br cl_lens cl_have] in HE.
  pose proof (cl_loop_have_mono
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r Hr) as HM.
  cbn [cl_br cl_lens cl_have] in HM.
  pose proof (cl_loop_inbud
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r
                (fun i => proj1 (proj1 (Htl i))) Hr) as HBgt.
  cbn [cl_br cl_lens cl_have] in HBgt.
  destruct r as [s1|s1|s1 m1|s1|]; cbn [cl_exit] in Hexit;
    try contradiction; [| |exact I].
  - (* ClDone: the two builds, then the DISCHARGED LEN_ tail *)
    destruct HW as (W1 & W2 & W3 & W4).
    destruct HE as (Ein & Ehold & E39 & E0b).
    cbv beta iota in HM.
    destruct (Z.eqb (cl_lens s1 256) 0).
    { cbn [arm_ok]. split.
      - unfold q_pos. bsimp. repeat split; lia.
      - apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
    unfold inf_table.
    assert (HLB1 : GtItTotal.LensBounded (cl_lens s1) (b_nlen (s_bld (q_st q))))
      by (intros i _; apply W4).
    match goal with
    | |- context [it_model CT_LENS ?l ?cs ?rt ?t0] =>
        remember (it_model CT_LENS l cs rt t0) as R1 eqn:EI1
    end.
    destruct R1 as [o1|].
    2:{ exfalso.
        exact (it_model_total _ _ _ _ _ Hnlen0 HLB1 (eq_sym EI1)). }
    cbv beta iota zeta.
    destruct (negb (Z.eqb (o_ret o1) 0)) eqn:Er1.
    { cbn [arm_ok]. split.
      - unfold q_pos. bsimp. repeat split; lia.
      - apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
    apply Bool.negb_false_iff in Er1. apply Z.eqb_eq in Er1.
    assert (HLB2 : GtItTotal.LensBounded
                     (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
                     (b_ndist (s_bld (q_st q))))
      by (intros i _; cbv beta; apply W4).
    match goal with
    | |- context [it_model CT_DISTS ?l ?cs ?rt ?t0] =>
        remember (it_model CT_DISTS l cs rt t0) as R2 eqn:EI2
    end.
    destruct R2 as [o2|].
    2:{ exfalso.
        exact (it_model_total _ _ _ _ _ Hndist0 HLB2 (eq_sym EI2)). }
    cbv beta iota zeta.
    destruct (negb (Z.eqb (o_ret o2) 0)) eqn:Er2.
    { cbn [arm_ok]. split.
      - unfold q_pos. bsimp. repeat split; lia.
      - apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
    apply Bool.negb_false_iff in Er2. apply Z.eqb_eq in Er2.
    destruct (Z.eqb (n_flush c) Z_TREES); [exact I|].
    (* The accepted build, named *)
    assert (HWF1 : it_wf CT_LENS (cl_lens s1) (b_nlen (s_bld (q_st q))) 9).
    { split; [lia|]. split; [intros i _; apply W4|].
      split; [unfold MAXBITS; lia|].
      right; left; split; [reflexivity | lia]. }
    assert (HWF2 : it_wf CT_DISTS
                     (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
                     (b_ndist (s_bld (q_st q))) 6).
    { split; [lia|]. split; [intros i _; cbv beta; apply W4|].
      split; [unfold MAXBITS; lia|].
      right; right; split; [reflexivity | lia]. }
    set (d := {| db_cs := t_codes (s_tab (q_st q));
                 db_lens := cl_lens s1;
                 db_nlen := b_nlen (s_bld (q_st q));
                 db_ndist := b_ndist (s_bld (q_st q));
                 db_o1 := o1; db_o2 := o2 |}).
    assert (Hdok : db_ok d).
    { split; [exact Hamb|].
      split; [exact HWF1|].
      split; [exact (eq_sym EI1)|].
      split; [exact Er1|].
      split; [exact HWF2|].
      split; [exact (eq_sym EI2)|].
      exact Er2. }
    match goal with
    | |- arm_ok _ (inf_LEN_ ?qq) =>
        assert (Hinst : db_installed d qq) by (repeat split; reflexivity)
    end.
    eapply (arm_ok_mono _ q).
    2:{ apply tail_LEN_ok.
        - bsimp; reflexivity.
        - (* CoreFacts at the constructed tail *)
          split. { unfold q_pos. ksimp. repeat split; lia. }
          split. { ksimp. lia. }
          split. { intros j. ksimp. rewrite Ein. exact (Hbytes j). }
          split. { intros j. ksimp. exact (Hwinb j). }
          split. { ksimp. lia. }
          split. { ksimp. lia. }
          split. { exact Hsane. }
          split. { ksimp. lia. }
          split. { ksimp. lia. }
          split. { ksimp. exact Ehold. }
          exact (dyn_amb_wb Hdyn CT_DISTS
                   (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
                   (b_ndist (s_bld (q_st q))) 6
                   (codes_wb (t_codes (s_tab (q_st q))) 0 (o_tbl o1))
                   (0 + o_used o1) o2
                   (dyn_amb_wb Hdyn CT_LENS (cl_lens s1)
                      (b_nlen (s_bld (q_st q))) 9
                      (t_codes (s_tab (q_st q))) 0 o1
                      Hamb HWF1
                      (fun Hty => False_ind _ (ct_lens_ne_codes Hty))
                      (eq_sym EI1))
                   HWF2
                   (fun Hty => False_ind _ (ct_dists_ne_codes Hty))
                   (eq_sym EI2)).
        - (* LenTblSide at the constructed tail, from [Hdyn] at [d] *)
          split. { exact (dyn_wf_tbl Hdyn d _ Hdok Hinst). }
          split. { exact (dyn_lcside Hdyn d _ Hdok Hinst). }
          split. { exact (dyn_tblside_d Hdyn d _ Hdok Hinst). }
          split. { exact (dyn_two_l Hdyn d _ Hdok Hinst). }
          split. { exact (dyn_two_d Hdyn d _ Hdok Hinst). }
          split. { exact (wf_tbl_len_bounded _
                            (dyn_wf_tbl Hdyn d _ Hdok Hinst)). }
          split. { exact (dyn_lenbits Hdyn d Hdok). }
          split. { exact (dyn_distbits Hdyn d Hdok). }
          exact (dyn_root_opshape Hdyn d _ Hdok Hinst). }
    apply rank2_le' with (m := M_CODELENS) (m' := M_LEN_);
      [exact Hm | bsimp; reflexivity |].
    cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
  - (* ClBad -> BAD (ascends, budget non-increasing) *)
    destruct HW as (W1 & W2 & W3 & W4).
    cbn [arm_ok]. split.
    + unfold q_pos. bsimp. repeat split; lia.
    + apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
        [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
Qed.

(** [inf_LENLENS] with the CODELENS tail discharged: the freshly built
    CODES table's [TblSide] is [dyn_codes_tblside] at the accepted
    [it_model CT_CODES] output; everything else threads. *)
Lemma reach_LENLENS :
  forall c q,
    q_mode q = M_LENLENS ->
    CoreFacts q ->
    lens_ok (b_lens (s_bld (q_st q))) ->
    (forall h, 0 <= h < b_have (s_bld (q_st q)) ->
       0 <= b_lens (s_bld (q_st q)) (inf_order h) <= 7) ->
    0 <= b_have (s_bld (q_st q)) ->
    0 < b_nlen (s_bld (q_st q)) <= 288 ->
    0 < b_ndist (s_bld (q_st q)) <= 32 ->
    arm_ok q (inf_LENLENS c q).
Proof.
  intros c q Hm Hcore Hlens Hpre7 Hbh0 Hnlen Hndist.
  pose proof Hcore as (Hp & H39 & Hbytes & Hwinb & Hwnext & Hwhave & Hsane
                       & Hh24 & Hl24 & Hhold & Hamb).
  pose proof Hp as (Hh & Hb & Hl).
  unfold inf_LENLENS. cbv zeta.
  pose proof (ll_go_walk 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hh Hb Hlens) as HW.
  pose proof (ll_go_env 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hh Hb Hhold (fun j => proj1 (Hbytes j)) H39) as HE.
  pose proof (ll_go_have_mono 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q)) as HM.
  pose proof (ll_go_inbud 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q)) as HBgt.
  pose proof (ll_go_le7 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hpre7) as HL7.
  match goal with
  | |- context [ll_go ?f ?nc ?hv0 ?ls0 ?b0] =>
      remember (ll_go f nc hv0 ls0 b0) as LG eqn:ELG
  end.
  destruct LG as [hv ls b|hv ls b]; [|exact I].
  destruct HW as (W1 & W2 & W3 & W4).
  destruct HE as (Ein & Ehold & E39 & E0b).
  cbv beta iota in HM.
  remember (ll_zero 19 hv ls) as LZ eqn:EZ.
  destruct LZ as [hv1 ls1]. cbv beta iota.
  assert (Hls1 : lens_ok ls1).
  { pose proof (ll_zero_walk 19 hv ls W4) as HZ. rewrite <- EZ in HZ.
    exact HZ. }
  cbv beta iota in HL7. destruct HL7 as (Hhvge & Hp7).
  assert (Hg7 : forall h, 0 <= h < 19 -> 0 <= ls1 (inf_order h) <= 7).
  { intros h Hh19.
    pose proof (ll_zero_le7 19 hv ls Hp7
                  ltac:(cbn [Z.of_nat]; lia) h Hh19) as HZ7.
    rewrite <- EZ in HZ7. cbn [snd] in HZ7. exact HZ7. }
  assert (Hguard : CT_CODES = CT_CODES ->
                   forall i, 0 <= i < 19 -> ls1 i <= 7).
  { intros _ i Hi.
    destruct (inf_order_covers i Hi) as (h & Hh19 & E).
    rewrite <- E. exact (proj2 (Hg7 h Hh19)). }
  unfold inf_table.
  assert (HLB : GtItTotal.LensBounded ls1 19) by (intros i _; apply Hls1).
  match goal with
  | |- context [it_model CT_CODES ?l ?cs ?rt ?t0] =>
      remember (it_model CT_CODES l cs rt t0) as R1 eqn:EI1
  end.
  destruct R1 as [o1|].
  2:{ exfalso.
      assert (Hc19 : 0 <= 19) by lia.
      exact (it_model_total _ _ _ _ _ Hc19 HLB (eq_sym EI1)). }
  cbv beta iota zeta.
  destruct (negb (Z.eqb (o_ret o1) 0)) eqn:Er1.
  { cbn [arm_ok]. split.
    - unfold q_pos. bsimp. repeat split; lia.
    - apply rank2_lt' with (m := M_LENLENS) (m' := M_BAD);
        [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
  apply Bool.negb_false_iff in Er1. apply Z.eqb_eq in Er1.
  assert (HWFC : it_wf CT_CODES ls1 19 7).
  { split; [lia|]. split; [intros i _; apply Hls1|].
    split; [unfold MAXBITS; lia|].
    left; split; [reflexivity | lia]. }
  eapply (arm_ok_mono _ q).
  2:{ apply reach_CODELENS.
      - bsimp; reflexivity.
      - (* CoreFacts at the constructed tail *)
        split. { unfold q_pos. ksimp. repeat split; lia. }
        split. { ksimp. lia. }
        split. { intros j. ksimp. rewrite Ein. exact (Hbytes j). }
        split. { intros j. ksimp. exact (Hwinb j). }
        split. { ksimp. lia. }
        split. { ksimp. lia. }
        split. { ksimp. exact Hsane. }
        split. { ksimp. lia. }
        split. { ksimp. lia. }
        split. { ksimp. exact Ehold. }
        ksimp.
        exact (dyn_amb_wb Hdyn CT_CODES ls1 19 7
                 (t_codes (s_tab (q_st q))) 0 o1
                 Hamb HWFC Hguard (eq_sym EI1)).
      - ksimp. exact Hls1.
      - ksimp. lia.
      - ksimp. lia.
      - ksimp. lia.
      - (* TblSide at the freshly built CODES table *)
        exact (dyn_codes_tblside Hdyn ls1 19 7
                 (t_codes (s_tab (q_st q))) o1 Hamb HWFC (eq_sym EI1)
                 Er1). }
  apply rank2_le' with (m := M_LENLENS) (m' := M_CODELENS);
    [exact Hm | bsimp; reflexivity |].
  cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
Qed.

(** [inf_TABLE] with the LENLENS tail discharged.  The b_nlen/b_ndist
    bounds at the tail are CONSTRUCTED here ([bits_of_range 5] on the two
    5-bit reads), not carried — TABLE is where they are born. *)
Lemma reach_TABLE :
  forall c q,
    q_mode q = M_TABLE ->
    CoreFacts q ->
    lens_ok (b_lens (s_bld (q_st q))) ->
    arm_ok q (inf_TABLE c q).
Proof.
  intros c q Hm Hcore Hlens.
  pose proof Hcore as (Hp & H39 & Hbytes & Hwinb & Hwnext & Hwhave & Hsane
                       & Hh24 & Hl24 & Hhold & Hamb).
  pose proof Hp as (Hh & Hb & Hl).
  unfold inf_TABLE.
  destruct (inf_nb 14 (q_br q)) as [b|b] eqn:Enb; [|exact I].
  pose proof (inf_nb_ok _ _ _ Enb) as E14.
  pose proof (inf_nb_env 14 (q_br q) b ltac:(lia) Hhold Hb
                (fun j => proj1 (Hbytes j)) H39 Enb) as (Nin & Nhold & N39).
  pose proof (inf_nb_have_mono _ _ _ Enb) as NM.
  apply inf_nb_bud in Enb as (E1 & E2 & E3). specialize (E3 Hh).
  pose proof (bits_of_range 5 b ltac:(lia)) as B1.
  change (2 ^ 5) with 32 in B1.
  pose proof (bits_of_range 5 (br_dropbits 5 b) ltac:(lia)) as B2.
  change (2 ^ 5) with 32 in B2.
  cbv zeta.
  destruct (Z.ltb 286 (br_bits_of 5 b + 257)
            || Z.ltb 30 (br_bits_of 5 (br_dropbits 5 b) + 1)).
  { cbn [arm_ok]. split.
    - unfold q_pos. bsimp. repeat split; lia.
    - apply rank2_lt' with (m := M_TABLE) (m' := M_BAD);
        [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
  eapply (arm_ok_mono _ q).
  2:{ apply reach_LENLENS.
      - bsimp; reflexivity.
      - (* CoreFacts at the constructed tail *)
        split. { unfold q_pos. bsimp. repeat split; lia. }
        split. { bsimp. lia. }
        split. { intros j. bsimp. rewrite Nin. exact (Hbytes j). }
        split. { intros j. bsimp. exact (Hwinb j). }
        split. { bsimp. lia. }
        split. { bsimp. lia. }
        split. { ksimp. exact Hsane. }
        split. { bsimp. lia. }
        split. { bsimp. lia. }
        split.
        { exact (dropbits_hold_nonneg 4 (br_dropbits 5 (br_dropbits 5 b))
                   (dropbits_hold_nonneg 5 (br_dropbits 5 b)
                      (dropbits_hold_nonneg 5 b Nhold))). }
        ksimp. exact Hamb.
      - ksimp. exact Hlens.
      - ksimp. intros h Hh0. lia.
      - ksimp. lia.
      - ksimp. lia.
      - ksimp. lia. }
  apply rank2_le' with (m := M_TABLE) (m' := M_LENLENS);
    [exact Hm | bsimp; reflexivity |].
  cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
Qed.

(** ** The deliverable: [step_ok] at every reachable state, ONE residual
    ([DynTblOk] — see its header).  The 29 non-TABLE-chain modes route
    through [step_ok_reachable], whose two carried callee obligations are
    vacuous off the chain (congruence on the mode); TABLE / LENLENS /
    CODELENS take the discharged arms above. *)
Theorem step_ok_reach :
  forall c q, ReachSt q -> step_ok c q.
Proof.
  intros c q HR.
  pose proof HR as (Hcore & Hmode).
  pose proof (core_of_reach q Hcore) as HCF.
  pose proof (rc_lens q Hcore) as Hlens.
  pose proof (rc_bhave q Hcore) as Hbh.
  pose proof (rm_bldrng q Hmode) as Hbld.
  pose proof (rm_tblCL q Hmode) as HtblCL.
  pose proof (rm_lens7 q Hmode) as Hl7.
  destruct (q_mode q) eqn:Hm;
    try (apply (step_ok_reachable c q HR);
         [ intros [F|F]; exfalso; congruence
         | intros F; exfalso; congruence ]).
  - (* M_TABLE *)
    unfold step_ok, inf_step. rewrite Hm. cbv beta iota.
    exact (reach_TABLE c q Hm HCF Hlens).
  - (* M_LENLENS *)
    unfold step_ok, inf_step. rewrite Hm. cbv beta iota.
    destruct (Hbld (or_introl eq_refl)) as [Hnl Hnd].
    exact (reach_LENLENS c q Hm HCF Hlens (Hl7 eq_refl) Hbh Hnl Hnd).
  - (* M_CODELENS *)
    unfold step_ok, inf_step. rewrite Hm. cbv beta iota.
    destruct (Hbld (or_intror eq_refl)) as [Hnl Hnd].
    exact (reach_CODELENS c q Hm HCF Hlens Hbh Hnl Hnd (HtblCL eq_refl)).
Qed.

End Knot.


(** ** [rm_back] support (A1.2) *)
Lemma uback_set_back : forall st v, u_back (s_cur (set_back st v)) = v.
Proof. reflexivity. Qed.
Lemma uback_set_length : forall st v,
  u_back (s_cur (set_length st v)) = u_back (s_cur st).
Proof. reflexivity. Qed.
Lemma uback_set_offset : forall st v,
  u_back (s_cur (set_offset st v)) = u_back (s_cur st).
Proof. reflexivity. Qed.
Lemma uback_set_extra : forall st v,
  u_back (s_cur (set_extra st v)) = u_back (s_cur st).
Proof. reflexivity. Qed.
Lemma uback_set_was : forall st v,
  u_back (s_cur (set_was st v)) = u_back (s_cur st).
Proof. reflexivity. Qed.
Lemma uback_set_mode : forall st m,
  u_back (s_cur (set_mode st m)) = u_back (s_cur st).
Proof. reflexivity. Qed.

(** Reduce a [u_back] read through the cursor setters and the [q_st] wrappers. *)
#[local] Ltac ubk :=
  cbn [q_st qset_st qset_br qset_ob qmode qbad];
  repeat first [ rewrite uback_set_back | rewrite uback_set_length
               | rewrite uback_set_offset | rewrite uback_set_extra
               | rewrite uback_set_was | rewrite uback_set_mode ].

(** The two-level decode adds at most two table entries' [c_bits] to [back]. *)
Lemma inf_decode_nb_le30 :
  forall sub t rb b h b2 nb,
    (forall i, c_bits (t i) <= 15) ->
    inf_decode sub t rb b = DecOk h b2 nb ->
    nb <= 30.
Proof.
  intros sub t rb b h b2 nb Ht H. unfold inf_decode in H.
  destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Ef; [|discriminate|discriminate].
  destruct (inf_fetch_go_entry _ _ _ _ _ _ Ef) as (i0 & ->).
  destruct (sub (t i0)).
  - destruct (inf_fetch2 t (t i0) b0) as [h1 b1|b1|] eqn:Ef2;
      [|discriminate|discriminate].
    destruct (inf_fetch2_go_entry _ _ _ _ _ _ Ef2) as (i1 & ->).
    injection H as _ _ Hnb. subst nb.
    pose proof (Ht i0). pose proof (Ht i1). lia.
  - injection H as _ _ Hnb. subst nb. pose proof (Ht i0). lia.
Qed.


(** ** (D') support (a5 665p; fork): the decode / NEEDBITS / loop bit bounds and the TblPD transport
    the three new [ReachMode] rows consume in StepPres.  The five decode lemmas are cand6-prep/PrbDecodeLe14.v 
    verbatim (a build machine an earlier development run GREEN); the rest is new here (probe PrbSupportC6.v). *)
(* ===== transplanted verbatim from cand6-prep/PrbDecodeLe14.v ===== *)
(** Root fetch from an arbitrary bit count. *)
Lemma fetch_root_le : forall t rb b h b', TblPD t rb -> inf_fetch t rb b = FetchOk h b' ->
  (exists i, 0 <= i < 2 ^ rb /\ t i = h) /\ c_bits h <= br_bits b' /\
  (br_bits b' = br_bits b \/ br_bits b' < c_bits h + 8).
Proof.
  intros t rb b h b' Hpd Hf.
  destruct (Z.leb (c_bits (t (br_bits_of rb b))) (br_bits b)) eqn:Hle.
  - unfold inf_fetch in Hf. cbn [inf_fetch_go] in Hf. cbv zeta in Hf. rewrite Hle in Hf.
    injection Hf as Hh Hb. subst h b'.
    split; [exists (br_bits_of rb b); split; [apply (cbt_idx_range t rb Hpd) | reflexivity] |].
    split; [apply Z.leb_le, Hle |]. left; reflexivity.
  - apply Z.leb_gt in Hle.
    assert (Hinv : FInv t rb b) by (unfold FInv; right; lia).
    destruct (fetch_go_lt8 t rb Hpd _ b h b' Hinv Hf) as (Hex & Hlo & Hhi).
    split; [exact Hex |]. split; [exact Hlo |]. right; exact Hhi.
Qed.

(** Second-level fetch from an arbitrary bit count (>= the root entry's width). *)
Lemma fetch2_root_le : forall t rb lst b h b', TblPD t rb -> (exists i, 0 <= i < 2 ^ rb /\ t i = lst) ->
  Z.land (c_op lst) 240 = 0 -> 0 <= c_op lst -> (c_op lst = 0 -> 0 <= c_bits (t (c_val lst))) ->
  c_bits lst <= br_bits b -> inf_fetch2 t lst b = FetchOk h b' ->
  c_bits lst + c_bits h <= br_bits b' /\
  ((br_bits b' = br_bits b /\ 0 <= c_bits h) \/ br_bits b' < c_bits lst + c_bits h + 8).
Proof.
  intros t rb lst b h b' Hpd Hroot H240 Hnn H0 Hcb Hf.
  pose proof (cbt_entry_nonneg t rb lst Hpd Hroot H240 Hnn H0 b) as Hnn1.
  destruct (Z.leb (c_bits lst + c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst))))
                  (br_bits b)) eqn:Hle.
  - unfold inf_fetch2 in Hf. cbn [inf_fetch2_go] in Hf. cbv zeta in Hf. rewrite Hle in Hf.
    injection Hf as Hh Hb. subst h b'. apply Z.leb_le in Hle.
    split; [exact Hle |]. left; split; [reflexivity | exact Hnn1].
  - apply Z.leb_gt in Hle.
    assert (Hinv : F2Inv t lst b) by (unfold F2Inv; split; [exact Hcb | right; lia]).
    destruct (fetch2_go_lt8 t rb lst Hpd Hroot H240 Hnn H0 _ b h b' Hinv Hf) as (Hlo & Hhi).
    split; [exact Hlo |]. right; exact Hhi.
Qed.

(** THE decode bound: post <= max (pre - 1) 7, for any entry bit count. *)
Lemma inf_decode_le : forall sub t rb b h b' nb, TblPD t rb -> SubGuardGen sub t rb ->
  inf_decode sub t rb b = DecOk h b' nb -> br_bits b' <= br_bits b - 1 \/ br_bits b' < 8.
Proof.
  intros sub t rb b h b' nb Hpd Hg Hd. unfold inf_decode in Hd.
  destruct (inf_fetch t rb b) as [h0 b0 | b0 |] eqn:Hf; try discriminate.
  destruct (fetch_root_le t rb b h0 b0 Hpd Hf) as ((i & Hi & Hti) & Hlo0 & Hc0).
  assert (Hw0 : 1 <= c_bits h0).
  { destruct Hpd as (_ & _ & Hw & _). specialize (Hw i Hi). rewrite Hti in Hw. lia. }
  destruct (sub h0) eqn:Hs.
  - destruct (inf_fetch2 t h0 b0) as [h1 b1 | b1 |] eqn:Hf2; try discriminate.
    injection Hd as Hh Hb Hn. subst b' nb.
    assert (Hs' : sub (t i) = true) by (rewrite Hti; exact Hs).
    destruct (Hg i Hi Hs') as (H240 & Hnn & H0). rewrite Hti in H240, Hnn, H0.
    destruct (fetch2_root_le t rb h0 b0 h1 b1 Hpd (ex_intro _ i (conj Hi Hti)) H240 Hnn H0 Hlo0 Hf2)
      as (Hlo1 & Hc1).
    rewrite !br_dropbits_bits. lia.
  - injection Hd as Hh Hb Hn. subst b' nb. rewrite br_dropbits_bits. lia.
Qed.

(** The (D') row shape: entry <= 14 gives post <= 13 (so <= 14). *)
Corollary inf_decode_le14 : forall sub t rb b h b' nb, TblPD t rb -> SubGuardGen sub t rb ->
  br_bits b <= 14 -> inf_decode sub t rb b = DecOk h b' nb -> br_bits b' <= 13.
Proof. intros sub t rb b h b' nb Hpd Hg Hb Hd. destruct (inf_decode_le sub t rb b h b' nb Hpd Hg Hd) as [Hx|Hx]; lia. Qed.

Corollary inf_decode_le14_ptr : forall sub t rb b h b' nb, TblPD t rb -> SubGuardPtr sub t rb ->
  br_bits b <= 14 -> inf_decode sub t rb b = DecOk h b' nb -> br_bits b' <= 14.
Proof. intros sub t rb b h b' nb Hpd Hg Hb Hd. pose proof (inf_decode_le14 sub t rb b h b' nb Hpd (subguard_ptr_gen _ _ _ Hg) Hb Hd); lia. Qed.
(* ===== cand13: transplanted verbatim from tiematch/PrbOff1Decode.v (a build machine an earlier development run rc 0; PA Closed) ===== *)
(** (A) root fetch: the entry is [t (br_bits_of rb bk)] for the reader [bk] of the successful trip *)
Lemma inf_fetch_go_entry_idx :
  forall f t nb b h b', inf_fetch_go f t nb b = FetchOk h b' ->
    exists bk, h = t (br_bits_of nb bk).
Proof.
  induction f as [|f IH]; intros t nb b h b' H; cbn [inf_fetch_go] in H; [discriminate|].
  destruct (Z.leb (c_bits (t (br_bits_of nb b))) (br_bits b)).
  - injection H as <- _. exists b. reflexivity.
  - destruct (br_pullbyte b) as [b1|]; [exact (IH _ _ _ _ _ H) | discriminate].
Qed.

(** (A) sub fetch: the entry is [t (c_val lst + shiftr (br_bits_of (c_bits lst + c_op lst) bk) (c_bits lst))] *)
Lemma inf_fetch2_go_entry_idx :
  forall f t lst b h b', inf_fetch2_go f t lst b = FetchOk h b' ->
    exists bk, h = t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) bk) (c_bits lst)).
Proof.
  induction f as [|f IH]; intros t lst b h b' H; cbn [inf_fetch2_go] in H; [discriminate|].
  match type of H with
  | context[Z.leb ?a ?bb] => destruct (Z.leb a bb)
  end.
  - injection H as <- _. exists b. reflexivity.
  - destruct (br_pullbyte b) as [b1|]; [exact (IH _ _ _ _ _ H) | discriminate].
Qed.

(** the sub index lies inside the pointer's window [0, 2^op) *)
Lemma sub_index_range :
  forall cb op x, 0 <= cb -> 0 <= op -> 0 <= x < 2 ^ (cb + op) ->
    0 <= Z.shiftr x cb < 2 ^ op.
Proof.
  intros cb op x Hcb Hop Hx.
  rewrite Z.shiftr_div_pow2 by exact Hcb.
  assert (Hp : 0 < 2 ^ cb) by (apply Z.pow_pos_nonneg; lia).
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; [exact Hp|].
    rewrite <- Z.pow_add_r by lia. lia.
Qed.

(** (B) a successful dist decode returns a LEAF entry *)
Lemma inf_decode_dist_leaf240 :
  forall t rb b h b2 nb,
    0 <= rb ->
    (forall i, 0 <= c_bits (t i)) ->
    (forall i, 0 <= i < 2 ^ rb -> Z.land (c_op (t i)) 240 = 0 -> 0 < c_op (t i)) ->
    DistSubLeaf t rb ->
    inf_decode sub_dist t rb b = DecOk h b2 nb ->
    Z.land (c_op h) 240 <> 0.
Proof.
  intros t rb b h b2 nb Hrb Hbits Hptr Hds H.
  unfold inf_decode in H.
  destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Ef; [|discriminate|discriminate].
  unfold inf_fetch in Ef.
  destruct (inf_fetch_go_entry_idx _ _ _ _ _ _ Ef) as (bk & Eh0).
  destruct (sub_dist h0) eqn:Es; cbv iota zeta in H.
  - (* level 2: h0 is a pointer, h is one of its sub-table entries *)
    destruct (inf_fetch2 t h0 b0) as [h1 b1|b1|] eqn:Ef2; cbv iota zeta in H; [|discriminate|discriminate].
    injection H as <- _ _.
    unfold inf_fetch2 in Ef2.
    destruct (inf_fetch2_go_entry_idx _ _ _ _ _ _ Ef2) as (bk2 & Eh1).
    unfold sub_dist in Es. apply Z.eqb_eq in Es.
    pose proof (bits_of_range rb bk Hrb) as Hi0.
    set (i0 := br_bits_of rb bk) in *.
    rewrite Eh0 in Es.
    pose proof (Hptr i0 Hi0 Es) as Hop.
    pose proof (Hbits i0) as Hcb.
    pose proof (bits_of_range (c_bits (t i0) + c_op (t i0)) bk2 ltac:(lia)) as Hx.
    pose proof (sub_index_range (c_bits (t i0)) (c_op (t i0)) _ Hcb ltac:(lia) Hx) as Hj.
    rewrite Eh1, Eh0.
    exact (Hds i0 Hi0 Es Hop _ Hj).
  - (* root leaf: sub_dist h0 = false is exactly land 240 <> 0 *)
    injection H as <- _ _.
    unfold sub_dist in Es. apply Z.eqb_neq in Es. exact Es.
Qed.

(** (C) the positive value: LeafPosT (rc_leafpos, shifted / distfix) at the decoded entry on the non-BAD branch *)
Lemma dist_val_pos :
  forall t rb b h b2 nb,
    LeafPosT t ->
    (forall i, 0 <= c_bits (t i)) ->
    inf_decode sub_dist t rb b = DecOk h b2 nb ->
    Z.land (c_op h) 240 <> 0 -> Z.land (c_op h) 64 = 0 ->
    1 <= c_val h.
Proof.
  intros t rb b h b2 nb HL Hbits H H240 H64.
  destruct (inf_decode_ok_facts _ _ _ _ _ _ _ Hbits H) as ((i & ->) & _).
  exact (HL i H240 H64).
Qed.

(** the DIST arm's supply, assembled: what pres_DIST hands to pres_DISTEXT's [1 <= u_offset] premise *)
Corollary dist_offset_pos :
  forall t rb b h b2 nb,
    0 <= rb ->
    LeafPosT t ->
    (forall i, 0 <= c_bits (t i)) ->
    (forall i, 0 <= i < 2 ^ rb -> Z.land (c_op (t i)) 240 = 0 -> 0 < c_op (t i)) ->
    DistSubLeaf t rb ->
    inf_decode sub_dist t rb b = DecOk h b2 nb ->
    Z.land (c_op h) 64 = 0 ->
    1 <= c_val h.
Proof.
  intros t rb b h b2 nb Hrb HL Hbits Hptr Hds H H64.
  exact (dist_val_pos t rb b h b2 nb HL Hbits H (inf_decode_dist_leaf240 t rb b h b2 nb Hrb Hbits Hptr Hds H) H64).
Qed.
(* ===== end of transplant ===== *)

(** [op & 0xf0 = 0] clears bits 4 and 6 — a pointer shape is never a leaf shape. *)
Lemma land240_16 : forall op, Z.land op 240 = 0 -> Z.land op 16 = 0.
Proof. intros op H. replace 16 with (Z.land 240 16) by reflexivity. rewrite Z.land_assoc, H. reflexivity. Qed.
Lemma land240_64 : forall op, Z.land op 240 = 0 -> Z.land op 64 = 0.
Proof. intros op H. replace 64 with (Z.land 240 64) by reflexivity. rewrite Z.land_assoc, H. reflexivity. Qed.

(** NEEDBITS(n) from ANY count: no pull keeps the count, a pull ends below n + 8. *)
Lemma inf_nb_go_le : forall f n b b', inf_nb_go f n b = NBOk b' ->
  br_bits b' = br_bits b \/ br_bits b' < n + 8.
Proof.
  induction f as [|f IH]; intros n b b' H; cbn [inf_nb_go] in H.
  - destruct (Z.ltb (br_bits b) n); [discriminate|]. injection H as <-. left; reflexivity.
  - destruct (Z.ltb (br_bits b) n) eqn:Hlt.
    + destruct (br_pullbyte b) as [b1|] eqn:Hp; [|discriminate].
      apply Z.ltb_lt in Hlt.
      destruct (br_pullbyte_step b b1 Hp) as (_ & _ & Hb1 & _).
      destruct (IH n b1 b' H) as [E|E]; right; lia.
    + injection H as <-. left; reflexivity.
Qed.
Lemma inf_nb_ok_le : forall n b b', inf_nb n b = NBOk b' -> br_bits b' = br_bits b \/ br_bits b' < n + 8.
Proof. intros n b b' H. exact (inf_nb_go_le _ _ _ _ H). Qed.

(** TblPD reads a table only at [0, 2^rb) and inside each pointer's window: transport along agreement there. *)
Lemma tblpd_ext : forall t t' rb,
  TblPD t rb ->
  (forall i, 0 <= i < 2 ^ rb -> t' i = t i) ->
  (forall i, 0 <= i < 2 ^ rb -> Z.land (c_op (t i)) 240 = 0 -> c_op (t i) <> 0 ->
     forall j, 0 <= j < 2 ^ c_op (t i) -> t' (c_val (t i) + j) = t (c_val (t i) + j)) ->
  TblPD t' rb.
Proof.
  intros t t' rb (Hrb & Hpd & Hw & Hsub) Hroot Hwin.
  split; [exact Hrb|]. split.
  - intros i j k Hi Hj Hk Hle Hm.
    rewrite (Hroot i Hi) in Hle. rewrite (Hroot i Hi), (Hroot j Hj).
    exact (Hpd i j k Hi Hj Hk Hle Hm).
  - split.
    + intros i Hi. rewrite (Hroot i Hi). exact (Hw i Hi).
    + intros i Hi H240 Hnz. rewrite (Hroot i Hi) in H240, Hnz. rewrite (Hroot i Hi).
      destruct (Hsub i Hi H240 Hnz) as (Hspd & Hsw).
      pose proof (Hwin i Hi H240 Hnz) as Hw'.
      split.
      * intros a b k Ha Hb Hk Hle Hm. cbv beta in Hle |- *.
        rewrite (Hw' a Ha) in Hle. rewrite (Hw' a Ha), (Hw' b Hb).
        exact (Hspd a b k Ha Hb Hk Hle Hm).
      * intros j Hj. cbv beta. rewrite (Hw' j Hj). exact (Hsw j Hj).
Qed.

(** The CODELENS loop keeps [bits <= 14] over a TblPD codes table: root fetch, NEEDBITS(bits + {2,3,7}), drops. *)
Lemma cl_step_bits14 : forall t nb tot s,
  TblPD t nb -> br_bits (cl_br s) <= 14 ->
  match cl_step t nb tot s with
  | ClCont s' | ClDone s' | ClBad s' _ => br_bits (cl_br s') <= 14
  | _ => True
  end.
Proof.
  intros t nb tot s Hpd Hb. unfold cl_step.
  destruct (Z.leb tot (cl_have s)); cbv beta iota; [exact Hb|].
  destruct (inf_fetch t nb (cl_br s)) as [h b|b|] eqn:Ef; cbv beta iota; [|exact I|exact I].
  destruct (fetch_root_le t nb (cl_br s) h b Hpd Ef) as ((i & Hi & Hti) & Hlo & Hc).
  assert (Hw : 1 <= c_bits h).
  { destruct Hpd as (_ & _ & Hw & _). specialize (Hw i Hi). rewrite Hti in Hw. lia. }
  destruct (Z.ltb (c_val h) 16).
  { cbn [cl_br]. rewrite br_dropbits_bits. lia. }
  destruct (inf_nb (if Z.eqb (c_val h) 16 then c_bits h + 2
                    else if Z.eqb (c_val h) 17 then c_bits h + 3
                    else c_bits h + 7) b) as [b'|b'] eqn:Enb; [|exact I].
  apply inf_nb_ok_le in Enb.
  (* the NEEDBITS count is at most c_bits h + 7, whichever repeat code fired *)
  assert (Hneed : (if Z.eqb (c_val h) 16 then c_bits h + 2
                   else if Z.eqb (c_val h) 17 then c_bits h + 3
                   else c_bits h + 7) <= c_bits h + 7)
    by (destruct (Z.eqb (c_val h) 16); [lia|]; destruct (Z.eqb (c_val h) 17); lia).
  assert (Hb' : br_bits b' <= 14 \/ br_bits b' < c_bits h + 15) by lia.
  clear Enb Hneed.
  cbv zeta.
  destruct (Z.eqb (c_val h) 16); cbv beta iota.
  { destruct (Z.eqb (cl_have s) 0); cbv beta iota; [cbn [cl_br]; rewrite br_dropbits_bits; lia|].
    destruct (Z.ltb tot (cl_have s + (3 + br_bits_of 2 (br_dropbits (c_bits h) b'))));
      cbv beta iota; cbn [cl_br]; rewrite !br_dropbits_bits; lia. }
  destruct (Z.eqb (c_val h) 17); cbv beta iota.
  { destruct (Z.ltb tot (cl_have s + (3 + br_bits_of 3 (br_dropbits (c_bits h) b'))));
      cbv beta iota; cbn [cl_br]; rewrite !br_dropbits_bits; lia. }
  destruct (Z.ltb tot (cl_have s + (11 + br_bits_of 7 (br_dropbits (c_bits h) b'))));
    cbv beta iota; cbn [cl_br]; rewrite !br_dropbits_bits; lia.
Qed.

Lemma cl_loop_bits14 : forall m t nb tot s r,
  TblPD t nb -> br_bits (cl_br s) <= 14 ->
  cl_loop m t nb tot s = Some r ->
  match r with
  | ClDone s' | ClBad s' _ => br_bits (cl_br s') <= 14
  | _ => True
  end.
Proof.
  induction m as [|m IH]; intros t nb tot s r Hpd Hb H; [cbn [cl_loop] in H; discriminate|].
  rewrite cl_loop_S in H.
  pose proof (cl_step_bits14 t nb tot s Hpd Hb) as HS.
  destruct (cl_step t nb tot s) as [s1|s1|s1 m1|s1|] eqn:ES.
  - exact (IH t nb tot s1 r Hpd HS H).
  - injection H as H; subst r. exact HS.
  - injection H as H; subst r. exact HS.
  - injection H as H; subst r. exact I.
  - injection H as H; subst r. exact I.
Qed.

(** Exit shape for the P3R leaves (P3RCodelens.v :263 has [EqL_br : q_br qL = cl_br s1] with
    [s1] the [ClDone] exit of the CODELENS loop; fork an earlier development run): the loop leaves at most 14 bits GIVEN the codes table's
    [TblPD] and the ENTRY bound -- both are [ReachMode] rows at the entry state ([rm_tblpdCL], [rm_bits14]); neither is a
    consequence of the P3R pack RL, so a caller without [ReachMode q] owes them as premises.  [cl_loop_bits14] covers the
    [ClBad] exit with the same hypotheses; StepPres.[cl_loop_leave_le14] covers [ClLeave]. *)
Corollary codelens_exit_bits14 : forall m t nb tot s s',
  TblPD t nb -> br_bits (cl_br s) <= 14 -> cl_loop m t nb tot s = Some (ClDone s') -> br_bits (cl_br s') <= 14.
Proof. intros m t nb tot s s' Hpd Hb H. exact (cl_loop_bits14 m t nb tot s (ClDone s') Hpd Hb H). Qed.

(** The LENLENS loop keeps [bits <= 14] (NEEDBITS(3) + DROPBITS(3) per code length). *)
Lemma ll_go_bits14 : forall f ncode have lens b,
  br_bits b <= 14 ->
  match ll_go f ncode have lens b with
  | LlOk _ _ b' => br_bits b' <= 14
  | LlLeave _ _ _ => True
  end.
Proof.
  induction f as [|f IH]; intros ncode have lens b Hb; cbn [ll_go]; [exact Hb|].
  destruct (Z.ltb have ncode); [|exact Hb].
  destruct (inf_nb 3 b) as [b'|b'] eqn:Enb; [|exact I].
  apply inf_nb_ok_le in Enb.
  apply IH. rewrite br_dropbits_bits. lia.
Qed.

(** The installed CODES view (LENLENS: [codes_wb cs 0 (o_tbl o)] read at offset 0) inherits the build's TblPD;
    the window indices are nonnegative by the installed array's own [amb_ok]. *)
Lemma tblpd_codes_wb0 : forall cs o rb,
  TblPD (o_tbl o) rb ->
  amb_ok (codes_wb cs 0 (o_tbl o)) ->
  TblPD (fun i => codes_wb cs 0 (o_tbl o) (0 + i)) rb.
Proof.
  intros cs o rb Hpd Hamb.
  apply (tblpd_ext (o_tbl o) _ rb Hpd).
  - intros i Hi. cbv beta. unfold codes_wb.
    destruct (Z.leb 0 (0 + i)) eqn:E; [replace (0 + i - 0) with i by lia; reflexivity | apply Z.leb_gt in E; lia].
  - intros i Hi H240 Hnz j Hj. cbv beta.
    assert (Hv : 0 <= c_val (o_tbl o i)).
    { destruct (Hamb (0 + i)) as (_ & Hv & _). unfold codes_wb in Hv.
      destruct (Z.leb 0 (0 + i)) eqn:E; cbv beta iota in Hv; [|apply Z.leb_gt in E; lia].
      replace (0 + i - 0) with i in Hv by lia. lia. }
    unfold codes_wb.
    destruct (Z.leb 0 (0 + (c_val (o_tbl o i) + j))) eqn:E;
      [replace (0 + (c_val (o_tbl o i) + j) - 0) with (c_val (o_tbl o i) + j) by lia; reflexivity
      | apply Z.leb_gt in E; lia].
Qed.

(** The two installed dynamic tables (CODELENS's [db_installed] view) carry TblPD: [it_tblpd_wf] on each build, transported
    through [codes_wb] by [it_covers_all]'s RootEntry (pointer windows sit inside the used extent; leaves are never pointers). *)
Lemma tblpd_installed_len : forall d q', db_ok d -> db_installed d q' ->
  TblPD (tbl_of (q_st q') (t_lencode (s_tab (q_st q')))) (t_lenbits (s_tab (q_st q'))).
Proof.
  intros d q' Hok Hin.
  pose proof Hok as (Hamb & Hwf1 & Hm1 & Hr1 & _).
  destruct (ItGSubCover.it_covers_all CT_LENS (db_lens d) (db_nlen d) 9 _ (db_o1 d)
              (or_introl eq_refl) Hwf1 Hm1 Hr1) as (Hcov & Hroot & _).
  pose proof Hwf1 as (Hc0 & Hlens & Hroot0 & Hty).
  assert (Hpd : TblPD (o_tbl (db_o1 d)) (o_bits (db_o1 d))).
  { apply (it_tblpd_wf CT_LENS (db_lens d) (db_nlen d) 9 (fun i => db_cs d (0 + i)) (db_o1 d));
      [lia | | lia | exact Hty | exact Hm1 | exact Hr1].
    intros i Hi. specialize (Hlens i Hi). unfold MAXBITS in Hlens. lia. }
  destruct Hin as (Hlc & Hlb & _ & _ & Hcs).
  rewrite Hlc, Hlb. unfold tbl_of. rewrite Hcs.
  apply (tblpd_ext (o_tbl (db_o1 d)) _ (o_bits (db_o1 d)) Hpd).
  - intros i Hi. cbv beta. unfold codes_wb.
    destruct (Z.leb (0 + o_used (db_o1 d)) (0 + i)) eqn:E1; [apply Z.leb_le in E1; lia|].
    destruct (Z.leb 0 (0 + i)) eqn:E2; [replace (0 + i - 0) with i by lia; reflexivity | apply Z.leb_gt in E2; lia].
  - intros i Hi H240 Hnz j Hj. cbv beta.
    destruct (Hroot i Hi) as [(Hleaf & _) | (_ & Hop & Hv & _ & Hvu)].
    + exfalso. destruct Hleaf as ([H0|[H16|H64]] & _);
        [exact (Hnz H0) | exact (H16 (land240_16 _ H240)) | exact (H64 (land240_64 _ H240))].
    + unfold codes_wb.
      destruct (Z.leb (0 + o_used (db_o1 d)) (0 + (c_val (o_tbl (db_o1 d) i) + j))) eqn:E1; [apply Z.leb_le in E1; lia|].
      destruct (Z.leb 0 (0 + (c_val (o_tbl (db_o1 d) i) + j))) eqn:E2;
        [replace (0 + (c_val (o_tbl (db_o1 d) i) + j) - 0) with (c_val (o_tbl (db_o1 d) i) + j) by lia; reflexivity
        | apply Z.leb_gt in E2; lia].
Qed.

Lemma tblpd_installed_dist : forall d q', db_ok d -> db_installed d q' ->
  TblPD (tbl_of (q_st q') (t_distcode (s_tab (q_st q')))) (t_distbits (s_tab (q_st q'))).
Proof.
  intros d q' Hok Hin.
  pose proof Hok as (Hamb & Hwf1 & Hm1 & Hr1 & Hwf2 & Hm2 & Hr2).
  destruct (ItGSubCover.it_covers_all CT_DISTS _ (db_ndist d) 6 _ (db_o2 d)
              (or_intror eq_refl) Hwf2 Hm2 Hr2) as (Hcov & Hroot & _).
  pose proof Hwf2 as (Hc0 & Hlens & Hroot0 & Hty).
  assert (Hpd : TblPD (o_tbl (db_o2 d)) (o_bits (db_o2 d))).
  { apply (it_tblpd_wf CT_DISTS (fun i => db_lens d (i + db_nlen d)) (db_ndist d) 6
             (fun i => codes_wb (db_cs d) 0 (o_tbl (db_o1 d)) ((0 + o_used (db_o1 d)) + i)) (db_o2 d));
      [lia | | lia | exact Hty | exact Hm2 | exact Hr2].
    intros i Hi. specialize (Hlens i Hi). unfold MAXBITS in Hlens. lia. }
  destruct Hin as (_ & _ & Hdc & Hdb & Hcs).
  rewrite Hdc, Hdb. unfold tbl_of. rewrite Hcs.
  apply (tblpd_ext (o_tbl (db_o2 d)) _ (o_bits (db_o2 d)) Hpd).
  - intros i Hi. cbv beta. unfold codes_wb.
    destruct (Z.leb (0 + o_used (db_o1 d)) (0 + o_used (db_o1 d) + i)) eqn:E1;
      [replace (0 + o_used (db_o1 d) + i - (0 + o_used (db_o1 d))) with i by lia; reflexivity
      | apply Z.leb_gt in E1; lia].
  - intros i Hi H240 Hnz j Hj. cbv beta.
    destruct (Hroot i Hi) as [(Hleaf & _) | (_ & Hop & Hv & _ & Hvu)].
    + exfalso. destruct Hleaf as ([H0|[H16|H64]] & _);
        [exact (Hnz H0) | exact (H16 (land240_16 _ H240)) | exact (H64 (land240_64 _ H240))].
    + unfold codes_wb.
      destruct (Z.leb (0 + o_used (db_o1 d)) (0 + o_used (db_o1 d) + (c_val (o_tbl (db_o2 d) i) + j))) eqn:E1;
        [replace (0 + o_used (db_o1 d) + (c_val (o_tbl (db_o2 d) i) + j) - (0 + o_used (db_o1 d)))
           with (c_val (o_tbl (db_o2 d) i) + j) by lia; reflexivity
        | apply Z.leb_gt in E1; lia].
Qed.

(* ==========================================================================
   (D'') support -- fork a5 WORDS: STOP #7 (TblWid sources), STOP #8 (the CODES root bound).
   ========================================================================== *)

(** [TblWid] reads [t] only at the root window and inside each pointer's window (same footprint as [tblpd_ext]). *)
Lemma tblwid_ext : forall t t' rb,
  TblWid t rb ->
  (forall i, 0 <= i < 2 ^ rb -> t' i = t i) ->
  (forall i, 0 <= i < 2 ^ rb -> Z.land (c_op (t i)) 240 = 0 -> c_op (t i) <> 0 ->
     forall j, 0 <= j < 2 ^ c_op (t i) -> t' (c_val (t i) + j) = t (c_val (t i) + j)) ->
  TblWid t' rb.
Proof.
  intros t t' rb Hw E1 E2 i Hi H240 Hnz.
  rewrite (E1 i Hi) in H240, Hnz |- *.
  destruct (Hw i Hi H240 Hnz) as (Hpos & Hs).
  split; [exact Hpos|]. intros j Hj. rewrite (E2 i Hi H240 Hnz j Hj). exact (Hs j Hj).
Qed.

(** the it_covers_all shape gives TblWid directly: a root pointer has width [root] and a positive [op], and every entry of its
    window is a SubEntry of width <= 15 - root. *)
Lemma tblwid_of_cover : forall ty o,
  2 ^ o_bits o <= o_used o ->
  (forall j, 0 <= j < 2 ^ o_bits o -> ItGSubCover.RootEntry ty (o_bits o) (o_used o) (o_tbl o j)) ->
  (forall i, 2 ^ o_bits o <= i < o_used o -> ItGSubCover.SubEntry ty (o_bits o) (o_tbl o i)) ->
  TblWid (o_tbl o) (o_bits o).
Proof.
  intros ty o Hcov Hroot Hsub i Hi H240 Hnz.
  destruct (Hroot i Hi) as [(Hleaf & _) | (Hb & Hop & Hv & Hlo & Hhi)].
  - exfalso. destruct Hleaf as ([H0|[H16|H64]] & _);
      [exact (Hnz H0) | exact (H16 (land240_16 _ H240)) | exact (H64 (land240_64 _ H240))].
  - split; [lia|]. intros j Hj.
    destruct (Hsub (c_val (o_tbl o i) + j) ltac:(lia)) as (_ & Hsb).
    lia.
Qed.

(** the dist table's root entries are never [op = 0] ([LeafShape]: [ty = CT_DISTS -> c_op e <> 0]; a pointer has [1 <= c_op]). *)
Lemma dist_root_nz_of_cover : forall o,
  (forall j, 0 <= j < 2 ^ o_bits o -> ItGSubCover.RootEntry CT_DISTS (o_bits o) (o_used o) (o_tbl o j)) ->
  forall i, 0 <= i < 2 ^ o_bits o -> c_op (o_tbl o i) <> 0.
Proof.
  intros o Hroot i Hi.
  destruct (Hroot i Hi) as [((_ & Hd & _) & _) | (_ & Hop & _)]; [exact (Hd eq_refl) | lia].
Qed.

(** The installed dynamic pair carries [TblWidSide] (STOP #7's establishment at the CODELENS install). *)
Lemma tblwid_installed : forall d q', db_ok d -> db_installed d q' -> TblWidSide q'.
Proof.
  intros d q' Hok Hin.
  pose proof Hok as (Hamb & Hwf1 & Hm1 & Hr1 & Hwf2 & Hm2 & Hr2).
  destruct (ItGSubCover.it_covers_all CT_LENS (db_lens d) (db_nlen d) 9 _ (db_o1 d)
              (or_introl eq_refl) Hwf1 Hm1 Hr1) as (Hcov1 & Hroot1 & Hsub1).
  destruct (ItGSubCover.it_covers_all CT_DISTS _ (db_ndist d) 6 _ (db_o2 d)
              (or_intror eq_refl) Hwf2 Hm2 Hr2) as (Hcov2 & Hroot2 & Hsub2).
  pose proof (tblwid_of_cover CT_LENS (db_o1 d) Hcov1 Hroot1 Hsub1) as Hw1.
  pose proof (tblwid_of_cover CT_DISTS (db_o2 d) Hcov2 Hroot2 Hsub2) as Hw2.
  pose proof (dist_root_nz_of_cover (db_o2 d) Hroot2) as Hnz2.
  destruct Hin as (Hlc & Hlb & Hdc & Hdb & Hcs).
  unfold TblWidSide. rewrite Hlc, Hlb, Hdc, Hdb. unfold tbl_of. rewrite Hcs.
  (* the two view equations, as in tblpd_installed_len/dist *)
  assert (V1 : forall i, 0 <= i < o_used (db_o1 d) ->
            codes_wb (codes_wb (db_cs d) 0 (o_tbl (db_o1 d))) (0 + o_used (db_o1 d)) (o_tbl (db_o2 d)) (0 + i)
            = o_tbl (db_o1 d) i).
  { intros i Hi. unfold codes_wb.
    destruct (Z.leb (0 + o_used (db_o1 d)) (0 + i)) eqn:E1; [apply Z.leb_le in E1; lia|].
    destruct (Z.leb 0 (0 + i)) eqn:E2; [replace (0 + i - 0) with i by lia; reflexivity | apply Z.leb_gt in E2; lia]. }
  assert (V2 : forall i, 0 <= i ->
            codes_wb (codes_wb (db_cs d) 0 (o_tbl (db_o1 d))) (0 + o_used (db_o1 d)) (o_tbl (db_o2 d))
              (0 + o_used (db_o1 d) + i)
            = o_tbl (db_o2 d) i).
  { intros i Hi. unfold codes_wb.
    destruct (Z.leb (0 + o_used (db_o1 d)) (0 + o_used (db_o1 d) + i)) eqn:E1;
      [replace (0 + o_used (db_o1 d) + i - (0 + o_used (db_o1 d))) with i by lia; reflexivity
      | apply Z.leb_gt in E1; lia]. }
  split; [|split].
  - apply (tblwid_ext (o_tbl (db_o1 d)) _ (o_bits (db_o1 d)) Hw1).
    + intros i Hi. cbv beta. apply V1. lia.
    + intros i Hi H240 Hnz j Hj. cbv beta.
      destruct (Hroot1 i Hi) as [(Hleaf & _) | (_ & Hop & Hv & Hlo & Hhi)].
      * exfalso. destruct Hleaf as ([H0|[H16|H64]] & _);
          [exact (Hnz H0) | exact (H16 (land240_16 _ H240)) | exact (H64 (land240_64 _ H240))].
      * apply V1. lia.
  - apply (tblwid_ext (o_tbl (db_o2 d)) _ (o_bits (db_o2 d)) Hw2).
    + intros i Hi. cbv beta. apply V2. lia.
    + intros i Hi H240 Hnz j Hj. cbv beta.
      destruct (Hroot2 i Hi) as [(Hleaf & _) | (_ & Hop & Hv & Hlo & Hhi)].
      * exfalso. destruct Hleaf as ([H0|[H16|H64]] & _);
          [exact (Hnz H0) | exact (H16 (land240_16 _ H240)) | exact (H64 (land240_64 _ H240))].
      * apply V2. lia.
  - intros i Hi. cbv beta. rewrite V2 by lia. exact (Hnz2 i Hi).
Qed.

(** TYPEDO's fixed tables: no entry has [0 < op < 16] (a level-2 pointer), so [TblWid] is vacuous; every distfix root entry has
    [op <> 0].  Decided by evaluation over the finite root windows (the leaf's [cbt_zseq] enumerator). *)
Definition nowid_b (t : ztbl) (rb : Z) : bool :=
  forallb (fun i => negb (Z.eqb (Z.land (c_op (t i)) 240) 0) || Z.eqb (c_op (t i)) 0) (cbt_zseq (2 ^ rb)).
Definition opnz_b (t : ztbl) (rb : Z) : bool :=
  forallb (fun i => negb (Z.eqb (c_op (t i)) 0)) (cbt_zseq (2 ^ rb)).
Lemma nowid_sound : forall t rb, nowid_b t rb = true -> TblWid t rb.
Proof.
  intros t rb H i Hi H240 Hnz.
  pose proof (proj1 (forallb_forall _ _) H i (cbt_zseq_in _ _ Hi)) as Hb. cbv beta in Hb.
  apply Bool.orb_true_iff in Hb. destruct Hb as [Hb|Hb].
  - apply Bool.negb_true_iff in Hb. apply Z.eqb_neq in Hb. contradiction.
  - apply Z.eqb_eq in Hb. contradiction.
Qed.
Lemma opnz_sound : forall t rb, opnz_b t rb = true -> forall i, 0 <= i < 2 ^ rb -> c_op (t i) <> 0.
Proof.
  intros t rb H i Hi.
  pose proof (proj1 (forallb_forall _ _) H i (cbt_zseq_in _ _ Hi)) as Hb. cbv beta in Hb.
  apply Bool.negb_true_iff in Hb. apply Z.eqb_neq in Hb. exact Hb.
Qed.
Lemma fix_tblwid : TblWid lenfix 9 /\ TblWid distfix 5 /\ (forall i, 0 <= i < 2 ^ 5 -> c_op (distfix i) <> 0).
Proof.
  split; [|split].
  - apply nowid_sound. vm_compute. reflexivity.
  - apply nowid_sound. vm_compute. reflexivity.
  - apply opnz_sound. vm_compute. reflexivity.
Qed.

(** ** cand13: [DistSubLeaf] — view transport, the cover shape, the CODELENS install, the fixed table *)

(** the contrapositives of [land240_16] / [land240_64] *)
Lemma land16_240 : forall op, Z.land op 16 <> 0 -> Z.land op 240 <> 0.
Proof. intros op H16 H240. exact (H16 (land240_16 op H240)). Qed.
Lemma land64_240 : forall op, Z.land op 64 <> 0 -> Z.land op 240 <> 0.
Proof. intros op H64 H240. exact (H64 (land240_64 op H240)). Qed.

(** the row reads the root window and every pointer's sub-window: agreement there transfers it (the [tblwid_ext] shape) *)
Lemma dsub_ext : forall t t' rb,
  DistSubLeaf t rb ->
  (forall i, 0 <= i < 2 ^ rb -> t' i = t i) ->
  (forall i, 0 <= i < 2 ^ rb -> Z.land (c_op (t i)) 240 = 0 -> c_op (t i) <> 0 ->
     forall j, 0 <= j < 2 ^ c_op (t i) -> t' (c_val (t i) + j) = t (c_val (t i) + j)) ->
  DistSubLeaf t' rb.
Proof.
  intros t t' rb Hd E1 E2 i Hi H240 Hpos.
  rewrite (E1 i Hi) in H240, Hpos |- *.
  intros j Hj. rewrite (E2 i Hi H240 ltac:(lia) j Hj). exact (Hd i Hi H240 Hpos j Hj).
Qed.

(** the it_covers_all shape gives [DistSubLeaf] for the DIST table: a pointer-shaped root entry is a [RootPtr] (its [RootLeaf]
    alternative contradicts [land 240 = 0]), its window [c_val, c_val + 2^op) lies in [2^root, used), and every entry there is a
    [SubEntry] whose [LeafShape] conj 1-2 for CT_DISTS exclude [op = 0], leaving [land 16 <> 0] or [land 64 <> 0] — a leaf. *)
Lemma dsub_of_cover : forall o,
  2 ^ o_bits o <= o_used o ->
  (forall j, 0 <= j < 2 ^ o_bits o -> ItGSubCover.RootEntry CT_DISTS (o_bits o) (o_used o) (o_tbl o j)) ->
  (forall i, 2 ^ o_bits o <= i < o_used o -> ItGSubCover.SubEntry CT_DISTS (o_bits o) (o_tbl o i)) ->
  DistSubLeaf (o_tbl o) (o_bits o).
Proof.
  intros o Hcov Hroot Hsub i Hi H240 Hpos j Hj.
  destruct (Hroot i Hi) as [(Hleaf & _) | (Hb & Hop & Hv & Hlo & Hhi)].
  - exfalso. destruct Hleaf as ([H0|[H16|H64]] & _);
      [lia | exact (H16 (land240_16 _ H240)) | exact (H64 (land240_64 _ H240))].
  - destruct (Hsub (c_val (o_tbl o i) + j) ltac:(lia)) as (Hls & _).
    destruct Hls as ([H0|[H16|H64]] & Hnz & _).
    + exfalso. exact (Hnz eq_refl H0).
    + exact (land16_240 _ H16).
    + exact (land64_240 _ H64).
Qed.

(** The installed dynamic pair carries [DistSubSide] (the CODELENS install; the same it_covers_all instance [tblwid_installed] uses). *)
Lemma dsub_installed : forall d q', db_ok d -> db_installed d q' -> DistSubSide q'.
Proof.
  intros d q' Hok Hin.
  pose proof Hok as (Hamb & Hwf1 & Hm1 & Hr1 & Hwf2 & Hm2 & Hr2).
  destruct (ItGSubCover.it_covers_all CT_DISTS _ (db_ndist d) 6 _ (db_o2 d)
              (or_intror eq_refl) Hwf2 Hm2 Hr2) as (Hcov2 & Hroot2 & Hsub2).
  pose proof (dsub_of_cover (db_o2 d) Hcov2 Hroot2 Hsub2) as Hd2.
  destruct Hin as (Hlc & Hlb & Hdc & Hdb & Hcs).
  unfold DistSubSide. rewrite Hdc, Hdb. unfold tbl_of. rewrite Hcs.
  assert (V2 : forall i, 0 <= i ->
            codes_wb (codes_wb (db_cs d) 0 (o_tbl (db_o1 d))) (0 + o_used (db_o1 d)) (o_tbl (db_o2 d))
              (0 + o_used (db_o1 d) + i)
            = o_tbl (db_o2 d) i).
  { intros i Hi. unfold codes_wb.
    destruct (Z.leb (0 + o_used (db_o1 d)) (0 + o_used (db_o1 d) + i)) eqn:E1;
      [replace (0 + o_used (db_o1 d) + i - (0 + o_used (db_o1 d))) with i by lia; reflexivity
      | apply Z.leb_gt in E1; lia]. }
  apply (dsub_ext (o_tbl (db_o2 d)) _ (o_bits (db_o2 d)) Hd2).
  - intros i Hi. cbv beta. apply V2. lia.
  - intros i Hi H240 Hnz j Hj. cbv beta.
    destruct (Hroot2 i Hi) as [(Hleaf & _) | (_ & Hop & Hv & Hlo & Hhi)].
    + exfalso. destruct Hleaf as ([H0|[H16|H64]] & _);
        [exact (Hnz H0) | exact (H16 (land240_16 _ H240)) | exact (H64 (land240_64 _ H240))].
    + apply V2. lia.
Qed.

(** TYPEDO's fixed dist table has no pointer entries, so [DistSubLeaf distfix 5] is vacuous — decided by computation
    (transplanted from tiematch/PrbOff1Decode.v ). *)
Lemma distfix_no_ptr : forall i, 0 <= i < 2 ^ 5 -> Z.land (c_op (distfix i)) 240 = 0 -> 0 < c_op (distfix i) -> False.
Proof.
  intros i Hi H240 Hop.
  assert (Hb : forallb (fun k => orb (negb (Z.eqb (Z.land (c_op (distfix (Z.of_nat k))) 240) 0)) (Z.leb (c_op (distfix (Z.of_nat k))) 0))
                       (seq 0 32) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb.
  specialize (Hb (Z.to_nat i) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in Hb by lia.
  rewrite H240 in Hb. cbn in Hb.
  apply Z.leb_le in Hb. lia.
Qed.
Corollary fix_dsub : DistSubLeaf distfix 5.
Proof. intros i Hi H240 Hop. exfalso. exact (distfix_no_ptr i Hi H240 Hop). Qed.

(** STOP #8's build-side fact: [inflate_table]'s root is [min root0 (max code length)] raised to the min code length, so with
    every length <= 7 and root0 = 7 the accepted CODES build has [o_bits <= 7]. *)
Lemma it_count_zero_above : forall n i lens cnt l,
  (forall k, 0 <= k < Z.of_nat n -> lens (i + k) < l) -> cnt l = 0 ->
  it_count n i lens cnt l = 0.
Proof.
  induction n as [|n IH]; intros i lens cnt l Hl Hc; cbn [it_count]; [exact Hc|].
  apply IH.
  - intros k Hk. replace (i + 1 + k) with (i + (k + 1)) by lia. apply Hl. rewrite Nat2Z.inj_succ in *. lia.
  - unfold zset. pose proof (Hl 0 ltac:(rewrite Nat2Z.inj_succ; lia)) as H0. replace (i + 0) with i in H0 by lia.
    destruct (Z.eqb_spec l (lens i)) as [E|E]; [lia | exact Hc].
Qed.

Lemma it_pre_root_le7 : forall ty lens codes root0 t0 c st,
  0 <= codes -> 1 <= root0 <= 7 ->
  (forall i, 0 <= i < codes -> lens i <= 7) ->
  it_pre ty lens codes root0 t0 = PreGo c st ->
  x_root c <= 7.
Proof.
  intros ty lens codes root0 t0 c st Hc Hr Hl H.
  unfold it_pre in H.
  set (cnt0 := it_count (Z.to_nat codes) 0 lens zzero) in *.
  set (mx := it_findmax 15%nat MAXBITS cnt0) in *.
  assert (Hmx7 : mx <= 7).
  { destruct (ItGTblSortWin.findmax_range 15%nat MAXBITS cnt0) as [Hz | (Hrng & Hnz)]; [fold mx in Hz; lia | fold mx in Hrng, Hnz].
    destruct (Z.le_gt_cases mx 7) as [Hle|Hgt]; [exact Hle|]. exfalso. apply Hnz.
    unfold cnt0. apply it_count_zero_above; [| reflexivity].
    intros k Hk. rewrite Z2Nat.id in Hk by lia. specialize (Hl (0 + k) ltac:(lia)). lia. }
  destruct (Z.eqb_spec mx 0) as [Hz|Hz]; [discriminate|].
  set (mn := it_findmin 16%nat 1 mx cnt0) in *.
  assert (Hmn : mn <= 7).
  { pose proof (ItGTblSortWin.findmin_le 16%nat 1 mx cnt0) as Hf. fold mn in Hf. lia. }
  destruct (it_kraft 15%nat 1 1 cnt0) as [lft|] eqn:Hk; [|discriminate].
  destruct (it_incomplete ty lft mx) eqn:Hi; [discriminate|].
  match type of H with
  | context[it_enough ?a ?b] => destruct (it_enough a b) eqn:He
  end; [discriminate|].
  injection H as Hc' _. subst c. cbn [x_root].
  destruct (Z.ltb (if Z.ltb mx root0 then mx else root0) mn); destruct (Z.ltb mx root0); lia.
Qed.

(* stated over abstract [codes] / [root0]: with the literals 19 / 7 in the statement the kernel's Qed check of the it_model case
   analysis took 504 s (lap an earlier development run, proof_check_time) -- the fuel [S (Z.to_nat 19)] invites conversion into it_loop; the
   abstract form checks like DynTblOkHolds.it_model_bits_range, and the 19/7 instance is an application. *)
Lemma codes_build_root7_gen : forall ty lens codes root0 t0 o,
  0 <= codes -> 1 <= root0 <= 7 ->
  (forall i, 0 <= i < codes -> lens i <= 7) ->
  it_model ty lens codes root0 t0 = Some o -> o_ret o = 0 -> o_bits o <= 7.
Proof.
  intros ty lens codes root0 t0 o Hc Hr Hl7 Hm Hret.
  unfold it_model in Hm.
  destruct (it_pre ty lens codes root0 t0) as [ | temp | | c st] eqn:Hpre.
  - injection Hm as <-. cbn [o_ret] in Hret. lia.
  - injection Hm as <-. cbn [o_bits]. lia.
  - injection Hm as <-. cbn [o_ret] in Hret. lia.
  - pose proof (it_pre_root_le7 ty lens codes root0 t0 c st Hc Hr Hl7 Hpre) as Hx.
    destruct (it_loop (S (Z.to_nat codes)) c st) as [[st'|st'|tt]|] eqn:Hlo; try discriminate Hm.
    + injection Hm as <-. cbn [o_bits]. exact Hx.
    + injection Hm as <-. cbn [o_ret] in Hret. lia.
Qed.

Lemma codes_build_root7 : forall lens t0 o,
  it_wf CT_CODES lens 19 7 -> (forall i, 0 <= i < 19 -> lens i <= 7) ->
  it_model CT_CODES lens 19 7 t0 = Some o -> o_ret o = 0 -> o_bits o <= 7.
Proof.
  intros lens t0 o _ Hl7 Hm Hret.
  exact (codes_build_root7_gen CT_CODES lens 19 7 t0 o ltac:(lia) ltac:(lia) Hl7 Hm Hret).
Qed.
