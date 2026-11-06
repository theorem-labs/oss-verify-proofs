(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibBswap.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymDriveLZ.
Unset Nia Cache.  (* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Ltac pin_reg_with HR r e tac :=
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
    let sr' := eval vm_compute in (sr_upd sr (ridx r) e) in
    let H := fresh "HRp" in
    assert (H : regs_ok E (sr_upd sr (ridx r) e) R) by (apply (regs_ok_pin E sr R r e HR); tac);
    change (sr_upd sr (ridx r) e) with sr' in H;
    clear HR; rename H into HR
  end.
Tactic Notation "pin_reg" constr(HR) constr(r) constr(e) "by" tactic3(tac) := pin_reg_with HR r e tac.

(* [comment removed for export] *)
Ltac kread_fact HK b k n H :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn b k n) in
    lazymatch r with
    | Some ?v =>
        let Hfl := fresh "Hfl" in
        assert (Hfl : flat E (SA b k) (Z.of_nat n));
        [ unfold flat, estart, elenZ; cbn [a_base a_off edenot Z.of_nat Pos.of_succ_nat Pos.succ]; ev_simpl E;
          rewrite_getr; try lia
        | pose proof (kread_rdn segs E M kn b k n v HK
                        ltac:(vm_cast_no_check (@eq_refl (option expr) (Some v)))
                        ltac:(lia) ltac:(lia) Hfl) as H;
          clear Hfl; unfold adenot in H; cbn [a_base a_off edenot] in H; ev_simpl_in E H ]
    | None => fail "kread: no knowledge entry covers this range"
    end
  end.

Section Lib.
Variable segs : list Segment.

Lemma know_ok_snoc : forall E M kn K,
  know_ok segs E M kn -> kentry_ok segs E M K -> know_ok segs E M (kn ++ [K]).
Proof. intros. apply know_ok_app; [assumption | constructor; [assumption | constructor]]. Qed.

(* [comment removed for export] *)
Lemma outside_of_apart : forall (x : word) lo len rs,
  (lo <= bv_unsigned x < lo + len)%Z ->
  Forall (fun r => bv_unsigned (fst r) + snd r <= lo \/ lo + len <= bv_unsigned (fst r))%Z rs ->
  outside x rs.
Proof.
  intros x lo len rs Hx. induction rs as [|[a n] rest IH]; cbn [outside]; intros H; [exact I|].
  apply Forall_cons_iff in H as [H1 H2]. cbn [fst snd] in H1.
  split; [| apply IH; exact H2]. unfold in_rng. lia.
Qed.

Lemma kblobd_frame : forall E M M' b k (l : expr) bk rs,
  kentry_ok segs E M (KBlobD (SA b k) l bk) ->
  frame_mod M M' rs ->
  Forall (fun r => bv_unsigned (fst r) + snd r <= estart E (SA b k)
                   \/ estart E (SA b k) + bv_unsigned (edenot E l) <= bv_unsigned (fst r))%Z rs ->
  kentry_ok segs E M' (KBlobD (SA b k) l bk).
Proof.
  intros E M M' b k l bk rs HK [Hout _] Hapart.
  cbn [kentry_ok] in HK |- *. destruct HK as (Hfl & Hlen & Hbytes).
  split; [exact Hfl|]. split; [exact Hlen|].
  intros i Hi. rewrite <- (Hbytes i Hi). apply Hout.
  unfold elenZ in Hi. destruct Hfl as (F1 & F2 & F3 & F4). unfold elenZ in F3, F4.
  apply (outside_of_apart _ (estart E (SA b k)) (bv_unsigned (edenot E l))); [| exact Hapart].
  rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma kblobd_mem_denot : forall E M log b k (l : expr) bk (RS : list (saddr * Z)),
  kentry_ok segs E M (KBlobD (SA b k) l bk) ->
  log_flat E log ->
  Forall (fun r => flat E (fst r) (snd r)) RS ->
  log_in_regions log RS = true ->
  Forall (fun r => estart E (fst r) + snd r <= estart E (SA b k)
                   \/ estart E (SA b k) + bv_unsigned (edenot E l) <= estart E (fst r))%Z RS ->
  kentry_ok segs E (mem_denot E M log) (KBlobD (SA b k) l bk).
Proof.
  intros E M log b k l bk RS HK Hlf Hfl Hin Hapart.
  eapply kblobd_frame; [exact HK | apply (frame_mod_mem_denot E M log RS Hlf Hfl Hin) |].
  unfold regions_denot. apply Forall_map. 
  eapply Forall_impl; [| apply Forall_and; [exact Hfl | exact Hapart]].
  intros [a n] [Hf Ha]. cbn [fst snd] in *. rewrite (flat_u E _ _ Hf). exact Ha.
Qed.

(* [comment removed for export] *)
Lemma be32_range : forall bs off, (0 <= be32 bs off < 2 ^ 32)%Z.
Proof.
  intros bs off. unfold be32, bs_byte.
  pose proof (byte_range (nth (Z.to_nat off) bs (Z_to_bv 8 0))).
  pose proof (byte_range (nth (Z.to_nat (off + 1)) bs (Z_to_bv 8 0))).
  pose proof (byte_range (nth (Z.to_nat (off + 2)) bs (Z_to_bv 8 0))).
  pose proof (byte_range (nth (Z.to_nat (off + 3)) bs (Z_to_bv 8 0))). lia.
Qed.

Lemma bs_byte_range : forall bs off, (0 <= bs_byte bs off < 256)%Z.
Proof. intros. unfold bs_byte. apply byte_range. Qed.

(* [comment removed for export] *)
Lemma ext_val_4_small : forall z, (0 <= z < 2 ^ 32)%Z -> ext_val false 0 4 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold ext_val, ext_Z. rewrite u_small by lia.
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z.
  rewrite Z.div_1_r, Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma word_to_le_bytes_4_low : forall (w : word),
  word_to_le_bytes 4 w = word_to_le_bytes 4 (Z_to_bv 64 (bv_unsigned w mod 2 ^ 32)).
Proof.
  intros w. unfold word_to_le_bytes.
  pose proof (u64_range w).
  pose proof (Z.mod_pos_bound (bv_unsigned w) (2 ^ 32) ltac:(lia)).
  rewrite (u_small (bv_unsigned w mod 2 ^ 32)) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned w)).
  change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z. reflexivity.
Qed.

Lemma cell32_of_word : forall M a (w : word),
  rdn segs M (Z_to_bv 64 a) 4 = Some (word_to_le_bytes 4 w) ->
  cell32 segs M a (bv_unsigned w mod 2 ^ 32).
Proof.
  intros M a w H. pose proof (u64_range w).
  pose proof (Z.mod_pos_bound (bv_unsigned w) (2 ^ 32) ltac:(lia)).
  split; [lia|]. unfold cell. rewrite H. f_equal. apply word_to_le_bytes_4_low.
Qed.

Lemma ext_val_4_word : forall (w : word),
  ext_val false 0 4 w = Z_to_bv 64 (bv_unsigned w mod 2 ^ 32).
Proof.
  intros w. unfold ext_val, ext_Z.
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z.
  rewrite Z.div_1_r. reflexivity.
Qed.

End Lib.
