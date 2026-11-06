(* The harness facts of one message on the ASan build: harness_props_at (lib/A/Prog/HarnessPropsA.v) at the value
   of the atoi wrapper, atoi_a = bv_swrap 32 (s10_val s) (lib/A/Prog/sup_reply_code_c.v:47, RtNumber's aatoi_realizes),
   and the reply code read with it, reply_code_a (:49-52).

   harness_props_at_holds needs five properties of the atoi value (HarnessPropsA.v, Section any_atoi). For atoi_a:
   - it is an int: bv_swrap 32 (swr_range, lib/Prog/HarnessPropsProof.v:224);
   - a word number_m accepts reads as its value: number_m takes the whole word after its blanks, an optional sign
     and at least one digit, and a value in [-10^6, 10^6] (lib/Spec/Verbs.v:129-154); musl's strtol model reads
     the same blanks, sign and digits (lib/Prog/__intscan_c.v:13-36), and the value is inside both the long range
     and the int range;
   - the "%d" text of a value in [0, 2^31) reads back as the value: the text is digits only (dec_pos_facts,
     HarnessPropsProof.v:458);
   - the declared refusals and the shapes have the plain image's codes: their digit runs have at most 3
     characters; checked by computation.
   It also gives piece 1 (run_args, lib/A/Prog/HarnessArgs.v) at these values. The bridges to the ASan statements'
   own forms are in lib/A/Prog/HarnessPropsABridge.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun CType.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandModel RecFacts RecModel
  rec_code_declared_c rec_shape_of_c printf_facts_c HarnessPropsProof.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require __intscan_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import HarnessArgs HarnessPropsA.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require sup_reply_code_c.
Import ListNotations.
Open Scope Z_scope.

Local Notation atoi_a := A.Prog.sup_reply_code_c.atoi_a.
Local Notation reply_code_a := A.Prog.sup_reply_code_c.reply_code_a.

(** * The five properties of atoi_a *)

Lemma atoi_a_range : forall s, -2^31 <= atoi_a s < 2^31.
Proof. intros s. unfold A.Prog.sup_reply_code_c.atoi_a. apply swr_range. Qed.

(* the digits of a digit run, as the plain spec and musl's strtol model read them *)
Lemma dval_digits : forall l acc d, Verbs.digits_val acc l = Some d -> __intscan_c.dval acc l = d.
Proof.
  induction l as [|b l IH]; intros acc d H; cbn [Verbs.digits_val] in H.
  - injection H as <-. reflexivity.
  - destruct (Verbs.is_digit b) eqn:Db; [|discriminate]. cbn [__intscan_c.dval].
    replace (CType.c_digit b) with true by (symmetry; exact Db). apply IH. exact H.
Qed.

(* the blanks, the sign and the digits number_m reads are the ones strtol reads *)
Lemma signed_s10 : forall w x, Verbs.signed_digits (Verbs.dropw Verbs.is_space w) = Some x ->
  __intscan_c.s10_signed w = x.
Proof.
  intros w x E. unfold __intscan_c.s10_signed, __intscan_c.s10_neg, __intscan_c.s10_mag, __intscan_c.s10_rest.
  rewrite skip_space_dropw.
  destruct (Verbs.dropw Verbs.is_space w) as [|b r]; [discriminate|].
  cbn [Verbs.signed_digits] in E. cbn [__intscan_c.sign_split].
  destruct (Z.eqb_spec (bv_unsigned b) 43) as [B43|B43].
  - rewrite (proj2 (Z.eqb_neq (bv_unsigned b) 45)) by lia. cbn [fst snd].
    unfold Verbs.digits_m in E. destruct r as [|c r']; [discriminate|]. apply dval_digits. exact E.
  - destruct (Z.eqb_spec (bv_unsigned b) 45) as [B45|B45]; cbn [fst snd].
    + unfold Verbs.digits_m in E. destruct r as [|c r']; [discriminate|].
      destruct (Verbs.digits_val 0 (c :: r')) as [d|] eqn:Ed; [|discriminate]. cbn in E. injection E as <-.
      rewrite (dval_digits _ _ _ Ed). reflexivity.
    + unfold Verbs.digits_m in E. apply dval_digits. exact E.
Qed.

Lemma atoi_a_number : forall w v, Verbs.number_m w = Some v -> atoi_a w = v.
Proof.
  intros w v H. pose proof (Verbs.number_m_range w v H) as Rg. unfold Verbs.number_m in H.
  destruct (Verbs.signed_digits (Verbs.dropw Verbs.is_space w)) as [x|] eqn:E; [|discriminate].
  destruct ((-1000000 <=? x) && (x <=? 1000000)); [|discriminate]. injection H as <-.
  unfold A.Prog.sup_reply_code_c.atoi_a, __intscan_c.s10_val. rewrite (signed_s10 w x E).
  unfold __intscan_c.LMIN. rewrite Z.min_r by lia. rewrite Z.max_r by lia. apply swr_id. lia.
Qed.

Lemma atoi_a_dec : forall v, 0 <= v < 2^31 -> atoi_a (dec v) = v.
Proof.
  intros v Hv. destruct (dec_pos_facts v ltac:(lia)) as [Hne Hdig]. rewrite dec_pos in * by lia.
  destruct (digits_val_digits 10 v [] 0 ltac:(cbn; lia)) as (m & Hm & E).
  rewrite Z.mul_0_l, Z.add_0_l in E. change (Verbs.digits_val v []) with (Some v) in E.
  destruct (digits 10 v []) as [|b r] eqn:Edg; [congruence|].
  assert (Hb : 48 <= bv_unsigned b <= 57) by (apply Hdig; left; reflexivity).
  assert (S : __intscan_c.s10_signed (b :: r) = v).
  { unfold __intscan_c.s10_signed, __intscan_c.s10_neg, __intscan_c.s10_mag, __intscan_c.s10_rest.
    cbn [CType.skip_space].
    replace (CType.c_space b) with false by (unfold CType.c_space; symmetry; apply orb_false_iff; split;
      [apply Z.eqb_neq; lia | apply andb_false_iff; right; apply Z.leb_gt; lia]).
    cbn [__intscan_c.sign_split].
    rewrite (proj2 (Z.eqb_neq (bv_unsigned b) 45)) by lia. rewrite (proj2 (Z.eqb_neq (bv_unsigned b) 43)) by lia.
    cbn [fst snd]. apply dval_digits. exact E. }
  unfold A.Prog.sup_reply_code_c.atoi_a, __intscan_c.s10_val. rewrite S. unfold __intscan_c.LMIN.
  rewrite Z.min_r by lia. rewrite Z.max_r by lia. apply swr_id. lia.
Qed.

Lemma atoi_a_decl : forallb (fun c => rcode_at atoi_a (resp c) =? c) rec_codes = true.
Proof. vm_compute. reflexivity. Qed.

Lemma atoi_a_shapes : forallb (fun s => 0 <=? rcode_at atoi_a (inst s)) shape_set = true.
Proof. vm_compute. reflexivity. Qed.

(** * The ASan image's harness facts *)

(* lib/Prog/HarnessProps.v:32-37 harness_props, over the ASan image's run VerbsRun.run_receive atoi_a reply_code_a
   (lib/A/Prog/verbs_receive_c.v:66-67 vr_runA) *)
Definition harness_props_a : Prop := harness_props_at atoi_a reply_code_a.

Theorem harness_props_holds_a : harness_props_a.
Proof.
  unfold harness_props_a. apply harness_props_at_holds;
    first [exact atoi_a_range | exact atoi_a_number | exact atoi_a_dec | exact atoi_a_decl | exact atoi_a_shapes].
Qed.

(* piece 1 (lib/A/Prog/HarnessArgs.v run_args) at the ASan image's values *)
Theorem run_args_a : forall R0 D,
  let '(R1, x, q) := VerbsRun.run_receive atoi_a reply_code_a (rec_clear R0) D in
  (length (r_calls R1) <= 2)%nat /\ ev_args_m R1 <= 5.
Proof. intros R0 D. exact (run_args atoi_a reply_code_a R0 D). Qed.
