(* Segment L02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput, both builds: the label of a drop-in turn in the
   spine's terms (build-independent: Spec/SegModel.v and Spec/SegPrintfBridge.v only).
   - label_of lb in its three cases: bit 7 set gives longl (120 'L'), lb = 0 gives NULL, else the snprintf text
     "reac-pw.conf.d/%u-x.conf" of lb, which for 0 < lb < 128 is the whole model text (at most 25 bytes, each in
     1..255), so snprintf's 40-byte buffer holds it with its NUL;
   - the printf_model equation snprintf_m_contract takes at that call (SegPrintfBridge.pm_label, pargs_label).
   Model lemmas of a segment walk. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require ITree.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Prelim FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Printf_model G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegPrintfBridge.
Import ListNotations.
Open Scope Z_scope.

(** The snprintf text of a label byte. *)
Definition lab_txt (lb : Z) : list Z := fmt F_label [AI lb].

Definition lab_okb (lb : Z) : bool :=
  (length (lab_txt lb) <=? 25)%nat && forallb (fun x => (0 <? x) && (x <? 256)) (lab_txt lb).

Lemma lab_okb_all : forallb (fun k => lab_okb (Z.of_nat k)) (seq 1 127) = true.
Proof. vm_compute. reflexivity. Qed.

(** For 0 < lb < 128 the text has at most 25 bytes, each in 1..255. *)
Lemma lab_txt_ok : forall lb, 0 < lb < 128 ->
  (length (lab_txt lb) <= 25)%nat /\ Forall (fun x => 0 < x < 256) (lab_txt lb).
Proof.
  intros lb H. pose proof lab_okb_all as A. rewrite forallb_forall in A.
  specialize (A (Z.to_nat lb) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in A by lia.
  unfold lab_okb in A. apply andb_prop in A as [A1 A2]. split; [apply Nat.leb_le; exact A1|].
  apply Forall_forall. intros x Hx. rewrite forallb_forall in A2. specialize (A2 x Hx).
  apply andb_prop in A2 as [B1 B2]. apply Z.ltb_lt in B1. apply Z.ltb_lt in B2. lia.
Qed.

(** snprintf(buf, 40, ...) keeps the whole text. *)
Lemma lab_snprintf : forall lb, 0 < lb < 128 -> snprintf_s 40 F_label [AI lb] = lab_txt lb.
Proof.
  intros lb H. destruct (lab_txt_ok lb H) as [L _]. unfold snprintf_s, lab_txt in *.
  apply firstn_all2. cbn [Z.sub Z.to_nat]. change (Z.to_nat (40 - 1)) with 39%nat. lia.
Qed.

(** Bit 7 of a byte. *)
Lemma land128_byte : forallb (fun k => Bool.eqb (Z.land (Z.of_nat k) 128 =? 0) (Z.of_nat k <? 128)) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma land128 : forall lb, 0 <= lb < 256 -> (Z.land lb 128 =? 0) = (lb <? 128).
Proof.
  intros lb H. pose proof land128_byte as A. rewrite forallb_forall in A.
  specialize (A (Z.to_nat lb) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in A by lia.
  apply Bool.eqb_prop in A. exact A.
Qed.

(** label_of in its three cases. *)
Lemma label_of_hi : forall lb, 128 <= lb < 256 -> label_of lb = Some longl.
Proof.
  intros lb H. unfold label_of. rewrite land128 by lia.
  replace (lb <? 128) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma label_of_zero : label_of 0 = None.
Proof. reflexivity. Qed.

Lemma label_of_mid : forall lb, 0 < lb < 128 -> label_of lb = Some (lab_txt lb).
Proof.
  intros lb H. unfold label_of. rewrite land128 by lia.
  replace (lb <? 128) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (lb =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  rewrite lab_snprintf by exact H. reflexivity.
Qed.

(** longl: 120 bytes 'L'. *)
Lemma longl_ok : length longl = 120%nat /\ Forall (fun x => 0 < x < 256) longl.
Proof. split; [reflexivity|]. unfold longl. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. Qed.

(** The printf_model equation of snprintf_m_contract at the label call: format F_label, arguments [PA_u lb], the
    output the whole text, the return value its length. *)
Lemma lab_pm : forall lb, 0 < lb < 128 ->
  Printf_model.printf_model (St:=list Z)
    (G_printf_core_common.G_printf_iface.OUT_snf (Prelim.zlength (lab_txt lb)))
    G_printf_core_common.G_printf_iface.OUTFP_snf (F_label ++ [0]) [Printf_model.PA_u lb] []
  = ITree.Ret (ITree.Exc.Ok (Z.of_nat (length (lab_txt lb)), lab_txt lb)).
Proof.
  intros lb H. destruct (lab_txt_ok lb H) as [L _].
  pose proof (SegPrintfBridge.pm_label lb ltac:(lia)) as P.
  unfold SegPrintfBridge.pm_eq in P. rewrite SegPrintfBridge.pargs_label in P.
  unfold lab_txt. apply P. unfold Prelim.zlength, FmtFp.INT_MAX. unfold lab_txt in L. lia.
Qed.

(** The format's own facts snprintf_m_contract takes (bytes, pass1_ok). *)
Lemma lab_fmt_good : Forall (fun c => 0 <= c < 256) F_label /\ Printf_model.pass1_ok (F_label ++ [0]) = true.
Proof.
  destruct (SegPrintfBridge.seg_format_good F_label ltac:(cbn; tauto)) as (_ & P & B). split; assumption.
Qed.
