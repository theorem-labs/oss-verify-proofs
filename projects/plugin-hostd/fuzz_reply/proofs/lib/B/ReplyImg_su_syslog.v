(* Reply image B (fuzz_reply.asan-ubsan), start-up row img-su-syslog-B of REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record)
   (CF-UNIT-HYPS.md:155 (sha256 77b3f94c95d2; internal record), Table 4): common_flags + 0x40 (log_to_syslog) = 0 after AsanInitInternal.
   The field offset 0x40 is the row's own text (CF-UNIT-HYPS.md:155 sha256 77b3f94c95d2; internal record); this image's DWARF does not describe
   CommonFlags, so the lemmas pin the whole 8-byte word at common_flags + 0x40 .. + 0x47, which holds the flag.
   common_flags of this image is YB1w.tfib_D_common_flags_dont_use_CommonFlags_struct_common (0x138168; the
   unstripped twin's symbol _ZN11__sanitizer21common_flags_dont_useE, size 288), so the word is at 0x1381a8
   (a_off 1278376). cgif's evidence for the same fact is the KWord at a_off 1277416 in
   proofs/cgif/cgif_file_fuzzer/lib/YB01.v:14 / YB03.v:12 (STARTUP-FACTS-CHECK.md:49-51 sha256 e2dc89b75692; internal record).
   - su_syslog_B: the consumer form (REPLY-IMG-ROWS.md:15 sha256 a33a582e3ffd; internal record), over @im_syms AImg_reply B;
   - replyb_log_to_syslog_const: the same over TfibSyms / as_const (row 8 of YF0m.Tfib_const_abs);
   - replyb_log_to_syslog_HS0_kn / _HS0 / _band / _start / _hs: the start-state form, in the first hand-off
     state, in the band state (YB03.JS_tfib_band) and in every one of the 50 collected hand-off states
     (YB01.HS_tfib_list). Names are A's (lib/A/ReplyImg_su_syslog.v) with the image letter swapped.
   The table scans run as one vm-checked boolean (whole-goal vm_compute), never as a list of literal pairs. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0c YK09 YA0e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YF0m YB01 YB03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply.
Import ListNotations. Import AX2. Import APC.
Open Scope Z_scope.

Definition replyb_log_to_syslog_addr : Z := tfib_D_common_flags_dont_use_CommonFlags_struct_common + 0x40.

Lemma replyb_log_to_syslog_addr_val : replyb_log_to_syslog_addr = 0x1381a8.
Proof. reflexivity. Qed.

(* Const-table form: at every layout, the image's const cells pin the word to 0. *)
Lemma replyb_log_to_syslog_const : forall (B : asyms) (ly : alayout), TfibSyms B ->
  In (z8 (ANum replyb_log_to_syslog_addr) 0) (as_const B ly).
Proof.
  intros B ly HT. rewrite (ts_const B HT ly). unfold Tfib_const.
  apply in_or_app. right. apply in_or_app. left.
  apply (nth_error_In _ 8). vm_compute. reflexivity.
Qed.

(* Consumer form (NAMING rule, REPLY-IMG-ROWS.md:15 (sha256 a33a582e3ffd; internal record); twin su_syslog_A). *)
Lemma su_syslog_B : forall (B : asyms) (ly : alayout), @im_syms AImg_reply B ->
  In (z8 (ANum replyb_log_to_syslog_addr) 0) (@im_const AImg_reply ly).
Proof.
  intros B ly TS. rewrite <- (@im_const_eq AImg_reply B ly TS).
  exact (replyb_log_to_syslog_const B ly TS).
Qed.

(* Start-state form: the know entry the collected start-up states carry for the word. *)
Definition replyb_log_to_syslog_cell : kentry :=
  KWord (SA (ELit 0) replyb_log_to_syslog_addr) 8 (ELit 0).

Lemma kentry_in_of_existsb : forall (c : kentry) (l : list kentry),
  existsb (APC.kentry_eqb c) l = true -> In c l.
Proof.
  intros c l H. apply existsb_exists in H. destruct H as [K [HIn HK]].
  apply APSG.kentry_eqb_eq in HK. rewrite HK. exact HIn.
Qed.

Lemma replyb_log_to_syslog_HS0_kn : In replyb_log_to_syslog_cell HS_tfib_0_kn.
Proof. apply kentry_in_of_existsb. vm_compute. reflexivity. Qed.

Lemma replyb_log_to_syslog_HS0 : In replyb_log_to_syslog_cell (APC.kn HS_tfib_0).
Proof. exact replyb_log_to_syslog_HS0_kn. Qed.

Lemma replyb_log_to_syslog_band : In replyb_log_to_syslog_cell (APC.kn JS_tfib_band).
Proof. apply kentry_in_of_existsb. vm_compute. reflexivity. Qed.

Lemma replyb_log_to_syslog_start :
  In replyb_log_to_syslog_cell HS_tfib_0_kn /\ In replyb_log_to_syslog_cell (APC.kn JS_tfib_band).
Proof. exact (conj replyb_log_to_syslog_HS0_kn replyb_log_to_syslog_band). Qed.

Lemma replyb_log_to_syslog_hs : forall (h : nat) (cs : acs), HS_tfib h = Some cs ->
  In replyb_log_to_syslog_cell (APC.kn cs).
Proof.
  assert (Hb : forallb (fun cs => existsb (APC.kentry_eqb replyb_log_to_syslog_cell) (APC.kn cs)) HS_tfib_list = true)
    by (vm_compute; reflexivity).
  intros h cs Hh. unfold HS_tfib in Hh. apply nth_error_In in Hh.
  rewrite forallb_forall in Hb. exact (kentry_in_of_existsb _ _ (Hb cs Hh)).
Qed.
