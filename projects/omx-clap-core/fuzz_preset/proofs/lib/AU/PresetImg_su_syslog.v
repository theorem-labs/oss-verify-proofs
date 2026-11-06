(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_su_syslog.v (commit 4d286b2e618d, file sha256 68941368d3d6) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 1 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 2 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Reply image B (fuzz_reply.asan-ubsan), start-up row img-su-syslog-B of the internal file REPLY-IMG-ROWS.md
   (the internal file CF-UNIT-HYPS.md:155, Table 4): common_flags + 0x40 (log_to_syslog) = 0 after AsanInitInternal.
   The field offset 0x40 is the row's own text (the internal file CF-UNIT-HYPS.md:155); this image's DWARF does not describe
   CommonFlags, so the lemmas pin the whole 8-byte word at common_flags + 0x40 .. + 0x47, which holds the flag.
   common_flags of this image is YB1w.tfib_D_common_flags_dont_use_CommonFlags_struct_common (0x13d228; the
   unstripped twin's symbol _ZN11__sanitizer21common_flags_dont_useE, size 288), so the word is at 0x13d268
   (a_off 1278376). cgif's evidence for the same fact is the KWord at a_off 1277416 in
   proofs/cgif/cgif_file_fuzzer/lib/YB01.v:14 / YB03.v:12 (the internal file STARTUP-FACTS-CHECK.md:49-51).
   - su_syslog_B: the consumer form (the internal file REPLY-IMG-ROWS.md:15), over @im_syms AImg_cgif B;
   - presetb_log_to_syslog_const: the same over TfibSyms / as_const (row 8 of YF0m.Tfib_const_abs);
   - presetb_log_to_syslog_HS0_kn / _HS0 / _band / _start / _hs: the start-state form, in the first hand-off
     state, in the band state (YB03.JS_tfib_band) and in every one of the 50 collected hand-off states
     (YB01.HS_tfib_list). Names are A's (lib/A/PresetImg_su_syslog.v) with the image letter swapped.
   The table scans run as one vm-checked boolean (whole-goal vm_compute), never as a list of literal pairs. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0c YK09 YA0e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YF0m YB01 YB03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
Import ListNotations. Import AX2. Import APC.
Open Scope Z_scope.

Definition presetb_log_to_syslog_addr : Z := tfib_D_common_flags_dont_use_CommonFlags_struct_common + 0x40.

Lemma presetb_log_to_syslog_addr_val : presetb_log_to_syslog_addr = 0x13d268.
Proof. reflexivity. Qed.

(* Const-table form: at every layout, the image's const cells pin the word to 0. *)
Lemma presetb_log_to_syslog_const : forall (B : asyms) (ly : alayout), TfibSyms B ->
  In (z8 (ANum presetb_log_to_syslog_addr) 0) (as_const B ly).
Proof.
  intros B ly HT. rewrite (ts_const B HT ly). unfold Tfib_const.
  apply in_or_app. right. apply in_or_app. left.
  apply (nth_error_In _ 8). vm_compute. reflexivity.
Qed.

(* Consumer form (NAMING rule, the internal file REPLY-IMG-ROWS.md:15; twin su_syslog_A). *)
Lemma su_syslog_B : forall (B : asyms) (ly : alayout), @im_syms AImg_cgif B ->
  In (z8 (ANum presetb_log_to_syslog_addr) 0) (@im_const AImg_cgif ly).
Proof.
  intros B ly TS. rewrite <- (@im_const_eq AImg_cgif B ly TS).
  exact (presetb_log_to_syslog_const B ly TS).
Qed.

(* Start-state form: the know entry the collected start-up states carry for the word. *)
Definition presetb_log_to_syslog_cell : kentry :=
  KWord (SA (ELit 0) presetb_log_to_syslog_addr) 8 (ELit 0).

Lemma kentry_in_of_existsb : forall (c : kentry) (l : list kentry),
  existsb (APC.kentry_eqb c) l = true -> In c l.
Proof.
  intros c l H. apply existsb_exists in H. destruct H as [K [HIn HK]].
  apply APSG.kentry_eqb_eq in HK. rewrite HK. exact HIn.
Qed.

Lemma presetb_log_to_syslog_HS0_kn : In presetb_log_to_syslog_cell HS_tfib_0_kn.
Proof. apply kentry_in_of_existsb. vm_compute. reflexivity. Qed.

Lemma presetb_log_to_syslog_HS0 : In presetb_log_to_syslog_cell (APC.kn HS_tfib_0).
Proof. exact presetb_log_to_syslog_HS0_kn. Qed.

Lemma presetb_log_to_syslog_band : In presetb_log_to_syslog_cell (APC.kn JS_tfib_band).
Proof. apply kentry_in_of_existsb. vm_compute. reflexivity. Qed.

Lemma presetb_log_to_syslog_start :
  In presetb_log_to_syslog_cell HS_tfib_0_kn /\ In presetb_log_to_syslog_cell (APC.kn JS_tfib_band).
Proof. exact (conj presetb_log_to_syslog_HS0_kn presetb_log_to_syslog_band). Qed.

Lemma presetb_log_to_syslog_hs : forall (h : nat) (cs : acs), HS_tfib h = Some cs ->
  In presetb_log_to_syslog_cell (APC.kn cs).
Proof.
  assert (Hb : forallb (fun cs => existsb (APC.kentry_eqb presetb_log_to_syslog_cell) (APC.kn cs)) HS_tfib_list = true)
    by (vm_compute; reflexivity).
  intros h cs Hh. unfold HS_tfib in Hh. apply nth_error_In in Hh.
  rewrite forallb_forall in Hb. exact (kentry_in_of_existsb _ _ (Hb cs Hh)).
Qed.
