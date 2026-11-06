From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import Mem Cells.
Require OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct.
Require OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Require OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.pcap_source_struct.
Require OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.pcap_source_struct_next.
Import ListNotations.
Open Scope Z_scope.

(* The ubsan unit states its reader contracts over lib/U/Prog/pcap_source_struct(_next).v, a copy of the plain chain
   model with the ubsan imports. The slot proof uses the plain model (lib/Prog/Slot/PWalk.v is stated over it), so
   these lemmas rewrite every function of the ubsan copy into the plain one. *)
Module PS := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct.
Module PN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Module US := OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.pcap_source_struct.
Module UN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.pcap_source_struct_next.

Definition pk (k : UN.pkind) : PN.pkind :=
  match k with
  | UN.KEnd => PN.KEnd | UN.KCutH => PN.KCutH | UN.KEmpty => PN.KEmpty | UN.KFit => PN.KFit
  | UN.KCutFit => PN.KCutFit | UN.KBig0 => PN.KBig0 | UN.KBig => PN.KBig | UN.KCutBig => PN.KCutBig
  end.

Lemma ps_cells_UP : US.ps_cells = PS.ps_cells. Proof. reflexivity. Qed.
Lemma pcap_magic_UP : US.pcap_magic = PS.pcap_magic. Proof. reflexivity. Qed.
Lemma pcap_good_UP : US.pcap_good = PS.pcap_good. Proof. reflexivity. Qed.
Lemma pcap_sw_UP : US.pcap_sw = PS.pcap_sw. Proof. reflexivity. Qed.

Lemma img_apart_UP : UN.img_apart = PN.img_apart. Proof. reflexivity. Qed.
Lemma hw_UP : UN.hw = PN.hw. Proof. reflexivity. Qed.
Lemma incl_UP : UN.incl = PN.incl. Proof. reflexivity. Qed.
Lemma orig_UP : UN.orig = PN.orig. Proof. reflexivity. Qed.
Lemma tagged_UP : UN.tagged = PN.tagged. Proof. reflexivity. Qed.
Lemma rec_len_UP : UN.rec_len = PN.rec_len. Proof. reflexivity. Qed.
Lemma rec_vid_UP : UN.rec_vid = PN.rec_vid. Proof. reflexivity. Qed.
Lemma rec_ts_UP : UN.rec_ts = PN.rec_ts. Proof. reflexivity. Qed.
Lemma rec_raw_UP : UN.rec_raw = PN.rec_raw. Proof. reflexivity. Qed.
Lemma rec_bytes_UP : UN.rec_bytes = PN.rec_bytes. Proof. reflexivity. Qed.

Lemma kind_UP : forall sw F cap q, PN.kind sw F cap q = pk (UN.kind sw F cap q).
Proof.
  intros sw F cap q. unfold PN.kind, UN.kind.
  change (PN.flen F) with (UN.flen F). change (PN.incl sw F q) with (UN.incl sw F q).
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma is_fit_UP : forall k, PN.is_fit (pk k) = UN.is_fit k.
Proof. intros k. destruct k; reflexivity. Qed.

Lemma kind_fit_UP : forall sw F cap q, UN.kind sw F cap q = UN.KFit <-> PN.kind sw F cap q = PN.KFit.
Proof.
  intros sw F cap q. rewrite kind_UP. destruct (UN.kind sw F cap q); cbn [pk]; split; congruence.
Qed.

Lemma chain_UP : forall sw F cap f q lh, UN.chain sw F cap f q lh = PN.chain sw F cap f q lh.
Proof.
  intros sw F cap f. induction f as [|f IH]; intros q lh; [reflexivity|].
  cbn [UN.chain PN.chain]. rewrite kind_UP.
  destruct (UN.kind sw F cap q); cbn [pk]; rewrite ?IH; reflexivity.
Qed.

Lemma psn_chain_UP : forall sw F cap p, UN.psn_chain sw F cap p = PN.psn_chain sw F cap p.
Proof. intros. unfold UN.psn_chain, PN.psn_chain. apply chain_UP. Qed.

Lemma psn_out_UP : forall h sw F cap p, UN.psn_out h sw F cap p = PN.psn_out h sw F cap p.
Proof. intros. unfold UN.psn_out, PN.psn_out. rewrite psn_chain_UP. reflexivity. Qed.

Lemma psn_q_UP : forall sw F cap p, UN.psn_q sw F cap p = PN.psn_q sw F cap p.
Proof. intros. unfold UN.psn_q, PN.psn_q. rewrite psn_chain_UP. reflexivity. Qed.

Lemma psn_lh_UP : forall sw F cap p, UN.psn_lh sw F cap p = PN.psn_lh sw F cap p.
Proof. intros. unfold UN.psn_lh, PN.psn_lh. rewrite psn_chain_UP. reflexivity. Qed.

Lemma res_of_UP : forall sw F cap q, UN.res_of sw F cap q = PN.res_of sw F cap q.
Proof. intros. unfold UN.res_of, PN.res_of. rewrite kind_UP. destruct (UN.kind sw F cap q); reflexivity. Qed.

Lemma pos_of_UP : forall sw F cap q, UN.pos_of sw F cap q = PN.pos_of sw F cap q.
Proof. intros. unfold UN.pos_of, PN.pos_of. rewrite kind_UP. destruct (UN.kind sw F cap q); reflexivity. Qed.

Lemma lol_of_UP : UN.lol_of = PN.lol_of. Proof. reflexivity. Qed.

Lemma vt_of_UP : forall sw F cap q v, UN.vt_of sw F cap q v = PN.vt_of sw F cap q v.
Proof. intros. unfold UN.vt_of, PN.vt_of. rewrite kind_UP, is_fit_UP. reflexivity. Qed.

Lemma vid_of_UP : forall sw F cap q v, UN.vid_of sw F cap q v = PN.vid_of sw F cap q v.
Proof. intros. unfold UN.vid_of, PN.vid_of. rewrite kind_UP, is_fit_UP. reflexivity. Qed.

Lemma ts_of_UP : forall sw F cap q v, UN.ts_of sw F cap q v = PN.ts_of sw F cap q v.
Proof. intros. unfold UN.ts_of, PN.ts_of. rewrite kind_UP, is_fit_UP. reflexivity. Qed.

Lemma is_fit_kind_UP : forall sw F cap q, UN.is_fit (UN.kind sw F cap q) = PN.is_fit (PN.kind sw F cap q).
Proof. intros. rewrite kind_UP, is_fit_UP. reflexivity. Qed.
