(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Fmt StrerrorTable PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module FmtFacts.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Fmt StrerrorTable PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Definition bytes_ok (l : list Z) : Prop := Forall (fun z => 0 < z < 256) l.
Definition arg_ok (a : farg) : Prop := match a with AInt _ => True | AStr s => bytes_ok s end.
Definition item_ok (i : fitem) : Prop := match i with FLit l => bytes_ok l | FConv _ => True | FBad l => bytes_ok l end.

(* [comment removed for export] *)
Definition bytes_okb (l : list Z) : bool := forallb (fun z => (0 <? z) && (z <? 256)) l.
Definition item_okb (i : fitem) : bool := match i with FLit l => bytes_okb l | FConv _ => true | FBad l => bytes_okb l end.
Definition items_okb (l : list fitem) : bool := forallb item_okb l.

Lemma bytes_okb_ok : forall l, bytes_okb l = true -> bytes_ok l.
Proof.
  induction l as [|x l IH]; intros Hb; [constructor|]. cbn in Hb. apply andb_prop in Hb as [H1 H2]. apply andb_prop in H1 as [Ha Hc].
  constructor; [| apply IH; exact H2]. apply Z.ltb_lt in Ha. apply Z.ltb_lt in Hc. lia.
Qed.
Lemma items_okb_ok : forall l, items_okb l = true -> Forall item_ok l.
Proof.
  induction l as [|x l IH]; intros Hb; [constructor|]. cbn in Hb. apply andb_prop in Hb as [H1 H2].
  constructor; [| apply IH; exact H2]. destruct x; cbn in *; [apply bytes_okb_ok; exact H1 | exact I | apply bytes_okb_ok; exact H1].
Qed.

Lemma bytes_ok_app : forall a b, bytes_ok a -> bytes_ok b -> bytes_ok (a ++ b).
Proof. intros. unfold bytes_ok in *. apply Forall_app. tauto. Qed.
Lemma bytes_ok_firstn : forall n l, bytes_ok l -> bytes_ok (firstn n l).
Proof.
  intros n l Hl. unfold bytes_ok in *. revert n. induction Hl as [|x l Hx Hl IH]; intros [|n]; cbn; try constructor; auto.
Qed.
Lemma bytes_ok_concat : forall ls, Forall bytes_ok ls -> bytes_ok (List.concat ls).
Proof. induction ls as [|l ls IH]; intros HF; cbn; [constructor|]. apply Forall_cons_iff in HF as [H1 H2]. apply bytes_ok_app; auto. Qed.

(* [comment removed for export] *)
Lemma udigits_aux_ok : forall fuel base n acc, 0 < base <= 100 -> bytes_ok acc -> bytes_ok (udigits_aux fuel base n acc).
Proof.
  induction fuel as [|fuel IH]; intros base n acc Hb Hacc; cbn [udigits_aux]; [exact Hacc|].
  destruct (n <=? 0); [exact Hacc|]. apply IH; [exact Hb|]. constructor; [|exact Hacc].
  pose proof (Z.mod_pos_bound n base ltac:(lia)). destruct (Z.ltb_spec (n mod base) 10); lia.
Qed.
Lemma dec_udigits_ok : forall n, bytes_ok (dec_udigits n).
Proof. intros. unfold dec_udigits, udigits. apply udigits_aux_ok; [lia| constructor]. Qed.
Lemma hex_udigits_ok : forall n, bytes_ok (hex_udigits n).
Proof. intros. unfold hex_udigits, udigits. apply udigits_aux_ok; [lia| constructor]. Qed.
Lemma zeros_ok : forall n, bytes_ok (zeros n).
Proof.
  intros n. unfold zeros, zrepeat, bytes_ok. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. lia.
Qed.

Lemma int_pieces_ok : forall neg ds, bytes_ok ds -> Forall bytes_ok (int_pieces neg ds).
Proof.
  intros neg ds Hds. unfold int_pieces. constructor.
  - destruct neg; [| constructor]. constructor; [lia| constructor].
  - destruct ds; [| constructor; [exact Hds| constructor]]. constructor; [constructor; [lia|constructor]|]. constructor; [constructor| constructor].
Qed.

Lemma conv_pieces_ok : forall c a, arg_ok a -> Forall bytes_ok (conv_pieces c a).
Proof.
  intros c a Ha. destruct c, a. all: cbn [conv_pieces]. all: cbv zeta.
  all: lazymatch goal with
       | |- Forall _ (int_pieces _ (dec_udigits _)) => apply int_pieces_ok; apply dec_udigits_ok
       | |- Forall _ (int_pieces _ (hex_udigits _)) => apply int_pieces_ok; apply hex_udigits_ok
       | |- Forall _ [[]; _] => constructor; [constructor|]; constructor; [first [exact Ha | constructor]| constructor]
       | _ => idtac
       end.
  (* [comment removed for export] *)
  constructor; [constructor|]. apply Forall_app. split.
  - destruct (_ <? 8); [| constructor]. constructor; [apply zeros_ok| constructor].
  - destruct (hex_udigits (u32 v)) eqn:E.
    + constructor; [constructor; [lia|constructor]|]. constructor; [constructor| constructor].
    + constructor; [| constructor]. rewrite <- E. apply hex_udigits_ok.
Qed.

Lemma fmt_pieces_ok : forall items args, Forall item_ok items -> Forall arg_ok args -> Forall bytes_ok (fmt_pieces items args).
Proof.
  induction items as [|i items IH]; intros args Hi Ha; cbn [fmt_pieces]; [constructor|].
  apply Forall_cons_iff in Hi as [H1 H2]. destruct i as [l|c|l].
  - constructor; [exact H1| apply IH; assumption].
  - constructor; [constructor|]. apply Forall_app. split.
    + apply conv_pieces_ok. destruct args as [|a args']; cbn; [exact I|]. apply Forall_cons_iff in Ha as [Ha _]. exact Ha.
    + apply IH; [exact H2|]. destruct args as [|a args']; cbn; [constructor|]. apply Forall_cons_iff in Ha as [_ Ha]. exact Ha.
  - constructor; [exact H1| constructor].
Qed.

Lemma fmt_output_ok : forall items args, Forall item_ok items -> Forall arg_ok args -> bytes_ok (fmt_output items args).
Proof. intros. unfold fmt_output. apply bytes_ok_concat. apply fmt_pieces_ok; assumption. Qed.

(* [comment removed for export] *)
Lemma snprintf_ok : forall n f args, items_okb (fmt f) = true -> Forall arg_ok args -> bytes_ok (Fmt.snprintf n f args).
Proof.
  intros n f args Hf Ha. unfold Fmt.snprintf, snprintf_out. apply bytes_ok_firstn. apply fmt_output_ok; [apply items_okb_ok; exact Hf| exact Ha].
Qed.

(* [comment removed for export] *)
Definition table_okb : bool := forallb (fun e => bytes_okb (str (snd e))) strerror_table && bytes_okb (str strerror_default).
Lemma table_okb_true : table_okb = true.
Proof. vm_compute. reflexivity. Qed.
Lemma strerror_ok : forall e, bytes_ok (strerror e).
Proof.
  intros e. unfold strerror.
  pose proof table_okb_true as T. unfold table_okb in T. apply andb_prop in T as [T1 T2].
  set (e' := if (0 <=? e) && (e <? STRERROR_N) then e else 0). clearbody e'.
  assert (GEN : forall t, forallb (fun p => bytes_okb (str (snd p))) t = true ->
            bytes_ok (str match table_lookup t e' with Some s => s | None => strerror_default end)).
  { induction t as [|[k s] t IH]; intros Ht; cbn.
    - apply bytes_okb_ok. exact T2.
    - cbn in Ht. apply andb_prop in Ht as [H1 H2]. destruct (k =? e'); [apply bytes_okb_ok; exact H1| apply IH; exact H2]. }
  apply GEN. exact T1.
Qed.
Lemma strerror_r_ok : forall e n, bytes_ok (snd (strerror_r e n)).
Proof.
  intros e n. unfold strerror_r. destruct (_ <? n); cbn [snd]; [apply strerror_ok|].
  destruct (0 <? n); [apply bytes_ok_firstn; apply strerror_ok| constructor].
Qed.

Lemma fmt_errmsg_ok : forall f args e, items_okb (fmt f) = true -> Forall arg_ok args -> bytes_ok (fmt_errmsg f args e).
Proof.
  intros f args e Hf Ha. unfold fmt_errmsg.
  destruct (_ <? _); [apply snprintf_ok; assumption|].
  apply bytes_ok_app; [apply snprintf_ok; assumption| apply bytes_ok_app].
  - apply bytes_okb_ok. vm_compute. reflexivity.
  - apply snprintf_ok; [vm_compute; reflexivity|]. constructor; [| constructor]. cbn [arg_ok]. apply strerror_r_ok.
Qed.

(* [comment removed for export] *)
Lemma args_ok_ints1 : forall a, Forall arg_ok [AInt a]. Proof. intros. repeat constructor. Qed.
Lemma args_ok_ints2 : forall a b, Forall arg_ok [AInt a; AInt b]. Proof. intros. repeat constructor. Qed.
Lemma args_ok_nil : Forall arg_ok ([] : list farg). Proof. constructor. Qed.

(* [comment removed for export] *)
Lemma bytes_ok_of_bytes : forall bs : list (bv 8), ~ In (Z_to_bv 8 0) bs -> bytes_ok (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; intros Hn; cbn [map]; [constructor|].
  constructor.
  - pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
    destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE]; [|lia]. exfalso. apply Hn. left. apply bv_eq. rewrite Z_to_bv_unsigned. rewrite E. reflexivity.
  - apply IH. intros Hi. apply Hn. right. exact Hi.
Qed.
Lemma args_ok_str1 : forall bs : list (bv 8), ~ In (Z_to_bv 8 0) bs -> Forall arg_ok [AStr (map bv_unsigned bs)].
Proof. intros bs Hn. constructor; [| constructor]. cbn. apply bytes_ok_of_bytes. exact Hn. Qed.
End FmtFacts.

(* [comment removed for export] *)
Module PPFacts.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Lemma swap_field_len : forall k off (d : list Z), 0 <= off -> length (swap_field k off d) = length d.
Proof.
  intros k off d Ho. unfold swap_field, buf_write_at, zslice, zfirstn, zskipn, zlength.
  rewrite !length_app, length_rev, !length_firstn, !length_skipn.
  rewrite Z2Nat.inj_add by lia. rewrite Nat2Z.id. lia.
Qed.

Ltac len_crunch :=
  repeat (cbn zeta; try (rewrite !swap_field_len by lia); try reflexivity;
          match goal with |- context [if ?c then _ else _] => destruct c end).

Lemma swap_pflog_header_len : forall hdr d, length (swap_pflog_header hdr d) = length d.
Proof. intros. unfold swap_pflog_header. len_crunch. Qed.

Lemma swap_socketcan_header_len : forall pr c l base d, 0 <= base -> length (swap_socketcan_header pr c l base d) = length d.
Proof. intros. unfold swap_socketcan_header. len_crunch. Qed.

Lemma swap_linux_sll_len : forall hdr d, length (swap_linux_sll_socketcan_header hdr d) = length d.
Proof. intros. unfold swap_linux_sll_socketcan_header. len_crunch; apply swap_socketcan_header_len; lia. Qed.
Lemma swap_linux_sll2_len : forall hdr d, length (swap_linux_sll2_socketcan_header hdr d) = length d.
Proof. intros. unfold swap_linux_sll2_socketcan_header. len_crunch; apply swap_socketcan_header_len; lia. Qed.

Lemma swap_usb_isodescs_len : forall fuel ndesc caplen i desc offset d, 0 <= desc ->
  length (swap_usb_isodescs fuel ndesc caplen i desc offset d) = length d.
Proof.
  induction fuel as [|fuel IH]; intros ndesc caplen i desc offset d Hd; [reflexivity|].
  cbn [swap_usb_isodescs]. len_crunch. rewrite IH by lia. rewrite !swap_field_len by lia. reflexivity.
Qed.

Lemma swap_linux_usb_header_len : forall hdr d b, length (swap_linux_usb_header hdr d b) = length d.
Proof.
  intros. unfold swap_linux_usb_header. len_crunch; rewrite ?swap_usb_isodescs_len by lia; rewrite ?swap_field_len by lia; reflexivity.
Qed.

Lemma swap_nflog_tlvs_len : forall fuel c l p d, 0 <= p -> length (swap_nflog_tlvs fuel c l p d) = length d.
Proof.
  induction fuel as [|fuel IH]; intros c l p d Hp; [reflexivity|].
  cbn [swap_nflog_tlvs].
  destruct (c <? 4); [reflexivity|]. cbn zeta.
  set (d1 := swap_field 2 p (swap_field 2 (p + 2) d)).
  set (size0 := get_le16 d1 p). set (size := if size0 mod 4 =? 0 then size0 else size0 + (4 - size0 mod 4)).
  destruct (size <? 4) eqn:E4; [subst d1; rewrite !swap_field_len by lia; reflexivity|].
  destruct ((c <? size) || (l <? size)); [subst d1; rewrite !swap_field_len by lia; reflexivity|].
  apply Z.ltb_ge in E4. rewrite IH by lia. subst d1. rewrite !swap_field_len by lia. reflexivity.
Qed.

Lemma swap_nflog_header_len : forall hdr d, length (swap_nflog_header hdr d) = length d.
Proof. intros. unfold swap_nflog_header. len_crunch. apply swap_nflog_tlvs_len. lia. Qed.

Lemma swap_pseudo_headers_len : forall lt hdr d, length (swap_pseudo_headers lt hdr d) = length d.
Proof.
  intros. unfold swap_pseudo_headers.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    auto using swap_pflog_header_len, swap_linux_sll_len, swap_linux_sll2_len, swap_linux_usb_header_len, swap_nflog_header_len.
Qed.

Theorem pp_length : forall lt sw hdr d, length (snd (pcapint_post_process lt sw hdr d)) = length d.
Proof. intros. unfold pcapint_post_process. cbn [snd]. destruct sw; [apply swap_pseudo_headers_len | reflexivity]. Qed.

Lemma fixup_usb_sec : forall hdr d, h_sec (fixup_usb_mmapped_len hdr d) = h_sec hdr /\ h_usec (fixup_usb_mmapped_len hdr d) = h_usec hdr
  /\ h_caplen (fixup_usb_mmapped_len hdr d) = h_caplen hdr
  /\ (h_len (fixup_usb_mmapped_len hdr d) = h_len hdr \/ h_len (fixup_usb_mmapped_len hdr d) = h_caplen hdr
      \/ (h_caplen hdr <= h_len (fixup_usb_mmapped_len hdr d) <= UINT_MAX)).
Proof.
  intros hdr d. unfold fixup_usb_mmapped_len.
  assert (U : forall a b, a <= UINT_MAX -> u_int_sum a b <= UINT_MAX).
  { intros a b Ha. unfold u_int_sum. destruct (Z.leb_spec b (UINT_MAX - a)); lia. }
  assert (L : incoming_isochronous_transfer_completed_len hdr d <= UINT_MAX).
  { unfold incoming_isochronous_transfer_completed_len. apply U. unfold iso_pseudo_header_len, u32, UINT_MAX. Z.div_mod_to_equations. lia. }
  set (LEN := incoming_isochronous_transfer_completed_len hdr d) in *.
  repeat match goal with |- context [if ?c then _ else _] =>
    lazymatch c with context [if _ then _ else _] => fail | _ => destruct c eqn:? end end;
    cbn in *;
    repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
                        | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H end;
    destruct hdr; cbn in *; repeat split; try reflexivity; try lia.
Qed.

Theorem pp_sec : forall lt sw hdr d,
  h_sec (fst (pcapint_post_process lt sw hdr d)) = h_sec hdr /\ h_usec (fst (pcapint_post_process lt sw hdr d)) = h_usec hdr.
Proof.
  intros. unfold pcapint_post_process. cbn [fst]. destruct (lt =? DLT_USB_LINUX_MMAPPED); [|split; reflexivity].
  pose proof (fixup_usb_sec hdr (if sw then swap_pseudo_headers lt hdr d else d)) as (A & B & _). split; assumption.
Qed.

Theorem pp_range : forall lt sw hdr d,
  0 <= h_caplen hdr <= Z.of_nat (length d) -> 0 <= h_len hdr < 2^32 -> Z.of_nat (length d) < 2^31 ->
  0 <= h_caplen (fst (pcapint_post_process lt sw hdr d)) < 2^32 /\ 0 <= h_len (fst (pcapint_post_process lt sw hdr d)) < 2^32.
Proof.
  intros lt sw hdr d Hc Hl Hd. unfold pcapint_post_process. cbn [fst]. destruct (lt =? DLT_USB_LINUX_MMAPPED); [|lia].
  pose proof (fixup_usb_sec hdr (if sw then swap_pseudo_headers lt hdr d else d)) as (_ & _ & C & D). unfold UINT_MAX in D. lia.
Qed.
End PPFacts.
