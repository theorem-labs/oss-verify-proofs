(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StrerrorTable StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Lemma length_list_ascii fs : length (String.list_ascii_of_string fs) = String.length fs.
Proof. induction fs as [|c fs IH]; cbn; [reflexivity| now rewrite IH]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition item_bytes_in (P : Z -> Prop) (it : fitem) : Prop :=
  match it with FLit l => Forall P l | FConv _ => True | FBad l => Forall P l end.

Lemma take_lit_sub : forall s l r, take_lit s = (l, r) -> s = l ++ r.
Proof.
  induction s as [|c s IH]; intros l r E; cbn in E.
  - inversion E; subst. reflexivity.
  - destruct (c =? 37).
    + inversion E; subst. reflexivity.
    + destruct (take_lit s) as [l0 r0] eqn:E0. inversion E; subst.
      cbn. f_equal. apply IH. reflexivity.
Qed.

Lemma parse_conv_suffix : forall s c r, parse_conv s = Some (c, r) -> exists p, s = p ++ r.
Proof.
  intros s c r E. unfold parse_conv in E.
  repeat (cbn in E; lazymatch type of E with
          | context [match ?x with _ => _ end] => is_var x; destruct x; try discriminate E
          | _ => fail end).
  all: inversion E; subst.
  all: lazymatch goal with
       | |- exists p, ?a :: ?b :: ?c :: ?t = p ++ ?t => exists [a; b; c]; reflexivity
       | |- exists p, ?a :: ?b :: ?t = p ++ ?t => exists [a; b]; reflexivity
       | |- exists p, ?a :: ?t = p ++ ?t => exists [a]; reflexivity
       end.
Qed.

Lemma parse_fmt_aux_bytes : forall (P : Z -> Prop) fuel s,
  Forall P s -> Forall (item_bytes_in P) (parse_fmt_aux fuel s).
Proof.
  induction fuel as [|fuel IH]; intros s Hs; cbn [parse_fmt_aux].
  - destruct s; constructor; [exact Hs| constructor].
  - destruct s as [|c s']; [constructor|].
    destruct (Z.eq_dec c 37) as [->|NE].
    + cbn. destruct (parse_conv s') as [[cv r]|] eqn:E.
      * constructor; [exact I|]. apply IH. destruct (parse_conv_suffix _ _ _ E) as [p ->].
        apply Forall_inv_tail in Hs. apply Forall_app in Hs. tauto.
      * constructor; [exact Hs| constructor].
    + replace (match c with 37 => _ | _ => let (l, r) := take_lit (c :: s') in FLit l :: parse_fmt_aux fuel r end)
        with (let (l, r) := take_lit (c :: s') in FLit l :: parse_fmt_aux fuel r).
      2:{ destruct c as [|p|p]; try reflexivity. repeat (destruct p; try reflexivity). exfalso; apply NE; reflexivity. }
      destruct (take_lit (c :: s')) as [l r] eqn:E.
      pose proof (take_lit_sub _ _ _ E) as Hsplit.
      rewrite Hsplit in Hs. apply Forall_app in Hs as [Hl Hr].
      constructor; [exact Hl| apply IH; exact Hr].
Qed.

Lemma str_bytes : forall s, Forall (fun z => 0 <= z < 256) (str s).
Proof.
  intros s. unfold str. apply Forall_map. apply Forall_forall. intros a _.
  pose proof (Ascii.N_ascii_bounded a). lia.
Qed.

Lemma fmt_bytes : forall fs, Forall (item_bytes_in (fun z => 0 <= z < 256)) (fmt fs).
Proof. intros fs. unfold fmt, parse_fmt. apply parse_fmt_aux_bytes. apply str_bytes. Qed.

(* [comment removed for export] *)
Lemma items_ok_okb : forall its args,
  Forall (item_bytes_in (fun z => 0 <= z < 256)) its -> items_ok its args = true -> items_okb its = true.
Proof.
  induction its as [|it its IH]; intros args HB HO; [reflexivity|].
  apply Forall_cons_iff in HB as [HBi HB]. cbn [items_ok] in HO. change (items_okb (it :: its)) with (item_okb it && items_okb its)%bool.
  destruct it as [l|c|l]; cbn [item_okb].
  - apply andb_prop in HO as [Hl HO]. rewrite (IH _ HB HO), andb_true_r.
    unfold bytes_okb. apply forallb_forall. intros z Hz.
    pose proof (proj1 (forallb_forall _ _) Hl z Hz) as Hz'. cbn in Hz'.
    pose proof (proj1 (Forall_forall _ _) HBi z Hz) as Hb. cbn in Hb.
    apply andb_prop in Hz' as [H0 _]. destruct (Z.eqb_spec z 0); [discriminate|].
    apply andb_true_intro; split; [apply Z.ltb_lt; lia| apply Z.ltb_lt; lia].
  - destruct args as [|a args']; [discriminate|]. apply andb_prop in HO as [_ HO]. exact (IH _ HB HO).
  - discriminate.
Qed.

Lemma fmt_ok_items_okb : forall fs args, fmt_ok fs args = true -> items_okb (fmt fs) = true.
Proof.
  intros fs args H. unfold fmt_ok in H. apply andb_prop in H as [H _].
  exact (items_ok_okb _ _ (fmt_bytes fs) H).
Qed.

(* [comment removed for export] *)
Lemma map_b8_no_nul : forall l, bytes_ok l -> ~ In (Z_to_bv 8 0) (map b8 l).
Proof.
  induction l as [|z l IH]; intros HB Hin; [exact Hin|].
  apply Forall_cons_iff in HB as [Hz HB]. cbn [map] in Hin. destruct Hin as [E|Hin]; [| exact (IH HB Hin)].
  unfold b8 in E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_small in E by (unfold bv_modulus; cbn; lia). lia.
Qed.
Lemma map_unsigned_b8 : forall l, bytes_ok l -> map bv_unsigned (map b8 l) = l.
Proof.
  induction l as [|z l IH]; intros HB; [reflexivity|]. apply Forall_cons_iff in HB as [Hz HB]. cbn [map]. f_equal; [| exact (IH HB)].
  unfold b8. apply Z_to_bv_small. unfold bv_modulus. cbn. lia.
Qed.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Lemma farg_words_ok : forall {hptr} tls L RNG FL (CL : list (@cblock hptr)) SP D dn m args ws,
  Forall2 (farg_word tls L RNG FL CL SP D dn m) args ws -> Forall arg_ok args.
Proof.
  intros hptr tls L RNG FL CL SP D dn m args ws FW. induction FW as [|a w args' ws' Ha _ IH]; constructor; [| exact IH].
  destruct a as [v|cs]; cbn [arg_ok farg_word] in *; [exact Logic.I|].
  destruct Ha as (P & bs & slack & _ & _ & NN & -> & _). apply bytes_ok_of_bytes. exact NN.
Qed.
End CANSEC1.

(* [comment removed for export] *)
Lemma snprintf_length_le : forall n f args, (1 <= n)%Z -> (Z.of_nat (length (Fmt.snprintf n f args)) <= n - 1)%Z.
Proof. intros n f args Hn. unfold Fmt.snprintf, snprintf_out. rewrite length_firstn. lia. Qed.
Definition table_lenb : bool := forallb (fun e => (length (str (snd e)) <=? 49)%nat) strerror_table && (length (str strerror_default) <=? 49)%nat.
Lemma table_lenb_true : table_lenb = true. Proof. vm_compute. reflexivity. Qed.
Lemma strerror_len : forall e, (length (Fmt.strerror e) <= 49)%nat.
Proof.
  intros e. unfold strerror. pose proof table_lenb_true as T. unfold table_lenb in T. apply andb_prop in T as [T1 T2].
  set (e' := if (0 <=? e) && (e <? STRERROR_N) then e else 0). clearbody e'.
  assert (GEN : forall t, forallb (fun p => (length (str (snd p)) <=? 49)%nat) t = true ->
            (length (str match table_lookup t e' with Some s => s | None => strerror_default end) <= 49)%nat).
  { induction t as [|[k s] t IH]; intros Ht; cbn.
    - apply Nat.leb_le. exact T2.
    - cbn in Ht. apply andb_prop in Ht as [H1 H2]. destruct (k =? e'); [apply Nat.leb_le; exact H1| apply IH; exact H2]. }
  apply GEN. exact T1.
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StrerrorTable OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Lemma length_list_ascii fs : length (String.list_ascii_of_string fs) = String.length fs.
Proof. induction fs as [|c fs IH]; cbn; [reflexivity| now rewrite IH]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition item_bytes_in (P : Z -> Prop) (it : fitem) : Prop :=
  match it with FLit l => Forall P l | FConv _ => True | FBad l => Forall P l end.

Lemma take_lit_sub : forall s l r, take_lit s = (l, r) -> s = l ++ r.
Proof.
  induction s as [|c s IH]; intros l r E; cbn in E.
  - inversion E; subst. reflexivity.
  - destruct (c =? 37).
    + inversion E; subst. reflexivity.
    + destruct (take_lit s) as [l0 r0] eqn:E0. inversion E; subst.
      cbn. f_equal. apply IH. reflexivity.
Qed.

Lemma parse_conv_suffix : forall s c r, parse_conv s = Some (c, r) -> exists p, s = p ++ r.
Proof.
  intros s c r E. unfold parse_conv in E.
  repeat (cbn in E; lazymatch type of E with
          | context [match ?x with _ => _ end] => is_var x; destruct x; try discriminate E
          | _ => fail end).
  all: inversion E; subst.
  all: lazymatch goal with
       | |- exists p, ?a :: ?b :: ?c :: ?t = p ++ ?t => exists [a; b; c]; reflexivity
       | |- exists p, ?a :: ?b :: ?t = p ++ ?t => exists [a; b]; reflexivity
       | |- exists p, ?a :: ?t = p ++ ?t => exists [a]; reflexivity
       end.
Qed.

Lemma parse_fmt_aux_bytes : forall (P : Z -> Prop) fuel s,
  Forall P s -> Forall (item_bytes_in P) (parse_fmt_aux fuel s).
Proof.
  induction fuel as [|fuel IH]; intros s Hs; cbn [parse_fmt_aux].
  - destruct s; constructor; [exact Hs| constructor].
  - destruct s as [|c s']; [constructor|].
    destruct (Z.eq_dec c 37) as [->|NE].
    + cbn. destruct (parse_conv s') as [[cv r]|] eqn:E.
      * constructor; [exact I|]. apply IH. destruct (parse_conv_suffix _ _ _ E) as [p ->].
        apply Forall_inv_tail in Hs. apply Forall_app in Hs. tauto.
      * constructor; [exact Hs| constructor].
    + replace (match c with 37 => _ | _ => let (l, r) := take_lit (c :: s') in FLit l :: parse_fmt_aux fuel r end)
        with (let (l, r) := take_lit (c :: s') in FLit l :: parse_fmt_aux fuel r).
      2:{ destruct c as [|p|p]; try reflexivity. repeat (destruct p; try reflexivity). exfalso; apply NE; reflexivity. }
      destruct (take_lit (c :: s')) as [l r] eqn:E.
      pose proof (take_lit_sub _ _ _ E) as Hsplit.
      rewrite Hsplit in Hs. apply Forall_app in Hs as [Hl Hr].
      constructor; [exact Hl| apply IH; exact Hr].
Qed.

Lemma str_bytes : forall s, Forall (fun z => 0 <= z < 256) (str s).
Proof.
  intros s. unfold str. apply Forall_map. apply Forall_forall. intros a _.
  pose proof (Ascii.N_ascii_bounded a). lia.
Qed.

Lemma fmt_bytes : forall fs, Forall (item_bytes_in (fun z => 0 <= z < 256)) (fmt fs).
Proof. intros fs. unfold fmt, parse_fmt. apply parse_fmt_aux_bytes. apply str_bytes. Qed.

(* [comment removed for export] *)
Lemma items_ok_okb : forall its args,
  Forall (item_bytes_in (fun z => 0 <= z < 256)) its -> items_ok its args = true -> items_okb its = true.
Proof.
  induction its as [|it its IH]; intros args HB HO; [reflexivity|].
  apply Forall_cons_iff in HB as [HBi HB]. cbn [items_ok] in HO. change (items_okb (it :: its)) with (item_okb it && items_okb its)%bool.
  destruct it as [l|c|l]; cbn [item_okb].
  - apply andb_prop in HO as [Hl HO]. rewrite (IH _ HB HO), andb_true_r.
    unfold bytes_okb. apply forallb_forall. intros z Hz.
    pose proof (proj1 (forallb_forall _ _) Hl z Hz) as Hz'. cbn in Hz'.
    pose proof (proj1 (Forall_forall _ _) HBi z Hz) as Hb. cbn in Hb.
    apply andb_prop in Hz' as [H0 _]. destruct (Z.eqb_spec z 0); [discriminate|].
    apply andb_true_intro; split; [apply Z.ltb_lt; lia| apply Z.ltb_lt; lia].
  - destruct args as [|a args']; [discriminate|]. apply andb_prop in HO as [_ HO]. exact (IH _ HB HO).
  - discriminate.
Qed.

Lemma fmt_ok_items_okb : forall fs args, fmt_ok fs args = true -> items_okb (fmt fs) = true.
Proof.
  intros fs args H. unfold fmt_ok in H. apply andb_prop in H as [H _].
  exact (items_ok_okb _ _ (fmt_bytes fs) H).
Qed.

(* [comment removed for export] *)
Lemma map_b8_no_nul : forall l, bytes_ok l -> ~ In (Z_to_bv 8 0) (map b8 l).
Proof.
  induction l as [|z l IH]; intros HB Hin; [exact Hin|].
  apply Forall_cons_iff in HB as [Hz HB]. cbn [map] in Hin. destruct Hin as [E|Hin]; [| exact (IH HB Hin)].
  unfold b8 in E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_small in E by (unfold bv_modulus; cbn; lia). lia.
Qed.
Lemma map_unsigned_b8 : forall l, bytes_ok l -> map bv_unsigned (map b8 l) = l.
Proof.
  induction l as [|z l IH]; intros HB; [reflexivity|]. apply Forall_cons_iff in HB as [Hz HB]. cbn [map]. f_equal; [| exact (IH HB)].
  unfold b8. apply Z_to_bv_small. unfold bv_modulus. cbn. lia.
Qed.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Lemma farg_words_ok : forall {hptr} tls L RNG FL (CL : list (@cblock hptr)) SP D dn m args ws,
  Forall2 (farg_word tls L RNG FL CL SP D dn m) args ws -> Forall arg_ok args.
Proof.
  intros hptr tls L RNG FL CL SP D dn m args ws FW. induction FW as [|a w args' ws' Ha _ IH]; constructor; [| exact IH].
  destruct a as [v|cs]; cbn [arg_ok farg_word] in *; [exact Logic.I|].
  destruct Ha as (P & bs & slack & _ & _ & NN & -> & _). apply bytes_ok_of_bytes. exact NN.
Qed.
End CANSEC1.

(* [comment removed for export] *)
Lemma snprintf_length_le : forall n f args, (1 <= n)%Z -> (Z.of_nat (length (Fmt.snprintf n f args)) <= n - 1)%Z.
Proof. intros n f args Hn. unfold Fmt.snprintf, snprintf_out. rewrite length_firstn. lia. Qed.
Definition table_lenb : bool := forallb (fun e => (length (str (snd e)) <=? 49)%nat) strerror_table && (length (str strerror_default) <=? 49)%nat.
Lemma table_lenb_true : table_lenb = true. Proof. vm_compute. reflexivity. Qed.
Lemma strerror_len : forall e, (length (Fmt.strerror e) <= 49)%nat.
Proof.
  intros e. unfold strerror. pose proof table_lenb_true as T. unfold table_lenb in T. apply andb_prop in T as [T1 T2].
  set (e' := if (0 <=? e) && (e <? STRERROR_N) then e else 0). clearbody e'.
  assert (GEN : forall t, forallb (fun p => (length (str (snd p)) <=? 49)%nat) t = true ->
            (length (str match table_lookup t e' with Some s => s | None => strerror_default end) <= 49)%nat).
  { induction t as [|[k s] t IH]; intros Ht; cbn.
    - apply Nat.leb_le. exact T2.
    - cbn in Ht. apply andb_prop in Ht as [H1 H2]. destruct (k =? e'); [apply Nat.leb_le; exact H1| apply IH; exact H2]. }
  apply GEN. exact T1.
Qed.
End TwB.
