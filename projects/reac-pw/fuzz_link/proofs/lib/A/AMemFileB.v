(** * reac-pw/fuzz_link (asan, image A): the memory FILE at link's allocator instance [PcapB].

    [amf_gi_ledger_kept] (AMemFile.v) asks three facts of every byte of the three heads and the three stdio words:
    an image byte, outside the allocator's statics, outside errno. This file proves them for every [B] with link's
    statics and errno (AF0m.v [Tfib_owned_static], 77 ranges, and [TFIB_ERRNO] 0x631b6c; link's [PcapB], lib/A/AD2l.v
    :28 / :39, has both by reflexivity) and link's image, and states [link_amf_gi_ledger_kept]: the kept state
    survives every callee of link's A walks whose footprint is closed (no sink token) and avoids the kept block, with
    the journal's head the A image's ([link_asink_head], passed by name). It is the lemma a callee site applies.
    The [B] is a parameter so this file does not wait on AD2l.v. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK04 YA0i YA0n YP09 YI04 YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AMemFile AMemFileT06.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Lemma exists_in_zr_b : forall a l, Exists (in_zr a) l ->
  existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l = true.
Proof.
  intros a l H. apply existsb_exists. apply Exists_exists in H as (r & Hr & Hz). unfold in_zr in Hz.
  exists r. split; [exact Hr|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma range_off_owned : forall lo n,
  forallb (fun k => negb (existsb (fun r => (fst r <=? lo + Z.of_nat k) && (lo + Z.of_nat k <? fst r + snd r))
    Tfib_owned_static)) (seq 0 n) = true ->
  forall a, lo <= a < lo + Z.of_nat n -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros lo n H a Ha Hx. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (a - lo)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. replace (lo + (a - lo)) with a in H by lia.
  rewrite (exists_in_zr_b a _ Hx) in H. discriminate.
Qed.

(** The premise of [amf_gi_ledger_kept] at link's statics, errno and image. *)
Lemma link_amf_premise : forall B, as_owned_static B = Tfib_owned_static -> as_errno B = TFIB_ERRNO ->
  forall a, amf_head_addr link_amf a \/ amf_env_addr link_amf a ->
  in_img tfibsegs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros B HO HE a Ha. split; [exact (link_amf_in_img a Ha)|].
  rewrite HO, HE.
  cbv [amf_head_addr amf_env_addr amf_ofl_head amf_sink_addr amf_say_addr amf_threaded amf_need_locks
    amf_ofl_lock link_amf] in Ha.
  split.
  - destruct Ha as [[H | [H | H]] | [H | [H | H]]].
    + apply (range_off_owned 0x62fec0 8); [vm_compute; reflexivity | cbn; lia].
    + apply (range_off_owned 0x6312e0 8); [vm_compute; reflexivity | cbn; lia].
    + apply (range_off_owned 0x652308 8); [vm_compute; reflexivity | cbn; lia].
    + apply (range_off_owned 0x651ea1 1); [vm_compute; reflexivity | cbn; lia].
    + apply (range_off_owned 0x651ea3 1); [vm_compute; reflexivity | cbn; lia].
    + apply (range_off_owned 0x652300 4); [vm_compute; reflexivity | cbn; lia].
  - unfold TFIB_ERRNO. lia.
Qed.

Section k.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(** The kept state across a callee of link's A walks (closed footprint, kept block avoided). *)
Lemma link_amf_gi_ledger_kept : forall B, as_owned_static B = Tfib_owned_static -> as_errno B = TFIB_ERRNO ->
  forall STK sp0 FP ly S (W : world tfibsegs) mem md own ly' S' (W' : world tfibsegs) mem' md' k T,
  YCbq.ajournal (SK := link_asink_head) tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  ~ YI16.sink_open_fp FP -> amf_fp_avoids FP T ->
  amf_gi_ledger B tfibsegs link_amf ly S T (rd W mem) -> amf_env tfibsegs link_amf (rd W mem) ->
  amf_gi_ledger B tfibsegs link_amf ly' S' T (rd W' mem') /\ amf_env tfibsegs link_amf (rd W' mem').
Proof.
  intros B HO HE STK sp0 FP ly S W mem md own ly' S' W' mem' md' k T HJ Hc Hav HG He.
  exact (amf_gi_ledger_kept (SK := link_asink_head) tfibsegs B link_amf STK sp0 FP ly S W mem md own ly' S' W'
    mem' md' k T HJ Hc (link_amf_premise B HO HE) Hav HG He).
Qed.

End k.
