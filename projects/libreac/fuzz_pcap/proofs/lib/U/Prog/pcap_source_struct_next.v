From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel.
Import ListNotations.
Open Scope Z_scope.

Definition img_apart (a n : Z) : Prop := a + n <= 0x10000 \/ (symaddr ImgPages.Ubsan.top) <= a.

Definition fb (F : list byte) (i : Z) : Z := bv_unsigned (nth (Z.to_nat i) F (Z_to_bv 8 0)).

Definition w32le (b0 b1 b2 b3 : Z) : Z := b0 + 256 * b1 + 65536 * b2 + 16777216 * b3.

Definition hw (sw : bool) (F : list byte) (q j : Z) : Z :=
  if sw then w32le (fb F (q + j + 3)) (fb F (q + j + 2)) (fb F (q + j + 1)) (fb F (q + j))
  else w32le (fb F (q + j)) (fb F (q + j + 1)) (fb F (q + j + 2)) (fb F (q + j + 3)).

Inductive pkind := KEnd | KCutH | KEmpty | KFit | KCutFit | KBig0 | KBig | KCutBig.

(* libreac v1.9.0: pcap_source_next no longer prints the oversized-frame message
   ("pcap_source: skipping oversized frame ..."); its fprintf call, stderr load and format string are gone
   in every build (pcap-v190-next.md (sha256 b1d06d8683d6; internal record), pcap-v190-plain-ubsan-map.md (sha256 115d30ff9eea; internal record) section 1.3).
   So `chain` emits no output: an oversized record is skipped (KBig) or ends the call (KBig0, KCutBig) silently.
   Control flow, return values and stream positions are those of v1.8. *)

Section Chain.
Variables (sw : bool) (F : list byte) (cap : Z).

Definition flen : Z := Z.of_nat (length F).

Definition incl (q : Z) : Z := hw sw F q 8.
Definition orig (q : Z) : Z := hw sw F q 12.

Definition kind (q : Z) : pkind :=
  if flen - q =? 0 then KEnd
  else if flen - q <? 16 then KCutH
  else if incl q =? 0 then KEmpty
  else if incl q <=? cap then (if q + 16 + incl q <=? flen then KFit else KCutFit)
  else if cap =? 0 then KBig0
  else if q + 16 + incl q <=? flen then KBig else KCutBig.

Fixpoint chain (fuel : nat) (q : Z) (lh : option Z) : Z * list byte * option Z :=
  match fuel with
  | O => (q, [], lh)
  | S f =>
      match kind q with
      | KEmpty => chain f (q + 16) lh
      | KBig => let '(Q, o, l) := chain f (q + 16 + incl q) (Some q) in (Q, o, l)
      | KBig0 | KCutBig => (q, [], Some q)
      | KFit | KCutFit => (q, [], Some q)
      | KEnd | KCutH => (q, [], lh)
      end
  end.

Definition tagged (q : Z) : bool := (18 <=? incl q) && (fb F (q + 28) =? 129) && (fb F (q + 29) =? 0).

Definition rec_len (q : Z) : Z := if tagged q then incl q - 4 else incl q.

Definition rec_vid (q : Z) : Z := (256 * fb F (q + 30) + fb F (q + 31)) mod 4096.

Definition rec_ts (q : Z) : Z := hw sw F q 0 * 1000000 + hw sw F q 4.

Definition rec_raw (q : Z) : list byte := firstn (Z.to_nat (incl q)) (skipn (Z.to_nat (q + 16)) F).

Definition rec_bytes (q : Z) : list byte :=
  let B := rec_raw q in
  if tagged q then firstn 12 B ++ firstn (Z.to_nat (incl q - 16)) (skipn 16 B) ++ skipn (Z.to_nat (incl q - 4)) B
  else B.

Definition res_of (q : Z) : Z :=
  match kind q with
  | KEnd => 0
  | KFit => rec_len q
  | _ => -1
  end.

Definition pos_of (q : Z) : Z :=
  match kind q with
  | KFit => q + 16 + incl q
  | KBig0 => q + 16
  | _ => flen
  end.

End Chain.

Definition psn_chain (sw : bool) (F : list byte) (cap p : Z) : Z * list byte * option Z :=
  chain sw F cap (S (length F)) p None.

Definition psn_out (h : Z) (sw : bool) (F : list byte) (cap p : Z) : list byte :=
  if h =? 0 then [] else snd (fst (psn_chain sw F cap p)).

Lemma chain_out_nil (sw : bool) (F : list byte) (cap : Z) (fuel : nat) :
  forall q lh, snd (fst (chain sw F cap fuel q lh)) = [].
Proof.
  induction fuel as [|f IH]; intros q lh; simpl; [reflexivity|].
  destruct (kind sw F cap q); simpl; auto.
  specialize (IH (q + 16 + incl sw F q) (Some q)).
  destruct (chain sw F cap f (q + 16 + incl sw F q) (Some q)) as [[Q o] l]; simpl in *; exact IH.
Qed.

Lemma psn_out_nil (h : Z) (sw : bool) (F : list byte) (cap p : Z) : psn_out h sw F cap p = [].
Proof. unfold psn_out, psn_chain. destruct (h =? 0); [reflexivity | apply chain_out_nil]. Qed.

Definition psn_q (sw : bool) (F : list byte) (cap p : Z) : Z := fst (fst (psn_chain sw F cap p)).

Definition psn_lh (sw : bool) (F : list byte) (cap p : Z) : option Z := snd (psn_chain sw F cap p).

Definition is_fit (k : pkind) : bool := match k with KFit => true | _ => false end.

Definition lol_of (sw : bool) (F : list byte) (lh : option Z) (lol : word) : word :=
  match lh with Some q => wz (orig sw F q) | None => lol end.

Definition vt_of (sw : bool) (F : list byte) (cap q : Z) (lvt : word) : word :=
  if is_fit (kind sw F cap q) then (if tagged sw F q then wz 1 else wz 0) else lvt.

Definition vid_of (sw : bool) (F : list byte) (cap q : Z) (lvid : word) : word :=
  if is_fit (kind sw F cap q) then (if tagged sw F q then wz (rec_vid F q) else wz 0) else lvid.

Definition ts_of (sw : bool) (F : list byte) (cap q : Z) (tsv : word) : word :=
  if is_fit (kind sw F cap q) then wz (rec_ts sw F q) else tsv.
