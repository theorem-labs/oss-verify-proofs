(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Stdio/PFreadM.v, with its module paths and module names changed; 272 of its 298 lines of code are new or changed and 163 lines of the source are left out. *)
(* pcap_source_next on the ASan builds of libreac v1.9.0: the IMAGE-FREE part of the statement
   and of the phase data, shared by the asan build (lib/A) and the asan-ubsan build (lib/B).

   WHY THIS FILE. A lib/B file's whole Require closure may hold only lib/B files, the core
   (lib/Reusable) and image-free lib/A files (porter 01:25Z). lib/A/Prog/PcapSourceNextDefs.v
   Requires the asan image's listing and instance (PcapSyms, PcapList, PcapAddr, PcapPa, PcapPaLib),
   so the shared text lives here instead: the contract tpcap_source_next_specX / _post and every
   definition it uses (nx_ps_at, nx_wr_ok, nx_kept, nx_wrset, nx_fin), the lift of the model
   (nxF, nx_q .. nx_tsv), the record loop's model clause (nx_chain_inv and its lemmas), and the
   frame and struct constants the two builds share. PcapSourceNextDefs.v Requires this file and
   keeps the asan image's own data (the machine frame, the spill slots, the cut pcs, the listing
   checks, the phase layer over PAImg); the instruction addresses behind each constant below are
   cited there, on the asan pin.

   The text names no image: it Requires only lib/Reusable, lib/A/Prog/PcapBase.v (image-free: the
   read-only range and arodata_okP, copied from cgif's YC20.v), lib/A/Stdio/PSource.v and
   PSourceMeta.v, and Pau's model lib/Prog/pcap_source_struct_next.v (PSN), used unchanged. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
(* Pau's address-free model of this function, used unchanged. REQUIRED, never Imported: lib/Lib's
   mkst empties the floating-point state, so a file that states against the core's cfg_at must take
   getr / mkst / seg_rom from YK11 only (a Theorem Labs lane 21:36Z, found by a Theorem Labs lane). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct_next.
Module PSN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the frame on the side stack: the same in both builds (the prologue asks
   __asan_stack_malloc_0 for 0x40 bytes, a class-0 slot, in both) ---- *)

Definition NX_CID : Z := 0.               (* the slot class: __asan_stack_malloc_0 *)
Definition NX_FREQ : Z := 64.             (* the request, a0 := 0x40 *)
Definition NX_FRAME : Z := 64.            (* the slot, fs_frame_bytes 0 *)
Definition NX_NSH : nat := 8%nat.         (* its shadow bytes *)
(* The frame's header: ASan's live-frame magic at F (then, at F + 8 and F + 16, the frame's
   description string and the function's own address, which are image data: PcapSourceNextDefs.v). *)
Definition NX_MAGIC : Z := 0x41b58ab3.
(* What the epilogue writes when it gives the frame back: the retired-frame magic at F, and, for a
   side-stack frame, 0 through the flag pointer the slot keeps in its last word. *)
Definition NX_RETIRED : Z := 0x45e0360e.
Definition NX_FLAGPTR : Z := 56.

(* ---- the frame's one object: the 16-byte record header `ph` ---- *)

Definition NO_PH : Z := 32.               (* ph = F + 32 *)
Definition NX_PH_LEN : Z := 16.           (* the header fread's nm *)

(* ---- the frame's shadow ---- *)

(* The 8 shadow bytes as the prologue leaves them: 0xf1 the left redzone (F+0..31), 0xf8 `ph` out
   of scope (F+32..47), 0xf3 the right redzone (F+48..63). *)
Definition NSH_entry : list Z := [241;241;241;241; 248;248; 243;243].

Definition nsh_set (sh : list Z) (lo n : nat) (v : Z) : list Z :=
  firstn lo sh ++ repeat v n ++ skipn (lo + n) sh.
(* `ph` in scope, at the head of every turn of the record loop. *)
Definition NSH_ph : list Z := nsh_set NSH_entry 4 2 0.
(* `ph` out of scope again: at the end of a skipped record and at the exit; both give NSH_entry
   back. *)
Definition NSH_out (sh : list Z) : list Z := nsh_set sh 4 2 248.
(* The frame given back: every shadow byte 0xf5 for a side-stack frame, every shadow byte 0 for a
   frame on the machine stack. *)
Definition NSH_retired : list Z := repeat 245 8.
Definition NSH_machine : list Z := repeat 0 8.

Lemma NSH_entry_len : length NSH_entry = NX_NSH.
Proof. reflexivity. Qed.
Lemma NX_FRAME_slot : fs_frame_bytes NX_CID = NX_FRAME /\ NX_FREQ <= NX_FRAME /\ Z.of_nat NX_NSH = NX_FRAME / 8.
Proof. split; [vm_compute; reflexivity|]. split; [unfold NX_FREQ, NX_FRAME; lia | vm_compute; reflexivity]. Qed.
Lemma NSH_out_ph : NSH_out NSH_ph = NSH_entry.
Proof. reflexivity. Qed.

(* ---- the object layout of `struct pcap_source` (24 bytes), as the code reads and writes it: the
   same source, so the same in both builds ---- *)

Definition PS_F_OFF : Z := 0.     (* FILE *f        *)
Definition PS_SW_OFF : Z := 8.    (* int swapped    *)
Definition PS_OL_OFF : Z := 12.   (* uint32 orig    *)
Definition PS_VT_OFF : Z := 16.   (* int vtag       *)
Definition PS_VID_OFF : Z := 20.  (* uint16 vid     *)
Definition PS_LEN : Z := 24.      (* the whole struct, as the harness memsets it *)

(* Its events: none. The three fread calls and the memmove allocate and free nothing. *)
Definition EV_NEXT : Z := 0.
(* The record buffer the harness hands over is `cap ? cap : 1` bytes and cap is at most 2040
   (8 x the first input byte; a Theorem Labs lane's pcap-sizes.md (sha256 28001d79f5f0; internal record)). *)
Definition NX_CAP_MAX : Z := 2040.
Definition nx_bufn (cap : Z) : Z := Z.max cap 1.


(* ---------------------------------------------------------------------------------------------- *)
(* Pau's model, lifted to the `list Z` the read-stream predicate uses                               *)
(* ---------------------------------------------------------------------------------------------- *)

(* The stream's content as the model reads it. PSource states the content as a list of Z with
   bytes_ok; the model indexes a list of byte. *)
Definition nxF (C : list Z) : list byte := bytesZ C.

(* Where the walk of the whole call ends up in the file, and what it hands back. The arguments are
   the byte-swap flag, the content, the record buffer's capacity and the caller-consumed count. *)
Definition nx_q (sw : bool) (C : list Z) (cap p : Z) : Z := PSN.psn_q sw (nxF C) cap p.
Definition nx_lh (sw : bool) (C : list Z) (cap p : Z) : option Z := PSN.psn_lh sw (nxF C) cap p.
Definition nx_kind (sw : bool) (C : list Z) (cap p : Z) : PSN.pkind :=
  PSN.kind sw (nxF C) cap (nx_q sw C cap p).
Definition nx_fit (sw : bool) (C : list Z) (cap p : Z) : bool := PSN.is_fit (nx_kind sw C cap p).
Definition nx_res (sw : bool) (C : list Z) (cap p : Z) : Z :=
  PSN.res_of sw (nxF C) cap (nx_q sw C cap p).
Definition nx_pos (sw : bool) (C : list Z) (cap p : Z) : Z :=
  PSN.pos_of sw (nxF C) cap (nx_q sw C cap p).
(* The record's length in the buffer (incl, or incl - 4 once the VLAN tag is stripped). *)
Definition nx_reclen (sw : bool) (C : list Z) (cap p : Z) : Z := PSN.rec_len sw (nxF C) (nx_q sw C cap p).
(* The bytes the call leaves at the head of the buffer when the record fits. *)
Definition nx_rec (sw : bool) (C : list Z) (cap p : Z) : list Z :=
  map (fun b : byte => bv_unsigned b) (PSN.rec_bytes sw (nxF C) (nx_q sw C cap p)).
(* The four fields of the caller's struct, as the call leaves them: the last non-empty record's
   original length (the field is untouched while every record seen was empty), and the VLAN tag,
   VLAN id and timestamp, which only a record that fits writes. *)
Definition nx_orig (sw : bool) (C : list Z) (cap p lol : Z) : Z :=
  match nx_lh sw C cap p with Some q => PSN.orig sw (nxF C) q | None => lol end.
Definition nx_vtag (sw : bool) (C : list Z) (cap p lvt : Z) : Z :=
  if nx_fit sw C cap p then (if PSN.tagged sw (nxF C) (nx_q sw C cap p) then 1 else 0) else lvt.
Definition nx_vid (sw : bool) (C : list Z) (cap p lvid : Z) : Z :=
  if nx_fit sw C cap p
  then (if PSN.tagged sw (nxF C) (nx_q sw C cap p) then PSN.rec_vid (nxF C) (nx_q sw C cap p) else 0)
  else lvid.
Definition nx_tsv (sw : bool) (C : list Z) (cap p tsv : Z) : Z :=
  if nx_fit sw C cap p then PSN.rec_ts sw (nxF C) (nx_q sw C cap p) else tsv.

Lemma nxF_length : forall C, length (nxF C) = length C.
Proof. intros C. apply length_map. Qed.

(* ---- the record loop's model clause ---- *)

(* The model, run from (q, lh) with `fuel` steps, ends where it ends from the call's start; the
   fuel bound says it never runs out before the code does (a KEmpty or KBig step moves q forward
   by at least 16, and each spends one unit). The start has fuel = S (length F) (psn_chain). *)
Definition nx_chain_inv (sw : bool) (F : list byte) (cap p q : Z) (lh : option Z) : Prop :=
  exists fuel : nat, Z.of_nat (length F) - q < 16 * Z.of_nat fuel /\
    PSN.chain sw F cap fuel q lh = PSN.psn_chain sw F cap p.

Lemma nx_chain_start : forall sw F cap p, 0 <= p -> nx_chain_inv sw F cap p p None.
Proof.
intros sw F cap p Hp. exists (S (length F)). split; [rewrite Nat2Z.inj_succ; lia | reflexivity].
Qed.

Lemma nx_chain_fuel : forall sw F cap p q lh,
  nx_chain_inv sw F cap p q lh -> q <= Z.of_nat (length F) ->
  exists f, PSN.chain sw F cap (S f) q lh = PSN.psn_chain sw F cap p /\
    Z.of_nat (length F) - q < 16 * Z.of_nat (S f).
Proof.
intros sw F cap p q lh (fuel & Hb & Hc) Hq.
destruct fuel as [|f]; [exfalso; cbn [Z.of_nat] in Hb; lia|].
exists f. split; assumption.
Qed.

(* What a KEmpty and a KBig header say (PSN.kind). *)
Lemma nx_kind_empty : forall sw F cap q, PSN.kind sw F cap q = PSN.KEmpty ->
  PSN.incl sw F q = 0 /\ 16 <= Z.of_nat (length F) - q.
Proof.
intros sw F cap q. unfold PSN.kind, PSN.flen.
destruct (Z.of_nat (length F) - q =? 0) eqn:A; [intros Hk; discriminate Hk|].
destruct (Z.of_nat (length F) - q <? 16) eqn:Bq; [intros Hk; discriminate Hk|].
destruct (PSN.incl sw F q =? 0) eqn:C.
- intros _. apply Z.ltb_ge in Bq. apply Z.eqb_eq in C. lia.
- destruct (PSN.incl sw F q <=? cap);
    [destruct (q + 16 + PSN.incl sw F q <=? Z.of_nat (length F)); intros Hk; discriminate Hk|].
  destruct (cap =? 0); [intros Hk; discriminate Hk|].
  destruct (q + 16 + PSN.incl sw F q <=? Z.of_nat (length F)); intros Hk; discriminate Hk.
Qed.

Lemma nx_kind_big : forall sw F cap q, PSN.kind sw F cap q = PSN.KBig ->
  cap < PSN.incl sw F q /\ cap <> 0 /\ q + 16 + PSN.incl sw F q <= Z.of_nat (length F) /\
  16 <= Z.of_nat (length F) - q.
Proof.
intros sw F cap q. unfold PSN.kind, PSN.flen.
destruct (Z.of_nat (length F) - q =? 0) eqn:A; [intros Hk; discriminate Hk|].
destruct (Z.of_nat (length F) - q <? 16) eqn:Bq; [intros Hk; discriminate Hk|].
destruct (PSN.incl sw F q =? 0) eqn:C; [intros Hk; discriminate Hk|].
destruct (PSN.incl sw F q <=? cap) eqn:D;
  [destruct (q + 16 + PSN.incl sw F q <=? Z.of_nat (length F)); intros Hk; discriminate Hk|].
destruct (cap =? 0) eqn:E; [intros Hk; discriminate Hk|].
destruct (q + 16 + PSN.incl sw F q <=? Z.of_nat (length F)) eqn:G; [|intros Hk; discriminate Hk].
intros _. apply Z.ltb_ge in Bq. apply Z.leb_gt in D. apply Z.eqb_neq in E. apply Z.leb_le in G. lia.
Qed.

(* One turn of the record loop that goes back to its head: a KEmpty header (q + 16, lh kept) and a
   skipped KBig record (q + 16 + incl, lh := q). *)
Lemma nx_chain_empty : forall sw F cap p q lh,
  nx_chain_inv sw F cap p q lh -> q <= Z.of_nat (length F) ->
  PSN.kind sw F cap q = PSN.KEmpty ->
  nx_chain_inv sw F cap p (q + 16) lh.
Proof.
intros sw F cap p q lh HI Hq Hk.
destruct (nx_chain_fuel _ _ _ _ _ _ HI Hq) as (f & Hc & Hb).
exists f. split; [rewrite Nat2Z.inj_succ in Hb; lia|].
rewrite <- Hc. cbn [PSN.chain]. rewrite Hk. reflexivity.
Qed.

Lemma nx_chain_big : forall sw F cap p q lh,
  nx_chain_inv sw F cap p q lh -> q <= Z.of_nat (length F) -> 0 <= cap ->
  PSN.kind sw F cap q = PSN.KBig ->
  nx_chain_inv sw F cap p (q + 16 + PSN.incl sw F q) (Some q).
Proof.
intros sw F cap p q lh HI Hq Hcap Hk.
destruct (nx_kind_big _ _ _ _ Hk) as (Hi & _ & _ & _).
destruct (nx_chain_fuel _ _ _ _ _ _ HI Hq) as (f & Hc & Hb).
exists f. split; [rewrite Nat2Z.inj_succ in Hb; lia|].
rewrite <- Hc. cbn [PSN.chain]. rewrite Hk.
destruct (PSN.chain sw F cap f (q + 16 + PSN.incl sw F q) (Some q)) as [[Q o] l]. reflexivity.
Qed.

(* A turn that ends the call: the model stops at q, with lh unchanged for KEnd / KCutH and lh = q
   for every kind that read a non-empty header. *)
Lemma nx_chain_stop : forall sw F cap p q lh,
  nx_chain_inv sw F cap p q lh -> q <= Z.of_nat (length F) ->
  PSN.kind sw F cap q <> PSN.KEmpty -> PSN.kind sw F cap q <> PSN.KBig ->
  PSN.psn_q sw F cap p = q /\
  PSN.psn_lh sw F cap p = match PSN.kind sw F cap q with PSN.KEnd | PSN.KCutH => lh | _ => Some q end.
Proof.
intros sw F cap p q lh HI Hq H1 H2.
destruct (nx_chain_fuel _ _ _ _ _ _ HI Hq) as (f & Hc & _).
unfold PSN.psn_q, PSN.psn_lh. rewrite <- Hc. cbn [PSN.chain].
destruct (PSN.kind sw F cap q);
  first [ exfalso; apply H1; reflexivity | exfalso; apply H2; reflexivity | split; reflexivity ].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* ---------------------------------------------------------------------------------------------- *)
(* The contract, over the image's data as parameters (shared with the asan-ubsan build)             *)
(* ---------------------------------------------------------------------------------------------- *)

(* SHARED STATEMENT (porter ruling 22:23Z; a Theorem Labs lane's PcapSourceClose.v e49c6125747 is the model).
   Everything from here to `End s` is stated over the image's data as parameters, so that the
   asan-ubsan build states the SAME contract over its own image:
     segs     the image's segments;
     rlo rhi  the read-only window (arodata_okP);
     nstk     the stack this call and its callees use below the caller's sp. It IS an image datum:
              the machine frame is 0xe0 bytes in the asan build and 0x100 bytes in the asan-ubsan
              build (each build's Defs cites its prologue). lib/A's instance is NX_STK.
   The literal constants left in the text are the ones the two images share: the struct layout
   PS_*_OFF / PS_LEN (same source), SHADOW_OFF = 0x7fff8000 (both), the class-0 frame
   (`__asan_stack_malloc_0(0x40)` in both), EV_NEXT = 0, SRC_FILE_BLOCK = 1304, NX_CAP_MAX and
   nx_bufn (the harness's buffer), alloc_ceiling. *)
Section s.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable nstk : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* The caller's `struct pcap_source`, field by field, at the offsets the code uses. *)
Definition nx_ps_at (m : word -> option byte) (ps h sw lol lvt lvid : Z) (pad : list Z) : Prop :=
  val_mem segs m (ps + PS_F_OFF) 8 h /\
  val_mem segs m (ps + PS_SW_OFF) 4 sw /\
  val_mem segs m (ps + PS_OL_OFF) 4 lol /\
  val_mem segs m (ps + PS_VT_OFF) 4 lvt /\
  val_mem segs m (ps + PS_VID_OFF) 2 lvid /\
  garr8 segs m (ps + 22) pad /\ length pad = 2%nat.

(* The caller's right to let the call write [q, q + n): the byte is one the caller's own journal may
   change (cgif lib/YC20.v:358-359), and it is not in the stack window this call and its callees
   use. `apresent` and `~ aowned` are NOT premises: the journal derives both from awr_byte
   (YCbq.v:478 awr_byte_cases, :1925 awr_byte_present). *)
Definition nx_wr_ok (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (lyc : alayout) (Sc : astate) (own : list (Z * Z)) (sp q n : Z) : Prop :=
  forall a, q <= a < q + n ->
    awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
    ~ (sp - nstk <= a < sp).

(* What a call keeps: everything but its own stack window and the bytes E it is allowed to write
   (cgif lib/YC20.v:311-323). The frame it takes on the side stack is not named: it is fresh, it is
   not a block and not one of the caller's frames, so no clause below reaches it. *)
Definition nx_kept (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
  (W2 : world segs) (mem2 : word -> option byte) (sp : Z) (E : Z -> Prop) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - nstk <= a < sp) -> ~ E a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
  (forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - nstk <= a < sp) ->
     apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
  (forall a, sp - nstk <= a < sp -> apresent (w_H W2) mem2 a).

(* The bytes the call may write: the caller's struct, the caller's record buffer, the caller's
   timestamp cell when it asked for one, and the FILE block of the stream (the fread wrapper moves
   its window and its position). The stream's DATA buffer b is never written: the stream is "rb". *)
Definition nx_wrset (ps buf cap ts h : Z) (a : Z) : Prop :=
  (ps <= a < ps + PS_LEN) \/ (buf <= a < buf + nx_bufn cap) \/
  (ts <> 0 /\ ts <= a < ts + 8) \/ (h <> 0 /\ h <= a < h + SRC_FILE_BLOCK).

(* The caller's memory and the result when the call is done, from the caller's memory `memc`
   (`sp` is the caller's sp, the top of the window nstk). Two arms:
   - the closed reader (h = 0): a0 = -1, and nothing of the caller's is touched;
   - the open reader: the model's walk, as far as the file and the buffer allow. A record that fits
     leaves the model's bytes PSN.rec_bytes at the head of the buffer. Their number is the record's
     incl: for a VLAN-tagged record the code's __asan_memmove moves incl - 16 bytes from buf + 16
     to buf + 12 and the last 4 bytes stay where they were, so the prefix is length (nx_rec ..)
     = incl long, while the result nx_res is rec_len = incl - 4 (found by a Theorem Labs lane).
   The walk's last phases carry this predicate for the word they will return in a0. *)
Definition nx_fin (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (sp : Z)
  (ps buf cap ts h b p sw lol lvt lvid tsv : Z) (C bj pad : list Z)
  (W2 : world segs) (mem2 : word -> option byte) (r : word) : Prop :=
  (h = 0 /\ r = w64 (-1) /\
   nx_kept lyc Sc W memc W2 mem2 sp (fun _ => False))
  \/
  (h <> 0 /\ r = w64 (nx_res (sw =? 1) C cap p) /\
   nx_kept lyc Sc W memc W2 mem2 sp (nx_wrset ps buf cap ts h) /\
   asource_at segs KS (rdW W2 mem2) h b C (nx_pos (sw =? 1) C cap p) /\
   nx_ps_at (rdW W2 mem2) ps h sw
     (nx_orig (sw =? 1) C cap p lol) (nx_vtag (sw =? 1) C cap p lvt)
     (nx_vid (sw =? 1) C cap p lvid) pad /\
   (exists bj', garr8 segs (rdW W2 mem2) buf bj' /\ length bj' = length bj /\
      (nx_fit (sw =? 1) C cap p = true ->
         firstn (length (nx_rec (sw =? 1) C cap p)) bj' = nx_rec (sw =? 1) C cap p)) /\
   (ts <> 0 -> val_mem segs (rdW W2 mem2) ts 8 (nx_tsv (sw =? 1) C cap p tsv))).

Definition tpcap_source_next_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
  (regs : bvmap 5 word) (ps buf cap ts h b p sw lol lvt lvid tsv : Z)
  (C bj pad : list Z) : world segs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_NEXT) /\
  aregs_preserved regs regs2 /\
  ablocks B ly2 S2 = ablocks B lyc Sc /\ frames S2 = frames Sc /\
  mo_le MT Sc S2 0 /\
  (* the call opens, closes and writes no file: the descriptor table and the file system are the
     caller's (the harness's pe_post needs both; afread_spec's post carries them) *)
  m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc /\
  nx_fin lyc Sc W memc (spZ regs) ps buf cap ts h b p sw lol lvt lvid tsv C bj pad W2 mem2 (getr regs2 10).

(* The premises. The closed reader (h = 0) runs the prologue, reads ps->f (after the shadow
   check of ps), takes the `h == 0` branch (result -1) straight to the frame's release and the
   exit: it reads no other field of the struct and never touches the buffer, the timestamp cell
   or cap. So every premise that only the open reader uses is guarded by `h <> 0`: the struct's
   other fields and their ranges (nx_ps_at, sw, lol / lvt / lvid), the right to write the struct,
   the whole record buffer block, the timestamp cell and the stream. Unguarded: what the closed
   path uses, the struct's FILE pointer and the struct's place (alignment, bounds, not in the
   image, shadow addressable), the call state and the class-0 frame's room. *)
Definition tpcap_source_next_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (ps buf cap ts h b p sw lol lvt lvid tsv M cid pos : Z) (C bj pad : list Z) (ch : list (Z * Z * Z)),
(* the caller's journal, which this call extends *)
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP segs rlo rhi B (aview segs (w_H W) memc) ->
(* the call state *)
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 ps -> getr regs 11 = w64 buf -> getr regs 12 = w64 cap -> getr regs 13 = w64 ts ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - nstk -> spZ regs <= sp0 ->
achain lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch ->
(* room on the side stack for one class-0 frame *)
count_cid NX_CID (frames Sc) < fs_frames NX_CID ->
(* the caller's struct: its FILE pointer (read on both paths), its place and its shadow. The struct
   lies in a side-stack frame the caller owns (the harness: F + 32 of its class-1 frame), as
   PcapSourceClose's: so it is off the image (lib/A/Prog/YC1h.v frm_off_imgP) by the image's own
   laws, with no image datum in this text (it needs ps apart from the image objects
   the prologue reads). *)
val_mem segs (rdW W memc) (ps + PS_F_OFF) 8 h -> 0 <= h < 2 ^ 64 ->
ps mod 8 = 0 -> 4096 <= ps -> ps + PS_LEN <= 2 ^ 47 -> amem_range ps PS_LEN ->
In (cid, pos) own -> frame_addr lyc cid pos <= ps -> ps + PS_LEN <= frame_addr lyc cid pos + fs_frame_bytes cid ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF ps PS_LEN ->
(* the open reader's struct: its other fields, their ranges, and the right to write them *)
(h <> 0 -> nx_ps_at (rdW W memc) ps h sw lol lvt lvid pad) ->
(h <> 0 -> sw = 0 \/ sw = 1) ->
(h <> 0 -> 0 <= lol < 2 ^ 32 /\ 0 <= lvt < 2 ^ 32 /\ 0 <= lvid < 2 ^ 16) ->
(h <> 0 -> nx_wr_ok STK sp0 FP ly S lyc Sc own (spZ regs) ps PS_LEN) ->
(* the open reader's record buffer: a live block of exactly `cap ? cap : 1` bytes. The two bounds
   on buf (a Theorem Labs lane's shared-contract items for the asan-ubsan twin: UContractCF.v:114, USegL.v:240)
   follow from `In (buf, _) (ablocks ...)` and the allocator laws (al_blocks: 4096 <= buf and the
   block lies under the heap ceiling); they are stated anyway so that both builds share one text. *)
(h <> 0 ->
   In (buf, nx_bufn cap) (ablocks B lyc Sc) /\
   4096 <= buf /\ buf + nx_bufn cap < 2 ^ 63 /\
   garr8 segs (rdW W memc) buf bj /\ Z.of_nat (length bj) = nx_bufn cap /\
   0 <= cap <= NX_CAP_MAX /\
   nx_wr_ok STK sp0 FP ly S lyc Sc own (spZ regs) buf (nx_bufn cap) /\
   (buf + nx_bufn cap <= ps \/ ps + PS_LEN <= buf)) ->
(* the open reader's timestamp cell, when the caller asked for one *)
(h <> 0 -> ts <> 0 ->
   val_mem segs (rdW W memc) ts 8 tsv /\ ts mod 8 = 0 /\ 4096 <= ts /\ ts + 8 <= 2 ^ 47 /\
   amem_range ts 8 /\
   (exists tcid tpos, In (tcid, tpos) own /\ frame_addr lyc tcid tpos <= ts /\
      ts + 8 <= frame_addr lyc tcid tpos + fs_frame_bytes tcid) /\
   nx_wr_ok STK sp0 FP ly S lyc Sc own (spZ regs) ts 8 /\
   range_addressable (aview segs (w_H W) memc) SHADOW_OFF ts 8 /\
   (ts + 8 <= ps \/ ps + PS_LEN <= ts) /\ (buf + nx_bufn cap <= ts \/ ts + 8 <= buf)) ->
(* the open reader's stream *)
(h <> 0 ->
   In (h, SRC_FILE_BLOCK) (ablocks B lyc Sc) /\
   In (b, Z.of_nat (length C)) (ablocks B lyc Sc) /\
   asource_at segs KS (rdW W memc) h b C p /\
   Z.of_nat (length C) < 2 ^ 26 /\ 0 <= p <= Z.of_nat (length C) /\
   (buf + nx_bufn cap <= h \/ h + SRC_FILE_BLOCK <= buf) /\
   (buf + nx_bufn cap <= b \/ b + Z.of_nat (length C) <= buf) /\
   (ps + PS_LEN <= h \/ h + SRC_FILE_BLOCK <= ps) /\
   (ps + PS_LEN <= b \/ b + Z.of_nat (length C) <= ps) /\
   (ts <> 0 -> (ts + 8 <= h \/ h + SRC_FILE_BLOCK <= ts) /\ (ts + 8 <= b \/ b + Z.of_nat (length C) <= ts)) /\
   (* the caller's right to let the fread wrapper change the stream's FILE block and the sink
      token (asource_fp, PSource.v:286): the same premise as PcapSourceClose's, so a caller supplies
      both from one fact *)
   (forall x, inFP (asource_fp h) x -> inFP FP x \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) x)) ->
(* the open reader's meta region (the interceptor's AddrHashMap; porter 22:40Z, as PcapSourceClose).
   The post states nothing about it: PSourceMeta.asrc_meta_inv_kept keeps it across the post's
   ajournal, so the caller gets it back from the journal alone. *)
(h <> 0 -> asrc_meta_inv segs KS lyc (rdW W memc) M) ->
SRr segs W (cfg_at segs a regs memc mdc)
  (tpcap_source_next_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
     ps buf cap ts h b p sw lol lvt lvid tsv C bj pad).

End s.

(* A kept relation with a larger write set: what a phase uses to bring the bytes it wrote so far
   under the post's nx_wrset. *)
Lemma nx_kept_mono : forall segs nstk B lyc Sc (W : world segs) memc (W2 : world segs) mem2 sp
  (E E' : Z -> Prop),
  (forall a, E a -> E' a) ->
  nx_kept segs nstk B lyc Sc W memc W2 mem2 sp E -> nx_kept segs nstk B lyc Sc W memc W2 mem2 sp E'.
Proof.
intros segs nstk B lyc Sc W memc W2 mem2 sp E E' HE (K1 & K2 & K3 & K4 & K5 & K6).
split; [intros a H1 H2 H3; apply K1; [exact H1 | exact H2 | intros X; exact (H3 (HE _ X))]|].
split; [intros b m i H1 H2 H3; apply (K2 b m i); [exact H1 | exact H2 | intros X; exact (H3 (HE _ X))]|].
split; [exact K3|].
split; [intros cid pos a H1 H2 H3; apply (K4 cid pos a); [exact H1 | exact H2 | intros X; exact (H3 (HE _ X))]|].
split; [exact K5 | exact K6].
Qed.

End a.

(* SK is explicit at every use: the closure's only global sink_head instance is the PLAIN build's
   (lib/Reusable/YI5b.v:12), so an inferred SK would make the stream facts vacuous (a Theorem Labs lane 21:57Z). *)
Arguments tpcap_source_next_post {fx rc} SK.
Arguments tpcap_source_next_specX {fx rc} SK.

(* GUARD (as PcapSourceClose.v): SK is passed by position and the shared statement takes
   the image data in the order segs rlo rhi nstk B MT KS; were SK implicit again, or the order to
   change, these lines would stop compiling. nx_fin does not take SK (it names no sink head). *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (segs : list Segment)
  (rlo rhi nstk : Z) (B : asyms) (MT : ameter_ops) (KS : asource_syms) (a : Z) =>
  tpcap_source_next_specX (fx:=fx) (rc:=rc) SK segs rlo rhi nstk B MT KS a : Prop).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (segs : list Segment)
  (nstk : Z) (B : asyms) (MT : ameter_ops) (KS : asource_syms) =>
  tpcap_source_next_post (fx:=fx) (rc:=rc) SK segs nstk B MT KS).
Check (fun (rc : YM05.RunCeil) (segs : list Segment) (nstk : Z) (B : asyms) (KS : asource_syms) =>
  @nx_fin rc segs nstk B KS).
