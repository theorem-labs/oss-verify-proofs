(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainP.v (commit ce1a656b52b7, file sha256 90bc46f9a40c) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainP.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 269f2fcdb241) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainP.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the other direction of DMdrainK's bridge - from the word values a
   walk leaves (val_mem) to the cells an interface field reads (cell_holds over the view).  DoRecycle's call
   premise asks for the temp list's cells, YFeuC.plist_cells (ImgBaseDG.v:97, = qc_cells at the list's root), and
   the drain has them as the words DMdeq.ATDR (DMdeq.v:193-207) and the batch objects leave; DMiface.di_requar_r
   (DMiface.v:203-210) asks for the same shape.
   rule 24: no function proved (kind: cell-shape lemmas; the lane's reuse search is the internal file LOOKUP-B1-drain.txt,
   `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24
   check B1LookupCheck CONFIRM).
   - [val_mem_cellZ] / [val_mem_cell]: a word value gives the cell;
   - [batch_cells_of_lcn]: a linked list of batches gives their batch_cells (the inverse of
     DMdrainK.lcn_of_cells), given the slot word of an item is its chunk header's address;
   - [plist_cells_of]: the four header words and the batches' cells give YFeuC.plist_cells.
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFeu YFey YFhf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMwalkIF DMdrainK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* Forall over the slot cells, which batch_cells builds as a map over combine (seq 0 n) items. *)
Lemma forall_map_combine : forall (A : Type) (P : A -> Prop) (f : nat * chunk -> A) (l : list chunk) (s : nat),
(forall i k, nth_error l i = Some k -> P (f ((s + i)%nat, k))) ->
Forall P (map f (combine (seq s (length l)) l)).
Proof.
intros A P f l. induction l as [|k0 l IH]; intros s HP; cbn [length seq combine map]; [apply Forall_nil|].
apply Forall_cons.
- pose proof (HP 0%nat k0 eq_refl) as H0. rewrite Nat.add_0_r in H0. exact H0.
- apply (IH (S s)). intros i k Hi. pose proof (HP (S i) k Hi) as H1.
  replace (S s + i)%nat with (s + S i)%nat by lia. exact H1.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable B : asyms.
Variable ly : alayout.
Variable H : word -> bool.
Variable mem : word -> option byte.
Let rd : reader := aview tfibsegs H mem.
Let m := mrestrict H mem.

(* A word value gives the cell the interface reads. *)
Lemma val_mem_cell : forall e (w : nat) e',
val_mem tfibsegs m (aeval B ly e) w (aeval B ly e') -> cell_holds B ly rd (ACell e w (AV e')).
Proof.
intros e w e' HV k Hk. cbn [c_at c_w c_val]. unfold m in HV.
unfold rd, aview. rewrite (HV k Hk). cbn [option_map]. f_equal. apply unsigned_lit_small8.
unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma val_mem_cellZ : forall e (w : nat) x,
val_mem tfibsegs m (aeval B ly e) w x -> cell_holds B ly rd (ACell e w (AV (ANum x))).
Proof. intros e w x HV. exact (val_mem_cell e w (ANum x) HV). Qed.

(* The batch cells of a linked list, from its words.  [iwB] is the slot word of an item (DMdrainK.v). *)
Lemma batch_cells_of_lcn : forall l,
lcn ly (iwB B ly) m l 0 -> Forall (cell_holds B ly rd) (batch_cells l).
Proof.
induction l as [|b t IH]; intros HL; [apply Forall_nil|].
cbn [lcn] in HL. destruct HL as [Hb Ht]. cbn [batch_cells].
destruct Hb as (V0 & V8 & V16 & VS).
apply Forall_cons.
{ apply val_mem_cell. cbn [aeval batch_exp]. unfold addrb in V0.
  destruct t as [|b' t']; cbn [aeval batch_exp fa addrb] in V0 |- *;
  match goal with |- val_mem _ _ ?a _ _ => replace a with (ly_space ly + b_self b) by lia end; exact V0. }
apply Forall_cons.
{ apply val_mem_cellZ. cbn [aeval aoff batch_exp]. unfold addrb in V8.
  match goal with |- val_mem _ _ ?a _ _ => replace a with (ly_space ly + b_self b + 8) by lia end. exact V8. }
apply Forall_cons.
{ apply val_mem_cellZ. cbn [aeval aoff batch_exp]. unfold addrb, zl in V16.
  match goal with |- val_mem _ _ ?a _ _ => replace a with (ly_space ly + b_self b + 16) by lia end. exact V16. }
apply Forall_app. split; [|exact (IH Ht)].
apply (forall_map_combine _ _ _ (b_items b) 0%nat). intros i k Hnth. cbn [fst snd].
rewrite Nat.add_0_l.
apply val_mem_cell. cbn [aeval aoff batch_exp]. unfold addrb, iwB in VS.
pose proof (VS i k Hnth) as V.
match goal with |- val_mem _ _ ?a _ _ => replace a with (ly_space ly + b_self b + 24 + 8 * Z.of_nat i) by lia end.
exact V.
Qed.
End d.
End c.
