(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of plugin-hostd/fuzz_command's sup_broadcast walk (sup_broadcast.v), in
   the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v: the facts about the program's statics and the shape literal
   that the record gives, the block lists' separation, and the symbolic state of the walk's last segment (0x8b048 ..
   the tail jump to answer). The constant cells are read the way the draft of CmdRecFacts.v reads them
   (crf_cell_byte, crf_cells_byte_ok), under local names until that file is in the kit. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* offsets in the listing (from its base, CmdList.v): the return points of the two calls and the store block *)
Definition SB_RET_RCF : Z := AF_sup_broadcast + 0x4c.
Definition SB_STORE : Z := AF_sup_broadcast + 0x6c.
Definition SB_RET_AL : Z := AF_sup_broadcast + 0xa8.
(* the listing's object atoms the walk names (CmdList.v:4867-4904; CmdAddr.v cmd_objs) *)
Definition SB_SHAPE : nat := A_OBJ 42.
Definition SB_GREC : nat := A_OBJ 44.
Definition SB_SPILL : nat := A_OBJ 51.
Definition SB_SB : Z := 0x7fff8000.

(* the byte of an absolute constant cell (CmdChk.v's crf_cell_byte / crf_cells_byte) *)
Definition sb_cell_byte (c : acell) (a : Z) : option Z :=
match c with
| ACell (ANum s) w (AV (ANum v)) =>
  if (s <=? a) && (a <? s + Z.of_nat w) then Some (le_byte v w (Z.to_nat (a - s))) else None
| _ => None
end.
Fixpoint sb_cells_byte (l : list acell) (a : Z) : option Z :=
match l with
| [] => None
| c :: t => match sb_cell_byte c a with Some v => Some v | None => sb_cells_byte t a end
end.
Lemma sb_cell_byte_ok : forall B ly (rd : reader) c a v, cell_holds B ly rd c -> sb_cell_byte c a = Some v -> rd a = Some v.
Proof.
intros B ly rd [ca cw cv] a v Hc H. destruct ca; try (cbn in H; discriminate).
destruct cv as [e|m w]; [|cbn in H; discriminate]. destruct e; try (cbn in H; discriminate).
cbn [sb_cell_byte] in H.
destruct ((z <=? a) && (a <? z + Z.of_nat cw)) eqn:E; [|cbn in H; discriminate]. injection H as <-.
apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
unfold cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
specialize (Hc (Z.to_nat (a - z)) ltac:(lia)). rewrite Z2Nat.id in Hc by lia.
replace (z + (a - z)) with a in Hc by lia. exact Hc.
Qed.
Lemma sb_cells_byte_ok : forall B ly (rd : reader) l a v,
Forall (cell_holds B ly rd) l -> sb_cells_byte l a = Some v -> rd a = Some v.
Proof.
intros B ly rd l a v Hl. induction Hl as [|c t Hc Ht IH]; cbn [sb_cells_byte]; [discriminate|].
destruct (sb_cell_byte c a) as [w|] eqn:E; [intros Hw; injection Hw as <-; exact (sb_cell_byte_ok B ly rd c a w Hc E) | exact IH].
Qed.

(* two members of a list without repeated first components that share it are equal *)
(* list membership of stdpp's NoDup (the one these files see) is Stdlib's In *)
Lemma sb_elem_of_In : forall {A : Type} (x : A) (l : list A), x ∈ l <-> In x l.
Proof.
intros A x l. induction l as [|y l IH]; split; intros H.
- inversion H.
- destruct H.
- inversion H; subst; [left; reflexivity | right; apply IH; assumption].
- destruct H as [<- | H]; [constructor 1 | constructor 2; apply IH; exact H].
Qed.
Lemma sb_nodup_fst : forall (l : list (Z * Z)) a x y, NoDup (map fst l) -> In (a, x) l -> In (a, y) l -> x = y.
Proof.
induction l as [|[b m] t IH]; intros a x y Hn Hx Hy; [destruct Hx|].
cbn [map] in Hn. inversion Hn as [|? ? Hb Ht]; subst. rewrite sb_elem_of_In in Hb.
destruct Hx as [Ex | Hx]; destruct Hy as [Ey | Hy].
- congruence.
- injection Ex as <- <-. exfalso. apply Hb. apply (in_map fst t (b, y)). exact Hy.
- injection Ey as <- <-. exfalso. apply Hb. apply (in_map fst t (b, x)). exact Hx.
- exact (IH a x y Ht Hx Hy).
Qed.
Lemma sb_pairwise_nodup : forall (l : list (Z * Z)),
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> (forall b, In b l -> 0 <= snd b) -> NoDup (map fst l).
Proof.
induction l as [|[b m] t IH]; intros Hp Hpos; [constructor|].
cbn [map pairwise] in Hp. destruct Hp as [Hf Ht]. cbn [map]. constructor.
- intros Hin. apply sb_elem_of_In in Hin. apply in_map_iff in Hin as ([b' m'] & Eb & Hin'). cbn in Eb. subst b'.
  pose proof (proj1 (Forall_forall _ _) Hf (b, req_size m') (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) t (b, m') Hin')) as Hd.
  pose proof (req_size_pos m (Hpos (b, m) (or_introl eq_refl))) as [Hr1 _].
  pose proof (req_size_pos m' (Hpos (b, m') (or_intror Hin'))) as [Hr2 _].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- apply IH; [exact Ht | intros b0 Hb0; apply Hpos; right; exact Hb0].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.

(* every byte of g_rec, record.spill and g_quitting is one of the program's statics (the statements' HPROG, from
   CmdBSyms' ts_prog) *)
Lemma HPROG : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof.
intros a (r & Hin & Hr). rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC.
unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* the statics are neither runtime-owned nor the errno cell (prog_static_sep, YCbq.v:218) *)
Lemma sb_pg_unowned : forall a, inFP cmd_PG a ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. pose proof (prog_static_sep B a (ts_ok B HB) (HPROG a Ha)) as (H1 & H2 & _). split; assumption.
Qed.

(* the live blocks start at distinct addresses (AR's separation, al_sep) *)
Lemma sb_blocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> NoDup (map fst (ablocks B ly S)).
Proof.
intros ly S W mem md HAR. destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _].
apply pairwise_app_l in Hp as [Hp _]. apply sb_pairwise_nodup; [exact Hp|].
intros [p n] Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn). cbn [snd]. lia.
Qed.

(* the record's constant cells (Tfib_const_abs, Tfib_const_shadow) hold at every state *)
Lemma sb_const_byte : forall ly S (W : world SEGS) mem md a v, AR SEGS B ly S W mem md ->
sb_cells_byte (Tfib_const_abs ++ Tfib_const_shadow) a = Some v -> rdW W mem a = Some v.
Proof.
intros ly S W mem md a v HAR Hc. apply (sb_cells_byte_ok B ly _ (Tfib_const_abs ++ Tfib_const_shadow) a v); [|exact Hc].
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite (ts_const B HB ly) in HC.
unfold Tfib_const in HC. apply Forall_app in HC as [_ HC]. exact HC.
Qed.

(* the shape "resp 0" (0x21ce0, 7 bytes): its shadow byte is 7 and the eight shadow bytes of its word are constant
   cells of the record (A/AF0m.v:2599-2606), so its checks pass and its shadow word is readable at every state *)
Lemma sb_shape_shadow : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
range_addressable (rdW W mem) SHADOW_OFF 0x21ce0 7 /\ shadow_hull_vis (rdW W mem) 0x21ce0 7.
Proof.
intros ly S W mem md HAR. split.
- intros x Hx. exists 7. split.
  + apply (sb_const_byte ly S W mem md _ 7 HAR).
    replace (shadow_of_addr SHADOW_OFF x) with 0x7fffc39c by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
    vm_compute. reflexivity.
  + unfold saddr_ok. right. Z.div_mod_to_equations. lia.
- intros s Hs.
  assert (E1 : shadow_addr 0x21ce0 / 8 * 8 = 0x7fffc398) by reflexivity.
  assert (E2 : shadow_addr (0x21ce0 + 7 - 1) / 8 * 8 + 8 = 0x7fffc3a0) by reflexivity.
  rewrite E1, E2 in Hs.
  assert (Hs' : s = 0x7fffc398 \/ s = 0x7fffc399 \/ s = 0x7fffc39a \/ s = 0x7fffc39b \/ s = 0x7fffc39c \/
    s = 0x7fffc39d \/ s = 0x7fffc39e \/ s = 0x7fffc39f) by lia.
  destruct Hs' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  (lazymatch goal with |- aview _ _ _ ?a <> None =>
   intros Hn; eassert (Hc : sb_cells_byte (Tfib_const_abs ++ Tfib_const_shadow) a = Some _) by (vm_compute; reflexivity);
   rewrite (sb_const_byte ly S W mem md _ _ HAR Hc) in Hn; discriminate Hn end).
Qed.

(* the shape's bytes are neither runtime-owned nor the errno cell (CmdBSyms' owned list and errno cell) *)
Lemma sb_shape_unowned : forall i, 0 <= i < 7 ->
~ Exists (in_zr (0x21ce0 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x21ce0 + i < as_errno B + 4).
Proof.
intros i Hi. rewrite (ts_owned B HB), (ts_errno B HB). split.
- intros HE. apply Exists_exists in HE as (r & Hr & Hra).
  assert (Hd : forallb (zr_disjointb (0x21ce0, 7)) Tfib_owned_static = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hd r Hr) as Hdr. unfold zr_disjointb in Hdr. cbn [fst snd] in Hdr.
  apply orb_prop in Hdr as [Hdr | Hdr]; apply Z.leb_le in Hdr; unfold in_zr in Hra; lia.
- unfold TFIB_ERRNO. lia.
Qed.

End e.
End f.
End d.
