(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the helper facts of sup_pool_config's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, entry BASE + AF_sup_pool_config = 0x8bed0, 127 instructions, 0 report calls, 0 UBSan trap
   sites) that need none of the callee statements record_c / arg_s_c / answer_c: the walk's program points, the
   model step in the form the three callee posts chain it, the "%d" text of the inlined arg_i (snprintf's piece
   list against the recorder's dec), the read-only literals "pool_config" (0x21ec0) and "%d" (0x21f40), and the
   block bookkeeping of the post. Re-walked from lib/A/Prog/sup_pool_config_d.v (the verb lemmas),
   sup_pool_config_s2.v (spc_model) and sup_pool_config_s3.v (spc_final_blocks, here over an owned-block list given
   by membership, since B's callees return their lists in their own order). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_pool_config_aux.v, with its module paths and module names changed; 343 of its 419 lines of code are new or changed and 465 lines of the source are left out. *)
(* The definitions and the shadow lemmas the per-binary facts of fuzz_command.asan-ubsan share (the B twin of
   lib/A/Prog/CmdRecBase.v; lib/B/Prog/CmdRecFacts.v re-exports this file and the groups that use it: CmdRecCells,
   CmdRecRo, CmdRecImg, CmdRecCover, CmdRecRest).

   - the record's pinned bytes: AR shows the byte the allocator record pins at a shadow address (a zero-shadow range,
     or one of its absolute constant cells: cmd_byte, lib/B/Prog/CmdChk.v), so the checkers cmd_addr_b / cmd_hull_b
     give range_addressable and shadow_hull_vis at every AR state (cmd_addressable_chk, cmd_hull_vis_chk,
     cmd_aread_ok_chk), and cmd_word_b a word (cmd_word_chk). cgif states the same facts per range (cgif
     lib/A/AD1k.v:206-233, rodata_zero_shadow, rodata_hull_zero, rodata_shadow_facts).
   - the image: `cmd_img_facts segs B` holds the facts about the segments and the record's static lists that a walk
     cannot compute over an abstract SEGS (CmdRecImg.v proves them for the pinned image by computation), and CmdRo's
     objects as two lists in its order (cmd_ro_objs, cmd_ro_list).
   Every list fact is one boolean check closed by vm_compute; nothing here destructs a per-binary list. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0d_tail.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdAddr CmdPa CmdImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdObj CmdBase CmdRo CmdGlob CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Export CmdChk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** * Boolean helpers *)
Lemma crf_zallf_ok : forall f k lo, crf_zallf f lo k = true -> forall x, lo <= x < lo + Z.of_nat k -> f x = true.
Proof.
intros f k. induction k as [|k IH]; intros lo H x Hx; [lia|].
cbn [crf_zallf] in H. apply andb_prop in H as [H1 H2].
destruct (Z.eq_dec x lo) as [->|Hne]; [exact H1|]. apply (IH (lo + 1) H2). lia.
Qed.
Lemma crf_some_ok : forall {A : Type} (o : option A), crf_some o = true -> o <> None.
Proof. intros A [x|] H; [discriminate | discriminate H]. Qed.
Lemma crf_in_rangesb : forall a l, in_rangesb a l = true <-> Exists (in_zr a) l.
Proof.
intros a l. induction l as [|[lo len] t IH]; cbn [in_rangesb].
- split; [discriminate | intros H; inversion H].
- rewrite Bool.orb_true_iff, Bool.andb_true_iff, Z.leb_le, Z.ltb_lt, IH, Exists_cons. unfold in_zr. cbn [fst snd].
  tauto.
Qed.
Lemma crf_disj_notin : forall r l a, forallb (zr_disjointb r) l = true -> in_zr a r -> ~ Exists (in_zr a) l.
Proof.
intros r l a H Ha HE. apply Exists_exists in HE as (q & Hq & Hqa).
pose proof (proj1 (forallb_forall _ _) H q Hq) as Hd. unfold zr_disjointb in Hd.
apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; unfold in_zr in Ha, Hqa; lia.
Qed.

(** * The bytes the record's constants pin (cmd_byte, CmdChk.v) *)
Lemma crf_cell_byte_ok : forall B ly (rd : reader) c a v, cell_holds B ly rd c -> crf_cell_byte c a = Some v -> rd a = Some v.
Proof.
intros B ly rd [ca cw cv] a v Hc H. destruct ca; try (cbn in H; discriminate).
destruct cv as [e|m w]; [|cbn in H; discriminate]. destruct e; try (cbn in H; discriminate).
cbn [crf_cell_byte] in H.
destruct ((z <=? a) && (a <? z + Z.of_nat cw)) eqn:E; [|cbn in H; discriminate]. injection H as <-.
apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
unfold cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
specialize (Hc (Z.to_nat (a - z)) ltac:(lia)). rewrite Z2Nat.id in Hc by lia.
replace (z + (a - z)) with a in Hc by lia. exact Hc.
Qed.
Lemma crf_cells_byte_ok : forall B ly (rd : reader) l a v,
Forall (cell_holds B ly rd) l -> crf_cells_byte l a = Some v -> rd a = Some v.
Proof.
intros B ly rd l a v Hl. induction Hl as [|c t Hc Ht IH]; cbn [crf_cells_byte]; [discriminate|].
destruct (crf_cell_byte c a) as [w|] eqn:E; [intros Hw; injection Hw as <-; exact (crf_cell_byte_ok B ly rd c a w Hc E) | exact IH].
Qed.
Lemma crf_zsh_hit_ok : forall (rd : reader) l s,
Forall (fun r => zero_shadow rd SHADOW_OFF (fst r) (snd r)) l -> crf_zsh_hit l s = true -> rd s = Some 0.
Proof.
intros rd l s Hl H. unfold crf_zsh_hit in H. apply existsb_exists in H as (r & Hr & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (proj1 (Forall_forall _ _) Hl r Hr (s - shadow_of_addr SHADOW_OFF (fst r)) ltac:(lia)) as HZ.
replace (shadow_of_addr SHADOW_OFF (fst r) + (s - shadow_of_addr SHADOW_OFF (fst r))) with s in HZ by lia. exact HZ.
Qed.
Lemma crf_zsh_hit_of : forall l s r, In r l ->
shadow_of_addr SHADOW_OFF (fst r) <= s < shadow_of_addr SHADOW_OFF (fst r) + snd r / 8 -> crf_zsh_hit l s = true.
Proof.
intros l s r Hr Hs. unfold crf_zsh_hit. apply existsb_exists. exists r. split; [exact Hr|].
apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(** * The checkers *)
(* what aread_ok asks of an image range, less the presence of its bytes *)
Definition cmd_rd_b (x n : Z) : bool :=
(0 <=? x) && (0 <=? n) && (x + n <=? kLowMemEnd - 1) && cmd_addr_b x n && ((n <=? 0) || cmd_hull_b x n).
(* the 8 bytes at [a] are pinned and make the word [v] *)
Definition cmd_word_b (a v : Z) : bool :=
match cmd_byte a, cmd_byte (a + 1), cmd_byte (a + 2), cmd_byte (a + 3), cmd_byte (a + 4), cmd_byte (a + 5),
cmd_byte (a + 6), cmd_byte (a + 7) with
| Some b0, Some b1, Some b2, Some b3, Some b4, Some b5, Some b6, Some b7 =>
  Z.eqb (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) v
| _, _, _, _, _, _, _, _ => false
end.

(** * Coverage of the image's shadow *)
(* the end of the zero-shadow range that holds the shadow byte of granule [g], if one does *)
Fixpoint crf_zsh_jump (l : list (Z * Z)) (g : Z) : option Z :=
match l with
| [] => None
| r :: t => if (fst r / 8 <=? g / 8) && (g / 8 <? fst r / 8 + snd r / 8) then Some (8 * (fst r / 8 + snd r / 8))
            else crf_zsh_jump t g
end.
Fixpoint crf_cover_from (fuel : nat) (g hi : Z) : bool :=
match fuel with
| O => false
| S f =>
  if hi <=? g then true else
  match crf_zsh_jump Tfib_zero_shadow g with
  | Some e => crf_cover_from f e hi
  | None => if crf_some (crf_cells_byte cmd_cabs (shadow_of_addr SHADOW_OFF g)) then crf_cover_from f (g + 8) hi else false
  end
end.
Lemma crf_zsh_jump_spec : forall l g e, crf_zsh_jump l g = Some e ->
exists r, In r l /\ fst r / 8 <= g / 8 < fst r / 8 + snd r / 8 /\ e = 8 * (fst r / 8 + snd r / 8).
Proof.
induction l as [|r t IH]; intros g e H; cbn [crf_zsh_jump] in H; [discriminate|].
destruct ((fst r / 8 <=? g / 8) && (g / 8 <? fst r / 8 + snd r / 8)) eqn:E.
- injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  exists r. split; [left; reflexivity | split; [lia | reflexivity]].
- destruct (IH g e H) as (r' & H1 & H2 & H3). exists r'. split; [right; exact H1 | split; [exact H2 | exact H3]].
Qed.
Lemma crf_cover_from_ok : forall fuel g hi, g mod 8 = 0 -> crf_cover_from fuel g hi = true ->
forall x, g <= x < hi -> cmd_byte (shadow_of_addr SHADOW_OFF x) <> None.
Proof.
induction fuel as [|f IH]; intros g hi Hg H x Hx; cbn [crf_cover_from] in H; [discriminate|].
destruct (hi <=? g) eqn:Ehi; [apply Z.leb_le in Ehi; lia|].
destruct (crf_zsh_jump Tfib_zero_shadow g) as [e|] eqn:EJ.
- destruct (crf_zsh_jump_spec _ _ _ EJ) as (r & Hr & Hb & He).
  destruct (Z_lt_le_dec x e) as [Hxe|Hxe].
  + unfold cmd_byte. rewrite (crf_zsh_hit_of Tfib_zero_shadow _ r Hr); [discriminate|].
    assert (D1 : g / 8 <= x / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : x / 8 < fst r / 8 + snd r / 8) by (apply Z.div_lt_upper_bound; lia).
    unfold shadow_of_addr. lia.
  + apply (IH e hi); [subst e; rewrite Z.mul_comm; apply Z_mod_mult | exact H | lia].
- destruct (crf_cells_byte cmd_cabs (shadow_of_addr SHADOW_OFF g)) as [v|] eqn:EC; [|cbn in H; discriminate].
  cbn [crf_some] in H.
  destruct (Z_lt_le_dec x (g + 8)) as [Hx8|Hx8].
  + assert (Q : x / 8 = g / 8). { clear - Hg Hx Hx8. Z.div_mod_to_equations. lia. }
    unfold cmd_byte. destruct (crf_zsh_hit Tfib_zero_shadow (shadow_of_addr SHADOW_OFF x)); [discriminate|].
    unfold shadow_of_addr in *. rewrite Q, EC. discriminate.
  + apply (IH (g + 8) hi); [|exact H | lia]. clear - Hg. Z.div_mod_to_equations. lia.
Qed.
Lemma crf_hull_lo : forall p s, 0x10000 <= p -> shadow_addr p / 8 * 8 <= s -> 0x10000 <= 8 * (s - SHADOW_OFF).
Proof. intros p s Hp Hs. unfold shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia. Qed.
Lemma crf_hull_hi : forall y s, 0 <= y < 0x606000 -> s < shadow_addr y / 8 * 8 + 8 -> 8 * (s - SHADOW_OFF) < 0x606000.
Proof. intros y s Hy Hs. unfold shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia. Qed.

(** * Image ranges *)
Definition crf_seg_sub (s : Segment) (r : Z * Z) : bool :=
(Z.of_N (seg_base s) <=? fst r) && (fst r + snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)).
Definition crf_img_rangeb (segs : list Segment) (r : Z * Z) : bool := existsb (fun s => crf_seg_sub s r) segs.
Definition crf_ro_rangeb (segs : list Segment) (lo hi : Z) (r : Z * Z) : bool :=
existsb (fun s => negb (seg_writable s) && crf_seg_sub s r) segs || ((lo <=? fst r) && (fst r + snd r <=? hi)).
Definition crf_ro_endb (segs : list Segment) (lo hi : Z) : bool :=
forallb (fun s => seg_writable s || ((lo <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? hi))) segs.
Lemma crf_img_rangeb_ok : forall segs r a, crf_img_rangeb segs r = true -> in_zr a r -> in_img segs a.
Proof.
intros segs r a H Ha. unfold crf_img_rangeb in H. apply existsb_exists in H as (s & Hs & Hb).
unfold crf_seg_sub in Hb. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
unfold in_zr in Ha. exists s. split; [exact Hs | lia].
Qed.
Lemma crf_ro_rangeb_ok : forall segs lo hi r a, crf_ro_rangeb segs lo hi r = true -> in_zr a r -> in_roP segs lo hi a.
Proof.
intros segs lo hi r a H Ha. unfold in_zr in Ha. unfold crf_ro_rangeb in H. apply orb_prop in H as [H|H].
- apply existsb_exists in H as (s & Hs & Hb). apply andb_prop in Hb as [Hw Hb]. apply negb_true_iff in Hw.
  unfold crf_seg_sub in Hb. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  left. exists s. split; [exact Hs | split; [exact Hw | lia]].
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. right. lia.
Qed.
Lemma crf_ro_endb_ok : forall segs a, crf_ro_endb segs 0x10000 0xa6c68 = true ->
in_roP segs CMD_RLO CMD_RHI a -> 0x10000 <= a < 0xa6c68.
Proof.
intros segs a H [(s & Hs & Hw & Ha)|Ha]; [|unfold CMD_RLO, CMD_RHI in Ha; lia].
pose proof (proj1 (forallb_forall _ _) H s Hs) as Hb. cbn beta in Hb. rewrite Hw in Hb. cbn [orb] in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
(* [f] at every integer of [lo, lo + k), by a tail call per integer (for the long image ranges) *)
Fixpoint crf_zallt (f : Z -> bool) (lo : Z) (k : nat) : bool :=
match k with O => true | S k' => if f lo then crf_zallt f (lo + 1) k' else false end.
Lemma crf_zallt_ok : forall f k lo, crf_zallt f lo k = true -> forall x, lo <= x < lo + Z.of_nat k -> f x = true.
Proof.
intros f k. induction k as [|k IH]; intros lo H x Hx; [lia|].
cbn [crf_zallt] in H. destruct (f lo) eqn:E; [|discriminate].
destruct (Z.eq_dec x lo) as [->|Hne]; [exact E|]. apply (IH (lo + 1) H). lia.
Qed.


(** * The read-only objects of CmdRo.v *)
(* CmdRo's 218 objects in cmd_ro_in's order (start, length), and their bytes in cmd_ro_bytes' order. If CmdRo.v is
   regenerated, cmd_ro_in_of, cmd_ro_in_to, crf_ro_bytes_of and crf_ro_list_objs stop compiling until these two
   lists are regenerated with it. *)
Definition cmd_ro_objs : list (Z * Z) := [
(0x10330, 9); (0x13794, 36); (0x15923, 18); (0x15fd2, 21); (0x176c8, 18); (0x17f1b, 16); (0x18ebf, 18); (0x18ed1, 23);
(0x1b056, 22); (0x1b074, 18); (0x1dfad, 36); (0x1ea5a, 34); (0x1f29a, 19); (0x20814, 39); (0x20852, 20); (0x210e0, 3);
(0x21100, 8); (0x21120, 7); (0x21140, 5); (0x21160, 2); (0x21180, 11); (0x211a0, 11); (0x211c0, 14); (0x211e0, 17);
(0x21220, 4); (0x21240, 61); (0x212a0, 12); (0x212c0, 1); (0x212e0, 14); (0x21300, 11); (0x21320, 17); (0x21360, 17);
(0x213a0, 17); (0x213e0, 17); (0x21420, 11); (0x21440, 31); (0x21480, 12); (0x214a0, 23); (0x214e0, 11); (0x21500, 35);
(0x21560, 8); (0x21580, 81); (0x21600, 10); (0x21620, 12); (0x21640, 15); (0x21660, 44); (0x216c0, 11); (0x216e0, 6);
(0x21700, 29); (0x21740, 6); (0x21760, 36); (0x217c0, 12); (0x217e0, 8); (0x21800, 15); (0x21820, 10); (0x21840, 7);
(0x21860, 10); (0x21880, 8); (0x218a0, 11); (0x218c0, 4); (0x218e0, 3); (0x21900, 9); (0x21920, 5); (0x21940, 3);
(0x21960, 8); (0x21980, 2); (0x219a0, 6); (0x219c0, 4); (0x219e0, 3); (0x21a00, 2); (0x21a20, 4); (0x21a40, 5);
(0x21a60, 6); (0x21a80, 7); (0x21aa0, 5); (0x21ac0, 8); (0x21ae0, 2); (0x21b00, 2); (0x21b20, 4); (0x21b40, 8);
(0x21b60, 6); (0x21b80, 4); (0x21ba0, 9); (0x21be0, 232); (0x21d00, 4); (0x21d20, 7); (0x21d40, 8); (0x21d60, 6);
(0x21d80, 2); (0x21da0, 3); (0x21dc0, 12); (0x21de0, 14); (0x21e00, 17); (0x21e40, 17); (0x21e80, 11); (0x21ea0, 11);
(0x21ec0, 12); (0x21ee0, 15); (0x21f00, 11); (0x21f20, 4); (0x21f40, 3); (0x21f60, 6); (0x21f80, 12); (0x21fa0, 15);
(0x21fc0, 10); (0x21fe0, 2); (0x22000, 4); (0x22020, 16); (0x22040, 61); (0x220a0, 54); (0x22100, 8); (0x22120, 10);
(0x22140, 11); (0x22160, 25); (0x221a0, 11); (0x221c0, 16); (0x221e0, 11); (0x22200, 13); (0x22220, 13); (0x22240, 16);
(0x22260, 79); (0x222e0, 11); (0x22300, 67); (0x22380, 12); (0x223a0, 11); (0x223c0, 25); (0x22400, 11); (0x22420, 18);
(0x22460, 8); (0x22480, 9); (0x224a0, 14); (0x224c0, 7); (0x22500, 3); (0x22520, 18); (0x22560, 19); (0x225a0, 4);
(0x225c0, 15); (0x225e0, 10); (0x22600, 10); (0x22620, 12); (0x22640, 14); (0x22660, 17); (0x226a0, 4); (0x226c0, 17);
(0x22700, 11); (0x22720, 15); (0x22740, 12); (0x22760, 11); (0x22780, 6); (0x227a0, 12); (0x227c0, 8); (0x227e0, 11);
(0x22800, 10); (0x22820, 5); (0x22840, 14); (0x22860, 17); (0x228a0, 4); (0x228c0, 8); (0x228e0, 6); (0x22900, 9);
(0x22920, 11); (0x22940, 13); (0x22960, 16); (0x22980, 11); (0x229a0, 12); (0x229c0, 11); (0x229e0, 11); (0x22a00, 8);
(0x22a20, 9); (0x22a40, 14); (0x22a60, 24); (0x22aa0, 13); (0x22ac0, 19); (0x22b00, 16); (0x22b20, 26); (0x22b60, 16);
(0x22b80, 12); (0x22ba0, 21); (0x22be0, 23); (0x22c20, 27); (0x22c60, 17); (0x22ca0, 47); (0x22d00, 15); (0x22d20, 22);
(0x22d60, 25); (0x22da0, 15); (0x22dc0, 2); (0x86bf8, 8); (0x86e64, 8); (0x87ae8, 8); (0x882d8, 8); (0x890e0, 8);
(0x8a188, 8); (0x8a400, 8); (0x8aa10, 8); (0x8af34, 8); (0x8b258, 8); (0x8b53c, 8); (0x8b8f8, 8); (0x8bb70, 8);
(0x8bed0, 8); (0x8c1c4, 8); (0x8c570, 8); (0x8c758, 8); (0x8c9f8, 8); (0x8ce4c, 8); (0x8da84, 8); (0x8df2c, 8);
(0xa5680, 528); (0xa5920, 208); (0xa5a20, 448); (0xa5a28, 8); (0xa5c40, 160); (0xa5d00, 144); (0xa6bc8, 8); (0xa6bd0, 8);
(0xa6bd8, 8); (0xa6be0, 8)].
Definition cmd_ro_list : list (Z * list byte) := [
(0x10330, RO_lit_10330); (0x13794, RO_lit_13794); (0x15923, RO_lit_15923); (0x15fd2, RO_lit_15fd2); (0x176c8, RO_lit_176c8);
(0x17f1b, RO_lit_17f1b); (0x18ebf, RO_lit_18ebf); (0x18ed1, RO_lit_18ed1); (0x1b056, RO_lit_1b056); (0x1b074, RO_lit_1b074);
(0x1dfad, RO_lit_1dfad); (0x1ea5a, RO_lit_1ea5a); (0x1f29a, RO_lit_1f29a); (0x20814, RO_lit_20814); (0x20852, RO_lit_20852);
(0x210e0, RO_lit_210e0); (0x21100, RO_lit_21100); (0x21120, RO_lit_21120); (0x21140, RO_lit_21140); (0x21160, RO_lit_21160);
(0x21180, RO_lit_21180); (0x211a0, RO_lit_211a0); (0x211c0, RO_lit_211c0); (0x211e0, RO_lit_211e0); (0x21220, RO_lit_21220);
(0x21240, RO_lit_21240); (0x212a0, RO_lit_212a0); (0x212c0, RO_lit_212c0); (0x212e0, RO_lit_212e0); (0x21300, RO_lit_21300);
(0x21320, RO_lit_21320); (0x21360, RO_lit_21360); (0x213a0, RO_lit_213a0); (0x213e0, RO_lit_213e0); (0x21420, RO_lit_21420);
(0x21440, RO_lit_21440); (0x21480, RO_lit_21480); (0x214a0, RO_lit_214a0); (0x214e0, RO_lit_214e0); (0x21500, RO_lit_21500);
(0x21560, RO_lit_21560); (0x21580, RO_lit_21580); (0x21600, RO_lit_21600); (0x21620, RO_lit_21620); (0x21640, RO_lit_21640);
(0x21660, RO_lit_21660); (0x216c0, RO_lit_216c0); (0x216e0, RO_lit_216e0); (0x21700, RO_lit_21700); (0x21740, RO_lit_21740);
(0x21760, RO_lit_21760); (0x217c0, RO_lit_217c0); (0x217e0, RO_lit_217e0); (0x21800, RO_lit_21800); (0x21820, RO_lit_21820);
(0x21840, RO_lit_21840); (0x21860, RO_lit_21860); (0x21880, RO_lit_21880); (0x218a0, RO_lit_218a0); (0x218c0, RO_lit_218c0);
(0x218e0, RO_lit_218e0); (0x21900, RO_lit_21900); (0x21920, RO_lit_21920); (0x21940, RO_lit_21940); (0x21960, RO_lit_21960);
(0x21980, RO_lit_21980); (0x219a0, RO_lit_219a0); (0x219c0, RO_lit_219c0); (0x219e0, RO_lit_219e0); (0x21a00, RO_lit_21a00);
(0x21a20, RO_lit_21a20); (0x21a40, RO_lit_21a40); (0x21a60, RO_lit_21a60); (0x21a80, RO_lit_21a80); (0x21aa0, RO_lit_21aa0);
(0x21ac0, RO_lit_21ac0); (0x21ae0, RO_lit_21ae0); (0x21b00, RO_lit_21b00); (0x21b20, RO_lit_21b20); (0x21b40, RO_lit_21b40);
(0x21b60, RO_lit_21b60); (0x21b80, RO_lit_21b80); (0x21ba0, RO_lit_21ba0); (0x21be0, RO_rec_codes); (0x21d00, RO_rec_ncodes);
(0x21d20, RO_lit_21d20); (0x21d40, RO_lit_21d40); (0x21d60, RO_lit_21d60); (0x21d80, RO_lit_21d80); (0x21da0, RO_lit_21da0);
(0x21dc0, RO_lit_21dc0); (0x21de0, RO_lit_21de0); (0x21e00, RO_lit_21e00); (0x21e40, RO_lit_21e40); (0x21e80, RO_lit_21e80);
(0x21ea0, RO_lit_21ea0); (0x21ec0, RO_lit_21ec0); (0x21ee0, RO_lit_21ee0); (0x21f00, RO_lit_21f00); (0x21f20, RO_lit_21f20);
(0x21f40, RO_lit_21f40); (0x21f60, RO_lit_21f60); (0x21f80, RO_lit_21f80); (0x21fa0, RO_lit_21fa0); (0x21fc0, RO_lit_21fc0);
(0x21fe0, RO_lit_21fe0); (0x22000, RO_lit_22000); (0x22020, RO_lit_22020); (0x22040, RO_lit_22040); (0x220a0, RO_lit_220a0);
(0x22100, RO_lit_22100); (0x22120, RO_lit_22120); (0x22140, RO_lit_22140); (0x22160, RO_lit_22160); (0x221a0, RO_lit_221a0);
(0x221c0, RO_lit_221c0); (0x221e0, RO_lit_221e0); (0x22200, RO_lit_22200); (0x22220, RO_lit_22220); (0x22240, RO_lit_22240);
(0x22260, RO_lit_22260); (0x222e0, RO_lit_222e0); (0x22300, RO_lit_22300); (0x22380, RO_lit_22380); (0x223a0, RO_lit_223a0);
(0x223c0, RO_lit_223c0); (0x22400, RO_lit_22400); (0x22420, RO_lit_22420); (0x22460, RO_lit_22460); (0x22480, RO_lit_22480);
(0x224a0, RO_lit_224a0); (0x224c0, RO_lit_224c0); (0x22500, RO_lit_22500); (0x22520, RO_lit_22520); (0x22560, RO_lit_22560);
(0x225a0, RO_lit_225a0); (0x225c0, RO_lit_225c0); (0x225e0, RO_lit_225e0); (0x22600, RO_lit_22600); (0x22620, RO_lit_22620);
(0x22640, RO_lit_22640); (0x22660, RO_lit_22660); (0x226a0, RO_lit_226a0); (0x226c0, RO_lit_226c0); (0x22700, RO_lit_22700);
(0x22720, RO_lit_22720); (0x22740, RO_lit_22740); (0x22760, RO_lit_22760); (0x22780, RO_lit_22780); (0x227a0, RO_lit_227a0);
(0x227c0, RO_lit_227c0); (0x227e0, RO_lit_227e0); (0x22800, RO_lit_22800); (0x22820, RO_lit_22820); (0x22840, RO_lit_22840);
(0x22860, RO_lit_22860); (0x228a0, RO_lit_228a0); (0x228c0, RO_lit_228c0); (0x228e0, RO_lit_228e0); (0x22900, RO_lit_22900);
(0x22920, RO_lit_22920); (0x22940, RO_lit_22940); (0x22960, RO_lit_22960); (0x22980, RO_lit_22980); (0x229a0, RO_lit_229a0);
(0x229c0, RO_lit_229c0); (0x229e0, RO_lit_229e0); (0x22a00, RO_lit_22a00); (0x22a20, RO_lit_22a20); (0x22a40, RO_lit_22a40);
(0x22a60, RO_lit_22a60); (0x22aa0, RO_lit_22aa0); (0x22ac0, RO_lit_22ac0); (0x22b00, RO_lit_22b00); (0x22b20, RO_lit_22b20);
(0x22b60, RO_lit_22b60); (0x22b80, RO_lit_22b80); (0x22ba0, RO_lit_22ba0); (0x22be0, RO_lit_22be0); (0x22c20, RO_lit_22c20);
(0x22c60, RO_lit_22c60); (0x22ca0, RO_lit_22ca0); (0x22d00, RO_lit_22d00); (0x22d20, RO_lit_22d20); (0x22d60, RO_lit_22d60);
(0x22da0, RO_lit_22da0); (0x22dc0, RO_lit_22dc0); (0x86bf8, RO_lit_86bf8); (0x86e64, RO_lit_86e64); (0x87ae8, RO_lit_87ae8);
(0x882d8, RO_lit_882d8); (0x890e0, RO_lit_890e0); (0x8a188, RO_lit_8a188); (0x8a400, RO_lit_8a400); (0x8aa10, RO_lit_8aa10);
(0x8af34, RO_lit_8af34); (0x8b258, RO_lit_8b258); (0x8b53c, RO_lit_8b53c); (0x8b8f8, RO_lit_8b8f8); (0x8bb70, RO_lit_8bb70);
(0x8bed0, RO_lit_8bed0); (0x8c1c4, RO_lit_8c1c4); (0x8c570, RO_lit_8c570); (0x8c758, RO_lit_8c758); (0x8c9f8, RO_lit_8c9f8);
(0x8ce4c, RO_lit_8ce4c); (0x8da84, RO_lit_8da84); (0x8df2c, RO_lit_8df2c); (0xa5680, RO_g_parsed); (0xa5920, RO_g_call_words);
(0xa5a20, RO_g_shapes); (0xa5a28, RO_ptr_a5a28); (0xa5c40, RO_g_instance_info_verbs); (0xa5d00, RO_g_instance_verbs); (0xa6bc8, RO_ptr_a6bc8);
(0xa6bd0, RO_ptr_a6bd0); (0xa6bd8, RO_ptr_a6bd8); (0xa6be0, RO_ptr_a6be0)].
Fixpoint crf_ro_in_list (ro : Z -> Prop) (l : list (Z * Z)) : Prop :=
match l with
| [] => True
| [r] => forall i, 0 <= i < snd r -> ro (fst r + i)
| r :: t => (forall i, 0 <= i < snd r -> ro (fst r + i)) /\ crf_ro_in_list ro t
end.
Lemma crf_ro_in_list_of : forall ro l, (forall a, Exists (in_zr a) l -> ro a) -> crf_ro_in_list ro l.
Proof.
intros ro l. induction l as [|r t IH]; intros H; [exact I|].
assert (Hr : forall i, 0 <= i < snd r -> ro (fst r + i)) by (intros i Hi; apply H; apply Exists_cons_hd; unfold in_zr; lia).
destruct t as [|r' t']; [exact Hr|]. split; [exact Hr|]. apply IH. intros a Ha. apply H. apply Exists_cons_tl. exact Ha.
Qed.
Lemma crf_ro_in_list_to : forall ro l, crf_ro_in_list ro l -> forall a, Exists (in_zr a) l -> ro a.
Proof.
intros ro l. induction l as [|r t IH]; intros H a Ha; [inversion Ha|].
assert (Hr : forall i, 0 <= i < snd r -> ro (fst r + i)) by (destruct t; [exact H | exact (proj1 H)]).
apply Exists_cons in Ha as [Ha|Ha].
- unfold in_zr in Ha. replace a with (fst r + (a - fst r)) by lia. apply Hr. lia.
- destruct t as [|r' t']; [inversion Ha|]. exact (IH (proj2 H) a Ha).
Qed.
(* cmd_ro_in holds of a predicate exactly when every byte of cmd_ro_objs satisfies it *)
Lemma cmd_ro_in_of : forall ro, (forall a, Exists (in_zr a) cmd_ro_objs -> ro a) -> cmd_ro_in ro.
Proof. intros ro H. exact (crf_ro_in_list_of ro cmd_ro_objs H). Qed.
Lemma cmd_ro_in_to : forall ro, cmd_ro_in ro -> forall a, Exists (in_zr a) cmd_ro_objs -> ro a.
Proof. intros ro H. exact (crf_ro_in_list_to ro cmd_ro_objs H). Qed.
Fixpoint crf_bytes_list (rd : reader) (l : list (Z * list byte)) : Prop :=
match l with
| [] => True
| [e] => abytes_atR rd (fst e) (snd e)
| e :: t => abytes_atR rd (fst e) (snd e) /\ crf_bytes_list rd t
end.
Lemma crf_bytes_list_of : forall rd l, (forall e, In e l -> abytes_atR rd (fst e) (snd e)) -> crf_bytes_list rd l.
Proof.
intros rd l. induction l as [|e t IH]; intros H; [exact I|].
assert (He : abytes_atR rd (fst e) (snd e)) by (apply H; left; reflexivity).
destruct t as [|e' t']; [exact He|]. split; [exact He|]. apply IH. intros x Hx. apply H. right. exact Hx.
Qed.
(* cmd_ro_bytes holds of a reader that shows every byte of cmd_ro_list *)
Lemma crf_ro_bytes_of : forall rd, (forall e, In e cmd_ro_list -> abytes_atR rd (fst e) (snd e)) -> cmd_ro_bytes rd.
Proof. intros rd H. exact (crf_bytes_list_of rd cmd_ro_list H). Qed.
Lemma crf_ro_list_objs : map (fun e => (fst e, Z.of_nat (length (snd e)))) cmd_ro_list = cmd_ro_objs.
Proof. vm_compute. reflexivity. Qed.
Lemma crf_ro_list_in : forall e i, In e cmd_ro_list -> (i < length (snd e))%nat ->
Exists (in_zr (fst e + Z.of_nat i)) cmd_ro_objs.
Proof.
intros e i He Hi. rewrite <- crf_ro_list_objs. apply Exists_exists. exists (fst e, Z.of_nat (length (snd e))).
split; [apply in_map_iff; exists e; split; [reflexivity | exact He] | unfold in_zr; cbn [fst snd]; lia].
Qed.
(* every byte of [a, a + length l) shows the byte of [l] *)
Definition crf_bytes_b (rd : reader) (a : Z) (l : list byte) : bool :=
forallb (fun i => match rd (a + Z.of_nat i) with Some v => Z.eqb v (bv_unsigned (nth i l (Z_to_bv 8 0))) | None => false end)
(seq 0 (length l)).
Lemma crf_bytes_b_ok : forall rd a l, crf_bytes_b rd a l = true -> abytes_atR rd a l.
Proof.
intros rd a l H i Hi. unfold crf_bytes_b in H.
pose proof (proj1 (forallb_forall _ _) H i ltac:(apply in_seq; lia)) as Hb. cbn beta in Hb.
destruct (rd (a + Z.of_nat i)) as [v|]; [apply Z.eqb_eq in Hb; rewrite Hb; reflexivity | cbn in Hb; discriminate].
Qed.
(* the image's bytes *)
Definition crf_rom (segs : list Segment) : reader := fun a => option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).


(** * The facts about the image and its segments *)
Record cmd_img_facts {SK : YI16.sink_head} (segs : list Segment) (B : asyms) : Prop := {
(* every byte of CmdRo's objects is outside the record's owned ranges and the errno cell, in the image, read-only,
   and the image holds CmdRo's bytes there *)
cif_ro_unowned : cmd_ro_in (fun a => ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4));
cif_ro_img : cmd_ro_in (in_img segs);
cif_ro_in : cmd_ro_in (in_roP segs CMD_RLO CMD_RHI);
cif_ro_image : forall e, In e cmd_ro_list -> abytes_atR (crf_rom segs) (fst e) (snd e);
(* the bytes after each literal's end up to its 8-byte word end are read-only, and every read-only byte has an
   image byte (the read-only segments' file size is their memory size), so every state shows them *)
cif_tails_rom : forall e a, In e cmd_ro_ends -> e < a < e - e mod 8 + 8 -> in_rom segs a;
cif_rom_some : forall a, in_rom segs a -> seg_rom segs (Z_to_bv 64 a) <> None;
(* every byte of g_rec, record.spill and g_quitting is in the image, in no read-only segment and outside RELRO *)
cif_prog_img : forall a, inFP cmd_PG a -> in_img segs a;
cif_prog_not_ro : forall a, inFP cmd_PG a -> ~ in_roP segs CMD_RLO CMD_RHI a;
cif_errno : errno_rom segs B;
cif_relro_img : forall a, CMD_RLO <= a < CMD_RHI -> in_img segs a;
(* every read-only byte is below the overflow-list head (CmdBase.v's ro_below_ofl) and below the end of RELRO *)
cif_ro_below_ofl : forall a, in_roP segs CMD_RLO CMD_RHI a -> a < YI16.sk_ofl_head;
cif_ro_end : forall a, in_roP segs CMD_RLO CMD_RHI a -> 0x10000 <= a < 0xa6c68;
(* the stack guard's bytes have an image byte, so every state shows them *)
cif_guard_rom : forall a, 0x604158 <= a < 0x604160 -> seg_rom segs (Z_to_bv 64 a) <> None;
(* the bytes of a read-only byte's 8-byte word have an image byte, so every state shows them *)
cif_ro_word_some : forall e a, in_roP segs CMD_RLO CMD_RHI e -> e < a < e - e mod 8 + 8 -> seg_rom segs (Z_to_bv 64 a) <> None;
(* the four musl word-loop constants the strnlen wrapper reads (the shared libc string proofs'
   astrnlen_whole_realizesM over consts_view 0x10358 0x10378, the same address and bytes on fuzz_command.asan-ubsan)
   lie in a read-only segment, so arodata_okP covers them *)
cif_snl_rom : forall a, 0x10358 <= a < 0x10378 -> in_rom segs a
}.


Lemma crf_present_view : forall segs (H : word -> bool) mem a, apresent H mem a -> aview segs H mem a <> None.
Proof. intros segs H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.
Lemma crf_rom_view_some : forall segs (H : word -> bool) mem a, seg_rom segs (Z_to_bv 64 a) <> None -> aview segs H mem a <> None.
Proof.
intros segs H mem a Hr. unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|]; [cbn; discriminate|].
destruct (seg_rom segs (Z_to_bv 64 a)) as [b|] eqn:E; [cbn; discriminate | congruence].
Qed.
Lemma crf_rdword_some : forall (rd : reader) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) -> exists v, rdword rd a = Some v.
Proof.
intros rd a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
pose proof (H 1 ltac:(lia)) as H1. pose proof (H 2 ltac:(lia)) as H2. pose proof (H 3 ltac:(lia)) as H3.
pose proof (H 4 ltac:(lia)) as H4. pose proof (H 5 ltac:(lia)) as H5. pose proof (H 6 ltac:(lia)) as H6.
pose proof (H 7 ltac:(lia)) as H7.
destruct (rd a) as [b0|] eqn:E0; [|congruence].
destruct (rd (a + 1)) as [b1|] eqn:E1; [|congruence].
destruct (rd (a + 2)) as [b2|] eqn:E2; [|congruence].
destruct (rd (a + 3)) as [b3|] eqn:E3; [|congruence].
destruct (rd (a + 4)) as [b4|] eqn:E4; [|congruence].
destruct (rd (a + 5)) as [b5|] eqn:E5; [|congruence].
destruct (rd (a + 6)) as [b6|] eqn:E6; [|congruence].
destruct (rd (a + 7)) as [b7|] eqn:E7; [|congruence].
eexists; reflexivity.
Qed.
(* [a] is in a read-only segment *)
Definition crf_rom_b (segs : list Segment) (a : Z) : bool :=
existsb (fun s => negb (seg_writable s) && ((Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))) segs.
Lemma crf_rom_b_ok : forall segs a, crf_rom_b segs a = true -> in_rom segs a.
Proof.
intros segs a H. unfold crf_rom_b in H. apply existsb_exists in H as (s & Hs & Hb).
apply andb_prop in Hb as [Hw Hb]. apply negb_true_iff in Hw. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. split; [exact Hs | split; [exact Hw | lia]].
Qed.
Definition crf_ly0 : alayout := ALayout 0 0 0 0 0 0 0 0 0 0 0 0 [] [] 0 [] (0, 0) (fun _ => 0).
Definition crf_z8_addrs (l : list acell) (v : Z) : list Z :=
flat_map (fun c => match c with ACell (ANum a) w (AV (ANum x)) => if Nat.eqb w 8 && Z.eqb x v then [a] else [] | _ => [] end) l.
Lemma crf_z8_addrs_in : forall l a v, In (z8 (ANum a) v) l -> In a (crf_z8_addrs l v).
Proof.
intros l a v H. unfold crf_z8_addrs. apply in_flat_map. exists (z8 (ANum a) v). split; [exact H|].
cbn -[Z.eqb]. rewrite Z.eqb_refl. cbn. left. reflexivity.
Qed.

(** * The shadow facts every group uses *)
(* Every lemma below is closed over exactly `segs B LAWS HB` (Proof using), the form of the statements
   lib/B/Prog/CmdRecFacts.v proves, so a walk applies each with the same arguments. *)
Section base. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HB : CmdBSyms B.
(* AR shows the byte the record pins *)
Lemma cmd_byte_ok : forall ly S (W : world segs) mem md a v, AR segs B ly S W mem md -> cmd_byte a = Some v ->
aview segs (w_H W) mem a = Some v.
Proof using LAWS HB.
intros ly S W mem md a v HAR. unfold cmd_byte. destruct (crf_zsh_hit Tfib_zero_shadow a) eqn:E.
- intros Hv; injection Hv as <-. apply (crf_zsh_hit_ok _ Tfib_zero_shadow a); [|exact E].
  apply Forall_forall. intros r Hr. exact (cmd_zshadow_rec segs B LAWS HB ly S W mem md r HAR Hr).
- apply (crf_cells_byte_ok B ly). pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite (ts_const B HB ly) in HC.
  unfold Tfib_const in HC. apply Forall_app in HC as [_ HC]. exact HC.
Qed.
Lemma cmd_addressable_chk : forall ly S (W : world segs) mem md a n, AR segs B ly S W mem md -> cmd_addr_b a n = true ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof using LAWS HB.
intros ly S W mem md a n HAR H x Hx. pose proof (crf_zallf_ok _ _ _ H x ltac:(lia)) as Hb. cbn beta in Hb.
destruct (cmd_byte (shadow_of_addr SHADOW_OFF x)) as [s|] eqn:E; [|cbn in Hb; discriminate].
exists s. split; [exact (cmd_byte_ok ly S W mem md _ s HAR E)|].
unfold crf_saddr_okb in Hb. unfold saddr_ok. apply orb_prop in Hb as [Hb|Hb].
- left. apply Z.eqb_eq. exact Hb.
- right. apply andb_prop in Hb as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.

(** ** (ii) shadow words, aread_ok *)
Lemma cmd_hull_vis_chk : forall ly S (W : world segs) mem md a n, AR segs B ly S W mem md -> cmd_hull_b a n = true ->
shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof using LAWS HB.
intros ly S W mem md x n HAR H s Hs. pose proof (crf_zallf_ok _ _ _ H s ltac:(lia)) as Hb. cbn beta in Hb.
destruct (cmd_byte s) as [v|] eqn:E; [|cbn in Hb; discriminate]. rewrite (cmd_byte_ok ly S W mem md s v HAR E). discriminate.
Qed.
(* both checks: the addressability and shadow-word parts of aread_ok (lib/B/Rt/RtDefs.v) *)
Lemma cmd_aread_ok_chk : forall ly S (W : world segs) mem md a n, AR segs B ly S W mem md ->
cmd_addr_b a n = true -> cmd_hull_b a n = true ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof using LAWS HB.
intros ly S W mem md a n HAR H1 H2.
split; [exact (cmd_addressable_chk ly S W mem md a n HAR H1) | exact (cmd_hull_vis_chk ly S W mem md a n HAR H2)].
Qed.
(* a low address is outside every scratch window of a runtime entry: the stack is above the allocator's ceiling *)
Lemma cmd_stk_above : forall stk ly S (W : world segs) regs mem md a, ecall_pre_stk segs B stk ly S W regs mem md ->
a < kLowMemEnd -> ~ ascratch_stk stk regs a.
Proof using.
intros stk ly S W regs mem md a ((HAR & _) & Hlo & _) Ha Hs.
pose proof (lo_stk_ceil _ (am_layout _ _ _ _ (proj1 HAR))) as C. pose proof ASAN_CEIL_range as [CR _].
unfold ascratch_stk, kLowMemEnd in *. lia.
Qed.
(* a word the record pins *)
Lemma cmd_word_chk : forall ly S (W : world segs) mem md a v, AR segs B ly S W mem md -> cmd_word_b a v = true ->
rdword (aview segs (w_H W) mem) a = Some v.
Proof using LAWS HB.
intros ly S W mem md a v HAR H. unfold cmd_word_b in H. unfold rdword.
destruct (cmd_byte a) as [b0|] eqn:E0; [|cbn in H; discriminate].
destruct (cmd_byte (a + 1)) as [b1|] eqn:E1; [|cbn in H; discriminate].
destruct (cmd_byte (a + 2)) as [b2|] eqn:E2; [|cbn in H; discriminate].
destruct (cmd_byte (a + 3)) as [b3|] eqn:E3; [|cbn in H; discriminate].
destruct (cmd_byte (a + 4)) as [b4|] eqn:E4; [|cbn in H; discriminate].
destruct (cmd_byte (a + 5)) as [b5|] eqn:E5; [|cbn in H; discriminate].
destruct (cmd_byte (a + 6)) as [b6|] eqn:E6; [|cbn in H; discriminate].
destruct (cmd_byte (a + 7)) as [b7|] eqn:E7; [|cbn in H; discriminate].
rewrite (cmd_byte_ok ly S W mem md _ _ HAR E0), (cmd_byte_ok ly S W mem md _ _ HAR E1),
(cmd_byte_ok ly S W mem md _ _ HAR E2), (cmd_byte_ok ly S W mem md _ _ HAR E3),
(cmd_byte_ok ly S W mem md _ _ HAR E4), (cmd_byte_ok ly S W mem md _ _ HAR E5),
(cmd_byte_ok ly S W mem md _ _ HAR E6), (cmd_byte_ok ly S W mem md _ _ HAR E7).
apply Z.eqb_eq in H. subst v. reflexivity.
Qed.

End base.
