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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_pool_config_aux.v, with its module paths and module names changed; 366 of its 444 lines of code are new or changed and 463 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CmdRecBase.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths; Cmd*/cmd_* -> Seg*/seg_*; the Requires it does not use left out (AE2k, RtPFCmd, the plain proof's RecInv, CmdRep); CmdRo's object lists -> SegRo's (seg_ro_objs, seg_ro_list, made from SegRo.v by copy_seg.py); the image's end 0x606000 -> YG0f.kImgEnd; the read-only end 0xa7108 -> 0xa3748 (.got end); the stack guard 0x6045d8 -> SegInstA.guardA (0x5ff078, __stack_chk_guard); musl's word-loop constants 0x10358..0x10378 -> 0x10350..0x10370 (the same 32 bytes, read by memchr / strlen / strchrnul at 0x10350 and 0x10368); added for the contracts' sa_lit / sa_cat premise (the record pins a literal's shadow at every AR state): seg_lit_objs, every .rodata string object of the program's three modules (twin .symtab .str*, 84, address and length through its NUL from the pin), their closed check crf_lit_objs_chk, the catalogue's crf_cat_chk (fuzz_catalogue 0xa18e0, pin_spec.CAT_BYTES), and seg_lit_pinned / seg_cat_pinned (SegABase.sa_pinned, through seg_rd_b); seg_snl_unowned (musl's word-loop constants [SegInstA.memchr_loA, SegInstA.memchr_hiA) are outside the record's owned ranges and the errno cell) and seg_longl_pinned_tail (longl's slack 0x5de6f9..0x5de6ff has an image byte in tfibsegs, so every state's reader shows it); cif_snl_rom over SegInstA.memchr_loA / memchr_hiA. *)
(* The definitions and the shadow lemmas the per-binary facts of fuzz_command.asan share (lib/A/Prog/CmdRecFacts.v
   re-exports this file and the groups that use it: CmdRecCells, CmdRecRo, CmdRecImg, CmdRecCover, CmdRecRest).

   - the record's pinned bytes: AR shows the byte the allocator record pins at a shadow address (a zero-shadow range,
     or one of its absolute constant cells: cmd_byte, lib/A/Prog/CmdChk.v), so the checkers cmd_addr_b / cmd_hull_b
     give range_addressable and shadow_hull_vis at every AR state (cmd_addressable_chk, cmd_hull_vis_chk,
     cmd_aread_ok_chk), and cmd_word_b a word (cmd_word_chk). cgif states the same facts per range (cgif
     lib/A/AD1k.v:206-233, rodata_zero_shadow, rodata_hull_zero, rodata_shadow_facts).
   - the image: `cmd_img_facts segs B` holds the facts about the segments and the record's static lists that a walk
     cannot compute over an abstract SEGS (CmdRecImg.v proves them for the pinned image by computation), and CmdRo's
     objects as two lists in its order (cmd_ro_objs, cmd_ro_list).
   Every list fact is one boolean check closed by vm_compute; nothing here destructs a per-binary list. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AF0m AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegAddr SegPa SegImg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib SegObj SegPgBase SegBase SegRo SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegZsh.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Export SegChk.
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
Definition seg_rd_b (x n : Z) : bool :=
(0 <=? x) && (0 <=? n) && (x + n <=? kLowMemEnd - 1) && seg_addr_b x n && ((n <=? 0) || seg_hull_b x n).
(* the 8 bytes at [a] are pinned and make the word [v] *)
Definition seg_word_b (a v : Z) : bool :=
match seg_byte a, seg_byte (a + 1), seg_byte (a + 2), seg_byte (a + 3), seg_byte (a + 4), seg_byte (a + 5),
seg_byte (a + 6), seg_byte (a + 7) with
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
  | None => if crf_some (crf_cells_byte seg_cabs (shadow_of_addr SHADOW_OFF g)) then crf_cover_from f (g + 8) hi else false
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
forall x, g <= x < hi -> seg_byte (shadow_of_addr SHADOW_OFF x) <> None.
Proof.
induction fuel as [|f IH]; intros g hi Hg H x Hx; cbn [crf_cover_from] in H; [discriminate|].
destruct (hi <=? g) eqn:Ehi; [apply Z.leb_le in Ehi; lia|].
destruct (crf_zsh_jump Tfib_zero_shadow g) as [e|] eqn:EJ.
- destruct (crf_zsh_jump_spec _ _ _ EJ) as (r & Hr & Hb & He).
  destruct (Z_lt_le_dec x e) as [Hxe|Hxe].
  + unfold seg_byte. rewrite (crf_zsh_hit_of Tfib_zero_shadow _ r Hr); [discriminate|].
    assert (D1 : g / 8 <= x / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : x / 8 < fst r / 8 + snd r / 8) by (apply Z.div_lt_upper_bound; lia).
    unfold shadow_of_addr. lia.
  + apply (IH e hi); [subst e; rewrite Z.mul_comm; apply Z_mod_mult | exact H | lia].
- destruct (crf_cells_byte seg_cabs (shadow_of_addr SHADOW_OFF g)) as [v|] eqn:EC; [|cbn in H; discriminate].
  cbn [crf_some] in H.
  destruct (Z_lt_le_dec x (g + 8)) as [Hx8|Hx8].
  + assert (Q : x / 8 = g / 8). { clear - Hg Hx Hx8. Z.div_mod_to_equations. lia. }
    unfold seg_byte. destruct (crf_zsh_hit Tfib_zero_shadow (shadow_of_addr SHADOW_OFF x)); [discriminate|].
    unfold shadow_of_addr in *. rewrite Q, EC. discriminate.
  + apply (IH (g + 8) hi); [|exact H | lia]. clear - Hg. Z.div_mod_to_equations. lia.
Qed.
Lemma crf_hull_lo : forall p s, 0x10000 <= p -> shadow_addr p / 8 * 8 <= s -> 0x10000 <= 8 * (s - SHADOW_OFF).
Proof. intros p s Hp Hs. unfold shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia. Qed.
Lemma crf_hull_hi : forall y s, 0 <= y < kImgEnd -> s < shadow_addr y / 8 * 8 + 8 -> 8 * (s - SHADOW_OFF) < kImgEnd.
Proof. intros y s Hy Hs. unfold shadow_addr, SHADOW_OFF, kImgEnd in *. Z.div_mod_to_equations. lia. Qed.

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
Lemma crf_ro_endb_ok : forall segs a, crf_ro_endb segs 0x10000 0xa3748 = true ->
in_roP segs SEG_RLO SEG_RHI a -> 0x10000 <= a < 0xa3748.
Proof.
intros segs a H [(s & Hs & Hw & Ha)|Ha]; [|unfold SEG_RLO, SEG_RHI in Ha; lia].
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
(* CmdRo's 209 objects in cmd_ro_in's order (start, length), and their bytes in cmd_ro_bytes' order. If CmdRo.v is
   regenerated, cmd_ro_in_of, cmd_ro_in_to, crf_ro_bytes_of and crf_ro_list_objs stop compiling until these two
   lists are regenerated with it. *)
Definition seg_ro_objs : list (Z * Z) := [
(0x103c8, 11); (0x17667, 117); (0x176dc, 37); (0x1b009, 15); (0x1ba5a, 86); (0x1d8f6, 20); (0x20fe0, 25);
(0x21020, 4); (0x21040, 8); (0x21060, 7); (0x21080, 3); (0x210a0, 13); (0x210c0, 8); (0x210e0, 5); (0x21100, 8);
(0x21120, 5); (0x21140, 5); (0x21160, 7); (0x21180, 6); (0x211a0, 4); (0x211c0, 4); (0x211e0, 20); (0x21220, 6);
(0x21240, 7); (0x21260, 4); (0x21280, 5); (0x212a0, 3); (0x212c0, 6); (0x212e0, 6); (0x21300, 14); (0x21340, 3);
(0x21360, 13); (0x21380, 4); (0x213a0, 47); (0x21400, 28); (0x21440, 35); (0x214a0, 8); (0x214c0, 61);
(0x21520, 27); (0x21560, 58); (0x215c0, 59); (0x21620, 70); (0x216a0, 60); (0x21700, 45); (0x21760, 5);
(0x21780, 65); (0x21800, 6); (0x21820, 5); (0x21840, 2); (0x21860, 1); (0x21880, 52); (0x218e0, 7); (0x21900, 41);
(0x21960, 6); (0x21980, 146); (0x21a40, 53); (0x21aa0, 8); (0x21ac0, 5); (0x21ae0, 5); (0x21b00, 7); (0x21b20, 6);
(0x21b40, 4); (0x21b60, 4); (0x21b80, 4); (0x21ba0, 5); (0x21bc0, 3); (0x21be0, 6); (0x21c00, 104); (0x21ca0, 92);
(0x21d40, 6); (0x21d60, 23); (0x21da0, 6); (0x21dc0, 22); (0x21e00, 7); (0x21e20, 29); (0x21e60, 12); (0x21e80, 29);
(0x21ec0, 6); (0x21ee0, 23); (0x21f20, 6); (0x21f40, 24); (0x21f80, 7); (0x21fa0, 24); (0x21fe0, 7); (0x22000, 24);
(0x22040, 7); (0x22060, 23); (0x220a0, 7); (0x220c0, 23); (0x22100, 7); (0x22120, 24); (0x84d34, 8); (0x85ebc, 8);
(0x87a78, 8); (0x88da4, 8); (0x89854, 8); (0xa1880, 40); (0xa18e0, 3256)].
Definition seg_ro_list : list (Z * list byte) := [
(0x103c8, RO_lit_103c8); (0x17667, RO_lit_17667); (0x176dc, RO_lit_176dc); (0x1b009, RO_lit_1b009);
(0x1ba5a, RO_lit_1ba5a); (0x1d8f6, RO_lit_1d8f6); (0x20fe0, RO_lit_20fe0); (0x21020, RO_lit_21020);
(0x21040, RO_lit_21040); (0x21060, RO_lit_21060); (0x21080, RO_lit_21080); (0x210a0, RO_lit_210a0);
(0x210c0, RO_lit_210c0); (0x210e0, RO_lit_210e0); (0x21100, RO_lit_21100); (0x21120, RO_lit_21120);
(0x21140, RO_lit_21140); (0x21160, RO_lit_21160); (0x21180, RO_lit_21180); (0x211a0, RO_lit_211a0);
(0x211c0, RO_lit_211c0); (0x211e0, RO_m_key_role); (0x21220, RO_lit_21220); (0x21240, RO_lit_21240);
(0x21260, RO_lit_21260); (0x21280, RO_lit_21280); (0x212a0, RO_lit_212a0); (0x212c0, RO_lit_212c0);
(0x212e0, RO_lit_212e0); (0x21300, RO_lit_21300); (0x21340, RO_lit_21340); (0x21360, RO_lit_21360);
(0x21380, RO_lit_21380); (0x213a0, RO_lit_213a0); (0x21400, RO_lit_21400); (0x21440, RO_lit_21440);
(0x214a0, RO_lit_214a0); (0x214c0, RO_lit_214c0); (0x21520, RO_lit_21520); (0x21560, RO_lit_21560);
(0x215c0, RO_lit_215c0); (0x21620, RO_lit_21620); (0x216a0, RO_lit_216a0); (0x21700, RO_lit_21700);
(0x21760, RO_lit_21760); (0x21780, RO_lit_21780); (0x21800, RO_lit_21800); (0x21820, RO_lit_21820);
(0x21840, RO_lit_21840); (0x21860, RO_lit_21860); (0x21880, RO_lit_21880); (0x218e0, RO_lit_218e0);
(0x21900, RO_lit_21900); (0x21960, RO_lit_21960); (0x21980, RO_lit_21980); (0x21a40, RO_lit_21a40);
(0x21aa0, RO_lit_21aa0); (0x21ac0, RO_lit_21ac0); (0x21ae0, RO_lit_21ae0); (0x21b00, RO_lit_21b00);
(0x21b20, RO_lit_21b20); (0x21b40, RO_lit_21b40); (0x21b60, RO_lit_21b60); (0x21b80, RO_lit_21b80);
(0x21ba0, RO_lit_21ba0); (0x21bc0, RO_lit_21bc0); (0x21be0, RO_lit_21be0); (0x21c00, RO_lit_21c00);
(0x21ca0, RO_lit_21ca0); (0x21d40, RO_lit_21d40); (0x21d60, RO_lit_21d60); (0x21da0, RO_lit_21da0);
(0x21dc0, RO_lit_21dc0); (0x21e00, RO_lit_21e00); (0x21e20, RO_lit_21e20); (0x21e60, RO_lit_21e60);
(0x21e80, RO_lit_21e80); (0x21ec0, RO_lit_21ec0); (0x21ee0, RO_lit_21ee0); (0x21f20, RO_lit_21f20);
(0x21f40, RO_lit_21f40); (0x21f80, RO_lit_21f80); (0x21fa0, RO_lit_21fa0); (0x21fe0, RO_lit_21fe0);
(0x22000, RO_lit_22000); (0x22040, RO_lit_22040); (0x22060, RO_lit_22060); (0x220a0, RO_lit_220a0);
(0x220c0, RO_lit_220c0); (0x22100, RO_lit_22100); (0x22120, RO_lit_22120); (0x84d34, RO_lit_84d34);
(0x85ebc, RO_lit_85ebc); (0x87a78, RO_lit_87a78); (0x88da4, RO_lit_88da4); (0x89854, RO_lit_89854);
(0xa1880, RO_m_key_words); (0xa18e0, RO_fuzz_catalogue)].
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
Lemma seg_ro_in_of : forall ro, (forall a, Exists (in_zr a) seg_ro_objs -> ro a) -> seg_ro_in ro.
Proof. intros ro H. exact (crf_ro_in_list_of ro seg_ro_objs H). Qed.
Lemma seg_ro_in_to : forall ro, seg_ro_in ro -> forall a, Exists (in_zr a) seg_ro_objs -> ro a.
Proof. intros ro H. exact (crf_ro_in_list_to ro seg_ro_objs H). Qed.
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
Lemma crf_ro_bytes_of : forall rd, (forall e, In e seg_ro_list -> abytes_atR rd (fst e) (snd e)) -> seg_ro_bytes rd.
Proof. intros rd H. exact (crf_bytes_list_of rd seg_ro_list H). Qed.
Lemma crf_ro_list_objs : map (fun e => (fst e, Z.of_nat (length (snd e)))) seg_ro_list = seg_ro_objs.
Proof. vm_compute. reflexivity. Qed.
Lemma crf_ro_list_in : forall e i, In e seg_ro_list -> (i < length (snd e))%nat ->
Exists (in_zr (fst e + Z.of_nat i)) seg_ro_objs.
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
Record seg_img_facts {SK : YI16.sink_head} (segs : list Segment) (B : asyms) : Prop := {
(* every byte of CmdRo's objects is outside the record's owned ranges and the errno cell, in the image, read-only,
   and the image holds CmdRo's bytes there *)
cif_ro_unowned : seg_ro_in (fun a => ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4));
cif_ro_img : seg_ro_in (in_img segs);
cif_ro_in : seg_ro_in (in_roP segs SEG_RLO SEG_RHI);
cif_ro_image : forall e, In e seg_ro_list -> abytes_atR (crf_rom segs) (fst e) (snd e);
(* the bytes after each literal's end up to its 8-byte word end are read-only, and every read-only byte has an
   image byte (the read-only segments' file size is their memory size), so every state shows them *)
cif_tails_rom : forall e a, In e seg_ro_ends -> e < a < e - e mod 8 + 8 -> in_rom segs a;
cif_rom_some : forall a, in_rom segs a -> seg_rom segs (Z_to_bv 64 a) <> None;
(* every byte of g_rec, record.spill and g_quitting is in the image, in no read-only segment and outside RELRO *)
cif_prog_img : forall a, inFP seg_PG a -> in_img segs a;
cif_prog_not_ro : forall a, inFP seg_PG a -> ~ in_roP segs SEG_RLO SEG_RHI a;
cif_errno : errno_rom segs B;
cif_relro_img : forall a, SEG_RLO <= a < SEG_RHI -> in_img segs a;
(* every read-only byte is below the overflow-list head (CmdBase.v's ro_below_ofl) and below the end of RELRO *)
cif_ro_below_ofl : forall a, in_roP segs SEG_RLO SEG_RHI a -> a < YI16.sk_ofl_head;
cif_ro_end : forall a, in_roP segs SEG_RLO SEG_RHI a -> 0x10000 <= a < 0xa3748;
(* the stack guard's bytes have an image byte, so every state shows them *)
cif_guard_rom : forall a, SegInstA.guardA <= a < SegInstA.guardA + 8 -> seg_rom segs (Z_to_bv 64 a) <> None;
(* the bytes of a read-only byte's 8-byte word have an image byte, so every state shows them *)
cif_ro_word_some : forall e a, in_roP segs SEG_RLO SEG_RHI e -> e < a < e - e mod 8 + 8 -> seg_rom segs (Z_to_bv 64 a) <> None;
(* the four musl word-loop constants the strnlen wrapper reads (the shared libc string proofs'
   astrnlen_whole_realizesM over consts_view 0x10358 0x10378) lie in a read-only segment, so arodata_okP covers them *)
cif_snl_rom : forall a, SegInstA.memchr_loA <= a < SegInstA.memchr_hiA -> in_rom segs a
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
   lib/A/Prog/CmdRecFacts.v proves, so a walk applies each with the same arguments. *)
Section base. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HB : SegBSyms B.
(* AR shows the byte the record pins *)
Lemma seg_byte_ok : forall ly S (W : world segs) mem md a v, AR segs B ly S W mem md -> seg_byte a = Some v ->
aview segs (w_H W) mem a = Some v.
Proof using LAWS HB.
intros ly S W mem md a v HAR. unfold seg_byte. destruct (crf_zsh_hit Tfib_zero_shadow a) eqn:E.
- intros Hv; injection Hv as <-. apply (crf_zsh_hit_ok _ Tfib_zero_shadow a); [|exact E].
  apply Forall_forall. intros r Hr. exact (seg_zshadow_rec segs B LAWS HB ly S W mem md r HAR Hr).
- apply (crf_cells_byte_ok B ly). pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite (ts_const B HB ly) in HC.
  unfold Tfib_const in HC. apply Forall_app in HC as [_ HC]. exact HC.
Qed.
Lemma seg_addressable_chk : forall ly S (W : world segs) mem md a n, AR segs B ly S W mem md -> seg_addr_b a n = true ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof using LAWS HB.
intros ly S W mem md a n HAR H x Hx. pose proof (crf_zallf_ok _ _ _ H x ltac:(lia)) as Hb. cbn beta in Hb.
destruct (seg_byte (shadow_of_addr SHADOW_OFF x)) as [s|] eqn:E; [|cbn in Hb; discriminate].
exists s. split; [exact (seg_byte_ok ly S W mem md _ s HAR E)|].
unfold crf_saddr_okb in Hb. unfold saddr_ok. apply orb_prop in Hb as [Hb|Hb].
- left. apply Z.eqb_eq. exact Hb.
- right. apply andb_prop in Hb as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.

(** ** (ii) shadow words, aread_ok *)
Lemma seg_hull_vis_chk : forall ly S (W : world segs) mem md a n, AR segs B ly S W mem md -> seg_hull_b a n = true ->
shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof using LAWS HB.
intros ly S W mem md x n HAR H s Hs. pose proof (crf_zallf_ok _ _ _ H s ltac:(lia)) as Hb. cbn beta in Hb.
destruct (seg_byte s) as [v|] eqn:E; [|cbn in Hb; discriminate]. rewrite (seg_byte_ok ly S W mem md s v HAR E). discriminate.
Qed.
(* both checks: the addressability and shadow-word parts of aread_ok (lib/A/Rt/RtDefs.v) *)
Lemma seg_aread_ok_chk : forall ly S (W : world segs) mem md a n, AR segs B ly S W mem md ->
seg_addr_b a n = true -> seg_hull_b a n = true ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof using LAWS HB.
intros ly S W mem md a n HAR H1 H2.
split; [exact (seg_addressable_chk ly S W mem md a n HAR H1) | exact (seg_hull_vis_chk ly S W mem md a n HAR H2)].
Qed.
(* a low address is outside every scratch window of a runtime entry: the stack is above the allocator's ceiling *)
Lemma seg_stk_above : forall stk ly S (W : world segs) regs mem md a, ecall_pre_stk segs B stk ly S W regs mem md ->
a < kLowMemEnd -> ~ ascratch_stk stk regs a.
Proof using.
intros stk ly S W regs mem md a ((HAR & _) & Hlo & _) Ha Hs.
pose proof (lo_stk_ceil _ (am_layout _ _ _ _ (proj1 HAR))) as C. pose proof ASAN_CEIL_range as [CR _].
unfold ascratch_stk, kLowMemEnd in *. lia.
Qed.
(* a word the record pins *)
Lemma seg_word_chk : forall ly S (W : world segs) mem md a v, AR segs B ly S W mem md -> seg_word_b a v = true ->
rdword (aview segs (w_H W) mem) a = Some v.
Proof using LAWS HB.
intros ly S W mem md a v HAR H. unfold seg_word_b in H. unfold rdword.
destruct (seg_byte a) as [b0|] eqn:E0; [|cbn in H; discriminate].
destruct (seg_byte (a + 1)) as [b1|] eqn:E1; [|cbn in H; discriminate].
destruct (seg_byte (a + 2)) as [b2|] eqn:E2; [|cbn in H; discriminate].
destruct (seg_byte (a + 3)) as [b3|] eqn:E3; [|cbn in H; discriminate].
destruct (seg_byte (a + 4)) as [b4|] eqn:E4; [|cbn in H; discriminate].
destruct (seg_byte (a + 5)) as [b5|] eqn:E5; [|cbn in H; discriminate].
destruct (seg_byte (a + 6)) as [b6|] eqn:E6; [|cbn in H; discriminate].
destruct (seg_byte (a + 7)) as [b7|] eqn:E7; [|cbn in H; discriminate].
rewrite (seg_byte_ok ly S W mem md _ _ HAR E0), (seg_byte_ok ly S W mem md _ _ HAR E1),
(seg_byte_ok ly S W mem md _ _ HAR E2), (seg_byte_ok ly S W mem md _ _ HAR E3),
(seg_byte_ok ly S W mem md _ _ HAR E4), (seg_byte_ok ly S W mem md _ _ HAR E5),
(seg_byte_ok ly S W mem md _ _ HAR E6), (seg_byte_ok ly S W mem md _ _ HAR E7).
apply Z.eqb_eq in H. subst v. reflexivity.
Qed.

End base.
Definition seg_lit_objs : list (Z * Z) := [
(0x20fe0, 25); (0x21020, 4); (0x21040, 8); (0x21060, 7); (0x21080, 3); (0x210a0, 13); (0x210c0, 8); (0x210e0, 5);
(0x21100, 8); (0x21120, 5); (0x21140, 5); (0x21160, 7); (0x21180, 6); (0x211a0, 4); (0x211c0, 4); (0x21220, 6);
(0x21240, 7); (0x21260, 4); (0x21280, 5); (0x212a0, 3); (0x212c0, 6); (0x212e0, 6); (0x21300, 14); (0x21340, 3);
(0x21360, 13); (0x21380, 4); (0x213a0, 47); (0x21400, 28); (0x21440, 35); (0x214a0, 8); (0x214c0, 61);
(0x21520, 27); (0x21560, 58); (0x215c0, 59); (0x21620, 70); (0x216a0, 60); (0x21700, 45); (0x21760, 5);
(0x21780, 65); (0x21800, 6); (0x21820, 5); (0x21840, 2); (0x21860, 1); (0x21880, 52); (0x218e0, 7); (0x21900, 41);
(0x21960, 6); (0x21980, 146); (0x21a40, 53); (0x21aa0, 8); (0x21ac0, 5); (0x21ae0, 5); (0x21b00, 7); (0x21b20, 6);
(0x21b40, 4); (0x21b60, 4); (0x21b80, 4); (0x21ba0, 5); (0x21bc0, 3); (0x21be0, 6); (0x21c00, 104); (0x21ca0, 92);
(0x21d40, 6); (0x21d60, 23); (0x21da0, 6); (0x21dc0, 22); (0x21e00, 7); (0x21e20, 29); (0x21e60, 12); (0x21e80, 29);
(0x21ec0, 6); (0x21ee0, 23); (0x21f20, 6); (0x21f40, 24); (0x21f80, 7); (0x21fa0, 24); (0x21fe0, 7); (0x22000, 24);
(0x22040, 7); (0x22060, 23); (0x220a0, 7); (0x220c0, 23); (0x22100, 7); (0x22120, 24)].
Lemma crf_lit_objs_chk : forallb (fun an => seg_rd_b (fst an) (snd an)) seg_lit_objs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crf_cat_chk : seg_rd_b 0xa18e0 pin_spec.CAT_BYTES = true.
Proof. vm_compute. reflexivity. Qed.
Section lits. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HB : SegBSyms B.
Lemma crf_rd_b_addr : forall q n, seg_rd_b q n = true ->
forall ly S (W : world segs) mem md, AR segs B ly S W mem md -> sa_addr (aview segs (w_H W) mem) q n.
Proof using LAWS HB.
intros q n H ly S W mem md HAR. unfold seg_rd_b in H.
apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
apply andb_prop in H as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in H3.
unfold sa_addr, amem_range, kLowMemEnd in *. split; [lia|]. split; [lia|]. split; [left; lia|].
split; [exact (seg_addressable_chk segs B LAWS HB ly S W mem md q n HAR H4)|].
intros Hn. apply orb_prop in H5 as [H5|H5]; [apply Z.leb_le in H5; lia | exact (seg_hull_vis_chk segs B LAWS HB ly S W mem md q n HAR H5)].
Qed.
Lemma seg_lit_pinned : forall q n, In (q, n) seg_lit_objs -> sa_pinned segs B q n.
Proof using LAWS HB.
intros q n Hin. unfold sa_pinned. apply crf_rd_b_addr. exact (proj1 (forallb_forall _ _) crf_lit_objs_chk (q, n) Hin).
Qed.
Lemma seg_cat_pinned : sa_pinned segs B 0xa18e0 pin_spec.CAT_BYTES.
Proof using LAWS HB. unfold sa_pinned. apply crf_rd_b_addr. exact crf_cat_chk. Qed.
End lits.
Lemma crf_snl_sep : zr_disjointb (SegInstA.memchr_loA, SegInstA.memchr_hiA - SegInstA.memchr_loA) (TFIB_ERRNO, 4) &&
forallb (zr_disjointb (SegInstA.memchr_loA, SegInstA.memchr_hiA - SegInstA.memchr_loA)) Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.
Lemma seg_snl_unowned : forall B, SegBSyms B -> forall a, SegInstA.memchr_loA <= a < SegInstA.memchr_hiA ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B HB a Ha. pose proof crf_snl_sep as H. apply andb_prop in H as [H1 H2].
rewrite (ts_owned B HB), (ts_errno B HB). split.
- apply (crf_disj_notin (SegInstA.memchr_loA, SegInstA.memchr_hiA - SegInstA.memchr_loA)); [exact H2 | unfold in_zr; cbn [fst snd]; lia].
- intros He. unfold zr_disjointb in H1. cbn [fst snd] in H1. apply orb_prop in H1 as [H1|H1]; apply Z.leb_le in H1; lia.
Qed.
Lemma crf_longl_tail_chk : crf_zallt (fun x => crf_some (seg_rom tfibsegs (Z_to_bv 64 x))) (A_LONGL + 121) 7 = true.
Proof. vm_compute. reflexivity. Qed.
Section tails. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma seg_longl_pinned_tail : forall B, sa_pinned_tail tfibsegs B (A_LONGL + 120).
Proof.
intros B. unfold sa_pinned_tail, sa_tail. intros ly S W mem md _ x Hx. apply crf_rom_view_some. apply crf_some_ok.
pose proof (crf_zallt_ok _ _ _ crf_longl_tail_chk x) as H. cbn beta in H. apply H.
unfold A_LONGL in *. cbn in Hx |- *. lia.
Qed.
End tails.
