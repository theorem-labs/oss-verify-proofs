(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_grant/proofs/lib/A/Prog/KindOfLink1.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/A/Prog/P_kind_of_link1.v, with its module names changed; 1490 of its 1537 lines of code are new or changed and 128 lines of the source are left out. *)
(* reac_ctrl_build_scene_step (fuzz_scene.asan 0x83834, 234 instructions): the contract of the
   memory-checked build's code and its walk.

   blk is a local of the CALLER's own frame (both call sites in LLVMFuzzerTestOneInput pass a
   slot of the frame from the class-8 frame allocator), so the contract takes the caller's journal and
   returns it extended, in the shape of the core's intrinsic lemma aj_intrin_at
   (Reusable/YCbq.v): a write into a frame of the journal's `own` is awr_byte's own-frame case,
   which a journal started by the callee (own = []) cannot use (BLK-FRAME.md (sha256 59cb1284237b; internal record)).

   What the code does (accepting path): the fill __asan_memset(blk + 2, 0, 32); blk[0] = 0xcd and
   blk[1] = 0xea; then FIRST (step 0), MIDDLE (1..341) or LAST (342) writes the header bytes and copies
   the payload with __asan_memcpy (LAST twice: 14 body bytes, then the 12 TAIL_TRAILER bytes); the
   inlined checksum stamp sums blk[2..33) in a count-down loop and stores the negated sum at blk[33];
   a0 = 0. Every store and load of blk is preceded by the inline check of its metadata byte, which
   passes because blk's 34 bytes are marked usable. Refusing path (blk = 0, body = 0, n <> 8904 or
   unsigned step > 342): a0 = -1 and only the own stack window changes.

   Numerals, each read from fuzz_scene.asan (unstripped sha256 6ed872f7cc8c1e42..., loaded bytes equal to
   bin sha256 43654a025fd02e1f...):
     8904      0x83864 lui a1,0x2 ; 0x83868 addiw a1,a1,712  (0x22c8)
     342       0x83874 li a1,342 ; 0x838cc li a2,342
     34        highest store 0x83ae8 sb a2,0(a1), a1 = s0 + 33 (0x83acc); fill 0x83888 addi s1,s0,2 ; 0x8388c li a2,32
     12        0x83a18 li a2,12
     0x20e20   0x83a10 auipc a1,0xfff9d ; 0x83a14 addi a1,a1,1040 = symbol reac_ctrl_build_scene_step.TAIL_TRAILER
               (scene_listing object 12, SceneAddr.v); its bytes 00 00 03 00 00 00 01 00 00 00 00 00 (.rodata)
     48        0x83834 addi sp,sp,-48 (saves ra@40 s0@32 s1@24 s2@16 s3@8 s4@0, 0x83838..0x8384c)
     0x68      return point of the fill: 0x8389c - 0x83834
     0x250     return point of the last copy: 0x83a84 - 0x83834
     0x83834   symbol reac_ctrl_build_scene_step (size 936); AF_reac_ctrl_build_scene_step = 0xfbc (SceneList.v)
     the shadow base: 0x8387c auipc a0,0x18 ; 0x83880 ld a0,-364(a0): GOT word 0x9b710 (object 1) holds
               0xa37f8 = __asan_shadow_memory_dynamic_address (object 16), read through PALib.
     205, 234  blk[0] = 0xcd (store 0x838b4), blk[1] = 0xea (store 0x838d0)
     header    FIRST stores blk[2..8] = 1, 1, 0, 24, -, 0x22, 0xc8 (0x838f4..0x83974, blk[6] from the fill);
               LAST blk[2..5] = 1, 2, 0, 14 (0x839a4..0x839f4); MIDDLE blk[2] = 1, blk[6] = 0, blk[5] = 26
               (0x83a30, 0x83a44, 0x83a6c); the same bytes as SceneBlock.scene_block
     copies    FIRST (blk + 9, body, 24): 0x83978, 0x83980, 0x8397c; LAST (blk + 7, body + 8890, 14): 0x839f0,
               0x839f8 lui a1,0x2 ; 0x839fc addiw a1,a1,698 ; 0x83a00 add, 0x83a04; LAST (blk + 21, TAIL_TRAILER, 12):
               0x83a0c, 0x83a10..0x83a14, 0x83a18; MIDDLE (blk + 7, body + 24 + 26 (step - 1), 26): 0x83a70,
               0x83a5c addiw s3,s3,-1 ; 0x83a64 mul ; 0x83a74 add ; 0x83a78 addi 24, 0x83a7c; the copies jal 0x83a80
               (LAST's first at 0x83a08), the fill jal 0x83898
     242, 257  scene_listing atoms of objects 1 and 16 (A_OBJ, SceneAddr.v / SceneACja.v header)
   Named entry-state obligations the composition discharges (not proved here):
     TAIL_TRAILER's metadata, expected content (scene-startup-cmp.md (sha256 25e76e6389d6; internal record), section 6, the same in asan and
     asan-ubsan, the donor's AB01 rule; metadata address = (a >> 3) + 0x7fff8000): 0x7fffc1c4 = 0x00, 0x7fffc1c5 = 0x04,
     0x7fffc1c6..0x7fffc1c7 = 0xf9, so [0x20e20, 0x20e2c) is usable (range_addressable 12) and its window is mapped
     (shadow_hull_vis 12); TAIL_TRAILER's 12 bytes; blk's marks (the caller's entry walk delivers them); blk apart
     from TAIL_TRAILER. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import
PaRun PaShadow PaStep PaJournal SceneSyms SceneList ScenePa ScenePaLib.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import YC81 YC4b YC1g YC1h YCbw YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------ *)
(* The constants of the code.                                                                 *)
Definition SCENE_BYTES : Z := 8904.
Definition SCENE_LAST : Z := 342.
Definition BLK_LEN : Z := 34.
Definition TT_LEN : Z := 12.
Definition SCENE_STEP_FRAME : Z := 48.
Definition SCENE_STEP_WIN : Z := SCENE_STEP_FRAME + ESTACK.
Definition O_FILL_RET : Z := 0x68.
Definition O_COPY_RET : Z := 0x250.
Definition OBJ_TT : nat := 12%nat.

(* The proof uses the wrappers' stack window ESTACK only through 0 <= ESTACK. *)
Lemma ESTACK_nonneg : 0 <= ESTACK.
Proof. unfold ESTACK; lia. Qed.

Definition scene_step_okZ (blk body n st : Z) : bool :=
  negb (blk =? 0) && negb (body =? 0) && (n =? SCENE_BYTES) && (st <=? SCENE_LAST).

(* ------------------------------------------------------------------------------------------ *)
(* Facts about the block the accepting path writes (SceneBlock.v, released, unchanged).        *)
Lemma byte_range : forall x : byte, 0 <= bv_unsigned x < 256.
Proof. intros x. pose proof (bv_unsigned_in_range 8 x) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.

Lemma length_scene_payload : forall b k, 8904 <= Z.of_nat (length b) -> 0 <= k <= 342 ->
  length (scene_payload b k) = 26%nat.
Proof.
  intros b k Hb Hk. unfold scene_payload, scene_off.
  destruct (Z.eqb_spec k 0) as [->|H0].
  - cbn [Z.eqb length app]. rewrite length_firstn, Nat.min_l by lia. reflexivity.
  - destruct (Z.eqb_spec k 342) as [->|H342].
    + cbn [Z.eqb]. rewrite length_app, length_firstn, length_skipn. cbn [scene_trailer map length].
      rewrite Nat.min_l by lia. reflexivity.
    + cbn [Z.eqb]. rewrite length_firstn, length_skipn, Nat.min_l by lia. reflexivity.
Qed.

Lemma length_scene_fields : forall b k, 8904 <= Z.of_nat (length b) -> 0 <= k <= 342 ->
  length (scene_fields b k) = 31%nat.
Proof. intros b k Hb Hk. unfold scene_fields. rewrite length_app, (length_scene_payload b k Hb Hk). reflexivity. Qed.

Lemma length_scene_block : forall b k, 8904 <= Z.of_nat (length b) -> 0 <= k <= 342 ->
  length (scene_block b k) = 34%nat.
Proof.
  intros b k Hb Hk. unfold scene_block. rewrite !length_app, (length_scene_fields b k Hb Hk). reflexivity.
Qed.

(* The block's fields are its bytes 2..32, and its last byte the negated sum of them. *)
Lemma scene_block_field : forall b k j, 8904 <= Z.of_nat (length b) -> 0 <= k <= 342 -> (j < 31)%nat ->
  nth (2 + j) (scene_block b k) (Z_to_bv 8 0) = nth j (scene_fields b k) (Z_to_bv 8 0).
Proof.
  intros b k j Hb Hk Hj. unfold scene_block. cbn [app].
  change (2 + j)%nat with (S (S j)). cbn [nth].
  rewrite app_nth1 by (rewrite (length_scene_fields b k Hb Hk); lia). reflexivity.
Qed.

Lemma scene_block_last : forall b k, 8904 <= Z.of_nat (length b) -> 0 <= k <= 342 ->
  nth 33 (scene_block b k) (Z_to_bv 8 0) =
  Z_to_bv 8 ((256 - byte_sum (scene_fields b k) mod 256) mod 256).
Proof.
  intros b k Hb Hk. unfold scene_block. cbn [app].
  change 33%nat with (S (S 31)). cbn [nth].
  rewrite app_nth2 by (rewrite (length_scene_fields b k Hb Hk); lia).
  rewrite (length_scene_fields b k Hb Hk). reflexivity.
Qed.

(* byte_sum of a 31-byte list, written out. *)
Definition bu (l : list byte) (j : nat) : Z := bv_unsigned (nth j l (Z_to_bv 8 0)).
Lemma byte_sum_31 : forall l, length l = 31%nat ->
  byte_sum l = bu l 0 + bu l 1 + bu l 2 + bu l 3 + bu l 4 + bu l 5 + bu l 6 + bu l 7 + bu l 8 + bu l 9
             + bu l 10 + bu l 11 + bu l 12 + bu l 13 + bu l 14 + bu l 15 + bu l 16 + bu l 17 + bu l 18 + bu l 19
             + bu l 20 + bu l 21 + bu l 22 + bu l 23 + bu l 24 + bu l 25 + bu l 26 + bu l 27 + bu l 28 + bu l 29
             + bu l 30.
Proof.
  intros l Hl.
  do 31 (destruct l as [|? l]; [cbn [length] in Hl; lia|]).
  destruct l; [|cbn [length] in Hl; lia].
  unfold bu, byte_sum. cbn [nth fold_right]. lia.
Qed.

Lemma sb_nth_firstn : forall (l : list byte) i n d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros l. induction l as [|x l IH]; intros i n d Hi; destruct n as [|n]; try lia; cbn [firstn nth];
    [destruct i; reflexivity | destruct i as [|i]; [reflexivity | apply IH; lia]].
Qed.

Lemma sb_nth_skipn : forall (l : list byte) i n d, nth i (skipn n l) d = nth (n + i) l d.
Proof.
  intros l i n. revert l. induction n as [|n IH]; intros l d; [reflexivity|].
  destruct l as [|x l]; cbn [skipn nth Nat.add]; [destruct i; reflexivity | apply IH].
Qed.

Lemma bu_lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hc. Qed.

(* The 33 bytes before the checksum, for each of the three kinds of step. *)
Lemma sb_first : forall b j, 8904 <= Z.of_nat (length b) -> (j < 33)%nat ->
  bu (scene_block b 0) j = if (j <? 9)%nat then nth j [205; 234; 1; 1; 0; 24; 0; 34; 200] 0 else bu b (j - 9).
Proof.
  intros b j Hb Hj. unfold bu, scene_block, scene_fields, scene_payload, scene_seg, scene_len. cbn [Z.eqb app].
  destruct (Nat.ltb_spec j 9) as [Hl | Hl].
  - do 9 (destruct j as [|j]; [cbn [nth]; apply bu_lit; lia|]). lia.
  - replace j with (9 + (j - 9))%nat at 1 by lia. cbn [nth Nat.add].
    rewrite app_nth1 by (rewrite length_firstn, Nat.min_l by lia; lia). rewrite sb_nth_firstn by lia. reflexivity.
Qed.

Lemma sb_last : forall b j, 8904 <= Z.of_nat (length b) -> (j < 33)%nat ->
  bu (scene_block b 342) j =
  if (j <? 7)%nat then nth j [205; 234; 1; 2; 0; 14; 0] 0
  else if (j <? 21)%nat then bu b (Z.to_nat 8890 + (j - 7)) else bu scene_trailer (j - 21).
Proof.
  intros b j Hb Hj. unfold bu, scene_block, scene_fields, scene_payload, scene_seg, scene_len, scene_off. cbn [Z.eqb Pos.eqb app].
  destruct (Nat.ltb_spec j 7) as [Hl | Hl].
  - do 7 (destruct j as [|j]; [cbn [nth]; apply bu_lit; lia|]). lia.
  - replace j with (7 + (j - 7))%nat at 1 by lia. cbn [nth Nat.add].
    assert (HL : length (firstn 14 (skipn (Z.to_nat 8890) b)) = 14%nat)
      by (rewrite length_firstn, length_skipn, Nat.min_l by lia; reflexivity).
    assert (HT : length scene_trailer = 12%nat) by reflexivity.
    rewrite app_nth1 by (rewrite length_app, HL, HT; lia).
    destruct (Nat.ltb_spec j 21) as [Hm | Hm].
    + rewrite app_nth1 by lia. rewrite sb_nth_firstn by lia. rewrite sb_nth_skipn. reflexivity.
    + rewrite app_nth2 by lia. rewrite HL. f_equal. f_equal. lia.
Qed.

Lemma sb_mid : forall b st j, 8904 <= Z.of_nat (length b) -> 1 <= st <= 341 -> (j < 33)%nat ->
  bu (scene_block b st) j =
  if (j <? 7)%nat then nth j [205; 234; 1; 0; 0; 26; 0] 0 else bu b (Z.to_nat (24 + 26 * (st - 1)) + (j - 7)).
Proof.
  intros b st j Hb Hst Hj. unfold bu, scene_block, scene_fields, scene_payload, scene_seg, scene_len, scene_off.
  replace (st =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (st =? 342) with false by (symmetry; apply Z.eqb_neq; lia). cbn [app].
  destruct (Nat.ltb_spec j 7) as [Hl | Hl].
  - do 7 (destruct j as [|j]; [cbn [nth]; apply bu_lit; lia|]). lia.
  - replace j with (7 + (j - 7))%nat at 1 by lia. cbn [nth Nat.add].
    rewrite app_nth1 by (rewrite length_firstn, length_skipn, Nat.min_l by lia; lia).
    rewrite sb_nth_firstn by lia. rewrite sb_nth_skipn. reflexivity.
Qed.

Lemma trailer_bytes : forall i, (i < 12)%nat ->
  bu scene_trailer i = nth i [0; 0; 3; 0; 0; 0; 1; 0; 0; 0; 0; 0] 0.
Proof. intros i Hi. do 12 (destruct i as [|i]; [reflexivity|]). lia. Qed.

Lemma neg_low_byte : forall s, 0 <= s < 2 ^ 64 ->
  ((- s) mod 2 ^ 64) mod 256 = (256 - s mod 256) mod 256.
Proof.
  intros s Hs.
  rewrite Z.mod_mod_divide by first [exists (2 ^ 56); reflexivity | lia].
  replace (- s) with (0 - s) by lia.
  rewrite (Zminus_mod 0 s 256), (Zminus_mod 256 (s mod 256) 256), Z.mod_same, Z.mod_mod, Zmod_0_l by lia.
  reflexivity.
Qed.

Lemma mod16_sub48 : forall s o, s mod 16 = 0 -> o mod 16 = 0 -> (s + o - 48) mod 16 = 0.
Proof. intros s o Hs Ho. rewrite Zminus_mod, Z.add_mod, Hs, Ho by lia. reflexivity. Qed.
Lemma mod16_add : forall s o, s mod 16 = 0 -> o mod 16 = 0 -> (s + o) mod 16 = 0.
Proof. intros s o Hs Ho. rewrite Z.add_mod, Hs, Ho by lia. reflexivity. Qed.
Lemma mod16_m48 : forall o, o mod 16 = 0 -> (o - 48) mod 16 = 0.
Proof. intros o Ho. rewrite Zminus_mod, Ho by lia. reflexivity. Qed.

(* ------------------------------------------------------------------------------------------ *)
(* Values of the symbolic terms the walk meets.                                               *)
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma U_sub0 : forall E b y, U E b = y -> U E (SAlu ALU_SUB (SLit 0) b) = (- y) mod 2 ^ 64.
Proof.
  intros E b y Hb. rewrite U_SAlu, Hb, U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
  rewrite (Z.mod_small 0) by lia. f_equal; lia.
Qed.
Lemma U_zext8 : forall E a x, U E a = x -> 0 <= x < 256 -> U E (SExt false 8 a) = x.
Proof.
  intros E a x Ha Hx. rewrite U_SExt, Ha. cbv beta iota. change (2 ^ Z.of_N 8) with 256.
  rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
End u.

(* The value of a sum, loads and negation term, bottom up; the leaves are atoms whose values the
   context names (ew E k = Z_to_bv 64 v) with their ranges. *)
Ltac ueval :=
  lazymatch goal with
  | |- U ?E (SAlu ALU_ADD ?a ?b) = _ =>
      eapply U_add_small; [ueval | ueval | lia | lia | lia]
  | |- U ?E (SAlu ALU_SUB (SLit 0) ?b) = _ => eapply U_sub0; ueval
  | |- U ?E (SExt false 8 ?a) = _ => eapply U_zext8; [ueval | lia]
  | |- U ?E (SOff ?k 0) = _ => eapply U_atom; [eassumption | lia]
  | |- U ?E (SLit ?z) = _ => apply U_lit; lia
  end.

(* ------------------------------------------------------------------------------------------ *)
(* A byte of a symbolic region whose chunk holds a literal (a store of a constant, or the fill).  *)
Fixpoint chunk_lit (cs : list YP09.chunk) (j : Z) : option Z :=
  match cs with
  | [] => None
  | c :: cs' =>
      if (YP09.c_off c <=? j) && (j <? YP09.c_off c + YP09.c_len c) then
        match YP09.c_val c with
        | CZero _ => Some 0
        | CVal w (SLit z) => if (w =? 1)%N then Some (z mod 256) else None
        | _ => None
        end
      else chunk_lit cs' j
  end.

Lemma byte_lit_mod : forall z, Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 z)) (8 * 0)) = Z_to_bv 8 (z mod 256).
Proof.
  intros z. change (8 * 0) with 0. rewrite Z.shiftr_0_r. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_mod_divide z (2 ^ 64) 256) by first [exists (2 ^ 56); reflexivity | lia]. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section m. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Lemma chunk_lit_sound : forall E m base cs j v,
  Forall (YP09.chunk_ok segs E m base) cs -> chunk_lit cs j = Some v ->
  mbyte segs m (base + j) = Some (Z_to_bv 8 v).
Proof.
  intros E m base cs. induction cs as [|c cs IH]; intros j v Hok Hl; [discriminate Hl|].
  inversion Hok as [|? ? Hc Hcs]; subst. cbn [chunk_lit] in Hl.
  destruct ((YP09.c_off c <=? j) && (j <? YP09.c_off c + YP09.c_len c)) eqn:Hin; [|exact (IH j v Hcs Hl)].
  apply andb_prop in Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct (Hc (j - YP09.c_off c) ltac:(lia)) as (bt & Hcb & Hmb).
  replace (base + YP09.c_off c + (j - YP09.c_off c)) with (base + j) in Hmb by lia.
  rewrite Hmb. f_equal.
  destruct c as [off cv]. cbn [YP09.c_val YP09.c_off YP09.c_len YP09.cv_len] in *.
  destruct cv as [w e | len | len | d s len]; try discriminate Hl.
  - destruct e; try discriminate Hl. destruct (N.eqb_spec w 1) as [->|]; [|discriminate Hl].
    injection Hl as <-. cbn [YP09.cbyte sv_denot] in Hcb. injection Hcb as <-.
    cbv [YP09.c_len YP09.cv_len YP09.c_val Z.of_N] in H2.
    assert (j - off = 0) as -> by lia. unfold YP09.byte_of_word. apply byte_lit_mod.
  - injection Hl as <-. cbn [YP09.cbyte] in Hcb. injection Hcb as <-. reflexivity.
Qed.

Lemma aview_of_mbyte_lit : forall H m a v,
  mbyte segs (mrestrict H m) a = Some (Z_to_bv 8 v) -> 0 <= v < 256 -> aview segs H m a = Some v.
Proof.
  intros H m a v Hm Hv. unfold aview. rewrite Hm. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.

Lemma mbyte_of_aview_some : forall H m a v,
  aview segs H m a = Some v -> mbyte segs (mrestrict H m) a = Some (Z_to_bv 8 v).
Proof.
  intros H m a v Ha. unfold aview in Ha. destruct (mbyte segs (mrestrict H m) a) as [x|] eqn:Hm; [|discriminate Ha].
  cbn [option_map] in Ha. injection Ha as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma aview_same_raw : forall H (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview segs H m' a = aview segs H m a.
Proof. intros H m m' a E. unfold aview, mbyte, mrestrict. cbv beta. rewrite E. reflexivity. Qed.

Lemma hull_sub : forall (rd : Z -> option Z) x n x' n',
  shadow_hull_vis rd x n -> 0 <= x -> x <= x' -> x' + n' <= x + n -> 0 < n' -> shadow_hull_vis rd x' n'.
Proof.
  intros rd x n x' n' HV H0 H1 H2 H3 s Hs. apply HV. unfold shadow_addr in *.
  assert (A1 : x / 8 <= x' / 8) by (apply Z.div_le_mono; lia).
  assert (A2 : (x' + n' - 1) / 8 <= (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (A3 : (SHADOW_OFF + x / 8) / 8 <= (SHADOW_OFF + x' / 8) / 8) by (apply Z.div_le_mono; lia).
  assert (A4 : (SHADOW_OFF + (x' + n' - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
  lia.
Qed.

(* Metadata reads: unchanged when nothing in the metadata band [SHADOW_OFF, kHighShadowEnd) changed. *)
Lemma ra_kept : forall (rd rd' : Z -> option Z) a n,
  (forall s, SHADOW_OFF <= s < kHighShadowEnd -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
  intros rd rd' a n Hk H0 Hn HR x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. split; [|exact Ho].
  rewrite Hk; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF, kHighShadowEnd.
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.

Lemma hull_kept : forall (rd rd' : Z -> option Z) a n,
  (forall s, SHADOW_OFF <= s < kHighShadowEnd -> rd' s = rd s) -> 0 <= a -> 0 < n -> a + n <= 2 ^ 47 - 64 ->
  shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof.
  intros rd rd' a n Hk H0 Hn0 Hn HV s Hs. rewrite Hk; [exact (HV s Hs)|].
  unfold shadow_addr, SHADOW_OFF, kHighShadowEnd in *.
  pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
  assert ((a + n - 1) / 8 < 2 ^ 44 - 8) by (apply Z.div_lt_upper_bound; lia).
  pose proof (Z.div_mod (2147450880 + a / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 + a / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)).
  lia.
Qed.
End m.

(* ------------------------------------------------------------------------------------------ *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).

Definition A_reac_ctrl_build_scene_stepP : Z := BASE + AF_reac_ctrl_build_scene_step.
Definition A_TT : Z := VAL (A_OBJ OBJ_TT).

Section h.
Variable B : asyms.

(* The contract. *)
Definition treac_ctrl_build_scene_step_post (regs : bvmap 5 word) (STK sp0 : Z) (FP : list (Z * Z))
  ly S (W0 : world SEGS) mem0 md0 own lyc Sc (W : world SEGS) mem (k : Z)
  (blk body n st : Z) (b : list byte) : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
    ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
    aregs_preserved regs regs' /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SCENE_STEP_WIN <= a < spZ regs) ->
       (scene_step_okZ blk body n st = true -> ~ (blk <= a < blk + BLK_LEN)) ->
       aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
    if scene_step_okZ blk body n st
    then getr regs' 10 = w64 0 /\
         (forall i, 0 <= i < BLK_LEN ->
            aview SEGS (w_H W) mem' (blk + i) = Some (bv_unsigned (nth (Z.to_nat i) (scene_block b st) (Z_to_bv 8 0))))
    else getr regs' 10 = w64 (-1).

Definition treac_ctrl_build_scene_step_spec : Prop :=
  forall (W : world SEGS) (regs : bvmap 5 word) mem md (STK sp0 o : Z) (FP : list (Z * Z))
         ly S (W0 : world SEGS) mem0 md0 own lyc Sc (k : Z) (blk body n st : Z) (b : list byte),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> SCENE_STEP_WIN - o <= STK ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 blk -> getr regs 11 = w64 body -> getr regs 12 = w64 n -> getr regs 13 = w64 st ->
  0 <= blk < 2 ^ 64 -> 0 <= body < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= st < 2 ^ 64 ->
  (scene_step_okZ blk body n st = true ->
     (exists cid pos, In (cid, pos) own /\ 0 <= cid /\
        frame_addr lyc cid pos <= blk /\ blk + BLK_LEN <= frame_addr lyc cid pos + fs_frame_bytes cid) /\
     (forall a, blk <= a < blk + BLK_LEN -> apresent (w_H W) mem a) /\
     range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF blk BLK_LEN /\
     shadow_hull_vis (aview SEGS (w_H W) mem) blk BLK_LEN /\
     (exists pq mq, In (pq, mq) (ablocks B lyc Sc) /\ pq <= body /\ body + SCENE_BYTES <= pq + req_size mq) /\
     length b = Z.to_nat SCENE_BYTES /\
     (forall i, 0 <= i < SCENE_BYTES ->
        aview SEGS (w_H W) mem (body + i) = Some (bv_unsigned (nth (Z.to_nat i) b (Z_to_bv 8 0)))) /\
     (forall i, 0 <= i < TT_LEN ->
        aview SEGS (w_H W) mem (A_TT + i) = Some (bv_unsigned (nth (Z.to_nat i) scene_trailer (Z_to_bv 8 0)))) /\
     range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF A_TT TT_LEN /\
     shadow_hull_vis (aview SEGS (w_H W) mem) A_TT TT_LEN /\
     (A_TT + TT_LEN <= blk \/ blk + BLK_LEN <= A_TT)) ->
  SRr SEGS W (cfg_at SEGS A_reac_ctrl_build_scene_stepP regs mem md)
    (treac_ctrl_build_scene_step_post regs STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem k blk body n st b).

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA SS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy).
Let HBgot := pal_got_shadow B TL.
Let HBcell := pal_cell B TL.
Let RUN := paj_run (SK := SK) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_scene) (PI := PI).

(* ------------------------------------------------------------------------------------------ *)
(* The invariant the walk keeps between its steps: outside the stack window below the entry sp
   and (accepting) outside blk every byte keeps its entry value, and present bytes stay present. *)
Definition sinv (W : world SEGS) (mem memc : word -> option byte) (lo hi : Z) (ok : bool) (blk : Z) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> (ok = true -> ~ (blk <= a < blk + BLK_LEN)) ->
     aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) memc a).

Lemma sinv_refl : forall W mem lo hi ok blk, sinv W mem mem lo hi ok blk.
Proof. intros. split; intros; [reflexivity | assumption]. Qed.

Lemma sinv_run : forall W mem m1 m2 E rs lo hi ok blk,
  sinv W mem m1 lo hi ok blk ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  (forall a, in_wrange E rs a -> lo <= a < hi \/ (ok = true /\ blk <= a < blk + BLK_LEN)) ->
  sinv W mem m2 lo hi ok blk.
Proof.
  intros W mem m1 m2 E rs lo hi ok blk [H1 H2] HF HG Hw. split.
  - intros a Ha Hw1 Hb. rewrite <- (H1 a Ha Hw1 Hb). apply (aview_eq_of SEGS). apply HF.
    rewrite unsigned_lit_small by lia. intros Hin.
    destruct (Hw a Hin) as [Hx | [Hok Hx]]; [exact (Hw1 Hx) | exact (Hb Hok Hx)].
  - intros a Ha. eapply apresent_grows; [exact HG | exact (H2 a Ha)].
Qed.

Lemma sinv_call : forall W mem m1 m2 d n clo chi lo hi ok blk,
  sinv W mem m1 lo hi ok blk ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (clo <= a < chi) ->
     aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
  (forall a, apresent (w_H W) m1 a -> apresent (w_H W) m2 a) ->
  (forall a, d <= a < d + n -> ok = true /\ blk <= a < blk + BLK_LEN) ->
  lo <= clo -> chi <= hi ->
  sinv W mem m2 lo hi ok blk.
Proof.
  intros W mem m1 m2 d n clo chi lo hi ok blk [H1 H2] Hf Hp Hd Hlo Hhi. split.
  - intros a Ha Hw Hb. rewrite <- (H1 a Ha Hw Hb). apply Hf; [exact Ha | | lia].
    intros Hx. destruct (Hd a Hx) as [Hok Hx']. exact (Hb Hok Hx').
  - intros a Ha. exact (Hp a (H2 a Ha)).
Qed.

(* The metadata band keeps its values under the invariant: it is neither stack nor blk. *)
Lemma sinv_shadow : forall W mem memc lo hi ok blk,
  sinv W mem memc lo hi ok blk -> kHighShadowEnd <= lo -> (ok = true -> in_app blk BLK_LEN) ->
  forall s, SHADOW_OFF <= s < kHighShadowEnd -> aview SEGS (w_H W) memc s = aview SEGS (w_H W) mem s.
Proof.
  intros W mem memc lo hi ok blk [H1 _] Hlo Happ s Hs. apply H1.
  - unfold kHighShadowEnd, SHADOW_OFF in *. lia.
  - lia.
  - intros Hok Hb. specialize (Happ Hok). unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, kHighShadowEnd in *. lia.
Qed.

Lemma ra_sinv : forall W mem memc lo hi ok blk a n,
  sinv W mem memc lo hi ok blk -> kHighShadowEnd <= lo -> (ok = true -> in_app blk BLK_LEN) ->
  0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n -> range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF a n.
Proof.
  intros W mem memc lo hi ok blk a n HI Hlo Happ H0 Hn HR.
  exact (ra_kept _ _ a n (sinv_shadow W mem memc lo hi ok blk HI Hlo Happ) H0 Hn HR).
Qed.

Lemma hull_sinv : forall W mem memc lo hi ok blk a n,
  sinv W mem memc lo hi ok blk -> kHighShadowEnd <= lo -> (ok = true -> in_app blk BLK_LEN) ->
  0 <= a -> 0 < n -> a + n <= 2 ^ 47 - 64 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) a n -> shadow_hull_vis (aview SEGS (w_H W) memc) a n.
Proof.
  intros W mem memc lo hi ok blk a n HI Hlo Happ H0 Hn0 Hn HV.
  exact (hull_kept _ _ a n (sinv_shadow W mem memc lo hi ok blk HI Hlo Happ) H0 Hn0 Hn HV).
Qed.

Lemma val_mem_kept : forall (m m' : word -> option byte) H a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS H m' x = aview SEGS H m x) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
  intros m m' H a n v Hk Hv kk Hkk. rewrite <- (Hv kk Hkk). apply (mbyte_of_aview SEGS). apply Hk. lia.
Qed.

(* ------------------------------------------------------------------------------------------ *)
(* The common tail: from the return point of the last copy (0x83a84) through the inlined stamp loop
   (0x83a90..0x83ab4: count-down counter a0 = 31..1, two moving pointers s1 = a1 = blk + 2 + i, the sum in
   a2, the check of blk + 2 + i before each load), the check and store of blk[33] (0x83acc..0x83ae8),
   the epilogue and ret. The tail's own symbolic state names the entry values of ra and s0..s4 (saved
   in the frame) and the 33 bytes blk[0..33) as atoms 33..71 (atom 32 is the shadow base). *)
Definition TAIL_K : Z := AF_reac_ctrl_build_scene_step + O_COPY_RET.
Definition BX_T : sv := SOff 20 0.
Definition tail_extra (regs0 : bvmap 5 word) (sbk : list byte) : list word :=
  [Z_to_bv 64 SB; getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20]
  ++ map (fun j => Z_to_bv 64 (bu sbk j)) (seq 0 33).
Definition RSTK_T : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 48 0 0
    [YP09.mkChunk 0 (CVal 8 (SOff 38 0)); YP09.mkChunk 8 (CVal 8 (SOff 37 0)); YP09.mkChunk 16 (CVal 8 (SOff 36 0));
     YP09.mkChunk 24 (CVal 8 (SOff 35 0)); YP09.mkChunk 32 (CVal 8 (SOff 34 0)); YP09.mkChunk 40 (CVal 8 (SOff 33 0))].
Definition RBLK_T : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 34 33 34
    (map (fun j : nat => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (39 + j)%nat 0))) (seq 2 31)).
Definition ss_T : sstate :=
  mkSS TAIL_K (sr_set sr_atoms 9%bv (SOff 8 2)) [RSTK_T; RBLK_T] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, PTR 0); (20%nat, mkAF SB SB 0)] [] []).
Definition SH_T : list shent := [mkSHE 8 0 34].

Definition fsum (l : list byte) : Z :=
  bu l 2 + bu l 3 + bu l 4 + bu l 5 + bu l 6 + bu l 7 + bu l 8 + bu l 9 + bu l 10 + bu l 11 + bu l 12
  + bu l 13 + bu l 14 + bu l 15 + bu l 16 + bu l 17 + bu l 18 + bu l 19 + bu l 20 + bu l 21 + bu l 22
  + bu l 23 + bu l 24 + bu l 25 + bu l 26 + bu l 27 + bu l 28 + bu l 29 + bu l 30 + bu l 31 + bu l 32.

Lemma bu_range : forall l j, 0 <= bu l j < 256.
Proof. intros l j. unfold bu. apply byte_range. Qed.

(* The stored checksum byte is the block's last byte. *)
Lemma tail_cks : forall b st x, 8904 <= Z.of_nat (length b) -> 0 <= st <= 342 ->
  x = fsum (scene_block b st) -> ((- x) mod 2 ^ 64) mod 256 = bu (scene_block b st) 33.
Proof.
  intros b st x Hb Hst ->.
  assert (HS : fsum (scene_block b st) = byte_sum (scene_fields b st)).
  { rewrite (byte_sum_31 _ (length_scene_fields b st Hb Hst)). unfold fsum, bu.
    rewrite <- !(scene_block_field b st) by (first [exact Hb | exact Hst | lia]). reflexivity. }
  assert (HR : 0 <= fsum (scene_block b st) < 2 ^ 64).
  { unfold fsum. repeat match goal with |- context [bu ?l ?j] => lazymatch goal with _ : 0 <= bu l j < 256 |- _ => fail | _ => pose proof (bu_range l j) end end. lia. }
  rewrite (neg_low_byte _ HR). unfold bu. rewrite (scene_block_last b st Hb Hst).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite HS.
  rewrite (Z.mod_small ((256 - byte_sum (scene_fields b st) mod 256) mod 256)); [reflexivity|].
  apply Z.mod_pos_bound. lia.
Qed.

Lemma tail_extra_atom : forall regs0 sbk j, (j < 33)%nat ->
  nth (7 + j) (tail_extra regs0 sbk) (Z_to_bv 64 0) = Z_to_bv 64 (bu sbk j).
Proof.
  intros regs0 sbk j Hj. unfold tail_extra.
  do 33 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

(* Normalising an environment that the run extended or a call havocked, down to the atoms below. *)
Ltac tenv := cbn [ew ewset extK havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub length Nat.add];
  rewrite ?ew_ewset_other by lia; repeat (rewrite YN3v.ew_havoc_old; [|cbv; lia]).

(* ueval with the atom case reading through an extended environment. *)
Ltac ueval_t :=
  lazymatch goal with
  | |- U ?E (SAlu ALU_ADD ?a ?b) = _ =>
      eapply U_add_small; [ueval_t | ueval_t | lia | lia | lia]
  | |- U ?E (SAlu ALU_SUB (SLit 0) ?b) = _ => eapply U_sub0; ueval_t
  | |- U ?E (SExt false 8 ?a) = _ => eapply U_zext8; [ueval_t | lia]
  | |- U ?E (SOff ?k 0) = _ =>
      rewrite U_SOff; tenv;
      match goal with H : ew _ k = Z_to_bv 64 ?v |- _ => rewrite H end;
      rewrite Z.add_0_r, unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia
  | |- U ?E (SLit ?z) = _ => apply U_lit; lia
  end.

Lemma tail_entry : forall W (regs : bvmap 5 word) mem md (STK sp0 o : Z) FP ly S W0 mem0 md0 own lyc Sc k
    (regs0 : bvmap 5 word) (blk : Z) (sbk : list byte) cid pos,
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  spZ regs0 = sp0 + o -> o mod 16 = 0 -> o <= 0 -> SCENE_STEP_WIN - o <= STK ->
  getr regs 2 = Z_to_bv 64 (spZ regs0 - SCENE_STEP_FRAME) ->
  getr regs 8 = w64 blk -> getr regs 9 = w64 (blk + 2) -> getr regs 20 = w64 SB ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 8) 8 (bv_unsigned (getr regs0 1)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 16) 8 (bv_unsigned (getr regs0 8)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 24) 8 (bv_unsigned (getr regs0 9)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 32) 8 (bv_unsigned (getr regs0 18)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 40) 8 (bv_unsigned (getr regs0 19)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 48) 8 (bv_unsigned (getr regs0 20)) ->
  In (cid, pos) own -> 0 <= cid ->
  frame_addr lyc cid pos <= blk -> blk + BLK_LEN <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  (forall j, (j < 33)%nat -> aview SEGS (w_H W) mem (blk + Z.of_nat j) = Some (bu sbk j)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (tail_extra regs0 sbk))) ss_T
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + TAIL_K)) mem (seg_rom SEGS))).
Proof.
  intros W regs mem md STK sp0 o FP ly S W0 mem0 md0 own lyc Sc k regs0 blk sbk cid pos
    HJ Hsp Ho16 Ho0 HoS R2 R8 R9 R20 V1 V8 V9 V18 V19 V20 Hown Hcid Hflo Hfhi HBY.
  unfold BLK_LEN in Hfhi.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & HJpres & Hstk & _).
  pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
  assert (WS : SCENE_STEP_WIN = 48 + ESTACK) by reflexivity. pose proof ESTACK_nonneg as HES.
  assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  destruct (frames_bounds SEGS B LAWS lyc Sc W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
  destruct ((al_frames _ _ LAWS) lyc Sc W mem md cid pos HAR Hfin) as (Hf32 & _ & Hfpres & _).
  pose proof (fs_frame_bytes_pos cid Hcid) as Hfb.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (tail_extra regs0 sbk))).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (tail_extra regs0 sbk)) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
  assert (E20 : ew E 20 = getr regs 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 20 20%bv eq_refl)).
  assert (EXT : forall j, (j < 40)%nat -> ew E (32 + j) = nth j (tail_extra regs0 sbk) (Z_to_bv 64 0))
    by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  assert (EX : forall j, (j < 33)%nat -> ew E (39 + j) = Z_to_bv 64 (bu sbk j)).
  { intros j Hj. replace (39 + j)%nat with (32 + (7 + j))%nat by lia. rewrite EXT by lia. apply tail_extra_atom. exact Hj. }
  assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - SCENE_STEP_FRAME)
    by (rewrite E2, R2; apply unsigned_lit_small; unfold SCENE_STEP_FRAME, SCENE_STEP_WIN in *; lia).
  assert (Ublk : bv_unsigned (ew E 8) = blk) by (rewrite E8, R8; unfold w64; apply unsigned_lit_small; lia).
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
  { intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  assert (SV : forall j r, (1 <= j <= 6)%nat -> nth j (tail_extra regs0 sbk) (Z_to_bv 64 0) = getr regs0 r ->
            sv_denot E (SOff (32 + j) 0) = Z_to_bv 64 (bv_unsigned (getr regs0 r))).
  { intros j r Hj Hr. cbn [sv_denot]. rewrite EXT by lia. rewrite Hr, Z.add_0_r. reflexivity. }
  unfold ss_T. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    cbn [sv_denot]. rewrite Ublk, R9. reflexivity.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok.
    + unfold RSTK_T. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
      unfold SCENE_STEP_FRAME, SCENE_STEP_WIN in *.
      split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 0 8%N (SOff 38 0) (bv_unsigned (getr regs0 20)));
          [exact (SV 6%nat 20%bv ltac:(lia) eq_refl) | apply (bv_unsigned_in_range 64) | lia |].
        replace (spZ regs0 - 48 + 0) with (spZ regs0 - 48) by lia. exact V20.
      * apply (chunk_ok_val SEGS E _ _ 8 8%N (SOff 37 0) (bv_unsigned (getr regs0 19)));
          [exact (SV 5%nat 19%bv ltac:(lia) eq_refl) | apply (bv_unsigned_in_range 64) | lia |].
        replace (spZ regs0 - 48 + 8) with (spZ regs0 - 40) by lia. exact V19.
      * apply (chunk_ok_val SEGS E _ _ 16 8%N (SOff 36 0) (bv_unsigned (getr regs0 18)));
          [exact (SV 4%nat 18%bv ltac:(lia) eq_refl) | apply (bv_unsigned_in_range 64) | lia |].
        replace (spZ regs0 - 48 + 16) with (spZ regs0 - 32) by lia. exact V18.
      * apply (chunk_ok_val SEGS E _ _ 24 8%N (SOff 35 0) (bv_unsigned (getr regs0 9)));
          [exact (SV 3%nat 9%bv ltac:(lia) eq_refl) | apply (bv_unsigned_in_range 64) | lia |].
        replace (spZ regs0 - 48 + 24) with (spZ regs0 - 24) by lia. exact V9.
      * apply (chunk_ok_val SEGS E _ _ 32 8%N (SOff 34 0) (bv_unsigned (getr regs0 8)));
          [exact (SV 2%nat 8%bv ltac:(lia) eq_refl) | apply (bv_unsigned_in_range 64) | lia |].
        replace (spZ regs0 - 48 + 32) with (spZ regs0 - 16) by lia. exact V8.
      * apply (chunk_ok_val SEGS E _ _ 40 8%N (SOff 33 0) (bv_unsigned (getr regs0 1)));
          [exact (SV 1%nat 1%bv ltac:(lia) eq_refl) | apply (bv_unsigned_in_range 64) | lia |].
        replace (spZ regs0 - 48 + 40) with (spZ regs0 - 8) by lia. exact V1.
    + unfold RBLK_T. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Ublk.
      split; [lia|]. split; [lia|]. split.
      * intros o' Ho'. apply (apresent_writable SEGS). apply (proj1 (Hfpres (blk + o') ltac:(lia))).
      * apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
        apply (chunk_ok_val SEGS E _ _ (Z.of_nat j) 1%N (SOff (39 + j)%nat 0) (bu sbk j)).
        -- cbn [sv_denot]. rewrite (EX j ltac:(lia)), Z.add_0_r, unsigned_lit_small by (pose proof (bu_range sbk j); lia). reflexivity.
        -- pose proof (bu_range sbk j). cbn. lia.
        -- cbn. lia.
        -- exact (proj1 (val_mem1_of_aview SEGS (w_H W) mem (blk + Z.of_nat j) (bu sbk j) (HBY j ltac:(lia)))).
  - unfold RSTK_T, RBLK_T. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Ublk.
    unfold SCENE_STEP_FRAME, SCENE_STEP_WIN in *. repeat split; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, Ublk, E20, R20. unfold w64, SB. rewrite unsigned_lit_small by lia.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SCENE_STEP_FRAME, SCENE_STEP_WIN in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
    all: rewrite Hsp; apply mod16_sub48; assumption.
Qed.

Lemma okZ_true : forall blk body n st, scene_step_okZ blk body n st = true ->
  blk <> 0 /\ body <> 0 /\ n = SCENE_BYTES /\ st <= SCENE_LAST.
Proof.
  intros blk body n st H. unfold scene_step_okZ in H.
  destruct (Z.eqb_spec blk 0), (Z.eqb_spec body 0), (Z.eqb_spec n SCENE_BYTES), (Z.leb_spec st SCENE_LAST);
    cbn in H; try discriminate H; repeat split; assumption.
Qed.

Lemma okZ_false : forall blk body n st, (blk = 0 \/ body = 0 \/ n <> SCENE_BYTES \/ SCENE_LAST < st) ->
  scene_step_okZ blk body n st = false.
Proof.
  intros blk body n st H. unfold scene_step_okZ.
  destruct (Z.eqb_spec blk 0), (Z.eqb_spec body 0), (Z.eqb_spec n SCENE_BYTES), (Z.leb_spec st SCENE_LAST);
    cbn; try reflexivity; lia.
Qed.

Ltac tenv_in H := cbn [ew ewset extK havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub length Nat.add] in H;
  rewrite ?ew_ewset_other in H by lia; repeat (rewrite YN3v.ew_havoc_old in H; [|cbv; lia]).

Lemma val_mem1_aview : forall H (m : word -> option byte) a v, 0 <= v < 256 ->
  val_mem SEGS (mrestrict H m) a 1 v -> aview SEGS H m a = Some v.
Proof.
  intros H m a v Hv Hm. apply (aview_of_mbyte_lit SEGS); [|exact Hv].
  specialize (Hm 0%nat ltac:(lia)). cbn [Z.of_nat] in Hm. rewrite Z.add_0_r in Hm. rewrite Hm.
  rewrite (le_byte_1_0 v Hv). reflexivity.
Qed.

Lemma scene_tail : forall W (regs : bvmap 5 word) mem md (STK sp0 o : Z) FP ly S W0 mem0 md0 own lyc Sc k
    (regs0 : bvmap 5 word) (mem00 : word -> option byte) (blk body n st : Z) (b : list byte) cid pos,
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  spZ regs0 = sp0 + o -> o mod 16 = 0 -> o <= 0 -> SCENE_STEP_WIN - o <= STK ->
  YK0s.ret_ok (getr regs0 1) ->
  getr regs 2 = Z_to_bv 64 (spZ regs0 - SCENE_STEP_FRAME) ->
  getr regs 8 = w64 blk -> getr regs 9 = w64 (blk + 2) -> getr regs 20 = w64 SB ->
  (forall r : bv 5, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs r = getr regs0 r) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 8) 8 (bv_unsigned (getr regs0 1)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 16) 8 (bv_unsigned (getr regs0 8)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 24) 8 (bv_unsigned (getr regs0 9)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 32) 8 (bv_unsigned (getr regs0 18)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 40) 8 (bv_unsigned (getr regs0 19)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 48) 8 (bv_unsigned (getr regs0 20)) ->
  scene_step_okZ blk body n st = true -> 0 <= st -> 8904 <= Z.of_nat (length b) ->
  In (cid, pos) own -> 0 <= cid ->
  frame_addr lyc cid pos <= blk -> blk + BLK_LEN <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF blk BLK_LEN ->
  (forall j, (j < 33)%nat -> aview SEGS (w_H W) mem (blk + Z.of_nat j) = Some (bu (scene_block b st) j)) ->
  sinv W mem00 mem (spZ regs0 - SCENE_STEP_WIN) (spZ regs0) (scene_step_okZ blk body n st) blk ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + TAIL_K)) mem (seg_rom SEGS)) md)
    (treac_ctrl_build_scene_step_post regs0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem00 k blk body n st b).
Proof.
  intros W regs mem md STK sp0 o FP ly S W0 mem0 md0 own lyc Sc k regs0 mem00 blk body n st b cid pos
    HJ Hsp Ho16 Ho0 HoS Hra R2 R8 R9 R20 RK V1 V8 V9 V18 V19 V20 HOK Hst0 Hlb Hown Hcid Hflo Hfhi HRA HBY HINV.
  unfold BLK_LEN in Hfhi.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & HJpres & Hstk & _).
  pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
  assert (WS : SCENE_STEP_WIN = 48 + ESTACK) by reflexivity. pose proof ESTACK_nonneg as HES.
  assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  destruct (frames_bounds SEGS B LAWS lyc Sc W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
  pose proof (fs_frame_bytes_pos cid Hcid) as Hfb.
  destruct (okZ_true blk body n st HOK) as (_ & _ & _ & HstL). unfold SCENE_LAST in HstL.
  set (sbk := scene_block b st) in *.
  pose proof (tail_entry W regs mem md STK sp0 o FP ly S W0 mem0 md0 own lyc Sc k regs0 blk sbk cid pos
    HJ Hsp Ho16 Ho0 HoS R2 R8 R9 R20 V1 V8 V9 V18 V19 V20 Hown Hcid Hflo Hfhi HBY) as HS.
  remember (Eimg (Ereg regs (tail_extra regs0 sbk))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (tail_extra regs0 sbk)) n)
    by (intros n0 Hn0; subst E; apply Eimg_low; exact Hn0).
  assert (EXT : forall j, (j < 40)%nat -> ew E (32 + j) = nth j (tail_extra regs0 sbk) (Z_to_bv 64 0))
    by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  assert (EX : forall j, (j < 33)%nat -> ew E (39 + j) = Z_to_bv 64 (bu sbk j)).
  { intros j Hj. replace (39 + j)%nat with (32 + (7 + j))%nat by lia. rewrite EXT by lia. apply tail_extra_atom. exact Hj. }
  assert (ER : forall (r : bv 5) (nr : nat), Z.of_nat nr = bv_unsigned r -> (nr < 32)%nat -> ew E nr = getr regs r)
    by (intros r nr Hr Hn; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ nr r Hr)).
  assert (G2 : bv_unsigned (ew E 2) = spZ regs0 - SCENE_STEP_FRAME)
    by (rewrite (ER 2%bv 2%nat eq_refl ltac:(lia)), R2; apply unsigned_lit_small; unfold SCENE_STEP_FRAME, SCENE_STEP_WIN in *; lia).
  assert (Ublk : bv_unsigned (ew E 8) = blk)
    by (rewrite (ER 8%bv 8%nat eq_refl ltac:(lia)), R8; unfold w64; apply unsigned_lit_small; lia).
  assert (E20 : ew E 20 = Z_to_bv 64 SB) by (rewrite (ER 20%bv 20%nat eq_refl ltac:(lia)), R20; reflexivity).
  assert (G3 : ew E 3 = getr regs0 3) by (rewrite (ER 3%bv 3%nat eq_refl ltac:(lia)); apply RK; cbv; tauto).
  assert (G4 : ew E 4 = getr regs0 4) by (rewrite (ER 4%bv 4%nat eq_refl ltac:(lia)); apply RK; cbv; tauto).
  assert (G21 : ew E 21 = getr regs0 21) by (rewrite (ER 21%bv 21%nat eq_refl ltac:(lia)); apply RK; cbv; tauto).
  assert (G22 : ew E 22 = getr regs0 22) by (rewrite (ER 22%bv 22%nat eq_refl ltac:(lia)); apply RK; cbv; tauto).
  assert (G23 : ew E 23 = getr regs0 23) by (rewrite (ER 23%bv 23%nat eq_refl ltac:(lia)); apply RK; cbv; tauto).
  assert (G24 : ew E 24 = getr regs0 24) by (rewrite (ER 24%bv 24%nat eq_refl ltac:(lia)); apply RK; cbv; tauto).
  assert (G25 : ew E 25 = getr regs0 25) by (rewrite (ER 25%bv 25%nat eq_refl ltac:(lia)); apply RK; cbv; tauto).
  assert (G26 : ew E 26 = getr regs0 26) by (rewrite (ER 26%bv 26%nat eq_refl ltac:(lia)); apply RK; cbv; tauto).
  assert (G27 : ew E 27 = getr regs0 27) by (rewrite (ER 27%bv 27%nat eq_refl ltac:(lia)); apply RK; cbv; tauto).
  assert (G33 : ew E 33 = getr regs0 1) by (exact (EXT 1%nat ltac:(lia))).
  assert (G34 : ew E 34 = getr regs0 8) by (exact (EXT 2%nat ltac:(lia))).
  assert (G35 : ew E 35 = getr regs0 9) by (exact (EXT 3%nat ltac:(lia))).
  assert (G36 : ew E 36 = getr regs0 18) by (exact (EXT 4%nat ltac:(lia))).
  assert (G37 : ew E 37 = getr regs0 19) by (exact (EXT 5%nat ltac:(lia))).
  assert (G38 : ew E 38 = getr regs0 20) by (exact (EXT 6%nat ltac:(lia))).
  (* the 31 field bytes the loop sums, as atoms 41..71 *)
  pose proof (EX 2%nat ltac:(lia)) as X2. pose proof (EX 3%nat ltac:(lia)) as X3. pose proof (EX 4%nat ltac:(lia)) as X4.
  pose proof (EX 5%nat ltac:(lia)) as X5. pose proof (EX 6%nat ltac:(lia)) as X6. pose proof (EX 7%nat ltac:(lia)) as X7.
  pose proof (EX 8%nat ltac:(lia)) as X8. pose proof (EX 9%nat ltac:(lia)) as X9. pose proof (EX 10%nat ltac:(lia)) as X10.
  pose proof (EX 11%nat ltac:(lia)) as X11. pose proof (EX 12%nat ltac:(lia)) as X12. pose proof (EX 13%nat ltac:(lia)) as X13.
  pose proof (EX 14%nat ltac:(lia)) as X14. pose proof (EX 15%nat ltac:(lia)) as X15. pose proof (EX 16%nat ltac:(lia)) as X16.
  pose proof (EX 17%nat ltac:(lia)) as X17. pose proof (EX 18%nat ltac:(lia)) as X18. pose proof (EX 19%nat ltac:(lia)) as X19.
  pose proof (EX 20%nat ltac:(lia)) as X20. pose proof (EX 21%nat ltac:(lia)) as X21. pose proof (EX 22%nat ltac:(lia)) as X22.
  pose proof (EX 23%nat ltac:(lia)) as X23. pose proof (EX 24%nat ltac:(lia)) as X24. pose proof (EX 25%nat ltac:(lia)) as X25.
  pose proof (EX 26%nat ltac:(lia)) as X26. pose proof (EX 27%nat ltac:(lia)) as X27. pose proof (EX 28%nat ltac:(lia)) as X28.
  pose proof (EX 29%nat ltac:(lia)) as X29. pose proof (EX 30%nat ltac:(lia)) as X30. pose proof (EX 31%nat ltac:(lia)) as X31.
  pose proof (EX 32%nat ltac:(lia)) as X32.
  cbn [Nat.add] in X2, X3, X4, X5, X6, X7, X8, X9, X10, X11, X12, X13, X14, X15, X16, X17, X18, X19, X20, X21, X22,
    X23, X24, X25, X26, X27, X28, X29, X30, X31, X32.
  pose proof (bu_range sbk 2) as B2. pose proof (bu_range sbk 3) as B3. pose proof (bu_range sbk 4) as B4.
  pose proof (bu_range sbk 5) as B5. pose proof (bu_range sbk 6) as B6. pose proof (bu_range sbk 7) as B7.
  pose proof (bu_range sbk 8) as B8. pose proof (bu_range sbk 9) as B9. pose proof (bu_range sbk 10) as B10.
  pose proof (bu_range sbk 11) as B11. pose proof (bu_range sbk 12) as B12. pose proof (bu_range sbk 13) as B13.
  pose proof (bu_range sbk 14) as B14. pose proof (bu_range sbk 15) as B15. pose proof (bu_range sbk 16) as B16.
  pose proof (bu_range sbk 17) as B17. pose proof (bu_range sbk 18) as B18. pose proof (bu_range sbk 19) as B19.
  pose proof (bu_range sbk 20) as B20. pose proof (bu_range sbk 21) as B21. pose proof (bu_range sbk 22) as B22.
  pose proof (bu_range sbk 23) as B23. pose proof (bu_range sbk 24) as B24. pose proof (bu_range sbk 25) as B25.
  pose proof (bu_range sbk 26) as B26. pose proof (bu_range sbk 27) as B27. pose proof (bu_range sbk 28) as B28.
  pose proof (bu_range sbk 29) as B29. pose proof (bu_range sbk 30) as B30. pose proof (bu_range sbk 31) as B31.
  pose proof (bu_range sbk 32) as B32.
  clear HE.
  (* the metadata of blk, for the checks of blk + 27 .. blk + 33 *)
  assert (SHOK : sh_ok SEGS BX_T SH_T E (mrestrict (w_H W) mem)).
  { unfold sh_ok, SH_T. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart, BX_T. cbn [she_m she_lo she_hi].
    rewrite (U_atom E 20 SB E20) by (unfold SB; lia).
    rewrite (U_atom E 8 blk) by (first [rewrite <- Ublk; symmetry; apply Z_to_bv_bv_unsigned | lia]).
    split.
    - rewrite <- (aview_rd_of SEGS). rewrite SB_SHADOW_OFF. replace (blk + 0) with blk by lia. exact HRA.
    - intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia. }
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8%nat blk); [reflexivity | exact Ublk | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right; right; right. exists cid, pos. split; [exact Hown|].
    left. unfold in_zr. cbn [fst snd]. lia. }
  (* at the ret: the final byte, the registers, the return *)
  pose proof (sinv_run W mem00 mem _ E (ss_mem ss_T) _ _ _ _ HINV HFr HG) as HINV2.
  match type of HINV2 with ?P -> _ => assert (HWR : P) end.
  { intros a (r & Hin & Ha). cbn [ss_T ss_mem In] in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [RSTK_T RBLK_T YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia|].
    rewrite Ublk in Ha. right. split; [exact HOK | unfold BLK_LEN; lia]. }
  specialize (HINV2 HWR). clear HWR.
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) |- _ =>
    assert (KEEP : forall j, 0 <= j < 33 -> aview SEGS (w_H W) (ms_mem msc) (blk + j) = aview SEGS (w_H W) mem (blk + j));
    [ intros j Hj; apply (aview_eq_of SEGS); apply HFr; rewrite unsigned_lit_small by lia;
      intros (r & Hin & Ha); cbn [ss_T ss_mem In] in Hin;
      destruct Hin as [<- | [<- | []]]; cbn [RSTK_T RBLK_T YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia|];
      rewrite Ublk in Ha; lia
    | ];
    let rf := eval vm_compute in (nth_error (ss_mem ssx) 1) in
    lazymatch rf with Some ?RF =>
      pose proof (st_ok_pi_region_nth Ex ssx _ 1 RF HS eq_refl) as HRF;
      let c0 := eval vm_compute in (hd_error (YP09.r_chunks RF)) in
      lazymatch c0 with Some (YP09.mkChunk 33 (CVal 1 ?v)) =>
        pose proof (field_of_region_any Ex _ 8%nat blk _ _ _ _ _ 33 1%N v HRF
          ltac:(tenv; exact Ublk) ltac:(left; reflexivity) ltac:(cbn; lia)) as HV33;
        change (bv_unsigned (sv_denot Ex v)) with (U Ex v) in HV33;
        let HUv := fresh "HUv" in
        eassert (HUv : U Ex v = _) by ueval_t;
        rewrite HUv in HV33; change (2 ^ (8 * Z.of_N 1)) with 256 in HV33; cbn [ms_mem restrict] in HV33;
        rewrite (tail_cks b st) in HV33 by first [exact Hlb | lia | (unfold fsum; fold sbk; lia)]
      end
    end;
    let R1 := fresh "R1" in let R10 := fresh "R10" in
    prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros mat';
    unfold treac_ctrl_build_scene_step_post; split; [reflexivity|];
    exists (ms_regs msc), (ms_mem msc); eexists;
    split; [cbn [ms_regs]; rewrite R1; tenv; rewrite ?G33; rewrite Hra; reflexivity|];
    split; [apply (ajournal_materialize (SK := SK) SEGS B LAWS Hsegs); exact HJ|];
    split;
    [ intros r Hr; unfold acallee_saved in Hr;
      assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                       r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
      clear Hr;
      repeat (destruct Hcases as [-> | Hcases]); [ .. | subst r];
      let R := fresh "R" in
      lazymatch goal with |- getr _ (Z_to_bv 5 ?rr) = _ => prreg HS (Z_to_bv 5 rr) R end;
      rewrite R; tenv;
      first
      [ rewrite ?G3, ?G4, ?G21, ?G22, ?G23, ?G24, ?G25, ?G26, ?G27, ?G34, ?G35, ?G36, ?G37, ?G38; reflexivity
      | rewrite G2; unfold SCENE_STEP_FRAME, spZ; replace (bv_unsigned (getr regs0 2) - 48 + 48) with (bv_unsigned (getr regs0 2)) by lia;
        apply Z_to_bv_bv_unsigned ]
    |];
    split; [exact (proj1 HINV2)|];
    split; [exact (proj2 HINV2)|];
    rewrite HOK; split; [rewrite R10; reflexivity|];
    intros i Hi; unfold BLK_LEN in Hi;
    destruct (Z.eq_dec i 33) as [-> | Hne];
    [ exact (val_mem1_aview _ _ _ _ (bu_range sbk 33) HV33)
    | rewrite (KEEP i ltac:(lia)); replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia;
      rewrite (HBY (Z.to_nat i) ltac:(lia)); reflexivity ]
  end.
Qed.

(* ------------------------------------------------------------------------------------------ *)
(* The walk from the entry. Its symbolic state names the entry registers (atoms 0..31) and the
   shadow base (atom 32); the frame is the stack region below the entry sp; the GOT word and the
   cell of the shadow base are read-only regions. After the fill the region of blk (base atom 10,
   34 bytes, writable) joins, holding the fill's zeros at blk[2..34). *)
Definition BX : sv := SOff 32 0.
Definition ss_A : sstate :=
  mkSS AF_reac_ctrl_build_scene_step sr_atoms [stack_region SCENE_STEP_FRAME; got_regionP; bcell_regionP 32] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0)] [] []).
Definition E_A (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 SB]).
Definition RB0 : YP09.region := YP09.mkRegion (Some 10%nat) 0 34 0 34 [YP09.mkChunk 2 (CZero 32)].
Definition SH_B : list shent := [mkSHE 10 0 34].

Lemma sbs_entry : forall W (regs : bvmap 5 word) mem md STK sp0 o FP ly S W0 mem0 md0 own lyc Sc k,
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> SCENE_STEP_WIN - o <= STK ->
  st_ok_pi SEGS VAL (E_A regs) ss_A
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_ctrl_build_scene_step)) mem (seg_rom SEGS))).
Proof.
  intros W regs mem md STK sp0 o FP ly S W0 mem0 md0 own lyc Sc k HJ Hsp Ho16 Ho0 HoS.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & Hstk & _).
  pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : SCENE_STEP_WIN = 48 + ESTACK) by reflexivity. pose proof ESTACK_nonneg as HES.
  destruct ((al_const _ _ LAWS) lyc Sc W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_obj_img 16 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  rewrite restrict_mkst_fx.
  set (E := E_A regs).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB]) n)
    by (intros n Hn; subst E; unfold E_A; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold E_A; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Ecell : ew E (A_OBJ 16) = Z_to_bv 64 (VAL (A_OBJ 16))) by (subst E; unfold E_A; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = sp0 + o) by (rewrite E2; exact Hsp).
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
  { intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  unfold ss_A. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. unfold SCENE_STEP_FRAME, SCENE_STEP_WIN in *.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o' Ho'. apply (apresent_writable SEGS). apply HJpres. lia.
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8%N (SOff (A_OBJ 16) 0) (VAL (A_OBJ 16)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 16)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 16) (VAL (A_OBJ 16)) Ecell) by (pose proof (pa_val_range (A_OBJ 16)); lia).
      split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 16)) 0 8%N BX SB);
      [cbn [sv_denot BX]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  - apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 16) (VAL (A_OBJ 16)) Ecell) by (pose proof (pa_val_range (A_OBJ 16)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SCENE_STEP_FRAME, SCENE_STEP_WIN in *.
    revert Hslo Hshi H47 Hceil C1 C3 WS HES HSTK0 HcellR HgcD HgotR HoS Hsp Ho0. clear. intros.
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
    unfold SCENE_STEP_FRAME, SCENE_STEP_WIN in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
    all: apply mod16_add; assumption.
Qed.

(* The stores of the walk go to blk (the caller's frame, the own-frame case of awr_byte) and to the
   own stack window. *)
Ltac awr_main Usp Ublk HAWB :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | lazymatch goal with |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ ?spx _ _ _ _ _ =>
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat);
      [reflexivity | exact Usp | cbn; unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia | cbn; lia |] end
  | lazymatch goal with |- awr_ok _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
      eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat);
      [reflexivity | exact Ublk | cbn [YP09.r_wlo YP09.r_whi]; intros ? ?; apply HAWB; unfold BLK_LEN; lia |] end ].

(* The written range of a run: the own stack window, or blk. *)
Ltac wr_main Usp Ublk :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]); try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region got_regionP bcell_regionP
       ew extK havoc Nat.ltb Nat.leb Nat.eqb] in Ha;
  first
  [ lia
  | left; rewrite Usp in Ha; unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia
  | right; rewrite Ublk in Ha; split; [assumption | unfold BLK_LEN; lia] ].

Ltac sinv_after HINV HFr HG Usp Ublk :=
  let H2 := fresh "HINV" in
  pose proof (sinv_run _ _ _ _ _ _ _ _ _ _ HINV HFr HG) as H2;
  match type of H2 with ?P -> _ => let HW := fresh "HW" in assert (HW : P) by (wr_main Usp Ublk); specialize (H2 HW); clear HW end;
  clear HINV HFr HG; rename H2 into HINV.

(* A saved register in the frame region of the symbolic state. *)
Lemma slot_of_stack : forall Ex (m : word -> option byte) nb cs lo hi wlo whi off (r : bv 5) (nr : nat) (regs : bvmap 5 word) sp,
  region_ok SEGS Ex m (YP09.mkRegion (Some nb) lo hi wlo whi cs) -> bv_unsigned (ew Ex nb) = sp ->
  In (YP09.mkChunk off (CVal 8 (SOff nr 0))) cs -> ew Ex nr = getr regs r ->
  val_mem SEGS m (sp + off) 8 (bv_unsigned (getr regs r)).
Proof.
  intros Ex m nb cs lo hi wlo whi off r nr regs sp HR Hb Hin Hv.
  apply (field_of_region Ex m nb sp cs lo hi wlo whi off 8%N (SOff nr 0) (bv_unsigned (getr regs r)) HR Hb Hin).
  - cbn [sv_denot]. rewrite Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. cbn. lia.
  - cbn. lia.
Qed.

(* A region of the symbolic state, from a state at a program point (st_ok_pi) or at a call (st_ok). *)
Ltac region_of HS idx HRB :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ssx _ =>
      let rb := eval vm_compute in (nth_error (ss_mem ssx) idx) in
      lazymatch rb with Some ?RB => pose proof (st_ok_pi_region_nth Ex ssx _ idx RB HS eq_refl) as HRB end
  | st_ok _ ?Ex ?ssx _ =>
      let rb := eval vm_compute in (nth_error (ss_mem ssx) idx) in
      lazymatch rb with Some ?RB => pose proof (st_ok_region_nth Ex ssx _ idx RB HS eq_refl) as HRB end
  end.
Ltac state_ms HS :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ ?ms => ms
  | st_ok _ _ _ ?ms => ms
  end.

(* The bytes of blk the symbolic region holds as literals at a call: blk[0..N) = L. *)
Ltac pre_bytes HS idx Ublk blk L N PRE :=
  let HRB := fresh "HRB" in let HRBc := fresh "HRBc" in
  region_of HS idx HRB;
  destruct HRB as (_ & _ & _ & HRBc);
  cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict mkst ew extK havoc Nat.ltb Nat.leb Nat.eqb] in HRBc;
  rewrite Ublk in HRBc;
  let ms := state_ms HS in
  lazymatch ms with restrict ?Hh ?msx =>
    assert (PRE : forall j, (j < N)%nat -> aview SEGS Hh (ms_mem msx) (blk + Z.of_nat j) = Some (nth j L 0));
    [ let j := fresh "j" in let Hj := fresh "Hj" in
      intros j Hj;
      repeat (destruct j as [|j];
        [apply (aview_of_mbyte_lit SEGS); [eapply (chunk_lit_sound SEGS); [exact HRBc | vm_compute; reflexivity] | cbn; lia] |]);
      lia
    | clear HRBc ]
  end.

(* At a call of a wrapper: the frame's sp, the registers the tail needs, and the saves. *)
Ltac spt Rsp Usp sp0 o :=
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
    assert (SPT : spZ rg = sp0 + o - 48) by (unfold spZ; rewrite Rsp; tenv; rewrite Usp, unsigned_lit_small by lia; lia) end.

Ltac rawreg HS r R :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
      pose proof (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) as R;
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e in R;
      cbn [ms_regs restrict mkst] in R
  | st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      pose proof (st_ok_restrict_reg sg Hh Ex ssx msx r HS) as R;
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e in R;
      cbn [ms_regs restrict mkst] in R
  end.

Ltac tail_regs HS Usp E10x E32x EKx regs blk sp0 o :=
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
    let Rs := fresh "Rs" in
    assert (R2T : getr rg 2 = Z_to_bv 64 (sp0 + o - 48))
      by (prreg HS (2%bv : bv 5) Rs; rewrite Rs; tenv; rewrite Usp; f_equal; lia);
    assert (R8T : getr rg 8 = w64 blk) by (prreg HS (8%bv : bv 5) Rs; rewrite Rs; tenv; rewrite E10x; reflexivity);
    assert (R9T : getr rg 9 = w64 (blk + 2))
      by (prreg HS (9%bv : bv 5) Rs; rewrite Rs; tenv; rewrite E10x, unsigned_lit_small by lia; reflexivity);
    assert (R20T : getr rg 20 = w64 SB) by (prreg HS (20%bv : bv 5) Rs; rewrite Rs; tenv; rewrite E32x; reflexivity);
    assert (RKT : forall r : bv 5, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rg r = getr regs r)
      by (intros r Hr; cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try contradiction;
          lazymatch goal with |- getr _ ?rr = _ => prreg HS rr Rs end; rewrite Rs; tenv; (apply EKx; [reflexivity | lia]))
  end.

Ltac tail_slots HS idx Usp EKx regs sp0 o :=
  let HRS := fresh "HRS" in
  region_of HS idx HRS; cbn [ms_mem restrict mkst] in HRS;
  lazymatch type of HRS with region_ok _ ?Ex _ _ =>
      pose proof (slot_of_stack Ex _ 2%nat _ _ _ _ _ (-8) 1%bv 1%nat regs (sp0 + o) HRS ltac:(tenv; exact Usp)
        ltac:(repeat (first [left; reflexivity | right])) ltac:(tenv; apply EKx; [reflexivity | lia])) as V1;
      pose proof (slot_of_stack Ex _ 2%nat _ _ _ _ _ (-16) 8%bv 8%nat regs (sp0 + o) HRS ltac:(tenv; exact Usp)
        ltac:(repeat (first [left; reflexivity | right])) ltac:(tenv; apply EKx; [reflexivity | lia])) as V8;
      pose proof (slot_of_stack Ex _ 2%nat _ _ _ _ _ (-24) 9%bv 9%nat regs (sp0 + o) HRS ltac:(tenv; exact Usp)
        ltac:(repeat (first [left; reflexivity | right])) ltac:(tenv; apply EKx; [reflexivity | lia])) as V9;
      pose proof (slot_of_stack Ex _ 2%nat _ _ _ _ _ (-32) 18%bv 18%nat regs (sp0 + o) HRS ltac:(tenv; exact Usp)
        ltac:(repeat (first [left; reflexivity | right])) ltac:(tenv; apply EKx; [reflexivity | lia])) as V18;
      pose proof (slot_of_stack Ex _ 2%nat _ _ _ _ _ (-40) 19%bv 19%nat regs (sp0 + o) HRS ltac:(tenv; exact Usp)
        ltac:(repeat (first [left; reflexivity | right])) ltac:(tenv; apply EKx; [reflexivity | lia])) as V19;
      pose proof (slot_of_stack Ex _ 2%nat _ _ _ _ _ (-48) 20%bv 20%nat regs (sp0 + o) HRS ltac:(tenv; exact Usp)
        ltac:(repeat (first [left; reflexivity | right])) ltac:(tenv; apply EKx; [reflexivity | lia])) as V20;
      clear HRS
  end.

(* The source side of a copy from body: readable, outside the wrapper's window, usable. *)
Ltac cpy_body HJx HINV HBODY Hpq SPT body pq mq :=
  let HAR2 := fresh "HAR2" in
  pose proof HJx as (HAR2 & _);
  split; [lia|]; split; [unfold SCENE_BYTES in *; lia|]; split;
  [ intros ? ?; split;
    [ lazymatch goal with |- aview _ _ _ ?a <> None =>
        rewrite (proj1 HINV a ltac:(lia) ltac:(unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia)
          ltac:(intros _; unfold BLK_LEN in *; lia));
        replace a with (body + (a - body)) by lia; rewrite HBODY by (unfold SCENE_BYTES in *; lia); discriminate end
    | rewrite SPT; lia ]
  |]; split; [unfold BLK_LEN in *; lia|]; split;
  [ eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ pq mq); [exact HAR2 | exact Hpq | lia | unfold SCENE_BYTES in *; lia] |];
  split;
  [ eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ pq mq); [exact HAR2 | exact Hpq | lia | unfold SCENE_BYTES in *; lia]
  | intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ pq mq); [exact HAR2 | exact Hpq | lia | unfold SCENE_BYTES in *; lia | lia] ].

(* A branch condition on atoms of the entry registers, as a fact about Z. *)
Ltac cond_norm Hc E10 E11 E12 E13 :=
  first [ rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_geu_U in Hc ];
  rewrite ?U_lit in Hc by lia;
  rewrite ?(U_atom _ 10 _ E10), ?(U_atom _ 11 _ E11), ?(U_atom _ 12 _ E12), ?(U_atom _ 13 _ E13) in Hc by lia;
  first [ apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc
        | apply (proj1 (Bool.negb_true_iff _)) in Hc; first [apply Z.eqb_neq in Hc | apply Z.ltb_ge in Hc]
        | apply (proj1 (Bool.negb_false_iff _)) in Hc; first [apply Z.eqb_eq in Hc | apply Z.ltb_lt in Hc] ].

(* A refused call: run the epilogue, return with a0 = -1; only the own stack window changed. *)
Ltac refuse_fin RUN RET HS HJ SHOK HINV HOKF Hsegs E1 Hra HAE Usp Ublk HAWB :=
  paj_run_tok RUN HS HJ SHOK Bspan; [awr_main Usp Ublk HAWB |];
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HGx : mem_grows _ _ |- _ =>
    sinv_after HINV HFx HGx Usp Ublk end;
  lazymatch goal with HS : st_ok_pi _ _ ?Ex _ (restrict _ ?msc) |- _ =>
    let R1 := fresh "R1" in let R10 := fresh "R10" in
    prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
    eapply (RET _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros ?;
    unfold treac_ctrl_build_scene_step_post; split; [reflexivity|];
    exists (ms_regs msc), (ms_mem msc); eexists;
    split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
    split; [apply (ajournal_materialize (SK := SK) SEGS B LAWS Hsegs); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ Ex _ _ _ [Z_to_bv 64 SB] HS); [exact HAE | vm_compute; reflexivity]|];
    split; [exact (proj1 HINV)|];
    split; [exact (proj2 HINV)|];
    rewrite HOKF; rewrite R10; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity
  end.

(* The regions the walk keeps across a call of a wrapper: its frame (outside the wrapper's
   window), and the read-only GOT word and cell. *)
Ltac kept_srk Hfr HJ2 Usp Egot Ecell :=
  let HJp := fresh "HJp" in
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJp & _);
  cbn [ms_mem restrict];
  repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; tenv;
  rewrite ?Usp, ?Egot, ?Ecell;
  rewrite ?unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 1)); pose proof (pa_val_range (A_OBJ 16)); lia);
  intros ? ?;
  first
  [ solve [exfalso; lia]
  | apply (mbyte_of_aview SEGS); apply Hfr; unfold BLK_LEN, SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia
  | intros _; apply (apresent_writable SEGS); apply HJp; unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia ].

(* The block's bytes once a copy (d, x, n) has run: below d from the region before it, in the copy
   from the source, both read through the invariant. *)
Lemma copy_bytes : forall (W : world SEGS) (mT m2 : word -> option byte) d x n (j : Z) v,
  (forall i, 0 <= i < n -> aview SEGS (w_H W) m2 (d + i) = aview SEGS (w_H W) mT (x + i)) ->
  d <= j < d + n -> aview SEGS (w_H W) mT (x + (j - d)) = Some v ->
  aview SEGS (w_H W) m2 j = Some v.
Proof. intros W mT m2 d x n j v Heff Hj Hv. replace j with (d + (j - d)) by lia. rewrite Heff by lia. exact Hv. Qed.

Section uv. Context {E : env}.
Lemma U_mul_small : forall a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x * y < 2 ^ 64 ->
  U E (SMd M_MUL a b) = x * y.
Proof. intros a b x y Ha Hb Hx Hy Hxy. rewrite U_SMd, Ha, Hb. cbn [zmd_raw]. apply zcanon_id. unfold M64. nia. Qed.
Lemma U_addw_m1 : forall a x, U E a = x -> 1 <= x < 2 ^ 31 -> U E (SAluw ALU_ADD a (SLit (-1))) = x - 1.
Proof.
  intros a x Ha Hx. rewrite U_of_S, S_SAluw, Ha, U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). change ((2 ^ 64 - 1) mod 2 ^ 32) with (2 ^ 32 - 1).
  rewrite (Z.mod_small x (2 ^ 32)) by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ Z.of_N 64) with (2 ^ 64).
  change (2 ^ 32 / 2) with (2 ^ 31).
  replace (x + (2 ^ 32 - 1) + 2 ^ 31) with ((x - 1 + 2 ^ 31) + 1 * 2 ^ 32) by lia.
  rewrite Z_mod_plus_full, (Z.mod_small (x - 1 + 2 ^ 31)) by lia.
  replace (x - 1 + 2 ^ 31 - 2 ^ 31) with (x - 1) by lia. apply Z.mod_small. lia.
Qed.
End uv.

(* The value of an address term the code builds from the entry registers. *)
Ltac uval_gen :=
  lazymatch goal with
  | |- U ?E (SAlu ALU_ADD ?a ?b) = _ => eapply U_add_small; [uval_gen | uval_gen | lia | lia | lia]
  | |- U ?E (SMd M_MUL ?a ?b) = _ => eapply U_mul_small; [uval_gen | uval_gen | lia | lia | lia]
  | |- U ?E (SAluw ALU_ADD ?a (SLit (-1))) = _ => eapply U_addw_m1; [uval_gen | lia]
  | |- U ?E (SExt false 8 ?a) = _ => eapply U_zext8; [uval_gen | lia]
  | |- U ?E (SOff ?k ?c) = _ =>
      rewrite U_SOff; tenv;
      match goal with H : ew _ k = Z_to_bv 64 ?v |- _ => rewrite H end;
      rewrite unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia
  | |- U ?E (SLit ?z) = _ => apply U_lit; lia
  end.

Ltac addr_val R :=
  rewrite R, denot_lit_U; unfold w64; f_equal;
  lazymatch goal with |- U ?Ex ?e = _ => let Hu := fresh "Hu" in eassert (Hu : U Ex e = _) by uval_gen; rewrite Hu; lia end.

(* acallee_saved of a register literal. *)
Ltac acs_lit := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

(* From the return point of the last copy to the tail: the frame's saves and the callee-saved
   registers come through the copy, which writes only blk and its own window. *)
Lemma tail_from_call : forall W (rgT regs3 : bvmap 5 word) (mm mem3 : word -> option byte) md3
    (STK sp0 o : Z) FP ly S W0 mem0 md0 own lyc Sc k (regs : bvmap 5 word) (mem : word -> option byte)
    (blk body n st : Z) (b : list byte) cid pos d nn,
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem3 md3 k ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> SCENE_STEP_WIN - o <= STK -> YK0s.ret_ok (getr regs 1) ->
  getr rgT 2 = Z_to_bv 64 (sp0 + o - 48) -> getr rgT 8 = w64 blk -> getr rgT 9 = w64 (blk + 2) -> getr rgT 20 = w64 SB ->
  (forall r : bv 5, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rgT r = getr regs r) ->
  aregs_preserved rgT regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + nn) -> ~ (sp0 + (o - 48) - ESTACK <= a < sp0 + (o - 48)) ->
     aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mm a) ->
  blk <= d -> d + nn <= blk + BLK_LEN ->
  val_mem SEGS (mrestrict (w_H W) mm) (sp0 + o + -8) 8 (bv_unsigned (getr regs 1)) ->
  val_mem SEGS (mrestrict (w_H W) mm) (sp0 + o + -16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem SEGS (mrestrict (w_H W) mm) (sp0 + o + -24) 8 (bv_unsigned (getr regs 9)) ->
  val_mem SEGS (mrestrict (w_H W) mm) (sp0 + o + -32) 8 (bv_unsigned (getr regs 18)) ->
  val_mem SEGS (mrestrict (w_H W) mm) (sp0 + o + -40) 8 (bv_unsigned (getr regs 19)) ->
  val_mem SEGS (mrestrict (w_H W) mm) (sp0 + o + -48) 8 (bv_unsigned (getr regs 20)) ->
  scene_step_okZ blk body n st = true -> 0 <= st -> 8904 <= Z.of_nat (length b) ->
  In (cid, pos) own -> 0 <= cid ->
  frame_addr lyc cid pos <= blk -> blk + BLK_LEN <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  range_addressable (aview SEGS (w_H W) mem3) SHADOW_OFF blk BLK_LEN ->
  (forall j, (j < 33)%nat -> aview SEGS (w_H W) mem3 (blk + Z.of_nat j) = Some (bu (scene_block b st) j)) ->
  sinv W mem mem3 (spZ regs - SCENE_STEP_WIN) (spZ regs) (scene_step_okZ blk body n st) blk ->
  SRr SEGS W (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + TAIL_K)) mem3 (seg_rom SEGS)) md3)
    (treac_ctrl_build_scene_step_post regs STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem k blk body n st b).
Proof.
  intros W rgT regs3 mm mem3 md3 STK sp0 o FP ly S W0 mem0 md0 own lyc Sc k regs mem blk body n st b cid pos d nn
    HJ Hsp Ho16 Ho0 HoS Hra R2 R8 R9 R20 RK HP Hfr Hd1 Hd2 V1 V8 V9 V18 V19 V20 HOK Hst0 Hlb Hown Hcid Hflo Hfhi HRA HBY HINV.
  unfold BLK_LEN in Hfhi, Hd2. pose proof ESTACK_nonneg as HES.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
  assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  destruct (frames_bounds SEGS B LAWS lyc Sc W mem3 md3 cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
  assert (KEEPS : forall x, sp0 + o - 48 <= x < sp0 + o -> aview SEGS (w_H W) mem3 x = aview SEGS (w_H W) mm x).
  { intros x Hx. unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in HoS.
    apply Hfr.
    - lia.
    - intros Hxd. lia.
    - intros Hxe. lia. }
  assert (CSb : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr rgT r).
  { intros r Hr. rewrite <- (Z_to_bv_bv_unsigned _ r). exact (HP _ Hr). }
  apply (scene_tail W regs3 mem3 md3 STK sp0 o FP ly S W0 mem0 md0 own lyc Sc k regs mem blk body n st b cid pos
           HJ Hsp Ho16 Ho0 HoS Hra).
  - rewrite (CSb 2%bv) by acs_lit. rewrite R2.
    unfold SCENE_STEP_FRAME. rewrite Hsp. f_equal; lia.
  - rewrite (CSb 8%bv) by acs_lit. exact R8.
  - rewrite (CSb 9%bv) by acs_lit. exact R9.
  - rewrite (CSb 20%bv) by acs_lit. exact R20.
  - intros r Hr. rewrite <- (RK r Hr). apply CSb.
    cbn [In] in Hr. repeat destruct Hr as [<- | Hr]; try contradiction; acs_lit.
  - rewrite Hsp. replace (sp0 + o - 8) with (sp0 + o + -8) by lia. apply (val_mem_kept mm); [|exact V1]. intros x Hx. apply KEEPS. lia.
  - rewrite Hsp. replace (sp0 + o - 16) with (sp0 + o + -16) by lia. apply (val_mem_kept mm); [|exact V8]. intros x Hx. apply KEEPS. lia.
  - rewrite Hsp. replace (sp0 + o - 24) with (sp0 + o + -24) by lia. apply (val_mem_kept mm); [|exact V9]. intros x Hx. apply KEEPS. lia.
  - rewrite Hsp. replace (sp0 + o - 32) with (sp0 + o + -32) by lia. apply (val_mem_kept mm); [|exact V18]. intros x Hx. apply KEEPS. lia.
  - rewrite Hsp. replace (sp0 + o - 40) with (sp0 + o + -40) by lia. apply (val_mem_kept mm); [|exact V19]. intros x Hx. apply KEEPS. lia.
  - rewrite Hsp. replace (sp0 + o - 48) with (sp0 + o + -48) by lia. apply (val_mem_kept mm); [|exact V20]. intros x Hx. apply KEEPS. lia.
  - exact HOK.
  - exact Hst0.
  - exact Hlb.
  - exact Hown.
  - exact Hcid.
  - exact Hflo.
  - exact Hfhi.
  - exact HRA.
  - exact HBY.
  - exact HINV.
Qed.

Theorem pb_reac_ctrl_build_scene_step : treac_ctrl_build_scene_step_spec.
Proof.
unfold treac_ctrl_build_scene_step_spec.
intros W regs mem md STK sp0 o FP ly S W0 mem0 md0 own lyc Sc k blk body n st b
  HJ Hsp Ho16 Ho0 HoS Hgp Htp Hra H10 H11 H12 H13 Rblk Rbody Rn Rst HOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & HJpres & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
assert (WS : SCENE_STEP_WIN = 48 + ESTACK) by reflexivity. pose proof ESTACK_nonneg as HES.
assert (HBL : BLK_LEN = 34) by reflexivity. assert (HSB : SCENE_BYTES = 8904) by reflexivity.
assert (HTL : TT_LEN = 12) by reflexivity. assert (HSF : SCENE_STEP_FRAME = 48) by reflexivity.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR. pose proof (pa_obj_img 16 ltac:(lia)) as HcellR.
pose proof (pa_obj_img OBJ_TT ltac:(unfold OBJ_TT; lia)) as HTTimg. change (VAL (A_OBJ OBJ_TT)) with A_TT in HTTimg.
pose proof (sbs_entry W regs mem md STK sp0 o FP ly S W0 mem0 md0 own lyc Sc k HJ Hsp Ho16 Ho0 HoS) as HS.
remember (E_A regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n0, (n0 < A_TEXT)%nat -> ew E n0 = ew (Ereg regs [Z_to_bv 64 SB]) n0)
  by (intros n0 Hn0; subst E; apply Eimg_low; exact Hn0).
assert (ER : forall (r : bv 5) (nr : nat), Z.of_nat nr = bv_unsigned r -> (nr < 32)%nat -> ew E nr = getr regs r)
  by (intros r nr Hr Hn; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ nr r Hr)).
assert (E1 : ew E 1 = getr regs 1) by exact (ER 1%bv 1%nat eq_refl ltac:(lia)).
assert (E3 : ew E 3 = getr regs 3) by exact (ER 3%bv 3%nat eq_refl ltac:(lia)).
assert (E4 : ew E 4 = getr regs 4) by exact (ER 4%bv 4%nat eq_refl ltac:(lia)).
assert (E10 : ew E 10 = Z_to_bv 64 blk) by (rewrite (ER 10%bv 10%nat eq_refl ltac:(lia)); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 body) by (rewrite (ER 11%bv 11%nat eq_refl ltac:(lia)); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 n) by (rewrite (ER 12%bv 12%nat eq_refl ltac:(lia)); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 st) by (rewrite (ER 13%bv 13%nat eq_refl ltac:(lia)); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 16) = Z_to_bv 64 (VAL (A_OBJ 16))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EgotU : bv_unsigned (ew E 242%nat) = VAL (A_OBJ 1))
  by (change 242%nat with (A_OBJ 1); rewrite Egot; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia).
assert (EcellU : bv_unsigned (ew E 257%nat) = VAL (A_OBJ 16))
  by (change 257%nat with (A_OBJ 16); rewrite Ecell; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 16)); lia).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) E)
  by (split; [intros n0 Hn0; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = sp0 + o) by (rewrite (ER 2%bv 2%nat eq_refl ltac:(lia)); exact Hsp).
clear HE.
assert (SHOK : sh_ok SEGS BX [] E (mrestrict (w_H W) mem)) by constructor.
pose proof (sinv_refl W mem (spZ regs - SCENE_STEP_WIN) (spZ regs) (scene_step_okZ blk body n st) blk) as HINV.
unfold cfg_at, A_reac_ctrl_build_scene_stepP.
change (w64 (BASE + AF_reac_ctrl_build_scene_step)) with (Z_to_bv 64 (BASE + AF_reac_ctrl_build_scene_step)).
(* 0x83834..0x83858: the frame, the saves, a0 = -1, beqz s0 *)
paj_run_tok RUN HS HJ SHOK Bspan; [awr_main Usp Usp Usp |].
sinv_after HINV HFr HG Usp Usp.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* blk = 0: refused *)
  cond_norm Hc E10 E11 E12 E13.
  assert (HOKF : scene_step_okZ blk body n st = false) by (apply okZ_false; left; exact Hc).
  refuse_fin RUN RET HS HJ SHOK HINV HOKF Hsegs E1 Hra HAE Usp Usp Usp. }
cond_norm Hc E10 E11 E12 E13. rename Hc into Hblk0.
(* 0x8385c..0x83860: mv s2,a1; beqz a1 *)
paj_run_tok RUN HS HJ SHOK Bspan; [awr_main Usp Usp Usp |].
sinv_after HINV HFr HG Usp Usp.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ cond_norm Hc E10 E11 E12 E13.
  assert (HOKF : scene_step_okZ blk body n st = false) by (apply okZ_false; right; left; exact Hc).
  refuse_fin RUN RET HS HJ SHOK HINV HOKF Hsegs E1 Hra HAE Usp Usp Usp. }
cond_norm Hc E10 E11 E12 E13. rename Hc into Hbody0.
(* 0x83864..0x8386c: a1 = 8904; bne a2,a1 *)
paj_run_tok RUN HS HJ SHOK Bspan; [awr_main Usp Usp Usp |].
sinv_after HINV HFr HG Usp Usp.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ cond_norm Hc E10 E11 E12 E13.
  assert (HOKF : scene_step_okZ blk body n st = false) by (apply okZ_false; right; right; left; unfold SCENE_BYTES; lia).
  refuse_fin RUN RET HS HJ SHOK HINV HOKF Hsegs E1 Hra HAE Usp Usp Usp. }
cond_norm Hc E10 E11 E12 E13. rename Hc into Hn8904.
(* 0x83870..0x83878: mv s3,a3; a1 = 342; bltu a1,a3 *)
paj_run_tok RUN HS HJ SHOK Bspan; [awr_main Usp Usp Usp |].
sinv_after HINV HFr HG Usp Usp.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ cond_norm Hc E10 E11 E12 E13.
  assert (HOKF : scene_step_okZ blk body n st = false) by (apply okZ_false; right; right; right; unfold SCENE_LAST; lia).
  refuse_fin RUN RET HS HJ SHOK HINV HOKF Hsegs E1 Hra HAE Usp Usp Usp. }
cond_norm Hc E10 E11 E12 E13. rename Hc into Hst342.
(* ---- the accepting path ---- *)
assert (HOKT : scene_step_okZ blk body n st = true).
{ unfold scene_step_okZ, SCENE_BYTES, SCENE_LAST.
  destruct (Z.eqb_spec blk 0), (Z.eqb_spec body 0), (Z.eqb_spec n 8904), (Z.leb_spec st 342); cbn; first [reflexivity | lia]. }
destruct (HOK HOKT) as ((cid & pos & Hown & Hcid & Hflo & Hfhi) & Hbpres & HRAb & HHVb &
  (pq & mq & Hpq & Hpqlo & Hpqhi) & Hlb & HBODY & HTT & HRAtt & HHVtt & HTTd).
clear HOK.
unfold BLK_LEN in Hfhi. unfold SCENE_BYTES in Hpqhi. unfold TT_LEN, BLK_LEN in HTTd.
assert (Hlb' : 8904 <= Z.of_nat (length b)) by (rewrite Hlb; unfold SCENE_BYTES; lia).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
pose proof (fs_frame_bytes_pos cid Hcid) as Hfb.
pose proof (frm_off_imgP B lyc Sc W mem md cid pos HAR Hfin) as Hfimg. unfold off_img in Hfimg.
assert (Happ : in_app blk BLK_LEN) by (eapply in_app_sub; [exact Hfapp | lia | unfold BLK_LEN; lia | unfold BLK_LEN; lia]).
assert (HappF : scene_step_okZ blk body n st = true -> in_app blk BLK_LEN) by (intros _; exact Happ).
destruct ((al_blocks _ _ LAWS) lyc Sc W mem md pq mq HAR Hpq) as (Hq16 & Hq4096 & Hqceil & Hqapp & Hqpres & _ & Hqmax).
pose proof (sep_block_frame SEGS B LAWS lyc Sc W mem md pq mq cid pos HAR Hpq Hfin) as Hsepbf.
unfold zdisjoint in Hsepbf. cbn [fst snd] in Hsepbf.
pose proof (req_size_pos mq ltac:(lia)) as Hrq.
assert (HAWB : forall a, blk <= a < blk + BLK_LEN -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a).
{ intros a Ha. right; right; right. exists cid, pos. split; [exact Hown|]. left. unfold in_zr. cbn [fst snd]. unfold BLK_LEN in *. lia. }
assert (HLO : kHighShadowEnd <= spZ regs - SCENE_STEP_WIN)
  by (unfold kHighShadowEnd, SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia).
assert (Ublk : bv_unsigned (ew E 10) = blk) by (rewrite E10; apply unsigned_lit_small; lia).
(* 0x8387c..0x83898: s4 = the shadow base (GOT word 0x9b710 -> cell 0xa37f8), s1 = blk + 2, the fill's arguments *)
paj_run_tok RUN HS HJ SHOK Bspan; [awr_main Usp Ublk HAWB |].
sinv_after HINV HFr HG Usp Ublk.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply SRr_bind;
[ eapply (aj_intrin_at (SK := SK) SEGS B LAWS Hsegs OSet (SIGMA SS___asan_memset) AMEMSET W rg mm
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (blk + 2) 0 32 (o - 48) _ HJ);
  [ rewrite Ra0; tenv; rewrite E10, unsigned_lit_small by lia; reflexivity
  | rewrite Ra1; reflexivity
  | rewrite Ra2; reflexivity
  | lia
  | lia
  | unfold BLK_LEN in *; lia
  | unfold spZ at 1; rewrite Rsp; tenv; rewrite Usp, unsigned_lit_small by lia; lia
  | apply mod16_m48; exact Ho16
  | lia
  | unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia
  | rewrite Rgp; tenv; rewrite E3; exact Hgp
  | rewrite Rtp; tenv; rewrite E4; exact Htp
  | exact Rra
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros a Ha; split; [apply HAWB; unfold BLK_LEN; lia | unfold BLK_LEN in *; lia]
  | eapply amem_range_sub_app; [exact Hfapp | exact Hfceil | lia | lia | lia]
  | apply (range_addressable_sub _ _ blk BLK_LEN); [| lia | unfold BLK_LEN; lia];
    exact (ra_sinv _ _ _ _ _ _ _ blk BLK_LEN HINV HLO HappF ltac:(lia) ltac:(unfold BLK_LEN; lia) HRAb)
  | intros _; apply (hull_sub _ blk BLK_LEN); [| lia | lia | unfold BLK_LEN; lia | lia];
    exact (hull_sinv _ _ _ _ _ _ _ blk BLK_LEN HINV HLO HappF ltac:(lia) ltac:(unfold BLK_LEN; lia) ltac:(unfold BLK_LEN; lia) HHVb)
  | exact I ]
| ]
end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff2 & Hfr2 & Hpres2).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
lazymatch type of Hfr2 with forall a, _ -> _ -> _ -> aview _ _ _ a = aview _ _ ?mT a =>
  pose proof (sinv_call _ _ _ _ _ _ _ _ _ _ _ blk HINV Hfr2 Hpres2
    ltac:(intros a Ha; split; [exact HOKT | unfold BLK_LEN; lia]) ltac:(unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia)
    ltac:(lia)) as HINV2 end.
clear HINV; rename HINV2 into HINV.
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ kept_srk Hfr2 HJ2 Usp EgotU EcellU. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 33 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall k0, (k0 < 33)%nat -> ew E' k0 = ew E k0) by (intros k0 Hk0; rewrite HE'; apply YN3v.ew_havoc_old; exact Hk0).
assert (Egot' : ew E' (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (rewrite HE', ew_havoc_above by (cbn; unfold A_OBJ, A_TEXT; lia); exact Egot).
assert (Ecell' : ew E' (A_OBJ 16) = Z_to_bv 64 (VAL (A_OBJ 16))) by (rewrite HE', ew_havoc_above by (cbn; unfold A_OBJ, A_TEXT; lia); exact Ecell).
assert (EgotU' : bv_unsigned (ew E' 242%nat) = VAL (A_OBJ 1))
  by (change 242%nat with (A_OBJ 1); rewrite Egot'; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia).
assert (EcellU' : bv_unsigned (ew E' 257%nat) = VAL (A_OBJ 16))
  by (change 257%nat with (A_OBJ 16); rewrite Ecell'; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 16)); lia).
clear HE'.
assert (Usp' : bv_unsigned (ew E' 2) = sp0 + o) by (rewrite OLD by lia; exact Usp).
assert (E'3 : ew E' 3 = getr regs 3) by (rewrite OLD by lia; exact E3).
assert (E'4 : ew E' 4 = getr regs 4) by (rewrite OLD by lia; exact E4).
assert (E'10 : ew E' 10 = Z_to_bv 64 blk) by (rewrite OLD by lia; exact E10).
assert (E'11 : ew E' 11 = Z_to_bv 64 body) by (rewrite OLD by lia; exact E11).
assert (E'12 : ew E' 12 = Z_to_bv 64 n) by (rewrite OLD by lia; exact E12).
assert (E'13 : ew E' 13 = Z_to_bv 64 st) by (rewrite OLD by lia; exact E13).
assert (E'32 : ew E' 32 = Z_to_bv 64 SB) by (rewrite OLD by lia; exact E32).
assert (EK' : forall (r : bv 5) (nr : nat), Z.of_nat nr = bv_unsigned r -> (nr < 32)%nat -> ew E' nr = getr regs r)
  by (intros r nr Hr1 Hr2; rewrite OLD by lia; exact (ER r nr Hr1 Hr2)).
assert (Ublk' : bv_unsigned (ew E' 10) = blk) by (rewrite E'10; apply unsigned_lit_small; lia).
(* blk's region joins: blk[2..34) = 0 from the fill; and the fact blk is a heap-range pointer *)
assert (F10 : afact_ok E' 10 (PTR 0)).
{ unfold afact_ok, PTR. cbn [af_lo af_hi af_al2]. rewrite Ublk', Z.pow_0_r, Z.mod_1_r.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, BLK_LEN in *. repeat split; lia. }
apply (st_ok_pi_add_fact E' _ _ 10 _ HS) in F10. clear HS. rename F10 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict ?Hh ?msx) =>
  assert (HR : region_ok SEGS E' (ms_mem (restrict Hh msx)) RB0);
  [ cbn [restrict ms_mem]; unfold RB0, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite Ublk';
    split; [lia|]; split; [lia|]; split;
    [ intros o' Ho'; apply (apresent_writable SEGS);
      pose proof HJ2 as (HAR2 & _ & _ & _ & _ & Hfrs2 & _);
      destruct ((al_frames _ _ LAWS) lyc Sc W mem2 md2 cid pos HAR2 Hfin) as (_ & _ & Hfp2 & _);
      apply (proj1 (Hfp2 (blk + o') ltac:(lia)))
    | apply Forall_cons; [|apply Forall_nil];
      intros i Hi; cbn [YP09.c_len YP09.cv_len YP09.c_val YP09.c_off YP09.cbyte] in Hi |- *;
      exists (Z_to_bv 8 0); split; [reflexivity|];
      pose proof (Heff2 i Hi) as Hz; rewrite Z.mod_0_l in Hz by lia;
      exact (mbyte_of_aview_some SEGS _ _ _ _ Hz) ]
  | pose proof (st_ok_pi_add_region E' ssx (restrict Hh msx) RB0 HS ltac:(vm_compute; reflexivity) HR) as HS2;
    match type of HS2 with ?tq -> _ => assert (HD : tq); [|specialize (HS2 HD); clear HD] end;
    [ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint, RB0;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite ?Ublk', ?Usp', ?EgotU', ?EcellU', ?Egot', ?Ecell';
      rewrite ?unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 1)); pose proof (pa_val_range (A_OBJ 16)); lia);
      unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, BLK_LEN in *;
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia]
    | clear HS HR; rename HS2 into HS ] ]
end.
assert (SHOK2 : sh_ok SEGS BX SH_B E' (mrestrict (w_H W) mem2)).
{ unfold sh_ok, SH_B. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart, BX. cbn [she_m she_lo she_hi].
  rewrite (U_atom E' 32 SB E'32) by (unfold SB; lia). rewrite (U_atom E' 10 blk E'10) by lia.
  split.
  - rewrite <- (aview_rd_of SEGS). rewrite SB_SHADOW_OFF. replace (blk + 0) with blk by lia.
    exact (ra_sinv _ _ _ _ _ _ _ blk BLK_LEN HINV HLO HappF ltac:(lia) ltac:(unfold BLK_LEN; lia) HRAb).
  - intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB, BLK_LEN in *. lia. }
clear SHOK. rename SHOK2 into SHOK.
(* 0x8389c..0x838d4: the checks and stores of blk[0] = 0xcd, blk[1] = 0xea; beq s3,342 *)
paj_run_tok RUN HS HJ2 SHOK Bspan; [awr_main Usp' Ublk' HAWB |].
sinv_after HINV HFr HG Usp' Ublk'.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* ---- LAST: step = 342 ---- *)
  cond_norm Hc E'10 E'11 E'12 E'13. subst st.
  (* 0x83988..0x83a08: blk[2..6) = 1, 2, 0, 14; the copy of body[8890..8904) to blk + 7 *)
  paj_run_tok RUN HS HJ2 SHOK Bspan; [awr_main Usp' Ublk' HAWB |].
  sinv_after HINV HFr HG Usp' Ublk'.
  pmkst HS.
  (* blk[0..7) before the copy *)
  pre_bytes HS 0%nat Ublk' blk [205; 234; 1; 2; 0; 14; 0] 7%nat PRE.
  prreg HS (10%bv : bv 5) Ra0. rawreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
  prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
  spt Rsp Usp' sp0 o.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  eapply SRr_bind;
  [ eapply (aj_intrin_at (SK := SK) SEGS B LAWS Hsegs OCpy (SIGMA SS___asan_memcpy) AMEMCPY W rg mm
      STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (blk + 7) (body + 8890) 14 (o - 48) _ HJ2);
    [ rewrite Ra0; tenv; rewrite E'10, unsigned_lit_small by lia; reflexivity
    | addr_val Ra1
    | rewrite Ra2; reflexivity
    | lia | lia | unfold BLK_LEN in *; lia
    | rewrite SPT; lia
    | apply mod16_m48; exact Ho16
    | lia
    | unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia
    | rewrite Rgp; tenv; rewrite E'3; exact Hgp
    | rewrite Rtp; tenv; rewrite E'4; exact Htp
    | exact Rra
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | intros a Ha; split; [apply HAWB; unfold BLK_LEN; lia | unfold BLK_LEN in *; lia]
    | eapply amem_range_sub_app; [exact Hfapp | exact Hfceil | lia | lia | lia]
    | apply (range_addressable_sub _ _ blk BLK_LEN); [| lia | unfold BLK_LEN; lia];
      exact (ra_sinv _ _ _ _ _ _ _ blk BLK_LEN HINV HLO HappF ltac:(lia) ltac:(unfold BLK_LEN; lia) HRAb)
    | intros _; apply (hull_sub _ blk BLK_LEN); [| lia | lia | unfold BLK_LEN; lia | lia];
      exact (hull_sinv _ _ _ _ _ _ _ blk BLK_LEN HINV HLO HappF ltac:(lia) ltac:(unfold BLK_LEN; lia) ltac:(unfold BLK_LEN; lia) HHVb)
    | cpy_body HJ2 HINV HBODY Hpq SPT body pq mq ]
  | ]
  end.
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3).
  clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp SPT.
  (* blk[0..7) and blk[7..21) after the first copy *)
  assert (B1 : forall j, (j < 21)%nat -> aview SEGS (w_H W) mem3 (blk + Z.of_nat j) = Some (bu (scene_block b 342) j)).
  { intros j Hj. rewrite (sb_last b j Hlb' ltac:(lia)).
    destruct (Nat.ltb_spec j 7) as [Hj7 | Hj7].
    - rewrite Hfr3 by (unfold BLK_LEN in *; lia). exact (PRE j Hj7).
    - destruct (Nat.ltb_spec j 21) as [_ | ?]; [|lia].
      eapply copy_bytes; [exact Heff3 | lia |].
      rewrite (proj1 HINV);
        [| lia | unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia | intros _; unfold BLK_LEN in *; lia].
      replace (body + 8890 + (blk + Z.of_nat j - (blk + 7))) with (body + Z.of_nat (Z.to_nat 8890 + (j - 7))) by lia.
      rewrite HBODY by (unfold SCENE_BYTES in *; lia). unfold bu. rewrite Nat2Z.id. reflexivity. }
  lazymatch type of Hfr3 with forall a, _ -> _ -> _ -> aview _ _ _ a = aview _ _ ?mT a =>
    pose proof (sinv_call _ _ _ _ _ _ _ _ _ _ _ blk HINV Hfr3 Hpres3
      ltac:(intros a Ha; split; [exact HOKT | unfold BLK_LEN; lia]) ltac:(unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia)
      ltac:(lia)) as HINV3 end.
  clear HINV; rename HINV3 into HINV.
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
    let KK := eval vm_compute in (run_K A_LIM BX SH_B ssx) in
    jafter_call_keep_hi HS KK regs3 (mrestrict (w_H W) mem3) HP3 [1; 2; 3]%nat HS2 end.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { kept_srk Hfr3 HJ3 Usp' EgotU' EcellU'. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ (havoc E' ?KK _) _ _ =>
    remember (havoc E' KK (map (getr regs3) CLOB)) as E'' eqn:HE'' in HS;
    assert (HEI'' : img_env VAL A_LIM E'') by (rewrite HE''; apply img_env_havoc_hi; [exact HEI' | cbv; lia]);
    assert (OLD' : forall k0, (k0 < 33)%nat -> ew E'' k0 = ew E' k0)
      by (intros k0 Hk0; rewrite HE''; apply YN3v.ew_havoc_old; lia);
    assert (Egot'' : ew E'' (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
      by (rewrite HE'', YN3v.ew_havoc_old by (unfold A_OBJ, A_TEXT; lia); exact Egot');
    assert (Ecell'' : ew E'' (A_OBJ 16) = Z_to_bv 64 (VAL (A_OBJ 16)))
      by (rewrite HE'', YN3v.ew_havoc_old by (unfold A_OBJ, A_TEXT; lia); exact Ecell')
  end.
  assert (Ett : ew E'' (A_OBJ OBJ_TT) = Z_to_bv 64 A_TT) by (apply img_env_atomP; [exact HEI'' | unfold A_OBJ, OBJ_TT, A_TEXT, A_LIM; lia]).
  clear HE''.
  assert (Usp'' : bv_unsigned (ew E'' 2) = sp0 + o) by (rewrite OLD' by lia; exact Usp').
  assert (E''3 : ew E'' 3 = getr regs 3) by (rewrite OLD' by lia; exact E'3).
  assert (E''4 : ew E'' 4 = getr regs 4) by (rewrite OLD' by lia; exact E'4).
  assert (E''10 : ew E'' 10 = Z_to_bv 64 blk) by (rewrite OLD' by lia; exact E'10).
  assert (Ublk'' : bv_unsigned (ew E'' 10) = blk) by (rewrite E''10; apply unsigned_lit_small; lia).
  assert (E''32 : ew E'' 32 = Z_to_bv 64 SB) by (rewrite OLD' by lia; exact E'32).
  assert (EK'' : forall (r : bv 5) (nr : nat), Z.of_nat nr = bv_unsigned r -> (nr < 32)%nat -> ew E'' nr = getr regs r)
    by (intros r nr Hr1 Hr2; rewrite OLD' by lia; exact (EK' r nr Hr1 Hr2)).
  assert (SHOK3 : sh_ok SEGS BX [] E'' (mrestrict (w_H W) mem3)) by constructor.
  clear SHOK. rename SHOK3 into SHOK.
  (* 0x83a0c..0x83a80: the copy of TAIL_TRAILER to blk + 21 *)
  paj_run_tok RUN HS HJ3 SHOK Bspan; [awr_main Usp'' Ublk'' HAWB |].
  (* blk[0..21) through the run, which writes only the frame *)
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    assert (B2 : forall j, (j < 21)%nat -> aview SEGS (w_H W) (ms_mem msx) (blk + Z.of_nat j) = Some (bu (scene_block b 342) j));
    [ intros j Hj; rewrite <- (B1 j Hj); apply (aview_eq_of SEGS); apply HFr; rewrite unsigned_lit_small by lia;
      intros (r & Hin & Ha); vm_compute in Hin; repeat (destruct Hin as [<- | Hin]); try contradiction;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew extK havoc Nat.ltb Nat.leb Nat.eqb] in Ha; rewrite ?Usp'' in Ha;
      unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, BLK_LEN in *; lia
    | ] end.
  sinv_after HINV HFr HG Usp'' Ublk''.
  pmkst HS.
  prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
  prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
  spt Rsp Usp'' sp0 o.
  tail_regs HS Usp'' E''10 E''32 EK'' regs blk sp0 o.
  tail_slots HS 0%nat Usp'' EK'' regs sp0 o.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ => set (rgT := rg) in *; set (mmT := mm) in * end.
  eapply SRr_bind;
  [ eapply (aj_intrin_at (SK := SK) SEGS B LAWS Hsegs OCpy (SIGMA SS___asan_memcpy) AMEMCPY W rgT mmT
      STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (blk + 21) A_TT 12 (o - 48) _ HJ3);
    [ rewrite Ra0; tenv; rewrite E''10, unsigned_lit_small by lia; reflexivity
    | rewrite Ra1; tenv; first [rewrite Ett | change (ew E'' 253%nat) with (ew E'' (A_OBJ OBJ_TT)); rewrite Ett]; reflexivity
    | rewrite Ra2; reflexivity
    | lia | lia | unfold BLK_LEN in *; lia
    | rewrite SPT; lia
    | apply mod16_m48; exact Ho16
    | lia
    | unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia
    | rewrite Rgp; tenv; rewrite E''3; exact Hgp
    | rewrite Rtp; tenv; rewrite E''4; exact Htp
    | exact Rra
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | intros a Ha; split; [apply HAWB; unfold BLK_LEN; lia | unfold BLK_LEN in *; lia]
    | eapply amem_range_sub_app; [exact Hfapp | exact Hfceil | lia | lia | lia]
    | apply (range_addressable_sub _ _ blk BLK_LEN); [| lia | unfold BLK_LEN; lia];
      exact (ra_sinv _ _ _ _ _ _ _ blk BLK_LEN HINV HLO HappF ltac:(lia) ltac:(unfold BLK_LEN; lia) HRAb)
    | intros _; apply (hull_sub _ blk BLK_LEN); [| lia | lia | unfold BLK_LEN; lia | lia];
      exact (hull_sinv _ _ _ _ _ _ _ blk BLK_LEN HINV HLO HappF ltac:(lia) ltac:(unfold BLK_LEN; lia) ltac:(unfold BLK_LEN; lia) HHVb)
    | split; [lia|]; split; [lia|]; split;
      [ intros a Ha; split;
        [ rewrite (proj1 HINV a ltac:(lia) ltac:(unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia)
            ltac:(intros _; unfold BLK_LEN, TT_LEN in *; lia));
          replace a with (A_TT + (a - A_TT)) by lia; rewrite HTT by (unfold TT_LEN; lia); discriminate
        | rewrite SPT; lia ]
      |]; split; [unfold BLK_LEN, TT_LEN in *; lia|]; split;
      [ unfold amem_range, kLowMemEnd; left; lia |]; split;
      [ exact (ra_sinv _ _ _ _ _ _ _ A_TT TT_LEN HINV HLO HappF ltac:(lia) ltac:(unfold TT_LEN; lia) HRAtt)
      | intros _; exact (hull_sinv _ _ _ _ _ _ _ A_TT TT_LEN HINV HLO HappF ltac:(lia) ltac:(unfold TT_LEN; lia)
                          ltac:(unfold TT_LEN; lia) HHVtt) ] ]
  | ].
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff4 & Hfr4 & Hpres4).
  pose proof (sinv_call _ _ _ _ _ _ _ _ _ _ _ blk HINV Hfr4 Hpres4
    ltac:(intros a Ha; split; [exact HOKT | unfold BLK_LEN; lia]) ltac:(unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia)
    ltac:(lia)) as HINV4.
  rename HINV into HINVp; rename HINV4 into HINV.
  eapply (tail_from_call W rgT regs4 mmT mem4 md4 STK sp0 o FP ly S W0 mem0 md0 own lyc Sc k regs mem blk body n 342 b cid pos
            (blk + 21) 12 HJ4 Hsp Ho16 Ho0 HoS Hra R2T R8T R9T R20T RKT HP4 Hfr4 ltac:(lia) ltac:(unfold BLK_LEN; lia)
            V1 V8 V9 V18 V19 V20 HOKT ltac:(lia) Hlb' Hown Hcid Hflo Hfhi).
  - exact (ra_sinv _ _ _ _ _ _ _ blk BLK_LEN HINV HLO HappF ltac:(lia) ltac:(unfold BLK_LEN; lia) HRAb).
  - intros j Hj. destruct (Nat.ltb_spec j 21) as [Hj21 | Hj21].
    + rewrite Hfr4 by (unfold BLK_LEN in *; lia). exact (B2 j Hj21).
    + rewrite (sb_last b j Hlb' Hj). destruct (Nat.ltb_spec j 7) as [?|_]; [lia|]. destruct (Nat.ltb_spec j 21) as [?|_]; [lia|].
      eapply copy_bytes; [exact Heff4 | lia |].
      rewrite (proj1 HINVp);
        [| lia | unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia | intros _; unfold BLK_LEN, TT_LEN in *; lia].
      replace (A_TT + (blk + Z.of_nat j - (blk + 21))) with (A_TT + Z.of_nat (j - 21)) by lia.
      rewrite HTT by (unfold TT_LEN; lia). unfold bu. rewrite Nat2Z.id. reflexivity.
  - exact HINV.
}
cond_norm Hc E'10 E'11 E'12 E'13. rename Hc into Hst_not_last.
(* 0x838d8..0x838e0: the check address of blk + 2 (hoisted); bnez s3 *)
paj_run_tok RUN HS HJ2 SHOK Bspan; [awr_main Usp' Ublk' HAWB |].
sinv_after HINV HFr HG Usp' Ublk'.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* ---- MIDDLE: 1 <= step <= 341 ---- *)
  cond_norm Hc E'10 E'11 E'12 E'13. rename Hc into Hst_not_first.
  assert (Hmid : 1 <= st <= 341) by lia.
  (* 0x83a20..0x83a80: blk[2] = 1, blk[6] = 0, blk[5] = 26; the copy of body[24 + 26 (step - 1) ..) to blk + 7 *)
  paj_run_tok RUN HS HJ2 SHOK Bspan; [awr_main Usp' Ublk' HAWB |].
  sinv_after HINV HFr HG Usp' Ublk'.
  pmkst HS.
  pre_bytes HS 0%nat Ublk' blk [205; 234; 1; 0; 0; 26; 0] 7%nat PRE.
  prreg HS (10%bv : bv 5) Ra0. rawreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
  prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
  spt Rsp Usp' sp0 o.
  tail_regs HS Usp' E'10 E'32 EK' regs blk sp0 o.
  tail_slots HS 1%nat Usp' EK' regs sp0 o.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ => set (rgT := rg) in *; set (mmT := mm) in * end.
  eapply SRr_bind;
  [ eapply (aj_intrin_at (SK := SK) SEGS B LAWS Hsegs OCpy (SIGMA SS___asan_memcpy) AMEMCPY W rgT mmT
      STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (blk + 7) (body + (24 + 26 * (st - 1))) 26 (o - 48) _ HJ2);
    [ rewrite Ra0; tenv; rewrite E'10, unsigned_lit_small by lia; reflexivity
    | addr_val Ra1
    | rewrite Ra2; reflexivity
    | lia | lia | unfold BLK_LEN in *; lia
    | rewrite SPT; lia
    | apply mod16_m48; exact Ho16
    | lia
    | unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia
    | rewrite Rgp; tenv; rewrite E'3; exact Hgp
    | rewrite Rtp; tenv; rewrite E'4; exact Htp
    | exact Rra
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | intros a Ha; split; [apply HAWB; unfold BLK_LEN; lia | unfold BLK_LEN in *; lia]
    | eapply amem_range_sub_app; [exact Hfapp | exact Hfceil | lia | lia | lia]
    | apply (range_addressable_sub _ _ blk BLK_LEN); [| lia | unfold BLK_LEN; lia];
      exact (ra_sinv _ _ _ _ _ _ _ blk BLK_LEN HINV HLO HappF ltac:(lia) ltac:(unfold BLK_LEN; lia) HRAb)
    | intros _; apply (hull_sub _ blk BLK_LEN); [| lia | lia | unfold BLK_LEN; lia | lia];
      exact (hull_sinv _ _ _ _ _ _ _ blk BLK_LEN HINV HLO HappF ltac:(lia) ltac:(unfold BLK_LEN; lia) ltac:(unfold BLK_LEN; lia) HHVb)
    | cpy_body HJ2 HINV HBODY Hpq SPT body pq mq ]
  | ].
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3).
  pose proof (sinv_call _ _ _ _ _ _ _ _ _ _ _ blk HINV Hfr3 Hpres3
    ltac:(intros a Ha; split; [exact HOKT | unfold BLK_LEN; lia]) ltac:(unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia)
    ltac:(lia)) as HINV3.
  rename HINV into HINVp; rename HINV3 into HINV.
  eapply (tail_from_call W rgT regs3 mmT mem3 md3 STK sp0 o FP ly S W0 mem0 md0 own lyc Sc k regs mem blk body n st b cid pos
            (blk + 7) 26 HJ3 Hsp Ho16 Ho0 HoS Hra R2T R8T R9T R20T RKT HP3 Hfr3 ltac:(lia) ltac:(unfold BLK_LEN; lia)
            V1 V8 V9 V18 V19 V20 HOKT ltac:(lia) Hlb' Hown Hcid Hflo Hfhi).
  - exact (ra_sinv _ _ _ _ _ _ _ blk BLK_LEN HINV HLO HappF ltac:(lia) ltac:(unfold BLK_LEN; lia) HRAb).
  - intros j Hj. rewrite (sb_mid b st j Hlb' Hmid Hj). destruct (Nat.ltb_spec j 7) as [Hj7 | Hj7].
    + rewrite Hfr3 by (unfold BLK_LEN in *; lia). exact (PRE j Hj7).
    + eapply copy_bytes; [exact Heff3 | lia |].
      rewrite (proj1 HINVp);
        [| lia | unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia | intros _; unfold BLK_LEN in *; lia].
      replace (body + (24 + 26 * (st - 1)) + (blk + Z.of_nat j - (blk + 7)))
        with (body + Z.of_nat (Z.to_nat (24 + 26 * (st - 1)) + (j - 7))) by lia.
      rewrite HBODY by (unfold SCENE_BYTES in *; lia). unfold bu. rewrite Nat2Z.id. reflexivity.
  - exact HINV.
}
(* ---- FIRST: step = 0 ---- *)
cond_norm Hc E'10 E'11 E'12 E'13. subst st.
(* 0x838e4..0x83980: blk[2..9) = 1, 1, 0, 24, -, 34, 200; the copy of body[0..24) to blk + 9 *)
paj_run_tok RUN HS HJ2 SHOK Bspan; [awr_main Usp' Ublk' HAWB |].
sinv_after HINV HFr HG Usp' Ublk'.
pmkst HS.
pre_bytes HS 0%nat Ublk' blk [205; 234; 1; 1; 0; 24; 0; 34; 200] 9%nat PRE.
prreg HS (10%bv : bv 5) Ra0. rawreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
spt Rsp Usp' sp0 o.
tail_regs HS Usp' E'10 E'32 EK' regs blk sp0 o.
tail_slots HS 1%nat Usp' EK' regs sp0 o.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ => set (rgT := rg) in *; set (mmT := mm) in * end.
eapply SRr_bind;
[ eapply (aj_intrin_at (SK := SK) SEGS B LAWS Hsegs OCpy (SIGMA SS___asan_memcpy) AMEMCPY W rgT mmT
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (blk + 9) body 24 (o - 48) _ HJ2);
  [ rewrite Ra0; tenv; rewrite E'10, unsigned_lit_small by lia; reflexivity
  | addr_val Ra1
  | rewrite Ra2; reflexivity
  | lia | lia | unfold BLK_LEN in *; lia
  | rewrite SPT; lia
  | apply mod16_m48; exact Ho16
  | lia
  | unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia
  | rewrite Rgp; tenv; rewrite E'3; exact Hgp
  | rewrite Rtp; tenv; rewrite E'4; exact Htp
  | exact Rra
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros a Ha; split; [apply HAWB; unfold BLK_LEN; lia | unfold BLK_LEN in *; lia]
  | eapply amem_range_sub_app; [exact Hfapp | exact Hfceil | lia | lia | lia]
  | apply (range_addressable_sub _ _ blk BLK_LEN); [| lia | unfold BLK_LEN; lia];
    exact (ra_sinv _ _ _ _ _ _ _ blk BLK_LEN HINV HLO HappF ltac:(lia) ltac:(unfold BLK_LEN; lia) HRAb)
  | intros _; apply (hull_sub _ blk BLK_LEN); [| lia | lia | unfold BLK_LEN; lia | lia];
    exact (hull_sinv _ _ _ _ _ _ _ blk BLK_LEN HINV HLO HappF ltac:(lia) ltac:(unfold BLK_LEN; lia) ltac:(unfold BLK_LEN; lia) HHVb)
  | cpy_body HJ2 HINV HBODY Hpq SPT body pq mq ]
| ].
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3).
pose proof (sinv_call _ _ _ _ _ _ _ _ _ _ _ blk HINV Hfr3 Hpres3
  ltac:(intros a Ha; split; [exact HOKT | unfold BLK_LEN; lia]) ltac:(unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia)
  ltac:(lia)) as HINV3.
rename HINV into HINVp; rename HINV3 into HINV.
eapply (tail_from_call W rgT regs3 mmT mem3 md3 STK sp0 o FP ly S W0 mem0 md0 own lyc Sc k regs mem blk body n 0 b cid pos
          (blk + 9) 24 HJ3 Hsp Ho16 Ho0 HoS Hra R2T R8T R9T R20T RKT HP3 Hfr3 ltac:(lia) ltac:(unfold BLK_LEN; lia)
          V1 V8 V9 V18 V19 V20 HOKT ltac:(lia) Hlb' Hown Hcid Hflo Hfhi).
- exact (ra_sinv _ _ _ _ _ _ _ blk BLK_LEN HINV HLO HappF ltac:(lia) ltac:(unfold BLK_LEN; lia) HRAb).
- intros j Hj. rewrite (sb_first b j Hlb' Hj). destruct (Nat.ltb_spec j 9) as [Hj9 | Hj9].
  + rewrite Hfr3 by (unfold BLK_LEN in *; lia). exact (PRE j Hj9).
  + eapply copy_bytes; [exact Heff3 | lia |].
    rewrite (proj1 HINVp);
      [| lia | unfold SCENE_STEP_WIN, SCENE_STEP_FRAME in *; lia | intros _; unfold BLK_LEN in *; lia].
    replace (body + (blk + Z.of_nat j - (blk + 9))) with (body + Z.of_nat (j - 9)) by lia.
    rewrite HBODY by (unfold SCENE_BYTES in *; lia). unfold bu. rewrite Nat2Z.id. reflexivity.
- exact HINV.
Qed.
End h.
End f.
End d.
