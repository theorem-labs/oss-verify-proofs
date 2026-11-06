(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_grant/proofs/lib/A/Prog/KindOfLink1.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/A/Prog/P_kind_of_link1.v, with its module paths and module names changed; 387 of its 433 lines of code are new or changed and 129 lines of the source are left out. *)
(* reac_ctrl_block_cksum_stamp (fuzz_scene.asan-ubsan 0x83930, 46 instructions; reac_ctrlblk.c:33-39):
   the contract of the asan-ubsan build's code and its walk.

   The only caller, reac_ctrl_build_scene_step (0x83d34), passes q = blk + 2, where blk is a local of
   the frame of LLVMFuzzerTestOneInput that the class-8 frame allocator gave it. So the stamp writes a
   frame object two calls up. The contract therefore takes the CALLER's journal and returns it
   extended, in the shape of the core's intrinsic lemma aj_intrin_at (Reusable/YCbq.v): the write of
   q + 31 is awr_byte's own-frame case (in_frames lyc own), which a journal started by the callee
   (afn_pre / apost_base, own = []) cannot use (BLK-FRAME.md (sha256 59cb1284237b; internal record)).

   What the code does: it takes a 16-byte frame and saves ra in it; it loads the shadow base K
   through the GOT; it sums the 31 bytes q[0..31) in a count-down loop (a4 = 31..1, two pointers
   a1 = a6 = q + i, the sum in a2); before each load the UBSan guards (q + i <u q; (q <> 0) xor
   (q + i = 0) = 0; q = 0) branch to the trap word, and the inline check of the metadata byte of
   q + i runs (slow path: andi t0,a1,7; blt t0,a7); after the loop the UBSan guard q >=u -31 branches
   to the trap word, the check of q + 31 runs, and the byte (- sum) mod 256 is stored at q + 31; ra
   is reloaded, the frame released, and it returns. It writes a0..a7 and (slow load path) t0, and
   no other register. Under the premises no trap and no report is reached: q is at least 4096 and
   q + 32 lies below alloc_ceiling (q is inside a frame of the journal's own), and q's 32 bytes are
   marked usable.

   Numerals, each read from the pinned image
   pau-pipeline/libreac/bin/fuzz_scene/fuzz_scene.asan-ubsan
   (sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f; the unstripped twin
   unstripped/fuzz_scene/fuzz_scene.asan-ubsan, sha256 ef0b41158fe08b45b5a8a0e514f8ebc31f2960d2b90acc03576a682fae2baf33,
   holds the same 46 words at 0x83930 and gives the symbols):
   - the function: .symtab reac_ctrl_block_cksum_stamp = 0x83930, size 184 = 46 words; its offset
     AF_reac_ctrl_block_cksum_stamp = 0x108c comes from lib/AU/Prog/SceneList.v (0x83930 - 0x828a4,
     .symtab LLVMFuzzerTestOneInput = 0x828a4 = the listing's base) and is not restated here.
   - 16 (STAMP_FRAME, stack_region 16): addi sp,sp,-16 at 0x83930 (0xff010113); sd ra,8(sp) at 0x83934
     (0x00113423); ld ra,8(sp) at 0x839cc (0x00813083); addi sp,sp,16 at 0x839d0 (0x01010113).
   - 32 (STAMP_LEN): the bytes the code reads and writes are q + 0 .. q + 31: the loads lbu a7,0(a6)
     at 0x8397c (0x00084883) with a6 = q + i, i = 0..30, and the store sb a1,0(a0) at 0x839c8
     (0x00b50023) with a0 = q + 31 (addi a0,a0,31 at 0x839b0, 0x01f50513). It is REAC_CTRL_BLOCK_LEN.
   - 31 (the loop count and the checksum byte's offset): li a4,31 at 0x83948 (0x01f00713), counted down
     by addi a4,a4,-1 at 0x83984 (0xfff70713) and tested by bnez a4 at 0x83990 (0xfc0714e3); the
     addi a0,a0,31 at 0x839b0.
   - -31 (the UBSan guard of q + 31): li a1,-31 at 0x839a8 (0xfe100593); bgeu a0,a1 at 0x839ac
     (0x02b57663) goes to the trap word unimp at 0x839d8 (0xc0001073). The loop's guards bltu a1,a0
     at 0x83958 (0x08a5e063), beqz a7 at 0x83964 (0x06088a63) after snez a5,a0 at 0x8394c (0x00a037b3),
     seqz a7,a1 at 0x8395c (0x0015b893), xor a7,a5,a7 at 0x83960 (0x0117c8b3), and beqz a0 at 0x83968
     (0x06050863) go to the same trap word.
   - the shadow base: auipc a1,0x18 at 0x8393c (0x00018597) and ld a1,260(a1) at 0x83940 (0x1045b583)
     read the GOT word 0x9ba40 (object 1, lib/AU/Prog/SceneAddr.v), which holds 0xa3af8 =
     .symtab __asan_shadow_memory_dynamic_address (object 16); ld a3,0(a1) at 0x83944 (0x0005b683)
     reads the cell. Both through PALib (pal_got_shadow, pal_cell) and the core's al_const.
   - the checks (access size 1): load q + i, 0x8396c..0x83978 (srli/add/lb/bnez), slow path 0x83998
     (andi t0,a1,7; blt t0,a7 back to 0x8397c), report call jal __asan_report_load1 (0x5ab08) at
     0x839a4; store q + 31, 0x839b4..0x839c0, slow path 0x839dc (andi a3,a0,7; blt a3,a1 back to
     0x839c4), report call jal __asan_report_store1 (0x5ae28) at 0x839e4.
   - STAMP_CLOB, the registers the code writes: a2 (li a2,0 0x83938; add 0x83988), a1 (0x8393c,
     0x83940, 0x83954, 0x83980, 0x839a8, 0x839b4..0x839bc, 0x839c4), a3 (0x83944, 0x839dc), a4 (0x83948,
     0x83984), a5 (0x8394c), a6 (0x83950, 0x8398c), a7 (0x8395c..0x83974, 0x8397c), a0 (0x839a0 on the
     report path, 0x839b0), t0 (0x83998). ra is reloaded with its saved value; sp is restored.
   The other constants are not image numerals: ESTACK is not used (the function makes no call that
   returns); the stack-pointer fact (2 ^ 46, 2 ^ 47, alignment 2 ^ 4) comes from astk_ok and
   asan_consts (Reusable/YCbq.v); PTR 0 (YC4b.v) is the pointer fact of q; SB (YC81.v) is the
   shadow offset SHADOW_OFF (Reusable/YG0f.v); 256, 2 ^ 63, 2 ^ 64 are byte and word bounds. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import
PaRun PaShadow PaStep PaJournal SceneSyms SceneList ScenePa ScenePaLib.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import YC81 YC4b YC1g YC1h YCbw YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------ *)
(* The constants of the code (the header names the instruction each comes from).               *)
Definition STAMP_FRAME : Z := 16.
Definition STAMP_LEN : Z := 32.
(* t0 and a0..a7: the registers the code writes. *)
Definition STAMP_CLOB : list (bv 5) := [5; 10; 11; 12; 13; 14; 15; 16; 17]%bv.
(* The others but x0. *)
Definition STAMP_KEPT : list (bv 5) :=
  [1; 2; 3; 4; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

(* ------------------------------------------------------------------------------------------ *)
(* Bytes and their sum.                                                                        *)
Lemma byte_range : forall x : byte, 0 <= bv_unsigned x < 256.
Proof. intros x. pose proof (bv_unsigned_in_range 8 x) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.

Definition bu (l : list byte) (j : nat) : Z := bv_unsigned (nth j l (Z_to_bv 8 0)).
Lemma bu_range : forall l j, 0 <= bu l j < 256.
Proof. intros l j. unfold bu. apply byte_range. Qed.

Definition fsum31 (l : list byte) : Z :=
  bu l 0 + bu l 1 + bu l 2 + bu l 3 + bu l 4 + bu l 5 + bu l 6 + bu l 7 + bu l 8 + bu l 9
  + bu l 10 + bu l 11 + bu l 12 + bu l 13 + bu l 14 + bu l 15 + bu l 16 + bu l 17 + bu l 18 + bu l 19
  + bu l 20 + bu l 21 + bu l 22 + bu l 23 + bu l 24 + bu l 25 + bu l 26 + bu l 27 + bu l 28 + bu l 29
  + bu l 30.

Lemma byte_sum_31 : forall l, length l = 31%nat -> byte_sum l = fsum31 l.
Proof.
  intros l Hl.
  do 31 (destruct l as [|? l]; [cbn [length] in Hl; lia|]).
  destruct l; [|cbn [length] in Hl; lia].
  unfold fsum31, bu, byte_sum. cbn [nth fold_right]. lia.
Qed.

Lemma fsum31_range : forall l, 0 <= fsum31 l < 2 ^ 64.
Proof.
  intros l. unfold fsum31.
  repeat match goal with |- context [bu l ?j] =>
    lazymatch goal with _ : 0 <= bu l j < 256 |- _ => fail | _ => pose proof (bu_range l j) end end.
  lia.
Qed.

Lemma neg_low_byte : forall s, 0 <= s < 2 ^ 64 ->
  ((- s) mod 2 ^ 64) mod 256 = (256 - s mod 256) mod 256.
Proof.
  intros s Hs.
  rewrite Z.mod_mod_divide by first [exists (2 ^ 56); reflexivity | lia].
  replace (- s) with (0 - s) by lia.
  rewrite (Zminus_mod 0 s 256), (Zminus_mod 256 (s mod 256) 256), Z.mod_same, Z.mod_mod, Zmod_0_l by lia.
  reflexivity.
Qed.

(* The stored byte, (- sum) mod 2 ^ 64 cut to 8 bits, is the C value (256 - (s & 0xff)) & 0xff. *)
Lemma stamp_cks : forall fb x, length fb = 31%nat -> x = fsum31 fb ->
  ((- x) mod 2 ^ 64) mod 256 = (256 - byte_sum fb mod 256) mod 256.
Proof.
  intros fb x Hl ->. rewrite (byte_sum_31 fb Hl). apply neg_low_byte. apply fsum31_range.
Qed.

Lemma mod16_add : forall s o, s mod 16 = 0 -> o mod 16 = 0 -> (s + o) mod 16 = 0.
Proof. intros s o Hs Ho. rewrite Z.add_mod, Hs, Ho by lia. reflexivity. Qed.

(* A register that is not in STAMP_CLOB is x0 or in STAMP_KEPT. *)
Lemma stamp_kept_regs : forall r : bv 5, ~ In r STAMP_CLOB -> r = 0%bv \/ In r STAMP_KEPT.
Proof.
  intros r Hr.
  assert (Hu : 0 <= bv_unsigned r < 32)
    by (pose proof (bv_unsigned_in_range 5 r) as H; change (bv_modulus 5) with 32 in H; exact H).
  assert (Hz : bv_unsigned r = 0 \/ bv_unsigned r = 1 \/ bv_unsigned r = 2 \/ bv_unsigned r = 3 \/
               bv_unsigned r = 4 \/ bv_unsigned r = 5 \/ bv_unsigned r = 6 \/ bv_unsigned r = 7 \/
               bv_unsigned r = 8 \/ bv_unsigned r = 9 \/ bv_unsigned r = 10 \/ bv_unsigned r = 11 \/
               bv_unsigned r = 12 \/ bv_unsigned r = 13 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15 \/
               bv_unsigned r = 16 \/ bv_unsigned r = 17 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/
               bv_unsigned r = 20 \/ bv_unsigned r = 21 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/
               bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27 \/
               bv_unsigned r = 28 \/ bv_unsigned r = 29 \/ bv_unsigned r = 30 \/ bv_unsigned r = 31) by lia.
  clear Hu.
  repeat (destruct Hz as [Hz | Hz]);
  first
  [ exfalso; apply Hr; unfold STAMP_CLOB;
    solve [repeat (first [left; apply bv_eq; rewrite Hz; reflexivity | right])]
  | left; apply bv_eq; rewrite Hz; reflexivity
  | right; unfold STAMP_KEPT;
    solve [repeat (first [left; apply bv_eq; rewrite Hz; reflexivity | right])] ].
Qed.

(* The register clause of the post gives the callee-saved one (aregs_preserved). *)
Lemma stamp_clob_preserved : forall regs regs' : bvmap 5 word,
  (forall r : bv 5, ~ In r STAMP_CLOB -> getr regs' r = getr regs r) -> aregs_preserved regs regs'.
Proof.
  intros regs regs' H r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr.
  repeat (destruct Hc as [-> | Hc]); [ .. | subst r ];
  apply H; unfold STAMP_CLOB; intros Hin; cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [apply (f_equal bv_unsigned) in Hin; vm_compute in Hin; discriminate Hin |]);
  exact Hin.
Qed.

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

Section m. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Lemma aview_of_mbyte_lit : forall H m a v,
  mbyte segs (mrestrict H m) a = Some (Z_to_bv 8 v) -> 0 <= v < 256 -> aview segs H m a = Some v.
Proof.
  intros H m a v Hm Hv. unfold aview. rewrite Hm. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.
Lemma val_mem1_aview : forall H (m : word -> option byte) a v, 0 <= v < 256 ->
  val_mem segs (mrestrict H m) a 1 v -> aview segs H m a = Some v.
Proof.
  intros H m a v Hv Hm. apply aview_of_mbyte_lit; [|exact Hv].
  specialize (Hm 0%nat ltac:(lia)). cbn [Z.of_nat] in Hm. rewrite Z.add_0_r in Hm. rewrite Hm.
  rewrite (le_byte_1_0 v Hv). reflexivity.
Qed.
End m.

(* Normalising an environment that the run extended, down to the atoms below. *)
Ltac tenv := cbn [ew ewset extK havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub length Nat.add];
  rewrite ?ew_ewset_other by lia; repeat (rewrite YN3v.ew_havoc_old; [|cbv; lia]).

(* The value of a sum, loads and negation term, bottom up; the leaves are atoms whose values the
   context names (ew E k = Z_to_bv 64 v) with their ranges. *)
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

(* ------------------------------------------------------------------------------------------ *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).

Definition A_reac_ctrl_block_cksum_stampP : Z := BASE + AF_reac_ctrl_block_cksum_stamp.

Section h.
Variable B : asyms.

(* The contract. q is the block (a0); fb names its first 31 bytes at entry.
   Post: the world is kept; the run returns to ra; the caller's journal extends (same STK, sp0, FP,
   own, lyc, Sc, k); every register but t0 and a0..a7 keeps its entry value; every byte outside the
   function's frame [sp - 16, sp) and outside q + 31 keeps its value; present bytes stay present;
   and q + 31 holds (256 - (sum of the 31 bytes mod 256)) mod 256, the C source's
   (uint8_t)((256 - (s & 0xff)) & 0xff). *)
Definition treac_ctrl_block_cksum_stamp_post (regs : bvmap 5 word) (STK sp0 : Z) (FP : list (Z * Z))
  ly S (W0 : world SEGS) mem0 md0 own lyc Sc (W : world SEGS) mem (k : Z) (q : Z) (fb : list byte)
  : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
    ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
    (forall r : bv 5, ~ In r STAMP_CLOB -> getr regs' r = getr regs r) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STAMP_FRAME <= a < spZ regs) -> a <> q + 31 ->
       aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
    aview SEGS (w_H W) mem' (q + 31) = Some ((256 - byte_sum fb mod 256) mod 256).

(* Premises: the caller's journal from its entry to the call; the call's sp inside the caller's
   stack window with room for the 16-byte frame; ra a return address; a0 = q; q's 32 bytes inside a
   frame of the journal's own (the caller's local); q's 32 bytes marked usable; fb the 31 bytes
   the loop reads. *)
Definition treac_ctrl_block_cksum_stamp_spec : Prop :=
  forall (W : world SEGS) (regs : bvmap 5 word) mem md (STK sp0 o : Z) (FP : list (Z * Z))
         ly S (W0 : world SEGS) mem0 md0 own lyc Sc (k : Z) (q : Z) (fb : list byte),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> STAMP_FRAME - o <= STK ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 q -> 0 <= q < 2 ^ 64 ->
  (exists cid pos, In (cid, pos) own /\ 0 <= cid /\
     frame_addr lyc cid pos <= q /\ q + STAMP_LEN <= frame_addr lyc cid pos + fs_frame_bytes cid) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q STAMP_LEN ->
  length fb = 31%nat ->
  (forall i, 0 <= i < 31 ->
     aview SEGS (w_H W) mem (q + i) = Some (bv_unsigned (nth (Z.to_nat i) fb (Z_to_bv 8 0)))) ->
  SRr SEGS W (cfg_at SEGS A_reac_ctrl_block_cksum_stampP regs mem md)
    (treac_ctrl_block_cksum_stamp_post regs STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem k q fb).

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.                                   (* ScenePaLib: shadow-base GOT slot and cell *)
Let HBgot := pal_got_shadow B TL.
Let HBcell := pal_cell B TL.
Let RUN := paj_run (SK := SK) B LAWS.
Let RET := paj_ret_at (PL := PL_scene) (PI := PI).

(* ------------------------------------------------------------------------------------------ *)
(* The walk's symbolic state at entry: atoms 0..31 the entry registers, atom 32 the shadow base,
   atoms 33..63 the 31 bytes q[0..31); regions: the frame below sp, the GOT word and the cell of the
   shadow base (read-only), and q's 32 bytes (bytes 0..30 the atoms, byte 31 writable). *)
Definition BX : sv := SOff 32 0.
Definition stamp_extra (fb : list byte) : list word :=
  Z_to_bv 64 SB :: map (fun j => Z_to_bv 64 (bu fb j)) (seq 0 31).
Definition E_S (regs : bvmap 5 word) (fb : list byte) : env := Eimg (Ereg regs (stamp_extra fb)).
Definition RQ : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 32 31 32
    (map (fun j : nat => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (33 + j)%nat 0))) (seq 0 31)).
Definition ss_S : sstate :=
  mkSS AF_reac_ctrl_block_cksum_stamp sr_atoms [stack_region STAMP_FRAME; got_regionP; bcell_regionP 32; RQ] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTR 0); (32%nat, mkAF SB SB 0)] [] []).
Definition SH_S : list shent := [mkSHE 10 0 32].

Lemma nth_map_seq0 : forall (f : nat -> word) n j d, (j < n)%nat -> nth j (map f (seq 0 n)) d = f j.
Proof.
  intros f n j d Hj. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hj).
  rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.

Lemma stamp_extra_atom : forall regs fb j, (j < 31)%nat ->
  ew (Ereg regs (stamp_extra fb)) (33 + j) = Z_to_bv 64 (bu fb j).
Proof.
  intros regs fb j Hj. replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra.
  unfold stamp_extra. cbn [nth].
  exact (nth_map_seq0 (fun j0 => Z_to_bv 64 (bu fb j0)) 31 j _ Hj).
Qed.

Lemma stamp_entry : forall W (regs : bvmap 5 word) mem md (STK sp0 o : Z) FP ly S W0 mem0 md0 own lyc Sc k
    (q : Z) (fb : list byte) cid pos,
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> STAMP_FRAME - o <= STK ->
  getr regs 10 = w64 q -> 0 <= q < 2 ^ 64 ->
  In (cid, pos) own -> 0 <= cid ->
  frame_addr lyc cid pos <= q -> q + STAMP_LEN <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  (forall j, (j < 31)%nat -> aview SEGS (w_H W) mem (q + Z.of_nat j) = Some (bu fb j)) ->
  st_ok_pi SEGS VAL (E_S regs fb) ss_S
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_ctrl_block_cksum_stamp)) mem (seg_rom SEGS))).
Proof.
  intros W regs mem md STK sp0 o FP ly S W0 mem0 md0 own lyc Sc k q fb cid pos
    HJ Hsp Ho16 Ho0 HoS H10 Hq Hown Hcid Hflo Hfhi HBY.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & HJpres & Hstk & _).
  pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
  assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  destruct (frames_bounds SEGS B LAWS lyc Sc W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
  destruct ((al_frames _ _ LAWS) lyc Sc W mem md cid pos HAR Hfin) as (Hf32 & _ & Hfpres & _).
  pose proof (fs_frame_bytes_pos cid Hcid) as Hfb.
  pose proof (frm_off_imgP B lyc Sc W mem md cid pos HAR Hfin) as Hfimg. unfold off_img in Hfimg.
  destruct ((al_const _ _ LAWS) lyc Sc W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_obj_img 16 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  rewrite restrict_mkst_fx.
  set (E := E_S regs fb).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (stamp_extra fb)) n)
    by (intros n Hn; subst E; unfold E_S; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (EX : forall j, (j < 31)%nat -> ew E (33 + j) = Z_to_bv 64 (bu fb j))
    by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply stamp_extra_atom; exact Hj).
  assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold E_S; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Ecell : ew E (A_OBJ 16) = Z_to_bv 64 (VAL (A_OBJ 16))) by (subst E; unfold E_S; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = sp0 + o) by (rewrite E2; exact Hsp).
  assert (Uq : bv_unsigned (ew E 10) = q) by (rewrite E10, H10; unfold w64; apply unsigned_lit_small; lia).
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
  { intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  unfold ss_S. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region, got_regionP, bcell_regionP, RQ.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. unfold STAMP_FRAME in *.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o' Ho'. apply (apresent_writable SEGS). apply HJpres. lia.
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 16) 0) (VAL (A_OBJ 16)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 16)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 16) (VAL (A_OBJ 16)) Ecell) by (pose proof (pa_val_range (A_OBJ 16)); lia).
      split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 16)) 0 8 BX SB);
      [cbn [sv_denot BX]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    + cbn [base_val]. rewrite Uq. unfold STAMP_LEN in *.
      split; [lia|]. split; [lia|]. split.
      * intros o' Ho'. apply (apresent_writable SEGS). apply (proj1 (Hfpres (q + o') ltac:(lia))).
      * apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
        apply (chunk_ok_val SEGS E _ _ (Z.of_nat j) 1%N (SOff (33 + j)%nat 0) (bu fb j)).
        -- cbn [sv_denot]. rewrite (EX j ltac:(lia)), Z.add_0_r, unsigned_lit_small by (pose proof (bu_range fb j); lia).
           reflexivity.
        -- pose proof (bu_range fb j). cbn. lia.
        -- cbn. lia.
        -- exact (proj1 (val_mem1_of_aview SEGS (w_H W) mem (q + Z.of_nat j) (bu fb j) (HBY j ltac:(lia)))).
  - apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, RQ, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 16) (VAL (A_OBJ 16)) Ecell) by (pose proof (pa_val_range (A_OBJ 16)); lia).
    cbn [base_val]. rewrite Usp, Uq.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold STAMP_FRAME, STAMP_LEN in *.
    revert Hslo Hshi H47 Hceil C1 C3 HSTK0 HcellR HgcD HgotR HoS Hsp Ho0 Hfimg Hflo Hfhi Hfceil Hf4096 Hfb Hq.
    clear. intros.
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uq, E32, unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold STAMP_FRAME, STAMP_LEN in *.
    repeat match goal with |- _ /\ _ => split end; first [lia | apply mod16_add; assumption].
Qed.

(* ------------------------------------------------------------------------------------------ *)
Theorem pb_reac_ctrl_block_cksum_stamp : treac_ctrl_block_cksum_stamp_spec.
Proof.
unfold treac_ctrl_block_cksum_stamp_spec.
intros W regs mem md STK sp0 o FP ly S W0 mem0 md0 own lyc Sc k q fb
  HJ Hsp Ho16 Ho0 HoS Hra H10 Hq (cid & pos & Hown & Hcid & Hflo & Hfhi) HRA Hlen HFB.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & HJpres & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
pose proof (fs_frame_bytes_pos cid Hcid) as Hfb.
assert (HBY : forall j, (j < 31)%nat -> aview SEGS (w_H W) mem (q + Z.of_nat j) = Some (bu fb j)).
{ intros j Hj. rewrite HFB by lia. unfold bu. rewrite Nat2Z.id. reflexivity. }
pose proof (stamp_entry W regs mem md STK sp0 o FP ly S W0 mem0 md0 own lyc Sc k q fb cid pos
  HJ Hsp Ho16 Ho0 HoS H10 Hq Hown Hcid Hflo Hfhi HBY) as HS.
pose proof HS as HS0.
remember (E_S regs fb) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (stamp_extra fb)) n)
  by (intros n0 Hn0; subst E; apply Eimg_low; exact Hn0).
assert (HAE : env_agree 32 (Ereg regs (stamp_extra fb)) E)
  by (split; [intros n0 Hn0; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (ER : forall (r : bv 5) (nr : nat), Z.of_nat nr = bv_unsigned r -> (nr < 32)%nat -> ew E nr = getr regs r)
  by (intros r nr Hr Hn; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ nr r Hr)).
assert (EX : forall j, (j < 31)%nat -> ew E (33 + j) = Z_to_bv 64 (bu fb j))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply stamp_extra_atom; exact Hj).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (rewrite (ER 10%bv 10%nat eq_refl ltac:(lia)); exact H10).
assert (Usp : bv_unsigned (ew E 2) = sp0 + o) by (rewrite (ER 2%bv 2%nat eq_refl ltac:(lia)); exact Hsp).
assert (Uq : bv_unsigned (ew E 10) = q) by (rewrite E10; apply unsigned_lit_small; lia).
(* the 31 bytes the loop sums, as atoms 33..63 *)
pose proof (EX 0%nat ltac:(lia)) as X0. pose proof (EX 1%nat ltac:(lia)) as X1. pose proof (EX 2%nat ltac:(lia)) as X2.
pose proof (EX 3%nat ltac:(lia)) as X3. pose proof (EX 4%nat ltac:(lia)) as X4. pose proof (EX 5%nat ltac:(lia)) as X5.
pose proof (EX 6%nat ltac:(lia)) as X6. pose proof (EX 7%nat ltac:(lia)) as X7. pose proof (EX 8%nat ltac:(lia)) as X8.
pose proof (EX 9%nat ltac:(lia)) as X9. pose proof (EX 10%nat ltac:(lia)) as X10. pose proof (EX 11%nat ltac:(lia)) as X11.
pose proof (EX 12%nat ltac:(lia)) as X12. pose proof (EX 13%nat ltac:(lia)) as X13. pose proof (EX 14%nat ltac:(lia)) as X14.
pose proof (EX 15%nat ltac:(lia)) as X15. pose proof (EX 16%nat ltac:(lia)) as X16. pose proof (EX 17%nat ltac:(lia)) as X17.
pose proof (EX 18%nat ltac:(lia)) as X18. pose proof (EX 19%nat ltac:(lia)) as X19. pose proof (EX 20%nat ltac:(lia)) as X20.
pose proof (EX 21%nat ltac:(lia)) as X21. pose proof (EX 22%nat ltac:(lia)) as X22. pose proof (EX 23%nat ltac:(lia)) as X23.
pose proof (EX 24%nat ltac:(lia)) as X24. pose proof (EX 25%nat ltac:(lia)) as X25. pose proof (EX 26%nat ltac:(lia)) as X26.
pose proof (EX 27%nat ltac:(lia)) as X27. pose proof (EX 28%nat ltac:(lia)) as X28. pose proof (EX 29%nat ltac:(lia)) as X29.
pose proof (EX 30%nat ltac:(lia)) as X30.
cbn [Nat.add] in X0, X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11, X12, X13, X14, X15, X16, X17, X18, X19, X20,
  X21, X22, X23, X24, X25, X26, X27, X28, X29, X30.
pose proof (bu_range fb 0) as B0. pose proof (bu_range fb 1) as B1. pose proof (bu_range fb 2) as B2.
pose proof (bu_range fb 3) as B3. pose proof (bu_range fb 4) as B4. pose proof (bu_range fb 5) as B5.
pose proof (bu_range fb 6) as B6. pose proof (bu_range fb 7) as B7. pose proof (bu_range fb 8) as B8.
pose proof (bu_range fb 9) as B9. pose proof (bu_range fb 10) as B10. pose proof (bu_range fb 11) as B11.
pose proof (bu_range fb 12) as B12. pose proof (bu_range fb 13) as B13. pose proof (bu_range fb 14) as B14.
pose proof (bu_range fb 15) as B15. pose proof (bu_range fb 16) as B16. pose proof (bu_range fb 17) as B17.
pose proof (bu_range fb 18) as B18. pose proof (bu_range fb 19) as B19. pose proof (bu_range fb 20) as B20.
pose proof (bu_range fb 21) as B21. pose proof (bu_range fb 22) as B22. pose proof (bu_range fb 23) as B23.
pose proof (bu_range fb 24) as B24. pose proof (bu_range fb 25) as B25. pose proof (bu_range fb 26) as B26.
pose proof (bu_range fb 27) as B27. pose proof (bu_range fb 28) as B28. pose proof (bu_range fb 29) as B29.
pose proof (bu_range fb 30) as B30.
clear HE.
(* q's metadata, for the 32 checks *)
assert (SHOK : sh_ok SEGS BX SH_S E (mrestrict (w_H W) mem)).
{ unfold sh_ok, SH_S. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart, BX. cbn [she_m she_lo she_hi].
  rewrite (U_atom E 32 SB E32) by (unfold SB; lia).
  rewrite (U_atom E 10 q E10) by lia.
  split.
  - rewrite <- (aview_rd_of SEGS). rewrite SB_SHADOW_OFF. replace (q + 0) with q by lia. exact HRA.
  - intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB, STAMP_LEN in *. lia. }
unfold cfg_at, A_reac_ctrl_block_cksum_stampP.
change (w64 (BASE + AF_reac_ctrl_block_cksum_stamp)) with (Z_to_bv 64 (BASE + AF_reac_ctrl_block_cksum_stamp)).
(* 0x83930..0x839d4: the whole function in one run: the frame, the K load, 31 passes of the loop
   (guards decided from q's pointer fact, checks from q's marks), the guard and check of q + 31, the
   store, the epilogue; it stops at the ret. *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat o);
    [reflexivity | exact Usp | cbn; unfold STAMP_FRAME in *; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat q); [reflexivity | exact Uq | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right; right; right. exists cid, pos. split; [exact Hown|].
  left. unfold in_zr. cbn [fst snd]. unfold STAMP_LEN in *. lia. }
(* at the ret: the checksum byte *)
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) |- _ =>
  let rf := eval vm_compute in (nth_error (ss_mem ssx) 3) in
  lazymatch rf with Some ?RF =>
    pose proof (st_ok_pi_region_nth Ex ssx _ 3 RF HS eq_refl) as HRF;
    let c0 := eval vm_compute in (hd_error (YP09.r_chunks RF)) in
    lazymatch c0 with Some (YP09.mkChunk 31 (CVal 1 ?v)) =>
      pose proof (field_of_region_any Ex _ 10%nat q _ _ _ _ _ 31 1%N v HRF
        ltac:(tenv; exact Uq) ltac:(left; reflexivity) ltac:(cbn; lia)) as HV31;
      change (bv_unsigned (sv_denot Ex v)) with (U Ex v) in HV31;
      let HUv := fresh "HUv" in
      eassert (HUv : U Ex v = _) by ueval_t;
      rewrite HUv in HV31; change (2 ^ (8 * Z.of_N 1)) with 256 in HV31; cbn [ms_mem restrict] in HV31;
      rewrite (stamp_cks fb) in HV31 by first [exact Hlen | (unfold fsum31; lia)]
    end
  end
end.
(* the return and the post *)
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) |- _ =>
  let R1 := fresh "R1" in
  prreg HS (1%bv : bv 5) R1;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros mat';
  unfold treac_ctrl_block_cksum_stamp_post; split; [reflexivity|];
  exists (ms_regs msc), (ms_mem msc); eexists;
  split; [cbn [ms_regs]; rewrite R1; tenv; rewrite (ER 1%bv 1%nat eq_refl ltac:(lia)); rewrite Hra; reflexivity|];
  split; [apply (ajournal_materialize (SK := SK) SEGS B LAWS Hsegs); exact HJ|];
  split;
  [ intros r Hr; destruct (stamp_kept_regs r Hr) as [-> | Hk];
    [ let R0 := fresh "R0" in let R00 := fresh "R00" in
      prreg HS (0%bv : bv 5) R0; prreg HS0 (0%bv : bv 5) R00; rewrite R0, R00; reflexivity
    | pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msc) regs (stamp_extra fb) STAMP_KEPT HS) as HK;
      cbn [ms_regs restrict] in HK; apply HK; [ | vm_compute; reflexivity | exact Hk ];
      first
      [ exact HAE
      | split;
        [ intros n0 Hn0; rewrite ?ew_ewset_other by lia; apply EL; unfold A_TEXT; lia
        | rewrite ?ed_ewset; exact (proj2 HAE) ] ] ]
  |];
  split;
  [ intros a Ha Hw Hn; apply (aview_eq_of SEGS); apply HFr; rewrite unsigned_lit_small by lia;
    intros (r & Hin & Har); cbn [ss_S ss_mem In] in Hin;
    destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    cbn [stack_region got_regionP bcell_regionP RQ YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Har;
    [ rewrite Usp in Har; apply Hw; rewrite Hsp; unfold STAMP_FRAME in *; lia
    | lia
    | lia
    | rewrite Uq in Har; apply Hn; unfold STAMP_LEN in *; lia ]
  |];
  split; [intros a Ha; eapply apresent_grows; [exact HG | exact Ha]|];
  apply (val_mem1_aview SEGS); [apply Z.mod_pos_bound; lia | exact HV31]
end.
Qed.

End h.
End f.
End d.
