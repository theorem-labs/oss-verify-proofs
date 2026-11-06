(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 615 of its 656 lines of code are new or changed and 412 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s22e.v, with its module names changed; 748 of its 838 lines of code are new or changed and 566 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): the kit of segment S15 of the
   walk of the test harness's entry function LLVMFuzzerTestOneInput (0x85ac4 .. 0x85b8c, the latch 0x859c4 ..
   0x859f8 and the table-full exit 0x85d44 .. 0x85d68; _s23, LLVMFuzzerTestOneInput_s23.v proves
   lt_seg_S15_stmt with it). No run of the code is proved here: the model of the inlined m_declared turn, the bytes
   of the VLAN table entries the turn reads and writes, the facts kept across a memory change, the seed of the
   segment's symbolic states, and (Section w) the segment's internal points with the shared facts every piece of
   the segment's proof uses at its end (s23_ctx_num, s23_ctx_slots, s23_end). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00 YG0q.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB PaArt PaLibF SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ============================== the model of one turn of the inlined m_declared ============================== *)
(* the duplicate test of fuzz_segconf.c:361-363 for the entry (p, v), as SegModel.m_decl_go states it *)
Definition s23_dup (p : list Z) (v : Z) (e : list Z * Z) : bool := (snd e =? v) && (SegModel.strcmp (fst e) p =? 0).

(* the counter never goes below its start except by the -1 of a full table *)
Lemma s23_decl_fst : forall l tab cap a, 0 <= a ->
  fst (SegModel.m_decl_go l tab cap a) = -1 \/ a <= fst (SegModel.m_decl_go l tab cap a).
Proof.
induction l as [|g l IH]; intros tab cap a Ha; cbn [SegModel.m_decl_go]; [right; cbn; lia|].
destruct (SegModel.ms_ignore g); [apply IH, Ha|].
destruct (SegModel.m_split (SegModel.ms_name g)) as [[p v]|]; [|apply IH, Ha].
destruct (existsb _ tab); [apply IH, Ha|].
destruct (cap <=? Z.of_nat (length tab)); [left; reflexivity|].
destruct (IH (tab ++ [(p, v)]) cap (a + 1) ltac:(lia)) as [E|E]; [left; exact E | right; lia].
Qed.
(* a prefix that has not failed: the rest of the list runs from its result *)
Lemma s23_decl_app : forall l r tab cap a, 0 <= a -> 0 <= fst (SegModel.m_decl_go l tab cap a) ->
  SegModel.m_decl_go (l ++ r) tab cap a =
  SegModel.m_decl_go r (snd (SegModel.m_decl_go l tab cap a)) cap (fst (SegModel.m_decl_go l tab cap a)).
Proof.
induction l as [|g l IH]; intros r tab cap a Ha Hf; cbn [app SegModel.m_decl_go]; [reflexivity|].
cbn [SegModel.m_decl_go] in Hf.
destruct (SegModel.ms_ignore g); [exact (IH r tab cap a Ha Hf)|].
destruct (SegModel.m_split (SegModel.ms_name g)) as [[p v]|]; [|exact (IH r tab cap a Ha Hf)].
destruct (existsb _ tab); [exact (IH r tab cap a Ha Hf)|].
destruct (cap <=? Z.of_nat (length tab)); [cbn in Hf; lia|].
exact (IH r (tab ++ [(p, v)]) cap (a + 1) ltac:(lia) Hf).
Qed.
(* a prefix that has failed: the whole list fails with it *)
Lemma s23_decl_app_fail : forall l r tab cap a, 0 <= a -> fst (SegModel.m_decl_go l tab cap a) < 0 ->
  SegModel.m_decl_go (l ++ r) tab cap a = SegModel.m_decl_go l tab cap a.
Proof.
induction l as [|g l IH]; intros r tab cap a Ha Hf; cbn [app SegModel.m_decl_go] in *; [cbn in Hf; lia|].
destruct (SegModel.ms_ignore g); [exact (IH r tab cap a Ha Hf)|].
destruct (SegModel.m_split (SegModel.ms_name g)) as [[p v]|]; [|exact (IH r tab cap a Ha Hf)].
destruct (existsb _ tab); [exact (IH r tab cap a Ha Hf)|].
destruct (cap <=? Z.of_nat (length tab)); [reflexivity|].
exact (IH r (tab ++ [(p, v)]) cap (a + 1) ltac:(lia) Hf).
Qed.
Lemma s23_firstn_S : forall {A} (l : list A) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
intros A l. induction l as [|x l IH]; intros [|i] d Hi; cbn [length] in Hi; try lia; [reflexivity|].
cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.
(* turn i of the inlined m_declared, for a segment that is not ignored and whose name splits into (p, v) *)
Lemma s23_decl_step : forall (sg : list SegModel.mseg) tab0 cap i p v,
  (i < length sg)%nat -> SegModel.ms_ignore (nth i sg SegModel.mseg_d) = false ->
  SegModel.m_split (SegModel.ms_name (nth i sg SegModel.mseg_d)) = Some (p, v) ->
  0 <= fst (SegModel.m_decl_go (firstn i sg) tab0 cap 0) ->
  SegModel.m_decl_go (firstn (S i) sg) tab0 cap 0 =
  (let a := fst (SegModel.m_decl_go (firstn i sg) tab0 cap 0) in
   let t := snd (SegModel.m_decl_go (firstn i sg) tab0 cap 0) in
   if existsb (s23_dup p v) t then (a, t)
   else if cap <=? Z.of_nat (length t) then (-1, t) else (a + 1, t ++ [(p, v)])).
Proof.
intros sg tab0 cap i p v Hi Hig Hsp Ha.
rewrite (s23_firstn_S sg i SegModel.mseg_d Hi).
rewrite (s23_decl_app _ _ tab0 cap 0 ltac:(lia) Ha). cbn [SegModel.m_decl_go]. rewrite Hig, Hsp. cbv zeta.
unfold s23_dup. destruct (existsb _ _); [reflexivity|].
destruct (cap <=? _); [reflexivity | reflexivity].
Qed.
(* the full table at turn i: the whole m_declared answers -1 with the table of turn i *)
Lemma s23_decl_full : forall (sg : list SegModel.mseg) tab0 cap i,
  (i <= length sg)%nat -> fst (SegModel.m_decl_go (firstn i sg) tab0 cap 0) < 0 ->
  SegModel.m_decl_go sg tab0 cap 0 = SegModel.m_decl_go (firstn i sg) tab0 cap 0.
Proof.
intros sg tab0 cap i Hi Hf. rewrite <- (firstn_skipn i sg) at 1. apply s23_decl_app_fail; [lia | exact Hf].
Qed.
(* the duplicate scan over the first j entries, one entry at a time *)
Lemma s23_existsb_S : forall f (t : list (list Z * Z)) j, (j < length t)%nat ->
  existsb f (firstn (S j) t) = existsb f (firstn j t) || f (nth j t ([], 0)).
Proof.
intros f t j Hj. rewrite (s23_firstn_S t j ([], 0) Hj), existsb_app. cbn [existsb]. rewrite orb_false_r. reflexivity.
Qed.
(* m_split's vid is in [1, 4094] and its parent is a prefix of the name *)
Lemma s23_digits_le : forall l v0 v, 0 <= v0 <= 4094 -> SegModel.m_digits l v0 = Some v -> 0 <= v <= 4094.
Proof.
induction l as [|q l IH]; intros v0 v Hv0 H; cbn [SegModel.m_digits] in H; [injection H as <-; exact Hv0|].
destruct ((q <? 48) || (57 <? q)) eqn:Eq; [discriminate|].
apply orb_false_iff in Eq as [E1 E2]. apply Z.ltb_ge in E1. apply Z.ltb_ge in E2.
destruct (4094 <? v0 * 10 + (q - 48)) eqn:E3; [discriminate|]. apply Z.ltb_ge in E3.
exact (IH (v0 * 10 + (q - 48)) v ltac:(lia) H).
Qed.
Lemma s23_split_props : forall name p v, SegModel.m_split name = Some (p, v) ->
  1 <= v <= 4094 /\ (length p <= length name)%nat /\ exists di, p = firstn di name.
Proof.
intros name p v H. unfold SegModel.m_split in H.
destruct (SegModel.strrchr name SegModel.DOT) as [di|]; [|discriminate].
destruct ((di =? 0)%nat || (SegModel.hd0 (skipn (S di) name) =? 0)); [discriminate|].
destruct (SegModel.m_digits (skipn (S di) name) 0) as [vd|] eqn:Ed; [|discriminate].
destruct (vd <? 1) eqn:E1; [discriminate|]. apply Z.ltb_ge in E1.
destruct (forallb SegModel.h_parent_ok (firstn di name)); [|discriminate].
injection H as <- <-. pose proof (s23_digits_le _ 0 vd ltac:(lia) Ed).
split; [lia|]. split; [rewrite length_firstn; lia | exists di; reflexivity].
Qed.
(* the model's strcmp test of two NUL-free texts is their equality *)
Lemma s23_strcmp0 : forall a b, SegModel.nulfree a -> SegModel.nulfree b ->
  (SegModel.strcmp a b =? 0) = true <-> a = b.
Proof. intros a b Ha Hb. rewrite (SegModel.strcmp_eq a b Ha Hb). apply SegModel.leqb_eq. Qed.

(* ================================ facts of the symbolic engine's values ================================ *)
Lemma s23_br_ge : forall E a b, U E a < 2 ^ 63 -> U E b < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = (U E b <=? U E a).
Proof.
intros E a b Ha Hb. cbn [branch_taken]. unfold bv_lts. unfold U in *.
rewrite !bv_signed_small by assumption. rewrite Z.leb_antisym. reflexivity.
Qed.
Lemma s23_br_lt : forall E a b, U E a < 2 ^ 63 -> U E b < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof. intros E a b Ha Hb. cbn [branch_taken]. unfold bv_lts. unfold U in *. rewrite !bv_signed_small by assumption. reflexivity. Qed.
Lemma s23_reg_keep : forall (regs regs0 : bvmap 5 word) (rr : bv 5) E (n : nat),
  getr regs rr = sv_denot E (SOff n 0) -> ew E n = getr regs0 rr -> getr regs rr = getr regs0 rr.
Proof. intros regs regs0 rr E n H Hn. rewrite H. cbn [sv_denot]. rewrite Hn, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma s23_reg_U : forall (regs : bvmap 5 word) (rr : bv 5) E e v,
  getr regs rr = sv_denot E e -> U E e = v -> getr regs rr = w64 v.
Proof. intros regs rr E e v H HU. rewrite H. unfold w64. rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma s23_rdword_range : forall segs H mem a v, rdword (aview segs H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros segs H mem a v Hw. unfold rdword in Hw.
repeat match type of Hw with context [aview segs H mem ?x] =>
  let E := fresh "E" in destruct (aview segs H mem x) as [?b|] eqn:E;
  [pose proof (sa_aview_rng _ _ _ _ _ E) | cbn in Hw; discriminate] end.
cbn in Hw. injection Hw as <-. lia.
Qed.
(* a run that writes nothing leaves every byte a reader sees *)
Lemma s23_ro_kept : forall segs E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> rs_read_only rs = true ->
  forall a, aview segs H m' a = aview segs H m a.
Proof. intros segs E rs H m m' HF Hro a. unfold aview. rewrite (frame_of_read_only E rs _ _ Hro HF). reflexivity. Qed.

(* ================================ the bytes of the VLAN table entries ================================ *)
Lemma s23_nth_fld : forall (bs : list byte) off n k d, (k < n)%nat ->
  nth k (seg_spec.fld off n bs) d = nth (off + k) bs d.
Proof.
intros bs off n k d Hk. unfold seg_spec.fld. rewrite nth_firstn. destruct (k <? n)%nat eqn:E; [|apply Nat.ltb_ge in E; lia].
rewrite nth_skipn. reflexivity.
Qed.
Lemma s23_length_fld : forall (bs : list byte) off n, (off + n <= length bs)%nat -> length (seg_spec.fld off n bs) = n.
Proof. intros bs off n H. unfold seg_spec.fld. rewrite length_firstn, length_skipn. lia. Qed.
Lemma s23_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold Mem.le4. rewrite unsigned_lit_small by lia. unfold le_byte.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small v (2 ^ 32)) by lia.
destruct k as [|[|[|[|k]]]]; [| | | |lia]; cbn [Z_to_le_bytes nth]; rewrite Z_to_bv_unsigned; unfold bv_wrap;
  change (bv_modulus 8) with 256; f_equal; rewrite ?Z.shiftr_shiftr by lia; reflexivity.
Qed.
(* the entry j of a model table: its parent as a C string, its vid as an unsigned word *)
Lemma s23_mtab_entry : forall (rd : reader) mt t j, sa_mtab rd mt t -> (j < length t)%nat ->
  sa_zs rd (mt + 20 * Z.of_nat j) (fst (nth j t ([], 0)) ++ [0]) /\ ~ In 0 (fst (nth j t ([], 0))) /\
  (length (fst (nth j t ([], 0%Z))) < 16)%nat /\ 0 <= snd (nth j t ([], 0)) < 2 ^ 32 /\
  sa_val rd (mt + 20 * Z.of_nat j + 16) 4 (snd (nth j t ([], 0))).
Proof.
intros rd mt t j (bs & Hb & Hlen & Henc) Hj.
destruct (Henc j Hj) as (Hfl & (Hl16 & Hlt & Hn0 & Hpre) & (Hv & Hle)).
set (e := nth j t ([], 0)) in *. set (f := seg_spec.fld (20 * j) 20 bs) in *.
assert (HB : forall k, (k < 20)%nat -> rd (mt + 20 * Z.of_nat j + Z.of_nat k) = Some (bv_unsigned (nth k f ZB0))).
{ intros k Hk. subst f. rewrite s23_nth_fld by exact Hk.
  replace (mt + 20 * Z.of_nat j + Z.of_nat k) with (mt + Z.of_nat (20 * j + k)) by lia. apply Hb. lia. }
split; [|split; [exact Hn0 | split; [exact Hlt | split; [exact Hv|]]]].
- intros k Hk. rewrite length_app in Hk. cbn [length] in Hk.
  rewrite HB by lia. f_equal. rewrite <- Hpre. rewrite nth_firstn.
  destruct (k <? S (length (fst e)))%nat eqn:E; [|apply Nat.ltb_ge in E; lia].
  unfold seg_spec.zs. rewrite (nth_indep (map bv_unsigned (seg_spec.fld 0 16 f)) 0 (bv_unsigned ZB0))
    by (rewrite length_map, (s23_length_fld f 0 16) by lia; lia).
  rewrite map_nth, s23_nth_fld by lia. reflexivity.
- intros k Hk. replace (mt + 20 * Z.of_nat j + 16 + Z.of_nat k) with (mt + 20 * Z.of_nat j + Z.of_nat (16 + k)) by lia.
  rewrite HB by lia. f_equal. rewrite <- (s23_nth_fld f 16 4 k ZB0 Hk). rewrite Hle. apply s23_le4_byte; [exact Hv | exact Hk].
Qed.
(* n mapped bytes of a reader of the machine are a byte list *)
Lemma s23_bytes_of_rd : forall segs H mem a n,
  (forall i, 0 <= i < Z.of_nat n -> aview segs H mem (a + i) <> None) ->
  exists bs, length bs = n /\ sa_bytes (aview segs H mem) a bs.
Proof.
intros segs H mem a n. revert a. induction n as [|n IH]; intros a Hv.
- exists []. split; [reflexivity | intros i Hi; cbn in Hi; lia].
- destruct (aview segs H mem a) as [z|] eqn:Ez; [|exfalso; apply (Hv 0 ltac:(lia)); rewrite Z.add_0_r; exact Ez].
  destruct (IH (a + 1)) as (bs & Hl & Hb).
  { intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply Hv. lia. }
  exists (Z_to_bv 8 z :: bs). split; [cbn; lia|].
  intros [|i] Hi; cbn [nth].
  + rewrite Z.add_0_r, Ez. f_equal. pose proof (sa_aview_rng _ _ _ _ _ Ez) as R.
    rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
  + cbn [length] in Hi. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply Hb. lia.
Qed.
(* the struct mvlan v (parent[16] at +0, vid at +16) as an entry of the model's table *)
Lemma s23_mvlan_of : forall (rd : reader) v par vid f,
  sa_strz rd v par -> (length par < 16)%nat -> sa_val rd (v + 16) 4 vid -> 0 <= vid < 2 ^ 32 ->
  length f = 20%nat -> sa_bytes rd v f -> seg_spec.mvlan_enc (par, vid) f.
Proof.
intros rd v par vid f (Hz & Hn0) Hl Hv Hvr Hfl Hb. split; [exact Hfl|]. cbn [fst snd].
assert (HF : forall k, (k < 20)%nat -> rd (v + Z.of_nat k) = Some (bv_unsigned (nth k f ZB0))) by (intros k Hk; apply Hb; lia).
split; [split; [|split; [exact Hl | split; [exact Hn0|]]]|].
- apply s23_length_fld. lia.
- apply (nth_ext _ _ 0 0).
  + rewrite length_firstn, length_app. unfold seg_spec.zs. rewrite length_map, (s23_length_fld f 0 16) by lia.
    cbn [length]. lia.
  + intros k Hk. rewrite length_firstn in Hk. unfold seg_spec.zs in Hk |- *.
    rewrite length_map, (s23_length_fld f 0 16) in Hk by lia.
    rewrite nth_firstn. destruct (k <? S (length par))%nat eqn:E; [|apply Nat.ltb_ge in E; lia].
    rewrite (nth_indep (map bv_unsigned (seg_spec.fld 0 16 f)) 0 (bv_unsigned ZB0))
      by (rewrite length_map, (s23_length_fld f 0 16) by lia; lia).
    rewrite map_nth, s23_nth_fld by lia. cbn [Nat.add].
    assert (Hk' : (k < length (par ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
    pose proof (Hz k Hk') as H1. rewrite HF in H1 by lia. injection H1 as H1. exact H1.
- split; [exact Hvr|]. apply (nth_ext _ _ ZB0 ZB0).
  + rewrite (s23_length_fld f 16 4) by lia. unfold Mem.le4. rewrite length_Z_to_le_bytes. reflexivity.
  + intros k Hk. rewrite (s23_length_fld f 16 4) in Hk by lia. apply bv_eq.
    rewrite s23_le4_byte by lia. rewrite s23_nth_fld by lia.
    pose proof (Hv k Hk) as H1. replace (v + 16 + Z.of_nat k) with (v + Z.of_nat (16 + k)) in H1 by lia.
    rewrite HF in H1 by lia.
    injection H1 as H1. exact H1.
Qed.
(* the model's table grown by one entry: the old entries kept, the new entry's 20 bytes written after them *)
Lemma s23_mtab_snoc : forall (rd rd' : reader) mt t e f,
  sa_mtab rd mt t -> (forall i, 0 <= i < 20 * Z.of_nat (length t) -> rd' (mt + i) = rd (mt + i)) ->
  length f = 20%nat -> sa_bytes rd' (mt + 20 * Z.of_nat (length t)) f -> seg_spec.mvlan_enc e f ->
  sa_mtab rd' mt (t ++ [e]).
Proof.
intros rd rd' mt t e f (bs & Hb & Hlen & Henc) Hk Hfl Hf He.
exists (bs ++ f). split; [|split].
- intros i Hi. rewrite length_app in Hi.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi1|Hi1].
  + rewrite app_nth1 by exact Hi1. rewrite Hk by lia. apply Hb. exact Hi1.
  + rewrite app_nth2 by exact Hi1. replace (mt + Z.of_nat i) with (mt + 20 * Z.of_nat (length t) + Z.of_nat (i - length bs)) by lia.
    apply Hf. lia.
- rewrite !length_app. cbn [length]. lia.
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.lt_ge_cases i (length t)) as [Hi1|Hi1].
  + rewrite app_nth1 by exact Hi1. replace (seg_spec.fld (20 * i) 20 (bs ++ f)) with (seg_spec.fld (20 * i) 20 bs).
    * apply Henc. exact Hi1.
    * unfold seg_spec.fld. rewrite skipn_app. replace (20 * i - length bs)%nat with 0%nat by lia. cbn [skipn].
      rewrite firstn_app. rewrite length_skipn. replace (20 - (length bs - 20 * i))%nat with 0%nat by lia.
      cbn [firstn]. rewrite app_nil_r. reflexivity.
  + assert (i = length t) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    replace (seg_spec.fld (20 * length t) 20 (bs ++ f)) with f; [exact He|].
    unfold seg_spec.fld. rewrite skipn_app, (skipn_all2 bs) by lia.
    replace (20 * length t - length bs)%nat with 0%nat by lia. rewrite skipn_O, app_nil_l.
    symmetry. apply firstn_all2. lia.
Qed.
(* m->n, the 4-byte count at m + 0x2000 the latch loads *)
Lemma s23_mconf_n : forall (rd : reader) m mc, sa_mconf rd m mc ->
  sa_val rd (m + seg_spec.MC_N) 4 (Z.of_nat (length (SegModel.mc_seg mc))) /\ (length (SegModel.mc_seg mc) <= 32)%nat.
Proof.
intros rd m mc (bs & Hb & Hl & H32 & _ & (Hv & Hle) & _).
split; [|exact H32]. intros k Hk.
unfold seg_spec.fldz, seg_spec.MC_N in Hle. change (Z.to_nat 4) with 4%nat in Hle.
unfold seg_spec.MC_N.
replace (m + 0x2000 + Z.of_nat k) with (m + Z.of_nat (Z.to_nat 0x2000 + k)) by (rewrite Nat2Z.inj_add, Z2Nat.id by lia; lia).
assert (Hk2 : (Z.to_nat 0x2000 + k < length bs)%nat).
{ apply Nat2Z.inj_lt. rewrite Nat2Z.inj_add, Z2Nat.id by lia. unfold seg_spec.SEG_M_SIZE in Hl. lia. }
rewrite (Hb _ Hk2).
f_equal. rewrite <- (s23_nth_fld bs (Z.to_nat 0x2000) 4 k ZB0 Hk). rewrite Hle. apply s23_le4_byte; [lia | exact Hk].
Qed.
(* a field read through the world's view is the same field of the restricted memory *)
Lemma s23_val_mem_of : forall segs H (mem : word -> option byte) a n v,
  sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.

(* ===================================== facts kept across a memory change ===================================== *)
(* rd' agrees with rd on [a, a + n) *)
Definition s23_kept (rd rd' : reader) (a n : Z) : Prop := forall x, a <= x < a + n -> rd' x = rd x.
Lemma s23_kept_sub : forall rd rd' a n b m, s23_kept rd rd' a n -> a <= b -> b + m <= a + n -> s23_kept rd rd' b m.
Proof. intros rd rd' a n b m H H1 H2 x Hx. apply H. lia. Qed.
Lemma s23_kept_bytes : forall rd rd' a bs, s23_kept rd rd' a (Z.of_nat (length bs)) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs HK H i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma s23_kept_zs : forall rd rd' a l, s23_kept rd rd' a (Z.of_nat (length l)) -> sa_zs rd a l -> sa_zs rd' a l.
Proof. intros rd rd' a l HK H i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma s23_kept_val : forall rd rd' a n v, s23_kept rd rd' a (Z.of_nat n) -> sa_val rd a n v -> sa_val rd' a n v.
Proof. intros rd rd' a n v HK H i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma s23_kept_word : forall rd rd' a v, s23_kept rd rd' a 8 -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.
Lemma s23_kept_strz : forall rd rd' p s, s23_kept rd rd' p (Z.of_nat (length s) + 1) -> sa_strz rd p s -> sa_strz rd' p s.
Proof.
intros rd rd' p s HK [H1 H2]. split; [|exact H2]. apply (s23_kept_zs rd); [|exact H1].
rewrite length_app. cbn [length]. intros x Hx. apply HK. lia.
Qed.
Lemma s23_kept_rconf : forall rd rd' c r, s23_kept rd rd' c seg_spec.SEG_C_SIZE -> sa_rconf rd c r -> sa_rconf rd' c r.
Proof.
intros rd rd' c r HK (bs & Hb & He). exists bs. split; [|exact He].
apply (s23_kept_bytes rd); [|exact Hb]. destruct He as (Hl & _). rewrite Hl. exact HK.
Qed.
Lemma s23_kept_mconf : forall rd rd' m r, s23_kept rd rd' m seg_spec.SEG_M_SIZE -> sa_mconf rd m r -> sa_mconf rd' m r.
Proof.
intros rd rd' m r HK (bs & Hb & He). exists bs. split; [|exact He].
apply (s23_kept_bytes rd); [|exact Hb]. destruct He as (Hl & _). rewrite Hl. exact HK.
Qed.
Lemma s23_kept_rtab : forall rd rd' a t, s23_kept rd rd' a (18 * Z.of_nat (length t)) -> sa_rtab rd a t -> sa_rtab rd' a t.
Proof.
intros rd rd' a t HK (bs & Hb & He). exists bs. split; [|exact He].
apply (s23_kept_bytes rd); [|exact Hb]. destruct He as (Hl & _). rewrite Hl. intros x Hx. apply HK. lia.
Qed.
Lemma s23_kept_mtab : forall rd rd' a t, s23_kept rd rd' a (20 * Z.of_nat (length t)) -> sa_mtab rd a t -> sa_mtab rd' a t.
Proof.
intros rd rd' a t HK (bs & Hb & He). exists bs. split; [|exact He].
apply (s23_kept_bytes rd); [|exact Hb]. destruct He as (Hl & _). rewrite Hl. intros x Hx. apply HK. lia.
Qed.
Lemma s23_kept_guard : forall rd rd' tab cap, s23_kept rd rd' (tab + seg_spec.RVLAN_SIZE * cap) 18 ->
  sa_guardtab rd tab cap -> sa_guardtab rd' tab cap.
Proof. intros rd rd' tab cap HK H. apply (s23_kept_bytes rd); [exact HK | exact H]. Qed.
Lemma s23_pairwise_NoDup : forall (l : list (Z * Z)), (forall x, In x l -> 0 < snd x) -> pairwise zdisjoint l -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hp Hpw; [constructor|]. destruct Hpw as [Hf Hpw].
constructor; [|apply IH; [intros y Hy; apply Hp; right; exact Hy | exact Hpw]].
intros Hin. rewrite Forall_forall in Hf. pose proof (Hf x Hin) as Hd. pose proof (Hp x (or_introl eq_refl)).
unfold zdisjoint in Hd. lia.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.

Lemma s23_ablocks_NoDup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
destruct (ablocks B ly S) as [|[p0 n0] bl] eqn:Eb; [constructor|].
assert (Hin0 : In (p0, n0) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR Hin0) as (_ & _ & _ & _ & _ & Hpw & _).
rewrite <- Eb. apply (List.NoDup_map_inv (fun b : Z * Z => (fst b, req_size (snd b)))).
apply s23_pairwise_NoDup; [|exact Hpw].
intros [a q] Hx. apply in_map_iff in Hx as ([pb nb] & Hq & Hpb). cbn in Hq. injection Hq as <- <-.
destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR Hpb) as (_ & _ & _ & _ & _ & _ & Hn).
cbn [snd]. pose proof (req_size_pos nb ltac:(lia)). lia.
Qed.
(* a live heap block of the state, with the allocator law's bounds *)
Definition s23_blk ly S (b n : Z) : Prop :=
  In (b, n) (ablocks B ly S) /\ 4096 <= b /\ b mod 16 = 0 /\ b + n <= alloc_ceiling /\ in_app b n.
Lemma s23_blk_of : forall ly S (W : world SEGS) mem md b n, AR SEGS B ly S W mem md -> 0 < n ->
  lt_hblk B ly S (rdW W mem) b n -> s23_blk ly S b n.
Proof.
intros ly S W mem md b n HAR Hn (Hin & H4 & H16 & _).
destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hin) as (_ & _ & Hc & Ha & _).
unfold req_size in Hc, Ha. destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia|].
split; [exact Hin|]. split; [exact H4|]. split; [exact H16|]. split; [exact Hc | exact Ha].
Qed.
(* a live block's lt_hblk at any state of the allocator record that holds it *)
Lemma s23_hblk_of : forall ly S (W : world SEGS) mem md b n, AR SEGS B ly S W mem md -> 0 < n ->
  s23_blk ly S b n -> lt_hblk B ly S (rdW W mem) b n.
Proof.
intros ly S W mem md b n HAR Hn (Hin & H4 & H16 & Hc & Ha).
assert (Hr : req_size n = n) by (unfold req_size; destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]).
pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md b n b n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md b n b n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hp. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md b n b n HAR Hin ltac:(lia) ltac:(lia) Hp).
Qed.
(* the frame's shadow with v out of scope: its three bytes 0xf8, every other byte as with v in scope *)
Lemma s23_fsh_N : forall (rd rd' : reader) sh,
  sa_zs rd sh (lt_fsh LFO_NV) -> (forall j, 4 <= j < 7 -> rd' (sh + j) = Some 0xf8) ->
  (forall j, 0 <= j < 36 -> ~ (4 <= j < 7) -> rd' (sh + j) = rd (sh + j)) ->
  sa_zs rd' sh (lt_fsh LFO_N).
Proof.
intros rd rd' sh H Hf Hk j Hj. rewrite lt_fsh_len in Hj.
destruct (Z_lt_le_dec (Z.of_nat j) 4) as [H4|H4]; [|destruct (Z_lt_le_dec (Z.of_nat j) 7) as [H7|H7]].
- rewrite Hk by lia. rewrite (H j) by (rewrite lt_fsh_len; exact Hj). f_equal.
  do 4 (destruct j as [|j]; [reflexivity|]). lia.
- rewrite Hf by lia. do 7 (destruct j as [|j]; [cbn in H4, H7; try lia; reflexivity|]). lia.
- rewrite Hk by lia. rewrite (H j) by (rewrite lt_fsh_len; exact Hj). f_equal.
  do 36 (destruct j as [|j]; [cbn in H4, H7; try lia; reflexivity|]). lia.
Qed.

(* the numbers of the entry's frame at a point of the walk: the entry sp, the realigned s1, the class-3 frame *)
Lemma s23_layout : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 352 < x_s1 cx <= x_sp0 cx - 320 /\ spZ regs = x_s1 cx /\
  frames S = [(LT_FCLS, x_fpos cx)] /\ frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx /\
  x_fr cx mod 64 = 0 /\ 4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512 /\
  fs_frame_bytes LT_FCLS = 512.
Proof.
intros cx ly S W regs mem md k o HB HF.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HF as (HJ & R2 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (EB : fs_frame_bytes LT_FCLS = 512) by reflexivity.
assert (Hs1 : x_s1 cx mod 32 = 0 /\ x_sp0 cx - 352 < x_s1 cx <= x_sp0 cx - 320).
{ unfold x_s1, LT_FRAME. pose proof (Z.mod_pos_bound (x_sp0 cx - 320) 32 ltac:(lia)).
  split; [|lia]. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
assert (HSP : alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47).
{ unfold x_sp0. unfold STK_LLVMFuzzerTestOneInput in Hslo. lia. }
assert (HFS : frames S = [(LT_FCLS, x_fpos cx)]) by (rewrite Hfrs, Hfr0; reflexivity).
assert (HFA : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ unfold x_fr, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite HFS; left; reflexivity).
destruct (frames_bounds _ _ LAWS ly S W mem md _ _ HAR Hin) as (F1 & F2 & F3).
destruct (frame_al64 _ _ ly S W mem md _ _ HAR Hin) as (F4 & _).
rewrite HFA, EB in *.
split; [exact Hal16|]. split; [exact HSP|]. split; [exact (proj1 Hs1)|]. split; [exact (proj2 Hs1)|].
split; [unfold spZ; rewrite R2; apply unsigned_lit_small; pose proof asan_consts as (C1 & _); lia|].
split; [exact HFS|]. split; [reflexivity|]. split; [exact F4|]. split; [exact F1|]. split; [exact F2|].
split; [exact F3 | reflexivity].
Qed.

(* a literal of the image is kept by a change that keeps the image's bytes; its tail is read from the image *)
Lemma s23_lit_kept : forall (W : world SEGS) mem mem' a s,
  (forall x, in_img SEGS x -> rdW W mem' x = rdW W mem x) ->
  sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W mem') a s.
Proof.
intros W mem mem' a s K (Hpos & (Hz & _) & Hpin & Hrt & Himg).
split; [exact Hpos|]. split; [split|split; [exact Hpin | split; [exact Hrt | exact Himg]]].
- apply (s23_kept_strz (rdW W mem)); [|exact Hz]. intros x Hx. apply K. exact (proj1 (Himg x Hx)).
- exact (sa_tail_of_romtail SEGS (w_H W) mem' _ Hrt).
Qed.
(* the image facts of a point are kept by a change that keeps every image byte *)
Lemma s23_img_kept : forall cx (W : world SEGS) mem mem',
  (forall a, 0x10000 <= a < kImgEnd -> rdW W mem' a = rdW W mem a) ->
  lt_img B cx (rdW W mem) -> lt_img B cx (rdW W mem').
Proof.
intros cx W mem mem' K (HRO & HIMG & HGI).
assert (KI : forall x, in_img SEGS x -> rdW W mem' x = rdW W mem x) by (intros x Hx; apply K; exact (pa_img_range x Hx)).
split; [|split].
- intros a Hro Hown Herr. rewrite K; [exact (HRO a Hro Hown Herr)|].
  destruct Hro as [(sg & Hs & _ & Hr) | Hr].
  + apply pa_img_range. exists sg. split; [exact Hs | exact Hr].
  + unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. unfold kImgEnd. lia.
- unfold seg_himg in HIMG |- *.
  destruct HIMG as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  split; [apply (s23_kept_val (rdW W mem)); [intros x Hx; apply KI; exact (proj1 (H2 x ltac:(lia))) | exact H1]|].
  split; [exact H2|].
  split; [intros s Hs; destruct (H3 s Hs) as [Hl Ha]; split; [exact (s23_lit_kept W mem mem' _ _ KI Hl) | exact Ha]|].
  split; [intros s Hs; destruct (H4 s Hs) as [Hl Ha]; split; [exact (s23_lit_kept W mem mem' _ _ KI Hl) | exact Ha]|].
  split.
  { destruct H5 as (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn. destruct (Hr i Hn) as (tp & Ht & Hl). exists tp. split.
    - apply (s23_kept_word (rdW W mem)); [|exact Ht]. intros x Hx. apply KI. refine (proj1 (Hi x _)).
      unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES in *. unfold pin_spec.CAT_N in Hn. lia.
    - exact (s23_lit_kept W mem mem' _ _ KI Hl). }
  split; [exact H6|].
  split.
  { destruct H7 as (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn. destruct (Hr i Hn) as (wp & Hw & Hl). exists wp. split.
    - apply (s23_kept_word (rdW W mem)); [|exact Hw]. intros x Hx. apply KI. refine (proj1 (Hi x _)). lia.
    - exact (s23_lit_kept W mem mem' _ _ KI Hl). }
  split.
  { destruct H8 as (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn. apply (s23_kept_val (rdW W mem)); [|exact (Hr i Hn)]. intros x Hx. apply KI. refine (proj1 (Hi x _)). lia. }
  split; [|exact H10]. destruct H9 as (Hg & g & Hg2). split.
  + apply (s23_kept_word (rdW W mem)); [|exact Hg]. intros x Hx. apply K. unfold gotwA, kImgEnd in *. lia.
  + exists g. apply (s23_kept_word (rdW W mem)); [|exact Hg2]. intros x Hx. apply K. unfold guardA, kImgEnd in *. lia.
- intros i Hi. rewrite K; [exact (HGI i Hi)|]. unfold longlA, A_LONGL, LONGL_W, kImgEnd in *. lia.
Qed.
(* the frame part of a point is kept by a change that keeps the saved registers, the frame's header and flag words
   and the shadow-base slot, given the frame's shadow at the new point *)
Lemma s23_frame_kept : forall cx ly S (W : world SEGS) regs mem md k o regs' mem' md' o',
  lt_frame B cx ly S W regs mem md k o ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  s23_kept (rdW W mem) (rdW W mem') (x_sp0 cx - 104) 104 ->
  s23_kept (rdW W mem) (rdW W mem') (x_fr cx) 24 -> s23_kept (rdW W mem) (rdW W mem') (x_fr cx + LT_FLAGW) 8 ->
  s23_kept (rdW W mem) (rdW W mem') (x_s1 cx + 176) 8 ->
  sa_zs (rdW W mem') (x_sh cx) (lt_fsh o') ->
  lt_frame B cx ly S W regs' mem' md' k o'.
Proof.
intros cx ly S W regs mem md k o regs' mem' md' o' HF HJ' E2 E3 E4 E8 E9 KS KH KW K176 Hsh.
destruct HF as (_ & R2 & R3 & R4 & R8 & R9 & HSV & H0 & H8 & H16 & HW & H176 & _).
split; [exact HJ'|]. rewrite E2, E3, E4, E8, E9.
split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
split.
{ intros i r Hi. pose proof (HSV i r Hi) as H. apply (s23_kept_word (rdW W mem)); [|exact H].
  assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  cbn [LT_SAVED length] in Hi13. apply (s23_kept_sub _ _ _ _ _ _ KS); lia. }
split; [apply (s23_kept_word (rdW W mem)); [apply (s23_kept_sub _ _ _ _ _ _ KH); lia | exact H0]|].
split; [apply (s23_kept_word (rdW W mem)); [apply (s23_kept_sub _ _ _ _ _ _ KH); lia | exact H8]|].
split; [apply (s23_kept_word (rdW W mem)); [apply (s23_kept_sub _ _ _ _ _ _ KH); lia | exact H16]|].
split; [apply (s23_kept_word (rdW W mem)); [exact KW | exact HW]|].
split; [apply (s23_kept_word (rdW W mem)); [exact K176 | exact H176]|].
exact Hsh.
Qed.

(* ============================== the symbolic states of the segment's runs ============================== *)
(* every register is its own atom; atoms 32 .. 39 are the slots' values cap, v = FR + 32, tab, mt, the entries
   added, the table's length, SH(FR) and m; a run may add atoms from 40 on *)
Definition s23_E (regs : bvmap 5 word) (vals : list Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) vals)).
Lemma s23_E_reg : forall regs vals n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (s23_E regs vals) n = getr regs r.
Proof.
intros regs vals n r Hr. pose proof (bv_unsigned_in_range 5 r) as R5. change (bv_modulus 5) with 32 in R5.
unfold s23_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr.
Qed.
Lemma s23_E_val : forall regs vals j, (32 + j < A_TEXT)%nat ->
  ew (s23_E regs vals) (32 + j) = Z_to_bv 64 (nth j vals 0).
Proof.
intros regs vals j Hj. unfold s23_E. rewrite Eimg_low by exact Hj. rewrite ew_Ereg_extra.
rewrite map_nth. reflexivity.
Qed.
Lemma s23_E_img : forall regs vals, img_env VAL A_LIM (s23_E regs vals).
Proof. intros regs vals. unfold s23_E. apply Eimg_env. Qed.
Lemma s23_E_agree : forall regs vals, env_agree 32 (Ereg regs (map (Z_to_bv 64) vals)) (s23_E regs vals).
Proof.
intros regs vals. split; [intros n Hn; unfold s23_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity].
Qed.
Lemma s23_denot_of_U : forall E e v, U E e = v -> 0 <= v < 2 ^ 64 -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H Hv. apply bv_eq. rewrite unsigned_lit_small by lia. exact H. Qed.
(* the shadow address the code keeps at 152(s1), computed from m's atom and the shadow base's *)
Definition shw (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff 15 0).
Lemma s23_U_shw : forall E (n : nat) c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 62 -> 0 <= c < 2 ^ 62 ->
  U E (SOff 15 0) = SHADOW_OFF -> U E (shw (SOff n c)) = shadow_addr (v + c).
Proof.
intros E n c v En Hv Hc H15. unfold shw. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c En) by lia. rewrite H15, U_lit by lia. change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_small ((v + c) / 8)) by (pose proof (Z.div_le_upper_bound (v + c) 8 (2 ^ 60)); lia).
unfold shadow_addr, SHADOW_OFF. rewrite Z.add_comm. apply zcanon_small.
pose proof (Z.div_le_upper_bound (v + c) 8 (2 ^ 60)). pose proof (Z.div_pos (v + c) 8). lia.
Qed.
(* the slots of the realigned frame the segment's runs read *)
Definition s1_chunks : list YP09.chunk :=
  [ YP09.mkChunk 32 (CVal 8 (SOff 32 0)); YP09.mkChunk 56 (CVal 8 (SOff 33 0)); YP09.mkChunk 88 (CVal 8 (SOff 34 0));
    YP09.mkChunk 96 (CVal 8 (SOff 35 16)); YP09.mkChunk 104 (CVal 8 (SOff 36 0)); YP09.mkChunk 112 (CVal 8 (SOff 35 0));
    YP09.mkChunk 120 (CVal 8 (SOff 37 0)); YP09.mkChunk 144 (CVal 8 (SOff 38 0));
    YP09.mkChunk 152 (CVal 8 (shw (SOff 39 0x2000))); YP09.mkChunk 168 (CVal 8 (SOff 39 0));
    YP09.mkChunk 176 (CVal 8 (SOff 15 0)); YP09.mkChunk 184 (CVal 8 (SOff 39 0x2000)) ].
Definition s1_region (wlo whi : Z) : YP09.region := YP09.mkRegion (Some 9%nat) 32 192 wlo whi s1_chunks.
Definition s23_slots (cx : lcx) (tab mt a n m : Z) : list (Z * Z) :=
  [(32, x_cap cx); (56, x_fr cx + FO_V); (88, tab); (96, mt + 16); (104, a); (112, mt); (120, n); (144, x_sh cx);
   (152, shadow_addr (m + seg_spec.MC_N)); (168, m); (176, SHADOW_OFF); (184, m + seg_spec.MC_N)].
Definition s23_vals (cx : lcx) (tab mt a n m : Z) : list Z := [x_cap cx; x_fr cx + FO_V; tab; mt; a; n; x_sh cx; m].
Lemma s23_chunk8 : forall (W : world SEGS) mem E base off e v,
  rdword (rdW W mem) (base + off) = Some v -> 0 <= v < 2 ^ 64 -> U E e = v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 e)).
Proof.
intros W mem E base off e v Hw Hv HU.
apply (chunk_ok_val SEGS E _ base off 8 e v); [exact (s23_denot_of_U E e v HU Hv) | cbn; lia | cbn; lia |].
exact (val_mem_of_rdword SEGS (w_H W) mem _ v Hw).
Qed.
(* the seed: a state at the point pc of the segment is an instance of the s1 region over these atoms *)
Lemma s23_s1_seed : forall pc wlo whi cx (W : world SEGS) regs mem tab mt a n m extra G,
  lt_slots cx (rdW W mem) (s23_slots cx tab mt a n m) ->
  getr regs 9 = w64 (x_s1 cx) -> getr regs 15 = w64 SHADOW_OFF ->
  0 <= x_s1 cx -> x_s1 cx + 192 <= 2 ^ 64 ->
  0 <= x_cap cx < 2 ^ 64 -> 0 <= x_fr cx + FO_V < 2 ^ 64 -> 0 <= tab < 2 ^ 64 -> 0 <= mt < 2 ^ 63 ->
  0 <= a < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= x_sh cx < 2 ^ 64 -> 0 <= m < 2 ^ 62 ->
  (forall o, wlo <= o < whi -> writable_at SEGS (mrestrict (w_H W) mem) (x_s1 cx + o)) ->
  region_wf (s1_region wlo whi) = true ->
  facts_ok (s23_E regs (s23_vals cx tab mt a n m ++ extra)) G ->
  st_ok_pi SEGS VAL (s23_E regs (s23_vals cx tab mt a n m ++ extra))
    (mkSS pc sr_atoms [s1_region wlo whi] None G)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc wlo whi cx W regs mem tab mt a n m extra G HSL R9 R15 Hs0 Hs1 Rc Rv Rt Rmt Ra Rn Rsh Rm Hwr Hwf HG.
set (E := s23_E regs (s23_vals cx tab mt a n m ++ extra)) in *.
assert (EV : forall j, (j < 8)%nat -> ew E (32 + j) = Z_to_bv 64 (nth j (s23_vals cx tab mt a n m) 0)).
{ intros j Hj. subst E. rewrite s23_E_val by (unfold A_TEXT; lia). rewrite app_nth1 by (cbn; lia). reflexivity. }
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx).
{ subst E. rewrite (s23_E_reg _ _ 9 9%bv eq_refl), R9. apply unsigned_lit_small. lia. }
assert (U15 : U E (SOff 15 0) = SHADOW_OFF).
{ apply U_atom; [subst E; rewrite (s23_E_reg _ _ 15 15%bv eq_refl); exact R15 | unfold SHADOW_OFF; lia]. }
assert (HW : forall o v, In (o, v) (s23_slots cx tab mt a n m) -> rdword (rdW W mem) (x_s1 cx + o) = Some v)
  by (intros o v Hin; exact (HSL o v Hin)).
unfold s23_slots in HW.
assert (HRO : regs_ok E sr_atoms regs) by (subst E; unfold s23_E; apply regs_ok_Eimg_Ereg).
clearbody E.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- exact HRO.
- cbn [regions_wf]. rewrite Hwf. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold YP09.region_ok.
  cbn [s1_region YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [exact Hwr|].
  unfold s1_chunks. repeat apply Forall_cons; try apply Forall_nil;
    (eapply s23_chunk8; [apply HW; cbn [In]; repeat (first [left; reflexivity | right]) | | ]).
  + exact Rc.
  + apply (U_atom E 32 _ (EV 0%nat ltac:(lia)) Rc).
  + exact Rv.
  + apply (U_atom E 33 _ (EV 1%nat ltac:(lia)) Rv).
  + exact Rt.
  + apply (U_atom E 34 _ (EV 2%nat ltac:(lia)) Rt).
  + lia.
  + apply (U_atom_off E 35 mt 16 (EV 3%nat ltac:(lia))); lia.
  + exact Ra.
  + apply (U_atom E 36 _ (EV 4%nat ltac:(lia)) Ra).
  + lia.
  + apply (U_atom E 35 mt (EV 3%nat ltac:(lia))). lia.
  + exact Rn.
  + apply (U_atom E 37 _ (EV 5%nat ltac:(lia)) Rn).
  + exact Rsh.
  + apply (U_atom E 38 _ (EV 6%nat ltac:(lia)) Rsh).
  + unfold shadow_addr, SHADOW_OFF, seg_spec.MC_N. pose proof (Z.div_pos (m + 0x2000) 8).
    pose proof (Z.div_le_upper_bound (m + 0x2000) 8 (2 ^ 60)). lia.
  + apply (s23_U_shw E 39 0x2000 m (EV 7%nat ltac:(lia))); [lia | lia | exact U15].
  + lia.
  + apply (U_atom E 39 m (EV 7%nat ltac:(lia))). lia.
  + unfold SHADOW_OFF. lia.
  + exact U15.
  + unfold seg_spec.MC_N. lia.
  + apply (U_atom_off E 39 m 0x2000 (EV 7%nat ltac:(lia))); lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- exact HG.
Qed.
End k.

(* ============================ the segment's internal points and their shared facts ============================ *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Section i.
Variable i : nat.

(* the premises of K85ac4 i, packed (LLVMFuzzerTestOneInput_defs.v LT_K85ac4_stmt, in its order) *)
Definition s23_ctx cx ly S (W : world SEGS) regs mem md k acc (c m tab mt : Z) (par : list Z) (vid : Z) : Prop :=
  lt_base B MT cx /\ sa_frm0 /\ (i < length (SegModel.mc_seg (x_mcF cx)))%nat /\
  lt_core B MT cx ly S W regs mem md k acc 4 LFO_NV
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  lt_hblk B ly S (rdW W mem) tab (x_tabn cx) /\ lt_hblk B ly S (rdW W mem) mt (x_mtn cx) /\
  SegModel.ms_ignore (x_seg cx i) = false /\
  SegModel.m_split (SegModel.ms_name (x_seg cx i)) = Some (par, vid) /\
  getr regs 15 = w64 SHADOW_OFF /\ getr regs 18 = w64 vid /\ getr regs 22 = w64 (seg_spec.mseg_addr m i) /\
  getr regs 23 = w64 (-8) /\ getr regs 25 = w64 (Z.of_nat i) /\ getr regs 26 = w64 (- seg_spec.mseg_addr m i) /\
  getr regs 27 = w64 (seg_spec.mseg_addr m i) /\
  0 <= fst (x_decl cx i) /\
  lt_slots cx (rdW W mem) (LT_LV cx c m ++
    [(88, tab); (96, mt + 16); (104, fst (x_decl cx i)); (112, mt); (120, Z.of_nat (length (snd (x_decl cx i))));
     (128, LT_VIDMAX); (136, LT_MASK); (152, shadow_addr (m + seg_spec.MC_N))]) /\
  lt_cm (rdW W mem) c m (x_run cx) /\
  lt_tabs cx (rdW W mem) tab mt (snd (x_decl cx i)) /\
  sa_strz (rdW W mem) (x_fr cx + FO_V) par /\ sa_val (rdW W mem) (x_fr cx + FO_VID) 4 vid.

(* the stack window below s1 the segment's two calls may write *)
Definition s23_scr (cx : lcx) (a : Z) : Prop := x_s1 cx - 2 * ESTACK <= a < x_s1 cx.
(* the bytes the segment may change before the latch: that window, the two counter slots 104(s1) and 120(s1), and
   the entry mt[mn] the copy writes *)
Definition s23_D0 (cx : lcx) (mt : Z) (mn : nat) (a : Z) : Prop :=
  s23_scr cx a \/ (x_s1 cx + 104 <= a < x_s1 cx + 112) \/ (x_s1 cx + 120 <= a < x_s1 cx + 128) \/
  (mt + 20 * Z.of_nat mn <= a < mt + 20 * Z.of_nat mn + 20).
(* a state of the segment reached from the K85ac4 state (regs0, mem0): the journal from the entry, the registers rl
   as at K85ac4, every byte outside D as at K85ac4 *)
Definition s23_rel cx ly S (W : world SEGS) regs0 mem0 regs mem md k (D : Z -> Prop) (rl : list (bv 5)) : Prop :=
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k /\
  (forall r, In r rl -> getr regs r = getr regs0 r) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ D a -> rdW W mem a = rdW W mem0 a).
Definition S23_RLK : list (bv 5) := [2; 3; 4; 8; 9; 15; 18; 22; 23; 25; 26; 27]%bv.

(* ---- the internal points of the segment ---- *)
(* 0x85ad8 (offset 0xda4): the scan's head after j < mn entries: s3 = &mt[j].vid, s4 = &mt[j], s5 = mn - j, s8 the
   duplicate test over mt[0 .. j) *)
Definition S15_LOOP (j : nat) : Prop :=
  forall cx ly S (W : world SEGS) regs0 mem0 md0 k acc c m tab mt par vid regs mem md,
  s23_ctx cx ly S W regs0 mem0 md0 k acc c m tab mt par vid ->
  s23_rel cx ly S W regs0 mem0 regs mem md k (s23_scr cx) S23_RLK ->
  (j < length (snd (x_decl cx i)))%nat ->
  getr regs 19 = w64 (mt + 16 + 20 * Z.of_nat j) -> getr regs 20 = w64 (mt + 20 * Z.of_nat j) ->
  getr regs 21 = w64 (Z.of_nat (length (snd (x_decl cx i))) - Z.of_nat j) ->
  getr regs 24 = w64 (seg_spec.b2z (existsb (s23_dup par vid) (firstn j (snd (x_decl cx i))))) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0xda4) regs mem md) (lt_post B MT cx).
(* 0x85b38 (offset 0xe04): the scan done, s8 its answer *)
Definition S15_X38 : Prop :=
  forall cx ly S (W : world SEGS) regs0 mem0 md0 k acc c m tab mt par vid regs mem md,
  s23_ctx cx ly S W regs0 mem0 md0 k acc c m tab mt par vid ->
  s23_rel cx ly S W regs0 mem0 regs mem md k (s23_scr cx) S23_RLK ->
  getr regs 24 = w64 (seg_spec.b2z (existsb (s23_dup par vid) (snd (x_decl cx i)))) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0xe04) regs mem md) (lt_post B MT cx).
(* 0x85b40 (offset 0xe0c): no duplicate, s5 = mn *)
Definition S15_X40 : Prop :=
  forall cx ly S (W : world SEGS) regs0 mem0 md0 k acc c m tab mt par vid regs mem md,
  s23_ctx cx ly S W regs0 mem0 md0 k acc c m tab mt par vid ->
  s23_rel cx ly S W regs0 mem0 regs mem md k (s23_scr cx) S23_RLK ->
  existsb (s23_dup par vid) (snd (x_decl cx i)) = false ->
  getr regs 21 = w64 (Z.of_nat (length (snd (x_decl cx i)))) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0xe0c) regs mem md) (lt_post B MT cx).


(* 0x85b7c (offset 0xe48): the join after the turn's model step, with x_decl (S i) in 104(s1), 120(s1) and at mt; the
   bytes outside s23_D0 as at K85ac4; s2 no longer vid (the copy path sets it to mn + 1) *)
Definition S23_RLKJ : list (bv 5) := [2; 3; 4; 8; 9; 15; 22; 23; 25; 26; 27]%bv.
Definition S15_PJ : Prop :=
  forall cx ly S (W : world SEGS) regs0 mem0 md0 k acc c m tab mt par vid regs mem md,
  s23_ctx cx ly S W regs0 mem0 md0 k acc c m tab mt par vid ->
  s23_rel cx ly S W regs0 mem0 regs mem md k (s23_D0 cx mt (length (snd (x_decl cx i)))) S23_RLKJ ->
  0 <= fst (x_decl cx (Datatypes.S i)) ->
  rdword (rdW W mem) (x_s1 cx + 104) = Some (fst (x_decl cx (Datatypes.S i))) ->
  rdword (rdW W mem) (x_s1 cx + 120) = Some (Z.of_nat (length (snd (x_decl cx (Datatypes.S i))))) ->
  sa_mtab (rdW W mem) mt (snd (x_decl cx (Datatypes.S i))) ->
  Z.of_nat (length (snd (x_decl cx (Datatypes.S i)))) <= x_cap cx ->
  SRr SEGS W (cfg_at SEGS (BASE + 0xe48) regs mem md) (lt_post B MT cx).

(* ---- the numbers and the facts of a K85ac4 state ---- *)
Lemma s23_ctx_num : forall cx ly S (W : world SEGS) regs mem md k acc c m tab mt par vid,
  s23_ctx cx ly S W regs mem md k acc c m tab mt par vid ->
  AR SEGS B ly S W mem md /\
  alloc_ceiling + 32000 <= x_s1 cx /\ x_s1 cx + 320 <= 2 ^ 47 /\ x_sp0 cx - 352 < x_s1 cx <= x_sp0 cx - 320 /\
  x_s1 cx mod 32 = 0 /\ spZ regs = x_s1 cx /\ frames S = [(LT_FCLS, x_fpos cx)] /\
  frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx /\ x_fr cx mod 64 = 0 /\ 4096 <= x_fr cx /\
  x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512 /\
  0 <= x_cap cx <= 39 /\ Z.of_nat (length (snd (x_decl cx i))) <= x_cap cx /\
  s23_blk B ly S c seg_spec.SEG_C_SIZE /\ s23_blk B ly S m seg_spec.SEG_M_SIZE /\
  s23_blk B ly S tab (x_tabn cx) /\ s23_blk B ly S mt (x_mtn cx).
Proof.
intros cx ly S W regs mem md k acc c m tab mt par vid CTX.
destruct CTX as (HB & HF0 & Hi & HC & Hc & Hm & Htab & Hmt & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htabs & _).
destruct HC as (HFR & _ & _ & _).
pose proof (proj1 HFR) as HJ. pose proof (proj1 HJ) as HAR.
destruct (s23_layout B MT LAWS cx ly S W regs mem md k LFO_NV HB HFR)
  as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & _).
destruct Htabs as (Htl & _ & _ & _ & _ & Hmn).
pose proof asan_consts as (C1 & _).
assert (Hcap : 0 <= x_cap cx <= 39) by lia.
assert (Htn : 0 < x_tabn cx) by (unfold x_tabn, seg_spec.RVLAN_SIZE; lia).
assert (Hmtn : 0 < x_mtn cx) by (unfold x_mtn, seg_spec.MVLAN_SIZE; lia).
split; [exact HAR|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact L3|]. split; [exact L5|].
split; [exact L6|]. split; [exact L7|]. split; [exact L8|]. split; [exact L9|]. split; [exact L10|].
split; [exact L11|]. split; [exact Hcap|]. split; [exact Hmn|].
split; [exact (s23_blk_of B LAWS ly S W mem md c seg_spec.SEG_C_SIZE HAR ltac:(unfold seg_spec.SEG_C_SIZE; lia) Hc)|].
split; [exact (s23_blk_of B LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR ltac:(unfold seg_spec.SEG_M_SIZE; lia) Hm)|].
split; [exact (s23_blk_of B LAWS ly S W mem md _ _ HAR Htn Htab)|].
exact (s23_blk_of B LAWS ly S W mem md _ _ HAR Hmtn Hmt).
Qed.
(* the slots the runs of the segment read, at a K85ac4 state *)
Lemma s23_ctx_slots : forall cx ly S (W : world SEGS) regs mem md k acc c m tab mt par vid,
  s23_ctx cx ly S W regs mem md k acc c m tab mt par vid ->
  lt_slots cx (rdW W mem) (s23_slots cx tab mt (fst (x_decl cx i)) (Z.of_nat (length (snd (x_decl cx i)))) m).
Proof.
intros cx ly S W regs mem md k acc c m tab mt par vid CTX.
destruct CTX as (_ & _ & _ & HC & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSL & _).
destruct HC as (HFR & _). destruct HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H176 & _).
intros o v Hin. unfold s23_slots in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-;
  first [exact H176 | apply HSL; unfold LT_LV; cbn [In app]; repeat (first [left; reflexivity | right])]|]).
destruct Hin.
Qed.

(* the cut facts at the end of the turn (K858f4 (i + 1) and K85bd0 share them), from the K85ac4 state and a state
   of the same allocator state whose bytes outside s23_D0 and v's three shadow bytes are those of K85ac4, with v out
   of scope and the model's table t' at mt *)
Lemma s23_end : forall cx ly S (W : world SEGS) regs0 mem0 md0 k acc c m tab mt par vid regs mem md
  (t' : list (list Z * Z)),
  s23_ctx cx ly S W regs0 mem0 md0 k acc c m tab mt par vid ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  getr regs 2 = getr regs0 2 -> getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  getr regs 8 = getr regs0 8 -> getr regs 9 = getr regs0 9 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s23_D0 cx mt (length (snd (x_decl cx i))) a -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) ->
     rdW W mem a = rdW W mem0 a) ->
  (forall j, 4 <= j < 7 -> rdW W mem (x_sh cx + j) = Some 0xf8) ->
  sa_mtab (rdW W mem) mt t' -> Z.of_nat (length t') <= x_cap cx ->
  lt_core B MT cx ly S W regs mem md k acc 4 LFO_N
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  lt_hblk B ly S (rdW W mem) tab (x_tabn cx) /\ lt_hblk B ly S (rdW W mem) mt (x_mtn cx) /\
  lt_cm (rdW W mem) c m (x_run cx) /\ lt_tabs cx (rdW W mem) tab mt t' /\
  lt_slots cx (rdW W mem) (LT_LV cx c m ++ [(96, mt + 16); (112, mt); (128, LT_VIDMAX); (136, LT_MASK);
    (152, shadow_addr (m + seg_spec.MC_N))]).
Proof.
intros cx ly S W regs0 mem0 md0 k acc c m tab mt par vid regs mem md t' CTX HJ E2 E3 E4 E8 E9 K Hf8 Hmtab Hlen.
destruct (s23_ctx_num _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX)
  as (HAR0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & Bc & Bm & Btab & Bmt).
destruct CTX as (HB & HF0 & Hi & HC & Hcb & Hmb & Htb & Hmtb & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSL & Hcm & Htabs
  & Hv & Hvid).
destruct HC as (HFR & HIMG & HBLK & HBUD).
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Bc as (Ic & Bc4 & _ & Bcc & Bca). pose proof Bm as (Im & Bm4 & _ & Bmc & Bma).
pose proof Btab as (It & Bt4 & _ & Btc & Bta). pose proof Bmt as (Imt & Bmt4 & _ & Bmtc & Bmta).
(* the four harness blocks are pairwise distinct, so their bytes are apart *)
pose proof (Permutation_NoDup HBLK (s23_ablocks_NoDup B LAWS ly S W mem0 md0 HAR0)) as HND.
apply NoDup_app_remove_r in HND.
assert (Dmc : zdisjoint (mt, req_size (x_mtn cx)) (c, req_size seg_spec.SEG_C_SIZE)).
{ apply (sep_blocks SEGS B LAWS ly S W mem0 md0 _ _ _ _ HAR0 Imt Ic). intros Heq. rewrite Heq in HND.
  inversion HND as [|? ? Hn _]. apply Hn. cbn. right; right; left. reflexivity. }
assert (Dmm : zdisjoint (mt, req_size (x_mtn cx)) (m, req_size seg_spec.SEG_M_SIZE)).
{ apply (sep_blocks SEGS B LAWS ly S W mem0 md0 _ _ _ _ HAR0 Imt Im). intros Heq. rewrite Heq in HND.
  inversion HND as [|? ? Hn _]. apply Hn. cbn. right; left. reflexivity. }
assert (Dmt : zdisjoint (mt, req_size (x_mtn cx)) (tab, req_size (x_tabn cx))).
{ apply (sep_blocks SEGS B LAWS ly S W mem0 md0 _ _ _ _ HAR0 Imt It). intros Heq. rewrite Heq in HND.
  inversion HND as [|? ? Hn _]. apply Hn. cbn. left. reflexivity. }
assert (Hin3 : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite N6; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS ly S W mem0 md0 _ _ _ _ HAR0 Imt Hin3) as Dmf. rewrite N7 in Dmf.
pose proof (blk_off_imgP B ly S W mem0 md0 _ _ HAR0 Imt) as Omt.
assert (EFB : fs_frame_bytes LT_FCLS = 512) by reflexivity. rewrite EFB in Dmf.
assert (RQ : forall n, 0 < n -> req_size n = n)
  by (intros n Hn; unfold req_size; destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]).
rewrite (RQ (x_mtn cx)) in Dmc, Dmm, Dmt, Dmf, Omt by (unfold x_mtn, seg_spec.MVLAN_SIZE; lia).
rewrite (RQ seg_spec.SEG_C_SIZE) in Dmc by (unfold seg_spec.SEG_C_SIZE; lia).
rewrite (RQ seg_spec.SEG_M_SIZE) in Dmm by (unfold seg_spec.SEG_M_SIZE; lia).
rewrite (RQ (x_tabn cx)) in Dmt by (unfold x_tabn, seg_spec.RVLAN_SIZE; lia).
unfold zdisjoint, off_img in Dmc, Dmm, Dmt, Dmf, Omt. cbn [fst snd] in Dmc, Dmm, Dmt, Dmf.
unfold x_tabn, x_mtn, seg_spec.RVLAN_SIZE, seg_spec.MVLAN_SIZE, seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE
  in Dmc, Dmm, Dmt, Dmf, Omt, Bcc, Bmc, Btc, Bmtc, Bca, Bma, Bta, Bmta.
pose proof (Z.div_mod (x_fr cx) 64 ltac:(lia)) as Hq. rewrite N8, Z.add_0_r in Hq. set (q := x_fr cx / 64) in Hq.
assert (Ush : x_sh cx = SHADOW_OFF + 8 * q).
{ unfold x_sh, shadow_addr. rewrite Hq. f_equal. replace (64 * q) with (q * 8 * 8) by lia. rewrite Z.div_mul by lia. lia. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in N11, Bca, Bma, Bta, Bmta.
unfold SHADOW_OFF in Ush.
set (mn := length (snd (x_decl cx i))) in *.
(* the bytes each fact reads are outside the changed set, by kind *)
assert (KST : forall a, (x_s1 cx <= a < x_s1 cx + 104 \/ x_s1 cx + 112 <= a < x_s1 cx + 120 \/
    x_s1 cx + 128 <= a < x_sp0 cx) -> rdW W mem a = rdW W mem0 a).
{ intros a Ha. apply K; unfold s23_D0, s23_scr, ESTACK;
  clear - Ha N1 N2 N3 C1 Bmtc Ush Hq N10 N12 N13; lia. }
assert (KFR : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W mem a = rdW W mem0 a).
{ intros a Ha. apply K; unfold s23_D0, s23_scr, ESTACK;
  clear - Ha N1 N2 N3 C1 Dmf N10 N11 N12 N13 Ush Hq; lia. }
assert (KC : forall a, c <= a < c + 16616 -> rdW W mem a = rdW W mem0 a).
{ intros a Ha. apply K; unfold s23_D0, s23_scr, ESTACK;
  clear - Ha N1 N2 N3 C1 Dmc Bca Bcc N9 N10 N12 N13 Ush Hq; lia. }
assert (KM : forall a, m <= a < m + 9236 -> rdW W mem a = rdW W mem0 a).
{ intros a Ha. apply K; unfold s23_D0, s23_scr, ESTACK;
  clear - Ha N1 N2 N3 C1 Dmm Bma Bmc N9 N10 N12 N13 Ush Hq; lia. }
assert (KT : forall a, tab <= a < tab + 18 * (x_cap cx + 1) -> rdW W mem a = rdW W mem0 a).
{ intros a Ha. apply K; unfold s23_D0, s23_scr, ESTACK;
  clear - Ha N1 N2 N3 C1 Dmt Bta Btc N9 N10 N12 N13 Ush Hq; lia. }
assert (KI : forall a, 0x10000 <= a < kImgEnd -> rdW W mem a = rdW W mem0 a).
{ intros a Ha. unfold kImgEnd in Ha. apply K; unfold s23_D0, s23_scr, ESTACK;
  clear - Ha N1 N2 N3 C1 Omt N9 N10 N12 N13 Ush Hq; lia. }
assert (KSH : forall j, 0 <= j < 36 -> ~ (4 <= j < 7) -> rdW W mem (x_sh cx + j) = rdW W mem0 (x_sh cx + j)).
{ intros j Hj Hn. apply K; unfold s23_D0, s23_scr, ESTACK;
  clear - Hj Hn N1 N2 N3 C1 Bmta Bmtc N9 N10 N12 N13 Ush Hq; lia. }
assert (KS : forall lo n, (forall a, lo <= a < lo + n -> rdW W mem a = rdW W mem0 a) ->
  s23_kept (rdW W mem0) (rdW W mem) lo n) by (intros lo n H x Hx; exact (H x Hx)).
destruct Htabs as (Htl & Hrtab & Hguard & Hnval & _ & _).
destruct Hcm as [Hrc Hmc].
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- split; [|split; [|split; [exact HBLK | exact HBUD]]].
  + apply (s23_frame_kept B cx ly S W regs0 mem0 md0 k LFO_NV regs mem md LFO_N HFR HJ E2 E3 E4 E8 E9).
    * apply KS. intros a Ha. apply KST. lia.
    * apply KS. intros a Ha. apply KFR. lia.
    * apply KS. intros a Ha. apply KFR. unfold LT_FLAGW in Ha. lia.
    * apply KS. intros a Ha. apply KST. lia.
    * destruct HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh).
      exact (s23_fsh_N (rdW W mem0) (rdW W mem) (x_sh cx) Hsh Hf8 KSH).
  + exact (s23_img_kept B cx W mem0 mem KI HIMG).
- exact (s23_hblk_of B LAWS ly S W mem md c seg_spec.SEG_C_SIZE HAR ltac:(unfold seg_spec.SEG_C_SIZE; lia) Bc).
- exact (s23_hblk_of B LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR ltac:(unfold seg_spec.SEG_M_SIZE; lia) Bm).
- exact (s23_hblk_of B LAWS ly S W mem md tab (x_tabn cx) HAR ltac:(unfold x_tabn, seg_spec.RVLAN_SIZE; lia) Btab).
- exact (s23_hblk_of B LAWS ly S W mem md mt (x_mtn cx) HAR ltac:(unfold x_mtn, seg_spec.MVLAN_SIZE; lia) Bmt).
- split.
  + apply (s23_kept_rconf (rdW W mem0)); [|exact Hrc]. unfold seg_spec.SEG_C_SIZE.
    apply KS. intros a Ha. apply KC. lia.
  + apply (s23_kept_mconf (rdW W mem0)); [|exact Hmc]. unfold seg_spec.SEG_M_SIZE.
    apply KS. intros a Ha. apply KM. lia.
- split; [exact Htl|]. split; [|split; [|split; [|split; [exact Hmtab | exact Hlen]]]].
  + apply (s23_kept_rtab (rdW W mem0)); [|exact Hrtab].
    apply KS. intros a Ha. apply KT. lia.
  + apply (s23_kept_guard (rdW W mem0)); [|exact Hguard]. unfold seg_spec.RVLAN_SIZE.
    apply KS. intros a Ha. apply KT. lia.
  + apply (s23_kept_val (rdW W mem0)); [|exact Hnval]. unfold FO_N.
    apply KS. intros a Ha. apply KFR. lia.
- intros o v Hin. assert (Ho : In (o, v) (LT_LV cx c m ++
    [(88, tab); (96, mt + 16); (104, fst (x_decl cx i)); (112, mt); (120, Z.of_nat mn);
     (128, LT_VIDMAX); (136, LT_MASK); (152, shadow_addr (m + seg_spec.MC_N))])).
  { apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin|right]. cbn [In] in Hin |- *.
    tauto. }
  assert (Hor : (o <= 96 \/ o = 112 \/ 128 <= o) /\ 0 <= o <= 184).
  { apply in_app_or in Hin as [Hin|Hin]; unfold LT_LV in Hin; cbn [In] in Hin;
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; lia|]); destruct Hin. }
  apply (s23_kept_word (rdW W mem0)); [|exact (HSL o v Ho)].
  apply KS. intros a Ha. apply KST. lia.
Qed.

End i.
End w.

(* ---- tactics of the runs ---- *)
Ltac s23_mdv := lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ =>
  let x := fresh "mdv" in set (x := d) in *; clearbody x end.
(* a register as the run's last state names it *)
Ltac s23_prraw HS r P :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as P;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in P;
    cbn [ms_regs restrict mkst] in P
  end.
(* a register a plain run left as its own atom, over the environment s23_E regs0 _ *)
Ltac s23_kreg HS HE r :=
  let P := fresh "P" in s23_prraw HS r P; apply (s23_reg_keep _ _ _ _ _ P); rewrite HE; apply s23_E_reg; reflexivity.
Ltac s23_kreg_goal HS HE := lazymatch goal with |- getr _ ?r = getr _ ?r => s23_kreg HS HE r end.
Ltac s23_vreg HS r := let P := fresh "P" in s23_prraw HS r P; apply (s23_reg_U _ _ _ _ _ P).

