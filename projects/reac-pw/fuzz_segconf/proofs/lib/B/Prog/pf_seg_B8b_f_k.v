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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 603 of its 653 lines of code are new or changed and 403 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a6_k.v, with its module paths and numbers changed; 537 of its 832 lines of code are new or changed and 358 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the KIT of the
   FOUND sub-walk of segment B8b of reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B8b_f.v,
   pb8b_found_holds : HA_B8B_JOIN B n -> H_FOUND B n, FOUND 0x88eb0 -> JOIN 0x88f00). A B8b sub-lane of
   the image-B G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment B8b, sub-walk FOUND; helper lemmas only, no instruction is walked
   here). Reuse search and CONFIRM: the rule-24 lookup record (none released).
   ADAPTED from a working branch's lib/A/Prog/pf_a6_k.v (a6_keeps, a6_keeps_call, a6_keeps_refuse,
   a6_base_move, a6_nm_move, a6_obj_arg, a6_buf_arg, a6_heap_*, a6_lit_move, a6_cat_move, a6_sl_move,
   a6_refuse_W_*, a6_band_not_app, a6_cx, a6_frame, a6_s1) + a working branch's lib/A/Prog/pf_a7_s.v
   (a7_round8, a7_le65535, a7_refuse_site_ok) and pf_a7_u.v (a7u_lit), re-derived on image B through the image-B
   ports of the same lemmas that the B7 segment lane compiled (lib/B/Prog/pf_seg_B7_k.v, pf_seg_B7_ch.v b7_chain, in its
   own clone; copied here, not Required).

   WHAT CHANGES FOR IMAGE B (checked against B's own files, not carried from A):
   - pf_fi has ten conjuncts (B's pf_pieces.v): the A nine plus pf_tf and c's slot 0xc8; its register list is
     [2; 3; 4; 8; 9; 20] (s4 = x20 = SHADOW_OFF; A: s6 = x22).
   - the realigned locals base is s1 = (sp0 - 0x160) & -32 (B's 0x87e38 `addi sp,sp,-352`), so
     sp0 - 0x180 < s1 <= sp0 - 0x160; STK_reac_segconf_parse_file = 12832 (SegInstB.STK_values).
   - the refuse call this kit serves is 0x88ef8: refuse(c, ln + 1, F_twice, np) with a2 = seg_litA_rc F_twice =
     0x21620 = listing object A_OBJ 68 (POSITIONAL NAME checked: index 68 of B's SegAddr.seg_objs is 0x21620,
     pb8bf_lit closes it by vm_compute).
   - sa_ssp after the call comes from the Section hypothesis SSPX (the stack-protector cells at every AR state, as
     segments B6, B9, B10b, B11c take it) at the state refuse returned (pb8bf_base_move). The record's image facts
     no longer give it: the image-B listing owner's SegRo.v (`mkro --owned`, ec20d5d4e1df) leaves the runtime-owned GOT words, gotwA
     = 0xa3e98 among them, out of seg_ro_in / seg_ro_list.
   - the read-only range lies in the image by VRO and the instance's pa_relro_img (pb8bf_in_roP_img).
   Section hypotheses: OBJ (pb8bf_lit only), VRO (pb8bf_in_roP_img, pb8bf_base_move and what calls it), SSPX
   (pb8bf_base_move and what calls it). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_seg_B8b_d pf_seg_B8b_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ============================== 1. pure arithmetic ============================== *)
(* the 64-bit canonical value of the sign extension of a u32 x (the `lw` of B#36 / B#37) *)
Lemma pb8bf_swrap32 : forall x, 0 <= x < 2 ^ 32 ->
  zcanon (bv_swrap 32 (x mod 2 ^ 32)) = if x <? 2 ^ 31 then x else x + (2 ^ 64 - 2 ^ 32).
Proof.
intros x Hx. rewrite (Z.mod_small x) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec x (2 ^ 31)) as [Hl|Hl].
- rewrite (Z.mod_small (x + 2 ^ 31) (2 ^ 32)) by lia. replace (x + 2 ^ 31 - 2 ^ 31) with x by lia.
  apply Z.mod_small. lia.
- rewrite <- (Z.mod_unique (x + 2 ^ 31) (2 ^ 32) 1 (x + 2 ^ 31 - 2 ^ 32)) by lia.
  symmetry. apply (Z.mod_unique _ (2 ^ 64) (-1)); lia.
Qed.
Lemma pb8bf_sext32_inj : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  zcanon (bv_swrap 32 (x mod 2 ^ 32)) = zcanon (bv_swrap 32 (y mod 2 ^ 32)) -> x = y.
Proof.
intros x y Hx Hy H. rewrite (pb8bf_swrap32 x Hx), (pb8bf_swrap32 y Hy) in H. revert H.
destruct (Z.ltb_spec x (2 ^ 31)) as [Lx|Lx], (Z.ltb_spec y (2 ^ 31)) as [Ly|Ly]; intros HE; lia.
Qed.
Lemma pb8bf_sext32_eq : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> x = y ->
  zcanon (bv_swrap 32 (x mod 2 ^ 32)) = zcanon (bv_swrap 32 (y mod 2 ^ 32)).
Proof. intros x y _ _ ->. reflexivity. Qed.
Lemma pb8bf_U_sext : forall E (a : sv) x, U E a = x -> 0 <= x < 2 ^ 32 ->
  U E (SExt true 32 a) = zcanon (bv_swrap 32 (x mod 2 ^ 32)).
Proof. intros E a x H _. rewrite U_SExt, H. reflexivity. Qed.
(* reader_pre's text bound (length s <= 65535)%nat, in Z (pf_a7_s.v a7_le65535) *)
Lemma pb8bf_le65535 : forall m : nat, (m <= 65535)%nat -> Z.of_nat m <= 65535.
Proof.
intros m H. apply Nat2Z.inj_le in H.
assert (E : Z.of_nat 65535%nat = 65535) by (vm_compute; reflexivity).
rewrite E in H. exact H.
Qed.
(* rounding up to the next multiple of 8 stays below an 8-aligned bound (pf_a7_s.v a7_round8) *)
Lemma pb8bf_round8 : forall x M, x <= M -> M mod 8 = 0 -> x + (- x) mod 8 <= M.
Proof.
intros x M H1 H2.
pose proof (Z.div_mod (- x) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod M 8 ltac:(lia)) as D2.
lia.
Qed.
Lemma pb8bf_w64_u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof.
intros z Hz. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* ============================== 2. the model and the counters ============================== *)
Lemma pb8bf_cnt_pos : forall cf (s : list Z) (o : nat), (o < length s)%nat ->
  pf_cnt cf (length (skipn o s)) -> rc_refused cf + 1 < 2 ^ 32.
Proof. intros cf s o _ [H1 _]. lia. Qed.
Lemma pb8bf_cnt_next : forall cf (s : list Z) (o : nat), (o < length s)%nat ->
  pf_cnt cf (length (skipn o s)) -> pf_cnt cf (length (skipn (pf_next s o) s)).
Proof.
intros cf s o Ho H. apply (pf_cnt_mono cf (length (skipn o s))); [|exact H].
pose proof (pf_next_skipn_lt s o Ho). lia.
Qed.
Lemma pb8bf_cnt_refuse_next : forall cf ln f a (s : list Z) (o : nat), (o < length s)%nat ->
  pf_cnt cf (length (skipn o s)) -> pf_cnt (refuse cf ln f a) (length (skipn (pf_next s o) s)).
Proof. intros cf ln f a s o Ho H. exact (pf_cnt_refuse cf ln f a _ _ (pf_next_skipn_lt s o Ho) H). Qed.
(* F_twice: a refusal format, one of parse_file's literals, one %s conversion *)
Lemma pb8bf_fmt : In F_twice seg_spec.REFUSE_FORMATS /\ In F_twice PARSE_FILE_LITS /\
  (forall x : list Z, seg_spec.conv_kinds F_twice = map seg_spec.arg_is_s [AS x]).
Proof.
split; [unfold seg_spec.REFUSE_FORMATS; pb8b_in|].
split; [unfold PARSE_FILE_LITS; apply in_or_app; left; pb8b_in|].
intros x. cbn [map seg_spec.arg_is_s]. vm_compute. reflexivity.
Qed.

(* ============================== 4 (pure part). the bytes of a u32 field ============================== *)
Lemma pb8bf_nth_le_bytes : forall (n k : nat) z, (k < n)%nat -> 0 <= z ->
  nth k (Z_to_le_bytes n z) seg_spec.ZERO = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros k z Hk Hz; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH; [| lia | apply Z.shiftr_nonneg; lia].
  rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma pb8bf_le4_byte : forall v k, (k < 4)%nat -> 0 <= v < 2 ^ 32 ->
  nth k (Mem.le4 (Z_to_bv 64 v)) seg_spec.ZERO = Z_to_bv 8 (le_byte v 4 k).
Proof.
intros v k Hk Hv. unfold Mem.le4.
assert (Hu : bv_unsigned (Z_to_bv 64 v) = v).
{ rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
rewrite Hu, (pb8bf_nth_le_bytes 4 k v Hk ltac:(lia)).
unfold le_byte. change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* ============================== 5 (pure part). refuse's footprint ============================== *)
(* every byte refuse writes lies in [c + RC_REFUSAL, c + RC_OVERFLOW) *)
Lemma pb8bf_refuse_W_in_block : forall c rcs a, inFP (refuse_W c rcs) a ->
  c + seg_spec.RC_REFUSAL <= a < c + seg_spec.RC_OVERFLOW.
Proof.
intros c rcs a (r & Hr & Ha). unfold refuse_W in Hr. apply in_app_or in Hr as [Hr|Hr].
- destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  unfold seg_spec.RC_REFUSED, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW in *. lia.
- revert Hr. destruct (length (rc_refusal rcs) <? 8)%nat eqn:E; intros Hr; [|destruct Hr].
  apply Nat.ltb_lt in E.
  destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha;
    unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.RC_NREF,
      seg_spec.RC_OVERFLOW in *; lia.
Qed.
Lemma pb8bf_refuse_W_pos : forall c rcs, 0 < c -> ~ YI16.sink_open_fp (refuse_W c rcs).
Proof.
intros c rcs Hc. apply sink_closed_pos. apply Forall_forall. intros r Hr. unfold refuse_W in Hr.
apply in_app_or in Hr as [Hr|Hr].
- destruct Hr as [<- | []]. cbn [fst]. unfold seg_spec.RC_REFUSED. lia.
- revert Hr. destruct (length (rc_refusal rcs) <? 8)%nat; intros Hr; [|destruct Hr].
  destruct Hr as [<- | [<- | []]]; cbn [fst];
    unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.RC_NREF; lia.
Qed.
(* refuse's footprint is inside parse_file's (the range refusal[0] .. overflow + 4 of RC_PARSE_W) *)
Lemma pb8bf_refuse_W_sub : forall c rcs a, inFP (refuse_W c rcs) a -> inFP (seg_spec.RC_PARSE_W c) a.
Proof.
intros c rcs a Ha. apply pb8bf_refuse_W_in_block in Ha.
exists (c + seg_spec.RC_REFUSAL, c + seg_spec.RC_OVERFLOW + 4). split.
- unfold seg_spec.RC_PARSE_W. right. left. reflexivity.
- cbn [fst snd]. lia.
Qed.

(* ============================== shadow and placement facts over Z ============================== *)
(* an 8-byte granule inside an addressable range has shadow byte 0 *)
Lemma pb8bf_sh0 : forall (rd : reader) q n x, range_addressable rd SHADOW_OFF q n -> q <= x -> x + 8 <= q + n ->
  rd (SHADOW_OFF + x / 8) = Some 0.
Proof.
intros rd q n x HR H1 H2.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
assert (Hy : x - x mod 8 + 7 = 7 + x / 8 * 8) by lia.
destruct (HR (x - x mod 8 + 7) ltac:(lia)) as (s & Hs & Hok).
assert (Ey : (x - x mod 8 + 7) / 8 = x / 8).
{ rewrite Hy, Z.div_add by lia. change (7 / 8) with 0. lia. }
assert (Ym : (x - x mod 8 + 7) mod 8 = 7).
{ rewrite Hy, Z_mod_plus_full. reflexivity. }
unfold shadow_of_addr in Hs. rewrite Ey in Hs.
destruct Hok as [-> | [Ha Hb]]; [exact Hs | lia].
Qed.
(* the realigned locals base s1 = (sp0 - 0x160) & -32 (pf_s1; pf_seg_B7_k.v b7k_s1) *)
Definition pb8bf_s1v (sp0 : Z) : Z := (sp0 - 0x160) - (sp0 - 0x160) mod 32.
Lemma pb8bf_s1 : forall sp0, sp0 mod 16 = 0 ->
  sp0 - 0x180 < pb8bf_s1v sp0 <= sp0 - 0x160 /\ pb8bf_s1v sp0 mod 32 = 0 /\ pb8bf_s1v sp0 mod 16 = 0 /\
  (pb8bf_s1v sp0 - sp0) mod 16 = 0.
Proof.
intros sp0 H16. unfold pb8bf_s1v.
pose proof (Z.mod_pos_bound (sp0 - 0x160) 32 ltac:(lia)) as Hm.
pose proof (Z.div_mod (sp0 - 0x160) 32 ltac:(lia)) as Hd.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hd16. rewrite H16 in Hd16.
split; [lia|].
replace ((sp0 - 0x160) - (sp0 - 0x160) mod 32) with (32 * ((sp0 - 0x160) / 32)) by lia.
split; [rewrite Z.mul_comm; apply Z_mod_mult|].
split; [replace (32 * ((sp0 - 0x160) / 32)) with ((2 * ((sp0 - 0x160) / 32)) * 16) by lia; apply Z_mod_mult|].
replace (32 * ((sp0 - 0x160) / 32) - sp0) with ((2 * ((sp0 - 0x160) / 32) - sp0 / 16) * 16) by lia.
apply Z_mod_mult.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
(* the stack-protector cells at every AR state (the image-A owner's route A; image B's stage-2 SegRecCells gives it), used
   only at the state refuse returned: across the walk's other steps sa_ssp is kept by the keep lemmas *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* a byte of the shadow band is in no app range (pf_a6_k.v a6_band_not_app) *)
Lemma pb8bf_band_not_app : forall b n s, in_app b n -> SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> ~ (b <= s < b + n).
Proof.
intros b n s Happ Hs Hin.
unfold in_app, SHADOW_OFF, kLowShadowBeg, YG0f.kHighMemBeg in *. lia.
Qed.

(* ============================== 2. the literal a2 holds at 0x88ef8 ============================== *)
(* listing object 68 is .str.11 0x21620, F_twice's text (B's SegAddr.seg_objs, index 68) *)
Lemma pb8bf_lit : forall E, img_env VAL A_LIM E -> ew E (A_OBJ 68) = w64 (seg_litA_rc F_twice).
Proof.
intros E HE. rewrite (img_env_atomP E (A_OBJ 68) HE) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite (OBJ 68%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

(* ============================== the entry facts, blocks, the image ============================== *)
Lemma pb8bf_s1_eq : forall v, pf_s1 v = pb8bf_s1v (pf_sp0 v).
Proof. reflexivity. Qed.
Lemma pb8bf_cx : forall v, pf_cx B v ->
  0 < p_c v /\ p_c v mod 16 = 0 /\ Z.of_nat (length (p_s v)) <= 65535 /\
  sa_disj (p_t v) (seg_spec.cstr_span (p_t v) (p_s v)) (p_c v) seg_spec.SEG_C_SIZE /\
  alloc_ceiling <= ly_stk_lo (p_ly v) /\ ly_stk_lo (p_ly v) + 12832 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\
  pf_sp0 v mod 16 = 0.
Proof.
intros v (HPRE & _ & _ & Hc64 & _ & _ & _ & _ & (fe & (C0 & C16 & _ & _ & _ & _ & _ & _ & _ & _ & LS & _ & _ & DJ & _) & _)
  & _ & _).
pose proof HPRE as (_ & _ & _ & _ & _ & (Hal & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
assert (LSz : Z.of_nat (length (p_s v)) <= 65535) by exact (pb8bf_le65535 _ LS).
unfold pf_sp0. rewrite SPF in Hslo. split; [lia|]. repeat split; first [exact C16 | exact LSz | exact DJ | lia].
Qed.
(* the read-only range lies in the image: its rom segments, and [RLO_A, RHI_A) = [pa_relro_lo, pa_relro_hi) by VRO *)
Lemma pb8bf_in_roP_img : forall a, in_roP SEGS RLO_A RHI_A a -> in_img SEGS a.
Proof.
intros a [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr]|].
destruct VRO as [Hlo Hhi]. apply pa_relro_img. rewrite Hlo, Hhi.
unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. lia.
Qed.
(* a literal keeps its bytes where the image bytes are kept; its tail is ROM, its shadow pinned *)
Lemma pb8bf_lit_move : forall (rd : reader) (W' : world SEGS) mem' a s, sa_lit SEGS B rd a s ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
     rdW W' mem' x = rd x) ->
  sa_lit SEGS B (rdW W' mem') a s.
Proof.
intros rd W' mem' a s (Ha & ((Hz & Hn) & _) & Hp & Hr & Hi) K.
split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hr)].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Hm & Ho & He). rewrite (K _ Hm Ho He). exact (Hz i Hi').
Qed.
Lemma pb8bf_cat_move : forall (rd : reader) (W' : world SEGS) mem', sa_cat SEGS B rd catA ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
     rdW W' mem' x = rd x) ->
  sa_cat SEGS B (rdW W' mem') catA.
Proof.
intros rd W' mem' (Hp & Hi & Hrows) K. split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (pb8bf_lit_move rd W' mem' tp _ Hl K)].
assert (Hn' : Z.of_nat i < 11) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (rdword_ext rd (rdW W' mem')); [exact Htp|]. intros k Hk.
unfold pin_spec.row_addr, pin_spec.CAT_ROW in *.
destruct (Hi (catA + 296 * Z.of_nat i + k) ltac:(unfold pin_spec.CAT_BYTES; lia)) as (Hm & Ho & He).
exact (K _ Hm Ho He).
Qed.
(* a range inside a live heap block is addressable, with its shadow words visible, at any state it is live *)
Lemma pb8bf_heap_addr : forall ly S (W : world SEGS) mem md q n,
  AR SEGS B ly S W mem md -> sa_heap B ly S q n -> 0 <= n -> sa_addr (rdW W mem) q n.
Proof.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hq) Hn.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
pose proof alloc_ceiling_lt as Hac.
unfold sa_addr.
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin Hb ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin Hb ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin Hb ltac:(lia) Hn0).
Qed.
Lemma pb8bf_heap_bounds : forall ly S (W : world SEGS) mem md q n,
  AR SEGS B ly S W mem md -> sa_heap B ly S q n -> 0 <= n ->
  exists b m, In (b, m) (ablocks B ly S) /\ b <= q /\ q + n <= b + req_size m /\ 4096 <= b /\
    b + req_size m <= alloc_ceiling /\ in_app b (req_size m).
Proof.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hq) Hn.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
exists b, m. split; [exact Hin|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact Happ].
Qed.
Lemma pb8bf_heap_perm : forall ly S ly' S' q n, Permutation (ablocks B ly' S') (ablocks B ly S) ->
  sa_heap B ly S q n -> sa_heap B ly' S' q n.
Proof.
intros ly S ly' S' q n HP (b & m & Hin & Hb & Hq). exists b, m.
split; [exact (Permutation_in _ (Permutation_sym HP) Hin) | lia].
Qed.
Lemma pb8bf_sl_move : forall (rd rd' : reader) b L, pf_sl rd b L ->
  Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 0x100) L -> 0 <= b -> b + 0x100 <= 2 ^ 64 ->
  (forall a, b <= a < 2 ^ 64 -> rd' a = rd a) -> pf_sl rd' b L.
Proof.
intros rd rd' b L HL HB Hb Hb2 K. unfold pf_sl in *. rewrite Forall_forall in HL, HB |- *.
intros ov Hin. rewrite <- (HL ov Hin). apply rdword_ext. intros k Hk.
pose proof (HB ov Hin). apply K. lia.
Qed.
Lemma pb8bf_PF_SL_offs : forall v pos, Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 0x100) (PF_SL v pos).
Proof. intros v pos. unfold PF_SL. repeat constructor; cbn [fst]; lia. Qed.

Section c1. Context {fx : YK11.FPState}.
Lemma pb8bf_frame : forall v pos lyc Sc Wc rX memc mdc,
  pf_fi B v pos lyc Sc Wc rX memc mdc ->
  In (5, pos) (frames Sc) /\ 4096 <= pf_F v pos /\ pf_F v pos + fs_frame_bytes 5 <= alloc_ceiling /\
  pf_F v pos mod 32 = 0 /\ in_app (pf_F v pos) (fs_frame_bytes 5) /\ frame_addr lyc 5 pos = pf_F v pos.
Proof.
intros v pos lyc Sc Wc rX memc mdc (HJ & Hly & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 5 pos HAR Hin) as (H4 & Hc & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 5 pos HAR Hin) as (Hal & Happ & _).
unfold pf_F. rewrite <- Hly.
split; [exact Hin|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Happ | reflexivity].
Qed.

(* ============================== 3. the block at the cut ============================== *)
Lemma pb8bf_blk : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  pf_obj B v lyc Sc (rdW Wc memc) ->
  0 < p_c v /\ p_c v mod 16 = 0 /\ 4096 <= p_c v /\ p_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling /\
  (p_c v + seg_spec.SEG_C_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= p_c v) /\
  sa_addr (rdW Wc memc) (p_c v) seg_spec.SEG_C_SIZE /\
  (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= p_c v /\ p_c v + seg_spec.SEG_C_SIZE <= b + req_size m).
Proof.
intros v pos lyc Sc Wc rX memc mdc HCX HFI HOBJ.
destruct (pb8b_cblk B v pos lyc Sc Wc rX memc mdc HCX HFI HOBJ) as (Hc0 & Hc16 & H4 & Hcl & AC & HC & _).
pose proof (proj1 (proj1 HFI)) as HAR.
destruct (pb8bf_heap_bounds lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HC
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (b & m & Hin & Hb1 & Hb2 & Hb3 & Hb4 & Happ).
split; [lia|]. split; [exact Hc16|]. split; [exact H4|]. split; [exact Hcl|].
split.
{ unfold in_app, kLowShadowBeg, kHighMemBeg in Happ.
  destruct Happ as [_ [Hl | [Hh _]]]; [left | right]; lia. }
split; [exact AC|].
exists b, m. split; [exact Hin|]. split; lia.
Qed.
(* the shadow byte of a byte of the block lies below the allocator's ceiling and outside the block *)
Lemma pb8bf_sh_apart : forall v pos lyc Sc Wc rX memc mdc x, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  pf_obj B v lyc Sc (rdW Wc memc) -> p_c v <= x -> x < p_c v + seg_spec.SEG_C_SIZE ->
  SHADOW_OFF <= SHADOW_OFF + x / 8 < alloc_ceiling /\
  ~ (p_c v <= SHADOW_OFF + x / 8 < p_c v + seg_spec.SEG_C_SIZE).
Proof.
intros v pos lyc Sc Wc rX memc mdc x HCX HFI HOBJ Hx1 Hx2.
destruct (pb8b_cblk B v pos lyc Sc Wc rX memc mdc HCX HFI HOBJ) as (_ & _ & H4 & Hcl & _ & HC & _).
pose proof (proj1 (proj1 HFI)) as HAR.
destruct (pb8bf_heap_bounds lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HC
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (b & m & Hin & Hb1 & Hb2 & Hb3 & Hb4 & Happ).
pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold seg_spec.SEG_C_SIZE in *.
assert (Hs : SHADOW_OFF <= SHADOW_OFF + x / 8 < SHADOW_OFF + 2 ^ 44) by lia.
split; [unfold SHADOW_OFF in *; lia|].
intros Hin2. apply (pb8bf_band_not_app b (req_size m) (SHADOW_OFF + x / 8) Happ Hs). lia.
Qed.
End c1.

(* ============================== 4. the two u32 field reads ============================== *)
Lemma pb8bf_val_of_bytes : forall (W : world SEGS) mem a (f : list byte) v,
  (forall k, (k < 4)%nat -> rdW W mem (a + Z.of_nat k) = Some (bv_unsigned (nth k f ZB0))) ->
  f = Mem.le4 (Z_to_bv 64 v) -> 0 <= v < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) mem) a 4 v.
Proof.
intros W mem a f v Hb Hf Hv k Hk.
pose proof (Hb k Hk) as E. unfold aview in E.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:Eb; try rewrite Eb in E;
  cbn [option_map] in E; [|discriminate].
injection E as E. f_equal. apply bv_eq. rewrite E, Hf. f_equal.
exact (pb8bf_le4_byte v k Hk Hv).
Qed.
Lemma pb8bf_seen_word : forall (W : world SEGS) mem c cf (i : nat), sa_rconf (rdW W mem) c cf ->
  (i < length (rc_seg cf))%nat -> 0 <= c ->
  0 <= rs_seen_gen (nth i (rc_seg cf) rseg_d) < 2 ^ 32 /\
  val_mem SEGS (mrestrict (w_H W) mem) (seg_spec.rseg_addr c i + seg_spec.RS_SEEN_GEN) 4
    (rs_seen_gen (nth i (rc_seg cf) rseg_d)).
Proof.
intros W mem c cf i (bs & Hb & Henc) Hi Hc.
pose proof Henc as (HL & HN & HE & _).
destruct (HE i Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & Hf).
split; [exact Hv|].
apply (pb8bf_val_of_bytes W mem _ (seg_spec.fldz seg_spec.RS_SEEN_GEN 4 (seg_spec.fld (356 * i) 356 bs)) _);
  [|exact Hf|exact Hv].
intros k Hk.
unfold seg_spec.fldz. change (Z.to_nat seg_spec.RS_SEEN_GEN) with 352%nat. change (Z.to_nat 4) with 4%nat.
rewrite (pb8b_fld_nth 352 4 _ k ZB0 Hk), (pb8b_fld_nth (356 * i) 356 bs (352 + k) ZB0 ltac:(lia)).
unfold seg_spec.SEG_C_SIZE in HL.
assert (Hlt : (356 * i + (352 + k) < length bs)%nat) by lia.
pose proof (Hb _ Hlt) as E.
replace (seg_spec.rseg_addr c i + seg_spec.RS_SEEN_GEN + Z.of_nat k) with (c + Z.of_nat (356 * i + (352 + k)))
  by (unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_SEEN_GEN; lia).
exact E.
Qed.
Lemma pb8bf_gen_word : forall (W : world SEGS) mem c cf, sa_rconf (rdW W mem) c cf -> 0 <= c ->
  0 <= rc_gen cf < 2 ^ 32 /\ val_mem SEGS (mrestrict (w_H W) mem) (c + seg_spec.RC_GEN) 4 (rc_gen cf).
Proof.
intros W mem c cf (bs & Hb & Henc) Hc.
destruct Henc as (HL & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & Hf).
split; [exact Hv|].
apply (pb8bf_val_of_bytes W mem _ (seg_spec.fldz seg_spec.RC_GEN 4 bs) _); [|exact Hf|exact Hv].
intros k Hk.
unfold seg_spec.fldz.
assert (H4 : (k < Z.to_nat 4)%nat) by (change (Z.to_nat 4) with 4%nat; exact Hk).
rewrite (pb8b_fld_nth (Z.to_nat seg_spec.RC_GEN) (Z.to_nat 4) bs k ZB0 H4).
assert (HG0 : 0 <= seg_spec.RC_GEN) by (unfold seg_spec.RC_GEN; lia).
assert (Hlt : (Z.to_nat seg_spec.RC_GEN + k < length bs)%nat).
{ apply Nat2Z.inj_lt. rewrite Nat2Z.inj_add, Z2Nat.id by exact HG0.
  unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *. lia. }
pose proof (Hb _ Hlt) as E.
replace (c + seg_spec.RC_GEN + Z.of_nat k) with (c + Z.of_nat (Z.to_nat seg_spec.RC_GEN + k))
  by (rewrite Nat2Z.inj_add, Z2Nat.id by exact HG0; lia).
exact E.
Qed.

(* ============================== 5. the journal keeps after refuse ============================== *)
(* what a later state must agree on for the cut facts to hold there: the stack from s1 up, the text and its NUL,
   the unowned image bytes, the class-5 frame and its shadow *)
Definition pb8bf_keeps (v : pfv) (pos : Z) (Wc : world SEGS) memc (W2 : world SEGS) mem2 : Prop :=
  (forall a, pf_s1 v <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memc a) /\
  (forall i, 0 <= i <= Z.of_nat (length (p_s v)) -> rdW W2 mem2 (p_t v + i) = rdW Wc memc (p_t v + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW Wc memc a) /\
  (forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 \/
             pf_SH v pos <= a < pf_SH v pos + fs_frame_bytes 5 / 8 ->
     rdW W2 mem2 a = rdW Wc memc a).
Section c2. Context {fx : YK11.FPState}.
(* after a call made at sp = s1 whose footprint lies in the block c: its journal keeps the stack outside its
   window and footprint, the live blocks outside the footprint, the unowned image bytes and the entry's frames *)
Lemma pb8bf_keeps_call : forall v pos lyc Sc Wc rX memc mdc sc STKc FPc ly2 S2 (W2 : world SEGS) mem2 md2 k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STKc (pf_s1 v) FPc lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k ->
  (forall a, inFP FPc a -> p_c v <= a < p_c v + seg_spec.SEG_C_SIZE) -> ~ YI16.sink_open_fp FPc ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  pb8bf_keeps v pos Wc memc W2 mem2.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc STKc FPc ly2 S2 W2 mem2 md2 k (CX & FI & PO & _ & _) HJc NFP HCl HP2.
destruct (pb8bf_cx v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (pb8bf_frame v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (pb8bf_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- pb8bf_s1_eq in S1a, S1b, S1c, S1d.
pose proof (proj1 (proj1 FI)) as HAR.
destruct PO as (_ & _ & HT & _ & HC & _).
destruct (pb8bf_heap_bounds _ _ _ _ _ (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
  as (bt & mt & Hint & Hb1 & Hb2 & Hb3 & Hb4 & _).
destruct (pb8bf_heap_bounds _ _ _ _ _ (p_c v) seg_spec.SEG_C_SIZE HAR HC ltac:(unfold seg_spec.SEG_C_SIZE; lia))
  as (bc & mc & Hinc & Hc1 & Hc2 & Hc3 & Hc4 & Hcapp).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
split.
{ intros a Ha. apply F1; [lia | lia | intros Hf; apply NFP in Hf; unfold seg_spec.SEG_C_SIZE in *; lia]. }
split.
{ intros i Hi. replace (p_t v + i) with (bt + (p_t v + i - bt)) by lia.
  apply (F2 bt mt (p_t v + i - bt)); [exact Hint | exact (Permutation_in _ (Permutation_sym HP2) Hint) | lia |].
  intros Hf. apply NFP in Hf. unfold sa_disj, seg_spec.cstr_span in HDJ.
  pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)). lia. }
split.
{ intros a Ha Ho He. apply F3; [exact Ha | exact Ho | exact He |].
  apply fp_spares_closed; [exact HCl|].
  intros Hf. apply NFP in Hf. exact (blk_img SEGS B LAWS lyc Sc Wc memc mdc bc mc a HAR Hinc ltac:(lia) Ha). }
intros a Ha. apply (F4 5 pos a Hfin).
- unfold frame_rng, in_zr. cbn [fst snd]. rewrite HFE. unfold pf_SH in Ha. exact Ha.
- intros Hf. apply NFP in Hf. destruct Ha as [Ha | Ha].
  + pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bc mc 5 pos HAR Hinc Hfin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFE in Hd. unfold seg_spec.SEG_C_SIZE in *. lia.
  + unfold pf_SH, shadow_addr in Ha. rewrite E5 in Ha. change (2048 / 8) with 256 in Ha.
    pose proof (Z.div_lt_upper_bound (pf_F v pos) 8 (2 ^ 44 - 256) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (pf_F v pos) 8 ltac:(lia) ltac:(lia)).
    apply (pb8bf_band_not_app bc (req_size mc) a Hcapp); [lia|].
    unfold seg_spec.SEG_C_SIZE in *. lia.
Qed.
End c2.
(* after refuse: its footprint refuse_W lies in the block c (refusal[n], n_refusals, refused) *)
Lemma pb8bf_keeps_refuse : forall (fx : YK11.FPState) v pos lyc Sc Wc rX memc mdc sc cf ly2 S2 (W2 : world SEGS)
  mem2 md2 k,
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_refuse (pf_s1 v) (refuse_W (p_c v) cf) lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  pb8bf_keeps v pos Wc memc W2 mem2.
Proof.
intros fx v pos lyc Sc Wc rX memc mdc sc cf ly2 S2 W2 mem2 md2 k HB HJc HP2.
destruct (pb8bf_cx v (proj1 HB)) as (Hc0 & _).
apply (pb8bf_keeps_call (fx := fx) v pos lyc Sc Wc rX memc mdc sc STK_refuse (refuse_W (p_c v) cf) ly2 S2 W2 mem2
  md2 k HB HJc); [| exact (pb8bf_refuse_W_pos _ cf Hc0) | exact HP2].
intros a Ha. apply pb8bf_refuse_W_in_block in Ha. unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW,
  seg_spec.SEG_C_SIZE in *. lia.
Qed.

(* ============================== 6. pf_base across the call ============================== *)
(* the cut's facts at the state refuse returned: the journals' keeps carry each, except sa_ssp, which SSPX gives
   at that state's AR *)
Lemma pb8bf_base_move : forall (fx fx1 : YK11.FPState) v pos lyc Sc Wc rX memc mdc sc ly2 S2 (W2 : world SEGS) regs2
  mem2 md2,
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc sc ->
  fxrel fx fx1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] ly2 S2 W2 mem2 md2 0 ->
  ly2 = lyc -> (exists f, S2 = set_fs f Sc) -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  pb8bf_keeps v pos Wc memc W2 mem2 ->
  (forall r, In r [2; 3; 4; 8; 9; 20] -> getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base (fx := fx1) B v pos ly2 S2 W2 regs2 mem2 md2 sc.
Proof.
intros fx fx1 v pos lyc Sc Wc rX memc mdc sc ly2 S2 W2 regs2 mem2 md2 (CX & FI & PO & SL & FSH) Hfx HJ2 Hly2
  (f2 & HS2) HP2 (K1 & K2 & K3 & K4) KR.
destruct (pb8bf_cx v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (pb8bf_frame (fx := fx) v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (pb8bf_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- pb8bf_s1_eq in S1a, S1b, S1c, S1d.
destruct FI as (HJ & Hly & (f & HSf) & HPerm & HSV & HFLW & HFRM & HTF & HC8 & HRG).
destruct PO as (STR & AT & HT & AC & HC & CAT & LITS & ROD & SSP).
pose proof (proj1 HJ2) as HAR2. pose proof (proj1 HJ) as HAR.
pose proof alloc_ceiling_lt as Hac.
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
assert (ROD2 : arodata_okP SEGS RLO_A RHI_A B (rdW W2 mem2)).
{ intros a Hro Ho He. rewrite (K3 a (pb8bf_in_roP_img a Hro) Ho He). exact (ROD a Hro Ho He). }
split; [exact CX|].
split.
{ split; [exact HJ2|]. split; [rewrite Hly2; exact Hly|].
  split; [exists f2; rewrite HS2, HSf; reflexivity|].
  split; [exact (Permutation_trans HP2 HPerm)|].
  split.
  { intros j r Hj. rewrite <- (HSV j r Hj). apply rdword_ext. intros k Hk.
    pose proof (proj1 (nth_error_Some PF_SAVED j) ltac:(rewrite Hj; discriminate)) as Hj13.
    unfold PF_SAVED in Hj13. cbn [length] in Hj13.
    apply K1. lia. }
  split.
  { rewrite <- HFLW. apply rdword_ext. intros k Hk. apply K4. left. lia. }
  split; [exact (fxrel_frm0 fx fx1 HFRM Hfx)|].
  split; [exact HTF|].
  split.
  { apply (pb8bf_sl_move (rdW Wc memc) (rdW W2 mem2) (pf_s1 v) [(0xc8, p_c v)] HC8);
      [apply Forall_cons; [cbn [fst]; lia | apply Forall_nil] | lia | lia |].
    intros a Ha. apply K1. exact Ha. }
  unfold pf_rg in *. rewrite Forall_forall in HRG |- *. intros rv Hin.
  rewrite (KR (fst rv)); [exact (HRG rv Hin)|].
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin. }
split.
{ destruct (pb8bf_heap_bounds lyc Sc Wc memc mdc (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
    as (bt & mt & Hint & Hbt1 & Hbt2 & _ & _ & _).
  assert (HT2 : sa_heap B ly2 S2 (p_t v) (Z.of_nat (length (p_s v)) + 1)) by exact (pb8bf_heap_perm _ _ _ _ _ _ HP2 HT).
  assert (HC2 : sa_heap B ly2 S2 (p_c v) seg_spec.SEG_C_SIZE) by exact (pb8bf_heap_perm _ _ _ _ _ _ HP2 HC).
  split.
  { destruct STR as ((Hz & Hn) & _). split; [split; [|exact Hn]|].
    - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
      rewrite K2 by lia. exact (Hz i Hi).
    - intros x Hx. apply (AR_block_word_vis SEGS B ly2 S2 W2 mem2 md2 bt mt (p_t v + Z.of_nat (length (p_s v))) x HAR2).
      + exact (Permutation_in _ (Permutation_sym HP2) Hint).
      + lia.
      + lia. }
  split; [exact (pb8bf_heap_addr ly2 S2 W2 mem2 md2 _ _ HAR2 HT2 ltac:(lia))|].
  split; [exact HT2|].
  split; [exact (pb8bf_heap_addr ly2 S2 W2 mem2 md2 _ _ HAR2 HC2 ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
  split; [exact HC2|].
  split; [exact (pb8bf_cat_move _ W2 mem2 CAT K3)|].
  split; [intros x Hx; exact (pb8bf_lit_move _ W2 mem2 _ _ (LITS x Hx) K3)|].
  split; [exact ROD2|].
  exact (SSPX ly2 S2 W2 mem2 md2 HAR2). }
split.
{ apply (pb8bf_sl_move (rdW Wc memc) _ (pf_s1 v) _ SL (pb8bf_PF_SL_offs v pos)); [lia | lia |].
  intros a Ha. apply K1. exact Ha. }
intros i Hi. rewrite K4; [exact (FSH i Hi)|]. right. rewrite E5. change (2048 / 8) with 256. lia.
Qed.
(* cur_name's bytes are in the frame *)
Lemma pb8bf_nm_move : forall v pos (rd rd' : reader) nm, pf_nm rd (pf_F v pos + PF_O_CN) nm ->
  (forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 -> rd' a = rd a) ->
  pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros v pos rd rd' nm (f & Hb & He) K. exists f. split; [|exact He].
intros i Hi. destruct He as (Hl & _). rewrite Hl in Hi. rewrite K; [exact (Hb i ltac:(lia))|].
change (fs_frame_bytes 5) with 2048. unfold PF_O_CN. lia.
Qed.
(* a C string in buf and its 8-byte tail lie in the frame (buf = F + 0x40, 512 bytes, 0x40 + 512 + 8 < 2048) *)
Lemma pb8bf_str_move : forall v pos (rd rd' : reader) (q : Z) (l : list Z), sa_str rd q l ->
  pf_inb (pf_F v pos + PF_O_BUF) q l -> 4096 <= pf_F v pos ->
  (forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 -> rd' a = rd a) -> sa_str rd' q l.
Proof.
intros v pos rd rd' q l ((Hz & Hn) & Ht) (Hb1 & Hb2) HF K. unfold PF_O_BUF in *.
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity. rewrite E5 in K.
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite K by lia. exact (Hz i Hi).
- intros x Hx. pose proof (Z.mod_pos_bound (q + Z.of_nat (length l)) 8 ltac:(lia)).
  rewrite K by lia. exact (Ht x Hx).
Qed.

(* ============================== 7. the refuse site 0x88ef8 ============================== *)
Section c3. Context {fx : YK11.FPState}.
(* a C string in an object [F + lo, F + hi) of the class-5 frame whose shadow cells are 0 at the cut's scope:
   an argument refuse can read (refuse_pre's sa_va_arg and refuse_va_locs' sa_fframe; pf_a6_k.v a6_obj_arg) *)
Lemma pb8bf_obj_arg : forall v pos lyc Sc Wc rX memc mdc sc (lo hi a3 : Z) (x : list Z) (Wl : list (Z * Z)),
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  32 <= lo -> lo mod 8 = 0 -> hi mod 8 = 0 -> hi <= 1088 ->
  (forall i, lo / 8 <= i < hi / 8 -> pf_shb sc i = 0) ->
  sa_str (rdW Wc memc) a3 x -> pf_F v pos + lo <= a3 -> a3 + Z.of_nat (length x) < pf_F v pos + hi ->
  Forall (fun iv => alloc_ceiling <= fst iv \/
    (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= fst iv /\ snd iv <= b + req_size m)) Wl ->
  sa_va_arg (rdW Wc memc) Wl (w64 a3) (SegModel.AS x) /\
  (sa_heap B lyc Sc (bv_unsigned (w64 a3)) (Z.of_nat (length x) + 1) \/
   sa_fframe lyc Sc (bv_unsigned (w64 a3)) (Z.of_nat (length x) + 1)).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc lo hi a3 x Wl (CX & FI & PO & SL & FSH) Hlo Hlo8 Hhi8 Hhi Hcell Hstr Hb1 Hb2
  HWl.
destruct (pb8bf_frame v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (proj1 (proj1 FI)) as HAR.
pose proof alloc_ceiling_lt as Hac.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
assert (Hu : bv_unsigned (w64 a3) = a3) by (apply pb8bf_w64_u; lia).
rewrite Hu.
assert (Hm8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
pose proof (Z.div_mod hi 8 ltac:(lia)) as Dhi. pose proof (Z.div_mod lo 8 ltac:(lia)) as Dlo.
(* the shadow cell of a byte of the frame *)
assert (HSC : forall y, pf_F v pos <= y < pf_F v pos + 2048 ->
  shadow_of_addr SHADOW_OFF y = pf_SH v pos + (y - pf_F v pos) / 8).
{ intros y Hy. unfold shadow_of_addr, pf_SH, shadow_addr.
  assert (Hy8 : y / 8 = (y - pf_F v pos) / 8 + pf_F v pos / 8).
  { rewrite <- Z.div_add by lia. f_equal. pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). lia. }
  lia. }
split.
- cbn [sa_va_arg]. rewrite Hu. split; [lia|]. split; [exact Hstr|].
  split; [assert (Hl : Z.of_nat (length x) < 1088) by lia; apply Nat2Z.inj_le; change (Z.of_nat 65535) with 65535; lia|].
  split.
  + unfold sa_addr. split; [lia|]. split; [lia|].
    split.
    { unfold amem_range. rewrite E5 in HFapp. unfold in_app in HFapp. destruct HFapp as [_ [Hl | [Hh1 _]]].
      - left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
      - right. unfold YG0f.kHighMemBeg, kHighMemEnd in *. lia. }
    split.
    * intros y Hy. exists 0. split; [|left; reflexivity].
      rewrite (HSC y) by lia. rewrite (FSH ((y - pf_F v pos) / 8)).
      -- f_equal. apply Hcell. split.
         ++ apply Z.div_le_mono; lia.
         ++ apply Z.div_lt_upper_bound; lia.
      -- split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
    * intros _ s Hs. unfold shadow_addr in Hs.
      assert (D1 : (pf_F v pos + 32) / 8 <= a3 / 8) by (apply Z.div_le_mono; lia).
      assert (D1' : (pf_F v pos + 32) / 8 = pf_F v pos / 8 + 4).
      { rewrite <- (Z.div_add (pf_F v pos) 4 8) by lia. reflexivity. }
      assert (D2 : (a3 + (Z.of_nat (length x) + 1) - 1) / 8 <= (pf_F v pos + 1087) / 8)
        by (apply Z.div_le_mono; lia).
      assert (D2' : (pf_F v pos + 1087) / 8 = pf_F v pos / 8 + 135).
      { rewrite (Z.div_mod (pf_F v pos) 8) at 1 by lia. rewrite Hm8, Z.add_0_r.
        replace (8 * (pf_F v pos / 8) + 1087) with (7 + (pf_F v pos / 8 + 135) * 8) by lia.
        rewrite Z.div_add by lia. change (7 / 8) with 0. lia. }
      assert (HSH4 : (SHADOW_OFF + pf_F v pos / 8) mod 4 = 0).
      { pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)). pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)).
        unfold SHADOW_OFF in *. rewrite Z.add_mod by lia.
        replace (pf_F v pos / 8) with (4 * (pf_F v pos / 32)) by lia.
        rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
      pose proof (Z.mod_pos_bound (SHADOW_OFF + a3 / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SHADOW_OFF + a3 / 8) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (SHADOW_OFF + (a3 + (Z.of_nat (length x) + 1) - 1) / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SHADOW_OFF + (a3 + (Z.of_nat (length x) + 1) - 1) / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SHADOW_OFF + pf_F v pos / 8) 4 ltac:(lia)).
      assert (Hs2 : pf_SH v pos <= s < pf_SH v pos + 144) by (unfold pf_SH, shadow_addr; lia).
      replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
      rewrite (FSH (s - pf_SH v pos)) by lia. discriminate.
  + unfold sa_apart_all. eapply Forall_impl; [|exact HWl]. cbv beta. intros iv [Hiv | (b & m & Hinb & Hb & Hm)].
    * left. unfold seg_spec.cstr_span.
      pose proof (Z.mod_pos_bound (- (a3 + Z.of_nat (length x) + 1)) 8 ltac:(lia)). lia.
    * pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hinb Hfin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFE, E5 in Hd. unfold seg_spec.cstr_span.
      pose proof (Z.mod_pos_bound (- (a3 + Z.of_nat (length x) + 1)) 8 ltac:(lia)).
      destruct Hd as [Hd | Hd]; [right | left]; lia.
- right. exists 5, pos. split; [exact Hfin|]. split; [lia|]. rewrite HFE, E5. lia.
Qed.
(* the name in buf (cells 8 .. 71 are 0 while buf is in scope, PF_SC_LINE) *)
Lemma pb8bf_buf_arg : forall v pos lyc Sc Wc rX memc mdc (a3 : Z) (x : list Z) (Wl : list (Z * Z)),
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  sa_str (rdW Wc memc) a3 x -> pf_inb (pf_F v pos + PF_O_BUF) a3 x ->
  Forall (fun iv => alloc_ceiling <= fst iv \/
    (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= fst iv /\ snd iv <= b + req_size m)) Wl ->
  sa_va_arg (rdW Wc memc) Wl (w64 a3) (SegModel.AS x) /\
  (sa_heap B lyc Sc (bv_unsigned (w64 a3)) (Z.of_nat (length x) + 1) \/
   sa_fframe lyc Sc (bv_unsigned (w64 a3)) (Z.of_nat (length x) + 1)).
Proof.
intros v pos lyc Sc Wc rX memc mdc a3 x Wl HB Hstr (Hb1 & Hb2) HWl. unfold PF_O_BUF in *.
apply (pb8bf_obj_arg v pos lyc Sc Wc rX memc mdc PF_SC_LINE 0x40 0x240 a3 x Wl HB); try lia; [| exact Hstr | exact HWl].
intros i Hi. change (0x40 / 8) with 8 in Hi. change (0x240 / 8) with 72 in Hi. unfold pf_shb.
destruct (i <? 4) eqn:E1; [apply Z.ltb_lt in E1; lia|].
destruct (i <? 6) eqn:E2; [apply Z.ltb_lt in E2; lia|].
destruct (i <? 8) eqn:E3; [apply Z.ltb_lt in E3; lia|].
destruct (i <? 72) eqn:E4; [|apply Z.ltb_ge in E4; lia].
reflexivity.
Qed.
End c3.
(* VERIFY rule 1j-bis, edge reac_segconf_parse_file -> refuse at 0x88ef8: refuse(c, ln + 1, F_twice, np), a2 =
   0x21620, a3 = np the header's name in buf (reloaded from slot 0xc0 at 0x88edc). INV_FOUND at the jal gives
   refuse_contract's premises over the call's registers regsc: arodata_okP and sa_ssp are pf_obj's at the call
   state, sa_frm0 pf_fi's, sa_room and the events the journal's frames / events clauses with pf_cx *)
Lemma pb8bf_refuse_site : forall (fx : YK11.FPState) n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i
  (regsc : bvmap 5 word),
  INV_FOUND (fx := fx) B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i ->
  getr regsc 10 = w64 (p_c v) -> getr regsc 11 = w64 (ln + 1) -> getr regsc 12 = w64 (seg_litA_rc F_twice) ->
  getr regsc 13 = w64 np -> spZ regsc = pf_s1 v ->
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\ 0 <= p_c v < 2 ^ 64 /\ 0 <= ln + 1 < 2 ^ 64 /\
  0 <= seg_litA_rc F_twice < 2 ^ 64 /\
  refuse_pre SEGS B seg_litA_rc gotwA guardA lyc Sc regsc (rdW Wc memc) (p_c v) (ln + 1) (seg_litA_rc F_twice)
    [getr regsc 13; getr regsc 14; getr regsc 15; getr regsc 16; getr regsc 17] cf (ln + 1) F_twice [AS name] /\
  sa_room Sc /\ st_nev Sc + EV_refuse <= EV_MAX.
Proof.
intros fx n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i regsc
  (HB & MID & ST & STR & INB & LEN & FIND & SLC & RG) R10 R11 R12 R13 Hsp.
pose proof HB as (CX & FI & PO & SL & FSH).
destruct (pb8bf_cx v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (pb8bf_frame (fx := fx) v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof FI as (HJ & Hly & _ & _ & _ & _ & HFRM & HTF & _ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & Hnev & _).
pose proof CX as (_ & _ & _ & Hc64 & _ & _ & _ & _ & _ & Hroom & Hev).
destruct PO as (_ & _ & _ & AC & HC & _ & LITS & ROD & SSP).
destruct ST as (RC & _ & CNT).
destruct MID as (Ho & _ & (Hno & _ & Hln & Hle)).
destruct pb8bf_fmt as (HF1 & HF2 & HF3).
pose proof (LITS F_twice HF2) as HLL.
assert (EL : seg_litA_rc F_twice = 0x21620) by (vm_compute; reflexivity).
assert (Hln1 : 0 <= ln + 1 < 2 ^ 31) by lia.
split; [exact ROD|].
split; [exact Hc64|].
split; [lia|].
split; [rewrite EL; lia|].
split.
- unfold refuse_pre.
  split; [lia|]. split; [exact Hc16|]. split; [exact RC|]. split; [exact HC|]. split; [exact AC|].
  split; [exact (pb8bf_cnt_pos cf (p_s v) o Ho CNT)|].
  split; [exact Hln1|]. split; [reflexivity|].
  split; [exact HF1|]. split; [exact (HF3 name)|].
  split; [destruct HLL as (Hp & _); lia|]. split; [reflexivity|]. split; [exact HLL|].
  assert (HWl : Forall (fun iv => alloc_ceiling <= fst iv \/
      (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= fst iv /\ snd iv <= b + req_size m))
      [(ly_stk_lo lyc, spZ regsc);
       (seg_spec.refusal_addr (p_c v) (length (rc_refusal cf)),
        seg_spec.refusal_addr (p_c v) (length (rc_refusal cf)) + seg_spec.RC_REFUSAL_LEN);
       (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)]).
  { destruct (pb8bf_heap_bounds _ _ _ _ _ (p_c v) seg_spec.SEG_C_SIZE HAR HC ltac:(unfold seg_spec.SEG_C_SIZE; lia))
      as (bc & mc & Hinc & Hc1 & Hc2 & _).
    destruct RC as (bs & _ & (_ & _ & _ & _ & HL8 & _)).
    constructor; [left; cbn [fst]; rewrite Hly; lia|].
    constructor; [right; exists bc, mc; split; [exact Hinc|]; cbn [fst snd];
      unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.SEG_C_SIZE in *; lia|].
    constructor; [right; exists bc, mc; split; [exact Hinc|]; cbn [fst snd];
      unfold seg_spec.RC_REFUSED, seg_spec.SEG_C_SIZE in *; lia|].
    constructor. }
  destruct (pb8bf_buf_arg (fx := fx) v pos lyc Sc Wc rX memc mdc np name _ HB STR INB HWl) as [HVA HLOC].
  split; [cbn [sa_va_args]; rewrite R13; exact (conj HVA I)|].
  split; [cbn [refuse_va_locs]; rewrite R13; exact (conj HLOC I)|].
  split; [exact HFRM|]. split; [exact SSP|].
  intros y Hy. apply LITS. unfold PARSE_FILE_LITS. apply in_or_app. right. exact Hy.
- split.
  + unfold sa_room. unfold sa_room_n in Hroom. rewrite Hfrs. cbn [app length]. lia.
  + unfold EV_refuse. unfold EV_reac_segconf_parse_file in Hev. lia.
Qed.

(* ============================== 8. the two cut rebuilds at JOIN ============================== *)
(* the registers of a cut, carried to a register file that agrees on them *)
Lemma pb8bf_rg_join : forall v pos o ln i np rX regs1,
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(19, seg_spec.rseg_addr (p_c v) i); (23, seg_spec.rseg_addr (p_c v) i + seg_spec.RS_SEEN_GEN)]) ->
  (forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 19] -> getr regs1 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr regs1 (Z_to_bv 5 13) = w64 (seg_spec.rseg_addr (p_c v) i) -> getr regs1 (Z_to_bv 5 23) = w64 np ->
  pf_rg regs1 (PF_RL v pos ++ PF_RM v o ln ++
               [(19, seg_spec.rseg_addr (p_c v) i); (13, seg_spec.rseg_addr (p_c v) i); (23, np)]).
Proof.
intros v pos o ln i np rX regs1 RG KR R13 R23.
unfold pf_rg in *. rewrite Forall_forall in RG |- *. intros rv Hin. cbv beta.
unfold PF_RL, PF_RM in Hin. cbn [app In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]];
  first [exact R13 | exact R23 |
         (rewrite KR by pb8b_in; apply RG; unfold PF_RL, PF_RM; pb8b_in)].
Qed.
Section c4. Context {fx : YK11.FPState}.
(* pf_base at another register file that agrees on pf_fi's six registers *)
Lemma pb8bf_base_regs : forall v pos lyc Sc Wc rX regs1 memc mdc sc,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  (forall r, In r [2; 3; 4; 8; 9; 20] -> getr regs1 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base B v pos lyc Sc Wc regs1 memc mdc sc.
Proof.
intros v pos lyc Sc Wc rX regs1 memc mdc sc (CX & FI & PO & SL & FSH) KR.
destruct FI as (HJ & Hly & HSf & HPerm & HSV & HFLW & HFRM & HTF & HC8 & HRG).
split; [exact CX|]. split; [|exact (conj PO (conj SL FSH))].
split; [exact HJ|]. split; [exact Hly|]. split; [exact HSf|]. split; [exact HPerm|]. split; [exact HSV|].
split; [exact HFLW|]. split; [exact HFRM|]. split; [exact HTF|]. split; [exact HC8|].
unfold pf_rg in *. rewrite Forall_forall in HRG |- *. intros rv Hin.
rewrite (KR (fst rv)); [exact (HRG rv Hin)|].
cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin.
Qed.
End c4.
(* the unequal arm of `bne a0,a1` (0x88ee0): nothing written, the cut's reader *)
Lemma pb8bf_join_same : forall (fx : YK11.FPState) n v pos lyc Sc Wc rX regs1 memc mdc cf nm o ln d np name i,
  INV_FOUND (fx := fx) B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i ->
  (forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 19] -> getr regs1 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr regs1 (Z_to_bv 5 13) = w64 (seg_spec.rseg_addr (p_c v) i) -> getr regs1 (Z_to_bv 5 23) = w64 np ->
  INV_B8B_JOIN (fx := fx) B n v pos lyc Sc Wc regs1 memc mdc cf nm o ln d np name i.
Proof.
intros fx n v pos lyc Sc Wc rX regs1 memc mdc cf nm o ln d np name i
  (HB & MID & ST & STR & INB & LEN & FIND & SLC & RG) KR R13 R23.
split.
{ apply (pb8bf_base_regs (fx := fx) v pos lyc Sc Wc rX regs1 memc mdc PF_SC_LINE HB).
  intros r Hr. apply KR. cbn [In] in Hr |- *. tauto. }
split; [exact MID|].
split.
{ destruct ST as (RC & NM & CNT). split; [exact RC|]. split; [exact NM|].
  exact (pb8bf_cnt_next cf (p_s v) o (proj1 MID) CNT). }
split; [exact STR|]. split; [exact INB|]. split; [exact LEN|].
split; [exact (pb8b_find_lt _ _ _ FIND)|].
exact (pb8bf_rg_join v pos o ln i np rX regs1 RG KR R13 R23).
Qed.
(* after the F_twice refusal (0x88ef8, return 0x88efc, then `mv a3,s3`): pf_base by the journals' keeps, c holds the
   refused record, cur_name and the name in buf kept (they are in the frame) *)
Lemma pb8bf_join_after : forall (fx fx1 : YK11.FPState) n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 md2c,
  INV_FOUND (fx := fx) B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i ->
  fxrel fx fx1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] ly2 S2 W2 mem2 md2 0 ->
  ajournal SEGS B STK_refuse (pf_s1 v) (refuse_W (p_c v) cf) lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2c EV_refuse ->
  sa_noalloc B lyc Sc ly2 S2 ->
  sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) F_twice [AS name]) ->
  (forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 19] -> getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr regs2 (Z_to_bv 5 13) = w64 (seg_spec.rseg_addr (p_c v) i) -> getr regs2 (Z_to_bv 5 23) = w64 np ->
  INV_B8B_JOIN (fx := fx1) B n v pos ly2 S2 W2 regs2 mem2 md2 (refuse cf (ln + 1) F_twice [AS name]) nm o ln d np
    name i.
Proof.
intros fx fx1 n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i ly2 S2 W2 regs2 mem2 md2 md2c
  (HB & MID & ST & STR & INB & LEN & FIND & SLC & RG) Hfx HJ2 HJR (HP2 & Hly2 & HS2) HRC KR R13 R23.
pose proof (pb8bf_keeps_refuse fx v pos lyc Sc Wc rX memc mdc PF_SC_LINE cf ly2 S2 W2 mem2 md2c EV_refuse HB HJR HP2)
  as K.
pose proof K as (K1 & K2 & K3 & K4).
pose proof HB as (CX & FI & _).
destruct (pb8bf_frame (fx := fx) v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
assert (KF : forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 -> rdW W2 mem2 a = rdW Wc memc a)
  by (intros a Ha; apply K4; left; exact Ha).
split.
{ apply (pb8bf_base_move fx fx1 v pos lyc Sc Wc rX memc mdc PF_SC_LINE ly2 S2 W2 regs2 mem2 md2 HB Hfx HJ2 Hly2 HS2
    HP2 K).
  intros r Hr. apply KR. cbn [In] in Hr |- *. tauto. }
split; [exact MID|].
split.
{ destruct ST as (RC & NM & CNT). split; [exact HRC|].
  split; [exact (pb8bf_nm_move v pos _ _ nm NM KF)|].
  exact (pb8bf_cnt_refuse_next cf (ln + 1) F_twice [AS name] (p_s v) o (proj1 MID) CNT). }
split; [exact (pb8bf_str_move v pos _ _ np name STR INB HF4 KF)|].
split; [exact INB|]. split; [exact LEN|].
split; [destruct (pb8b_refuse_seg cf (ln + 1) F_twice [AS name]) as (-> & _); exact (pb8b_find_lt _ _ _ FIND)|].
exact (pb8bf_rg_join v pos o ln i np rX regs2 RG KR R13 R23).
Qed.

(* ============================== 9. the frame chain at the refuse call ============================== *)
(* the achain premise of cl_callSF at a call made at s1 (pf_seg_B7_ch.v b7_chain): the prologue's record (ra at
   sp0 - 8, the entry s0 at sp0 - 16, pf_fi's pf_saved) pushed on afn_pre's chain, which the journal keeps above sp0 *)
Lemma pb8bf_chain : forall (fx : YK11.FPState) v pos lyc Sc Wc rX memc mdc sc,
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc sc ->
  exists ch1, achain lyc (rdW Wc memc) (pf_s1 v) (pf_sp0 v) ch1.
Proof.
intros fx v pos lyc Sc Wc rX memc mdc sc HB.
pose proof HB as (HCX & HFI & _).
destruct (pb8bf_cx v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
pose proof (pb8bf_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- pb8bf_s1_eq in S1a, S1b, S1c, S1d.
destruct (pb8bf_frame (fx := fx) v pos lyc Sc Wc rX memc mdc HFI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
destruct HFI as (HJ & Hly & _ & _ & HSV & _).
destruct HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & (fe & HPF) & _).
pose proof HPRE as (HAR0 & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal & _ & _ & _ & Hshi & H47' & _ & Htop & Htop2).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
subst lyc.
destruct HPF as (HRP & _). destruct HRP as (_ & _ & _ & (bc & mc & Hbc & Hc1 & Hc2) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR0 Hbc) as (_ & _ & Hcc & _ & _ & _ & Hm).
pose proof (req_size_pos mc (proj1 Hm)) as [_ Hreq].
pose proof STK_values as (_ & _ & _ & SPF & _).
change (spZ (p_regs v)) with (pf_sp0 v) in *.
destruct (Z_lt_le_dec (pf_sp0 v) (ly_top (p_ly v) - 16)) as [Hlt | Hge].
- exists ((pf_sp0 v, raZ (p_regs v), s0Z (p_regs v)) :: p_ch v).
  apply (achain_push (p_ly v) (rdW (p_W v) (p_mem v)) (rdW Wc memc) (pf_sp0 v) (s0Z (p_regs v)) (raZ (p_regs v))
    (p_ch v) (pf_s1 v) Hch).
  + lia.
  + intros a Ha. apply F1; [lia | rewrite SPF; lia |].
    intros Hf. apply pb8b_fp_in in Hf. unfold seg_spec.SEG_C_SIZE in *. lia.
  + assert (E1 : Z_to_bv 5 1 = (1%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HSV 0%nat 1 eq_refl) as H1. rewrite E1 in H1.
    replace (pf_sp0 v - 8 - 8 * Z.of_nat 0) with (pf_sp0 v - 8) in H1 by lia. exact H1.
  + assert (E8 : Z_to_bv 5 8 = (8%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HSV 1%nat 8 eq_refl) as H8. rewrite E8 in H8.
    replace (pf_sp0 v - 8 - 8 * Z.of_nat 1) with (pf_sp0 v - 16) in H8 by lia. exact H8.
  + exact Hra4.
  + lia.
  + pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16. rewrite D16.
    replace (16 * (pf_sp0 v / 16)) with (2 * (pf_sp0 v / 16) * 8) by lia. apply Z_mod_mult.
  + exact Hlt.
  + lia.
- exists []. left. split; [right; left; lia | reflexivity].
Qed.

End e.
End f.
End d.
