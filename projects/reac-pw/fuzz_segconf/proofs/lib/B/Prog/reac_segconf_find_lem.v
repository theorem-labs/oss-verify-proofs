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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 325 of its 378 lines of code are new or changed and 400 lines of the source are left out. *)
(* The pieces of the walk of reac_segconf_find on fuzz_segconf image B (fuzz_segconf.asan-ubsan, entry BASE +
   AF_reac_segconf_find = 0x89a84, 61 instructions, frame 64) that are not the run itself: the image-B numbers,
   the symbolic states of the three seeds (entry, loop head 0x89b08, epilogue 0x89b40), the byte bridges from
   the contract's reader forms (lib/B/Prog/SegABase.v) to the strcmp wrapper's (lib/B/Rt/RtDefs.v) and the
   arithmetic of B's loop counters. The image-B port of lib/A/Prog/reac_segconf_find.v (commit
   561c4bddbbdf, which holds that walk's step plan plan-reac_segconf_find.md (image A's walk record)); the loop's form is
   plugin-hostd/fuzz_command's image-B lib/B/Prog/rec_calls_equal.v (origin/ossv/recipes 501c0d516c69). Step plan:
   the unit record's Bwalks-G45-plans/plan-reac_segconf_find.md. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib SegObj SegGlob PaDenot PaSB PaCall PaLibG.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase PaArt PaNoChain
  reac_segconf_find_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Module LMem := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= image B's numbers ======================================= *)
(* The stack this call needs at image B, image B's instance file's SegInstB.STK_reac_segconf_find, under the name the
   proofs here and in reac_segconf_find.v use: its 64-byte frame (addi sp,sp,-64 at 0x89a84) and, below it, the
   strcmp wrapper's window (RtString.astrcmp_realizes asks ecall_pre_stk (2 * ESTACK) at 0x89b18, sp = entry
   sp - 64). *)
Notation STK_reac_segconf_find_B := SegInstB.STK_reac_segconf_find (only parsing).
(* the listing offsets of the cut points (BASE = 0x84dc0) *)
Definition FND_LH : Z := 0x4d48.   (* 0x89b08, the loop head: beqz s5 *)
Definition FND_EPI : Z := 0x4d80.  (* 0x89b40, the epilogue, a0 set *)
Definition FND_RA : Z := 0x4d5c.   (* 0x89b1c, the return address of the strcmp call *)
(* the frame: ra s0 s1 s2 s3 s4 s5 at sp0-8 .. sp0-56 *)
Definition fnd_saved : list Z := [1; 8; 9; 18; 19; 20; 21].
Definition fnd_spF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition fnd_SBF : afact := mkAF SB SB 0.
Definition fnd_Bx : sv := SOff 32 0.
(* c lies in a live heap block of 16616 bytes below the allocator ceiling *)
Definition FND_CHI : Z := 0x7fffff800000 - 16616.

(* ======================================= the symbolic states ======================================= *)
(* Entry. Atoms: 0..31 the registers at entry (10 = a0 = c, 11 = a1 = name); 32 the shadow base SB; 33 n = c->n;
   A_OBJ 0 the shadow-base GOT word (0xa3210), A_OBJ 12 its cell (0xac7b8). Regions: the 64-byte frame, the GOT
   word, the cell, c->n (c + 0x2c80, 4 bytes). *)
Definition fnd_creg : YP09.region :=
YP09.mkRegion (Some 10%nat) 0x2c80 0x2c84 0 0 [YP09.mkChunk 0x2c80 (CVal 4 (SOff 33 0))].
Definition fnd_facts0 : facts :=
mkFacts [(2%nat, fnd_spF); (10%nat, mkAF 4096 FND_CHI 4); (11%nat, mkAF 1 (2 ^ 63) 0); (32%nat, fnd_SBF);
(33%nat, mkAF 0 32 0)] [] [].
Definition fnd_ss_entry : sstate :=
mkSS AF_reac_segconf_find sr_atoms [stack_region 64; got_regionP; bcell_regionP 32; fnd_creg] None fnd_facts0.
Definition fnd_extra0 (n : Z) : list word := map (Z_to_bv 64) [SB; n].
(* Loop head: registers as atoms, no region; the counters are facts of the concrete registers *)
Definition fnd_ss_lh : sstate := mkSS FND_LH sr_atoms [] None (mkFacts [(2%nat, fnd_spF); (32%nat, fnd_SBF)] [] []).
(* Epilogue: the frame's seven saved words as atoms 32..38, sp = sp0 - 64 *)
Definition fnd_estack : YP09.region := YP09.mkRegion (Some 2%nat) 0 64 0 0
  (map (fun j => YP09.mkChunk (56 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 7)).
Definition fnd_ss_epi : sstate := mkSS FND_EPI sr_atoms [fnd_estack] None (mkFacts [(2%nat, fnd_spF)] [] []).

(* ===================================== byte lists and readers ===================================== *)
Lemma fnd_nth_fld : forall {A : Type} (bs : list A) k n i d, (i < n)%nat -> nth i (firstn n (skipn k bs)) d = nth (k + i) bs d.
Proof.
intros A bs k. revert bs. induction k as [|k IH]; intros bs n i d Hi.
- cbn [skipn Nat.add]. revert bs i Hi. induction n as [|n IHn]; intros bs i Hi; [lia|].
  destruct bs as [|x bs]; [destruct i; reflexivity|]. destruct i as [|i]; [reflexivity|].
  cbn [firstn nth]. apply IHn. lia.
- destruct bs as [|x bs].
  + cbn [skipn]. assert (H0 : firstn n (@nil A) = []) by (destruct n; reflexivity). rewrite H0. destruct i; reflexivity.
  + cbn [skipn]. rewrite (IH bs n i d Hi). reflexivity.
Qed.

(* byte k of the little-endian bytes of z (lib/Lib/Mem.v's le4 is Z_to_le_bytes 4) *)
Lemma fnd_zle_nth : forall n z k, (k < n)%nat -> 0 <= z ->
  nth k (Z_to_le_bytes n z) ZB0 = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk Hz; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (Z.of_nat 0) with 0. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
- rewrite IH by (first [lia | apply Z.shiftr_nonneg; lia]). rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma fnd_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (LMem.le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold LMem.le4. rewrite unsigned_lit_small by lia. rewrite fnd_zle_nth by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap, le_byte. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.

(* a u32 field (seg_spec.u32_enc) through the reader *)
Lemma fnd_u32_val : forall rd a bs off v, sa_bytes rd a bs -> 0 <= off -> (Z.to_nat off + 4 <= length bs)%nat ->
  seg_spec.u32_enc v (seg_spec.fldz off 4 bs) -> sa_val rd (a + off) 4 v.
Proof.
intros rd a bs off v HB Ho Hl (Hv & HF) k Hk.
assert (Hn : nth k (seg_spec.fldz off 4 bs) ZB0 = nth (Z.to_nat off + k) bs ZB0).
{ unfold seg_spec.fldz, seg_spec.fld. change (Z.to_nat 4) with 4%nat. apply fnd_nth_fld. exact Hk. }
specialize (HB (Z.to_nat off + k)%nat ltac:(lia)).
replace (a + off + Z.of_nat k) with (a + Z.of_nat (Z.to_nat off + k)) by lia.
rewrite HB, <- Hn, HF. f_equal. apply fnd_le4_byte; lia.
Qed.

(* the name of c->seg[k] (rconf_enc's entry k, rseg_enc's char[16] field at 0) is a C string at c + 356 k *)
Lemma fnd_name_strz : forall rd c bs rcs k, sa_bytes rd c bs -> seg_spec.rconf_enc rcs bs -> (k < length (rc_seg rcs))%nat ->
  sa_strz rd (c + 356 * Z.of_nat k) (rs_name (r_seg rcs k)) /\ (length (rs_name (r_seg rcs k)) < 16)%nat.
Proof.
intros rd c bs rcs k HB HE Hk.
destruct HE as (HL & HLS & HSEG & _).
destruct (HSEG k Hk) as (_ & (Hfl & Hsl & Hn0 & Hfs) & _).
unfold seg_spec.SEG_C_SIZE in HL.
change (nth k (rc_seg rcs) rseg_d) with (r_seg rcs k) in Hfl, Hsl, Hn0, Hfs.
set (s := rs_name (r_seg rcs k)) in *.
set (F := seg_spec.fld (356 * k) 356 bs) in *.
split; [|exact Hsl]. split; [|exact Hn0].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
assert (Hfi : nth i (seg_spec.zs (seg_spec.fld 0 16 F)) 0 = nth i (s ++ [0]) 0).
{ rewrite <- Hfs. symmetry.
  pose proof (fnd_nth_fld (seg_spec.zs (seg_spec.fld 0 16 F)) 0 (S (length s)) i 0 ltac:(lia)) as Hq.
  cbn [skipn Nat.add] in Hq. exact Hq. }
assert (Hfn : nth i (seg_spec.zs (seg_spec.fld 0 16 F)) 0 = bv_unsigned (nth (356 * k + i) bs ZB0)).
{ unfold seg_spec.zs.
  transitivity (nth i (map bv_unsigned (seg_spec.fld 0 16 F)) (bv_unsigned ZB0)); [reflexivity|].
  rewrite map_nth. f_equal. unfold seg_spec.fld at 1. rewrite fnd_nth_fld by lia. cbn [Nat.add].
  unfold F, seg_spec.fld. apply fnd_nth_fld. lia. }
specialize (HB (356 * k + i)%nat ltac:(lia)).
replace (c + 356 * Z.of_nat k + Z.of_nat i) with (c + Z.of_nat (356 * k + i)) by lia.
rewrite HB, <- Hfn, Hfi. reflexivity.
Qed.

(* the bytes after that name up to the next 8-byte boundary are bytes of c's 16616 *)
Lemma fnd_name_tail : forall rd c bs k len, sa_bytes rd c bs -> Z.of_nat (length bs) = 16616 -> (k < 32)%nat ->
  (len < 16)%nat -> sa_tail rd (c + 356 * Z.of_nat k + Z.of_nat len).
Proof.
intros rd c bs k len HB Hl Hk Hlen x Hx.
pose proof (Z.mod_pos_bound (c + 356 * Z.of_nat k + Z.of_nat len) 8 ltac:(lia)).
assert (Hx2 : c <= x < c + 16616) by lia.
specialize (HB (Z.to_nat (x - c)) ltac:(lia)). rewrite Z2Nat.id in HB by lia.
replace (c + (x - c)) with x in HB by lia. rewrite HB. discriminate.
Qed.

(* sub-ranges of a range the shadow says usable *)
Lemma fnd_ra_sub : forall rd q n q' n', range_addressable rd SHADOW_OFF q n -> q <= q' -> q' + n' <= q + n ->
  range_addressable rd SHADOW_OFF q' n'.
Proof. intros rd q n q' n' H H1 H2 x Hx. apply H. lia. Qed.
Lemma fnd_hull_sub : forall rd q n q' n', shadow_hull_vis rd q n -> q <= q' -> 0 < n' -> q' + n' <= q + n ->
  shadow_hull_vis rd q' n'.
Proof.
intros rd q n q' n' H H1 H0 H2 s Hs. apply H.
pose proof (shadow_mono q q' H1). pose proof (shadow_mono (q' + n' - 1) (q + n - 1) ltac:(lia)).
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ H3). pose proof (R8 _ _ H4). lia.
Qed.
Lemma fnd_mem_range_sub : forall q n q' n', amem_range q n -> q <= q' -> q' + n' <= q + n -> amem_range q' n'.
Proof. intros q n q' n' [H|[H H']] H1 H2; [left; lia | right; lia]. Qed.
Lemma fnd_addr_sub : forall rd q n q' n', sa_addr rd q n -> q <= q' -> 0 <= n' -> q' + n' <= q + n -> sa_addr rd q' n'.
Proof.
intros rd q n q' n' (Hq & Hn & Hm & Hra & Hhv) H1 H0 H2.
split; [lia|]. split; [lia|]. split; [exact (fnd_mem_range_sub q n q' n' Hm H1 H2)|].
split; [exact (fnd_ra_sub rd q n q' n' Hra H1 H2)|].
intros Hn'. apply (fnd_hull_sub rd q n q' n'); [apply Hhv; lia | lia | lia | lia].
Qed.

Lemma fnd_val_mem_of_sa : forall segs H (mem : word -> option byte) a n v,
  sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate].
cbn in Hv. injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
etransitivity; [symmetry; apply bv_wrap_small; apply bv_unsigned_in_range|]. f_equal. exact Hv.
Qed.
Lemma fnd_sa_of_val_mem : forall segs H (m0 : word -> option byte) x n v,
  val_mem segs (mrestrict H m0) x n v -> sa_val (aview segs H m0) x n v.
Proof.
intros segs H m0 x n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
transitivity (le_byte v n k mod 256); [reflexivity|]. unfold le_byte. apply Z.mod_mod. lia.
Qed.

(* every byte the reader gives is a byte value *)
Lemma fnd_zs_range : forall segs H mem a l, sa_zs (aview segs H mem) a l -> Forall (fun z => 0 <= z < 256) l.
Proof.
intros segs H mem a l HZ. apply Forall_nth. intros i d Hi.
rewrite (nth_indep l d 0) by exact Hi.
exact (sa_aview_rng segs H mem _ _ (HZ i Hi)).
Qed.

(* the wrapper's answer on the two byte strings is the model's strcmp on their values (seg_query_facts's
   sq_name_cmp over the contract's texts) *)
Lemma fnd_zb_eq : forall s1 s2, Forall (fun z => 0 <= z < 256) s1 -> Forall (fun z => 0 <= z < 256) s2 ->
  ~ In 0 s1 -> ~ In 0 s2 -> (seg_spec.zb s1 = seg_spec.zb s2 <-> SegModel.strcmp s1 s2 = 0).
Proof.
intros s1 s2 R1 R2 N1 N2.
apply (seg_query_facts.sq_name_cmp (seg_spec.zb s1) (seg_spec.zb s2) s1 s2);
  [apply sa_zs_zb; exact R1 | apply sa_zs_zb; exact R2 | exact N1 | exact N2].
Qed.

(* ===================================== the words of B's counters ===================================== *)
(* `not s3,s0` (xori -1): 2 ^ 64 - 1 - c *)
Lemma fnd_lxor_allones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx.
assert (E : 2 ^ 64 - 1 - x = Z.lnot x mod 2 ^ 64).
{ rewrite Z.lnot_eq_pred_opp. apply Z.mod_unique_pos with (q := -1); lia. }
rewrite E. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec. replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity.
rewrite Z.testbit_mod_pow2, Z.lnot_spec by lia.
destruct (Z.ltb_spec i 64).
- rewrite Z.ones_spec_low by lia. replace (i <? 64) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (Z.testbit x i); reflexivity.
- rewrite Z.ones_spec_high by lia. replace (i <? 64) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite (Z_testbit_high 64 x i) by lia. reflexivity.
Qed.
Lemma fnd_xor_m1 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite unsigned_lit_small by lia.
replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by (rewrite Z_to_bv_unsigned; reflexivity).
rewrite fnd_lxor_allones by lia. rewrite unsigned_lit_small by lia.
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma fnd_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
(* `sgtz a1,a0; neg a1,a1; and s4,a1,a0`: n when n > 0 *)
Lemma fnd_s4 : forall x, 0 < x < 2 ^ 63 ->
  alu64 ALU_AND (alu64 ALU_SUB (Z_to_bv 64 0) (alu64 ALU_SLT (Z_to_bv 64 0) (Z_to_bv 64 x))) (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
intros x Hx.
assert (H1 : alu64 ALU_SLT (Z_to_bv 64 0) (Z_to_bv 64 x) = Z_to_bv 64 1).
{ apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
  rewrite !fnd_swrap_small by lia. destruct (Z.ltb_spec 0 x); [reflexivity | lia]. }
rewrite H1.
assert (H2 : alu64 ALU_SUB (Z_to_bv 64 0) (Z_to_bv 64 1) = Z_to_bv 64 (2 ^ 64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
rewrite H2. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
change (2 ^ 64 - 1) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia.
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
(* `blez a0` (bge zero,a0) on n *)
Lemma fnd_bge0 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = (v <=? 0).
Proof.
intros E n v Hn Hv. cbn [branch_taken sv_denot]. rewrite Hn, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia.
unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia. rewrite !fnd_swrap_small by lia.
destruct (Z.ltb_spec 0 v); destruct (Z.leb_spec v 0); try reflexivity; lia.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section p.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
#[local] Notation LAWS := (YG0q.AR_laws_ok SEGS B).

(* every place sa_loc names (a live heap block, a live side-stack frame, image bytes) lies below the allocator
   ceiling, so below the stack window of this call *)
Lemma fnd_loc_below : forall ly S (W : world SEGS) mem md q n, AR SEGS B ly S W mem md -> sa_loc SEGS B ly S q n -> 0 < n ->
  0 <= q /\ q + n <= alloc_ceiling.
Proof using B.
intros ly S W mem md q n HAR [(b & m & Hin & Hb & Hq) | [(cid & pos & Hin & Hcid & Hlo & Hhi) | Himg]] Hn.
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hc & _).
  assert (Hr : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (H4096 & Hceil & _). lia.
- destruct (Himg q ltac:(lia)) as (Hq & _). destruct (Himg (q + n - 1) ltac:(lia)) as (Hq2 & _).
  pose proof (pa_segs_low _ Hq) as R1. pose proof (pa_segs_low _ Hq2) as R2.
  pose proof asan_consts as (C1 & _ & _ & _ & C5). rewrite C5 in R1, R2. lia.
Qed.

(* the runtime entries' read-only premise at a later state, from arodata_okP at the entry: every image byte lies
   below the stack window, which is all a call or a run of this walk writes *)
Lemma fnd_rom_at : forall rlo rhi (W : world SEGS) mem memc lo hi, arodata_okP SEGS rlo rhi B (rdW W mem) ->
  kept_out (rdW W mem) (rdW W memc) lo hi -> kImgEnd <= lo -> rt_rom_view SEGS B W memc.
Proof using B.
intros rlo rhi W mem memc lo hi HROD HK Hlo x Hx Ho He.
assert (Himg : in_img SEGS x) by (destruct Hx as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
pose proof (pa_img_range _ Himg) as HR. unfold kImgEnd in HR, Hlo. rewrite (HK x) by lia.
apply HROD; [left; exact Hx | exact Ho | exact He].
Qed.

(* a string as the contract states it at the entry (SegABase's reader forms), as the strcmp row's premises at a
   later state whose memory below the stack window is the entry's *)
Lemma fnd_str_call : forall (W : world SEGS) mem memc (regsc : bvmap 5 word) lo hi x s,
  sa_strz (rdW W mem) x s -> sa_tail (rdW W mem) (x + Z.of_nat (length s)) ->
  sa_addr (rdW W mem) x (Z.of_nat (length s) + 1) -> Z.of_nat (length s) + 1 < 2 ^ 32 -> 0 < x ->
  x + Z.of_nat (length s) + 1 <= alloc_ceiling -> alloc_ceiling <= lo -> lo <= spZ regsc - 2 * ESTACK ->
  kept_out (rdW W mem) (rdW W memc) lo hi ->
  astr_at SEGS W memc x (seg_spec.zb s) /\ aread_ok SEGS (2 * ESTACK) W regsc memc x (astr_len (seg_spec.zb s) + 1) /\
  atail_vis SEGS W memc (x + astr_len (seg_spec.zb s)).
Proof using B.
intros W mem memc regsc lo hi x s SX TX AX R32 Hx Hc Hlo Hsp HK.
pose proof asan_consts as (C1 & C2 & _). pose proof alloc_ceiling_value as [_ HAC].
assert (Hsp64 : spZ regsc < 2 ^ 64)
  by (unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regsc 2)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; lia).
assert (HE4 : ESTACK = 4096) by reflexivity.
assert (HL : astr_len (seg_spec.zb s) = Z.of_nat (length s)) by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
rewrite HL.
destruct (sa_strz_bytes SEGS (w_H W) mem x s SX) as (HB & HN & _).
assert (RD : forall a, x <= a < x + (Z.of_nat (length s) + 1) -> rdW W mem a <> None).
{ intros a Ha. specialize (HB (Z.to_nat (a - x)) ltac:(unfold seg_spec.zb; rewrite length_app, length_map; cbn [length]; lia)).
  rewrite Z2Nat.id in HB by lia. replace (x + (a - x)) with a in HB by lia. rewrite HB. discriminate. }
split; [|split].
- apply (astr_atR_view SEGS). apply (astr_atR_kept _ _ lo hi x (seg_spec.zb s) HK);
    [split; [exact HB | exact HN] | lia | unfold seg_spec.zb; rewrite length_map; lia | lia].
- apply (aread_ok_kept SEGS (2 * ESTACK) (2 * ESTACK) W regsc regsc mem memc lo hi x _ HK); [| lia | lia | lia | lia | lia].
  destruct AX as (A0 & A1 & A2 & A3 & A4).
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; split; [exact (RD a Ha) | unfold ascratch_stk; lia]|].
  split; [exact A2|]. split; [exact A3 | exact A4].
- assert (Hxe : 0 <= x + Z.of_nat (length s) < alloc_ceiling) by lia.
  pose proof (tail_below (x + Z.of_nat (length s)) alloc_ceiling Hxe HAC) as HTB.
  apply (atail_vis_kept SEGS W mem memc lo hi); [exact HK | exact TX | lia | lia | lia].
Qed.

Hypothesis TL : PALib B.

(* the entry state: registers as atoms of the entry registers, atom 32 = SB, atom 33 = n = c->n; the 64-byte frame
   writable; the shadow GOT word and cell (AR_const_law through PALib); c->n (the contract's rconf bytes) *)
Lemma fnd_entry_seed : forall (W : world SEGS) ly S regs mem md c name n,
  afn_pre_na SEGS B STK_reac_segconf_find_B ly S W regs mem md ->
  getr regs 10 = w64 c -> getr regs 11 = w64 name ->
  4096 <= c -> c + 16616 <= alloc_ceiling -> c mod 16 = 0 -> (c + 16616 <= 0x10000 \/ kImgEnd <= c) ->
  1 <= name <= 2 ^ 63 ->
  sa_val (rdW W mem) (c + 0x2c80) 4 n -> 0 <= n <= 32 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (fnd_extra0 n))) fnd_ss_entry
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_find)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS fnd_Bx [] (Eimg (Ereg regs (fnd_extra0 n))) (mrestrict (w_H W) mem).
Proof using B TL.
intros W ly S regs mem md c name n HPRE H10 H11 Hc Hcc Hc16 Hoff Hn Hval Hnr.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_reac_segconf_find_B = 8256) by reflexivity.
pose proof (pa_obj_img 0 ltac:(lia)) as O0. pose proof (pa_obj_img 12 ltac:(lia)) as O12.
pose proof (pal_got_cell B TL) as Ogc. unfold kImgEnd in O0, O12, Hoff.
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (fnd_extra0 n))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 name)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
split.
- unfold fnd_ss_entry. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region, got_regionP, bcell_regionP, fnd_creg.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) _ E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) _ E253) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat c E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ c 0x2c80 4 (SOff 33 0) n);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (fnd_val_mem_of_sa SEGS (w_H W) mem _ _ _ Hval).
  + apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, fnd_creg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) _ E241), (VB (A_OBJ 12) _ E253), (VB 10%nat c E10) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 HSTK Hstk0 Hc Hcc Hoff O0 O12 Ogc. clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [fnd_facts0 f_atoms atoms_ok]. unfold afact_ok, fnd_spF, fnd_SBF. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, E32, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB, FND_CHI.
    revert Hslo Hshi H47 Hceil Hal16 C1 HSTK Hstk0 Hc Hcc Hc16 Hn Hnr. clear. unfold spZ. intros.
    repeat match goal with |- _ /\ _ => split end; try lia; reflexivity.
- unfold sh_ok. constructor.
Qed.

(* the loop head 0x89b08: registers as atoms, atom 32 = SB, no region *)
Lemma fnd_lh_seed : forall (W : world SEGS) (regs1 : bvmap 5 word) mem1,
  2 ^ 46 <= spZ regs1 <= 2 ^ 47 -> spZ regs1 mod 16 = 0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [w64 SB])) fnd_ss_lh
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + FND_LH)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS fnd_Bx [] (Eimg (Ereg regs1 [w64 SB])) (mrestrict (w_H W) mem1).
Proof using B.
intros W regs1 mem1 Hsp Hal.
set (E := Eimg (Ereg regs1 [w64 SB])).
assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (subst E; rewrite (ew_Eimg_Ereg_nat regs1 _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold fnd_ss_lh. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, fnd_spF, fnd_SBF. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). change (2 ^ 4) with 16.
  rewrite Z.pow_0_r, Z.mod_1_r. repeat split; try lia.
Qed.
End p.
End k.
