(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: ported from this harness's lib/A/Prog/check_reply_s1.v (the ASan walk, a working branch 91059853ab1) to the ASan+UBSan build fuzz_command.asan-ubsan (lib/B, entry 0x86e64): B's addresses, and the UBSan checks of `g_rec.reply[g_rec.reply_size - 1]` (0x86fcc-0x86fe0): the pointer-overflow branch (bltu) split and its taken arm refuted by the reply block's bounds; `snez` and `seqz` fold to 1 and 0 from the atoms' ranges, so the null checks fall through. *)
(* Modified by Theorem Labs, 2026-10: the first segment of check_reply's walk (fuzz_command.asan-ubsan, 0x86e64), from the
   entry to the memchr call 0x86ffc (cr_s1 : CR_MC_stmt -> CR_ENTRY_stmt, lib/B/Prog/check_reply_m.v), ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close) at origin/ossv/recipes
   c8557374ad2e, with the class-1 side-stack frame steps of A/ACa2.v (cgif_raw_addframe) and A/AChf.v (flushFrame):
   the entry seed cr_entry (check_reply_k.v); a token run over the prologue to the call of __asan_stack_malloc_1; the
   call through aj_stack_malloc_atS; the state after it (the kept stack and GOT regions, the frame F as a0's atom 46,
   fresh atoms 58 = F's flag cell and 59 = F's shadow, the frame's header, tail and shadow, g_rec's GOT word and
   fields, the reply's NUL byte); a plain run over the frame set-up; the frame's shadow made read-only and a token run
   over the inline checks #1..#4 to 0x86ffc; there the registers and the regions' fields give cr_mid and cr_regs_at. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/check_reply_s1.v, with its module paths, module names and numbers changed; 757 of its 876 lines of code are new or changed and 428 lines of the source are left out. *)
(* reac_segconf_declared on fuzz_segconf.asan (image A), segment S1 of its walk: reac_segconf_declared_d.v dc_S1P,
   from the entry 0x89854 to the loop head KL 0 (0x899c0) or to the join KX (0x89a78).
   The stretches, all run by the symbolic executor over the position-abstract listing (SegPaLib.v):
   - 0x89854 .. 0x89898: the 192-byte frame, the zero word at sp0 - 192, the 13 saved registers, s0 = sp0,
     sp = s1 = sp1 = (sp0 - 192) & -32 (atom 33, an alias of the `andi`);
   - the zero word's region is dropped (it is never read again and may lie under the slot sp1 + 16) and the
     slot region [sp1 + 8, sp1 + 88) is added;
   - 0x8989c .. 0x898cc: the argument spills, the two GOT loads, `beqz a2` decided by the flag cell's constant 1,
     the call of the class-1 frame entry (aj_stack_malloc_atS);
   - after the call: the frame F (atom 39, the call's a0), its flag cell (atom 51), its shadow SB + F / 8 (atom 52,
     the alias of `(a5 >> 3) + s4`), c->n (atom 53); `bnez a0` decided by F >= 4096 (the real-stack fallback
     0x898e0 .. 0x898f8 is not walked), the frame header and its 12 shadow bytes, `beqz s6` decided by c >= 4096;
   - the frame's shadow made read-only, then a token run over inline check 1 (0x89978 .. 0x89990): its one
     obligation is the shadow of [c + 0x2c80, c + 0x2c84), addressable because it lies in c's live heap block;
   - `blez a0` on c->n: nn = 0 runs to KX through 0x89a74, nn > 0 runs to KL 0. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c reac_segconf_declared_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- the symbolic state at the entry ---------- *)
(* atoms: 0-31 the registers, 32 the shadow base SB, 33 the realigned stack pointer sp1 = dc_sp1 sp0, 34 the
   use-after-return flag cell; 10 (a0 = c) is a 16-aligned heap pointer *)
Definition dcs1_zero : YP09.region := YP09.mkRegion (Some 2%nat) (-192) (-184) (-192) (-184) [].
Definition dcs1_saved : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [].
Definition dcs1_slot : YP09.region := YP09.mkRegion (Some 33%nat) 8 88 8 88 [].
Definition dcs1_atoms0 : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (33%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB SB 0);
   (34%nat, mkAF 0x10000 0x601000 2); (10%nat, PTR 4)].
Definition dcs1_alias0 : list (sv * sv) := [(SAlu ALU_AND (SOff 2 (-192)) (SLit (-32)), SOff 33 0)].
Definition dcs1_regions0 : smem :=
  [dcs1_zero; dcs1_saved; got_regionP; bcell_regionP 32; uar_got_regionP 34; uar_cell_regionP 34].
Definition dcs1_ss0 : sstate :=
  mkSS AF_reac_segconf_declared sr_atoms dcs1_regions0 None (mkFacts dcs1_atoms0 [] dcs1_alias0).
Definition dcs1_extra (sp0 uar : Z) : list word := map (Z_to_bv 64) [SB; dc_sp1 sp0; uar].
(* c->n, the 4 bytes at c + 0x2c80, as atom 53 *)
Definition dcs1_nreg : YP09.region :=
  YP09.mkRegion (Some 10%nat) 11392 11396 0 0 [YP09.mkChunk 11392 (CVal 4 (SOff 53 0))].
Definition dcs1_box (P : Prop) : Prop := P.
Ltac dcs1_inl := repeat (first [left; reflexivity | right]).

Lemma dcs1_sp1_and : forall sp0, 0 <= sp0 + -192 < 2 ^ 64 ->
  alu64 ALU_AND (Z_to_bv 64 (sp0 + -192)) (Z_to_bv 64 (-32)) = Z_to_bv 64 (dc_sp1 sp0).
Proof.
intros sp0 H. rewrite and_lit_Z. f_equal. rewrite zcanon_id by (unfold M64; lia).
change (zsigned64 (-32)) with (- 2 ^ 5). rewrite land_neg_pow2 by lia. unfold dc_sp1.
replace (sp0 - 192) with (sp0 + -192) by lia. reflexivity.
Qed.

(* ---------- c->n through the reader: rconf_enc's u32 field at RC_N ---------- *)
Lemma dcs1_nth_skipn : forall {A} (l : list A) j i d, nth i (skipn j l) d = nth (j + i) l d.
Proof.
induction l as [|a l IH]; intros [|j] i d; cbn; [destruct i; reflexivity | destruct i; reflexivity | reflexivity | apply IH].
Qed.
Lemma dcs1_le_bytes_nth : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth_error]. rewrite IH by lia. f_equal. f_equal.
  rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma dcs1_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold Mem.le4.
assert (Uv : bv_unsigned (Z_to_bv 64 v) = v).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. change (bv_modulus 64) with (2 ^ 64). lia. }
rewrite Uv. rewrite (nth_error_nth _ _ _ (dcs1_le_bytes_nth 4 v k Hk)).
rewrite Z_to_bv_unsigned. unfold bv_wrap, le_byte. change (bv_modulus 8) with 256.
rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat 4))) by (cbn; lia). reflexivity.
Qed.
Lemma dcs1_fldz_val : forall (rd : reader) a bs off n v,
  sa_bytes rd a bs -> 0 <= off -> off + Z.of_nat n <= Z.of_nat (length bs) ->
  (forall k, (k < n)%nat -> bv_unsigned (nth k (seg_spec.fldz off (Z.of_nat n) bs) ZB0) = le_byte v n k) ->
  sa_val rd (a + off) n v.
Proof.
intros rd a bs off n v HB H0 Hlen Hk j Hj.
replace (a + off + Z.of_nat j) with (a + Z.of_nat (Z.to_nat off + j)) by lia.
rewrite (HB (Z.to_nat off + j)%nat) by lia. f_equal.
rewrite <- (Hk j Hj). f_equal.
unfold seg_spec.fldz, seg_spec.fld. rewrite Nat2Z.id.
rewrite nth_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
symmetry. apply dcs1_nth_skipn.
Qed.
Lemma dcs1_rc_n : forall (rd : reader) c bs rc, sa_bytes rd c bs -> seg_spec.rconf_enc rc bs ->
  sa_val rd (c + seg_spec.RC_N) 4 (Z.of_nat (length (rc_seg rc))) /\ (length (rc_seg rc) <= 32)%nat.
Proof.
intros rd c bs rc HB HE. destruct (seg_query_facts.sq_rconf_len rc bs HE) as [L LS].
destruct HE as (_ & _ & _ & (Hv & HN) & _). split; [|exact LS].
apply (dcs1_fldz_val rd c bs seg_spec.RC_N 4 _ HB);
  [unfold seg_spec.RC_N; lia | change (Z.of_nat 4) with 4; unfold seg_spec.RC_N; lia |].
intros k Hk. change (Z.of_nat 4) with 4. rewrite HN. apply dcs1_le4_byte; [exact Hv | exact Hk].
Qed.

(* a signed compare of 0 with a small atom (`blez`) *)
Lemma dcs1_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
change (2 ^ 64 / 2) with (2 ^ 63).
rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma dcs1_bge0 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = (v <=? 0).
Proof.
intros E n v Hn Hv. cbn [branch_taken sv_denot]. rewrite Hn, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia.
unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia. rewrite !dcs1_swrap_small by lia.
destruct (Z.ltb_spec 0 v); destruct (Z.leb_spec v 0); try reflexivity; lia.
Qed.
Lemma dcs1_w64_m8 : Z_to_bv 64 18446744073709551608 = w64 (-8).
Proof. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma dcs1_val_mem_of_sa : forall H mem0 a n v,
  sa_val (aview SEGS H mem0) a n v -> val_mem SEGS (mrestrict H mem0) a n v.
Proof using.
intros H mem0 a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte SEGS H mem0 _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
(* reading the symbolic state back at a cut *)
Lemma dcs1_reg_atom : forall (H : word -> bool) E ss ms (r : bv 5) n,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof using.
intros H E ss ms r n HS Hr. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma dcs1_reg_sv : forall (H : word -> bool) E ss ms (r : bv 5) e,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> getr (ms_regs ms) r = sv_denot E e.
Proof using. intros H E ss ms r e HS Hr. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hr. reflexivity. Qed.
Lemma dcs1_rd_chunk8 : forall E H mem base off a n v cs,
  Forall (YP09.chunk_ok SEGS E (mrestrict H mem) base) cs -> In (YP09.mkChunk off (CVal 8 (SOff n 0))) cs ->
  a = base + off -> ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof using.
intros E H mem base off a n v cs Hc Hin -> Hn Hv. rewrite Forall_forall in Hc. specialize (Hc _ Hin).
apply rdword_of_val_mem; [|exact Hv].
apply (val_of_chunk_ok SEGS E _ base off 8 (SOff n 0) v Hc);
[cbn [sv_denot]; rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Hv | cbn; lia].
Qed.
Lemma dcs1_rd_chunk8_lit : forall E H mem base off a v cs,
  Forall (YP09.chunk_ok SEGS E (mrestrict H mem) base) cs -> In (YP09.mkChunk off (CVal 8 (SLit v))) cs ->
  a = base + off -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof using.
intros E H mem base off a v cs Hc Hin -> Hv. rewrite Forall_forall in Hc. specialize (Hc _ Hin).
apply rdword_of_val_mem; [|exact Hv].
apply (val_of_chunk_ok SEGS E _ base off 8 (SLit v) v Hc); [reflexivity | exact Hv | cbn; lia].
Qed.
(* the saved registers, from the chunks the prologue's stores left in the stack region *)
Lemma dcs1_saved_ok : forall E H mem sp0 (regs : bvmap 5 word) cs,
  Forall (YP09.chunk_ok SEGS E (mrestrict H mem) sp0) cs ->
  (forall j r, nth_error dc_saved j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
  (forall r, In r dc_saved -> ew E (Z.to_nat r) = getr regs (Z_to_bv 5 r)) ->
  forall j r, nth_error dc_saved j = Some r ->
  rdword (aview SEGS H mem) (sp0 - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr regs (Z_to_bv 5 r))).
Proof using.
intros E H mem sp0 regs cs Hc Hin Hv j r Hj.
apply (dcs1_rd_chunk8 E H mem sp0 (-8 - 8 * Z.of_nat j) _ (Z.to_nat r) _ cs Hc (Hin j r Hj)); [lia | |].
- rewrite (Hv r (nth_error_In _ _ Hj)). symmetry. apply Z_to_bv_bv_unsigned.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Rg. change (bv_modulus 64) with (2 ^ 64) in Rg. exact Rg.
Qed.

Section e.
Variable B : asyms.
Variables RLO RHI GOTW GUARD : Z.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* awr_ok reads only the regions' bases and windows *)
Lemma dcs1_awr_skel : forall Ex rs rs' STK sp0 FP bl0 blc fr0 lyx own,
  skeleton rs' = skeleton rs -> awr_ok SEGS B Ex rs STK sp0 FP bl0 blc fr0 lyx own ->
  awr_ok SEGS B Ex rs' STK sp0 FP bl0 blc fr0 lyx own.
Proof using.
intros Ex rs rs' STK sp0 FP bl0 blc fr0 lyx own Hsk H a Ha. apply H. exact (in_wrange_skeleton Ex rs' rs a Hsk Ha).
Qed.

(* ---------- the bytes a journal with an empty footprint keeps ---------- *)
Lemma dcs1_kept_blk : forall STK sp0 ly S W mem md own S' mem' md' k b m a,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly S' W mem' md' k ->
  In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly S') -> b <= a < b + req_size m ->
  rdW W mem' a = rdW W mem a.
Proof using.
intros STK sp0 ly S W mem md own S' mem' md' k b m a HJ H1 H2 Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
replace a with (b + (a - b)) by lia. apply (F2 b m (a - b) H1 H2); [lia | apply inFP_nil].
Qed.
Lemma dcs1_kept_frm : forall STK sp0 ly S W mem md own S' mem' md' k cid pos a,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly S' W mem' md' k ->
  In (cid, pos) (frames S) -> frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
  rdW W mem' a = rdW W mem a.
Proof using.
intros STK sp0 ly S W mem md own S' mem' md' k cid pos a HJ Hin Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
apply (F4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | apply inFP_nil].
Qed.
Lemma dcs1_kept_hi : forall STK sp0 ly S W mem md own S' mem' md' k a,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly S' W mem' md' k ->
  alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) -> rdW W mem' a = rdW W mem a.
Proof using.
intros STK sp0 ly S W mem md own S' mem' md' k a HJ Ha Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
apply (F1 a Ha Hn). apply inFP_nil.
Qed.
(* the table and the count cell, kept from the entry *)
Lemma dcs1_tab_kept : forall STK ly S W regs mem md ch tab max n t own S' mem' md' k,
  afn_pre SEGS B STK ly S W regs mem md ch ->
  vtab_pre SEGS B ly S W mem regs tab max n t ->
  ajournal SEGS B STK (spZ regs) [] ly S W mem md own ly S' W mem' md' k ->
  ablocks B ly S' = ablocks B ly S ->
  sa_rtab (rdW W mem') tab t /\ sa_val (rdW W mem') n 4 (Z.of_nat (length t)).
Proof using.
intros STK ly S W regs mem md ch tab max n t own S' mem' md' k HPRE HV HJ Eab.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HV as (Ht0 & Ht16 & (bs & HB & HE) & Htl & (b & m & Hin & Hb1 & Hb2) & _ & _ & Hn0 & Hn4 & Hnv & Hdst & _).
assert (Hin' : In (b, m) (ablocks B ly S')) by (rewrite Eab; exact Hin).
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & Hb4096 & Hbc & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
unfold seg_spec.RVLAN_SIZE in Hb2.
split.
- exists bs. split; [|exact HE]. intros i Hi.
  destruct HE as (HL & _). rewrite HL in Hi.
  rewrite (dcs1_kept_blk STK (spZ regs) ly S W mem md own S' mem' md' k b m (tab + Z.of_nat i) HJ Hin Hin') by lia.
  apply HB. rewrite HL. exact Hi.
- intros i Hi. rewrite <- (Hnv i Hi).
  destruct Hdst as [((cid & pos & Hfin & Hcid & Hf1 & Hf2) & _) | [((b' & m' & Hin2 & Hb1' & Hb2') & _) | (Hs1 & Hs2 & _)]].
  + apply (dcs1_kept_frm STK (spZ regs) ly S W mem md own S' mem' md' k cid pos _ HJ Hfin). lia.
  + assert (Hin2' : In (b', m') (ablocks B ly S')) by (rewrite Eab; exact Hin2).
    destruct (al_blocks _ _ LAWS ly S W mem md b' m' HAR Hin2) as (_ & _ & _ & _ & _ & _ & Hm').
    pose proof (req_size_pos m' ltac:(lia)) as [_ Hreq'].
    apply (dcs1_kept_blk STK (spZ regs) ly S W mem md own S' mem' md' k b' m' _ HJ Hin2 Hin2'). lia.
  + apply (dcs1_kept_hi STK (spZ regs) ly S W mem md own S' mem' md' k _ HJ); lia.
Qed.

(* ---------- the entry seed ---------- *)
Lemma dcs1_entry : forall STK W ly S regs mem md ch c,
  afn_pre SEGS B STK ly S W regs mem md ch -> 208 <= STK ->
  getr regs 10 = w64 c -> 4096 <= c <= 140737479966720 -> c mod 16 = 0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (dcs1_extra (spZ regs) (as_uar_cell B)))) dcs1_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_declared)) mem (seg_rom SEGS))).
Proof using TL TLF.
intros STK W ly S regs mem md ch c HPRE HSTK H10 Hc Hc16.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
set (sp0 := spZ regs) in *.
destruct (dc_sp1_facts sp0 Hal16) as (Hs1al & Hs1).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (dcs1_extra sp0 (as_uar_cell B)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (dcs1_extra sp0 (as_uar_cell B)) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth dcs1_extra map] in E32, E33, E34. clear EX.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12. pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
unfold kImgEnd in Hob0, Hob1, Hob12, Huar.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Hs1r : sp0 - 208 <= dc_sp1 sp0 <= sp0 - 192) by (destruct Hs1 as [Hq | Hq]; lia).
unfold dcs1_ss0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dcs1_regions0, dcs1_zero, dcs1_saved, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 34 0) (as_uar_cell B));
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
  + rewrite (VB 34%nat (as_uar_cell B) E34) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold dcs1_regions0, dcs1_zero, dcs1_saved, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 34%nat (as_uar_cell B) E34) by lia.
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Hob0 Hob1 Hob12 Huar Hsep Hs1r. clear. intros.
  unfold kImgEnd in *. rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  repeat split; first [ assumption | (apply or_comm; assumption) | lia ].
- split; [|split; [exact I|]].
  2: { cbn [f_alias alias_ok dcs1_alias0]. split; [|exact I]. cbn [sv_denot]. rewrite Usp, E33, Z.add_0_r, Z_to_bv_bv_unsigned.
       rewrite <- (dcs1_sp1_and sp0) by lia. reflexivity. }
  cbn [f_atoms atoms_ok dcs1_atoms0]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E33, E34, E10, H10. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Huar Huar4 Hs1al Hs1r Hal16 Hc Hc16. clear. unfold SB, kImgEnd. intros.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Hypothesis ASM : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ML : model_laws (as_universe B).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

(* ---------- what both cuts carry: the frame part, the kept part, the table ---------- *)
Lemma dcs1_close : forall c fpos S2 regs3 mem3 md3 fS2,
  dc_pre B STK_reac_segconf_declared RLO RHI GOTW GUARD c ->
  ajournal SEGS B STK_reac_segconf_declared (dc_sp0 c) [] (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(1, fpos)]
    (x_ly c) S2 (x_W c) mem3 md3 0 ->
  ablocks B (x_ly c) S2 = ablocks B (x_ly c) (x_S c) -> S2 = set_fs fS2 (x_S c) ->
  getr regs3 2 = w64 (dc_s1 c) -> getr regs3 3 = getr (x_regs c) 3 -> getr regs3 4 = getr (x_regs c) 4 ->
  getr regs3 8 = w64 (dc_sp0 c) -> getr regs3 9 = w64 (dc_s1 c) ->
  getr regs3 19 = w64 (SB + frame_addr (x_ly c) 1 fpos / 8) -> getr regs3 20 = w64 SB ->
  (forall j r, nth_error dc_saved j = Some r ->
    rdword (rdW (x_W c) mem3) (dc_sp0 c - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs c) (Z_to_bv 5 r)))) ->
  rdword (rdW (x_W c) mem3) (dc_s1 c + 16) = Some (frame_addr (x_ly c) 1 fpos) ->
  rdword (rdW (x_W c) mem3) (dc_s1 c + 24) = Some (frame_addr (x_ly c) 1 fpos) ->
  rdword (rdW (x_W c) mem3) (dc_s1 c + 32) = Some (dc_a1 c) ->
  rdword (rdW (x_W c) mem3) (dc_s1 c + 40) = Some (dc_a2 c) ->
  rdword (rdW (x_W c) mem3) (dc_s1 c + 48) = Some (dc_a3 c) ->
  rdword (rdW (x_W c) mem3) (frame_addr (x_ly c) 1 fpos + 120) = Some (flag_addr (x_ly c) 1 fpos) ->
  dc_fi B STK_reac_segconf_declared (dc_setpos c fpos) 0 (x_ly c) S2 (x_W c) regs3 mem3 md3 /\
  dc_un B (dc_setpos c fpos) (x_ly c) S2 /\ dc_tab (dc_setpos c fpos) (x_tb c) (x_W c) mem3.
Proof using.
intros c fpos S2 regs3 mem3 md3 fS2 HPRE HJ Eab ES2 R2 R3 R4 R8 R9 R19 R20 HSV W16 W24 W32 W40 W48 W120.
destruct HPRE as [cp_afn cp_rod cp_a0 cp_c64 cp_a1 cp_tab64 cp_a2 cp_max64 cp_a3 cp_n64 cp_dpre cp_room cp_nev].
pose proof cp_afn as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & _).
destruct cp_dpre as (_ & _ & _ & _ & _ & Hvt & _).
split; [|split].
- constructor.
  + change (ajournal SEGS B STK_reac_segconf_declared (dc_sp0 c) (dc_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
      ([(1, fpos)] ++ []) (x_ly c) S2 (x_W c) mem3 md3 (0 + 0)).
    eapply (ajournal_sub SEGS B LAWS pa_segs_low);
      [exact (ajournal_init SEGS B STK_reac_segconf_declared (dc_FP c) _ _ _ _ _ _ _ cp_afn) | exact HJ | lia | lia |].
    intros a Ha. exfalso. exact (inFP_nil a Ha).
  + exact R2.
  + rewrite R3. exact Hgp0.
  + rewrite R4. exact Htp0.
  + exact R8.
  + exact R9.
  + exact R19.
  + exact R20.
  + exact HSV.
  + exact W16.
  + exact W24.
  + exact W32.
  + exact W40.
  + exact W48.
  + exact W120.
- constructor.
  + cbn [dc_setpos x_ly x_S]. rewrite Eab. apply Permutation_refl.
  + reflexivity.
  + exists fS2. exact ES2.
- destruct (dcs1_tab_kept STK_reac_segconf_declared (x_ly c) (x_S c) (x_W c) (x_regs c) (x_mem c) (x_md c) (x_ch c)
    (x_tab c) (x_max c)
    (x_n c) (x_tb c) [(1, fpos)] S2 mem3 md3 0 cp_afn Hvt HJ Eab) as [T1 T2].
  destruct Hvt as (_ & _ & _ & Htl & _).
  split; [exact T1|]. split; [exact T2|]. cbn [dc_setpos x_tb x_max]. split; [lia | lia].
Qed.

Lemma dc_S1 : dc_S1P B STK_reac_segconf_declared RLO RHI GOTW GUARD.
Proof using TL TLF ML SMP ASM.
unfold dc_S1P. intros c HPRE HX HL.
assert (HSTK : STK_reac_segconf_declared = 12560) by reflexivity.
pose proof HPRE as HPRE2.
destruct HPRE2 as [cp_afn cp_rod cp_a0 cp_c64 cp_a1 cp_tab64 cp_a2 cp_max64 cp_a3 cp_n64 cp_dpre cp_room cp_nev].
pose proof cp_afn as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstkd & Hpres0 & Hch0 & HQT0).
pose proof Hstkd as (Hal16 & Hsp00 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof cp_dpre as (Hc0 & Hc16 & (bs & HBS & HENC) & (cb & cm & Hcin & Hcb1 & Hcb2) & Haddr & Hvt & Hdj1 & Hdj2 & Hssp).
destruct (dcs1_rc_n _ (x_c c) bs (x_rc c) HBS HENC) as [Hnval Hn32].
destruct (al_blocks _ _ LAWS _ _ _ _ _ cb cm HAR0 Hcin) as (Hcb16 & Hcb4096 & Hcbceil & Hcbapp & _ & _ & Hcm).
pose proof (req_size_pos cm ltac:(lia)) as [_ Hcreq].
unfold seg_spec.SEG_C_SIZE in Hcb2. unfold seg_spec.RC_N in Hnval.
set (nn := Z.of_nat (length (rc_seg (x_rc c)))) in *.
assert (Hnn : 0 <= nn <= 32) by (subst nn; lia).
assert (Hcr : 4096 <= x_c c /\ x_c c + 16616 <= alloc_ceiling) by lia.
pose proof (dcs1_entry STK_reac_segconf_declared (x_W c) (x_ly c) (x_S c) (x_regs c) (x_mem c) (x_md c) (x_ch c) (x_c c) cp_afn
  ltac:(lia) cp_a0 ltac:(lia) Hc16) as HS.
pose proof (ajournal_init SEGS B STK_reac_segconf_declared [] (x_ly c) (x_S c) (x_W c) (x_regs c) (x_mem c) (x_md c) (x_ch c)
  cp_afn) as HJ.
set (regs := x_regs c) in *. set (ly := x_ly c) in *. set (S := x_S c) in *.
set (W := x_W c) in *. set (mem := x_mem c) in *. set (md := x_md c) in *.
set (sp0 := spZ regs) in *.
destruct (dc_sp1_facts sp0 Hal16) as (Hs1al & Hs1).
remember (Eimg (Ereg regs (dcs1_extra sp0 (as_uar_cell B)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (dcs1_extra sp0 (as_uar_cell B)) (Z_to_bv 64 0))
  by (intros j Hj; rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth dcs1_extra map] in E32, E33, E34. clear HE EX.
set (sp1 := dc_sp1 sp0) in *.
assert (Hs1b : sp0 - 208 <= sp1 <= sp0 - 192) by (destruct Hs1 as [Hq | Hq]; lia).
assert (Ho16 : (sp1 - sp0) mod 16 = 0)
  by (destruct Hs1 as [Hq | Hq]; rewrite Hq; [replace (sp0 - 192 - sp0) with (-192) by lia
      | replace (sp0 - 208 - sp0) with (-208) by lia]; reflexivity).
assert (HS1R : 0 <= sp1 < 2 ^ 64) by lia.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (Usp1 : bv_unsigned (ew E 33) = sp0 + (sp1 - sp0)) by (rewrite E33, (unsigned_lit_small _ HS1R); lia).
assert (U33 : bv_unsigned (ew E 33) = sp1) by lia.
assert (E10 : ew E 10 = w64 (x_c c)) by (rewrite (EE 10%nat 10%bv eq_refl); exact cp_a0).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (pal_got_cell B TL) as HgcD.
assert (U241 : bv_unsigned (ew E 241) = VAL (A_OBJ 0)) by exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U253 : bv_unsigned (ew E 253) = VAL (A_OBJ 12)) by exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U242 : bv_unsigned (ew E 242) = VAL (A_OBJ 1)) by exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (palf_uar_img B TLF) as Huar.
unfold kImgEnd in Hob0, Hob1, Hob12, Huar.
assert (U34 : bv_unsigned (ew E 34) = as_uar_cell B)
  by (rewrite E34; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + AF_reac_segconf_declared)) with (Z_to_bv 64 (BASE + AF_reac_segconf_declared)).
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W) mem).
(* 0x89854 .. 0x89898: the frame, the zero word, the saved registers, sp1 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_segconf_declared + 0x48).
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
clear HF HFr HG.
lazymatch goal with |- context [with_vm_backing ?a ?b ?cc] => set (md0 := with_vm_backing a b cc) in *; clearbody md0 end.
(* the zero word's region out, the slot region [sp1 + 8, sp1 + 88) in *)
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  let rs := eval vm_compute in (tl (ss_mem ssx)) in
  assert (HS2 : st_ok_pi SEGS VAL E (mkSS (ss_pc ssx) (ss_regs ssx) rs (ss_resv ssx) (ss_facts ssx)) msx);
  [ apply st_ok_pi_submem; [exact HS
    | lazymatch goal with |- submem _ ?l => let l' := eval vm_compute in l in change (submem rs l') end; submem_tac
    | vm_compute; reflexivity ] | ] end.
clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  assert (Rok : region_ok SEGS E (ms_mem msx) dcs1_slot);
  [ unfold region_ok, dcs1_slot; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
    rewrite U33; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply Hpres1; lia | ];
  assert (Rdj : all_disjoint E dcs1_slot (ss_mem ssx));
  [ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    unfold dcs1_slot; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite U33, Usp, U241, U253, U242, U34; unfold kImgEnd in *; repeat split; lia | ];
  pose proof (st_ok_pi_add_region E _ msx dcs1_slot HS eq_refl Rok Rdj) as HS2 end.
clear HS Rok Rdj. rename HS2 into HS.
lazymatch type of HS with st_ok_pi ?a ?b ?cc ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
(* 0x8989c .. 0x898cc: the spills, the GOT loads, beqz a2 on the flag cell's 1, the call of the frame entry *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
  eapply awr_ok_cons_stack_off with (n := 33%nat) (d := sp1 - sp0); [reflexivity | exact Usp1 | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
clear HF HFr HG.
lazymatch goal with |- context [with_vm_backing ?a ?b ?cc] => set (md1 := with_vm_backing a b cc) in *; clearbody md1 end.
pose proof (proj1 HJ) as HAR1.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR1) as (Kcell1 & _ & Kgot1 & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot1. rewrite (pal_cell B TL) in Kcell1.
apply (val_mem_of_rdword SEGS) in Kgot1. apply (val_mem_of_rdword SEGS) in Kcell1.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
pose proof (palf_sm B TLF 1 ltac:(cbn; tauto)) as HSM1. change (cs_stack_malloc 1) with SS___asan_stack_malloc_1 in HSM1.
rewrite HSM1.
pose proof (count_cid_le_length 1 (frames S)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs (pal_env B TL) ML SMP 1 (ASM fx) ltac:(lia) W (ms_regs msX) (ms_mem msX)
    STK_reac_segconf_declared sp0 [] ly S W mem md [] ly S md1 0 (sp1 - sp0) _ HJ) end.
  - unfold spZ at 1. rewrite R2. exact Usp1.
  - exact Ho16.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp0.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp0.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - change (fs_frames 1) with 8192. unfold sa_room in cp_room. lia. }
cbv beta. clear R1 R2 R3 R4 SHOK HSM1.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag
  & HK & HJ1 & (fS2 & ES2)).
pose proof (proj1 HJ2) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot2. rewrite (pal_cell B TL) in Kcell2.
apply (val_mem_of_rdword SEGS) in Kgot2. apply (val_mem_of_rdword SEGS) in Kcell2.
(* the state after the call: the slot, the saved registers, the shadow GOT word and cell *)
jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp1 | lia | lia | lia | lia | lia].
  - eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | lia | lia | lia | lia | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
      [exact U241 | exact Kgot1 | exact Kgot2 | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
      [exact U253 | exact Kcell1 | exact Kcell2 | lia]. }
specialize (HS2 HQ). clear HQ HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (Ev1 := havoc E 35 (map (getr regs2) CLOB)) in HS.
assert (HIM1 : img_env VAL A_LIM Ev1) by (apply img_env_havoc; [exact HEI | rewrite length_map; unfold A_TEXT; cbn; lia]).
(* the frame F, its flag cell FL, its shadow SB + F / 8 *)
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (al_flag _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (_ & _ & HFLapp & HFLce).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFoff.
assert (Hcin2 : In (cb, cm) (ablocks B ly S2)) by (rewrite Eab; exact Hcin).
pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 cb cm 1 fpos HAR2 Hcin2 Hfin2) as HdCF.
pose proof (blk_off_imgP B ly S W mem md cb cm HAR0 Hcin) as Hcoff.
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
unfold zdisjoint in HdCF. cbn [fst snd] in HdCF. red in HFoff, Hcoff.
assert (HFLb : 4096 <= FL < alloc_ceiling) by (clear - HFLapp HFLce; unfold in_app in HFLapp; lia).
assert (ZONES : dcs1_box ((F + 128 <= 0x10000 \/ (0x601000 <= F /\ F + 128 <= 0x7fff7000) \/ 0x10007fff8000 <= F) /\
  (cb + req_size cm <= 0x10000 \/ (0x601000 <= cb /\ cb + req_size cm <= 0x7fff7000) \/ 0x10007fff8000 <= cb) /\
  (cb + req_size cm <= F \/ F + 128 <= cb))).
{ unfold dcs1_box. clear - HFoff HFapp Hcoff Hcbapp HdCF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
clear HFoff HFapp Hcoff Hcbapp HdCF HFLapp.
assert (RF : 0 <= F < 2 ^ 64) by lia. assert (RFL : 0 <= FL < 2 ^ 64) by lia.
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
pose proof (Z.div_mod F 8 ltac:(lia)) as HF8d. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HF8m.
assert (E39a : ew Ev1 39 = Z_to_bv 64 F).
{ subst Ev1. unfold havoc, CLOB. cbn [ew map nth Nat.ltb Nat.leb Nat.sub]. exact Ha0. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 51 Ev1 ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 nn] HS
    ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc Ev1 51 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 nn]) as Ev2 eqn:HEv2 in HS.
assert (HIM2 : img_env VAL A_LIM Ev2) by (rewrite HEv2; apply img_env_havoc; [exact HIM1 | unfold A_TEXT; cbn; lia]).
assert (AG : forall k, (k < 35)%nat -> ew Ev2 k = ew E k)
  by (intros k Hk; rewrite HEv2, ew_havoc_old by lia; subst Ev1; apply ew_havoc_old; lia).
assert (E39 : ew Ev2 39 = Z_to_bv 64 F) by (rewrite HEv2, ew_havoc_old by lia; exact E39a).
assert (E51 : ew Ev2 51 = Z_to_bv 64 FL)
  by (rewrite HEv2; exact (ew_havoc_new Ev1 51 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 nn] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E52 : ew Ev2 52 = Z_to_bv 64 (SB + F / 8))
  by (rewrite HEv2; exact (ew_havoc_new Ev1 51 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 nn] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E53 : ew Ev2 53 = Z_to_bv 64 nn)
  by (rewrite HEv2; exact (ew_havoc_new Ev1 51 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 nn] 2 (Z_to_bv 64 0) ltac:(cbn; lia))).
clear HEv2 E39a.
assert (E32' : ew Ev2 32 = Z_to_bv 64 SB) by (rewrite AG by lia; exact E32).
assert (E10' : ew Ev2 10 = Z_to_bv 64 (x_c c)) by (rewrite AG by lia; exact E10).
assert (U39 : bv_unsigned (ew Ev2 39) = F) by (rewrite E39; apply unsigned_lit_small; lia).
assert (U51 : bv_unsigned (ew Ev2 51) = FL) by (rewrite E51; apply unsigned_lit_small; lia).
assert (U52 : bv_unsigned (ew Ev2 52) = SB + F / 8) by (rewrite E52; apply unsigned_lit_small; unfold SB; lia).
assert (U53 : bv_unsigned (ew Ev2 53) = nn) by (rewrite E53; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew Ev2 10) = x_c c) by (rewrite E10'; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew Ev2 2) = sp0) by (rewrite AG by lia; exact Usp).
assert (U33b : bv_unsigned (ew Ev2 33) = sp1) by (rewrite AG by lia; exact U33).
assert (U33c : bv_unsigned (ew Ev2 33) = sp0 + (sp1 - sp0)) by lia.
assert (V241 : bv_unsigned (ew Ev2 241) = VAL (A_OBJ 0)) by exact (HIM2 (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (V253 : bv_unsigned (ew Ev2 253) = VAL (A_OBJ 12)) by exact (HIM2 (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
(* facts: F a 32-aligned side-stack address, its shadow, c->n, and the shadow alias of the frame *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_fact Ev _ _ 39 (HPTR 5) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U39; change (2 ^ 5) with 32; lia)) as HS3 end.
clear HS. rename HS3 into HS.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HFd8 : F / 8 = 4 * (F / 32))
  by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_fact Ev _ _ 52 (mkAF (SB + 512) (SB + 2 ^ 44) 2) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U52; change (2 ^ 2) with 4; unfold SB;
          split; [lia|]; split; [rewrite HFd8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia;
          apply Z_mod_mult | lia])) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_fact Ev _ _ 53 (mkAF 0 32 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U53, Z.pow_0_r, Z.mod_1_r; lia)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 39 32 52 F SB E39 RF E32' E52)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi ?a ?b ?cc ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
unfold shadow_addr in HFSpres.
(* the regions: the frame with its flag pointer at 120, its shadow (writable for the set-up), c->n *)
assert (VFL : val_mem SEGS (mrestrict (w_H W) mem2) (F + 120) 8 FL).
{ replace (F + 120) with (F + 128 - 8) by lia. exact (val_mem_of_rdword SEGS _ _ _ _ Hflag). }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  assert (Rok : region_ok SEGS Ev (ms_mem msx) (fframe_region 39 51 1 []));
  [ unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
    change (fs_frame_bytes 1) with 128; rewrite U39;
    split; [lia|]; split; [lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
    | apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val SEGS Ev _ F (128 - 8) 8 (SOff 51 0) FL);
      [ cbn [sv_denot]; rewrite E51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside
      | replace (F + (128 - 8)) with (F + 120) by lia; exact VFL ] ] | ];
  assert (Rdj : all_disjoint Ev (fframe_region 39 51 1 []) (ss_mem ssx));
  [ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    unfold fframe_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    change (fs_frame_bytes 1) with 128; rewrite U39, U2, U33b, V241, V253; unfold dcs1_box in ZONES; unfold kImgEnd in *; repeat split; lia | ];
  pose proof (st_ok_pi_add_region Ev _ msx (fframe_region 39 51 1 []) HS eq_refl Rok Rdj) as HS3 end.
clear HS Rok Rdj. rename HS3 into HS.
lazymatch type of HS with st_ok_pi ?a ?b ?cc ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  assert (Rok : region_ok SEGS Ev (ms_mem msx) (fshadow_region 52 1 0 16 []));
  [ unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    change (fs_frame_bytes 1 / 8) with 16; rewrite U52;
    split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS); pose proof (proj1 (HFSpres o ltac:(lia))) as Hq;
      unfold SHADOW_OFF in Hq; unfold SB; exact Hq
    | apply Forall_nil ] | ];
  assert (Rdj : all_disjoint Ev (fshadow_region 52 1 0 16 []) (ss_mem ssx));
  [ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    unfold fshadow_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    change (fs_frame_bytes 1 / 8) with 16; change (fs_frame_bytes 1) with 128; rewrite U52, U39, U2, U33b, V241, V253;
    unfold dcs1_box in ZONES; unfold SB, kImgEnd in *; repeat split; lia | ];
  pose proof (st_ok_pi_add_region Ev _ msx (fshadow_region 52 1 0 16 []) HS eq_refl Rok Rdj) as HS3 end.
clear HS Rok Rdj. rename HS3 into HS.
lazymatch type of HS with st_ok_pi ?a ?b ?cc ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
assert (VNN : val_mem SEGS (mrestrict (w_H W) mem2) (x_c c + 11392) 4 nn).
{ eapply val_mem_entry_block; [exact HJ2 | exact Hcin | exact Hcin2 | lia | cbn; lia | intros x _; apply inFP_nil |].
  apply dcs1_val_mem_of_sa. exact Hnval. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  assert (Rok : region_ok SEGS Ev (ms_mem msx) dcs1_nreg);
  [ unfold region_ok, dcs1_nreg; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U10; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val SEGS Ev _ (x_c c) 11392 4 (SOff 53 0) nn);
    [ cbn [sv_denot]; rewrite E53, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside | exact VNN ] | ];
  assert (Rdj : all_disjoint Ev dcs1_nreg (ss_mem ssx));
  [ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    unfold dcs1_nreg; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite U10, U52, U39, U2, U33b, V241, V253; unfold dcs1_box in ZONES; unfold SB, kImgEnd in *; repeat split; lia | ];
  pose proof (st_ok_pi_add_region Ev _ msx dcs1_nreg HS eq_refl Rok Rdj) as HS3 end.
clear HS Rok Rdj. rename HS3 into HS.
lazymatch type of HS with st_ok_pi ?a ?b ?cc ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
(* 0x898d0 .. 0x89974: a5 = F, bnez a0 taken, the frame header, its 12 shadow bytes, beqz s6 not taken *)
paj_run_to_sh RUNTOP HS HJ2 (AF_reac_segconf_declared + 0x124).
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  eapply awr_ok_cons_gen with (n := 52%nat) (b := SB + F / 8); [reflexivity | exact U52 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 1, fpos.
    split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd]. fold F.
    change (fs_frame_bytes 1 / 8) with 16. unfold SB in Ha. unfold SHADOW_OFF. lia. }
  eapply awr_ok_cons_gen with (n := 39%nat) (b := F); [reflexivity | exact U39 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. change (fs_frame_bytes 1) with 128 in Ha.
    right; right; right; left. exists 1, fpos.
    split; [left; reflexivity|]. left. unfold in_zr, frame_rng. cbn [fst snd]. fold F.
    change (fs_frame_bytes 1) with 128. lia. }
  eapply awr_ok_cons_stack_off with (n := 33%nat) (d := sp1 - sp0); [reflexivity | exact U33c | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
  do 2 (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
lazymatch goal with |- context [with_vm_backing ?a ?b ?cc] => set (md3 := with_vm_backing a b cc) in *; clearbody md3 end.
clear HF HFr HG.
(* the frame's shadow read-only for the token run *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let r := eval vm_compute in (nth 1 rs dcs1_nreg) in
  pose proof (ast_ok_pi_set_region Ex ssx msx 1 r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx 1 r HS ltac:(vm_compute; reflexivity))
      ltac:(intros o Ho; lia))) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi ?a ?b ?cc ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
(* 0x89978 .. 0x89998: inline check 1 on c->n (its obligation: the shadow of c + 0x2c80, 4 bytes, from c's live
   block), the load of c->n; stops at blez *)
pose proof (proj1 HJ2) as HAR3.
assert (UBx : U Ev2 (SOff 32 0) = SHADOW_OFF) by (rewrite (U_atom Ev2 32 SB E32') by (unfold SB; lia); reflexivity).
assert (UF : U Ev2 (SOff 39 0) = F) by (apply U_atom; [exact E39 | lia]).
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H W) ?ms3) =>
  shok_auto_with SHOK (SOff 32 0) Ex (mrestrict (w_H W) (ms_mem ms3)) (@nil shent)
    ltac:(eapply (shent_app_of_frame SEGS B LAWS ly S2 W _ _ Ex (SOff 32 0) 39%nat F 1 fpos 0 128 _ HAR3 Hfin2 UBx UF);
      [fold F; lia | lia | fold F; change (fs_frame_bytes 1) with 128; lia])
end.
paj_run_tok RUN HS HJ2 SHOK Bspan.
{ try unfold ob_holds. try cbn [ob_x ob_n]. rewrite UBx. rewrite U_SOff, U10.
  rewrite zcanon_id by (unfold M64; lia).
  eapply (range_addressable_of_block SEGS B LAWS); [exact HAR3 | exact Hcin2 | lia | lia]. }
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
  do 2 (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]).
  eapply awr_ok_cons_gen with (n := 39%nat) (b := F); [reflexivity | exact U39 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. change (fs_frame_bytes 1) with 128 in Ha.
    right; right; right; left. exists 1, fpos.
    split; [left; reflexivity|]. left. unfold in_zr, frame_rng. cbn [fst snd]. fold F.
    change (fs_frame_bytes 1) with 128. lia. }
  eapply awr_ok_cons_stack_off with (n := 33%nat) (d := sp1 - sp0); [reflexivity | exact U33c | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
  do 2 (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
lazymatch goal with |- context [with_vm_backing ?a ?b ?cc] => set (md4 := with_vm_backing a b cc) in *; clearbody md4 end.
clear HF HFr HG.
(* the state at blez: its env, what the code after it may write *)
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (Ev3 := Ex) in * end.
assert (AG3 : forall k, (k < 1024)%nat -> ew Ev3 k = ew Ev2 k)
  by (intros k Hk; subst Ev3; rewrite ?ew_ewset_other by lia; reflexivity).
assert (AGE : forall k, (k < 35)%nat -> ew Ev3 k = ew E k) by (intros k Hk; rewrite AG3, AG by lia; reflexivity).
assert (F39 : ew Ev3 39 = Z_to_bv 64 F) by (rewrite AG3 by lia; exact E39).
assert (F51 : ew Ev3 51 = Z_to_bv 64 FL) by (rewrite AG3 by lia; exact E51).
assert (F52 : ew Ev3 52 = Z_to_bv 64 (SB + F / 8)) by (rewrite AG3 by lia; exact E52).
assert (F53 : ew Ev3 53 = w64 nn) by (rewrite AG3 by lia; exact E53).
assert (F32 : ew Ev3 32 = Z_to_bv 64 SB) by (rewrite AG3 by lia; exact E32').
assert (F10 : ew Ev3 10 = Z_to_bv 64 (x_c c)) by (rewrite AG3 by lia; exact E10').
assert (F33 : ew Ev3 33 = Z_to_bv 64 sp1) by (rewrite AGE by lia; exact E33).
assert (W39 : bv_unsigned (ew Ev3 39) = F) by (rewrite F39; apply unsigned_lit_small; lia).
assert (W10 : bv_unsigned (ew Ev3 10) = x_c c) by (rewrite F10; apply unsigned_lit_small; lia).
assert (W2 : bv_unsigned (ew Ev3 2) = sp0) by (rewrite AGE by lia; exact Usp).
assert (W33 : bv_unsigned (ew Ev3 33) = sp0 + (sp1 - sp0)) by (rewrite AGE by lia; exact Usp1).
assert (W33b : bv_unsigned (ew Ev3 33) = sp1) by lia.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
  assert (AWR3 : awr_ok SEGS B Ev3 (ss_mem ssx) STK_reac_segconf_declared sp0 [] (ablocks B ly S) (ablocks B ly S2) (frames S)
    ly [(1, fpos)]) end.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
  do 2 (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]).
  eapply awr_ok_cons_gen with (n := 39%nat) (b := F); [reflexivity | exact W39 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. change (fs_frame_bytes 1) with 128 in Ha.
    right; right; right; left. exists 1, fpos.
    split; [left; reflexivity|]. left. unfold in_zr, frame_rng. cbn [fst snd]. fold F.
    change (fs_frame_bytes 1) with 128. lia. }
  eapply awr_ok_cons_stack_off with (n := 33%nat) (d := sp1 - sp0); [reflexivity | exact W33 | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact W2 | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
  do 2 (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
(* the values every cut reads back *)
assert (Gev : forall r, In r dc_saved -> ew Ev3 (Z.to_nat r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. cbn in Hr. repeat (destruct Hr as [<- | Hr]; [rewrite AGE by (cbn; lia); apply EE; reflexivity |]). destruct Hr. }
assert (Garg : forall k (r : bv 5), (k < 35)%nat -> Z.of_nat k = bv_unsigned r ->
  ew Ev3 k = Z_to_bv 64 (bv_unsigned (getr regs r))).
{ intros k r Hk Hr. rewrite AGE by exact Hk. rewrite (EE k r Hr). symmetry. apply Z_to_bv_bv_unsigned. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* c->n <= 0, so c->n = 0: 0x89a74 stores 0 at 56(s1); the join KX *)
  rewrite (dcs1_bge0 Ev3 53 nn F53) in Hc by lia. apply Z.leb_le in Hc.
  assert (Hseg0 : rc_seg (x_rc c) = []) by (apply length_zero_iff_nil; subst nn; lia).
  paj_run_to_tok RUNTO HS HJ2 SHOK Bspan (AF_reac_segconf_declared + 0x224).
  { lazymatch type of AWR3 with awr_ok _ _ _ ?rsA _ _ _ _ _ _ _ _ =>
      apply (dcs1_awr_skel _ rsA); [vm_compute; reflexivity | exact AWR3] end. }
  lazymatch goal with |- context [with_vm_backing ?a ?b ?cc] => set (md5 := with_vm_backing a b cc) in *; clearbody md5 end.
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssK (restrict _ ?msK) =>
    let r2 := eval vm_compute in (nth 2 (ss_mem ssK) dcs1_nreg) in
    let r3 := eval vm_compute in (nth 3 (ss_mem ssK) dcs1_nreg) in
    let r4 := eval vm_compute in (nth 4 (ss_mem ssK) dcs1_nreg) in
    pose proof (st_ok_pi_region_nth Ev3 ssK _ 2 r2 HS ltac:(vm_compute; reflexivity)) as RFR;
    pose proof (st_ok_pi_region_nth Ev3 ssK _ 3 r3 HS ltac:(vm_compute; reflexivity)) as RSL;
    pose proof (st_ok_pi_region_nth Ev3 ssK _ 4 r4 HS ltac:(vm_compute; reflexivity)) as RSV;
    pose proof (dcs1_reg_atom (w_H W) Ev3 ssK msK 2 33 HS ltac:(vm_compute; reflexivity)) as G2;
    pose proof (dcs1_reg_atom (w_H W) Ev3 ssK msK 3 3 HS ltac:(vm_compute; reflexivity)) as G3;
    pose proof (dcs1_reg_atom (w_H W) Ev3 ssK msK 4 4 HS ltac:(vm_compute; reflexivity)) as G4;
    pose proof (dcs1_reg_atom (w_H W) Ev3 ssK msK 8 2 HS ltac:(vm_compute; reflexivity)) as G8;
    pose proof (dcs1_reg_atom (w_H W) Ev3 ssK msK 9 33 HS ltac:(vm_compute; reflexivity)) as G9;
    pose proof (dcs1_reg_atom (w_H W) Ev3 ssK msK 19 52 HS ltac:(vm_compute; reflexivity)) as G19;
    pose proof (dcs1_reg_atom (w_H W) Ev3 ssK msK 20 32 HS ltac:(vm_compute; reflexivity)) as G20;
    pmkst HS; set (regs5 := ms_regs msK) in *; set (mem5 := ms_mem msK) in * end.
  destruct RFR as (_ & _ & _ & CFR). destruct RSL as (_ & _ & _ & CSL). destruct RSV as (_ & _ & _ & CSV).
  cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in CFR, CSL, CSV.
  rewrite W39 in CFR. rewrite W33b in CSL. rewrite W2 in CSV.
  assert (P2 : getr regs5 2 = w64 (dc_s1 c)) by (rewrite G2; exact F33).
  assert (P3 : getr regs5 3 = getr (x_regs c) 3) by (rewrite G3, AGE by lia; apply EE; reflexivity).
  assert (P4 : getr regs5 4 = getr (x_regs c) 4) by (rewrite G4, AGE by lia; apply EE; reflexivity).
  assert (P8 : getr regs5 8 = w64 (dc_sp0 c))
    by (rewrite G8, AGE, (EE 2%nat 2%bv eq_refl) by lia; unfold w64, dc_sp0, spZ; symmetry; apply Z_to_bv_bv_unsigned).
  assert (P9 : getr regs5 9 = w64 (dc_s1 c)) by (rewrite G9; exact F33).
  assert (P19 : getr regs5 19 = w64 (SB + frame_addr (x_ly c) 1 fpos / 8)) by (rewrite G19; exact F52).
  assert (P20 : getr regs5 20 = w64 SB) by (rewrite G20; exact F32).
  assert (PSV : forall j r, nth_error dc_saved j = Some r ->
    rdword (rdW (x_W c) mem5) (dc_sp0 c - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs c) (Z_to_bv 5 r)))).
  { apply (dcs1_saved_ok Ev3 (w_H W) mem5 sp0 regs _ CSV); [|exact Gev].
    intros j r Hj. do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn; dcs1_inl |]).
    destruct j; cbn in Hj; discriminate. }
  assert (P16 : rdword (rdW (x_W c) mem5) (dc_s1 c + 16) = Some (frame_addr (x_ly c) 1 fpos))
    by (apply (dcs1_rd_chunk8 Ev3 (w_H W) mem5 sp1 16 _ 39 F _ CSL); [dcs1_inl | reflexivity | exact F39 | lia]).
  assert (P24 : rdword (rdW (x_W c) mem5) (dc_s1 c + 24) = Some (frame_addr (x_ly c) 1 fpos))
    by (apply (dcs1_rd_chunk8 Ev3 (w_H W) mem5 sp1 24 _ 39 F _ CSL); [dcs1_inl | reflexivity | exact F39 | lia]).
  assert (P32 : rdword (rdW (x_W c) mem5) (dc_s1 c + 32) = Some (dc_a1 c))
    by (apply (dcs1_rd_chunk8 Ev3 (w_H W) mem5 sp1 32 _ 11 _ _ CSL);
        [dcs1_inl | reflexivity | apply Garg; [lia | reflexivity] | apply bv_unsigned_in_range]).
  assert (P40 : rdword (rdW (x_W c) mem5) (dc_s1 c + 40) = Some (dc_a2 c))
    by (apply (dcs1_rd_chunk8 Ev3 (w_H W) mem5 sp1 40 _ 12 _ _ CSL);
        [dcs1_inl | reflexivity | apply Garg; [lia | reflexivity] | apply bv_unsigned_in_range]).
  assert (P48 : rdword (rdW (x_W c) mem5) (dc_s1 c + 48) = Some (dc_a3 c))
    by (apply (dcs1_rd_chunk8 Ev3 (w_H W) mem5 sp1 48 _ 13 _ _ CSL);
        [dcs1_inl | reflexivity | apply Garg; [lia | reflexivity] | apply bv_unsigned_in_range]).
  assert (P120 : rdword (rdW (x_W c) mem5) (frame_addr (x_ly c) 1 fpos + 120) = Some (flag_addr (x_ly c) 1 fpos))
    by (apply (dcs1_rd_chunk8 Ev3 (w_H W) mem5 F 120 _ 51 FL _ CFR); [dcs1_inl | reflexivity | exact F51 | lia]).
  destruct (dcs1_close c fpos S2 regs5 mem5 md5 fS2 HPRE HJ2 Eab ES2 P2 P3 P4 P8 P9 P19 P20 PSV P16 P24 P32 P40 P48 P120)
    as (FI & UN & TB).
  assert (Hres : dc_res (dc_setpos c fpos) = (0, x_tb c))
    by (unfold dc_res, r_declared; cbn [dc_setpos x_rc x_tb x_max]; rewrite Hseg0; reflexivity).
  change (SRr SEGS W (cfg_at SEGS (BASE + DC_KX) regs5 mem5 md5)
    (dc_post B STK_reac_segconf_declared (dc_setpos c fpos))).
  apply (HX fpos ly S2 W regs5 mem5 md5).
  split; [exact FI|]. split; [exact UN|]. rewrite Hres. split; [exact TB|].
  change (0 mod 2 ^ 64) with 0.
  apply (dcs1_rd_chunk8_lit Ev3 (w_H W) mem5 sp1 56 _ 0 _ CSL); [dcs1_inl | reflexivity | lia].
- (* c->n > 0: s7 = 0, 56(s1) = 0, the loop registers; the loop head KL 0 *)
  rewrite (dcs1_bge0 Ev3 53 nn F53) in Hc by lia. apply Z.leb_gt in Hc.
  assert (Hseg1 : (0 < length (rc_seg (x_rc c)))%nat) by (subst nn; lia).
  paj_run_to_tok RUNTO HS HJ2 SHOK Bspan (AF_reac_segconf_declared + 0x16c).
  { lazymatch type of AWR3 with awr_ok _ _ _ ?rsA _ _ _ _ _ _ _ _ =>
      apply (dcs1_awr_skel _ rsA); [vm_compute; reflexivity | exact AWR3] end. }
  lazymatch goal with |- context [with_vm_backing ?a ?b ?cc] => set (md5 := with_vm_backing a b cc) in *; clearbody md5 end.
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssK (restrict _ ?msK) =>
    let r2 := eval vm_compute in (nth 2 (ss_mem ssK) dcs1_nreg) in
    let r3 := eval vm_compute in (nth 3 (ss_mem ssK) dcs1_nreg) in
    let r4 := eval vm_compute in (nth 4 (ss_mem ssK) dcs1_nreg) in
    pose proof (st_ok_pi_region_nth Ev3 ssK _ 2 r2 HS ltac:(vm_compute; reflexivity)) as RFR;
    pose proof (st_ok_pi_region_nth Ev3 ssK _ 3 r3 HS ltac:(vm_compute; reflexivity)) as RSL;
    pose proof (st_ok_pi_region_nth Ev3 ssK _ 4 r4 HS ltac:(vm_compute; reflexivity)) as RSV;
    pose proof (dcs1_reg_atom (w_H W) Ev3 ssK msK 2 33 HS ltac:(vm_compute; reflexivity)) as G2;
    pose proof (dcs1_reg_atom (w_H W) Ev3 ssK msK 3 3 HS ltac:(vm_compute; reflexivity)) as G3;
    pose proof (dcs1_reg_atom (w_H W) Ev3 ssK msK 4 4 HS ltac:(vm_compute; reflexivity)) as G4;
    pose proof (dcs1_reg_atom (w_H W) Ev3 ssK msK 8 2 HS ltac:(vm_compute; reflexivity)) as G8;
    pose proof (dcs1_reg_atom (w_H W) Ev3 ssK msK 9 33 HS ltac:(vm_compute; reflexivity)) as G9;
    pose proof (dcs1_reg_atom (w_H W) Ev3 ssK msK 19 52 HS ltac:(vm_compute; reflexivity)) as G19;
    pose proof (dcs1_reg_atom (w_H W) Ev3 ssK msK 20 32 HS ltac:(vm_compute; reflexivity)) as G20;
    pose proof (dcs1_reg_atom (w_H W) Ev3 ssK msK 22 10 HS ltac:(vm_compute; reflexivity)) as G22;
    pose proof (dcs1_reg_sv (w_H W) Ev3 ssK msK 18 (SLit 18446744073709551608) HS ltac:(vm_compute; reflexivity)) as G18;
    pose proof (dcs1_reg_sv (w_H W) Ev3 ssK msK 21 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 11392) (SLit 3)) (SOff 32 0)) HS
      ltac:(vm_compute; reflexivity)) as G21;
    pose proof (dcs1_reg_sv (w_H W) Ev3 ssK msK 23 (SLit 0) HS ltac:(vm_compute; reflexivity)) as G23;
    pose proof (dcs1_reg_sv (w_H W) Ev3 ssK msK 24 (SOff 10 11392) HS ltac:(vm_compute; reflexivity)) as G24;
    pose proof (dcs1_reg_sv (w_H W) Ev3 ssK msK 25 (SOff 10 24) HS ltac:(vm_compute; reflexivity)) as G25;
    pose proof (dcs1_reg_sv (w_H W) Ev3 ssK msK 26 (SOff 39 32) HS ltac:(vm_compute; reflexivity)) as G26;
    pose proof (dcs1_reg_sv (w_H W) Ev3 ssK msK 27 (SOff 39 64) HS ltac:(vm_compute; reflexivity)) as G27;
    pmkst HS; set (regs5 := ms_regs msK) in *; set (mem5 := ms_mem msK) in * end.
  destruct RFR as (_ & _ & _ & CFR). destruct RSL as (_ & _ & _ & CSL). destruct RSV as (_ & _ & _ & CSV).
  cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in CFR, CSL, CSV.
  rewrite W39 in CFR. rewrite W33b in CSL. rewrite W2 in CSV.
  assert (P2 : getr regs5 2 = w64 (dc_s1 c)) by (rewrite G2; exact F33).
  assert (P3 : getr regs5 3 = getr (x_regs c) 3) by (rewrite G3, AGE by lia; apply EE; reflexivity).
  assert (P4 : getr regs5 4 = getr (x_regs c) 4) by (rewrite G4, AGE by lia; apply EE; reflexivity).
  assert (P8 : getr regs5 8 = w64 (dc_sp0 c))
    by (rewrite G8, AGE, (EE 2%nat 2%bv eq_refl) by lia; unfold w64, dc_sp0, spZ; symmetry; apply Z_to_bv_bv_unsigned).
  assert (P9 : getr regs5 9 = w64 (dc_s1 c)) by (rewrite G9; exact F33).
  assert (P19 : getr regs5 19 = w64 (SB + frame_addr (x_ly c) 1 fpos / 8)) by (rewrite G19; exact F52).
  assert (P20 : getr regs5 20 = w64 SB) by (rewrite G20; exact F32).
  assert (PSV : forall j r, nth_error dc_saved j = Some r ->
    rdword (rdW (x_W c) mem5) (dc_sp0 c - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs c) (Z_to_bv 5 r)))).
  { apply (dcs1_saved_ok Ev3 (w_H W) mem5 sp0 regs _ CSV); [|exact Gev].
    intros j r Hj. do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn; dcs1_inl |]).
    destruct j; cbn in Hj; discriminate. }
  assert (P16 : rdword (rdW (x_W c) mem5) (dc_s1 c + 16) = Some (frame_addr (x_ly c) 1 fpos))
    by (apply (dcs1_rd_chunk8 Ev3 (w_H W) mem5 sp1 16 _ 39 F _ CSL); [dcs1_inl | reflexivity | exact F39 | lia]).
  assert (P24 : rdword (rdW (x_W c) mem5) (dc_s1 c + 24) = Some (frame_addr (x_ly c) 1 fpos))
    by (apply (dcs1_rd_chunk8 Ev3 (w_H W) mem5 sp1 24 _ 39 F _ CSL); [dcs1_inl | reflexivity | exact F39 | lia]).
  assert (P32 : rdword (rdW (x_W c) mem5) (dc_s1 c + 32) = Some (dc_a1 c))
    by (apply (dcs1_rd_chunk8 Ev3 (w_H W) mem5 sp1 32 _ 11 _ _ CSL);
        [dcs1_inl | reflexivity | apply Garg; [lia | reflexivity] | apply bv_unsigned_in_range]).
  assert (P40 : rdword (rdW (x_W c) mem5) (dc_s1 c + 40) = Some (dc_a2 c))
    by (apply (dcs1_rd_chunk8 Ev3 (w_H W) mem5 sp1 40 _ 12 _ _ CSL);
        [dcs1_inl | reflexivity | apply Garg; [lia | reflexivity] | apply bv_unsigned_in_range]).
  assert (P48 : rdword (rdW (x_W c) mem5) (dc_s1 c + 48) = Some (dc_a3 c))
    by (apply (dcs1_rd_chunk8 Ev3 (w_H W) mem5 sp1 48 _ 13 _ _ CSL);
        [dcs1_inl | reflexivity | apply Garg; [lia | reflexivity] | apply bv_unsigned_in_range]).
  assert (P120 : rdword (rdW (x_W c) mem5) (frame_addr (x_ly c) 1 fpos + 120) = Some (flag_addr (x_ly c) 1 fpos))
    by (apply (dcs1_rd_chunk8 Ev3 (w_H W) mem5 F 120 _ 51 FL _ CFR); [dcs1_inl | reflexivity | exact F51 | lia]).
  destruct (dcs1_close c fpos S2 regs5 mem5 md5 fS2 HPRE HJ2 Eab ES2 P2 P3 P4 P8 P9 P19 P20 PSV P16 P24 P32 P40 P48 P120)
    as (FI & UN & TB).
  change (SRr SEGS W (cfg_at SEGS (BASE + DC_KL) regs5 mem5 md5)
    (dc_post B STK_reac_segconf_declared (dc_setpos c fpos))).
  apply (HL fpos (x_tb c) 0 ly S2 W regs5 mem5 md5).
  split; [exact FI|]. split; [exact UN|]. split; [exact TB|].
  split; [exact Hseg1|].
  split; [split; [reflexivity | lia]|].
  split.
  { unfold dc_lregs. cbn [dc_setpos x_c dc_F x_ly x_fpos]. unfold DC_RC_N, DC_IGN.
    split; [rewrite G23; reflexivity|].
    split; [rewrite G22, F10; unfold w64; f_equal; lia|].
    split; [rewrite G25; cbn [sv_denot]; rewrite W10; unfold w64; f_equal; lia|].
    split; [rewrite G24; cbn [sv_denot]; rewrite W10; unfold w64; f_equal; lia|].
    split; [rewrite G21; unfold w64; apply (denot_shx Ev3 10 32 11392 (x_c c) SB F10 F32); unfold SB; lia|].
    split; [rewrite G26; cbn [sv_denot]; rewrite W39; reflexivity|].
    split; [rewrite G27; cbn [sv_denot]; rewrite W39; reflexivity|].
    rewrite G18. exact dcs1_w64_m8. }
  apply (dcs1_rd_chunk8_lit Ev3 (w_H W) mem5 sp1 56 _ 0 _ CSL); [dcs1_inl | reflexivity | lia].
Qed.

End e.
End f.
End d.
