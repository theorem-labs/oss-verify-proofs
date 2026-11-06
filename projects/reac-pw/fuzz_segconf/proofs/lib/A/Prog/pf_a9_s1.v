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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 883 of its 935 lines of code are new or changed and 401 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): stretch SA9_A of segment A9 of reac_segconf_parse_file's walk
   (lib/A/Prog/pf_a9_d.v): KEY 0x87fac -> REF3 0x87e74 (no '=') or K2 0x87fe4. Part of segment A9's proof,
   by the G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's image-A walk, one stretch of segment A9;
   the whole function's rule-24 line, its released-proof index output and the G3 walk owner's CONFIRM of
   2026-10-30T15:42:08Z are in the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md, reuse
   verdict none: written new).

   The code (the excerpt reac_segconf_parse_file.fuzz_segconf.asan.s in records/segp/dis/ at that commit):
     0x87fac addi a1, zero, 0x3d; 0x87fb0 mv a0, s7; 0x87fb4 jal strchr     s1_strchr_step (token run, then
                                                                            PaArt.aj_art_at with ASTRCHR)
     0x87fb8 ld s4, 0xb0(s1); 0x87fbc beqz a0
       a0 = 0: 0x88094 auipc / addi a2 (A_OBJ 40 = F_neither), 0x8809c ld s8, 0x90(s1), j 0x881c4,
               mv a0, s8; mv a1, s10; mv a3, s7; j 0x87e74 = REF3            s1_none (seed with a0 pinned to 0)
       a0 = eq: mv s8, a0; check 9 (store1 at eq, 0x87fc4 - 0x87fd0, slow path 0x88a34); sb zero, 0(s8);
               mv a0, s7; 0x87fdc jal trim                                 s1_found (token run with the shadow
                                                                            entry of eq, PaNoChain.cl_callS_wide
                                                                            with TRIM)
               0x87fe0 mv s7, a0 = K2                                      s1_k2
   The seeds: the slot s1 + 0xb0 (and s1 + 0x90 on the no-'=' arm) is a read-only region of atom 9 whose chunk
   is an extra atom holding cur (and c); the byte at eq is a one-byte writable region of atom 10 (trim_t.v's
   tf_ss form for the same check-and-store); the shadow base of check 9 is s6's own atom 22 (pf_fi).
   The transport across both calls and the store is pf_a9_s1_k.v's s1_move (pf_a5_k.v a5_move0): every write
   of the stretch is in a5_Wrx (the stack below s1, buf).
   Section hypotheses: TL (the runtime record, for aj_art_at's errno cell), SIGP (trim's call target), OBJ
   (the F_neither literal's atom), ASTRCHR (RtSeg row 6), TRIM (trim_c.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaSB PaNoChain PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  trim_c pf_pieces pf_a5_d pf_a5_k pf_a9_d pf_a9_f pf_a9_s1_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== small facts ============================== *)
Lemma s1_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v ->
  getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

Lemma s1_rg_eq : forall (rX rX' : bvmap 5 word) L,
  (forall r v, In (r, v) L -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) -> pf_rg rX L -> pf_rg rX' L.
Proof.
intros rX rX' L HE H. unfold pf_rg in *. rewrite Forall_forall in *. intros [r v] Hin. cbn [fst snd] in *.
rewrite (HE r v Hin). exact (H (r, v) Hin).
Qed.

Lemma s1_w64_mod : forall a, Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64).
Proof.
intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zmod_mod. reflexivity.
Qed.

Ltac s1_in := cbn [In app]; repeat (first [left; reflexivity | right]).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* every visible byte stays visible, from the same over the 64-bit range (aview reads through Z_to_bv 64) *)
Lemma s1_vis_all : forall (W W' : world SEGS) mem mem',
  (forall a, 0 <= a < 2 ^ 64 -> rdW W mem a <> None -> rdW W' mem' a <> None) ->
  forall a, rdW W mem a <> None -> rdW W' mem' a <> None.
Proof.
intros W W' mem mem' H a Ha.
assert (E : forall (W0 : world SEGS) m, rdW W0 m a = rdW W0 m (a mod 2 ^ 64))
  by (intros W0 m; unfold aview, mbyte; rewrite (s1_w64_mod a); reflexivity).
rewrite E. rewrite E in Ha. apply H; [apply Z.mod_pos_bound; lia | exact Ha].
Qed.

(* a C string carried to a reader that agrees on its mapped span *)
Lemma s1_sa_str_keep : forall (rd rd' : reader) p s, (forall a, p <= a < s1_span p s -> rd' a = rd a) ->
  sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s HK [[Hz Hn] Ht].
pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as M.
split; [split|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite HK; [exact (Hz i ltac:(rewrite length_app; cbn [length]; lia))|].
  unfold s1_span. lia.
- exact Hn.
- intros y Hy. rewrite HK; [exact (Ht y Hy)|]. unfold s1_span. lia.
Qed.

(* a word read through the reader is a 64-bit value *)
Lemma s1_rdword_rng : forall (W : world SEGS) mem a v, rdword (rdW W mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros W mem a v H. unfold rdword in H.
destruct (rdW W mem a) as [b0|] eqn:E0; [|discriminate H].
destruct (rdW W mem (a + 1)) as [b1|] eqn:E1; [|discriminate H].
destruct (rdW W mem (a + 2)) as [b2|] eqn:E2; [|discriminate H].
destruct (rdW W mem (a + 3)) as [b3|] eqn:E3; [|discriminate H].
destruct (rdW W mem (a + 4)) as [b4|] eqn:E4; [|discriminate H].
destruct (rdW W mem (a + 5)) as [b5|] eqn:E5; [|discriminate H].
destruct (rdW W mem (a + 6)) as [b6|] eqn:E6; [|discriminate H].
destruct (rdW W mem (a + 7)) as [b7|] eqn:E7; [|discriminate H].
injection H as <-.
destruct (aview_byte SEGS _ _ _ _ E0) as (_ & _ & _ & R0).
destruct (aview_byte SEGS _ _ _ _ E1) as (_ & _ & _ & R1).
destruct (aview_byte SEGS _ _ _ _ E2) as (_ & _ & _ & R2).
destruct (aview_byte SEGS _ _ _ _ E3) as (_ & _ & _ & R3).
destruct (aview_byte SEGS _ _ _ _ E4) as (_ & _ & _ & R4).
destruct (aview_byte SEGS _ _ _ _ E5) as (_ & _ & _ & R5).
destruct (aview_byte SEGS _ _ _ _ E6) as (_ & _ & _ & R6).
destruct (aview_byte SEGS _ _ _ _ E7) as (_ & _ & _ & R7).
lia.
Qed.

(* the byte a run wrote into a one-byte written region, at a call stop (trim_t.v tr_wbyte over st_ok) *)
Lemma s1_wbyte : forall E ss ms (H : word -> bool) (n i : nat) Pz v,
  st_ok SEGS E ss (restrict H ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 v)]) ->
  bv_unsigned (ew E n) = Pz ->
  aview SEGS H (ms_mem ms) Pz = Some (bv_unsigned (sv_denot E v) mod 256).
Proof.
intros E ss ms H n i Pz v HS Hn HP.
pose proof (st_ok_region_nth E ss (restrict H ms) i _ HS Hn) as Hr.
pose proof (field_of_region_any E _ n Pz _ 0 1 0 1 0 1%N v Hr HP (or_introl eq_refl) ltac:(lia)) as V.
cbn [ms_mem restrict] in V. rewrite Z.add_0_r in V. change (2 ^ (8 * Z.of_N 1)) with 256 in V.
apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.

(* the store of a NUL at p + k into the C string s at p leaves its first k bytes a C string *)
Lemma s1_prefix_str : forall (rd rd' : reader) p s k,
  sa_str rd p s -> (k <= length s)%nat ->
  (forall a, p <= a < s1_span p s -> a <> p + Z.of_nat k -> rd' a = rd a) ->
  rd' (p + Z.of_nat k) = Some 0 ->
  sa_str rd' p (firstn k s).
Proof.
intros rd rd' p s k Hs Hk HK H0.
pose proof Hs as [[Hz Hn] Ht].
assert (Lk : length (firstn k s) = k) by (rewrite length_firstn; lia).
pose proof (Z.div_mod (p + Z.of_nat (length s)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
pose proof (s1_span_mono p s (p + Z.of_nat k) ltac:(lia)) as Hm.
apply s1_sa_str_of.
- intros i Hi. rewrite Lk in Hi. rewrite HK; [| unfold s1_span; lia | lia].
  rewrite (s1_str_nth rd p s i Hs ltac:(lia)). rewrite app_nth1 by lia. rewrite nth_firstn.
  replace ((i <? k)%nat) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
- rewrite Lk. exact H0.
- intros Hin. apply Hn. exact (a9_in_firstn k s 0 Hin).
- intros y Hy. rewrite Lk in Hy. rewrite HK; [| lia | lia].
  apply (s1_span_some rd p s y Hs). lia.
Qed.

(* the bytes of the C string s from k on, at p + k, when the reader agrees there *)
Lemma s1_suffix_str : forall (rd rd' : reader) p s k,
  sa_str rd p s -> (k <= length s)%nat ->
  (forall a, p + Z.of_nat k <= a < s1_span p s -> rd' a = rd a) ->
  sa_str rd' (p + Z.of_nat k) (skipn k s).
Proof.
intros rd rd' p s k Hs Hk HK.
pose proof Hs as [[Hz Hn] Ht].
assert (Lk : length (skipn k s) = (length s - k)%nat) by (rewrite length_skipn; lia).
pose proof (Z.div_mod (p + Z.of_nat (length s)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
apply s1_sa_str_of.
- intros i Hi. rewrite Lk in Hi. rewrite HK by (unfold s1_span; lia).
  replace (p + Z.of_nat k + Z.of_nat i) with (p + Z.of_nat (k + i)) by lia.
  rewrite (s1_str_nth rd p s (k + i) Hs ltac:(lia)). rewrite app_nth1 by lia.
  rewrite nth_skipn_add. reflexivity.
- rewrite Lk. rewrite HK by (unfold s1_span; lia).
  replace (p + Z.of_nat k + Z.of_nat (length s - k)) with (p + Z.of_nat (length s)) by lia.
  rewrite (s1_str_nth rd p s (length s) Hs ltac:(lia)). rewrite app_nth2 by lia. rewrite Nat.sub_diag.
  reflexivity.
- intros Hin. apply Hn. exact (a9_in_skipn k s 0 Hin).
- intros y Hy. rewrite Lk in Hy.
  replace (p + Z.of_nat k + Z.of_nat (length s - k)) with (p + Z.of_nat (length s)) in Hy by lia.
  rewrite HK by (unfold s1_span; lia). exact (Ht y Hy).
Qed.

(* trim's answer at lp: the C string at lp + trim_lead K is r_trim K (trim_c.v's post bytes and pfA_facts.v
   L_trim_holds; pf_a9_s2.v b2_trim_str for the string at lp) *)
Lemma s1_key_str : forall (W W2 : world SEGS) mem mem2 p K,
  sa_str (rdW W mem) p K ->
  sa_bytes (rdW W2 mem2) p
    (seg_spec.zb (firstn (seg_spec.trim_lead K + length (r_trim K)) K) ++ [seg_spec.ZERO]) ->
  (forall a, rdW W mem a <> None -> rdW W2 mem2 a <> None) ->
  sa_str (rdW W2 mem2) (p + Z.of_nat (seg_spec.trim_lead K)) (r_trim K).
Proof.
intros W W2 mem mem2 p K Hs HBY HV.
pose proof Hs as [[Hz Hn] Ht].
pose proof (L_trim_holds K Hn) as (L1 & L2 & L3).
set (ld := seg_spec.trim_lead K) in *. set (rt := r_trim K) in *.
assert (HR : forall j, (j < length K)%nat -> 0 <= nth j K 0 < 256).
{ intros j Hj. pose proof (s1_str_nth _ p K j Hs ltac:(lia)) as E. rewrite app_nth1 in E by exact Hj.
  exact (sa_aview_rng SEGS _ _ _ _ E). }
assert (HLB : length (seg_spec.zb (firstn (ld + length rt) K)) = (ld + length rt)%nat)
  by (unfold seg_spec.zb; rewrite length_map, length_firstn; lia).
assert (HNTH : forall i, (i < length rt)%nat -> nth i rt 0 = nth (ld + i) K 0).
{ intros i Hi. rewrite L2, nth_firstn.
  replace ((i <? length rt)%nat) with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  rewrite nth_skipn_add. reflexivity. }
apply s1_sa_str_of.
- intros i Hi.
  replace (p + Z.of_nat ld + Z.of_nat i) with (p + Z.of_nat (ld + i)) by lia.
  rewrite (HBY (ld + i)%nat) by (rewrite length_app, HLB; cbn [length]; lia). f_equal.
  rewrite app_nth1 by (rewrite HLB; lia). unfold seg_spec.zb, ZB0.
  rewrite (map_nth (Z_to_bv 8) (firstn (ld + length rt) K) 0 (ld + i)).
  rewrite nth_firstn. replace ((ld + i <? ld + length rt)%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite HNTH by exact Hi.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. apply HR. lia.
- replace (p + Z.of_nat ld + Z.of_nat (length rt)) with (p + Z.of_nat (ld + length rt)) by lia.
  rewrite (HBY (ld + length rt)%nat) by (rewrite length_app, HLB; cbn [length]; lia).
  rewrite app_nth2 by (rewrite HLB; lia). rewrite HLB, Nat.sub_diag. reflexivity.
- exact L3.
- intros y Hy. apply HV.
  replace (p + Z.of_nat ld + Z.of_nat (length rt)) with (p + Z.of_nat (ld + length rt)) in Hy by lia.
  apply (s1_span_some _ p K y Hs).
  pose proof (s1_span_mono p K (p + Z.of_nat (ld + length rt)) ltac:(lia)) as Hm. lia.
Qed.

Section e.
Variable B : asyms.
(* the runtime record of the image (aj_art_at's errno cell, pal_env) *)
Hypothesis TL : PALib B.
(* the listing's facts over the abstract instance (SegObj.v): call targets, object atoms *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
(* the interceptor owner's RtSeg row 6, at the listing's strchr trampoline *)
Hypothesis ASTRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strchr).
(* trim (lib/A/Prog/trim_c.v) at image A's numbers *)
Hypothesis TRIM : forall fx0 : YK11.FPState,
  trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the state after strchr returns (0x87fb8): a9_core, the line in buf at lp, the registers A9 keeps, s8 = c,
   s7 = lp, and strchr's answer in a0 *)
Definition s1_M1 (n : nat) (x : a9x) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) : Prop :=
  a9_core B n x lyc Sc Wc rX memc mdc /\
  a9_inbuf (rdW Wc memc) x (y_lp x) (a9_line x) /\
  pf_rg rX (A9_RC x ++ [(24, p_c (y_v x)); (23, y_lp x)]) /\
  ((getr rX (Z_to_bv 5 10) = w64 0 /\ strchr (a9_line x) EQ = None) \/
   (exists ei, strchr (a9_line x) EQ = Some ei /\ getr rX (Z_to_bv 5 10) = w64 (y_lp x + Z.of_nat ei))).

(* the seed at KEY: every register its own atom, no region (the run to the call reads and writes no memory) *)
Definition s1_ss0 : sstate := mkSS PF_KEY sr_atoms [] None (mkFacts [] [] []).

Ltac s1_kept HS EE :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?r) = getr _ (Z_to_bv 5 ?r) =>
    let H := fresh "Hk" in prreg HS (Z_to_bv 5 r) H; rewrite H; apply EE; reflexivity end.

(* ---------- KEY 0x87fac .. the strchr call 0x87fb4 .. its return 0x87fb8 ---------- *)
Lemma s1_strchr_step : forall n x lyc Sc Wc rX memc mdc (Q : world SEGS -> config -> Prop),
  a9_core B n x lyc Sc Wc rX memc mdc ->
  a9_inbuf (rdW Wc memc) x (y_lp x) (a9_line x) ->
  pf_rg rX (PF_RL (y_v x) (y_pos x) ++ PF_RM (y_v x) (y_o x) (y_ln x) ++ [(20, 0x20); (25, 9); (23, y_lp x)]) ->
  (forall rX1 memc1 mdc1, s1_M1 n x lyc Sc Wc rX1 memc1 mdc1 ->
     SRr SEGS Wc (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x540)) rX1 memc1 mdc1) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_KEY) rX memc mdc) Q.
Proof.
intros n x lyc Sc Wc rX memc mdc Q HC HLN HRG Kc.
pose proof HC as (HB & HM & HS0 & HL & HLT & HD0 & HDL).
destruct (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & HSHP).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof (s1_st_of_base B _ _ _ _ _ _ _ _ HB) as HST.
destruct (s1_stk B _ _ _ _ _ _ _ HST) as (Hal16 & Hceil & Hslo & Hs32 & Hs1r & Ho16).
destruct (s1_win B _ _ _ _ _ _ _ (2 * ESTACK) HST ltac:(unfold ESTACK; lia)) as (Hw1 & Hw2 & Hbud).
destruct (s1_frame_rng B _ _ _ _ _ _ _ HST) as (F1 & F2 & F3 & F4).
pose proof HB as (_ & (HJ & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
destruct HLN as [HSTR HINB].
pose proof HINB as [Hib1 Hib2]. unfold a9_buf, PF_O_BUF in Hib1, Hib2.
(* the seed *)
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg rX [])) s1_ss0
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_KEY)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold s1_ss0. apply pa_entry_st_ok_full;
    [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | split; [exact I | split; exact I]]. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg rX [])) k = getr rX r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
revert HS HEI EE. generalize (Eimg (Ereg rX [])) as E. intros E HS HEI EE.
assert (SHOK : sh_ok SEGS (SOff 22 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + PF_KEY)) with (Z_to_bv 64 (BASE + PF_KEY)).
(* 0x87fac addi a1, zero, 0x3d; 0x87fb0 mv a0, s7; 0x87fb4 jal the strchr trampoline *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_nil. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
assert (KV1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HFr HG.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
pmkst HS.
prreg HS (Z_to_bv 5 1) Q1. prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11.
(* the registers the run left as their own atoms *)
assert (QK : forall r v, In (r, v) (a5_FI B (y_v x) ++ A9_RC x ++ [(24, p_c (y_v x)); (23, y_lp x)]) ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r v Hr. unfold a5_FI, A9_RC, PF_RM in Hr. cbn [In app] in Hr.
  repeat (destruct Hr as [Hr | Hr]; [injection Hr as <- _; s1_kept HS EE |]). destruct Hr. }
assert (RG1 : pf_rg rX (a5_FI B (y_v x) ++ A9_RC x ++ [(24, p_c (y_v x)); (23, y_lp x)])).
{ apply a5_rg_app. split; [exact HFI|].
  eapply a5_rg_incl; [|exact HRG].
  intros rv Hrv. unfold A9_RC, PF_RL, PF_RM in *. cbn [In app] in *. tauto. }
pose proof (s1_rg_eq _ _ _ QK RG1) as RGm.
pose proof (proj1 (a5_rg_app _ _ _) RGm) as [RGmFI RGmA].
assert (Rs1 : getr (ms_regs ms) (Z_to_bv 5 2) = w64 (pf_s1 (y_v x)))
  by (apply (a5_rg_get _ _ _ _ RGmFI); unfold a5_FI; s1_in).
assert (Rgp : getr (ms_regs ms) (Z_to_bv 5 3) = w64 (as_gp B))
  by (apply (a5_rg_get _ _ _ _ RGmFI); unfold a5_FI; s1_in).
assert (Rtp : getr (ms_regs ms) (Z_to_bv 5 4) = w64 (as_tp B))
  by (apply (a5_rg_get _ _ _ _ RGmFI); unfold a5_FI; s1_in).
assert (R23 : getr rX (Z_to_bv 5 23) = w64 (y_lp x)) by (apply (a5_rg_get _ _ _ _ HRG); s1_in).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12). rewrite SPF in G1.
assert (Hlp : 0 <= y_lp x < 2 ^ 64) by lia.
assert (Q10' : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (y_lp x))
  by (rewrite Q10, (EE 23%nat (Z_to_bv 5 23) eq_refl); exact R23).
assert (Hsp1 : spZ (ms_regs ms) = pf_s1 (y_v x)).
{ unfold spZ. lazymatch goal with |- bv_unsigned (getr _ ?r) = _ => rewrite (s1_bvr _ r 2 _ eq_refl Rs1) end.
  unfold w64. apply unsigned_lit_small. lia. }
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)).
{ lazymatch goal with |- YK0s.ret_ok (getr _ ?r) => rewrite (s1_bvr _ r 1 _ eq_refl Q1) end.
  apply ret_ok_codeptr_v; [lia | reflexivity]. }
(* the cut's facts at the call: nothing was written *)
assert (HC1 : a9_core B n x lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv).
{ apply (s1_move B n x lyc Sc Wc rX memc mdc Sc Wc (ms_regs ms) (ms_mem ms) mdv HC HJ).
  - exists (st_fs Sc). destruct Sc; reflexivity.
  - apply Permutation_refl.
  - intros a Ha _. exact (KM1 a Ha).
  - exact KV1.
  - exact RGmFI. }
pose proof HC1 as (HB1 & _).
pose proof (s1_st_of_base B _ _ _ _ _ _ _ _ HB1) as HST1.
assert (HSTR1 : sa_str (rdW Wc (ms_mem ms)) (y_lp x) (a9_line x)).
{ apply (s1_sa_str_keep (rdW Wc memc)); [|exact HSTR].
  intros a Ha. apply KM1. pose proof (s1_span_mono (y_lp x) (a9_line x) (y_lp x + Z.of_nat (length (a9_line x)))
    ltac:(lia)) as Hs. unfold s1_span in *.
  pose proof (Z.div_mod (y_lp x + Z.of_nat (length (a9_line x))) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (y_lp x + Z.of_nat (length (a9_line x))) 8 ltac:(lia)). lia. }
destruct (s1_strchr_pre B _ _ _ _ _ _ _ (ms_regs ms) (y_lp x) (a9_line x) HST1 Hsp1 HraT
  ltac:(lazymatch goal with |- getr _ ?r = _ => exact (s1_bvr _ r 3 _ eq_refl Rgp) end)
  ltac:(lazymatch goal with |- getr _ ?r = _ => exact (s1_bvr _ r 4 _ eq_refl Rtp) end)
  ltac:(lazymatch goal with |- getr _ ?r = _ => exact (s1_bvr _ r 10 _ eq_refl Q10') end)
  ltac:(lazymatch goal with |- getr _ ?r = _ => exact (s1_bvr _ r 11 _ eq_refl Q11) end)
  HSTR1 HINB) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
(* the call *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False)
    (SIG SS___interceptor_trampoline_strchr) Wc (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file
    (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x))) (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x))
    (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc _ 0 (pf_s1 (y_v x) - pf_sp0 (y_v x)) _ _ HJ
    ltac:(rewrite Hsp1; lia) Ho16 ltac:(lia) ltac:(unfold ESTACK; lia) Hbud
    ltac:(lazymatch goal with |- getr _ ?r = _ => exact (s1_bvr _ r 1 _ eq_refl Q1) end)
    (fun a (H : False) => False_ind _ H)).
  exact (ASTRCHR fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (y_lp x) 0x3d (seg_spec.zb (a9_line x))
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ & HK2).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
rewrite SPF in Hpres2.
assert (HK2' : forall a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx (y_v x) (y_pos x) false false a ->
    rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hn. rewrite HK2; [exact (KM1 a Ha) | exact Ha | | tauto].
  intros Hw. apply Hn. unfold a5_Wrx. left. rewrite SPF. unfold ESTACK in Hw. lia. }
assert (HV2 : forall a, rdW Wc memc a <> None -> rdW Wc mem2 a <> None).
{ apply s1_vis_all. intros a Ha Hv.
  destruct (Z_lt_le_dec a (pf_s1 (y_v x) - 2 * ESTACK)) as [Hlo | Hlo];
  [|destruct (Z_lt_le_dec a (pf_s1 (y_v x))) as [Hhi | Hhi]].
  - rewrite HK2; [exact (KV1 a Hv) | exact Ha | lia | tauto].
  - apply (aview_some_of_apresent SEGS). apply Hpres2. unfold ESTACK in *. lia.
  - rewrite HK2; [exact (KV1 a Hv) | exact Ha | lia | tauto]. }
assert (RG2 : pf_rg regs2 (a5_FI B (y_v x) ++ A9_RC x ++ [(24, p_c (y_v x)); (23, y_lp x)])).
{ apply (a5_rg_pres _ _ _ HP2); [|exact RGm].
  unfold a5_FI, A9_RC, PF_RM. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. }
pose proof (proj1 (a5_rg_app _ _ _) RG2) as [RG2FI RG2A].
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 12932)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x540)) regs2 mem2 md2).
apply Kc.
split.
{ apply (s1_move B n x lyc Sc Wc rX memc mdc Sc Wc regs2 mem2 md2 HC HJ2).
  - exists (st_fs Sc). destruct Sc; reflexivity.
  - apply Permutation_refl.
  - exact HK2'.
  - exact HV2.
  - exact RG2FI. }
split.
{ split; [|exact HINB]. apply (s1_sa_str_keep (rdW Wc memc)); [|exact HSTR].
  intros a Ha.
  pose proof (Z.div_mod (y_lp x + Z.of_nat (length (a9_line x))) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (y_lp x + Z.of_nat (length (a9_line x))) 8 ltac:(lia)).
  unfold s1_span in Ha.
  unfold ESTACK in Hw2.
  rewrite HK2; [apply KM1; lia | lia | unfold ESTACK; lia | tauto]. }
split; [exact RG2A|].
(* strchr's answer *)
cbv beta in HQ.
pose proof HSTR as [[_ HNZ] _].
destruct (s1_astr_of_sa Wc memc _ _ HSTR) as (_ & _ & _ & HZS & _).
destruct HQ as [(H0 & HnIn) | (j & Hfirst & Hj)].
- left. split.
  + lazymatch type of H0 with getr _ ?r = _ => exact (s1_bvr _ r 10 _ eq_refl H0) end.
  + apply a9_strchr_none; [lia|]. change (map (fun b : byte => bv_unsigned b) (seg_spec.zb (a9_line x)))
      with (seg_spec.zs (seg_spec.zb (a9_line x))) in HnIn. rewrite HZS in HnIn. exact HnIn.
- right. exists j. split.
  + apply a9_strchr_of_first; [lia | exact HNZ|].
    change (map (fun b : byte => bv_unsigned b) (seg_spec.zb (a9_line x)))
      with (seg_spec.zs (seg_spec.zb (a9_line x))) in Hfirst. rewrite HZS in Hfirst. exact Hfirst.
  + lazymatch type of Hj with getr _ ?r = _ => exact (s1_bvr _ r 10 _ eq_refl Hj) end.
Qed.

(* the F_neither literal's atom: listing object 40 (0x216a0) *)
Lemma s1_neither_atom : forall E, img_env VAL A_LIM E -> ew E 281%nat = w64 (seg_litA_rc F_neither).
Proof.
intros E HE. rewrite (img_env_atomP E 281%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 281%nat with (A_OBJ 40). rewrite (OBJ 40%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

(* ---------- no '=' (a0 = 0): 0x87fb8 .. 0x87fbc beqz .. 0x88094 .. 0x881d0 j REF3 0x87e74 ---------- *)
(* the seed: a0 pinned to 0, the slots s1 + 0x90 (c, atom 32) and s1 + 0xb0 (cur, atom 33) *)
Definition s1_rN : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x90 0xb8 0 0
    [YP09.mkChunk 0x90 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xb0 (CVal 8 (SOff 33 0))].
Definition s1_ssN : sstate :=
  mkSS (AF_reac_segconf_parse_file + 0x540) (sr_set sr_atoms (Z_to_bv 5 10) (SLit 0)) [s1_rN] None
    (mkFacts [] [] []).

Lemma s1_none : forall n x lyc Sc Wc rX memc mdc,
  a9_core B n x lyc Sc Wc rX memc mdc ->
  a9_inbuf (rdW Wc memc) x (y_lp x) (a9_line x) ->
  pf_rg rX (A9_RC x ++ [(24, p_c (y_v x)); (23, y_lp x)]) ->
  getr rX (Z_to_bv 5 10) = w64 0 -> strchr (a9_line x) EQ = None ->
  HA_REF3 B n ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x540)) rX memc mdc) (a9_goal B x).
Proof.
intros n x lyc Sc Wc rX memc mdc HC HLN HRG R10 HNONE HR3.
pose proof HC as (HB & HM & HS0 & HL & HLT & HD0 & HDL).
destruct (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & HSHP).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (HCX & (HJ & _) & _ & HSL & _).
pose proof HCX as (_ & _ & _ & Hc64 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12). rewrite SPF in G1.
destruct HLN as [HSTR HINB].
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 (y_v x))) by (apply (a5_rg_get _ _ _ _ HFI); unfold a5_FI; s1_in).
assert (W90 : rdword (rdW Wc memc) (pf_s1 (y_v x) + 0x90) = Some (p_c (y_v x)))
  by (exact (proj1 (Forall_forall _ _) HSL (0x90, p_c (y_v x)) ltac:(unfold PF_SL; s1_in))).
assert (WB0 : rdword (rdW Wc memc) (pf_s1 (y_v x) + 0xb0) = Some (a9_cp x))
  by (exact (proj1 (Forall_forall _ _) HL (0xb0, a9_cp x) ltac:(s1_in))).
pose proof (s1_rdword_rng Wc memc _ _ WB0) as Hcp.
(* the seed *)
set (E := Eimg (Ereg rX [w64 (p_c (y_v x)); w64 (a9_cp x)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = w64 (p_c (y_v x)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 (a9_cp x))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 (y_v x))
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E s1_ssN
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x540))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx.
  assert (HS1 : st_ok_pi SEGS VAL E (mkSS (AF_reac_segconf_parse_file + 0x540) sr_atoms [s1_rN] None
      (mkFacts [] [] []))
    (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x540))) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
  { apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, s1_rN.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (chunk_ok_val SEGS E _ (pf_s1 (y_v x)) 0x90 8 (SOff 32 0) (p_c (y_v x)));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
        exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W90).
      + apply (chunk_ok_val SEGS E _ (pf_s1 (y_v x)) 0xb0 8 (SOff 33 0) (a9_cp x));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
        exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ WB0).
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - split; [exact I | split; exact I]. }
  exact (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 10) 0 HS1 R10 eq_refl). }
clearbody E.
assert (SHOK : sh_ok SEGS (SOff 22 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + (AF_reac_segconf_parse_file + 0x540)))
  with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x540))).
paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_REF3.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
assert (KV1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HFr HG.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11. prreg HS (Z_to_bv 5 12) Q12.
prreg HS (Z_to_bv 5 13) Q13. prreg HS (Z_to_bv 5 20) Q20. prreg HS (Z_to_bv 5 24) Q24.
assert (QK : forall r v, In (r, v) (a5_FI B (y_v x) ++ A9_RC x) ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r v Hr. unfold a5_FI, A9_RC, PF_RM in Hr. cbn [In app] in Hr.
  repeat (destruct Hr as [Hr | Hr]; [injection Hr as <- _; s1_kept HS EE |]). destruct Hr. }
assert (RG1 : pf_rg rX (a5_FI B (y_v x) ++ A9_RC x)).
{ apply a5_rg_app. split; [exact HFI|]. eapply a5_rg_incl; [|exact HRG].
  intros rv Hrv. apply in_or_app. left. exact Hrv. }
pose proof (s1_rg_eq _ _ _ QK RG1) as RGm.
pose proof (proj1 (a5_rg_app _ _ _) RGm) as [RGmFI RGmA].
assert (R23 : getr rX (Z_to_bv 5 23) = w64 (y_lp x)) by (apply (a5_rg_get _ _ _ _ HRG); s1_in).
assert (R26 : getr rX (Z_to_bv 5 26) = w64 (y_ln x + 1))
  by (apply (a5_rg_get _ _ _ _ HRG); unfold A9_RC, PF_RM; s1_in).
pmkst HS.
assert (HC1 : a9_core B n x lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv).
{ apply (s1_move B n x lyc Sc Wc rX memc mdc Sc Wc (ms_regs ms) (ms_mem ms) mdv HC HJ).
  - exists (st_fs Sc). destruct Sc; reflexivity.
  - apply Permutation_refl.
  - intros a Ha _. exact (KM1 a Ha).
  - exact KV1.
  - exact RGmFI. }
pose proof HC1 as (HB1 & HM1 & HS1 & _).
pose proof HINB as [Hib1 Hib2]. unfold a9_buf, PF_O_BUF in Hib1, Hib2.
pose proof (s1_st_of_base B _ _ _ _ _ _ _ _ HB) as HST.
destruct (s1_frame_rng B _ _ _ _ _ _ _ HST) as (F1 & F2 & F3 & F4).
assert (HSTR1 : sa_str (rdW Wc (ms_mem ms)) (y_lp x) (a9_line x)).
{ apply (s1_sa_str_keep (rdW Wc memc)); [|exact HSTR].
  intros a Ha. apply KM1. unfold s1_span in Ha.
  pose proof (Z.div_mod (y_lp x + Z.of_nat (length (a9_line x))) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (y_lp x + Z.of_nat (length (a9_line x))) 8 ltac:(lia)). lia. }
(* REF3 with f = F_neither, args = [AS line], a3 = lp *)
unfold a9_goal. rewrite (a9_rkey_none (y_cf x) (y_cur x) (y_nm x) (y_ln x + 1) (a9_line x) HNONE).
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (BASE + 12608)) (ms_mem ms) (seg_rom SEGS)) mdv)
  with (cfg_at SEGS (BASE + PF_REF3) (ms_regs ms) (ms_mem ms) mdv).
apply (HR3 fx (y_v x) (y_pos x) lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (y_cf x) (y_cur x) (y_nm x) (y_o x)
  (y_ln x) (y_d x) F_neither (seg_litA_rc F_neither) [AS (a9_line x)] (y_lp x)).
split; [exact HB1|]. split; [exact HM1|]. split; [exact HS1|].
split.
{ right. exists (a9_line x). split; [left; split; reflexivity|]. split; [reflexivity|].
  split; [exact HSTR1 | exact HINB]. }
unfold pf_rg, PF_RL, PF_RM. cbn [app].
repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
- apply (a5_rg_get _ _ _ _ RGmA); unfold A9_RC, PF_RM; s1_in.
- apply (a5_rg_get _ _ _ _ RGmA); unfold A9_RC, PF_RM; s1_in.
- rewrite Q24, E32. reflexivity.
- apply (a5_rg_get _ _ _ _ RGmA); unfold A9_RC, PF_RM; s1_in.
- apply (a5_rg_get _ _ _ _ RGmA); unfold A9_RC, PF_RM; s1_in.
- apply (a5_rg_get _ _ _ _ RGmA); unfold A9_RC, PF_RM; s1_in.
- rewrite Q20, E33. reflexivity.
- rewrite Q10, E32. reflexivity.
- rewrite Q11, (EE 26%nat (Z_to_bv 5 26) eq_refl). exact R26.
- rewrite Q12. exact (s1_neither_atom E HEI).
- rewrite Q13, (EE 23%nat (Z_to_bv 5 23) eq_refl). exact R23.
Qed.

(* ---------- after trim (0x87fe0): mv s7, a0 -> K2 0x87fe4 ---------- *)
(* INV_K2 with the key's pointer still in a0 (s7 is set by the one instruction left) *)
Definition s1_M2 (n : nat) (x : a9x) (ei : nat) (kp : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  a9_core B n x lyc Sc Wc rX memc mdc /\
  strchr (a9_line x) EQ = Some ei /\
  a9_inbuf (rdW Wc memc) x kp (a9_key x ei) /\
  kp + Z.of_nat (length (a9_key x ei)) <= y_lp x + Z.of_nat ei /\
  a9_inbuf (rdW Wc memc) x (y_lp x + Z.of_nat ei + 1) (skipn (S ei) (a9_line x)) /\
  pf_rg rX (A9_RC x ++ [(24, y_lp x + Z.of_nat ei); (20, a9_cp x); (10, kp)]).

(* a C string of buf carried to a reader equal to the cut's on the 64-bit range *)
Lemma s1_inbuf_same : forall n x lyc Sc Wc rX memc mdc (Wc' : world SEGS) memc' q s,
  a9_core B n x lyc Sc Wc rX memc mdc ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc' memc' a = rdW Wc memc a) ->
  a9_inbuf (rdW Wc memc) x q s -> a9_inbuf (rdW Wc' memc') x q s.
Proof.
intros n x lyc Sc Wc rX memc mdc Wc' memc' q s (HB & _) HK (HS & HI).
destruct (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof alloc_ceiling_lt as HCL.
pose proof HI as [Hb1 Hb2]. unfold a9_buf, PF_O_BUF in Hb1, Hb2.
split; [|exact HI].
apply (s1_sa_str_keep (rdW Wc memc)); [|exact HS].
intros a Ha. apply HK. unfold s1_span in Ha.
pose proof (Z.div_mod (q + Z.of_nat (length s)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (q + Z.of_nat (length s)) 8 ltac:(lia)). lia.
Qed.

Lemma s1_k2 : forall n x ei kp lyc Sc Wc rX memc mdc,
  s1_M2 n x ei kp lyc Sc Wc rX memc mdc -> from_K2 B n ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x568)) rX memc mdc) (a9_goal B x).
Proof.
intros n x ei kp lyc Sc Wc rX memc mdc (HC & HCH & HKEY & HKLE & HREST & HRG) HK2.
pose proof HC as (HB & _).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (_ & (HJ & _) & _).
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg rX []))
  (mkSS (AF_reac_segconf_parse_file + 0x568) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x568))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
    [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | split; [exact I | split; exact I]]. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg rX [])) k = getr rX r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
revert HS HEI EE. generalize (Eimg (Ereg rX [])) as E. intros E HS HEI EE.
assert (SHOK : sh_ok SEGS (SOff 22 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + (AF_reac_segconf_parse_file + 0x568)))
  with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x568))).
(* 0x87fe0 mv s7, a0 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan A9_K2.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_nil. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
assert (KV1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HFr HG.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
prreg HS (Z_to_bv 5 23) Q23.
assert (QK : forall r v, In (r, v) (a5_FI B (y_v x) ++ A9_RC x ++ [(24, y_lp x + Z.of_nat ei); (20, a9_cp x)]) ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r v Hr. unfold a5_FI, A9_RC, PF_RM in Hr. cbn [In app] in Hr.
  repeat (destruct Hr as [Hr | Hr]; [injection Hr as <- _; s1_kept HS EE |]). destruct Hr. }
assert (RG1 : pf_rg rX (a5_FI B (y_v x) ++ A9_RC x ++ [(24, y_lp x + Z.of_nat ei); (20, a9_cp x)])).
{ apply a5_rg_app. split; [exact HFI|]. eapply a5_rg_incl; [|exact HRG].
  intros rv Hrv. apply in_app_or in Hrv as [Hrv | Hrv]; apply in_or_app;
    [left; exact Hrv | right; cbn [In] in *; tauto]. }
pose proof (s1_rg_eq _ _ _ QK RG1) as RGm.
pose proof (proj1 (a5_rg_app _ _ _) RGm) as [RGmFI RGmA].
assert (R10 : getr rX (Z_to_bv 5 10) = w64 kp)
  by (apply (a5_rg_get _ _ _ _ HRG); apply in_or_app; right; s1_in).
pmkst HS.
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (BASE + 12976)) (ms_mem ms) (seg_rom SEGS)) mdv)
  with (cfg_at SEGS (BASE + A9_K2) (ms_regs ms) (ms_mem ms) mdv).
apply (HK2 x ei kp lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv).
split.
{ apply (s1_move B n x lyc Sc Wc rX memc mdc Sc Wc (ms_regs ms) (ms_mem ms) mdv HC HJ).
  - exists (st_fs Sc). destruct Sc; reflexivity.
  - apply Permutation_refl.
  - intros a Ha _. exact (KM1 a Ha).
  - exact KV1.
  - exact RGmFI. }
split; [exact HCH|].
split; [exact (s1_inbuf_same n x lyc Sc Wc rX memc mdc Wc (ms_mem ms) kp _ HC KM1 HKEY)|].
split; [exact HKLE|].
split; [exact (s1_inbuf_same n x lyc Sc Wc rX memc mdc Wc (ms_mem ms) _ _ HC KM1 HREST)|].
replace (A9_RC x ++ [(24, y_lp x + Z.of_nat ei); (20, a9_cp x); (23, kp)])
  with ((A9_RC x ++ [(24, y_lp x + Z.of_nat ei); (20, a9_cp x)]) ++ [(23, kp)])
  by (rewrite <- app_assoc; reflexivity).
apply a5_rg_app. split; [exact RGmA|].
apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
rewrite Q23, (EE 10%nat (Z_to_bv 5 10) eq_refl). exact R10.
Qed.

(* ---------- '=' at ei: 0x87fb8 .. check 9 .. sb zero, 0(s8) .. 0x87fdc jal trim ---------- *)
(* the seed: the slot s1 + 0xb0 (cur, atom 32), the byte at eq = a0 (atom 10) writable, check 9's shadow base
   s6 (atom 22) pinned to SB by its fact (trim_t.v's tf_ss form for the same check-and-store) *)
Definition s1_rF : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xb0 0xb8 0 0 [YP09.mkChunk 0xb0 (CVal 8 (SOff 32 0))].
Definition s1_rE : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 1 [].
Definition s1_ssF : sstate :=
  mkSS (AF_reac_segconf_parse_file + 0x540) sr_atoms [s1_rF; s1_rE] None
    (mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (22%nat, mkAF SB SB 0)] [] []).
Definition s1_SH : list shent := [mkSHE 10 0 1].

(* the state at the trim call 0x87fdc: the key part of the line at lp (its NUL stored at eq), the rest of the
   line at eq + 1, s8 = eq, s4 = cur, s7 = a0 = lp, ra = 0x87fe0 *)
Definition s1_Mc (n : nat) (x : a9x) (ei : nat) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  a9_core B n x lyc Sc Wc rX memc mdc /\
  strchr (a9_line x) EQ = Some ei /\
  a9_inbuf (rdW Wc memc) x (y_lp x) (firstn ei (a9_line x)) /\
  a9_inbuf (rdW Wc memc) x (y_lp x + Z.of_nat ei + 1) (skipn (S ei) (a9_line x)) /\
  pf_rg rX (A9_RC x ++ [(24, y_lp x + Z.of_nat ei); (20, a9_cp x); (23, y_lp x); (10, y_lp x)]) /\
  getr rX (Z_to_bv 5 1) = Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x568)).

Lemma s1_found_run : forall n x lyc Sc Wc rX memc mdc ei (Q : world SEGS -> config -> Prop),
  a9_core B n x lyc Sc Wc rX memc mdc ->
  a9_inbuf (rdW Wc memc) x (y_lp x) (a9_line x) ->
  pf_rg rX (A9_RC x ++ [(24, p_c (y_v x)); (23, y_lp x)]) ->
  strchr (a9_line x) EQ = Some ei -> getr rX (Z_to_bv 5 10) = w64 (y_lp x + Z.of_nat ei) ->
  (forall rXc memcc mdcc, s1_Mc n x ei lyc Sc Wc rXc memcc mdcc ->
     SRr SEGS Wc (mkCfg (mkst rXc (Z_to_bv 64 (BASE + AF_trim)) memcc (seg_rom SEGS)) mdcc) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x540)) rX memc mdc) Q.
Proof.
intros n x lyc Sc Wc rX memc mdc ei Q HC HLN HRG HCH R10 Kc.
pose proof HC as (HB & HM & HS0 & HL & HLT & HD0 & HDL).
destruct (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & HSHP).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof (s1_st_of_base B _ _ _ _ _ _ _ _ HB) as HST.
destruct (s1_frame_rng B _ _ _ _ _ _ _ HST) as (F1 & F2 & F3 & F4).
pose proof HB as (HCX & (HJ & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12). rewrite SPF in G1.
pose proof alloc_ceiling_lt as HCL.
destruct HLN as [HSTR HINB].
pose proof HINB as [Hib1 Hib2]. unfold a9_buf, PF_O_BUF in Hib1, Hib2.
destruct (a9_strchr_lt (a9_line x) EQ ei HCH) as [Hei _].
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 (y_v x))) by (apply (a5_rg_get _ _ _ _ HFI); unfold a5_FI; s1_in).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF) by (apply (a5_rg_get _ _ _ _ HFI); unfold a5_FI; s1_in).
assert (WB0 : rdword (rdW Wc memc) (pf_s1 (y_v x) + 0xb0) = Some (a9_cp x))
  by (exact (proj1 (Forall_forall _ _) HL (0xb0, a9_cp x) ltac:(s1_in))).
pose proof (s1_rdword_rng Wc memc _ _ WB0) as Hcp.
pose proof (s1_addr_buf B _ _ _ _ _ _ _ (y_lp x + Z.of_nat ei) 1 HST ltac:(unfold PF_O_BUF; lia) ltac:(lia)
  ltac:(unfold PF_O_BUF; lia)) as (_ & _ & _ & HRAe & _).
(* the seed *)
set (E := Eimg (Ereg rX [w64 (a9_cp x)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = w64 (a9_cp x))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 (y_v x))
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = y_lp x + Z.of_nat ei)
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), R10; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = SB)
  by (rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl), R22; unfold w64, SB; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E s1_ssF
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x540))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold s1_ssF. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, s1_rF.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (pf_s1 (y_v x)) 0xb0 8 (SOff 32 0) (a9_cp x));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
      exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ WB0).
    + unfold region_ok, s1_rE.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. assert (o = 0) as -> by lia. rewrite Z.add_0_r.
      apply (apresent_writable SEGS). apply HFP. unfold PF_O_BUF in *. lia.
  - unfold s1_rF, s1_rE. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U9, U10. unfold PF_O_BUF in *. repeat split; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U22. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia. }
clearbody E.
assert (UB : U E (SOff 22 0) = SHADOW_OFF).
{ rewrite (U_atom E 22 SB); [reflexivity | | unfold SB; lia].
  rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl), R22. reflexivity. }
assert (UE : U E (SOff 10 0) = y_lp x + Z.of_nat ei).
{ apply U_atom; [rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), R10; reflexivity | lia]. }
assert (SHOK : sh_ok SEGS (SOff 22 0) s1_SH E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, s1_SH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E (SOff 22 0) 10%nat (y_lp x + Z.of_nat ei) 1
    (y_lp x + Z.of_nat ei) 0 1 HRAe UB UE); [lia | lia |].
  intros y Hy. change (Z.min 0 1) with 0 in Hy. change (Z.max 0 1) with 1 in Hy.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold SHADOW_OFF.
  unfold PF_O_BUF in *. destruct G9 as [_ [G9 | [G9a G9b]]]; lia. }
unfold cfg_at. change (w64 (BASE + (AF_reac_segconf_parse_file + 0x540)))
  with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x540))).
(* 0x87fb8 ld s4; beqz a0 (decided: a0 >= 4096); mv s8, a0; check 9; sb zero, 0(s8); mv a0, s7; jal trim *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 10%nat) (b := y_lp x + Z.of_nat ei); [reflexivity | exact U10 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right; left. exists 5, (y_pos x). split; [left; reflexivity|].
  left. unfold in_zr. cbn [fst snd]. rewrite Hly.
  change (frame_addr (p_ly (y_v x)) 5 (y_pos x)) with (pf_F (y_v x) (y_pos x)).
  change (fs_frame_bytes 5) with 2048. unfold PF_O_BUF in *. lia. }
assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> y_lp x + Z.of_nat ei -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hne.
  apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun a' => a' = y_lp x + Z.of_nat ei) HFr);
    [|exact Ha | exact Hne].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U10 in Hrr; lia |]).
  destruct Hin'. }
assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HFr HG.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
assert (HW0 : rdW Wc (ms_mem ms) (y_lp x + Z.of_nat ei) = Some 0).
{ pose proof (s1_wbyte _ _ _ _ 10%nat 1%nat (y_lp x + Z.of_nat ei) (SLit 0) HS ltac:(vm_compute; reflexivity)) as V.
  rewrite V; [reflexivity|]. cbn [extK]. exact U10. }
pmkst HS.
prreg HS (Z_to_bv 5 1) Q1. prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 24) Q24. prreg HS (Z_to_bv 5 20) Q20.
assert (QK : forall r v, In (r, v) (a5_FI B (y_v x) ++ A9_RC x ++ [(23, y_lp x)]) ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r v Hr. unfold a5_FI, A9_RC, PF_RM in Hr. cbn [In app] in Hr.
  repeat (destruct Hr as [Hr | Hr]; [injection Hr as <- _; s1_kept HS EE |]). destruct Hr. }
assert (RG1 : pf_rg rX (a5_FI B (y_v x) ++ A9_RC x ++ [(23, y_lp x)])).
{ apply a5_rg_app. split; [exact HFI|]. eapply a5_rg_incl; [|exact HRG].
  intros rv Hrv. apply in_app_or in Hrv as [Hrv | Hrv]; apply in_or_app;
    [left; exact Hrv | right; cbn [In] in *; tauto]. }
pose proof (s1_rg_eq _ _ _ QK RG1) as RGm.
pose proof (proj1 (a5_rg_app _ _ _) RGm) as [RGmFI RGmA].
assert (R23 : getr rX (Z_to_bv 5 23) = w64 (y_lp x)) by (apply (a5_rg_get _ _ _ _ HRG); s1_in).
rewrite (SIGP SS_trim ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_trim) with AF_trim by (vm_compute; reflexivity).
apply Kc.
split.
{ apply (s1_move B n x lyc Sc Wc rX memc mdc Sc Wc (ms_regs ms) (ms_mem ms) mdv HC HJ).
  - exists (st_fs Sc). destruct Sc; reflexivity.
  - apply Permutation_refl.
  - intros a Ha Hw. apply KM; [exact Ha|]. intros ->. apply Hw. right; right; left.
    unfold a5_buf, PF_O_BUF. lia.
  - exact KV.
  - exact RGmFI. }
split; [exact HCH|].
split.
{ split.
  - apply (s1_prefix_str (rdW Wc memc) _ (y_lp x) (a9_line x) ei HSTR ltac:(lia)); [|exact HW0].
    intros a Ha Hne. apply KM; [|exact Hne]. unfold s1_span in Ha.
    pose proof (Z.div_mod (y_lp x + Z.of_nat (length (a9_line x))) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (y_lp x + Z.of_nat (length (a9_line x))) 8 ltac:(lia)). lia.
  - unfold pf_inb, a9_buf, PF_O_BUF. rewrite length_firstn. lia. }
split.
{ replace (y_lp x + Z.of_nat ei + 1) with (y_lp x + Z.of_nat (S ei)) by lia. split.
  - apply (s1_suffix_str (rdW Wc memc) _ (y_lp x) (a9_line x) (S ei) HSTR ltac:(lia)).
    intros a Ha. apply KM; [|lia]. unfold s1_span in Ha.
    pose proof (Z.div_mod (y_lp x + Z.of_nat (length (a9_line x))) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (y_lp x + Z.of_nat (length (a9_line x))) 8 ltac:(lia)). lia.
  - unfold pf_inb, a9_buf, PF_O_BUF. rewrite length_skipn. lia. }
split.
{ apply a5_rg_app. split.
  { eapply a5_rg_incl; [|exact RGmA]. intros rv Hrv. apply in_or_app. left. exact Hrv. }
  unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
  - rewrite Q24, (EE 10%nat (Z_to_bv 5 10) eq_refl). exact R10.
  - rewrite Q20, E32. reflexivity.
  - apply (a5_rg_get _ _ _ _ RGmA). apply in_or_app. right. s1_in.
  - rewrite Q10, (EE 23%nat (Z_to_bv 5 23) eq_refl). exact R23. }
exact Q1.
Qed.

(* VERIFY rule 1j-bis, edge reac_segconf_parse_file -> trim at 0x87fdc: a cut of A9 whose memory holds the key
   part of the line at lp (K = firstn ei line, its NUL stored at eq by 0x87fd4) and a0 = lp gives every premise
   of trim_contract besides afn_pre (which cl_callS_wide builds from the journal). From pf_a9_s1_k.v
   s1_trim_site_ok (pf_a7_s.v a7_trim_site_ok). *)
Lemma trim_site_ok_87fdc : forall n x ei lyc Sc Wc rX memc mdc (regs : bvmap 5 word),
  a9_core B n x lyc Sc Wc rX memc mdc ->
  a9_inbuf (rdW Wc memc) x (y_lp x) (firstn ei (a9_line x)) ->
  getr regs 10 = w64 (y_lp x) ->
  s1_trim_call B lyc Sc Wc memc regs (y_lp x) (firstn ei (a9_line x)).
Proof.
intros n x ei lyc Sc Wc rX memc mdc regs (HB & _) (HS & HI) R10.
exact (s1_trim_site_ok B _ _ _ _ _ _ _ regs _ _ (s1_st_of_base B _ _ _ _ _ _ _ _ HB) R10 HS HI).
Qed.

Lemma s1_bvr' : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr r = v ->
  getr rr (Z_to_bv 5 k) = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.

(* ---------- the trim call 0x87fdc .. its return 0x87fe0 .. K2 ---------- *)
Lemma s1_trim_step : forall n x ei lyc Sc Wc rXc memcc mdcc,
  s1_Mc n x ei lyc Sc Wc rXc memcc mdcc -> from_K2 B n ->
  SRr SEGS Wc (mkCfg (mkst rXc (Z_to_bv 64 (BASE + AF_trim)) memcc (seg_rom SEGS)) mdcc) (a9_goal B x).
Proof.
intros n x ei lyc Sc Wc rXc memcc mdcc (HC & HCH & HKS & HREST & HRG & HR1) HK2.
pose proof HC as (HB & HM & HS0 & HL & HLT & HD0 & HDL).
destruct (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & HSHP).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof (s1_st_of_base B _ _ _ _ _ _ _ _ HB) as HST.
destruct (s1_stk B _ _ _ _ _ _ _ HST) as (Hal16 & Hceil & Hslo & Hs32 & Hs1r & Ho16).
pose proof HB as (HCX & (HJ & _) & _).
destruct (a5_chain B _ _ _ _ _ _ _ _ _ HB) as [ch1 HCH1].
pose proof STK_values as (STR & _ & _ & SPF & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof alloc_ceiling_lt as HCL.
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12). rewrite SPF in G1.
destruct (a9_strchr_lt _ _ _ HCH) as [Hei _].
pose proof HKS as (HKSTR & Hkb1 & Hkb2). unfold a9_buf, PF_O_BUF in Hkb1, Hkb2.
pose proof HKSTR as ((_ & HNK) & _).
pose proof (L_trim_holds (firstn ei (a9_line x)) HNK) as (L1 & L2 & L3).
assert (HLK : length (firstn ei (a9_line x)) = ei) by (rewrite length_firstn; lia).
rewrite HLK in L1, Hkb2.
pose proof HREST as (HRSTR & Hrb1 & Hrb2). unfold a9_buf, PF_O_BUF in Hrb1, Hrb2.
rewrite length_skipn in Hrb2.
set (K := firstn ei (a9_line x)) in *.
set (te := trim_end_addr (y_lp x) K).
assert (HTE : y_lp x <= te <= y_lp x + Z.of_nat ei) by (unfold te, trim_end_addr; lia).
(* the registers at the call *)
assert (Rg : forall r v, In (r, v) (a5_FI B (y_v x)) -> getr rXc (Z_to_bv 5 r) = w64 v)
  by (intros r v Hr; exact (a5_rg_get _ _ _ _ HFI Hr)).
assert (C2 : getr rXc 2 = w64 (pf_s1 (y_v x))).
{ lazymatch goal with |- getr _ ?r = _ => apply (s1_bvr _ r 2 _ eq_refl) end. apply Rg. unfold a5_FI. s1_in. }
assert (C3 : getr rXc 3 = w64 (as_gp B)).
{ lazymatch goal with |- getr _ ?r = _ => apply (s1_bvr _ r 3 _ eq_refl) end. apply Rg. unfold a5_FI. s1_in. }
assert (C4 : getr rXc 4 = w64 (as_tp B)).
{ lazymatch goal with |- getr _ ?r = _ => apply (s1_bvr _ r 4 _ eq_refl) end. apply Rg. unfold a5_FI. s1_in. }
assert (C8 : getr rXc 8 = w64 (pf_sp0 (y_v x))).
{ lazymatch goal with |- getr _ ?r = _ => apply (s1_bvr _ r 8 _ eq_refl) end. apply Rg. unfold a5_FI. s1_in. }
assert (C10 : getr rXc 10 = w64 (y_lp x)).
{ lazymatch goal with |- getr _ ?r = _ => apply (s1_bvr _ r 10 _ eq_refl) end.
  apply (a5_rg_get _ _ _ _ HRG). apply in_or_app. right. s1_in. }
assert (C1 : getr rXc 1 = Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x568))).
{ lazymatch goal with |- getr _ ?r = _ => exact (s1_bvr _ r 1 _ eq_refl HR1) end. }
assert (Csp : spZ rXc = pf_s1 (y_v x)) by (unfold spZ; rewrite C2; unfold w64; apply unsigned_lit_small; lia).
(* VERIFY rule 1j-bis at 0x87fdc *)
pose proof (trim_site_ok_87fdc n x ei lyc Sc Wc rXc memcc mdcc rXc HC HKS C10) as (ROD & _ & Hp64 & TPRE & TEV).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS Wc rXc memcc _ STK_reac_segconf_parse_file (pf_sp0 (y_v x))
    (seg_spec.RC_PARSE_W (p_c (y_v x))) (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x))
    [(5, y_pos x)] lyc Sc mdcc 0 STK_trim [(te, te + 1)] EV_trim
    (pf_s1 (y_v x) - pf_sp0 (y_v x)) (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x568))) ch1
    (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (y_lp x + Z.of_nat (seg_spec.trim_lead K)) /\
       sa_bytes (aview SEGS (w_H W') mem') (y_lp x)
         (seg_spec.zb (firstn (seg_spec.trim_lead K + length (SegModel.r_trim K)) K) ++ [seg_spec.ZERO]) /\
       sa_kept SEGS Wc memcc W' mem' rXc STK_trim (fun a => a = trim_end_addr (y_lp x) K) /\
       sa_noalloc B lyc Sc ly' S') HJ).
  - rewrite Csp. lia.
  - exact Ho16.
  - lia.
  - rewrite STR. lia.
  - rewrite STR, SPF. lia.
  - exact C3.
  - exact C4.
  - exact C1.
  - apply ret_ok_codeptr_v; [unfold AF_reac_segconf_parse_file; lia | reflexivity].
  - unfold AF_reac_segconf_parse_file in *. rewrite unsigned_lit_small by lia. lia.
  - replace (pf_sp0 (y_v x) + (pf_s1 (y_v x) - pf_sp0 (y_v x))) with (pf_s1 (y_v x)) by lia.
    unfold s0Z. rewrite C8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH1.
  - intros HPRE1. eapply SRr_mono.
    { exact (TRIM fx lyc Sc Wc rXc memcc mdcc ch1 (y_lp x) K HPRE1 ROD C10 Hp64 TPRE TEV). }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. split; [rewrite C1; reflexivity|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
    right; right; right; left. exists 5, (y_pos x). split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite Hly.
    change (frame_addr (p_ly (y_v x)) 5 (y_pos x)) with (pf_F (y_v x) (y_pos x)).
    change (fs_frame_bytes 5) with 2048. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw Hn.
    apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
    exfalso. lia. }
(* back at 0x87fe0, at the same FP state *)
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (Ha02 & HBY2 & HKT2 & HNA2)).
destruct HNA2 as (HPm2 & Hly2 & HSf2). subst ly2.
replace (0 + EV_trim) with 0 in HJ2 by (unfold EV_trim; lia).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
rewrite SPF in Hpres2.
assert (HKT : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 (y_v x) - STK_trim <= a < pf_s1 (y_v x)) -> a <> te ->
  rdW W2 mem2 a = rdW Wc memcc a).
{ intros a Ha Hw He. apply HKT2; [exact Ha | rewrite Csp; exact Hw | exact He]. }
assert (HTEV : rdW W2 mem2 te <> None).
{ unfold te, trim_end_addr. rewrite (HBY2 (seg_spec.trim_lead K + length (r_trim K))%nat); [discriminate|].
  unfold seg_spec.zb. rewrite length_app, length_map, length_firstn. cbn [length]. lia. }
assert (HVT : forall a, rdW Wc memcc a <> None -> rdW W2 mem2 a <> None).
{ apply s1_vis_all. intros a Ha Hv.
  destruct (Z.eq_dec a te) as [-> | Hne]; [exact HTEV|].
  destruct (Z_lt_le_dec a (pf_s1 (y_v x) - STK_trim)) as [Hlo | Hlo];
  [|destruct (Z_lt_le_dec a (pf_s1 (y_v x))) as [Hhi | Hhi]].
  - rewrite HKT; [exact Hv | exact Ha | lia | exact Hne].
  - apply (aview_some_of_apresent SEGS). apply Hpres2. rewrite STR in Hlo. lia.
  - rewrite HKT; [exact Hv | exact Ha | lia | exact Hne]. }
assert (HCT : a9_core B n x lyc S2 W2 regs2 mem2 md2).
{ apply (s1_move B n x lyc Sc Wc rXc memcc mdcc S2 W2 regs2 mem2 md2 HC HJ2 HSf2 HPm2).
  - intros a Ha Hw. apply HKT; [exact Ha | | ].
    + intros Hq. apply Hw. left. rewrite SPF. rewrite STR in Hq. lia.
    + intros ->. apply Hw. right; right; left. unfold a5_buf, PF_O_BUF. lia.
  - exact HVT.
  - exact (a5_rg_pres rXc regs2 _ HP2 (a5_FI_cs B _) HFI). }
pose proof (s1_key_str Wc W2 memcc mem2 (y_lp x) K HKSTR HBY2 HVT) as HKEY.
change (r_trim K) with (a9_key x ei) in HKEY, L1, L3.
change (seg_spec.zb (firstn (seg_spec.trim_lead K + length (SegModel.r_trim K)) K)) with
  (seg_spec.zb (firstn (seg_spec.trim_lead K + length (a9_key x ei)) K)) in HBY2.
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x568))) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x568)) regs2 mem2 md2).
apply (s1_k2 n x ei (y_lp x + Z.of_nat (seg_spec.trim_lead K)) lyc S2 W2 regs2 mem2 md2); [|exact HK2].
split; [exact HCT|]. split; [exact HCH|].
split.
{ split; [exact HKEY|]. unfold pf_inb, a9_buf, PF_O_BUF. lia. }
split; [lia|].
split.
{ split; [|exact (proj2 HREST)].
  apply (s1_sa_str_keep (rdW Wc memcc)); [|exact HRSTR].
  intros a Ha. unfold s1_span in Ha. rewrite length_skipn in Ha.
  pose proof (Z.div_mod (y_lp x + Z.of_nat ei + 1 + Z.of_nat (length (a9_line x) - S ei)) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (y_lp x + Z.of_nat ei + 1 + Z.of_nat (length (a9_line x) - S ei)) 8 ltac:(lia)).
  apply HKT; [lia | rewrite STR; lia | lia]. }
replace (A9_RC x ++ [(24, y_lp x + Z.of_nat ei); (20, a9_cp x); (10, y_lp x + Z.of_nat (seg_spec.trim_lead K))])
  with ((A9_RC x ++ [(24, y_lp x + Z.of_nat ei); (20, a9_cp x)]) ++
        [(10, y_lp x + Z.of_nat (seg_spec.trim_lead K))]) by (rewrite <- app_assoc; reflexivity).
apply a5_rg_app. split.
{ apply (a5_rg_pres rXc regs2 _ HP2).
  - unfold A9_RC, PF_RM. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
  - eapply a5_rg_incl; [|exact HRG]. intros rv Hrv. unfold A9_RC, PF_RM in *. cbn [app In] in *. tauto. }
apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
lazymatch type of Ha02 with getr _ ?r = _ => exact (s1_bvr' _ r 10 _ eq_refl Ha02) end.
Qed.

(** ** Stretch A: from REF3 (at every FP state) and K2, the walk reaches A9's goal from KEY *)
Lemma a9_sA : SA9_A B.
Proof.
unfold SA9_A, H_KEY.
intros n HR3 HK2 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp HI.
pose proof (a9_of_KEY B n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp HI) as HX. cbv zeta in HX.
destruct HX as (HC & HLN & HRG).
apply (s1_strchr_step n (mkA9X v pos cf cur nm o ln d lp) lyc Sc Wc rX memc mdc _ HC HLN HRG).
intros rX1 memc1 mdc1 (HC1 & HLN1 & HRG1 & [(R10 & HN) | (ei & HCH & R10)]).
- exact (s1_none n _ lyc Sc Wc rX1 memc1 mdc1 HC1 HLN1 HRG1 R10 HN HR3).
- apply (s1_found_run n _ lyc Sc Wc rX1 memc1 mdc1 ei _ HC1 HLN1 HRG1 HCH R10).
  intros rXc memcc mdcc HMc. exact (s1_trim_step n _ ei lyc Sc Wc rXc memcc mdcc HMc HK2).
Qed.

End e.
End f.
End d.
