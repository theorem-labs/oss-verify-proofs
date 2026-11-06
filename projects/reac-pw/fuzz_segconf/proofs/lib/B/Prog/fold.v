(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan+UBSan build of plugin-hostd/fuzz_command
   (0x89ef8, 164 instructions, frame 144 bytes), ported from the ASan walk lib/A/Prog/rec_calls_equal.v (0x89968). The
   shape is the A walk's: the symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed
   by the shadow tokens (PaShadow.v), the strcmp wrapper's call stepped through by its Theorem Labs lane contract (PaArt.v
   aj_art_at), the two loops cut at their heads (0x89f98, 0x8a064) and at the outer latch (0x8a0b4), each piece re-seeded
   from the concrete state there, the loops proved by induction. What B changes:
   - the frame (144 bytes) keeps n at 0(sp), the UBSan predicates `b mod 8 = 0 && b <> 0`, `b <> 0`,
     `a mod 8 = 0 && a <> 0` at 8(sp), 16(sp), 24(sp), and b at 32(sp); a stays in a5/s11 and `a <> 0` in a4/s8;
   - the inner loop counts s5 = 8k up to s2 = 8 * nargs and forms both argument addresses from s3/s10 (a[i].args) and
     s1/s9 (b[i].args) plus s5 (the seed's alias facts name the two sums);
   - eight UBSan trap branches, all to the `unimp` at 0x8a168, are refuted from the run's facts: 0x89fac, 0x89fbc,
     0x89fe4, 0x89ff4 are decided by the executor (a4 = 1 and the three predicate slots = 1 at the outer seed, which the
     entry derives from rce_calls' `a mod 8 = 0` and rce_home's 4096 <= a; a + 56i >= 4096 by the seed's atom fact);
     0x89fb4 and 0x89fec (a + 56i < a, b + 56i < b unsigned) and 0x8a064, 0x8a068 (~(a[i].args) < 8k, ~(b[i].args) < 8k)
     are refuted at the branch from the values of their operands. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_calls_equal.v, with its module paths and module names changed; 1064 of its 1245 lines of code are new or changed and 1411 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of fold on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, unstripped twin 80e82127e8ca; entry 0x87c94, 280 bytes, 70 instructions, a 16-byte frame holding
   only the return address, no side-stack frame): fold_contract of lib/B/Prog/fold_c.v at image B's numbers, in
   plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the entry, SRr of apost_base at the return, over
   `Context {PI : PAImg seg_listing}` of image B's listing lib/B/Prog/SegPa.v). Written new: image A has no fold
   (clang inlines it into m_file there), so there is no image-A walk to adapt; the loop logic and the fact that
   kills each UBSan trap come from the segconf porter's UBSan walk lib/U/Prog/fold.v (another framework), the form from
   the image-B m_file-family owner's proved image-B walk lib/B/Prog/ieq.v.

   The code (the neutral listing of fold in image B):
     0x87c94-0x87cb0  frame of 16: ra at sp+8; a4 := the GOT word as_got_shadow B (image B 0xa3210 = listing
                      A_OBJ 0), a5 := the shadow base it points to (the cell A_OBJ 12 = 0xac7b8);
                      a3 := cap - 1; `bltu a1,a3` (0x87ca8) keeps a1 = n when n <u cap - 1, else a1 := cap - 1:
                      a1 = k = min(n, cap - 1)
     FO_K 0x87cb4     `beqz a1` -> 0x87d64 when k = 0
     0x87cb8-0x87cd4  a7 := 0 (i), a6 := ~out, t0 := (s <> 0), t1 = a3 := s, t2 = a4 := out, t3 := k
     LOOP 0x87cd8     the UBSan checks of s + i (bltu a3,a0 / seqz-xor-beqz t4 / beqz a0) and of out + i
                      (bltu a6,a7), each to the trap 0x87d94 (unimp); the instrumented check of s[i] (a load of
                      the shadow byte at (a3 >> 3) + the shadow base and a compare; slow block 0x87d48; the error
                      path, a call of errpath_load1 at 0x87da8, is not reached) and of out + i (slow block
                      0x87d54, error path 0x87d60); lbu s[i] (t4), the fold t4 + 32 (t4 - 'A' <u 26) =
                      SegModel.lower s[i], `sb t4,0(t2)` (0x87d34) at out + i; i += 1, t3 -= 1, the four cursors
                      step, `beqz t3` -> 0x87d68, else j LOOP
     0x87d64          (k = 0 path) a6 := ~out
     0x87d68          the UBSan check `bltu a6,a1` of out + k, to the trap
     TAIL 0x87d70     a0 := out + k (0x87d6c), the instrumented check of out + k (slow block 0x87d98, error path
                      0x87da0), `sb zero,0(a0)` (0x87d80), a0 := k, ra restored, sp += 16, ret
   The five UBSan trap branches (each to the unimp at 0x87d94), each decided "not taken" by the symbolic executor
   at its branch (PaSym.v sym_step_pi: decide_cond2 under facts_ok, kit YP0e.v), so the trap instruction is never
   executed:
     0x87cd8 bltu a3,a0  a3 = s + i, a0 = s: the assumed condition s + i >=u s (fo_l_conds; s + k <=
                         alloc_ceiling by the contract's sa_loc, so s + i does not wrap)
     0x87ce4 beqz t4     t4 = t0 xor (s + i = 0): t0 = 1 (s <> 0, the contract's premise when k > 0; the executor
                         folds snez s to 1 from the entry fact s in [1, 2^64 - 1], fo_NZF) and (s + i = 0) folds
                         to 0 from the fact s + i in [4096, 2^47 - 64] (fo_PTRF), so t4 = 1
     0x87ce8 beqz a0     s in [4096, 2^47 - 64] (fo_PTRF, atom 38; 4096 <= s from sa_loc)
     0x87cec bltu a6,a7  a6 = ~out, a7 = i: the assumed condition ~out >=u i (fo_l_conds), i.e. out + i does not
                         wrap: out + k + 1 <= alloc_ceiling by sa_fframe and AR
     0x87d68 bltu a6,a1  a6 = ~out, a1 = k: the assumed condition ~out >=u k (fo_l_conds), out + k does not wrap
   Cut points (listing offsets from BASE = 0x84dc0): the entry AF_fold 0x2ed4; FO_K 0x2ef4 (0x87cb4), re-seeded
   with a1 = k, after the two arms of the `bltu` that computes k; FO_LOOP 0x2f18 (0x87cd8) at byte i, re-seeded
   from the concrete state, the loop proved by induction on the bytes left; FO_TAIL 0x2fb0 (0x87d70), re-seeded
   with a0 = out + k. The three instrumented checks are decided by the shadow tokens (PaShadow.v) from one-byte
   shadow entries of s + i, out + i and out + k, whose range_addressable the contract's sa_addr and the shadow
   half of sa_dst's frame arm give.
   Memory: the code writes its own frame (ra at sp0 - 8) and [out, out + k + 1) only; every other byte is kept
   (fo_kept, the post's sa_kept), and s's and out's bytes lie below alloc_ceiling (sa_loc, sa_fframe), so their
   facts hold at every point. The walk takes no runtime entry as a Section hypothesis: on its good path fold
   calls nothing. Its one record hypothesis is TL : PALib B (the shadow GOT word and the shadow cell by role).
   Image numbers: the entry BASE + AF_fold and STK_fold = 16 (lib/B/Prog/SegInstB.v, image B's frame; the error
   path is dead, so no callee window is added). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import fold_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
Module SM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.SegModel.
Module SP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.seg_spec.

(* image B: STK_fold (SegInstB.v: the 16-byte frame; fold calls nothing on its good path) *)
#[local] Notation FO_STK := SegInstB.STK_fold.

(* ---------- the model ---------- *)
Lemma fo_zs_length : forall bs, length (SP.zs bs) = length bs.
Proof. intros bs. unfold SP.zs. apply length_map. Qed.
Lemma fo_zb_length : forall zl, length (SP.zb zl) = length zl.
Proof. intros zl. unfold SP.zb. apply length_map. Qed.
Lemma fo_nth_firstn : forall {A} (x : list A) k i d, (i < k)%nat -> nth i (firstn k x) d = nth i x d.
Proof.
intros A x. induction x as [|a x IH]; intros k i d H; [destruct k, i; reflexivity|].
destruct k as [|k]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma fo_map_nth : forall {A B} (f : A -> B) (x : list A) i d d', (i < length x)%nat -> nth i (map f x) d' = f (nth i x d).
Proof.
intros A B f x. induction x as [|a x IH]; intros i d d' H; [cbn in H; lia|].
destruct i as [|i]; [reflexivity|]. cbn [map nth]. apply IH. cbn in H. lia.
Qed.
(* byte i of the folded text is SegModel.lower of byte i of the input (U's fo_nth, lib/U/Prog/fold.v:153) *)
Lemma fo_nth_val : forall (bs : list byte) cap i, (i < length (fold_out bs cap))%nat ->
  nth i (fold_out bs cap) 0 = SM.lower (bv_unsigned (nth i bs ZB0)).
Proof.
intros bs cap i Hi. unfold fold_out, SM.h_fold in *.
rewrite length_map, length_firstn, fo_zs_length in Hi.
rewrite (fo_map_nth SM.lower _ i 0 0) by (rewrite length_firstn, fo_zs_length; lia).
rewrite fo_nth_firstn by lia.
unfold SP.zs. rewrite (fo_map_nth bv_unsigned bs i ZB0 0) by lia. reflexivity.
Qed.
Lemma fo_lower_rng : forall c, 0 <= c < 256 -> 0 <= SM.lower c < 256.
Proof.
intros c Hc. unfold SM.lower.
destruct ((65 <=? c) && (c <=? 90))%bool eqn:E; [|lia].
apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.
Lemma fo_nth_rng : forall (bs : list byte) cap i, (i < length (fold_out bs cap))%nat ->
  0 <= nth i (fold_out bs cap) 0 < 256.
Proof.
intros bs cap i Hi. rewrite (fo_nth_val bs cap i Hi). apply fo_lower_rng.
pose proof (bv_unsigned_in_range 8 (nth i bs ZB0)) as HR. change (bv_modulus 8) with 256 in HR. exact HR.
Qed.
(* the word function of one byte value, checked on all 256 values (ieq's ie_zbrute) *)
Lemma fo_zbrute : forall (F G : Z -> Z) c, 0 <= c < 256 ->
  forallb (fun k => F (Z.of_nat k) =? G (Z.of_nat k)) (seq 0 256) = true -> F c = G c.
Proof.
intros F G c Hc H. rewrite forallb_forall in H.
specialize (H (Z.to_nat c) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia. apply Z.eqb_eq. exact H.
Qed.
Ltac fo_brute c Hc :=
  lazymatch goal with |- ?L = ?R =>
    let F := lazymatch eval pattern c in L with ?F _ => F end in
    let G := lazymatch eval pattern c in R with ?G _ => G end in
    apply (fo_zbrute F G c Hc); vm_compute; reflexivity end.
Ltac fo_U_norm := repeat first [rewrite U_SAlu | rewrite U_SMd | rewrite U_SLit | rewrite U_SOff].
(* an assumed condition of the loop head: atom na >=u atom nb (the UBSan pointer checks) *)
Lemma fo_cond_geu : forall E na nb a b, ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b ->
  0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> b <= a -> acond_ok E (mkAC BC_GEU (SOff na 0) (SOff nb 0)).
Proof.
intros E na nb a b Ha Hb Ra Rb Hle. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_geu_U, (U_atom E na a Ha Ra), (U_atom E nb b Hb Rb).
apply negb_true_iff, Z.ltb_ge. exact Hle.
Qed.
(* `not a6,a2` = xor with -1 *)
Lemma fo_lxor_allones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
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
Lemma fo_U_not : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = 2 ^ 64 - 1 - x.
Proof.
intros E n x Hn Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn Hx), U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite fo_lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* ---------- bytes through a reader ---------- *)
Lemma fo_val1 : forall (rd : reader) a v, rd a = Some v -> 0 <= v < 256 -> sa_val rd a 1 v.
Proof.
intros rd a v H Hv k Hk. assert (k = 0%nat) by lia. subst k. change (Z.of_nat 0) with 0. rewrite Z.add_0_r, H. f_equal.
unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a field read through the world's view is the same field of the restricted memory *)
Lemma fo_val_mem_of_sa_val : forall segs H mem a n v,
  sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
(* one byte, the other way *)
Lemma fo_rd1 : forall segs H mem a v, val_mem segs (mrestrict H mem) a 1 v -> 0 <= v < 256 ->
  aview segs H mem a = Some v.
Proof.
intros segs H mem a v HV Hv. pose proof (HV 0%nat ltac:(lia)) as H0.
change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r in H0.
unfold aview. rewrite H0. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
cbv [YO0f.le_byte YG0f.le_byte]. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma fo_sa_val8_of_val_mem : forall segs H mem a v, val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 ->
  sa_val (aview segs H mem) a 8 v.
Proof.
intros segs H mem a v HV Hv k Hk. unfold aview. rewrite (HV k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
cbv [YO0f.le_byte YG0f.le_byte]. apply Z.mod_mod. lia.
Qed.
End r.

(* ---------- the symbolic states of the cut points ---------- *)
Definition FO_K : Z := 0x2ef4.     (* 0x87cb4, `beqz a1` with a1 = k *)
Definition FO_LOOP : Z := 0x2f18.  (* 0x87cd8, the loop head (the first UBSan check, bltu a3,a0) *)
Definition FO_TAIL : Z := 0x2fb0.  (* 0x87d70, the NUL store's check, a0 = out + k *)
Definition fo_Bx : sv := SOff 32 0.
Definition fo_spF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition fo_SBF : afact := mkAF SB SB 0.
Definition fo_PTRF : afact := mkAF 4096 (2 ^ 47 - 64) 0.
Definition fo_CNTF : afact := mkAF 1 (2 ^ 63) 0.
Definition fo_IDXF : afact := mkAF 0 (2 ^ 63) 0.
Definition fo_BYTEF : afact := mkAF 0 255 0.
(* a nonzero word: s at FO_K when k > 0 (the contract's premise), so that snez s folds to 1 *)
Definition fo_NZF : afact := mkAF 1 (2 ^ 64 - 1) 0.
(* ~out, the UBSan wrap bound *)
Definition fo_NOTF : afact := mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0.
(* the entry: atom 32 the shadow base *)
Definition fo_ss_entry : sstate := mkSS AF_fold sr_atoms [stack_region 16; got_regionP; bcell_regionP 32] None
  (mkFacts [(2%nat, fo_spF); (32%nat, fo_SBF)] [] []).
(* FO_K with k = 0: a1 is the literal 0, so `beqz a1` is taken *)
Definition fo_ss_k0 : sstate := mkSS FO_K (sr_set (sr_set sr_atoms 11 (SLit 0)) 15 (SOff 32 0)) [] None
  (mkFacts [(2%nat, fo_spF); (32%nat, fo_SBF)] [] []).
(* FO_K with k > 0: a0 = s nonzero and a1 = k in [1, 2^63] *)
Definition fo_ss_k1 : sstate := mkSS FO_K (sr_set sr_atoms 15 (SOff 32 0)) [] None
  (mkFacts [(2%nat, fo_spF); (10%nat, fo_NZF); (11%nat, fo_CNTF); (32%nat, fo_SBF)] [] []).
(* the loop head at byte i: atoms 32 the shadow base, 33 s + i, 34 out + i, 35 i, 36 k - i, 37 s[i], 38 s,
   39 k, 40 out, 41 ~out. Registers: t0 = 1, t1 = a3 = s + i, t2 = a4 = out + i, a0 = s, a1 = k, a2 = out,
   a5 = the shadow base, a6 = ~out, a7 = i, t3 = k - i *)
Definition fo_l_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
   5 (SLit 1)) 6 (SOff 33 0)) 7 (SOff 34 0)) 10 (SOff 38 0)) 11 (SOff 39 0)) 12 (SOff 40 0)) 13 (SOff 33 0))
   14 (SOff 34 0)) 15 (SOff 32 0)) 16 (SOff 41 0)) 17 (SOff 35 0)) 28 (SOff 36 0).
Definition fo_rs : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))].
Definition fo_rout (m : nat) : YP09.region := YP09.mkRegion (Some m) 0 1 0 1 [].
(* the UBSan pointer checks: s + i, out + i and out + k do not wrap *)
Definition fo_l_conds : list acond :=
  [mkAC BC_GEU (SOff 33 0) (SOff 38 0); mkAC BC_GEU (SOff 41 0) (SOff 35 0); mkAC BC_GEU (SOff 41 0) (SOff 39 0)].
Definition fo_l_facts : facts := mkFacts
  [(2%nat, fo_spF); (32%nat, fo_SBF); (33%nat, fo_PTRF); (34%nat, fo_PTRF); (35%nat, fo_IDXF); (36%nat, fo_CNTF);
   (37%nat, fo_BYTEF); (38%nat, fo_PTRF); (39%nat, fo_CNTF); (40%nat, fo_PTRF); (41%nat, fo_NOTF)] fo_l_conds [].
(* the shadow entries of the two checks of the loop body: the byte s + i and the byte out + i are addressable *)
Definition fo_l_SH : list shent := [mkSHE 33 0 1; mkSHE 34 0 1].
Definition fo_ss_loop : sstate := mkSS FO_LOOP fo_l_regs [fo_rs; fo_rout 34] None fo_l_facts.
(* the tail: atoms 32 the shadow base, 33 out + k, 34 k, 35 the saved return address *)
Definition fo_t_regs : list sv := sr_set (sr_set (sr_set sr_atoms 10 (SOff 33 0)) 11 (SOff 34 0)) 15 (SOff 32 0).
Definition fo_tstack : YP09.region := YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 35 0))].
Definition fo_t_SH : list shent := [mkSHE 33 0 1].
Definition fo_ss_tail : sstate := mkSS FO_TAIL fo_t_regs [fo_tstack; fo_rout 33] None
  (mkFacts [(2%nat, fo_spF); (32%nat, fo_SBF); (33%nat, fo_PTRF); (34%nat, fo_IDXF)] [] []).

Ltac fo_regs_ok EE eqs :=
  apply regs_ok_by_cases; intros rr Hrr; cbv [all_regs In] in Hrr;
  repeat (destruct Hrr as [<- | Hrr];
    [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a0 ?rr2) =>
        let v := eval vm_compute in (sr_get a0 rr2) in change (sr_get a0 rr2) with v end;
      cbn [sv_denot];
      first [ reflexivity
            | rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply EE; reflexivity
            | rewrite ?Z.add_0_r; eqs; assumption
            | rewrite ?Z.add_0_r; eqs; unfold w64 in *; assumption ]
    | ]); try (destruct Hrr).
Ltac fo_md :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md2 _ |- _ =>
    lazymatch md2 with with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := md2) in *; clearbody m | _ => idtac end end.
(* the branch hypothesis psrr_branch_tok leaves, whatever name it chose *)
Ltac fo_br := lazymatch goal with HB : branch_taken _ _ _ = _ |- _ => rename HB into HBR end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* a register the symbolic state holds as its own entry atom *)
Lemma fo_reg_atom : forall (H : word -> bool) Ex ss ms (r : bv 5) (k : nat) v,
  st_ok_pi SEGS VAL Ex ss (restrict H ms) -> Z.of_nat k = bv_unsigned r -> sr_get (ss_regs ss) r = SOff k 0 ->
  ew Ex k = v -> getr (ms_regs ms) r = v.
Proof.
intros H Ex ss ms r k v HS Hk Hr Hv. rewrite (st_ok_pi_restrict_reg H Ex ss ms r HS), Hr. cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hv.
Qed.
Ltac fo_same HS tac :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    apply (fo_reg_atom _ _ _ ms r k _ HS); [reflexivity | vm_compute; reflexivity | tac] end.
(* the register's symbolic value, NOT normalised (prreg's cbn would destroy sv_denot) *)
Ltac fo_rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* a region of the state the run reached *)
Lemma fo_region_of : forall E ss ms i r, st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
  region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. apply (st_ok_region_nth E (abs_ss VAL ss) ms i r HS). destruct ss; exact Hi.
Qed.
(* the shadow entry of a range the walk's checks read *)
Lemma fo_shent_ok : forall E m n x lo hi, ew E 32 = w64 SB -> bv_unsigned (ew E n) = x -> 0 <= x + lo -> x + hi < 2 ^ 64 -> lo <= hi ->
  range_addressable (rd_of SEGS m) SHADOW_OFF (x + lo) (hi - lo) ->
  (forall y, x + lo <= y < x + hi -> ~ (SB <= y < SB + 2 ^ 44)) ->
  shent_ok SEGS fo_Bx E m (mkSHE n lo hi).
Proof.
intros E m n x lo hi H32 Hn H0 H1 Hlh Hra Hband. unfold shent_ok, app_apart, fo_Bx. cbn [she_m she_lo she_hi].
assert (U32 : U E (SOff 32 0) = SB).
{ rewrite U_SOff, H32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). apply zcanon_small. unfold SB; lia. }
assert (Hxr : 0 <= x < 2 ^ 64) by (rewrite <- Hn; pose proof (bv_unsigned_in_range 64 (ew E n)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR).
assert (Un : U E (SOff n 0) = x) by (rewrite U_SOff, Hn, Z.add_0_r; apply zcanon_small; exact Hxr).
rewrite U32, Un. split; [exact Hra|].
intros y Hy. rewrite Z.min_l, Z.max_r in Hy by lia. apply Hband. lia.
Qed.
(* the extra words of a seed *)
Lemma fo_ex_w64 : forall regs1 (zl : list Z) j, (32 + j < A_TEXT)%nat -> (j < length zl)%nat ->
  ew (Eimg (Ereg regs1 (map w64 zl))) (32 + j) = w64 (nth j zl 0).
Proof.
intros regs1 zl j H1 H2. rewrite Eimg_low by exact H1. rewrite ew_Ereg_extra.
rewrite (nth_indep _ _ (w64 0)) by (rewrite length_map; exact H2). apply map_nth.
Qed.
Section e.
Variable B : asyms.
(* the record hypothesis: PALib (lib/B/Prog/SegPaLib.v: the shadow GOT word A_OBJ 0 and the shadow cell A_OBJ 12
   are as_got_shadow B and as_shadow_cell B, by role; image B 0xa3210 and 0xac7b8) *)
Hypothesis TL : PALib B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

Ltac fo_keep HFr K lo hi U1 :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : kept_out (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => lo <= x < hi) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
          [ injection Hq as <- <- <-;
            cbn [base_val extK ewset ew Nat.eqb Nat.add length] in Hrr; rewrite ?U1 in Hrr; lia | ]);
        destruct Hin
      | exact Hx0 | exact Hn0 ]) end.
(* where an object of segconf's code lies: a live heap block, a live side-stack frame or the image, below
   alloc_ceiling and apart from the shadow band (ieq's ie_loc) *)
Lemma fo_loc : forall ly S W mem md q k, AR SEGS B ly S W mem md -> sa_loc SEGS B ly S q k -> 0 < k ->
  4096 <= q /\ q + k <= alloc_ceiling /\ (forall x, q <= x < q + k -> ~ (SB <= x < SB + 2 ^ 44)).
Proof.
intros ly S W mem md q k HAR HL Hk. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HL as [(b & m & Hin & Hb & Hbm) | [(cid & pos & Hin & Hc & Hf1 & Hf2) | Himg]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & Hb4 & Hbc & Hba & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *.
  split; [lia|]. split; [lia|]. intros x Hx. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfa).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *.
  split; [lia|]. split; [lia|]. intros x Hx. lia.
- destruct (Himg q ltac:(lia)) as (Hi0 & _). destruct (Himg (q + k - 1) ltac:(lia)) as (Hi1 & _).
  pose proof (pa_img_range _ Hi0) as R0. pose proof (pa_img_range _ Hi1) as R1. unfold kImgEnd in R0, R1.
  split; [lia|]. split; [lia|]. intros x Hx. unfold SB. lia.
Qed.

(* ---------- one call of fold ---------- *)
Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (s n out cap : Z) (l : list byte).
Hypothesis HPRE : afn_pre SEGS B FO_STK ly S W regs mem md ch.
Hypothesis H10 : getr regs 10 = w64 s.
Hypothesis Hs64 : 0 <= s < 2 ^ 64.
Hypothesis H11 : getr regs 11 = w64 n.
Hypothesis Hn64 : 0 <= n < 2 ^ 64.
Hypothesis H12 : getr regs 12 = w64 out.
Hypothesis Ho64 : 0 <= out < 2 ^ 64.
Hypothesis H13 : getr regs 13 = w64 cap.
Hypothesis Hc64 : 0 <= cap < 2 ^ 64.
Hypothesis HC1 : 1 <= cap.
Hypothesis HLN : Z.of_nat (length l) = n.
Hypothesis HS0 : (0 < Z.of_nat (length (fold_out l cap)) -> s <> 0).
Hypothesis HSB : sa_bytes (rdW W mem) s (firstn (length (fold_out l cap)) l).
Hypothesis HSA : sa_addr (rdW W mem) s (Z.of_nat (length (fold_out l cap))).
Hypothesis HRA : range_addressable (rdW W mem) SHADOW_OFF out (Z.of_nat (length (fold_out l cap)) + 1).
Hypothesis HDJ : sa_disj s (Z.of_nat (length (fold_out l cap))) out (Z.of_nat (length (fold_out l cap)) + 1).
Hypothesis HSL : sa_loc SEGS B ly S s (Z.of_nat (length (fold_out l cap))).
Hypothesis HFF : sa_fframe ly S out (Z.of_nat (length (fold_out l cap)) + 1).

#[local] Notation FO := (fold_out l cap).
#[local] Notation KK := (Z.of_nat (length (fold_out l cap))).
#[local] Notation FP := [(out, out + Z.of_nat (length (fold_out l cap)) + 1)].

Definition fo_Q : world SEGS -> config -> Prop :=
apost_base SEGS B FO_STK FP regs ly S W mem md EV_fold
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 KK /\
 sa_bytes (rdW W' mem') out (SP.zb (FO ++ [0])) /\
 sa_kept SEGS W mem W' mem' regs FO_STK (fun a => out <= a < out + KK + 1) /\
 sa_noalloc B ly S ly' S').

Lemma fo_sp : spZ regs mod 16 = 0 /\ alloc_ceiling + FO_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2). lia.
Qed.
Lemma fo_KK : KK = Z.min n (cap - 1) /\ 0 <= KK /\ KK <= n /\ KK + 1 <= cap.
Proof.
pose proof (fold_out_length l cap HC1) as HL. rewrite HLN in HL. pose proof (Nat2Z.is_nonneg (length FO)). lia.
Qed.
Lemma fo_out_loc : 4096 <= out /\ out + KK + 1 <= alloc_ceiling /\
  (forall x, out <= x < out + KK + 1 -> ~ (SB <= x < SB + 2 ^ 44)).
Proof.
pose proof HPRE as (HAR & _). pose proof fo_KK as (_ & HK0 & _).
destruct (fo_loc ly S W mem md out (KK + 1) HAR (or_intror (or_introl HFF)) ltac:(lia)) as (H1 & H2 & H3).
split; [exact H1|]. split; [lia|]. intros x Hx. apply H3. lia.
Qed.
Lemma fo_s_loc : 0 < KK -> 4096 <= s /\ s + KK <= alloc_ceiling /\ (forall x, s <= x < s + KK -> ~ (SB <= x < SB + 2 ^ 44)).
Proof. intros Hk. pose proof HPRE as (HAR & _). exact (fo_loc ly S W mem md s KK HAR HSL Hk). Qed.
(* fold may write out's k + 1 bytes: they are in the footprint and in a live caller frame *)
Lemma fo_awr_out : forall a, out <= a < out + KK + 1 ->
  awr_byte SEGS B FO_STK (spZ regs) FP (ablocks B ly S) (ablocks B ly S) (frames S) ly [] a.
Proof.
intros a Ha. right. right. right. right. right. right.
split; [exists (out, out + KK + 1); split; [left; reflexivity | cbn [fst snd]; lia]|].
destruct HFF as (cid & pos & Hin & Hc & H1 & H2). exists cid, pos. split; [exact Hin|].
left. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma fo_present : forall mem1 md1 a, AR SEGS B ly S W mem1 md1 -> out <= a < out + KK + 1 -> apresent (w_H W) mem1 a.
Proof.
intros mem1 md1 a HAR Ha. destruct HFF as (cid & pos & Hin & Hc & H1 & H2).
destruct (al_frames _ _ LAWS ly S W mem1 md1 cid pos HAR Hin) as (_ & _ & Hb & _).
exact (proj1 (Hb a ltac:(lia))).
Qed.

(* what the walk keeps: every byte outside the stack window and outside [out, out + k + 1) *)
Definition fo_kept (mem1 : word -> option byte) : Prop :=
  sa_kept SEGS W mem W mem1 regs FO_STK (fun a => out <= a < out + KK + 1).
(* the callee-saved registers fold never writes (sp is kept apart: it is sp0 - 16 inside the body) *)
Definition fo_csl : list Z := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition fo_cs (r1 : bvmap 5 word) : Prop := forall r, In r fo_csl -> getr r1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
(* the return address in the frame *)
Definition fo_frame (rd : reader) : Prop := sa_val rd (spZ regs - 8) 8 (bv_unsigned (getr regs 1)).
(* a memory cut with i bytes folded *)
Definition fo_mcut (i : nat) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  ajournal SEGS B FO_STK (spZ regs) FP ly S W mem md [] ly S W mem1 md1 0 /\
  fo_kept mem1 /\ fo_frame (rdW W mem1) /\
  (forall j, (j < i)%nat -> rdW W mem1 (out + Z.of_nat j) = Some (nth j FO 0)).
Definition fo_cut (i : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  fo_mcut i mem1 md1 /\ getr regs1 2 = w64 (spZ regs - 16) /\ fo_cs regs1.

Lemma fo_cs_trans : forall r1 r2, fo_cs r1 ->
  (forall r, In r fo_csl -> getr r2 (Z_to_bv 5 r) = getr r1 (Z_to_bv 5 r)) -> fo_cs r2.
Proof. intros r1 r2 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma fo_pres_of_cs : forall r1, fo_cs r1 -> getr r1 (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2) -> aregs_preserved regs r1.
Proof.
intros r1 HCS H2 r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ In r fo_csl) by (unfold fo_csl; cbn [In]; lia).
destruct Hc as [->|Hin]; [exact H2 | exact (HCS r Hin)].
Qed.
Lemma fo_mcut_keep : forall i mem1 md1 mem2 md2 lo hi,
  (i <= length FO)%nat -> fo_mcut i mem1 md1 ->
  ajournal SEGS B FO_STK (spZ regs) FP ly S W mem md [] ly S W mem2 md2 0 ->
  kept_out (rdW W mem1) (rdW W mem2) lo hi ->
  (forall a, lo <= a < hi -> out + Z.of_nat i <= a < out + KK + 1) ->
  fo_mcut i mem2 md2.
Proof.
intros i mem1 md1 mem2 md2 lo hi Hi (HJ & HK & HFR & HM) HJ2 HK2 Hwin.
pose proof fo_sp as (Hal16 & Hslo & Hshi). pose proof fo_out_loc as (Ho4 & Hoc & _).
pose proof fo_KK as (_ & HK0 & HKn & _).
assert (HST : FO_STK = 16) by reflexivity.
split; [exact HJ2|]. split.
{ intros a Ha Hs1 Hs2. destruct (Z_lt_le_dec a lo) as [Hl|Hl]; [rewrite (HK2 a Ha) by lia; exact (HK a Ha Hs1 Hs2)|].
  destruct (Z_lt_le_dec a hi) as [Hh|Hh]; [exfalso; apply Hs2; pose proof (Hwin a ltac:(lia)); lia|].
  rewrite (HK2 a Ha) by lia. exact (HK a Ha Hs1 Hs2). }
split.
{ intros k Hk. pose proof (HFR k Hk) as Hv.
  assert (Hr : 0 <= spZ regs - 8 + Z.of_nat k < 2 ^ 64) by lia.
  rewrite (HK2 _ Hr); [exact Hv|]. intros Hin. pose proof (Hwin _ Hin). lia. }
intros j Hj. pose proof (HM j Hj) as Hv.
assert (Hjk : Z.of_nat j < KK) by lia.
assert (Hr : 0 <= out + Z.of_nat j < 2 ^ 64) by lia.
rewrite (HK2 _ Hr); [exact Hv|]. intros Hin. pose proof (Hwin _ Hin). lia.
Qed.
Lemma fo_cut_keep : forall i regs1 mem1 md1 regs2 mem2 md2 lo hi,
  (i <= length FO)%nat -> fo_cut i regs1 mem1 md1 ->
  ajournal SEGS B FO_STK (spZ regs) FP ly S W mem md [] ly S W mem2 md2 0 ->
  kept_out (rdW W mem1) (rdW W mem2) lo hi ->
  (forall a, lo <= a < hi -> out + Z.of_nat i <= a < out + KK + 1) ->
  getr regs2 2 = getr regs1 2 ->
  (forall r, In r fo_csl -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
  fo_cut i regs2 mem2 md2.
Proof.
intros i regs1 mem1 md1 regs2 mem2 md2 lo hi Hi (HMC & R2 & RCS) HJ2 HK2 Hwin Q2 QCS.
split; [exact (fo_mcut_keep i mem1 md1 mem2 md2 lo hi Hi HMC HJ2 HK2 Hwin)|].
split; [rewrite Q2; exact R2 | exact (fo_cs_trans regs1 regs2 RCS QCS)].
Qed.
Lemma fo_cut_S : forall i regs1 mem1 md1, fo_cut i regs1 mem1 md1 ->
  rdW W mem1 (out + Z.of_nat i) = Some (nth i FO 0) -> fo_cut (Datatypes.S i) regs1 mem1 md1.
Proof.
intros i regs1 mem1 md1 ((HJ & HK & HFR & HM) & R2 & RCS) Hv.
split; [|split; [exact R2 | exact RCS]].
split; [exact HJ|]. split; [exact HK|]. split; [exact HFR|].
intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne]; [exact Hv|]. apply HM. lia.
Qed.
(* the shadow of out's bytes, and of s's, survives every step: shadow addresses are inside [SB, SB + 2^44),
   which is below the stack window and apart from both objects *)
Lemma fo_ra_out : forall mem1, fo_kept mem1 -> range_addressable (rdW W mem1) SHADOW_OFF out (KK + 1).
Proof.
intros mem1 HK x Hx. pose proof fo_sp as (Hal16 & Hslo & Hshi). pose proof fo_out_loc as (Ho4 & Hoc & Hob).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : FO_STK = 16) by reflexivity.
destruct (HRA x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
rewrite <- Hsv. unfold shadow_of_addr, SHADOW_OFF in *.
assert (Hd0 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (Hd1 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
apply HK; [unfold SB in *; lia | unfold SB in *; lia |].
intros Hin. apply (Hob _ Hin). unfold SB. lia.
Qed.
Lemma fo_ra_s : forall mem1, fo_kept mem1 -> 0 < KK -> range_addressable (rdW W mem1) SHADOW_OFF s KK.
Proof.
intros mem1 HK Hk x Hx. pose proof fo_sp as (Hal16 & Hslo & Hshi). pose proof fo_out_loc as (Ho4 & Hoc & Hob).
pose proof (fo_s_loc Hk) as (Hs4 & Hsc & Hsb).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : FO_STK = 16) by reflexivity.
pose proof HSA as (A0 & A1 & A2 & A3 & A4).
destruct (A3 x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
rewrite <- Hsv. unfold shadow_of_addr, SHADOW_OFF in *.
assert (Hd0 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (Hd1 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
apply HK; [unfold SB in *; lia | unfold SB in *; lia |].
intros Hin. apply (Hob _ Hin). unfold SB. lia.
Qed.
(* the byte of s the loop reads at i, at any cut *)
Lemma fo_byte_s : forall mem1 i, fo_kept mem1 -> (i < length FO)%nat ->
  rdW W mem1 (s + Z.of_nat i) = Some (bv_unsigned (nth i l ZB0)).
Proof.
intros mem1 i HK Hi. pose proof fo_sp as (Hal16 & Hslo & Hshi).
pose proof (fo_s_loc ltac:(lia)) as (Hs4 & Hsc & Hsb). pose proof fo_out_loc as (Ho4 & Hoc & Hob).
pose proof fo_KK as (_ & HK0 & HKn & _).
assert (HST : FO_STK = 16) by reflexivity.
assert (Hil : (i < length l)%nat) by lia.
assert (Hlf : (i < length (firstn (length FO) l))%nat) by (rewrite length_firstn; lia).
pose proof (HSB i Hlf) as Hv. rewrite fo_nth_firstn in Hv by lia.
rewrite <- Hv. apply HK; [lia | lia |]. intros Hin. destruct HDJ as [Hd|Hd]; lia.
Qed.

(* ---------- the tail: 0x87d70 .. 0x87d90, the NUL at out + k, a0 := k, ret ---------- *)
Definition fo_t_extra : list word := [w64 SB; w64 (out + KK); w64 KK; getr regs 1].
Lemma fo_tail_seed : forall regs1 mem1 md1,
  fo_cut (length FO) regs1 mem1 md1 ->
  getr regs1 10 = w64 (out + KK) -> getr regs1 11 = w64 KK -> getr regs1 15 = w64 SB ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 fo_t_extra)) fo_ss_tail
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + FO_TAIL)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS fo_Bx fo_t_SH (Eimg (Ereg regs1 fo_t_extra)) (mrestrict (w_H W) mem1).
Proof.
intros regs1 mem1 md1 HCUT R10 R11 R15.
pose proof HCUT as ((HJ & HK & HFR & HM) & R2 & RCS).
pose proof fo_sp as (Hal16 & Hslo & Hshi). pose proof fo_out_loc as (Ho4 & Hoc & Hob).
pose proof fo_KK as (_ & HK0 & HKn & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : FO_STK = 16) by reflexivity.
pose proof HJ as (HAR1 & _).
set (E := Eimg (Ereg regs1 fo_t_extra)).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = w64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 fo_t_extra 0)).
assert (E33 : ew E 33 = w64 (out + KK))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 fo_t_extra 1)).
assert (E34 : ew E 34 = w64 KK)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 fo_t_extra 2)).
assert (E35 : ew E 35 = getr regs 1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 fo_t_extra 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 16)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = out + KK) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = KK) by (rewrite E34; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold fo_ss_tail. apply pa_entry_st_ok_full.
  + fo_regs_ok EE ltac:(rewrite ?E32u, ?E33u, ?E34u).
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold region_ok, fo_tstack.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      pose proof (bv_unsigned_in_range 64 (getr regs 1)) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
      apply (chunk_ok_val SEGS E _ (spZ regs - 16) 8 8 (SOff 35 0) (bv_unsigned (getr regs 1))).
      -- cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HRr.
      -- cbn. lia.
      -- replace (spZ regs - 16 + 8) with (spZ regs - 8) by lia.
         apply fo_val_mem_of_sa_val. exact HFR.
    * unfold region_ok, fo_rout.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E33u.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply (fo_present mem1 md1); [exact HAR1 | lia].
  + apply pairwise_disjoint_of_extents. unfold fo_tstack, fo_rout, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, E33u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, fo_spF, fo_SBF, fo_PTRF, fo_IDXF.
    cbn [af_lo af_hi af_al2]. rewrite Usp, E32u, E33u, E34u. change (2 ^ 4) with 16.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; rewrite Zminus_mod, Hal16; reflexivity.
- unfold sh_ok, fo_t_SH. apply Forall_cons; [|apply Forall_nil].
  apply (fo_shent_ok E _ 33 (out + KK) 0 1 E32 E33u); try lia.
  + rewrite Z.add_0_r.
    apply (range_addressable_sub (rd_of SEGS (mrestrict (w_H W) mem1)) SHADOW_OFF out (KK + 1)); [|lia|lia].
    exact (fo_ra_out mem1 HK).
  + intros y Hy. apply Hob. lia.
Qed.
Lemma fo_tail : forall regs1 mem1 md1,
  fo_cut (length FO) regs1 mem1 md1 ->
  getr regs1 10 = w64 (out + KK) -> getr regs1 11 = w64 KK -> getr regs1 15 = w64 SB ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + FO_TAIL)) mem1 (seg_rom SEGS)) md1) fo_Q.
Proof.
intros regs1 mem1 md1 HCUT R10 R11 R15.
pose proof HCUT as (HMC & R2 & RCS). pose proof HMC as (HJ & HK & HFR & HM).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof fo_sp as (Hal16 & Hslo & Hshi). pose proof fo_out_loc as (Ho4 & Hoc & Hob).
pose proof fo_KK as (_ & HK0 & HKn & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : FO_STK = 16) by reflexivity.
destruct (fo_tail_seed regs1 mem1 md1 HCUT R10 R11 R15) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 fo_t_extra))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 fo_t_extra)) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E33 : ew (Eimg (Ereg regs1 fo_t_extra)) 33 = w64 (out + KK))
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 fo_t_extra 1)).
assert (E34 : ew (Eimg (Ereg regs1 fo_t_extra)) 34 = w64 KK)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 fo_t_extra 2)).
assert (E35 : ew (Eimg (Ereg regs1 fo_t_extra)) 35 = getr regs 1)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 fo_t_extra 3)).
remember (Eimg (Ereg regs1 fo_t_extra)) as E eqn:HE0. clear HE0.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 16)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew E 33) = out + KK) by (rewrite E33; apply unsigned_lit_small; lia).
(* 0x87d70 .. 0x87d90: the check of out + k, `sb zero`, a0 := k, ra restored, sp += 16, ret *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac.
  eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ _ _ 33%nat); [reflexivity | exact E33u | | apply YCbq.awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply fo_awr_out. lia. }
fo_md.
fo_keep HFr KEEPT (out + KK) (out + KK + 1) E33u. clear HF HFr HG.
(* the NUL the tail stored *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let rr := eval vm_compute in (nth_error (ss_mem ssx) 1%nat) in
  lazymatch rr with Some ?r0 =>
    pose proof (fo_region_of Ex ssx (restrict (w_H W) msx) 1%nat r0 HS ltac:(vm_compute; reflexivity)) as HRg end;
  cbn [ms_mem restrict] in HRg;
  assert (E33x : bv_unsigned (ew Ex 33) = out + KK)
    by (cbn [extK ewset ew Nat.eqb Nat.add length]; exact E33u) end.
lazymatch type of HRg with region_ok _ ?Ex _ _ =>
  pose proof (field_of_region Ex _ 33%nat (out + KK) _ 0 1 0 1 0 1 (SLit 0) 0 HRg E33x
    ltac:(cbn [In]; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as HNv end.
rewrite Z.add_0_r in HNv.
assert (HNUL : rdW W (ms_mem ms) (out + KK) = Some 0) by (apply (fo_rd1 SEGS); [exact HNv | lia]).
assert (HMCF : fo_mcut (length FO) (ms_mem ms) mdv).
{ apply (fo_mcut_keep (length FO) mem1 md1 _ _ (out + KK) (out + KK + 1) ltac:(lia) HMC HJ KEEPT).
  intros a Ha. lia. }
pose proof HMCF as (HJF & HKF & HFRF & HMF).
prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
assert (RCSF : fo_cs (ms_regs ms)).
{ apply (fo_cs_trans regs1 _ RCS). intros rr Hrr. unfold fo_csl in Hrr. cbn [In] in Hrr.
  repeat (destruct Hrr as [<- | Hrr];
    [ fo_same HS ltac:(cbn [extK ewset ew Nat.eqb Nat.add length]; apply EE; reflexivity) | ]).
  destruct Hrr. }
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold fo_Q, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split.
{ rewrite F1, E35. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJF. }
split.
{ apply fo_pres_of_cs; [exact RCSF|].
  rewrite (st_ok_pi_restrict_reg (w_H W) _ _ _ (Z_to_bv 5 2) HS).
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
    let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end.
  cbn [sv_denot]. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite Usp.
  replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold spZ.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [|split; [|split]].
- rewrite F10. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite E34. reflexivity.
- (* the folded text and its NUL at out *)
  intros j Hj. rewrite fo_zb_length, length_app in Hj. cbn [length] in Hj.
  unfold SP.zb. rewrite (fo_map_nth (Z_to_bv 8) _ j 0 ZB0) by (rewrite length_app; cbn [length]; lia).
  destruct (Nat.lt_ge_cases j (length FO)) as [Hlt|Hge].
  + rewrite (HMF j Hlt). f_equal. rewrite app_nth1 by exact Hlt.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    symmetry. apply Z.mod_small. exact (fo_nth_rng l cap j Hlt).
  + assert (Hje : j = length FO) by lia. subst j.
    replace (out + Z.of_nat (length FO)) with (out + KK) by lia. rewrite HNUL. f_equal.
    rewrite app_nth2 by lia. replace (length FO - length FO)%nat with 0%nat by lia. reflexivity.
- exact HKF.
- split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs S). destruct S; reflexivity.
Qed.

(* ---------- the loop head: 0x87cd8 at byte i ---------- *)
Definition fo_l_extra (i : nat) (c : Z) : list word :=
  map w64 [SB; s + Z.of_nat i; out + Z.of_nat i; Z.of_nat i; KK - Z.of_nat i; c; s; KK; out; 2 ^ 64 - 1 - out].
Definition fo_LP (i : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  fo_cut i regs1 mem1 md1 /\ (i < length FO)%nat /\
  getr regs1 5 = w64 1 /\ getr regs1 6 = w64 (s + Z.of_nat i) /\ getr regs1 7 = w64 (out + Z.of_nat i) /\
  getr regs1 10 = w64 s /\ getr regs1 11 = w64 KK /\ getr regs1 12 = w64 out /\
  getr regs1 13 = w64 (s + Z.of_nat i) /\ getr regs1 14 = w64 (out + Z.of_nat i) /\
  getr regs1 15 = w64 SB /\ getr regs1 16 = w64 (2 ^ 64 - 1 - out) /\
  getr regs1 17 = w64 (Z.of_nat i) /\ getr regs1 28 = w64 (KK - Z.of_nat i).
Lemma fo_loop_seed : forall i c regs1 mem1 md1,
  fo_cut i regs1 mem1 md1 -> (i < length FO)%nat -> 0 <= c < 256 ->
  rdW W mem1 (s + Z.of_nat i) = Some c ->
  getr regs1 5 = w64 1 -> getr regs1 6 = w64 (s + Z.of_nat i) -> getr regs1 7 = w64 (out + Z.of_nat i) ->
  getr regs1 10 = w64 s -> getr regs1 11 = w64 KK -> getr regs1 12 = w64 out ->
  getr regs1 13 = w64 (s + Z.of_nat i) -> getr regs1 14 = w64 (out + Z.of_nat i) ->
  getr regs1 15 = w64 SB -> getr regs1 16 = w64 (2 ^ 64 - 1 - out) ->
  getr regs1 17 = w64 (Z.of_nat i) -> getr regs1 28 = w64 (KK - Z.of_nat i) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 (fo_l_extra i c))) fo_ss_loop
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + FO_LOOP)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS fo_Bx fo_l_SH (Eimg (Ereg regs1 (fo_l_extra i c))) (mrestrict (w_H W) mem1).
Proof.
intros i c regs1 mem1 md1 HCUT Hi Hc VS R5 R6 R7 R10 R11 R12 R13 R14 R15 R16 R17 R28.
pose proof HCUT as ((HJ & HK & HFR & HM) & R2 & RCS).
pose proof HJ as (HAR1 & _).
pose proof fo_sp as (Hal16 & Hslo & Hshi). pose proof fo_out_loc as (Ho4 & Hoc & Hob).
pose proof fo_KK as (_ & HK0 & HKn & _).
pose proof (fo_s_loc ltac:(lia)) as (Hs4 & Hsc & Hsb).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : FO_STK = 16) by reflexivity.
set (E := Eimg (Ereg regs1 (fo_l_extra i c))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j v, nth_error [SB; s + Z.of_nat i; out + Z.of_nat i; Z.of_nat i; KK - Z.of_nat i; c; s; KK; out; 2 ^ 64 - 1 - out] j = Some v ->
  ew E (32 + j) = w64 v).
{ intros j v Hj. assert (Hj10 : (j < 10)%nat) by (change 10%nat with (length [SB; s + Z.of_nat i; out + Z.of_nat i; Z.of_nat i; KK - Z.of_nat i; c; s; KK; out; 2 ^ 64 - 1 - out]); apply (proj1 (nth_error_Some _ j)); rewrite Hj; discriminate).
  subst E. unfold fo_l_extra. rewrite fo_ex_w64 by (cbn; unfold A_TEXT; lia). f_equal. apply nth_error_nth. exact Hj. }
pose proof (EX 0%nat _ eq_refl) as E32. pose proof (EX 1%nat _ eq_refl) as E33. pose proof (EX 2%nat _ eq_refl) as E34.
pose proof (EX 3%nat _ eq_refl) as E35. pose proof (EX 4%nat _ eq_refl) as E36. pose proof (EX 5%nat _ eq_refl) as E37.
pose proof (EX 6%nat _ eq_refl) as E38. pose proof (EX 7%nat _ eq_refl) as E39. pose proof (EX 8%nat _ eq_refl) as E40.
pose proof (EX 9%nat _ eq_refl) as E41.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 16)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = s + Z.of_nat i) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = out + Z.of_nat i) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = Z.of_nat i) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = KK - Z.of_nat i) by (rewrite E36; apply unsigned_lit_small; lia).
assert (E37u : bv_unsigned (ew E 37) = c) by (rewrite E37; apply unsigned_lit_small; lia).
assert (E38u : bv_unsigned (ew E 38) = s) by (rewrite E38; apply unsigned_lit_small; lia).
assert (E39u : bv_unsigned (ew E 39) = KK) by (rewrite E39; apply unsigned_lit_small; lia).
assert (E40u : bv_unsigned (ew E 40) = out) by (rewrite E40; apply unsigned_lit_small; lia).
assert (E41u : bv_unsigned (ew E 41) = 2 ^ 64 - 1 - out) by (rewrite E41; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold fo_ss_loop. apply pa_entry_st_ok_full.
  + fo_regs_ok EE ltac:(rewrite ?E32u, ?E33u, ?E34u, ?E35u, ?E36u, ?E37u, ?E38u, ?E39u, ?E40u, ?E41u).
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold region_ok, fo_rs.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E33u.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (s + Z.of_nat i) 0 1 (SOff 37 0) c);
        [cbn [sv_denot]; rewrite E37u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      apply fo_val_mem_of_sa_val. rewrite Z.add_0_r. exact (fo_val1 _ _ _ VS Hc).
    * unfold region_ok, fo_rout.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E34u.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply (fo_present mem1 md1); [exact HAR1 | lia].
  + apply pairwise_disjoint_of_extents. unfold fo_rs, fo_rout, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E33u, E34u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct HDJ as [Hd|Hd]; repeat split; lia.
  + split.
    * cbn [f_atoms atoms_ok fo_l_facts]. unfold afact_ok, fo_spF, fo_SBF, fo_PTRF, fo_CNTF, fo_IDXF, fo_BYTEF, fo_NOTF.
      cbn [af_lo af_hi af_al2].
      rewrite Usp, E32u, E33u, E34u, E35u, E36u, E37u, E38u, E39u, E40u, E41u. change (2 ^ 4) with 16.
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat split; try lia; rewrite Zminus_mod, Hal16; reflexivity.
    * (* the three assumed conditions: s + i >=u s, ~out >=u i and ~out >=u k *)
      split; [|exact I]. cbn [conds_ok fo_l_conds f_conds fo_l_facts].
      split; [apply (fo_cond_geu E 33 38 (s + Z.of_nat i) s E33 E38); lia|].
      split; [apply (fo_cond_geu E 41 35 (2 ^ 64 - 1 - out) (Z.of_nat i) E41 E35); lia|].
      split; [apply (fo_cond_geu E 41 39 (2 ^ 64 - 1 - out) KK E41 E39); lia|]. exact I.
- unfold sh_ok, fo_l_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (fo_shent_ok E _ 33 (s + Z.of_nat i) 0 1 E32 E33u); try lia.
    * rewrite Z.add_0_r.
      apply (range_addressable_sub (rd_of SEGS (mrestrict (w_H W) mem1)) SHADOW_OFF s KK); [|lia|lia].
      exact (fo_ra_s mem1 HK ltac:(lia)).
    * intros y Hy. apply Hsb. lia.
  + apply (fo_shent_ok E _ 34 (out + Z.of_nat i) 0 1 E32 E34u); try lia.
    * rewrite Z.add_0_r.
      apply (range_addressable_sub (rd_of SEGS (mrestrict (w_H W) mem1)) SHADOW_OFF out (KK + 1)); [|lia|lia].
      exact (fo_ra_out mem1 HK).
    * intros y Hy. apply Hob. lia.
Qed.

Lemma fo_loop_step : forall i regs1 mem1 md1,
  ((Datatypes.S i < length FO)%nat -> forall r m d, fo_LP (Datatypes.S i) r m d ->
    SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + FO_LOOP)) m (seg_rom SEGS)) d) fo_Q) ->
  fo_LP i regs1 mem1 md1 ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + FO_LOOP)) mem1 (seg_rom SEGS)) md1) fo_Q.
Proof.
intros i regs1 mem1 md1 NXT (HCUT & Hi & R5 & R6 & R7 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R28).
pose proof HCUT as (HMC & R2 & RCS). pose proof HMC as (HJ & HK & HFR & HM).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof fo_sp as (Hal16 & Hslo & Hshi). pose proof fo_out_loc as (Ho4 & Hoc & Hob).
pose proof fo_KK as (_ & HK0 & HKn & _).
pose proof (fo_s_loc ltac:(lia)) as (Hs4 & Hsc & Hsb).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : FO_STK = 16) by reflexivity.
set (c := bv_unsigned (nth i l ZB0)).
assert (Hcr : 0 <= c < 256)
  by (subst c; pose proof (bv_unsigned_in_range 8 (nth i l ZB0)) as HR; change (bv_modulus 8) with 256 in HR; exact HR).
assert (VS : rdW W mem1 (s + Z.of_nat i) = Some c) by (apply fo_byte_s; [exact HK | exact Hi]).
assert (HFOi : nth i FO 0 = SM.lower c) by (subst c; apply fo_nth_val; exact Hi).
clearbody c.
destruct (fo_loop_seed i c regs1 mem1 md1 HCUT Hi Hcr VS R5 R6 R7 R10 R11 R12 R13 R14 R15 R16 R17 R28) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (fo_l_extra i c)))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 (fo_l_extra i c))) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j v, nth_error [SB; s + Z.of_nat i; out + Z.of_nat i; Z.of_nat i; KK - Z.of_nat i; c; s; KK; out; 2 ^ 64 - 1 - out] j = Some v ->
  ew (Eimg (Ereg regs1 (fo_l_extra i c))) (32 + j) = w64 v).
{ intros j v Hj. assert (Hj10 : (j < 10)%nat) by (change 10%nat with (length [SB; s + Z.of_nat i; out + Z.of_nat i; Z.of_nat i; KK - Z.of_nat i; c; s; KK; out; 2 ^ 64 - 1 - out]); apply (proj1 (nth_error_Some _ j)); rewrite Hj; discriminate).
  unfold fo_l_extra. rewrite fo_ex_w64 by (cbn; unfold A_TEXT; lia). f_equal. apply nth_error_nth. exact Hj. }
pose proof (EX 0%nat _ eq_refl) as E32. pose proof (EX 1%nat _ eq_refl) as E33. pose proof (EX 2%nat _ eq_refl) as E34.
pose proof (EX 3%nat _ eq_refl) as E35. pose proof (EX 4%nat _ eq_refl) as E36. pose proof (EX 5%nat _ eq_refl) as E37.
pose proof (EX 6%nat _ eq_refl) as E38. pose proof (EX 7%nat _ eq_refl) as E39. pose proof (EX 8%nat _ eq_refl) as E40.
pose proof (EX 9%nat _ eq_refl) as E41.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41. clear EX.
remember (Eimg (Ereg regs1 (fo_l_extra i c))) as E eqn:HE0. clear HE0.
assert (E33u : bv_unsigned (ew E 33) = s + Z.of_nat i) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = out + Z.of_nat i) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = Z.of_nat i) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = KK - Z.of_nat i) by (rewrite E36; apply unsigned_lit_small; lia).
assert (E37u : bv_unsigned (ew E 37) = c) by (rewrite E37; apply unsigned_lit_small; lia).
assert (E39u : bv_unsigned (ew E 39) = KK) by (rewrite E39; apply unsigned_lit_small; lia).
assert (E40u : bv_unsigned (ew E 40) = out) by (rewrite E40; apply unsigned_lit_small; lia).
(* 0x87cd8 .. 0x87d40: the UBSan checks, the two instrumented checks, the fold, `sb` at out + i, the cursors *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac.
  eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ _ _ 34%nat); [reflexivity | exact E34u | | apply YCbq.awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply fo_awr_out. lia. }
fo_md.
fo_keep HFr KEEP1 (out + Z.of_nat i) (out + Z.of_nat i + 1) E34u. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the last byte: t3 - 1 = 0, so i + 1 = k; 0x87d68, then the tail *)
  fo_br.
  assert (HiK : Z.of_nat i + 1 = KK).
  { rewrite branch_eq_U, U_SLit in HBR.
    lazymatch type of HBR with (U ?Ex (SOff 36 ?o) =? _) = _ =>
      rewrite (U_atom_off Ex 36 (KK - Z.of_nat i) o) in HBR
        by (first [cbn [extK ewset ew Nat.eqb Nat.add length]; exact E36 | lia]) end.
    apply Z.eqb_eq in HBR. change (zcanon 0) with 0 in HBR. lia. }
  clear HBR.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan FO_TAIL.
  { awr_ok_tac.
    eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ _ _ 34%nat); [reflexivity |
      cbn [extK ewset ew Nat.eqb Nat.add length]; exact E34u | | apply YCbq.awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply fo_awr_out. lia. }
  fo_md.
  fo_keep HFr KEEP2 (out + Z.of_nat i) (out + Z.of_nat i + 1) E34u. clear HF HFr HG.
  pmkst HS.
  fo_rreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (15%bv : bv 5) Q15.
  (* the byte the loop stored at out + i *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    let rr := eval vm_compute in (nth_error (ss_mem ssx) 1%nat) in
  lazymatch rr with Some ?r0 =>
    pose proof (fo_region_of Ex ssx (restrict (w_H W) msx) 1%nat r0 HS ltac:(vm_compute; reflexivity)) as HRg end;
    cbn [ms_mem restrict] in HRg;
    assert (E34x : bv_unsigned (ew Ex 34) = out + Z.of_nat i) by (cbn [extK ewset ew Nat.eqb Nat.add length]; exact E34u);
    assert (E37x : bv_unsigned (ew Ex 37) = c) by (cbn [extK ewset ew Nat.eqb Nat.add length]; exact E37u) end.
  lazymatch type of HRg with region_ok _ ?Ex _ _ =>
    pose proof (field_of_region Ex _ 34%nat (out + Z.of_nat i) _ 0 1 0 1 0 1
      (SAlu ALU_ADD (SOff 37 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 37 (-65)) (SLit 26)) (SLit 5))) (SM.lower c)
      HRg E34x ltac:(cbn [In]; tauto)
      ltac:(rewrite denot_lit_U; f_equal; fo_U_norm; rewrite ?E37x; fo_brute c Hcr)
      ltac:(cbn; pose proof (fo_lower_rng c Hcr); lia) ltac:(cbn; lia)) as HBv end.
  rewrite Z.add_0_r in HBv. change (N.to_nat 1) with 1%nat in HBv.
  lazymatch type of HBv with val_mem _ (mrestrict _ ?mF) _ _ _ =>
    assert (HBYTE : aview SEGS (w_H W) mF (out + Z.of_nat i) = Some (SM.lower c))
      by (apply (fo_rd1 SEGS); [exact HBv | apply fo_lower_rng; exact Hcr]) end.
  assert (HiN : (Datatypes.S i = length FO)%nat) by lia.
  apply fo_tail.
  + rewrite <- HiN. apply fo_cut_S; [|rewrite HFOi; exact HBYTE].
    eapply (fo_cut_keep i regs1 mem1 md1 _ _ _ (out + Z.of_nat i) (out + Z.of_nat i + 1) ltac:(lia) HCUT HJ
      (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2 ltac:(lia) ltac:(lia))).
    * intros a Ha. lia.
    * fo_same HS ltac:(cbn [extK ewset ew Nat.eqb Nat.add length]; apply EE; reflexivity).
    * intros rr Hrr. unfold fo_csl in Hrr. cbn [In] in Hrr.
      repeat (destruct Hrr as [<- | Hrr];
        [ fo_same HS ltac:(cbn [extK ewset ew Nat.eqb Nat.add length]; apply EE; reflexivity) | ]).
      destruct Hrr.
  + rewrite Q10, denot_lit_U. unfold w64. f_equal. fo_U_norm. cbn [zalu_raw].
    cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite E39u, E40u, !Z.add_0_r.
    rewrite (zcanon_small KK) by lia. rewrite (zcanon_small out) by lia.
    rewrite zcanon_id by (unfold M64; lia). lia.
  + rewrite Q11. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite E39. reflexivity.
  + rewrite Q15. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite E32. reflexivity.
- (* more bytes: back to the loop head at i + 1 *)
  fo_br.
  assert (HiK : Z.of_nat (Datatypes.S i) < KK).
  { rewrite branch_eq_U, U_SLit in HBR.
    lazymatch type of HBR with (U ?Ex (SOff 36 ?o) =? _) = _ =>
      rewrite (U_atom_off Ex 36 (KK - Z.of_nat i) o) in HBR
        by (first [cbn [extK ewset ew Nat.eqb Nat.add length]; exact E36 | lia]) end.
    apply Z.eqb_neq in HBR. change (zcanon 0) with 0 in HBR. lia. }
  clear HBR.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan FO_LOOP.
  { awr_ok_tac.
    eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ _ _ 34%nat); [reflexivity |
      cbn [extK ewset ew Nat.eqb Nat.add length]; exact E34u | | apply YCbq.awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply fo_awr_out. lia. }
  fo_md.
  fo_keep HFr KEEP2 (out + Z.of_nat i) (out + Z.of_nat i + 1) E34u. clear HF HFr HG.
  pmkst HS.
  prreg HS (5%bv : bv 5) Q5. prreg HS (6%bv : bv 5) Q6. prreg HS (7%bv : bv 5) Q7.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15.
  prreg HS (16%bv : bv 5) Q16. prreg HS (17%bv : bv 5) Q17. prreg HS (28%bv : bv 5) Q28.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    let rr := eval vm_compute in (nth_error (ss_mem ssx) 1%nat) in
  lazymatch rr with Some ?r0 =>
    pose proof (fo_region_of Ex ssx (restrict (w_H W) msx) 1%nat r0 HS ltac:(vm_compute; reflexivity)) as HRg end;
    cbn [ms_mem restrict] in HRg;
    assert (E34x : bv_unsigned (ew Ex 34) = out + Z.of_nat i) by (cbn [extK ewset ew Nat.eqb Nat.add length]; exact E34u);
    assert (E37x : bv_unsigned (ew Ex 37) = c) by (cbn [extK ewset ew Nat.eqb Nat.add length]; exact E37u) end.
  lazymatch type of HRg with region_ok _ ?Ex _ _ =>
    pose proof (field_of_region Ex _ 34%nat (out + Z.of_nat i) _ 0 1 0 1 0 1
      (SAlu ALU_ADD (SOff 37 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 37 (-65)) (SLit 26)) (SLit 5))) (SM.lower c)
      HRg E34x ltac:(cbn [In]; tauto)
      ltac:(rewrite denot_lit_U; f_equal; fo_U_norm; rewrite ?E37x; fo_brute c Hcr)
      ltac:(cbn; pose proof (fo_lower_rng c Hcr); lia) ltac:(cbn; lia)) as HBv end.
  rewrite Z.add_0_r in HBv. change (N.to_nat 1) with 1%nat in HBv.
  lazymatch type of HBv with val_mem _ (mrestrict _ ?mF) _ _ _ =>
    assert (HBYTE : aview SEGS (w_H W) mF (out + Z.of_nat i) = Some (SM.lower c))
      by (apply (fo_rd1 SEGS); [exact HBv | apply fo_lower_rng; exact Hcr]) end.
  apply (NXT ltac:(lia)). split.
  { apply fo_cut_S; [|rewrite HFOi; exact HBYTE].
    eapply (fo_cut_keep i regs1 mem1 md1 _ _ _ (out + Z.of_nat i) (out + Z.of_nat i + 1) ltac:(lia) HCUT HJ
      (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2 ltac:(lia) ltac:(lia))).
    - intros a Ha. lia.
    - fo_same HS ltac:(cbn [extK ewset ew Nat.eqb Nat.add length]; apply EE; reflexivity).
    - intros rr Hrr. unfold fo_csl in Hrr. cbn [In] in Hrr.
      repeat (destruct Hrr as [<- | Hrr];
        [ fo_same HS ltac:(cbn [extK ewset ew Nat.eqb Nat.add length]; apply EE; reflexivity) | ]).
      destruct Hrr. }
  split; [lia|].
  split; [rewrite Q5; reflexivity|].
  split; [rewrite Q6; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite E33u; unfold w64; f_equal; lia|].
  split; [rewrite Q7; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite E34u; unfold w64; f_equal; lia|].
  split; [rewrite Q10; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite E38; reflexivity|].
  split; [rewrite Q11; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite E39; reflexivity|].
  split; [rewrite Q12; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite E40; reflexivity|].
  split; [rewrite Q13; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite E33u; unfold w64; f_equal; lia|].
  split; [rewrite Q14; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite E34u; unfold w64; f_equal; lia|].
  split; [rewrite Q15; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite E32; reflexivity|].
  split; [rewrite Q16; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite E41; reflexivity|].
  split; [rewrite Q17; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite E35u; unfold w64; f_equal; lia|].
  rewrite Q28. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite E36u. unfold w64. f_equal; lia.
Qed.
Lemma fo_loop_all : forall dd i, (i + dd = length FO)%nat -> forall r m d, fo_LP i r m d ->
  SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + FO_LOOP)) m (seg_rom SEGS)) d) fo_Q.
Proof.
induction dd as [|dd IH]; intros i Hd r m d HLP.
- exfalso. destruct HLP as (_ & Hi & _). lia.
- apply (fo_loop_step i); [|exact HLP].
  intros Hsi r' m' d' HLP'. apply (IH (Datatypes.S i)); [lia | exact HLP'].
Qed.

(* ---------- FO_K (0x87cb4): a1 = k, the k = 0 arm and the loop ---------- *)
Lemma fo_k0_seed : forall regs1 mem1 md1,
  fo_cut 0 regs1 mem1 md1 -> getr regs1 11 = w64 0 -> getr regs1 15 = w64 SB ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [w64 SB])) fo_ss_k0
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + FO_K)) mem1 (seg_rom SEGS))).
Proof.
intros regs1 mem1 md1 HCUT R11 R15.
pose proof HCUT as (HMC & R2 & RCS).
pose proof fo_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : FO_STK = 16) by reflexivity.
set (E := Eimg (Ereg regs1 [w64 SB])).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = w64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 [w64 SB] 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 16)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
rewrite restrict_mkst_fx. unfold fo_ss_k0. apply pa_entry_st_ok_full.
- fo_regs_ok EE ltac:(rewrite ?E32u).
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, fo_spF, fo_SBF. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32u. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; try lia; rewrite Zminus_mod, Hal16; reflexivity.
Qed.
Lemma fo_k1_seed : forall regs1 mem1 md1,
  fo_cut 0 regs1 mem1 md1 -> 0 < KK -> s <> 0 ->
  getr regs1 10 = w64 s -> getr regs1 11 = w64 KK -> getr regs1 15 = w64 SB ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [w64 SB])) fo_ss_k1
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + FO_K)) mem1 (seg_rom SEGS))).
Proof.
intros regs1 mem1 md1 HCUT HKp Hs0 R10 R11 R15.
pose proof HCUT as (HMC & R2 & RCS).
pose proof fo_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof fo_KK as (_ & HK0 & HKn & _).
pose proof (fo_s_loc HKp) as (Hs4 & Hsc & Hsb).
assert (HST : FO_STK = 16) by reflexivity.
set (E := Eimg (Ereg regs1 [w64 SB])).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = w64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 [w64 SB] 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 16)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E10u : bv_unsigned (ew E 10) = s)
  by (rewrite (EE 10%nat 10%bv eq_refl), R10; unfold w64; apply unsigned_lit_small; lia).
assert (E11u : bv_unsigned (ew E 11) = KK)
  by (rewrite (EE 11%nat 11%bv eq_refl), R11; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold fo_ss_k1. apply pa_entry_st_ok_full.
- fo_regs_ok EE ltac:(rewrite ?E32u).
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, fo_spF, fo_SBF, fo_NZF, fo_CNTF.
  cbn [af_lo af_hi af_al2]. rewrite Usp, E32u, E10u, E11u. change (2 ^ 4) with 16.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; try lia; rewrite Zminus_mod, Hal16; reflexivity.
Qed.
Lemma fo_k : forall regs1 mem1 md1,
  fo_cut 0 regs1 mem1 md1 ->
  getr regs1 10 = w64 s -> getr regs1 11 = w64 KK -> getr regs1 12 = w64 out -> getr regs1 15 = w64 SB ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + FO_K)) mem1 (seg_rom SEGS)) md1) fo_Q.
Proof.
intros regs1 mem1 md1 HCUT R10 R11 R12 R15.
pose proof HCUT as (HMC & R2 & RCS). pose proof HMC as (HJ & HK & HFR & HM).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof fo_sp as (Hal16 & Hslo & Hshi). pose proof fo_out_loc as (Ho4 & Hoc & Hob).
pose proof fo_KK as (_ & HK0 & HKn & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : FO_STK = 16) by reflexivity.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 [w64 SB]))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 [w64 SB])) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew (Eimg (Ereg regs1 [w64 SB])) 32 = w64 SB)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 [w64 SB] 0)).
assert (SHOK : sh_ok SEGS fo_Bx [] (Eimg (Ereg regs1 [w64 SB])) (mrestrict (w_H W) mem1)) by apply Forall_nil.
destruct (Nat.eq_dec (length FO) 0) as [HZ|HNZ].
- (* k = 0: 0x87d64 `not a6,a2`, 0x87d68 (not taken), the tail with a0 = out *)
  assert (HKz : KK = 0) by (rewrite HZ; reflexivity).
  assert (R11z : getr regs1 11 = w64 0) by (rewrite R11, HKz; reflexivity).
  pose proof (fo_k0_seed regs1 mem1 md1 HCUT R11z R15) as HS.
  remember (Eimg (Ereg regs1 [w64 SB])) as E eqn:HE0. clear HE0.
  assert (Usp : bv_unsigned (ew E 2) = spZ regs - 16)
    by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
  assert (E12u : bv_unsigned (ew E 12) = out)
    by (rewrite (EE 12%nat 12%bv eq_refl), R12; unfold w64; apply unsigned_lit_small; lia).
  paj_run_tok RUN HS HJ SHOK Bspan.
  { apply YCbq.awr_ok_nil. }
  fo_md.
  fo_keep HFr KEEP1 (spZ regs - FO_STK) (spZ regs - FO_STK) Usp. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* ~out <u 0: impossible *)
    fo_br. exfalso. rewrite branch_ltu_U, U_SLit in HBR. change (zcanon 0) with 0 in HBR.
    apply Z.ltb_lt in HBR.
    lazymatch type of HBR with U ?Ex ?v < 0 => pose proof (U_range Ex v) as HU end. lia.
  + fo_br. clear HBR.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan FO_TAIL.
    { apply YCbq.awr_ok_nil. }
    fo_md.
    fo_keep HFr KEEP2 (spZ regs - FO_STK) (spZ regs - FO_STK) Usp. clear HF HFr HG.
    pmkst HS.
    fo_rreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (15%bv : bv 5) Q15.
    apply fo_tail.
    * rewrite HZ.
      eapply (fo_cut_keep 0%nat regs1 mem1 md1 _ _ _ (spZ regs - FO_STK) (spZ regs - FO_STK) ltac:(lia) HCUT HJ
        (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2 ltac:(lia) ltac:(lia))).
      -- intros a Ha. lia.
      -- fo_same HS ltac:(cbn [extK ewset ew Nat.eqb Nat.add length]; apply EE; reflexivity).
      -- intros rr Hrr. unfold fo_csl in Hrr. cbn [In] in Hrr.
         repeat (destruct Hrr as [<- | Hrr];
           [ fo_same HS ltac:(cbn [extK ewset ew Nat.eqb Nat.add length]; apply EE; reflexivity) | ]).
         destruct Hrr.
    * rewrite Q10, denot_lit_U. unfold w64. f_equal. fo_U_norm. cbn [zalu_raw].
      cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite ?E12u, ?HKz, ?Z.add_0_r.
      rewrite ?(zcanon_small out) by lia. rewrite ?Z.add_0_r.
      first [ reflexivity | rewrite zcanon_id by (unfold M64; lia); lia | lia ].
    * rewrite Q11, HKz. reflexivity.
    * rewrite Q15. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite E32. reflexivity.
- (* k > 0: the loop prologue, then the loop at byte 0 *)
  assert (HKp : 0 < KK) by lia.
  assert (Hs0 : s <> 0) by (apply HS0; lia).
  pose proof (fo_k1_seed regs1 mem1 md1 HCUT HKp Hs0 R10 R11 R15) as HS.
  remember (Eimg (Ereg regs1 [w64 SB])) as E eqn:HE0. clear HE0.
  assert (Usp : bv_unsigned (ew E 2) = spZ regs - 16)
    by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan FO_LOOP.
  { apply YCbq.awr_ok_nil. }
  fo_md.
  fo_keep HFr KEEP1 (spZ regs - FO_STK) (spZ regs - FO_STK) Usp. clear HF HFr HG.
  pmkst HS.
  prreg HS (5%bv : bv 5) Q5. prreg HS (6%bv : bv 5) Q6. prreg HS (7%bv : bv 5) Q7.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15.
  fo_rreg HS (16%bv : bv 5) Q16. prreg HS (17%bv : bv 5) Q17. prreg HS (28%bv : bv 5) Q28.
  apply (fo_loop_all (length FO) 0%nat ltac:(lia)).
  split.
  { eapply (fo_cut_keep 0%nat regs1 mem1 md1 _ _ _ (spZ regs - FO_STK) (spZ regs - FO_STK) ltac:(lia) HCUT HJ KEEP1).
    - intros a Ha. lia.
    - fo_same HS ltac:(cbn [extK ewset ew Nat.eqb Nat.add length]; apply EE; reflexivity).
    - intros rr Hrr. unfold fo_csl in Hrr. cbn [In] in Hrr.
      repeat (destruct Hrr as [<- | Hrr];
        [ fo_same HS ltac:(cbn [extK ewset ew Nat.eqb Nat.add length]; apply EE; reflexivity) | ]).
      destruct Hrr. }
  split; [lia|].
  split; [rewrite Q5; reflexivity|].
  split; [rewrite Q6; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite (EE 10%nat 10%bv eq_refl), R10; unfold w64; f_equal; lia|].
  split; [rewrite Q7; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite (EE 12%nat 12%bv eq_refl), R12; unfold w64; f_equal; lia|].
  split; [rewrite Q10; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity|].
  split; [rewrite Q11; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite (EE 11%nat 11%bv eq_refl), R11; reflexivity|].
  split; [rewrite Q12; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite (EE 12%nat 12%bv eq_refl), R12; reflexivity|].
  split; [rewrite Q13; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite (EE 10%nat 10%bv eq_refl), R10; unfold w64; f_equal; lia|].
  split; [rewrite Q14; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite (EE 12%nat 12%bv eq_refl), R12; unfold w64; f_equal; lia|].
  split; [rewrite Q15; cbn [extK ewset ew Nat.eqb Nat.add length]; rewrite E32; reflexivity|].
  split.
  { rewrite Q16, denot_lit_U. unfold w64. f_equal.
    cbn [extK ewset ew Nat.eqb Nat.add length].
    apply (fo_U_not _ 12 out); [rewrite (EE 12%nat 12%bv eq_refl), R12; reflexivity | lia]. }
  split; [rewrite Q17; reflexivity|].
  rewrite Q28. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite (EE 11%nat 11%bv eq_refl), R11.
  unfold w64. f_equal; lia.
Qed.

(* ---------- the entry: 0x87c94 .. 0x87cb0 and the two arms of `bltu a1,a3` ---------- *)
Lemma fo_entry_seed :
  st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 SB])) fo_ss_entry
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_fold)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS fo_Bx [] (Eimg (Ereg regs [w64 SB])) (mrestrict (w_H W) mem).
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof fo_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : FO_STK = 16) by reflexivity.
set (E := Eimg (Ereg regs [w64 SB])).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
assert (U241 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite E241; apply unsigned_lit_small; lia).
assert (U253 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (rewrite E253; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pal_got_cell B TL) as HgcD.
unfold kImgEnd in HcellR, HgotR.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold fo_ss_entry. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite U241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite U253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
      | unfold SB; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U241, U253.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, fo_spF, fo_SBF. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). change (2 ^ 4) with 16.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; try lia; exact Hal16.
Qed.
Lemma fo_entry : SRr SEGS W (cfg_at SEGS (BASE + AF_fold) regs mem md) fo_Q.
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof fo_sp as (Hal16 & Hslo & Hshi). pose proof fo_out_loc as (Ho4 & Hoc & Hob).
pose proof fo_KK as (HKmin & HK0 & HKn & HKc).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : FO_STK = 16) by reflexivity.
destruct fo_entry_seed as [HS SHOK].
pose proof (ajournal_init SEGS B FO_STK FP ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs [w64 SB]))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs [w64 SB])) k = getr regs r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew (Eimg (Ereg regs [w64 SB])) 32 = w64 SB)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
remember (Eimg (Ereg regs [w64 SB])) as E eqn:HE0. clear HE0.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E11 : ew E 11 = w64 n) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E13 : ew E 13 = w64 cap) by (rewrite (EE 13%nat 13%bv eq_refl); exact H13).
assert (E13u : bv_unsigned (ew E 13) = cap) by (rewrite E13; unfold w64; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + AF_fold)) with (Z_to_bv 64 (BASE + AF_fold)).
(* 0x87c94 .. 0x87ca8: the frame, the GOT word, the shadow base, a3 := cap - 1, `bltu a1,a3` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
fo_md.
fo_keep HFr KEEP0 (spZ regs - FO_STK) (spZ regs) Usp. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* n <u cap - 1: k = n *)
  fo_br.
  assert (HKe : KK = n).
  { rewrite branch_ltu_U, (U_atom E 11 n E11 ltac:(lia)), (U_atom_off E 13 cap (-1) E13 ltac:(lia) ltac:(lia)) in HBR.
    apply Z.ltb_lt in HBR. lia. }
  clear HBR.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan FO_K.
  { awr_ok_tac; cbn [extK ewset ew Nat.eqb Nat.add length]; exact Usp. }
  fo_md.
  fo_keep HFr KEEP1 (spZ regs - FO_STK) (spZ regs) Usp. clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (12%bv : bv 5) Q12. prreg HS (15%bv : bv 5) Q15.
  (* the saved return address *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    let rr := eval vm_compute in (nth_error (ss_mem ssx) 0%nat) in
  lazymatch rr with Some ?r0 =>
    pose proof (fo_region_of Ex ssx (restrict (w_H W) msx) 0%nat r0 HS ltac:(vm_compute; reflexivity)) as HRg end;
    cbn [ms_mem restrict] in HRg;
    assert (Uspx : bv_unsigned (ew Ex 2) = spZ regs) by (cbn [extK ewset ew Nat.eqb Nat.add length]; exact Usp) end.
  pose proof (bv_unsigned_in_range 64 (getr regs 1)) as HRr.
  change (bv_modulus 64) with (2 ^ 64) in HRr.
  lazymatch type of HRg with region_ok _ ?Ex _ _ =>
    pose proof (field_of_region Ex _ 2%nat (spZ regs) _ (-16) 0 (-16) 0 (-8) 8 (SOff 1 0)
      (bv_unsigned (getr regs 1)) HRg Uspx ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; cbn [extK ewset ew Nat.eqb Nat.add length];
            rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact HRr) ltac:(cbn; lia)) as HFv end.
  replace (spZ regs + -8) with (spZ regs - 8) in HFv by lia.
  apply fo_k.
  + split; [|split].
    * split; [exact HJ|]. split.
      { intros a Ha Hs1 Hs2.
        exact (kept_out_trans _ _ _ _ _ _ _ KEEP0 KEEP1 ltac:(lia) ltac:(lia) a Ha Hs1). }
      split; [apply (fo_sa_val8_of_val_mem SEGS); [exact HFv | exact HRr]|].
      intros j Hj. lia.
    * rewrite Q2. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite Usp. unfold w64. f_equal; lia.
    * intros rr Hrr. unfold fo_csl in Hrr. cbn [In] in Hrr.
      repeat (destruct Hrr as [<- | Hrr];
        [ fo_same HS ltac:(cbn [extK ewset ew Nat.eqb Nat.add length]; apply EE; reflexivity) | ]).
      destruct Hrr.
  + rewrite Q10. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite (EE 10%nat 10%bv eq_refl), H10. reflexivity.
  + rewrite Q11. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite E11, HKe. reflexivity.
  + rewrite Q12. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite (EE 12%nat 12%bv eq_refl), H12. reflexivity.
  + rewrite Q15. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite E32. reflexivity.
- (* n >=u cap - 1: k = cap - 1 *)
  fo_br.
  assert (HKe : KK = cap - 1).
  { rewrite branch_ltu_U, (U_atom E 11 n E11 ltac:(lia)), (U_atom_off E 13 cap (-1) E13 ltac:(lia) ltac:(lia)) in HBR.
    apply Z.ltb_ge in HBR. lia. }
  clear HBR.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan FO_K.
  { awr_ok_tac; cbn [extK ewset ew Nat.eqb Nat.add length]; exact Usp. }
  fo_md.
  fo_keep HFr KEEP1 (spZ regs - FO_STK) (spZ regs) Usp. clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (12%bv : bv 5) Q12. prreg HS (15%bv : bv 5) Q15.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    let rr := eval vm_compute in (nth_error (ss_mem ssx) 0%nat) in
  lazymatch rr with Some ?r0 =>
    pose proof (fo_region_of Ex ssx (restrict (w_H W) msx) 0%nat r0 HS ltac:(vm_compute; reflexivity)) as HRg end;
    cbn [ms_mem restrict] in HRg;
    assert (Uspx : bv_unsigned (ew Ex 2) = spZ regs) by (cbn [extK ewset ew Nat.eqb Nat.add length]; exact Usp) end.
  pose proof (bv_unsigned_in_range 64 (getr regs 1)) as HRr.
  change (bv_modulus 64) with (2 ^ 64) in HRr.
  lazymatch type of HRg with region_ok _ ?Ex _ _ =>
    pose proof (field_of_region Ex _ 2%nat (spZ regs) _ (-16) 0 (-16) 0 (-8) 8 (SOff 1 0)
      (bv_unsigned (getr regs 1)) HRg Uspx ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; cbn [extK ewset ew Nat.eqb Nat.add length];
            rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact HRr) ltac:(cbn; lia)) as HFv end.
  replace (spZ regs + -8) with (spZ regs - 8) in HFv by lia.
  apply fo_k.
  + split; [|split].
    * split; [exact HJ|]. split.
      { intros a Ha Hs1 Hs2.
        exact (kept_out_trans _ _ _ _ _ _ _ KEEP0 KEEP1 ltac:(lia) ltac:(lia) a Ha Hs1). }
      split; [apply (fo_sa_val8_of_val_mem SEGS); [exact HFv | exact HRr]|].
      intros j Hj. lia.
    * rewrite Q2. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite Usp. unfold w64. f_equal; lia.
    * intros rr Hrr. unfold fo_csl in Hrr. cbn [In] in Hrr.
      repeat (destruct Hrr as [<- | Hrr];
        [ fo_same HS ltac:(cbn [extK ewset ew Nat.eqb Nat.add length]; apply EE; reflexivity) | ]).
      destruct Hrr.
  + rewrite Q10. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite (EE 10%nat 10%bv eq_refl), H10. reflexivity.
  + rewrite Q11. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite E13u, HKe. unfold w64. f_equal; lia.
  + rewrite Q12. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite (EE 12%nat 12%bv eq_refl), H12. reflexivity.
  + rewrite Q15. cbn [extK ewset ew Nat.eqb Nat.add length]. rewrite E32. reflexivity.
Qed.

End w.

(* ---------- the contract ---------- *)
Theorem fold_walkB : fold_contract SEGS B (BASE + AF_fold) SegInstB.STK_fold.
Proof.
unfold fold_contract.
intros ly S W regs mem md ch s n out cap l HPRE H10 Hs64 H11 Hn64 H12 Ho64 H13 Hc64 HIP HEV.
destruct HIP as ((HC1 & HLN & HS0 & HSB & HSA & HRA & HDJ) & HSL & HFF).
first [ eapply (fo_entry ly S W regs mem md ch s n out cap l); eassumption
      | eapply fo_entry; eassumption ].
Qed.
End e.
End d.
End b.

About fold_walkB.
Print Assumptions fold_walkB.
