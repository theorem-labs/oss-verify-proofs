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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_calls_equal.v, with its module paths, module names and numbers changed; 910 of its 1180 lines of code are new or changed and 1322 lines of the source are left out. *)
(* The program walk of check_declared on reac-pw/fuzz_segconf image A (fuzz_segconf.asan, BASE + AF_check_declared =
   0x87658, 94 instructions), against check_declared_contract (lib/A/Prog/check_declared_c.v); the strcmp wrapper's
   contract (RtString.astrcmp_realizes) is a Section hypothesis. Control flow: the plain / UBSan owner's plain walk
   lib/Prog/check_declared.v. Form: plugin-hostd/fuzz_command's lib/A/Prog/rec_calls_equal.v (origin/ossv/recipes
   501c0d516c69): the symbolic executor over the position-abstract listing (SegPaLib.v), the inline checks removed
   by the shadow tokens (PaShadow.v), the wrapper call stepped through by its contract (PaArt.v aj_art_at), the loop
   cut at its head and re-seeded from the concrete state there, the loop proved by induction. Step plan:
   provenance/evidence/listing-plans/plan-check_declared.md.

   Cut points (listing offsets from BASE): 0x2924 the entry; 0x2980 (0x876b4) the head of the entry loop;
   0x29fc (0x87730) the guard set-up; 0x2a1c (0x87750) the guard loop at its first byte; 0x2a60 (0x87794) the
   epilogue. The guard loop runs straight through from its seed: the seed holds the 18 bytes of tab[cap] as the
   literal 0x5a, so each of its branches is decided by the executor.

   The arms to the no-return hook and abort (0x877c0 / 0x877c4) are untaken: 0x87680 (got = want), 0x87688
   (n = mn), 0x876dc (the vids agree), 0x876ec (the parents are equal strings, so the wrapper returns 0), 0x87790
   (the guard bytes are 0x5a). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YG0q YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase PaArt check_declared_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module SM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.SegModel.
Module SP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.seg_spec.

(* ---------- the model: strcmp on NUL-free strings (the plain walk's lemmas, lib/Prog/check_declared.v) ---------- *)
Lemma cd_zs_inj : forall l l' : list byte, SP.zs l = SP.zs l' -> l = l'.
Proof.
unfold SP.zs. induction l as [|x l IH]; intros [|y l'] H; cbn [map] in H; try discriminate; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Lemma cd_zs_nonul : forall l : list byte, ~ In (Z_to_bv 8 0) l -> ~ In 0 (SP.zs l).
Proof.
intros l H Hin. unfold SP.zs in Hin. apply in_map_iff in Hin as (b & Hb & Hin). apply H.
replace (Z_to_bv 8 0) with b; [exact Hin|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.
Lemma cd_strcmp_eq : forall s t, ~ In 0 s -> ~ In 0 t -> SM.strcmp s t = 0 -> s = t.
Proof.
induction s as [|a s IH]; intros [|b t] Hs Ht H; cbn [SM.strcmp] in H.
- reflexivity.
- exfalso. apply Ht. left. lia.
- exfalso. apply Hs. left. lia.
- revert H. destruct (Z.eqb_spec a b) as [E|E]; destruct (Z.eqb_spec a 0) as [E0|E0]; cbn [andb negb]; intros H.
  + exfalso. apply Hs. left. lia.
  + subst b. f_equal. apply IH; [intros X; apply Hs; right; exact X | intros X; apply Ht; right; exact X | exact H].
  + exfalso. lia.
  + exfalso. lia.
Qed.
(* SegModel.strcmp of two NUL-free byte strings is 0 only when they are equal *)
Lemma cd_bridge_strcmp : forall sx sy : list byte, ~ In (Z_to_bv 8 0) sx -> ~ In (Z_to_bv 8 0) sy ->
  SM.strcmp (SP.zs sx) (SP.zs sy) = 0 -> sx = sy.
Proof.
intros sx sy Hx Hy H. apply cd_zs_inj. apply cd_strcmp_eq; [apply cd_zs_nonul; exact Hx | apply cd_zs_nonul; exact Hy | exact H].
Qed.
(* a C string field: its first [length s + 1] bytes are the string's bytes and the NUL *)
Lemma cd_cstr_split : forall cap s f, SP.cstr_enc cap s f ->
  exists sx, firstn (S (length s)) f = sx ++ [Z_to_bv 8 0] /\ SP.zs sx = s /\ ~ In (Z_to_bv 8 0) sx.
Proof.
intros cap s f (Hl & Hs & Hn & Hz).
assert (Zp : SP.zs (firstn (S (length s)) f) = s ++ [0]) by (unfold SP.zs in *; rewrite <- firstn_map; exact Hz).
assert (NE : firstn (S (length s)) f <> []).
{ intros E. rewrite E in Zp. cbn in Zp. destruct s; discriminate. }
destruct (exists_last NE) as (sx & b & E).
rewrite E in Zp. unfold SP.zs in Zp. rewrite map_app in Zp. cbn [map] in Zp.
apply app_inj_tail in Zp as [Z1 Z2].
exists sx. split; [rewrite E; repeat f_equal; apply bv_eq; rewrite Z2; reflexivity|].
split; [exact Z1|].
intros Hin. apply Hn. rewrite <- Z1. unfold SP.zs. apply in_map_iff. exists (Z_to_bv 8 0). split; [reflexivity|exact Hin].
Qed.
Lemma cd_forallb2_nth : forall {A B} (P : A -> B -> bool) l1 l2 da db i, SM.forallb2 P l1 l2 = true ->
  (i < length l1)%nat -> P (nth i l1 da) (nth i l2 db) = true.
Proof.
intros A B P. induction l1 as [|x l1 IH]; intros [|y l2] da db i H Hi; cbn [SM.forallb2 length] in *;
  try discriminate; try lia.
apply andb_prop in H as [H1 H2]. destruct i as [|i]; cbn [nth]; [exact H1|]. apply IH; [exact H2 | lia].
Qed.
Lemma cd_vlans_are_spec : forall gv gt wv wt cap, SM.vlans_are (gv, gt) (wv, wt) cap = true ->
  gv = wv /\ length gt = length wt /\ Z.of_nat (length gt) <= cap /\
  forall i, (i < length gt)%nat -> snd (nth i gt ([], 0)) = snd (nth i wt ([], 0)) /\
                                  SM.strcmp (fst (nth i gt ([], 0))) (fst (nth i wt ([], 0))) = 0.
Proof.
intros gv gt wv wt cap H. unfold SM.vlans_are in H. cbn [fst snd] in H.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.leb_le in H4.
split; [exact H1|]. split; [exact H2|]. split; [exact H4|].
intros i Hi. pose proof (cd_forallb2_nth _ _ _ ([], 0) ([], 0) i H3 Hi) as P. cbn beta in P.
apply andb_prop in P as [P1 P2]. apply Z.eqb_eq in P1. apply Z.eqb_eq in P2. split; assumption.
Qed.

(* ---------- byte views through a reader ---------- *)
Lemma cd_fld_fld : forall a n b k (l : list byte), (a + n <= k)%nat ->
  firstn n (skipn a (firstn k (skipn b l))) = firstn n (skipn (b + a) l).
Proof.
intros a n b k l H. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
replace (Nat.min n (k - a)) with n by lia. rewrite (Nat.add_comm a b). reflexivity.
Qed.
Lemma cd_nth_firstn : forall {A} (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
intros A. induction l as [|x l IH]; intros n i d H.
- rewrite firstn_nil. reflexivity.
- destruct n as [|n]; [lia|]. destruct i as [|i]; cbn [firstn nth]; [reflexivity|]. apply IH. lia.
Qed.
Lemma cd_nth_skipn : forall {A} (l : list A) j i d, nth i (skipn j l) d = nth (j + i) l d.
Proof.
intros A. induction l as [|a l IH]; intros [|j] i d; cbn; [destruct i; reflexivity | destruct i; reflexivity | reflexivity | apply IH].
Qed.
Lemma cd_bytes_sub : forall rd a (l : list byte) k n, sa_bytes rd a l -> (k + n <= length l)%nat ->
  sa_bytes rd (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
intros rd a l k n H Hk i Hi. rewrite length_firstn, length_skipn in Hi.
replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
rewrite cd_nth_firstn by lia. rewrite cd_nth_skipn. apply H. lia.
Qed.
Lemma cd_le_bytes_nth : forall n z k, (k < n)%nat ->
  bv_unsigned (nth k (Z_to_le_bytes n z) (Z_to_bv 8 0)) = Z.shiftr z (8 * Z.of_nat k) mod 256.
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- rewrite Z_to_bv_unsigned. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
(* the n little-endian bytes of v, read through a reader, give the field value v *)
Lemma cd_val_le : forall rd a (n : nat) v, 0 <= v < 2 ^ (8 * Z.of_nat n) -> (n <= 8)%nat ->
  sa_bytes rd a (Z_to_le_bytes n (bv_unsigned (Z_to_bv 64 v))) -> sa_val rd a n v.
Proof.
intros rd a n v Hv Hn H k Hk. rewrite (H k) by (rewrite Mem.length_Z_to_le_bytes; exact Hk).
f_equal. unfold ZB0. rewrite cd_le_bytes_nth by exact Hk.
assert (Hv64 : 0 <= v < 2 ^ 64).
{ split; [lia|]. apply (Z.lt_le_trans _ (2 ^ (8 * Z.of_nat n))); [lia|]. apply Z.pow_le_mono_r; lia. }
rewrite unsigned_lit_small by exact Hv64. unfold YG0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.
(* a field read through the world's view is the same field of the restricted memory *)
Lemma cd_val_mem_of_sa_val : forall segs H mem a n v,
  sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
(* reads that are the same outside a window [lo, hi) (PaArt.v's kept_out, restated here) *)
Definition cd_kept (rd rd' : reader) (lo hi : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rd' a = rd a.
Lemma cd_kept_trans : forall rd1 rd2 rd3 lo hi lo' hi',
  cd_kept rd1 rd2 lo hi -> cd_kept rd2 rd3 lo' hi' -> lo <= lo' -> hi' <= hi -> cd_kept rd1 rd3 lo hi.
Proof. intros rd1 rd2 rd3 lo hi lo' hi' H12 H23 Hl Hh a Ha Hn. rewrite (H23 a Ha) by lia. exact (H12 a Ha Hn). Qed.
Lemma cd_bytes_kept : forall rd rd' lo hi p l, cd_kept rd rd' lo hi -> sa_bytes rd p l ->
  0 <= p -> p + Z.of_nat (length l) <= lo -> lo < 2 ^ 64 -> sa_bytes rd' p l.
Proof. intros rd rd' lo hi p l HK H Hp Hl Hlo i Hi. rewrite (HK (p + Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma cd_val_kept : forall rd rd' lo hi x n v, cd_kept rd rd' lo hi -> sa_val rd x n v ->
  0 <= x -> (hi <= x \/ x + Z.of_nat n <= lo) -> x + Z.of_nat n < 2 ^ 64 -> sa_val rd' x n v.
Proof. intros rd rd' lo hi x n v HK H Hx Hw Hr k Hk. rewrite (HK (x + Z.of_nat k)) by lia. exact (H k Hk). Qed.

(* ---------- the tables, entry by entry ---------- *)
(* entry i of the reader's table: the vid's two bytes at tab + 18 i + 16, and the parent's string with its NUL at
   tab + 18 i *)
Lemma cd_rtab_entry : forall rd tab gt bt i, sa_bytes rd tab bt -> SP.rtab_enc gt bt -> (i < length gt)%nat ->
  sa_val rd (tab + 18 * Z.of_nat i + 16) 2 (snd (nth i gt ([], 0))) /\
  0 <= snd (nth i gt ([], 0)) < 65536 /\
  exists sx, sa_bytes rd (tab + 18 * Z.of_nat i) (sx ++ [Z_to_bv 8 0]) /\ SP.zs sx = fst (nth i gt ([], 0)) /\
             ~ In (Z_to_bv 8 0) sx /\ (length sx < 16)%nat.
Proof.
intros rd tab gt bt i HB [HL HE] Hi.
destruct (HE i Hi) as (L18 & HC & HV & H2).
split; [|split; [exact HV|]].
- assert (HB2 : sa_bytes rd (tab + Z.of_nat (18 * i + 16)) (firstn 2 (skipn (18 * i + 16) bt)))
    by (apply cd_bytes_sub; [exact HB | lia]).
  unfold SP.fld in H2. rewrite cd_fld_fld in H2 by lia. rewrite H2 in HB2.
  replace (tab + 18 * Z.of_nat i + 16) with (tab + Z.of_nat (18 * i + 16)) by lia.
  apply cd_val_le; [cbn; lia | lia | exact HB2].
- pose proof HC as (_ & Hlt & _).
  destruct (cd_cstr_split 16 _ _ HC) as (sx & E & Z1 & N1).
  exists sx. split; [|split; [exact Z1 | split; [exact N1|]]].
  + rewrite <- E. unfold SP.fld. rewrite cd_fld_fld by lia. rewrite firstn_firstn, Nat.add_0_r.
    replace (Nat.min (S (length (fst (nth i gt ([], 0))))) 16) with (S (length (fst (nth i gt ([], 0))))) by lia.
    replace (tab + 18 * Z.of_nat i) with (tab + Z.of_nat (18 * i)) by lia.
    apply cd_bytes_sub; [exact HB | lia].
  + rewrite <- Z1 in Hlt. unfold SP.zs in Hlt. rewrite length_map in Hlt. exact Hlt.
Qed.
(* entry i of the model's table: the vid's four bytes at mt + 20 i + 16, and the parent's string with its NUL at
   mt + 20 i *)
Lemma cd_mtab_entry : forall rd mt wt bm i, sa_bytes rd mt bm -> SP.mtab_enc wt bm -> (i < length wt)%nat ->
  sa_val rd (mt + 20 * Z.of_nat i + 16) 4 (snd (nth i wt ([], 0))) /\
  0 <= snd (nth i wt ([], 0)) < 2 ^ 32 /\
  exists sy, sa_bytes rd (mt + 20 * Z.of_nat i) (sy ++ [Z_to_bv 8 0]) /\ SP.zs sy = fst (nth i wt ([], 0)) /\
             ~ In (Z_to_bv 8 0) sy /\ (length sy < 16)%nat.
Proof.
intros rd mt wt bm i HB [HL HE] Hi.
destruct (HE i Hi) as (L20 & HC & HV & H4).
split; [|split; [exact HV|]].
- assert (HB4 : sa_bytes rd (mt + Z.of_nat (20 * i + 16)) (firstn 4 (skipn (20 * i + 16) bm)))
    by (apply cd_bytes_sub; [exact HB | lia]).
  unfold SP.fldz, SP.fld in H4. change (Z.to_nat 16) with 16%nat in H4. change (Z.to_nat 4) with 4%nat in H4.
  rewrite cd_fld_fld in H4 by lia. rewrite H4 in HB4.
  replace (mt + 20 * Z.of_nat i + 16) with (mt + Z.of_nat (20 * i + 16)) by lia.
  apply cd_val_le; [cbn; lia | lia | exact HB4].
- pose proof HC as (_ & Hlt & _).
  destruct (cd_cstr_split 16 _ _ HC) as (sy & E & Z1 & N1).
  exists sy. split; [|split; [exact Z1 | split; [exact N1|]]].
  + rewrite <- E. unfold SP.fld. rewrite cd_fld_fld by lia. rewrite firstn_firstn, Nat.add_0_r.
    replace (Nat.min (S (length (fst (nth i wt ([], 0))))) 16) with (S (length (fst (nth i wt ([], 0))))) by lia.
    replace (mt + 20 * Z.of_nat i) with (mt + Z.of_nat (20 * i)) by lia.
    apply cd_bytes_sub; [exact HB | lia].
  + rewrite <- Z1 in Hlt. unfold SP.zs in Hlt. rewrite length_map in Hlt. exact Hlt.
Qed.
(* byte j of the guard entry tab[cap] *)
Lemma cd_guard_byte : forall rd a j, sa_bytes rd a SP.GUARD_BYTES -> (j < 18)%nat ->
  sa_val rd (a + Z.of_nat j) 1 90.
Proof.
intros rd a j H Hj k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
rewrite (H j) by (unfold SP.GUARD_BYTES; rewrite repeat_length; exact Hj).
unfold SP.GUARD_BYTES. rewrite nth_repeat_lt by exact Hj. reflexivity.
Qed.

(* ---------- words ---------- *)
(* tab + mulhu(cap << 32, 9 << 33) = tab + 18 cap: the guard set-up's address computation (0x87730-0x87740) *)
Lemma cd_mulhu18 : forall c, 0 <= c < 40 -> Z.shiftr (c * 2 ^ 32 * (9 * 2 ^ 33)) 64 = 18 * c.
Proof.
intros c Hc. rewrite Z.shiftr_div_pow2 by lia.
replace (c * 2 ^ 32 * (9 * 2 ^ 33)) with ((18 * c) * 2 ^ 64)
  by (change (2 ^ 32) with 4294967296; change (2 ^ 33) with 8589934592; change (2 ^ 64) with 18446744073709551616; ring).
apply Z.div_mul. change (2 ^ 64) with 18446744073709551616. lia.
Qed.
Lemma cd_set_fs_self : forall S : astate, exists f, S = set_fs f S.
Proof. intros S. destruct S. eexists. unfold set_fs. cbn. reflexivity. Qed.
Lemma cd_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof using.
intros z Hz. unfold bv_swrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma cd_bge0 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = (v <=? 0).
Proof using.
intros E n v Hn Hv. cbn [branch_taken sv_denot]. rewrite Hn, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia.
unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia. rewrite !cd_swrap_small by lia.
destruct (Z.ltb_spec 0 v); destruct (Z.leb_spec v 0); try reflexivity; lia.
Qed.

(* ---------- the symbolic states of the cut points ---------- *)
Definition CD_LOOP : Z := 0x2980.   (* 0x876b4, the head of the entry loop *)
Definition CD_GSET : Z := 0x29fc.   (* 0x87730, the guard set-up *)
Definition CD_GUARD : Z := 0x2a1c.  (* 0x87750, the guard loop *)
Definition CD_EPI : Z := 0x2a60.    (* 0x87794, the epilogue *)
Definition CD_RET : Z := 0x29b8.    (* 0x876ec, the strcmp call's return *)
(* the frame: ra and s0..s7 saved at sp0-8 .. sp0-72 *)
Definition cd_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23].
Definition cd_PTRF : afact := mkAF 4096 (2 ^ 47 - 64) 0.
Definition cd_spF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition cd_SBF : afact := mkAF SB SB 0.
Definition cd_CAPF : afact := mkAF 0 39 0.
Definition cd_CNTF : afact := mkAF 1 40 0.
Definition cd_VIDF : afact := mkAF 0 65535 0.
Definition cd_Bx : sv := SOff 32 0.
(* the entry: atom 32 the shadow base *)
Definition cd_ss_entry : sstate := mkSS AF_check_declared sr_atoms [stack_region 80; got_regionP; bcell_regionP 32] None
  (mkFacts [(2%nat, cd_spF); (32%nat, cd_SBF)] [] []).
(* the epilogue: atoms 32..40 the saved ra, s0..s7 *)
Definition cd_estack : YP09.region := YP09.mkRegion (Some 2%nat) 0 80 0 0
  (map (fun j => YP09.mkChunk (72 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 9)).
Definition cd_ss_epi : sstate := mkSS CD_EPI sr_atoms [cd_estack] None (mkFacts [(2%nat, cd_spF)] [] []).
(* the guard loop: atoms 32 the shadow base, 33 tab + 18 cap *)
Definition cd_g_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 9 (SOff 33 0)) 10 (SOff 33 0)) 11 (SLit 90)) 12 (SLit 17)) 23 (SOff 32 0).
Definition cd_guard_r : YP09.region := YP09.mkRegion (Some 33%nat) 0 18 0 0
  (map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SLit 90))) (seq 0 18)).
Definition cd_g_facts : facts := mkFacts [(2%nat, cd_spF); (32%nat, cd_SBF); (33%nat, cd_PTRF)] [] [].
Definition cd_g_SH : list shent := [mkSHE 33 0 18].
Definition cd_ss_guard : sstate := mkSS CD_GUARD cd_g_regs [cd_guard_r] None cd_g_facts.
(* the guard set-up: atoms 32 the shadow base, 33 tab, 34 cap *)
Definition cd_s_regs : list sv := sr_set (sr_set (sr_set sr_atoms 8 (SOff 34 0)) 9 (SOff 33 0)) 23 (SOff 32 0).
Definition cd_ss_gset : sstate := mkSS CD_GSET cd_s_regs [] None
  (mkFacts [(2%nat, cd_spF); (32%nat, cd_SBF); (33%nat, cd_PTRF); (34%nat, cd_CAPF)] [] []).
(* the loop head: atoms 32 the shadow base, 33 tab, 34 cap, 35 tab + 18 i, 36 mt + 20 i, 37 n - i, 38 the vid of
   entry i (the same value in both tables) *)
Definition cd_l_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
   8 (SOff 34 0)) 9 (SOff 33 0)) 18 (SOff 36 0)) 19 (SOff 37 0)) 20 (SOff 36 16)) 21 (SOff 35 16)) 22 (SOff 35 0))
   23 (SOff 32 0).
Definition cd_entT : YP09.region := YP09.mkRegion (Some 35%nat) 0 18 0 0 [YP09.mkChunk 16 (CVal 2 (SOff 38 0))].
Definition cd_entM : YP09.region := YP09.mkRegion (Some 36%nat) 0 20 0 0 [YP09.mkChunk 16 (CVal 4 (SOff 38 0))].
Definition cd_l_facts : facts := mkFacts
  [(2%nat, cd_spF); (32%nat, cd_SBF); (33%nat, cd_PTRF); (34%nat, cd_CAPF); (35%nat, cd_PTRF); (36%nat, cd_PTRF);
   (37%nat, cd_CNTF); (38%nat, cd_VIDF)] [] [].
(* entry i and entry i + 1 of each table (i + 1 <= cap, inside the block): the shadow byte of the vid's granule is 0 *)
Definition cd_l_SH : list shent := [mkSHE 35 0 36; mkSHE 36 0 40].
Definition cd_ss_loop : sstate := mkSS CD_LOOP cd_l_regs [cd_entT] None cd_l_facts.
(* swap the one table region of a state *)
Definition cd_swap (r : YP09.region) (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) [r] (ss_resv ss) (ss_facts ss).

Ltac cd_regs_ok EE eqs :=
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
Ltac cd_md :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md2 _ |- _ =>
    lazymatch md2 with with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := md2) in *; clearbody m | _ => idtac end end.

(* the value s1 and a0 hold at 0x87750: the executor's expression of tab + mulhu(cap << 32, 9 << 33) *)
Lemma cd_gset_U : forall E t c, U E (SOff 33 0) = t -> U E (SOff 34 0) = c -> 0 <= c < 40 -> 0 <= t -> t + 18 * c < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff 33 0) (SMd M_MULHU (SAlu ALU_SLL (SOff 34 0) (SLit 32)) (SLit 77309411328))) = t + 18 * c.
Proof using.
intros E t c Ht Hc Hc40 Ht0 Hlt.
repeat first [ rewrite U_SAlu | rewrite U_SMd | rewrite U_SLit ]. rewrite Ht, Hc. cbn [zalu_raw zmd_raw].
change (zcanon 32) with 32. change (zcanon 77309411328) with 77309411328. change (Z.land 32 63) with 32.
change (Z.of_N 64) with 64.
rewrite Z.shiftl_mul_pow2 by lia. rewrite (zcanon_small (c * 2 ^ 32)) by lia.
replace 77309411328 with (9 * 2 ^ 33) by reflexivity.
rewrite cd_mulhu18 by lia. rewrite (zcanon_small (18 * c)) by lia. apply zcanon_small. lia.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack a call needs: its own 80-byte frame and the strcmp wrapper's window (RtString.astrcmp_realizes,
   ecall_pre_stk segs B (2 * ESTACK)) *)
#[local] Notation CD_STK := SegInstA.STK_check_declared (only parsing).
Lemma cd_swap_ok : forall E ss ms r,
  st_ok_pi SEGS VAL E ss ms -> region_wf r = true -> region_ok SEGS E (ms_mem ms) r ->
  st_ok_pi SEGS VAL E (cd_swap r ss) ms.
Proof using.
intros E ss ms r HS Hwf Hr.
pose proof (st_ok_pi_submem E ss ms [] HS (submem_nil _) eq_refl) as HS0.
pose proof (st_ok_pi_add_region E _ ms r HS0 Hwf Hr I) as HS1. exact HS1.
Qed.

Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
(* the runtime entry the call reaches: the strcmp wrapper at its trampoline (the interceptor layer's interface, row 17) *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

Ltac cd_keep_empty HFr K lo hi :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : cd_kept (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
      | exact Hx0 | tauto ]) end.
Ltac cd_keep_win HFr K lo hi Usp :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : cd_kept (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => lo <= x < hi) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]); destruct Hin
      | exact Hx0 | exact Hn0 ]) end.

(* the shadow of a range the walk's checks read *)
Lemma cd_shent_ok : forall E m n x lo hi, ew E 32 = w64 SB -> bv_unsigned (ew E n) = x -> 0 <= x + lo -> x + hi < 2 ^ 64 -> lo <= hi ->
  range_addressable (rd_of SEGS m) SHADOW_OFF (x + lo) (hi - lo) ->
  (forall y, x + lo <= y < x + hi -> ~ (SB <= y < SB + 2 ^ 44)) ->
  shent_ok SEGS cd_Bx E m (mkSHE n lo hi).
Proof using.
intros E m n x lo hi H32 Hn H0 H1 Hlh Hra Hband. unfold shent_ok, app_apart, cd_Bx. cbn [she_m she_lo she_hi].
assert (U32 : U E (SOff 32 0) = SB).
{ rewrite U_SOff, H32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). apply zcanon_small. unfold SB; lia. }
assert (Hxr : 0 <= x < 2 ^ 64) by (rewrite <- Hn; pose proof (bv_unsigned_in_range 64 (ew E n)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR).
assert (Un : U E (SOff n 0) = x) by (rewrite U_SOff, Hn, Z.add_0_r; apply zcanon_small; exact Hxr).
rewrite U32, Un. split; [exact Hra|].
intros y Hy. rewrite Z.min_l, Z.max_r in Hy by lia. apply Hband. lia.
Qed.
(* the extra words of a seed *)
Lemma cd_ex_w64 : forall regs1 (l : list Z) j, (32 + j < A_TEXT)%nat -> (j < length l)%nat ->
  ew (Eimg (Ereg regs1 (map w64 l))) (32 + j) = w64 (nth j l 0).
Proof using.
intros regs1 l j H1 H2. rewrite Eimg_low by exact H1. rewrite ew_Ereg_extra.
rewrite (nth_indep _ _ (w64 0)) by (rewrite length_map; exact H2). apply map_nth.
Qed.
(* a heap range is outside the shadow band *)
Lemma cd_block_band : forall ly S W mem md p k x, AR SEGS B ly S W mem md -> In (p, k) (ablocks B ly S) ->
  p <= x < p + req_size k -> ~ (SB <= x < SB + 2 ^ 44).
Proof using LAWS.
intros ly S W mem md p k x HAR Hin Hx.
destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hin) as (_ & _ & _ & Hpapp & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia.
Qed.

(* ---------- one call of check_declared ---------- *)
Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (tab mt cap pt kt pm km : Z) (gt wt : list (list Z * Z)) (bt bm : list byte) (rlo rhi : Z).
Hypothesis HPRE : afn_pre SEGS B CD_STK ly S W regs mem md ch.
Hypothesis H1011 : getr regs 10 = getr regs 11.
Hypothesis H12 : getr regs 12 = w64 tab.
Hypothesis H13 : getr regs 13 = w64 (Z.of_nat (length gt)).
Hypothesis H14 : getr regs 14 = w64 mt.
Hypothesis H15 : getr regs 15 = w64 (Z.of_nat (length gt)).
Hypothesis H16 : getr regs 16 = w64 cap.
Hypothesis HCAP : 0 <= cap < 40.
Hypothesis HTB : In (pt, kt) (ablocks B ly S).
Hypothesis HTB1 : pt <= tab.
Hypothesis HTB2 : tab + 18 * (cap + 1) <= pt + kt.
Hypothesis HMB : In (pm, km) (ablocks B ly S).
Hypothesis HMB1 : pm <= mt.
Hypothesis HMB2 : mt + 20 * (cap + 1) <= pm + km.
Hypothesis HBT : sa_bytes (rdW W mem) tab bt.
Hypothesis HET : SP.rtab_enc gt bt.
Hypothesis HBM : sa_bytes (rdW W mem) mt bm.
Hypothesis HEM : SP.mtab_enc wt bm.
Hypothesis HGD : sa_bytes (rdW W mem) (tab + 18 * cap) SP.GUARD_BYTES.
Hypothesis HL : length gt = length wt.
Hypothesis HC : Z.of_nat (length gt) <= cap.
Hypothesis HE : forall i, (i < length gt)%nat -> snd (nth i gt ([], 0)) = snd (nth i wt ([], 0)) /\
  SM.strcmp (fst (nth i gt ([], 0))) (fst (nth i wt ([], 0))) = 0.
Hypothesis HROD : arodata_okP SEGS rlo rhi B (rdW W mem).

Definition cd_Q : world SEGS -> config -> Prop :=
apost_base SEGS B CD_STK [] regs ly S W mem md 0 (fun ly' S' W' regs' mem' md' =>
  sa_kept SEGS W mem W' mem' regs CD_STK (fun _ => False) /\ sa_noalloc B ly S ly' S').
(* the saved registers in the frame *)
Definition cd_frame (rd : reader) : Prop :=
forall j r, nth_error cd_saved j = Some r ->
sa_val rd (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* a cut point: the journal from the entry, the memory below the stack window unchanged, the frame, sp, gp, tp and
   the callee-saved registers the function never writes (s8..s11) *)
Definition cd_cut (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal SEGS B CD_STK (spZ regs) [] ly S W mem md [] ly S W mem1 md1 0 /\
cd_kept (rdW W mem) (rdW W mem1) (spZ regs - CD_STK) (spZ regs) /\
cd_frame (rdW W mem1) /\
getr regs1 2 = w64 (spZ regs - 80) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 24 = getr regs 24 /\ getr regs1 25 = getr regs 25 /\ getr regs1 26 = getr regs 26 /\
getr regs1 27 = getr regs 27.

Lemma cd_sp : spZ regs mod 16 = 0 /\ alloc_ceiling + CD_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof using HPRE HCAP HL HC.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2). lia.
Qed.

(* a cut carried to a later state whose memory differs only in a window below the frame *)
Lemma cd_cut_kept : forall regs1 mem1 md1 regs2 mem2 md2 lo hi,
  cd_cut regs1 mem1 md1 ->
  ajournal SEGS B CD_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 ->
  cd_kept (rdW W mem1) (rdW W mem2) lo hi -> spZ regs - CD_STK <= lo -> hi <= spZ regs - 80 ->
  getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
  getr regs2 24 = getr regs1 24 -> getr regs2 25 = getr regs1 25 -> getr regs2 26 = getr regs1 26 ->
  getr regs2 27 = getr regs1 27 ->
  cd_cut regs2 mem2 md2.
Proof using HPRE HCAP HL HC.
intros regs1 mem1 md1 regs2 mem2 md2 lo hi (HJ & HK & HFR & R2 & R3 & R4 & R24 & R25 & R26 & R27) HJ2 HK2 Hlo Hhi
  Q2 Q3 Q4 Q24 Q25 Q26 Q27.
pose proof cd_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : CD_STK = 8272) by reflexivity.
split; [exact HJ2|]. split.
{ intros x Hx Hn. destruct (Z_lt_le_dec x lo) as [Hl|Hl]; [rewrite (HK2 x Hx) by lia; exact (HK x Hx Hn)|].
  destruct (Z_lt_le_dec x hi) as [Hh|Hh]; [exfalso; apply Hn; lia|]. rewrite (HK2 x Hx) by lia. exact (HK x Hx Hn). }
split.
{ intros j r Hr. assert (Hj : (j < 9)%nat) by (change 9%nat with (length cd_saved); apply (proj1 (nth_error_Some cd_saved j)); rewrite Hr; discriminate).
  intros k Hk. rewrite (HK2 _) by lia. exact (HFR j r Hr k Hk). }
rewrite Q2, Q3, Q4, Q24, Q25, Q26, Q27. auto 10.
Qed.

(* ---------- the epilogue: 0x87794 .. 0x877bc, ra and s0..s7 restored, ret ---------- *)
Definition cd_e_extra : list word := map (fun r => getr regs (Z_to_bv 5 r)) cd_saved.
Lemma cd_e_nth : forall j r, nth_error cd_saved j = Some r -> nth j cd_e_extra (Z_to_bv 64 0) = getr regs (Z_to_bv 5 r).
Proof using.
intros j r H. unfold cd_e_extra. apply nth_error_nth. rewrite (map_nth_error (fun r0 => getr regs (Z_to_bv 5 r0)) j cd_saved H). reflexivity.
Qed.
Lemma cd_epi_seed : forall regs1 mem1, getr regs1 2 = w64 (spZ regs - 80) -> cd_frame (rdW W mem1) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 cd_e_extra)) cd_ss_epi
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + CD_EPI)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS cd_Bx [] (Eimg (Ereg regs1 cd_e_extra)) (mrestrict (w_H W) mem1).
Proof using HPRE HCAP HL HC.
intros regs1 mem1 R2 HFR. pose proof cd_sp as (Hal16 & Hlo & Hhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : CD_STK = 8272) by reflexivity.
set (E := Eimg (Ereg regs1 cd_e_extra)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 80).
{ subst E. rewrite (ew_Eimg_Ereg_nat regs1 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold cd_ss_epi. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, cd_estack.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
  destruct (nth_error cd_saved j) as [r|] eqn:Hr; [| apply nth_error_None in Hr; cbn in Hr; lia].
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
  apply (chunk_ok_val SEGS E _ (spZ regs - 80) (72 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  + cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra, (cd_e_nth j r Hr).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HRr.
  + cbn. lia.
  + replace (spZ regs - 80 + (72 - 8 * Z.of_nat j)) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
    apply cd_val_mem_of_sa_val. exact (HFR j r Hr).
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok, cd_spF. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. split; [lia|]. split; [|lia]. rewrite Zminus_mod, Hal16. reflexivity.
Qed.
Lemma cd_epi : forall regs1 mem1 md1, cd_cut regs1 mem1 md1 ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + CD_EPI)) mem1 (seg_rom SEGS)) md1) cd_Q.
Proof using HPRE HCAP HL HC TL.
intros regs1 mem1 md1 (HJ & HK & HFR & R2 & R3 & R4 & R24 & R25 & R26 & R27).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof cd_sp as (Hal16 & Hlo & Hhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : CD_STK = 8272) by reflexivity.
destruct (cd_epi_seed regs1 mem1 R2 HFR) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 cd_e_extra))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs1 cd_e_extra)) n = getr regs1 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j r, nth_error cd_saved j = Some r -> ew (Eimg (Ereg regs1 cd_e_extra)) (32 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hr. assert (Hj : (j < 9)%nat) by (change 9%nat with (length cd_saved); apply (proj1 (nth_error_Some cd_saved j)); rewrite Hr; discriminate).
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (cd_e_nth j r Hr). }
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs1 cd_e_extra)) 2) = spZ regs - 80).
{ rewrite (EE 2%nat 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
pose proof (EX 0%nat 1 eq_refl) as E32. pose proof (EX 1%nat 8 eq_refl) as E33. pose proof (EX 2%nat 9 eq_refl) as E34.
pose proof (EX 3%nat 18 eq_refl) as E35. pose proof (EX 4%nat 19 eq_refl) as E36. pose proof (EX 5%nat 20 eq_refl) as E37.
pose proof (EX 6%nat 21 eq_refl) as E38. pose proof (EX 7%nat 22 eq_refl) as E39. pose proof (EX 8%nat 23 eq_refl) as E40.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39, E40.
pose proof (EE 3%nat 3%bv eq_refl) as E3. pose proof (EE 4%nat 4%bv eq_refl) as E4.
pose proof (EE 24%nat 24%bv eq_refl) as E24. pose proof (EE 25%nat 25%bv eq_refl) as E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. pose proof (EE 27%nat 27%bv eq_refl) as E27.
clear EX.
remember (Eimg (Ereg regs1 cd_e_extra)) as E eqn:HE0. clear HE0.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
cd_md.
cd_keep_empty HFr KEEPE (spZ regs - CD_STK) (spZ regs - CD_STK). clear HF HFr HG.
prreg HS (1%bv : bv 5) F1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold cd_Q, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split.
{ rewrite F1, E32. change (getr regs (Z_to_bv 5 1)) with (getr regs 1). unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ. }
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| subst r];
  rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot];
  first
  [ rewrite Usp; replace (spZ regs - 80 + 80) with (spZ regs) by lia; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
  | rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    first [ rewrite E3, R3; reflexivity | rewrite E4, R4; reflexivity
          | rewrite E24, R24; reflexivity | rewrite E25, R25; reflexivity | rewrite E26, R26; reflexivity
          | rewrite E27, R27; reflexivity
          | rewrite E33; reflexivity | rewrite E34; reflexivity | rewrite E35; reflexivity | rewrite E36; reflexivity
          | rewrite E37; reflexivity | rewrite E38; reflexivity | rewrite E39; reflexivity | rewrite E40; reflexivity ] ]. }
split.
{ intros a Ha Hn _. rewrite (KEEPE a Ha) by lia. exact (HK a Ha Hn). }
unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|]. apply cd_set_fs_self.
Qed.

(* ---------- the entry's facts about the two tables ---------- *)
Lemma cd_tabs : 4096 <= tab /\ tab + 18 * (cap + 1) <= alloc_ceiling /\
  range_addressable (rdW W mem) SHADOW_OFF tab (18 * (cap + 1)) /\
  (forall x, tab <= x < tab + 18 * (cap + 1) -> ~ (SB <= x < SB + 2 ^ 44)) /\
  4096 <= mt /\ mt + 20 * (cap + 1) <= alloc_ceiling /\
  range_addressable (rdW W mem) SHADOW_OFF mt (20 * (cap + 1)) /\
  (forall x, mt <= x < mt + 20 * (cap + 1) -> ~ (SB <= x < SB + 2 ^ 44)).
Proof using HPRE HTB HTB1 HTB2 HMB HMB1 HMB2 HCAP HL HC LAWS.
pose proof HPRE as (HAR & _).
destruct (al_blocks _ _ LAWS ly S W mem md pt kt HAR HTB) as (_ & Ht4 & Htc & _ & _ & _ & Htk).
destruct (al_blocks _ _ LAWS ly S W mem md pm km HAR HMB) as (_ & Hm4 & Hmc & _ & _ & _ & Hmk).
pose proof (req_size_pos kt ltac:(lia)) as [_ Rt]. pose proof (req_size_pos km ltac:(lia)) as [_ Rm].
split; [lia|]. split; [lia|].
split; [apply (range_addressable_of_block SEGS B LAWS ly S W mem md pt kt tab _ HAR HTB); lia|].
split; [intros x Hx; apply (cd_block_band ly S W mem md pt kt x HAR HTB); lia|].
split; [lia|]. split; [lia|].
split; [apply (range_addressable_of_block SEGS B LAWS ly S W mem md pm km mt _ HAR HMB); lia|].
intros x Hx; apply (cd_block_band ly S W mem md pm km x HAR HMB); lia.
Qed.

(* ---------- the guard loop: 0x87750 .. 0x8778c for the 18 bytes of tab[cap], then 0x8778c .. 0x87790 ---------- *)
Lemma cd_guard_seed : forall regs1 mem1, getr regs1 2 = w64 (spZ regs - 80) ->
  getr regs1 9 = w64 (tab + 18 * cap) -> getr regs1 10 = w64 (tab + 18 * cap) ->
  getr regs1 11 = w64 90 -> getr regs1 12 = w64 17 -> getr regs1 23 = w64 SB ->
  sa_bytes (rdW W mem1) (tab + 18 * cap) SP.GUARD_BYTES ->
  range_addressable (rdW W mem1) SHADOW_OFF (tab + 18 * cap) 18 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 (map w64 [SB; tab + 18 * cap]))) cd_ss_guard
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + CD_GUARD)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS cd_Bx cd_g_SH (Eimg (Ereg regs1 (map w64 [SB; tab + 18 * cap]))) (mrestrict (w_H W) mem1).
Proof using HPRE HTB HTB1 HTB2 HMB HMB1 HMB2 HCAP HL HC LAWS.
intros regs1 mem1 R2 R9 R10 R11 R12 R23 HGB RAG.
pose proof cd_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : CD_STK = 8272) by reflexivity.
destruct cd_tabs as (Ht4 & Htc & _ & HtBD & _).
set (G := tab + 18 * cap) in *.
set (E := Eimg (Ereg regs1 (map w64 [SB; G]))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 80) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
pose proof (cd_ex_w64 regs1 [SB; G] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (cd_ex_w64 regs1 [SB; G] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
cbn [nth Nat.add] in E32, E33. fold E in E32, E33.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = G) by (rewrite E33; apply unsigned_lit_small; subst G; lia).
split.
- rewrite restrict_mkst_fx. unfold cd_ss_guard. apply pa_entry_st_ok_full.
  + cd_regs_ok EE ltac:(rewrite ?E32u, ?E33u).
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, cd_guard_r.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E33u.
    split; [subst G; lia|]. split; [subst G; lia|]. split; [intros o Ho; lia|].
    apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
    apply (chunk_ok_val SEGS E _ G (Z.of_nat j) 1 (SLit 90) 90); [reflexivity | cbn; lia | cbn; lia |].
    apply cd_val_mem_of_sa_val. apply cd_guard_byte; [exact HGB | lia].
  + cbn. tauto.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok cd_g_facts]. unfold afact_ok, cd_spF, cd_SBF, cd_PTRF. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32u, E33u. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; try (rewrite Zminus_mod, Hal16; reflexivity); subst G; lia.
- unfold sh_ok, cd_g_SH. apply Forall_cons; [|apply Forall_nil].
  apply (cd_shent_ok E _ 33 G 0 18 E32 E33u); try (subst G; lia).
  + rewrite Z.add_0_r. exact RAG.
  + intros y Hy. apply HtBD. subst G. lia.
Qed.
Lemma cd_guard : forall regs1 mem1 md1, cd_cut regs1 mem1 md1 ->
  getr regs1 9 = w64 (tab + 18 * cap) -> getr regs1 10 = w64 (tab + 18 * cap) ->
  getr regs1 11 = w64 90 -> getr regs1 12 = w64 17 -> getr regs1 23 = w64 SB ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + CD_GUARD)) mem1 (seg_rom SEGS)) md1) cd_Q.
Proof using HPRE HTB HTB1 HTB2 HMB HMB1 HMB2 HCAP HGD HL HC TL LAWS.
intros regs1 mem1 md1 HCUT R9 R10 R11 R12 R23.
pose proof HCUT as (HJ & HK & HFR & R2 & R3 & R4 & R24 & R25 & R26 & R27).
pose proof cd_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : CD_STK = 8272) by reflexivity.
destruct cd_tabs as (Ht4 & Htc & HtRA & HtBD & _).
assert (HGB : sa_bytes (rdW W mem1) (tab + 18 * cap) SP.GUARD_BYTES).
{ apply (cd_bytes_kept (rdW W mem) _ (spZ regs - CD_STK) (spZ regs) _ _ HK HGD); [lia | unfold SP.GUARD_BYTES; rewrite repeat_length; cbn; lia | lia]. }
assert (RAG : range_addressable (rdW W mem1) SHADOW_OFF (tab + 18 * cap) 18).
{ apply (range_addressable_kept_win (rdW W mem) (rdW W mem1) (spZ regs - CD_STK) (spZ regs)); [exact HK | lia | lia | lia |].
  apply (range_addressable_sub _ _ tab (18 * (cap + 1))); [exact HtRA | lia | lia]. }
destruct (cd_guard_seed regs1 mem1 R2 R9 R10 R11 R12 R23 HGB RAG) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (map w64 [SB; tab + 18 * cap])))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs1 (map w64 [SB; tab + 18 * cap]))) n = getr regs1 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 2%nat 2%bv eq_refl) as E2. pose proof (EE 3%nat 3%bv eq_refl) as E3. pose proof (EE 4%nat 4%bv eq_refl) as E4.
pose proof (EE 24%nat 24%bv eq_refl) as E24. pose proof (EE 25%nat 25%bv eq_refl) as E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. pose proof (EE 27%nat 27%bv eq_refl) as E27.
remember (Eimg (Ereg regs1 (map w64 [SB; tab + 18 * cap]))) as E eqn:HE0. clear HE0.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 80) by (rewrite E2, R2; apply unsigned_lit_small; lia).
(* the 18 bytes, each 0x5a, then 0x8778c: a3 = 0x5a, so `bne a3,a0` is not taken *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan CD_EPI.
{ awr_ok_tac; exact Usp. }
cd_md.
cd_keep_empty HFr KEEP1 (spZ regs - CD_STK) (spZ regs - CD_STK). clear HF HFr HG.
pmkst HS.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
apply cd_epi.
apply (cd_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ KEEP1); [lia | lia | rewrite Q2, E2; reflexivity
  | rewrite Q3, E3; reflexivity | rewrite Q4, E4; reflexivity | rewrite Q24, E24; reflexivity
  | rewrite Q25, E25; reflexivity | rewrite Q26, E26; reflexivity | rewrite Q27, E27; reflexivity].
Qed.

(* ---------- the guard set-up: 0x87730 .. 0x8774c, s1 := tab + 18 cap ---------- *)
Lemma cd_gset_seed : forall regs1 mem1, getr regs1 2 = w64 (spZ regs - 80) ->
  getr regs1 8 = w64 cap -> getr regs1 9 = w64 tab -> getr regs1 23 = w64 SB ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 (map w64 [SB; tab; cap]))) cd_ss_gset
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + CD_GSET)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS cd_Bx [] (Eimg (Ereg regs1 (map w64 [SB; tab; cap]))) (mrestrict (w_H W) mem1).
Proof using HPRE HTB HTB1 HTB2 HMB HMB1 HMB2 HCAP HL HC LAWS.
intros regs1 mem1 R2 R8 R9 R23.
pose proof cd_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : CD_STK = 8272) by reflexivity.
destruct cd_tabs as (Ht4 & Htc & _).
set (E := Eimg (Ereg regs1 (map w64 [SB; tab; cap]))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 80) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
pose proof (cd_ex_w64 regs1 [SB; tab; cap] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (cd_ex_w64 regs1 [SB; tab; cap] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (cd_ex_w64 regs1 [SB; tab; cap] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
cbn [nth Nat.add] in E32, E33, E34. fold E in E32, E33, E34.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = tab) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = cap) by (rewrite E34; apply unsigned_lit_small; lia).
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold cd_ss_gset. apply pa_entry_st_ok_full.
- cd_regs_ok EE ltac:(rewrite ?E32u, ?E33u, ?E34u).
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, cd_spF, cd_SBF, cd_PTRF, cd_CAPF. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32u, E33u, E34u. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; try lia; rewrite Zminus_mod, Hal16; reflexivity.
Qed.
Lemma cd_gset : forall regs1 mem1 md1, cd_cut regs1 mem1 md1 ->
  getr regs1 8 = w64 cap -> getr regs1 9 = w64 tab -> getr regs1 23 = w64 SB ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + CD_GSET)) mem1 (seg_rom SEGS)) md1) cd_Q.
Proof using HPRE HTB HTB1 HTB2 HMB HMB1 HMB2 HCAP HGD HL HC TL LAWS.
intros regs1 mem1 md1 HCUT R8 R9 R23.
pose proof HCUT as (HJ & HK & HFR & R2 & R3 & R4 & R24 & R25 & R26 & R27).
pose proof cd_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : CD_STK = 8272) by reflexivity.
destruct cd_tabs as (Ht4 & Htc & _).
destruct (cd_gset_seed regs1 mem1 R2 R8 R9 R23) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (map w64 [SB; tab; cap])))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs1 (map w64 [SB; tab; cap]))) n = getr regs1 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (cd_ex_w64 regs1 [SB; tab; cap] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (cd_ex_w64 regs1 [SB; tab; cap] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (cd_ex_w64 regs1 [SB; tab; cap] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
cbn [nth Nat.add] in E32, E33, E34.
pose proof (EE 2%nat 2%bv eq_refl) as E2. pose proof (EE 3%nat 3%bv eq_refl) as E3. pose proof (EE 4%nat 4%bv eq_refl) as E4.
pose proof (EE 24%nat 24%bv eq_refl) as E24. pose proof (EE 25%nat 25%bv eq_refl) as E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. pose proof (EE 27%nat 27%bv eq_refl) as E27.
remember (Eimg (Ereg regs1 (map w64 [SB; tab; cap]))) as E eqn:HE0. clear HE0.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 80) by (rewrite E2, R2; apply unsigned_lit_small; lia).
assert (U33 : U E (SOff 33 0) = tab) by (apply U_atom; [exact E33 | lia]).
assert (U34 : U E (SOff 34 0) = cap) by (apply U_atom; [exact E34 | lia]).
paj_run_to_tok RUNTO HS HJ SHOK Bspan CD_GUARD.
{ awr_ok_tac; exact Usp. }
cd_md.
cd_keep_empty HFr KEEP1 (spZ regs - CD_STK) (spZ regs - CD_STK). clear HF HFr HG.
pmkst HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_restrict_reg _ E ssx msx 9 HS) as Q9;
  pose proof (st_ok_pi_restrict_reg _ E ssx msx 10 HS) as Q10;
  let e9 := eval vm_compute in (sr_get (ss_regs ssx) 9) in change (sr_get (ss_regs ssx) 9) with e9 in Q9;
  let e10 := eval vm_compute in (sr_get (ss_regs ssx) 10) in change (sr_get (ss_regs ssx) 10) with e10 in Q10;
  cbn [ms_regs restrict mkst] in Q9, Q10 end.
assert (U9 : U E (SAlu ALU_ADD (SOff 33 0) (SMd M_MULHU (SAlu ALU_SLL (SOff 34 0) (SLit 32)) (SLit 77309411328)))
  = tab + 18 * cap) by (apply cd_gset_U; lia).
assert (U10 : U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 33 0) (SMd M_MULHU (SAlu ALU_SLL (SOff 34 0) (SLit 32)) (SLit 77309411328)))
  (SLit 0)) = tab + 18 * cap).
{ rewrite U_SAlu, U9, U_SLit. cbn [zalu_raw]. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_small. lia. }
assert (P9 : getr (ms_regs ms) 9 = w64 (tab + 18 * cap)) by (rewrite Q9; unfold w64; rewrite <- U9; unfold U; symmetry; apply Z_to_bv_bv_unsigned).
assert (P10 : getr (ms_regs ms) 10 = w64 (tab + 18 * cap)) by (rewrite Q10; unfold w64; rewrite <- U10; unfold U; symmetry; apply Z_to_bv_bv_unsigned).
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (23%bv : bv 5) Q23.
prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
apply cd_guard.
- apply (cd_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ KEEP1); [lia | lia | rewrite Q2, E2; reflexivity
    | rewrite Q3, E3; reflexivity | rewrite Q4, E4; reflexivity | rewrite Q24, E24; reflexivity
    | rewrite Q25, E25; reflexivity | rewrite Q26, E26; reflexivity | rewrite Q27, E27; reflexivity].
- exact P9.
- exact P10.
- rewrite Q11. reflexivity.
- rewrite Q12. reflexivity.
- rewrite Q23, E32. reflexivity.
Qed.

(* ---------- the entry loop's head: 0x876b4 at entry i ---------- *)
Definition cd_l_extra (i : nat) (v : Z) : list word :=
map w64 [SB; tab; cap; tab + 18 * Z.of_nat i; mt + 20 * Z.of_nat i; Z.of_nat (length gt) - Z.of_nat i; v].
Definition cd_LP (i : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
cd_cut regs1 mem1 md1 /\ (i < length gt)%nat /\
getr regs1 8 = w64 cap /\ getr regs1 9 = w64 tab /\
getr regs1 18 = w64 (mt + 20 * Z.of_nat i) /\ getr regs1 19 = w64 (Z.of_nat (length gt) - Z.of_nat i) /\
getr regs1 20 = w64 (mt + 20 * Z.of_nat i + 16) /\ getr regs1 21 = w64 (tab + 18 * Z.of_nat i + 16) /\
getr regs1 22 = w64 (tab + 18 * Z.of_nat i) /\ getr regs1 23 = w64 SB.
Lemma cd_loop_seed : forall (i : nat) v regs1 mem1, (i < length gt)%nat -> 0 <= v < 65536 ->
  getr regs1 2 = w64 (spZ regs - 80) ->
  getr regs1 8 = w64 cap -> getr regs1 9 = w64 tab ->
  getr regs1 18 = w64 (mt + 20 * Z.of_nat i) -> getr regs1 19 = w64 (Z.of_nat (length gt) - Z.of_nat i) ->
  getr regs1 20 = w64 (mt + 20 * Z.of_nat i + 16) -> getr regs1 21 = w64 (tab + 18 * Z.of_nat i + 16) ->
  getr regs1 22 = w64 (tab + 18 * Z.of_nat i) -> getr regs1 23 = w64 SB ->
  sa_val (rdW W mem1) (tab + 18 * Z.of_nat i + 16) 2 v ->
  range_addressable (rdW W mem1) SHADOW_OFF (tab + 18 * Z.of_nat i) 36 ->
  range_addressable (rdW W mem1) SHADOW_OFF (mt + 20 * Z.of_nat i) 40 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 (cd_l_extra i v))) cd_ss_loop
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + CD_LOOP)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS cd_Bx cd_l_SH (Eimg (Ereg regs1 (cd_l_extra i v))) (mrestrict (w_H W) mem1).
Proof using HPRE HTB HTB1 HTB2 HMB HMB1 HMB2 HCAP HL HC LAWS.
intros i v regs1 mem1 Hi Hv R2 R8 R9 R18 R19 R20 R21 R22 R23 VT RAT RAM.
pose proof cd_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : CD_STK = 8272) by reflexivity.
destruct cd_tabs as (Ht4 & Htc & _ & HtBD & Hm4 & Hmc & _ & HmBD).
set (E := Eimg (Ereg regs1 (cd_l_extra i v))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 80) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (EX : forall j x, nth_error [SB; tab; cap; tab + 18 * Z.of_nat i; mt + 20 * Z.of_nat i; Z.of_nat (length gt) - Z.of_nat i; v] j = Some x ->
  ew E (32 + j) = w64 x).
{ intros j x Hj. assert (Hj7 : (j < 7)%nat) by (change 7%nat with (length [SB; tab; cap; tab + 18 * Z.of_nat i; mt + 20 * Z.of_nat i; Z.of_nat (length gt) - Z.of_nat i; v]); apply (proj1 (nth_error_Some _ j)); rewrite Hj; discriminate).
  subst E. unfold cd_l_extra. rewrite cd_ex_w64 by (cbn; unfold A_TEXT; lia). f_equal. apply nth_error_nth. exact Hj. }
pose proof (EX 0%nat _ eq_refl) as E32. pose proof (EX 1%nat _ eq_refl) as E33. pose proof (EX 2%nat _ eq_refl) as E34.
pose proof (EX 3%nat _ eq_refl) as E35. pose proof (EX 4%nat _ eq_refl) as E36. pose proof (EX 5%nat _ eq_refl) as E37.
pose proof (EX 6%nat _ eq_refl) as E38.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38. clear EX.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = tab) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = cap) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = tab + 18 * Z.of_nat i) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = mt + 20 * Z.of_nat i) by (rewrite E36; apply unsigned_lit_small; lia).
assert (E37u : bv_unsigned (ew E 37) = Z.of_nat (length gt) - Z.of_nat i) by (rewrite E37; apply unsigned_lit_small; lia).
assert (E38u : bv_unsigned (ew E 38) = v) by (rewrite E38; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold cd_ss_loop. apply pa_entry_st_ok_full.
  + cd_regs_ok EE ltac:(rewrite ?E32u, ?E33u, ?E34u, ?E35u, ?E36u, ?E37u, ?E38u).
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, cd_entT.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E35u.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (tab + 18 * Z.of_nat i) 16 2 (SOff 38 0) v); [cbn [sv_denot]; rewrite E38u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
    apply cd_val_mem_of_sa_val. exact VT.
  + cbn. tauto.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok cd_l_facts]. unfold afact_ok, cd_spF, cd_SBF, cd_PTRF, cd_CAPF, cd_CNTF, cd_VIDF.
    cbn [af_lo af_hi af_al2].
    rewrite Usp, E32u, E33u, E34u, E35u, E36u, E37u, E38u. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; rewrite Zminus_mod, Hal16; reflexivity.
- unfold sh_ok, cd_l_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (cd_shent_ok E _ 35 (tab + 18 * Z.of_nat i) 0 36 E32 E35u); try lia; [rewrite Z.add_0_r; exact RAT | intros y Hy; apply HtBD; lia].
  + apply (cd_shent_ok E _ 36 (mt + 20 * Z.of_nat i) 0 40 E32 E36u); try lia; [rewrite Z.add_0_r; exact RAM | intros y Hy; apply HmBD; lia].
Qed.

(* ---------- a parent string at the strcmp call, and the image bytes the wrapper reads ---------- *)
Lemma cd_str_call : forall x s p k memc regsc, In (p, k) (ablocks B ly S) -> p <= x -> x + Z.of_nat (length s) + 1 <= p + k ->
  sa_bytes (rdW W mem) x (s ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) s ->
  cd_kept (rdW W mem) (rdW W memc) (spZ regs - CD_STK) (spZ regs) -> spZ regsc = spZ regs - 80 ->
  0 < x /\ astr_at SEGS W memc x s /\ aread_ok SEGS (2 * ESTACK) W regsc memc x (astr_len s + 1) /\
  atail_vis SEGS W memc (x + astr_len s).
Proof using HPRE HCAP HL HC LAWS.
intros x s p k memc regsc Hpk Hpx Hxk HB HN HK Hsp.
pose proof HPRE as (HAR & _). pose proof cd_sp as (Hal16 & Hslo & Hshi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : CD_STK = 8272) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity. pose proof alloc_ceiling_value as [_ HAC].
destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hpk) as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hkr).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
split; [lia|]. split.
{ split; [|exact HN]. apply (cd_bytes_kept (rdW W mem) _ (spZ regs - CD_STK) (spZ regs) x _ HK HB); [lia | rewrite length_app; cbn [length]; lia | lia]. }
split.
{ unfold astr_len.
  apply (aread_ok_kept SEGS 0 (2 * ESTACK) W regs regsc mem memc (spZ regs - CD_STK) (spZ regs) x _ HK);
    [| lia | lia | lia | rewrite Hsp, Hes; lia | lia].
  apply (aread_ok_of_block SEGS B LAWS 0 ly S W regs mem md p k x _ HAR Hpk Hpx); lia. }
{ assert (Hxe : 0 <= x + astr_len s < alloc_ceiling) by (unfold astr_len; lia).
  pose proof (tail_below _ _ Hxe HAC) as HTB0.
  apply (atail_vis_kept SEGS W mem memc _ _ _ HK); [| unfold astr_len; lia | lia | lia].
  intros a Ha. apply (AR_block_word_vis SEGS B ly S W mem md p k (x + astr_len s) a HAR Hpk); unfold astr_len in *; lia. }
Qed.
Lemma cd_rom_at : forall memc, cd_kept (rdW W mem) (rdW W memc) (spZ regs - CD_STK) (spZ regs) ->
  rt_rom_view SEGS B W memc.
Proof using HPRE HROD HCAP HL HC.
intros memc HK x Hx Ho He. pose proof cd_sp as (Hal16 & Hslo & Hshi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : CD_STK = 8272) by reflexivity.
destruct Hx as (sg & Hsg & Hw & Hr).
assert (Himg : in_img SEGS x) by (exists sg; split; [exact Hsg | exact Hr]).
pose proof (pa_img_range _ Himg) as HR. unfold kImgEnd in HR. rewrite (HK x) by lia.
apply HROD; [left; exists sg; split; [exact Hsg | split; [exact Hw | exact Hr]] | exact Ho | exact He].
Qed.

(* ---------- one entry of the loop: 0x876b4 .. 0x87708 ---------- *)
Lemma cd_loop_step : forall i regs1 mem1 md1,
  ((Datatypes.S i < length gt)%nat -> forall r m d, cd_LP (Datatypes.S i) r m d ->
    SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + CD_LOOP)) m (seg_rom SEGS)) d) cd_Q) ->
  cd_LP i regs1 mem1 md1 ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + CD_LOOP)) mem1 (seg_rom SEGS)) md1) cd_Q.
Proof using HPRE HROD HTB HTB1 HTB2 HMB HMB1 HMB2 HCAP HBT HET HBM HEM HGD HL HC HE TL ASTRCMP LAWS.
intros i regs1 mem1 md1 NXT (HCUT & Hi & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23).
pose proof HCUT as (HJ & HK & HFR & R2 & R3 & R4 & R24 & R25 & R26 & R27).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof cd_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : CD_STK = 8272) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct cd_tabs as (Ht4 & Htc & HtRA & HtBD & Hm4 & Hmc & HmRA & HmBD).
assert (Hiw : (i < length wt)%nat) by lia.
destruct (HE i Hi) as [EV ES].
destruct (cd_rtab_entry _ tab gt bt i HBT HET Hi) as (VT & RV & sx & BX & ZX & NX & LX).
destruct (cd_mtab_entry _ mt wt bm i HBM HEM Hiw) as (VM & RVM & sy & BY & ZY & NY & LY).
rewrite <- EV in VM.
assert (HSX : sx = sy) by (apply cd_bridge_strcmp; [exact NX | exact NY | rewrite ZX, ZY; exact ES]).
set (v := snd (nth i gt ([], 0))) in *.
assert (VT1 : sa_val (rdW W mem1) (tab + 18 * Z.of_nat i + 16) 2 v)
  by (apply (cd_val_kept (rdW W mem) _ (spZ regs - CD_STK) (spZ regs) _ _ _ HK VT); cbn; lia).
assert (RAT1 : range_addressable (rdW W mem1) SHADOW_OFF (tab + 18 * Z.of_nat i) 36).
{ apply (range_addressable_kept_win (rdW W mem) (rdW W mem1) (spZ regs - CD_STK) (spZ regs)); [exact HK | lia | lia | lia |].
  apply (range_addressable_sub _ _ tab (18 * (cap + 1))); [exact HtRA | lia | lia]. }
assert (RAM1 : range_addressable (rdW W mem1) SHADOW_OFF (mt + 20 * Z.of_nat i) 40).
{ apply (range_addressable_kept_win (rdW W mem) (rdW W mem1) (spZ regs - CD_STK) (spZ regs)); [exact HK | lia | lia | lia |].
  apply (range_addressable_sub _ _ mt (20 * (cap + 1))); [exact HmRA | lia | lia]. }
destruct (cd_loop_seed i v regs1 mem1 Hi RV R2 R8 R9 R18 R19 R20 R21 R22 R23 VT1 RAT1 RAM1) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (cd_l_extra i v)))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs1 (cd_l_extra i v))) n = getr regs1 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j x, nth_error [SB; tab; cap; tab + 18 * Z.of_nat i; mt + 20 * Z.of_nat i; Z.of_nat (length gt) - Z.of_nat i; v] j = Some x ->
  ew (Eimg (Ereg regs1 (cd_l_extra i v))) (32 + j) = w64 x).
{ intros j x Hj. assert (Hj7 : (j < 7)%nat) by (change 7%nat with (length [SB; tab; cap; tab + 18 * Z.of_nat i; mt + 20 * Z.of_nat i; Z.of_nat (length gt) - Z.of_nat i; v]); apply (proj1 (nth_error_Some _ j)); rewrite Hj; discriminate).
  unfold cd_l_extra. rewrite cd_ex_w64 by (cbn; unfold A_TEXT; lia). f_equal. apply nth_error_nth. exact Hj. }
pose proof (EX 0%nat _ eq_refl) as E32. pose proof (EX 1%nat _ eq_refl) as E33. pose proof (EX 2%nat _ eq_refl) as E34.
pose proof (EX 3%nat _ eq_refl) as E35. pose proof (EX 4%nat _ eq_refl) as E36. pose proof (EX 5%nat _ eq_refl) as E37.
pose proof (EX 6%nat _ eq_refl) as E38.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38. clear EX.
pose proof (EE 2%nat 2%bv eq_refl) as E2. pose proof (EE 3%nat 3%bv eq_refl) as E3. pose proof (EE 4%nat 4%bv eq_refl) as E4.
pose proof (EE 24%nat 24%bv eq_refl) as E24. pose proof (EE 25%nat 25%bv eq_refl) as E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. pose proof (EE 27%nat 27%bv eq_refl) as E27.
remember (Eimg (Ereg regs1 (cd_l_extra i v))) as E eqn:HE0. clear HE0.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 80) by (rewrite E2, R2; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = tab + 18 * Z.of_nat i) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = mt + 20 * Z.of_nat i) by (rewrite E36; apply unsigned_lit_small; lia).
assert (E37u : bv_unsigned (ew E 37) = Z.of_nat (length gt) - Z.of_nat i) by (rewrite E37; apply unsigned_lit_small; lia).
assert (E38u : bv_unsigned (ew E 38) = v) by (rewrite E38; apply unsigned_lit_small; lia).
(* 0x876b4 .. 0x876d4: the check of tab[i].vid (slow block 0x8770c), the check of mt[i].vid (slow block 0x8771c),
   tab[i].vid; mt[i].vid needs mt[i]'s region *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
cd_md.
cd_keep_empty HFr KEEP1 (spZ regs - CD_STK) (spZ regs - 80). clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (RB : region_ok SEGS E (ms_mem (restrict (w_H W) msx)) cd_entM);
  [ cbn [ms_mem restrict]; unfold region_ok, cd_entM;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite E36u;
    split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val SEGS E _ (mt + 20 * Z.of_nat i) 16 4 (SOff 38 0) v); [cbn [sv_denot]; rewrite E38u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |];
    apply cd_val_mem_of_sa_val;
    apply (cd_val_kept (rdW W mem) _ (spZ regs - CD_STK) (spZ regs));
    [ apply (cd_kept_trans _ _ _ _ _ _ _ HK KEEP1); lia | exact VM | lia | cbn; lia | cbn; lia ]
  | ] end.
pose proof (cd_swap_ok E _ _ cd_entM HS eq_refl RB) as HS'. clear HS RB. rename HS' into HS.
(* 0x876d8 .. 0x876e8: mt[i].vid; `bne a1,a0` (the abort arm 0x877c0) is decided by the executor: both loads give the
   atom 38, the one vid below 2^16, so `lhu` and the sign extension of `lw` are the same value; a0 := tab + 18 i,
   a1 := mt + 20 i; the call of the strcmp wrapper *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
cd_md.
cd_keep_empty HFr KEEP2 (spZ regs - CD_STK) (spZ regs - 80). clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  set (rT0 := rT) in *; set (mT0 := mT) in * end.
assert (KEEPc : cd_kept (rdW W mem) (rdW W mT0) (spZ regs - CD_STK) (spZ regs)).
{ apply (cd_kept_trans _ _ _ _ _ _ _ (cd_kept_trans _ _ _ _ _ _ _ HK KEEP1 ltac:(lia) ltac:(lia)) KEEP2); lia. }
assert (HspT : spZ rT0 = spZ regs + -80) by (unfold spZ at 1; rewrite P2, Usp; lia).
assert (HspT' : spZ rT0 = spZ regs - 80) by lia.
assert (P3' : getr rT0 3 = w64 (as_gp B)) by (rewrite P3, E3, R3; exact Hgp).
assert (P4' : getr rT0 4 = w64 (as_tp B)) by (rewrite P4, E4, R4; exact Htp).
assert (HraT : YK0s.ret_ok (getr rT0 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (P10' : getr rT0 10 = w64 (tab + 18 * Z.of_nat i)) by (rewrite P10, E35; reflexivity).
assert (P11' : getr rT0 11 = w64 (mt + 20 * Z.of_nat i)) by (rewrite P11, E36; reflexivity).
destruct (cd_str_call (tab + 18 * Z.of_nat i) sx pt kt mT0 rT0 HTB ltac:(lia) ltac:(lia) BX NX KEEPc HspT') as (Hxa0 & STRa & RDa & TLa).
destruct (cd_str_call (mt + 20 * Z.of_nat i) sy pm km mT0 rT0 HMB ltac:(lia) ltac:(lia) BY NY KEEPc HspT') as (Hxb0 & STRb & RDb & TLb).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False) (SIG SS___interceptor_trampoline_strcmp)
    W rT0 mT0 CD_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (-80) (Z_to_bv 64 (BASE + CD_RET)) _ HJ HspT eq_refl
    ltac:(lia) ltac:(lia) ltac:(rewrite HST, Hes; lia) P1 (fun a0 (H : False) => False_ind _ H)).
  apply (ASTRCMP fx ly S W rT0 mT0 _ (tab + 18 * Z.of_nat i) (mt + 20 * Z.of_nat i) sx sy).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) CD_STK (spZ regs) [] ly S W mem md [] ly S W mT0 _ 0 rT0 (-80)
      HJ HspT eq_refl ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite HST, Hes; lia) HraT P3' P4').
  - exact P10'. - exact P11'. - lia. - lia.
  - exact STRa. - exact STRb. - exact RDa. - exact RDb. - exact TLa. - exact TLb.
  - exact (cd_rom_at mT0 KEEPc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
(* back at 0x876ec *)
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (A52 : ew (havoc E 48 (map (getr regs2) CLOB)) 52 = getr regs2 10) by reflexivity.
remember (havoc E 48 (map (getr regs2) CLOB)) as Ec eqn:HEc.
assert (HEI3 : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall n, (n < 48)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; apply YN3v.ew_havoc_old; exact Hn).
clear HEc.
assert (Usp3 : bv_unsigned (ew Ec 2) = spZ regs - 80) by (rewrite OLD3 by lia; exact Usp).
assert (SHOK3 : sh_ok SEGS cd_Bx [] Ec (mrestrict (w_H W) mem2)) by apply Forall_nil.
assert (KEEPk : cd_kept (rdW W mT0) (rdW W mem2) (spZ regs - CD_STK) (spZ regs - 80))
  by (intros x0 Hx0 Hn0; apply HK2; [exact Hx0 | rewrite Hes; lia | tauto]).
clear HK2. clear HJ. rename HJ2 into HJ.
assert (KEEPm : cd_kept (rdW W mem1) (rdW W mem2) (spZ regs - CD_STK) (spZ regs - 80)).
{ apply (cd_kept_trans _ _ _ _ _ _ _ (cd_kept_trans _ _ _ _ _ _ _ KEEP1 KEEP2 ltac:(lia) ltac:(lia)) KEEPk); lia. }
clear KEEP1 KEEP2 KEEPk KEEPc.
(* 0x876ec: bnez a0, the wrapper's answer: the parents are equal strings, so it is 0 *)
psrr_branch_tok RUN BR HS SHOK3 Bspan.
{ exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc. unfold U. f_equal. cbn [sv_denot].
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, A52, (proj2 HQ2 HSX). reflexivity. }
clear Hc.
(* 0x876f0 .. 0x87704: s3 -= 1, the cursors step, beqz s3 *)
paj_run_tok RUN HS HJ SHOK3 Bspan.
{ awr_ok_tac; exact Usp3. }
cd_md.
cd_keep_empty HFr KEEP4 (spZ regs - CD_STK) (spZ regs - 80). clear HF HFr HG.
assert (U37 : U Ec (SOff 37 (-1)) = Z.of_nat (length gt) - Z.of_nat i - 1).
{ apply U_atom_off; [rewrite OLD3 by lia; exact E37 | lia | lia]. }
psrr_branch_tok RUN BR HS SHOK3 Bspan.
- (* the last entry: to the guard set-up 0x87730 *)
  assert (HiN : Datatypes.S i = length gt).
  { rewrite branch_eq_U in Hc. rewrite ?U37, ?U_SLit in Hc. apply Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK3 Bspan CD_GSET.
  { awr_ok_tac; exact Usp3. }
  cd_md.
  cd_keep_empty HFr KEEP5 (spZ regs - CD_STK) (spZ regs - 80). clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  rewrite ?OLD3 in Q2, Q3, Q4, Q8, Q9, Q23, Q24, Q25, Q26, Q27 by lia.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mF _) _) _ =>
    assert (KEEP : cd_kept (rdW W mem1) (rdW W mF) (spZ regs - CD_STK) (spZ regs - 80))
      by (apply (cd_kept_trans _ _ _ _ _ _ _ (cd_kept_trans _ _ _ _ _ _ _ KEEPm KEEP4 ltac:(lia) ltac:(lia)) KEEP5); lia) end.
  apply cd_gset.
  + apply (cd_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ KEEP); [lia | lia | rewrite Q2, E2; reflexivity
      | rewrite Q3, E3; reflexivity | rewrite Q4, E4; reflexivity | rewrite Q24, E24; reflexivity
      | rewrite Q25, E25; reflexivity | rewrite Q26, E26; reflexivity | rewrite Q27, E27; reflexivity].
  + rewrite Q8, E34. reflexivity.
  + rewrite Q9, E33. reflexivity.
  + rewrite Q23, E32. reflexivity.
- (* more entries: back to the loop head with i + 1 *)
  assert (HiN : (Datatypes.S i < length gt)%nat).
  { rewrite branch_eq_U in Hc. rewrite ?U37, ?U_SLit in Hc. apply Z.eqb_neq in Hc. change (zcanon 0) with 0 in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK3 Bspan CD_LOOP.
  { awr_ok_tac; exact Usp3. }
  cd_md.
  cd_keep_empty HFr KEEP5 (spZ regs - CD_STK) (spZ regs - 80). clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  rewrite ?OLD3 in Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27 by lia.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mF _) _) _ =>
    assert (KEEP : cd_kept (rdW W mem1) (rdW W mF) (spZ regs - CD_STK) (spZ regs - 80))
      by (apply (cd_kept_trans _ _ _ _ _ _ _ (cd_kept_trans _ _ _ _ _ _ _ KEEPm KEEP4 ltac:(lia) ltac:(lia)) KEEP5); lia) end.
  apply (NXT HiN). split.
  { apply (cd_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ KEEP); [lia | lia | rewrite Q2, E2; reflexivity
      | rewrite Q3, E3; reflexivity | rewrite Q4, E4; reflexivity | rewrite Q24, E24; reflexivity
      | rewrite Q25, E25; reflexivity | rewrite Q26, E26; reflexivity | rewrite Q27, E27; reflexivity]. }
  split; [exact HiN|].
  split; [rewrite Q8, E34; reflexivity|]. split; [rewrite Q9, E33; reflexivity|].
  split; [rewrite Q18, E36u; unfold w64; f_equal; lia|].
  split; [rewrite Q19, E37u; unfold w64; f_equal; lia|].
  split; [rewrite Q20, E36u; unfold w64; f_equal; lia|].
  split; [rewrite Q21, E35u; unfold w64; f_equal; lia|].
  split; [rewrite Q22, E35u; unfold w64; f_equal; lia|].
  rewrite Q23, E32. reflexivity.
Qed.
Lemma cd_loop_all : forall dd i, (i + dd = length gt)%nat -> (i < length gt)%nat -> forall r m d, cd_LP i r m d ->
  SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + CD_LOOP)) m (seg_rom SEGS)) d) cd_Q.
Proof using HPRE HROD HTB HTB1 HTB2 HMB HMB1 HMB2 HCAP HBT HET HBM HEM HGD HL HC HE TL ASTRCMP LAWS.
induction dd as [|dd IH]; intros i Hd Hi r m d HLP; [lia|].
apply (cd_loop_step i); [|exact HLP].
intros Hsi r' m' d' HLP'. apply (IH (Datatypes.S i)); [lia | exact Hsi | exact HLP'].
Qed.

(* ---------- the entry: 0x87658 .. 0x876b4 ---------- *)
Lemma cd_stack_field : forall E H mem' cs off n v,
  region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 cs) -> bv_unsigned (ew E 2) = spZ regs ->
  In (YP09.mkChunk off (CVal 8 (SOff n 0))) cs -> ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  sa_val (aview SEGS H mem') (spZ regs + off) 8 v.
Proof using HCAP HL HC.
intros E H mem' cs off n v HR Hsp Hin Hn Hv k Hk.
change 8%nat with (N.to_nat 8) in Hk |- *.
pose proof (field_of_region E _ 2 (spZ regs) cs (-80) 0 (-80) 0 off 8 (SOff n 0) v HR Hsp Hin) as HF.
assert (HFv : val_mem SEGS (mrestrict H mem') (spZ regs + off) (N.to_nat 8) v).
{ apply HF.
  - cbn [sv_denot]. rewrite Hn, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  - cbn. lia. }
unfold aview. rewrite (HFv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YG0f.le_byte. apply Z.mod_mod. lia.
Qed.
Lemma cd_entry_seed :
  st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 SB])) cd_ss_entry
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_declared)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS cd_Bx [] (Eimg (Ereg regs [w64 SB])) (mrestrict (w_H W) mem).
Proof using HPRE HCAP HL HC TL LAWS.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof cd_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : CD_STK = 8272) by reflexivity.
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
rewrite restrict_mkst_fx. unfold cd_ss_entry. apply pa_entry_st_ok_full.
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
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, cd_spF, cd_SBF. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat split; try lia; exact Hal16.
Qed.
Lemma cd_entry_gen :
  (forall r m d, cd_LP 0 r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + CD_LOOP)) m (seg_rom SEGS)) d) cd_Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_check_declared) regs mem md) cd_Q.
Proof using HPRE H1011 H12 H13 H14 H15 H16 HTB HTB1 HTB2 HMB HMB1 HMB2 HCAP HGD HL HC TL LAWS.
intros LOOP.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof cd_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : CD_STK = 8272) by reflexivity.
destruct cd_tabs as (Ht4 & Htc & _ & _ & Hm4 & Hmc & _ & _).
destruct cd_entry_seed as [HS SHOK].
pose proof (ajournal_init SEGS B CD_STK [] ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs [w64 SB]))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs [w64 SB])) n = getr regs r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (Eimg (Ereg regs [w64 SB])) 32 = w64 SB) by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
remember (Eimg (Ereg regs [w64 SB])) as E eqn:HE0. clear HE0.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E13 : ew E 13 = w64 (Z.of_nat (length gt))) by (rewrite (EE 13%nat 13%bv eq_refl); exact H13).
assert (FRM : forall H mem' cs, region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 cs) ->
  (forall j r, nth_error cd_saved j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
  cd_frame (aview SEGS H mem')).
{ intros H mem' cs HR Hin j r Hr.
  assert (Hr' : 1 <= r <= 23) by (apply nth_error_In in Hr; cbn in Hr; intuition lia).
  replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia.
  apply (cd_stack_field E H mem' cs _ (Z.to_nat r)); [exact HR | exact Usp | exact (Hin j r Hr) | |
    pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr; change (bv_modulus 64) with (2 ^ 64) in HRr; exact HRr].
  rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
unfold cfg_at. change (w64 (BASE + AF_check_declared)) with (Z_to_bv 64 (BASE + AF_check_declared)).
(* 0x87658 .. 0x87680: the frame, bne a0,a1 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
cd_md.
cd_keep_win HFr KEEP0 (spZ regs - CD_STK) (spZ regs) Usp. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* got <> want: the abort arm 0x877c0, refuted *)
  exfalso. rewrite branch_ne_U, !U_SOff in Hc. rewrite (EE 10%nat 10%bv eq_refl), (EE 11%nat 11%bv eq_refl), H1011 in Hc.
  rewrite Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
(* 0x87684 .. 0x87688: s3 := n, bne a3,a5 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
cd_md.
cd_keep_win HFr KEEP1 (spZ regs - CD_STK) (spZ regs) Usp. clear HF HFr HG.
pose proof (cd_kept_trans _ _ _ _ _ _ _ KEEP0 KEEP1 (Z.le_refl _) (Z.le_refl _)) as K01. clear KEEP0 KEEP1.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* n <> mn: the abort arm, refuted *)
  exfalso. rewrite branch_ne_U, !U_SOff in Hc. rewrite (EE 13%nat 13%bv eq_refl), (EE 15%nat 15%bv eq_refl), H13, H15 in Hc.
  rewrite Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
(* 0x8768c .. 0x876a0: s0 := cap, s1 := tab, the shadow base, blez s3 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
cd_md.
cd_keep_win HFr KEEP2 (spZ regs - CD_STK) (spZ regs) Usp. clear HF HFr HG.
pose proof (cd_kept_trans _ _ _ _ _ _ _ K01 KEEP2 (Z.le_refl _) (Z.le_refl _)) as K02. clear K01 KEEP2.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* no entry: to the guard set-up *)
  assert (H0 : length gt = 0%nat).
  { rewrite (cd_bge0 E 13 (Z.of_nat (length gt)) E13) in Hc by lia. apply Z.leb_le in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan CD_GSET.
  { awr_ok_tac; exact Usp. }
  cd_md.
  cd_keep_win HFr KEEP3 (spZ regs - CD_STK) (spZ regs) Usp. clear HF HFr HG.
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict] in HRg end.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  apply cd_gset.
  + split; [exact HJ|]. split; [apply (cd_kept_trans _ _ _ _ _ _ _ K02 KEEP3); lia|].
    split.
    { apply (FRM _ _ _ HRg). intros j r Hr. do 9 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]).
      cbn in Hr; destruct j; discriminate Hr. }
    split; [rewrite Q2, Usp; reflexivity|].
    split; [rewrite Q3; apply EE; reflexivity|]. split; [rewrite Q4; apply EE; reflexivity|].
    split; [rewrite Q24; apply EE; reflexivity|]. split; [rewrite Q25; apply EE; reflexivity|].
    split; [rewrite Q26; apply EE; reflexivity|]. rewrite Q27; apply EE; reflexivity.
  + rewrite Q8, (EE 16%nat 16%bv eq_refl). exact H16.
  + rewrite Q9, (EE 12%nat 12%bv eq_refl). exact H12.
  + rewrite Q23, E32. reflexivity.
- (* entries: 0x876a4 .. 0x876b0, the cursors, then the loop at entry 0 *)
  assert (H0 : (0 < length gt)%nat).
  { rewrite (cd_bge0 E 13 (Z.of_nat (length gt)) E13) in Hc by lia. apply Z.leb_gt in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan CD_LOOP.
  { awr_ok_tac; exact Usp. }
  cd_md.
  cd_keep_win HFr KEEP3 (spZ regs - CD_STK) (spZ regs) Usp. clear HF HFr HG.
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict] in HRg end.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  assert (Utab : bv_unsigned (ew E 12) = tab) by (rewrite (EE 12%nat 12%bv eq_refl), H12; apply unsigned_lit_small; lia).
  assert (Umt : bv_unsigned (ew E 14) = mt) by (rewrite (EE 14%nat 14%bv eq_refl), H14; apply unsigned_lit_small; lia).
  apply LOOP.
  split.
  { split; [exact HJ|]. split; [apply (cd_kept_trans _ _ _ _ _ _ _ K02 KEEP3); lia|].
    split.
    { apply (FRM _ _ _ HRg). intros j r Hr. do 9 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]).
      cbn in Hr; destruct j; discriminate Hr. }
    split; [rewrite Q2, Usp; reflexivity|].
    split; [rewrite Q3; apply EE; reflexivity|]. split; [rewrite Q4; apply EE; reflexivity|].
    split; [rewrite Q24; apply EE; reflexivity|]. split; [rewrite Q25; apply EE; reflexivity|].
    split; [rewrite Q26; apply EE; reflexivity|]. rewrite Q27; apply EE; reflexivity. }
  split; [exact H0|].
  split; [rewrite Q8, (EE 16%nat 16%bv eq_refl); exact H16|].
  split; [rewrite Q9, (EE 12%nat 12%bv eq_refl); exact H12|].
  split; [rewrite Q18, (EE 14%nat 14%bv eq_refl), H14; unfold w64; f_equal; lia|].
  split; [rewrite Q19, (EE 13%nat 13%bv eq_refl), H13; unfold w64; f_equal; lia|].
  split; [rewrite Q20, Umt; unfold w64; f_equal; lia|].
  split; [rewrite Q21, Utab; unfold w64; f_equal; lia|].
  split; [rewrite Q22, (EE 12%nat 12%bv eq_refl), H12; unfold w64; f_equal; lia|].
  rewrite Q23, E32. reflexivity.
Qed.
Lemma cd_entry : SRr SEGS W (cfg_at SEGS (BASE + AF_check_declared) regs mem md) cd_Q.
Proof using HPRE HROD H1011 H12 H13 H14 H15 H16 HTB HTB1 HTB2 HMB HMB1 HMB2 HCAP HBT HET HBM HEM HGD HL HC HE TL ASTRCMP LAWS.
apply cd_entry_gen. intros r m d HLP.
pose proof HLP as (_ & Hn & _).
apply (cd_loop_all (length gt) 0); [lia | exact Hn | exact HLP].
Qed.

End w.

(* ---------- the contract ---------- *)
Theorem check_declared_walk :
  check_declared_contract SEGS B (BASE + AF_check_declared) SegInstA.STK_check_declared SegInstA.RLO_A SegInstA.RHI_A.
Proof using TL ASTRCMP.
unfold check_declared_contract.
intros ly S W regs mem md ch got want tab n mt mn cap gv wv gt wt HPRE HROD H10 Rgot H11 Rwant H12 Rtab H13 Rn H14 Rmt
  H15 Rmn H16 Rcap HCD HEV.
destruct HCD as (Egot & Ewant & Hgv & Hwv & Hcap & Htab0 & Htab16 & (bt & HBT & HET) & HGD & (pt & kt & HTB & HTB1 & HTB2)
  & HTA & HTS & En & Hmt0 & Hmt16 & (bm & HBM & HEM) & (pm & km & HMB & HMB1 & HMB2) & HMA & HMS & Hwl & Emn & HV).
destruct (cd_vlans_are_spec _ _ _ _ _ HV) as (Egw & HL & HC & HE).
unfold sa_guardtab in HGD. unfold SP.RVLAN_SIZE, SP.MVLAN_SIZE in *.
subst n mn.
apply (cd_entry ly S W regs mem md ch tab mt cap pt kt pm km gt wt bt bm SegInstA.RLO_A SegInstA.RHI_A); try assumption.
- rewrite H10, H11, Egot, Ewant, Egw. reflexivity.
- rewrite H15, <- HL. reflexivity.
Qed.
End e.
End d.
End b.
