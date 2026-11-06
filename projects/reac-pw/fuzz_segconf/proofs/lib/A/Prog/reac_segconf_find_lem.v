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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/reac_segconf_declared_s1.v, with its module paths and module names changed; 53 of its 93 lines of code are new or changed and 836 lines of the source are left out. *)
(* reac_segconf_find on fuzz_segconf.asan (image A): the facts its walk (reac_segconf_find.v) reads off the
   contract's reader premises, stated over SegABase's reader forms and seg_spec's encodings. No machine state here.
   - c->n: the 4 bytes at c + 0x2c80 read as n = length (rc_seg rcs) (rconf_enc's u32_enc at RC_N), the value of
     the `lw` at 0x8953c;
   - the name of c->seg[i] with its NUL, the bytes the strcmp wrapper reads (the A twin of the plain
     seg_query_facts.sq_seg_name, over sa_bytes), shorter than its 16-byte field;
   - S = set_fs (st_fs S) S, the last conjunct of sa_noalloc;
   - the name argument nm as the byte list the wrapper's contract takes (zb nm) is SegABase.sa_strz_bytes, and
     the model side of the loop is seg_query_facts' (sq_find_go_step, sq_find_go_end, sq_name_cmp). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0f YG00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Lemma fnd_nth_skipn : forall {A} (l : list A) j i d, nth i (skipn j l) d = nth (j + i) l d.
Proof.
induction l as [|a l IH]; intros [|j] i d; cbn; [destruct i; reflexivity | destruct i; reflexivity | reflexivity | apply IH].
Qed.

(* a stretch of the bytes at a *)
Lemma fnd_bytes_sub : forall (rd : reader) a bs k n, sa_bytes rd a bs -> (k + n <= length bs)%nat ->
sa_bytes rd (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
intros rd a bs k n H L i Hi. rewrite length_firstn, length_skipn in Hi.
replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
rewrite (H (k + i)%nat) by lia. f_equal. f_equal.
rewrite nth_firstn. replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
symmetry. apply fnd_nth_skipn.
Qed.

(* ---------- c->n ---------- *)
Lemma fnd_le_bytes_nth : forall n z k, (k < n)%nat ->
nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth_error]. rewrite IH by lia. f_equal. f_equal.
  rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma fnd_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold Mem.le4.
assert (Uv : bv_unsigned (Z_to_bv 64 v) = v).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. change (bv_modulus 64) with (2 ^ 64). lia. }
rewrite Uv. rewrite (nth_error_nth _ _ _ (fnd_le_bytes_nth 4 v k Hk)).
rewrite Z_to_bv_unsigned. unfold bv_wrap, le_byte. change (bv_modulus 8) with 256.
rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat 4))) by (cbn; lia). reflexivity.
Qed.
(* a little-endian field of the block, read byte by byte *)
Lemma fnd_fldz_val : forall (rd : reader) a bs off n v,
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
symmetry. apply fnd_nth_skipn.
Qed.
Lemma fnd_rc_n : forall (rd : reader) c bs rc, sa_bytes rd c bs -> seg_spec.rconf_enc rc bs ->
sa_val rd (c + seg_spec.RC_N) 4 (Z.of_nat (length (SegModel.rc_seg rc))) /\
(length (SegModel.rc_seg rc) <= 32)%nat.
Proof.
intros rd c bs rc HB HE. destruct (seg_query_facts.sq_rconf_len rc bs HE) as [L LS].
destruct HE as (_ & _ & _ & (Hv & HN) & _). split; [|exact LS].
apply (fnd_fldz_val rd c bs seg_spec.RC_N 4 _ HB);
  [unfold seg_spec.RC_N; lia | change (Z.of_nat 4) with 4; unfold seg_spec.RC_N; lia |].
intros k Hk. change (Z.of_nat 4) with 4. rewrite HN. apply fnd_le4_byte; [exact Hv | exact Hk].
Qed.

(* ---------- the name of c->seg[i] ---------- *)
Lemma fnd_seg_name : forall (rd : reader) c bs rc i, sa_bytes rd c bs -> seg_spec.rconf_enc rc bs ->
(i < length (SegModel.rc_seg rc))%nat ->
exists sx, sa_bytes rd (c + 356 * Z.of_nat i) (sx ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) sx /\
seg_spec.zs sx = SegModel.rs_name (SegModel.r_seg rc i) /\ ~ In 0 (SegModel.rs_name (SegModel.r_seg rc i)) /\
(length sx < 16)%nat.
Proof.
intros rd c bs rc i HB HE Hi. destruct (seg_query_facts.sq_rconf_len rc bs HE) as [L LS].
destruct (seg_query_facts.sq_rseg rc bs i HE Hi) as (_ & (HL & Hlt & HN & HF) & _).
rewrite seg_query_facts.sq_fld_fld in HL, HF by lia. rewrite Nat.add_0_r in HL, HF.
remember (SegModel.rs_name (SegModel.r_seg rc i)) as s eqn:Es.
remember (seg_spec.fld (356 * i) 16 bs) as g eqn:Eg.
exists (firstn (length s) g).
assert (G : firstn (S (length s)) g = firstn (length s) g ++ [nth (length s) g seg_spec.ZERO])
  by (apply seg_query_facts.sq_firstn_S; lia).
unfold seg_spec.zs in HF. rewrite firstn_map, G, map_app in HF. cbn [map] in HF.
apply app_inj_tail in HF as [H1 H2].
assert (Z0 : nth (length s) g seg_spec.ZERO = Z_to_bv 8 0)
  by (apply seg_query_facts.sq_byte_eq; rewrite H2; reflexivity).
split; [|split; [|split; [exact H1 | split; [exact HN|]]]].
- rewrite <- Z0, <- G. subst g. unfold seg_spec.fld. rewrite firstn_firstn, Nat.min_l by lia.
  replace (c + 356 * Z.of_nat i) with (c + Z.of_nat (356 * i)) by lia.
  apply fnd_bytes_sub; [exact HB | lia].
- apply seg_query_facts.sq_zs_nul. unfold seg_spec.zs. rewrite H1. exact HN.
- rewrite length_firstn. lia.
Qed.

(* ---------- the state record: S' = S is a set_fs of S (sa_noalloc's last conjunct) ---------- *)
Lemma fnd_set_fs_self : forall S : astate, S = set_fs (st_fs S) S.
Proof. intros []. reflexivity. Qed.
