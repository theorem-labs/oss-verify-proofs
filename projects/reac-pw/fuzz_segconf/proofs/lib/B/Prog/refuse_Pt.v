(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: number's walk on the ASan build of plugin-hostd/fuzz_command, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v and ACam.v (a walk segment, the side-stack frame's release): from strtol's return (0x8e534) to number's return, the four paths of number's tests (the word's first byte, the end pointer's byte, the range of the value) and the release of the class-0 frame. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/numberB.v, with its module paths and module names changed; 753 of its 818 lines of code are new or changed and 366 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3...): the second half
   of refuse's image-B prefix walk, from RB_TEXT (0x894e4, snprintf's return) through the vsnprintf call, checks 4
   and 5 and the n_refusals store, to the release (0x89544), where RB_REL_stmt takes over. A sub-lane of
   a sub-lane (the image-B refuse walk lane, the image-B G3 walk owner), 2026-10-30.

   proves no function (kind: segment lemma of refuse's image-B walk): `rbp_txt : RBP_TXT_stmt ...`, the statement
   of lib/B/Prog/refuse_Pk.v, which a sub-lane takes as a hypothesis. ADAPTED from plugin-hostd/fuzz_command
   lib/B/Prog/check_reply_s4.v (a printf wrapper call and the FP state after it), numberB.v / numberR.v (token runs,
   the cut to the release) at origin/ossv/recipes 501c0d516c69, and from this lane base's lib/B/Prog/refuse_H.v head
   (the image-B refuse walk lane: the region and keep tactics), re-derived on image B's code (refuse.fuzz_segconf.asan-ubsan.s
   lines 125-149).

   THE RUNS (image-B pcs):
   - 0x894e4 .. 0x894fc (plain run; the frame's shadow byte 4 and its word [32, 40) writable, everything else
     read-only): `li a1,199; bltu a1,a0` decided by atom 1304 = k = |T1| <= 108 (rf_T1); `sb zero,4(s8)`; ap =
     s0 + 8 = sp - 40 stored at frame word 32. It stops at UBSan trap T4 (0x894fc `bltu ~dst, k`, `not` has no
     range): split, the taken side refuted by rbt_T4 (dst = c + 0x2e88 + 200 n < 2 ^ 47, k <= 108).
   - 0x89500 .. 0x89518 (plain run, every region read-only; nothing is stored): a3 = ap read back, a0 = dst + k,
     a1 = 200 - k, a2 = fmt; `jal wrapper_vsnprintf`. The call: refuse_Ps.rbs_aj_vsnprintf_atSF (row 5 at
     FR_seg 0x10000 gotw, window SEG_VSN_K) with the destination [dst + k, dst + 200) in the slot of the block c
     (off the image), the five spilled va words at sp - 40 .. sp - 8, FFR at the format and the caller's arguments.
     The call returns at the FP state fx1 (fxrel fx fx1); the rest is rbp_tail at fx1, lifted by
     srr_apost_baseF_lift.
   - 0x8951c .. 0x89540 (token run over the c block, rb_SH; the frame and its shadow read-only, the n_refusals
     cell writable): check 4 (0x8951c `lb` of n_refusals' shadow, 0x89520 `bnez`) and check 5 (0x89530, 0x89534)
     decided by the block's tokens; UBSan trap T5 (0x8952c `blt n + 1, n`) decided by the executor itself (the
     `lw` value is atom 35 in [0, 7], the `addiw` value atom 35 + 1); `sw` stores n + 1. It stops at the shadow
     store 0x89540.
   - 0x89540 .. 0x89544 (plain run; the frame's shadow byte 4 writable again): `sb a0,4(s8)` (0xf8).
   - 0x89544 = RB_REL: rb_canon_ok to ss_rel0, then RB_REL_stmt (REL) with SegModel.refuse's record, built by
     refuse_Pf.rbf_rconf_refuse from the slot (T1 from the first snprintf, the vsnprintf text after it), c->refused
     + 1 and n_refusals + 1.
   The trap sites of this segment: T4 0x894fc (split, refuted), T5 0x8952c (decided); the unimp 0x895e0 and the
   slow paths 0x89618 .. 0x8963c are never reached. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YI16 YM05 YN2j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot PaCall PaCallRun PaArt PaArtOwn PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs RtPFupoison RtPFPf RtPFShared RtPFCmd RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c refuse_E refuse_K refuse_f refuse_pft refuse_Pk.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require refuse_Ps refuse_Pf refuse_Pg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== the states of the segment ============================== *)
(* the state with the region (base atom b, low offset lo) given the write window [wlo, whi) *)
Definition rbt_win (ss : sstate) (b : nat) (lo wlo whi : Z) : sstate :=
let i := rbp_find (ss_mem ss) b lo 0 in
mkSS (ss_pc ss) (ss_regs ss) (list_upd (ss_mem ss) i (set_window (nth i (ss_mem ss) got_regionP) wlo whi))
  (ss_resv ss) (ss_facts ss).
(* RB_TEXT with k's range, the frame's shadow byte 4 and its word [32, 40) writable, the stack and the block's
   cells read-only *)
Definition ss_t1 : sstate := Eval vm_compute in
rbt_win (rbt_win (rbt_win (rbt_win (add_atom ss_txt 1304 (mkAF 0 108 0)) 1041 0 4 5) 1028 32 32 40) 2 (-144) (-144) (-144))
  10 13512 13516 13516.
(* the plain run stops at UBSan trap T4 (0x894fc) *)
Definition ss_t2 : sstate := Eval vm_compute in fst (sym_runN_pi seg_tpi FUEL ss_t1).
Definition rbt_T4_a : sv := SAlu ALU_XOR (SAlu ALU_ADD (SOff 10 11912) (SMd M_MUL (SOff 35 0) (SLit 200))) (SLit (-1)).
Definition rbt_T4_b : sv := SOff 1304 0.
(* T4 not taken, every window closed: the run to the vsnprintf call stores nothing *)
Definition ss_t3 : sstate := Eval vm_compute in
rbt_win (rbt_win (add_cond ss_t2 (mkAC (neg_bc BC_LTU) rbt_T4_a rbt_T4_b)) 1041 0 4 4) 1028 32 32 32.
Definition ss_t4 : sstate := Eval vm_compute in fst (sym_runN_pi seg_tpi FUEL ss_t3).
(* the regions the call keeps: the frame's shadow, its words [0, 32) and [40, 64), the saved registers, the block's
   n_refusals / refused cells (the ap word [32, 40) is not read again) *)
Definition rbt_keep : list nat := [0; 1; 3; 4; 5]%nat.
(* 0x8951c: vsnprintf's return; the clobbered registers are the fresh atoms 1320 .. 1335 *)
Definition ss_vret : sstate := Eval vm_compute in
set_facts (ss_after_call ss_t4 (pick (ss_mem ss_t4) rbt_keep) 1320 RB_VRET) rbp_fx.

(* ============================== arithmetic of the trap and the call's registers ============================== *)
(* UBSan trap T4 (0x894fc `bltu ~dst, k`, dst = c + 0x2e88 + 200 n): never taken *)
Lemma rbt_T4 : forall E c nr k, ew E 10 = Z_to_bv 64 c -> ew E 35 = Z_to_bv 64 nr -> ew E 1304 = Z_to_bv 64 k ->
0 <= c -> c + 16616 <= 2 ^ 47 -> 0 <= nr <= 7 -> 0 <= k <= 108 ->
(U E rbt_T4_a <? U E rbt_T4_b) = false.
Proof.
intros E c nr k H10 H35 Hk Hc0 Hc1 Hnr Hk0.
unfold rbt_T4_a, rbt_T4_b. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E 10 c 11912 H10) by lia. rewrite U_SMd, (U_atom E 35 nr H35) by lia. rewrite U_SLit, U_SLit.
cbn [zmd_raw]. rewrite (U_atom E 1304 k Hk) by lia.
unfold zcanon, M64. rewrite (Z.mod_small 200) by lia. rewrite (Z.mod_small (nr * 200)) by lia.
rewrite (Z.mod_small (c + 11912 + nr * 200)) by lia.
change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite lxor_allones by lia.
rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.
(* a0 at the call: dst + k *)
Lemma rbt_den_d : forall E c nr k, ew E 10 = Z_to_bv 64 c -> ew E 35 = Z_to_bv 64 nr -> ew E 1304 = Z_to_bv 64 k ->
0 <= c -> c + 16616 <= 2 ^ 47 -> 0 <= nr <= 7 -> 0 <= k <= 108 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 11912) (SMd M_MUL (SOff 35 0) (SLit 200))) (SOff 1304 0)) =
Z_to_bv 64 (c + 11912 + 200 * nr + k).
Proof.
intros E c nr k H10 H35 Hk Hc0 Hc1 Hnr Hk0.
rewrite <- (Z_to_bv_bv_unsigned _ (sv_denot E _)). f_equal. fold (U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 11912) (SMd M_MUL (SOff 35 0) (SLit 200))) (SOff 1304 0))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E 10 c 11912 H10) by lia. rewrite U_SMd, (U_atom E 35 nr H35) by lia. rewrite U_SLit.
cbn [zmd_raw]. rewrite (U_atom E 1304 k Hk) by lia.
unfold zcanon, M64. rewrite (Z.mod_small 200) by lia. rewrite (Z.mod_small (nr * 200)) by lia.
rewrite (Z.mod_small (c + 11912 + nr * 200)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* a1 at the call: 200 - k *)
Lemma rbt_den_n : forall E k, ew E 1304 = Z_to_bv 64 k -> 0 <= k <= 108 ->
sv_denot E (SAlu ALU_SUB (SLit 0) (SOff 1304 (-200))) = Z_to_bv 64 (200 - k).
Proof.
intros E k Hk Hk0.
rewrite <- (Z_to_bv_bv_unsigned _ (sv_denot E _)). f_equal. fold (U E (SAlu ALU_SUB (SLit 0) (SOff 1304 (-200)))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_SOff, Hk, unsigned_lit_small by lia.
unfold zcanon, M64. rewrite (Z.mod_small 0) by lia.
rewrite <- (Z.mod_unique (k + -200) (2 ^ 64) (-1) (k - 200 + 2 ^ 64)) by lia.
rewrite <- (Z.mod_unique (0 - (k - 200 + 2 ^ 64)) (2 ^ 64) (-1) (200 - k)) by lia. reflexivity.
Qed.

(* ============================== the footprint and its cells ============================== *)
Lemma rbt_inFP_nref : forall c rcs a, (length (rc_refusal rcs) < 8)%nat -> c + 13512 <= a < c + 13516 ->
inFP (refuse_W c rcs) a.
Proof.
intros c rcs a Hn Ha. exists (c + seg_spec.RC_NREF, c + seg_spec.RC_NREF + 4). split.
- unfold refuse_W. rewrite (proj2 (Nat.ltb_lt _ _) Hn). cbn [app In]. right. right. left. reflexivity.
- cbn [fst snd]. unfold seg_spec.RC_NREF. lia.
Qed.
Lemma rbt_inFP_slot : forall c rcs a, (length (rc_refusal rcs) < 8)%nat ->
seg_spec.refusal_addr c (length (rc_refusal rcs)) <= a < seg_spec.refusal_addr c (length (rc_refusal rcs)) + 200 ->
inFP (refuse_W c rcs) a.
Proof.
intros c rcs a Hn Ha. exists (seg_spec.refusal_addr c (length (rc_refusal rcs)),
  seg_spec.refusal_addr c (length (rc_refusal rcs)) + seg_spec.RC_REFUSAL_LEN). split.
- unfold refuse_W. rewrite (proj2 (Nat.ltb_lt _ _) Hn). cbn [app In]. right. left. reflexivity.
- cbn [fst snd]. unfold seg_spec.RC_REFUSAL_LEN. lia.
Qed.
Lemma rbt_inFP_cases : forall c rcs a, inFP (refuse_W c rcs) a ->
(c + 13516 <= a < c + 13520) \/
(seg_spec.refusal_addr c (length (rc_refusal rcs)) <= a < seg_spec.refusal_addr c (length (rc_refusal rcs)) + 200) \/
(c + 13512 <= a < c + 13516).
Proof.
intros c rcs a ((lo, hi) & Hin & Ha). cbn [fst snd] in Ha. unfold refuse_W in Hin.
apply in_app_or in Hin. destruct Hin as [Hin | Hin].
- destruct Hin as [Hq | []]. injection Hq as <- <-. left. unfold seg_spec.RC_REFUSED in Ha. lia.
- destruct (length (rc_refusal rcs) <? 8)%nat; [|destruct Hin].
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <-.
  + right. left. unfold seg_spec.RC_REFUSAL_LEN in Ha. lia.
  + right. right. unfold seg_spec.RC_NREF in Ha. lia.
Qed.

(* ============================== region and keep lemmas (refuse_H.v's, under the rbt_ prefix) ============================== *)
Lemma rbt_le_byte_mod : forall v k, YG0f.le_byte v 4 k = YG0f.le_byte (v mod 2 ^ 32) 4 k.
Proof. intros v k. unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma rbt_chunk4_aval : forall {fx : YK11.FPState} segs E H (m : word -> option byte) base off e (v : Z),
YP09.chunk_ok segs E (mrestrict H m) base (YP09.mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v ->
rd32 (aview segs H m) (base + off) v.
Proof.
intros fx segs E H m base off e v Hc He k Hk.
destruct (Hc (Z.of_nat k) ltac:(unfold YP09.c_len; cbn [YP09.c_val YP09.cv_len]; lia)) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as <-.
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. rewrite He, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64).
unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). change 256 with (2 ^ 8).
apply Z.bits_inj'. intros j Hj.
destruct (Z_lt_le_dec j 8) as [Hj8|Hj8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma rbt_region_aval4 : forall {fx : YK11.FPState} segs E H (m : word -> option byte) n b cs lo hi wlo whi od e v,
region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 4 e)) cs -> sv_denot E e = Z_to_bv 64 v ->
rd32 (aview segs H m) (b + od) v.
Proof.
intros fx segs E H m n b cs lo hi wlo whi od e v (_ & _ & _ & Hcs) Hn Hc He.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (rbt_chunk4_aval segs E H m b od e v Hck He).
Qed.
(* an 8-byte chunk of a region read back as a word *)
Lemma rbt_region_word : forall {fx : YK11.FPState} segs E H (m : word -> option byte) n b cs lo hi wlo whi od e,
region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 8 e)) cs ->
rdword (aview segs H m) (b + od) = Some (bv_unsigned (sv_denot E e)).
Proof.
intros fx segs E H m n b cs lo hi wlo whi od e (_ & _ & _ & Hcs) Hn Hc.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
apply rdword_of_val_mem; [|exact Hr]. change 8%nat with (N.to_nat 8).
apply (val_of_chunk_ok segs E (mrestrict H m) b od 8 e); [exact Hck | symmetry; apply Z_to_bv_bv_unsigned | cbn; lia | cbn; lia].
Qed.
Ltac rbt_in_tac := let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; vm_compute in Hx; repeat (destruct Hx as [<- | Hx]; [vm_compute; repeat (first [left; reflexivity | right]) |]); destruct Hx.

(* ============================== the caller's arguments and the literal at another reader ============================== *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* sa_va_args at a reader R1, string by string *)
Lemma rbt_va_move : forall (R0 R1 : YG0f.reader) Wl (P : Z -> Z -> Prop) (vs : list word) (xs : list SegModel.arg),
sa_va_args R0 Wl vs xs -> refuse_va_locs P vs xs ->
(forall q s, P q (Z.of_nat (length s) + 1) -> sa_apart_all q (seg_spec.cstr_span q s) Wl ->
  sa_str R0 q s -> sa_addr R0 q (Z.of_nat (length s) + 1) ->
  sa_str R1 q s /\ sa_addr R1 q (Z.of_nat (length s) + 1)) ->
sa_va_args R1 Wl vs xs.
Proof.
intros R0 R1 Wl P vs xs. revert vs. induction xs as [|x xs IH]; intros vs Hva Hloc Hmv.
- destruct vs; exact I.
- destruct vs as [|v vs]; [destruct x; exact (False_ind _ Hva)|].
  cbn [sa_va_args] in Hva |- *. destruct Hva as [Hx Hva].
  destruct x as [s|z]; cbn [refuse_va_locs] in Hloc.
  + destruct Hloc as [Hq Hloc]. cbn [sa_va_arg] in Hx |- *. destruct Hx as (Hnz & Hstr & Hlen & Hadr & Hap).
    destruct (Hmv (bv_unsigned v) s Hq Hap Hstr Hadr) as [Hs1 Ha1].
    split; [|exact (IH vs Hva Hloc Hmv)].
    split; [exact Hnz|]. split; [exact Hs1|]. split; [exact Hlen|]. split; [exact Ha1 | exact Hap].
  + split; [exact Hx | exact (IH vs Hva Hloc Hmv)].
Qed.
(* the arguments refuse's callers give satisfy refuse_f.v's rf_argok *)
Lemma rbt_argok : forall (rd : YG0f.reader) Wl (vs : list word) xs, sa_va_args rd Wl vs xs ->
(forall a v, rd a = Some v -> 0 <= v < 256) -> Forall rf_argok xs.
Proof.
intros rd Wl vs xs. revert vs. induction xs as [|x xs IH]; intros vs Hva Hb; [constructor|].
destruct vs as [|v vs]; [exact (False_ind _ Hva)|].
cbn [sa_va_args] in Hva. destruct Hva as [Hx Hva]. constructor; [|exact (IH vs Hva Hb)].
destruct x as [s|z]; cbn [sa_va_arg] in Hx; cbn [rf_argok].
- destruct Hx as (_ & Hstr & Hlen & _). pose proof (refuse_Pf.rbf_str_bytes rd _ s Hstr Hb) as Hs.
  destruct Hstr as ((_ & Hn0) & _). split; [exact Hn0|]. split; [|exact Hlen].
  apply Forall_forall. intros y Hy. pose proof (proj1 (Forall_forall _ _) Hs y Hy) as Hy'. cbv beta in Hy'. lia.
- destruct Hx as [Hz _]. exact Hz.
Qed.
Lemma rbt_locs_mono : forall (P P' : Z -> Z -> Prop) (vs : list word) xs,
(forall q n, P q n -> P' q n) -> refuse_va_locs P vs xs -> refuse_va_locs P' vs xs.
Proof.
intros P P' vs xs HP. revert vs. induction xs as [|x xs IH]; intros vs H; [destruct vs; exact I|].
destruct vs as [|v vs]; [destruct x; exact (False_ind _ H)|].
destruct x as [s|z]; cbn [refuse_va_locs] in H |- *.
- destruct H as [H1 H2]. split; [exact (HP _ _ H1) | exact (IH vs H2)].
- exact (IH vs H).
Qed.
(* an image literal at a reader that agrees on its bytes and NUL (its slack is the image's, sa_romtail) *)
Lemma rbt_lit_move : forall segs B H (mem' : word -> option byte) (rd : YG0f.reader) a s,
sa_lit segs B rd a s -> (forall x, a <= x <= a + Z.of_nat (length s) -> aview segs H mem' x = rd x) ->
sa_lit segs B (aview segs H mem') a s.
Proof.
intros segs B H mem' rd a s (H0 & ((Hz & Hn0) & _) & Hp & Hrt & Hi) K.
split; [exact H0|]. split; [|exact (conj Hp (conj Hrt Hi))].
split; [split; [|exact Hn0] | exact (sa_tail_of_romtail segs H mem' _ Hrt)].
intros i Hi'. rewrite length_app in Hi'. cbn [length] in Hi'. rewrite K by lia.
apply Hz. rewrite length_app. cbn [length]. lia.
Qed.
(* sn_len of the text vsnprintf writes at n = 200 - k *)
Lemma rbt_sn_len : forall k (T : list Z), 0 <= k <= 108 ->
sn_len (200 - k - 1) T = Z.of_nat (length (firstn (Z.to_nat (199 - k)) T)) + 1 /\
Z.of_nat (length (firstn (Z.to_nat (199 - k)) T)) <= 199 - k /\
sn_bytes (200 - k - 1) T = firstn (Z.to_nat (199 - k)) T ++ [0].
Proof.
intros k T Hk. replace (200 - k - 1) with (199 - k) by lia. unfold sn_len, sn_bytes.
rewrite length_app, length_firstn. cbn [length]. split; [lia|]. split; [lia | reflexivity].
Qed.
End h.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* a region over bytes a call left unchanged, whose write window is present after the call *)
Lemma rbt_region_kept_pres : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
(* the shadow knowledge of the token run: c's block, 16616 addressable bytes in application memory *)
Lemma rbt_shok : forall E H mem c, bv_unsigned (ew E 10) = c -> ew E 32 = Z_to_bv 64 SB ->
range_addressable (aview SEGS H mem) SHADOW_OFF c 16616 -> in_app c 16616 -> 0 <= c -> c + 16616 <= 2 ^ 47 ->
sh_ok SEGS (SOff 32 0) rb_SH E (mrestrict H mem).
Proof.
intros E H mem c Uc E32 HRA Happ Hc0 Hc1.
assert (UB : U E (SOff 32 0) = SHADOW_OFF) by (rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity).
assert (Uc' : U E (SOff 10 0) = c) by (rewrite U_SOff, Uc, Z.add_0_r; apply zcanon_id; unfold M64; lia).
unfold sh_ok, rb_SH. apply Forall_cons; [|apply Forall_nil]. split; cbn [she_m she_lo she_hi].
- rewrite Z.add_0_r, Z.sub_0_r, Uc'. eapply (obl_of_range SEGS _ _ E (SOff 32 0) _ 16616 c 16616 HRA UB); lia.
- intros a Ha. cbn [she_m she_lo she_hi Z.min Z.max] in Ha. rewrite Uc' in Ha. rewrite UB.
  revert Happ Ha. clear. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL. intros. lia.
Qed.

Variable B : asyms.
Variables (STK RLO RHI : Z) (lit : list Z -> Z) (gotw guard : Z) (cr : list (Z * Z)).
(* row 5, the vsnprintf wrapper at its trampoline (RtPFSeg.v), at every FP state *)
Hypothesis VSNP : forall fx0 : YK11.FPState, @seg_avsnprintf_realizes fx0 rc SEGS B 0x10000 kImgEnd cr
  (SIGMA SS___interceptor_trampoline_vsnprintf) gotw guard.
(* FFR: segconf's printf family renders refuse's formats at SegModel's text (refuse_pft.v) *)
Hypothesis FFR : ffr_family SEGS B gotw (FR_seg 0x10000 gotw).
(* the release (refuse_K.v), at every FP state *)
Hypothesis REL : forall fx0 : YK11.FPState, RB_REL_stmt (fx := fx0) B.
Hypothesis LAWS : AR_laws SEGS B.
(* refuse's 19 formats are image literals below the GOT word *)
Hypothesis FMTS : forall fmt, In fmt REFUSE_ALL_FMTS ->
  0x10000 <= lit fmt /\ lit fmt + Z.of_nat (length fmt) + 1 <= gotw.
(* the stack-protector cells are image words *)
Hypothesis GOTW : 0x10000 <= gotw /\ gotw + 8 <= kImgEnd /\ 0x10000 <= guard /\ guard + 8 <= kImgEnd.
(* row 5's read-only words are image ranges *)
Hypothesis CRP : Forall (fun r => 0x10000 <= fst r /\ 0 <= snd r /\ fst r + snd r <= kImgEnd) cr.

(* ============================== 0x8951c .. the release (at any FP state) ============================== *)
Section t. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
(* vsnprintf's return to the release: checks 4 and 5, trap T5, n_refusals + 1, the shadow byte 4, then REL. The
   record at the release is the caller's: rcs2 holds for every reader that agrees with the return's on the block
   but n_refusals and holds n + 1 there (the main proof builds it from the two printf texts). *)
Lemma rbp_tail : forall ly S W (regs : bvmap 5 word) mem md ch c rcs rcs2 ms md2 S2 fpos Ev,
afn_pre SEGS B STK ly S W regs mem md ch -> 160 + 16 + 3 * ESTACK <= STK ->
getr regs 10 = w64 c -> sa_heap B ly S c seg_spec.SEG_C_SIZE -> (length (rc_refusal rcs) < 8)%nat ->
img_env VAL A_LIM Ev ->
st_ok_pi SEGS VAL Ev ss_vret (restrict (w_H W) ms) ->
ajournal SEGS B STK (spZ regs) (refuse_W c rcs) ly S W mem md [(0, fpos)] ly S2 W (ms_mem ms) md2 0 ->
frames S2 = (0, fpos) :: frames S -> ablocks B ly S2 = ablocks B ly S -> (exists f0, S2 = set_fs f0 S) ->
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ev n = getr regs r) ->
ew Ev 32 = Z_to_bv 64 SB -> ew Ev 33 = Z_to_bv 64 (rsp1 (spZ regs)) ->
ew Ev 35 = Z_to_bv 64 (Z.of_nat (length (rc_refusal rcs))) ->
ew Ev 1028 = Z_to_bv 64 (frame_addr ly 0 fpos) -> ew Ev 1040 = Z_to_bv 64 (flag_addr ly 0 fpos) ->
ew Ev 1041 = Z_to_bv 64 (SB + frame_addr ly 0 fpos / 8) ->
(forall rd' : YG0f.reader,
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> ~ (seg_spec.RC_NREF <= i < seg_spec.RC_NREF + 4) ->
    rd' (c + i) = rdW W (ms_mem ms) (c + i)) ->
  rd32 rd' (c + seg_spec.RC_NREF) (Z.of_nat (length (rc_refusal rcs)) + 1) -> sa_rconf rd' c rcs2) ->
SRr SEGS W (mkCfg ms md2) (RB_POST B STK regs ly S W mem md c rcs rcs2).
Proof.
intros ly S W regs mem md ch c rcs rcs2 ms md2 S2 fpos Ev HPRE HSTK H10 HHEAP Hn8 HEI HS HJ Hfrs2 Eab HS2f AGR
  E32 E33 E35 E1028 E1040 E1041 HREC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (proj1 HJ) as HAR2.
pose proof HHEAP as (bc & mc & Hbin & Hb1 & Hb2).
assert (HbinS2 : In (bc, mc) (ablocks B ly S2)) by (rewrite Eab; exact Hbin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR2 HbinS2) as (Hbc16 & Hbc4096 & Hbcceil & Hbcapp & Hbcpres & _ & Hmc).
pose proof (req_size_pos0 mc ltac:(lia)) as [Hmc0 Hmcr].
change seg_spec.SEG_C_SIZE with 16616 in Hb2.
set (F := frame_addr ly 0 fpos) in *.
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 0) with 64 in HF4096, HFceil, HFapp.
assert (Hn7 : Z.of_nat (length (rc_refusal rcs)) <= 7) by lia.
assert (HF8 : F / 8 <= 2 ^ 44 - 8) by (apply Z.div_le_upper_bound; lia).
assert (HF80 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (U10 : bv_unsigned (ew Ev 10) = c)
  by (rewrite (AGR 10%nat 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
assert (U1041 : bv_unsigned (ew Ev 1041) = SB + F / 8) by (rewrite E1041; apply unsigned_lit_small; unfold SB; lia).
assert (U1028 : bv_unsigned (ew Ev 1028) = F) by (rewrite E1028; apply unsigned_lit_small; lia).
assert (Hcapp : in_app c 16616) by (apply (in_app_sub bc (req_size mc)); [exact Hbcapp | lia | lia | lia]).
(* the token run's shadow knowledge at the return *)
pose proof (rbt_shok Ev (w_H W) (ms_mem ms) c U10 E32
  (range_addressable_of_block SEGS B LAWS ly S2 W (ms_mem ms) md2 bc mc c 16616 HAR2 HbinS2 ltac:(lia) ltac:(lia))
  Hcapp ltac:(lia) ltac:(lia)) as SHOK.
(* n_refusals' cell writable for the `sw` *)
rbp_rewin HS 10%nat 13512 13512 13516
  ltac:(let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; rewrite U10; apply (apresent_writable SEGS);
        apply (proj1 (Hbcpres (c + o) ltac:(lia)))).
(* 0x8951c .. 0x89540: the token run (checks 4 and 5, trap T5, the `sw`) *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bcx ?fr0 ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bcx fr0 lyx own) end.
  do 4 (apply awr_ok_cons_ro; [cbn; lia|]).
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 10%nat c); [reflexivity | exact U10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. left. split; [apply rbt_inFP_nref; [exact Hn8 | lia]|].
    exists bc, mc. split; [exact HbinS2 | lia]. }
  apply awr_ok_nil. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => c + 13512 <= a < c + 13516) HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U10, ?U1041, ?U1028 in Hrr; lia |]);
  destruct Hin)) as UN1.
cbv beta in UN1. clear HF HFr HG.
(* the frame's shadow byte 4 writable for the `sb` *)
pose proof (proj1 HJ) as HAR3.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR3 Hfin2) as (_ & _ & _ & HFSp3).
change (fs_frame_bytes 0 / 8) with 8 in HFSp3. fold F in HFSp3.
rbp_rewin HS 1041%nat 0 4 5
  ltac:(let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; rewrite U1041; apply (apresent_writable SEGS);
        replace (SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr, SB, SHADOW_OFF; lia);
        apply (proj1 (HFSp3 o ltac:(lia)))).
(* 0x89540 .. 0x89544: the plain run (`sb a0,4(s8)`) *)
paj_run_to_shc RUNTOP HS HJ RB_REL.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bcx ?fr0 ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bcx fr0 lyx own) end.
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 1041%nat (SB + F / 8)); [reflexivity | exact U1041 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists 0, fpos. split; [left; reflexivity|]. right. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd].
    change (fs_frame_bytes 0) with 64. change (64 / 8) with 8. fold F. unfold SB in Ha. lia. }
  do 3 (apply awr_ok_cons_ro; [cbn; lia|]).
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 10%nat c); [reflexivity | exact U10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. left. split; [apply rbt_inFP_nref; [exact Hn8 | lia]|].
    exists bc, mc. split; [exact HbinS2 | lia]. }
  apply awr_ok_nil. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => (SB + F / 8 + 4 <= a < SB + F / 8 + 5) \/ (c + 13512 <= a < c + 13516)) HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U10, ?U1041, ?U1028 in Hrr; lia |]);
  destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
(* n_refusals + 1 at the release, from the store's chunk *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  let i := eval vm_compute in (rbp_find (ss_mem ssx) 10%nat 13512 0) in
  let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) i r HS ltac:(vm_compute; reflexivity)) as HRcnt;
  cbn [ms_mem restrict] in HRcnt end.
pose proof (rbt_region_aval4 SEGS Ev (w_H W) _ 10 c _ _ _ _ _ 13512 (SOff 35 1)
  (Z.of_nat (length (rc_refusal rcs)) + 1) HRcnt U10 ltac:(left; reflexivity)
  ltac:(cbn [sv_denot]; rewrite E35, unsigned_lit_small by lia; reflexivity)) as VNR.
assert (HRC2 : sa_rconf (rdW W (ms_mem msF)) c rcs2).
{ apply HREC.
  - intros i Hi Hni. change seg_spec.SEG_C_SIZE with 16616 in Hi. change seg_spec.RC_NREF with 13512 in Hni.
    assert (Hx : ~ ((SB + F / 8 + 4 <= c + i < SB + F / 8 + 5) \/ (c + 13512 <= c + i < c + 13516))).
    { revert Hcapp HF8 HF80 Hi Hni. clear. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB. intros. lia. }
    rewrite (UN2 (c + i) ltac:(lia) Hx). apply (UN1 (c + i)); lia.
  - change seg_spec.RC_NREF with 13512. exact VNR. }
(* 0x89544: the canonical release state, then REL *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
pose proof (rb_canon_ok Hh Ex ssx msx 1200 RB_REL_CLOB rel_regions RB_REL rel_atoms [] [] HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(rbt_in_tac) (fun x (Hx : In x []) => match Hx with end)
  (fun x (Hx : In x []) => match Hx with end)) as HS3 end.
lazymatch type of HS3 with st_ok_pi _ _ _ ?x _ => replace x with ss_rel0 in HS3 by (vm_compute; reflexivity) end.
lazymatch type of HS3 with st_ok_pi _ _ ?Evx _ _ => set (Evr := Evx) in HS3 end.
assert (HEIr : img_env VAL A_LIM Evr) by (subst Evr; apply img_env_havoc_hi; [assumption | unfold A_LIM; lia]).
assert (AGr : forall n, (n < 1200)%nat -> ew Evr n = ew Ev n)
  by (intros n Hn; subst Evr; rewrite ew_havoc_old by lia; repeat (rewrite ew_ewset_other by lia); reflexivity).
refine (REL fx STK ly S W regs mem md ch c rcs rcs2 msF _ S2 fpos Evr HPRE ltac:(lia) HHEAP HEIr HS3
  HJ Hfrs2 Eab HS2f _ _ _ _ _ _ HRC2).
- intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite AGr by lia. apply AGR. exact Hn.
- rewrite AGr by lia. exact E32.
- rewrite AGr by lia. exact E33.
- rewrite AGr by lia. exact E1028.
- rewrite AGr by lia. exact E1040.
- rewrite AGr by lia. exact E1041.
Qed.
End t.

(* ============================== RB_TEXT .. the vsnprintf call, then rbp_tail at the returned FP state ============================== *)
Section m. Context {fx : YK11.FPState}.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).
(* a caller's string in a live block or a live side-stack frame of an AR state, at a reader m that agrees with R0 on
   its bytes and NUL (and, in a frame, on its shadow): its sa_str (slack by AR_block_word_vis or the frame's bytes) and
   sa_addr (the block's shadow by AR, the frame's kept) *)
Lemma rbt_str_at : forall ly S (W : world SEGS) m md q s (R0 : YG0f.reader),
AR SEGS B ly S W m md ->
((exists b n, In (b, n) (ablocks B ly S) /\ b <= q /\ q + (Z.of_nat (length s) + 1) <= b + n) \/
 ((exists cid pos, In (cid, pos) (frames S) /\ 0 <= cid /\ frame_addr ly cid pos <= q /\
    q + (Z.of_nat (length s) + 1) <= frame_addr ly cid pos + fs_frame_bytes cid) /\
  (forall x, q <= x < q + (Z.of_nat (length s) + 1) ->
    rdW W m (shadow_of_addr SHADOW_OFF x) = R0 (shadow_of_addr SHADOW_OFF x)))) ->
sa_str R0 q s -> sa_addr R0 q (Z.of_nat (length s) + 1) ->
(forall x, q <= x <= q + Z.of_nat (length s) -> rdW W m x = R0 x) ->
sa_str (rdW W m) q s /\ sa_addr (rdW W m) q (Z.of_nat (length s) + 1).
Proof.
intros ly S W m md q s R0 HAR Hloc ((Hz & Hn0) & _) (A0 & A1 & A2 & A3 & A4) K.
assert (Hstr : sa_strz (rdW W m) q s).
{ split; [|exact Hn0]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite K by lia. apply Hz. rewrite length_app. cbn [length]. lia. }
destruct Hloc as [(b & n & Hin & H1 & H2) | ((cid & pos & Hin & Hcid & H1 & H2) & KS)].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos0 n ltac:(lia)) as [_ Hreq].
  split; [split; [exact Hstr|] |].
  + intros x Hx. apply (AR_block_word_vis SEGS B ly S W m md b n (q + Z.of_nat (length s)) x HAR Hin); lia.
  + split; [exact A0|]. split; [exact A1|]. split; [exact A2|].
    split; [exact (range_addressable_of_block SEGS B LAWS ly S W m md b n q (Z.of_nat (length s) + 1) HAR Hin ltac:(lia) ltac:(lia))|].
    intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W m md b n q (Z.of_nat (length s) + 1) HAR Hin ltac:(lia) ltac:(lia) ltac:(lia)).
- destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hin) as (Hal & _ & Hpr & _).
  assert (Hfs : fs_frame_bytes cid = 8 * (8 * 2 ^ cid)) by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by lia; lia).
  split; [split; [exact Hstr|] |].
  + intros x Hx.
    pose proof (Z.div_mod (q + Z.of_nat (length s)) 8 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (q + Z.of_nat (length s)) 8 ltac:(lia)) as D2.
    pose proof (Z.div_mod (frame_addr ly cid pos) 32 ltac:(lia)) as D3. rewrite Hal, Z.add_0_r in D3.
    apply (aview_some_of_apresent SEGS). apply (proj1 (Hpr x ltac:(lia))).
  + split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
    * intros x Hx. destruct (A3 x Hx) as (sv & Hs & Hok). exists sv. rewrite (KS x Hx). split; [exact Hs | exact Hok].
    * intros _. exact (shadow_hull_vis_of_frame SEGS B LAWS ly S W m md cid pos q (Z.of_nat (length s) + 1) HAR Hin H1 H2 ltac:(lia)).
Qed.

Theorem rbp_txt : RBP_TXT_stmt B STK RLO RHI lit gotw guard.
Proof.
unfold RBP_TXT_stmt.
intros ly S W regs mem md ch c line fp ln rcs f args ms md2 S2 fpos Ev
  HCX HSTK Hn8 HEI HS HJ Hfrs2 Eab HS2f AGR E32 E33 E35 E36 E1028 E1040 E1041 E1304 HSSP HKEEP HR32 HZS.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof GOTW as (Hg1 & Hg2 & Hg3 & Hg4).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HCX as (HPRE & HROD & H10 & Hc64 & H11 & Hl64 & H12 & Hfp64 & HRPRE & HROOM & HEV).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HRPRE as (Hc0 & Hc16 & HRC & HHEAP & HADDR & HREF1 & Hln & Hlne & Hinf & Hck & Hfp0 & Hfpl & HLIT & HVA
  & HLOCS & HFRM & HSSP0 & HLITS).
pose proof (proj1 HJ) as HAR2.
pose proof HHEAP as (bc & mc & Hbin & Hb1 & Hb2).
assert (HbinS2 : In (bc, mc) (ablocks B ly S2)) by (rewrite Eab; exact Hbin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR2 HbinS2) as (Hbc16 & Hbc4096 & Hbcceil & Hbcapp & Hbcpres & _ & Hmc).
pose proof (req_size_pos0 mc ltac:(lia)) as [Hmc0 Hmcr].
pose proof (blk_off_imgP B ly S2 W (ms_mem ms) md2 bc mc HAR2 HbinS2) as Hbcimg. unfold off_img in Hbcimg.
change seg_spec.SEG_C_SIZE with 16616 in Hb2.
set (sp0 := spZ regs) in *.
destruct (rsp1_facts sp0 Hal16) as (Hs1al & Hs1).
set (F := frame_addr ly 0 fpos) in *.
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFal & _ & HFpres & HFSpres).
change (fs_frame_bytes 0) with 64 in HF4096, HFceil, HFapp, HFpres, HFSpres. change (64 / 8) with 8 in HFSpres.
pose proof (sep_block_frame SEGS B LAWS ly S2 W (ms_mem ms) md2 bc mc 0 fpos HAR2 HbinS2 Hfin2) as HWF.
unfold zdisjoint in HWF. cbn [fst snd] in HWF. change (fs_frame_bytes 0) with 64 in HWF.
pose proof (frm_off_imgP B ly S2 W (ms_mem ms) md2 0 fpos HAR2 Hfin2) as HFimg. unfold off_img in HFimg.
change (fs_frame_bytes 0) with 64 in HFimg.
assert (HF8 : F / 8 <= 2 ^ 44 - 8) by (apply Z.div_le_upper_bound; lia).
assert (HF80 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (Hn7 : Z.of_nat (length (rc_refusal rcs)) <= 7) by lia.
pose proof HRC as (bs & Hbs & Henc).
destruct (rf_T1 rcs bs ln Henc Hln) as (HTl & HTn & HTb).
fold (rbp_T1 rcs ln) in HTl, HTn, HTb.
set (k := Z.of_nat (length (rbp_T1 rcs ln))) in *.
assert (Hkd : k = Z.of_nat (length (rbp_T1 rcs ln))) by reflexivity.
assert (Hk : 0 <= k <= 108) by lia.
assert (Hslot : seg_spec.refusal_addr c (length (rc_refusal rcs)) = c + 11912 + 200 * Z.of_nat (length (rc_refusal rcs)))
  by (unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN; lia).
change seg_spec.SEG_C_SIZE with 16616 in HKEEP. change seg_spec.RC_REFUSED with 13516 in HKEEP.
change seg_spec.RC_REFUSAL with 11912 in HKEEP.
assert (Hcapp : in_app c 16616) by (apply (in_app_sub bc (req_size mc)); [exact Hbcapp | lia | lia | lia]).
pose proof Hcapp as Hcapp'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hcapp'.
assert (E10 : ew Ev 10 = Z_to_bv 64 c) by (rewrite (AGR 10%nat 10%bv eq_refl), H10; reflexivity).
assert (U10 : bv_unsigned (ew Ev 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew Ev 2) = sp0) by (rewrite (AGR 2%nat 2%bv eq_refl); reflexivity).
assert (U33 : bv_unsigned (ew Ev 33) = rsp1 sp0) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U1041 : bv_unsigned (ew Ev 1041) = SB + F / 8) by (rewrite E1041; apply unsigned_lit_small; unfold SB; lia).
assert (U1028 : bv_unsigned (ew Ev 1028) = F) by (rewrite E1028; apply unsigned_lit_small; lia).
pose proof (rbt_sn_len k (SegModel.fmt f args) Hk) as (Hsl & Hsl2 & Hsb).
pose proof (rbt_argok (rdW W mem) _ _ args HVA (fun a v E => sa_aview_rng _ _ _ _ _ E)) as HOK.
destruct (rf_txt f args (or_intror (or_intror Hinf)) Hck HOK) as (HFn & HFb & HFl).
(* the five spilled va words at sp - 40 .. sp - 8, at RB_TEXT *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  let i := eval vm_compute in (rbp_find (ss_mem ssx) 2%nat (-144) 0) in
  let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) i r HS ltac:(vm_compute; reflexivity)) as HRstk;
  cbn [ms_mem restrict] in HRstk end.
Ltac rbt_cin := cbn [In]; repeat (first [left; reflexivity | right]).
pose proof (rbt_region_word SEGS Ev (w_H W) (ms_mem ms) 2 sp0 _ _ _ _ _ (-40) (SOff 13 0) HRstk U2 ltac:(rbt_cin)) as W13.
pose proof (rbt_region_word SEGS Ev (w_H W) (ms_mem ms) 2 sp0 _ _ _ _ _ (-32) (SOff 14 0) HRstk U2 ltac:(rbt_cin)) as W14.
pose proof (rbt_region_word SEGS Ev (w_H W) (ms_mem ms) 2 sp0 _ _ _ _ _ (-24) (SOff 15 0) HRstk U2 ltac:(rbt_cin)) as W15.
pose proof (rbt_region_word SEGS Ev (w_H W) (ms_mem ms) 2 sp0 _ _ _ _ _ (-16) (SOff 16 0) HRstk U2 ltac:(rbt_cin)) as W16.
pose proof (rbt_region_word SEGS Ev (w_H W) (ms_mem ms) 2 sp0 _ _ _ _ _ (-8) (SOff 17 0) HRstk U2 ltac:(rbt_cin)) as W17.
cbn [sv_denot] in W13, W14, W15, W16, W17.
rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned in W13, W14, W15, W16, W17.
rewrite (AGR 13%nat 13%bv eq_refl) in W13. rewrite (AGR 14%nat 14%bv eq_refl) in W14.
rewrite (AGR 15%nat 15%bv eq_refl) in W15. rewrite (AGR 16%nat 16%bv eq_refl) in W16.
rewrite (AGR 17%nat 17%bv eq_refl) in W17.
clear HRstk.
(* k's range, then the windows of the first run *)
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 1304 (mkAF 0 108 0) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E1304, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia))
  as HS3; clear HS; rename HS3 into HS end.
rbp_norm HS.
rbp_rewin HS 1041%nat 0 4 5
  ltac:(let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; rewrite U1041; apply (apresent_writable SEGS);
        replace (SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr, SB, SHADOW_OFF; lia);
        apply (proj1 (HFSpres o ltac:(lia)))).
rbp_rewin HS 1028%nat 32 32 40
  ltac:(let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; rewrite U1028; apply (apresent_writable SEGS);
        apply (proj1 (HFpres (F + o) ltac:(lia)))).
rbp_rewin HS 2%nat (-144) (-144) (-144) ltac:(let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; lia).
rbp_rewin HS 10%nat 13512 13516 13516 ltac:(let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; lia).
(* 0x894e4 .. 0x894fc: the plain run to UBSan trap T4 *)
paj_run_sh RUNP HS HJ.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fpx ?b0 ?bcx ?fr0 ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fpx b0 bcx fr0 lyx own) end.
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 1041%nat (SB + F / 8)); [reflexivity | exact U1041 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists 0, fpos. split; [left; reflexivity|]. right. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd].
    change (fs_frame_bytes 0) with 64. change (64 / 8) with 8. fold F. unfold SB in Ha. lia. }
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 1028%nat F); [reflexivity | exact U1028 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists 0, fpos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    change (fs_frame_bytes 0) with 64. fold F. lia. }
  do 3 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (SB + F / 8 + 4 <= a < SB + F / 8 + 5) \/ (F + 32 <= a < F + 40)) HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U10, ?U1041, ?U1028, ?U2 in Hrr; lia |]);
  destruct Hin)) as UNa.
cbv beta in UNa. clear HF HFr HG.
(* UBSan trap T4 (0x894fc): not taken *)
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ltu_U in Hc.
  pose proof (rbt_T4 Ev c (Z.of_nat (length (rc_refusal rcs))) k E10 E35 E1304 ltac:(lia) ltac:(lia) ltac:(lia) Hk) as T4.
  unfold rbt_T4_a, rbt_T4_b in T4. rewrite T4 in Hc. discriminate Hc. }
clear Hc.
rbp_rewin HS 1041%nat 0 4 4 ltac:(let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; lia).
rbp_rewin HS 1028%nat 32 32 32 ltac:(let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; lia).
(* 0x89500 .. 0x89518: the plain run to the vsnprintf call (no store) *)
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fpx ?b0 ?bcx ?fr0 ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fpx b0 bcx fr0 lyx own) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into msT end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
  destruct Hin)) as UNb.
cbv beta in UNb. clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdv := dM) in *; clearbody mdv end.
(* what the runs kept: everything but the frame's shadow byte 4 and its word [32, 40) *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 5) -> ~ (F + 32 <= a < F + 40) ->
  rdW W (ms_mem msT) a = rdW W (ms_mem ms) a).
{ intros a Ha H1 H2. rewrite (UNb a Ha (fun X => X)). apply UNa; [exact Ha | tauto]. }
clear UNa UNb.
(* the registers at the call *)
Ltac rbt_reg HS r Hr :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?msx) =>
  pose proof (st_ok_restrict_reg segs H E ss msx r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict] in Hr end.
prreg HS (1%bv : bv 5) Rg1. prreg HS (2%bv : bv 5) Rg2. prreg HS (3%bv : bv 5) Rg3. prreg HS (4%bv : bv 5) Rg4.
prreg HS (12%bv : bv 5) Rg12. prreg HS (13%bv : bv 5) Rg13.
rbt_reg HS (10%bv : bv 5) Rg10. rbt_reg HS (11%bv : bv 5) Rg11.
rewrite (rbt_den_d Ev c _ k E10 E35 E1304 ltac:(lia) ltac:(lia) ltac:(lia) Hk) in Rg10.
rewrite (rbt_den_n Ev k E1304 Hk) in Rg11.
rewrite U2 in Rg13.
assert (HspT : spZ (ms_regs msT) = sp0 + (rsp1 sp0 - sp0)) by (unfold spZ; rewrite Rg2, E33, unsigned_lit_small by lia; lia).
pose proof (proj1 HJ) as HART.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HART HbinS2) as (_ & _ & _ & _ & HbcpresT & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
(* the image bytes the contract names (journal clause 481: the footprint lies in the block c, off the image) *)
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  rdW W (ms_mem msT) a = rdW W mem a).
{ intros a Hi Ho He. pose proof (pa_img_range a Hi) as Hr. unfold kImgEnd in Hr.
  apply (J3 a Hi Ho He). apply fp_spares_closed.
  - intros Hz. destruct (rbt_inFP_cases c rcs 0 Hz) as [Q | [Q | Q]]; rewrite ?Hslot in Q; lia.
  - intros Hz. destruct (rbt_inFP_cases c rcs a Hz) as [Q | [Q | Q]]; rewrite ?Hslot in Q; lia. }
(* the bytes of the live blocks and the caller's frames, outside c->refused and the slot *)
assert (KEEPB : forall x, 0 <= x < 2 ^ 64 ->
  ((exists p n, In (p, n) (ablocks B ly S) /\ p <= x < p + req_size n) \/
   (exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid)) ->
  ~ (c + 13516 <= x < c + 13520) -> ~ (c + 11912 + 200 * Z.of_nat (length (rc_refusal rcs)) <= x <
     c + 11912 + 200 * Z.of_nat (length (rc_refusal rcs)) + 200) ->
  rdW W (ms_mem msT) x = rdW W mem x).
{ intros x Hx Hloc Hnr Hns. destruct (inFP_dec (refuse_W c rcs) x) as [Hin | Hnin].
  - destruct (rbt_inFP_cases c rcs x Hin) as [Q | [Q | Q]]; rewrite ?Hslot in Q; [lia | lia |].
    rewrite (KM x Hx) by (unfold SB; lia).
    replace x with (c + (x - c)) by lia. apply HKEEP; lia.
  - destruct Hloc as [(p & n & Hin & Hp) | (cid & pos & Hin & Hp)].
    + replace x with (p + (x - p)) by lia. apply (J2 p n (x - p)); [exact Hin | rewrite Eab; exact Hin | lia |].
      replace (p + (x - p)) with x by lia. exact Hnin.
    + apply (J4 cid pos x Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hnin]. }
(* the shadow of the caller's frames *)
assert (KEEPS : forall cid pos x, In (cid, pos) (frames S) ->
  shadow_addr (frame_addr ly cid pos) <= x < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
  rdW W (ms_mem msT) x = rdW W mem x).
{ intros cid pos x Hin Hx.
  assert (HinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hin).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR2 HinS2) as (Hf1 & Hf2 & _).
  assert (Hq1 : (frame_addr ly cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 44 - 8) by (apply Z.div_le_upper_bound; lia).
  pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)) as Hq0.
  assert (Hq2 : frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8 <= (frame_addr ly cid pos + fs_frame_bytes cid) / 8).
  { apply Z.div_le_lower_bound; [lia|].
    pose proof (Z.mul_div_le (frame_addr ly cid pos) 8 ltac:(lia)). pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)). lia. }
  apply (J4 cid pos x Hin); [right; unfold in_zr; cbn [fst snd]; lia|].
  intros Hz. destruct (rbt_inFP_cases c rcs x Hz) as [Q | [Q | Q]]; rewrite ?Hslot in Q;
  unfold shadow_addr, SHADOW_OFF in Hx; lia. }
(* the format literal, the read-only image view and the stack-protector cells at the call *)
assert (HLITT : sa_lit SEGS B (rdW W (ms_mem msT)) fp f).
{ apply (rbt_lit_move SEGS B (w_H W) (ms_mem msT) (rdW W mem) fp f HLIT).
  intros x Hx. pose proof HLIT as (_ & _ & _ & _ & Himg).
  destruct (Himg x ltac:(lia)) as (Hi & Ho & He). exact (KIMG x Hi Ho He). }
assert (HROM : RtDefs.rt_rom_view SEGS B W (ms_mem msT)).
{ intros a Hrom Ho He. unfold aerrno_cell in He.
  assert (Hi : in_img SEGS a) by (destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
  rewrite (KIMG a Hi Ho He). apply HROD; [left; exact Hrom | exact Ho | exact He]. }
assert (KIMG2 : forall a, 0x10000 <= a < kImgEnd -> rdW W (ms_mem msT) a = rdW W (ms_mem ms) a).
{ intros a Ha. unfold kImgEnd in Ha. apply KM; [lia | unfold SB; lia | lia]. }
assert (HGRD : aguard_ok SEGS W (ms_mem msT) gotw guard).
{ destruct HSSP as (G1 & g & G2). split.
  - rewrite (rdword_ext (rdW W (ms_mem ms)) (rdW W (ms_mem msT)) gotw); [exact G1|].
    intros j Hj. apply KIMG2. lia.
  - exists g. rewrite (rdword_ext (rdW W (ms_mem ms)) (rdW W (ms_mem msT)) guard); [exact G2|].
    intros j Hj. apply KIMG2. lia. }
(* the call's write set, snp_out at the window and the written part *)
set (d := c + 11912 + 200 * Z.of_nat (length (rc_refusal rcs)) + k) in *.
assert (Hdd : d = c + 11912 + 200 * Z.of_nat (length (rc_refusal rcs)) + k) by reflexivity.
set (rs := snp_out SEG_VSN_K (spZ (ms_regs msT)) d (sn_len (200 - k - 1) (SegModel.fmt f args))).
set (Wl := [(ly_stk_lo ly, sp0); (seg_spec.refusal_addr c (length (rc_refusal rcs)),
  seg_spec.refusal_addr c (length (rc_refusal rcs)) + seg_spec.RC_REFUSAL_LEN);
  (c + seg_spec.RC_REFUSED, c + seg_spec.RC_REFUSED + 4)]).
(* FFR at the format and the caller's arguments *)
assert (HFMT : refuse_pft.ffr_fmt SEGS B gotw (rdW W (ms_mem msT)) rs fp f).
{ destruct (FMTS f (refuse_Pf.rbf_fmt_in f Hinf)) as (Hf1 & Hf2). rewrite <- Hfpl in Hf1, Hf2.
  pose proof (Z.mod_pos_bound (- (fp + Z.of_nat (length f) + 1)) 8 ltac:(lia)) as Hm.
  eapply (refuse_Pf.rbf_ffr_fmt B); [exact HART | exact HLITT | lia | exact Hf2 | lia |].
  unfold rs, snp_out. rewrite HspT. unfold seg_spec.cstr_span.
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold SEG_VSN_K, kImgEnd in *; lia|].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold kImgEnd in *; lia | apply Forall_nil]. }
assert (HLOCS2 : refuse_va_locs (fun q n => sa_heap B ly S2 q n \/ sa_fframe ly S2 q n)
  [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] args).
{ refine (rbt_locs_mono _ _ _ _ _ HLOCS). intros q n [(b & m & Hin & H1 & H2) | (cid & pos & Hin & H0 & H1 & H2)].
  - left. exists b, m. rewrite Eab. exact (conj Hin (conj H1 H2)).
  - right. exists cid, pos. rewrite Hfrs2. exact (conj (or_intror Hin) (conj H0 (conj H1 H2))). }
assert (HAPART : refuse_Pf.rbf_args_apart rs [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] args).
{ apply (refuse_Pf.rbf_args_apart_of_va (rdW W mem) Wl rs _ args HVA).
  unfold rs, snp_out. rewrite HspT.
  unfold Wl.
  apply Forall_cons; [exists (ly_stk_lo ly, sp0); split; [left; reflexivity | cbn [fst snd]; unfold SEG_VSN_K; lia]|].
  apply Forall_cons; [|apply Forall_nil].
  exists (seg_spec.refusal_addr c (length (rc_refusal rcs)),
    seg_spec.refusal_addr c (length (rc_refusal rcs)) + seg_spec.RC_REFUSAL_LEN).
  split; [right; left; reflexivity | cbn [fst snd]; rewrite Hslot; unfold seg_spec.RC_REFUSAL_LEN; lia]. }
assert (HVAT : sa_va_args (rdW W (ms_mem msT)) Wl [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] args).
{ apply (rbt_va_move (rdW W mem) _ Wl _ _ args HVA HLOCS).
  intros q s Hq Hap Hstr Hadr. pose proof Hadr as (Hq0 & Hq1 & _).
  assert (Hspan : Z.of_nat (length s) + 1 <= seg_spec.cstr_span q s)
    by (unfold seg_spec.cstr_span; pose proof (Z.mod_pos_bound (- (q + Z.of_nat (length s) + 1)) 8 ltac:(lia)); lia).
  unfold sa_apart_all, Wl in Hap. apply Forall_cons_iff in Hap as [Ha1 Hap].
  apply Forall_cons_iff in Hap as [Ha2 Hap]. apply Forall_cons_iff in Hap as [Ha3 _].
  cbn [fst snd] in Ha1, Ha2, Ha3. rewrite Hslot in Ha2. unfold seg_spec.RC_REFUSAL_LEN, seg_spec.RC_REFUSED in Ha2, Ha3.
  apply (rbt_str_at ly S2 W (ms_mem msT) mdv q s (rdW W mem) HART); [| exact Hstr | exact Hadr |].
  - destruct Hq as [(b & m & Hin & H1 & H2) | (cid & pos & Hin & H0 & H1 & H2)].
    + left. exists b, m. rewrite Eab. exact (conj Hin (conj H1 H2)).
    + right. split; [exists cid, pos; rewrite Hfrs2; exact (conj (or_intror Hin) (conj H0 (conj H1 H2)))|].
      intros x Hx. apply (KEEPS cid pos); [exact Hin|].
      destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hin) as (Hal' & _).
      assert (Hfs : fs_frame_bytes cid = 8 * (8 * 2 ^ cid)) by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by lia; lia).
      assert (Hfs8 : fs_frame_bytes cid / 8 = 8 * 2 ^ cid) by (rewrite Hfs, Z.mul_comm, Z.div_mul by lia; reflexivity).
      pose proof (Z.div_mod (frame_addr ly cid pos) 32 ltac:(lia)) as D1. rewrite Hal', Z.add_0_r in D1.
      assert (Hf8 : frame_addr ly cid pos / 8 = 4 * (frame_addr ly cid pos / 32)).
      { rewrite D1 at 1. replace (32 * (frame_addr ly cid pos / 32)) with ((4 * (frame_addr ly cid pos / 32)) * 8) by lia.
        apply Z.div_mul. lia. }
      pose proof (Z.div_mod x 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D3.
      unfold shadow_of_addr, shadow_addr. rewrite Hfs8, Hf8. lia.
  - intros x Hx. apply KEEPB; [lia | | lia | lia].
    destruct Hq as [(b & m & Hin & H1 & H2) | (cid & pos & Hin & H0 & H1 & H2)].
    + left. exists b, m. split; [exact Hin|]. pose proof (req_size_pos0 m ltac:(lia)). lia.
    + right. exists cid, pos. split; [exact Hin | lia]. }
assert (HARGS : refuse_pft.ffr_args (rdW W (ms_mem msT)) rs
  (map (fun v : word => bv_unsigned v) [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17]) args).
{ apply (refuse_Pf.rbf_ffr_args_va W (ms_mem msT) Wl rs _ args HVAT).
  exact (refuse_Pf.rbf_args_place_of_locs B LAWS ly S2 W (ms_mem msT) mdv rs _ args HART HLOCS2 HAPART). }
(* the destination's slack word *)
pose proof (amem8_of_block SEGS B LAWS ly S2 W (ms_mem msT) mdv bc mc d (200 - k) HART HbinS2 ltac:(lia) ltac:(lia) ltac:(lia))
  as HAM8.
(* 0x89518: vsnprintf(dst + k, 200 - k, fmt, ap) *)
pmkst HS.
eapply SRr_bind.
{ apply (refuse_Ps.rbs_aj_vsnprintf_atSF (fx := fx) SEGS B LAWS Hsegs (FR_seg 0x10000 gotw) SEG_VSN_K gotw guard 0x10000
    kImgEnd cr (SIGMA SS___interceptor_trampoline_vsnprintf) (VSNP fx) ltac:(unfold SEG_VSN_K; lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(unfold kImgEnd; lia) CRP W (ms_regs msT) (ms_mem msT) STK sp0 (refuse_W c rcs) ly S W mem md
    [(0, fpos)] ly S2 mdv 0 d (200 - k) fp (sp0 - 40)
    (map (fun v : word => bv_unsigned v) [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17])
    (SegModel.fmt f args) (rsp1 sp0 - sp0) (Z_to_bv 64 (BASE + 18268)) HJ).
  - unfold w64. exact Rg10.
  - unfold w64. exact Rg11.
  - rewrite Rg12, (AGR 12%nat 12%bv eq_refl). exact H12.
  - unfold w64. rewrite Rg13. f_equal; lia.
  - lia.
  - lia.
  - lia.
  - exact HspT.
  - destruct Hs1 as [Hq|Hq]; rewrite Hq;
    [replace (sp0 - 160 - sp0) with (-160) by lia | replace (sp0 - 176 - sp0) with (-176) by lia]; reflexivity.
  - lia.
  - unfold SEG_VSN_K. lia.
  - rewrite Rg3, (AGR 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Rg4, (AGR 4%nat 4%bv eq_refl). exact Htp.
  - exact Rg1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split.
    + right. left. split; [apply rbt_inFP_slot; [exact Hn8 | rewrite Hslot; lia]|].
      exists bc, mc. split; [exact HbinS2 | lia].
    + unfold SEG_VSN_K. lia.
  - intros a Ha _ _. apply (apresent_writable SEGS). apply (proj1 (HbcpresT a ltac:(lia))).
  - unfold amem_range in HAM8 |- *. lia.
  - apply (range_addressable_of_block SEGS B LAWS ly S2 W (ms_mem msT) mdv bc mc); [exact HART | exact HbinS2 | lia | lia].
  - apply (shadow_hull_vis_of_block SEGS B LAWS ly S2 W (ms_mem msT) mdv bc mc); [exact HART | exact HbinS2 | lia | lia | lia].
  - unfold kImgEnd. lia.
  - unfold SEG_VSN_K, kImgEnd. lia.
  - exact HGRD.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros i Hi. cbn [length map] in Hi.
    destruct i as [|[|[|[|[|i]]]]]; [| | | | | lia]; cbn [nth map];
    match goal with |- rdword _ ?a = _ =>
      rewrite (rdword_ext (rdW W (ms_mem ms)) (rdW W (ms_mem msT)) a)
        by (let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply KM; [lia | unfold SB; lia | lia]) end;
    [replace (sp0 - 40 + 8 * Z.of_nat 0) with (sp0 + -40) by lia; exact W13
    |replace (sp0 - 40 + 8 * Z.of_nat 1) with (sp0 + -32) by lia; exact W14
    |replace (sp0 - 40 + 8 * Z.of_nat 2) with (sp0 + -24) by lia; exact W15
    |replace (sp0 - 40 + 8 * Z.of_nat 3) with (sp0 + -16) by lia; exact W16
    |replace (sp0 - 40 + 8 * Z.of_nat 4) with (sp0 + -8) by lia; exact W17].
  - lia.
  - cbn [length map]. lia.
  - cbn [length map]. unfold snp_out. rewrite HspT.
    apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold SEG_VSN_K; lia|].
    apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
  - exact (FFR _ _ fp f _ args (refuse_Pf.rbf_fmt_in f Hinf) Hck HFMT HARGS).
  - exact HFl.
  - exact HROM.
  - lia.
  - left. unfold SEG_VSN_K. lia.
  - cbn [length map]. lia.
  - exact HAM8.
  - exact HFRM. }
(* back at 0x8951c at the FP state fx1 the wrapper returns *)
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md3 & Hfx & -> & HJ3 & HP3 & H10r & HBY & HKP & HPR & HSM).
rewrite Hsb in HBY. rewrite Hsl in HBY, HKP.
(* the record at the release, from the two texts *)
assert (HREC : forall rd' : YG0f.reader,
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> ~ (seg_spec.RC_NREF <= i < seg_spec.RC_NREF + 4) ->
    rd' (c + i) = rdW W mem2 (c + i)) ->
  rd32 rd' (c + seg_spec.RC_NREF) (Z.of_nat (length (rc_refusal rcs)) + 1) ->
  sa_rconf rd' c (SegModel.refuse rcs ln f args)).
{ intros rd' Hk2 Hn32.
  change seg_spec.SEG_C_SIZE with 16616 in Hk2. change seg_spec.RC_NREF with 13512 in Hk2.
  assert (K2 : forall i, 0 <= i < 16616 -> ~ (13512 <= i < 13516) ->
    ~ (d <= c + i < d + (Z.of_nat (length (firstn (Z.to_nat (199 - k)) (SegModel.fmt f args))) + 1)) ->
    rd' (c + i) = rdW W (ms_mem msT) (c + i)).
  { intros i Hi Hni Hnd. rewrite (Hk2 i Hi Hni). apply HKP; [lia | exact Hnd | unfold SEG_VSN_K; lia]. }
  apply (refuse_Pf.rbf_rconf_refuse (rdW W mem) rd' c rcs ln f args HRC HREF1 Hn8 Hln Hinf Hck HOK).
  - intros i Hi Hr Hn Hs. change seg_spec.SEG_C_SIZE with 16616 in Hi. change seg_spec.RC_REFUSED with 13516 in Hr.
    change seg_spec.RC_NREF with 13512 in Hn. change seg_spec.RC_REFUSAL with 11912 in Hs.
    rewrite (K2 i Hi Hn) by lia. apply KEEPB; [lia | | lia | lia].
    left. exists bc, mc. split; [exact Hbin | lia].
  - rewrite (refuse_Pf.rbf_slot_text rcs ln f args Hln Hn8 bs Henc). fold (rbp_T1 rcs ln).
    change (Z.of_nat (length (rbp_T1 rcs ln))) with k.
    rewrite length_app. intros i Hi. change seg_spec.RC_REFUSAL with 11912 in Hi.
    rewrite (K2 i) by lia. rewrite (KM (c + i)) by (unfold SB; lia). apply HKEEP; lia.
  - change seg_spec.RC_REFUSED with 13516. intros j Hj.
    replace (c + 13516 + Z.of_nat j) with (c + (13516 + Z.of_nat j)) by lia.
    rewrite (K2 (13516 + Z.of_nat j)) by lia. rewrite (KM (c + (13516 + Z.of_nat j))) by (unfold SB; lia).
    replace (c + (13516 + Z.of_nat j)) with (c + seg_spec.RC_REFUSED + Z.of_nat j) by (unfold seg_spec.RC_REFUSED; lia).
    exact (HR32 j Hj).
  - exact Hn32.
  - rewrite (refuse_Pf.rbf_slot_text rcs ln f args Hln Hn8 bs Henc). fold (rbp_T1 rcs ln).
    change (Z.of_nat (length (rbp_T1 rcs ln))) with k.
    rewrite Hslot. intros j Hj. rewrite <- app_assoc in Hj |- *. rewrite length_app in Hj. cbn [length] in Hj.
    rewrite length_app in Hj. cbn [length] in Hj.
    replace (c + 11912 + 200 * Z.of_nat (length (rc_refusal rcs)) + Z.of_nat j)
      with (c + (11912 + 200 * Z.of_nat (length (rc_refusal rcs)) + Z.of_nat j)) by lia.
    destruct (Nat.lt_ge_cases j (length (rbp_T1 rcs ln))) as [Hjl | Hjl].
    + rewrite (K2 (11912 + 200 * Z.of_nat (length (rc_refusal rcs)) + Z.of_nat j)) by lia.
      rewrite (KM (c + (11912 + 200 * Z.of_nat (length (rc_refusal rcs)) + Z.of_nat j))) by (unfold SB; lia).
      rewrite app_nth1 by exact Hjl.
      pose proof (HZS j ltac:(rewrite length_app; cbn [length]; lia)) as Z1.
      rewrite app_nth1 in Z1 by exact Hjl. rewrite Hslot in Z1.
      replace (c + (11912 + 200 * Z.of_nat (length (rc_refusal rcs)) + Z.of_nat j))
        with (c + 11912 + 200 * Z.of_nat (length (rc_refusal rcs)) + Z.of_nat j) by lia. exact Z1.
    + rewrite (Hk2 (11912 + 200 * Z.of_nat (length (rc_refusal rcs)) + Z.of_nat j)) by lia.
      rewrite app_nth2 by exact Hjl.
      replace (c + (11912 + 200 * Z.of_nat (length (rc_refusal rcs)) + Z.of_nat j)) with (d + (Z.of_nat j - k)) by lia.
      rewrite (HBY (Z.of_nat j - k)) by lia. f_equal; f_equal; lia. }
(* re-seat at 0x8951c: the five kept regions, all read-only, outside the written part and the window *)
unfold RB_POST. refine (srr_apost_baseF_lift SEGS fx1 _ _ _ _ _ _ _ _ _ _ _ _ _ Hfx _).
jafter_call_keep_hi HS 1320%nat regs2 (mrestrict (w_H W) mem2) HP3 rbt_keep HS2.
match type of HS2 with ?A -> _ => assert (HQ : A); [|specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (rbt_region_kept_pres Ev (w_H W) _ _ 1041 (SB + F / 8)); [exact U1041 | | intros a Ha; lia].
    intros a Ha. unfold SB in Ha. apply HKP; [lia | lia | unfold SEG_VSN_K; lia].
  - apply (rbt_region_kept_pres Ev (w_H W) _ _ 1028 F); [exact U1028 | | intros a Ha; lia].
    intros a Ha. apply HKP; [lia | lia | unfold SEG_VSN_K; lia].
  - apply (rbt_region_kept_pres Ev (w_H W) _ _ 1028 F); [exact U1028 | | intros a Ha; lia].
    intros a Ha. apply HKP; [lia | lia | unfold SEG_VSN_K; lia].
  - apply (rbt_region_kept_pres Ev (w_H W) _ _ 2 sp0); [exact U2 | | intros a Ha; lia].
    intros a Ha. apply HKP; [lia | lia | unfold SEG_VSN_K; lia].
  - apply (rbt_region_kept_pres Ev (w_H W) _ _ 10 c); [exact U10 | | intros a Ha; lia].
    intros a Ha. apply HKP; [lia | lia | unfold SEG_VSN_K; lia]. }
rewrite <- restrict_mkst_fx in HS2.
pose proof (st_ok_pi_restrict_xfx fx fx1 SEGS VAL _ _ (w_H W) regs2 _ mem2 (seg_rom SEGS) HS2) as HS4.
clear HS2.
pose proof (st_ok_pi_facts_incl3 (fx := fx1) _ _ _ (f_atoms (ss_facts ss_vret)) [] (f_alias (ss_facts ss_vret)) HS4
  ltac:(rbt_in_tac) (fun x (Hx : In x []) => match Hx with end) ltac:(rbt_in_tac)) as HS5.
clear HS4. rbp_to HS5 ss_vret.
set (Ev2 := havoc Ev 1320 (map (getr regs2) CLOB)) in HS5.
assert (AG2 : forall n, (n < 1320)%nat -> ew Ev2 n = ew Ev n) by (intros n Hn; subst Ev2; apply ew_havoc_old; exact Hn).
refine (rbp_tail (fx := fx1) ly S W regs mem md ch c rcs (SegModel.refuse rcs ln f args)
  _ md3 S2 fpos Ev2 HPRE HSTK H10 HHEAP Hn8
  ltac:(subst Ev2; apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]) HS5 HJ3 Hfrs2 Eab HS2f _ _ _ _ _ _ _ HREC).
- intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite AG2 by lia. apply AGR. exact Hn.
- rewrite AG2 by lia. exact E32.
- rewrite AG2 by lia. exact E33.
- rewrite AG2 by lia. exact E35.
- rewrite AG2 by lia. exact E1028.
- rewrite AG2 by lia. exact E1040.
- rewrite AG2 by lia. exact E1041.
Qed.
End m.
End d.
