(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B/W_drain_dnrk.v, the memory bookkeeping that the image-B drain stages
   DROP / NEXT / REST and their shared memchr join (lib/B/W_drain_join.v, W_drain_next.v, W_drain_rest.v) need over
   lib/B/W_drain_cx.v's cut predicates.  Proves no function (kind: segment lemma).
   COPIED, with the prefix dtk_ renamed dnk_ and nothing else changed:
     dnk_low .. dnk_garr8_kept  from a working branch c0a3958f203
                                lib/B/W_drain_topb_bk.v:101-478 (the TOP tail lane's bookkeeping, itself ported from
                                lib/A/W_drain_epi.v; not yet on the drain base, so copied, not imported);
     dnk_nth_le_bytes, dnk_garr8_le, dnk_le_garr8, dnk_le8_bytes, dnk_le4_bytes, dnk_writable_view
                                from lib/B/W_gse_tail.v:65-185 (its gt_ lemmas), on the drain base.
   NEW here: dnk_entry_len, the entry field readers dnk_entry_skip / dnk_entry_buf / dnk_entry_used, and
   dnk_DMEM_call (DMEM survives a call whose writes all lie in its scratch below drain's frame: memchr's, at the
   memchr join 0x83990).
   ARx FORM (an internal work row): Section cx restates every lemma of Section c that reads AR over any allocator relation ARx
   (W_drain_cx_x.v's Section c header, plus HP0), with the suffix _x: the image-B twins of lib/A/W_drain_epi.v's
   Section cx (dend_*_x of DR_x slice B), where these lemmas came from; the journals are at W_contract_x.v's
   DRAIN_STK_x.  Section c is unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

(* lib/B/W_gse_tail.v:65-72 gt_nth_le_bytes *)
Lemma dnk_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Notation le8 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
Notation le4 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4.

(* lib/B/W_gse_tail.v:105-185: gt_garr8_le, gt_le_garr8, gt_le8_bytes, gt_le4_bytes, gt_writable_view *)
Lemma dnk_garr8_le : forall m a n z, garr8 SEGS m a (bzs (Z_to_le_bytes n z)) -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  val_mem SEGS m a n z.
Proof.
intros m a n z Hg Hz k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n z)))%nat) by (unfold bzs; rewrite length_map, length_Z_to_le_bytes; exact Hk).
destruct (Hg k Hl) as [Hv _]. specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv.
rewrite Hv. apply f_equal.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite map_nth, dnk_nth_le_bytes by exact Hk. unfold bz.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
Lemma dnk_le_garr8 : forall m a n z, val_mem SEGS m a n z -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  garr8 SEGS m a (bzs (Z_to_le_bytes n z)).
Proof.
intros m a n z Hv Hz j Hj. unfold bzs in Hj. rewrite length_map, length_Z_to_le_bytes in Hj.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hj).
rewrite map_nth, dnk_nth_le_bytes by exact Hj. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256.
split; [|apply Z.mod_pos_bound; lia].
intros k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
rewrite (Hv j Hj). f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
Lemma dnk_le8_bytes : forall z, 0 <= z < 2 ^ 64 -> le8 (Z_to_bv 64 z) = Z_to_le_bytes 8 z.
Proof.
intros z Hz. unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8, word_to_le_bytes.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma dnk_le4_bytes : forall z, 0 <= z < 2 ^ 64 -> le4 (Z_to_bv 64 z) = Z_to_le_bytes 4 z.
Proof.
intros z Hz. unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma dnk_writable_view : forall H (m : word -> option byte) a v, 0 <= a < 2 ^ 64 ->
aview SEGS H m a = Some v -> ~ in_rom SEGS a -> writable_at SEGS (mrestrict H m) a.
Proof.
intros H m a v Ha Hv Hn. unfold aview, mbyte in Hv. unfold writable_at, wview.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em; [discriminate|].
unfold seg_rom, memory_read in Hv.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [sg|] eqn:Ef; [|discriminate].
change (Z.of_N 1) with 1 in Ef. rewrite Ef.
destruct (seg_readable sg); [|discriminate].
destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi). rewrite unsigned_lit_small in Hlo, Hhi by lia.
destruct (seg_writable sg) eqn:Ew.
- destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) eqn:Eb;
  [discriminate|].
  exfalso. change (N.to_nat 1) with 1%nat in Hv. cbn [segment_read_bytes] in Hv. rewrite Eb in Hv. cbn in Hv.
  discriminate Hv.
- exfalso. apply Hn. exists sg. split; [exact Hin|]. split; [exact Ew | lia].
Qed.

(* NEW: the 56 bytes of a source_t, and its skip / buf / used fields read off them. *)
Lemma dnk_entry_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (bzs (entry_bytes e)) = 56%nat.
Proof.
intros e H1 H2. unfold bzs, entry_bytes. rewrite length_map, !length_app,
  !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4,
  !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8, H1, H2. reflexivity.
Qed.
Lemma dnk_entry_split : forall e, bzs (entry_bytes e) =
  bzs (le4 (Z_to_bv 64 (re_fd e)) ++ le4 (Z_to_bv 64 (re_eof e))) ++ bzs (le4 (Z_to_bv 64 (re_skip e))) ++
  bzs (re_pad1 e) ++ bzs (le8 (Z_to_bv 64 (re_buf e))) ++ bzs (le8 (Z_to_bv 64 (re_used e))) ++
  bzs (le8 (Z_to_bv 64 (re_cap e)) ++ le8 (Z_to_bv 64 (re_hp e)) ++ le4 (Z_to_bv 64 (re_nheld e)) ++ re_pad2 e).
Proof. intros e. unfold bzs, entry_bytes. rewrite !map_app, <- !app_assoc. reflexivity. Qed.
Lemma dnk_entry_fields : forall m SA e, garr8 SEGS m SA (bzs (entry_bytes e)) -> length (re_pad1 e) = 4%nat ->
  garr8 SEGS m SA (bzs (le4 (Z_to_bv 64 (re_fd e)) ++ le4 (Z_to_bv 64 (re_eof e)))) /\
  garr8 SEGS m (SA + 8) (bzs (le4 (Z_to_bv 64 (re_skip e)))) /\
  garr8 SEGS m (SA + 12) (bzs (re_pad1 e)) /\
  garr8 SEGS m (SA + 16) (bzs (le8 (Z_to_bv 64 (re_buf e)))) /\
  garr8 SEGS m (SA + 24) (bzs (le8 (Z_to_bv 64 (re_used e)))) /\
  garr8 SEGS m (SA + 32)
    (bzs (le8 (Z_to_bv 64 (re_cap e)) ++ le8 (Z_to_bv 64 (re_hp e)) ++ le4 (Z_to_bv 64 (re_nheld e)) ++ re_pad2 e)).
Proof.
intros m SA e Hg Hp1. rewrite dnk_entry_split in Hg.
apply (garr8_app SEGS) in Hg as [G1 Hg]. apply (garr8_app SEGS) in Hg as [G2 Hg].
apply (garr8_app SEGS) in Hg as [G3 Hg]. apply (garr8_app SEGS) in Hg as [G4 Hg].
apply (garr8_app SEGS) in Hg as [G5 G6].
assert (L4 : forall w, Z.of_nat (length (bzs (le4 w))) = 4)
  by (intros w; unfold bzs; rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4;
      reflexivity).
assert (L8 : forall w, Z.of_nat (length (bzs (le8 w))) = 8)
  by (intros w; unfold bzs; rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8;
      reflexivity).
assert (L44 : forall w v, Z.of_nat (length (bzs (le4 w ++ le4 v))) = 8)
  by (intros w v; unfold bzs; rewrite length_map, length_app,
      !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4; reflexivity).
assert (LP : Z.of_nat (length (bzs (re_pad1 e))) = 4) by (unfold bzs; rewrite length_map, Hp1; reflexivity).
rewrite L44 in G2, G3, G4, G5, G6. rewrite L4 in G3, G4, G5, G6. rewrite LP in G4, G5, G6.
rewrite L8 in G5, G6. rewrite L8 in G6.
replace (SA + 8 + 4) with (SA + 12) in G3, G4, G5, G6 by lia.
replace (SA + 12 + 4) with (SA + 16) in G4, G5, G6 by lia.
replace (SA + 16 + 8) with (SA + 24) in G5, G6 by lia.
replace (SA + 24 + 8) with (SA + 32) in G6 by lia.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5 | exact G6].
Qed.
Lemma dnk_entry_buf : forall m SA e, garr8 SEGS m SA (bzs (entry_bytes e)) -> length (re_pad1 e) = 4%nat ->
  0 <= re_buf e < 2 ^ 64 -> val_mem SEGS m (SA + 16) 8 (re_buf e).
Proof.
intros m SA e Hg Hp1 Hb. destruct (dnk_entry_fields m SA e Hg Hp1) as (_ & _ & _ & G & _).
rewrite (dnk_le8_bytes _ Hb) in G. apply (dnk_garr8_le m (SA + 16) 8 (re_buf e) G). cbn. lia.
Qed.
Lemma dnk_entry_used : forall m SA e, garr8 SEGS m SA (bzs (entry_bytes e)) -> length (re_pad1 e) = 4%nat ->
  0 <= re_used e < 2 ^ 64 -> val_mem SEGS m (SA + 24) 8 (re_used e).
Proof.
intros m SA e Hg Hp1 Hb. destruct (dnk_entry_fields m SA e Hg Hp1) as (_ & _ & _ & _ & G & _).
rewrite (dnk_le8_bytes _ Hb) in G. apply (dnk_garr8_le m (SA + 24) 8 (re_used e) G). cbn. lia.
Qed.
Lemma dnk_entry_skip : forall m SA e, garr8 SEGS m SA (bzs (entry_bytes e)) -> length (re_pad1 e) = 4%nat ->
  0 <= re_skip e < 2 ^ 32 -> val_mem SEGS m (SA + 8) 4 (re_skip e).
Proof.
intros m SA e Hg Hp1 Hb. destruct (dnk_entry_fields m SA e Hg Hp1) as (_ & G & _).
rewrite (dnk_le4_bytes (re_skip e) ltac:(lia)) in G. apply (dnk_garr8_le m (SA + 8) 4 (re_skip e) G). cbn. lia.
Qed.


Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c SEGS B MT MMAX CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.

Definition dnk_low (cx : dcx) (a : Z) : Prop := 0 <= a < alloc_ceiling /\ ~ (dxG cx <= a < dxG cx + ATABLE).

Lemma dnk_zall : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma dnk_zpw : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply dnk_zall; [exact H1 | lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | lia].
Qed.

Lemma dnk_errno_sep : forall a,
(rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_client RG <= a < rg_client RG + 4 \/
 rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/
 rg_send_dead RG <= a < rg_send_dead RG + 1 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8) ->
~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha He.
pose proof (dnk_zpw _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D2.
pose proof (dnk_zpw _ 3 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D3.
pose proof (dnk_zpw _ 4 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D4.
pose proof (dnk_zpw _ 5 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D5.
pose proof (dnk_zpw _ 6 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D6.
pose proof (dnk_zpw _ 7 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D7.
pose proof (dnk_zpw _ 8 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D8.
pose proof (dnk_zpw _ 9 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D9.
pose proof (dnk_zpw _ 10 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D10.
cbn [nth] in D2, D3, D4, D5, D6, D7, D8, D9, D10. unfold zdisj in *. cbn [fst snd] in *. lia.
Qed.

Lemma dnk_low_img : forall cx ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> 0x10000 <= a < IMG_TOP -> dnk_low cx a.
Proof.
intros cx ly S W mem md a HAR Hin Ha.
pose proof (blk_off_imgP B ly S W mem md _ _ HAR Hin) as Ho. red in Ho.
pose proof asan_consts as (C1 & _).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in Ho.
unfold dnk_low, ATABLE, IMG_TOP in *. lia.
Qed.

Lemma dnk_low_blk : forall cx ly S (W : world SEGS) mem md L p n a,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
In (p, n) L -> p <= a < p + req_size n ->
dnk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md L p n a HAR HP HL Ha.
assert (Hin : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); right; exact HL).
destruct (al_blocks SEGS B LAWS ly S W mem md p n HAR Hin) as (_ & H4 & Hc & _).
destruct (in_split _ _ HL) as (l1 & l2 & ->).
assert (HP2 : Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: (p, n) :: l1 ++ l2))
  by (eapply Permutation_trans; [exact HP | apply perm_skip; apply Permutation_sym, Permutation_middle]).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in Hd.
split; [unfold dnk_low, ATABLE; lia|].
intros He. apply (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin ltac:(lia)).
apply (proj1 (HG a ltac:(unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))).
Qed.

Lemma dnk_gs_ok : forall cx ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> rg_s RG <= a < rg_s RG + 4 * ASRC ->
dnk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md a HAR Hin Ha. pose proof HGSB as (G1 & G2 & _).
split; [apply (dnk_low_img cx ly S W mem md a HAR Hin); unfold ASRC in *; lia|].
apply dnk_errno_sep. left. exact Ha.
Qed.

Lemma dnk_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma dnk_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma dnk_fp_entry : forall cx ly S (W : world SEGS) mem md e L,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aentry_blks e) -> In b L) -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
dnk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md e L HAR HP HB HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (BLK : forall p n, In (p, n) (aentry_blks e) -> 0 <= n -> p <= a < p + n ->
  dnk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn Hpa. pose proof (req_size_pos n Hn) as (_ & Hrq).
  exact (dnk_low_blk cx ly S W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (BLK (re_buf e) (re_cap e)); [| lia | lia].
  unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. lia.
    * unfold bzs in Ha. rewrite length_map, dnk_key_ptrs_len in Ha. unfold re_nheld in Hk1.
      apply (BLK (re_hp e) (re_kh e)); [| lia | lia].
      unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (key_addr k) (Z.of_nat (length (key_text k)) + 1)); [| lia | lia].
    unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
    apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
Qed.

Lemma dnk_fp_list : forall cx ly S (W : world SEGS) mem md L LA l lines,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (alist_blks l) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) ->
alist_at B ly S W mem LA l lines -> rg_s RG <= LA -> LA + 16 <= rg_s RG + 4 * ASRC ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
dnk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md L LA l lines HAR HP HB HGin HL Hlo Hhi r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
assert (BLK : forall p n, In (p, n) (alist_blks l) -> 0 <= n -> p <= a < p + n ->
  dnk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn0 Hpa. pose proof (req_size_pos n Hn0) as (_ & Hrq).
  exact (dnk_low_blk cx ly S W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (dnk_gs_ok cx ly S W mem md a HAR HGin). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, dnk_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (BLK (hl_v l) (AREC * hl_cap l)); [| unfold AREC; lia | unfold hl_n, AREC in *; lia].
    unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (fst q) (Z.of_nat (length (snd q)) + 1)); [| lia | lia].
    unfold alist_blks. apply in_or_app. right.
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
Qed.

Lemma dnk_fp_src : forall cx ly S (W : world SEGS) mem md L h,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (asrc_blks h) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) -> (dxj cx < 4)%nat ->
asrc_at B ly S W mem (dHA RG cx) h ->
forall r, In r (asrc_fp (dHA RG cx) h) -> forall a, fst r <= a < snd r ->
dnk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md L h HAR HP HB HGin Hj HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; lia).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (dnk_gs_ok cx ly S W mem md a HAR HGin). lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
  apply (dnk_low_blk cx ly S W mem md L (hs_partial h) APARTIAL a HAR HP); [apply HB; left; reflexivity | lia].
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + exact (dnk_fp_list cx ly S W mem md L (dHA RG cx + 16) (hs_pending h) false HAR HP
      (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_introl Hb)))) HGin Hpend
      ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * exact (dnk_fp_list cx ly S W mem md L (dHA RG cx + 64) (hs_expected h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb)))))) HGin Hexp
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
    * exact (dnk_fp_list cx ly S W mem md L (dHA RG cx + 80) (hs_held h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hb)))))) HGin Hheld
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
Qed.

Lemma dnk_fp_out : forall cx ly S (W : world SEGS) mem md c O mx no cap out L,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aout_blks cap out) -> In b L) ->
aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
dnk_low cx a /\ (r <> (as_errno B, as_errno B + 4) -> ~ (as_errno B <= a < as_errno B + 4)).
Proof.
intros cx ly S W mem md c O mx no cap out L HAR HP HB HOUT r Hr a Ha.
assert (GT : In (dxG cx, ATABLE) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
assert (IMG : forall x, 0x10000 <= x < 0x5fc000 -> dnk_low cx x)
  by (intros x Hx; apply (dnk_low_img cx ly S W mem md x HAR GT); unfold IMG_TOP; exact Hx).
assert (GDR : forall x, inG (G_DR B RG) x -> 0x10000 <= x < 0x5fc000)
  by (intros x Hx; exact (pa_img_range _ (proj1 (HG x Hx)))).
pose proof (pa_obj_img 9 ltac:(lia)) as P9. rewrite HV9 in P9.
pose proof HSM as (Hs1 & Hs2). pose proof HSD as (Hd1 & Hd2). unfold IMG_TOP in Hs2, Hd2.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- split; [apply IMG; lia | intros _; apply dnk_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dnk_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dnk_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dnk_errno_sep; tauto].
- split; [apply IMG; lia | intros _; apply dnk_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dnk_errno_sep; tauto].
- split; [apply IMG; lia | intros _; apply dnk_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dnk_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros Hne; exfalso; apply Hne; reflexivity].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq).
  destruct (dnk_low_blk cx ly S W mem md L out cap a HAR HP) as [D1 D2];
    [apply HB; unfold aout_blks; rewrite Hc0; left; reflexivity | lia |].
  split; [exact D1 | intros _; exact D2].
Qed.

Lemma dnk_aout_ev : forall ly S (W : world SEGS) m m' c O mx no cap out ev,
aout_at B RG ly S W m c O mx no cap out ->
(forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
   ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W m W m' a) ->
(cap <> 0 -> forall a, out <= a < out + cap -> ~ (as_errno B <= a < as_errno B + 4)) ->
val_mem SEGS (arm W m') (as_errno B) 4 ev -> awr W m' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
aout_at B RG ly S W m' (CTL (ct_cl c) (ct_br c) (ct_dd c) (ct_ei c) ev) O mx no cap out.
Proof.
intros ly S W m m' c O mx no cap out ev
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
   H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HOB VE WE Hev.
assert (KC : forall a n, In (a, a + n) (aout_fp B RG cap out) -> forall x, a <= x < a + n ->
  ~ (as_errno B <= x < as_errno B + 4) -> abyte_kept W m W m' x)
  by (intros a n Hin x Hx Hne; exact (HK (a, a + n) Hin x Hx Hne)).
unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_max RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H1]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_max RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H2]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_nout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H3]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_nout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H4]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_capout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H5]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_capout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H6]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_out RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H7]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_out RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H8]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_client RG) 4); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H9]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_client RG) 4); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H10]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_client_broken RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H11]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_client_broken RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H12]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_dead RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H13]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_dead RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H14]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H15]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dnk_errno_sep; repeat (first [left; lia | right]); lia] | exact H16]|].
split; [exact VE|]. split; [exact WE|]. split; [exact Hev|].
do 6 (split; [assumption|]).
destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|].
exists junk. split; [exact Hj|].
apply (akept_garr8 W m); [|exact Hg].
intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
apply (KC out cap); [unfold aout_fp; rewrite Ec; repeat (first [left; reflexivity | right]) | lia | apply (HOB ltac:(lia)); lia].
Qed.

Lemma dnk_perm_mv : forall (x : Z * Z) l1 l2 l3 r, Permutation (x :: l1 ++ l2 ++ l3 ++ r) (l1 ++ l2 ++ l3 ++ x :: r).
Proof. intros. rewrite !app_assoc. apply Permutation_middle. Qed.

Lemma dnk_aentry_blks_in : forall ly S (W : world SEGS) m e,
aentry_okx B ly S W m e -> forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
intros ly S W m e (_ & _ & _ & _ & _ & _ & _ & _ & Hbuf & _ & Hhp & _ & _ & Hkeys) b Hb.
unfold aentry_blks in Hb.
destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [app] in Hb.
- destruct (Z.eqb_spec (re_hp e) 0) as [Hz0|Hz0]; cbn [app] in Hb.
  + apply in_map_iff in Hb as (k & <- & Hk).
    rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
  + destruct Hb as [<- | Hb].
    * destruct Hhp as [(Hz & _)|(_ & Hin & _)]; [lia | exact Hin].
    * apply in_map_iff in Hb as (k & <- & Hk).
      rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
- destruct Hb as [<- | Hb].
  + destruct Hbuf as [(Hc & _)|(_ & Hin & _)]; [lia | exact Hin].
  + destruct (Z.eqb_spec (re_hp e) 0) as [Hz0|Hz0]; cbn [app] in Hb.
    * apply in_map_iff in Hb as (k & <- & Hk).
      rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
    * destruct Hb as [<- | Hb].
      -- destruct Hhp as [(Hz & _)|(_ & Hin & _)]; [lia | exact Hin].
      -- apply in_map_iff in Hb as (k & <- & Hk).
         rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
Qed.

Lemma dnk_alist_blks_in : forall ly S (W : world SEGS) m LA l lines,
alist_at B ly S W m LA l lines -> forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
intros ly S W m LA l lines (_ & _ & _ & _ & _ & Hv & _ & _ & Hrecs) b Hb.
unfold alist_blks in Hb.
destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [app] in Hb.
- apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in Hrecs. exact (proj1 (Hrecs r Hr)).
- destruct Hb as [<- | Hb].
  + destruct Hv as [(Hc & _)|(_ & Hin & _)]; [lia | exact Hin].
  + apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in Hrecs. exact (proj1 (Hrecs r Hr)).
Qed.

Lemma dnk_asrc_blks_in : forall ly S (W : world SEGS) m HA h,
asrc_at B ly S W m HA h -> forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
intros ly S W m HA h HS b Hb.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & _ & _ & _ &
  Hexp & Hheld & _).
unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact Hpb|].
apply in_app_or in Hb as [Hb | Hb];
  [exact (dnk_alist_blks_in ly S W m (HA + 16) (hs_pending h) false Hpend b Hb)|].
apply in_app_or in Hb as [Hb | Hb];
  [exact (dnk_alist_blks_in ly S W m (HA + 64) (hs_expected h) true Hexp b Hb)
  |exact (dnk_alist_blks_in ly S W m (HA + 80) (hs_held h) true Hheld b Hb)].
Qed.

Lemma dnk_aout_blks_in : forall ly S (W : world SEGS) m c O mx no cap out,
aout_at B RG ly S W m c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
intros ly S W m c O mx no cap out HOUT b Hb.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & Hblk).
unfold aout_blks in Hb. destruct (cap =? 0) eqn:Hc0; [destruct Hb|]. destruct Hb as [<- | []].
destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia | exact Hin].
Qed.

Lemma dnk_aentry_okx_kept : forall ly S (W : world SEGS) m ly' S' (W' : world SEGS) m' e,
aentry_okx B ly S W m e -> akept W m W' m' (aentry_fp e) ->
(forall b, In b (aentry_blks e) -> In b (ablocks B ly' S')) -> aentry_okx B ly' S' W' m' e.
Proof.
intros ly S W m ly' S' W' m' e
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) HK HB.
do 8 (split; [assumption|]).
split.
{ destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|].
  split; [apply HB; unfold aentry_blks; rewrite Ec; left; reflexivity|].
  split; [exact Hj|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_buf e) (bzs (re_U e ++ re_junk e)))); [|exact Hx].
  unfold aentry_fp. rewrite Ec. left. reflexivity. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11|right].
  assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
  split; [exact Hz|].
  split; [apply HB; unfold aentry_blks; apply in_or_app; right; rewrite Ez; left; reflexivity|].
  split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_hp e) (bzs (key_ptrs (re_keys e))))); [|exact Hx].
  unfold aentry_fp. apply in_or_app. right. left. reflexivity. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [apply HB; unfold aentry_blks; apply in_or_app; right; apply in_or_app; right;
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
split; [|exact K3].
apply (akept_garr8 W m); [|exact K2].
intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
unfold aentry_fp. apply in_or_app. right. right.
apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.

Lemma dnk_garr8_kept : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof.
intros W m W' m' a l H KL. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (KL x Hx).
Qed.

(* NEW: the same footprint facts against ANY block X of the round (the dnk_ lemmas above take the relay's table
   (dxG cx, ATABLE)): REST moves the relay's buffer, so every other footprint byte must lie off it. *)
Definition dnx_low (X : Z * Z) (a : Z) : Prop := 0 <= a < alloc_ceiling /\ ~ (fst X <= a < fst X + req_size (snd X)).

Lemma dnx_low_img : forall X ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> In X (ablocks B ly S) -> 0x10000 <= a < IMG_TOP -> dnx_low X a.
Proof.
intros [xp xn] ly S W mem md a HAR Hin Ha.
pose proof (blk_off_imgP B ly S W mem md _ _ HAR Hin) as Ho. red in Ho.
pose proof asan_consts as (C1 & _).
unfold dnx_low, IMG_TOP in *. cbn [fst snd]. lia.
Qed.

Lemma dnx_low_blk : forall X ly S (W : world SEGS) mem md L p n a,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (X :: L) ->
In (p, n) L -> p <= a < p + req_size n ->
dnx_low X a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros X ly S W mem md L p n a HAR HP HL Ha.
assert (Hin : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); right; exact HL).
destruct (al_blocks SEGS B LAWS ly S W mem md p n HAR Hin) as (_ & H4 & Hc & _).
destruct (in_split _ _ HL) as (l1 & l2 & ->).
assert (HP2 : Permutation (ablocks B ly S) (X :: (p, n) :: l1 ++ l2))
  by (eapply Permutation_trans; [exact HP | apply perm_skip; apply Permutation_sym, Permutation_middle]).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
split; [unfold dnx_low; lia|].
intros He. apply (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin ltac:(lia)).
apply (proj1 (HG a ltac:(unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))).
Qed.

Lemma dnx_gs_ok : forall X ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> In X (ablocks B ly S) -> rg_s RG <= a < rg_s RG + 4 * ASRC ->
dnx_low X a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros X ly S W mem md a HAR Hin Ha. pose proof HGSB as (G1 & G2 & _).
split; [apply (dnx_low_img X ly S W mem md a HAR Hin); unfold ASRC in *; lia|].
apply dnk_errno_sep. left. exact Ha.
Qed.

Lemma dnx_fp_list : forall X ly S (W : world SEGS) mem md L LA l lines,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (X :: L) ->
(forall b, In b (alist_blks l) -> In b L) -> In X (ablocks B ly S) ->
alist_at B ly S W mem LA l lines -> rg_s RG <= LA -> LA + 16 <= rg_s RG + 4 * ASRC ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
dnx_low X a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros X ly S W mem md L LA l lines HAR HP HB HXin HL Hlo Hhi r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
assert (BLK : forall p n, In (p, n) (alist_blks l) -> 0 <= n -> p <= a < p + n ->
  dnx_low X a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn0 Hpa. pose proof (req_size_pos n Hn0) as (_ & Hrq).
  exact (dnx_low_blk X ly S W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (dnx_gs_ok X ly S W mem md a HAR HXin). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, dnk_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (BLK (hl_v l) (AREC * hl_cap l)); [| unfold AREC; lia | unfold hl_n, AREC in *; lia].
    unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (fst q) (Z.of_nat (length (snd q)) + 1)); [| lia | lia].
    unfold alist_blks. apply in_or_app. right.
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
Qed.

Lemma dnx_fp_src : forall X cx ly S (W : world SEGS) mem md L h,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (X :: L) ->
(forall b, In b (asrc_blks h) -> In b L) -> In X (ablocks B ly S) -> (dxj cx < 4)%nat ->
asrc_at B ly S W mem (dHA RG cx) h ->
forall r, In r (asrc_fp (dHA RG cx) h) -> forall a, fst r <= a < snd r ->
dnx_low X a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros X cx ly S W mem md L h HAR HP HB HXin Hj HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; lia).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (dnx_gs_ok X ly S W mem md a HAR HXin). lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
  apply (dnx_low_blk X ly S W mem md L (hs_partial h) APARTIAL a HAR HP); [apply HB; left; reflexivity | lia].
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + exact (dnx_fp_list X ly S W mem md L (dHA RG cx + 16) (hs_pending h) false HAR HP
      (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_introl Hb)))) HXin Hpend
      ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * exact (dnx_fp_list X ly S W mem md L (dHA RG cx + 64) (hs_expected h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb)))))) HXin Hexp
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
    * exact (dnx_fp_list X ly S W mem md L (dHA RG cx + 80) (hs_held h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hb)))))) HXin Hheld
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
Qed.

Local Ltac dnx_gdr := lazymatch goal with IMG : forall x, _ -> dnx_low ?X x, GDR : forall x, inG _ x -> _ |- _ =>
  apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ] end.
Lemma dnx_fp_out : forall X ly S (W : world SEGS) mem md c O mx no cap out L,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (X :: L) ->
(forall b, In b (aout_blks cap out) -> In b L) ->
aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> dnx_low X a.
Proof.
intros X ly S W mem md c O mx no cap out L HAR HP HB HOUT r Hr a Ha.
assert (GT : In X (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
assert (IMG : forall x, 0x10000 <= x < 0x5fc000 -> dnx_low X x)
  by (intros x Hx; apply (dnx_low_img X ly S W mem md x HAR GT); unfold IMG_TOP; exact Hx).
assert (GDR : forall x, inG (G_DR B RG) x -> 0x10000 <= x < 0x5fc000)
  by (intros x Hx; exact (pa_img_range _ (proj1 (HG x Hx)))).
pose proof (pa_obj_img 9 ltac:(lia)) as P9. rewrite HV9 in P9.
pose proof HSM as (Hs1 & Hs2). pose proof HSD as (Hd1 & Hd2). unfold IMG_TOP in Hs2, Hd2.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha;
  [ apply IMG; lia | dnx_gdr | dnx_gdr | dnx_gdr | apply IMG; lia | dnx_gdr | apply IMG; lia | dnx_gdr | dnx_gdr | ].
destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq).
exact (proj1 (dnx_low_blk X ly S W mem md L out cap a HAR HP ltac:(apply HB; unfold aout_blks; rewrite Hc0; left; reflexivity) ltac:(lia))).
Qed.

(* NEW: DMEM survives a call whose writes lie in [lo, sp) for lo above the allocator ceiling, with presence kept
   and its journal given at the new memory (aj_gx_entry_at's post): every byte DMEM reads is below the ceiling
   (blocks, image, globals: dnk_fp_entry / dnk_fp_src / dnk_fp_out / dnk_low_img) or in drain's own frame. *)
Lemma dnk_DMEM_call : forall cx ly1 S1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1 lo,
DBASE B MT MMAX RG cx ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k2 ->
alloc_ceiling <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < dsp0 cx - DRAIN_FRAME) -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM B RG cx ly1 S1 W1 m2 md2 k2 e1 h1 sg out1 ev1 sent LB1.
Proof.
intros cx ly1 S1 W1 m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1 lo HB HMEM HJ2 Hlo KL HP.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
pose proof HB as (Hafn & _ & _ & HSAlo & HSAhi & _ & _ & _ & _ & Hj & _).
pose proof Hafn as (_ & _ & _ & _ & _ & (_ & _ & Hcl & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hslo, Hshi.
assert (HDS : DRAIN_STK = 16880) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
pose proof asan_consts as (C1 & _).
assert (GT : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (HK : forall a, 0 <= a < alloc_ceiling \/ dsp0 cx - DRAIN_FRAME <= a < 2 ^ 64 -> abyte_kept W1 m1 W1 m2 a).
{ intros a Ha. split; [apply KL; lia|]. unfold arm. apply (writable_kept (w_H W1) m1 m2 a (HP a)). }
assert (HKL : forall a, dnk_low cx a -> abyte_kept W1 m1 W1 m2 a) by (intros a (Ha & _); apply HK; left; exact Ha).
assert (HVMF : forall a v, dsp0 cx - DRAIN_FRAME <= a -> a + 8 <= dsp0 cx ->
  val_mem SEGS (arm W1 m1) a 8 v -> val_mem SEGS (arm W1 m2) a 8 v).
{ intros a v H1 H2 Hv. apply (akept_vm W1 m1); [|exact Hv]. intros x Hx. apply HK. right. lia. }
assert (HVMG : forall a v, rg_s RG <= a -> a + 4 <= rg_s RG + 4 * ASRC ->
  val_mem SEGS (arm W1 m1) a 4 v -> val_mem SEGS (arm W1 m2) a 4 v).
{ intros a v H1 H2 Hv. apply (akept_vm W1 m1); [|exact Hv]. intros x Hx. cbn in Hx.
  apply HKL. exact (proj1 (dnk_gs_ok cx ly1 S1 W1 m1 md1 x HAR GT ltac:(lia))). }
assert (HBIN : forall b, In b (aentry_blks e1) \/ In b (asrc_blks h1) \/ In b (aout_blks (drain_b_c.ds_ocap sg) out1) ->
  In b (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx)).
{ intros b [Hb | [Hb | Hb]]; apply in_or_app; [left; exact Hb | right; apply in_or_app; left; exact Hb |].
  right; apply in_or_app; right; apply in_or_app; left; exact Hb. }
split; [exact HJ2|].
split.
{ intros a Ha. pose proof Ha as (sg0 & Hsg & _ & Hr).
  pose proof (pa_img_range a (ex_intro _ sg0 (conj Hsg Hr))) as Hai.
  rewrite (KL a ltac:(lia) ltac:(lia)). exact (Hrom a Ha). }
split; [intros a Ha1 Ha2 Ha3 Ha4; apply HP; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  repeat match type of HFR with _ /\ _ => let A := fresh "A" in destruct HFR as [A HFR] end.
  repeat match goal with |- _ /\ _ => split end;
    first [ apply HVMF; [lia | lia | assumption]
          | intros i Hi; apply HVMF; [unfold DR_SAVE_OFF; lia | unfold DR_SAVE_OFF; lia | exact (HFR i Hi)] ]. }
split.
{ apply (akept_garr8 W1 m1); [|exact Hgarr]. intros x Hx.
  pose proof HEOK as (_ & _ & Hp1 & Hp2 & _).
  rewrite (dnk_entry_len e1 Hp1 Hp2) in Hx.
  destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR GT) as (_ & H4 & Hc & _).
  change (req_size ATABLE) with 896 in Hc. unfold AENT, ATABLE in *. apply HK. left. lia. }
split; [intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 m2 _ (HP _)); exact (Hawr i Hi)|].
split.
{ apply (dnk_aentry_okx_kept ly1 S1 W1 m1 ly1 S1 W1 m2 e1 HEOK); [|exact (dnk_aentry_blks_in ly1 S1 W1 m1 e1 HEOK)].
  intros r Hr a Ha. apply HKL.
  exact (proj1 (dnk_fp_entry cx ly1 S1 W1 m1 md1 e1 _ HAR Hperm (fun b Hb => HBIN b (or_introl Hb)) HEOK r Hr a Ha)). }
split.
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 Hsrc);
    [|exact (dnk_asrc_blks_in ly1 S1 W1 m1 (dHA RG cx) h1 Hsrc)].
  intros r Hr a Ha. apply HKL.
  exact (proj1 (dnk_fp_src cx ly1 S1 W1 m1 md1 _ h1 HAR Hperm (fun b Hb => HBIN b (or_intror (or_introl Hb)))
    GT Hj Hsrc r Hr a Ha)). }
split.
{ intros i Hi Hne. destruct (Hoth i Hi Hne) as (f & o & V1 & V2 & Hdis). exists f, o.
  assert (Hi4 : Z.of_nat i < 4) by lia. pose proof HGSB as (G1 & G2 & G3). unfold ASRC in *.
  split; [apply HVMG; [lia | lia | exact V1]|].
  split; [apply HVMG; [lia | lia | exact V2] | exact Hdis]. }
split.
{ intros x Hx1 Hx2. pose proof (Hgsk x Hx1 Hx2) as (Hv & Hw).
  pose proof (proj1 (dnk_gs_ok cx ly1 S1 W1 m1 md1 x HAR GT Hx1)) as (Hxl & _).
  split; [rewrite (KL x ltac:(lia) ltac:(lia)); exact Hv|].
  intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 x (HP x)). exact (Hw Hwr). }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2); [exact Hout| |].
  - intros r Hr a Ha. apply HKL.
    exact (proj1 (dnk_fp_out cx ly1 S1 W1 m1 md1 _ _ _ _ _ _ _ HAR Hperm
      (fun b Hb => HBIN b (or_intror (or_intror Hb))) Hout r Hr a Ha)).
  - exact (dnk_aout_blks_in ly1 S1 W1 m1 _ _ _ _ _ _ Hout). }
split; [exact Hlivout | exact Hperm].
Qed.

End c.

(* ---- THE GENERIC KIT (an internal work row): the AR-reading lemmas above over any allocator relation ARx with its laws, at the
   room texts.  The Section is W_drain_cx_x.v's Section c - its variables B PST ARx MT RP MMAX RG in that order, each
   hypothesis that file's text - with the allocator rules in their caller-context forms (no allocator is called by
   the segments that use these lemmas, so no call-site fact HCTX_* is stated), and after LAWS the generic-relation
   fact HP0 (no hidden head in any ARx state, a Theorem Labs lane's ruling).  An image byte lies in no live block (YCbqG.v
   blk_img_x, the laws' client-image field): the image's cells (g_s, G_DR, HGO's three) are apart from every block
   without a numeric image band, so dnk_low_img_x / dnx_low_img_x take `in_img SEGS a` (lib/A/W_drain_epi.v
   dend_low_img_x).  AR-free lemmas this Section reads are restated with an _x suffix, so no lemma's Section
   generalization is relied on. ---- *)
Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes_x B ARx (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes_x B ARx (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
Hypothesis RMM : forall S k k', (k' <= k)%nat -> rp_RM RP S k -> rp_RM RP S k'.
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at_x ARx 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at_x ARx 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at_x ARx 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.

Lemma dnk_zall_x : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma dnk_zpw_x : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply dnk_zall_x; [exact H1 | lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | lia].
Qed.

Lemma dnk_errno_sep_x : forall a,
(rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_client RG <= a < rg_client RG + 4 \/
 rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/
 rg_send_dead RG <= a < rg_send_dead RG + 1 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8) ->
~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha He.
pose proof (dnk_zpw_x _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D2.
pose proof (dnk_zpw_x _ 3 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D3.
pose proof (dnk_zpw_x _ 4 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D4.
pose proof (dnk_zpw_x _ 5 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D5.
pose proof (dnk_zpw_x _ 6 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D6.
pose proof (dnk_zpw_x _ 7 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D7.
pose proof (dnk_zpw_x _ 8 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D8.
pose proof (dnk_zpw_x _ 9 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D9.
pose proof (dnk_zpw_x _ 10 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D10.
cbn [nth] in D2, D3, D4, D5, D6, D7, D8, D9, D10. unfold zdisj in *. cbn [fst snd] in *. lia.
Qed.

(* an image byte is no byte of the table block (YCbqG.v blk_img_x, the laws' client-image field) *)
Lemma dnk_low_img_x : forall cx ly S Hp (W : world SEGS) mem md a,
ARx ly S Hp W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> in_img SEGS a -> dnk_low cx a.
Proof.
intros cx ly S Hp W mem md a HAR Hin Ha.
pose proof (pa_img_range a Ha) as Hr.
pose proof asan_consts as (C1 & _).
assert (NT : ~ (dxG cx <= a < dxG cx + req_size ATABLE))
  by (intros Ht; exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ a HAR Hin Ht Ha)).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in NT.
unfold dnk_low, ATABLE in *. lia.
Qed.

Lemma dnk_low_blk_x : forall cx ly S Hp (W : world SEGS) mem md L p n a,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
In (p, n) L -> p <= a < p + req_size n ->
dnk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S Hp W mem md L p n a HAR HP HL Ha.
assert (Hin : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); right; exact HL).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & H4 & Hc & _).
destruct (in_split _ _ HL) as (l1 & l2 & ->).
assert (HP2 : Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: (p, n) :: l1 ++ l2))
  by (eapply Permutation_trans; [exact HP | apply perm_skip; apply Permutation_sym, Permutation_middle]).
pose proof (sep_blocks_perm_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in Hd.
split; [unfold dnk_low, ATABLE; lia|].
intros He. apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md p n a HAR Hin ltac:(lia)).
apply (proj1 (HG a ltac:(unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))).
Qed.

Lemma dnk_gs_ok_x : forall cx ly S Hp (W : world SEGS) mem md a,
ARx ly S Hp W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> rg_s RG <= a < rg_s RG + 4 * ASRC ->
dnk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S Hp W mem md a HAR Hin Ha.
split; [apply (dnk_low_img_x cx ly S Hp W mem md a HAR Hin); refine (proj1 (HG a _)); unfold inG, G_DR;
  apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Ha|].
apply dnk_errno_sep_x. left. exact Ha.
Qed.

Lemma dnk_key_ptrs_len_x : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma dnk_recs_len_x : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma dnk_fp_entry_x : forall cx ly S Hp (W : world SEGS) mem md e L,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aentry_blks e) -> In b L) -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
dnk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S Hp W mem md e L HAR HP HB HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (BLK : forall p n, In (p, n) (aentry_blks e) -> 0 <= n -> p <= a < p + n ->
  dnk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn Hpa. pose proof (req_size_pos n Hn) as (_ & Hrq).
  exact (dnk_low_blk_x cx ly S Hp W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (BLK (re_buf e) (re_cap e)); [| lia | lia].
  unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. lia.
    * unfold bzs in Ha. rewrite length_map, dnk_key_ptrs_len_x in Ha. unfold re_nheld in Hk1.
      apply (BLK (re_hp e) (re_kh e)); [| lia | lia].
      unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (key_addr k) (Z.of_nat (length (key_text k)) + 1)); [| lia | lia].
    unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
    apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
Qed.

Lemma dnk_fp_list_x : forall cx ly S Hp (W : world SEGS) mem md L LA l lines,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (alist_blks l) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) ->
alist_at B ly S W mem LA l lines -> rg_s RG <= LA -> LA + 16 <= rg_s RG + 4 * ASRC ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
dnk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S Hp W mem md L LA l lines HAR HP HB HGin HL Hlo Hhi r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
assert (BLK : forall p n, In (p, n) (alist_blks l) -> 0 <= n -> p <= a < p + n ->
  dnk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn0 Hpa. pose proof (req_size_pos n Hn0) as (_ & Hrq).
  exact (dnk_low_blk_x cx ly S Hp W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (dnk_gs_ok_x cx ly S Hp W mem md a HAR HGin). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, dnk_recs_len_x in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (BLK (hl_v l) (AREC * hl_cap l)); [| unfold AREC; lia | unfold hl_n, AREC in *; lia].
    unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (fst q) (Z.of_nat (length (snd q)) + 1)); [| lia | lia].
    unfold alist_blks. apply in_or_app. right.
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
Qed.

Lemma dnk_fp_src_x : forall cx ly S Hp (W : world SEGS) mem md L h,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (asrc_blks h) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) -> (dxj cx < 4)%nat ->
asrc_at B ly S W mem (dHA RG cx) h ->
forall r, In r (asrc_fp (dHA RG cx) h) -> forall a, fst r <= a < snd r ->
dnk_low cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S Hp W mem md L h HAR HP HB HGin Hj HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; lia).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (dnk_gs_ok_x cx ly S Hp W mem md a HAR HGin). lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
  apply (dnk_low_blk_x cx ly S Hp W mem md L (hs_partial h) APARTIAL a HAR HP); [apply HB; left; reflexivity | lia].
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + exact (dnk_fp_list_x cx ly S Hp W mem md L (dHA RG cx + 16) (hs_pending h) false HAR HP
      (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_introl Hb)))) HGin Hpend
      ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * exact (dnk_fp_list_x cx ly S Hp W mem md L (dHA RG cx + 64) (hs_expected h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb)))))) HGin Hexp
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
    * exact (dnk_fp_list_x cx ly S Hp W mem md L (dHA RG cx + 80) (hs_held h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hb)))))) HGin Hheld
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
Qed.

Local Ltac dnk_gdr_x := lazymatch goal with IMG : forall x, in_img _ x -> _, GDR : forall x, inG (G_DR _ _) x -> _ |- _ =>
  apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ] end.
Local Ltac dnk_go_x := lazymatch goal with IMG : forall x, in_img _ x -> _, GO : forall x, inG [_; _; _] x -> _ |- _ =>
  apply IMG, GO; unfold inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ] end.

Lemma dnk_fp_out_x : forall cx ly S Hp (W : world SEGS) mem md c O mx no cap out L,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aout_blks cap out) -> In b L) ->
aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
dnk_low cx a /\ (r <> (as_errno B, as_errno B + 4) -> ~ (as_errno B <= a < as_errno B + 4)).
Proof.
intros cx ly S Hp W mem md c O mx no cap out L HAR HP HB HOUT r Hr a Ha.
assert (GT : In (dxG cx, ATABLE) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
assert (IMG : forall x, in_img SEGS x -> dnk_low cx x)
  by (intros x Hx; exact (dnk_low_img_x cx ly S Hp W mem md x HAR GT Hx)).
assert (GDR : forall x, inG (G_DR B RG) x -> in_img SEGS x) by (intros x Hx; exact (proj1 (HG x Hx))).
assert (GO : forall x, inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x -> in_img SEGS x)
  by (intros x Hx; exact (proj1 (HGO x Hx))).
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- split; [dnk_go_x | intros _; apply dnk_errno_sep_x; tauto].
- split; [dnk_gdr_x | intros _; apply dnk_errno_sep_x; tauto].
- split; [dnk_gdr_x | intros _; apply dnk_errno_sep_x; tauto].
- split; [dnk_gdr_x | intros _; apply dnk_errno_sep_x; tauto].
- split; [dnk_go_x | intros _; apply dnk_errno_sep_x; tauto].
- split; [dnk_gdr_x | intros _; apply dnk_errno_sep_x; tauto].
- split; [dnk_go_x | intros _; apply dnk_errno_sep_x; tauto].
- split; [dnk_gdr_x | intros _; apply dnk_errno_sep_x; tauto].
- split; [dnk_gdr_x | intros Hne; exfalso; apply Hne; reflexivity].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq).
  destruct (dnk_low_blk_x cx ly S Hp W mem md L out cap a HAR HP) as [D1 D2];
    [apply HB; unfold aout_blks; rewrite Hc0; left; reflexivity | lia |].
  split; [exact D1 | intros _; exact D2].
Qed.

(* the same footprint facts against ANY block X of the round (Section c's dnx_ lemmas) *)
Lemma dnx_low_img_x : forall X ly S Hp (W : world SEGS) mem md a,
ARx ly S Hp W mem md -> In X (ablocks B ly S) -> in_img SEGS a -> dnx_low X a.
Proof.
intros [xp xn] ly S Hp W mem md a HAR Hin Ha.
pose proof (pa_img_range a Ha) as Hr.
pose proof asan_consts as (C1 & _).
assert (NT : ~ (xp <= a < xp + req_size xn))
  by (intros Ht; exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ a HAR Hin Ht Ha)).
unfold dnx_low. cbn [fst snd]. lia.
Qed.

Lemma dnx_low_blk_x : forall X ly S Hp (W : world SEGS) mem md L p n a,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (X :: L) ->
In (p, n) L -> p <= a < p + req_size n ->
dnx_low X a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros X ly S Hp W mem md L p n a HAR HP HL Ha.
assert (Hin : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); right; exact HL).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & H4 & Hc & _).
destruct (in_split _ _ HL) as (l1 & l2 & ->).
assert (HP2 : Permutation (ablocks B ly S) (X :: (p, n) :: l1 ++ l2))
  by (eapply Permutation_trans; [exact HP | apply perm_skip; apply Permutation_sym, Permutation_middle]).
pose proof (sep_blocks_perm_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
split; [unfold dnx_low; lia|].
intros He. apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md p n a HAR Hin ltac:(lia)).
apply (proj1 (HG a ltac:(unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))).
Qed.

Lemma dnx_gs_ok_x : forall X ly S Hp (W : world SEGS) mem md a,
ARx ly S Hp W mem md -> In X (ablocks B ly S) -> rg_s RG <= a < rg_s RG + 4 * ASRC ->
dnx_low X a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros X ly S Hp W mem md a HAR Hin Ha.
split; [apply (dnx_low_img_x X ly S Hp W mem md a HAR Hin); refine (proj1 (HG a _)); unfold inG, G_DR;
  apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Ha|].
apply dnk_errno_sep_x. left. exact Ha.
Qed.

Lemma dnx_fp_list_x : forall X ly S Hp (W : world SEGS) mem md L LA l lines,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (X :: L) ->
(forall b, In b (alist_blks l) -> In b L) -> In X (ablocks B ly S) ->
alist_at B ly S W mem LA l lines -> rg_s RG <= LA -> LA + 16 <= rg_s RG + 4 * ASRC ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
dnx_low X a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros X ly S Hp W mem md L LA l lines HAR HP HB HXin HL Hlo Hhi r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
assert (BLK : forall p n, In (p, n) (alist_blks l) -> 0 <= n -> p <= a < p + n ->
  dnx_low X a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn0 Hpa. pose proof (req_size_pos n Hn0) as (_ & Hrq).
  exact (dnx_low_blk_x X ly S Hp W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (dnx_gs_ok_x X ly S Hp W mem md a HAR HXin). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, dnk_recs_len_x in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (BLK (hl_v l) (AREC * hl_cap l)); [| unfold AREC; lia | unfold hl_n, AREC in *; lia].
    unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (fst q) (Z.of_nat (length (snd q)) + 1)); [| lia | lia].
    unfold alist_blks. apply in_or_app. right.
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
Qed.

Lemma dnx_fp_src_x : forall X cx ly S Hp (W : world SEGS) mem md L h,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (X :: L) ->
(forall b, In b (asrc_blks h) -> In b L) -> In X (ablocks B ly S) -> (dxj cx < 4)%nat ->
asrc_at B ly S W mem (dHA RG cx) h ->
forall r, In r (asrc_fp (dHA RG cx) h) -> forall a, fst r <= a < snd r ->
dnx_low X a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros X cx ly S Hp W mem md L h HAR HP HB HXin Hj HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; lia).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (dnx_gs_ok_x X ly S Hp W mem md a HAR HXin). lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
  apply (dnx_low_blk_x X ly S Hp W mem md L (hs_partial h) APARTIAL a HAR HP); [apply HB; left; reflexivity | lia].
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + exact (dnx_fp_list_x X ly S Hp W mem md L (dHA RG cx + 16) (hs_pending h) false HAR HP
      (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_introl Hb)))) HXin Hpend
      ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * exact (dnx_fp_list_x X ly S Hp W mem md L (dHA RG cx + 64) (hs_expected h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb)))))) HXin Hexp
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
    * exact (dnx_fp_list_x X ly S Hp W mem md L (dHA RG cx + 80) (hs_held h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hb)))))) HXin Hheld
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
Qed.

Local Ltac dnx_gdr_x := lazymatch goal with IMG : forall x, in_img _ x -> _, GDR : forall x, inG (G_DR _ _) x -> _ |- _ =>
  apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ] end.
Local Ltac dnx_go_x := lazymatch goal with IMG : forall x, in_img _ x -> _, GO : forall x, inG [_; _; _] x -> _ |- _ =>
  apply IMG, GO; unfold inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ] end.
Lemma dnx_fp_out_x : forall X ly S Hp (W : world SEGS) mem md c O mx no cap out L,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (X :: L) ->
(forall b, In b (aout_blks cap out) -> In b L) ->
aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> dnx_low X a.
Proof.
intros X ly S Hp W mem md c O mx no cap out L HAR HP HB HOUT r Hr a Ha.
assert (GT : In X (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
assert (IMG : forall x, in_img SEGS x -> dnx_low X x)
  by (intros x Hx; exact (dnx_low_img_x X ly S Hp W mem md x HAR GT Hx)).
assert (GDR : forall x, inG (G_DR B RG) x -> in_img SEGS x) by (intros x Hx; exact (proj1 (HG x Hx))).
assert (GO : forall x, inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x -> in_img SEGS x)
  by (intros x Hx; exact (proj1 (HGO x Hx))).
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha;
  [ dnx_go_x | dnx_gdr_x | dnx_gdr_x | dnx_gdr_x | dnx_go_x | dnx_gdr_x | dnx_go_x | dnx_gdr_x | dnx_gdr_x | ].
destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq).
exact (proj1 (dnx_low_blk_x X ly S Hp W mem md L out cap a HAR HP ltac:(apply HB; unfold aout_blks; rewrite Hc0; left; reflexivity) ltac:(lia))).
Qed.

(* Section c's AR-free block-membership and keeping lemmas, restated *)
Lemma dnk_aentry_blks_in_x : forall ly S (W : world SEGS) m e,
aentry_okx B ly S W m e -> forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
intros ly S W m e (_ & _ & _ & _ & _ & _ & _ & _ & Hbuf & _ & Hhp & _ & _ & Hkeys) b Hb.
unfold aentry_blks in Hb.
destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [app] in Hb.
- destruct (Z.eqb_spec (re_hp e) 0) as [Hz0|Hz0]; cbn [app] in Hb.
  + apply in_map_iff in Hb as (k & <- & Hk).
    rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
  + destruct Hb as [<- | Hb].
    * destruct Hhp as [(Hz & _)|(_ & Hin & _)]; [lia | exact Hin].
    * apply in_map_iff in Hb as (k & <- & Hk).
      rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
- destruct Hb as [<- | Hb].
  + destruct Hbuf as [(Hc & _)|(_ & Hin & _)]; [lia | exact Hin].
  + destruct (Z.eqb_spec (re_hp e) 0) as [Hz0|Hz0]; cbn [app] in Hb.
    * apply in_map_iff in Hb as (k & <- & Hk).
      rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
    * destruct Hb as [<- | Hb].
      -- destruct Hhp as [(Hz & _)|(_ & Hin & _)]; [lia | exact Hin].
      -- apply in_map_iff in Hb as (k & <- & Hk).
         rewrite Forall_forall in Hkeys. exact (proj1 (Hkeys k Hk)).
Qed.

Lemma dnk_alist_blks_in_x : forall ly S (W : world SEGS) m LA l lines,
alist_at B ly S W m LA l lines -> forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
intros ly S W m LA l lines (_ & _ & _ & _ & _ & Hv & _ & _ & Hrecs) b Hb.
unfold alist_blks in Hb.
destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [app] in Hb.
- apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in Hrecs. exact (proj1 (Hrecs r Hr)).
- destruct Hb as [<- | Hb].
  + destruct Hv as [(Hc & _)|(_ & Hin & _)]; [lia | exact Hin].
  + apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in Hrecs. exact (proj1 (Hrecs r Hr)).
Qed.

Lemma dnk_asrc_blks_in_x : forall ly S (W : world SEGS) m HA h,
asrc_at B ly S W m HA h -> forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
intros ly S W m HA h HS b Hb.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & _ & _ & _ &
  Hexp & Hheld & _).
unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact Hpb|].
apply in_app_or in Hb as [Hb | Hb];
  [exact (dnk_alist_blks_in_x ly S W m (HA + 16) (hs_pending h) false Hpend b Hb)|].
apply in_app_or in Hb as [Hb | Hb];
  [exact (dnk_alist_blks_in_x ly S W m (HA + 64) (hs_expected h) true Hexp b Hb)
  |exact (dnk_alist_blks_in_x ly S W m (HA + 80) (hs_held h) true Hheld b Hb)].
Qed.

Lemma dnk_aout_blks_in_x : forall ly S (W : world SEGS) m c O mx no cap out,
aout_at B RG ly S W m c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
intros ly S W m c O mx no cap out HOUT b Hb.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & Hblk).
unfold aout_blks in Hb. destruct (cap =? 0) eqn:Hc0; [destruct Hb|]. destruct Hb as [<- | []].
destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia | exact Hin].
Qed.

Lemma dnk_aentry_okx_kept_x : forall ly S (W : world SEGS) m ly' S' (W' : world SEGS) m' e,
aentry_okx B ly S W m e -> akept W m W' m' (aentry_fp e) ->
(forall b, In b (aentry_blks e) -> In b (ablocks B ly' S')) -> aentry_okx B ly' S' W' m' e.
Proof.
intros ly S W m ly' S' W' m' e
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) HK HB.
do 8 (split; [assumption|]).
split.
{ destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|].
  split; [apply HB; unfold aentry_blks; rewrite Ec; left; reflexivity|].
  split; [exact Hj|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_buf e) (bzs (re_U e ++ re_junk e)))); [|exact Hx].
  unfold aentry_fp. rewrite Ec. left. reflexivity. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11|right].
  assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
  split; [exact Hz|].
  split; [apply HB; unfold aentry_blks; apply in_or_app; right; rewrite Ez; left; reflexivity|].
  split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_hp e) (bzs (key_ptrs (re_keys e))))); [|exact Hx].
  unfold aentry_fp. apply in_or_app. right. left. reflexivity. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [apply HB; unfold aentry_blks; apply in_or_app; right; apply in_or_app; right;
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
split; [|exact K3].
apply (akept_garr8 W m); [|exact K2].
intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
unfold aentry_fp. apply in_or_app. right. right.
apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0): dnk_DMEM_call_x at a world relation R.  DMEM_x -> W_drain_cx_x.v's
   DMEM_xR .. R, ajournal_gx_x -> ajournal_gx_xR .. R (R right after ARx); every other token is the strict text's.
   dnk_DMEM_call_x below is it at R := wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.

(* R twin of dnk_DMEM_call_x *)
Lemma dnk_DMEM_call_xR : forall cx Hp kr ly1 S1 Hp1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1
  lo,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k2 ->
alloc_ceiling <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < dsp0 cx - DRAIN_FRAME) -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m2 md2 k2 e1 h1 sg out1 ev1 sent LB1.
Proof.
intros cx Hp kr ly1 S1 Hp1 W1 m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1 lo HB HMEM HJ2 Hlo KL HP.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HJ as HAR. eapply ajournal_gx_AR_xR in HAR.
pose proof HB as (Hafn & _ & _ & HSAlo & HSAhi & _ & _ & _ & _ & Hj & _).
pose proof Hafn as (_ & _ & _ & _ & _ & (_ & _ & Hcl & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hslo, Hshi.
assert (HDS : DRAIN_STK_x = 17008) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
pose proof asan_consts as (C1 & _).
assert (GT : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (HK : forall a, 0 <= a < alloc_ceiling \/ dsp0 cx - DRAIN_FRAME <= a < 2 ^ 64 -> abyte_kept W1 m1 W1 m2 a).
{ intros a Ha. split; [apply KL; lia|]. unfold arm. apply (writable_kept (w_H W1) m1 m2 a (HP a)). }
assert (HKL : forall a, dnk_low cx a -> abyte_kept W1 m1 W1 m2 a) by (intros a (Ha & _); apply HK; left; exact Ha).
assert (HVMF : forall a v, dsp0 cx - DRAIN_FRAME <= a -> a + 8 <= dsp0 cx ->
  val_mem SEGS (arm W1 m1) a 8 v -> val_mem SEGS (arm W1 m2) a 8 v).
{ intros a v H1 H2 Hv. apply (akept_vm W1 m1); [|exact Hv]. intros x Hx. apply HK. right. lia. }
assert (HVMG : forall a v, rg_s RG <= a -> a + 4 <= rg_s RG + 4 * ASRC ->
  val_mem SEGS (arm W1 m1) a 4 v -> val_mem SEGS (arm W1 m2) a 4 v).
{ intros a v H1 H2 Hv. apply (akept_vm W1 m1); [|exact Hv]. intros x Hx. cbn in Hx.
  apply HKL. exact (proj1 (dnk_gs_ok_x cx ly1 S1 Hp1 W1 m1 md1 x HAR GT ltac:(lia))). }
assert (HBIN : forall b, In b (aentry_blks e1) \/ In b (asrc_blks h1) \/ In b (aout_blks (drain_b_c.ds_ocap sg) out1) ->
  In b (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx)).
{ intros b [Hb | [Hb | Hb]]; apply in_or_app; [left; exact Hb | right; apply in_or_app; left; exact Hb |].
  right; apply in_or_app; right; apply in_or_app; left; exact Hb. }
split; [exact HJ2|].
split.
{ intros a Ha. pose proof Ha as (sg0 & Hsg & _ & Hr).
  pose proof (pa_img_range a (ex_intro _ sg0 (conj Hsg Hr))) as Hai.
  rewrite (KL a ltac:(lia) ltac:(lia)). exact (Hrom a Ha). }
split; [intros a Ha1 Ha2 Ha3 Ha4; apply HP; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  repeat match type of HFR with _ /\ _ => let A := fresh "A" in destruct HFR as [A HFR] end.
  repeat match goal with |- _ /\ _ => split end;
    first [ apply HVMF; [lia | lia | assumption]
          | intros i Hi; apply HVMF; [unfold DR_SAVE_OFF; lia | unfold DR_SAVE_OFF; lia | exact (HFR i Hi)] ]. }
split.
{ apply (akept_garr8 W1 m1); [|exact Hgarr]. intros x Hx.
  pose proof HEOK as (_ & _ & Hp1' & Hp2' & _).
  rewrite (dnk_entry_len e1 Hp1' Hp2') in Hx.
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR GT) as (_ & H4 & Hc & _).
  change (req_size ATABLE) with 896 in Hc. unfold AENT, ATABLE in *. apply HK. left. lia. }
split; [intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 m2 _ (HP _)); exact (Hawr i Hi)|].
split.
{ apply (dnk_aentry_okx_kept_x ly1 S1 W1 m1 ly1 S1 W1 m2 e1 HEOK); [|exact (dnk_aentry_blks_in_x ly1 S1 W1 m1 e1 HEOK)].
  intros r Hr a Ha. apply HKL.
  exact (proj1 (dnk_fp_entry_x cx ly1 S1 Hp1 W1 m1 md1 e1 _ HAR Hperm (fun b Hb => HBIN b (or_introl Hb)) HEOK r Hr a Ha)). }
split.
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 Hsrc);
    [|exact (dnk_asrc_blks_in_x ly1 S1 W1 m1 (dHA RG cx) h1 Hsrc)].
  intros r Hr a Ha. apply HKL.
  exact (proj1 (dnk_fp_src_x cx ly1 S1 Hp1 W1 m1 md1 _ h1 HAR Hperm (fun b Hb => HBIN b (or_intror (or_introl Hb)))
    GT Hj Hsrc r Hr a Ha)). }
split.
{ intros i Hi Hne. destruct (Hoth i Hi Hne) as (f & o & V1 & V2 & Hdis). exists f, o.
  assert (Hi4 : Z.of_nat i < 4) by lia. pose proof HGSB as (G1 & G2 & G3). unfold ASRC in *.
  split; [apply HVMG; [lia | lia | exact V1]|].
  split; [apply HVMG; [lia | lia | exact V2] | exact Hdis]. }
split.
{ intros x Hx1 Hx2. pose proof (Hgsk x Hx1 Hx2) as (Hv & Hw).
  pose proof (proj1 (dnk_gs_ok_x cx ly1 S1 Hp1 W1 m1 md1 x HAR GT Hx1)) as (Hxl & _).
  split; [rewrite (KL x ltac:(lia) ltac:(lia)); exact Hv|].
  intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 x (HP x)). exact (Hw Hwr). }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2); [exact Hout| |].
  - intros r Hr a Ha. apply HKL.
    exact (proj1 (dnk_fp_out_x cx ly1 S1 Hp1 W1 m1 md1 _ _ _ _ _ _ _ HAR Hperm
      (fun b Hb => HBIN b (or_intror (or_intror Hb))) Hout r Hr a Ha)).
  - exact (dnk_aout_blks_in_x ly1 S1 W1 m1 _ _ _ _ _ _ Hout). }
split; [exact Hlivout | exact Hperm].
Qed.
End wR.
(* the strict texts are the R twins above at R := wle: each R premise at wle is the strict hypothesis of the same
   name, and the three laws hold for wle *)
Local Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

(* DMEM_x survives a call whose writes lie in [lo, sp) for lo above the allocator ceiling, with presence kept and its
   journal given at the new memory (Section c's dnk_DMEM_call over ARx: the cut's ghost list Hp1 is the journal's) *)
Lemma dnk_DMEM_call_x : forall cx Hp kr ly1 S1 Hp1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1
  lo,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
DMEM_x B PST ARx RG cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k2 ->
alloc_ceiling <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < dsp0 cx - DRAIN_FRAME) -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM_x B PST ARx RG cx Hp ly1 S1 Hp1 W1 m2 md2 k2 e1 h1 sg out1 ev1 sent LB1.
Proof.
eapply (dnk_DMEM_call_xR (@wle SEGS)); wle_inst.
Qed.

End cx.
End b.
End a.
