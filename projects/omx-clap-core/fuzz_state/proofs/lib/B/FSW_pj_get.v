(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 1266 of its 1332 lines of code are new or changed and 1014 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_dec_E.v, with its module paths, module names and numbers changed; 1298 of its 1424 lines of code are new or changed and 1206 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the per-function walk form of lib/A/FSW_pj_get.v (a working branch bfa606fd37a),
   re-walked over image B's own code. *)
(* pj_get (fs.asan-ubsan, IMAGE B, 0x83894 .. 0x83a54, 112 instructions; pf.c:352-362): its ASan contract
   lib/B/FSH_Fn_reader.pj_get_spec (S0 aaf2c4ec41f), by a symbolic walk of B's OWN machine code over lib/B's walk kit
   (FSW_K / FSW_ret / FSW_rd), in the per-function form of the donor cgif_file_fuzzer as ported by a Theorem Labs lane.
   rule 24 (a Theorem Labs lane): reuse search by name with control (proof-index pj_get pj_free pj_string; pj_object
   pj_get_str pj_string: released hits are the plain lib/Prog and ubsan lib/U proofs only, no ASan address), by every B
   address (pj_get 0x83894, a direct jal callee: no trampoline / wrapper / REAL slot), and over the named cold branches
   (two working branches' lib/B/Prog: bespoke evt-form proofs of B's code, templates only, not bridgeable);
   CONFIRMED by the read-only checker a Theorem Labs lane (a Theorem Labs lane chk-B4-summary.txt: pj_get B: CONFIRM).
   TEMPLATES, read and never imported: the image-A walk (kit usage, premise discharges, the post); bump's
   lib/B/Prog/pj_get.v (B's segments, register facts and shadow-check pcs); the listing
   (internal path). B IS NOT A's CODE: frame 96 (A 80) saving ra, s0..s9;
   loop head 0x83948 with s2 = s9 = keys + 8 i, s4 = -56 i, s5 = i, s6 = n, s7 = keys, s8 = 1; and UBSan's checks.
   ASan: five inline shadow checks (obj at 0x838ec, a 4-byte check whose slow path 0x83a30 has no andi, so the engine
   asks the whole granule; obj + 40 at 0x8390c; obj + 32 at 0x83928; keys[i] at 0x83970; obj + 24 at 0x839e0), each
   walked by the kit's token run (FSW_K fsw_aj_run_tokU, fs_Bx / fs_Bspan) with one shadow entry per object (obj from
   pobj's range_addressable, the keys slot from the keys block's payload, pg_ra_payload), so every __asan_report_* arm
   (0x83a3c, 0x83a40 .. 0x83a50) is untaken.
   UBSan (trap mode: one unimp at 0x83a2c, no __ubsan_* call). Each branch to it is decided by the engine from a fact
   the walk gives it, and each fact is a premise of the spec:
     0x838d0 `bnez (o & 7)`: o mod 8 = 0, pobj (both arms) -> es_gf atom 10 al2 3.
     0x8394c `beq (keys <> 0) (keys + 8 i = 0)`: keys >= 4112 and keys + 8 i + 8 <= alloc_ceiling: rnode's pj_node
       object clause with n >= 1 gives cap >= 1 and In (keys, 8 cap) UL, rd_blocks_ok gives fs_rblock, fsw_rblock_low
       the bounds -> lp_atoms atom 23 in [4112, CEIL], atom 18 in [4096, CEIL].
     0x83954 `bnez (i >> 60)`: i < n <= cap < 2 ^ 44 (the keys block bound) -> lp_conds' first (pg_lp_conds).
     0x83958 `bltu (keys + 8 i) keys`: keys + 8 i < 2 ^ 64 (the same bound) -> lp_conds' second.
     0x8395c `beqz keys`: keys >= 4112 (as 0x8394c) -> atom 23.
     0x83964 `bnez ((keys + 8 i) & 7)`: keys mod 16 = 0, fs_rblock's alignment -> atom 18 al2 3.
     0x83a04 `beq (kids <> 0) (kids + 56 i = 0)`: kids >= 4112 (In (kids, 56 cap) UL, fs_rblock) and
       kids + 56 n <= alloc_ceiling -> hit_G atom 44 and hit_conds' first (pg_hit_conds).
     0x83a08 `bltu (kids + 56 i) kids`: kids + 56 i < 2 ^ 64 (the kids block bound) -> hit_conds' second.
     0x83a20 `bnez (mulh (i, 56) xor (56 i >>s 63))`, the signed overflow test of i * 56: i <= 2 ^ 54, so
       56 i < 2 ^ 63 -> hit_conds' third.
   The strcmp call 0x83980 -> 0x83984 goes through FSW_K.fsw_intrin_atU over the RUNTIME contract astrcmp_realizesU
   at B's trampoline PC_strcmp 0x426cc (Section hypothesis).
   THE LOOP INVARIANT (pj_li below, at the loop head 0x83948, i the member index, n the member count): the machine is at
   0x83948 with sp = entry sp - 96, s0 = obj, s1 = key, s2 = s9 = keys + 8 i, s3 = the shadow base, s4 = -56 i, s5 = i,
   s6 = n, s7 = keys, s8 = 1, gp / tp / s10 / s11 the entry values, the eleven saved registers in the frame, the journal
   from the entry at tick 0, ARU at the same U, the memory below alloc_ceiling as at the entry (aview), and no member
   j < i named kname; proved by induction on the remaining count n - i (pg_loop). SK stays the Sections' Context (the
   B instantiation passes FSH_Base.fsB_sink_head with `@`). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YN2e.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret FSH_Fn_reader FSW_rd FSW_strkit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSW_pj_get_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjStruct.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* ================= plain bytes (lib/Lib Mem.bytes_at, PjStruct) to the ASan side's val_mem / garr8 ================= *)
Lemma pg_mrd : forall m a, Mem.mrd tfibsegs m (Mem.wa a) = mbyte tfibsegs m a.
Proof. intros m a. reflexivity. Qed.
Lemma pg_vm_u64 : forall m a v, PjStruct.pj_u64 tfibsegs m a v -> val_mem tfibsegs m a 8 v.
Proof.
intros m a v (Hv & _ & _ & Hb) k Hk. rewrite Mem.length_le8 in Hb. specialize (Hb k Hk).
rewrite pg_mrd in Hb. rewrite Hb. unfold Mem.le8. exact (YN2e.word_to_le_bytes_nth 8 v k Hk ltac:(lia)).
Qed.
Lemma pg_vm_u32 : forall m a v, PjStruct.pj_u32 tfibsegs m a v -> val_mem tfibsegs m a 4 v.
Proof.
intros m a v (Hv & _ & _ & Hb) k Hk. rewrite Mem.length_le4 in Hb. specialize (Hb k Hk).
rewrite pg_mrd in Hb. rewrite Hb. exact (YN2e.word_to_le_bytes_nth 4 v k Hk ltac:(lia)).
Qed.
Lemma pg_garr8 : forall m p s, PjStruct.pj_cbytes tfibsegs m p s ->
  garr8 tfibsegs m p (s ++ [0]) /\ Forall (fun c => c <> 0) s.
Proof.
intros m p s (HF & _ & _ & Hb).
assert (HR : forall j, (j < length (s ++ [0%Z]))%nat -> 0 <= nth j (s ++ [0]) 0 < 256).
{ intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  destruct (Nat.lt_ge_cases j (length s)) as [L|L].
  - rewrite app_nth1 by exact L. rewrite Forall_forall in HF. pose proof (HF (nth j s 0) (nth_In s 0 L)). lia.
  - rewrite app_nth2 by exact L. replace (j - length s)%nat with 0%nat by lia. cbn. lia. }
split.
- intros j Hj. split; [|exact (HR j Hj)]. intros k Hk. assert (k = 0%nat) as -> by lia.
  change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
  assert (Hj' : (j < length (map (Z_to_bv 8) (s ++ [0%Z])))%nat) by (rewrite length_map; exact Hj).
  pose proof (Hb j Hj') as Hbj. rewrite pg_mrd in Hbj. rewrite Hbj, nth_error_map, (nth_error_nth' _ 0%Z Hj).
  cbn [option_map]. f_equal.
  apply bv_eq. rewrite !Z_to_bv_unsigned. pose proof (HR j Hj) as Hr.
  set (v := nth j (s ++ [0]) 0) in *.
  unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. rewrite Z.shiftr_0_r.
  rewrite (Z.mod_small v (2 ^ 8)) by (cbn; lia). rewrite (Z.mod_small v 256) by lia. reflexivity.
- rewrite Forall_forall in HF |- *. intros c Hc. pose proof (HF c Hc). lia.
Qed.

(* ================= the memory below alloc_ceiling read the same (aview), and what it carries ================= *)
Definition av_below (H : word -> bool) (m m' : word -> option byte) (lo : Z) : Prop :=
  forall a, 0 <= a < lo -> aview tfibsegs H m' a = aview tfibsegs H m a.
Lemma av_refl : forall H m lo, av_below H m m lo.
Proof. intros H m lo a _. reflexivity. Qed.
Lemma av_trans : forall H m1 m2 m3 lo, av_below H m1 m2 lo -> av_below H m2 m3 lo -> av_below H m1 m3 lo.
Proof. intros H m1 m2 m3 lo H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.
Lemma av_of_sb : forall H m m' lo, same_below m m' lo -> av_below H m m' lo.
Proof. intros H m m' lo Hs a Ha. exact (aview_below H m m' lo a Hs Ha). Qed.
Lemma pg_vm_av : forall H m m' lo a (n : nat) v, av_below H m m' lo -> 0 <= a -> a + Z.of_nat n <= lo ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof.
intros H m m' lo a n v Hs H0 Hn Hv k Hk. rewrite (mbyte_of_aview tfibsegs H H m m' (a + Z.of_nat k)); [exact (Hv k Hk)|].
apply Hs. lia.
Qed.
Lemma pg_ra_av : forall H m m' p n, av_below H m m' alloc_ceiling -> 0 <= p -> p + n <= alloc_ceiling ->
  range_addressable (aview tfibsegs H m) SHADOW_OFF p n -> range_addressable (aview tfibsegs H m') SHADOW_OFF p n.
Proof.
intros H m m' p n Hs Hp Hn Hr x Hx. destruct (Hr x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
assert (Hx' : 0 <= x < alloc_ceiling) by lia.
rewrite (Hs _ (fsw_shadow_below x Hx')). exact Es.
Qed.
Lemma pg_glob_av : forall (W : world tfibsegs) m m' live peak cnt fail,
  av_below (w_H W) m m' alloc_ceiling -> fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hs (G1 & G2 & G3 & G4 & R).
pose proof asan_consts as (C1 & _).
assert (VB : forall a v, 0 <= a -> a + 8 <= alloc_ceiling -> val_mem tfibsegs (mrestrict (w_H W) m) a 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) m') a 8 v).
{ intros a v Ha Hb Hv. exact (pg_vm_av (w_H W) m m' alloc_ceiling a 8 v Hs Ha Hb Hv). }
unfold fs_glob, fs_glob_at. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VB; [lia | lia | exact G1]|].
split; [apply VB; [lia | lia | exact G2]|].
split; [apply VB; [lia | lia | exact G3]|].
split; [apply VB; [lia | lia | exact G4]|].
exact R.
Qed.
Lemma pg_arodata_av : forall (W : world tfibsegs) m m',
  av_below (w_H W) m m' alloc_ceiling -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m').
Proof.
intros W m m' Hs HR a Ha Ho He. pose proof asan_consts as (C1 & _).
assert (Hb : 0 <= a < alloc_ceiling).
{ destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in Hr; lia].
  assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | exact Hr]).
  pose proof (fs_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl. lia. }
rewrite (Hs a Hb). exact (HR a Ha Ho He).
Qed.
(* cstr_ok's clauses are all aview / mbyte reads below alloc_ceiling (the pattern of FSW_K.cstr_ok_below) *)
Lemma pg_cstr_av : forall (W : world tfibsegs) m m' p l,
  av_below (w_H W) m m' alloc_ceiling -> cstr_ok tfibsegs W m p l -> cstr_ok tfibsegs W m' p l.
Proof.
intros W m m' p l Hs H.
pose proof asan_consts as (C1 & _).
assert (AV : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a)
  by (intros a Ha; exact (Hs a Ha)).
unfold cstr_ok, cstr in H |- *.
repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
repeat match goal with |- _ /\ _ => split end; try assumption; lazymatch goal with
  | Hg : garr8 _ (mrestrict _ m) p (l ++ [0]) |- garr8 _ _ p (l ++ [0]) =>
      apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg); intros a Ha; rewrite length_app in Ha; cbn [length] in Ha;
      apply (mbyte_of_aview tfibsegs); apply AV; lia
  | Hra : range_addressable (aview _ _ m) ?o ?q ?n |- range_addressable (aview _ _ m') ?o ?q ?n =>
      intros x Hx; destruct (Hra x Hx) as (s & Hs1 & Hs2); exists s; split; [|exact Hs2];
      rewrite AV; [exact Hs1|]; unfold shadow_of_addr, SHADOW_OFF; lia
  | Hhv : shadow_hull_vis (aview _ _ m) ?q ?n |- shadow_hull_vis (aview _ _ m') ?q ?n =>
      intros s Hsr; rewrite AV; [exact (Hhv s Hsr)|]; unfold shadow_addr, SHADOW_OFF in Hsr; lia
  | Htl : forall a, _ -> aview _ _ m a <> None |- forall a, _ -> aview _ _ m' a <> None =>
      (* the word holding the NUL ends at or below alloc_ceiling: p + |l| + 1 <= alloc_ceiling and alloc_ceiling is
         4096-aligned (YM05.alloc_ceiling_value), so (p + |l|) / 8 * 8 + 8 <= alloc_ceiling (FSW_K.cstr_ok_below) *)
      intros a Ha; rewrite AV; [exact (Htl a Ha)|];
      pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia));
      pose proof (Z.div_mod (p + Z.of_nat (length l)) 8 ltac:(lia));
      pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia));
      pose proof (proj2 YM05.alloc_ceiling_value); lia
  end.
Qed.
(* a byte outside the image (no rom fallback) read the same is the same restricted byte *)
Lemma pg_raw : forall H m m' x, av_below H m m' alloc_ceiling -> 0 <= x < alloc_ceiling -> ~ in_img tfibsegs x ->
  mrestrict H m' (Z_to_bv 64 x) = mrestrict H m (Z_to_bv 64 x).
Proof.
intros H m m' x Hs Hx Hi. pose proof asan_consts as (C1 & _).
pose proof (Hs x Hx) as E. pose proof (seg_rom_none tfibsegs x ltac:(lia) Hi) as R.
unfold aview, mbyte in E. rewrite R in E.
destruct (mrestrict H m' (Z_to_bv 64 x)) as [b'|] eqn:E1, (mrestrict H m (Z_to_bv 64 x)) as [b|] eqn:E2;
  cbn [option_map] in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.


(* the bytes of a pobj are client bytes: below alloc_ceiling, not image *)
Lemma pg_pobj_client : forall ly S (W : world tfibsegs) mx md m v, AR tfibsegs B ly S W mx md ->
  pobj tfibsegs B ly S W m v -> forall x, v <= x < v + 56 -> 0 <= x < alloc_ceiling /\ ~ in_img tfibsegs x.
Proof.
intros ly S W mx md m v HAR HP x Hx.
destruct (fsw_pobj_low B ly S W mx md m v HAR HP) as (L1 & L2). split; [lia|].
destruct HP as [[((cid & pos & Hin & _ & _ & H1 & H2) & _) | ((b & n & Hin & H1 & H2) & _)] _].
- apply (frm_img tfibsegs B LAWS ly S W mx md cid pos x HAR Hin). unfold FSH_Fn_reader.fs_afobj in *. lia.
- apply (blk_img tfibsegs B LAWS ly S W mx md b n x HAR Hin). unfold HEAD in *. lia.
Qed.
Lemma pg_rblocks_av : forall ly S (W : world tfibsegs) mx md m m' UL, AR tfibsegs B ly S W mx md ->
  av_below (w_H W) m m' alloc_ceiling ->
  rd_blocks_ok tfibsegs B ly S W m UL -> rd_blocks_ok tfibsegs B ly S W m' UL.
Proof.
intros ly S W mx md m m' UL HAR Hs H a k Hak. pose proof (H a k Hak) as Hb. pose proof Hb as (Hin & Hal & Hn & Hv).
destruct (fsw_ablock_low B ly S W mx md _ _ HAR Hin) as (A1 & A2 & A3).
split; [exact Hin|]. split; [exact Hal|]. split; [exact Hn|].
apply (pg_vm_av (w_H W) m m' alloc_ceiling (a - HEAD) 8 k Hs); [unfold HEAD in *; lia | | exact Hv].
change (Z.of_nat 8) with 8. unfold HEAD in *. lia.
Qed.
Lemma pg_rnode_av : forall ly S (W : world tfibsegs) mx md m m' UL v t D, AR tfibsegs B ly S W mx md ->
  av_below (w_H W) m m' alloc_ceiling ->
  (forall x, v <= x < v + 56 -> 0 <= x < alloc_ceiling /\ ~ in_img tfibsegs x) ->
  rnode tfibsegs B ly S W m UL v t D -> rnode tfibsegs B ly S W m' UL v t D.
Proof.
intros ly S W mx md m m' UL v t D HAR Hs Hv (HN & HB & HI).
split; [|split; [exact (pg_rblocks_av ly S W mx md m m' UL HAR Hs HB) | exact HI]].
apply (PjStruct.pj_node_frame tfibsegs t (mrestrict (w_H W) m) (fun a k => In (a, k) UL)
  (mrestrict (w_H W) m') (fun a k => In (a, k) UL) v D HN); [intros a k Hak; exact (HI _ Hak)|].
intros x Hx. pose proof (u64_range x) as Hr.
assert (E : x = Z_to_bv 64 (bv_unsigned x)) by (symmetry; apply Z_to_bv_bv_unsigned).
rewrite E. destruct Hx as [Hx|((a & k) & Hb & Hx)].
- destruct (Hv _ Hx) as (H1 & H2). exact (pg_raw (w_H W) m m' (bv_unsigned x) Hs H1 H2).
- unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx.
  pose proof (HB a k (HI _ Hb)) as Hrb. pose proof Hrb as (Hin & _ & _ & _).
  destruct (fsw_rblock_low B ly S W mx md m a k HAR Hrb) as (R1 & R2).
  assert (Hrq : req_size (k + HEAD) = k + HEAD) by (unfold req_size, HEAD in *; destruct (Z.eqb_spec (k + 16) 0); lia).
  apply (pg_raw (w_H W) m m' (bv_unsigned x) Hs); [lia|].
  apply (blk_img tfibsegs B LAWS ly S W mx md (a - HEAD) (k + HEAD) _ HAR Hin). rewrite Hrq. unfold HEAD. lia.
Qed.

(* ================= the end of a live block lies at least 8 bytes below alloc_ceiling ================= *)
(* (rule 24 lookup 2026-10-28: `git grep 'p + req_size n + 8\|block_end_margin\|chunk_end'` over origin/main,
   ossv/recipes, ossv/candidates, release/pau-projects-recipes, three working branches: see the report;
   a primary chunk ends at or below its region's free array, inside ly_space + kSpaceSize; a secondary chunk keeps its
   redzone after the user bytes (YG0a secondary_geometry) *)
Lemma pg_block_margin : forall ly S (W : world tfibsegs) mx md p n, AR tfibsegs B ly S W mx md ->
  In (p, n) (ablocks B ly S) -> p + req_size n + 8 <= alloc_ceiling.
Proof.
intros ly S W mx md p n HAR Hin.
pose proof HAR as (M & _).
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn).
pose proof (chunk_facts B ly S _ k M Hk) as (Happ & Hceil & Hb16 & Huser & Hrz & Hrz16 & Hreq & Hext & Hcase).
pose proof (am_layout B ly S _ M) as LO.
pose proof (lo_space_in ly LO) as LS. pose proof (lo_high ly LO) as LH. unfold in_high in LH.
unfold ASAN_CEIL in *. rewrite <- Hu, Huser. rewrite <- Hn.
destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; try (cbn in Hcase; contradiction).
- destruct Hcase as (Hc & Hfp & Hcc & Hex & Hbase & Hx0 & Hxm & Hxa & Ham & Hmf).
  unfold region_base, region_off in *. rewrite !Z.shiftl_mul_pow2 in * by lia.
  unfold kSpaceSize, kFreeArrayOffset, kPrimResvSize in *. rewrite Hex in Hext. lia.
- destruct Hcase as (Ho & Hfp & Hbase & Hex & _).
  pose proof (secondary_geometry (ck_req k) ltac:(lia) Hfp) as (_ & Hns & _ & Hsm & _).
  pose proof (needed_primary_bounds (ck_req k) ltac:(lia)) as (Hnp & _).
  unfold ck_rz in *. lia.
Qed.

(* ================= a payload byte of a live block is no user-poisoned shadow byte (fs_heads: U holds only the
   16-byte heads at block starts) ================= *)
Lemma pg_payload_not_ush : forall ly S U (W : world tfibsegs) m md b n x,
  ARU tfibsegs B ly S U W m md -> fs_heads B ly S U -> In (b, n) (ablocks B ly S) -> b + 16 <= x < b + req_size n ->
  in_ush U (shadow_addr x) = false.
Proof.
intros ly S U W m md b n x H FH Hb Hx.
destruct (in_ush U (shadow_addr x)) eqn:E; [|reflexivity]. exfalso.
apply in_ush_spec in E as (r & Hr & Hs).
destruct (FH r Hr) as (E16 & m' & Hm' & M16).
destruct (upoison_ok_In B ly S U r (ARU_ok tfibsegs B ly S U W m md H) Hr) as (A8 & _).
destruct r as [q s]. cbn [fst snd] in *. subst s.
unfold shadow_addr in Hs. change (16 / 8) with 2 in Hs.
pose proof (Z.div_mod q 8 ltac:(lia)) as Dq. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Rx.
destruct (Z.eq_dec q b) as [->|NE]; [lia|].
pose proof (al_blocks _ _ LAWS ly S W (unpoison U m) md b n (ARU_AR tfibsegs B ly S U W m md H) Hb)
  as (_ & _ & _ & _ & _ & PW & _).
assert (I1 : In (q, req_size m') (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (q, m')); exact Hm').
assert (I2 : In (b, req_size n) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (b, n)); exact Hb).
destruct (pairwise_In2 zdisjoint _ _ _ PW I1 I2 ltac:(intros Eq; injection Eq; intros _ Eq'; exact (NE Eq')))
  as [D|D]; unfold zdisjoint in D; cbn [fst snd] in D; lia.
Qed.

(* ================= a member name (pj_cstr in a reader block) is a cstr_ok string, on the machine's memory ================= *)
Lemma pg_cstr_member : forall ly S U (W : world tfibsegs) m md UL x kx nm,
  ARU tfibsegs B ly S U W m md -> fs_heads B ly S U -> rd_blocks_ok tfibsegs B ly S W m UL ->
  PjStruct.pj_cstr tfibsegs (mrestrict (w_H W) m) (fun a k => In (a, k) UL) x kx nm -> cstr_ok tfibsegs W m x nm.
Proof.
intros ly S U W m md UL x kx nm H FH HB (Hin & Hlen & Hcb).
pose proof (HB x kx Hin) as Hrb. pose proof Hrb as (Hbl & Hal & Hk & _).
pose proof (ARU_AR tfibsegs B ly S U W m md H) as HAR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W (unpoison U m) md _ _ HAR Hbl) as (B16 & B4096 & Bceil & Bapp & Bpres & _ & Bmax).
assert (Hrq : req_size (kx + HEAD) = kx + HEAD) by (unfold req_size, HEAD in *; destruct (Z.eqb_spec (kx + 16) 0); lia).
rewrite Hrq in Bceil, Bapp. unfold HEAD in *.
pose proof (pg_block_margin ly S W (unpoison U m) md _ _ HAR Hbl) as Hmar. rewrite Hrq in Hmar. unfold HEAD in Hmar.
destruct (pg_garr8 _ _ _ Hcb) as (Hg & Hnz).
assert (Happ : forall a, x <= a < x + kx -> 0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)).
{ intros a Ha. unfold in_app, kLowShadowBeg, SHADOW_OFF, kHighMemBeg in *. lia. }
assert (Hc : cstr_ok tfibsegs W (unpoison U m) x nm).
{ split; [split; [|exact Hnz]|].
  { apply (garr8_frame tfibsegs _ _ x (nm ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
    destruct (Happ a ltac:(lia)) as (A1 & A2). apply (mbyte_unpoison_app B ly S U W m md a H A1 A2). }
  split; [lia|]. split; [lia|]. split; [unfold MALLOC_MAX in *; lia|].
  split; [unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia|].
  split.
  { apply (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U m) md (x - 16) (kx + 16) x _ HAR Hbl);
      rewrite ?Hrq; lia. }
  split.
  { destruct (al_shadow _ _ LAWS ly S W (unpoison U m) md _ _ HAR Hbl) as (_ & Hhv). rewrite Hrq in Hhv.
    apply (shadow_hull_vis_sub _ (x - 16) (kx + 16) x _ Hhv); lia. }
  intros a Ha. apply (block_word_tail_vis B ly S W (unpoison U m) md (x - 16) (kx + 16) HAR Hbl ltac:(lia)).
  pose proof (word_end_mono (x + Z.of_nat (length nm)) (x - 16 + (kx + 16) - 1) ltac:(lia)). lia. }
apply (cstr_ok_unpoison B ly S U W m md x nm H); [|exact Hc].
intros a Ha. apply (pg_payload_not_ush ly S U W m md (x - 16) (kx + 16) a H FH Hbl). rewrite Hrq. lia.
Qed.

(* the client home of a pobj is application memory (in_app, so apart from the shadow) *)
Lemma pg_pobj_app : forall ly S (W : world tfibsegs) mx md m v, AR tfibsegs B ly S W mx md ->
  pobj tfibsegs B ly S W m v -> in_app v 56.
Proof.
intros ly S W mx md m v HAR HP.
destruct HP as [[((cid & pos & Hin & _ & _ & H1 & H2) & _) | ((b & n & Hin & H1 & H2) & _)] _].
- destruct (frames_bounds tfibsegs B LAWS ly S W mx md cid pos HAR Hin) as (_ & _ & Ha).
  apply (in_app_sub _ _ v 56 Ha); lia.
- destruct (al_blocks _ _ LAWS ly S W mx md b n HAR Hin) as (_ & _ & _ & Ha & _).
  apply (in_app_sub _ _ v 56 Ha); unfold HEAD in *; lia.
Qed.
(* a run whose write windows all lie at or above lo leaves memory below lo unchanged *)
Lemma pg_sb_wr : forall E rs (m m' : word -> option byte) lo,
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> lo <= a) -> lo <= 2 ^ 64 -> same_below m m' lo.
Proof.
intros E rs m m' lo HF Hw H64 x Hx. apply HF. rewrite unsigned_lit_small by lia. intros Hin.
pose proof (Hw _ Hin). lia.
Qed.
(* an image cell and a client object do not overlap *)
Lemma pg_disj_img : forall lo1 hi1 lo2 hi2, (forall x, lo1 <= x < hi1 -> in_img tfibsegs x) ->
  (forall x, lo2 <= x < hi2 -> ~ in_img tfibsegs x) -> lo1 < hi1 -> lo2 < hi2 -> hi1 <= lo2 \/ hi2 <= lo1.
Proof.
intros lo1 hi1 lo2 hi2 H1 H2 L1 L2.
destruct (Z_le_gt_dec hi1 lo2) as [D|D]; [left; exact D|].
destruct (Z_le_gt_dec hi2 lo1) as [D'|D']; [right; exact D'|].
exfalso. apply (H2 (Z.max lo1 lo2)); [lia|]. apply H1. lia.
Qed.
(* one shadow entry from addressability and an application home *)
Lemma pg_shent : forall E m n base lo hi, U E fs_Bx = SHADOW_OFF -> U E (SOff n 0) = base -> lo <= hi ->
  range_addressable (rd_of tfibsegs m) SHADOW_OFF (base + lo) (hi - lo) -> in_app (base + lo) (hi - lo) ->
  shent_ok tfibsegs fs_Bx E m (mkSHE n lo hi).
Proof.
intros E m n base lo hi HB Hn Hlh Hra Happ. unfold shent_ok. cbn [she_m she_lo she_hi]. rewrite HB, Hn.
split; [exact Hra|]. unfold app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hn. intros a Ha.
rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma pg_afact : forall E n v lo hi al, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  v mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E n (mkAF lo hi al).
Proof.
intros E n v lo hi al Hn Hv Hr Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hn.
rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma pg_U_bx : forall regs xs, U (Ereg regs (fs_extraT ++ xs)) fs_Bx = SHADOW_OFF.
Proof.
intros regs xs. unfold fs_Bx. apply U_atom; [|unfold SHADOW_OFF; lia].
change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.
End g.

(* ================= the symbolic states of the walk ================= *)
(* the upper bound of every client pointer: alloc_ceiling <= 0x7fffff800000 (YM05 RunCeil alloc_ceiling_val) *)
Definition CEIL : Z := 0x7fffff800000.
(* the entry with o <> 0: the object region at a0 (atom 10) holds the tag tg (a literal: the walk splits on the tree's
   constructor), keys at +32 (xatom 0 = atom 33) and n at +40 (atom 34, or the literal 0 for an empty object) *)
Definition es_obj (tg : Z) (nv : sv) : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 56 0 0
    [YP09.mkChunk 0 (CVal 4 (SLit tg)); YP09.mkChunk 32 (CVal 8 (SOff 33 0)); YP09.mkChunk 40 (CVal 8 nv)].
Definition es_gf (big : bool) : list (nat * afact) :=
  (10%nat, mkAF 4096 CEIL 3) :: (if big then [(33%nat, mkAF 4112 CEIL 4); (34%nat, mkAF 1 (2 ^ 54) 0)] else []).
Definition es_ss (tg : Z) (nv : sv) (big : bool) : sstate := fss0T_args A_pj_get 96 [es_obj tg nv] (es_gf big).
Definition es_SH : list shent := [mkSHE 10 0 56].
(* the loop head 0x83948 and the return point 0x83984 of strcmp: every register its own atom, except s3 = the shadow
   base (atom 32, the shape the token engine matches), s8 = 1 and s9 = s2 (both keys + 8 i, atom 18); the frame's saved
   ra, s0..s9 are xatoms 0..10 (atoms 33..43), the object's kids xatom 11 (44), keys[i] xatom 12 (45); s0 = obj
   (atom 8), s4 = -56 i (atom 20), s5 = i (atom 21), s6 = n (atom 22), s7 = keys (atom 23) *)
Definition lp_cs : list YP09.chunk :=
  [YP09.mkChunk 88 (CVal 8 (SOff 33 0)); YP09.mkChunk 80 (CVal 8 (SOff 34 0)); YP09.mkChunk 72 (CVal 8 (SOff 35 0));
   YP09.mkChunk 64 (CVal 8 (SOff 36 0)); YP09.mkChunk 56 (CVal 8 (SOff 37 0)); YP09.mkChunk 48 (CVal 8 (SOff 38 0));
   YP09.mkChunk 40 (CVal 8 (SOff 39 0)); YP09.mkChunk 32 (CVal 8 (SOff 40 0)); YP09.mkChunk 24 (CVal 8 (SOff 41 0));
   YP09.mkChunk 16 (CVal 8 (SOff 42 0)); YP09.mkChunk 8 (CVal 8 (SOff 43 0))].
Definition lp_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms 19%bv (SOff 32 0)) 24%bv (SLit 1)) 25%bv (SOff 18 0).
Definition lp_mem : smem :=
  [fstk_ret 96 lp_cs;
   YP09.mkRegion (Some 8%nat) 0 56 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 44 0))];
   YP09.mkRegion (Some 18%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 45 0))]].
Definition lp_atoms : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (8%nat, mkAF 4096 CEIL 3); (18%nat, mkAF 4096 CEIL 3); (23%nat, mkAF 4112 CEIL 0)].
Definition lp_conds : list acond :=
  [mkAC BC_EQ (SAlu ALU_SRL (SOff 21 0) (SLit 60)) (SLit 0); mkAC BC_GEU (SOff 18 0) (SOff 23 0)].
Definition lp_ss : sstate := mkSS 0x83948 lp_regs lp_mem None (mkFacts lp_atoms lp_conds []).
(* after strcmp (0x83984): the hit (a0 = 0) adds kids >= 4112 (atom 44) and the three UBSan conditions of the hit arm
   (0x83a04 the pointer-overflow null test of kids + 56 i, 0x83a08 its wrap test, 0x83a20 the signed-overflow test of
   i * 56), each in the exact operand shape the engine builds (MEASURED: the run from the hit state with lp_conds only
   stops at 0x83a04 on `SR_branch BC_EQ (SLit 1) (SAlu ALU_SLTU hA2 (SLit 1))`); a miss adds a0 >= 1 (atom 10) and
   n = i + 1 (the last member: 0x83998 `bne s6, s5` falls through) or n <> i + 1 (members left: back to 0x83948) *)
Definition hM : sv := SMd M_MUL (SOff 21 0) (SLit 56).
Definition hA2 : sv := SAlu ALU_ADD hM (SOff 44 0).
Definition hX : sv := SAlu ALU_XOR (SMd M_MULH (SOff 21 0) (SLit 56)) (SAlu ALU_SRA hM (SLit 63)).
Definition hit_conds : list acond :=
  [mkAC BC_NE (SLit 1) (SAlu ALU_SLTU hA2 (SLit 1)); mkAC BC_GEU hA2 (SOff 44 0);
   mkAC BC_EQ (SAlu ALU_SLTU (SLit 0) hX) (SLit 0)].
Definition hit_G : facts := mkFacts (lp_atoms ++ [(44%nat, mkAF 4112 CEIL 0)]) (lp_conds ++ hit_conds) [].
Definition miss_G (last : bool) : facts :=
  mkFacts (lp_atoms ++ [(10%nat, mkAF 1 (2 ^ 64 - 1) 0)])
    (lp_conds ++ [mkAC (if last then BC_EQ else BC_NE) (SOff 22 0) (SOff 21 1)]) [].
Definition lp_SH : list shent := [mkSHE 8 0 56; mkSHE 18 0 8].

(* ================= the UBSan conditions the engine is given, from the machine values ================= *)
Lemma pg_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64) with 18446744073709551616. change (18446744073709551616 / 2) with 9223372036854775808.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma pg_conds_app : forall E l1 l2, conds_ok E l1 -> conds_ok E l2 -> conds_ok E (l1 ++ l2).
Proof.
intros E l1. induction l1 as [|c l1 IH]; intros l2 H1 H2; [exact H2|].
destruct H1 as [Hc H1]. split; [exact Hc | apply IH; assumption].
Qed.
(* the loop head's two (0x83954: i >> 60 = 0, the overflow test of 8 i; 0x83958: keys + 8 i >= keys, the wrap test) *)
Lemma pg_lp_conds : forall R xs P ky i,
  YK11.getr R 18 = Z_to_bv 64 P -> YK11.getr R 23 = Z_to_bv 64 ky -> 0 <= ky /\ ky <= P /\ P < 2 ^ 64 ->
  YK11.getr R 21 = Z_to_bv 64 i -> 0 <= i < 2 ^ 60 ->
  conds_ok (Ereg R (fs_extraT ++ xs)) lp_conds.
Proof.
intros R xs P ky i H18 H23 HP H21 Hi.
set (E := Ereg R (fs_extraT ++ xs)).
assert (U18 : U E (SOff 18 0) = P) by (apply U_atom; [subst E; rewrite (ew_Ereg_nat R _ 18 18%bv eq_refl); exact H18 | lia]).
assert (U23 : U E (SOff 23 0) = ky) by (apply U_atom; [subst E; rewrite (ew_Ereg_nat R _ 23 23%bv eq_refl); exact H23 | lia]).
assert (U21 : U E (SOff 21 0) = i) by (apply U_atom; [subst E; rewrite (ew_Ereg_nat R _ 21 21%bv eq_refl); exact H21 | lia]).
cbn [lp_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
split; [|split; [|exact I]].
- rewrite branch_eq_U, U_SAlu, U21, !U_SLit. cbn [zalu_raw].
  change (Z.land (zcanon 60) 63) with 60. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
- rewrite branch_geu_U, U18, U23. apply negb_true_iff, Z.ltb_ge. lia.
Qed.
(* the hit arm's three (0x83a04, 0x83a08, 0x83a20) *)
Lemma pg_hit_conds : forall E i kids, ew E 21 = Z_to_bv 64 i -> ew E 44 = Z_to_bv 64 kids ->
  0 <= i <= 2 ^ 54 -> 1 <= kids -> kids + 56 * i < 2 ^ 63 ->
  conds_ok E hit_conds.
Proof.
intros E i kids H21 H44 Hi Hk Hki.
assert (U21 : U E (SOff 21 0) = i) by (apply U_atom; [exact H21 | lia]).
assert (U44 : U E (SOff 44 0) = kids) by (apply U_atom; [exact H44 | lia]).
assert (UM : U E hM = 56 * i).
{ unfold hM. rewrite U_SMd, U21, U_SLit. cbn [zmd_raw]. change (zcanon 56) with 56.
  rewrite zcanon_id by (unfold M64; lia). lia. }
assert (UA : U E hA2 = kids + 56 * i).
{ unfold hA2. rewrite U_SAlu, UM, U44. cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia. }
assert (UH : U E (SMd M_MULH (SOff 21 0) (SLit 56)) = 0).
{ rewrite U_SMd, U21, U_SLit. cbn [zmd_raw]. change (zcanon 56) with 56.
  rewrite (pg_swrap_small i) by lia. rewrite (pg_swrap_small 56) by lia. change (Z.of_N 64) with 64.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
assert (US : U E (SAlu ALU_SRA hM (SLit 63)) = 0).
{ rewrite U_SAlu, UM, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 63) 63) with 63.
  rewrite (pg_swrap_small (56 * i)) by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
assert (UX : U E hX = 0) by (unfold hX; rewrite U_SAlu, UH, US; reflexivity).
cbn [hit_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
split; [|split; [|split; [|exact I]]].
- rewrite branch_ne_U, (U_SAlu E ALU_SLTU), UA, !U_SLit. cbn [zalu_raw]. change (zcanon 1) with 1.
  destruct (Z.ltb_spec (kids + 56 * i) 1) as [L|L]; [lia|]. reflexivity.
- rewrite branch_geu_U, UA, U44. apply negb_true_iff, Z.ltb_ge. lia.
- rewrite branch_eq_U, (U_SAlu E ALU_SLTU), UX, !U_SLit. reflexivity.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* the image facts (lib/B/FSH_Rt.v; the reader Section's IMG): rom_view at the strcmp call. Owner: S0 states the
   interface (lib/B/FSH_Rt.v fs_img_facts), RELOC proves it once for build B's asyms *)
Hypothesis IMG : fs_img_facts tfibsegs B.
(* owner RELOC: image B's shadow-offset GOT word 0x9fc10 and cell 0xa8438 (lib/B/FSH_Base.v FsShadowSyms) *)
Hypothesis HSS : FsShadowSyms B.

(* ---- the entry state with o <> 0 ---- *)
Lemma pg_entry_st : forall ly S U (W : world tfibsegs) regs mem md ch o tg nv big keys nval,
  afn_preU tfibsegs B STK_pj_get ly S U W regs mem md ch ->
  YK11.getr regs 10 = w64 o -> 4096 <= o -> o mod 8 = 0 -> o + 56 <= alloc_ceiling ->
  (forall x, o <= x < o + 56 -> ~ in_img tfibsegs x) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) o 4 tg -> 0 <= tg < 2 ^ 32 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (o + 32) 8 keys -> 0 <= keys < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (o + 40) 8 nval -> 0 <= nval < 2 ^ 64 ->
  sv_denot (Ereg regs (fs_extraT ++ [Z_to_bv 64 keys; Z_to_bv 64 nval])) nv = Z_to_bv 64 nval ->
  atoms_ok (Ereg regs (fs_extraT ++ [Z_to_bv 64 keys; Z_to_bv 64 nval])) (es_gf big) ->
  st_ok tfibsegs (Ereg regs (fs_extraT ++ [Z_to_bv 64 keys; Z_to_bv 64 nval])) (es_ss tg nv big)
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 A_pj_get) mem (YK11.seg_rom tfibsegs))).
Proof.
intros ly S U W regs mem md ch o tg nv big keys nval HPRE H10 Ho4 Ho8 HoC Himg Htg Rtg Hky Rky Hnv Rnv Env Hgf.
pose proof HSS as [Hgot Hcell].
change FS_GOT_shadow with tfib_D_GOT_asan_shadow_memory_dynamic_address in Hgot.
change FS_shadow_cell with tfib_D_asan_shadow_memory_dynamic_address in Hcell.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
set (E := Ereg regs (fs_extraT ++ [Z_to_bv 64 keys; Z_to_bv 64 nval])).
assert (E10 : bv_unsigned (ew E 10) = o).
{ subst E. rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10. unfold w64. apply unsigned_lit_small. lia. }
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (FS : STK_pj_get = ltac:(let v := eval vm_compute in (STK_pj_get) in exact v)) by (vm_compute; reflexivity). rewrite FS in Hceil.
apply (fsw_entryT_argsX B STK_pj_get 96 ly S U W regs mem md ch A_pj_get [es_obj tg nv] (es_gf big)
  [Z_to_bv 64 keys; Z_to_bv 64 nval] Hgot Hcell HPRE ltac:(rewrite FS; lia) ltac:(vm_compute; reflexivity)).
- constructor; [|constructor]. unfold region_ok, es_obj.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E. rewrite E10.
  split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
  constructor; [|constructor; [|constructor; [|constructor]]].
  + apply (chunk_ok_val tfibsegs E _ o 0 4 (SLit tg) tg); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Htg].
  + apply (chunk_ok_val tfibsegs E _ o 32 8 (SOff 33 0) keys); [| cbn; lia | cbn; lia | exact Hky].
    rewrite fsw_SOff0. change 33%nat with (32 + 1)%nat. subst E. rewrite ew_Ereg_extra. reflexivity.
  + apply (chunk_ok_val tfibsegs E _ o 40 8 nv nval); [exact Env | cbn; lia | cbn; lia | exact Hnv].
- apply pairwise_disjoint_of_extents.
  unfold fsT_regions_args, fsT_regions, fs_got_region, fs_bcell_region, fstk, es_obj, extent_of_region.
  cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite E2, E10.
  assert (G1 : forall x, tfib_D_GOT_asan_shadow_memory_dynamic_address <= x < tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 -> in_img tfibsegs x)
    by (intros x Hx; apply (seg_covers_img tfib_D_GOT_asan_shadow_memory_dynamic_address 8 x); [vm_compute; reflexivity | exact Hx]).
  assert (G2 : forall x, tfib_D_asan_shadow_memory_dynamic_address <= x < tfib_D_asan_shadow_memory_dynamic_address + 8 -> in_img tfibsegs x)
    by (intros x Hx; apply (seg_covers_img tfib_D_asan_shadow_memory_dynamic_address 8 x); [vm_compute; reflexivity | exact Hx]).
  pose proof (pg_disj_img _ _ o (o + 56) G1 Himg ltac:(lia) ltac:(lia)) as D1.
  pose proof (pg_disj_img _ _ o (o + 56) G2 Himg ltac:(lia) ltac:(lia)) as D2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- exact Hgf.
Qed.

(* ---- segment E0: o = 0 (0x838c4 `beqz a0` taken, the epilogue 0x839a0, ret); no check on this path ---- *)
Lemma pg_seg_null : forall ly S U (W : world tfibsegs) regs mem md ch Qp,
  afn_preU tfibsegs B STK_pj_get ly S U W regs mem md ch -> YK11.getr regs 10 = w64 0 ->
  (forall regs' mem' md', aregs_preserved regs regs' -> YK11.getr regs' 10 = w64 0 -> same_below mem mem' alloc_ceiling ->
     Qp ly S W regs' mem' md') ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_pj_get regs mem md)
    (fpostU tfibsegs B STK_pj_get (spZ regs) [] regs ly S U W mem md 0 U Qp).
Proof.
intros ly S U W regs mem md ch Qp HPRE H10 HQ.
pose proof HPRE as (HAP & _ & _). pose proof HAP as (HAR & Hra & _).
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : STK_pj_get = ltac:(let v := eval vm_compute in (STK_pj_get) in exact v)) by (vm_compute; reflexivity).
pose proof (fsw_entry B STK_pj_get 96 ly S U W regs mem md ch A_pj_get HPRE ltac:(rewrite FS; lia)
  ltac:(vm_compute; reflexivity)) as HS0'.
pose proof (st_ok_set_reg tfibsegs _ _ _ 10%bv (SLit 0) HS0' ltac:(intros Hx; discriminate Hx)
  ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite H10; reflexivity)) as HS.
clear HS0'.
pose proof (ajournal_init tfibsegs B STK_pj_get [] ly S W regs (unpoison U mem) md ch HAP) as HJ.
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPRE) as HARU.
assert (Usp : bv_unsigned (ew (Ereg regs []) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_pj_get) with (Z_to_bv 64 A_pj_get).
fsw_aj_runU pj_get_tbl_ok HS HJ HARU.
{ cbn [ss_mem fss0]. eapply awr_ok_cons_stack with (n := 2%nat);
    [reflexivity | exact Usp | cbn; rewrite FS; lia | cbn; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ =>
  pose proof (fsw_reg_atom _ regs [] _ m 1%bv 1%bv 1 HS ltac:(vm_compute; reflexivity) eq_refl) as R1;
  pose proof (fsw_reg_lit _ _ _ m 10%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R10;
  assert (HP : aregs_preserved regs (ms_regs m))
    by (eapply (aregs_preserved_of_st_ok tfibsegs _ _ _ _ regs [] HS); [apply env_agree_refl | vm_compute; reflexivity]);
  assert (SB : same_below mem (ms_mem m) alloc_ceiling)
    by (apply (pg_sb_wr _ _ mem (ms_mem m) alloc_ceiling HF); [|lia];
        intros a (r & Hin & Hr); cbn in Hin; destruct Hin as [<-|[]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fstk] in Hr; rewrite Usp in Hr; lia)
end.
eapply (fsw_retU B pj_get_tbl pj_get_tbl_ok W _ _ _ _ STK_pj_get (spZ regs) [] regs ly S U W mem md ly S U 0 Qp HS);
  [reflexivity | vm_compute; reflexivity | rewrite R1; exact Hra | exact HJ | exact HARU | exact HP |].
intros mt. apply HQ; [exact HP | exact R10 | exact SB].
Qed.

(* ---- segment E1: o <> 0 and the node is not an object (tag 0..5), or an empty object (tag 6, n = 0): the UBSan
   alignment test of obj (0x838d0, decided by atom 10's 8-alignment), the shadow check of obj (0x838f0, covered), the tag
   test 0x838fc, for the object the shadow check of obj + 40 (0x83910, covered) and the n test 0x83918; a0 = 0 at
   0x8399c, epilogue, ret ---- *)
Lemma pg_seg_early : forall ly S U (W : world tfibsegs) regs mem md ch o tg nv keys nval Qp,
  In (tg, nv) [(0, SOff 34 0); (1, SOff 34 0); (2, SOff 34 0); (3, SOff 34 0); (4, SOff 34 0); (5, SOff 34 0); (6, SLit 0)] ->
  afn_preU tfibsegs B STK_pj_get ly S U W regs mem md ch ->
  YK11.getr regs 10 = w64 o -> 4096 <= o -> o mod 8 = 0 -> o + 56 <= alloc_ceiling ->
  (forall x, o <= x < o + 56 -> ~ in_img tfibsegs x) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF o 56 -> in_app o 56 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) o 4 tg ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (o + 32) 8 keys -> 0 <= keys < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (o + 40) 8 nval -> 0 <= nval < 2 ^ 64 -> (tg = 6 -> nval = 0) ->
  (forall regs' mem' md', aregs_preserved regs regs' -> YK11.getr regs' 10 = w64 0 -> same_below mem mem' alloc_ceiling ->
     Qp ly S W regs' mem' md') ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_pj_get regs mem md)
    (fpostU tfibsegs B STK_pj_get (spZ regs) [] regs ly S U W mem md 0 U Qp).
Proof.
intros ly S U W regs mem md ch o tg nv keys nval Qp Hin HPRE H10 Ho4 Ho8 HoC Himg Hra0 Happ Htg Hky Rky Hnv Rnv H6 HQ.
pose proof HPRE as (HAP & _ & _). pose proof HAP as (HAR & Hra & _).
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : STK_pj_get = ltac:(let v := eval vm_compute in (STK_pj_get) in exact v)) by (vm_compute; reflexivity).
set (xs := [Z_to_bv 64 keys; Z_to_bv 64 nval]).
set (E := Ereg regs (fs_extraT ++ xs)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (U10 : YP0e.U E (SOff 10 0) = o).
{ apply U_atom; [|lia]. subst E. rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl). exact H10. }
assert (Hnv' : sv_denot E nv = Z_to_bv 64 nval).
{ destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]; injection E1 as <- <-;
    [..|rewrite (H6 eq_refl); reflexivity];
    rewrite fsw_SOff0; change 34%nat with (32 + 2)%nat; subst E; rewrite ew_Ereg_extra; reflexivity. }
assert (Rtg : 0 <= tg < 2 ^ 32) by (destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]; injection E1 as <- <-; lia).
assert (HoCE : 4096 <= o <= CEIL) by (unfold CEIL; pose proof alloc_ceiling_val as (_ & AC); lia).
assert (Hgf : atoms_ok E (es_gf false)).
{ cbn [es_gf atoms_ok]. split; [|exact I].
  apply (pg_afact E 10 o); [subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10 | lia | exact HoCE
    | change (2 ^ 3) with 8; exact Ho8 | lia]. }
pose proof (pg_entry_st ly S U W regs mem md ch o tg nv false keys nval HPRE H10 Ho4 Ho8 HoC Himg Htg Rtg Hky Rky Hnv Rnv
  Hnv' Hgf) as HS.
assert (SHOK : sh_ok tfibsegs fs_Bx es_SH E (mrestrict (w_H W) mem)).
{ constructor; [|constructor]. apply (pg_shent E _ 10 o 0 56); [apply pg_U_bx | exact U10 | lia | | ];
    rewrite Z.add_0_r, Z.sub_0_r; [exact Hra0 | exact Happ]. }
pose proof (ajournal_init tfibsegs B STK_pj_get [] ly S W regs (unpoison U mem) md ch HAP) as HJ.
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPRE) as HARU.
unfold cfg_at. change (w64 A_pj_get) with (Z_to_bv 64 A_pj_get).
destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]; injection E1 as <- <-; clear Hnv' Rtg H6.
all: fsw_aj_run_tokU pj_get_tbl_ok HS HJ HARU SHOK fs_Bspan;
  [ cbn [ss_mem es_ss fss0T_args fsT_regions_args fsT_regions app];
    eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact Usp | cbn; rewrite FS; lia | cbn; lia |];
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil
  | lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ =>
      pose proof (fsw_reg_atom _ regs _ _ m 1%bv 1%bv 1 HS ltac:(vm_compute; reflexivity) eq_refl) as R1;
      pose proof (fsw_reg_lit _ _ _ m 10%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R10;
      assert (HP : aregs_preserved regs (ms_regs m))
        by (eapply (aregs_preserved_of_st_ok tfibsegs _ _ _ _ regs _ HS); [apply env_agree_refl | vm_compute; reflexivity]);
      assert (SB : same_below mem (ms_mem m) alloc_ceiling)
        by (apply (pg_sb_wr _ _ mem (ms_mem m) alloc_ceiling HF); [|lia];
            intros a (r & Hr0 & Hr); cbn in Hr0; destruct Hr0 as [<-|[<-|[<-|[<-|[]]]]];
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fstk fs_got_region fs_bcell_region es_obj] in Hr;
            [rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl) in Hr; change (bv_unsigned (YK11.getr regs 2)) with (spZ regs) in Hr
            | ..]; lia)
    end;
    eapply (fsw_retU B pj_get_tbl pj_get_tbl_ok W _ _ _ _ STK_pj_get (spZ regs) [] regs ly S U W mem md ly S U 0 Qp HS);
      [reflexivity | vm_compute; reflexivity | rewrite R1; exact Hra | exact HJ | exact HARU | exact HP |];
    intros mt; apply HQ; [exact HP | exact R10 | exact SB] ].
Qed.

(* ---- the loop-head / return-point state from machine facts ---- *)
Definition pg_saved (regs0 : bvmap 5 word) : list word :=
  [YK11.getr regs0 1; YK11.getr regs0 8; YK11.getr regs0 9; YK11.getr regs0 18; YK11.getr regs0 19;
   YK11.getr regs0 20; YK11.getr regs0 21; YK11.getr regs0 22; YK11.getr regs0 23; YK11.getr regs0 24;
   YK11.getr regs0 25].
Definition pg_lxs (regs0 : bvmap 5 word) (kids key : Z) : list word :=
  fs_extraT ++ pg_saved regs0 ++ [Z_to_bv 64 kids; Z_to_bv 64 key].
Lemma pg_lp_cs : lp_cs = map (fun j => YP09.mkChunk (88 - 8 * Z.of_nat j) (CVal 8 (SOff (33 + j) 0))) (seq 0 11).
Proof. reflexivity. Qed.
Lemma pg_lp_build : forall (W : world tfibsegs) R m pc sr G regs0 sp0 o P kids key,
  regs_ok (Ereg R (pg_lxs regs0 kids key)) sr R -> facts_ok (Ereg R (pg_lxs regs0 kids key)) G ->
  bv_unsigned (YK11.getr R 2) = sp0 - 96 -> alloc_ceiling + 96 <= sp0 <= 2 ^ 47 ->
  (forall a, sp0 - 96 <= a < sp0 -> writable_at tfibsegs (mrestrict (w_H W) m) a) ->
  (forall j, (j < 11)%nat -> val_mem tfibsegs (mrestrict (w_H W) m) (sp0 - 8 - 8 * Z.of_nat j) 8
     (bv_unsigned (nth j (pg_saved regs0) (Z_to_bv 64 0)))) ->
  YK11.getr R 8 = Z_to_bv 64 o -> 0 <= o -> o + 56 <= alloc_ceiling ->
  val_mem tfibsegs (mrestrict (w_H W) m) (o + 24) 8 kids -> 0 <= kids < 2 ^ 64 ->
  YK11.getr R 18 = Z_to_bv 64 P -> 0 <= P -> P + 8 <= alloc_ceiling ->
  val_mem tfibsegs (mrestrict (w_H W) m) P 8 key -> 0 <= key < 2 ^ 64 ->
  (o + 56 <= P \/ P + 8 <= o) ->
  st_ok tfibsegs (Ereg R (pg_lxs regs0 kids key)) (mkSS pc sr lp_mem None G)
    (restrict (w_H W) (YK11.mkst R (Z_to_bv 64 pc) m (YK11.seg_rom tfibsegs))).
Proof.
intros W R m pc sr G regs0 sp0 o P kids key Hsr HG Hsp Hsp0 Hw Hfr H8 Ho0 HoC Hkd Rkd H18 HP0 HPC Hky Rky Hdj.
pose proof asan_consts as (C1 & _).
set (E := Ereg R (pg_lxs regs0 kids key)).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 96) by (subst E; rewrite (ew_Ereg_nat R _ 2 2%bv eq_refl); exact Hsp).
assert (E8 : bv_unsigned (ew E 8) = o)
  by (subst E; rewrite (ew_Ereg_nat R _ 8 8%bv eq_refl), H8; apply unsigned_lit_small; lia).
assert (E18 : bv_unsigned (ew E 18) = P)
  by (subst E; rewrite (ew_Ereg_nat R _ 18 18%bv eq_refl), H18; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); [exact Hsr | vm_compute; reflexivity | | | exact HG].
- constructor; [|constructor; [|constructor; [|constructor]]].
  + unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    fold E. rewrite E2. split; [lia|]. split; [lia|]. split; [intros off Hoff; apply Hw; lia|].
    rewrite pg_lp_cs. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj).
    apply in_seq in Hj. cbn [Nat.add] in Hj.
    apply (chunk_ok_val tfibsegs E _ (sp0 - 96) (88 - 8 * Z.of_nat j) 8 (SOff (33 + j) 0)
      (bv_unsigned (nth j (pg_saved regs0) (Z_to_bv 64 0)))).
    * rewrite fsw_SOff0. replace (33 + j)%nat with (32 + S j)%nat by lia. subst E. rewrite ew_Ereg_extra.
      unfold pg_lxs. cbn [nth fs_extraT app]. rewrite app_nth1 by (cbn [length pg_saved]; lia).
      symmetry. apply Z_to_bv_bv_unsigned.
    * apply u64_range.
    * cbn; lia.
    * replace (sp0 - 96 + (88 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia. exact (Hfr j ltac:(lia)).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    fold E. rewrite E8. split; [lia|]. split; [lia|]. split; [intros off Hoff; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs E _ o 24 8 (SOff 44 0) kids); [| cbn; lia | cbn; lia | exact Hkd].
    rewrite fsw_SOff0. change 44%nat with (32 + 12)%nat. subst E. rewrite ew_Ereg_extra. reflexivity.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    fold E. rewrite E18. split; [lia|]. split; [lia|]. split; [intros off Hoff; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs E _ P 0 8 (SOff 45 0) key); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Hky].
    rewrite fsw_SOff0. change 45%nat with (32 + 13)%nat. subst E. rewrite ew_Ereg_extra. reflexivity.
- apply pairwise_disjoint_of_extents. unfold lp_mem, fstk_ret, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite E2, E8, E18.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ---- register values the engine leaves as expressions ---- *)
(* the hit's answer (MEASURED: a0 at the final ret, from `sub a0, a0, s4` at 0x83a24 with s4 = -56 i) *)
Lemma pg_U_hit : forall E i kids, ew E 20 = Z_to_bv 64 (-56 * i) -> ew E 44 = Z_to_bv 64 kids ->
  0 <= kids < 2 ^ 64 -> 0 <= kids + 56 * i < 2 ^ 64 ->
  YP0e.U E (SAlu ALU_ADD (SMd M_MUL (SOff 20 0) (SLit (-1))) (SOff 44 0)) = kids + 56 * i.
Proof.
intros E i kids H20 H44 Hk Hki. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom E 44 kids H44 Hk), U_SLit, U_SOff, H20, Z.add_0_r, Z_to_bv_unsigned.
unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.add_mod_idemp_l by lia. rewrite Z.mod_mod by lia.
rewrite <- (Z.add_mod_idemp_l ((-56 * i) mod 2 ^ 64 * (-1 mod 2 ^ 64)) kids (2 ^ 64)) by lia.
rewrite <- Z.mul_mod by lia. rewrite Z.add_mod_idemp_l by lia.
replace (-56 * i * -1 + kids) with (kids + 56 * i) by lia.
apply Z.mod_small. exact Hki.
Qed.
(* two states over the same env name the same value in a register they give the same expression *)
Lemma pg_same_reg : forall H E ss1 ss2 ms1 ms2 (r : bv 5),
  st_ok tfibsegs E ss1 (restrict H ms1) -> st_ok tfibsegs E ss2 (restrict H ms2) ->
  sr_get (ss_regs ss1) r = sr_get (ss_regs ss2) r -> YK11.getr (ms_regs ms1) r = YK11.getr (ms_regs ms2) r.
Proof.
intros H E ss1 ss2 ms1 ms2 r H1 H2 Er.
rewrite (st_ok_restrict_reg tfibsegs H E ss1 ms1 r H1), (st_ok_restrict_reg tfibsegs H E ss2 ms2 r H2), Er. reflexivity.
Qed.
(* lp_regs is sound over a machine whose s3 is the shadow base, s8 = 1 and s9 = s2 *)
Lemma pg_lp_regs_ok : forall R xs,
  YK11.getr R 19 = Z_to_bv 64 SHADOW_OFF -> YK11.getr R 24 = Z_to_bv 64 1 -> YK11.getr R 25 = YK11.getr R 18 ->
  regs_ok (Ereg R (fs_extraT ++ xs)) lp_regs R.
Proof.
intros R xs H19 H24 H25.
assert (E32 : ew (Ereg R (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
unfold lp_regs.
apply regs_ok_pin; [| intros Hx; discriminate Hx | rewrite fsw_SOff0, (ew_Ereg_nat R _ 18 18%bv eq_refl); exact H25].
apply regs_ok_pin; [| intros Hx; discriminate Hx | cbn [sv_denot]; exact H24].
apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx | rewrite fsw_SOff0, E32; exact H19].
Qed.
Lemma pg_lp_atoms : forall R xs sp0 o P ky,
  bv_unsigned (YK11.getr R 2) = sp0 - 96 -> 2 ^ 46 <= sp0 - 96 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
  YK11.getr R 8 = Z_to_bv 64 o -> 4096 <= o <= CEIL -> o mod 8 = 0 ->
  YK11.getr R 18 = Z_to_bv 64 P -> 4096 <= P <= CEIL -> P mod 8 = 0 ->
  YK11.getr R 23 = Z_to_bv 64 ky -> 4112 <= ky <= CEIL ->
  atoms_ok (Ereg R (fs_extraT ++ xs)) lp_atoms.
Proof.
intros R xs sp0 o P ky H2 Hs1 Hs2 Hs3 H8 Ho Ho8 H18 HP HP8 H23 Hk.
cbn [lp_atoms atoms_ok]. repeat split.
all: try (unfold afact_ok; cbn [af_lo af_hi af_al2]).
all: rewrite ?(ew_Ereg_nat R _ 2 2%bv eq_refl), ?(ew_Ereg_nat R _ 8 8%bv eq_refl), ?(ew_Ereg_nat R _ 18 18%bv eq_refl),
  ?(ew_Ereg_nat R _ 23 23%bv eq_refl), ?H8, ?H18, ?H23, ?unsigned_lit_small by (unfold CEIL in *; lia).
all: try (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; cbn [nth fs_extraT app];
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia)).
all: try rewrite H2.
all: change (2 ^ 4) with 16 in *; change (2 ^ 3) with 8 in *; rewrite ?Z.pow_0_r, ?Z.mod_1_r;
  unfold CEIL, SHADOW_OFF in *; try lia.
all: rewrite Zminus_mod, Hs3; reflexivity.
Qed.
Lemma pg_lp_shok : forall (W : world tfibsegs) R xs m o P,
  YK11.getr R 8 = Z_to_bv 64 o -> 0 <= o < 2 ^ 64 -> YK11.getr R 18 = Z_to_bv 64 P -> 0 <= P < 2 ^ 64 ->
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF o 56 -> in_app o 56 ->
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF P 8 -> in_app P 8 ->
  sh_ok tfibsegs fs_Bx lp_SH (Ereg R (fs_extraT ++ xs)) (mrestrict (w_H W) m).
Proof.
intros W R xs m o P H8 Ho H18 HP Hro Hoa Hrp Hpa.
constructor; [|constructor; [|constructor]].
- apply (pg_shent _ _ 8 o 0 56); [apply pg_U_bx | apply U_atom; [rewrite (ew_Ereg_nat R _ 8 8%bv eq_refl); exact H8 | lia]
    | lia | rewrite Z.add_0_r, Z.sub_0_r; exact Hro | rewrite Z.add_0_r, Z.sub_0_r; exact Hoa].
- apply (pg_shent _ _ 18 P 0 8); [apply pg_U_bx | apply U_atom; [rewrite (ew_Ereg_nat R _ 18 18%bv eq_refl); exact H18 | lia]
    | lia | rewrite Z.add_0_r, Z.sub_0_r; exact Hrp | rewrite Z.add_0_r, Z.sub_0_r; exact Hpa].
Qed.
(* the frame's saved registers read back from a state's frame region *)
Lemma pg_frame_of_region : forall E m regs0 sp0,
  region_ok tfibsegs E m (fstk_ret 96 lp_cs) -> bv_unsigned (ew E 2) = sp0 - 96 ->
  (forall j, (j < 11)%nat -> ew E (33 + j) = nth j (pg_saved regs0) (Z_to_bv 64 0)) ->
  forall j, (j < 11)%nat -> val_mem tfibsegs m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (nth j (pg_saved regs0) (Z_to_bv 64 0))).
Proof.
intros E m regs0 sp0 HR E2 Ex j Hj.
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 - 96 + (88 - 8 * Z.of_nat j)) by lia.
apply (fsw_field E m 2 (sp0 - 96) lp_cs 0 96 0 96 (88 - 8 * Z.of_nat j) 8 (SOff (33 + j) 0) _ HR E2).
- rewrite pg_lp_cs. apply in_map_iff. exists j. split; [reflexivity|]. apply in_seq. lia.
- rewrite fsw_SOff0, (Ex j Hj). symmetry. apply Z_to_bv_bv_unsigned.
- apply u64_range.
- cbn; lia.
Qed.
(* a value read through the machine's view is kept where the view is kept *)
Lemma pg_vm_aview : forall H m m' a (n : nat) v, (forall i, 0 <= i < Z.of_nat n -> aview tfibsegs H m' (a + i) = aview tfibsegs H m (a + i)) ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof.
intros H m m' a n v Hs Hv k Hk. rewrite (mbyte_of_aview tfibsegs H H m m' (a + Z.of_nat k)); [exact (Hv k Hk)|].
apply Hs. lia.
Qed.
Lemma pg_atoms_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1. induction l1 as [|[n f] l1 IH]; intros l2 H1 H2; [exact H2|]. destruct H1 as [Hf H1]. split; [exact Hf | apply IH; assumption]. Qed.
Lemma pg_denot_off : forall E n w c, ew E n = Z_to_bv 64 w -> sv_denot E (SOff n c) = Z_to_bv 64 (w + c).
Proof.
intros E n w c Hn. apply bv_eq. rewrite denot_SOff, Hn, !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.
(* the callee-saved registers at the final ret of a loop-env state: sp back up by the frame, the reloaded saved
   registers (xatoms 1..10 = atoms 34..43 for s0..s9), the others their own atoms *)
Definition pg_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 96 | 8 => SOff 34 0 | 9 => SOff 35 0 | 18 => SOff 36 0 | 19 => SOff 37 0 | 20 => SOff 38 0
  | 21 => SOff 39 0 | 22 => SOff 40 0 | 23 => SOff 41 0 | 24 => SOff 42 0 | 25 => SOff 43 0
  | z => SOff (Z.to_nat z) 0 end.
Lemma pg_expect_ok : forall R regs0 kids key, bv_unsigned (YK11.getr R 2) = spZ regs0 - 96 ->
  YK11.getr R 3 = YK11.getr regs0 3 -> YK11.getr R 4 = YK11.getr regs0 4 ->
  YK11.getr R 26 = YK11.getr regs0 26 -> YK11.getr R 27 = YK11.getr regs0 27 ->
  forall r, In r CALLEE_SAVED -> sv_denot (Ereg R (pg_lxs regs0 kids key)) (pg_expect r) = YK11.getr regs0 r.
Proof.
intros R regs0 kids key H2 H3 H4 H26 H27 r Hr.
cbv [CALLEE_SAVED In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
lazymatch goal with |- sv_denot _ (pg_expect ?q) = _ =>
  let e := eval vm_compute in (pg_expect q) in change (pg_expect q) with e end.
- apply fsw_sp_back. rewrite (ew_Ereg_nat R _ 2 2%bv eq_refl). exact H2.
- rewrite fsw_SOff0, (ew_Ereg_nat R _ 3 3%bv eq_refl). exact H3.
- rewrite fsw_SOff0, (ew_Ereg_nat R _ 4 4%bv eq_refl). exact H4.
- exact (fsw_extra_atom R _ 2).
- exact (fsw_extra_atom R _ 3).
- exact (fsw_extra_atom R _ 4).
- exact (fsw_extra_atom R _ 5).
- exact (fsw_extra_atom R _ 6).
- exact (fsw_extra_atom R _ 7).
- exact (fsw_extra_atom R _ 8).
- exact (fsw_extra_atom R _ 9).
- exact (fsw_extra_atom R _ 10).
- exact (fsw_extra_atom R _ 11).
- rewrite fsw_SOff0, (ew_Ereg_nat R _ 26 26%bv eq_refl). exact H26.
- rewrite fsw_SOff0, (ew_Ereg_nat R _ 27 27%bv eq_refl). exact H27.
Qed.

(* ================= the loop: its invariant at the loop head 0x83948 ================= *)
Definition pg_lregs (regs0 regsL : bvmap 5 word) (o k keys n : Z) (i : nat) : Prop :=
  YK11.getr regsL 2 = Z_to_bv 64 (spZ regs0 - 96) /\
  YK11.getr regsL 3 = YK11.getr regs0 3 /\ YK11.getr regsL 4 = YK11.getr regs0 4 /\
  YK11.getr regsL 8 = Z_to_bv 64 o /\ YK11.getr regsL 9 = Z_to_bv 64 k /\
  YK11.getr regsL 18 = Z_to_bv 64 (keys + 8 * Z.of_nat i) /\
  YK11.getr regsL 19 = Z_to_bv 64 SHADOW_OFF /\
  YK11.getr regsL 20 = Z_to_bv 64 (-56 * Z.of_nat i) /\
  YK11.getr regsL 21 = Z_to_bv 64 (Z.of_nat i) /\
  YK11.getr regsL 22 = Z_to_bv 64 n /\
  YK11.getr regsL 23 = Z_to_bv 64 keys /\
  YK11.getr regsL 24 = Z_to_bv 64 1 /\
  YK11.getr regsL 25 = Z_to_bv 64 (keys + 8 * Z.of_nat i) /\
  YK11.getr regsL 26 = YK11.getr regs0 26 /\ YK11.getr regsL 27 = YK11.getr regs0 27.
Definition pj_li (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (o k keys n : Z) (i : nat) (ms : machine_state) (md : Model) : Prop :=
  exists regsL memL,
    ms = YK11.mkst regsL (Z_to_bv 64 0x83948) memL (YK11.seg_rom tfibsegs) /\
    Z.of_nat i < n /\
    ajournal tfibsegs B STK_pj_get (spZ regs0) [] ly S W (unpoison U mem0) md0 [] ly S W (unpoison U memL) md 0 /\
    ARU tfibsegs B ly S U W memL md /\
    av_below (w_H W) mem0 memL alloc_ceiling /\
    pg_lregs regs0 regsL o k keys n i /\
    (forall j, (j < 11)%nat -> val_mem tfibsegs (mrestrict (w_H W) memL) (spZ regs0 - 8 - 8 * Z.of_nat j) 8
       (bv_unsigned (nth j (pg_saved regs0) (Z_to_bv 64 0)))).

(* owner RUNTIME (a Theorem Labs lane): the strcmp interceptor's ARU contract at image B's trampoline 0x426cc
   (lib/B/FSH_Fn_reader.v header, FsRt.fr_strcmp) *)
Hypothesis fs_strcmp_realizesU : astrcmp_realizesU tfibsegs B PC_strcmp.

Section lp.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (o k : Z) (kname : list Z) (members : list (list Z * PjTree.jv))
  (kids keys nn : Z)
  (Qp : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop).
Hypothesis Hnn : nn = Z.of_nat (length members).
Hypothesis Hra : YK0s.ret_ok (YK11.getr regs0 1).
Hypothesis Hgp : YK11.getr regs0 3 = w64 (as_gp B).
Hypothesis Htp : YK11.getr regs0 4 = w64 (as_tp B).
Hypothesis Hsp : spZ regs0 mod 16 = 0 /\ alloc_ceiling + STK_pj_get <= spZ regs0 /\ spZ regs0 <= 2 ^ 47.
Hypothesis Hro0 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem0).
Hypothesis Ho : 4096 <= o /\ o mod 8 = 0 /\ o + 56 <= alloc_ceiling.
Hypothesis HoRA : range_addressable (aview tfibsegs (w_H W) mem0) SHADOW_OFF o 56.
Hypothesis HoAPP : in_app o 56.
Hypothesis Hkd : val_mem tfibsegs (mrestrict (w_H W) mem0) (o + 24) 8 kids.
Hypothesis Rkd : 4112 <= kids /\ kids + 56 * nn <= CEIL.
Hypothesis Hn : 1 <= nn <= 2 ^ 54.
Hypothesis Hky : 4112 <= keys /\ keys mod 8 = 0 /\ keys + 8 * nn <= alloc_ceiling.
Hypothesis HkyRA : range_addressable (aview tfibsegs (w_H W) mem0) SHADOW_OFF keys (8 * nn).
Hypothesis HkyAPP : in_app keys (8 * nn).
Hypothesis Hdj : o + 56 <= keys \/ keys + 8 * nn <= o.
Hypothesis HM : forall i nm u, nth_error members i = Some (nm, u) ->
  exists x, val_mem tfibsegs (mrestrict (w_H W) mem0) (keys + 8 * Z.of_nat i) 8 x /\ 0 <= x < 2 ^ 64 /\
    cstr_ok tfibsegs W mem0 x nm.
Hypothesis HK : cstr_ok tfibsegs W mem0 k kname.
Hypothesis QH : forall i u regs' mem' md', nth_error members i = Some (kname, u) ->
  (forall j nm u', (j < i)%nat -> nth_error members j = Some (nm, u') -> nm <> kname) ->
  aregs_preserved regs0 regs' -> YK11.getr regs' 10 = Z_to_bv 64 (kids + 56 * Z.of_nat i) ->
  av_below (w_H W) mem0 mem' alloc_ceiling -> Qp ly S W regs' mem' md'.
Hypothesis QM : forall regs' mem' md', (forall nm u, In (nm, u) members -> nm <> kname) ->
  aregs_preserved regs0 regs' -> YK11.getr regs' 10 = w64 0 -> av_below (w_H W) mem0 mem' alloc_ceiling ->
  Qp ly S W regs' mem' md'.

(* the facts every loop-env state is built from, at a memory read the same below alloc_ceiling as at the entry *)
Lemma pg_lp_st : forall i R m md pc sr G x,
  ajournal tfibsegs B STK_pj_get (spZ regs0) [] ly S W (unpoison U mem0) md0 [] ly S W (unpoison U m) md 0 ->
  ARU tfibsegs B ly S U W m md -> av_below (w_H W) mem0 m alloc_ceiling ->
  pg_lregs regs0 R o k keys nn i -> Z.of_nat i < nn ->
  (forall j, (j < 11)%nat -> val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs0 - 8 - 8 * Z.of_nat j) 8
     (bv_unsigned (nth j (pg_saved regs0) (Z_to_bv 64 0)))) ->
  val_mem tfibsegs (mrestrict (w_H W) mem0) (keys + 8 * Z.of_nat i) 8 x -> 0 <= x < 2 ^ 64 ->
  regs_ok (Ereg R (pg_lxs regs0 kids x)) sr R -> facts_ok (Ereg R (pg_lxs regs0 kids x)) G ->
  st_ok tfibsegs (Ereg R (pg_lxs regs0 kids x)) (mkSS pc sr lp_mem None G)
    (restrict (w_H W) (YK11.mkst R (Z_to_bv 64 pc) m (YK11.seg_rom tfibsegs))) /\
  sh_ok tfibsegs fs_Bx lp_SH (Ereg R (pg_lxs regs0 kids x)) (mrestrict (w_H W) m).
Proof.
intros i R m md pc sr G x HJ HARU HAV HR Hi Hfr Hx Rx Hsr HG.
destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & _).
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_val as (AC1 & AC2).
pose proof Hsp as (Hsp16 & HspC & Hsp47). pose proof Ho as (Ho1 & Ho2 & Ho3). pose proof Hky as (Hk1 & Hk2 & Hk3).
pose proof Rkd as (Rk1 & Rk2). unfold CEIL in Rk2.
assert (FS : STK_pj_get = ltac:(let v := eval vm_compute in (STK_pj_get) in exact v)) by (vm_compute; reflexivity). rewrite FS in HspC.
set (P := keys + 8 * Z.of_nat i) in *.
assert (HP1 : 4096 <= P /\ P + 8 <= keys + 8 * nn) by (subst P; lia).
split.
- apply (pg_lp_build W R m pc sr G regs0 (spZ regs0) o P kids x Hsr HG).
  + rewrite R2. apply unsigned_lit_small. lia.
  + lia.
  + intros a Ha. apply (apresent_writable tfibsegs). apply (fsw_apresent_unpoison B ly S U W m md a HARU);
      [unfold kHighMemBeg; lia|].
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. rewrite FS. lia.
  + exact Hfr.
  + exact R8.
  + lia.
  + lia.
  + apply (pg_vm_av (w_H W) mem0 m alloc_ceiling (o + 24) 8 kids HAV); [lia | change (Z.of_nat 8) with 8; lia | exact Hkd].
  + lia.
  + exact R18.
  + lia.
  + lia.
  + apply (pg_vm_av (w_H W) mem0 m alloc_ceiling P 8 x HAV); [lia | change (Z.of_nat 8) with 8; lia | exact Hx].
  + exact Rx.
  + lia.
- unfold pg_lxs. apply (pg_lp_shok W R _ m o P R8 ltac:(lia) R18 ltac:(lia)).
  + exact (pg_ra_av (w_H W) mem0 m o 56 HAV ltac:(lia) ltac:(lia) HoRA).
  + exact HoAPP.
  + apply (pg_ra_av (w_H W) mem0 m P 8 HAV ltac:(lia) ltac:(lia)).
    exact (range_addressable_sub _ SHADOW_OFF keys (8 * nn) P 8 HkyRA ltac:(lia) ltac:(lia)).
  + apply (in_app_sub keys (8 * nn) P 8 HkyAPP); lia.
Qed.

(* rom_view at any memory read as the entry's below alloc_ceiling (IMG over the unpoisoned reading; the image lies
   below the shadow, where U reads nothing) *)
Lemma pg_rom_view : forall m md, ARU tfibsegs B ly S U W m md -> av_below (w_H W) mem0 m alloc_ceiling ->
  rom_view tfibsegs W m.
Proof.
intros m md HARU HAV.
pose proof (pg_arodata_av B W mem0 m HAV Hro0) as HroM.
assert (HroU : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U m))).
{ intros a Hro Ho' He. assert (Hb : 0 <= a < SHADOW_OFF).
  { destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [|unfold FS_RLO, FS_RHI, SHADOW_OFF in *; lia].
    pose proof (fs_segs_img a (ex_intro _ sg (conj Hsg Hr))) as Hl. unfold FS_IMG_END, SHADOW_OFF in *. lia. }
  rewrite (aview_at tfibsegs (w_H W) (unpoison U m) m a); [exact (HroM a Hro Ho' He)|].
  apply (unpoison_app B ly S U W m md a HARU); unfold SHADOW_OFF in *; lia. }
destruct (proj2 IMG ly S W (unpoison U m) md (ARU_AR tfibsegs B ly S U W m md HARU) HroU) as (Hrom & _).
intros a Ha. assert (Hb : 0 <= a < SHADOW_OFF).
{ destruct Ha as (sg & Hsg & _ & Hr). pose proof (fs_segs_img a (ex_intro _ sg (conj Hsg Hr))) as Hl.
  unfold FS_IMG_END, SHADOW_OFF in *. lia. }
rewrite <- (aview_at tfibsegs (w_H W) (unpoison U m) m a); [exact (Hrom a Ha)|].
apply (unpoison_app B ly S U W m md a HARU); unfold SHADOW_OFF in *; lia.
Qed.
Lemma pg_lregs_pres : forall R R' i, aregs_preserved R R' -> pg_lregs regs0 R o k keys nn i -> pg_lregs regs0 R' o k keys nn i.
Proof.
intros R R' i HP (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr R' r = YK11.getr R r) by (intros r Hr; exact (fsw_pres R R' r HP Hr)).
unfold pg_lregs. repeat split; (rewrite PR; [assumption | unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?q] => let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end;
  lia]).
Qed.

(* ---- the strcmp call 0x83980 -> 0x83984 (FSW_K.fsw_intrin_atU over fs_strcmp_realizesU): from the call site to the
   return point, with the journal, ARU, the memory below alloc_ceiling, the callee-saved registers and the frame kept,
   and a0 = 0 exactly when the member name equals the key ---- *)
Lemma pg_strcmp_step : forall i regsC memC mdC x nm (Post : world tfibsegs -> config -> Prop),
  ajournal tfibsegs B STK_pj_get (spZ regs0) [] ly S W (unpoison U mem0) md0 [] ly S W (unpoison U memC) mdC 0 ->
  ARU tfibsegs B ly S U W memC mdC -> av_below (w_H W) mem0 memC alloc_ceiling ->
  pg_lregs regs0 regsC o k keys nn i ->
  YK11.getr regsC 1 = Z_to_bv 64 539012 -> YK11.getr regsC 10 = Z_to_bv 64 x -> YK11.getr regsC 11 = Z_to_bv 64 k ->
  cstr_ok tfibsegs W mem0 x nm ->
  (forall j, (j < 11)%nat -> val_mem tfibsegs (mrestrict (w_H W) memC) (spZ regs0 - 8 - 8 * Z.of_nat j) 8
     (bv_unsigned (nth j (pg_saved regs0) (Z_to_bv 64 0)))) ->
  (forall regs2 mem2 md2 v,
     ajournal tfibsegs B STK_pj_get (spZ regs0) [] ly S W (unpoison U mem0) md0 [] ly S W (unpoison U mem2) md2 0 ->
     ARU tfibsegs B ly S U W mem2 md2 -> av_below (w_H W) mem0 mem2 alloc_ceiling ->
     pg_lregs regs0 regs2 o k keys nn i ->
     (forall j, (j < 11)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem2) (spZ regs0 - 8 - 8 * Z.of_nat j) 8
        (bv_unsigned (nth j (pg_saved regs0) (Z_to_bv 64 0)))) ->
     YK11.getr regs2 10 = w64 v -> 0 <= v < 2 ^ 64 -> (v = 0 <-> str_eq nm kname) ->
     SRr tfibsegs W (mkCfg (YK11.mkst regs2 (Z_to_bv 64 539012) mem2 (YK11.seg_rom tfibsegs)) md2) Post) ->
  SRr tfibsegs W (mkCfg (YK11.mkst regsC (Z_to_bv 64 272076) memC (YK11.seg_rom tfibsegs)) mdC) Post.
Proof.
intros i regsC memC mdC x nm Post HJ HARU HAV HR H1 H10 H11 Hcx Hfr HK2.
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_val as (AC1 & AC2).
pose proof Hsp as (Hsp16 & HspC & Hsp47).
assert (FS : STK_pj_get = ltac:(let v := eval vm_compute in (STK_pj_get) in exact v)) by (vm_compute; reflexivity). rewrite FS in HspC.
pose proof HR as (R2 & R3 & R4 & _).
assert (Hspc : spZ regsC = spZ regs0 + -96) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
assert (Hpk : ecall_preU_k tfibsegs B STK_RT_STR ly S U W regsC memC mdC).
{ apply (fsw_ecall_preU_k_at B STK_pj_get (spZ regs0) [] ly S W (unpoison U mem0) md0 [] ly S U W memC mdC 0 regsC
    (-96) STK_RT_STR HJ HARU Hspc);
    first [ reflexivity | (unfold STK_RT_STR, ESTACK; rewrite FS; lia) | (unfold STK_RT_STR, ESTACK; lia)
          | (rewrite H1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity)
          | (rewrite R3; exact Hgp) | (rewrite R4; exact Htp) | lia ]. }
pose proof (pg_rom_view memC mdC HARU HAV) as Hrom.
pose proof (fs_strcmp_realizesU ly S U W regsC memC mdC x k nm kname Hpk Hrom H10 H11
  (pg_cstr_av W mem0 memC x nm HAV Hcx) (pg_cstr_av W mem0 memC k kname HAV HK)) as HC.
eapply SRr_bind.
{ eapply (fsw_intrin_atU B STK_pj_get (spZ regs0) [] ly S W (unpoison U mem0) md0 [] ly S U W memC mdC 0 U
    (fun a => spZ regsC - STK_RT_STR <= a < spZ regsC) (w64 (raZ regsC)) _
    (fun regs' mem' md' => aregs_preserved regsC regs' /\
       (exists v, YK11.getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ (v = 0 <-> str_eq nm kname)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsC - STK_RT_STR <= a < spZ regsC) ->
          aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) memC a)) HJ).
  - eapply SRr_mono; [exact HC|].
    intros W' c' _ (EW & regs' & mem' & md' & v & Ec & HAR' & HPO' & HP' & Hsbm & H10' & Rv & Hv & Hfr' & Hpr').
    subst W'. split; [reflexivity|]. exists regs', mem', md'. split; [exact Ec|].
    split; [split; [exact HAR' | split; [exact (ARU_ok tfibsegs B ly S U W memC mdC HARU) | exact HPO']]|].
    split; [exact Hsbm|].
    split.
    { intros a Ha Hn'. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Eu.
      - apply (aview_unpoison_in tfibsegs). exact Eu.
      - rewrite !(aview_unpoison_out tfibsegs) by exact Eu. exact (Hfr' a Ha Hn'). }
    split.
    { intros a (Hh & b & Hb). split; [exact Hh|]. unfold unpoison in Hb |- *.
      destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))); [eexists; reflexivity|].
      destruct (Hpr' a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'. }
    split; [exact HP'|]. split; [exists v; split; [exact H10' | split; [exact Rv | exact Hv]]|]. exact Hfr'.
  - (* awr_byte's awr_byte0 arm, its stack case *)
    intros a Ha. left. left. rewrite Hspc in Ha. unfold STK_RT_STR, ESTACK in Ha. rewrite FS. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & (v & H10v & Rv & Hv) & Hfr2).
assert (Era : w64 (raZ regsC) = Z_to_bv 64 539012) by (unfold raZ, w64; rewrite H1, unsigned_lit_small by lia; reflexivity).
rewrite Era.
apply (HK2 regs2 mem2 md2 v HJ2 HARU2); [| exact (pg_lregs_pres regsC regs2 i HP2 HR) | | exact H10v | exact Rv | exact Hv].
- apply (av_trans _ mem0 memC mem2 alloc_ceiling HAV). intros a Ha. apply Hfr2; [lia|].
  rewrite Hspc. unfold STK_RT_STR, ESTACK. lia.
- intros j Hj. apply (pg_vm_aview (w_H W) memC mem2); [|exact (Hfr j Hj)].
  intros i' Hi'. apply Hfr2; [lia|]. rewrite Hspc. unfold STK_RT_STR, ESTACK. lia.
Qed.

(* the write-window obligation and the memory-below transfer of a run from a loop-env state *)
Ltac pg_awr R R2 FS :=
  cbn [ss_mem]; unfold lp_mem;
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -96);
  [reflexivity | rewrite (ew_Ereg_nat R _ 2 2%bv eq_refl), R2; rewrite unsigned_lit_small by lia; lia
  | cbn; rewrite FS; lia | cbn; lia |];
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil.
Ltac pg_sb HF R R2 :=
  apply (pg_sb_wr _ _ _ _ alloc_ceiling HF); [|lia];
  let a := fresh "a" in let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in
  intros a (r & Hr0 & Hr); cbn [ss_mem lp_mem In] in Hr0; destruct Hr0 as [<-|[<-|[<-|[]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fstk_ret] in Hr;
  [rewrite (ew_Ereg_nat R _ 2 2%bv eq_refl), R2, unsigned_lit_small in Hr by lia | ..]; lia.

(* ---- one iteration: the loop head 0x83948 (the UBSan tests 0x8394c, 0x83954, 0x83958, 0x8395c, 0x83964 decided, the
   shadow check of keys[i] at 0x83974 covered), strcmp, then the hit (0x839d4: the shadow check of obj + 24 covered,
   the UBSan tests 0x83a04, 0x83a08, 0x83a20 decided; a0 = kids + 56 i, ret), the miss at the last member (a0 = 0,
   ret), or the miss with members left (back to 0x83948 with i + 1) ---- *)
Lemma pg_step : forall i ms md,
  pj_li ly S U W regs0 mem0 md0 o k keys nn i ms md ->
  (forall j nm u, (j < i)%nat -> nth_error members j = Some (nm, u) -> nm <> kname) ->
  (forall ms' md', pj_li ly S U W regs0 mem0 md0 o k keys nn (Datatypes.S i) ms' md' ->
     (forall j nm u, (j < Datatypes.S i)%nat -> nth_error members j = Some (nm, u) -> nm <> kname) ->
     SRr tfibsegs W (mkCfg ms' md') (fpostU tfibsegs B STK_pj_get (spZ regs0) [] regs0 ly S U W mem0 md0 0 U Qp)) ->
  SRr tfibsegs W (mkCfg ms md) (fpostU tfibsegs B STK_pj_get (spZ regs0) [] regs0 ly S U W mem0 md0 0 U Qp).
Proof.
intros i ms md HLI Hpre IH.
destruct HLI as (regsL & memL & -> & Hi & HJ & HARU & HAV & HR & Hfr).
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_val as (AC1 & AC2).
pose proof Hsp as (Hsp16 & HspC & Hsp47). assert (FS : STK_pj_get = ltac:(let v := eval vm_compute in (STK_pj_get) in exact v)) by (vm_compute; reflexivity). rewrite FS in HspC.
pose proof Ho as (Ho1 & Ho2 & Ho3). pose proof Hky as (Hk1 & Hk2 & Hk3). pose proof Rkd as (Rk1 & Rk2).
unfold CEIL in Rk2.
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
destruct (nth_error members i) as [[nm u]|] eqn:Ei; [|apply nth_error_None in Ei; rewrite Hnn in Hi; lia].
destruct (HM i nm u Ei) as (x & Hx & Rx & Hcx).
assert (HP1 : 4096 <= keys + 8 * Z.of_nat i /\ keys + 8 * Z.of_nat i + 8 <= keys + 8 * nn /\
  (keys + 8 * Z.of_nat i) mod 8 = 0 /\ keys + 8 * Z.of_nat i < 2 ^ 61) by lia.
assert (HGA : forall R, pg_lregs regs0 R o k keys nn i ->
  atoms_ok (Ereg R (pg_lxs regs0 kids x)) lp_atoms /\ conds_ok (Ereg R (pg_lxs regs0 kids x)) lp_conds).
{ intros R (Q2 & _ & _ & Q8 & _ & Q18 & _ & _ & Q21 & _ & Q23 & _). unfold pg_lxs. split.
  - apply (pg_lp_atoms R _ (spZ regs0) o (keys + 8 * Z.of_nat i) keys); unfold CEIL; try assumption; try lia.
    rewrite Q2. apply unsigned_lit_small. lia.
  - apply (pg_lp_conds R _ (keys + 8 * Z.of_nat i) keys (Z.of_nat i) Q18 Q23); [lia | exact Q21 | lia]. }
assert (Hsr : regs_ok (Ereg regsL (pg_lxs regs0 kids x)) lp_regs regsL)
  by (unfold pg_lxs; apply (pg_lp_regs_ok regsL _ R19 R24); rewrite R25, R18; reflexivity).
destruct (HGA regsL HR) as (HA0 & HC0).
destruct (pg_lp_st i regsL memL md 0x83948 lp_regs (mkFacts lp_atoms lp_conds []) x HJ HARU HAV HR Hi Hfr Hx Rx Hsr
  (conj HA0 (conj HC0 I))) as [HS SHOK].
fsw_aj_run_to_tokU pj_get_tbl_ok HS HJ HARU SHOK fs_Bspan 272076.
{ pg_awr regsL R2 FS. }
lazymatch goal with |- SRr _ _ (mkCfg ?mC ?mdC) _ =>
lazymatch type of HS with st_ok _ _ ?sC _ =>
  assert (Hpc : ss_pc sC = 272076) by (vm_compute; reflexivity);
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ sC mC HS eq_refl) as EmC; rewrite Hpc in EmC;
  pose proof (fsw_reg_lit _ _ _ mC 1%bv 539012 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as RC1;
  pose proof (fsw_reg_extra _ regsL (pg_lxs regs0 kids x) _ mC 10%bv 13 HS ltac:(vm_compute; reflexivity)) as RC10;
  pose proof (fsw_reg_atom _ regsL _ _ mC 11%bv 9%bv 9 HS ltac:(vm_compute; reflexivity) eq_refl) as RC11;
  assert (RCS : aregs_preserved regsL (ms_regs mC))
    by (apply (fsw_preserved _ _ sC mC regsL (fun r => sr_get lp_regs r) HS);
        [vm_compute; reflexivity | intros r _; symmetry; exact (Hsr r)]);
  assert (SBC : same_below memL (ms_mem mC) alloc_ceiling) by (pg_sb HF regsL R2);
  pose proof (fsw_region_nth _ sC (restrict (w_H W) mC) 0 (fstk_ret 96 lp_cs) HS ltac:(vm_compute; reflexivity)) as Hrg
end end.
cbn [nth pg_lxs fs_extraT pg_saved app] in RC10. clear HF HFr HG.
assert (E2 : bv_unsigned (ew (Ereg regsL (pg_lxs regs0 kids x)) 2) = spZ regs0 - 96)
  by (rewrite (ew_Ereg_nat regsL _ 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (Ex : forall j, (j < 11)%nat -> ew (Ereg regsL (pg_lxs regs0 kids x)) (33 + j) = nth j (pg_saved regs0) (Z_to_bv 64 0)).
{ intros j Hj. replace (33 + j)%nat with (32 + Datatypes.S j)%nat by lia. rewrite ew_Ereg_extra. unfold pg_lxs.
  cbn [nth fs_extraT app]. apply app_nth1. cbn [length pg_saved]. lia. }
pose proof (pg_frame_of_region _ _ regs0 (spZ regs0) Hrg E2 Ex) as HfrC.
rewrite EmC.
apply (pg_strcmp_step i (ms_regs ms) (ms_mem ms) _ x nm _ HJ HARU (av_trans _ _ _ _ _ HAV (av_of_sb _ _ _ _ SBC))
  (pg_lregs_pres regsL (ms_regs ms) i RCS HR) RC1 RC10 ltac:(rewrite RC11, R9; reflexivity) Hcx HfrC).
intros regs2 mem2 md2 v HJ2 HARU2 HAV2 HR2 Hfr2 H10v Rv Hv.
pose proof HR2 as (S2 & S3 & S4 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27).
assert (E22 : bv_unsigned (ew (Ereg regs2 (pg_lxs regs0 kids x)) 2) = spZ regs0 - 96)
  by (rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), S2; apply unsigned_lit_small; lia).
assert (Ex2 : forall j, (j < 11)%nat -> ew (Ereg regs2 (pg_lxs regs0 kids x)) (33 + j) = nth j (pg_saved regs0) (Z_to_bv 64 0)).
{ intros j Hj. replace (33 + j)%nat with (32 + Datatypes.S j)%nat by lia. rewrite ew_Ereg_extra. unfold pg_lxs.
  cbn [nth fs_extraT app]. apply app_nth1. cbn [length pg_saved]. lia. }
assert (Hsr2 : regs_ok (Ereg regs2 (pg_lxs regs0 kids x)) lp_regs regs2)
  by (unfold pg_lxs; apply (pg_lp_regs_ok regs2 _ S19 S24); rewrite S25, S18; reflexivity).
destruct (HGA regs2 HR2) as (HA2 & HC2).
assert (Hpf : forall R mF, bv_unsigned (YK11.getr R 2) = spZ regs0 - 96 -> YK11.getr R 3 = YK11.getr regs0 3 ->
  YK11.getr R 4 = YK11.getr regs0 4 -> YK11.getr R 26 = YK11.getr regs0 26 -> YK11.getr R 27 = YK11.getr regs0 27 ->
  forall sF, st_ok tfibsegs (Ereg R (pg_lxs regs0 kids x)) sF (restrict (w_H W) mF) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs sF) r) (pg_expect r)) CALLEE_SAVED = true ->
  aregs_preserved regs0 (ms_regs mF)).
{ intros R mF Q2 Q3 Q4 Q26 Q27 sF HSF Hfb.
  exact (fsw_preserved _ _ sF mF regs0 pg_expect HSF Hfb (pg_expect_ok R regs0 kids x Q2 Q3 Q4 Q26 Q27)). }
assert (S2' : bv_unsigned (YK11.getr regs2 2) = spZ regs0 - 96) by (rewrite S2; apply unsigned_lit_small; lia).
assert (E44 : ew (Ereg regs2 (pg_lxs regs0 kids x)) 44 = Z_to_bv 64 kids)
  by (change 44%nat with (32 + 12)%nat; rewrite ew_Ereg_extra; reflexivity).
destruct (Z.eq_dec v 0) as [V0|V0].
- (* the hit: a0 = kids + 56 i *)
  assert (Enm : nm = kname) by (apply Hv; exact V0).
  assert (Hsr3 : regs_ok (Ereg regs2 (pg_lxs regs0 kids x)) (sr_set lp_regs 10%bv (SLit 0)) regs2)
    by (apply regs_ok_pin; [exact Hsr2 | intros Hx'; discriminate Hx' | rewrite H10v, V0; reflexivity]).
  assert (HGH : facts_ok (Ereg regs2 (pg_lxs regs0 kids x)) hit_G).
  { split; [|split; [|exact I]]; cbn [hit_G f_atoms f_conds f_alias].
    - apply pg_atoms_app; [exact HA2|]. split; [|exact I].
      apply (pg_afact _ 44 kids); [exact E44 | lia | unfold CEIL; lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
    - apply pg_conds_app; [exact HC2|].
      apply (pg_hit_conds _ (Z.of_nat i) kids); [rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl); exact S21
        | exact E44 | lia | lia | lia]. }
  destruct (pg_lp_st i regs2 mem2 md2 539012 _ hit_G x HJ2 HARU2 HAV2 HR2 Hi Hfr2 Hx Rx Hsr3 HGH) as [HSH SHOK2].
  fsw_aj_run_tokU pj_get_tbl_ok HSH HJ2 HARU2 SHOK2 fs_Bspan.
  { pg_awr regs2 S2 FS. }
  lazymatch goal with |- SRr _ _ (mkCfg ?mF _) _ =>
  lazymatch type of HSH with st_ok _ _ ?sF _ =>
    pose proof (fsw_reg_extra _ regs2 (pg_lxs regs0 kids x) _ mF 1%bv 1 HSH ltac:(vm_compute; reflexivity)) as RF1;
    assert (Hs10 : sr_get (ss_regs sF) 10%bv = SAlu ALU_ADD (SMd M_MUL (SOff 20 0) (SLit (-1))) (SOff 44 0))
      by (vm_compute; reflexivity);
    pose proof (st_ok_restrict_reg tfibsegs _ _ sF mF 10%bv HSH) as RF10;
    pose proof (Hpf regs2 mF S2' S3 S4 S26 S27 sF HSH ltac:(vm_compute; reflexivity)) as HPF;
    assert (SBF : same_below mem2 (ms_mem mF) alloc_ceiling) by (pg_sb HF regs2 S2)
  end end.
  cbn [nth pg_lxs fs_extraT pg_saved app] in RF1. rewrite Hs10, denot_lit_U in RF10.
  rewrite (pg_U_hit _ (Z.of_nat i) kids) in RF10.
  2: { rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl). exact S20. }
  2: exact E44.
  2: lia.
  2: lia.
  eapply (fsw_retU B pj_get_tbl pj_get_tbl_ok W _ _ _ _ STK_pj_get (spZ regs0) [] regs0 ly S U W mem0 md0 ly S U 0 Qp HSH);
    [reflexivity | vm_compute; reflexivity | rewrite RF1; exact Hra | exact HJ2 | exact HARU2 | exact HPF |].
  intros mt. apply (QH i u); [rewrite <- Enm; exact Ei | exact Hpre | exact HPF | exact RF10 |].
  exact (av_trans _ _ _ _ _ HAV2 (av_of_sb _ _ _ _ SBF)).
- assert (Hne : nm <> kname) by (intros Eq; apply V0; apply Hv; exact Eq).
  assert (Hpre' : forall j nm' u', (j < Datatypes.S i)%nat -> nth_error members j = Some (nm', u') -> nm' <> kname).
  { intros j nm' u' Hj Ej. destruct (Nat.eq_dec j i) as [->|Hne'].
    - rewrite Ei in Ej. injection Ej as <- _. exact Hne.
    - apply (Hpre j nm' u'); [lia | exact Ej]. }
  assert (Ha0 : atoms_ok (Ereg regs2 (pg_lxs regs0 kids x)) [(10%nat, mkAF 1 (2 ^ 64 - 1) 0)]).
  { split; [|exact I]. apply (pg_afact _ 10 v); [rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact H10v | lia | lia
      | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
  assert (HGM : forall last : bool, (if last then nn = Z.of_nat i + 1 else nn <> Z.of_nat i + 1) ->
    facts_ok (Ereg regs2 (pg_lxs regs0 kids x)) (miss_G last)).
  { intros last Hl. split; [|split; [|exact I]]; cbn [miss_G f_atoms f_conds f_alias].
    - apply pg_atoms_app; [exact HA2 | exact Ha0].
    - apply pg_conds_app; [exact HC2|]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
      assert (U22 : YP0e.U (Ereg regs2 (pg_lxs regs0 kids x)) (SOff 22 0) = nn)
        by (apply U_atom; [rewrite (ew_Ereg_nat regs2 _ 22 22%bv eq_refl); exact S22 | lia]).
      assert (U21 : YP0e.U (Ereg regs2 (pg_lxs regs0 kids x)) (SOff 21 1) = Z.of_nat i + 1)
        by (apply U_atom_off; [rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl); exact S21 | lia | lia]).
      destruct last; cbv beta iota in Hl |- *.
      + rewrite branch_eq_U, U22, U21. apply Z.eqb_eq. exact Hl.
      + rewrite branch_ne_U, U22, U21. apply negb_true_iff, Z.eqb_neq. exact Hl. }
  destruct (Z.eq_dec nn (Z.of_nat i + 1)) as [RL|RL].
  + (* the miss at the last member: a0 = 0 *)
    destruct (pg_lp_st i regs2 mem2 md2 539012 lp_regs (miss_G true) x HJ2 HARU2 HAV2 HR2 Hi Hfr2 Hx Rx Hsr2 (HGM true RL))
      as [HSE SHOK2].
    fsw_aj_run_tokU pj_get_tbl_ok HSE HJ2 HARU2 SHOK2 fs_Bspan.
    { pg_awr regs2 S2 FS. }
    lazymatch goal with |- SRr _ _ (mkCfg ?mF _) _ =>
    lazymatch type of HSE with st_ok _ _ ?sF _ =>
      pose proof (fsw_reg_extra _ regs2 (pg_lxs regs0 kids x) _ mF 1%bv 1 HSE ltac:(vm_compute; reflexivity)) as RF1;
      pose proof (fsw_reg_lit _ _ _ mF 10%bv 0 HSE ltac:(vm_compute; reflexivity) ltac:(lia)) as RF10;
      pose proof (Hpf regs2 mF S2' S3 S4 S26 S27 sF HSE ltac:(vm_compute; reflexivity)) as HPF;
      assert (SBF : same_below mem2 (ms_mem mF) alloc_ceiling) by (pg_sb HF regs2 S2)
    end end.
    cbn [nth pg_lxs fs_extraT pg_saved app] in RF1.
    eapply (fsw_retU B pj_get_tbl pj_get_tbl_ok W _ _ _ _ STK_pj_get (spZ regs0) [] regs0 ly S U W mem0 md0 ly S U 0 Qp HSE);
      [reflexivity | vm_compute; reflexivity | rewrite RF1; exact Hra | exact HJ2 | exact HARU2 | exact HPF |].
    intros mt. apply QM; [| exact HPF | exact RF10 | exact (av_trans _ _ _ _ _ HAV2 (av_of_sb _ _ _ _ SBF))].
    intros nm' u' Hin Eq. apply In_nth_error in Hin as (j & Ej).
    assert (Hj : (j < length members)%nat) by (apply nth_error_Some; rewrite Ej; discriminate).
    apply (Hpre' j nm' u'); [rewrite Hnn in RL; lia | exact Ej | exact Eq].
  + (* the miss with members left: back at the loop head with i + 1 *)
    destruct (pg_lp_st i regs2 mem2 md2 539012 lp_regs (miss_G false) x HJ2 HARU2 HAV2 HR2 Hi Hfr2 Hx Rx Hsr2 (HGM false RL))
      as [HSN SHOK2].
    pose proof HSN as HSN0.
    fsw_aj_run_to_tokU pj_get_tbl_ok HSN HJ2 HARU2 SHOK2 fs_Bspan 538952.
    { pg_awr regs2 S2 FS. }
    lazymatch goal with |- SRr _ _ (mkCfg ?mN _) _ =>
    lazymatch type of HSN with st_ok _ _ ?sN _ =>
      assert (HpcN : ss_pc sN = 538952) by (vm_compute; reflexivity);
      pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ sN mN HSN eq_refl) as EmN; rewrite HpcN in EmN;
      assert (RN : forall r : bv 5, sr_get (ss_regs sN) r = sr_get lp_regs r ->
        YK11.getr (ms_regs mN) r = YK11.getr regs2 r)
        by (intros r Hr; exact (pg_same_reg _ _ _ _ mN _ r HSN HSN0 Hr));
      pose proof (st_ok_restrict_reg tfibsegs _ _ sN mN 18%bv HSN) as N18;
      pose proof (st_ok_restrict_reg tfibsegs _ _ sN mN 20%bv HSN) as N20;
      pose proof (st_ok_restrict_reg tfibsegs _ _ sN mN 21%bv HSN) as N21;
      pose proof (st_ok_restrict_reg tfibsegs _ _ sN mN 25%bv HSN) as N25;
      assert (G18 : sr_get (ss_regs sN) 18%bv = SOff 18 8) by (vm_compute; reflexivity);
      assert (G20 : sr_get (ss_regs sN) 20%bv = SOff 20 (-56)) by (vm_compute; reflexivity);
      assert (G21 : sr_get (ss_regs sN) 21%bv = SOff 21 1) by (vm_compute; reflexivity);
      assert (G25 : sr_get (ss_regs sN) 25%bv = SOff 18 8) by (vm_compute; reflexivity);
      pose proof (RN 2%bv ltac:(vm_compute; reflexivity)) as N2;
      pose proof (RN 3%bv ltac:(vm_compute; reflexivity)) as N3;
      pose proof (RN 4%bv ltac:(vm_compute; reflexivity)) as N4;
      pose proof (RN 8%bv ltac:(vm_compute; reflexivity)) as N8;
      pose proof (RN 9%bv ltac:(vm_compute; reflexivity)) as N9;
      pose proof (RN 19%bv ltac:(vm_compute; reflexivity)) as N19;
      pose proof (RN 22%bv ltac:(vm_compute; reflexivity)) as N22;
      pose proof (RN 23%bv ltac:(vm_compute; reflexivity)) as N23;
      pose proof (RN 24%bv ltac:(vm_compute; reflexivity)) as N24;
      pose proof (RN 26%bv ltac:(vm_compute; reflexivity)) as N26;
      pose proof (RN 27%bv ltac:(vm_compute; reflexivity)) as N27;
      assert (SBN : same_below mem2 (ms_mem mN) alloc_ceiling) by (pg_sb HF regs2 S2);
      pose proof (fsw_region_nth _ sN (restrict (w_H W) mN) 0 (fstk_ret 96 lp_cs) HSN ltac:(vm_compute; reflexivity)) as HrgN
    end end.
    rewrite G18, (pg_denot_off _ 18 (keys + 8 * Z.of_nat i) 8) in N18 by (rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl); exact S18).
    rewrite G25, (pg_denot_off _ 18 (keys + 8 * Z.of_nat i) 8) in N25 by (rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl); exact S18).
    rewrite G20, (pg_denot_off _ 20 (-56 * Z.of_nat i) (-56)) in N20 by (rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl); exact S20).
    rewrite G21, (pg_denot_off _ 21 (Z.of_nat i) 1) in N21 by (rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl); exact S21).
    rewrite EmN. apply IH; [|exact Hpre'].
    eexists _, _. split; [reflexivity|]. split; [rewrite Nat2Z.inj_succ; lia|].
    split; [exact HJ2|]. split; [exact HARU2|]. split; [exact (av_trans _ _ _ _ _ HAV2 (av_of_sb _ _ _ _ SBN))|].
    split.
    { unfold pg_lregs. rewrite N2, N3, N4, N8, N9, N18, N19, N20, N21, N22, N23, N24, N25, N26, N27, Nat2Z.inj_succ.
      repeat split; try assumption; f_equal; lia. }
    exact (pg_frame_of_region _ _ regs0 (spZ regs0) HrgN E22 Ex2).
Qed.

Lemma pg_loop : forall j i ms md, (length members - i = j)%nat ->
  pj_li ly S U W regs0 mem0 md0 o k keys nn i ms md ->
  (forall j' nm u, (j' < i)%nat -> nth_error members j' = Some (nm, u) -> nm <> kname) ->
  SRr tfibsegs W (mkCfg ms md) (fpostU tfibsegs B STK_pj_get (spZ regs0) [] regs0 ly S U W mem0 md0 0 U Qp).
Proof.
induction j as [|j IH]; intros i ms md Hj HLI Hpre.
- exfalso. destruct HLI as (_ & _ & _ & Hi & _). rewrite Hnn in Hi. lia.
- apply (pg_step i ms md HLI Hpre). intros ms' md' HLI' Hpre'. apply (IH (Datatypes.S i) ms' md'); [lia | exact HLI' | exact Hpre'].
Qed.
End lp.

(* ---- segment E2: o <> 0, an object with n >= 1 members: the alignment test and shadow check of obj, the checks of
   obj + 40 and obj + 32 (covered), keys loaded into s7 / s9 / s2 and s8 = (keys <> 0) = 1 (atom 33 >= 4112), to the loop
   head 0x83948 with i = 0 ---- *)
(* the frame region the prologue leaves (MEASURED: the engine's state at 0x83948 from the entry) *)
Definition ent_chunks : list YP09.chunk :=
  [YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
   YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition ent_frame : YP09.region := YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 ent_chunks.
Lemma pg_ef1 : forall R xs m sp0 off (r : bv 5) n, region_ok tfibsegs (Ereg R xs) m ent_frame ->
  bv_unsigned (ew (Ereg R xs) 2) = sp0 -> In (YP09.mkChunk off (CVal 8 (SOff n 0))) ent_chunks ->
  Z.of_nat n = bv_unsigned r -> val_mem tfibsegs m (sp0 + off) 8 (bv_unsigned (YK11.getr R r)).
Proof.
intros R xs m sp0 off r n HR E2 Hin Hn.
apply (fsw_field (Ereg R xs) m 2 sp0 ent_chunks (-96) 0 (-96) 0 off 8 (SOff n 0) _ HR E2 Hin).
- rewrite fsw_SOff0, (ew_Ereg_nat R xs n r Hn). symmetry. apply Z_to_bv_bv_unsigned.
- apply u64_range.
- cbn; lia.
Qed.
Lemma pg_ent_frame : forall R xs m sp0, region_ok tfibsegs (Ereg R xs) m ent_frame -> bv_unsigned (YK11.getr R 2) = sp0 ->
  forall j, (j < 11)%nat -> val_mem tfibsegs m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (nth j (pg_saved R) (Z_to_bv 64 0))).
Proof.
intros R xs m sp0 HR H2 j Hj.
assert (E2 : bv_unsigned (ew (Ereg R xs) 2) = sp0) by (rewrite (ew_Ereg_nat R xs 2 2%bv eq_refl); exact H2).
assert (G : forall K OFF (r : bv 5) n, sp0 - 8 - 8 * Z.of_nat K = sp0 + OFF ->
  In (YP09.mkChunk OFF (CVal 8 (SOff n 0))) ent_chunks -> Z.of_nat n = bv_unsigned r ->
  val_mem tfibsegs m (sp0 - 8 - 8 * Z.of_nat K) 8 (bv_unsigned (YK11.getr R r))).
{ intros K OFF r n EK Hin Hn. rewrite EK. exact (pg_ef1 R xs m sp0 OFF r n HR E2 Hin Hn). }
destruct j as [|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]; [..|lia]; cbn [nth pg_saved].
- apply (G 0%nat (-8) 1%bv 1%nat); [lia | cbn [ent_chunks In]; repeat (first [left; reflexivity | right]) | reflexivity].
- apply (G 1%nat (-16) 8%bv 8%nat); [lia | cbn [ent_chunks In]; repeat (first [left; reflexivity | right]) | reflexivity].
- apply (G 2%nat (-24) 9%bv 9%nat); [lia | cbn [ent_chunks In]; repeat (first [left; reflexivity | right]) | reflexivity].
- apply (G 3%nat (-32) 18%bv 18%nat); [lia | cbn [ent_chunks In]; repeat (first [left; reflexivity | right]) | reflexivity].
- apply (G 4%nat (-40) 19%bv 19%nat); [lia | cbn [ent_chunks In]; repeat (first [left; reflexivity | right]) | reflexivity].
- apply (G 5%nat (-48) 20%bv 20%nat); [lia | cbn [ent_chunks In]; repeat (first [left; reflexivity | right]) | reflexivity].
- apply (G 6%nat (-56) 21%bv 21%nat); [lia | cbn [ent_chunks In]; repeat (first [left; reflexivity | right]) | reflexivity].
- apply (G 7%nat (-64) 22%bv 22%nat); [lia | cbn [ent_chunks In]; repeat (first [left; reflexivity | right]) | reflexivity].
- apply (G 8%nat (-72) 23%bv 23%nat); [lia | cbn [ent_chunks In]; repeat (first [left; reflexivity | right]) | reflexivity].
- apply (G 9%nat (-80) 24%bv 24%nat); [lia | cbn [ent_chunks In]; repeat (first [left; reflexivity | right]) | reflexivity].
- apply (G 10%nat (-88) 25%bv 25%nat); [lia | cbn [ent_chunks In]; repeat (first [left; reflexivity | right]) | reflexivity].
Qed.
Lemma pg_seg_enter : forall ly S U (W : world tfibsegs) regs mem md ch o k keys nval Qp,
  afn_preU tfibsegs B STK_pj_get ly S U W regs mem md ch ->
  YK11.getr regs 10 = w64 o -> YK11.getr regs 11 = w64 k -> 4096 <= o -> o mod 8 = 0 -> o + 56 <= alloc_ceiling ->
  (forall x, o <= x < o + 56 -> ~ in_img tfibsegs x) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF o 56 -> in_app o 56 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) o 4 6 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (o + 32) 8 keys -> 4112 <= keys <= CEIL -> keys mod 16 = 0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (o + 40) 8 nval -> 1 <= nval <= 2 ^ 54 ->
  (forall ms md', pj_li ly S U W regs mem md o k keys nval 0 ms md' ->
     SRr tfibsegs W (mkCfg ms md') (fpostU tfibsegs B STK_pj_get (spZ regs) [] regs ly S U W mem md 0 U Qp)) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_pj_get regs mem md)
    (fpostU tfibsegs B STK_pj_get (spZ regs) [] regs ly S U W mem md 0 U Qp).
Proof.
intros ly S U W regs mem md ch o k keys nval Qp HPRE H10 H11 Ho4 Ho8 HoC Himg Hra0 Happ Htg Hky Rky Hk16 Hnv Rnv HL.
pose proof HPRE as (HAP & _ & _).
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_val as (AC1 & AC2).
assert (FS : STK_pj_get = ltac:(let v := eval vm_compute in (STK_pj_get) in exact v)) by (vm_compute; reflexivity). rewrite FS in Hceil.
set (xs := [Z_to_bv 64 keys; Z_to_bv 64 nval]).
set (E := Ereg regs (fs_extraT ++ xs)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (U10 : YP0e.U E (SOff 10 0) = o)
  by (apply U_atom; [subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10 | unfold CEIL in *; lia]).
assert (E33 : ew E 33 = Z_to_bv 64 keys) by (change 33%nat with (32 + 1)%nat; subst E; rewrite ew_Ereg_extra; reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 nval) by (change 34%nat with (32 + 2)%nat; subst E; rewrite ew_Ereg_extra; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (change 32%nat with (32 + 0)%nat; subst E; rewrite ew_Ereg_extra; reflexivity).
assert (Hgf : atoms_ok E (es_gf true)).
{ cbn [es_gf atoms_ok app]. split; [|split; [|split; [|exact I]]].
  - apply (pg_afact E 10 o); [subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10 | unfold CEIL in *; lia
      | unfold CEIL in *; lia | change (2 ^ 3) with 8; exact Ho8 | lia].
  - apply (pg_afact E 33 keys); [exact E33 | unfold CEIL in *; lia | lia | change (2 ^ 4) with 16; exact Hk16 | lia].
  - apply (pg_afact E 34 nval); [exact E34 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
pose proof (pg_entry_st ly S U W regs mem md ch o 6 (SOff 34 0) true keys nval HPRE H10 Ho4 Ho8 HoC Himg Htg ltac:(lia)
  Hky ltac:(unfold CEIL in *; lia) Hnv ltac:(lia) ltac:(rewrite fsw_SOff0; exact E34) Hgf) as HS.
assert (SHOK : sh_ok tfibsegs fs_Bx es_SH E (mrestrict (w_H W) mem)).
{ constructor; [|constructor]. apply (pg_shent E _ 10 o 0 56); [apply pg_U_bx | exact U10 | lia | | ];
    rewrite Z.add_0_r, Z.sub_0_r; [exact Hra0 | exact Happ]. }
pose proof (ajournal_init tfibsegs B STK_pj_get [] ly S W regs (unpoison U mem) md ch HAP) as HJ.
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPRE) as HARU.
unfold cfg_at. change (w64 A_pj_get) with (Z_to_bv 64 A_pj_get).
fsw_aj_run_to_tokU pj_get_tbl_ok HS HJ HARU SHOK fs_Bspan 538952.
{ cbn [ss_mem es_ss fss0T_args fsT_regions_args fsT_regions app];
  eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact Usp | cbn; rewrite FS; lia | cbn; lia |];
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ (mkCfg ?mE _) _ =>
lazymatch type of HS with st_ok _ _ ?sE _ =>
  assert (HpcE : ss_pc sE = 538952) by (vm_compute; reflexivity);
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ sE mE HS eq_refl) as EmE; rewrite HpcE in EmE;
  assert (RG : forall (r : bv 5) e, sr_get (ss_regs sE) r = e -> YK11.getr (ms_regs mE) r = sv_denot E e)
    by (intros r e Hr; rewrite (st_ok_restrict_reg tfibsegs _ _ sE mE r HS), Hr; reflexivity);
  (* each expected register value is stated: vm_compute only ever sees a closed goal *)
  pose proof (RG 2%bv (SOff 2 (-96)) ltac:(clear; vm_compute; reflexivity)) as N2;
  pose proof (RG 3%bv (SOff 3 0) ltac:(clear; vm_compute; reflexivity)) as N3;
  pose proof (RG 4%bv (SOff 4 0) ltac:(clear; vm_compute; reflexivity)) as N4;
  pose proof (RG 8%bv (SOff 10 0) ltac:(clear; vm_compute; reflexivity)) as N8;
  pose proof (RG 9%bv (SOff 11 0) ltac:(clear; vm_compute; reflexivity)) as N9;
  pose proof (RG 18%bv (SOff 33 0) ltac:(clear; vm_compute; reflexivity)) as N18;
  pose proof (RG 19%bv (SOff 32 0) ltac:(clear; vm_compute; reflexivity)) as N19;
  pose proof (fsw_reg_lit _ _ _ mE 20%bv 0 HS ltac:(clear; vm_compute; reflexivity) ltac:(lia)) as N20;
  pose proof (fsw_reg_lit _ _ _ mE 21%bv 0 HS ltac:(clear; vm_compute; reflexivity) ltac:(lia)) as N21;
  pose proof (RG 22%bv (SOff 34 0) ltac:(clear; vm_compute; reflexivity)) as N22;
  pose proof (RG 23%bv (SOff 33 0) ltac:(clear; vm_compute; reflexivity)) as N23;
  pose proof (fsw_reg_lit _ _ _ mE 24%bv 1 HS ltac:(clear; vm_compute; reflexivity) ltac:(lia)) as N24;
  pose proof (RG 25%bv (SOff 33 0) ltac:(clear; vm_compute; reflexivity)) as N25;
  pose proof (RG 26%bv (SOff 26 0) ltac:(clear; vm_compute; reflexivity)) as N26;
  pose proof (RG 27%bv (SOff 27 0) ltac:(clear; vm_compute; reflexivity)) as N27;
  assert (SBE : same_below mem (ms_mem mE) alloc_ceiling)
    by (apply (pg_sb_wr _ _ mem (ms_mem mE) alloc_ceiling HF); [|lia];
        intros a (r & Hr0 & Hr); cbn in Hr0; destruct Hr0 as [<-|[<-|[<-|[<-|[]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fstk fs_got_region fs_bcell_region es_obj] in Hr;
        [rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl) in Hr; change (bv_unsigned (YK11.getr regs 2)) with (spZ regs) in Hr
        | ..]; lia);
  pose proof (fsw_region_nth _ sE (restrict (w_H W) mE) 0 ent_frame HS ltac:(vm_compute; reflexivity)) as HrgE
end end.
rewrite (pg_denot_off E 2 (spZ regs) (-96)) in N2
  by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned).
assert (Er : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; subst E; exact (ew_Ereg_nat regs _ n r Hn)).
rewrite fsw_SOff0, (Er 3%nat 3%bv eq_refl) in N3.
rewrite fsw_SOff0, (Er 4%nat 4%bv eq_refl) in N4.
rewrite fsw_SOff0, (Er 10%nat 10%bv eq_refl), H10 in N8.
rewrite fsw_SOff0, (Er 11%nat 11%bv eq_refl), H11 in N9.
rewrite fsw_SOff0, E33 in N18. rewrite fsw_SOff0, E32 in N19. rewrite fsw_SOff0, E34 in N22.
rewrite fsw_SOff0, E33 in N23. rewrite fsw_SOff0, E33 in N25.
rewrite fsw_SOff0, (Er 26%nat 26%bv eq_refl) in N26.
rewrite fsw_SOff0, (Er 27%nat 27%bv eq_refl) in N27.
rewrite EmE. apply HL.
eexists _, _. split; [reflexivity|]. split; [cbn; lia|].
split; [exact HJ|]. split; [exact HARU|]. split; [exact (av_of_sb _ _ _ _ SBE)|].
split.
{ unfold pg_lregs. rewrite N2, N3, N4, N8, N9, N18, N19, N20, N21, N22, N23, N24, N25, N26, N27. cbn [Z.of_nat].
  repeat split; try reflexivity; f_equal; lia. }
exact (pg_ent_frame regs (fs_extraT ++ xs) _ (spZ regs) HrgE eq_refl).
Qed.

(* ---- the reader facts the loop takes, from the entry data ---- *)
Lemma pg_ra_payload : forall ly S U (W : world tfibsegs) m md b n p len, ARU tfibsegs B ly S U W m md ->
  fs_heads B ly S U -> In (b, n) (ablocks B ly S) -> b + 16 <= p -> p + len <= b + req_size n ->
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF p len.
Proof.
intros ly S U W m md b n p len H FH Hb Hp Hl x Hx.
pose proof asan_consts as (C1 & _).
destruct (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U m) md b n p len
  (ARU_AR tfibsegs B ly S U W m md H) Hb ltac:(lia) Hl x Hx) as (s & Es & Hok).
exists s. split; [|exact Hok]. change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Es |- *.
destruct (al_blocks _ _ LAWS ly S W (unpoison U m) md b n (ARU_AR tfibsegs B ly S U W m md H) Hb) as (_ & B4 & Bc & _).
rewrite <- (aview_unpoison_out tfibsegs (w_H W) U m (shadow_addr x)); [exact Es|].
rewrite wz; [exact (pg_payload_not_ush B ly S U W m md b n x H FH Hb ltac:(lia))|].
unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos x 8). pose proof (Z.div_le_upper_bound x 8 (2 ^ 61)). lia.
Qed.
Lemma pg_mems_nth : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D i nm u,
  PjStruct.pj_mems tfibsegs m lblk P a ka l D -> nth_error l i = Some (nm, u) ->
  exists x kx D1, PjStruct.pj_u64 tfibsegs m (ka + 8 * Z.of_nat i) x /\ PjStruct.pj_cstr tfibsegs m lblk x kx nm /\
    P (a + 56 * Z.of_nat i) u D1 /\ incl D1 D.
Proof.
intros m lblk P l. induction l as [|[nm0 u0] l IH]; intros a ka D i nm u H E; [destruct i; discriminate|].
cbn [PjStruct.pj_mems] in H. destruct H as (x & kx & D1 & D2 & -> & Hx & Hc & Hp & Hr).
destruct i as [|i]; cbn [nth_error] in E.
- injection E as <- <-. exists x, kx, D1. cbn [Z.of_nat]. rewrite !Z.mul_0_r, !Z.add_0_r.
  split; [exact Hx|]. split; [exact Hc|]. split; [exact Hp|].
  intros y Hy. right. apply in_or_app. left. exact Hy.
- destruct (IH _ _ _ _ _ _ Hr E) as (x' & kx' & D1' & H1 & H2 & H3 & H4).
  exists x', kx', D1'. replace (ka + 8 * Z.of_nat (Datatypes.S i)) with (ka + 8 + 8 * Z.of_nat i) by lia.
  replace (a + 56 * Z.of_nat (Datatypes.S i)) with (a + 56 + 56 * Z.of_nat i) by lia.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros y Hy. right. apply in_or_app. right. exact (H4 y Hy).
Qed.
Lemma pg_node_hdr : forall m lblk p t D, PjStruct.pj_node tfibsegs m lblk p t D ->
  exists num str kids keys n cap, PjStruct.pj_hdr tfibsegs m p (PjTree.tag t) num str kids keys n cap.
Proof.
intros m lblk p t D H. destruct t; cbn [PjStruct.pj_node] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & HH & _); exists num, str, kids, keys, n, cap; exact HH.
Qed.

(* ================= the theorem ================= *)
Theorem pj_get_holds : @pj_get_spec fx rc SK tfibsegs B.
Proof.
intros ly S U W regs mem md ch o k kname t D UL live peak cnt fail HPRE HFH H10 H11 Hobj HK HKk HG.
destruct HPRE as [HAPU Hro0].
pose proof HAPU as (HAP & _ & _). pose proof HAP as (HAR & Hra & _ & Hgp & Htp & _).
pose proof (fsw_sp B _ ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HAPU) as HARU.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HARu.
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_val as (AC1 & AC2).
destruct Hobj as [-> | (HN & HPO)].
- apply (pg_seg_null ly S U W regs mem md ch _ HAPU H10).
  intros regs' mem' md' HP' H10' SB'. cbv beta.
  split; [reflexivity|]. split; [exact (cstr_ok_below W mem mem' k kname SB' HK)|]. split; [exact HKk|].
  split; [exact (fs_glob_below W mem mem' live peak cnt fail SB' HG)|]. left. split; [reflexivity | exact H10'].
- pose proof (fsw_pobj_low B ly S W (unpoison U mem) md mem o HARu HPO) as (Ho1 & Ho2).
  pose proof (pg_pobj_client B ly S W (unpoison U mem) md mem o HARu HPO) as Hcl.
  pose proof (pg_pobj_app B ly S W (unpoison U mem) md mem o HARu HPO) as Happ.
  assert (Ho8 : o mod 8 = 0 /\ range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF o 56)
    by (destruct HPO as [[(_ & Ho8 & HoRA) | (_ & Ho8 & HoRA)] _]; split; assumption).
  destruct Ho8 as (Ho8 & HoRA).
  assert (Hcl' : forall x, o <= x < o + 56 -> ~ in_img tfibsegs x) by (intros x Hx; exact (proj2 (Hcl x Hx))).
  assert (HQ : forall regs' mem' z, av_below (w_H W) mem mem' alloc_ceiling -> YK11.getr regs' 10 = w64 z ->
    (rnode tfibsegs B ly S W mem' UL o t D ->
       rd_get_res tfibsegs (mrestrict (w_H W) mem') (fun a n => In (a, n) UL) o t D kname z) ->
    ablocks B ly S = ablocks B ly S /\ cstr_ok tfibsegs W mem' k kname /\ cstr_kept B ly S U k kname /\
    fs_glob tfibsegs W mem' live peak cnt fail /\
    (o = 0 /\ YK11.getr regs' 10 = w64 0 \/ o <> 0 /\ rnode tfibsegs B ly S W mem' UL o t D /\
     exists z0, YK11.getr regs' 10 = w64 z0 /\
       rd_get_res tfibsegs (mrestrict (w_H W) mem') (fun a n => In (a, n) UL) o t D kname z0)).
  { intros regs' mem' z HAV H10' Hres.
    pose proof (pg_rnode_av B ly S W (unpoison U mem) md mem mem' UL o t D HARu HAV Hcl HN) as HN'.
    split; [reflexivity|]. split; [exact (pg_cstr_av W mem mem' k kname HAV HK)|]. split; [exact HKk|].
    split; [exact (pg_glob_av W mem mem' live peak cnt fail HAV HG)|].
    right. split; [lia|]. split; [exact HN'|]. exists z. split; [exact H10' | exact (Hres HN')]. }
  pose proof HN as (HNode & HB & HI).
  destruct t as [ | | | txt bits | s | items | members ].
  1-6: destruct (pg_node_hdr _ _ _ _ _ HNode) as (num & str & kids & keys & n & cap & HH);
    pose proof HH as (_ & Htg & _ & _ & _ & Hky & Hnv & _);
    pose proof Hky as (Rky & _); pose proof Hnv as (Rnv & _);
    lazymatch type of Htg with PjStruct.pj_u32 _ _ _ ?tg =>
    apply (pg_seg_early ly S U W regs mem md ch o tg (SOff 34 0) keys n _
      ltac:(cbn [PjTree.tag]; repeat (first [left; reflexivity | right])) HAPU H10 Ho1 Ho8 ltac:(lia) Hcl' HoRA Happ
      (pg_vm_u32 _ _ _ Htg) (pg_vm_u64 _ _ _ Hky) Rky (pg_vm_u64 _ _ _ Hnv) Rnv ltac:(cbn [PjTree.tag]; intros; lia))
    end;
    intros regs' mem' md' HP' H10' SB'; cbv beta;
    apply (HQ regs' mem' 0 (av_of_sb _ _ _ _ SB') H10'); intros _; reflexivity.
  cbn [PjStruct.pj_node] in HNode.
  destruct HNode as (HND & HAP' & num & str & kids & keys & n & cap & HH & Hs0 & Hn & Hncap & Hcapc & Di & ED & HMm).
  pose proof HH as (_ & Htg & _ & _ & Hkd & Hky & Hnv & _).
  pose proof Hky as (Rky & _). pose proof Hnv as (Rnv & _). pose proof Hkd as (Rkd0 & _).
  destruct (Z.eq_dec n 0) as [N0|N0].
  + (* the empty object *)
    rewrite N0 in Hnv.
    apply (pg_seg_early ly S U W regs mem md ch o 6 (SLit 0) keys 0 _
      ltac:(repeat (first [left; reflexivity | right])) HAPU H10 Ho1 Ho8 ltac:(lia) Hcl' HoRA Happ
      (pg_vm_u32 _ _ _ Htg) (pg_vm_u64 _ _ _ Hky) Rky (pg_vm_u64 _ _ _ Hnv) ltac:(lia) (fun _ => eq_refl)).
    intros regs' mem' md' HP' H10' SB'. cbv beta.
    apply (HQ regs' mem' 0 (av_of_sb _ _ _ _ SB') H10'). intros _. cbn [rd_get_res]. left. split; [|reflexivity].
    intros nm u Hin. destruct members; [destruct Hin | cbn [length] in Hn; lia].
  + (* an object with members: to the loop *)
    destruct Hcapc as [(C0 & _) | (Cp & Hlk & Hly)]; [lia|].
    pose proof (HB keys (8 * cap) Hly) as Hrbk. pose proof Hrbk as (Hkbl & Hk16 & _ & _).
    destruct (fsw_rblock_low B ly S W (unpoison U mem) md mem keys (8 * cap) HARu Hrbk) as (K1 & K2).
    pose proof (HB kids (56 * cap) Hlk) as Hrbd.
    destruct (fsw_rblock_low B ly S W (unpoison U mem) md mem kids (56 * cap) HARu Hrbd) as (D1 & D2).
    assert (Hrq : req_size (8 * cap + HEAD) = 8 * cap + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (8 * cap + 16) 0); lia).
    unfold HEAD in *.
    assert (Hnn : n = Z.of_nat (length members)) by exact Hn.
    assert (Hsp : spZ regs mod 16 = 0 /\ alloc_ceiling + STK_pj_get <= spZ regs /\ spZ regs <= 2 ^ 47) by lia.
    assert (Ho : 4096 <= o /\ o mod 8 = 0 /\ o + 56 <= alloc_ceiling) by lia.
    pose proof (pg_vm_u64 _ _ _ Hkd) as Vkd.
    assert (Rkd : 4112 <= kids /\ kids + 56 * n <= CEIL) by (unfold CEIL; lia).
    assert (Hn1 : 1 <= n <= 2 ^ 54) by lia.
    assert (Hky' : 4112 <= keys /\ keys mod 8 = 0 /\ keys + 8 * n <= alloc_ceiling) by lia.
    assert (HkyRA : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF keys (8 * n))
      by (apply (pg_ra_payload ly S U W mem md (keys - 16) (8 * cap + 16) keys (8 * n) HARU HFH Hkbl); rewrite ?Hrq; lia).
    assert (HkyAPP : in_app keys (8 * n)).
    { destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md _ _ HARu Hkbl) as (_ & _ & _ & Ha & _).
      rewrite Hrq in Ha. apply (in_app_sub _ _ keys (8 * n) Ha); lia. }
    assert (Hdj : o + 56 <= keys \/ keys + 8 * n <= o).
    { assert (Hin : In (keys, 8 * cap) D)
        by (rewrite ED; replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia); right; left; reflexivity).
      destruct (Z_le_gt_dec (o + 56) keys) as [L|L]; [left; exact L|].
      destruct (Z_le_gt_dec (keys + 8 * n) o) as [L'|L']; [right; exact L'|].
      exfalso. apply (HAP' (keys, 8 * cap) (Z.max o keys) Hin); [unfold PjStruct.pj_holds; cbn [fst snd]|]; lia. }
    assert (HM : forall i nm u, nth_error members i = Some (nm, u) ->
      exists x, val_mem tfibsegs (mrestrict (w_H W) mem) (keys + 8 * Z.of_nat i) 8 x /\ 0 <= x < 2 ^ 64 /\
        cstr_ok tfibsegs W mem x nm).
    { intros i nm u Ei. destruct (pg_mems_nth _ _ _ _ _ _ _ _ _ _ HMm Ei) as (x & kx & D3 & Hx & Hc & _ & _).
      exists x. split; [exact (pg_vm_u64 _ _ _ Hx)|]. split; [exact (proj1 Hx)|].
      exact (pg_cstr_member B ly S U W mem md UL x kx nm HARU HFH HB Hc). }
    apply (pg_seg_enter ly S U W regs mem md ch o k keys n _ HAPU H10 H11 Ho1 Ho8 ltac:(lia) Hcl' HoRA Happ
      (pg_vm_u32 _ _ _ Htg) (pg_vm_u64 _ _ _ Hky) ltac:(unfold CEIL; lia) ltac:(lia) (pg_vm_u64 _ _ _ Hnv) Hn1).
    intros ms md' HLI.
    apply pg_loop with (ly := ly) (S := S) (U := U) (W := W) (regs0 := regs) (mem0 := mem) (md0 := md) (o := o) (k := k)
      (kname := kname) (members := members) (kids := kids) (keys := keys) (nn := n) (j := (length members - 0)%nat) (i := 0%nat);
      try eassumption; try reflexivity.
    * intros i u regs' mem' md'' Ei Hpre HP' H10' HAV'. cbv beta.
      apply (HQ regs' mem' (kids + 56 * Z.of_nat i) HAV' H10'). intros HN'.
      pose proof HN' as (HNode2 & _ & _). cbn [PjStruct.pj_node] in HNode2.
      destruct HNode2 as (_ & _ & num2 & str2 & kids2 & keys2 & n2 & cap2 & HH2 & _ & _ & _ & _ & Di2 & ED2 & HM2).
      pose proof HH2 as (_ & _ & _ & _ & Hkd2 & _).
      assert (Hkd' : PjStruct.pj_u64 tfibsegs (mrestrict (w_H W) mem') (o + 24) kids).
      { apply (PjStruct.pj_u64_eq tfibsegs (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') (o + 24) kids Hkd).
        intros x Hx. pose proof (u64_range x) as Hr.
        assert (E : x = Z_to_bv 64 (bv_unsigned x)) by (symmetry; apply Z_to_bv_bv_unsigned).
        rewrite E. apply (pg_raw (w_H W) mem mem' (bv_unsigned x) HAV'); [lia | apply Hcl'; lia]. }
      pose proof (PjStruct.pj_u64_uniq tfibsegs _ _ _ _ Hkd2 Hkd') as <-.
      destruct (pg_mems_nth _ _ _ _ _ _ _ _ _ _ HM2 Ei) as (x & kx & D3 & _ & _ & HP3 & Hinc).
      unfold rd_get_res. right. exists i, u, kids2, D3.
      split; [exact Ei|]. split; [exact Hpre|]. split; [exact Hkd'|]. split; [reflexivity|]. split; [exact HP3|].
      intros y Hy. rewrite ED2. apply in_or_app. right. exact (Hinc y Hy).
    * intros regs' mem' md'' Hall HP' H10' HAV'. cbv beta.
      apply (HQ regs' mem' 0 HAV' H10'). intros _. unfold rd_get_res. left. split; [exact Hall | reflexivity].
    * intros j nm u Hj. lia.
Qed.

End s.
