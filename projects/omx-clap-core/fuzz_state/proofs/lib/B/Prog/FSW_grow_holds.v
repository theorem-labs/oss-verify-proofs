(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the IMAGE B (fs.asan-ubsan) composition of grow's walk (FSW_grow.v's stage lemmas)
   through its two fuzz_realloc calls: grow_holds : grow_spec (lib/B/FSH_Fn_reader.v:575). rule 24 line, reuse search and
   port source: FSW_grow.v's header (lane brief (internal path), CONFIRM a Theorem Labs lane;
   ported from a working branch 75e39a1f41d:proofs/omx-clap-core/fuzz_state/lib/B/Prog/grow.v).
   The callee contract is ALLOC's fuzz_realloc_spec (lib/B/FSH_Fn_alloc.v, CTX-free, the text of S0
   a working branch f32db4da382), the named Section hypothesis fuzz_realloc_holds; the image fact is
   FsShadowSyms B (the shadow-base cells; FSW_grow.v's stages). The theorem's shape mirrors image A's
   (grow_holds : forall {fx rc SK} B, FsShadowSyms B -> fuzz_realloc_spec tfibsegs B -> grow_spec tfibsegs B), with
   tfibsegs B's image (lib/B/YB1v.v, AsanUbsan's loaded segments); grow_spec's Section hypothesis IMG (fs_img_facts) is not
   needed by this walk, so it is not a premise.
   PORTED lemma by lemma (copied, never Required, never bridged), from the image-A walk of the same C, final at
   a working branch 728177ca53c lib/A/Prog/FSW_grow_holds.v (a Theorem Labs lane; its lines 1-501 equal 582c4d69613's):
     fs_pstat_img, grow_frame_chunks (frame 96, s9), gB_rs_ok / gB_disj (shadow cell of v + 24 at atom 25 = s9),
     gC_rs_ok / gC_disj (frame 96), grow_bb, grow_rsum_app, grow_rsum_perm, grow_garr8_ex, grow_mbyte_eq, grow_val_eq,
     grow_writable_grows, fs_pstat_not_ro (B's static addresses 0xa41c0 / 0x5daac0 .. 0x5dab08), grow_perm_swap,
     grow_blk_nodup, grow_block_bytes, grow_v_off_rblk, grow_pj_rw, grow_awr, grow_hdr_upd, grow_glob_img,
     grow_arodata_img, grow_rblock_eq, grow_pobj_run, grow_realloc_step, grow_inFP_blk, grow_val_eqm, grow_moved,
     grow_word_eq, grow_req, ghide, grow_cap_arm (B: frame 96, resumes 0x83d68 / 0x83db8, s9 = the shadow of v + 24,
     the kept registers 3 4 18 26 27) and grow_holds;
   and, for B's own code, from a working branch 75e39a1f41d lib/B/Prog/grow.v: the realloc arms' shape
   (gr_oom_seg / gr_keys_oom_seg are dead here: grow_spec's quiet makes every fuzz_realloc grant, and the resumed a0's
   fact decides the OOM beqz 0x83d6c / 0x83db8 not taken) and the size arithmetic gr_cap2 / gr_sz. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret FSPstat FSH_Fn_reader FSW_rd FSW_pj FSW_K3 FSW_rres FSH_Fn_alloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderRes PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YN1e.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import FSW_grow_tbl FSW_grow_shcell FSW_grow.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* the alloc.c statics are image bytes *)
Lemma fs_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a ((lo & hi) & Hin & Ha). cbn [fst snd] in Ha.
assert (HB : forall lo hi, In (lo, hi) FS_PSTAT_FP ->
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true).
{ intros lo' hi' H. unfold FS_PSTAT_FP in H. cbn [In] in H.
  repeat (destruct H as [H|H]; [injection H as <- <-; vm_compute; reflexivity|]); destruct H. }
apply HB in Hin. apply existsb_exists in Hin as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists s. split; [exact Hs | lia].
Qed.

(* the saved-register chunks of grow's frame, under any env whose xatoms 6..15 hold them *)
Lemma grow_frame_chunks : forall regs2 xs m sp regs,
  firstn 11 (skipn 6 xs) = map (YK11.getr regs) grow_saved_regs -> grow_frame m sp regs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) m (sp - 96)) gB_cs.
Proof.
intros regs2 xs m sp regs HX Hfr.
assert (EX : forall i, (i < 11)%nat -> ew (Ereg regs2 (fs_extraT ++ xs)) (xatom (6 + i)) =
  nth i (map (YK11.getr regs) grow_saved_regs) (Z_to_bv 64 0)).
{ intros i Hi. rewrite fsw_ew_xatom, <- fpj_nth_skipn, <- HX. symmetry. exact (fpj_nth_firstn _ 11 i _ Hi). }
unfold grow_frame, grow_saved in Hfr.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end.
cbn [fst snd] in *. unfold gB_cs.
repeat (apply Forall_cons; [
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff (xatom ?j) 0))) =>
    let i := eval vm_compute in (j - 6)%nat in
    let r := eval vm_compute in (nth i grow_saved_regs 0%bv) in
    apply (chunk_ok_val tfibsegs _ _ _ off 8 _ (bv_unsigned (YK11.getr regs r)));
    [ rewrite fsw_SOff0; change j with (6 + i)%nat; rewrite (EX i ltac:(lia)); symmetry; apply Z_to_bv_bv_unsigned
    | apply u64_range | cbn; lia
    | replace (sp - 96 + off) with (sp + (off - 96)) by lia; assumption ] end|]).
apply Forall_nil.
Qed.


Section gb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* stage B's resume regions, at the memory after fuzz_realloc (kids): v's type word and keys slot read only / the kids slot
   writable (atom 9 = v), v's cap slot writable (atom 8 = v + 48), and the two shadow cells grow reads through s9 / s5 *)
Lemma gB_rs_ok : forall E (H : word -> bool) mem v ty keys,
  ew E 9 = Z_to_bv 64 v -> ew E 8 = Z_to_bv 64 (v + 48) ->
  bv_unsigned (ew E 25) = SHADOW_OFF + (v + 24) / 8 -> bv_unsigned (ew E 21) = SHADOW_OFF + (v + 48) / 8 ->
  ew E (xatom 4) = Z_to_bv 64 ty -> ew E (xatom 5) = Z_to_bv 64 keys ->
  4096 <= v -> v + 56 <= alloc_ceiling -> v mod 8 = 0 ->
  (forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict H mem) (v + i)) ->
  val_mem tfibsegs (mrestrict H mem) v 4 ty -> 0 <= ty < 2 ^ 32 ->
  val_mem tfibsegs (mrestrict H mem) (v + 32) 8 keys -> 0 <= keys < 2 ^ 64 ->
  range_addressable (aview tfibsegs H mem) SHADOW_OFF v 56 ->
  Forall (region_ok tfibsegs E (mrestrict H mem)) gB_rs.
Proof.
intros E H mem v ty keys E9 E8 E25 E21 Ety Eky Hv4 Hvc Hv8 Hw Vty Hty Vky Hky Hra.
pose proof asan_consts as (C1 & _).
assert (U9 : bv_unsigned (ew E 9) = v) by (rewrite E9; apply wz; lia).
assert (U8 : bv_unsigned (ew E 8) = v + 48) by (rewrite E8; apply wz; lia).
unfold gB_rs. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
- unfold gB_objT. apply (fsw_pj_part_okR tfibsegs E _ 9 v v 0 4); [lia | lia | exact U9 | lia | lia |].
  constructor; [|constructor]. apply (chunk_ok_val tfibsegs _ _ _ 0 4 _ ty); [rewrite fsw_SOff0; exact Ety | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. exact Vty.
- unfold gB_objK. apply (fsw_pj_part_okW tfibsegs E _ 9 v v 24 40 24 32); [lia | lia | exact Hw | exact U9 | lia | lia | right; lia |].
  constructor; [|constructor]. apply (chunk_ok_val tfibsegs _ _ _ 32 8 _ keys); [rewrite fsw_SOff0; exact Eky | cbn; lia | cbn; lia | exact Vky].
- unfold gB_objC. apply (fsw_pj_part_okW tfibsegs E _ 8 v (v + 48) 0 8 0 8); [lia | lia | exact Hw | exact U8 | lia | lia | right; lia | constructor].
- apply (fsw_shcell_region_ok H mem E 25 (v + 24) E25); [lia | rewrite Z.add_mod, Hv8 by lia; reflexivity |].
  apply (range_addressable_sub _ _ v 56); [exact Hra | lia | lia].
- apply (fsw_shcell_region_ok H mem E 21 (v + 48) E21); [lia | rewrite Z.add_mod, Hv8 by lia; reflexivity |].
  apply (range_addressable_sub _ _ v 56); [exact Hra | lia | lia].
Qed.
(* ... and with the frame and the two image cells, pairwise disjoint *)
Lemma gB_disj : forall E sp v,
  bv_unsigned (ew E 2) = sp - 96 -> bv_unsigned (ew E 9) = v -> bv_unsigned (ew E 8) = v + 48 ->
  bv_unsigned (ew E 25) = SHADOW_OFF + (v + 24) / 8 -> bv_unsigned (ew E 21) = SHADOW_OFF + (v + 48) / 8 ->
  alloc_ceiling + 96 <= sp -> 4096 <= v -> v + 56 <= alloc_ceiling -> (v + 56 <= 0x10000 \/ FS_IMG_END <= v) ->
  (forall a, v <= a < v + 56 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  pairwise_disjoint E (fsT_ret_regions 96 gB_cs gB_rs).
Proof.
intros E sp v E2 E9 E8 E25 E21 Hc Hv4 Hvc Hvimg Hsh. pose proof asan_consts as (C1 & _).
assert (Hs1 : ~ (SHADOW_OFF <= v < SHADOW_OFF + 2 ^ 44)) by (apply Hsh; lia).
assert (Hs2 : ~ (SHADOW_OFF <= v + 55 < SHADOW_OFF + 2 ^ 44)) by (apply Hsh; lia).
assert (D24 : (v + 24) / 8 + 3 = (v + 48) / 8) by (Z.div_mod_to_equations; lia).
assert (B24 : 0 <= (v + 24) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold SHADOW_OFF in *; lia]).
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, gB_rs, gB_objT, gB_objK, gB_objC, fs_shcell_region.
cbn [app pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E9, E8, E25, E21.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END, SHADOW_OFF in *.
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
(* stage C's resume regions, at the memory after fuzz_realloc (keys): v's keys slot writable (atom 9 = v + 32), v's cap
   slot writable (atom 8 = v + 48), and the two shadow cells grow reads through s7 / s5 *)
Lemma gC_rs_ok : forall E (H : word -> bool) mem v,
  bv_unsigned (ew E 9) = v + 32 -> bv_unsigned (ew E 8) = v + 48 ->
  bv_unsigned (ew E 23) = SHADOW_OFF + (v + 32) / 8 -> bv_unsigned (ew E 21) = SHADOW_OFF + (v + 48) / 8 ->
  4096 <= v -> v + 56 <= alloc_ceiling -> v mod 8 = 0 ->
  (forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict H mem) (v + i)) ->
  range_addressable (aview tfibsegs H mem) SHADOW_OFF v 56 ->
  Forall (region_ok tfibsegs E (mrestrict H mem)) gC_rs.
Proof.
intros E H mem v E9 E8 E23 E21 Hv4 Hvc Hv8 Hw Hra.
pose proof asan_consts as (C1 & _).
unfold gC_rs. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- unfold gC_objK. apply (fsw_pj_part_okW tfibsegs E _ 9 v (v + 32) 0 8 0 8); [lia | lia | exact Hw | exact E9 | lia | lia | right; lia | constructor].
- unfold gB_objC. apply (fsw_pj_part_okW tfibsegs E _ 8 v (v + 48) 0 8 0 8); [lia | lia | exact Hw | exact E8 | lia | lia | right; lia | constructor].
- apply (fsw_shcell_region_ok H mem E 23 (v + 32) E23); [lia | rewrite Z.add_mod, Hv8 by lia; reflexivity |].
  apply (range_addressable_sub _ _ v 56); [exact Hra | lia | lia].
- apply (fsw_shcell_region_ok H mem E 21 (v + 48) E21); [lia | rewrite Z.add_mod, Hv8 by lia; reflexivity |].
  apply (range_addressable_sub _ _ v 56); [exact Hra | lia | lia].
Qed.
(* ... and with the frame and the two image cells, pairwise disjoint *)
Lemma gC_disj : forall E sp v,
  bv_unsigned (ew E 2) = sp - 96 -> bv_unsigned (ew E 9) = v + 32 -> bv_unsigned (ew E 8) = v + 48 ->
  bv_unsigned (ew E 23) = SHADOW_OFF + (v + 32) / 8 -> bv_unsigned (ew E 21) = SHADOW_OFF + (v + 48) / 8 ->
  alloc_ceiling + 96 <= sp -> 4096 <= v -> v + 56 <= alloc_ceiling -> (v + 56 <= 0x10000 \/ FS_IMG_END <= v) ->
  (forall a, v <= a < v + 56 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  pairwise_disjoint E (fsT_ret_regions 96 gB_cs gC_rs).
Proof.
intros E sp v E2 E9 E8 E23 E21 Hc Hv4 Hvc Hvimg Hsh. pose proof asan_consts as (C1 & _).
assert (Hs1 : ~ (SHADOW_OFF <= v < SHADOW_OFF + 2 ^ 44)) by (apply Hsh; lia).
assert (Hs2 : ~ (SHADOW_OFF <= v + 55 < SHADOW_OFF + 2 ^ 44)) by (apply Hsh; lia).
assert (D32 : (v + 32) / 8 + 2 = (v + 48) / 8) by (Z.div_mod_to_equations; lia).
assert (B32 : 0 <= (v + 32) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold SHADOW_OFF in *; lia]).
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, gC_rs, gC_objK, gB_objC, fs_shcell_region.
cbn [app pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E9, E8, E23, E21.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END, SHADOW_OFF in *.
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
End gb.

(* ================= the n = cap arm: generic facts ================= *)
Section gh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the live blocks' request sum (blocks_bytes) is rd_sum of ablocks *)
Lemma grow_bb : forall B ly S, blocks_bytes S = rd_sum (ablocks B ly S).
Proof.
intros B ly S. unfold blocks_bytes, rd_sum, ablocks, blocks.
induction (st_chunks S) as [|c cs IH]; [reflexivity|].
cbn [List.filter fold_right]. destruct (is_alloc c); cbn [map fold_right snd]; rewrite IH; reflexivity.
Qed.
Lemma grow_rsum_app : forall l1 l2, rd_sum (l1 ++ l2) = rd_sum l1 + rd_sum l2.
Proof. intros l1 l2. unfold rd_sum. induction l1 as [|b l1 IH]; cbn [app fold_right]; [reflexivity | rewrite IH; lia]. Qed.
Lemma grow_rsum_perm : forall l l', Permutation l l' -> rd_sum l = rd_sum l'.
Proof. intros l l' HP. unfold rd_sum. induction HP; cbn [fold_right]; lia. Qed.
(* n bytes present at p make a garr8 list of them *)
Lemma grow_garr8_ex : forall m p (k : nat),
  (forall i, (i < k)%nat -> exists b, mbyte tfibsegs m (p + Z.of_nat i) = Some b) ->
  exists l, length l = k /\ garr8 tfibsegs m p l.
Proof.
intros m p k. induction k as [|k IH]; intros Hb.
- exists []. split; [reflexivity | apply garr8_nil].
- destruct IH as (l & Hl & Hg); [intros i Hi; apply Hb; lia|].
  destruct (Hb k ltac:(lia)) as (b & Eb).
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  exists (l ++ [bv_unsigned b]). split; [rewrite length_app, Hl; cbn [length]; lia|].
  intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  destruct (Nat.lt_ge_cases j (length l)) as [Hjl|Hjl].
  + rewrite app_nth1 by exact Hjl. exact (Hg j Hjl).
  + assert (j = length l) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    split; [|lia]. intros kk Hkk. assert (kk = 0%nat) as -> by lia.
    rewrite Z.add_0_r, Hl, Eb; f_equal; rewrite (le_byte_small (bv_unsigned b) 1 0) by (cbn; lia);
      change (Z.shiftr (bv_unsigned b) (8 * Z.of_nat 0)) with (bv_unsigned b); symmetry; apply Z_to_bv_bv_unsigned.
Qed.
(* a byte the machine's memory holds equally at both ends *)
Lemma grow_mbyte_eq : forall (H H' : word -> bool) m m' x,
  mrestrict H' m' (Z_to_bv 64 x) = mrestrict H m (Z_to_bv 64 x) -> mbyte tfibsegs (mrestrict H' m') x = mbyte tfibsegs (mrestrict H m) x.
Proof. intros H H' m m' x E. unfold mbyte. rewrite E. reflexivity. Qed.
Lemma grow_val_eq : forall (H : word -> bool) m m' a (n : nat) v,
  val_mem tfibsegs (mrestrict H m) a n v ->
  (forall k, (k < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  val_mem tfibsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v Hv E k Hk. unfold mbyte, mrestrict in *. rewrite (E k Hk). exact (Hv k Hk). Qed.
(* writability survives a memory that only grows *)
Lemma grow_writable_grows : forall m m' a, mem_grows m m' -> writable_at tfibsegs m a -> writable_at tfibsegs m' a.
Proof.
intros m m' a MG Hw. unfold writable_at, wview in *.
destruct (m' (Z_to_bv 64 a)) eqn:E1; [discriminate|].
destruct (m (Z_to_bv 64 a)) eqn:E2; [|exact Hw].
exfalso. apply (MG (Z_to_bv 64 a)); [rewrite E2; discriminate | exact E1].
Qed.
(* fuzz/alloc.c's statics are no read-only byte (they are .data / .bss of a writable segment) *)
Lemma fs_pstat_not_ro : forall a, inFP FS_PSTAT_FP a -> ~ in_roP tfibsegs FS_RLO FS_RHI a.
Proof.
intros a ((lo & hi) & Hin & Ha) [(s & Hs & Hw & Hr) | Hr]; cbn [fst snd] in Ha.
- assert (HB : forallb (fun s => seg_writable s ||
     (((Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0xa41c0) || (0xa41c8 <=? Z.of_N (seg_base s))) &&
      ((Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5daac0) || (0x5dab08 <=? Z.of_N (seg_base s))))) tfibsegs = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) HB s Hs) as Hc. cbv beta in Hc. rewrite Hw in Hc. cbn [orb] in Hc.
  apply andb_prop in Hc as [Hc1 Hc2]. apply orb_prop in Hc1. apply orb_prop in Hc2.
  destruct Hc1 as [Hc1|Hc1]; apply Z.leb_le in Hc1; destruct Hc2 as [Hc2|Hc2]; apply Z.leb_le in Hc2;
  unfold FS_PSTAT_FP in Hin; cbn [In] in Hin;
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]); destruct Hin.
- unfold FS_RLO, FS_RHI in Hr. unfold FS_PSTAT_FP in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]); destruct Hin.
Qed.
Lemma grow_perm_swap : forall (c1 c2 b1 b2 : list (Z * Z)) r o,
  c1 ++ c2 = b1 ++ b2 -> Permutation ((c1 ++ r :: c2) ++ [o]) ((b1 ++ o :: b2) ++ [r]).
Proof.
intros c1 c2 b1 b2 r o E.
transitivity (r :: o :: (c1 ++ c2)).
- rewrite <- app_assoc. cbn [app].
  transitivity (r :: (c1 ++ c2 ++ [o])); [apply Permutation_sym, Permutation_middle|].
  apply perm_skip. rewrite app_assoc. apply Permutation_sym, Permutation_cons_append.
- rewrite E, <- app_assoc. cbn [app].
  transitivity (o :: r :: (b1 ++ b2)); [apply perm_swap|].
  transitivity (o :: (b1 ++ b2 ++ [r])); [apply perm_skip; rewrite app_assoc; apply Permutation_cons_append|].
  apply Permutation_middle.
Qed.
End gh.

Section gk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the blocks of an AR state are pairwise distinct *)
Lemma grow_blk_nodup : forall ly S W mem md c1 c2 x,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = c1 ++ x :: c2 -> ~ In x (c1 ++ c2).
Proof.
intros ly S W mem md c1 c2 [p n] HAR E Hin.
destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W mem md p n HAR) as (_ & _ & _ & _ & _ & PW & Hn).
{ rewrite E. apply in_or_app. right. left. reflexivity. }
pose proof (req_size_pos n ltac:(lia)) as (R1 & _).
set (g := fun b : Z * Z => (fst b, req_size (snd b))) in PW. rewrite E in PW.
assert (D : zdisjoint (p, req_size n) (p, req_size n)).
{ apply in_app_or in Hin as [Hin|Hin]; apply in_split in Hin as (d1 & d2 & ->).
  - apply (YCbq.pairwise_In2 zdisjoint _ (p, req_size n) (p, req_size n) (map g d1) (map g d2) (map g c2) PW).
    rewrite <- app_assoc. cbn [app]. rewrite map_app. cbn [map]. rewrite map_app. cbn [map]. reflexivity.
  - apply (YCbq.pairwise_In2 zdisjoint _ (p, req_size n) (p, req_size n) (map g c1) (map g d1) (map g d2) PW).
    rewrite map_app. cbn [map]. rewrite map_app. cbn [map]. reflexivity. }
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
(* the bytes of a live reader block are present: they make a zbytes_at list *)
Lemma grow_block_bytes : forall ly S U (W : world tfibsegs) mem md p k,
  ARU tfibsegs B ly S U W mem md -> fs_rblock tfibsegs B ly S W mem p k ->
  exists old, Z.of_nat (length old) = k /\ zbytes_at tfibsegs W mem p old.
Proof.
intros ly S U W mem md p k HU (Hin & Hal & Hk & _).
pose proof HU as (HAR & _).
destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W (unpoison U mem) md (p - HEAD) (k + HEAD) HAR Hin)
  as (_ & _ & _ & _ & HP & _).
assert (Hr : req_size (k + HEAD) = k + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (k + 16) 0); lia).
destruct (grow_garr8_ex (mrestrict (w_H W) mem) p (Z.to_nat k)) as (l & Hl & Hg).
- intros i Hi. destruct (HP (p + Z.of_nat i) ltac:(rewrite Hr; unfold HEAD; lia)) as ((Hh & b & Hb) & _).
  exists b. unfold mbyte, mrestrict. rewrite Hh.
  rewrite <- (fsw_unpoison_app B ly S U W mem md (p + Z.of_nat i) HU); [rewrite Hb; reflexivity | |].
  + destruct (fsw_ablock_low B ly S W (unpoison U mem) md _ _ HAR Hin) as (A1 & A2 & _). pose proof asan_consts as (C1 & _).
    unfold HEAD in *. lia.
  + apply (fsw_ablock_off_shadow B ly S W (unpoison U mem) md (p - HEAD) (k + HEAD) HAR Hin). rewrite Hr. unfold HEAD. lia.
- exists l. split; [rewrite Hl; lia | exact Hg].
Qed.
(* an object v (pobj) is apart from a live reader block (p, k) it does not lie in (pj_apart), the block's head included *)
Lemma grow_v_off_rblk : forall ly S W mx md m v p k,
  AR tfibsegs B ly S W mx md -> pobj tfibsegs B ly S W m v -> In (p - HEAD, k + HEAD) (ablocks B ly S) -> 0 < k ->
  PjStruct.pj_apart [(p, k)] v -> forall x, v <= x < v + 56 -> ~ (p - HEAD <= x < p + k).
Proof.
intros ly S W mx md m v p k HAR HP Hin Hk HA x Hx Hpx.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (Hr : req_size (k + HEAD) = k + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (k + 16) 0); lia).
destruct HP as [[((cid & pos & Hf & _ & _ & H1 & H2) & _)|((b & n & Hb & H1 & H2) & _)] _].
- pose proof (sep_block_frame tfibsegs B LAWS ly S W mx md _ _ cid pos HAR Hin Hf) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite Hr in D. unfold HEAD in *. lia.
- destruct (Z.eq_dec b (p - HEAD)) as [Eb|Eb]; [destruct (Z.eq_dec n (k + HEAD)) as [En|En]|].
  + subst b n. rewrite Hr in H2. apply (HA (p, k) v); [left; reflexivity | unfold PjStruct.pj_holds; cbn [fst snd]; unfold HEAD in *; lia | lia].
  + pose proof (sep_blocks tfibsegs B LAWS ly S W mx md b n _ _ HAR Hb Hin ltac:(intros E; injection E; intros; contradiction)) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite Hr in D. unfold HEAD in *. lia.
  + pose proof (sep_blocks tfibsegs B LAWS ly S W mx md b n _ _ HAR Hb Hin ltac:(intros E; injection E; intros; contradiction)) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite Hr in D. unfold HEAD in *. lia.
Qed.
(* pj_rw of a pobj at an ARU state: its bytes are writable (pobj) and present (a live block's or frame's, AR) *)
Lemma grow_pj_rw : forall ly S U (W : world tfibsegs) mem md v,
  ARU tfibsegs B ly S U W mem md -> pobj tfibsegs B ly S W mem v -> PjStruct.pj_rw tfibsegs (mrestrict (w_H W) mem) v.
Proof.
intros ly S U W mem md v HU HP.
pose proof HU as (HAR & _). pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR HP) as (L1 & L2).
pose proof (fsw_pobj_off_shadow B ly S W (unpoison U mem) md mem v HAR HP) as NS.
pose proof asan_consts as (C1 & _).
assert (PR : forall a, v <= a < v + 56 -> apresent (w_H W) (unpoison U mem) a).
{ intros a Ha. destruct HP as [[((cid & pos & Hf & _ & _ & H1 & H2) & _)|((b & n & Hb & H1 & H2) & _)] _].
  - destruct (al_frames tfibsegs B LAWS ly S W (unpoison U mem) md cid pos HAR Hf) as (_ & _ & HF & _).
    exact (proj1 (HF a ltac:(lia))).
  - destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U mem) md b n HAR Hb) as (_ & _ & _ & _ & HB & _).
    exact (proj1 (HB a ltac:(unfold HEAD in *; lia))). }
destruct HP as [Hpl Hw].
split; [destruct Hpl as [(_ & Ha & _)|(_ & Ha & _)]; exact Ha|].
split; [lia|]. split; [lia|]. intros a Ha.
split.
- replace a with (v + (a - v)) by lia. exact (Hw (a - v) ltac:(lia)).
- destruct (PR a Ha) as (Hh & b & Hb). exists b.
  change (lib.Lib.Mem.wa a) with (Z_to_bv 64 a). unfold lib.Lib.Mem.mrd, mrestrict. rewrite Hh.
  rewrite <- (fsw_unpoison_app B ly S U W mem md a HU ltac:(lia) (NS a Ha)). rewrite Hb. reflexivity.
Qed.
(* awr_byte for a byte of v's written fields: v in a frame of the entry frames, or in a live block of the call state *)
Lemma grow_awr : forall ly S lyc Sc (W : world tfibsegs) mem STK sp0 FP own v lo hi,
  pobj tfibsegs B lyc Sc W mem v -> frames Sc = frames S ->
  v <= lo -> hi <= v + 56 -> (forall a, lo <= a < hi -> inFP FP a) ->
  forall a, lo <= a < hi -> awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a.
Proof.
intros ly S lyc Sc W mem STK sp0 FP own v lo hi HP Hfr Hlo Hhi HF a Ha.
destruct HP as [[((cid & pos & Hf & _ & _ & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
- unfold awr_byte. right; right. split; [exact (HF a Ha)|]. exists cid, pos. rewrite <- Hfr.
  split; [exact Hf|]. unfold in_zr, frame_rng. cbn [fst snd]. lia.
- unfold awr_byte, awr_byte0. left; right; left. split; [exact (HF a Ha)|]. exists b, m. split; [exact Hb | unfold HEAD in H1; lia].
Qed.
(* the header of v after its slots change: the other bytes kept, the three slots read anew *)
Lemma grow_hdr_upd : forall m m' p ty num str kids keys n cap k' y' cap',
  PjStruct.pj_hdr tfibsegs m p ty num str kids keys n cap -> PjStruct.pj_rw tfibsegs m' p ->
  (forall x : word, p <= bv_unsigned x < p + 24 \/ p + 40 <= bv_unsigned x < p + 48 -> m' x = m x) ->
  PjStruct.pj_u64 tfibsegs m' (p + 24) k' -> PjStruct.pj_u64 tfibsegs m' (p + 32) y' ->
  PjStruct.pj_u64 tfibsegs m' (p + 48) cap' ->
  PjStruct.pj_hdr tfibsegs m' p ty num str k' y' n cap'.
Proof.
intros m m' p ty num str kids keys n cap k' y' cap' (_ & (T0 & T1) & (N0 & N1) & (S0 & S1) & _ & _ & (P0 & P1) & _) Hrw E HK HY HC.
split; [exact Hrw|].
split; [split; [exact T0 | apply (PjStruct.pj_bytes_eq tfibsegs m m'); [exact T1 | intros x Hx; apply E; rewrite Mem.length_le4 in Hx; lia]]|].
split; [split; [exact N0 | apply (PjStruct.pj_bytes_eq tfibsegs m m'); [exact N1 | intros x Hx; apply E; rewrite Mem.length_le8 in Hx; lia]]|].
split; [split; [exact S0 | apply (PjStruct.pj_bytes_eq tfibsegs m m'); [exact S1 | intros x Hx; apply E; rewrite Mem.length_le8 in Hx; lia]]|].
split; [exact HK|]. split; [exact HY|].
split; [split; [exact P0 | apply (PjStruct.pj_bytes_eq tfibsegs m m'); [exact P1 | intros x Hx; apply E; rewrite Mem.length_le8 in Hx; lia]]|].
exact HC.
Qed.
(* the statics and the read-only view across a memory change that keeps every image byte *)
Lemma grow_glob_img : forall (W : world tfibsegs) m m' live peak cnt fail,
  (forall x, in_img tfibsegs x -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hs (G1 & G2 & G3 & G4 & R).
assert (VB : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W) m) g 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v Hg Hv. apply (grow_val_eq _ m m' g 8 v Hv). intros k Hk. apply Hs. apply fs_pstat_img.
  apply (inFP_FS_PSTAT_FP g Hg). lia. }
unfold fs_glob, fs_glob_at in *. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VB; [cbn; tauto | exact G1]|].
split; [apply VB; [cbn; tauto | exact G2]|].
split; [apply VB; [cbn; tauto | exact G3]|].
split; [apply VB; [cbn; tauto | exact G4]|].
exact R.
Qed.
Lemma grow_arodata_img : forall (W : world tfibsegs) m m',
  (forall x, in_img tfibsegs x -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m').
Proof.
intros W m m' Hs HR a Ha Ho He.
assert (E : aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a).
{ unfold aview. pose proof (fs_segs_img a (fsw_roP_img a Ha)) as Hl.
  rewrite (grow_mbyte_eq (w_H W) (w_H W) m m' a); [reflexivity|]. unfold mrestrict. rewrite (Hs a (fsw_roP_img a Ha)). reflexivity. }
rewrite E. exact (HR a Ha Ho He).
Qed.
(* a reader block's head word, and a pobj, across a memory change that keeps the bytes they read *)
Lemma grow_rblock_eq : forall ly S (W : world tfibsegs) m m' p k,
  (forall x, p - HEAD <= x < p - HEAD + 8 -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  fs_rblock tfibsegs B ly S W m p k -> fs_rblock tfibsegs B ly S W m' p k.
Proof.
intros ly S W m m' p k E (Hin & Hal & Hk & Hv). split; [exact Hin|]. split; [exact Hal|]. split; [exact Hk|].
apply (grow_val_eq _ m m' (p - HEAD) 8 k Hv). intros j Hj. apply E. lia.
Qed.
Lemma grow_pobj_run : forall ly S (W : world tfibsegs) m m' v,
  pobj tfibsegs B ly S W m v ->
  (forall x, 0 <= x < alloc_ceiling -> ~ (v + 24 <= x < v + 40) -> ~ (v + 48 <= x < v + 56) ->
     m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall a, v <= a < v + 56 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) -> 0 <= v -> v + 56 <= alloc_ceiling ->
  pobj tfibsegs B ly S W m' v.
Proof.
intros ly S W m m' v HP E MG NS Hv0 Hvc.
assert (RA : range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF v 56 ->
             range_addressable (aview tfibsegs (w_H W) m') SHADOW_OFF v 56).
{ intros Hr x Hx. destruct (Hr x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
  assert (Hx0 : 0 <= x < alloc_ceiling) by lia. pose proof (fsw_shadow_below x Hx0) as Hsb.
  pose proof asan_consts as (C1 & _).
  assert (Hsh : SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 2 ^ 44)
    by (unfold shadow_of_addr; split; [|apply Zplus_lt_compat_l; apply Z.div_lt_upper_bound]; Z.div_mod_to_equations; lia).
  rewrite <- Es. unfold aview. rewrite (grow_mbyte_eq (w_H W) (w_H W) m m'); [reflexivity|]. unfold mrestrict.
  rewrite E; [reflexivity | lia | intros Hx' | intros Hx'];
    exact (NS (shadow_of_addr SHADOW_OFF x) ltac:(lia) Hsh). }
destruct HP as [Hpl Hw]. split.
- destruct Hpl as [(Hf & Ha & Hr)|(Hb & Ha & Hr)]; [left | right]; (split; [assumption|]); (split; [exact Ha | exact (RA Hr)]).
- intros i Hi. exact (grow_writable_grows _ _ (v + i) MG (Hw i Hi)).
Qed.
End gk.

(* ================= the fuzz_realloc call, in one form for both of grow's calls =================
   fuzz_realloc_spec's three arms read under quiet (cnt <> fail): the refused arm is dead, and the p = 0 / p <> 0 arms
   become one post over Dp ([] for p = 0, [(p, k)] the old block otherwise): the journal with footprint FS_PSTAT_FP ++
   the old block, charged at rd_ev's rate (1 for p = 0, 3 otherwise), the heads by ugrow1, the new block, the blocks by
   Permutation, every other old block kept and distinct from the new one, the old bytes at the new block, and the
   statics. *)
Section rs. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis fuzz_realloc_holds : @fuzz_realloc_spec fx rc SK tfibsegs B.

Lemma grow_realloc_step : forall ly S U W regs mem md ch p k n old live peak cnt fail Dp
  (Q : world tfibsegs -> config -> Prop),
  fpreU tfibsegs B STK_fuzz_realloc ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  YK11.getr regs 10 = w64 p -> YK11.getr regs 11 = w64 n -> 1 <= n -> n + HEAD < MALLOC_MAX ->
  fs_glob tfibsegs W mem live peak cnt fail -> live + n < 2 ^ 64 -> cnt + 1 < 2 ^ 64 -> cnt <> fail ->
  ((p = 0 /\ k = 0 /\ old = [] /\ Dp = []) \/
   (p <> 0 /\ Dp = [(p, k)] /\ (exists U1 U2, U = U1 ++ (p - HEAD, HEAD) :: U2) /\
    fs_rblock tfibsegs B ly S W mem p k /\ Z.of_nat (length old) = k /\ zbytes_at tfibsegs W mem p old /\ k <= live)) ->
  st_nev S + (if p =? 0 then EV_fuzz_malloc else 3) <= EV_MAX ->
  blocks_bytes S + (n + HEAD) <= LIVE_MAX ->
  (forall ly' S' U' W' regs' mem' md' res, wle W W' ->
     ajournal tfibsegs B STK_fuzz_realloc (spZ regs) (FS_PSTAT_FP ++ ablocks_fp (rd_hblocks Dp)) ly S W (unpoison U mem)
       md [] ly' S' W' (unpoison U' mem') md' (if p =? 0 then 1 else 3) ->
     upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' -> aregs_preserved regs regs' ->
     YK11.getr regs' 10 = w64 res -> 4096 + HEAD <= res ->
     ugrow1 U U' p res -> FSupoisonU.fs_heads B ly' S' U' -> fs_rblock tfibsegs B ly' S' W' mem' res n ->
     Permutation (ablocks B ly' S' ++ rd_hblocks Dp) (ablocks B ly S ++ [(res - HEAD, n + HEAD)]) ->
     (forall b, In b (ablocks B ly S) -> ~ In b (rd_hblocks Dp) ->
        In b (ablocks B ly' S') /\ b <> (res - HEAD, n + HEAD)) ->
     zbytes_at tfibsegs W' mem' res (firstn (Z.to_nat (Z.min k n)) old) ->
     fs_glob tfibsegs W' mem' (live - k + n) (Z.max peak (live - k + n)) (cnt + 1) fail ->
     SRr tfibsegs W' (mkCfg (mkst regs' (YK11.getr regs 1) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_fuzz_realloc regs mem md) Q.
Proof.
intros ly S U W regs mem md ch p k n old live peak cnt fail Dp Q HPRE HH Hp Hn Hn1 HnM HG HL HC Hcf HOLD HEV HBB K.
eapply SRr_bind.
{ apply (fuzz_realloc_holds ly S U W regs mem md ch p k n old live peak cnt fail HPRE HH Hp Hn Hn1 HnM HG (fun _ => HL) HC).
  - destruct HOLD as [(H1 & H2 & H3 & _) | (H1 & _ & H3 & H4 & H5 & H6 & H7)]; [left; auto | right; auto 7].
  - split; intros Hp0; [rewrite (proj2 (Z.eqb_eq p 0) Hp0) in HEV | rewrite (proj2 (Z.eqb_neq p 0) Hp0) in HEV]; exact HEV.
  - exact (fun _ => HBB). }
intros W' c' Hle [(Hc & _) | [(_ & Hp0 & res & HPOST) | (_ & Hp0 & U1 & U2 & res & EU & HPOST)]];
  [exfalso; exact (Hcf Hc) | |].
- destruct HOLD as [(_ & Hk0 & Ho & ED) | (Hne & _)]; [|exfalso; exact (Hne Hp0)].
  subst k old Dp.
  destruct HPOST as (ly' & S' & regs' & mem' & md' & -> & HJ & OK & PO & HP & (R10 & Rres & Eab & FH & RB & G')).
  rewrite (proj2 (Z.eqb_eq p 0) Hp0) in K.
  apply (K ly' S' (U ++ [(res - HEAD, HEAD)]) W' regs' mem' md' res Hle).
  + cbn [rd_hblocks map ablocks_fp]. rewrite app_nil_r. exact HJ.
  + exact OK.
  + exact PO.
  + exact HP.
  + exact R10.
  + exact Rres.
  + left. split; [exact Hp0 | reflexivity].
  + exact FH.
  + exact (RB ltac:(lia)).
  + cbn [rd_hblocks map]. rewrite app_nil_r, Eab. apply Permutation_refl.
  + intros b Hb _. rewrite Eab. split; [apply in_or_app; left; exact Hb|].
    intros ->. apply (grow_blk_nodup B ly' S' W' _ md' (ablocks B ly S) [] (res - HEAD, n + HEAD) (proj1 HJ)); [rewrite Eab; reflexivity|].
    rewrite app_nil_r. exact Hb.
  + rewrite firstn_nil. unfold zbytes_at. apply garr8_nil.
  + replace (live - 0 + n) with (live + n) by lia. exact G'.
- destruct HOLD as [(Hz & _) | (_ & ED & _ & HRB & _ & _ & _)]; [exfalso; exact (Hp0 Hz)|]. subst Dp.
  destruct HPOST as (ly' & S' & regs' & mem' & md' & -> & HJ & OK & PO & HP &
    (R10 & Rres & (b1 & b2 & c1 & c2 & Eb & Ec & Ebc) & FH & RB & ZB & G')).
  rewrite (proj2 (Z.eqb_neq p 0) Hp0) in K.
  apply (K ly' S' (U1 ++ U2 ++ [(res - HEAD, HEAD)]) W' regs' mem' md' res Hle).
  + exact HJ.
  + exact OK.
  + exact PO.
  + exact HP.
  + exact R10.
  + exact Rres.
  + right. split; [exact Hp0|]. exists U1, U2. split; [exact EU | reflexivity].
  + exact FH.
  + exact (RB ltac:(lia)).
  + change (rd_hblocks [(p, k)]) with [(p - HEAD, k + HEAD)]. rewrite Ec, Eb. apply grow_perm_swap. exact Ebc.
  + intros b Hb Hnb. change (rd_hblocks [(p, k)]) with [(p - HEAD, k + HEAD)] in Hnb.
    rewrite Eb in Hb.
    assert (Hb' : In b (b1 ++ b2)).
    { apply in_app_or in Hb as [Hb|[Hb|Hb]]; [apply in_or_app; left; exact Hb | exfalso; apply Hnb; left; exact Hb |
        apply in_or_app; right; exact Hb]. }
    rewrite <- Ebc in Hb'. rewrite Ec. split.
    * apply in_app_or in Hb' as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx].
    * intros ->. exact (grow_blk_nodup B ly' S' W' _ md' c1 c2 _ (proj1 HJ) Ec Hb').
  + exact ZB.
  + exact G'.
Qed.
End rs.

Section gm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a reader block (a, k) of D: its ASan block's bytes are in ablocks_fp (rd_hblocks D) *)
Lemma grow_inFP_blk : forall D a k x, In (a, k) D -> 0 < k -> a - HEAD <= x < a + k -> inFP (ablocks_fp (rd_hblocks D)) x.
Proof.
intros D a k x Hin Hk Hx. exists (a - HEAD, a - HEAD + req_size (k + HEAD)). split.
- unfold ablocks_fp, rd_hblocks. apply in_map_iff. exists (a - HEAD, k + HEAD). split; [reflexivity|].
  apply in_map_iff. exists (a, k). split; [reflexivity | exact Hin].
- cbn [fst snd]. unfold req_size, HEAD in *. destruct (Z.eqb_spec (k + 16) 0); lia.
Qed.
Lemma grow_val_eqm : forall m m' a (n : nat) v, val_mem tfibsegs m a n v ->
  (forall k, (k < n)%nat -> mbyte tfibsegs m' (a + Z.of_nat k) = mbyte tfibsegs m (a + Z.of_nat k)) ->
  val_mem tfibsegs m' a n v.
Proof. intros m m' a n v H E k Hk. rewrite (E k Hk). exact (H k Hk). Qed.
(* two garr8 copies of one list hold the same bytes *)
Lemma grow_moved : forall m1 m2 a1 a2 l, garr8 tfibsegs m1 a1 l -> garr8 tfibsegs m2 a2 l ->
  forall i, 0 <= i < Z.of_nat (length l) -> mbyte tfibsegs m1 (a1 + i) = mbyte tfibsegs m2 (a2 + i).
Proof.
intros m1 m2 a1 a2 l H1 H2 i Hi.
destruct (H1 (Z.to_nat i) ltac:(lia)) as (V1 & _). destruct (H2 (Z.to_nat i) ltac:(lia)) as (V2 & _).
pose proof (V1 0%nat ltac:(lia)) as E1. pose proof (V2 0%nat ltac:(lia)) as E2.
rewrite Z2Nat.id in E1, E2 by lia. cbn [Z.of_nat] in E1, E2. rewrite Z.add_0_r in E1, E2. rewrite E1, E2. reflexivity.
Qed.
Lemma grow_word_eq : forall (m m' : word -> option byte) (P : Z -> Prop) (x : word),
  (forall z, P z -> m' (Z_to_bv 64 z) = m (Z_to_bv 64 z)) -> P (bv_unsigned x) -> m' x = m x.
Proof. intros m m' P x H Hp. rewrite <- (Z_to_bv_bv_unsigned 64 x). exact (H _ Hp). Qed.
Lemma grow_req : forall k, 0 <= k -> req_size (k + HEAD) = k + HEAD.
Proof. intros k Hk. unfold req_size, HEAD. destruct (Z.eqb_spec (k + 16) 0); lia. Qed.
(* a fact kept out of lia's sight (lia case-splits every implication / disjunction over arithmetic in the context) *)
Definition ghide (P : Prop) : Prop := P.
End gm.

(* ================= the n = cap arm: from entering fuzz_realloc (kids) at 0x83d64 to grow's post =================
   The two fuzz_realloc calls (grow_realloc_step), each resumed by FSW_K3.fsw_after_callFPU_args into stage B (0x83d68)
   or stage C (0x83db8), and the ret through FSW_ret.fsw_retU. v's bytes lie off each call's footprint (FS_PSTAT_FP,
   image bytes, and the old block, grow_v_off_rblk), so the journal keeps v's header, placement and writability
   (FSW_rd.pobj_kept_call, fsw_journal_kept_byte); the new blocks are apart from v (v's container survives each call and
   differs from the new block: grow_realloc_step's survival clause). The composed journal charges 1 or 3 per call
   (p = 0 / p <> 0), which is rd_ev (grow_tr ty cap cap) exactly. *)
Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-base cells of B (lib/B/FSH_Base.v FsShadowSyms: GOT word 0x9fc10, cell 0xa8438) *)
Hypothesis HSS : FsShadowSyms B.
(* callee: ALLOC's fuzz_realloc (a Theorem Labs lane), proved by ALLOC's walk from FS_AREALLOC_A (a Theorem Labs lane's realloc theorem) *)
Hypothesis fuzz_realloc_holds : @fuzz_realloc_spec fx rc SK tfibsegs B.

Lemma grow_cap_arm : forall ly S U W regs mem md ch v ty num str kids keys cap live peak cnt fail regsC memC mat,
  let Dold0 := ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk ty keys cap in
  fpreU tfibsegs B STK_grow ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  pobj tfibsegs B ly S W mem v ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem) v ty num str kids keys cap cap ->
  PjStruct.pj_slots_at (fun a k => In (a, k) Dold0) ty kids keys cap cap ->
  rd_blocks_ok tfibsegs B ly S W mem Dold0 -> PjStruct.pj_apart Dold0 v -> incl (rd_heads Dold0) U ->
  fs_glob tfibsegs W mem live peak cnt fail -> quiet cnt fail (Z.of_nat (length (grow_tr ty cap cap))) ->
  rd_sum Dold0 <= live ->
  56 * ReaderRes.cap2 cap + HEAD < MALLOC_MAX -> live + rd_live (grow_tr ty cap cap) < 2 ^ 64 ->
  st_nev S + rd_ev (grow_tr ty cap cap) <= EV_MAX -> blocks_bytes S + rd_live (grow_tr ty cap cap) <= LIVE_MAX ->
  grow_call_kids W regs regsC memC v cap kids ->
  ajournal tfibsegs B STK_grow (spZ regs) (grow_FP v ty kids keys cap) ly S W (unpoison U mem) md [] ly S W
    (unpoison U memC) (with_vm_backing (m_vm_lazy md) mat md) 0 ->
  ARU tfibsegs B ly S U W memC (with_vm_backing (m_vm_lazy md) mat md) ->
  same_below mem memC alloc_ceiling ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_fuzz_realloc regsC memC (with_vm_backing (m_vm_lazy md) mat md))
    (@grow_post fx rc SK B ly S U W regs mem md v ty num str kids keys cap cap live peak cnt fail).
Proof.
intros ly S U W regs mem md ch v ty num str kids keys cap live peak cnt fail regsC memC mat Dold0
  HPRE HHEADS HPO HHDR HSL HBLK HAPART HINCL HG HQ HRS HMAX HLIVE HEV HLV HC HJ HARU SB.
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *.
set (FP := grow_FP v ty kids keys cap) in *.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (A1 & _).
pose proof HPRE as (HPU & HRO). pose proof HPU as (HAP & _ & _).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & _).
destruct (fsw_sp B _ ly S U W regs mem md ch HPU) as (Hal16 & Hceil & H47 & _).
assert (FSg : STK_grow = ltac:(let x := eval vm_compute in STK_grow in exact x)) by reflexivity.
assert (FSr : STK_fuzz_realloc = ltac:(let x := eval vm_compute in STK_fuzz_realloc in exact x)) by reflexivity.
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR HPO) as (Lv1 & Lv2).
assert (Hvimg : ghide (v + 56 <= 0x10000 \/ FS_IMG_END <= v)) by exact (fsw_pobj_off_img B ly S W (unpoison U mem) md mem v HAR HPO).
pose proof (fsw_pobj_off_shadow B ly S W (unpoison U mem) md mem v HAR HPO) as Hvsh.
assert (Hv8 : v mod 8 = 0) by (destruct HPO as [[(_ & Ha & _)|(_ & Ha & _)] _]; exact Ha).
pose proof HHDR as (Hrw & Hty & Hnum & Hstr & Hkids & Hkeys & Hn & Hcap).
assert (Hty0 : 5 <= ty <= 6) by (destruct (proj1 HSL); lia).
pose proof (proj1 (proj2 HSL)) as Hncap.
assert (Hcap0 : ghide (cap = 0 -> kids = 0 /\ (ty = 6 -> keys = 0))) by exact (proj1 (proj2 (proj2 HSL))).
assert (Hcapp : ghide (0 < cap -> In (kids, 56 * cap) Dold0 /\ (ty = 6 -> In (keys, 8 * cap) Dold0)))
  by exact (proj2 (proj2 (proj2 HSL))).
pose proof HC as (C1r & C2 & C10 & C11 & C56 & C8c & C8 & C9 & C19 & C20 & C21 & C22 & C23 & C25 & Ckeep & Cfr).
assert (KP : forall r, In r [3; 4; 18; 26; 27]%bv -> YK11.getr regsC r = YK11.getr regs r)
  by (rewrite Forall_forall in Ckeep; exact Ckeep).
pose proof HQ as (Qf & Qc0 & Qc).
assert (Hc0 : 0 <= cap) by (destruct Hcap; lia).
assert (Hy0 : 0 <= keys < 2 ^ 64) by (destruct Hkeys; lia).
assert (C2N : ReaderRes.cap2 cap = if cap =? 0 then 8 else 2 * cap) by reflexivity.
assert (Hcp : 1 <= ReaderRes.cap2 cap) by (rewrite C2N; destruct (Z.eqb_spec cap 0); lia).
assert (Hcq : cap <= ReaderRes.cap2 cap) by (rewrite C2N; destruct (Z.eqb_spec cap 0); lia).
assert (HM : 56 * ReaderRes.cap2 cap + 16 < 2 ^ 28) by (unfold MALLOC_MAX, HEAD in HMAX; exact HMAX).
assert (Wv : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z) by (intros z Hz; unfold w64; apply wz; exact Hz).
(* ---- the trace's charges ---- *)
assert (RL : rd_live (grow_tr ty cap cap) =
  56 * ReaderRes.cap2 cap + HEAD + (if ty =? 6 then 8 * ReaderRes.cap2 cap + HEAD else 0)).
{ unfold rd_live, grow_tr. rewrite Z.eqb_refl. destruct (ty =? 6); cbn [fold_right PjGrammar.esize];
  rewrite ?Z2Nat.id by lia; lia. }
assert (RE : rd_ev (grow_tr ty cap cap) = (if cap =? 0 then 1 else 3) + (if ty =? 6 then (if cap =? 0 then 1 else 3) else 0)).
{ unfold rd_ev, grow_tr. rewrite Z.eqb_refl.
  destruct (Z.eqb_spec cap 0) as [E0|E0].
  - subst cap. destruct (ty =? 6); cbn; reflexivity.
  - assert (N1 : Nat.eqb (Z.to_nat (56 * cap)) 0 = false) by (apply Nat.eqb_neq; lia).
    assert (N2 : Nat.eqb (Z.to_nat (8 * cap)) 0 = false) by (apply Nat.eqb_neq; lia).
    destruct (ty =? 6); cbn [fold_right]; rewrite ?N1, ?N2; unfold EV_fuzz_realloc, EV_fuzz_malloc; lia. }
assert (RH : PjGrammar.held (grow_tr ty cap cap) =
  (56 * ReaderRes.cap2 cap - 56 * cap) + (if ty =? 6 then 8 * ReaderRes.cap2 cap - 8 * cap else 0)).
{ unfold grow_tr. rewrite Z.eqb_refl. destruct (ty =? 6); cbn [PjGrammar.held PjGrammar.held_ev];
  rewrite ?Z2Nat.id by lia; lia. }
assert (RN : Z.of_nat (length (grow_tr ty cap cap)) = if ty =? 6 then 2 else 1).
{ unfold grow_tr. rewrite Z.eqb_refl. destruct (ty =? 6); reflexivity. }
assert (EK : ReaderRes.kids_blk kids cap = if cap =? 0 then [] else [(kids, 56 * cap)]) by reflexivity.
assert (EY : ReaderRes.keys_blk ty keys cap = if (cap =? 0) || negb (ty =? 6) then [] else [(keys, 8 * cap)])
  by reflexivity.
assert (RS : rd_sum Dold0 = 56 * cap + (if ty =? 6 then 8 * cap else 0)).
{ change Dold0 with (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk ty keys cap). rewrite EK, EY.
  destruct (Z.eqb_spec cap 0) as [E0|E0]; [subst cap; destruct (ty =? 6); unfold rd_sum; cbn; lia|].
  destruct (ty =? 6); unfold rd_sum; cbn [orb negb fold_right app snd]; lia. }
rewrite RL in HLIVE, HLV. rewrite RE in HEV. rewrite RS in HRS. rewrite RN in Qc.
(* ---- the old blocks ---- *)
assert (KZ : ghide (cap = 0 -> kids = 0)) by (intros E; exact (proj1 (Hcap0 E))).
assert (YZ : ghide (cap = 0 -> ty = 6 -> keys = 0)) by (intros E; exact (proj2 (Hcap0 E))).
assert (KIN : ghide (cap <> 0 -> In (kids, 56 * cap) Dold0)) by (intros E; exact (proj1 (Hcapp ltac:(lia)))).
assert (YIN : ghide (cap <> 0 -> ty = 6 -> In (keys, 8 * cap) Dold0)) by (intros E H6; exact (proj2 (Hcapp ltac:(lia)) H6)).
assert (KRB : ghide (cap <> 0 -> fs_rblock tfibsegs B ly S W mem kids (56 * cap))) by (intros E; exact (HBLK _ _ (KIN E))).
assert (YRB : ghide (cap <> 0 -> ty = 6 -> fs_rblock tfibsegs B ly S W mem keys (8 * cap)))
  by (intros E H6; exact (HBLK _ _ (YIN E H6))).
assert (KLO : ghide (cap <> 0 -> 4096 + HEAD <= kids /\ kids + 56 * cap <= alloc_ceiling))
  by (intros E; exact (fsw_rblock_low B ly S W (unpoison U mem) md mem kids _ HAR (KRB E))).
assert (YLO : ghide (cap <> 0 -> ty = 6 -> 4096 + HEAD <= keys /\ keys + 8 * cap <= alloc_ceiling))
  by (intros E H6; exact (fsw_rblock_low B ly S W (unpoison U mem) md mem keys _ HAR (YRB E H6))).
assert (KAP : ghide (cap <> 0 -> PjStruct.pj_apart [(kids, 56 * cap)] v))
  by (intros E b x Hb Hx; apply (HAPART b x); [destruct Hb as [<-|[]]; exact (KIN E) | exact Hx]).
assert (YAP : ghide (cap <> 0 -> ty = 6 -> PjStruct.pj_apart [(keys, 8 * cap)] v))
  by (intros E H6 b x Hb Hx; apply (HAPART b x); [destruct Hb as [<-|[]]; exact (YIN E H6) | exact Hx]).
assert (VK : ghide (cap <> 0 -> forall x, v <= x < v + 56 -> ~ (kids - HEAD <= x < kids + 56 * cap)))
  by (intros E; exact (grow_v_off_rblk B ly S W (unpoison U mem) md mem v kids (56 * cap) HAR HPO (proj1 (KRB E)) ltac:(lia) (KAP E))).
assert (VY : ghide (cap <> 0 -> ty = 6 -> forall x, v <= x < v + 56 -> ~ (keys - HEAD <= x < keys + 8 * cap)))
  by (intros E H6; exact (grow_v_off_rblk B ly S W (unpoison U mem) md mem v keys (8 * cap) HAR HPO (proj1 (YRB E H6)) ltac:(lia) (YAP E H6))).
assert (KYD : ghide (cap <> 0 -> ty = 6 -> kids + 56 * cap <= keys - HEAD \/ keys + 8 * cap <= kids - HEAD)).
{ intros E H6.
  pose proof (sep_blocks tfibsegs B LAWS ly S W (unpoison U mem) md _ _ _ _ HAR (proj1 (KRB E)) (proj1 (YRB E H6))
    ltac:(intros Eq; injection Eq as _ Eq; lia)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite !grow_req in D by lia. unfold HEAD in *. lia. }
(* ---- v's placement at entry, its container not an old block ---- *)
assert (PL : ghide ((exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= v /\ v + 56 <= frame_addr ly cid pos + fs_frame_bytes cid) \/
             (exists b m, In (b, m) (ablocks B ly S) /\ b + HEAD <= v /\ v + 56 <= b + req_size m /\ ~ In (b, m) (rd_hblocks Dold0)))).
{ unfold ghide. destruct HPO as [[((cid & pos & Hin & _ & _ & H1 & H2) & _)|((b & m & Hin & H1 & H2) & _)] _]; [left; exists cid, pos; auto|right].
  exists b, m. split; [exact Hin|]. split; [exact H1|]. split; [exact H2|].
  intros Hbm. unfold rd_hblocks in Hbm. apply in_map_iff in Hbm as ((a & k) & Eb & Hak). cbn [fst snd] in Eb.
  injection Eb as <- <-. pose proof (HBLK a k Hak) as (_ & _ & Hk & _).
  rewrite grow_req in H2 by lia.
  apply (HAPART (a, k) v Hak); [unfold PjStruct.pj_holds; cbn [fst snd]; unfold HEAD in *; lia | lia]. }
assert (VNI : forall x, v <= x < v + 56 -> ~ in_img tfibsegs x).
{ intros x Hx. refine (proj2 (al_client_img tfibsegs B LAWS ly S W (unpoison U mem) md x HAR _)).
  destruct PL as [(cid & pos & Hin & H1 & H2)|(b & m & Hin & H1 & H2 & _)];
    [right; left; exists cid, pos; split; [exact Hin | lia] | left; exists b, m; split; [exact Hin | unfold HEAD in *; lia]]. }
assert (FPa : forall a, v + 24 <= a < v + 40 \/ v + 48 <= a < v + 56 -> inFP FP a).
{ intros a [Ha|Ha]; [exists (v + 24, v + 40) | exists (v + 48, v + 56)];
    (split; [unfold FP, grow_FP; apply in_or_app; left; cbn [In]; tauto | cbn [fst snd]; lia]). }
assert (FPs : forall a, inFP FS_PSTAT_FP a -> inFP FP a)
  by (intros a Ha; unfold FP, grow_FP; apply inFP_app; right; apply inFP_app; right; exact Ha).
assert (FPb : forall a k x, In (a, k) Dold0 -> 0 < k -> a - HEAD <= x < a + k -> inFP FP x)
  by (intros a k x Hin Hk Hx; unfold FP, grow_FP; apply inFP_app; right; apply inFP_app; left; exact (grow_inFP_blk Dold0 a k x Hin Hk Hx)).
(* ---- the call of fuzz_realloc (kids) ---- *)
assert (KU : ghide (cap <> 0 -> exists U1 U2, U = U1 ++ (kids - HEAD, HEAD) :: U2)).
{ intros E. apply in_split. apply HINCL. unfold rd_heads. apply (in_map (fun b => (fst b - HEAD, HEAD)) _ (kids, 56 * cap)). exact (KIN E). }
assert (RBC : ghide (cap <> 0 -> fs_rblock tfibsegs B ly S W memC kids (56 * cap)))
  by (intros E; exact (fs_rblock_below B ly S W (unpoison U mem) md mem memC kids _ HAR SB (KRB E))).
assert (OLD1 : exists old1, ghide (cap = 0 -> old1 = []) /\
  ghide (cap <> 0 -> Z.of_nat (length old1) = 56 * cap /\ zbytes_at tfibsegs W memC kids old1)).
{ unfold ghide. destruct (Z.eq_dec cap 0) as [E|E]; [exists []; split; [intros _; reflexivity | intros Hn0; contradiction]|].
  destruct (grow_block_bytes B ly S U W memC md1 kids (56 * cap) HARU (RBC E)) as (o & Ho1 & Ho2).
  exists o. split; [intros Hn0; contradiction | intros _; split; assumption]. }
destruct OLD1 as (old1 & OLD1z & OLD1n).
assert (HRO1 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memC)) by exact (arodata_below B W mem memC SB HRO).
assert (PRE1 : fpreU tfibsegs B STK_fuzz_realloc ly S U W regsC memC md1 []).
{ apply (fsw_fpreU_atFP B STK_grow (spZ regs) FP ly S U W (unpoison U mem) md [] ly S W memC md1 0 regsC STK_fuzz_realloc (-96) [] HJ HARU HRO1).
  - lia.
  - reflexivity.
  - lia.
  - rewrite FSr; lia.
  - rewrite FSr, FSg; lia.
  - unfold YK0s.ret_ok. rewrite C1r. vm_compute. reflexivity.
  - unfold raZ. rewrite C1r, Wv by lia. lia.
  - rewrite (KP 3%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact Hgp.
  - rewrite (KP 4%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact Htp.
  - apply achain_low. unfold s0Z. rewrite C8, Wv by lia. lia. }
apply (@grow_realloc_step fx rc SK B fuzz_realloc_holds ly S U W regsC memC md1 [] kids (56 * cap) (56 * ReaderRes.cap2 cap) old1 live peak cnt fail
  (ReaderRes.kids_blk kids cap)).
{ exact PRE1. }
{ exact HHEADS. }
{ exact C10. }
{ exact C11. }
{ lia. }
{ exact HMAX. }
{ exact (fs_glob_below W mem memC live peak cnt fail SB HG). }
{ destruct (ty =? 6); unfold HEAD in *; lia. }
{ destruct (ty =? 6); lia. }
{ rewrite Qf. unfold SIZE_MAXZ. destruct (ty =? 6); lia. }
{ destruct (Z.eq_dec cap 0) as [E|E].
  - left. rewrite (KZ E). split; [reflexivity|]. split; [lia|]. split; [exact (OLD1z E)|].
    unfold ReaderRes.kids_blk. rewrite (proj2 (Z.eqb_eq cap 0) E). reflexivity.
  - right. split; [pose proof (KLO E); unfold HEAD in *; lia|].
    split; [rewrite EK, (proj2 (Z.eqb_neq cap 0) E); reflexivity|].
    split; [exact (KU E)|]. split; [exact (RBC E)|]. split; [exact (proj1 (OLD1n E))|]. split; [exact (proj2 (OLD1n E))|].
    destruct (ty =? 6); lia. }
{ destruct (Z.eq_dec cap 0) as [E|E].
  - rewrite (KZ E). cbn [Z.eqb]. rewrite (proj2 (Z.eqb_eq cap 0) E) in HEV. unfold EV_fuzz_malloc. destruct (ty =? 6); lia.
  - rewrite (proj2 (Z.eqb_neq kids 0) ltac:(pose proof (KLO E); unfold HEAD in *; lia)).
    rewrite (proj2 (Z.eqb_neq cap 0) E) in HEV. destruct (ty =? 6); lia. }
{ destruct (ty =? 6); unfold HEAD in *; lia. }
intros ly1 S1 U1 W1 regs1 mem1 md1' res _ HJ1 OK1 PO1 HP1 R10 Rres UG1 FH1 RB1 PERM1 SURV1 ZB1 G1.
(* ================= after fuzz_realloc (kids) ================= *)
assert (KEQ1 : (if kids =? 0 then 1 else 3) = (if cap =? 0 then 1 else 3)).
{ destruct (Z.eq_dec cap 0) as [E|E]; [rewrite (KZ E), (proj2 (Z.eqb_eq cap 0) E); reflexivity|].
  rewrite (proj2 (Z.eqb_neq cap 0) E), (proj2 (Z.eqb_neq kids 0)); [reflexivity|]. pose proof (KLO E). unfold HEAD in *. lia. }
rewrite KEQ1 in HJ1.
pose proof HJ1 as (HAR1 & Hly1 & _ & _ & _ & Hfr1 & _). cbn [app] in Hfr1.
assert (RQn1 : req_size (56 * ReaderRes.cap2 cap + HEAD) = 56 * ReaderRes.cap2 cap + HEAD) by (apply grow_req; lia).
destruct (fsw_rblock_low B ly1 S1 W1 (unpoison U1 mem1) md1' mem1 res _ HAR1 RB1) as (Res1 & Res2).
pose proof RB1 as (Rin1 & Ral1 & _ & _).
assert (FP1c : forall a, inFP (FS_PSTAT_FP ++ ablocks_fp (rd_hblocks (ReaderRes.kids_blk kids cap))) a ->
   inFP FS_PSTAT_FP a \/ (cap <> 0 /\ kids - HEAD <= a < kids + 56 * cap)).
{ intros a Ha. apply inFP_app in Ha as [Ha|Ha]; [left; exact Ha|right].
  rewrite EK in Ha. destruct (Z.eqb_spec cap 0) as [E|E]; [destruct Ha as (r & [] & _)|].
  split; [exact E|]. destruct Ha as (r & Hr & Hrr). unfold ablocks_fp, rd_hblocks in Hr. cbn [map In] in Hr.
  destruct Hr as [<-|[]]. cbn [fst snd] in Hrr. rewrite grow_req in Hrr by lia. unfold HEAD in *. lia. }
assert (F1v : forall a, v <= a < v + 56 -> ~ inFP (FS_PSTAT_FP ++ ablocks_fp (rd_hblocks (ReaderRes.kids_blk kids cap))) a).
{ intros a Ha Hf. destruct (FP1c a Hf) as [Hs|(E & Hk)]; [exact (VNI a Ha (fs_pstat_img a Hs)) | exact (VK E a Ha Hk)]. }
assert (F1s : forall a, inFP (FS_PSTAT_FP ++ ablocks_fp (rd_hblocks (ReaderRes.kids_blk kids cap))) a ->
   ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)).
{ intros a Hf. destruct (FP1c a Hf) as [Hs|(E & Hk)].
  - pose proof (fs_segs_img a (fs_pstat_img a Hs)). unfold FS_IMG_END, SHADOW_OFF in *. lia.
  - apply (fsw_ablock_off_shadow B ly S W (unpoison U mem) md _ _ HAR (proj1 (KRB E))). rewrite grow_req by lia. unfold HEAD in *. lia. }
assert (HPOc : pobj tfibsegs B ly S W memC v) by exact (pobj_below B ly S W (unpoison U mem) md mem memC v HAR SB HPO).
assert (HPO1 : pobj tfibsegs B ly1 S1 W1 mem1 v)
  by exact (pobj_kept_call B _ _ _ ly S U W memC md1 ly1 S1 U1 W1 mem1 md1' _ v HJ1 HARU OK1 PO1 F1v F1s FH1 HPOc).
assert (VB1 : forall x, v <= x < v + 56 -> mrestrict (w_H W1) mem1 (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)).
{ intros x Hx. transitivity (mrestrict (w_H W) memC (Z_to_bv 64 x)).
  - refine (proj2 (fsw_journal_kept_byte B _ _ _ ly S U W memC md1 ly1 S1 U1 W1 mem1 md1' _ x HJ1 HARU OK1 PO1 _ (F1v x Hx))).
    destruct PL as [(cid & pos & Hin & H1 & H2)|(b & m & Hin & H1 & H2 & _)];
      [right; exists cid, pos; split; [exact Hin | lia] | left; exists b, m; split; [exact Hin | unfold HEAD in *; lia]].
  - unfold mrestrict. rewrite (SB x ltac:(lia)). reflexivity. }
assert (HHDR1 : PjStruct.pj_hdr tfibsegs (mrestrict (w_H W1) mem1) v ty num str kids keys cap cap).
{ apply (PjStruct.pj_hdr_eq tfibsegs (mrestrict (w_H W) mem)); [exact HHDR|].
  intros x Hx. exact (grow_word_eq _ _ (fun z => v <= z < v + 56) x VB1 Hx). }
(* the keys block across the call *)
assert (F1y : ghide (cap <> 0 -> ty = 6 -> forall x, keys - HEAD <= x < keys + 8 * cap ->
   ~ inFP (FS_PSTAT_FP ++ ablocks_fp (rd_hblocks (ReaderRes.kids_blk kids cap))) x)).
{ intros E H6 x Hx Hf. destruct (FP1c x Hf) as [Hs|(_ & Hk)].
  - apply (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md _ _ x HAR (proj1 (YRB E H6)));
      [rewrite grow_req by lia; unfold HEAD in *; lia | exact (fs_pstat_img x Hs)].
  - pose proof (KYD E H6). unfold HEAD in *. lia. }
assert (YRB1 : ghide (cap <> 0 -> ty = 6 -> fs_rblock tfibsegs B ly1 S1 W1 mem1 keys (8 * cap))).
{ intros E H6. apply (fs_rblock_kept_call B _ _ _ ly S U W memC md1 ly1 S1 U1 W1 mem1 md1' _ keys (8 * cap) HJ1 HARU OK1 PO1 (F1y E H6)).
  exact (fs_rblock_below B ly S W (unpoison U mem) md mem memC keys _ HAR SB (YRB E H6)). }
assert (YB1 : ghide (cap <> 0 -> ty = 6 -> forall x, keys <= x < keys + 8 * cap ->
   mrestrict (w_H W1) mem1 (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x))).
{ intros E H6 x Hx. transitivity (mrestrict (w_H W) memC (Z_to_bv 64 x)).
  - refine (proj2 (fsw_journal_kept_byte B _ _ _ ly S U W memC md1 ly1 S1 U1 W1 mem1 md1' _ x HJ1 HARU OK1 PO1 _
      (F1y E H6 x ltac:(unfold HEAD; lia)))).
    left. exists (keys - HEAD), (8 * cap + HEAD). split; [exact (proj1 (YRB E H6)) | rewrite grow_req by lia; unfold HEAD; lia].
  - unfold mrestrict. rewrite (SB x ltac:(pose proof (YLO E H6); lia)). reflexivity. }
assert (YS1 : ghide (cap <> 0 -> ty = 6 -> In (keys - HEAD, 8 * cap + HEAD) (ablocks B ly1 S1) /\
   (keys - HEAD, 8 * cap + HEAD) <> (res - HEAD, 56 * ReaderRes.cap2 cap + HEAD))).
{ intros E H6. apply SURV1; [exact (proj1 (YRB E H6))|]. rewrite EK, (proj2 (Z.eqb_neq cap 0) E).
  unfold rd_hblocks. cbn [map In fst snd]. intros [Eq|[]]. injection Eq as _ Eq. lia. }
(* v's container across the call: a frame of the entry frames, or a surviving block apart from the new one *)
assert (PL1 : ghide ((exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= v /\ v + 56 <= frame_addr ly cid pos + fs_frame_bytes cid) \/
   (exists b m, In (b, m) (ablocks B ly1 S1) /\ (b, m) <> (res - HEAD, 56 * ReaderRes.cap2 cap + HEAD) /\
      ~ In (b, m) (rd_hblocks Dold0) /\ b + HEAD <= v /\ v + 56 <= b + req_size m))).
{ unfold ghide. destruct PL as [PLf|(b & m & Hin & H1 & H2 & Hnd)]; [left; exact PLf|right].
  destruct (SURV1 (b, m) Hin) as (Hin1 & Hne1).
  { intros Hk. apply Hnd. change Dold0 with (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk ty keys cap).
    unfold rd_hblocks in *. rewrite map_app. apply in_or_app. left. exact Hk. }
  exists b, m. auto 7. }
assert (VR1 : forall x, v <= x < v + 56 -> ~ (res - HEAD <= x < res + 56 * ReaderRes.cap2 cap)).
{ intros x Hx Hr. destruct PL1 as [(cid & pos & Hin & H1 & H2)|(b & m & Hin1 & Hne & _ & H1 & H2)].
  - assert (Hin1 : In (cid, pos) (frames S1)) by (rewrite Hfr1; exact Hin).
    pose proof (sep_block_frame tfibsegs B LAWS ly1 S1 W1 _ md1' _ _ cid pos HAR1 Rin1 Hin1) as D.
    destruct (al_layout tfibsegs B LAWS ly S W (unpoison U mem) md ly1 HAR Hly1) as (_ & HFA & _).
    rewrite HFA in D. unfold zdisjoint in D. cbn [fst snd] in D. rewrite RQn1 in D. unfold HEAD in *. lia.
  - pose proof (sep_blocks tfibsegs B LAWS ly1 S1 W1 _ md1' b m _ _ HAR1 Hin1 Rin1 Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite RQn1 in D. unfold HEAD in *. lia. }
(* registers after the call *)
assert (R2 : YK11.getr regs1 2 = YK11.getr regsC 2) by exact (HP1 2 ltac:(unfold acallee_saved; lia)).
assert (R8 : YK11.getr regs1 8 = w64 (v + 48)) by (rewrite <- C8; exact (HP1 8 ltac:(unfold acallee_saved; lia))).
assert (R9 : YK11.getr regs1 9 = w64 v) by (rewrite <- C9; exact (HP1 9 ltac:(unfold acallee_saved; lia))).
assert (R19 : YK11.getr regs1 19 = w64 (8 * ReaderRes.cap2 cap)) by (rewrite <- C19; exact (HP1 19 ltac:(unfold acallee_saved; lia))).
assert (R21 : YK11.getr regs1 21 = w64 (SHADOW_OFF + (v + 48) / 8)) by (rewrite <- C21; exact (HP1 21 ltac:(unfold acallee_saved; lia))).
assert (R22 : YK11.getr regs1 22 = w64 (ReaderRes.cap2 cap)) by (rewrite <- C22; exact (HP1 22 ltac:(unfold acallee_saved; lia))).
assert (R23 : YK11.getr regs1 23 = w64 SHADOW_OFF) by (rewrite <- C23; exact (HP1 23 ltac:(unfold acallee_saved; lia))).
assert (R25 : YK11.getr regs1 25 = w64 (SHADOW_OFF + (v + 24) / 8)) by (rewrite <- C25; exact (HP1 25 ltac:(unfold acallee_saved; lia))).
assert (R3 : YK11.getr regs1 3 = YK11.getr regs 3)
  by (rewrite <- (KP 3%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact (HP1 3 ltac:(unfold acallee_saved; lia))).
assert (R4 : YK11.getr regs1 4 = YK11.getr regs 4)
  by (rewrite <- (KP 4%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact (HP1 4 ltac:(unfold acallee_saved; lia))).
assert (R26 : YK11.getr regs1 26 = YK11.getr regs 26)
  by (rewrite <- (KP 26%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact (HP1 26 ltac:(unfold acallee_saved; lia))).
assert (R27 : YK11.getr regs1 27 = YK11.getr regs 27)
  by (rewrite <- (KP 27%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact (HP1 27 ltac:(unfold acallee_saved; lia))).
assert (SP1 : spZ regs1 = spZ regs - 96) by (unfold spZ at 1; rewrite R2; exact C2).
assert (SH24 : 0 <= SHADOW_OFF + (v + 24) / 8 < 2 ^ 64) by (pose proof (Z.div_pos (v + 24) 8); pose proof (Z.div_le_upper_bound (v + 24) 8 (2 ^ 60)); unfold SHADOW_OFF; lia).
assert (SH48 : 0 <= SHADOW_OFF + (v + 48) / 8 < 2 ^ 64) by (pose proof (Z.div_pos (v + 48) 8); pose proof (Z.div_le_upper_bound (v + 48) 8 (2 ^ 60)); unfold SHADOW_OFF; lia).
assert (SH32 : 0 <= SHADOW_OFF + (v + 32) / 8 < 2 ^ 64) by (pose proof (Z.div_pos (v + 32) 8); pose proof (Z.div_le_upper_bound (v + 32) 8 (2 ^ 60)); unfold SHADOW_OFF; lia).
set (xs := grow_xsB cnt fail live peak ty keys regs).
assert (EE1 : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew (Ereg regs1 (fs_extraT ++ xs)) n = YK11.getr regs1 r)
  by (intros r n0 Hn0; apply ew_Ereg_nat; exact Hn0).
assert (AC1 : ajournal tfibsegs B STK_grow (spZ regs) FP ly S W (unpoison U mem) md [] ly1 S1 W1 (unpoison U1 mem1) md1'
    (0 + (if cap =? 0 then 1 else 3)) /\
  ARU tfibsegs B ly1 S1 U1 W1 mem1 md1' /\
  st_ok tfibsegs (Ereg regs1 (fs_extraT ++ xs)) (fss_retT 0x83d68 96 gB_cs gB_rs gB_gf)
    (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 0x83d68) mem1 (seg_rom tfibsegs)))).
{ apply (fsw_after_callFPU_args B STK_grow (spZ regs) FP [] ly S U W mem md W ly S U memC md1 0 STK_fuzz_realloc
    (FS_PSTAT_FP ++ ablocks_fp (rd_hblocks (ReaderRes.kids_blk kids cap))) 96 regsC ly1 S1 U1 W1 regs1 mem1 md1' _ xs
    gB_cs gB_rs gB_gf 0x83d68 (proj1 HSS) (proj2 HSS) HJ HARU HJ1).
  - intros a Ha. destruct (FP1c a Ha) as [Hs|(E & Hk)].
    + right; right; left. split; [exact (FPs a Hs) | exact (fs_pstat_img a Hs)].
    + left. split; [exact (FPb kids (56 * cap) a (KIN E) ltac:(lia) Hk)|].
      exists (kids - HEAD), (56 * cap + HEAD). split; [exact (proj1 (KRB E)) | rewrite grow_req by lia; unfold HEAD in *; lia].
  - exact OK1.
  - exact PO1.
  - exact HP1.
  - exact C2.
  - lia.
  - rewrite FSr; lia.
  - rewrite FSr, FSg; lia.
  - reflexivity.
  - vm_compute; reflexivity.
  - unfold gB_cs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.
  - apply (grow_frame_chunks regs1 xs _ (spZ regs) regs); [reflexivity | exact Cfr].
  - apply (gB_rs_ok (Ereg regs1 (fs_extraT ++ xs)) (w_H W1) mem1 v ty keys).
    + rewrite (EE1 9%bv 9%nat eq_refl), R9. reflexivity.
    + rewrite (EE1 8%bv 8%nat eq_refl), R8. reflexivity.
    + rewrite (EE1 25%bv 25%nat eq_refl), R25. apply Wv. exact SH24.
    + rewrite (EE1 21%bv 21%nat eq_refl), R21. apply Wv. exact SH48.
    + subst xs. rewrite fsw_ew_xatom. reflexivity.
    + subst xs. rewrite fsw_ew_xatom. reflexivity.
    + lia.
    + lia.
    + exact Hv8.
    + destruct HPO1 as [_ Hw]. exact Hw.
    + apply fsw_pj_u32_val. exact (proj1 (proj2 HHDR1)).
    + destruct Hty as (Hty32 & _). exact Hty32.
    + apply fsw_pj_u64_val. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HHDR1)))))).
    + exact Hy0.
    + destruct HPO1 as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr.
  - apply (gB_disj (Ereg regs1 (fs_extraT ++ xs)) (spZ regs) v).
    + rewrite (EE1 2%bv 2%nat eq_refl). exact SP1.
    + rewrite (EE1 9%bv 9%nat eq_refl), R9. apply Wv. lia.
    + rewrite (EE1 8%bv 8%nat eq_refl), R8. apply Wv. lia.
    + rewrite (EE1 25%bv 25%nat eq_refl), R25. apply Wv. exact SH24.
    + rewrite (EE1 21%bv 21%nat eq_refl), R21. apply Wv. exact SH48.
    + rewrite FSg in Hceil. lia.
    + lia.
    + lia.
    + exact Hvimg.
    + exact Hvsh.
  - unfold gB_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EE1 9%bv 9%nat eq_refl), (EE1 8%bv 8%nat eq_refl), (EE1 23%bv 23%nat eq_refl), (EE1 10%bv 10%nat eq_refl), R9, R8, R23, R10.
    rewrite !Wv by (unfold SHADOW_OFF in *; lia). rewrite (Wv res) by (unfold HEAD in *; lia).
    change (2 ^ 3) with 8. change (2 ^ 0) with 1. change (2 ^ 4) with 16.
    assert (M48 : (v + 48) mod 8 = 0) by (rewrite Z.add_mod, Hv8 by lia; reflexivity).
    repeat split; try lia; try (apply Z.mod_1_r); try exact Hv8; try exact M48; try exact Ral1. }
destruct AC1 as (HJ1' & HARU1 & HS1).
rewrite C1r. change (w64 0x83d68) with (Z_to_bv 64 0x83d68).
(* ================= stage B ================= *)
apply (@grow_stageB fx rc SK B ly S W (unpoison U mem) md [] ly1 S1 U1 W1 regs regs1 mem1 md1' STK_grow (spZ regs) FP
  (0 + (if cap =? 0 then 1 else 3)) v res (ReaderRes.cap2 cap) cnt fail live peak ty keys _ HS1 HJ1' HARU1).
{ exact SP1. }
{ reflexivity. }
{ rewrite FSg; lia. }
{ exact R9. }
{ exact R8. }
{ exact R10. }
{ exact R22. }
{ exact R23. }
{ repeat constructor; assumption. }
{ lia. }
{ lia. }
{ exact Hv8. }
{ unfold HEAD in *; lia. }
{ lia. }
{ lia. }
{ exact Hy0. }
{ destruct HPO1 as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr. }
{ exact Hvsh. }
{ apply (grow_awr B ly S ly1 S1 W1 mem1 STK_grow (spZ regs) FP [] v (v + 24) (v + 32) HPO1 Hfr1); [lia | lia | intros a Ha; apply FPa; lia]. }
{ apply (grow_awr B ly S ly1 S1 W1 mem1 STK_grow (spZ regs) FP [] v (v + 48) (v + 56) HPO1 Hfr1); [lia | lia | intros a Ha; apply FPa; lia]. }
(* ================= type 6: the call of fuzz_realloc (keys) and stage C ================= *)
{ intros Hty6 regsC2 memC2 mat2 HC2 FR2 MG2 VK2 HJ2 HARU2.
  set (md2 := with_vm_backing (m_vm_lazy md1') mat2 md1') in *.
  pose proof HC2 as (D1 & D2 & D10 & D11 & D9 & D18 & D23 & Dkeep & Dfr).
  assert (KP2 : forall r, In r [3; 4; 8; 19; 20; 21; 22; 24; 25; 26; 27]%bv -> YK11.getr regsC2 r = YK11.getr regs1 r)
    by (rewrite Forall_forall in Dkeep; exact Dkeep).
  assert (EYs : ReaderRes.keys_blk ty keys cap = if cap =? 0 then [] else [(keys, 8 * cap)])
    by (rewrite EY, (proj2 (Z.eqb_eq ty 6) Hty6); cbn [negb]; rewrite orb_false_r; reflexivity).
  assert (FR2' : forall x, 0 <= x < alloc_ceiling -> ~ (v <= x < v + 56) -> memC2 (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x))
    by (intros x Hx Hv; apply FR2; lia).
  assert (YRBc : ghide (cap <> 0 -> fs_rblock tfibsegs B ly1 S1 W1 memC2 keys (8 * cap))).
  { intros E. apply (grow_rblock_eq B ly1 S1 W1 mem1 memC2 keys (8 * cap)); [|exact (YRB1 E Hty6)].
    intros x Hx. apply FR2'; [pose proof (YLO E Hty6); unfold HEAD in *; lia|].
    intros Hv. apply (VY E Hty6 x Hv). unfold HEAD in *. lia. }
  assert (OLD2 : exists old2, ghide (cap = 0 -> old2 = []) /\
     ghide (cap <> 0 -> Z.of_nat (length old2) = 8 * cap /\ zbytes_at tfibsegs W1 memC2 keys old2)).
  { unfold ghide. destruct (Z.eq_dec cap 0) as [E|E]; [exists []; split; [intros _; reflexivity | intros Hn0; contradiction]|].
    destruct (grow_block_bytes B ly1 S1 U1 W1 memC2 md2 keys (8 * cap) HARU2 (YRBc E)) as (o & Ho1 & Ho2).
    exists o. split; [intros Hn0; contradiction | intros _; split; assumption]. }
  destruct OLD2 as (old2 & OLD2z & OLD2n).
  assert (IMG2 : forall x, in_img tfibsegs x -> memC2 (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x)).
  { intros x Hx. pose proof (fs_segs_img x Hx). apply FR2'; [unfold FS_IMG_END in *; lia|]. intros Hv. exact (VNI x Hv Hx). }
  assert (HRO2 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W1) memC2)).
  { apply (grow_arodata_img B W1 mem1 memC2 IMG2).
    apply (arodata_kept B _ _ _ ly S U W memC md1 ly1 S1 U1 W1 mem1 md1' _ HJ1 HARU OK1 PO1).
    - apply sink_closed_pos. apply Forall_app. split; [unfold FS_PSTAT_FP; repeat constructor; cbn [fst]; lia|].
      rewrite EK. destruct (Z.eqb_spec cap 0) as [E|E]; [constructor|].
      unfold ablocks_fp, rd_hblocks. cbn [map]. constructor; [cbn [fst]; pose proof (KLO E); unfold HEAD in *; lia | constructor].
    - intros a Ha Hf. destruct (FP1c a Hf) as [Hs|(E & Hk)]; [exact (fs_pstat_not_ro a Hs Ha)|].
      apply (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md _ _ a HAR (proj1 (KRB E)));
        [rewrite grow_req by lia; unfold HEAD in *; lia | exact (fsw_roP_img a Ha)].
    - exact HRO1. }
  assert (Q8 : YK11.getr regsC2 8 = w64 (v + 48))
    by (rewrite (KP2 8%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R8).
  assert (PRE2 : fpreU tfibsegs B STK_fuzz_realloc ly1 S1 U1 W1 regsC2 memC2 md2 []).
  { apply (fsw_fpreU_atFP B STK_grow (spZ regs) FP ly S U1 W (unpoison U mem) md [] ly1 S1 W1 memC2 md2 _ regsC2 STK_fuzz_realloc (-96) []
      HJ2 HARU2 HRO2).
    - rewrite D2, SP1. lia.
    - reflexivity.
    - lia.
    - rewrite FSr; lia.
    - rewrite FSr, FSg; lia.
    - unfold YK0s.ret_ok. rewrite D1. vm_compute. reflexivity.
    - unfold raZ. rewrite D1, Wv by lia. lia.
    - rewrite (KP2 3%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))), R3. exact Hgp.
    - rewrite (KP2 4%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))), R4. exact Htp.
    - apply achain_low. unfold s0Z. rewrite Q8, Wv by lia. lia. }
  apply (@grow_realloc_step fx rc SK B fuzz_realloc_holds ly1 S1 U1 W1 regsC2 memC2 md2 [] keys (8 * cap) (8 * ReaderRes.cap2 cap) old2
    (live - 56 * cap + 56 * ReaderRes.cap2 cap) (Z.max peak (live - 56 * cap + 56 * ReaderRes.cap2 cap)) (cnt + 1) fail
    (ReaderRes.keys_blk ty keys cap)).
  { exact PRE2. }
  { exact FH1. }
  { exact D10. }
  { rewrite D11. exact R19. }
  { lia. }
  { unfold MALLOC_MAX, HEAD. lia. }
  { exact (grow_glob_img W1 mem1 memC2 _ _ _ _ IMG2 G1). }
  { rewrite (proj2 (Z.eqb_eq ty 6) Hty6) in HLIVE. unfold HEAD in *. lia. }
  { rewrite (proj2 (Z.eqb_eq ty 6) Hty6) in Qc. lia. }
  { rewrite Qf. unfold SIZE_MAXZ. rewrite (proj2 (Z.eqb_eq ty 6) Hty6) in Qc. lia. }
  { destruct (Z.eq_dec cap 0) as [E|E].
    - left. rewrite (YZ E Hty6). split; [reflexivity|]. split; [lia|]. split; [exact (OLD2z E)|].
      unfold ReaderRes.keys_blk. rewrite (proj2 (Z.eqb_eq cap 0) E). reflexivity.
    - right. split; [pose proof (YLO E Hty6); unfold HEAD in *; lia|].
      split; [rewrite EYs, (proj2 (Z.eqb_neq cap 0) E); reflexivity|].
      split.
      { assert (Hy : In (keys - HEAD, HEAD) U).
        { apply HINCL. unfold rd_heads. apply (in_map (fun b => (fst b - HEAD, HEAD)) _ (keys, 8 * cap)). exact (YIN E Hty6). }
        destruct UG1 as [(Hk0' & _) | (_ & Ua & Ub & EU & EU1)]; [exfalso; pose proof (KLO E); unfold HEAD in *; lia|].
        apply in_split. rewrite EU1. rewrite EU in Hy. apply in_app_or in Hy as [Hy|[Hy|Hy]].
        - apply in_or_app. left. exact Hy.
        - exfalso. injection Hy. intros. pose proof (KYD E Hty6). unfold HEAD in *. lia.
        - apply in_or_app. right. apply in_or_app. left. exact Hy. }
      split; [exact (YRBc E)|]. split; [exact (proj1 (OLD2n E))|]. split; [exact (proj2 (OLD2n E))|].
      rewrite C2N, (proj2 (Z.eqb_neq cap 0) E). rewrite (proj2 (Z.eqb_eq ty 6) Hty6) in HRS. lia. }
  { pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
    rewrite (proj2 (Z.eqb_eq ty 6) Hty6) in HEV.
    destruct (Z.eq_dec cap 0) as [E|E].
    - rewrite (YZ E Hty6). cbn [Z.eqb]. rewrite (proj2 (Z.eqb_eq cap 0) E) in HEV, Hnev2. unfold EV_fuzz_malloc. lia.
    - rewrite (proj2 (Z.eqb_neq keys 0)) by (pose proof (YLO E Hty6); unfold HEAD in *; lia).
      rewrite (proj2 (Z.eqb_neq cap 0) E) in HEV, Hnev2. lia. }
  { rewrite (grow_bb B ly1 S1). pose proof (grow_rsum_perm _ _ PERM1) as PS. rewrite !grow_rsum_app in PS.
    rewrite (grow_bb B ly S) in HLV. rewrite (proj2 (Z.eqb_eq ty 6) Hty6) in HLV.
    assert (RS1 : rd_sum [(res - HEAD, 56 * ReaderRes.cap2 cap + HEAD)] = 56 * ReaderRes.cap2 cap + HEAD)
      by (unfold rd_sum; cbn [fold_right snd]; lia).
    assert (RS0 : 0 <= rd_sum (rd_hblocks (ReaderRes.kids_blk kids cap)))
      by (rewrite EK; destruct (Z.eqb_spec cap 0); unfold rd_sum, rd_hblocks; cbn [map fold_right snd]; unfold HEAD; lia).
    unfold HEAD in *. lia. }
  intros ly2 S2 U2 W2 regs2 mem2 md2' y2 _ HJc2 OK2 PO2 HP2 R10b Ry UG2 FH2 RB2 PERM2 SURV2 ZB2 G2.
  (* ================= after fuzz_realloc (keys) ================= *)
  assert (KEQ2 : (if keys =? 0 then 1 else 3) = (if cap =? 0 then 1 else 3)).
  { destruct (Z.eq_dec cap 0) as [E|E]; [rewrite (YZ E Hty6), (proj2 (Z.eqb_eq cap 0) E); reflexivity|].
    rewrite (proj2 (Z.eqb_neq cap 0) E), (proj2 (Z.eqb_neq keys 0)); [reflexivity|]. pose proof (YLO E Hty6). unfold HEAD in *. lia. }
  rewrite KEQ2 in HJc2.
  pose proof HJc2 as (HAR2 & Hly2 & _ & _ & _ & Hfr2 & _). cbn [app] in Hfr2.
  assert (RQn2 : req_size (8 * ReaderRes.cap2 cap + HEAD) = 8 * ReaderRes.cap2 cap + HEAD) by (apply grow_req; lia).
  destruct (fsw_rblock_low B ly2 S2 W2 (unpoison U2 mem2) md2' mem2 y2 _ HAR2 RB2) as (Ry1 & Ry2).
  pose proof RB2 as (Yin2 & Yal2 & _ & _).
  assert (FP2c : forall a, inFP (FS_PSTAT_FP ++ ablocks_fp (rd_hblocks (ReaderRes.keys_blk ty keys cap))) a ->
     inFP FS_PSTAT_FP a \/ (cap <> 0 /\ keys - HEAD <= a < keys + 8 * cap)).
  { intros a Ha. apply inFP_app in Ha as [Ha|Ha]; [left; exact Ha|right].
    rewrite EYs in Ha. destruct (Z.eqb_spec cap 0) as [E|E]; [destruct Ha as (r & [] & _)|].
    split; [exact E|]. destruct Ha as (r & Hr & Hrr). unfold ablocks_fp, rd_hblocks in Hr. cbn [map In] in Hr.
    destruct Hr as [<-|[]]. cbn [fst snd] in Hrr. rewrite grow_req in Hrr by lia. unfold HEAD in *. lia. }
  assert (F2v : forall a, v <= a < v + 56 -> ~ inFP (FS_PSTAT_FP ++ ablocks_fp (rd_hblocks (ReaderRes.keys_blk ty keys cap))) a).
  { intros a Ha Hf. destruct (FP2c a Hf) as [Hs|(E & Hk)]; [exact (VNI a Ha (fs_pstat_img a Hs)) | exact (VY E Hty6 a Ha Hk)]. }
  assert (F2s : forall a, inFP (FS_PSTAT_FP ++ ablocks_fp (rd_hblocks (ReaderRes.keys_blk ty keys cap))) a ->
     ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)).
  { intros a Hf. destruct (FP2c a Hf) as [Hs|(E & Hk)].
    - pose proof (fs_segs_img a (fs_pstat_img a Hs)). unfold FS_IMG_END, SHADOW_OFF in *. lia.
    - apply (fsw_ablock_off_shadow B ly S W (unpoison U mem) md _ _ HAR (proj1 (YRB E Hty6))). rewrite grow_req by lia. unfold HEAD in *. lia. }
  assert (HPOc2 : pobj tfibsegs B ly1 S1 W1 memC2 v).
  { apply (grow_pobj_run B ly1 S1 W1 mem1 memC2 v HPO1); [intros x Hx H1 H2; apply FR2; lia | exact MG2 | exact Hvsh | lia | lia]. }
  assert (HPO2 : pobj tfibsegs B ly2 S2 W2 mem2 v)
    by exact (pobj_kept_call B _ _ _ ly1 S1 U1 W1 memC2 md2 ly2 S2 U2 W2 mem2 md2' _ v HJc2 HARU2 OK2 PO2 F2v F2s FH2 HPOc2).
  assert (VB2 : forall x, v <= x < v + 56 -> mrestrict (w_H W2) mem2 (Z_to_bv 64 x) = mrestrict (w_H W1) memC2 (Z_to_bv 64 x)).
  { intros x Hx. refine (proj2 (fsw_journal_kept_byte B _ _ _ ly1 S1 U1 W1 memC2 md2 ly2 S2 U2 W2 mem2 md2' _ x HJc2 HARU2 OK2 PO2 _ (F2v x Hx))).
    destruct HPOc2 as [[((cid & pos & Hin & _ & _ & H1 & H2) & _)|((b & m & Hin & H1 & H2) & _)] _];
      [right; exists cid, pos; split; [exact Hin | lia] | left; exists b, m; split; [exact Hin | unfold HEAD in *; lia]]. }
  assert (F2r : forall x, res - HEAD <= x < res + 56 * ReaderRes.cap2 cap ->
     ~ inFP (FS_PSTAT_FP ++ ablocks_fp (rd_hblocks (ReaderRes.keys_blk ty keys cap))) x).
  { intros x Hx Hf. destruct (FP2c x Hf) as [Hs|(E & Hk)].
    - apply (blk_img tfibsegs B LAWS ly1 S1 W1 _ md1' _ _ x HAR1 Rin1); [rewrite RQn1; unfold HEAD in *; lia | exact (fs_pstat_img x Hs)].
    - destruct (YS1 E Hty6) as (Yin1 & Yne1).
      pose proof (sep_blocks tfibsegs B LAWS ly1 S1 W1 _ md1' _ _ _ _ HAR1 Yin1 Rin1 Yne1) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite grow_req, RQn1 in D by lia. unfold HEAD in *. lia. }
  assert (RBk : forall x, res - HEAD <= x < res + 56 * ReaderRes.cap2 cap ->
     mrestrict (w_H W2) mem2 (Z_to_bv 64 x) = mrestrict (w_H W1) mem1 (Z_to_bv 64 x)).
  { intros x Hx. transitivity (mrestrict (w_H W1) memC2 (Z_to_bv 64 x)).
    - refine (proj2 (fsw_journal_kept_byte B _ _ _ ly1 S1 U1 W1 memC2 md2 ly2 S2 U2 W2 mem2 md2' _ x HJc2 HARU2 OK2 PO2 _ (F2r x Hx))).
      left. exists (res - HEAD), (56 * ReaderRes.cap2 cap + HEAD). split; [exact Rin1 | rewrite RQn1; lia].
    - unfold mrestrict. rewrite (FR2' x); [reflexivity | lia | intros Hv; exact (VR1 x Hv Hx)]. }
  assert (RB2r : fs_rblock tfibsegs B ly2 S2 W2 mem2 res (56 * ReaderRes.cap2 cap)).
  { apply (fs_rblock_kept_call B _ _ _ ly1 S1 U1 W1 memC2 md2 ly2 S2 U2 W2 mem2 md2' _ res _ HJc2 HARU2 OK2 PO2 F2r).
    apply (grow_rblock_eq B ly1 S1 W1 mem1 memC2 res _); [|exact RB1].
    intros x Hx. apply FR2'; [unfold HEAD in *; lia|]. intros Hv. apply (VR1 x Hv). unfold HEAD in *. lia. }
  assert (VY2 : forall x, v <= x < v + 56 -> ~ (y2 - HEAD <= x < y2 + 8 * ReaderRes.cap2 cap)).
  { intros x Hx Hr. destruct PL1 as [(cid & pos & Hin & H1 & H2)|(b & m & Hin1 & Hne1 & Hnd & H1 & H2)].
    - assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfr2, Hfr1; exact Hin).
      pose proof (sep_block_frame tfibsegs B LAWS ly2 S2 W2 _ md2' _ _ cid pos HAR2 Yin2 Hin2) as D.
      destruct (al_layout tfibsegs B LAWS ly1 S1 W1 _ md2 ly2 (proj1 HARU2) Hly2) as (_ & HFA2 & _).
      destruct (al_layout tfibsegs B LAWS ly S W (unpoison U mem) md ly1 HAR Hly1) as (_ & HFA1 & _).
      rewrite HFA2, HFA1 in D. unfold zdisjoint in D. cbn [fst snd] in D. rewrite RQn2 in D. unfold HEAD in *. lia.
    - destruct (SURV2 (b, m) Hin1) as (Hin2 & Hne2).
      { intros Hk. apply Hnd. change Dold0 with (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk ty keys cap).
        unfold rd_hblocks in *. rewrite map_app. apply in_or_app. right. exact Hk. }
      pose proof (sep_blocks tfibsegs B LAWS ly2 S2 W2 _ md2' b m _ _ HAR2 Hin2 Yin2 Hne2) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite RQn2 in D. unfold HEAD in *. lia. }
  (* registers after the second call *)
  assert (T2 : YK11.getr regs2 2 = YK11.getr regsC2 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
  assert (SP2 : spZ regs2 = spZ regs - 96) by (unfold spZ at 1; rewrite T2; fold (spZ regsC2); rewrite D2; exact SP1).
  assert (T8 : YK11.getr regs2 8 = w64 (v + 48)) by (rewrite <- Q8; exact (HP2 8 ltac:(unfold acallee_saved; lia))).
  assert (T9 : YK11.getr regs2 9 = w64 (v + 32)) by (rewrite <- D9; exact (HP2 9 ltac:(unfold acallee_saved; lia))).
  assert (T21 : YK11.getr regs2 21 = w64 (SHADOW_OFF + (v + 48) / 8)).
  { rewrite <- R21, <- (KP2 21%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))).
    exact (HP2 21 ltac:(unfold acallee_saved; lia)). }
  assert (T22 : YK11.getr regs2 22 = w64 (ReaderRes.cap2 cap)).
  { rewrite <- R22, <- (KP2 22%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))).
    exact (HP2 22 ltac:(unfold acallee_saved; lia)). }
  assert (T23 : YK11.getr regs2 23 = w64 (SHADOW_OFF + (v + 32) / 8)) by (rewrite <- D23; exact (HP2 23 ltac:(unfold acallee_saved; lia))).
  assert (T3 : YK11.getr regs2 3 = YK11.getr regs 3).
  { transitivity (YK11.getr regsC2 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr regs1 3); [exact (KP2 3%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right])))|]. exact R3. }
  assert (T4 : YK11.getr regs2 4 = YK11.getr regs 4).
  { transitivity (YK11.getr regsC2 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr regs1 4); [exact (KP2 4%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right])))|]. exact R4. }
  assert (T26 : YK11.getr regs2 26 = YK11.getr regs 26).
  { transitivity (YK11.getr regsC2 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr regs1 26); [exact (KP2 26%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right])))|]. exact R26. }
  assert (T27 : YK11.getr regs2 27 = YK11.getr regs 27).
  { transitivity (YK11.getr regsC2 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr regs1 27); [exact (KP2 27%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right])))|]. exact R27. }
  assert (EE2 : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew (Ereg regs2 (fs_extraT ++ xs)) n = YK11.getr regs2 r)
    by (intros r n0 Hn0; apply ew_Ereg_nat; exact Hn0).
  assert (Dfr' : grow_frame (mrestrict (w_H W1) memC2) (spZ regs) regs)
    by (replace (spZ regs) with (spZ regs1 + 96) by lia; exact Dfr).
  assert (AC2 : ajournal tfibsegs B STK_grow (spZ regs) FP ly S W (unpoison U mem) md [] ly2 S2 W2 (unpoison U2 mem2) md2'
      (0 + (if cap =? 0 then 1 else 3) + (if cap =? 0 then 1 else 3)) /\
    ARU tfibsegs B ly2 S2 U2 W2 mem2 md2' /\
    st_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (fss_retT 0x83db8 96 gB_cs gC_rs gC_gf)
      (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x83db8) mem2 (seg_rom tfibsegs)))).
  { apply (fsw_after_callFPU_args B STK_grow (spZ regs) FP [] ly S U W1 mem md W ly1 S1 U1 memC2 md2 _ STK_fuzz_realloc
      (FS_PSTAT_FP ++ ablocks_fp (rd_hblocks (ReaderRes.keys_blk ty keys cap))) 96 regsC2 ly2 S2 U2 W2 regs2 mem2 md2' _ xs
      gB_cs gC_rs gC_gf 0x83db8 (proj1 HSS) (proj2 HSS) HJ2 HARU2 HJc2).
    - intros a Ha. destruct (FP2c a Ha) as [Hs|(E & Hk)].
      + right; right; left. split; [exact (FPs a Hs) | exact (fs_pstat_img a Hs)].
      + left. split; [exact (FPb keys (8 * cap) a (YIN E Hty6) ltac:(lia) Hk)|].
        exists (keys - HEAD), (8 * cap + HEAD). split; [exact (proj1 (YS1 E Hty6)) | rewrite grow_req by lia; unfold HEAD in *; lia].
    - exact OK2.
    - exact PO2.
    - exact HP2.
    - rewrite D2. exact SP1.
    - lia.
    - rewrite FSr; lia.
    - rewrite FSr, FSg; lia.
    - reflexivity.
    - vm_compute; reflexivity.
    - unfold gB_cs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.
    - apply (grow_frame_chunks regs2 xs _ (spZ regs) regs); [reflexivity | exact Dfr'].
    - apply (gC_rs_ok (Ereg regs2 (fs_extraT ++ xs)) (w_H W2) mem2 v).
      + rewrite (EE2 9%bv 9%nat eq_refl), T9. apply Wv. lia.
      + rewrite (EE2 8%bv 8%nat eq_refl), T8. apply Wv. lia.
      + rewrite (EE2 23%bv 23%nat eq_refl), T23. apply Wv. exact SH32.
      + rewrite (EE2 21%bv 21%nat eq_refl), T21. apply Wv. exact SH48.
      + lia.
      + lia.
      + exact Hv8.
      + destruct HPO2 as [_ Hw]. exact Hw.
      + destruct HPO2 as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr.
    - apply (gC_disj (Ereg regs2 (fs_extraT ++ xs)) (spZ regs) v).
      + rewrite (EE2 2%bv 2%nat eq_refl). exact SP2.
      + rewrite (EE2 9%bv 9%nat eq_refl), T9. apply Wv. lia.
      + rewrite (EE2 8%bv 8%nat eq_refl), T8. apply Wv. lia.
      + rewrite (EE2 23%bv 23%nat eq_refl), T23. apply Wv. exact SH32.
      + rewrite (EE2 21%bv 21%nat eq_refl), T21. apply Wv. exact SH48.
      + rewrite FSg in Hceil. lia.
      + lia.
      + lia.
      + exact Hvimg.
      + exact Hvsh.
    - unfold gC_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite (EE2 9%bv 9%nat eq_refl), (EE2 8%bv 8%nat eq_refl), (EE2 10%bv 10%nat eq_refl), T9, T8, R10b.
      rewrite (Wv (v + 32)), (Wv (v + 48)) by lia. rewrite (Wv y2) by (unfold HEAD in *; lia).
      change (2 ^ 3) with 8. change (2 ^ 4) with 16.
      assert (M48 : (v + 48) mod 8 = 0) by (rewrite Z.add_mod, Hv8 by lia; reflexivity).
      assert (M32 : (v + 32) mod 8 = 0) by (rewrite Z.add_mod, Hv8 by lia; reflexivity).
      repeat split; try lia; try exact M32; try exact M48; try exact Yal2. }
  destruct AC2 as (HJ2' & HARU2' & HS2).
  rewrite D1. change (w64 0x83db8) with (Z_to_bv 64 0x83db8).
  (* ================= stage C ================= *)
  apply (@grow_stageC fx rc SK B ly S W (unpoison U mem) md [] ly2 S2 U2 W2 regs regs2 mem2 md2' STK_grow (spZ regs) FP _ v y2
    (ReaderRes.cap2 cap) cnt fail live peak ty keys _ HS2 HJ2' HARU2').
  { exact SP2. }
  { reflexivity. }
  { rewrite FSg; lia. }
  { exact T9. }
  { exact T8. }
  { exact R10b. }
  { exact T22. }
  { repeat constructor; assumption. }
  { lia. }
  { lia. }
  { exact Hv8. }
  { unfold HEAD in *; lia. }
  { lia. }
  { apply (grow_awr B ly S ly2 S2 W2 mem2 STK_grow (spZ regs) FP [] v (v + 32) (v + 40) HPO2 ltac:(rewrite Hfr2; exact Hfr1));
      [lia | lia | intros a Ha; apply FPa; lia]. }
  { apply (grow_awr B ly S ly2 S2 W2 mem2 STK_grow (spZ regs) FP [] v (v + 48) (v + 56) HPO2 ltac:(rewrite Hfr2; exact Hfr1));
      [lia | lia | intros a Ha; apply FPa; lia]. }
  intros E' ssf msf mat3 HSf Hrv Hpc RF1 RF10 HPf FRf MGf VYf VCf HJf HARUf.
  (* ================= the ret, type 6 ================= *)
  assert (FRw : forall x : word, v <= bv_unsigned x < v + 24 \/ v + 40 <= bv_unsigned x < v + 48 ->
      mrestrict (w_H W2) (ms_mem msf) x = mrestrict (w_H W1) mem1 x).
  { intros x Hx. pose proof (u64_range x) as Hxr.
    transitivity (mrestrict (w_H W2) mem2 x).
    { unfold mrestrict. rewrite (grow_word_eq mem2 (ms_mem msf)
        (fun z => 0 <= z < alloc_ceiling /\ ~ (v + 32 <= z < v + 40) /\ ~ (v + 48 <= z < v + 56)) x);
        [reflexivity | intros z (Hz1 & Hz2 & Hz3); exact (FRf z Hz1 Hz2 Hz3) | lia]. }
    transitivity (mrestrict (w_H W1) memC2 x).
    { apply (grow_word_eq _ _ (fun z => v <= z < v + 56) x); [exact VB2 | lia]. }
    unfold mrestrict. rewrite (grow_word_eq mem1 memC2
      (fun z => 0 <= z < alloc_ceiling /\ ~ (v + 24 <= z < v + 32) /\ ~ (v + 48 <= z < v + 56)) x);
      [reflexivity | intros z (Hz1 & Hz2 & Hz3); exact (FR2 z Hz1 Hz2 Hz3) | lia]. }
  assert (HPOf : pobj tfibsegs B ly2 S2 W2 (ms_mem msf) v).
  { apply (grow_pobj_run B ly2 S2 W2 mem2 (ms_mem msf) v HPO2); [intros x Hx H1 H2; apply FRf; lia | exact MGf | exact Hvsh | lia | lia]. }
  assert (FRm : forall x, 0 <= x < alloc_ceiling -> ~ (v <= x < v + 56) ->
     mbyte tfibsegs (mrestrict (w_H W2) (ms_mem msf)) x = mbyte tfibsegs (mrestrict (w_H W2) mem2) x).
  { intros x Hx Hv. apply grow_mbyte_eq. unfold mrestrict. rewrite FRf; [reflexivity | lia | lia | lia]. }
  eapply SRr_mono;
    [|intros W3 c3 _ HF; exists res, y2, (ReaderRes.cap2 cap), Dold0,
        [(res, 56 * ReaderRes.cap2 cap); (y2, 8 * ReaderRes.cap2 cap)], U2; split; [|exact HF]].
  2:{ right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Rres|]. split; [exact Ral1|].
      split; [intros _; split; [exact Ry | exact Yal2]|]. split; [intros H6; contradiction|].
      split; [rewrite (proj2 (Z.eqb_eq ty 6) Hty6); reflexivity|].
      exists U1. split; [exact UG1 | rewrite (proj2 (Z.eqb_eq ty 6) Hty6); exact UG2]. }
  apply (fsw_retU B grow_tbl grow_tbl_ok W2 E' ssf msf _ STK_grow (spZ regs) FP regs ly S U W mem md ly2 S2 U2
    (rd_ev (grow_tr ty cap cap)) _ HSf Hrv Hpc).
  { rewrite RF1. exact Hra. }
  { apply (ajournal_mono_k tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJf). rewrite RE, (proj2 (Z.eqb_eq ty 6) Hty6). lia. }
  { exact HARUf. }
  { exact HPf. }
  intros mat'. cbv beta.
  split; [exact RF10|].
  split.
  { change Dold0 with (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk ty keys cap).
    change (rd_hblocks [(res, 56 * ReaderRes.cap2 cap); (y2, 8 * ReaderRes.cap2 cap)])
      with ([(res - HEAD, 56 * ReaderRes.cap2 cap + HEAD)] ++ [(y2 - HEAD, 8 * ReaderRes.cap2 cap + HEAD)]).
    assert (RHA : forall A0 B0, rd_hblocks (A0 ++ B0) = rd_hblocks A0 ++ rd_hblocks B0) by (intros; unfold rd_hblocks; apply map_app).
    rewrite RHA.
    transitivity ((ablocks B ly2 S2 ++ rd_hblocks (ReaderRes.keys_blk ty keys cap)) ++ rd_hblocks (ReaderRes.kids_blk kids cap)).
    { rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
    transitivity ((ablocks B ly1 S1 ++ [(y2 - HEAD, 8 * ReaderRes.cap2 cap + HEAD)]) ++ rd_hblocks (ReaderRes.kids_blk kids cap)).
    { apply Permutation_app_tail. exact PERM2. }
    transitivity ((ablocks B ly1 S1 ++ rd_hblocks (ReaderRes.kids_blk kids cap)) ++ [(y2 - HEAD, 8 * ReaderRes.cap2 cap + HEAD)]).
    { rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
    transitivity ((ablocks B ly S ++ [(res - HEAD, 56 * ReaderRes.cap2 cap + HEAD)]) ++ [(y2 - HEAD, 8 * ReaderRes.cap2 cap + HEAD)]).
    { apply Permutation_app_tail. exact PERM1. }
    rewrite <- app_assoc. reflexivity. }
  split.
  { apply (grow_hdr_upd _ _ v ty num str kids keys cap cap res y2 (ReaderRes.cap2 cap) HHDR1).
    - exact (grow_pj_rw B ly2 S2 U2 W2 (ms_mem msf) _ v HARUf HPOf).
    - intros x Hx. apply FRw. lia.
    - apply fsw_val_pj_u64; [| unfold HEAD in *; lia | lia | lia].
      apply (grow_val_eqm (mrestrict (w_H W1) memC2)); [exact VK2|].
      intros k Hk. transitivity (mbyte tfibsegs (mrestrict (w_H W2) mem2) (v + 24 + Z.of_nat k)).
      + apply grow_mbyte_eq. unfold mrestrict. rewrite FRf; [reflexivity | lia | lia | lia].
      + apply grow_mbyte_eq. exact (VB2 (v + 24 + Z.of_nat k) ltac:(lia)).
    - apply fsw_val_pj_u64; [exact VYf | unfold HEAD in *; lia | lia | lia].
    - apply fsw_val_pj_u64; [exact VCf | lia | lia | lia]. }
  split.
  { split; [exact (proj1 HSL)|]. split; [lia|]. split; [intros; lia|]. intros _.
    unfold ReaderRes.kids_blk, ReaderRes.keys_blk. rewrite (proj2 (Z.eqb_neq (ReaderRes.cap2 cap) 0)) by lia.
    rewrite (proj2 (Z.eqb_eq ty 6) Hty6). cbn [orb negb app In].
    split; [left; reflexivity | intros _; right; left; reflexivity]. }
  split.
  { unfold ReaderRes.kids_blk, ReaderRes.keys_blk. rewrite (proj2 (Z.eqb_neq (ReaderRes.cap2 cap) 0)) by lia.
    rewrite (proj2 (Z.eqb_eq ty 6) Hty6). cbn [orb negb app].
    intros a k [Eq|[Eq|[]]]; injection Eq as <- <-.
    - apply (grow_rblock_eq B ly2 S2 W2 mem2 (ms_mem msf) res _); [|exact RB2r].
      intros x Hx. apply FRf; [unfold HEAD in *; lia | |]; intros Hv; apply (VR1 x); unfold HEAD in *; lia.
    - apply (grow_rblock_eq B ly2 S2 W2 mem2 (ms_mem msf) y2 _); [|exact RB2].
      intros x Hx. apply FRf; [unfold HEAD in *; lia | |]; intros Hv; apply (VY2 x); unfold HEAD in *; lia. }
  split.
  { intros i Hi. destruct (Z.eq_dec cap 0) as [E|E]; [lia|].
    rewrite (FRm (res + i)); [| unfold HEAD in *; lia | intros Hv; apply (VR1 (res + i) Hv); unfold HEAD in *; lia].
    rewrite (grow_mbyte_eq (w_H W1) (w_H W2) mem1 mem2 (res + i) (RBk (res + i) ltac:(unfold HEAD in *; lia))).
    rewrite Z.min_l in ZB1 by lia. rewrite firstn_all2 in ZB1 by (pose proof (proj1 (OLD1n E)); lia).
    rewrite (grow_moved _ _ res kids old1 ZB1 (proj2 (OLD1n E)) i ltac:(rewrite (proj1 (OLD1n E)); lia)).
    apply (mbyte_below (w_H W) mem memC alloc_ceiling (kids + i) SB). pose proof (KLO E). unfold HEAD in *. lia. }
  split.
  { intros _ i Hi. destruct (Z.eq_dec cap 0) as [E|E]; [lia|].
    rewrite (FRm (y2 + i)); [| unfold HEAD in *; lia | intros Hv; apply (VY2 (y2 + i) Hv); unfold HEAD in *; lia].
    rewrite Z.min_l in ZB2 by lia. rewrite firstn_all2 in ZB2 by (pose proof (proj1 (OLD2n E)); lia).
    rewrite (grow_moved _ _ y2 keys old2 ZB2 (proj2 (OLD2n E)) i ltac:(rewrite (proj1 (OLD2n E)); lia)).
    apply grow_mbyte_eq. unfold mrestrict at 1. rewrite (FR2' (keys + i)); [|pose proof (YLO E Hty6); unfold HEAD in *; lia | intros Hv; apply (VY E Hty6 (keys + i) Hv); unfold HEAD in *; lia].
    exact (YB1 E Hty6 (keys + i) ltac:(lia)). }
  split; [exact HPOf|].
  exists (Z.max (Z.max peak (live - 56 * cap + 56 * ReaderRes.cap2 cap))
    (live - 56 * cap + 56 * ReaderRes.cap2 cap - 8 * cap + 8 * ReaderRes.cap2 cap)).
  split; [lia|].
  replace (live + PjGrammar.held (grow_tr ty cap cap)) with (live - 56 * cap + 56 * ReaderRes.cap2 cap - 8 * cap + 8 * ReaderRes.cap2 cap)
    by (rewrite RH, (proj2 (Z.eqb_eq ty 6) Hty6); lia).
  replace (cnt + Z.of_nat (length (grow_tr ty cap cap))) with (cnt + 1 + 1) by (rewrite RN, (proj2 (Z.eqb_eq ty 6) Hty6); lia).
  apply (grow_glob_img W2 mem2 (ms_mem msf)); [|exact G2].
  intros x Hx. pose proof (fs_segs_img x Hx). apply (FRf x); [unfold FS_IMG_END in *; lia | |]; (intros Hv; apply (VNI x); [lia | exact Hx]). }
(* ================= other types: the ret after stage B ================= *)
intros Hty6 E' ssf msf mat2 HSf Hrv Hpc RF1 RF10 HPf FRf MGf VKf VCf HJf HARUf.
assert (EYn : ReaderRes.keys_blk ty keys cap = [])
  by (rewrite EY, (proj2 (Z.eqb_neq ty 6) Hty6); rewrite orb_true_r; reflexivity).
assert (HPOf : pobj tfibsegs B ly1 S1 W1 (ms_mem msf) v).
{ apply (grow_pobj_run B ly1 S1 W1 mem1 (ms_mem msf) v HPO1); [intros x Hx H1 H2; apply FRf; lia | exact MGf | exact Hvsh | lia | lia]. }
assert (FRm : forall x, 0 <= x < alloc_ceiling -> ~ (v <= x < v + 56) ->
   mbyte tfibsegs (mrestrict (w_H W1) (ms_mem msf)) x = mbyte tfibsegs (mrestrict (w_H W1) mem1) x).
{ intros x Hx Hv. apply grow_mbyte_eq. unfold mrestrict. rewrite FRf; [reflexivity | lia | lia | lia]. }
eapply SRr_mono;
  [|intros W3 c3 _ HF; exists res, keys, (ReaderRes.cap2 cap), Dold0, [(res, 56 * ReaderRes.cap2 cap)], U1; split; [|exact HF]].
2:{ right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Rres|]. split; [exact Ral1|].
    split; [intros H6; contradiction|]. split; [intros _; reflexivity|].
    split; [rewrite (proj2 (Z.eqb_neq ty 6) Hty6); reflexivity|].
    exists U1. split; [exact UG1 | rewrite (proj2 (Z.eqb_neq ty 6) Hty6); reflexivity]. }
apply (fsw_retU B grow_tbl grow_tbl_ok W1 E' ssf msf _ STK_grow (spZ regs) FP regs ly S U W mem md ly1 S1 U1
  (rd_ev (grow_tr ty cap cap)) _ HSf Hrv Hpc).
{ rewrite RF1. exact Hra. }
{ apply (ajournal_mono_k tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJf). rewrite RE, (proj2 (Z.eqb_neq ty 6) Hty6). lia. }
{ exact HARUf. }
{ exact HPf. }
intros mat'. cbv beta.
split; [exact RF10|].
split.
{ change Dold0 with (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk ty keys cap). rewrite EYn, app_nil_r.
  change (rd_hblocks [(res, 56 * ReaderRes.cap2 cap)]) with [(res - HEAD, 56 * ReaderRes.cap2 cap + HEAD)]. exact PERM1. }
split.
{ apply (grow_hdr_upd _ _ v ty num str kids keys cap cap res keys (ReaderRes.cap2 cap) HHDR1).
  - exact (grow_pj_rw B ly1 S1 U1 W1 (ms_mem msf) _ v HARUf HPOf).
  - intros x Hx. pose proof (u64_range x) as Hxr. unfold mrestrict.
    rewrite (grow_word_eq mem1 (ms_mem msf)
      (fun z => 0 <= z < alloc_ceiling /\ ~ (v + 24 <= z < v + 32) /\ ~ (v + 48 <= z < v + 56)) x);
      [reflexivity | intros z (Hz1 & Hz2 & Hz3); exact (FRf z Hz1 Hz2 Hz3) | lia].
  - apply fsw_val_pj_u64; [exact VKf | unfold HEAD in *; lia | lia | lia].
  - apply (PjStruct.pj_u64_eq tfibsegs (mrestrict (w_H W1) mem1)); [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HHDR1))))))|].
    intros x Hx. pose proof (u64_range x) as Hxr. unfold mrestrict.
    rewrite (grow_word_eq mem1 (ms_mem msf)
      (fun z => 0 <= z < alloc_ceiling /\ ~ (v + 24 <= z < v + 32) /\ ~ (v + 48 <= z < v + 56)) x);
      [reflexivity | intros z (Hz1 & Hz2 & Hz3); exact (FRf z Hz1 Hz2 Hz3) | lia].
  - apply fsw_val_pj_u64; [exact VCf | lia | lia | lia]. }
split.
{ split; [exact (proj1 HSL)|]. split; [lia|]. split; [intros; lia|]. intros _.
  unfold ReaderRes.kids_blk. rewrite (proj2 (Z.eqb_neq (ReaderRes.cap2 cap) 0)) by lia.
  split; [apply in_or_app; left; left; reflexivity | intros H6; contradiction]. }
split.
{ unfold ReaderRes.kids_blk, ReaderRes.keys_blk. rewrite (proj2 (Z.eqb_neq (ReaderRes.cap2 cap) 0)) by lia.
  rewrite (proj2 (Z.eqb_neq ty 6) Hty6). cbn [orb negb app].
  intros a k [Eq|[]]; injection Eq as <- <-.
  apply (grow_rblock_eq B ly1 S1 W1 mem1 (ms_mem msf) res _); [|exact RB1].
  intros x Hx. apply FRf; [unfold HEAD in *; lia | |]; intros Hv; apply (VR1 x); unfold HEAD in *; lia. }
split.
{ intros i Hi. destruct (Z.eq_dec cap 0) as [E|E]; [lia|].
  rewrite (FRm (res + i)); [| unfold HEAD in *; lia | intros Hv; apply (VR1 (res + i) Hv); unfold HEAD in *; lia].
  rewrite Z.min_l in ZB1 by lia. rewrite firstn_all2 in ZB1 by (pose proof (proj1 (OLD1n E)); lia).
  rewrite (grow_moved _ _ res kids old1 ZB1 (proj2 (OLD1n E)) i ltac:(rewrite (proj1 (OLD1n E)); lia)).
  apply (mbyte_below (w_H W) mem memC alloc_ceiling (kids + i) SB). pose proof (KLO E). unfold HEAD in *. lia. }
split; [intros H6; contradiction|].
split; [exact HPOf|].
exists (Z.max peak (live - 56 * cap + 56 * ReaderRes.cap2 cap)). split; [lia|].
replace (live + PjGrammar.held (grow_tr ty cap cap)) with (live - 56 * cap + 56 * ReaderRes.cap2 cap)
  by (rewrite RH, (proj2 (Z.eqb_neq ty 6) Hty6); lia).
replace (cnt + Z.of_nat (length (grow_tr ty cap cap))) with (cnt + 1) by (rewrite RN, (proj2 (Z.eqb_neq ty 6) Hty6); lia).
apply (grow_glob_img W1 mem1 (ms_mem msf)); [|exact G1].
intros x Hx. pose proof (fs_segs_img x Hx). apply (FRf x); [unfold FS_IMG_END in *; lia | |]; (intros Hv; apply (VNI x); [lia | exact Hx]).
Qed.

(* ================= grow_spec: the n < cap arm through the ret, the n = cap arm grow_cap_arm ================= *)
Theorem grow_holds : @grow_spec fx rc SK tfibsegs B.
Proof.
intros ly S U W regs mem md ch v ty num str kids keys n cap live peak cnt fail Dold0 HPRE HHEADS H10 HPO Hstkv
  HHDR HSL HBLK HAPART HINCL HG HQ HRS HMAX HLIVE HEV HLV.
pose proof HPRE as (HPU & HRO). pose proof HPU as (HAP & _ & _). pose proof HAP as (HAR & Hra & _).
pose proof asan_consts as (C1 & _).
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR HPO) as (Lv1 & Lv2).
pose proof HHDR as (Hrw & Hty & Hnum & Hstr & Hkids & Hkeys & Hn & Hcap).
pose proof HSL as (Hty56 & Hncap & Hcap0 & Hcapp).
assert (Hrav : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF v 56)
  by (destruct HPO as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr).
eapply (@grow_stageA fx rc SK B HSS ly S U W regs mem md ch (grow_FP v ty kids keys cap) v ty num str kids keys n cap cnt fail live peak).
- exact HPU.
- exact H10.
- lia.
- lia.
- exact (fsw_pobj_off_img B ly S W (unpoison U mem) md mem v HAR HPO).
- exact Hrav.
- exact HHDR.
- destruct Hn as [Hn0 _]. lia.
- lia.
- (* n < cap: the return *)
  intros Hlt E' ssf msf mat HSf Hrv Hpc R1 R10 HP HJ HARU SB.
  assert (Hgt : grow_tr ty n cap = []) by (unfold grow_tr; rewrite (proj2 (Z.eqb_neq n cap) ltac:(lia)); reflexivity).
  eapply SRr_mono;
    [|intros W2 c2 _ HF; exists kids, keys, cap, [], [], U; split; [left; repeat split; lia | exact HF]].
  apply (fsw_retU B grow_tbl grow_tbl_ok W E' ssf msf _ STK_grow (spZ regs) (grow_FP v ty kids keys cap) regs ly S U W
    mem md ly S U (rd_ev (grow_tr ty n cap)) _ HSf Hrv Hpc).
  + rewrite R1. exact Hra.
  + rewrite Hgt. exact HJ.
  + exact HARU.
  + exact HP.
  + intros mat'. cbv beta.
    rewrite Hgt. cbn [rd_hblocks map app length Z.of_nat PjGrammar.held]. rewrite !app_nil_r, !Z.add_0_r.
    split; [exact R10|].
    split; [apply Permutation_refl|].
    split.
    { apply (PjStruct.pj_hdr_eq tfibsegs (mrestrict (w_H W) mem)); [exact HHDR|].
      intros x Hx. apply (fsw_mrestrict_below (w_H W) mem (ms_mem msf) x SB). lia. }
    split; [exact HSL|].
    split; [exact (rd_blocks_ok_below B ly S W (unpoison U mem) md mem (ms_mem msf) Dold0 HAR SB HBLK)|].
    assert (MV : forall p k i, In (p, k) Dold0 -> 0 <= i < k ->
      mbyte tfibsegs (mrestrict (w_H W) (ms_mem msf)) (p + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (p + i)).
    { intros p k i Hin Hi. destruct (fsw_rblock_low B ly S W (unpoison U mem) md mem p k HAR (HBLK p k Hin)) as (R2 & R3).
      apply (mbyte_below (w_H W) mem (ms_mem msf) alloc_ceiling (p + i) SB). unfold HEAD in R2. lia. }
    split.
    { intros i Hi. apply (MV kids (56 * cap)); [|lia]. subst Dold0. unfold ReaderRes.kids_blk.
      destruct (Z.eqb_spec cap 0); [lia|]. left. reflexivity. }
    split.
    { intros H6 i Hi. apply (MV keys (8 * cap)); [|lia]. subst Dold0. unfold ReaderRes.kids_blk, ReaderRes.keys_blk.
      destruct (Z.eqb_spec cap 0); [lia|]. rewrite H6. cbn. right. left. reflexivity. }
    split; [exact (pobj_below B ly S W (unpoison U mem) md mem (ms_mem msf) v HAR SB HPO)|].
    exists peak. split; [lia|]. exact (fs_glob_below W mem (ms_mem msf) live peak cnt fail SB HG).
- (* n = cap: the two fuzz_realloc calls *)
  intros Heq regsC memC mat HC HJ HARU SB. subst n.
  exact (grow_cap_arm ly S U W regs mem md ch v ty num str kids keys cap live peak cnt fail regsC memC mat
    HPRE HHEADS HPO HHDR HSL HBLK HAPART HINCL HG HQ HRS (HMAX eq_refl) HLIVE HEV HLV HC HJ HARU SB).
Qed.
End H.

(* the theorem's elaborated shape, every implicit argument explicit (the sink head is the binder SK, never an inferred
   instance; the image is B's tfibsegs): image A's binder list and premise order *)
Check (@grow_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (B : asyms),
  FsShadowSyms B -> @fuzz_realloc_spec fx rc SK tfibsegs B -> @grow_spec fx rc SK tfibsegs B).
Print Assumptions grow_holds.
