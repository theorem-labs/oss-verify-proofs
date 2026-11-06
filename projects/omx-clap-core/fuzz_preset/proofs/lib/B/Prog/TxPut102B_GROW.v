(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 620 of its 675 lines of code are new or changed and 1869 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/TxPut102B_S0.v, with its module paths, module names and numbers changed; 1234 of its 1338 lines of code are new or changed and 571 lines of the source are left out. *)
(* fuzz_preset lib/B, the #102 re-walk of tx_put on image B' (asan-ubsan build): segment S_GROW (row
   TPB-GROW), from the cut TP_PC_GROW (+180) through the realloc wrapper call to the cuts TP_PC_FIT
   (+256, the call returned a block) and TP_PC_NULL (+460, the call returned NULL).
   rule 24: proves segment GROW of function tx_put (B' image) (kind: walk segment, statement frozen; reuse search:
   the internal file REWALK-102-PLAN.md section T3, a sweep of the work branches 15:1xZ with a positive control: no proved tx_put
   GROW segment on A' or B'; lib/B/Prog/tx_put.v (sha256 5a267d23cc99; internal record) txp_grow (:502) is the shape of the instruction steps
   only). The cap0 = 0 call's model law is lib/A/Prog/TxPut102A_Rnull.v's realloc_null_model_law_x_cf.
   The callee texts AREAL / AREALN are tp_seg_GROW_stmt's own premises. No keep across the realloc uses the whole-view
   keeps tpk_alo / tpk_mlo (the copy writes below the ceiling): every carry is range-restricted.
   THE RE-HIDING MOVE: the realloc of a live block (cap0 > 0) frees the old buffer, so the segment concludes SRr' segs
   RZ_cf. The run up to the call stays plain SRr and is lifted once (YGcfRhLift.ra_rh_of_SRr). The call is the rule over
   R at the cf instance with the memnorm keep, YGcallRkKeep.aj_realloc_at_x_cfR_keep, from the primed keep row AREAL at
   headroom 0: its entry room from room_live_cf, its entry headroom from tp_img's tpi_hull_adm at the run position,
   and QMm_cf at the call memory from tpi_hull_ok and the entry's RELRO fact (the tpi_relro / tpi_ro_reads_nw fields).
   The cap0 = 0 call (no free) is YGcallRxKeep.aj_realloc_null_at_x_keep, lifted at wle. Both calls' leaves carry the
   memnorm keep, which carries P across the call (srr_inv_call). The run after the call uses the runners over R at
   wle' segs RZ_cf. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07 YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecBound.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallcf YGcallRx YGcallRcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRealloc ReallocP YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallRxKeep YGcallRkKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomPosKeep PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PLB102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Refute.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import TxPutCall102 TxPutKeep102 TxPutCarry102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import TxPut102A_Rnull S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import TxPut102B_Base.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at the cut TP_PC_GROW (+180) ----
   atoms: 2 = the entry sp sp0 (sp is SOff 2 (-112)), 8 = s0 = t, 32 = the shadow offset, 33 = b0, 34 = len0,
   35 = cap0, 36 = failed (0). The shadow registers are kept in the form the inline checks match (YCbn.v match_x):
   s6 = SOff 32 0 (the check base), s10 = t >> 3, s7 / s9 / s8 = ((t + 8 / 16 / 24) >> 3) + s6; s3 / s5 / s4 = t + 8 /
   16 / 24. One region: the record's 28 accessed bytes at t (b, n, cap 8 bytes each, failed 4), writable. *)
Definition tg_Bx : sv := SOff 32 0.
Definition tg_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition tg_shx (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 c) (SLit 3)) (SOff 32 0).
Definition tg_sr : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    2%bv (SOff 2 (- TP_FRAME))) 22%bv (SOff 32 0)) 26%bv (SAlu ALU_SRL (SOff 8 0) (SLit 3)))
    23%bv (tg_shx 8)) 25%bv (tg_shx 16)) 24%bv (tg_shx 24))
    19%bv (SOff 8 8)) 21%bv (SOff 8 16)) 20%bv (SOff 8 24).
Definition tg_rec : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 28 0 28
    [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0));
     YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 4 (SOff 36 0))].
Definition tg_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 (2 ^ 47 - 2 ^ 23) 0);
           (34%nat, mkAF 0 (2 ^ 28) 0); (35%nat, mkAF 0 (2 ^ 47 - 2 ^ 23) 0); (36%nat, mkAF 0 0 0)] [] [].
Definition ss_grow : sstate := mkSS (TP_OFF + TP_PC_GROW) tg_sr [tg_rec] None tg_facts.
Definition tg_vals (b0 len0 cap0 : Z) : list Z := [SHADOW_OFF; b0; len0; cap0; 0].

(* ---- small engine facts ---- *)
Lemma tg_getr_upd_other : forall regs (r r' : bv 5) w, r' <> r -> getr (regupd regs r w) r' = getr regs r'.
Proof.
intros regs r r' w Hne. unfold getr, regupd. destruct (bv_eqb r' 0); [reflexivity|].
unfold reg_get. rewrite bvmap_get_set_other by (intros Heq; apply Hne; symmetry; exact Heq). reflexivity.
Qed.
Lemma tg_getr_upd_same : forall regs (r : bv 5) w, bv_eqb r 0 = false -> getr (regupd regs r w) r = w.
Proof. intros regs r w H. unfold getr, regupd. rewrite H. unfold reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.
Lemma tg_regs_ok_set : forall E sr regs (r : bv 5) e,
  regs_ok E sr regs -> getr regs r = sv_denot E e -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e H He r'. unfold sr_set.
destruct (bv_eqb r 0) eqn:Hr0; [exact (H r')|].
unfold sr_get. destruct (bv_eqb r' 0) eqn:Hr'0.
- specialize (H r'). unfold sr_get in H. rewrite Hr'0 in H. exact H.
- rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
  + apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact He.
  + specialize (H r'). unfold sr_get in H. rewrite Hr'0 in H. exact H.
Qed.
Lemma tg_U_add : forall E a b, U E (SAlu ALU_ADD a b) = (U E a + U E b) mod 2 ^ 64.
Proof. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. reflexivity. Qed.
Lemma tg_U_srl3 : forall E a, 0 <= U E a -> U E (SAlu ALU_SRL a (SLit 3)) = U E a / 8.
Proof.
intros E a Ha. rewrite U_SAlu, U_SLit. cbn [zalu_raw].
pose proof (U_range E a) as Hr.
assert (Z3 : zcanon 3 = 3) by (apply zcanon_id; unfold M64; lia). rewrite Z3. change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64 in *. split; [apply Z.div_pos; lia|].
apply (Z.le_lt_trans _ (U E a)); [apply Z.div_le_upper_bound; lia | lia].
Qed.
(* the shadow-address registers: ((t + c) >> 3) + the shadow base, and t >> 3 *)
Lemma tg_shreg : forall E t c, bv_unsigned (ew E 8) = t -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  0 <= t -> 0 <= c -> t + c < 2 ^ 47 ->
  sv_denot E (tg_shx c) = w64 (SHADOW_OFF + (t + c) / 8).
Proof.
intros E t c Ht H32 H0 Hc Hlt. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned.
change (bv_unsigned (sv_denot E (tg_shx c))) with (U E (tg_shx c)). unfold tg_shx.
assert (U8 : U E (SOff 8 c) = t + c) by (rewrite U_SOff, Ht; apply zcanon_id; unfold M64; lia).
assert (U32 : U E (SOff 32 0) = SHADOW_OFF).
{ rewrite U_SOff, H32, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia). apply zcanon_id. unfold M64, SHADOW_OFF; lia. }
rewrite tg_U_add, tg_U_srl3, U8, U32 by (rewrite U8; lia).
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
assert (0 <= (t + c) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite !Z.mod_small by (unfold SHADOW_OFF; lia). lia.
Qed.
Lemma tg_tshr : forall E t, bv_unsigned (ew E 8) = t -> 0 <= t < 2 ^ 47 ->
  sv_denot E (SAlu ALU_SRL (SOff 8 0) (SLit 3)) = w64 (t / 8).
Proof.
intros E t Ht Hr. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned.
change (bv_unsigned (sv_denot E (SAlu ALU_SRL (SOff 8 0) (SLit 3)))) with (U E (SAlu ALU_SRL (SOff 8 0) (SLit 3))).
assert (U8 : U E (SOff 8 0) = t) by (rewrite U_SOff, Ht, Z.add_0_r; apply zcanon_id; unfold M64; lia).
rewrite tg_U_srl3, U8 by (rewrite U8; lia).
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
assert (0 <= t / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma tg_soff : forall E (k : nat) c v, bv_unsigned (ew E k) + c = v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff k c) = w64 v.
Proof. intros E k c v Hv Hr. cbn [sv_denot]. rewrite Hv. reflexivity. Qed.

(* ---- a live block of the cf allocator ends at least 8 bytes below the allocation ceiling (the new buffer's
   `b1 + cap1 + 8 <= alloc_ceiling` at the FIT cut). The block's user range lies in its chunk (chunk_facts_cf,
   YG0scf.v: user = ck_base + ck_rz, ck_rz + req_size req <= ck_extent); primary: the chunk ends by region_base +
   kFreeArrayOffset and the region ends 2 ^ 32 below ASAN_CEIL (region_in_prim, YG0s.v); secondary: the request is at
   least 64513 (YGcfSecBound.sec_req_min), so rz_size req = 2048 and the extent has a whole redzone to spare
   (secondary_geometry, needed_primary_bounds, YG0a.v). ---- *)
Section TS. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Lemma tg_sec_rz_2048 : forall n, 0 <= n -> from_primary n = false -> rz_size n = 2048.
Proof.
intros n Hn Hf. pose proof (YGcfSecBound.sec_req_min n Hn Hf) as L.
unfold rz_size, rz_log.
repeat match goal with |- context [?a <=? ?b] => replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia) end.
reflexivity.
Qed.
Lemma tg_block_slack8_cf : forall segs B ly S Hp (W : world segs) mem md p n,
  ARcf segs B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> p + req_size n + 8 <= YM05.alloc_ceiling.
Proof.
intros segs B ly S Hp W mem md p n (M & _) Hin.
unfold ablocks in Hin. apply in_map_iff in Hin as ([q m] & Eq & Hb). cbn [fst snd] in Eq. injection Eq as <- <-.
unfold blocks in Hb. apply in_map_iff in Hb as (k & Ek & Hk). apply filter_In in Hk as [Hk _]. injection Ek as <- <-.
pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (_ & CE & _ & EU & RZ & _ & RQ & EX & ARM).
rewrite EU. unfold ASAN_CEIL in CE.
destruct (ck_beg k) as [|off|r o|c' q'] eqn:Eb; try contradiction.
- cbv zeta in ARM. destruct ARM as (Hc & _ & _ & Ee & Eba & Hx & _ & Hxs & Ha).
  pose proof (region_in_prim ly (prim_class off) LO ltac:(lia)) as (_ & _ & _ & _ & R5).
  unfold ASAN_CEIL in R5. change (2 ^ 32) with 4294967296 in R5. unfold kFreeArrayOffset in Ha. lia.
- destruct ARM as (_ & Hf & _ & Ee & _).
  pose proof (tg_sec_rz_2048 (ck_req k) ltac:(lia) Hf) as R7.
  pose proof (secondary_geometry (ck_req k) ltac:(lia) Hf) as (_ & ENS & _ & [SG _] & _).
  pose proof (needed_primary_bounds (ck_req k) ltac:(lia)) as (NP & _).
  lia.
Qed.
End TS.

(* ---- pure facts ---- *)
Lemma tgs_req_pos : forall k, 0 < k -> req_size k = k.
Proof. intros k Hk. unfold req_size. destruct (Z.eqb_spec k 0); lia. Qed.

(* a byte outside the record's 28 bytes and the old buffer is outside tx_put's footprint (req_size cap0 = cap0 for
   cap0 <> 0, so the old block's range is exactly [b0, b0 + cap0)) *)
Lemma tgs_notFP : forall t b0 cap0 a, ~ (t <= a < t + 28) -> ~ (b0 <= a < b0 + cap0) ->
  ~ inFP (prhtx_fp t b0 cap0) a.
Proof.
intros t b0 cap0 a N1 N2 (r & Hr & Hin). unfold prhtx_fp in Hr.
destruct Hr as [<- | Hr]; [cbn [fst snd] in Hin; lia|].
revert Hr. destruct (cap0 =? 0) eqn:E; intros Hr; [destruct Hr|].
unfold ablocks_fp in Hr. cbn [map] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hin.
unfold req_size in Hin. rewrite E in Hin. lia.
Qed.

(* the footprint does not open the sink: each of its ranges starts above 0 *)
Lemma tgs_no_sink : forall t b0 cap0, 0 < t -> (cap0 <> 0 -> 0 < b0) -> ~ YI16.sink_open_fp (prhtx_fp t b0 cap0).
Proof.
intros t b0 cap0 Ht Hb H. unfold YI16.sink_open_fp, YI16.in_fp in H. destruct H as (r & Hr & Hin).
unfold prhtx_fp in Hr. destruct Hr as [<- | Hr]; [cbn [fst snd] in Hin; lia|].
revert Hr. destruct (cap0 =? 0) eqn:E; intros Hr; [destruct Hr|].
unfold ablocks_fp in Hr. cbn [map] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hin.
apply Z.eqb_neq in E. specialize (Hb E). lia.
Qed.

(* the hull of a non-empty sub-window lies in the hull of the window *)
Lemma tgs_hull_sub : forall (rd : reader) x n x' n', 0 < n' -> x <= x' -> x' + n' <= x + n ->
  shadow_hull_vis rd x n -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' Hn' H1 H2 Hh s Hs. apply Hh.
assert (A1 : shadow_addr x / 8 <= shadow_addr x' / 8).
{ apply Z.div_le_mono; [lia|]. unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
assert (A2 : shadow_addr (x' + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8).
{ apply Z.div_le_mono; [lia|]. unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.

(* the hull of a window 64 bytes inside the image's bounds is shadow of image bytes *)
Lemma tgs_img_hull : forall (rd : reader) (L H : Z) x n, 0 <= x ->
  (forall a, L <= a < H -> rd (shadow_addr a) <> None) ->
  L + 64 <= x -> x + n + 64 <= H ->
  shadow_hull_vis rd x n.
Proof.
intros rd L H x n Hx0 Himg Hlo Hhi s Hs.
assert (E : shadow_addr ((s - SHADOW_OFF) * 8) = s) by (unfold shadow_addr; rewrite Z.div_mul by lia; lia).
rewrite <- E. apply Himg. clear E Himg.
unfold shadow_addr, SHADOW_OFF in *.
Z.div_mod_to_equations. lia.
Qed.

(* an 8-aligned zero-shadow range gives range_addressable on every sub-window *)
Lemma tgs_zs_ra : forall (rd : reader) q m a n, q mod 8 = 0 -> m mod 8 = 0 ->
  zero_shadow rd SHADOW_OFF q m -> q <= a -> a + n <= q + m -> range_addressable rd SHADOW_OFF a n.
Proof.
intros rd q m a n Hq Hm Hz H1 H2. apply (range_addressable_sub rd SHADOW_OFF q m); [|exact H1|exact H2].
apply zero_shadow_range; assumption.
Qed.

(* a live fake frame is 64-aligned and 64-sized (page-aligned fake stack, class 0 <= cid) *)
Lemma tgs_frame_al : forall ly cid pos, ly_F ly mod 4096 = 0 -> 0 <= cid ->
  frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0.
Proof.
intros ly cid pos HF Hc.
assert (Eu : ly_F ly = 4096 * (ly_F ly / 4096)) by (pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)); lia).
assert (E1 : frame_addr ly cid pos = (64 * (ly_F ly / 4096) + 576 + cid * 16384 + pos * 2 ^ cid) * 64).
{ unfold frame_addr, fs_frame_off, fs_frame_bytes, kFakeFramesOff, kStackSizeLog.
  rewrite !Z.shiftl_mul_pow2 by lia. rewrite Eu at 1. change (2 ^ 20) with 1048576. ring. }
assert (E2 : fs_frame_bytes cid = 2 ^ cid * 64) by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by lia; ring).
rewrite E1, E2. split; apply Z.mod_mul; lia.
Qed.

(* the shadow byte of a byte of a frame lies in the frame's shadow range *)
Lemma tgs_frame_ra : forall f F x, f mod 64 = 0 -> F mod 64 = 0 -> f <= x < f + F ->
  shadow_addr f <= shadow_of_addr SHADOW_OFF x < shadow_addr f + F / 8.
Proof. intros f F x Hf HF Hx. unfold shadow_addr, shadow_of_addr. Z.div_mod_to_equations. lia. Qed.

(* the shadow hull of a non-empty window inside a 64-aligned, 64-sized frame lies in the frame's shadow range *)
Lemma tgs_frame_hull : forall f F x n s, f mod 64 = 0 -> F mod 64 = 0 -> f <= x -> 0 < n -> x + n <= f + F ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
  shadow_addr f <= s < shadow_addr f + F / 8.
Proof. intros f F x n s Hf HF H1 Hn H2 Hs. unfold shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia. Qed.

Section TSs. Context {rc : YM05.RunCeil}.
(* a shadow byte of an app byte below the ceiling is outside the footprint: below the record (which is on the real
   stack, above 2 ^ 46) and outside the old buffer (app memory) *)
Lemma tgs_shadow_notFP : forall t b0 cap0 a,
  2 ^ 46 <= t -> (cap0 <> 0 -> in_app b0 (req_size cap0)) ->
  SHADOW_OFF <= a < SHADOW_OFF + YM05.alloc_ceiling / 8 ->
  ~ inFP (prhtx_fp t b0 cap0) a.
Proof.
intros t b0 cap0 a Ht Hb Ha (r & Hr & Hin). pose proof YM05.alloc_ceiling_value as [C _].
assert (Ha2 : a < 2 ^ 46 /\ a < 0x10007fff8000) by (unfold SHADOW_OFF in *; Z.div_mod_to_equations; lia).
unfold prhtx_fp in Hr.
destruct Hr as [<- | Hr]; [cbn [fst snd] in Hin; lia|].
revert Hr. destruct (cap0 =? 0) eqn:E; intros Hr; [destruct Hr|].
unfold ablocks_fp in Hr. cbn [map] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hin.
apply Z.eqb_neq in E. destruct (Hb E) as [_ [HL | [HH _]]];
unfold YG0f.kLowShadowBeg, YG0f.kHighMemBeg, SHADOW_OFF in *; lia.
Qed.
End TSs.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : PAImg B_prog_listing}.
#[local] Existing Instances TP_PrhImg TP_PAListing TP_RL.
#[local] Notation segs := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
#[local] Notation ARX := (ARcfx B).
(* the allocator's laws: AR_laws_ok_cf (YG0lawscf.v), at YGcallcf's bridge (as FuzzFreeB.v) *)
Let LAWS : AR_laws_x segs B ARX cf_head := AR_laws_x_xs segs B (AR_laws_ok_cf segs B).

Definition tg_E (regs : bvmap 5 word) (sp0 : Z) (xs : list Z) : env :=
  @Eimg _ B_prog_listing PA (Ereg (regupd regs 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) xs)).
Lemma tg_E_sp : forall regs sp0 xs, ew (tg_E regs sp0 xs) 2 = Z_to_bv 64 sp0.
Proof.
intros regs sp0 xs. unfold tg_E. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat _ _ 2 2%bv eq_refl). apply tg_getr_upd_same. reflexivity.
Qed.
Lemma tg_E_reg : forall regs sp0 xs (r : bv 5) k, Z.of_nat k = bv_unsigned r -> r <> 2%bv ->
  ew (tg_E regs sp0 xs) k = getr regs r.
Proof.
intros regs sp0 xs r k Hk Hne. pose proof (bv_unsigned_in_range _ r) as Hr. unfold bv_modulus in Hr.
change (2 ^ Z.of_N 5) with 32 in Hr.
unfold tg_E. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat _ _ k r Hk). apply tg_getr_upd_other. exact Hne.
Qed.
Lemma tg_E_extra : forall regs sp0 xs i, (i < 100)%nat -> ew (tg_E regs sp0 xs) (32 + i) = Z_to_bv 64 (nth i xs 0).
Proof.
intros regs sp0 xs i Hi. unfold tg_E. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite ew_Ereg_extra. change (Z_to_bv 64 0) with ((fun z => Z_to_bv 64 z) 0). rewrite map_nth. reflexivity.
Qed.
(* regs_ok at sp = SOff 2 (-112) over the env whose atom 2 is sp0 (TxPut102B_END.v's tpe_regs_ok_e) *)
Lemma tg_regs_ok_sp : forall regs sp0 xs, spZ regs = sp0 - TP_FRAME -> TP_FRAME <= sp0 < 2 ^ 64 ->
  regs_ok (tg_E regs sp0 xs) (sr_set sr_atoms 2%bv (SOff 2 (- TP_FRAME))) regs.
Proof.
intros regs sp0 xs Hsp Hsp0 r'.
pose proof (regs_ok_Eimg_Ereg (L := B_prog_listing) (PI := PA) (regupd regs 2%bv (Z_to_bv 64 sp0))
  (map (Z_to_bv 64) xs) r') as H.
fold (tg_E regs sp0 xs) in H.
unfold sr_set. change (bv_eqb 2%bv 0%bv) with false. cbv iota.
unfold getr, regupd, sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact H|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx 2%bv)) eqn:Hi.
- apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'.
  cbn [sv_denot]. rewrite tg_E_sp. unfold spZ in Hsp. unfold TP_FRAME in *.
  rewrite unsigned_lit_small by lia.
  unfold getr in Hsp. change (bv_eqb 2%bv 0%bv) with false in Hsp. cbv iota in Hsp.
  apply bv_eq. rewrite unsigned_lit_small by lia. lia.
- apply Nat.eqb_neq in Hi.
  unfold reg_get in *. rewrite bvmap_get_set_other in H by (intros Heq; apply Hi; rewrite Heq; reflexivity).
  exact H.
Qed.

(* ---- the entry of the segment: the symbolic state ss_grow holds at the cut's machine state ---- *)
Lemma tg_entry : forall (W : world segs) regs mem sp0 t b0 len0 cap0,
  spZ regs = sp0 - TP_FRAME -> 2 ^ 46 <= sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
  2 ^ 46 <= t <= 2 ^ 47 - 32 -> t mod 8 = 0 ->
  getr regs 22 = w64 SHADOW_OFF -> getr regs 8 = w64 t -> getr regs 26 = w64 (t / 8) ->
  getr regs 23 = w64 (SHADOW_OFF + (t + 8) / 8) -> getr regs 25 = w64 (SHADOW_OFF + (t + 16) / 8) ->
  getr regs 24 = w64 (SHADOW_OFF + (t + 24) / 8) ->
  getr regs 19 = w64 (t + 8) -> getr regs 21 = w64 (t + 16) -> getr regs 20 = w64 (t + 24) ->
  (forall a, t <= a < t + 28 -> writable_at segs (mrestrict (w_H W) mem) a) ->
  prhtx_rec W mem t b0 len0 cap0 0 ->
  0 <= b0 <= 2 ^ 47 - 2 ^ 23 -> 0 <= len0 <= 2 ^ 28 -> 0 <= cap0 <= 2 ^ 47 - 2 ^ 23 ->
  st_ok_pi segs VAL (tg_E regs sp0 (tg_vals b0 len0 cap0)) ss_grow
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + (TP_OFF + TP_PC_GROW))) mem (YK11.seg_rom segs))) /\
  sh_ok segs tg_Bx [] (tg_E regs sp0 (tg_vals b0 len0 cap0)) (mrestrict (w_H W) mem).
Proof.
intros W regs mem sp0 t b0 len0 cap0 Hsp Hsp0 Hal16 Ht Hta R22 R8 R26 R23 R25 R24 R19 R21 R20 Hwrit HREC
  Hb0 Hlen Hcap.
pose proof HREC as (Rb & Rl & Rc & Rf & Mb & Ml & Mc & Mf).
set (E := tg_E regs sp0 (tg_vals b0 len0 cap0)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (tg_E_extra regs sp0 _ 0 ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 b0) by exact (tg_E_extra regs sp0 _ 1 ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 len0) by exact (tg_E_extra regs sp0 _ 2 ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 cap0) by exact (tg_E_extra regs sp0 _ 3 ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 0) by exact (tg_E_extra regs sp0 _ 4 ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (subst E; rewrite tg_E_sp; apply unsigned_lit_small; lia).
assert (Ut : bv_unsigned (ew E 8) = t).
{ subst E. rewrite (tg_E_reg regs sp0 _ 8%bv 8 eq_refl) by (intros Hc; discriminate (f_equal bv_unsigned Hc)).
  rewrite R8. apply unsigned_lit_small. lia. }
assert (Dv : forall (x : nat) v, ew E x = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff x 0) = Z_to_bv 64 v).
{ intros x v Hx Hv. cbn [sv_denot]. rewrite Hx, Z.add_0_r, unsigned_lit_small by exact Hv. reflexivity. }
rewrite restrict_mkst_fx.
split.
- unfold ss_grow. apply pa_entry_st_ok_full.
  + unfold tg_sr.
    apply tg_regs_ok_set; [| rewrite R20; symmetry; apply tg_soff; [rewrite Ut; reflexivity | lia]].
    apply tg_regs_ok_set; [| rewrite R21; symmetry; apply tg_soff; [rewrite Ut; reflexivity | lia]].
    apply tg_regs_ok_set; [| rewrite R19; symmetry; apply tg_soff; [rewrite Ut; reflexivity | lia]].
    apply tg_regs_ok_set; [| rewrite R24; symmetry; apply tg_shreg; [exact Ut | exact E32 | lia | lia | lia]].
    apply tg_regs_ok_set; [| rewrite R25; symmetry; apply tg_shreg; [exact Ut | exact E32 | lia | lia | lia]].
    apply tg_regs_ok_set; [| rewrite R23; symmetry; apply tg_shreg; [exact Ut | exact E32 | lia | lia | lia]].
    apply tg_regs_ok_set; [| rewrite R26; symmetry; apply tg_tshr; [exact Ut | lia]].
    apply tg_regs_ok_set;
      [| rewrite R22; symmetry; apply tg_soff; [rewrite E32, Z.add_0_r; apply unsigned_lit_small | ]; unfold SHADOW_OFF; lia].
    subst E. apply tg_regs_ok_sp; [exact Hsp | unfold TP_FRAME; lia].
  + vm_compute. reflexivity.
  + constructor; [|constructor]. unfold region_ok, tg_rec.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Ut.
    split; [lia|]. split; [lia|].
    split; [intros q Hq; exact (Hwrit (t + q) ltac:(lia))|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    * apply (chunk_ok_val segs E _ t 0 8 (SOff 33 0) b0); [apply Dv; [exact E33 | lia] | lia | lia |].
      rewrite Z.add_0_r. exact Mb.
    * apply (chunk_ok_val segs E _ t 8 8 (SOff 34 0) len0); [apply Dv; [exact E34 | lia] | lia | lia | exact Ml].
    * apply (chunk_ok_val segs E _ t 16 8 (SOff 35 0) cap0); [apply Dv; [exact E35 | lia] | lia | lia | exact Mc].
    * apply (chunk_ok_val segs E _ t 24 4 (SOff 36 0) 0); [apply Dv; [exact E36 | lia] | lia | lia | exact Mf].
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [|split; [exact I | exact I]].
    unfold tg_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Ut, E32, E33, E34, E35, E36.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* the record's write window lies in the widened journal's window [sp0 - STK_tx_put, sp0 + dw) *)
Ltac tg_envl := repeat rewrite ew_ewset_other by lia;
  repeat match goal with H : bv_unsigned (ew _ ?k) = _ |- context [bv_unsigned (ew _ ?k)] => rewrite H end; lia.
Ltac tg_awr :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
| lazymatch goal with |- awr_ok ?Ex (YP09.mkRegion (Some ?m) _ _ _ _ _ :: _) _ ?sp0' _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ m (bv_unsigned (ew Ex m) - sp0')) end;
  [reflexivity | tg_envl | cbn [YP09.r_wlo]; tg_envl | cbn [YP09.r_whi]; tg_envl |] ].
(* the stack's shadow reads 0 at every ARcf state (AR_laws_x field alx_zshadow_byte) *)
Lemma tg_stack_ra : forall ly S Hp W mem md a len, ARX ly S Hp W mem md ->
  ly_stk_lo ly <= a -> a + len <= ly_stk_hi ly ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a len.
Proof.
intros ly S Hp W mem md a len HAR Hlo Hhi x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. exact (alx_zshadow_byte segs B ARX LAWS ly S Hp W mem md x HAR ltac:(lia)).
Qed.
Lemma tg_rd_of : forall (Wx : world segs) m, rd_of segs (mrestrict (w_H Wx) m) = aview segs (w_H Wx) m.
Proof. intros Wx m. reflexivity. Qed.
Lemma tg_U32 : forall E, ew E 32 = Z_to_bv 64 SHADOW_OFF -> U E tg_Bx = SHADOW_OFF.
Proof.
intros E H. unfold tg_Bx. rewrite U_SOff, H, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia).
apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.
Lemma tg_U8 : forall E t c, bv_unsigned (ew E 8) = t -> 0 <= t + c < 2 ^ 64 -> U E (SOff 8 c) = t + c.
Proof. intros E t c H Hr. rewrite U_SOff, H. apply zcanon_id. unfold M64. lia. Qed.
(* a run over [tg_rec] writes only the record's window [t, t + 28) *)
Lemma tg_aview_frame : forall (Wx : world segs) (Ex : env) (m m' : word -> option byte) t a,
  frame_of Ex [tg_rec] (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') -> bv_unsigned (ew Ex 8) = t ->
  0 <= a < 2 ^ 64 -> ~ (t <= a < t + 28) -> aview segs (w_H Wx) m' a = aview segs (w_H Wx) m a.
Proof.
intros Wx Ex m m' t a HF Ht Ha Hn. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros (r & [<- | []] & Hr).
cbn [tg_rec YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Ht in Hr. lia.
Qed.
Lemma tg_sll1 : forall E (j : nat) v, bv_unsigned (ew E j) = v -> 0 <= v -> 2 * v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SLL (SOff j 0) (SLit 1)) = w64 (2 * v).
Proof.
intros E j v Hv H0 H1. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned.
change (bv_unsigned (sv_denot E (SAlu ALU_SLL (SOff j 0) (SLit 1)))) with (U E (SAlu ALU_SLL (SOff j 0) (SLit 1))).
rewrite U_SAlu, U_SLit, U_SOff, Hv, Z.add_0_r. cbn [zalu_raw].
rewrite (zcanon_id v) by (unfold M64; lia). rewrite (zcanon_id 1) by (unfold M64; lia).
change (Z.land 1 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite zcanon_id by (unfold M64; lia).
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
Qed.
(* what a symbolic state whose one region is the record says of the memory: the record's four fields and its writable
   bytes *)
Lemma tg_rec_of_mem : forall (W : world segs) m E t e0 e1 e2 e3 v0 v1 v2 v3,
  mem_ok segs E (mrestrict (w_H W) m)
    [YP09.mkRegion (Some 8%nat) 0 28 0 28 [YP09.mkChunk 0 (CVal 8 e0); YP09.mkChunk 8 (CVal 8 e1);
      YP09.mkChunk 16 (CVal 8 e2); YP09.mkChunk 24 (CVal 4 e3)]] ->
  bv_unsigned (ew E 8) = t ->
  sv_denot E e0 = Z_to_bv 64 v0 -> sv_denot E e1 = Z_to_bv 64 v1 -> sv_denot E e2 = Z_to_bv 64 v2 ->
  sv_denot E e3 = Z_to_bv 64 v3 ->
  0 <= v0 < 2 ^ 64 -> 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> (v3 = 0 \/ v3 = 1) ->
  prhtx_rec W m t v0 v1 v2 v3 /\ (forall a, t <= a < t + 28 -> writable_at segs (mrestrict (w_H W) m) a).
Proof.
intros W m E t e0 e1 e2 e3 v0 v1 v2 v3 (Hwf & Hrs & Hpd) Ht H0 H1 H2 H3 R0 R1 R2 R3.
apply Forall_inv in Hrs. destruct Hrs as (_ & _ & Hw & Hcs).
cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in Hw, Hcs. rewrite Ht in Hw, Hcs.
pose proof (Forall_inv Hcs) as C0. pose proof (Forall_inv (Forall_inv_tail Hcs)) as C1.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hcs))) as C2.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail Hcs)))) as C3.
split.
- split; [exact R0|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  split; [pose proof (val_of_chunk_ok segs E _ t 0 8 e0 v0 C0 H0 ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(lia)) as V;
    rewrite Z.add_0_r in V; exact V|].
  split; [exact (val_of_chunk_ok segs E _ t 8 8 e1 v1 C1 H1 ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(lia))|].
  split; [exact (val_of_chunk_ok segs E _ t 16 8 e2 v2 C2 H2 ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(lia))|].
  exact (val_of_chunk_ok segs E _ t 24 4 e3 v3 C3 H3 ltac:(change (8 * Z.of_N 4) with 32; lia) ltac:(lia)).
- intros a Ha. replace a with (t + (a - t)) by lia. apply Hw. lia.
Qed.

(* an acall_kept with a smaller exception set gives the one with a larger set *)
Lemma tg_kept_mono : forall lyc Sc (Wc : world segs) memc (W2 : world segs) mem2 slo shi (X X' : Z -> Prop),
  acall_kept_x segs B lyc Sc Wc memc W2 mem2 slo shi X -> (forall a, X a -> X' a) ->
  acall_kept_x segs B lyc Sc Wc memc W2 mem2 slo shi X'.
Proof.
intros lyc Sc Wc memc W2 mem2 slo shi X X' (K1 & K2 & K3 & K4 & K5 & K6) HX.
split; [exact K1|]. split.
{ intros b m i Hb Hi Hn. apply (K2 b m i Hb Hi). intros Hx. exact (Hn (HX _ Hx)). }
split; [exact K3|]. split.
{ intros cid pos a Hin Hr Hn. apply (K4 cid pos a Hin Hr). intros Hx. exact (Hn (HX _ Hx)). }
split; [exact K5 | exact K6].
Qed.

(* ---- what the continuation needs from the realloc call, the same for cap0 > 0 (aj_realloc_at_x_cfR_keep) and
   cap0 = 0 (aj_realloc_null_at_x_keep): the post state's journal from the entry, aregs, a0 = res, Hp, P, the room, the
   call's keep exempting the new and the old block, and per outcome the blocks, the grow and the run position (no
   refusal arm: a NULL is `res = 0 -> False`, :511-512, by tg_refute_null) ---- *)
Definition tg_EX (D : tp_in) (res a : Z) : Prop :=
  res <> 0 /\ (res <= a < res + req_size (tp_req D) \/ (tp_cap0 D <> 0 /\ tp_b0 D <= a < tp_b0 D + req_size (tp_cap0 D))).
Definition tg_post (P : (word -> option byte) -> Prop) (D : tp_in) (Wc : world segs) (regsc : bvmap 5 word)
  (memc : word -> option byte) (ly4 : alayout) (S4 : astate) (Hp4 : list Z) (W4 : world segs) (regs4 : bvmap 5 word)
  (mem4 : word -> option byte) (md4 : Model) (res k4 : Z) : Prop :=
  (exists WS4, tp_budget D WS4 /\
     ajournal_xwR (SK := SK) segs B prh_pst ARX (wle' segs YGcfRehidePost.RZ_cf) (STK_tx_put + tp_dw D)
       (tp_sp0 D + tp_dw D) (tp_FP D)
       (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) [] ly4 S4 Hp4 W4 mem4 md4 k4 WS4) /\
  aregs_preserved regsc regs4 /\ getr regs4 10 = w64 res /\ Hp4 = tp_Hp D /\ P mem4 /\ room_live_cf S4 /\
  acall_kept_x segs B (tp_ly D) (tp_S D) Wc memc W4 mem4 (spZ regsc - ASTACK) (spZ regsc) (tg_EX D res) /\
  (* The batch kit's text has no live refused path (its refused arm is DEAD): the realloc's NULL is refuted at the call (tg_refute_null) *)
  (res = 0 -> False) /\
  (res <> 0 -> 4096 <= res /\ res mod 16 = 0 /\
     prhtx_grow B (tp_ly D) (tp_S D) ly4 S4 (tp_b0 D) (tp_cap0 D) res (tp_req D) /\
     blocks_bytes S4 <= blocks_bytes (tp_S D) + tp_req D - tp_cap0 D /\
     In (res, tp_req D) (ablocks B ly4 S4) /\
     (exists l, ablocks B ly4 S4 = l ++ [(res, tp_req D)] /\
        forall bb, In bb (ablocks B (tp_ly D) (tp_S D)) -> bb <> (tp_b0 D, tp_cap0 D) -> In bb l) /\
     (forall i, 0 <= i < tp_len0 D -> aview segs (w_H W4) mem4 (res + i) = aview segs (w_H Wc) memc (tp_b0 D + i)) /\
     tp_pos_grow D S4 0).

Lemma tg_beq : forall E (j : nat) v, ew E j = w64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff j 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E j v H Hv. cbn [sv_denot]. rewrite H, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia.
cbn [branch_taken]. unfold c_eq, bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

(* ---- the carries of the cuts' predicates across the call, from range-restricted keeps (never the whole view) ---- *)
(* the record of a symbolic state whose one region is the record, chunks in any order *)
Lemma tg_rec_of_mem2 : forall (W : world segs) m E t cs e0 e1 e2 e3 v0 v1 v2 v3,
  mem_ok segs E (mrestrict (w_H W) m) [YP09.mkRegion (Some 8%nat) 0 28 0 28 cs] ->
  In (YP09.mkChunk 0 (CVal 8 e0)) cs -> In (YP09.mkChunk 8 (CVal 8 e1)) cs ->
  In (YP09.mkChunk 16 (CVal 8 e2)) cs -> In (YP09.mkChunk 24 (CVal 4 e3)) cs ->
  bv_unsigned (ew E 8) = t ->
  sv_denot E e0 = Z_to_bv 64 v0 -> sv_denot E e1 = Z_to_bv 64 v1 -> sv_denot E e2 = Z_to_bv 64 v2 ->
  sv_denot E e3 = Z_to_bv 64 v3 ->
  0 <= v0 < 2 ^ 64 -> 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> (v3 = 0 \/ v3 = 1) ->
  prhtx_rec W m t v0 v1 v2 v3 /\ (forall a, t <= a < t + 28 -> writable_at segs (mrestrict (w_H W) m) a).
Proof.
intros W m E t cs e0 e1 e2 e3 v0 v1 v2 v3 (Hwf & Hrs & Hpd) I0 I1 I2 I3 Ht H0 H1 H2 H3 R0 R1 R2 R3.
apply Forall_inv in Hrs. destruct Hrs as (_ & _ & Hw & Hcs).
cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in Hw, Hcs. rewrite Ht in Hw, Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ I0) as C0. pose proof (proj1 (Forall_forall _ _) Hcs _ I1) as C1.
pose proof (proj1 (Forall_forall _ _) Hcs _ I2) as C2. pose proof (proj1 (Forall_forall _ _) Hcs _ I3) as C3.
split.
- split; [exact R0|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  split; [pose proof (val_of_chunk_ok segs E _ t 0 8 e0 v0 C0 H0 ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(lia)) as V;
    rewrite Z.add_0_r in V; exact V|].
  split; [exact (val_of_chunk_ok segs E _ t 8 8 e1 v1 C1 H1 ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(lia))|].
  split; [exact (val_of_chunk_ok segs E _ t 16 8 e2 v2 C2 H2 ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(lia))|].
  exact (val_of_chunk_ok segs E _ t 24 4 e3 v3 C3 H3 ltac:(change (8 * Z.of_N 4) with 32; lia) ltac:(lia)).
- intros a Ha. replace a with (t + (a - t)) by lia. apply Hw. lia.
Qed.
(* t->cap's new value: (n << 1) + 2 + (len0 << 1) *)
Lemma tg_capexpr : forall E len0 n, bv_unsigned (ew E 9) = n -> bv_unsigned (ew E 34) = len0 ->
  0 <= n -> 0 <= len0 -> len0 + n + 1 <= 2 ^ 28 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 9 0) (SLit 1)) (SLit 2)) (SAlu ALU_SLL (SOff 34 0) (SLit 1)))
  = Z_to_bv 64 (2 * (len0 + n + 1)).
Proof.
intros E len0 n Hn Hl H0 H1 H2. apply bv_eq. rewrite Z_to_bv_unsigned.
change (bv_unsigned (sv_denot E ?x)) with (U E x).
rewrite !tg_U_add, !U_SAlu, !U_SLit, !U_SOff, Hn, Hl, !Z.add_0_r. cbn [zalu_raw].
rewrite (zcanon_id n), (zcanon_id len0), (zcanon_id 1), (zcanon_id 2) by (unfold M64; lia).
change (Z.land 1 63) with 1. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite !zcanon_id by (unfold M64; lia).
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small (n * 2 + 2) (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* tp_K over a world relation R at a state reached from the entry: the widened journal at R for every byte but the
   caller window, which the walk keeps itself (outside FP) *)
Lemma tg_K_of_journal : forall (R : world segs -> world segs -> Prop) D ly2 S2 Hp2 W2 mem2 md2 k2 {WS : list (list Z)},
  ajournal_xwR (SK := SK) segs B prh_pst ARX R (STK_tx_put + tp_dw D) (tp_sp0 D + tp_dw D) (tp_FP D)
    (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) [] ly2 S2 Hp2 W2 mem2 md2 k2 WS ->
  (forall a, tp_sp0 D <= a < tp_sp0 D + tp_dw D -> ~ inFP (tp_FP D) a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H (tp_W D)) (tp_mem D) a) ->
  tp_KR B SK R D ly2 S2 W2 mem2 md2.
Proof.
intros R D ly2 S2 Hp2 W2 mem2 md2 k2 WS
  (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT) Hwin.
unfold tp_KR, tp_OR.
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|]. split; [exact Hio|].
split; [rewrite Hfrs; reflexivity|].
split.
{ intros a Ha Hw Hq. destruct (Z_lt_ge_dec a (tp_sp0 D)) as [Hlt|Hge].
  - apply F1; [exact Ha | lia].
  - destruct (Z_lt_ge_dec a (tp_sp0 D + tp_dw D)) as [Hlt2|Hge2].
    + apply Hwin; [lia | exact Hq].
    + apply F1; [exact Ha | lia]. }
split; [intros p m i H1 H2 Hi Hf _; exact (F2 p m i H1 H2 Hi Hf)|].
split; [exact Hgone|].
split; [intros a Hi Hn He Hp Hs _; exact (F3 a Hi Hn He Hp Hs)|].
split; [intros cid pos a Hin Hr Hf _; exact (F4 cid pos a Hin Hr Hf)|].
intros a Hx He _. exact (F5 a Hx He).
Qed.
(* val_mem through the restricted memories, from a view equality on its bytes *)
Lemma tg_val_keep : forall (W W' : world segs) mem mem' a n v,
  val_mem segs (mrestrict (w_H W) mem) a n v ->
  (forall k, (k < n)%nat -> aview segs (w_H W') mem' (a + Z.of_nat k) = aview segs (w_H W) mem (a + Z.of_nat k)) ->
  val_mem segs (mrestrict (w_H W') mem') a n v.
Proof.
intros W W' mem mem' a n v Hv Hk. apply (prh_val_mem_keep _ _ _ _ _ Hv). intros k Hkn. apply prh_mbyte_of_aview. exact (Hk k Hkn).
Qed.
Lemma tg_saved_keep : forall D (W W' : world segs) mem mem',
  tp_saved D W mem -> (forall a, tp_sp0 D - 104 <= a < tp_sp0 D -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  tp_saved D W' mem'.
Proof.
intros D W W' mem mem' (V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27) Hk.
unfold tp_saved.
repeat split; (eapply tg_val_keep; [eassumption | intros kk Hkk; apply Hk; lia]).
Qed.
Lemma tg_rod_keep : forall (W W' : world segs) mem mem',
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W) mem) ->
  (forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W') mem').
Proof.
intros W W' mem mem' Hro Hk. unfold PresetRodata.arodata_okP in *. intros a Ha Ho He.
assert (Hi : in_img segs a).
{ destruct Ha as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hr)]. }
rewrite (Hk a Hi Ho He). exact (Hro a Ha Ho He).
Qed.
Lemma tg_own_keep : forall (W W' : world segs) mem mem' own,
  prh_own W mem own -> (forall a, Exists (in_zr a) prh_pst -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  prh_own W' mem' own.
Proof.
intros W W' mem mem' own [Hv Ho] Hk. split; [|exact Ho].
apply (tg_val_keep W W' mem mem' _ _ _ Hv). intros kk Hkk. apply Hk.
unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma tg_rd32_keep : forall (rd rd' : reader) a v, rd32 rd a v -> (forall k, 0 <= k < 4 -> rd' (a + k) = rd (a + k)) ->
  rd32 rd' a v.
Proof. intros rd rd' a v H Hk k Hk4. rewrite Hk by lia. exact (H k Hk4). Qed.
Lemma tg_mbyte_of_aview2 : forall (Hh Hh' : word -> bool) (m m' : word -> option byte) a a',
  aview segs Hh' m' a' = aview segs Hh m a -> mbyte segs (mrestrict Hh' m') a' = mbyte segs (mrestrict Hh m) a.
Proof.
intros Hh Hh' m m' a a' E. unfold aview in E.
destruct (mbyte segs (mrestrict Hh' m') a') as [b1|] eqn:E1, (mbyte segs (mrestrict Hh m) a) as [b2|] eqn:E2;
  cbn [option_map] in E; try discriminate; [|reflexivity].
injection E as Eb. f_equal. apply bv_eq. exact Eb.
Qed.
(* bytes_at at a shifted address, from a view equality that shifts *)
Lemma tg_bytes_shift : forall (W W' : world segs) mem mem' p p' l,
  bytes_at W mem p l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> aview segs (w_H W') mem' (p' + i) = aview segs (w_H W) mem (p + i)) ->
  bytes_at W' mem' p' l.
Proof.
intros W W' mem mem' p p' l Hb Hk. unfold bytes_at, garr8 in *. intros j Hj.
destruct (Hb j Hj) as [Hv Hr]. split; [|exact Hr].
unfold val_mem in *. intros k Hk1. assert (k = 0%nat) by lia. subst k.
specialize (Hv 0%nat Hk1). cbn [Z.of_nat] in Hv |- *. rewrite !Z.add_0_r in Hv |- *.
rewrite <- Hv. apply tg_mbyte_of_aview2. apply Hk. lia.
Qed.
(* a block_shadow gives range_addressable of every sub-window *)
Lemma tg_ra_of_bs : forall (rd : reader) p n x m, block_shadow rd SHADOW_OFF p n -> p <= x -> x + m <= p + n ->
  range_addressable rd SHADOW_OFF x m.
Proof.
intros rd p n x m (Hal & Hn & Hs) Hx Hxm y Hy. unfold shadow_of_addr.
pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.div_mod y 8 ltac:(lia)) as Dy.
pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as My. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn.
pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Mn.
assert (Ei : SHADOW_OFF + y / 8 = SHADOW_OFF + p / 8 + (y / 8 - p / 8)) by lia.
rewrite Ei. assert (Hi : 0 <= y / 8 - p / 8 < (n + 7) / 8).
{ split; [apply Zle_minus_le_0; apply Z.div_le_mono; lia|].
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia. }
change (SHADOW_OFF + p / 8) with (shadow_of_addr SHADOW_OFF p). rewrite (Hs _ Hi). eexists. split; [reflexivity|].
destruct (Z.ltb_spec (y / 8 - p / 8) (n / 8)); [left; reflexivity | right]. lia.
Qed.
(* the shadow hull of a sub-window lies in the window's *)
Lemma tg_hull_sub : forall (rd : reader) p n x m, shadow_hull_vis rd p n -> p <= x -> 0 < m -> x + m <= p + n ->
  shadow_hull_vis rd x m.
Proof.
intros rd p n x m H Hx Hm Hxm s Hs. apply H. unfold shadow_addr in *.
split.
- apply (Z.le_trans _ ((SHADOW_OFF + x / 8) / 8 * 8)); [|lia].
  apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
- apply (Z.lt_le_trans _ ((SHADOW_OFF + (x + m - 1) / 8) / 8 * 8 + 8)); [lia|].
  apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
  apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
Qed.

(* no harness head lies in a live block whose base is no head *)
Lemma tg_no_head : forall ly S Hp W mem md Lam peak cnt fail ran most own p m,
  ARX ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (p, m) (ablocks B ly S) ->
  (forall a k, In (a, k) Lam -> a - cf_head <> p) -> forall h, In h Hp -> ~ (p <= h < p + req_size m).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own p m HAR HL Hin Hne h Hh Hr.
pose proof (Permutation_in _ (prh_ledger_heads B ly S Hp W mem Lam peak cnt fail ran most own HL) Hh) as Hm.
apply in_map_iff in Hm as ([a k] & Ea & Hak). cbn [fst] in Ea. subst h.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL Hak) as (Hk0 & Hab & _).
pose proof cf_head_nonneg as Hh0.
assert (Hd : (a - cf_head, k + cf_head) <> (p, m)) by (intros E; injection E as E1 _; exact (Hne a k Hak E1)).
pose proof (sep_blocks_x segs B ARX LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hin Hd) as Z.
unfold zdisjoint in Z. cbn [fst snd] in Z.
assert (1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
lia.
Qed.
(* a block of the list before the last element is disjoint from the last one *)
Lemma tg_new_disj : forall ly S Hp W mem md l x bb,
  ARX ly S Hp W mem md -> ablocks B ly S = l ++ [x] -> In bb l ->
  zdisjoint (fst bb, req_size (snd bb)) (fst x, req_size (snd x)).
Proof.
intros ly S Hp W mem md l [xp xn] bb HAR El Hbb.
assert (Hx : In (xp, xn) (ablocks B ly S)) by (rewrite El; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks segs B ARX LAWS _ _ _ _ _ _ _ _ HAR Hx) as (_ & _ & _ & _ & _ & Hpw).
rewrite El, map_app in Hpw. cbn [map fst snd] in Hpw |- *.
exact (pairwise_In _ _ _ _ _ _ eq_refl Hpw (in_map (fun b => (fst b, req_size (snd b))) l bb Hbb) (or_introl eq_refl)).
Qed.
(* a run over a one-region state whose write window is the record writes only the record *)
Lemma tg_aview_frame_g : forall (Wx : world segs) (Ex : env) rs (m m' : word -> option byte) t a,
  frame_of Ex rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  (forall b, in_wrange Ex rs b -> t <= b < t + 28) ->
  0 <= a < 2 ^ 64 -> ~ (t <= a < t + 28) -> aview segs (w_H Wx) m' a = aview segs (w_H Wx) m a.
Proof.
intros Wx Ex rs m m' t a HF Hw Ha Hn. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros Hi. exact (Hn (Hw a Hi)).
Qed.
Ltac tg_reg HS r Q :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hx ?msx) =>
    pose proof (st_ok_pi_restrict_reg Hx Ex ssx msx r HS) as Q;
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e in Q end;
  cbn [ms_regs restrict mkst] in Q.

(* ---- helpers of the FIT cut: a register read of an atom, and the address range of a live block ---- *)
Lemma tgf_denot0 : forall E (x : nat), sv_denot E (SOff x 0) = ew E x.
Proof. intros E x. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma tgf_soffU : forall E (k : nat) c v, bv_unsigned (ew E k) = v -> 0 <= v + c < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SOff k c)) = v + c.
Proof. intros E k c v H Hr. cbn [sv_denot]. rewrite H. apply unsigned_lit_small. exact Hr. Qed.
Lemma tgf_amem_of_app : forall p m, in_app p m -> p + m <= YM05.alloc_ceiling -> amem_range p m.
Proof. intros p m Ha Hc. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). zlia. Qed.

(* a read-only byte of the image is an image byte *)
Lemma tgs_roP_img : forall a, in_roP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a -> in_img segs a.
Proof. intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; assumption | exact (pa_relro_img a Hr)]. Qed.

Lemma tg_src_end : forall (R : world segs -> world segs -> Prop) D ly4 S4 W4 mem4 md4 k4 {WS : list (list Z)},
  tp_pre B CTX0 D -> tp_img B ->
  ajournal_xwR (SK := SK) segs B prh_pst ARX R (STK_tx_put + tp_dw D) (tp_sp0 D + tp_dw D) (tp_FP D)
    (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) [] ly4 S4 (tp_Hp D) W4 mem4 md4 k4 WS ->
  (forall a k, In (a, k) (tp_Lam D) -> In (a - cf_head, k + cf_head) (ablocks B ly4 S4)) ->
  src_rd W4 mem4 (tp_s D) (tp_src D).
Proof.
intros R D ly4 S4 W4 mem4 md4 k4 WS HPRE HIMG HJ HLAM4.
destruct HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & _ & HPLACE & _ & _ & HINV & HSRC & HLEN & HKEPT & HDISJ & _ &
  HLED & _).
destruct HFPRE as [(HAR0 & _ & _ & _ & _ & HSTK & _) _].
destruct HJ as (HAR4 & _ & _ & _ & _ & _ & _ & _ & _ & HBLK & HIMGK & HFRK & _).
pose proof (tpi_head_wide _ HIMG) as HW. unfold prh_head_wide in HW.
pose proof (proj1 HAR4) as HARcf4.
(* the record lies on the real stack, above 2 ^ 46 *)
destruct HPLACE as (_ & Htlo & _).
destruct HSTK as (_ & HSTK0 & HCL & HSL & _).
assert (Ht : 2 ^ 46 <= tp_t D) by (pose proof YM05.alloc_ceiling_value as [C _]; lia).
(* the old buffer, when there is one: a live block at the entry, above 4096 *)
assert (HB0 : tp_cap0 D <> 0 -> In (tp_b0 D, tp_cap0 D) (ablocks B (tp_ly D) (tp_S D)) /\ 4096 <= tp_b0 D).
{ intros Hc. destruct HINV as [_ [(Hc0 & _) | (_ & _ & Hin & _ & H4 & _)]]; [lia | split; assumption]. }
assert (HSP : ~ YI16.sink_open_fp (tp_FP D)).
{ apply tgs_no_sink; [lia | intros Hc; destruct (HB0 Hc); lia]. }
assert (HFPno : forall a, tp_s D <= a < tp_s D + tp_n D -> ~ inFP (tp_FP D) a).
{ intros a Ha. destruct (HDISJ a Ha) as [N1 N2]. exact (tgs_notFP _ _ _ a N1 N2). }
(* the journal's image clause, at a read-only, not owned, not errno byte *)
assert (HIK : forall a, in_roP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a ->
  ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview segs (w_H W4) mem4 a = aview segs (w_H (tp_W D)) (tp_mem D) a).
{ intros a Hr Ho He. apply HIMGK; [exact (tgs_roP_img a Hr) | exact Ho | exact He | |].
  - intros Hp. exact (tpi_pst_rw _ HIMG a Hp Hr).
  - intros Hs. exfalso. exact (HSP Hs). }
(* the image's zero-shadow ranges at the end state: 8-aligned (asyms_ok) and zero (alx_zshadow) *)
assert (HZS : forall q m, In (q, m) (as_zero_shadow B) ->
  q mod 8 = 0 /\ m mod 8 = 0 /\ zero_shadow (aview segs (w_H W4) mem4) SHADOW_OFF q m).
{ intros q m Hqm.
  pose proof (aso_zshadow _ (amc_syms _ _ _ _ _ (proj1 HARcf4))) as HZ. rewrite Forall_forall in HZ.
  destruct (HZ (q, m) Hqm) as (_ & _ & Hq & Hm & _). cbn [fst snd] in Hq, Hm.
  split; [exact Hq|]. split; [exact Hm|].
  exact (alx_zshadow _ _ _ LAWS ly4 S4 (tp_Hp D) W4 mem4 md4 (q, m) HAR4 (or_intror Hqm)). }
(* the hull of a window 64 bytes inside the image, at the end state *)
assert (HIH : forall x n, 0 <= x -> @pa_lo _ B_prog_listing PA + 64 <= x -> x + n + 64 <= @pa_hi _ B_prog_listing PA ->
  shadow_hull_vis (aview segs (w_H W4) mem4) x n).
{ intros x n H0 H1 H2. apply (tgs_img_hull _ (@pa_lo _ B_prog_listing PA) (@pa_hi _ B_prog_listing PA));
    [exact H0| |exact H1|exact H2].
  intros a Ha. destruct (tpi_img_bounds _ HIMG) as [El Eh]. rewrite El, Eh in Ha.
  exact (tpi_img_shvis _ HIMG ly4 S4 (tp_Hp D) W4 mem4 md4 a HARcf4 Ha). }
unfold src_rd in HSRC |- *. rewrite HLEN in HSRC |- *.
destruct HSRC as (HB & H4096 & HCE & HAM & HRA & HHU).
assert (KEY : (forall a, tp_s D <= a < tp_s D + tp_n D ->
    aview segs (w_H W4) mem4 a = aview segs (w_H (tp_W D)) (tp_mem D) a) /\
  range_addressable (aview segs (w_H W4) mem4) SHADOW_OFF (tp_s D) (tp_n D) /\
  (0 < tp_n D -> shadow_hull_vis (aview segs (w_H W4) mem4) (tp_s D) (tp_n D))).
{ destruct HKEPT as [[(b & m & HbL & Hb1 & Hb2) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]] |
    (cid & pos & Hfin & Hfr)].
  - (* a harness block of Lam *)
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ b m _ _ HLED HbL) as (Hm0 & HE & HHp & _).
    pose proof (HLAM4 b m HbL) as HE4.
    assert (HR : req_size (m + cf_head) = m + cf_head) by (apply tgs_req_pos; lia).
    destruct (alx_hshadow _ _ _ LAWS ly4 S4 (tp_Hp D) W4 mem4 md4 (b - cf_head) (m + cf_head) HAR4 HE4 HHp)
      as [BS HU].
    rewrite HR in BS, HU. replace (b - cf_head + cf_head) with b in BS, HU by lia.
    replace (m + cf_head - cf_head) with m in BS, HU by lia.
    split; [|split].
    + intros a Ha. pose proof (HBLK (b - cf_head) (m + cf_head) (a - (b - cf_head)) HE HE4) as K.
      replace (b - cf_head + (a - (b - cf_head))) with a in K by lia.
      apply K; [rewrite HR; lia | exact (HFPno a Ha)].
    + apply (block_shadow_range _ _ _ _ _ _ BS); lia.
    + intros Hn. apply (tgs_hull_sub _ b m); [lia | lia | lia | apply HU; lia].
  - (* a registered read-only global *)
    split; [|split].
    + intros a Ha. destruct (Hro a Ha) as (Hr & Ho & He). exact (HIK a Hr Ho He).
    + destruct Hzs as (q & m & Hqm & Hq & Hm). destruct (HZS q m Hqm) as (Hq8 & Hm8 & Hz).
      exact (tgs_zs_ra _ q m _ _ Hq8 Hm8 Hz Hq Hm).
    + intros _. exact (HIH (tp_s D) (tp_n D) ltac:(lia) Hlo Hhi).
  - (* an image string under route (a) *)
    split; [|split].
    + intros a Ha. destruct (Hro a Ha) as (Hr & Ho & He & _). exact (HIK a Hr Ho He).
    + intros x Hx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
      destruct (Hro x Hx) as (_ & _ & _ & [Hz | (v & Hv & Hvr)]).
      * destruct Hz as (q & m & Hqm & Hq & Hm). destruct (HZS q m Hqm) as (Hq8 & Hm8 & Hzz).
        exact (tgs_zs_ra _ q m _ _ Hq8 Hm8 Hzz Hq Hm x ltac:(lia)).
      * pose proof (alx_const_cells _ _ _ LAWS ly4 S4 (tp_Hp D) W4 mem4 md4 HAR4) as HC.
        rewrite Forall_forall in HC. specialize (HC _ (Hv ly4)).
        unfold YG0f.cell_holds, YG0f.z1, YG0f.c1 in HC. cbn [c_at c_w c_val aeval] in HC.
        specialize (HC 0%nat ltac:(lia)). rewrite Z.add_0_r in HC.
        assert (Hv8 : 0 <= v < 8) by lia.
        assert (LB : YG0f.le_byte v 1 0 = v).
        { unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
          rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
          rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia. }
        rewrite LB in HC. exists v. split; [exact HC | unfold saddr_ok; lia].
    + intros _. exact (HIH (tp_s D) (tp_n D) ltac:(lia) Hlo Hhi).
  - (* a fake frame of the entry state *)
    unfold in_zr, frame_rng in Hfr. cbn [fst snd] in Hfr.
    pose proof (proj1 (Forall_forall _ _) (proj2 (alx_sep _ _ _ LAWS _ _ _ _ _ _ HAR0)) (cid, pos) Hfin) as Hsep.
    cbn [fst snd] in Hsep.
    pose proof (proj1 (Forall_forall _ _)
      (wfs_live _ (wfc_fakestack _ _ _ _ _ (amc_wf _ _ _ _ _ (proj1 (proj1 HAR0))))) (cid, pos) Hfin) as Hwf.
    cbn [fst snd] in Hwf.
    pose proof (lo_F_al _ (alx_layout_ok _ _ _ LAWS _ _ _ _ _ _ HAR0)) as HFal. unfold page_aligned in HFal.
    destruct (tgs_frame_al (tp_ly D) cid pos HFal ltac:(lia)) as [Hf64 HF64].
    assert (SHK : forall a, shadow_addr (frame_addr (tp_ly D) cid pos) <= a <
        shadow_addr (frame_addr (tp_ly D) cid pos) + fs_frame_bytes cid / 8 ->
      aview segs (w_H W4) mem4 a = aview segs (w_H (tp_W D)) (tp_mem D) a).
    { intros a Ha. apply (HFRK cid pos a Hfin); [right; unfold in_zr; cbn [fst snd]; exact Ha|].
      apply tgs_shadow_notFP; [exact Ht | |].
      - intros Hc. destruct (HB0 Hc) as [Hin _].
        destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR0 Hin) as (_ & _ & _ & Happ & _). exact Happ.
      - unfold shadow_addr in Ha. Z.div_mod_to_equations. lia. }
    split; [|split].
    + intros a Ha. apply (HFRK cid pos a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; exact (Hfr a Ha) |
        exact (HFPno a Ha)].
    + apply (tpk_ra_keep (aview segs (w_H (tp_W D)) (tp_mem D))); [|exact HRA].
      intros x Hx. apply SHK. exact (tgs_frame_ra _ _ x Hf64 HF64 (Hfr x Hx)).
    + intros Hn. apply (tpk_hull_keep (aview segs (w_H (tp_W D)) (tp_mem D))); [|exact (HHU Hn)].
      intros s Hs. apply SHK.
      pose proof (Hfr (tp_s D) ltac:(lia)) as Hlo. pose proof (Hfr (tp_s D + tp_n D - 1) ltac:(lia)) as Hhi.
      exact (tgs_frame_hull _ _ (tp_s D) (tp_n D) s Hf64 HF64 ltac:(lia) Hn ltac:(lia) Hs). }
destruct KEY as (KB & KS & KH).
refine (conj _ (conj H4096 (conj HCE (conj HAM (conj KS KH))))).
eapply tpk_bytes_at_rng; [|exact HB]. intros a Ha. apply KB. lia.
Qed.

(* the old buffer's facts at a later allocator state with the same blocks (the NULL cut): its bytes by the given keep,
   its presence (alx_blocks) and its shadow and hull (alx_shadow; the block holds no hidden head, tg_no_head) from the
   allocator laws at the later state *)
Lemma tgn_inv_keep : forall Lam ly S Hp (W : world segs) mem md peak cnt fail ran most own ly' S' (W' : world segs)
  mem' md' b len cap txt,
  ARX ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhtx_inv B Lam ly S W mem b len cap txt ->
  ARX ly' S' Hp W' mem' md' -> ablocks B ly' S' = ablocks B ly S ->
  (forall i, 0 <= i < cap -> aview segs (w_H W') mem' (b + i) = aview segs (w_H W) mem (b + i)) ->
  prhtx_inv B Lam ly' S' W' mem' b len cap txt.
Proof.
intros Lam ly S Hp W mem md peak cnt fail ran most own ly' S' W' mem' md' b len cap txt HAR HL (Hl & Hc) HAR' Eab Hk.
split; [exact Hl|].
destruct Hc as [Hz | (Hcap & Hlt & Hin & Hby & H4 & Hce & Ham & Hwr & Hra & Hhu & Hlam)]; [left; exact Hz | right].
assert (Hreq : req_size cap = cap) by (apply tgs_req_pos; exact Hcap).
assert (Hin' : In (b, cap) (ablocks B ly' S')) by (rewrite Eab; exact Hin).
pose proof (tg_no_head ly S Hp W mem md Lam peak cnt fail ran most own b cap HAR HL Hin Hlam) as Hhp.
destruct (alx_blocks segs B ARX LAWS _ _ _ _ _ _ _ _ HAR' Hin') as (_ & _ & _ & _ & Hpres & _).
destruct (alx_shadow segs B ARX LAWS _ _ _ _ _ _ _ _ HAR' Hin' Hhp) as [Hbs Hhv].
rewrite Hreq in Hpres, Hbs, Hhv.
assert (Hlen : Z.of_nat (length (txt ++ [0])) = len + 1) by (rewrite length_app; cbn [length]; lia).
split; [exact Hcap|]. split; [exact Hlt|]. split; [exact Hin'|].
split.
{ apply (tg_bytes_shift W W' mem mem' b b _ Hby). intros i Hi. rewrite Hlen in Hi. apply Hk. lia. }
split; [exact H4|]. split; [exact Hce|]. split; [exact Ham|].
split; [intros a Ha; apply (apresent_writable segs); exact (proj1 (Hpres a Ha))|].
split; [apply (block_shadow_range _ _ _ _ _ _ Hbs); lia|].
split; [exact Hhv | exact Hlam].
Qed.

(* ---- THE REFUSED REALLOC IS REFUTED (DEAD-TXPUT; the same lemma as the A' GROW's tpg_refute_null): entered
   unfailed and growing, the grow's run event is a consumer event (the batch kit's consumer window, tp_k1pre, over this call's
   one event) at the run position of the entry state, so a refusal of the raw realloc (mt_refused at the call state)
   contradicts P8 through PRH_Refute.prh_refute_tx_put ---- *)
Lemma tg_refute_null : forall D S2 n tr,
  tp_pre B CTX0 D -> tp_k1pre B D -> tp_f0 D = 0 -> tp_cap0 D < tp_need D ->
  Wf_cf (as_universe B) (tp_S D) -> mt_refused malloc_cf free_cf n tr (tp_S D) S2 -> False.
Proof.
intros D S2 n tr HPRE HK1 Hf0 Hneed HWF Href.
pose proof HPRE as (_ & _ & _ & HPOS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV & _ & _).
destruct HK1 as (_ & HCF).
pose proof (HCF Hf0) as Hc. rewrite (tp_evk_grow D Hneed) in Hc.
apply (PRH_Refute.prh_refute_tx_put (as_universe B) (tp_rp_sm D) (tp_rp_x D) (tp_rp_os D) (tp_rp_i D) (tp_cap0 D)
  (tp_len0 D + tp_n D + 1) (tp_rp_H0 D) (tp_rp_hist D) (tp_S D) (HEV Hf0 Hneed) Hc HPOS HWF).
right. exists n, tr, S2. exact Href.
Qed.
(* the grow's budget: its one wild trace, within the batch-kit post's budget (one event per grow) *)
Lemma tg_budget_grow : forall D tr, tp_cap0 D < tp_need D -> tp_budget D ([] ++ [tr]).
Proof. intros D tr Hn _. cbn [app]. unfold wbudget. rewrite (tp_evk_grow D Hn). apply wfresh_one. Qed.

(* ---- THE SEGMENT ---- *)
Lemma tp_seg_GROW_ok : tp_seg_GROW_stmt B SK CTX0.
Proof.
intros AREAL AREALN ARX_DEPOT P PLAW PCALL Q D ly3 S3 Hp3 W3 regs3 mem3 md3 k HAT HIMG KFIT HPM.
destruct HAT as (HK1 & (HPRE & HJ & HK & HKR & HSP & HSV & EHP & HROD) & (S22 & S8 & S9 & S18) & Hf0 & HGROW & Ely & ES &
  R11 & R12 & R19 & R21 & R20 & R23 & R25 & R24 & R26 & HREC & HINV & HTR & HSIDE).
subst ly3 S3 Hp3.
pose proof HPRE as (HFPRE & HUNIV & HRL & HPOS & HLIVE & H10 & H11 & H12 & HFW & HPLACE & HTRACE0 & HREC0 & HINV0 &
  HSRC0 & HSLEN & HKEPT & HDISJ & HNEED & HLED0 & HEVP & HBB & HREQ & HLEN).
destruct HFPRE as (HPRE0 & HROD0 & HSTKHI & HRAC).
pose proof HPRE0 as ([HAR0 HXS0] & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFW as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HPLACE as (Hta & Ht1 & Ht2 & Hwrit0 & Hra28).
pose proof HREC as (Rb0 & Rl0 & Rc0 & Rf0 & Mb & Ml & Mc & Mf).
pose proof HINV as (Hltxt & Hinv).
assert (FTP : @STK_tx_put TP_PrhImg = 16496) by (vm_compute; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YM05.alloc_ceiling_value rc) as Hceilv.
unfold tp_need in HGROW, HNEED, R11. unfold tp_req, tp_need in HREQ.
unfold tp_sp0 in HSP. unfold tp_recat in HREC.
unfold tp_J, tp_sp0, tp_FP in HJ. unfold tp_K, tp_OR, tp_FP, tp_sp0 in HK.
pose proof HJ as (HAR3 & Jly & Jsecs & Jwle & Jio & Jfrs & Jnev & Jk & J1 & J2 & J3 & J4 & Jgone & Jpres & Jstat & J5 & JQT & _).
set (t := tp_t D) in *. set (n := tp_n D) in *. set (b0 := tp_b0 D) in *. set (len0 := tp_len0 D) in *.
set (cap0 := tp_cap0 D) in *. set (regs := tp_regs D) in *. set (dw := tp_dw D) in *.
set (sp0 := spZ regs) in *.
assert (Hn0 : 0 <= n) by (rewrite <- HSLEN; lia).
assert (Hbc : 0 <= b0 <= 2 ^ 47 - 2 ^ 23 /\ 0 <= cap0 <= 2 ^ 47 - 2 ^ 23).
{ destruct Hinv as [(Ec & Eb & El) | (Hc0 & Hlc & Hblk & Hby & H4096 & Hceil8 & Hamr & Hw & Hra' & Hhull & Hnb)];
  lia. }
assert (Hwrit3 : forall a, t <= a < t + 28 -> writable_at segs (mrestrict (w_H W3) mem3) a).
{ intros a Ha. apply (apresent_writable segs). apply Jpres. rewrite FTP. lia. }
assert (Ht32 : t <= 2 ^ 47 - 32) by (pose proof (Z.div_mod t 8 ltac:(lia)) as Hdm; rewrite Hta in Hdm; lia).
destruct (tg_entry W3 regs3 mem3 sp0 t b0 len0 cap0 HSP ltac:(lia) Hal16 ltac:(lia) Hta S22 S8 R26 R23 R25 R24
  R19 R21 R20 Hwrit3 HREC ltac:(lia) ltac:(lia) ltac:(lia)) as [HS SHOK].
unfold tp_cfg. replace (tp_pc TP_PC_GROW) with (BASE + (TP_OFF + TP_PC_GROW)) by (unfold tp_pc; lia).
remember (tg_E regs3 sp0 (tg_vals b0 len0 cap0)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold tg_E; apply Eimg_env).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; exact (tg_E_extra regs3 sp0 _ 0 ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 b0) by (subst E; exact (tg_E_extra regs3 sp0 _ 1 ltac:(lia))).
assert (E34 : ew E 34 = Z_to_bv 64 len0) by (subst E; exact (tg_E_extra regs3 sp0 _ 2 ltac:(lia))).
assert (E35 : ew E 35 = Z_to_bv 64 cap0) by (subst E; exact (tg_E_extra regs3 sp0 _ 3 ltac:(lia))).
assert (E36 : ew E 36 = Z_to_bv 64 0) by (subst E; exact (tg_E_extra regs3 sp0 _ 4 ltac:(lia))).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (subst E; rewrite tg_E_sp; apply unsigned_lit_small; lia).
assert (Ut : bv_unsigned (ew E 8) = t).
{ subst E. rewrite (tg_E_reg regs3 sp0 _ 8%bv 8 eq_refl) by (intros Hc; discriminate (f_equal bv_unsigned Hc)).
  rewrite S8. apply unsigned_lit_small. lia. }
assert (E3 : ew E 3 = getr regs3 3)
  by (subst E; apply (tg_E_reg regs3 sp0 _ 3%bv 3 eq_refl); intros Hc; discriminate (f_equal bv_unsigned Hc)).
assert (E4 : ew E 4 = getr regs3 4)
  by (subst E; apply (tg_E_reg regs3 sp0 _ 4%bv 4 eq_refl); intros Hc; discriminate (f_equal bv_unsigned Hc)).
assert (E11 : ew E 11 = getr regs3 11)
  by (subst E; apply (tg_E_reg regs3 sp0 _ 11%bv 11 eq_refl); intros Hc; discriminate (f_equal bv_unsigned Hc)).
assert (E8 : ew E 8 = getr regs3 8)
  by (subst E; apply (tg_E_reg regs3 sp0 _ 8%bv 8 eq_refl); intros Hc; discriminate (f_equal bv_unsigned Hc)).
assert (E9 : ew E 9 = getr regs3 9)
  by (subst E; apply (tg_E_reg regs3 sp0 _ 9%bv 9 eq_refl); intros Hc; discriminate (f_equal bv_unsigned Hc)).
assert (E18 : ew E 18 = getr regs3 18)
  by (subst E; apply (tg_E_reg regs3 sp0 _ 18%bv 18 eq_refl); intros Hc; discriminate (f_equal bv_unsigned Hc)).
clear HE.
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing TP_PAListing PA B prh_pst ARX _ LAWS P PLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing TP_PAListing PA B prh_pst ARX _ LAWS P PLAW).
pose (BR := paj_branch (PI := PA)).
(* the runners and the branch over R at wle' segs RZ_cf, for the run after the call *)
pose (RUNR := @paj_run_x_invR fx rc SK B_prog_listing TP_PAListing PA B prh_pst ARX _ LAWS P PLAW
  (wle' segs YGcfRehidePost.RZ_cf) (wle'_refl segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)).
pose (RUNTOR := @paj_run_to_x_invR fx rc SK B_prog_listing TP_PAListing PA B prh_pst ARX _ LAWS P PLAW
  (wle' segs YGcfRehidePost.RZ_cf) (wle'_refl segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)).
pose (BRR := paj_branchR (PI := PA) (wle' segs YGcfRehidePost.RZ_cf)).
(* the run up to the call is plain SRr, lifted once into SRr' segs RZ_cf at its start *)
apply (YGcfRhLift.ra_rh_of_SRr segs YGcfRehidePost.RZ_cf).
(* +180 .. +200: the load check of t, a0 = t->b, a1 = 2 * a1, the call of the realloc wrapper *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM tg_Bspan.
- (* the shadow of t: the stack's zero shadow (alx_zshadow_byte) at the cut's state *)
  cbn [ms_mem mkst]. rewrite tg_rd_of. rewrite (tg_U32 E E32), (tg_U8 E t 0 Ut) by lia. rewrite Z.add_0_r.
  apply (tg_stack_ra _ _ _ _ _ _ _ _ HAR3); lia.
- tg_awr.
- (* ---- the call of the realloc wrapper (+200), at sp = sp0 - 112 = (sp0 + dw) - (112 + dw) ---- *)
  rename HS into HSc. rename HJ into HJc. rename HPM into HPMc. rename HF into HFc. rename HFr into HFrc.
  prreg HSc (10%bv : bv 5) Q10. prreg HSc (2%bv : bv 5) Q2. prreg HSc (1%bv : bv 5) Q1.
  prreg HSc (3%bv : bv 5) Q3. prreg HSc (4%bv : bv 5) Q4. prreg HSc (8%bv : bv 5) Q8.
  pose proof (st_ok_restrict_reg segs (w_H W3) _ _ ms 11%bv HSc) as Q11.
  lazymatch type of HSc with st_ok _ _ ?ssx _ =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) 11%bv) in change (sr_get (ss_regs ssx) 11%bv) with e in Q11 end.
  cbn [ms_regs restrict mkst] in Q11.
  assert (U10 : getr (ms_regs ms) 10 = w64 b0) by (rewrite Q10, E33; reflexivity).
  assert (U11 : getr (ms_regs ms) 11 = w64 (2 * (len0 + n + 1))).
  { rewrite Q11. apply tg_sll1; [| lia | lia]. rewrite ew_ewset_other by lia. rewrite E11, R11. apply unsigned_lit_small. lia. }
  assert (Usp3 : spZ (ms_regs ms) = sp0 + dw + - (TP_FRAME + dw)).
  { unfold spZ. rewrite Q2, Usp, unsigned_lit_small by (unfold TP_FRAME; lia). unfold TP_FRAME. lia. }
  assert (U3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, E3, (HKR 3%bv ltac:(cbn; tauto)); exact Hgp).
  assert (U4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, E4, (HKR 4%bv ltac:(cbn; tauto)); exact Htp).
  assert (Us0 : s0Z (ms_regs ms) = t) by (unfold s0Z; rewrite Q8; exact Ut).
  assert (HBASE : BASE = B_prog_base) by exact (tpi_base _ HIMG).
  assert (Ura : raZ (ms_regs ms) = BASE + 15312)
    by (unfold raZ; rewrite Q1; apply unsigned_lit_small; rewrite HBASE; unfold B_prog_base; lia).
  assert (Hrapi : BASE + 15312 = pi_ret_tx_realloc) by (rewrite HBASE; vm_compute; reflexivity).
  assert (Hrok : ret_ok (Z_to_bv 64 (BASE + 15312)))
    by (apply (ret_ok_codeptr_v (L := B_prog_listing) (PI := PA)); [lia | reflexivity]).
  assert (Has : ASTACK = 16384) by reflexivity.
  assert (Hmod16 : - (TP_FRAME + dw) mod 16 = 0).
  { replace (- (TP_FRAME + dw)) with ((- 7 - dw / 16) * 16) by (pose proof (Z.div_mod dw 16 ltac:(lia)); unfold TP_FRAME; lia).
    apply Z.mod_mul. lia. }
  (* the record at the call: its fields and bytes (the run wrote none of them) *)
  pose proof (st_ok_mem_ok segs _ _ _ HSc) as HMOc. cbn [ss_mem setpc restrict ms_mem] in HMOc.
  destruct (tg_rec_of_mem W3 (ms_mem ms) (ewset E 512 w) t (SOff 33 0) (SOff 34 0) (SOff 35 0) (SOff 36 0) b0 len0 cap0 0
    HMOc) as (HRECc & HWRc).
  { rewrite ew_ewset_other by lia. exact Ut. }
  { cbn [sv_denot]. rewrite ew_ewset_other, E33, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
  { cbn [sv_denot]. rewrite ew_ewset_other, E34, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
  { cbn [sv_denot]. rewrite ew_ewset_other, E35, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
  { cbn [sv_denot]. rewrite ew_ewset_other, E36, Z.add_0_r by lia. reflexivity. }
  all: try lia.
  (* the call's trace: C-TXTRACE through TxPutCall102.tp_trace_universe *)
  assert (HU0 : universe_ok (as_universe B)) by exact (universe_ok_of_ARcf segs B _ _ _ _ _ _ (proj1 HAR3)).
  destruct (tp_trace_universe B CTX0 (tp_ly D) W3 mem3 t (tp_ly D) W3 (ms_mem ms) (ms_regs ms) HU0 HTR HUNIV
    ltac:(vm_compute; reflexivity) ltac:(lia) Us0 ltac:(rewrite Ura; exact Hrapi)
    ltac:(rewrite Ura, HBASE; unfold B_prog_base; lia) ltac:(rewrite Usp3; unfold TP_FRAME; lia) eq_refl)
    as (ch & Hchc & Htrc0).
  { intros a Ha Hn. exact (tg_aview_frame W3 E mem3 (ms_mem ms) t a HFrc Ut ltac:(lia) Hn). }
  { exact (txc_present_of_rec W3 (ms_mem ms) t b0 len0 cap0 0 HRECc). }
  (* the realloc rules take the univcore admission at the call state. In the batch kit's text the call's trace is WILD
     (prhtx_trace: inU), and the text gives the room for this call's one wild trace (tp_k1pre's wild room, kr =
     tp_evk D = 1 for a grow), so the trace is admitted at the call state - the GROW cut's, tp_S D - by
     YCbqGwild.wild_room_admits, with the depot's NoDup from ARX_DEPOT (AR_laws_x's field 25 at ARcfx; the statement's
     binder, which the instance projects from the cf laws) *)
  assert (HGROWn : tp_cap0 D < tp_need D) by (unfold tp_need; exact HGROW).
  pose proof (proj1 HK1 Hf0) as Hroom. rewrite (tp_evk_grow D HGROWn) in Hroom.
  pose proof (YCbqGwild.wild_room_admits (as_universe B) [] 1 (tp_S D) _ (ARX_DEPOT _ _ _ _ _ _ HAR3) Hroom Htrc0
    (or_intror Nat.lt_0_1)) as Hadm0.
  pose proof (palc_env B (tpi_pal _ HIMG)) as HENV.
  pose (OWNLOW := ARx_owned_low_law_xs segs B (AR_laws_ok_cf segs B)).
  pose (WFL := ARx_wf_law_xs segs B).
  pose (XSL := ARx_xs_law_xs segs B).
  pose proof (tp_RQ_of_live (tp_S D) HRL JQT) as HRQ.
  rewrite (st_ok_restrict_mkst segs (w_H W3) _ _ ms HSc eq_refl). cbn [ss_pc setpc].
  assert (Hlive : blocks_bytes (tp_S D) + 2 * (len0 + n + 1) <= LIVE_MAX) by (unfold LIVE_tx in HBB; lia).
  (* the call memory's QMm_cf: the state part from room_live_cf and the hull admission (tpi_hull_ok at the run
     position), the RELRO fact from the entry's arodata_okP through the journal to the call
     (YGcallcf.arodata_ok_cf_of_journal_P at tp_img's RELRO facts) *)
  assert (Ht0 : 0 < t) by (pose proof (@YM05.alloc_ceiling_value rc) as [Cv _]; lia).
  assert (Hb0pos : cap0 <> 0 -> 0 < b0).
  { intros Hc. destruct Hinv as [(Ec & _ & _) | (_ & _ & _ & _ & H4 & _)]; lia. }
  pose proof HROD0 as HRODc. destruct (tpi_relro_bounds _ HIMG) as (ERl & ERh & ERt). rewrite ERl, ERh in HRODc.
  assert (HQMm : QMm_cf segs B (tp_S D) (ms_mem ms)).
  { destruct (tp_QM_of_live B (tp_ly D) (tp_S D) (tp_Hp D) W3 mem3 md3 (proj1 HAR3) JQT HRL
      (tpi_hull_ok _ HIMG _ _ _ _ _ _ (tp_S D) HLEN HPOS)) as (QM1 & QM2 & QM3 & QM4 & QM5 & QM6).
    refine (conj QM1 (conj QM2 (conj QM3 (conj QM4 (conj QM5 (conj QM6 _)))))).
    exact (arodata_ok_cf_of_journal_P (SK := SK) segs B prh_pst ARX _ _ _ _ _ _ (tp_Hp D) _ _ _ _ _ _ _ _ _ _ _ _ HJc
      (tpi_relro_seg _ HIMG) (tpi_errno_relro _ HIMG) ERt (tpi_ro_reads_nw _ HIMG) (tpi_relro_pst _ HIMG)
      (tgs_no_sink t b0 cap0 Ht0 Hb0pos) HRODc). }
  apply SRr_ret. cbv beta.
  eapply (SRr'_bind segs YGcfRehidePost.RZ_cf) with (P := fun W4 c4 => exists ly4 S4 Hp4 regs4 mem4 md4 res k4,
    c4 = mkCfg (mkst regs4 (Z_to_bv 64 (BASE + 15312)) mem4 (seg_rom segs)) md4 /\
    tg_post P D W3 (ms_regs ms) (ms_mem ms) ly4 S4 Hp4 W4 regs4 mem4 md4 res k4).
  { destruct Hinv as [(Ec0 & Eb0 & El0) | (Hc0 & Hlc & Hblk & Hby & H4096 & Hceil8 & Hamr & Hwb & Hrab & Hhull & Hnb)].
  + (* cap0 = 0: realloc (NULL, 2 * need), YGcallRxKeep.aj_realloc_null_at_x_keep at the model law of
       TxPut102A_Rnull.v *)
    pose (AREALNx := YGcallRxKeep.arealloc_null_realizes_x_cf_keep segs B (SIGMA AS___wrap_realloc) AREALN).
    assert (HU : universe_ok (as_universe B)) by exact (universe_ok_of_ARcf segs B _ _ _ _ _ _ (proj1 HAR3)).
    assert (U10' : getr (ms_regs ms) 10 = w64 0) by (rewrite U10, Eb0; reflexivity).
    assert (HRQ0 : qtight (tp_S D) /\ ROOM_cf_k (tp_S D) (RK_realloc + 0)) by exact HRQ.
    apply (SRr_SRr' segs YGcfRehidePost.RZ_cf). eapply SRr_mono.
    { exact (@YGcallRxKeep.aj_realloc_null_at_x_keep fx rc SK segs B prh_pst ARX (QMm_cf segs B)
        (fun s _ _ => qtight s /\ ROOM_cf_k s (RK_realloc + 0))
        malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe B)) xs_cf _ LAWS (@pa_segs_low _ _ PA) HENV OWNLOW WFL
        (realloc_null_model_law_x_cf B 0 HU) XSL (SIGMA AS___wrap_realloc) cf_pc_realloc_ra0 AREALNx
        [] W3 (ms_regs ms) (ms_mem ms) (STK_tx_put + dw) (sp0 + dw) (prhtx_fp t b0 cap0) (tp_ly D) (tp_S D) (tp_Hp D)
        (tp_W D) (tp_mem D) (tp_md D) [] (tp_ly D) (tp_S D) (tp_Hp D) _ k (2 * (len0 + n + 1))
        (- (TP_FRAME + dw)) (Z_to_bv 64 (BASE + 15312)) ch HJc U10' U11 ltac:(lia) Hlive Usp3 Hmod16
        ltac:(unfold TP_FRAME; lia) ltac:(rewrite Has, FTP; unfold TP_FRAME; lia) U3 U4 Q1 Hrok HQMm HRQ0 Hchc Hadm0). }
    intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HPR4 & Hres & Hfrs4 & HPREc & _ &
      (q & Eq & Hqiff & (trc & Hpath & Hgf) & Hleaf) & HARM).
    (* the call's own trace is WILD in the batch kit: it stays in the post journal's budget ([] ++ [trace]) *)
    assert (HMN : YAkMemnorm.memnorm segs (ms_mem ms) -> YAkMemnorm.memnorm segs mem4).
    { destruct Hleaf as (ly' & regs' & mem' & md' & Ec' & _ & _ & _ & _ & _ & _ & HMN').
      apply (f_equal (fun c => ms_mem (cfg_ms c))) in Ec'. cbn in Ec'. rewrite Ec'. exact HMN'. }
    assert (HRL4 : room_live_cf S4)
      by exact (tp_room_live_after0 B (tp_ly D) (tp_S D) (tp_Hp D) W3 (ms_regs ms) (ms_mem ms) _ ch
        (2 * (len0 + n + 1)) _ trc q S4 HRL HLIVE HPREc Hpath).
    exists ly4, S4, (tp_Hp D), regs4, mem4, md4, res, (k + (st_nev S4 - st_nev (tp_S D))).
    split; [reflexivity|].
    unfold tg_post, tp_FP, tp_sp0. rewrite Usp3.
    split; [eexists; split; [apply (tg_budget_grow D); exact HGROWn |
      exact (ajournal_xwR_mono (SK := SK) segs B prh_pst ARX (@wle segs) (wle' segs YGcfRehidePost.RZ_cf)
        (wle_wle' segs YGcfRehidePost.RZ_cf) _ _ _ _ _ (tp_Hp D) _ _ _ _ _ _ _ _ _ _ _ _ HJ4)]|].
    split; [exact HPR4|]. split; [exact Hres|]. split; [reflexivity|].
    split; [exact (PCALL _ _ HMN HPMc)|]. split; [exact HRL4|].
    destruct HARM as [(Er & Eab4 & Ebl4 & HKC & Herr & Hoom & Href) | (H4096r & Hr16 & Eab4 & HKC)].
    * (* realloc (NULL, ..) returned NULL: REFUTED (the batch kit's consumer window: tg_refute_null) *)
      exfalso. exact (tg_refute_null D S4 _ _ HPRE HK1 Hf0 HGROWn (WFL _ _ _ _ _ _ HAR3) Href).
    * (* realloc (NULL, ..) returned a block *)
      assert (Hrne : res <> 0) by lia.
      assert (Hqn : q <> PNull) by (intros Hq0; apply Hrne; apply Hqiff; exact Hq0).
      split.
      { apply (tg_kept_mono _ _ _ _ _ _ _ _ _ _ HKC). intros a Ha. split; [exact Hrne|].
        left. unfold tp_req, tp_need. exact Ha. }
      split; [intros Er; exfalso; exact (Hrne Er)|].
      intros _. split; [exact H4096r|]. split; [exact Hr16|].
      destruct (tp_grow_blocks0 B (tp_ly D) (tp_S D) (tp_ly D) (tp_S D) ly4 S4 b0 cap0 res (2 * (len0 + n + 1))
        eq_refl Ec0 ltac:(lia) Eab4) as [Hgr Hbb].
      unfold tp_req, tp_need.
      split; [exact Hgr|]. split; [exact Hbb|].
      split; [rewrite Eab4; apply in_or_app; right; left; reflexivity|].
      split; [exists (ablocks B (tp_ly D) (tp_S D)); split; [exact Eab4 | intros bb Hbb' _; exact Hbb']|].
      split; [intros i Hi; exfalso; lia|].
      unfold tp_pos_grow, tp_need. intros _ _ _. pose proof (HEVP Hf0 HGROW) as Hev.
      exact (tp_pos_after_grow0 B _ _ _ _ _ _ (tp_ly D) (tp_S D) (tp_Hp D) W3 (ms_regs ms) (ms_mem ms) _ ch cap0
        (2 * (len0 + n + 1)) _ trc q S4 HPREc Ec0 ltac:(lia) Hlive Hadm0 Hpath Hqn HPOS Hev).
  + (* cap0 > 0: realloc (b0, 2 * need), the rule over R with the keep YGcallRkKeep.aj_realloc_at_x_cfR_keep at
       headroom 0: the call frees the old buffer, so the journal after it is at wle' segs RZ_cf *)
    assert (HRQk : qtight (tp_S D) /\ ROOM_cf_k (tp_S D) (RK_realloc + 0) /\ cf_hull_adm (tp_S D) (2 * (len0 + n + 1))).
    { split; [exact (proj1 HRQ)|]. split; [exact (proj2 HRQ)|].
      pose proof (HEVP Hf0 HGROW) as Hev. rewrite (proj2 (Z.eqb_neq cap0 0) ltac:(lia)) in Hev.
      exact (tpi_hull_adm _ HIMG _ _ _ _ _ _ (tp_S D) cap0 (2 * (len0 + n + 1)) HLEN HPOS Hev). }
    pose proof (ajournal_xwR_mono (SK := SK) segs B prh_pst ARX (@wle segs) (wle' segs YGcfRehidePost.RZ_cf)
      (wle_wle' segs YGcfRehidePost.RZ_cf) _ _ _ _ _ (tp_Hp D) _ _ _ _ _ _ _ _ _ _ _ _ HJc) as HJcR.
    assert (HFP : In (b0, cap0) (ablocks B (tp_ly D) (tp_S D)) -> forall i, 0 <= i < req_size cap0 ->
      inFP (prhtx_fp t b0 cap0) (b0 + i)).
    { intros _ i Hi. unfold prhtx_fp, ablocks_fp. rewrite (proj2 (Z.eqb_neq cap0 0) ltac:(lia)). cbn [map fst snd].
      exists (b0, b0 + req_size cap0). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
    (* the freed base is not hidden (YGcallRx's premise ~ In pa Hpc, since YGcallRx.v blob 929b45781ba3): Hp is the ledger's
       Lam heads (entry ledger HLED0 at the entry relation, ARX = conj HAR0 HXS0), and no Lam base is b0's head (Hnb) *)
    assert (Hhid0 : ~ In b0 (tp_Hp D)).
    { intros Hh. apply (tg_no_head _ _ _ _ _ _ _ _ _ _ _ _ _ b0 cap0 (conj HAR0 HXS0) HLED0 Hblk Hnb b0 Hh).
      rewrite tgs_req_pos by lia. lia. }
    eapply (SRr'_mono segs YGcfRehidePost.RZ_cf).
    { exact (YGcallRkKeep.aj_realloc_at_x_cfR_keep (SK := SK) segs B prh_pst LAWS (@pa_segs_low _ _ PA) HENV OWNLOW WFL
        XSL HU0 0 (SIGMA AS___wrap_realloc) AREAL []
        W3 (ms_regs ms) (ms_mem ms) (STK_tx_put + dw) (sp0 + dw) (prhtx_fp t b0 cap0) (tp_ly D) (tp_S D) (tp_Hp D)
        (tp_W D) (tp_mem D) (tp_md D) [] (tp_ly D) (tp_S D) (tp_Hp D) _ k b0 cap0 (2 * (len0 + n + 1))
        (- (TP_FRAME + dw)) (Z_to_bv 64 (BASE + 15312)) ch HJcR Hblk Hhid0 U10 U11 ltac:(lia) Hlive Usp3 Hmod16
        ltac:(unfold TP_FRAME; lia) ltac:(rewrite Has, FTP; unfold TP_FRAME; lia) U3 U4 Q1 Hrok HQMm HRQk Hchc Hadm0
        HFP). }
    intros W4 c4 Hwle4 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & res & -> & HJ4 & HPR4 & Hres & Hfrs4 & HPREc & _ &
      (p & q & Ep & Hpin & Eq & Hqiff & (trc & Hpath & Hgf) & Hleaf) & HARM).
    (* the call's own trace is WILD in the batch kit: it stays in the post journal's budget ([] ++ [trace]) *)
    assert (HMN : YAkMemnorm.memnorm segs (ms_mem ms) -> YAkMemnorm.memnorm segs mem4).
    { destruct Hleaf as (ly' & regs' & mem' & md' & Ec' & _ & _ & _ & _ & _ & _ & HMN').
      apply (f_equal (fun c => ms_mem (cfg_ms c))) in Ec'. cbn in Ec'. rewrite Ec'. exact HMN'. }
    assert (HRL4 : room_live_cf S4)
      by exact (tp_room_live_after B (tp_ly D) (tp_S D) (tp_Hp D) W3 (ms_regs ms) (ms_mem ms) _ ch p
        (2 * (len0 + n + 1)) _ trc q S4 HRL HLIVE HPREc Hadm0 ltac:(lia) Hlive Hpath).
    exists ly4, S4, Hp4, regs4, mem4, md4, res, (k + (st_nev S4 - st_nev (tp_S D))).
    split; [reflexivity|].
    unfold tg_post, tp_FP, tp_sp0. rewrite Usp3.
    split; [eexists; split; [apply (tg_budget_grow D); exact HGROWn | exact HJ4]|].
    split; [exact HPR4|]. split; [exact Hres|].
    destruct HARM as [(Er & EHp4 & Eab4 & Ebl4 & HKC & Herr & Hoom & Href) |
                      (H4096r & Hr16 & EHp4 & (l1 & l2 & El1 & El2) & Hcopy & HKC)].
    * (* the realloc returned NULL: REFUTED (the batch kit's consumer window: tg_refute_null) *)
      exfalso. exact (tg_refute_null D S4 _ _ HPRE HK1 Hf0 HGROWn (WFL _ _ _ _ _ _ HAR3) Href).
    * (* the realloc returned a block *)
      assert (Hrne : res <> 0) by lia.
      assert (Hqn : q <> PNull) by (intros Hq0; apply Hrne; apply Hqiff; exact Hq0).
      split; [rewrite EHp4; exact (tp_hp_remove B _ _ _ _ _ _ _ _ _ _ _ _ b0 HLED0 Hnb)|].
      split; [exact (PCALL _ _ HMN HPMc)|]. split; [exact HRL4|].
      split.
      { apply (tg_kept_mono _ _ _ _ _ _ _ _ _ _ HKC). intros a [Ha | Ha]; (split; [exact Hrne|]);
          [left; unfold tp_req, tp_need; exact Ha | right; split; [lia | exact Ha]]. }
      split; [intros Er; exfalso; exact (Hrne Er)|].
      intros _. split; [exact H4096r|]. split; [exact Hr16|].
      destruct (tp_grow_blocks B (tp_ly D) (tp_S D) (tp_ly D) (tp_S D) ly4 S4 b0 cap0 res (2 * (len0 + n + 1)) l1 l2
        eq_refl ltac:(lia) ltac:(lia) El1 El2) as [Hgr Hbb].
      unfold tp_req, tp_need.
      split; [exact Hgr|]. split; [exact Hbb|].
      split; [rewrite El2; apply in_or_app; right; apply in_or_app; right; left; reflexivity|].
      split.
      { exists (l1 ++ l2). split; [rewrite El2, app_assoc; reflexivity|].
        intros bb Hbb' Hne. rewrite El1 in Hbb'. apply in_app_or in Hbb' as [Hb | [Hb | Hb]].
        - apply in_or_app. left. exact Hb.
        - exfalso. exact (Hne (eq_sym Hb)).
        - apply in_or_app. right. exact Hb. }
      split; [intros i Hi; apply Hcopy; lia|].
      unfold tp_pos_grow, tp_need. intros _ _ _. pose proof (HEVP Hf0 HGROW) as Hev.
      exact (tp_pos_after_grow B _ _ _ _ _ _ (tp_ly D) (tp_S D) (tp_Hp D) W3 (ms_regs ms) (ms_mem ms) _ ch p b0 cap0
        (2 * (len0 + n + 1)) _ trc q S4 HPREc HRL Hc0 Ep ltac:(lia) Hpin ltac:(lia) Hlive Hadm0 Hpath Hqn HPOS Hev). }
  (* ---- after the call (+204): the same continuation for both cap0 cases ---- *)
  intros W4 c4 Hwle4 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & res & k4 & -> & HPOST). unfold SRr'.
  unfold tg_post, tg_EX, tp_sp0, tp_FP, tp_req, tp_need in HPOST.
  change (tp_dw D) with dw in HPOST. change (tp_t D) with t in HPOST. change (tp_b0 D) with b0 in HPOST.
  change (tp_cap0 D) with cap0 in HPOST. change (tp_len0 D) with len0 in HPOST. change (tp_n D) with n in HPOST.
  change (spZ (tp_regs D)) with sp0 in HPOST.
  pose proof HPOST as ((WS4 & HBUD4 & HJ4w) & HPR4 & Hres & EHp4 & HPM4 & HRL4 & HKC & HNULLA & HOKA).
  subst Hp4.
  pose proof HKC as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6).
  pose proof HJ4w as (HAR4 & J4ly & J4secs & J4wle & J4io & J4frs & J4nev & J4k & J41 & J42 & J43 & J44 & J4gone &
    J4pres & J4stat & J45 & J4QT).
  rewrite Usp3 in KC1, KC5, KC6.
  (* the record across the call: above the callee's stack, kept (acall_kept's stack clause); present (the journal) *)
  jafter_call_keep_pi HSc 40%nat regs4 (mrestrict (w_H W4) mem4) HPR4 [0]%nat HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. constructor; [|constructor]. unfold region_kept.
    cbn [tg_rec YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val].
    rewrite ew_ewset_other, Ut by lia. split; intros a Ha.
    - apply prh_mbyte_of_aview. apply KC1; [lia | rewrite Has; unfold TP_FRAME; lia].
    - intros _. apply (apresent_writable segs). apply J4pres. rewrite FTP. lia. }
  rewrite <- restrict_mkst_fx in HS2.
  remember (havoc (ewset E 512 w) 40 (map (getr regs4) CLOB)) as E2 eqn:HE2 in HS2.
  assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI0 | cbv; lia]).
  assert (OLD2 : forall j, (j < 40)%nat -> ew E2 j = ew E j).
  { intros j Hj. rewrite HE2, YN3v.ew_havoc_old by exact Hj. apply ew_ewset_other. lia. }
  assert (E44 : ew E2 44 = w64 res) by (rewrite HE2; unfold havoc; cbn [ew]; exact Hres).
  clear HE2.
  assert (SHOK2 : sh_ok segs tg_Bx [] E2 (mrestrict (w_H W4) mem4)) by constructor.
  (* +204: the NULL test `beqz a0` *)
  assert (Hresr : 0 <= res < 2 ^ 64).
  { destruct (Z.eq_dec res 0) as [-> | Hne]; [lia|].
    destruct (HOKA Hne) as (H4096r & _ & _ & _ & Hin4 & _).
    destruct (alx_blocks segs B ARX LAWS _ _ _ _ _ _ _ _ HAR4 Hin4) as (_ & _ & Hc4 & _).
    unfold req_size in Hc4. destruct (Z.eqb_spec (2 * (len0 + n + 1)) 0); lia. }
  assert (Ut2 : bv_unsigned (ew E2 8) = t) by (rewrite OLD2 by lia; exact Ut).
  assert (E32' : ew E2 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD2 by lia; exact E32).
  pose proof J4ly as (_ & _ & _ & _ & _ & _ & _ & _ & Ely4top & Ely4lo & Ely4hi & _).
  (* ---- the keeps from the GROW cut to the post-call state (range-restricted; never the whole view) ---- *)
  assert (HTF : TP_FRAME = 112) by reflexivity.
  assert (KPRE : forall a, 0 <= a < 2 ^ 64 -> ~ (t <= a < t + 28) ->
    aview segs (w_H W3) (ms_mem ms) a = aview segs (w_H W3) mem3 a)
    by (intros a Ha Hn; exact (tg_aview_frame W3 E mem3 (ms_mem ms) t a HFrc Ut Ha Hn)).
  assert (Hsplo : YM05.alloc_ceiling + ASTACK + TP_FRAME <= sp0) by lia.
  assert (KHI4 : forall a, sp0 - TP_FRAME <= a < 2 ^ 64 -> ~ (t <= a < t + 28) ->
    aview segs (w_H W4) mem4 a = aview segs (w_H W3) mem3 a).
  { intros a Ha Hn. rewrite KC1 by lia. apply KPRE; [lia | exact Hn]. }
  assert (KIMG4 : forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> aview segs (w_H W4) mem4 a = aview segs (w_H W3) mem3 a).
  { intros a Hi Ho He. rewrite (KC3 a Hi Ho He). pose proof (@pa_segs_low _ _ PA a Hi) as Hl. unfold kLowMemEnd in Hl.
    apply KPRE; lia. }
  assert (KBLK4 : forall p m i, In (p, m) (ablocks B (tp_ly D) (tp_S D)) -> 0 <= i < req_size m ->
    ~ (res <> 0 /\ (res <= p + i < res + req_size (2 * (len0 + n + 1)) \/ (cap0 <> 0 /\ b0 <= p + i < b0 + req_size cap0))) ->
    aview segs (w_H W4) mem4 (p + i) = aview segs (w_H W3) mem3 (p + i)).
  { intros p m i Hb Hi Hn. rewrite (KC2 p m i Hb Hi Hn).
    destruct (alx_blocks segs B ARX LAWS _ _ _ _ _ _ _ _ HAR3 Hb) as (_ & H4096p & Hcp & _). apply KPRE; lia. }
  assert (KWIN4 : forall a, sp0 <= a < sp0 + dw -> ~ inFP (prhtx_fp t b0 cap0) a ->
    aview segs (w_H W4) mem4 a = aview segs (w_H (tp_W D)) (tp_mem D) a).
  { intros a Ha Hf.
    assert (Hnr : ~ (t <= a < t + 28))
      by (intros Hr; apply Hf; exists (t, t + 28); split; [left; reflexivity | cbn [fst snd]; lia]).
    rewrite KHI4 by lia. pose proof HK as (_ & _ & _ & _ & _ & K1 & _). apply K1; [lia | lia | exact Hf]. }
  pose proof (tpi_pst_img _ HIMG) as HPSTI.
  assert (KPST4 : forall a, Exists (in_zr a) prh_pst -> aview segs (w_H W4) mem4 a = aview segs (w_H W3) mem3 a).
  { intros a Hx. apply KIMG4; [exact (HPSTI a Hx) | exact (tpi_pst_owned _ HIMG a Hx) | exact (tpi_pst_errno _ HIMG a Hx)]. }
  pose proof HSIDE as (HLED3 & HSRC3 & _).
  pose proof (tpi_head_wide _ HIMG) as HHW. unfold prh_head_wide in HHW.
  assert (KHEAD4 : forall a kk i, In (a, kk) (tp_Lam D) -> 0 <= i < 8 ->
    ~ (res <> 0 /\ (res <= a - cf_head + i < res + req_size (2 * (len0 + n + 1)) \/
                     (cap0 <> 0 /\ b0 <= a - cf_head + i < b0 + req_size cap0))) ->
    aview segs (w_H W4) mem4 (a - cf_head + i) = aview segs (w_H W3) mem3 (a - cf_head + i)).
  { intros a kk i Hin Hi Hn.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a kk _ _ HLED3 Hin) as (Hk0 & Hab & _).
    apply (KBLK4 _ _ i Hab); [|exact Hn].
    assert (kk + cf_head <= req_size (kk + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
    lia. }
  psrr_branch_tok RUNR BRR HS2 SHOK2 tg_Bspan.
  + (* a0 = 0: REFUTED - the realloc's NULL is refuted at the call (tg_post's res = 0 -> False) *)
    rewrite (tg_beq E2 44 res E44 Hresr) in Hc. apply Z.eqb_eq in Hc. exfalso. exact (HNULLA Hc).
  + (* a0 <> 0: the grow succeeded; the store check of t, t->b := a0, the checks of t + 8 / t + 16, t->cap := 2 * need *)
    rewrite (tg_beq E2 44 res E44 Hresr) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hrne.
    (* the run reads an empty-budget journal: the post-call one, rebased at its depot; unbased after the run *)
    pose proof (ajournal_xw_rebaseR (SK := SK) segs B prh_pst ARX (wle' segs YGcfRehidePost.RZ_cf)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4w) as HJ4r.
    paj_run_to_tok_x_inv RUNTOR HS2 HJ4r SHOK2 HPM4 tg_Bspan (TP_OFF + TP_PC_FIT).
    1-3: cbn [ms_mem mkst]; rewrite tg_rd_of, (tg_U32 E2 E32'), (tg_U8 E2 t _ Ut2) by lia;
      apply (tg_stack_ra _ _ _ _ _ _ _ _ HAR4); rewrite ?Ely4lo, ?Ely4hi; lia.
    { tg_awr. }
    pose proof (ajournal_xw_unbase0R (SK := SK) segs B prh_pst ARX (wle' segs YGcfRehidePost.RZ_cf)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4r (ajxR_wild HJ4w)) as HJ4.
    rename HFr into HFrF. clear HF HG.
    pmkst HS2. unfold ss_pc.
    lazymatch goal with |- context [{| cfg_ms := mkst ?rg (Z_to_bv 64 (BASE + ?pc)) ?m _; cfg_model := ?d |}] =>
      replace (Z_to_bv 64 (BASE + pc)) with (Z_to_bv 64 (tp_pc TP_PC_FIT))
        by (f_equal; unfold tp_pc, TP_PC_FIT; rewrite TP_OFF_val; lia);
      eapply (KFIT ly4 S4 (tp_Hp D) W4 rg m d _ res (2 * (len0 + n + 1))); [| exact HPM4] end.
    (* ---- the FIT cut (+256): the run wrote only the record (t->b := res, t->cap := 2 * need); every other
       fact rides on the range-restricted keeps from the GROW cut and the allocator laws at the end state ---- *)
    tg_reg HS2 (2%bv : bv 5) QF2. tg_reg HS2 (3%bv : bv 5) QF3. tg_reg HS2 (4%bv : bv 5) QF4.
    tg_reg HS2 (8%bv : bv 5) QF8. tg_reg HS2 (9%bv : bv 5) QF9. tg_reg HS2 (18%bv : bv 5) QF18.
    tg_reg HS2 (22%bv : bv 5) QF22. tg_reg HS2 (19%bv : bv 5) QF19. tg_reg HS2 (21%bv : bv 5) QF21.
    tg_reg HS2 (23%bv : bv 5) QF23. tg_reg HS2 (25%bv : bv 5) QF25. tg_reg HS2 (26%bv : bv 5) QF26.
    lazymatch type of HS2 with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      pose proof (st_ok_mem_ok segs Ex _ msx HS2) as HMOF;
      cbn [ss_mem restrict ms_mem setpc abs_ss] in HMOF;
      lazymatch type of HMOF with mem_ok _ _ _ ?l =>
        let l' := eval vm_compute in l in change l with l' in HMOF end end.
    lazymatch type of HS2 with st_ok_pi _ _ ?Ex _ _ =>
      assert (EF40 : forall j, (j < 40)%nat -> ew Ex j = ew E j)
        by (intros j Hj; repeat rewrite ew_ewset_other by lia; apply OLD2; exact Hj);
      assert (EF44 : ew Ex 44 = w64 res) by (repeat rewrite ew_ewset_other by lia; exact E44);
      assert (UF2 : bv_unsigned (ew Ex 2) = sp0) by (rewrite EF40 by lia; exact Usp);
      assert (UtF : bv_unsigned (ew Ex 8) = t) by (rewrite EF40 by lia; exact Ut);
      assert (E32F : ew Ex 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EF40 by lia; exact E32) end.
    lazymatch type of HJ4 with ajournal_xwR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wn ?mn ?dn ?kn _ =>
      set (memF := mn) in *; set (mdF := dn) in *; set (kF := kn) in * end.
    pose proof HJ4 as (HARF & _).
    (* the run from +204 writes only the record's window [t, t + 28) *)
    assert (KEF : forall a, 0 <= a < 2 ^ 64 -> ~ (t <= a < t + 28) ->
      aview segs (w_H W4) memF a = aview segs (w_H W4) mem4 a).
    { intros a Ha Hn. apply (tg_aview_frame_g W4 _ _ mem4 memF t a HFrF); [| exact Ha | exact Hn].
      intros bb (r & Hin & Hr). vm_compute in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Ut2 in Hr. lia. }
    destruct (HOKA Hrne) as (H4096r & Hr16 & Hgrow & Hbbs & Hin4 & (l & El & Hl) & Hcopy & Hposg).
    (* the ledger's blocks are entry blocks other than the old buffer, so they are in l, apart from the new block *)
    assert (HLl : forall a kk, In (a, kk) (tp_Lam D) -> In (a - cf_head, kk + cf_head) l).
    { intros a kk Hak. destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a kk _ _ HLED3 Hak) as (Hk0 & Hab & _).
      apply Hl; [exact Hab|]. intros Hq. injection Hq as Hq1 Hq2.
      destruct Hinv as [(Ec & _ & _) | (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnb)]; [lia | exact (Hnb a kk Hak Hq1)]. }
    assert (HLAM4 : forall a kk, In (a, kk) (tp_Lam D) -> In (a - cf_head, kk + cf_head) (ablocks B ly4 S4)).
    { intros a kk Hak. rewrite El. apply in_or_app. left. exact (HLl a kk Hak). }
    assert (HHD : forall h, In h (tp_Hp D) -> ~ (res <= h < res + req_size (2 * (len0 + n + 1)))).
    { intros h Hh Hr.
      pose proof (Permutation_in _ (prh_ledger_heads B _ _ _ _ _ _ _ _ _ _ _ _ HLED3) Hh) as Hm.
      apply in_map_iff in Hm as ([a kk] & Ea & Hak). cbn [fst] in Ea. subst h.
      destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a kk _ _ HLED3 Hak) as (Hk0 & _).
      pose proof (tg_new_disj _ _ _ _ _ _ l _ _ HARF El (HLl a kk Hak)) as Zd.
      unfold zdisjoint in Zd. cbn [fst snd] in Zd.
      assert (kk + cf_head <= req_size (kk + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
      lia. }
    (* the new block at the end state: slack, range, presence, shadow (allocator laws) *)
    pose proof (tg_block_slack8_cf segs B ly4 S4 (tp_Hp D) W4 memF mdF res (2 * (len0 + n + 1)) (proj1 HARF) Hin4)
      as HSL8.
    rewrite (tgs_req_pos (2 * (len0 + n + 1))) in HSL8 by lia.
    destruct (alx_blocks segs B ARX LAWS _ _ _ _ _ _ _ _ HARF Hin4) as (_ & _ & Hce4 & Happ & Hpr4 & _).
    rewrite (tgs_req_pos (2 * (len0 + n + 1))) in Hce4, Happ, Hpr4 by lia.
    destruct (alx_shadow segs B ARX LAWS _ _ _ _ _ _ _ _ HARF Hin4 HHD) as [BSF HUF].
    rewrite (tgs_req_pos (2 * (len0 + n + 1))) in BSF, HUF by lia.
    pose proof (tgf_amem_of_app _ _ Happ Hce4) as HAMF.
    (* the source window stays apart from the new block, and stays kept *)
    pose proof (proj1 (proj2 (alx_layout segs B ARX LAWS _ _ _ _ _ _ ly4 HAR3 J4ly))) as HFA.
    assert (HFR4 : frames S4 = frames (tp_S D)) by (rewrite J4frs; reflexivity).
    assert (HSN : forall a, tp_s D <= a < tp_s D + n -> ~ (res <= a < res + 2 * (len0 + n + 1))).
    { intros a Ha Hr.
      destruct HKEPT as [[(bk & mk & HbL & Hb1 & Hb2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (cid & pos & Hfin & Hfr)].
      - destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ bk mk _ _ HLED3 HbL) as (Hk0 & _).
        pose proof (tg_new_disj _ _ _ _ _ _ l _ _ HARF El (HLl bk mk HbL)) as Zd.
        unfold zdisjoint in Zd. cbn [fst snd] in Zd. rewrite (tgs_req_pos (2 * (len0 + n + 1))) in Zd by lia.
        assert (mk + cf_head <= req_size (mk + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (mk + cf_head) 0); lia).
        lia.
      - destruct (Hro a Ha) as (Hrp & _).
        assert (Hr' : res <= a < res + req_size (2 * (len0 + n + 1))) by (rewrite tgs_req_pos by lia; lia).
        refine (proj2 (alx_client_img segs B ARX LAWS _ _ _ _ _ _ a HARF _) (tgs_roP_img a Hrp)).
        left. exists res, (2 * (len0 + n + 1)). split; [exact Hin4 | exact Hr'].
      - destruct (Hro a Ha) as (Hrp & _).
        assert (Hr' : res <= a < res + req_size (2 * (len0 + n + 1))) by (rewrite tgs_req_pos by lia; lia).
        refine (proj2 (alx_client_img segs B ARX LAWS _ _ _ _ _ _ a HARF _) (tgs_roP_img a Hrp)).
        left. exists res, (2 * (len0 + n + 1)). split; [exact Hin4 | exact Hr'].
      - unfold in_zr, frame_rng in Hfr. cbn [fst snd] in Hfr. pose proof (Hfr a Ha) as Hfa.
        destruct (alx_sep segs B ARX LAWS _ _ _ _ _ _ HARF) as [Hsep _].
        assert (Hfin4 : In (cid, pos) (frames S4)) by (rewrite HFR4; exact Hfin).
        pose proof (pairwise_In _ _ _ _ _ _ eq_refl Hsep
          (in_map (fun b => (fst b, req_size (snd b))) _ _ Hin4)
          (in_map (fun f => (frame_addr ly4 (fst f) (snd f), fs_frame_bytes (fst f))) _ _ Hfin4)) as Zd.
        unfold zdisjoint in Zd. cbn [fst snd] in Zd. rewrite HFA in Zd.
        rewrite (tgs_req_pos (2 * (len0 + n + 1))) in Zd by lia. lia. }
    assert (HKEPT4 : prhtx_kept B (tp_Lam D) ly4 S4 (tp_s D) n).
    { unfold prhtx_kept. destruct HKEPT as [Hk | (cid & pos & Hfin & Hfr)]; [left; exact Hk | right].
      exists cid, pos. split; [rewrite HFR4; exact Hfin|].
      intros a Ha. specialize (Hfr a Ha). unfold in_zr, frame_rng in Hfr |- *. cbn [fst snd] in Hfr |- *.
      rewrite HFA. exact Hfr. }
    (* the ledger, the own cell and the source window at the end state *)
    assert (KPSTF : forall a, Exists (in_zr a) prh_pst -> aview segs (w_H W4) memF a = aview segs (w_H W3) mem3 a).
    { intros a Ha. pose proof (@pa_segs_low _ _ PA a (HPSTI a Ha)) as Hlo. unfold kLowMemEnd in Hlo.
      rewrite KEF by lia. exact (KPST4 a Ha). }
    assert (HHK : forall a kk i, In (a, kk) (tp_Lam D) -> 0 <= i < 8 ->
      aview segs (w_H W4) memF (a - cf_head + i) = aview segs (w_H W3) mem3 (a - cf_head + i)).
    { intros a kk i Hak Hi.
      destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a kk _ _ HLED3 Hak) as (Hk0 & Hab & _).
      destruct (alx_blocks segs B ARX LAWS _ _ _ _ _ _ _ _ HAR3 Hab) as (_ & H4h & Hce & _).
      assert (RSk : kk + cf_head <= req_size (kk + cf_head))
        by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
      rewrite KEF by lia.
      apply (KHEAD4 a kk i Hak Hi). intros (_ & [Hnew | (Hc0 & Hold)]).
      - pose proof (tg_new_disj _ _ _ _ _ _ l _ _ HARF El (HLl a kk Hak)) as Zd.
        unfold zdisjoint in Zd. cbn [fst snd] in Zd. lia.
      - destruct Hinv as [(Ec & _ & _) | (_ & _ & Hblk & _ & _ & _ & _ & _ & _ & _ & Hnb)]; [lia|].
        assert (Hd : (a - cf_head, kk + cf_head) <> (b0, cap0))
          by (intros Hq; injection Hq as Hq1 _; exact (Hnb a kk Hak Hq1)).
        pose proof (sep_blocks_x segs B ARX LAWS _ _ _ _ _ _ _ _ _ _ HAR3 Hab Hblk Hd) as Zd.
        unfold zdisjoint in Zd. cbn [fst snd] in Zd. lia. }
    assert (HBL : forall a kk, In (a, kk) (tp_Lam D) -> In (a - cf_head, kk + cf_head) (ablocks B (tp_ly D) (tp_S D)) ->
      In (a - cf_head, kk + cf_head) (ablocks B ly4 S4)) by (intros a kk Hak _; exact (HLAM4 a kk Hak)).
    pose proof (prh_ledger_kept_aview B (tp_ly D) (tp_S D) (tp_Hp D) W3 mem3 ly4 S4 (tp_Hp D) W4 memF (tp_Lam D)
      (tp_peak D) (tp_cnt D) (tp_fail D) (tp_ran D) (tp_most D) (tp_own D) HLED3 KPSTF HHK HBL (Permutation_refl _))
      as HLEDF.
    pose proof (tg_src_end _ D ly4 S4 W4 memF mdF kF HPRE HIMG HJ4 HLAM4) as HSRCF.
    (* the text in the new buffer: the realloc's copy of the old buffer's first len0 bytes *)
    assert (HBYF : bytes_at W4 memF res (tp_txt D)).
    { destruct Hinv as [(Ec & Eb & Ln0) | (Hc0 & Hlc & Hblk & Hby & H4096 & Hceil8 & _)].
      - unfold bytes_at, garr8. intros j Hj. exfalso. lia.
      - apply (tg_bytes_shift W3 W4 mem3 memF b0 res (tp_txt D) (proj1 (proj1 (garr8_app segs _ _ _ _) Hby))).
        intros i Hi. rewrite Hltxt in Hi.
        rewrite KEF by lia. rewrite Hcopy by lia. apply KPRE; lia. }
    (* the record: t->b = res, t->n = len0, t->cap = 2 * need, failed = 0 *)
    assert (HRWF : prhtx_rec W4 memF t res len0 (2 * (len0 + n + 1)) 0 /\
      (forall a, t <= a < t + 28 -> writable_at segs (mrestrict (w_H W4) memF) a)).
    { refine (tg_rec_of_mem2 W4 memF _ t _ (SOff 44 0) (SOff 34 0)
        (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 9 0) (SLit 1)) (SLit 2)) (SAlu ALU_SLL (SOff 34 0) (SLit 1)))
        (SOff 36 0) res len0 (2 * (len0 + n + 1)) 0 HMOF _ _ _ _ UtF _ _ _ _ Hresr Rl0 _ (or_introl eq_refl)).
      - cbn [In]. right. left. reflexivity.
      - cbn [In]. right. right. left. reflexivity.
      - cbn [In]. left. reflexivity.
      - cbn [In]. right. right. right. left. reflexivity.
      - rewrite tgf_denot0. exact EF44.
      - rewrite tgf_denot0, EF40 by lia. exact E34.
      - apply tg_capexpr; [| | lia | lia | exact HNEED].
        + rewrite EF40 by lia. rewrite E9, S9. apply unsigned_lit_small. lia.
        + rewrite EF40 by lia. rewrite E34. apply unsigned_lit_small. lia.
      - rewrite tgf_denot0, EF40 by lia. exact E36.
      - lia. }
    (* ---- the cut predicate ---- *)
    unfold tp_at_FIT, tp_carryR.
    exists WS4. split; [exact HBUD4|].
    split.
    { split; [exact HPRE|]. split; [exact HJ4|].
      split.
      { apply (tg_K_of_journal (wle' segs YGcfRehidePost.RZ_cf) D ly4 S4 (tp_Hp D) W4 memF mdF kF HJ4).
        intros a Ha Hf. change (tp_sp0 D) with sp0 in Ha. change (tp_dw D) with dw in Ha.
        change (tp_FP D) with (prhtx_fp t b0 cap0) in Hf.
        assert (Hnr : ~ (t <= a < t + 28))
          by (intros Hr; apply Hf; exists (t, t + 28); split; [left; reflexivity | cbn [fst snd]; lia]).
        rewrite KEF by lia. exact (KWIN4 a Ha Hf). }
      split.
      { intros r Hr. destruct Hr as [<- | [<- | []]].
        - refine (eq_trans QF3 _). rewrite tgf_denot0, EF40 by lia.
          exact (eq_trans E3 (HKR 3%bv ltac:(cbn; tauto))).
        - refine (eq_trans QF4 _). rewrite tgf_denot0, EF40 by lia.
          exact (eq_trans E4 (HKR 4%bv ltac:(cbn; tauto))). }
      split.
      { unfold spZ. rewrite QF2. rewrite (tgf_soffU _ 2 (-112) sp0) by (first [exact UF2 | lia]).
        change (tp_sp0 D) with sp0. unfold TP_FRAME. lia. }
      split.
      { apply (tg_saved_keep D W3 W4 mem3 memF HSV). intros a Ha. change (tp_sp0 D) with sp0 in Ha.
        rewrite KEF by lia. apply KHI4; [rewrite HTF; lia | lia]. }
      split; [reflexivity|].
      apply (tg_rod_keep W3 W4 mem3 memF HROD). intros a Hi Ho He.
      pose proof (@pa_segs_low _ _ PA a Hi) as Hlo. unfold kLowMemEnd in Hlo.
      rewrite KEF by lia. exact (KIMG4 a Hi Ho He). }
    split.
    { unfold tp_shregs. split; [|split; [|split]].
      - refine (eq_trans QF22 _). rewrite tgf_denot0, EF40 by lia. exact E32.
      - refine (eq_trans QF8 _). rewrite tgf_denot0, EF40 by lia. exact (eq_trans E8 S8).
      - refine (eq_trans QF9 _). rewrite tgf_denot0, EF40 by lia. exact (eq_trans E9 S9).
      - refine (eq_trans QF18 _). rewrite tgf_denot0, EF40 by lia. exact (eq_trans E18 S18). }
    split; [exact Hf0|].
    split; [refine (eq_trans QF19 _); apply (tg_soff _ 8 8 (t + 8)); [rewrite UtF; reflexivity | lia]|].
    split; [refine (eq_trans QF21 _); apply (tg_soff _ 8 16 (t + 16)); [rewrite UtF; reflexivity | lia]|].
    split; [refine (eq_trans QF23 _); apply (tg_shreg _ t 8); [exact UtF | exact E32F | lia | lia | lia]|].
    split; [refine (eq_trans QF25 _); apply (tg_shreg _ t 16); [exact UtF | exact E32F | lia | lia | lia]|].
    split; [refine (eq_trans QF26 _); apply (tg_tshr _ t); [exact UtF | lia]|].
    split; [exact (proj1 HRWF)|].
    split.
    { unfold tp_blk.
      split; [lia|]. split; [exact Hin4|]. split; [exact H4096r|]. split; [exact HSL8|].
      split; [exact HAMF|].
      split; [intros a Ha; apply (apresent_writable segs); exact (proj1 (Hpr4 a Ha))|].
      split; [exact (tg_ra_of_bs _ res (2 * (len0 + n + 1)) res (2 * (len0 + n + 1)) BSF ltac:(lia) ltac:(lia))|].
      split; [exact HUF|].
      intros a kk Hak Hq.
      destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a kk _ _ HLED3 Hak) as (Hk0 & _).
      pose proof (tg_new_disj _ _ _ _ _ _ l _ _ HARF El (HLl a kk Hak)) as Zd.
      unfold zdisjoint in Zd. cbn [fst snd] in Zd. rewrite (tgs_req_pos (2 * (len0 + n + 1))) in Zd by lia.
      assert (kk + cf_head <= req_size (kk + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
      lia. }
    split; [exact HBYF|].
    split; [change (tp_need D) with (len0 + n + 1); lia|].
    split; [exact HSN|].
    split; [exact HKEPT4|].
    split.
    { unfold tp_fitarm. right. split; [exact HGROW|]. split; [reflexivity|]. split; [exact Hgrow | exact Hbbs]. }
    split.
    { unfold tp_side. split; [exact HLEDF|]. split; [exact HSRCF | exact HRL4]. }
    unfold tp_pos. split; [exact Hposg|].
    unfold tp_pos_keep. intros Hng. exfalso. apply Hng. split; [exact Hf0|]. split; [reflexivity | exact HGROW].
Qed.

End g.
Print Assumptions tp_seg_GROW_ok.
