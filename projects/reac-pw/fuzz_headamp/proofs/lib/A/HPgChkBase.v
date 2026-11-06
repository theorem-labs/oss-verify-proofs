(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b01 (the
   save-slot region, regs_ok_override / ck_regs_ok / ck_lit / ck_atom, ck_kept_run, awr_stk / kwr_stk, the run /
   keep / leaf chain, ck_wx / ck_segs_low) and proofs/reac-pw/fuzz_role/lib/A/RPgRefuse.v at 77f59d02b01 (the .got
   word and shadow-offset cell regions with base None and their al_const proofs) for reac-pw/fuzz_headamp's image A
   (fuzz_headamp.asan): the common plumbing of the walks of headamp's check functions against lib/A/HPgCSpec.v's
   hd_check_*_specX. What is new against role's files: the .got word 0x9c370 and the cell 0xa4db8 of this image;
   the entry state takes data regions and pointer facts as arguments (role's check functions read no memory); the
   shadow entries of the token engine (YCbn.v) for the checked pointer ranges, proved from the contracts'
   range_addressable and hd_app_rng premises (hc_shent); the leaf closes HPgCSpec's hd_post (its ra clause and its
   stack window T_check_STK = 32 around the 16-byte save slot); AR's laws come from the kernel theorem
   YG0q.AR_laws_ok, not a Section hypothesis. Everything here is generic over the segments and over the .got word
   and the cell (hc_entry_at, hc_app_apart_at, hc_prelude_with); the last block is image A's instance, and
   lib/AU/HPgChkBaseU.v is image B's. *)
(* The common plumbing of the image-A walks of fuzz_headamp.asan's check functions (unstripped sha256
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a; the pinned f3e0669d2819 has the same loaded
   bytes except .note.gnu.build-id). Proves no function (kind: walk plumbing).

   Every check function starts `addi sp,sp,-0x10; sd ra,8(sp)` and returns `ld ra,8(sp); addi sp,sp,0x10; ret`;
   the only store is the save of ra into the 16-byte slot [sp - 16, sp). Each one with an instrumented access loads
   the runtime's shadow offset by `auipc aX,0x18; ld aX,..(aX)` (the .got word 0x9c370, which holds the address of
   the shadow-offset cell 0xa4db8) and `ld aY,0(aX)` (the cell, which holds 0x7fff8000). The entry state gives the
   .got word and the cell as read-only regions with absolute addresses (base None): the word as the literal 0xa4db8,
   the cell as env slot 32 = 0x7fff8000, the token engine's shadow base hc_Bx. Both facts are AR's constant law
   (YG0d.al_const) at the record's as_got_shadow and as_shadow_cell, which the walks take as the Section hypotheses
   HBgot : as_got_shadow B = 0x9c370 and HBcell : as_shadow_cell B = 0xa4db8.

   An instrumented access `lb t,0(sh); bnez t,L` with L = `andi u,x,7; [addi u,u,k;] blt u,t,back; report` is the
   token engine's pattern (YCbn.v tok_load / tok_branch / slow_block): when the shadow entries cover the checked
   bytes, the engine continues at the access on both arms (u gets a fresh atom), so the report arm is never stepped.
   This covers the slow arm that res->refusal (res + 8, shadow 0x04) always takes. The shadow entries are proved
   from the contract's range_addressable premise; their static check needs the pointer's atom fact below 2^47 and
   the checked range outside the shadow band, both from hd_app_rng's in_app half (hc_app_fact, hc_app_band). The
   data regions miss the .got word and the cell by hd_app_rng's ~ in_img half (hc_app_apart), and the save slot
   because the stack lies above alloc_ceiling (YCbq.astk_ok). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the walk's context: env slot 32 is the shadow base; slots 33.. the values the walk names ---- *)
Definition hc_SB : Z := 0x7fff8000.
Definition hc_Bx : sv := SOff 32 0.
Definition hc_Bspan : Z * Z := (hc_SB, hc_SB + 2 ^ 44 - 1).
Definition hc_extra (xs : list Z) : list word := map (Z_to_bv 64) (hc_SB :: xs).
Lemma hc_E32 : forall regs xs, ew (Ereg regs (hc_extra xs)) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs xs. exact (ew_Ereg_extra regs (hc_extra xs) 0). Qed.
Lemma hc_E33 : forall regs w xs, ew (Ereg regs (hc_extra (w :: xs))) 33 = Z_to_bv 64 w.
Proof. intros regs w xs. exact (ew_Ereg_extra regs (hc_extra (w :: xs)) 1). Qed.

(* ---- the entry state ---- *)
(* the save slot [sp - 16, sp) *)
Definition hc_stack_region : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [].
(* a read-only data region at the pointer in register slot n *)
Definition hc_data (n : nat) (lo hi : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some n) lo hi 0 0 cs.
(* sp in [2^46, 2^47], 16-aligned; env slot 32 is 0x7fff8000 *)
Definition hc_facts (fs : list (nat * afact)) : facts :=
mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF hc_SB hc_SB 0) :: fs) [] [].
(* a pointer's atom fact: below the highest allocation ceiling *)
Definition HC_PHI : Z := 0x7fffff800000.
Definition hc_pfact (n : nat) (al : Z) : nat * afact := (n, mkAF 0 HC_PHI al).
(* the entry registers: sr_atoms with the overrides ov (register, value the contract fixes) *)
Definition hc_sr (ov : list (bv 5 * sv)) : list sv := fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr_atoms.
(* the .got word [gotw, gotw + 8): the address cellw of the shadow-offset cell; the cell [cellw, cellw + 8):
   0x7fff8000, the atom of env slot 32. Each image instantiates gotw and cellw (image A below, image B in
   lib/AU/HPgChkBaseU.v). *)
Definition hc_got_region_at (gotw cellw : Z) : YP09.region :=
YP09.mkRegion None gotw (gotw + 8) 0 0 [YP09.mkChunk gotw (CVal 8 (SLit cellw))].
Definition hc_cell_region_at (cellw : Z) : YP09.region :=
YP09.mkRegion None cellw (cellw + 8) 0 0 [YP09.mkChunk cellw (CVal 8 hc_Bx)].
Definition hc_base_regions_at (gotw cellw : Z) : smem := [hc_stack_region; hc_got_region_at gotw cellw; hc_cell_region_at cellw].
Definition ss_hc_at (gotw cellw : Z) (pc : Z) (ov : list (bv 5 * sv)) (rs : smem) (fs : list (nat * afact)) : sstate :=
mkSS pc (hc_sr ov) (hc_base_regions_at gotw cellw ++ rs) None (hc_facts fs).

(* an override of a register by a value it already has keeps regs_ok *)
Lemma hc_regs_ok_override : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> r <> 0%bv -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv r'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hb0.
{ exfalso. apply Hr0. unfold bv_eqb in Hb0. apply Z.eqb_eq in Hb0. apply bv_eq. exact Hb0. }
specialize (Hr r'). unfold sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.
Lemma hc_regs_ok : forall regs extra (ov : list (bv 5 * sv)),
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs extra) (snd p) = getr regs (fst p)) ov ->
regs_ok (Ereg regs extra) (hc_sr ov) regs.
Proof.
intros regs extra ov Hov. unfold hc_sr.
assert (G : forall sr, regs_ok (Ereg regs extra) sr regs ->
regs_ok (Ereg regs extra) (fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr) regs).
{ induction Hov as [|[r e] ov [Hr0 Hv] Hov IH]; intros sr Hsr; cbn [fold_left]; [exact Hsr|].
apply IH. apply hc_regs_ok_override; assumption. }
apply G. apply regs_ok_Ereg.
Qed.
Lemma hc_lit : forall E v, sv_denot E (SLit v) = w64 v.
Proof. intros E v. reflexivity. Qed.
Lemma hc_atom_off : forall regs extra n (r : bv 5) c, Z.of_nat n = bv_unsigned r ->
sv_denot (Ereg regs extra) (SOff n c) = Z_to_bv 64 (bv_unsigned (getr regs r) + c).
Proof.
intros regs extra n r c Hn. apply bv_eq. rewrite denot_SOff, (ew_Ereg_nat regs extra n r Hn).
rewrite Z_to_bv_unsigned. reflexivity.
Qed.
Lemma hc_nz : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv.
Proof. intros r Hr Hz. apply Hr. rewrite Hz. reflexivity. Qed.
(* an env slot holding v denotes v as an atom *)
Lemma hc_denot_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. apply bv_eq. rewrite denot_SOff, H, Z.add_0_r, unsigned_lit_small by exact Hv.
apply zcanon_id. unfold M64. lia.
Qed.
(* a register's env slot *)
Lemma hc_ew : forall regs extra n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v ->
ew (Ereg regs extra) n = Z_to_bv 64 v.
Proof. intros regs extra n r v Hn H. rewrite (ew_Ereg_nat regs extra n r Hn). exact H. Qed.
(* a signed compare of two values in the signed range *)
Lemma hc_lts : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
intros a b Ha Hb. unfold bv_lts. rewrite !signed_lit, !zcanon_wrap, !bv_swrap_wrap', !swrap64_id by (unfold half64; lia).
reflexivity.
Qed.
(* image B's alignment trap of two 4-aligned pointers: `or t,a,b; andi t,t,3; bnez t,trap` (the UBSan
   type-mismatch check of check_keys / check_refusal) reads 0 *)
Lemma hc_or_align4 : forall E n m p q, bv_unsigned (ew E n) = p -> bv_unsigned (ew E m) = q ->
p mod 4 = 0 -> q mod 4 = 0 -> U E (SAlu ALU_AND (SAlu ALU_OR (SOff n 0) (SOff m 0)) (SLit 3)) = 0.
Proof.
intros E n m p q Hn Hm Hp Hq.
pose proof (bv_unsigned_in_range _ (ew E n)) as Bn. pose proof (bv_unsigned_in_range _ (ew E m)) as Bm.
change (bv_modulus 64) with (2 ^ 64) in Bn, Bm. rewrite Hn in Bn. rewrite Hm in Bm.
rewrite !U_SAlu, !U_SOff, U_SLit, Hn, Hm, !Z.add_0_r. cbn [zalu_raw].
unfold zcanon, M64.
rewrite (Z.mod_small p), (Z.mod_small q), (Z.mod_small 3) by lia.
change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
rewrite (Z.mod_mod_divide (Z.lor p q) (2 ^ 64) (2 ^ 2)) by (exists (2 ^ 62); reflexivity).
rewrite (Z.mod_small (Z.lor p q mod 2 ^ 2) (2 ^ 64)) by (pose proof (Z.mod_pos_bound (Z.lor p q) (2 ^ 2) ltac:(lia)); lia).
rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l, !Z.land_ones by lia.
change (2 ^ 2) with 4. rewrite Hp, Hq. reflexivity.
Qed.
(* a register holding the pointer p *)
Lemma hc_Ereg_ptr : forall regs extra n (r : bv 5) p, Z.of_nat n = bv_unsigned r -> getr regs r = w64 p -> 0 <= p < 2 ^ 64 ->
bv_unsigned (ew (Ereg regs extra) n) = p.
Proof. intros regs extra n r p Hn H Hp. rewrite (ew_Ereg_nat regs extra n r Hn), H. apply unsigned_lit_small. exact Hp. Qed.

Section g. Context {segs : list Segment}.
(* a range inside one segment is image *)
Lemma hc_in_img_of_b : forall a n,
existsb (fun s : Segment => (Z.of_N (seg_base s) <=? a) && (a + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs = true ->
forall x, a <= x < a + n -> in_img segs x.
Proof.
intros a n H x Hx. apply existsb_exists in H as (sg & Hin & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
Qed.
(* a read-only data region at the pointer p held in env slot n *)
Lemma hc_data_ok : forall E m n p lo hi cs,
bv_unsigned (ew E n) = p -> 0 <= p + lo -> p + hi <= 2 ^ 64 ->
Forall (YP09.chunk_ok segs E m p) cs ->
region_ok segs E m (hc_data n lo hi cs).
Proof.
intros E m n p lo hi cs Hn Hlo Hhi Hcs. unfold region_ok, hc_data.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hn.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia | exact Hcs].
Qed.
(* a 4-byte chunk holding the 32-bit value of an atom *)
Lemma hc_chunk4 : forall E m p off e v,
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> val_mem segs m (p + off) 4 v ->
YP09.chunk_ok segs E m p (YP09.mkChunk off (CVal 4 e)).
Proof. intros E m p off e v He Hv Hm. apply (chunk_ok_val segs E m p off 4 e v He); [exact Hv | zside | exact Hm]. Qed.
Lemma hc_chunk1 : forall E m p off e v,
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 8 -> val_mem segs m (p + off) 1 v ->
YP09.chunk_ok segs E m p (YP09.mkChunk off (CVal 1 e)).
Proof. intros E m p off e v He Hv Hm. apply (chunk_ok_val segs E m p off 1 e v He); [exact Hv | zside | exact Hm]. Qed.
(* the value premises of the contracts in the chunk form: the four bytes of v are the bytes of v mod 2^32 *)
Lemma hc_val4_mod : forall m a v, val_mem segs m a 4 v -> val_mem segs m a 4 (v mod 2 ^ 32).
Proof.
intros m a v H k Hk. rewrite (H k Hk). do 2 f_equal. unfold YO0f.le_byte. change 256 with (2 ^ 8).
try change (8 * Z.of_nat 4) with 32.
assert (Hs : 0 <= 8 * Z.of_nat k <= 24) by lia.
apply Z.bits_inj'. intros n Hn. destruct (Z.lt_ge_cases n 8) as [Hl | Hh].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* ---- the checked ranges: hd_app_rng's two halves ---- *)
Section a. Context {rc : YM05.RunCeil}.
Lemma hc_app_fact : forall p n, in_app p n -> 0 <= n -> 4096 <= p /\ p + n <= ASAN_CEIL /\ ASAN_CEIL <= HC_PHI.
Proof.
intros p n [H1 H2] Hn. pose proof ASAN_CEIL_range as [C _]. unfold kLowShadowBeg, kHighMemBeg, HC_PHI in *. lia.
Qed.
Lemma hc_app_band : forall p n, in_app p n ->
forall x, p <= x < p + n -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof.
intros p n [H1 H2] x Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
(* a range outside the image misses the .got word and the cell, both image bytes *)
Lemma hc_app_apart_at : forall gotw cellw p n,
(forall x, gotw <= x < gotw + 8 -> in_img segs x) -> (forall x, cellw <= x < cellw + 8 -> in_img segs x) ->
(forall x, p <= x < p + n -> ~ in_img segs x) -> 0 < n ->
(p + n <= gotw \/ gotw + 8 <= p) /\ (p + n <= cellw \/ cellw + 8 <= p).
Proof.
intros gotw cellw p n Hg Hc H Hn. split.
- destruct (Z_le_gt_dec (p + n) gotw) as [|H1]; [left; lia|].
destruct (Z_le_gt_dec (gotw + 8) p) as [|H2]; [right; lia|].
exfalso. apply (H (Z.max p gotw)); [lia|]. apply Hg. lia.
- destruct (Z_le_gt_dec (p + n) cellw) as [|H1]; [left; lia|].
destruct (Z_le_gt_dec (cellw + 8) p) as [|H2]; [right; lia|].
exfalso. apply (H (Z.max p cellw)); [lia|]. apply Hc. lia.
Qed.
(* a shadow entry for [p + lo, p + hi), p the value of env slot n *)
Lemma hc_shent : forall H mem E (n : nat) p lo hi,
range_addressable (aview segs H mem) SHADOW_OFF (p + lo) (hi - lo) -> in_app (p + lo) (hi - lo) ->
ew E 32 = Z_to_bv 64 SHADOW_OFF -> bv_unsigned (ew E n) = p -> lo <= hi ->
shent_ok segs hc_Bx E (mrestrict H mem) (mkSHE n lo hi).
Proof.
intros H mem E n p lo hi Hra Happ E32 En Hle.
apply (shent_ok_of_range segs H mem E hc_Bx n (p + lo) (hi - lo) p lo hi Hra).
- unfold U, hc_Bx. rewrite denot_SOff, E32, Z.add_0_r. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
apply zcanon_id. unfold SHADOW_OFF, M64. lia.
- unfold U. rewrite denot_SOff, En, Z.add_0_r. apply zcanon_id.
pose proof (bv_unsigned_in_range _ (ew E n)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
- lia.
- lia.
- intros x Hx. apply (hc_app_band (p + lo) (hi - lo) Happ). lia.
Qed.
End a.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the entry state: the save slot, the .got word and the cell, then the walk's data regions rs and facts fs *)
Lemma hc_entry_at : forall gotw cellw pc ov xs (rs : smem) fs (W : world segs) regs memc,
0 <= gotw -> gotw + 8 <= 2 ^ 64 -> 0 <= cellw -> cellw + 8 <= 2 ^ 64 -> 0 <= pc ->
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs (hc_extra xs)) (snd p) = getr regs (fst p)) ov ->
(forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 ->
rdword (aview segs (w_H W) memc) gotw = Some cellw ->
rdword (aview segs (w_H W) memc) cellw = Some SHADOW_OFF ->
regions_wf (hc_base_regions_at gotw cellw ++ rs) = true ->
Forall (region_ok segs (Ereg regs (hc_extra xs)) (mrestrict (w_H W) memc)) rs ->
zpairwise_disjoint (map (extent_of_region (Ereg regs (hc_extra xs))) (hc_base_regions_at gotw cellw ++ rs)) ->
atoms_ok (Ereg regs (hc_extra xs)) ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF hc_SB hc_SB 0) :: fs) ->
st_ok segs (Ereg regs (hc_extra xs)) (ss_hc_at gotw cellw pc ov rs fs)
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom segs))).
Proof.
intros gotw cellw pc ov xs rs fs W regs memc Hg0 Hg1 Hc0 Hc1 Hpc Hov Hpres Hsp Kgot Kcell Hwf Hrs Hdj Hat.
rewrite restrict_mkst_fx.
set (E := Ereg regs (hc_extra xs)) in *.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; apply hc_E32).
unfold ss_hc_at. apply (entry_st_ok_full segs); change (Ereg regs (hc_extra xs)) with E.
- apply hc_regs_ok. exact Hov.
- exact Hwf.
- unfold hc_base_regions_at, hc_stack_region, hc_got_region_at, hc_cell_region_at. cbn [app].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|exact Hrs]]];
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ (* the save slot *)
rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
+ (* the .got word *)
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val segs E _ 0 gotw 8 (SLit cellw) cellw); [reflexivity | zside | zside |].
exact (val_mem_of_rdword segs (w_H W) memc _ _ Kgot).
+ (* the shadow-offset cell *)
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val segs E _ 0 cellw 8 hc_Bx SHADOW_OFF);
[unfold hc_Bx; apply bv_eq; rewrite denot_SOff, E32, Z.add_0_r;
 rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); apply zcanon_id; unfold SHADOW_OFF, M64; lia
| unfold SHADOW_OFF; zside | zside |].
exact (val_mem_of_rdword segs (w_H W) memc _ _ Kcell).
- apply pairwise_disjoint_of_extents. exact Hdj.
- split; [exact Hat | split; [exact I | exact I]].
Qed.
End b.

(* ---- the walk's plumbing [RPgCheck.v ck_kept_run, awr_stk, kwr_stk, ck_run, ck_keep, ck_leaf] ---- *)
Lemma hc_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
(* a run keeps every byte outside the zone its write windows lie in *)
Lemma hc_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview segs H m1 a = aview segs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview segs H m2 a = aview segs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
End g.

(* the write-range obligation: the save slot [sp - 16, sp) lies in the caller's stack allowance *)
Ltac hc_awr :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch goal with B2 : bv_unsigned (ew _ 2) = ?spv |- _ =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
[reflexivity | cbn [ew ewset Nat.eqb]; rewrite B2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia
| cbn [YP09.r_wlo YP09.r_whi]; lia |] ]
end end.
(* every write window of a state lies in the save slot [sp - 16, sp) *)
Ltac hc_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Hb;
first [ lazymatch goal with B2 : bv_unsigned (ew _ 2) = _ |- _ => rewrite B2 in Hb end; lia | lia ] | ]);
destruct Hr.
Ltac hc_run tblok :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok tblok HS HJ SHOK hc_Bspan; [hc_awr | ] end.
Ltac hc_keep :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (hc_kept_run _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by hc_kwr end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the split at a branch the engine does not decide: each side gets its condition `branch_taken c a b = true`
   or `= false` *)
Ltac hc_branch tblok :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tblok HS SH hc_Bspan end.
(* the `ret` leaf, into HPgCSpec's hd_post at fx2 = fx, E = False and R = True: the ra clause from the restored ra,
   the memory clause from KE (the save slot lies in the stack window [sp - T_check_STK, sp)) *)
Ltac hc_leaf tblok :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
  KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
lazymatch type of tblok with table_ok _ ?tbl =>
let HWX := lazymatch goal with H : wx_segs_nowrap _ |- _ => H end in
eapply (SRr_ret_at _ tbl tblok HWX W E); [exact HS | reflexivity | vm_compute; reflexivity |] end;
let mat' := fresh "mat" in intros mat';
red; eexists; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [lazymatch goal with E1 : ew _ 1 = getr _ 1, Hra : YK0s.ret_ok _ |- _ => rewrite R1, E1, Hra; reflexivity end|];
split; [reflexivity|];
split; [eapply ajournal_materialize; eassumption|];
split; [lazymatch goal with HAE : env_agree 32 _ _ |- _ =>
  eapply aregs_preserved_of_st_ok; [exact HS | env_agree_chain HAE | vm_compute; reflexivity] end|];
split; [lazymatch goal with E1 : ew _ 1 = getr _ 1 |- _ => etransitivity; [exact R1 | exact E1] end|];
split; [reflexivity|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply hc_same_io_wvb]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split; [let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
        let Hq := fresh "Hq" in
        intros a Ha Hz _; apply (KE a Ha); intros Hq; apply Hz; unfold T_check_STK; lia | exact I]
end.
(* the common start of a walk: AR's laws, the journal's stack facts, the .got word and the cell by AR's constant
   law at HBgot / HBcell, sp in [2^46, 2^47] and the save slot present; wx and slow are the image's
   wx_segs_nowrap and segments-below-kLowMemEnd facts *)
Ltac hc_prelude_with wx slow :=
lazymatch goal with
| HJ : ajournal ?segs ?B ?STK ?sp0 _ _ _ _ _ _ _ ?lyc ?Sc ?W ?memc ?mdc _, HBgot : as_got_shadow ?B = _,
  HBcell : as_shadow_cell ?B = _, Hwlo : _ <= spZ ?regs - T_check_STK |- _ =>
pose proof (AR_laws_ok segs B) as LAWS;
pose proof wx as Hwx; pose proof slow as Hsegs;
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _);
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _);
pose proof asan_consts as (C1 & _);
unfold T_check_STK in Hwlo;
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _);
rewrite HBgot, HBcell in Kgot; rewrite HBcell in Kcell;
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia;
assert (Hpr : forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) by (intros a Ha; apply Hpres; lia)
end.

(* ======================== image A (fuzz_headamp.asan, lib/A/Img0.v rsegs) ======================== *)
(* ---- the image's code and segments ---- *)
Lemma hc_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma hc_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.

(* ---- the shadow offset: the .got word and the cell ---- *)
Definition HC_GOT_SH : Z := 0x9c370.
Definition HC_SH_CELL : Z := 0xa4db8.
Lemma hc_got_img : forall x, HC_GOT_SH <= x < HC_GOT_SH + 8 -> in_img rsegs x.
Proof. apply hc_in_img_of_b. vm_compute. reflexivity. Qed.
Lemma hc_cell_img : forall x, HC_SH_CELL <= x < HC_SH_CELL + 8 -> in_img rsegs x.
Proof. apply hc_in_img_of_b. vm_compute. reflexivity. Qed.

(* the regions at image A's .got word and cell (the literal forms the walks unfold) *)
Definition hc_got_region : YP09.region :=
YP09.mkRegion None HC_GOT_SH (HC_GOT_SH + 8) 0 0 [YP09.mkChunk HC_GOT_SH (CVal 8 (SLit HC_SH_CELL))].
Definition hc_cell_region : YP09.region :=
YP09.mkRegion None HC_SH_CELL (HC_SH_CELL + 8) 0 0 [YP09.mkChunk HC_SH_CELL (CVal 8 hc_Bx)].
Definition hc_base_regions : smem := [hc_stack_region; hc_got_region; hc_cell_region].
Definition ss_hc (pc : Z) (ov : list (bv 5 * sv)) (rs : smem) (fs : list (nat * afact)) : sstate :=
mkSS pc (hc_sr ov) (hc_base_regions ++ rs) None (hc_facts fs).
Lemma hc_app_apart : forall p n, (forall x, p <= x < p + n -> ~ in_img rsegs x) -> 0 < n ->
(p + n <= HC_GOT_SH \/ HC_GOT_SH + 8 <= p) /\ (p + n <= HC_SH_CELL \/ HC_SH_CELL + 8 <= p).
Proof. intros p n H Hn. exact (hc_app_apart_at HC_GOT_SH HC_SH_CELL p n hc_got_img hc_cell_img H Hn). Qed.
Section ia. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma hc_entry : forall pc ov xs (rs : smem) fs (W : world rsegs) regs memc, 0 <= pc ->
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs (hc_extra xs)) (snd p) = getr regs (fst p)) ov ->
(forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 ->
rdword (aview rsegs (w_H W) memc) HC_GOT_SH = Some HC_SH_CELL ->
rdword (aview rsegs (w_H W) memc) HC_SH_CELL = Some SHADOW_OFF ->
regions_wf (hc_base_regions ++ rs) = true ->
Forall (region_ok rsegs (Ereg regs (hc_extra xs)) (mrestrict (w_H W) memc)) rs ->
zpairwise_disjoint (map (extent_of_region (Ereg regs (hc_extra xs))) (hc_base_regions ++ rs)) ->
atoms_ok (Ereg regs (hc_extra xs)) ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF hc_SB hc_SB 0) :: fs) ->
st_ok rsegs (Ereg regs (hc_extra xs)) (ss_hc pc ov rs fs)
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc ov xs rs fs W regs memc Hpc. apply (hc_entry_at HC_GOT_SH HC_SH_CELL); unfold HC_GOT_SH, HC_SH_CELL; lia.
Qed.
End ia.
Ltac hc_prelude := hc_prelude_with hc_wx hc_segs_low.
