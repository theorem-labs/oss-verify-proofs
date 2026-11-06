(* fuzz_preset, S1 ALLOC-HEAP, image A (asan, f0d2e8d4): the walk of fuzz_free (alloc.c :118-127; A 0x85754, 71 slots
   of h-verbs-1's whole-program listing lib/A/Listing_prog.v, PI_prog_A) against K0's text tfuzz_free_specX
   (lib/A/PRH_FnAlloc.v, room invariant room_live_cf at RL := prh_room_live_a8, with the named live-set bound on ccnt24),
   at the allocator relation ARcf pa_segs B /\ xs_placed_cf (h-mani-a8's
   YG0ncf.v, S1KitAlloc's YGcallcf.v), preset's CfParams_preset and CfImg_A, in cgif's per-function form (fuzz_grant's
   CtrlIdentityPollBlock.v on origin/cold/pg-prog): YC80x / YC1fPx's mixed runner over YCbqG's ajournal_x (the frame and
   the static g_live), __asan_unpoison_memory_region by YGcallPx's aj_unpoison_x, the tail jump to the free wrapper by
   YGcallx's aj_free_x_ct at o = 0, the ledger by S1Ledger's prh_ledger_disown.
   KIT 342c852ff9b6 (K0's old-pin text fix): the m-form post (fpostm) is paid by h-hpreset-7's carrier
   m |-> (memnorm mem -> memnorm m) through the runner segments (YC1fPx's paj_run_x_m_inv) and across the two calls by
   the texts' own keeps (YGcallMxmn's aj_unpoison_x_m, aj_free_x_ct_m); the run position by h-pre-b1's
   PresetRoomPosKeep (room_pos_keep_free / room_pos_keep_bulk_free at the tail call, room_pos_keep_eq on p = 0); the
   ccnt24 arms by S1Ccnt24.v's prh_ccnt24_free (the free's block equation; the internal file CCNT24-FREE.md).
   #102 (this line, A' images, the kit of record walkkit-next decff67d721f): the ledger carries g_most / g_own_ran_out
   (prh_ledger .. most own); the walk keeps both cells off its writes (KSV) and passes them through
   prh_glob_final_le and prh_ledger_disown (the S1Ledger.v 8cf15eeb6311).
   The body (A's listing): p = 0 returns; else unpoison (p - 16, 16), the two ASan checks of the head (folded: the
   head's shadow is 0 after the unpoison), k := the head (eight lbu), g_live -= k (a store through an auipc base: a row
   of the generated alias table A_alias_hints), the frame popped, `j __wrap_free` with a0 = p - 16 and the entry ra.
   Numerals in this file: the frame 32 (LENGTH: the listing's `addi sp, sp, -32`), the head 16 / -16 / -8 / 8 (LENGTH:
   cf_head of CfParams_preset and the head word), the stack need 16416 (DERIVED: STK_fuzz_free at prh_img_A, by
   computation), 4096 / 4112 (DERIVED: cgif's lowest block, + cf_head), atom indices 2 / 10 / 32 / 33 / 34 and the
   call base 48 (DERIVED: the symbolic engine's numbering, cgif's convention), register numbers (WORD), the byte lanes
   8 .. 56, 256 and the spans 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64 (WORD / DERIVED: bytes, machine words, the engine's
   spans), 39 (LENGTH: the listing's object count, PAImg's pa_obj_img). No ADDRESS literal: every address is
   A_prog_sigma / A_prog_val of lib/A/PAImg_prog.v, a CfImg_A field, or a PrhImg field of lib/A/PRH_Img.v.
   THE RE-HIDING MOVE (the text concludes SRr' segs RZ_cf, its post fpostbm at wle' segs RZ_cf): the non-NULL arm runs
   over the R runners at wle' segs RZ_cf (YC1fPx's paj_run_x_m_invR, YCbqG's ajournal_x_initR, YGcallMxmn's
   aj_unpoison_x_mR) and calls the primed free row with the memnorm keep (YGcfMallocComposeKeep's
   afree_realizes_cf_rh_keep) by YGcallMxmnKeep's aj_free_x_ct_m_rh_keep, whose last conjunct carries memnorm across
   the free; the NULL arm keeps its plain walk and is lifted (YA0nH.SRr_SRr', YCbqG.ajournal_xwR_mono at
   YA0nH.wle_wle'). The free's call memory QMm_cf: cf_hull_ok from the text's budget (lib/A/PresetHullPay.v
   hull_ok_of_budget) and arodata_ok_cf from the entry's reader form through the journal (YGcallcf.v
   arodata_ok_cf_of_journal_P at image A's rows, lib/A/CfAroPresetA.v); the hull use from the free's model path
   (YGcfSecsStep.secs_free_step). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallx YGcallcf YGcallPx YGcallPcf YGcfHp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetRun PresetReqAt PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm YGcallMxmn YCbqGwild.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA S1Ledger S1Ccnt24.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfSecsStep YGcfAroBridge
  YGcfMallocComposeKeep YGcallMxmnKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0m CfAroPresetA PresetHullPay.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the head read (A 0x857b0-0x8580c): eight lbu of the head bytes recombined by slli / or are the head word.
   Same shape and proof as S1ReallocA's (lib/A/Prog/FuzzRealloc.v ra_hdr_sv), restated so this file depends on no
   other walk. ---- *)
Definition ff_hb (x : nat) (s : Z) : sv := SExt false 8 (SAlu ALU_SRL (SOff x 0) (SLit s)).
Definition ff_hsll (v : sv) (t : Z) : sv := SAlu ALU_SLL v (SLit t).
Definition ff_hhalf (b3 b2 b1 b0 : sv) : sv :=
  SAlu ALU_OR (SAlu ALU_OR (ff_hsll b3 24) (ff_hsll b2 16)) (SAlu ALU_OR (ff_hsll b1 8) b0).
Definition ff_hdr_sv (x : nat) : sv :=
  SAlu ALU_OR (ff_hsll (ff_hhalf (ff_hb x 56) (ff_hb x 48) (ff_hb x 40) (ff_hb x 32)) 32)
    (ff_hhalf (ff_hb x 24) (ff_hb x 16) (ff_hb x 8) (SExt false 8 (SOff x 0))).
Lemma ff_zc : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. lia. Qed.
Lemma ff_land63 : forall s, 0 <= s < 64 -> Z.land s 63 = s.
Proof. intros s Hs. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma ff_lor_add : forall a b s, 0 <= a -> 0 <= s -> 0 <= b < 2 ^ s -> Z.lor (a * 2 ^ s) b = a * 2 ^ s + b.
Proof.
intros a b s Ha Hs Hb. apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
destruct (Z.lt_ge_cases n s) as [Hl|Hl].
- rewrite Z.mul_pow2_bits_low by lia.
  rewrite <- (Z.mod_pow2_bits_low (a * 2 ^ s + b) s n Hl).
  rewrite Z.add_comm, Z.mod_add by (apply Z.pow_nonzero; lia). rewrite Z.mod_small by lia. reflexivity.
- rewrite Z.mul_pow2_bits by lia.
  assert (Hbn : Z.testbit b n = false).
  { destruct (Z.eq_dec b 0) as [->|Hb0]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
    apply (Z.lt_le_trans _ (2 ^ s)); [lia | apply Z.pow_le_mono_r; lia]. }
  rewrite Hbn, Bool.orb_false_r.
  assert (Ht : Z.testbit (a * 2 ^ s + b) n = Z.testbit ((a * 2 ^ s + b) / 2 ^ s) (n - s)).
  { rewrite <- Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_spec by lia. f_equal; lia. }
  rewrite Ht. rewrite Z.div_add_l by (apply Z.pow_nonzero; lia).
  rewrite (Z.div_small b) by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma ff_U_hb : forall E x s, 0 <= s < 64 -> U E (ff_hb x s) = (bv_unsigned (ew E x) / 2 ^ s) mod 256.
Proof.
intros E x s Hs. unfold ff_hb. rewrite U_SExt, U_SAlu, U_SLit, U_SOff, Z.add_0_r. cbn [zalu_raw].
pose proof (bv_unsigned_in_range _ (ew E x)) as Hw. unfold bv_modulus in Hw. change (Z.of_N 64) with 64 in Hw.
rewrite (ff_zc (bv_unsigned (ew E x))) by lia. rewrite (ff_zc s) by lia. rewrite ff_land63 by lia.
rewrite Z.shiftr_div_pow2 by lia.
assert (H0 : 0 <= bv_unsigned (ew E x) / 2 ^ s < 2 ^ 64).
{ split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (bv_unsigned (ew E x))); [apply Z.div_le_upper_bound; nia | lia]. }
rewrite (ff_zc (bv_unsigned (ew E x) / 2 ^ s)) by lia. change (2 ^ Z.of_N 8) with 256.
apply ff_zc. pose proof (Z.mod_pos_bound (bv_unsigned (ew E x) / 2 ^ s) 256 ltac:(lia)). lia.
Qed.
Lemma ff_U_hb0 : forall E x, U E (SExt false 8 (SOff x 0)) = (bv_unsigned (ew E x) / 2 ^ 0) mod 256.
Proof.
intros E x. rewrite U_SExt, U_SOff, Z.add_0_r. change (2 ^ 0) with 1. rewrite Z.div_1_r.
pose proof (bv_unsigned_in_range _ (ew E x)) as Hw. unfold bv_modulus in Hw. change (Z.of_N 64) with 64 in Hw.
rewrite (ff_zc (bv_unsigned (ew E x))) by lia. change (2 ^ Z.of_N 8) with 256.
apply ff_zc. pose proof (Z.mod_pos_bound (bv_unsigned (ew E x)) 256 ltac:(lia)). lia.
Qed.
Lemma ff_U_hsll : forall E v t c, U E v = c -> 0 <= c -> 0 <= t < 64 -> c * 2 ^ t < 2 ^ 64 ->
  U E (ff_hsll v t) = c * 2 ^ t.
Proof.
intros E v t c Hv Hc Ht Hlt. unfold ff_hsll. rewrite U_SAlu, U_SLit, Hv. cbn [zalu_raw].
rewrite (ff_zc t) by lia. rewrite ff_land63 by lia. rewrite Z.shiftl_mul_pow2 by lia.
apply ff_zc. assert (0 <= c * 2 ^ t) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.
Lemma ff_U_hor : forall E u v a s b, U E u = a * 2 ^ s -> U E v = b -> 0 <= a -> 0 <= s -> 0 <= b < 2 ^ s ->
  a * 2 ^ s + b < 2 ^ 64 -> U E (SAlu ALU_OR u v) = a * 2 ^ s + b.
Proof.
intros E u v a s b Hu Hv Ha Hs Hb Hlt. rewrite U_SAlu, Hu, Hv. cbn [zalu_raw]. rewrite ff_lor_add by lia.
apply ff_zc. assert (0 <= a * 2 ^ s) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.
Lemma ff_dm : forall w k k', 0 <= w -> 0 <= k -> k' = k + 8 ->
  w / 2 ^ k = (w / 2 ^ k) mod 256 + 256 * (w / 2 ^ k').
Proof.
intros w k k' Hw Hk ->. rewrite (Z.div_mod (w / 2 ^ k) 256) at 1 by lia.
rewrite Z.div_div by (try apply Z.pow_nonzero; lia). rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. lia.
Qed.
Lemma ff_hdr_U : forall E x, U E (ff_hdr_sv x) = bv_unsigned (ew E x).
Proof.
intros E x.
pose proof (bv_unsigned_in_range _ (ew E x)) as Hw. unfold bv_modulus in Hw. change (Z.of_N 64) with 64 in Hw.
set (w := bv_unsigned (ew E x)) in *.
assert (BB : forall s, 0 <= (w / 2 ^ s) mod 256 < 256) by (intros s; apply Z.mod_pos_bound; lia).
pose proof (BB 0) as R0. pose proof (BB 8) as R8. pose proof (BB 16) as R16. pose proof (BB 24) as R24.
pose proof (BB 32) as R32. pose proof (BB 40) as R40. pose proof (BB 48) as R48. pose proof (BB 56) as R56.
set (b0 := (w / 2 ^ 0) mod 256) in *. set (b8 := (w / 2 ^ 8) mod 256) in *. set (b16 := (w / 2 ^ 16) mod 256) in *.
set (b24 := (w / 2 ^ 24) mod 256) in *. set (b32 := (w / 2 ^ 32) mod 256) in *. set (b40 := (w / 2 ^ 40) mod 256) in *.
set (b48 := (w / 2 ^ 48) mod 256) in *. set (b56 := (w / 2 ^ 56) mod 256) in *.
assert (HL : U E (ff_hhalf (ff_hb x 24) (ff_hb x 16) (ff_hb x 8) (SExt false 8 (SOff x 0))) =
  (b24 * 2 ^ 8 + b16) * 2 ^ 16 + (b8 * 2 ^ 8 + b0)).
{ unfold ff_hhalf. apply ff_U_hor; try lia.
  - replace ((b24 * 2 ^ 8 + b16) * 2 ^ 16) with (b24 * 2 ^ 24 + b16 * 2 ^ 16) by ring.
    apply ff_U_hor; try lia.
    + apply ff_U_hsll; [apply ff_U_hb; lia | lia | lia | lia].
    + apply ff_U_hsll; [apply ff_U_hb; lia | lia | lia | lia].
  - apply ff_U_hor; try lia.
    + apply ff_U_hsll; [apply ff_U_hb; lia | lia | lia | lia].
    + apply ff_U_hb0. }
assert (HH : U E (ff_hhalf (ff_hb x 56) (ff_hb x 48) (ff_hb x 40) (ff_hb x 32)) =
  (b56 * 2 ^ 8 + b48) * 2 ^ 16 + (b40 * 2 ^ 8 + b32)).
{ unfold ff_hhalf. apply ff_U_hor; try lia.
  - replace ((b56 * 2 ^ 8 + b48) * 2 ^ 16) with (b56 * 2 ^ 24 + b48 * 2 ^ 16) by ring.
    apply ff_U_hor; try lia.
    + apply ff_U_hsll; [apply ff_U_hb; lia | lia | lia | lia].
    + apply ff_U_hsll; [apply ff_U_hb; lia | lia | lia | lia].
  - apply ff_U_hor; try lia.
    + apply ff_U_hsll; [apply ff_U_hb; lia | lia | lia | lia].
    + apply ff_U_hb; lia. }
unfold ff_hdr_sv. rewrite (ff_U_hor E _ _ ((b56 * 2 ^ 8 + b48) * 2 ^ 16 + (b40 * 2 ^ 8 + b32)) 32
  ((b24 * 2 ^ 8 + b16) * 2 ^ 16 + (b8 * 2 ^ 8 + b0))); [| apply ff_U_hsll; [exact HH | lia | lia | lia] | exact HL | lia | lia | lia | lia].
pose proof (ff_dm w 0 8 ltac:(lia) ltac:(lia) eq_refl) as D0. pose proof (ff_dm w 8 16 ltac:(lia) ltac:(lia) eq_refl) as D8.
pose proof (ff_dm w 16 24 ltac:(lia) ltac:(lia) eq_refl) as D16. pose proof (ff_dm w 24 32 ltac:(lia) ltac:(lia) eq_refl) as D24.
pose proof (ff_dm w 32 40 ltac:(lia) ltac:(lia) eq_refl) as D32. pose proof (ff_dm w 40 48 ltac:(lia) ltac:(lia) eq_refl) as D40.
pose proof (ff_dm w 48 56 ltac:(lia) ltac:(lia) eq_refl) as D48. pose proof (ff_dm w 56 64 ltac:(lia) ltac:(lia) eq_refl) as D56.
assert (Z0 : w / 2 ^ 0 = w) by (change (2 ^ 0) with 1; apply Z.div_1_r).
assert (Z64 : w / 2 ^ 64 = 0) by (apply Z.div_small; lia).
fold b0 b8 b16 b24 b32 b40 b48 b56 in D0, D8, D16, D24, D32, D40, D48, D56.
clearbody b0 b8 b16 b24 b32 b40 b48 b56 w. clear HL HH BB.
rewrite Z0 in D0. rewrite Z64 in D56. clear Z0 Z64.
remember (w / 2 ^ 8) as q8 eqn:Q8. remember (w / 2 ^ 16) as q16 eqn:Q16. remember (w / 2 ^ 24) as q24 eqn:Q24.
remember (w / 2 ^ 32) as q32 eqn:Q32. remember (w / 2 ^ 40) as q40 eqn:Q40. remember (w / 2 ^ 48) as q48 eqn:Q48.
remember (w / 2 ^ 56) as q56 eqn:Q56. clear Q8 Q16 Q24 Q32 Q40 Q48 Q56.
change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *. change (2 ^ 32) with 4294967296 in *.
lia.
Qed.
Lemma ff_hdr_denot : forall E x, sv_denot E (ff_hdr_sv x) = ew E x.
Proof. intros E x. apply bv_eq. exact (ff_hdr_U E x). Qed.

(* ---- the symbolic states at fuzz_free's entry (atoms per a Theorem Labs lane's internal file INTERFACE.md: A_OBJ 0 the shadow-base GOT
   cell, A_OBJ 12 the cell it points to, A_OBJ 9 g_live).
   p <> 0 (ss_ff): atoms 2 = entry sp, 10 = p, 32 = the shadow offset, 33 = g_live, 34 = the block's head word k;
   regions: the 32-byte frame, the GOT slot and the cell (read only), g_live (written), the head word (read only);
   the g_live store's alias row is h-verbs-1's generated A_alias_hints.
   p = 0 (ss_ff0): the frame only. ---- *)
Definition FF_PC : Z := 4 * Z.of_nat (A_prog_slot AS_fuzz_free).
Definition FF_Bx : sv := SOff 32 0.
Definition FF_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition ff_live : YP09.region := YP09.mkRegion (Some (A_OBJ 9)) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition ff_head : YP09.region := YP09.mkRegion (Some 10%nat) (-16) (-8) 0 0 [YP09.mkChunk (-16) (CVal 8 (SOff 34 0))].
Definition ff_regions : smem := [stack_region 32; got_regionP; bcell_regionP 32; ff_live; ff_head].
Definition ff_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4112 (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (A_OBJ 9, mkAF (A_prog_val (A_OBJ 9)) (A_prog_val (A_OBJ 9)) 0)] [] A_alias_hints.
Definition ss_ff : sstate := mkSS FF_PC sr_atoms ff_regions None ff_facts.
Definition ss_ff0 : sstate := mkSS FF_PC sr_atoms [stack_region 32] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
(* after the unpoison: the head's 16 bytes are addressable (their shadow is 0) *)
Definition ff_SH1 : list shent := [mkSHE 10 (-16) 0].

#[local] Abbreviation PA := (PI_prog_A).
#[local] Abbreviation PL := (PL_prog_A).
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PI_prog_A).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
#[local] Abbreviation PST := (prh_pst (PI := prh_img_A)).
#[local] Abbreviation LIVE := (pi_g_live (PrhImg := prh_img_A)).

(* the statics' addresses, computed from the image record (never typed) *)
Lemma ff_live_val : LIVE = A_prog_val (A_OBJ 9).
Proof. vm_compute. reflexivity. Qed.
Lemma ff_live_pst : forall a, LIVE <= a < LIVE + 8 -> Exists (in_zr a) PST.
Proof. intros a Ha. unfold prh_pst. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. change (Z.of_nat pi_gz_live) with 8. lia. Qed.
(* membership in no write window *)
Lemma ff_not_wr : forall E rs a,
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r \/ base_val E (YP09.r_base r) + YP09.r_whi r <= a \/
                   a < base_val E (YP09.r_base r) + YP09.r_wlo r) rs ->
  ~ in_wrange E rs a.
Proof. intros E rs a HF (r & Hin & Hr). rewrite Forall_forall in HF. specialize (HF r Hin). lia. Qed.
Lemma ff_apres_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_A.
Context {SK : YI16.sink_head}.
(* the statics lie in the image, below the shadow and the stack *)
Lemma ff_pst_range : forall a, Exists (in_zr a) PST -> YImgTop.IMG_LO <= a < YImgTop.IMG_TOP.
Proof.
intros a Ha. pose proof (pst_in_img_A a Ha) as Hi.
exact (@pa_img_range _ A_prog_listing PI_prog_A a Hi).
Qed.

Lemma ff_val : forall j, VAL j = A_prog_val j.
Proof. reflexivity. Qed.
(* atoms 32 .. 34: the shadow base, g_live's entry value, the head word (cgif's extra-atom convention) *)
Definition FF_E (regs : bvmap 5 word) (xs : list Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs (map (Z_to_bv 64) xs)).
Lemma FF_E_img : forall regs xs j, (A_TEXT <= j < A_LIM)%nat -> bv_unsigned (ew (FF_E regs xs) j) = VAL j.
Proof. intros regs xs j Hj. unfold FF_E. rewrite Eimg_img by exact Hj. apply unsigned_lit_small. apply pa_val_range. Qed.
Lemma FF_E_reg : forall regs xs n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (FF_E regs xs) n = getr regs x.
Proof.
intros regs xs n x Hn. unfold FF_E. pose proof (u5_range x) as Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n x Hn).
Qed.
Lemma FF_E_extra : forall regs l k,
  ew (FF_E regs [SHADOW_OFF; l; k]) 32 = Z_to_bv 64 SHADOW_OFF /\
  ew (FF_E regs [SHADOW_OFF; l; k]) 33 = Z_to_bv 64 l /\
  ew (FF_E regs [SHADOW_OFF; l; k]) 34 = Z_to_bv 64 k.
Proof. intros regs l k. unfold FF_E. rewrite !Eimg_low by (unfold A_TEXT; lia). repeat split. Qed.
Lemma FF_E_agree : forall regs xs, env_agree 32 (Ereg regs (map (Z_to_bv 64) xs)) (FF_E regs xs).
Proof. intros regs xs. split; [intros n Hn; unfold FF_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.
Lemma ff_entry_pc : SIGMA AS_fuzz_free = BASE + FF_PC.
Proof. vm_compute. reflexivity. Qed.
Lemma ff_stk : STK_fuzz_free = 16416.
Proof. vm_compute. reflexivity. Qed.
Lemma ff_cf_head : cf_head = 16.
Proof. reflexivity. Qed.
Lemma ff_unpoison_pc : SIGMA AS___asan_unpoison_memory_region = cf_pc_unpoison.
Proof. vm_compute. reflexivity. Qed.

Lemma ff_aview_of_frame : forall (Wx : world SEGS) (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma ff_region_ok : forall E ss ms r, st_ok_pi SEGS VAL E ss ms -> In r (ss_mem ss) -> region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms r HS Hin. destruct (st_ok_mem_ok SEGS E (abs_ss VAL ss) ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r Hin).
Qed.
Lemma ff_chunk_val : forall E m (j : nat) lo hi wlo whi cs off (w : N) e v,
  region_ok SEGS E m (YP09.mkRegion (Some j) lo hi wlo whi cs) -> In (YP09.mkChunk off (CVal w e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS m (bv_unsigned (ew E j) + off) (N.to_nat w) v.
Proof.
intros E m j lo hi wlo whi cs off w e v (_ & _ & _ & Hcs) Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck.
exact (val_of_chunk_ok SEGS E m _ off w e v Hck He Hv Hw).
Qed.
Lemma ff_kept_gen : forall E (m m' : word -> option byte) k b lo hi wlo whi cs, bv_unsigned (ew E k) = b ->
  (forall a, b + lo <= a < b + hi -> mbyte SEGS m' a = mbyte SEGS m a) ->
  (forall a, b + wlo <= a < b + whi -> writable_at SEGS m' a) ->
  region_kept SEGS E m m' (YP09.mkRegion (Some k) lo hi wlo whi cs).
Proof.
intros E m m' k b lo hi wlo whi cs Hb Hm Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hb; intros a Ha;
  [exact (Hm a Ha) | intros _; exact (Hw a Ha)].
Qed.

(* the image numbers a walk compares, computed from the generated instance, never typed *)
Ltac ff_lits :=
  repeat match goal with
  | H : context [@pa_val ?r A_prog_listing PI_prog_A ?j] |- _ =>
    let v := eval vm_compute in (A_prog_val j) in change (@pa_val r A_prog_listing PI_prog_A j) with v in H
  | |- context [@pa_val ?r A_prog_listing PI_prog_A ?j] =>
    let v := eval vm_compute in (A_prog_val j) in change (@pa_val r A_prog_listing PI_prog_A j) with v
  | H : context [A_prog_val ?j] |- _ =>
    let v := eval vm_compute in (A_prog_val j) in change (A_prog_val j) with v in H
  | |- context [A_prog_val ?j] =>
    let v := eval vm_compute in (A_prog_val j) in change (A_prog_val j) with v
  end;
  cbv [pi_g_live pi_g_peak pi_g_count pi_g_fail pi_g_ran_out pi_g_most pi_g_own_ran_out pi_gz_live pi_gz_peak
       pi_gz_count pi_gz_fail pi_gz_ran_out pi_gz_most pi_gz_own_ran_out prh_img_A YImgTop.IMG_LO YImgTop.IMG_TOP] in *.
(* the frame and g_live are the only write windows of a stretch *)
Definition ff_rs_ok (rs : smem) : Prop := forall r, In r rs ->
  YP09.r_whi r <= YP09.r_wlo r \/
  (YP09.r_base r = Some 2%nat /\ -32 <= YP09.r_wlo r /\ YP09.r_whi r <= 0) \/
  (YP09.r_base r = Some (A_OBJ 9) /\ 0 <= YP09.r_wlo r /\ YP09.r_whi r <= 8).
Ltac ff_rs :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; vm_compute in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi];
      first [ left; lia | right; left; split; [reflexivity | lia] | right; right; split; [reflexivity | lia] ] | ]);
  destruct Hr.
Lemma ff_wr_lem : forall E rs STK sp0 FP bl0 blc ly own, img_env VAL A_LIM E -> bv_unsigned (ew E 2) = sp0 -> 32 <= STK ->
  ff_rs_ok rs -> forall a, in_wrange E rs a -> awr_byte STK sp0 FP bl0 blc ly own a \/ Exists (in_zr a) PST.
Proof.
intros E rs STK sp0 FP bl0 blc ly own HEI Usp H32 Hrs a (r & Hin & Ha).
destruct (Hrs r Hin) as [H | [(Eb & H1 & H2) | (Eb & H1 & H2)]]; [lia | |]; rewrite Eb in Ha; cbn [base_val] in Ha.
- left. unfold awr_byte. left. lia.
- right. apply ff_live_pst. rewrite (HEI (A_OBJ 9) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) in Ha.
  rewrite ff_live_val. cbn [pa_val PI_prog_A] in Ha. lia.
Qed.
Lemma ff_keep_run : forall (Wx : world SEGS) E rs (m m' : word -> option byte) sp0 a,
  frame_of E rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') -> img_env VAL A_LIM E ->
  bv_unsigned (ew E 2) = sp0 -> ff_rs_ok rs ->
  0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> ~ (LIVE <= a < LIVE + 8) ->
  aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E rs m m' sp0 a HF HEI Usp Hrs Ha H1 H2. apply (ff_aview_of_frame Wx E rs m m' a HF); [|exact Ha].
intros (r & Hin & Hr).
destruct (Hrs r Hin) as [H | [(Eb & L1 & L2) | (Eb & L1 & L2)]]; [lia | |]; rewrite Eb in Hr; cbn [base_val] in Hr.
- lia.
- rewrite (HEI (A_OBJ 9) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) in Hr.
  rewrite ff_live_val in H2. cbn [pa_val PI_prog_A] in Hr. lia.
Qed.
(* the stack pointer atom 2 through the engine's environment updates *)
Ltac ff_sp Usp :=
  first [ exact Usp
        | cbn [ew ewset havoc extK Nat.eqb Nat.ltb Nat.leb nth length Nat.add];
          rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by (cbv; lia); exact Usp ].
Ltac ff_wr Usp := apply ff_wr_lem; [eassumption | ff_sp Usp | rewrite ff_stk; lia | ff_rs].
Ltac ff_keep HFr K sp0 Usp :=
  lazymatch type of HFr with
  | frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?mA) (mrestrict _ ?mB) =>
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> ~ (LIVE <= a < LIVE + 8) ->
      aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a)
      by (intros a Ha H1 H2; apply (ff_keep_run Wx Ex rsx mA mB sp0 a HFr); [eassumption | ff_sp Usp | ff_rs | exact Ha | exact H1 | exact H2])
  end.

(* the p = 0 path: the frame is the only write window *)
Definition ff_rs0_ok (rs : smem) : Prop := forall r, In r rs ->
  YP09.r_whi r <= YP09.r_wlo r \/ (YP09.r_base r = Some 2%nat /\ -32 <= YP09.r_wlo r /\ YP09.r_whi r <= 0).
Ltac ff_rs0 :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; vm_compute in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; first [ left; lia | right; split; [reflexivity | lia] ] | ]);
  destruct Hr.
Lemma ff_keep_run0 : forall (Wx : world SEGS) E rs (m m' : word -> option byte) sp0 a,
  frame_of E rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  bv_unsigned (ew E 2) = sp0 -> ff_rs0_ok rs ->
  0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E rs m m' sp0 a HF Usp Hrs Ha H1. apply (ff_aview_of_frame Wx E rs m m' a HF); [|exact Ha].
intros (r & Hin & Hr).
destruct (Hrs r Hin) as [H | (Eb & L1 & L2)]; [lia |]; rewrite Eb in Hr; cbn [base_val] in Hr. lia.
Qed.
Ltac ff_keep0 HFr K sp0 Usp :=
  lazymatch type of HFr with
  | frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?mA) (mrestrict _ ?mB) =>
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a)
      by (intros a Ha H1; apply (ff_keep_run0 Wx Ex rsx mA mB sp0 a HFr); [ff_sp Usp | ff_rs0 | exact Ha | exact H1])
  end.

Section f.
Variable B : asyms.
(* the allocator relation of the walk (S1KitAlloc's ARxs, YGcallcf.v): ARcf with the error-buffer extents placed *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).

(* ---- Section hypotheses: the callee texts and the marked stand-ins ---- *)
(* callee text: the free wrapper, primed (a free re-hides shadow, so the run ends at wle' segs RZ_cf), with the memnorm
   keep at the leaf (YGcfMallocComposeKeep.v) *)
Hypothesis AFREE : YGcfMallocComposeKeep.afree_realizes_cf_rh_keep SEGS B.
(* callee text: __asan_unpoison_memory_region at the second allocator (h-rw-man-5, YGcfHp.v) *)
Hypothesis AUNPOISON : aunpoison_realizes_cf SEGS B.
(* STAND-IN for the unit's image binding of B (TfibSyms analogue; owner a Theorem Labs lane), proved once by the final instance *)
Hypothesis PAL : PALib (rc := rc) (L := A_prog_listing) (PI := PA) B.
(* STAND-IN for the unit's image binding of B (TfibSyms analogue; owner a Theorem Labs lane), proved once by the final instance *)
Hypothesis pal_pst_ok : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* STAND-IN for the unit's TFIB symbol binding of B (image binding, no state; the instance's TfibB_syms): errno's
   place, apart from the read-only ranges of the call memory's arodata_ok_cf (CfAroPresetA.errno_relro_preset_A) *)
Hypothesis TB : AF0m.TfibSyms B.

(* the allocator's laws: h-mani-a8's AR_laws_ok_cf (YG0lawscf.v), at YGcallcf's bridge *)
Let LAWS_cf : AR_laws_cf SEGS B := AR_laws_ok_cf SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B LAWS_cf.
Let OWNLOW := ARx_owned_low_law_xs SEGS B LAWS_cf.
Let WFL := ARx_wf_law_xs SEGS B.

Let AUNPOISONx : aunpoison_realizes_x SEGS B ARcfx cf_head cf_pc_unpoison := aunpoison_realizes_cf_xs SEGS B AUNPOISON.
Lemma ff_pst_ok : forall a, Exists (in_zr a) PST -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
Proof. intros a Ha. split; [exact (pst_in_img_A a Ha) | exact (proj1 (pal_pst_ok a Ha))]. Qed.
(* alloc.c's statics are no byte the call memory's arodata_ok_cf covers: each such byte is a read-only image byte
   (RELRO, or a report read inside a non-writable segment, CfAroPresetA.ro_reads_nw_preset_A), and no static is one
   (S1ImgA.pst_not_ro_A) *)
Lemma ff_pst_aro : forall a, aro_addr_cf a -> ~ Exists (in_zr a) PST.
Proof.
intros a Ha Hx. apply (pst_not_ro_A a Hx). destruct Ha as [Ha | Ha].
- right. unfold PAImg_prog.A_prog_relro_lo, PAImg_prog.A_prog_relro_hi. cbv [cf_relro_lo cf_relro_hi CfImg_A] in Ha.
  exact Ha.
- left. pose proof CfAroPresetA.ro_reads_nw_preset_A as RONW.
  unfold YGcfAroBridge.ro_reads_nw_t in RONW. rewrite Forall_forall in RONW.
  apply Exists_exists in Ha as (r & Hr & Hra). unfold in_zr in Hra.
  destruct (RONW r Hr) as (_ & sg & Hin & NW & L & R). exists sg. split; [exact Hin|]. split; [exact NW | lia].
Qed.
Let RUN := paj_run_x_m (SK := SK) (L := A_prog_listing) (PL := PL) (PI := PA) B PST ARcfx LAWS ff_pst_ok.
(* the same runner carrying the memnorm keep from a fixed memory m0 (h-hpreset-7's carrier, YSRrMemnorm.v:40) *)
Let RUNM (m0 : word -> option byte) := paj_run_x_m_inv (SK := SK) (L := A_prog_listing) (PL := PL) (PI := PA) B PST
  ARcfx LAWS ff_pst_ok (fun m => YAkMemnorm.memnorm SEGS m0 -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) m0 (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
(* the same runner over the walk's world relation wle' segs RZ_cf (the free re-hides shadow) *)
Let RUNMR (m0 : word -> option byte) := paj_run_x_m_invR (SK := SK) (L := A_prog_listing) (PL := PL) (PI := PA) B PST
  ARcfx LAWS ff_pst_ok (fun m => YAkMemnorm.memnorm SEGS m0 -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) m0 (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS))
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).
Let BR := paj_branch (L := A_prog_listing) (PI := PA).
Let RET := paj_ret_at (L := A_prog_listing) (PL := PL) (PI := PA).

(* a block lies off the image range (S1ReallocA's ra_blk_off_img: ALedger_cf's image cover and the client law) *)
Lemma ff_blk_off_img : forall ly S Hp (W : world SEGS) mem md b n, ARcfx ly S Hp W mem md -> In (b, n) (ablocks B ly S) ->
  b + req_size n <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= b.
Proof.
intros ly S Hp W mem md b n HAR Hin. pose proof HAR as ((_ & LG & _) & _).
pose proof (alc_img _ _ _ _ LG Asan.Asan_segment_000 ltac:(left; reflexivity)) as [C1 _].
pose proof (alc_img _ _ _ _ LG Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ C2].
cbn in C1, C2.
pose proof (proj1 (Forall_forall _ _) (prh_ablocks_nonneg_cf (PA := PA) B ly S Hp W mem md (proj1 HAR)) _ Hin) as Hn0.
cbn [snd] in Hn0.
assert (Hr0 : 0 < req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
destruct (Z.le_gt_cases (b + req_size n) YImgTop.IMG_LO) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases YImgTop.IMG_TOP b) as [|H2]; [right; lia|]. exfalso.
destruct (alx_client_img _ _ _ LAWS ly S Hp W mem md (Z.max b YImgTop.IMG_LO) HAR) as [Hn _];
  [left; exists b, n; split; [exact Hin | unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia] |].
apply Hn. unfold in_zr. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. lia.
Qed.

(* ---- entry ---- *)
Lemma ff_entry1 : forall ly S Hp (W : world SEGS) regs mem md ch p k live peak cnt fail ran most own,
  afn_pre_x SEGS B ARcfx STK_fuzz_free ly S Hp W regs mem md ch ->
  getr regs 10 = w64 p -> In (p - 16, k + 16) (ablocks B ly S) -> 0 <= k ->
  val_mem SEGS (mrestrict (w_H W) mem) (p - 16) 8 k ->
  prh_glob (PA := PA) W mem live peak cnt fail ran most own ->
  st_ok_pi SEGS VAL (FF_E regs [SHADOW_OFF; live; k]) ss_ff
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + FF_PC)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS FF_Bx [] (FF_E regs [SHADOW_OFF; live; k]) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch p k live peak cnt fail ran most own HPRE H10 Hin Hk Hhd HG.
pose proof HPRE as ([HAR HXS] & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof ff_stk as WS.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct HG as (Mlive & Mpeak & Mcnt & Mfail & Mran & Mmost & Mown & Rl & Rp & Rc & Rf & Rr).
rewrite ff_live_val in Mlive.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (p - 16) (k + 16) (conj HAR HXS) Hin) as (Hb16 & Hb4096 & Hbceil & Happ & Hbpres & _).
assert (Hreq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
rewrite Hreq in Hbceil, Happ, Hbpres.
destruct (alc_const _ _ LAWS_cf ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B PAL), (pal_cell B PAL) in Kgot. rewrite (pal_cell B PAL) in Kcell.
pose proof (pal_got_cell B PAL) as HgcD.
pose proof (ff_blk_off_img ly S Hp W mem md (p - 16) (k + 16) (conj HAR HXS) Hin) as Hoff. rewrite Hreq in Hoff.
assert (Hobj : forall j, (j < 39)%nat -> YImgTop.IMG_LO <= VAL (A_OBJ j) /\ VAL (A_OBJ j) + 8 <= YImgTop.IMG_TOP)
  by (intros j Hj; exact (pa_obj_img j Hj)).
rewrite restrict_mkst_fx.
set (E := FF_E regs [SHADOW_OFF; live; k]).
destruct (FF_E_extra regs live k) as (E32 & E33 & E34). fold E in E32, E33, E34.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (FF_E_reg _ _ 2 2%bv eq_refl); reflexivity).
assert (Up : bv_unsigned (ew E 10) = p)
  by (subst E; rewrite (FF_E_reg _ _ 10 10%bv eq_refl), H10; apply unsigned_lit_small; lia).
assert (Uimg : forall j, (A_TEXT <= j < A_LIM)%nat -> bv_unsigned (ew E j) = VAL j) by (intros j Hj; subst E; apply FF_E_img; exact Hj).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold FF_E; apply Eimg_env).
assert (Dv : forall (x : nat) v, ew E x = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff x 0) = Z_to_bv 64 v).
{ intros x v Hx Hv. cbn [sv_denot]. rewrite Hx, Z.add_0_r, unsigned_lit_small by exact Hv. reflexivity. }
assert (Di : forall j, (A_TEXT <= j < A_LIM)%nat -> sv_denot E (SOff j 0) = Z_to_bv 64 (VAL j)).
{ intros j Hj. cbn [sv_denot]. rewrite Uimg by exact Hj. rewrite Z.add_0_r. reflexivity. }
assert (BV : forall j, (A_TEXT <= j < A_LIM)%nat -> base_val E (Some j) = VAL j) by (intros j Hj; cbn [base_val]; apply Uimg; exact Hj).
split.
- unfold ss_ff. apply pa_entry_st_ok_full.
  + subst E. unfold FF_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ff_regions, stack_region, got_regionP, bcell_regionP, ff_live, ff_head.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    rewrite ?BV by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
    * pose proof (pa_val_range (A_OBJ 0)). pose proof (pa_val_range (A_OBJ 12)).
      split; [lia|]. split; [rewrite ?ff_val; ff_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [apply Di; unfold A_OBJ, A_TEXT, A_LIM; lia | lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * pose proof (pa_val_range (A_OBJ 12)).
      split; [lia|]. split; [rewrite ?ff_val; ff_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 32 0) SHADOW_OFF);
      [apply Dv; [exact E32 | unfold SHADOW_OFF; lia] | unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * pose proof (pa_val_range (A_OBJ 9)).
      split; [lia|]. split; [rewrite ?ff_val; ff_lits; lia|].
      split; [intros q Hq; apply pst_writable_A; apply ff_live_pst; rewrite ff_live_val; rewrite <- ff_val; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 33 0) live); [apply Dv; [exact E33 | lia] | lia | lia |].
      rewrite Z.add_0_r. exact Mlive.
    * cbn [base_val]. rewrite Up. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p (-16) 8 (SOff 34 0) k); [apply Dv; [exact E34 | lia] | lia | lia |].
      replace (p + -16) with (p - 16) by lia. exact Hhd.
  + unfold ff_regions, stack_region, got_regionP, bcell_regionP, ff_live, ff_head.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite ?BV by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    cbn [base_val]. rewrite Usp, Up. rewrite !Uimg by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    pose proof (Hobj 0%nat ltac:(lia)) as I0. pose proof (Hobj 12%nat ltac:(lia)) as I12.
    pose proof (Hobj 9%nat ltac:(lia)) as I9.
    rewrite !ff_val in I0, I12, I9. rewrite ?ff_val in HgcD |- *.
    ff_lits.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  + split; [|split; [exact I | exact (A_alias_hints_ok E HEI)]].
    unfold ff_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Up, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Uimg by (unfold A_OBJ, A_TEXT, A_LIM; lia). cbn [pa_val PI_prog_A].
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hp16 : p mod 16 = 0) by (replace p with ((p - 16) + 1 * 16) by lia; rewrite Z.mod_add by lia; exact Hb16).
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
- unfold sh_ok. apply Forall_nil.
Qed.

Lemma ff_entry0 : forall ly S Hp (W : world SEGS) regs mem md ch,
  afn_pre_x SEGS B ARcfx STK_fuzz_free ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (FF_E regs []) ss_ff0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + FF_PC)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS FF_Bx [] (FF_E regs []) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof ff_stk as WS.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
rewrite restrict_mkst_fx.
set (E := FF_E regs []).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (FF_E_reg _ _ 2 2%bv eq_refl); reflexivity).
split.
- unfold ss_ff0. apply pa_entry_st_ok_full.
  + subst E. unfold FF_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
  + exact (conj I I).
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16. repeat match goal with |- _ /\ _ => split end; try lia; exact I.
- unfold sh_ok. apply Forall_nil.
Qed.

(* a harness head lies in its block, below the allocator ceiling *)
Lemma ff_head_range : forall ly S Hp W mem md Lam peak cnt fail ran most own a k i,
  ARcfx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam -> 0 <= i < 8 ->
  4096 <= a - cf_head + i < alloc_ceiling.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k i HAR HL Hin Hi.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL Hin) as (Hk & Hb & _).
destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hb) as (_ & H4096 & Hceil & _).
rewrite ff_cf_head in *. unfold req_size in Hceil. destruct (k + 16 =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. lia.
Qed.

(* ---- p = 0: the frame, beqz taken, the epilogue, ret ---- *)
Lemma ff_p0 : forall ly S Hp W regs mem md ch Lam peak cnt fail ran most own,
  afn_pre_x SEGS B ARcfx STK_fuzz_free ly S Hp W regs mem md ch ->
  getr regs 10 = w64 0 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr SEGS W (cfg_at SEGS (SIGMA AS_fuzz_free) regs mem md)
    (fpost B ARcfx SK STK_fuzz_free [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       S' = S /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\ prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem'))).
Proof.
intros ly S Hp W regs mem md ch Lam peak cnt fail ran most own HPRE H10 HL.
destruct (ff_entry0 ly S Hp W regs mem md ch HPRE) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARcfx _ [] ly S Hp W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof ff_stk as WS.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
remember (FF_E regs []) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold FF_E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (FF_E_reg _ _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (FF_E_reg _ _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; exact (FF_E_reg _ _ 10 10%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [])) E) by (subst E; apply FF_E_agree).
clear HE.
unfold cfg_at. change (w64 (SIGMA AS_fuzz_free)) with (Z_to_bv 64 (BASE + FF_PC)).
(* the frame and the saves; stop at beqz a0 *)
pose proof (fun H : YAkMemnorm.memnorm SEGS mem => H) as HPM.
paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM FF_Bspan; [ff_wr Usp |].
clear HF HG. ff_keep0 HFr KA (spZ regs) Usp. clear HFr.
psrr_branch_tok RUN BR HS SHOK FF_Bspan.
2:{ (* beqz not taken: a0 is 0 *)
  exfalso. rewrite branch_eq_U, (U_atom E 10 0), U_SLit in Hc by (first [rewrite E10, H10; reflexivity | lia]).
  vm_compute in Hc. discriminate Hc. }
(* the epilogue; stop at ret *)
paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM FF_Bspan; [ff_wr Usp |].
clear HF HG. ff_keep0 HFr KB (spZ regs) Usp. clear HFr.
prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold fpost, apost_base_x.
eexists ly, S, Hp, _, _, _, 0.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARcfx LAWS (@pa_segs_low _ A_prog_listing PI_prog_A)); exact HJ|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [|exact HPM].
lazymatch goal with |- prh_ledger _ _ _ _ _ ?mT _ _ _ _ _ _ _ =>
  assert (KS : forall a, 0 <= a < spZ regs - 32 -> aview SEGS (w_H W) mT a = aview SEGS (w_H W) mem a)
    by (intros a Ha; cbn [ms_mem]; rewrite (KB a ltac:(lia) ltac:(lia)); exact (KA a ltac:(lia) ltac:(lia))) end.
apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W); [exact HL | | | | apply Permutation_refl].
- intros a Ha. pose proof (ff_pst_range a Ha) as Hr. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hr. apply KS. lia.
- intros a k0 i Hin Hi. pose proof (ff_head_range ly S Hp W mem md Lam peak cnt fail ran most own a k0 i HAR HL Hin Hi).
  apply KS. lia.
- intros a k0 _ H. exact H.
Qed.

(* the engine's region of g_live at a stop, and its one chunk, read off the state (never typed) *)
Ltac ff_pick_live rs :=
  let j9 := eval vm_compute in (A_OBJ 9) in
  lazymatch rs with
  | (YP09.mkRegion (Some ?j) ?lo ?hi ?wlo ?whi ?cs) :: ?t =>
    tryif constr_eq j j9 then constr:(YP09.mkRegion (Some j) lo hi wlo whi cs) else ff_pick_live t
  end.

(* ---- p <> 0: unpoison the head (Hp loses p - 16), g_live -= k, the frame popped, the tail jump to the free
   wrapper with a0 = p - 16 and the entry ra; over wle' segs RZ_cf (the primed free re-hides shadow). The memnorm
   keep: the runners' carrier to the tail call, then the keep rule's last conjunct across the free ---- *)
Lemma ff_live_arm : forall ly S Hp W regs mem md ch p n Lam peak cnt fail ran most own l1 l2,
  fpre (L := A_prog_listing) (PA := PA) B ARcfx STK_fuzz_free ly S Hp W regs mem md ch ->
  YGcfRoomLive.room_live_cf S -> YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  PresetHullBudget.hull_budget S [] ->
  admits (as_universe B) (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S ->
  getr regs 10 = w64 p -> Lam = l1 ++ (p, n) :: l2 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (cfg_at SEGS (SIGMA AS_fuzz_free) regs mem md)
    (fpostb (L := A_prog_listing) (PA := PA) B ARcfx SK
       (YCbqGwild.wbudget [call_trace ly (pc_free_ra0 (as_code B)) regs ch] 0) STK_fuzz_free (ablocks_fp [(p - cf_head, n + cf_head)])
       regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' => YGcfRoomLive.room_live_cf S' /\
          Hp' = remove Z.eq_dec (p - cf_head) Hp /\
          (exists b1 b2, ablocks B ly S = b1 ++ (p - cf_head, n + cf_head) :: b2 /\ ablocks B ly' S' = b1 ++ b2) /\
          (* the run position across this free (the HFr and HBulk events of tfuzz_free_specX's arms) *)
          (forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
             nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HFr (n + cf_head)) ->
             exists hist', PresetRoomPos.iface_room_pos sm x os (Datatypes.S i) H0 hist' S') /\
          (forall sm x os i L k H0 hb, nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HBulk L) ->
             nth_error L k = Some (n + cf_head) ->
             PresetRoomPosKeep.iface_room_pos_bulk sm x os i L k H0 hb S ->
             exists hb', PresetRoomPosKeep.iface_room_pos_bulk sm x os i L (Datatypes.S k) H0 hb' S') /\
          YGcfRoomLive.ccnt24 S' + Z.of_nat (PresetRoom.ccnt YG00.kBatchClass [n + cf_head]) = YGcfRoomLive.ccnt24 S /\
          PresetHullBudget.hull_used S S' [] /\
          (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem') /\
          prh_ledger B ly' S' Hp' W' mem' (l1 ++ l2) peak cnt fail ran most own)).
Proof.
intros ly S Hp W regs mem md ch p n Lam peak cnt fail ran most own l1 l2 [HPRE HRO] HRLV H24 HHUL HTR H10 HLam HL.
pose proof (@pa_segs_low _ A_prog_listing PI_prog_A) as Hsegs.
pose proof ff_stk as WS. pose proof ff_cf_head as Hcf.
assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
pose proof HL as HL0'. pose proof HL as HL0. apply prh_ledger_iff in HL0 as [HGL HLB].
pose proof HGL as (Glive & Gpeak & Gcnt & Gfail & Gran & Gmost & Gown & Rlp & Rpk & Rcnt & Rfail & Rran).
pose proof HLB as (HND & HFA & HPERM).
assert (HinL : In (p, n) Lam) by (rewrite HLam; apply in_or_app; right; left; reflexivity).
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran p n most own HL HinL) as (Hn0 & Hblk & HinHp & Hp16 & Hhead).
rewrite Hcf in Hblk, HinHp, Hhead.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (p - 16) (n + 16) HAR Hblk) as (Hb16 & Hb4096 & Hbceil & Happ & Hbpres & _).
assert (Hreq : req_size (n + 16) = n + 16) by (unfold req_size; destruct (Z.eqb_spec (n + 16) 0); lia).
rewrite Hreq in Hbceil, Happ, Hbpres.
pose proof (ff_blk_off_img ly S Hp W mem md (p - 16) (n + 16) HAR Hblk) as Hoff. rewrite Hreq in Hoff.
set (live := Ledger.lsum Lam) in *.
assert (Hsum : live = Ledger.lsum (l1 ++ l2) + n) by (unfold live; rewrite HLam; apply prh_lsum_split).
assert (Hrest0 : 0 <= Ledger.lsum (l1 ++ l2)).
{ apply prh_lsum_nonneg. pose proof (prh_lblocks_sizes B ly S Hp W mem Lam HLB) as HS0.
  rewrite HLam in HS0. apply Forall_app in HS0 as [F1 F2]. apply Forall_inv_tail in F2.
  apply Forall_app. split; [exact F1 | exact F2]. }
destruct (ff_entry1 ly S Hp W regs mem md ch p n live peak cnt fail ran most own HPRE H10 Hblk Hn0 Hhead HGL) as [HS SHOK].
pose proof (ajournal_x_initR (SK := SK) SEGS B PST ARcfx (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_refl SEGS YGcfRehidePost.RZ_cf) STK_fuzz_free (ablocks_fp [(p - cf_head, n + cf_head)])
  ly S Hp W regs mem md ch HPRE) as HJ.
unfold cfg_at. change (w64 (SIGMA AS_fuzz_free)) with (Z_to_bv 64 (BASE + FF_PC)).
remember (FF_E regs [SHADOW_OFF; live; n]) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold FF_E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (FF_E_reg _ _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (FF_E_reg _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (FF_E_reg _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (FF_E_reg _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; exact (FF_E_reg _ _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; exact (FF_E_reg _ _ 10 10%bv eq_refl)).
destruct (FF_E_extra regs live n) as (E32 & E33 & E34). rewrite <- HE in E32, E33, E34.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Up : bv_unsigned (ew E 10) = p) by (rewrite E10, H10; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; live; n])) E) by (subst E; apply FF_E_agree).
clear HE.
(* stretch 1: the frame and the saves, beqz decided by p's fact (p >= 4112), the shadow base, s0 = p - 16, the
   unpoison arguments; stop at the call *)
pose proof (fun H : YAkMemnorm.memnorm SEGS mem => H) as HPM.
paj_run_tok_x_inv (RUNMR mem) HS HJ SHOK HPM FF_Bspan; [ff_wr Usp |].
clear HF HG. ff_keep HFr K1 (spZ regs) Usp. clear HFr.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
eapply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
{ apply (SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  eapply (YGcallMxmn.aj_unpoison_x_mR (SK := SK) SEGS B PST ARcfx cf_head LAWS Hsegs (wle' SEGS YGcfRehidePost.RZ_cf)
    (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf) cf_pc_unpoison AUNPOISONx
    W E _ _ STK_fuzz_free (spZ regs) (ablocks_fp [(p - cf_head, n + cf_head)]) ly S Hp W mem md [] ly S Hp _ 0
    (p - 16) (n + 16) (-32) (ew E 2) _ HS).
  - cbn [ss_pc setpc]. exact ff_unpoison_pc.
  - reflexivity.
  - exact HJ.
  - rewrite Ra0, Up. first [reflexivity | unfold w64; f_equal; lia].
  - rewrite Ra1. reflexivity.
  - reflexivity.
  - exact HinHp.
  - exact Hblk.
  - rewrite Hreq, Hcf. lia.
  - exact (st_ok_restrict_reg SEGS (w_H W) E _ _ 2%bv HS).
  - reflexivity.
  - exact Usp.
  - reflexivity.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite Rgp, E3. exact Hgp.
  - rewrite Rtp, E4. exact Htp.
  - exact Rra.
  - apply (ret_ok_codeptr_v (L := A_prog_listing) (PI := PA)); [lia | reflexivity]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hshd & Hkeep & Hpres2 & Hmn2).
pose proof (fun H0 => Hmn2 (HPM H0)) as HPM2. clear HPM Hmn2. rename HPM2 into HPM.
rewrite Hcf in Hshd, Hkeep. change (16 / 8) with 2 in Hkeep.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
assert (Hshb : SHADOW_OFF <= shadow_addr (p - 16) /\ shadow_addr (p - 16) + 2 <= SHADOW_OFF + alloc_ceiling / 8 + 2).
{ unfold shadow_addr. pose proof (Z.div_pos (p - 16) 8 ltac:(lia) ltac:(lia)).
  assert ((p - 16) / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia). lia. }
assert (Hacd : alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 16) by (apply Z.div_le_upper_bound; lia).
unfold SHADOW_OFF in Hshb.
(* back at the return slot: all five regions are kept by the unpoison *)
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  pose proof (pa_obj_img (L := A_prog_listing) (PAImg := PA) 0%nat ltac:(lia)) as I0.
  pose proof (pa_obj_img (L := A_prog_listing) (PAImg := PA) 12%nat ltac:(lia)) as I12.
  pose proof (pa_obj_img (L := A_prog_listing) (PAImg := PA) 9%nat ltac:(lia)) as I9.
  pose proof Happ as Happ'. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ'.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
  - apply (ff_kept_gen E _ _ 2 (spZ regs)); [exact Usp | |].
    + intros a Ha. apply prh_mbyte_of_aview. apply Hkeep; lia.
    + intros a Ha. apply (apresent_writable SEGS). apply HJpres2. lia.
  - apply (ff_kept_gen E _ _ (A_OBJ 0) (VAL (A_OBJ 0))); [apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia | | intros a Ha; lia].
    intros a Ha. apply prh_mbyte_of_aview. apply Hkeep; ff_lits; lia.
  - apply (ff_kept_gen E _ _ (A_OBJ 12) (VAL (A_OBJ 12))); [apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia | | intros a Ha; lia].
    intros a Ha. apply prh_mbyte_of_aview. apply Hkeep; ff_lits; lia.
  - apply (ff_kept_gen E _ _ (A_OBJ 9) (VAL (A_OBJ 9))); [apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia | |].
    + intros a Ha. apply prh_mbyte_of_aview. apply Hkeep; ff_lits; lia.
    + intros a Ha. apply pst_writable_A. apply ff_live_pst. rewrite ff_live_val. rewrite <- ff_val. lia.
  - apply (ff_kept_gen E _ _ 10 p); [exact Up | | intros a Ha; lia].
    intros a Ha. apply prh_mbyte_of_aview. apply Hkeep; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 48 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E')
  by (rewrite HE'; apply (img_env_havoc (L := A_prog_listing) (PI := PA)); [exact HEI | cbv; lia]).
assert (OLD : forall k, (k < 48)%nat -> ew E' k = ew E k) by (intros k Hk; rewrite HE'; apply YN3v.ew_havoc_old; exact Hk).
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; live; n])) E')
  by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE'.
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite (OLD 2%nat ltac:(lia)); exact Usp).
assert (Up' : bv_unsigned (ew E' 10) = p) by (rewrite (OLD 10%nat ltac:(lia)); exact Up).
(* the head's shadow entry: its 16 bytes read shadow 0 after the unpoison *)
assert (SHOK' : sh_ok SEGS FF_Bx ff_SH1 E' (mrestrict (w_H W) mem2)).
{ unfold sh_ok, ff_SH1. apply Forall_cons; [|apply Forall_nil].
  assert (UB : U E' FF_Bx = SHADOW_OFF)
    by (unfold FF_Bx; apply U_atom; [rewrite (OLD 32%nat ltac:(lia)); exact E32 | unfold SHADOW_OFF; lia]).
  assert (UP : U E' (SOff 10 0) = p) by (apply U_atom; [rewrite (OLD 10%nat ltac:(lia)), E10, H10; reflexivity | lia]).
  unfold shent_ok, app_apart, range_addressable. cbn [she_m she_lo she_hi]. rewrite UB, UP. split.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    rewrite <- (aview_rd_of SEGS). change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). apply Hshd. lia.
  - intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia. }
clear SHOK.
(* stretch 3: the two head checks (folded), the head word, g_live -= k, the epilogue; stop at the tail jump *)
paj_run_tok_x_inv (RUNMR mem) HS HJ2 SHOK' HPM FF_Bspan; [ff_wr Usp' |].
clear HF HG. ff_keep HFr K3 (spZ regs) Usp'. clear HFr.
(* at the tail jump: a0 = p - 16, sp / ra / s0 back at their entry values *)
prreg HS (10%bv : bv 5) T10. prreg HS (2%bv : bv 5) T2. prreg HS (1%bv : bv 5) T1.
prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msc) => set (msT := msc) in * end.
assert (HspT : spZ (ms_regs msT) = spZ regs) by (unfold spZ at 1; rewrite T2, (OLD 2%nat ltac:(lia)), E2; reflexivity).
assert (HraT : getr (ms_regs msT) 1 = getr regs 1) by (rewrite T1, (OLD 1%nat ltac:(lia)), E1; reflexivity).
assert (Hs0T : getr (ms_regs msT) 8 = getr regs 8) by (rewrite T8, (OLD 8%nat ltac:(lia)), E8; reflexivity).
(* the memory at the tail: off the frame and the unpoison's window, g_live and the head's two shadow bytes, the entry's *)
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 - 4096 <= a < spZ regs) -> ~ (LIVE <= a < LIVE + 8) ->
  ~ (shadow_addr (p - 16) <= a < shadow_addr (p - 16) + 2) -> aview SEGS (w_H W) (ms_mem msT) a = aview SEGS (w_H W) mem a).
{ intros a Ha H1 H2 H3. rewrite (K3 a Ha ltac:(lia) H2). rewrite (Hkeep a Ha ltac:(rewrite Hes; lia) H3).
  exact (K1 a Ha ltac:(lia) H2). }
(* g_live at the tail: live - n, off the engine's last state *)
pose proof (st_ok_mem_ok SEGS E' _ _ HS) as (_ & HMO & _). cbn [ss_mem setpc ms_mem restrict] in HMO.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HMO)))) as HRL. clear HMO.
assert (HUe : U E' (SAlu ALU_SUB (SOff 33 0) (ff_hdr_sv 34)) = live - n).
{ rewrite U_SAlu, ff_hdr_U. rewrite (U_atom E' 33 live) by (first [rewrite (OLD 33%nat ltac:(lia)), E33; reflexivity | lia]).
  rewrite (OLD 34%nat ltac:(lia)), E34, unsigned_lit_small by lia. cbn [zalu_raw]. unfold zcanon, M64. apply Z.mod_small. lia. }
pose proof (ff_chunk_val E' _ (A_OBJ 9) 0 8 0 8 _ 0 8 (SAlu ALU_SUB (SOff 33 0) (ff_hdr_sv 34)) (live - n) HRL
  ltac:(left; reflexivity) ltac:(apply bv_eq; rewrite unsigned_lit_small by lia; exact HUe) ltac:(cbn; lia) ltac:(cbn; lia)) as HvT.
rewrite (HEI' (A_OBJ 9) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) in HvT.
change (N.to_nat 8) with 8%nat in HvT. replace (VAL (A_OBJ 9) + 0) with LIVE in HvT by (rewrite ff_live_val; reflexivity).
(* the tail call's trace: the text's admitted trace at the tail call's registers (the same trace: sp, ra, s0 kept) *)
assert (ECT : call_trace ly (pc_free_ra0 (as_code B)) (ms_regs msT) ch = call_trace ly (pc_free_ra0 (as_code B)) regs ch).
{ unfold call_trace, frame0_ok, raZ, s0Z. rewrite HspT, HraT, Hs0T. reflexivity. }
assert (HTRT : admits (as_universe B) (call_trace ly (pc_free_ra0 (as_code B)) (ms_regs msT) ch) S)
  by (rewrite ECT; exact HTR).
(* the call memory QMm_cf at the tail call: the room from room_live_room, cf_hull_ok from the text's budget
   (PresetHullPay.hull_ok_of_budget), arodata_ok_cf from the entry's reader form through the journal to the tail
   (arodata_ok_cf_of_journal_P at image A's rows; its footprint, the freed block, opens no sink) *)
assert (HAROT : arodata_ok_cf SEGS B (ms_mem msT)).
{ apply (arodata_ok_cf_of_journal_P (SK := SK) SEGS B PST ARcfx (wle' SEGS YGcfRehidePost.RZ_cf)
    STK_fuzz_free (spZ regs) (ablocks_fp [(p - cf_head, n + cf_head)]) ly S Hp W mem md [] ly S
    (remove Z.eq_dec (p - 16) Hp) W (ms_mem msT) _ 0 [] HJ2
    CfAroPresetA.relro_seg_preset_A (CfAroPresetA.errno_relro_preset_A B TB)
    CfAroPresetA.relro_top_preset_A CfAroPresetA.ro_reads_nw_preset_A ff_pst_aro).
  - apply YCbq.sink_closed_ablocks_fp. constructor; [cbn [fst]; lia | constructor].
  - exact (proj1 HRO). }
assert (HQM : QMm_cf SEGS B S (ms_mem msT)).
{ destruct (QM_cf_of_room SEGS B ly S Hp W mem md (proj1 HAR) HQT (YGcfRoomLive.room_live_room S HRLV)
    (PresetHullPay.hull_ok_of_budget S [] HHUL)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 HAROT)))))). }
(* the tail call of the free wrapper, primed, with the keep (YGcallMxmnKeep's aj_free_x_ct_m_rh_keep at o = 0, the
   entry ra) *)
eapply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
{ eapply (YGcallMxmnKeep.aj_free_x_ct_m_rh_keep (SK := SK) SEGS B PST LAWS Hsegs (pal_env B PAL) OWNLOW WFL
    (alloc_model_laws_x_cf B (universe_ok_of_ARcf SEGS B ly S Hp W mem md (proj1 HAR)))
    AFREE W E' _ msT STK_fuzz_free (spZ regs) (ablocks_fp [(p - cf_head, n + cf_head)]) ly S Hp W mem md
    [] ly S (remove Z.eq_dec (p - 16) Hp) _ 0 (p - 16) (n + 16) 0 (ew E' 2) (getr regs 1) ch HS (pal_free B PAL) eq_refl HJ2).
  - exact Hblk.
  - apply prh_hp_remove_notin.
  - rewrite T10, Up'. first [reflexivity | unfold w64; f_equal; lia].
  - exact (st_ok_restrict_reg SEGS (w_H W) E' _ _ 2%bv HS).
  - reflexivity.
  - exact Usp'.
  - reflexivity.
  - lia.
  - rewrite WS, Has. lia.
  - rewrite T3, (OLD 3%nat ltac:(lia)), E3. exact Hgp.
  - rewrite T4, (OLD 4%nat ltac:(lia)), E4. exact Htp.
  - exact HraT.
  - exact Hra.
  - exact HQM.
  - apply (achain_chain_pre ly _ (spZ regs) (s0Z regs) ch).
    + apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
      intros a Ha. apply KT; [lia | lia | | ].
      * rewrite ff_live_val. ff_lits. lia.
      * unfold SHADOW_OFF in *. lia.
    + rewrite HspT. lia.
    + unfold s0Z. rewrite Hs0T. reflexivity.
    + unfold raZ. rewrite HraT. exact Hra4.
  - exact HTRT.
  - intros _ i Hi. exists (p - 16, p - 16 + req_size (n + 16)). split; [left; reflexivity | cbn [fst snd]; lia]. }
cbv beta. intros W5 c5 Hwle5 (ly2 & S2 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & (b1 & b2 & Eb1 & Eb2) & Hfr5 & HPREc & Htrc &
  (q & trc & Hqa & Hqin & Hpath & Hgf & Hleaf) & HKEPT & Hmn5).
pose proof HKEPT as (Kc1 & Kc2 & Kc3 & _).
(* the journal is at the free's budget [call trace] (the rule's post, WS ++ [trace] at WS = []): the one trace this
   free can store, so wbudget [trace] 0 holds (YCbqGwild.wfresh_one_in) *)
apply (SRrG_ret SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf)).
unfold fpostb, YCbqGwild.apost_base_xbR.
exists ly2, S2, (remove Z.eq_dec (p - 16) Hp), regs5, mem5, md5, (0 + (st_nev S2 - st_nev S)),
  [call_trace ly (pc_free_ra0 (as_code B)) (ms_regs msT) ch].
split; [reflexivity|].
split; [unfold YCbqGwild.wbudget; rewrite ECT; rewrite YCbqGwild.wfresh_one_in by (left; reflexivity); lia|].
split; [exact HJ5|].
split; [eapply ff_apres_trans; [eapply (aregs_preserved_of_st_ok SEGS _ E' _ _ regs _ HS); [exact HAE' | vm_compute; reflexivity] | exact HP5]|].
split.
{ (* the room after the free: h-mani-a8's RL_free_step at L24 + DRV + 1, its batch-class bound from the named
     live-set premise (CfRoomLivePreset.preset_rl_b24_ok) *)
  exact (YGcfRoomLive.RL_free_step SEGS B ly S (remove Z.eq_dec (p - 16) Hp) W (ms_regs msT) (ms_mem msT) _ ch
    (PresetLiveBounds.L24 + PresetLiveBounds.DRV + 1) q _ trc (tt, S2)
    (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPREc) (CfRoomLivePreset.preset_rl_b24_ok S H24) HRLV Hpath). }
split; [reflexivity|].
split; [exists b1, b2; split; [exact Eb1 | exact Eb2]|].
assert (Hqn : q <> PNull) by (intros Eq; subst q; cbn in Hqa; lia).
split.
{ (* the run position, HFr: h-pre-b1's room_pos_keep_free at the tail call (the call's acall_pre_cf, trace, block
     and model path from aj_free_x_ct's post) *)
  intros sm x os i H0 hist Hpos He. rewrite Hcf in He. eexists.
  exact (PresetRoomPosKeep.room_pos_keep_free SEGS B ly S (remove Z.eq_dec (p - 16) Hp) W (ms_regs msT) (ms_mem msT) _ ch
    sm x os i H0 hist q (n + 16) _ trc S2 (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPREc) HTRT Hqin Hqn Hpath Hpos He). }
split.
{ (* the run position, HBulk: h-pre-b1's room_pos_keep_bulk_free at the tail call *)
  intros sm x os i L k H0 hb He Hk Hpos. rewrite Hcf in Hk. eexists.
  exact (PresetRoomPosKeep.room_pos_keep_bulk_free SEGS B ly S (remove Z.eq_dec (p - 16) Hp) W (ms_regs msT) (ms_mem msT) _ ch
    sm x os i L k H0 hb q (n + 16) _ trc S2 (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPREc) HTRT Hqin Hqn Hpath He Hk Hpos). }
(* the class-24 live count loses exactly this block's request (S1Ccnt24.v's prh_ccnt24_free) *)
split; [rewrite Hcf; exact (prh_ccnt24_free B ly S ly2 S2 b1 b2 (p - 16, n + 16) Eb1 Eb2) |].
(* the hull meters: the free keeps both (YGcfSecsStep.secs_free_step on the free's model path) *)
split; [exact (PresetHullBudget.hull_used_same S S2 [] (YGcfSecsStep.secs_free_step _ _ _ _ _ Hpath)) |].
(* the memnorm keep: the runners' carrier to the tail call's memory, then the free's own keep *)
split; [intros H0; exact (Hmn5 (HPM H0)) |].
(* the ledger without the freed block (S1Ledger's prh_ledger_disown) *)
assert (HKS : forall a, Exists (in_zr a) PST -> ~ (LIVE <= a < LIVE + 8) ->
  aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hl. pose proof (ff_pst_range a Ha) as Hr. destruct (pal_pst_ok a Ha) as [Ho Hr2].
  rewrite (Kc3 a (pst_in_img_A a Ha) Ho Hr2). apply KT; [unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hr; lia | unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hr; lia | exact Hl |].
  unfold YImgTop.IMG_LO, YImgTop.IMG_TOP, SHADOW_OFF in *. lia. }
assert (HKL : forall a, LIVE <= a < LIVE + 8 -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W) (ms_mem msT) a).
{ intros a Ha. pose proof (ff_live_pst a Ha) as Hx. destruct (pal_pst_ok a Hx) as [Ho Hr2].
  exact (Kc3 a (pst_in_img_A a Hx) Ho Hr2). }
assert (KSV : forall a w v, (a = pi_g_peak /\ w = 8%nat \/ a = pi_g_count /\ w = 8%nat \/ a = pi_g_fail /\ w = 8%nat \/
    a = pi_g_ran_out /\ w = 1%nat \/ a = pi_g_most /\ w = 8%nat \/ a = pi_g_own_ran_out /\ w = 1%nat) ->
  val_mem SEGS (mrestrict (w_H W) mem) a w v -> val_mem SEGS (mrestrict (w_H W5) mem5) a w v).
{ intros a w v Haw Hv0. apply (prh_val_mem_keep (L := A_prog_listing) (PA := PA) _ _ _ _ _ Hv0).
  intros k Hk. apply (prh_mbyte_of_aview (L := A_prog_listing) (PA := PA)).
  assert (Hx : Exists (in_zr (a + Z.of_nat k)) PST)
    by (unfold prh_pst; destruct Haw as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]];
        [ do 1 apply Exists_cons_tl; apply Exists_cons_hd
        | do 2 apply Exists_cons_tl; apply Exists_cons_hd
        | do 3 apply Exists_cons_tl; apply Exists_cons_hd
        | do 4 apply Exists_cons_tl; apply Exists_cons_hd
        | do 5 apply Exists_cons_tl; apply Exists_cons_hd
        | do 6 apply Exists_cons_tl; apply Exists_cons_hd ];
        unfold in_zr; cbn [fst snd]; ff_lits; lia).
  apply HKS; [exact Hx|]. destruct Haw as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]; ff_lits; lia. }
assert (HG5 : prh_glob (PA := PA) W5 mem5 (Ledger.lsum (l1 ++ l2)) peak cnt fail ran most own).
{ apply (prh_glob_final_le (L := A_prog_listing) (PA := PA) W mem W5 mem5 live peak cnt fail ran
    (Ledger.lsum (l1 ++ l2)) cnt fail ran most own HGL).
  - replace (Ledger.lsum (l1 ++ l2)) with (live - n) by lia.
    apply (prh_val_mem_keep (L := A_prog_listing) (PA := PA) _ _ _ _ _ HvT). intros k Hk.
    apply (prh_mbyte_of_aview (L := A_prog_listing) (PA := PA)). apply HKL. lia.
  - lia.
  - apply KSV; [left; split; reflexivity | exact Gpeak].
  - apply KSV; [right; left; split; reflexivity | exact Gcnt].
  - exact Rcnt.
  - apply KSV; [right; right; left; split; reflexivity | exact Gfail].
  - exact Rfail.
  - apply KSV; [right; right; right; left; split; reflexivity | exact Gran].
  - exact Rran.
  - destruct Gmost as [Gm Gmb]. split; [|exact Gmb].
    apply KSV; [right; right; right; right; left; split; reflexivity | exact Gm].
  - destruct Gown as [Go Gob]. split; [|exact Gob].
    apply KSV; [right; right; right; right; right; split; reflexivity | exact Go]. }
rewrite HLam in HL.
assert (HnotP : forall a ka, In (a, ka) (l1 ++ l2) -> a <> p).
{ intros a ka Hin Ea. subst a. rewrite HLam in HND. rewrite map_app in HND. cbn [map fst] in HND.
  apply NoDup_ListNoDup in HND.
  apply (NoDup_remove_2 _ _ _ HND). rewrite <- map_app. apply in_map_iff. exists (p, ka). split; [reflexivity | exact Hin]. }
assert (HinLam : forall a ka, In (a, ka) (l1 ++ l2) -> In (a, ka) Lam).
{ intros a ka Hin. rewrite HLam. apply in_app_or in Hin as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
apply (prh_ledger_disown B ly S Hp W mem ly2 S2 _ W5 mem5 l1 l2 p n peak cnt fail ran peak cnt fail ran most own HL HG5).
- intros a ka i Hin Hi.
  destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a ka most own HL0' (HinLam a ka Hin)) as (Hka & Hab & _).
  rewrite Hcf in Hab |- *.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (a - 16) (ka + 16) HAR Hab) as (_ & Ha4096 & Haceil & Haapp & _).
  assert (Hreqa : req_size (ka + 16) = ka + 16) by (unfold req_size; destruct (Z.eqb_spec (ka + 16) 0); lia).
  rewrite Hreqa in Haceil, Haapp.
  assert (Hne : (a - 16, ka + 16) <> (p - 16, n + 16)) by (intros Eq; injection Eq as Ea _; apply (HnotP a ka Hin); lia).
  pose proof (sep_blocks_x SEGS B ARcfx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hblk Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreqa, Hreq in Hd.
  pose proof (ff_blk_off_img ly S Hp W mem md _ _ HAR Hab) as Hoffa. rewrite Hreqa in Hoffa.
  apply (prh_mbyte_of_aview (L := A_prog_listing) (PA := PA)).
  rewrite (Kc2 (a - 16) (ka + 16) i Hab ltac:(rewrite Hreqa; lia) ltac:(cbv beta; rewrite Hreq; lia)).
  pose proof Haapp as Haapp'. unfold in_app, kLowShadowBeg, kHighMemBeg in Haapp'.
  apply KT; [lia | lia | |].
  + intros Hl. pose proof (ff_pst_range _ (ff_live_pst _ Hl)) as Hr. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. lia.
  + unfold SHADOW_OFF in *. lia.
- intros a ka Hin Hab. rewrite Eb2. rewrite Eb1 in Hab.
  apply in_app_or in Hab as [H|[H|H]]; [apply in_or_app; left; exact H | | apply in_or_app; right; exact H].
  exfalso. injection H as Ea _. apply (HnotP a ka Hin). rewrite ?Hcf in Ea. lia.
- reflexivity.
Qed.

Theorem fuzz_free_holds :
  tfuzz_free_specX (fx := fx) (rc := rc) (cp := CfParams_preset) (PI := prh_img_A)
    (RL := prh_room_live_a8 (cp := CfParams_preset)) (L := A_prog_listing) (PA := PI_prog_A) B ARcfx SK.
Proof.
unfold tfuzz_free_specX, fpostbm, fQmn.
intros most own ly S Hp W regs mem md ch p n Lam peak cnt fail ran HPRE HRL H24 HHUL HTR H10 HPL HL.
destruct (Z.eq_dec p 0) as [-> | Hpn].
- (* p = 0: the early return; S' = S keeps the room, the position, the bound and both hull meters. The walk is the
     plain one (no free), lifted to wle' segs RZ_cf *)
  cbn [Z.eqb]. destruct HPRE as [HPRE0 HRO].
  eapply (SRrG_mono SEGS (wle' SEGS YGcfRehidePost.RZ_cf));
    [exact (SRr_SRr' SEGS YGcfRehidePost.RZ_cf _ _ _
       (ff_p0 ly S Hp W regs mem md ch Lam peak cnt fail ran most own HPRE0 H10 HL)) |].
  (* a NULL free stores nothing: the budgeted post at WS = [] *)
  intros W' c' _ H. unfold fpost, apost_base_x in H. unfold fpostb, YCbqGwild.apost_base_xbR.
  destruct H as (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ' & HP' & ES & EHp & Eab & HL' & Hmn).
  exists ly', S', Hp', regs', mem', md', k, (@nil (list Z)). split; [exact Hc|]. split; [exact (le_n 0)|].
  split; [exact (ajournal_xwR_mono (SK := SK) SEGS B PST ARcfx (@wle SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
    (wle_wle' SEGS YGcfRehidePost.RZ_cf) STK_fuzz_free (spZ regs) [] ly S Hp W mem md [] ly' S' Hp' W' mem' md' k []
    HJ')|].
  split; [exact HP'|].
  split; [|exact Hmn]. subst S'.
  split; [intros Hc0; exfalso; exact (Hc0 eq_refl) |].
  split; [exact (PresetHullBudget.hull_used_refl S []) |].
  (* K1's post-implication at E = []: the position is kept (S' = S) *)
  split; [intros _ sm x os i H0 hist Hpos _; exists hist; cbn [length]; rewrite Nat.add_0_r; exact Hpos |].
  split; [intros Hc0; exfalso; exact (Hc0 eq_refl) |].
  split; [intros Hc0; exfalso; exact (Hc0 eq_refl) |].
  split; [intros Hb; exact Hb |].
  left. split; [reflexivity|]. split; [reflexivity|]. split; [exact EHp|]. split; [exact Eab | exact HL'].
- (* p <> 0: p is a member of the ledger *)
  destruct HPL as [-> | HinL]; [contradiction |].
  apply in_split in HinL as (l1 & l2 & HLam).
  replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hpn).
  eapply (SRrG_mono SEGS (wle' SEGS YGcfRehidePost.RZ_cf));
    [exact (ff_live_arm ly S Hp W regs mem md ch p n Lam peak cnt fail ran most own l1 l2 HPRE (HRL Hpn) (H24 Hpn)
       (HHUL Hpn) HTR H10 HLam HL) |].
  intros W' c' _ H. unfold fpostb, YCbqGwild.apost_base_xbR in *.
  destruct H as (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & Hbud & HJ' & HP' & HR & EHp & Hbl & HRP & HRB & Hc24 &
    HU & Hmn & HL').
  exists ly', S', Hp', regs', mem', md', k, WS. split; [exact Hc|]. split; [exact Hbud|]. split; [exact HJ'|].
  split; [exact HP'|].
  split.
  { split; [intros _; exact HR|].
    split; [exact HU|].
    split; [intros Hp0; contradiction |].
    (* K1's post-implications at E = [HFr (n + cf_head)] and at the bulk event: prh_run_at_one gives the run's event *)
    split; [intros _ sm x os i H0 hist Hpos He; apply prh_run_at_one in He;
            destruct (HRP sm x os i H0 hist Hpos He) as [h' Hh']; exists h'; cbn [length]; rewrite Nat.add_1_r; exact Hh' |].
    split; [intros _ sm x os i H0 L kL hb Hb He Hk; apply prh_run_at_one in He; exact (HRB sm x os i L kL H0 hb He Hk Hb) |].
    split; [intros Hb24; lia |].
    right. split; [exact Hpn|]. split; [exact EHp|]. split; [exact Hc24|]. split; [exact Hbl|].
    exists l1, l2. split; [exact HLam | exact HL']. }
  (* the keep across the free (fQmn of the text's fpostbm, PRH_Base.v): ff_live_arm's *)
  exact Hmn.
Qed.

End f.
End d.
