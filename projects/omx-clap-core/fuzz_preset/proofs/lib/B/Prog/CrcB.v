(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B' (asan-ubsan, #102 pin d663f82d7f48, unstripped twin c90d4fa54d43):
   the walk of check_reject_clean (#102 source fuzz_preset.c:538-555, body unchanged; B' 0x8208c, 21 instructions of
   the whole-program listing lib/B/Listing_prog.v c97cc46b3e13, no UBSan check branch) against the text
   tcheck_reject_clean_specX (lib/A/PRH_FnCheck.v:537, blob 9ecd8eb167c6, the #102 kit tip f97c8b2f046b:
   the ledger with `most own`, the five-conjunct fpre (raZ ceiling, frm_zero), the m-form post fpostm), proved VERBATIM at image B'
   (PI := prh_img_B, L := B_prog_listing, PA := PI_prog_B) and preset's CfParams (lib/A/CfParamsPreset.v), for ANY
   allocator relation ARx with its laws (AR_laws_x, YCbqG.v blob c3b5d0111037). Lane BCrs of h-rw-pre-5; relocated
   from the old-pin walk (B 0x8211c, donor e63efdd8558c) by lane CrcBp: relocation only (the instruction words
   are equal on both images, every pc-relative target the same symbol + offset).
   Modelled on c-omx-alloc's lib/B/Prog/FuzzStrdupB.v (an intrinsic call, a program call, the branches, the return).
   The code: the frame (16 bytes: ra, s0); `beqz a0` (rc == 0) to the abort tail; s0 = live; bcmp (doc, &empty, 56)
   through the wrapper (YGcallMxmn.v aj_bcmp_at_xm, the keep form); `bnez a0` to the abort tail; fuzz_alloc_live ()
   through its text (YCbqGcall.v aj_call_x); `bne a0, s0` to the abort tail; the epilogue and ret. Each abort branch
   is shown NOT taken: rc <> 0; doc's 56 bytes and `empty`'s are all zero (the text's src_rd; the read-only image
   bytes, through fpre's arodata_okP and the image fact cr_empty_ro, its guard for those 56 bytes); g_live is
   live. So the abort tail (B' 0x820d4 / 0x820d8) is unreachable and no refusal exit is stated.
   s0 holds live across fuzz_alloc_live: the call's frame-chain premise is met by live < alloc_ceiling
   (PRW_LiveBound.v prh_lsum_lt_ceiling). fpre's return-address ceiling at that call: the jal's return pc is slot 13
   of the listing (cr_ret_live_lt_ceil, PRW_StepKit.pa_slot_lt_ceil_b). The m-form post: memnorm is carried from the
   entry memory by YC1fPx.v's paj_run_x_inv (YSRrMemnorm.srr_inv_laws_imp), across bcmp by aj_bcmp_at_xm's keep and
   across fuzz_alloc_live by its text's fpostm.
   Numerals: 16 (LENGTH: the frame, `addi sp, sp, -16`); 56 (LENGTH: sizeof (struct pj), `li a2, 56`); 0x10fc0
   (DERIVED: `empty`'s offset from the listing atom A_OBJ 2, the PAddHi slot of lib/B/Listing_prog.v:645); 52 (DERIVED:
   4 * 13, the slot after the jal to fuzz_alloc_live); 8 (LENGTH: a granule); 2 ^ 31, 2 ^ 32, 2 ^ 40, 2 ^ 44, 2 ^ 46,
   2 ^ 47, 2 ^ 63, 2 ^ 64 (DERIVED: int range, slot range, shadow and stack bounds, machine word); 4096 (LENGTH:
   ESTACK / zero page); 64 (LENGTH: GrantRo's hull margin); 8208 / 0 (DERIVED: STK_check_reject_clean /
   STK_fuzz_alloc_live at prh_img_B, checked by vm_compute); atom indices 2, 10-12, 32, 33, 37, 49, 53 (DERIVED: the
   symbolic engine's numbering, as FuzzStrdupB.v). No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc PRH_FnCheck CfParamsPreset.
From OSSVerify.omx_clap_core.fuzz_preset.images Require AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PRW_LiveBound.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
#[local] Notation CP := CfParams_preset.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
(* image B's own bounds, the generated per-image CfImg fields (lib/AU/CfImgB.v 82495e01f675, cf_img_lo / cf_img_top;
   h-mani-a8's rule 18:56Z for the image-shadow premise: never YImgTop's IMG_LO / IMG_TOP) *)
#[local] Notation CLO := (@cf_img_lo CfImgB.CfImg_B).
#[local] Notation CTOP := (@cf_img_top CfImgB.CfImg_B).
(* the symbolic state at check_reject_clean's entry: its frame of 16 bytes below the entry sp (atom 2), sp in the
   stack band astk_ok gives, no shadow entry (the function makes no instrumented access of its own) *)
Definition CR_Bx : sv := SOff 32 0.
Definition CR_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition cr_regions : smem := [ stack_region 16 ].
Definition cr_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition CR_PC : Z := B_prog_sigma AS_check_reject_clean - B_prog_base.
Definition ss_cr : sstate := mkSS CR_PC sr_atoms cr_regions None cr_facts.
Definition cr_SH : list shent := [].
Definition CR_EI (regs : bvmap 5 word) : env := @Eimg _ B_prog_listing PA (Ereg regs []).
(* `static const struct pj empty` (#102 source fuzz_preset.c:540), read by bcmp: the listing atom A_OBJ 2 plus the
   offset of the PAddHi slot that forms its address (DERIVED) *)
Definition CR_EMPTY : Z := B_prog_val (A_OBJ 2) + 0x10fc0.
(* fpre's return-address ceiling at the fuzz_alloc_live call: the jal's return pc is slot 13 of check_reject_clean
   (CR_PC + 52), a slot of the listing, so below alloc_ceiling (PRW_StepKit.pa_slot_lt_ceil_b; its boolean slot premise
   closed by vm_compute on this CLOSED goal, never inside the walk) *)
Lemma cr_ret_live_lt_ceil : 0 <= CR_PC + 52 < 2 ^ 40 /\ BASE + (CR_PC + 52) < YM05.alloc_ceiling.
Proof.
assert (Hk : 0 <= CR_PC + 52 < 2 ^ 40) by (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
split; [exact Hk|].
apply (PRW_StepKit.pa_slot_lt_ceil_b (L := B_prog_listing) (PL := PL) (PI := PA)); [exact Hk|].
vm_compute. reflexivity.
Qed.

(* ---- address arithmetic (no state) ---- *)
Lemma cr_req : forall z, 0 < z -> req_size z = z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.
Lemma cr_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma cr_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (SHADOW_OFF + x / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
lia.
Qed.
(* fuzz_grant GrantRo.v:82-100 ro_hull's arithmetic (FuzzStrdupB.v sd_hull_img): the hull of a range at least 64 bytes
   inside [CLO, CTOP) (image B's OWN bounds, CfImgB.v cf_img_lo / cf_img_top) is the shadow of image bytes *)
Lemma cr_hull_img : forall a n s, 0 < n -> CLO + 64 <= a -> a + n + 64 <= CTOP ->
shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
s = shadow_addr (8 * (s - SHADOW_OFF)) /\ CLO <= 8 * (s - SHADOW_OFF) < CTOP.
Proof.
intros a n s Hn Hlo Hhi Hs. unfold CfImgB.CfImg_B in *. cbn [cf_img_lo cf_img_top] in *. unfold shadow_addr in *.
assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
unfold SHADOW_OFF in *.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.
(* a nonzero int in a0 (sign-extended) is not 0 as a 64-bit word *)
Lemma cr_rc_canon : forall r, - 2 ^ 31 <= r < 2 ^ 31 -> r <> 0 ->
  (zcanon (bv_unsigned (Z_to_bv 64 r) + 0) =? zcanon 0) = false.
Proof.
intros r R NZ. apply Z.eqb_neq.
rewrite (zcanon_id 0) by (unfold M64; lia).
rewrite Z_to_bv_unsigned, Z.add_0_r, zcanon_wrap.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_mod by lia.
destruct (Z_lt_le_dec r 0) as [N|P].
- rewrite <- (Z.mod_add r 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. exact NZ.
Qed.

(* ---- the image (computed from the generated segments and the listing; no number typed) ---- *)
Lemma cr_empty_img : CLO + 64 <= CR_EMPTY /\ CR_EMPTY + 56 + 64 <= CTOP /\ 4096 <= CR_EMPTY /\
  CR_EMPTY + 56 + 8 <= kLowMemEnd - 1.
Proof. repeat split; apply Z.leb_le; vm_compute; reflexivity. Qed.
(* `empty`'s 56 bytes: inside one read-only segment, and zero in the image *)
Definition cr_rocov : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? CR_EMPTY) &&
    (CR_EMPTY + 56 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) SEGS.
Lemma cr_rocov_ok : cr_rocov = true.
Proof. vm_compute. reflexivity. Qed.
Definition cr_romb : bool :=
  forallb (fun j => match seg_rom SEGS (Z_to_bv 64 (CR_EMPTY + Z.of_nat j)) with
                   | Some b => bv_unsigned b =? 0 | None => false end) (seq 0 56).
Lemma cr_romb_ok : cr_romb = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cr_empty_rom : forall j, 0 <= j < 56 ->
  in_rom SEGS (CR_EMPTY + j) /\ in_roP SEGS RLO RHI (CR_EMPTY + j) /\
  option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 (CR_EMPTY + j))) = Some 0.
Proof.
intros j Hj. pose proof cr_rocov_ok as H. unfold cr_rocov in H. apply existsb_exists in H as (s & Hs & Hb).
apply andb_true_iff in Hb as [Hb H3]. apply andb_true_iff in Hb as [H1 H2].
apply negb_true_iff in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
assert (Hr : in_rom SEGS (CR_EMPTY + j)) by (exists s; split; [exact Hs|]; split; [exact H1|]; lia).
split; [exact Hr|]. split; [left; exists s; split; [exact Hs|]; split; [exact H1|]; lia|].
pose proof cr_romb_ok as R. unfold cr_romb in R. rewrite forallb_forall in R.
specialize (R (Z.to_nat j) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in R by lia.
destruct (seg_rom SEGS (Z_to_bv 64 (CR_EMPTY + j))) as [b|]; [|discriminate R].
apply Z.eqb_eq in R. cbn [option_map]. rewrite R. reflexivity.
Qed.
Lemma cr_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
(* alloc.c's statics are image bytes below the low-memory end *)
Lemma cr_pst_low : forall a, Exists (in_zr a) PST -> 0 <= a < kLowMemEnd.
Proof.
intros a Hx. unfold prh_pst in Hx.
cbn [pi_g_live pi_g_peak pi_g_count pi_g_fail pi_g_ran_out pi_g_most pi_g_own_ran_out pi_gz_live pi_gz_peak pi_gz_count
  pi_gz_fail pi_gz_ran_out pi_gz_most pi_gz_own_ran_out prh_img_B] in Hx.
unfold kLowMemEnd.
repeat (apply Exists_cons in Hx; destruct Hx as [Hx|Hx]; [unfold in_zr in Hx; cbn [fst snd] in Hx; lia |]).
apply Exists_nil in Hx; destruct Hx.
Qed.

(* ---- bytes ---- *)
Lemma cr_garr8_aview : forall (W : world SEGS) m p l j, garr8 SEGS (mrestrict (w_H W) m) p l -> (j < length l)%nat ->
aview SEGS (w_H W) m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m p l j H Hj. unfold aview. rewrite (garr8_mbyte SEGS _ p l j H Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (H j Hj)).
Qed.
Lemma cr_garr8_move : forall (W W' : world SEGS) m m' x d l, garr8 SEGS (mrestrict (w_H W) m) x l ->
(forall j, (j < length l)%nat -> aview SEGS (w_H W') m' (d + Z.of_nat j) = aview SEGS (w_H W) m (x + Z.of_nat j)) ->
garr8 SEGS (mrestrict (w_H W') m') d l.
Proof.
intros W W' m m' x d l H HA j Hj. destruct (H j Hj) as [V R]. split; [|exact R].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (V 0%nat Hkk). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
specialize (HA j Hj). unfold aview in HA. rewrite V in HA. cbn [option_map] in HA.
destruct (mbyte SEGS (mrestrict (w_H W') m') (d + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in HA; [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.
Lemma cr_src_ok : forall (W : world SEGS) regs m p l, garr8 SEGS (mrestrict (w_H W) m) p l ->
(forall a, p <= a < p + Z.of_nat (length l) -> ~ (spZ regs - ESTACK <= a < spZ regs)) ->
src_ok SEGS W regs m p (Z.of_nat (length l)).
Proof.
intros W regs m p l H Hw a Ha. split; [|exact (Hw a Ha)].
replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (cr_garr8_aview W m p l (Z.to_nat (a - p)) H) by lia. discriminate.
Qed.

(* ---- the frame and the stack writes ---- *)
Lemma cr_aview_of_frame : forall (Wx : world SEGS) (E' : env) rs (m m' : word -> option byte) a,
frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
(* cgif-pg CtrlIdentityPollBlock.v's ipb_awr / ipb_keep at check_reject_clean's frame of 16 bytes (FuzzStrdupB.v
   sd_awr / sd_keep) *)
Ltac cr_awr rg HU :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
lazymatch goal with |- awr_ok _ _ _ ?sp0' _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ rg - sp0')) end;
[ reflexivity
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth]; rewrite ?ew_ewset_other by lia;
rewrite ?ew_havoc_old by (cbv; lia); rewrite HU; lia
| cbn [YP09.r_wlo stack_region]; lia
| cbn [YP09.r_whi stack_region]; lia
| apply awr_ok_nil ].
Ltac cr_keep K H rg Wx HU :=
lazymatch type of K with
| frame_of ?Ex ?rsx (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (H : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ rg - 16 <= a < spZ rg) ->
aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a)
by (intros a Ha Hn; apply (cr_aview_of_frame Wx Ex rsx mA mB a K); [|exact Ha];
intros (r & Hin & Hr); vm_compute in Hin;
destruct Hin as [Hin | Hin]; [subst r | destruct Hin];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
rewrite ?ew_ewset_other in Hr by lia; rewrite ?ew_havoc_old in Hr by (cbv; lia);
rewrite HU in Hr; lia)
end.

(* THE READ-ONLY BYTES THIS WALK READS ITSELF: `empty`'s 56 (bcmp's second operand; the walk needs their values to
   show the abort branch is not taken). fpre's arodata_okP gives the image byte of an in_roP byte that is not
   owned-static and not errno (its guard, lib/A/PRH_Base.v arodata_okP); this is that guard, for those 56 bytes only,
   as an image fact of B'. It replaces the stand-in pal_rom_ok (`forall a, in_rom SEGS a -> ~ owned /\ ~ errno`), which
   is FALSE at the instance: the owned-static redzones of .rodata globals lie in B's read-only segments
   (CrcBRomRefute.v cr_pal_rom_ok_false_B at B', the same proposition as g-ph-relay's #102 refutation
   pal_rom_ok_false_B102, cold/g-ph-relay-p102-N9-ROMVIEW-102Bp 0d0f7930f0a3 lib/ZZRomviewProbe102Bp.v:46-49; their
   agreement is CrcBRomRefute.v cr_pal_rom_ok_txt_B102). Instance witness: CrcBRomRefute.v cr_empty_ro_B (vm_compute
   at YD2l.TfibB, blob 95803a8b9493). *)
Definition cr_empty_ro (B : asyms) : Prop :=
  forall a, CR_EMPTY <= a < CR_EMPTY + 56 ->
    ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {HL : Z}.
(* the allocator relation's laws (YCbqG.v AR_laws_x, 18 fields; the engine's form) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation LEDGER := (prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B).
(* the image's shadow bytes are present in every state, over image B's OWN bounds, the CfImg fields of image B's
   generated record (CLO / CTOP = @cf_img_lo / @cf_img_top CfImgB.CfImg_B): h-mani-a8's img_shadow_vis_cf text
   (YGcfAmx2.v:47-49) at ci := CfImg_B with ARcf -> ARx (a8's rule 18:56Z; its B' instance
   tfib_img_shadow_vis_cf_B, lib/AU/AImgShadowVisCfB.v on cold/h-mani-a8-alloc102, pending) *)
Definition cr_img_shadow_vis_B : Prop :=
  forall ly S Hp (W : world SEGS) mem md a, ARx ly S Hp W mem md -> CLO <= a < CTOP ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* callee texts: fuzz_alloc_live's (a Theorem Labs lane, lib/A/PRH_FnAlloc.v:110, blob 740f4d11d144 at kit f97c8b2f046b: the
   ledger with `most own`, the m-form post fpostm; owner slice S2, the accessors) and the bcmp wrapper's in the keep form
   (YGcallMxmn.v:265 abcmp_realizes_xm, blob b47cf7942c3d: YGcallMx.v abcmp_realizes_x plus the memnorm keep; owner
   a Theorem Labs lane's bcmp row, po_bcmp_cf pays it) *)
Hypothesis FLIVE : tfuzz_alloc_live_specX (cp := CP) (PI := prh_img_B) (PA := PA) B ARx SK.
Hypothesis BCMP : YGcallMxmn.abcmp_realizes_xm SEGS B ARx (SIGMA AS___wrap_bcmp).
(* IMAGE FACT (owner the image instance; RESTATED from the false pal_rom_ok, see cr_empty_ro): `empty`'s 56 bytes are
   not owned-static and not errno, so fpre's arodata_okP gives their image bytes. Witness at B': cr_empty_ro_B. *)
Hypothesis EMPTY_RO : cr_empty_ro B.
(* the image's shadow bytes at B's bounds (owner h-mani-a8: img_shadow_vis_cf at ARcf, a unit-supplied fact) *)
Hypothesis IMGV : cr_img_shadow_vis_B.
(* IMAGE FACT (the kit's header: `empty` lies in one of B's registered zero-shadow ranges; owner the image instance):
   a granule-aligned range of as_zero_shadow B covers its 56 bytes. Witness at B': CrcBRomRefute.v cr_empty_zs_B. *)
Hypothesis EMPTY_ZS : exists q m, In (q, m) (as_zero_shadow B) /\ q mod 8 = 0 /\ q <= CR_EMPTY /\
  CR_EMPTY + 56 <= q + m / 8 * 8.

Lemma cr_entry : forall STK ly S Hp W regs mem md ch,
afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> 16 <= STK ->
st_ok_pi SEGS VAL (CR_EI regs) ss_cr (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CR_PC)) mem (seg_rom SEGS)))
/\ sh_ok SEGS CR_Bx cr_SH (CR_EI regs) (mrestrict (w_H W) mem).
Proof.
intros STK ly S Hp W regs mem md ch HPRE H16.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
rewrite restrict_mkst_fx.
set (E := CR_EI regs) in *.
assert (E2 : ew E 2 = getr regs 2)
by (subst E; unfold CR_EI; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split.
- unfold ss_cr. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold cr_regions, stack_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
+ cbn [cr_regions pairwise_disjoint all_disjoint]. exact (conj I I).
+ split; [|split; [exact I | exact I]].
cbn [cr_facts f_atoms atoms_ok].
split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia].
- unfold sh_ok, cr_SH. apply Forall_nil.
Qed.

(* the read-only view survives any change below alloc_ceiling's complement *)
Lemma cr_rod_kept : forall (W W' : world SEGS) m m', arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) m) ->
(forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
arodata_okP SEGS RLO RHI B (aview SEGS (w_H W') m').
Proof.
intros W W' m m' H HA a Hro Hn He. pose proof (@pa_segs_low _ _ PA a (cr_ro_img a Hro)) as Hl.
pose proof asan_consts as (C1 & _ & _ & _ & C5). rewrite HA by lia. exact (H a Hro Hn He).
Qed.

(* the ledger survives a memory change below alloc_ceiling that misses the statics and every head word *)
Lemma cr_ledger_kept : forall ly S Hp W mem mem' memX mdX Lam peak cnt fail ran most own (C : Z -> Prop),
ARx ly S Hp W memX mdX -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
(forall a, 0 <= a < alloc_ceiling -> ~ C a -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
(forall a, Exists (in_zr a) PST -> ~ C a) ->
(forall a k i, In (a, k) Lam -> 0 <= i < 8 -> ~ C (a - 16 + i)) ->
LEDGER ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem mem' memX mdX Lam peak cnt fail ran most own C HAR HLd HK HCs HCh.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem' Lam peak cnt fail ran most own HLd).
- intros a Ha. pose proof (cr_pst_low a Ha). apply HK; [lia | exact (HCs a Ha)].
- intros a k i Hin Hi.
  destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLd Hin) as (Hk0 & Hab & _).
  change (@cf_head CfParams_preset) with 16 in *.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W memX mdX (a - 16) (k + 16) HAR Hab) as (_ & H4096 & Hc & _).
  rewrite cr_req in Hc by lia. apply HK; [lia | exact (HCh a k i Hin Hi)].
- intros a k _ H. exact H.
- apply Permutation_refl.
Qed.

(* `empty`'s shadow: its granules lie in a zero-shadow range (alx_zshadow), its hull in the image's shadow *)
Lemma cr_empty_shadow : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF CR_EMPTY 56 /\
  shadow_hull_vis (aview SEGS (w_H W) mem) CR_EMPTY 56.
Proof.
intros ly S Hp W mem md HAR. destruct EMPTY_ZS as (q & m & Hin & Hq8 & Hqlo & Hqhi).
pose proof (alx_zshadow SEGS B ARx LAWS ly S Hp W mem md (q, m) HAR
  ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
cbn [fst snd] in Hz. pose proof cr_empty_img as (I1 & I2 & I3 & I4).
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  assert (Hq : q = q / 8 * 8) by (pose proof (Z.div_mod q 8 ltac:(lia)); lia).
  assert (Ex : x / 8 = q / 8 + (x - q) / 8).
  { replace x with ((x - q) + q / 8 * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
  unfold zero_shadow, shadow_of_addr in Hz. unfold shadow_of_addr. rewrite Ex, Z.add_assoc. apply Hz.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
- intros s Hs. destruct (cr_hull_img CR_EMPTY 56 s ltac:(lia) I1 I2 Hs) as [E Hr]. rewrite E.
  exact (IMGV ly S Hp W mem md _ HAR Hr).
Qed.

(* ---- the walk ---- *)
Theorem check_reject_clean_holds_B :
  tcheck_reject_clean_specX (cp := CP) (PI := prh_img_B) (PA := PA) B ARx SK.
Proof.
unfold tcheck_reject_clean_specX, fpostm, fQmn.
intros ly S Hp W regs mem md ch rcv doc live Lam peak cnt fail ran most own (HPRE & HROD & HTOP & HRAC & HFRM) H10 Hrc
  Hrc0 H11 HSRC H12 Hlive HLED.
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof (pa_base_lo (PL := PL) (PI := PA)) as HBLO. change (@pa_lo _ _ PA) with IMG_LO_B in HBLO. unfold IMG_LO_B in HBLO.
pose proof (@pa_B_ok _ _ PA) as HBASE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cr_empty_img as (I1 & I2 & I3 & I4).
assert (FST : @STK_check_reject_clean prh_img_B = 8208) by (vm_compute; reflexivity).
assert (FSL : @STK_fuzz_alloc_live prh_img_B = 0) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
rewrite FST in *.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
pose proof HSRC as (Hdg & Hd4096 & Hdceil & Hdamr & HdRA & HdHU).
rewrite repeat_length in Hdceil, Hdamr, HdRA, HdHU. change (Z.of_nat 56) with 56 in Hdceil, Hdamr, HdRA, HdHU.
pose proof (prh_lsum_lt_ceiling (cp := CP) (PI := prh_img_B) (PA := PA) B ARx LAWS ly S Hp W mem md Lam peak cnt fail ran
  most own HAR HLED) as HLB.
destruct (cr_entry 8208 ly S Hp W regs mem md ch HPRE ltac:(lia)) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx 8208 [] ly S Hp W regs mem md ch HPRE) as HJ.
remember (CR_EI regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold CR_EI; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs []) n) by (intros n Hn; subst E; unfold CR_EI; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 rcv) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 doc) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 live) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (EA2 : bv_unsigned (ew E (A_OBJ 2)) = VAL (A_OBJ 2)) by (apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE EL.
pose (RUN := paj_run_x (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
(* the same runner carrying the memnorm keep from the entry memory (h-hpreset-7's carrier, YSRrMemnorm.v:40) *)
pose (RUNM := paj_run_x_inv (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS))).
pose (BR := paj_branch (PI := PA)).
pose (RET := paj_ret_at (PL := PL) (PI := PA)).
unfold cfg_at. change (w64 (SIGMA AS_check_reject_clean)) with (Z_to_bv 64 (BASE + CR_PC)).
(* ---- slots 0-3: the frame (sd ra, sd s0), `beqz a0` ---- *)
pose proof (fun H : YAkMemnorm.memnorm SEGS mem => H) as HPM.
paj_run_tok_x_inv RUNM HS HJ SHOK HPM CR_Bspan; [cr_awr regs Usp|].
clear HF HG. cr_keep HFr KA regs W Usp. clear HFr.
psrr_branch_tok RUN BR HS SHOK CR_Bspan.
{ (* rc = 0: the abort tail, not taken *)
  exfalso. rewrite branch_eq_U, U_SOff, E10, U_SLit, (cr_rc_canon rcv Hrc Hrc0) in Hc. discriminate Hc. }
clear Hc.
(* ---- slots 4-10: s0 = live, a0 = doc, a1 = &empty, a2 = 56, the bcmp call ---- *)
paj_run_tok_x_inv RUNM HS HJ SHOK HPM CR_Bspan; [cr_awr regs Usp|].
clear HF HG. cr_keep HFr KB regs W Usp. clear HFr.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (2%bv : bv 5) Rsp1. prreg HS (1%bv : bv 5) Rra1. prreg HS (3%bv : bv 5) Rgp1. prreg HS (4%bv : bv 5) Rtp1.
pose proof (proj1 HJ) as HART. cbv beta in HART.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  assert (HspT : spZ rT = spZ regs - 16) by (unfold spZ at 1; rewrite Rsp1, Usp; rewrite unsigned_lit_small by lia; lia);
  assert (KAB : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) mT a = aview SEGS (w_H W) mem a)
    by (intros a Ha; rewrite (KB a ltac:(lia) ltac:(lia)); exact (KA a ltac:(lia) ltac:(lia)));
  pose proof (cr_empty_shadow _ _ _ _ _ _ HART) as [HeRA HeHU];
  assert (HdgT : garr8 SEGS (mrestrict (w_H W) mT) doc (repeat 0 56))
    by (apply (cr_garr8_move W W mem mT doc doc (repeat 0 56) Hdg); intros j Hj; rewrite repeat_length in Hj;
        apply KAB; lia);
  assert (HeV : forall j, 0 <= j < 56 -> aview SEGS (w_H W) mT (CR_EMPTY + j) = Some 0)
    by (intros j Hj; destruct (cr_empty_rom j Hj) as (_ & Hro & Hv);
        destruct (EMPTY_RO (CR_EMPTY + j) ltac:(clear - Hj; lia)) as [Hno Her];
        rewrite KAB by lia; rewrite (HROD _ Hro Hno Her); exact Hv);
  assert (HdV : forall j, 0 <= j < 56 -> aview SEGS (w_H W) mT (doc + j) = Some 0)
    by (intros j Hj; replace (doc + j) with (doc + Z.of_nat (Z.to_nat j)) by lia;
        rewrite (cr_garr8_aview W mT doc (repeat 0 56) (Z.to_nat j) HdgT) by (rewrite repeat_length; lia);
        rewrite nth_repeat; reflexivity)
end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (YGcallMxmn.aj_bcmp_at_xm (SK := SK) SEGS B PST ARx LAWS Hsegs (SIGMA AS___wrap_bcmp) BCMP W rT mT 8208
    (spZ regs) []
    ly S Hp W mem md [] ly S Hp dT 0 doc CR_EMPTY 56 (-16) _ HJ) end.
  - rewrite Ra0, E11. reflexivity.
  - rewrite Ra1. unfold w64, CR_EMPTY. f_equal.
    lazymatch goal with |- context [ew E ?n] => change (ew E n) with (ew E (A_OBJ 2)) end. rewrite EA2. reflexivity.
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite HspT. lia.
  - reflexivity.
  - lia.
  - rewrite Hes. lia.
  - rewrite Rgp1, E3. exact Hgp.
  - rewrite Rtp1, E4. exact Htp.
  - exact Rra1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - change 56 with (Z.of_nat (length (repeat 0 56))). apply (cr_src_ok W _ _ doc (repeat 0 56) HdgT).
    intros a Ha. rewrite repeat_length in Ha. rewrite HspT. lia.
  - intros a Ha. split; [|rewrite HspT; lia]. replace a with (CR_EMPTY + (a - CR_EMPTY)) by lia.
    rewrite (HeV (a - CR_EMPTY) ltac:(lia)). discriminate.
  - intros a Ha. lia.
  - intros a Ha. lia.
  - exact Hdamr.
  - unfold amem_range. left. lia.
  - eapply range_addressable_agree; [|exact HdRA]. intros x Hx. pose proof (cr_shadow_low x ltac:(lia)). apply KAB. lia.
  - intros Hn0 s0 Hs. pose proof (cr_hull_low doc 56 s0 ltac:(lia) Hn0 ltac:(lia) Hs).
    rewrite KAB by lia. apply HdHU; [exact Hn0 | exact Hs].
  - exact HeRA.
  - intros _. exact HeHU. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2 & Hmn2).
pose proof (fun H0 => Hmn2 (HPM H0)) as HPM2. clear HPM Hmn2. rename HPM2 into HPM.
assert (Hv0 : v = w64 0).
{ apply Hcmp. intros i Hi. rewrite (HdV i Hi), (HeV i Hi). reflexivity. }
rewrite Hv0 in Hv. clear Hv0 Hcmp.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2J & _).
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HSX.
lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
{ constructor; [|apply Forall_nil]. split.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp in Ha.
    apply (mbyte_of_aview SEGS). apply Hfr2; lia.
  - intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
    apply (apresent_writable SEGS). apply Hpres2J. lia. }
specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
remember (havoc E 33 (map (getr regs2) CLOB)) as E1' eqn:HE1 in HSX.
assert (HIM1 : img_env VAL A_LIM E1') by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall n, (n < 33)%nat -> ew E1' n = ew E n) by (intros n Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
assert (E1a0 : ew E1' 37 = w64 0) by (rewrite HE1, <- Hv; reflexivity).
assert (HAE1 : env_agree 32 (Ereg regs []) E1') by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE1.
assert (Usp1 : bv_unsigned (ew E1' 2) = spZ regs) by (rewrite OLD1 by (cbv; lia); exact Usp).
assert (SHOK1 : sh_ok SEGS CR_Bx cr_SH E1' (mrestrict (w_H W) mem2)) by (unfold sh_ok, cr_SH; apply Forall_nil).
assert (KAC : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite (Hfr2 a ltac:(lia) ltac:(lia)). apply KAB. exact Ha. }
clear HS HJ SHOK. rename HSX into HS. rename HJ2 into HJ. rename SHOK1 into SHOK.
(* ---- slot 11: `bnez a0` (bcmp's result), not taken ---- *)
psrr_branch_tok RUN BR HS SHOK CR_Bspan.
{ exfalso. rewrite branch_ne_U, (U_atom E1' 37 0 E1a0 ltac:(lia)), U_SLit in Hc.
  rewrite (zcanon_id 0) in Hc by (unfold M64; lia). cbn in Hc. discriminate Hc. }
clear Hc.
(* ---- slot 12: the fuzz_alloc_live call ---- *)
paj_run_tok_x_inv RUNM HS HJ SHOK HPM CR_Bspan; [cr_awr regs Usp1|].
clear HF HG. cr_keep HFr KD regs W Usp1. clear HFr.
prreg HS (2%bv : bv 5) P2. prreg HS (1%bv : bv 5) P1. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8.
lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ =>
  assert (KAD : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) (ms_mem msq) a = aview SEGS (w_H W) mem a)
    by (intros a Ha; rewrite (KD a ltac:(lia) ltac:(lia)); exact (KAC a Ha))
end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ =>
  eapply (aj_call_x (SK := SK) SEGS B PST ARx LAWS Hsegs W E1' _ msq 8208 (spZ regs) [] ly S Hp W mem md [] ly S Hp mdq 0
    (@STK_fuzz_alloc_live prh_img_B) [] (-16) (ew E1' 2) _ [] _ HS eq_refl HJ) end.
  - exact (st_ok_restrict_reg SEGS (w_H W) E1' _ _ 2%bv HS).
  - reflexivity.
  - exact Usp1.
  - reflexivity.
  - lia.
  - rewrite FSL. lia.
  - rewrite FSL. lia.
  - rewrite P3, OLD1, E3 by (cbv; lia). exact Hgp.
  - rewrite P4, OLD1, E4 by (cbv; lia). exact Htp.
  - exact P1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite P8, OLD1, E12 by (cbv; lia). rewrite unsigned_lit_small by lia. lia.
  - intros HPRE1.
    lazymatch type of HPRE1 with afn_pre_x _ _ _ _ _ _ _ _ ?rq _ _ _ =>
      assert (Htop1 : spZ rq + 64 <= ly_stk_hi ly)
        by (unfold spZ at 1; rewrite P2; cbn [sv_denot]; rewrite Usp1; rewrite unsigned_lit_small by lia; lia);
      (* fpre's return-address ceiling at the callee: the jal's own return pc, slot 13 (cr_ret_live_lt_ceil) *)
      assert (Hra1 : raZ rq < YM05.alloc_ceiling)
        by (unfold raZ; rewrite P1;
            lazymatch goal with |- bv_unsigned (Z_to_bv 64 (_ + ?k)) < _ => change k with (CR_PC + 52) end;
            pose proof cr_ret_live_lt_ceil as (Hk & Hc); rewrite unsigned_lit_small by lia; exact Hc) end.
    refine (FLIVE ly S Hp W _ _ _ _ Lam peak cnt fail ran most own
      (conj HPRE1 (conj (cr_rod_kept W W mem _ HROD KAD) (conj Htop1 (conj Hra1 HFRM)))) _).
    apply (cr_ledger_kept ly S Hp W mem _ mem md Lam peak cnt fail ran most own (fun _ => False) HAR HLED);
      [intros a Ha _; exact (KAD a Ha) | intros; tauto | intros; tauto].
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs3 & mem3 & md3 & k1 & -> & HJ3 & HJc & HP3 &
  (HRL2 & Hres & HHp2 & HS2 & HAB2 & HLED3) & Hmn3).
pose proof (fun H0 => Hmn3 (HPM H0)) as HPM2. clear HPM Hmn3. rename HPM2 into HPM.
pose proof (proj1 HJ3) as HAR3. cbv beta in HAR3.
jafter_call_keep_pi HS 49%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. constructor; [|apply Forall_nil].
  eapply (region_kept_stack_sub_x (SK := SK) SEGS B PST ARx); [exact HJc | exact HJ3 | exact Usp1 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E1' 49 (map (getr regs3) CLOB)) as E3' eqn:HE3 in HS.
assert (HIM3 : img_env VAL A_LIM E3') by (rewrite HE3; apply img_env_havoc; [exact HIM1 | cbv; lia]).
assert (OLD3 : forall n, (n < 49)%nat -> ew E3' n = ew E1' n) by (intros n Hn; rewrite HE3; apply ew_havoc_old; exact Hn).
assert (E3a0 : ew E3' 53 = w64 (Ledger.lsum Lam)) by (rewrite HE3, <- Hres; reflexivity).
assert (HAE3 : env_agree 32 (Ereg regs []) E3') by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3' 2) = spZ regs) by (rewrite OLD3 by (cbv; lia); exact Usp1).
assert (SHOK3 : sh_ok SEGS CR_Bx cr_SH E3' (mrestrict (w_H W2) mem3)) by (unfold sh_ok, cr_SH; apply Forall_nil).
clear HJ SHOK HJc. rename HJ3 into HJ. rename SHOK3 into SHOK.
(* ---- slot 13: `bne a0, s0` (g_live against live), not taken ---- *)
psrr_branch_tok RUN BR HS SHOK CR_Bspan.
{ exfalso. assert (E312 : ew E3' 12 = Z_to_bv 64 live) by (rewrite OLD3, OLD1 by (cbv; lia); exact E12).
  rewrite branch_ne_U, (U_atom E3' 53 (Ledger.lsum Lam) E3a0 ltac:(lia)), (U_atom E3' 12 live E312 ltac:(lia)) in Hc.
  rewrite Hlive, Z.eqb_refl in Hc. cbn in Hc. discriminate Hc. }
(* ---- slots 14-17: the epilogue and ret ---- *)
paj_run_tok_x_inv RUNM HS HJ SHOK HPM CR_Bspan; [cr_awr regs Usp3|].
clear HF HG. cr_keep HFr KE regs W2 Usp3. clear HFr.
prreg HS (1%bv : bv 5) R1.
eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold fpost, apost_base_x.
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly2, S2, Hp2, r, m, d, (0 + k1) end.
split; [cbn [ms_regs]; rewrite R1, OLD3, OLD1, E1 by (cbv; lia); rewrite Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs); exact HJ|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (@nil word) HS); [exact HAE3 | vm_compute; reflexivity]|].
split; [|exact HPM].
split; [exact HHp2|]. split; [exact HS2|]. split; [exact HAB2|]. split; [exact HRL2|].
apply (cr_ledger_kept ly2 S2 Hp2 W2 mem3 _ mem3 md3 Lam peak cnt fail ran most own (fun _ => False) HAR3 HLED3);
  [intros a Ha _; cbn [ms_mem]; exact (KE a ltac:(lia) ltac:(lia)) | intros; tauto | intros; tauto].
Qed.
End f.
End d.
