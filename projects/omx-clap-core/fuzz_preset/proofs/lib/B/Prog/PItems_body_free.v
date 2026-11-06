(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_entry.v, with its module paths and module names changed; 826 of its 913 lines of code are new or changed and 1478 lines of the source are left out. *)
(* Theorem Labs, 2026-10: the MISSING-COLON FREE path of parse_items' image-B walk, PI_O_FREE (0x87ec8) .. the `j`
   back to the epilogue (0x87f34). Proves PItems_pres.v's
   pi_free_spec. Source preset_file.c:236-240: the colon is missing, so keys[n] (the key parse_string just made) is
   freed and parse_items returns -1.
   THE FREED BLOCK is pi_free_pre's (kx, kk): In (kx, kk) Lamc, ~ In (kx, kk) Lam, and kx - cf_head lies in no block
   of the ENTRY state S. So nothing of it is in FP = rd_fp q v (q's two cells are in the caller window, v's 56 bytes
   were the caller's at the entry), and the entry journal's block clause does not cover it: the footprint of the
   fuzz_free call is a TEMPORARY block of this call (YCbq.v in_tmp_block). Proved from the pre in pi_free_holds
   (HX0S: (kx, kk) is in D0, and rd_blocks_move's first clause says no block of D0 is a block of S; the fp_sub_x
   obligation of aj_call_xb_spR is then its in_tmp_block arm).
   THE WALK (the neutral listing, the internal file parse_items.fuzz_preset.asan-ubsan.s):
   the block makes no store. Its symbolic state (pif_ss) holds four READ-ONLY regions (the frame cells [sp],
   [sp + 8], [sp + 16]; the keys field v + 32; the n cell v + 40 through s6; the key slot keys + 8 n), s8 pinned to
   the shadow address of v + 40 in the form the token engine matches ((x >> 3) + s10), two shadow entries (the
   node's 56 bytes, the slot's 8) and ONE ALIAS: keys + 8 n is the slot atom 34, so the slot's checks are decided
   by its own facts (a per-atom bound of keys and of n cannot bound their sum below the shadow band). The token
   runner then decides by itself the shadow checks 0x87ed0 / 0x87ed8 / 0x87f28 (the probe byte is the literal 0
   under a covering entry, so the errpath twins 0x880e0 / 0x880e8 / 0x880f0 are never reached), the result-non-zero
   check 0x87ef8 (keys >= 4096 and the slot >= 4096), the null check 0x87f10 (keys >= 4096) and the alignment check
   0x87f18 (the slot is 8-aligned); it stops at 0x87f08 (the 2 ^ 60 guard: (n + 2 ^ 60) >> 61 = 0 as n <= 2 ^ 54) and
   0x87f0c (the wrap: keys + 8 n >= keys), both closed here by hand, and ends at the jal fuzz_free (aj_call_xb_spR at
   wle' segs RZ_cf to the text tfuzz_free_specX, which concludes SRr' segs RZ_cf with its budgeted post at wle'), then hands
   over to the epilogue PI_O_EPI at res = s5 = -1. The whole walk runs at wle' segs RZ_cf (pi_free_spec's journal and
   goal): the R runners PI_RUNR / PI_RUNTOR, paj_branchR, the journal lemmas' R forms.
   THE TRACE of the fuzz_free call reads the frame chain from s0 = q + 16 (0x87ab8 `addi s0, s1, 16`): one record
   (q + 16, text + len, the cursor), stopped by bad_next because the cursor is below alloc_ceiling and so below q
   (prh_cur_entry at parse_items), or no record when q + 16 is at the stack top; the closure's cursor clause or its
   empty-chain clause puts it in the universe (and [pc0] when frame 0 is not ok).
   FORM (b) (kit walkkit-next f97c8b2f046b, POST-IMPLICATION): the kit's tfuzz_free_specX states no entry position; its
   post's p <> 0 arm gives the position implication over [HFr (kk + cf_head)] from the call state to the return state,
   which PItems_posb.pi_posb_call composes onto pi_free_pre's pi_posb S Sc tr0 (the free's own trace event is
   rd_hevs [EFree kk] = [HFr (kk + HEAD)], HEAD = cf_head by PIF_HEAD); the live requests after the free are the
   call state's less the freed block's request (the post's ablocks split, pif_live_free), composed onto pi_live by
   pi_live_call. The text's post (pi_post = tpiP_Q, built through tpiP_Q_of_R) reads both off at the exit (pi_posb_post,
   pi_live). THE HULL (route (b)): fuzz_free's budget hull_budget Sc [] is pi_ent's (pi_ent_hull) paid past the prefix
   (pi_posb_budget_nil); its post's hull_used Sc S2 [] extends the block's use (pi_posb_call), so the post's
   tpiP_hull is the use over the whole (all-granted) trace. The post's injected reading: no call was refused
   (pi_grant_granted).
   Numerals: 4 / 8 / 16 / 24 / 32 / 40 / 56 / 144 LENGTH; 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 54 / 2 ^ 60 (also written
   1152921504606846976) / 2 ^ 61 / 2 ^ 64 DERIVED (bounds and the guard constant of the listing); 0x7fff7f800000
   DERIVED (YK06.alloc_ceiling's definition, restated for lia); 3 / 61 WORD (shift amounts); atom indices 2 .. 36
   DERIVED (the engine's numbering: registers below 32, extra atoms from 32, the call's havoc from 36). No ADDRESS
   literal: every pc is PI_AT PI_O_* at the listing instance. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YC80xf YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YK06 YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_ledk1 PItems_forder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Charge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild YG01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs PItems_pres.
(* beside PItems_body.v's preamble: PItems_shape.v's node-shape algebra (pis_exit_open's pj_fdR, pis_fd_frame), and the
   batch's memnorm and form (b)'s position / live-request names (used qualified) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_posb.
(* THE RE-HIDING MOVE and THE HULL (route (b)): the walk runs at the world relation wle' segs RZ_cf (YA0nH; the runner
   and branch over R, YSRrG), since fuzz_free frees; fuzz_free's hull budget and use (PresetHullBudget) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================================================================================== *)
(* the symbolic state at PI_O_FREE *)
Definition pif_shx (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff 26 0).
Definition pif_slot : sv := SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SLL (SOff 33 0) (SLit 3)).
Definition pif_slot2 : sv := SAlu ALU_ADD (SAlu ALU_SLL (SOff 33 0) (SLit 3)) (SOff 32 0).
Definition pif_regs : list sv := sr_set sr_atoms 24%bv (pif_shx (SOff 19 40)).
Definition pif_regions : smem :=
[ YP09.mkRegion (Some 2%nat) 0 24 0 0
    [YP09.mkChunk 0 (CVal 8 (SLit (2 ^ 60))); YP09.mkChunk 8 (CVal 8 (pif_shx (SOff 19 32)));
     YP09.mkChunk 16 (CVal 8 (SOff 19 32))];
  YP09.mkRegion (Some 19%nat) 32 40 0 0 [YP09.mkChunk 32 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 22%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
  YP09.mkRegion (Some 34%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 35 0))] ].
Definition pif_atoms : list (nat * afact) :=
[ (19%nat, mkAF 0 (2 ^ 47 - 56) 3); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
  (32%nat, mkAF 4096 (2 ^ 47 - 8) 3); (34%nat, mkAF 4096 (2 ^ 47 - 8) 3) ].
Definition pif_facts : facts := mkFacts pif_atoms [] [(pif_slot, SOff 34 0); (pif_slot2, SOff 34 0)].
Definition pif_ss (pc : Z) : sstate := mkSS pc pif_regs pif_regions None pif_facts.
Definition pif_SH : list shent := [mkSHE 19 0 56; mkSHE 34 0 8].
Definition pif_Bx : sv := SOff 26 0.
Definition pif_extra (keys n kx : Z) : list word := map (Z_to_bv 64) [keys; n; keys + 8 * n; kx].

Lemma pif_denot_shx : forall E x sb v, sv_denot E x = Z_to_bv 64 v -> ew E 26 = Z_to_bv 64 sb ->
  0 <= v < 2 ^ 63 -> 0 <= sb < 2 ^ 32 -> sv_denot E (pif_shx x) = Z_to_bv 64 (sb + v / 8).
Proof.
intros E x sb v Hx H26 Hv Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (pif_shx x))). f_equal.
change (U E (pif_shx x) = sb + v / 8). unfold pif_shx.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, H26.
assert (Ux : U E x = v) by (unfold U; rewrite Hx; apply unsigned_lit_small; lia). rewrite Ux.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound v 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id (v / 8)) by (unfold M64; lia). rewrite (zcanon_id sb) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* ---- the pure trace facts of the missing-colon free (PjGrammar.v / PRH_Reader.v) ---- *)
Lemma pif_calls_free : forall t n, calls (t ++ [EFree n]) = calls t.
Proof. induction t as [|e t IH]; intros n; cbn [app calls is_call]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma pif_hpeak_free : forall t n, hpeakR (t ++ [EFree n]) = hpeakR t.
Proof.
induction t as [|e t IH]; intros n; cbn [app hpeakR held_ev].
- lia.
- rewrite IH. reflexivity.
Qed.

Lemma pif_nlive_free : forall t n, nliveR (t ++ [EFree n]) = nliveR t - 1.
Proof. induction t as [|e t IH]; intros n; cbn [app nliveR nlive_evR]; [lia|]. rewrite IH. lia. Qed.

Lemma pif_held_free : forall t n, held (t ++ [EFree n]) = held t - Z.of_nat n.
Proof. induction t as [|e t IH]; intros n; cbn [app held held_ev]; [lia|]. rewrite IH. lia. Qed.

Lemma pif_lsz_free : forall t n, lszR (t ++ [EFree n]) = rm1nR n (lszR t).
Proof. intros t n. unfold lszR. rewrite fold_left_app. reflexivity. Qed.

Lemma pif_rm1_perm : forall k s, In k s -> Permutation s (k :: rm1nR k s).
Proof.
intros k s. induction s as [|x s IH]; intros H; [destruct H|]. cbn [rm1nR].
destruct (Nat.eqb_spec x k) as [->|Hne]; [apply Permutation_refl|].
destruct H as [H|H]; [exfalso; exact (Hne H)|].
eapply perm_trans; [apply perm_skip; exact (IH H)|]. apply perm_swap.
Qed.

(* a FIXED trace of depot shape is admitted at every state (YG01.admits, its second room disjunct) *)
Lemma pif_admits_fix : forall U tr s, (length tr <= kUnwindMax)%nat -> In tr (u_fix U) -> admits U tr s.
Proof.
intros U tr s Hl Hf. split; [split; [exact Hl | left; exact Hf]|]. right. left. apply mem_trace_In. exact Hf.
Qed.

(* the ledger move of the prefix, extended by the free of one of its blocks *)
Lemma pif_led_free : forall Lam peak cnt fail ran most ok gt tr D Lamc peakc cntc failc ranc Dfin l1 l2 kx kk,
  rd_ledger_move Lam peak cnt fail ran most ok gt tr D Lamc peakc cntc failc ranc ->
  Permutation D (Dfin ++ [(kx, kk)]) -> Lamc = l1 ++ (kx, kk) :: l2 -> 0 <= kk ->
  rd_ledger_move Lam peak cnt fail ran most ok gt (tr ++ [EFree (Z.to_nat kk)]) Dfin (l1 ++ l2) peakc cntc failc ranc.
Proof.
intros Lam peak cnt fail ran most ok gt tr D Lamc peakc cntc failc ranc Dfin l1 l2 kx kk
  (HO & HC & HF & HP & HS & HN & HK) HD -> Hkk.
unfold rd_ledger_move. rewrite pif_calls_free, pif_hpeak_free, pif_lsz_free, pif_nlive_free, PItems_ledk1.pik1_reqs_free.
split; [exact HO|]. split; [exact HC|]. split; [exact HF|].
split.
{ apply (Permutation_cons_inv (a := (kx, kk))).
  eapply perm_trans; [apply Permutation_middle|].
  eapply perm_trans; [exact HP|].
  eapply perm_trans; [apply Permutation_app_tail; exact HD|].
  rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
split.
{ assert (HDs : Permutation (map snd D) (kk :: map snd Dfin)).
  { eapply perm_trans; [apply Permutation_map; exact HD|]. rewrite map_app. cbn [map snd].
    apply Permutation_sym. apply Permutation_cons_append. }
  assert (Hin : In (Z.to_nat kk) (lszR tr)).
  { assert (Hk : In kk (map Z.of_nat (lszR tr))).
    { apply (Permutation_in _ HS). apply (Permutation_in _ (Permutation_sym HDs)). left. reflexivity. }
    apply in_map_iff in Hk as (m & Hm & Hmin). subst kk. rewrite Nat2Z.id. exact Hmin. }
  pose proof (pif_rm1_perm _ _ Hin) as HR.
  apply (Permutation_cons_inv (a := kk)).
  eapply perm_trans; [apply Permutation_sym; exact HDs|].
  eapply perm_trans; [exact HS|].
  eapply perm_trans; [apply Permutation_map; exact HR|].
  cbn [map]. rewrite Z2Nat.id by exact Hkk. apply Permutation_refl. }
split.
{ pose proof (Permutation_length HD) as HL. rewrite length_app in HL. cbn [length] in HL. lia. }
exact HK.
Qed.

Section body. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
#[local] Notation Lb := B_prog_listing.
#[local] Notation PLb := PL_prog_B.
#[local] Notation PIb := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ Lb PIb).
#[local] Notation VALb := (@pa_val _ Lb PIb).
#[local] Notation PIATb o := (@PI_AT _ Lb PIb o).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib (PI := PIb) B.

(* the epilogue, PItems_entry.v's pi_epi_holds (the top supplies it as EPI : forall d, pi_epi_spec B ARx SK d); the value
   segment is NOT a Section hypothesis: each step takes pi_val_spec at its own d / N, as PItems_top.v consumes it *)
Hypothesis HEPI : forall d, pi_epi_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d.

(* the callee texts (the kit's, lib/A), at this image and at EVERY float state the run can reach *)
Hypothesis TSKW : forall fy : YK11.FPState, tskip_ws_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK.
Hypothesis TGROW : forall (fy : YK11.FPState) CTX0,
  tgrow_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK CTX0.
Hypothesis TPSTR : forall (fy : YK11.FPState) CTX0 CW,
  tparse_string_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK CTX0 CW.
Hypothesis TFREE : forall fy : YK11.FPState, tfuzz_free_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK.

(* ---- MARKED Section hypotheses of this block (see the report). fuzz_free's live-count premise at the call
   0x87f30 is NOT one of them: it is pi_free_pre's last conjunct (a cut premise of this block; no call between
   PI_O_FREE and the jal, so it is the call-state count). ---- *)
(* image facts of image B's PrhImg (reflexivity at prh_img_B, lib/B/PRH_ImgB.v): parse_items' frame is
   the listing's 144 (PItems_value.v's FRPI text), its s0 is the cursor + 16 (0x87ab8 `addi s0, s1, 16`), and the
   return site of the missing-colon `jal fuzz_free` is its fuzz_free site *)
Hypothesis FRPI : PRH_Base.pi_frame F_parse_items = PI_FRAME.
Hypothesis FS0 : pi_s0cur F_parse_items = Some 16.
Hypothesis FSITE : In (VALb A_TEXT + PIATb PI_O_FFREE + 4) (pi_ret_sites F_parse_items RT_fuzz_free).
(* the program's statics are not read-only (the KEY segment's PIK_PSTRO, same text). At
   PIi := prh_img_B it is S1ImgB.v pst_not_ro_B. *)
Hypothesis PIF_PSTRO : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS pa_relro_lo pa_relro_hi a.
(* The kit's post body is STABLE: PItemsEntry's pi_post_stable (lib/B/Prog/PItems_entry.v, Qed), verbatim at this
   image. OWNER: PItems_entry.v; discharged at the top by pi_post_stable. *)
Hypothesis PIF_QS : forall ly0 S0 dd o tb text len p q v Lam peak cnt fail ran most own kr,
  pi_Qstable (L := Lb) (PA := PIb)
    (pi_post (L := Lb) (PA := PIb) B ly0 S0 dd o tb text len p q v Lam peak cnt fail ran most own kr).
(* the instance's head length is the model's (form (b): the free's position implication is over [HFr (kk + cf_head)],
   the trace's event is rd_hevs [EFree kk] = [HFr (kk + HEAD)]). OWNER: the instance; reflexivity at CfParams_preset
   (cf_head = 16 = PresetReqAt.HEAD). *)
Hypothesis PIF_HEAD : cf_head = PresetReqAt.HEAD.

(* ---- small facts the walk uses ---- *)
Lemma pif_disj : forall lo1 hi1 lo2 hi2, (forall a, lo1 <= a < hi1 -> lo2 <= a < hi2 -> False) ->
  lo1 < hi1 -> lo2 < hi2 -> hi1 <= lo2 \/ hi2 <= lo1.
Proof.
intros lo1 hi1 lo2 hi2 H H1 H2. destruct (Z_le_gt_dec hi1 lo2) as [E|E]; [left; exact E|].
destruct (Z_le_gt_dec hi2 lo1) as [E'|E']; [right; exact E'|].
exfalso. apply (H (Z.max lo1 lo2)); lia.
Qed.

(* a block shadow gives the addressability of one 8-aligned granule inside it *)
Lemma pif_ra_of_bs : forall (rd : Z -> option Z) Bz p m a,
  block_shadow rd Bz p m -> p <= a -> a mod 8 = 0 -> a + 8 <= p + m -> range_addressable rd Bz a 8.
Proof.
intros rd Bz p m a (Hp8 & Hm & Hbs) Hpa Ha8 Ham x Hx.
exists 0. split; [|left; reflexivity].
assert (Ei : shadow_of_addr Bz x = shadow_of_addr Bz p + (a - p) / 8).
{ unfold shadow_of_addr. Z.div_mod_to_equations. lia. }
rewrite Ei. assert (Hi : 0 <= (a - p) / 8 < m / 8) by (Z.div_mod_to_equations; lia).
rewrite (Hbs ((a - p) / 8) ltac:(Z.div_mod_to_equations; lia)).
replace ((a - p) / 8 <? m / 8) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* THE ENTRY STATE at PI_O_FREE: the four read-only regions, the pinned s8, the atom facts and the slot alias *)
Lemma pif_st_ok : forall (fxc : YK11.FPState) (Wc : world SEGS) memc (regs : bvmap 5 word) v keys n kx pc,
  getr regs 19 = w64 v -> getr regs 22 = w64 (v + 40) -> getr regs 24 = w64 (pi_sh (v + 40)) ->
  getr regs 26 = w64 SHADOW_OFF ->
  0 <= v <= 2 ^ 47 - 56 -> v mod 8 = 0 ->
  4096 <= keys -> keys mod 8 = 0 -> 0 <= n -> keys + 8 * n + 8 <= 2 ^ 47 -> 0 <= kx < 2 ^ 64 ->
  2 ^ 46 <= spZ regs -> spZ regs + 24 <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs) 8 (2 ^ 60) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs + 8) 8 (pi_sh (v + 32)) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs + 16) 8 (v + 32) ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (v + 32) keys ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (v + 40) n ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (keys + 8 * n) 8 kx ->
  (spZ regs + 24 <= v + 32 \/ v + 48 <= spZ regs) ->
  (keys + 8 * n + 8 <= v + 32 \/ v + 48 <= keys + 8 * n) ->
  keys + 8 * n + 8 <= spZ regs ->
  st_ok_pi (fx := fxc) SEGS VALb (Eimg (PI := PIb) (Ereg regs (pif_extra keys n kx))) (pif_ss pc)
    (restrict (w_H Wc) (@YK11.mkst fxc regs (Z_to_bv 64 (VALb A_TEXT + pc)) memc (seg_rom SEGS))).
Proof.
intros fxc Wc memc regs v keys n kx pc H19 H22 H24 H26 Hv Hv8 Hk4 Hk8 Hn Hkn Hkx Hsp1 Hsp2
  V0 V8 V16 [Hkr Vk] [Hnr Vn] Vx D1 D2 D3.
set (E := Eimg (PI := PIb) (Ereg regs (pif_extra keys n kx))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (pif_extra keys n kx)) i)
  by (intros i Hi; unfold E; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E19 : ew E 19 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E22 : ew E 22 = Z_to_bv 64 (v + 40)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 keys) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (keys + 8 * n)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 kx) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U19 : bv_unsigned (ew E 19) = v) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = v + 40) by (rewrite E22; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = keys) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = keys + 8 * n) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = kx) by (rewrite E35; apply unsigned_lit_small; lia).
assert (D19 : forall c, 0 <= v + c < 2 ^ 64 -> sv_denot E (SOff 19 c) = Z_to_bv 64 (v + c)).
{ intros c Hc. rewrite denot_lit_U, U_SOff, U19, zcanon_id by (unfold M64; lia). reflexivity. }
assert (DS : sv_denot E pif_slot = sv_denot E (SOff 34 0) /\ sv_denot E pif_slot2 = sv_denot E (SOff 34 0)).
{ assert (UK : U E (SOff 34 0) = keys + 8 * n) by (rewrite U_SOff, U34, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity).
  assert (US : U E (SAlu ALU_SLL (SOff 33 0) (SLit 3)) = 8 * n).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U33, Z.add_0_r.
    change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (zcanon_id n) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia. }
  assert (UK32 : U E (SOff 32 0) = keys) by (rewrite U_SOff, U32, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity).
  split; apply U_inj; unfold pif_slot, pif_slot2; rewrite U_SAlu; cbn [zalu_raw]; rewrite ?UK32, ?US, UK;
  rewrite zcanon_id by (unfold M64; lia); lia. }
rewrite (restrict_mkst_fx (fx := fxc)). unfold pif_ss.
apply (pa_entry_st_ok_full (fx := fxc) (L := Lb) (PI := PIb)).
- unfold pif_regs. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  rewrite H24, (pif_denot_shx E (SOff 19 40) SHADOW_OFF (v + 40) (D19 40 ltac:(lia)) E26) by (unfold SHADOW_OFF; lia).
  reflexivity.
- vm_compute. reflexivity.
- unfold pif_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 0 8 (SLit (2 ^ 60)) (2 ^ 60)); [reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact V0].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 8 8 (pif_shx (SOff 19 32)) (pi_sh (v + 32)));
        [ rewrite (pif_denot_shx E (SOff 19 32) SHADOW_OFF (v + 32) (D19 32 ltac:(lia)) E26) by (unfold SHADOW_OFF; lia); reflexivity
        | unfold pi_sh, SHADOW_OFF; cbn; Z.div_mod_to_equations; lia | zside | exact V8].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 16 8 (SOff 19 32) (v + 32)); [apply D19; lia | cbn; lia | zside | exact V16].
  + rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ v 32 8 (SOff 32 0) keys);
      [rewrite denot_lit_U, U_SOff, U32, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside | exact Vk].
  + rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (v + 40) 0 8 (SOff 33 0) n);
      [rewrite denot_lit_U, U_SOff, U33, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vn].
  + rewrite U34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (keys + 8 * n) 0 8 (SOff 35 0) kx);
      [rewrite denot_lit_U, U_SOff, U35, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vx].
- apply pairwise_disjoint_of_extents. unfold pif_regions. cbn [map]. unfold extent_of_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U19, U22, U34.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok pif_facts pif_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U26, U32, U34. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; lia.
  + cbn [f_alias pif_facts alias_ok]. destruct DS as [DS1 DS2]. split; [exact DS1|]. split; [exact DS2 | exact I].
Qed.

(* ---- the memory plumbing of the call ---- *)
(* a run whose regions have empty write windows leaves the memory as it was *)
Lemma pif_mem_eq : forall E (rs : smem) (m m' : word -> option byte),
  Forall (fun r => YP09.r_wlo r = YP09.r_whi r) rs -> frame_of E rs m m' -> m' = m.
Proof.
intros E rs m m' HW HF. apply functional_extensionality. intros x. apply HF. intros (r & Hin & Hr).
rewrite Forall_forall in HW. rewrite (HW r Hin) in Hr. lia.
Qed.

(* after a run of this block: the memory (restricted and full) is the one before it (no store) *)
Ltac pif_meq M MF :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict ?H ?m) (mrestrict _ ?m') |- _ =>
    assert (M : mrestrict H m' = mrestrict H m)
      by (refine (pif_mem_eq _ _ _ _ _ HFr); vm_compute; repeat constructor);
    clear HFr end;
  lazymatch goal with HF : frame_of _ _ ?m ?m' |- _ =>
    assert (MF : m' = m) by (refine (pif_mem_eq _ _ _ _ _ HF); vm_compute; repeat constructor);
    clear HF end;
  repeat match goal with HG : prh_glob _ _ _ _ _ _ _ |- _ => clear HG end.

Lemma pif_rdword_of_val : forall (H : word -> bool) (mem : word -> option byte) a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bb : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bb 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bb 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bb 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bb 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bb 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bb 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bb 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bb 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* fpre's read-only view rides through a journal (over any world relation R) whose footprint does not open the sink
   (its image clause, ajxR_img) *)
Lemma pif_rod_kept : forall (R : world SEGS -> world SEGS -> Prop) STK sp0 FP ly S Hp (W : world SEGS) mem md own
  lyc Sc Hpc (W' : world SEGS) mem' md' k,
  ajournal_xR (SK := SK) SEGS B prh_pst ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W' mem' md' k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem').
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W' mem' md' k HJ Hsk Hrod a Hro Hos Her.
rewrite (ajxR_img HJ a); [exact (Hrod a Hro Hos Her) | | exact Hos | exact Her | | apply fp_spares_closed; exact Hsk].
- destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img a Hr)].
- intros Hp'. exact (PIF_PSTRO a Hp' Hro).
Qed.

(* an address outside the image whose two views agree is the same byte, writable when it was *)
Lemma pif_same : forall (H H' : word -> bool) (m m' : word -> option byte) x,
  0 <= x < 2 ^ 64 -> ~ in_img SEGS x -> aview SEGS H' m' x = aview SEGS H m x ->
  pis_same SEGS (mrestrict H m) (mrestrict H' m') x.
Proof.
intros H H' m m' x Hx Hn E. pose proof (mbyte_of_aview SEGS H H' m m' x E) as M.
assert (R : mrestrict H' m' (Z_to_bv 64 x) = mrestrict H m (Z_to_bv 64 x)).
{ unfold mbyte in M. rewrite (seg_rom_none SEGS x Hx Hn) in M.
  destruct (mrestrict H' m' (Z_to_bv 64 x)), (mrestrict H m (Z_to_bv 64 x)); congruence. }
split; [exact M|]. unfold writable_at, wview. rewrite R. tauto.
Qed.

(* the pairwise disjointness of the blocks (and frames), against the block the call frees *)
Lemma pif_pw_blk : forall (f : Z * Z -> Z * Z) (l1 l2 R : list (Z * Z)) x y,
  pairwise zdisjoint (map f (l1 ++ x :: l2) ++ R) -> In y (l1 ++ l2) -> zdisjoint (f y) (f x).
Proof.
intros f l1 l2 R x y HP Hy. apply in_app_or in Hy as [Hy|Hy].
- apply in_split in Hy as (a & b & ->). apply (pairwise_zdisjoint_split _ _ _ HP).
  exists (map f a), (map f b), (map f l2 ++ R). left.
  rewrite !map_app. cbn [map]. repeat (first [rewrite <- app_assoc | rewrite <- app_comm_cons]). reflexivity.
- apply in_split in Hy as (a & b & ->). apply (pairwise_zdisjoint_split _ _ _ HP).
  exists (map f l1), (map f a), (map f b ++ R). right.
  rewrite !map_app. cbn [map]. rewrite ?map_app. cbn [map].
  repeat (first [rewrite <- app_assoc | rewrite <- app_comm_cons]). reflexivity.
Qed.

Lemma pif_pw_frm : forall (f : Z * Z -> Z * Z) (l1 l2 R : list (Z * Z)) x z,
  pairwise zdisjoint (map f (l1 ++ x :: l2) ++ R) -> In z R -> zdisjoint z (f x).
Proof.
intros f l1 l2 R x z HP Hz. apply in_split in Hz as (a & b & ->). apply (pairwise_zdisjoint_split _ _ _ HP).
exists (map f l1), (map f l2 ++ a), b. right.
rewrite !map_app. cbn [map]. repeat (first [rewrite <- app_assoc | rewrite <- app_comm_cons]). reflexivity.
Qed.

(* ---- list and ledger facts of the free ---- *)
Lemma pif_nodup_prefix : forall {A : Type} (l l' : list A), List.NoDup (l ++ l') -> List.NoDup l.
Proof.
intros A l l'. induction l as [|x l IH]; intros H; [constructor|].
cbn [app] in H. inversion H as [|y t Hn Hd]; subst. constructor; [|exact (IH Hd)].
intros Hx. apply Hn. apply in_or_app. left. exact Hx.
Qed.

Lemma pif_combine : forall {A C : Type} (l : list (A * C)), combine (map fst l) (map snd l) = l.
Proof. intros A C l. induction l as [|[a c] l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma pif_lsum_app : forall D1 D2, Ledger.lsum (D1 ++ D2) = Ledger.lsum D1 + Ledger.lsum D2.
Proof. induction D1 as [|[a k] D1 IH]; intros D2; cbn [app Ledger.lsum]; [reflexivity|]. rewrite IH. lia. Qed.

Lemma pif_lsum_perm : forall D D', Permutation D D' -> Ledger.lsum D = Ledger.lsum D'.
Proof.
intros D D' H. induction H as [|[a k] l l' _ IH|[a k] [b m] l|l l' l'' _ IH1 _ IH2];
  cbn [Ledger.lsum] in *; lia.
Qed.

Lemma pif_prh_held_free : forall t kk, 0 <= kk ->
  PRH_Charge.prh_held (t ++ [EFree (Z.to_nat kk)]) = PRH_Charge.prh_held t - kk.
Proof. intros t kk Hk. unfold PRH_Charge.prh_held. rewrite pif_held_free, pif_calls_free, Z2Nat.id by exact Hk. lia. Qed.

Lemma pif_bytes_free : forall lyc Sc ly2 S2 b1 b2 x0,
  ablocks B lyc Sc = b1 ++ x0 :: b2 -> ablocks B ly2 S2 = b1 ++ b2 ->
  blocks_bytes S2 = blocks_bytes Sc - snd x0.
Proof.
intros lyc Sc ly2 S2 b1 b2 x0 E1 E2.
rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B lyc Sc), E1, E2, !bsum_app, bsum_cons. lia.
Qed.

(* the blocks move of the prefix, extended by the free of one of its blocks *)
Lemma pif_bm_free : forall ly S lyc Sc ly2 S2 D0 Dfin tr0 rest dd kx kk b1 b2,
  rd_blocks_move B ly S lyc Sc D0 tr0 rest dd -> Permutation D0 (Dfin ++ [(kx, kk)]) ->
  ablocks B lyc Sc = b1 ++ (kx - cf_head, kk + cf_head) :: b2 -> ablocks B ly2 S2 = b1 ++ b2 ->
  frames S2 = frames Sc ->
  rd_blocks_move B ly S ly2 S2 Dfin (tr0 ++ [EFree (Z.to_nat kk)]) rest dd.
Proof.
intros ly S lyc Sc ly2 S2 D0 Dfin tr0 rest dd kx kk b1 b2 (H1 & H2 & H3 & H4) HP E1 E2 EF.
split; [intros a k Hin; apply H1; apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hin|].
split.
{ assert (HA : Permutation (prhReader_ab D0) (prhReader_ab (Dfin ++ [(kx, kk)])))
    by (unfold prhReader_ab; apply Permutation_map; exact HP).
  unfold prhReader_ab in HA, H2 |- *. rewrite map_app in HA. cbn [map fst snd] in HA.
  rewrite E2. apply (Permutation_app_inv b1 b2 _ (ablocks B ly S) (kx - cf_head, kk + cf_head)).
  rewrite <- E1. eapply perm_trans; [exact H2|].
  eapply perm_trans; [apply Permutation_app_tail; exact HA|].
  rewrite <- app_assoc. cbn [app]. apply Permutation_refl. }
split; [rewrite EF; exact H3|].
rewrite pif_hpeak_free. exact H4.
Qed.

(* the live requests the room sees after the free: the call state's, less the freed block's request (form (b)'s
   chaining fact, from the post's ablocks split; rs_live is the sizes of the allocator's blocks) *)
Lemma pif_live_free : forall lyc Sc ly2 S2 b1 b2 a z,
  ablocks B lyc Sc = b1 ++ (a, z) :: b2 -> ablocks B ly2 S2 = b1 ++ b2 ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) [PresetReqAt.HFr z]).
Proof.
intros lyc Sc ly2 S2 b1 b2 a z E1 E2.
assert (L1 : PresetRoom.rs_live (YGcfRoom.room_of_cf Sc) = map snd (ablocks B lyc Sc))
  by (unfold ablocks; rewrite map_map; reflexivity).
assert (L2 : PresetRoom.rs_live (YGcfRoom.room_of_cf S2) = map snd (ablocks B ly2 S2))
  by (unfold ablocks; rewrite map_map; reflexivity).
rewrite L1, L2, E1, E2. unfold PresetReqAt.hlive_from. cbn [fold_left PresetReqAt.hstep].
apply Permutation_sym. apply PresetReqAt.rm1_perm_cons.
rewrite !map_app. cbn [map snd]. apply Permutation_sym. apply Permutation_middle.
Qed.

(* the free's heap event, at the instance's head length *)
Lemma pif_hevs_free : forall kk, 0 <= kk ->
  PresetReqAt.rd_hevs [EFree (Z.to_nat kk)] = [PresetReqAt.HFr (kk + cf_head)].
Proof.
intros kk Hk. cbn [PresetReqAt.rd_hevs flat_map PresetReqAt.rd_hev app]. rewrite Z2Nat.id by exact Hk.
rewrite PIF_HEAD. reflexivity.
Qed.

Theorem pi_free_holds : forall d CTX0 CW, pi_free_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW.
Proof.
intros d CTX0 CW fxc fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
  lyc Sc Hpc Wc memc mdc k regs WS0 HJw HWS HPRE.
destruct HPRE as (Ho & HFP & HENT & HMNc & HFRM & HREGS & HRB & H21 & n & cap & acc & kids & keys & Di & ok0 &
  tr0 & D0 & Lamc & peakc & cntc & failc & ranc & kx & kk & HAFT & HPAT & HVSH & HLED & Hncap & HCONT & HDEP & HAP &
  HPERM & HSLOT & HKIN & HKNL & HKNB & HRUN & HPLED & HBM & HPOSB & HLIVE & HBB & HLOK & HLSD & HRL & HC24 &
  HGR & Hcapn & af & HFORD & HFLE).
subst o.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (AC6 : YK06.alloc_ceiling = 0x7fff7f800000) by reflexivity.
pose proof HREGS as (R9 & R19 & R18 & R8 & R20 & R26 & R27 & R25 & R23).
pose proof HRB as (R22 & R24 & V0 & V32 & V24 & V16 & V8).
pose proof HCONT as (HHDR & Hnacc & Hnc & Hcap54 & Hslots & Hok0 & HNDi & HAPDi & HMEMS).
unfold pi_ajR in HJw.
pose proof (ajxR_ar HJw) as HAR. pose proof (ajxR_ly HJw) as HLY. pose proof (ajxR_secs HJw) as HSEC.
pose proof (ajxR_rel HJw) as HWLE. pose proof (ajxR_io HJw) as HAOS. pose proof (ajxR_frs HJw) as HFRS0.
pose proof (ajxR_nev HJw) as HNEV. pose proof (ajxR_k HJw) as HK0. pose proof (ajxR_hi HJw) as HKA.
pose proof (ajxR_blk HJw) as HKB. pose proof (ajxR_img HJw) as HKI. pose proof (ajxR_frm HJw) as HKF.
pose proof (ajxR_gone HJw) as HKG. pose proof (ajxR_pres HJw) as Hpres. pose proof (ajxR_stk HJw) as Hastk.
pose proof (ajxR_extra HJw) as HKX. pose proof (ajxR_qt HJw) as HQT.
(* THE BUDGETED JOURNAL, at the walk's relation wle' segs RZ_cf: the runs take the empty-budget
   journal, so rebase it at the block's depot (YCbqGwild.ajournal_xw_rebaseR); HWD is the wild part's cover the step
   back needs (ajournal_xw_unbase0R) *)
pose proof (ajxR_wild HJw) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ.
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
pose proof HENT as (HMNe & HPKs & HPK24 & HCTX & HUC & HCUR & HCH & HPART & H10e & H11e & H12e & Hgp & Htp & HRD &
  Hptl & Hnth & HROOMe & HCH0 & HFRS & HROD & HCWe & HWRe & _).
pose proof HRD as (HFZ0 & HMU & HRU1 & HRU2 & HOKe & HFWIN & Hsq & Hqe & HRAq & HSRC & HHOME & HMAXR & HNODE &
  Hqv & Htv & Hvwin & HLEDe & HdM & HCNTe & HCEILe).
pose proof HNODE as (Hv4096 & Hv8 & HRWv & HZv & HATe & HAMv & HNOWN & HRAve).
pose proof HFRM as (Fsp & F3 & F4 & FV1 & FV2 & FV3 & FV4 & FV5 & FV6 & FV7 & FV8 & FV9 & FV10 & FV11 & FV12 & FV13 &
  Fwin & Fra & Fe0 & Fe16).
pose proof (@cf_head_nonneg cp) as CH0.
unfold PI_FRAME in Fsp.
(* the stack numbers: parse_items' bound covers its own frame and fuzz_free's *)
assert (HFF0 : 0 <= STK_fuzz_free)
  by (pose proof (pi_frame_nonneg F_fuzz_free); unfold STK_fuzz_free, zmaxl; cbn [fold_right]; lia).
assert (HSTK : STK_fuzz_free + 144 <= STK_parse_items d).
{ unfold STK_parse_items. rewrite FRPI. unfold PI_FRAME. pose proof (pi_frame_nonneg F_parse_value).
  assert (HLEAF : STK_fuzz_free <= LEAF_pv_pi) by (unfold LEAF_pv_pi, zmaxl; cbn [fold_right]; lia).
  assert (0 <= Z.of_nat (PjGrammar.MAXD - d) * (PRH_Base.pi_frame F_parse_value + 144))
    by (apply Z.mul_nonneg_nonneg; lia). lia. }
assert (Hsp0 : YM05.alloc_ceiling + 144 <= spZ regs0) by lia.
assert (Hsp1 : spZ regs0 + e <= 2 ^ 47) by lia.
(* the keys block, the key block and the node *)
destruct Hslots as [(Hc0 & _ & _) | (Hcp & Hkids & Hkeys)]; [lia|].
specialize (Hkeys eq_refl). unfold prh_lin in Hkids, Hkeys.
pose proof HLED as HND. apply prh_ledger_nodup in HND.
pose proof HLED as HHB. apply prh_ledger_blocks in HHB.
pose proof (proj1 (Forall_forall _ _) HHB _ Hkeys) as (K0 & Kin & Khp & K16 & Kv). cbn [fst snd] in K0, Kin, Khp, K16, Kv.
pose proof (proj1 (Forall_forall _ _) HHB _ HKIN) as (X0 & Xin & Xhp & X16 & Xv). cbn [fst snd] in X0, Xin, Xhp, X16, Xv.
assert (RS : forall z, 0 < z -> req_size z = z) by (intros z Hz; unfold req_size; destruct (Z.eqb_spec z 0); lia).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Kin) as (KB16 & KB4096 & KBc & KBapp & _).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Xin) as (XB16 & XB4096 & XBc & XBapp & _).
rewrite RS in KBc, KBapp by lia.
assert (XKK : 0 <= kk + cf_head) by lia.
pose proof (req_size_pos (kk + cf_head) XKK) as XRS.
pose proof HHDR as (Hrwv & HTy & HNum & HStr & HKd & HKy & HNn & HCp).
assert (Hv47 : v + 56 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMv; lia).
assert (Hkx64 : 0 <= kx < 2 ^ 64) by lia.
assert (Hkx0 : kx <> 0) by lia.
(* THE FREED BLOCK IS NONE OF THE ENTRY STATE'S: (kx, kk) is one of the blocks the prefix allocated (D0), and the
   prefix's blocks move says no such block is a block of S - so it is a temporary block of this call, outside FP *)
assert (HX0S : ~ In (kx - cf_head, kk + cf_head) (ablocks B ly S)).
{ destruct HBM as (HB1 & _). apply (HB1 kx kk). apply (Permutation_in _ (Permutation_sym HPERM)).
  apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
(* the regions are apart: the frame cells from the node (the node is outside the entry stack window), the slot
   from the node (pj_apartR of the keys block) and from the frame (a block lies below the stack) *)
assert (D1 : spZ regs + 24 <= v + 32 \/ v + 48 <= spZ regs).
{ apply pif_disj; [|lia|lia]. intros a Ha1 Ha2. apply (proj2 (HNOWN a ltac:(lia))). lia. }
assert (Hkin : In (keys, 8 * Z.of_nat cap) (pi_sblk true kids keys cap)).
{ unfold pi_sblk, kids_blkR, keys_blkR. replace (Z.of_nat cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn. right. left. reflexivity. }
assert (D2 : keys + 8 * Z.of_nat n + 8 <= v + 32 \/ v + 48 <= keys + 8 * Z.of_nat n).
{ apply pif_disj; [|lia|lia]. intros a Ha1 Ha2. apply (HAP _ a Hkin); [unfold pj_holdsR; cbn [fst snd]; lia | lia]. }
pose proof (pif_st_ok fxc Wc memc regs v keys (Z.of_nat n) kx (PIATb PI_O_FREE) R19 R22 R24 R26
  ltac:(lia) Hv8 ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) Hkx64 ltac:(lia) ltac:(lia)
  V0 V8 V16 HKy HNn HSLOT D1 D2 ltac:(lia)) as HS.
remember (Eimg (PI := PIb) (Ereg regs (pif_extra keys (Z.of_nat n) kx))) as E eqn:HE in HS.
assert (HEI : img_env VALb A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (pif_extra keys (Z.of_nat n) kx)) i)
  by (intros i Hi; rewrite HE; apply Eimg_low; exact Hi).
assert (EK : forall nk (rk : bv 5), Z.of_nat nk = bv_unsigned rk -> ew E nk = getr regs rk).
{ intros nk rk Hk. pose proof (bv_unsigned_in_range 5 rk) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
  rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ nk rk Hk). }
assert (E19 : ew E 19 = Z_to_bv 64 v) by (rewrite (EK 19%nat 19%bv eq_refl); exact R19).
assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EK 26%nat 26%bv eq_refl); exact R26).
assert (E32 : ew E 32 = Z_to_bv 64 keys) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat n)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (keys + 8 * Z.of_nat n)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 kx) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (U32 : bv_unsigned (ew E 32) = keys) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = Z.of_nat n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = keys + 8 * Z.of_nat n) by (rewrite E34; apply unsigned_lit_small; lia).
(* the two shadow entries: the node's 56 bytes (the pre's current shadow) and the key slot's 8, past the keys
   block's hidden head (pi_hshadow_law's field of AR_laws_x) *)
destruct (alx_hshadow _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Kin Khp) as [HBS _].
rewrite RS in HBS by lia. replace (keys - cf_head + cf_head) with keys in HBS by lia.
replace (8 * Z.of_nat cap + cf_head - cf_head) with (8 * Z.of_nat cap) in HBS by lia.
assert (HRAs : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (keys + 8 * Z.of_nat n) 8)
  by (apply (pif_ra_of_bs _ _ keys (8 * Z.of_nat cap)); [exact HBS | lia | Z.div_mod_to_equations; lia | lia]).
assert (HBx : U E pif_Bx = SHADOW_OFF) by (unfold pif_Bx; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS pif_Bx pif_SH E (mrestrict (w_H Wc) memc)).
{ unfold pif_SH. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range SEGS (w_H Wc) memc E pif_Bx 19 v 56 v 0 56 HVSH HBx);
      [rewrite (U_atom E 19 v E19) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMv. unfold SHADOW_OFF. lia.
  - apply (shent_ok_of_range SEGS (w_H Wc) memc E pif_Bx 34 (keys + 8 * Z.of_nat n) 8 (keys + 8 * Z.of_nat n) 0 8 HRAs HBx);
      [rewrite (U_atom E 34 _ E34) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in KBapp. unfold SHADOW_OFF in *. lia. }
unfold pi_goalR, cfg_at.
change (w64 (VALb A_TEXT + PIATb PI_O_FREE)) with (Z_to_bv 64 (VALb A_TEXT + PIATb PI_O_FREE)).
pose (RUN := PI_RUNR (fx := fxc) (SK := SK) (L := Lb) (PL := PLb) (PI := PIb) B prh_pst ARx LAWS).
pose (BR := paj_branchR (fx := fxc) (L := Lb) (PI := PIb) (wle' SEGS YGcfRehidePost.RZ_cf)).
(* RUN 1, 0x87ec8 .. 0x87f08: the shadow probe of v + 32 (0x87ed0, errpath 0x880e0, NOT TAKEN: the byte is the
   literal 0 under the node's entry mkSHE 19 0 56) and of v + 40 (0x87ed8, errpath 0x880e8, NOT TAKEN: same entry),
   the loads of n and keys, the slot address, its result-non-zero check 0x87ef8 (NOT TAKEN: keys >= 4096 by atom 32,
   the slot >= 4096 by atom 34), stopping at the 2 ^ 60 guard *)
pi_run RUN HS HJ SHOK.
{ unfold awr_ok. intros a (r & Hin & Ha). unfold pif_ss in Hin. cbn [ss_mem] in Hin. unfold pif_regions in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
pif_meq M1 MF1.
psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
{ (* 0x87f08 TAKEN would need (n + 2 ^ 60) >> 61 <> 0: impossible, n <= cap <= 2 ^ 54 *)
  exfalso. rewrite branch_ne_U, U_SAlu, U_SOff, U33 in Hc. cbn [zalu_raw] in Hc.
  rewrite (zcanon_id (Z.of_nat n + 1152921504606846976)) in Hc by (unfold M64; lia).
  change (Z.land (U E (SLit 61)) 63) with 61 in Hc. rewrite Z.shiftr_div_pow2 in Hc by lia.
  rewrite (Z.div_small (Z.of_nat n + 1152921504606846976) (2 ^ 61)) in Hc by lia.
  vm_compute in Hc. discriminate Hc. }
clear Hc.
(* RUN 2: 0x87f08 not taken, up to the wrap check 0x87f0c *)
pi_run RUN HS HJ SHOK.
{ unfold awr_ok. intros a (r & Hin & Ha). unfold pif_ss in Hin. cbn [ss_mem add_cond] in Hin. unfold pif_regions in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
pif_meq M2 MF2.
psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
{ (* 0x87f0c TAKEN would need keys + 8 n < keys: impossible *)
  exfalso. rewrite branch_ltu_U, (U_atom E 34 _ E34), (U_atom E 32 _ E32) in Hc by lia.
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* RUN 3: 0x87f0c not taken; the null check 0x87f10 (NOT TAKEN: keys >= 4096, atom 32), the alignment check
   0x87f18 (NOT TAKEN: the slot is 8-aligned, atom 34's al2 = 3), the slot's shadow probe 0x87f28 (errpath 0x880f0,
   NOT TAKEN: the byte is the literal 0 under mkSHE 34 0 8), the key load, the jal fuzz_free *)
pi_run RUN HS HJ SHOK.
{ unfold awr_ok. intros a (r & Hin & Ha). unfold pif_ss in Hin. cbn [ss_mem add_cond] in Hin. unfold pif_regions in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
pif_meq M3 MF3.
(* ==== THE CALL OF fuzz_free (0x87f30), the text tfuzz_free_specX (SRr' segs RZ_cf, a budgeted post): aj_call_xb_spR ==== *)
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msn) => rename msn into msC end.
assert (EQM : mrestrict (w_H Wc) (ms_mem msC) = mrestrict (w_H Wc) memc) by (rewrite M3, M2, M1; reflexivity).
(* the overlay is still normal at the call: the runs stored nothing *)
assert (HMNC : YAkMemnorm.memnorm SEGS (ms_mem msC)) by (rewrite MF3, MF2, MF1; exact HMNc).
try rewrite !wvb_collapse in HJ.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
assert (Usp : spZ (ms_regs msC) = spZ regs) by (unfold spZ; rewrite P2, (EK 2%nat 2%bv eq_refl); reflexivity).
assert (Us0 : s0Z (ms_regs msC) = q + 16)
  by (unfold s0Z; rewrite P8, (EK 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; lia).
assert (Ra0 : getr (ms_regs msC) 10 = w64 kx) by (rewrite P10, E35; reflexivity).
(* the cursor at the entry: its word at q is the entry cursor p, below alloc_ceiling (prh_cur_entry at parse_items,
   s0 = q + 16), so the text lies below q; its word at q + 8, the end text + len, is a data word of the run *)
pose proof HOKe as (Vpe & Vee & Vde & Hrwe & Hq8 & Ht0 & Htl & Hple & Hlen & HGtb & Hdqt & Hd032).
pose proof ((proj2 HCUR) F_parse_items (or_intror eq_refl)) as HW16.
unfold prh_s0 in HW16. rewrite FS0 in HW16. replace (q + 16 - 16) with q in HW16 by lia.
assert (Hpe : prh_word_entry W mem regs0 q p).
{ unfold prh_word_entry.
  destruct (Z.eqb_spec q (spZ regs0 - 8)) as [E8'|_]; [lia|].
  destruct (Z.eqb_spec q (spZ regs0 - 16)) as [E16'|_]; [lia|].
  apply (pif_rdword_of_val (w_H W) mem q p Vpe). lia. }
pose proof (HW16 p Hpe) as Hp_ac.
assert (Htq : text + len <= q) by lia.
assert (Hwe : prh_word_entry W mem regs0 (q + 8) (text + len)).
{ unfold prh_word_entry.
  destruct (Z.eqb_spec (q + 8) (spZ regs0 - 8)) as [E8'|_]; [lia|].
  destruct (Z.eqb_spec (q + 8) (spZ regs0 - 16)) as [E16'|_]; [lia|].
  apply (pif_rdword_of_val (w_H W) mem (q + 8) (text + len) Vee). lia. }
(* THE CURSOR SET (the batch kit 240b06ed4fd4): the trace of this free, with the data word text + len, is CW's (or its word is
   of this free, with the data word text + len, is CW's (or its word is pj_parse's code word, a FIXED trace by the closure's clause 4a) *)
assert (Hwe8 : prh_word_entry W mem regs0 (prh_s0 F_parse_items q - 8) (text + len))
  by (unfold prh_s0; rewrite FS0; replace (q + 16 - 8) with (q + 8) by lia; exact Hwe).
pose proof (HCWe F_parse_items (VALb A_TEXT + PIATb PI_O_FFREE + 4) (text + len) (or_intror eq_refl)
  (in_or_app _ _ _ (or_intror FSITE)) Hwe8) as HCWt.
(* the room for CW at this block's state: the entry's (pi_ent), across the prefix's journal, whose wild traces are
   all CW's (the pre's budget), so no fresh slot is used (YCbqGwild.ajournal_xw_roomR) *)
pose proof (YCbqGwild.ajournal_xw_roomR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CW 0 HJw HWRe HWS) as HROOMc.
change (0 - YCbqGwild.wfresh CW WS0)%nat with 0%nat in HROOMc.
(* the depot holds no repeat: AR_laws_x's field 25 (the kit's cut, YCbqG.v alx_depot_nodup) *)
pose proof (alx_depot_nodup _ _ _ LAWS lyc Sc Hpc Wc memc mdc HAR) as HNDc.
(* the frame chain fuzz_free's trace reads, from s0 = q + 16: one record (q + 16, text + len, the cursor), stopped by
   bad_next since the cursor is below q; or none, when q + 16 is at the stack top. Its trace is in the universe by
   the closure's cursor clause (one record) or its empty-chain clause; [pc0] when frame 0 is not ok. *)
destruct HAFT as (p1 & d1 & Hp1 & Hd1 & Vq0 & Vq8 & Vq16 & Hrwq).
pose proof HSRC as (_ & Ht4096 & _).
assert (HCU : exists ch1, achain lyc (aview SEGS (w_H Wc) (ms_mem msC)) (spZ regs) (q + 16) ch1 /\
  admits (as_universe B) (call_trace lyc (pc_free_ra0 (as_code B)) (ms_regs msC) ch1) Sc /\
  (In (call_trace lyc (pc_free_ra0 (as_code B)) (ms_regs msC) ch1) CW \/
   In (call_trace lyc (pc_free_ra0 (as_code B)) (ms_regs msC) ch1) (u_fix (as_universe B)))).
{ pose proof HUC as (CL1 & CL2 & CL3 & CL4a & CL4b).
  assert (Hr0 : raZ (ms_regs msC) = VALb A_TEXT + PIATb PI_O_FFREE + 4) by (unfold raZ; rewrite P1; vm_compute; reflexivity).
  assert (U1f : In [pc_free_ra0 (as_code B)] (u_fix (as_universe B))) by exact (CL1 RT_fuzz_free).
  assert (U1 : admits (as_universe B) [pc_free_ra0 (as_code B)] Sc /\
    (In [pc_free_ra0 (as_code B)] CW \/ In [pc_free_ra0 (as_code B)] (u_fix (as_universe B))))
    by (split; [apply pif_admits_fix; [cbn [length]; unfold kUnwindMax; lia | exact U1f] | right; exact U1f]).
  destruct (Z_lt_le_dec (q + 16) (ly_top lyc - 16)) as [Hlt | Hge].
  - exists [(q + 16, text + len, p1)]. split.
    + right. split; [lia|]. split; [exact Hlt|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|]. split.
      * cbn [fpchain]. split; [reflexivity|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|].
        split; [replace (q + 16 - 8) with (q + 8) by lia;
                apply (pif_rdword_of_val (w_H Wc) (ms_mem msC) (q + 8) (text + len)); [rewrite EQM; exact Vq8 | lia]|].
        split; [replace (q + 16 - 16) with q by lia;
                apply (pif_rdword_of_val (w_H Wc) (ms_mem msC) q p1); [rewrite EQM; exact Vq0 | lia]|].
        split; [lia|].
        unfold bad_next. replace (p1 <=? q + 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      * constructor; [cbn [fst]; lia | constructor].
    + unfold call_trace. destruct (frame0_ok lyc (ms_regs msC)); [|exact U1].
      unfold unwind_of_chain. cbn [flat_map app]. rewrite Hr0.
      pose proof (prh_univ_closure_wild B CTX0 F_parse_items (VALb A_TEXT + PIATb PI_O_FFREE + 4) (text + len) HUC
        (or_intror eq_refl) (in_or_app _ _ _ (or_intror FSITE))) as UI.
      destruct HCWt as [HCW | HCD].
      * unfold prh_trace in UI, HCW. cbn [flat_map app] in UI, HCW.
        exact (conj (YCbqGwild.wild_room_admits _ CW 0 Sc _ HNDc HROOMc UI (or_introl HCW)) (or_introl HCW)).
      * pose proof (prh_univ_closure_cur B CTX0 F_parse_items (VALb A_TEXT + PIATb PI_O_FFREE + 4) (text + len) HUC
          (or_intror eq_refl) (in_or_app _ _ _ (or_intror FSITE)) HCD) as U.
        unfold prh_trace in U. cbn [flat_map app] in U.
        exact (conj (pif_admits_fix _ _ Sc ltac:(apply firstn_le_length) U) (or_intror U)).
  - exists []. split.
    + left. split; [right; left; lia | reflexivity].
    + unfold call_trace. destruct (frame0_ok lyc (ms_regs msC)); [|exact U1].
      unfold unwind_of_chain. cbn [flat_map app]. rewrite Hr0.
      pose proof (CL2 F_parse_items RT_fuzz_free (VALb A_TEXT + PIATb PI_O_FFREE + 4) FSITE) as U.
      unfold prh_trace in U. cbn [flat_map app prh_pc0] in U.
      exact (conj (pif_admits_fix _ _ Sc ltac:(apply firstn_le_length) U) (or_intror U)). }
destruct HCU as (ch1 & HCH1 & HUNIV & HTRK).
pose proof (@pa_segs_low _ _ PIb) as Hsegs.
assert (Hr0c : raZ (ms_regs msC) < YM05.alloc_ceiling).
{ assert (Hr0 : raZ (ms_regs msC) = VALb A_TEXT + PIATb PI_O_FFREE + 4) by (unfold raZ; rewrite P1; vm_compute; reflexivity).
  assert (Hr0v : VALb A_TEXT + PIATb PI_O_FFREE + 4 < 2 ^ 40) by (vm_compute; reflexivity). lia. }
(* THE GRANTED RUN: the prefix ate one grant per call (pi_grant), and the missing colon is the grammar's refusal, so
   the all-granted run is this run (PItems_ledk1.pik1_run_granted), and its trace is prhPi_gtrace *)
assert (HGRUN : fst (PjGrammar.jr_items prh_jr_strtod d true (rest_atR tb text p) []) = (None, tr0 ++ [EFree (Z.to_nat kk)])).
{ pose proof (HRUN []) as HR0. rewrite app_nil_r, HGR in HR0.
  exact (PItems_ledk1.pik1_run_granted _ _ _ _ _ _ (PjGrammar.agrees_jr_items _ _ _ _) HR0). }
assert (HGT : PRH_Charge.prhPi_gtrace d true (rest_atR tb text p) = tr0 ++ [EFree (Z.to_nat kk)])
  by (unfold PRH_Charge.prhPi_gtrace; rewrite HGRUN; reflexivity).
assert (Hkk0 : 0 <= kk) by (clear - X0; lia).
(* THE HULL BUDGET of the free (route (b)): the free makes no event, and its block lies inside the entry's all-granted
   list tr0 ++ [EFree kk] (pi_ent's budget, HGT), whose prefix tr0 the block has used (pi_posb) *)
assert (HHBc : PresetHullBudget.hull_budget Sc []).
{ pose proof HENT as HHB0. apply pi_ent_hull in HHB0. rewrite HGT, PresetReqAt.rd_hevs_app in HHB0.
  exact (PItems_posb.pi_posb_budget_nil S Sc tr0 _ _ HHB0 HPOSB eq_refl). }
(* back to the budgeted journal from S at WS0 (the runs stored nothing), then the call of a BUDGETED callee by the call
   rule over the walk's relation (fuzz_free's text concludes SRr' segs RZ_cf, its post at wle') *)
pose proof (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD) as HJb.
eapply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
{ eapply (YCbqGwild.aj_call_xb_spR (SK := SK) SEGS B prh_pst ARx LAWS Hsegs (wle' SEGS YGcfRehidePost.RZ_cf)
    (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc E _ msC
    (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v) ly S Hp W mem md [] lyc Sc Hpc _ k WS0
    STK_fuzz_free _ (- (PI_FRAME + e)) _ ch1 _ _ HS eq_refl HJb).
  - rewrite Usp, Fsp. unfold PI_FRAME. lia.
  - unfold PI_FRAME. rewrite Z.mod_opp_l_z; [reflexivity | lia | rewrite Z.add_mod, Fe16 by lia; reflexivity].
  - unfold PI_FRAME. lia.
  - exact HFF0.
  - unfold PI_FRAME. lia.
  - rewrite P3, (EK 3%nat 3%bv eq_refl), F3. exact Hgp.
  - rewrite P4, (EK 4%nat 4%bv eq_refl), F4. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - vm_compute. discriminate.
  - replace (spZ regs0 + e + - (PI_FRAME + e)) with (spZ regs) by (unfold PI_FRAME; lia). rewrite Us0. exact HCH1.
  - intros HPRE1. cbn [ss_pc setpc].
    (* form (b): no entry position; the room, the class-24 count and the hull budget are asked for the non-NULL free
       only *)
    refine (TFREE fxc most own lyc Sc Hpc Wc (ms_regs msC) (ms_mem msC) _ ch1 kx kk Lamc peakc cntc
      failc ranc _ (fun _ => HRL) (fun _ => HC24) (fun _ => HHBc) HUNIV Ra0 (or_intror HKIN) _).
    + split; [exact HPRE1|]. split.
      { apply (pif_rod_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); [|exact HROD].
        intros (r & Hr & H0). cbn [rd_fp In] in Hr.
        destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in H0; lia. }
      pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
      split; [rewrite Usp; lia|]. split; [exact Hr0c|].
      (* FRM0-ENTRY: the rounding mode at the call is the block's, zero by pi_fpok *)
      exact (proj1 HFP).
    + rewrite MF3, MF2, MF1. exact HLED.
  - intros a Ha. replace (kx =? 0) with false in Ha by (symmetry; apply Z.eqb_neq; exact Hkx0).
    destruct Ha as (r & Hr & Ha). cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    right. left. exists (kx - cf_head), (kk + cf_head). split; [exact Xin|]. split; [exact HX0S | exact Ha]. }
(* ==== back at the return site 0x87f34 ==== *)
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HPW1 & HJ2 & HJc & HP2 & HQF & HMN2).
(* fuzz_free's post (a conjunction that grows; the text has no record), read by the type of each conjunct *)
cbv beta in HQF.
repeat match type of HQF with _ /\ _ => let Hq := fresh "HQc" in destruct HQF as [Hq HQF] end.
lazymatch goal with Hq : PresetHullBudget.hull_used Sc S2 [] |- _ => rename Hq into HHU2 end.
lazymatch goal with Hq : _ -> room_live_cf S2 |- _ => rename Hq into HRL2 end.
lazymatch goal with Hq : (_ = 0 /\ _) \/ _ |- _ => rename Hq into HQ2 end.
destruct HQ2 as [(Hk0 & _) | (_ & EHp2 & HC24e & (b1 & b2 & Eab1 & Eab2) & l1 & l2 & ELam & HLED2)];
  [exfalso; exact (Hkx0 Hk0)|].
replace (kx =? 0) with false in HJc by (symmetry; apply Z.eqb_neq; exact Hkx0).
replace (spZ regs0 + e + - (PI_FRAME + e)) with (spZ regs) in HJc by (unfold PI_FRAME; lia).
pose proof (ajxR_ar HJc) as JAR. pose proof (ajxR_ly HJc) as JLY. pose proof (ajxR_secs HJc) as JSEC.
pose proof (ajxR_rel HJc) as JWLE. pose proof (ajxR_io HJc) as JAOS. pose proof (ajxR_frs HJc) as JFR.
pose proof (ajxR_nev HJc) as JNEV. pose proof (ajxR_k HJc) as JK. pose proof (ajxR_hi HJc) as JSTK.
pose proof (ajxR_blk HJc) as JBLK. pose proof (ajxR_img HJc) as JIMG. pose proof (ajxR_frm HJc) as JFRM.
pose proof (ajxR_gone HJc) as JFREE. pose proof (ajxR_pres HJc) as JPRES. pose proof (ajxR_stk HJc) as JASTK.
pose proof (ajxR_extra HJc) as JEXT. pose proof (ajxR_qt HJc) as JQT.
assert (AVc : forall x, aview SEGS (w_H Wc) (ms_mem msC) x = aview SEGS (w_H Wc) memc x)
  by (intros x; unfold aview, mbyte; rewrite EQM; reflexivity).
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)). rewrite <- restrict_mkst_fx in HS2.
remember (havoc E 36 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS2.
assert (HEIq : img_env VALb A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n0, (n0 < 36)%nat -> ew E2 n0 = ew E n0) by (intros n0 Hn0; rewrite HE2; apply ew_havoc_old; exact Hn0).
clear HE2.
assert (SHOKq : sh_ok SEGS pif_Bx [] E2 (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
clear HS SHOK HJ HJb. rename HS2 into HS. rename SHOKq into SHOK.
pose proof (ajxR_wild HJ2) as HWD2.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HJ.
pose (RUNTO := PI_RUNTOR (fx := fxc) (SK := SK) (L := Lb) (PL := PLb) (PI := PIb) B prh_pst ARx LAWS).
(* RUN 4: the `j` to the epilogue, res = s5 = -1 *)
pi_run_to RUNTO HS HJ SHOK (PIATb PI_O_EPI).
{ apply awr_ok_nil. }
pif_meq M4 MF4.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) => rename msn into msE end.
assert (HMNE : YAkMemnorm.memnorm SEGS (ms_mem msE)) by (rewrite MF4; exact (HMN2 HMNC)).
prreg HS (21%bv : bv 5) R21'. prreg HS (2%bv : bv 5) R2'. prreg HS (3%bv : bv 5) R3'. prreg HS (4%bv : bv 5) R4'.
assert (Rk21 : getr (ms_regs msE) 21 = w64 (-1)) by (rewrite R21', OLD2, (EK 21%nat 21%bv eq_refl) by lia; exact H21).
assert (Uspe : spZ (ms_regs msE) = spZ regs)
  by (unfold spZ; rewrite R2', OLD2, (EK 2%nat 2%bv eq_refl) by lia; reflexivity).
assert (AVe : forall x, aview SEGS (w_H W2) (ms_mem msE) x = aview SEGS (w_H W2) mem2 x)
  by (intros x; unfold aview, mbyte; rewrite M4; reflexivity).
(* what the call keeps: above the callee's window (the frame, the cursor cells, the caller window) *)
assert (KSTK : forall x, spZ regs <= x < 2 ^ 47 -> aview SEGS (w_H W2) (ms_mem msE) x = aview SEGS (w_H Wc) memc x).
{ intros x Hx. rewrite AVe, (JSTK x ltac:(rewrite ?AC6; lia) ltac:(lia)). apply AVc. }
(* every allocator block of the call state other than the freed one: kept (block clause), outside the freed
   block (the separation law), outside the image *)
assert (KBLK : forall p0 n0 x, In (p0, n0) (ablocks B lyc Sc) -> (p0, n0) <> (kx - cf_head, kk + cf_head) ->
  p0 <= x < p0 + req_size n0 -> pis_same SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) (ms_mem msE)) x).
{ intros p0 n0 x Hin Hne Hx.
  assert (Hin2 : In (p0, n0) (b1 ++ b2)).
  { rewrite Eab1 in Hin. apply in_app_or in Hin as [H|[H|H]];
      [apply in_or_app; left; exact H | exfalso; exact (Hne (eq_sym H)) | apply in_or_app; right; exact H]. }
  destruct (alx_sep _ _ _ LAWS lyc Sc Hpc Wc memc mdc HAR) as [Hpw _]. rewrite Eab1 in Hpw.
  pose proof (pif_pw_blk (fun b => (fst b, req_size (snd b))) b1 b2 _ _ _ Hpw Hin2) as Hdj.
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Hin) as (_ & P4096 & Pc & _).
  assert (HnFP : ~ inFP (ablocks_fp [(kx - cf_head, kk + cf_head)]) x).
  { intros (r & Hr & Ha). cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha. lia. }
  assert (JB : aview SEGS (w_H W2) mem2 x = aview SEGS (w_H Wc) (ms_mem msC) x).
  { assert (Hin3 : In (p0, n0) (ablocks B ly2 S2)) by (rewrite Eab2; exact Hin2).
    pose proof (JBLK p0 n0 (x - p0) Hin Hin3 ltac:(lia)) as JB.
    replace (p0 + (x - p0)) with x in JB by lia. exact (JB HnFP). }
  apply pif_same; [rewrite ?AC6 in Pc; lia | |].
  - destruct (alx_client_img _ _ _ LAWS lyc Sc Hpc Wc memc mdc x HAR
      (or_introl (ex_intro _ p0 (ex_intro _ n0 (conj Hin Hx))))) as [_ Hn]. exact Hn.
  - rewrite AVe, JB. apply AVc. }
(* every fake frame of the call state: kept (frames clause), apart from the freed block, outside the image *)
assert (KFRM : forall cid pos x, In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid ->
  pis_same SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) (ms_mem msE)) x).
{ intros cid pos x Hin Hx.
  destruct (alx_sep _ _ _ LAWS lyc Sc Hpc Wc memc mdc HAR) as [Hpw Hfb]. rewrite Eab1 in Hpw.
  assert (Hz : In (frame_addr lyc cid pos, fs_frame_bytes cid)
    (map (fun f => (frame_addr lyc (fst f) (snd f), fs_frame_bytes (fst f))) (frames Sc))).
  { apply in_map_iff. exists (cid, pos). split; [reflexivity | exact Hin]. }
  pose proof (pif_pw_frm (fun b => (fst b, req_size (snd b))) b1 b2 _ _ _ Hpw Hz) as Hdj.
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
  assert (HnFP : ~ inFP (ablocks_fp [(kx - cf_head, kk + cf_head)]) x).
  { intros (r & Hr & Ha). cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha. lia. }
  pose proof (proj1 (Forall_forall _ _) Hfb (cid, pos) Hin) as [F1 F2]. cbn [fst snd] in F1, F2.
  apply pif_same; [rewrite ?AC6 in F2; lia | |].
  - destruct (alx_client_img _ _ _ LAWS lyc Sc Hpc Wc memc mdc x HAR
      (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Hx)))))) as [_ Hn]. exact Hn.
  - rewrite AVe, (JFRM cid pos x Hin (or_introl Hx) HnFP). apply AVc. }
(* the node's 56 bytes: wherever the entry put it (a block of Lam, a block of S, a fake frame of S; never the
   caller window, rd_pre's window clause), that block or frame is still one of the call state and is not the
   freed block, which is none of S *)
assert (KNODE : forall x, v <= x < v + 56 ->
  pis_same SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) (ms_mem msE)) x).
{ intros x Hx.
  destruct HATe as [(a0 & k0 & Hin & H1 & H2) | [(b0 & m0 & Hin & _ & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
  - pose proof HLEDe as HHBe. apply prh_ledger_blocks in HHBe.
    pose proof (proj1 (Forall_forall _ _) HHBe (a0, k0) Hin) as (Ek0 & Ein & _). cbn [fst snd] in Ek0, Ein.
    assert (Hc : In (a0 - cf_head, k0 + cf_head) (ablocks B lyc Sc)).
    { destruct HBM as (_ & HB2 & _). apply (Permutation_in _ (Permutation_sym HB2)). apply in_or_app. right. exact Ein. }
    apply (KBLK _ _ x Hc).
    + intros E0. rewrite E0 in Ein. exact (HX0S Ein).
    + assert (Hz0 : 0 <= k0 + cf_head) by lia. pose proof (req_size_pos _ Hz0). lia.
  - assert (Hc : In (b0, m0) (ablocks B lyc Sc)).
    { destruct HBM as (_ & HB2 & _). apply (Permutation_in _ (Permutation_sym HB2)). apply in_or_app. right. exact Hin. }
    apply (KBLK _ _ x Hc).
    + intros E0. rewrite E0 in Hin. exact (HX0S Hin).
    + pose proof (req_size_pos m0 ltac:(lia)). lia.
  - assert (Hc : In (cid, pos) (frames Sc)).
    { destruct HBM as (_ & _ & HB3 & _). apply (Permutation_in _ (Permutation_sym HB3)). exact Hin. }
    pose proof HLY as (_ & _ & _ & _ & _ & EF & _).
    apply (KFRM cid pos x Hc). unfold frame_addr in *. rewrite EF. lia.
  - exfalso. lia. }
(* the nesting is below MAXD: at MAXD the run would refuse with no event, not with the free *)
assert (HdMAX : (d < PjGrammar.MAXD)%nat).
{ pose proof (HRUN []) as HR0. unfold jr_items, jr_cont in HR0.
  lazymatch type of HR0 with context [Nat.ltb PjGrammar.MAXD ?x] => destruct (Nat.ltb PjGrammar.MAXD x) eqn:EM end.
  - exfalso. apply (f_equal (fun r => snd (fst r))) in HR0. cbn in HR0. destruct tr0; discriminate HR0.
  - apply Nat.ltb_ge in EM. lia. }
pmkst HS.
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |} _ =>
  replace pcw with (w64 (VALb A_TEXT + PIATb PI_O_EPI)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
try rewrite !wvb_collapse in HJ.
(* ==== the epilogue, PItems_pres.v's pi_epi_spec, at res = -1 ==== *)
pose proof (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD2) as HJe.
(* THE BUDGET at the epilogue: WS0's traces are CW's (the pre), and the free stored at most its own trace tr (its
   post's wbudget [tr] 0): CW's, or FIXED, which then leaves the budget (YCbqG.ajournal_xw_fix1R) *)
assert (HJE : exists WSe, ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
    (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v)
    ly S Hp W mem md [] ly2 S2 Hp2 W2 (ms_mem msE) (with_vm_backing (m_vm_lazy md2) mat2 md2) (k + k1) WSe /\
    YCbqGwild.wbudget CW 0 WSe).
{ unfold YCbqGwild.wbudget in HPW1.
  pose proof (YCbqGwild.wfresh_zero_incl _ _ (proj1 (Nat.le_0_r _) HPW1)) as Hi.
  (* the wider budget WS0 ++ [tr] (YCbqG.ajournal_xw_incl, over R: ajx_budgetR) *)
  pose proof (wild_incl_mono _ _ (WS0 ++ WS1) (WS0 ++ [call_trace lyc (pc_free_ra0 (as_code B)) (ms_regs msC) ch1])
    (incl_app (incl_appl _ (incl_refl _)) (incl_appr _ Hi)) (ajxR_wild HJe)) as Hw1.
  destruct HTRK as [HinCW | Hfix].
  - exists (WS0 ++ [call_trace lyc (pc_free_ra0 (as_code B)) (ms_regs msC) ch1]). split; [exact (ajx_budgetR _ HJe Hw1)|].
    change 0%nat with (0 + 0)%nat. apply YCbqGwild.wbudget_app; [exact HWS|].
    unfold YCbqGwild.wbudget. rewrite (YCbqGwild.wfresh_one_in _ _ HinCW). lia.
  - exists WS0. split; [exact (ajournal_xw_fix1R Hfix (ajx_budgetR _ HJe Hw1)) | exact HWS]. }
destruct HJE as (WSe & HJe2 & HBe).
apply (HEPI d (YCbqGwild.wbudget CW 0) fxc fx0 ly S Hp W mem md regs0 e q v _ ly2 S2 Hp2 W2 _ _ (k + k1) _ (-1)
  WSe HJe2 HBe).
unfold pi_epi_pre. split; [exact HFP|]. split; [exact HMNE|].
split.
{ (* the frame, kept above the callee's window *)
  assert (VK : forall o0 w, 40 <= o0 -> o0 + 8 <= 144 ->
    val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs + o0) 8 w ->
    val_mem SEGS (mrestrict (w_H W2) (ms_mem msE)) (spZ (ms_regs msE) + o0) 8 w).
  { intros o0 w Ho1 Ho2 Hv kk0 Hk0. rewrite Uspe.
    rewrite (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc (ms_mem msE) (spZ regs + o0 + Z.of_nat kk0));
      [exact (Hv kk0 Hk0) | apply KSTK; lia]. }
  split; [rewrite Uspe; unfold PI_FRAME; lia|].
  split; [rewrite R3', OLD2, (EK 3%nat 3%bv eq_refl) by lia; exact F3|].
  split; [rewrite R4', OLD2, (EK 4%nat 4%bv eq_refl) by lia; exact F4|].
  split; [apply VK; [lia | lia | exact FV1]|]. split; [apply VK; [lia | lia | exact FV2]|].
  split; [apply VK; [lia | lia | exact FV3]|]. split; [apply VK; [lia | lia | exact FV4]|].
  split; [apply VK; [lia | lia | exact FV5]|]. split; [apply VK; [lia | lia | exact FV6]|].
  split; [apply VK; [lia | lia | exact FV7]|]. split; [apply VK; [lia | lia | exact FV8]|].
  split; [apply VK; [lia | lia | exact FV9]|]. split; [apply VK; [lia | lia | exact FV10]|].
  split; [apply VK; [lia | lia | exact FV11]|]. split; [apply VK; [lia | lia | exact FV12]|].
  split; [apply VK; [lia | lia | exact FV13]|].
  split; [intros a Ha Hn; rewrite (KSTK a ltac:(lia)); exact (Fwin a Ha Hn)|].
  exact (conj Fra (conj Fe0 Fe16)). }
split; [exact Rk21|].
split; [apply PIF_QS|].
intros regs' H10'.
(* ==== the text's post (pi_post = tpiP_Q), its None arm: the run refused with the free event ==== *)
pose proof HPLED as HPLu. unfold pi_led, rd_ledger_move in HPLu. destruct HPLu as (_ & _ & _ & HPL & _).
assert (HPERM' : Permutation D0 ((pi_sblk true kids keys cap ++ Di) ++ [(kx, kk)])) by (rewrite <- app_assoc; exact HPERM).
assert (HND0 : List.NoDup (map fst D0)).
{ pose proof HND as HNDl. apply NoDup_ListNoDup in HNDl.
  pose proof (Permutation_NoDup (Permutation_map fst HPL) HNDl) as H0. rewrite map_app in H0.
  exact (pif_nodup_prefix _ _ H0). }
pose proof (Permutation_NoDup (Permutation_map fst HPERM') HND0) as HNDF. rewrite map_app in HNDF. cbn [map fst] in HNDF.
assert (HkxF : ~ In kx (map fst (pi_sblk true kids keys cap ++ Di))).
{ intros Hin. apply (NoDup_remove_2 _ [] kx HNDF). rewrite app_nil_r. exact Hin. }
assert (HNDD : NoDup (pi_sblk true kids keys cap ++ Di))
  by (apply NoDup_ListNoDup; exact (NoDup_map_inv _ _ (pif_nodup_prefix _ _ HNDF))).
(* the live requests and the position after the free (form (b)): fuzz_free's p <> 0 arm composed onto the block's
   pi_live / pi_posb over tr0, the free's own event being rd_hevs [EFree kk] = [HFr (kk + cf_head)]; the hull use
   extended by the free's (its post keeps both meters, and HFr counts nothing: hull_count_fr) *)
assert (HLV2 : PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
  (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) (tr0 ++ [EFree (Z.to_nat kk)])).
{ apply (PItems_posb.pi_live_call _ (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) _ tr0 _ HLIVE).
  rewrite (pif_hevs_free kk Hkk0). exact (pif_live_free lyc Sc ly2 S2 b1 b2 _ _ Eab1 Eab2). }
assert (HPB2 : PItems_posb.pi_posb S S2 (tr0 ++ [EFree (Z.to_nat kk)])).
{ apply (PItems_posb.pi_posb_call S Sc S2 tr0 _ HPOSB); rewrite (pif_hevs_free kk Hkk0).
  - match goal with Hq : kx <> 0 -> _ |- _ => exact (Hq Hkx0) end.
  - destruct (PresetHullBudget.hull_count_fr (kk + cf_head)) as [Nf Tf].
    apply (PresetHullBudget.hull_used_weaken _ _ [] _ HHU2).
    + rewrite Nf, PresetHullBudget.hull_nsec_nil. apply Nat.le_refl.
    + rewrite Tf, PresetHullBudget.hull_tsec_nil. apply Z.le_refl. }
(* THE HULL USE over the whole call's trace, which is the all-granted one (HGT) *)
assert (HHULL : PresetHullBudget.hull_used S S2
  (PresetReqAt.rd_hevs (PRH_Charge.prhPi_gtrace d true (rest_atR tb text p))))
  by (rewrite HGT; exact (PItems_posb.pi_posb_hull _ _ _ HPB2)).
assert (HGNT : prh_granted ok0 cnt fail (PjGrammar.calls tr0)) by (rewrite HGR; apply PItems_ledk1.pik1_grant_granted).
assert (HRAN : ranc = ran) by exact (PItems_ledk1.pik1_move_ran _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGNT HPLED).
(* the run, the ledger at the epilogue's memory, its move over the WHOLE call's granted trace (a granted move is
   priced 0 at any granted trace), the bytes and the net bytes *)
pose proof (HRUN []) as FRUN. rewrite app_nil_r in FRUN.
pose proof HLED2 as FLED. rewrite <- MF4 in FLED.
pose proof (pif_led_free Lam peak cnt fail ran most ok0 (PRH_Charge.prhPi_gtrace d true (rest_atR tb text p)) tr0 D0
  Lamc peakc cntc failc ranc _ l1 l2 kx kk
  (PItems_ledk1.pik1_move_regt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGNT HPLED) HPERM' ELam Hkk0) as FLM.
assert (FBY : blocks_bytes S2 <= blocks_bytes S + PRH_Charge.prh_held (tr0 ++ [EFree (Z.to_nat kk)])).
{ rewrite (pif_bytes_free lyc Sc ly2 S2 b1 b2 _ Eab1 Eab2), pif_prh_held_free by lia. cbn [snd]. lia. }
assert (FLS : Ledger.lsum (pi_sblk true kids keys cap ++ Di) = PjGrammar.held (tr0 ++ [EFree (Z.to_nat kk)])).
{ rewrite pif_held_free, Z2Nat.id by lia. pose proof (pif_lsum_perm _ _ HPERM') as HL.
  rewrite pif_lsum_app in HL. cbn [Ledger.lsum] in HL. lia. }
(* the half-built container plus the key slot: pis_exit_open at the call state, carried by its footprint *)
assert (Enf : Z.of_nat (length (map snd acc)) = Z.of_nat n) by (rewrite length_map, <- Hnacc; reflexivity).
assert (HOP : pis_open SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) v true 0 kids keys (Z.of_nat cap)
  (Z.of_nat (length (map snd acc))) (map snd acc) (map fst acc) Di).
{ split; [exact HNDD|]. split.
  { intros b x Hb Hx. apply in_app_or in Hb as [Hb|Hb]; [exact (HAP b x Hb Hx) | exact (HAPDi b x Hb Hx)]. }
  rewrite Enf. split; [exact HHDR|].
  split.
  { split; [right; reflexivity|]. split; [lia|]. split; [intros Hc; lia|].
    intros _. split; [exact Hkids|]. intros _. exact Hkeys. }
  split; [intros Hf; discriminate Hf|].
  split; [rewrite !length_map; reflexivity|]. rewrite pif_combine. exact HMEMS. }
(* the two frame facts of the container's footprint from the call state to the epilogue's: its blocks stay the
   ledger's (the freed key block is none of them), and its bytes keep their values *)
assert (HLBF : forall a k0, In (a, k0) (pis_slots true kids keys (Z.of_nat cap) ++ Di) -> prh_lin Lamc a k0 ->
  prh_lin (l1 ++ l2) a k0).
{ intros a k0 Hin Hl. unfold prh_lin in Hl |- *. rewrite ELam in Hl.
  apply in_app_or in Hl as [Hl|[Hl|Hl]]; [apply in_or_app; left; exact Hl | | apply in_or_app; right; exact Hl].
  exfalso. injection Hl as Ia Ib. rewrite <- Ia, <- Ib in Hin.
  apply HkxF. apply in_map_iff. exists (kx, kk). split; [reflexivity | exact Hin].
}
assert (HSMF : forall x, pj_footR v (pis_slots true kids keys (Z.of_nat cap) ++ Di) x ->
  pis_same SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) (ms_mem msE)) x).
{ intros x [Hx | ([b0 m0] & Hbb & Hx)].
  + exact (KNODE x Hx).
  + unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    assert (HinD0 : In (b0, m0) D0) by (apply (Permutation_in _ (Permutation_sym HPERM')); apply in_or_app; left; exact Hbb).
    assert (HinL : In (b0, m0) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact HinD0).
    pose proof (proj1 (Forall_forall _ _) HHB (b0, m0) HinL) as (Em0 & Ein & _). cbn [fst snd] in Em0, Ein.
    apply (KBLK _ _ x Ein).
    * intros E0. injection E0 as Ia Ib. apply HkxF. apply in_map_iff. exists (b0, m0). split; [cbn; lia | exact Hbb].
    * assert (Hz0 : 0 <= m0 + cf_head) by lia. pose proof (req_size_pos _ Hz0). lia.
}
(* the text's post, BUILT THROUGH ITS RECORD (tpiP_Q_of_R; the arm through tpiP_ANone_of_R). THE INJECTED READING: the free
   path refused no call, its prefix is all-granted (pi_grant_granted). The holes, in order: the outcome, then the
   arm's free order, cursor and partial tree. *)
unfold pi_post.
refine (tpiP_Q_of_R (ok := ok0) (res := None) (tr := tr0 ++ [EFree (Z.to_nat kk)]) (okr := [])
  (D := pi_sblk true kids keys cap ++ Di) (Lam' := l1 ++ l2) (peak' := peakc) (cnt' := cntc) (fail' := failc)
  (ran' := ranc) _
  {| tpiP_run := FRUN; tpiP_ledger := FLED; tpiP_room := HRL2 Hkx0; tpiP_hull := HHULL; tpiP_live := HLV2;
     tpiP_pos := PItems_posb.pi_posb_post _ _ _ HPB2; tpiP_outcome := _;
     tpiP_injected := fun _ _ _ _ _ _ _ _ _ _ => pi_grant_granted ok0 tr0 cnt fail _ HGR;
     tpiP_ledger_move := FLM;
     tpiP_blocks_move := pif_bm_free ly S lyc Sc ly2 S2 D0 _ tr0 _ d kx kk b1 b2 HBM HPERM' Eab1 Eab2 JFR;
     tpiP_bytes := FBY; tpiP_lsum := FLS;
     tpiP_arm := tpiP_ANone_of_R {| tpiPn_ret := H10'; tpiPn_freeord := _; tpiPn_in_after := _; tpiPn_fd := _ |} |}).
(* THE OUTCOME: ran' = ran, the all-granted run's result is this one, and the position advances by its events *)
{ intros sm x os i H0 hist Hpos Hrun _ _. split; [exact HRAN|]. split; [exact HGRUN|].
  rewrite HGT in Hrun |- *. exact (PItems_posb.pi_posb_post _ _ _ HPB2 sm x os i H0 hist Hpos Hrun). }
(* THE PARTIAL TREE'S FREE ORDER (the batch kit, the None arm): the completed slots' order list (pi_forder) at every depth
   bound n = S nn >= MAXD - d, then kids, then keys (PItems_forder.pis_fo_open), framed to the epilogue's memory;
   the kit's model is decided at the missing colon: af ++ arrz true cap *)
{ change (pi_sblk true kids keys cap) with (pis_slots true kids keys (Z.of_nat cap)).
  intros Hhd N HN.
  destruct (PItems_forder.pi_forder_at _ _ _ _ _ _ _ _ _ d HFORD Hhd HdMAX HDEP N HN) as (nn & Facc & -> & _ & HPF & HMF).
  rewrite Hnacc in HPF. rewrite <- (length_map snd acc) in HPF.
  pose proof (PItems_forder.pis_fo_open SEGS _ _ v true 0 kids keys (Z.of_nat cap) (map snd acc) (map fst acc) Di nn Facc
    HOP HPF) as HFO.
  exists (Facc ++ pis_slots true kids keys (Z.of_nat cap)). split.
  - apply (PItems_forder.pis_fo_node_xfer SEGS (Nat.succ nn) _ _ _ _ v v _ _ HFO).
    + intros a k0 Hin. apply (HLBF a k0 Hin). exact (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HFO a k0 Hin).
    + intros x Hx. apply HSMF. right. exact Hx.
    + exact Hv8.
    + intros i Hi. refine (proj1 (HSMF (v + i) _)). unfold pj_footR. left. clear - Hi; lia.
    + intros i Hi Hw. refine (proj2 (HSMF (v + i) _) Hw). unfold pj_footR. left. clear - Hi; lia.
    + exact (PItems_forder.pis_fo_apart SEGS _ _ _ _ _ _ HFO).
  - rewrite map_app, HMF, (PItems_forder.pis_fo_slots_hb_nat _ true kids keys cap Hhd).
    rewrite <- (app_nil_r ok0), (HFLE []). reflexivity. }
{ (* the cursor after the refusal: kept above the callee's window *)
  assert (VQ : forall a n0 w, q <= a -> a + Z.of_nat n0 <= q + 24 ->
    val_mem SEGS (mrestrict (w_H Wc) memc) a n0 w -> val_mem SEGS (mrestrict (w_H W2) (ms_mem msE)) a n0 w).
  { intros a n0 w Ha1 Ha2 Hv kk0 Hk0.
    rewrite (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc (ms_mem msE) (a + Z.of_nat kk0));
      [exact (Hv kk0 Hk0) | apply KSTK; lia]. }
  exists p1, d1. split; [exact Hp1|]. split; [unfold PjGrammar.MAXD in HdMAX; lia|].
  split; [apply VQ; [lia | cbn; lia | exact Vq0]|].
  split; [apply VQ; [lia | cbn; lia | exact Vq8]|].
  split; [apply VQ; [lia | cbn; lia | exact Vq16]|].
  intros x Hx.
  assert (NI : ~ in_img SEGS x) by (intros Hi; pose proof (Hsegs x Hi); lia).
  destruct (pif_same (w_H Wc) (w_H W2) memc (ms_mem msE) x ltac:(lia) NI (KSTK x ltac:(lia))) as [_ Hw].
  exact (Hw (Hrwq x Hx)). }
pose proof (pis_exit_open SEGS _ _ v true 0 kids keys (Z.of_nat cap) (map snd acc) (map fst acc) Di d HOP HdMAX
  ltac:(apply Forall_map; exact HDEP)) as HFD.
change (pi_sblk true kids keys cap) with (pis_slots true kids keys (Z.of_nat cap)).
exact (pis_fd_frame SEGS _ _ _ _ _ v _ HFD HLBF HSMF).
Qed.

End body.
