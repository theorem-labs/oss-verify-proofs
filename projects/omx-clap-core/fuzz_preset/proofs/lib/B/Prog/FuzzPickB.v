(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YC1fP.v, with its module paths and module names changed; 710 of its 767 lines of code are new or changed and 456 lines of the source are left out. *)
(* fuzz_preset, IMAGE B' (asan-ubsan, #102 pin d663f82d7f488d30; listing of record lib/B/Listing_prog.v, slots as at
   blob 8bcc2c9e7809, a working branch d42e123915ae; the cut's blob c97cc46b3e13 changes only its header
   line): the walk of fuzz.h's fuzz_pick (omx-clap-core fuzz/fuzz.h
   :64-72 at 246923f0, blob 0269c7f7; out of line on B' only, 0x84da4, 42 instructions from slot 3510) against the kit's
   text tfuzz_pick_specX (lib/A/PRH_FnCheck.v:923, blob c40cf3fdcd2a at the batch kit's cut 7cdbb61b5fa0), proved VERBATIM.
   proves function fuzz_pick (reuse search: the internal file REWALK-102-PLAN.md section F3)
   the batch kit's REBIND (rule 24: the rebind proves no function): the walk is a Theorem Labs lane's working branch
   ff497269cc63 (this path, blob d6f8c0dfa621), proved there against the kit's earlier text (PRH_FnCheck.v blob
   6f6bc83d7420). The two texts, comments stripped, differ ONLY in the ledger's two #102 fields: the binders
   `most own` and prh_ledger's last two arguments `most own`, in the pre and in the post. The walk keeps the ledger
   whole (prh_ledger_kept_aview), so the proof changes only in its intros.
   FORM. The walk fuzz_pick_walk_B is generic in the allocator relation ARx (one hypothesis, its engine laws LAWS), in
   CfParams / PrhRoomLive, and in the image instance {PA : PAImg B_prog_listing}; the runner's tables come from
   PL_B102 (lib/B/Prog/PLB102.v), and the two facts of the instance the walk reads are one named premise FP_IMG
   (fpi_entry: the entry is slot 3510; fpi_hi: the image lies below 2 ^ 31). The binding of B to the image's
   shadow-base GOT word and cell is YC1fP's PALibCore.
   THE TOP fuzz_pick_holds_B (end of file) is the kit's text at the B' halts top's instance, with the type of
   HaltsClosedB.v's H_text_fuzz_pick_B (a working branch 5f51f36fad3f, blob 895e87822602, :257-259),
   so that citation is `exact`: PI := preset_prh_img (= prh_img_B), L := B_prog_listing, PA := PI_prog_B
   (lib/B/PAImg_prog.v blob 15fab93fe702, which builds at the cut), B := TfibB (lib/Reusable/YD2l.v),
   ARx := PresetCfnB.iface_ARx (ARcf /\ xs_placed_cf at CfParams_preset), RL := prh_room_live_a8,
   SK := preset_sink_head. The walk's three premises are closed there: FP_IMG by vm_compute, PALibCore by
   YC1fP.palib_core of PALibB.exvi_eh_palib, LAWS by YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf (as HaltsClosedB.v
   laws_iface_B). The top's files are Required after the walk, so PAImg_prog's global instance PI_prog_B is not in
   scope in the generic walk. The top has no hypothesis.
   THE CODE (neutral listing fuzz_pick.asan-ubsan.new.s (sha256 ff28600a0550; internal record)): frame 16 and the ra spill; len = 0 skips
   to h = 5381 and the return; else the shadow base (GOT A_OBJ 0 -> cell A_OBJ 12), h = 5381 (lui 1, addiw 1285),
   then the loop at 0x84dd0: the UBSan pointer-overflow checks of p + i (bltu / snez-seqz-xor / beqz p, all to the
   `unimp` at 0x84e48), the ASan load1 check of p + i (slow block 0x84e18, report 0x84e24), h = (h << 5) + h + p[i],
   i++, len--; after the loop `n ? h % n : 0` (remu) and the return.
   UNREACHABLE ARMS, with the reason: the three UBSan branches are decided by the loop state's facts (p <= p + i:
   the condition GEU (p + i) p; p + i <> 0 and p <> 0: atom ranges from 4096), which the kit's premises 0 < p and src_rd
   give; the ASan report is never reached because every byte p + i is addressable (src_rd's range_addressable, the
   engine's shadow entry); the report site is skipped by the engine's check token.
   SEGMENTS: E (entry to the len test, then to the loop head or the return) and L (one loop iteration, the loop
   lemma fp_loop by induction on the bytes still to read, ck_djb2's own recursion).
   NUMERALS. DERIVED: 3510 (the slot of fuzz_pick in the listing; 4 * 3510 = 14040 = 0x84da4 - 0x816cc), 44 (the
   loop head, 0x84dd0 - 0x84da4), atom indices (registers below 32, extras from 32). WORD: 5381 (djb2's seed), 33
   and 5 (its multiplier, as the shift), 255 (a byte). LENGTH: 16 (the frame), 8 (the ra slot), 1 (a byte),
   3 * 2 ^ 20 (the kit's length bound), 4096, 2 ^ 31 / 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64. No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG0dcf YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PLB102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
(* the PLAIN build's sink head must never fill SK here: every SK below is passed explicitly *)
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- image B': fuzz_pick's entry and its loop head, as offsets from the listing base (4 * the slot) ---- *)
Definition FP_SLOT : nat := 3510.
Definition FP_K : Z := 4 * Z.of_nat FP_SLOT.
Definition FP_LOOP : Z := FP_K + 44.
Definition FP_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* the listing's first two words at the slot are the frame (addi sp, sp, -16; sd ra, 8(sp)) *)
Lemma fp_slot_words : nth FP_SLOT B_prog_listing (PW 0) = PW 0xff010113 /\
  nth (S FP_SLOT) B_prog_listing (PW 0) = PW 0x113423.
Proof. split; vm_compute; reflexivity. Qed.

(* ---- segment E: the symbolic state at fuzz_pick's entry ----
   atoms: 1 = ra, 2 = entry sp, 10 = p, 11 = len, 12 = n, 32 = the shadow offset; regions: the 16-byte frame
   (written: the ra spill), the shadow-base GOT word (A_OBJ 0) and the shadow-base cell (A_OBJ 12), read only. *)
Definition fp_regions : smem := [stack_region 16; got_regionP; bcell_regionP 32].
Definition fp_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47) 0); (11%nat, mkAF 0 (3 * 2 ^ 20) 0);
    (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_fe : sstate := mkSS FP_K sr_atoms fp_regions None fp_facts.
Definition FP_BxE : sv := SOff 32 0.
Definition fp_SHE : list shent := [].

(* ---- segment L: the symbolic state at the loop head (0x84dd0) ----
   atoms: 1 = ra, 2 = sp (entry sp - 16), 10 = p, 11 = the bytes still to read, 12 = n, 13 = p + i (a3 and a7),
   14 = h, 15 = the shadow offset (a5), 32 = the byte p[i]; a6 = 1 (p <> 0); regions: the frame with the saved ra
   at sp + 8, and the byte p[i]; one shadow entry: the byte p[i] is addressable. *)
Definition fp_lregs : list sv := sr_set (sr_set sr_atoms 17%bv (SOff 13 0)) 16%bv (SLit 1).
Definition fp_lregions : smem :=
  [ YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 1 0))];
    YP09.mkRegion (Some 13%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition fp_lfacts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47) 0); (11%nat, mkAF 1 (3 * 2 ^ 20) 0);
    (13%nat, mkAF 4096 (2 ^ 47 - 2) 0); (15%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0)]
    [mkAC BC_GEU (SOff 13 0) (SOff 10 0)] [].
Definition ss_fl : sstate := mkSS FP_LOOP fp_lregs fp_lregions None fp_lfacts.
Definition FP_BxL : sv := SOff 15 0.
Definition fp_SHL : list shent := [mkSHE 13 0 1].
(* the registers the loop and the epilogue leave alone (the callee-saved ones but sp) *)
Definition FP_KEPT : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* ---- pure facts ---- *)
Lemma fp_djb2_cons : forall h c r, ck_djb2 h (c :: r) = ck_djb2 ((33 * h + c) mod 2 ^ 64) r.
Proof. reflexivity. Qed.
Lemma fp_djb2_range : forall r h, 0 <= h < 2 ^ 64 -> 0 <= ck_djb2 h r < 2 ^ 64.
Proof.
induction r as [|c r IH]; intros h Hh; cbn [ck_djb2]; [exact Hh|].
apply IH. apply Z.mod_pos_bound. lia.
Qed.
Lemma fp_amem_sub : forall p n q m, amem_range p n -> p <= q -> 0 <= m -> q + m <= p + n -> amem_range q m.
Proof. intros p n q m H H1 H2 H3. unfold amem_range in *. lia. Qed.
Lemma fp_garr8_tl : forall segs (mm : word -> option byte) q c r, garr8 segs mm q (c :: r) -> garr8 segs mm (q + 1) r.
Proof.
intros segs mm q c r H j Hj. destruct (H (S j) ltac:(cbn [length]; lia)) as [V R].
cbn [nth] in V, R. replace (q + Z.of_nat (S j)) with (q + 1 + Z.of_nat j) in V by lia. exact (conj V R).
Qed.
Lemma fp_garr8_hd : forall segs (mm : word -> option byte) q c r,
  garr8 segs mm q (c :: r) -> val_mem segs mm q 1 c /\ 0 <= c < 256.
Proof.
intros segs mm q c r H. destruct (H 0%nat ltac:(cbn [length]; lia)) as [V R]. cbn [nth] in V, R.
rewrite Z.add_0_r in V. exact (conj V R).
Qed.
Lemma fp_ra_tl : forall rd q (c : Z) (r : list Z), range_addressable rd SHADOW_OFF q (Z.of_nat (length (c :: r))) ->
  range_addressable rd SHADOW_OFF (q + 1) (Z.of_nat (length r)).
Proof. intros rd q c r H x Hx. apply H. cbn [length]. lia. Qed.
Lemma fp_hash_step : forall E h c, bv_unsigned (ew E 14) = h -> bv_unsigned (ew E 32) = c ->
  0 <= h < 2 ^ 64 -> 0 <= c < 256 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 14 0) (SLit 33)) (SOff 32 0)) = w64 ((33 * h + c) mod 2 ^ 64).
Proof.
intros E h c Hh Hc Rh Rc. apply bv_eq. unfold w64. rewrite unsigned_lit_small by (apply Z.mod_pos_bound; lia).
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 14 0) (SLit 33)) (SOff 32 0))))
  with (U E (SAlu ALU_ADD (SMd M_MUL (SOff 14 0) (SLit 33)) (SOff 32 0))).
rewrite U_SAlu, U_SMd, !U_SOff, U_SLit, Hh, Hc, !Z.add_0_r. cbn [zalu_raw zmd_raw].
rewrite (zcanon_id h), (zcanon_id c), (zcanon_id 33) by (unfold M64; lia).
unfold zcanon, M64. rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.
Lemma fp_remu : forall E h c n, bv_unsigned (ew E 14) = h -> bv_unsigned (ew E 32) = c -> bv_unsigned (ew E 12) = n ->
  0 <= h < 2 ^ 64 -> 0 <= c < 256 -> 0 < n < 2 ^ 64 ->
  sv_denot E (SMd M_REMU (SAlu ALU_ADD (SMd M_MUL (SOff 14 0) (SLit 33)) (SOff 32 0)) (SOff 12 0))
  = w64 (((33 * h + c) mod 2 ^ 64) mod n).
Proof.
intros E h c n Hh Hc Hn Rh Rc Rn.
assert (Hi : U E (SAlu ALU_ADD (SMd M_MUL (SOff 14 0) (SLit 33)) (SOff 32 0)) = (33 * h + c) mod 2 ^ 64).
{ unfold U. rewrite (fp_hash_step E h c Hh Hc Rh Rc). unfold w64. apply unsigned_lit_small. apply Z.mod_pos_bound. lia. }
assert (Hr : 0 <= ((33 * h + c) mod 2 ^ 64) mod n < n) by (apply Z.mod_pos_bound; lia).
apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia.
change (bv_unsigned (sv_denot E (SMd M_REMU (SAlu ALU_ADD (SMd M_MUL (SOff 14 0) (SLit 33)) (SOff 32 0)) (SOff 12 0))))
  with (U E (SMd M_REMU (SAlu ALU_ADD (SMd M_MUL (SOff 14 0) (SLit 33)) (SOff 32 0)) (SOff 12 0))).
rewrite U_SMd, Hi, U_SOff, Hn, Z.add_0_r, (zcanon_id n) by (unfold M64; lia). cbn [zmd_raw].
rewrite (proj2 (Z.eqb_neq n 0)) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma fp_remu0 : forall E n, bv_unsigned (ew E 12) = n -> 0 < n < 2 ^ 64 ->
  sv_denot E (SMd M_REMU (SLit 5381) (SOff 12 0)) = w64 (5381 mod n).
Proof.
intros E n Hn Rn.
assert (Hr : 0 <= 5381 mod n < n) by (apply Z.mod_pos_bound; lia).
apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia.
change (bv_unsigned (sv_denot E (SMd M_REMU (SLit 5381) (SOff 12 0)))) with (U E (SMd M_REMU (SLit 5381) (SOff 12 0))).
rewrite U_SMd, U_SLit, U_SOff, Hn, Z.add_0_r, (zcanon_id n), (zcanon_id 5381) by (unfold M64; lia). cbn [zmd_raw].
rewrite (proj2 (Z.eqb_neq n 0)) by lia. apply zcanon_id. unfold M64. lia.
Qed.

Section h. Context {fx0 : YK11.FPState}.
Variable segs : list Segment.
(* the loop head's regions have no write window: a run from it changes no byte *)
Lemma fp_nowin : forall E (H : word -> bool) (m m' : word -> option byte) a,
  frame_of E fp_lregions (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 ->
  aview segs H m' a = aview segs H m a.
Proof.
intros E H m m' a Hf Ha. unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros (r & Hr & Hb). cbn [fp_lregions In] in Hr.
destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hb; lia.
Qed.
(* skip_ws_x.v skw_garr8_kept / skw_val_kept / skw_ra_kept (lib/B/Prog/skip_ws_x.v :136-154), restated *)
Lemma fp_garr8_kept : forall H (m m' : word -> option byte) p L,
  (forall a, p <= a < p + Z.of_nat (length L) -> aview segs H m' a = aview segs H m a) ->
  garr8 segs (mrestrict H m) p L -> garr8 segs (mrestrict H m') p L.
Proof.
intros H m m' p L HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. cbn in Hk. rewrite (mbyte_of_aview segs H H m m' (p + Z.of_nat j + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.
Lemma fp_val_kept : forall H (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs H m' x = aview segs H m x) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H m') a n v.
Proof.
intros H m m' a n v HE Hv kk Hk. rewrite (mbyte_of_aview segs H H m m' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.
Lemma fp_ra_kept : forall H (m m' : word -> option byte) a n,
  (forall x, a <= x < a + n -> aview segs H m' (shadow_of_addr SHADOW_OFF x) = aview segs H m (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable (aview segs H m) SHADOW_OFF a n -> range_addressable (aview segs H m') SHADOW_OFF a n.
Proof. intros H m m' a n HE HR x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. rewrite (HE x Hx). auto. Qed.
End h.
(* a run whose regions have no write window writes nothing: its write premise awr_ok holds vacuously *)
Ltac fp_nowr :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  intros a (r & Hr & Ha); cbn in Hr;
  repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|]);
  destruct Hr.
(* off a run's write windows its memory is kept (CheckBoundedAllocB.v cba_aview_frame, image-generic) *)
Ltac fp_notw Usp :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  intros (r & Hr & Ha); cbn in Hr;
  repeat (destruct Hr as [<-|Hr]; [cbn [stack_region got_regionP bcell_regionP YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?Usp in Ha; lia|]);
  destruct Hr.
(* the entry runs write only the frame window [sp - 16, sp): awr_byte's first case (the STK window) *)
Ltac fp_wr Usp WS :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  intros a (r & Hr & Ha); cbn in Hr;
  repeat (destruct Hr as [<-|Hr];
    [cbn [stack_region got_regionP bcell_regionP YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?Usp in Ha; first [lia | left; rewrite WS; lia]|]);
  destruct Hr.
(* skip_ws_x.v skw_aregs (:294-302) at FP_KEPT *)
Lemma fp_aregs : forall regs regs' : bvmap 5 word,
  (forall r, In r FP_KEPT -> getr regs' r = getr regs r) -> getr regs' 2 = getr regs 2 -> aregs_preserved regs regs'.
Proof.
intros regs regs' HK H2 r Hr. unfold acallee_saved in Hr.
destruct (Z.eq_dec r 2) as [->|Hr2]; [exact H2|].
assert (Hc : In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) by (cbn; lia).
apply HK. clear -Hc. cbn in Hc.
unfold FP_KEPT. repeat destruct Hc as [<- | Hc]; try contradiction; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]).
Qed.
(* the program's statics (prh_pst at prh_img_B) are image bytes, far below the stack (CheckBoundedAllocB.v cba_pst_low) *)
Lemma fp_pst_low : forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> 0 <= a < 2 ^ 46.
Proof.
intros a H. apply Exists_exists in H as (r & Hr & Ha). vm_compute in Hr.
repeat destruct Hr as [<-|Hr]; try contradiction; unfold in_zr in Ha; cbn [fst snd] in Ha; lia.
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation PL := PL_B102.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Abbreviation PST := (@prh_pst prh_img_B).

(* THE TWO IMAGE FACTS THE WALK READS (vm_compute facts at PI_prog_B): the entry is the listing's slot 3510, and the
   image (so its GOT word and cell) lies below 2 ^ 31, far below every stack frame *)
Record FP_IMG : Prop := {
  fpi_entry : SIGMA AS_fuzz_pick = BASE + FP_K;
  fpi_hi : @pa_hi _ B_prog_listing PA <= 2 ^ 31 }.

Definition FP_EI (regs : bvmap 5 word) (extra : list Z) : env :=
  Eimg (L := B_prog_listing) (PI := PA) (Ereg regs (map (Z_to_bv 64) extra)).

Lemma fp_win_kept : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a Hf Ha Hn. unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma fp_region_nth : forall E ss ms i r,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok SEGS E _ ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
(* skip_ws_x.v skw_field (:118-127) *)
Lemma fp_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem SEGS m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok SEGS E m b od w e v Hck He Hv Hw).
Qed.
Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the engine laws of the allocator relation, ONE named hypothesis (discharged at the instance) *)
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.

Let BR := paj_branch (L := B_prog_listing) (PI := PA).
Let RET := paj_ret_at (L := B_prog_listing) (PL := PL) (PI := PA).

(* ---- the loop: from the loop head with `rest` still to read at q = p + i, hash h so far ---- *)
Lemma fp_loop : forall (rest : list Z) W (regs : bvmap 5 word) memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k
  memE p q n h,
  rest <> [] -> Z.of_nat (length rest) <= 3 * 2 ^ 20 ->
  ajournal_x (SK := SK) SEGS B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
  (YAkMemnorm.memnorm SEGS memE -> YAkMemnorm.memnorm SEGS memc) ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 (Z.of_nat (length rest)) -> getr regs 12 = w64 n ->
  getr regs 13 = w64 q -> getr regs 14 = w64 h -> getr regs 15 = w64 SHADOW_OFF ->
  getr regs 16 = w64 1 -> getr regs 17 = w64 q ->
  spZ regs mod 16 = 0 -> 2 ^ 46 <= spZ regs -> spZ regs + 16 <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs + 8) 8 (bv_unsigned (getr regs 1)) ->
  4096 <= p <= q -> amem_range q (Z.of_nat (length rest)) -> q + Z.of_nat (length rest) <= spZ regs ->
  0 <= h < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  garr8 SEGS (mrestrict (w_H W) memc) q rest ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q (Z.of_nat (length rest)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + FP_LOOP)) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
       ajournal_x (SK := SK) SEGS B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
       (forall r, In r FP_KEPT -> getr regs' r = getr regs r) /\
       getr regs' 2 = w64 (spZ regs + 16) /\
       (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
       (YAkMemnorm.memnorm SEGS memE -> YAkMemnorm.memnorm SEGS mem') /\
       getr regs' 10 = w64 (if n =? 0 then 0 else ck_djb2 h rest mod n)).
Proof.
induction rest as [|c rest IH]; intros W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k memE p q n h
  Hne Hlen HJ HPM Hra H10 H11 H12 H13 H14 H15 H16 H17 Hal Hsplo Hsphi Vra Hpq Ham Hqs Hh Hn GT HRA;
  [contradiction|].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL PA B PST ARx HL LAWS
  (fun m => YAkMemnorm.memnorm SEGS memE -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) memE (srr_inv_laws_memnorm_k SEGS))).
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL PA B PST ARx HL LAWS
  (fun m => YAkMemnorm.memnorm SEGS memE -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) memE (srr_inv_laws_memnorm_k SEGS))).
pose proof (fp_garr8_hd _ _ _ _ _ GT) as [Vc Hc8].
cbn [length] in Hlen, H11, Ham, Hqs, HRA.
assert (Hqe : q + Z.of_nat (Datatypes.S (length rest)) <= 2 ^ 47 - 1) by (unfold amem_range in Ham; lia).
remember (FP_EI regs [c]) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall kk, (kk < A_TEXT)%nat -> ew E kk = ew (Ereg regs (map (Z_to_bv 64) [c])) kk)
  by (intros kk Hkk; subst E; apply Eimg_low; exact Hkk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat (Datatypes.S (length rest))))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 n)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 q)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E14 : ew E 14 = Z_to_bv 64 h)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E15 : ew E 15 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E32 : ew E 32 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [c])) E)
  by (split; [intros kk Hkk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = Z.of_nat (Datatypes.S (length rest))) by (rewrite E11; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = n) by (rewrite E12; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew E 13) = q) by (rewrite E13; apply unsigned_lit_small; lia).
assert (U14 : bv_unsigned (ew E 14) = h) by (rewrite E14; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew E 15) = SHADOW_OFF) by (rewrite E15; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; apply unsigned_lit_small; lia).
(* the loop head's state *)
assert (HS : st_ok_pi SEGS VAL E ss_fl (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + FP_LOOP)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_fl. apply pa_entry_st_ok_full.
  - unfold fp_lregs. apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE; unfold FP_EI; apply regs_ok_Eimg_Ereg | |] | |].
    + intros X; discriminate X.
    + cbn [sv_denot]. rewrite U13, Z.add_0_r. exact H17.
    + intros X; discriminate X.
    + exact H16.
  - vm_compute. reflexivity.
  - unfold fp_lregions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (spZ regs) 8 8 (SOff 1 0) (bv_unsigned (getr regs 1)));
      [cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs 1)) as R; unfold bv_modulus in R; cbn in R |- *; lia | zside | exact Vra].
    + rewrite U13. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ q 0 1 (SOff 32 0) c);
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vc].
  - apply pairwise_disjoint_of_extents. unfold fp_lregions. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U13.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split].
    + cbn [fp_lfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U10, U11, U13, U15, U32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SHADOW_OFF. repeat split; lia.
    + cbn [fp_lfacts f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite branch_geu_U, (U_atom E 13 q E13), (U_atom E 10 p E10) by lia.
      apply negb_true_iff, Z.ltb_ge. lia.
    + exact I. }
assert (HBx : U E FP_BxL = SHADOW_OFF) by (unfold FP_BxL; apply (U_atom E 15 SHADOW_OFF E15); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS FP_BxL fp_SHL E (mrestrict (w_H W) memc)).
{ unfold fp_SHL. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) memc E FP_BxL 13 q (Z.of_nat (Datatypes.S (length rest))) q 0 1 HRA HBx);
    [rewrite (U_atom E 13 q E13) by lia; reflexivity | lia | lia |].
  intros x0 Hx0. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. unfold SHADOW_OFF. lia. }
clear HE EL.
(* the iteration: the three UBSan checks, the ASan check of p[i], the hash step, to the loop test *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM FP_Bspan.
{ intros a (r & Hr & Ha). cbn [ss_mem ss_fl fp_lregions In] in Hr.
  destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia. }
rename HFr into HFr1. clear HF HG.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a)
  by (intros a Ha; exact (fp_nowin SEGS E (w_H W) memc (ms_mem ms) a HFr1 Ha)).
clear HFr1.
(* the loop test `bnez a1` (0x84e10): a byte left after p[i] or not *)
psrr_branch_tok RUN BR HS SHOK FP_Bspan.
- (* taken: rest <> [], back to the loop head *)
  rewrite branch_ne_U, U_SOff, U_SLit in Hc. cbn [ew ewset Nat.eqb] in Hc. rewrite U11 in Hc.
  assert (Hrne : rest <> []) by (intros ->; vm_compute in Hc; discriminate Hc).
  clear Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM FP_Bspan FP_LOOP.
  { fp_nowr. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem mx) a = aview SEGS (w_H W) memc a)
      by (intros a Ha; rewrite (fp_nowin SEGS _ (w_H W) _ (ms_mem mx) a HFr Ha); exact (K1 a Ha)) end.
  clear HF HFr HG K1.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
  prreg HS (12%bv : bv 5) R12. prreg HS (13%bv : bv 5) R13. prreg HS (15%bv : bv 5) R15. prreg HS (16%bv : bv 5) R16.
  prreg HS (17%bv : bv 5) R17.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 14%bv HS) as R14.
  lazymatch type of R14 with _ = sv_denot ?Ex (sr_get ?l _) =>
    let e := eval vm_compute in (sr_get l 14%bv) in change (sr_get l 14%bv) with e in R14;
    rewrite (fp_hash_step Ex h c) in R14 by first [cbn [ew ewset Nat.eqb]; first [exact U14 | exact U32] | lia] end.
  rewrite E1 in R1. rewrite E2 in R2. rewrite E10 in R10. rewrite U11 in R11. rewrite E12 in R12.
  rewrite U13 in R13, R17. rewrite E15 in R15.
  pose proof (fp_garr8_tl _ _ _ _ _ GT) as GT1.
  pose proof (fp_ra_tl _ _ c rest HRA) as HRA1.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?mx) =>
    assert (SP : spZ (ms_regs mx) = spZ regs) by (unfold spZ; rewrite R2; reflexivity);
    assert (AGx : env_agree 32 (Ereg regs (map (Z_to_bv 64) [c])) Ex)
      by (eapply env_agree_trans; [exact HAE|]; split; [intros nn Hnn; rewrite !ew_ewset_other by lia; reflexivity | reflexivity]);
    pmkst HS; change (BASE + 14104) with (BASE + FP_LOOP);
    eapply SRr_mono;
    [ eapply (IH W (ms_regs mx) (ms_mem mx) _ STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k memE p (q + 1) n
        ((33 * h + c) mod 2 ^ 64));
      [ exact Hrne | lia | exact HJ | exact HPM
      | rewrite R1; exact Hra | exact R10
      | rewrite R11; f_equal; lia | exact R12 | exact R13 | exact R14 | exact R15 | exact R16 | exact R17
      | rewrite SP; exact Hal | rewrite SP; exact Hsplo | rewrite SP; exact Hsphi
      | rewrite SP, R1; apply (fp_val_kept SEGS (w_H W) memc); [intros x0 Hx0; apply K2; lia | exact Vra]
      | lia
      | apply (fp_amem_sub q (Z.of_nat (Datatypes.S (length rest)))); [exact Ham | lia | lia | lia]
      | rewrite SP; lia
      | apply Z.mod_pos_bound; lia | exact Hn
      | apply (fp_garr8_kept SEGS (w_H W) memc); [intros x0 Hx0; apply K2; lia | exact GT1]
      | apply (fp_ra_kept SEGS (w_H W) memc); [intros x0 Hx0; apply K2; unfold shadow_of_addr, SHADOW_OFF;
          split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | pose proof (Z.div_le_upper_bound x0 8 (2 ^ 47)); lia]
        | exact HRA1 ] ]
    | cbv beta; intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HK5 & Hsp5 & Hkp5 & HPM5 & V5);
      split; [reflexivity|]; exists regs5, mem5, md5;
      split; [rewrite R1; reflexivity|];
      split; [exact HJ5|];
      split; [intros r Hr; rewrite (HK5 r Hr);
              exact (regs_kept_of_st_ok_pi _ _ _ regs _ FP_KEPT HS AGx ltac:(vm_compute; reflexivity) r Hr)|];
      split; [rewrite Hsp5, SP; reflexivity|];
      split; [intros a Ha; rewrite (Hkp5 a Ha); exact (K2 a Ha)|];
      split; [exact HPM5|];
      rewrite V5; reflexivity ]
  end.
- (* not taken: p[i] was the last byte *)
  rewrite branch_ne_U, U_SOff, U_SLit in Hc. cbn [ew ewset Nat.eqb] in Hc. rewrite U11 in Hc.
  assert (Hre : rest = []).
  { destruct rest as [|c1 rest1]; [reflexivity|]. exfalso. apply negb_false_iff, Z.eqb_eq in Hc.
    cbn [length] in Hc, Hlen. unfold zcanon, M64 in Hc.
    rewrite (Z.mod_small (Z.of_nat (Datatypes.S (Datatypes.S (length rest1))) + -1) (2 ^ 64)) in Hc by (split; lia).
    rewrite Z.mod_0_l in Hc by lia. lia. }
  subst rest. clear Hc.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM FP_Bspan.
  { fp_nowr. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem mx) a = aview SEGS (w_H W) memc a)
      by (intros a Ha; rewrite (fp_nowin SEGS _ (w_H W) _ (ms_mem mx) a HFr Ha); exact (K1 a Ha)) end.
  clear HF HFr HG K1.
  (* `beqz a2` (0x84e2c): n = 0 gives 0, else remu *)
  psrr_branch_tok RUN BR HS SHOK FP_Bspan.
  + rewrite branch_eq_U, U_SOff, U_SLit in Hc. cbn [ew ewset Nat.eqb] in Hc. rewrite U12 in Hc.
    assert (Hn0 : n = 0) by (apply Z.eqb_eq in Hc; unfold zcanon, M64 in Hc; rewrite Z.add_0_r, Z.mod_small, Z.mod_0_l in Hc by lia; exact Hc).
    subst n. clear Hc.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM FP_Bspan.
    { fp_nowr. }
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?mx) =>
      assert (K3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem mx) a = aview SEGS (w_H W) memc a)
        by (intros a Ha; rewrite (fp_nowin SEGS _ (w_H W) _ (ms_mem mx) a HFr Ha); exact (K2 a Ha));
      assert (AGx : env_agree 32 (Ereg regs (map (Z_to_bv 64) [c])) Ex)
        by (eapply env_agree_trans; [exact HAE|]; split; [intros nn Hnn; rewrite !ew_ewset_other by lia; reflexivity | reflexivity]);
      prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (10%bv : bv 5) Q10;
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
      let mq := fresh "mq" in intros mq; cbv beta;
      split; [reflexivity|];
      exists (ms_regs mx), (ms_mem mx); eexists;
      split; [cbn [ms_regs]; rewrite Q1, E1, Hra; reflexivity|];
      repeat rewrite wvb_collapse in HJ;
      split; [eapply (ajournal_x_materialize (SK := SK)); solve [exact HJ | exact LAWS | exact (@pa_segs_low _ B_prog_listing PA)]|];
      split; [intros r Hr; exact (regs_kept_of_st_ok_pi _ _ _ regs _ FP_KEPT HS AGx ltac:(vm_compute; reflexivity) r Hr)|];
      split; [rewrite Q2, Usp; reflexivity|];
      split; [exact K3|];
      split; [exact HPM|];
      rewrite Q10, Hn0; reflexivity
    end.
  + rewrite branch_eq_U, U_SOff, U_SLit in Hc. cbn [ew ewset Nat.eqb] in Hc. rewrite U12 in Hc.
    assert (Hn0 : n <> 0) by (intros ->; vm_compute in Hc; discriminate Hc).
    clear Hc.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM FP_Bspan.
    { fp_nowr. }
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?mx) =>
      assert (K3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem mx) a = aview SEGS (w_H W) memc a)
        by (intros a Ha; rewrite (fp_nowin SEGS _ (w_H W) _ (ms_mem mx) a HFr Ha); exact (K2 a Ha));
      assert (AGx : env_agree 32 (Ereg regs (map (Z_to_bv 64) [c])) Ex)
        by (eapply env_agree_trans; [exact HAE|]; split; [intros nn Hnn; rewrite !ew_ewset_other by lia; reflexivity | reflexivity]);
      prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2;
      pose proof (st_ok_pi_restrict_reg _ _ _ _ 10%bv HS) as Q10;
      lazymatch type of Q10 with _ = sv_denot _ (sr_get ?l _) =>
        let e := eval vm_compute in (sr_get l 10%bv) in change (sr_get l 10%bv) with e in Q10 end;
      rewrite (fp_remu Ex h c n) in Q10 by first [cbn [ew ewset Nat.eqb]; first [exact U14 | exact U32 | exact U12] | lia];
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
      let mq := fresh "mq" in intros mq; cbv beta;
      split; [reflexivity|];
      exists (ms_regs mx), (ms_mem mx); eexists;
      split; [cbn [ms_regs]; rewrite Q1, E1, Hra; reflexivity|];
      repeat rewrite wvb_collapse in HJ;
      split; [eapply (ajournal_x_materialize (SK := SK)); solve [exact HJ | exact LAWS | exact (@pa_segs_low _ B_prog_listing PA)]|];
      split; [intros r Hr; exact (regs_kept_of_st_ok_pi _ _ _ regs _ FP_KEPT HS AGx ltac:(vm_compute; reflexivity) r Hr)|];
      split; [rewrite Q2, Usp; reflexivity|];
      split; [exact K3|];
      split; [exact HPM|];
      rewrite Q10, (proj2 (Z.eqb_neq n 0) Hn0); reflexivity
    end.
Qed.

(* the block law's placement part (YCbqG ARx_blocks_law; CheckBoundedAllocB.v cba_blocks) *)
Lemma fp_blocks : forall ly S Hp (W : world SEGS) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling.
Proof.
intros ly S Hp W mem md p n HA HI.
first [ destruct (alx_blocks _ _ _ _ LAWS ly S Hp W mem md p n HA HI) as (H1 & H2 & H3 & _)
      | destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HA HI) as (H1 & H2 & H3 & _)
      | destruct (alx_blocks LAWS ly S Hp W mem md p n HA HI) as (H1 & H2 & H3 & _) ].
split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* ---- segment E and the function: the kit's text at the cut, VERBATIM, at every PAImg of the listing of record (the top
   fuzz_pick_holds_B below instantiates it) ---- *)
Theorem fuzz_pick_walk_B : FP_IMG -> PALibCore (PI := PA) B ->
  tfuzz_pick_specX (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx SK.
Proof.
intros [HENT HHI] TL.
unfold tfuzz_pick_specX.
intros ly S Hp W regs mem md ch p x n Lam peak cnt fail ran most own.
cbv zeta.
intros HFP H10 H11 H12 Hn Hlen Hp0 Hpl HSRC HL0.
unfold fpre in HFP. destruct HFP as (HPRE & HRO & HSP64 & HRAC).
assert (WS : STK_fuzz_pick = 16) by reflexivity.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
rewrite WS in Hstk0, Hslo, Hpres.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct HSRC as (GT & Hp4 & Hpc & Ham & HRA & _).
first [ destruct (alx_const _ _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _)
      | destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _)
      | destruct (alx_const LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _) ].
rewrite (palc_got_shadow B TL), (palc_cell B TL) in Kgot. rewrite (palc_cell B TL) in Kcell.
pose proof (palc_got_cell B TL) as HgcD.
pose proof (@pa_obj_img _ B_prog_listing PA 0 ltac:(lia)) as (O0a & O0b).
pose proof (@pa_obj_img _ B_prog_listing PA 12 ltac:(lia)) as (O12a & O12b).
pose proof (@pa_val_range _ B_prog_listing PA (A_OBJ 0)) as V0r.
pose proof (@pa_val_range _ B_prog_listing PA (A_OBJ 12)) as V12r.
remember (FP_EI regs [SHADOW_OFF]) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall kk, (kk < A_TEXT)%nat -> ew E kk = ew (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF])) kk)
  by (intros kk Hkk; subst E; apply Eimg_low; exact Hkk).
assert (EI : forall x0, (A_TEXT <= x0 < A_LIM)%nat -> ew E x0 = Z_to_bv 64 (VAL x0))
  by (intros x0 Hx0; subst E; apply Eimg_img; exact Hx0).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat (length x)))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 n)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF])) E)
  by (split; [intros kk Hkk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = Z.of_nat (length x)) by (rewrite E11; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = n) by (rewrite E12; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (VBI : forall x0, (A_TEXT <= x0 < A_LIM)%nat -> base_val E (Some x0) = VAL x0).
{ intros x0 Hx0. cbn [base_val]. rewrite (EI x0 Hx0). apply unsigned_lit_small. apply pa_val_range. }
(* the entry state *)
assert (HS : st_ok_pi SEGS VAL E ss_fe (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + FP_K)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_fe. apply pa_entry_st_ok_full.
  - rewrite HE. unfold FP_EI. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold fp_regions, stack_region, got_regionP, bcell_regionP. repeat apply Forall_cons; try apply Forall_nil;
      unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + rewrite (VBI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). split; [lia|]. split; [lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite (EI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    + rewrite (VBI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). split; [lia|]. split; [lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; cbn; lia | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  - apply pairwise_disjoint_of_extents. unfold fp_regions, stack_region, got_regionP, bcell_regionP. cbn [map].
    unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VBI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), (VBI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split].
    + cbn [fp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U10, U11, U32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SHADOW_OFF. repeat split; lia.
    + exact I.
    + exact I. }
clear HE EL.
assert (SHOK : sh_ok SEGS FP_BxE fp_SHE E (mrestrict (w_H W) mem)) by constructor.
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx STK_fuzz_pick [] ly S Hp W regs mem md ch HPRE) as HJ.
assert (HPM : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem) by exact (fun h => h).
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL PA B PST ARx HL LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL PA B PST ARx HL LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
unfold cfg_at. rewrite HENT. change (w64 (BASE + FP_K)) with (Z_to_bv 64 (BASE + FP_K)).
(* the frame, the ra spill, to the len test `beqz a1` *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM FP_Bspan.
{ intros a (r & Hr & Ha). cbn [ss_mem ss_fe fp_regions In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [stack_region got_regionP bcell_regionP YP09.r_base YP09.r_wlo YP09.r_whi] in Ha;
  [cbn [base_val] in Ha; left; rewrite Usp in Ha; rewrite WS; lia | lia | lia]. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
  assert (KE1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem mx) a = aview SEGS (w_H W) mem a) end.
{ intros a Ha Hna; apply (fp_win_kept _ _ _ _ _ a HFr Ha); fp_notw Usp. }
clear HF HFr HG.
(* the len test `beqz a1` (0x84db0) *)
psrr_branch_tok RUN BR HS SHOK FP_Bspan.
- (* len = 0: h = 5381 and straight to the return *)
  rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite U11 in Hc.
  assert (Hx : x = []).
  { destruct x as [|x0 x1]; [reflexivity|]. exfalso. apply Z.eqb_eq in Hc. cbn [length] in Hc, Hlen.
    unfold zcanon, M64 in Hc. rewrite Z.add_0_r, Z.mod_0_l in Hc by lia.
    rewrite (Z.mod_small (Z.of_nat (Datatypes.S (length x1))) (2 ^ 64)) in Hc by (split; lia). lia. }
  subst x. clear Hc.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM FP_Bspan.
  { fp_wr Usp WS. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
    assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
      aview SEGS (w_H W) (ms_mem mx) a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hna; rewrite (fp_win_kept _ _ _ _ _ a HFr Ha) by fp_notw Usp; exact (KE1 a Ha Hna)) end.
  clear HF HFr HG KE1.
  (* `beqz a2` (0x84e2c) *)
  psrr_branch_tok RUN BR HS SHOK FP_Bspan.
  + rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite U12 in Hc.
    assert (Hn0 : n = 0) by (apply Z.eqb_eq in Hc; unfold zcanon, M64 in Hc; rewrite Z.add_0_r, Z.mod_small, Z.mod_0_l in Hc by lia; exact Hc).
    clear Hc.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM FP_Bspan.
    { fp_wr Usp WS. }
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
    assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
      aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hna; rewrite (fp_win_kept _ _ _ _ _ a HFr Ha) by fp_notw Usp; exact (KE2 a Ha Hna)).
    clear HF HFr HG KE2.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mq. unfold fpostm, fpost, fQmn, apost_base_x. cbv beta.
    exists ly, S, Hp, (ms_regs msF), (ms_mem msF). eexists. exists 0.
    split; [cbn [ms_regs]; rewrite Q1, E1, Hra; reflexivity|].
    repeat rewrite wvb_collapse in HJ.
    split; [eapply (ajournal_x_materialize (SK := SK)); solve [exact HJ | exact LAWS | exact (@pa_segs_low _ B_prog_listing PA)]|].
    split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS); [exact HAE | vm_compute; reflexivity]|].
    split; [|exact HPM].
    split; [rewrite Q10; unfold ck_pick; rewrite (proj2 (Z.eqb_eq n 0) Hn0); reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros Hr0; exact Hr0|].
    split; [|apply garr8_nil].
    eapply prh_ledger_kept_aview; [exact HL0 | | | |].
    * intros a Ha. destruct (fp_pst_low a Ha) as [Ha0 Ha1]. apply KE; lia.
    * intros a k i Hin Hi. pose proof HL0 as (_ & _ & HLF & _). rewrite Forall_forall in HLF.
      destruct (HLF (a, k) Hin) as (Hk0 & Hkin & _). cbn [fst snd] in Hk0, Hkin.
      pose proof cf_head_nonneg as Hcf0.
      destruct (fp_blocks ly S Hp W mem md _ _ HAR Hkin) as (Hp16 & Hp4096 & Hpceil).
      unfold req_size in Hpceil. destruct (Z.eqb_spec (k + cf_head) 0) as [E0|E0]; apply KE; lia.
    * intros a k _ H. exact H.
    * apply Permutation_refl.
  + rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite U12 in Hc.
    assert (Hn0 : n <> 0) by (intros ->; vm_compute in Hc; discriminate Hc).
    clear Hc.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM FP_Bspan.
    { fp_wr Usp WS. }
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
    assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
      aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hna; rewrite (fp_win_kept _ _ _ _ _ a HFr Ha) by fp_notw Usp; exact (KE2 a Ha Hna)).
    clear HF HFr HG KE2.
    prreg HS (1%bv : bv 5) Q1.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 10%bv HS) as Q10.
    lazymatch type of Q10 with _ = sv_denot ?Ex (sr_get ?l _) =>
      let e := eval vm_compute in (sr_get l 10%bv) in change (sr_get l 10%bv) with e in Q10;
      rewrite (fp_remu0 Ex n) in Q10 by first [exact U12 | lia] end.
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mq. unfold fpostm, fpost, fQmn, apost_base_x. cbv beta.
    exists ly, S, Hp, (ms_regs msF), (ms_mem msF). eexists. exists 0.
    split; [cbn [ms_regs]; rewrite Q1, E1, Hra; reflexivity|].
    repeat rewrite wvb_collapse in HJ.
    split; [eapply (ajournal_x_materialize (SK := SK)); solve [exact HJ | exact LAWS | exact (@pa_segs_low _ B_prog_listing PA)]|].
    split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS); [exact HAE | vm_compute; reflexivity]|].
    split; [|exact HPM].
    split; [rewrite Q10; unfold ck_pick; rewrite (proj2 (Z.eqb_neq n 0) Hn0); reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros Hr0; exact Hr0|].
    split; [|apply garr8_nil].
    eapply prh_ledger_kept_aview; [exact HL0 | | | |].
    * intros a Ha. destruct (fp_pst_low a Ha) as [Ha0 Ha1]. apply KE; lia.
    * intros a k i Hin Hi. pose proof HL0 as (_ & _ & HLF & _). rewrite Forall_forall in HLF.
      destruct (HLF (a, k) Hin) as (Hk0 & Hkin & _). cbn [fst snd] in Hk0, Hkin.
      pose proof cf_head_nonneg as Hcf0.
      destruct (fp_blocks ly S Hp W mem md _ _ HAR Hkin) as (Hp16 & Hp4096 & Hpceil).
      unfold req_size in Hpceil. destruct (Z.eqb_spec (k + cf_head) 0) as [E0|E0]; apply KE; lia.
    * intros a k _ H. exact H.
    * apply Permutation_refl.
- (* len > 0: the shadow base, h = 5381, to the loop head *)
  rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite U11 in Hc.
  assert (Hx : x <> []) by (intros ->; vm_compute in Hc; discriminate Hc).
  clear Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM FP_Bspan FP_LOOP.
  { fp_wr Usp WS. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
    assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
      aview SEGS (w_H W) (ms_mem mx) a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hna; rewrite (fp_win_kept _ _ _ _ _ a HFr Ha) by fp_notw Usp; exact (KE1 a Ha Hna)) end.
  clear HF HFr HG KE1.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
  prreg HS (12%bv : bv 5) R12. prreg HS (13%bv : bv 5) R13. prreg HS (14%bv : bv 5) R14. prreg HS (15%bv : bv 5) R15.
  prreg HS (16%bv : bv 5) R16. prreg HS (17%bv : bv 5) R17.
  rewrite E1 in R1. rewrite Usp in R2. rewrite E10 in R10, R13, R17. rewrite E11 in R11. rewrite E12 in R12.
  rewrite E32 in R15.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msL end.
  assert (SP : spZ (ms_regs msL) = spZ regs - 16) by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
  pose proof (fp_region_nth _ _ _ 0 _ HS eq_refl) as RS. cbn [ms_mem restrict] in RS.
  pose proof (fp_field _ _ 2%nat (spZ regs) _ _ _ _ _ (-8) 8 (SOff 1 0) (bv_unsigned (getr regs 1)) RS
    Usp ltac:(left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Rr; unfold bv_modulus in Rr; cbn in Rr |- *; lia)
    ltac:(zside)) as VS.
  pmkst HS. change (BASE + 14084) with (BASE + FP_LOOP).
  assert (Hpe : p + Z.of_nat (length x) <= 2 ^ 47 - 1) by (unfold amem_range in Ham; lia).
  eapply SRr_mono.
  { eapply (fp_loop x W (ms_regs msL) (ms_mem msL) _ STK_fuzz_pick (spZ regs) [] ly S Hp W mem md [] ly S Hp 0 mem
      p p n 5381).
    - exact Hx.
    - lia.
    - exact HJ.
    - exact HPM.
    - rewrite R1. exact Hra.
    - exact R10.
    - exact R11.
    - exact R12.
    - exact R13.
    - exact R14.
    - exact R15.
    - exact R16.
    - exact R17.
    - rewrite SP. replace (spZ regs - 16) with (spZ regs + (-1) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
    - rewrite SP. lia.
    - rewrite SP. lia.
    - rewrite SP, R1. replace (spZ regs - 16 + 8) with (spZ regs + -8) by lia. exact VS.
    - lia.
    - exact Ham.
    - rewrite SP. lia.
    - lia.
    - lia.
    - apply (fp_garr8_kept SEGS (w_H W) mem); [intros a0 Ha0; apply KE2; lia | exact GT].
    - apply (fp_ra_kept SEGS (w_H W) mem); [|exact HRA].
      intros a0 Ha0. pose proof (Z.div_pos a0 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound a0 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
      apply KE2; unfold shadow_of_addr, SHADOW_OFF; lia. }
  cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HK5 & Hsp5 & Hkp5 & HPM5 & V5).
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview SEGS (w_H W) mem5 a = aview SEGS (w_H W) mem a)
    by (intros a Ha Hna; rewrite (Hkp5 a Ha); exact (KE2 a Ha Hna)).
  unfold fpostm, fpost, fQmn, apost_base_x. cbv beta.
  exists ly, S, Hp, regs5, mem5, md5, 0.
  split; [rewrite R1; reflexivity|].
  split; [exact HJ5|].
  split.
  { apply fp_aregs.
    - intros r Hr. rewrite (HK5 r Hr).
      exact (regs_kept_of_st_ok_pi _ _ _ regs _ FP_KEPT HS HAE ltac:(vm_compute; reflexivity) r Hr).
    - rewrite Hsp5, SP. replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold w64, spZ. apply Z_to_bv_bv_unsigned. }
  split; [|exact HPM5].
  split; [rewrite V5; unfold ck_pick; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros Hr0; exact Hr0|].
  split.
  + eapply prh_ledger_kept_aview; [exact HL0 | | | |].
    * intros a Ha. destruct (fp_pst_low a Ha) as [Ha0 Ha1]. apply KF; lia.
    * intros a k i Hin Hi. pose proof HL0 as (_ & _ & HLF & _). rewrite Forall_forall in HLF.
      destruct (HLF (a, k) Hin) as (Hk0 & Hkin & _). cbn [fst snd] in Hk0, Hkin.
      pose proof cf_head_nonneg as Hcf0.
      destruct (fp_blocks ly S Hp W mem md _ _ HAR Hkin) as (Hp16 & Hp4096 & Hpceil).
      unfold req_size in Hpceil. destruct (Z.eqb_spec (k + cf_head) 0) as [E0|E0]; apply KF; lia.
    * intros a k _ H. exact H.
    * apply Permutation_refl.
  + unfold bytes_at. apply (fp_garr8_kept SEGS (w_H W) mem); [intros a0 Ha0; apply KF; lia | exact GT].
Qed.
End f.
End w.

(* ---------------------------------------------------------------------- *)
(* THE TOP: the kit's text at the B' halts top's instance. Its type is HaltsClosedB.v's H_text_fuzz_pick_B
   (a working branch 5f51f36fad3f :257-259) in the same frame: the two local instances (the start-up
   float state YK11.fx0 and the image's CfImg_B, HaltsClosedB.v :125 / :127), the abbreviations PAB / ARi / RLX / SEGS_B
   (:132-135) and the same named arguments. The names are qualified because this file Imports none of the halts top's
   modules. Required here, after the walk: PAImg_prog's PI_prog_B is a global instance. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PAImg_prog PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB PresetCfnB.

Section top.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Abbreviation PAB r := (PAImg_prog.PI_prog_B (rc := r)).
#[local] Abbreviation ARi r := (PresetCfnB.iface_ARx (rc := r) (L := B_prog_listing) (PA := PAB r) YD2l.TfibB).
#[local] Abbreviation RLX := (@prh_room_live_a8 CfParamsPreset.CfParams_preset).
#[local] Abbreviation SEGS_B r := (@pa_segs r B_prog_listing (PAB r)).

(* FP_IMG at PI_prog_B: the entry 0x84da4 is the listing base 0x816cc plus 4 * 3510, and the image top 0x601000 lies
   below 2 ^ 31 *)
Lemma fp_img_B : forall rc : YM05.RunCeil, FP_IMG (rc := rc) (PA := PAB rc).
Proof.
intros rc. constructor.
- apply Z.eqb_eq. vm_compute. reflexivity.
- apply Z.leb_le. vm_compute. reflexivity.
Qed.

(* the image binding at TfibB: a Theorem Labs lane's PALib for B' (lib/B/PALibB.v, every field by vm_compute) *)
Lemma fp_palib_B : forall rc : YM05.RunCeil, PALibCore (rc := rc) (L := B_prog_listing) (PI := PAB rc) YD2l.TfibB.
Proof. intros rc. exact (YC1fP.palib_core YD2l.TfibB PALibB.exvi_eh_palib). Qed.

(* the engine laws at iface_ARx (HaltsClosedB.v laws_iface_B, the same proof) *)
Lemma fp_laws_B : forall rc : YM05.RunCeil,
  YCbqG.AR_laws_x (SEGS_B rc) YD2l.TfibB (ARi rc) (@cf_head CfParamsPreset.CfParams_preset).
Proof.
intros rc. unfold PresetCfnB.iface_ARx.
exact (YGcallcf.AR_laws_x_xs (cp := CfParamsPreset.CfParams_preset) (SEGS_B rc) YD2l.TfibB
  (YG0lawscf.AR_laws_ok_cf (cp := CfParamsPreset.CfParams_preset) (SEGS_B rc) YD2l.TfibB)).
Qed.

Theorem fuzz_pick_holds_B : forall (rc : YM05.RunCeil) (fy : YK11.FPState),
  PRH_FnCheck.tfuzz_pick_specX (fx := fy) (rc := rc) (cp := CfParamsPreset.CfParams_preset)
    (PI := PresetCfnB.preset_prh_img) (RL := RLX) (L := B_prog_listing) (PA := PAB rc) YD2l.TfibB (ARi rc)
    PresetCfnB.preset_sink_head.
Proof.
intros rc fy.
exact (fuzz_pick_walk_B (fx := fy) (rc := rc) (cp := CfParamsPreset.CfParams_preset) (RL := RLX) (PA := PAB rc)
  YD2l.TfibB (ARi rc) PresetCfnB.preset_sink_head (fp_laws_B rc) (fp_img_B rc) (fp_palib_B rc)).
Qed.
End top.

Set Printing Implicit.
Check fuzz_pick_holds_B.
Unset Printing Implicit.
Print Assumptions fuzz_pick_holds_B.
