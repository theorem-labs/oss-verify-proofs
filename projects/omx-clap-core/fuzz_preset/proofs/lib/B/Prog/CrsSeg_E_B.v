(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACem.v, with its module paths and module names changed; 884 of its 944 lines of code are new or changed and 391 lines of the source are left out. *)
(* fuzz_preset, image B' (the #102 pins, asan-ubsan): SEGMENT E of the walk of check_reject_clean_starved against the kit's
   text tcheck_reject_clean_starved_specX, row E_B (a Theorem Labs lane's internal file BRIEF-crcs-Bprime-seg.md; family lead a Theorem Labs lane).
   rule 24: proves function check_reject_clean_starved on image B' (reuse search: `proof-index check_reject_clean_starved 0x82160`, the internal file
   index-crcs-Aprime.out, and an internal record of that lookup; CONFIRM by checker LookupCheckCrcsAp. At that search origin/ossv/recipes had no lib/A or lib/B, its
   released rows were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released asan Proof.v existed for check_reject_clean_starved).
   DONOR: the A' segment lib/A/Prog/CrsSeg_E.v (blob c7928c832ea9, a working branch 80467ffbd3ed, kit
   v4): the same lemmas, the same premise names and order, every kit name with the B' kit's `_B` / `cb_*` spelling.
   INPUTS.
   - Pin: B' asan-ubsan sha256 d663f82d7f488d30 (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1).
   - Listing: lib/B/Listing_prog.v blob c97cc46b3e13 + lib/B/PAImg_prog.v blob 15fab93fe702 (listings v3). Entry
     0x820e0 = slot 645 (B_entry_check_reject_clean_starved); image record lib/B/PRH_ImgB.v blob 3216eca68342.
   - The kit text: tcheck_reject_clean_starved_specX in lib/A/PRH_FnCheck.v blob 9ecd8eb167c6, callee text
      tfuzz_alloc_live_specX in lib/A/PRH_FnAlloc.v blob 740f4d11d144, lib/A/PRH_Base.v blob fdb45545469b,
      at PI := prh_img_B, PA := PI_prog_B.
   - Kit: lib/B/Prog/CrsKitBp.v blob 1dd89c0383ac at a working branch a179cedc95a7 (FROZEN, cited).
   THE CLOSING LEMMA crs_seg_E_B: (forall p, crs_from_H1_B .. (crs_with_fpos_B C p)) -> crs_from_E_B .. C, premises in
   the A' order: HX_asmr (YGcallMxmn.astack_malloc_realizes_xm at class 1), HX_ownlow (ARx_owned_low_law), HX_pal
   (PALib at PI_prog_B; B' instance: lib/B/PALibB.v exvi_eh_palib), HX_pal_uar_img (the use-after-return cell in
   [pa_lo, pa_hi) of PI_prog_B), HX_pal_sm1 (__asan_stack_malloc_1's code address), HX_pal_pst_static (alloc.c's
   statics neither runtime-owned nor errno), HI_head8 (8 <= cf_head; witness crs_seg_E_B_HI_head8_B' at the end of
   this file), HT_fuzz_alloc_live (the kit's callee text), HK (the kit's CrsKeep_B). The B' witnesses of HX_pal_uar_img /
   HX_pal_sm1 / HX_pal_pst_static are lib/B/Prog/CrsWitBp.v. The only run-position step is ce_pos_E
   (crs_evs_at_H1_B = []).
   THE BODY WALKED (+0 .. +296, B' 0x820e0-0x82204, listing slots 645-718). Measured on the B' listing: the same words
   as the A' segment slot for slot (A' 736-809), only the hi-atom numbers of the four auipc and the two auipc-relative
   immediates differ (the runner resolves them through pa_val); so the same seams +100 / +104 / +124 / +296:
     A1 +0    the prologue, the 13 saves, `addi s0, sp, 128`, `andi sp, sp, -32`, the argument moves, the two GOT words
     A2 +100  `lw a2, 0(a2)`: the use-after-return word, 1 by ARx_const_law
     A3 +104  `ld s11, 0(a1)`, `mv s5, a0`, `beqz a2` (NOT taken), `li a0, 128`, `jal __asan_stack_malloc_1` (+120)
     call     __asan_stack_malloc_1 through YGcallMxmn.aj_stack_malloc_at_xm at class 1; capacity crs_cap_pre_B
     B  +124  `mv s2, a0`, `bnez s2` (TAKEN), `sd s10, 16(s1)`, the frame header, s9, the sixteen shadow bytes,
              `jal fuzz_alloc_live` (+292); its return site is H1
   UNREACHABLE ARMS, each refuted: `beqz a2` at +112 (a2 = 1, alx_const); the real-stack fallback +132 .. +168
   (s2 = frame_addr >= 4096, ARx_frames_law). E has no UBSan check, no report arm, no own check and no abort arm.
   S10 COPIES (helpers, statement and proof verbatim, each named at its source): the B' walk environment
   (PRW_WalkEnv.v's TE part at PI_prog_B, now Required from lib/B/Prog/PRW_WalkEnvB.v), S10Env.v blob d8ca1dd59ead (te_img, ts_vm_present, ts_rdword_keep, ts_vm_av,
   ts_region_nth_c, ts_alias_shadow, te_close, ts_cs, ts_ap, ts_le_byte1, ts_aview_of_vm1, ts_garr_av), S10TxString.v
   (tskeep, cs_tac), S10TxState.v (s10_aview_present); YCem.v's rdword_of_val_mem.
   NUMERALS. LENGTH: 8 / 16 / 24 / 32 / 56 / 64 / 128 / 144, 4096. DERIVED: the seam offsets 100 / 104 / 124 / 296
   (4 * the B' listing slot from slot 645: B' 0x82144 / 0x82148 / 0x8215c / 0x82208) and the seam points
   BASE + 2680 / 2684 / 2704 / 2876 a run leaves in pc or ra (CRS_PC_E_B + a seam offset, by computation, in
   `change`), 2 ^ 31 / 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64, atom indices, A_OBJ 0 / 1 / 12. WORD: register indices.
   No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallScf YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnAlloc PRH_FnReader PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import CrsKitBp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PRW_WalkEnvB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require S1ImgB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Module MN := YAkMemnorm.

(* the segment environment TE and its lemmas (lib/A/Prog/PRW_WalkEnv.v's TE part at B'): lib/B/Prog/PRW_WalkEnvB.v,
   Required above; this file's own copy is gone (one copy for the walk) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- S10 COPIES (origin/cold/h-hpreset-7-walk-s10 88b4aea723f), statement and proof verbatim ---- *)

(* YCem.v:101 rdword_of_val_mem *)
Lemma ce_rdword_of_val_mem : forall {rc : YM05.RunCeil} segs H mem a v,
val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros rc segs H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* S10TxState.v s10_aview_present *)
Lemma ce_aview_present : forall {rc : YM05.RunCeil} segs (H : word -> bool) mem a, apresent H mem a -> aview segs H mem a <> None.
Proof.
intros rc segs H mem a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

Section s10e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
(* S10Env.v:106 te_img *)
Lemma ce_te_img : forall regs0 regsc more n, (A_TEXT <= n < A_LIM)%nat -> ew (TE regs0 regsc more) n = Z_to_bv 64 (VAL n).
Proof. intros regs0 regsc more n Hn. unfold TE. apply Eimg_img. exact Hn. Qed.
(* S10Env.v:184 ts_region_nth_c *)
Lemma ce_region_nth_c : forall E ss ms i r, st_ok SEGS E ss ms -> nth_error (ss_mem ss) i = Some r ->
  YP09.region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok SEGS E _ ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
(* S10Env.v:219 ts_vm_present *)
Lemma ce_vm_present : forall (H : word -> bool) m a n v, val_mem SEGS (mrestrict H m) a n v ->
  forall j, (j < n)%nat -> aview SEGS H m (a + Z.of_nat j) <> None.
Proof. intros H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). discriminate. Qed.
(* S10Env.v:223 ts_rdword_keep *)
Lemma ce_rdword_keep : forall (rd rd' : reader) a, (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold rdword.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
(* S10Env.v:249 ts_vm_av *)
Lemma ce_vm_av : forall (H H' : word -> bool) m m' a n v,
  (forall j, (j < n)%nat -> aview SEGS H' m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hag HV j Hj. rewrite (mbyte_of_aview SEGS H H' m m' _ (Hag j Hj)). exact (HV j Hj).
Qed.
(* S10Env.v:281 ts_alias_shadow *)
Lemma ce_alias_shadow : forall E nF nB nS F, bv_unsigned (ew E nF) = F -> bv_unsigned (ew E nB) = SHADOW_OFF ->
  bv_unsigned (ew E nS) = shadow_addr F -> 0 <= F < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff nF 0) (SLit 3)) (SOff nB 0)) = sv_denot E (SOff nS 0).
Proof.
intros E nF nB nS F HF HB HS HFr. apply U_inj. rewrite !U_SAlu, !U_SOff, U_SLit, HF, HB, HS.
unfold zcanon, M64, zalu_raw, shadow_addr, SHADOW_OFF.
change (Z.land (3 mod 2 ^ 64) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= F / 8 < 2 ^ 44) by lia. rewrite !Z.add_0_r. rewrite !Z.mod_small; lia.
Qed.
End s10e.

(* S10Env.v:372 te_close *)
Local Ltac ce_te_close :=
  lazymatch goal with |- ew (TE ?r0 ?rc ?mo) ?n = _ =>
    let nn := eval vm_compute in n in
    lazymatch eval vm_compute in (Nat.ltb nn 32) with
    | true => apply (te_entry r0 rc mo _ nn); reflexivity
    | false => lazymatch eval vm_compute in (Nat.ltb nn 64) with
      | true => let kk := eval vm_compute in (Nat.sub nn 32) in apply (te_cur r0 rc mo _ kk); reflexivity
      | false => let j := eval vm_compute in (Nat.sub nn 64) in rewrite (te_more_lt r0 rc mo j) by lia; reflexivity
      end
    end
  end.
(* S10TxString.v:117 tskeep *)
Local Ltac ce_keep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; ce_te_close end.
(* S10TxString.v:120 cs_tac *)
Local Ltac ce_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.
(* S10Env.v:388 ts_ap *)
Lemma ce_ap : forall rg rg' (r : bv 5), aregs_preserved rg rg' -> acallee_saved (bv_unsigned r) -> getr rg' r = getr rg r.
Proof. intros rg rg' r HP Hr. pose proof (HP _ Hr) as Hq. rewrite Z_to_bv_bv_unsigned in Hq. exact Hq. Qed.

(* ======================================================================================================== *)
(* ---- SEGMENT E ---- *)

(* the seams, offsets from the entry (4 * the listing slot from slot 736) *)
Definition CE_A2_OFF : Z := 100.   (* lw a2, 0(a2): the use-after-return word *)
Definition CE_A3_OFF : Z := 104.   (* ld s11, 0(a1): the shadow base *)
Definition CE_B_OFF : Z := 124.    (* __asan_stack_malloc_1's return site *)
(* the realigned sp after `addi sp, sp, -128` and `andi sp, sp, -32` *)
Definition ce_sp2 (sp0 : Z) : Z := (sp0 - 128) / 32 * 32.

Lemma ce_sp2_range : forall sp0, sp0 mod 16 = 0 -> 144 <= sp0 ->
  0 <= ce_sp2 sp0 /\ sp0 - 144 <= ce_sp2 sp0 <= sp0 - 128 /\ ce_sp2 sp0 mod 32 = 0.
Proof.
intros sp0 Hal H. unfold ce_sp2. pose proof (Z.mul_div_le (sp0 - 128) 32 ltac:(lia)).
pose proof (Z.mod_pos_bound (sp0 - 128) 32 ltac:(lia)). pose proof (Z.div_mod (sp0 - 128) 32 ltac:(lia)).
split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia|].
split; [|apply Z.mod_mul; lia]. split; [|lia].
assert ((sp0 - 128) mod 32 = 0 \/ (sp0 - 128) mod 32 = 16) as [Hm|Hm]
  by (rewrite Z.mod_divide in Hal by lia; destruct Hal as [q ->]; lia); lia.
Qed.

Lemma ce_sp2_word : forall (w : word), 128 <= bv_unsigned w ->
  alu64 ALU_AND (Z_to_bv 64 (bv_unsigned w + -128)) (Z_to_bv 64 (-32)) = w64 (ce_sp2 (bv_unsigned w)).
Proof.
intros w H128. pose proof (bv_unsigned_in_range 64 w) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned. unfold w64, ce_sp2 in *.
rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small (bv_unsigned w + -128)) by lia.
change ((-32) mod 2 ^ 64) with (2 ^ 64 - 32). rewrite ts_land_m32 by lia.
rewrite Z.mod_small; [lia|]. split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia|].
pose proof (Z.mul_div_le (bv_unsigned w - 128) 32 ltac:(lia)). lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).

Lemma ce_pa_hi : @pa_hi _ B_prog_listing PA <= 2 ^ 31.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma ce_pa_lo : 0 <= @pa_lo _ B_prog_listing PA.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma ce_stk_vals : STK_check_reject_clean_starved (PI := prh_img_B) = 27312 /\ STK_fuzz_alloc_live (PI := prh_img_B) = 0.
Proof. vm_compute. split; reflexivity. Qed.
(* the read-only view's addresses are image addresses (S10TxStrGlue.v:134 ts_ro_img, verbatim) *)
Lemma ce_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation LEDGER := (prh_ledger (PI := prh_img_B) (PA := PA) B).
#[local] Notation STK := (STK_check_reject_clean_starved (PI := prh_img_B)).

(* ---- segment A1: the prologue, the GOT words, to the flag's load ---- *)
Definition ce_A1_regions : smem :=
  [ YP09.mkRegion (Some 2%nat) (-128) 0 (-128) 0 [];
    got_regionP;
    YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 64 0))] ].
Definition ce_A1_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ce_ss_A1 : sstate := mkSS CRS_PC_E_B sr_atoms ce_A1_regions None ce_A1_facts.

Lemma ce_A1_entry : forall STK0 ly S Hp W regs mem md ch,
  PALib (L := B_prog_listing) (PI := PA) B -> 128 <= STK0 ->
  afn_pre_x SEGS B ARx STK0 ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (TE regs regs [w64 (as_uar_cell B)]) ce_ss_A1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CRS_PC_E_B)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs regs [w64 (as_uar_cell B)]) (mrestrict (w_H W) mem).
Proof.
intros STK0 ly S Hp W regs mem md ch PAL H128 HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kgotu).
rewrite (pal_got_shadow (PI := PA) B PAL), (pal_cell (PI := PA) B PAL) in Kgot.
rewrite (pal_got_uar (PI := PA) B PAL) in Kgotu.
pose proof (pal_got_uar_disj (PI := PA) B PAL) as (D01 & _).
set (E := TE regs regs [w64 (as_uar_cell B)]).
assert (E2 : ew E 2 = getr regs 2) by (apply te_entry; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E64 : ew E 64 = w64 (as_uar_cell B)) by exact (te_more_lt regs regs [w64 (as_uar_cell B)] 0 ltac:(lia)).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (apply ce_te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply ce_te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (apply ce_te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (@pa_val_range _ _ PA (A_OBJ 0)) as R0. pose proof (@pa_val_range _ _ PA (A_OBJ 1)) as R1.
pose proof (@pa_val_range _ _ PA (A_OBJ 12)) as R12.
pose proof (ts_rdword_range _ _ _ _ Kgotu) as Ruar.
pose proof (@pa_obj_img _ _ PA 0 ltac:(lia)) as I0. pose proof (@pa_obj_img _ _ PA 1 ltac:(lia)) as I1.
pose proof ce_pa_hi as Hhi.
split.
- apply ts_st_ok.
  all: try change (TE regs regs [w64 (as_uar_cell B)]) with E.
  + unfold E, TE. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ce_A1_regions, got_regionP. repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_rok E _ 2 (spZ regs)); [exact Usp | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * apply (ts_rok E _ (A_OBJ 0) (VAL (A_OBJ 0))); [rewrite Eo0; apply unsigned_lit_small; lia | lia | lia | intros o Ho; lia |].
      constructor; [|constructor].
      apply (ts_chunk E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * apply (ts_rok E _ (A_OBJ 1) (VAL (A_OBJ 1))); [rewrite Eo1; apply unsigned_lit_small; lia | lia | lia | intros o Ho; lia |].
      constructor; [|constructor].
      apply (ts_chunk E _ _ 0 8 (SOff 64 0) (as_uar_cell B));
        [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgotu).
  + apply pairwise_disjoint_of_extents. unfold ce_A1_regions, got_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite Usp, Eo0, Eo1, !unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [ce_A1_facts f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16. lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- segment A2: the flag's load (one instruction; the flag cell is the only region) ---- *)
Definition ce_ss_A2 : sstate :=
  mkSS (CRS_PC_E_B + CE_A2_OFF) cur_atoms [YP09.mkRegion (Some (xr 12)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]] None
    (mkFacts [] [] []).
Lemma ce_A2_entry : forall regs regsc memc (Wc : world SEGS),
  @pa_lo _ B_prog_listing PA <= as_uar_cell B /\ as_uar_cell B + 4 <= @pa_hi _ B_prog_listing PA ->
  getr regsc 12 = w64 (as_uar_cell B) -> rd32 (aview SEGS (w_H Wc) memc) (as_uar_cell B) 1 ->
  st_ok_pi SEGS VAL (TE regs regsc []) ce_ss_A2
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (CRS_PC_E_B + CE_A2_OFF))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs regsc []) (mrestrict (w_H Wc) memc).
Proof.
intros regs regsc memc Wc Huar R12 Hu. pose proof ce_pa_hi as Hhi. pose proof ce_pa_lo as Hlo.
set (E := TE regs regsc []).
assert (X12 : bv_unsigned (ew E (xr 12)) = as_uar_cell B).
{ unfold E, xr. rewrite (te_cur regs regsc [] 12%bv 12) by reflexivity. rewrite R12. apply unsigned_lit_small. lia. }
split.
- apply ts_st_ok.
  all: try change (TE regs regsc []) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + constructor; [|constructor].
    apply (ts_rok E _ (xr 12) (as_uar_cell B)); [exact X12 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 0 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (ts_val_mem_rd32 _ _ _ _ Hu).
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [exact I | split; exact I].
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- segment A3: the shadow base's load, `mv s5, a0`, the flag test, `li a0, 128`, to the frame call ---- *)
Definition ce_ss_A3 : sstate :=
  mkSS (CRS_PC_E_B + CE_A3_OFF) cur_atoms [YP09.mkRegion (Some (xr 11)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 64 0))]] None
    (mkFacts [(xr 12, mkAF 1 1 0)] [] []).
Lemma ce_A3_entry : forall regs regsc memc (Wc : world SEGS),
  getr regsc 11 = w64 (VAL (A_OBJ 12)) -> getr regsc 12 = w64 1 ->
  rdword (aview SEGS (w_H Wc) memc) (VAL (A_OBJ 12)) = Some SHADOW_OFF ->
  st_ok_pi SEGS VAL (TE regs regsc [w64 SHADOW_OFF]) ce_ss_A3
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (CRS_PC_E_B + CE_A3_OFF))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs regsc [w64 SHADOW_OFF]) (mrestrict (w_H Wc) memc).
Proof.
intros regs regsc memc Wc R11 R12 Hc.
pose proof (@pa_obj_img _ _ PA 12 ltac:(lia)) as I12.
pose proof ce_pa_hi as Hhi. pose proof (@pa_val_range _ _ PA (A_OBJ 12)) as R12v.
set (E := TE regs regsc [w64 SHADOW_OFF]).
assert (X11 : bv_unsigned (ew E (xr 11)) = VAL (A_OBJ 12)).
{ unfold E, xr. rewrite (te_cur regs regsc _ 11%bv 11) by reflexivity. rewrite R11. apply unsigned_lit_small. lia. }
assert (X12 : bv_unsigned (ew E (xr 12)) = 1).
{ unfold E, xr. rewrite (te_cur regs regsc _ 12%bv 12) by reflexivity. rewrite R12. reflexivity. }
assert (E64 : ew E 64 = w64 SHADOW_OFF) by exact (te_more_lt regs regsc [w64 SHADOW_OFF] 0 ltac:(lia)).
split.
- apply ts_st_ok.
  all: try change (TE regs regsc [w64 SHADOW_OFF]) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + constructor; [|constructor].
    apply (ts_rok E _ (xr 11) (VAL (A_OBJ 12))); [exact X11 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 0 8 (SOff 64 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Hc).
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X12. cbn. lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- segment B: after __asan_stack_malloc_1 (+124), the frame's header and shadow, to fuzz_alloc_live's call.
   Regions: s1's slot [sp2 + 16, sp2 + 24), the fake frame's header [F, F + 24), F's 16 shadow bytes (atom 64 = the
   shadow pointer, aliased to `(F >> 3) + s11`). Facts: s1 = sp2 in the stack band, a0 = F at or above the code floor
   (so `bnez s2` is TAKEN and the real-stack fallback +132 .. +168 is refuted), s11 = the shadow base. ---- *)
Definition ce_ss_B : sstate := mkSS (CRS_PC_E_B + CE_B_OFF) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 16 24 16 24 [];
    YP09.mkRegion (Some (xr 10)) 0 24 0 24 [];
    YP09.mkRegion (Some 64%nat) 0 16 0 16 [] ] None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 10, mkAF 4096 (2 ^ 47) 5); (xr 27, mkAF SHADOW_OFF SHADOW_OFF 0);
            (64%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)] []
           [(SAlu ALU_ADD (SAlu ALU_SRL (SOff (xr 10) 0) (SLit 3)) (SOff (xr 27) 0), SOff 64 0)]).
Lemma ce_B_entry : forall regs lyc Sc Hpc Wc memc mdc pos rg sp2,
  ARx lyc Sc Hpc Wc memc mdc -> In (1, pos) (frames Sc) ->
  (forall a, sp2 + 16 <= a < sp2 + 24 -> apresent (w_H Wc) memc a) ->
  YM05.alloc_ceiling <= sp2 -> sp2 + 64 <= 2 ^ 47 -> sp2 mod 32 = 0 ->
  getr rg 9 = w64 sp2 -> getr rg 10 = w64 (frame_addr lyc 1 pos) -> getr rg 27 = w64 SHADOW_OFF ->
  st_ok_pi SEGS VAL (TE regs rg [w64 (shadow_addr (frame_addr lyc 1 pos))]) ce_ss_B
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (CRS_PC_E_B + CE_B_OFF))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs rg [w64 (shadow_addr (frame_addr lyc 1 pos))]) (mrestrict (w_H Wc) memc).
Proof.
intros regs lyc Sc Hpc Wc memc mdc pos rg sp2 HAR Hin Hsp Hc Hc47' Hsp32 R9 R10 R27.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc 1 pos HAR Hin) as (F1 & F2 & F3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc 1 pos HAR Hin) as (F32 & _ & Fpr & Fsh).
change (fs_frame_bytes 1) with 128 in F2, F3, Fpr, Fsh.
set (F := frame_addr lyc 1 pos) in *.
set (E := TE regs rg [w64 (shadow_addr F)]).
assert (X9 : bv_unsigned (ew E (xr 9)) = sp2).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X10 : bv_unsigned (ew E (xr 10)) = F).
{ unfold E, xr. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. rewrite R10. apply unsigned_lit_small. lia. }
assert (X27 : bv_unsigned (ew E (xr 27)) = SHADOW_OFF).
{ unfold E, xr. rewrite (te_cur regs rg _ 27%bv 27) by reflexivity. rewrite R27. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (Hsh2 : SHADOW_OFF <= shadow_addr F <= SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (Hsh : 0 <= shadow_addr F < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
assert (X64 : bv_unsigned (ew E 64) = shadow_addr F).
{ unfold E. rewrite (te_more_lt regs rg _ 0) by lia. cbn [nth]. apply unsigned_lit_small. exact Hsh. }
unfold SHADOW_OFF in Hsh2.
split.
- apply ts_st_ok.
  all: try change (TE regs rg [w64 (shadow_addr F)]) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_rok E _ (xr 9) sp2); [exact X9 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hsp. lia.
    * apply (ts_rok E _ (xr 10) F); [exact X10 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Fpr. lia.
    * apply (ts_rok E _ 64 (shadow_addr F)); [exact X64 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Fsh o ltac:(lia))).
  + apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X9, X10, X64.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. repeat split; lia.
  + split; [|split; [exact I|]].
    * cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X9, X10, X27, X64.
      change (2 ^ 5) with 32. change (2 ^ 0) with 1.
      unfold shadow_addr, SHADOW_OFF. repeat split; try lia.
    * cbn [f_alias alias_ok]. split; [|exact I].
      apply (ce_alias_shadow E (xr 10) (xr 27) 64 F X10 X27 X64). lia.
- unfold sh_ok. apply Forall_nil.
Qed.

End f.
End d.

(* ======================================================================================================== *)
(* ---- SEGMENT E: the walk, inside the kit's Sections again (B / ARx / LAWS) ---- *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation LEDGER := (prh_ledger (PI := prh_img_B) (PA := PA) B).
#[local] Notation STK := (STK_check_reject_clean_starved (PI := prh_img_B)).

(* S10Env.v:291 ts_le_byte1, :296 ts_aview_of_vm1, :255 ts_garr_av *)
Lemma ce_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite !Z.mod_small; lia.
Qed.
Lemma ce_aview_of_vm1 : forall (H : word -> bool) m a v, val_mem SEGS (mrestrict H m) a 1 v -> 0 <= v < 256 ->
  aview SEGS H m a = Some v.
Proof.
intros H m a v HV Hv. pose proof (HV 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0.
unfold aview. rewrite H0. cbn [option_map]. f_equal. rewrite ce_le_byte1 by exact Hv.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.
Lemma ce_garr_av : forall (H H' : word -> bool) m m' a l,
  (forall j, (j < length l)%nat -> aview SEGS H' m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hag HG j Hj. destruct (HG j Hj) as [V R]. split; [|exact R].
apply (ce_vm_av H H' m m' _ 1 _); [|exact V].
intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat]. rewrite Z.add_0_r. exact (Hag j Hj).
Qed.

(* one shadow byte of the frame after segment B, read off the run's shadow region *)
Local Ltac ce_shb E HR2 U64 :=
  lazymatch goal with |- exists v, aview _ _ _ (shadow_addr ?Fv + ?jj) = Some v /\ _ =>
    lazymatch type of HR2 with context [YP09.mkChunk jj (CVal 1 (SLit ?vv))] =>
      let vb := eval vm_compute in (vv mod 256) in
      let V := fresh "V" in
      pose proof (ts_field E _ 64 (shadow_addr Fv) _ _ _ _ _ jj 1 (SLit vv) HR2 U64
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
      change (N.to_nat 1) with 1%nat in V;
      replace (U E (SLit vv) mod 2 ^ (8 * Z.of_N 1)) with vb in V by (rewrite U_SLit; vm_compute; reflexivity);
      exists vb; split; [apply ce_aview_of_vm1; [exact V | lia] | intros; first [reflexivity | lia]]
    end end.
(* ---- transport helpers ---- *)
(* the ledger across a step that keeps the allocator blocks and changes no byte of alloc.c's statics nor of a block *)
Lemma ce_ledger_move : forall ly S Hp (Wa : world SEGS) mema ly' S' (Wb : world SEGS) memb Lam peak cnt fail ran most own,
  8 <= cf_head ->
  LEDGER ly S Hp Wa mema Lam peak cnt fail ran most own ->
  ablocks B ly' S' = ablocks B ly S ->
  (forall a, Exists (in_zr a) PST -> aview SEGS (w_H Wb) memb a = aview SEGS (w_H Wa) mema a) ->
  (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n ->
     aview SEGS (w_H Wb) memb (p + i) = aview SEGS (w_H Wa) mema (p + i)) ->
  LEDGER ly' S' Hp Wb memb Lam peak cnt fail ran most own.
Proof.
intros ly S Hp Wa mema ly' S' Wb memb Lam peak cnt fail ran most own H8 (HG & Hnd & HF & Hperm) Eab Kpst Kbl.
split; [|split; [exact Hnd | split; [|exact Hperm]]].
- unfold prh_glob, prh_most, prh_own in *. destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & GR).
  split; [|split; [|split; [|split; [|split; [|split; [split; [|exact G6r] | split; [split; [|exact G7r] | exact GR]]]]]]];
  (eapply ce_vm_av; [|eassumption]); intros j Hj; apply Kpst; unfold prh_pst;
  repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
- rewrite Forall_forall in HF |- *. intros [a kk] Hin. specialize (HF _ Hin). cbn [fst snd] in *.
  unfold prh_hblock in *.
  destruct HF as (Hk & Hab & Hhp & Ha16 & Hv).
  split; [exact Hk|]. split; [rewrite Eab; exact Hab|]. split; [exact Hhp|]. split; [exact Ha16|].
  eapply ce_vm_av; [|exact Hv]. intros j Hj.
  apply (Kbl (a - cf_head) (kk + cf_head) (Z.of_nat j) Hab). unfold req_size. destruct (Z.eqb_spec (kk + cf_head) 0); lia.
Qed.

(* the thirteen saved words across a step that keeps [sp0 - 104, sp0) *)
Lemma ce_saved_keep : forall (C : crsC_B) (Wa Wb : world SEGS) mema memb,
  crs_saved_B C Wa mema ->
  (forall a, spZ (cb_regs C) - 104 <= a < spZ (cb_regs C) -> aview SEGS (w_H Wb) memb a = aview SEGS (w_H Wa) mema a) ->
  crs_saved_B C Wb memb.
Proof.
intros C Wa Wb mema memb H K. unfold crs_saved_B in *. rewrite Forall_forall in *.
intros p Hp. rewrite <- (H p Hp). apply ce_rdword_keep. intros j Hj. apply K.
unfold CRS_SAVED_B in Hp. cbn [In] in Hp.
repeat (destruct Hp as [<- | Hp]; [cbn [fst]; lia|]). destruct Hp.
Qed.

(* the view of two memories equal at every address *)
Lemma ce_aview_ext : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a E. apply aview_eq_of. unfold mrestrict. rewrite E. reflexivity. Qed.
Lemma ce_memnorm_ext : forall (m m' : word -> option byte), (forall x, m' x = m x) -> MN.memnorm SEGS m -> MN.memnorm SEGS m'.
Proof. intros m m' E Hm. apply (MN.memnorm_sub SEGS m m' Hm). intros x b Hx. rewrite <- E. exact Hx. Qed.

(* THE POSITION STEP of segment E (one local lemma, h-w6u-rep's rule for kit v2): H1's boundary has made no run event
   (crs_evs_at_H1_B = []), and __asan_stack_malloc_1 changes st_fs only, so the entry's model-run position holds EXACTLY
   at the frame state (PresetRoomPosKeep.room_pos_set_fs) *)
Lemma ce_pos_E : forall (C : crsC_B) f ran3,
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) (cb_rp_H0 C) (cb_rp_hist C) (cb_S C) ->
  crs_pos_B C (crs_evs_at_H1_B C) ran3 (set_fs f (cb_S C)).
Proof.
intros C f ran3 H _. exists (cb_rp_hist C). unfold crs_evs_at_H1_B. cbn [length]. rewrite Nat.add_0_r.
exact (PresetRoomPosKeep.room_pos_set_fs _ _ _ _ _ _ _ f H).
Qed.

(* ---- SEGMENT B onwards (from __asan_stack_malloc_1's return to H1) ---- *)
Lemma ce_stage_B :
  (forall a, Exists (in_zr a) PST -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  8 <= cf_head ->
  PRH_FnAlloc.tfuzz_alloc_live_specX (fx := fx) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK ->
  CrsKeep_B (SK := SK) B ARx ->
  forall CTX0 (C : crsC_B),
  (forall p, crs_from_H1_B (fx := fx) (rc := rc) (SK := SK) B ARx CTX0 (crs_with_fpos_B C p)) ->
  crs_pre_B (fx := fx) (rc := rc) B ARx CTX0 C ->
  forall pos S2 mem2 md2 rg k f,
  AJ STK (spZ (cb_regs C)) [] (cb_ly C) (cb_S C) (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C) [(1, pos)]
     (cb_ly C) S2 (cb_Hp C) (cb_W C) mem2 md2 k ->
  S2 = set_fs f (cb_S C) ->
  rdword (aview SEGS (w_H (cb_W C)) mem2) (frame_addr (cb_ly C) 1 pos + 120) = Some (flag_addr (cb_ly C) 1 pos) ->
  crs_saved_B C (cb_W C) mem2 ->
  (forall a, spZ (cb_regs C) <= a < 2 ^ 64 ->
     aview SEGS (w_H (cb_W C)) mem2 a = aview SEGS (w_H (cb_W C)) (cb_mem C) a) ->
  LEDGER (cb_ly C) S2 (cb_Hp C) (cb_W C) mem2 (cb_Lam C) (cb_peak C) (cb_cnt C) SIZE_MAXZ (cb_ran C) (cb_most C) 0 ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H (cb_W C)) mem2) ->
  MN.memnorm SEGS mem2 ->
  getr rg 2 = w64 (ce_sp2 (spZ (cb_regs C))) -> getr rg 9 = w64 (ce_sp2 (spZ (cb_regs C))) ->
  getr rg 8 = getr (cb_regs C) 2 -> getr rg 3 = getr (cb_regs C) 3 -> getr rg 4 = getr (cb_regs C) 4 ->
  getr rg 19 = getr (cb_regs C) 13 -> getr rg 20 = getr (cb_regs C) 11 -> getr rg 21 = getr (cb_regs C) 10 ->
  getr rg 23 = getr (cb_regs C) 12 -> getr rg 27 = w64 SHADOW_OFF ->
  getr rg 10 = w64 (frame_addr (cb_ly C) 1 pos) ->
  SRr SEGS (cb_W C) (mkCfg (mkst rg (Z_to_bv 64 (BASE + (CRS_PC_E_B + CE_B_OFF))) mem2 (seg_rom SEGS)) md2)
    (fun W' c' => YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W' c' (crs_post_B (fx := fx) (rc := rc) (SK := SK) B ARx C)).
Proof.
intros HX_pal_pst_static HI_head8 HT_fuzz_alloc_live HK CTX0 C HH1 HPRE pos S2 mem2 md2 rg k f
  HJ ES2 HFL HSV HUP HLED2 HROD2 HMN2 R2 R9 R8 R3 R4 R19 R20 R21 R23 R27 R10.
pose proof HPRE as HPRE0.
destruct C as [ly S Hp W regs mem md ch data tb took doc t D Lam peak cnt ran most rp_x rp_os rp_i rp_H0 rp_hist fpos dp0 ws0].
unfold crs_pre_B, cSize_B in HPRE.
cbn [cb_ly cb_S cb_Hp cb_W cb_regs cb_mem cb_md cb_ch cb_data cb_tb cb_took cb_doc cb_t cb_D cb_Lam cb_peak cb_cnt cb_ran cb_most
  cb_rp_x cb_rp_os cb_rp_i cb_rp_H0 cb_rp_hist cb_fpos] in HPRE, HJ, HFL, HUP, HLED2, HROD2, R2, R9, R8, R3, R4, R19, R20, R21, R23, R10, ES2 |- *.
destruct HPRE as ((HAF & HROD & HSHI & HRAC & HFRM0) & HMN & HCL & HCTX & H10 & H11 & H12 & H13 & Hsz & Hd0 & Hd62 & HSRC & HHOME &
  Htook & HDOC & HLED & Hcnt & HRUN & Hran & HRQ & HRQW & HLIVE & HRQC & HFR & HROOM & HRP & HFRM & HWR0 & HSEC0 & H240 & HCONS0).
pose proof HAF as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
destruct ce_stk_vals as (ESTK & ESTK1).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof ce_pa_hi as Hhi.
destruct (ce_sp2_range (spZ regs) Hal16 ltac:(lia)) as (Hs0 & Hs1 & Hs32).
pose proof HJ as (HAR2 & HLY2 & _ & _ & _ & HFR2 & _ & _ & _ & _ & _ & _ & _ & HPR2 & _).
assert (Hin : In (1, pos) (frames S2)) by (rewrite HFR2; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS ly S2 Hp W mem2 md2 1 pos HAR2 Hin) as (F1 & F2 & F3).
change (fs_frame_bytes 1) with 128 in F2, F3.
destruct (ce_B_entry B ARx LAWS regs ly S2 Hp W mem2 md2 pos rg (ce_sp2 (spZ regs)) HAR2 Hin
  (fun a Ha => HPR2 a ltac:(lia)) ltac:(lia) ltac:(lia) Hs32 R9 R10 R27) as [HS SHOK].
pose proof HS as HSb.
set (F := frame_addr ly 1 pos) in *.
set (E := TE regs rg [w64 (shadow_addr F)]) in *.
assert (HEI : img_env VAL A_LIM E) by apply te_env.
assert (Hsh : 0 <= shadow_addr F < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (U9 : bv_unsigned (ew E (xr 9)) = ce_sp2 (spZ regs)).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. unfold w64. apply unsigned_lit_small. lia. }
assert (U10 : bv_unsigned (ew E (xr 10)) = F).
{ unfold E, xr. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. rewrite R10. unfold w64. apply unsigned_lit_small. lia. }
assert (U64 : bv_unsigned (ew E 64) = shadow_addr F).
{ unfold E. rewrite (te_more_lt regs rg _ 0) by lia. cbn [nth]. apply unsigned_lit_small. exact Hsh. }
pose (RUN := @paj_run_x fx rc SK B_prog_listing PL PA B PST ARx _ LAWS).
paj_run_tok_x RUN HS HJ SHOK (0, 0).
{ cbv [ce_ss_B ss_mem].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 9) (ce_sp2 (spZ regs) - spZ regs)); [reflexivity | | cbn; lia | cbn; lia |].
  { rewrite U9. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 10) F); [reflexivity | exact U10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 1, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 64%nat (shadow_addr F)); [reflexivity | exact U64 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 1, pos. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. fold F. lia. }
  apply awr_ok_nil. }
pose proof (ce_region_nth_c E _ _ 2 _ HS eq_refl) as HR2. cbn [ms_mem restrict] in HR2.
pose proof HJ as (HAR5 & HLY5 & _ & _ & _ & HFR5 & _ & _ & _ & _ & _ & _ & _ & HPR5 & _).
prreg HS (1%bv : bv 5) Q1. prreg HS (25%bv : bv 5) Q25. prreg HS (18%bv : bv 5) Q18. prreg HS (26%bv : bv 5) Q26.
assert (Y5 : forall (r : bv 5), In r [2; 3; 4; 8; 9; 19; 20; 21; 23; 27]%bv -> getr (ms_regs ms) r = getr rg r).
{ intros r Hr. cbv [In] in Hr. unfold E in HS.
  repeat (destruct Hr as [<- | Hr]; [ce_keep HS |]). destruct Hr. }
(* the run's writes: s1's slot, the frame's header, the frame's shadow *)
assert (Hwr : forall a, in_wrange E (ss_mem ce_ss_B) a ->
  (ce_sp2 (spZ regs) + 16 <= a < ce_sp2 (spZ regs) + 24) \/ (F <= a < F + 24) \/ (shadow_addr F <= a < shadow_addr F + 16)).
{ intros a (r & Hr & Ha). cbv [ce_ss_B ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ts_bv_some in Ha;
  [rewrite U9 in Ha; left | rewrite U10 in Ha; right; left | rewrite U64 in Ha; right; right]; lia. }
assert (K5 : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((ce_sp2 (spZ regs) + 16 <= a < ce_sp2 (spZ regs) + 24) \/ (F <= a < F + 24) \/
     (shadow_addr F <= a < shadow_addr F + 16)) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem2 a)
  by (intros a Ha Hn; exact (ts_keep W E (ss_mem ce_ss_B) mem2 (ms_mem ms) _ HFr Hwr a Ha Hn)).
assert (HMN5 : MN.memnorm SEGS (ms_mem ms)).
{ eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H W) E (abs_ss VAL ce_ss_B)); [| exact HSb |]; [exact HMN2 | exact HF]. }
(* ---- the facts at fuzz_alloc_live's call ---- *)
set (sp2 := ce_sp2 (spZ regs)) in *.
assert (KIMG : forall a, in_img SEGS a -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem2 a).
{ intros a Hi. pose proof (Hsegs a Hi) as Hr. apply K5; [lia|]. intros [Hs | [Hf | Hs]]; [lia | |].
  - exact (frm_img_x _ _ _ LAWS ly S2 Hp W mem2 md2 1 pos a HAR2 Hin ltac:(change (fs_frame_bytes 1) with 128; fold F; lia) Hi).
  - unfold shadow_addr, SHADOW_OFF in *. lia. }
assert (HLED5 : LEDGER ly S2 Hp W (ms_mem ms) Lam peak cnt SIZE_MAXZ ran most 0).
{ apply (ce_ledger_move ly S2 Hp W mem2 ly S2 W (ms_mem ms) Lam peak cnt SIZE_MAXZ ran most 0 HI_head8 HLED2 eq_refl).
  - intros a Ha. exact (KIMG a (S1ImgB.pst_in_img_B a Ha)).
  - intros p n i Hpn Hi. destruct (alx_blocks _ _ _ LAWS ly S2 Hp W mem2 md2 p n HAR2 Hpn) as (_ & H4096 & Hpce & Happ & _).
    apply K5; [lia|]. intros [Hs | [Hf | Hs]]; [lia | |].
    + pose proof (sep_block_frame_x _ _ _ LAWS ly S2 Hp W mem2 md2 _ _ 1 pos HAR2 Hpn Hin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd. fold F in Hd. lia.
    + unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. lia. }
assert (HROD5 : arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) (ms_mem ms))).
{ unfold arodata_okP. intros a Hro Hno Her. rewrite (KIMG a (ce_ro_img a Hro)). exact (HROD2 a Hro Hno Her). }
assert (HSV5 : crs_saved_B (mkCrsC_B ly S Hp W regs mem md ch data tb took doc t D Lam peak cnt ran most rp_x rp_os rp_i
  rp_H0 rp_hist fpos dp0 ws0) W (ms_mem ms)).
{ apply (ce_saved_keep _ W W mem2 (ms_mem ms) HSV). cbn [cb_regs]. intros a Ha. apply K5; [lia|].
  unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. lia. }
assert (HFL5 : rdword (aview SEGS (w_H W) (ms_mem ms)) (F + 120) = Some (flag_addr ly 1 pos)).
{ rewrite <- HFL. apply ce_rdword_keep. intros j Hj. apply K5; [lia|].
  unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. lia. }
(* the frame's sixteen shadow bytes after the pokes: f1 x4, 00 x7, f3 x5 *)
assert (VSH : forall i, 0 <= i < 16 -> exists v, aview SEGS (w_H W) (ms_mem ms) (shadow_addr F + i) = Some v /\
  (4 <= i <= 10 -> v = 0)).
{ intros i Hi.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/
    i = 12 \/ i = 13 \/ i = 14 \/ i = 15) as Hc by lia.
  repeat (destruct Hc as [-> | Hc]; [ce_shb E HR2 U64 |]); subst i; ce_shb E HR2 U64. }
(* the chain the callee unwinds: s0 = sp0, its saved ra and s0 below it, the caller's chain above it *)
assert (HUP5 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite (K5 a ltac:(lia) ltac:(unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *; lia)).
  exact (HUP a Ha). }
pose proof HSV5 as HSV5'. unfold crs_saved_B, CRS_SAVED_B in HSV5'. cbn [cb_regs] in HSV5'.
pose proof (Forall_inv HSV5') as Sra. pose proof (Forall_inv (Forall_inv_tail HSV5')) as Ss0.
cbn [fst snd] in Sra, Ss0.
assert (Hch1 : exists ch1, achain ly (aview SEGS (w_H W) (ms_mem ms)) sp2 (spZ regs) ch1).
{ destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
  - exists ((spZ regs, raZ regs, s0Z regs) :: ch).
    apply (achain_push ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) (raZ regs) ch sp2 Hch ltac:(lia)).
    + exact HUP5.
    + replace (spZ regs - 8) with (spZ regs - 128 + 120) by lia. exact Sra.
    + replace (spZ regs - 16) with (spZ regs - 128 + 112) by lia. exact Ss0.
    + exact Hra4.
    + lia.
    + rewrite Z.mod_divide in Hal16 |- * by lia. destruct Hal16 as [q Hq]. exists (2 * q). lia.
    + exact Hlt.
    + lia.
  - exists []. left. split; [right; left; lia | reflexivity]. }
destruct Hch1 as (ch1 & Hch1).
pose proof (@pa_B_ok _ _ PA) as HBASE.
assert (EQ1 : bv_unsigned (getr (ms_regs ms) 1) = BASE + 2876) by (rewrite Q1; apply unsigned_lit_small; lia).
assert (Hsp5 : spZ (ms_regs ms) = spZ regs + (sp2 - spZ regs)).
{ unfold spZ at 1. rewrite (Y5 2%bv) by (cbv; tauto). rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hs05 : s0Z (ms_regs ms) = spZ regs).
{ unfold s0Z. rewrite (Y5 8%bv) by (cbv; tauto). rewrite R8. reflexivity. }
(* ---- the fuzz_alloc_live call (YCbqGcall.aj_call_x_sp with the kit's tfuzz_alloc_live_specX) ---- *)
eapply SRr_bind.
{ eapply (aj_call_x_sp (SK := SK) SEGS B PST ARx LAWS Hsegs W _ _ ms STK (spZ regs) [] ly S Hp W mem md [(1, pos)]
    ly S2 Hp _ k (STK_fuzz_alloc_live (PI := prh_img_B)) [] (sp2 - spZ regs) (getr (ms_regs ms) 1) ch1
    _ HS eq_refl HJ Hsp5).
  - rewrite Z.mod_divide in Hal16, Hs32 by lia. destruct Hal16 as [q1 Hq1]. destruct Hs32 as [q3 Hq3].
    apply Z.mod_divide; [lia|]. exists (2 * q3 - q1). lia.
  - lia.
  - rewrite ESTK1. lia.
  - rewrite ESTK1, ESTK. lia.
  - rewrite (Y5 3%bv) by (cbv; tauto). rewrite R3. exact Hgp.
  - rewrite (Y5 4%bv) by (cbv; tauto). rewrite R4. exact Htp.
  - reflexivity.
  - rewrite Q1. apply bv_eq. vm_compute. reflexivity.
  - rewrite EQ1. vm_compute. discriminate.
  - rewrite Hs05. replace (spZ regs + (sp2 - spZ regs)) with sp2 by lia. exact Hch1.
  - intros HPRE1. cbn [ss_pc setpc].
    refine (HT_fuzz_alloc_live ly S2 Hp W (ms_regs ms) (ms_mem ms) _ ch1 Lam peak cnt SIZE_MAXZ ran most 0
      (conj HPRE1 (conj HROD5 (conj _ (conj _ HFRM0)))) HLED5).
    + rewrite Hsp5. lia.
    + unfold raZ. rewrite EQ1. assert (BASE + 2876 < 2 ^ 31) by (vm_compute; reflexivity). lia.
  - intros a (r & [] & _). }
cbv beta. intros W3 c3 _ (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k1 & -> & HJ3 & HJ1 & HP3 & HQ3).
destruct HQ3 as ((Hroom3 & Ha03 & EHp3 & ES3 & Eab3 & HLED3) & Hmn3).
subst Hp3 S3.
rewrite Q1. change (BASE + 2876) with (BASE + CRS_PC_H1_B).
(* ---- H1: the continuation, at the frame position pos ---- *)
destruct HK as [KP1 KP2 KP3 KP4 KP5].
pose proof HJ3 as (HAR3 & HLY3 & HSE3 & HWLE3 & HIO3 & HFR3 & HNEV3 & HK3 & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9).
pose proof HJ1 as (HAR1' & HLY1 & _ & _ & _ & HFR1 & _ & _ & L1 & L2 & L3 & L4 & _).
destruct (crs_ly_keep_B B ARx LAWS ly S Hp W mem md ly3 1 pos HAR HLY3) as (EF3 & EFL3).
destruct (alx_frames _ _ _ LAWS ly S2 Hp W mem2 md2 1 pos HAR2 Hin) as (HF32 & _ & _ & _).
change (fs_frame_bytes 1) with 128 in HF32. fold F in HF32.
assert (Eabs : ablocks B ly S2 = ablocks B ly S) by (rewrite ES2; reflexivity).
assert (Eab33 : ablocks B ly3 S2 = ablocks B ly S) by (rewrite Eab3; exact Eabs).
assert (Hin3 : In (1, pos) (frames S2)) by exact Hin.
assert (HnoFP : forall a, ~ inFP [] a) by (intros a (r & [] & _)).
assert (HspFP : forall a, fp_spares [] a) by (intros a Hf; destruct Hf as (r & [] & _)).
(* the frame's sixteen shadow bytes at H1 *)
assert (SK3 : forall i, 0 <= i < 16 -> aview SEGS (w_H W3) mem3 (shadow_addr F + i) = aview SEGS (w_H W) (ms_mem ms) (shadow_addr F + i)).
{ intros i Hi. apply (L4 1 pos _ Hin3); [right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1 / 8) with 16; fold F; lia |].
  apply HnoFP. }
(* the bytes the entry state's facts read, kept by the journal from the entry *)
assert (KBLK : forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n ->
  aview SEGS (w_H W3) mem3 (p + i) = aview SEGS (w_H W) mem (p + i)).
{ intros p n i Hpn Hi. apply (J2 p n i Hpn); [rewrite Eab33; exact Hpn | exact Hi | apply HnoFP]. }
assert (KLAM : forall b m x, In (b, m) Lam -> b <= x < b + m ->
  aview SEGS (w_H W3) mem3 x = aview SEGS (w_H W) mem x /\ (exists p n, In (p, n) (ablocks B ly S) /\ p <= x < p + req_size n)).
{ intros b m x Hbm Hx. pose proof HLED as (_ & _ & HFb & _). rewrite Forall_forall in HFb.
  destruct (HFb (b, m) Hbm) as (Hm0 & Hab & _). cbn [fst snd] in Hm0, Hab.
  assert (Hrq : req_size (m + cf_head) = m + cf_head) by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
  split.
  - replace x with ((b - cf_head) + (x - (b - cf_head))) by lia. apply (KBLK _ _ _ Hab). rewrite Hrq. lia.
  - exists (b - cf_head), (m + cf_head). split; [exact Hab | rewrite Hrq; lia]. }
assert (KIMG3 : forall a, in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Hro Hno Her. apply (J3 a (ce_ro_img a Hro) Hno Her); [| apply HspFP].
  intros Hp'. exact (S1ImgB.pst_not_ro_B a Hp' Hro). }
assert (KDAT : forall a, data <= a < data + Z.of_nat (length tb) -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct HHOME as [[(b & m & Hbm & Hb1 & Hb2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hbm & _ & Hb1 & Hb2)].
  - exact (proj1 (KLAM b m a Hbm ltac:(lia))).
  - destruct (Hro a Ha) as (H1 & H2 & H3). exact (KIMG3 a H1 H2 H3).
  - destruct (Hro a Ha) as (H1 & H2 & H3 & _). exact (KIMG3 a H1 H2 H3).
  - replace a with (b + (a - b)) by lia. apply (KBLK b m (a - b) Hbm).
    unfold req_size. destruct (Z.eqb_spec m 0); lia. }
(* H1's cut concludes at the re-hiding relation: E's plain stretch hands it over here *)
apply SRr_ret.
refine (HH1 pos fx ly3 S2 Hp W3 regs3 mem3 md3 (k + k1) sp2 eq_refl _ _ _ _ _).
(* crs_base_B *)
- unfold crs_base_B, crs_with_fpos_B. cbn [cb_ly cb_S cb_Hp cb_W cb_regs cb_mem cb_md cb_fpos].
  split; [exact HPRE0|]. split; [exact HFRM|]. split; [intros r _; reflexivity|].
  split; [unfold crs_J_B; cbn [cb_dp cb_S cb_ly cb_Hp cb_W cb_mem cb_md cb_regs cb_fpos]; rewrite crs_set_depot_id_B;
          exact HJ3|].
  split.
  { unfold crs_frame_B, cF_B. cbn [cb_ly cb_S cb_fpos]. change CRS_CID_B with 1. change (fs_frame_bytes 1) with 128. fold F.
    split; [rewrite HFR3; reflexivity|]. split.
    - rewrite EFL3. rewrite <- HFL5. replace (F + 128 - 8) with (F + 120) by lia. apply ce_rdword_keep. intros j Hj.
      apply (L4 1 pos _ Hin3); [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; fold F; lia |].
      apply HnoFP.
    - intros a Ha. destruct (alx_frames _ _ _ LAWS ly3 S2 Hp W3 mem3 md3 1 pos HAR3 Hin3) as (_ & _ & Fp3 & _).
      change (fs_frame_bytes 1) with 128 in Fp3. rewrite EF3 in Fp3. fold F in Fp3. exact (proj1 (Fp3 a Ha)). }
  split.
  { apply (ce_saved_keep _ W W3 (ms_mem ms) mem3 HSV5). cbn [cb_regs]. intros a Ha.
    apply L1; [lia|]. rewrite ESTK1. lia. }
  split.
  { unfold crs_slot_B, cOut_B, cF_B. cbn [cb_ly cb_fpos]. change CRS_CID_B with 1. unfold CRS_OFF_DOC_B. fold F. split.
    - intros x Hx. assert (Ei : SHADOW_OFF + x / 8 = shadow_addr F + (x - F) / 8) by (unfold shadow_addr; lia).
      destruct (VSH ((x - F) / 8) ltac:(lia)) as (v & Hv & Hv0).
      exists 0. unfold shadow_of_addr. rewrite Ei, SK3 by lia. rewrite Hv, (Hv0 ltac:(lia)).
      split; [reflexivity | left; reflexivity].
    - intros s Hs. assert (Ei : s = shadow_addr F + (s - shadow_addr F)) by lia.
      assert (Hi : 0 <= s - shadow_addr F < 16) by (unfold shadow_addr, SHADOW_OFF in *; lia).
      rewrite Ei, SK3 by exact Hi. destruct (VSH (s - shadow_addr F) Hi) as (v & Hv & _). rewrite Hv. discriminate. }
  split.
  { unfold arodata_okP. intros a Hro Hno Her.
    rewrite (L3 a (ce_ro_img a Hro) Hno Her ltac:(intros Hp'; exact (S1ImgB.pst_not_ro_B a Hp' Hro)) (HspFP a)).
    exact (HROD5 a Hro Hno Her). }
  split; [exact (Hmn3 HMN5)|].
  split; [rewrite (ce_ap _ _ 3%bv HP3) by ce_cs; rewrite (Y5 3%bv) by (cbv; tauto); exact R3|].
  split; [rewrite (ce_ap _ _ 4%bv HP3) by ce_cs; rewrite (Y5 4%bv) by (cbv; tauto); exact R4|].
  assert (EFR : CRS_FRAME_B = 144) by (vm_compute; reflexivity). rewrite EFR.
  split; [lia|]. split; [lia|]. split; [lia|].
  (* no budget spent yet, the journal's entry depot the entry's own *)
  unfold crs_dpok_B. cbn [cb_ws cb_dp cb_S]. split; [unfold YCbqGwild.wbudget, YCbqGwild.wfresh; cbn; lia|].
  rewrite app_nil_r. apply incl_refl.
(* crs_regsat_B *)
- unfold crs_regsat_B, crs_rbase_B, crs_rsh_B, crs_rargs_B, cF_B, cSize_B, crs_with_fpos_B.
  cbn [app cb_regs cb_ly cb_fpos cb_doc cb_tb cb_data cb_took cb_Lam]. change CRS_CID_B with 1. fold F.
  repeat constructor; cbn [fst snd].
  + rewrite (ce_ap _ _ 2%bv HP3) by ce_cs. rewrite (Y5 2%bv) by (cbv; tauto). exact R2.
  + rewrite (ce_ap _ _ 8%bv HP3) by ce_cs. rewrite (Y5 8%bv) by (cbv; tauto). rewrite R8.
    unfold w64, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  + rewrite (ce_ap _ _ 9%bv HP3) by ce_cs. rewrite (Y5 9%bv) by (cbv; tauto). exact R9.
  + rewrite (ce_ap _ _ 18%bv HP3) by ce_cs. rewrite Q18. unfold E. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. exact R10.
  + rewrite (ce_ap _ _ 26%bv HP3) by ce_cs. rewrite Q26. unfold E. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. exact R10.
  + rewrite (ce_ap _ _ 27%bv HP3) by ce_cs. rewrite (Y5 27%bv) by (cbv; tauto). exact R27.
  + rewrite (ce_ap _ _ 25%bv HP3) by ce_cs. rewrite Q25. unfold E. exact (te_more_lt regs rg _ 0 ltac:(lia)).
  + rewrite (ce_ap _ _ 19%bv HP3) by ce_cs. rewrite (Y5 19%bv) by (cbv; tauto). rewrite R19. exact H13.
  + rewrite (ce_ap _ _ 20%bv HP3) by ce_cs. rewrite (Y5 20%bv) by (cbv; tauto). rewrite R20. exact H11.
  + rewrite (ce_ap _ _ 21%bv HP3) by ce_cs. rewrite (Y5 21%bv) by (cbv; tauto). rewrite R21. exact H10.
  + rewrite (ce_ap _ _ 23%bv HP3) by ce_cs. rewrite (Y5 23%bv) by (cbv; tauto). rewrite R23. exact H12.
  + exact Ha03.
(* crs_live_B *)
- unfold crs_live_B, crs_core_B, crs_perm_B, crs_with_fpos_B. cbn [cb_ly cb_S cb_Lam cb_peak cb_cnt cb_ran].
  split; [split; [exact HLED3|]; split; [lia|]; split; [reflexivity|]; split; [lia|]; split; [lia|]; split|].
  + apply Hroom3. rewrite ES2. apply RL_set_fs. exact HROOM.
  + rewrite ES2. exact (ce_pos_E (mkCrsC_B ly S Hp W regs mem md ch data tb took doc t D Lam peak cnt ran most rp_x rp_os
      rp_i rp_H0 rp_hist pos dp0 ws0) f ran HRP).
  + split; [apply Permutation_refl|]. rewrite Eab33. apply Permutation_refl.
(* crs_dat_B *)
- unfold crs_dat_B, cSize_B, crs_with_fpos_B. cbn [cb_tb cb_data].
  assert (Hhome3 : PRH_FnReader.prhReader_home (L := B_prog_listing) (PA := PA) B ly3 S2 Hp Lam data (Z.of_nat (length tb))).
  { apply (KP2 ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0 ly3 S2 Hp W3 mem3 Lam peak cnt SIZE_MAXZ ran most 0 data
      (Z.of_nat (length tb)) HLED HLED3 (Permutation_refl _)); [rewrite Eab33; apply Permutation_refl | exact HHOME]. }
  split; [|split; [exact Hhome3|]].
  + destruct HSRC as (Hby & _). unfold bytes_at in *. apply (ce_garr_av (w_H W) (w_H W3) mem mem3 data tb); [|exact Hby].
    intros j Hj. apply KDAT. lia.
  + destruct HSRC as (_ & H4096 & Hceil' & _).
    destruct (Z.eq_dec (Z.of_nat (length tb)) 0) as [E0 | E0].
    * split; [intros x Hx; lia | intros Hlt; lia].
    * destruct (KP1 ly3 S2 Hp W3 mem3 md3 Lam peak cnt SIZE_MAXZ ran most 0 data (Z.of_nat (length tb)) HAR3 HLED3 Hhome3
        ltac:(lia) ltac:(lia) ltac:(lia)) as [Ha Hh].
      split; [exact Ha | intros _; exact Hh].
(* crs_tree_B *)
- unfold crs_tree_B, crs_with_fpos_B. cbn [cb_doc cb_t cb_D]. intros Hd.
  destruct HDOC as [Hd0' | (Hrd & (Hnode & HDL & Hvis & Hobj) & _)]; [contradiction|].
  unfold ck_tree_ok. split; [|split; [exact HDL | split]].
  + apply (PRH_Reader.pj_nodeR_frame SEGS t (mrestrict (w_H W) mem) (mrestrict (w_H W3) mem3) (prh_lin Lam) doc D Hnode).
    intros x Hx. destruct Hx as [Hx | (bk & Hbk & Hx)].
    * pose proof Hobj as (_ & (cid & pos' & Hin' & Hflo & Hfhi) & _).
      assert (Hin'' : In (cid, pos') (frames S2)) by (rewrite HFR3; right; exact Hin').
      assert (Kx : aview SEGS (w_H W3) mem3 x = aview SEGS (w_H W) mem x).
      { apply (J4 cid pos' x Hin'); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | apply HnoFP]. }
      split; [exact (mbyte_of_aview SEGS _ _ _ _ x Kx)|].
      intros _. apply (apresent_writable SEGS).
      destruct (crs_ly_keep_B B ARx LAWS ly S Hp W mem md ly3 cid pos' HAR HLY3) as (EF' & _).
      destruct (alx_frames _ _ _ LAWS ly3 S2 Hp W3 mem3 md3 cid pos' HAR3 Hin'') as (_ & _ & Fp' & _).
      rewrite EF' in Fp'. exact (proj1 (Fp' x ltac:(lia))).
    * destruct bk as [b m]. unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
      destruct (KLAM b m x (HDL _ Hbk) Hx) as (Kx & (p & n & Hpn & Hpx)).
      split; [exact (mbyte_of_aview SEGS _ _ _ _ x Kx)|].
      intros _. apply (apresent_writable SEGS).
      assert (Hpn3 : In (p, n) (ablocks B ly3 S2)) by (rewrite Eab33; exact Hpn).
      destruct (alx_blocks _ _ _ LAWS ly3 S2 Hp W3 mem3 md3 p n HAR3 Hpn3) as (_ & _ & _ & _ & Hpr & _).
      exact (proj1 (Hpr x Hpx)).
  + exact (KP3 ly3 S2 Hp W3 mem3 md3 Lam peak cnt SIZE_MAXZ ran most 0 D HAR3 HLED3 HDL).
  + exact (KP5 STK (spZ regs) ly S Hp W mem md [(1, pos)] ly3 S2 Hp W3 mem3 md3 (k + k1) doc HAR HJ3 Hobj).
Qed.

(* ======================================================================================================== *)
(* ---- THE CLOSING LEMMA ---- *)
Theorem crs_seg_E_B :
  (* HX: the engine rules' Section hypotheses that B / ARx / LAWS do not give (header) *)
  YGcallMxmn.astack_malloc_realizes_xm SEGS B ARx 1 ->
  ARx_owned_low_law SEGS B ARx ->
  PALib (L := B_prog_listing) (PI := PA) B ->
  @pa_lo _ B_prog_listing PA <= as_uar_cell B /\ as_uar_cell B + 4 <= @pa_hi _ B_prog_listing PA ->
  SIGMA AS___asan_stack_malloc_1 = pc_stack_malloc (as_code B) 1 ->
  (forall a, Exists (in_zr a) PST -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  (* HI: the instance fact *)
  8 <= cf_head ->
  (* HT: the callee's text *)
  PRH_FnAlloc.tfuzz_alloc_live_specX (fx := fx) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK ->
  (* HK: the kit's transport record *)
  CrsKeep_B (SK := SK) B ARx ->
  forall CTX0 (C : crsC_B),
  (forall p, crs_from_H1_B (fx := fx) (rc := rc) (SK := SK) B ARx CTX0 (crs_with_fpos_B C p)) ->
  crs_from_E_B (fx := fx) (rc := rc) (SK := SK) B ARx CTX0 C.
Proof.
intros HX_asmr HX_ownlow HX_pal HX_pal_uar_img HX_pal_sm1 HX_pal_pst_static HI_head8 HT_fuzz_alloc_live HK
  CTX0 C HH1.
destruct C as [ly S Hp W regs mem md ch data tb took doc t D Lam peak cnt ran most rp_x rp_os rp_i rp_H0 rp_hist fpos dp0 ws0].
unfold crs_from_E_B. intros HPRE. pose proof HPRE as HPRE0.
unfold crs_pre_B, cSize_B in HPRE.
cbn [cb_ly cb_S cb_Hp cb_W cb_regs cb_mem cb_md cb_ch cb_data cb_tb cb_took cb_doc cb_t cb_D cb_Lam cb_peak cb_cnt cb_ran cb_most
  cb_rp_x cb_rp_os cb_rp_i cb_rp_H0 cb_rp_hist cb_fpos] in HPRE |- *.
destruct HPRE as ((HAF & HROD & HSHI & HRAC & HFRM0) & HMN & HCL & HCTX & H10 & H11 & H12 & H13 & Hsz & Hd0 & Hd62 & HSRC & HHOME &
  Htook & HDOC & HLED & Hcnt & HRUN & Hran & HRQ & HRQW & HLIVE & HRQC & HFR & HROOM & HRP & HFRM & HWR0 & HSEC0 & H240 & HCONS0).
(* E's cuts are before the walk's first free: E runs plain SRr, lifted once into the re-hiding relation of its
   conclusion (YGcfRhLift.ra_rh_of_SRr); ce_stage_B hands the SRr' goal to H1's cut *)
apply YGcfRhLift.ra_rh_of_SRr.
pose proof HAF as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
destruct ce_stk_vals as (ESTK & ESTK1).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof ce_pa_hi as Hhi.
assert (Hpst : forall a, Exists (in_zr a) PST -> 0 <= a < 2 ^ 31).
{ intros a Ha. pose proof (Hsegs a (S1ImgB.pst_in_img_B a Ha)) as R. lia. }
assert (Hblk : forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n -> 4096 <= p + i < YM05.alloc_ceiling).
{ intros p n i Hin Hi. destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & H4096 & Hpce & _). lia. }
destruct (ce_A1_entry B ARx LAWS STK ly S Hp W regs mem md ch HX_pal ltac:(lia) HAF) as [HS SHOK].
pose proof HS as HSa1.
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx STK [] ly S Hp W regs mem md ch HAF) as HJ.
remember (TE regs regs [w64 (as_uar_cell B)]) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply te_env).
assert (E64a : ew E 64 = w64 (as_uar_cell B)) by (subst E; exact (te_more_lt regs regs [w64 (as_uar_cell B)] 0 ltac:(lia))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (te_entry regs regs _ 2%bv 2) by reflexivity; reflexivity).
assert (EE : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros r n Hn; subst E; apply te_entry; exact Hn).
pose (RUNTO := @paj_run_to_x fx rc SK B_prog_listing PL PA B PST ARx _ LAWS).
pose (RUN := @paj_run_x fx rc SK B_prog_listing PL PA B PST ARx _ LAWS).
unfold cfg_at. rewrite <- crs_pc_entry_B.
(* ---- A1: entry to the flag's load ---- *)
paj_run_to_tok_x RUNTO HS HJ SHOK (0, 0) (CRS_PC_E_B + CE_A2_OFF).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS.
pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR1 & _).
prreg HS (12%bv : bv 5) R12. prreg HS (11%bv : bv 5) R11. prreg HS (10%bv : bv 5) R10.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (2%bv : bv 5) R2. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (23%bv : bv 5) R23.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
pose proof (ts_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
assert (HMN1 : MN.memnorm SEGS (ms_mem ms)).
{ eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H W) E (abs_ss VAL ce_ss_A1)); [| exact HSa1 |]; [exact HMN | exact HF]. }
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ apply (ts_keep W E (ss_mem ce_ss_A1) mem (ms_mem ms) _ HFr).
  intros a (r & Hr & Ha). cbv [ce_ss_A1 ss_mem ce_A1_regions got_regionP In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ts_bv_some in Ha|]);
  [ rewrite Usp in Ha; lia | lia | lia | destruct Hr ]. }
set (regs1 := ms_regs ms) in *. set (mem1 := ms_mem ms) in *.
assert (EP2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (H144 : 144 <= spZ regs) by lia.
assert (X2 : getr regs1 2 = w64 (ce_sp2 (spZ regs))) by (rewrite R2, EP2; apply ce_sp2_word; unfold spZ in H144; lia).
assert (X9 : getr regs1 9 = w64 (ce_sp2 (spZ regs))).
{ rewrite R9, EP2, (ce_sp2_word (getr regs 2)) by (unfold spZ in H144; lia). apply ts_add0_word. }
assert (X8 : getr regs1 8 = getr regs 2) by (rewrite R8; exact EP2).
assert (X10 : getr regs1 10 = getr regs 10) by (rewrite R10; apply EE; reflexivity).
assert (X19 : getr regs1 19 = getr regs 13) by (rewrite R19; apply EE; reflexivity).
assert (X20 : getr regs1 20 = getr regs 11) by (rewrite R20; apply EE; reflexivity).
assert (X23 : getr regs1 23 = getr regs 12) by (rewrite R23; apply EE; reflexivity).
assert (X3 : getr regs1 3 = getr regs 3) by (rewrite R3; apply EE; reflexivity).
assert (X4 : getr regs1 4 = getr regs 4) by (rewrite R4; apply EE; reflexivity).
assert (X11 : getr regs1 11 = w64 (VAL (A_OBJ 12)))
  by (rewrite R11, HEdef, ce_te_img by (unfold A_TEXT, A_LIM; lia); reflexivity).
assert (X12 : getr regs1 12 = w64 (as_uar_cell B)) by (rewrite R12; exact E64a).
pose (C0 := mkCrsC_B ly S Hp W regs mem md ch data tb took doc t D Lam peak cnt ran most rp_x rp_os rp_i rp_H0 rp_hist
  fpos dp0 ws0).
assert (HSV1 : crs_saved_B C0 W mem1).
{ unfold crs_saved_B, CRS_SAVED_B, C0. cbn [cb_regs]. repeat constructor; cbn [fst snd];
  lazymatch goal with |- rdword _ (spZ regs - 128 + ?off) = Some (bv_unsigned (getr regs ?r)) =>
    let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    let od := eval vm_compute in (off - 128) in
    pose proof (ts_field E _ 2 (spZ regs) _ _ _ _ _ od 8 (SOff n 0) HR0 Usp
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V; change (N.to_nat 8) with 8%nat in V;
    rewrite ts_U_atom_mod, (EE r n) in V by reflexivity;
    replace (spZ regs - 128 + off) with (spZ regs + od) by lia;
    apply ce_rdword_of_val_mem; [exact V|];
    pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb; exact Hb
  end. }
clear HF HG HFr HR0 R2 R3 R4 R8 R9 R10 R11 R12 R19 R20 R23.
(* ---- A2: the flag's load ---- *)
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR1) as (_ & Kuar1 & _ & _).
destruct (ce_A2_entry B regs regs1 mem1 W HX_pal_uar_img X12 Kuar1) as [HS2 SHOK2].
clear HS SHOK.
change (BASE + 2680) with (BASE + (CRS_PC_E_B + CE_A2_OFF)).
assert (HEI2 : img_env VAL A_LIM (TE regs regs1 [])) by apply te_env.
paj_run_to_tok_x RUNTO HS2 HJ SHOK2 (0, 0) (CRS_PC_E_B + CE_A3_OFF).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS2.
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR2 & _).
prreg HS2 (12%bv : bv 5) Q12.
assert (Y : forall (r : bv 5), In r [2; 3; 4; 8; 9; 10; 11; 19; 20; 23]%bv -> getr (ms_regs ms0) r = getr regs1 r).
{ intros r Hr. cbv [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [ce_keep HS2 |]). destruct Hr. }
assert (K2 : forall x, ms_mem ms0 x = mem1 x).
{ intros x. apply HF. intros (r & Hr & Ha). cbv [ce_ss_A2 ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. lia. }
clear HF HG HFr.
set (regs2 := ms_regs ms0) in *. set (mem2 := ms_mem ms0) in *.
(* ---- A3: the shadow base's load, the flag test (not taken: a2 = 1), `li a0, 128`, to the frame call ---- *)
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR2) as (Kcell2 & _ & _ & _).
rewrite (pal_cell (PI := PA) B HX_pal) in Kcell2.
destruct (ce_A3_entry regs regs2 mem2 W ltac:(rewrite (Y 11%bv) by (cbv; tauto); exact X11) Q12 Kcell2) as [HS3 SHOK3].
clear HS2 SHOK2.
change (BASE + 2684) with (BASE + (CRS_PC_E_B + CE_A3_OFF)).
assert (HEI3 : img_env VAL A_LIM (TE regs regs2 [w64 SHADOW_OFF])) by apply te_env.
paj_run_tok_x RUN HS3 HJ SHOK3 (0, 0).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS3.
pose proof HJ as (HAR3 & HLY3 & _ & _ & _ & HFR3 & _ & _ & _ & _ & _ & _ & _ & HPR3 & _).
assert (Y3 : forall (r : bv 5), In r [2; 3; 4; 8; 9; 19; 20; 23]%bv -> getr (ms_regs ms1) r = getr regs2 r).
{ intros r Hr. cbv [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [ce_keep HS3 |]). destruct Hr. }
assert (Z21 : getr (ms_regs ms1) 21 = getr regs2 10) by ce_keep HS3.
prreg HS3 (27%bv : bv 5) Z27. prreg HS3 (1%bv : bv 5) Z1.
assert (K3 : forall x, ms_mem ms1 x = mem2 x).
{ intros x. apply HF. intros (r & Hr & Ha). cbv [ce_ss_A3 ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. lia. }
clear HF HG HFr.
(* ---- the __asan_stack_malloc_1 call (YGcallMxmn.aj_stack_malloc_at_xm, class 1) ---- *)
rewrite HX_pal_sm1.
destruct (ce_sp2_range (spZ regs) Hal16 ltac:(lia)) as (Hs0 & Hs1 & Hs32).
assert (R2' : getr (ms_regs ms1) 2 = w64 (ce_sp2 (spZ regs)))
  by (rewrite (Y3 2%bv) by (cbv; tauto); rewrite (Y 2%bv) by (cbv; tauto); exact X2).
assert (Hsp1 : spZ (ms_regs ms1) = spZ regs + (ce_sp2 (spZ regs) - spZ regs)).
{ unfold spZ at 1. rewrite R2'. unfold w64. rewrite unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ eapply (YGcallMxmn.aj_stack_malloc_at_xm (SK := SK) SEGS B PST ARx LAWS Hsegs (pal_env (PI := PA) B HX_pal) HX_ownlow
    (YGcallScf.stack_malloc_x_any SEGS ARx) 1 HX_asmr ltac:(lia)
    W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ce_sp2 (spZ regs) - spZ regs) (getr (ms_regs ms1) 1) HJ Hsp1).
  - rewrite Z.mod_divide in Hal16, Hs32 by lia. destruct Hal16 as [q1 Hq1]. destruct Hs32 as [q3 Hq3].
    apply Z.mod_divide; [lia|]. exists (2 * q3 - q1). lia.
  - lia.
  - unfold ESTACK. lia.
  - rewrite (Y3 3%bv) by (cbv; tauto). rewrite (Y 3%bv) by (cbv; tauto). rewrite X3. exact Hgp.
  - rewrite (Y3 4%bv) by (cbv; tauto). rewrite (Y 4%bv) by (cbv; tauto). rewrite X4. exact Htp.
  - reflexivity.
  - rewrite Z1. apply bv_eq. vm_compute. reflexivity.
  - rewrite HFR3. exact (crs_cap_pre_B (fx := fx) B ARx CTX0 C0 HPRE0). }
intros W2 c2 _ (-> & S2 & rgB & memB & mdB & pos & -> & HJ2 & HprB & H10B & EabB & HfrsB & HfreshB & HnevB & HbbB & HzB &
  HflB & HfpB & HkB & HJ1B & (fB & ES2) & HmnB).
unfold acall_kept_x, acall_kept in HkB. destruct HkB as (KB1 & KB2 & KB3 & KB4 & KB5 & KB6).
rewrite Z1. change (BASE + 2704) with (BASE + (CRS_PC_E_B + CE_B_OFF)).
(* the memory at the frame call is the memory after A1 *)
assert (K13 : forall a, aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem1 a).
{ intros a. rewrite (ce_aview_ext _ _ _ a K3). exact (ce_aview_ext _ _ _ a K2). }
(* ---- segment B onwards ---- *)
apply (ce_stage_B HX_pal_pst_static HI_head8 HT_fuzz_alloc_live HK CTX0 C0 HH1 HPRE0 pos S2 memB mdB rgB 0 fB).
all: unfold C0; cbn [cb_ly cb_S cb_Hp cb_W cb_regs cb_mem cb_md cb_Lam cb_peak cb_cnt cb_ran].
- exact HJ2.
- exact ES2.
- change (fs_frame_bytes 1) with 128 in HflB. replace (frame_addr ly 1 pos + 120) with (frame_addr ly 1 pos + 128 - 8) by lia.
  exact HflB.
- apply (ce_saved_keep C0 W W mem1 memB HSV1). intros a Ha. unfold C0 in Ha. cbn [cb_regs] in Ha.
  rewrite (KB1 a ltac:(lia) ltac:(lia)). exact (K13 a).
- intros a Ha. rewrite (KB1 a ltac:(lia) ltac:(lia)), K13. exact (K1 a ltac:(lia) ltac:(lia)).
- apply (ce_ledger_move ly S Hp W mem ly S2 W memB Lam peak cnt SIZE_MAXZ ran most 0 HI_head8 HLED EabB).
  + intros a Ha. destruct (HX_pal_pst_static a Ha) as [Hno Her]. pose proof (Hpst a Ha) as Hr.
    rewrite (KB3 a (S1ImgB.pst_in_img_B a Ha) Hno Her), K13. exact (K1 a ltac:(lia) ltac:(lia)).
  + intros p n i Hin Hi. pose proof (Hblk p n i Hin Hi) as Hr.
    rewrite (KB2 p n i Hin Hi ltac:(intros [])), K13. exact (K1 (p + i) ltac:(lia) ltac:(lia)).
- unfold arodata_okP. intros a Hro Hno Her. pose proof (Hsegs a (ce_ro_img a Hro)) as Hr.
  rewrite (KB3 a (ce_ro_img a Hro) Hno Her), K13, (K1 a ltac:(lia) ltac:(lia)). exact (HROD a Hro Hno Her).
- apply HmnB. apply (ce_memnorm_ext mem2); [exact K3|]. apply (ce_memnorm_ext mem1); [exact K2 | exact HMN1].
- rewrite (ce_ap _ _ 2%bv HprB) by ce_cs. exact R2'.
- rewrite (ce_ap _ _ 9%bv HprB) by ce_cs. rewrite (Y3 9%bv) by (cbv; tauto). rewrite (Y 9%bv) by (cbv; tauto). exact X9.
- rewrite (ce_ap _ _ 8%bv HprB) by ce_cs. rewrite (Y3 8%bv) by (cbv; tauto). rewrite (Y 8%bv) by (cbv; tauto). exact X8.
- rewrite (ce_ap _ _ 3%bv HprB) by ce_cs. rewrite (Y3 3%bv) by (cbv; tauto). rewrite (Y 3%bv) by (cbv; tauto). exact X3.
- rewrite (ce_ap _ _ 4%bv HprB) by ce_cs. rewrite (Y3 4%bv) by (cbv; tauto). rewrite (Y 4%bv) by (cbv; tauto). exact X4.
- rewrite (ce_ap _ _ 19%bv HprB) by ce_cs. rewrite (Y3 19%bv) by (cbv; tauto). rewrite (Y 19%bv) by (cbv; tauto). exact X19.
- rewrite (ce_ap _ _ 20%bv HprB) by ce_cs. rewrite (Y3 20%bv) by (cbv; tauto). rewrite (Y 20%bv) by (cbv; tauto). exact X20.
- rewrite (ce_ap _ _ 21%bv HprB) by ce_cs. rewrite Z21. rewrite (Y 10%bv) by (cbv; tauto). exact X10.
- rewrite (ce_ap _ _ 23%bv HprB) by ce_cs. rewrite (Y3 23%bv) by (cbv; tauto). rewrite (Y 23%bv) by (cbv; tauto). exact X23.
- rewrite (ce_ap _ _ 27%bv HprB) by ce_cs. rewrite Z27. exact (te_more_lt regs regs2 [w64 SHADOW_OFF] 0 ltac:(lia)).
- exact H10B.
Qed.

End f.
End d.

(* ---- INSTANCE WITNESS of the image premise HI_head8 (unit ruling 16:45Z): at the preset's CfParams instance the
   harness head is 16 bytes (lib/A/CfParamsPreset.v preset_head_wide) ---- *)
Lemma crs_seg_E_B_HI_head8_B' : 8 <= @cf_head CfParams_preset.
Proof. exact preset_head_wide. Qed.
