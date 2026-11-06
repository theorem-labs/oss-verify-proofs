(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (route (B''): the call memory in the call rules): Section allocm takes
   YGcallx's new QMm (the call's conjuncts on the state and the call memory) and QMQ (QMm S mem -> QM S); its eight
   _m rules take `QMm Sc <call memory>` instead of `QM Sc`, and pass QMm / QMQ to YGcallx's rules. *)
(* Modified by Theorem Labs, 2026-10-30 (the world relation R): the free _m rules are proved once over the journal's
   world relation R and the callee's call post APOST (aj_free_x_ct_mR / aj_free_at_x_ct_mR; the old _m names are the
   instances at wle and acall_post_x; aj_free_x_mR / aj_free_at_x_mR likewise); every other call rule here with a
   journal takes it at any R, the old names being their wle instances: aj_intrin_at_xmR, aj_poison_at_x_mR and
   aj_poison_x_mR take R alone; aj_intrin_at_xm_frR, aj_bcmp_at_xmR, aj_strcmp_at_xroR, aj_strlen_at_xroR,
   aj_strcmp_at_xromR, aj_strlen_at_xromR, aj_strlen_at_xmR, aj_stack_malloc_at_xmR, aj_set_shadow_at_xmR,
   aj_unpoison_at_x_mR and aj_unpoison_x_mR take R reflexive and transitive, binders first (the stack-malloc form uses
   both to compose the call's own journal into the caller's); the malloc _m rules aj_malloc_x_mR, aj_malloc_x_ct_mR,
   aj_malloc_at_x_mR and aj_malloc_at_x_ct_mR also take wle inside R (YGcallx's malloc R forms); section 12 states the cf
   free forms under the re-hide (aj_free_x_ct_m_rh / aj_free_at_x_ct_m_rh: SRr' segs RZ_cf, the journal at wle' segs
   RZ_cf). *)
(* Modified by Theorem Labs, 2026-10-31 (field round 3 part 3c: memnorm out of every call text): YGcallx.v's leaves
   malloc_leaf_x / free_leaf_x / free_leaf_xA lost their memnorm keep, the conjunct family 4's keep was read from. So
   the eight _m malloc / free rules of section 10, their R forms (_mR) and section 12's two cf free forms (_m_rh) drop
   the keep (MN.memnorm segs memT -> MN.memnorm segs mem2) from their conclusion: each _m / _mR rule is now its
   YGcallx.v original VERBATIM (the _mR forms are proved by it), under its own name for the walks that apply it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallMxmn.v, with its module paths and module names changed; 487 of its 563 lines of code are new or changed and 2253 lines of the source are left out. *)
(* fuzz_preset, image B' (the #102 pins, asan-ubsan): segment R of the walk of check_reject_clean_starved against
   the kit's text tcheck_reject_clean_starved_specX, row R_B (a Theorem Labs lane's internal file BRIEF-crcs-Bprime-seg.md). Its one
   export is crs_seg_R_B : .. -> crs_from_R_B B ARx CTX0 C (lib/B/Prog/CrsKitBp.v).
   rule 24: proves function check_reject_clean_starved on image B' (reuse search: `proof-index
   check_reject_clean_starved 0x82160`, the internal file index-crcs-Aprime.out, and an internal record of that
   lookup; CONFIRM by checker LookupCheckCrcsAp. At that search origin/ossv/recipes had no lib/A or lib/B, its
   released rows were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released asan Proof.v existed for
   check_reject_clean_starved). DONOR (reuse): the A' segment file
   lib/A/Prog/CrsSeg_R.v blob af4097e508fc (a working branch aee0692b20cc), carried lemma for lemma with the kit's
   `_B` names and B''s instance; every number re-derived at B' (below), none shifted from A'.
   INPUTS.
   - Pin B' asan-ubsan sha256 d663f82d7f488d30 (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1).
   - Listing lib/B/Listing_prog.v blob c97cc46b3e13 + lib/B/PAImg_prog.v blob 15fab93fe702 (a Theorem Labs lane's listings v3);
     entry 0x820e0 = slot 645 (B_entry_check_reject_clean_starved); R = slots 829 .. 892 (B' 0x823c0 .. 0x824bc, the
     `ret`), the same 64 instruction words as A''s R, read off the B' listing at slot 829.
   - Image record lib/B/PRH_ImgB.v (prh_img_B); the kit text tcheck_reject_clean_starved_specX in lib/A/PRH_FnCheck.v blob
     9ecd8eb167c6, lib/A/PRH_Base.v blob fdb45545469b, through the B'
     kit lib/B/Prog/CrsKitBp.v blob 1dd89c0383ac (a working branch a179cedc95a7). R makes no call.
   THE SEGMENT: ONE engine run from R (+736) to the `ret` (+988): `li a0, -8` and `sb a0` over the local's shadow
     bytes 4 .. 10 (s9 = the frame's shadow); the retired magic 0x45e0360e by `sd a0, 0(s10)` (s10 = F); `beqz s2` -
     THE s2 = 0 ARM (the real-stack shadow clear) IS UNREACHABLE: s2 = F and the run's fact on s2's atom is 4096 <= F
     (frames_bounds_x), so the engine decides the branch and never enters it; `li a0, -11` and `sb a0` over all sixteen
     shadow bytes; THE INLINE RELEASE `ld a0, 120(s2); sb zero, 0(a0)` (crs_frame_B) by YGcallSx.aj_flag_store_x; `j`;
     `addi sp, s0, -128`; the thirteen restores from the saved slots (crs_saved_B); `addi sp, sp, 128`; `ret`
     (YC1fP.paj_ret_at). No call, no `__asan_report_*` arm, no UBSan check.
   PREMISES, in the A' order and names (a Theorem Labs lane's rulings, 2026-10-29): HX_asfx, HX_fflx, HX_sfx = YGcallSx.v's ASFX /
   FFLX / SFX (blob 17d7d2cdbcd1 :214-226) verbatim at segs := SEGS (B'); HX_fflp = the flag byte is present
   (Crt102Tail.v's FFLP, blob 2f7b18811820 :384); HI_head8 : 8 <= cf_head (an instance fact; witness HI_head8_B' at the
   end, by CfParamsPreset.preset_head_wide: the CfParams instance is the same for both images). The position step is
   ONE lemma, crsRB_pos_step.
   B' IMAGE FACTS, by computation at PI_prog_B (crsRB_img_seg): pa_lo = 65536, pa_hi = 6295552, and the four segments
   [65536, +135168), [200704, +462848), [663552, +8192), [671744, +5623808) cover [pa_lo, pa_hi) without a gap.
   COPIED / RESTATED (not Required): YGcallMxmn.v's ak_wview_absent_seg / ak_wview_not_ro / in_wrange_dec /
   memnorm_frame_of (a working branch, blob 2ca1815f60a8 :636-701), renamed crsRB_*; S1Ledger.v's
   prh_ledger_kept_aview restated for the E sweep as crsRB_ledger_kept; PRW_WalkEnv.v's TE environment at B' (Required from lib/B/Prog/PRW_WalkEnvB.v).
   Numerals. LENGTH: 120 / 128 (the flag word at F + fs_frame_bytes 1 - 8; the class-1 frame), 16 (its shadow bytes),
   8 (the magic word, the ledger's head word), 104 (the thirteen saves below the entry sp), 56 (struct pj).
   DERIVED: atom indices (the engine's numbering: 2 the entry sp, 32 + r the current r, 64 the flag's address);
   2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 63 / 2 ^ 64 (shadow span, stack band, word); the B' image numbers above
   (computation). No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YC80x YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CrsModel PRW_CrcGen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import CrsKitBp S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PRW_WalkEnvB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- COPIED from YGcallMxmn.v (blob 2ca1815f60a8 :636-701): memnorm across one symbolic-runner phase ---- *)
Lemma crsRB_wview_absent_seg : forall segs m a, wview segs m a <> None -> m a = None ->
  find_segment segs (bv_unsigned a) 1 <> None.
Proof.
  intros segs m a W E. unfold wview in W. rewrite E in W.
  destruct (find_segment segs (bv_unsigned a) 1); [discriminate|]. exfalso. apply W. reflexivity.
Qed.

Lemma crsRB_wview_not_ro : forall segs m a, wview segs m a <> None -> m a = None -> YAkMemnorm.ro_addr segs a = false.
Proof.
  intros segs m a H Hm. unfold wview, YAkMemnorm.ro_addr in *. rewrite Hm in H.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|]; [|reflexivity].
  destruct (seg_writable seg); [reflexivity|]. exfalso; apply H; reflexivity.
Qed.

Lemma crsRB_in_wrange_dec : forall E rs a, {in_wrange E rs a} + {~ in_wrange E rs a}.
Proof.
intros E rs a.
destruct (Exists_dec (fun r => YP09.base_val E (YP09.r_base r) + YP09.r_wlo r <= a < YP09.base_val E (YP09.r_base r) + YP09.r_whi r) rs)
  as [Hx|Hx].
- intros r. destruct (Z_le_dec (YP09.base_val E (YP09.r_base r) + YP09.r_wlo r) a);
  [destruct (Z_lt_dec a (YP09.base_val E (YP09.r_base r) + YP09.r_whi r))|]; [left; lia | right; lia | right; lia].
- left. apply Exists_exists in Hx. exact Hx.
- right. intros Hf. apply Hx. apply Exists_exists. exact Hf.
Qed.

Section fr. Context {fx : YK11.FPState}.
Lemma crsRB_memnorm_frame_of : forall (segs : list Segment) (H : word -> bool) E ss (ms : machine_state) (m' : word -> option byte), YAkMemnorm.memnorm segs (ms_mem ms) -> st_ok segs E ss (restrict H ms) -> frame_of E (ss_mem ss) (ms_mem ms) m' -> YAkMemnorm.memnorm segs m'.
Proof.
intros segs H E ss ms m' (Hi & Ht) HS HF.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & ROK & _) & _).
assert (HW : forall a : word, in_wrange E (ss_mem ss) (bv_unsigned a) -> wview segs (mrestrict H (ms_mem ms)) a <> None).
{ intros a (r & Hin & Hr).
  pose proof (proj1 (Forall_forall _ _) ROK r Hin) as Hok. unfold region_ok in Hok.
  destruct Hok as (_ & _ & Hw & _).
  specialize (Hw (bv_unsigned a - YP09.base_val E (YP09.r_base r)) ltac:(lia)).
  unfold writable_at in Hw.
  replace (YP09.base_val E (YP09.r_base r) + (bv_unsigned a - YP09.base_val E (YP09.r_base r))) with (bv_unsigned a) in Hw by lia.
  rewrite Z_to_bv_bv_unsigned in Hw. exact Hw. }
assert (HN : forall a : word, ms_mem ms a = None -> mrestrict H (ms_mem ms) a = None).
{ intros a Ea. unfold mrestrict. destruct (H a); [reflexivity | exact Ea]. }
split.
- intros a b Ea. destruct (ms_mem ms a) as [b0|] eqn:E0; [exact (Hi a b0 E0)|].
  destruct (crsRB_in_wrange_dec E (ss_mem ss) (bv_unsigned a)) as [Hin|Hout].
  + exact (crsRB_wview_not_ro segs (mrestrict H (ms_mem ms)) a (HW a Hin) (HN a E0)).
  + rewrite (HF a Hout), E0 in Ea. discriminate.
- intros a b Ea. destruct (ms_mem ms a) as [b0|] eqn:E0; [exact (Ht a b0 E0)|].
  destruct (crsRB_in_wrange_dec E (ss_mem ss) (bv_unsigned a)) as [Hin|Hout].
  + left. exact (crsRB_wview_absent_seg segs (mrestrict H (ms_mem ms)) a (HW a Hin) (HN a E0)).
  + rewrite (HF a Hout), E0 in Ea. discriminate.
Qed.
End fr.

(* the segment environment TE and its lemmas (lib/A/Prog/PRW_WalkEnv.v's TE part at B'): lib/B/Prog/PRW_WalkEnvB.v,
   Required above; this file's own copy is gone (one copy for the walk) *)

(* ======================================================================================================== *)
(* ---- THE SYMBOLIC STATE at R (PRW_WalkEnv's TE: atoms 0-31 the entry registers, 32-63 the current ones, 64 the
   flag's address; xr r = 32 + r). gp, tp pinned to the entry's, s0 to the entry sp (atom 2). Regions: the flag word
   (F + 120 through s2, read-only, its value the flag's address), the flag byte (writable), the thirteen saves below
   the entry sp (read-only, the entry registers in CRS_SAVED_B's order), the frame's sixteen shadow bytes (through s9,
   writable), the frame's first word (through s10, writable: the retired magic). s2's fact 4096 <= F decides
   `beqz s2`. ---- *)
Definition crsRB_sr : list sv := sr_set (sr_set (sr_set cur_atoms 3%bv (SOff 3 0)) 4%bv (SOff 4 0)) 8%bv (SOff 2 0).
Definition crsRB_saves : list YP09.chunk :=
  [YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
   YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
   YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
   YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
   YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-104) (CVal 8 (SOff 27 0))].
Definition crsRB_ss : sstate := mkSS CRS_PC_R_B crsRB_sr
  [ YP09.mkRegion (Some (xr 18)) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 64 0))];
    YP09.mkRegion (Some 64%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 2%nat) (-104) 0 0 0 crsRB_saves;
    YP09.mkRegion (Some (xr 25)) 0 16 0 16 [];
    YP09.mkRegion (Some (xr 26)) 0 8 0 8 [] ] None
  (mkFacts [(xr 18, mkAF 4096 (2 ^ 47) 5); (64%nat, mkAF 0 (2 ^ 47) 0); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
            (xr 25, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0); (xr 26, mkAF 4096 (2 ^ 47) 5)] [] []).

(* closes `ew (TE r0 rc mo) n = X` for an entry register, a current register or an extra (Crt102Tail's S10Env.v
   te_close, restated: S10Env.v is not on this base) *)
Local Ltac crsRB_te_close :=
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

(* R's write set: the frame's sixteen shadow bytes, its first word (the retired magic), the flag byte *)
Definition crsRB_wr (F fl a : Z) : Prop := (shadow_addr F <= a < shadow_addr F + 16) \/ (F <= a < F + 8) \/ a = fl.

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

(* the image's four segments are contiguous over [pa_lo, pa_hi) (by computation) *)
Lemma crsRB_img_seg : forall a, @pa_lo _ B_prog_listing PA <= a < @pa_hi _ B_prog_listing PA -> in_img SEGS a.
Proof.
intros a Ha. unfold in_img.
assert (EL : @pa_lo _ B_prog_listing PA = 65536 /\ @pa_hi _ B_prog_listing PA = 6295552) by (vm_compute; split; reflexivity).
destruct EL as [EL1 EL2]. rewrite EL1, EL2 in Ha.
assert (Hseg : forall i lo n, nth_error SEGS i <> None ->
  option_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) (nth_error SEGS i) = Some (lo, n) ->
  lo <= a < lo + n -> exists sg, In sg SEGS /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)).
{ intros i lo n Hne Hm Hr. destruct (nth_error SEGS i) as [s|] eqn:Es; [|exfalso; exact (Hne eq_refl)].
  cbn [option_map] in Hm. injection Hm as <- <-. exists s. split; [exact (nth_error_In _ _ Es) | exact Hr]. }
destruct (Z_lt_le_dec a 200704).
{ apply (Hseg 0%nat 65536 135168); [vm_compute; discriminate | vm_compute; reflexivity | lia]. }
destruct (Z_lt_le_dec a 663552).
{ apply (Hseg 1%nat 200704 462848); [vm_compute; discriminate | vm_compute; reflexivity | lia]. }
destruct (Z_lt_le_dec a 671744).
{ apply (Hseg 2%nat 663552 8192); [vm_compute; discriminate | vm_compute; reflexivity | lia]. }
apply (Hseg 3%nat 671744 5623808); [vm_compute; discriminate | vm_compute; reflexivity | lia].
Qed.

(* the symbolic state at R from concrete facts (Crt102Tail.v ct_F_entry's shape) *)
Lemma crsRB_entry : forall fxk (Wc : world SEGS) memc (r0 rg : bvmap 5 word) F fl,
  getr rg 18 = w64 F -> getr rg 25 = w64 (shadow_addr F) -> getr rg 26 = w64 F ->
  getr rg 3 = getr r0 3 -> getr rg 4 = getr r0 4 -> getr rg 8 = getr r0 2 ->
  2 ^ 46 <= spZ r0 <= 2 ^ 47 -> spZ r0 mod 16 = 0 ->
  4096 <= F -> F + 128 <= spZ r0 - 104 -> F mod 32 = 0 -> F + 128 <= 2 ^ 47 ->
  0 <= fl -> fl + 1 <= spZ r0 - 104 -> (fl + 1 <= F \/ F + 128 <= fl) ->
  (fl + 1 <= shadow_addr F \/ shadow_addr F + 16 <= fl) -> fl <= 2 ^ 47 ->
  (F + 128 <= shadow_addr F \/ shadow_addr F + 16 <= F) -> shadow_addr F + 16 <= spZ r0 - 104 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (F + 120) 8 fl ->
  Forall (fun p : Z * bv 5 =>
            rdword (aview SEGS (w_H Wc) memc) (spZ r0 - 128 + fst p) = Some (bv_unsigned (getr r0 (snd p))))
    CRS_SAVED_B ->
  (forall a, F <= a < F + 8 -> apresent (w_H Wc) memc a) ->
  (forall a, shadow_addr F <= a < shadow_addr F + 16 -> apresent (w_H Wc) memc a) ->
  apresent (w_H Wc) memc fl ->
  st_ok_pi SEGS VAL (TE r0 rg [w64 fl]) crsRB_ss
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + CRS_PC_R_B)) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE r0 rg [w64 fl]) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc r0 rg F fl R18 R25 R26 R3 R4 R8 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 VFL HSV PF PSH PFL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := TE r0 rg [w64 fl]).
assert (Hsh : SHADOW_OFF <= shadow_addr F < SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (X18 : bv_unsigned (ew E (xr 18)) = F).
{ unfold E, xr. rewrite (te_cur r0 rg _ 18%bv 18) by reflexivity. rewrite R18. apply unsigned_lit_small. lia. }
assert (X25 : bv_unsigned (ew E (xr 25)) = shadow_addr F).
{ unfold E, xr. rewrite (te_cur r0 rg _ 25%bv 25) by reflexivity. rewrite R25. apply unsigned_lit_small.
  unfold SHADOW_OFF in *. lia. }
assert (X26 : bv_unsigned (ew E (xr 26)) = F).
{ unfold E, xr. rewrite (te_cur r0 rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small. lia. }
assert (E64 : ew E 64 = w64 fl) by exact (te_more_lt r0 rg [w64 fl] 0 ltac:(lia)).
assert (X64 : bv_unsigned (ew E 64) = fl) by (rewrite E64; apply unsigned_lit_small; lia).
assert (X2 : bv_unsigned (ew E 2) = spZ r0) by (unfold E; rewrite (te_entry r0 rg _ 2%bv 2) by reflexivity; reflexivity).
assert (EN : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E n = getr r0 r)
  by (intros r n Hn; unfold E; apply te_entry; exact Hn).
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE r0 rg [w64 fl]) with E.
- unfold crsRB_sr.
  apply YI04.regs_ok_pin; [| intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 2%bv 2%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R8].
  apply YI04.regs_ok_pin; [| intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 4%bv 4%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R4].
  apply YI04.regs_ok_pin; [apply te_regs_ok | intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 3%bv 3%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R3].
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 18) F); [exact X18 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 120 8 (SOff 64 0) fl);
      [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    exact VFL.
  + apply (ts_rok E _ 64 fl); [exact X64 | lia | lia | intros o Ho; apply (apresent_writable SEGS);
      replace (fl + o) with fl by lia; exact PFL | constructor].
  + apply (ts_rok E _ 2 (spZ r0)); [exact X2 | lia | lia | intros o Ho; lia |].
    unfold crsRB_saves. repeat apply Forall_cons; try apply Forall_nil.
    all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
      let j := eval vm_compute in (Z.to_nat (- off / 8 - 1)) in
      let p := eval vm_compute in (nth j CRS_SAVED_B (0, 0%bv)) in
      let r := eval vm_compute in (snd p) in
      let o := eval vm_compute in (fst p) in
      assert (V : rdword (aview SEGS (w_H Wc) memc) (spZ r0 - 128 + o) = Some (bv_unsigned (getr r0 r)))
        by (exact (proj1 (Forall_forall _ _) HSV (o, r) ltac:(cbv [CRS_SAVED_B In]; repeat (first [left; reflexivity | right]))));
      apply (ts_chunk E _ _ off 8 (SOff n 0) (bv_unsigned (getr r0 r)));
      [ cbn [sv_denot]; rewrite (EN r n) by reflexivity; rewrite Z.add_0_r; reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr r0 r)) as BR; change (bv_modulus 64) with (2 ^ 64) in BR; cbn; lia
      | cbn; lia
      | apply (val_mem_of_rdword SEGS) in V; replace (spZ r0 + off) with (spZ r0 - 128 + o) by lia; exact V ]
    end.
  + apply (ts_rok E _ (xr 25) (shadow_addr F)); [exact X25 | unfold SHADOW_OFF in *; lia | unfold SHADOW_OFF in *; lia | |
      constructor].
    intros o Ho. apply (apresent_writable SEGS). apply PSH. lia.
  + apply (ts_rok E _ (xr 26) F); [exact X26 | lia | lia | | constructor].
    intros o Ho. apply (apresent_writable SEGS). apply PF. lia.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X18, X64, X2, X25, X26.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X18, X64, X2, X25, X26.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 0) with 1. unfold SHADOW_OFF in *. repeat split; lia.
Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation LEDGER := (prh_ledger (PI := prh_img_B) (PA := PA) B).
#[local] Notation STK := (STK_check_reject_clean_starved (PI := prh_img_B)).

(* ---- the ledger (the kit's E-sweep prh_ledger, PRH_Base.v blob fdb45545469b :507-526: the statics with g_most and
   g_own_ran_out, the blocks, the heads) is kept by a memory change that keeps alloc.c's statics and each block's head
   word, at a state whose blocks contain the old ones (S1Ledger.v's prh_ledger_kept_aview, restated for the E sweep's
   two cells: S1Ledger.v on this base still states the old ledger) ---- *)
Lemma crsRB_ledger_kept : forall ly S Hp W mem ly' S' W' mem' Lam peak cnt fail ran most own,
  LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) PST -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 ->
     aview SEGS (w_H W') mem' (a - cf_head + i) = aview SEGS (w_H W) mem (a - cf_head + i)) ->
  (forall a k, In (a, k) Lam -> In (a - cf_head, k + cf_head) (ablocks B ly S) ->
     In (a - cf_head, k + cf_head) (ablocks B ly' S')) ->
  LEDGER ly' S' Hp W' mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem ly' S' W' mem' Lam peak cnt fail ran most own
  ((G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & GR) & HND & HBL & HHP) Hs Hh Hb.
assert (VK : forall a w v, val_mem SEGS (mrestrict (w_H W) mem) a w v ->
  (forall k, (k < w)%nat -> Exists (in_zr (a + Z.of_nat k)) PST) -> val_mem SEGS (mrestrict (w_H W') mem') a w v).
{ intros a w v Hv Hx k Hk. rewrite <- (Hv k Hk). apply (mbyte_of_aview SEGS). exact (Hs _ (Hx k Hk)). }
assert (HPS : forall a w, In (a, Z.of_nat w) PST -> forall k, (k < w)%nat -> Exists (in_zr (a + Z.of_nat k)) PST).
{ intros a w Hin k Hk. apply Exists_exists. exists (a, Z.of_nat w). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
unfold prh_pst in HPS.
split.
{ split; [apply (VK _ _ _ G1), HPS; cbn [In]; repeat (first [left; reflexivity | right])|].
  split; [apply (VK _ _ _ G2), HPS; cbn [In]; repeat (first [left; reflexivity | right])|].
  split; [apply (VK _ _ _ G3), HPS; cbn [In]; repeat (first [left; reflexivity | right])|].
  split; [apply (VK _ _ _ G4), HPS; cbn [In]; repeat (first [left; reflexivity | right])|].
  split; [apply (VK _ _ _ G5), HPS; cbn [In]; repeat (first [left; reflexivity | right])|].
  split; [split; [apply (VK _ _ _ G6), HPS; cbn [In]; repeat (first [left; reflexivity | right]) | exact G6r]|].
  split; [split; [apply (VK _ _ _ G7), HPS; cbn [In]; repeat (first [left; reflexivity | right]) | exact G7r]|].
  exact GR. }
split; [exact HND|]. split; [|exact HHP].
rewrite Forall_forall in HBL |- *. intros (a, k) Hin.
destruct (HBL (a, k) Hin) as (Hk0 & Hab & Hhp & Hal & Hv). cbn [fst snd] in *.
split; [exact Hk0|]. split; [exact (Hb a k Hin Hab)|]. split; [exact Hhp|]. split; [exact Hal|].
intros j Hj. rewrite <- (Hv j Hj). apply (mbyte_of_aview SEGS). apply (Hh a k (Z.of_nat j) Hin). lia.
Qed.

(* ---- what R's three writes keep: the ledger (at the released state), the input bytes, the document ---- *)
Lemma crsRB_keep : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C ly3 S3 Hp3 W3 mem3 md3 k Lam3 peak3 cnt3
  ran3 S' mem' md' fl,
  8 <= cf_head ->
  crs_pre_B B ARx CTX0 C -> crs_JR_B B ARx R C ly3 S3 Hp3 W3 mem3 md3 k ->
  frames S3 = (CRS_CID_B, cb_fpos C) :: frames (cb_S C) ->
  crs_perm_B B C ly3 S3 Lam3 -> LEDGER ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 SIZE_MAXZ ran3 (cb_most C) 0 ->
  PRH_Base.bytes_at W3 mem3 (cb_data C) (cb_tb C) -> crs_tree_B C ly3 S3 Lam3 W3 mem3 ->
  ARx ly3 S' Hp3 W3 mem' md' -> ablocks B ly3 S' = ablocks B ly3 S3 -> frames S' = frames (cb_S C) ->
  aowned B ly3 S3 fl -> ~ in_img SEGS fl ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ crsRB_wr (cF_B C) fl a ->
     aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a) ->
  LEDGER ly3 S' Hp3 W3 mem' Lam3 peak3 cnt3 SIZE_MAXZ ran3 (cb_most C) 0 /\
  PRH_Base.bytes_at W3 mem' (cb_data C) (cb_tb C) /\
  (cb_doc C <> 0 -> pj_nodeR SEGS (mrestrict (w_H W3) mem') (prh_lin Lam3) (cb_doc C) (cb_t C) (cb_D C)).
Proof.
intros R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k Lam3 peak3 cnt3 ran3 S' mem' md' fl HH8 HP HJ EFR3 (HPL & HPA) HLED HBY
  HTR HAR' EAB' EFR' Fown Fimg HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof HP as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & HD0 & HD1 & _ & HHOME & _ & HDOC & HLED0 & _).
pose proof HPRE as ((HAR0 & _) & _).
pose proof HJ as HJ'. unfold crs_JR_B in HJ'. destruct HJ' as (HAR3 & HLE3 & _).
destruct (crs_cF_keepR_B B ARx LAWS R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k HP HJ) as (EF3 & _).
assert (Hin : In (CRS_CID_B, cb_fpos C) (frames S3)) by (rewrite EFR3; left; reflexivity).
assert (E128 : fs_frame_bytes CRS_CID_B = 128) by (vm_compute; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 CRS_CID_B (cb_fpos C) HAR3 Hin) as (Fb1 & Fb2 & Fb3).
rewrite EF3 in Fb1, Fb2, Fb3. rewrite E128 in Fb2, Fb3.
(* ---- R's writes miss the image, every live block and every frame of the entry state ---- *)
assert (NWimg : forall a, crsRB_wr (cF_B C) fl a -> ~ in_img SEGS a).
{ intros a [Ha | [Ha | ->]]; [| | exact Fimg].
  - intros Hi. pose proof (pa_segs_low a Hi) as Hl. unfold shadow_addr in Ha. unfold SHADOW_OFF, kLowMemEnd in *. lia.
  - apply (frm_img_x SEGS B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 CRS_CID_B (cb_fpos C) a HAR3 Hin). rewrite EF3, E128. lia. }
assert (NWblk : forall a p n, crsRB_wr (cF_B C) fl a -> In (p, n) (ablocks B ly3 S3) -> p <= a < p + req_size n -> False).
{ intros a p n Hw Hpn Ha.
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W3 mem3 md3 p n HAR3 Hpn) as (_ & _ & _ & Happ & Hb & _).
  destruct Hw as [Hs | [Hf | ->]].
  - pose proof (in_app_addr _ _ a Happ Ha) as Hap.
    unfold app_addr, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - pose proof (sep_block_frame_x SEGS B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 p n CRS_CID_B (cb_fpos C) HAR3 Hpn Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF3, E128 in Hd. lia.
  - exact (proj2 (Hb fl Ha) Fown). }
assert (NWfrm : forall a cid pos, crsRB_wr (cF_B C) fl a -> In (cid, pos) (frames (cb_S C)) ->
  frame_addr ly3 cid pos <= a < frame_addr ly3 cid pos + fs_frame_bytes cid -> False).
{ intros a cid pos Hw Hg Ha.
  assert (Hg3 : In (cid, pos) (frames S3)) by (rewrite EFR3; right; exact Hg).
  destruct (alx_frames _ _ _ LAWS ly3 S3 Hp3 W3 mem3 md3 cid pos HAR3 Hg3) as (_ & Happ & Hfb & _).
  destruct Hw as [Hs | [Hf | ->]].
  - pose proof (in_app_addr _ _ a Happ Ha) as Hap.
    unfold app_addr, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - apply in_split in Hg as (l2 & l3 & El).
    pose proof (sep_frames_pos_x SEGS B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 (CRS_CID_B, cb_fpos C) (cid, pos) [] l2 l3 HAR3
      ltac:(rewrite EFR3, El; reflexivity)) as Hd.
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite EF3, E128 in Hd.
    pose proof (fs_frame_bytes_nonneg cid). lia.
  - exact (proj2 (Hfb fl Ha) Fown). }
(* the ledger's blocks, and the bytes of a live block, kept *)
assert (HLB : forall a k0, In (a, k0) Lam3 -> 0 <= k0 /\ In (a - cf_head, k0 + cf_head) (ablocks B ly3 S3)).
{ intros a k0 Hin0. pose proof (prh_ledger_blocks B ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 SIZE_MAXZ ran3 (cb_most C) 0 HLED) as HF.
  rewrite Forall_forall in HF. destruct (HF (a, k0) Hin0) as (Hk0 & Hab & _). exact (conj Hk0 Hab). }
assert (HKB : forall p n i, In (p, n) (ablocks B ly3 S3) -> 0 <= i < req_size n ->
  aview SEGS (w_H W3) mem' (p + i) = aview SEGS (w_H W3) mem3 (p + i)).
{ intros p n i Hpn Hi. destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W3 mem3 md3 p n HAR3 Hpn) as (_ & H4096 & Hc & _).
  apply HK; [lia|]. intros Hw. exact (NWblk _ p n Hw Hpn ltac:(lia)). }
split.
{ apply (crsRB_ledger_kept ly3 S3 Hp3 W3 mem3 ly3 S' W3 mem' Lam3 peak3 cnt3 SIZE_MAXZ ran3 (cb_most C) 0 HLED).
  - intros a Ha. pose proof (@pa_segs_low _ _ PA a (pst_in_img_B a Ha)) as Hlow.
    apply HK; [unfold kLowMemEnd in Hlow; lia|]. intros Hw. exact (NWimg a Hw (pst_in_img_B a Ha)).
  - intros a k0 i Hin0 Hi. destruct (HLB a k0 Hin0) as (Hk0 & Hab).
    apply (HKB (a - cf_head) (k0 + cf_head) i Hab). unfold req_size. destruct (Z.eqb_spec (k0 + cf_head) 0); lia.
  - intros a k0 _ Hab. rewrite EAB'. exact Hab. }
split.
{ (* the input bytes: in an entry block, a live ledger block or the read-only image (the reader's home) *)
  assert (HDK : forall j, (j < length (cb_tb C))%nat ->
    aview SEGS (w_H W3) mem' (cb_data C + Z.of_nat j) = aview SEGS (w_H W3) mem3 (cb_data C + Z.of_nat j)).
  { intros j Hj. unfold cSize_B in HD1. apply HK; [lia|]. intros Hw.
    assert (Hab3 : forall b m, In (b, m) (ablocks B (cb_ly C) (cb_S C)) -> In (b, m) (ablocks B ly3 S3))
      by (intros b m Hbm; exact (Permutation_in _ (Permutation_sym HPA) Hbm)).
    unfold PRH_FnReader.prhReader_home, kept_at, kept_img, cSize_B in HHOME.
    destruct HHOME as [[(b & m & Hbm & Hb1 & Hb2) | [(_ & Hi1 & Hi2 & _) | (Hi1 & Hi2 & _)]] | (b & m & Hbm & _ & Hb1 & Hb2)].
    - pose proof (prh_ledger_blocks B (cb_ly C) (cb_S C) (cb_Hp C) (cb_W C) (cb_mem C) (cb_Lam C) (cb_peak C) (cb_cnt C)
        SIZE_MAXZ (cb_ran C) (cb_most C) 0 HLED0) as HF.
      rewrite Forall_forall in HF. destruct (HF (b, m) Hbm) as (Hm0 & Hab & _). cbn [fst snd] in Hm0, Hab.
      apply (NWblk _ (b - cf_head) (m + cf_head) Hw (Hab3 _ _ Hab)).
      unfold req_size. destruct (Z.eqb_spec (m + cf_head) 0); lia.
    - apply (NWimg _ Hw). apply crsRB_img_seg. lia.
    - apply (NWimg _ Hw). apply crsRB_img_seg. lia.
    - apply (NWblk _ b m Hw (Hab3 _ _ Hbm)). unfold req_size. destruct (Z.eqb_spec m 0); lia. }
  intros j Hj. destruct (HBY j Hj) as (Hv & Hr). split; [|exact Hr].
  intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. rewrite <- (Hv 0%nat Hkk). cbn [Z.of_nat]. rewrite !Z.add_0_r.
  apply (mbyte_of_aview SEGS). exact (HDK j Hj). }
(* the document: its header in a frame of the entry state, its blocks ledger blocks *)
intros Hdoc. destruct (HTR Hdoc) as (HND & HDL & _ & _).
destruct HDOC as [H0 | (_ & HTOK0 & _)]; [exfalso; exact (Hdoc H0)|].
destruct HTOK0 as (_ & _ & _ & (_ & (cid & pos & Hg & Hg1 & Hg2) & _)).
destruct (crs_ly_keep_B B ARx LAWS (cb_ly C) (cb_S C) (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C) ly3 cid pos HAR0 HLE3)
  as (Ely & _).
assert (Hg3 : In (cid, pos) (frames S3)) by (rewrite EFR3; right; exact Hg).
destruct (frames_bounds_x SEGS B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 cid pos HAR3 Hg3) as (Gb1 & Gb2 & _).
rewrite Ely in Gb1, Gb2.
apply (pj_nodeR_frame SEGS (cb_t C) (mrestrict (w_H W3) mem3) (mrestrict (w_H W3) mem') (prh_lin Lam3) (cb_doc C) (cb_D C) HND).
intros x [Hx | ((a, k0) & Hb & Hx)].
- split.
  + apply (mbyte_of_aview SEGS). apply HK; [lia|]. intros Hw. exact (NWfrm x cid pos Hw Hg ltac:(rewrite Ely; lia)).
  + intros _. apply (apresent_writable SEGS).
    assert (HgS : In (cid, pos) (frames S')) by (rewrite EFR'; exact Hg).
    destruct (alx_frames _ _ _ LAWS ly3 S' Hp3 W3 mem' md' cid pos HAR' HgS) as (_ & _ & Hfb' & _).
    exact (proj1 (Hfb' x ltac:(rewrite Ely; lia))).
- unfold pj_holdsR in Hx. cbn [fst snd] in Hx. destruct (HLB a k0 (HDL _ Hb)) as (Hk0 & Hab).
  assert (Hrq : a - cf_head <= x < a - cf_head + req_size (k0 + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
  split.
  + apply (mbyte_of_aview SEGS). replace x with (a - cf_head + (x - (a - cf_head))) by lia.
    apply (HKB _ _ _ Hab). lia.
  + intros _. apply (apresent_writable SEGS).
    destruct (alx_blocks _ _ _ LAWS ly3 S' Hp3 W3 mem' md' _ _ HAR' ltac:(rewrite EAB'; exact Hab))
      as (_ & _ & _ & _ & Hb' & _).
    exact (proj1 (Hb' x Hrq)).
Qed.

(* THE POSITION STEP of R, the one place R reads the model-run position (kit v2 c0766e47c280: crs_pos_B is the EXACT
   position cb_rp_i C + length evs under ran3 = 0): the inline release keeps it (PresetRoomPosKeep.room_pos_stack_free) *)
Lemma crsRB_pos_step : forall C evs ran3 S3 c p, crs_pos_B C evs ran3 S3 -> crs_pos_B C evs ran3 (stack_free_state c p S3).
Proof.
intros C evs ran3 S3 c p HP H0. destruct (HP H0) as (h' & HRP). exists h'.
exact (PresetRoomPosKeep.room_pos_stack_free _ _ _ _ _ _ _ _ _ HRP).
Qed.

(* ---- R (+688): THE SEGMENT. The premises, in h-w6u-rep's order: HX_asfx, HX_fflx, HX_sfx are YGcallSx.v's ASFX /
   FFLX / SFX (blob 17d7d2cdbcd1 :214-226) verbatim at segs := SEGS; HX_fflp is Crt102Tail.v's FFLP (blob
   2f7b18811820 :384-385) verbatim; HI_head8 is the instance fact 8 <= cf_head (CfParams_preset: 16). ---- *)
Lemma crs_seg_R_B : forall CTX0 C
  (HX_asfx : forall ly S Hp W mem md mem' md' cid pos,
    ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
    aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
    (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
    (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
    m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
    (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
    ARx ly (stack_free_state cid pos S) Hp W mem' md')
  (HX_fflx : forall ly S Hp (W : world SEGS) mem md cid pos,
    ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
    aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)))
  (HX_sfx : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
    exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2)
  (HX_fflp : forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
    apresent (w_H W) mem (flag_addr ly cid pos))
  (HI_head8 : 8 <= cf_head),
  crs_from_R_B (fx := fx) (rc := rc) (ci := ci) (cp := cp) (RL := RL) (SK := SK) B ARx CTX0 C.
Proof.
intros CTX0 C ASFX FFLX SFX FFLP HH8.
unfold crs_from_R_B.
intros fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 cnt3 ran3 HB HRS HLV HBY HTR HCE.
(* THE WORLD RELATION: R's cut is after the walk's first free, so its boundary is crs_baseR_B at R := wle' SEGS RZ_cf;
   the run (the flag store and the epilogue) by the engine's R rule aj_flag_store_xR, and the text's post fpostFbm is
   at the same relation (PRH_Base.fpostFb is apost_base_xbFR at wle'), so the journal is unbased at R *)
unfold YA0nH.SRr'.
set (R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) in *.
assert (Rr : forall W, R W W) by exact (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf).
assert (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) by exact (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf).
pose proof HB as (HP & HFZ & HFK & HJ & HFRM & HSV & HSL & HROD & HMN & R3 & R4 & Hsp2a & Hsp2b & Hsp2m & HDP).
(* frm_zero's Z.land / Z.shiftr body makes lia fail: keep it out of lia's sight (Crt102Tail.v ct_at_F) *)
assert (HFZ' : unit -> frm_zero (@YK11.fp_csr fxk)) by (intros _; exact HFZ). clear HFZ.
pose proof HP as (HPRE & _).
pose proof HPRE as ((HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (crs_cF_keepR_B B ARx LAWS R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k HP HJ) as (EF3 & _).
unfold crs_regsat_B, crs_rbase_B, crs_rsh_B in HRS. cbn [app] in HRS. repeat rewrite Forall_cons_iff in HRS.
cbn [fst snd] in HRS. destruct HRS as (G2 & G8 & G9 & G18 & G26 & G27 & G25 & _).
destruct HFRM as (EFR3 & HFLW & HFP).
pose proof HJ as HJ0. unfold crs_JR_B in HJ0. pose proof HJ0 as (HAR3 & HLE3 & _).
assert (Hin : In (CRS_CID_B, cb_fpos C) (frames S3)) by (rewrite EFR3; left; reflexivity).
assert (E128 : fs_frame_bytes CRS_CID_B = 128) by (vm_compute; reflexivity).
assert (HSTK : 104 <= STK) by (apply Z.leb_le; vm_compute; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 CRS_CID_B (cb_fpos C) HAR3 Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS ly3 S3 Hp3 W3 mem3 md3 CRS_CID_B (cb_fpos C) HAR3 Hin) as (F32 & _ & Ffr & Fsh).
rewrite EF3 in Fb1, Fb2, Fb3, F32, Ffr, Fsh. rewrite E128 in Fb2, Fb3, Ffr, Fsh, HFLW, HFP.
destruct (FFLX ly3 S3 Hp3 W3 mem3 md3 CRS_CID_B (cb_fpos C) HAR3 Hin) as (Fown & Fapp & Fimg).
pose proof (FFLP ly3 S3 Hp3 W3 mem3 md3 CRS_CID_B (cb_fpos C) HAR3 Hin) as Fpr.
set (fl := flag_addr ly3 CRS_CID_B (cb_fpos C)) in *.
set (F := cF_B C) in *.
set (sp0 := spZ (cb_regs C)) in *.
pose proof (app_addr_below_ceil fl Fapp) as Flow. unfold ASAN_CEIL in Flow.
assert (Hflf : fl + 1 <= F \/ F + 128 <= fl).
{ destruct (Z_lt_le_dec fl F) as [Hl|Hl]; [left; lia|].
  destruct (Z_le_gt_dec (F + 128) fl) as [Hg|Hg]; [right; lia|].
  exfalso. exact (proj2 (Ffr fl ltac:(lia)) Fown). }
assert (Hfls : fl + 1 <= shadow_addr F \/ shadow_addr F + 16 <= fl).
{ destruct (Z_lt_le_dec fl (shadow_addr F)) as [Hl|Hl]; [left; lia|].
  destruct (Z_le_gt_dec (shadow_addr F + 16) fl) as [Hg|Hg]; [right; lia|].
  exfalso. pose proof (Fsh (fl - shadow_addr F) ltac:(lia)) as (_ & Hno).
  replace (shadow_addr F + (fl - shadow_addr F)) with fl in Hno by lia. exact (Hno Fown). }
assert (VFL : val_mem SEGS (mrestrict (w_H W3) mem3) (F + 120) 8 fl).
{ apply (val_mem_of_rdword SEGS). replace (F + 120) with (F + 128 - 8) by lia. exact HFLW. }
assert (R8' : getr regs3 8 = getr (cb_regs C) 2) by (rewrite G8; unfold w64, sp0, spZ; apply Z_to_bv_bv_unsigned).
assert (Hsp0 : 2 ^ 46 <= sp0 <= 2 ^ 47) by lia.
assert (HFsh : F + 128 <= shadow_addr F \/ shadow_addr F + 16 <= F).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fb3. unfold shadow_addr, SHADOW_OFF. lia. }
destruct (crsRB_entry fxk W3 mem3 (cb_regs C) regs3 F fl G18 G25 G26 R3 R4 R8' Hsp0 Hal16 Fb1 ltac:(lia) F32
  ltac:(lia) ltac:(unfold fl; lia) ltac:(lia) Hflf Hfls ltac:(lia) HFsh ltac:(unfold shadow_addr, SHADOW_OFF; lia)
  VFL HSV ltac:(intros a Ha; exact (proj1 (Ffr a ltac:(lia))))
  ltac:(intros a Ha; pose proof (Fsh (a - shadow_addr F) ltac:(lia)) as (Hp0 & _);
        replace (shadow_addr F + (a - shadow_addr F)) with a in Hp0 by lia; exact Hp0) Fpr) as [HS SHOK].
set (E := TE (cb_regs C) regs3 [w64 fl]) in *.
assert (HEI : img_env VAL A_LIM E) by apply te_env.
assert (U64 : bv_unsigned (ew E 64) = fl).
{ unfold E. rewrite (te_more_lt (cb_regs C) regs3 [w64 fl] 0) by lia. cbn [nth]. apply unsigned_lit_small. lia. }
assert (U25 : bv_unsigned (ew E (xr 25)) = shadow_addr F).
{ unfold E, xr. rewrite (te_cur (cb_regs C) regs3 _ 25%bv 25) by reflexivity. rewrite G25. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
assert (U26 : bv_unsigned (ew E (xr 26)) = F).
{ unfold E, xr. rewrite (te_cur (cb_regs C) regs3 _ 26%bv 26) by reflexivity. rewrite G26. apply unsigned_lit_small. lia. }
(* R's writes: the flag byte, the sixteen shadow bytes, the frame's first word *)
assert (HwrR : forall a, in_wrange E (ss_mem crsRB_ss) a -> crsRB_wr F fl a).
{ intros a (rr & Hr & Ha). cbv [crsRB_ss ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha;
    rewrite ts_bv_some in Ha.
  - lia.
  - rewrite U64 in Ha. right; right. lia.
  - lia.
  - rewrite U25 in Ha. left. lia.
  - rewrite U26 in Ha. right; left. lia. }
unfold crs_cfg_B, w64.
pose (FS := aj_flag_store_xR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS pa_segs_low ASFX FFLX SFX
  asym pa_wx (clookup pa_tbl) VAL SIGMA B_prog_listing (@pl_tpi _ PL) (@pl_tw _ PL)
  pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text (@pl_lim _ PL) (@pl_len _ PL) (@pl_tpi_eq _ PL) (@pl_tw_eq _ PL)
  R Rr Rt).
lazymatch type of HS with st_ok_pi _ _ ?E0 ?ss _ =>
  let K := eval vm_compute in (run_K A_LIM (SLit 0) [] ss) in
  let rr := eval vm_compute in (sym_runN_pi_tok (@pl_tpi _ PL) (@pl_tw _ PL) K (SLit 0) (2 ^ 63, 2 ^ 63) [] FUEL ss) in
  lazymatch rr with (?st', ?rs) =>
  assert (Hrun : sym_runN_pi_tok (@pl_tpi _ PL) (@pl_tw _ PL) K (SLit 0) (2 ^ 63, 2 ^ 63) [] FUEL ss = (st', rs))
    by (vm_compute; reflexivity);
  eapply (FS W3 FUEL E0 K (SLit 0) (2 ^ 63, 2 ^ 63) [] ss st' rs _ STK sp0 [] (cb_ly C)
    (YG00.set_depot (cb_dp C) (cb_S C)) (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C) [] ly3 S3 Hp3 _ _ CRS_CID_B (cb_fpos C) _ ltac:(unfold A_LIM; cbn; lia) HEI
    ltac:(unfold CRS_CID_B; lia) HS SHOK ltac:(vm_compute; reflexivity) Hrun I HJ0)
  end end.
- (* no inline check, no obligation *)
  match goal with |- Forall ?P ?l => let l' := eval vm_compute in l in change (Forall P l') end. apply Forall_nil.
- (* the writes: the frame's own bytes and shadow bytes (in_frames), and the flag *)
  intros a HW. destruct (HwrR a HW) as [Hs | [Hm | ->]]; [left | left | right; reflexivity].
  + right; right; right. exists CRS_CID_B, (cb_fpos C). split; [left; reflexivity|]. right. unfold in_zr.
    cbn [fst snd]. rewrite EF3, E128. change (128 / 8) with 16. exact Hs.
  + right; right; right. exists CRS_CID_B, (cb_fpos C). split; [left; reflexivity|]. left. unfold in_zr.
    cbn [fst snd]. rewrite EF3, E128. lia.
- (* the flag is 0 after the run *)
  intros ws msr Hlen HSr.
  pose proof (ts_region_nth _ _ _ 1 _ HSr eq_refl) as HR1.
  lazymatch type of HSr with st_ok_pi _ _ (extK ?E1 ?KK ?ws0) _ _ =>
    assert (X64 : bv_unsigned (ew (extK E1 KK ws0) 64) = fl)
      by (rewrite (proj1 (env_agree_extK E1 KK ws0) 64%nat) by (cbv; lia); exact U64) end.
  pose proof (ts_field _ _ 64 fl _ 0 1 0 1 0 1%N (SLit 0) HR1 X64
    ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as V.
  pose proof (V 0%nat ltac:(cbn; lia)) as V0. cbn [Z.of_nat] in V0. rewrite !Z.add_0_r in V0.
  unfold fl in V0. rewrite V0. f_equal; try (rewrite U_SLit; apply bv_eq; vm_compute; reflexivity).
- (* the epilogue's `ret`: crs_post_B *)
  intros ws ms' mat' Hlen HEI' HS' SHOK' HJ' HFr1 HFr2 Hgr.
  cbn [ms_mem mkst] in HFr1, HFr2.
  assert (K' : forall a, 0 <= a < 2 ^ 64 -> ~ crsRB_wr F fl a ->
    aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) mem3 a)
    by (intros a Ha Hn; exact (ts_keep W3 _ (ss_mem crsRB_ss) mem3 (ms_mem ms') _ HFr2 HwrR a Ha Hn)).
  pose proof HJ' as (HAR' & _ & _ & _ & _ & HFR' & _).
  prreg HS' (1%bv : bv 5) Q1.
  assert (X1 : getr (ms_regs ms') 1 = getr (cb_regs C) 1).
  { rewrite Q1. lazymatch goal with |- ew (extK ?E1 ?KK ?ws0) 1 = _ =>
      rewrite (proj1 (env_agree_extK E1 KK ws0) 1%nat) by (cbv; lia) end.
    apply te_entry. reflexivity. }
  (* the memory is normal after the run (YGcallMxmn.v memnorm_frame_of, copied above) *)
  assert (HMN' : YAkMemnorm.memnorm SEGS (cb_mem C) -> YAkMemnorm.memnorm SEGS (ms_mem ms')).
  { intros _. exact (crsRB_memnorm_frame_of SEGS (w_H W3) _ _
      (@YK11.mkst fxk regs3 (Z_to_bv 64 (BASE + CRS_PC_R_B)) mem3 (YK11.seg_rom SEGS)) (ms_mem ms') HMN HS HFr1). }
  (* the keeps at the released state *)
  destruct HLV as ((HLED & HPK & HRN & HCN & HCN2 & HRL & HPOS) & HPERM).
  assert (EAB' : ablocks B ly3 (stack_free_state CRS_CID_B (cb_fpos C) S3) = ablocks B ly3 S3)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  destruct (crsRB_keep R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k Lam3 peak3 cnt3 ran3 _ (ms_mem ms') _ fl HH8 HP HJ EFR3
    HPERM HLED HBY HTR HAR' EAB' ltac:(rewrite HFR'; reflexivity) Fown Fimg K') as (HLED' & HBY' & HDOC').
  (* the `ret` keeps the world: a plain step, lifted into R (wle <= R) *)
  apply (YA0nH.SRr_SRrG SEGS R (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)).
  eapply (paj_ret_at (PL := PL) (PI := PA) W3 _ _ ms' _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
  intros mat''.
  (* THE BUDGETED POST (the kit's cut): the walk's journal is at the empty budget from the entry with its depot moved to
     cb_dp C; UNBASE it (YCbqGwild.ajournal_xw_unbase0R at R) to the journal from the entry at the budget cb_ws C, which
     the kit's crs_dpok_B bounds by the text's wbudget [] (prh_wk F_check_reject_clean_starved) *)
  destruct HDP as (HDP1 & HDP2).
  unfold crs_post_B, fpostFbm, fpostFb, fQmn, YCbqGwild.apost_base_xbFR.
  exists fxk, ly3, (stack_free_state CRS_CID_B (cb_fpos C) S3), Hp3, (ms_regs ms'), (ms_mem ms'). eexists. exists k, (cb_ws C).
  split; [rewrite X1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  split; [exact (HFZ' tt)|]. split; [exact HFK|].
  split; [exact HDP1|].
  split; [apply (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cb_dp C));
          [apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) R); exact HJ' | exact HDP2]|].
  split.
  { eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ (cb_regs C) (map (getr regs3) all_regs ++ [w64 fl]) HS');
      [| vm_compute; reflexivity].
    split.
    - intros n Hn. lazymatch goal with |- ew (extK ?E1 ?KK ?ws0) n = _ =>
        rewrite (proj1 (env_agree_extK E1 KK ws0) n) by lia end.
      unfold E, TE. apply Eimg_low. unfold A_TEXT. lia.
    - lazymatch goal with |- ed (extK ?E1 ?KK ?ws0) = _ => rewrite (proj2 (env_agree_extK E1 KK ws0)) end.
      reflexivity. }
  split; [|exact HMN'].
  destruct HCE as (HCE1 & HCE2). destruct HPERM as (HPL & HPA).
  unfold crs_Q_B. split; [exact (RL_stack_free _ _ _ HRL)|].
  exists Lam3, peak3, cnt3, ran3.
  split; [exact HPL|]. split; [rewrite EAB'; exact HPA|]. split; [exact HPK|]. split; [lia|].
  split; [left; exact HRN|]. split; [exact HRN|]. split; [exact HCE2|].
  split; [exact (crsRB_pos_step C (crs_evs_at_R_B C) ran3 S3 CRS_CID_B (cb_fpos C) HPOS)|].
  split; [exact HLED'|]. split; [exact HBY' | exact HDOC'].
Qed.
Print Assumptions crs_seg_R_B.
End f.

End d.

Print Assumptions crs_seg_R_B.
Set Printing Implicit.
About crs_seg_R_B.
Unset Printing Implicit.

(* THE INSTANCE WITNESS of crs_seg_R_B's one image / instance premise (a Theorem Labs lane's rule, 16:45Z): HI_head8 at
   preset's CfParams instance (the same for both images), by the instance's own lemma (lib/A/CfParamsPreset.v preset_head_wide) *)
Lemma HI_head8_B' : 8 <= @cf_head CfParamsPreset.CfParams_preset.
Proof. exact CfParamsPreset.preset_head_wide. Qed.
