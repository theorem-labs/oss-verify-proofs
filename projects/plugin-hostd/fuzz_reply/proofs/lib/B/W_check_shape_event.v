(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's check_shape_event,
   a NEW walk over lib/B/W_listing.v (B's body is not A's up to relocation: VERDICT.md (sha256 810ca1df9ca9; internal record)), after
   lib/A/W_check_shape_event.v (a working branch 3ed7f2a7227), in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites), lib/A/ACh2.v (internal call) and lib/A/ACbk.v. *)
(* check_shape_event(event) at 0x8657c (image B; 0x85fa0 in A; 39 instructions, A has 32) reads g_gone.  When it is
   set, it tail-calls check_shape_done(0).  Otherwise it takes the stream's first line with next_line (an internal
   call; cells &line, &len, &at in its own 48-byte frame), checks its length against strlen(event) and its bytes with
   bcmp, CALLS check_shape_done(at) (A tail-calls it; B keeps its frame across the call and returns with its own
   epilogue at 0x865f8-0x86608), and returns.  B's body has no UBSan trap edge: UBSan is trap mode in this pin, and
   this function does no checked arithmetic and no checked pointer access (frame cells and one global byte), so the
   only `unimp` (0x86614) follows `jal abort` and is reached only after abort returns.  The three abort arms are
   refuted from the contract's functional half.  The walk is generic over the allocator relation ARx (Section c
   below); its Section hypotheses: LAWS, ASTRLEN (W_contract_x.v astrlen_realizes_x), ABCMP (W_sites_x.v
   abcmp_realizes_x), NL (next_line's contract nl_spec_x), CSD (check_shape_done's contract csd_spec_x, W_contract_x.v;
   image B's pb_check_shape_done_x is lib/B/W_check_shape_done.v) and TL (PALib B: pal_env puts errno below
   alloc_ceiling, for aleaf_post_x's errno-view conjunct). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_journal W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require next_line_c.
(* route R: the leaf contract twins (a Theorem Labs lane's W_contract_leaf_xR.v, NAMES.md (sha256 4a0eb3e6fe06; internal record)) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_leaf_xR.
(* The sink-instance guard, after every import (MERGE.md (sha256 0694aca87ccd; internal record) item 3): no sink instance is a hint below, so the
   walk's sink_head is the Section's SK *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
(* The contract cse_spec / CSE_STK / CSE_FRAME is the kit's: lib/B/W_contract.v Section w3, generated from the
   integrated lib/A input a working branch d6225197406 (W3's text of a working branch 3ed7f2a7227, with
   fe77cb0fea2's stream presence premise `OUT <= a < OUT + O`). *)
Definition A_check_shape_event : Z := AF_fr_check_shape_event.
Definition A_check_shape_eventP : Z := BASE + A_check_shape_event.
(* return addresses in check_shape_event: after next_line (0x865c8), strlen (0x865d8), bcmp (0x865ec) and
   check_shape_done (0x865f8) *)
Definition CSE_RET_NL : Z := AF_fr_check_shape_event + 0x4c.
Definition CSE_RET_STRLEN : Z := AF_fr_check_shape_event + 0x5c.
Definition CSE_RET_BCMP : Z := AF_fr_check_shape_event + 0x70.
Definition CSE_RET_CSD : Z := AF_fr_check_shape_event + 0x7c.
(* ---- THE GENERIC WALK (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): check_shape_event over any allocator relation
   ARx with its laws, stated as W_contract_x.cse_spec_x.  The Section hypotheses beyond the AR walk's: PST / ARx / hl /
   LAWS (the generic relation) and HP0 (the unit's hidden-head set is empty in every ARx state: fuzz_reply calls no
   poison routine; a Theorem Labs lane's ruling).  This walk reads no heap block, so HP0 goes unused and is not in the theorem.
   The callees are the _x contracts, check_shape_done's included (CSD, csd_spec_x over the same ARx). ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis NL : nl_spec_x B PST ARx (BASE + AF_fr_next_line).
Hypothesis CSD : csd_spec_x B PST ARx (BASE + AF_fr_check_shape_done).
(* the allocator instance's library facts: pal_env puts errno in the image, below alloc_ceiling, so every run and call
   of this walk keeps its view (aleaf_post_x's errno conjunct) *)
Hypothesis TL : PALib B.
Let HG0 : gx_ok SEGS B [] := gx_ok_nil SEGS B.
Let RUN := paj_run_x_x B PST ARx LAWS [] HG0 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS [] HG0 0 [].
Local Notation AJG := (ajournal_gx_x SEGS B PST ARx [] 0 []).
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
(* awr_ok_tac is in Reusable.YCbq and in lib/B.YCbq; name each in full (lib/B/W_check_bounded.v). *)
Ltac awr_any := first [ OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.awr_ok_tac
                       | OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.awr_ok_tac ].
(* A run writes only inside its regions' windows, all in [sp - 48, sp) or empty: a byte outside this function's
   stack window keeps the value the previous fact Kprev gives it. *)
Ltac keep_run Kprev UspX :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hno := fresh "Hno" in
  intros a Ha Hno;
  lazymatch goal with |- aview _ _ ?m1 _ = _ =>
  lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict _ ?m0) (mrestrict _ m1) |- _ =>
    rewrite <- (Kprev a Ha Hno);
    apply (aview_kept_out Ev rs _ m0 m1 Hf a Ha);
    let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros (r & Hin & Hr);
    lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite UspX in Hr;
       unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in Hno; lia|]);
    destruct Hin end end.
(* The atom table (the facts the runner decides from).  Atoms 0..31 are the entry registers, 32.. the extras below,
   A_TEXT.. the image.  Every branch of this walk is decided from these or from the contract's functional half; there
   is no trap edge to decide. *)
Definition Bx : sv := SOff 33 0.
(* the frame: the three cells next_line writes (line, len, at), then the saved registers; and g_gone *)
Definition cse_cells : YP09.region := YP09.mkRegion (Some 2%nat) (-48) (-24) (-48) (-24) [].
Definition cse_saved : YP09.region := YP09.mkRegion (Some 2%nat) (-24) 0 (-24) 0 [].
Definition cse_gone : YP09.region := YP09.mkRegion (Some A_g_gone) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition cse_regions : smem := [ cse_cells; cse_saved; cse_gone ].
(* the cells again after next_line: line = g_out (atom 35), len = |event| (36), at = |event| + 1 (34) *)
Definition cse_cells2 : YP09.region := YP09.mkRegion (Some 2%nat) (-48) (-24) (-48) (-24)
[YP09.mkChunk (-48) (CVal 8 (SOff 35 0)); YP09.mkChunk (-40) (CVal 8 (SOff 36 0)); YP09.mkChunk (-32) (CVal 8 (SOff 34 0))].
(* sp: in [2^46, 2^47], 16-aligned; g_gone: 0 or 1; the shadow base *)
Definition cse_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF 0 1 0); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_cse : sstate := mkSS A_check_shape_event sr_atoms cse_regions None cse_facts.
Definition cse_SH : list shent := [].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* atoms 32.. : g_gone, the shadow base, and what next_line leaves in the three cells *)
Definition cse_extra (gone ne OUT : Z) : list word := map (Z_to_bv 64) [gone; SB; ne + 1; OUT; ne].
Lemma cse_entry_x : forall W ly S Hp regs mem md ch gone ne OUT,
afn_pre_x SEGS B ARx CSE_STK ly S Hp W regs mem md ch ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> (gone = 0 \/ gone = 1) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cse_extra gone ne OUT))) ss_cse
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_check_shape_eventP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx cse_SH (Eimg (Ereg regs (cse_extra gone ne OUT))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch gone ne OUT HPRE Mg Rg.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CSE_STK = 8304) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (cse_extra gone ne OUT))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 gone) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Eg : ew E A_g_gone = Z_to_bv 64 (VAL A_g_gone)) by (subst E; apply Eimg_img; unfold A_g_gone, A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 27 ltac:(lia)) as HgR. change (A_OBJ 27) with A_g_gone in HgR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_cse, A_check_shape_eventP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold cse_regions, cse_cells, cse_saved, cse_gone.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB A_g_gone (VAL A_g_gone) Eg) by (pose proof (pa_val_range A_g_gone); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL A_g_gone) 0 1 (SOff 32 0) gone);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact Mg.
+ apply pairwise_disjoint_of_extents. unfold cse_regions, cse_cells, cse_saved, cse_gone, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB A_g_gone (VAL A_g_gone) Eg) by (pose proof (pa_val_range A_g_gone); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HgR. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [cse_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Rg. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cse_SH. constructor.
Qed.
(* Facts about bytes the walk did not write carry over in the aview form. *)
Lemma val_mem_kept : forall H H' (m m' : word -> option byte) a n v,
(forall i, 0 <= i < Z.of_nat n -> aview SEGS H' m' (a + i) = aview SEGS H m (a + i)) ->
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hk Hv k Hlt. rewrite (mbyte_of_aview SEGS H H' m m'); [apply Hv; exact Hlt|]. apply Hk. lia.
Qed.
Lemma ob_at_kept : forall (W W' : world SEGS) m m' x l,
(forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS (w_H W') m' (x + i) = aview SEGS (w_H W) m (x + i)) ->
ob_at W m x l -> ob_at W' m' x l.
Proof. intros W W' m m' x l Hk Hl i Hi. rewrite Hk by exact Hi. exact (Hl i Hi). Qed.
Lemma aregs_preserved_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma sub_mod8 : forall x c, x mod 16 = 0 -> c mod 8 = 0 -> (x - c) mod 8 = 0.
Proof.
intros x c Hx Hc. apply Z.mod_divide in Hx; [|lia]. apply Z.mod_divide in Hc; [|lia]. apply Z.mod_divide; [lia|].
apply Z.divide_sub_r; [|exact Hc]. apply (Z.divide_trans _ 16); [exists 2; reflexivity | exact Hx].
Qed.
(* The stack's shadow is zero: ARx's zero-shadow byte law (YCbqG.ARx_zshadow_byte_law, field alx_zshadow_byte), per
   address of [ly_stk_lo, ly_stk_hi). *)
Lemma range_addressable_stack_x : forall ly S Hp W mem md a len,
ARx ly S Hp W mem md -> ly_stk_lo ly <= a -> a + len <= ly_stk_hi ly -> 0 <= len ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a len.
Proof.
intros ly S Hp W mem md a len HAR Hlo Hhi Hlen x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. exact (alx_zshadow_byte _ _ _ LAWS ly S Hp W mem md x HAR ltac:(lia)).
Qed.
(* Shadow facts about application bytes survive any change above alloc_ceiling. *)
Lemma ra_kept : forall H H' (m m' : word -> option byte) a len lo hi,
alloc_ceiling <= lo -> amem_range a len -> 0 <= a ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (lo <= y < hi) -> aview SEGS H' m' y = aview SEGS H m y) ->
range_addressable (aview SEGS H m) SHADOW_OFF a len -> range_addressable (aview SEGS H' m') SHADOW_OFF a len.
Proof.
intros H H' m m' a len lo hi Hlo Hmr Ha0 Hk Hra x Hx. destruct (Hra x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
destruct (shadow_below_stack lo hi x Hlo (amem_range_in a len x Hmr Ha0 ltac:(lia) ltac:(lia))) as [S1 S2].
rewrite <- Hsv. unfold shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x). apply Hk; assumption.
Qed.
Lemma shv_kept : forall H H' (m m' : word -> option byte) a len lo hi,
alloc_ceiling <= lo -> amem_range a len -> 0 <= a -> 0 < len ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (lo <= y < hi) -> aview SEGS H' m' y = aview SEGS H m y) ->
shadow_hull_vis (aview SEGS H m) a len -> shadow_hull_vis (aview SEGS H' m') a len.
Proof.
intros H H' m m' a len lo hi Hlo Hmr Ha0 Hl Hk Hv sa Hsa.
destruct (shadow_hull_below_stack lo hi a len sa Hlo (amem_range_in a len a Hmr Ha0 ltac:(lia) ltac:(lia))
  (amem_range_in a len (a + len - 1) Hmr Ha0 ltac:(lia) ltac:(lia)) Hsa) as [S1 S2].
rewrite Hk by assumption. exact (Hv sa Hsa).
Qed.
(* image B's image top is 0x5fc000 (W_kit.v pa_img_range) *)
Lemma rom_kept : forall (W : world SEGS) (m m' : word -> option byte) lo hi, 0x5fc000 <= lo ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (lo <= y < hi) -> aview SEGS (w_H W) m' y = aview SEGS (w_H W) m y) ->
rom_view SEGS W m -> rom_view SEGS W m'.
Proof.
intros W m m' lo hi Hlo Hk Hr a Hin. rewrite Hk; [exact (Hr a Hin) | |].
- destruct Hin as (sg & Hsg & _ & Hra). pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HI. lia.
- destruct Hin as (sg & Hsg & _ & Hra). pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hra])) as HI. lia.
Qed.
(* The stream's first line is the event when the stream is the event and its NUL. *)
Lemma nul_split_unique : forall (e ln rest : list byte), e ++ [Z_to_bv 8 0] = ln ++ Z_to_bv 8 0 :: rest ->
~ In (Z_to_bv 8 0) e -> ~ In (Z_to_bv 8 0) ln -> ln = e.
Proof.
induction e as [|x e IH]; intros [|y ln] rest Heq He Hl; cbn in Heq.
- reflexivity.
- injection Heq as Hy _. exfalso. apply Hl. left. symmetry. exact Hy.
- injection Heq as Hx _. exfalso. apply He. left. exact Hx.
- injection Heq as -> Heq. f_equal. apply (IH ln rest Heq); intros H; [apply He | apply Hl]; right; exact H.
Qed.
Lemma first_byte_of_ob : forall W m x e, ob_at W m x (e ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) e ->
first_byte SEGS W m x (Z.of_nat (length e) + 1) 0 (Z.of_nat (length e)).
Proof.
intros W m x e Hob Hnz. split; [lia|]. split.
- intros i Hi. exists (bv_unsigned (nth (Z.to_nat i) e (Z_to_bv 8 0))). split.
  + rewrite (Hob i) by (rewrite length_app; cbn [length]; lia). rewrite app_nth1 by lia. reflexivity.
  + intros H0. apply Hnz. assert (Hn : nth (Z.to_nat i) e (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; rewrite H0; reflexivity).
    rewrite <- Hn. apply nth_In. lia.
- intros _. rewrite (Hob (Z.of_nat (length e))) by (rewrite length_app; cbn [length]; lia).
  rewrite app_nth2 by lia. rewrite Nat2Z.id, Nat.sub_diag. reflexivity.
Qed.
Lemma shv_sub : forall rd x n n', 0 < n' <= n -> 0 <= x -> shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' Hn Hx Hv sa Hsa. apply Hv. split; [lia|].
assert (Hm : shadow_addr (x + n' - 1) <= shadow_addr (x + n - 1)) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (Hd : shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
(* The gone arm's tail call: at check_shape_done's entry the frame is gone, every callee-saved register and ra are
   the entry's, and a0 is the position check_shape_done compares with g_nout. *)
Lemma cse_tail_x : forall W0 regs mem0 md0 ch ly S Hp W ms mdc n,
afn_pre_x SEGS B ARx CSE_STK ly S Hp W0 regs mem0 md0 ch ->
ajournal_x SEGS B PST ARx CSE_STK (spZ regs) [] ly S Hp W0 mem0 md0 [] ly S Hp W (ms_mem ms) mdc 0 ->
ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + AF_fr_check_shape_done)) (ms_mem ms) (seg_rom SEGS) ->
aregs_preserved regs (ms_regs ms) -> getr (ms_regs ms) 1 = getr regs 1 ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (VAL A_g_nout) 8 n ->
(forall a, apresent (w_H W0) mem0 a -> apresent (w_H W) (ms_mem ms) a) ->
(* errno's view at the tail call is the entry's; check_shape_done keeps it (aleaf_post_x's last conjunct) *)
(forall j, 0 <= j < 4 -> aview SEGS (w_H W) (ms_mem ms) (as_errno B + j) = aview SEGS (w_H W0) mem0 (as_errno B + j)) ->
SRr SEGS W (mkCfg ms mdc) (aleaf_post_x B PST ARx CSE_STK regs ly S Hp W0 mem0 md0 (fun _ => True)).
Proof.
intros W0 regs mem0 md0 ch ly S Hp W ms mdc n HPRE HJ Hms HP Hra1 H10 Rn Mn HPRS HERRS.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (P2 : getr (ms_regs ms) 2 = getr regs 2) by (apply (HP 2); unfold acallee_saved; lia).
assert (P3 : getr (ms_regs ms) 3 = getr regs 3) by (apply (HP 3); unfold acallee_saved; lia).
assert (P4 : getr (ms_regs ms) 4 = getr regs 4) by (apply (HP 4); unfold acallee_saved; lia).
assert (P8 : getr (ms_regs ms) 8 = getr regs 8) by (apply (HP 8); unfold acallee_saved; lia).
assert (Hsp : spZ (ms_regs ms) = spZ regs + 0) by (unfold spZ; rewrite P2; lia).
assert (Q1 : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite Hra1; exact Hra).
assert (Q1' : 4096 <= raZ (ms_regs ms)) by (unfold raZ; rewrite Hra1; exact Hra4).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3; exact Hgp).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4; exact Htp).
assert (Qch : achain ly (aview SEGS (w_H W) (ms_mem ms)) (spZ regs + 0) (s0Z (ms_regs ms)) ch).
{ unfold s0Z. rewrite P8. fold (s0Z regs). rewrite Z.add_0_r.
  apply (achain_kept ly (aview SEGS (w_H W0) mem0) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch ltac:(lia) ltac:(lia)).
  intros a Ha. apply G1; [lia | lia]. }
assert (HPRE1 : afn_pre_x SEGS B ARx CSD_STK ly S Hp W (ms_regs ms) (ms_mem ms) mdc ch).
{ eapply (afn_pre_x_at SEGS B PST ARx CSE_STK (spZ regs) [] ly S Hp W0 mem0 md0 [] ly S Hp W (ms_mem ms) mdc 0
  (ms_regs ms) CSD_STK 0 ch HJ Hsp); first [exact Q1 | exact Q1' | exact Q3 | exact Q4 | rewrite Hsp; exact Qch
  | reflexivity | unfold CSD_STK, CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK; lia]. }
rewrite Hms. eapply SRr_mono.
{ exact (CSD W ly S Hp (ms_regs ms) (ms_mem ms) mdc ch n HPRE1 H10 Rn Mn). }
cbv beta. unfold aleaf_post_x. intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & HPR2 & HERR2).
exists regs2, mem2, md2. split; [rewrite Hra1; reflexivity|].
split; [|split; [exact (aregs_preserved_trans _ _ _ HP HP2) | split; [exact I | split; [intros a Ha; apply HPR2, HPRS, Ha |
  intros jj Hjj; rewrite (HERR2 jj Hjj); exact (HERRS jj Hjj)]]]].
rewrite Hsp, Z.add_0_r in HJ2.
pose proof (ajournal_x_sub SEGS B PST ARx LAWS pa_segs_low CSE_STK (spZ regs) [] ly S Hp W0 mem0 md0 [] ly S Hp W (ms_mem ms) mdc 0
  CSD_STK (spZ regs) [] [] ly S Hp W2 mem2 md2 0 HJ HJ2
  ltac:(unfold CSD_STK, CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK; lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ3.
cbn [app] in HJ3. rewrite Z.add_0_r in HJ3. exact HJ3.
Qed.
Theorem pb_check_shape_event_x : cse_spec_x B PST ARx A_check_shape_eventP.
Proof.
intros W ly S Hp regs mem md ch EV e gone O OUT ob HPRE H10 Hnz Hev Rev0 Revc Rev1 Rev2 HevOff Hmr Hmr8 Hrae Hhve Htail Hrom
Mg Rg Mno Mout Hlen Hob Hout HF.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
set (ne := Z.of_nat (length e)) in *.
destruct (cse_entry_x W ly S Hp regs mem md ch gone ne OUT HPRE Mg Rg) as [HS SHOK].
assert (HJ : AJG CSE_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp W mem md 0)
by (apply ajournal_gx_nil_x; exact (ajournal_x_init SEGS B PST ARx CSE_STK [] ly S Hp W regs mem md ch HPRE)).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CSE_STK = 8304) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
remember (Eimg (Ereg regs (cse_extra gone ne OUT))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E1 : ew E 1 = getr regs 1) by exact (EEo 1%nat 1%bv eq_refl).
assert (E2 : ew E 2 = getr regs 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = getr regs 3) by exact (EEo 3%nat 3%bv eq_refl).
assert (E4 : ew E 4 = getr regs 4) by exact (EEo 4%nat 4%bv eq_refl).
assert (E10 : ew E 10 = Z_to_bv 64 EV) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 gone) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (ne + 1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 OUT) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 ne) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cse_extra gone ne OUT)) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_check_shape_eventP) with (Z_to_bv 64 A_check_shape_eventP).
unfold A_check_shape_eventP, A_check_shape_event.
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; awr_any; exact Usp. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* beqz taken, g_gone is clear: the stream holds exactly the event's line *)
assert (Hg0 : gone = 0).
{ rewrite branch_eq_U, (U_atom E 32 gone E32), U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia. }
destruct HF as [[Hg1 _] | [_ Hobe]]; [lia|].
assert (HO : O = ne + 1) by (rewrite <- Hlen, Hobe, length_app; cbn [length]; unfold ne; lia).
destruct (Hout ltac:(lia)) as (Rout0 & Rout1 & Rb32 & Hmro8 & Hrao & Hhvo & Hvo).
assert (Hmro : amem_range OUT O) by (unfold amem_range in *; lia).
(* run to next_line *)
paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AF_fr_next_line. { apply awr_ok_x_of0; awr_any; exact Usp. }
apply ajournal_gx_nil_x in HJ.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (Usp1 : spZ (ms_regs ms0) = spZ regs - 48).
{ unfold spZ. rewrite Q2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSE_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
  assert (HQ1 : aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
  { lazymatch type of HFr0 with frame_of ?Ev ?rs _ _ => apply (aview_kept_out Ev rs (w_H W) _ _ HFr0 a Ha) end.
    intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia|]).
    destruct Hin. }
  rewrite HQ1. lazymatch type of HFr with frame_of ?Ev ?rs _ _ => apply (aview_kept_out Ev rs (w_H W) _ _ HFr a Ha) end.
  intros (r & Hin & Hr). cbn [ss_mem ss_cse cse_regions In] in Hin. unfold cse_cells, cse_saved, cse_gone in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia|]).
  destruct Hin. }
(* the cell `at` holds 0 (the prologue's `sd zero,16(sp)`) *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 0 (ss_mem ssx) cse_cells) in
  pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg0 end.
cbn [ms_mem restrict] in HRg0.
pose proof (field_of_region E _ 2 (spZ regs) _ _ _ _ _ (-32) 8 (SLit 0) 0 HRg0 Usp ltac:(cbn; tauto) ltac:(reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as Vat.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR0 & _).
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
assert (HPREn : afn_pre_x SEGS B ARx NL_STK ly S Hp W (ms_regs ms0) (ms_mem ms0) mdc []).
{ eapply (afn_pre_x_at SEGS B PST ARx CSE_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp W (ms_mem ms0) mdc 0 (ms_regs ms0) NL_STK (-48) []
  HJ ltac:(rewrite Usp1; lia)); first
  [ reflexivity | unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK; lia
  | rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | unfold raZ; rewrite Q1; rewrite unsigned_lit_small by lia; lia
  | rewrite Q3, E3; exact Hgp | rewrite Q4, E4; exact Htp
  | apply achain_low; unfold s0Z; rewrite Q8, E10; rewrite unsigned_lit_small by lia; lia ]. }
eapply SRr_bind.
{ eapply (NL W ly S Hp (ms_regs ms0) (ms_mem ms0) mdc [] 48 (spZ regs - 32) (spZ regs - 48) (spZ regs - 40) 0 O OUT ob HPREn).
  all: try lia. all: try (rewrite Usp1; lia). all: try reflexivity. all: try exact Hlen.
  - intros a Ha. apply HPR0. rewrite Usp1 in Ha. unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK. lia.
  - rewrite Q10, Usp. reflexivity.
  - rewrite Q11, Usp. reflexivity.
  - rewrite Q12, Usp. reflexivity.
  - apply sub_mod8; [exact Hal16 | reflexivity].
  - apply sub_mod8; [exact Hal16 | reflexivity].
  - apply sub_mod8; [exact Hal16 | reflexivity].
  - apply (range_addressable_stack_x ly S Hp W (ms_mem ms0) mdc); [exact (proj1 HJ) | unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in *; lia | lia | lia].
  - apply (range_addressable_stack_x ly S Hp W (ms_mem ms0) mdc); [exact (proj1 HJ) | unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in *; lia | lia | lia].
  - apply (range_addressable_stack_x ly S Hp W (ms_mem ms0) mdc); [exact (proj1 HJ) | unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in *; lia | lia | lia].
  - replace (spZ regs - 32) with (spZ regs + -32) by lia. exact Vat.
  - apply (val_mem_kept (w_H W) (w_H W) mem (ms_mem ms0)); [|exact Mno].
    intros i Hi. pose proof (pa_obj_img 12 ltac:(lia)) as HnoR. change (A_OBJ 12) with A_g_nout in HnoR.
    pose proof (pa_val_range A_g_nout). apply KEEP0; [lia|]. unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in *. lia.
  - apply (val_mem_kept (w_H W) (w_H W) mem (ms_mem ms0)); [|exact Mout].
    intros i Hi. pose proof (pa_obj_img 29 ltac:(lia)) as HoR. change (A_OBJ 29) with A_g_out in HoR.
    pose proof (pa_val_range A_g_out). apply KEEP0; [lia|]. unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in *. lia.
  - apply (ob_at_kept W W mem (ms_mem ms0)); [|exact Hob]. intros i Hi.
    destruct (Hvo (OUT + i) ltac:(lia)) as [_ Hn]. apply KEEP0; [lia | exact Hn].
  - intros _. split; [exact Rout0|]. split; [lia|]. split; [exact Rb32|].
    intros a Ha. destruct (Hvo a ltac:(lia)) as [_ Hn]. rewrite Usp1.
    replace (spZ regs - 48 - NL_STK) with (spZ regs - CSE_STK) by (unfold CSE_STK, CSE_FRAME; lia). lia.
  - intros _. split; [rewrite Hobe; cbn [Z.to_nat skipn]; apply in_or_app; right; left; reflexivity|].
    assert (KLO : forall y, 0 <= y < 2 ^ 64 -> ~ (spZ regs - CSE_STK <= y < spZ regs) ->
      aview SEGS (w_H W) (ms_mem ms0) y = aview SEGS (w_H W) mem y) by exact KEEP0.
    assert (HLO : alloc_ceiling <= spZ regs - CSE_STK) by lia.
    split; [exact Hmro8|].
    split; [exact (ra_kept _ _ _ _ OUT O _ _ HLO Hmro ltac:(lia) KLO Hrao)|].
    split; [exact (shv_kept _ _ _ _ OUT O _ _ HLO Hmro ltac:(lia) ltac:(lia) KLO Hhvo)|].
    exact (rom_kept W mem (ms_mem ms0) (spZ regs - CSE_STK) (spZ regs) ltac:(lia) KLO Hrom).
}
cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJn & HP2 & HWW & HPn & HFRn & Mno2 & Mout2 & Hob2 & HARM).
subst W2.
destruct HARM as [(HA0 & _) | (ln & _ & Hfl & R10n & Vat2 & Vln2 & Vlen2)]; [lia|].
assert (Hln : ln = e).
{ destruct Hfl as (rest & Hsk & Hnz'). rewrite Hobe in Hsk. cbn [Z.to_nat skipn] in Hsk. exact (nul_split_unique e ln rest Hsk Hnz Hnz'). }
subst ln. fold ne in Vat2, Vlen2. rewrite Z.add_0_r in Vln2. replace (0 + ne + 1) with (ne + 1) in Vat2 by lia.
(* next_line's journal inside this function's *)
assert (HJx : AJG CSE_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp W (ms_mem ms0) mdc 0)
  by (apply ajournal_gx_nil_x; exact HJ).
rewrite Usp1 in HJn, HFRn.
pose proof (ajournal_gx_sub_x SEGS B PST ARx LAWS Hsegs [] CSE_STK (spZ regs) 0 [] [] ly S Hp W mem md [] ly S Hp W (ms_mem ms0) mdc 0
  NL_STK (spZ regs - 48) 48 (nl_cells (spZ regs - 32) (spZ regs - 48) (spZ regs - 40)) [] [] ly S Hp W mem2 md2 0 HJx HJn
  ltac:(unfold CSE_STK, CSE_FRAME; lia) ltac:(lia) ltac:(lia)) as HJ2x.
assert (HJ2 : ajournal_x SEGS B PST ARx CSE_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp W mem2 md2 0).
{ apply ajournal_gx_nil_x. replace 0 with (0 + 0) at 4 by lia. change ([] : list (Z * Z)) with ([] ++ [] : list (Z * Z)) at 4.
  apply HJ2x.
  - intros a (r & Hin & Hr). left. cbn [nl_cells In] in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK; lia.
  - apply gx_ok_nil.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
clear HJ2x HJx.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR2 & _).
destruct HJn as (_ & _ & _ & HXOn).
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSE_STK <= a < spZ regs) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. rewrite HFRn; [apply KEEP0; assumption | exact Ha | unfold CSE_STK, CSE_FRAME in Hno; lia |].
  intros (r & Hin & Hr). cbn [nl_cells In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in Hno; lia. }
(* back in check_shape_event: keep the saved registers, reseat the three cells *)
jafter_call_keep_pi HS 37%nat regs2 (mrestrict (w_H W) mem2) HP2 [1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply HXOn; [lia|].
    intros (r & Hin & Hr). cbn [nl_cells In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
  - intros a Ha _. apply (apresent_writable SEGS). apply HPR2. unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 37 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 37)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs (cse_extra gone ne OUT)) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (UspA : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by (cbv; lia); exact Usp).
apply (st_ok_pi_add_region Ea _ _ cse_cells2) in HS; [| reflexivity | | ].
2: { unfold region_ok, cse_cells2. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst].
  cbn [base_val]. rewrite UspA. split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). apply HPR2. unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK. lia.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val SEGS Ea _ (spZ regs) (-48) 8 (SOff 35 0) OUT);
      [cbn [sv_denot]; rewrite OLDa by (cbv; lia); rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      replace (spZ regs + -48) with (spZ regs - 48) by lia. exact Vln2.
    + apply (chunk_ok_val SEGS Ea _ (spZ regs) (-40) 8 (SOff 36 0) ne);
      [cbn [sv_denot]; rewrite OLDa by (cbv; lia); rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      replace (spZ regs + -40) with (spZ regs - 40) by lia. exact Vlen2.
    + apply (chunk_ok_val SEGS Ea _ (spZ regs) (-32) 8 (SOff 34 0) (ne + 1));
      [cbn [sv_denot]; rewrite OLDa by (cbv; lia); rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      replace (spZ regs + -32) with (spZ regs - 32) by lia. exact Vat2. }
2: { apply all_disjoint_of_extents. unfold cse_cells2, extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi map ss_mem].
  cbn [base_val]. rewrite UspA. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. lia. }
assert (SHOK2 : sh_ok SEGS Bx cse_SH Ea (mrestrict (w_H W) mem2)) by (unfold sh_ok, cse_SH; constructor).
rewrite Q1.
prreg HS (10%bv : bv 5) R10a.
assert (F41 : ew Ea 41 = Z_to_bv 64 1) by (rewrite <- R10a; exact R10n).
assert (HLO : alloc_ceiling <= spZ regs - CSE_STK) by lia.
apply ajournal_gx_nil_x in HJ2.
paj_run_tok_x RUN HS HJ2 SHOK2 Bspan. { apply awr_ok_x_of0; awr_any; exact UspA. }
psrr_branch_tok RUN BR HS SHOK2 Bspan.
+ (* next_line returned 0: impossible, it found the event's line *)
  exfalso. rewrite branch_eq_U, (U_atom Ea 41 1 F41), U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0. lia.
+ (* strlen(event) *)
  clear Hc0. paj_run_tok_x RUN HS HJ2 SHOK2 Bspan. { apply awr_ok_x_of0; awr_any; exact UspA. }
  apply ajournal_gx_nil_x in HJ2.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSE_STK <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem a).
  { assert (KEEP15 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSE_STK <= a < spZ regs) ->
      aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a) by keep_run KEEP1 UspA.
    keep_run KEEP15 UspA. }
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
  prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10.
  assert (UspT : spZ (ms_regs ms2) = spZ regs - 48).
  { unfold spZ. rewrite P2, UspA. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR2b & _).
  eapply SRr_bind.
  { eapply (aj_strlen_at_x B PST ARx LAWS _ ASTRLEN W (ms_regs ms2) (ms_mem ms2) CSE_STK (spZ regs) ([] : list (Z * Z))
      ly S Hp W mem md ([] : list (Z * Z)) ly S Hp _ 0 EV ne (-48) (Z_to_bv 64 (BASE + CSE_RET_STRLEN)) HJ2).
    - rewrite P10, OLDa by (cbv; lia). exact E10.
    - exact Rev0.
    - lia.
    - exact Rev2.
    - exact Rev1.
    - rewrite UspT. lia.
    - reflexivity.
    - lia.
    - unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK. lia.
    - rewrite P3, OLDa by (cbv; lia). exact (eq_trans E3 Hgp).
    - rewrite P4, OLDa by (cbv; lia). exact (eq_trans E4 Htp).
    - exact P1.
    - apply ret_ok_codeptr_v; [unfold CSE_RET_STRLEN, AF_fr_check_shape_event; lia | reflexivity].
    - apply first_byte_of_ob; [|exact Hnz]. apply (ob_at_kept W W mem (ms_mem ms2)); [|exact Hev].
      intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. fold ne in Hi. apply KEEP2; [lia|]. apply HevOff. lia.
    - intros a Ha. split.
      + rewrite KEEP2 by (try lia; apply HevOff; lia). replace a with (EV + (a - EV)) by lia.
        rewrite (Hev (a - EV)) by (rewrite length_app; cbn [length]; fold ne; lia). discriminate.
      + rewrite UspT. pose proof (HevOff a ltac:(lia)). unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in *. lia.
    - intros a Ha [HA HB]. apply (HevOff a Ha). unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in *. lia.
    - exact Hmr.
    - exact Hmr8.
    - exact (ra_kept _ _ _ _ EV (ne + 1) _ _ HLO Hmr ltac:(lia) KEEP2 Hrae).
    - exact (shv_kept _ _ _ _ EV (ne + 1) _ _ HLO Hmr ltac:(lia) ltac:(lia) KEEP2 Hhve).
    - intros a Ha. destruct (Htail a Ha) as [Hv Hn]. rewrite KEEP2; [exact Hv | lia | exact Hn].
    - exact (rom_kept W mem (ms_mem ms2) (spZ regs - CSE_STK) (spZ regs) ltac:(lia) KEEP2 Hrom). }
  cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hlen3 & Hfr3 & Hpres3).
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR3 & _).
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSE_STK <= a < spZ regs) ->
    aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hno. rewrite Hfr3; [apply KEEP2; assumption | exact Ha |].
    unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in *. lia. }
  jafter_call_keep_pi HS 53%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1]%nat HS3.
  match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil];
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite UspA.
    - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; unfold ESTACK in *; lia.
    - intros a Ha _. apply (apresent_writable SEGS). apply HPR3. unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK. lia.
    - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr3; unfold ESTACK in *; lia.
    - intros a Ha _. apply (apresent_writable SEGS). apply HPR3. unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  remember (havoc Ea 53 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
  assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
  assert (OLDb : forall m, (m < 53)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
  assert (HAEb : env_agree 32 (Ereg regs (cse_extra gone ne OUT)) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
  clear HEb.
  assert (UspB : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by (cbv; lia); exact UspA).
  assert (SHOK3 : sh_ok SEGS Bx cse_SH Eb (mrestrict (w_H W) mem3)) by (unfold sh_ok, cse_SH; constructor).
  prreg HS (10%bv : bv 5) R10c.
  assert (F57 : ew Eb 57 = Z_to_bv 64 ne) by (rewrite <- R10c; exact Hlen3).
  assert (F36 : ew Eb 36 = Z_to_bv 64 ne) by (rewrite OLDb, OLDa by (cbv; lia); exact E36).
  apply ajournal_gx_nil_x in HJ3.
  paj_run_tok_x RUN HS HJ3 SHOK3 Bspan. { apply awr_ok_x_of0; awr_any; exact UspB. }
  psrr_branch_tok RUN BR HS SHOK3 Bspan.
  * (* strlen(event) <> len: impossible, both are |e| *)
    exfalso. rewrite branch_ne_U, (U_atom Eb 36 ne F36), (U_atom Eb 57 ne F57) in Hc0 by lia.
    rewrite Z.eqb_refl in Hc0. discriminate.
  * (* bcmp(line, event, len) *)
    clear Hc0. paj_run_tok_x RUN HS HJ3 SHOK3 Bspan. { apply awr_ok_x_of0; awr_any; exact UspB. }
    assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSE_STK <= a < spZ regs) ->
      aview SEGS (w_H W) (ms_mem ms4) a = aview SEGS (w_H W) mem a).
    { assert (KEEP35 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSE_STK <= a < spZ regs) ->
        aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a) by keep_run KEEP3 UspB.
      keep_run KEEP35 UspB. }
    pmkst HS.
    prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3.
    prreg HS (4%bv : bv 5) T4. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
    assert (UspT4 : spZ (ms_regs ms4) = spZ regs - 48).
    { unfold spZ. rewrite T2, UspB. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
    eapply SRr_bind.
    { eapply (aj_bcmp_gx_at_x B PST ARx LAWS (SIGMA WS_bcmp) ABCMP [] 0 [] W (ms_regs ms4) (ms_mem ms4) CSE_STK (spZ regs)
        ([] : list (Z * Z)) ly S Hp W mem md ([] : list (Z * Z)) ly S Hp _ 0 OUT EV ne (-48) (Z_to_bv 64 (BASE + CSE_RET_BCMP))
        HG0 ltac:(reflexivity) HJ3).
      - rewrite T10, OLDb, OLDa by (cbv; lia). exact E35.
      - rewrite T11, OLDb, OLDa by (cbv; lia). exact E10.
      - rewrite T12. exact F36.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - rewrite UspT4. lia.
      - reflexivity.
      - lia.
      - unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK. lia.
      - rewrite T3, OLDb, OLDa by (cbv; lia). exact (eq_trans E3 Hgp).
      - rewrite T4, OLDb, OLDa by (cbv; lia). exact (eq_trans E4 Htp).
      - exact T1.
      - apply ret_ok_codeptr_v; [unfold CSE_RET_BCMP, AF_fr_check_shape_event; lia | reflexivity].
      - intros a Ha. destruct (Hvo a ltac:(lia)) as [Hv Hn]. split; [rewrite KEEP4; [exact Hv | lia | exact Hn]|].
        rewrite UspT4. unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in *. lia.
      - intros a Ha. split.
        + rewrite KEEP4 by (try lia; apply HevOff; lia). replace a with (EV + (a - EV)) by lia.
          rewrite (Hev (a - EV)) by (rewrite length_app; cbn [length]; fold ne; lia). discriminate.
        + rewrite UspT4. pose proof (HevOff a ltac:(lia)). unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in *. lia.
      - intros a Ha [HA HB]. destruct (Hvo a ltac:(lia)) as [_ Hn]. apply Hn. unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in *. lia.
      - intros a Ha [HA HB]. apply (HevOff a ltac:(lia)). unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in *. lia.
      - unfold amem_range in *. lia.
      - unfold amem_range in *. lia.
      - eapply range_addressable_sub; [exact (ra_kept _ _ _ _ OUT O _ _ HLO Hmro ltac:(lia) KEEP4 Hrao) | lia | lia].
      - intros Hpn. apply (shv_sub _ OUT O ne); [lia | lia | exact (shv_kept _ _ _ _ OUT O _ _ HLO Hmro ltac:(lia) ltac:(lia) KEEP4 Hhvo)].
      - eapply range_addressable_sub; [exact (ra_kept _ _ _ _ EV (ne + 1) _ _ HLO Hmr ltac:(lia) KEEP4 Hrae) | lia | lia].
      - intros Hpn. apply (shv_sub _ EV (ne + 1) ne); [lia | lia | exact (shv_kept _ _ _ _ EV (ne + 1) _ _ HLO Hmr ltac:(lia) ltac:(lia) KEEP4 Hhve)]. }
    cbv beta. intros W4 c4 Hwle4 (-> & regs4 & mem4 & md4 & v & -> & HJ4 & HP4 & Hv & Hcmp & Hfr4 & Hpres4).
    (* the line is the event: bcmp returns 0 *)
    assert (Hv0 : v = w64 0).
    { apply Hcmp. intros i Hi.
      rewrite KEEP4 by (try lia; destruct (Hvo (OUT + i) ltac:(lia)) as [_ Hn]; exact Hn).
      rewrite KEEP4 by (try lia; apply HevOff; lia).
      rewrite (Hob i) by lia. rewrite (Hev i) by (rewrite length_app; cbn [length]; fold ne; lia).
      rewrite Hobe. rewrite app_nth1 by lia. reflexivity. }
    pose proof HJ4 as HJ4a. apply ajournal_gx_nil_x in HJ4a.
    pose proof HJ4a as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR4 & _). clear HJ4a.
    assert (KEEP5 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSE_STK <= a < spZ regs) ->
      aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem a).
    { intros a Ha Hno. rewrite Hfr4; [apply KEEP4; assumption | exact Ha |].
      unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in *. lia. }
    jafter_call_keep_pi HS 69%nat regs4 (mrestrict (w_H W) mem4) HP4 [0; 1]%nat HS4.
    match type of HS4 with ?ty -> _ => assert (HRK : ty); [|specialize (HS4 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil];
      split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite UspB.
      - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr4; unfold ESTACK in *; lia.
      - intros a Ha _. apply (apresent_writable SEGS). apply HPR4. unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK. lia.
      - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr4; unfold ESTACK in *; lia.
      - intros a Ha _. apply (apresent_writable SEGS). apply HPR4. unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK. lia. }
    clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
    remember (havoc Eb 69 (map (getr regs4) CLOB)) as Ec eqn:HEc in HS.
    assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEIb | cbv; lia]).
    assert (OLDc : forall m, (m < 69)%nat -> ew Ec m = ew Eb m) by (intros m Hm; rewrite HEc; apply YN3v.ew_havoc_old; exact Hm).
    assert (HAEc : env_agree 32 (Ereg regs (cse_extra gone ne OUT)) Ec) by (rewrite HEc; apply env_agree_havoc_ge; [cbv; lia | exact HAEb]).
    clear HEc.
    assert (UspC : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLDc by (cbv; lia); exact UspB).
    assert (SHOK4 : sh_ok SEGS Bx cse_SH Ec (mrestrict (w_H W) mem4)) by (unfold sh_ok, cse_SH; constructor).
    prreg HS (10%bv : bv 5) R10d.
    assert (F73 : ew Ec 73 = Z_to_bv 64 0) by (rewrite <- R10d, Hv, Hv0; reflexivity).
    paj_run_tok_x RUN HS HJ4 SHOK4 Bspan. { apply awr_ok_x_of0; awr_any; exact UspC. }
    psrr_branch_tok RUN BR HS SHOK4 Bspan.
    -- (* bcmp <> 0: impossible *)
       exfalso. rewrite branch_ne_U, (U_atom Ec 73 0 F73), U_lit in Hc0 by lia. discriminate.
    -- (* the call check_shape_done(at), at = |e| + 1 = g_nout; B keeps its frame across it *)
       clear Hc0. paj_run_to_tok_x RUNTO HS HJ4 SHOK4 Bspan AF_fr_check_shape_done. { apply awr_ok_x_of0; awr_any; exact UspC. }
       assert (KEEP6 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSE_STK <= a < spZ regs) ->
         aview SEGS (w_H W) (ms_mem ms6) a = aview SEGS (w_H W) mem a).
       { assert (KEEP55 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSE_STK <= a < spZ regs) ->
           aview SEGS (w_H W) (ms_mem ms5) a = aview SEGS (w_H W) mem a) by keep_run KEEP5 UspC.
         keep_run KEEP55 UspC. }
       pmkst HS.
       prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3.
       prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10.
       assert (UspD : spZ (ms_regs ms6) = spZ regs - 48).
       { unfold spZ. rewrite R2, UspC. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
       assert (R10' : getr (ms_regs ms6) 10 = w64 (ne + 1)) by (rewrite R10, OLDc, OLDb, OLDa by (cbv; lia); exact E34).
       assert (Mno6 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms6)) (VAL A_g_nout) 8 (ne + 1)).
       { rewrite <- HO. apply (val_mem_kept (w_H W) (w_H W) mem (ms_mem ms6)); [|exact Mno].
         intros i Hi. pose proof (pa_obj_img 12 ltac:(lia)) as HnoR. change (A_OBJ 12) with A_g_nout in HnoR.
         pose proof (pa_val_range A_g_nout). apply KEEP6; [lia|]. unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in *. lia. }
       lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc6 := mdq) in * end.
       apply ajournal_gx_nil_x in HJ4.
       assert (HPREc : afn_pre_x SEGS B ARx CSD_STK ly S Hp W (ms_regs ms6) (ms_mem ms6) mdc6 []).
       { eapply (afn_pre_x_at SEGS B PST ARx CSE_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp W (ms_mem ms6) mdc6 0 (ms_regs ms6) CSD_STK (-48) []
         HJ4 ltac:(rewrite UspD; lia)); first
         [ reflexivity | unfold CSD_STK, CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK; lia
         | rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]
         | unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia
         | rewrite R3, OLDc, OLDb, OLDa by (cbv; lia); exact (eq_trans E3 Hgp)
         | rewrite R4, OLDc, OLDb, OLDa by (cbv; lia); exact (eq_trans E4 Htp)
         | apply achain_low; unfold s0Z; rewrite R8, OLDc, OLDb, OLDa by (cbv; lia); rewrite E10;
           rewrite unsigned_lit_small by lia; lia ]. }
       eapply SRr_bind.
       { exact (CSD W ly S Hp (ms_regs ms6) (ms_mem ms6) mdc6 [] (ne + 1) HPREc R10' ltac:(lia) Mno6). }
       cbv beta. intros W7 c7 Hwle7 (regs7 & mem7 & md7 & -> & HJc & HPc & _ & HPRc & HERRc).
       rewrite UspD in HJc.
       pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & G7 & _).
       (* check_shape_done's journal inside this function's *)
       pose proof (ajournal_x_sub SEGS B PST ARx LAWS pa_segs_low CSE_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp W (ms_mem ms6) mdc6 0
         CSD_STK (spZ regs - 48) [] [] ly S Hp W7 mem7 md7 0 HJ4 HJc
         ltac:(unfold CSD_STK, CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK; lia) ltac:(lia)
         ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ5.
       cbn [app] in HJ5. rewrite Z.add_0_r in HJ5.
       pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR5 & _).
       (* back in check_shape_event after the call: the cells and the saved registers are outside check_shape_done's
          window [sp - 64, sp - 48) *)
       jafter_call_keep_pi HS 85%nat regs7 (mrestrict (w_H W7) mem7) HPc [0; 1]%nat HS5.
       match type of HS5 with ?ty -> _ => assert (HRK : ty); [|specialize (HS5 HRK); clear HRK] end.
       { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil];
         split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite UspC.
         - intros a Ha. apply (mbyte_of_aview SEGS). apply G7; unfold CSD_STK, ESTACK in *; lia.
         - intros a Ha _. apply (apresent_writable SEGS). apply HPR5. unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK. lia.
         - intros a Ha. apply (mbyte_of_aview SEGS). apply G7; unfold CSD_STK, ESTACK in *; lia.
         - intros a Ha _. apply (apresent_writable SEGS). apply HPR5. unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK. lia. }
       clear HS. rewrite <- restrict_mkst_fx in HS5. rename HS5 into HS.
       remember (havoc Ec 85 (map (getr regs7) CLOB)) as Ed eqn:HEd in HS.
       assert (HEId : img_env VAL A_LIM Ed) by (rewrite HEd; apply img_env_havoc; [exact HEIc | cbv; lia]).
       assert (OLDd : forall m, (m < 85)%nat -> ew Ed m = ew Ec m) by (intros m Hm; rewrite HEd; apply YN3v.ew_havoc_old; exact Hm).
       assert (HAEd : env_agree 32 (Ereg regs (cse_extra gone ne OUT)) Ed) by (rewrite HEd; apply env_agree_havoc_ge; [cbv; lia | exact HAEc]).
       clear HEd.
       assert (UspE : bv_unsigned (ew Ed 2) = spZ regs) by (rewrite OLDd by (cbv; lia); exact UspC).
       assert (SHOK5 : sh_ok SEGS Bx cse_SH Ed (mrestrict (w_H W7) mem7)) by (unfold sh_ok, cse_SH; constructor).
       rewrite R1.
       (* the epilogue: restore ra, s0, s1, pop the frame, return *)
       apply ajournal_gx_nil_x in HJ5.
       paj_run_tok_x RUN HS HJ5 SHOK5 Bspan. { apply awr_ok_x_of0; awr_any; exact UspE. }
       pose proof (proj1 (pal_env B TL)) as HERRB.
       prreg HS (1%bv : bv 5) R1f.
       eapply (RET W7 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
       intros mat'. unfold aleaf_post_x.
       lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
       split; [cbn [ms_regs]; rewrite R1f; rewrite OLDd, OLDc, OLDb, OLDa by (cbv; lia); rewrite E1, Hra; reflexivity|].
       split; [|split; [|split; [exact I | split; [intros a Ha; cbn [ms_mem]; pres_chain |]]]].
       3: { intros jj Hjj. cbn [ms_mem].
            assert (Hea : 0 <= as_errno B + jj < 2 ^ 64) by lia.
            assert (Heb : as_errno B + jj < spZ regs - CSE_STK)
              by (unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK; lia).
            (* the epilogue run writes only inside its regions' windows, all in this frame *)
            lazymatch goal with |- aview _ _ ?m1 _ = _ =>
            lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict _ mem7) (mrestrict _ m1) |- _ =>
              rewrite (aview_kept_out Ev rs _ mem7 m1 Hf (as_errno B + jj) Hea) end end.
            2: { let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
                 intros (r & Hin & Hr);
                 lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
                 cbn [In] in Hin;
                 repeat (destruct Hin as [<- | Hin];
                   [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?UspE in Hr;
                    unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in Heb; lia|]);
                 destruct Hin. }
            rewrite (HERRc jj Hjj). apply KEEP6; [exact Hea|].
            unfold CSE_STK, CSE_FRAME, NL_STK, NL_FRAME, ESTACK in *. lia. }
       ++ cbn [ms_mem]. apply (ajournal_x_materialize SEGS B PST ARx LAWS Hsegs). apply ajournal_gx_nil_x. exact HJ5.
       ++ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs (cse_extra gone ne OUT) HS); [exact HAEd | vm_compute; reflexivity] end.
- (* beqz not taken, g_gone is set: the controller went, nothing was read, and check_shape_done(0) passes *)
assert (Hg1 : gone = 1).
{ rewrite branch_eq_U, (U_atom E 32 gone E32), U_lit in Hc by lia. apply Z.eqb_neq in Hc. lia. }
destruct HF as [[_ HO0] | [Hg0 _]]; [|lia]. rewrite HO0 in Mno.
paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AF_fr_check_shape_done. { apply awr_ok_x_of0; awr_any; exact Usp. }
pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Hms. cbn [ss_pc] in Hms.
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
  assert (HQ1 : aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
  { lazymatch type of HFr0 with frame_of ?Ev ?rs _ _ => apply (aview_kept_out Ev rs (w_H W) _ _ HFr0 a Ha) end.
    intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia|]).
    destruct Hin. }
  rewrite HQ1. lazymatch type of HFr with frame_of ?Ev ?rs _ _ => apply (aview_kept_out Ev rs (w_H W) _ _ HFr a Ha) end.
  intros (r & Hin & Hr). cbn [ss_mem ss_cse cse_regions In] in Hin. unfold cse_cells, cse_saved, cse_gone in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia|]).
  destruct Hin. }
apply ajournal_gx_nil_x in HJ.
eapply (cse_tail_x W regs mem md ch ly S Hp W ms0 _ 0 HPRE HJ).
+ exact Hms.
+ eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (cse_extra gone ne OUT) HS); [exact HAE | vm_compute; reflexivity].
+ rewrite R1, E1. reflexivity.
+ rewrite R10. reflexivity.
+ lia.
+ apply (val_mem_kept (w_H W) (w_H W) mem (ms_mem ms0)); [|exact Mno].
  intros i Hi. pose proof (pa_obj_img 12 ltac:(lia)) as HnoR. change (A_OBJ 12) with A_g_nout in HnoR.
  pose proof (pa_val_range A_g_nout) as HnoV.
  apply KEEP; [lia|]. lia.
+ intros a Ha. pres_chain.
+ pose proof (proj1 (pal_env B TL)) as HERRB. pose proof asan_consts as (C1x & _ & _ & _ & C5x).
  intros jj Hjj. apply KEEP; lia.
Qed.

(* ---- route R (group G7-leaf-AB, for a Theorem Labs lane's top_x at R): pb_check_shape_event_x at a world relation R, a LIFT
   with no re-proof.  The strict SRr run becomes SRrG SEGS R by SRr_SRrG (WLE_R), and the post's journal
   (aleaf_post_x -> a Theorem Labs lane's aleaf_post_xR) goes to R by ajournal_xR_mono; W_contract_leaf_xR.v
   cse_spec_xR_of_x is those two steps.  The callees (strlen, bcmp, next_line, check_shape_done) stay at their strict
   contracts (ASTRLEN, ABCMP, NL, CSD). ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Theorem pb_check_shape_event_xR : cse_spec_xR B PST ARx R A_check_shape_eventP.
Proof. apply (cse_spec_xR_of_x B PST ARx R WLE_R). exact pb_check_shape_event_x. Qed.
End wR.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_check_shape_event's statement is the AR
   walk's, byte-identical, now a corollary of pb_check_shape_event_x at ARx := ARi0 (cgif's AR with the head set
   empty), PST := [].  Its Section takes LX0 (the laws at ARi0, a Theorem Labs lane's ruling (a)) in place of LAWS: the
   instance builds it once, W_journal_x.AR_laws_x_ARi0 (YCbqG.AR_laws_x_of_AR ..).  The callees' AR contracts become
   the generic walk's hypotheses by the kit's bridges W_contract_x astrlen_realizes_x_of_AR0 / nl_spec_x_of_AR0 /
   csd_spec_x_of_AR0 and W_sites_x abcmp_realizes_x_of_AR0; the conclusion by W_contract_x cse_spec_x_AR0. ---- *)
Section cAR.
Variable B : asyms.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA WS_bcmp).
Hypothesis NL : nl_spec B (BASE + AF_fr_next_line).
Hypothesis CSD : csd_spec B (BASE + AF_fr_check_shape_done).
Hypothesis TL : PALib B.
Theorem pb_check_shape_event : cse_spec B A_check_shape_eventP.
Proof.
apply cse_spec_x_AR0.
exact (pb_check_shape_event_x B [] (ARi0 SEGS B) LX0 (astrlen_realizes_x_of_AR0 B _ ASTRLEN)
  (abcmp_realizes_x_of_AR0 SEGS B _ ABCMP) (nl_spec_x_of_AR0 B _ NL) (csd_spec_x_of_AR0 B _ CSD) TL).
Qed.
(* the closure, printed into every build log: Section variables B, LX0, ASTRLEN, ABCMP, NL, CSD, TL (and the contexts)
   and the axioms, to be checked against toolchain/allowed-axioms.txt *)
Print Assumptions pb_check_shape_event.
End cAR.
End b.
End a.
