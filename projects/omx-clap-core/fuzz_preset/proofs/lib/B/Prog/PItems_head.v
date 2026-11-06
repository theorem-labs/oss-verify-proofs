(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: segment HEAD + CLOSE of parse_items' image-B walk:
   back from the first skip_ws, the empty-container test, and the closer in its two copies.
   THE TEXT is the kit's lib/A/PRH_FnParse.v tparse_items_specX (record walk-S5b 4e6e65af6e1: room_live_cf invariant,
   rd_blocks_move and the blocks_bytes bound in the post); the segment statements are the
   lib/B/Prog/PItems_pres.v specs pi_head_spec / pi_close_spec / pi_close2_spec, proved here at image B's listing
   (B_prog_listing / PL_prog_B / PI_prog_B) and image B's PrhImg (prh_img_B), all passed explicitly. The shared layer
   is lib/B/Prog/PItems_defs.v, the generic transport lemmas (reader agreement, ledger, placement) are in
   lib/B/Prog/PItems_agr.v; the neighbours enter as Section hypotheses with PItems_pres.v's exact texts:
   pi_loop_spec (the member loop at PI_O_LOOP) and pi_epi_spec (the epilogue at PI_O_EPI).
   THE BATCH (kit preset-tree-at-2026-10-29T13-54-32Z.tsv (sha256 14e543909afe; internal record), parse text blob 646976800439):
   the post is the m-form (fpostWFm); every run here is YC1fPx's paj_run_to_x_inv at P = YAkMemnorm.memnorm
   (YSRrMemnorm.srr_inv_laws_memnorm_k), so the overlay's normality goes from the block's state to the next block's (or the
   epilogue's); the blocks make no call and no allocator step, so the travelling position and live requests (PItems_posb.v's
   pi_posb / pi_live, the post-implication form of the kit) move only by pi_posb_eq / pi_live_eq (Sc unchanged, no
   event): the head hands them on over the empty prefix trace, the closer gives the post's position transfer
   (pi_posb_post) and live-request permutation from them over its own trace.
   The batch kit (240b06ed4fd4; lane PItemsB.K1Head): every segment spec takes the cursor set CW and the budget
   the cursor set CW and the budget WS0 (pi_aj .. WS0 -> wbudget CW 0 WS0 -> pre -> pi_goal .. CW). Each run here takes the
   EMPTY-budget journal (YCbqGwild.ajournal_xw_rebase at the block's depot) and hands the epilogue / the next segment the
   budgeted one back (ajournal_xw_unbase0): the blocks make no allocator call, so WS0 is unchanged. The head enters the
   member loop at n = 0 with the granted prefix [] [], cap = 0 = ncap 0, no member and the free list [] (pi_fl_eq from
   jf_cont's loop arm), and the empty container's close pre with the free order [] (jf_cont's closer arm) and the
   empty node's capacity word. The closers conclude the batch kit's post: the OUTCOME (PjGrammar.agrees_some: a Some run is
   the all-granted run, so its trace is the granted trace and no call was refused), and the Some arm's free order
   and capacities carried from the pre across the two cursor stores (PRH_PjOrder.pj_foR_frame,
   PvB_Frees.pvf_ncap_frame).
   THE RE-HIDING MOVE and THE HULL (the segment texts' current form): every segment spec takes its journal at the world
   relation wle' segs RZ_cf (YA0nH) and concludes YA0nH.SRr' with its post at wle', so every run here is YC1fPx's R
   runner paj_run_to_x_invR at wle' (the branch YSRrG.paj_branchR, the journal's rebase / unbase0 their R forms), and
   cl_core / hd_mk_loop / hd_mk_close conclude SRr'. The blocks make no call, so pi_posb (which carries the hull use)
   moves only by pi_posb_eq; the closer gives the post's hull use from the pre's pi_posb over its whole trace
   (PItems_posb.pi_posb_hull_post) and the injected-reading conjunct from its Some run (cl_granted: no call was
   refused). The post is read and built through the text's records (tpiP_R_of / tpiP_Q_of_R, tpiP_ASome_of_R).
   BLOCKS (the neutral listing, the internal file parse_items.fuzz_preset.asan-ubsan.s):
     PI_O_HEAD   0x87b24 .. 0x87b6c and 0x87e44 / 0x87e48: the shadow checks of q and q + 8, the loads of in->p and
                 in->end, `p >= end` (0x87b48), the null and shadow checks of the byte at p, the closer test
                 ('}' at 0x87b68 / 0x87b6c for an object, ']' at 0x87e44 / 0x87e48 for an array).
     PI_O_CLOSE  0x87e4c .. 0x87e84: `p = -1`, the shadow check of q, in->p++, the shadow check of the depth word,
                 the depth load, `addiw -1`, the signed-overflow check (0x87e74), the second shadow check of the depth
                 word, s5 = 0, the store of the lowered depth, then the epilogue.
     PI_O_CLOSE2 0x87f58 .. 0x87f88: the second copy of the same block (0x87f5c / 0x87f80 are its two UBSan
                 checks); its last shadow check jumps back into the first copy at 0x87e80.
   WHY TWO LEMMAS, ONE PRE: the copies differ in their pc-relative targets and in where the slow path sits, so no one
   symbolic run covers both; each copy has its own run (cl_core's two arms) and both share the state construction
   (cl_st_ok), the post-run argument (cl_fin) and the data argument (pi_close_post).
   CHECKS NOT TAKEN (each resolved inside the symbolic run from the run's facts, or by the arm's own hypothesis):
     0x87b28 / 0x87e58 / 0x87f64 `bnez` on the shadow of q, 0x87b3c on the shadow of q + 8, 0x87e68 / 0x87e7c /
       0x87f74 / 0x87f88 on the shadow of q + 16: the SH entry (q, 0, 24) from range_addressable q 24 (pi_cur /
       pi_close_pre), so each shadow byte is 0;
     0x87b4c `beqz p` (null text pointer): the run's fact 4096 <= p, from src_rd's 4096 <= text and pj_in_okR's
       text <= p;
     0x87b5c `bnez` on the shadow of the byte at p and its slow path 0x87fdc: the SH entry (p, 0, 1) from src_rd's
       range_addressable text len, p < text + len on that arm;
     0x87e50 / 0x87f5c `beq p, -1` (pointer overflow of p + 1): the run's fact p <= 2 ^ 47 - 2, from src_rd's
       text + len + 8 <= alloc_ceiling;
     0x87e74 / 0x87f80 `bge d, d + 1` (signed overflow of depth - 1): the run's fact 1 <= d + 1 <= 32, from
       pj_in_okR's depth bound with the prologue's depth refusal (S d <= MAXD).
   Numerals: 0, 8, 16, 20, 24, 40, 56, 104, 136, 144 are LENGTH (cursor / node / frame offsets); 0xec, 0x138,
   0x414, 0x450, 0x520 are LENGTH (offsets inside the body, PItems_defs.v / PItems_pres.v names); 4096, 2 ^ 47,
   2 ^ 62, 2 ^ 64, 2 ^ 63, 2 ^ 32 are DERIVED (address-space bounds); 1, 3, 32, 33, 93, 125 are WORD
   (shift amount, depth bound, ASCII). No ADDRESS: every pc is pa_val A_TEXT + PI_AT PI_O_*. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
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
YP0d YP0c YC80 YC80x YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs PItems_pres PItems_agr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_posb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
(* the batch kit tools: PItemsB's OUTCOME lemmas (pik1_move_ran) and PValueB's capacity frame (pvf_ncap_frame, pvf_zero_foR) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_ledk1 PvB_Frees.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================================================================================== *)
(* THE CLOSER's symbolic state: s1 = q (atom 9), a0 = the cursor pc (atom 10), s10 = SHADOW_OFF (atom 26), the
   depth word d + 1 (extra atom 32); s0, s9 and s11 pinned to q + 16 and the two shadow addresses; the cursor's
   p field and depth word as two writable regions, exactly the two cells of FP the closer stores into *)
Definition cl_sregs : list sv :=
  sr_set (sr_set (sr_set sr_atoms 8%bv (SOff 9 16)) 25%bv (pi_shx (SOff 9 16))) 27%bv (pi_shx (SOff 9 0)).
Definition cl_smem : smem :=
 [ YP09.mkRegion (Some 9%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 10 0))];
   YP09.mkRegion (Some 9%nat) 16 20 16 20 [YP09.mkChunk 16 (CVal 4 (SOff 32 0))] ].
Definition cl_facts : list (nat * afact) :=
 [ (9%nat, mkAF 4096 (2 ^ 47 - 24) 3); (10%nat, mkAF 4096 (2 ^ 47 - 2) 0);
   (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 1 32 0) ].
Definition ss_cl (pc : Z) : sstate := mkSS pc cl_sregs cl_smem None (mkFacts cl_facts [] []).
Definition cl_SH : list shent := [mkSHE 9 0 24].
Definition pi_Bx : sv := SOff 26 0.

(* the cells the closer stores into are q's p field and depth word; every other byte is kept *)
Definition cl_F (q : Z) (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ (q <= a < q + 8 \/ q + 16 <= a < q + 20).

(* ---- projections of the entry premises pi_ent / rd_pre: the record text has moved several times, so every segment
   lemma reads the fields it uses through this one lemma, whose proof finds each field by its type ---- *)
Section ent. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Lemma pi_ent_facts : forall B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v
  (o : bool) (CTX0 CW : list (list Z)),
  pi_ent (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW ->
  pj_in_okR (@pa_segs rc B_prog_listing (@PI_prog_B rc)) (mrestrict (w_H W) mem) q text len p (Z.of_nat d) tb /\
  spZ regs0 <= q /\ q + 24 <= spZ regs0 + e /\
  src_rd (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) W mem text tb /\
  (q + 24 <= v \/ v + 56 <= q) /\ (0 < len -> text + len <= v \/ v + 56 <= text) /\
  p < text + len /\ nth_error tb (Z.to_nat (p - text)) = Some (if o then 123 else 91) /\
  cnt + 2 * Z.of_nat (length (rest_atR tb text p)) + 2 < 2 ^ 64 - 1.
Proof.
intros B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW H.
unfold pi_ent, rd_pre in H.
repeat match goal with X : _ /\ _ |- _ => destruct X end.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); assumption.
Qed.
End ent.

Section cl. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation VAL := (@pa_val rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation PIAT := (@PI_AT rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

Lemma cl_st_ok : forall (W : world SEGS) memc (regs : bvmap 5 word) q pc dp off,
  getr regs 9 = w64 q -> getr regs 8 = w64 (q + 16) -> getr regs 26 = w64 SHADOW_OFF ->
  getr regs 27 = w64 (pi_sh q) -> getr regs 25 = w64 (pi_sh (q + 16)) -> getr regs 10 = w64 pc ->
  4096 <= q <= 2 ^ 47 - 24 -> q mod 8 = 0 -> 4096 <= pc <= 2 ^ 47 - 2 -> 1 <= dp <= 32 ->
  val_mem SEGS (rdW W memc) q 8 pc -> val_mem SEGS (rdW W memc) (q + 16) 4 dp ->
  (forall x, q <= x < q + 24 -> writable_at SEGS (rdW W memc) x) ->
  st_ok_pi SEGS VAL (Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) (Ereg regs [Z_to_bv 64 dp])) (ss_cl off)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (VAL A_TEXT + off)) memc (seg_rom SEGS))).
Proof.
intros W memc regs q pc dp off H9 H8 H26 H27 H25 H10 Hq Hq8 Hpc Hdp Vp Vd Hwr.
set (E := Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) (Ereg regs [Z_to_bv 64 dp])).
assert (E9 : ew E 9 = Z_to_bv 64 q) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = Z_to_bv 64 pc) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 dp) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = pc) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = dp) by (rewrite E32; apply unsigned_lit_small; lia).
assert (D9 : forall c, 0 <= q + c < 2 ^ 64 -> sv_denot E (SOff 9 c) = Z_to_bv 64 (q + c)).
{ intros c Hc. rewrite denot_lit_U, U_SOff, U9, zcanon_id by (unfold M64; lia). reflexivity. }
rewrite restrict_mkst_fx. unfold ss_cl. apply pa_entry_st_ok_full.
- unfold cl_sregs.
  apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg| |]| |]| |];
  try (intros X; discriminate X).
  + rewrite H8, D9 by lia. reflexivity.
  + rewrite H25, (pi_denot_shx E (SOff 9 16) SHADOW_OFF (q + 16) (D9 16 ltac:(lia)) E26) by (unfold SHADOW_OFF; lia).
    reflexivity.
  + rewrite H27, (pi_denot_shx E (SOff 9 0) SHADOW_OFF q ltac:(rewrite D9 by lia; f_equal; lia) E26) by (unfold SHADOW_OFF; lia).
    reflexivity.
- vm_compute. reflexivity.
- unfold cl_smem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite U9.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ q 0 8 (SOff 10 0) pc); [rewrite denot_lit_U, U_SOff, U10, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vp].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ q 16 4 (SOff 32 0) dp); [rewrite denot_lit_U, U_SOff, U32, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside | exact Vd].
- apply pairwise_disjoint_of_extents. unfold cl_smem. cbn [map]. unfold extent_of_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok cl_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U10, U26, U32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable d : nat.
Variable HL : Z.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
(* PItems_entry.v's epilogue, PItems_pres.v's text *)
Hypothesis HEPI : pi_epi_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing)
  (PA := PI_prog_B) (PL := PL_prog_B) B ARx SK d.
Let RUNTO := PI_RUNTOR (fx := fx) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B) (PI := PI_prog_B)
  B (@prh_pst prh_img_B) ARx LAWS.
(* the same runner carrying the overlay's normality (YAkMemnorm.memnorm) from the run's start memory to its end *)
Let RUNTOI := paj_run_to_x_invR (fx := fx) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B) (PI := PI_prog_B)
  B (@prh_pst prh_img_B) ARx LAWS (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).

Lemma pi_stk_nonneg : 0 <= STK_parse_items (PI := prh_img_B) d.
Proof.
unfold STK_parse_items. pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - d)).
assert (EL : LEAF_pv_pi (PI := prh_img_B) = 16560) by (vm_compute; reflexivity). rewrite EL.
cbn [PRH_Base.pi_frame prh_img_B]. lia.
Qed.

(* THE CLOSER, either copy, from the run's facts to any post Q the epilogue can conclude, at any budget predicate P
   the journal's budget WS0 meets (the closer makes no allocator call: the epilogue gets WS0 back) *)
Lemma cl_core : forall (off : Z) (fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md (regs0 : bvmap 5 word) e q v (o : bool)
  (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  lyc Sc Hpc Wc memc mdc k WS0 (regs : bvmap 5 word) pc,
  (off = PI_O_CLOSE \/ off = PI_O_CLOSE2) ->
  pi_ajR (rc := rc) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf)
    ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 -> P WS0 ->
  pi_fpok fx0 fx -> YAkMemnorm.memnorm SEGS memc ->
  pi_frame (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs0 regs W mem Wc memc e q v ->
  pi_regs regs q v o -> getr regs 10 = w64 pc ->
  val_mem SEGS (rdW Wc memc) q 8 pc -> val_mem SEGS (rdW Wc memc) (q + 16) 4 (Z.of_nat d + 1) ->
  (forall x, q <= x < q + 24 -> writable_at SEGS (rdW Wc memc) x) ->
  q mod 8 = 0 -> 4096 <= pc <= 2 ^ 47 - 2 -> (d < 32)%nat -> spZ regs0 <= q -> q + 24 <= spZ regs0 + e ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF q 24 ->
  pi_Qstable (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) Q ->
  (forall memf mdf, pi_agr (cl_F q) (rdW Wc memc) (rdW Wc memf) ->
     val_mem SEGS (rdW Wc memf) q 8 (pc + 1) -> val_mem SEGS (rdW Wc memf) (q + 16) 4 (Z.of_nat d) ->
     (forall x, q <= x < q + 24 -> writable_at SEGS (rdW Wc memf) x) ->
     forall regs', getr regs' 10 = w64 0 -> Q lyc Sc Hpc Wc regs' memf mdf) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfg_at (fx := fx) SEGS (VAL A_TEXT + PIAT off) regs memc mdc)
    (fpostWFbm (fx := fx0) (rc := rc) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK P
      (STK_parse_items (PI := prh_img_B) d) e (rd_fp q v) regs0 ly S Hp W mem md Q).
Proof.
intros off fx0 ly S Hp W mem md regs0 e q v o P Q lyc Sc Hpc Wc memc mdc k WS0 regs pc
  Hoff HJw HP Hfp HMN Hfr Hrg H10 Vp Vd Hwr Hq8 Hpcr Hd Hsq Hqe Hra HQs HQ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pi_stk_nonneg as HSTK.
unfold pi_ajR in HJw.
pose proof HJw as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _ & _).
(* THE BUDGETED JOURNAL (the batch kit): the run takes the empty-budget journal rebased at this block's depot; HWD covers the
   moved depot's wild part, which the step back to WS0 needs (YCbqGwild.ajournal_xw_unbase0R, at wle') *)
pose proof (ajxR_wild HJw) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ.
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
assert (Hq0 : alloc_ceiling <= q) by lia.
assert (Hq47 : q + 24 <= 2 ^ 47) by lia.
pose proof Hrg as (R9 & R19 & R18 & R8 & R20 & R26 & R27 & R25 & R23).
pose proof (cl_st_ok Wc memc regs q pc (Z.of_nat d + 1) (PIAT off) R9 R8 R26 R27 R25 H10 ltac:(lia) Hq8 Hpcr ltac:(lia)
  Vp Vd Hwr) as HS.
remember (Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) (Ereg regs [Z_to_bv 64 (Z.of_nat d + 1)])) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E9 : ew E 9 = Z_to_bv 64 q) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E10 : ew E 10 = Z_to_bv 64 pc) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E32 : ew E 32 = Z_to_bv 64 (Z.of_nat d + 1)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = pc) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = Z.of_nat d + 1) by (rewrite E32; apply unsigned_lit_small; lia).
clear HE.
assert (SHOK : sh_ok SEGS pi_Bx cl_SH E (rdW Wc memc)).
{ unfold cl_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H Wc) memc E pi_Bx 9 q 24 q 0 24 Hra);
  [unfold pi_Bx; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
  | rewrite (U_atom E 9 q E9) by lia; reflexivity | lia | lia | intros x Hx; unfold SHADOW_OFF; lia]. }
unfold cfg_at. change (w64 (VAL A_TEXT + PIAT off)) with (Z_to_bv 64 (VAL A_TEXT + PIAT off)).
destruct Hoff as [-> | ->]; paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_EPI).
all: lazymatch goal with
| |- awr_ok _ _ _ _ _ _ _ _ _ =>
    unfold ss_cl; cbn [ss_mem]; unfold cl_smem;
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (q - (spZ regs0 + e)));
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |];
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (q - (spZ regs0 + e)));
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |];
    apply awr_ok_nil
| _ => idtac
end.
all: lazymatch goal with
| HFr : frame_of _ _ _ _, HS : st_ok_pi _ _ _ _ (restrict _ ?ms') |- _ =>
    assert (AGR : pi_agr (cl_F q) (rdW Wc memc) (rdW Wc (ms_mem ms')));
    [ intros a [Ha Hn]; apply HFr; rewrite unsigned_lit_small by lia; intros (r & Hin & Hr);
      unfold ss_cl in Hin; cbn [ss_mem] in Hin; unfold cl_smem in Hin;
      destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U9 in Hr;
      apply Hn; lia
    | ];
    pose proof (pi_region_nth _ _ _ _ _ 0 _ HS eq_refl) as RG0;
    pose proof (pi_region_nth _ _ _ _ _ 1 _ HS eq_refl) as RG1;
    cbn [ms_mem restrict] in RG0, RG1;
    pose proof (pi_field SEGS _ _ 9%nat q _ _ _ _ _ 0 8 (SOff 10 1) (pc + 1) RG0 U9 ltac:(left; reflexivity)
      ltac:(rewrite denot_lit_U, U_SOff, U10, zcanon_id by (unfold M64; lia); reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ;
    rewrite Z.add_0_r in VQ;
    pose proof (pi_field SEGS _ _ 9%nat q _ _ _ _ _ 16 4 (SOff 32 (-1)) (Z.of_nat d) RG1 U9 ltac:(left; reflexivity)
      ltac:(rewrite denot_lit_U, U_SOff, U32, zcanon_id by (unfold M64; lia); f_equal; lia) ltac:(cbn; lia) ltac:(zside)) as VD;
    assert (WR : forall x, q <= x < q + 24 -> writable_at SEGS (rdW Wc (ms_mem ms')) x);
    [ intros x Hx;
      destruct (Z_lt_dec x (q + 8)) as [Hx1|Hx1]; [destruct RG0 as (_ & _ & Hw0 & _); cbn [YP09.r_base base_val YP09.r_wlo YP09.r_whi] in Hw0;
        rewrite U9 in Hw0; replace x with (q + (x - q)) by lia; apply Hw0; lia|];
      destruct (Z_lt_dec x (q + 16)) as [Hx2|Hx2]; [apply (pi_wr_agr SEGS (cl_F q) _ _ x AGR); [split; lia | apply Hwr; lia]|];
      destruct (Z_lt_dec x (q + 20)) as [Hx3|Hx3]; [destruct RG1 as (_ & _ & Hw1 & _); cbn [YP09.r_base base_val YP09.r_wlo YP09.r_whi] in Hw1;
        rewrite U9 in Hw1; replace x with (q + (x - q)) by lia; apply Hw1; lia|];
      apply (pi_wr_agr SEGS (cl_F q) _ _ x AGR); [split; lia | apply Hwr; lia]
    | ];
    prreg HS (21%bv : bv 5) R21'; prreg HS (2%bv : bv 5) R2'; prreg HS (3%bv : bv 5) R3'; prreg HS (4%bv : bv 5) R4';
    pmkst HS;
    lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
      replace pcw with (w64 (VAL A_TEXT + PIAT PI_O_EPI)) by (unfold w64; f_equal; vm_compute; reflexivity) end;
    apply (HEPI P fx fx0 ly S Hp W mem md regs0 e q v Q lyc Sc Hpc Wc _ _ k _ 0 WS0
      (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS YGcfRehidePost.RZ_cf)
         _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD) HP);
    unfold pi_epi_pre; split; [exact Hfp|]; split; [exact HMN|];
    split;
    [ apply (pi_frame_kept (cl_F q) regs0 regs _ W mem Wc memc _ e q v Hfr);
      [ unfold spZ; rewrite R2', E2; reflexivity | rewrite R3', E3; reflexivity | rewrite R4', E4; reflexivity | exact AGR
      | intros a Ha; split; [lia|]; lia
      | intros a Ha Hn; split; [lia|]; intros Hc; apply Hn;
        destruct Hc as [Hc|Hc]; [exists (q, q + 8) | exists (q + 16, q + 20)]; (split; [cbn; tauto | cbn [fst snd]; lia]) ]
    | ];
    split; [cbn [ms_regs]; rewrite R21'; reflexivity|];
    split; [exact HQs|];
    intros regs'' H10''; exact (HQ _ _ AGR VQ VD WR regs'' H10'')
end.
Qed.

(* The kit's post reads memory only through the reader, so it survives any memory with the same reader *)
Lemma cl_post_stable : forall ly0 S0 dd (o : bool) tb text len p q v Lam peak cnt fail ran most own kr,
  pi_Qstable (rc := rc) (L := B_prog_listing) (PA := PI_prog_B)
    (pi_post (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
       B ly0 S0 dd o tb text len p q v Lam peak cnt fail ran most own kr).
Proof.
intros ly0 S0 dd o tb text len p q v Lam peak cnt fail ran most own kr ly S Hp W regs m m' md md' Heq HQ.
assert (E : rdW W m' = rdW W m) by (apply functional_extensionality; exact Heq).
unfold pi_post in HQ |- *.
(* the text's post read and rebuilt through its records: only the ledger and the arm read memory *)
destruct (tpiP_R_of HQ) as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & HR).
apply tpiP_Q_of_R with (ok := ok) (res := res) (tr := tr) (okr := okr) (D := D) (Lam' := Lam') (peak' := peak')
  (cnt' := cnt') (fail' := fail') (ran' := ran').
pose proof (tpiP_arm HR) as HA. unfold tpiP_ASome, tpiP_ANone in HA.
exact {| tpiP_run := tpiP_run HR;
  tpiP_ledger := cl_ledger_rdeq B _ _ _ _ _ _ _ _ _ _ _ _ _ E (tpiP_ledger HR);
  tpiP_room := tpiP_room HR; tpiP_hull := tpiP_hull HR; tpiP_live := tpiP_live HR; tpiP_pos := tpiP_pos HR;
  tpiP_outcome := tpiP_outcome HR; tpiP_injected := tpiP_injected HR; tpiP_ledger_move := tpiP_ledger_move HR;
  tpiP_blocks_move := tpiP_blocks_move HR; tpiP_bytes := tpiP_bytes HR; tpiP_lsum := tpiP_lsum HR;
  tpiP_arm := ltac:(unfold tpiP_ASome, tpiP_ANone; rewrite E; exact HA) |}.
Qed.

Variable CTX0 : list (list Z).
Variable CW : list (list Z).

(* a reader agreement on F gives PRH_Reader's agreement (bytes and writability) on any part of F *)
Lemma cl_agree_of : forall F (m m' : word -> option byte) (X : Z -> Prop),
  pi_agr F m m' -> (forall x, X x -> F x) -> pj_agreeR SEGS m m' X.
Proof.
intros F m m' X HA HX x Hx. split.
- unfold mbyte. rewrite (HA x (HX x Hx)). reflexivity.
- exact (pi_wr_agr SEGS F m m' x HA (HX x Hx)).
Qed.

(* a run that ends in Some read every allocator call it made as granted (PjGrammar.agrees: a refusal stops the run
   with None), so the ledger move refused nothing *)
Lemma cl_granted : forall dd (o : bool) x ok t r tr okr cnt fail,
  PjGrammar.jr_items prh_jr_strtod dd o x ok = (Some (t, r), tr, okr) -> prh_granted ok cnt fail (PjGrammar.calls tr).
Proof.
intros dd o x ok t r tr okr cnt fail E.
pose proof (PjGrammar.agrees_jr_items prh_jr_strtod dd o x) as AG.
destruct (PjGrammar.agrees_some _ _ _ _ _ _ AG E) as [E0 _].
intros i Hi Hf. exfalso.
destruct (PjGrammar.ok_upto_dec ok (PjGrammar.calls tr)) as [Hu | (j & Hj & Hf' & Hu)].
- rewrite (Hu i Hi) in Hf. discriminate Hf.
- pose proof (proj2 (AG ok) j) as K. rewrite E0 in K. cbn [fst snd] in K.
  destruct (K Hj Hf' Hu) as (P0 & e0 & rest & Em & _). rewrite E in Em. discriminate Em.
Qed.

(* THE DATA ARGUMENT of the closer: the kit's post at the memory the two stores leave. Everything the post reads is
   either the cursor (rebuilt from the run's two values), the ledger and the blocks of D (below the allocation
   ceiling, hence below q) or the node's 56 bytes (apart from q by rd_pre). The batch kit's conjuncts: the OUTCOME (the run
   is the all-granted one, PjGrammar.agrees_some: its trace is the granted trace, no call was refused, and the
   position is the pre's pi_posb over it), and the Some arm's free order and capacities, carried over the subtree's
   footprint pj_footR v D, which the two stores miss. *)
Lemma cl_close_data : forall (fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md ch CTX (regs0 : bvmap 5 word)
  e q v (o : bool) text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k WS
  pc ok tr okr D Lam' peak' cnt' fail' ran' t r memf mdf (regs' : bvmap 5 word),
  pi_ajR (rc := rc) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf)
    ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS ->
  pi_ent (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW ->
  PjGrammar.jr_items prh_jr_strtod d o (rest_atR tb text p) ok = (Some (t, r), tr, okr) ->
  rest_atR tb text pc = PjGrammar.closer o :: r ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B lyc Sc Hpc Wc memc Lam' peak' cnt' fail' ran'
    most own ->
  room_live_cf (PrhRoomLive := RL) Sc ->
  PItems_posb.pi_posb S Sc tr ->
  PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr ->
  rd_ledger_move Lam peak cnt fail ran most ok (prhPi_gtrace d o (rest_atR tb text p)) tr D Lam' peak' cnt' fail' ran' ->
  rd_blocks_move (cp := cp) B ly S lyc Sc D tr (rest_atR tb text p) d ->
  blocks_bytes Sc <= blocks_bytes S + prh_held (cp := cp) tr ->
  Ledger.lsum D = PjGrammar.held tr ->
  pj_in_okR SEGS (rdW Wc memc) q text len pc (Z.of_nat d + 1) tb ->
  pj_nodeR SEGS (rdW Wc memc) (prh_lin Lam') v t D ->
  Ledger.lsum D <= 224 * (Z.of_nat (length (rest_atR tb text p)) - Z.of_nat (length r)) ->
  (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat ->
     exists F, PRH_PjOrder.pj_foR SEGS (rdW Wc memc) (prh_lin Lam') nn v D F /\
       map (fun b => snd b + cf_head) F = prhPi_frees d o (rest_atR tb text p) ok) ->
  pj_ncapR SEGS (rdW Wc memc) v t ->
  4096 <= v -> v + 56 <= 2 ^ 47 ->
  pi_agr (cl_F q) (rdW Wc memc) (rdW Wc memf) ->
  val_mem SEGS (rdW Wc memf) q 8 (pc + 1) -> val_mem SEGS (rdW Wc memf) (q + 16) 4 (Z.of_nat d) ->
  (forall x, q <= x < q + 24 -> writable_at SEGS (rdW Wc memf) x) ->
  getr regs' 10 = w64 0 ->
  pi_post (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    B ly S d o tb text len p q v Lam peak cnt fail ran most own kr lyc Sc Hpc Wc regs' memf mdf.
Proof.
intros fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k WS
  pc ok tr okr D Lam' peak' cnt' fail' ran' t r memf mdf regs'
  HJ Hent HJR Hrest HLG HRM HPB HLV HMV HBM HBB HLH HIN HND HLS HFO HNC Hv0 Hv1 AGR Vq Vd WR H10'.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pi_stk_nonneg as HSTK.
unfold pi_ajR in HJ.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
destruct (pi_ent_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hent) as (_ & Hsq & Hqe & HSRC & Hdqv & _ & Hplt & _).
destruct HSRC as (_ & Ht4 & Htc & _ & _ & _).
destruct HIN as (Vp0 & Ve0 & Vd0 & Hrw0 & Hq8 & Ht0 & Htl & Hple & Hlen & HG & Hdqt & Hd032).
assert (Hq0 : YM05.alloc_ceiling <= q) by lia.
(* the cursor's new place: the closer is one byte, so pc + 1 = text + len - |r| *)
assert (HL1 : length (rest_atR tb text pc) = (1 + length r)%nat) by (rewrite Hrest; reflexivity).
unfold rest_atR in HL1. rewrite length_skipn in HL1.
assert (Hpc1 : pc + 1 = text + len - Z.of_nat (length r)) by lia.
assert (Hpclt : pc < text + len) by lia.
(* every byte below the allocation ceiling, and every byte of the text, is kept *)
assert (HFc : forall a, 0 <= a < YM05.alloc_ceiling -> cl_F q a) by (intros a Ha; split; lia).
assert (HFt : forall x, text <= x < text + len -> cl_F q x) by (intros x Hx; split; lia).
(* the subtree's blocks are ledger blocks (Lam' = D ++ Lam up to order), so below the ceiling, hence below q *)
assert (HLD : forall a kk, In (a, kk) D -> prh_lin Lam' a kk).
{ intros a kk Hin. unfold prh_lin. destruct HMV as (_ & _ & _ & HP & _).
  apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin. }
(* the subtree's footprint (the node's 56 bytes, apart from q, and the blocks of D) is kept *)
assert (HFT : forall x, pj_footR v D x -> cl_F q x).
{ intros x [Hx | (b & Hb & Hbx)].
  - split; lia.
  - destruct b as [bb bm]. pose proof (HLD bb bm Hb) as HinL. unfold prh_lin in HinL.
    unfold pj_holdsR in Hbx. cbn [fst snd] in Hbx.
    destruct (cl_D_bounds B ARx HL LAWS lyc Sc Hpc Wc memc mdc Lam' peak' cnt' fail' ran' most own bb bm HARc HLG HinL)
      as [Hb1 Hb2].
    split; lia. }
pose proof (cl_agree_of (cl_F q) _ _ _ AGR HFT) as HAG.
(* the run is the all-granted one (PjGrammar.agrees_some): the granted trace is tr *)
destruct (PjGrammar.agrees_some _ _ _ _ _ _ (PjGrammar.agrees_jr_items prh_jr_strtod d o (rest_atR tb text p)) HJR)
  as [E0 _].
assert (EG : prhPi_gtrace d o (rest_atR tb text p) = tr) by (unfold prhPi_gtrace; rewrite E0; reflexivity).
(* the cursor at pc + 1, depth d: its two stores, and every other byte the reader reads is kept *)
assert (HIN' : pj_in_okR SEGS (rdW Wc memf) q text len (text + len - Z.of_nat (length r)) (Z.of_nat d) tb).
{ rewrite <- Hpc1.
  split; [exact Vq|]. split.
  { apply (pi_val_agr SEGS (cl_F q) _ _ _ _ _ AGR); [intros kk Hk; split; lia | exact Ve0]. }
  split; [exact Vd|]. split; [exact WR|]. split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|].
  split; [lia|]. split; [exact Hlen|]. split.
  { apply (pi_garr8_agr SEGS (cl_F q) _ _ _ _ AGR); [intros x Hx; apply HFt; lia | exact HG]. }
  split; [exact Hdqt | lia]. }
(* the free order of the tree, carried across the stores (they miss its footprint) *)
assert (HFO' : cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat ->
  exists F, PRH_PjOrder.pj_foR SEGS (rdW Wc memf) (prh_lin Lam') nn v D F /\
    map (fun b => snd b + cf_head) F = prhPi_frees d o (rest_atR tb text p) ok).
{ intros HH nn Hnn. destruct (HFO HH nn Hnn) as (F & HF1 & HF2). exists F. split; [|exact HF2].
  exact (PRH_PjOrder.pj_foR_frame SEGS nn _ _ _ _ v D F HF1 HLD HAG). }
(* THE HULL USE: the pre's pi_posb over the whole trace tr is the run's at the instance's outcomes ok *)
assert (HPB' : PItems_posb.pi_posb S Sc (snd (fst (PjGrammar.jr_items prh_jr_strtod d o (rest_atR tb text p) ok))))
  by (rewrite HJR; exact HPB).
unfold pi_post.
apply tpiP_Q_of_R with (ok := ok) (res := Some (t, r)) (tr := tr) (okr := okr) (D := D) (Lam' := Lam') (peak' := peak')
  (cnt' := cnt') (fail' := fail') (ran' := ran').
exact {|
  tpiP_run := HJR;
  tpiP_ledger := cl_ledger_agr B ARx HL LAWS (cl_F q) lyc Sc Hpc Wc memc mdc memf Lam' peak' cnt' fail' ran' most own
    HARc HFc AGR HLG;
  tpiP_room := HRM;
  (* the use over tr is inside the all-granted list (PresetHullBudget.hull_items_agrees) *)
  tpiP_hull := PItems_posb.pi_posb_hull_post S Sc prh_jr_strtod d o (rest_atR tb text p) ok HPB';
  (* the closer makes no call and no allocator step: the live requests and the position transfer are the pre's, over
     the same trace tr at the same state Sc *)
  tpiP_live := PItems_posb.pi_live_eq _ _ _ tr (Permutation_refl _) HLV;
  tpiP_pos := PItems_posb.pi_posb_post S Sc tr (PItems_posb.pi_posb_eq S Sc Sc tr eq_refl HPB);
  (* THE OUTCOME: no refusal (ran' = ran), the run is the all-granted one, and the position over the granted trace is
     the position over tr *)
  tpiP_outcome := ltac:(intros sm x os i H0 hist HI HR _ _; rewrite EG in HR |- *;
    split; [exact (PItems_ledk1.pik1_move_ran _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (cl_granted d o _ ok t r tr okr cnt fail HJR) HMV)
    | split; [exact (f_equal fst E0) | exact (PItems_posb.pi_posb_post S Sc tr HPB sm x os i H0 hist HI HR)]]);
  (* THE INJECTED READING: a Some run refused no call, at any chosen failure *)
  tpiP_injected := ltac:(intros; exact (cl_granted d o _ ok t r tr okr cnt fail HJR));
  tpiP_ledger_move := HMV;
  tpiP_blocks_move := HBM;
  tpiP_bytes := HBB;
  tpiP_lsum := HLH;
  (* the Some arm: the node by the footprint frame lemma, its capacity words by PvB_Frees.pvf_ncap_frame *)
  tpiP_arm := tpiP_ASome_of_R {|
    tpiPs_ret := H10';
    tpiPs_freeord := HFO';
    tpiPs_in_ok := HIN';
    tpiPs_node := pi_nodeR_agr SEGS t (cl_F q) _ _ _ _ _ AGR HFT HND;
    tpiPs_ncap := PvB_Frees.pvf_ncap_frame SEGS t (w_H Wc) memc _ _ v D HND HAG HNC;
    tpiPs_lsum_le := HLS |} |}.
Qed.

End cl.

(* ================================================================================================== *)
(* ---- the model at the empty-container test: jr_cont's own case split (PjGrammar.v:254-263) ---- *)

(* the member loop is entered: the byte after the opener's white space is not the closer (or there is none) *)
Lemma hd_cont_loop : forall dd (o : bool) x0 y, (Nat.succ dd <= PjGrammar.MAXD)%nat ->
  y = PjGrammar.skip (tl x0) ->
  match y with [] => True | c :: _ => c <> PjGrammar.closer o end ->
  pi_run_eq dd o x0 [] [] (2 * length x0 + 2) 0 0 [] y.
Proof.
intros dd o x0 y Hd Hy Hc ok1 r t ok2 H.
cbn [app] in *. unfold PjGrammar.jr_items, PjGrammar.jr_cont. cbv zeta.
assert (HF : (PjGrammar.MAXD <? S dd)%nat = false) by (apply Nat.ltb_ge; exact Hd). rewrite HF.
rewrite <- Hy. cbn [rev] in H.
destruct y as [|c r']; [exact H|].
destruct (Z.eqb_spec c (PjGrammar.closer o)) as [->|Hne]; [contradiction | exact H].
Qed.

(* the container is empty: the byte is the closer, so the whole call is jret (mk o [], r) with no event *)
Lemma hd_cont_close : forall dd (o : bool) x0 y r, (Nat.succ dd <= PjGrammar.MAXD)%nat ->
  y = PjGrammar.skip (tl x0) -> y = PjGrammar.closer o :: r ->
  forall ok, PjGrammar.jr_items prh_jr_strtod dd o x0 ok = (Some (PjGrammar.mk o [], r), [], ok).
Proof.
intros dd o x0 y r Hd Hy Hy2 ok.
unfold PjGrammar.jr_items, PjGrammar.jr_cont. cbv zeta.
assert (HF : (PjGrammar.MAXD <? S dd)%nat = false) by (apply Nat.ltb_ge; exact Hd). rewrite HF.
rewrite <- Hy, Hy2. rewrite Z.eqb_refl. reflexivity.
Qed.

(* The kit's free model jf_cont (PresetReqAt.v:251-259) splits as jr_cont does: at the member loop the whole call's free
   list is jfl's from the empty container (n = cap = 0, af = []), with the fuel the head hands the loop *)
Lemma hd_frees_loop : forall dd (o : bool) x0 y, (Nat.succ dd <= PjGrammar.MAXD)%nat ->
  y = PjGrammar.skip (tl x0) ->
  match y with [] => True | c :: _ => c <> PjGrammar.closer o end ->
  pi_fl_eq dd o x0 [] (2 * length x0 + 2) 0 0 [] y.
Proof.
intros dd o x0 y Hd Hy Hc ok1.
cbn [app]. unfold prhPi_frees, PresetReqAt.jf_cont. cbv zeta.
assert (HF : (PjGrammar.MAXD <? S dd)%nat = false) by (apply Nat.ltb_ge; exact Hd). rewrite HF.
rewrite <- Hy.
destruct y as [|c r']; [reflexivity|].
destruct (Z.eqb_spec c (PjGrammar.closer o)) as [->|Hne]; [contradiction | reflexivity].
Qed.

(* ... and at the empty container (the byte is the closer) the free list is empty *)
Lemma hd_frees_close : forall dd (o : bool) x0 y r, (Nat.succ dd <= PjGrammar.MAXD)%nat ->
  y = PjGrammar.skip (tl x0) -> y = PjGrammar.closer o :: r ->
  forall ok, prhPi_frees dd o x0 ok = [].
Proof.
intros dd o x0 y r Hd Hy Hy2 ok.
unfold prhPi_frees, PresetReqAt.jf_cont. cbv zeta.
assert (HF : (PjGrammar.MAXD <? S dd)%nat = false) by (apply Nat.ltb_ge; exact Hd). rewrite HF.
rewrite <- Hy, Hy2. rewrite Z.eqb_refl. reflexivity.
Qed.

(* the room the head carries (the whole call's granted trace) is the room the member loop asks (jrl's granted
   trace from the empty container): at ok = [] the two traces are the same list *)
Lemma hd_room_loop : forall {cp : CfParams} {RL : PrhRoomLive} Sc dd (o : bool) x0 y f n cap,
  pi_run_eq dd o x0 [] [] f n cap [] y ->
  rd_room (cp := cp) (RL := RL) Sc (prhPi_gtrace dd o x0) ->
  rd_room (cp := cp) (RL := RL) Sc (snd (fst (PjGrammar.jrl prh_jr_strtod f (Nat.succ dd) o n cap [] y []))).
Proof.
intros cp RL Sc dd o x0 y f n cap HR HM.
destruct (PjGrammar.jrl prh_jr_strtod f (Nat.succ dd) o n cap [] y []) as [[r t] ok2] eqn:EJ.
cbn [fst snd]. pose proof (HR [] r t ok2 EJ) as EI. cbn [app] in EI.
unfold prhPi_gtrace in HM. rewrite EI in HM. exact HM.
Qed.

(* the closer's room: the invariant room of the call *)
Lemma hd_room_close : forall {cp : CfParams} {RL : PrhRoomLive} Sc gt,
  rd_room (cp := cp) (RL := RL) Sc gt -> room_live_cf (PrhRoomLive := RL) Sc.
Proof. intros cp RL Sc gt (HR & _ & _). exact HR. Qed.

(* the ledger does not move on the head's paths: no call, so no refusal at any granted trace gt (the batch kit's move) *)
Lemma hd_move_id : forall Lam peak cnt fail ran most gt, 0 <= cnt < 2 ^ 64 -> 0 <= Ledger.lsum Lam <= peak ->
  rd_ledger_move Lam peak cnt fail ran most [] gt [] [] Lam peak cnt fail ran.
Proof.
intros Lam peak cnt fail ran most gt Hcnt Hsum. unfold rd_ledger_move.
cbn [PjGrammar.calls lszR nliveR hpeakR map length].
split; [split; [intros i Hi; lia | split; [left; reflexivity | intros i Hi; lia]]|].
split; [rewrite Z.add_0_r; symmetry; apply Z.mod_small; lia|].
split; [split; [intros H; lia | intros _; reflexivity]|].
split; [cbn [app]; apply Permutation_refl|].
split; [apply Permutation_refl|].
split; [reflexivity|]. unfold prh_refused_peak. cbn [List.seq map fold_right]. lia.
Qed.

(* the empty container's node: pi_cont at n = cap = 0 with no members IS the kit's pj_nodeR for mk o [] *)
Lemma hd_node_empty : forall {rc : YM05.RunCeil} m lblk (o : bool) v,
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) m lblk o v 0 0 0 0 [] [] ->
  pj_nodeR (@pa_segs rc B_prog_listing (@PI_prog_B rc)) m lblk v (PjGrammar.mk o []) [].
Proof.
intros rc m lblk o v (Hh & _ & _ & _ & _ & _ & _ & Hap & Hl).
change (Z.of_nat 0) with 0 in Hh.
destruct o; cbn [PjGrammar.mk PjTree.tag] in *.
- split; [constructor|]. split; [exact Hap|].
  exists 0, 0, 0, 0, 0, 0. split; [exact Hh|].
  split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
  split; [left; split; [reflexivity | split; reflexivity]|].
  exists []. split; [cbn; reflexivity|]. cbn [pj_memsR] in Hl |- *. exact Hl.
- split; [constructor|]. split; [exact Hap|].
  exists 0, 0, 0, 0, 0, 0. split; [exact Hh|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
  split; [left; split; reflexivity|].
  exists []. split; [cbn; reflexivity|]. cbn [pj_itemsR map] in Hl |- *. exact Hl.
Qed.

(* the empty container's capacity (CAP): its header's cap word is 0 = ncap 0, and it has no kid *)
Lemma hd_ncap_empty : forall segs m (o : bool) v ty,
  pj_hdrR segs m v ty 0 0 0 0 0 0 -> pj_ncapR segs m v (PjGrammar.mk o []).
Proof.
intros segs m o v ty (_ & _ & _ & _ & K & _ & _ & C).
destruct o; cbn [PjGrammar.mk pj_ncapR map]; (split; [exact C | exists 0; split; [exact K | exact I]]).
Qed.

(* ================================================================================================== *)
(* THE HEAD's symbolic state: s1 = q (atom 9), s10 = SHADOW_OFF (26), s0 / s9 / s11 pinned, s2 the literal
   (if o then 1 else 0); the cursor's p field (atom 32) and end word (atom 33) read-only, and, when the cursor is
   not at the end, the text byte at p1 (atom 34) as its own read-only region. No window is writable: the head
   stores nothing. *)
Definition hd_sregs (o : bool) : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 8%bv (SOff 9 16)) 25%bv (pi_shx (SOff 9 16))) 27%bv (pi_shx (SOff 9 0)))
    18%bv (SLit (if o then 1 else 0)).
Definition hd_smem (bt : bool) : smem :=
  (if bt then [YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))]] else []) ++
  [ YP09.mkRegion (Some 9%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))] ].
Definition hd_facts : list (nat * afact) :=
 [ (9%nat, mkAF 4096 (2 ^ 47 - 24) 3); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (32%nat, mkAF 4096 (2 ^ 47 - 2) 0); (33%nat, mkAF 4096 (2 ^ 47 - 1) 0); (34%nat, mkAF 0 255 0) ].
Definition ss_hd (o bt : bool) (pc : Z) : sstate := mkSS pc (hd_sregs o) (hd_smem bt) None (mkFacts hd_facts [] []).
Definition hd_SH (bt : bool) : list shent := (if bt then [mkSHE 32 0 1] else []) ++ [mkSHE 9 0 24].

Section hd. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation VAL := (@pa_val rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation PIAT := (@PI_AT rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

Lemma hd_st_ok : forall (W : world SEGS) memc (regs : bvmap 5 word) q p1 ed c (o bt : bool) off,
  getr regs 9 = w64 q -> getr regs 8 = w64 (q + 16) -> getr regs 26 = w64 SHADOW_OFF ->
  getr regs 27 = w64 (pi_sh q) -> getr regs 25 = w64 (pi_sh (q + 16)) -> getr regs 18 = w64 (if o then 1 else 0) ->
  4096 <= q <= 2 ^ 47 - 24 -> q mod 8 = 0 -> 4096 <= p1 <= 2 ^ 47 - 2 -> 4096 <= ed <= 2 ^ 47 - 1 ->
  0 <= c < 256 -> (bt = true -> q + 16 <= p1 \/ p1 + 1 <= q) ->
  val_mem SEGS (rdW W memc) q 8 p1 -> val_mem SEGS (rdW W memc) (q + 8) 8 ed ->
  (bt = true -> val_mem SEGS (rdW W memc) p1 1 c) ->
  st_ok_pi SEGS VAL (Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B)
                      (Ereg regs [Z_to_bv 64 p1; Z_to_bv 64 ed; Z_to_bv 64 c])) (ss_hd o bt off)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (VAL A_TEXT + off)) memc (seg_rom SEGS))).
Proof.
intros W memc regs q p1 ed c o bt off H9 H8 H26 H27 H25 H18 Hq Hq8 Hp1 Hed Hc Hdj Vp Ve Vc.
set (E := Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B)
           (Ereg regs [Z_to_bv 64 p1; Z_to_bv 64 ed; Z_to_bv 64 c])).
assert (E9 : ew E 9 = Z_to_bv 64 q) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 p1) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ed) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 c) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (U9 : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = p1) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = ed) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = c) by (rewrite E34; apply unsigned_lit_small; lia).
assert (D9 : forall x, 0 <= q + x < 2 ^ 64 -> sv_denot E (SOff 9 x) = Z_to_bv 64 (q + x)).
{ intros x Hx. rewrite denot_lit_U, U_SOff, U9, zcanon_id by (unfold M64; lia). reflexivity. }
rewrite restrict_mkst_fx. unfold ss_hd. apply pa_entry_st_ok_full.
- unfold hd_sregs.
  apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg| |]| |]| |]| |];
  try (intros X; discriminate X).
  + rewrite H8, D9 by lia. reflexivity.
  + rewrite H25, (pi_denot_shx E (SOff 9 16) SHADOW_OFF (q + 16) (D9 16 ltac:(lia)) E26) by (unfold SHADOW_OFF; lia).
    reflexivity.
  + rewrite H27, (pi_denot_shx E (SOff 9 0) SHADOW_OFF q ltac:(rewrite D9 by lia; f_equal; lia) E26) by (unfold SHADOW_OFF; lia).
    reflexivity.
  + rewrite H18. cbn [sv_denot]. unfold w64. destruct o; reflexivity.
- destruct bt; vm_compute; reflexivity.
- unfold hd_smem. destruct bt; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U32. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ p1 0 1 (SOff 34 0) c);
    [rewrite denot_lit_U, U_SOff, U34, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside
    | rewrite Z.add_0_r; exact (Vc eq_refl)].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|]. constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) p1);
      [rewrite denot_lit_U, U_SOff, U32, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside
      | rewrite Z.add_0_r; exact Vp].
    * apply (chunk_ok_val SEGS E _ q 8 8 (SOff 33 0) ed);
      [rewrite denot_lit_U, U_SOff, U33, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside | exact Ve].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|]. constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) p1);
      [rewrite denot_lit_U, U_SOff, U32, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside
      | rewrite Z.add_0_r; exact Vp].
    * apply (chunk_ok_val SEGS E _ q 8 8 (SOff 33 0) ed);
      [rewrite denot_lit_U, U_SOff, U33, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside | exact Ve].
- apply pairwise_disjoint_of_extents. unfold hd_smem. destruct bt;
  [pose proof (Hdj eq_refl) as Hdj'|]; cbn [app map]; unfold extent_of_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U32;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok hd_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U26, U32, U33, U34. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

End hd.

Section hd2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation VAL := (@pa_val rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation PIAT := (@PI_AT rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable d : nat.
Variable CTX0 : list (list Z).
Variable CW : list (list Z).
Variable HL : Z.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Hypothesis HEPI : pi_epi_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing)
  (PA := PI_prog_B) (PL := PL_prog_B) B ARx SK d.
Hypothesis HLOOP : pi_loop_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing)
  (PA := PI_prog_B) (PL := PL_prog_B) B ARx SK d CTX0 CW.

(* what the head's two arms share: the pre's data, the run's registers, and the (unchanged) memory *)
Definition hd_data (fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem (md : Model) ch CTX (regs0 : bvmap 5 word) e q v (o : bool)
  text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc (Wc : world SEGS) memc (mdc : Model) (regs : bvmap 5 word) p1
  : Prop :=
  pi_fpok fx0 fx /\
  pi_ent (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW /\
  PItems_posb.pi_posb S Sc [] /\
  PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) [] /\
  pi_frame (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs0 regs W mem Wc memc e q v /\
  ablocks B lyc Sc = ablocks B ly S /\
  (Nat.succ d <= PjGrammar.MAXD)%nat /\
  rest_atR tb text p1 = PjGrammar.skip (tl (rest_atR tb text p)) /\
  pi_cur (rc := rc) (cp := cp) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B)
    B regs0 e q v text len tb d lyc Sc Hpc Wc memc p1 Lam peak cnt fail ran most own /\
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) (rdW Wc memc) (prh_lin Lam) o v 0 0 0 0 [] [] /\
  rd_room (cp := cp) (RL := RL) Sc (prhPi_gtrace d o (rest_atR tb text p)).

(* the registers the head leaves: the pinned set, plus s4 = q + 8 and s7 = shadow (q + 8) *)
Definition hd_regs_out (regs0 regs' : bvmap 5 word) (q v : Z) (o : bool) : Prop :=
  pi_regs regs' q v o /\ getr regs' 21 = w64 (-1) /\
  spZ regs' = spZ regs0 - PI_FRAME /\ getr regs' 3 = getr regs0 3 /\ getr regs' 4 = getr regs0 4.

Lemma hd_rest_len : forall tb text p p1 len,
  Z.of_nat (length tb) = len -> 0 < text -> text <= p < text + len -> text <= p1 <= text + len ->
  rest_atR tb text p1 = PjGrammar.skip (tl (rest_atR tb text p)) ->
  (length (rest_atR tb text p1) + 1 <= length (rest_atR tb text p))%nat.
Proof.
intros tb text p p1 len Hlen Ht0 Hp Hp1 Hy.
rewrite Hy. unfold rest_atR in *.
pose proof (PjGrammar.skip_len (tl (skipn (Z.to_nat (p - text)) tb))) as H1.
pose proof (length_skipn (Z.to_nat (p - text)) tb) as H2.
destruct (skipn (Z.to_nat (p - text)) tb) as [|b rr] eqn:HE; cbn [tl length] in *; lia.
Qed.

(* the prologue and skip_ws allocate nothing: with no event and no block, the record's block move and byte bound
   hold from the entry blocks (pi_head_pre's ablocks equality) and the journal's frames (own = []) *)
Lemma hd_blocks_nil : forall ly S Hp (W : world SEGS) mem md regs0 e q v lyc Sc Hpc Wc memc mdc k WS x,
  pi_ajR (rc := rc) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf)
    ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS ->
  ablocks B lyc Sc = ablocks B ly S ->
  rd_blocks_move (cp := cp) B ly S lyc Sc [] [] x d /\ blocks_bytes Sc <= blocks_bytes S + prh_held (cp := cp) [] /\
  Ledger.lsum [] = PjGrammar.held [].
Proof.
intros ly S Hp W mem md regs0 e q v lyc Sc Hpc Wc memc mdc k WS x HJ HAB.
unfold pi_ajR in HJ. pose proof (ajxR_frs HJ) as HFR. cbn [app] in HFR.
split.
- unfold rd_blocks_move. split; [intros a kk Hin; destruct Hin|].
  split; [cbn [prhReader_ab map app]; rewrite HAB; apply Permutation_refl|].
  split; [rewrite HFR; apply Permutation_refl|].
  cbn [hpeakR]. lia.
- split; [|reflexivity].
  unfold prh_held. cbn [PjGrammar.held PjGrammar.calls]. rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S), HAB. lia.
Qed.

(* pi_cur is a reader predicate: it survives a memory with the same restricted reader *)
Lemma hd_cur_rdeq : forall (regs0 : bvmap 5 word) e q v text len tb dd lyc Sc Hpc (Wc : world SEGS) memc memc' pc
  Lamc peakc cntc failc ranc most own,
  rdW Wc memc' = rdW Wc memc ->
  pi_cur (rc := rc) (cp := cp) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B)
    B regs0 e q v text len tb dd lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc most own ->
  pi_cur (rc := rc) (cp := cp) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B)
    B regs0 e q v text len tb dd lyc Sc Hpc Wc memc' pc Lamc peakc cntc failc ranc most own.
Proof.
intros regs0 e q v text len tb dd lyc Sc Hpc Wc memc memc' pc Lamc peakc cntc failc ranc most own Heq H.
unfold pi_cur, src_rd, bytes_at, prh_ledger, prh_glob, prh_most, prh_own, prh_hblock, aview in H |- *.
rewrite Heq. exact H.
Qed.

(* the member loop arm: the byte is not the closer (or the cursor is at the end) *)
Lemma hd_mk_loop : forall fx0 ly S Hp (W : world SEGS) mem md ch CTX regs0 e q v (o : bool) text len tb p Lam
  peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k WS0 p1 (regs regs' : bvmap 5 word) memc' mdc',
  pi_ajR (rc := rc) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf)
    ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc' mdc' k WS0 -> YCbqGwild.wbudget CW 0 WS0 ->
  hd_data fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc
    regs p1 ->
  rdW Wc memc' = rdW Wc memc -> YAkMemnorm.memnorm SEGS memc' ->
  hd_regs_out regs0 regs' q v o ->
  match rest_atR tb text p1 with [] => True | c :: _ => c <> PjGrammar.closer o end ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfg_at (fx := fx) SEGS (VAL A_TEXT + PIAT PI_O_LOOP) regs' memc' mdc')
    (fpostWFbm (fx := fx0) (rc := rc) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK
      (YCbqGwild.wbudget CW 0) (STK_parse_items (PI := prh_img_B) d) e (rd_fp q v) regs0 ly S Hp W mem md
      (pi_post (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
         B ly S d o tb text len p q v Lam peak cnt fail ran most own kr)).
Proof.
intros fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k
  WS0 p1 regs regs' memc' mdc' HJ HWS HD MEQ HMN' HR Hne.
destruct HD as (Hfp & Hent & HPB & HLV & Hfr & HAB & Hdm & Hy & HCUR & HCONT & HRM).
destruct HR as (Hrg & R21 & Hsp & H3 & H4).
pose proof (pi_ent_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hent) as (HIN0 & _ & _ & _ & _ & _ & Hplt & _ & Hcnt0).
pose proof HCUR as (HIN & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HIN as (_ & _ & _ & _ & _ & Ht0 & _ & Hple & Hlen & _ & _ & _).
pose proof HIN0 as (_ & _ & _ & _ & _ & _ & _ & Hple0 & _).
assert (AGRt : pi_agr (fun _ => True) (rdW Wc memc) (rdW Wc memc')) by (intros a _; rewrite MEQ; reflexivity).
assert (HLn : (length (rest_atR tb text p1) + 1 <= length (rest_atR tb text p))%nat)
  by (apply (hd_rest_len tb text p p1 len Hlen Ht0 ltac:(lia) ltac:(lia) Hy)).
apply (HLOOP fx fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
  lyc Sc Hpc Wc memc' mdc' k regs' WS0 HJ HWS).
unfold pi_loop_pre.
split; [exact Hfp|]. split; [exact Hent|].
split; [exact HMN'|].
split.
{ pose proof Hfr as (Fsp & F3 & F4 & _).
  apply (pi_frame_kept (fun _ => True) regs0 regs regs' W mem Wc memc memc' e q v Hfr
    ltac:(lia) ltac:(rewrite H3, F3; reflexivity) ltac:(rewrite H4, F4; reflexivity) AGRt);
  intros a Ha; try (intros _); exact I. }
split; [exact Hrg|]. split; [exact R21|].
exists (2 * length (rest_atR tb text p) + 2)%nat, 0%nat, 0%nat, [], 0, 0, [], p1, [], [], [], Lam, peak, cnt, fail, ran.
split; [exact (hd_cur_rdeq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MEQ HCUR)|].
split; [lia|].
split; [rewrite MEQ; exact HCONT|].
split; [constructor|].
split; [intros b x Hb; destruct Hb|].
split; [cbn [pi_sblk kids_blkR keys_blkR app]; apply Permutation_refl|].
split; [lia|].
split; [apply (hd_cont_loop d o (rest_atR tb text p) (rest_atR tb text p1) Hdm Hy Hne)|].
split.
{ pose proof (prh_ledger_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as (Hl0 & _ & Hc0 & _).
  unfold pi_led. apply hd_move_id; lia. }
destruct (hd_blocks_nil ly S Hp W mem md regs0 e q v lyc Sc Hpc Wc memc' mdc' k WS0 (rest_atR tb text p) HJ HAB)
  as (HBM0 & HBB0 & HLH0).
split; [exact HBM0|].
(* no call, no event: the position and live requests over the empty prefix trace are the head's *)
split; [exact (PItems_posb.pi_posb_eq S Sc Sc [] eq_refl HPB)|].
split; [exact (PItems_posb.pi_live_eq _ _ _ [] (Permutation_refl _) HLV)|].
split; [exact HBB0|]. split; [reflexivity|]. split; [exact HLH0|].
split; [exact (hd_room_loop Sc d o (rest_atR tb text p) (rest_atR tb text p1) _ 0 0
  (hd_cont_loop d o (rest_atR tb text p) (rest_atR tb text p1) Hdm Hy Hne) HRM)|].
(* THE BATCH KIT'S INVARIANTS at n = 0: no call yet (the granted prefix [] []), cap = 0 = ncap 0, no member, and the free
   list [] with the kit's jfl from the empty container (jf_cont's loop arm) *)
split; [unfold pi_grant; reflexivity|].
split; [reflexivity|].
split; [unfold pi_ncaps; exact I|].
exists []. split.
- intros _ nn _. exists []. cbn [PRH_PjOrder.pf_oitemsR map]. split; [split; reflexivity | reflexivity].
- exact (hd_frees_loop d o (rest_atR tb text p) (rest_atR tb text p1) Hdm Hy Hne).
Qed.

End hd2.

(* ---- the two closer lemmas: PItems_pres.v's pi_close_spec and pi_close2_spec at image B ---- *)
Lemma cl_spec_gen : forall {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world (@pa_segs rc B_prog_listing (@PI_prog_B rc)) -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) (CTX0 CW : list (list Z)) (HL : Z),
  AR_laws_x (@pa_segs rc B_prog_listing (@PI_prog_B rc)) B ARx HL ->
  pi_epi_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    (PL := PL_prog_B) B ARx SK d ->
  forall off, (off = PI_O_CLOSE \/ off = PI_O_CLOSE2) ->
  forall (fxc fx0 : YK11.FPState) ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs WS0,
  pi_ajR (rc := rc) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK
    (wle' (@pa_segs rc B_prog_listing (@PI_prog_B rc)) YGcfRehidePost.RZ_cf)
    ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 -> YCbqGwild.wbudget CW 0 WS0 ->
  pi_close_pre (fx := fxc) (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs CTX0 CW ->
  pi_goalR (fx := fxc) (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    B ARx SK (wle' (@pa_segs rc B_prog_listing (@PI_prog_B rc)) YGcfRehidePost.RZ_cf)
    fx0 ly S Hp W mem md regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr off Wc memc mdc regs CW.
Proof.
intros rc ci cp RL B ARx SK d CTX0 CW HL LAWS HEPI off Hoff fxc fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam
  peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs WS0 HJ HWS HPRE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pi_stk_nonneg d) as HSTK.
pose proof HPRE as (Hfp & Hent & HMN & Hfr & Hrg & pc & ok & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & t & r
  & H10 & HJR & Hrest & HLG & HRM & HMV & HBM & HPB & HLV & HBB & HLH & HIN & HND & HPL & HLS & HRA & HFO & HNC).
pose proof (pi_ent_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hent) as (_ & Hsq & Hqe & HSRC & _).
destruct HSRC as (_ & Ht4 & Htc & _ & _ & _).
pose proof HIN as (Vp0 & Ve0 & Vd0 & Hrw0 & Hq8 & Ht0 & Htl & Hple & Hlen & HG & Hdqt & Hd032).
pose proof HJ as HJ0. unfold pi_ajR in HJ0.
pose proof HJ0 as (HARc & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HLlo & HLhi & _).
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
assert (Z1 : YM05.alloc_ceiling <= ly_stk_lo lyc) by (rewrite HLlo; lia).
assert (Z2 : ly_stk_lo lyc <= spZ regs0) by (rewrite HLlo; lia).
assert (Z3 : spZ regs0 + e <= 2 ^ 47) by lia.
destruct (cl_at_bounds B ARx HL LAWS lyc Sc Hpc Wc memc mdc Lam' peak' cnt' fail' ran' most own regs0 e v HARc HLG HPL
  Z1 Z2 Z3) as [Hv0 Hv1].
assert (Zpc : 4096 <= pc <= 2 ^ 47 - 2) by lia.
assert (Zd : (d < 32)%nat) by lia.
unfold pi_goalR.
(* the closer makes no allocator call: the epilogue's budget is the pre's WS0, at the post's wbudget CW 0 *)
apply (cl_core (fx := fxc) B ARx SK d HL LAWS HEPI off fx0 ly S Hp W mem md regs0 e q v o (YCbqGwild.wbudget CW 0)
  (pi_post (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
     B ly S d o tb text len p q v Lam peak cnt fail ran most own kr)
  lyc Sc Hpc Wc memc mdc k WS0 regs pc Hoff HJ HWS Hfp HMN Hfr Hrg H10 Vp0 Vd0 Hrw0 Hq8 Zpc Zd Hsq Hqe HRA).
- apply cl_post_stable.
- intros memf mdf AGR Vq Vd WR regs' H10'.
  eapply cl_close_data; try eassumption; lia.
Qed.

Theorem pi_close_holds : forall {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world (@pa_segs rc B_prog_listing (@PI_prog_B rc)) -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) (CTX0 CW : list (list Z)) (HL : Z),
  AR_laws_x (@pa_segs rc B_prog_listing (@PI_prog_B rc)) B ARx HL ->
  pi_epi_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    (PL := PL_prog_B) B ARx SK d ->
  pi_close_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    (PL := PL_prog_B) B ARx SK d CTX0 CW.
Proof.
intros rc ci cp RL B ARx SK d CTX0 CW HL LAWS HEPI.
unfold pi_close_spec. intros fxc fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
  lyc Sc Hpc Wc memc mdc k regs WS0 HJ HWS HPRE.
exact (cl_spec_gen B ARx SK d CTX0 CW HL LAWS HEPI PI_O_CLOSE (or_introl eq_refl) fxc fx0 ly S Hp W mem md ch CTX regs0 e q
  v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs WS0 HJ HWS HPRE).
Qed.

Theorem pi_close2_holds : forall {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world (@pa_segs rc B_prog_listing (@PI_prog_B rc)) -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) (CTX0 CW : list (list Z)) (HL : Z),
  AR_laws_x (@pa_segs rc B_prog_listing (@PI_prog_B rc)) B ARx HL ->
  pi_epi_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    (PL := PL_prog_B) B ARx SK d ->
  pi_close2_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    (PL := PL_prog_B) B ARx SK d CTX0 CW.
Proof.
intros rc ci cp RL B ARx SK d CTX0 CW HL LAWS HEPI.
unfold pi_close2_spec. intros fxc fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
  lyc Sc Hpc Wc memc mdc k regs WS0 HJ HWS HPRE.
exact (cl_spec_gen B ARx SK d CTX0 CW HL LAWS HEPI PI_O_CLOSE2 (or_intror eq_refl) fxc fx0 ly S Hp W mem md ch CTX regs0 e q
  v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs WS0 HJ HWS HPRE).
Qed.

(* the byte the run reads at the cursor *)
Lemma hd_nth_skipn : forall (l : list Z) kk b rest, skipn kk l = b :: rest -> nth kk l 0 = b.
Proof.
induction l as [|x l IH]; intros [|kk] b rest H; cbn in H; try discriminate.
- injection H as -> ->. reflexivity.
- cbn. exact (IH kk b rest H).
Qed.


(* a run whose regions have no writable window leaves the reader pointwise unchanged *)
Lemma hd_meq_of : forall {fx : YK11.FPState} E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall r0, In r0 rs -> YP09.r_whi r0 <= YP09.r_wlo r0) ->
  mrestrict H m' = mrestrict H m.
Proof.
intros fx E rs H m m' HFr Hro. apply functional_extensionality. intros x. apply HFr.
intros (r0 & Hin & Hr). pose proof (Hro r0 Hin). lia.
Qed.


Lemma hd_regs_out_of : forall (regs0 regs' : bvmap 5 word) q v (o : bool),
  getr regs' 9 = w64 q -> getr regs' 19 = w64 v -> getr regs' 18 = w64 (if o then 1 else 0) ->
  getr regs' 8 = w64 (q + 16) -> getr regs' 20 = w64 (q + 8) -> getr regs' 26 = w64 SHADOW_OFF ->
  getr regs' 27 = w64 (pi_sh q) -> getr regs' 25 = w64 (pi_sh (q + 16)) -> getr regs' 23 = w64 (pi_sh (q + 8)) ->
  getr regs' 21 = w64 (-1) -> spZ regs' = spZ regs0 - PI_FRAME -> getr regs' 3 = getr regs0 3 ->
  getr regs' 4 = getr regs0 4 -> hd_regs_out regs0 regs' q v o.
Proof. intros. unfold hd_regs_out, pi_regs. repeat split; assumption. Qed.

Section hd3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation VAL := (@pa_val rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation PIAT := (@PI_AT rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable d : nat.
Variable CTX0 : list (list Z).
Variable CW : list (list Z).
Variable HL : Z.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Hypothesis HEPI : pi_epi_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing)
  (PA := PI_prog_B) (PL := PL_prog_B) B ARx SK d.
Hypothesis HLOOP : pi_loop_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing)
  (PA := PI_prog_B) (PL := PL_prog_B) B ARx SK d CTX0 CW.

(* the empty-container arm: the byte at the cursor IS the closer, so the model answers jret (mk o [], r) with no
   event, the ledger does not move, and the node is the empty container: its free order is [] (jf_cont's closer
   arm) and its capacity word is 0 = ncap 0 *)
Lemma hd_mk_close : forall (fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md ch CTX regs0 e q v (o : bool) text len tb p Lam
  peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k WS0 p1 (regs regs' : bvmap 5 word) memc' mdc' r,
  pi_ajR (rc := rc) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf)
    ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc' mdc' k WS0 -> YCbqGwild.wbudget CW 0 WS0 ->
  hd_data (fx := fx) B d CTX0 CW fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc regs p1 ->
  rdW Wc memc' = rdW Wc memc -> YAkMemnorm.memnorm SEGS memc' ->
  hd_regs_out regs0 regs' q v o ->
  getr regs' 10 = w64 p1 ->
  rest_atR tb text p1 = PjGrammar.closer o :: r ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfg_at (fx := fx) SEGS (VAL A_TEXT + PIAT PI_O_CLOSE) regs' memc' mdc')
    (fpostWFbm (fx := fx0) (rc := rc) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK
      (YCbqGwild.wbudget CW 0) (STK_parse_items (PI := prh_img_B) d) e (rd_fp q v) regs0 ly S Hp W mem md
      (pi_post (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
         B ly S d o tb text len p q v Lam peak cnt fail ran most own kr)).
Proof.
intros fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k
  WS0 p1 regs regs' memc' mdc' r HJ HWS HD MEQ HMN' HR H10 Hcl.
destruct HD as (Hfp & Hent & HPB & HLV & Hfr & HAB & Hdm & Hy & HCUR & HCONT & HRM).
destruct HR as (Hrg & R21 & Hsp & H3 & H4).
pose proof (pi_ent_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hent) as (HIN0 & _ & _ & _ & _ & _ & Hplt & _).
pose proof HCUR as (HIN & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HIN as (_ & _ & _ & _ & _ & Ht0 & _ & Hple & Hlen & _ & _ & _).
pose proof HIN0 as (_ & _ & _ & _ & _ & _ & _ & Hple0 & _).
assert (AGRt : pi_agr (fun _ => True) (rdW Wc memc) (rdW Wc memc')) by (intros a _; rewrite MEQ; reflexivity).
assert (HLn : (length (rest_atR tb text p1) + 1 <= length (rest_atR tb text p))%nat)
  by (apply (hd_rest_len tb text p p1 len Hlen Ht0 ltac:(lia) ltac:(lia) Hy)).
assert (HLr : (length r + 1 <= length (rest_atR tb text p))%nat) by (rewrite Hcl in HLn; cbn [length] in HLn; lia).
pose proof HCONT as (Hh0 & _). change (Z.of_nat 0) with 0 in Hh0.
apply (pi_close_holds B ARx SK d CTX0 CW HL LAWS HEPI fx fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam
  peak cnt fail ran most own kr lyc Sc Hpc Wc memc' mdc' k regs' WS0 HJ HWS).
unfold pi_close_pre.
split; [exact Hfp|]. split; [exact Hent|].
split; [exact HMN'|].
split.
{ pose proof Hfr as (Fsp & F3 & F4 & _).
  apply (pi_frame_kept (fun _ => True) regs0 regs regs' W mem Wc memc memc' e q v Hfr
    ltac:(lia) ltac:(rewrite H3, F3; reflexivity) ltac:(rewrite H4, F4; reflexivity) AGRt);
  intros a Ha; try (intros _); exact I. }
split; [exact Hrg|].
exists p1, [], [], [], [], Lam, peak, cnt, fail, ran, (PjGrammar.mk o []), r.
split; [exact H10|].
split; [exact (hd_cont_close d o (rest_atR tb text p) (rest_atR tb text p1) r Hdm Hy Hcl [])|].
split; [exact Hcl|].
split; [exact (cl_ledger_rdeq B lyc Sc Hpc Wc memc memc' Lam peak cnt fail ran most own MEQ HLG)|].
split; [exact (hd_room_close Sc _ HRM)|].
split.
{ pose proof (prh_ledger_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as (Hl0 & _ & Hc0 & _).
  apply hd_move_id; lia. }
destruct (hd_blocks_nil B ARx SK d ly S Hp W mem md regs0 e q v lyc Sc Hpc Wc memc' mdc' k WS0 (rest_atR tb text p) HJ HAB)
  as (HBM0 & HBB0 & HLH0).
split; [exact HBM0|].
(* no call, no event: the closer's trace is [] and its position and live requests are the head's *)
split; [exact (PItems_posb.pi_posb_eq S Sc Sc [] eq_refl HPB)|].
split; [exact (PItems_posb.pi_live_eq _ _ _ [] (Permutation_refl _) HLV)|].
split; [exact HBB0|]. split; [exact HLH0|].
split; [rewrite MEQ; exact HIN|].
split; [rewrite MEQ; exact (hd_node_empty (rdW Wc memc) (prh_lin Lam) o v HCONT)|].
split; [exact HPLAT|].
split; [cbn [Ledger.lsum]; lia|].
split; [unfold aview; rewrite MEQ; exact HRA|].
(* THE BATCH KIT SOME-ARM CONJUNCTS of the empty container: the free order [] against jf_cont's closer arm, and cap = 0 *)
split.
{ intros _ nn _. exists []. split.
  - rewrite MEQ. exact (PvB_Frees.pvf_zero_foR SEGS (rdW Wc memc) (prh_lin Lam) nn v _ Hh0).
  - rewrite (hd_frees_close d o (rest_atR tb text p) (rest_atR tb text p1) r Hdm Hy Hcl []). reflexivity. }
rewrite MEQ. exact (hd_ncap_empty SEGS (rdW Wc memc) o v _ Hh0).
Qed.

Let RUNTO := PI_RUNTOR (fx := fx) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B) (PI := PI_prog_B)
  B (@prh_pst prh_img_B) ARx LAWS.
(* the same runner carrying the overlay's normality (YAkMemnorm.memnorm) from the run's start memory to its end *)
Let RUNTOI := paj_run_to_x_invR (fx := fx) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B) (PI := PI_prog_B)
  B (@prh_pst prh_img_B) ARx LAWS (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).
Let BR := paj_branchR (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) (wle' SEGS YGcfRehidePost.RZ_cf).

Lemma hd_core : forall (fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md ch CTX regs0 e q v (o : bool)
  text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k (regs : bvmap 5 word) WS0,
  pi_ajR (rc := rc) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf)
    ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 -> YCbqGwild.wbudget CW 0 WS0 ->
  pi_head_pre (fx := fx) (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs CTX0 CW ->
  pi_goalR (fx := fx) (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) fx0 ly S Hp W mem md regs0 e q v o text len tb p d Lam peak cnt fail ran
    most own kr PI_O_HEAD Wc memc mdc regs CW.
Proof.
intros fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k
  regs WS0 HJw HWS HPRE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pi_stk_nonneg d) as HSTK.
pose proof HPRE as (Hfp & Hent & HMN & HPB & HLV & Hfr & R9 & R19 & R18 & R8 & R26 & R27 & R25 & R21 & Hdm & HAB & p1 & Hy
  & HCUR & HCONT & HRM).
pose proof HCUR as (HIN & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HIN as (Vp & Ve & Vdp & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG & Hdqt & Hd032).
pose proof (pi_ent_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hent) as (_ & Hsq & Hqe & _ & _ & _ & Hplt & Hnth & _).
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & _). rewrite Hlen in Htc, Htam, Htra.
pose proof HJw as HJ0. unfold pi_ajR in HJ0.
pose proof HJ0 as (HARc & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
(* THE BUDGETED JOURNAL (the batch kit): the runs take the empty-budget journal rebased at this block's depot; every exit steps
   back to WS0 (YCbqGwild.ajournal_xw_unbase0R, at wle') over HWD: the head makes no allocator call *)
pose proof (ajxR_wild HJ0) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HJ.
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
assert (Hq0 : YM05.alloc_ceiling <= q) by lia.
assert (Hqb : 4096 <= q <= 2 ^ 47 - 24) by lia.
assert (Hp1b : 4096 <= p1 <= 2 ^ 47 - 2) by lia.
assert (Hedb : 4096 <= text + len <= 2 ^ 47 - 1) by lia.
assert (HD : hd_data (fx := fx) B d CTX0 CW fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran
  most own kr lyc Sc Hpc Wc memc mdc regs p1).
{ unfold hd_data. split; [exact Hfp|]. split; [exact Hent|]. split; [exact HPB|]. split; [exact HLV|].
  split; [exact Hfr|]. split; [exact HAB|].
  split; [exact Hdm|]. split; [exact Hy|]. split; [exact HCUR|]. split; [exact HCONT | exact HRM]. }
pose proof Hfr as (Fsp & F3 & F4 & _).
unfold pi_goalR, cfg_at.
destruct (Z_lt_dec p1 (text + len)) as [Hlt | Hge].
- (* THE CURSOR IS ON A BYTE: the closer test decides between the empty container and the member loop *)
  destruct (skipn (Z.to_nat (p1 - text)) tb) as [|c r0] eqn:HSK.
  { exfalso. pose proof (length_skipn (Z.to_nat (p1 - text)) tb) as HLn0. rewrite HSK in HLn0. cbn [length] in HLn0. lia. }
  assert (Hck : nth (Z.to_nat (p1 - text)) tb 0 = c) by (apply (hd_nth_skipn tb _ c r0); exact HSK).
  destruct (HGt (Z.to_nat (p1 - text)) ltac:(lia)) as [Vc0 Hc256].
  rewrite Hck in Vc0, Hc256.
  replace (text + Z.of_nat (Z.to_nat (p1 - text))) with p1 in Vc0 by lia.
  assert (Hyc : rest_atR tb text p1 = c :: r0) by (unfold rest_atR; exact HSK).
  pose proof (hd_st_ok (fx := fx) Wc memc regs q p1 (text + len) c o true (PIAT PI_O_HEAD) R9 R8 R26 R27 R25 R18
    Hqb Hq8 Hp1b Hedb Hc256 ltac:(intros _; lia) Vp Ve ltac:(intros _; exact Vc0)) as HS.
  remember (Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B)
             (Ereg regs [Z_to_bv 64 p1; Z_to_bv 64 (text + len); Z_to_bv 64 c])) as E eqn:HE in HS.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E3 : ew E 3 = getr regs 3) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
  assert (E4 : ew E 4 = getr regs 4) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
  assert (E9 : ew E 9 = Z_to_bv 64 q) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
  assert (E19 : ew E 19 = Z_to_bv 64 v) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
  assert (E21 : ew E 21 = Z_to_bv 64 (-1)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
  assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 p1) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (text + len)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 c) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (U9 : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew E 32) = p1) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = text + len) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E 34) = c) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (D9 : forall x, 0 <= q + x < 2 ^ 64 -> sv_denot E (SOff 9 x) = Z_to_bv 64 (q + x))
    by (intros x Hx; rewrite denot_lit_U, U_SOff, U9, zcanon_id by (unfold M64; lia); reflexivity).
  assert (DQ0 : sv_denot E (SOff 9 0) = Z_to_bv 64 q) by (rewrite D9 by lia; f_equal; lia).
  assert (DQ8 : sv_denot E (SOff 9 8) = Z_to_bv 64 (q + 8)) by (apply D9; lia).
  assert (DQ16 : sv_denot E (SOff 9 16) = Z_to_bv 64 (q + 16)) by (apply D9; lia).
  assert (HQ63 : 0 <= q < 2 ^ 63) by lia.
  assert (HQ63a : 0 <= q + 8 < 2 ^ 63) by lia.
  assert (HQ63b : 0 <= q + 16 < 2 ^ 63) by lia.
  assert (HSB : 0 <= SHADOW_OFF < 2 ^ 32) by (unfold SHADOW_OFF; lia).
  assert (W16 : Z_to_bv 64 (bv_unsigned (ew E 9) + 16) = Z_to_bv 64 (q + 16)) by (rewrite U9; reflexivity).
  assert (W8 : Z_to_bv 64 (bv_unsigned (ew E 9) + 8) = Z_to_bv 64 (q + 8)) by (rewrite U9; reflexivity).
  clear HE.
  assert (SHOK : sh_ok SEGS pi_Bx (hd_SH true) E (rdW Wc memc)).
  { unfold hd_SH. cbn [app]. constructor; [|constructor; [|constructor]].
    - apply (shent_ok_of_range SEGS (w_H Wc) memc E pi_Bx 32 text len p1 0 1 Htra);
      [unfold pi_Bx; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
      | rewrite (U_atom E 32 p1 E32) by lia; reflexivity | lia | lia
      | intros x Hx; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; unfold SHADOW_OFF; lia].
    - apply (shent_ok_of_range SEGS (w_H Wc) memc E pi_Bx 9 q 24 q 0 24 HRA);
      [unfold pi_Bx; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
      | rewrite (U_atom E 9 q E9) by lia; reflexivity | lia | lia | intros x Hx; unfold SHADOW_OFF; lia]. }
  change (w64 (VAL A_TEXT + PIAT PI_O_HEAD)) with (Z_to_bv 64 (VAL A_TEXT + PIAT PI_O_HEAD)).
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_LOOP).
  { unfold ss_hd; cbn [ss_mem]; unfold hd_smem; cbn [app];
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
  assert (MEQ1 : rdW Wc (ms_mem ms) = rdW Wc memc).
  { apply (hd_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
  clear HF HFr HG.
  psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
  + (* p1 >= end: impossible on this arm *)
    exfalso. rewrite branch_geu_U, !U_SOff in Hc. cbn [ew ewset extK Nat.eqb] in Hc.
    rewrite U32, U33, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
    destruct (Z.ltb_spec p1 (text + len)); [discriminate Hc | lia].
  + rewrite branch_geu_U, !U_SOff in Hc. cbn [ew ewset extK Nat.eqb] in Hc.
    rewrite U32, U33, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia). clear Hc.
    destruct o.
    * (* an object: the closer is '}' *)
      paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_LOOP).
      { unfold ss_hd; cbn [ss_mem]; unfold hd_smem; cbn [app];
        repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
      assert (MX2 : rdW Wc (ms_mem ms0) = rdW Wc (ms_mem ms)).
      { apply (hd_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
        repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
      assert (MEQ2 : rdW Wc (ms_mem ms0) = rdW Wc memc) by (rewrite MX2; exact MEQ1).
      clear HF HFr HG.
      psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
      -- (* the byte is '}' : the empty object *)
         rewrite branch_eq_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset extK Nat.eqb] in Hc.
         rewrite U34, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia).
         assert (Hc125 : c = 125) by (destruct (Z.eqb_spec 125 c); [lia | discriminate Hc]). clear Hc.
         paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_CLOSE).
         { unfold ss_hd; cbn [ss_mem]; unfold hd_smem; cbn [app];
           repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
         assert (MX3 : rdW Wc (ms_mem ms1) = rdW Wc (ms_mem ms0)).
         { apply (hd_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
           repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
         assert (MEQ3 : rdW Wc (ms_mem ms1) = rdW Wc memc) by (rewrite MX3; exact MEQ2).
         clear HF HFr HG.
         prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19. prreg HS (18%bv : bv 5) Q18.
         prreg HS (8%bv : bv 5) Q8. prreg HS (20%bv : bv 5) Q20. prreg HS (26%bv : bv 5) Q26.
         prreg HS (27%bv : bv 5) Q27. prreg HS (25%bv : bv 5) Q25. prreg HS (23%bv : bv 5) Q23.
         prreg HS (21%bv : bv 5) Q21. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
         prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10.
         pmkst HS.
         lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
           replace pcw with (w64 (VAL A_TEXT + PIAT PI_O_CLOSE)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
         apply (hd_mk_close fx0 ly S Hp W mem md ch CTX regs0 e q v true text len tb p Lam
           peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k WS0 p1 regs _ _ _ r0
           (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS YGcfRehidePost.RZ_cf)
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD) HWS HD MEQ3 HMN).
         ++ apply hd_regs_out_of;
            [ cbn [ms_regs]; rewrite Q9, E9; reflexivity
            | cbn [ms_regs]; rewrite Q19, E19; reflexivity
            | cbn [ms_regs]; rewrite Q18; reflexivity
            | cbn [ms_regs]; rewrite Q8, U9; reflexivity
            | cbn [ms_regs]; rewrite Q20, U9; reflexivity
            | cbn [ms_regs]; rewrite Q26, E26; reflexivity
            | cbn [ms_regs]; rewrite Q27, (hd_alu_shx _ _ q SHADOW_OFF E9 E26 HQ63 HSB); unfold pi_sh, w64; reflexivity
            | cbn [ms_regs]; rewrite Q25, (hd_alu_shx _ _ (q + 16) SHADOW_OFF W16 E26 HQ63b HSB);
              unfold pi_sh, w64; reflexivity
            | cbn [ms_regs]; rewrite Q23, (hd_alu_shx _ _ (q + 8) SHADOW_OFF W8 E26 HQ63a HSB);
              unfold pi_sh, w64; reflexivity
            | cbn [ms_regs]; rewrite Q21, E21; reflexivity
            | cbn [ms_regs]; unfold spZ in *; rewrite Q2, E2; exact Fsp
            | cbn [ms_regs]; rewrite Q3, E3; exact F3
            | cbn [ms_regs]; rewrite Q4, E4; exact F4 ].
         ++ cbn [ms_regs]. rewrite Q10, E32. reflexivity.
         ++ rewrite Hyc, Hc125. reflexivity.
      -- (* the byte is not '}' : the member loop *)
         rewrite branch_eq_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset extK Nat.eqb] in Hc.
         rewrite U34, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia).
         assert (Hcne : c <> 125) by (destruct (Z.eqb_spec 125 c); [discriminate Hc | lia]). clear Hc.
         paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_LOOP).
         { unfold ss_hd; cbn [ss_mem]; unfold hd_smem; cbn [app];
           repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
         assert (MX3 : rdW Wc (ms_mem ms1) = rdW Wc (ms_mem ms0)).
         { apply (hd_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
           repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
         assert (MEQ3 : rdW Wc (ms_mem ms1) = rdW Wc memc) by (rewrite MX3; exact MEQ2).
         clear HF HFr HG.
         prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19. prreg HS (18%bv : bv 5) Q18.
         prreg HS (8%bv : bv 5) Q8. prreg HS (20%bv : bv 5) Q20. prreg HS (26%bv : bv 5) Q26.
         prreg HS (27%bv : bv 5) Q27. prreg HS (25%bv : bv 5) Q25. prreg HS (23%bv : bv 5) Q23.
         prreg HS (21%bv : bv 5) Q21. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
         prreg HS (4%bv : bv 5) Q4.
         pmkst HS.
         lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
           replace pcw with (w64 (VAL A_TEXT + PIAT PI_O_LOOP)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
         apply (hd_mk_loop B ARx SK d CTX0 CW HLOOP fx0 ly S Hp W mem md ch CTX regs0 e q v true text len tb p Lam
           peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k WS0 p1 regs _ _ _
           (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS YGcfRehidePost.RZ_cf)
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD) HWS HD MEQ3 HMN).
         ++ apply hd_regs_out_of;
            [ cbn [ms_regs]; rewrite Q9, E9; reflexivity
            | cbn [ms_regs]; rewrite Q19, E19; reflexivity
            | cbn [ms_regs]; rewrite Q18; reflexivity
            | cbn [ms_regs]; rewrite Q8, U9; reflexivity
            | cbn [ms_regs]; rewrite Q20, U9; reflexivity
            | cbn [ms_regs]; rewrite Q26, E26; reflexivity
            | cbn [ms_regs]; rewrite Q27, (hd_alu_shx _ _ q SHADOW_OFF E9 E26 HQ63 HSB); unfold pi_sh, w64; reflexivity
            | cbn [ms_regs]; rewrite Q25, (hd_alu_shx _ _ (q + 16) SHADOW_OFF W16 E26 HQ63b HSB);
              unfold pi_sh, w64; reflexivity
            | cbn [ms_regs]; rewrite Q23, (hd_alu_shx _ _ (q + 8) SHADOW_OFF W8 E26 HQ63a HSB);
              unfold pi_sh, w64; reflexivity
            | cbn [ms_regs]; rewrite Q21, E21; reflexivity
            | cbn [ms_regs]; unfold spZ in *; rewrite Q2, E2; exact Fsp
            | cbn [ms_regs]; rewrite Q3, E3; exact F3
            | cbn [ms_regs]; rewrite Q4, E4; exact F4 ].
         ++ rewrite Hyc. cbn [PjGrammar.closer]. exact Hcne.
    * (* an array: the closer is ']' *)
      paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_LOOP).
      { unfold ss_hd; cbn [ss_mem]; unfold hd_smem; cbn [app];
        repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
      assert (MX2 : rdW Wc (ms_mem ms0) = rdW Wc (ms_mem ms)).
      { apply (hd_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
        repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
      assert (MEQ2 : rdW Wc (ms_mem ms0) = rdW Wc memc) by (rewrite MX2; exact MEQ1).
      clear HF HFr HG.
      psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
      -- (* the byte is not ']' : the member loop *)
         rewrite branch_ne_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset extK Nat.eqb] in Hc.
         rewrite U34, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia).
         assert (Hcne : c <> 93) by (destruct (Z.eqb_spec 93 c); [discriminate Hc | lia]). clear Hc.
         paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_LOOP).
         { unfold ss_hd; cbn [ss_mem]; unfold hd_smem; cbn [app];
           repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
         assert (MX3 : rdW Wc (ms_mem ms1) = rdW Wc (ms_mem ms0)).
         { apply (hd_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
           repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
         assert (MEQ3 : rdW Wc (ms_mem ms1) = rdW Wc memc) by (rewrite MX3; exact MEQ2).
         clear HF HFr HG.
         prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19. prreg HS (18%bv : bv 5) Q18.
         prreg HS (8%bv : bv 5) Q8. prreg HS (20%bv : bv 5) Q20. prreg HS (26%bv : bv 5) Q26.
         prreg HS (27%bv : bv 5) Q27. prreg HS (25%bv : bv 5) Q25. prreg HS (23%bv : bv 5) Q23.
         prreg HS (21%bv : bv 5) Q21. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
         prreg HS (4%bv : bv 5) Q4.
         pmkst HS.
         lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
           replace pcw with (w64 (VAL A_TEXT + PIAT PI_O_LOOP)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
         apply (hd_mk_loop B ARx SK d CTX0 CW HLOOP fx0 ly S Hp W mem md ch CTX regs0 e q v false text len tb p Lam
           peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k WS0 p1 regs _ _ _
           (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS YGcfRehidePost.RZ_cf)
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD) HWS HD MEQ3 HMN).
         ++ apply hd_regs_out_of;
            [ cbn [ms_regs]; rewrite Q9, E9; reflexivity
            | cbn [ms_regs]; rewrite Q19, E19; reflexivity
            | cbn [ms_regs]; rewrite Q18; reflexivity
            | cbn [ms_regs]; rewrite Q8, U9; reflexivity
            | cbn [ms_regs]; rewrite Q20, U9; reflexivity
            | cbn [ms_regs]; rewrite Q26, E26; reflexivity
            | cbn [ms_regs]; rewrite Q27, (hd_alu_shx _ _ q SHADOW_OFF E9 E26 HQ63 HSB); unfold pi_sh, w64; reflexivity
            | cbn [ms_regs]; rewrite Q25, (hd_alu_shx _ _ (q + 16) SHADOW_OFF W16 E26 HQ63b HSB);
              unfold pi_sh, w64; reflexivity
            | cbn [ms_regs]; rewrite Q23, (hd_alu_shx _ _ (q + 8) SHADOW_OFF W8 E26 HQ63a HSB);
              unfold pi_sh, w64; reflexivity
            | cbn [ms_regs]; rewrite Q21, E21; reflexivity
            | cbn [ms_regs]; unfold spZ in *; rewrite Q2, E2; exact Fsp
            | cbn [ms_regs]; rewrite Q3, E3; exact F3
            | cbn [ms_regs]; rewrite Q4, E4; exact F4 ].
         ++ rewrite Hyc. cbn [PjGrammar.closer]. exact Hcne.
      -- (* the byte is ']' : the empty array *)
         rewrite branch_ne_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset extK Nat.eqb] in Hc.
         rewrite U34, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia).
         assert (Hc93 : c = 93) by (destruct (Z.eqb_spec 93 c); [lia | discriminate Hc]). clear Hc.
         paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_CLOSE).
         { unfold ss_hd; cbn [ss_mem]; unfold hd_smem; cbn [app];
           repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
         assert (MX3 : rdW Wc (ms_mem ms1) = rdW Wc (ms_mem ms0)).
         { apply (hd_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
           repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
         assert (MEQ3 : rdW Wc (ms_mem ms1) = rdW Wc memc) by (rewrite MX3; exact MEQ2).
         clear HF HFr HG.
         prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19. prreg HS (18%bv : bv 5) Q18.
         prreg HS (8%bv : bv 5) Q8. prreg HS (20%bv : bv 5) Q20. prreg HS (26%bv : bv 5) Q26.
         prreg HS (27%bv : bv 5) Q27. prreg HS (25%bv : bv 5) Q25. prreg HS (23%bv : bv 5) Q23.
         prreg HS (21%bv : bv 5) Q21. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
         prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10.
         pmkst HS.
         lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
           replace pcw with (w64 (VAL A_TEXT + PIAT PI_O_CLOSE)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
         apply (hd_mk_close fx0 ly S Hp W mem md ch CTX regs0 e q v false text len tb p Lam
           peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k WS0 p1 regs _ _ _ r0
           (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS YGcfRehidePost.RZ_cf)
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD) HWS HD MEQ3 HMN).
         ++ apply hd_regs_out_of;
            [ cbn [ms_regs]; rewrite Q9, E9; reflexivity
            | cbn [ms_regs]; rewrite Q19, E19; reflexivity
            | cbn [ms_regs]; rewrite Q18; reflexivity
            | cbn [ms_regs]; rewrite Q8, U9; reflexivity
            | cbn [ms_regs]; rewrite Q20, U9; reflexivity
            | cbn [ms_regs]; rewrite Q26, E26; reflexivity
            | cbn [ms_regs]; rewrite Q27, (hd_alu_shx _ _ q SHADOW_OFF E9 E26 HQ63 HSB); unfold pi_sh, w64; reflexivity
            | cbn [ms_regs]; rewrite Q25, (hd_alu_shx _ _ (q + 16) SHADOW_OFF W16 E26 HQ63b HSB);
              unfold pi_sh, w64; reflexivity
            | cbn [ms_regs]; rewrite Q23, (hd_alu_shx _ _ (q + 8) SHADOW_OFF W8 E26 HQ63a HSB);
              unfold pi_sh, w64; reflexivity
            | cbn [ms_regs]; rewrite Q21, E21; reflexivity
            | cbn [ms_regs]; unfold spZ in *; rewrite Q2, E2; exact Fsp
            | cbn [ms_regs]; rewrite Q3, E3; exact F3
            | cbn [ms_regs]; rewrite Q4, E4; exact F4 ].
         ++ cbn [ms_regs]. rewrite Q10, E32. reflexivity.
         ++ rewrite Hyc, Hc93. reflexivity.
- (* THE CURSOR IS AT THE END OF THE TEXT: no byte, straight into the member loop *)
  assert (Hpe : p1 = text + len) by lia.
  assert (Hyn : rest_atR tb text p1 = []) by (unfold rest_atR; apply skipn_all2; lia).
  pose proof (hd_st_ok (fx := fx) Wc memc regs q p1 (text + len) 0 o false (PIAT PI_O_HEAD) R9 R8 R26 R27 R25 R18
    Hqb Hq8 Hp1b Hedb ltac:(lia) ltac:(intros X; discriminate X) Vp Ve ltac:(intros X; discriminate X)) as HS.
  remember (Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B)
             (Ereg regs [Z_to_bv 64 p1; Z_to_bv 64 (text + len); Z_to_bv 64 0])) as E eqn:HE in HS.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E3 : ew E 3 = getr regs 3) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
  assert (E4 : ew E 4 = getr regs 4) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
  assert (E9 : ew E 9 = Z_to_bv 64 q) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
  assert (E19 : ew E 19 = Z_to_bv 64 v) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
  assert (E21 : ew E 21 = Z_to_bv 64 (-1)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
  assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 p1) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (text + len)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (U9 : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew E 32) = p1) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = text + len) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (D9 : forall x, 0 <= q + x < 2 ^ 64 -> sv_denot E (SOff 9 x) = Z_to_bv 64 (q + x))
    by (intros x Hx; rewrite denot_lit_U, U_SOff, U9, zcanon_id by (unfold M64; lia); reflexivity).
  assert (DQ0 : sv_denot E (SOff 9 0) = Z_to_bv 64 q) by (rewrite D9 by lia; f_equal; lia).
  assert (DQ8 : sv_denot E (SOff 9 8) = Z_to_bv 64 (q + 8)) by (apply D9; lia).
  assert (DQ16 : sv_denot E (SOff 9 16) = Z_to_bv 64 (q + 16)) by (apply D9; lia).
  assert (HQ63 : 0 <= q < 2 ^ 63) by lia.
  assert (HQ63a : 0 <= q + 8 < 2 ^ 63) by lia.
  assert (HQ63b : 0 <= q + 16 < 2 ^ 63) by lia.
  assert (HSB : 0 <= SHADOW_OFF < 2 ^ 32) by (unfold SHADOW_OFF; lia).
  assert (W16 : Z_to_bv 64 (bv_unsigned (ew E 9) + 16) = Z_to_bv 64 (q + 16)) by (rewrite U9; reflexivity).
  assert (W8 : Z_to_bv 64 (bv_unsigned (ew E 9) + 8) = Z_to_bv 64 (q + 8)) by (rewrite U9; reflexivity).
  clear HE.
  assert (SHOK : sh_ok SEGS pi_Bx (hd_SH false) E (rdW Wc memc)).
  { unfold hd_SH. cbn [app]. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H Wc) memc E pi_Bx 9 q 24 q 0 24 HRA);
    [unfold pi_Bx; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
    | rewrite (U_atom E 9 q E9) by lia; reflexivity | lia | lia | intros x Hx; unfold SHADOW_OFF; lia]. }
  change (w64 (VAL A_TEXT + PIAT PI_O_HEAD)) with (Z_to_bv 64 (VAL A_TEXT + PIAT PI_O_HEAD)).
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_LOOP).
  { unfold ss_hd; cbn [ss_mem]; unfold hd_smem; cbn [app];
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
  assert (MEQ1 : rdW Wc (ms_mem ms) = rdW Wc memc).
  { apply (hd_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
  clear HF HFr HG.
  psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
  + (* p1 >= end: the member loop with an empty rest *)
    rewrite branch_geu_U, !U_SOff in Hc. cbn [ew ewset extK Nat.eqb] in Hc.
    rewrite U32, U33, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia). clear Hc.
    paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_LOOP).
    { unfold ss_hd; cbn [ss_mem]; unfold hd_smem; cbn [app];
      repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
    assert (MX2 : rdW Wc (ms_mem ms0) = rdW Wc (ms_mem ms)).
    { apply (hd_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
      repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
    assert (MEQ2 : rdW Wc (ms_mem ms0) = rdW Wc memc) by (rewrite MX2; exact MEQ1).
    clear HF HFr HG.
    prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19. prreg HS (18%bv : bv 5) Q18.
    prreg HS (8%bv : bv 5) Q8. prreg HS (20%bv : bv 5) Q20. prreg HS (26%bv : bv 5) Q26.
    prreg HS (27%bv : bv 5) Q27. prreg HS (25%bv : bv 5) Q25. prreg HS (23%bv : bv 5) Q23.
    prreg HS (21%bv : bv 5) Q21. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
    prreg HS (4%bv : bv 5) Q4.
    pmkst HS.
    lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
      replace pcw with (w64 (VAL A_TEXT + PIAT PI_O_LOOP)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
    apply (hd_mk_loop B ARx SK d CTX0 CW HLOOP fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam
      peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k WS0 p1 regs _ _ _
      (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS YGcfRehidePost.RZ_cf)
         _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD) HWS HD MEQ2 HMN).
    * apply hd_regs_out_of;
      [ cbn [ms_regs]; rewrite Q9, E9; reflexivity
      | cbn [ms_regs]; rewrite Q19, E19; reflexivity
      | cbn [ms_regs]; rewrite Q18; reflexivity
      | cbn [ms_regs]; rewrite Q8, U9; reflexivity
      | cbn [ms_regs]; rewrite Q20, U9; reflexivity
      | cbn [ms_regs]; rewrite Q26, E26; reflexivity
      | cbn [ms_regs]; rewrite Q27, (hd_alu_shx _ _ q SHADOW_OFF E9 E26 HQ63 HSB); unfold pi_sh, w64; reflexivity
      | cbn [ms_regs]; rewrite Q25, (hd_alu_shx _ _ (q + 16) SHADOW_OFF W16 E26 HQ63b HSB); unfold pi_sh, w64; reflexivity
      | cbn [ms_regs]; rewrite Q23, (hd_alu_shx _ _ (q + 8) SHADOW_OFF W8 E26 HQ63a HSB); unfold pi_sh, w64; reflexivity
      | cbn [ms_regs]; rewrite Q21, E21; reflexivity
      | cbn [ms_regs]; unfold spZ in *; rewrite Q2, E2; exact Fsp
      | cbn [ms_regs]; rewrite Q3, E3; exact F3
      | cbn [ms_regs]; rewrite Q4, E4; exact F4 ].
    * rewrite Hyn. exact I.
  + (* p1 < end: impossible at the end of the text *)
    exfalso. rewrite branch_geu_U, !U_SOff in Hc. cbn [ew ewset extK Nat.eqb] in Hc.
    rewrite U32, U33, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
    destruct (Z.ltb_spec p1 (text + len)); [lia | discriminate Hc].
Qed.

End hd3.

(* ---- PItems_pres.v's pi_head_spec at image B ---- *)
Theorem pi_head_holds : forall {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world (@pa_segs rc B_prog_listing (@PI_prog_B rc)) -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (d : nat) (CTX0 CW : list (list Z)) (HL : Z),
  AR_laws_x (@pa_segs rc B_prog_listing (@PI_prog_B rc)) B ARx HL ->
  pi_epi_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    (PL := PL_prog_B) B ARx SK d ->
  pi_loop_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    (PL := PL_prog_B) B ARx SK d CTX0 CW ->
  pi_head_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    (PL := PL_prog_B) B ARx SK d CTX0 CW.
Proof.
intros rc ci cp RL B ARx SK d CTX0 CW HL LAWS HEPI HLOOP.
unfold pi_head_spec. intros fxc fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
  lyc Sc Hpc Wc memc mdc k regs WS0 HJ HWS HPRE.
exact (hd_core (fx := fxc) B ARx SK d CTX0 CW HL LAWS HEPI HLOOP fx0 ly S Hp W mem md ch CTX regs0 e q v o
  text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs WS0 HJ HWS HPRE).
Qed.

Print Assumptions pi_head_holds.
Print Assumptions pi_close_holds.
Print Assumptions pi_close2_holds.
Print Assumptions hd_mk_loop.
Print Assumptions hd_mk_close.
Print Assumptions cl_core.
