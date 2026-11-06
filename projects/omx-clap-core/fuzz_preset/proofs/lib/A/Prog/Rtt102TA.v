(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/pj_string_seg_ent.v, with its module names changed; 1582 of its 1646 lines of code are new or changed and 650 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Rtt102EA.v, with its module names changed; 1674 of its 1781 lines of code are new or changed and 1539 lines of the source are left out. *)
(* STATUS: stretch T of round_trip_text at image A' ON THE BATCH KIT'S CUT (the batch kit head 7cdbb61b5fa0, the
   re-fitted shared layer 80a1d52c32c7) WITH the stack-premise text head 4b8f95c0455c (the text's appended premise
   astack_up_x), CONDITIONAL: rtt_seg_t_A_cond (end of file) proves Rtt102Cut.RTT_SEG_T from ONE tagged premise,
   RTT_T_TRACE_AT (C-TXTRACE: the tx realloc site's universe fact, owner a Theorem Labs lane / the image binding of B; the
   caller's stack above the entry sp is now rtt_pre's own, Rtt102Cut.rtt_pre_up), over the Section hypotheses listed
   at Section f (the KIT's two tx texts PRH_FnTx.ttx_put_specX / ttx_value_specX at the cut, the memnorm
   __asan_memset row, the engine laws, and the image stand-ins). K0-AMR8 is DISCHARGED by the engine (AR_laws_x's
   alx_blocks_hi).
   R-FORM PORT (the stretch T port's head on the wave-0 contract 448ecd157e57, Step-2 draft tip 7ed43ad5685e): the
   stretch is proved at YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf and every journal is at RZW := YA0nH.wle' SEGS RZ_cf
   (CrtFit's WLE contract): the tx calls through YCbqGwild.aj_call_xWb_spR (the texts' posts are fpostWbmR at
   wle'), the memset row by aj_intrin_at_xmR lifted by YA0nH.SRr_SRr', the runs by the _invR runners. The tx texts'
   `(length rp_os <= 4)%nat` is Rtt102Cut.rtt_pre_os4. No fact of the walk is read across the world relation: the
   base across a call is the callee journal's aview clauses and ARx at the new state. *)
(* fuzz_preset, image A' (asan, pin 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): STRETCH T of the walk of
   round_trip_text on the #102 pins - the inlined rendered() (merged fuzz_preset.c:477-492) between Rtt102Cut.v's
   cuts RT_PJW (entry + 304, A' 0x84a9c) and RT_TXE (entry + 388, A' 0x84af0):
     mv s6, a0;  addi a0, s1, 0x18; li a2, 0x20; mv a1, zero; jal __asan_memset;
     a1 := "";    addi a0, s1, 0x18; mv a2, zero;  jal tx_put;
     addi a0, s1, 0x18; mv a1, s4; mv a2, s5; mv a3, zero; jal tx_value;
     beqz s5, +0x18;  a1 := "\n"; addi a0, s1, 0x18; li a2, 1; jal tx_put.
   The statement is Rtt102Cut.v's RTT_SEG_T at L := A_prog_listing, PA := PI_prog_A, PI := prh_img_A. Lane
   WalkRtt102.RttT. The image-generic half (the model and the transport) is lib/A/Prog/Rtt102TGlue.v.
   rule 24: no function proved (kind: segment lemma); the function-level gate is CLEARED for round_trip_text
   (proof-index round_trip_text, EXIT=0): only plain (lib/Prog) and ubsan (lib/U/Prog) released proofs exist,
   neither consumable here. Written new; released files cited for content only.

   NUMERALS. DERIVED: 13196 (= 4 * A_prog_slot AS_round_trip_text, the function's offset from the listing base),
   the seam offsets 304 / 324 / 344 / 364 / 388 inside the function (4 * the slot inside it: A' 0x84a9c / 0x84ab0 /
   0x84ac4 / 0x84ad8 / 0x84af0), 70080 / 70112 (the two literals' offsets from pa_val (A_OBJ 2), the listing's
   PAddHi resolution: .rodata 0x211c0 and 0x211e0), atom indices. LENGTH: 0, 1 (the two literals' lengths), 24 / 32
   (the record at s1 + 0x18 and the memset's size), 16 / 160 (the frame and the realignment, through Rtt102Cut.RT_R).
   WORD: the register numbers. No ADDRESS literal: every code address is pa_sigma / pa_val of PAImg_prog.v. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW YGcallMx YGcallMxmn YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild YGcallStackUp.
(* the re-hiding move (CrtFit's WLE contract): the step relation YA0nH.SRr' segs RZ_cf, its world relation
   RZW := YA0nH.wle' segs RZ_cf (every journal below), its step lemmas (YSRrG), all used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YImgTop YGcfNames FCiface YGcfRoomKeep YGcfRoomLive YGcfTreeVis YGcallHull YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterSpec WriterApp
PjWriteHyp TxModel TvSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_Reader PRH_FnCheck CfImgA CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnTx PRH_FnWriter PRH_FnEx
PRH_Supply.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1ImgA S1Ledger Rtt102Cut
Rtt102TGlue.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* a register a run did not write: its value is the segment's start value (S10TxString.v's tskeep) *)
Ltac rttkeep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.

(* ---- the seams inside round_trip_text (DERIVED: 4 * the slot inside the function; A' addresses in the header) ---- *)
Definition RTT_T_MSET : Z := 324.   (* 0x84ab0: __asan_memset returned *)
Definition RTT_T_PUT1 : Z := 344.   (* 0x84ac4: the "" tx_put returned *)
Definition RTT_T_TXV  : Z := 364.   (* 0x84ad8: tx_value returned; `beqz s5` *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
#[local] Existing Instance prh_img_A.
Context {SK : YI16.sink_head} {RL : PrhRoomLive}.
#[local] Notation PA := (PI_prog_A).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
#[local] Notation STKR := (@STK_round_trip_text prh_img_A).

(* round_trip_text's offset from the listing's base, and the two literals rendered() hands tx_put *)
Definition RTT_PC_A : Z := 4 * Z.of_nat (A_prog_slot AS_round_trip_text).
Definition RTT_LIT0_A : Z := VAL (A_OBJ 2) + 70080.   (* .rodata 0x211c0: "" *)
Definition RTT_LITNL_A : Z := VAL (A_OBJ 2) + 70112.  (* .rodata 0x211e0: "\n" *)

Lemma RTT_PC_val : BASE + RTT_PC_A = SIGMA AS_round_trip_text.
Proof. vm_compute. reflexivity. Qed.

(* the two literals' bytes, read off the image's read-only segments *)
Lemma rtt_t_lit0_rom : forall j, (j < 0)%nat ->
  option_map (fun bb : byte => bv_unsigned bb) (seg_rom SEGS (Z_to_bv 64 (RTT_LIT0_A + Z.of_nat j)))
    = Some (nth j (@nil Z) 0).
Proof. intros j Hj. exfalso. lia. Qed.

Lemma rtt_t_litnl_rom : forall j, (j < 1)%nat ->
  option_map (fun bb : byte => bv_unsigned bb) (seg_rom SEGS (Z_to_bv 64 (RTT_LITNL_A + Z.of_nat j)))
    = Some (nth j [10] 0).
Proof. intros j Hj. destruct j as [|j]; [vm_compute; reflexivity | exfalso; cbn in Hj; lia]. Qed.

(* the empty literal needs no image binding: kept_img at length 0 is two bounds on its address *)
Lemma rtt_t_lit0_img : forall B, kept_img (PA := PA) B RTT_LIT0_A 0.
Proof.
intros B. unfold kept_img. split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|].
intros a Ha. exfalso. lia.
Qed.

Lemma rtt_t_lit_rng : 65536 <= RTT_LIT0_A /\ RTT_LIT0_A < 2 ^ 31 /\ 65536 <= RTT_LITNL_A /\ RTT_LITNL_A < 2 ^ 31.
Proof. split; [vm_compute; discriminate|]. split; [vm_compute; reflexivity|].
split; [vm_compute; discriminate | vm_compute; reflexivity]. Qed.

(* ---- the four runs of the stretch: none of them touches memory, so each is a FRESH symbolic state with no
   region and no shadow entry, and the only facts are the branch condition of the last one ---- *)
Definition ss_T (pc : Z) (G : facts) : sstate := mkSS pc cur_atoms [] None G.
Definition gf_none : facts := mkFacts [] [] [].
(* `beqz s5` at + 364: s5 is pretty, which rtt_pre pins to 0 or 1 *)
Definition gf_s5 (c : branch_cond) : facts := mkFacts [] (map (fun v => mkAC c (SOff (xr 21) 0) (SLit v)) [0]) [].

Lemma rtt_t_ss_ok : forall (fxc : YK11.FPState) (regs0 rg : bvmap 5 word) (pc : Z) (G : facts)
  (Wc : world SEGS) (memc : word -> option byte),
  facts_ok (TE regs0 rg []) G ->
  st_ok_pi SEGS VAL (TE regs0 rg []) (ss_T pc G)
    (restrict (w_H Wc) (@YK11.mkst fxc rg (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs0 rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxc regs0 rg pc G Wc memc HG. split; [|apply Forall_nil].
apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | exact HG].
Qed.

Lemma rtt_t_facts_none : forall (regs0 rg : bvmap 5 word), facts_ok (TE regs0 rg []) gf_none.
Proof. intros regs0 rg. split; [exact I | split; [exact I | exact I]]. Qed.

Lemma rtt_t_s5_atom : forall (regs0 rg : bvmap 5 word) (v : Z),
  getr rg 21 = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew (TE regs0 rg []) (xr 21)) = v.
Proof.
intros regs0 rg v Hv Hr. unfold xr. rewrite (te_cur regs0 rg [] 21%bv 21) by reflexivity.
rewrite Hv. apply unsigned_lit_small. lia.
Qed.

Lemma rtt_t_facts_s5_eq : forall (regs0 rg : bvmap 5 word) (v : Z),
  getr rg 21 = w64 v -> 0 <= v < 2 ^ 64 -> v = 0 -> facts_ok (TE regs0 rg []) (gf_s5 BC_EQ).
Proof.
intros regs0 rg v Hv Hr Hc. pose proof (rtt_t_s5_atom regs0 rg v Hv Hr) as X.
split; [exact I|]. split; [|exact I].
exact (ts_conds_eq _ (xr 21) v [0] X ltac:(repeat constructor; lia)).
Qed.

Lemma rtt_t_facts_s5_ne : forall (regs0 rg : bvmap 5 word) (v : Z),
  getr rg 21 = w64 v -> 0 <= v < 2 ^ 64 -> v <> 0 -> facts_ok (TE regs0 rg []) (gf_s5 BC_NE).
Proof.
intros regs0 rg v Hv Hr Hc. pose proof (rtt_t_s5_atom regs0 rg v Hv Hr) as X.
split; [exact I|]. split; [|exact I].
exact (ts_conds_ne _ (xr 21) v [0] X ltac:(repeat constructor; lia)).
Qed.

(* ---- the stack allowances of the three callees inside round_trip_text's own (PrhImg facts, by computation) ---- *)
Lemma rtt_t_stk_A :
  4096 + 176 <= STKR /\
  0 <= @STK_tx_put prh_img_A /\ @STK_tx_put prh_img_A + 176 <= STKR /\
  0 <= @STK_tx_value prh_img_A DOC_D /\ @STK_tx_value prh_img_A DOC_D + 176 <= STKR.
Proof. repeat split; vm_compute; discriminate. Qed.

Lemma rtt_t_frame_A : @pi_frame prh_img_A F_round_trip_text = 176.
Proof. vm_compute. reflexivity. Qed.

(* alloc.c's statics are image bytes, and are not read-only (S1ImgA.v, image A) *)
Lemma rtt_t_pst_img : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Proof. exact pst_in_img_A. Qed.
Lemma rtt_t_pst_ro : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a.
Proof. exact pst_not_ro_A. Qed.

(* set_depot moves the depot and no other field (the journal's entry in Rtt102Cut.rtt_J's form, the entry state with
   its depot moved to the current state's: YCbqGwild.ajournal_xw_rebaseR) *)
Lemma rtt_t_sd_frames : forall d s, frames (set_depot d s) = frames s.
Proof. reflexivity. Qed.
Lemma rtt_t_sd_ablocks : forall (B0 : asyms) d ly s, ablocks B0 ly (set_depot d s) = ablocks B0 ly s.
Proof. reflexivity. Qed.
Lemma rtt_t_sd_sd : forall d d' s, set_depot d (set_depot d' s) = set_depot d s.
Proof. reflexivity. Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).
(* the allocator's laws at the instance's head (engine fold; the instance discharges them) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the hidden head is at least a granule wide (PRH_Base.v prh_head_wide; owner the instance, cf_head = 16 at the
   preset instance): a ledger block's head and user bytes are one live block of positive size *)
Hypothesis HW : prh_head_wide.
(* MARKED STAND-IN (owned by the kit, the image binding of B; WalkS10's ruling 2026-10-29): the zero-shadow ranges are
   granule-aligned *)
Hypothesis zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
(* the image's shadow is mapped at every ARx state. DISCHARGED at ARx := ARxs by the cf instance owner's
   tfib_img_shadow_vis_cf (lib/A/AImgShadowVisCf.v:32 on the preset allocator branch at fee5c13e19d0,
   YGcfAmx2.v:47's img_shadow_vis_cf) + the projection of ARcf, at ci := CfImg_A, the bounds IMG_LO / IMG_TOP =
   cf_img_lo / cf_img_top = 0x10000 / 0x600000 by reflexivity. It stays a NAMED hypothesis here because this
   file's ARx is the generic Variable, not ARxs, so there is no ARcf to project (WalkRtt102's ruling,
   2026-10-29 17:1xZ). *)
(* the owner's instance witness, stated verbatim beside the citation (it holds by eq_refl: YImgTop.v:12-13 and
   CfImgA.v:60,62 are the same two literals, 0x10000 / 0x600000) *)
Example ib : IMG_LO = @cf_img_lo CfImg_A /\ IMG_TOP = @cf_img_top CfImg_A := conj eq_refl eq_refl.
Hypothesis img_shadow_vis_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* MARKED STAND-IN (owned by the kit, image A's Tfib_const_shadow; PRH_FnTx.v TX-LIT): the newline literal rendered() hands
   tx_put is kept by route (a) at its length 1. The empty literal needs none (rtt_t_lit0_img). *)
Hypothesis rtt_t_litnl_img : kept_img (PA := PA) B RTT_LITNL_A 1.
(* ---- the callee texts, QUANTIFIED OVER THE FLOAT STATE (the three calls are made at the cut's fxc): the KIT's texts
   on the Step-2 draft tip (lib/A/PRH_FnTx.v), BUDGETED (fpostWbmR at wle' SEGS RZ_cf, the re-hiding move, at
   wbudget_if f0 [] (length (prhtx_evs ..)), with the guarded room, the run's `(length rp_os <= 4)%nat` and the
   consumer-window entry premises) and carrying the dead-arm post conjunct `f0 = 0 -> f1 = 0`
   (K0-DEAD-TXPUT / K0-DEAD-TXVALUE) ---- *)
Variable CTX0 : list (list Z).
Hypothesis TXPUT : forall fx', PRH_FnTx.ttx_put_specX (fx := fx') (L := A_prog_listing) (PA := PA) B ARx SK CTX0.
Hypothesis TXVAL : forall fx', PRH_FnTx.ttx_value_specX (fx := fx') (L := A_prog_listing) (PA := PA) B ARx SK CTX0
  DOC_D.
(* the runtime row rendered() calls: __asan_memset, in the memnorm-keeping form (YGcallMxmn.v's table) *)
Hypothesis AIM : forall fx', aintrin_realizes_xm (fx := fx') SEGS B ARx OSet (SIGMA AS___asan_memset).

Section g.
(* ---- the cut's data: the text's variables at the entry, the stretch below, and the state at RT_PJW ---- *)
Variable D : rtt_in (PA := PA).
Hypothesis HPRE : rtt_pre (fx := fx) B ARx CTX0 D.
Variable fxc : YK11.FPState.
(* the allocator state at RT_PJW *)
Variable S0 : astate.
Variables (pos F : Z).
(* pj_write's outcome, fixed for the whole stretch *)
Variables (q : Z) (Lamw : list (Z * Z)) (peakw cntw ranw : Z) (wab : list (Z * Z)).
(* every block live at the entry is one of the writer's blocks (rtt_wout: wab = the text block :: the entry's) *)
Hypothesis HWAB : forall x, In x (ablocks B (ri_ly D) (ri_S D)) -> In x wab.
(* every harness block of the entry is one of the ledger's after the write (rtt_wout: Lamw = (q, capw) :: ri_Lam D) *)
Hypothesis HLAMW : forall x, In x (ri_Lam D) -> In x Lamw.
#[local] Notation sp0 := (ri_sp D).
#[local] Notation sp1 := (RT_R (ri_sp D)).
#[local] Notation rect := (RT_R (ri_sp D) + RT_REC).
(* the journal's entry at a state S of the stretch: the function's entry state with its depot moved to S's
   (Rtt102Cut.rtt_J) *)
#[local] Notation EJ x := (set_depot (st_depot x) (ri_S D)).

(* ---- what every point of the stretch carries, except the record and the buffer: the journal from the entry with
   its depot moved to the current state's (Rtt102Cut.rtt_J), and g_most and g_own_ran_out as LEDGER FIELDS
   (prh_ledger .. ran most own), so the ledger's own travels with the base. ---- *)
Definition rtt_t_base (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
  (md : Model) (kj own : Z) : Prop :=
  AJ STKR sp0 (ri_FP D) (ri_ly D) (EJ S) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)]
    ly S Hp W mem md kj /\
  frame_addr ly RT_CID pos = F /\
  rtt_frame D ly S W mem pos /\ rtt_saved D W mem /\
  (YAkMemnorm.memnorm SEGS (ri_mem D) -> YAkMemnorm.memnorm SEGS mem) /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) /\
  rtt_room D S /\
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin (ri_Lam D)) (ri_doc D) (ri_t D) (ri_D D) /\
  PRH_FnWriter.prhWriter_tree_vis W mem (ri_D D) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (ri_doc D) 56 /\
  ck_in_frame ly S (ri_doc D) 56 /\
  rtt_copy_kept D W mem /\
  rtt_led B D ly S Hp W mem Lamw peakw cntw ranw own /\
  (q <> 0 -> bytes_at W mem q (ri_tb D ++ [0])) /\
  (* constant over the stretch, carried so that every transport can name the blocks it must keep *)
  (q <> 0 -> exists capw, In (q, capw) Lamw /\ Z.of_nat (length (ri_tb D)) < capw) /\
  (forall bk, In bk (ri_D D) -> In bk Lamw) /\
  (ri_copy D <> 0 -> ck_in_frame ly S (ri_copy D) 56).

(* ---- the record at s1 + 24 and the buffer it names: the blocks are the writer's, plus the buffer once it exists ---- *)
Definition rtt_t_buf (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
  (b len cap f own : Z) (txt : list Z) : Prop :=
  PRH_FnTx.prhtx_rec (PA := PA) W mem rect b len cap f /\
  PRH_FnTx.prhtx_inv (PA := PA) B Lamw ly S W mem b len cap txt /\
  (f = 0 -> own = 0) /\ (f = 0 \/ f = 1) /\
  Z.of_nat (length txt) = len /\ 0 <= cap /\
  (cap = 0 -> Permutation (ablocks B ly S) wab) /\
  (0 < cap -> Permutation (ablocks B ly S) ((b, cap) :: wab)) /\
  blocks_bytes S <= blocks_bytes S0 + cap.

(* ---- the registers the prologue fixed, plus s5 = pretty and s6 = q (set by the stretch's first instruction) ---- *)
Definition rtt_t_bregs (rg : bvmap 5 word) : Prop :=
  getr rg 2 = w64 sp1 /\ getr rg 8 = w64 sp0 /\ getr rg 9 = w64 sp1 /\
  getr rg 18 = w64 F /\ getr rg 19 = w64 (ri_copy D) /\ getr rg 20 = w64 (ri_doc D) /\
  getr rg 25 = w64 (shadow_addr F) /\ getr rg 26 = w64 F /\
  getr rg 3 = w64 (as_gp B) /\ getr rg 4 = w64 (as_tp B) /\
  getr rg 21 = w64 (ri_pretty D) /\ getr rg 22 = w64 q.

Lemma rtt_t_bregs_pres : forall rg rg', rtt_t_bregs rg -> aregs_preserved rg rg' -> rtt_t_bregs rg'.
Proof.
intros rg rg' (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4 & R21 & R22) HP. unfold rtt_t_bregs.
rewrite (ts_ap rg rg' 2%bv HP) by ts_cs. rewrite (ts_ap rg rg' 8%bv HP) by ts_cs.
rewrite (ts_ap rg rg' 9%bv HP) by ts_cs. rewrite (ts_ap rg rg' 18%bv HP) by ts_cs.
rewrite (ts_ap rg rg' 19%bv HP) by ts_cs. rewrite (ts_ap rg rg' 20%bv HP) by ts_cs.
rewrite (ts_ap rg rg' 25%bv HP) by ts_cs. rewrite (ts_ap rg rg' 26%bv HP) by ts_cs.
rewrite (ts_ap rg rg' 3%bv HP) by ts_cs. rewrite (ts_ap rg rg' 4%bv HP) by ts_cs.
rewrite (ts_ap rg rg' 21%bv HP) by ts_cs. rewrite (ts_ap rg rg' 22%bv HP) by ts_cs.
repeat split; assumption.
Qed.

(* ---- the stretch's arithmetic: the realigned sp, the stack window, and what lies below the allocator ceiling ---- *)
Lemma rtt_t_nums : forall ly S Hp W mem md kj own, rtt_t_base ly S Hp W mem md kj own ->
  sp0 mod 16 = 0 /\ YM05.alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STKR <= sp0 /\
  sp0 <= ly_stk_hi ly /\ ly_stk_hi ly <= 2 ^ 47 /\ sp0 <= ly_top ly /\ ly_top ly <= ly_stk_hi ly /\
  sp0 - 176 <= sp1 /\ sp1 <= sp0 - 160 /\ sp1 mod 32 = 0 /\ YM05.alloc_ceiling <= sp1 - ESTACK.
Proof.
intros ly S Hp W mem md kj own (HJ & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof rtt_t_stk_A as (HS1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
rewrite Etop, Eslo, Eshi.
unfold RT_R, RT_FRAME.
split; [exact Hal16|]. split; [exact Hceil|]. split; [exact Hslo|]. split; [exact Hshi|].
split; [exact H47|]. split; [exact Htop2|]. split; [exact Htop|].
Z.div_mod_to_equations; lia.
Qed.

(* a frame that holds 56 bytes is at least a granule-multiple wide (fs_frame_bytes cid = 64 << cid) *)
Lemma rtt_t_fs_mod8 : forall cid, 56 <= fs_frame_bytes cid -> fs_frame_bytes cid mod 8 = 0.
Proof.
intros cid H. destruct (Z_lt_le_dec cid 0) as [Hn | Hp].
- exfalso. unfold fs_frame_bytes in H. replace cid with (- (- cid)) in H by lia.
  rewrite Z.shiftl_div_pow2 in H by lia.
  replace (- - - cid) with (- cid) in H by lia.
  assert (Hge2 : 2 <= 2 ^ (- cid)).
  { replace 2 with (2 ^ 1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
  assert (Hq : 0 < 2 <= 2 ^ (- cid)) by (split; lia).
  pose proof (Z.div_le_compat_l 64 2 (2 ^ (- cid)) ltac:(lia) Hq) as Hle.
  change (64 / 2) with 32 in Hle.
  assert (Hc : 56 <= 32) by (eapply Z.le_trans; [exact H | exact Hle]).
  lia.
- rewrite fs_frame_bytes_eq by exact Hp. replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by ring.
  apply Z.mod_mul. lia.
Qed.

(* ---- THE BASE ACROSS A STEP that keeps the bytes the base names: the thirteen saved words, the bytes and shadow of
   every fake frame of S, the bytes (head included) of every block the ledger lists; the journal, the read-only view,
   the room, g_most and the ledger at the new state are the step's own facts ---- *)
Lemma rtt_t_base_tr : forall ly S Hp W mem md kj own ly' S' Hp' (W' : world SEGS) mem' md' kj',
  rtt_t_base ly S Hp W mem md kj own ->
  AJ STKR sp0 (ri_FP D) (ri_ly D) (EJ S') (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)]
    ly' S' Hp' W' mem' md' kj' ->
  (forall a, sp0 - 104 <= a < sp0 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  (forall cid p a, In (cid, p) (frames S) ->
     (in_zr a (frame_rng ly (cid, p)) \/ in_zr a (shadow_addr (frame_addr ly cid p), fs_frame_bytes cid / 8)) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  (forall a k i, In (a, k) Lamw -> 0 <= i < k + cf_head ->
     aview SEGS (w_H W') mem' (a - cf_head + i) = aview SEGS (w_H W) mem (a - cf_head + i)) ->
  (YAkMemnorm.memnorm SEGS (ri_mem D) -> YAkMemnorm.memnorm SEGS mem') ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W') mem') ->
  rtt_room D S' ->
  rtt_led B D ly' S' Hp' W' mem' Lamw peakw cntw ranw own ->
  rtt_t_base ly' S' Hp' W' mem' md' kj' own.
Proof.
intros ly S Hp W mem md kj own ly' S' Hp' W' mem' md' kj' HB HJ' KSV KFR KBL HMN HRO HRM HLED'.
pose proof HB as (HJ & HFA & HFR & HSV & HMN0 & HRO0 & HRM0 & HND & HTV & HRA & HCF & HCP & HLED & HQB
  & HQBLK & HDL & HCPF).
pose proof HJ as (HAR & HLY & _ & _ & _ & HFRS & _).
pose proof HJ' as (HAR' & HLY' & _ & _ & _ & HFRS' & _).
pose proof (@cf_head_nonneg cp) as Hh0.
assert (EFS : frames S' = frames S) by (rewrite HFRS, HFRS'; reflexivity).
assert (EF : forall cid p, frame_addr ly' cid p = frame_addr ly cid p).
{ intros cid p. unfold frame_addr.
  destruct HLY as (_ & _ & _ & _ & _ & E6 & _). destruct HLY' as (_ & _ & _ & _ & _ & E6' & _).
  rewrite E6, E6'. reflexivity. }
assert (EFL : forall cid p, flag_addr ly' cid p = flag_addr ly cid p).
{ intros cid p. unfold flag_addr.
  destruct HLY as (_ & _ & _ & _ & _ & E6 & _). destruct HLY' as (_ & _ & _ & _ & _ & E6' & _).
  rewrite E6, E6'. reflexivity. }
(* the frame bytes, and the shadow bytes of any range inside a frame *)
assert (KF : forall cid p a, In (cid, p) (frames S) ->
  frame_addr ly cid p <= a < frame_addr ly cid p + fs_frame_bytes cid ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a).
{ intros cid p a Hin Ha. apply (KFR cid p a Hin). left. unfold in_zr, frame_rng. cbn [fst snd]. lia. }
assert (KFS : forall cid p x, In (cid, p) (frames S) -> 56 <= fs_frame_bytes cid ->
  frame_addr ly cid p <= x < frame_addr ly cid p + fs_frame_bytes cid ->
  aview SEGS (w_H W') mem' (shadow_addr x) = aview SEGS (w_H W) mem (shadow_addr x)).
{ intros cid p x Hin H56 Hx. apply (KFR cid p _ Hin). right.
  destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid p HAR Hin) as (H32 & _).
  pose proof (rtt_t_fs_mod8 cid H56) as H8.
  unfold in_zr, shadow_addr. cbn [fst snd]. Z.div_mod_to_equations. lia. }
(* the document's tree, read in the frames and the blocks the ledger still lists *)
assert (HFOOT : forall x, pj_footR (ri_doc D) (ri_D D) x ->
  aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x /\ writable_at SEGS (mrestrict (w_H W') mem') x).
{ intros x [Hx | (bk & Hbk & Hhold)].
  - destruct HCF as (cid & p & Hin & Hlo & Hhi).
    split; [apply (KF cid p _ Hin); lia|].
    assert (Hin' : In (cid, p) (frames S')) by (rewrite EFS; exact Hin).
    destruct (alx_frames SEGS B ARx LAWS ly' S' Hp' W' mem' md' cid p HAR' Hin') as (_ & _ & Hpr & _).
    rewrite EF in Hpr. apply apresent_writable. exact (proj1 (Hpr x ltac:(lia))).
  - destruct bk as [a kk]. unfold pj_holdsR in Hhold. cbn [fst snd] in Hhold.
    pose proof HLED' as (HL' & _).
    pose proof (prh_ledger_hblock B ly' S' Hp' W' mem' Lamw peakw cntw SIZE_MAXZ ranw a kk (ri_most D) own HL' (HDL (a, kk) Hbk))
      as (Hk & Hab & _ & _ & _).
    split.
    + replace x with (a - cf_head + (x - a + cf_head)) by lia. apply (KBL a kk); [exact (HDL _ Hbk) | lia].
    + assert (Hrq : kk + cf_head <= req_size (kk + cf_head)) by (apply rtt_t_req_ge; lia).
      destruct (alx_blocks SEGS B ARx LAWS ly' S' Hp' W' mem' md' _ _ HAR' Hab) as (_ & _ & _ & _ & Hpr & _).
      apply apresent_writable. exact (proj1 (Hpr x ltac:(lia))). }
split; [exact HJ'|]. split; [rewrite EF; exact HFA|].
split.
{ (* the fake frame: the frame list is the journal's, its flag word and its bytes are kept *)
  pose proof HFR as (E1 & E2 & E3 & E4).
  assert (Hin1 : In (RT_CID, pos) (frames S)) by (rewrite E1; left; reflexivity).
  assert (Hfb : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
  split; [rewrite EFS; exact E1|]. split; [exact E2|]. split.
  - rewrite EF, EFL, <- E3. apply ts_rdword_keep. intros j Hj.
    apply (KF RT_CID pos _ Hin1). unfold RT_FLAGP. rewrite Hfb. lia.
  - intros a Ha. rewrite EF in Ha.
    assert (Hin' : In (RT_CID, pos) (frames S')) by (rewrite EFS; exact Hin1).
    destruct (alx_frames SEGS B ARx LAWS ly' S' Hp' W' mem' md' RT_CID pos HAR' Hin') as (_ & _ & Hpr & _).
    rewrite EF in Hpr. exact (proj1 (Hpr a Ha)). }
split.
{ (* the thirteen saved words lie in [sp0 - 104, sp0) *)
  intros j Hj. eapply ts_vm_av; [|exact (HSV j Hj)].
  intros i Hi. apply KSV. lia. }
split; [exact HMN|]. split; [exact HRO|]. split; [exact HRM|].
split.
{ eapply rtt_t_node_keep; [exact HND | |];
  intros x Hx; [exact (proj1 (HFOOT x Hx)) | exact (proj2 (HFOOT x Hx))]. }
split.
{ pose proof HLED' as (HL' & _).
  exact (rtt_t_tvis_lam B ARx LAWS HW ly' S' Hp' W' mem' md' Lamw peakw cntw SIZE_MAXZ ranw (ri_most D) own
    W mem (ri_D D) HAR' HL' HDL HTV). }
split.
{ eapply range_addressable_agree; [|exact HRA]. intros x Hx.
  destruct HCF as (cid & p & Hin & Hlo & Hhi).
  unfold shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x).
  apply (KFS cid p x Hin); lia. }
split.
{ destruct HCF as (cid & p & Hin & Hlo & Hhi). exists cid, p. rewrite EFS, EF. auto. }
split.
{ intros Hc a Ha. rewrite <- (HCP Hc a Ha).
  destruct (HCPF Hc) as (cid & p & Hin & Hlo & Hhi). apply (KF cid p _ Hin). lia. }
split; [exact HLED'|].
split.
{ intros Hq. destruct (HQBLK Hq) as (capw & Hin & Hlt).
  eapply ts_garr_av; [|exact (HQB Hq)]. intros j Hj.
  rewrite length_app in Hj. cbn [length] in Hj.
  replace (q + Z.of_nat j) with (q - cf_head + (Z.of_nat j + cf_head)) by lia.
  apply (KBL q capw); [exact Hin | lia]. }
split; [exact HQBLK|]. split; [exact HDL|].
intros Hc. destruct (HCPF Hc) as (cid & p & Hin & Hlo & Hhi). exists cid, p. rewrite EFS, EF. auto.
Qed.

(* ---- the memset's write set, and everything a cut carries, lies off it: the record and the runtime's own
   ESTACK window are on the REAL STACK at or above the allocator ceiling, while the image, every harness block,
   every fake frame and all their shadow bytes lie below it; the thirteen saved words are on the real stack but
   above the record ---- *)
Lemma rtt_t_base_keep_mem : forall ly S Hp W mem md kj own mem' md' kj',
  rtt_t_base ly S Hp W mem md kj own ->
  AJ STKR sp0 (ri_FP D) (ri_ly D) (EJ S) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)]
    ly S Hp W mem' md' kj' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rect <= a < rect + 32) -> ~ (sp1 - ESTACK <= a < sp1) ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (YAkMemnorm.memnorm SEGS (ri_mem D) -> YAkMemnorm.memnorm SEGS mem') ->
  rtt_t_base ly S Hp W mem' md' kj' own.
Proof.
intros ly S Hp W mem md kj own mem' md' kj' HB HJ' HK HMN.
pose proof (rtt_t_nums ly S Hp W mem md kj own HB) as
  (Hal16 & Hceil & Hslo & Hshi & H47 & Htop2 & Htop & Hs1a & Hs1b & Hs1m & Hces).
pose proof HB as (HJ & _ & _ & _ & _ & HRO & HRM & _ & _ & _ & _ & _ & HLED & _).
pose proof HJ as (HAR & _).
pose proof ASAN_CEIL_range as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
pose proof rtt_t_stk_A as (HSK1 & HSP0 & HSP1 & HSV0 & HSV1).
pose proof (@cf_head_nonneg cp) as Hh0.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hrect : rect = sp1 + 24) by reflexivity.
assert (KLO : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply HK; unfold ASAN_CEIL in *; lia. }
assert (KIMG : forall a, in_img SEGS a -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply KLO. pose proof (@pa_segs_low _ _ PA a Ha). unfold kLowMemEnd in *.
  unfold ASAN_CEIL in *. lia. }
assert (KBLK : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a).
{ intros p n a Hin Ha.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md p n HAR Hin) as (_ & H4096 & Hc & _).
  apply KLO. unfold ASAN_CEIL in *. lia. }
assert (KBL : forall a k i, In (a, k) Lamw -> 0 <= i < k + cf_head ->
  aview SEGS (w_H W) mem' (a - cf_head + i) = aview SEGS (w_H W) mem (a - cf_head + i)).
{ intros a k i Hin Hi. pose proof HLED as (HL & _).
  pose proof (prh_ledger_hblock B ly S Hp W mem Lamw peakw cntw SIZE_MAXZ ranw a k (ri_most D) own HL Hin)
    as (Hk & Hab & _ & _ & _).
  apply (KBLK (a - cf_head) (k + cf_head) _ Hab).
  assert (Hrq : k + cf_head <= req_size (k + cf_head)) by (apply rtt_t_req_ge; lia). lia. }
assert (KPST : forall a, Exists (in_zr a) PST -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KIMG, rtt_t_pst_img, Ha).
pose proof HW as HW8. unfold prh_head_wide in HW8.
assert (KBL8 : forall a k i, In (a, k) Lamw -> 0 <= i < 8 ->
  aview SEGS (w_H W) mem' (a - cf_head + i) = aview SEGS (w_H W) mem (a - cf_head + i)).
{ intros a k i Hin Hi. pose proof HLED as (HL & _).
  pose proof (prh_ledger_hblock B ly S Hp W mem Lamw peakw cntw SIZE_MAXZ ranw a k (ri_most D) own HL Hin)
    as (Hk & _ & _ & _ & _).
  apply (KBL a k i Hin). lia. }
assert (HLED' : rtt_led B D ly S Hp W mem' Lamw peakw cntw ranw own).
{ pose proof HLED as (HL & HPK). split; [|exact HPK].
  exact (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem' Lamw peakw cntw SIZE_MAXZ ranw (ri_most D) own HL
    KPST KBL8 (fun a k _ H => H) (Permutation_refl Hp)). }
apply (rtt_t_base_tr ly S Hp W mem md kj own ly S Hp W mem' md' kj' HB HJ').
- intros a Ha. apply HK; unfold ASAN_CEIL in *; lia.
- intros cid p a Hin Ha.
  destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as (_ & HFsep).
  pose proof (proj1 (Forall_forall _ _) HFsep (cid, p) Hin) as (Hlo & Hhi). cbn [fst snd] in Hlo, Hhi.
  apply KLO. unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha.
  destruct Ha as [Ha | Ha]; [unfold ASAN_CEIL in *; lia|].
  unfold shadow_addr, SHADOW_OFF in Ha. pose proof (fs_frame_bytes_nonneg cid).
  assert (frame_addr ly cid p / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold ASAN_CEIL in *; lia).
  assert (0 <= fs_frame_bytes cid / 8 <= 2 ^ 44)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; unfold ASAN_CEIL in *; lia]).
  unfold ASAN_CEIL in *. lia.
- exact KBL.
- exact HMN.
- intros a Hro Hno Her. rewrite KIMG; [exact (HRO a Hro Hno Her)|].
  destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img a Hr)].
- exact HRM.
- exact HLED'.
Qed.

(* ---- the registers before the stretch's first instruction (s6 not yet q; a0 = q) ---- *)
Definition rtt_t_cregs (rg : bvmap 5 word) : Prop :=
  getr rg 2 = w64 sp1 /\ getr rg 8 = w64 sp0 /\ getr rg 9 = w64 sp1 /\
  getr rg 18 = w64 F /\ getr rg 19 = w64 (ri_copy D) /\ getr rg 20 = w64 (ri_doc D) /\
  getr rg 25 = w64 (shadow_addr F) /\ getr rg 26 = w64 F /\
  getr rg 3 = w64 (as_gp B) /\ getr rg 4 = w64 (as_tp B) /\
  getr rg 21 = w64 (ri_pretty D).

(* the memory invariant the runners carry (YSRrMemnorm.v: the keep form of memnorm from the entry) *)
Definition rtt_t_P (m : word -> option byte) : Prop :=
  YAkMemnorm.memnorm SEGS (ri_mem D) -> YAkMemnorm.memnorm SEGS m.
Lemma rtt_t_PLAW : srr_inv_laws SEGS rtt_t_P.
Proof. exact (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) (ri_mem D) (srr_inv_laws_memnorm_k SEGS)). Qed.

(* g_own_ran_out is one of alloc.c's statics, an image byte (S1ImgA.v) *)
Lemma rtt_t_own_pst : forall i, (i < pi_gz_own_ran_out)%nat ->
  Exists (in_zr (pi_g_own_ran_out + Z.of_nat i)) PST.
Proof.
intros i Hi. unfold prh_pst. apply Exists_exists. exists (pi_g_own_ran_out, Z.of_nat pi_gz_own_ran_out).
split; [cbn [In]; auto 10 | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* ---- STEP 0 (+304 .. +320, then `jal __asan_memset` with a0 = s1 + 24, a1 = 0, a2 = 32): s6 := q and the
   32-byte record zeroed on round_trip_text's real stack (aj_intrin_at_xmR, YGcallMxmn.v's table: the memnorm keep;
   the row's plain SRr lifted into SRr' by YA0nH.SRr_SRr') ---- *)
Lemma rtt_t_step0 : forall ly S Hp W mem md kj own rg (K : world SEGS -> config -> Prop),
  rtt_t_base ly S Hp W mem md kj own -> rtt_t_cregs rg -> getr rg 10 = w64 q ->
  (forall mem' md' kj' rg',
     rtt_t_base ly S Hp W mem' md' kj' own -> rtt_t_bregs rg' ->
     (forall i, 0 <= i < 32 -> aview SEGS (w_H W) mem' (rect + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (rect <= a < rect + 32) -> ~ (sp1 - ESTACK <= a < sp1) ->
        aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fxc rg' (Z_to_bv 64 (BASE + (RTT_PC_A + RTT_T_MSET)))
       mem' (YK11.seg_rom SEGS)) md') K) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fxc rg (Z_to_bv 64 (BASE + (RTT_PC_A + RT_PJW))) mem
    (YK11.seg_rom SEGS)) md) K.
Proof.
intros ly S Hp W mem md kj own rg K HB HCR Ha0 HK.
pose proof (rtt_t_nums ly S Hp W mem md kj own HB) as
  (Hal16 & Hceil & Hslo & Hshi & H47 & Htop2 & Htop & Hs1a & Hs1b & Hs1m & Hces).
pose proof HB as (HJ & HFA & _ & _ & HMN0 & _).
pose proof HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4 & R21).
pose proof rtt_t_stk_A as (HSK1 & _).
pose proof ASAN_CEIL_range as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
pose proof (@pa_B_ok _ _ PA) as HBASE.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hrect : rect = sp1 + 24) by reflexivity.
destruct (rtt_t_ss_ok fxc (ri_regs D) rg (RTT_PC_A + RT_PJW) gf_none W mem (rtt_t_facts_none _ _)) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE (ri_regs D) rg [])) by apply te_env.
assert (HPM : rtt_t_P mem) by exact HMN0.
pose (RUN := @paj_run_x_invR fxc rc SK A_prog_listing PL PA B PST ARx _ LAWS rtt_t_P rtt_t_PLAW RZW
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
paj_run_tok_x_invR RUN HS HJ SHOK HPM (0, 0).
{ cbv [ss_T ss_mem]. apply awr_ok_nil. }
assert (Hm : forall x, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem x).
{ intros x. apply HFr. intros (r & Hr & _). cbv [ss_T ss_mem In] in Hr. destruct Hr. }
assert (Hav : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a; apply aview_eq_of; apply Hm).
(* the base at the run's memory: the run wrote nothing *)
pose proof (rtt_t_base_keep_mem ly S Hp W mem md kj own (ms_mem ms) _ _ HB HJ (fun a _ _ _ => Hav a) HPM) as HB1.
pose proof HB1 as (_ & _ & _ & _ & HMN1 & _).
(* the registers the run set, and the ones it kept *)
prreg HS (22%bv : bv 5) Q22. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
assert (Z2 : getr (ms_regs ms) 2 = getr rg 2) by rttkeep HS.
assert (Z8 : getr (ms_regs ms) 8 = getr rg 8) by rttkeep HS.
assert (Z9 : getr (ms_regs ms) 9 = getr rg 9) by rttkeep HS.
assert (Z18 : getr (ms_regs ms) 18 = getr rg 18) by rttkeep HS.
assert (Z19 : getr (ms_regs ms) 19 = getr rg 19) by rttkeep HS.
assert (Z20 : getr (ms_regs ms) 20 = getr rg 20) by rttkeep HS.
assert (Z25 : getr (ms_regs ms) 25 = getr rg 25) by rttkeep HS.
assert (Z26 : getr (ms_regs ms) 26 = getr rg 26) by rttkeep HS.
assert (Z3 : getr (ms_regs ms) 3 = getr rg 3) by rttkeep HS.
assert (Z4 : getr (ms_regs ms) 4 = getr rg 4) by rttkeep HS.
assert (Z21 : getr (ms_regs ms) 21 = getr rg 21) by rttkeep HS.
assert (X22 : getr (ms_regs ms) 22 = w64 q) by (rewrite Q22; rewrite <- Ha0; te_close).
assert (A41 : ew (TE (ri_regs D) rg []) 41 = w64 sp1) by (rewrite <- R9; te_close).
assert (X10 : getr (ms_regs ms) 10 = w64 rect).
{ rewrite Q10, A41. unfold w64. rewrite unsigned_lit_small by lia. rewrite Hrect. reflexivity. }
assert (X11 : getr (ms_regs ms) 11 = w64 0) by (rewrite Q11; reflexivity).
assert (X12 : getr (ms_regs ms) 12 = w64 32) by (rewrite Q12; reflexivity).
assert (HBR1 : rtt_t_bregs (ms_regs ms)).
{ unfold rtt_t_bregs. rewrite Z2, Z8, Z9, Z18, Z19, Z20, Z25, Z26, Z3, Z4, Z21, X22.
  repeat split; assumption. }
assert (Hspc : spZ (ms_regs ms) = sp0 + (sp1 - sp0)).
{ unfold spZ. rewrite Z2, R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
pmkst HS.
eapply YSRrG.SRr'_bind.
{ (* the row is the plain memnorm row: its run is lifted into SRr' (YA0nH.SRr_SRr'), its journal stays at RZW *)
  apply YA0nH.SRr_SRr'.
  eapply (aj_intrin_at_xmR (fx := fxc) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) RZW
    OSet (SIGMA AS___asan_memset) (AIM fxc) W (ms_regs ms) (ms_mem ms) STKR sp0 (ri_FP D)
    (ri_ly D) (EJ S) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)] ly S Hp _ _
    rect 0 32 (sp1 - sp0) _ HJ).
  - exact X10.
  - exact X11.
  - exact X12.
  - lia.
  - lia.
  - lia.
  - exact Hspc.
  - Z.div_mod_to_equations; lia.
  - lia.
  - rewrite Hes. lia.
  - rewrite Z3. exact R3.
  - rewrite Z4. exact R4.
  - reflexivity.
  - rewrite Q1. apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - intros a Ha. split; [left; lia | lia].
  - unfold amem_range. right. unfold kHighMemBeg, kHighMemEnd. unfold ASAN_CEIL in *. lia.
  - eapply (rtt_t_stk_ra B ARx LAWS); [exact (proj1 HJ) | lia | lia].
  - intros _. eapply (rtt_t_stk_hull B ARx LAWS); [exact (proj1 HJ) | lia | lia].
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres2 & Heff & Hfr2 & Hpres2 & Hmn2).
(* the base at the memset's memory: it wrote the record and its own window only *)
pose proof (rtt_t_base_keep_mem ly S Hp W (ms_mem ms) _ _ own mem2 md2 _ HB1 HJ2
  (fun a Ha H1 H2 => Hfr2 a Ha H1 ltac:(intros H3; apply H2; lia)) (fun H => Hmn2 (HMN1 H))) as HB2.
try rewrite Q1.
apply (HK mem2 md2 _ regs2 HB2).
- exact (rtt_t_bregs_pres _ _ HBR1 HP2).
- intros i Hi. rewrite Heff by lia. reflexivity.
- intros a Ha H1 H2. rewrite (Hfr2 a Ha H1 ltac:(intros H3; apply H2; lia)). apply Hav.
Qed.

(* ---- THE PREMISES EVERY tx_* TEXT ASKS AT A CALL from the rendering, and the facts its post gives back. The call
   is a BUDGETED CALLER-WINDOW call (YCbqGwild.v aj_call_xWb_spR at RZW): the record lies in round_trip_text's own frame,
   so the callee's window is [sp1, sp0), e1 = sp0 - sp1, o = sp1 - sp0 and o + e1 = 0. ---- *)
#[local] Notation DWIN := (ri_sp D - RT_R (ri_sp D)).

Definition rtt_t_cpre (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
  (regsc : bvmap 5 word) (b len cap f own : Z) (txt : list Z) : Prop :=
  fwin ly W regsc mem DWIN /\ PRH_FnTx.prhtx_place (PA := PA) ly S W regsc mem DWIN rect /\
  PRH_FnTx.prhtx_rec (PA := PA) W mem rect b len cap f /\
  PRH_FnTx.prhtx_inv (PA := PA) B Lamw ly S W mem b len cap txt /\
  prh_ledger B ly S Hp W mem Lamw peakw cntw SIZE_MAXZ ranw (ri_most D) own /\
  room_live_cf S /\ arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) /\
  spZ regsc + 64 <= ly_stk_hi ly /\ count_cid 0 (frames S) < fs_frames 0 /\
  blocks_bytes S - cap + PRH_FnTx.LIVE_tx <= LIVE_MAX.

(* ---- the facts of the text's own premises that the rendering's calls need. ONE positional reading of rtt_pre,
   so a change to the text moves one lemma. The run-event premise is the text's own (Rtt102Cut.v:164, the kit's
   ck_rtt_evs over the record model); the rendering's segment comes from it by PRH_Base.prh_run_at_app_iff and
   PRH_Supply.prhtx_evs_r_evs. ---- *)
Lemma rtt_t_pre_facts :
  fpre (fx := fx) B ARx STKR (ri_ly D) (ri_S D) (ri_Hp D) (ri_W D) (ri_regs D) (ri_mem D) (ri_md D) (ri_ch D) /\
  blocks_bytes (ri_S D) + LIVE_round_trip_text (ri_t D) (ri_p D) <= LIVE_MAX /\
  RQ_rtt (ri_t D) (ri_p D) + cf_head < cf_malloc_max /\
  Z.of_nat (length (frames (ri_S D))) <= ck_FRAMES_CAP - FR_round_trip_text /\
  PjWriteHyp.wlen (ri_t D) (ri_p D) + 1 <= 2 ^ 28 /\
  (PjTree.depth (ri_t D) <= 32)%nat /\ (ri_pretty D = 0 \/ ri_pretty D = 1) /\
  prh_run_at ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D)
    (ck_rtt_evs ReaderRes.jr_strtod (ri_t D) (ri_p D) (ri_copy D)).
Proof.
pose proof HPRE as (H1 & _ & _ & _ & _ & _ & _ & H8 & _ & _ & _ & H12 & H13 & _ & _ & _ & H17 & _ & _ &
  H20 & H21 & H22 & _).
split; [exact H1|]. split; [exact H20|]. split; [exact H21|]. split; [exact H22|].
split; [exact H13|]. split; [exact H12|]. split; [exact H8 | exact H17].
Qed.

(* ---- the rendering's own run events, from the text's list: ck_rtt_evs = w_evs ++ r_evs ++ .., and the
   rendering's segment r_evs IS prhtx_evs 0 0 (ck_rtt_ns t p) - the kit's PRH_Supply.v prhtx_evs_r_evs, CITED (the file
   is pin-free at blob d6e52752685a and in the lane base since the rtt102 walk lane f9eda666dd9; the
   earlier explicit-argument form was the workaround for its old red closure through lib/Reusable/YCeh.v) ---- *)
Lemma rtt_t_run_at_r :
  prh_run_at ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D + RT_K_W D)%nat
    (PRH_FnTx.prhtx_evs 0 0 (ck_rtt_ns (ri_t D) (ri_p D))).
Proof.
pose proof rtt_t_pre_facts as (_ & _ & _ & _ & _ & _ & _ & HRA).
unfold ck_rtt_evs, PresetReqAt.rt_text in HRA.
rewrite PRH_Supply.prhtx_evs_r_evs. unfold RT_K_W.
rewrite <- !app_assoc in HRA.
apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in HRA as [_ HRA].
apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in HRA as [HRA _]. exact HRA.
Qed.

(* the shared half of a tx call's premises, from the base and the buffer *)
Lemma rtt_t_cpre_of : forall ly S Hp W mem md kj own b len cap f txt regsc,
  rtt_t_base ly S Hp W mem md kj own -> rtt_t_buf ly S Hp W mem b len cap f own txt ->
  spZ regsc = sp1 ->
  blocks_bytes S0 <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) ->
  rtt_t_cpre ly S Hp W mem regsc b len cap f own txt.
Proof.
intros ly S Hp W mem md kj own b len cap f txt regsc HB HBF Hsp HBB0.
pose proof (rtt_t_nums ly S Hp W mem md kj own HB) as
  (Hal16 & Hceil & Hslo & Hshi & H47 & Htop2 & Htop & Hs1a & Hs1b & Hs1m & Hces).
pose proof HB as (HJ & HFA & HFR & HSV & _ & HRO & HRM & _ & _ & _ & _ & _ & HLED & _).
pose proof HBF as (HREC & HINV & Hf0 & Hf01 & HLEN & Hcap0 & HP0 & HP1 & HBB).
pose proof HJ as (HAR & HLY & _ & _ & _ & HFRS & _ & _ & _ & _ & _ & _ & _ & HPRES & _).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof rtt_t_pre_facts as (HFP & HLIVE & _ & Hfrm & _).
pose proof rtt_t_stk_A as (HSK1 & _).
split.
{ split; [lia|]. split; [Z.div_mod_to_equations; lia|].
  split; [rewrite Hsp, Etop; lia|]. intros a Ha. apply HPRES. rewrite Hsp in Ha. lia. }
split.
{ split; [unfold RT_REC; Z.div_mod_to_equations; lia|].
  split; [rewrite Hsp; unfold RT_REC; lia|]. split; [rewrite Hsp; unfold RT_REC; lia|].
  split.
  - intros a Ha. apply apresent_writable. apply HPRES. unfold RT_REC in Ha. lia.
  - eapply (rtt_t_stk_ra B ARx LAWS); [exact HAR | rewrite Eslo; unfold RT_REC; lia
    | rewrite Eshi; unfold RT_REC; lia]. }
split; [exact HREC|]. split; [exact HINV|].
split; [exact (proj1 HLED)|]. split; [exact HRM|]. split; [exact HRO|].
split; [rewrite Hsp, Eshi; lia|].
split.
{ (* class 0 is tx_string's / tx_value's frame class: the text's frame bound, the rendering's own frame is class 1 *)
  rewrite HFRS, rtt_t_sd_frames. change ([(RT_CID, pos)] ++ frames (ri_S D)) with ((RT_CID, pos) :: frames (ri_S D)).
  cbn [count_cid]. assert (E0 : (RT_CID =? 0) = false) by reflexivity. rewrite E0.
  pose proof (rtt_count_le 0 (frames (ri_S D))) as Hc.
  assert (E2 : fs_frames 0 = 16384) by (vm_compute; reflexivity).
  assert (E1 : ck_FRAMES_CAP - FR_round_trip_text = 29) by (vm_compute; reflexivity). lia. }
(* the live bytes this call may add, from the text's own live budget *)
pose proof (rtt_t_live_parse_nonneg (WriterValue.wdoc (ri_t D) (ri_p D))) as Hpn.
unfold LIVE_round_trip_text in HLIVE. unfold PRH_FnTx.LIVE_tx in *. lia.
Qed.

(* ---- the frame-pointer chain at a call from the rendering: s0 is round_trip_text's entry sp, whose two words
   below it are the saved ra and the caller's s0 (rtt_saved's first two slots) ---- *)
Lemma rtt_t_chain_at : forall ly S Hp W mem md kj own,
  rtt_t_base ly S Hp W mem md kj own ->
  exists ch1, achain ly (aview SEGS (w_H W) mem) sp1 sp0 ch1.
Proof.
intros ly S Hp W mem md kj own HB.
pose proof (rtt_t_nums ly S Hp W mem md kj own HB) as
  (Hal16 & Hceil & Hslo & Hshi & H47 & Htop2 & Htop & Hs1a & Hs1b & Hs1m & Hces).
pose proof HB as (HJ & _ & _ & HSV & _).
pose proof HJ as (_ & HLY & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof rtt_t_pre_facts as (HFP & _).
pose proof HFP as (HAPRE & _).
pose proof HAPRE as (_ & Hrok & Hra4 & _ & _ & Hstk0 & _ & Hch0 & _).
pose proof rtt_t_stk_A as (HSK1 & _).
(* the entry chain, at the entry view; the journal keeps every byte at or above sp0 *)
assert (Hkeep : forall a, sp0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W) mem a = aview SEGS (w_H (ri_W D)) (ri_mem D) a) by (intros a Ha; apply F1; lia).
pose proof (achain_kept (ri_ly D) (aview SEGS (w_H (ri_W D)) (ri_mem D)) (aview SEGS (w_H W) mem)
  (spZ (ri_regs D)) (s0Z (ri_regs D)) (ri_ch D) sp0 Hch0 (Z.le_refl _) ltac:(lia) Hkeep) as Hch1.
pose proof (achain_ly_top (ri_ly D) ly _ _ _ _ Etop Hch1) as Hch2.
(* the saved ra and s0 at sp0 - 8 and sp0 - 16 *)
pose proof (HSV 0%nat ltac:(lia)) as V0. pose proof (HSV 1%nat ltac:(lia)) as V1.
unfold RTT_SAVED in V0, V1. cbn [nth] in V0, V1.
replace (ri_sp D - 8 * (Z.of_nat 0 + 1)) with (sp0 - 8) in V0 by (cbn [Z.of_nat]; lia).
replace (ri_sp D - 8 * (Z.of_nat 1 + 1)) with (sp0 - 16) in V1 by (cbn [Z.of_nat Pos.of_succ_nat]; lia).
pose proof (bv_unsigned_in_range 64 (getr (ri_regs D) 1%bv)) as Rr1.
pose proof (bv_unsigned_in_range 64 (getr (ri_regs D) 8%bv)) as Rr8.
change (bv_modulus 64) with (2 ^ 64) in Rr1, Rr8.
apply (rtt_t_achain_at ly (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem) sp0 sp1
  (bv_unsigned (getr (ri_regs D) 1%bv)) (s0Z (ri_regs D)) _ ltac:(exact Hch2) ltac:(lia)
  (fun a _ => eq_refl)).
- exact (rtt_t_rdword_of_vm (w_H W) mem _ _ V0 ltac:(lia)).
- unfold s0Z. exact (rtt_t_rdword_of_vm (w_H W) mem _ _ V1 ltac:(lia)).
- unfold raZ in Hra4. lia.
- lia.
- lia.
- lia.
Qed.

(* ---- a block is never live twice: the sep law (ARx field) makes the live blocks pairwise disjoint, and a block's
   request is at least one byte ---- *)
Lemma rtt_t_nodup : forall ly S Hp W mem md x l,
  ARx ly S Hp W mem md -> 0 < snd x -> Permutation (ablocks B ly S) (x :: l) -> In x l -> False.
Proof.
intros ly S Hp W mem md x l HAR Hx0 HP Hin.
assert (Hx : In x (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
destruct x as [p n].
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md p n HAR Hx) as (_ & _ & _ & _ & _ & HPB).
pose (f := fun b : Z * Z => (fst b, req_size (snd b))).
pose proof (rtt_t_pairwise_perm _ zdisjoint rtt_t_zdisjoint_sym _ _ (Permutation_map f HP) HPB) as HX.
cbn [map pairwise] in HX. destruct HX as (Hfx & _).
rewrite Forall_forall in Hfx. pose proof (Hfx (f (p, n)) (in_map f l (p, n) Hin)) as Hd.
unfold f, zdisjoint in Hd. cbn [fst snd] in Hd, Hx0.
assert (Hr : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
lia.
Qed.

(* ---- the callee's footprint inside the caller's: the record is in round_trip_text's own stack window, the old
   buffer is a block the rendering made since the entry ---- *)
Lemma rtt_t_fp_sub : forall ly S Hp W mem md kj own b len cap f txt,
  rtt_t_base ly S Hp W mem md kj own -> rtt_t_buf ly S Hp W mem b len cap f own txt ->
  fp_sub_x B STKR sp0 (ri_FP D) (PRH_FnTx.prhtx_fp rect b cap) (ri_ly D) (EJ S) [(RT_CID, pos)] ly S.
Proof.
intros ly S Hp W mem md kj own b len cap f txt HB HBF.
pose proof (rtt_t_nums ly S Hp W mem md kj own HB) as
  (Hal16 & Hceil & Hslo & Hshi & H47 & Htop2 & Htop & Hs1a & Hs1b & Hs1m & Hces).
pose proof HBF as (HREC & HINV & _ & _ & _ & Hcap0 & _ & HP1 & _).
pose proof HB as (HJ & _).
pose proof rtt_t_stk_A as (HSK1 & _).
intros a Ha. rewrite rtt_t_sd_ablocks. destruct (rtt_t_fp_cases _ _ _ _ Ha) as [Hr | (Hc0 & Hb)].
- (* the record: round_trip_text's own frame *)
  right. right. right. unfold RT_REC in Hr. lia.
- (* the old buffer: live now, and not the entry's (it would be one of the writer's blocks twice) *)
  right. left. destruct HINV as (_ & [(Hz & _) | (Hcp & _ & Hin & _)]); [lia|].
  exists b, cap. split; [exact Hin | split; [|exact Hb]].
  intros Hin0. exact (rtt_t_nodup ly S Hp W mem md (b, cap) wab (proj1 HJ) Hcp (HP1 Hcp) (HWAB _ Hin0)).
Qed.

(* ---- ONE tx_* CALL from the rendering, through YCbqGwild.v's aj_call_xWb_spR (the BUDGETED caller-window rule at RZW) at
   o = sp1 - sp0 and the callee window e1 = sp0 - sp1 (so o + e1 = 0: the callee's window top is round_trip_text's
   entry sp). The caller's journal is the cut's (rtt_J, an empty-budget journal: WS0 = []); the callee's text gives
   fpostW_xbR RZW P, so the caller's journal comes back at the budget [] ++ WS1 with P WS1 and is moved to the new state's
   depot (YCbqGwild.ajournal_xw_rebaseR: Rtt102Cut.rtt_J_redepot's step); the callee's own journal at WS1 goes on to
   the wild count. The caller hands the text its premises (rtt_t_cpre; the callee's own fwin and afn_pre_x come from
   the rule) and reads its post back as QC at the return site. ---- *)
Lemma rtt_t_txcall : forall (Wc : world SEGS) E ss ms ly S Hp md kj own b len cap f txt STK1
  (P : list (list Z) -> Prop)
  (QC : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (K : world SEGS -> config -> Prop),
  st_ok SEGS E ss (restrict (w_H Wc) ms) -> ss_resv ss = None ->
  rtt_t_base ly S Hp Wc (ms_mem ms) md kj own -> rtt_t_buf ly S Hp Wc (ms_mem ms) b len cap f own txt ->
  getr (ms_regs ms) 2 = w64 sp1 -> getr (ms_regs ms) 8 = w64 sp0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  YK0s.ret_ok (getr (ms_regs ms) 1) -> 4096 <= raZ (ms_regs ms) ->
  0 <= STK1 -> STK1 + 176 <= STKR ->
  blocks_bytes S0 <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) ->
  (forall ch1, rtt_t_cpre ly S Hp Wc (ms_mem ms) (ms_regs ms) b len cap f own txt ->
     afn_pre_x SEGS B ARx STK1 ly S Hp Wc (ms_regs ms) (ms_mem ms) md ch1 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (@YK11.mkst fxc (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms)
        (YK11.seg_rom SEGS)) md)
       (YCbqGwild.fpostW_xbR (fx := fxc) (SK := SK) SEGS B PST ARx RZW P STK1 DWIN (PRH_FnTx.prhtx_fp rect b cap)
          (ms_regs ms) ly S Hp Wc (ms_mem ms) md QC)) ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2 k1 WS1,
     AJ STKR sp0 (ri_FP D) (ri_ly D) (EJ S2) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)]
       ly2 S2 Hp2 W2 mem2 md2 k2 ->
     AJW (STK1 + DWIN) sp0 (PRH_FnTx.prhtx_fp rect b cap) ly S Hp Wc (ms_mem ms) md []
       ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
     P WS1 ->
     (forall a, sp1 <= a < sp0 -> ~ inFP (PRH_FnTx.prhtx_fp rect b cap) a ->
        aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a) ->
     aregs_preserved (ms_regs ms) regs2 -> QC ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg (@YK11.mkst fxc regs2 (getr (ms_regs ms) 1) mem2
       (YK11.seg_rom SEGS)) md2) K) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms md) K.
Proof.
intros Wc E ss ms ly S Hp md kj own b len cap f txt STK1 P QC K
  HS Hrv HB HBF R2 R8 R3 R4 Hrok Hra4 HSTK0 HSTK1 HBB0 HCALLEE HK.
pose proof (rtt_t_nums ly S Hp Wc (ms_mem ms) md kj own HB) as
  (Hal16 & Hceil & Hslo & Hshi & H47 & Htop2 & Htop & Hs1a & Hs1b & Hs1m & Hces).
pose proof HB as (HJ & _).
pose proof rtt_t_stk_A as (HSK1 & _).
pose proof ASAN_CEIL_range as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
destruct (rtt_t_chain_at ly S Hp Wc (ms_mem ms) md kj own HB) as (ch1 & Hch1).
assert (Hspc : spZ (ms_regs ms) = sp0 + (sp1 - sp0)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hs0 : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small. lia. }
eapply YSRrG.SRr'_bind.
{ eapply (YCbqGwild.aj_call_xWb_spR (fx := fxc) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) RZW
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc E ss ms
    STKR sp0 (ri_FP D) (ri_ly D) (EJ S) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)]
    ly S Hp md kj [] STK1 DWIN (PRH_FnTx.prhtx_fp rect b cap) (sp1 - sp0) (getr (ms_regs ms) 1) ch1 P QC
    HS Hrv HJ Hspc).
  - Z.div_mod_to_equations; lia.
  - lia.
  - exact HSTK0.
  - lia.
  - lia.
  - Z.div_mod_to_equations; lia.
  - lia.
  - exact R3.
  - exact R4.
  - reflexivity.
  - exact Hrok.
  - exact Hra4.
  - rewrite Hs0. replace (sp0 + (sp1 - sp0)) with sp1 by lia. exact Hch1.
  - intros HPRE1 _. apply (HCALLEE ch1); [|exact HPRE1].
    exact (rtt_t_cpre_of ly S Hp Wc (ms_mem ms) md kj own b len cap f txt (ms_regs ms) HB HBF
      ltac:(lia) HBB0).
  - exact (rtt_t_fp_sub ly S Hp Wc (ms_mem ms) md kj own b len cap f txt HB HBF). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & WS1 & -> & HPW & HJ2 & HJ1 & HW1 & HP2 & HQ).
replace (sp0 + (sp1 - sp0) + DWIN) with sp0 in HJ1 by lia.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARx RZW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2)
  as HJ2'.
rewrite rtt_t_sd_sd in HJ2'.
apply (HK ly2 S2 Hp2 W2 regs2 mem2 md2 (kj + k2) k2 WS1 HJ2' HJ1 HPW); [|exact HP2 | exact HQ].
intros a Ha Hn. apply HW1; [lia | exact Hn].
Qed.
(* ---- THE BASE ACROSS A tx CALL: the callee's own journal (at the call state, window [sp1, sp0)) keeps the frames,
   the ledger's blocks and the saved words, all off its footprint (the record above the ceiling, the old buffer a
   block of its own); the text's post gives the ledger, g_most, the room and the memnorm keep ---- *)
Lemma rtt_t_base_txcall : forall ly S Hp W mem md kj own b len cap f txt STK1
  ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k2 k1 WS1,
  rtt_t_base ly S Hp W mem md kj own -> rtt_t_buf ly S Hp W mem b len cap f own txt ->
  AJ STKR sp0 (ri_FP D) (ri_ly D) (EJ S2) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)]
    ly2 S2 Hp2 W2 mem2 md2 k2 ->
  AJW (STK1 + DWIN) sp0 (PRH_FnTx.prhtx_fp rect b cap) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall a, sp1 <= a < sp0 -> ~ inFP (PRH_FnTx.prhtx_fp rect b cap) a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  room_live_cf S2 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lamw peakw cntw SIZE_MAXZ ranw (ri_most D) own ->
  rtt_t_base ly2 S2 Hp2 W2 mem2 md2 k2 own.
Proof.
intros ly S Hp W mem md kj own b len cap f txt STK1 ly2 S2 Hp2 W2 mem2 md2 k2 k1 WS1
  HB HBF HJ2 HJ1 HWIN HMN HRM HL2.
pose proof (rtt_t_nums ly S Hp W mem md kj own HB) as
  (Hal16 & Hceil & Hslo & Hshi & H47 & Htop2 & Htop & Hs1a & Hs1b & Hs1m & Hces).
pose proof HB as (HJ & _ & _ & _ & HMN0 & HRO & _ & _ & _ & _ & _ & _ & HLED & _).
pose proof HJ as (HAR & _).
pose proof HBF as (HREC & HINV & _ & _ & _ & Hcap0 & _ & _ & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K1B & _ & K1F & _).
pose proof ASAN_CEIL_range as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
pose proof rtt_t_stk_A as (HSK1 & HSP0 & HSP1 & HSV0 & HSV1).
pose proof (@cf_head_nonneg cp) as Hh0.
assert (Hes : ESTACK = 4096) by reflexivity.
(* the old buffer, when there is one, is a live block of its own, below the low shadow or in high memory *)
assert (HBUF : cap <> 0 -> In (b, cap) (ablocks B ly S) /\ (forall a k, In (a, k) Lamw -> a - cf_head <> b)).
{ intros Hc. destruct HINV as (_ & [(Hz & _) | (_ & _ & Hin & _ & _ & _ & _ & _ & _ & _ & Hlam)]); [lia|].
  split; [exact Hin | exact Hlam]. }
(* a byte of the old buffer is not a frame byte, nor a frame's shadow byte, nor a ledger block's byte *)
assert (NFP_F : forall cid p a, In (cid, p) (frames S) ->
  (in_zr a (frame_rng ly (cid, p)) \/ in_zr a (shadow_addr (frame_addr ly cid p), fs_frame_bytes cid / 8)) ->
  ~ inFP (PRH_FnTx.prhtx_fp rect b cap) a).
{ intros cid p a Hin Ha Hf. destruct (rtt_t_fp_cases _ _ _ _ Hf) as [Hr | (Hc0 & Hb)].
  - destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as (_ & HFsep).
    pose proof (proj1 (Forall_forall _ _) HFsep (cid, p) Hin) as (Hflo & Hfhi). cbn [fst snd] in Hflo, Hfhi.
    unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. unfold RT_REC in Hr. unfold ASAN_CEIL in *.
    destruct Ha as [Ha | Ha]; [lia|].
    unfold shadow_addr, SHADOW_OFF in Ha. pose proof (fs_frame_bytes_nonneg cid).
    assert (frame_addr ly cid p / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
    assert (0 <= fs_frame_bytes cid / 8 <= 2 ^ 44)
      by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). lia.
  - destruct (HBUF Hc0) as (Hin2 & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b cap HAR Hin2) as (_ & _ & _ & Happ & _).
    unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. destruct Ha as [Ha | Ha].
    + pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md b cap cid p HAR Hin2 Hin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
    + destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid p HAR Hin) as (Hf0 & Hfc & _).
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
      unfold shadow_addr, SHADOW_OFF in Ha. pose proof (fs_frame_bytes_nonneg cid).
      assert (Hrqc : cap <= req_size cap) by (apply rtt_t_req_ge; lia).
      unfold ASAN_CEIL in *. Z.div_mod_to_equations. lia. }
assert (NFP_B : forall a k i, In (a, k) Lamw -> 0 <= i < k + cf_head ->
  ~ inFP (PRH_FnTx.prhtx_fp rect b cap) (a - cf_head + i)).
{ intros a k i Hin Hi Hf.
  pose proof (prh_ledger_hblock B ly S Hp W mem Lamw peakw cntw SIZE_MAXZ ranw a k (ri_most D) own (proj1 HLED) Hin)
    as (Hk & Hab & _ & _ & _).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hbc & _).
  assert (Hrq : k + cf_head <= req_size (k + cf_head)) by (apply rtt_t_req_ge; lia).
  destruct (rtt_t_fp_cases _ _ _ _ Hf) as [Hr | (Hc0 & Hb)].
  - unfold RT_REC in Hr. unfold ASAN_CEIL in *. lia.
  - destruct (HBUF Hc0) as (Hin2 & Hlam).
    assert (Hne : (b, cap) <> (a - cf_head, k + cf_head))
      by (intros E0; injection E0 as E1 _; exact (Hlam a k Hin (eq_sym E1))).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hin2 Hab Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
apply (rtt_t_base_tr ly S Hp W mem md kj own ly2 S2 Hp2 W2 mem2 md2 k2 HB HJ2).
- intros a Ha. apply HWIN; [lia|]. intros Hf. destruct (rtt_t_fp_cases _ _ _ _ Hf) as [Hr | (Hc0 & Hb)].
  + unfold RT_REC in Hr. lia.
  + destruct (HBUF Hc0) as (Hin2 & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b cap HAR Hin2) as (_ & _ & Hbc & _).
    assert (Hrqc : cap <= req_size cap) by (apply rtt_t_req_ge; lia). unfold ASAN_CEIL in *. lia.
- intros cid p a Hin Ha. apply (K1F cid p a Hin Ha). exact (NFP_F cid p a Hin Ha).
- intros a k i Hin Hi.
  pose proof (prh_ledger_hblock B ly S Hp W mem Lamw peakw cntw SIZE_MAXZ ranw a k (ri_most D) own (proj1 HLED) Hin)
    as (Hk & Hab & _ & _ & _).
  pose proof (prh_ledger_hblock B ly2 S2 Hp2 W2 mem2 Lamw peakw cntw SIZE_MAXZ ranw a k (ri_most D) own HL2 Hin)
    as (_ & Hab2 & _ & _ & _).
  assert (Hrq : k + cf_head <= req_size (k + cf_head)) by (apply rtt_t_req_ge; lia).
  replace (a - cf_head + i) with ((a - cf_head) + i) by lia.
  assert (Hik : 0 <= i < req_size (k + cf_head)) by lia.
  apply (K1B (a - cf_head) (k + cf_head) i Hab Hab2 Hik).
  exact (NFP_B a k i Hin Hi).
- intros H0. exact (HMN (HMN0 H0)).
- assert (Hb0 : cap <> 0 -> 0 < b).
  { intros Hc. destruct HINV as (_ & [(Hz & _) | (_ & _ & _ & _ & H4096 & _)]); [lia | lia]. }
  exact (rtt_t_rod_kept B ARx SK (STK1 + DWIN) sp0 (PRH_FnTx.prhtx_fp rect b cap)
    ly _ Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 rtt_t_pst_ro
    (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARx RZW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1)
    (rtt_t_fp_closed rect b cap ltac:(unfold RT_REC; lia) Hb0) HRO).
- exact HRM.
- split; [exact HL2 | exact (proj2 HLED)].
Qed.

(* ---- the document's root and the copy's place at a later state of the journal from the entry: ck_tree_ok's
   ck_obj_home (the root in a frame of the entry, its shadow addressable) and ck_out_ok's frame. The frames live at the
   entry are still live (frames S = own ++ frames S0), at the same address (layout_le), and their shadow bytes are
   kept by the journal's frame clause: no shadow byte is in FP, which is the copy's 56 bytes in an application band.
   (Rtt102Cut.rtt_carry does not carry these; tx_value's text asks both of its v.) ---- *)
Lemma rtt_t_doc_home : forall ly S Hp W mem md k,
  AJ STKR sp0 (ri_FP D) (ri_ly D) (EJ S) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)]
    ly S Hp W mem md k ->
  ck_in_frame ly S (ri_doc D) 56 /\ range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (ri_doc D) 56 /\
  (ri_copy D <> 0 -> ck_in_frame ly S (ri_copy D) 56).
Proof.
intros ly S Hp W mem md k HJ.
pose proof HPRE as (HFP & _ & _ & _ & _ & _ & _ & _ & _ & HTREE & _ & _ & _ & HCOPY & _).
pose proof HFP as ((HAR0 & _) & _).
pose proof HTREE as (_ & _ & _ & (_ & HCF0 & HRA0)).
pose proof HJ as (_ & HLY & _ & _ & _ & HFRS & _ & _ & _ & _ & _ & K1F & _).
rewrite rtt_t_sd_frames in HFRS, K1F.
pose proof ASAN_CEIL_range as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
pose proof rtt_t_stk_A as (HSK1 & HSP0 & HSP1 & HSV0 & HSV1).
assert (EF : forall cid p, frame_addr ly cid p = frame_addr (ri_ly D) cid p).
{ intros cid p. unfold frame_addr. destruct HLY as (_ & _ & _ & _ & _ & E6 & _). rewrite E6. reflexivity. }
assert (INF : forall a n, ck_in_frame (ri_ly D) (ri_S D) a n -> ck_in_frame ly S a n).
{ intros a n (cid & p & Hin & Hlo & Hhi). exists cid, p. rewrite HFRS, EF. split; [right; exact Hin | lia]. }
(* a shadow byte of an address inside an entry frame is no byte of the copy: the copy is in an application band *)
assert (NFP : forall cid p x, In (cid, p) (frames (ri_S D)) ->
  frame_addr (ri_ly D) cid p <= x < frame_addr (ri_ly D) cid p + fs_frame_bytes cid ->
  ~ inFP (ri_FP D) (shadow_addr x)).
{ intros cid p x Hin Hx Hf. unfold ri_FP in Hf. destruct (Z.eqb_spec (ri_copy D) 0) as [E0 | E0].
  - exact (inFP_nil _ Hf).
  - apply inFP_cons in Hf. destruct Hf as [Hf | Hf]; [|exact (inFP_nil _ Hf)]. cbn [fst snd] in Hf.
    destruct HCOPY as [Hc0 | (_ & _ & (Hcf & _) & _)]; [exact (E0 Hc0)|].
    destruct Hcf as (cid2 & p2 & Hin2 & Hlo2 & Hhi2).
    destruct (frames_bounds_x SEGS B ARx LAWS (ri_ly D) (ri_S D) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D)
      cid p HAR0 Hin) as (Hf0 & Hfc & _).
    destruct (frames_bounds_x SEGS B ARx LAWS (ri_ly D) (ri_S D) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D)
      cid2 p2 HAR0 Hin2) as (Hg0 & Hgc & Happ).
    pose proof (fs_frame_bytes_nonneg cid). pose proof (fs_frame_bytes_nonneg cid2).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
    unfold shadow_addr, SHADOW_OFF in Hf. Z.div_mod_to_equations. lia. }
split; [exact (INF _ _ HCF0)|].
split.
{ destruct HCF0 as (cid & p & Hin & Hlo & Hhi).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  assert (H56 : 56 <= fs_frame_bytes cid) by lia.
  pose proof (rtt_t_fs_mod8 cid H56) as H8.
  destruct (frames_bounds_x SEGS B ARx LAWS (ri_ly D) (ri_S D) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D)
    cid p HAR0 Hin) as (Hf0 & Hfc & _).
  destruct (alx_frames SEGS B ARx LAWS (ri_ly D) (ri_S D) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D)
    cid p HAR0 Hin) as (H32 & _).
  eapply range_addressable_agree; [|exact HRA0]. intros x Hx.
  unfold shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x).
  apply (K1F cid p (shadow_addr x) Hin); [right | exact (NFP cid p x Hin ltac:(lia))].
  unfold in_zr, shadow_addr. cbn [fst snd]. Z.div_mod_to_equations. lia. }
intros Hc. destruct HCOPY as [Hc0 | (_ & _ & (Hcf & _) & _)]; [exact (False_ind _ (Hc Hc0))|].
exact (INF _ _ Hcf).
Qed.
(* ---- THE RENDERING'S WINDOW in the text's run: its events r_evs = prhtx_evs 0 0 (ck_rtt_ns t p) (PRH_Supply) start
   at RT_K_W, and they are consumer allocations (rtt_pre's prh_cons_from, split by prh_cons_from_app_iff) ---- *)
Lemma rtt_t_cons_r :
  PRH_Base.prh_cons_from ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D + RT_K_W D)%nat
    (length (PRH_FnTx.prhtx_evs 0 0 (ck_rtt_ns (ri_t D) (ri_p D)))).
Proof.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HC & _).
unfold ck_rtt_evs, PresetReqAt.rt_text in HC.
rewrite PRH_Supply.prhtx_evs_r_evs. unfold RT_K_W.
rewrite <- !app_assoc in HC. rewrite !length_app in HC.
apply (proj1 (prh_cons_from_app_iff _ _ _ _ _ _)) in HC as [_ HC].
apply (proj1 (prh_cons_from_app_iff _ _ _ _ _ _)) in HC as [HC _]. exact HC.
Qed.

(* the window of one call: after the calls dn, the call of the pieces ks; its run events and its consumer window *)
Lemma rtt_t_window : forall dn ks rest, dn ++ ks ++ rest = ck_rtt_ns (ri_t D) (ri_p D) ->
  prh_run_at ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D + RT_K_W D + length (PRH_FnTx.prhtx_evs 0 0 dn))%nat
    (PRH_FnTx.prhtx_evs (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) ks) /\
  PRH_Base.prh_cons_from ReaderRes.jr_strtod (ri_x D) (ri_os D)
    (ri_i D + RT_K_W D + length (PRH_FnTx.prhtx_evs 0 0 dn))%nat
    (length (PRH_FnTx.prhtx_evs (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) ks)).
Proof.
intros dn ks rest Ens.
pose proof rtt_t_run_at_r as HR. pose proof rtt_t_cons_r as HC.
rewrite <- Ens in HR, HC.
rewrite !PRH_FnTx.prhtx_evs_app, Z.add_0_l in HR, HC.
rewrite length_app in HC.
apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in HR as [_ HR].
apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in HR as [HR _].
apply (proj1 (prh_cons_from_app_iff _ _ _ _ _ _)) in HC as [_ HC].
rewrite length_app in HC.
apply (proj1 (prh_cons_from_app_iff _ _ _ _ _ _)) in HC as [HC _].
split; [exact HR | exact HC].
Qed.

(* the granted state of the rendering after the calls dn: the buffer is the model's (length zsum dn, capacity
   tx_capf 0 0 dn, not failed, g_own_ran_out 0), the position is the text's at RT_K_W plus the calls' events, and the
   wild traces stored since the entry are at most the calls' grows - the same count (one wild trace per grow, the
   tx texts' budget) *)
Definition rtt_t_gpos (S : astate) (dn : list Z) : Prop :=
  rtt_pos D S (RT_K_W D + length (PRH_FnTx.prhtx_evs 0 0 dn))%nat /\
  rtt_wild B D S (length (PRH_FnTx.prhtx_evs 0 0 dn)).

(* ---- C-TXTRACE AT THE CUT. Each of the three tx calls asks PRH_FnTx.prhtx_trace B ly W mem rect, STATE-FREE since
   the batch kit's cut: (1) every byte of [rect - 16, ly_top ly) present, and (2) for every chain read through a reader that
   agrees with the view there outside the record, the unwinder's trace from the record in the universe. (2) is the
   realloc site's universe fact at ANY tail; (1) holds below the entry sp by the journal's window clause and above it
   from the entry's live stack (YGcallStackUp.astack_up_x) through the journal's high-memory keep. The walk derives
   neither from the stretch: the first is RTT_T_TRACE_AT (end of file), the second the text's last premise
   (Rtt102Cut.rtt_pre_up). ---- *)
Definition rtt_t_trace_at : Prop :=
  (forall t ch, inU (as_universe B) (unwind_of_chain cf_pc_realloc_ra0 ((t, pi_ret_tx_realloc, t) :: ch))) /\
  YGcallStackUp.astack_up_x SEGS (ri_ly D) (ri_W D) (ri_sp D) (ri_mem D).

Lemma rtt_t_trace_of : forall ly S Hp W mem md kj own, rtt_t_base ly S Hp W mem md kj own -> rtt_t_trace_at ->
  PRH_FnTx.prhtx_trace B ly W mem rect.
Proof.
intros ly S Hp W mem md kj own HB (HU & HUP).
unfold YGcallStackUp.astack_up_x in HUP.
pose proof (rtt_t_nums ly S Hp W mem md kj own HB) as
  (Hal16 & Hceil & Hslo & Hshi & H47 & Htop2 & Htop & Hs1a & Hs1b & Hs1m & Hces).
pose proof HB as (HJ & _).
pose proof HJ as (_ & HLY & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & HPRES & _).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof rtt_t_stk_A as (HSK1 & _).
unfold PRH_FnTx.prhtx_trace. intros _. split.
- intros a Ha. destruct (Z_lt_le_dec a sp0) as [Hlt | Hge].
  + apply rtt_t_aview_present. apply HPRES. unfold RT_REC in Ha. lia.
  + rewrite (F1 a ltac:(lia) ltac:(lia)). apply rtt_t_aview_present. apply HUP. rewrite <- Etop. lia.
- intros rd ch _ _. exact (HU rect ch).
Qed.

Lemma rtt_t_univ : prh_univ_closure B CTX0.
Proof. pose proof HPRE as (_ & _ & H & _). exact H. Qed.

(* the calls already made and the one being made fit inside the rendering's total *)
Lemma rtt_t_split_bound : forall dn ks rest, dn ++ ks ++ rest = ck_rtt_ns (ri_t D) (ri_p D) ->
  0 <= TxModel.zsum dn /\ 0 <= TxModel.zsum ks /\
  TxModel.zsum dn + TxModel.zsum ks <= ck_tx_len (ri_t D) (ri_p D).
Proof.
intros dn ks rest E. pose proof (rtt_t_ns_nonneg (ri_t D) (ri_p D)) as HF. rewrite <- E in HF.
apply Forall_app in HF as [H1 H2]. apply Forall_app in H2 as [H2 H3].
pose proof (rtt_t_zsum_nonneg _ H1). pose proof (rtt_t_zsum_nonneg _ H2). pose proof (rtt_t_zsum_nonneg _ H3).
unfold ck_tx_len. rewrite <- E, !TxModel.zsum_app. lia.
Qed.

(* the rendering's request bound on any prefix: 2 * (len + 1) stays under the allocator's maximum *)
Lemma rtt_t_req_bound : forall dn ks rest, dn ++ ks ++ rest = ck_rtt_ns (ri_t D) (ri_p D) ->
  2 * (TxModel.zsum dn + TxModel.zsum ks + 1) < cf_malloc_max /\
  TxModel.zsum dn + TxModel.zsum ks + 1 <= 2 ^ 28.
Proof.
intros dn ks rest E. pose proof (rtt_t_split_bound dn ks rest E) as (Z1 & Z2 & Z3).
pose proof rtt_t_pre_facts as (_ & _ & HRQ & _ & HWL & _).
pose proof (rtt_t_req_rq (ri_t D) (ri_p D)) as Hrq. pose proof (@cf_head_nonneg cp) as Hh0.
rewrite rtt_t_txlen in Z3. unfold PjWriteHyp.wlen in HWL.
assert (HT : 2 * (ck_tx_len (ri_t D) (ri_p D) + 1) <= TX_req (ri_t D) (ri_p D)) by (unfold TX_req; lia).
rewrite rtt_t_txlen in HT. split; lia.
Qed.

(* ---- THE RENDERING'S WILD BUDGET: its grows number at most RTT_WK_T (PRH_FnTx.prhtx_evs_le_30 at the whole
   rendering, from an empty buffer), so the grows so far and the next call's fit there ---- *)
Lemma rtt_t_evs_all : (length (PRH_FnTx.prhtx_evs 0 0 (ck_rtt_ns (ri_t D) (ri_p D))) <= RTT_WK_T)%nat.
Proof.
pose proof (rtt_t_req_bound (ck_rtt_ns (ri_t D) (ri_p D)) [] [] ltac:(rewrite !app_nil_r; reflexivity))
  as (_ & H28).
cbn [TxModel.zsum] in H28. rewrite Z.add_0_r in H28.
exact (PRH_FnTx.prhtx_evs_le_30 _ (rtt_t_ns_nonneg (ri_t D) (ri_p D)) H28).
Qed.

Lemma rtt_t_evs_split : forall dn ks rest, dn ++ ks ++ rest = ck_rtt_ns (ri_t D) (ri_p D) ->
  (length (PRH_FnTx.prhtx_evs 0 0 dn) +
   length (PRH_FnTx.prhtx_evs (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) ks) <= RTT_WK_T)%nat.
Proof.
intros dn ks rest Ens. pose proof rtt_t_evs_all as H30.
rewrite <- Ens in H30. rewrite !PRH_FnTx.prhtx_evs_app, Z.add_0_l, !length_app in H30. lia.
Qed.

(* the room a call after the calls dn takes (its own grows), from the text's entry room less the grows so far
   (Rtt102Cut.rtt_wild_room) *)
Lemma rtt_t_room_at : forall S dn ks rest, dn ++ ks ++ rest = ck_rtt_ns (ri_t D) (ri_p D) ->
  rtt_wild B D S (length (PRH_FnTx.prhtx_evs 0 0 dn)) ->
  YCbqGwild.wild_room (as_universe B) []
    (length (PRH_FnTx.prhtx_evs (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) ks)) (st_depot S).
Proof.
intros S dn ks rest Ens HWD.
pose proof (rtt_t_evs_split dn ks rest Ens) as Hle. unfold RTT_WK_T in Hle.
assert (Ewk : prh_wk F_round_trip_text = 32%nat) by reflexivity.
assert (HR : YCbqGwild.wild_room (as_universe B) []
  (prh_wk F_round_trip_text - length (PRH_FnTx.prhtx_evs 0 0 dn)) (st_depot S)).
{ eapply (rtt_wild_room (fx := fx)); [exact HPRE | exact HWD | rewrite Ewk; lia]. }
rewrite Ewk in HR.
apply (YCbqGwild.wild_room_le _ _ (32 - length (PRH_FnTx.prhtx_evs 0 0 dn))); [lia | exact HR].
Qed.

(* ---- the buffer after a call that DONE its pieces: the record and the buffer the post states, the blocks the
   writer's plus the new buffer (the growth replaces the old one), the live bytes bounded by the new capacity ---- *)
Lemma rtt_t_buf_next : forall ly S Hp W mem b len cap txt ly2 S2 Hp2 W2 mem2 b1 cap1 (pre : list Z),
  rtt_t_buf ly S Hp W mem b len cap 0 0 txt ->
  PRH_FnTx.prhtx_rec W2 mem2 rect b1 (len + Z.of_nat (length pre)) cap1 0 ->
  PRH_FnTx.prhtx_inv B Lamw ly2 S2 W2 mem2 b1 (len + Z.of_nat (length pre)) cap1 (txt ++ pre) ->
  PRH_FnTx.prhtx_grow B ly S ly2 S2 b cap b1 cap1 ->
  blocks_bytes S2 <= blocks_bytes S + cap1 - cap ->
  rtt_t_buf ly2 S2 Hp2 W2 mem2 b1 (len + Z.of_nat (length pre)) cap1 0 0 (txt ++ pre).
Proof.
intros ly S Hp W mem b len cap txt ly2 S2 Hp2 W2 mem2 b1 cap1 pre HBF HREC HINV HGR HBB2.
pose proof HBF as (_ & _ & _ & _ & HLEN & Hcap0 & HP0 & HP1 & HBB).
pose proof HREC as (_ & _ & Hc1 & _).
split; [exact HREC|]. split; [exact HINV|]. split; [intros _; reflexivity|]. split; [left; reflexivity|].
split; [rewrite length_app, Nat2Z.inj_add, HLEN; reflexivity|]. split; [lia|].
destruct HGR as [(Eb & Ec & Eab) | (Hlt & bl1 & bl2 & Hsh & HP)].
- subst b1 cap1. rewrite Eab. split; [exact HP0|]. split; [exact HP1|]. lia.
- assert (HPw : Permutation (bl1 ++ bl2) wab).
  { destruct Hsh as [(Hz & Eab) | (Hz & Eab)].
    + rewrite <- Eab. exact (HP0 Hz).
    + specialize (HP1 Hz). rewrite Eab in HP1. apply Permutation_sym.
      eapply (Permutation_cons_app_inv bl1 bl2). apply Permutation_sym. exact HP1. }
  split; [intros Hz; lia|].
  split; [intros _; eapply Permutation_trans; [exact HP | apply perm_skip; exact HPw]|]. lia.
Qed.

(* ---- ONE GRANTED tx_put CALL (A' +0x154 "" or +0x180 "\n"): after the calls dn, the call of src at s. The run left
   the machine at the jal with a0 = the record, a1 = s, a2 = |src|, ra = the return site kret. The kit's text (TXPUT)
   at the cut's fxc, its room from the wild budget; its post read back as the granted state after dn ++ [|src|]. ---- *)
Lemma rtt_t_gput_core : forall (Wc : world SEGS) E ss ms ly S Hp md kj b txt dn (s : Z) (src : list Z) rest
  (kret : Z) (K : world SEGS -> config -> Prop),
  st_ok SEGS E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_tx_put ->
  dn ++ [Z.of_nat (length src)] ++ rest = ck_rtt_ns (ri_t D) (ri_p D) ->
  rtt_t_base ly S Hp Wc (ms_mem ms) md kj 0 ->
  rtt_t_buf ly S Hp Wc (ms_mem ms) b (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) 0 0 txt ->
  rtt_t_gpos S dn -> rtt_t_bregs (ms_regs ms) ->
  getr (ms_regs ms) 10 = w64 rect -> getr (ms_regs ms) 11 = w64 s ->
  getr (ms_regs ms) 12 = w64 (Z.of_nat (length src)) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + kret) -> 0 <= kret < 2 ^ 40 -> kret mod 2 = 0 ->
  rtt_fx (fx := fx) fxc ->
  (* C-TXTRACE (RTT_T_TRACE_AT) *)
  rtt_t_trace_at ->
  src_rd Wc (ms_mem ms) s src -> PRH_FnTx.prhtx_kept B Lamw ly S s (Z.of_nat (length src)) ->
  (forall a, s <= a < s + Z.of_nat (length src) ->
     ~ (rect <= a < rect + 28) /\ ~ (b <= a < b + TxModel.tx_capf 0 0 dn)) ->
  blocks_bytes S0 <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2 b1,
     rtt_t_base ly2 S2 Hp2 W2 mem2 md2 k2 0 ->
     rtt_t_buf ly2 S2 Hp2 W2 mem2 b1 (TxModel.zsum (dn ++ [Z.of_nat (length src)]))
       (TxModel.tx_capf 0 0 (dn ++ [Z.of_nat (length src)])) 0 0 (txt ++ src) ->
     rtt_t_gpos S2 (dn ++ [Z.of_nat (length src)]) -> rtt_t_bregs regs2 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg (@YK11.mkst fxc regs2 (Z_to_bv 64 (BASE + kret)) mem2
       (YK11.seg_rom SEGS)) md2) K) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms md) K.
Proof.
intros Wc E ss ms ly S Hp md kj b txt dn s src rest kret K HS Hrv Hpc Ens HB HBF HGP HBR
  Ha0 Ha1 Ha2 Hra Hk0 Hk2 HFX HTA HSRC HKEPT HDISJ HBB0 HK.
pose proof (rtt_t_trace_of ly S Hp Wc (ms_mem ms) md kj 0 HB HTA) as HTR.
pose proof HBR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4 & R21 & R22).
pose proof rtt_t_stk_A as (HSK1 & HSP0 & HSP1 & _).
pose proof (@pa_B_ok _ _ PA) as HBASE.
pose proof ASAN_CEIL_range as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
pose proof (rtt_t_window dn [Z.of_nat (length src)] rest Ens) as (HRUN & HCONS).
pose proof (rtt_t_req_bound dn [Z.of_nat (length src)] rest Ens) as (HRQ & H28).
cbn [TxModel.zsum] in HRQ, H28. rewrite Z.add_0_r in HRQ, H28.
destruct HGP as ((hist & HPOS) & HWLD). rewrite Nat.add_assoc in HPOS.
(* the wild room this call takes: its own grows, inside the text's room less the grows so far *)
pose proof (rtt_t_room_at S dn [Z.of_nat (length src)] rest Ens HWLD) as HROOMK.
assert (Hrok : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite Hra; apply (ret_ok_codeptr_v (PI := PA)); lia).
assert (Hraz : raZ (ms_regs ms) = BASE + kret).
{ unfold raZ. rewrite Hra. apply unsigned_lit_small. lia. }
assert (HB0 : 4096 <= BASE < 2 ^ 40) by (split; vm_compute; [discriminate | reflexivity]).
assert (Hra4 : 4096 <= raZ (ms_regs ms)) by (rewrite Hraz; lia).
assert (Hrac : raZ (ms_regs ms) < YM05.alloc_ceiling) by (rewrite Hraz; lia).
assert (HEV : 0 = 0 -> TxModel.tx_capf 0 0 dn < TxModel.zsum dn + Z.of_nat (length src) + 1 ->
  nth_error (PresetRun.hruns ReaderRes.jr_strtod (ri_x D) (ri_os D))
    (ri_i D + RT_K_W D + length (PRH_FnTx.prhtx_evs 0 0 dn))%nat =
  Some (if TxModel.tx_capf 0 0 dn =? 0
        then PresetReqAt.HMal (2 * (TxModel.zsum dn + Z.of_nat (length src) + 1))
        else PresetReqAt.HRe (TxModel.tx_capf 0 0 dn) (2 * (TxModel.zsum dn + Z.of_nat (length src) + 1)))).
{ intros _ Hgr. cbn [PRH_FnTx.prhtx_evs] in HRUN. rewrite (proj2 (Z.leb_gt _ _) Hgr) in HRUN.
  cbn [app] in HRUN. apply (proj1 (prh_run_at_one _ _ _ _ _)) in HRUN. exact HRUN. }
eapply (rtt_t_txcall Wc E ss ms ly S Hp md kj 0 b (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) 0 txt
  (@STK_tx_put prh_img_A)
  (PRH_Base.wbudget_if 0 [] (length (PRH_FnTx.prhtx_evs (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn)
     [Z.of_nat (length src)]))) _ K
  HS Hrv HB HBF R2 R8 R3 R4 Hrok Hra4 HSP0 HSP1 HBB0).
- (* THE CALLEE: the kit's tx_put text at fxc *)
  intros ch1 HCP HPRE1. rewrite Hpc.
  pose proof HCP as (HFW & HPL & HREC & HINV & HLED & HRM & HRO & HSHI & _ & HLIVE).
  exact (TXPUT fxc ReaderRes.jr_strtod (ri_x D) (ri_os D)
    (ri_i D + RT_K_W D + length (PRH_FnTx.prhtx_evs 0 0 dn))%nat
    (ri_H0 D) hist ly S Hp Wc (ms_regs ms) (ms_mem ms) md ch1 DWIN rect s (Z.of_nat (length src)) b
    (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) 0 0 txt src
    Lamw peakw cntw SIZE_MAXZ ranw (ri_most D)
    (conj HPRE1 (conj HRO (conj HSHI (conj Hrac (proj1 HFX)))))
    rtt_t_univ HRM HPOS (rtt_pre_os4 B ARx CTX0 D HPRE) (fun _ => HROOMK) (fun _ => HCONS) Ha0 Ha1 Ha2 HFW HPL HTR
    HREC HINV HSRC eq_refl
    HKEPT HDISJ H28 HLED HEV HLIVE HRQ).
- (* THE RETURN: the granted outcome (K0-DEAD-TXPUT: f0 = 0 gives f1 = 0, so DONE) read back *)
  intros ly2 S2 Hp2 W2 regs2 mem2 md2 k2 k1 WS1 HJ2 HJ1 HPW HW1 HP2 (HQ & HMN2).
  destruct HQ as (b1 & cap1 & f1 & own' & pre & HPOST & HOUT & HDEAD & _ & HRM2 & HPG & HPK & HL2).
  specialize (HDEAD eq_refl). subst f1.
  destruct HOUT as [(_ & _ & Eown & Epre & Ecap) | [(Hf & _) | (_ & _ & Hf1 & _)]];
    [| exfalso; exact (Hf eq_refl) | exfalso; lia].
  subst own' pre cap1.
  pose proof HPOST as (HREC2 & HINV2 & _ & EHp & HGR & HBB2).
  pose proof (rtt_t_base_txcall ly S Hp Wc (ms_mem ms) md kj 0 b (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) 0 txt
    (@STK_tx_put prh_img_A) ly2 S2 Hp2 W2 mem2 md2 k2 k1 WS1 HB HBF HJ2 HJ1 HW1 HMN2 HRM2 HL2) as HB2.
  pose proof (rtt_t_buf_next ly S Hp Wc (ms_mem ms) b (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) txt
    ly2 S2 Hp2 W2 mem2 b1 (TxModel.tx_cap1 (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) (Z.of_nat (length src)))
    src HBF HREC2 HINV2 HGR HBB2) as HBF2.
  assert (Elen : TxModel.zsum dn + Z.of_nat (length src) = TxModel.zsum (dn ++ [Z.of_nat (length src)])).
  { rewrite TxModel.zsum_app. cbn [TxModel.zsum]. lia. }
  assert (Ecapn : TxModel.tx_cap1 (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) (Z.of_nat (length src)) =
                  TxModel.tx_capf 0 0 (dn ++ [Z.of_nat (length src)])).
  { rewrite TxModel.tx_capf_app. cbn [TxModel.tx_capf]. rewrite Z.add_0_l. reflexivity. }
  rewrite Elen, Ecapn in HBF2.
  (* the wild traces since the entry: this call's budget added (Rtt102Cut.rtt_wild_keep over its own journal) *)
  assert (HW2 : rtt_wild B D S2 (length (PRH_FnTx.prhtx_evs 0 0 dn) +
    length (PRH_FnTx.prhtx_evs (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) [Z.of_nat (length src)]))).
  { eapply rtt_wild_keep; [| exact HWLD | exact HJ1 | exact (HPW eq_refl)]. reflexivity. }
  rewrite Hra. apply (HK ly2 S2 Hp2 W2 regs2 mem2 md2 k2 b1 HB2 HBF2); [| exact (rtt_t_bregs_pres _ _ HBR HP2)].
  (* the position: one event when the put grew, none otherwise; the wild count by the same events *)
  unfold rtt_t_gpos. rewrite PRH_FnTx.prhtx_evs_app, length_app, Z.add_0_l. split; [|exact HW2].
  unfold rtt_pos. cbn [PRH_FnTx.prhtx_evs].
  destruct (Z.leb_spec (TxModel.zsum dn + Z.of_nat (length src) + 1) (TxModel.tx_capf 0 0 dn)) as [Hfit | Hgr].
  + cbn [app length].
    exists hist. replace (ri_i D + (RT_K_W D + (length (PRH_FnTx.prhtx_evs 0 0 dn) + 0)))%nat
      with (ri_i D + RT_K_W D + length (PRH_FnTx.prhtx_evs 0 0 dn))%nat by lia.
    apply HPK. intros (_ & _ & Hc). lia.
  + cbn [app length]. destruct (HPG eq_refl eq_refl Hgr) as (hist' & HP').
    exists hist'. replace (ri_i D + (RT_K_W D + (length (PRH_FnTx.prhtx_evs 0 0 dn) + 1)))%nat
      with (Datatypes.S (ri_i D + RT_K_W D + length (PRH_FnTx.prhtx_evs 0 0 dn)))%nat by lia.
    exact HP'.
Qed.


(* the document's root node at a call: in a frame of S (prhtx_home's frame arm), below the record *)
Lemma rtt_t_doc_at : forall ly S Hp W mem md kj own,
  rtt_t_base ly S Hp W mem md kj own ->
  PRH_FnTx.prhtx_home Lamw ly S (ri_doc D) 56 /\ ri_doc D + 56 <= rect.
Proof.
intros ly S Hp W mem md kj own HB.
pose proof (rtt_t_nums ly S Hp W mem md kj own HB) as
  (Hal16 & Hceil & Hslo & Hshi & H47 & Htop2 & Htop & Hs1a & Hs1b & Hs1m & Hces).
pose proof HB as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HCF & _).
pose proof HJ as (HAR & _).
pose proof rtt_t_stk_A as (HSK1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
destruct HCF as (cid & p & Hin & Hlo & Hhi).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid p HAR Hin) as (Hf0 & Hfc & _).
split.
- right. exists cid, p. split; [exact Hin|]. intros a Ha. unfold in_zr, frame_rng. cbn [fst snd]. lia.
- unfold RT_REC. lia.
Qed.

(* ---- THE GRANTED tx_value CALL (A' +0x168): after the call "" (dn = [0]), the call of the value's pieces at
   (doc, pretty, 0); the kit's text (TXVAL) at fxc, n := DOC_D, its room from the wild budget ---- *)
Lemma rtt_t_gval_core : forall (Wc : world SEGS) E ss ms ly S Hp md kj b txt dn rest
  (kret : Z) (K : world SEGS -> config -> Prop),
  st_ok SEGS E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_tx_value ->
  dn ++ TxModel.tv_calls (ri_t D) (ri_p D) 0 ++ rest = ck_rtt_ns (ri_t D) (ri_p D) ->
  rtt_t_base ly S Hp Wc (ms_mem ms) md kj 0 ->
  rtt_t_buf ly S Hp Wc (ms_mem ms) b (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) 0 0 txt ->
  rtt_t_gpos S dn -> rtt_t_bregs (ms_regs ms) ->
  getr (ms_regs ms) 10 = w64 rect -> getr (ms_regs ms) 11 = w64 (ri_doc D) ->
  getr (ms_regs ms) 12 = w64 (ri_pretty D) -> getr (ms_regs ms) 13 = w64 0 ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + kret) -> 0 <= kret < 2 ^ 40 -> kret mod 2 = 0 ->
  rtt_fx (fx := fx) fxc ->
  (* C-TXTRACE (RTT_T_TRACE_AT) *)
  rtt_t_trace_at ->
  blocks_bytes S0 <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2 b1,
     rtt_t_base ly2 S2 Hp2 W2 mem2 md2 k2 0 ->
     rtt_t_buf ly2 S2 Hp2 W2 mem2 b1 (TxModel.zsum (dn ++ TxModel.tv_calls (ri_t D) (ri_p D) 0))
       (TxModel.tx_capf 0 0 (dn ++ TxModel.tv_calls (ri_t D) (ri_p D) 0)) 0 0
       (txt ++ concat (WriterValue.wvpieces (ri_t D) (ri_p D) 0)) ->
     rtt_t_gpos S2 (dn ++ TxModel.tv_calls (ri_t D) (ri_p D) 0) -> rtt_t_bregs regs2 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg (@YK11.mkst fxc regs2 (Z_to_bv 64 (BASE + kret)) mem2
       (YK11.seg_rom SEGS)) md2) K) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms md) K.
Proof.
intros Wc E ss ms ly S Hp md kj b txt dn rest kret K HS Hrv Hpc Ens HB HBF HGP HBR
  Ha0 Ha1 Ha2 Ha3 Hra Hk0 Hk2 HFX HTA HBB0 HK.
pose proof (rtt_t_trace_of ly S Hp Wc (ms_mem ms) md kj 0 HB HTA) as HTR.
pose proof HBR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4 & R21 & R22).
pose proof rtt_t_stk_A as (HSK1 & _ & _ & HSV0 & HSV1).
pose proof (@pa_B_ok _ _ PA) as HBASE.
pose proof ASAN_CEIL_range as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
pose proof (rtt_t_window dn (TxModel.tv_calls (ri_t D) (ri_p D) 0) rest Ens) as (HRUN & HCONS).
pose proof (rtt_t_req_bound dn (TxModel.tv_calls (ri_t D) (ri_p D) 0) rest Ens) as (HRQ & H28).
rewrite rtt_t_zsum_tv in HRQ, H28.
pose proof rtt_t_pre_facts as (_ & _ & _ & _ & _ & HDEP & HPR & _).
pose proof HB as (HJ & _ & _ & _ & _ & _ & _ & HND & HTV & HRA & _ & _ & HLED & _ & _ & HDL & _).
pose proof HJ as (HAR & _).
destruct (rtt_t_doc_at ly S Hp Wc (ms_mem ms) md kj 0 HB) as (HHOME & HAPART).
destruct HGP as ((hist & HPOS) & HWLD). rewrite Nat.add_assoc in HPOS.
(* the wild room this call takes: its own grows, inside the text's room less the grows so far *)
pose proof (rtt_t_room_at S dn (TxModel.tv_calls (ri_t D) (ri_p D) 0) rest Ens HWLD) as HROOMK.
assert (Hrok : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite Hra; apply (ret_ok_codeptr_v (PI := PA)); lia).
assert (Hraz : raZ (ms_regs ms) = BASE + kret).
{ unfold raZ. rewrite Hra. apply unsigned_lit_small. lia. }
assert (HB0 : 4096 <= BASE < 2 ^ 40) by (split; vm_compute; [discriminate | reflexivity]).
assert (Hra4 : 4096 <= raZ (ms_regs ms)) by (rewrite Hraz; lia).
assert (Hrac : raZ (ms_regs ms) < YM05.alloc_ceiling) by (rewrite Hraz; lia).
assert (HDEPN : (PjTree.depth (ri_t D) <= DOC_D)%nat) by (unfold DOC_D, PjGrammar.MAXD; lia).
assert (HND2 : pj_nodeR SEGS (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamw) (ri_doc D) (ri_t D) (ri_D D)).
{ apply (rtt_t_nodeR_lblk (ri_t D) _ (prh_lin (ri_Lam D)) (prh_lin Lamw) (ri_doc D) (ri_D D)); [|exact HND].
  intros a k Hak. unfold prh_lin in *. exact (HLAMW _ Hak). }
eapply (rtt_t_txcall Wc E ss ms ly S Hp md kj 0 b (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) 0 txt
  (@STK_tx_value prh_img_A DOC_D)
  (PRH_Base.wbudget_if 0 [] (length (PRH_FnTx.prhtx_evs (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn)
     (TxModel.tv_calls (ri_t D) (ri_p D) 0)))) _ K
  HS Hrv HB HBF R2 R8 R3 R4 Hrok Hra4 HSV0 HSV1 HBB0).
- (* THE CALLEE: the kit's tx_value text at fxc, depth bound DOC_D *)
  intros ch1 HCP HPRE1. rewrite Hpc.
  pose proof HCP as (HFW & HPL & HREC & HINV & HLED' & HRM & HRO & HSHI & HCNT & HLIVE).
  pose proof (rtt_t_bvis_of_tvis B ARx ly S Hp Wc (ms_mem ms) md Lamw peakw cntw SIZE_MAXZ ranw
    (ri_most D) 0 (ri_D D) HAR HLED' HDL HTV) as HBV.
  assert (HPRR : - 2 ^ 31 <= ri_pretty D < 2 ^ 31) by lia.
  assert (HD0 : 0 <= 0) by lia.
  assert (HDD : 0 + Z.of_nat (PjTree.depth (ri_t D)) <= 2 ^ 31 - 1) by lia.
  exact (TXVAL fxc ReaderRes.jr_strtod (ri_x D) (ri_os D)
    (ri_i D + RT_K_W D + length (PRH_FnTx.prhtx_evs 0 0 dn))%nat
    (ri_H0 D) hist ly S Hp Wc (ms_regs ms) (ms_mem ms) md ch1 DWIN rect (ri_doc D) (ri_pretty D) 0 b
    (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) 0 0 (ri_t D) (ri_D D) txt
    Lamw peakw cntw SIZE_MAXZ ranw (ri_most D)
    (conj HPRE1 (conj HRO (conj HSHI (conj Hrac (proj1 HFX)))))
    rtt_t_univ HRM HPOS (rtt_pre_os4 B ARx CTX0 D HPRE) (fun _ => HROOMK) (fun _ => HCONS) HDEPN Ha0 Ha1 Ha2 Ha3
    HPRR HD0 HDD
    HFW HPL HTR HREC HINV HND2 HDL HHOME HRA HBV (or_introl HAPART)
    H28 HLED' (fun _ => HRUN) HLIVE HRQ HCNT).
- (* THE RETURN: the granted outcome (K0-DEAD-TXVALUE) read back; the advance is exactly the value's events *)
  intros ly2 S2 Hp2 W2 regs2 mem2 md2 k2 k1 WS1 HJ2 HJ1 HPW HW1 HP2 (HQ & HMN2).
  destruct HQ as (b1 & cap1 & f1 & own' & pre & HPOST & HOUT & HDEAD & _ & _ & _ & _ & HRM2 &
    j & hist' & _ & HP' & HJJ & _ & HL2).
  specialize (HDEAD eq_refl). subst f1.
  destruct HOUT as [(_ & _ & Eown & Epre & Ecap) | [(Hf & _) | (_ & Hf1 & _)]];
    [| exfalso; exact (Hf eq_refl) | exfalso; lia].
  subst own' pre cap1.
  specialize (HJJ eq_refl eq_refl). subst j.
  pose proof HPOST as (HREC2 & HINV2 & _ & EHp & HGR & HBB2).
  pose proof (rtt_t_base_txcall ly S Hp Wc (ms_mem ms) md kj 0 b (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) 0 txt
    (@STK_tx_value prh_img_A DOC_D) ly2 S2 Hp2 W2 mem2 md2 k2 k1 WS1 HB HBF HJ2 HJ1 HW1 HMN2 HRM2 HL2) as HB2.
  pose proof (rtt_t_buf_next ly S Hp Wc (ms_mem ms) b (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) txt
    ly2 S2 Hp2 W2 mem2 b1
    (TxModel.tx_capf (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) (TxModel.tv_calls (ri_t D) (ri_p D) 0))
    (concat (WriterValue.wvpieces (ri_t D) (ri_p D) 0)) HBF HREC2 HINV2 HGR HBB2) as HBF2.
  assert (Elen : TxModel.zsum dn + Z.of_nat (length (concat (WriterValue.wvpieces (ri_t D) (ri_p D) 0))) =
                 TxModel.zsum (dn ++ TxModel.tv_calls (ri_t D) (ri_p D) 0)).
  { rewrite TxModel.zsum_app, rtt_t_zsum_tv. reflexivity. }
  assert (Ecapn : TxModel.tx_capf (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) (TxModel.tv_calls (ri_t D) (ri_p D) 0) =
                  TxModel.tx_capf 0 0 (dn ++ TxModel.tv_calls (ri_t D) (ri_p D) 0)).
  { rewrite TxModel.tx_capf_app, Z.add_0_l. reflexivity. }
  rewrite Elen, Ecapn in HBF2.
  (* the wild traces since the entry: this call's budget added (Rtt102Cut.rtt_wild_keep over its own journal) *)
  assert (HW2 : rtt_wild B D S2 (length (PRH_FnTx.prhtx_evs 0 0 dn) +
    length (PRH_FnTx.prhtx_evs (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) (TxModel.tv_calls (ri_t D) (ri_p D) 0)))).
  { eapply rtt_wild_keep; [| exact HWLD | exact HJ1 | exact (HPW eq_refl)]. reflexivity. }
  rewrite Hra. apply (HK ly2 S2 Hp2 W2 regs2 mem2 md2 k2 b1 HB2 HBF2); [| exact (rtt_t_bregs_pres _ _ HBR HP2)].
  unfold rtt_t_gpos. rewrite PRH_FnTx.prhtx_evs_app, length_app, Z.add_0_l. split; [|exact HW2].
  unfold rtt_pos. exists hist'.
  replace (ri_i D + (RT_K_W D + (length (PRH_FnTx.prhtx_evs 0 0 dn) +
      length (PRH_FnTx.prhtx_evs (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) (TxModel.tv_calls (ri_t D) (ri_p D) 0)))))%nat
    with (ri_i D + RT_K_W D + length (PRH_FnTx.prhtx_evs 0 0 dn) +
      length (PRH_FnTx.prhtx_evs (TxModel.zsum dn) (TxModel.tx_capf 0 0 dn) (TxModel.tv_calls (ri_t D) (ri_p D) 0)))%nat
    by lia.
  exact HP'.
Qed.

(* ---- the record after the memset: four zero fields, the empty buffer over the writer's blocks ---- *)
Lemma rtt_t_le0 : forall w k, le_byte 0 w k = 0.
Proof. intros w k. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.

Lemma rtt_t_vm0 : forall (W : world SEGS) mem a n,
  (forall k, (k < n)%nat -> aview SEGS (w_H W) mem (a + Z.of_nat k) = Some 0) ->
  val_mem SEGS (mrestrict (w_H W) mem) a n 0.
Proof.
intros W mem a n H k Hk. pose proof (rtt_t_val1_of_aview SEGS (w_H W) mem _ _ (H k Hk)) as (V & _).
specialize (V 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in V. rewrite Z.add_0_r in V. rewrite V.
rewrite !rtt_t_le0. reflexivity.
Qed.

Lemma rtt_t_buf0 : forall ly S Hp W mem,
  Permutation (ablocks B ly S) wab -> blocks_bytes S <= blocks_bytes S0 ->
  (forall i, 0 <= i < 32 -> aview SEGS (w_H W) mem (rect + i) = Some 0) ->
  rtt_t_buf ly S Hp W mem 0 0 0 0 0 [].
Proof.
intros ly S Hp W mem HP HBB HZ.
assert (Z8 : forall o, 0 <= o -> o + 8 <= 32 -> val_mem SEGS (mrestrict (w_H W) mem) (rect + o) 8 0).
{ intros o Ho Ho2. apply rtt_t_vm0. intros k Hk. rewrite <- Z.add_assoc. apply HZ. lia. }
assert (Z4 : val_mem SEGS (mrestrict (w_H W) mem) (rect + 24) 4 0).
{ apply rtt_t_vm0. intros k Hk. rewrite <- Z.add_assoc. apply HZ. lia. }
assert (Z0 : val_mem SEGS (mrestrict (w_H W) mem) rect 8 0).
{ pose proof (Z8 0 ltac:(lia) ltac:(lia)) as V. rewrite Z.add_0_r in V. exact V. }
split.
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
  split; [exact Z0|]. split; [exact (Z8 8 ltac:(lia) ltac:(lia))|].
  split; [exact (Z8 16 ltac:(lia) ltac:(lia)) | exact Z4]. }
split; [split; [reflexivity | left; split; [reflexivity | split; reflexivity]]|].
split; [intros _; reflexivity|]. split; [left; reflexivity|].
split; [reflexivity|]. split; [lia|].
split; [intros _; exact HP|]. split; [intros Hc; lia|]. lia.
Qed.

(* a literal register after a run: the image atom's value plus the offset *)
Ltac rttewc := repeat match goal with |- context [ew (TE ?r0 ?rc ?mo) ?n] =>
  let nn := eval vm_compute in n in
  lazymatch eval vm_compute in (Nat.ltb nn 240) with
  | true => fail
  | false => rewrite (te_img r0 rc mo n) by (unfold A_TEXT, A_LIM; lia)
  end end.

(* ---- SEGMENT 1 (+324 .. the jal at +340): a0 = s1 + 24, a1 = "", a2 = 0; then tx_put (granted) ---- *)
Lemma rtt_t_seg1 : forall ly S Hp W mem md kj rg (K : world SEGS -> config -> Prop),
  rtt_t_base ly S Hp W mem md kj 0 -> rtt_t_bregs rg ->
  Permutation (ablocks B ly S) wab -> blocks_bytes S <= blocks_bytes S0 ->
  (forall i, 0 <= i < 32 -> aview SEGS (w_H W) mem (rect + i) = Some 0) ->
  rtt_t_gpos S [] -> rtt_fx (fx := fx) fxc ->
  (* C-TXTRACE (RTT_T_TRACE_AT) *)
  rtt_t_trace_at ->
  blocks_bytes S0 <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2 b1,
     rtt_t_base ly2 S2 Hp2 W2 mem2 md2 k2 0 ->
     rtt_t_buf ly2 S2 Hp2 W2 mem2 b1 (TxModel.zsum [0]) (TxModel.tx_capf 0 0 [0]) 0 0 [] ->
     rtt_t_gpos S2 [0] -> rtt_t_bregs regs2 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg (@YK11.mkst fxc regs2 (Z_to_bv 64 (BASE + (RTT_PC_A + RTT_T_PUT1)))
       mem2 (YK11.seg_rom SEGS)) md2) K) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fxc rg (Z_to_bv 64 (BASE + (RTT_PC_A + RTT_T_MSET))) mem
    (YK11.seg_rom SEGS)) md) K.
Proof.
intros ly S Hp W mem md kj rg K HB HBR HPW HBBs HZ HGP HFX HTA HBB0 HK.
pose proof (rtt_t_nums ly S Hp W mem md kj 0 HB) as
  (Hal16 & Hceil & Hslo & Hshi & H47 & Htop2 & Htop & Hs1a & Hs1b & Hs1m & Hces).
pose proof HB as (HJ & _ & _ & _ & HMN0 & _).
pose proof HBR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4 & R21 & R22).
pose proof ASAN_CEIL_range as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
pose proof rtt_t_stk_A as (HSK1 & HSP0 & HSP1 & HSV0 & HSV1).
pose proof rtt_t_lit_rng as (L1 & L2 & _).
assert (Hrect : rect = sp1 + 24) by reflexivity.
destruct (rtt_t_ss_ok fxc (ri_regs D) rg (RTT_PC_A + RTT_T_MSET) gf_none W mem (rtt_t_facts_none _ _)) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE (ri_regs D) rg [])) by apply te_env.
assert (HPM : rtt_t_P mem) by exact HMN0.
pose (RUN := @paj_run_x_invR fxc rc SK A_prog_listing PL PA B PST ARx _ LAWS rtt_t_P rtt_t_PLAW RZW
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
paj_run_tok_x_invR RUN HS HJ SHOK HPM (0, 0).
{ cbv [ss_T ss_mem]. apply awr_ok_nil. }
assert (Hm : forall x, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem x).
{ intros x. apply HFr. intros (r & Hr & _). cbv [ss_T ss_mem In] in Hr. destruct Hr. }
assert (Hav : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a; apply aview_eq_of; apply Hm).
pose proof (rtt_t_base_keep_mem ly S Hp W mem md kj 0 (ms_mem ms) _ _ HB HJ (fun a _ _ _ => Hav a) HPM) as HB1.
pose proof (rtt_t_buf0 ly S Hp W (ms_mem ms) HPW HBBs (fun i Hi => eq_trans (Hav _) (HZ i Hi))) as HBF1.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
assert (Z2 : getr (ms_regs ms) 2 = getr rg 2) by rttkeep HS.
assert (Z8 : getr (ms_regs ms) 8 = getr rg 8) by rttkeep HS.
assert (Z9 : getr (ms_regs ms) 9 = getr rg 9) by rttkeep HS.
assert (Z18 : getr (ms_regs ms) 18 = getr rg 18) by rttkeep HS.
assert (Z19 : getr (ms_regs ms) 19 = getr rg 19) by rttkeep HS.
assert (Z20 : getr (ms_regs ms) 20 = getr rg 20) by rttkeep HS.
assert (Z25 : getr (ms_regs ms) 25 = getr rg 25) by rttkeep HS.
assert (Z26 : getr (ms_regs ms) 26 = getr rg 26) by rttkeep HS.
assert (Z3 : getr (ms_regs ms) 3 = getr rg 3) by rttkeep HS.
assert (Z4 : getr (ms_regs ms) 4 = getr rg 4) by rttkeep HS.
assert (Z21 : getr (ms_regs ms) 21 = getr rg 21) by rttkeep HS.
assert (Z22 : getr (ms_regs ms) 22 = getr rg 22) by rttkeep HS.
assert (A41 : ew (TE (ri_regs D) rg []) 41 = w64 sp1) by (rewrite <- R9; te_close).
assert (X10 : getr (ms_regs ms) 10 = w64 rect).
{ rewrite Q10, A41. unfold w64. rewrite unsigned_lit_small by lia. rewrite Hrect. reflexivity. }
assert (X11 : getr (ms_regs ms) 11 = w64 RTT_LIT0_A).
{ rewrite Q11. rttewc. unfold w64, RTT_LIT0_A.
  first [ rewrite unsigned_lit_small by (split; vm_compute; [discriminate | reflexivity]); reflexivity
        | reflexivity ]. }
assert (X12 : getr (ms_regs ms) 12 = w64 (Z.of_nat (length (@nil Z)))) by (rewrite Q12; reflexivity).
assert (Hra : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (RTT_PC_A + RTT_T_PUT1))) by (rewrite Q1; vm_compute; reflexivity).
assert (HBR1 : rtt_t_bregs (ms_regs ms)).
{ unfold rtt_t_bregs. rewrite Z2, Z8, Z9, Z18, Z19, Z20, Z25, Z26, Z3, Z4, Z21, Z22. exact HBR. }
assert (HSRC : src_rd W (ms_mem ms) RTT_LIT0_A []).
{ assert (E1 : 4096 <= RTT_LIT0_A) by (vm_compute; discriminate).
  assert (E2 : RTT_LIT0_A <= 2147483000) by (vm_compute; discriminate).
  unfold src_rd. cbn [length Z.of_nat].
  split; [intros j Hj; cbn in Hj; lia|]. split; [exact E1|]. split; [unfold ASAN_CEIL in *; lia|].
  split; [unfold amem_range; left; vm_compute; discriminate|].
  split; [apply range_addressable_nil; lia | intros Hc; lia]. }
assert (HKEPT : PRH_FnTx.prhtx_kept B Lamw ly S RTT_LIT0_A (Z.of_nat (length (@nil Z)))).
{ left. right. right. exact (rtt_t_lit0_img B). }
assert (Hk : 0 <= RTT_PC_A + RTT_T_PUT1 < 2 ^ 40) by (split; vm_compute; [discriminate | reflexivity]).
assert (Hk2 : (RTT_PC_A + RTT_T_PUT1) mod 2 = 0) by (vm_compute; reflexivity).
apply (rtt_t_gput_core W _ _ ms ly S Hp _ _ 0 [] [] RTT_LIT0_A []
  (TxModel.tv_calls (ri_t D) (ri_p D) 0 ++ (if ri_p D then [1] else [])) (RTT_PC_A + RTT_T_PUT1) K
  HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl HB1 HBF1 HGP HBR1 X10 X11 X12 Hra Hk Hk2
  HFX HTA HSRC HKEPT ltac:(intros a Ha; cbn in Ha; lia) HBB0).
intros ly2 S2 Hp2 W2 regs2 mem2 md2 k2 b1 HB2 HBF2 HGP2 HBR2.
exact (HK ly2 S2 Hp2 W2 regs2 mem2 md2 k2 b1 HB2 HBF2 HGP2 HBR2).
Qed.

(* ---- the buffer across a run that wrote nothing: every field is read through the restricted memory, pointwise ---- *)
Lemma rtt_t_vm_keep : forall (W : world SEGS) mem mem' a n v,
  (forall x, mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  val_mem SEGS (mrestrict (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem') a n v.
Proof. intros W mem mem' a n v Hm V k Hk. specialize (V k Hk). unfold mbyte in *. rewrite Hm. exact V. Qed.

Lemma rtt_t_buf_keep : forall ly S Hp (W : world SEGS) mem mem' b len cap f own txt,
  (forall x, mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  rtt_t_buf ly S Hp W mem b len cap f own txt -> rtt_t_buf ly S Hp W mem' b len cap f own txt.
Proof.
intros ly S Hp W mem mem' b len cap f own txt Hm HBF.
assert (Hav : forall a, aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) by (intros a; apply aview_eq_of; apply Hm).
pose proof HBF as (HREC & HINV & H3 & H4 & H5 & H6 & H7 & H8 & H9).
split.
{ destruct HREC as (R1 & R2 & R3 & R4 & V1 & V2 & V3 & V4).
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  split; [exact (rtt_t_vm_keep W mem mem' _ _ _ Hm V1)|].
  split; [exact (rtt_t_vm_keep W mem mem' _ _ _ Hm V2)|].
  split; [exact (rtt_t_vm_keep W mem mem' _ _ _ Hm V3) | exact (rtt_t_vm_keep W mem mem' _ _ _ Hm V4)]. }
split; [|exact (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 H9))))))].
destruct HINV as (L & [E0 | (Hc & Hl & Hin & Hby & H4096 & Hce & Ham & Hw & Hra & Hhu & Hlam)]);
  [split; [exact L | left; exact E0]|].
split; [exact L|]. right.
split; [exact Hc|]. split; [exact Hl|]. split; [exact Hin|].
split; [intros j Hj; destruct (Hby j Hj) as (V & R); split; [eapply rtt_t_vm_keep; eassumption | exact R]|].
split; [exact H4096|]. split; [exact Hce|]. split; [exact Ham|].
split; [intros a Ha; specialize (Hw a Ha); unfold writable_at in *; unfold wview in *; rewrite Hm; exact Hw|].
split; [eapply range_addressable_agree; [|exact Hra]; intros x _; apply Hav|].
split; [intros s0 Hs0; rewrite Hav; exact (Hhu s0 Hs0)|].
exact Hlam.
Qed.

(* ---- RT_TXE ASSEMBLED: the rendering done on the granted path, its buffer holding the writer's document; the wild
   traces stored are its grows, within RTT_WK_T (so within the text's 32). K0-AMR8 (rtt_at_txe's
   YGcfStr.amem_range8 want, whose high-band arm needs kHighMemBeg + 15 <= want) is the engine's alx_blocks_hi. ---- *)
Lemma rtt_t_txe_asm : forall ly S Hp W regs mem md kj b txt,
  rtt_t_base ly S Hp W mem md kj 0 ->
  rtt_t_buf ly S Hp W mem b (TxModel.zsum (ck_rtt_ns (ri_t D) (ri_p D)))
    (TxModel.tx_capf 0 0 (ck_rtt_ns (ri_t D) (ri_p D))) 0 0 txt ->
  txt = ri_tb D ->
  rtt_t_gpos S (ck_rtt_ns (ri_t D) (ri_p D)) -> rtt_t_bregs regs -> rtt_fx (fx := fx) fxc ->
  rtt_wout B D q Lamw cntw ranw wab ->
  blocks_bytes S0 <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) ->
  rtt_at_txe (fx := fx) B ARx SK D fxc ly S Hp W regs mem md kj pos.
Proof.
intros ly S Hp W regs mem md kj b txt HB HBF Etxt HGP HBR HFX HWO HBB0.
pose proof HB as (HJ & HFA & HFR & HSV & HMN & HRO & HRM & HND & HTV & HRA & HCF & HCP & HLED & HQB & HQBLK & HDL &
  HCPF).
pose proof HBF as (HREC & HINV & _ & _ & HLEN & Hcap0 & HP0 & HP1 & HBB).
pose proof HBR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4 & R21 & R22).
pose proof HJ as (HAR & _).
pose proof (rtt_t_cap_pos (ri_t D) (ri_p D)) as Hc2.
pose proof (rtt_t_cap_req (ri_t D) (ri_p D)) as HTR.
pose proof rtt_t_pre_facts as (_ & _ & _ & _ & HWL & _).
pose proof ASAN_CEIL_range as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
pose proof rtt_t_stk_A as (HSK1 & HSP0 & HSP1 & HSV0 & HSV1).
pose proof (@cf_head_nonneg cp) as Hh0.
destruct HGP as (HGPOS & HGW).
assert (HW30 : rtt_wild B D S RTT_WK_T) by (eapply rtt_wild_le; [exact rtt_t_evs_all | exact HGW]).
assert (HW32 : rtt_wild B D S (prh_wk F_round_trip_text)).
{ eapply rtt_wild_le; [|exact HW30]. assert (Ewk : prh_wk F_round_trip_text = 32%nat) by reflexivity.
  rewrite Ewk. unfold RTT_WK_T. lia. }
subst txt.
assert (En : TxModel.zsum (ck_rtt_ns (ri_t D) (ri_p D)) = Z.of_nat (length (ri_tb D))).
{ change (TxModel.zsum (ck_rtt_ns (ri_t D) (ri_p D))) with (ck_tx_len (ri_t D) (ri_p D)).
  rewrite rtt_t_txlen. reflexivity. }
destruct HINV as (Hlen' & [(Hz & _) | (Hcpos & Hlc & Hin & Hby & H4096 & Hceil & Hamr & Hw & Hra & Hhu & Hlam)]);
  [lia|].
pose proof (HP1 Hcpos) as HP2.
assert (HT29 : TX_req (ri_t D) (ri_p D) <= 2 ^ 29).
{ unfold TX_req. rewrite rtt_t_txlen. change (ri_tb D) with (WriterValue.wdoc (ri_t D) (ri_p D)) in *.
  unfold PjWriteHyp.wlen in HWL. lia. }
assert (HnHp : ~ In b Hp).
{ intros HinHp. pose proof HLED as ((_ & _ & _ & HPHp) & _).
  apply (Permutation_in _ HPHp) in HinHp. apply in_map_iff in HinHp as ((a & k) & Ea & Hak).
  exact (Hlam a k Hak Ea). }
split.
{ split; [exact HFX|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact HSV|].
  split; [unfold rtt_cregs; cbv zeta; rewrite HFA; repeat split; assumption|].
  split; [exact HMN|]. split; [exact HRO|]. split; [exact HRM|]. split; [exact HND|].
  split; [exact HTV | exact HW32]. }
split; [exact R21|]. split; [exact HCP|].
pose proof HWO as (Hq0 & _).
exists q, Lamw, peakw, cntw, ranw, wab, b, (TxModel.zsum (ck_rtt_ns (ri_t D) (ri_p D))),
  (TxModel.tx_capf 0 0 (ck_rtt_ns (ri_t D) (ri_p D))).
split; [exact R22|]. split; [exact HLED|]. split; [exact HWO|]. split; [exact (HQB Hq0)|].
split; [destruct HREC as (_ & _ & _ & _ & V1 & V2 & V3 & V4); split; [exact V1 | split; [exact V2 | split;
  [exact V3 | exact V4]]]|].
split; [lia|]. split; [exact En|]. split; [exact Hby|].
split.
{ split; [lia|]. split; [exact Hin|].
  split; [intros Hin0; exact (rtt_t_nodup ly S Hp W mem md (b, TxModel.tx_capf 0 0 (ck_rtt_ns (ri_t D) (ri_p D)))
    wab HAR Hcpos HP2 (HWAB _ Hin0))|].
  split; [exact HnHp | exact HTR]. }
split; [lia|].
split.
{ destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b _ HAR Hin) as (_ & _ & _ & Happ & _).
  rewrite (rtt_t_req_pos _ Hcpos) in Happ. unfold YGcfStr.amem_range8.
  unfold in_app, ASAN_CEIL in Happ. destruct Happ as [_ [HLo | [HHi1 HHi2]]].
  - left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
  - right. pose proof (alx_blocks_hi SEGS B ARx LAWS ly S Hp W mem md b _ HAR Hin HHi1) as Hhi16.
    split; [lia|]. unfold kHighMemEnd in *. lia. }
split.
{ symmetry. apply rtt_t_cap_rcaps.
  pose proof (PRH_Supply.tv_calls_tx_val (ri_t D) (ri_p D) 0) as K. change (Z.of_nat 0) with 0 in K. exact K. }
split; [exact HP2|].
split; [unfold PRH_FnTx.LIVE_tx; lia|].
split; [|exact HW30].
rewrite PRH_Supply.prhtx_evs_r_evs in HGPOS. unfold RT_K_R. unfold RT_K_W in HGPOS. exact HGPOS.
Qed.

(* ---- the state after a run that wrote nothing, at the run's memory ---- *)
Lemma rtt_t_after_run : forall ly S Hp (W : world SEGS) mem md kj b len cap txt mem' md' kj',
  rtt_t_base ly S Hp W mem md kj 0 -> rtt_t_buf ly S Hp W mem b len cap 0 0 txt ->
  AJ STKR sp0 (ri_FP D) (ri_ly D) (EJ S) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)]
    ly S Hp W mem' md' kj' ->
  (forall x, mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  rtt_t_P mem' ->
  rtt_t_base ly S Hp W mem' md' kj' 0 /\ rtt_t_buf ly S Hp W mem' b len cap 0 0 txt.
Proof.
intros ly S Hp W mem md kj b len cap txt mem' md' kj' HB HBF HJ Hm HPM.
assert (Hav : forall a, aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) by (intros a; apply aview_eq_of; apply Hm).
split; [exact (rtt_t_base_keep_mem ly S Hp W mem md kj 0 mem' md' kj' HB HJ (fun a _ _ _ => Hav a) HPM)|].
exact (rtt_t_buf_keep ly S Hp W mem mem' b len cap 0 0 txt Hm HBF).
Qed.

(* ---- SEGMENT 2 (+344 .. the jal at +360): a0 = s1 + 24, a1 = s4 = doc, a2 = s5 = pretty, a3 = 0; then tx_value ---- *)
Lemma rtt_t_seg2 : forall ly S Hp W mem md kj rg b (K : world SEGS -> config -> Prop),
  rtt_t_base ly S Hp W mem md kj 0 ->
  rtt_t_buf ly S Hp W mem b (TxModel.zsum [0]) (TxModel.tx_capf 0 0 [0]) 0 0 [] ->
  rtt_t_gpos S [0] -> rtt_t_bregs rg -> rtt_fx (fx := fx) fxc ->
  (* C-TXTRACE (RTT_T_TRACE_AT) *)
  rtt_t_trace_at ->
  blocks_bytes S0 <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2 b1,
     rtt_t_base ly2 S2 Hp2 W2 mem2 md2 k2 0 ->
     rtt_t_buf ly2 S2 Hp2 W2 mem2 b1 (TxModel.zsum ([0] ++ TxModel.tv_calls (ri_t D) (ri_p D) 0))
       (TxModel.tx_capf 0 0 ([0] ++ TxModel.tv_calls (ri_t D) (ri_p D) 0)) 0 0
       ([] ++ concat (WriterValue.wvpieces (ri_t D) (ri_p D) 0)) ->
     rtt_t_gpos S2 ([0] ++ TxModel.tv_calls (ri_t D) (ri_p D) 0) -> rtt_t_bregs regs2 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg (@YK11.mkst fxc regs2 (Z_to_bv 64 (BASE + (RTT_PC_A + RTT_T_TXV)))
       mem2 (YK11.seg_rom SEGS)) md2) K) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fxc rg (Z_to_bv 64 (BASE + (RTT_PC_A + RTT_T_PUT1))) mem
    (YK11.seg_rom SEGS)) md) K.
Proof.
intros ly S Hp W mem md kj rg b K HB HBF HGP HBR HFX HTA HBB0 HK.
pose proof (rtt_t_nums ly S Hp W mem md kj 0 HB) as
  (Hal16 & Hceil & Hslo & Hshi & H47 & Htop2 & Htop & Hs1a & Hs1b & Hs1m & Hces).
pose proof HB as (HJ & _ & _ & _ & HMN0 & _).
pose proof HBR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4 & R21 & R22).
pose proof ASAN_CEIL_range as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
pose proof rtt_t_stk_A as (HSK1 & HSP0 & HSP1 & HSV0 & HSV1).
assert (Hrect : rect = sp1 + 24) by reflexivity.
destruct (rtt_t_ss_ok fxc (ri_regs D) rg (RTT_PC_A + RTT_T_PUT1) gf_none W mem (rtt_t_facts_none _ _)) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE (ri_regs D) rg [])) by apply te_env.
assert (HPM : rtt_t_P mem) by exact HMN0.
pose (RUN := @paj_run_x_invR fxc rc SK A_prog_listing PL PA B PST ARx _ LAWS rtt_t_P rtt_t_PLAW RZW
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
paj_run_tok_x_invR RUN HS HJ SHOK HPM (0, 0).
{ cbv [ss_T ss_mem]. apply awr_ok_nil. }
assert (Hm : forall x, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem x).
{ intros x. apply HFr. intros (r & Hr & _). cbv [ss_T ss_mem In] in Hr. destruct Hr. }
destruct (rtt_t_after_run ly S Hp W mem md kj b _ _ [] (ms_mem ms) _ _ HB HBF HJ Hm HPM) as (HB1 & HBF1).
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (13%bv : bv 5) Q13. prreg HS (1%bv : bv 5) Q1.
assert (Z2 : getr (ms_regs ms) 2 = getr rg 2) by rttkeep HS.
assert (Z8 : getr (ms_regs ms) 8 = getr rg 8) by rttkeep HS.
assert (Z9 : getr (ms_regs ms) 9 = getr rg 9) by rttkeep HS.
assert (Z18 : getr (ms_regs ms) 18 = getr rg 18) by rttkeep HS.
assert (Z19 : getr (ms_regs ms) 19 = getr rg 19) by rttkeep HS.
assert (Z20 : getr (ms_regs ms) 20 = getr rg 20) by rttkeep HS.
assert (Z25 : getr (ms_regs ms) 25 = getr rg 25) by rttkeep HS.
assert (Z26 : getr (ms_regs ms) 26 = getr rg 26) by rttkeep HS.
assert (Z3 : getr (ms_regs ms) 3 = getr rg 3) by rttkeep HS.
assert (Z4 : getr (ms_regs ms) 4 = getr rg 4) by rttkeep HS.
assert (Z21 : getr (ms_regs ms) 21 = getr rg 21) by rttkeep HS.
assert (Z22 : getr (ms_regs ms) 22 = getr rg 22) by rttkeep HS.
assert (A41 : ew (TE (ri_regs D) rg []) 41 = w64 sp1) by (rewrite <- R9; te_close).
assert (X10 : getr (ms_regs ms) 10 = w64 rect).
{ rewrite Q10, A41. unfold w64. rewrite unsigned_lit_small by lia. rewrite Hrect. reflexivity. }
assert (X11 : getr (ms_regs ms) 11 = w64 (ri_doc D)) by (rewrite Q11; rewrite <- R20; te_close).
assert (X12 : getr (ms_regs ms) 12 = w64 (ri_pretty D)) by (rewrite Q12; rewrite <- R21; te_close).
assert (X13 : getr (ms_regs ms) 13 = w64 0) by (rewrite Q13; reflexivity).
assert (Hra : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (RTT_PC_A + RTT_T_TXV))) by (rewrite Q1; vm_compute; reflexivity).
assert (HBR1 : rtt_t_bregs (ms_regs ms)).
{ unfold rtt_t_bregs. rewrite Z2, Z8, Z9, Z18, Z19, Z20, Z25, Z26, Z3, Z4, Z21, Z22. exact HBR. }
assert (Hk : 0 <= RTT_PC_A + RTT_T_TXV < 2 ^ 40) by (split; vm_compute; [discriminate | reflexivity]).
assert (Hk2 : (RTT_PC_A + RTT_T_TXV) mod 2 = 0) by (vm_compute; reflexivity).
assert (Ens : [0] ++ TxModel.tv_calls (ri_t D) (ri_p D) 0 ++ (if ri_p D then [1] else []) = ck_rtt_ns (ri_t D) (ri_p D))
  by reflexivity.
apply (rtt_t_gval_core W _ _ ms ly S Hp _ _ b [] [0] (if ri_p D then [1] else []) (RTT_PC_A + RTT_T_TXV) K
  HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Ens HB1 HBF1 HGP HBR1 X10 X11 X12 X13 Hra Hk Hk2
  HFX HTA HBB0).
intros ly2 S2 Hp2 W2 regs2 mem2 md2 k2 b1 HB2 HBF2 HGP2 HBR2.
exact (HK ly2 S2 Hp2 W2 regs2 mem2 md2 k2 b1 HB2 HBF2 HGP2 HBR2).
Qed.

(* the image band of A' inside YImgTop's bounds, by computation *)
Lemma rtt_t_band_A :
  4096 <= @pa_lo _ A_prog_listing PA /\ @pa_hi _ A_prog_listing PA <= kLowMemEnd - 1 /\
  @pa_lo _ A_prog_listing PA + 64 <= @pa_hi _ A_prog_listing PA /\
  (forall a, @pa_lo _ A_prog_listing PA <= a < @pa_hi _ A_prog_listing PA -> IMG_LO <= a < IMG_TOP).
Proof.
assert (E1 : IMG_LO <= @pa_lo _ A_prog_listing PA) by (vm_compute; discriminate).
assert (E2 : @pa_hi _ A_prog_listing PA <= IMG_TOP) by (vm_compute; discriminate).
split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|].
intros a Ha. lia.
Qed.

(* ---- SEGMENT 3 (+364): `beqz s5`. pretty = 0 goes to RT_TXE (+388) at once; pretty = 1 runs to the "\n" tx_put at
   +380 (a0 = s1 + 24, a1 = "\n", a2 = 1), whose return site is RT_TXE ---- *)
Lemma rtt_t_seg3 : forall ly S Hp W mem md kj rg b (K : world SEGS -> config -> Prop),
  rtt_t_base ly S Hp W mem md kj 0 ->
  rtt_t_buf ly S Hp W mem b (TxModel.zsum ([0] ++ TxModel.tv_calls (ri_t D) (ri_p D) 0))
    (TxModel.tx_capf 0 0 ([0] ++ TxModel.tv_calls (ri_t D) (ri_p D) 0)) 0 0
    ([] ++ concat (WriterValue.wvpieces (ri_t D) (ri_p D) 0)) ->
  rtt_t_gpos S ([0] ++ TxModel.tv_calls (ri_t D) (ri_p D) 0) -> rtt_t_bregs rg ->
  rtt_fx (fx := fx) fxc ->
  (* C-TXTRACE (RTT_T_TRACE_AT) *)
  rtt_t_trace_at ->
  blocks_bytes S0 <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2 b1,
     rtt_t_base ly2 S2 Hp2 W2 mem2 md2 k2 0 ->
     rtt_t_buf ly2 S2 Hp2 W2 mem2 b1 (TxModel.zsum (ck_rtt_ns (ri_t D) (ri_p D)))
       (TxModel.tx_capf 0 0 (ck_rtt_ns (ri_t D) (ri_p D))) 0 0 (ri_tb D) ->
     rtt_t_gpos S2 (ck_rtt_ns (ri_t D) (ri_p D)) -> rtt_t_bregs regs2 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg (@YK11.mkst fxc regs2 (Z_to_bv 64 (BASE + (RTT_PC_A + RT_TXE)))
       mem2 (YK11.seg_rom SEGS)) md2) K) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fxc rg (Z_to_bv 64 (BASE + (RTT_PC_A + RTT_T_TXV))) mem
    (YK11.seg_rom SEGS)) md) K.
Proof.
intros ly S Hp W mem md kj rg b K HB HBF HGP HBR HFX HTA HBB0 HK.
pose proof (rtt_t_nums ly S Hp W mem md kj 0 HB) as
  (Hal16 & Hceil & Hslo & Hshi & H47 & Htop2 & Htop & Hs1a & Hs1b & Hs1m & Hces).
pose proof HB as (HJ & _ & _ & _ & HMN0 & _).
pose proof HBR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4 & R21 & R22).
pose proof ASAN_CEIL_range as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
pose proof rtt_t_stk_A as (HSK1 & HSP0 & HSP1 & HSV0 & HSV1).
pose proof rtt_t_pre_facts as (_ & _ & _ & _ & _ & _ & HPR & _).
assert (Hrect : rect = sp1 + 24) by reflexivity.
assert (HEI : img_env VAL A_LIM (TE (ri_regs D) rg [])) by apply te_env.
assert (HPM : rtt_t_P mem) by exact HMN0.
destruct HPR as [Hpr0 | Hpr1].
- (* pretty = 0: the branch is taken, the state is RT_TXE's *)
  assert (Ep : ri_p D = false) by (unfold ri_p; rewrite Hpr0; reflexivity).
  assert (E0 : [0] ++ TxModel.tv_calls (ri_t D) (ri_p D) 0 = ck_rtt_ns (ri_t D) (ri_p D)).
  { unfold ck_rtt_ns. rewrite Ep. change (if false then [1] else @nil Z) with (@nil Z). rewrite app_nil_r.
    reflexivity. }
  assert (Et : [] ++ concat (WriterValue.wvpieces (ri_t D) (ri_p D) 0) = ri_tb D).
  { change (ri_tb D) with (WriterValue.wdoc (ri_t D) (ri_p D)). rewrite <- rtt_t_wdoc. rewrite Ep.
    change (if false then [10] else @nil Z) with (@nil Z). rewrite app_nil_r. reflexivity. }
  rewrite E0 in HBF, HGP. rewrite Et in HBF.
  assert (HG : facts_ok (TE (ri_regs D) rg []) (gf_s5 BC_EQ)).
  { apply (rtt_t_facts_s5_eq _ _ 0); [rewrite R21, Hpr0; reflexivity | lia | reflexivity]. }
  destruct (rtt_t_ss_ok fxc (ri_regs D) rg (RTT_PC_A + RTT_T_TXV) (gf_s5 BC_EQ) W mem HG) as [HS SHOK].
  pose (RUNTO := @paj_run_to_x_invR fxc rc SK A_prog_listing PL PA B PST ARx _ LAWS rtt_t_P rtt_t_PLAW RZW
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM (0, 0) (RTT_PC_A + RT_TXE).
  { cbv [ss_T ss_mem]. apply awr_ok_nil. }
  assert (Hm : forall x, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem x).
  { intros x. apply HFr. intros (r & Hr & _). cbv [ss_T ss_mem In] in Hr. destruct Hr. }
  destruct (rtt_t_after_run ly S Hp W mem md kj b _ _ (ri_tb D) (ms_mem ms) _ _ HB HBF HJ Hm HPM)
    as (HB1 & HBF1).
  assert (Z2 : getr (ms_regs ms) 2 = getr rg 2) by rttkeep HS.
  assert (Z8 : getr (ms_regs ms) 8 = getr rg 8) by rttkeep HS.
  assert (Z9 : getr (ms_regs ms) 9 = getr rg 9) by rttkeep HS.
  assert (Z18 : getr (ms_regs ms) 18 = getr rg 18) by rttkeep HS.
  assert (Z19 : getr (ms_regs ms) 19 = getr rg 19) by rttkeep HS.
  assert (Z20 : getr (ms_regs ms) 20 = getr rg 20) by rttkeep HS.
  assert (Z25 : getr (ms_regs ms) 25 = getr rg 25) by rttkeep HS.
  assert (Z26 : getr (ms_regs ms) 26 = getr rg 26) by rttkeep HS.
  assert (Z3 : getr (ms_regs ms) 3 = getr rg 3) by rttkeep HS.
  assert (Z4 : getr (ms_regs ms) 4 = getr rg 4) by rttkeep HS.
  assert (Z21 : getr (ms_regs ms) 21 = getr rg 21) by rttkeep HS.
  assert (Z22 : getr (ms_regs ms) 22 = getr rg 22) by rttkeep HS.
  assert (HBR1 : rtt_t_bregs (ms_regs ms)).
  { unfold rtt_t_bregs. rewrite Z2, Z8, Z9, Z18, Z19, Z20, Z25, Z26, Z3, Z4, Z21, Z22. exact HBR. }
  pmkst HS.
  lazymatch goal with |- ?G (mkCfg (YK11.mkst _ (Z_to_bv 64 ?pc) _ _) _) _ =>
    replace pc with (BASE + (RTT_PC_A + RT_TXE)) by (vm_compute; reflexivity) end.
  exact (HK ly S Hp W (ms_regs ms) (ms_mem ms) _ _ b HB1 HBF1 HGP HBR1).
- (* pretty = 1: the "\n" put *)
  assert (Ep : ri_p D = true) by (unfold ri_p; rewrite Hpr1; reflexivity).
  assert (Ens : ([0] ++ TxModel.tv_calls (ri_t D) (ri_p D) 0) ++ [Z.of_nat (length [10])] ++ [] =
                ck_rtt_ns (ri_t D) (ri_p D)).
  { unfold ck_rtt_ns. rewrite Ep. rewrite <- app_assoc. reflexivity. }
  assert (E1 : ([0] ++ TxModel.tv_calls (ri_t D) (ri_p D) 0) ++ [Z.of_nat (length [10])] =
               ck_rtt_ns (ri_t D) (ri_p D)) by (rewrite <- Ens, app_nil_r; reflexivity).
  assert (Et : ([] ++ concat (WriterValue.wvpieces (ri_t D) (ri_p D) 0)) ++ [10] = ri_tb D).
  { change (ri_tb D) with (WriterValue.wdoc (ri_t D) (ri_p D)). rewrite <- rtt_t_wdoc. rewrite Ep. reflexivity. }
  assert (HG : facts_ok (TE (ri_regs D) rg []) (gf_s5 BC_NE)).
  { apply (rtt_t_facts_s5_ne _ _ 1); [rewrite R21, Hpr1; reflexivity | lia | lia]. }
  destruct (rtt_t_ss_ok fxc (ri_regs D) rg (RTT_PC_A + RTT_T_TXV) (gf_s5 BC_NE) W mem HG) as [HS SHOK].
  pose (RUN := @paj_run_x_invR fxc rc SK A_prog_listing PL PA B PST ARx _ LAWS rtt_t_P rtt_t_PLAW RZW
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  paj_run_tok_x_invR RUN HS HJ SHOK HPM (0, 0).
  { cbv [ss_T ss_mem]. apply awr_ok_nil. }
  assert (Hm : forall x, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem x).
  { intros x. apply HFr. intros (r & Hr & _). cbv [ss_T ss_mem In] in Hr. destruct Hr. }
  destruct (rtt_t_after_run ly S Hp W mem md kj b _ _ _ (ms_mem ms) _ _ HB HBF HJ Hm HPM)
    as (HB1 & HBF1).
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
  assert (Z2 : getr (ms_regs ms) 2 = getr rg 2) by rttkeep HS.
  assert (Z8 : getr (ms_regs ms) 8 = getr rg 8) by rttkeep HS.
  assert (Z9 : getr (ms_regs ms) 9 = getr rg 9) by rttkeep HS.
  assert (Z18 : getr (ms_regs ms) 18 = getr rg 18) by rttkeep HS.
  assert (Z19 : getr (ms_regs ms) 19 = getr rg 19) by rttkeep HS.
  assert (Z20 : getr (ms_regs ms) 20 = getr rg 20) by rttkeep HS.
  assert (Z25 : getr (ms_regs ms) 25 = getr rg 25) by rttkeep HS.
  assert (Z26 : getr (ms_regs ms) 26 = getr rg 26) by rttkeep HS.
  assert (Z3 : getr (ms_regs ms) 3 = getr rg 3) by rttkeep HS.
  assert (Z4 : getr (ms_regs ms) 4 = getr rg 4) by rttkeep HS.
  assert (Z21 : getr (ms_regs ms) 21 = getr rg 21) by rttkeep HS.
  assert (Z22 : getr (ms_regs ms) 22 = getr rg 22) by rttkeep HS.
  assert (A41 : ew (TE (ri_regs D) rg []) 41 = w64 sp1) by (rewrite <- R9; te_close).
  assert (X10 : getr (ms_regs ms) 10 = w64 rect).
  { rewrite Q10, A41. unfold w64. rewrite unsigned_lit_small by lia. rewrite Hrect. reflexivity. }
  assert (X11 : getr (ms_regs ms) 11 = w64 RTT_LITNL_A).
  { rewrite Q11. rttewc. unfold w64, RTT_LITNL_A.
    first [ rewrite unsigned_lit_small by (split; vm_compute; [discriminate | reflexivity]); reflexivity
          | reflexivity ]. }
  assert (X12 : getr (ms_regs ms) 12 = w64 (Z.of_nat (length [10]))) by (rewrite Q12; reflexivity).
  assert (Hra : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (RTT_PC_A + RT_TXE))) by (rewrite Q1; vm_compute; reflexivity).
  assert (HBR1 : rtt_t_bregs (ms_regs ms)).
  { unfold rtt_t_bregs. rewrite Z2, Z8, Z9, Z18, Z19, Z20, Z25, Z26, Z3, Z4, Z21, Z22. exact HBR. }
  pose proof HB1 as (HJ1 & _ & _ & _ & _ & HRO1 & _).
  pose proof HJ1 as (HAR1 & _).
  pose proof rtt_t_band_A as (BLO & BHI & BLH & BIN).
  assert (Hn1 : (0 < length [10])%nat) by (cbn; lia).
  destruct (rtt_t_src_img B ARx LAWS zs_aligned img_shadow_vis_x ly S Hp W (ms_mem ms) _ Lamw RTT_LITNL_A [10]
    BLO BHI BLH BIN HAR1 HRO1 rtt_t_litnl_img Hn1 rtt_t_litnl_rom) as (HSRC & HKEPT).
  pose proof rtt_t_lit_rng as (_ & _ & L3 & L4).
  assert (HDISJ : forall a, RTT_LITNL_A <= a < RTT_LITNL_A + Z.of_nat (length [10]) ->
     ~ (rect <= a < rect + 28) /\
     ~ (b <= a < b + TxModel.tx_capf 0 0 ([0] ++ TxModel.tv_calls (ri_t D) (ri_p D) 0))).
  { intros a Ha. cbn [length Z.of_nat Pos.of_succ_nat] in Ha. split; [unfold RT_REC in *; lia|].
    intros Hb. pose proof HBF1 as (_ & HINV1 & _).
    destruct HINV1 as (_ & [(Hz & _) | (Hcp & _ & Hin & _)]); [lia|].
    pose proof (alx_client_img SEGS B ARx LAWS ly S Hp W (ms_mem ms) _ a HAR1
      ltac:(left; exists b, (TxModel.tx_capf 0 0 ([0] ++ TxModel.tv_calls (ri_t D) (ri_p D) 0)); split;
            [exact Hin | pose proof (rtt_t_req_ge (TxModel.tx_capf 0 0 ([0] ++ TxModel.tv_calls (ri_t D) (ri_p D) 0))
               ltac:(lia)); lia])) as (_ & Hnimg).
    apply Hnimg. pose proof rtt_t_litnl_img as (_ & _ & Hro).
    destruct (Hro a ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; lia)) as (Hr & _).
    destruct Hr as [(sg & Hin2 & _ & Hr) | Hr]; [exists sg; split; [exact Hin2 | exact Hr] | exact (pa_relro_img a Hr)]. }
  assert (Hk : 0 <= RTT_PC_A + RT_TXE < 2 ^ 40) by (split; vm_compute; [discriminate | reflexivity]).
  assert (Hk2 : (RTT_PC_A + RT_TXE) mod 2 = 0) by (vm_compute; reflexivity).
  apply (rtt_t_gput_core W _ _ ms ly S Hp _ _ b _ ([0] ++ TxModel.tv_calls (ri_t D) (ri_p D) 0) RTT_LITNL_A [10] []
    (RTT_PC_A + RT_TXE) K HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Ens HB1 HBF1 HGP HBR1
    X10 X11 X12 Hra Hk Hk2 HFX HTA HSRC HKEPT HDISJ HBB0).
  intros ly2 S2 Hp2 W2 regs2 mem2 md2 k2 b1 HB2 HBF2 HGP2 HBR2.
  rewrite E1 in HBF2, HGP2. rewrite Et in HBF2.
  exact (HK ly2 S2 Hp2 W2 regs2 mem2 md2 k2 b1 HB2 HBF2 HGP2 HBR2).
Qed.

(* ---- THE STRETCH, inside the section: from RT_PJW to RT_TXE, where the continuation is the RT_TXE stretch ---- *)
Lemma rtt_t_main : forall ly S Hp W regs mem md kj (Q : world SEGS -> config -> Prop),
  S0 = S -> frame_addr ly RT_CID pos = F ->
  rtt_carry (fx := fx) B ARx SK D fxc ly S Hp W regs mem md kj pos ->
  getr regs 21 = w64 (ri_pretty D) -> rtt_copy_kept D W mem -> getr regs 10 = w64 q ->
  rtt_led B D ly S Hp W mem Lamw peakw cntw ranw 0 -> rtt_wout B D q Lamw cntw ranw wab ->
  Permutation (ablocks B ly S) wab -> bytes_at W mem q (ri_tb D ++ [0]) ->
  blocks_bytes S <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) ->
  rtt_pos D S (RT_K_W D) -> rtt_wild B D S 0 ->
  (* C-TXTRACE (RTT_T_TRACE_AT) *)
  rtt_t_trace_at ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2,
     rtt_at_txe (fx := fx) B ARx SK D fxc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (mkCfg (@YK11.mkst fxc regs2 (Z_to_bv 64 (BASE + (RTT_PC_A + RT_TXE)))
       mem2 (YK11.seg_rom SEGS)) md2) Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (RTT_PC_A + RT_PJW))) mem
    (YK11.seg_rom SEGS)) md) Q.
Proof.
intros ly S Hp W regs mem md kj Q ES HF HCA R21 HCP R10 HLED HWO HPERM HQB HBB HPOS HW0 HTA HTXE.
assert (HBBs : blocks_bytes S <= blocks_bytes S0) by (rewrite ES; lia).
assert (HBB0 : blocks_bytes S0 <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D))
  by (rewrite ES; exact HBB).
pose proof HCA as (HFX & HJ & HFR & HSV & HCR & HMN & HRO & HRM & HND & HTV & _).
destruct (rtt_t_doc_home ly S Hp W mem md kj HJ) as (HCF & HRA & HCPF).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HDL0 & _) & _).
pose proof HWO as (Hq0 & _ & _ & capw & ELam & _ & _ & Hcapw & _).
assert (HB0 : rtt_t_base ly S Hp W mem md kj 0).
{ split; [exact HJ|]. split; [exact HF|]. split; [exact HFR|]. split; [exact HSV|].
  split; [exact HMN|]. split; [exact HRO|]. split; [exact HRM|]. split; [exact HND|].
  split; [exact HTV|]. split; [exact HRA|]. split; [exact HCF|]. split; [exact HCP|].
  split; [exact HLED|]. split; [intros _; exact HQB|].
  split; [intros _; exists capw; split; [rewrite ELam; left; reflexivity | exact Hcapw]|].
  split; [intros bk Hbk; exact (HLAMW _ (HDL0 _ Hbk)) | exact HCPF]. }
assert (HCRG : rtt_t_cregs regs).
{ unfold rtt_cregs in HCR. cbv zeta in HCR. rewrite HF in HCR.
  destruct HCR as (C2 & C8 & C9 & C18 & C19 & C20 & C25 & C26 & C3 & C4).
  unfold rtt_t_cregs.
  split; [exact C2|]. split; [exact C8|]. split; [exact C9|]. split; [exact C18|]. split; [exact C19|].
  split; [exact C20|]. split; [exact C25|]. split; [exact C26|]. split; [exact C3|]. split; [exact C4 | exact R21]. }
apply (rtt_t_step0 ly S Hp W mem md kj 0 regs Q HB0 HCRG R10).
intros mem1 md1 kj1 rg1 HB1 HBR1 HZ HKEEP.
assert (HGP0 : rtt_t_gpos S []).
{ unfold rtt_t_gpos. cbn [PRH_FnTx.prhtx_evs length]. rewrite Nat.add_0_r. exact (conj HPOS HW0). }
apply (rtt_t_seg1 ly S Hp W mem1 md1 kj1 rg1 Q HB1 HBR1 HPERM HBBs
  (fun i Hi => HZ i Hi) HGP0 HFX HTA HBB0).
intros ly2 S2 Hp2 W2 regs2 mem2 md2 k2 b1 HB2 HBF2 HGP2 HBR2.
apply (rtt_t_seg2 ly2 S2 Hp2 W2 mem2 md2 k2 regs2 b1 Q HB2 HBF2 HGP2 HBR2 HFX HTA HBB0).
intros ly3 S3 Hp3 W3 regs3 mem3 md3 k3 b2 HB3 HBF3 HGP3 HBR3.
apply (rtt_t_seg3 ly3 S3 Hp3 W3 mem3 md3 k3 regs3 b2 Q HB3 HBF3 HGP3 HBR3 HFX HTA HBB0).
intros ly4 S4 Hp4 W4 regs4 mem4 md4 k4 b3 HB4 HBF4 HGP4 HBR4.
exact (HTXE ly4 S4 Hp4 W4 regs4 mem4 md4 k4
  (rtt_t_txe_asm ly4 S4 Hp4 W4 regs4 mem4 md4 k4 b3 (ri_tb D) HB4 HBF4 eq_refl HGP4 HBR4 HFX HWO HBB0)).
Qed.

(* ---- the text owner's FPState check, in its 17:5xZ AMENDED form (Print, implicits on, notations off, so a second
   FPState inside a Prop BODY cannot hide): this Section binds BOTH the contract's entry float state fx (Section
   d's Context) and the cut's fxc (a Variable). Every Prop-bodied definition of this stretch is PRINTED into the
   build log; the cut's own predicates are the cut file's to print (Rtt102CutCheck.v). ---- *)
Set Printing Implicit.
Unset Printing Notations.
Print rtt_t_base.
Print rtt_t_buf.
Print rtt_t_cpre.
Print rtt_t_bregs.
Print rtt_t_cregs.
Print rtt_t_P.
Print rtt_t_gpos.
Print rtt_t_trace_at.
Check (@rtt_at_pjw).
Check (@rtt_at_txe).
Check (@rtt_seg).
Set Printing Notations.
Unset Printing Implicit.

End g.

(* ================================================================================================= *)
(* ---- THE ONE TAGGED PREMISE, at Section f where B is bound, and THE TOP LEMMA ----

   C-TXTRACE (RTT_T_TRACE_AT). At each of the three tx calls the kit text asks PRH_FnTx.prhtx_trace B ly W mem rect
   (rect = s1 + 24, the record on round_trip_text's real stack), STATE-FREE since the batch kit's cut. It has two halves:
   (U) THE REALLOC SITE'S UNIVERSE FACT, the one premise left: the trace cf_pc_realloc_ra0 :: pi_ret_tx_realloc ::
       <any tail> is in as_universe B (owner a Theorem Labs lane, the image binding of B). Its A' witness is
       lib/A/WildRoomInstA.v tx_trace_inU_A at ACej.Tfib_universe, word for word (0x53c74 is CfImg_A's
       cf_pc_realloc_ra0, 0x84db0 is prh_img_A's pi_ret_tx_realloc; Rtt102TopA.rtt_t_trace_inU_at_A). The membership
       `In [cf_pc_realloc_ra0; pi_ret_tx_realloc] (u_wild (as_universe B))` does NOT suffice here:
       YCbqGwild.inU_unwind_wild also needs pi_ret_tx_realloc <> cf_pc_realloc_ra0, and ci is the Section's generic
       CfImg.
   (S) THE CALLER'S STACK ABOVE THE ENTRY SP, for prhtx_trace's first half `forall a, rect - 16 <= a < ly_top ly ->
       aview .. <> None`: below the entry sp the journal's window clause gives it (rtt_t_trace_of), above it the
       text's LAST PREMISE `YGcallStackUp.astack_up_x segs ly W (spZ regs) mem` (the stack-premise text head
       4b8f95c0455c, the text owner's ruling 10:58Z) does, through Rtt102Cut.rtt_pre_up. Before that commit (S) was a
       second conjunct of this premise, `forall D, rtt_pre D -> astack_up_x ..`, false at the instance (the
       statement was vacuous there); it is now rtt_pre's own, so this premise is (U) alone. ---- *)
Definition RTT_T_TRACE_AT : Prop :=
  forall t ch, inU (as_universe B) (unwind_of_chain cf_pc_realloc_ra0 ((t, pi_ret_tx_realloc, t) :: ch)).

(* ---- STRETCH T AT IMAGE A', CONDITIONAL ON THE ONE TAGGED PREMISE ---- *)
Theorem rtt_seg_t_A_cond :
  RTT_T_TRACE_AT ->
  @RTT_SEG_T fx rc ci cp prh_img_A RL A_prog_listing PA B ARx SK CTX0.
Proof.
intros HU HTXE D HPRE fxc ly S Hp W regs mem md k pos HAT.
pose proof HAT as (HCA & R21 & HCP & q & Lamw & peakw & cntw & ranw & wab & R10 & HLED & HWO & HPERM & HQB & HBB &
  HPOS & HW0).
pose proof HWO as (Hq0 & _ & _ & capw & ELam & _ & Ewab & _).
rewrite <- RTT_PC_val, <- Z.add_assoc.
eapply (rtt_t_main D HPRE fxc S pos (frame_addr ly RT_CID pos) q Lamw peakw cntw ranw wab
  (fun x Hx => ltac:(rewrite Ewab; right; exact Hx))
  (fun x Hx => ltac:(rewrite ELam; right; exact Hx))
  ly S Hp W regs mem md k _ eq_refl eq_refl HCA R21 HCP R10 HLED HWO
  HPERM HQB HBB HPOS HW0 (conj HU (rtt_pre_up B ARx CTX0 D HPRE))).
intros ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HTXE2.
rewrite Z.add_assoc, RTT_PC_val.
exact (HTXE D HPRE fxc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos HTXE2).
Qed.

End f.
End d.

(* ---- the top lemma's assumptions, and its float-state arguments printed with implicits (the text owner's FPState
   check: rtt_seg_t_A_cond's RTT_SEG_T must carry the contract's entry fx, the same FPState as Section d's) ---- *)
Print Assumptions rtt_seg_t_A_cond.
Set Printing Implicit.
Check @rtt_seg_t_A_cond.
Unset Printing Implicit.
