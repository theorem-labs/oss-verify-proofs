(* fuzz_preset, slice S5b, lane IelemB: the PROOFS of parse_items' element-loop steps over the boundary states of
   lib/A/VrdIElem.v (image A, whole-program listing lib/A/Listing_prog.v + lib/A/PAImg_prog.v, instances
   PL_prog_A / PI_prog_A). rule 24: no function is proved here; every callee is its PUBLISHED text, taken as a
   named Section hypothesis, and every neighbouring segment is a boundary state of VrdIElem.v.

   This file proves, in this order:
     tvrd_iexit_aG -- the epilogue, listing slots 6242..6257 (rows 310..325): `mv a0, s2`, the thirteen reloads,
                      `addi sp, sp, 0x90`, `ret`. No call, no store, no branch. For every memory invariant Pm with its
                      laws (vi_iexit_okG); tvrd_iexit_a is its corollary at Pm := True (vi_iexit_ok).
     tvrd_igrow_aG -- rows 280..283: `mv a0, s4`, `jal grow`, the branch back to the loop head, for every memory
                      invariant Pm with its laws (vi_igrow_okG); tvrd_igrow_a is its corollary at Pm := True
                      (vi_igrow_ok). The section hypothesis HI_head (cf_head = PresetReqAt.HEAD) relates grow's
                      event lists to the position's.
   tvrd_ikey_a (rows 108..209) is proved by a Theorem Labs lane's PI-key lane in lib/A/VrdIKey.v and tvrd_ival_a (rows
   210..279) by the Ival walk; both statements stay in VrdIElem.v.

   A'LEDGER (a Theorem Labs lane, 2026-10-29), against the kit text a working branch 3ac20a5c9e30
   (PRH_FnParse.v blob 94232293d483, PRH_FnReader.v blob fb7b12dfa169, PRH_Base.v blob ee2f5cd7ed35, PRH_FnAlloc.v
   blob 95e26ff95e63) and A2Ipro's VrdIElem.v (707e244ec40): every prh_ledger takes g_most / g_own_ran_out (most own
   after ran, most0 own0 after ran0 in the two-ledger helpers); rd_ledger_move takes most and the WHOLE call's
   all-granted trace G (vrd_imodel / vrd_iexit_a: prhPi_gtrace at the entry cursor); vi_lm_comp / vi_grow_swap_step
   state a step's oks over its requests and most and its peak with the refusal peak over its own granted trace gtg,
   with G = tr ++ gtg ++ rest; grow's post (vi_gpost) is the kit's post-implication text, per-arm transfer and
   live-request move, OUTCOME exclusion and #102 refusal ledger in each refused arm. The pure trace helpers are proved
   once in VrdLedgerStep.v (this file Requires it; the vi_ names forward). vi_sat_grow at the end is the
   satisfiability witness of vi_grow_swap_step at the unit's own reader run.

   THE SYMBOLIC ENTRY OF A MID-FUNCTION SEGMENT. A segment of this lane does not start at a function entry, so its
   symbolic state is built by hand: the stack region is parse_items' own frame [sp, sp + 144) with sp = sp0 - 144,
   and the thirteen callee-saved words the prologue wrote are CHUNKS of that region over FRESH ATOMS 32..44, whose
   values the environment binds to the ENTRY registers (vi_extras). That is what makes the epilogue's reloads
   denote the entry registers again, which is exactly aregs_preserved. Atoms 32..44 are below A_TEXT = 240, so they
   are free (YP0b.v:13-14). No shadow entry: the epilogue makes no instrumented access, so SH = [].
   Numerals: 144 (LENGTH, parse_items' frame), the slot offsets 136 / 128 / ... / 40 (DERIVED: the listing's
   `ld` offsets 0x88 .. 0x28), the atom indices 32..44 (DERIVED: the engine's numbering). No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse VrdFrame VrdIElem
VrdCallKeep VrdLedgerStep VrdIFd.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG08cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
(* the re-hiding move's SRr' / wle' (YA0nH) and preset's zone (YGcfRehidePost.RZ_cf); the threaded hull budget *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
(* PRW_StepKit loads YF0v.v, which sets Zify's euclidean-division flag off GLOBALLY; this file's lia goals need it on
   (without this line :699 fails at once, "No applicable tactic") *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}
        {HL : Z}.
#[local] Notation PAI := PI_prog_A.
#[local] Notation PLA := PL_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PAI).
#[local] Notation VAL := (@pa_val _ A_prog_listing PAI).
#[local] Notation BASE := (@pa_val _ A_prog_listing PAI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.

(* ---- the symbolic frame of a mid-function segment ---- *)

(* the thirteen callee-saved words the prologue wrote, as the ENTRY registers they hold *)
Definition vi_extras (regs0 : bvmap 5 word) : list word :=
  [ getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20;
    getr regs0 21; getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26;
    getr regs0 27 ].

Definition vi_EI (regs regs0 : bvmap 5 word) : env :=
  @Eimg _ A_prog_listing PAI (Ereg regs (vi_extras regs0)).

(* the frame region of parse_items: [sp, sp + 144) with the thirteen saved words at the listing's offsets. Its write
   window is EMPTY: the epilogue only reads the frame, so the run's frame_of keeps every byte of memory and the write
   premise is awr_ok_cons_ro *)
Definition vi_frame_chunks : list YP09.chunk :=
  [ YP09.mkChunk 136 (CVal 8 (SOff 32 0)); YP09.mkChunk 128 (CVal 8 (SOff 33 0));
    YP09.mkChunk 120 (CVal 8 (SOff 34 0)); YP09.mkChunk 112 (CVal 8 (SOff 35 0));
    YP09.mkChunk 104 (CVal 8 (SOff 36 0)); YP09.mkChunk 96 (CVal 8 (SOff 37 0));
    YP09.mkChunk 88 (CVal 8 (SOff 38 0)); YP09.mkChunk 80 (CVal 8 (SOff 39 0));
    YP09.mkChunk 72 (CVal 8 (SOff 40 0)); YP09.mkChunk 64 (CVal 8 (SOff 41 0));
    YP09.mkChunk 56 (CVal 8 (SOff 42 0)); YP09.mkChunk 48 (CVal 8 (SOff 43 0));
    YP09.mkChunk 40 (CVal 8 (SOff 44 0)) ].
Definition vi_frame_region : YP09.region := YP09.mkRegion (Some 2%nat) 0 144 0 0 vi_frame_chunks.
Definition vi_epi_regions : smem := [ vi_frame_region ].
Definition vi_epi_facts : facts := mkFacts [] [] [].
Definition vi_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition vi_SH : list shent := [].
Definition vi_Bx : sv := SOff 26 0.
(* the symbolic state of ANY slot of the function body over that frame: only the pc moves *)
Definition vi_ss (k : nat) : sstate :=
  mkSS (4 * Z.of_nat k) sr_atoms vi_epi_regions None vi_epi_facts.

Lemma vi_base : BASE = A_prog_base.
Proof. reflexivity. Qed.

(* fpre's fourth conjunct at row 281's `jal grow` (kit 04388d628fb on: raZ regs < YM05.alloc_ceiling, PRH_Base.v:407):
   the return pc, listing slot A_IGROWRET_SLOT, is below the run's allocation ceiling - PRW_StepKit's ONE copy
   (pa_slot_lt_ceil_b), in a CLOSED goal. NEVER discharge it inside the call proof: there its vm_compute ran away
   (40 min, 60 GB RSS, killed; the S3 walk, 2026-10-29) *)
Lemma vi_grow_ret_slot_ceil : bv_unsigned (Z_to_bv 64 (BASE + 24856)) < YM05.alloc_ceiling.
Proof.
  pose proof (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PAI) 24856 ltac:(lia) ltac:(vm_compute; reflexivity)) as H.
  rewrite unsigned_lit_small; [exact H|]. rewrite vi_base. unfold A_prog_base. lia.
Qed.

Lemma vi_chunk8 : forall (E' : env) m base off (n : nat) (w : word),
  ew E' n = w -> val_mem SEGS m (base + off) 8 (bv_unsigned w) ->
  YP09.chunk_ok SEGS E' m base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
  intros E' m base off n w Hs Hv.
  apply (chunk_ok_val SEGS E' m base off 8 (SOff n 0) (bv_unsigned w)).
  - cbn [sv_denot]. rewrite Z.add_0_r, Hs. reflexivity.
  - cbn [Z.of_N]. exact (bv_unsigned_in_range 64 w).
  - cbn [Z.of_N]. lia.
  - exact Hv.
Qed.

(* ---- the charge algebra of a trace split, which every call of the loop needs: the continuation's granted trace
   is the callee's granted trace followed by the rest, and each of rd_room's three parts splits along it ---- *)

Lemma vi_rk_app : forall a b, prhPv_rk (a ++ b) = (prhPv_rk a + prhPv_rk b)%nat.
Proof. induction a as [|e a IH]; intros b; cbn [app prhPv_rk]; [reflexivity | rewrite IH; lia]. Qed.

(* FORWARDERS (A'Ledger, the Require cut): the proofs of these trace helpers live ONCE in VrdLedgerStep.v (the vl_
   names), which this file Requires; the vi_ names stay for their citers (VrdIPro.v cites vi_lsum_app /
   vi_lsum_perm) *)
Lemma vi_maxreq_nonneg : forall t, 0 <= prh_maxreq t.
Proof. exact vl_maxreq_nonneg. Qed.

Lemma vi_maxreq_app : forall a b, prh_maxreq (a ++ b) = Z.max (prh_maxreq a) (prh_maxreq b).
Proof. exact vl_maxreq_app. Qed.

Lemma vi_calls_app : forall a b, PjGrammar.calls (a ++ b) = (PjGrammar.calls a + PjGrammar.calls b)%nat.
Proof. exact PjGrammar.calls_app. Qed.

Lemma vi_held_app : forall a b, PjGrammar.held (a ++ b) = PjGrammar.held a + PjGrammar.held b.
Proof. exact PjGrammar.held_app. Qed.

Lemma vi_hpeak_nonneg : forall t, 0 <= hpeakR t.
Proof. exact vl_hpeak_nonneg. Qed.

Lemma vi_hpeak_app : forall a b, hpeakR (a ++ b) = Z.max (hpeakR a) (PjGrammar.held a + hpeakR b).
Proof. exact vl_hpeak_app. Qed.

(* a granted run of jrl is its grow's granted run followed by the rest (vrd_jtail's) *)
Lemma vi_jrl_gsplit : forall f d (o : bool) n cap acc y cap1 trg,
  PjGrammar.grow o n cap [] = (Some cap1, trg, []) ->
  PjGrammar.jrl prh_jr_strtod (S f) d o n cap acc y [] =
    (fst (fst (vrd_jtail d o n cap1 acc f y [])),
     trg ++ snd (fst (vrd_jtail d o n cap1 acc f y [])),
     snd (vrd_jtail d o n cap1 acc f y [])).
Proof.
  intros f d o n cap acc y cap1 trg HG.
  rewrite vrd_jrl_unfold. unfold PjGrammar.jbind at 1. rewrite HG. cbv beta iota.
  destruct (vrd_jtail d o n cap1 acc f y []) as [[r t] ok2]. reflexivity.
Qed.

(* the granted grow of the machine's `jal grow`: at n = cap it is the two (or one) EGrow events of PjGrammar.grow,
   which is exactly PRH_Charge.prhPg_gtrace, and it never refuses on the granted oracle *)
Lemma vi_grow_granted : forall (o : bool) (n cap : nat),
  PjGrammar.grow o n cap [] =
    (Some (if Nat.ltb n cap then cap else if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat),
     prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap), []).
Proof.
  intros o n cap. unfold prhPg_gtrace. rewrite !Nat2Z.id.
  unfold PjGrammar.grow at 2. unfold PjGrammar.grow at 1.
  destruct (Nat.ltb n cap); [reflexivity|].
  unfold PjGrammar.jbind, PjGrammar.jrealloc, PjGrammar.take, PjGrammar.jret. cbn [fst snd].
  destruct o; reflexivity.
Qed.

(* ---- the ledger's user bytes and the state's block bytes, which the grow step's room and the boundary's
   lsum = held conjunct move across the call ---- *)

Lemma vi_lsum_app : forall a b, Ledger.lsum (a ++ b) = Ledger.lsum a + Ledger.lsum b.
Proof. exact vl_lsum_app. Qed.

Lemma vi_lsum_perm : forall a b, Permutation a b -> Ledger.lsum a = Ledger.lsum b.
Proof. exact vl_lsum_perm. Qed.

(* blocks_bytes sums the allocator's REQUESTS, which is exactly what ablocks carries *)
Lemma vi_blocks_bytes_lsum : forall ly S, blocks_bytes S = Ledger.lsum (ablocks B ly S).
Proof.
  intros ly S. unfold blocks_bytes, ablocks, blocks.
  induction (st_chunks S) as [|k l IH]; cbn [List.filter map fold_right Ledger.lsum]; [reflexivity|].
  destruct (is_alloc k); cbn [map Ledger.lsum]; rewrite IH; reflexivity.
Qed.

Lemma vi_prh_held_app : forall a b, prh_held (a ++ b) = prh_held a + prh_held b.
Proof.
  intros a b. unfold prh_held. rewrite PjGrammar.held_app, vi_calls_app, Nat2Z.inj_add. lia.
Qed.

(* the charge of the machine's `jal grow` at n = cap: one realloc for an array, two for an object; the largest
   single request is the kids array's 56 * cap2R cap *)
Lemma vi_gtrace_charge : forall (o : bool) (cap : Z), 0 <= cap ->
  PjGrammar.held (prhPg_gtrace o cap cap) = (if o then 64 else 56) * (cap2R cap - cap) /\
  PjGrammar.calls (prhPg_gtrace o cap cap) = (if o then 2 else 1)%nat /\
  prh_maxreq (prhPg_gtrace o cap cap) = 56 * cap2R cap.
Proof.
  intros o cap Hc. unfold prhPg_gtrace, cap2R.
  destruct (Z.eqb_spec cap 0) as [->|Hne].
  - cbn [Z.to_nat]. unfold PjGrammar.grow. cbn [Nat.ltb Nat.leb Nat.eqb].
    unfold PjGrammar.jbind, PjGrammar.jrealloc, PjGrammar.take, PjGrammar.jret.
    destruct o; cbn [fst snd app PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call
                     prh_maxreq map fold_right PjGrammar.esize]; repeat split; lia.
  - unfold PjGrammar.grow. rewrite (proj2 (Nat.ltb_ge (Z.to_nat cap) (Z.to_nat cap)) (Nat.le_refl _)).
    replace (Nat.eqb (Z.to_nat cap) 0) with false by (symmetry; apply Nat.eqb_neq; lia).
    unfold PjGrammar.jbind, PjGrammar.jrealloc, PjGrammar.take, PjGrammar.jret.
    destruct o; cbn [fst snd app PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call
                     prh_maxreq map fold_right PjGrammar.esize]; repeat split; lia.
Qed.

(* the thirteen saved words at sp0 - 8 - 8 j, in vi_extras' order: ra, x8, x9, x18 .. x27 *)
Definition vi_saved (W : world SEGS) (mem : word -> option byte) (regs0 : bvmap 5 word) : Prop :=
  forall j, (j < 13)%nat ->
    val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 8 - 8 * Z.of_nat j) 8
      (bv_unsigned (nth j (vi_extras regs0) (Z_to_bv 64 0))).

Lemma vi_ew_extra : forall regs regs0 j, (j < 13)%nat ->
  ew (vi_EI regs regs0) (32 + j) = nth j (vi_extras regs0) (Z_to_bv 64 0).
Proof.
  intros regs regs0 j Hj. unfold vi_EI.
  rewrite (Eimg_low (PI := PAI) _ (32 + j)%nat) by (unfold A_TEXT; lia).
  apply ew_Ereg_extra.
Qed.

Lemma vi_ew_low : forall (regs regs0 : bvmap 5 word) (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (vi_EI regs regs0) n = getr regs r.
Proof.
  intros regs regs0 n r Hn. unfold vi_EI.
  assert (Hlt : (n < 32)%nat) by (pose proof (u5_range r); lia).
  rewrite (Eimg_low (PI := PAI) _ n) by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ n r Hn).
Qed.

Lemma vi_frame_chunk : forall regs regs0 W mem j, (j < 13)%nat -> vi_saved W mem regs0 ->
  YP09.chunk_ok SEGS (vi_EI regs regs0) (mrestrict (w_H W) mem) (spZ regs0 - 144)
    (YP09.mkChunk (136 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))).
Proof.
  intros regs regs0 W mem j Hj HV.
  apply (vi_chunk8 _ _ _ _ _ (nth j (vi_extras regs0) (Z_to_bv 64 0))).
  - exact (vi_ew_extra regs regs0 j Hj).
  - replace (spZ regs0 - 144 + (136 - 8 * Z.of_nat j)) with (spZ regs0 - 8 - 8 * Z.of_nat j) by lia.
    exact (HV j Hj).
Qed.

(* the symbolic entry of ANY segment over parse_items' frame: the frame region at sp = sp0 - 144 over atom 2,
   read-only (a reading segment), the thirteen saved words as atoms 32..44, no shadow entry *)
Lemma vi_st_ok : forall (k : nat) (fxP : YK11.FPState) (W : world SEGS) regs0 regs mem,
  spZ regs = spZ regs0 - 144 -> 0 <= spZ regs0 - 144 -> spZ regs0 <= 2 ^ 64 ->
  vi_saved W mem regs0 ->
  st_ok_pi (fx := fxP) SEGS VAL (vi_EI regs regs0) (vi_ss k)
    (restrict (w_H W) (@YK11.mkst fxP regs (w64 (A_IPC k)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS vi_Bx vi_SH (vi_EI regs regs0) (mrestrict (w_H W) mem).
Proof.
  intros k fxP W regs0 regs mem Hsp Hlo Hhi HV.
  assert (Usp : bv_unsigned (ew (vi_EI regs regs0) 2) = spZ regs0 - 144)
    by (rewrite (vi_ew_low regs regs0 2 2%bv eq_refl); exact Hsp).
  split; [|unfold sh_ok, vi_SH; apply Forall_nil].
  rewrite (restrict_mkst_fx (fx := fxP)).
  change (w64 (A_IPC k)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat k)).
  unfold vi_ss. apply (pa_entry_st_ok_full (fx := fxP)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold vi_epi_regions. apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, vi_frame_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split.
    + intros o Ho. lia.
    + unfold vi_frame_chunks.
      repeat apply Forall_cons; try apply Forall_nil.
      * exact (vi_frame_chunk regs regs0 W mem 0 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 1 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 2 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 3 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 4 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 5 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 6 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 7 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 8 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 9 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 10 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 11 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 12 ltac:(lia) HV).
  - cbn [vi_epi_regions pairwise_disjoint all_disjoint]. exact (conj I I).
  - exact (conj I (conj I I)).
Qed.

(* the saved words of a boundary state's frame, in vi_saved's form *)
Lemma vi_saved_of_iframe : forall E P, vrd_iframe E P -> vi_saved (ip_W P) (ip_mem P) (ie_regs E).
Proof.
  intros E P (_ & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & _).
  intros j Hj.
  destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]]; [..|lia].
  - replace (spZ (ie_regs E) - 8 - 8 * Z.of_nat 0) with (spZ (ie_regs E) - 8) by lia. exact V1.
  - replace (spZ (ie_regs E) - 8 - 8 * Z.of_nat 1) with (spZ (ie_regs E) - 16) by lia. exact V2.
  - replace (spZ (ie_regs E) - 8 - 8 * Z.of_nat 2) with (spZ (ie_regs E) - 24) by lia. exact V3.
  - replace (spZ (ie_regs E) - 8 - 8 * Z.of_nat 3) with (spZ (ie_regs E) - 32) by lia. exact V4.
  - replace (spZ (ie_regs E) - 8 - 8 * Z.of_nat 4) with (spZ (ie_regs E) - 40) by lia. exact V5.
  - replace (spZ (ie_regs E) - 8 - 8 * Z.of_nat 5) with (spZ (ie_regs E) - 48) by lia. exact V6.
  - replace (spZ (ie_regs E) - 8 - 8 * Z.of_nat 6) with (spZ (ie_regs E) - 56) by lia. exact V7.
  - replace (spZ (ie_regs E) - 8 - 8 * Z.of_nat 7) with (spZ (ie_regs E) - 64) by lia. exact V8.
  - replace (spZ (ie_regs E) - 8 - 8 * Z.of_nat 8) with (spZ (ie_regs E) - 72) by lia. exact V9.
  - replace (spZ (ie_regs E) - 8 - 8 * Z.of_nat 9) with (spZ (ie_regs E) - 80) by lia. exact V10.
  - replace (spZ (ie_regs E) - 8 - 8 * Z.of_nat 10) with (spZ (ie_regs E) - 88) by lia. exact V11.
  - replace (spZ (ie_regs E) - 8 - 8 * Z.of_nat 11) with (spZ (ie_regs E) - 96) by lia. exact V12.
  - replace (spZ (ie_regs E) - 8 - 8 * Z.of_nat 12) with (spZ (ie_regs E) - 104) by lia. exact V13.
Qed.

(* a run over vi_epi_regions writes nothing: its frame_of keeps every byte *)
Lemma vi_frame_all : forall E' (m m' : word -> option byte),
  frame_of E' vi_epi_regions m m' -> forall x, m' x = m x.
Proof.
  intros E' m m' HF x. apply HF. intros (r & Hin & Hr).
  destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi vi_frame_region] in Hr. lia.
Qed.

(* two memories that agree everywhere keep every byte set *)
Lemma vi_keep_all : forall (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall Pz, rd_keep SEGS m m' Pz.
Proof.
  intros m m' H Pz. split.
  - intros a _. unfold mbyte. rewrite H. reflexivity.
  - intros a _ Hw. unfold writable_at, wview in *. rewrite H. exact Hw.
Qed.

Lemma vi_aview_all : forall (Hh : word -> bool) (m m' : word -> option byte),
  (forall x, mrestrict Hh m' x = mrestrict Hh m x) -> forall a, aview SEGS Hh m' a = aview SEGS Hh m a.
Proof. intros Hh m m' H a. unfold aview, mbyte. rewrite H. reflexivity. Qed.

Lemma vi_in_after_keep : forall m m' q text len lo hi,
  pj_in_afterR SEGS m q text len lo hi -> (forall Pz, rd_keep SEGS m m' Pz) ->
  pj_in_afterR SEGS m' q text len lo hi.
Proof.
  intros m m' q text len lo hi (p' & d' & Hp & Hd & H1 & H2 & H3 & H4) HK.
  exists p', d'. split; [exact Hp|]. split; [exact Hd|].
  split; [exact (val_mem_keep SEGS m m' q 8 p' H1 (HK _))|].
  split; [exact (val_mem_keep SEGS m m' (q + 8) 8 (text + len) H2 (HK _))|].
  split; [exact (val_mem_keep SEGS m m' (q + 16) 4 d' H3 (HK _))|].
  exact (rd_rw_keep SEGS m m' q 24 H4 (HK _)).
Qed.

(* a register of a symbolic state, its listing value computed *)
Ltac vi_reg HS r Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [sv_denot] in Hr; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hr end.

(* a callee-saved register the epilogue reloads from saved word j *)
Ltac vi_saved_reg HS j :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    let Hr := fresh "Hr" in vi_reg HS r Hr; rewrite Hr;
    lazymatch goal with |- ew (vi_EI ?a ?b) _ = _ => exact (vi_ew_extra a b j ltac:(lia)) end end.

(* ---- 1. the epilogue, slots 6242..6257 ---- *)
(* a journal at a budget, its model materialized (YCbqG.ajournal_x_materializeR at the empty budget, through
   YCbqGwild's rebaseR / unbase0R: the budget is the journal's last conjunct, which the materialization does not read),
   over any world relation R (the re-hiding move's wle' among them) *)
Lemma vi_jrn_materialize {R : world SEGS -> world SEGS -> Prop} :
  forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS X,
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc
    (with_vm_backing (m_vm_lazy mdc) X mdc) k WS.
Proof.
  intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS X HJ.
  apply (YCbqGwild.ajournal_xw_unbase0R SEGS B prh_pst ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (st_depot Sc) WS).
  - apply (ajournal_x_materializeR (SK := SK) SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PAI) R).
    exact (YCbqGwild.ajournal_xw_rebaseR SEGS B prh_pst ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
  - exact (ajxR_wild HJ).
Qed.

(* THE GENERIC FORM (A2Ipro's tvrd_iexit_aG, VrdIElem.v at 707e244ec40; a Theorem Labs lane's generic-invariant rule, 12:19Z):
   the epilogue carries any memory invariant Pm with its laws srr_inv_laws by YC1fPx's runner twin paj_run_x_inv, and
   the return leaves the memory as the run left it. vi_iexit_ok below is its corollary at Pm := fun _ => True.
   THE KIT'S CUT: the position's journal is at the budget ie_CW E (VrdIElem.vrd_ijrn); the run is stated at the empty
   budget, so it runs from the journal rebased to the position's depot (YCbqGwild.ajournal_xw_rebaseR), and the post is
   fpostWFb at wbudget CW 0 with the position's own budget CW (VrdIElem.vrd_wbudget_cw). The answer carries the post's
   new free-order and capacity conjuncts straight from vrd_iexit_a (the epilogue writes no byte).
   THE RE-HIDING MOVE: the position's journal is at wle' SEGS RZ_cf, so the run is the runner's R form at wle' and the
   return, which keeps the world, is lifted by YA0nH.SRr_SRr'; the hull use is vrd_iexit_a's, in the post's place. *)
Theorem vi_iexit_okG : forall CTX CTX0 CW, tvrd_iexit_aG B ARx SK CTX CTX0 CW.
Proof.
  unfold tvrd_iexit_aG, tvrd_iexit_aP. intros CTX CTX0 CW Pm PLAW E P res HEN HX HPM.
  pose proof (vi_saved_of_iframe E P (proj1 HX)) as HSV.
  destruct HX as (HFR & HJN & Hgp & Htp & Hs2 & Hres & HLED & HROOM & HXF & HOUT & HLM & HBB & HLS & HANS & HLIVE
    & HHU & HINJ).
  destruct HFR as (Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  destruct HJN as (HJw & HWIN & HFZ & HFK & HROD & HBM & HCH2).
  destruct HEN as ((HAFN & HROD0 & Hstkhi) & Hq & Hv & Ho & HRD & Hp & Hnth & HRM & HRP0 & HCTX & HUNIV & HCUR & HCHAIN
    & HQCH & HFCH & HCTX2 & Hfr & (HCW & _ & _ & _)).
  destruct HAFN as (HAR & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  (* the run is stated at the empty budget: the journal rebased to the position's depot *)
  pose proof (YCbqGwild.ajournal_xw_rebaseR SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ.
  destruct (vi_st_ok A_IEPI_SLOT (ip_fx P) (ip_W P) (ie_regs E) (ip_regs P) (ip_mem P) Hsp ltac:(lia) ltac:(lia) HSV)
    as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (vi_EI (ip_regs P) (ie_regs E))) by (unfold vi_EI; apply Eimg_env).
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW
                (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf)
                (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RET := paj_ret_at (fx := ip_fx P) (PL := PLA) (PI := PAI)).
  unfold vrd_cfg.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vi_Bspan;
    [eapply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
  match goal with ms0 : machine_state |- _ => rename ms0 into ms2 end.
  pose proof (vi_frame_all _ _ _ HFr) as HM.
  pose proof (vi_keep_all _ _ HM) as HK.
  vi_reg HS (Z_to_bv 5 1) R1. vi_reg HS (Z_to_bv 5 10) R10.
  assert (E1 : getr (ms_regs ms2) 1 = getr (ie_regs E) 1).
  { transitivity (getr (ms_regs ms2) (Z_to_bv 5 1)); [reflexivity|]. rewrite R1.
    exact (vi_ew_extra (ip_regs P) (ie_regs E) 0 ltac:(lia)). }
  apply (SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  eapply (RET (ip_W P) _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat2. split; [|exact HPM]. unfold fpostWFb, YCbqGwild.fpostWF_xbR.
  exists (ip_fx P), (ip_ly P), (ip_S P), (ip_Hp P), (ms_regs ms2), (ms_mem ms2).
  exists (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy (ip_md P)) mat (ip_md P))) mat2
            (with_vm_backing (m_vm_lazy (ip_md P)) mat (ip_md P))), (ip_k P), (ie_CW E).
  split; [unfold YK0s.ret_ok in Hra; rewrite E1, Hra; reflexivity|].
  split; [exact HFZ|]. split; [exact HFK|].
  split; [rewrite HCW; exact (vrd_wbudget_cw CW)|].
  split; [apply vi_jrn_materialize;
          exact (YCbqGwild.ajournal_xw_unbase0R SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ (ajxR_wild HJw))|].
  split; [intros a Ha Hn; rewrite (vi_aview_all _ _ _ HM a); exact (HWIN a Ha Hn)|].
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                 r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]].
    - vi_reg HS (Z_to_bv 5 2) R2. rewrite R2.
      rewrite (vi_ew_low (ip_regs P) (ie_regs E) 2 (Z_to_bv 5 2) eq_refl).
      change (bv_unsigned (getr (ip_regs P) (Z_to_bv 5 2))) with (spZ (ip_regs P)). rewrite Hsp.
      replace (spZ (ie_regs E) - 144 + 144) with (spZ (ie_regs E)) by lia.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    - vi_reg HS (Z_to_bv 5 3) R3. rewrite R3, (vi_ew_low (ip_regs P) (ie_regs E) 3 (Z_to_bv 5 3) eq_refl).
      etransitivity; [exact Hgp|]. symmetry. exact Hgp0.
    - vi_reg HS (Z_to_bv 5 4) R4. rewrite R4, (vi_ew_low (ip_regs P) (ie_regs E) 4 (Z_to_bv 5 4) eq_refl).
      etransitivity; [exact Htp|]. symmetry. exact Htp0.
    - vi_saved_reg HS 1%nat.
    - vi_saved_reg HS 2%nat.
    - vi_saved_reg HS 3%nat.
    - vi_saved_reg HS 4%nat.
    - vi_saved_reg HS 5%nat.
    - vi_saved_reg HS 6%nat.
    - vi_saved_reg HS 7%nat.
    - vi_saved_reg HS 8%nat.
    - vi_saved_reg HS 9%nat.
    - vi_saved_reg HS 10%nat.
    - vi_saved_reg HS 11%nat.
    - vi_saved_reg HS 12%nat. }
  destruct HANS as (r2 & okr & Hjr & Hok & Hfail).
  assert (HMeq : mrestrict (w_H (ip_W P)) (ms_mem ms2) = mrestrict (w_H (ip_W P)) (ip_mem P))
    by (apply functional_extensionality; exact HM).
  unfold vrd_items_q, tpiP_Q.
  exists (ip_ok P), (if res =? 0 then Some (mk (ie_o E) (rev (ip_acc P)), r2) else None), (ip_tr P), okr,
    (ip_D P), (ip_Lam P), (ip_peak P), (ip_cnt P), (ip_fail P), (ip_ran P).
  split; [rewrite vrd_strtod_same; exact Hjr|].
  split.
  { apply (prh_ledger_kept (L := A_prog_listing) (PA := PAI) B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P));
      [exact HLED | | | | apply Permutation_refl].
    - intros a _. exact (proj1 (HK (fun _ => True)) a I).
    - intros a k i _ _. exact (proj1 (HK (fun _ => True)) _ I).
    - intros a k _ Hab. exact Hab. }
  split; [exact HROOM|]. split; [exact HHU|]. split; [exact HLIVE|]. split; [exact HXF|].
  split.
  { intros sm x os i H0 hist HP HR HC Hf.
    destruct (HOUT sm x os i H0 hist HP HR HC Hf) as (Hran & Hfst & Hx).
    split; [exact Hran|]. split; [|exact Hx].
    rewrite Hfst, vrd_strtod_same, Hjr. reflexivity. }
  split; [exact HINJ|].
  split; [exact HLM|]. split; [exact HBM|]. split; [exact HBB|]. split; [exact HLS|].
  assert (A10 : getr (ms_regs ms2) 10 = w64 res).
  { transitivity (getr (ms_regs ms2) (Z_to_bv 5 10)); [reflexivity|].
    rewrite R10, (vi_ew_low (ip_regs P) (ie_regs E) 18 (Z_to_bv 5 18) eq_refl). exact Hs2. }
  destruct Hres as [-> | ->].
  - cbn [Z.eqb]. destruct (Hok eq_refl) as (Hin & Hnode & Hsum & HFO & HNC).
    split; [exact A10|]. split; [rewrite HMeq; exact HFO|]. split; [|split; [|split]].
    + exact (pj_in_okR_keep SEGS _ _ _ _ _ _ _ _ Hin (HK _)).
    + exact (pj_nodeR_keep SEGS _ _ _ _ _ _ _ Hnode (fun x k _ h => h) (HK _)).
    + rewrite HMeq. exact HNC.
    + exact Hsum.
  - cbn [Z.eqb]. destruct (Hfail eq_refl) as (Hin & Hfd & HFO).
    split; [exact A10|]. split; [rewrite HMeq; exact HFO|]. split.
    + exact (vi_in_after_keep _ _ _ _ _ _ _ Hin HK).
    + exact (pj_fdR_keep SEGS _ _ _ _ _ _ _ Hfd (fun x k _ h => h) (HK _)).
Qed.

(* the step Prop of record: the corollary of vi_iexit_okG at the trivial invariant (VrdIElem.tvrd_iexit_a_of_P) *)
Theorem vi_iexit_ok : forall CTX CTX0 CW, tvrd_iexit_a B ARx SK CTX CTX0 CW.
Proof.
  intros CTX CTX0 CW. apply tvrd_iexit_a_of_P. apply vi_iexit_okG. exact (srr_inv_laws_true SEGS).
Qed.


(* ==== THE POSITION FACTS AT A LATER STATE, after ANY callee (a Theorem Labs lane's approval, 2026-10-29: one copy for ikey
   after parse_string, ival after parse_value and the memset, ipro and igrow after grow). A journal does not keep the
   SHADOW of a heap block or of an image range across a call (ajournal_x keeps block bytes, frames with their
   shadow, image bytes and the stack above alloc_ceiling); those facts are rebuilt here from the AR_laws_x laws at
   the later state, by where the bytes live. FOUR NAMED HYPOTHESES, each an instance / image fact:
   - H_HL: the harness-block shadow law's head length is cf_head (AR_laws_x field 14; at the cf instance YGcallcf's
     builder concludes at cf_head, so this is an identity there; VrdArm.v carries the same);
   - H_zsal: the image's zero-shadow ranges are granule-aligned (asyms_ok's aso_zshadow, which ARcf's amc_syms gives);
   - H_imgvis: the image's shadow is mapped at every state (a Theorem Labs lane's img_shadow_vis_cf, YGcfAmx2.v:47, over ARx);
   - H_pst_ro: alloc.c's statics are not read-only (S1ImgA.v pst_not_ro_A at prh_img_A). ==== *)
Hypothesis H_HL : HL = cf_head.
Hypothesis H_zsal : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
Hypothesis H_imgvis : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Hypothesis H_pst_ro : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS pa_relro_lo pa_relro_hi a.

(* a value read through views that agree byte for byte *)
Lemma vi_vm_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> aview SEGS H' m' (a + Z.of_nat k) = aview SEGS H m (a + Z.of_nat k)) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
  intros H H' m m' a n v HA Hv. apply (prh_val_mem_keep _ _ _ _ _ Hv). intros k Hk.
  apply prh_mbyte_of_aview. exact (HA k Hk).
Qed.

(* the hull of a sub-range (FuzzStrdup.v:113 sd_hull_sub, cgif YCbq.v:1945, restated) *)
Lemma vrd_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
  intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
  pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
  assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
    by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
  pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* the hull of a range 64 bytes inside the image is the shadow of image bytes (FuzzStrdup.v:123 sd_hull_img) *)
Lemma vrd_hull_img : forall a n s, 0 < n -> IMG_LO + 64 <= a -> a + n + 64 <= IMG_TOP ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ IMG_LO <= 8 * (s - SHADOW_OFF) < IMG_TOP.
Proof.
  intros a n s Hn Hlo Hhi Hs. unfold IMG_LO, IMG_TOP in *. unfold shadow_addr in *.
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

Lemma vrd_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
  intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img a Hr)].
Qed.

(* a harness block of ANY state: its user bytes are addressable and its hull is visible (field 14 at H_HL) *)
Lemma vrd_lam_shadow : forall ly S Hp W mem md Lam peak cnt fail ran most own a k,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a k /\
  (0 < k -> shadow_hull_vis (aview SEGS (w_H W) mem) a k).
Proof.
  intros ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL0 Hin.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HL0 Hin) as (Hk & Hab & Hhp & _).
  destruct (alx_hshadow SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hab Hhp) as [Hbs Hhu].
  rewrite H_HL in Hbs, Hhu. replace (a - cf_head + cf_head) with a in Hbs, Hhu by lia.
  pose proof (@cf_head_nonneg cp) as Hcf.
  assert (Hreq : k <= req_size (k + cf_head) - cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  split.
  - destruct (Z_lt_le_dec 0 k) as [Hk0 | Hk0]; [|apply range_addressable_nil; lia].
    exact (block_shadow_range _ _ _ _ a k Hbs ltac:(lia) ltac:(lia)).
  - intros Hk0. apply (vrd_hull_sub _ a (req_size (k + cf_head) - cf_head) a k); [apply Hhu | lia | lia | exact Hk0].
    unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0); lia.
Qed.

(* the real stack's shadow reads 0 at every state (field alx_zshadow_byte) *)
Lemma vrd_stack_ra : forall ly S Hp W mem md a n, ARx ly S Hp W mem md -> ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n.
Proof.
  intros ly S Hp W mem md a n HAR Hlo Hhi x Hx. exists 0.
  split; [exact (alx_zshadow_byte SEGS B ARx LAWS ly S Hp W mem md x HAR ltac:(lia)) | left; reflexivity].
Qed.

(* an ENTRY allocator block whose base is not a hidden head (the home of a text, or of a node, outside the harness
   ledger) is no hidden head at a later state either: the later heads are the entry ledger's, or bases of blocks
   allocated since (rd_blocks_move), and a block of the entry state is apart from those *)
Lemma vrd_base_not_hp : forall ly0 S0 Hp0 W0 mem0 Lam0 peak0 cnt0 fail0 ran0 most0 own0
    ly S Hp W mem md D tr rest d Lam peak cnt fail ran most own b m,
  0 <= m -> In (b, m) (ablocks B ly0 S0) -> ~ In b Hp0 ->
  prh_ledger B ly0 S0 Hp0 W0 mem0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 ->
  ARx ly S Hp W mem md -> rd_blocks_move B ly0 S0 ly S D tr rest d ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> Permutation Lam (D ++ Lam0) ->
  ~ In b Hp.
Proof.
  intros ly0 S0 Hp0 W0 mem0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 ly S Hp W mem md D tr rest d Lam peak cnt fail ran
    most own b m Hm Hin Hnh HL0 HAR (HDnew & HABp & _) HL1 HLp Hbh.
  pose proof (@cf_head_nonneg cp) as Hcf.
  destruct HL1 as (_ & _ & HF1 & HP1). apply (Permutation_in _ HP1) in Hbh.
  apply in_map_iff in Hbh as ((x & k) & Hx & HinL). cbn [fst] in Hx.
  pose proof (proj1 (Forall_forall _ _) HF1 (x, k) HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  rewrite Hx in Hab.
  apply (Permutation_in _ HLp) in HinL. apply in_app_or in HinL as [HinD | Hin0].
  - pose proof (HDnew x k HinD) as Hnew. rewrite Hx in Hnew.
    assert (Hne : (b, m) <> (b, k + cf_head)) by (intros E; rewrite E in Hin; exact (Hnew Hin)).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR
                  (Permutation_in _ (Permutation_sym HABp) (in_or_app _ _ _ (or_intror Hin))) Hab Hne) as Hdj.
    unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. unfold req_size in Hdj.
    destruct (Z.eqb_spec m 0); destruct (Z.eqb_spec (k + cf_head) 0); lia.
  - apply Hnh. destruct HL0 as (_ & _ & _ & HP0). apply (Permutation_in _ (Permutation_sym HP0)).
    apply in_map_iff. exists (x, k). split; [cbn [fst]; exact Hx | exact Hin0].
Qed.

(* ... and no later hidden head lies inside it, so field 3 (alx_shadow) gives its shadow *)
Lemma vrd_block_no_hp : forall ly0 S0 Hp0 W0 mem0 Lam0 peak0 cnt0 fail0 ran0 most0 own0
    ly S Hp W mem md D tr rest d Lam peak cnt fail ran most own b m,
  0 <= m -> In (b, m) (ablocks B ly0 S0) -> ~ In b Hp0 ->
  prh_ledger B ly0 S0 Hp0 W0 mem0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 ->
  ARx ly S Hp W mem md -> rd_blocks_move B ly0 S0 ly S D tr rest d ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> Permutation Lam (D ++ Lam0) ->
  In (b, m) (ablocks B ly S) /\ (forall h, In h Hp -> ~ (b <= h < b + req_size m)).
Proof.
  intros ly0 S0 Hp0 W0 mem0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 ly S Hp W mem md D tr rest d Lam peak cnt fail ran
    most own b m Hm Hin Hnh HL0 HAR HBM HL1 HLp.
  pose proof (vrd_base_not_hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hin Hnh HL0 HAR HBM HL1
                HLp) as Hbnot.
  pose proof HBM as (_ & HABp & _).
  assert (Hin' : In (b, m) (ablocks B ly S))
    by exact (Permutation_in _ (Permutation_sym HABp) (in_or_app _ _ _ (or_intror Hin))).
  split; [exact Hin'|].
  intros h Hh Hhin. pose proof (@cf_head_nonneg cp) as Hcf.
  pose proof HL1 as (_ & _ & HF1 & HP1). pose proof (Permutation_in _ HP1 Hh) as Hh'.
  apply in_map_iff in Hh' as ((x & k) & Hx & HinL). cbn [fst] in Hx.
  pose proof (proj1 (Forall_forall _ _) HF1 (x, k) HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  rewrite Hx in Hab.
  destruct (Z.eq_dec h b) as [-> | Hne]; [exact (Hbnot Hh)|].
  assert (Hne' : (b, m) <> (h, k + cf_head)) by (intros E; injection E as E1 _; lia).
  pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hin' Hab Hne') as Hdj.
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. unfold req_size in Hdj, Hhin.
  destruct (Z.eqb_spec m 0); destruct (Z.eqb_spec (k + cf_head) 0); lia.
Qed.

(* the text's HOME at a later state (PRH_FnReader.v prhReader_home), from its home at the entry *)
Lemma vrd_home_at : forall ly0 S0 Hp0 W0 mem0 Lam0 peak0 cnt0 fail0 ran0 most0 own0
    ly S Hp W mem md D tr rest d Lam peak cnt fail ran most own p n,
  0 <= n -> prhReader_home B ly0 S0 Hp0 Lam0 p n ->
  prh_ledger B ly0 S0 Hp0 W0 mem0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 ->
  ARx ly S Hp W mem md -> rd_blocks_move B ly0 S0 ly S D tr rest d ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> Permutation Lam (D ++ Lam0) ->
  prhReader_home B ly S Hp Lam p n.
Proof.
  intros ly0 S0 Hp0 W0 mem0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 ly S Hp W mem md D tr rest d Lam peak cnt fail ran
    most own p n Hn [Hk | (b & m & Hin & Hnh & Hb & Hm)] HL0 HAR HBM HL1 HLp.
  - left. destruct Hk as [(a & k & Hin & Ha & Hk) | Hk'].
    + left. exists a, k. split; [|lia].
      apply (Permutation_in _ (Permutation_sym HLp)). apply in_or_app. right. exact Hin.
    + right. exact Hk'.
  - assert (Hm0 : 0 <= m) by lia. right. exists b, m.
    destruct (vrd_block_no_hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hin Hnh HL0 HAR HBM HL1
                HLp) as (Hin' & _).
    split; [exact Hin'|]. split; [|lia].
    exact (vrd_base_not_hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hin Hnh HL0 HAR HBM HL1
             HLp).
Qed.

(* a byte window the reader reads (PRH_Base.v src_rd) at a later state, from the window and its home at the entry and
   the journal between: the bytes by the journal's block clause (a block of the entry state still live) or image
   clause (read-only image bytes), the shadow by the law of the home at the later state. THE KIT'S CUT: the journal at any
   budget WS (implicit; ajournal_x is WS = []): the budget is the journal's last conjunct, which no step here reads.
   The journal is at any world relation R (implicit; the re-hiding move's wle' among them): no step reads its world
   conjunct *)
Lemma vrd_src_at {R : world SEGS -> world SEGS -> Prop} {WS : list (list Z)} :
  forall STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 Lam0 peak0 cnt0 fail0 ran0 most0 own0
    ly S Hp W mem md k D tr rest d Lam peak cnt fail ran most own p (tb : list Z),
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx R STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 [] ly S Hp W mem md k WS ->
  ~ YI16.sink_open_fp FP -> (forall a, p <= a < p + Z.of_nat (length tb) -> ~ inFP FP a) ->
  src_rd W0 mem0 p tb -> prhReader_home B ly0 S0 Hp0 Lam0 p (Z.of_nat (length tb)) ->
  prh_ledger B ly0 S0 Hp0 W0 mem0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 ->
  rd_blocks_move B ly0 S0 ly S D tr rest d ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> Permutation Lam (D ++ Lam0) ->
  src_rd W mem p tb.
Proof.
  intros STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 ly S Hp W mem md k D tr rest d Lam
    peak cnt fail ran most own p tb HJ Hsink HnFP Hsrc Hhome HL0 HBM HL1 HLp.
  set (n := Z.of_nat (length tb)) in *.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & _).
  pose proof HBM as (HDnew & HABp & _).
  pose proof (@cf_head_nonneg cp) as Hcf.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  assert (Hlive : forall x, In x (ablocks B ly0 S0) -> In x (ablocks B ly S))
    by (intros x Hx; exact (Permutation_in _ (Permutation_sym HABp) (in_or_app _ _ _ (or_intror Hx)))).
  destruct Hsrc as (Hby & H4096 & Hceil & Hamr & HRA & Hhu).
  (* the bytes *)
  assert (HKb : forall a, p <= a < p + n -> aview SEGS (w_H W) mem a = aview SEGS (w_H W0) mem0 a).
  { intros a Ha.
    destruct Hhome as [[(b & m & Hin & Hb & Hm) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]]
                      | (b & m & Hin & Hnh & Hb & Hm)].
    - destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ b m _ _ HL0 Hin) as (Hm0 & Hab & _).
      replace a with (b - cf_head + (a - (b - cf_head))) by lia.
      apply (F2 (b - cf_head) (m + cf_head) (a - (b - cf_head)) Hab (Hlive _ Hab)).
      + unfold req_size. destruct (Z.eqb_spec (m + cf_head) 0); lia.
      + replace (b - cf_head + (a - (b - cf_head))) with a by lia. exact (HnFP a Ha).
    - destruct (Hro a Ha) as (Hr & Hno & Her).
      apply F3; [exact (vrd_ro_img a Hr) | exact Hno | exact Her | exact (fun Hx => H_pst_ro a Hx Hr) |].
      exact (fp_spares_closed FP a Hsink).
    - destruct (Hro a Ha) as (Hr & Hno & Her & _).
      apply F3; [exact (vrd_ro_img a Hr) | exact Hno | exact Her | exact (fun Hx => H_pst_ro a Hx Hr) |].
      exact (fp_spares_closed FP a Hsink).
    - replace a with (b + (a - b)) by lia.
      apply (F2 b m (a - b) Hin (Hlive _ Hin)).
      + unfold req_size. destruct (Z.eqb_spec m 0); lia.
      + replace (b + (a - b)) with a by lia. exact (HnFP a Ha). }
  (* the shadow *)
  assert (Hsh : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n /\
                (0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) p n)).
  { destruct Hhome as [[(b & m & Hin & Hb & Hm) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]]
                      | (b & m & Hin & Hnh & Hb & Hm)].
    - assert (HinL : In (b, m) Lam)
        by (apply (Permutation_in _ (Permutation_sym HLp)); apply in_or_app; right; exact Hin).
      destruct (vrd_lam_shadow _ _ _ _ _ _ _ _ _ _ _ _ _ b m HAR HL1 HinL) as [Hra Hh].
      split; [exact (range_addressable_sub _ _ b m p n Hra Hb Hm)|].
      intros Hn. exact (vrd_hull_sub _ b m p n (Hh ltac:(lia)) Hb Hm Hn).
    - destruct Hzs as (q & mm & Hin & Hq & Hqm).
      pose proof (proj1 (Forall_forall _ _) H_zsal (q, mm) Hin) as (Z1 & Z2). cbn [fst snd] in Z1, Z2.
      pose proof (alx_zshadow SEGS B ARx LAWS ly S Hp W mem md (q, mm) HAR
                    ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
      cbn [fst snd] in Hz.
      split; [exact (range_addressable_sub _ _ q mm p n (zero_shadow_range _ _ q mm Z1 Z2 Hz) Hq Hqm)|].
      intros Hn s0 Hs. destruct (vrd_hull_img p n s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
      exact (H_imgvis _ _ _ _ _ _ _ HAR Hr).
    - split.
      + intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzs | (v & Hv & Hv8)]).
        * destruct Hzs as (q & mm & Hin & Hq & Hqm).
          pose proof (proj1 (Forall_forall _ _) H_zsal (q, mm) Hin) as (Z1 & Z2). cbn [fst snd] in Z1, Z2.
          pose proof (alx_zshadow SEGS B ARx LAWS ly S Hp W mem md (q, mm) HAR
                        ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
          cbn [fst snd] in Hz.
          pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
          exact (range_addressable_sub _ _ q mm x 1 (zero_shadow_range _ _ q mm Z1 Z2 Hz) ltac:(lia) ltac:(lia)
                   x ltac:(lia)).
        * pose proof (alx_const_cells SEGS B ARx LAWS ly S Hp W mem md HAR) as Hcc.
          pose proof (proj1 (Forall_forall _ _) Hcc _ (Hv ly)) as Hc.
          unfold cell_holds, z1, c1 in Hc. cbn [c_at c_w c_val aeval] in Hc.
          specialize (Hc 0%nat ltac:(lia)). rewrite Z.add_0_r in Hc.
          exists v. split; [|unfold saddr_ok; lia].
          assert (Es : shadow_of_addr SHADOW_OFF x = shadow_addr x) by (unfold shadow_of_addr, shadow_addr; reflexivity).
          rewrite Es, Hc. f_equal. unfold le_byte. rewrite Z.shiftr_0_r, !Z.mod_small by lia. reflexivity.
      + intros Hn s0 Hs. destruct (vrd_hull_img p n s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
        exact (H_imgvis _ _ _ _ _ _ _ HAR Hr).
    - assert (Hm0 : 0 <= m) by lia.
      destruct (vrd_block_no_hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hin Hnh HL0 HAR HBM HL1
                  HLp) as (Hin' & Hnoh).
      destruct (alx_shadow SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin' Hnoh) as [Hbs Hhb].
      assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
      split.
      + destruct (Z_lt_le_dec 0 n) as [Hn | Hn]; [|apply range_addressable_nil; lia].
        exact (block_shadow_range _ _ _ _ p n Hbs Hb ltac:(lia)).
      + intros Hn. exact (vrd_hull_sub _ b (req_size m) p n Hhb Hb ltac:(lia) Hn). }
  destruct Hsh as [HRA' Hhu'].
  split; [|split; [exact H4096 | split; [exact Hceil | split; [exact Hamr | split; [exact HRA' | exact Hhu']]]]].
  intros j Hj. destruct (Hby j Hj) as [Hv Hr]. split; [|exact Hr].
  apply (vi_vm_aview (w_H W0) (w_H W) mem0 mem); [|exact Hv].
  intros kk Hk. apply HKb. unfold n. lia.
Qed.

(* a fake frame holding 56 bytes has a non-negative class and a granule-multiple size *)
Lemma vrd_fs8 : forall c, 56 <= fs_frame_bytes c -> 0 <= c /\ fs_frame_bytes c mod 8 = 0.
Proof.
  intros c H. unfold fs_frame_bytes in *.
  destruct (Z_lt_le_dec c 0) as [Hc | Hc].
  - exfalso. rewrite Z.shiftl_div_pow2 in H by lia.
    assert (2 <= 2 ^ (- c)) by (replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia).
    assert (64 / 2 ^ (- c) <= 32) by (apply Z.div_le_upper_bound; lia). lia.
  - split; [exact Hc|]. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mul_mod by lia.
    change (64 mod 8) with 0. rewrite Z.mul_0_l. reflexivity.
Qed.

(* the NODE's shadow at a later state, from its home at the entry (rd_pre's prhReader_at with the real-stack window
   excluded): a harness block (field 14), an allocator block outside the harness ledger (field 3: no hidden head
   lies in it), or a live fake frame (the journal keeps a frame's shadow). THE KIT'S CUT: the journal at any budget WS, and
   at any world relation R (implicit, its world conjunct unread) *)
Lemma vrd_node_ra_at {R : world SEGS -> world SEGS -> Prop} {WS : list (list Z)} :
  forall STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 Lam0 peak0 cnt0 fail0 ran0 most0
    own0 regs0 e0 ly S Hp W mem md k D tr rest d Lam peak cnt fail ran most own v,
  ARx ly0 S0 Hp0 W0 mem0 md0 ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx R STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 [] ly S Hp W mem md k WS ->
  prhReader_at B ly0 S0 Lam0 regs0 e0 v 56 -> (v + 56 <= spZ regs0 \/ spZ regs0 + e0 <= v) ->
  range_addressable (aview SEGS (w_H W0) mem0) SHADOW_OFF v 56 ->
  (forall x, v <= x < v + 56 -> ~ inFP FP (shadow_addr x)) ->
  prh_ledger B ly0 S0 Hp0 W0 mem0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 ->
  rd_blocks_move B ly0 S0 ly S D tr rest d ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> Permutation Lam (D ++ Lam0) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56.
Proof.
  intros STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 regs0 e0 ly S Hp W mem md k D tr rest
    d Lam peak cnt fail ran most own v HAR0 HJ Hat Hwin HRA0 HnFP HL0 HBM HL1 HLp.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
  pose proof (@cf_head_nonneg cp) as Hcf.
  destruct Hat as [(a & kk & Hin & Ha & Hk) | [(b & m & Hin & Hnl & Hb & Hm) | [(cid & pos & Hin & Hf1 & Hf2) | Hww]]].
  - assert (HinL : In (a, kk) Lam)
      by (apply (Permutation_in _ (Permutation_sym HLp)); apply in_or_app; right; exact Hin).
    destruct (vrd_lam_shadow _ _ _ _ _ _ _ _ _ _ _ _ _ a kk HAR HL1 HinL) as [Hra _].
    exact (range_addressable_sub _ _ a kk v 56 Hra Ha Hk).
  - assert (Hnh : ~ In b Hp0).
    { intros Hbh. pose proof HL0 as (_ & _ & HF0 & HP0). apply (Permutation_in _ HP0) in Hbh.
      apply in_map_iff in Hbh as ((x & kx) & Hx & HinL). cbn [fst] in Hx.
      pose proof (proj1 (Forall_forall _ _) HF0 (x, kx) HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
      rewrite Hx in Hab.
      destruct (Z.eq_dec m (kx + cf_head)) as [Em | Ne].
      - apply Hnl. replace (b + cf_head) with x by lia. replace (m - cf_head) with kx by lia. exact HinL.
      - assert (Hne' : (b, m) <> (b, kx + cf_head)) by (intros E; injection E; lia).
        pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR0 Hin Hab Hne') as Hdj.
        unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. unfold req_size in Hdj.
        destruct (Z.eqb_spec m 0); destruct (Z.eqb_spec (kx + cf_head) 0); lia. }
    assert (Hm0 : 0 <= m) by lia.
    destruct (vrd_block_no_hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hin Hnh HL0 HAR HBM HL1
                HLp) as (Hin' & Hnoh).
    destruct (alx_shadow SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin' Hnoh) as [Hbs _].
    assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
    exact (block_shadow_range _ _ _ _ v 56 Hbs Hb ltac:(lia)).
  - destruct (alx_frames SEGS B ARx LAWS ly0 S0 Hp0 W0 mem0 md0 cid pos HAR0 Hin) as (Hfa32 & _).
    destruct (vrd_fs8 cid ltac:(lia)) as (Hc0 & Hfs8).
    intros x Hx. destruct (HRA0 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    assert (Es : shadow_of_addr SHADOW_OFF x = shadow_addr x) by (unfold shadow_of_addr, shadow_addr; reflexivity).
    rewrite Es in Hs |- *. rewrite <- Hs.
    apply (F4 cid pos (shadow_addr x) Hin); [|exact (HnFP x Hx)].
    right. unfold in_zr, shadow_addr. cbn [fst snd].
    set (fa := frame_addr ly0 cid pos) in *. set (fs := fs_frame_bytes cid) in *.
    pose proof (Z.div_mod fa 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound fa 8 ltac:(lia)) as M1.
    pose proof (Z.div_mod x 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M2.
    pose proof (Z.div_mod fs 8 ltac:(lia)) as D3.
    assert (fa mod 8 = 0).
    { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hfa32; [|lia]. destruct Hfa32 as [kq Hkq].
      exists (4 * kq). lia. }
    lia.
  - exfalso. lia.
Qed.

(* the hull of a range inside an application range misses that range (FuzzStrdup.v:99 sd_hull_out) *)
Lemma vrd_hull_out : forall p len x n s, in_app p len -> p + len <= alloc_ceiling -> p <= x -> 0 < n -> x + n <= p + len ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> ~ (p <= s < p + len).
Proof.
  intros p len x n s Happ Hc Hx Hn Hxn Hs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_addr in Hs.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as P1.
  pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M1.
  assert (P3 : (x + n - 1) / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  assert (alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
  pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M2.
  unfold SHADOW_OFF in *. lia.
Qed.

(* the node lies in application memory (its home at the entry) *)
Lemma vrd_node_app : forall CTX CTX0 CW E, vrd_ient_ok B ARx CTX CTX0 CW E -> in_app (ie_v E) 56.
Proof.
  intros CTX CTX0 CW E HEN.
  destruct HEN as ((HAFN & _) & _ & _ & _ & HRD & _).
  pose proof HAFN as (HAR & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode & _ & _ & Hvwin & HLED0 & _).
  pose proof Hnode as (_ & _ & _ & _ & Hvat & _).
  pose proof (@cf_head_nonneg cp) as Hcf0.
  destruct Hvat as [(a0 & k0 & Hin & Hle & Hhi) | [(b0 & m0 & Hin & _ & Hle & Hhi) | [(cid & pos & Hin & Hle & Hhi) | Hww]]].
  - destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED0 Hin) as (Hk0 & Hab0 & _).
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab0) as (_ & _ & _ & Happ & _).
    apply (in_app_sub _ _ _ _ Happ); [lia | lia |]. unfold req_size. destruct (Z.eqb_spec (k0 + cf_head) 0); lia.
  - destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & Happ & _).
    apply (in_app_sub _ _ _ _ Happ); [lia | lia |]. unfold req_size. destruct (Z.eqb_spec m0 0); lia.
  - destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ cid pos HAR Hin) as (_ & _ & Happ).
    apply (in_app_sub _ _ _ _ Happ); lia.
  - exfalso. lia.
Qed.

(* ==== THE TWO LEMMAS FOR EVERY LOOP STEP WITH A CALL. Hypotheses: the call's entry data (vrd_ient_ok) and, at the
   LATER state (ly, S, Hp, W, mem, md, k) - any state the call's journal from the entry admits, e.g. the state a
   callee's post returns - the position's journal (vrd_ijrn's first conjunct; THE KIT'S CUT: at any budget WS, implicit),
   its blocks (vrd_ijrn's rd_blocks_move), its ledger (vrd_icur's prh_ledger) and its ledger list (vrd_imodel's
   rd_ledger_move: Permutation Lam (D ++ ie_Lam E)). Every conclusion is about the view of that later state,
   (w_H W, mem). ==== *)
Lemma vrd_icur_after_call {R : world SEGS -> world SEGS -> Prop} {WS : list (list Z)} :
  forall CTX CTX0 CW E ly S Hp W mem md k D tr Lam peak cnt fail ran
    most own,
  vrd_ient_ok B ARx CTX CTX0 CW E ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx R (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) [] ly S Hp W mem md k WS ->
  rd_blocks_move B (ie_ly E) (ie_S E) ly S D tr (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ie_d E) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> Permutation Lam (D ++ ie_Lam E) ->
  src_rd W mem (ie_text E) (ie_tb E) /\ prhReader_home B ly S Hp Lam (ie_text E) (ie_len E) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (ie_q E) 24.
Proof.
  intros CTX CTX0 CW E ly S Hp W mem md k D tr Lam peak cnt fail ran most own HEN HJ HBM HL1 HLp.
  destruct HEN as ((HAFN & _) & _ & _ & _ & HRD & _).
  pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
  pose proof HRD as (_ & _ & _ & _ & Hinok & Hfwin & Hqlo & Hqhi & _ & Hsrc & Hhome & _ & Hnode & Hqv & Htv & _ & HLED0
    & _).
  pose proof Hfwin as (He0 & _ & Hetop & _).
  pose proof Hinok as (_ & _ & _ & _ & _ & Ht0 & Htl & Htp & Hlen & _).
  pose proof Hsrc as (_ & H4096 & Hsceil & _).
  pose proof Hnode as (Hv4096 & _).
  pose proof HJ as (HAR & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (HSTKp : 0 <= STK_parse_items (ie_d E)).
  { unfold STK_parse_items. pose proof (pi_frame_nonneg F_parse_items). pose proof (pi_frame_nonneg F_parse_value).
    assert (0 <= LEAF_pv_pi) by (unfold LEAF_pv_pi, zmaxl; cbn [fold_right]; lia).
    assert (0 <= Z.of_nat (PjGrammar.MAXD - ie_d E) * (pi_frame F_parse_value + pi_frame F_parse_items))
      by (apply Z.mul_nonneg_nonneg; lia). lia. }
  assert (Hsink : ~ YI16.sink_open_fp (rd_fp (ie_q E) (ie_v E))).
  { apply sink_closed_pos. unfold rd_fp. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
  rewrite <- Hlen in Hhome |- *.
  assert (HnFP : forall a, ie_text E <= a < ie_text E + Z.of_nat (length (ie_tb E)) ->
                   ~ inFP (rd_fp (ie_q E) (ie_v E)) a).
  { intros a Ha (r & Hin & Hr). cbn [rd_fp In] in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia. }
  assert (Hn0 : 0 <= Z.of_nat (length (ie_tb E))) by lia.
  split; [|split].
  - exact (vrd_src_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hsink HnFP Hsrc Hhome
             HLED0 HBM HL1 HLp).
  - exact (vrd_home_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hn0 Hhome HLED0 HAR HBM HL1 HLp).
  - apply (vrd_stack_ra _ _ _ _ _ _ _ _ HAR); lia.
Qed.

Lemma vrd_node_ra_after_call {R : world SEGS -> world SEGS -> Prop} {WS : list (list Z)} :
  forall CTX CTX0 CW E ly S Hp W mem md k D tr Lam peak cnt fail
    ran most own,
  vrd_ient_ok B ARx CTX CTX0 CW E ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx R (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) [] ly S Hp W mem md k WS ->
  rd_blocks_move B (ie_ly E) (ie_S E) ly S D tr (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ie_d E) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> Permutation Lam (D ++ ie_Lam E) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (ie_v E) 56.
Proof.
  intros CTX CTX0 CW E ly S Hp W mem md k D tr Lam peak cnt fail ran most own HEN HJ HBM HL1 HLp.
  pose proof (vrd_node_app CTX CTX0 CW E HEN) as Happ.
  pose proof (vrd_node_low B ARx HL LAWS CTX CTX0 CW E HEN) as Hvlow.
  destruct HEN as ((HAFN & _) & _ & _ & _ & HRD & _).
  pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & Hqlo & _ & _ & _ & _ & _ & Hnode & _ & _ & Hvwin & HLED0 & _).
  pose proof Hnode as (_ & _ & _ & _ & Hvat & _ & _ & HvRA).
  assert (HSTKp : 0 <= STK_parse_items (ie_d E)).
  { unfold STK_parse_items. pose proof (pi_frame_nonneg F_parse_items). pose proof (pi_frame_nonneg F_parse_value).
    assert (0 <= LEAF_pv_pi) by (unfold LEAF_pv_pi, zmaxl; cbn [fold_right]; lia).
    assert (0 <= Z.of_nat (PjGrammar.MAXD - ie_d E) * (pi_frame F_parse_value + pi_frame F_parse_items))
      by (apply Z.mul_nonneg_nonneg; lia). lia. }
  assert (HnFP : forall x, ie_v E <= x < ie_v E + 56 -> ~ inFP (rd_fp (ie_q E) (ie_v E)) (shadow_addr x)).
  2: exact (vrd_node_ra_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HJ Hvat Hvwin
              HvRA HnFP HLED0 HBM HL1 HLp).
  intros x Hx (r & Hin & Hr). cbn [rd_fp In] in Hin. pose proof asan_consts as (C1 & _).
  assert (Hsx : shadow_addr x < alloc_ceiling).
  { unfold shadow_addr, SHADOW_OFF. assert (x / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
    assert (alloc_ceiling / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; try lia.
  apply (vrd_hull_out (ie_v E) 56 x 1 (shadow_addr x) Happ Hvlow ltac:(lia) ltac:(lia) ltac:(lia)); [|exact Hr].
  replace (x + 1 - 1) with x by lia.
  pose proof (Z.div_mod (shadow_addr x) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia)). lia.
Qed.



(* ---- 3. the capacity step, slots 6212..6215 and 6241 (rows 280..283, 309) ---- *)

(* a register of a post-CALL symbolic state (the runner's call stop gives st_ok, not st_ok_pi) *)
Ltac vi_regc HS r Hr :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg _ _ _ _ _ r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [sv_denot] in Hr; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hr end.

(* the return slot of row 281's `jal grow` *)
Definition A_IGROWRET_SLOT : nat := 6214%nat.

(* a callee-saved register across a call *)
Lemma vi_kept : forall (regs regs' : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof.
  intros regs regs' r H Hc. pose proof (H _ Hc) as HH. rewrite !Z_to_bv_bv_unsigned in HH. exact HH.
Qed.

(* the bytes of a present range, as the list grow's text names (kb / yb) *)
Definition vi_bytes (W : world SEGS) (mem : word -> option byte) (a n : Z) : list Z :=
  map (fun j => match mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat j) with
                | Some b => bv_unsigned b | None => 0 end) (seq 0 (Z.to_nat n)).

Lemma vi_le_byte1 : forall z, 0 <= z < 256 -> le_byte z 1 0 = z.
Proof.
  intros z Hz. unfold le_byte. rewrite Z.shiftr_0_r. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma vi_bytes_ok : forall W mem a n, 0 <= n ->
  (forall x, a <= x < a + n -> apresent (w_H W) mem x) ->
  bytes_at W mem a (vi_bytes W mem a n) /\ Z.of_nat (length (vi_bytes W mem a n)) = n.
Proof.
  intros W mem a n Hn HP. unfold vi_bytes. rewrite length_map, length_seq. split; [|lia].
  intros j Hj. rewrite length_map, length_seq in Hj.
  set (f := fun j0 : nat => match mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat j0) with
                            | Some b => bv_unsigned b | None => 0 end).
  assert (Hnth : nth j (map f (seq 0 (Z.to_nat n))) 0 = f j).
  { rewrite (nth_indep _ 0 (f 0%nat)) by (rewrite length_map, length_seq; exact Hj).
    rewrite map_nth, seq_nth by exact Hj. reflexivity. }
  rewrite Hnth.
  destruct (HP (a + Z.of_nat j) ltac:(lia)) as (Hh & b & Hb).
  assert (Hm : mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat j) = Some b)
    by (unfold mbyte, mrestrict; rewrite Hh, Hb; reflexivity).
  unfold f. rewrite Hm. pose proof (bv_unsigned_in_range 8 b) as Hr.
  change (bv_modulus 8) with 256 in Hr.
  split; [|lia].
  intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r, Hm.
  f_equal. rewrite vi_le_byte1 by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* the granted grow at n = cap > 0, as events *)
Lemma vi_gtrace_eq : forall (o : bool) (c : nat), (0 < c)%nat ->
  prhPg_gtrace o (Z.of_nat c) (Z.of_nat c) =
    PjGrammar.EGrow (56 * c) (56 * (2 * c)) :: (if o then [PjGrammar.EGrow (8 * c) (8 * (2 * c))] else []).
Proof.
  intros o c Hc. unfold prhPg_gtrace. rewrite !Nat2Z.id. unfold PjGrammar.grow.
  rewrite (proj2 (Nat.ltb_ge c c) (Nat.le_refl _)).
  replace (Nat.eqb c 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  unfold PjGrammar.jbind, PjGrammar.jrealloc, PjGrammar.take, PjGrammar.jret.
  destruct o; reflexivity.
Qed.

(* the symbolic state after the call: parse_items' frame again, a0 the callee's constant result *)
Definition vi_ss_a0 (k : nat) (c : Z) : sstate :=
  mkSS (4 * Z.of_nat k) (sr_set sr_atoms (Z_to_bv 5 10) (SLit c)) vi_epi_regions None vi_epi_facts.

Lemma vi_st_ok_a0 : forall (k : nat) (fxP : YK11.FPState) (W : world SEGS) regs0 regs mem c,
  spZ regs = spZ regs0 - 144 -> 0 <= spZ regs0 - 144 -> spZ regs0 <= 2 ^ 64 ->
  vi_saved W mem regs0 -> getr regs (Z_to_bv 5 10) = Z_to_bv 64 c ->
  st_ok_pi (fx := fxP) SEGS VAL (vi_EI regs regs0) (vi_ss_a0 k c)
    (restrict (w_H W) (@YK11.mkst fxP regs (w64 (A_IPC k)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS vi_Bx vi_SH (vi_EI regs regs0) (mrestrict (w_H W) mem).
Proof.
  intros k fxP W regs0 regs mem c Hsp Hlo Hhi HV Ha0.
  assert (Usp : bv_unsigned (ew (vi_EI regs regs0) 2) = spZ regs0 - 144)
    by (rewrite (vi_ew_low regs regs0 2 2%bv eq_refl); exact Hsp).
  split; [|unfold sh_ok, vi_SH; apply Forall_nil].
  rewrite (restrict_mkst_fx (fx := fxP)).
  change (w64 (A_IPC k)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat k)).
  unfold vi_ss_a0. apply (pa_entry_st_ok_full (fx := fxP)).
  - apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | |cbn [sv_denot]; exact Ha0].
    intros H0. apply (f_equal (@bv_unsigned 5)) in H0. vm_compute in H0. discriminate H0.
  - vm_compute. reflexivity.
  - unfold vi_epi_regions. apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, vi_frame_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split.
    + intros o Ho. lia.
    + unfold vi_frame_chunks.
      repeat apply Forall_cons; try apply Forall_nil.
      * exact (vi_frame_chunk regs regs0 W mem 0 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 1 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 2 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 3 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 4 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 5 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 6 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 7 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 8 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 9 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 10 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 11 ltac:(lia) HV).
      * exact (vi_frame_chunk regs regs0 W mem 12 ltac:(lia) HV).
  - cbn [vi_epi_regions pairwise_disjoint all_disjoint]. exact (conj I I).
  - exact (conj I (conj I I)).
Qed.

(* grow's footprint at the loop's call, as its text names it *)
Definition vi_gFP (E : vrd_ient) (P : vrd_ipos) : list (Z * Z) :=
  [(ie_v E + 24, ie_v E + 40); (ie_v E + 48, ie_v E + 56)] ++
  ablocks_fp (prhReader_ab (kids_blkR (ip_kids P) (ip_cap P) ++
                            keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P))).

(* grow's post body at the loop's call: the INNER Q of grow's text, the text's own named body PRH_FnReader.tgrP_Q
   (tgrP_Q_check: the text concludes fpostWmR .. at tgrP_Q) at the call's data (the memnorm wrapper fQmn is dropped by
   proj1). The POST-IMPLICATION form: no entry position; each arm carries its own live-request move and position
   transfer, each REFUSED arm its OUTCOME exclusion and #102's refusal ledger, the kids-refused arm also the
   injected-reading exclusion *)
Definition vi_gpost (E : vrd_ient) (P : vrd_ipos) (ly' : alayout) (S' : astate) (Hp' : list Z)
  (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  tgrP_Q (L := A_prog_listing) (PA := PAI) B (ie_most E) (ie_own E) (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P)
    (ie_v E) (if ie_o E then 6 else 5) 0 0 (ip_kids P) (ip_keys P) (ip_n P) (ip_cap P)
    (vi_bytes (ip_W P) (ip_mem P) (ip_kids P) (56 * ip_cap P)) (vi_bytes (ip_W P) (ip_mem P) (ip_keys P) (8 * ip_cap P))
    (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) ly' S' Hp' W' regs' mem' md'.

Variable CTX0 : list (list Z).
Variable CW : list (list Z).
(* grow's PUBLISHED text (the kit's cut, lib/A/PRH_FnReader.v blob f1ae32e3b2cd: no DW, the per-event live room), at every
   float state (the loop's positions carry theirs, ip_fx) *)
Hypothesis H_grow : forall fxg : YK11.FPState, tgrow_specX (fx := fxg) B ARx SK CTX0.
(* the image numbers (prh_img_A, by computation): parse_items' frame is 144 bytes, grow keeps s0 = v + 48 and
   parse_items keeps s0 = q *)
Hypothesis H_img : pi_frame F_parse_items = 144.
Hypothesis H_s0g : pi_s0cur F_grow = Some 48.
Hypothesis H_s0p : pi_s0cur F_parse_items = Some 0.

Lemma vi_stk_grow : 0 <= STK_grow.
Proof.
  unfold STK_grow, STK_fuzz_realloc, zmaxl. cbn [fold_right].
  pose proof (pi_frame_nonneg F_grow). pose proof (pi_frame_nonneg F_fuzz_realloc). lia.
Qed.

Lemma vi_stk_ge : forall d, 144 + STK_grow <= STK_parse_items d.
Proof.
  intros d. unfold STK_parse_items. rewrite H_img.
  pose proof vi_stk_grow. pose proof (pi_frame_nonneg F_parse_value).
  assert (STK_grow <= LEAF_pv_pi) by (unfold LEAF_pv_pi, zmaxl; cbn [fold_right]; lia).
  assert (0 <= Z.of_nat (PjGrammar.MAXD - d) * (pi_frame F_parse_value + 144))
    by (apply Z.mul_nonneg_nonneg; lia).
  lia.
Qed.

(* ---- the model's traces and the ledger across one grow (pure facts) ---- *)

Lemma vi_hpeak_pos : forall t, hpeakR t <= Z.of_nat (PjGrammar.pos t).
Proof.
  induction t as [|e t IH]; cbn [hpeakR PjGrammar.pos]; [lia|].
  destruct e; cbn [PjGrammar.held_ev PjGrammar.pos_ev]; lia.
Qed.

Lemma vi_held_hpeak : forall t, PjGrammar.held t <= hpeakR t.
Proof. induction t as [|e t IH]; cbn [hpeakR PjGrammar.held]; lia. Qed.

Lemma vi_nlive_app : forall a b, nliveR (a ++ b) = nliveR a + nliveR b.
Proof. induction a as [|e a IH]; intros b; cbn [app nliveR]; [reflexivity | rewrite IH; lia]. Qed.

Lemma vi_lsz_app : forall a b, lszR (a ++ b) = fold_left lsz_evR b (lszR a).
Proof. intros a b. unfold lszR. apply fold_left_app. Qed.

Lemma vi_rm1n_perm : forall k s, In k s -> Permutation s (k :: rm1nR k s).
Proof.
  intros k s. induction s as [|x s IH]; intros Hin; [destruct Hin|]. cbn [rm1nR].
  destruct (Nat.eqb_spec x k) as [-> | Hne]; [apply Permutation_refl|].
  destruct Hin as [-> | Hin]; [exfalso; exact (Hne eq_refl)|].
  eapply Permutation_trans; [apply perm_skip; exact (IH Hin)|]. apply perm_swap.
Qed.

(* removing a size the list holds, as a permutation *)
Lemma vi_rm1n_of : forall k s s', Permutation s (k :: s') -> Permutation (rm1nR k s) s'.
Proof.
  intros k s s' Hp. assert (Hin : In k s) by (apply (Permutation_in _ (Permutation_sym Hp)); left; reflexivity).
  pose proof (vi_rm1n_perm k s Hin) as H2. apply (Permutation_cons_inv (a := k)).
  eapply Permutation_trans; [apply Permutation_sym; exact H2 | exact Hp].
Qed.

Lemma vi_skipn_nth : forall (l : list Z) k c, nth_error l k = Some c -> skipn k l = c :: skipn (S k) l.
Proof.
  induction l as [|x l IH]; intros k c H; [destruct k; discriminate|].
  destruct k as [|k]; cbn [nth_error skipn] in *; [injection H as ->; reflexivity | exact (IH k c H)].
Qed.

(* a prefix of the trace of jr_items over a text that starts with a byte: its calls and its peak are bounded by the text
   (PjGrammar.vspec_jr_items) *)
Lemma vi_trace_bounds : forall d o b y okl r tr t ok2,
  PjGrammar.jr_items prh_jr_strtod d o (b :: y) okl = (r, tr ++ t, ok2) ->
  (PjGrammar.calls tr <= 2 * length (b :: y))%nat /\
  hpeakR tr <= 224 * Z.of_nat (length (b :: y)) + 512 * Z.of_nat (PjGrammar.MAXD - d).
Proof.
  intros d o b y okl r tr t ok2 H.
  pose proof (PjGrammar.vspec_jr_items prh_jr_strtod d o b y okl) as (H1 & H2 & _).
  rewrite H in H1, H2. cbn [fst snd] in H1, H2. rewrite PjGrammar.calls_app in H1. rewrite PjGrammar.pos_app in H2.
  pose proof (vi_hpeak_pos tr). split; lia.
Qed.

(* the ledger move of the whole call so far, composed with one more step (grow's), when the steps so far granted
   every call: ok is all true, so fail and ran are the entry's. #102's refusal rule (A'Ledger, kit PRH_FnParse.v blob
   94232293d483): the step states its oks over its own requests (prh_ev_reqs trg) against most, and its peak with
   the refusal peak over ITS all-granted trace gtg; the call's all-granted trace G is the trace so far, then gtg, then
   the rest, and the step makes at most gtg's calls (the two LAST premises) *)
Lemma vi_lm_comp : forall Lam0 peak0 cnt0 fail0 ran0 most G tr D Lam peak cnt fail ran
    okg gtg trg rest D' Lam' peak' cnt' fail' ran',
  rd_ledger_move Lam0 peak0 cnt0 fail0 ran0 most (repeat true (PjGrammar.calls tr)) G tr D Lam peak cnt fail ran ->
  Ledger.lsum D = PjGrammar.held tr ->
  cnt0 + Z.of_nat (PjGrammar.calls tr + PjGrammar.calls trg) < 2 ^ 64 - 1 -> 0 <= cnt0 ->
  length okg = PjGrammar.calls trg ->
  prh_oks okg cnt fail (PjGrammar.calls trg) (prh_ev_reqs trg) most ran ran' ->
  cnt' = cnt + Z.of_nat (PjGrammar.calls trg) -> fail_afterR cnt fail (PjGrammar.calls trg) fail' ->
  Permutation Lam' (D' ++ Lam0) ->
  Permutation (map snd D') (map Z.of_nat (fold_left lsz_evR trg (lszR tr))) ->
  Z.of_nat (length D') = nliveR tr + nliveR trg ->
  peak' = Z.max (Z.max peak (Ledger.lsum Lam + hpeakR trg))
            (prh_refused_peak okg cnt fail (PjGrammar.calls trg) (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds gtg))) ->
  G = tr ++ gtg ++ rest -> (PjGrammar.calls trg <= PjGrammar.calls gtg)%nat ->
  rd_ledger_move Lam0 peak0 cnt0 fail0 ran0 most (repeat true (PjGrammar.calls tr) ++ okg) G (tr ++ trg) D' Lam'
    peak' cnt' fail' ran'.
Proof.
  intros Lam0 peak0 cnt0 fail0 ran0 most G tr D Lam peak cnt fail ran okg gtg trg rest D' Lam' peak' cnt' fail' ran'
    (Hok & Hcnt & Hfa & HLp & Hsz & Hnl & Hpk) HlsD Hbd Hc0 Hlen Hok2 Hcnt' Hfa' HLp' Hsz' Hnl' Hpk' HG Hkg.
  assert (HRP : prh_refused_peak (repeat true (PjGrammar.calls tr) ++ okg) cnt0 fail0
                  (PjGrammar.calls tr + PjGrammar.calls trg) (map (Z.add (Ledger.lsum Lam0)) (prh_ev_helds G)) =
                prh_refused_peak okg (cnt0 + Z.of_nat (PjGrammar.calls tr)) fail0 (PjGrammar.calls trg)
                  (map (Z.add (Ledger.lsum Lam0 + PjGrammar.held tr)) (prh_ev_helds gtg)))
    by (rewrite HG; apply vl_refused_peak_gsplit; exact Hkg).
  assert (RP1 : prh_refused_peak (repeat true (PjGrammar.calls tr)) cnt0 fail0 (PjGrammar.calls tr)
                  (map (Z.add (Ledger.lsum Lam0)) (prh_ev_helds G)) = 0).
  { apply prh_refused_peak_granted. intros i Hi Hf. rewrite nth_repeat_lt in Hf by exact Hi. discriminate. }
  pose proof (vl_ev_reqs_length tr) as Hrl.
  set (k1 := PjGrammar.calls tr) in *. set (k2 := PjGrammar.calls trg) in *.
  destruct Hok as (O1 & O2 & O3).
  assert (Hno : forall i, (i < k1)%nat -> cnt0 + Z.of_nat i <> fail0).
  { intros i Hi He. pose proof (O1 i Hi He) as Hf. rewrite nth_repeat_lt in Hf by exact Hi. discriminate. }
  assert (Eran : ran = ran0).
  { destruct O2 as [-> | (_ & i & Hi & Hf & _)]; [reflexivity|].
    unfold prh_refused in Hf. rewrite nth_repeat_lt in Hf by exact Hi. discriminate. }
  assert (Ecnt : cnt = cnt0 + Z.of_nat k1) by (rewrite Hcnt; apply Z.mod_small; lia).
  assert (Efail : fail = fail0).
  { destruct Hfa as [_ Hf2]. apply Hf2. intros (Hlo & Hhi).
    apply (Hno (Z.to_nat (fail0 - cnt0))); [lia | lia]. }
  subst ran fail cnt. rewrite Ecnt in *.
  assert (Hnth : forall i, nth i (repeat true k1 ++ okg) true = if Nat.ltb i k1 then true else nth (i - k1) okg true).
  { intros i. destruct (Nat.ltb_spec i k1) as [Hi | Hi].
    - rewrite app_nth1 by (rewrite repeat_length; exact Hi). apply nth_repeat_lt. exact Hi.
    - rewrite app_nth2 by (rewrite repeat_length; exact Hi). rewrite repeat_length. reflexivity. }
  destruct Hok2 as (P1 & P2 & P3).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - rewrite PjGrammar.calls_app, vl_ev_reqs_app. fold k1 k2. split; [|split].
    + intros i Hi He. rewrite Hnth. destruct (Nat.ltb_spec i k1) as [Hi1 | Hi1]; [exfalso; exact (Hno i Hi1 He)|].
      apply P1; [lia|]. rewrite Nat2Z.inj_sub by exact Hi1. lia.
    + destruct P2 as [-> | (Hr & j & Hj & Hf & Hm)]; [left; reflexivity|].
      right. split; [exact Hr|]. exists (k1 + j)%nat. split; [lia|]. split.
      * rewrite vl_refused_app. exact Hf.
      * rewrite app_nth2 by lia. replace (k1 + j - length (prh_ev_reqs tr))%nat with j by lia. exact Hm.
    + intros i Hi Hf Hm. destruct (Nat.lt_ge_cases i k1) as [Hi1 | Hi1].
      * rewrite (vl_refused_rep k1 okg cnt0 fail0 i Hi1) in Hf. discriminate Hf.
      * replace i with (k1 + (i - k1))%nat in Hf, Hm by lia. rewrite vl_refused_app in Hf.
        rewrite app_nth2 in Hm by lia.
        replace (k1 + (i - k1) - length (prh_ev_reqs tr))%nat with (i - k1)%nat in Hm by lia.
        apply (P3 (i - k1)%nat); [lia | exact Hf | exact Hm].
  - rewrite Hcnt', PjGrammar.calls_app, Nat2Z.inj_add. fold k1 k2. rewrite Z.add_assoc. symmetry. apply Z.mod_small. lia.
  - rewrite PjGrammar.calls_app. fold k1 k2. destruct Hfa' as (F1 & F2). split.
    + intros Hin. apply F1. split; [|lia].
      destruct (Z_lt_le_dec fail0 (cnt0 + Z.of_nat k1)) as [Hlt | Hge]; [|exact Hge].
      exfalso. apply (Hno (Z.to_nat (fail0 - cnt0))); lia.
    + intros Hnin. apply F2. intros Hin. apply Hnin. lia.
  - exact HLp'.
  - rewrite vi_lsz_app. exact Hsz'.
  - rewrite vi_nlive_app. exact Hnl'.
  - rewrite PjGrammar.calls_app. fold k1 k2.
    assert (HLs : Ledger.lsum Lam = Ledger.lsum Lam0 + PjGrammar.held tr)
      by (rewrite (vi_lsum_perm _ _ HLp), vi_lsum_app; lia).
    rewrite Hpk', vi_hpeak_app, Hpk, RP1, HRP, HLs.
    pose proof (vi_hpeak_nonneg tr). pose proof (vi_hpeak_nonneg trg).
    pose proof (vl_refused_peak_nonneg okg (cnt0 + Z.of_nat k1) fail0 k2
      (map (Z.add (Ledger.lsum Lam0 + PjGrammar.held tr)) (prh_ev_helds gtg))).
    lia.
Qed.

(* all granted: the oks of a run of granted calls *)
Lemma vi_oks_true : forall k cnt fail ns most ran, (forall i, (i < k)%nat -> cnt + Z.of_nat i <> fail) ->
  prh_oks (repeat true k) cnt fail k ns most ran ran.
Proof.
  intros k cnt fail ns most ran H. split; [|split].
  - intros i Hi He. exfalso. exact (H i Hi He).
  - left. reflexivity.
  - intros i Hi Hf. unfold prh_refused in Hf. rewrite nth_repeat_lt in Hf by exact Hi. discriminate.
Qed.

Lemma vi_fa_none : forall cnt fail k, (forall i, (i < k)%nat -> cnt + Z.of_nat i <> fail) -> fail_afterR cnt fail k fail.
Proof.
  intros cnt fail k H. split; [|intros _; reflexivity].
  intros (Hlo & Hhi). exfalso. apply (H (Z.to_nat (fail - cnt))); lia.
Qed.

(* a sizes list without one granted size, as a permutation of the Z sizes *)
Lemma vi_rm1n_Z : forall k s l, Permutation (map Z.of_nat s) (Z.of_nat k :: l) ->
  Permutation (map Z.of_nat (rm1nR k s)) l.
Proof.
  intros k s l Hp.
  assert (Hin : In k s).
  { assert (H1 : In (Z.of_nat k) (map Z.of_nat s)) by (apply (Permutation_in _ (Permutation_sym Hp)); left; reflexivity).
    apply in_map_iff in H1 as (k' & Hk & Hin). apply Nat2Z.inj in Hk. subst k'. exact Hin. }
  pose proof (Permutation_map Z.of_nat (vi_rm1n_perm k s Hin)) as H2. cbn [map] in H2.
  apply (Permutation_cons_inv (a := Z.of_nat k)).
  eapply Permutation_trans; [apply Permutation_sym; exact H2 | exact Hp].
Qed.

(* a block that occurs once in a list whose zones are pairwise apart, if its own zone is not apart from itself *)
Lemma vi_pw_once : forall (l : list (Z * Z)) x, pairwise zdisjoint l -> ~ zdisjoint x x -> In x l ->
  exists l', Permutation l (x :: l') /\ ~ In x l'.
Proof.
  induction l as [|y t IH]; intros x Hpw Hxx Hin; [destruct Hin|].
  destruct Hpw as (Hy & Ht). destruct (decide (y = x)) as [-> | Hne].
  - exists t. split; [apply Permutation_refl|]. intros Hin'.
    exact (Hxx (proj1 (Forall_forall _ _) Hy x Hin')).
  - destruct Hin as [-> | Hin]; [exfalso; exact (Hne eq_refl)|].
    destruct (IH x Ht Hxx Hin) as (l' & Hp & Hn). exists (y :: l'). split.
    + eapply Permutation_trans; [apply perm_skip; exact Hp | apply perm_swap].
    + intros [-> | Hin']; [exact (Hne eq_refl) | exact (Hn Hin')].
Qed.

(* a block cannot sit in both parts of a block list the allocator keeps apart *)
Lemma vi_dup_absurd : forall (l A Bl : list (Z * Z)) x,
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> Permutation l (A ++ Bl) ->
  In x A -> In x Bl -> 0 < req_size (snd x) -> False.
Proof.
  intros l A Bl x Hpw Hp HA HB Hpos.
  set (g := fun b : Z * Z => (fst b, req_size (snd b))) in *.
  assert (Hxx : ~ zdisjoint (g x) (g x)) by (unfold zdisjoint, g; cbn [fst snd]; lia).
  assert (Hin : In (g x) (map g l))
    by (apply in_map; apply (Permutation_in _ (Permutation_sym Hp)); apply in_or_app; left; exact HA).
  destruct (vi_pw_once (map g l) (g x) Hpw Hxx Hin) as (l' & Hp' & Hn).
  apply in_split in HA as (A1 & A2 & ->).
  assert (H2 : Permutation (g x :: l') (g x :: (map g A1 ++ map g A2 ++ map g Bl))).
  { eapply Permutation_trans; [apply Permutation_sym; exact Hp'|].
    eapply Permutation_trans; [apply Permutation_map; exact Hp|].
    rewrite !map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
    apply Permutation_sym. apply Permutation_middle. }
  apply Permutation_cons_inv in H2. apply Hn. apply (Permutation_in _ (Permutation_sym H2)).
  apply in_or_app. right. apply in_or_app. right. apply in_map. exact HB.
Qed.

(* grow at n = cap > 0, on the oracles of its arms *)
Lemma vi_grow_ok : forall (o : bool) c okt, (0 < c)%nat ->
  PjGrammar.grow o c c ((if o then [true; true] else [true]) ++ okt) =
    (Some (2 * c)%nat, prhPg_gtrace o (Z.of_nat c) (Z.of_nat c), okt).
Proof.
  intros o c okt Hc. rewrite vi_gtrace_eq by exact Hc. unfold PjGrammar.grow.
  rewrite (proj2 (Nat.ltb_ge c c) (Nat.le_refl _)).
  replace (Nat.eqb c 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  unfold PjGrammar.jbind, PjGrammar.jrealloc, PjGrammar.take, PjGrammar.jret. destruct o; reflexivity.
Qed.

Lemma vi_grow_no1 : forall (o : bool) c okt, (0 < c)%nat ->
  PjGrammar.grow o c c (false :: okt) = (None, [PjGrammar.EFail (56 * (2 * c))], okt).
Proof.
  intros o c okt Hc. unfold PjGrammar.grow.
  rewrite (proj2 (Nat.ltb_ge c c) (Nat.le_refl _)).
  replace (Nat.eqb c 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  unfold PjGrammar.jbind, PjGrammar.jrealloc, PjGrammar.take. reflexivity.
Qed.

Lemma vi_grow_no2 : forall c okt, (0 < c)%nat ->
  PjGrammar.grow true c c (true :: false :: okt) =
    (None, [PjGrammar.EGrow (56 * c) (56 * (2 * c)); PjGrammar.EFail (8 * (2 * c))], okt).
Proof.
  intros c okt Hc. unfold PjGrammar.grow.
  rewrite (proj2 (Nat.ltb_ge c c) (Nat.le_refl _)).
  replace (Nat.eqb c 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  unfold PjGrammar.jbind, PjGrammar.jrealloc, PjGrammar.take. reflexivity.
Qed.

(* the ledger list after a swap of some of the position's blocks *)
Lemma vi_swap_lam : forall (Lam Lam' D Dold Dnew Di' Lam0 Lam1 : list (Z * Z)),
  Permutation Lam (D ++ Lam0) -> Permutation D (Dold ++ Di') ->
  Permutation Lam (Dold ++ Lam1) -> Permutation Lam' (Dnew ++ Lam1) ->
  Permutation Lam' ((Dnew ++ Di') ++ Lam0) /\ Permutation Lam1 (Di' ++ Lam0).
Proof.
  intros Lam Lam' D Dold Dnew Di' Lam0 Lam1 H1 H2 H3 H4.
  assert (H5 : Permutation Lam1 (Di' ++ Lam0)).
  { apply (Permutation_app_inv_l Dold). eapply Permutation_trans; [apply Permutation_sym; exact H3|].
    eapply Permutation_trans; [exact H1|]. rewrite app_assoc. apply Permutation_app_tail. exact H2. }
  split; [|exact H5].
  eapply Permutation_trans; [exact H4|]. rewrite <- app_assoc. apply Permutation_app_head. exact H5.
Qed.

(* THE GROW STEP'S LEDGER SHAPE (a Theorem Labs lane's ruling: one copy, for every grow call of the unit - parse_items' loop
   step, its prologue's first grow and image B's lanes). The call so far granted every allocator call (ok all true);
   grow then replaced the position's blocks Dold by Dnew (fuzz_realloc's swap, prhReader_swap's ledger-list part; at
   cap = 0 Dold = [] and EGrow 0 n is a fresh block; on a refusal of the first realloc Dold = Dnew = []) with the
   trace trg on the oracle okg. The step's own facts: its oks, counter and fail_after (grow's post), what trg does to
   the live sizes (HSZ: for EGrow m n with m > 0, vi_rm1n_Z), the live count and the peak; the result is the whole
   call's ledger move and the lsum fact vrd_imodel / vrd_iexit_a carry. #102's refusal rule (A'Ledger): the oks take
   the step's requests and most, the peak the refusal peak over the step's all-granted trace gtg, and the call's
   all-granted trace G is the trace so far, then gtg, then the rest (the two LAST premises, as vi_lm_comp's) *)
Lemma vi_grow_swap_step : forall Lam0 peak0 cnt0 fail0 ran0 most G tr D Lam peak cnt fail ran
    Dold Dnew Di Lam1 Lam' okg gtg trg rest peak' cnt' fail' ran',
  rd_ledger_move Lam0 peak0 cnt0 fail0 ran0 most (repeat true (PjGrammar.calls tr)) G tr D Lam peak cnt fail ran ->
  Ledger.lsum D = PjGrammar.held tr ->
  Permutation D (Dold ++ Di) -> Permutation Lam (Dold ++ Lam1) -> Permutation Lam' (Dnew ++ Lam1) ->
  0 <= cnt0 -> cnt0 + Z.of_nat (PjGrammar.calls tr + PjGrammar.calls trg) < 2 ^ 64 - 1 ->
  length okg = PjGrammar.calls trg ->
  prh_oks okg cnt fail (PjGrammar.calls trg) (prh_ev_reqs trg) most ran ran' ->
  cnt' = cnt + Z.of_nat (PjGrammar.calls trg) -> fail_afterR cnt fail (PjGrammar.calls trg) fail' ->
  (forall (s : list nat) (L : list Z), Permutation (map Z.of_nat s) (map snd Dold ++ L) ->
     Permutation (map Z.of_nat (fold_left lsz_evR trg s)) (map snd Dnew ++ L)) ->
  Z.of_nat (length Dnew) = Z.of_nat (length Dold) + nliveR trg ->
  Ledger.lsum Dnew = Ledger.lsum Dold + PjGrammar.held trg ->
  peak' = Z.max (Z.max peak (Ledger.lsum Lam + hpeakR trg))
            (prh_refused_peak okg cnt fail (PjGrammar.calls trg) (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds gtg))) ->
  G = tr ++ gtg ++ rest -> (PjGrammar.calls trg <= PjGrammar.calls gtg)%nat ->
  rd_ledger_move Lam0 peak0 cnt0 fail0 ran0 most (repeat true (PjGrammar.calls tr) ++ okg) G (tr ++ trg) (Dnew ++ Di)
    Lam' peak' cnt' fail' ran' /\
  Ledger.lsum (Dnew ++ Di) = PjGrammar.held (tr ++ trg).
Proof.
  intros Lam0 peak0 cnt0 fail0 ran0 most G tr D Lam peak cnt fail ran Dold Dnew Di Lam1 Lam' okg gtg trg rest peak'
    cnt' fail' ran' HLM HlsD HDp HL1a HL1b Hc0 Hbd Hlen Hoks Hcnt' Hfa' HSZ Hnl Hls Hpk' HG Hkg.
  pose proof HLM as (_ & _ & _ & HLp & Hsz & HnD & _).
  destruct (vi_swap_lam _ _ _ _ Dnew Di Lam0 Lam1 HLp HDp HL1a HL1b) as (HLp' & _).
  split.
  - apply (vi_lm_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ okg gtg trg rest (Dnew ++ Di) Lam' peak' cnt' fail' ran' HLM HlsD
             Hbd Hc0 Hlen Hoks Hcnt' Hfa' HLp').
    + rewrite map_app. apply Permutation_sym. apply HSZ.
      eapply Permutation_trans; [apply Permutation_sym; exact Hsz|].
      rewrite <- map_app. apply Permutation_map. exact HDp.
    + rewrite length_app, Nat2Z.inj_add, Hnl, <- HnD, (Permutation_length HDp), length_app, Nat2Z.inj_add. lia.
    + exact Hpk'.
    + exact HG.
    + exact Hkg.
  - rewrite vi_lsum_app, vi_held_app, Hls, <- HlsD, (vi_lsum_perm _ _ HDp), vi_lsum_app. lia.
Qed.

(* ---- the two runs after grow returns (slot 6214). a0 = 0 takes row 282's `beqz` back to the loop head (slot 6040);
   a0 = -1 falls to row 283's `j`, row 309's `addi s2, zero, -1`, and stops at the exit (slot 6242). Nothing is
   written; the registers the boundaries read are kept (s2 := -1 on the exit). ---- *)
Definition vi_kregs : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition vi_xregs : list Z := [2; 3; 4].

Ltac vi_kreg HS :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?n) = getr ?regs2 (Z_to_bv 5 ?n) =>
    let Hr := fresh "Hr" in vi_reg HS (Z_to_bv 5 n) Hr; rewrite Hr; apply vi_ew_low; reflexivity end.

(* THE KIT'S CUT: the entry journal at a budget WS (implicit); the run is stated at the empty budget, so it runs from the
   journal rebased to the state's depot and comes back with unbase0 (YCbqGwild, the recipe's step 2).
   THE RE-HIDING MOVE: the journal from the entry spans the loop's earlier calls (grow's realloc, parse_value), so it
   is at wle' SEGS RZ_cf; this run makes no call, and runs by the runner's R form at wle', concluding SRr' *)
Lemma vi_run_head {WS : list (list Z)} : forall (fxP : YK11.FPState) E W2 ly2 S2 Hp2 regs2 mem2 md2 k
    (Q : world SEGS -> config -> Prop),
  spZ regs2 = spZ (ie_regs E) - 144 -> 0 <= spZ (ie_regs E) - 144 -> spZ (ie_regs E) <= 2 ^ 64 ->
  vi_saved W2 mem2 (ie_regs E) -> getr regs2 (Z_to_bv 5 10) = Z_to_bv 64 0 ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) [] ly2 S2 Hp2 W2 mem2 md2 k
    WS ->
  (forall regs' md', (forall n, In n vi_kregs -> getr regs' (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
     ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
       (spZ (ie_regs E) + ie_e E)
       (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) [] ly2 S2 Hp2 W2 mem2 md' k
       WS ->
     Q W2 (mkCfg (@YK11.mkst fxP regs' (w64 (A_IPC A_IELEM_SLOT)) mem2 (YK11.seg_rom SEGS)) md')) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W2
    (mkCfg (@YK11.mkst fxP regs2 (w64 (A_IPC A_IGROWRET_SLOT)) mem2 (YK11.seg_rom SEGS)) md2) Q.
Proof.
  intros fxP E W2 ly2 S2 Hp2 regs2 mem2 md2 k Q Hsp2 Hlo Hhi HSV2 Ha0 HJw HQ.
  pose proof (ajxR_wild HJw) as Hwild.
  pose proof (YCbqGwild.ajournal_xw_rebaseR SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJc.
  destruct (vi_st_ok_a0 A_IGROWRET_SLOT fxP W2 (ie_regs E) regs2 mem2 0 Hsp2 Hlo Hhi HSV2 Ha0) as [HS2 SHOK2].
  assert (HEI2 : img_env VAL A_LIM (vi_EI regs2 (ie_regs E))) by (unfold vi_EI; apply Eimg_env).
  pose (RUNTO := paj_run_to_xR (fx := fxP) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS
                  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf)
                  (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  paj_run_to_tok_x RUNTO HS2 HJc SHOK2 vi_Bspan (4 * Z.of_nat A_IELEM_SLOT).
  { eapply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  assert (HMEM : ms_mem ms = mem2)
    by (apply functional_extensionality; intros x; exact (vi_frame_all _ _ _ HF x)).
  assert (HK : forall n, In n vi_kregs -> getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [vi_kregs In] in Hn.
    repeat (destruct Hn as [<- | Hn]; [vi_kreg HS2|]). destruct Hn. }
  pmkst HS2. rewrite HMEM in HJc |- *.
  apply (SRrG_ret SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf)). apply (HQ _ _ HK).
  exact (YCbqGwild.ajournal_xw_unbase0R SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
           _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc Hwild).
Qed.

Lemma vi_run_exit {WS : list (list Z)} : forall (fxP : YK11.FPState) E W2 ly2 S2 Hp2 regs2 mem2 md2 k
    (Q : world SEGS -> config -> Prop),
  spZ regs2 = spZ (ie_regs E) - 144 -> 0 <= spZ (ie_regs E) - 144 -> spZ (ie_regs E) <= 2 ^ 64 ->
  vi_saved W2 mem2 (ie_regs E) -> getr regs2 (Z_to_bv 5 10) = Z_to_bv 64 (-1) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) [] ly2 S2 Hp2 W2 mem2 md2 k
    WS ->
  (forall regs' md', (forall n, In n vi_xregs -> getr regs' (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
     getr regs' 18 = w64 (-1) ->
     ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
       (spZ (ie_regs E) + ie_e E)
       (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) [] ly2 S2 Hp2 W2 mem2 md' k
       WS ->
     Q W2 (mkCfg (@YK11.mkst fxP regs' (w64 (A_IPC A_IEPI_SLOT)) mem2 (YK11.seg_rom SEGS)) md')) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W2
    (mkCfg (@YK11.mkst fxP regs2 (w64 (A_IPC A_IGROWRET_SLOT)) mem2 (YK11.seg_rom SEGS)) md2) Q.
Proof.
  intros fxP E W2 ly2 S2 Hp2 regs2 mem2 md2 k Q Hsp2 Hlo Hhi HSV2 Ha0 HJw HQ.
  pose proof (ajxR_wild HJw) as Hwild.
  pose proof (YCbqGwild.ajournal_xw_rebaseR SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJc.
  destruct (vi_st_ok_a0 A_IGROWRET_SLOT fxP W2 (ie_regs E) regs2 mem2 (-1) Hsp2 Hlo Hhi HSV2 Ha0) as [HS2 SHOK2].
  assert (HEI2 : img_env VAL A_LIM (vi_EI regs2 (ie_regs E))) by (unfold vi_EI; apply Eimg_env).
  pose (RUNTO := paj_run_to_xR (fx := fxP) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS
                  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf)
                  (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  paj_run_to_tok_x RUNTO HS2 HJc SHOK2 vi_Bspan (4 * Z.of_nat A_IEPI_SLOT).
  { eapply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  assert (HMEM : ms_mem ms = mem2)
    by (apply functional_extensionality; intros x; exact (vi_frame_all _ _ _ HF x)).
  assert (HK : forall n, In n vi_xregs -> getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [vi_xregs In] in Hn.
    repeat (destruct Hn as [<- | Hn]; [vi_kreg HS2|]). destruct Hn. }
  assert (H18 : getr (ms_regs ms) 18 = w64 (-1)).
  { change (getr (ms_regs ms) 18) with (getr (ms_regs ms) (Z_to_bv 5 18)).
    let Hr := fresh "Hr" in vi_reg HS2 (Z_to_bv 5 18) Hr; rewrite Hr.
    unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. }
  pmkst HS2. rewrite HMEM in HJc |- *.
  apply (SRrG_ret SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf)). apply (HQ _ _ HK H18).
  exact (YCbqGwild.ajournal_xw_unbase0R SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
           _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc Hwild).
Qed.

(* ---- moving a position's facts to the state after a call ---- *)

(* bytes that read the same and are present keep every byte fact (VrdFrame.rd_keep) *)
Lemma vi_keep_of_av : forall (H H' : word -> bool) (m m' : word -> option byte) (Pz : Z -> Prop),
  (forall a, Pz a -> aview SEGS H' m' a = aview SEGS H m a /\ apresent H' m' a) ->
  rd_keep SEGS (mrestrict H m) (mrestrict H' m') Pz.
Proof.
  intros H H' m m' Pz HK. split; intros a Ha.
  - apply prh_mbyte_of_aview. exact (proj1 (HK a Ha)).
  - intros _. apply apresent_writable. exact (proj2 (HK a Ha)).
Qed.

(* the frame words, at a state with the same sp, world and memory *)
Lemma vi_iframe_sp : forall E P P', vrd_iframe E P -> spZ (ip_regs P') = spZ (ip_regs P) ->
  ip_W P' = ip_W P -> ip_mem P' = ip_mem P -> vrd_iframe E P'.
Proof.
  intros E P P' HF Hsp HW Hm. unfold vrd_iframe in *. cbv zeta in *. rewrite HW, Hm, Hsp. exact HF.
Qed.

Ltac vi_cs := match goal with |- In (bv_unsigned ?r) vi_kregs =>
  let z := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with z; cbn [vi_kregs In]; tauto end.

(* the loop's registers, at a state whose kept registers are the position's *)
Lemma vi_iregs_keep : forall E P P', vrd_iregs B E P ->
  (forall n, In n vi_kregs -> getr (ip_regs P') (Z_to_bv 5 n) = getr (ip_regs P) (Z_to_bv 5 n)) ->
  vrd_iregs B E P'.
Proof.
  intros E P P' HR HK.
  destruct HR as (R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  assert (G : forall (r : bv 5) (w : word), In (bv_unsigned r) vi_kregs -> getr (ip_regs P) r = w ->
            getr (ip_regs P') r = w).
  { intros r w Hn Hw. pose proof (HK _ Hn) as E1. rewrite !Z_to_bv_bv_unsigned in E1. rewrite E1. exact Hw. }
  unfold vrd_iregs.
  repeat (split; [apply G; [vi_cs | assumption]|]).
  apply G; [vi_cs | assumption].
Qed.

Lemma vi_kregs_cs : forall n, In n vi_kregs -> acallee_saved n.
Proof. intros n Hn. cbn [vi_kregs In] in Hn. unfold acallee_saved. lia. Qed.

(* every byte of a harness block of a state is present there *)
Lemma vi_lam_present : forall ly S Hp W mem md Lam peak cnt fail ran most own a k x,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  a <= x < a + k -> apresent (w_H W) mem x.
Proof.
  intros ly S Hp W mem md Lam peak cnt fail ran most own a k x HAR HLd Hin Hx.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HLd Hin) as (Hk & Hab & _).
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & _ & _ & _ & Hpr & _).
  pose proof (@cf_head_nonneg cp).
  apply (proj1 (Hpr x ltac:(unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia))).
Qed.

(* two harness blocks of a state with different addresses hold no byte in common *)
Lemma vi_lam_disj : forall ly S Hp W mem md Lam peak cnt fail ran most own a k a' k' x,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> In (a', k') Lam -> a <> a' -> a <= x < a + k ->
  ~ (a' - cf_head <= x < a' - cf_head + req_size (k' + cf_head)).
Proof.
  intros ly S Hp W mem md Lam peak cnt fail ran most own a k a' k' x HAR HLd Hin Hin' Hne Hx Hx'.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HLd Hin) as (Hk & Hab & _).
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a' k' _ _ HLd Hin') as (Hk' & Hab' & _).
  assert (Hneq : (a - cf_head, k + cf_head) <> (a' - cf_head, k' + cf_head)) by (intros E; injection E; lia).
  pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hab Hab' Hneq) as Hd.
  pose proof (@cf_head_nonneg cp).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold req_size in Hd, Hx'.
  destruct (Z.eqb_spec (k + cf_head) 0); destruct (Z.eqb_spec (k' + cf_head) 0); lia.
Qed.

Lemma vi_nodup_app_disj : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x H Hin Hin2; [destruct Hin|].
  cbn [app] in H. apply List.NoDup_cons_iff in H as [Hy H]. destruct Hin as [-> | Hin].
  - apply Hy. apply in_or_app. right. exact Hin2.
  - exact (IH l2 x H Hin Hin2).
Qed.

Lemma vi_nodup_of : forall (Lam D L : list (Z * Z)), NoDup (map fst Lam) -> Permutation Lam (D ++ L) ->
  NoDup D /\ NoDup (map fst D) /\ (forall a k a' k', In (a, k) D -> In (a', k') L -> a <> a').
Proof.
  intros Lam D L H Hp. apply NoDup_ListNoDup in H.
  assert (H2 : List.NoDup (map fst (D ++ L))) by (apply (Permutation_NoDup (Permutation_map fst Hp)); exact H).
  rewrite map_app in H2. split; [|split].
  - apply NoDup_ListNoDup. exact (NoDup_map_inv _ _ (NoDup_app_remove_r _ _ H2)).
  - apply NoDup_ListNoDup. exact (NoDup_app_remove_r _ _ H2).
  - intros a k a' k' Hin Hin' ->. apply (vi_nodup_app_disj _ _ a' H2).
    + apply in_map_iff. exists (a', k). split; [reflexivity | exact Hin].
    + apply in_map_iff. exists (a', k'). split; [reflexivity | exact Hin'].
Qed.

(* the blocks a later state owns are apart from the node (its home at the entry: a harness block of the entry, an
   allocator block of the entry, or a fake frame of the entry - all still live, all apart from the new blocks) *)
Lemma vi_apart_node : forall CTX E ly S Hp W mem md D tr Lam peak cnt fail ran most own,
  vrd_ient_ok B ARx CTX CTX0 CW E -> ARx ly S Hp W mem md ->
  layout_le (length (st_secs (ie_S E))) (ie_ly E) ly ->
  rd_blocks_move B (ie_ly E) (ie_S E) ly S D tr (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ie_d E) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> Permutation Lam (D ++ ie_Lam E) ->
  pj_apartR D (ie_v E).
Proof.
  intros CTX E ly S Hp W mem md D tr Lam peak cnt fail ran most own HEN HAR Hlyle (HDnew & HABp & HFRp & _) HLd HLp.
  destruct HEN as ((HAFN & _) & _ & _ & _ & HRD & _).
  pose proof HAFN as (HAR0 & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode & _ & _ & Hvwin & HLED0 & _).
  pose proof Hnode as (_ & _ & _ & _ & Hvat & _).
  pose proof (alx_layout SEGS B ARx LAWS (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) ly HAR0 Hlyle)
    as (_ & Hfa_ly & _).
  pose proof (@cf_head_nonneg cp) as Hcf.
  pose proof HLd as (_ & HND & _).
  destruct (vi_nodup_of Lam D (ie_Lam E) HND HLp) as (_ & _ & Hdis).
  intros [bb kk] x Hin Hx Hvx. unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
  assert (HinL : In (bb, kk) Lam) by (apply (Permutation_in _ (Permutation_sym HLp)); apply in_or_app; left; exact Hin).
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ bb kk _ _ HLd HinL) as (Hk & Hab & _).
  pose proof (HDnew bb kk Hin) as Hnew.
  assert (Hreq : req_size (kk + cf_head) = kk + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
  destruct Hvat as [(a0 & k0 & Hin0 & Hle & Hhi) | [(b0 & m0 & Hin0 & _ & Hle & Hhi) | [(cid & pos & Hin0 & Hle & Hhi) | Hww]]].
  - assert (HinL0 : In (a0, k0) Lam)
      by (apply (Permutation_in _ (Permutation_sym HLp)); apply in_or_app; right; exact Hin0).
    apply (vi_lam_disj _ _ _ _ _ _ _ _ _ _ _ _ _ bb kk a0 k0 x HAR HLd HinL HinL0 (Hdis _ _ _ _ Hin Hin0) Hx).
    unfold req_size. destruct (Z.eqb_spec (k0 + cf_head) 0); lia.
  - assert (Hin0' : In (b0, m0) (ablocks B ly S))
      by (apply (Permutation_in _ (Permutation_sym HABp)); apply in_or_app; right; exact Hin0).
    assert (Hne : (b0, m0) <> (bb - cf_head, kk + cf_head)) by (intros Heq; rewrite Heq in Hin0; exact (Hnew Hin0)).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hin0' Hab Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq in Hd.
    assert (m0 <= req_size m0) by (unfold req_size; destruct (Z.eqb_spec m0 0); lia). lia.
  - assert (Hin0' : In (cid, pos) (frames S)) by (apply (Permutation_in _ (Permutation_sym HFRp)); exact Hin0).
    pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ cid pos HAR Hab Hin0') as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq, Hfa_ly in Hd. lia.
  - exfalso. lia.
Qed.

(* bytes a block copy carried (grow's bytes_at k' kb with kb the old array's bytes) read the same at the copy *)
Lemma vi_bytes_mbyte : forall W mem W' mem' a a' n x,
  (forall y, a <= y < a + n -> apresent (w_H W) mem y) ->
  bytes_at W' mem' a' (vi_bytes W mem a n) -> 0 <= x < n ->
  mbyte SEGS (mrestrict (w_H W') mem') (a' + x) = mbyte SEGS (mrestrict (w_H W) mem) (a + x).
Proof.
  intros W mem W' mem' a a' n x HP Hb Hx.
  destruct (vi_bytes_ok W mem a n ltac:(lia) HP) as (Hb0 & Hl).
  assert (Hj : (Z.to_nat x < length (vi_bytes W mem a n))%nat) by lia.
  destruct (Hb (Z.to_nat x) Hj) as (Hv & _). destruct (Hb0 (Z.to_nat x) Hj) as (Hv0 & _).
  specialize (Hv 0%nat ltac:(lia)). specialize (Hv0 0%nat ltac:(lia)).
  rewrite Z2Nat.id in Hv, Hv0 by lia. cbn [Z.of_nat] in Hv, Hv0. rewrite Z.add_0_r in Hv, Hv0.
  rewrite Hv, Hv0. reflexivity.
Qed.

(* blocks both states own, outside the callee's footprint, keep their bytes (THE KIT'S CUT: the journal at any budget, and
   at any world relation R, its world conjunct unread) *)
Lemma vi_keep_blocks {R : world SEGS -> world SEGS -> Prop} {WS : list (list Z)} :
  forall STK sp0 FP ly S Hp W mem md ly' S' Hp' W' mem' md' k
    Lam peak cnt fail ran most own Lam' peak' cnt' fail' ran' most' own' (Dk : list (Z * Z)),
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx R STK sp0 FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k WS ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most' own' ->
  (forall b, In b Dk -> In b Lam /\ In b Lam') ->
  (forall b x, In b Dk -> pj_holdsR b x -> ~ inFP FP x) ->
  rd_keep SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') (rd_blk Dk).
Proof.
  intros STK sp0 FP ly S Hp W mem md ly' S' Hp' W' mem' md' k Lam peak cnt fail ran most own Lam' peak' cnt' fail'
    ran' most' own' Dk HJ HLd HLd' Hboth HnFP.
  pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  pose proof (@cf_head_nonneg cp) as Hcf.
  apply vi_keep_of_av. intros x Hx. apply Exists_exists in Hx as ((a0 & k0) & Hin & Hh).
  pose proof Hh as Hh'. unfold pj_holdsR in Hh'; cbn [fst snd] in Hh'.
  destruct (Hboth _ Hin) as (HinL & HinL').
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a0 k0 _ _ HLd HinL) as (Hk & Hab & _).
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a0 k0 _ _ HLd' HinL') as (_ & Hab' & _).
  split.
  - replace x with (a0 - cf_head + (x - (a0 - cf_head))) by lia.
    apply (F2 _ _ _ Hab Hab').
    + unfold req_size. destruct (Z.eqb_spec (k0 + cf_head) 0); lia.
    + replace (a0 - cf_head + (x - (a0 - cf_head))) with x by lia. exact (HnFP _ x Hin Hh).
  - exact (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 x HAR' HLd' HinL' Hh').
Qed.

(* the room of the rest, after a granted step (THE KIT'S CUT: rd_room's live conjunct is per event, PRH_Base.prh_live_evs;
   the rest's live room is the tail of the step's events from the state the step leads to, so the premises are the
   step's live-request move and room_live_cf, as VrdLedgerStep.vl_room_tail, which it is) *)
Lemma vi_room_after : forall S S' trg tl,
  rd_room S (trg ++ tl) -> room_live_cf S' ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetReqAt.rd_hevs trg)) ->
  rd_room S' tl.
Proof. exact vl_room_tail. Qed.

(* a partly built node (refused inside the loop) is freeable to one more than its elements' depth *)
Lemma vi_part_fd : forall m lblk v ty kids keys n cap ks Dk Dy Di D (l : list (list Z * jv)) k,
  NoDup D -> pj_apartR D v -> pj_hdrR SEGS m v ty 0 0 kids keys n cap ->
  (kids = 0 /\ n = 0 /\ Dk = [] \/ exists kk, lblk kids kk /\ 56 * n <= kk /\ Dk = [(kids, kk)]) ->
  (keys = 0 /\ ks = false /\ Dy = [] \/ ks = true /\ exists kk, lblk keys kk /\ 8 * n <= kk /\ Dy = [(keys, kk)]) ->
  Permutation D (Dk ++ Dy ++ Di) ->
  (if ks then pj_memsR SEGS m lblk (pj_nodeR SEGS m lblk) kids keys l Di
   else pj_itemsR (pj_nodeR SEGS m lblk) kids (map snd l) Di) ->
  Z.of_nat (length l) = n ->
  Forall (fun mm => (PjTree.depth (snd mm) <= k)%nat) l ->
  pj_fdR SEGS m lblk (S k) v D.
Proof.
  intros m lblk v ty kids keys n cap ks Dk Dy Di D l k HND HAP Hhdr Hk Hy HD Hsub Hn Hd.
  cbn [pj_fdR]. split; [exact HND|]. split; [exact HAP|].
  exists ty, 0, 0, kids, keys, n, cap, ks, [], Dk, Dy, Di.
  split; [exact Hhdr|]. split; [left; split; reflexivity|]. split; [exact Hk|]. split; [exact Hy|].
  split; [exact HD|].
  rewrite <- Hn, Nat2Z.id. destruct ks.
  - apply (vrd_fd_mems SEGS l); [apply Forall_forall; intros mm _; apply vrd_nodefd_all | exact Hsub | exact Hd].
  - rewrite <- (length_map snd l).
    apply (vrd_fd_items SEGS (map snd l)); [apply Forall_forall; intros u _; apply vrd_nodefd_all | exact Hsub |].
    apply Forall_map. exact Hd.
Qed.

(* the subtree below the node's array, at another memory and possibly a copied array *)
Lemma vi_sub_move : forall (o : bool) m m' lblk lblk' kids keys kids' keys' (acc : list (list Z * jv)) Di,
  (if o then pj_memsR SEGS m lblk (pj_nodeR SEGS m lblk) kids keys (rev acc) Di
   else pj_itemsR (pj_nodeR SEGS m lblk) kids (map snd (rev acc)) Di) ->
  (forall x k, In (x, k) Di -> lblk x k -> lblk' x k) ->
  rd_keep SEGS m m' (rd_blk Di) ->
  (forall x, 0 <= x < 56 * Z.of_nat (length acc) -> mbyte SEGS m' (kids' + x) = mbyte SEGS m (kids + x)) ->
  (forall x, 0 <= x < 56 * Z.of_nat (length acc) -> writable_at SEGS m' (kids' + x)) -> kids' mod 8 = 0 ->
  (o = true -> forall x, 0 <= x < 8 * Z.of_nat (length acc) -> mbyte SEGS m' (keys' + x) = mbyte SEGS m (keys + x)) ->
  (forall b x, In b Di -> pj_holdsR b x -> ~ (kids' <= x < kids' + 56 * Z.of_nat (length acc))) ->
  (if o then pj_memsR SEGS m' lblk' (pj_nodeR SEGS m' lblk') kids' keys' (rev acc) Di
   else pj_itemsR (pj_nodeR SEGS m' lblk') kids' (map snd (rev acc)) Di).
Proof.
  intros o m m' lblk lblk' kids keys kids' keys' acc Di Hs Himp HK Hb Hw Hal Hkb HAP.
  destruct o.
  - apply (vrd_mems_move SEGS (rev acc) m m' lblk lblk' kids kids' keys keys' Di Hs Himp HK);
      rewrite ?length_rev; [exact Hb | exact Hw | exact Hal | exact (Hkb eq_refl) | exact HAP].
  - apply (vrd_items_move SEGS (map snd (rev acc)) m m' lblk lblk' kids kids' Di Hs Himp HK);
      rewrite ?length_map, ?length_rev; [exact Hb | exact Hw | exact Hal | exact HAP].
Qed.

(* ==== THE KIT'S CUT: THE BATCH KIT'S LAYER ACROSS grow (VrdIElem.v's vrd_incaps / vrd_iforder / the model's free list) ==== *)

(* the ordered twin of vi_part_fd: a node's order list is its slots' list, then its arrays (no str block) *)
Lemma vi_part_fo : forall m lblk v ty kids keys n cap ks Dk Dy Di D Facc nn,
  NoDup D -> pj_apartR D v -> pj_hdrR SEGS m v ty 0 0 kids keys n cap ->
  (kids = 0 /\ n = 0 /\ Dk = [] \/ exists kk, lblk kids kk /\ 56 * n <= kk /\ Dk = [(kids, kk)]) ->
  (keys = 0 /\ ks = false /\ Dy = [] \/ ks = true /\ exists kk, lblk keys kk /\ 8 * n <= kk /\ Dy = [(keys, kk)]) ->
  Permutation D (Dk ++ Dy ++ Di) ->
  PRH_PjOrder.pf_oitemsR SEGS m lblk (PRH_PjOrder.pj_foR SEGS m lblk nn) ks kids keys (Z.to_nat n) Di Facc ->
  PRH_PjOrder.pj_foR SEGS m lblk (S nn) v D (Facc ++ Dk ++ Dy).
Proof.
  intros m lblk v ty kids keys n cap ks Dk Dy Di D Facc nn HND HAP Hhdr Hk Hy HD HOI.
  cbn [PRH_PjOrder.pj_foR]. unfold PRH_PjOrder.pj_oshapeR.
  split; [first [exact HND | apply NoDup_ListNoDup; exact HND]|]. split; [exact HAP|].
  exists ty, 0, 0, kids, keys, n, cap, ks, [], Dk, Dy, Di, Facc.
  split; [exact Hhdr|]. split; [left; split; reflexivity|]. split; [exact Hk|]. split; [exact Hy|].
  split; [exact HD|]. split; [exact HOI|]. rewrite app_nil_r. reflexivity.
Qed.

(* vi_sub_move's keep premises, as one predicate: the members' blocks Di in the new ledger and kept, the slot array
   copied from kids to kids' (in place when kids' = kids), writable there and apart from Di, the keys copied *)
Definition vi_subkeep (o : bool) (m m' : word -> option byte) (lblk' : Z -> Z -> Prop) (kids keys kids' keys' : Z)
  (acc : list (list Z * jv)) (Di : list (Z * Z)) : Prop :=
  (forall x k, In (x, k) Di -> lblk' x k) /\ rd_keep SEGS m m' (rd_blk Di) /\
  (forall x, 0 <= x < 56 * Z.of_nat (length acc) -> mbyte SEGS m' (kids' + x) = mbyte SEGS m (kids + x)) /\
  (forall x, 0 <= x < 56 * Z.of_nat (length acc) -> writable_at SEGS m' (kids' + x)) /\ kids' mod 8 = 0 /\
  (o = true -> forall x, 0 <= x < 8 * Z.of_nat (length acc) -> mbyte SEGS m' (keys' + x) = mbyte SEGS m (keys + x)) /\
  (forall b x, In b Di -> pj_holdsR b x -> ~ (kids' <= x < kids' + 56 * Z.of_nat (length acc))).

(* the completed slots' order list at the new memory (its block list Di' a permutation of vrd_inode's Di) *)
Lemma vi_fo_sub : forall (o : bool) m m' lblk lblk' kids keys kids' keys' (acc : list (list Z * jv)) Di Di' Facc nn,
  vi_subkeep o m m' lblk' kids keys kids' keys' acc Di -> Permutation Di' Di ->
  PRH_PjOrder.pf_oitemsR SEGS m lblk (PRH_PjOrder.pj_foR SEGS m lblk nn) o kids keys (length acc) Di' Facc ->
  PRH_PjOrder.pf_oitemsR SEGS m' lblk' (PRH_PjOrder.pj_foR SEGS m' lblk' nn) o kids' keys' (length acc) Di' Facc.
Proof.
  intros o m m' lblk lblk' kids keys kids' keys' acc Di Di' Facc nn (HLk & HK & Hb & Hw & Hal & Hkb & HAP) HP HOI.
  assert (HinD : forall b, In b Di' -> In b Di) by (intros b Hb'; exact (Permutation_in _ HP Hb')).
  apply (vrd_fo_items_move SEGS nn m m' lblk lblk' o kids keys kids' keys' (length acc) Di' Facc HOI).
  - intros x k Hin. exact (HLk x k (HinD _ Hin)).
  - eapply rd_keep_mono; [exact HK|]. intros z Hz. exact (rd_blk_sub Di' Di z HinD Hz).
  - exact Hb.
  - exact Hw.
  - exact Hal.
  - intros b x Hin Hx. exact (HAP b x (HinD _ Hin) Hx).
  - exact Hkb.
Qed.

(* the members' capacities at the new memory *)
Lemma vi_nc_sub : forall (o : bool) m m' lblk lblk' kids keys kids' keys' (acc : list (list Z * jv)) Di,
  (if o then pj_memsR SEGS m lblk (pj_nodeR SEGS m lblk) kids keys (rev acc) Di
   else pj_itemsR (pj_nodeR SEGS m lblk) kids (map snd (rev acc)) Di) ->
  vi_subkeep o m m' lblk' kids keys kids' keys' acc Di ->
  pj_kidsR (fun a (mb : list Z * jv) => pj_ncapR SEGS m a (snd mb)) kids (rev acc) ->
  pj_kidsR (fun a (mb : list Z * jv) => pj_ncapR SEGS m' a (snd mb)) kids' (rev acc).
Proof.
  intros o m m' lblk lblk' kids keys kids' keys' acc Di Hs (_ & HK & Hb & _) HNC. destruct o.
  - apply (vrd_ncaps_mems_move SEGS (rev acc) m m' lblk kids kids' keys Di Hs HNC HK).
    rewrite length_rev. exact Hb.
  - apply (vrd_ncaps_items_move SEGS (rev acc) m m' lblk kids kids' Di Hs HNC HK).
    rewrite length_rev. exact Hb.
Qed.

(* the batch kit order list of a loop position carried to a later one with the same members (a granted or no-op grow):
   the block list after the arrays is vrd_inode's Di at both *)
Lemma vi_iforder_step : forall E P P' af Di,
  vrd_iforder E P [] af -> ip_acc P' = ip_acc P -> ip_n P' = ip_n P ->
  Z.of_nat (length (ip_acc P)) = ip_n P ->
  Permutation (ip_D P) ([] ++ kids_blkR (ip_kids P) (ip_cap P) ++
                        keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ Di) ->
  Permutation (ip_D P') (kids_blkR (ip_kids P') (ip_cap P') ++
                         keys_blkR (if ie_o E then 6 else 5) (ip_keys P') (ip_cap P') ++ Di) ->
  vi_subkeep (ie_o E) (rdW (ip_W P) (ip_mem P)) (rdW (ip_W P') (ip_mem P')) (prh_lin (ip_Lam P'))
    (ip_kids P) (ip_keys P) (ip_kids P') (ip_keys P') (ip_acc P) Di ->
  vrd_iforder E P' [] af.
Proof.
  intros E P P' af Di HFO Hacc Hn Hlen HD HD' HSK Hh nn Hnn.
  rewrite Hacc in Hnn.
  destruct (HFO Hh nn Hnn) as (Di' & Facc & HP & HOI & Hm).
  assert (HPi : Permutation Di' Di).
  { apply (Permutation_app_inv_l (kids_blkR (ip_kids P) (ip_cap P) ++
                                  keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P))).
    rewrite <- !app_assoc. cbn [app] in HP, HD.
    exact (Permutation_trans (Permutation_sym HP) HD). }
  exists Di', Facc. split; [|split; [|exact Hm]].
  - cbn [app]. eapply Permutation_trans; [exact HD'|].
    apply Permutation_app_head. apply Permutation_app_head. exact (Permutation_sym HPi).
  - rewrite Hn. replace (Z.to_nat (ip_n P)) with (length (ip_acc P)) in HOI |- * by lia.
    exact (vi_fo_sub (ie_o E) _ _ _ _ _ _ _ _ (ip_acc P) Di Di' Facc nn HSK HPi HOI).
Qed.

(* the members' capacities likewise *)
Lemma vi_incaps_step : forall E P P' Di,
  vrd_incaps E P -> ip_acc P' = ip_acc P ->
  (if ie_o E
   then pj_memsR SEGS (rdW (ip_W P) (ip_mem P)) (prh_lin (ip_Lam P))
          (pj_nodeR SEGS (rdW (ip_W P) (ip_mem P)) (prh_lin (ip_Lam P))) (ip_kids P) (ip_keys P) (rev (ip_acc P)) Di
   else pj_itemsR (pj_nodeR SEGS (rdW (ip_W P) (ip_mem P)) (prh_lin (ip_Lam P))) (ip_kids P)
          (map snd (rev (ip_acc P))) Di) ->
  vi_subkeep (ie_o E) (rdW (ip_W P) (ip_mem P)) (rdW (ip_W P') (ip_mem P')) (prh_lin (ip_Lam P'))
    (ip_kids P) (ip_keys P) (ip_kids P') (ip_keys P') (ip_acc P) Di ->
  vrd_incaps E P'.
Proof.
  intros E P P' Di HNC Hacc Hs HSK. unfold vrd_incaps in HNC |- *. rewrite Hacc.
  exact (vi_nc_sub (ie_o E) _ _ _ _ _ _ _ _ (ip_acc P) Di Hs HSK HNC).
Qed.

(* the capacity after grow: the count's ncap (PresetReqAt.ncap (S n) = gcap n (ncap n)), room left or doubled *)
Lemma vi_ncap_lt : forall n cap, 0 <= n < cap -> cap = Z.of_nat (PresetReqAt.ncap (Z.to_nat n)) ->
  cap = Z.of_nat (PresetReqAt.ncap (S (Z.to_nat n))).
Proof.
  intros n cap Hn Hc.
  replace (PresetReqAt.ncap (S (Z.to_nat n))) with (PjRoundTrip.gcap (Z.to_nat n) (PresetReqAt.ncap (Z.to_nat n)))
    by reflexivity.
  unfold PjRoundTrip.gcap. destruct (Nat.ltb_spec (Z.to_nat n) (PresetReqAt.ncap (Z.to_nat n))); lia.
Qed.

Lemma vi_ncap_eq : forall n cap, 0 < cap -> n = cap -> cap = Z.of_nat (PresetReqAt.ncap (Z.to_nat n)) ->
  2 * cap = Z.of_nat (PresetReqAt.ncap (S (Z.to_nat n))).
Proof.
  intros n cap Hc Hn HN.
  replace (PresetReqAt.ncap (S (Z.to_nat n))) with (PjRoundTrip.gcap (Z.to_nat n) (PresetReqAt.ncap (Z.to_nat n)))
    by reflexivity.
  unfold PjRoundTrip.gcap. destruct (Nat.ltb_spec (Z.to_nat n) (PresetReqAt.ncap (Z.to_nat n))); [lia|].
  destruct (Nat.eqb_spec (PresetReqAt.ncap (Z.to_nat n)) 0); lia.
Qed.

(* the model's free list across grow: granted, jfl one member deep is vrd_jfb at the new cap; refused, the completed
   slots' list then the arrays the refused grow left (PresetReqAt.gheld) *)
Lemma vi_fl_granted : forall d (o : bool) x ok f n cap af y okg cap1 g,
  (forall okr, prhPi_frees d o x (ok ++ okr) = PresetReqAt.jfl ReaderRes.jr_strtod (S f) (S d) o n cap af y okr) ->
  (forall okr, PjGrammar.grow o n cap (okg ++ okr) = (Some cap1, g, okr)) ->
  forall okr, prhPi_frees d o x ((ok ++ okg) ++ okr) = vrd_jfb f (S d) o n cap1 af y okr.
Proof.
  intros d o x ok f n cap af y okg cap1 g HF HG okr.
  rewrite <- app_assoc, (HF (okg ++ okr)), vrd_jfl_unfold, (HG okr). reflexivity.
Qed.

Lemma vi_fl_refused : forall d (o : bool) x ok f n cap af y okr tg ok',
  (forall okr, prhPi_frees d o x (ok ++ okr) = PresetReqAt.jfl ReaderRes.jr_strtod (S f) (S d) o n cap af y okr) ->
  PjGrammar.grow o n cap okr = (None, tg, ok') ->
  prhPi_frees d o x (ok ++ okr) = af ++ PresetReqAt.gheld o cap tg.
Proof. intros d o x ok f n cap af y okr tg ok' HF HG. rewrite (HF okr), vrd_jfl_unfold, HG. reflexivity. Qed.

(* grow with room left does nothing and consumes no grant *)
Lemma vi_grow_lt : forall (o : bool) n cap ok, (n < cap)%nat -> PjGrammar.grow o n cap ok = (Some cap, [], ok).
Proof.
  intros o n cap ok H. unfold PjGrammar.grow. rewrite (proj2 (Nat.ltb_lt n cap) H). reflexivity.
Qed.

(* the arrays an object's refused keys realloc leaves after a granted kids realloc: the new kids, the old keys *)
Lemma vi_gheld_half : forall c : nat, (0 < c)%nat ->
  PresetReqAt.gheld true c [PjGrammar.EGrow (56 * c) (56 * (2 * c)); PjGrammar.EFail (8 * (2 * c))] =
  [Z.of_nat (56 * (2 * c)) + PresetReqAt.HEAD; Z.of_nat (8 * c) + PresetReqAt.HEAD].
Proof. intros [|c] Hc; [lia | reflexivity]. Qed.

(* the members fit every depth bound nn at or above MAXD - S d *)
Lemma vi_dep_le : forall (acc : list (list Z * jv)) k nn, (k <= nn)%nat ->
  Forall (fun mm => (PjTree.depth (snd mm) <= k)%nat) acc ->
  Forall (fun mm => (PjTree.depth (snd mm) <= nn)%nat) acc.
Proof. intros acc k nn Hk H. eapply Forall_impl; [|exact H]. intros mm Hm. cbv beta in Hm |- *. lia. Qed.

(* THE PARTIAL FREE ORDER AT A REFUSED grow (the post's None arm): the completed slots' order list at the exit
   memory, then the arrays as the refused grow left them (Dk ++ Dy, the model's gheld); the arguments after the order
   facts are vi_part_fd's *)
Lemma vi_fo_exit : forall E P af Di (W' : world SEGS) mem' Lam' ok' okr tg ok2 ty kids keys n cap Dk Dy D',
  vrd_iforder E P [] af ->
  (forall okr, prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P ++ okr) =
     PresetReqAt.jfl ReaderRes.jr_strtod (S (ip_f P)) (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P))
       (Z.to_nat (ip_cap P)) af (rest_atR (ie_tb E) (ie_text E) (ip_p P)) okr) ->
  PjGrammar.grow (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) okr = (None, tg, ok2) ->
  ok' = ip_ok P ++ okr ->
  Z.of_nat (length (ip_acc P)) = ip_n P ->
  Forall (fun mm => (PjTree.depth (snd mm) <= PjGrammar.MAXD - S (ie_d E))%nat) (ip_acc P) ->
  (ie_d E < PjGrammar.MAXD)%nat ->
  Permutation (ip_D P) ([] ++ kids_blkR (ip_kids P) (ip_cap P) ++
                        keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ Di) ->
  vi_subkeep (ie_o E) (rdW (ip_W P) (ip_mem P)) (rdW W' mem') (prh_lin Lam')
    (ip_kids P) (ip_keys P) kids keys (ip_acc P) Di ->
  (cf_head = PresetReqAt.HEAD -> map (fun b => snd b + cf_head) (Dk ++ Dy) =
     PresetReqAt.gheld (ie_o E) (Z.to_nat (ip_cap P)) tg) ->
  n = ip_n P ->
  NoDup D' -> pj_apartR D' (ie_v E) -> pj_hdrR SEGS (rdW W' mem') (ie_v E) ty 0 0 kids keys n cap ->
  (kids = 0 /\ n = 0 /\ Dk = [] \/ exists kk, prh_lin Lam' kids kk /\ 56 * n <= kk /\ Dk = [(kids, kk)]) ->
  (keys = 0 /\ ie_o E = false /\ Dy = [] \/
   ie_o E = true /\ exists kk, prh_lin Lam' keys kk /\ 8 * n <= kk /\ Dy = [(keys, kk)]) ->
  Permutation D' (Dk ++ Dy ++ Di) ->
  (cf_head = PresetReqAt.HEAD -> forall n0, (PjGrammar.MAXD - ie_d E <= n0)%nat ->
     exists F, PRH_PjOrder.pj_foR SEGS (rdW W' mem') (prh_lin Lam') n0 (ie_v E) D' F /\
       map (fun b => snd b + cf_head) F =
         prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) ok').
Proof.
  intros E P af Di W' mem' Lam' ok' okr tg ok2 ty kids keys n cap Dk Dy D' HFO HFL HG Hok Hlen Hdep Hd HD HSK
    Hgh Hn HND HAP Hhdr Hk Hy HD' Hh n0 Hn0.
  destruct n0 as [|nn]; [lia|].
  destruct (HFO Hh nn (vi_dep_le (ip_acc P) (PjGrammar.MAXD - S (ie_d E)) nn ltac:(lia) Hdep))
    as (Di' & Facc & HP & HOI & Hm).
  assert (HPi : Permutation Di' Di).
  { apply (Permutation_app_inv_l (kids_blkR (ip_kids P) (ip_cap P) ++
                                  keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P))).
    rewrite <- !app_assoc. cbn [app] in HP, HD.
    exact (Permutation_trans (Permutation_sym HP) HD). }
  replace (Z.to_nat (ip_n P)) with (length (ip_acc P)) in HOI by lia.
  pose proof (vi_fo_sub (ie_o E) _ _ _ _ _ _ _ _ (ip_acc P) Di Di' Facc nn HSK HPi HOI) as HOI'.
  exists (Facc ++ Dk ++ Dy). split.
  - apply (vi_part_fo _ _ (ie_v E) ty kids keys n cap (ie_o E) Dk Dy Di' D' Facc nn HND HAP Hhdr Hk Hy).
    + eapply Permutation_trans; [exact HD'|]. apply Permutation_app_head. apply Permutation_app_head.
      exact (Permutation_sym HPi).
    + rewrite Hn. replace (Z.to_nat (ip_n P)) with (length (ip_acc P)) by lia. exact HOI'.
  - rewrite map_app, Hm, (Hgh Hh), Hok. symmetry. exact (vi_fl_refused _ _ _ _ _ _ _ _ _ okr tg ok2 HFL HG).
Qed.

(* the blocks the call owns after grow swapped some of them (prhReader_swap's allocator-block part): the new blocks
   are fresh - not an old block (their sizes differ) and not one kept (the allocator keeps no block twice) *)
Lemma vi_swap_move : forall ly0 S0 ly S ly2 S2 Hp2 W2 mem2 md2 D tr tr' rest d Dold Dnew Di' bl,
  rd_blocks_move B ly0 S0 ly S D tr rest d ->
  Permutation D (Dold ++ Di') ->
  Permutation (ablocks B ly S) (prhReader_ab Dold ++ bl) ->
  Permutation (ablocks B ly2 S2) (prhReader_ab Dnew ++ bl) ->
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  (forall b, In b Dnew -> 0 < snd b + cf_head) ->
  (forall b b', In b Dnew -> In b' Dold -> snd b <> snd b') ->
  frames S2 = frames S ->
  hpeakR tr' <= 224 * Z.of_nat (length rest) + 512 * Z.of_nat (PjGrammar.MAXD - d) ->
  rd_blocks_move B ly0 S0 ly2 S2 (Dnew ++ Di') tr' rest d.
Proof.
  intros ly0 S0 ly S ly2 S2 Hp2 W2 mem2 md2 D tr tr' rest d Dold Dnew Di' bl (HDnew & HABp & HFRp & _) HDp Hsw1 Hsw2
    HAR2 Hpos Hsz Hfr Hhp.
  assert (Hbl : Permutation bl (prhReader_ab Di' ++ ablocks B ly0 S0)).
  { apply (Permutation_app_inv_l (prhReader_ab Dold)).
    eapply Permutation_trans; [apply Permutation_sym; exact Hsw1|]. eapply Permutation_trans; [exact HABp|].
    rewrite app_assoc. apply Permutation_app_tail. unfold prhReader_ab. rewrite <- map_app.
    apply Permutation_map. exact HDp. }
  split; [|split; [|split]].
  - intros a k Hin Hin0. apply in_app_or in Hin as [Hin | Hin].
    + assert (HinS : In (a - cf_head, k + cf_head) (ablocks B ly S))
        by (apply (Permutation_in _ (Permutation_sym HABp)); apply in_or_app; right; exact Hin0).
      apply (Permutation_in _ Hsw1) in HinS. apply in_app_or in HinS as [HinO | HinB].
      * unfold prhReader_ab in HinO. apply in_map_iff in HinO as ((a'' & k'') & Heq & HinO').
        cbn [fst snd] in Heq. injection Heq as _ Hk. apply (Hsz (a, k) (a'', k'') Hin HinO'). cbn [snd]. lia.
      * assert (HinN : In (a - cf_head, k + cf_head) (prhReader_ab Dnew))
          by (unfold prhReader_ab; apply in_map_iff; exists (a, k); split; [reflexivity | exact Hin]).
        assert (HinS2 : In (a - cf_head, k + cf_head) (ablocks B ly2 S2))
          by (apply (Permutation_in _ (Permutation_sym Hsw2)); apply in_or_app; left; exact HinN).
        destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR2 HinS2) as (_ & _ & _ & _ & _ & Hpw).
        apply (vi_dup_absurd _ _ _ _ Hpw Hsw2 HinN HinB). cbn [snd]. pose proof (Hpos _ Hin) as Hp0. cbn [snd] in Hp0.
        unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0); lia.
    + apply (HDnew a k); [apply (Permutation_in _ (Permutation_sym HDp)); apply in_or_app; right; exact Hin | exact Hin0].
  - eapply Permutation_trans; [exact Hsw2|]. unfold prhReader_ab in *. rewrite map_app, <- app_assoc.
    apply Permutation_app_head. exact Hbl.
  - rewrite Hfr. exact HFRp.
  - exact Hhp.
Qed.

(* ---- after grow returns (slot 6214): the branch of row 282 to the loop head, or rows 283 / 309 to the exit. The
   post of VrdIElem.tvrd_igrow_aP: the loop head keeps the element count of the call site's position P, and the
   memory invariant Pm holds at the memory reached ---- *)
Definition vi_post (Pm : (word -> option byte) -> Prop) (E : vrd_ient) (P : vrd_ipos) : world SEGS -> config -> Prop :=
  fun W3 c3 =>
    ((exists P', W3 = ip_W P' /\ c3 = vrd_cfg A_IELEM_SLOT P' /\ vrd_ielem_a B ARx SK E P' /\ ip_n P' = ip_n P) \/
     (exists P' res, W3 = ip_W P' /\ c3 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a B ARx SK E P' res)) /\
    Pm (ms_mem (cfg_ms c3)).

(* ==== THE POST-IMPLICATION CONJUNCTS ACROSS grow (A'Ledger; kit text PRH_FnReader.v blob fb7b12dfa169, PRH_FnParse.v
   blob 94232293d483). grow's arm lists prhPg_evs read requests with the instance's cf_head, the position's
   PresetReqAt.rd_hevs with the model's HEAD; they agree by the instance fact HI_head (the one spelling, discharged at
   the unit's top by reflexivity at CfParams_preset). The lemmas below compose grow's arm facts onto the position's:
   the transfer and the live requests over the trace so far then grow's arm trace, the live-count premises from the
   entry's along the call's all-granted trace, the OUTCOME at a refused arm, and the counter after a granted prefix. ==== *)
Hypothesis HI_head : cf_head = PresetReqAt.HEAD.

Lemma vi_ty6 : forall o : bool, ((if o then 6 else 5) =? 6) = o.
Proof. intros [|]; reflexivity. Qed.

(* grow's event list on an arm is rd_hevs of the model's grow trace on that arm's outcomes *)
Lemma vi_evs_arm : forall (o : bool) n cap okA, 0 <= n -> 0 <= cap ->
  prhPg_evs ((if o then 6 else 5) =? 6) n cap okA =
    PresetReqAt.rd_hevs (snd (fst (PjGrammar.grow o (Z.to_nat n) (Z.to_nat cap) okA))).
Proof. intros o n cap okA Hn Hc. rewrite vi_ty6. exact (prhPg_evs_model o n cap okA Hn Hc HI_head). Qed.

(* the peak count along events depends on the live list only up to order *)
Lemma vi_pkR_perm : forall f es s s', Permutation s s' -> PresetRun.pkR f s es = PresetRun.pkR f s' es.
Proof.
  intros f es. induction es as [|e r IH]; intros s s' H; cbn [PresetRun.pkR].
  - exact (PresetReqAt.cnt_perm f s s' H).
  - rewrite (PresetReqAt.cnt_perm f s s' H), (IH _ _ (PresetReqAtNoMiss.hstep_perm e s s' H)). reflexivity.
Qed.

(* a callee's live-count peak along its own events, below the call's along all of its events (PresetRun.pkR_app) *)
Lemma vi_pk_mid : forall f (S0 S1 : astate) (tr gtg rest : list ev),
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S1))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)) (PresetReqAt.rd_hevs tr)) ->
  (PresetRun.pkR f (PresetRoom.rs_live (YGcfRoom.room_of_cf S1)) (PresetReqAt.rd_hevs gtg) <=
   PresetRun.pkR f (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)) (PresetReqAt.rd_hevs (tr ++ gtg ++ rest)))%nat.
Proof.
  intros f S0 S1 tr gtg rest HP. rewrite (vi_pkR_perm f _ _ _ HP).
  unfold PresetReqAt.rd_hevs. rewrite !flat_map_app, !PresetRun.pkR_app. lia.
Qed.

(* the position transfer across a callee whose arm list is rd_hevs of its arm trace (VrdIElem.vrd_xfer_app) *)
Lemma vi_xfer_step : forall (S1 S2 S3 : astate) (t1 t2 : list ev) (E2 : list PresetReqAt.hev),
  E2 = PresetReqAt.rd_hevs t2 ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S1 ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs t1) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs t1))%nat H0 hist' S2) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S2 ->
     PRH_Base.prh_run_at sm x os i E2 ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length E2)%nat H0 hist' S3) ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist S1 ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (t1 ++ t2)) ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs (t1 ++ t2)))%nat H0 hist' S3.
Proof.
  intros S1 S2 S3 t1 t2 E2 -> H1 H2 sm x os i H0 hist HP HR.
  eapply vrd_xfer_app; [exact H1 | exact H2 | exact HP | exact HR].
Qed.

(* the live requests across a callee, the same way (VrdIElem.vrd_live_app) *)
Lemma vi_live_step : forall (S1 S2 S3 : astate) (t1 t2 : list ev) (E2 : list PresetReqAt.hev),
  E2 = PresetReqAt.rd_hevs t2 ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S1)) (PresetReqAt.rd_hevs t1)) ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S3))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) E2) ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S3))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S1)) (PresetReqAt.rd_hevs (t1 ++ t2))).
Proof. intros S1 S2 S3 t1 t2 E2 -> H1 H2. eapply vrd_live_app; [exact H1 | exact H2]. Qed.

(* THE HULL USE across a granted callee whose all-granted list is rd_hevs of the trace the position takes on
   (PresetHullBudget.hull_used_app over rd_hevs' split, hull_rd_app) *)
Lemma vi_hull_step : forall (S1 S2 S3 : astate) (t1 t2 : list ev) (E2 : list PresetReqAt.hev),
  E2 = PresetReqAt.rd_hevs t2 ->
  PresetHullBudget.hull_used S1 S2 (PresetReqAt.rd_hevs t1) -> PresetHullBudget.hull_used S2 S3 E2 ->
  PresetHullBudget.hull_used S1 S3 (PresetReqAt.rd_hevs (t1 ++ t2)).
Proof.
  intros S1 S2 S3 t1 t2 E2 -> H1 H2. rewrite PresetHullBudget.hull_rd_app.
  exact (PresetHullBudget.hull_used_app S1 S2 S3 _ _ H1 H2).
Qed.

(* THE HULL USE at an exit after a callee on ANY arm: the call's all-granted trace is the trace so far, the callee's
   granted trace, the rest, and the callee used at most its all-granted list (VrdIElem.vrd_huse_out) *)
Lemma vi_hull_exit : forall (S0 S1 S2 : astate) (tr gtg rest G : list ev) (Eg : list PresetReqAt.hev),
  G = tr ++ gtg ++ rest -> Eg = PresetReqAt.rd_hevs gtg ->
  PresetHullBudget.hull_used S0 S1 (PresetReqAt.rd_hevs tr) -> PresetHullBudget.hull_used S1 S2 Eg ->
  PresetHullBudget.hull_used S0 S2 (PresetReqAt.rd_hevs G).
Proof.
  intros S0 S1 S2 tr gtg rest G Eg -> -> H1 H2. rewrite !PresetHullBudget.hull_rd_app.
  exact (vrd_huse_out S0 S1 S2 _ _ _ H1 H2).
Qed.

(* ---- THE OUTCOME OF AN INJECTED READING AT A GROW (the text's conjunct at an exit after grow). Grow's events under the
   model's list from the position are a prefix of the continuation's (vi_inj_grow); with the chosen failure past
   grow's window, grow's events under that list are its all-granted ones (vi_pg_okk). ---- *)
Lemma vi_pg_okk : forall (o : bool) n cap j, 0 <= cap -> n = cap ->
  (PjGrammar.calls (prhPg_gtrace o n cap) <= j)%nat ->
  prhPg_evs ((if o then 6 else 5) =? 6) n cap (PresetReqAt.okk j) = prhPg_evs ((if o then 6 else 5) =? 6) n cap [].
Proof.
  intros o n cap j Hc -> Hj. rewrite vi_ty6. pose proof (vi_gtrace_charge o cap Hc) as (_ & Hg & _).
  rewrite Hg in Hj. unfold prhPg_evs. destruct (cap <? cap); [reflexivity|].
  destruct j as [|[|j]]; [destruct o; lia | destruct o; [lia | reflexivity] | reflexivity].
Qed.

Lemma vi_inj_grow : forall E P okt,
  ip_cont P = PjGrammar.jrl prh_jr_strtod (S (ip_f P)) (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P))
                (ip_acc P) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) ->
  0 <= ip_n P -> 0 <= ip_cap P ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat),
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (ip_cont P okt)))) ->
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (ip_cont P okt))))) ->
  PRH_Base.prh_run_at sm x os i (prhPg_evs ((if ie_o E then 6 else 5) =? 6) (ip_n P) (ip_cap P) okt) /\
  PRH_Base.prh_cons_from sm x os i (length (prhPg_evs ((if ie_o E then 6 else 5) =? 6) (ip_n P) (ip_cap P) okt)).
Proof.
  intros E P okt Hcont Hn Hc sm x os i HR HC.
  rewrite Hcont, vrd_jrl_unfold in HR, HC.
  lazymatch type of HR with context [PjGrammar.jbind ?m ?k okt] =>
    destruct (vrd_jbind_prefix _ _ m k okt) as (t2 & Et) end.
  rewrite Et in HR, HC. rewrite (vi_evs_arm (ie_o E) (ip_n P) (ip_cap P) okt Hn Hc).
  exact (vrd_run_prefix sm x os i _ _ HR HC).
Qed.


(* THE OUTCOME AT A CALLEE'S REFUSED ARM: a run of the call's all-granted events (the trace so far, the callee's
   granted trace, the rest), all consumer events, reaches the callee's entry at the position the trace so far gives
   (PRH_Base.prh_run_at_app_iff / prh_cons_from_app_iff), which the callee's exclusion refutes *)
Lemma vi_outcome_refused : forall (S0 S1 : astate) (tr gtg rest : list ev) (Eg : list PresetReqAt.hev),
  Eg = PresetReqAt.rd_hevs gtg ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs tr) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs tr))%nat H0 hist' S1) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S1 ->
     PRH_Base.prh_run_at sm x os i Eg -> PRH_Base.prh_cons_from sm x os i (length Eg) -> False) ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (tr ++ gtg ++ rest)) ->
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (tr ++ gtg ++ rest))) -> False.
Proof.
  intros S0 S1 tr gtg rest Eg -> HXF HEX sm x os i H0 hist HP HR HC.
  assert (Ha : PresetReqAt.rd_hevs (tr ++ gtg ++ rest) =
               PresetReqAt.rd_hevs tr ++ PresetReqAt.rd_hevs gtg ++ PresetReqAt.rd_hevs rest)
    by (unfold PresetReqAt.rd_hevs; rewrite !flat_map_app; reflexivity).
  rewrite Ha in HR, HC. rewrite !length_app in HC.
  apply PRH_Base.prh_run_at_app_iff in HR as [HR1 HR2].
  apply PRH_Base.prh_run_at_app_iff in HR2 as [HR2 _].
  apply PRH_Base.prh_cons_from_app_iff in HC as [_ HC].
  apply PRH_Base.prh_cons_from_app_iff in HC as [HC _].
  destruct (HXF sm x os i H0 hist HP HR1) as (h1 & Hh1).
  exact (HEX sm x os _ H0 h1 Hh1 HR2 HC).
Qed.

(* the counter and the failure index after a granted prefix (the steps so far refused nothing) *)
Lemma vi_lm_granted : forall Lam0 peak0 cnt0 fail0 ran0 most G tr D Lam peak cnt fail ran,
  rd_ledger_move Lam0 peak0 cnt0 fail0 ran0 most (repeat true (PjGrammar.calls tr)) G tr D Lam peak cnt fail ran ->
  0 <= cnt0 -> cnt0 + Z.of_nat (PjGrammar.calls tr) < 2 ^ 64 ->
  cnt = cnt0 + Z.of_nat (PjGrammar.calls tr) /\ fail = fail0.
Proof.
  intros Lam0 peak0 cnt0 fail0 ran0 most G tr D Lam peak cnt fail ran ((O1 & _ & _) & Hcnt & Hfa & _) Hc0 Hb.
  assert (Hno : forall i, (i < PjGrammar.calls tr)%nat -> cnt0 + Z.of_nat i <> fail0).
  { intros i Hi He. pose proof (O1 i Hi He) as Hf. rewrite nth_repeat_lt in Hf by exact Hi. discriminate. }
  split; [rewrite Hcnt; apply Z.mod_small; lia|].
  destruct Hfa as [_ Hf2]. apply Hf2. intros (Hlo & Hhi). apply (Hno (Z.to_nat (fail0 - cnt0))); lia.
Qed.

(* a refusal, as its two facts (PRH_Base.prh_refused) *)
Lemma vi_refused_at : forall ok cnt fail i, prh_refused ok cnt fail i = true ->
  nth i ok true = false /\ cnt + Z.of_nat i <> fail.
Proof.
  intros ok cnt fail i H. unfold prh_refused in H. apply andb_prop in H as [H1 H2].
  apply negb_true_iff in H1. apply negb_true_iff in H2. apply Z.eqb_neq in H2. exact (conj H1 H2).
Qed.

Lemma vi_refused_of : forall ok cnt fail i, nth i ok true = false -> cnt + Z.of_nat i <> fail ->
  prh_refused ok cnt fail i = true.
Proof.
  intros ok cnt fail i H1 H2. unfold prh_refused. rewrite H1. cbn [negb andb].
  apply negb_true_iff. apply Z.eqb_neq. exact H2.
Qed.

(* the refusal peak of grow's refused first realloc, and of its refused second one *)
Lemma vi_rpeak1 : forall cnt fail h r, cnt <> fail ->
  prh_refused_peak [false] cnt fail 1 (h :: r) = Z.max (Z.min SIZE_MAXZ h) 0.
Proof.
  intros cnt fail h r Hne. unfold prh_refused_peak. cbn [List.seq map fold_right nth].
  rewrite (vi_refused_of [false] cnt fail 0 eq_refl ltac:(lia)). reflexivity.
Qed.

Lemma vi_rpeak2 : forall cnt fail h0 h1 r, cnt + 1 <> fail ->
  prh_refused_peak [true; false] cnt fail 2 (h0 :: h1 :: r) = Z.max 0 (Z.max (Z.min SIZE_MAXZ h1) 0).
Proof.
  intros cnt fail h0 h1 r Hne. unfold prh_refused_peak. cbn [List.seq map fold_right nth].
  replace (prh_refused [true; false] cnt fail 0) with false by reflexivity.
  rewrite (vi_refused_of [true; false] cnt fail 1 eq_refl ltac:(lia)). reflexivity.
Qed.

(* THE CALL'S ALL-GRANTED TRACE at a jrl head: the trace so far, grow's granted trace, then the rest (the model's
   factorisation at okr = [], PjGrammar.agrees_jr_items on the granted prefix, vi_jrl_gsplit) *)
Lemma vi_gt_grow : forall d o x (okp : list bool) tr f n cap acc y (cont : PjGrammar.M (jv * list Z)),
  okp = repeat true (PjGrammar.calls tr) ->
  PjGrammar.jr_items prh_jr_strtod d o x (okp ++ []) =
    (fst (fst (cont [])), tr ++ snd (fst (cont [])), snd (cont [])) ->
  cont = PjGrammar.jrl prh_jr_strtod (S f) (S d) o (Z.to_nat n) (Z.to_nat cap) acc y ->
  0 <= n -> 0 <= cap ->
  exists rest, prhPi_gtrace d o x = tr ++ PRH_Charge.prhPg_gtrace o n cap ++ rest.
Proof.
  intros d o x okp tr f n cap acc y cont Hok Hf Hc Hn Hcap.
  rewrite app_nil_r in Hf.
  pose proof (PjGrammar.agrees_jr_items prh_jr_strtod d o x okp) as (HA & _).
  assert (HE := HA (fun k _ => eq_trans (f_equal (fun l => nth k l true) Hok) (vrd_nth_rep_true _ k))).
  rewrite Hf in HE. apply (f_equal (fun t => snd (fst t))) in HE. cbn [fst snd] in HE.
  subst cont.
  pose proof (vi_grow_granted o (Z.to_nat n) (Z.to_nat cap)) as HGG. rewrite !Z2Nat.id in HGG by assumption.
  rewrite (vi_jrl_gsplit _ _ _ _ _ _ _ _ _ HGG) in HE. cbn [fst snd] in HE.
  eexists. unfold prhPi_gtrace. rewrite <- HE. reflexivity.
Qed.

(* THE KIT'S CUT: the composed journal from the entry is at the position's budget ie_CW E (grow stores no wild trace: its
   two reallocs are code-only, PRH_FnParse.rd_pre's fixed pair, so the call rule's budget WS1 is []).
   THE RE-HIDING MOVE: grow's realloc re-hides, so both journals are at wle' SEGS RZ_cf and the runs after the call
   conclude SRr'. THE HULL: the loop head's use over its events so far composes grow's (vi_hull_step), an exit's use
   over the call's all-granted events follows on every arm (vi_hull_exit). *)
Lemma vi_igrow_post : forall (Pm : (word -> option byte) -> Prop) CTX E P W2 ly2 S2 Hp2 regs2 mem2 md2 k1,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_icomma_a B ARx SK E P ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    ly2 S2 Hp2 W2 mem2 md2 (ip_k P + k1) (ie_CW E) ->
  ajournal_xR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_grow + (144 + ie_e E))
    (spZ (ie_regs E) + ie_e E) (vi_gFP E P)
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) (ip_md P) [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, spZ (ie_regs E) - 144 <= a < spZ (ie_regs E) + ie_e E ->
     ~ inFP (vi_gFP E P) a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H (ip_W P)) (ip_mem P) a) ->
  (forall n, acallee_saved n -> getr regs2 (Z_to_bv 5 n) = getr (ip_regs P) (Z_to_bv 5 n)) ->
  vi_gpost E P ly2 S2 Hp2 W2 regs2 mem2 md2 -> Pm mem2 ->
  SRr' SEGS YGcfRehidePost.RZ_cf W2
    (mkCfg (@YK11.mkst (ip_fx P) regs2 (w64 (A_IPC A_IGROWRET_SLOT)) mem2 (YK11.seg_rom SEGS)) md2)
    (vi_post Pm E P).
Proof.
  intros Pm CTX E P W2 ly2 S2 Hp2 regs2 mem2 md2 k1 HEN HX HJc HJg HX2 HK HQ2 HPM2.
  pose proof HEN as HEN0.
  pose proof (vi_saved_of_iframe E P (proj1 HX)) as HSV.
  pose proof (proj1 (proj1 HX)) as Hsp.
  destruct HX as (HFR & HRG & HND & HCU & HJN & HMD & Hn & Hcnt4 & Hcont & HcapN & HNC & (af & HFO & HFL)).
  pose proof HJN as (HJ & HWIN & HFZ & HFK & HROD & HBM & HCH2).
  destruct HEN as ((HAFN & HROD0 & Hstkhi) & Hq & Hv & Ho & HRD & Hp & Hnth & HRM & HRP0 & HCTX & HUNIV & HCUR
    & HCHAIN & HQCH & HFCH & HCTX2 & Hfr & (HCW & HCWE & HWR & HHB)).
  pose proof HAFN as (HAR & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HRD as (_ & _ & _ & _ & Hinok & Hfwin & Hqlo & Hqhi & HRAq & Hsrc & Hhome & Hmaxrun & Hnode
    & Hqv & Htv & Hvwin & HLED0 & Hdmax & Hcntb).
  pose proof Hfwin as (He0 & He16 & Hetop & Hepres).
  pose proof HND as HND'. unfold vrd_inode in HND'. cbv beta zeta in HND'.
  destruct HND' as (Hhdr & Hncap & Hcap54 & Hcap0 & Hlin & Hlen & (Di & HDperm & Hrep) & Hrw & HRAv & HRAk
    & HRAy & Hkeys0).
  pose proof HCU as (Hinok1 & HRAq1 & Hsrc1 & Hhome1 & HLED & Hfrb & Hcnt2).
  pose proof HMD as (Hokp & Hfac & HLM & Hroom & Hfuel & Hbb & Hdep & Hlsum & HXF & HLV & HHU).
  pose proof HLM as (Hoks & Hcnt & Hfa & HLperm & Hsz & HnD & Hpeak).
  pose proof HBM as (HDnew & HABperm & HFRperm & Hhpk).
  pose proof (vi_stk_ge (ie_d E)) as HSTK.
  pose proof vi_stk_grow as HSTKg.
  pose proof HJ as (HARP & HlyP & _).
  pose proof HJc as (HARc2 & HlyE2 & _).
  pose proof HJg as (HARg & Hlyg & _ & _ & _ & Hfrsg & _ & _ & Fg1 & Fg2 & Fg3 & Fg4 & Hgoneg & Hpresg & _).
  pose proof (vrd_node_low B ARx HL LAWS CTX CTX0 CW E HEN0) as Hvceil.
  pose proof (@cf_head_nonneg cp) as Hcf0.
  (* the blocks the position owns *)
  assert (HarrD : forall b, In b (kids_blkR (ip_kids P) (ip_cap P) ++
                                  keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P)) -> In b (ip_D P)).
  { intros b Hin. apply (Permutation_in _ (Permutation_sym HDperm)). rewrite app_nil_l, app_assoc.
    apply in_or_app. left. exact Hin. }
  assert (HDiD : forall b, In b Di -> In b (ip_D P)).
  { intros b Hin. apply (Permutation_in _ (Permutation_sym HDperm)). rewrite app_nil_l.
    apply in_or_app. right. apply in_or_app. right. exact Hin. }
  assert (HDLam : forall a k, In (a, k) (ip_D P) -> In (a, k) (ip_Lam P)).
  { intros a k Hin. apply (Permutation_in _ (Permutation_sym HLperm)). apply in_or_app. left. exact Hin. }
  pose proof HLED as (_ & HNDL & _).
  destruct (vi_nodup_of (ip_Lam P) (ip_D P) (ie_Lam E) HNDL HLperm) as (HNDD & HNDfD & _).
  (* Di is apart from the arrays (other entries of the ledger) and from the node *)
  assert (HapP : pj_apartR (ip_D P) (ie_v E))
    by exact (vi_apart_node CTX E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEN0 HARP HlyP HBM HLED HLperm).
  assert (Hc0 : 0 < ip_cap P) by lia.
  assert (HkD : In (ip_kids P, 56 * ip_cap P) (ip_D P)).
  { apply HarrD. apply in_or_app. left. unfold kids_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). left. reflexivity. }
  assert (HyD : ie_o E = true -> In (ip_keys P, 8 * ip_cap P) (ip_D P)).
  { intros Ho6. apply HarrD. apply in_or_app. right. unfold keys_blkR. rewrite Ho6.
    rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). left. reflexivity. }
  assert (HDiarr : forall a k, In (a, k) Di -> a <> ip_kids P /\ (ie_o E = true -> a <> ip_keys P)).
  { intros a k Hin. pose proof HDperm as Hp'. rewrite app_nil_l in Hp'.
    assert (HN : NoDup (map fst (kids_blkR (ip_kids P) (ip_cap P) ++
                     keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ Di))).
    { apply NoDup_ListNoDup. apply NoDup_ListNoDup in HNDfD.
      exact (Permutation_NoDup (Permutation_map fst Hp') HNDfD). }
    apply NoDup_ListNoDup in HN. rewrite !map_app in HN.
    unfold kids_blkR, keys_blkR in HN. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in HN. cbn [orb] in HN.
    split.
    - intros ->. cbn [map fst app] in HN. apply List.NoDup_cons_iff in HN as [Hn1 _]. apply Hn1.
      apply in_or_app. right. apply in_map_iff. exists (ip_kids P, k). split; [reflexivity | exact Hin].
    - intros Ho6 ->. rewrite Ho6 in HN. cbn [negb Z.eqb Pos.eqb map fst app] in HN.
      apply List.NoDup_cons_iff in HN as [_ HN]. apply List.NoDup_cons_iff in HN as [Hn1 _]. apply Hn1.
      apply in_map_iff. exists (ip_keys P, k). split; [reflexivity | exact Hin]. }
  (* every byte grow may write is below alloc_ceiling *)
  assert (HFP1low : forall a, inFP (vi_gFP E P) a -> 4096 <= a < alloc_ceiling).
  { intros a (r & Hin & Hr). unfold vi_gFP in Hin. apply in_app_or in Hin as [Hin | Hin].
    - pose proof Hnode as (Hv4096 & _). cbn [In] in Hin. destruct Hin as [<- | [<- | []]]; cbn [fst snd] in Hr; lia.
    - unfold ablocks_fp, prhReader_ab in Hin. rewrite map_map in Hin.
      apply in_map_iff in Hin as ((bb & kk) & Heq & Hinb). subst r. cbn [fst snd] in Hr.
      destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ bb kk _ _ HLED (HDLam _ _ (HarrD _ Hinb))) as (_ & Hab0 & _).
      destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HARP Hab0) as (_ & _ & Hc1 & Happ & _).
      unfold in_app in Happ. lia. }
  (* the blocks of Di miss the footprint *)
  assert (HDiFP : forall b x, In b Di -> pj_holdsR b x -> ~ inFP (vi_gFP E P) x).
  { intros [a0 k0] x Hin Hx (r & Hinr & Hr). pose proof (HDiD _ Hin) as HinD.
    unfold vi_gFP in Hinr. apply in_app_or in Hinr as [Hinr | Hinr].
    - apply (HapP (a0, k0) x HinD Hx).
      cbn [In] in Hinr. destruct Hinr as [<- | [<- | []]]; cbn [fst snd] in Hr; lia.
    - unfold ablocks_fp, prhReader_ab in Hinr. rewrite map_map in Hinr.
      apply in_map_iff in Hinr as ((bb & kk) & Heq & Hinb). subst r. cbn [fst snd] in Hr.
      unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
      assert (Hne : a0 <> bb).
      { apply in_app_or in Hinb as [Hinb | Hinb].
        - unfold kids_blkR in Hinb. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in Hinb.
          destruct Hinb as [Heq | []]. injection Heq as <- _. exact (proj1 (HDiarr _ _ Hin)).
        - unfold keys_blkR in Hinb. destruct (ie_o E) eqn:Eo; cbn [negb Z.eqb Pos.eqb orb] in Hinb;
            [|rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in Hinb; destruct Hinb].
          rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in Hinb. cbn [orb] in Hinb.
          destruct Hinb as [Heq | []]. injection Heq as <- _. exact (proj2 (HDiarr _ _ Hin) eq_refl). }
      destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ bb kk _ _ HLED (HDLam _ _ (HarrD _ Hinb))) as (Hkk & _).
      exact (vi_lam_disj _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 bb kk x HARP HLED (HDLam _ _ HinD) (HDLam _ _ (HarrD _ Hinb))
               Hne Hx Hr). }
  assert (Hspc : alloc_ceiling <= spZ (ie_regs E) - 144) by lia.
  (* every byte at or above the loop's sp is the position's *)
  assert (HKup : forall a, spZ (ie_regs E) - 144 <= a < 2 ^ 64 ->
             aview SEGS (w_H W2) mem2 a = aview SEGS (w_H (ip_W P)) (ip_mem P) a).
  { intros a Ha. destruct (Z_lt_le_dec a (spZ (ie_regs E) + ie_e E)) as [Hlt | Hge].
    - apply HX2; [lia|]. intros Hin. pose proof (HFP1low a Hin). lia.
    - apply Fg1; lia. }
  assert (Hsp2 : spZ regs2 = spZ (ie_regs E) - 144).
  { unfold spZ. change (getr regs2 2) with (getr regs2 (Z_to_bv 5 2)).
    rewrite (HK 2 ltac:(unfold acallee_saved; lia)). exact Hsp. }
  assert (HSV2 : vi_saved W2 mem2 (ie_regs E)).
  { intros j Hj. apply (vi_vm_aview (w_H (ip_W P)) (w_H W2) (ip_mem P) mem2); [|exact (HSV j Hj)].
    intros k Hk. apply HKup. lia. }
  (* the call keep (lib/A/VrdCallKeep.v), at the state grow returns *)
  set (P2 := MkIPos (ip_fx P) ly2 S2 Hp2 W2 regs2 mem2 md2 (ip_k P + k1) (ip_n P) (ip_cap P) (ip_kids P)
               (ip_keys P) (ip_p P) (ip_acc P) (ip_f P) (ip_cont P) (ip_ok P) (ip_tr P) (ip_D P) (ip_Lam P)
               (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P)).
  destruct (vrd_call_keep B ARx SK LAWS H_pst_ro CTX CTX0 CW E P P2 (STK_grow + (144 + ie_e E)) (vi_gFP E P) k1 []
              H_img H_s0p HEN0 HFR HJN ltac:(intros a Ha; right; right; exact (HFP1low a Ha)) HJg HX2
              ltac:(cbn [ip_regs P2]; rewrite Hsp2, Hsp; reflexivity))
    as (CK1 & CK2 & CK3 & CK4 & _).
  (* the q words, the frame words and every byte from the loop's sp up are the position's at the new state *)
  assert (Hpres2 : forall a, spZ (ie_regs E) - STK_parse_items (ie_d E) <= a < spZ (ie_regs E) + ie_e E ->
             apresent (w_H W2) mem2 a).
  { pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpc & _). intros a Ha. apply Hpc. lia. }
  assert (Hin_ok2 : forall p, pj_in_okR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (ie_q E) (ie_text E) (ie_len E) p
                      (Z.of_nat (ie_d E) + 1) (ie_tb E) ->
                    src_rd W2 mem2 (ie_text E) (ie_tb E) ->
                    pj_in_okR SEGS (mrestrict (w_H W2) mem2) (ie_q E) (ie_text E) (ie_len E) p
                      (Z.of_nat (ie_d E) + 1) (ie_tb E)).
  { intros p (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12) (Hby2 & _).
    assert (KV : forall a (n : nat) vv, ie_q E <= a -> a + Z.of_nat n <= ie_q E + 24 ->
       val_mem SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) a n vv -> val_mem SEGS (mrestrict (w_H W2) mem2) a n vv).
    { intros a n vv Ha1 Ha2 Hvv. apply (vi_vm_aview (w_H (ip_W P)) (w_H W2) (ip_mem P) mem2); [|exact Hvv].
      intros k Hk. apply HKup. lia. }
    split; [apply KV; [lia | cbn; lia | exact I1]|].
    split; [apply KV; [lia | cbn; lia | exact I2]|].
    split; [apply KV; [lia | cbn; lia | exact I3]|].
    split; [intros x Hx; apply apresent_writable; apply Hpres2; lia|].
    split; [exact I5|]. split; [exact I6|]. split; [exact I7|]. split; [exact I8|]. split; [exact I9|].
    split; [exact Hby2 | split; [exact I11 | exact I12]]. }
  (* arm-independent model facts *)
  assert (Hdlt : (ie_d E < PjGrammar.MAXD)%nat).
  { pose proof Hinok1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd32). unfold PjGrammar.MAXD. lia. }
  assert (HMX : (PjGrammar.MAXD - ie_d E)%nat = S (PjGrammar.MAXD - S (ie_d E))) by lia.
  assert (Hrest0 : rest_atR (ie_tb E) (ie_text E) (ie_p E) =
                   (if ie_o E then 123 else 91) :: skipn (S (Z.to_nat (ie_p E - ie_text E))) (ie_tb E))
    by (unfold rest_atR; apply vi_skipn_nth; exact Hnth).
  assert (HM : forall okt r t ok2, PjGrammar.jrl prh_jr_strtod (S (ip_f P)) (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P))
                 (Z.to_nat (ip_cap P)) (ip_acc P) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) okt = (r, t, ok2) ->
               PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))
                 (ip_ok P ++ okt) = (r, ip_tr P ++ t, ok2)).
  { intros okt r t ok2 Hj. rewrite Hfac, Hcont, Hj. reflexivity. }
  assert (HTB : forall okt r t1 t ok2, PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E)
                  (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P ++ okt) = (r, (ip_tr P ++ t1) ++ t, ok2) ->
       ie_cnt E + Z.of_nat (PjGrammar.calls (ip_tr P) + PjGrammar.calls t1) < 2 ^ 64 - 1 /\
       hpeakR (ip_tr P ++ t1) <= 224 * Z.of_nat (length (rest_atR (ie_tb E) (ie_text E) (ie_p E))) +
                                  512 * Z.of_nat (PjGrammar.MAXD - ie_d E)).
  { intros okt r t1 t ok2 Hj. pose proof Hj as Hj'. rewrite Hrest0 in Hj'.
    destruct (vi_trace_bounds _ _ _ _ _ _ _ _ _ Hj') as (Hc1 & Hh1). rewrite <- Hrest0 in Hc1, Hh1.
    rewrite PjGrammar.calls_app in Hc1. split; lia. }
  pose proof HLM as HLM'. rewrite Hokp in HLM'.
  assert (Hcnt0 : 0 <= ie_cnt E)
    by (pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLED0) as (_ & _ & Hc & _); lia).
  pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLED) as ((HLs0 & Hpkge) & _ & HcntP & _).
  (* the call's all-granted trace: the trace so far, grow's granted trace, the rest; grow's granted events *)
  destruct (vi_gt_grow (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P) (ip_tr P) (ip_f P)
              (ip_n P) (ip_cap P) (ip_acc P) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) (ip_cont P) Hokp (Hfac []) Hcont
              ltac:(lia) ltac:(lia)) as (grest & HGs).
  assert (EeG : prhPg_evs ((if ie_o E then 6 else 5) =? 6) (ip_n P) (ip_cap P) [] =
                PresetReqAt.rd_hevs (PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P)))
    by (rewrite (vi_evs_arm (ie_o E) (ip_n P) (ip_cap P) [] ltac:(lia) ltac:(lia)); reflexivity).
  pose proof (proj1 (Hlin Hc0)) as HkL0.
  assert (HpresK : forall y, ip_kids P <= y < ip_kids P + 56 * ip_cap P -> apresent (w_H (ip_W P)) (ip_mem P) y)
    by (intros y Hy; exact (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ y HARP HLED HkL0 Hy)).
  assert (HpresY : ie_o E = true -> forall y, ip_keys P <= y < ip_keys P + 8 * ip_cap P ->
                     apresent (w_H (ip_W P)) (ip_mem P) y)
    by (intros Ho6 y Hy; exact (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ y HARP HLED (proj2 (Hlin Hc0) Ho6) Hy)).
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED HkL0) as (_ & _ & _ & Hk16' & _).
  assert (Hdep' : Forall (fun mm => (PjTree.depth (snd mm) <= PjGrammar.MAXD - S (ie_d E))%nat) (rev (ip_acc P)))
    by (apply Forall_rev; exact Hdep).
  assert (HDp0 : Permutation (ip_D P) ([(ip_kids P, 56 * ip_cap P)] ++
                   keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ Di)).
  { rewrite app_nil_l in HDperm. unfold kids_blkR in HDperm. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in HDperm.
    exact HDperm. }
  assert (HDiKeep : forall (W' : world SEGS) mem' ly' S' Hp' md' k' Lam' peak' cnt' fail' ran' most' own',
     ajournal_xR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_grow + (144 + ie_e E))
       (spZ (ie_regs E) + ie_e E) (vi_gFP E P)
       (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) (ip_md P) [] ly' S' Hp' W' mem' md' k' ->
     prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most' own' -> (forall b, In b Di -> In b Lam') ->
     rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H W') mem') (rd_blk Di)).
  { intros W' mem' ly' S' Hp' md' k' Lam' peak' cnt' fail' ran' most' own' HJ' HL' HDi'.
    eapply vi_keep_blocks; [exact HJ' | exact HLED | exact HL' | | exact HDiFP].
    intros [x k] Hin. split; [exact (HDLam x k (HDiD _ Hin)) | exact (HDi' _ Hin)]. }
  assert (HDiApK : forall b x, In b Di -> pj_holdsR b x ->
                     ~ (ip_kids P <= x < ip_kids P + 56 * Z.of_nat (length (ip_acc P)))).
  { intros [a0 k0] x Hin Hx Hx'. unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
    apply (vi_lam_disj _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 (ip_kids P) (56 * ip_cap P) x HARP HLED
             (HDLam _ _ (HDiD _ Hin)) HkL0 (proj1 (HDiarr _ _ Hin)) Hx).
    unfold req_size. destruct (Z.eqb_spec (56 * ip_cap P + cf_head) 0); lia. }
  assert (HX3 : forall regs', getr regs' (Z_to_bv 5 3) = getr regs2 (Z_to_bv 5 3) -> getr regs' 3 = w64 (as_gp B)).
  { intros regs' E3. change (getr regs' 3) with (getr regs' (Z_to_bv 5 3)). rewrite E3.
    rewrite (HK 3 ltac:(unfold acallee_saved; lia)). exact (proj1 HRG). }
  assert (HX4 : forall regs', getr regs' (Z_to_bv 5 4) = getr regs2 (Z_to_bv 5 4) -> getr regs' 4 = w64 (as_tp B)).
  { intros regs' E4. change (getr regs' 4) with (getr regs' (Z_to_bv 5 4)). rewrite E4.
    rewrite (HK 4 ltac:(unfold acallee_saved; lia)). exact (proj1 (proj2 HRG)). }
  assert (HXsp : forall regs', getr regs' (Z_to_bv 5 2) = getr regs2 (Z_to_bv 5 2) -> spZ regs' = spZ regs2).
  { intros regs' E2. unfold spZ. change (getr regs' 2) with (getr regs' (Z_to_bv 5 2)).
    change (getr regs2 2) with (getr regs2 (Z_to_bv 5 2)). rewrite E2. reflexivity. }
  unfold vi_gpost, tgrP_Q in HQ2. cbv zeta in HQ2.
  destruct HQ2 as (Hrl2 & Hhu2 & Hbb2 & [A1 | [A2 | [A3 | [A4 | [A5 | [A6 | A7]]]]]]).
  - (* ARM 1: room left, grow did nothing -> the loop head *)
    destruct A1 as (Hnlt & Ha0 & EHp & Eab & _ & HLED2 & Hhdr2 & Hkeep2 & HLV2 & HXF2).
    (* no allocator call on this arm: grow's list is empty *)
    assert (Ee1 : prhPg_evs ((if ie_o E then 6 else 5) =? 6) (ip_n P) (ip_cap P) [] = PresetReqAt.rd_hevs [])
      by (unfold prhPg_evs; rewrite (proj2 (Z.ltb_lt _ _) Hnlt); reflexivity).
    apply (vi_run_head (ip_fx P) E W2 ly2 S2 Hp2 regs2 mem2 md2 (ip_k P + k1) (vi_post Pm E P) Hsp2 ltac:(lia) ltac:(lia)
             HSV2 ltac:(change (getr regs2 (Z_to_bv 5 10)) with (getr regs2 10); exact Ha0) HJc).
    intros regs' md' HKr HJc'. split; [|exact HPM2]. left.
    set (rest := rest_atR (ie_tb E) (ie_text E) (ip_p P)) in *.
    set (cont' := vrd_jtail (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P) rest).
    assert (Hceq : forall okr, ip_cont P okr = cont' okr).
    { intros okr. rewrite Hcont, vrd_jrl_unfold. unfold PjGrammar.grow.
      rewrite (proj2 (Nat.ltb_lt (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P))) ltac:(lia)).
      unfold PjGrammar.jbind, PjGrammar.jret. cbv beta iota. unfold cont'.
      destruct (vrd_jtail _ _ _ _ _ _ _ okr) as [[r t] o2]. reflexivity. }
    exists (MkIPos (ip_fx P) ly2 S2 Hp2 W2 regs' mem2 md' (ip_k P + k1) (ip_n P) (ip_cap P) (ip_kids P)
              (ip_keys P) (ip_p P) (ip_acc P) (ip_f P) cont' (ip_ok P) (ip_tr P) (ip_D P) (ip_Lam P)
              (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P)).
    split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
    assert (HKr' : forall n, In n vi_kregs -> getr regs' (Z_to_bv 5 n) = getr (ip_regs P) (Z_to_bv 5 n))
      by (intros n Hkn; rewrite (HKr n Hkn); exact (HK n (vi_kregs_cs n Hkn))).
    assert (Hsp' : spZ regs' = spZ regs2).
    { unfold spZ. change (getr regs' 2) with (getr regs' (Z_to_bv 5 2)).
      change (getr regs2 2) with (getr regs2 (Z_to_bv 5 2)). rewrite (HKr 2 ltac:(cbn [vi_kregs In]; tauto)).
      reflexivity. }
    assert (HBM' : rd_blocks_move B (ie_ly E) (ie_S E) ly2 S2 (ip_D P) (ip_tr P)
                     (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ie_d E)).
    { split; [exact HDnew|]. split; [rewrite Eab; exact HABperm|]. split; [rewrite Hfrsg; exact HFRperm | exact Hhpk]. }
    destruct (vrd_icur_after_call CTX CTX0 CW E ly2 S2 Hp2 W2 mem2 md' (ip_k P + k1) (ip_D P) (ip_tr P) (ip_Lam P)
                _ _ _ _ _ _ HEN0 HJc' HBM' HLED2 HLperm) as (Hsrc2 & Hhome2 & HRAq2).
    pose proof (vrd_node_ra_after_call CTX CTX0 CW E ly2 S2 Hp2 W2 mem2 md' (ip_k P + k1) (ip_D P) (ip_tr P)
                  (ip_Lam P) _ _ _ _ _ _ HEN0 HJc' HBM' HLED2 HLperm) as HRAv2.
    assert (Hbb0 : blocks_bytes S2 <= blocks_bytes (ip_S P)).
    { rewrite (vi_blocks_bytes_lsum ly2 S2), (vi_blocks_bytes_lsum (ip_ly P) (ip_S P)), Eab. lia. }
    pose proof (proj1 (Hlin Hc0)) as HkL.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED HkL) as (_ & _ & _ & Hk16 & _).
    assert (HkFP : forall x, ip_kids P <= x < ip_kids P + 56 * ip_cap P ->
              aview SEGS (w_H W2) mem2 x = aview SEGS (w_H (ip_W P)) (ip_mem P) x).
    { intros x Hx. apply (Hkeep2 (ip_kids P - cf_head) (ip_kids P - cf_head + req_size (56 * ip_cap P + cf_head))).
      - unfold ablocks_fp, prhReader_ab. rewrite map_map. apply in_map_iff. exists (ip_kids P, 56 * ip_cap P).
        split; [reflexivity|]. apply in_or_app. left. unfold kids_blkR.
        rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). left. reflexivity.
      - unfold req_size. destruct (Z.eqb_spec (56 * ip_cap P + cf_head) 0); lia. }
    assert (HyFP : ie_o E = true -> forall x, ip_keys P <= x < ip_keys P + 8 * ip_cap P ->
              aview SEGS (w_H W2) mem2 x = aview SEGS (w_H (ip_W P)) (ip_mem P) x).
    { intros Ho6 x Hx. apply (Hkeep2 (ip_keys P - cf_head) (ip_keys P - cf_head + req_size (8 * ip_cap P + cf_head))).
      - unfold ablocks_fp, prhReader_ab. rewrite map_map. apply in_map_iff. exists (ip_keys P, 8 * ip_cap P).
        split; [reflexivity|]. apply in_or_app. right. unfold keys_blkR. rewrite Ho6.
        rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). left. reflexivity.
      - unfold req_size. destruct (Z.eqb_spec (8 * ip_cap P + cf_head) 0); lia. }
    split.
    { apply (vi_iframe_sp E P2); [exact CK1 | exact Hsp' | reflexivity | reflexivity]. }
    split.
    { apply (vi_iregs_keep E P _ HRG). exact HKr'. }
    split.
    { unfold vrd_inode. cbv zeta. cbn [ip_W ip_mem ip_n ip_cap ip_kids ip_keys ip_Lam ip_acc ip_D].
      split; [exact Hhdr2|]. split; [lia|]. split; [exact Hcap54|]. split; [exact Hcap0|]. split; [exact Hlin|].
      split; [exact Hlen|].
      split.
      { exists Di. split; [exact HDperm|].
        apply (vi_sub_move (ie_o E) _ _ _ _ (ip_kids P) (ip_keys P) (ip_kids P) (ip_keys P) (ip_acc P) Di Hrep).
        - intros x k _ Hb. exact Hb.
        - eapply vi_keep_blocks; [exact HJg | exact HLED | exact HLED2 | | exact HDiFP].
          intros [x k] Hin. pose proof (HDLam x k (HDiD _ Hin)). split; assumption.
        - intros x Hx. apply prh_mbyte_of_aview. apply HkFP. lia.
        - intros x Hx. apply apresent_writable.
          apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ (ip_kids P) (56 * ip_cap P) _ HARg HLED2 HkL). lia.
        - lia.
        - intros Ho6 x Hx. apply prh_mbyte_of_aview. apply (HyFP Ho6). lia.
        - intros [a0 k0] x Hin Hx Hx'. unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
          apply (vi_lam_disj _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 (ip_kids P) (56 * ip_cap P) x HARP HLED
                   (HDLam _ _ (HDiD _ Hin)) HkL (proj1 (HDiarr _ _ Hin)) Hx).
          unfold req_size. destruct (Z.eqb_spec (56 * ip_cap P + cf_head) 0); lia. }
      split.
      { intros x Hx. apply apresent_writable.
        apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ (ip_kids P) (56 * ip_cap P) _ HARg HLED2 HkL). lia. }
      split; [exact HRAv2|].
      split; [intros _; exact (proj1 (vrd_lam_shadow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HkL))|].
      split; [intros Ho6 _; exact (proj1 (vrd_lam_shadow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 (proj2 (Hlin Hc0) Ho6)))|].
      exact Hkeys0. }
    split.
    { unfold vrd_icur. cbv zeta. cbn [ip_W ip_mem ip_p ip_S ip_ly ip_Hp ip_Lam ip_peak ip_cnt ip_fail ip_ran].
      split; [exact (Hin_ok2 (ip_p P) Hinok1 Hsrc2)|].
      split; [exact HRAq2|]. split; [exact Hsrc2|]. split; [exact Hhome2|]. split; [exact HLED2|].
      split; [rewrite Hfrsg; exact Hfrb | exact Hcnt2]. }
    split.
    { split; [exact HJc'|]. split; [exact CK2|]. split; [exact HFZ|]. split; [exact HFK|]. split; [exact CK3|].
      split; [exact HBM'|]. exact CK4. }
    split.
    { split; [exact Hokp|].
      split; [intros okr; cbn [ip_ok ip_tr ip_cont]; rewrite Hfac, Hceq; reflexivity|].
      split; [exact HLM|].
      split.
      { cbn [ip_S ip_cont]. rewrite <- (Hceq []).
        exact (vi_room_after (ip_S P) S2 [] _ Hroom Hrl2 ltac:(rewrite <- Ee1; exact HLV2)). }
      split; [exact Hfuel|].
      split; [cbn [ip_S ip_tr]; lia|].
      split; [exact Hdep|]. split; [exact Hlsum|].
      split; [pose proof (vi_xfer_step _ _ _ (ip_tr P) [] _ Ee1 HXF HXF2) as HXF3; rewrite app_nil_r in HXF3;
              exact HXF3|].
      pose proof (vi_live_step _ _ _ (ip_tr P) [] _ Ee1 HLV HLV2) as HLV3. rewrite app_nil_r in HLV3.
      split; [exact HLV3|].
      pose proof (vi_hull_step _ _ _ (ip_tr P) [] _ Ee1 HHU Hhu2) as HHU3. rewrite app_nil_r in HHU3. exact HHU3. }
    split; [exact Hnlt|]. split; [reflexivity|].
    (* THE BATCH KIT'S LAYER: nothing moved, the caps and the order list ride the keep of the slots and of Di *)
    assert (HSK : vi_subkeep (ie_o E) (rdW (ip_W P) (ip_mem P)) (rdW W2 mem2) (prh_lin (ip_Lam P))
                    (ip_kids P) (ip_keys P) (ip_kids P) (ip_keys P) (ip_acc P) Di).
    { split; [intros x k Hin; exact (HDLam x k (HDiD _ Hin))|].
      split; [apply (HDiKeep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg HLED2); intros [x k] Hin; exact (HDLam x k (HDiD _ Hin))|].
      split; [intros x Hx; apply prh_mbyte_of_aview; apply HkFP; lia|].
      split; [intros x Hx; apply apresent_writable;
              apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ (ip_kids P) (56 * ip_cap P) _ HARg HLED2 HkL); lia|].
      split; [lia|].
      split; [intros Ho6 x Hx; apply prh_mbyte_of_aview; apply (HyFP Ho6); lia|].
      exact HDiApK. }
    split; [exact (vi_ncap_lt (ip_n P) (ip_cap P) ltac:(lia) HcapN)|].
    split; [eapply (vi_incaps_step E P _ Di HNC); [reflexivity | exact Hrep | exact HSK]|].
    exists af. split.
    { eapply (vi_iforder_step E P _ af Di HFO); [reflexivity | reflexivity | exact Hlen | exact HDperm | exact HDperm
                                                | exact HSK]. }
    intros okr. cbn [ip_ok ip_f ip_n ip_cap ip_p].
    pose proof (vi_fl_granted _ _ _ (ip_ok P) (ip_f P) _ _ af _ [] (Z.to_nat (ip_cap P)) [] HFL
                  ltac:(intros okr'; exact (vi_grow_lt (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) okr'
                                                       ltac:(lia))) okr) as HFL'.
    rewrite app_nil_r in HFL'. exact HFL'.
  - (* ARM 2: the kids realloc is the one set to fail (cnt = fail) -> the exit with -1 *)
    destruct A2 as (Hnc & Hcf & Ha0 & EHp & Eab & _ & HLED2 & Hhdr2 & Hkb2 & Hyb2 & HLV2 & HXF2).
    set (cN := Z.to_nat (ip_cap P)) in *.
    assert (HcN : (0 < cN)%nat) by lia.
    assert (HnN : Z.to_nat (ip_n P) = cN) by (unfold cN; rewrite Hnc; reflexivity).
    set (trR := [PjGrammar.EFail (56 * (2 * cN))]).
    (* grow's events on this arm, and its granted trace's calls *)
    assert (Ee2 : prhPg_evs ((if ie_o E then 6 else 5) =? 6) (ip_n P) (ip_cap P) [false] = PresetReqAt.rd_hevs trR).
    { rewrite (vi_evs_arm (ie_o E) (ip_n P) (ip_cap P) [false] ltac:(lia) ltac:(lia)), HnN.
      change (Z.to_nat (ip_cap P)) with cN. rewrite (vi_grow_no1 (ie_o E) cN [] HcN). reflexivity. }
    assert (HgC : (1 <= PjGrammar.calls (PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P)))%nat).
    { rewrite Hnc. pose proof (vi_gtrace_charge (ie_o E) (ip_cap P) ltac:(lia)) as (_ & Hg & _). rewrite Hg.
      destruct (ie_o E); lia. }
    assert (Hj2 : PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))
                    (ip_ok P ++ [false]) = (None, ip_tr P ++ trR, [])).
    { apply HM. rewrite vrd_jrl_unfold, HnN. unfold PjGrammar.jbind at 1. rewrite vi_grow_no1 by exact HcN.
      reflexivity. }
    destruct (HTB [false] None trR [] [] ltac:(rewrite app_nil_r; exact Hj2)) as (Hcb & Hhb).
    assert (HBM2 : rd_blocks_move B (ie_ly E) (ie_S E) ly2 S2 (ip_D P) (ip_tr P ++ trR)
                     (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ie_d E)).
    { split; [exact HDnew|]. split; [rewrite Eab; exact HABperm|]. split; [rewrite Hfrsg; exact HFRperm | exact Hhb]. }
    apply (vi_run_exit (ip_fx P) E W2 ly2 S2 Hp2 regs2 mem2 md2 (ip_k P + k1) (vi_post Pm E P) Hsp2 ltac:(lia) ltac:(lia)
             HSV2 ltac:(change (getr regs2 (Z_to_bv 5 10)) with (getr regs2 10); exact Ha0) HJc).
    intros regs' md' HKx H18 HJc'. split; [|exact HPM2]. right.
    destruct (vrd_icur_after_call CTX CTX0 CW E ly2 S2 Hp2 W2 mem2 md' (ip_k P + k1) (ip_D P) (ip_tr P ++ trR)
                (ip_Lam P) _ _ _ _ _ _ HEN0 HJc' HBM2 HLED2 HLperm)
      as (Hsrc2 & _ & _).
    exists (MkIPos (ip_fx P) ly2 S2 Hp2 W2 regs' mem2 md' (ip_k P + k1) (ip_n P) (ip_cap P) (ip_kids P)
              (ip_keys P) (ip_p P) (ip_acc P) (ip_f P) (fun okr => (None, [], okr)) (ip_ok P ++ [false])
              (ip_tr P ++ trR) (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P + 1) SIZE_MAXZ (ip_ran P)), (-1).
    split; [reflexivity|]. split; [reflexivity|].
    pose proof (HXsp regs' (HKx 2 ltac:(cbn [vi_xregs In]; tauto))) as Hsp'.
    split. { apply (vi_iframe_sp E P2); [exact CK1 | exact Hsp' | reflexivity | reflexivity]. }
    split.
    { split; [exact HJc'|]. split; [exact CK2|]. split; [exact HFZ|]. split; [exact HFK|]. split; [exact CK3|].
      split; [exact HBM2|]. exact CK4. }
    split; [exact (HX3 regs' (HKx 3 ltac:(cbn [vi_xregs In]; tauto)))|].
    split; [exact (HX4 regs' (HKx 4 ltac:(cbn [vi_xregs In]; tauto)))|].
    split; [exact H18|]. split; [right; reflexivity|].
    split; [exact HLED2|]. split; [exact Hrl2|].
    split; [exact (vi_xfer_step _ _ _ (ip_tr P) trR _ Ee2 HXF HXF2)|].
    split.
    { (* the kids realloc was the chosen failure: no run meets the clause's counter premise *)
      intros sm x os i H0 hist _ _ _ Hf. exfalso.
      destruct (vi_lm_granted _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLM' Hcnt0 ltac:(lia)) as (Ecnt & Efail).
      rewrite HGs, !PjGrammar.calls_app in Hf. clear -Hf Ecnt Efail Hcf HgC Hcnt0. lia. }
    split.
    { cbn [ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran]. rewrite Hokp.
      eapply (vi_lm_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P)) _ grest);
        [exact HLM' | exact Hlsum | cbn [trR PjGrammar.calls PjGrammar.is_call]; lia | exact Hcnt0
        | reflexivity | | | | exact HLperm | exact Hsz | | | exact HGs | ].
      - split; [|split].
        + intros i Hi _. assert (i = 0%nat) by (cbn in Hi; lia). subst i. reflexivity.
        + left. reflexivity.
        + intros i Hi Hf _. exfalso. apply vi_refused_at in Hf as [_ Hf]. apply Hf.
          assert (i = 0%nat) by (cbn in Hi; lia). subst i. lia.
      - cbn. lia.
      - split; [intros _; reflexivity | intros Hno; exfalso; apply Hno; cbn; lia].
      - cbn [nliveR nlive_evR trR]. lia.
      - rewrite prh_refused_peak_granted.
        + cbn [hpeakR trR PjGrammar.held_ev]. clear -Hpkge HLs0. lia.
        + intros i Hi _. assert (i = 0%nat) by (cbn in Hi; lia). subst i. lia.
      - cbn [trR PjGrammar.calls PjGrammar.is_call]. exact HgC. }
    split.
    { cbn [ip_S ip_tr]. rewrite vi_prh_held_app.
      assert (Hh0 : prh_held trR = cf_head) by (unfold prh_held, trR; cbn; lia).
      rewrite (vi_blocks_bytes_lsum ly2 S2), Eab, <- (vi_blocks_bytes_lsum (ip_ly P) (ip_S P)). lia. }
    split.
    { cbn [ip_D ip_tr]. rewrite vi_held_app. cbn [trR PjGrammar.held PjGrammar.held_ev]. lia. }
    split; [|split; [exact (vi_live_step _ _ _ (ip_tr P) trR _ Ee2 HLV HLV2)
                    |split; [exact (vi_hull_exit _ _ _ (ip_tr P) _ grest _ _ HGs EeG HHU Hhu2)|]]].
    2: { (* THE OUTCOME OF AN INJECTED READING: the refused kids realloc is the chosen failure *)
         intros sm x os i H0 hist Hq1 Hq2 Hq3 Hq4. cbn [ip_ok ip_tr].
         eapply vrd_inj_exit; [exact HMD | | exact Hq1 | exact Hq2 | exact Hq3 | exact Hq4].
         intros sm' x' os' i' H0' hist' Hp' Hr' Hc' Hw'.
         destruct (vi_lm_granted _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLM' Hcnt0 ltac:(lia)) as (Ecnt & Efail).
         intros ii Hii _.
         assert (ii = 0%nat) by (cbn [trR PjGrammar.calls PjGrammar.is_call] in Hii; lia). subst ii. lia. }
    exists [], []. cbn [ip_ok ip_tr ip_W ip_mem ip_Lam ip_D]. split; [rewrite Hj2; reflexivity|].
    split; [intros Hr0; discriminate Hr0|].
    intros _. split.
    { destruct (Hin_ok2 (ip_p P) Hinok1 Hsrc2) as (I1 & I2 & I3 & I4 & _ & _ & _ & I8 & _ & _ & _ & I12).
      exists (ip_p P), (Z.of_nat (ie_d E) + 1). split; [lia|]. split; [lia|].
      split; [exact I1|]. split; [exact I2|]. split; [exact I3 | exact I4]. }
    assert (HSK : vi_subkeep (ie_o E) (rdW (ip_W P) (ip_mem P)) (rdW W2 mem2) (prh_lin (ip_Lam P))
                    (ip_kids P) (ip_keys P) (ip_kids P) (ip_keys P) (ip_acc P) Di).
    { split; [intros x k Hin; exact (HDLam x k (HDiD _ Hin))|].
      split; [apply (HDiKeep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg HLED2); intros [x k] Hin; exact (HDLam x k (HDiD _ Hin))|].
      split; [intros x Hx; exact (vi_bytes_mbyte _ _ _ _ _ _ _ x HpresK Hkb2 ltac:(lia))|].
      split; [intros x Hx; apply apresent_writable; apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HkL0);
              lia|].
      split; [lia|].
      split; [intros Ho6 x Hx;
              exact (vi_bytes_mbyte _ _ _ _ _ _ _ x (HpresY Ho6) (Hyb2 ltac:(rewrite Ho6; reflexivity)) ltac:(lia))|].
      exact HDiApK. }
    assert (HDy : keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) = [] /\ ip_keys P = 0 /\ ie_o E = false \/
                  ie_o E = true /\ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) = [(ip_keys P, 8 * ip_cap P)]).
    { destruct (ie_o E) eqn:Eo.
      - right. split; [reflexivity|]. unfold keys_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). reflexivity.
      - left. split; [unfold keys_blkR; rewrite orb_true_r; reflexivity | split; [exact (Hkeys0 eq_refl) | reflexivity]]. }
    assert (HKb : [(ip_kids P, 56 * ip_cap P)] = kids_blkR (ip_kids P) (ip_cap P))
      by (unfold kids_blkR; rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)); reflexivity).
    split.
    2: { (* THE PARTIAL FREE ORDER (FREEORD-NONE): the completed slots, then both arrays as the refused grow kept
            them (gheld at a refused kids realloc = arrz) *)
      apply (vi_fo_exit E P af Di W2 mem2 (ip_Lam P) _ [false] [PjGrammar.EFail (56 * (2 * cN))] []
               (if ie_o E then 6 else 5) (ip_kids P) (ip_keys P) (ip_n P) (ip_cap P)
               [(ip_kids P, 56 * ip_cap P)] (keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P)) (ip_D P)
               HFO HFL).
      - rewrite HnN. exact (vi_grow_no1 (ie_o E) cN [] HcN).
      - reflexivity.
      - exact Hlen.
      - exact Hdep.
      - exact Hdlt.
      - exact HDperm.
      - exact HSK.
      - intros Hh. rewrite HKb.
        change (PresetReqAt.gheld (ie_o E) (Z.to_nat (ip_cap P)) [PjGrammar.EFail (56 * (2 * cN))])
          with (PresetReqAt.arrz (ie_o E) (Z.to_nat (ip_cap P))).
        exact (vrd_arrz_blk (ie_o E) (ip_kids P) (ip_keys P) (ip_cap P) ltac:(lia) Hh).
      - reflexivity.
      - exact HNDD.
      - exact (vi_apart_node CTX E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEN0 HARg HlyE2 HBM2 HLED2 HLperm).
      - exact Hhdr2.
      - right. exists (56 * ip_cap P). split; [exact HkL0|]. split; [lia | reflexivity].
      - destruct HDy as [(-> & Hk0 & Hoo) | (Hoo & ->)].
        + left. split; [exact Hk0 | split; [exact Hoo | reflexivity]].
        + right. split; [exact Hoo|]. exists (8 * ip_cap P). split; [exact (proj2 (Hlin Hc0) Hoo)|]. split; [lia | reflexivity].
      - exact HDp0. }
    rewrite HMX.
    apply (vi_part_fd _ _ _ (if ie_o E then 6 else 5) (ip_kids P) (ip_keys P) (ip_n P) (ip_cap P) (ie_o E)
             [(ip_kids P, 56 * ip_cap P)] (keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P)) Di (ip_D P)
             (rev (ip_acc P))).
    + exact HNDD.
    + exact (vi_apart_node CTX E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEN0 HARg HlyE2 HBM2 HLED2 HLperm).
    + exact Hhdr2.
    + right. exists (56 * ip_cap P). split; [exact HkL0|]. split; [lia | reflexivity].
    + destruct (ie_o E) eqn:Eo.
      * right. split; [reflexivity|]. exists (8 * ip_cap P). split; [exact (proj2 (Hlin Hc0) eq_refl)|].
        split; [lia|]. unfold keys_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). reflexivity.
      * left. split; [exact (Hkeys0 eq_refl)|]. split; [reflexivity|]. unfold keys_blkR. rewrite orb_true_r. reflexivity.
    + exact HDp0.
    + apply (vi_sub_move (ie_o E) _ _ _ _ (ip_kids P) (ip_keys P) (ip_kids P) (ip_keys P) (ip_acc P) Di Hrep).
      * intros x k _ Hb. exact Hb.
      * apply (HDiKeep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg HLED2). intros [x k] Hin. exact (HDLam x k (HDiD _ Hin)).
      * intros x Hx. exact (vi_bytes_mbyte _ _ _ _ _ _ _ x HpresK Hkb2 ltac:(lia)).
      * intros x Hx. apply apresent_writable. apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HkL0). lia.
      * lia.
      * intros Ho6 x Hx.
        exact (vi_bytes_mbyte _ _ _ _ _ _ _ x (HpresY Ho6) (Hyb2 ltac:(rewrite Ho6; reflexivity)) ltac:(lia)).
      * exact HDiApK.
    + rewrite length_rev. exact Hlen.
    + exact Hdep'.
  - (* ARM 3: the kids realloc refused by the allocator (cnt <> fail) -> the exit with -1 *)
    destruct A3 as (Hnc & Hcf & Ha0 & EHp & Eab & _ & _ & _ & Hexc & Hinj3 & HLED2 & Hhdr2 & Hkb2 & Hyb2 & HLV2 & HXF2).
    set (cN := Z.to_nat (ip_cap P)) in *.
    assert (HcN : (0 < cN)%nat) by lia.
    assert (HnN : Z.to_nat (ip_n P) = cN) by (unfold cN; rewrite Hnc; reflexivity).
    set (trR := [PjGrammar.EFail (56 * (2 * cN))]).
    assert (HcZ : Z.of_nat cN = ip_cap P) by lia.
    assert (Hc2 : cap2R (ip_cap P) = 2 * ip_cap P)
      by (unfold cap2R; rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)); lia).
    (* grow's events on this arm, its granted trace, and the refused kids realloc's ledger at cap <> 0 *)
    assert (Ee3 : prhPg_evs ((if ie_o E then 6 else 5) =? 6) (ip_n P) (ip_cap P) [false] = PresetReqAt.rd_hevs trR).
    { rewrite (vi_evs_arm (ie_o E) (ip_n P) (ip_cap P) [false] ltac:(lia) ltac:(lia)), HnN.
      change (Z.to_nat (ip_cap P)) with cN. rewrite (vi_grow_no1 (ie_o E) cN [] HcN). reflexivity. }
    assert (EGT : PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P) =
                  PjGrammar.EGrow (56 * cN) (56 * (2 * cN)) ::
                    (if ie_o E then [PjGrammar.EGrow (8 * cN) (8 * (2 * cN))] else []))
      by (rewrite Hnc, <- HcZ; exact (vi_gtrace_eq (ie_o E) cN HcN)).
    rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in HLED2. cbv beta iota in HLED2.
    rewrite (Z.mod_small (ip_cnt P + 1) (2 ^ 64)) in HLED2 by lia.
    assert (Hj2 : PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))
                    (ip_ok P ++ [false]) = (None, ip_tr P ++ trR, [])).
    { apply HM. rewrite vrd_jrl_unfold, HnN. unfold PjGrammar.jbind at 1. rewrite vi_grow_no1 by exact HcN.
      reflexivity. }
    destruct (HTB [false] None trR [] [] ltac:(rewrite app_nil_r; exact Hj2)) as (Hcb & Hhb).
    assert (HBM2 : rd_blocks_move B (ie_ly E) (ie_S E) ly2 S2 (ip_D P) (ip_tr P ++ trR)
                     (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ie_d E)).
    { split; [exact HDnew|]. split; [rewrite Eab; exact HABperm|]. split; [rewrite Hfrsg; exact HFRperm | exact Hhb]. }
    apply (vi_run_exit (ip_fx P) E W2 ly2 S2 Hp2 regs2 mem2 md2 (ip_k P + k1) (vi_post Pm E P) Hsp2 ltac:(lia) ltac:(lia)
             HSV2 ltac:(change (getr regs2 (Z_to_bv 5 10)) with (getr regs2 10); exact Ha0) HJc).
    intros regs' md' HKx H18 HJc'. split; [|exact HPM2]. right.
    destruct (vrd_icur_after_call CTX CTX0 CW E ly2 S2 Hp2 W2 mem2 md' (ip_k P + k1) (ip_D P) (ip_tr P ++ trR)
                (ip_Lam P) _ _ _ _ _ _ HEN0 HJc' HBM2 HLED2 HLperm)
      as (Hsrc2 & _ & _).
    exists (MkIPos (ip_fx P) ly2 S2 Hp2 W2 regs' mem2 md' (ip_k P + k1) (ip_n P) (ip_cap P) (ip_kids P)
              (ip_keys P) (ip_p P) (ip_acc P) (ip_f P) (fun okr => (None, [], okr)) (ip_ok P ++ [false])
              (ip_tr P ++ trR) (ip_D P) (ip_Lam P)
              (Z.max (ip_peak P) (Z.min SIZE_MAXZ (Ledger.lsum (ip_Lam P) - 56 * ip_cap P + 56 * cap2R (ip_cap P))))
              (ip_cnt P + 1) (ip_fail P) (if 56 * cap2R (ip_cap P) <=? ie_most E then 1 else ip_ran P)), (-1).
    split; [reflexivity|]. split; [reflexivity|].
    pose proof (HXsp regs' (HKx 2 ltac:(cbn [vi_xregs In]; tauto))) as Hsp'.
    split. { apply (vi_iframe_sp E P2); [exact CK1 | exact Hsp' | reflexivity | reflexivity]. }
    split.
    { split; [exact HJc'|]. split; [exact CK2|]. split; [exact HFZ|]. split; [exact HFK|]. split; [exact CK3|].
      split; [exact HBM2|]. exact CK4. }
    split; [exact (HX3 regs' (HKx 3 ltac:(cbn [vi_xregs In]; tauto)))|].
    split; [exact (HX4 regs' (HKx 4 ltac:(cbn [vi_xregs In]; tauto)))|].
    split; [exact H18|]. split; [right; reflexivity|].
    split; [exact HLED2|]. split; [exact Hrl2|].
    split; [exact (vi_xfer_step _ _ _ (ip_tr P) trR _ Ee3 HXF HXF2)|].
    split.
    { intros sm x os i H0 hist HP HR HC _. exfalso. rewrite HGs in HR, HC.
      exact (vi_outcome_refused _ _ (ip_tr P) _ grest _ EeG HXF Hexc sm x os i H0 hist HP HR HC). }
    split.
    { cbn [ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran]. rewrite Hokp.
      eapply (vi_lm_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P)) _ grest);
        [exact HLM' | exact Hlsum | cbn [trR PjGrammar.calls PjGrammar.is_call]; lia | exact Hcnt0
        | reflexivity | | | | exact HLperm | exact Hsz | | | exact HGs | ].
      - split; [|split].
        + intros i Hi He. exfalso. assert (i = 0%nat) by (cbn in Hi; lia). subst i. cbn in He. lia.
        + destruct (Z.leb_spec (56 * cap2R (ip_cap P)) (ie_most E)) as [Hle | Hgt]; [right | left; reflexivity].
          split; [reflexivity|]. exists 0%nat. split; [cbn; lia|]. split.
          * apply vi_refused_of; [reflexivity | lia].
          * change (nth 0 (prh_ev_reqs trR) 0) with (Z.of_nat (56 * (2 * cN))).
            clear -Hle Hc2 HcZ. lia.
        + intros i Hi _ Hm. assert (i = 0%nat) by (cbn in Hi; lia). subst i.
          change (nth 0 (prh_ev_reqs trR) 0) with (Z.of_nat (56 * (2 * cN))) in Hm.
          destruct (Z.leb_spec (56 * cap2R (ip_cap P)) (ie_most E)) as [_ | Hgt];
            [reflexivity | exfalso; clear -Hm Hgt Hc2 HcZ; lia].
      - cbn. lia.
      - split; [intros Hin; exfalso; cbn in Hin; lia | intros _; reflexivity].
      - cbn [nliveR nlive_evR trR]. lia.
      - change (PjGrammar.calls trR) with 1%nat. rewrite EGT. cbn [prh_ev_helds PjGrammar.is_call app map].
        rewrite vi_rpeak1 by exact Hcf. cbn [hpeakR trR PjGrammar.held_ev]. rewrite Hc2.
        clear -Hpkge HLs0 HcZ. lia.
      - rewrite EGT. cbn [trR PjGrammar.calls PjGrammar.is_call]. lia. }
    split.
    { cbn [ip_S ip_tr]. rewrite vi_prh_held_app.
      assert (Hh0 : prh_held trR = cf_head) by (unfold prh_held, trR; cbn; lia).
      rewrite (vi_blocks_bytes_lsum ly2 S2), Eab, <- (vi_blocks_bytes_lsum (ip_ly P) (ip_S P)). lia. }
    split.
    { cbn [ip_D ip_tr]. rewrite vi_held_app. cbn [trR PjGrammar.held PjGrammar.held_ev]. lia. }
    split; [|split; [exact (vi_live_step _ _ _ (ip_tr P) trR _ Ee3 HLV HLV2)
                    |split; [exact (vi_hull_exit _ _ _ (ip_tr P) _ grest _ _ HGs EeG HHU Hhu2)|]]].
    2: { (* THE OUTCOME OF AN INJECTED READING: the refused kids realloc is no chosen failure, so no model run
            under the model's list meets this arm: inside grow's window by the arm's own exclusion, past it by the
            all-granted one *)
         intros sm x os i H0 hist Hq1 Hq2 Hq3 Hq4. cbn [ip_ok ip_tr].
         eapply vrd_inj_exit; [exact HMD | | exact Hq1 | exact Hq2 | exact Hq3 | exact Hq4].
         intros sm' x' os' i' H0' hist' Hp' Hr' Hc' Hw'.
         destruct (vi_lm_granted _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLM' Hcnt0 ltac:(lia)) as (Ecnt & Efail).
         exfalso.
         destruct (vi_inj_grow E P _ Hcont ltac:(lia) ltac:(lia) sm' x' os' i' Hr' Hc') as (Hrg & Hcg).
         assert (Ejw : (Z.to_nat (ie_fail E - ie_cnt E) - PjGrammar.calls (ip_tr P))%nat =
                       Z.to_nat (ip_fail P - ip_cnt P)) by lia.
         rewrite Ejw in Hrg, Hcg.
         destruct (Z_lt_le_dec (ip_fail P)
                     (ip_cnt P + Z.of_nat (PjGrammar.calls (prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P)))))
           as [HwIn | HwOut].
         - apply (Hinj3 sm' x' os' i' H0' hist' Hp' Hrg Hcg). rewrite vi_ty6. lia.
         - rewrite (vi_pg_okk (ie_o E) (ip_n P) (ip_cap P) (Z.to_nat (ip_fail P - ip_cnt P)) ltac:(lia) Hnc
                      ltac:(lia)) in Hrg, Hcg.
           exact (Hexc sm' x' os' i' H0' hist' Hp' Hrg Hcg). }
    exists [], []. cbn [ip_ok ip_tr ip_W ip_mem ip_Lam ip_D]. split; [rewrite Hj2; reflexivity|].
    split; [intros Hr0; discriminate Hr0|].
    intros _. split.
    { destruct (Hin_ok2 (ip_p P) Hinok1 Hsrc2) as (I1 & I2 & I3 & I4 & _ & _ & _ & I8 & _ & _ & _ & I12).
      exists (ip_p P), (Z.of_nat (ie_d E) + 1). split; [lia|]. split; [lia|].
      split; [exact I1|]. split; [exact I2|]. split; [exact I3 | exact I4]. }
    assert (HSK : vi_subkeep (ie_o E) (rdW (ip_W P) (ip_mem P)) (rdW W2 mem2) (prh_lin (ip_Lam P))
                    (ip_kids P) (ip_keys P) (ip_kids P) (ip_keys P) (ip_acc P) Di).
    { split; [intros x k Hin; exact (HDLam x k (HDiD _ Hin))|].
      split; [apply (HDiKeep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg HLED2); intros [x k] Hin; exact (HDLam x k (HDiD _ Hin))|].
      split; [intros x Hx; exact (vi_bytes_mbyte _ _ _ _ _ _ _ x HpresK Hkb2 ltac:(lia))|].
      split; [intros x Hx; apply apresent_writable; apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HkL0);
              lia|].
      split; [lia|].
      split; [intros Ho6 x Hx;
              exact (vi_bytes_mbyte _ _ _ _ _ _ _ x (HpresY Ho6) (Hyb2 ltac:(rewrite Ho6; reflexivity)) ltac:(lia))|].
      exact HDiApK. }
    assert (HDy : keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) = [] /\ ip_keys P = 0 /\ ie_o E = false \/
                  ie_o E = true /\ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) = [(ip_keys P, 8 * ip_cap P)]).
    { destruct (ie_o E) eqn:Eo.
      - right. split; [reflexivity|]. unfold keys_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). reflexivity.
      - left. split; [unfold keys_blkR; rewrite orb_true_r; reflexivity | split; [exact (Hkeys0 eq_refl) | reflexivity]]. }
    assert (HKb : [(ip_kids P, 56 * ip_cap P)] = kids_blkR (ip_kids P) (ip_cap P))
      by (unfold kids_blkR; rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)); reflexivity).
    split.
    2: { (* THE PARTIAL FREE ORDER (FREEORD-NONE): the completed slots, then both arrays as the refused grow kept
            them (gheld at a refused kids realloc = arrz) *)
      apply (vi_fo_exit E P af Di W2 mem2 (ip_Lam P) _ [false] [PjGrammar.EFail (56 * (2 * cN))] []
               (if ie_o E then 6 else 5) (ip_kids P) (ip_keys P) (ip_n P) (ip_cap P)
               [(ip_kids P, 56 * ip_cap P)] (keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P)) (ip_D P)
               HFO HFL).
      - rewrite HnN. exact (vi_grow_no1 (ie_o E) cN [] HcN).
      - reflexivity.
      - exact Hlen.
      - exact Hdep.
      - exact Hdlt.
      - exact HDperm.
      - exact HSK.
      - intros Hh. rewrite HKb.
        change (PresetReqAt.gheld (ie_o E) (Z.to_nat (ip_cap P)) [PjGrammar.EFail (56 * (2 * cN))])
          with (PresetReqAt.arrz (ie_o E) (Z.to_nat (ip_cap P))).
        exact (vrd_arrz_blk (ie_o E) (ip_kids P) (ip_keys P) (ip_cap P) ltac:(lia) Hh).
      - reflexivity.
      - exact HNDD.
      - exact (vi_apart_node CTX E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEN0 HARg HlyE2 HBM2 HLED2 HLperm).
      - exact Hhdr2.
      - right. exists (56 * ip_cap P). split; [exact HkL0|]. split; [lia | reflexivity].
      - destruct HDy as [(-> & Hk0 & Hoo) | (Hoo & ->)].
        + left. split; [exact Hk0 | split; [exact Hoo | reflexivity]].
        + right. split; [exact Hoo|]. exists (8 * ip_cap P). split; [exact (proj2 (Hlin Hc0) Hoo)|]. split; [lia | reflexivity].
      - exact HDp0. }
    rewrite HMX.
    apply (vi_part_fd _ _ _ (if ie_o E then 6 else 5) (ip_kids P) (ip_keys P) (ip_n P) (ip_cap P) (ie_o E)
             [(ip_kids P, 56 * ip_cap P)] (keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P)) Di (ip_D P)
             (rev (ip_acc P))).
    + exact HNDD.
    + exact (vi_apart_node CTX E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEN0 HARg HlyE2 HBM2 HLED2 HLperm).
    + exact Hhdr2.
    + right. exists (56 * ip_cap P). split; [exact HkL0|]. split; [lia | reflexivity].
    + destruct (ie_o E) eqn:Eo.
      * right. split; [reflexivity|]. exists (8 * ip_cap P). split; [exact (proj2 (Hlin Hc0) eq_refl)|].
        split; [lia|]. unfold keys_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). reflexivity.
      * left. split; [exact (Hkeys0 eq_refl)|]. split; [reflexivity|]. unfold keys_blkR. rewrite orb_true_r. reflexivity.
    + exact HDp0.
    + apply (vi_sub_move (ie_o E) _ _ _ _ (ip_kids P) (ip_keys P) (ip_kids P) (ip_keys P) (ip_acc P) Di Hrep).
      * intros x k _ Hb. exact Hb.
      * apply (HDiKeep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg HLED2). intros [x k] Hin. exact (HDLam x k (HDiD _ Hin)).
      * intros x Hx. exact (vi_bytes_mbyte _ _ _ _ _ _ _ x HpresK Hkb2 ltac:(lia)).
      * intros x Hx. apply apresent_writable. apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HkL0). lia.
      * lia.
      * intros Ho6 x Hx.
        exact (vi_bytes_mbyte _ _ _ _ _ _ _ x (HpresY Ho6) (Hyb2 ltac:(rewrite Ho6; reflexivity)) ltac:(lia)).
      * exact HDiApK.
    + rewrite length_rev. exact Hlen.
    + exact Hdep'.
  - (* ARM 4: an array's kids realloc granted -> the loop head, the array moved to k' *)
    destruct A4 as (Hnc & Hcf & Hty & Ha0 & k' & Lam' & Hk'lo & Hk'16 & (HswB & HswH & HswL) & HLED2 & HlsL & Hkb2
      & Hvis2 & Hhdr2 & _ & HLV2 & HXF2).
    assert (Ho5 : ie_o E = false) by (destruct (ie_o E); [exfalso; exact (Hty eq_refl) | reflexivity]).
    rewrite Ho5 in HlsL, Hbb2, Hhdr2.
    set (cN := Z.to_nat (ip_cap P)) in *.
    assert (HcN : (0 < cN)%nat) by lia.
    assert (HcZ : Z.of_nat cN = ip_cap P) by lia.
    assert (HnN : Z.to_nat (ip_n P) = cN) by (unfold cN; rewrite Hnc; reflexivity).
    assert (Hc2 : cap2R (ip_cap P) = 2 * ip_cap P) by (unfold cap2R; rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)); lia).
    set (trg := prhPg_gtrace false (Z.of_nat cN) (Z.of_nat cN)) in *.
    assert (Etrg : trg = [PjGrammar.EGrow (56 * cN) (56 * (2 * cN))]) by (unfold trg; rewrite vi_gtrace_eq by exact HcN; reflexivity).
    assert (Egt : PRH_Charge.prhPg_gtrace (5 =? 6) (ip_n P) (ip_cap P) = trg) by (rewrite Hnc, <- HcZ; reflexivity).
    rewrite Egt in Hbb2, HlsL.
    assert (Htrg_h : PjGrammar.held trg = 56 * (2 * ip_cap P - ip_cap P))
      by (rewrite Etrg; cbn [PjGrammar.held PjGrammar.held_ev]; lia).
    assert (Htrg_p : hpeakR trg = PjGrammar.held trg) by (rewrite Etrg; cbn [hpeakR PjGrammar.held PjGrammar.held_ev]; lia).
    assert (Htrg_c : PjGrammar.calls trg = 1%nat) by (rewrite Etrg; reflexivity).
    (* the model *)
    assert (HG : forall okt, PjGrammar.grow (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) ([true] ++ okt) =
                             (Some (2 * cN)%nat, trg, okt)).
    { intros okt. rewrite HnN, Ho5. exact (vi_grow_ok false cN okt HcN). }
    (* grow's events on this arm, and its granted trace *)
    assert (Ee4 : prhPg_evs ((if ie_o E then 6 else 5) =? 6) (ip_n P) (ip_cap P) [true] = PresetReqAt.rd_hevs trg).
    { rewrite (vi_evs_arm (ie_o E) (ip_n P) (ip_cap P) [true] ltac:(lia) ltac:(lia)).
      exact (f_equal (fun r => PresetReqAt.rd_hevs (snd (fst r))) (HG [])). }
    assert (EGt : PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P) = trg) by (rewrite Ho5; exact Egt).
    pose proof (vrd_jr_items_after_grow (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P) [true]
                  (ip_tr P) trg (ip_f P) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (2 * cN)%nat (ip_acc P)
                  (rest_atR (ie_tb E) (ie_text E) (ip_p P)) HG HM) as Hfac'.
    pose proof (Hfac' []) as Hfac0. rewrite app_nil_r in Hfac0.
    destruct (HTB [true] _ trg _ _ Hfac0) as (Hcb & Hhb).
    (* the blocks and the ledger list *)
    destruct HswB as (bl & Hsw1 & Hsw2). destruct HswL as (Lam1 & HL1a & HL1b).
    assert (HDk : Permutation (ip_D P) (kids_blkR (ip_kids P) (ip_cap P) ++ Di)).
    { unfold kids_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). rewrite Ho5 in HDp0.
      unfold keys_blkR in HDp0. rewrite orb_true_r, app_nil_l in HDp0. exact HDp0. }
    set (Dnew := [(k', 56 * cap2R (ip_cap P))]) in *.
    destruct (vi_swap_lam _ _ _ _ Dnew Di (ie_Lam E) Lam1 HLperm HDk HL1a HL1b) as (HLp' & HL1).
    assert (HSW : rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E)
                    (repeat true (PjGrammar.calls (ip_tr P)) ++ [true])
                    (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P ++ trg)
                    (Dnew ++ Di) Lam'
                    (Z.max (ip_peak P) (Ledger.lsum Lam')) (ip_cnt P + 1) (ip_fail P) (ip_ran P) /\
                  Ledger.lsum (Dnew ++ Di) = PjGrammar.held (ip_tr P ++ trg)).
    { apply (vi_grow_swap_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ (kids_blkR (ip_kids P) (ip_cap P)) Dnew Di Lam1 Lam' [true]
               (PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P)) trg grest _ _ _ _ HLM' Hlsum HDk HL1a HL1b Hcnt0).
      - rewrite Htrg_c. rewrite Htrg_c in Hcb. clear -Hcb. lia.
      - rewrite Htrg_c. reflexivity.
      - rewrite Htrg_c. apply vi_oks_true. intros i Hi He. assert (i = 0%nat) by (clear -Hi; lia). subst i.
        cbn in He. clear -He Hcf. lia.
      - rewrite Htrg_c. cbn. clear. lia.
      - rewrite Htrg_c. apply vi_fa_none. intros i Hi He. assert (i = 0%nat) by (clear -Hi; lia). subst i.
        cbn in He. clear -He Hcf. lia.
      - intros s L Hs. rewrite Etrg. cbn [fold_left].
        replace (56 * cN)%nat with (S (56 * cN - 1)) by (clear -HcN; lia). cbn [lsz_evR].
        replace (S (56 * cN - 1)) with (56 * cN)%nat by (clear -HcN; lia).
        cbn [map Dnew app snd]. rewrite Hc2.
        replace (56 * (2 * ip_cap P)) with (Z.of_nat (56 * (2 * cN))) by (clear -HcZ; lia). apply perm_skip.
        apply vi_rm1n_Z. replace (Z.of_nat (56 * cN)) with (56 * ip_cap P) by (clear -HcZ; lia).
        unfold kids_blkR in Hs. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in Hs. exact Hs.
      - unfold kids_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). rewrite Etrg. cbn [length Dnew nliveR].
        replace (56 * cN)%nat with (S (56 * cN - 1)) by (clear -HcN; lia). cbn [nlive_evR]. clear. lia.
      - unfold kids_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). cbn [Dnew Ledger.lsum].
        rewrite Htrg_h, Hc2. clear. lia.
      - rewrite prh_refused_peak_granted by (intros i Hi Hf; destruct i as [|[|i]]; discriminate Hf).
        rewrite Htrg_p, <- HlsL. clear -HLs0 Hpkge. lia.
      - exact HGs.
      - rewrite EGt. apply Nat.le_refl. }
    destruct HSW as (HLM2 & HlsD').
    assert (HBM' : rd_blocks_move B (ie_ly E) (ie_S E) ly2 S2 (Dnew ++ Di) (ip_tr P ++ trg)
                     (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ie_d E)).
    { apply (vi_swap_move _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bl HBM HDk Hsw1 Hsw2 HARg).
      - intros b [<- | []]. cbn [snd]. lia.
      - intros b b' [<- | []] Hb'. unfold kids_blkR in Hb'. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in Hb'.
        destruct Hb' as [<- | []]. cbn [snd]. lia.
      - exact Hfrsg.
      - exact Hhb. }
    assert (HinNew : In (k', 56 * cap2R (ip_cap P)) Lam')
      by (apply (Permutation_in _ (Permutation_sym HL1b)); left; reflexivity).
    assert (HDiL' : forall b, In b Di -> In b Lam').
    { intros b Hin. apply (Permutation_in _ (Permutation_sym HL1b)). right.
      apply (Permutation_in _ (Permutation_sym HL1)). apply in_or_app. left. exact Hin. }
    pose proof HLED2 as (_ & HNDL2 & _).
    destruct (vi_nodup_of Lam' (Dnew ++ Di) (ie_Lam E) HNDL2 HLp') as (HNDD' & HNDfD' & _).
    assert (Hk'Di : forall a k, In (a, k) Di -> a <> k').
    { intros a k Hin ->. cbn [Dnew app map fst] in HNDfD'. apply NoDup_ListNoDup in HNDfD'.
      apply List.NoDup_cons_iff in HNDfD' as [Hn1 _]. apply Hn1. apply in_map_iff. exists (k', k). split; [reflexivity | exact Hin]. }
    (* the room of the granted continuation *)
    assert (HcontG : snd (fst (ip_cont P [])) =
                     trg ++ snd (fst (vrd_jtail (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (2 * cN)%nat (ip_acc P) (ip_f P)
                                       (rest_atR (ie_tb E) (ie_text E) (ip_p P)) []))).
    { rewrite Hcont, (vi_jrl_gsplit _ _ _ _ _ _ _ (2 * cN)%nat trg); [reflexivity|].
      rewrite HnN, Ho5, Etrg. unfold PjGrammar.grow. rewrite (proj2 (Nat.ltb_ge cN cN) (Nat.le_refl _)).
      replace (Nat.eqb cN 0) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity. }
    pose proof Hroom as Hroom0. rewrite HcontG in Hroom0.
    assert (Hcap2b : 56 * cap2R (ip_cap P) + cf_head < cf_malloc_max).
    { destruct Hroom0 as (_ & Hmx & _). rewrite vi_maxreq_app in Hmx. rewrite Etrg in Hmx.
      cbn [prh_maxreq map fold_right PjGrammar.esize] in Hmx. rewrite Hc2. lia. }
    pose proof YG08cf.cf_malloc_max_bound as HMMB.
    apply (vi_run_head (ip_fx P) E W2 ly2 S2 Hp2 regs2 mem2 md2 (ip_k P + k1) (vi_post Pm E P) Hsp2 ltac:(lia) ltac:(lia)
             HSV2 ltac:(change (getr regs2 (Z_to_bv 5 10)) with (getr regs2 10); exact Ha0) HJc).
    intros regs' md' HKr HJc'. split; [|exact HPM2]. left.
    set (rest := rest_atR (ie_tb E) (ie_text E) (ip_p P)) in *.
    exists (MkIPos (ip_fx P) ly2 S2 Hp2 W2 regs' mem2 md' (ip_k P + k1) (ip_n P) (cap2R (ip_cap P)) k'
              (ip_keys P) (ip_p P) (ip_acc P) (ip_f P)
              (vrd_jtail (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (cap2R (ip_cap P))) (ip_acc P) (ip_f P) rest)
              (ip_ok P ++ [true]) (ip_tr P ++ trg) (Dnew ++ Di) Lam' (Z.max (ip_peak P) (Ledger.lsum Lam'))
              (ip_cnt P + 1) (ip_fail P) (ip_ran P)).
    split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
    assert (HKr' : forall n, In n vi_kregs -> getr regs' (Z_to_bv 5 n) = getr (ip_regs P) (Z_to_bv 5 n))
      by (intros n Hkn; rewrite (HKr n Hkn); exact (HK n (vi_kregs_cs n Hkn))).
    pose proof (HXsp regs' (HKr 2 ltac:(cbn [vi_kregs In]; tauto))) as Hsp'.
    assert (Ec2 : Z.to_nat (cap2R (ip_cap P)) = (2 * cN)%nat) by (rewrite Hc2; lia).
    destruct (vrd_icur_after_call CTX CTX0 CW E ly2 S2 Hp2 W2 mem2 md' (ip_k P + k1) (Dnew ++ Di) (ip_tr P ++ trg) Lam'
                _ _ _ _ _ _ HEN0 HJc' HBM' HLED2 HLp')
      as (Hsrc2 & Hhome2 & HRAq2).
    pose proof (vrd_node_ra_after_call CTX CTX0 CW E ly2 S2 Hp2 W2 mem2 md' (ip_k P + k1) (Dnew ++ Di) (ip_tr P ++ trg)
                  Lam' _ _ _ _ _ _ HEN0 HJc' HBM' HLED2 HLp') as HRAv2.
    split.
    { apply (vi_iframe_sp E P2); [exact CK1 | exact Hsp' | reflexivity | reflexivity]. }
    split.
    { apply (vi_iregs_keep E P _ HRG). exact HKr'. }
    split.
    { unfold vrd_inode. cbv zeta. cbn [ip_W ip_mem ip_n ip_cap ip_kids ip_keys ip_Lam ip_acc ip_D]. rewrite Ho5.
      split; [exact Hhdr2|]. split; [lia|]. split; [lia|]. split; [intros Hz; lia|].
      split; [intros _; split; [exact HinNew | intros Hf; discriminate Hf]|].
      split; [exact Hlen|].
      split.
      { exists Di. split.
        - unfold kids_blkR, keys_blkR. rewrite (proj2 (Z.eqb_neq (cap2R (ip_cap P)) 0) ltac:(lia)). cbn [orb negb Z.eqb Pos.eqb].
          try rewrite orb_true_r. apply Permutation_refl.
        - rewrite Ho5 in Hrep.
          apply (vi_sub_move false _ _ _ _ (ip_kids P) (ip_keys P) k' (ip_keys P) (ip_acc P) Di Hrep).
          + intros x k Hin _. exact (HDiL' _ Hin).
          + exact (HDiKeep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg HLED2 HDiL').
          + intros x Hx. exact (vi_bytes_mbyte _ _ _ _ _ _ _ x HpresK Hkb2 ltac:(lia)).
          + intros x Hx. apply apresent_writable.
            apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HinNew). lia.
          + lia.
          + intros Hf. discriminate Hf.
          + intros [a0 k0] x Hin Hx Hx'. unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
            apply (vi_lam_disj _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 k' (56 * cap2R (ip_cap P)) x HARg HLED2 (HDiL' _ Hin) HinNew
                     (Hk'Di _ _ Hin) Hx).
            unfold req_size. destruct (Z.eqb_spec (56 * cap2R (ip_cap P) + cf_head) 0); lia. }
      split.
      { intros x Hx. apply apresent_writable.
        apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HinNew). lia. }
      split; [exact HRAv2|].
      split; [intros _; exact (proj1 (vrd_lam_shadow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HinNew))|].
      split; [intros Hf; discriminate Hf|].
      intros _. exact (Hkeys0 Ho5). }
    split.
    { unfold vrd_icur. cbv zeta. cbn [ip_W ip_mem ip_p ip_S ip_ly ip_Hp ip_Lam ip_peak ip_cnt ip_fail ip_ran].
      split; [exact (Hin_ok2 (ip_p P) Hinok1 Hsrc2)|].
      split; [exact HRAq2|]. split; [exact Hsrc2|]. split; [exact Hhome2|]. split; [exact HLED2|].
      split; [rewrite Hfrsg; exact Hfrb | clear -Hcnt4; unfold rest in Hcnt4; lia]. }
    split.
    { split; [exact HJc'|]. split; [exact CK2|]. split; [exact HFZ|]. split; [exact HFK|]. split; [exact CK3|].
      split; [exact HBM'|]. exact CK4. }
    split.
    { split; [cbn [ip_ok ip_tr]; rewrite Hokp, PjGrammar.calls_app, Htrg_c, repeat_app; reflexivity|].
      split; [intros okr; cbn [ip_ok ip_tr ip_cont]; rewrite Ec2; exact (Hfac' okr)|].
      split.
      { cbn [ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran]. rewrite Hokp. exact HLM2. }
      split.
      { cbn [ip_S ip_cont]. rewrite Ec2.
        apply (vi_room_after (ip_S P) S2 trg); [exact Hroom0 | exact Hrl2 | rewrite <- Ee4; exact HLV2]. }
      split; [exact Hfuel|].
      split; [cbn [ip_S ip_tr]; rewrite vi_prh_held_app; lia|].
      split; [exact Hdep|]. split; [exact HlsD'|].
      split; [exact (vi_xfer_step _ _ _ (ip_tr P) trg _ Ee4 HXF HXF2)|].
      split; [exact (vi_live_step _ _ _ (ip_tr P) trg _ Ee4 HLV HLV2)|].
      exact (vi_hull_step _ _ _ (ip_tr P) trg _ (eq_trans EeG (f_equal PresetReqAt.rd_hevs EGt)) HHU Hhu2). }
    split; [cbn [ip_n ip_cap]; lia|].
    split; [reflexivity|].
    (* THE BATCH KIT'S LAYER: the slot array moved to k' with the members' blocks Di kept *)
    assert (HSK : vi_subkeep (ie_o E) (rdW (ip_W P) (ip_mem P)) (rdW W2 mem2) (prh_lin Lam')
                    (ip_kids P) (ip_keys P) k' (ip_keys P) (ip_acc P) Di).
    { split; [intros x k Hin; exact (HDiL' _ Hin)|].
      split; [exact (HDiKeep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg HLED2 HDiL')|].
      split; [intros x Hx; exact (vi_bytes_mbyte _ _ _ _ _ _ _ x HpresK Hkb2 ltac:(lia))|].
      split; [intros x Hx; apply apresent_writable;
              apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HinNew); lia|].
      split; [lia|].
      split; [intros Hf; rewrite Ho5 in Hf; discriminate Hf|].
      intros [a0 k0] x Hin Hx Hx'. unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
      apply (vi_lam_disj _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 k' (56 * cap2R (ip_cap P)) x HARg HLED2 (HDiL' _ Hin) HinNew
               (Hk'Di _ _ Hin) Hx).
      unfold req_size. destruct (Z.eqb_spec (56 * cap2R (ip_cap P) + cf_head) 0); lia. }
    split; [cbn [ip_n ip_cap]; rewrite Hc2; exact (vi_ncap_eq (ip_n P) (ip_cap P) ltac:(lia) Hnc HcapN)|].
    split; [eapply (vi_incaps_step E P _ Di HNC); [reflexivity | exact Hrep | exact HSK]|].
    exists af. split.
    { eapply (vi_iforder_step E P _ af Di HFO); [reflexivity | reflexivity | exact Hlen | exact HDperm | | exact HSK].
      cbn [ip_D ip_kids ip_keys ip_cap]. rewrite Ho5.
      unfold kids_blkR, keys_blkR. rewrite (proj2 (Z.eqb_neq (cap2R (ip_cap P)) 0) ltac:(lia)).
      cbn [orb negb Z.eqb Pos.eqb]. try rewrite orb_true_r. apply Permutation_refl. }
    intros okr. cbn [ip_ok ip_f ip_n ip_cap ip_p]. rewrite Ec2.
    exact (vi_fl_granted _ _ _ (ip_ok P) (ip_f P) _ _ af _ [true] (2 * cN)%nat trg HFL HG okr).
  - (* ARM 5: an object's kids realloc granted, its keys realloc the one set to fail -> the exit with -1 *)
    destruct A5 as (Hnc & Hcf & Hty & Hcf1 & Ha0 & k' & Lam' & Hk'lo & Hk'16 & (HswB & HswH & HswL) & HLED2 & Hkb2
      & Hvis2 & Hyb2 & Hhdr2 & HLV2 & HXF2).
    assert (Ho6 : ie_o E = true) by (destruct (ie_o E); [reflexivity | discriminate Hty]).
    rewrite Ho6 in Hhdr2.
    set (cN := Z.to_nat (ip_cap P)) in *.
    assert (HcN : (0 < cN)%nat) by lia.
    assert (HcZ : Z.of_nat cN = ip_cap P) by lia.
    assert (HnN : Z.to_nat (ip_n P) = cN) by (unfold cN; rewrite Hnc; reflexivity).
    assert (Hc2 : cap2R (ip_cap P) = 2 * ip_cap P)
      by (unfold cap2R; rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)); lia).
    set (trR := [PjGrammar.EGrow (56 * cN) (56 * (2 * cN)); PjGrammar.EFail (8 * (2 * cN))]).
    (* grow's events on this arm, and its granted trace *)
    assert (Ee5 : prhPg_evs ((if ie_o E then 6 else 5) =? 6) (ip_n P) (ip_cap P) [true; false] =
                  PresetReqAt.rd_hevs trR).
    { rewrite (vi_evs_arm (ie_o E) (ip_n P) (ip_cap P) [true; false] ltac:(lia) ltac:(lia)), HnN, Ho6.
      change (Z.to_nat (ip_cap P)) with cN. rewrite (vi_grow_no2 cN [] HcN). reflexivity. }
    assert (EGT6 : PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P) =
                   [PjGrammar.EGrow (56 * cN) (56 * (2 * cN)); PjGrammar.EGrow (8 * cN) (8 * (2 * cN))])
      by (rewrite Hnc, Ho6, <- HcZ; exact (vi_gtrace_eq true cN HcN)).
    assert (Hj5 : PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))
                    (ip_ok P ++ [true; false]) = (None, ip_tr P ++ trR, [])).
    { apply HM. rewrite vrd_jrl_unfold, HnN. unfold PjGrammar.jbind at 1. rewrite Ho6, vi_grow_no2 by exact HcN.
      reflexivity. }
    destruct (HTB [true; false] None trR [] [] ltac:(rewrite app_nil_r; exact Hj5)) as (Hcb & Hhb).
    destruct HswB as (bl & Hsw1 & Hsw2). destruct HswL as (Lam1 & HL1a & HL1b).
    set (Dy := [(ip_keys P, 8 * ip_cap P)]).
    assert (HDk : Permutation (ip_D P) (kids_blkR (ip_kids P) (ip_cap P) ++ (Dy ++ Di))).
    { unfold kids_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). rewrite Ho6 in HDp0.
      unfold keys_blkR in HDp0. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in HDp0. exact HDp0. }
    set (Dnew := [(k', 56 * cap2R (ip_cap P))]) in *.
    destruct (vi_swap_lam _ _ _ _ Dnew (Dy ++ Di) (ie_Lam E) Lam1 HLperm HDk HL1a HL1b) as (HLp' & HL1).
    assert (HBM' : rd_blocks_move B (ie_ly E) (ie_S E) ly2 S2 (Dnew ++ (Dy ++ Di)) (ip_tr P ++ trR)
                     (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ie_d E)).
    { apply (vi_swap_move _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bl HBM HDk Hsw1 Hsw2 HARg).
      - intros b [<- | []]. cbn [snd]. clear -Hc0 Hcf0 Hc2. lia.
      - intros b b' [<- | []] Hb'. unfold kids_blkR in Hb'. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in Hb'.
        destruct Hb' as [<- | []]. cbn [snd]. clear -Hc0 Hc2. lia.
      - exact Hfrsg.
      - exact Hhb. }
    assert (HinNew : In (k', 56 * cap2R (ip_cap P)) Lam')
      by (apply (Permutation_in _ (Permutation_sym HL1b)); left; reflexivity).
    assert (HDiL' : forall b, In b (Dy ++ Di) -> In b Lam').
    { intros b Hin. apply (Permutation_in _ (Permutation_sym HL1b)). right.
      apply (Permutation_in _ (Permutation_sym HL1)). apply in_or_app. left. exact Hin. }
    pose proof HLED2 as (_ & HNDL2 & _).
    destruct (vi_nodup_of Lam' (Dnew ++ (Dy ++ Di)) (ie_Lam E) HNDL2 HLp') as (HNDD' & HNDfD' & _).
    assert (Hk'Di : forall a k, In (a, k) Di -> a <> k').
    { intros a k Hin ->. cbn [Dnew Dy app map fst] in HNDfD'. apply NoDup_ListNoDup in HNDfD'.
      apply List.NoDup_cons_iff in HNDfD' as [Hn1 _]. apply Hn1. right. apply in_map_iff. exists (k', k).
      split; [reflexivity | exact Hin]. }
    assert (HLs' : Ledger.lsum Lam' = Ledger.lsum (ip_Lam P) + 56 * ip_cap P).
    { pose proof (vi_lsum_perm _ _ HL1a) as E1. pose proof (vi_lsum_perm _ _ HL1b) as E2.
      rewrite vi_lsum_app in E1, E2. unfold kids_blkR in E1. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in E1.
      cbn [Ledger.lsum Dnew] in E1, E2. rewrite Hc2 in E2. lia. }
    assert (HSW : rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E)
                    (repeat true (PjGrammar.calls (ip_tr P)) ++ [true; false])
                    (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P ++ trR)
                    (Dnew ++ (Dy ++ Di)) Lam'
                    (Z.max (ip_peak P) (Ledger.lsum Lam')) (ip_cnt P + 2) SIZE_MAXZ (ip_ran P) /\
                  Ledger.lsum (Dnew ++ (Dy ++ Di)) = PjGrammar.held (ip_tr P ++ trR)).
    { apply (vi_grow_swap_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ (kids_blkR (ip_kids P) (ip_cap P)) Dnew (Dy ++ Di) Lam1 Lam'
               [true; false] (PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P)) trR grest _ _ _ _ HLM' Hlsum HDk
               HL1a HL1b Hcnt0).
      - cbn [trR PjGrammar.calls PjGrammar.is_call] in Hcb |- *. clear -Hcb. lia.
      - reflexivity.
      - split; [|split].
        + intros i Hi He. cbn in Hi. destruct i as [|[|i]]; [exfalso; cbn in He; clear -He Hcf; lia | reflexivity
                                                            | exfalso; clear -Hi; lia].
        + left. reflexivity.
        + intros i Hi Hf _. exfalso. apply vi_refused_at in Hf as [Hf Hne]. cbn in Hi.
          destruct i as [|[|i]]; [discriminate Hf | apply Hne; clear -Hcf1; lia | clear -Hi; lia].
      - cbn. clear. lia.
      - split; [intros _; reflexivity | intros Hno; exfalso; apply Hno; cbn; clear -Hcf1; lia].
      - intros s L Hs. cbn [trR fold_left].
        replace (56 * cN)%nat with (S (56 * cN - 1)) by (clear -HcN; lia). cbn [lsz_evR].
        replace (S (56 * cN - 1)) with (56 * cN)%nat by (clear -HcN; lia).
        cbn [map Dnew app snd]. rewrite Hc2.
        replace (56 * (2 * ip_cap P)) with (Z.of_nat (56 * (2 * cN))) by (clear -HcZ; lia). apply perm_skip.
        apply vi_rm1n_Z. replace (Z.of_nat (56 * cN)) with (56 * ip_cap P) by (clear -HcZ; lia).
        unfold kids_blkR in Hs. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in Hs. exact Hs.
      - unfold kids_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). cbn [length Dnew trR nliveR].
        replace (56 * cN)%nat with (S (56 * cN - 1)) by (clear -HcN; lia). cbn [nlive_evR]. clear. lia.
      - unfold kids_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)).
        cbn [Dnew Ledger.lsum trR PjGrammar.held PjGrammar.held_ev]. rewrite Hc2. clear -HcZ. lia.
      - rewrite prh_refused_peak_granted.
        + cbn [trR hpeakR PjGrammar.held_ev]. rewrite HLs'. clear -HcZ HcN HLs0 Hpkge. lia.
        + intros i Hi Hf. cbn in Hi. destruct i as [|[|i]]; [discriminate Hf | clear -Hcf1; lia | clear -Hi; lia].
      - exact HGs.
      - rewrite EGT6. cbn [trR PjGrammar.calls PjGrammar.is_call]. lia. }
    destruct HSW as (HLM2 & HlsD').
    apply (vi_run_exit (ip_fx P) E W2 ly2 S2 Hp2 regs2 mem2 md2 (ip_k P + k1) (vi_post Pm E P) Hsp2 ltac:(lia) ltac:(lia)
             HSV2 ltac:(change (getr regs2 (Z_to_bv 5 10)) with (getr regs2 10); exact Ha0) HJc).
    intros regs' md' HKx H18 HJc'. split; [|exact HPM2]. right.
    destruct (vrd_icur_after_call CTX CTX0 CW E ly2 S2 Hp2 W2 mem2 md' (ip_k P + k1) (Dnew ++ (Dy ++ Di))
                (ip_tr P ++ trR) Lam' _ _ _ _ _ _ HEN0 HJc' HBM' HLED2 HLp') as (Hsrc2 & _ & _).
    exists (MkIPos (ip_fx P) ly2 S2 Hp2 W2 regs' mem2 md' (ip_k P + k1) (ip_n P) (ip_cap P) k'
              (ip_keys P) (ip_p P) (ip_acc P) (ip_f P) (fun okr => (None, [], okr)) (ip_ok P ++ [true; false])
              (ip_tr P ++ trR) (Dnew ++ (Dy ++ Di)) Lam' (Z.max (ip_peak P) (Ledger.lsum Lam')) (ip_cnt P + 2) SIZE_MAXZ
              (ip_ran P)), (-1).
    split; [reflexivity|]. split; [reflexivity|].
    pose proof (HXsp regs' (HKx 2 ltac:(cbn [vi_xregs In]; tauto))) as Hsp'.
    split. { apply (vi_iframe_sp E P2); [exact CK1 | exact Hsp' | reflexivity | reflexivity]. }
    split.
    { split; [exact HJc'|]. split; [exact CK2|]. split; [exact HFZ|]. split; [exact HFK|]. split; [exact CK3|].
      split; [exact HBM'|]. exact CK4. }
    split; [exact (HX3 regs' (HKx 3 ltac:(cbn [vi_xregs In]; tauto)))|].
    split; [exact (HX4 regs' (HKx 4 ltac:(cbn [vi_xregs In]; tauto)))|].
    split; [exact H18|]. split; [right; reflexivity|].
    split; [exact HLED2|]. split; [exact Hrl2|].
    split; [exact (vi_xfer_step _ _ _ (ip_tr P) trR _ Ee5 HXF HXF2)|].
    split.
    { (* the keys realloc was the chosen failure: no run meets the clause's counter premise *)
      intros sm x os i H0 hist _ _ _ Hf. exfalso.
      destruct (vi_lm_granted _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLM' Hcnt0 ltac:(lia)) as (Ecnt & Efail).
      rewrite HGs, !PjGrammar.calls_app, EGT6 in Hf. cbn [PjGrammar.calls PjGrammar.is_call] in Hf.
      clear -Hf Ecnt Efail Hcf1 Hcnt0. lia. }
    split.
    { cbn [ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran]. rewrite Hokp. exact HLM2. }
    split.
    { cbn [ip_S ip_tr]. rewrite vi_prh_held_app.
      assert (Hh0 : prh_held trR = 56 * ip_cap P + 2 * cf_head)
        by (unfold prh_held, trR; cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call];
            clear -HcZ; lia).
      assert (Hbs : blocks_bytes S2 = blocks_bytes (ip_S P) + 56 * ip_cap P).
      { rewrite (vi_blocks_bytes_lsum ly2 S2), (vi_blocks_bytes_lsum (ip_ly P) (ip_S P)).
        rewrite (vi_lsum_perm _ _ Hsw1), (vi_lsum_perm _ _ Hsw2), !vi_lsum_app. unfold kids_blkR, prhReader_ab.
        rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). cbn [map Ledger.lsum fst snd Dnew]. rewrite Hc2. lia. }
      clear -Hbs Hbb Hh0 Hcf0. lia. }
    split; [exact HlsD'|].
    split; [|split; [exact (vi_live_step _ _ _ (ip_tr P) trR _ Ee5 HLV HLV2)
                    |split; [exact (vi_hull_exit _ _ _ (ip_tr P) _ grest _ _ HGs EeG HHU Hhu2)|]]].
    2: { (* THE OUTCOME OF AN INJECTED READING: the refused keys realloc is the chosen failure *)
         intros sm x os i H0 hist Hq1 Hq2 Hq3 Hq4. cbn [ip_ok ip_tr].
         eapply vrd_inj_exit; [exact HMD | | exact Hq1 | exact Hq2 | exact Hq3 | exact Hq4].
         intros sm' x' os' i' H0' hist' Hp' Hr' Hc' Hw'.
         destruct (vi_lm_granted _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLM' Hcnt0 ltac:(lia)) as (Ecnt & Efail).
         intros ii Hii Hnb.
         assert (Hii' : (ii < 2)%nat) by (cbn [trR PjGrammar.calls PjGrammar.is_call] in Hii; lia).
         destruct ii as [|[|ii]]; [cbn in Hnb; discriminate Hnb | lia | lia]. }
    exists [], []. cbn [ip_ok ip_tr ip_W ip_mem ip_Lam ip_D]. split; [rewrite Hj5; reflexivity|].
    split; [intros Hr0; discriminate Hr0|].
    intros _. split.
    { destruct (Hin_ok2 (ip_p P) Hinok1 Hsrc2) as (I1 & I2 & I3 & I4 & _ & _ & _ & I8 & _ & _ & _ & I12).
      exists (ip_p P), (Z.of_nat (ie_d E) + 1). split; [clear -I8; lia|]. split; [clear -I12; lia|].
      split; [exact I1|]. split; [exact I2|]. split; [exact I3 | exact I4]. }
    assert (HSK : vi_subkeep (ie_o E) (rdW (ip_W P) (ip_mem P)) (rdW W2 mem2) (prh_lin Lam')
                    (ip_kids P) (ip_keys P) k' (ip_keys P) (ip_acc P) Di).
    { split; [intros x k Hin; apply HDiL'; apply in_or_app; right; exact Hin|].
      split; [apply (HDiKeep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg HLED2); intros b Hin; apply HDiL'; apply in_or_app; right;
              exact Hin|].
      split; [intros x Hx; exact (vi_bytes_mbyte _ _ _ _ _ _ _ x HpresK Hkb2 ltac:(clear -Hx Hlen Hnc; lia))|].
      split; [intros x Hx; apply apresent_writable;
              apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HinNew); rewrite Hc2;
              clear -Hx Hlen Hnc Hc0; lia|].
      split; [clear -Hk'16; lia|].
      split; [intros _ x Hx; exact (vi_bytes_mbyte _ _ _ _ _ _ _ x (HpresY Ho6) Hyb2 ltac:(clear -Hx Hlen Hnc; lia))|].
      intros [a0 k0] x Hin Hx Hx'. unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
      assert (HinL' : In (a0, k0) Lam') by (apply HDiL'; apply in_or_app; right; exact Hin).
      apply (vi_lam_disj _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 k' (56 * cap2R (ip_cap P)) x HARg HLED2 HinL' HinNew
               (Hk'Di _ _ Hin) Hx).
      unfold req_size. rewrite Hc2.
      destruct (Z.eqb_spec (56 * (2 * ip_cap P) + cf_head) 0) as [He | He]; clear -He Hx' Hlen Hnc Hc0 Hcf0; lia. }
    split.
    2: { (* THE PARTIAL FREE ORDER (FREEORD-NONE): the completed slots, then the new kids and the old keys (gheld
            at a refused keys realloc after a granted kids realloc) *)
      apply (vi_fo_exit E P af Di W2 mem2 Lam' _ [true; false] trR [] 6 k' (ip_keys P) (ip_n P) (ip_cap P) Dnew Dy
               (Dnew ++ (Dy ++ Di)) HFO HFL).
      - rewrite HnN, Ho6. exact (vi_grow_no2 cN [] HcN).
      - reflexivity.
      - exact Hlen.
      - exact Hdep.
      - exact Hdlt.
      - exact HDperm.
      - exact HSK.
      - intros Hh. rewrite Ho6. change (Z.to_nat (ip_cap P)) with cN. unfold trR. rewrite (vi_gheld_half cN HcN).
        unfold Dnew, Dy. cbn [map app snd]. rewrite Hh, Hc2. f_equal; [lia | f_equal; lia].
      - reflexivity.
      - exact HNDD'.
      - exact (vi_apart_node CTX E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEN0 HARg HlyE2 HBM' HLED2 HLp').
      - exact Hhdr2.
      - right. exists (56 * cap2R (ip_cap P)). split; [exact HinNew|]. split; [rewrite Hc2; clear -Hnc Hc0; lia | reflexivity].
      - right. split; [exact Ho6|]. exists (8 * ip_cap P). split; [apply HDiL'; left; reflexivity|].
        split; [clear -Hnc; lia | reflexivity].
      - apply Permutation_refl. }
    rewrite HMX.
    apply (vi_part_fd _ _ _ 6 k' (ip_keys P) (ip_n P) (ip_cap P) true Dnew Dy Di (Dnew ++ (Dy ++ Di))
             (rev (ip_acc P))).
    + exact HNDD'.
    + exact (vi_apart_node CTX E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEN0 HARg HlyE2 HBM' HLED2 HLp').
    + exact Hhdr2.
    + right. exists (56 * cap2R (ip_cap P)). split; [exact HinNew|]. split; [rewrite Hc2; clear -Hnc Hc0; lia | reflexivity].
    + right. split; [reflexivity|]. exists (8 * ip_cap P). split; [apply HDiL'; left; reflexivity|].
      split; [clear -Hnc; lia | reflexivity].
    + apply Permutation_refl.
    + rewrite Ho6 in Hrep.
      apply (vi_sub_move true _ _ _ _ (ip_kids P) (ip_keys P) k' (ip_keys P) (ip_acc P) Di Hrep).
      * intros x k Hin _. apply HDiL'. apply in_or_app. right. exact Hin.
      * apply (HDiKeep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg HLED2). intros b Hin. apply HDiL'. apply in_or_app. right. exact Hin.
      * intros x Hx. exact (vi_bytes_mbyte _ _ _ _ _ _ _ x HpresK Hkb2 ltac:(clear -Hx Hlen Hnc; lia)).
      * intros x Hx. apply apresent_writable.
        apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HinNew). rewrite Hc2. clear -Hx Hlen Hnc Hc0. lia.
      * clear -Hk'16. lia.
      * intros _ x Hx. exact (vi_bytes_mbyte _ _ _ _ _ _ _ x (HpresY Ho6) Hyb2 ltac:(clear -Hx Hlen Hnc; lia)).
      * intros [a0 k0] x Hin Hx Hx'. unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
        assert (HinL' : In (a0, k0) Lam') by (apply HDiL'; apply in_or_app; right; exact Hin).
        apply (vi_lam_disj _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 k' (56 * cap2R (ip_cap P)) x HARg HLED2 HinL' HinNew
                 (Hk'Di _ _ Hin) Hx).
        unfold req_size. rewrite Hc2. destruct (Z.eqb_spec (56 * (2 * ip_cap P) + cf_head) 0) as [He | He]; clear -He Hx' Hlen Hnc Hc0 Hcf0; lia.
    + rewrite length_rev. exact Hlen.
    + exact Hdep'.
  - (* ARM 6: an object's kids realloc granted, its keys realloc refused by the allocator -> the exit with -1 *)
    destruct A6 as (Hnc & Hcf & Hty & Hcf1 & Ha0 & k' & Lam' & Hk'lo & Hk'16 & (HswB & HswH & HswL) & _ & _ & Hexc
      & HLED2 & Hkb2 & Hvis2 & Hyb2 & Hhdr2 & HLV2 & HXF2).
    assert (Ho6 : ie_o E = true) by (destruct (ie_o E); [reflexivity | discriminate Hty]).
    rewrite Ho6 in Hhdr2.
    set (cN := Z.to_nat (ip_cap P)) in *.
    assert (HcN : (0 < cN)%nat) by lia.
    assert (HcZ : Z.of_nat cN = ip_cap P) by lia.
    assert (HnN : Z.to_nat (ip_n P) = cN) by (unfold cN; rewrite Hnc; reflexivity).
    assert (Hc2 : cap2R (ip_cap P) = 2 * ip_cap P)
      by (unfold cap2R; rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)); lia).
    set (trR := [PjGrammar.EGrow (56 * cN) (56 * (2 * cN)); PjGrammar.EFail (8 * (2 * cN))]).
    (* grow's events on this arm, its granted trace, and the refused keys realloc's ledger at cap <> 0 *)
    assert (Ee6 : prhPg_evs ((if ie_o E then 6 else 5) =? 6) (ip_n P) (ip_cap P) [true; false] =
                  PresetReqAt.rd_hevs trR).
    { rewrite (vi_evs_arm (ie_o E) (ip_n P) (ip_cap P) [true; false] ltac:(lia) ltac:(lia)), HnN, Ho6.
      change (Z.to_nat (ip_cap P)) with cN. rewrite (vi_grow_no2 cN [] HcN). reflexivity. }
    assert (EGT6 : PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P) =
                   [PjGrammar.EGrow (56 * cN) (56 * (2 * cN)); PjGrammar.EGrow (8 * cN) (8 * (2 * cN))])
      by (rewrite Hnc, Ho6, <- HcZ; exact (vi_gtrace_eq true cN HcN)).
    rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in HLED2. cbv beta iota in HLED2.
    rewrite (Z.mod_small (ip_cnt P + 1 + 1) (2 ^ 64)) in HLED2 by lia.
    replace (ip_cnt P + 1 + 1) with (ip_cnt P + 2) in HLED2 by lia.
    assert (Hj6 : PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))
                    (ip_ok P ++ [true; false]) = (None, ip_tr P ++ trR, [])).
    { apply HM. rewrite vrd_jrl_unfold, HnN. unfold PjGrammar.jbind at 1. rewrite Ho6, vi_grow_no2 by exact HcN.
      reflexivity. }
    destruct (HTB [true; false] None trR [] [] ltac:(rewrite app_nil_r; exact Hj6)) as (Hcb & Hhb).
    destruct HswB as (bl & Hsw1 & Hsw2). destruct HswL as (Lam1 & HL1a & HL1b).
    set (Dy := [(ip_keys P, 8 * ip_cap P)]).
    assert (HDk : Permutation (ip_D P) (kids_blkR (ip_kids P) (ip_cap P) ++ (Dy ++ Di))).
    { unfold kids_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). rewrite Ho6 in HDp0.
      unfold keys_blkR in HDp0. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in HDp0. exact HDp0. }
    set (Dnew := [(k', 56 * cap2R (ip_cap P))]) in *.
    destruct (vi_swap_lam _ _ _ _ Dnew (Dy ++ Di) (ie_Lam E) Lam1 HLperm HDk HL1a HL1b) as (HLp' & HL1).
    assert (HBM' : rd_blocks_move B (ie_ly E) (ie_S E) ly2 S2 (Dnew ++ (Dy ++ Di)) (ip_tr P ++ trR)
                     (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ie_d E)).
    { apply (vi_swap_move _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bl HBM HDk Hsw1 Hsw2 HARg).
      - intros b [<- | []]. cbn [snd]. clear -Hc0 Hcf0 Hc2. lia.
      - intros b b' [<- | []] Hb'. unfold kids_blkR in Hb'. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in Hb'.
        destruct Hb' as [<- | []]. cbn [snd]. clear -Hc0 Hc2. lia.
      - exact Hfrsg.
      - exact Hhb. }
    assert (HinNew : In (k', 56 * cap2R (ip_cap P)) Lam')
      by (apply (Permutation_in _ (Permutation_sym HL1b)); left; reflexivity).
    assert (HDiL' : forall b, In b (Dy ++ Di) -> In b Lam').
    { intros b Hin. apply (Permutation_in _ (Permutation_sym HL1b)). right.
      apply (Permutation_in _ (Permutation_sym HL1)). apply in_or_app. left. exact Hin. }
    pose proof HLED2 as (_ & HNDL2 & _).
    destruct (vi_nodup_of Lam' (Dnew ++ (Dy ++ Di)) (ie_Lam E) HNDL2 HLp') as (HNDD' & HNDfD' & _).
    assert (Hk'Di : forall a k, In (a, k) Di -> a <> k').
    { intros a k Hin ->. cbn [Dnew Dy app map fst] in HNDfD'. apply NoDup_ListNoDup in HNDfD'.
      apply List.NoDup_cons_iff in HNDfD' as [Hn1 _]. apply Hn1. right. apply in_map_iff. exists (k', k).
      split; [reflexivity | exact Hin]. }
    assert (HLs' : Ledger.lsum Lam' = Ledger.lsum (ip_Lam P) + 56 * ip_cap P).
    { pose proof (vi_lsum_perm _ _ HL1a) as E1. pose proof (vi_lsum_perm _ _ HL1b) as E2.
      rewrite vi_lsum_app in E1, E2. unfold kids_blkR in E1. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in E1.
      cbn [Ledger.lsum Dnew] in E1, E2. rewrite Hc2 in E2. lia. }
    assert (HSW : rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E)
                    (repeat true (PjGrammar.calls (ip_tr P)) ++ [true; false])
                    (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P ++ trR)
                    (Dnew ++ (Dy ++ Di)) Lam'
                    (Z.max (Z.max (ip_peak P) (Ledger.lsum Lam'))
                       (Z.min SIZE_MAXZ (Ledger.lsum Lam' - 8 * ip_cap P + 8 * cap2R (ip_cap P))))
                    (ip_cnt P + 2) (ip_fail P) (if 8 * cap2R (ip_cap P) <=? ie_most E then 1 else ip_ran P) /\
                  Ledger.lsum (Dnew ++ (Dy ++ Di)) = PjGrammar.held (ip_tr P ++ trR)).
    { apply (vi_grow_swap_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ (kids_blkR (ip_kids P) (ip_cap P)) Dnew (Dy ++ Di) Lam1 Lam'
               [true; false] (PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P)) trR grest _ _ _ _ HLM' Hlsum HDk
               HL1a HL1b Hcnt0).
      - cbn [trR PjGrammar.calls PjGrammar.is_call] in Hcb |- *. clear -Hcb. lia.
      - reflexivity.
      - split; [|split].
        + intros i Hi He. exfalso. cbn in Hi. destruct i as [|[|i]]; cbn in He;
            [clear -He Hcf; lia | clear -He Hcf1; lia | clear -Hi; lia].
        + destruct (Z.leb_spec (8 * cap2R (ip_cap P)) (ie_most E)) as [Hle | Hgt]; [right | left; reflexivity].
          split; [reflexivity|]. exists 1%nat. split; [cbn; lia|]. split.
          * apply vi_refused_of; [reflexivity | clear -Hcf1; lia].
          * change (nth 1 (prh_ev_reqs trR) 0) with (Z.of_nat (8 * (2 * cN))).
            clear -Hle Hc2 HcZ. lia.
        + intros i Hi Hf Hm. cbn in Hi. destruct i as [|[|i]].
          * exfalso. apply vi_refused_at in Hf as [Hf _]. discriminate Hf.
          * change (nth 1 (prh_ev_reqs trR) 0) with (Z.of_nat (8 * (2 * cN))) in Hm.
            destruct (Z.leb_spec (8 * cap2R (ip_cap P)) (ie_most E)) as [_ | Hgt];
              [reflexivity | exfalso; clear -Hm Hgt Hc2 HcZ; lia].
          * exfalso. clear -Hi. lia.
      - cbn. clear. lia.
      - split; [intros Hin; exfalso; cbn in Hin; clear -Hin Hcf Hcf1; lia | intros _; reflexivity].
      - intros s L Hs. cbn [trR fold_left].
        replace (56 * cN)%nat with (S (56 * cN - 1)) by (clear -HcN; lia). cbn [lsz_evR].
        replace (S (56 * cN - 1)) with (56 * cN)%nat by (clear -HcN; lia).
        cbn [map Dnew app snd]. rewrite Hc2.
        replace (56 * (2 * ip_cap P)) with (Z.of_nat (56 * (2 * cN))) by (clear -HcZ; lia). apply perm_skip.
        apply vi_rm1n_Z. replace (Z.of_nat (56 * cN)) with (56 * ip_cap P) by (clear -HcZ; lia).
        unfold kids_blkR in Hs. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)) in Hs. exact Hs.
      - unfold kids_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). cbn [length Dnew trR nliveR].
        replace (56 * cN)%nat with (S (56 * cN - 1)) by (clear -HcN; lia). cbn [nlive_evR]. clear. lia.
      - unfold kids_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)).
        cbn [Dnew Ledger.lsum trR PjGrammar.held PjGrammar.held_ev]. rewrite Hc2. clear -HcZ. lia.
      - change (PjGrammar.calls trR) with 2%nat. rewrite EGT6. cbn [prh_ev_helds PjGrammar.is_call app map].
        rewrite vi_rpeak2 by exact Hcf1. cbn [trR hpeakR PjGrammar.held_ev]. rewrite HLs', Hc2.
        clear -HcZ HcN HLs0 Hpkge. lia.
      - exact HGs.
      - rewrite EGT6. cbn [trR PjGrammar.calls PjGrammar.is_call]. lia. }
    destruct HSW as (HLM2 & HlsD').
    apply (vi_run_exit (ip_fx P) E W2 ly2 S2 Hp2 regs2 mem2 md2 (ip_k P + k1) (vi_post Pm E P) Hsp2 ltac:(lia) ltac:(lia)
             HSV2 ltac:(change (getr regs2 (Z_to_bv 5 10)) with (getr regs2 10); exact Ha0) HJc).
    intros regs' md' HKx H18 HJc'. split; [|exact HPM2]. right.
    destruct (vrd_icur_after_call CTX CTX0 CW E ly2 S2 Hp2 W2 mem2 md' (ip_k P + k1) (Dnew ++ (Dy ++ Di))
                (ip_tr P ++ trR) Lam' _ _ _ _ _ _ HEN0 HJc' HBM' HLED2 HLp') as (Hsrc2 & _ & _).
    exists (MkIPos (ip_fx P) ly2 S2 Hp2 W2 regs' mem2 md' (ip_k P + k1) (ip_n P) (ip_cap P) k'
              (ip_keys P) (ip_p P) (ip_acc P) (ip_f P) (fun okr => (None, [], okr)) (ip_ok P ++ [true; false])
              (ip_tr P ++ trR) (Dnew ++ (Dy ++ Di)) Lam'
              (Z.max (Z.max (ip_peak P) (Ledger.lsum Lam'))
                 (Z.min SIZE_MAXZ (Ledger.lsum Lam' - 8 * ip_cap P + 8 * cap2R (ip_cap P))))
              (ip_cnt P + 2) (ip_fail P) (if 8 * cap2R (ip_cap P) <=? ie_most E then 1 else ip_ran P)), (-1).
    split; [reflexivity|]. split; [reflexivity|].
    pose proof (HXsp regs' (HKx 2 ltac:(cbn [vi_xregs In]; tauto))) as Hsp'.
    split. { apply (vi_iframe_sp E P2); [exact CK1 | exact Hsp' | reflexivity | reflexivity]. }
    split.
    { split; [exact HJc'|]. split; [exact CK2|]. split; [exact HFZ|]. split; [exact HFK|]. split; [exact CK3|].
      split; [exact HBM'|]. exact CK4. }
    split; [exact (HX3 regs' (HKx 3 ltac:(cbn [vi_xregs In]; tauto)))|].
    split; [exact (HX4 regs' (HKx 4 ltac:(cbn [vi_xregs In]; tauto)))|].
    split; [exact H18|]. split; [right; reflexivity|].
    split; [exact HLED2|]. split; [exact Hrl2|].
    split; [exact (vi_xfer_step _ _ _ (ip_tr P) trR _ Ee6 HXF HXF2)|].
    split.
    { intros sm x os i H0 hist HP HR HC _. exfalso. rewrite HGs in HR, HC.
      exact (vi_outcome_refused _ _ (ip_tr P) _ grest _ EeG HXF Hexc sm x os i H0 hist HP HR HC). }
    split.
    { cbn [ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran]. rewrite Hokp. exact HLM2. }
    split.
    { cbn [ip_S ip_tr]. rewrite vi_prh_held_app.
      assert (Hh0 : prh_held trR = 56 * ip_cap P + 2 * cf_head)
        by (unfold prh_held, trR; cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call];
            clear -HcZ; lia).
      assert (Hbs : blocks_bytes S2 = blocks_bytes (ip_S P) + 56 * ip_cap P).
      { rewrite (vi_blocks_bytes_lsum ly2 S2), (vi_blocks_bytes_lsum (ip_ly P) (ip_S P)).
        rewrite (vi_lsum_perm _ _ Hsw1), (vi_lsum_perm _ _ Hsw2), !vi_lsum_app. unfold kids_blkR, prhReader_ab.
        rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). cbn [map Ledger.lsum fst snd Dnew]. rewrite Hc2. lia. }
      clear -Hbs Hbb Hh0 Hcf0. lia. }
    split; [exact HlsD'|].
    split; [|split; [exact (vi_live_step _ _ _ (ip_tr P) trR _ Ee6 HLV HLV2)
                    |split; [exact (vi_hull_exit _ _ _ (ip_tr P) _ grest _ _ HGs EeG HHU Hhu2)|]]].
    2: { (* THE OUTCOME OF AN INJECTED READING: the refused keys realloc is no chosen failure and grow's window is
            closed (cnt <> fail, cnt + 1 <> fail), so no model run under the model's list meets this arm: grow's
            events under that list are its all-granted ones, which the arm excludes *)
         intros sm x os i H0 hist Hq1 Hq2 Hq3 Hq4. cbn [ip_ok ip_tr].
         eapply vrd_inj_exit; [exact HMD | | exact Hq1 | exact Hq2 | exact Hq3 | exact Hq4].
         intros sm' x' os' i' H0' hist' Hp' Hr' Hc' Hw'.
         destruct (vi_lm_granted _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLM' Hcnt0 ltac:(lia)) as (Ecnt & Efail).
         exfalso.
         destruct (vi_inj_grow E P _ Hcont ltac:(lia) ltac:(lia) sm' x' os' i' Hr' Hc') as (Hrg & Hcg).
         pose proof (vi_gtrace_charge (ie_o E) (ip_cap P) ltac:(lia)) as (_ & Hgc & _).
         assert (Hjw : (PjGrammar.calls (prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P)) <=
                        Z.to_nat (ie_fail E - ie_cnt E) - PjGrammar.calls (ip_tr P))%nat).
         { rewrite Hnc, Hgc. destruct (ie_o E); lia. }
         rewrite (vi_pg_okk (ie_o E) (ip_n P) (ip_cap P) _ ltac:(lia) Hnc Hjw) in Hrg, Hcg.
         exact (Hexc sm' x' os' i' H0' hist' Hp' Hrg Hcg). }
    exists [], []. cbn [ip_ok ip_tr ip_W ip_mem ip_Lam ip_D]. split; [rewrite Hj6; reflexivity|].
    split; [intros Hr0; discriminate Hr0|].
    intros _. split.
    { destruct (Hin_ok2 (ip_p P) Hinok1 Hsrc2) as (I1 & I2 & I3 & I4 & _ & _ & _ & I8 & _ & _ & _ & I12).
      exists (ip_p P), (Z.of_nat (ie_d E) + 1). split; [clear -I8; lia|]. split; [clear -I12; lia|].
      split; [exact I1|]. split; [exact I2|]. split; [exact I3 | exact I4]. }
    assert (HSK : vi_subkeep (ie_o E) (rdW (ip_W P) (ip_mem P)) (rdW W2 mem2) (prh_lin Lam')
                    (ip_kids P) (ip_keys P) k' (ip_keys P) (ip_acc P) Di).
    { split; [intros x k Hin; apply HDiL'; apply in_or_app; right; exact Hin|].
      split; [apply (HDiKeep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg HLED2); intros b Hin; apply HDiL'; apply in_or_app; right;
              exact Hin|].
      split; [intros x Hx; exact (vi_bytes_mbyte _ _ _ _ _ _ _ x HpresK Hkb2 ltac:(clear -Hx Hlen Hnc; lia))|].
      split; [intros x Hx; apply apresent_writable;
              apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HinNew); rewrite Hc2;
              clear -Hx Hlen Hnc Hc0; lia|].
      split; [clear -Hk'16; lia|].
      split; [intros _ x Hx; exact (vi_bytes_mbyte _ _ _ _ _ _ _ x (HpresY Ho6) Hyb2 ltac:(clear -Hx Hlen Hnc; lia))|].
      intros [a0 k0] x Hin Hx Hx'. unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
      assert (HinL' : In (a0, k0) Lam') by (apply HDiL'; apply in_or_app; right; exact Hin).
      apply (vi_lam_disj _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 k' (56 * cap2R (ip_cap P)) x HARg HLED2 HinL' HinNew
               (Hk'Di _ _ Hin) Hx).
      unfold req_size. rewrite Hc2.
      destruct (Z.eqb_spec (56 * (2 * ip_cap P) + cf_head) 0) as [He | He]; clear -He Hx' Hlen Hnc Hc0 Hcf0; lia. }
    split.
    2: { (* THE PARTIAL FREE ORDER (FREEORD-NONE): the completed slots, then the new kids and the old keys (gheld
            at a refused keys realloc after a granted kids realloc) *)
      apply (vi_fo_exit E P af Di W2 mem2 Lam' _ [true; false] trR [] 6 k' (ip_keys P) (ip_n P) (ip_cap P) Dnew Dy
               (Dnew ++ (Dy ++ Di)) HFO HFL).
      - rewrite HnN, Ho6. exact (vi_grow_no2 cN [] HcN).
      - reflexivity.
      - exact Hlen.
      - exact Hdep.
      - exact Hdlt.
      - exact HDperm.
      - exact HSK.
      - intros Hh. rewrite Ho6. change (Z.to_nat (ip_cap P)) with cN. unfold trR. rewrite (vi_gheld_half cN HcN).
        unfold Dnew, Dy. cbn [map app snd]. rewrite Hh, Hc2. f_equal; [lia | f_equal; lia].
      - reflexivity.
      - exact HNDD'.
      - exact (vi_apart_node CTX E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEN0 HARg HlyE2 HBM' HLED2 HLp').
      - exact Hhdr2.
      - right. exists (56 * cap2R (ip_cap P)). split; [exact HinNew|]. split; [rewrite Hc2; clear -Hnc Hc0; lia | reflexivity].
      - right. split; [exact Ho6|]. exists (8 * ip_cap P). split; [apply HDiL'; left; reflexivity|].
        split; [clear -Hnc; lia | reflexivity].
      - apply Permutation_refl. }
    rewrite HMX.
    apply (vi_part_fd _ _ _ 6 k' (ip_keys P) (ip_n P) (ip_cap P) true Dnew Dy Di (Dnew ++ (Dy ++ Di))
             (rev (ip_acc P))).
    + exact HNDD'.
    + exact (vi_apart_node CTX E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEN0 HARg HlyE2 HBM' HLED2 HLp').
    + exact Hhdr2.
    + right. exists (56 * cap2R (ip_cap P)). split; [exact HinNew|]. split; [rewrite Hc2; clear -Hnc Hc0; lia | reflexivity].
    + right. split; [reflexivity|]. exists (8 * ip_cap P). split; [apply HDiL'; left; reflexivity|].
      split; [clear -Hnc; lia | reflexivity].
    + apply Permutation_refl.
    + rewrite Ho6 in Hrep.
      apply (vi_sub_move true _ _ _ _ (ip_kids P) (ip_keys P) k' (ip_keys P) (ip_acc P) Di Hrep).
      * intros x k Hin _. apply HDiL'. apply in_or_app. right. exact Hin.
      * apply (HDiKeep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg HLED2). intros b Hin. apply HDiL'. apply in_or_app. right. exact Hin.
      * intros x Hx. exact (vi_bytes_mbyte _ _ _ _ _ _ _ x HpresK Hkb2 ltac:(clear -Hx Hlen Hnc; lia)).
      * intros x Hx. apply apresent_writable.
        apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HinNew). rewrite Hc2. clear -Hx Hlen Hnc Hc0. lia.
      * clear -Hk'16. lia.
      * intros _ x Hx. exact (vi_bytes_mbyte _ _ _ _ _ _ _ x (HpresY Ho6) Hyb2 ltac:(clear -Hx Hlen Hnc; lia)).
      * intros [a0 k0] x Hin Hx Hx'. unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
        assert (HinL' : In (a0, k0) Lam') by (apply HDiL'; apply in_or_app; right; exact Hin).
        apply (vi_lam_disj _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 k' (56 * cap2R (ip_cap P)) x HARg HLED2 HinL' HinNew
                 (Hk'Di _ _ Hin) Hx).
        unfold req_size. rewrite Hc2. destruct (Z.eqb_spec (56 * (2 * ip_cap P) + cf_head) 0) as [He | He]; clear -He Hx' Hlen Hnc Hc0 Hcf0; lia.
    + rewrite length_rev. exact Hlen.
    + exact Hdep'.
  - (* ARM 7: an object's kids and keys reallocs granted -> the loop head, both arrays moved *)
    destruct A7 as (Hnc & Hcf & Hty & Hcf1 & Ha0 & k' & y' & Lam' & Hk'lo & Hk'16 & Hy'lo & Hy'16 & (HswB & HswH & HswL)
      & HLED2 & HlsL & Hkb2 & Hvis2 & Hyb2 & Hvisy & Hhdr2 & _ & HLV2 & HXF2).
    assert (Ho6 : ie_o E = true) by (destruct (ie_o E); [reflexivity | discriminate Hty]).
    rewrite Ho6 in HlsL, Hbb2, Hhdr2.
    set (cN := Z.to_nat (ip_cap P)) in *.
    assert (HcN : (0 < cN)%nat) by lia.
    assert (HcZ : Z.of_nat cN = ip_cap P) by lia.
    assert (HnN : Z.to_nat (ip_n P) = cN) by (unfold cN; rewrite Hnc; reflexivity).
    assert (Hc2 : cap2R (ip_cap P) = 2 * ip_cap P)
      by (unfold cap2R; rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)); lia).
    set (trg := prhPg_gtrace true (Z.of_nat cN) (Z.of_nat cN)) in *.
    assert (Etrg : trg = [PjGrammar.EGrow (56 * cN) (56 * (2 * cN)); PjGrammar.EGrow (8 * cN) (8 * (2 * cN))])
      by (unfold trg; rewrite vi_gtrace_eq by exact HcN; reflexivity).
    assert (Egt : PRH_Charge.prhPg_gtrace (6 =? 6) (ip_n P) (ip_cap P) = trg) by (rewrite Hnc, <- HcZ; reflexivity).
    rewrite Egt in Hbb2, HlsL.
    assert (Htrg_h : PjGrammar.held trg = 64 * ip_cap P)
      by (rewrite Etrg; cbn [PjGrammar.held PjGrammar.held_ev]; clear -HcZ; lia).
    assert (Htrg_p : hpeakR trg = PjGrammar.held trg)
      by (rewrite Etrg; cbn [hpeakR PjGrammar.held PjGrammar.held_ev]; clear -HcZ; lia).
    assert (Htrg_c : PjGrammar.calls trg = 2%nat) by (rewrite Etrg; reflexivity).
    (* the model *)
    assert (HG : forall okt, PjGrammar.grow (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) ([true; true] ++ okt) =
                             (Some (2 * cN)%nat, trg, okt)).
    { intros okt. rewrite HnN, Ho6. exact (vi_grow_ok true cN okt HcN). }
    (* grow's events on this arm, and its granted trace *)
    assert (Ee7 : prhPg_evs ((if ie_o E then 6 else 5) =? 6) (ip_n P) (ip_cap P) [true; true] =
                  PresetReqAt.rd_hevs trg).
    { rewrite (vi_evs_arm (ie_o E) (ip_n P) (ip_cap P) [true; true] ltac:(lia) ltac:(lia)).
      exact (f_equal (fun r => PresetReqAt.rd_hevs (snd (fst r))) (HG [])). }
    assert (EGt : PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P) = trg) by (rewrite Ho6; exact Egt).
    pose proof (vrd_jr_items_after_grow (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P) [true; true]
                  (ip_tr P) trg (ip_f P) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (2 * cN)%nat (ip_acc P)
                  (rest_atR (ie_tb E) (ie_text E) (ip_p P)) HG HM) as Hfac'.
    pose proof (Hfac' []) as Hfac0. rewrite app_nil_r in Hfac0.
    destruct (HTB [true; true] _ trg _ _ Hfac0) as (Hcb & Hhb).
    (* the blocks and the ledger list *)
    destruct HswB as (bl & Hsw1 & Hsw2). destruct HswL as (Lam1 & HL1a & HL1b).
    set (Dold := kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P)) in *.
    assert (EDold : Dold = [(ip_kids P, 56 * ip_cap P); (ip_keys P, 8 * ip_cap P)]).
    { unfold Dold, kids_blkR, keys_blkR. rewrite Ho6, (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). reflexivity. }
    assert (HDk : Permutation (ip_D P) (Dold ++ Di)) by (rewrite app_nil_l, app_assoc in HDperm; exact HDperm).
    set (Dnew := [(y', 8 * cap2R (ip_cap P)); (k', 56 * cap2R (ip_cap P))]) in *.
    destruct (vi_swap_lam _ _ _ _ Dnew Di (ie_Lam E) Lam1 HLperm HDk HL1a HL1b) as (HLp' & HL1).
    assert (HSW : rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E)
                    (repeat true (PjGrammar.calls (ip_tr P)) ++ [true; true])
                    (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P ++ trg)
                    (Dnew ++ Di) Lam'
                    (Z.max (ip_peak P) (Z.max (Ledger.lsum (ip_Lam P) + 56 * (cap2R (ip_cap P) - ip_cap P))
                                              (Ledger.lsum Lam')))
                    (ip_cnt P + 2) (ip_fail P) (ip_ran P) /\
                  Ledger.lsum (Dnew ++ Di) = PjGrammar.held (ip_tr P ++ trg)).
    { apply (vi_grow_swap_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dold Dnew Di Lam1 Lam' [true; true]
               (PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P)) trg grest _ _ _ _ HLM' Hlsum HDk HL1a HL1b Hcnt0).
      - rewrite Htrg_c. rewrite Htrg_c in Hcb. clear -Hcb. lia.
      - rewrite Htrg_c. reflexivity.
      - rewrite Htrg_c. apply vi_oks_true. intros i Hi He. destruct i as [|[|i]]; cbn in He;
          [clear -He Hcf; lia | clear -He Hcf1; lia | clear -Hi; lia].
      - rewrite Htrg_c. cbn. clear. lia.
      - rewrite Htrg_c. apply vi_fa_none. intros i Hi He. destruct i as [|[|i]]; cbn in He;
          [clear -He Hcf; lia | clear -He Hcf1; lia | clear -Hi; lia].
      - intros s L Hs. rewrite Etrg. cbn [fold_left].
        replace (56 * cN)%nat with (S (56 * cN - 1)) by (clear -HcN; lia).
        replace (8 * cN)%nat with (S (8 * cN - 1)) by (clear -HcN; lia).
        cbn [lsz_evR rm1nR].
        replace (S (56 * cN - 1)) with (56 * cN)%nat by (clear -HcN; lia).
        replace (S (8 * cN - 1)) with (8 * cN)%nat by (clear -HcN; lia).
        rewrite (proj2 (Nat.eqb_neq (56 * (2 * cN)) (8 * cN)) ltac:(clear -HcN; lia)). cbv beta iota.
        cbn [map Dnew app snd]. rewrite Hc2.
        replace (8 * (2 * ip_cap P)) with (Z.of_nat (8 * (2 * cN))) by (clear -HcZ; lia).
        replace (56 * (2 * ip_cap P)) with (Z.of_nat (56 * (2 * cN))) by (clear -HcZ; lia).
        apply perm_skip. apply perm_skip.
        apply vi_rm1n_Z. replace (Z.of_nat (8 * cN)) with (8 * ip_cap P) by (clear -HcZ; lia).
        apply vi_rm1n_Z. replace (Z.of_nat (56 * cN)) with (56 * ip_cap P) by (clear -HcZ; lia).
        rewrite EDold in Hs. exact Hs.
      - rewrite EDold, Etrg. cbn [length Dnew nliveR].
        replace (56 * cN)%nat with (S (56 * cN - 1)) by (clear -HcN; lia).
        replace (8 * cN)%nat with (S (8 * cN - 1)) by (clear -HcN; lia). cbn [nlive_evR]. clear. lia.
      - rewrite EDold, Htrg_h. cbn [Dnew Ledger.lsum]. rewrite Hc2. clear. lia.
      - rewrite prh_refused_peak_granted
          by (intros i Hi Hf; rewrite Htrg_c in Hi; destruct i as [|[|i]]; [discriminate Hf | discriminate Hf | lia]).
        rewrite Htrg_p, HlsL, Htrg_h, Hc2. clear -Hc0 HLs0 Hpkge. lia.
      - exact HGs.
      - rewrite EGt. apply Nat.le_refl. }
    destruct HSW as (HLM2 & HlsD').
    assert (HBM' : rd_blocks_move B (ie_ly E) (ie_S E) ly2 S2 (Dnew ++ Di) (ip_tr P ++ trg)
                     (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ie_d E)).
    { apply (vi_swap_move _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bl HBM HDk Hsw1 Hsw2 HARg).
      - intros b [<- | [<- | []]]; cbn [snd]; rewrite Hc2; clear -Hc0 Hcf0; lia.
      - intros b b' Hb Hb'. rewrite EDold in Hb'.
        destruct Hb as [<- | [<- | []]]; destruct Hb' as [<- | [<- | []]]; cbn [snd]; rewrite Hc2; clear -Hc0; lia.
      - exact Hfrsg.
      - exact Hhb. }
    assert (HinNewK : In (k', 56 * cap2R (ip_cap P)) Lam')
      by (apply (Permutation_in _ (Permutation_sym HL1b)); right; left; reflexivity).
    assert (HinNewY : In (y', 8 * cap2R (ip_cap P)) Lam')
      by (apply (Permutation_in _ (Permutation_sym HL1b)); left; reflexivity).
    assert (HDiL' : forall b, In b Di -> In b Lam').
    { intros b Hin. apply (Permutation_in _ (Permutation_sym HL1b)). right. right.
      apply (Permutation_in _ (Permutation_sym HL1)). apply in_or_app. left. exact Hin. }
    pose proof HLED2 as (_ & HNDL2 & _).
    destruct (vi_nodup_of Lam' (Dnew ++ Di) (ie_Lam E) HNDL2 HLp') as (HNDD' & HNDfD' & _).
    assert (Hk'Di : forall a k, In (a, k) Di -> a <> k').
    { intros a k Hin ->. cbn [Dnew app map fst] in HNDfD'. apply NoDup_ListNoDup in HNDfD'.
      apply List.NoDup_cons_iff in HNDfD' as [_ HN2]. apply List.NoDup_cons_iff in HN2 as [Hn1 _]. apply Hn1.
      apply in_map_iff. exists (k', k). split; [reflexivity | exact Hin]. }
    (* the room of the granted continuation *)
    assert (HcontG : snd (fst (ip_cont P [])) =
                     trg ++ snd (fst (vrd_jtail (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (2 * cN)%nat (ip_acc P) (ip_f P)
                                       (rest_atR (ie_tb E) (ie_text E) (ip_p P)) []))).
    { rewrite Hcont, (vi_jrl_gsplit _ _ _ _ _ _ _ (2 * cN)%nat trg); [reflexivity|].
      rewrite HnN, Ho6, Etrg. unfold PjGrammar.grow. rewrite (proj2 (Nat.ltb_ge cN cN) (Nat.le_refl _)).
      replace (Nat.eqb cN 0) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity. }
    pose proof Hroom as Hroom0. rewrite HcontG in Hroom0.
    assert (Hcap2b : 56 * cap2R (ip_cap P) + cf_head < cf_malloc_max).
    { destruct Hroom0 as (_ & Hmx & _). rewrite vi_maxreq_app in Hmx. rewrite Etrg in Hmx.
      cbn [prh_maxreq map fold_right PjGrammar.esize] in Hmx. rewrite Hc2. clear -Hmx HcZ. lia. }
    pose proof YG08cf.cf_malloc_max_bound as HMMB.
    apply (vi_run_head (ip_fx P) E W2 ly2 S2 Hp2 regs2 mem2 md2 (ip_k P + k1) (vi_post Pm E P) Hsp2 ltac:(lia) ltac:(lia)
             HSV2 ltac:(change (getr regs2 (Z_to_bv 5 10)) with (getr regs2 10); exact Ha0) HJc).
    intros regs' md' HKr HJc'. split; [|exact HPM2]. left.
    exists (MkIPos (ip_fx P) ly2 S2 Hp2 W2 regs' mem2 md' (ip_k P + k1) (ip_n P) (cap2R (ip_cap P)) k' y'
              (ip_p P) (ip_acc P) (ip_f P)
              (vrd_jtail (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (cap2R (ip_cap P))) (ip_acc P) (ip_f P)
                 (rest_atR (ie_tb E) (ie_text E) (ip_p P)))
              (ip_ok P ++ [true; true]) (ip_tr P ++ trg) (Dnew ++ Di) Lam'
              (Z.max (ip_peak P) (Z.max (Ledger.lsum (ip_Lam P) + 56 * (cap2R (ip_cap P) - ip_cap P)) (Ledger.lsum Lam')))
              (ip_cnt P + 2) (ip_fail P) (ip_ran P)).
    split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
    assert (HKr' : forall n, In n vi_kregs -> getr regs' (Z_to_bv 5 n) = getr (ip_regs P) (Z_to_bv 5 n))
      by (intros n Hkn; rewrite (HKr n Hkn); exact (HK n (vi_kregs_cs n Hkn))).
    pose proof (HXsp regs' (HKr 2 ltac:(cbn [vi_kregs In]; tauto))) as Hsp'.
    assert (Ec2 : Z.to_nat (cap2R (ip_cap P)) = (2 * cN)%nat) by (rewrite Hc2; clear -HcZ; lia).
    destruct (vrd_icur_after_call CTX CTX0 CW E ly2 S2 Hp2 W2 mem2 md' (ip_k P + k1) (Dnew ++ Di) (ip_tr P ++ trg) Lam'
                _ _ _ _ _ _ HEN0 HJc' HBM' HLED2 HLp')
      as (Hsrc2 & Hhome2 & HRAq2).
    pose proof (vrd_node_ra_after_call CTX CTX0 CW E ly2 S2 Hp2 W2 mem2 md' (ip_k P + k1) (Dnew ++ Di) (ip_tr P ++ trg)
                  Lam' _ _ _ _ _ _ HEN0 HJc' HBM' HLED2 HLp') as HRAv2.
    split.
    { apply (vi_iframe_sp E P2); [exact CK1 | exact Hsp' | reflexivity | reflexivity]. }
    split.
    { apply (vi_iregs_keep E P _ HRG). exact HKr'. }
    split.
    { unfold vrd_inode. cbv zeta. cbn [ip_W ip_mem ip_n ip_cap ip_kids ip_keys ip_Lam ip_acc ip_D]. rewrite Ho6.
      split; [exact Hhdr2|]. split; [rewrite Hc2; clear -Hnc Hc0 Hn; lia|].
      split; [rewrite Hc2; clear -Hcap2b HMMB Hcf0 Hc2; lia|]. split; [intros Hz; rewrite Hc2 in Hz; clear -Hz Hc0; lia|].
      split; [intros _; split; [exact HinNewK | intros _; exact HinNewY]|].
      split; [exact Hlen|].
      split.
      { exists Di. split.
        - unfold kids_blkR, keys_blkR. rewrite (proj2 (Z.eqb_neq (cap2R (ip_cap P)) 0) ltac:(rewrite Hc2; clear -Hc0; lia)).
          cbn [orb negb Z.eqb Pos.eqb app]. apply perm_swap.
        - rewrite Ho6 in Hrep.
          apply (vi_sub_move true _ _ _ _ (ip_kids P) (ip_keys P) k' y' (ip_acc P) Di Hrep).
          + intros x k Hin _. exact (HDiL' _ Hin).
          + exact (HDiKeep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg HLED2 HDiL').
          + intros x Hx. exact (vi_bytes_mbyte _ _ _ _ _ _ _ x HpresK Hkb2 ltac:(clear -Hx Hlen Hnc; lia)).
          + intros x Hx. apply apresent_writable.
            apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HinNewK). rewrite Hc2. clear -Hx Hlen Hnc Hc0. lia.
          + clear -Hk'16. lia.
          + intros _ x Hx. exact (vi_bytes_mbyte _ _ _ _ _ _ _ x (HpresY Ho6) Hyb2 ltac:(clear -Hx Hlen Hnc; lia)).
          + intros [a0 k0] x Hin Hx Hx'. unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
            apply (vi_lam_disj _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 k' (56 * cap2R (ip_cap P)) x HARg HLED2 (HDiL' _ Hin) HinNewK
                     (Hk'Di _ _ Hin) Hx).
            unfold req_size. rewrite Hc2.
            destruct (Z.eqb_spec (56 * (2 * ip_cap P) + cf_head) 0) as [He | He]; clear -He Hx' Hlen Hnc Hc0 Hcf0; lia. }
      split.
      { intros x Hx. apply apresent_writable.
        apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HinNewK). rewrite Hc2 in Hx |- *. clear -Hx Hn. lia. }
      split; [exact HRAv2|].
      split; [intros _; exact (proj1 (vrd_lam_shadow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HinNewK))|].
      split; [intros _ _; exact (proj1 (vrd_lam_shadow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HinNewY))|].
      intros Hf. discriminate Hf. }
    split.
    { unfold vrd_icur. cbv zeta. cbn [ip_W ip_mem ip_p ip_S ip_ly ip_Hp ip_Lam ip_peak ip_cnt ip_fail ip_ran].
      split; [exact (Hin_ok2 (ip_p P) Hinok1 Hsrc2)|].
      split; [exact HRAq2|]. split; [exact Hsrc2|]. split; [exact Hhome2|]. split; [exact HLED2|].
      split; [rewrite Hfrsg; exact Hfrb | clear -Hcnt4; lia]. }
    split.
    { split; [exact HJc'|]. split; [exact CK2|]. split; [exact HFZ|]. split; [exact HFK|]. split; [exact CK3|].
      split; [exact HBM'|]. exact CK4. }
    split.
    { split; [cbn [ip_ok ip_tr]; rewrite Hokp, PjGrammar.calls_app, Htrg_c, repeat_app; reflexivity|].
      split; [intros okr; cbn [ip_ok ip_tr ip_cont]; rewrite Ec2; exact (Hfac' okr)|].
      split.
      { cbn [ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran]. rewrite Hokp. exact HLM2. }
      split.
      { cbn [ip_S ip_cont]. rewrite Ec2.
        apply (vi_room_after (ip_S P) S2 trg); [exact Hroom0 | exact Hrl2 | rewrite <- Ee7; exact HLV2]. }
      split; [exact Hfuel|].
      split; [cbn [ip_S ip_tr]; rewrite vi_prh_held_app; clear -Hbb Hbb2; lia|].
      split; [exact Hdep|]. split; [exact HlsD'|].
      split; [exact (vi_xfer_step _ _ _ (ip_tr P) trg _ Ee7 HXF HXF2)|].
      split; [exact (vi_live_step _ _ _ (ip_tr P) trg _ Ee7 HLV HLV2)|].
      exact (vi_hull_step _ _ _ (ip_tr P) trg _ (eq_trans EeG (f_equal PresetReqAt.rd_hevs EGt)) HHU Hhu2). }
    split; [cbn [ip_n ip_cap]; rewrite Hc2; clear -Hnc Hc0; lia|].
    split; [reflexivity|].
    (* THE BATCH KIT'S LAYER: both arrays moved (kids to k', keys to y') with the members' blocks Di kept *)
    assert (HSK : vi_subkeep (ie_o E) (rdW (ip_W P) (ip_mem P)) (rdW W2 mem2) (prh_lin Lam')
                    (ip_kids P) (ip_keys P) k' y' (ip_acc P) Di).
    { split; [intros x k Hin; exact (HDiL' _ Hin)|].
      split; [exact (HDiKeep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg HLED2 HDiL')|].
      split; [intros x Hx; exact (vi_bytes_mbyte _ _ _ _ _ _ _ x HpresK Hkb2 ltac:(clear -Hx Hlen Hnc; lia))|].
      split; [intros x Hx; apply apresent_writable;
              apply (vi_lam_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARg HLED2 HinNewK); rewrite Hc2;
              clear -Hx Hlen Hnc Hc0; lia|].
      split; [clear -Hk'16; lia|].
      split; [intros _ x Hx; exact (vi_bytes_mbyte _ _ _ _ _ _ _ x (HpresY Ho6) Hyb2 ltac:(clear -Hx Hlen Hnc; lia))|].
      intros [a0 k0] x Hin Hx Hx'. unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
      apply (vi_lam_disj _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 k' (56 * cap2R (ip_cap P)) x HARg HLED2 (HDiL' _ Hin) HinNewK
               (Hk'Di _ _ Hin) Hx).
      unfold req_size. rewrite Hc2.
      destruct (Z.eqb_spec (56 * (2 * ip_cap P) + cf_head) 0) as [He | He]; clear -He Hx' Hlen Hnc Hc0 Hcf0; lia. }
    split; [cbn [ip_n ip_cap]; rewrite Hc2; exact (vi_ncap_eq (ip_n P) (ip_cap P) ltac:(lia) Hnc HcapN)|].
    split; [eapply (vi_incaps_step E P _ Di HNC); [reflexivity | exact Hrep | exact HSK]|].
    exists af. split.
    { eapply (vi_iforder_step E P _ af Di HFO); [reflexivity | reflexivity | exact Hlen | exact HDperm | | exact HSK].
      cbn [ip_D ip_kids ip_keys ip_cap]. rewrite Ho6.
      unfold kids_blkR, keys_blkR. rewrite (proj2 (Z.eqb_neq (cap2R (ip_cap P)) 0) ltac:(rewrite Hc2; clear -Hc0; lia)).
      cbn [orb negb Z.eqb Pos.eqb app]. apply perm_swap. }
    intros okr. cbn [ip_ok ip_f ip_n ip_cap ip_p]. rewrite Ec2.
    exact (vi_fl_granted _ _ _ (ip_ok P) (ip_f P) _ _ af _ [true; true] (2 * cN)%nat trg HFL HG okr).
Qed.

(* THE CAPACITY STEP IN THE GENERIC FORM (VrdIElem.tvrd_igrow_aG, a Theorem Labs lane's ruling): the memory invariant Pm
   crosses the run to the call unchanged (the run writes nothing), crosses grow by its memnorm keep (srr_inv_call),
   and crosses the runs after it unchanged (vi_igrow_post); the loop head keeps the element count *)
Theorem vi_igrow_okG : forall CTX, tvrd_igrow_aG B ARx SK CTX CTX0 CW.
Proof.
  unfold tvrd_igrow_aG, tvrd_igrow_aP. intros CTX Pm PLAW PCALL E P HEN HX HPM.
  pose proof HEN as HEN0.
  pose proof (vi_saved_of_iframe E P (proj1 HX)) as HSV.
  pose proof (proj1 (proj1 HX)) as Hsp.
  destruct HX as (HFR & HRG & HND & HCU & HJN & HMD & Hn & Hcnt4 & Hcont & HK1).
  pose proof HJN as (HJ & HWIN & HFZ & HFK & HROD & HBM & HCH2).
  destruct HEN as ((HAFN & HROD0 & Hstkhi) & Hq & Hv & Ho & HRD & Hp & Hnth & HRM & HRP0 & HCTX & HUNIV & HCUR & HCHAIN
    & HQCH & HFCH & HCTX2 & Hfr & HCWslot).
  pose proof HAFN as (HAR & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HRD as (_ & _ & _ & _ & Hinok & Hfwin & Hqlo & Hqhi & HRAq & Hsrc & Hhome & Hmaxrun & Hnode
    & Hqv & Htv & Hvwin & HLED0 & Hdmax & Hcntb).
  pose proof Hfwin as (He0 & He16 & Hetop & Hepres).
  pose proof HND as HND'. unfold vrd_inode in HND'. cbv beta zeta in HND'.
  destruct HND' as (Hhdr & Hncap & Hcap54 & Hcap0 & Hlin & Hlen & (Di & HDperm & Hrep) & Hrw & HRAv & HRAk
    & HRAy & Hkeys0).
  pose proof HCU as (Hinok1 & HRAq1 & Hsrc1 & Hhome1 & HLED & Hfrb & Hcnt2).
  pose proof HMD as (Hokp & Hfac & HLM & Hroom & Hfuel & Hbb & Hdep & Hlsum & HXF & HLV & HHU).
  pose proof HCWslot as (_ & _ & _ & HHB).
  destruct HRP0 as (_ & HpkS & Hpk24).
  pose proof HLM as (Hoks & Hcnt & Hfa & HLperm & Hsz & HnD & Hpeak).
  pose proof HBM as (HDnew & HABperm & HFRperm & Hhpk).
  (* the call's all-granted trace: the trace so far, grow's granted trace, the rest; grow's granted events *)
  destruct (vi_gt_grow (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P) (ip_tr P) (ip_f P)
              (ip_n P) (ip_cap P) (ip_acc P) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) (ip_cont P) Hokp (Hfac []) Hcont
              ltac:(lia) ltac:(lia)) as (grest & HGs).
  assert (EeG : prhPg_evs ((if ie_o E then 6 else 5) =? 6) (ip_n P) (ip_cap P) [] =
                PresetReqAt.rd_hevs (PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P)))
    by (rewrite (vi_evs_arm (ie_o E) (ip_n P) (ip_cap P) [] ltac:(lia) ltac:(lia)); reflexivity).
  pose proof (vi_stk_ge (ie_d E)) as HSTK.
  pose proof vi_stk_grow as HSTKg.
  pose proof (proj1 HJ) as HARP.
  pose proof HJ as (_ & HlyP & _).
  pose proof HlyP as (_ & _ & _ & _ & _ & _ & _ & _ & EtopP & EsloP & EshiP & _).
  destruct (vi_st_ok A_ICOMMA_SLOT (ip_fx P) (ip_W P) (ie_regs E) (ip_regs P) (ip_mem P) Hsp
              ltac:(lia) ltac:(lia) HSV) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (vi_EI (ip_regs P) (ie_regs E))) by (unfold vi_EI; apply Eimg_env).
  pose (RUN := paj_run_xR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS
                (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf)
                (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  unfold vrd_cfg.
  (* THE KIT'S CUT: the position's journal is at the budget ie_CW E; the run and grow's call rule are stated at the empty
     budget, so they run from the journal rebased to the position's depot, and the journal comes back to the budget
     after the call (YCbqGwild.ajournal_xw_unbase0R: grow stores no wild trace, its reallocs are code-only). THE
     RE-HIDING MOVE: the journal, the run and the call rule are at wle' SEGS RZ_cf (their R forms) *)
  pose proof (ajxR_wild HJ) as Hwild0.
  pose proof (YCbqGwild.ajournal_xw_rebaseR SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJr.
  paj_run_tok_x RUN HS HJr SHOK vi_Bspan;
    [eapply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
  (* the run wrote nothing: the memory at the call is the position's *)
  assert (HMEM : ms_mem ms = ip_mem P)
    by (apply functional_extensionality; intros x;
        rewrite <- (Z_to_bv_bv_unsigned 64 x); apply (vi_frame_all _ _ _ HF)).
  vi_regc HS (Z_to_bv 5 1) R1. vi_regc HS (Z_to_bv 5 2) R2. vi_regc HS (Z_to_bv 5 3) R3.
  vi_regc HS (Z_to_bv 5 4) R4. vi_regc HS (Z_to_bv 5 10) R10. vi_regc HS (Z_to_bv 5 8) R8.
  pose proof HRG as (Rgp & Rtp & R8v & R9v & R18v & R19v & R20v & R21v & R22v & R23v & R24v & R25v & R26v & R27v).
  assert (E240 : ew (vi_EI (ip_regs P) (ie_regs E)) 240 = Z_to_bv 64 BASE)
    by (unfold vi_EI; apply Eimg_img; unfold A_TEXT, A_LIM; lia).
  pose proof (@pa_B_ok _ A_prog_listing PAI) as (HB0 & HB1 & HB2).
  assert (HBr : 0 <= BASE < 2 ^ 64)
    by (pose proof (Z.pow_pos_nonneg 2 40 ltac:(lia) ltac:(lia)); lia).
  rewrite E240, (unsigned_lit_small BASE HBr) in R1.
  rewrite (vi_ew_low (ip_regs P) (ie_regs E) 2 (Z_to_bv 5 2) eq_refl) in R2.
  rewrite (vi_ew_low (ip_regs P) (ie_regs E) 3 (Z_to_bv 5 3) eq_refl) in R3.
  rewrite (vi_ew_low (ip_regs P) (ie_regs E) 4 (Z_to_bv 5 4) eq_refl) in R4.
  rewrite (vi_ew_low (ip_regs P) (ie_regs E) 20 (Z_to_bv 5 20) eq_refl) in R10.
  rewrite (vi_ew_low (ip_regs P) (ie_regs E) 8 (Z_to_bv 5 8) eq_refl) in R8.
  destruct HCH2 as (ch2' & Hch2' & Hspine2).
  assert (Hqr : 0 <= ie_q E < 2 ^ 64).
  { destruct Hinok as (_ & _ & _ & _ & _ & Hpos & Hlt & _). lia. }
  assert (Hs0 : s0Z (ms_regs ms) = ie_q E).
  { unfold s0Z. change (getr (ms_regs ms) 8) with (getr (ms_regs ms) (Z_to_bv 5 8)). rewrite R8.
    change (getr (ip_regs P) (Z_to_bv 5 8)) with (getr (ip_regs P) 8). rewrite R8v.
    unfold w64. apply unsigned_lit_small. exact Hqr. }
  assert (Hspms : spZ (ms_regs ms) = spZ (ie_regs E) - 144).
  { unfold spZ at 1. change (getr (ms_regs ms) 2) with (getr (ms_regs ms) (Z_to_bv 5 2)). rewrite R2.
    change (bv_unsigned (getr (ip_regs P) (Z_to_bv 5 2))) with (spZ (ip_regs P)). exact Hsp. }
  (* ---- where the node lies: an allocator block or a fake frame of the ENTRY state (rd_pre's prhReader_at, the
     real-stack window excluded by its last-but-three conjunct), still live at the position ---- *)
  pose proof Hnode as (Hv4096 & Hv8 & Hvrw & Hvzero & Hvat & Hvamr & Hvown & HvRA).
  pose proof (alx_layout SEGS B ARx LAWS (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) (ip_ly P)
                HAR HlyP) as (Hab_ly & Hfa_ly & _).
  assert (HinLP : forall a k, In (a, k) (ie_Lam E) -> In (a, k) (ip_Lam P)).
  { intros a k Hin. apply (Permutation_in _ (Permutation_sym HLperm)). apply in_or_app. right. exact Hin. }
  assert (HinAB : forall b m, In (b, m) (ablocks B (ie_ly E) (ie_S E)) -> In (b, m) (ablocks B (ip_ly P) (ip_S P))).
  { intros b m Hin. apply (Permutation_in _ (Permutation_sym HABperm)). apply in_or_app. right. exact Hin. }
  assert (HinFR : forall f, In f (frames (ie_S E)) -> In f (frames (ip_S P))).
  { intros f Hin. apply (Permutation_in _ (Permutation_sym HFRperm)). exact Hin. }
  assert (HDLam : forall a k, In (a, k) (ip_D P) -> In (a, k) (ip_Lam P)).
  { intros a k Hin. apply (Permutation_in _ (Permutation_sym HLperm)). apply in_or_app. left. exact Hin. }
  pose proof cf_head_nonneg as Hcf0.
  assert (HvC : (exists b m, In (b, m) (ablocks B (ie_ly E) (ie_S E)) /\ b <= ie_v E /\ ie_v E + 56 <= b + req_size m) \/
                (exists cid pos, In (cid, pos) (frames (ie_S E)) /\ frame_addr (ie_ly E) cid pos <= ie_v E /\
                   ie_v E + 56 <= frame_addr (ie_ly E) cid pos + fs_frame_bytes cid)).
  { destruct Hvat as [(a0 & k0 & Hin & Hle & Hhi) | [(b0 & m0 & Hin & _ & Hle & Hhi) | [(cid & pos & Hin & Hle & Hhi) | Hww]]].
    - left. destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED0 Hin) as (Hk0 & Hab0 & _).
      exists (a0 - cf_head), (k0 + cf_head). split; [exact Hab0|].
      unfold req_size. destruct (Z.eqb_spec (k0 + cf_head) 0); lia.
    - left. exists b0, m0. split; [exact Hin|]. unfold req_size. destruct (Z.eqb_spec m0 0); lia.
    - right. exists cid, pos. split; [exact Hin | lia].
    - exfalso. lia. }
  assert (Hvceil : ie_v E + 56 <= alloc_ceiling).
  { destruct HvC as [(b0 & m0 & Hin & Hle & Hhi) | (cid & pos & Hin & Hle & Hhi)].
    - destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ b0 m0 HAR Hin) as (_ & _ & Hc0 & _). lia.
    - destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ cid pos HAR Hin) as (_ & Hc0 & _). lia. }
  (* the blocks the position owns are apart from the node *)
  assert (HapD : forall bb kk x, In (bb, kk) (ip_D P) -> bb <= x < bb + kk -> ~ (ie_v E <= x < ie_v E + 56)).
  { intros bb kk x Hin Hx Hvx.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ bb kk _ _ HLED (HDLam _ _ Hin)) as (Hk0 & Hab0 & _).
    pose proof (HDnew bb kk Hin) as Hnew.
    assert (Hreq : req_size (kk + cf_head) = kk + cf_head)
      by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
    destruct HvC as [(b0 & m0 & Hin0 & Hle & Hhi) | (cid & pos & Hin0 & Hle & Hhi)].
    - assert (Hne : (b0, m0) <> (bb - cf_head, kk + cf_head)) by (intros Heq; rewrite Heq in Hin0; exact (Hnew Hin0)).
      pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ b0 m0 (bb - cf_head) (kk + cf_head) HARP
                    (HinAB _ _ Hin0) Hab0 Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq in Hd. lia.
    - pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ (bb - cf_head) (kk + cf_head) cid pos HARP
                    Hab0 (HinFR _ Hin0)) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq, Hfa_ly in Hd. lia. }
  (* every byte of a harness block of the position is present *)
  assert (HpresL : forall a k x, In (a, k) (ip_Lam P) -> a <= x < a + k -> apresent (w_H (ip_W P)) (ip_mem P) x).
  { intros a k x Hin Hx.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HLED Hin) as (Hk0 & Hab0 & _).
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HARP Hab0) as (_ & _ & _ & _ & Hpr & _).
    apply (proj1 (Hpr x ltac:(unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia))). }
  (* the granted continuation is grow's granted run, then the rest (vrd_jtail's) *)
  set (nN := Z.to_nat (ip_n P)) in *. set (cN := Z.to_nat (ip_cap P)) in *.
  assert (HnZ : Z.of_nat nN = ip_n P) by (unfold nN; lia).
  assert (HcZ : Z.of_nat cN = ip_cap P) by (unfold cN; lia).
  set (cap1 := if Nat.ltb nN cN then cN else if Nat.eqb cN 0 then 8%nat else (2 * cN)%nat).
  set (trg := prhPg_gtrace (ie_o E) (Z.of_nat nN) (Z.of_nat cN)).
  pose proof (vi_grow_granted (ie_o E) nN cN) as HGG. fold cap1 trg in HGG.
  set (TL := vrd_jtail (S (ie_d E)) (ie_o E) nN cap1 (ip_acc P) (ip_f P) (rest_atR (ie_tb E) (ie_text E) (ip_p P))).
  assert (HcontG : snd (fst (ip_cont P [])) = trg ++ snd (fst (TL []))).
  { rewrite Hcont. rewrite (vi_jrl_gsplit _ _ _ _ _ _ _ _ _ HGG). reflexivity. }
  rewrite HcontG in Hroom.
  (* at n = cap (> 0) the granted grow is one EGrow (two for an object) *)
  assert (Htrg : ip_n P = ip_cap P ->
    trg = PjGrammar.EGrow (56 * cN) (56 * (2 * cN)) ::
            (if ie_o E then [PjGrammar.EGrow (8 * cN) (8 * (2 * cN))] else [])).
  { intros Hnc. unfold trg. replace nN with cN by (unfold nN, cN; rewrite Hnc; reflexivity).
    apply vi_gtrace_eq. lia. }
  (* the node and the arrays: the shapes grow's text names *)
  assert (Hty6 : (if ie_o E then 6 else 5) = 6 -> ie_o E = true) by (destruct (ie_o E); [reflexivity | discriminate]).
  set (FP1 := [(ie_v E + 24, ie_v E + 40); (ie_v E + 48, ie_v E + 56)] ++
              ablocks_fp (prhReader_ab (kids_blkR (ip_kids P) (ip_cap P) ++
                                        keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P)))).
  (* an array of the node is a block the position owns *)
  assert (HarrD : forall b, In b (kids_blkR (ip_kids P) (ip_cap P) ++
                                  keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P)) -> In b (ip_D P)).
  { intros b Hin. apply (Permutation_in _ (Permutation_sym HDperm)). rewrite app_nil_l, app_assoc.
    apply in_or_app. left. exact Hin. }
  (* the call of row 281: grow, at the loop's sp, window e1 = 144 + ie_e E *)
  eapply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  { eapply (aj_call_xW_spR SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PAI)
              (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf)
              (wle'_trans SEGS YGcfRehidePost.RZ_cf)
              (ip_W P) _ _ ms (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E)
              (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (set_depot (st_depot (ip_S P)) (ie_S E)) (ie_Hp E) (ie_W E)
              (ie_mem E) (ie_md E) []
              (ip_ly P) (ip_S P) (ip_Hp P) _ (ip_k P) STK_grow (144 + ie_e E) FP1
              (- (144 + ie_e E)) _ ch2' _ HS eq_refl HJr).
    - rewrite Hspms. lia.
    - rewrite Z.mod_opp_l_z; [reflexivity | lia |].
      rewrite Z.add_mod by lia. rewrite He16. reflexivity.
    - lia.
    - exact HSTKg.
    - lia.
    - lia.
    - rewrite Z.add_mod by lia. rewrite He16. reflexivity.
    - lia.
    - change (getr (ms_regs ms) 3) with (getr (ms_regs ms) (Z_to_bv 5 3)). rewrite R3. exact Rgp.
    - change (getr (ms_regs ms) 4) with (getr (ms_regs ms) (Z_to_bv 5 4)). rewrite R4. exact Rtp.
    - change (getr (ms_regs ms) 1) with (getr (ms_regs ms) (Z_to_bv 5 1)). exact R1.
    - apply (ret_ok_codeptr_v 24856); [lia | reflexivity].
    - rewrite (unsigned_lit_small (BASE + 24856)) by (unfold M64; lia). lia.
    - replace (spZ (ie_regs E) + ie_e E + - (144 + ie_e E)) with (spZ (ie_regs E) - 144) by lia.
      rewrite Hs0, HMEM. exact Hch2'.
    - intros HPRE HFW. cbn [ss_pc setpc].
      refine (H_grow (ip_fx P) (ie_most E) (ie_own E) (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ms_regs ms) (ms_mem ms) _ ch2' (144 + ie_e E)
                (ie_v E) (if ie_o E then 6 else 5) 0 0 (ip_kids P) (ip_keys P) (ip_n P) (ip_cap P)
                (vi_bytes (ip_W P) (ip_mem P) (ip_kids P) (56 * ip_cap P))
                (vi_bytes (ip_W P) (ip_mem P) (ip_keys P) (8 * ip_cap P))
                (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P)
                _ HUNIV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      + split; [exact HPRE|]. split; [rewrite HMEM; exact HROD|]. split; [rewrite Hspms, EshiP; lia|].
        unfold raZ. change (getr (ms_regs ms) 1) with (getr (ms_regs ms) (Z_to_bv 5 1)). rewrite R1.
        split; [exact vi_grow_ret_slot_ceil | exact HFZ].
      + exact (vrd_node_chain B ARx HL LAWS CTX CTX0 CW E _ _ _ H_s0g HEN0).
      + exact (proj1 Hroom).
      + (* the live counts at grow's events, from the entry's along the call's granted events *)
        rewrite EeG. pose proof (vi_pk_mid YGcfRoomLive.rl_sec_req (ie_S E) (ip_S P) (ip_tr P)
          (PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P)) grest HLV) as Hm.
        rewrite <- HGs in Hm. clear -Hm HpkS. lia.
      + rewrite EeG. pose proof (vi_pk_mid (PresetRoom.in_cls YG00.kBatchClass) (ie_S E) (ip_S P) (ip_tr P)
          (PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P)) grest HLV) as Hm.
        rewrite <- HGs in Hm. clear -Hm Hpk24. lia.
      + (* the hull budget at grow's all-granted events: the entry's, past the events so far
           (PresetHullBudget.hull_budget_infix over the call's all-granted events split at the call) *)
        rewrite EeG. pose proof HHB as HHB'. rewrite HGs, !PresetHullBudget.hull_rd_app in HHB'.
        exact (PresetHullBudget.hull_budget_infix (ie_S E) (ip_S P) _ _ _ HHB' HHU).
      + change (getr (ms_regs ms) 10) with (getr (ms_regs ms) (Z_to_bv 5 10)). rewrite R10. exact R20v.
      + lia.
      + exact Hv8.
      + rewrite HMEM. exact Hhdr.
      + split; [destruct (ie_o E); [right | left]; reflexivity|].
        split; [lia|]. split.
        * intros Hc. destruct (Hcap0 Hc) as (Hk & Hy). split; [exact Hk | intros _; exact Hy].
        * intros Hc. destruct (Hlin Hc) as (Hk & Hy). split; [exact Hk|].
          intros Hty. exact (Hy (Hty6 Hty)).
      + intros [bb kk] x Hin Hx. unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
        exact (HapD bb kk x (HarrD _ Hin) Hx).
      + exact HFW.
      + destruct Hvat as [(a0 & k0 & Hin & Hle & Hhi) | [(b0 & m0 & Hin & Hnl & Hle & Hhi) | [(cid & pos & Hin & Hle & Hhi) | Hww]]].
        * left. exists a0, k0. split; [exact (HinLP _ _ Hin) | lia].
        * right. left. exists b0, m0. split; [exact (HinAB _ _ Hin)|]. split; [|lia].
          intros HinL. apply (Permutation_in _ HLperm) in HinL. apply in_app_or in HinL as [HinD | HinL].
          -- apply (HDnew _ _ HinD). replace (b0 + cf_head - cf_head) with b0 by lia.
             replace (m0 - cf_head + cf_head) with m0 by lia. exact Hin.
          -- exact (Hnl HinL).
        * right. right. left. exists cid, pos. split; [exact (HinFR _ Hin)|]. rewrite Hfa_ly. lia.
        * exfalso. lia.
      + rewrite HMEM. exact HRAv.
      + intros Hnc. assert (Hc0 : 0 < ip_cap P) by lia.
        destruct (Hlin Hc0) as (HkL & HyL).
        destruct (vi_bytes_ok (ip_W P) (ip_mem P) (ip_kids P) (56 * ip_cap P) ltac:(lia)
                    (fun x Hx => HpresL _ _ x HkL Hx)) as (Hkb & Hkl).
        split; [rewrite HMEM; exact Hkb|]. split; [exact Hkl|].
        intros Hty. pose proof (Hty6 Hty) as Ho6.
        destruct (vi_bytes_ok (ip_W P) (ip_mem P) (ip_keys P) (8 * ip_cap P) ltac:(lia)
                    (fun x Hx => HpresL _ _ x (HyL Ho6) Hx)) as (Hyb & Hyl).
        split; [rewrite HMEM; exact Hyb | exact Hyl].
      + rewrite HMEM. exact HLED.
      + lia.
      + intros Hnc. pose proof (Htrg Hnc) as Hg.
        assert (HcN : (0 < cN)%nat) by lia.
        assert (Hgm : prh_maxreq trg = 112 * ip_cap P).
        { rewrite Hg. destruct (ie_o E); cbn [prh_maxreq map fold_right PjGrammar.esize]; lia. }
        (* The kit's cut: grow's live room is PER EVENT at its own all-granted events, a prefix of the call's events
           from this position (PRH_Base.prh_live_evs; VrdLedgerStep.vl_live_evs_prefix) *)
        destruct Hroom as (_ & Hmax & Hlive).
        rewrite vi_maxreq_app, Hgm in Hmax.
        split.
        * unfold cap2R. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). lia.
        * assert (Etg : trg = PRH_Charge.prhPg_gtrace (ie_o E) (ip_n P) (ip_cap P))
            by (unfold trg; rewrite HnZ, HcZ; reflexivity).
          rewrite EeG, <- Etg. unfold PresetReqAt.rd_hevs in Hlive |- *. rewrite flat_map_app in Hlive.
          exact (vl_live_evs_prefix _ _ _ Hlive).
    - intros a Ha. destruct Ha as (r & Hin & Hr).
      unfold FP1 in Hin. apply in_app_or in Hin as [Hin | Hin].
      + left. exists (ie_v E, ie_v E + 56).
        split; [right; right; left; reflexivity|].
        cbn [In] in Hin. destruct Hin as [<- | [<- | []]]; cbn [fst snd] in Hr |- *; lia.
      + right. left. unfold ablocks_fp, prhReader_ab in Hin. rewrite map_map in Hin.
        apply in_map_iff in Hin as ((bb & kk) & Heq & Hinb). subst r. cbn [fst snd] in Hr.
        pose proof (HarrD _ Hinb) as HinD.
        exists (bb - cf_head), (kk + cf_head). split; [|split; [exact (HDnew _ _ HinD) | exact Hr]].
        destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ bb kk _ _ HLED (HDLam _ _ HinD)) as (_ & Hab0 & _).
        exact Hab0. }
  (* ---- after the call: the call-site position Pc and the arms (vi_igrow_post) ---- *)
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJc & HJg & HX2 & HP2 & HQ2).
  change (Z_to_bv 64 (BASE + 24856)) with (w64 (A_IPC A_IGROWRET_SLOT)).
  assert (HKms : forall n, In n vi_kregs -> getr (ms_regs ms) (Z_to_bv 5 n) = getr (ip_regs P) (Z_to_bv 5 n)).
  { intros n Hkn. cbn [vi_kregs In] in Hkn.
    repeat (destruct Hkn as [<- | Hkn];
            [lazymatch goal with |- getr _ (Z_to_bv 5 ?z) = _ =>
               let Hr := fresh "Hr" in vi_regc HS (Z_to_bv 5 z) Hr; rewrite Hr; apply vi_ew_low; reflexivity end|]).
    destruct Hkn. }
  replace (spZ (ie_regs E) + ie_e E + - (144 + ie_e E) + (144 + ie_e E)) with (spZ (ie_regs E) + ie_e E) in HJg by lia.
  rewrite HMEM in HJg, HX2, HQ2.
  (* the memory invariant across grow, by its memnorm keep *)
  pose proof (PCALL _ _ (proj2 HQ2) HPM) as HPM2.
  eapply (vi_igrow_post Pm CTX E
            (MkIPos (ip_fx P) (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ms_regs ms) (ip_mem P) _ (ip_k P) (ip_n P)
               (ip_cap P) (ip_kids P) (ip_keys P) (ip_p P) (ip_acc P) (ip_f P) (ip_cont P) (ip_ok P) (ip_tr P) (ip_D P)
               (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P))
            W2 ly2 S2 Hp2 regs2 mem2 md2 k1); [exact HEN0 | idtac | | exact HJg | | exact HP2 | | exact HPM2].
  2: { exact (YCbqGwild.ajournal_xw_unbase0R SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc Hwild0). }
  3: { exact (proj1 HQ2). }
  - split; [apply (vi_iframe_sp E P); [exact HFR | cbn [ip_regs]; rewrite Hspms; exact (eq_sym Hsp) | reflexivity
                                      | reflexivity]|].
    split; [apply (vi_iregs_keep E P _ HRG); exact HKms|].
    split; [exact HND|]. split; [exact HCU|].
    split; [split; [rewrite HMEM in HJr;
                    exact (YCbqGwild.ajournal_xw_unbase0R SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
                             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJr Hwild0)
                   | exact (proj2 HJN)]|].
    split; [exact HMD|]. split; [exact Hn|]. split; [exact Hcnt4|]. split; [exact Hcont | exact HK1].
  - intros a Ha Hna. apply HX2; [lia | exact Hna].
Qed.

(* the step Prop of record: the corollary of vi_igrow_okG at the trivial invariant (VrdIElem.tvrd_igrow_a_of_P) *)
Theorem vi_igrow_ok : forall CTX, tvrd_igrow_a B ARx SK CTX CTX0 CW.
Proof.
  intros CTX. apply tvrd_igrow_a_of_P. apply (vi_igrow_okG CTX (fun _ => True)).
  - constructor; intros; exact I.
  - intros m m' _ _. exact I.
Qed.

End S.

(* CHECK 1 FOR THE KIT'S CUT (lane RBase): the batch kit's layer the boundaries gained (VrdIElem.v vrd_ielem_a's cap = ncap (S n)
   and its free list at vrd_jfb) is satisfiable at the unit's own reader run. parse_items at d = 0, o = false, on the
   text [1] (bytes 91 49 93): after the first grow (granted, ok [true]; cap 0 to 8), the loop head's n = 0 has
   cap 8 = ncap 1, and the model's free list prhPi_frees at the grant prefix [true] is jfl's body after the grow,
   vrd_jfb at fuel 7 (prhPi_frees' fuel 2 * 3 + 2 = 8, one spent), depth 1, cap 8, accumulator [] - for every later
   grant list okr. The order list at n = 0 is pf_oitemsR's empty slot list (Di = [], Facc = [], af = []). *)
Lemma vi_sat_k1 : forall okr,
  PresetReqAt.ncap 1 = 8%nat /\
  prhPi_frees 0 false [91; 49; 93] ([true] ++ okr) = vrd_jfb 7 1 false 0 8 [] [49; 93] okr.
Proof. intros okr. split; reflexivity. Qed.

(* CHECK 1 OF VERIFY 21:4xZ for the changed shared statements vi_lm_comp / vi_grow_swap_step (A'Ledger): satisfiable
   at the unit's own reader run. parse_items at d = 0, o = false, on the text [1] (bytes 91 49 93): the whole call's
   all-granted trace prhPi_gtrace is the first grow's EGrow 0 448 (cap 0 to 8 slots of 56 bytes) then the number's
   EAlloc 2; from the start ledger (Lam [], peak 0, cnt 0, fail 1, ran 0, most 2) the first grow (Dold [],
   Dnew [(k, 448)], okg [true], gtg [EGrow 0 448], rest [EAlloc 2]) composes to g_peak 448 and g_count 1. *)
Lemma vi_sat_grow : forall k,
  prhPi_gtrace 0 false [91; 49; 93] = [EGrow 0 448; EAlloc 2] /\
  rd_ledger_move [] 0 0 1 0 2 (repeat true 0 ++ [true]) (prhPi_gtrace 0 false [91; 49; 93])
    ([] ++ [EGrow 0 448]) ([(k, 448)] ++ []) [(k, 448)] 448 1 1 0.
Proof.
  intros k.
  assert (HG : prhPi_gtrace 0 false [91; 49; 93] = [EGrow 0 448; EAlloc 2]) by (vm_compute; reflexivity).
  split; [exact HG|].
  assert (H0 : rd_ledger_move [] 0 0 1 0 2 (repeat true (PjGrammar.calls [])) (prhPi_gtrace 0 false [91; 49; 93])
                 [] [] [] 0 0 1 0).
  { unfold rd_ledger_move. rewrite HG. cbn [PjGrammar.calls repeat].
    split; [split; [intros i Hi; lia | split; [left; reflexivity | intros i Hi; lia]]|].
    split; [reflexivity|]. split; [split; intros H; [lia | reflexivity]|].
    split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
    reflexivity. }
  refine (proj1 (vi_grow_swap_step [] 0 0 1 0 2 (prhPi_gtrace 0 false [91; 49; 93]) [] [] [] 0 0 1 0
              [] [(k, 448)] [] [] [(k, 448)] [true] [EGrow 0 448] [EGrow 0 448] [EAlloc 2] 448 1 1 0
              H0 eq_refl (Permutation_refl _) (Permutation_refl _) (Permutation_refl _) _ _ eq_refl
              _ _ _ _ _ _ _ _ _)).
  - lia.
  - cbn. lia.
  - apply vi_oks_true. intros i Hi He. cbn in Hi. assert (i = 0%nat) by lia. subst i. cbn in He. lia.
  - reflexivity.
  - apply vi_fa_none. intros i Hi He. cbn in Hi. assert (i = 0%nat) by lia. subst i. cbn in He. lia.
  - intros s L Hs. cbn in Hs |- *. exact (perm_skip _ Hs).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite HG. reflexivity.
  - cbn. lia.
Qed.

(* the audit (the kit's cut re-fit, lane RBase): each step theorem closed under its Section hypotheses only *)
Print Assumptions vi_iexit_okG.
Print Assumptions vi_iexit_ok.
Print Assumptions vi_igrow_okG.
Print Assumptions vi_igrow_ok.
Print Assumptions vi_fo_exit.
Print Assumptions vi_sat_k1.
