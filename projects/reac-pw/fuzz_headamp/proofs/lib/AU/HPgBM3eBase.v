(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95be for
   reac-pw/fuzz_rate's image A: role's pcs (C3 0x820c4, the memcpy return 0x820e4, the parse return 0x8210c, E
   0x8212c, MAL 0x823fc, T 0x82408) become rate's (0x828b8, 0x828dc, 0x8290c, E 0x82930, MAL 0x82c9c, A 0x82ca8);
   the registers are renamed as rate's code has them (pod s2 -> s6, &cell s6 -> s5 = &hz, flags & 1 s4 -> s3, the
   frame's shadow base s3 -> s4, the shadow offset s7 -> s2, len s8 -> s10, pp + 0x4d18 s10 -> s9); F is read from
   the cell R+0x78 (blocks A and C: a read-only region at R), the hz cell takes the 4-byte 0x5a5a5a5a, block B also
   stores pod into R+0x138 (a writable window of the region at R) and reloads the flags byte into s10; the memcpy call
   is lib/A/RtPgSteps.v rts_intrin_at (role's hd_memcpy dropped), the .rodata zone is [0x10000, 0x22000), the cut file
   is lib/A/RtPgSeg.v (rl_ -> rt_, e_ -> q_, the role cell -> rs_hz_at, the frame pattern at the exits rs_PZ), the
   entry-state and list lemmas come from lib/A/RtPgScanKit.v and the memory facts from lib/A/RtPgMem.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgScanHead.v, with its module paths and module names changed; 211 of its 269 lines of code are new or changed and 973 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanF.v (rk_skipn_cons, rk_pairs_skip,
   rk_pairs_run, rk_pairs_end, rk_pairs_last) and proofs/reac-pw/fuzz_role/lib/A/RPgScanOuter.v and RPgScanInner.v
   (ro_post, ro_post_intro, ro_at_get, ro_at_sub, ro_at_keep, ro_chk_base, ro_denot0, ro_bge and the run tactics) at
   e39c26ea588; module paths fuzz_role -> fuzz_headamp, the rk_ / ro_ / si_ prefixes -> hb_, the cut lists and the
   cut base restated over headamp's lib/A/HPgSeg.v and HPgSegM.v (hs_at, hq_base3), the record facts restated over
   headamp's fold (Pod/Headamp.v ha_fold) instead of role's role_of_pairs. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgM3bBase.v at 42ff422eb80; the prefix
   hb_ -> hbu_, every statement restated over image B's segment layer (lib/AU/HPgSeg.v hsu_at, hsu_core,
   lib/AU/HPgSegM.v hqu_base3, hqu_fold_inv, hqu_pair_inv, hqu_exp and the hqu_L_ cut lists), image B's segments
   (lib/AU/Img0U.v) and image B's real frame of 0x220 bytes; the five-register scan list of image A (hq_L_scan)
   has no twin in image B and is dropped from the list tactics. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgBM3bBase.v, with its module names changed; 366 of its 477 lines of code are new or changed and 158 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanF.v (rk_skipn_cons, rk_pairs_skip,
   rk_pairs_run, rk_pairs_end, rk_pairs_last) and proofs/reac-pw/fuzz_role/lib/A/RPgScanOuter.v and RPgScanInner.v
   (ro_post, ro_post_intro, ro_at_get, ro_at_sub, ro_at_keep, ro_chk_base, ro_denot0, ro_bge and the run tactics) at
   e39c26ea588; module paths fuzz_role -> fuzz_headamp, the rk_ / ro_ / si_ prefixes -> hb_, the cut lists and the
   cut base restated over headamp's lib/A/HPgSeg.v and HPgSegM.v (hs_at, hq_base3), the record facts restated over
   headamp's fold (Pod/Headamp.v ha_fold) instead of role's role_of_pairs. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgM3bBase.v at 42ff422eb80 and
   proofs/reac-pw/fuzz_headamp/lib/A/HPgM3eBase.v at 13478523ccf; the same shared steps for image B: the prefixes
   hb_ / he_ -> hbe_, image A's segment layer (the hs_ names of lib/A/HPgSeg.v and the hq_ names of
   lib/A/HPgSegM.v) -> image B's (the hsu_ and hqu_ names of lib/AU), lib/A/Img0.v -> lib/AU/Img0U.v, lib/A/HPgSteps.v ->
   lib/AU/HPgSteps.v, image B's frame (x at F + 0x2c0 and its granules 88 .. 104, res at F + 0x2a0, the real frame of
   0x220 bytes), the record's float states named with their implicit arguments. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the facts the two pieces of the cell write and the last four checks of the walk of
   LLVMFuzzerTestOneInput (0x80c40) share, over lib/AU/HPgSegM.v's cuts of the checking segment M03. Proves no
   function (kind: segment lemma).

   WHAT IS HERE.
   - the model: on an uncorrupted record the parse's answer is expect_of's (hbe_ans_exp); expect_of's n is its cell
     count and its rc is -1 or that count (hbe_exp_n); on a live record rc is the cell count (hbe_exp_rc);
   - the reading and keeping of a cut's (location, value) list (the hbe_at lemmas), the cut base at a state that differs from
     a cut's only in its registers and its I/O-equal model (hbe_base3_regs), and the block post of a run that stores
     nothing (hbe_post) with the run tactics;
   - hbe_seg / hbe_blk: the geometry the segment's start facts give (HPgSeg.hsu_pre, i.e. HPgCSpec.hd_seg_pre at
     image B's record): F is the class-4 frame the harness holds, 32-aligned, in application memory, below the
     allocator's ceiling and outside the image; R is a stack address at or above the ceiling plus the callees'
     stack; every block live at the segment's start lies below the ceiling, in application memory and apart from F;
   - hbe_hc_core: a cut's journal-and-frame part gives the call adapters' frame of facts (HPgCalls.hc_core) at R;
     hbe_core_call and hbe_core_blk carry hsu_core across a call and across a block of straight-line code;
   - hbe_base3_kept: what every cut inside M03 carries (HPgSegM.hqu_base3) stays true when only the callees' stack
     [R - T_SEG_STK, R), the 136 bytes of x (F + 0x2c0) and x's 17 shadow granules (88 .. 104) may have changed.
   SECTION HYPOTHESES: MTL : ameter_laws MT (the meter's order is a preorder) and errno_low : api_env rsegs B (the
   errno cell lies in the image). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgCalls.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the pairs of the record's entries ================================ *)
Lemma hbe_skipn_cons : forall {A : Type} (l : list A) (j : nat) (d : A), (j < length l)%nat ->
skipn j l = nth j l d :: skipn (S j) l.
Proof.
intros A l. induction l as [|x l IH]; intros j d Hj; cbn [length] in Hj; [lia|].
destruct j as [|j]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn [length] in Hj. lia.
Qed.

Lemma hbe_pairwise_app : forall {X : Type} (R : X -> X -> Prop) (l1 l2 : list X) x y,
YG0f.pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|a l1 IH]; intros l2 x y HP Hx Hy; [destruct Hx|].
cbn [app YG0f.pairwise] in HP. destruct HP as [HF HP]. destruct Hx as [<-|Hx].
- rewrite Forall_forall in HF. apply HF. apply in_or_app. right. exact Hy.
- exact (IH l2 x y HP Hx Hy).
Qed.

(* ================================ the answers ================================ *)
(* On an uncorrupted record the parse's answer is expect_of's, for either null flag (fuzz_headamp.c:333-340:
   the parse of NULL and expect_of with the null flag both give (-1, [], (0, 0, NONE))). *)
Lemma hbe_ans_exp : forall (cx : hsu_scx rsegs) (r : Model.pod_rec),
Model.pod_rec_wf r -> Model.corrupt r = false -> 0 <= e_null (x_e rsegs cx) <= 1 ->
hqu_ans rsegs cx r = hqu_exp rsegs cx r.
Proof.
intros cx r Hwf Hc Hn. unfold hqu_ans, hqu_exp, hd_props.
assert (Hb : Model.buf r = Model.pod_encode r).
{ unfold Model.corrupt in Hc. unfold Model.buf. destruct (Model.p_corr r); [discriminate Hc | reflexivity]. }
destruct (Z.eq_dec (e_null (x_e rsegs cx)) 0) as [H0|H0].
- rewrite H0. cbn [Z.eqb]. cbn [parse_props]. rewrite Hb. apply parse_model_encode_any. exact Hwf.
- assert (H1 : e_null (x_e rsegs cx) = 1) by lia. rewrite H1. reflexivity.
Qed.

(* the answer's parts (Spec/HeadBytes.v answer_ok_parts) and its cells' length *)
Lemma hbe_ans_ok : forall (cx : hsu_scx rsegs) r, 0 <= e_cap (x_e rsegs cx) <= 9 ->
answer_ok (e_cap (x_e rsegs cx)) (hqu_ans rsegs cx r) /\
(length (ans_cells (hqu_ans rsegs cx r)) <= X_CELLS)%nat /\
Z.of_nat (length (ans_cells (hqu_ans rsegs cx r))) <= e_cap (x_e rsegs cx).
Proof.
intros cx r Hc. pose proof (parse_props_total (hd_props (e_null (x_e rsegs cx)) (Model.buf r)) (e_cap (x_e rsegs cx))
  ltac:(lia)) as HO. fold (hqu_ans rsegs cx r) in HO.
split; [exact HO|].
apply answer_ok_parts in HO as [[(_ & E2 & _) | (E1 & E2 & _)] _].
- rewrite E2. cbn [length]. unfold X_CELLS. split; lia.
- unfold X_CELLS. split; lia.
Qed.

(* expect_of's answer: n is the number of cells, and so is rc unless the record is not a Props object (or the null
   flag is set), when rc = -1 with no cell *)
Lemma hbe_exp_n : forall (cx : hsu_scx rsegs) r,
ans_n (hqu_exp rsegs cx r) = Z.of_nat (length (ans_cells (hqu_exp rsegs cx r))) /\
(ans_rc (hqu_exp rsegs cx r) = -1 \/ ans_rc (hqu_exp rsegs cx r) = Z.of_nat (length (ans_cells (hqu_exp rsegs cx r)))).
Proof.
intros cx r. unfold hqu_exp, expect_model.
destruct ((e_null (x_e rsegs cx) =? 1) || negb (Model.is_props r)); [cbn; split; [reflexivity | left; reflexivity]|].
destruct (negb (Model.params_struct r)); [cbn; split; [reflexivity | right; reflexivity]|].
destruct (ha_fold expect_cell (e_cap (x_e rsegs cx)) (Accessors.pairs (Model.ents r)) [] 0 REFUSE_NONE)
  as [[cells keys] rf].
cbn. split; [reflexivity | right; reflexivity].
Qed.

(* the loop runs only on a live record, where expect_of's rc is the number of cells *)
Lemma hbe_exp_rc : forall (cx : hsu_scx rsegs) r, hqu_live rsegs cx r ->
ans_rc (hqu_exp rsegs cx r) = Z.of_nat (length (ans_cells (hqu_exp rsegs cx r))).
Proof.
intros cx r (Hn & _ & Hp & Hs).
assert (E1 : (e_null (x_e rsegs cx) =? 1) = false) by (rewrite Hn; reflexivity).
unfold hqu_exp, expect_model. rewrite E1, Hp, Hs. cbn [orb negb].
destruct (ha_fold _ _ _ _ _ _) as [[c k] f]. reflexivity.
Qed.

(* ================================ the cut lists ================================ *)
(* a register fact of a list *)
Lemma hbe_at_get : forall H mem regs e L r v, hsu_at rsegs H mem regs e L -> In (LReg r, v) L ->
getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros H mem regs e L r v HL Hin. unfold hsu_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin). Qed.
(* a cell fact of a list *)
Lemma hbe_at_cell : forall H mem regs e L b o v, hsu_at rsegs H mem regs e L -> In (LCell b o, v) L ->
val_mem rsegs (mrestrict H mem) (hd_xv e b + o) 8 (v mod 2 ^ 64).
Proof. intros H mem regs e L b o v HL Hin. unfold hsu_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin). Qed.
(* a sub-list of a list of facts *)
Lemma hbe_at_sub : forall H mem regs e L L', hsu_at rsegs H mem regs e L -> (forall x, In x L' -> In x L) ->
hsu_at rsegs H mem regs e L'.
Proof.
intros H mem regs e L L' HL Hs. unfold hsu_at in *. rewrite Forall_forall in *. intros x Hx. exact (HL x (Hs x Hx)).
Qed.
(* a list whose registers all lie in kept holds at a register file that agrees on kept *)
Definition hbe_locb (kept : list (bv 5)) (f : hd_loc * Z) : bool :=
match fst f with LReg r => existsb (fun c => bv_eqb c (Z_to_bv 5 r)) kept | LCell _ _ => true end.
Lemma hbe_at_keep : forall H mem regs e L, hsu_at rsegs H mem regs e L ->
forall regs' (kept : list (bv 5)),
(forall r, In r kept -> getr regs' r = getr regs r) -> forallb (hbe_locb kept) L = true ->
hsu_at rsegs H mem regs' e L.
Proof.
intros H mem regs e L HL regs' kept Hk Hb. unfold hsu_at in *. rewrite Forall_forall in *.
intros [[r|b o] v] Hx. 2:{ exact (HL _ Hx). }
pose proof (HL _ Hx) as Hv. cbn [hd_at fst snd] in Hv |- *.
pose proof (proj1 (forallb_forall _ _) Hb _ Hx) as Hl. unfold hbe_locb in Hl. cbn [fst] in Hl.
apply existsb_exists in Hl as (c & Hc & Hcb). apply bv_eqb_eq in Hcb. subst c.
rewrite (Hk _ Hc). exact Hv.
Qed.
Lemma hbe_at_app : forall H mem regs e L1 L2,
hsu_at rsegs H mem regs e (L1 ++ L2) <-> hsu_at rsegs H mem regs e L1 /\ hsu_at rsegs H mem regs e L2.
Proof. intros H mem regs e L1 L2. unfold hsu_at. apply Forall_app. Qed.
(* membership in M03's concrete lists of facts *)
Ltac hbe_unf := unfold hqu_L_seg, hqu_L_frame, hqu_L_loopc, hqu_L_loopr, hqu_L_t56, hqu_L_body.
Ltac hbe_in := hbe_unf; cbv zeta; cbn [In app]; repeat (first [left; reflexivity | right]).
(* a list of facts that is a sub-list of a hypothesis' *)
Ltac hbe_sub HL :=
apply (hbe_at_sub _ _ _ _ _ _ HL);
let y := fresh "y" in let Hy := fresh "Hy" in
intros y Hy; hbe_unf; cbv zeta in Hy |- *; cbn [In app] in Hy |- *;
repeat (destruct Hy as [<-|Hy]; [repeat (first [left; reflexivity | right]) |]); destruct Hy.
(* membership in a kept-register list map (Z_to_bv 5) [...] *)
Ltac hbe_kin := apply in_map; cbn [In]; lia.

(* ================================ the block post and its arithmetic ================================ *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.

(* the state at a block's end pc, for a block that stores nothing: the world, the journal and the memory as at the
   block's start, the I/O state, the kept registers, and R *)
Definition hbe_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (pc : Z) (kept : list (bv 5))
(R : bvmap 5 word -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 pc) memc (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md2 k /\ same_io mdc md2 /\
(forall r, In r kept -> getr regs2 r = getr regs r) /\ R regs2.

Lemma hbe_post_intro : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc kept
(R : bvmap 5 word -> Prop) E' ss' ms md',
st_ok rsegs E' ss' (restrict (w_H W) ms) -> ss_resv ss' = None -> ss_pc ss' = pc -> ms_mem ms = memc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md' k -> same_io mdc md' ->
(forall r, In r kept -> getr (ms_regs ms) r = getr regs r) -> R (ms_regs ms) ->
hbe_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc kept R W (mkCfg ms md').
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc kept R E' ss' ms md' HS Hrv Hpc Hm HJ Hio Hk HR.
split; [reflexivity|]. exists (ms_regs ms), md'.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E' ss' ms HS Hrv) at 1; rewrite Hpc, Hm; reflexivity|].
split; [exact HJ|]. split; [exact Hio|]. split; [exact Hk | exact HR].
Qed.
End b.

Lemma hbe_denot0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma hbe_blt : forall j n, 0 <= j < 2 ^ 63 -> 0 <= n < 2 ^ 63 ->
branch_taken BC_LT (Z_to_bv 64 j) (Z_to_bv 64 n) = (j <? n).
Proof.
intros j n Hj Hn. rewrite YO0c.branch_lt, !unsigned_lit_small by lia.
rewrite !YO0b.s64_small by lia. reflexivity.
Qed.
(* an 8-byte real-frame cell as a region chunk over an extra atom *)
Lemma hbe_slot_chunk : forall {fx : YK11.FPState} E H mem R o v (n : nat), ew E n = Z_to_bv 64 v ->
val_mem rsegs (mrestrict H mem) (R + o) 8 (v mod 2 ^ 64) ->
YP09.chunk_ok rsegs E (mrestrict H mem) R (YP09.mkChunk o (CVal 8 (SOff n 0))).
Proof.
intros fx E H mem R o v n Hn Hv.
apply (chunk_ok_val rsegs E _ R o 8 (SOff n 0) (v mod 2 ^ 64)); [| | lia | exact Hv].
- rewrite hbe_denot0, Hn. symmetry. apply HPgSteps.Z_to_bv_mod64.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
Qed.

(* ================================ the run tactics ================================ *)
(* the memory after a run over read-only regions is the memory at the block's start *)
Ltac hbe_mem :=
lazymatch goal with HF : frame_of ?E0 ?rs0 ?m0 (ms_mem ?ms1) |- _ =>
  let H := fresh "HMn" in
  pose proof (frame_of_read_only E0 rs0 m0 (ms_mem ms1) eq_refl HF) as H;
  first [ match goal with HM0 : ms_mem ?ms0 = _ |- _ =>
            lazymatch ms0 with ms1 => fail | _ => rewrite HM0 in H; clear HM0 end end
        | idtac ];
  let HM := fresh "HM" in rename H into HM end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac hbe_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply HPgSteps.same_io_wvb]; kio] in kio.
(* the symbolic value of register r in the engine's last state, as a closed term *)
Ltac hbe_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.
(* the registers of a kept list keep their value *)
Ltac hbe_kept kept :=
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HAE : env_agree 32 (Ereg ?rg ?ex0) _ |- _ =>
  intros r Hr; exact (YI04.regs_kept_of_st_ok rsegs E' ss' (restrict _ ms) rg ex0 kept HS HAE
    ltac:(vm_compute; reflexivity) r Hr) end.
(* the post of a block's arm, after hbe_mem *)
Ltac hbe_post_intro B kept :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms), HM : ms_mem ?ms = _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  rewrite HM in HJ;
  eapply (hbe_post_intro B); [exact HS | reflexivity | reflexivity | exact HM | exact HJ | hbe_io | hbe_kept kept | ] end.

(* ================================ the segment's geometry and the cut base ================================ *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis errno_low : api_env rsegs B.

(* what the pieces read of the segment's start *)
Lemma hbe_start_wf : forall (cx : hsu_scx rsegs) r ev, @hqu_start_M03 fx rc SK rsegs B cx r ev -> pod_rec_wf r.
Proof. intros cx r ev HS. pose proof HS as (_ & _ & Hw & _). exact Hw. Qed.
Lemma hbe_start_pre : forall (cx : hsu_scx rsegs) r ev, @hqu_start_M03 fx rc SK rsegs B cx r ev ->
hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B).
Proof. intros cx r ev HS. exact (proj1 HS). Qed.

Lemma hbe_seg : forall (cx : hsu_scx rsegs) sh, hsu_pre rsegs B headamp_himg_B cx sh ->
In (4, x_pos rsegs cx) (frames (x_Sc rsegs cx)) /\ In (4, x_pos rsegs cx) (x_own rsegs cx) /\
e_F (x_e rsegs cx) = frame_addr (x_lyc rsegs cx) 4 (x_pos rsegs cx) /\
e_F (x_e rsegs cx) mod 32 = 0 /\ 4096 <= e_F (x_e rsegs cx) /\ e_F (x_e rsegs cx) + 1024 <= alloc_ceiling /\
in_app (e_F (x_e rsegs cx)) 1024 /\
(forall a, e_F (x_e rsegs cx) <= a < e_F (x_e rsegs cx) + 1024 -> ~ in_img rsegs a) /\
alloc_ceiling + T_SEG_STK <= e_R (x_e rsegs cx) /\ e_R (x_e rsegs cx) <= 2 ^ 47 /\
spZ (x_regs rsegs cx) = e_R (x_e rsegs cx) /\
0 <= e_cap (x_e rsegs cx) <= 9 /\ 0 <= e_null (x_e rsegs cx) <= 1.
Proof.
intros cx sh HP.
pose proof HP as HP'. apply hc_core_of_seg_pre in HP'; [|cbn [hi_rsz headamp_himg_B]; lia].
apply hc_core_R in HP' as (HR1 & HR2 & HR3).
pose proof HP as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _ & Hcap & Hnull & _).
cbn [hi_cid headamp_himg_B] in Hown, HF.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (4, x_pos rsegs cx) (frames (x_Sc rsegs cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (H32 & Happ & _ & _).
destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (_ & Hsep).
pose proof (proj1 (Forall_forall _ _) Hsep _ Hin) as (H4096 & Hceil). cbn [fst snd] in H4096, Hceil.
change (fs_frame_bytes 4) with 1024 in Happ, Hceil.
rewrite <- HF in H32, Happ, H4096, Hceil.
split; [exact Hin|]. split; [exact Hown|]. split; [exact HF|]. split; [exact H32|]. split; [exact H4096|].
split; [exact Hceil|]. split; [exact Happ|].
split.
{ intros a Ha. refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR _)).
  right. left. exists 4, (x_pos rsegs cx). split; [exact Hin|]. rewrite <- HF. change (fs_frame_bytes 4) with 1024. exact Ha. }
split; [exact HR1|]. split; [exact HR2|]. split; [exact HR3|]. split; [exact Hcap | exact Hnull].
Qed.

(* the real frame lies in the stack, below 2^47 *)
Lemma hbe_start_R : forall (cx : hsu_scx rsegs) r ev, @hqu_start_M03 fx rc SK rsegs B cx r ev ->
0 < e_R (x_e rsegs cx) /\ e_R (x_e rsegs cx) + 0x220 <= 2 ^ 47 /\ e_R (x_e rsegs cx) mod 32 = 0.
Proof.
intros cx r ev HS. pose proof (hbe_start_pre cx r ev HS) as Hpre.
destruct Hpre as (HJ & _ & _ & _ & _ & HeS & HRal & HRS & HstkR & _).
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & HSTK & Hc1 & Hc2 & Hc3 & Hc4 & _).
pose proof (@alloc_ceiling_val rc) as [[Hc0 _] _].
cbn [hi_rsz headamp_himg_B] in HRS.
unfold T_SEG_STK, ASTACK in *. lia.
Qed.

(* a block live at the segment's start: below the ceiling, in application memory, apart from F *)
Lemma hbe_blk : forall (cx : hsu_scx rsegs) sh p n, hsu_pre rsegs B headamp_himg_B cx sh ->
In (p, n) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
(p + req_size n <= e_F (x_e rsegs cx) \/ e_F (x_e rsegs cx) + 1024 <= p).
Proof.
intros cx sh p n HP Hin.
destruct (hbe_seg cx sh HP) as (Hfin & _ & HF & _).
pose proof HP as (HJ & _).
pose proof HJ as (HAR & _).
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _).
destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (Hpw & _).
pose proof (hbe_pairwise_app zdisjoint _ _ (p, req_size n) (e_F (x_e rsegs cx), 1024) Hpw) as HD.
assert (H1 : In (p, req_size n) (map (fun b => (fst b, req_size (snd b))) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx))))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (p, n)); exact Hin).
assert (H2 : In (e_F (x_e rsegs cx), 1024)
  (map (fun f => (frame_addr (x_lyc rsegs cx) (fst f) (snd f), fs_frame_bytes (fst f))) (frames (x_Sc rsegs cx)))).
{ rewrite HF. change 1024 with (fs_frame_bytes (fst (4, x_pos rsegs cx))).
  apply (in_map (fun f => (frame_addr (x_lyc rsegs cx) (fst f) (snd f), fs_frame_bytes (fst f))) _ (4, x_pos rsegs cx)).
  exact Hfin. }
specialize (HD H1 H2). unfold zdisjoint in HD. cbn [fst snd] in HD.
split; [exact H4096|]. split; [exact Hceil|]. split; [exact Happ | exact HD].
Qed.

(* the checks' base at a state that differs from a cut's only in its registers and its I/O-equal model *)
Lemma hbe_base3_regs : forall (cx : hsu_scx rsegs) (fx2 : YK11.FPState) r sh ly2 S2 W2 regs2 mem2 md2 regs3 md3,
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem2 md3 (x_k rsegs cx) ->
same_io md2 md3 ->
(forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs3 mem2 md3.
Proof.
intros cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 regs3 md3 (Hcore & Hrest) HJ3 Hio3 H234'.
split; [|exact Hrest].
unfold hsu_core, hsu_mid in Hcore |- *.
destruct Hcore as (_ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
split; [exact HJ3|].
split; [intros q Hq; rewrite (H234' q Hq); exact (H234 q Hq)|].
split; [exact Hfr|]. split; [exact Hperm|]. split; [exact (same_io_trans _ _ _ Hio Hio3)|].
split; [exact Hmo | exact Hkeep].
Qed.

(* ======================================= the frame of facts across a run and a call ======================================= *)
Lemma hbe_hc_core : forall (cx : hsu_scx rsegs) sh E ly2 S2 W2 regs2 mem2 md2,
hsu_pre rsegs B headamp_himg_B cx sh -> hsu_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx)
  ly2 S2 W2 mem2 md2 regs2 (e_R (x_e rsegs cx)).
Proof.
intros cx sh E ly2 S2 W2 regs2 mem2 md2 HP Hcore.
pose proof HP as (_ & Hev & H2 & H3 & H4 & HS & Hal & Hrsz & Hwin & _).
destruct Hcore as (HJ & Hr234 & _).
cbn [hi_rsz headamp_himg_B] in Hrsz.
unfold hc_core. split; [exact HJ|]. split; [exact Hev|].
split; [rewrite <- H2; exact (Hr234 2 (or_introl eq_refl))|].
split; [rewrite <- H3; exact (Hr234 3 (or_intror (or_introl eq_refl)))|].
split; [rewrite <- H4; exact (Hr234 4 (or_intror (or_intror eq_refl)))|].
assert (Hal16 : e_R (x_e rsegs cx) mod 16 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ 32); [exists 2; reflexivity | apply Z.mod_divide; [lia | exact Hal]]. }
split; [exact Hal16|]. split; [exact Hwin | lia].
Qed.

(* after a call of one of headamp's own functions (HPgCalls' adapters: the callee's stack is [R - T, R)) *)
Lemma hbe_core_call : forall (cx : hsu_scx rsegs) sh E T ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
hsu_pre rsegs B headamp_himg_B cx sh -> hsu_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 -> 0 <= T <= T_SEG_STK ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx)
  ly3 S3 W3 mem3 md3 regs3 (e_R (x_e rsegs cx)) ->
aregs_preserved regs2 regs3 -> frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T <= y < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 y = aview rsegs (w_H W2) mem2 y) ->
hsu_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx sh E T ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HP Hcore HT HC3 Hpres Hfr Hperm Hio Hmo Hkeep.
destruct (hbe_seg cx sh HP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp & _).
destruct Hcore as (HJ & Hr234 & Hfr2 & Hperm2 & Hio2 & Hmo2 & Hmem2).
destruct HC3 as (HJ3 & _).
split; [exact HJ3|].
split; [intros r0 Hr0; rewrite <- (Hr234 r0 Hr0); apply Hpres; unfold acallee_saved; lia|].
split; [rewrite Hfr; exact Hfr2|].
split; [exact (Permutation_trans Hperm Hperm2)|].
split; [exact (same_io_trans _ _ _ Hio2 Hio)|].
split; [exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo2 Hmo)|].
intros a Ha Hs He. rewrite Hsp in Hs.
rewrite (Hkeep a Ha ltac:(unfold T_SEG_STK, ASTACK in *; lia)). exact (Hmem2 a Ha ltac:(rewrite Hsp; exact Hs) He).
Qed.

(* after a block of straight-line code whose post has HPgSteps.hdu_blk_postE's clauses, writing only inside E *)
Lemma hbe_core_blk : forall (cx : hsu_scx rsegs) E (Wr : Z -> Prop) (clob : list (bv 5))
ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
hsu_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 mem3 md3 (x_k rsegs cx) ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs3 r = getr regs2 r) ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> ~ In (Z_to_bv 5 r) clob) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
(forall a, Wr a -> E a) ->
hsu_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx E Wr clob ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hcore HJ3 Hkr Hcl Hfr Hperm Hio Hmo Hkeep HWE.
destruct Hcore as (HJ & Hr234 & Hfr2 & Hperm2 & Hio2 & Hmo2 & Hmem2).
split; [exact HJ3|].
split.
{ intros r0 Hr0. rewrite <- (Hr234 r0 Hr0). apply Hkr; [|exact (Hcl r0 Hr0)].
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  destruct Hr0 as [ -> | [ -> | -> ] ]; vm_compute; discriminate. }
split; [rewrite Hfr; exact Hfr2|].
split; [exact (Permutation_trans Hperm Hperm2)|].
split; [exact (same_io_trans _ _ _ Hio2 Hio)|].
split; [exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo2 Hmo)|].
intros a Ha Hs He. rewrite (Hkeep a Ha (fun HW => He (HWE a HW))). exact (Hmem2 a Ha Hs He).
Qed.

(* ======================================= what a cut carries, across writes to x ======================================= *)
(* the bytes the two pieces and the callees they call may write: the callees' stack, x, and x's shadow granules *)
Definition hbe_wz (cx : hsu_scx rsegs) (a : Z) : Prop :=
(e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) \/
(e_F (x_e rsegs cx) + HQU_XO <= a < e_F (x_e rsegs cx) + HQU_XO + 136) \/
(shadow_addr (e_F (x_e rsegs cx)) + 88 <= a < shadow_addr (e_F (x_e rsegs cx)) + 105).

(* M03's write set holds every byte of hbe_wz but the callees' stack *)
Lemma hbe_wz_E3 : forall (cx : hsu_scx rsegs) a,
(e_F (x_e rsegs cx) + HQU_XO <= a < e_F (x_e rsegs cx) + HQU_XO + 136) \/
(shadow_addr (e_F (x_e rsegs cx)) + 88 <= a < shadow_addr (e_F (x_e rsegs cx)) + 105) ->
hqu_E3 rsegs B cx a.
Proof.
intros cx a Ha. unfold hqu_E3. left. unfold hd_inw. cbn [hi_w3 headamp_himg_B]. apply Exists_exists.
unfold HQU_XO in Ha. destruct Ha as [Ha|Ha].
- exists (XF 0, 0x2a0, 0xa8). split; [cbn [In]; left; reflexivity|]. cbn [fst snd hd_xv]. lia.
- exists (XShF, 0x54, 0x15). split; [cbn [In]; right; left; reflexivity|]. cbn [fst snd hd_xv]. lia.
Qed.

(* F's shadow bytes lie in the shadow band, far below kHighMemBeg *)
Lemma hbe_fsh_rng : forall (cx : hsu_scx rsegs) sh, hsu_pre rsegs B headamp_himg_B cx sh ->
0x7fff8000 <= shadow_addr (e_F (x_e rsegs cx)) /\ shadow_addr (e_F (x_e rsegs cx)) + 128 <= 0x10007fef8080.
Proof.
intros cx sh HP.
destruct (hbe_seg cx sh HP) as (_ & _ & _ & _ & HF4 & HFc & _).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
assert (Hd1 : 0 <= e_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia).
assert (Hd2 : e_F (x_e rsegs cx) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
assert (Hd3 : 0x7fffff800000 / 8 = 0xffffff00000) by reflexivity. rewrite Hd3 in Hd2.
unfold shadow_addr, SHADOW_OFF. lia.
Qed.

(* a range in application memory below the ceiling and apart from F avoids hbe_wz *)
Lemma hbe_wz_app : forall (cx : hsu_scx rsegs) sh p n a, hsu_pre rsegs B headamp_himg_B cx sh ->
in_app p n -> p + n <= alloc_ceiling -> (p + n <= e_F (x_e rsegs cx) \/ e_F (x_e rsegs cx) + 1024 <= p) ->
p <= a < p + n -> ~ hbe_wz cx a.
Proof.
intros cx sh p n a HP Happ Hc Hd Ha.
destruct (hbe_seg cx sh HP) as (_ & _ & _ & _ & HF4 & HFc & HFapp & _ & HR & _).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
pose proof (hbe_fsh_rng cx sh HP) as Hb.
unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold hbe_wz, HQU_XO. unfold T_SEG_STK, ASTACK in *.
intros [H|[H|H]]; lia.
Qed.

(* a byte of the image avoids hbe_wz *)
Lemma hbe_wz_img : forall (cx : hsu_scx rsegs) sh a, hsu_pre rsegs B headamp_himg_B cx sh -> in_img rsegs a ->
~ hbe_wz cx a.
Proof.
intros cx sh a HP Hi.
destruct (hbe_seg cx sh HP) as (_ & _ & _ & _ & HF4 & HFc & _ & HFimg & HR & _).
pose proof (HPgSteps.img_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
pose proof (hbe_fsh_rng cx sh HP) as Hb.
unfold hbe_wz, HQU_XO. unfold T_SEG_STK, ASTACK in *.
intros [H|[H|H]]; [lia | exact (HFimg a ltac:(lia) Hi) | lia].
Qed.

(* res, F + 0x2a0 .. F + 0x2ac, avoids hbe_wz *)
Lemma hbe_wz_res : forall (cx : hsu_scx rsegs) sh a, hsu_pre rsegs B headamp_himg_B cx sh ->
e_F (x_e rsegs cx) + HQU_RES <= a < e_F (x_e rsegs cx) + HQU_RES + 12 -> ~ hbe_wz cx a.
Proof.
intros cx sh a HP Ha.
destruct (hbe_seg cx sh HP) as (_ & _ & _ & _ & HF4 & HFc & HFapp & _ & HR & _).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
pose proof (hbe_fsh_rng cx sh HP) as Hb.
unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. unfold HQU_RES in Ha. unfold hbe_wz, HQU_XO.
unfold T_SEG_STK, ASTACK in *.
intros [H|[H|H]]; lia.
Qed.

(* the real-frame cells [R, R + 0x160) avoid hbe_wz *)
Lemma hbe_wz_R : forall (cx : hsu_scx rsegs) sh a, hsu_pre rsegs B headamp_himg_B cx sh ->
e_R (x_e rsegs cx) <= a < e_R (x_e rsegs cx) + 0x160 -> ~ hbe_wz cx a.
Proof.
intros cx sh a HP Ha.
destruct (hbe_seg cx sh HP) as (_ & _ & _ & _ & HF4 & HFc & HFapp & _ & HR & _).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
pose proof (hbe_fsh_rng cx sh HP) as Hb.
unfold hbe_wz, HQU_XO. unfold T_SEG_STK, ASTACK in *.
intros [H|[H|H]]; lia.
Qed.

(* a garr8 fact over bytes that avoid hbe_wz, carried *)
Lemma hbe_garr8_kept : forall (cx : hsu_scx rsegs) (W2 W3 : world rsegs) mem2 mem3 a (l : list byte),
garr8 rsegs (mrestrict (w_H W2) mem2) a (hd_zbytes l) ->
(forall y, 0 <= y < 2 ^ 64 -> ~ hbe_wz cx y -> aview rsegs (w_H W3) mem3 y = aview rsegs (w_H W2) mem2 y) ->
(forall y, a <= y < a + Z.of_nat (length l) -> 0 <= y < 2 ^ 64 /\ ~ hbe_wz cx y) ->
garr8 rsegs (mrestrict (w_H W3) mem3) a (hd_zbytes l).
Proof.
intros cx W2 W3 mem2 mem3 a l Hg Hk Hd.
apply (proj1 (hm_bytes_zbytes rsegs (w_H W3) mem3 a l)).
apply (hm_bytes_kept rsegs (w_H W2) mem2); [exact (proj2 (hm_bytes_zbytes rsegs (w_H W2) mem2 a l) Hg)|].
intros y Hy. destruct (Hd y Hy) as [Hr Hn]. exact (Hk y Hr Hn).
Qed.

Lemma hbe_base3_kept : forall (cx : hsu_scx rsegs) (r : Model.pod_rec) ev (fx2 fx3 : YK11.FPState) sh sh'
ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
hsu_core rsegs B MT cx (hqu_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ hbe_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
hsu_fsh_at rsegs cx W3 mem3 sh' -> @hqu_fxk fx fx3 ->
@hqu_base3 fx rc SK rsegs B MT cx fx3 r sh' ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx r ev fx2 fx3 sh sh' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HS Hb Hcore3 Hk Hfsh Hfx.
pose proof HS as (HP & _ & Hwf & Hlen & _ & _ & Hpodb & _ & _ & _ & _ & Houtb & _).
pose proof HP as HP0.
pose proof HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcap & _ & _ & _ & _ & _ & _ & _ & _ & Hppb).
destruct Hb as (_ & _ & _ & Hrom & Hpp & Hpod & Hout & Hres & (ev2 & Herr)).
destruct Hppb as (_ & Hppin & _). destruct Hpodb as (_ & Hpodin & _). destruct Houtb as (_ & Houtin & _).
destruct (hbe_blk cx _ _ _ HP Hppin) as (Hpp4 & Hppc & Hppa & Hppd).
destruct (hbe_blk cx _ _ _ HP Hpodin) as (Hpod4 & Hpodc & Hpoda & Hpodd).
destruct (hbe_blk cx _ _ _ HP Houtin) as (Hout4 & Houtc & Houta & Houtd).
destruct (hbe_seg cx _ HP) as (_ & _ & _ & _ & HF4 & HFc & _).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
destruct (hbe_ans_ok cx r Hcap) as (_ & _ & Hlc).
assert (Hreq : forall n, 0 <= n -> n <= req_size n) by (intros n Hn; unfold req_size; destruct (Z.eqb_spec n 0); lia).
split; [exact Hcore3|]. split; [exact Hfx|]. split; [exact Hfsh|].
split.
{ apply (hm_rom_kept rsegs W2 W3 mem2 mem3 Hrom).
  intros a (sg & Hin & _ & Hsb).
  assert (Himg : in_img rsegs a) by (exists sg; split; [exact Hin | exact Hsb]).
  pose proof (HPgSteps.img_segs_low a Himg) as Hlow. unfold kLowMemEnd in Hlow.
  exact (Hk a ltac:(lia) (hbe_wz_img cx _ a HP Himg)). }
split.
{ unfold hsu_pp_at in *. apply (hbe_garr8_kept cx W2 W3 mem2 mem3 _ _ Hpp Hk).
  rewrite (Layout.length_pp_bytes r Hwf). intros y Hy.
  assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hppc, Hppa, Hppd.
  split; [lia|]. exact (hbe_wz_app cx _ _ _ y HP Hppa Hppc Hppd Hy). }
split.
{ apply (hbe_garr8_kept cx W2 W3 mem2 mem3 _ _ Hpod Hk). rewrite <- Hlen. intros y Hy.
  pose proof (Hreq (e_len (x_e rsegs cx)) ltac:(lia)) as Hq.
  split; [lia|]. exact (hbe_wz_app cx _ _ _ y HP Hpoda Hpodc Hpodd ltac:(lia)). }
split.
{ apply (hbe_garr8_kept cx W2 W3 mem2 mem3 _ _ Hout Hk). rewrite length_ha_cells_bytes. intros y Hy.
  pose proof (Hreq (3 * (e_cap (x_e rsegs cx) + 1)) ltac:(lia)) as Hq.
  split; [lia|]. exact (hbe_wz_app cx _ _ _ y HP Houta Houtc Houtd ltac:(lia)). }
split.
{ apply (hbe_garr8_kept cx W2 W3 mem2 mem3 _ _ Hres Hk). unfold ans_res_bytes. rewrite length_ha_res_bytes.
  intros y Hy. split; [unfold HQU_RES in *; lia|]. exact (hbe_wz_res cx _ y HP Hy). }
exists ev2. intros j Hj.
pose proof errno_low as ((He0 & He1) & Heimg & _). unfold kLowMemEnd in He1.
assert (Hj' : 0 <= Z.of_nat j < 4) by (split; [apply Nat2Z.is_nonneg | apply (Nat2Z.inj_lt j 4); exact Hj]).
assert (Hi : in_img rsegs (as_errno B + Z.of_nat j)) by (apply Heimg; lia).
assert (Hb : 0 <= as_errno B + Z.of_nat j < 2 ^ 64) by lia.
rewrite (Hk _ Hb (hbe_wz_img cx _ _ HP Hi)). exact (Herr j Hj).
Qed.

End d.
End c.
