(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_entry.v, with its module paths and module names changed; 3268 of its 3420 lines of code are new or changed and 1413 lines of the source are left out. *)
(* Theorem Labs, 2026-10: segment PI_O_LOOP of parse_items' image-B walk.
   Block: PI_O_LOOP (0x87b70 .. 0x87bb8), the member loop's head: a0 = v, the grow call, the refusal test and
   the frame cache the loop body reads (pi_regs_body). It stops at PI_O_BODY (0x87bbc), which is PItems_body.v's.
   The pres and the specs are in lib/B/Prog/PItems_pres.v; this file holds only lemmas and the Section
   hypotheses of its neighbours and callees. The Section preamble is PItems_body.v's, verbatim.
   Rule 24: proves no function (kind: segment lemma of an existing walk; the top theorem that proves parse_items is
   in another file).
   THE RESULT: pi_loop_holds (section 5), `(forall N, pi_body_spec d CTX0 CW N) -> pi_loop_spec d CTX0 CW`: pi_loop_pre
   fixes the cursor pc inside an existential, so the cut is taken at N := length (rest_atR tb text pc).
   KIT: the batch kit 240b06ed4fd4 (form (b), POST-IMPLICATION): no rp_* binders; the ledger's most / own (the entry's)
   POST-IMPLICATION): no rp_* binders; the ledger's most / own (the entry's) ride in every prh_ledger / pi_cur / pi_post;
   the prefix's travelling facts are PItems_posb.v's pi_posb / pi_live, extended at the grow call by tgrow_specX's per-arm
   live requests and position implication (pil_s_trav), and grow's two live-count premises come from pi_ent's by
   PItems_value_model.v's pvm_lc_call. PIL_HEAD (cf_head = PresetReqAt.HEAD) is the instance's, in sections 4 and 5.
   THE JOURNAL: the spec binds the BUDGETED journal at WS0, at the world relation wle' segs RZ_cf (pi_ajR .. WS0, wbudget CW 0
   WS0; grow frees, YA0nH): the run and the unbudgeted grow call (aj_call_xW_spR) take it rebased (ajournal_xw_rebaseR),
   every exit steps back to WS0 (ajournal_xw_unbase0R), grow stores no wild trace, so the budget at both exits is WS0's.
   THE HULL: grow's hull budget is pi_ent's, paid by the block's use (PItems_posb.pi_posb_budget); its post's use extends
   pi_posb on the continuing arms and gives the refused post's (pi_posb_hull_call). The loop invariants pi_grant /
   cap = ncap n / pi_ncaps / pi_forder with pi_fl_eq go through the step to pi_body_pre's tail, or into the text's post at
   a refusal (built through PRH_FnParse.tpiP_R): its OUTCOME and its injected reading (grow's exclusions at a refused
   arm, the chosen failure's call otherwise), the ledger move (pvm_ledger_app) and the partial free order (PItems_forder).
   Sections: 1 the value shapes the block computes; 2 PjGrammar.grow's two shapes; 3 pj_fdR up to permutation;
   4 THE GROW-POST STEP pil_grow_step, machine-free, SHARED WITH PItems_value_sep.v (its grow2 at 0x87e14 calls the same
   grow): from pi_loop_pre's existential data at the call state, tgrow_specX's post at the return state and what the
   caller's journal kept, EITHER pi_body_pre's existential data at the return state (a0 = 0) OR the kit's refused post
   (a0 = -1), all seven arms of tgrow_specX (its tgrP_R records); 5 the walk at wle': the call (aj_call_xW_spR), what
   it kept (pil_kdi, pil_newv, pil_kcur by PItems_kept.v's pi_cur_kept_callR), the return site (pil_ret_run), the
   readers across the cache stores (pil_cur_agr, pvm_ncaps_frame / pvm_forder_frame), and pi_loop_holds.

   THE BLOCK, instruction by instruction (the neutral listing, the internal file parse_items.fuzz_preset.asan-ubsan.s, lines 80-98):
     0x87b70 mv a0,s3            a0 = v
     0x87b74 jal grow            the kit's tgrow_specX (a WINDOW post fpostW: aj_call_xW at e1 = PI_FRAME + e)
     0x87b78 bnez a0 -> PI_O_EPI grow refused / failed: the function returns -1 through the epilogue
     0x87b7c li a0,1 ; 0x87b8c slli a0,a0,0x3c ; 0x87b90 sd a0,0(sp)        [sp]      = 2 ^ 60
     0x87b80 addi a1,s3,32 ; 0x87ba0 sd a1,16(sp)                           [sp + 16] = v + 32   (keys)
     0x87ba4 srli a1,a1,3 ; 0x87bb4 add a1,a1,s10 ; 0x87bb8 sd a1,8(sp)     [sp + 8]  = sh (v + 32)
     0x87b88 addi a2,s3,24 ; 0x87b94 sd a2,32(sp)                           [sp + 32] = v + 24   (kids)
     0x87b98 srli a0,a2,3 ; 0x87ba8 add a0,a0,s10 ; 0x87bac sd a0,24(sp)    [sp + 24] = sh (v + 24)
     0x87b84 addi s6,s3,40                                                  s6 = v + 40
     0x87b9c srli s8,s6,3 ; 0x87bb0 add s8,s8,s10                           s8 = sh (v + 40)
   which is exactly PItems_defs.v's pi_regs_body. There is NO load and NO UBSan check branch in the range: the
   only branch is the grow-refusal test at 0x87b78, and the five stores are to the function's own frame.

   Numerals: 3, 4, 8, 16, 24, 32, 40, 48, 56, 64 and 4096 are LENGTHs (field offsets, the cache cells, the shift that
   divides by the ASan granule, the alignment exponent of sp, a page / ESTACK); 5 and 6 are WORDs (the node types
   array / object) and 12 is a WORD (ENOMEM, inside tgrow_specX's post copied verbatim); 2 ^ 46, 2 ^ 47, 2 ^ 54,
   2 ^ 60 (written once as 1152921504606846976, the run's literal) and 2 ^ 64 are DERIVED. No ADDRESS in code: every
   pc is PI_AT PI_O_* at the image-B listing instance (the hex numbers above are comments). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs PItems_pres.
(* beyond PItems_body.v's preamble: the granted-trace charge (prhPv_rk) the room clauses name, and the pure model
   and shape layers of parse_items' walk (PItems_shape.v: the R port of the plain shape lemmas; PItems_value_model.v:
   segment VALUE's trace / ledger / room lemmas, taken by path as PItems_value_model.v (sha256 5a66754fe8f9; internal record)) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Charge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_model PItems_shape PItems_value_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_agr PItems_kept.
(* the batch's travelling facts: memnorm and its runner laws (YSRrMemnorm is override-free), the run position *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
(* The batch kit (the kit's batch 240b06ed4fd4): the order-list layer (PRH_PjOrder), the granted-prefix and ledger tools (PItems_ledk1),
   granted-prefix and ledger tools (PItems_ledk1), the ordered exit lemmas (PItems_forder) and the capacity frame (PvB_Frees, by path) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_ledk1 PItems_forder PvB_Frees.
(* THE RE-HIDING MOVE and THE HULL: the walk runs at the world relation wle' segs RZ_cf (YA0nH; the branch and bind
   over R, YSRrG), since grow frees; the hull budget and use (PresetHullBudget) *)
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
(* 1. The three value shapes the block computes, as the symbolic engine leaves them.                   *)
(*                                                                                                     *)
(* srli by 3 of a register offset is NOT folded by YP0e's srl_lin (its lin_divisible test asks the     *)
(* COEFFICIENT to be a multiple of 8, and the coefficient of a register is 1), so the engine leaves    *)
(* SAlu ALU_SRL (SOff n c) (SLit 3) and the walk denotes it here. The 8-alignment of the register is   *)
(* a fact about its VALUE, which these lemmas take as a premise.                                       *)
(* ================================================================================================== *)

(* an `addi rd, rs, c`: the register's value plus the offset *)
Lemma pil_sv_off : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = w64 (x + c).
Proof.
intros E n x c H Hx Hc. apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia.
exact (U_atom_off E n x c H Hx Hc).
Qed.

(* the `add rd, rd, s10` that turns a granule index into its shadow address: pi_sh of the address *)
Lemma pil_sv_sh : forall E n m x c, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 SHADOW_OFF ->
  0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 -> SHADOW_OFF + (x + c) / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = w64 (pi_sh (x + c)).
Proof.
intros E n m x c Hn Hm Hx Hc Hsh.
assert (Hq : 0 <= (x + c) / 8 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.le_lt_trans with (x + c); [apply Z.div_le_upper_bound; lia | lia]]).
assert (HS0 : 0 <= SHADOW_OFF < 2 ^ 64) by (unfold SHADOW_OFF; lia).
assert (Hsrl : U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (x + c) / 8).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E n x c Hn Hx Hc), U_SLit.
  rewrite (zcanon_id 3) by (unfold M64; lia).
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 3) with 8. apply zcanon_id. unfold M64. lia. }
assert (HU : U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = SHADOW_OFF + (x + c) / 8).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E m SHADOW_OFF Hm HS0), Hsrl.
  rewrite zcanon_id by (unfold M64; lia). lia. }
apply bv_eq. unfold w64, pi_sh.
rewrite unsigned_lit_small by (unfold SHADOW_OFF in *; lia). exact HU.
Qed.

(* ================================================================================================== *)
(* 2. PjGrammar.grow (PjGrammar.v:221-226), the model side of the call: its two shapes.                *)
(* The machine's arm decides which; the booleans the model consumes are take's, one per realloc.       *)
(* ================================================================================================== *)

(* room left: nothing is done, the cap is unchanged and no event is made *)
Lemma pil_grow_lt : forall (o : bool) (n cap : nat) (ok : list bool), (n < cap)%nat ->
  PjGrammar.grow o n cap ok = (Some cap, [], ok).
Proof.
intros o n cap ok H. unfold PjGrammar.grow.
rewrite (proj2 (Nat.ltb_lt n cap) H). reflexivity.
Qed.

(* the array is full: the kids realloc, and for an object the keys realloc, at the doubled cap *)
Lemma pil_grow_ge : forall (o : bool) (n cap : nat) (ok : list bool), (cap <= n)%nat ->
  PjGrammar.grow o n cap ok =
  jbind (jrealloc (56 * cap) (56 * (if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat)))
    (fun _ => if o
              then jbind (jrealloc (8 * cap) (8 * (if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat)))
                     (fun _ => jret (if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat))
              else jret (if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat)) ok.
Proof.
intros o n cap ok H. unfold PjGrammar.grow.
rewrite (proj2 (Nat.ltb_ge n cap) H). reflexivity.
Qed.

(* the model's new cap on every arm that returns 0, in the shape PRH_FnReader's tgrow_specX reports it
   (cap2R is over Z, grow's cap' over nat) *)
Lemma pil_cap2R : forall cap : nat, cap2R (Z.of_nat cap) = Z.of_nat (if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat).
Proof.
intros cap. unfold cap2R. destruct cap as [|c]; cbn [Nat.eqb]; [reflexivity|].
rewrite (proj2 (Z.eqb_neq (Z.of_nat (S c)) 0)) by lia. lia.
Qed.

(* grow's doubled cap (PjGrammar.v:224) *)
Definition pil_c2 (cap : nat) : nat := if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat.

(* grow's five model runs from a full array, one per arm of tgrow_specX that reaches a realloc: the booleans are
   take's, one per realloc (PjGrammar.v:193-199) *)
Lemma pil_grow_arr_ok : forall (n cap : nat) ok, (cap <= n)%nat ->
  PjGrammar.grow false n cap (true :: ok) = (Some (pil_c2 cap), [EGrow (56 * cap) (56 * pil_c2 cap)], ok).
Proof. intros n cap ok H. rewrite pil_grow_ge by exact H. reflexivity. Qed.

Lemma pil_grow_arr_no : forall (n cap : nat) ok, (cap <= n)%nat ->
  PjGrammar.grow false n cap (false :: ok) = (None, [EFail (56 * pil_c2 cap)], ok).
Proof. intros n cap ok H. rewrite pil_grow_ge by exact H. reflexivity. Qed.

Lemma pil_grow_obj_ok : forall (n cap : nat) ok, (cap <= n)%nat ->
  PjGrammar.grow true n cap (true :: true :: ok) =
  (Some (pil_c2 cap), [EGrow (56 * cap) (56 * pil_c2 cap); EGrow (8 * cap) (8 * pil_c2 cap)], ok).
Proof. intros n cap ok H. rewrite pil_grow_ge by exact H. reflexivity. Qed.

Lemma pil_grow_obj_no1 : forall (n cap : nat) ok, (cap <= n)%nat ->
  PjGrammar.grow true n cap (false :: ok) = (None, [EFail (56 * pil_c2 cap)], ok).
Proof. intros n cap ok H. rewrite pil_grow_ge by exact H. reflexivity. Qed.

Lemma pil_grow_obj_no2 : forall (n cap : nat) ok, (cap <= n)%nat ->
  PjGrammar.grow true n cap (true :: false :: ok) =
  (None, [EGrow (56 * cap) (56 * pil_c2 cap); EFail (8 * pil_c2 cap)], ok).
Proof. intros n cap ok H. rewrite pil_grow_ge by exact H. reflexivity. Qed.

Lemma pil_jbind_some : forall (A Bt : Type) (m : M A) (kk : A -> M Bt) ok a t ok1 r t' ok2,
  m ok = (Some a, t, ok1) -> kk a ok1 = (r, t', ok2) -> jbind m kk ok = (r, t ++ t', ok2).
Proof. intros A Bt m kk ok a t ok1 r t' ok2 H1 H2. unfold jbind. rewrite H1, H2. reflexivity. Qed.

Lemma pil_jbind_none : forall (A Bt : Type) (m : M A) (kk : A -> M Bt) ok t ok1,
  m ok = (None, t, ok1) -> jbind m kk ok = (None, t, ok1).
Proof. intros A Bt m kk ok t ok1 H1. unfold jbind. rewrite H1. reflexivity. Qed.

(* ================================================================================================== *)
(* 3. The refused exit: pj_fdR only constrains its block list up to order, so a walk may hand it the   *)
(* ledger's D0 (pi_loop_pre keeps D0 as a PERMUTATION of the slot blocks and the members' blocks).     *)
(* ================================================================================================== *)
Section pure. Variable segs : list Segment.

Lemma pil_fshape_perm : forall m lblk Pi p D D', Permutation D D' ->
  pj_fshapeR segs m lblk Pi p D -> pj_fshapeR segs m lblk Pi p D'.
Proof.
intros m lblk Pi p D D' HP HF.
destruct HF as (HN & HA & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Hh & Hs & Hk & Hy & HPm & HPi).
split; [ first [ eapply Permutation_NoDup; [exact HP | exact HN]
               | apply NoDup_ListNoDup; eapply Permutation_NoDup;
                 [exact HP | apply NoDup_ListNoDup; exact HN] ] |].
split.
- intros b x Hb Hx. eapply HA; [| exact Hx].
  eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hb].
- exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
  split; [exact Hh|]. split; [exact Hs|]. split; [exact Hk|]. split; [exact Hy|].
  split; [| exact HPi].
  eapply Permutation_trans; [apply Permutation_sym; exact HP | exact HPm].
Qed.

Lemma pil_fd_perm : forall m lblk d p D D', Permutation D D' ->
  pj_fdR segs m lblk d p D -> pj_fdR segs m lblk d p D'.
Proof.
intros m lblk d p D D' HP H. destruct d as [|d']; cbn [pj_fdR] in H |- *;
  exact (pil_fshape_perm m lblk _ p D D' HP H).
Qed.

End pure.

(* ================================================================================================== *)
(* 4. THE GROW-POST STEP, machine-free (shared with PItems_value_sep.v's grow2 at 0x87e14).           *)
(* ================================================================================================== *)
Section gs. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the cap grow leaves on its GRANTED run (ok = []): cap when a slot is free, else the doubled cap *)
Definition pil_gcap (n cap : nat) : nat :=
  if Nat.ltb n cap then cap else (if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat).

(* grow's granted run (ok = []: take answers true) ends at pil_gcap with its own granted trace *)
Lemma pil_grow_granted : forall (o : bool) (n cap : nat),
  PjGrammar.grow o n cap [] = (Some (pil_gcap n cap), snd (fst (PjGrammar.grow o n cap [])), []).
Proof.
intros o n cap. unfold pil_gcap. destruct (Nat.ltb_spec n cap) as [Hl|Hl].
- rewrite (pil_grow_lt o n cap [] Hl). reflexivity.
- rewrite (pil_grow_ge o n cap [] Hl). destruct o; reflexivity.
Qed.

(* jrl's granted trace at a loop head is grow's granted trace, then the member's (pi_jrb at the granted cap) *)
Lemma pil_gt_split : forall f' D (o : bool) (n cap : nat) accr y,
  snd (fst (jrl prh_jr_strtod (Nat.succ f') D o n cap accr y [])) =
  PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap) ++
  snd (fst (pi_jrb f' D o n (pil_gcap n cap) accr y [])).
Proof.
intros f' D o n cap accr y. rewrite pi_jrl_unfold. unfold PRH_Charge.prhPg_gtrace. rewrite !Nat2Z.id.
destruct (pi_jrb f' D o n (pil_gcap n cap) accr y []) as [[r t] ok2] eqn:Ej.
rewrite (pil_jbind_some nat (jv * list Z) (PjGrammar.grow o n cap) (fun cap1 => pi_jrb f' D o n cap1 accr y)
  [] (pil_gcap n cap) (snd (fst (PjGrammar.grow o n cap []))) [] r t ok2 (pil_grow_granted o n cap) Ej).
reflexivity.
Qed.

(* a grow arm that returns 0 moves the run equation from jrl to the member's body pi_jrb *)
Lemma pil_runB : forall d (o : bool) x0 ok0 tr0 f' n cap acc y okg g cap',
  pi_run_eq d o x0 ok0 tr0 (Nat.succ f') n cap acc y ->
  (forall ok1, PjGrammar.grow o n cap (okg ++ ok1) = (Some cap', g, ok1)) ->
  pi_run_eqB d o x0 (ok0 ++ okg) (tr0 ++ g) f' n cap' (rev acc) y.
Proof.
intros d o x0 ok0 tr0 f' n cap acc y okg g cap' HR HG ok1 r t ok2 Hj.
rewrite <- !app_assoc. apply HR. rewrite pi_jrl_unfold.
eapply pil_jbind_some; [exact (HG ok1) | exact Hj].
Qed.

(* a grow arm that returns -1 decides the whole call's run: refused, with grow's events last *)
Lemma pil_run_refused : forall d (o : bool) x0 ok0 tr0 f' n cap acc y okr gr,
  pi_run_eq d o x0 ok0 tr0 (Nat.succ f') n cap acc y ->
  PjGrammar.grow o n cap okr = (None, gr, []) ->
  jr_items prh_jr_strtod d o x0 (ok0 ++ okr) = (None, tr0 ++ gr, []).
Proof.
intros d o x0 ok0 tr0 f' n cap acc y okr gr HR HG. apply HR. rewrite pi_jrl_unfold.
eapply pil_jbind_none. exact HG.
Qed.

(* the peak of the prefix and grow's granted events is bounded as the whole call's: the granted run is a run *)
Lemma pil_hpeak_granted : forall d (o : bool) x0 ok0 tr0 f' n cap acc y,
  x0 <> [] -> pi_run_eq d o x0 ok0 tr0 (Nat.succ f') n cap acc y ->
  hpeakR (tr0 ++ PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap)) <=
    224 * Z.of_nat (length x0) + 512 * Z.of_nat (PjGrammar.MAXD - d).
Proof.
intros d o x0 ok0 tr0 f' n cap acc y Hne HR.
destruct (jrl prh_jr_strtod (Nat.succ f') (Nat.succ d) o n cap (rev acc) y []) as [[r t] ok2] eqn:Ej.
pose proof (HR [] r t ok2 Ej) as HI.
pose proof (pvm_hpeak_items d o x0 (ok0 ++ []) r (tr0 ++ t) ok2 Hne HI) as HB.
pose proof (pil_gt_split f' (Nat.succ d) o n cap (rev acc) y) as HS. rewrite Ej in HS. cbn [fst snd] in HS.
rewrite HS, app_assoc in HB.
pose proof (pvm_hpeak_prefix (tr0 ++ PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap))
  (snd (fst (pi_jrb f' (Nat.succ d) o n (pil_gcap n cap) (rev acc) y [])))) as HP.
lia.
Qed.

(* tgrow_specX's post: the text's own PRH_FnReader.tgrP_Q (tgrP_Q_check: it IS the text's post, the Q of its fpostWmR; the
   memnorm keep, fQmn's second conjunct, is the call rule's and stays outside), in this file's argument order. Read it
   through tgrP_R_of and the arm records tgrP_R1 .. tgrP_R7 (tgrP_R1_of .. tgrP_R7_of): its hull use (tgrP_hull), the
   seven arms' live requests and position implications, the two REFUSED arms' OUTCOME exclusions over the all-granted
   list prhPg_evs .. [], and the kids-refused arm's injected-reading exclusion (tgrP3_injected) *)
Definition pil_gpost (ty num str v kids keys n cap : Z) (kb yb : list Z) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
  : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  tgrP_Q B most own ly S Hp W mem v ty num str kids keys n cap kb yb Lam peak cnt fail ran.

(* THE STEP. Inputs: (1) pi_loop_pre's existential data at the call state (the loop head's pi_cur, its grow
   headroom cntc + 2 |rest| + 4, pi_run_eq over acc, the members' depth bound, the prefix's rd_blocks_move, its byte
   bound, ok count and lsum, and the batch kit's loop invariants: the granted prefix pi_grant, cap = ncap n, the members'
   capacities pi_ncaps, the completed slots' free order pi_forder with its model pi_fl_eq), memnorm of the call
   state's memory, and the prefix's two travelling facts (form (b)): pi_posb S Sc tr0 and pi_live over tr0; (2) grow's
   own data: the old slot bytes it was called with, its post Q at the return state (pil_gpost) and its fpostWm memnorm
   keep; (3) the return state's ARx, and what the caller's journal kept: the members' blocks Di, the call's new blocks
   apart from the node, the frames, and the cursor record at the return state for a ledger that keeps the non-slot
   blocks and a counter with the usual headroom. The peak bound of rd_blocks_move across grow is NOT a premise: it is
   pvm_hpeak_items on the granted run (PItems_value_model.v).
   Output: a0 = 0, memnorm at the return state, and pi_body_pre's existential data at the return state (fuel
   f = Nat.succ f', n < cap', pi_posb / pi_live over the extended prefix tr0', and pi_body_pre's batch-kit tail: pi_grant,
   cap' = ncap (S n), pi_ncaps, pi_forder with the model after the grow pi_fl_eqB), OR a0 = -1, memnorm at the return
   state, and the batch kit's post (pi_post: its OUTCOME, the ledger move at the call's all-granted trace, its None arm with
   the partial free order) at the return state for every register file with a0 = -1. most / own are the entry's, kept
   by every text. *)
Definition pil_grow_step_stmt : Prop :=
  forall ly (S : astate) (d : nat) (o : bool) (tb : list Z) (text len p q v e : Z) (regs0 : bvmap 5 word)
    (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (kr : nat)
    lyc Sc Hpc (Wc : world segs) memc (f n cap : nat) (acc : list (list Z * jv)) kids keys Di pc ok0 tr0 D0
    Lamc peakc cntc failc ranc (af : list Z) (kb yb : list Z) ly' S' Hp' (W' : world segs) (regs' : bvmap 5 word) mem'
    (md' : Model),
  (* (1) the call state *)
  YAkMemnorm.memnorm segs memc ->
  pi_cur B regs0 e q v text len tb d lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc most own ->
  cntc + 2 * Z.of_nat (length (rest_atR tb text pc)) + 4 < 2 ^ 64 - 1 ->
  pi_cont (rdW Wc memc) (prh_lin Lamc) o v kids keys n cap acc Di ->
  Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) acc ->
  pj_apartR (pi_sblk o kids keys cap) v ->
  Permutation D0 (pi_sblk o kids keys cap ++ Di) ->
  (2 * length (rest_atR tb text pc) + 2 <= f)%nat ->
  pi_run_eq d o (rest_atR tb text p) ok0 tr0 f n cap acc (rest_atR tb text pc) ->
  (* the entry's text is not empty (pi_ent's opener byte) and the entry counter's headroom (pi_ent's rd_pre and
     its ledger): with PjGrammar.G7_4_items they rule out a wrap of g_count across the prefix and grow *)
  rest_atR tb text p <> [] ->
  0 <= cnt < 2 ^ 64 /\ cnt + 2 * Z.of_nat (length (rest_atR tb text p)) + 2 < 2 ^ 64 - 1 ->
  pi_led Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc ->
  rd_blocks_move B ly S lyc Sc D0 tr0 (rest_atR tb text p) d ->
  PItems_posb.pi_posb S Sc tr0 ->
  PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0 ->
  blocks_bytes Sc <= blocks_bytes S + prh_held tr0 -> length ok0 = PjGrammar.calls tr0 ->
  Ledger.lsum D0 = PjGrammar.held tr0 ->
  rd_room Sc (snd (fst (jrl prh_jr_strtod f (Nat.succ d) o n cap (rev acc) (rest_atR tb text pc) []))) ->
  pi_grant ok0 tr0 -> cap = PresetReqAt.ncap n -> pi_ncaps (rdW Wc memc) kids acc ->
  pi_forder (rdW Wc memc) (prh_lin Lamc) o kids keys n Di acc af ->
  pi_fl_eq d o (rest_atR tb text p) ok0 f n cap af (rest_atR tb text pc) ->
  (* (2) grow *)
  (n = cap -> bytes_at Wc memc kids kb /\ Z.of_nat (length kb) = 56 * Z.of_nat cap /\
     (o = true -> bytes_at Wc memc keys yb /\ Z.of_nat (length yb) = 8 * Z.of_nat cap)) ->
  pil_gpost (if o then 6 else 5) 0 0 v kids keys (Z.of_nat n) (Z.of_nat cap) kb yb
    lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc most own ly' S' Hp' W' regs' mem' md' ->
  (YAkMemnorm.memnorm segs memc -> YAkMemnorm.memnorm segs mem') ->
  (* (3) what the call kept *)
  (forall x, (exists b, In b Di /\ pj_holdsR b x) ->
     mbyte segs (rdW W' mem') x = mbyte segs (rdW Wc memc) x /\
     (writable_at segs (rdW Wc memc) x -> writable_at segs (rdW W' mem') x)) ->
  ARx ly' S' Hp' W' mem' md' ->
  (forall b m x, In (b, m) (ablocks B ly' S') -> ~ In (b, m) (ablocks B lyc Sc) -> b <= x < b + m ->
     ~ (v <= x < v + 56)) ->
  (forall Lam2 peak2 cnt2 fail2 ran2, prh_ledger B ly' S' Hp' W' mem' Lam2 peak2 cnt2 fail2 ran2 most own ->
     (forall a k, In (a, k) Lamc -> ~ In (a, k) (pi_sblk o kids keys cap) -> In (a, k) Lam2) ->
     (forall a k, In (a, k) Lam2 -> In (a, k) Lamc \/ ~ In (a - cf_head, k + cf_head) (ablocks B lyc Sc)) ->
     cnt2 + 2 * Z.of_nat (length (rest_atR tb text pc)) + 2 < 2 ^ 64 - 1 ->
     pi_cur B regs0 e q v text len tb d ly' S' Hp' W' mem' pc Lam2 peak2 cnt2 fail2 ran2 most own) ->
  Permutation (frames S') (frames Sc) ->
  (* the step *)
  (getr regs' 10 = w64 0 /\ YAkMemnorm.memnorm segs mem' /\
   exists (f' cap' : nat) kids' keys' ok0' tr0' D0' Lam' peak' cnt' fail' ran',
     f = Nat.succ f' /\
     pi_cur B regs0 e q v text len tb d ly' S' Hp' W' mem' pc Lam' peak' cnt' fail' ran' most own /\
     (n < cap')%nat /\
     pi_cont (rdW W' mem') (prh_lin Lam') o v kids' keys' n cap' acc Di /\
     Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) acc /\
     pj_apartR (pi_sblk o kids' keys' cap') v /\
     Permutation D0' (pi_sblk o kids' keys' cap' ++ Di) /\
     (2 * length (rest_atR tb text pc) + 1 <= f')%nat /\
     pi_run_eqB d o (rest_atR tb text p) ok0' tr0' f' n cap' (rev acc) (rest_atR tb text pc) /\
     pi_led Lam peak cnt fail ran most ok0' tr0' D0' Lam' peak' cnt' fail' ran' /\
     rd_blocks_move B ly S ly' S' D0' tr0' (rest_atR tb text p) d /\
     PItems_posb.pi_posb S S' tr0' /\
     PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
       tr0' /\
     blocks_bytes S' <= blocks_bytes S + prh_held tr0' /\ length ok0' = PjGrammar.calls tr0' /\
     Ledger.lsum D0' = PjGrammar.held tr0' /\
     rd_room S' (snd (fst (pi_jrb f' (Nat.succ d) o n cap' (rev acc) (rest_atR tb text pc) []))) /\
     pi_grant ok0' tr0' /\ cap' = PresetReqAt.ncap (Nat.succ n) /\ pi_ncaps (rdW W' mem') kids' acc /\
     exists af', pi_forder (rdW W' mem') (prh_lin Lam') o kids' keys' n Di acc af' /\
       pi_fl_eqB d o (rest_atR tb text p) ok0' f' n cap' af' (rest_atR tb text pc))
  \/
  (getr regs' 10 = w64 (-1) /\ YAkMemnorm.memnorm segs mem' /\
   forall (regs'' : bvmap 5 word) (md'' : Model), getr regs'' 10 = w64 (-1) ->
     pi_post B ly S d o tb text len p q v Lam peak cnt fail ran most own kr ly' S' Hp' W' regs'' mem' md'').

(* the step's conclusion, as a name the arms below share (pil_grow_step_stmt's conclusion, verbatim) *)
Definition pil_step_out (ly : alayout) (Se : astate) (d : nat) (o : bool) (tb : list Z) (text len p q v e : Z)
  (regs0 : bvmap 5 word) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (kr : nat) (f n : nat)
  (acc : list (list Z * jv)) (Di : list (Z * Z)) (pc : Z) (ly' : alayout) (S' : astate) (Hp' : list Z)
  (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  (getr regs' 10 = w64 0 /\ YAkMemnorm.memnorm segs mem' /\
   exists (f' cap' : nat) kids' keys' ok0' tr0' D0' Lam' peak' cnt' fail' ran',
     f = Nat.succ f' /\
     pi_cur B regs0 e q v text len tb d ly' S' Hp' W' mem' pc Lam' peak' cnt' fail' ran' most own /\
     (n < cap')%nat /\
     pi_cont (rdW W' mem') (prh_lin Lam') o v kids' keys' n cap' acc Di /\
     Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) acc /\
     pj_apartR (pi_sblk o kids' keys' cap') v /\
     Permutation D0' (pi_sblk o kids' keys' cap' ++ Di) /\
     (2 * length (rest_atR tb text pc) + 1 <= f')%nat /\
     pi_run_eqB d o (rest_atR tb text p) ok0' tr0' f' n cap' (rev acc) (rest_atR tb text pc) /\
     pi_led Lam peak cnt fail ran most ok0' tr0' D0' Lam' peak' cnt' fail' ran' /\
     rd_blocks_move B ly Se ly' S' D0' tr0' (rest_atR tb text p) d /\
     PItems_posb.pi_posb Se S' tr0' /\
     PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf Se)) (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
       tr0' /\
     blocks_bytes S' <= blocks_bytes Se + prh_held tr0' /\ length ok0' = PjGrammar.calls tr0' /\
     Ledger.lsum D0' = PjGrammar.held tr0' /\
     rd_room S' (snd (fst (pi_jrb f' (Nat.succ d) o n cap' (rev acc) (rest_atR tb text pc) []))) /\
     pi_grant ok0' tr0' /\ cap' = PresetReqAt.ncap (Nat.succ n) /\ pi_ncaps (rdW W' mem') kids' acc /\
     exists af', pi_forder (rdW W' mem') (prh_lin Lam') o kids' keys' n Di acc af' /\
       pi_fl_eqB d o (rest_atR tb text p) ok0' f' n cap' af' (rest_atR tb text pc))
  \/
  (getr regs' 10 = w64 (-1) /\ YAkMemnorm.memnorm segs mem' /\
   forall (regs'' : bvmap 5 word) (md'' : Model), getr regs'' 10 = w64 (-1) ->
     pi_post B ly Se d o tb text len p q v Lam peak cnt fail ran most own kr ly' S' Hp' W' regs'' mem' md'').

(* ================================================================================================== *)
(* 4b. THE STEP's pure helpers. The only law used is AR_laws_x (live blocks are present, pairwise apart). The   *)
(* head length the instance's event lists use (prhPg_evs: cf_head) is the model's (rd_hevs: PresetReqAt.HEAD):  *)
(* PIL_HEAD (OWNER: the instance, reflexivity at CfParams_preset, 16 = 16), so prhPg_evs_model applies.         *)
(* ================================================================================================== *)
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Hypothesis PIL_HEAD : cf_head = PresetReqAt.HEAD.

Lemma pil_ty6 : forall o : bool, ((if o then 6 else 5) =? 6) = o.
Proof. intros o. destruct o; reflexivity. Qed.

(* tgrow_specX's event list on an arm is the model's: the heap events of grow's trace under the arm's outcomes *)
Lemma pil_evs_model : forall (o : bool) (n cap : nat) okA,
  prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap) okA =
  PresetReqAt.rd_hevs (snd (fst (PjGrammar.grow o n cap okA))).
Proof.
intros o n cap okA. rewrite pil_ty6, (prhPg_evs_model o (Z.of_nat n) (Z.of_nat cap) okA) by (first [lia | exact PIL_HEAD]).
rewrite !Nat2Z.id. reflexivity.
Qed.

Lemma pil_sblk_slots : forall (o : bool) kids keys cap, pi_sblk o kids keys cap = pis_slots o kids keys (Z.of_nat cap).
Proof. intros o kids keys cap. destruct o; reflexivity. Qed.

Lemma pil_apart_r : forall A Bl v, pj_apartR (A ++ Bl) v -> pj_apartR Bl v.
Proof. intros A Bl v H b x Hb. apply H. apply in_or_app. right. exact Hb. Qed.

Lemma pil_req_ge : forall k, 0 <= k -> k <= req_size k.
Proof. intros k Hk. unfold req_size. destruct (k =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia]. Qed.

Lemma pil_c2_gt : forall cap, (cap < pil_c2 cap)%nat.
Proof. intros cap. unfold pil_c2. destruct cap; cbn [Nat.eqb]; lia. Qed.

Lemma pil_gcap_lt : forall n cap, (n < cap)%nat -> pil_gcap n cap = cap.
Proof. intros n cap H. unfold pil_gcap. rewrite (proj2 (Nat.ltb_lt n cap) H). reflexivity. Qed.

Lemma pil_gcap_ge : forall n cap, (cap <= n)%nat -> pil_gcap n cap = pil_c2 cap.
Proof. intros n cap H. unfold pil_gcap. rewrite (proj2 (Nat.ltb_ge n cap) H). reflexivity. Qed.

Lemma pil_gtrace_lt : forall (o : bool) (n cap : nat), (n < cap)%nat ->
  PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap) = [].
Proof. intros o n cap H. unfold PRH_Charge.prhPg_gtrace. rewrite !Nat2Z.id, pil_grow_lt by exact H. reflexivity. Qed.

Lemma pil_gtrace_ge : forall (o : bool) (n cap : nat), (cap <= n)%nat ->
  PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap) =
  EGrow (56 * cap) (56 * pil_c2 cap) :: (if o then [EGrow (8 * cap) (8 * pil_c2 cap)] else []).
Proof. intros o n cap H. unfold PRH_Charge.prhPg_gtrace. rewrite !Nat2Z.id, pil_grow_ge by exact H. destruct o; reflexivity. Qed.

Lemma pil_open_of_cont : forall m lblk (o : bool) v kids keys (n cap : nat) acc Di,
  pi_cont m lblk o v kids keys n cap acc Di ->
  NoDup (pi_sblk o kids keys cap ++ Di) -> pj_apartR (pi_sblk o kids keys cap) v ->
  pis_open segs m lblk v o 0 kids keys (Z.of_nat cap) (Z.of_nat (length (map snd acc))) (map snd acc) (map fst acc) Di.
Proof.
intros m lblk o v kids keys n cap acc Di (Hh & Hn & Hle & H54 & Hsl & Hk0 & HND & HapD & Hit) HN Hap.
rewrite pil_sblk_slots in HN, Hap. rewrite length_map, <- Hn.
split; [exact HN|]. split; [apply pis_r_apart_app; [exact Hap | exact HapD]|].
split; [destruct o; exact Hh|].
split.
- unfold pj_slots_atR. split; [destruct o; unfold pis_oz; lia|]. split; [lia|].
  destruct Hsl as [(Hc0 & Hk & Hy) | (Hc & Hk & Hy)].
  + split; [intros _; split; [exact Hk | intros _; exact Hy] | intros Hc; lia].
  + split; [intros Hc0; lia|]. intros _. split; [exact Hk|]. intros H6. apply Hy.
    destruct o; [reflexivity | unfold pis_oz in H6; lia].
- split; [exact Hk0|]. unfold pis_items. destruct o.
  + split; [rewrite !length_map; reflexivity|]. rewrite pis_combine_map. exact Hit.
  + exact Hit.
Qed.

Lemma pil_cont_of_open : forall m lblk (o : bool) v kids keys (n cap : nat) acc Di,
  pis_open segs m lblk v o 0 kids keys (Z.of_nat cap) (Z.of_nat n) (map snd acc) (map fst acc) Di ->
  n = length acc -> (n <= cap)%nat -> Z.of_nat cap <= 2 ^ 54 ->
  pi_cont m lblk o v kids keys n cap acc Di.
Proof.
intros m lblk o v kids keys n cap acc Di (HN & Hap & Hh & Hsl & Hk0 & Hit) Hn Hle H54.
split; [destruct o; exact Hh|]. split; [exact Hn|]. split; [exact Hle|]. split; [exact H54|].
destruct Hsl as (_ & _ & Hc0 & Hcp).
split.
{ destruct (Nat.eq_dec cap 0) as [E|E].
  - left. subst cap. destruct (Hc0 eq_refl) as [Hk Hy]. split; [reflexivity|]. split; [exact Hk|].
    destruct o; [apply Hy; reflexivity | apply Hk0; reflexivity].
  - right. destruct (Hcp ltac:(lia)) as [Hk Hy]. split; [lia|]. split; [exact Hk|].
    intros ->. apply Hy. reflexivity. }
split; [exact Hk0|]. split; [exact (pis_nodup_r _ _ _ HN)|]. split; [exact (pil_apart_r _ _ _ Hap)|].
unfold pis_items in Hit. destruct o.
- destruct Hit as [_ Hit]. rewrite pis_combine_map in Hit. exact Hit.
- exact Hit.
Qed.

Lemma pil_garr8_moved : forall m m' a a' (l : list Z), garr8 segs m a l -> garr8 segs m' a' l ->
  pis_moved segs m m' a a' (Z.of_nat (length l)).
Proof.
intros m m' a a' l H H' i Hi.
assert (Hj : (Z.to_nat i < length l)%nat) by lia.
destruct (H (Z.to_nat i) Hj) as [Hv _]. destruct (H' (Z.to_nat i) Hj) as [Hv' _].
pose proof (Hv 0%nat ltac:(lia)) as E. pose proof (Hv' 0%nat ltac:(lia)) as E'.
replace (a + Z.of_nat (Z.to_nat i) + Z.of_nat 0) with (a + i) in E by lia.
replace (a' + Z.of_nat (Z.to_nat i) + Z.of_nat 0) with (a' + i) in E' by lia.
rewrite E, E'. reflexivity.
Qed.

Lemma pil_blk_wr : forall ly S Hp W mem md b k x, ARx ly S Hp W mem md -> In (b, k) (ablocks B ly S) ->
  b <= x < b + req_size k -> writable_at segs (rdW W mem) x.
Proof.
intros ly S Hp W mem md b k x HA Hin Hx.
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md b k HA Hin) as (_ & _ & _ & _ & Hpr & _).
apply apresent_writable. exact (proj1 (Hpr x Hx)).
Qed.

Lemma pil_lam_hb : forall ly S Hp W mem Lam peak cnt fail ran most own a k,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B ly S) /\ a mod 16 = 0.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin.
pose proof HL as HF. apply prh_ledger_blocks in HF.
rewrite Forall_forall in HF. destruct (HF (a, k) Hin) as (Hk & Hb & _ & Hm & _). cbn [fst snd] in *.
split; [exact Hk|]. split; [exact Hb | exact Hm].
Qed.

Lemma pil_lam_wr : forall ly S Hp W mem md Lam peak cnt fail ran most own a k x,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  a <= x < a + k -> writable_at segs (rdW W mem) x.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k x HA HL Hin Hx.
destruct (pil_lam_hb ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin) as (Hk & Hb & _).
pose proof (@cf_head_nonneg cp) as Hh. assert (Hr : k + cf_head <= req_size (k + cf_head)) by (apply pil_req_ge; lia).
apply (pil_blk_wr ly S Hp W mem md (a - cf_head) (k + cf_head) x HA Hb). lia.
Qed.

Lemma pil_lam_bound : forall ly S Hp W mem md Lam peak cnt fail ran most own a k,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= k /\ 4096 <= a - cf_head /\ a + k <= YM05.alloc_ceiling /\ a mod 16 = 0.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k HA HL Hin.
destruct (pil_lam_hb ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin) as (Hk & Hb & Hm).
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HA Hb) as (_ & H4 & Hc & _).
pose proof (@cf_head_nonneg cp) as Hh. assert (Hr : k + cf_head <= req_size (k + cf_head)) by (apply pil_req_ge; lia).
split; [exact Hk|]. split; [exact H4|]. split; [lia | exact Hm].
Qed.

Lemma pil_keep_same : forall (Wc W' : world segs) memc mem' FPL a k x,
  (forall lo hi y, In (lo, hi) FPL -> lo <= y < hi -> aview segs (w_H W') mem' y = aview segs (w_H Wc) memc y) ->
  In (a - cf_head, a - cf_head + req_size (k + cf_head)) FPL -> 0 <= k -> a <= x < a + k ->
  writable_at segs (rdW W' mem') x -> pis_same segs (rdW Wc memc) (rdW W' mem') x.
Proof.
intros Wc0 W1 m0 m1 FPL a k x Hkeep Hin Hk Hx Hw. pose proof (@cf_head_nonneg cp) as Hh.
assert (Hr : k + cf_head <= req_size (k + cf_head)) by (apply pil_req_ge; lia).
split; [apply mbyte_of_aview; apply (Hkeep _ _ x Hin); lia | intros _; exact Hw].
Qed.

Lemma pil_fp_kids : forall kids keys capZ ty, capZ <> 0 ->
  In (kids - cf_head, kids - cf_head + req_size (56 * capZ + cf_head))
    (ablocks_fp (prhReader_ab (kids_blkR kids capZ ++ keys_blkR ty keys capZ))).
Proof.
intros kids keys capZ ty H. unfold kids_blkR. rewrite (proj2 (Z.eqb_neq capZ 0) H).
unfold ablocks_fp, prhReader_ab. cbn [map app fst snd]. left. reflexivity.
Qed.

Lemma pil_fp_keys : forall kids keys capZ, capZ <> 0 ->
  In (keys - cf_head, keys - cf_head + req_size (8 * capZ + cf_head))
    (ablocks_fp (prhReader_ab (kids_blkR kids capZ ++ keys_blkR 6 keys capZ))).
Proof.
intros kids keys capZ H. unfold kids_blkR, keys_blkR. rewrite (proj2 (Z.eqb_neq capZ 0) H).
unfold ablocks_fp, prhReader_ab. cbn [map app fst snd orb negb Z.eqb]. right. left. reflexivity.
Qed.

Lemma pil_pw_perm : forall {X} (R : X -> X -> Prop), (forall x y, R x y -> R y x) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros X R Hs l l' HP. induction HP as [| x l l' HP IH | x y l | l l' l'' H1 IH1 H2 IH2]; intros H.
- exact H.
- destruct H as [Hf Hp]. split; [|exact (IH Hp)].
  rewrite Forall_forall in *. intros z Hz. apply Hf. exact (Permutation_in _ (Permutation_sym HP) Hz).
- destruct H as [Hy [Hx Hp]]. apply Forall_cons_iff in Hy as [Hyx Hyl].
  split; [constructor; [apply Hs; exact Hyx | exact Hx]|]. split; [exact Hyl | exact Hp].
- exact (IH2 (IH1 H)).
Qed.

Lemma pil_blk_new_apart : forall ly S Hp W mem md x l, ARx ly S Hp W mem md ->
  Permutation (ablocks B ly S) (x :: l) -> forall y, In y l ->
  zdisjoint (fst x, req_size (snd x)) (fst y, req_size (snd y)).
Proof.
intros ly S Hp W mem md x l HA HP y Hy.
assert (Hin : In x (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
destruct x as [p0 n0].
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md p0 n0 HA Hin) as (_ & _ & _ & _ & _ & Hpw).
assert (Hpw' : pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) ((p0, n0) :: l))).
{ refine (pil_pw_perm zdisjoint _ (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) _
    (Permutation_map _ HP) Hpw).
  intros a b Hab. unfold zdisjoint in *. lia. }
cbn [map pairwise] in Hpw'. destruct Hpw' as [Hf _]. rewrite Forall_forall in Hf.
apply Hf. apply (in_map (fun b => (fst b, req_size (snd b))) l y Hy).
Qed.

Lemma pil_blk_new_fresh : forall ly S Hp W mem md x l, ARx ly S Hp W mem md ->
  Permutation (ablocks B ly S) (x :: l) -> 0 < req_size (snd x) -> ~ In x l.
Proof.
intros ly S Hp W mem md x l HA HP Hr Hin.
pose proof (pil_blk_new_apart ly S Hp W mem md x l HA HP x Hin) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma pil_held_hpeak : forall t, PjGrammar.held t <= hpeakR t.
Proof. induction t as [|e r IH]; cbn [PjGrammar.held hpeakR]; lia. Qed.

Lemma pil_lsum_perm : forall l l', Permutation l l' -> Ledger.lsum l = Ledger.lsum l'.
Proof. intros l l' H. rewrite !pvm_lsum_map. apply pvm_zsum_perm. apply Permutation_map. exact H. Qed.

Lemma pil_perm_rm1n : forall a s, In a s -> Permutation s (a :: rm1nR a s).
Proof.
intros a s. induction s as [|x r IH]; intros Hin; [destruct Hin|].
cbn [rm1nR]. destruct (Nat.eqb x a) eqn:E.
- apply Nat.eqb_eq in E. subst. reflexivity.
- destruct Hin as [-> | Hin]; [rewrite Nat.eqb_refl in E; discriminate|].
  eapply perm_trans; [apply perm_skip; exact (IH Hin) | apply perm_swap].
Qed.

Lemma pil_lsz_app : forall t g, lszR (t ++ g) = fold_left lsz_evR g (lszR t).
Proof. intros t g. unfold lszR. rewrite fold_left_app. reflexivity. Qed.

(* ---- THE BATCH KIT'S LEDGER MOVE (lib/A/PRH_FnParse.v rd_ledger_move: prh_oks keyed on each call's request against g_most,
   the refusal peak over the call's ALL-GRANTED trace) ---- *)
Lemma pil_rep_app : forall k j, repeat true k ++ repeat true j = repeat true (k + j).
Proof. intros k j. symmetry. apply repeat_app. Qed.

(* a GRANTED move (every call granted, none of them the chosen failure): g_ran_out kept, refusal peak 0, at any
   granted trace gt *)
Lemma pil_move_granted : forall Lam peak cnt fail ran most k gt tr D Lam' peak' cnt' fail',
  PjGrammar.calls tr = k ->
  (forall i, (i < k)%nat -> cnt + Z.of_nat i <> fail) ->
  cnt' = (cnt + Z.of_nat k) mod 2 ^ 64 ->
  fail_afterR cnt fail k fail' ->
  Permutation Lam' (D ++ Lam) ->
  Permutation (map snd D) (map Z.of_nat (lszR tr)) ->
  Z.of_nat (length D) = nliveR tr ->
  peak' = Z.max (Z.max peak (Ledger.lsum Lam + hpeakR tr)) 0 ->
  rd_ledger_move Lam peak cnt fail ran most (repeat true k) gt tr D Lam' peak' cnt' fail' ran.
Proof.
intros Lam peak cnt fail ran most k gt tr D Lam' peak' cnt' fail' Hk Hf Hc Hfa HP HS HN HK. subst k.
unfold rd_ledger_move.
split; [|split; [exact Hc|split; [exact Hfa|split; [exact HP|split; [exact HS|split; [exact HN|]]]]]].
- split; [|split].
  + intros i Hi E. exfalso. exact (Hf i Hi E).
  + left. reflexivity.
  + intros i Hi Hr _. exfalso. unfold prh_refused in Hr.
    rewrite (PItems_ledk1.pik1_ok_upto_repeat _ (S i) i ltac:(lia)) in Hr. cbn in Hr. discriminate Hr.
- rewrite (prh_refused_peak_granted _ _ _ _ _ (PItems_ledk1.pik1_grant_granted _ _ _ _)). exact HK.
Qed.

(* ONE refused or chosen-failed allocator call [EFail k] after the granted trace's EGrow a b (grow's kids realloc, or
   an object's keys realloc after a granted kids realloc): its own move, from its arm's ledger *)
Lemma pil_mv_fail1 : forall Lam1 peak1 cnt1 fail1 ran1 most (a b k : nat) peak2 cnt2 fail2 ran2,
  0 <= Ledger.lsum Lam1 <= peak1 -> 0 <= cnt1 -> cnt1 + 1 < 2 ^ 64 ->
  ((cnt1 = fail1 /\ peak2 = peak1 /\ cnt2 = cnt1 + 1 /\ fail2 = SIZE_MAXZ /\ ran2 = ran1) \/
   (cnt1 <> fail1 /\ peak2 = Z.max peak1 (Z.min SIZE_MAXZ (Ledger.lsum Lam1 + (Z.of_nat b - Z.of_nat a))) /\
    cnt2 = (cnt1 + 1) mod 2 ^ 64 /\ fail2 = fail1 /\ ran2 = (if Z.of_nat k <=? most then 1 else ran1))) ->
  forall r, rd_ledger_move Lam1 peak1 cnt1 fail1 ran1 most [false] (EGrow a b :: r) [EFail k] [] Lam1
    peak2 cnt2 fail2 ran2.
Proof.
intros Lam1 peak1 cnt1 fail1 ran1 most a b k peak2 cnt2 fail2 ran2 HL Hc0 Hcb Hcase r.
assert (ER : prh_ev_reqs [EFail k] = [Z.of_nat k]) by reflexivity.
assert (ERf : forall c, prh_refused [false] c fail1 0 = negb (c =? fail1)).
{ intros c. unfold prh_refused. cbn [nth negb andb]. rewrite Z.add_0_r. reflexivity. }
unfold rd_ledger_move. cbn [PjGrammar.calls PjGrammar.is_call]. rewrite ER.
split; [|split; [|split; [|split; [|split; [|split]]]]].
- split; [|split].
  + intros i Hi _. destruct i; [reflexivity | lia].
  + destruct Hcase as [(E & -> & -> & -> & ->) | (E & -> & -> & -> & ->)]; [left; reflexivity|].
    destruct (Z.leb_spec (Z.of_nat k) most) as [Hm|Hm]; [|left; reflexivity].
    right. split; [reflexivity|]. exists 0%nat. split; [lia|]. rewrite ERf.
    split; [rewrite (proj2 (Z.eqb_neq _ _) E); reflexivity | exact Hm].
  + intros i Hi Hr Hm. destruct i; [|lia]. rewrite ERf in Hr. cbn [nth] in Hm.
    destruct Hcase as [(E & _) | (E & _ & _ & _ & ->)].
    * rewrite (proj2 (Z.eqb_eq _ _) E) in Hr. discriminate Hr.
    * rewrite (proj2 (Z.leb_le _ _) Hm). reflexivity.
- destruct Hcase as [(E & _ & -> & _) | (E & _ & -> & _)]; [rewrite Z.mod_small by lia|]; reflexivity.
- unfold fail_afterR. destruct Hcase as [(E & _ & _ & -> & _) | (E & _ & _ & -> & _)];
    split; intros H; first [reflexivity | lia].
- apply Permutation_refl.
- replace (lszR [PjGrammar.EFail k]) with (@nil nat) by reflexivity. apply Permutation_refl.
- reflexivity.
- replace (hpeakR [PjGrammar.EFail k]) with 0 by reflexivity.
  unfold prh_refused_peak. cbn [List.seq map fold_right prh_ev_helds PjGrammar.is_call app nth PjGrammar.held_ev].
  rewrite ERf.
  destruct Hcase as [(E & -> & _) | (E & -> & _)].
  + rewrite (proj2 (Z.eqb_eq _ _) E). cbn [negb]. lia.
  + rewrite (proj2 (Z.eqb_neq _ _) E). cbn [negb]. unfold SIZE_MAXZ in *. lia.
Qed.

(* the model's free list after a GRANTED grow: jfl one member deep is pi_jfb at grow's new cap (pi_jfl_unfold) *)
Lemma pil_flB : forall d (o : bool) x0 ok0 f' n cap af y okg g cap',
  pi_fl_eq d o x0 ok0 (S f') n cap af y ->
  (forall ok1, PjGrammar.grow o n cap (okg ++ ok1) = (Some cap', g, ok1)) ->
  pi_fl_eqB d o x0 (ok0 ++ okg) f' n cap' af y.
Proof.
intros d o x0 ok0 f' n cap af y okg g cap' HF HG ok1.
rewrite <- app_assoc, (HF (okg ++ ok1)), pi_jfl_unfold, (HG ok1). reflexivity.
Qed.

(* ... and after a REFUSED grow: the completed slots' list, then the arrays as the refused grow left them *)
Lemma pil_fl_refused : forall d (o : bool) x0 ok0 f' n cap af y okr tg,
  pi_fl_eq d o x0 ok0 (S f') n cap af y -> PjGrammar.grow o n cap okr = (None, tg, []) ->
  prhPi_frees d o x0 (ok0 ++ okr) = af ++ PresetReqAt.gheld o cap tg.
Proof. intros d o x0 ok0 f' n cap af y okr tg HF HG. rewrite (HF okr), pi_jfl_unfold, HG. reflexivity. Qed.

Lemma pil_cnt_mod : forall cnt k j cntc, cntc = (cnt + Z.of_nat k) mod 2 ^ 64 ->
  0 <= cnt -> cnt + Z.of_nat (k + j) < 2 ^ 64 -> cntc + Z.of_nat j = (cnt + Z.of_nat (k + j)) mod 2 ^ 64.
Proof.
intros cnt k j cntc -> H0 H1. rewrite Nat2Z.inj_add in *.
rewrite (Z.mod_small (cnt + Z.of_nat k)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma pil_fa_none : forall cnt fail k j failc, fail_afterR cnt fail k failc ->
  ~ (cnt + Z.of_nat k <= fail < cnt + Z.of_nat (k + j)) -> fail_afterR cnt fail (k + j) failc.
Proof.
intros cnt fail k j failc (F1 & F2) Hn. split.
- intros H. apply F1. lia.
- intros H. apply F2. lia.
Qed.

Lemma pil_fa_hit : forall cnt fail k j failc, fail_afterR cnt fail k failc ->
  cnt + Z.of_nat k <= fail < cnt + Z.of_nat (k + j) -> fail_afterR cnt fail (k + j) SIZE_MAXZ.
Proof. intros cnt fail k j failc _ H. split; [intros _; reflexivity | intros H'; exfalso; lia]. Qed.

(* which call of the ones after the prefix is the chosen failure: with no wrap of g_count, grow's view (cntc + j =
   failc) and the entry's (fail = cnt + k + j) agree *)
Lemma pil_fail_at : forall cnt fail k cntc failc j, fail_afterR cnt fail k failc -> cntc = cnt + Z.of_nat k ->
  0 <= j -> cntc + j < SIZE_MAXZ -> (cntc + j = failc <-> fail = cnt + Z.of_nat k + j).
Proof.
intros cnt fail k cntc failc j (F1 & F2) Hc Hj Hs.
destruct (Z_lt_le_dec fail cnt) as [Hl|Hl]; [|destruct (Z_lt_le_dec fail (cnt + Z.of_nat k)) as [Hu|Hu]].
- rewrite (F2 ltac:(lia)). split; intros; lia.
- rewrite (F1 ltac:(lia)). split; intros; lia.
- rewrite (F2 ltac:(lia)). split; intros; lia.
Qed.

(* the prefix and grow's granted calls fit the entry's text (PjGrammar.G7_4_items on the granted run) *)
Lemma pil_calls_bound : forall d (o : bool) x0 ok0 tr0 f' n cap acc y,
  x0 <> [] -> pi_run_eq d o x0 ok0 tr0 (Nat.succ f') n cap acc y ->
  (PjGrammar.calls tr0 + PjGrammar.calls (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap)) <= 2 * length x0)%nat.
Proof.
intros d o x0 ok0 tr0 f' n cap acc y Hne HR. destruct x0 as [|b y0]; [exfalso; apply Hne; reflexivity|].
destruct (jrl prh_jr_strtod (Nat.succ f') (Nat.succ d) o n cap (rev acc) y []) as [[r t] ok2] eqn:Ej.
pose proof (HR [] r t ok2 Ej) as HI.
pose proof (PjGrammar.G7_4_items prh_jr_strtod d o b y0 (ok0 ++ [])) as HB. rewrite HI in HB. cbn [fst snd] in HB.
pose proof (pil_gt_split f' (Nat.succ d) o n cap (rev acc) y) as HS. rewrite Ej in HS. cbn [fst snd] in HS.
rewrite HS, !calls_app in HB. lia.
Qed.

Lemma pil_req_pos : forall k, 0 < k -> 0 < req_size k.
Proof. intros k Hk. unfold req_size. destruct (k =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia]. Qed.

Lemma pil_sblk_false : forall kids keys cap, pi_sblk false kids keys cap = kids_blkR kids (Z.of_nat cap).
Proof.
intros kids keys cap. unfold pi_sblk, keys_blkR. replace (negb (5 =? 6)) with true by reflexivity.
rewrite orb_true_r. apply app_nil_r.
Qed.

Lemma pil_sblk_true : forall kids keys cap,
  pi_sblk true kids keys cap = kids_blkR kids (Z.of_nat cap) ++ keys_blkR 6 keys (Z.of_nat cap).
Proof. reflexivity. Qed.

Lemma pil_kblk : forall kids (cap : nat),
  kids_blkR kids (Z.of_nat cap) = if Nat.eqb cap 0 then [] else [(kids, 56 * Z.of_nat cap)].
Proof. intros kids cap. unfold kids_blkR. destruct cap; reflexivity. Qed.

Lemma pil_yblk : forall keys (cap : nat),
  keys_blkR 6 keys (Z.of_nat cap) = if Nat.eqb cap 0 then [] else [(keys, 8 * Z.of_nat cap)].
Proof. intros keys cap. unfold keys_blkR. destruct cap; reflexivity. Qed.

(* the live sizes after one EGrow: the old block's size leaves (when it is a block), the new one's comes *)
Lemma pil_kcase : forall kids (cap : nat),
  ((56 * cap)%nat = 0%nat /\ kids_blkR kids (Z.of_nat cap) = []) \/
  ((0 < 56 * cap)%nat /\ map snd (kids_blkR kids (Z.of_nat cap)) = [Z.of_nat (56 * cap)]).
Proof.
intros kids cap. rewrite pil_kblk. destruct cap as [|c]; [left; split; reflexivity|].
right. split; [lia|]. cbn [Nat.eqb map snd]. f_equal. lia.
Qed.

Lemma pil_ycase : forall keys (cap : nat),
  ((8 * cap)%nat = 0%nat /\ keys_blkR 6 keys (Z.of_nat cap) = []) \/
  ((0 < 8 * cap)%nat /\ map snd (keys_blkR 6 keys (Z.of_nat cap)) = [Z.of_nat (8 * cap)]).
Proof.
intros keys cap. rewrite pil_yblk. destruct cap as [|c]; [left; split; reflexivity|].
right. split; [lia|]. cbn [Nat.eqb map snd]. f_equal. lia.
Qed.

Lemma pil_lsz_grow : forall s (Dx Di : list (Z * Z)) (a b : nat),
  Permutation (map snd (Dx ++ Di)) (map Z.of_nat s) ->
  ((a = 0%nat /\ Dx = []) \/ ((0 < a)%nat /\ map snd Dx = [Z.of_nat a])) ->
  Permutation (Z.of_nat b :: map snd Di) (map Z.of_nat (lsz_evR s (EGrow a b))).
Proof.
intros s Dx Di a b HP [(-> & ->) | (Ha & Hx)].
- cbn [lsz_evR app map]. apply perm_skip. exact HP.
- destruct a as [|a']; [lia|]. cbn [lsz_evR map]. apply perm_skip.
  rewrite map_app, Hx in HP. cbn [app] in HP.
  assert (Hin : In (S a') s).
  { assert (H1 : In (Z.of_nat (S a')) (map Z.of_nat s)) by (apply (Permutation_in _ HP); left; reflexivity).
    apply in_map_iff in H1 as (x & Hx1 & Hx2). apply Nat2Z.inj in Hx1. subst x. exact Hx2. }
  pose proof (Permutation_map Z.of_nat (pil_perm_rm1n _ _ Hin)) as HQ. cbn [map] in HQ.
  eapply Permutation_cons_inv. exact (Permutation_trans HP HQ).
Qed.

(* ---- the kit's CAP across grow's MOVED arms (no shared lemma moves a node: PvB_Frees.pvf_ncap_frame and PItems_value_model.v's
   pvm_ncaps_items / _mems keep the address): a member's node copied to a new slot (its 56 header bytes moved, its
   blocks D kept) keeps its capacity words, its children by pvf_ncap_frame; then the members of pi_cont, slot by slot ---- *)
Lemma pil_ncap_mv : forall t (H : word -> bool) mem m' lblk p p' D,
  pj_nodeR segs (mrestrict H mem) lblk p t D ->
  pj_agreeR segs (mrestrict H mem) m' (fun x => exists b, In b D /\ pj_holdsR b x) ->
  pis_moved segs (mrestrict H mem) m' p p' 56 ->
  pj_ncapR segs (mrestrict H mem) p t -> pj_ncapR segs m' p' t.
Proof.
intros t H mem m' lblk p p' D HN HM Hmv HC.
assert (HU : forall o0 w, 0 <= o0 -> o0 + 8 <= 56 -> rd_u64 segs (mrestrict H mem) (p + o0) w ->
  rd_u64 segs m' (p' + o0) w).
{ intros o0 w H0 H1 Hw. apply (pis_u64_mv segs _ _ (p + o0) (p' + o0) w Hw). intros i Hi.
  replace (p' + o0 + i) with (p' + (o0 + i)) by lia. replace (p + o0 + i) with (p + (o0 + i)) by lia.
  apply Hmv. lia. }
destruct t as [| | | txt bits | s | items | members]; cbn [pj_ncapR] in HC |- *; try exact I.
- cbn [pj_nodeR] in HN. destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & Hb).
  destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  destruct HC as (H48 & kids' & H24 & Hk).
  pose proof Hh as (_ & _ & _ & _ & Hkids & _).
  assert (Ekk : kids' = kids) by exact (PvB_Frees.pvf_u64_det segs H mem (p + 24) kids' kids H24 Hkids). subst kids'.
  split; [exact (HU 48 _ ltac:(lia) ltac:(lia) H48)|].
  exists kids. split; [exact (HU 24 _ ltac:(lia) ltac:(lia) H24)|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  apply (PvB_Frees.pvf_kids_items (pj_nodeR segs (mrestrict H mem) lblk) (pj_ncapR segs (mrestrict H mem)) _ items kids
    Di Hi Hk).
  intros i u D1 Hil Hinc HP HQ.
  pose proof (pj_nth_lenR items i u Hil) as Hlt.
  assert (Hp : 0 < cap) by lia.
  assert (Hin : In (kids, 56 * cap) D).
  { subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  apply (PvB_Frees.pvf_ncap_frame segs u H mem m' lblk _ D1 HP); [|exact HQ].
  intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
  + exists (kids, 56 * cap). split; [exact Hin | unfold pj_holdsR; cbn [fst snd]; lia].
  + exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
- cbn [pj_nodeR] in HN. destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & Hb).
  destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  destruct HC as (H48 & kids' & H24 & Hk).
  pose proof Hh as (_ & _ & _ & _ & Hkids & _).
  assert (Ekk : kids' = kids) by exact (PvB_Frees.pvf_u64_det segs H mem (p + 24) kids' kids H24 Hkids). subst kids'.
  split; [exact (HU 48 _ ltac:(lia) ltac:(lia) H48)|].
  exists kids. split; [exact (HU 24 _ ltac:(lia) ltac:(lia) H24)|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  apply (PvB_Frees.pvf_kids_mems segs (mrestrict H mem) lblk (pj_nodeR segs (mrestrict H mem) lblk)
    (pj_ncapR segs (mrestrict H mem)) _ members kids keys Di Hi Hk).
  intros i nm u D1 Hil Hinc HP HQ.
  pose proof (pj_nth_lenR members i (nm, u) Hil) as Hlt.
  assert (Hp : 0 < cap) by lia.
  assert (Hin : In (kids, 56 * cap) D).
  { subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  apply (PvB_Frees.pvf_ncap_frame segs u H mem m' lblk _ D1 HP); [|exact HQ].
  intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
  + exists (kids, 56 * cap). split; [exact Hin | unfold pj_holdsR; cbn [fst snd]; lia].
  + exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
Qed.

Lemma pil_ncaps_mv_items : forall (H : word -> bool) mem m' lblk (accs : list (list Z * jv)) a a' Di,
  pj_itemsR (pj_nodeR segs (mrestrict H mem) lblk) a (map snd accs) Di ->
  pi_ncaps (mrestrict H mem) a accs ->
  pj_agreeR segs (mrestrict H mem) m' (fun x => exists b, In b Di /\ pj_holdsR b x) ->
  pis_moved segs (mrestrict H mem) m' a a' (56 * Z.of_nat (length accs)) ->
  pi_ncaps m' a' accs.
Proof.
intros H mem m' lblk accs. unfold pi_ncaps.
induction accs as [|[nm u] r IH]; intros a a' Di HI HK HA Hmv; cbn [map pj_itemsR pj_kidsR] in HI, HK |- *;
  [exact I|].
destruct HI as (D1 & D2 & -> & H1 & H2). destruct HK as (K1 & K2). cbn [snd] in K1 |- *. split.
- apply (pil_ncap_mv u H mem m' lblk a a' D1 H1); [| |exact K1].
  + apply (PRH_PjOrder.pf_agree_mono segs _ _ _ _ HA). intros x (b & Hb & Hx).
    exists b. split; [apply in_or_app; left; exact Hb | exact Hx].
  + intros i Hi. apply Hmv. cbn [length]. lia.
- apply (IH (a + 56) (a' + 56) D2 H2 K2).
  + apply (PRH_PjOrder.pf_agree_mono segs _ _ _ _ HA). intros x (b & Hb & Hx).
    exists b. split; [apply in_or_app; right; exact Hb | exact Hx].
  + intros i Hi. replace (a' + 56 + i) with (a' + (56 + i)) by lia. replace (a + 56 + i) with (a + (56 + i)) by lia.
    apply Hmv. cbn [length] in Hi |- *. lia.
Qed.

Lemma pil_ncaps_mv_mems : forall (H : word -> bool) mem m' lblk (accs : list (list Z * jv)) a ka a' Di,
  pj_memsR segs (mrestrict H mem) lblk (pj_nodeR segs (mrestrict H mem) lblk) a ka accs Di ->
  pi_ncaps (mrestrict H mem) a accs ->
  pj_agreeR segs (mrestrict H mem) m' (fun x => exists b, In b Di /\ pj_holdsR b x) ->
  pis_moved segs (mrestrict H mem) m' a a' (56 * Z.of_nat (length accs)) ->
  pi_ncaps m' a' accs.
Proof.
intros H mem m' lblk accs. unfold pi_ncaps.
induction accs as [|[nm u] r IH]; intros a ka a' Di HI HK HA Hmv; cbn [pj_memsR pj_kidsR] in HI, HK |- *; [exact I|].
destruct HI as (x0 & k0 & D1 & D2 & -> & _ & _ & H1 & H2). destruct HK as (K1 & K2). cbn [snd] in K1 |- *. split.
- apply (pil_ncap_mv u H mem m' lblk a a' D1 H1); [| |exact K1].
  + apply (PRH_PjOrder.pf_agree_mono segs _ _ _ _ HA). intros x (b & Hb & Hx).
    exists b. split; [right; apply in_or_app; left; exact Hb | exact Hx].
  + intros i Hi. apply Hmv. cbn [length]. lia.
- apply (IH (a + 56) (ka + 8) (a' + 56) D2 H2 K2).
  + apply (PRH_PjOrder.pf_agree_mono segs _ _ _ _ HA). intros x (b & Hb & Hx).
    exists b. split; [right; apply in_or_app; right; exact Hb | exact Hx].
  + intros i Hi. replace (a' + 56 + i) with (a' + (56 + i)) by lia. replace (a + 56 + i) with (a + (56 + i)) by lia.
    apply Hmv. cbn [length] in Hi |- *. lia.
Qed.

(* the members' capacities of pi_cont, its slot array copied from kids to kids' and its members' blocks Di kept *)
Lemma pil_ncaps_mv : forall (H : word -> bool) mem m' lblk (o : bool) v kids keys (n cap : nat) acc Di kids',
  pi_cont (mrestrict H mem) lblk o v kids keys n cap acc Di ->
  pi_ncaps (mrestrict H mem) kids acc ->
  (forall x, (exists b, In b Di /\ pj_holdsR b x) -> pis_same segs (mrestrict H mem) m' x) ->
  pis_moved segs (mrestrict H mem) m' kids kids' (56 * Z.of_nat n) ->
  pi_ncaps m' kids' acc.
Proof.
intros H mem m' lblk o v kids keys n cap acc Di kids' HC HK HD Hmv.
pose proof HC as (_ & En & _ & _ & _ & _ & _ & _ & Hi).
assert (HA : pj_agreeR segs (mrestrict H mem) m' (fun x => exists b, In b Di /\ pj_holdsR b x)) by exact HD.
rewrite En in Hmv.
destruct o; [exact (pil_ncaps_mv_mems H mem m' lblk acc kids keys kids' Di Hi HK HA Hmv)
           | exact (pil_ncaps_mv_items H mem m' lblk acc kids kids' Di Hi HK HA Hmv)].
Qed.

(* ================================================================================================== *)
(* 4c. THE STEP, arm by arm: the step's premises are this section's hypotheses.                        *)
(* ================================================================================================== *)
Section step.
Variables (ly : alayout) (Se : astate) (d : nat) (o : bool) (tb : list Z) (text len p q v e : Z)
  (regs0 : bvmap 5 word) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (kr : nat)
  (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world segs) (memc : word -> option byte) (f n cap : nat)
  (acc : list (list Z * jv)) (kids keys : Z) (Di : list (Z * Z)) (pc : Z) (ok0 : list bool) (tr0 : list ev)
  (D0 Lamc : list (Z * Z)) (peakc cntc failc ranc : Z) (af : list Z) (kb yb : list Z) (ly' : alayout) (S' : astate)
  (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model).
Hypothesis HMN : YAkMemnorm.memnorm segs memc.
Hypothesis HCUR : pi_cur B regs0 e q v text len tb d lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc most own.
Hypothesis HCNT : cntc + 2 * Z.of_nat (length (rest_atR tb text pc)) + 4 < 2 ^ 64 - 1.
Hypothesis HCONT : pi_cont (rdW Wc memc) (prh_lin Lamc) o v kids keys n cap acc Di.
Hypothesis HDEP : Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) acc.
Hypothesis HAP : pj_apartR (pi_sblk o kids keys cap) v.
Hypothesis HPERM : Permutation D0 (pi_sblk o kids keys cap ++ Di).
Hypothesis HFUEL : (2 * length (rest_atR tb text pc) + 2 <= f)%nat.
Hypothesis HRUN : pi_run_eq d o (rest_atR tb text p) ok0 tr0 f n cap acc (rest_atR tb text pc).
Hypothesis HX0 : rest_atR tb text p <> [].
Hypothesis HCNT0 : 0 <= cnt < 2 ^ 64 /\ cnt + 2 * Z.of_nat (length (rest_atR tb text p)) + 2 < 2 ^ 64 - 1.
Hypothesis HLED : pi_led Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc.
Hypothesis HBLK : rd_blocks_move B ly Se lyc Sc D0 tr0 (rest_atR tb text p) d.
(* the prefix's two travelling facts at the call state (form (b)): the position relation and the live requests *)
Hypothesis HPOSB : PItems_posb.pi_posb Se Sc tr0.
Hypothesis HLIVE : PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf Se))
  (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0.
Hypothesis HBB : blocks_bytes Sc <= blocks_bytes Se + prh_held tr0.
Hypothesis HOK : length ok0 = PjGrammar.calls tr0.
Hypothesis HLS : Ledger.lsum D0 = PjGrammar.held tr0.
Hypothesis HROOM : rd_room Sc (snd (fst (jrl prh_jr_strtod f (Nat.succ d) o n cap (rev acc) (rest_atR tb text pc) []))).
(* The batch kit's loop invariants at the call state (pi_loop_pre's tail) *)
Hypothesis HGRANT : pi_grant ok0 tr0.
Hypothesis HCAPN : cap = PresetReqAt.ncap n.
Hypothesis HNCAPS : pi_ncaps (rdW Wc memc) kids acc.
Hypothesis HFO : pi_forder (rdW Wc memc) (prh_lin Lamc) o kids keys n Di acc af.
Hypothesis HFL : pi_fl_eq d o (rest_atR tb text p) ok0 f n cap af (rest_atR tb text pc).
Hypothesis HBYT : n = cap -> bytes_at Wc memc kids kb /\ Z.of_nat (length kb) = 56 * Z.of_nat cap /\
  (o = true -> bytes_at Wc memc keys yb /\ Z.of_nat (length yb) = 8 * Z.of_nat cap).
Hypothesis HKDI : forall x, (exists b, In b Di /\ pj_holdsR b x) ->
  mbyte segs (rdW W' mem') x = mbyte segs (rdW Wc memc) x /\
  (writable_at segs (rdW Wc memc) x -> writable_at segs (rdW W' mem') x).
Hypothesis HAR : ARx ly' S' Hp' W' mem' md'.
Hypothesis HNEWV : forall b m x, In (b, m) (ablocks B ly' S') -> ~ In (b, m) (ablocks B lyc Sc) -> b <= x < b + m ->
  ~ (v <= x < v + 56).
Hypothesis HKCUR : forall Lam2 peak2 cnt2 fail2 ran2, prh_ledger B ly' S' Hp' W' mem' Lam2 peak2 cnt2 fail2 ran2 most own ->
  (forall a k, In (a, k) Lamc -> ~ In (a, k) (pi_sblk o kids keys cap) -> In (a, k) Lam2) ->
  (forall a k, In (a, k) Lam2 -> In (a, k) Lamc \/ ~ In (a - cf_head, k + cf_head) (ablocks B lyc Sc)) ->
  cnt2 + 2 * Z.of_nat (length (rest_atR tb text pc)) + 2 < 2 ^ 64 - 1 ->
  pi_cur B regs0 e q v text len tb d ly' S' Hp' W' mem' pc Lam2 peak2 cnt2 fail2 ran2 most own.
Hypothesis HFR : Permutation (frames S') (frames Sc).
(* grow's memnorm keep at the return state *)
Hypothesis HMK : YAkMemnorm.memnorm segs memc -> YAkMemnorm.memnorm segs mem'.

Local Notation OUT := (pil_step_out ly Se d o tb text len p q v e regs0 Lam peak cnt fail ran most own kr f n acc Di pc
  ly' S' Hp' W' regs' mem').

Lemma pil_s_mn : YAkMemnorm.memnorm segs mem'.
Proof. exact (HMK HMN). Qed.
Local Notation x0 := (rest_atR tb text p).
Local Notation y := (rest_atR tb text pc).
Local Notation mc := (rdW Wc memc).
Local Notation m' := (rdW W' mem').

Lemma pil_s_led : prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc most own.
Proof. destruct HCUR as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma pil_s_nodup : NoDup (pi_sblk o kids keys cap ++ Di).
Proof.
pose proof pil_s_led as HN. apply prh_ledger_nodup in HN. destruct HLED as (_ & _ & _ & HPL & _).
apply NoDup_ListNoDup. apply (Permutation_NoDup HPERM).
apply NoDup_ListNoDup. apply (pis_nodup_l _ _ Lam). apply NoDup_ListNoDup.
apply (Permutation_NoDup HPL). apply (NoDup_map_inv fst).
first [exact HN | apply NoDup_ListNoDup; exact HN].
Qed.

Lemma pil_s_incl : forall a k, In (a, k) (pi_sblk o kids keys cap ++ Di) -> In (a, k) Lamc.
Proof.
intros a k H. destruct HLED as (_ & _ & _ & HPL & _).
apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left.
exact (Permutation_in _ (Permutation_sym HPERM) H).
Qed.

Lemma pil_s_dlt : (d < PjGrammar.MAXD)%nat.
Proof.
destruct HCUR as (Hin & _). destruct Hin as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd).
unfold PjGrammar.MAXD. lia.
Qed.

Lemma pil_s_open : pis_open segs mc (prh_lin Lamc) v o 0 kids keys (Z.of_nat cap) (Z.of_nat (length (map snd acc)))
  (map snd acc) (map fst acc) Di.
Proof. exact (pil_open_of_cont _ _ _ _ _ _ _ _ _ _ HCONT pil_s_nodup HAP). Qed.

Lemma pil_s_len : n = length acc.
Proof. destruct HCONT as (_ & H & _). exact H. Qed.

Lemma pil_s_lenmap : length (map snd acc) = n.
Proof. rewrite length_map. symmetry. exact pil_s_len. Qed.

Lemma pil_s_le : (n <= cap)%nat.
Proof. destruct HCONT as (_ & _ & H & _). exact H. Qed.

Lemma pil_s_54 : Z.of_nat cap <= 2 ^ 54.
Proof. destruct HCONT as (_ & _ & _ & H & _). exact H. Qed.

Lemma pil_s_slots : (cap = 0%nat /\ kids = 0 /\ keys = 0) \/
  (0 < cap)%nat /\ In (kids, 56 * Z.of_nat cap) Lamc /\ (o = true -> In (keys, 8 * Z.of_nat cap) Lamc).
Proof. destruct HCONT as (_ & _ & _ & _ & H & _). exact H. Qed.

Lemma pil_s_depmap : Forall (fun t => (PjTree.depth t <= PjGrammar.MAXD - Nat.succ d)%nat) (map snd acc).
Proof. apply Forall_map. exact HDEP. Qed.

Lemma pil_s_fuel : exists f', f = S f'.
Proof. destruct f as [|f'] eqn:Ef; [exfalso; lia | exists f'; reflexivity]. Qed.

Lemma pil_s_run : forall f', f = S f' -> pi_run_eq d o x0 ok0 tr0 (S f') n cap acc y.
Proof. intros f' Ef. rewrite <- Ef. exact HRUN. Qed.

Lemma pil_s_room : forall f', f = S f' ->
  rd_room Sc (snd (fst (jrl prh_jr_strtod (S f') (Nat.succ d) o n cap (rev acc) y []))).
Proof. intros f' Ef. rewrite <- Ef. exact HROOM. Qed.

(* g_count has no wrap across the prefix and grow *)
Lemma pil_s_cnt : forall f', f = S f' ->
  cntc = cnt + Z.of_nat (PjGrammar.calls tr0) /\
  cnt + Z.of_nat (PjGrammar.calls tr0) + Z.of_nat (PjGrammar.calls (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap)))
    < 2 ^ 64 - 1.
Proof.
intros f' Ef. pose proof (pil_calls_bound d o _ ok0 tr0 f' n cap acc _ HX0 (pil_s_run f' Ef)) as HB.
destruct HLED as (_ & Hc & _). destruct HCNT0 as (H0 & H1).
split; [rewrite Hc; apply Z.mod_small; lia | lia].
Qed.

(* the cursor after a refusal: pi_cur's at the return state *)
Lemma pil_s_after : forall Lam2 peak2 cnt2 fail2 ran2,
  pi_cur B regs0 e q v text len tb d ly' S' Hp' W' mem' pc Lam2 peak2 cnt2 fail2 ran2 most own ->
  pj_in_afterR segs m' q text len (Z.of_nat d + 1) 33.
Proof.
intros Lam2 peak2 cnt2 fail2 ran2 (Hin & _).
destruct Hin as (V1 & V2 & V3 & Hrw & _ & _ & _ & Hp & _ & _ & _ & Hd).
exists pc, (Z.of_nat d + 1). split; [lia|]. split; [lia|]. auto.
Qed.

(* an arm's two travelling facts as tgrow_specX's post states them (pil_gpost), at the arm's outcomes okA *)
Local Notation GPERM okA := (Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
       (prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap) okA))).
Local Notation GPOS okA := (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
     (i : nat) (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sc ->
     PRH_Base.prh_run_at sm x os i (prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap) okA) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os
       (i + length (prhPg_evs ((if o then 6 else 5) =? 6)%Z (Z.of_nat n) (Z.of_nat cap) okA%list))%nat H0 hist' S').
(* a REFUSED arm's OUTCOME exclusion as tgrow_specX's batch-kit post states it, over the all-granted list prhPg_evs .. [] *)
Local Notation GEXCL := (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
     (i : nat) (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sc ->
     PRH_Base.prh_run_at sm x os i (prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap) []) ->
     PRH_Base.prh_cons_from sm x os i (length (prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap) [])) ->
     False).
(* the hull use of tgrow_specX's post (its tgrP_hull), over the all-granted list prhPg_evs .. [] *)
Local Notation GHULL := (PresetHullBudget.hull_used Sc S'
     (prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap) [])).
(* the kids-refused arm's injected-reading exclusion as tgrow_specX's post states it (its tgrP3_injected) *)
Local Notation GINJ := (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
     (i : nat) (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sc ->
     PRH_Base.prh_run_at sm x os i (prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap)
       (PresetReqAt.okk (Z.to_nat (failc - cntc)))) ->
     PRH_Base.prh_cons_from sm x os i (length (prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap)
       (PresetReqAt.okk (Z.to_nat (failc - cntc))))) ->
     cntc <= failc < cntc + Z.of_nat (PjGrammar.calls (PRH_Charge.prhPg_gtrace ((if o then 6 else 5) =? 6) (Z.of_nat n)
       (Z.of_nat cap))) -> False).

(* ... composed with the call state's: the arm's event list is rd_hevs of grow's trace g under okA (pil_evs_model),
   so pi_live_call extends the prefix's live requests over tr0 ++ g ... *)
Lemma pil_s_live : forall okA g,
  snd (fst (PjGrammar.grow o n cap okA)) = g -> GPERM okA ->
  PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf Se)) (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (tr0 ++ g).
Proof.
intros okA g Hg HP. rewrite pil_evs_model, Hg in HP. exact (PItems_posb.pi_live_call _ _ _ tr0 g HLIVE HP).
Qed.

(* ... and the position relation over tr0 ++ g (the position half of pi_posb_call; a refused arm's events are not the
   all-granted ones its hull use is stated over) ... *)
Lemma pil_s_pos : forall okA g,
  snd (fst (PjGrammar.grow o n cap okA)) = g -> GPOS okA ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist Se ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (tr0 ++ g)) ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs (tr0 ++ g)))%nat H0 hist' S'.
Proof.
intros okA g Hg HI sm x os i H0 hist Hi Hr. rewrite pil_evs_model, Hg in HI.
rewrite PresetReqAt.rd_hevs_app in Hr |- *. apply PRH_Base.prh_run_at_app_iff in Hr. destruct Hr as [Hr1 Hr2].
destruct (PItems_posb.pi_posb_post _ _ _ HPOSB sm x os i H0 hist Hi Hr1) as (hist1 & Hi1).
destruct (HI sm x os _ H0 hist1 Hi1 Hr2) as (hist2 & Hi2).
exists hist2. rewrite length_app, Nat.add_assoc. exact Hi2.
Qed.

(* ... and, on an arm whose trace g is grow's granted one, the whole of pi_posb (pi_posb_call, with the post's hull
   use over the all-granted list, which is then g's) *)
Lemma pil_s_trav : forall okA g,
  snd (fst (PjGrammar.grow o n cap okA)) = g -> snd (fst (PjGrammar.grow o n cap [])) = g ->
  GPERM okA -> GPOS okA -> GHULL ->
  PItems_posb.pi_posb Se S' (tr0 ++ g) /\
  PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf Se)) (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (tr0 ++ g).
Proof.
intros okA g Hg Hg0 HP HI HH. split; [| exact (pil_s_live okA g Hg HP)].
rewrite pil_evs_model, Hg in HI. rewrite pil_evs_model, Hg0 in HH.
exact (PItems_posb.pi_posb_call Se Sc S' tr0 g HPOSB HI HH).
Qed.

(* ---- The batch kit: the granted prefix, the call's all-granted trace, the OUTCOME's exclusions, the free order ---- *)
Lemma pil_s_grant : ok0 = repeat true (PjGrammar.calls tr0).
Proof. exact HGRANT. Qed.

(* no call of the granted prefix is the chosen failure (pi_led's prh_oks under pi_grant) *)
Lemma pil_s_oks : forall i, (i < PjGrammar.calls tr0)%nat -> cnt + Z.of_nat i <> fail.
Proof.
intros i Hi E. destruct HLED as ((O1 & _ & _) & _). pose proof (O1 i Hi E) as Hn.
rewrite pil_s_grant, (PItems_ledk1.pik1_ok_upto_repeat _ (S i) i ltac:(lia)) in Hn. discriminate Hn.
Qed.

(* the prefix's peak: its refusal peak is 0 *)
Lemma pil_s_pk : peakc = Z.max (Z.max peak (Ledger.lsum Lam + hpeakR tr0)) 0.
Proof.
destruct HLED as (_ & _ & _ & _ & _ & _ & HPK). rewrite HPK, pil_s_grant.
rewrite (prh_refused_peak_granted _ _ _ _ _ (PItems_ledk1.pik1_grant_granted _ _ _ _)). reflexivity.
Qed.

Lemma pil_s_lsum : 0 <= Ledger.lsum Lamc <= peakc.
Proof. pose proof pil_s_led as H. apply prh_ledger_bounds in H. destruct H as (H & _). exact H. Qed.

(* the granted prefix keeps g_ran_out (PItems_ledk1.pik1_move_ran) *)
Lemma pil_s_ran : ranc = ran.
Proof.
assert (G : prh_granted ok0 cnt fail (PjGrammar.calls tr0))
  by (rewrite pil_s_grant; apply PItems_ledk1.pik1_grant_granted).
exact (PItems_ledk1.pik1_move_ran Lam peak cnt fail ran most ok0 tr0 tr0 D0 Lamc peakc cntc failc ranc G HLED).
Qed.

(* the prefix trace is well formed (a prefix of the run's trace, pvm_wf_items) *)
Lemma pil_s_wf0 : pvm_wf tr0.
Proof.
destruct (jrl prh_jr_strtod f (S d) o n cap (rev acc) y []) as [[r t] ok2] eqn:Ej.
pose proof (pvm_wf_items d o x0 (ok0 ++ [])) as W. rewrite (HRUN [] r t ok2 Ej) in W. cbn [fst snd] in W.
unfold pvm_wf in W. apply pvm_wf_from_app in W. exact (proj1 W).
Qed.

(* THE CALL'S ALL-GRANTED TRACE: the prefix (granted, pi_grant), grow's granted trace, then the member's body at grow's
   granted cap (PItems_value_model.v pvm_gt_grant, pil_gt_split) *)
Lemma pil_s_gt : forall f', f = S f' ->
  PRH_Charge.prhPi_gtrace d o x0 = tr0 ++ PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap) ++
    snd (fst (pi_jrb f' (Nat.succ d) o n (pil_gcap n cap) (rev acc) y [])).
Proof.
intros f' Ef. unfold PRH_Charge.prhPi_gtrace.
rewrite (pvm_gt_grant d o x0 ok0 tr0 (jrl prh_jr_strtod f (S d) o n cap (rev acc) y) HRUN pil_s_grant). cbn [snd].
f_equal. rewrite Ef. exact (pil_gt_split f' (S d) o n cap (rev acc) y).
Qed.

Lemma pil_s_wfg : pvm_wf (PRH_Charge.prhPi_gtrace d o x0).
Proof. exact (pvm_wf_items d o x0 []). Qed.

(* the entry's g_fail_at is a word (the call state's, or inside the prefix's window) *)
Lemma pil_s_fail_bnd : forall f', f = S f' -> 0 <= fail < 2 ^ 64.
Proof.
intros f' Ef. destruct (pil_s_cnt f' Ef) as (Hcc & Hno).
pose proof pil_s_led as HLc. apply prh_ledger_bounds in HLc. destruct HLc as (_ & _ & _ & Hfb & _).
destruct HLED as (_ & _ & (F1 & F2) & _). destruct HCNT0 as (H0 & _).
destruct (Z_lt_le_dec fail cnt) as [Hl|Hl]; [rewrite <- (F2 ltac:(lia)); exact Hfb|].
destruct (Z_lt_le_dec fail (cnt + Z.of_nat (PjGrammar.calls tr0))) as [Hu|Hu]; [lia|].
rewrite <- (F2 ltac:(lia)). exact Hfb.
Qed.

(* the capacity after the member's grow is grow's granted cap *)
Lemma pil_s_ncap : PresetReqAt.ncap (Nat.succ n) = pil_gcap n cap.
Proof. rewrite HCAPN. reflexivity. Qed.

Lemma pil_s_fl : forall f', f = S f' -> pi_fl_eq d o x0 ok0 (S f') n cap af y.
Proof. intros f' Ef. rewrite <- Ef. exact HFL. Qed.

(* THE OUTCOME AT A REFUSED GROW: a run whose next events are the call's all-granted ones passes the call state with
   grow's all-granted events next, its reallocs consumer events, which grow's refused arm excludes *)
Lemma pil_s_excl : forall f', f = S f' ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sc ->
     PRH_Base.prh_run_at sm x os i (prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap) []) ->
     PRH_Base.prh_cons_from sm x os i (length (prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap) [])) ->
     False) ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist Se ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (PRH_Charge.prhPi_gtrace d o x0)) ->
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (PRH_Charge.prhPi_gtrace d o x0))) -> False.
Proof.
intros f' Ef HX sm x os i H0 hist HP HR HC.
rewrite (pil_s_gt f' Ef), !PresetReqAt.rd_hevs_app in HR, HC.
apply PRH_Base.prh_run_at_app_iff in HR as [HR1 HR2]. apply PRH_Base.prh_run_at_app_iff in HR2 as [HR2 _].
destruct (PItems_posb.pi_posb_post _ _ _ HPOSB sm x os i H0 hist HP HR1) as (hist1 & HP1).
rewrite !length_app in HC.
assert (HC1 : PRH_Base.prh_cons_from sm x os (i + length (PresetReqAt.rd_hevs tr0))
  (length (PresetReqAt.rd_hevs (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap)))))
  by (eapply PRH_Base.prh_cons_from_sub; [|exact HC]; lia).
assert (EG : PresetReqAt.rd_hevs (snd (fst (PjGrammar.grow o n cap []))) =
  PresetReqAt.rd_hevs (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap)))
  by (unfold PRH_Charge.prhPg_gtrace; rewrite !Nat2Z.id; reflexivity).
rewrite pil_evs_model, EG in HX.
exact (HX sm x os _ H0 hist1 HP1 HR2 HC1).
Qed.

(* ... and at grow's CHOSEN failure (its j-th realloc, j < its granted calls): the window premise contradicts it *)
Lemma pil_s_wexcl : forall f' (j : nat), f = S f' -> cntc + Z.of_nat j = failc ->
  (j < PjGrammar.calls (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap)))%nat ->
  ~ (fail < cnt \/ cnt + Z.of_nat (PjGrammar.calls (PRH_Charge.prhPi_gtrace d o x0)) <= fail).
Proof.
intros f' j Ef Hj Hjc HW.
destruct (pil_s_cnt f' Ef) as (Hcc & Hno). destruct HCNT0 as (H0 & _).
destruct HLED as (_ & _ & Hfa & _).
pose proof (proj1 (pil_fail_at cnt fail _ cntc failc (Z.of_nat j) Hfa Hcc ltac:(lia) ltac:(unfold SIZE_MAXZ; lia)) Hj)
  as E.
rewrite (pil_s_gt f' Ef), !calls_app in HW. lia.
Qed.

(* THE HULL USE AT A REFUSED GROW: the prefix's use over its events (pi_posb), then grow's own over its all-granted list
   (GHULL), are inside the call's all-granted list (PItems_posb.pi_posb_hull_call; the list split by pil_s_gt) *)
Lemma pil_s_hullx : GHULL -> forall f', f = S f' ->
  PresetHullBudget.hull_used Se S' (PresetReqAt.rd_hevs (PRH_Charge.prhPi_gtrace d o x0)).
Proof.
intros HH f' Ef. rewrite (pil_s_gt f' Ef), !PresetReqAt.rd_hevs_app.
assert (EG : PresetReqAt.rd_hevs (snd (fst (PjGrammar.grow o n cap []))) =
  PresetReqAt.rd_hevs (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap)))
  by (unfold PRH_Charge.prhPg_gtrace; rewrite !Nat2Z.id; reflexivity).
rewrite pil_evs_model, EG in HH.
exact (PItems_posb.pi_posb_hull_call Se Sc S' tr0 _ _ _ HPOSB eq_refl HH).
Qed.

(* THE INJECTED READING AT grow's CHOSEN failure (its j-th realloc, j < its granted calls): the refused call of the
   granted prefix, j granted calls of grow and the chosen one is the call fail - cnt (pil_fail_at) *)
Lemma pil_s_chosen : forall f' (j : nat) k, f = S f' -> cntc + Z.of_nat j = failc ->
  (j < PjGrammar.calls (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap)))%nat ->
  prh_granted (ok0 ++ repeat true j ++ [false]) cnt fail k.
Proof.
intros f' j k Ef Hj Hjc i _ Hn.
destruct (pil_s_cnt f' Ef) as (Hcc & Hno). destruct HCNT0 as (H0 & _).
destruct HLED as (_ & _ & Hfa & _).
pose proof (proj1 (pil_fail_at cnt fail _ cntc failc (Z.of_nat j) Hfa Hcc ltac:(lia) ltac:(unfold SIZE_MAXZ; lia)) Hj)
  as E.
rewrite pil_s_grant, app_assoc, pil_rep_app in Hn.
destruct (Nat.lt_ge_cases i (PjGrammar.calls tr0 + j)) as [Hl|Hl].
- rewrite app_nth1 in Hn by (rewrite repeat_length; exact Hl). rewrite nth_repeat in Hn. discriminate Hn.
- rewrite app_nth2 in Hn by (rewrite repeat_length; exact Hl). rewrite repeat_length in Hn.
  destruct (i - (PjGrammar.calls tr0 + j))%nat as [|m] eqn:Em; [lia|].
  destruct m; cbn in Hn; discriminate Hn.
Qed.

(* THE INJECTED READING AT A REFUSED GROW: a model run under PresetReqAt.okk at the call fail - cnt passes the call
   state (the prefix is granted, so the call is not one of its calls) with grow's events under the shifted grant list
   next; inside grow's window the arm's injected exclusion refutes it, past the window grow's list is the all-granted
   one and the arm's OUTCOME exclusion refutes it *)
Lemma pil_s_injx : forall f', f = S f' -> (cap <= n)%nat -> GEXCL -> GINJ ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist Se ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d o x0
    (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) ->
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d o x0
    (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) ->
  cnt <= fail < cnt + Z.of_nat (PjGrammar.calls (PRH_Charge.prhPi_gtrace d o x0)) -> False.
Proof.
intros f' Ef Hge HX HJ sm x os i H0 hist HP HR HC HW.
destruct (pil_s_cnt f' Ef) as (Hcc & Hno). destruct HCNT0 as (H0c & _).
assert (HK : (PjGrammar.calls tr0 <= Z.to_nat (fail - cnt))%nat).
{ destruct (Nat.lt_ge_cases (Z.to_nat (fail - cnt)) (PjGrammar.calls tr0)) as [Hl|Hl]; [|exact Hl].
  exfalso. apply (pil_s_oks _ Hl). lia. }
set (k' := (Z.to_nat (fail - cnt) - PjGrammar.calls tr0)%nat).
assert (EK : PresetReqAt.okk (Z.to_nat (fail - cnt)) = ok0 ++ PresetReqAt.okk k').
{ rewrite pil_s_grant. unfold PresetReqAt.okk. rewrite app_assoc, pil_rep_app. f_equal. f_equal. unfold k'. lia. }
destruct (jrl prh_jr_strtod f (S d) o n cap (rev acc) y (PresetReqAt.okk k')) as [[r t] ok2] eqn:Ej.
rewrite EK, (HRUN _ r t ok2 Ej) in HR, HC. cbn [fst snd] in HR, HC.
assert (ET : exists t', t = snd (fst (PjGrammar.grow o n cap (PresetReqAt.okk k'))) ++ t').
{ rewrite Ef, pi_jrl_unfold in Ej.
  destruct (prhReader_jbind_pre _ _ (PjGrammar.grow o n cap) (fun cap1 => pi_jrb f' (S d) o n cap1 (rev acc) y)
    (PresetReqAt.okk k')) as (t' & Et).
  rewrite Ej in Et. cbn [fst snd] in Et. exists t'. exact Et. }
destruct ET as (t' & ->).
rewrite !PresetReqAt.rd_hevs_app in HR, HC. rewrite !length_app in HC.
apply PRH_Base.prh_run_at_app_iff in HR as [HR1 HR2]. apply PRH_Base.prh_run_at_app_iff in HR2 as [HR2 _].
destruct (PItems_posb.pi_posb_post _ _ _ HPOSB sm x os i H0 hist HP HR1) as (hist1 & HP1).
assert (HC1 : PRH_Base.prh_cons_from sm x os (i + length (PresetReqAt.rd_hevs tr0))
  (length (PresetReqAt.rd_hevs (snd (fst (PjGrammar.grow o n cap (PresetReqAt.okk k')))))))
  by (eapply PRH_Base.prh_cons_from_sub; [|exact HC]; lia).
rewrite <- pil_evs_model in HR2, HC1.
(* the call state's counters: cntc = cnt + calls tr0, and failc = fail past the prefix's window *)
destruct HLED as (_ & _ & (F1 & F2) & _).
assert (Hfc : failc = fail) by (apply F2; lia).
assert (Hgc : PjGrammar.calls (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap)) = (if o then 2 else 1)%nat)
  by (rewrite pil_gtrace_ge by exact Hge; destruct o; reflexivity).
destruct (Nat.lt_ge_cases k' (if o then 2 else 1)%nat) as [Hin | Hout].
- (* inside grow's window: the arm's injected exclusion *)
  assert (Ek' : Z.to_nat (failc - cntc) = k') by (unfold k'; lia).
  rewrite <- Ek' in HR2, HC1.
  apply (HJ sm x os _ H0 hist1 HP1 HR2 HC1).
  rewrite pil_ty6, Hgc. unfold k' in Hin. lia.
- (* past it: grow's list is the all-granted one, the OUTCOME exclusion *)
  assert (EA : prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap) (PresetReqAt.okk k') =
    prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap) []).
  { apply prhPg_evs_arm. right. rewrite pil_ty6. split.
    - assert (Hg1 : (1 <= if o then 2 else 1)%nat) by (case o; cbn; lia).
      rewrite PresetRun.okk_true by lia. reflexivity.
    - intros _ Ho. rewrite Ho in Hout. cbn in Hout. rewrite PresetRun.okk_true by lia. reflexivity. }
  rewrite EA in HR2, HC1.
  exact (HX sm x os _ H0 hist1 HP1 HR2 HC1).
Qed.

(* the completed slots' free order after a GRANTED grow: the slot array moved (or kept) to kids', the members' blocks
   kept (PItems_forder.v pis_fo_items_xfer) *)
Lemma pil_s_fo_mv : forall kids' keys' (Lam' : list (Z * Z)),
  (forall x k, In (x, k) Di -> prh_lin Lam' x k) ->
  pis_moved segs mc m' kids kids' (56 * Z.of_nat n) ->
  (forall i, 0 <= i < 56 * Z.of_nat n -> writable_at segs mc (kids + i) -> writable_at segs m' (kids' + i)) ->
  ((0 < n)%nat -> kids' mod 8 = 0) ->
  (kids' = kids \/ pis_apart_n Di kids' (56 * Z.of_nat n)) ->
  (o = true -> pis_moved segs mc m' keys keys' (8 * Z.of_nat n)) ->
  pi_forder m' (prh_lin Lam') o kids' keys' n Di acc af.
Proof.
intros kids' keys' Lam' HL Hmv HW H8 Hap Hy HH nn Hnn.
destruct (HFO HH nn Hnn) as (Facc & HI & HM). exists Facc. split; [|exact HM].
exact (PItems_forder.pis_fo_items_xfer segs nn mc (prh_lin Lamc) m' (prh_lin Lam') o kids keys kids' keys' n Di Facc HI
  HL HKDI Hmv HW H8 Hap Hy).
Qed.

(* the members' capacities likewise (pil_ncaps_mv) *)
Lemma pil_s_ncaps_mv : forall kids', pis_moved segs mc m' kids kids' (56 * Z.of_nat n) -> pi_ncaps m' kids' acc.
Proof.
intros kids' Hmv. exact (pil_ncaps_mv (w_H Wc) memc m' (prh_lin Lamc) o v kids keys n cap acc Di kids' HCONT HNCAPS
  HKDI Hmv).
Qed.

(* the members fit every depth bound nn >= MAXD - S d (pi_forder's premise at a refusal exit) *)
Lemma pil_s_dep : forall nn, (PjGrammar.MAXD - S d <= nn)%nat -> Forall (fun mb => (PjTree.depth (snd mb) <= nn)%nat) acc.
Proof.
intros nn Hnn. apply Forall_forall. intros mb Hmb.
pose proof (proj1 (Forall_forall _ _) HDEP mb Hmb) as H. cbv beta in H. exact (Nat.le_trans _ _ _ H Hnn).
Qed.

(* ---- arm 1: room left (n < cap): nothing moves ---- *)
Lemma pil_arm_room :
  Z.of_nat n < Z.of_nat cap -> getr regs' 10 = w64 0 -> ablocks B ly' S' = ablocks B lyc Sc ->
  prh_ledger B ly' S' Hp' W' mem' Lamc peakc cntc failc ranc most own ->
  pj_hdrR segs m' v (if o then 6 else 5) 0 0 kids keys (Z.of_nat n) (Z.of_nat cap) ->
  (forall lo hi x, In (lo, hi) (ablocks_fp (prhReader_ab (kids_blkR kids (Z.of_nat cap) ++
       keys_blkR (if o then 6 else 5) keys (Z.of_nat cap)))) ->
     lo <= x < hi -> aview segs (w_H W') mem' x = aview segs (w_H Wc) memc x) ->
  room_live_cf S' ->
  blocks_bytes S' <= blocks_bytes Sc +
    prh_held (PRH_Charge.prhPg_gtrace ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap)) ->
  GPERM [] -> GPOS [] -> GHULL ->
  OUT.
Proof.
intros Hlt H10 HAB HL' Hh' Hkeep HRL HBB' HPm HIm HHU.
assert (Hlt' : (n < cap)%nat) by lia. rewrite pil_ty6, pil_gtrace_lt in HBB' by exact Hlt'.
destruct (pil_s_trav [] [] ltac:(rewrite (pil_grow_lt o n cap [] Hlt'); reflexivity)
  ltac:(rewrite (pil_grow_lt o n cap [] Hlt'); reflexivity) HPm HIm HHU) as (HPB' & HLV').
rewrite app_nil_r in HPB', HLV'.
destruct pil_s_fuel as [f' Ef].
(* the slots read so far (and an object's key slots) keep their bytes and stay writable: nothing is written on this arm *)
assert (HSL : forall x, kids <= x < kids + 56 * Z.of_nat n -> pis_same segs mc m' x).
{ intros x Hx. destruct pil_s_slots as [(Hc & _) | (_ & Hkb & _)]; [lia|].
  apply (pil_keep_same Wc W' memc mem' _ kids (56 * Z.of_nat cap) x Hkeep);
    [apply pil_fp_kids; lia | lia | lia |].
  apply (pil_lam_wr ly' S' Hp' W' mem' md' Lamc peakc cntc failc ranc most own kids (56 * Z.of_nat cap) x HAR HL' Hkb). lia. }
assert (HKY : o = true -> forall x, keys <= x < keys + 8 * Z.of_nat n -> pis_same segs mc m' x).
{ intros Ho x Hx. destruct pil_s_slots as [(Hc & _) | (_ & _ & Hyb)]; [lia|]. rewrite Ho in Hkeep.
  apply (pil_keep_same Wc W' memc mem' _ keys (8 * Z.of_nat cap) x Hkeep);
    [apply pil_fp_keys; lia | lia | lia |].
  apply (pil_lam_wr ly' S' Hp' W' mem' md' Lamc peakc cntc failc ranc most own keys (8 * Z.of_nat cap) x HAR HL'
    (Hyb Ho)). lia. }
assert (Hmv : pis_moved segs mc m' kids kids (56 * Z.of_nat n)) by (intros i Hi; exact (proj1 (HSL (kids + i) ltac:(lia)))).
left. split; [exact H10|]. split; [exact pil_s_mn|].
exists f', cap, kids, keys, ok0, tr0, D0, Lamc, peakc, cntc, failc, ranc.
split; [exact Ef|].
split; [apply HKCUR; [exact HL' | intros a k Ha _; exact Ha | intros a k Ha; left; exact Ha | lia]|].
split; [exact Hlt'|].
split.
{ apply (pil_cont_of_open m' (prh_lin Lamc) o v kids keys n cap acc Di);
    [| exact pil_s_len | exact pil_s_le | exact pil_s_54].
  eapply (pis_frame segs); [exact pil_s_open | destruct o; exact Hh' | lia | |].
  - intros a k Ha. unfold prh_lin. apply pil_s_incl. rewrite pil_sblk_slots. exact Ha.
  - intros x Hx. unfold pis_ifoot in Hx. rewrite pil_s_lenmap in Hx.
    destruct Hx as [Hx | [[Ho Hx] | Hx]]; [exact (HSL x Hx) | exact (HKY Ho x Hx) | exact (HKDI x Hx)]. }
split; [exact HDEP|]. split; [exact HAP|]. split; [exact HPERM|].
split; [lia|].
split.
{ pose proof (pil_runB d o _ ok0 tr0 f' n cap acc _ [] [] cap (pil_s_run f' Ef)) as H.
  rewrite !app_nil_r in H. apply H. intros ok1. cbn [app]. apply pil_grow_lt. exact Hlt'. }
split; [exact HLED|].
split.
{ destruct HBLK as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [rewrite HAB; exact B2|].
  split; [exact (Permutation_trans HFR B3) | exact B4]. }
split; [exact HPB'|]. split; [exact HLV'|].
split; [unfold prh_held in HBB'; cbn [PjGrammar.held PjGrammar.calls] in HBB'; lia|].
split; [exact HOK|]. split; [exact HLS|].
split.
{ pose proof (pil_gt_split f' (Nat.succ d) o n cap (rev acc) y) as HS. rewrite pil_gcap_lt in HS by exact Hlt'.
  assert (HR' : rd_room Sc (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap) ++
    snd (fst (pi_jrb f' (Nat.succ d) o n cap (rev acc) y [])))) by (rewrite <- HS; exact (pil_s_room f' Ef)).
  apply (pvm_room_after Sc S' _ _ HR' HRL). rewrite pil_gtrace_lt by exact Hlt'.
  rewrite pil_evs_model, (pil_grow_lt o n cap [] Hlt') in HPm. cbn [fst snd] in HPm. exact HPm. }
(* The batch kit's tail: no call, so the granted prefix and the order list are the call state's; cap = ncap n = ncap (S n) *)
split; [exact HGRANT|].
split; [rewrite pil_s_ncap, (pil_gcap_lt n cap Hlt'); reflexivity|].
split; [exact (pil_s_ncaps_mv kids Hmv)|].
exists af. split.
- apply (pil_s_fo_mv kids keys Lamc).
  + intros x k Hin. unfold prh_lin. apply pil_s_incl. apply in_or_app. right. exact Hin.
  + exact Hmv.
  + intros i Hi Hw. exact (proj2 (HSL (kids + i) ltac:(lia)) Hw).
  + intros Hn0. destruct pil_s_slots as [(Hc & _) | (_ & Hkb & _)]; [lia|].
    destruct (pil_lam_hb _ _ _ _ _ _ _ _ _ _ _ _ _ _ pil_s_led Hkb) as (_ & _ & Hm). lia.
  + left. reflexivity.
  + intros Ho i Hi. exact (proj1 (HKY Ho (keys + i) ltac:(lia))).
- pose proof (pil_flB d o _ ok0 f' n cap af _ [] [] cap (pil_s_fl f' Ef) (fun ok1 => pil_grow_lt o n cap ok1 Hlt')) as HF.
  rewrite app_nil_r in HF. exact HF.
Qed.

(* ---- arms 2 and 3: the kids realloc fails (the chosen failure, or a refusal); nothing moves ---- *)
Lemma pil_arm_kfail : forall peak2 cnt2 fail2 ran2,
  Z.of_nat n = Z.of_nat cap -> getr regs' 10 = w64 (-1) -> ablocks B ly' S' = ablocks B lyc Sc ->
  prh_ledger B ly' S' Hp' W' mem' Lamc peak2 cnt2 fail2 ran2 most own ->
  pj_hdrR segs m' v (if o then 6 else 5) 0 0 kids keys (Z.of_nat n) (Z.of_nat cap) ->
  bytes_at W' mem' kids kb -> ((if o then 6 else 5) = 6 -> bytes_at W' mem' keys yb) ->
  room_live_cf S' ->
  ((cntc = failc /\ peak2 = peakc /\ cnt2 = cntc + 1 /\ fail2 = SIZE_MAXZ /\ ran2 = ranc) \/
   (cntc <> failc /\
    peak2 = (if Z.of_nat cap =? 0 then Z.max peakc (Z.min SIZE_MAXZ (Ledger.lsum Lamc + 56 * cap2R (Z.of_nat cap)))
             else Z.max peakc (Z.min SIZE_MAXZ (Ledger.lsum Lamc - 56 * Z.of_nat cap + 56 * cap2R (Z.of_nat cap)))) /\
    cnt2 = (cntc + 1) mod 2 ^ 64 /\ fail2 = failc /\
    ran2 = (if 56 * cap2R (Z.of_nat cap) <=? most then 1 else ranc) /\ GEXCL /\ GINJ)) ->
  GPERM [false] -> GPOS [false] -> GHULL ->
  OUT.
Proof.
intros peak2 cnt2 fail2 ran2 Hneq H10 HAB HL' Hh' Hkb' Hyb' HRL Hcase HPm HIm HHU.
assert (Hn : n = cap) by lia. assert (Hge : (cap <= n)%nat) by lia.
pose proof (pil_cap2R cap) as Hc2.
change (if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat) with (pil_c2 cap) in Hc2.
destruct pil_s_fuel as [f' Ef].
destruct (pil_s_cnt f' Ef) as (Hcc & Hno). rewrite pil_gtrace_ge in Hno by lia.
assert (Hgc : PjGrammar.calls (EGrow (56 * cap) (56 * pil_c2 cap) :: (if o then [EGrow (8 * cap) (8 * pil_c2 cap)] else [])) =
  (if o then 2 else 1)%nat) by (destruct o; reflexivity). rewrite Hgc in Hno.
set (G := [EFail (56 * pil_c2 cap)]).
assert (HGR : PjGrammar.grow o n cap [false] = (None, G, [])).
{ destruct o; [apply pil_grow_obj_no1 | apply pil_grow_arr_no]; lia. }
assert (HGg : snd (fst (PjGrammar.grow o n cap [false])) = G) by (rewrite HGR; reflexivity).
destruct (HBYT Hn) as (Hkb & Hlkb & Hyb).
pose proof pil_s_lsum as HLs.
assert (Hc2' : cnt2 = cntc + 1).
{ destruct Hcase as [(_ & _ & -> & _) | (_ & _ & -> & _)]; [reflexivity | apply Z.mod_small; lia]. }
pose proof (HKCUR Lamc peak2 cnt2 fail2 ran2 HL' ltac:(intros a k Ha _; exact Ha)
  ltac:(intros a k Ha; left; exact Ha) ltac:(lia)) as HC'.
(* the call's own move (fuzz_realloc's arm), then the whole move: the granted prefix and the call *)
assert (HMV : rd_ledger_move Lamc peakc cntc failc ranc most [false]
  (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap)) G [] Lamc peak2 cnt2 fail2 ran2).
{ rewrite (pil_gtrace_ge o n cap Hge). apply pil_mv_fail1; [exact HLs | lia | lia |].
  destruct Hcase as [(Hcf & -> & -> & -> & ->) | (Hcf & -> & -> & -> & -> & _ & _)];
    [left; repeat split; first [exact Hcf | reflexivity] | right].
  split; [exact Hcf|]. split; [rewrite Hc2; destruct (Z.eqb_spec (Z.of_nat cap) 0); lia|].
  split; [reflexivity|]. split; [reflexivity|]. rewrite Hc2.
  replace (56 * Z.of_nat (pil_c2 cap)) with (Z.of_nat (56 * pil_c2 cap)) by lia. reflexivity. }
assert (Hcb : cnt + Z.of_nat (PjGrammar.calls tr0 + PjGrammar.calls G) < SIZE_MAXZ)
  by (subst G; cbn [PjGrammar.calls PjGrammar.is_call]; unfold SIZE_MAXZ; lia).
assert (HLM : rd_ledger_move Lam peak cnt fail ran most (ok0 ++ [false]) (PRH_Charge.prhPi_gtrace d o x0) (tr0 ++ G) D0
  Lamc peak2 cnt2 fail2 ran2).
{ rewrite (pil_s_gt f' Ef).
  exact (pvm_ledger_app Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc [false]
    (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap)) G [] Lamc peak2 cnt2 fail2 ran2 _
    pil_s_wf0 I HOK (proj1 (proj1 HCNT0)) Hcb (pil_s_fail_bnd f' Ef)
    ltac:(rewrite pil_s_grant; apply PItems_ledk1.pik1_grant_granted)
    ltac:(rewrite (pil_gtrace_ge o n cap Hge); subst G; destruct o; cbn; lia) HLED HMV). }
assert (HhG : hpeakR (tr0 ++ G) = hpeakR tr0)
  by (subst G; rewrite hpeak_app; cbn [hpeakR held_ev]; pose proof (pil_held_hpeak tr0); lia).
assert (HO : pis_open segs mc (prh_lin Lamc) v o 0 kids keys (Z.of_nat cap) (Z.of_nat (length (map snd acc)))
  (map snd acc) (map fst acc) Di) by exact pil_s_open.
assert (Hmk : pis_moved segs mc m' kids kids (56 * Z.of_nat cap))
  by (rewrite <- Hlkb; exact (pil_garr8_moved _ _ _ _ _ Hkb Hkb')).
assert (Hmy : o = true -> pis_moved segs mc m' keys keys (8 * Z.of_nat cap)).
{ intros Ho'. destruct (Hyb Ho') as (Hy & Hly). rewrite <- Hly.
  apply (pil_garr8_moved _ _ _ _ _ Hy). apply Hyb'. rewrite Ho'. reflexivity. }
assert (HW : forall i, 0 <= i < 56 * Z.of_nat (length (map snd acc)) -> writable_at segs mc (kids + i) ->
  writable_at segs m' (kids + i)).
{ intros i Hi _. rewrite pil_s_lenmap in Hi.
  destruct pil_s_slots as [(Hc0 & _) | (_ & Hkin & _)]; [lia|].
  apply (pil_lam_wr ly' S' Hp' W' mem' md' Lamc peak2 cnt2 fail2 ran2 most own kids (56 * Z.of_nat cap) _ HAR HL' Hkin).
  lia. }
right. split; [exact H10|]. split; [exact pil_s_mn|]. intros regs'' md'' H10''.
(* the text's post, built through its record (PRH_FnParse.tpiP_R) *)
refine (tpiP_Q_of_R (ok := ok0 ++ [false]) (res := None) (tr := tr0 ++ G) (okr := []) (D := D0) (Lam' := Lamc)
  (peak' := peak2) (cnt' := cnt2) (fail' := fail2) (ran' := ran2) md''
  {| tpiP_run := pil_run_refused d o _ ok0 tr0 f' n cap acc _ [false] G (pil_s_run f' Ef) HGR;
     tpiP_ledger := HL'; tpiP_room := HRL; tpiP_hull := pil_s_hullx HHU f' Ef;
     tpiP_live := pil_s_live [false] G HGg HPm; tpiP_pos := pil_s_pos [false] G HGg HIm;
     tpiP_outcome := _; tpiP_injected := _; tpiP_ledger_move := HLM; tpiP_blocks_move := _; tpiP_bytes := _;
     tpiP_lsum := _; tpiP_arm := _ |}).
- (* THE OUTCOME: the chosen failure is among the granted calls (the window premise), a refusal is grow's exclusion *)
  intros sm x os i H0 hist HP HR HC HW'. exfalso.
  destruct Hcase as [(Hcf & _) | (Hcf & _ & _ & _ & _ & HX & _)].
  + apply (pil_s_wexcl f' 0 Ef ltac:(lia) ltac:(rewrite (pil_gtrace_ge o n cap Hge); destruct o; cbn; lia) HW').
  + exact (pil_s_excl f' Ef HX sm x os i H0 hist HP HR HC).
- (* THE INJECTED READING: the chosen failure is the refused call; a refusal is excluded by grow's two clauses *)
  intros sm x os i H0 hist HP HR HC HW'.
  destruct Hcase as [(Hcf & _) | (Hcf & _ & _ & _ & _ & HX & HJ)].
  + exact (pil_s_chosen f' 0 _ Ef ltac:(lia) ltac:(rewrite (pil_gtrace_ge o n cap Hge); destruct o; cbn; lia)).
  + exfalso. exact (pil_s_injx f' Ef Hge HX HJ sm x os i H0 hist HP HR HC HW').
- destruct HBLK as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [rewrite HAB; exact B2|].
  split; [exact (Permutation_trans HFR B3)|]. rewrite HhG. exact B4.
- rewrite (blocks_bytes_bsum B ly' S'), HAB, <- (blocks_bytes_bsum B lyc Sc), pvm_prh_held_app.
  assert (HG0 : 0 <= prh_held G) by (subst G; unfold prh_held; cbn; pose proof (@cf_head_nonneg cp); lia). lia.
- rewrite held_app; subst G; cbn [PjGrammar.held held_ev]; lia.
- split; [exact H10''|].
  (* the partial free order: the completed slots, then both arrays as the refused grow kept them (PresetReqAt.gheld) *)
  split.
  { intros HH. apply (PItems_forder.pi_forder_post d _ pil_s_dlt). intros nn Hnn.
    destruct (HFO HH nn (pil_s_dep nn Hnn)) as (Facc & HI & HM).
    exists (Facc ++ pis_slots o kids keys (Z.of_nat cap)). split.
    - apply (pvm_foR_perm segs m' (prh_lin Lamc) (S nn) v (pis_slots o kids keys (Z.of_nat cap) ++ Di) D0);
        [rewrite <- pil_sblk_slots; apply Permutation_sym; exact HPERM|].
      rewrite <- pil_s_lenmap in HI.
      apply (PItems_forder.pis_fo_grow_kept segs mc m' (prh_lin Lamc) v o 0 kids keys (Z.of_nat cap) (map snd acc)
        (map fst acc) Di nn Facc HO); [rewrite pil_s_lenmap; destruct o; exact Hh' | exact Hmk | exact Hmy | exact HW
        | exact HKDI | exact HI].
    - rewrite map_app, HM, (pil_fl_refused d o _ ok0 f' n cap af _ [false] G (pil_s_fl f' Ef) HGR). f_equal.
      subst G. rewrite (PItems_forder.pis_fo_kept_hb cf_head o kids keys (Z.of_nat cap) (56 * pil_c2 cap) HH ltac:(lia)),
        Nat2Z.id. reflexivity. }
  split; [exact (pil_s_after _ _ _ _ _ HC')|].
  apply (pil_fd_perm segs m' (prh_lin Lamc) _ v (pis_slots o kids keys (Z.of_nat cap) ++ Di) D0);
    [rewrite <- pil_sblk_slots; apply Permutation_sym; exact HPERM|].
  apply (pis_exit_grow_kept segs mc m' (prh_lin Lamc) v o 0 kids keys (Z.of_nat cap) (map snd acc) (map fst acc) Di d HO
    pil_s_dlt pil_s_depmap); [rewrite pil_s_lenmap; destruct o; exact Hh' | exact Hmk | exact Hmy | exact HW | exact HKDI].
Qed.

(* ---- the moved arms' shared facts ---- *)
Lemma pil_s_lam0 : forall Dold Drest Lam0, Permutation Lamc (Dold ++ Lam0) ->
  Permutation (pi_sblk o kids keys cap) (Dold ++ Drest) -> Permutation Lam0 (Drest ++ Di ++ Lam).
Proof.
intros Dold Drest Lam0 H1 H2. destruct HLED as (_ & _ & _ & HPL & _).
apply (Permutation_app_inv_l Dold).
assert (E : Permutation Lamc ((Dold ++ Drest) ++ Di ++ Lam)).
{ apply (Permutation_trans HPL). rewrite app_assoc. apply Permutation_app_tail.
  apply (Permutation_trans HPERM). apply Permutation_app_tail. exact H2. }
rewrite <- app_assoc in E. exact (Permutation_trans (Permutation_sym H1) E).
Qed.

Lemma pil_s_bl : forall Dold Drest bl, Permutation (ablocks B lyc Sc) (prhReader_ab Dold ++ bl) ->
  Permutation (pi_sblk o kids keys cap) (Dold ++ Drest) ->
  Permutation bl (prhReader_ab Drest ++ prhReader_ab Di ++ ablocks B ly Se).
Proof.
intros Dold Drest bl H1 H2. destruct HBLK as (_ & HB2 & _).
apply (Permutation_app_inv_l (prhReader_ab Dold)).
assert (E : Permutation (ablocks B lyc Sc) (prhReader_ab ((Dold ++ Drest) ++ Di) ++ ablocks B ly Se)).
{ apply (Permutation_trans HB2). apply Permutation_app_tail. apply Permutation_map.
  apply (Permutation_trans HPERM). apply Permutation_app_tail. exact H2. }
unfold prhReader_ab in E |- *. rewrite !map_app, <- !app_assoc in E.
exact (Permutation_trans (Permutation_sym H1) E).
Qed.

Lemma pil_s_newv : forall a K, In (a - cf_head, K + cf_head) (ablocks B ly' S') ->
  ~ In (a - cf_head, K + cf_head) (ablocks B lyc Sc) -> pj_apartR [(a, K)] v.
Proof.
intros a K Hin Hn b x Hb Hx. destruct Hb as [<- | []]. unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
pose proof (@cf_head_nonneg cp). apply (HNEWV _ _ x Hin Hn). lia.
Qed.

Lemma pil_s_dik : forall b, In b Di -> 0 <= snd b.
Proof.
intros [ab kb0] Hb. assert (Hl : In (ab, kb0) Lamc) by (apply pil_s_incl; apply in_or_app; right; exact Hb).
destruct (pil_lam_hb _ _ _ _ _ _ _ _ _ _ _ _ _ _ pil_s_led Hl) as (Hk & _). exact Hk.
Qed.

Lemma pil_s_apart_n : forall a K L0 rest, 0 <= K -> 0 <= L0 -> L0 <= K ->
  Permutation (ablocks B ly' S') ((a - cf_head, K + cf_head) :: rest) ->
  (forall b, In b Di -> In (fst b - cf_head, snd b + cf_head) rest) ->
  pis_apart_n Di a L0.
Proof.
intros a K L0 rest HK HL0 HLK HP Hr b x Hb Hx Hrng.
pose proof (@cf_head_nonneg cp) as Hh. pose proof (pil_s_dik b Hb) as Hbk.
pose proof (pil_blk_new_apart ly' S' Hp' W' mem' md' _ rest HAR HP _ (Hr b Hb)) as Hd.
assert (R1 : K + cf_head <= req_size (K + cf_head)) by (apply pil_req_ge; lia).
assert (R2 : snd b + cf_head <= req_size (snd b + cf_head)) by (apply pil_req_ge; lia).
unfold zdisjoint, pj_holdsR in *. cbn [fst snd] in *. lia.
Qed.

(* THE GRANTED KIDS REALLOC (arm 4, and the first half of arms 5 / 6): the prefix extended by grow's kids event, its
   ledger move over its own trace (the batch kit: granted, so g_ran_out kept and refusal peak 0); Drest is the rest of the slot
   blocks (an object's keys block, nothing for an array) *)
Lemma pil_led_kids : forall f' k' Lam' Lam0 Drest, f = S f' -> (cap <= n)%nat -> cntc <> failc ->
  Permutation Lamc (kids_blkR kids (Z.of_nat cap) ++ Lam0) ->
  Permutation Lam' ((k', 56 * cap2R (Z.of_nat cap)) :: Lam0) ->
  Permutation (pi_sblk o kids keys cap) (kids_blkR kids (Z.of_nat cap) ++ Drest) ->
  pi_led Lam peak cnt fail ran most (ok0 ++ [true]) (tr0 ++ [EGrow (56 * cap) (56 * pil_c2 cap)])
    ((k', 56 * cap2R (Z.of_nat cap)) :: Drest ++ Di) Lam' (Z.max peakc (Ledger.lsum Lam')) (cntc + 1) failc ranc.
Proof.
intros f' k' Lam' Lam0 Drest Ef Hge Hcf HL1 HL2' Hsb.
pose proof (pil_c2_gt cap) as Hc2g. pose proof (pil_cap2R cap) as Hc2.
change (if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat) with (pil_c2 cap) in Hc2.
destruct (pil_s_cnt f' Ef) as (Hcc & Hno).
pose proof (pil_s_lam0 _ _ _ HL1 Hsb) as HL0.
assert (HPERM' : Permutation D0 ((kids_blkR kids (Z.of_nat cap) ++ Drest) ++ Di))
  by (apply (Permutation_trans HPERM); apply Permutation_app_tail; exact Hsb).
pose proof pil_s_pk as HPK'.
destruct HLED as (Ho0 & Hc & Hfa & HPL & HPS & HLEN & HPK).
assert (HcG : PjGrammar.calls (tr0 ++ [EGrow (56 * cap) (56 * pil_c2 cap)]) = (PjGrammar.calls tr0 + 1)%nat)
  by (rewrite calls_app; reflexivity).
pose proof (pil_fail_at cnt fail _ cntc failc 0 Hfa Hcc ltac:(lia) ltac:(unfold SIZE_MAXZ; lia)) as E.
rewrite !Z.add_0_r in E.
assert (Hfn : fail <> cnt + Z.of_nat (PjGrammar.calls tr0)) by (intros Hf; apply Hcf; apply (proj2 E); exact Hf).
unfold pi_led. rewrite pil_s_grant, pil_s_ran. change [true] with (repeat true 1). rewrite pil_rep_app, <- HcG.
apply pil_move_granted.
- reflexivity.
- intros i Hi. rewrite HcG in Hi. destruct (Nat.lt_ge_cases i (PjGrammar.calls tr0)) as [Hi'|Hi'];
    [exact (pil_s_oks i Hi')|]. replace i with (PjGrammar.calls tr0) by lia. intros Hf. apply Hfn. lia.
- rewrite HcG. apply (pil_cnt_mod cnt (PjGrammar.calls tr0) 1 cntc Hc); lia.
- rewrite HcG. apply (pil_fa_none cnt fail (PjGrammar.calls tr0) 1 failc Hfa). lia.
- apply (Permutation_trans HL2'). cbn [app]. apply perm_skip. rewrite <- app_assoc. exact HL0.
- rewrite pil_lsz_app. cbn [fold_left map snd]. rewrite Hc2.
  replace (56 * Z.of_nat (pil_c2 cap)) with (Z.of_nat (56 * pil_c2 cap)) by lia.
  apply (pil_lsz_grow _ (kids_blkR kids (Z.of_nat cap)) (Drest ++ Di) (56 * cap) (56 * pil_c2 cap));
    [| exact (pil_kcase kids cap)].
  rewrite app_assoc. exact (Permutation_trans (Permutation_map snd (Permutation_sym HPERM')) HPS).
- rewrite pvm_nlive_app, <- HLEN, (Permutation_length HPERM'), !length_app. cbn [length nliveR].
  destruct (Nat.eq_dec cap 0) as [E3|E3].
  + rewrite pil_kblk. rewrite E3. cbn. rewrite ?length_app. lia.
  + rewrite pil_kblk. destruct (Nat.eqb_spec cap 0); [lia|].
    replace (56 * cap)%nat with (S (56 * cap - 1)) by lia. cbn. rewrite ?length_app. lia.
- rewrite HPK', hpeak_app. cbn [hpeakR PjGrammar.held_ev].
  assert (HlsL : Ledger.lsum Lam' = Ledger.lsum Lamc + 56 * cap2R (Z.of_nat cap) - Ledger.lsum (kids_blkR kids (Z.of_nat cap)))
    by (rewrite (pil_lsum_perm _ _ HL2'), (pil_lsum_perm _ _ HL1), pvm_lsum_app; cbn [Ledger.lsum]; lia).
  assert (HlsC : Ledger.lsum Lamc = Ledger.lsum D0 + Ledger.lsum Lam)
    by (rewrite (pil_lsum_perm _ _ HPL); apply pvm_lsum_app).
  rewrite HlsL, HlsC, HLS, Hc2, pil_kblk. pose proof (pil_held_hpeak tr0).
  destruct (Nat.eqb_spec cap 0) as [E3|E3]; [subst cap; cbn [Ledger.lsum]; lia | cbn [Ledger.lsum]; lia].
Qed.

(* ---- arm 4: an array, the kids moved ---- *)
Lemma pil_arm_arr : forall k' Lam',
  Z.of_nat n = Z.of_nat cap -> cntc <> failc -> (if o then 6 else 5) <> 6 -> getr regs' 10 = w64 0 ->
  4096 + cf_head <= k' -> k' mod 16 = 0 ->
  prhReader_swap B lyc Sc Hpc Lamc ly' S' Hp' Lam' (kids_blkR kids (Z.of_nat cap)) [(k', 56 * cap2R (Z.of_nat cap))] ->
  prh_ledger B ly' S' Hp' W' mem' Lam' (Z.max peakc (Ledger.lsum Lam')) (cntc + 1) failc ranc most own ->
  Ledger.lsum Lam' = Ledger.lsum Lamc + PjGrammar.held (PRH_Charge.prhPg_gtrace ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap)) ->
  bytes_at W' mem' k' kb ->
  pj_hdrR segs m' v (if o then 6 else 5) 0 0 k' keys (Z.of_nat n) (cap2R (Z.of_nat cap)) ->
  pj_slots_atR (prh_lin Lam') (if o then 6 else 5) k' keys (Z.of_nat n) (cap2R (Z.of_nat cap)) ->
  room_live_cf S' ->
  blocks_bytes S' <= blocks_bytes Sc +
    prh_held (PRH_Charge.prhPg_gtrace ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap)) ->
  GPERM [true] -> GPOS [true] -> GHULL ->
  OUT.
Proof.
intros k' Lam' Hneq Hcf Hty H10 Hk1 Hk2 Hsw HL' Hls Hkb' Hh' Hsl' HRL HBB' HPm HIm HHU.
assert (Ho : o = false) by (destruct o; [exfalso; apply Hty; reflexivity | reflexivity]).
assert (Hn : n = cap) by lia. assert (Hge : (cap <= n)%nat) by lia.
pose proof (pil_c2_gt cap) as Hc2g. pose proof (pil_cap2R cap) as Hc2.
change (if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat) with (pil_c2 cap) in Hc2.
pose proof (@cf_head_nonneg cp) as Hh. pose proof (@alloc_ceiling_lt rc) as Hac.
rewrite pil_ty6, Ho, pil_gtrace_ge in Hls, HBB' by exact Hge.
change (EGrow (56 * cap) (56 * pil_c2 cap) :: (if false then [EGrow (8 * cap) (8 * pil_c2 cap)] else []))
  with [EGrow (56 * cap) (56 * pil_c2 cap)] in Hls, HBB'.
destruct pil_s_fuel as [f' Ef].
destruct (pil_s_trav [true] [EGrow (56 * cap) (56 * pil_c2 cap)]
  ltac:(rewrite Ho, (pil_grow_arr_ok n cap [] Hge); reflexivity)
  ltac:(rewrite Ho, (pil_grow_ge false n cap [] Hge); reflexivity) HPm HIm HHU) as (HPB' & HLV').
destruct (pil_s_cnt f' Ef) as (Hcc & Hno). rewrite Ho, pil_gtrace_ge in Hno by exact Hge.
cbn [PjGrammar.calls PjGrammar.is_call] in Hno.
destruct (HBYT Hn) as (Hkb & Hlkb & _).
destruct Hsw as ((bl & HA1 & HA2) & _ & (Lam0 & HL1 & HL2)).
assert (Hsb : Permutation (pi_sblk o kids keys cap) (kids_blkR kids (Z.of_nat cap) ++ []))
  by (rewrite Ho, pil_sblk_false, app_nil_r; reflexivity).
assert (HPERM' : Permutation D0 (kids_blkR kids (Z.of_nat cap) ++ Di))
  by (rewrite <- (pil_sblk_false kids keys cap), <- Ho; exact HPERM).
pose proof (pil_s_lam0 _ _ _ HL1 Hsb) as HL0. cbn [app] in HL0.
pose proof (pil_s_bl _ _ _ HA1 Hsb) as Hbl.
assert (Hbl' : Permutation bl (prhReader_ab Di ++ ablocks B ly Se)) by exact Hbl.
assert (HL2' : Permutation Lam' ((k', 56 * cap2R (Z.of_nat cap)) :: Lam0)) by exact HL2.
assert (Hkin' : In (k', 56 * cap2R (Z.of_nat cap)) Lam')
  by (apply (Permutation_in _ (Permutation_sym HL2')); left; reflexivity).
destruct (pil_lam_bound ly' S' Hp' W' mem' md' _ _ _ _ _ _ _ _ _ HAR HL' Hkin') as (Hk0 & Hk4 & Hkc & _).
assert (HAB' : Permutation (ablocks B ly' S') ((k' - cf_head, 56 * cap2R (Z.of_nat cap) + cf_head) :: bl))
  by exact HA2.
assert (Hfr : ~ In (k' - cf_head, 56 * cap2R (Z.of_nat cap) + cf_head) bl).
{ apply (pil_blk_new_fresh ly' S' Hp' W' mem' md' _ bl HAR HAB'). apply pil_req_pos. cbn [snd]. lia. }
assert (Hnold : ~ In (k' - cf_head, 56 * cap2R (Z.of_nat cap) + cf_head) (ablocks B lyc Sc)).
{ intros Hin. apply (Permutation_in _ HA1) in Hin. apply in_app_or in Hin as [Hin | Hin]; [| exact (Hfr Hin)].
  rewrite pil_kblk in Hin. destruct (Nat.eqb cap 0); cbn in Hin; [exact Hin|].
  destruct Hin as [Heq | []]. injection Heq as _ Heq. lia. }
assert (Hnv : pj_apartR [(k', 56 * cap2R (Z.of_nat cap))] v).
{ apply pil_s_newv; [apply (Permutation_in _ (Permutation_sym HAB')); left; reflexivity | exact Hnold]. }
assert (Hdi : forall b, In b Di -> In (fst b - cf_head, snd b + cf_head) bl).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym Hbl')). apply in_or_app. left.
  exact (in_map (fun ak => (fst ak - cf_head, snd ak + cf_head)) Di b Hb). }
assert (HO : pis_open segs mc (prh_lin Lamc) v false 0 kids keys (Z.of_nat cap) (Z.of_nat (length (map snd acc)))
  (map snd acc) (map fst acc) Di) by (rewrite <- Ho; exact pil_s_open).
assert (HO' : pis_open segs m' (prh_lin Lam') v false 0 k' keys (cap2R (Z.of_nat cap)) (Z.of_nat (length (map snd acc)))
  (map snd acc) (map fst acc) Di).
{ apply (pis_grow_arr segs mc m' Lamc Lam' Lam0 v 0 kids keys (Z.of_nat cap) _ (map snd acc) (map fst acc) Di k'
    HO HL1 HL2').
  - pose proof HL' as HN'. apply prh_ledger_nodup in HN'.
    first [exact HN' | apply NoDup_ListNoDup; exact HN' | apply NoDup_ListNoDup in HN'; exact HN'].
  - rewrite <- Hlkb. exact (pil_garr8_moved _ _ _ _ _ Hkb Hkb').
  - rewrite pil_s_lenmap. rewrite Ho in Hh'. exact Hh'.
  - rewrite pil_s_lenmap. rewrite Ho in Hsl'. exact Hsl'.
  - rewrite pil_s_lenmap. lia.
  - lia.
  - lia.
  - rewrite pil_s_lenmap. lia.
  - intros i Hi. rewrite pil_s_lenmap in Hi.
    apply (pil_lam_wr ly' S' Hp' W' mem' md' Lam' _ _ _ _ _ _ k' (56 * cap2R (Z.of_nat cap)) (k' + i) HAR HL' Hkin'). lia.
  - exact HKDI.
  - rewrite pil_s_lenmap. apply (pil_s_apart_n k' (56 * cap2R (Z.of_nat cap)) _ bl); [lia | lia | lia | exact HAB' | exact Hdi].
  - exact Hnv. }
assert (HC' : pi_cont m' (prh_lin Lam') o v k' keys n (pil_c2 cap) acc Di).
{ rewrite Ho. apply pil_cont_of_open; [| exact pil_s_len | lia |].
  - rewrite <- Hc2. rewrite <- pil_s_lenmap at 1. exact HO'.
  - destruct Hsl' as (_ & (_ & H54) & _). lia. }
left. split; [exact H10|]. split; [exact pil_s_mn|].
exists f', (pil_c2 cap), k', keys, (ok0 ++ [true]), (tr0 ++ [EGrow (56 * cap) (56 * pil_c2 cap)]),
  (pi_sblk o k' keys (pil_c2 cap) ++ Di), Lam', (Z.max peakc (Ledger.lsum Lam')), (cntc + 1), failc, ranc.
split; [exact Ef|].
split.
{ apply HKCUR; [exact HL' | | | lia].
  - intros a k Ha Hns. apply (Permutation_in _ HL1) in Ha.
    apply in_app_or in Ha as [Ha | Ha].
    + exfalso. apply Hns. rewrite Ho, pil_sblk_false. exact Ha.
    + apply (Permutation_in _ (Permutation_sym HL2')). right. exact Ha.
  - intros a k Ha. apply (Permutation_in _ HL2') in Ha. destruct Ha as [Heq | Ha].
    + right. injection Heq as Eqa Eqk. subst a k. exact Hnold.
    + left. apply (Permutation_in _ (Permutation_sym HL1)). apply in_or_app. right. exact Ha. }
split; [lia|]. split; [exact HC'|]. split; [exact HDEP|].
split.
{ rewrite Ho, pil_sblk_false, pil_kblk. destruct (Nat.eqb_spec (pil_c2 cap) 0) as [E0|E0]; [lia|].
  rewrite <- Hc2. exact Hnv. }
split; [apply Permutation_refl|]. split; [lia|].
split.
{ apply (pil_runB d o _ ok0 tr0 f' n cap acc _ [true] [EGrow (56 * cap) (56 * pil_c2 cap)] (pil_c2 cap) (pil_s_run f' Ef)).
  intros ok1. rewrite Ho. apply pil_grow_arr_ok. exact Hge. }
assert (ED : pi_sblk o k' keys (pil_c2 cap) ++ Di = (k', 56 * cap2R (Z.of_nat cap)) :: [] ++ Di).
{ rewrite Ho, pil_sblk_false, pil_kblk. destruct (Nat.eqb_spec (pil_c2 cap) 0) as [E0|E0]; [lia|].
  rewrite <- Hc2. reflexivity. }
split; [rewrite ED; exact (pil_led_kids f' k' Lam' Lam0 [] Ef Hge Hcf HL1 HL2' Hsb)|].
split.
{ split; [|split; [|split]].
  - intros a k Hin. rewrite Ho, pil_sblk_false, pil_kblk in Hin.
    destruct (Nat.eqb_spec (pil_c2 cap) 0) as [E0|E0]; [lia|].
    destruct Hin as [Heq | Hin].
    + injection Heq as Ha Hk. subst a k. intros Hold. apply Hfr. apply (Permutation_in _ (Permutation_sym Hbl')).
      apply in_or_app. right. rewrite Hc2. exact Hold.
    + destruct HBLK as (B1 & _). apply B1. apply (Permutation_in _ (Permutation_sym HPERM')). apply in_or_app. right.
      exact Hin.
  - apply (Permutation_trans HAB'). rewrite Ho, pil_sblk_false, pil_kblk.
    destruct (Nat.eqb_spec (pil_c2 cap) 0) as [E0|E0]; [lia|].
    rewrite <- Hc2. cbn [app prhReader_ab map fst snd]. apply perm_skip. exact Hbl'.
  - destruct HBLK as (_ & _ & B3 & _). exact (Permutation_trans HFR B3).
  - pose proof (pil_hpeak_granted d o _ ok0 tr0 f' n cap acc _ HX0 (pil_s_run f' Ef)) as HP.
    rewrite Ho, pil_gtrace_ge in HP by exact Hge. exact HP. }
split; [exact HPB'|]. split; [exact HLV'|].
split; [rewrite pvm_prh_held_app; lia|].
split; [rewrite length_app, calls_app, HOK; reflexivity|].
split.
{ rewrite held_app, <- HLS, (pil_lsum_perm _ _ HPERM'), !pvm_lsum_app. rewrite Ho, pil_sblk_false, !pil_kblk.
  destruct (Nat.eqb_spec (pil_c2 cap) 0); [lia|]. cbn [PjGrammar.held held_ev Ledger.lsum].
  destruct (Nat.eqb_spec cap 0) as [E1|E1]; cbn [Ledger.lsum]; lia. }
split.
{ pose proof (pil_gt_split f' (Nat.succ d) o n cap (rev acc) y) as HS. rewrite pil_gcap_ge in HS by exact Hge.
  assert (HR' : rd_room Sc (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap) ++
    snd (fst (pi_jrb f' (Nat.succ d) o n (pil_c2 cap) (rev acc) y [])))) by (rewrite <- HS; exact (pil_s_room f' Ef)).
  rewrite Ho, pil_gtrace_ge in HR' by exact Hge. rewrite Ho.
  change ((EGrow (56 * cap) (56 * pil_c2 cap) :: (if false then [EGrow (8 * cap) (8 * pil_c2 cap)] else [])) ++
    snd (fst (pi_jrb f' (Nat.succ d) false n (pil_c2 cap) (rev acc) y [])))
    with ([EGrow (56 * cap) (56 * pil_c2 cap)] ++ snd (fst (pi_jrb f' (Nat.succ d) false n (pil_c2 cap) (rev acc) y [])))
    in HR'.
  apply (pvm_room_after Sc S' _ _ HR' HRL).
  rewrite pil_evs_model, Ho, (pil_grow_arr_ok n cap [] Hge) in HPm. cbn [fst snd] in HPm. exact HPm. }
(* The batch kit's tail: the granted kids realloc appends one grant; cap' = gcap n cap = ncap (S n); the slots moved to k' *)
assert (Hmv : pis_moved segs mc m' kids k' (56 * Z.of_nat n))
  by (rewrite Hn, <- Hlkb; exact (pil_garr8_moved _ _ _ _ _ Hkb Hkb')).
split; [unfold pi_grant; rewrite pil_s_grant, calls_app; cbn [PjGrammar.calls PjGrammar.is_call];
  rewrite <- pil_rep_app; reflexivity|].
split; [rewrite pil_s_ncap, (pil_gcap_ge n cap Hge); reflexivity|].
split; [exact (pil_s_ncaps_mv k' Hmv)|].
exists af. split.
- apply (pil_s_fo_mv k' keys Lam').
  + intros x k Hin. unfold prh_lin. apply (Permutation_in _ (Permutation_sym HL2')). right.
    apply (Permutation_in _ (Permutation_sym HL0)). apply in_or_app. left. exact Hin.
  + exact Hmv.
  + intros i Hi _. rewrite Hn in Hi.
    apply (pil_lam_wr ly' S' Hp' W' mem' md' Lam' _ _ _ _ _ _ k' (56 * cap2R (Z.of_nat cap)) (k' + i) HAR HL' Hkin'). lia.
  + intros _. lia.
  + right. apply (pil_s_apart_n k' (56 * cap2R (Z.of_nat cap)) _ bl); [lia | lia | lia | exact HAB' | exact Hdi].
  + intros Ho'. rewrite Ho in Ho'. discriminate Ho'.
- apply (pil_flB d o _ ok0 f' n cap af _ [true] [EGrow (56 * cap) (56 * pil_c2 cap)] (pil_c2 cap) (pil_s_fl f' Ef)).
  intros ok1. rewrite Ho. apply pil_grow_arr_ok. exact Hge.
Qed.


(* ---- arms 5 and 6: an object, the kids moved, the keys realloc fails ---- *)
Lemma pil_arm_khalf : forall k' Lam' peak2 cnt2 fail2 ran2,
  Z.of_nat n = Z.of_nat cap -> cntc <> failc -> (if o then 6 else 5) = 6 -> getr regs' 10 = w64 (-1) ->
  4096 + cf_head <= k' -> k' mod 16 = 0 ->
  prhReader_swap B lyc Sc Hpc Lamc ly' S' Hp' Lam' (kids_blkR kids (Z.of_nat cap)) [(k', 56 * cap2R (Z.of_nat cap))] ->
  prh_ledger B ly' S' Hp' W' mem' Lam' peak2 cnt2 fail2 ran2 most own ->
  bytes_at W' mem' k' kb -> bytes_at W' mem' keys yb ->
  pj_hdrR segs m' v (if o then 6 else 5) 0 0 k' keys (Z.of_nat n) (Z.of_nat cap) ->
  room_live_cf S' ->
  ((cntc + 1 = failc /\ peak2 = Z.max peakc (Ledger.lsum Lam') /\ cnt2 = cntc + 2 /\ fail2 = SIZE_MAXZ /\ ran2 = ranc) \/
   (cntc + 1 <> failc /\
    peak2 = (if Z.of_nat cap =? 0
             then Z.max (Z.max peakc (Ledger.lsum Lam')) (Z.min SIZE_MAXZ (Ledger.lsum Lam' + 8 * cap2R (Z.of_nat cap)))
             else Z.max (Z.max peakc (Ledger.lsum Lam'))
                    (Z.min SIZE_MAXZ (Ledger.lsum Lam' - 8 * Z.of_nat cap + 8 * cap2R (Z.of_nat cap)))) /\
    cnt2 = (cntc + 1 + 1) mod 2 ^ 64 /\ fail2 = failc /\
    ran2 = (if 8 * cap2R (Z.of_nat cap) <=? most then 1 else ranc) /\ GEXCL)) ->
  GPERM [true; false] -> GPOS [true; false] -> GHULL ->
  OUT.
Proof.
intros k' Lam' peak2 cnt2 fail2 ran2 Hneq Hcf Hty H10 Hk1 Hk2 Hsw HL' Hkb' Hyb' Hh' HRL Hcase HPm HIm HHU.
assert (Ho : o = true) by (destruct o; [reflexivity | exfalso; cbn in Hty; lia]).
assert (Hn : n = cap) by lia. assert (Hge : (cap <= n)%nat) by lia.
pose proof (pil_c2_gt cap) as Hc2g. pose proof (pil_cap2R cap) as Hc2.
change (if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat) with (pil_c2 cap) in Hc2.
pose proof (@cf_head_nonneg cp) as Hh. pose proof (@alloc_ceiling_lt rc) as Hac.
destruct pil_s_fuel as [f' Ef].
destruct (pil_s_cnt f' Ef) as (Hcc & Hno). rewrite Ho, pil_gtrace_ge in Hno by exact Hge.
cbn [PjGrammar.calls PjGrammar.is_call] in Hno.
destruct (HBYT Hn) as (Hkb & Hlkb & Hyb0). destruct (Hyb0 Ho) as (Hyb & Hlyb).
destruct Hsw as ((bl & HA1 & HA2) & _ & (Lam0 & HL1 & HL2)).
assert (Hsb : Permutation (pi_sblk o kids keys cap) (kids_blkR kids (Z.of_nat cap) ++ keys_blkR 6 keys (Z.of_nat cap)))
  by (rewrite Ho; reflexivity).
assert (HPERM' : Permutation D0 ((kids_blkR kids (Z.of_nat cap) ++ keys_blkR 6 keys (Z.of_nat cap)) ++ Di))
  by (rewrite <- (pil_sblk_true kids keys cap), <- Ho; exact HPERM).
pose proof (pil_s_lam0 _ _ _ HL1 Hsb) as HL0.
pose proof (pil_s_bl _ _ _ HA1 Hsb) as Hbl.
assert (HL2' : Permutation Lam' ((k', 56 * cap2R (Z.of_nat cap)) :: Lam0)) by exact HL2.
assert (Hkin' : In (k', 56 * cap2R (Z.of_nat cap)) Lam')
  by (apply (Permutation_in _ (Permutation_sym HL2')); left; reflexivity).
destruct (pil_lam_bound ly' S' Hp' W' mem' md' _ _ _ _ _ _ _ _ _ HAR HL' Hkin') as (Hk0 & Hk4 & Hkc & _).
assert (HAB' : Permutation (ablocks B ly' S') ((k' - cf_head, 56 * cap2R (Z.of_nat cap) + cf_head) :: bl))
  by exact HA2.
assert (Hfr : ~ In (k' - cf_head, 56 * cap2R (Z.of_nat cap) + cf_head) bl).
{ apply (pil_blk_new_fresh ly' S' Hp' W' mem' md' _ bl HAR HAB'). apply pil_req_pos. cbn [snd]. lia. }
assert (Hnold : ~ In (k' - cf_head, 56 * cap2R (Z.of_nat cap) + cf_head) (ablocks B lyc Sc)).
{ intros Hin. apply (Permutation_in _ HA1) in Hin. apply in_app_or in Hin as [Hin | Hin]; [| exact (Hfr Hin)].
  rewrite pil_kblk in Hin. destruct (Nat.eqb cap 0); cbn in Hin; [exact Hin|].
  destruct Hin as [Heq | []]. injection Heq as _ Heq. lia. }
assert (Hnv : pj_apartR [(k', 56 * cap2R (Z.of_nat cap))] v).
{ apply pil_s_newv; [apply (Permutation_in _ (Permutation_sym HAB')); left; reflexivity | exact Hnold]. }
assert (Hdi : forall b, In b Di -> In (fst b - cf_head, snd b + cf_head) bl).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym Hbl)). apply in_or_app. right. apply in_or_app. left.
  exact (in_map (fun ak => (fst ak - cf_head, snd ak + cf_head)) Di b Hb). }
assert (HlsL : Ledger.lsum Lam' = Ledger.lsum Lamc + (56 * cap2R (Z.of_nat cap) - Ledger.lsum (kids_blkR kids (Z.of_nat cap)))).
{ rewrite (pil_lsum_perm _ _ HL2'), (pil_lsum_perm _ _ HL1), pvm_lsum_app. cbn [Ledger.lsum]. lia. }
assert (Hc2' : cnt2 = cntc + 2).
{ destruct Hcase as [(_ & _ & -> & _) | (_ & _ & -> & _)]; [reflexivity | rewrite Z.mod_small; lia]. }
assert (HC'' : pi_cur B regs0 e q v text len tb d ly' S' Hp' W' mem' pc Lam' peak2 cnt2 fail2 ran2 most own).
{ apply HKCUR; [exact HL' | | | lia].
  - intros a k Ha Hns. apply (Permutation_in _ HL1) in Ha.
    apply in_app_or in Ha as [Ha | Ha].
    + exfalso. apply Hns. rewrite Ho. apply in_or_app. left. exact Ha.
    + apply (Permutation_in _ (Permutation_sym HL2')). right. exact Ha.
  - intros a k Ha. apply (Permutation_in _ HL2') in Ha. destruct Ha as [Heq | Ha].
    + right. injection Heq as Eqa Eqk. subst a k. exact Hnold.
    + left. apply (Permutation_in _ (Permutation_sym HL1)). apply in_or_app. right. exact Ha. }
set (G := [EGrow (56 * cap) (56 * pil_c2 cap); EFail (8 * pil_c2 cap)]).
assert (HGR : PjGrammar.grow o n cap [true; false] = (None, G, [])) by (rewrite Ho; apply pil_grow_obj_no2; exact Hge).
assert (HGg : snd (fst (PjGrammar.grow o n cap [true; false])) = G) by (rewrite HGR; reflexivity).
assert (Hh1 : hpeakR (tr0 ++ G) =
  Z.max (hpeakR tr0) (PjGrammar.held tr0 + (Z.of_nat (56 * pil_c2 cap) - Z.of_nat (56 * cap))))
  by (subst G; rewrite hpeak_app; cbn [hpeakR held_ev]; lia).
(* the ledger: the granted kids realloc (pil_led_kids), then the keys realloc's own move (pil_mv_fail1) *)
assert (HW1 : pvm_wf (tr0 ++ [EGrow (56 * cap) (56 * pil_c2 cap)])).
{ pose proof pil_s_wfg as W. rewrite (pil_s_gt f' Ef), (pil_gtrace_ge o n cap Hge), Ho in W. cbn [app] in W.
  change (tr0 ++ EGrow (56 * cap) (56 * pil_c2 cap) :: EGrow (8 * cap) (8 * pil_c2 cap) ::
    snd (fst (pi_jrb f' (Nat.succ d) true n (pil_gcap n cap) (rev acc) y [])))
    with (tr0 ++ [EGrow (56 * cap) (56 * pil_c2 cap)] ++ EGrow (8 * cap) (8 * pil_c2 cap) ::
    snd (fst (pi_jrb f' (Nat.succ d) true n (pil_gcap n cap) (rev acc) y []))) in W.
  rewrite app_assoc in W. unfold pvm_wf in W. apply pvm_wf_from_app in W. exact (proj1 W). }
assert (HLb : 0 <= Ledger.lsum Lam') by (pose proof HL' as HB; apply prh_ledger_bounds in HB; lia).
assert (HMV : rd_ledger_move Lam' (Z.max peakc (Ledger.lsum Lam')) (cntc + 1) failc ranc most [false]
  [EGrow (8 * cap) (8 * pil_c2 cap)] [EFail (8 * pil_c2 cap)] [] Lam' peak2 cnt2 fail2 ran2).
{ apply pil_mv_fail1; [lia | lia | lia |].
  destruct Hcase as [(Hcf1 & -> & -> & -> & ->) | (Hcf1 & -> & -> & -> & -> & _)];
    [left; repeat split; first [exact Hcf1 | reflexivity | lia] | right].
  split; [exact Hcf1|]. split; [rewrite Hc2; destruct (Z.eqb_spec (Z.of_nat cap) 0); lia|].
  split; [reflexivity|]. split; [reflexivity|]. rewrite Hc2.
  replace (8 * Z.of_nat (pil_c2 cap)) with (Z.of_nat (8 * pil_c2 cap)) by lia. reflexivity. }
assert (HLM : rd_ledger_move Lam peak cnt fail ran most (ok0 ++ [true; false]) (PRH_Charge.prhPi_gtrace d o x0)
  (tr0 ++ G) ((k', 56 * cap2R (Z.of_nat cap)) :: keys_blkR 6 keys (Z.of_nat cap) ++ Di) Lam' peak2 cnt2 fail2 ran2).
{ pose proof (pvm_ledger_app Lam peak cnt fail ran most (ok0 ++ [true]) (tr0 ++ [EGrow (56 * cap) (56 * pil_c2 cap)])
    ((k', 56 * cap2R (Z.of_nat cap)) :: keys_blkR 6 keys (Z.of_nat cap) ++ Di) Lam' (Z.max peakc (Ledger.lsum Lam'))
    (cntc + 1) failc ranc [false] [EGrow (8 * cap) (8 * pil_c2 cap)] [EFail (8 * pil_c2 cap)] [] Lam' peak2 cnt2 fail2
    ran2 (snd (fst (pi_jrb f' (Nat.succ d) true n (pil_gcap n cap) (rev acc) y [])))
    HW1 I ltac:(rewrite length_app, calls_app, HOK; reflexivity) (proj1 (proj1 HCNT0))
    ltac:(rewrite calls_app; cbn [PjGrammar.calls PjGrammar.is_call]; unfold SIZE_MAXZ; lia) (pil_s_fail_bnd f' Ef)
    ltac:(rewrite pil_s_grant; change [true] with (repeat true 1); rewrite pil_rep_app;
          apply PItems_ledk1.pik1_grant_granted)
    ltac:(cbn; lia) (pil_led_kids f' k' Lam' Lam0 (keys_blkR 6 keys (Z.of_nat cap)) Ef Hge Hcf HL1 HL2' Hsb) HMV) as X.
  rewrite <- !app_assoc in X. cbn [app] in X.
  rewrite (pil_s_gt f' Ef), (pil_gtrace_ge o n cap Hge), Ho. cbn [app]. subst G. exact X. }
right. split; [exact H10|]. split; [exact pil_s_mn|]. intros regs'' md'' H10''.
(* the text's post, built through its record (PRH_FnParse.tpiP_R) *)
refine (tpiP_Q_of_R (ok := ok0 ++ [true; false]) (res := None) (tr := tr0 ++ G) (okr := [])
  (D := (k', 56 * cap2R (Z.of_nat cap)) :: keys_blkR 6 keys (Z.of_nat cap) ++ Di) (Lam' := Lam')
  (peak' := peak2) (cnt' := cnt2) (fail' := fail2) (ran' := ran2) md''
  {| tpiP_run := pil_run_refused d o _ ok0 tr0 f' n cap acc _ [true; false] G (pil_s_run f' Ef) HGR;
     tpiP_ledger := HL'; tpiP_room := HRL; tpiP_hull := pil_s_hullx HHU f' Ef;
     tpiP_live := pil_s_live [true; false] G HGg HPm; tpiP_pos := pil_s_pos [true; false] G HGg HIm;
     tpiP_outcome := _; tpiP_injected := _; tpiP_ledger_move := HLM; tpiP_blocks_move := _; tpiP_bytes := _;
     tpiP_lsum := _; tpiP_arm := _ |}).
- (* THE OUTCOME: the keys realloc's chosen failure is grow's second granted call (the window), a refusal is grow's
     exclusion *)
  intros sm x os i H0 hist HP HR HC HW'. exfalso.
  destruct Hcase as [(Hcf1 & _) | (Hcf1 & _ & _ & _ & _ & HX)].
  + apply (pil_s_wexcl f' 1 Ef ltac:(lia) ltac:(rewrite (pil_gtrace_ge o n cap Hge), Ho; cbn; lia) HW').
  + exact (pil_s_excl f' Ef HX sm x os i H0 hist HP HR HC).
- (* THE INJECTED READING: the chosen failure is the refused keys call; a refusal: its window guards close grow's
     window (cntc <> failc, cntc + 1 <> failc), past it grow's OUTCOME exclusion *)
  intros sm x os i H0 hist HP HR HC HW'.
  destruct Hcase as [(Hcf1 & _) | (Hcf1 & _ & _ & _ & _ & HX)].
  + exact (pil_s_chosen f' 1 _ Ef ltac:(lia) ltac:(rewrite (pil_gtrace_ge o n cap Hge), Ho; cbn; lia)).
  + assert (HJ : GINJ).
    { intros sm' x' os' i' H0' hist' _ _ _ HWg.
      rewrite pil_ty6, Ho, (pil_gtrace_ge true n cap Hge) in HWg. cbn in HWg. lia. }
    exfalso. exact (pil_s_injx f' Ef Hge HX HJ sm x os i H0 hist HP HR HC HW').
- destruct HLED as (Ho0 & Hc & Hfa & HPL & HPS & HLEN & HPK).
  split; [|split; [|split]].
  + intros a k Hin. destruct Hin as [Heq | Hin].
    * injection Heq as Ha Hk. subst a k. intros Hold. apply Hfr. apply (Permutation_in _ (Permutation_sym Hbl)).
      apply in_or_app. right. apply in_or_app. right. exact Hold.
    * destruct HBLK as (B1 & _). apply B1. apply (Permutation_in _ (Permutation_sym HPERM')).
      rewrite <- app_assoc. apply in_or_app. right. exact Hin.
  + apply (Permutation_trans HAB'). unfold prhReader_ab in Hbl |- *. cbn [map fst snd app]. apply perm_skip.
    rewrite map_app, <- app_assoc. exact Hbl.
  + destruct HBLK as (_ & _ & B3 & _). exact (Permutation_trans HFR B3).
  + pose proof (pil_hpeak_granted d o _ ok0 tr0 f' n cap acc _ HX0 (pil_s_run f' Ef)) as HP.
    rewrite Ho, pil_gtrace_ge in HP by exact Hge. rewrite hpeak_app in HP. cbn [hpeakR held_ev] in HP.
    rewrite Hh1. lia.
- rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HAB'), pvm_prh_held_app.
  change (bsum ((k' - cf_head, 56 * cap2R (Z.of_nat cap) + cf_head) :: bl))
    with ((56 * cap2R (Z.of_nat cap) + cf_head) + bsum bl).
  pose proof (bsum_perm _ _ HA1) as Hb1. rewrite <- (blocks_bytes_bsum B lyc Sc), bsum_app in Hb1.
  assert (HbK : bsum (prhReader_ab (kids_blkR kids (Z.of_nat cap))) =
    if Nat.eqb cap 0 then 0 else 56 * Z.of_nat cap + cf_head)
    by (rewrite pil_kblk; destruct (Nat.eqb cap 0); cbn; lia).
  rewrite HbK in Hb1. subst G. unfold prh_held at 2.
  cbn [PjGrammar.held held_ev PjGrammar.calls PjGrammar.is_call].
  rewrite Hc2. revert Hb1. destruct (Nat.eqb_spec cap 0) as [E3|E3]; intros Hb1; lia.
- subst G. rewrite held_app, <- HLS, (pil_lsum_perm _ _ HPERM'). cbn [Ledger.lsum PjGrammar.held held_ev].
  rewrite !pvm_lsum_app. rewrite Hc2, pil_kblk. destruct (Nat.eqb_spec cap 0) as [E3|E3]; cbn [Ledger.lsum]; lia.
- split; [exact H10''|].
  (* the partial free order: the completed slots (moved to k'), then the new kids block and the old keys block *)
  split.
  { intros HH. apply (PItems_forder.pi_forder_post d _ pil_s_dlt). intros nn Hnn.
    destruct (HFO HH nn (pil_s_dep nn Hnn)) as (Facc & HI & HM).
    exists (Facc ++ (k', 56 * cap2R (Z.of_nat cap)) :: keys_blkR 6 keys (Z.of_nat cap)). split.
    - rewrite <- pil_s_lenmap in HI. rewrite Ho in HI.
      apply (PItems_forder.pis_fo_grow_half segs mc m' Lamc Lam' Lam0 v 0 kids keys (Z.of_nat cap) (map snd acc)
        (map fst acc) Di k' nn Facc ltac:(rewrite <- Ho; exact pil_s_open) HL1 HL2').
      + pose proof HL' as HN'. apply prh_ledger_nodup in HN'.
        first [exact HN' | apply NoDup_ListNoDup; exact HN' | apply NoDup_ListNoDup in HN'; exact HN'].
      + rewrite <- Hlkb. exact (pil_garr8_moved _ _ _ _ _ Hkb Hkb').
      + rewrite <- Hlyb. exact (pil_garr8_moved _ _ _ _ _ Hyb Hyb').
      + rewrite pil_s_lenmap. rewrite Ho in Hh'. exact Hh'.
      + lia.
      + intros i Hi. rewrite pil_s_lenmap in Hi.
        apply (pil_lam_wr ly' S' Hp' W' mem' md' Lam' _ _ _ _ _ _ k' (56 * cap2R (Z.of_nat cap)) (k' + i) HAR HL' Hkin').
        lia.
      + exact HKDI.
      + rewrite pil_s_lenmap. apply (pil_s_apart_n k' (56 * cap2R (Z.of_nat cap)) _ bl);
          [lia | lia | lia | exact HAB' | exact Hdi].
      + exact Hnv.
      + exact HI.
    - rewrite map_app, HM, (pil_fl_refused d o _ ok0 f' n cap af _ [true; false] G (pil_s_fl f' Ef) HGR). f_equal.
      subst G. rewrite (PItems_forder.pis_fo_half_hb cf_head o keys (Z.of_nat cap) k' (56 * cap) (56 * pil_c2 cap)
        (8 * pil_c2 cap) HH ltac:(lia) ltac:(rewrite Hc2; lia)), Nat2Z.id. reflexivity. }
  split; [exact (pil_s_after _ _ _ _ _ HC'')|].
  apply (pis_exit_grow_half segs mc m' Lamc Lam' Lam0 v 0 kids keys (Z.of_nat cap) (map snd acc) (map fst acc) Di k' d
    ltac:(rewrite <- Ho; exact pil_s_open) pil_s_dlt pil_s_depmap HL1 HL2').
  + pose proof HL' as HN'. apply prh_ledger_nodup in HN'.
    first [exact HN' | apply NoDup_ListNoDup; exact HN' | apply NoDup_ListNoDup in HN'; exact HN'].
  + rewrite <- Hlkb. exact (pil_garr8_moved _ _ _ _ _ Hkb Hkb').
  + rewrite <- Hlyb. exact (pil_garr8_moved _ _ _ _ _ Hyb Hyb').
  + rewrite pil_s_lenmap. rewrite Ho in Hh'. exact Hh'.
  + lia.
  + lia.
  + rewrite pil_s_lenmap. lia.
  + intros i Hi. rewrite pil_s_lenmap in Hi.
    apply (pil_lam_wr ly' S' Hp' W' mem' md' Lam' _ _ _ _ _ _ k' (56 * cap2R (Z.of_nat cap)) (k' + i) HAR HL' Hkin'). lia.
  + exact HKDI.
  + rewrite pil_s_lenmap. apply (pil_s_apart_n k' (56 * cap2R (Z.of_nat cap)) _ bl); [lia | lia | lia | exact HAB' | exact Hdi].
  + exact Hnv.
Qed.

(* ---- arm 7: an object, the kids and the keys moved ---- *)
Lemma pil_arm_obj : forall k' y' Lam',
  Z.of_nat n = Z.of_nat cap -> cntc <> failc -> (if o then 6 else 5) = 6 -> cntc + 1 <> failc -> getr regs' 10 = w64 0 ->
  4096 + cf_head <= k' -> k' mod 16 = 0 -> 4096 + cf_head <= y' -> y' mod 16 = 0 ->
  prhReader_swap B lyc Sc Hpc Lamc ly' S' Hp' Lam'
    (kids_blkR kids (Z.of_nat cap) ++ keys_blkR (if o then 6 else 5) keys (Z.of_nat cap))
    [(y', 8 * cap2R (Z.of_nat cap)); (k', 56 * cap2R (Z.of_nat cap))] ->
  prh_ledger B ly' S' Hp' W' mem' Lam'
    (Z.max peakc (Z.max (Ledger.lsum Lamc + 56 * (cap2R (Z.of_nat cap) - Z.of_nat cap)) (Ledger.lsum Lam')))
    (cntc + 2) failc ranc most own ->
  Ledger.lsum Lam' = Ledger.lsum Lamc + PjGrammar.held (PRH_Charge.prhPg_gtrace ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap)) ->
  bytes_at W' mem' k' kb -> bytes_at W' mem' y' yb ->
  pj_hdrR segs m' v (if o then 6 else 5) 0 0 k' y' (Z.of_nat n) (cap2R (Z.of_nat cap)) ->
  pj_slots_atR (prh_lin Lam') (if o then 6 else 5) k' y' (Z.of_nat n) (cap2R (Z.of_nat cap)) ->
  room_live_cf S' ->
  blocks_bytes S' <= blocks_bytes Sc +
    prh_held (PRH_Charge.prhPg_gtrace ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap)) ->
  GPERM [true; true] -> GPOS [true; true] -> GHULL ->
  OUT.
Proof.
intros k' y' Lam' Hneq Hcf Hty Hcf1 H10 Hk1 Hk2 Hy1 Hy2 Hsw HL' Hls Hkb' Hyb' Hh' Hsl' HRL HBB' HPm HIm HHU.
assert (Ho : o = true) by (destruct o; [reflexivity | exfalso; cbn in Hty; lia]).
assert (Hn : n = cap) by lia. assert (Hge : (cap <= n)%nat) by lia.
pose proof (pil_c2_gt cap) as Hc2g. pose proof (pil_cap2R cap) as Hc2.
change (if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat) with (pil_c2 cap) in Hc2.
assert (Hc2v : (0 < cap)%nat -> pil_c2 cap = (2 * cap)%nat)
  by (intros Hp; unfold pil_c2; destruct (Nat.eqb_spec cap 0); [lia | reflexivity]).
pose proof (@cf_head_nonneg cp) as Hh. pose proof (@alloc_ceiling_lt rc) as Hac.
rewrite pil_ty6, Ho, pil_gtrace_ge in Hls, HBB' by exact Hge.
change (EGrow (56 * cap) (56 * pil_c2 cap) :: (if true then [EGrow (8 * cap) (8 * pil_c2 cap)] else []))
  with [EGrow (56 * cap) (56 * pil_c2 cap); EGrow (8 * cap) (8 * pil_c2 cap)] in Hls, HBB'.
destruct pil_s_fuel as [f' Ef].
destruct (pil_s_trav [true; true] [EGrow (56 * cap) (56 * pil_c2 cap); EGrow (8 * cap) (8 * pil_c2 cap)]
  ltac:(rewrite Ho, (pil_grow_obj_ok n cap [] Hge); reflexivity)
  ltac:(rewrite Ho, (pil_grow_ge true n cap [] Hge); reflexivity) HPm HIm HHU) as (HPB' & HLV').
destruct (pil_s_cnt f' Ef) as (Hcc & Hno). rewrite Ho, pil_gtrace_ge in Hno by exact Hge.
cbn [PjGrammar.calls PjGrammar.is_call] in Hno.
destruct (HBYT Hn) as (Hkb & Hlkb & Hyb0). destruct (Hyb0 Ho) as (Hyb & Hlyb).
destruct Hsw as ((bl & HA1 & HA2) & _ & (Lam0 & HL1 & HL2)).
assert (Hsb : Permutation (pi_sblk o kids keys cap)
  ((kids_blkR kids (Z.of_nat cap) ++ keys_blkR (if o then 6 else 5) keys (Z.of_nat cap)) ++ []))
  by (rewrite app_nil_r; reflexivity).
assert (HPERM' : Permutation D0 ((kids_blkR kids (Z.of_nat cap) ++ keys_blkR 6 keys (Z.of_nat cap)) ++ Di))
  by (rewrite <- (pil_sblk_true kids keys cap), <- Ho; exact HPERM).
pose proof (pil_s_lam0 _ _ _ HL1 Hsb) as HL0. cbn [app] in HL0.
pose proof (pil_s_bl _ _ _ HA1 Hsb) as Hbl.
assert (Hbl' : Permutation bl (prhReader_ab Di ++ ablocks B ly Se)) by exact Hbl.
rewrite Ho in HA1, HL1.
assert (HL2' : Permutation Lam' ((y', 8 * cap2R (Z.of_nat cap)) :: (k', 56 * cap2R (Z.of_nat cap)) :: Lam0))
  by exact HL2.
assert (Hkin' : In (k', 56 * cap2R (Z.of_nat cap)) Lam')
  by (apply (Permutation_in _ (Permutation_sym HL2')); right; left; reflexivity).
assert (Hyin' : In (y', 8 * cap2R (Z.of_nat cap)) Lam')
  by (apply (Permutation_in _ (Permutation_sym HL2')); left; reflexivity).
destruct (pil_lam_bound ly' S' Hp' W' mem' md' _ _ _ _ _ _ _ _ _ HAR HL' Hkin') as (Hk0 & Hk4 & Hkc & _).
destruct (pil_lam_bound ly' S' Hp' W' mem' md' _ _ _ _ _ _ _ _ _ HAR HL' Hyin') as (Hy0 & Hy4 & Hyc & _).
assert (HAB' : Permutation (ablocks B ly' S')
  ((y' - cf_head, 8 * cap2R (Z.of_nat cap) + cf_head) :: (k' - cf_head, 56 * cap2R (Z.of_nat cap) + cf_head) :: bl))
  by exact HA2.
assert (HABk : Permutation (ablocks B ly' S')
  ((k' - cf_head, 56 * cap2R (Z.of_nat cap) + cf_head) :: (y' - cf_head, 8 * cap2R (Z.of_nat cap) + cf_head) :: bl))
  by (apply (Permutation_trans HAB'); apply perm_swap).
assert (Hfk : ~ In (k' - cf_head, 56 * cap2R (Z.of_nat cap) + cf_head)
  ((y' - cf_head, 8 * cap2R (Z.of_nat cap) + cf_head) :: bl)).
{ apply (pil_blk_new_fresh ly' S' Hp' W' mem' md' _ _ HAR HABk). apply pil_req_pos. cbn [snd]. lia. }
assert (Hfy : ~ In (y' - cf_head, 8 * cap2R (Z.of_nat cap) + cf_head)
  ((k' - cf_head, 56 * cap2R (Z.of_nat cap) + cf_head) :: bl)).
{ apply (pil_blk_new_fresh ly' S' Hp' W' mem' md' _ _ HAR HAB'). apply pil_req_pos. cbn [snd]. lia. }
assert (Hold : forall a K, In (a, K) (prhReader_ab (kids_blkR kids (Z.of_nat cap) ++
    keys_blkR (if true then 6 else 5) keys (Z.of_nat cap))) ->
  K = 56 * Z.of_nat cap + cf_head \/ K = 8 * Z.of_nat cap + cf_head).
{ intros a K Hin. change (if true then 6 else 5) with 6 in Hin. rewrite pil_kblk, pil_yblk in Hin.
  destruct (Nat.eqb cap 0); cbn in Hin; [destruct Hin|].
  destruct Hin as [Hq | [Hq | []]]; injection Hq as _ Hq; lia. }
assert (Hnoldk : ~ In (k' - cf_head, 56 * cap2R (Z.of_nat cap) + cf_head) (ablocks B lyc Sc)).
{ intros Hin. apply (Permutation_in _ HA1) in Hin. apply in_app_or in Hin as [Hin | Hin]; [| apply Hfk; right; exact Hin].
  destruct (Hold _ _ Hin) as [E | E]; lia. }
assert (Hnoldy : ~ In (y' - cf_head, 8 * cap2R (Z.of_nat cap) + cf_head) (ablocks B lyc Sc)).
{ intros Hin. apply (Permutation_in _ HA1) in Hin. apply in_app_or in Hin as [Hin | Hin]; [| apply Hfy; right; exact Hin].
  destruct (Hold _ _ Hin) as [E | E]; [|lia].
  destruct (Nat.eq_dec cap 0) as [E0|E0]; [lia | rewrite (Hc2v ltac:(lia)) in Hc2; lia]. }
assert (Hnvk : pj_apartR [(k', 56 * cap2R (Z.of_nat cap))] v).
{ apply pil_s_newv; [apply (Permutation_in _ (Permutation_sym HABk)); left; reflexivity | exact Hnoldk]. }
assert (Hnvy : pj_apartR [(y', 8 * cap2R (Z.of_nat cap))] v).
{ apply pil_s_newv; [apply (Permutation_in _ (Permutation_sym HAB')); left; reflexivity | exact Hnoldy]. }
assert (Hnv : pj_apartR [(k', 56 * cap2R (Z.of_nat cap)); (y', 8 * cap2R (Z.of_nat cap))] v).
{ intros b x [<- | [<- | []]] Hx; [exact (Hnvk _ x (or_introl eq_refl) Hx) | exact (Hnvy _ x (or_introl eq_refl) Hx)]. }
assert (Hdi : forall b, In b Di ->
  In (fst b - cf_head, snd b + cf_head) ((y' - cf_head, 8 * cap2R (Z.of_nat cap) + cf_head) :: bl)).
{ intros b Hb. right. apply (Permutation_in _ (Permutation_sym Hbl')). apply in_or_app. left.
  exact (in_map (fun ak => (fst ak - cf_head, snd ak + cf_head)) Di b Hb). }
assert (HO : pis_open segs mc (prh_lin Lamc) v true 0 kids keys (Z.of_nat cap) (Z.of_nat (length (map snd acc)))
  (map snd acc) (map fst acc) Di) by (rewrite <- Ho; exact pil_s_open).
assert (HO' : pis_open segs m' (prh_lin Lam') v true 0 k' y' (cap2R (Z.of_nat cap)) (Z.of_nat (length (map snd acc)))
  (map snd acc) (map fst acc) Di).
{ apply (pis_grow_obj segs mc m' Lamc Lam' Lam0 v 0 kids keys (Z.of_nat cap) _ (map snd acc) (map fst acc) Di k' y'
    HO ltac:(rewrite app_assoc; exact HL1) HL2').
  - pose proof HL' as HN'. apply prh_ledger_nodup in HN'.
    first [exact HN' | apply NoDup_ListNoDup; exact HN' | apply NoDup_ListNoDup in HN'; exact HN'].
  - rewrite <- Hlkb. exact (pil_garr8_moved _ _ _ _ _ Hkb Hkb').
  - rewrite <- Hlyb. exact (pil_garr8_moved _ _ _ _ _ Hyb Hyb').
  - rewrite pil_s_lenmap. rewrite Ho in Hh'. exact Hh'.
  - rewrite pil_s_lenmap. rewrite Ho in Hsl'. exact Hsl'.
  - rewrite pil_s_lenmap. lia.
  - lia.
  - lia.
  - rewrite pil_s_lenmap. lia.
  - intros i Hi. rewrite pil_s_lenmap in Hi.
    apply (pil_lam_wr ly' S' Hp' W' mem' md' Lam' _ _ _ _ _ _ k' (56 * cap2R (Z.of_nat cap)) (k' + i) HAR HL' Hkin'). lia.
  - lia.
  - rewrite pil_s_lenmap. lia.
  - exact HKDI.
  - rewrite pil_s_lenmap. apply (pil_s_apart_n k' (56 * cap2R (Z.of_nat cap)) _
      ((y' - cf_head, 8 * cap2R (Z.of_nat cap) + cf_head) :: bl)); [lia | lia | lia | exact HABk | exact Hdi].
  - exact Hnv. }
assert (HC' : pi_cont m' (prh_lin Lam') o v k' y' n (pil_c2 cap) acc Di).
{ rewrite Ho. apply pil_cont_of_open; [| exact pil_s_len | lia |].
  - rewrite <- Hc2. rewrite <- pil_s_lenmap at 1. exact HO'.
  - destruct Hsl' as (_ & (_ & H54) & _). lia. }
left. split; [exact H10|]. split; [exact pil_s_mn|].
exists f', (pil_c2 cap), k', y', (ok0 ++ [true; true]),
  (tr0 ++ [EGrow (56 * cap) (56 * pil_c2 cap); EGrow (8 * cap) (8 * pil_c2 cap)]),
  (pi_sblk o k' y' (pil_c2 cap) ++ Di), Lam',
  (Z.max peakc (Z.max (Ledger.lsum Lamc + 56 * (cap2R (Z.of_nat cap) - Z.of_nat cap)) (Ledger.lsum Lam'))),
  (cntc + 2), failc, ranc.
split; [exact Ef|].
split.
{ apply HKCUR; [exact HL' | | | lia].
  - intros a k Ha Hns. apply (Permutation_in _ HL1) in Ha.
    apply in_app_or in Ha as [Ha | Ha].
    + exfalso. apply Hns. rewrite Ho. exact Ha.
    + apply (Permutation_in _ (Permutation_sym HL2')). right. right. exact Ha.
  - intros a k Ha. apply (Permutation_in _ HL2') in Ha. destruct Ha as [Heq | [Heq | Ha]].
    + right. injection Heq as Eqa Eqk. subst a k. exact Hnoldy.
    + right. injection Heq as Eqa Eqk. subst a k. exact Hnoldk.
    + left. apply (Permutation_in _ (Permutation_sym HL1)). apply in_or_app. right. exact Ha. }
split; [lia|]. split; [exact HC'|]. split; [exact HDEP|].
split.
{ rewrite Ho, pil_sblk_true, pil_kblk, pil_yblk. destruct (Nat.eqb_spec (pil_c2 cap) 0) as [E0|E0]; [lia|].
  rewrite <- Hc2. cbn [app]. exact Hnv. }
split; [apply Permutation_refl|]. split; [lia|].
split.
{ apply (pil_runB d o _ ok0 tr0 f' n cap acc _ [true; true]
    [EGrow (56 * cap) (56 * pil_c2 cap); EGrow (8 * cap) (8 * pil_c2 cap)] (pil_c2 cap) (pil_s_run f' Ef)).
  intros ok1. rewrite Ho. apply pil_grow_obj_ok. exact Hge. }
destruct HLED as (Ho0 & Hc & Hfa & HPL & HPS & HLEN & HPK).
assert (HcG : PjGrammar.calls (tr0 ++ [EGrow (56 * cap) (56 * pil_c2 cap); EGrow (8 * cap) (8 * pil_c2 cap)]) =
  (PjGrammar.calls tr0 + 2)%nat) by (rewrite calls_app; reflexivity).
split.
{ pose proof (pil_fail_at cnt fail _ cntc failc 0 Hfa Hcc ltac:(lia) ltac:(unfold SIZE_MAXZ; lia)) as E0.
  pose proof (pil_fail_at cnt fail _ cntc failc 1 Hfa Hcc ltac:(lia) ltac:(unfold SIZE_MAXZ; lia)) as E1.
  rewrite !Z.add_0_r in E0.
  assert (Hfn0 : fail <> cnt + Z.of_nat (PjGrammar.calls tr0)) by (intros Hf; apply Hcf; apply (proj2 E0); exact Hf).
  assert (Hfn1 : fail <> cnt + Z.of_nat (PjGrammar.calls tr0) + 1) by (intros Hf; apply Hcf1; apply (proj2 E1); exact Hf).
  pose proof pil_s_pk as HPK'.
  unfold pi_led. rewrite pil_s_grant, pil_s_ran. change [true; true] with (repeat true 2). rewrite pil_rep_app, <- HcG.
  apply pil_move_granted; [reflexivity | | | | | | |].
  - intros i Hi. rewrite HcG in Hi. destruct (Nat.lt_ge_cases i (PjGrammar.calls tr0)) as [Hi'|Hi'];
      [exact (pil_s_oks i Hi')|].
    destruct (Nat.eq_dec i (PjGrammar.calls tr0)) as [->|Hne]; [intros Hf; apply Hfn0; lia|].
    replace i with (PjGrammar.calls tr0 + 1)%nat by lia. intros Hf. apply Hfn1. lia.
  - rewrite HcG. apply (pil_cnt_mod cnt (PjGrammar.calls tr0) 2 cntc Hc); lia.
  - rewrite HcG. apply (pil_fa_none cnt fail (PjGrammar.calls tr0) 2 failc Hfa). lia.
  - apply (Permutation_trans HL2'). rewrite Ho, pil_sblk_true, pil_kblk, pil_yblk.
    destruct (Nat.eqb_spec (pil_c2 cap) 0) as [E2|E2]; [lia|]. rewrite <- Hc2. cbn [app].
    eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_skip. exact HL0.
  - rewrite pil_lsz_app. cbn [fold_left]. rewrite Ho, pil_sblk_true, pil_kblk, pil_yblk.
    destruct (Nat.eqb_spec (pil_c2 cap) 0) as [E2|E2]; [lia|]. cbn [app map snd].
    replace (56 * Z.of_nat (pil_c2 cap)) with (Z.of_nat (56 * pil_c2 cap)) by lia.
    replace (8 * Z.of_nat (pil_c2 cap)) with (Z.of_nat (8 * pil_c2 cap)) by lia.
    assert (HQ : Permutation (map snd (kids_blkR kids (Z.of_nat cap) ++ keys_blkR 6 keys (Z.of_nat cap) ++ Di))
      (map Z.of_nat (lszR tr0))).
    { rewrite app_assoc. exact (Permutation_trans (Permutation_map snd (Permutation_sym HPERM')) HPS). }
    pose proof (pil_lsz_grow _ _ _ (56 * cap) (56 * pil_c2 cap) HQ (pil_kcase kids cap)) as P1.
    assert (HQ2 : Permutation (map snd (keys_blkR 6 keys (Z.of_nat cap) ++ (k', Z.of_nat (56 * pil_c2 cap)) :: Di))
      (map Z.of_nat (lsz_evR (lszR tr0) (EGrow (56 * cap) (56 * pil_c2 cap))))).
    { rewrite map_app. cbn [map snd]. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
      rewrite <- map_app. exact P1. }
    pose proof (pil_lsz_grow _ _ _ (8 * cap) (8 * pil_c2 cap) HQ2 (pil_ycase keys cap)) as P2.
    cbn [map snd] in P2. eapply Permutation_trans; [apply perm_swap | exact P2].
  - rewrite pvm_nlive_app, <- HLEN, (Permutation_length HPERM'), !length_app.
    rewrite Ho, pil_sblk_true, !pil_kblk, !pil_yblk. destruct (Nat.eqb_spec (pil_c2 cap) 0) as [E2|E2]; [lia|].
    destruct (Nat.eq_dec cap 0) as [E3|E3].
    + rewrite E3. cbn. lia.
    + destruct (Nat.eqb_spec cap 0); [lia|].
      replace (56 * cap)%nat with (S (56 * cap - 1)) by lia. replace (8 * cap)%nat with (S (8 * cap - 1)) by lia. cbn. lia.
  - rewrite HPK', hpeak_app, Hls. cbn [hpeakR held_ev PjGrammar.held].
    assert (HlsC : Ledger.lsum Lamc = Ledger.lsum D0 + Ledger.lsum Lam)
      by (rewrite (pil_lsum_perm _ _ HPL); apply pvm_lsum_app).
    rewrite HlsC, HLS, Hc2. pose proof (pil_held_hpeak tr0). lia. }
split.
{ split; [|split; [|split]].
  - intros a k Hin. rewrite Ho, pil_sblk_true, pil_kblk, pil_yblk in Hin.
    destruct (Nat.eqb_spec (pil_c2 cap) 0) as [E2|E2]; [lia|].
    destruct Hin as [Heq | [Heq | Hin]].
    + injection Heq as Ha Hk. subst a k. intros Hold'. apply Hfk. right. apply (Permutation_in _ (Permutation_sym Hbl')).
      apply in_or_app. right. rewrite Hc2. exact Hold'.
    + injection Heq as Ha Hk. subst a k. intros Hold'. apply Hfy. right. apply (Permutation_in _ (Permutation_sym Hbl')).
      apply in_or_app. right. rewrite Hc2. exact Hold'.
    + destruct HBLK as (B1 & _). apply B1. apply (Permutation_in _ (Permutation_sym HPERM')). apply in_or_app. right.
      exact Hin.
  - apply (Permutation_trans HABk). rewrite Ho, pil_sblk_true, pil_kblk, pil_yblk.
    destruct (Nat.eqb_spec (pil_c2 cap) 0) as [E2|E2]; [lia|].
    rewrite <- Hc2. cbn [app prhReader_ab map fst snd]. apply perm_skip. apply perm_skip. exact Hbl'.
  - destruct HBLK as (_ & _ & B3 & _). exact (Permutation_trans HFR B3).
  - pose proof (pil_hpeak_granted d o _ ok0 tr0 f' n cap acc _ HX0 (pil_s_run f' Ef)) as HP.
    rewrite Ho, pil_gtrace_ge in HP by exact Hge. exact HP. }
split; [exact HPB'|]. split; [exact HLV'|].
split; [rewrite pvm_prh_held_app; lia|].
split; [rewrite length_app, calls_app, HOK; reflexivity|].
split.
{ rewrite held_app, <- HLS, (pil_lsum_perm _ _ HPERM'), !pvm_lsum_app. rewrite Ho, pil_sblk_true, !pil_kblk, !pil_yblk.
  destruct (Nat.eqb_spec (pil_c2 cap) 0); [lia|]. cbn [PjGrammar.held held_ev Ledger.lsum app].
  destruct (Nat.eqb_spec cap 0) as [E3|E3]; cbn [Ledger.lsum app]; lia. }
split.
{ pose proof (pil_gt_split f' (Nat.succ d) o n cap (rev acc) y) as HS. rewrite pil_gcap_ge in HS by exact Hge.
  assert (HR' : rd_room Sc (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap) ++
    snd (fst (pi_jrb f' (Nat.succ d) o n (pil_c2 cap) (rev acc) y [])))) by (rewrite <- HS; exact (pil_s_room f' Ef)).
  rewrite Ho, pil_gtrace_ge in HR' by exact Hge. rewrite Ho.
  change ((EGrow (56 * cap) (56 * pil_c2 cap) :: (if true then [EGrow (8 * cap) (8 * pil_c2 cap)] else [])) ++
    snd (fst (pi_jrb f' (Nat.succ d) true n (pil_c2 cap) (rev acc) y [])))
    with ([EGrow (56 * cap) (56 * pil_c2 cap); EGrow (8 * cap) (8 * pil_c2 cap)] ++
      snd (fst (pi_jrb f' (Nat.succ d) true n (pil_c2 cap) (rev acc) y []))) in HR'.
  apply (pvm_room_after Sc S' _ _ HR' HRL).
  rewrite pil_evs_model, Ho, (pil_grow_obj_ok n cap [] Hge) in HPm. cbn [fst snd] in HPm. exact HPm. }
(* The batch kit's tail: two granted reallocs; cap' = gcap n cap = ncap (S n); the slots moved to k', the key slots to y' *)
assert (Hmv : pis_moved segs mc m' kids k' (56 * Z.of_nat n))
  by (rewrite Hn, <- Hlkb; exact (pil_garr8_moved _ _ _ _ _ Hkb Hkb')).
split; [unfold pi_grant; rewrite pil_s_grant, calls_app; cbn [PjGrammar.calls PjGrammar.is_call];
  rewrite <- pil_rep_app; reflexivity|].
split; [rewrite pil_s_ncap, (pil_gcap_ge n cap Hge); reflexivity|].
split; [exact (pil_s_ncaps_mv k' Hmv)|].
exists af. split.
- apply (pil_s_fo_mv k' y' Lam').
  + intros x k Hin. unfold prh_lin. apply (Permutation_in _ (Permutation_sym HL2')). right. right.
    apply (Permutation_in _ (Permutation_sym HL0)). apply in_or_app. left. exact Hin.
  + exact Hmv.
  + intros i Hi _. rewrite Hn in Hi.
    apply (pil_lam_wr ly' S' Hp' W' mem' md' Lam' _ _ _ _ _ _ k' (56 * cap2R (Z.of_nat cap)) (k' + i) HAR HL' Hkin'). lia.
  + intros _. lia.
  + right. apply (pil_s_apart_n k' (56 * cap2R (Z.of_nat cap)) _ ((y' - cf_head, 8 * cap2R (Z.of_nat cap) + cf_head) :: bl));
      [lia | lia | lia | exact HABk | exact Hdi].
  + intros _. rewrite Hn, <- Hlyb. exact (pil_garr8_moved _ _ _ _ _ Hyb Hyb').
- apply (pil_flB d o _ ok0 f' n cap af _ [true; true]
    [EGrow (56 * cap) (56 * pil_c2 cap); EGrow (8 * cap) (8 * pil_c2 cap)] (pil_c2 cap) (pil_s_fl f' Ef)).
  intros ok1. rewrite Ho. apply pil_grow_obj_ok. exact Hge.
Qed.

Hypothesis HG : pil_gpost (if o then 6 else 5) 0 0 v kids keys (Z.of_nat n) (Z.of_nat cap)
  kb yb lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc most own ly' S' Hp' W' regs' mem' md'.

(* grow's post read through the text's records (PRH_FnReader.tgrP_R and its arm records), each arm to its lemma *)
Lemma pil_step_core : OUT.
Proof.
pose proof HG as HGQ. unfold pil_gpost in HGQ.
pose proof (tgrP_R_of (md' := md') HGQ) as HR. pose proof (tgrP_hull HR) as HHU.
pose proof (tgrP_room HR) as HRL. pose proof (tgrP_bytes HR) as HBB'.
destruct (tgrP_arms HR) as [A | [A | [A | [A | [A | [A | A]]]]]].
- pose proof (tgrP_R1_of A) as R1.
  exact (pil_arm_room (tgrP1_lt R1) (tgrP1_ret R1) (tgrP1_ablocks R1) (tgrP1_ledger R1) (tgrP1_hdr R1) (tgrP1_keep R1)
    HRL HBB' (tgrP1_live R1) (tgrP1_pos R1) HHU).
- pose proof (tgrP_R2_of A) as R2.
  exact (pil_arm_kfail peakc (cntc + 1) SIZE_MAXZ ranc (tgrP2_eq R2) (tgrP2_ret R2) (tgrP2_ablocks R2) (tgrP2_ledger R2)
    (tgrP2_hdr R2) (tgrP2_kb R2) (tgrP2_yb R2) HRL
    (or_introl (conj (tgrP2_chosen R2) (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))))
    (tgrP2_live R2) (tgrP2_pos R2) HHU).
- pose proof (tgrP_R3_of A) as R3.
  exact (pil_arm_kfail _ _ failc _ (tgrP3_eq R3) (tgrP3_ret R3) (tgrP3_ablocks R3) (tgrP3_ledger R3) (tgrP3_hdr R3)
    (tgrP3_kb R3) (tgrP3_yb R3) HRL
    (or_intror (conj (tgrP3_notchosen R3) (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl
      (conj (tgrP3_outcome R3) (tgrP3_injected R3))))))))
    (tgrP3_live R3) (tgrP3_pos R3) HHU).
- destruct (tgrP_R4_of A) as (k' & Lam' & R4).
  exact (pil_arm_arr k' Lam' (tgrP4_eq R4) (tgrP4_notchosen R4) (tgrP4_array R4) (tgrP4_ret R4) (tgrP4_kmin R4)
    (tgrP4_kalign R4) (tgrP4_swap R4) (tgrP4_ledger R4) (tgrP4_lsum R4) (tgrP4_kb R4) (tgrP4_hdr R4) (tgrP4_slots R4)
    HRL HBB' (tgrP4_live R4) (tgrP4_pos R4) HHU).
- destruct (tgrP_R5_of A) as (k' & Lam' & R5).
  exact (pil_arm_khalf k' Lam' _ _ SIZE_MAXZ ranc (tgrP5_eq R5) (tgrP5_notchosen R5) (tgrP5_object R5) (tgrP5_ret R5)
    (tgrP5_kmin R5) (tgrP5_kalign R5) (tgrP5_swap R5) (tgrP5_ledger R5) (tgrP5_kb R5) (tgrP5_yb R5) (tgrP5_hdr R5) HRL
    (or_introl (conj (tgrP5_chosen R5) (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))))
    (tgrP5_live R5) (tgrP5_pos R5) HHU).
- destruct (tgrP_R6_of A) as (k' & Lam' & R6).
  exact (pil_arm_khalf k' Lam' _ _ failc _ (tgrP6_eq R6) (tgrP6_notchosen R6) (tgrP6_object R6) (tgrP6_ret R6)
    (tgrP6_kmin R6) (tgrP6_kalign R6) (tgrP6_swap R6) (tgrP6_ledger R6) (tgrP6_kb R6) (tgrP6_yb R6) (tgrP6_hdr R6) HRL
    (or_intror (conj (tgrP6_notchosen1 R6) (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl
      (tgrP6_outcome R6)))))))
    (tgrP6_live R6) (tgrP6_pos R6) HHU).
- destruct (tgrP_R7_of A) as (k' & y' & Lam' & R7).
  exact (pil_arm_obj k' y' Lam' (tgrP7_eq R7) (tgrP7_notchosen R7) (tgrP7_object R7) (tgrP7_notchosen1 R7) (tgrP7_ret R7)
    (tgrP7_kmin R7) (tgrP7_kalign R7) (tgrP7_ymin R7) (tgrP7_yalign R7) (tgrP7_swap R7) (tgrP7_ledger R7)
    (tgrP7_lsum R7) (tgrP7_kb R7) (tgrP7_yb R7) (tgrP7_hdr R7) (tgrP7_slots R7) HRL HBB' (tgrP7_live R7) (tgrP7_pos R7)
    HHU).
Qed.

End step.

Lemma pil_grow_step : pil_grow_step_stmt.
Proof.
unfold pil_grow_step_stmt.
intros ly S d o tb text len p q v e regs0 Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc f n cap acc kids keys Di
  pc ok0 tr0 D0 Lamc peakc cntc failc ranc af kb yb ly' S' Hp' W' regs' mem' md'
  HMN HCUR HCNT HCONT HDEP HAP HPERM HFUEL HRUN HX0 HCNT0 HLED HBLK HPOSB HLIVE HBB HOK HLS HROOM
  HGRANT HCAPN HNCAPS HFO HFL HBYT HG HMK HKDI HAR HNEWV HKCUR HFR.
change (pil_step_out ly S d o tb text len p q v e regs0 Lam peak cnt fail ran most own kr f n acc Di pc ly' S' Hp' W'
  regs' mem').
eapply pil_step_core; eassumption.
Qed.

End gs.

(* ================================================================================================== *)
(* 5. THE WALK of PI_O_LOOP (0x87b70 .. 0x87bb8). The Section preamble is PItems_body.v's, verbatim.   *)
(* ================================================================================================== *)
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

(* ---- the image facts of the abstract PrhImg instance this segment needs.
   Each is discharged at PIi := prh_img_B by computation. PIL_FR and PIL_PSTRO are the KEY segment's PIK_FR and
   PIK_PSTRO, same texts (PIL_PSTRO is PItems_kept.v's HPSTRO, = S1ImgB.pst_not_ro_B at image B). ---- *)
Hypothesis PIL_FR : PRH_Base.pi_frame F_parse_items = PI_FRAME.
(* grow sets s0 := a0 + 48 (image B's generated pi_s0cur F_grow, MEASURED at 0x870b8 `addi s0, s1, 48`) *)
Hypothesis PIL_S0G : pi_s0cur F_grow = Some 48.
Hypothesis PIL_PSTRO : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS pa_relro_lo pa_relro_hi a.
(* the statics (the allocator's ledger words, prh_pst) are image bytes (at image B by computation
   on prh_pst and PI_prog_B's segments, as FuzzFreeB.v's ff_live_pst) *)
Hypothesis PIL_PSTIMG : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a.
(* the head length of the instance's event lists (prhPg_evs: cf_head) is the model's (rd_hevs: PresetReqAt.HEAD), so
   tgrow_specX's count premises and its post's lists meet pi_ent's and pi_posb's (OWNER: the instance, reflexivity at
   CfParams_preset, 16 = 16) *)
Hypothesis PIL_HEAD : cf_head = PresetReqAt.HEAD.
(* PItems_kept.v's laws (PItems_kept.pi_cur_kept_call needs them; texts verbatim, owners as named there: HSH, HZS,
   HIMG); the grow call's journal is at wle' (aj_call_xW_spR), so the
   walk takes the kept-call statement over a world relation R *)
Hypothesis HSH : pi_hshadow_law (L := Lb) (PA := PIb) B ARx cf_head.
Hypothesis HZS : pi_zs_law (L := Lb) (PA := PIb) B ARx.
Hypothesis HIMG : pi_img_law (L := Lb) (PA := PIb) B ARx.

Lemma pil_hkc : pi_cur_kept_callR_stmt (L := Lb) (PA := PIb) (SKq := SK) B ARx.
Proof. exact (pi_cur_kept_callR B ARx LAWS HSH HZS HIMG PIL_PSTRO). Qed.

Lemma pil_s0g : forall x, prh_s0 F_grow x = x + 48.
Proof. intros x. unfold prh_s0. rewrite PIL_S0G. reflexivity. Qed.

(* the return site of the grow call: 0x87b78, the refusal test *)
Definition PIL_O_RET : Z := PI_O_LOOP + 8.

Lemma pil_zmaxl_in : forall x l, In x l -> x <= zmaxl l.
Proof.
intros x l. induction l as [|y l IH]; intros H; [destruct H|]. cbn [zmaxl fold_right].
destruct H as [<-|H]; [lia|]. specialize (IH H). fold (zmaxl l). lia.
Qed.

(* the stack budget of the grow call: its frame and parse_items' own fit in parse_items' bound *)
Lemma pil_stk_grow : forall d, STK_grow + PI_FRAME <= STK_parse_items d.
Proof.
intros d. unfold STK_parse_items, LEAF_pv_pi. rewrite PIL_FR.
pose proof (pil_zmaxl_in STK_grow [STK_RT_ECALL; STK_RT_STRTOD; STK_fuzz_malloc; STK_fuzz_free; STK_literal;
  STK_parse_string; STK_grow; STK_skip_ws] ltac:(cbn; tauto)) as H1.
pose proof (pi_frame_nonneg F_parse_value) as H2. pose proof (pi_frame_nonneg F_parse_items) as H3.
pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - d)) as H4.
assert (H5 : 0 <= Z.of_nat (PjGrammar.MAXD - d) * (PRH_Base.pi_frame F_parse_value + PRH_Base.pi_frame F_parse_items)) by nia.
lia.
Qed.

Lemma pil_rdword_of_val : forall (H : word -> bool) (mem : word -> option byte) a v,
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

(* pi_cur is a reader predicate: it survives a memory with the same restricted reader *)
Lemma pil_cur_rdeq : forall (regs0 : bvmap 5 word) e q v text len tb dd lyc Sc Hpc (Wc : world SEGS) memc memc' pc
  Lamc peakc cntc failc ranc most own,
  mrestrict (w_H Wc) memc' = mrestrict (w_H Wc) memc ->
  pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb dd lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc most own ->
  pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb dd lyc Sc Hpc Wc memc' pc Lamc peakc cntc failc ranc most own.
Proof.
intros regs0 e q v text len tb dd lyc Sc Hpc Wc memc memc' pc Lamc peakc cntc failc ranc most own Heq H.
unfold pi_cur, src_rd, bytes_at, prh_ledger, prh_glob, prh_most, prh_own, prh_hblock, aview in H |- *.
rewrite Heq. exact H.
Qed.

(* fpre's read-only view rides through a journal (at any world relation) whose footprint does not open the sink (its
   image clause) *)
Lemma pil_rod_kept : forall (R : world SEGS -> world SEGS -> Prop) STK sp0 FP ly S Hp (W : world SEGS) mem md own lyc Sc
  Hpc (W' : world SEGS) mem' md' k,
  ajournal_xR (SK := SK) SEGS B prh_pst ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W' mem' md' k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem').
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W' mem' md' k HJ Hsk Hrod a Hro Hos Her.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (Hrod a Hro Hos Her) | | exact Hos | exact Her | | apply fp_spares_closed; exact Hsk].
- destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img a Hr)].
- intros Hp'. exact (PIL_PSTRO a Hp' Hro).
Qed.

(* bytes read through one world's reader agree with another's wherever their views agree *)
Lemma pil_val_win : forall (W1 W2 : world SEGS) m1 m2 a n x,
  (forall k, (k < n)%nat -> aview SEGS (w_H W2) m2 (a + Z.of_nat k) = aview SEGS (w_H W1) m1 (a + Z.of_nat k)) ->
  val_mem SEGS (mrestrict (w_H W1) m1) a n x -> val_mem SEGS (mrestrict (w_H W2) m2) a n x.
Proof.
intros W1 W2 m1 m2 a n x HA HV kk Hk.
rewrite (mbyte_of_aview SEGS (w_H W1) (w_H W2) m1 m2 (a + Z.of_nat kk) (HA kk Hk)). exact (HV kk Hk).
Qed.

(* parse_items' frame across a stretch that keeps its view on [sp + 40, entry sp + e) outside rd_fp q v (the frame
   cells sp + 40 .. sp + 144 and the caller window; the stretch may write the cache cells [sp, sp + 40)) *)
Lemma pil_frame_win : forall (regs0 regs regs' : bvmap 5 word) (W : world SEGS) mem (Wc W' : world SEGS) memc mem' e q v,
  pi_frame (L := Lb) (PA := PIb) regs0 regs W mem Wc memc e q v ->
  spZ regs' = spZ regs -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> spZ regs0 <= q ->
  (v + 56 <= spZ regs \/ spZ regs0 + e <= v) ->
  (forall a, spZ regs + 40 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H Wc) memc a) ->
  pi_frame (L := Lb) (PA := PIb) regs0 regs' W mem W' mem' e q v.
Proof.
intros regs0 regs regs' W mem Wc W' memc mem' e q v
  (Fsp & F3 & F4 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & Fw & Fr & He0 & He16)
  Hsp H3 H4 Hq Hv HW.
unfold PI_FRAME in Fsp.
assert (NF : forall a, spZ regs + 40 <= a < spZ regs + 144 -> ~ inFP (rd_fp q v) a).
{ intros a Ha (r & Hr & Hra). cbn [rd_fp In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hra; lia. }
assert (VW : forall o x, 40 <= o -> o + 8 <= 144 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs + o) 8 x -> val_mem SEGS (mrestrict (w_H W') mem') (spZ regs' + o) 8 x).
{ intros o x Ho1 Ho2 Hv0. rewrite Hsp. apply (pil_val_win Wc W' memc mem'); [|exact Hv0].
  intros kk Hk. apply HW; [lia|]. apply NF. lia. }
split; [rewrite Hsp; unfold PI_FRAME; lia|]. split; [rewrite H3; exact F3|]. split; [rewrite H4; exact F4|].
split; [apply VW; [lia | lia | exact V1]|]. split; [apply VW; [lia | lia | exact V2]|].
split; [apply VW; [lia | lia | exact V3]|]. split; [apply VW; [lia | lia | exact V4]|].
split; [apply VW; [lia | lia | exact V5]|]. split; [apply VW; [lia | lia | exact V6]|].
split; [apply VW; [lia | lia | exact V7]|]. split; [apply VW; [lia | lia | exact V8]|].
split; [apply VW; [lia | lia | exact V9]|]. split; [apply VW; [lia | lia | exact V10]|].
split; [apply VW; [lia | lia | exact V11]|]. split; [apply VW; [lia | lia | exact V12]|].
split; [apply VW; [lia | lia | exact V13]|].
split; [|split; [exact Fr | split; [exact He0 | exact He16]]].
intros a Ha Hn. rewrite <- (Fw a Ha Hn). apply HW; [lia | exact Hn].
Qed.

(* The kit's post reads memory only through the world's reader *)
Lemma pil_post_stable : forall ly S d o tb text len p q v Lam peak cnt fail ran most own kr,
  pi_Qstable (L := Lb) (PA := PIb) (pi_post (L := Lb) (PA := PIb) B ly S d o tb text len p q v Lam peak cnt fail ran
    most own kr).
Proof.
intros ly S d o tb text len p q v Lam peak cnt fail ran most own kr ly' S' Hp' W' regs m m' md md' Hm HQ.
assert (Em : mrestrict (w_H W') m' = mrestrict (w_H W') m) by (apply functional_extensionality; exact Hm).
unfold pi_post, tpiP_Q, tpiP_ASome, tpiP_ANone, prh_ledger, prh_glob, prh_most, prh_own, prh_hblock in *.
pattern (mrestrict (w_H W') m'). rewrite Em. exact HQ.
Qed.

(* a jump to the epilogue with s5 = -1: PItemsEntry's pi_epi_spec at the budget predicate P (the batch kit: generic in P), given
   the journal at wle' at a budget WS0 with P WS0, the frame at the jump and the refused post for a0 = -1 *)
Lemma pil_epi_exit : forall d (P : list (list Z) -> Prop) (fxc fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md
  (regs0 : bvmap 5 word) e q v (o : bool) tb text len p Lam peak cnt fail ran most own kr lyc Sc Hpc (Wc : world SEGS)
  memc mdc k (regs : bvmap 5 word) WS0,
  pi_ajR (L := Lb) (PA := PIb) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc
    memc mdc k WS0 -> P WS0 ->
  pi_fpok fx0 fxc -> YAkMemnorm.memnorm SEGS memc ->
  pi_frame (L := Lb) (PA := PIb) regs0 regs W mem Wc memc e q v -> getr regs 21 = w64 (-1) ->
  (forall regs', getr regs' 10 = w64 (-1) ->
     pi_post (L := Lb) (PA := PIb) B ly S d o tb text len p q v Lam peak cnt fail ran most own kr
       lyc Sc Hpc Wc regs' memc mdc) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfg_at (fx := fxc) SEGS (VALb A_TEXT + PIATb PI_O_EPI) regs memc mdc)
    (fpostWFbm (fx := fx0) (L := Lb) (PA := PIb) B ARx SK P (STK_parse_items d) e (rd_fp q v) regs0 ly S Hp W mem md
       (pi_post (L := Lb) (PA := PIb) B ly S d o tb text len p q v Lam peak cnt fail ran most own kr)).
Proof.
intros d P fxc fx0 ly S Hp W mem md regs0 e q v o tb text len p Lam peak cnt fail ran most own kr
  lyc Sc Hpc Wc memc mdc k regs WS0 HJ HP HFP HMN HFR H21 HQ.
apply (HEPI d P fxc fx0 ly S Hp W mem md regs0 e q v
  (pi_post (L := Lb) (PA := PIb) B ly S d o tb text len p q v Lam peak cnt fail ran most own kr)
  lyc Sc Hpc Wc memc mdc k regs (-1) WS0 HJ HP).
split; [exact HFP|]. split; [exact HMN|]. split; [exact HFR|]. split; [exact H21|].
split; [apply pil_post_stable | exact HQ].
Qed.

(* off the image, two equal views are two equal readers: the same byte and the same writability *)
Lemma pil_agree_view : forall (W1 W2 : world SEGS) m1 m2 x, 0 <= x < 2 ^ 64 -> ~ in_img SEGS x ->
  aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x ->
  mbyte SEGS (mrestrict (w_H W2) m2) x = mbyte SEGS (mrestrict (w_H W1) m1) x /\
  (writable_at SEGS (mrestrict (w_H W1) m1) x -> writable_at SEGS (mrestrict (w_H W2) m2) x).
Proof.
intros W1 W2 m1 m2 x Hx Hn E.
pose proof (mbyte_of_aview SEGS _ _ _ _ x E) as EM. split; [exact EM|].
unfold mbyte in EM. rewrite (seg_rom_none SEGS x Hx Hn) in EM.
unfold writable_at, wview. revert EM.
destruct (mrestrict (w_H W1) m1 (Z_to_bv 64 x)) as [b|] eqn:E1;
  destruct (mrestrict (w_H W2) m2 (Z_to_bv 64 x)) as [b'|] eqn:E2; intros EM Hw.
- intros C; discriminate C.
- discriminate EM.
- intros C; discriminate C.
- exfalso. apply Hw. rewrite unsigned_lit_small by lia. rewrite (find_segment_none SEGS x Hn). reflexivity.
Qed.

(* ---- block arithmetic over the image's laws (LAWS) ---- *)
Lemma pil_req_pos0 : forall k, 0 <= k -> 0 < req_size k.
Proof. intros k Hk. unfold req_size. destruct (Z.eqb_spec k 0); lia. Qed.

Lemma pil_req_ge0 : forall k, 0 <= k -> k <= req_size k.
Proof. intros k Hk. unfold req_size. destruct (Z.eqb_spec k 0); lia. Qed.

(* a ledger entry is a live allocator block, its head below it *)
Lemma pil_lam_blk : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own a k,
  prh_ledger (L := Lb) (PA := PIb) B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B ly S) /\ In (a - cf_head) Hp.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin.
pose proof HL as HF. apply prh_ledger_blocks in HF.
rewrite Forall_forall in HF. destruct (HF (a, k) Hin) as (Hk & Hb & Hh & _). cbn [fst snd] in *. auto.
Qed.

Lemma pil_blk_bnd : forall ly S Hp (W : world SEGS) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem md p n HA Hin.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md p n HA Hin) as (_ & H4 & Hc & _). auto.
Qed.

(* a ledger entry's user bytes exist *)
Lemma pil_lam_bytes : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own a k,
  ARx ly S Hp W mem md -> prh_ledger (L := Lb) (PA := PIb) B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  exists l, bytes_at (L := Lb) (PA := PIb) W mem a l /\ Z.of_nat (length l) = k.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k HA HL Hin.
destruct (pil_lam_blk ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin) as (Hk & Hb & _).
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HA Hb) as (_ & _ & _ & _ & Hpr & _).
pose proof (@cf_head_nonneg cp) as Hh.
assert (Hr : k + cf_head <= req_size (k + cf_head)) by (apply pil_req_ge0; lia).
destruct (garr8_of_present SEGS (mrestrict (w_H W) mem) a (Z.to_nat k)) as (l & Hl & G).
{ intros x Hx. destruct (proj1 (Hpr x ltac:(lia))) as (Hh0 & b0 & Hb0). exists b0. unfold mrestrict. rewrite Hh0. exact Hb0. }
exists l. split; [exact G | lia].
Qed.

(* two live blocks that differ are apart *)
Lemma pil_blk_disj : forall ly S Hp (W : world SEGS) mem md P Q, ARx ly S Hp W mem md ->
  In P (ablocks B ly S) -> In Q (ablocks B ly S) -> P <> Q ->
  zdisjoint (fst P, req_size (snd P)) (fst Q, req_size (snd Q)).
Proof.
intros ly S Hp W mem md [p n] [p' n'] HA HP HQ Hne. cbn [fst snd].
exact (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md p n p' n' HA HP HQ Hne).
Qed.

(* two live blocks of positive size with the same base are one block *)
Lemma pil_blk_same_base : forall ly S Hp (W : world SEGS) mem md b m m', ARx ly S Hp W mem md ->
  In (b, m) (ablocks B ly S) -> In (b, m') (ablocks B ly S) -> 0 <= m -> 0 <= m' -> m = m'.
Proof.
intros ly S Hp W mem md b m m' HA H1 H2 Hm Hm'.
destruct (Z.eq_dec m m') as [E|E]; [exact E|]. exfalso.
pose proof (pil_blk_disj ly S Hp W mem md (b, m) (b, m') HA H1 H2 ltac:(intros C; injection C; lia)) as Hd.
pose proof (pil_req_pos0 m Hm). pose proof (pil_req_pos0 m' Hm'). unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the node lies below the allocation ceiling: every place prhReader_at allows but the granted window is a live block
   or a live frame (rd_pre excludes the window) *)
Lemma pil_v_low : forall lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc most own (regs0 : bvmap 5 word)
  e v,
  ARx lyc Sc Hpc Wc memc mdc ->
  prh_ledger (L := Lb) (PA := PIb) B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc most own ->
  prhReader_at B lyc Sc Lamc regs0 e v 56 -> (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  v + 56 <= YM05.alloc_ceiling.
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc most own regs0 e v HA HL Hat Hw.
pose proof (@cf_head_nonneg cp) as Hh.
destruct Hat as [(a & k & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
- destruct (pil_lam_blk lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc most own a k HL Hin) as (Hk & Hb & _).
  destruct (pil_blk_bnd lyc Sc Hpc Wc memc mdc _ _ HA Hb) as (_ & Hc).
  assert (Hr : k + cf_head <= req_size (k + cf_head)) by (apply pil_req_ge0; lia). lia.
- destruct (pil_blk_bnd lyc Sc Hpc Wc memc mdc _ _ HA Hin) as (_ & Hc).
  assert (Hr : m <= req_size m) by (apply pil_req_ge0; lia). lia.
- destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos HA Hin) as (_ & Hc & _). lia.
- lia.
Qed.

(* the call's window holds the caller's: prhReader_at at the call's sp and window *)
Lemma pil_at_widen : forall ly S Lam (regs0 regs : bvmap 5 word) e v,
  spZ regs = spZ regs0 - PI_FRAME -> 0 <= e ->
  prhReader_at B ly S Lam regs0 e v 56 -> prhReader_at B ly S Lam regs (PI_FRAME + e) v 56.
Proof.
intros ly S Lam regs0 regs e v Hsp He H. unfold PI_FRAME in *.
destruct H as [H | [H | [H | (H1 & H2)]]]; [left; exact H | right; left; exact H | right; right; left; exact H |].
right; right; right. rewrite Hsp. lia.
Qed.

(* grow's own room premise, out of the room of the run jrl grants at the loop head: the request bound from rd_room's
   maxreq, and the live room at each of grow's all-granted events (the batch kit's tip's prh_live_evs) from rd_room's, grow's
   events being the first segment of the granted trace's (prhPg_evs_model at PIL_HEAD; PItems_ledk1.pik1_live_evs_pre) *)
Lemma pil_grow_room : forall (o : bool) (n cap : nat) rest S,
  n = cap -> rd_room S (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap) ++ rest) ->
  56 * cap2R (Z.of_nat cap) + cf_head < cf_malloc_max /\
  prh_live_evs S (prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap) []).
Proof.
intros o n cap rest S En (R1 & R2 & R3). split.
- rewrite (pil_gtrace_ge o n cap) in R2 by lia.
  pose proof (pil_cap2R cap) as Hc2. change (if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat) with (pil_c2 cap) in Hc2.
  pose proof (@cf_head_nonneg cp) as Hh.
  assert (Hc2v : (cap = 0%nat /\ pil_c2 cap = 8%nat) \/ ((0 < cap)%nat /\ pil_c2 cap = (2 * cap)%nat))
    by (unfold pil_c2; destruct (Nat.eqb_spec cap 0); [left | right]; lia).
  rewrite pvm_maxreq_app in R2. rewrite Hc2.
  set (M := prh_maxreq rest) in R2.
  destruct o; unfold prh_maxreq in R2; cbn [map fold_right PjGrammar.esize] in R2; cbv iota;
    destruct Hc2v as [(E0 & E1) | (E0 & E1)]; rewrite E1 in *;
    try (subst cap; cbn [Z.of_nat] in *); lia.
- rewrite PresetReqAt.rd_hevs_app in R3. apply PItems_ledk1.pik1_live_evs_pre in R3.
  rewrite pil_ty6, (prhPg_evs_model o (Z.of_nat n) (Z.of_nat cap) [] ltac:(lia) ltac:(lia) PIL_HEAD).
  unfold PRH_Charge.prhPg_gtrace in R3. exact R3.
Qed.

(* the views of two memories with one restricted reader agree *)
Lemma pil_aview_mr : forall (H : word -> bool) (m m' : word -> option byte) a,
  mrestrict H m' = mrestrict H m -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a E. apply (aview_eq_of SEGS). rewrite E. reflexivity. Qed.

(* ---- the grow call's footprint ---- *)
Definition pil_fp1 (o : bool) (v kids keys : Z) (cap : nat) : list (Z * Z) :=
  [(v + 24, v + 40); (v + 48, v + 56)] ++ ablocks_fp (prhReader_ab (pi_sblk o kids keys cap)).

Lemma pil_fp1_cases : forall (o : bool) v kids keys (cap : nat) x, inFP (pil_fp1 o v kids keys cap) x ->
  (v + 24 <= x < v + 56) \/
  exists s ks, In (s, ks) (pi_sblk o kids keys cap) /\ s - cf_head <= x < s - cf_head + req_size (ks + cf_head).
Proof.
intros o v kids keys cap x (r & Hr & Hx). unfold pil_fp1 in Hr. apply in_app_or in Hr as [Hr | Hr].
- left. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hx; lia.
- right. unfold ablocks_fp, prhReader_ab in Hr. rewrite map_map in Hr. apply in_map_iff in Hr as ([s ks] & <- & Hin).
  exists s, ks. cbn [fst snd] in Hx |- *. split; [exact Hin | lia].
Qed.

(* a live block that is none of the slot blocks avoids their ranges *)
Lemma pil_avoid_slots : forall ly S Hp (W : world SEGS) mem md (o : bool) kids keys (cap : nat) P x,
  ARx ly S Hp W mem md ->
  (forall s ks, In (s, ks) (pi_sblk o kids keys cap) -> In (s - cf_head, ks + cf_head) (ablocks B ly S)) ->
  In P (ablocks B ly S) ->
  (forall s ks, In (s, ks) (pi_sblk o kids keys cap) -> P <> (s - cf_head, ks + cf_head)) ->
  fst P <= x < fst P + req_size (snd P) ->
  ~ (exists s ks, In (s, ks) (pi_sblk o kids keys cap) /\ s - cf_head <= x < s - cf_head + req_size (ks + cf_head)).
Proof.
intros ly S Hp W mem md o kids keys cap P x HA Hsl HP Hne Hx (s & ks & Hin & Hx2).
pose proof (pil_blk_disj ly S Hp W mem md P (s - cf_head, ks + cf_head) HA HP (Hsl s ks Hin) (Hne s ks Hin)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* ---- the callee journal's block clauses (the journal at any world relation R) ---- *)
Lemma pil_survive : forall (R : world SEGS -> world SEGS -> Prop) STK1 sp1 FP1 lyc Sc Hpc (Wc : world SEGS) memc mdc own
  ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 p n i,
  ajournal_xR (SK := SK) SEGS B prh_pst ARx R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc own ly2 S2 Hp2 W2 mem2 md2 k1 ->
  In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n -> ~ inFP FP1 (p + i) ->
  In (p, n) (ablocks B ly2 S2).
Proof.
intros R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc own ly2 S2 Hp2 W2 mem2 md2 k1 p n i HJ Hin Hi Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F13 & _).
assert (Hd : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
destruct (in_dec Hd (p, n) (ablocks B ly2 S2)) as [H | H]; [exact H|].
exfalso. exact (Hn (F13 p n i Hin H Hi)).
Qed.

Lemma pil_keptb : forall (R : world SEGS -> world SEGS -> Prop) STK1 sp1 FP1 lyc Sc Hpc (Wc : world SEGS) memc mdc own
  ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 p n i,
  ajournal_xR (SK := SK) SEGS B prh_pst ARx R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc own ly2 S2 Hp2 W2 mem2 md2 k1 ->
  In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n -> ~ inFP FP1 (p + i) ->
  aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H Wc) memc (p + i).
Proof.
intros R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc own ly2 S2 Hp2 W2 mem2 md2 k1 p n i HJ Hin Hi Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F10 & _).
exact (F10 p n i Hin (pil_survive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n i HJ Hin Hi Hn) Hi Hn).
Qed.

Lemma pil_nodup_app_disj : forall (l1 l2 : list (Z * Z)) x, NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros l1 l2 x HN H1 H2.
assert (HN' : List.NoDup (l1 ++ l2)) by (first [exact HN | apply NoDup_ListNoDup; exact HN]).
clear HN. induction l1 as [|y l1 IH]; [destruct H1|].
cbn [app] in HN'. apply List.NoDup_cons_iff in HN' as [Hn HN''].
destruct H1 as [<-|H1]; [apply Hn; apply in_or_app; right; exact H2 | exact (IH H1 HN'')].
Qed.

(* the slot blocks as allocator blocks of the call state *)
Lemma pil_slots_ab : forall lyc Sc Hpc (Wc : world SEGS) memc Lamc peakc cntc failc ranc most own (o : bool) kids keys
  (cap : nat),
  prh_ledger (L := Lb) (PA := PIb) B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc most own ->
  incl (pi_sblk o kids keys cap) Lamc ->
  forall s ks, In (s, ks) (pi_sblk o kids keys cap) -> In (s - cf_head, ks + cf_head) (ablocks B lyc Sc).
Proof.
intros lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc most own o kids keys cap HL Hinc s ks Hs.
exact (proj1 (proj2 (pil_lam_blk lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc most own s ks HL (Hinc _ Hs)))).
Qed.

(* the text's bytes are in none of the slot blocks: its home at the entry is an entry block, kept, or the image *)
Lemma pil_text_slots : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own lyc Sc Hpc (Wc : world SEGS)
  memc mdc Lamc peakc cntc failc ranc text len (o : bool) kids keys (cap : nat) Di D0,
  ARx lyc Sc Hpc Wc memc mdc ->
  prh_ledger (L := Lb) (PA := PIb) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (L := Lb) (PA := PIb) B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc most own ->
  prhReader_home (L := Lb) (PA := PIb) B ly S Hp Lam text len ->
  Permutation D0 (pi_sblk o kids keys cap ++ Di) ->
  (forall a k, In (a, k) D0 -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) ->
  Permutation (ablocks B lyc Sc) (prhReader_ab D0 ++ ablocks B ly S) ->
  incl (pi_sblk o kids keys cap) Lamc ->
  forall x, text <= x < text + len ->
  ~ (exists s ks, In (s, ks) (pi_sblk o kids keys cap) /\ s - cf_head <= x < s - cf_head + req_size (ks + cf_head)).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc text len o kids
  keys cap Di D0 HAc HL HLc Hhome HP0 HB1 HB2 Hinc x Hx (s & ks & Hs & Hxs).
pose proof (pil_slots_ab lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc most own o kids keys cap HLc Hinc s ks Hs) as HQ.
assert (HQn : ~ In (s - cf_head, ks + cf_head) (ablocks B ly S))
  by (apply HB1; apply (Permutation_in _ (Permutation_sym HP0)); apply in_or_app; left; exact Hs).
assert (Hold : forall P, In P (ablocks B ly S) -> fst P <= x < fst P + req_size (snd P) -> False).
{ intros P HPin HPx.
  assert (HPc : In P (ablocks B lyc Sc))
    by (apply (Permutation_in _ (Permutation_sym HB2)); apply in_or_app; right; exact HPin).
  assert (Hne : P <> (s - cf_head, ks + cf_head)) by (intros Heq; rewrite Heq in HPin; exact (HQn HPin)).
  pose proof (pil_blk_disj lyc Sc Hpc Wc memc mdc P _ HAc HPc HQ Hne) as Hd. unfold zdisjoint in Hd.
  cbn [fst snd] in Hd. lia. }
pose proof (@cf_head_nonneg cp) as Hh.
destruct Hhome as [[(a & k & Hin & H1 & H2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hin & _ & H1 & H2)].
- destruct (pil_lam_blk ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin) as (Hk & HE & _).
  apply (Hold _ HE). cbn [fst snd].
  first [ assert (Hr0 : 0 <= k + cf_head) by lia
        | (try (match goal with H : ?T |- _ => idtac "PIL-H:" H ":" T; fail end); fail) ].
  pose proof (pil_req_ge0 (k + cf_head) Hr0). lia.
- destruct (Hro x Hx) as (Hroa & _ & _).
  assert (Himg : in_img SEGS x)
    by (destruct Hroa as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img x Hr)]).
  exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ x HAc HQ Hxs Himg).
- destruct (Hro x Hx) as (Hroa & _ & _ & _).
  assert (Himg : in_img SEGS x)
    by (destruct Hroa as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img x Hr)]).
  exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ x HAc HQ Hxs Himg).
- apply (Hold (b, m) Hin). cbn [fst snd]. assert (Hm0 : 0 <= m) by lia. pose proof (pil_req_ge0 m Hm0). lia.
Qed.

(* the node's bytes are in none of the slot blocks (prhReader_at's places, the window excluded) *)
Lemma pil_v_slots : forall lyc Sc Hpc (Wc : world SEGS) memc mm mdc Lamc peakc cntc failc ranc most own
  (regs0 : bvmap 5 word) e (o : bool) v kids keys (cap : nat),
  ARx lyc Sc Hpc Wc memc mdc ->
  prh_ledger (L := Lb) (PA := PIb) B lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own ->
  incl (pi_sblk o kids keys cap) Lamc -> pj_apartR (pi_sblk o kids keys cap) v ->
  prhReader_at B lyc Sc Lamc regs0 e v 56 -> (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  (exists P, In P (ablocks B lyc Sc) /\ fst P <= v /\ v + 56 <= fst P + req_size (snd P) /\ 0 <= snd P /\
    (forall s ks, In (s, ks) (pi_sblk o kids keys cap) -> P <> (s - cf_head, ks + cf_head))) \/
  (exists cid pos, In (cid, pos) (frames Sc) /\
    frame_addr lyc cid pos <= v /\ v + 56 <= frame_addr lyc cid pos + fs_frame_bytes cid).
Proof.
intros lyc Sc Hpc Wc memc mm mdc Lamc peakc cntc failc ranc most own regs0 e o v kids keys cap HA HL Hinc HAP Hat Hw.
pose proof (@cf_head_nonneg cp) as Hh.
destruct Hat as [(a & k & Hin & H1 & H2) | [(b & m & Hin & Hnl & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
- destruct (pil_lam_blk lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own a k HL Hin) as (Hk & HE & _).
  left. exists (a - cf_head, k + cf_head). cbn [fst snd].
  assert (Hr0 : 0 <= k + cf_head) by lia. pose proof (pil_req_ge0 (k + cf_head) Hr0).
  split; [exact HE|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros s ks Hs Heq. injection Heq as E1 E2. assert (Ea : a = s) by lia. assert (Ek : k = ks) by lia. subst s ks.
  exact (HAP (a, k) v Hs ltac:(unfold pj_holdsR; cbn [fst snd]; lia) ltac:(lia)).
- left. exists (b, m). cbn [fst snd]. assert (Hm0 : 0 <= m) by lia. pose proof (pil_req_ge0 m Hm0).
  split; [exact Hin|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros s ks Hs Heq. injection Heq as E1 E2. apply Hnl.
  replace (b + cf_head) with s by lia. replace (m - cf_head) with ks by lia. apply Hinc. exact Hs.
- right. exists cid, pos. auto.
- lia.
Qed.

(* the members' bytes are kept by the grow call (they are in none of grow's footprint) *)
Lemma pil_kdi : forall (R : world SEGS -> world SEGS -> Prop) lyc Sc Hpc (Wc : world SEGS) memc mm mdc Lamc peakc cntc
  failc ranc most own (o : bool) v kids keys (cap : nat) Di STK1 sp1 ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1,
  ARx lyc Sc Hpc Wc memc mdc ->
  prh_ledger (L := Lb) (PA := PIb) B lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own ->
  incl (pi_sblk o kids keys cap ++ Di) Lamc -> NoDup (pi_sblk o kids keys cap ++ Di) -> pj_apartR Di v ->
  ajournal_xR (SK := SK) SEGS B prh_pst ARx R STK1 sp1 (pil_fp1 o v kids keys cap) lyc Sc Hpc Wc mm mdc []
    ly2 S2 Hp2 W2 mem2 md2 k1 ->
  forall x, (exists b, In b Di /\ pj_holdsR b x) ->
    mbyte SEGS (mrestrict (w_H W2) mem2) x = mbyte SEGS (mrestrict (w_H Wc) mm) x /\
    (writable_at SEGS (mrestrict (w_H Wc) mm) x -> writable_at SEGS (mrestrict (w_H W2) mem2) x).
Proof.
intros R lyc Sc Hpc Wc memc mm mdc Lamc peakc cntc failc ranc most own o v kids keys cap Di STK1 sp1 ly2 S2 Hp2 W2 mem2
  md2 k1
  HA HL Hinc HND HapD HJ1 x ((a & k) & Hb & Hx).
unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
pose proof (@cf_head_nonneg cp) as Hh.
assert (HinL : In (a, k) Lamc) by (apply Hinc; apply in_or_app; right; exact Hb).
destruct (pil_lam_blk lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own a k HL HinL) as (Hk & HP & _).
assert (Hinc' : incl (pi_sblk o kids keys cap) Lamc) by (intros y Hy; apply Hinc; apply in_or_app; left; exact Hy).
pose proof (pil_slots_ab lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own o kids keys cap HL Hinc') as Hsl.
assert (Hne : forall s ks, In (s, ks) (pi_sblk o kids keys cap) -> (a - cf_head, k + cf_head) <> (s - cf_head, ks + cf_head)).
{ intros s ks Hs Heq. injection Heq as E1 E2. assert (Ea : a = s) by lia. assert (Ek : k = ks) by lia. subst s ks.
  exact (pil_nodup_app_disj _ _ (a, k) HND Hs Hb). }
assert (Hr0 : 0 <= k + cf_head) by lia. pose proof (pil_req_ge0 (k + cf_head) Hr0) as Hr.
assert (Hnf : ~ inFP (pil_fp1 o v kids keys cap) (a - cf_head + (x - (a - cf_head)))).
{ replace (a - cf_head + (x - (a - cf_head))) with x by lia. intros Hf.
  destruct (pil_fp1_cases o v kids keys cap x Hf) as [Hv | Hs].
  - exact (HapD (a, k) x Hb ltac:(unfold pj_holdsR; cbn [fst snd]; lia) ltac:(lia)).
  - exact (pil_avoid_slots lyc Sc Hpc Wc memc mdc o kids keys cap (a - cf_head, k + cf_head) x HA Hsl HP Hne
      ltac:(cbn [fst snd]; lia) Hs). }
assert (Hi : 0 <= x - (a - cf_head) < req_size (k + cf_head)) by lia.
pose proof (pil_keptb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x - (a - cf_head)) HJ1 HP Hi Hnf) as Hv.
replace (a - cf_head + (x - (a - cf_head))) with x in Hv by lia.
destruct (pil_blk_bnd lyc Sc Hpc Wc memc mdc _ _ HA HP) as (Hb4 & Hbc).
pose proof (@alloc_ceiling_lt rc) as Hac.
apply (pil_agree_view Wc W2 mm mem2 x); [lia | | exact Hv].
exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ x HA HP ltac:(lia)).
Qed.

(* the call's new blocks are apart from the node *)
Lemma pil_newv : forall (R : world SEGS -> world SEGS -> Prop) lyc Sc Hpc (Wc : world SEGS) memc mm mdc Lamc peakc cntc
  failc ranc most own (regs0 : bvmap 5 word) e (o : bool) v kids keys (cap : nat) STK1 sp1 ly2 S2 Hp2 (W2 : world SEGS)
  mem2 md2 k1,
  ARx lyc Sc Hpc Wc memc mdc ->
  prh_ledger (L := Lb) (PA := PIb) B lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own ->
  incl (pi_sblk o kids keys cap) Lamc -> pj_apartR (pi_sblk o kids keys cap) v ->
  prhReader_at B lyc Sc Lamc regs0 e v 56 -> (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  ajournal_xR (SK := SK) SEGS B prh_pst ARx R STK1 sp1 (pil_fp1 o v kids keys cap) lyc Sc Hpc Wc mm mdc []
    ly2 S2 Hp2 W2 mem2 md2 k1 ->
  forall b m x, In (b, m) (ablocks B ly2 S2) -> ~ In (b, m) (ablocks B lyc Sc) -> b <= x < b + m -> ~ (v <= x < v + 56).
Proof.
intros R lyc Sc Hpc Wc memc mm mdc Lamc peakc cntc failc ranc most own regs0 e o v kids keys cap STK1 sp1 ly2 S2 Hp2 W2
  mem2 md2
  k1 HA HL Hinc HAP Hat Hw HJ1 b m x Hb2 Hbn Hx Hvx.
pose proof HJ1 as (HA2 & HLY & _ & _ & _ & Hfr & _). cbn [app] in Hfr.
pose proof (pil_slots_ab lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own o kids keys cap HL Hinc) as Hsl.
assert (Hm0 : 0 <= m) by lia. pose proof (pil_req_ge0 m Hm0) as Hrm.
destruct (pil_v_slots lyc Sc Hpc Wc memc mm mdc Lamc peakc cntc failc ranc most own regs0 e o v kids keys cap HA HL Hinc
  HAP Hat Hw)
  as [([p n] & HP & Hpv1 & Hpv2 & Hn0 & Hne) | (cid & pos & Hin & H1 & H2)]; cbn [fst snd] in *.
- assert (Hnf : ~ inFP (pil_fp1 o v kids keys cap) (p + (v - p))).
  { replace (p + (v - p)) with v by lia. intros Hf.
    destruct (pil_fp1_cases o v kids keys cap v Hf) as [Hv | Hs]; [lia|].
    exact (pil_avoid_slots lyc Sc Hpc Wc memc mdc o kids keys cap (p, n) v HA Hsl HP Hne ltac:(cbn [fst snd]; lia) Hs). }
  assert (Hi : 0 <= v - p < req_size n) by lia.
  pose proof (pil_survive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n (v - p) HJ1 HP Hi Hnf) as HP2.
  assert (Hneq : (b, m) <> (p, n)) by (intros Heq; rewrite Heq in Hbn; exact (Hbn HP)).
  pose proof (pil_blk_disj ly2 S2 Hp2 W2 mem2 md2 (b, m) (p, n) HA2 Hb2 HP2 Hneq) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfr; exact Hin).
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m cid pos HA2 Hb2 Hin2) as Hd.
  assert (EF : frame_addr ly2 cid pos = frame_addr lyc cid pos)
    by (unfold frame_addr; destruct HLY as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
  rewrite EF in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the node's bytes are in no slot block *)
Lemma pil_v_noslot : forall lyc Sc Hpc (Wc : world SEGS) memc mm mdc Lamc peakc cntc failc ranc most own
  (regs0 : bvmap 5 word) e (o : bool) v kids keys (cap : nat),
  ARx lyc Sc Hpc Wc memc mdc ->
  prh_ledger (L := Lb) (PA := PIb) B lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own ->
  incl (pi_sblk o kids keys cap) Lamc -> pj_apartR (pi_sblk o kids keys cap) v ->
  prhReader_at B lyc Sc Lamc regs0 e v 56 -> (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  forall x, v <= x < v + 56 ->
  ~ (exists s ks, In (s, ks) (pi_sblk o kids keys cap) /\ s - cf_head <= x < s - cf_head + req_size (ks + cf_head)).
Proof.
intros lyc Sc Hpc Wc memc mm mdc Lamc peakc cntc failc ranc most own regs0 e o v kids keys cap HA HL Hinc HAP Hat Hw x
  Hx (s & ks & Hs & Hxs).
pose proof (pil_slots_ab lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own o kids keys cap HL Hinc s ks Hs) as HQ.
destruct (pil_v_slots lyc Sc Hpc Wc memc mm mdc Lamc peakc cntc failc ranc most own regs0 e o v kids keys cap HA HL Hinc
  HAP Hat Hw)
  as [([p n] & HP & H1 & H2 & Hn0 & Hne) | (cid & pos & Hin & H1 & H2)]; cbn [fst snd] in *.
- pose proof (pil_blk_disj lyc Sc Hpc Wc memc mdc (p, n) _ HA HP HQ (Hne s ks Hs)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ cid pos HA HQ Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the node's bytes are application bytes *)
Lemma pil_v_app : forall lyc Sc Hpc (Wc : world SEGS) memc mm mdc Lamc peakc cntc failc ranc most own
  (regs0 : bvmap 5 word) e (o : bool) v kids keys (cap : nat),
  ARx lyc Sc Hpc Wc memc mdc ->
  prh_ledger (L := Lb) (PA := PIb) B lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own ->
  incl (pi_sblk o kids keys cap) Lamc -> pj_apartR (pi_sblk o kids keys cap) v ->
  prhReader_at B lyc Sc Lamc regs0 e v 56 -> (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  forall x, v <= x < v + 56 -> 4096 <= x /\ (x < kLowShadowBeg \/ (kHighMemBeg <= x /\ x < ASAN_CEIL)).
Proof.
intros lyc Sc Hpc Wc memc mm mdc Lamc peakc cntc failc ranc most own regs0 e o v kids keys cap HA HL Hinc HAP Hat Hw x
  Hx.
destruct (pil_v_slots lyc Sc Hpc Wc memc mm mdc Lamc peakc cntc failc ranc most own regs0 e o v kids keys cap HA HL Hinc
  HAP Hat Hw)
  as [([p n] & HP & H1 & H2 & Hn0 & Hne) | (cid & pos & Hin & H1 & H2)]; cbn [fst snd] in *.
- destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc p n HA HP) as (_ & _ & _ & Happ & _).
  unfold in_app in Happ. lia.
- destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos HA Hin) as (_ & _ & Happ).
  unfold in_app in Happ. lia.
Qed.

(* a slot block's bytes are application bytes *)
Lemma pil_slot_app : forall lyc Sc Hpc (Wc : world SEGS) memc mm mdc Lamc peakc cntc failc ranc most own (o : bool) kids
  keys (cap : nat),
  ARx lyc Sc Hpc Wc memc mdc ->
  prh_ledger (L := Lb) (PA := PIb) B lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own ->
  incl (pi_sblk o kids keys cap) Lamc ->
  forall s ks x, In (s, ks) (pi_sblk o kids keys cap) -> s - cf_head <= x < s - cf_head + req_size (ks + cf_head) ->
  4096 <= x /\ (x < kLowShadowBeg \/ (kHighMemBeg <= x /\ x < ASAN_CEIL)).
Proof.
intros lyc Sc Hpc Wc memc mm mdc Lamc peakc cntc failc ranc most own o kids keys cap HA HL Hinc s ks x Hs Hx.
pose proof (pil_slots_ab lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own o kids keys cap HL Hinc s ks Hs) as HQ.
destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ HA HQ) as (_ & _ & _ & Happ & _).
unfold in_app in Happ. lia.
Qed.

(* no application byte is a shadow byte of an application address *)
Lemma pil_sh_ne : forall x y, 0 <= x -> (x < kLowMemEnd \/ (kHighMemBeg <= x /\ x < kHighMemEnd)) ->
  4096 <= y -> (y < kLowShadowBeg \/ (kHighMemBeg <= y /\ y < ASAN_CEIL)) -> y <> shadow_of_addr SHADOW_OFF x.
Proof.
intros x y Hx0 Hx Hy0 Hy E. pose proof (@ASAN_CEIL_range rc) as CR. unfold shadow_of_addr in E.
unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg in *. lia.
Qed.

(* THE CURSOR AT THE RETURN OF GROW: PItems_kept.v's pi_cur_kept_callR at the grow call (the journal at any R) *)
Lemma pil_kcur : forall (R : world SEGS -> world SEGS -> Prop) ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own
  (regs0 : bvmap 5 word) e q v text len (tb : list Z) (d : nat) lyc Sc Hpc (Wc : world SEGS) mm mdc pc
  Lamc peakc cntc failc ranc (o : bool) kids keys (cap : nat) Di D0 sp1 ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1,
  (* the entry *)
  prh_ledger (L := Lb) (PA := PIb) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_home (L := Lb) (PA := PIb) B ly S Hp Lam text len -> 0 < len ->
  (text + len <= v \/ v + 56 <= text) -> (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  spZ regs0 <= q -> q + 24 <= spZ regs0 + e -> YM05.alloc_ceiling <= spZ regs0 ->
  (* the call state *)
  ARx lyc Sc Hpc Wc mm mdc ->
  pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb d lyc Sc Hpc Wc mm pc Lamc peakc cntc failc ranc most own ->
  Permutation D0 (pi_sblk o kids keys cap ++ Di) ->
  (forall a k, In (a, k) D0 -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) ->
  Permutation (ablocks B lyc Sc) (prhReader_ab D0 ++ ablocks B ly S) ->
  incl (pi_sblk o kids keys cap) Lamc -> pj_apartR (pi_sblk o kids keys cap) v ->
  (* the call *)
  sp1 = spZ regs0 - PI_FRAME -> 0 <= e ->
  ajournal_xR (SK := SK) SEGS B prh_pst ARx R (STK_grow + (PI_FRAME + e)) (sp1 + (PI_FRAME + e))
    (pil_fp1 o v kids keys cap)
    lyc Sc Hpc Wc mm mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, sp1 <= a < sp1 + (PI_FRAME + e) -> ~ inFP (pil_fp1 o v kids keys cap) a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) mm a) ->
  ly_stk_lo ly2 <= spZ regs0 -> spZ regs0 + e <= ly_stk_hi ly2 ->
  forall Lam2 peak2 cnt2 fail2 ran2,
    prh_ledger (L := Lb) (PA := PIb) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most own ->
    (forall a k, In (a, k) Lamc -> ~ In (a, k) (pi_sblk o kids keys cap) -> In (a, k) Lam2) ->
    (forall a k, In (a, k) Lam2 -> In (a, k) Lamc \/ ~ In (a - cf_head, k + cf_head) (ablocks B lyc Sc)) ->
    cnt2 + 2 * Z.of_nat (length (rest_atR tb text pc)) + 2 < 2 ^ 64 - 1 ->
    pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb d ly2 S2 Hp2 W2 mem2 pc Lam2 peak2 cnt2 fail2 ran2 most own.
Proof.
intros R ly S Hp W mem Lam peak cnt fail ran most own regs0 e q v text len tb d lyc Sc Hpc Wc mm mdc pc Lamc peakc cntc
  failc ranc
  o kids keys cap Di D0 sp1 ly2 S2 Hp2 W2 mem2 md2 k1 HL0 Hhome0 Hlen Htv Hvw Hspq Hqe Hceil HA HCUR HP0 HB1 HB2 Hinc HAP
  Esp He HJ1 HX Hslo Hshi Lam2 peak2 cnt2 fail2 ran2 HL2 Hkeep Hnew Hcnt2.
pose proof HCUR as (HIN & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & _).
pose proof HIN as (_ & _ & _ & _ & _ & _ & _ & _ & Hlen' & _).
pose proof HJ1 as (HA2 & _).
pose proof (@cf_head_nonneg cp) as Hh. pose proof (@ASAN_CEIL_range rc) as CR. unfold ASAN_CEIL in CR.
pose proof (pil_v_low lyc Sc Hpc Wc mm mdc Lamc peakc cntc failc ranc most own regs0 e v HA HLG HPLAT Hvw) as Hvl.
assert (HTS := pil_text_slots ly S Hp W mem Lam peak cnt fail ran most own lyc Sc Hpc Wc mm mdc Lamc peakc cntc failc
  ranc text len o kids keys cap Di D0 HA HL0 HLG Hhome0 HP0 HB1 HB2 Hinc).
assert (HVS := pil_v_noslot lyc Sc Hpc Wc mm mm mdc Lamc peakc cntc failc ranc most own regs0 e o v kids keys cap HA HLG
  Hinc HAP HPLAT Hvw).
assert (HVA := pil_v_app lyc Sc Hpc Wc mm mm mdc Lamc peakc cntc failc ranc most own regs0 e o v kids keys cap HA HLG
  Hinc HAP HPLAT Hvw).
assert (HSA := pil_slot_app lyc Sc Hpc Wc mm mm mdc Lamc peakc cntc failc ranc most own o kids keys cap HA HLG Hinc).
(* every byte of grow's footprint is an application byte below the ceiling *)
assert (HFA : forall y, inFP (pil_fp1 o v kids keys cap) y ->
  4096 <= y /\ (y < kLowShadowBeg \/ (kHighMemBeg <= y /\ y < ASAN_CEIL))).
{ intros y Hy. destruct (pil_fp1_cases o v kids keys cap y Hy) as [Hv | (s & ks & Hs & Hys)];
  [apply HVA; lia | exact (HSA s ks y Hs Hys)]. }
unfold ASAN_CEIL in HFA.
apply (pil_hkc R regs0 e q v text len tb d lyc Sc Hpc Wc mm mdc pc Lamc peakc cntc failc ranc most own
  STK_grow sp1 (PI_FRAME + e) (pil_fp1 o v kids keys cap) [] ly2 S2 Hp2 W2 mem2 md2 k1 pc Lam2 peak2 cnt2 fail2 ran2
  most own []).
- exact HCUR.
- exact HJ1.
- exact HX.
- unfold PI_FRAME. lia.
- rewrite Esp. unfold PI_FRAME. lia.
- rewrite Esp. unfold PI_FRAME. lia.
- exact Hslo.
- exact Hshi.
- destruct HHOME as [[(b & m & Hbin & Hb1 & Hb2) | Hro] | (b & m & Hbin & _ & Hb1 & Hb2)].
  + right; right. destruct (pil_lam_blk lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own b m HLG Hbin)
      as (K0 & Kin & _).
    exists (b - cf_head), (m + cf_head). split; [exact Kin | lia].
  + destruct Hro as [Hro | Hki]; [left; exact Hro | right; left; exact Hki].
  + right; right. exists b, m. auto.
- (* the blocks that hold the text or the node are kept, their hidden heads too *)
  intros b m Hbm Hcont.
  assert (Hm0 : 0 < m) by (destruct Hcont as [(H1 & H2) | (H1 & H2)]; lia).
  assert (Hrm : m <= req_size m) by (apply pil_req_ge0; lia).
  assert (HS2 : In (b, m) (ablocks B ly2 S2)).
  { destruct Hcont as [(H1 & H2) | (H1 & H2)].
    - assert (Hi : 0 <= text - b < req_size m) by lia.
      apply (pil_survive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b m (text - b) HJ1 Hbm Hi).
      replace (b + (text - b)) with text by lia. intros Hf.
      destruct (pil_fp1_cases o v kids keys cap text Hf) as [Hv | Hs]; [lia|].
      assert (Hx : text <= text < text + len) by lia. exact (HTS text Hx Hs).
    - assert (Hi : 0 <= v - b < req_size m) by lia.
      apply (pil_survive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b m (v - b) HJ1 Hbm Hi).
      replace (b + (v - b)) with v by lia. intros Hf.
      destruct (pil_fp1_cases o v kids keys cap v Hf) as [Hv | Hs]; [lia|].
      assert (Hx : v <= v < v + 56) by lia. exact (HVS v Hx Hs). }
  split; [exact HS2|].
  assert (Hnslot : forall a k, In (a, k) (pi_sblk o kids keys cap) -> (b, m) <> (a - cf_head, k + cf_head)).
  { intros a k Ha Heq. injection Heq as E1 E2.
    assert (Hrk : k + cf_head <= req_size (k + cf_head)) by (apply pil_req_ge0; lia).
    destruct Hcont as [(H1 & H2) | (H1 & H2)].
    - assert (Hx : text <= text < text + len) by lia. apply (HTS text Hx). exists a, k. split; [exact Ha | lia].
    - assert (Hx : v <= v < v + 56) by lia. apply (HVS v Hx). exists a, k. split; [exact Ha | lia]. }
  pose proof HLG as HHp. apply prh_ledger_heads in HHp. pose proof HL2 as HHp2. apply prh_ledger_heads in HHp2.
  split; intros Hb.
  + apply (Permutation_in _ HHp) in Hb. apply in_map_iff in Hb as ([a k] & Eb & Hak). cbn [fst] in Eb.
    destruct (pil_lam_blk lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own a k HLG Hak) as (Hk & HE & _).
    rewrite Eb in HE.
    assert (Em : m = k + cf_head) by (apply (pil_blk_same_base lyc Sc Hpc Wc mm mdc b m (k + cf_head) HA Hbm HE); lia).
    assert (Hns : ~ In (a, k) (pi_sblk o kids keys cap)).
    { intros Hs. apply (Hnslot a k Hs). rewrite Em. f_equal. lia. }
    pose proof (Hkeep a k Hak Hns) as Hak2.
    apply (Permutation_in _ (Permutation_sym HHp2)). apply in_map_iff. exists (a, k). split; [exact Eb | exact Hak2].
  + apply (Permutation_in _ HHp2) in Hb. apply in_map_iff in Hb as ([a k] & Eb & Hak). cbn [fst] in Eb.
    destruct (Hnew a k Hak) as [Hold | Hfresh].
    * apply (Permutation_in _ (Permutation_sym HHp)). apply in_map_iff. exists (a, k). split; [exact Eb | exact Hold].
    * exfalso. destruct (pil_lam_blk ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most own a k HL2 Hak)
        as (Hk & HE2 & _).
      rewrite Eb in HE2.
      assert (Em : m = k + cf_head)
        by (apply (pil_blk_same_base ly2 S2 Hp2 W2 mem2 md2 b m (k + cf_head) HA2 HS2 HE2); lia).
      apply Hfresh. rewrite Eb, <- Em. exact Hbm.
- (* the text's bytes *)
  intros a Ha Hf. destruct (pil_fp1_cases o v kids keys cap a Hf) as [Hv | Hs]; [lia | exact (HTS a Ha Hs)].
- (* the text's shadow bytes *)
  intros a Ha Hf. destruct (HFA _ Hf) as (Hy0 & Hy).
  rewrite Hlen' in Htam. unfold amem_range in Htam.
  apply (pil_sh_ne a (shadow_of_addr SHADOW_OFF a)); [lia | unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia | lia | | reflexivity].
  unfold ASAN_CEIL. exact Hy.
- (* the node's shadow bytes *)
  intros a Ha Hf. destruct (HFA _ Hf) as (Hy0 & Hy). destruct (HVA a Ha) as (Ha0 & Hav).
  apply (pil_sh_ne a (shadow_of_addr SHADOW_OFF a)); [lia | unfold kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia | lia | | reflexivity].
  unfold ASAN_CEIL. exact Hy.
- (* the sink: address 0 is in no range of grow's footprint *)
  intros Hf. destruct (HFA 0 Hf) as (Hy0 & _). lia.
- (* the cursor: grow's post says nothing of it; its bytes are above the ceiling, the footprint below *)
  right. split; [reflexivity|]. intros a Ha Hf. destruct (HFA a Hf) as (Hy0 & Hy).
  unfold kLowShadowBeg, kHighMemBeg in *. lia.
- exact HL2.
- exact Hcnt2.
- left. reflexivity.
- intros a k Hak Hcont. apply (Hkeep a k Hak). intros Hs.
  destruct (pil_lam_blk lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own a k HLG Hak) as (Hk & _ & _).
  assert (Hrk : k + cf_head <= req_size (k + cf_head)) by (apply pil_req_ge0; lia).
  destruct Hcont as [(H1 & H2) | (H1 & H2)].
  + assert (Hx : text <= text < text + len) by lia. apply (HTS text Hx). exists a, k. split; [exact Hs | lia].
  + assert (Hh1 : pj_holdsR (a, k) v) by (unfold pj_holdsR; cbn [fst snd]; lia).
    assert (Hh2 : v <= v < v + 56) by lia. exact (HAP (a, k) v Hs Hh1 Hh2).
- exact Hspq.
- exact Hqe.
- exact Hnew.
- exact HA.
Qed.

(* ---- THE RETURN SITE (0x87b78 .. 0x87bb8): the refusal test and the frame cache ---- *)
(* 0x87b78 `bnez a0`: the branch the run takes, with a0 grow's result *)
Lemma pil_br_ne : forall E (w : word), ew E 10 = w ->
  branch_taken BC_NE (sv_denot E (SOff 10 0)) (sv_denot E (SLit 0)) = negb (bv_unsigned w =? 0).
Proof.
intros E w Hw. rewrite branch_ne_U.
rewrite (U_atom E 10 (bv_unsigned w)) by (first [rewrite Hw, Z_to_bv_bv_unsigned; reflexivity | apply bv_unsigned_in_range]).
rewrite U_SLit. change (zcanon 0) with 0. reflexivity.
Qed.

(* the run from the return site: TAKEN (a0 <> 0) to the epilogue with nothing changed; NOT TAKEN (a0 = 0) through the
   15 instructions of the cache to PI_O_BODY, the five cache words written at [sp, sp + 40) and nothing else. The
   journal from the entry spans grow's frees, so it is at wle' segs RZ_cf, and so is the run (SRr') *)
Lemma pil_ret_run : forall (fxc : YK11.FPState) d e (regs0 : bvmap 5 word) q v ly S Hp (W : world SEGS) mem md
  ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k2 (regs2 : bvmap 5 word) (Q : world SEGS -> config -> Prop),
  ajournal_xR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k2 ->
  2 ^ 46 <= spZ regs2 -> spZ regs2 + 40 <= 2 ^ 47 -> spZ regs2 mod 16 = 0 ->
  spZ regs2 = spZ regs0 - PI_FRAME -> 0 <= e -> PI_FRAME <= STK_parse_items d ->
  getr regs2 19 = w64 v -> getr regs2 26 = w64 SHADOW_OFF -> 0 <= v -> v + 56 <= 2 ^ 47 ->
  YAkMemnorm.memnorm SEGS mem2 ->
  (getr regs2 10 <> w64 0 -> forall (regs3 : bvmap 5 word) mem3 md3 k3,
     ajournal_xR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
       (rd_fp q v) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem3 md3 k3 ->
     YAkMemnorm.memnorm SEGS mem3 ->
     mrestrict (w_H W2) mem3 = mrestrict (w_H W2) mem2 ->
     spZ regs3 = spZ regs2 -> getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 ->
     getr regs3 21 = getr regs2 21 ->
     SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfg_at (fx := fxc) SEGS (VALb A_TEXT + PIATb PI_O_EPI) regs3 mem3 md3) Q) ->
  (getr regs2 10 = w64 0 -> forall (regs3 : bvmap 5 word) mem3 md3 k3,
     ajournal_xR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
       (rd_fp q v) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem3 md3 k3 ->
     YAkMemnorm.memnorm SEGS mem3 ->
     (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 25; 26; 27]%bv -> getr regs3 r = getr regs2 r) ->
     getr regs3 22 = w64 (v + 40) -> getr regs3 24 = w64 (pi_sh (v + 40)) ->
     pi_agr (fun a => 0 <= a < 2 ^ 64 /\ ~ (spZ regs2 <= a < spZ regs2 + 40))
       (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) mem3) ->
     val_mem SEGS (mrestrict (w_H W2) mem3) (spZ regs2) 8 (2 ^ 60) ->
     val_mem SEGS (mrestrict (w_H W2) mem3) (spZ regs2 + 32) 8 (v + 24) ->
     val_mem SEGS (mrestrict (w_H W2) mem3) (spZ regs2 + 24) 8 (pi_sh (v + 24)) ->
     val_mem SEGS (mrestrict (w_H W2) mem3) (spZ regs2 + 16) 8 (v + 32) ->
     val_mem SEGS (mrestrict (w_H W2) mem3) (spZ regs2 + 8) 8 (pi_sh (v + 32)) ->
     SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfg_at (fx := fxc) SEGS (VALb A_TEXT + PIATb PI_O_BODY) regs3 mem3 md3) Q) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfg_at (fx := fxc) SEGS (VALb A_TEXT + PIATb PIL_O_RET) regs2 mem2 md2) Q.
Proof.
intros fxc d e regs0 q v ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 k2 regs2 Q HJ2 Hsp46 Hsp47 Hsp16 Hsp He Hstk R19 R26
  Hv0 Hv47 HPM KEPI KBODY.
unfold cfg_at in *.
remember (Eimg (PI := PIb) (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VALb A_LIM E) by (subst E; apply Eimg_env).
assert (EK : forall nk (rk : bv 5), Z.of_nat nk = bv_unsigned rk -> ew E nk = getr regs2 rk).
{ intros nk rk Hk. pose proof (bv_unsigned_in_range 5 rk) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs2 [] nk rk Hk). }
assert (HS : st_ok_pi (fx := fxc) SEGS VALb E (mkSS (PIATb PIL_O_RET) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (@YK11.mkst fxc regs2 (Z_to_bv 64 (VALb A_TEXT + PIATb PIL_O_RET)) mem2 (seg_rom SEGS)))).
{ rewrite (restrict_mkst_fx (fx := fxc)).
  apply (pa_entry_st_ok_full (fx := fxc) (L := Lb) (PI := PIb) E (PIATb PIL_O_RET) sr_atoms regs2 []
    (mkFacts [] [] []) (mrestrict (w_H W2) mem2)).
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute; reflexivity.
  - constructor.
  - cbn; exact I.
  - repeat split; exact I. }
assert (SHOK : sh_ok SEGS (SLit 0) [] E (mrestrict (w_H W2) mem2)) by constructor.
pose (RUN := PI_RUNR (fx := fxc) (SK := SK) (L := Lb) (PL := PLb) (PI := PIb) B prh_pst ARx LAWS).
(* the runner that carries memnorm across the run (YC1fPx's _invR runner at YSRrMemnorm's memnorm laws, at wle') *)
pose (RUNTO := paj_run_to_x_invR (fx := fxc) (SK := SK) (L := Lb) (PL := PLb) (PI := PIb) B prh_pst ARx LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (BR := paj_branchR (fx := fxc) (L := Lb) (PI := PIb) (wle' SEGS YGcfRehidePost.RZ_cf)).
change (w64 (VALb A_TEXT + PIATb PIL_O_RET)) with (Z_to_bv 64 (VALb A_TEXT + PIATb PIL_O_RET)).
assert (E19 : ew E 19 = Z_to_bv 64 v) by (rewrite (EK 19%nat 19%bv eq_refl); exact R19).
assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EK 26%nat 26%bv eq_refl); exact R26).
assert (U2 : bv_unsigned (ew E 2) = spZ regs2) by (rewrite (EK 2%nat 2%bv eq_refl); reflexivity).
pose proof (pil_br_ne E (getr regs2 10) (EK 10%nat 10%bv eq_refl)) as HBR.
pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as R10r. unfold bv_modulus in R10r.
assert (KREG : forall msx ssx (r : bv 5), st_ok_pi (fx := fxc) SEGS VALb E ssx (restrict (w_H W2) msx) ->
  sr_get (ss_regs ssx) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs msx) r = getr regs2 r).
{ intros msx ssx r HSx Hr. rewrite (st_ok_pi_restrict_reg (w_H W2) E ssx msx r HSx), Hr. cbn [sv_denot].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply EK. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  unfold bv_modulus in Hr5. cbn in Hr5. lia. }
psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
- (* TAKEN: grow returned non-zero; the epilogue, nothing changed *)
  assert (HNZ : getr regs2 10 <> w64 0).
  { intros E0. rewrite HBR, E0 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia. discriminate Hc. }
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM BAND_SPAN (PIATb PI_O_EPI).
  { apply awr_ok_nil. }
  lazymatch goal with HS' : st_ok_pi _ _ _ ?ssx (restrict _ ?msx) |- _ =>
    assert (MEQ : mrestrict (w_H W2) (ms_mem msx) = mrestrict (w_H W2) mem2);
    [ apply functional_extensionality; intros x; apply HFr; intros (r & Hin & _); exact Hin
    | ];
    assert (K2 : getr (ms_regs msx) 2 = getr regs2 2) by (apply (KREG msx ssx 2%bv HS); vm_compute; reflexivity);
    assert (K3 : getr (ms_regs msx) 3 = getr regs2 3) by (apply (KREG msx ssx 3%bv HS); vm_compute; reflexivity);
    assert (K4 : getr (ms_regs msx) 4 = getr regs2 4) by (apply (KREG msx ssx 4%bv HS); vm_compute; reflexivity);
    assert (K21 : getr (ms_regs msx) 21 = getr regs2 21) by (apply (KREG msx ssx 21%bv HS); vm_compute; reflexivity)
  end.
  pmkst HS.
  lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
    replace pcw with (w64 (VALb A_TEXT + PIATb PI_O_EPI)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
  apply (KEPI HNZ _ _ _ _ HJ2 HPM MEQ); [unfold spZ; rewrite K2; reflexivity | exact K3 | exact K4 | exact K21].
- (* NOT TAKEN: grow returned 0; the cache *)
  assert (HZ : getr regs2 10 = w64 0).
  { rewrite HBR in Hc. apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia.
    destruct (Z.eqb_spec (bv_unsigned (getr regs2 10)) 0) as [Hz|Hz]; [exact Hz | discriminate Hc]. }
  apply st_ok_pi_add_fact with (n := 2%nat) (f := mkAF (2 ^ 46) (2 ^ 47) 4) in HS;
    [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U2; change (2 ^ 4) with 16; repeat split; lia].
  apply st_ok_pi_add_region with (r := YP09.mkRegion (Some 2%nat) 0 40 0 40 []) in HS.
  2: vm_compute; reflexivity.
  2: { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
       rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
       intros o Ho. apply (apresent_writable SEGS).
       pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
       apply Hpres. unfold PI_FRAME in *. lia. }
  2: { apply all_disjoint_of_extents. exact I. }
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM BAND_SPAN (PIATb PI_O_BODY).
  { lazymatch goal with |- awr_ok ?E' ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly' ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E' rs' stk s0 fp b0 bc ly' own) end.
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs2 - (spZ regs0 + e));
      [reflexivity | rewrite U2; lia | cbn; unfold PI_FRAME in *; lia | cbn; unfold PI_FRAME in *; lia | apply awr_ok_nil]. }
  lazymatch goal with HS' : st_ok_pi _ _ _ ?ssx (restrict _ ?msx) |- _ =>
    rename msx into ms3; set (ss3 := ssx) in HS
  end.
  assert (AGR : pi_agr (fun a => 0 <= a < 2 ^ 64 /\ ~ (spZ regs2 <= a < spZ regs2 + 40))
    (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms3))).
  { intros a (Ha & Hn). apply HFr. rewrite unsigned_lit_small by lia. intros (r & Hin & Hra).
    lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change l with l' in Hin end.
    destruct Hin as [<- | []]. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hra. rewrite U2 in Hra. lia. }
  pose proof (pi_region_nth SEGS VALb E _ _ 0%nat _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  assert (Hpi24 : 0 <= pi_sh (v + 24) < 2 ^ 64) by (unfold pi_sh, SHADOW_OFF; lia).
  assert (Hpi32 : 0 <= pi_sh (v + 32) < 2 ^ 64) by (unfold pi_sh, SHADOW_OFF; lia).
  assert (Hpi40 : 0 <= pi_sh (v + 40) < 2 ^ 64) by (unfold pi_sh, SHADOW_OFF; lia).
  assert (HSO : SHADOW_OFF + (v + 24) / 8 < 2 ^ 64 /\ SHADOW_OFF + (v + 32) / 8 < 2 ^ 64 /\
    SHADOW_OFF + (v + 40) / 8 < 2 ^ 64) by (unfold SHADOW_OFF; lia).
  assert (V0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (spZ regs2 + 0) (N.to_nat 8) (2 ^ 60)).
  { apply (pi_field SEGS E _ 2 (spZ regs2) _ 0 40 0 40 0 8 (SLit 1152921504606846976) (2 ^ 60) HR0 U2).
    - repeat (first [left; reflexivity | right]).
    - cbn [sv_denot]. reflexivity.
    - change (8 * Z.of_N 8) with 64. lia.
    - cbn. lia. }
  assert (V32 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (spZ regs2 + 32) (N.to_nat 8) (v + 24)).
  { apply (pi_field SEGS E _ 2 (spZ regs2) _ 0 40 0 40 32 8 (SOff 19 24) (v + 24) HR0 U2).
    - repeat (first [left; reflexivity | right]).
    - exact (pil_sv_off E 19 v 24 E19 ltac:(lia) ltac:(lia)).
    - change (8 * Z.of_N 8) with 64. lia.
    - cbn. lia. }
  assert (V24 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (spZ regs2 + 24) (N.to_nat 8) (pi_sh (v + 24))).
  { apply (pi_field SEGS E _ 2 (spZ regs2) _ 0 40 0 40 24 8
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 24) (SLit 3)) (SOff 26 0)) (pi_sh (v + 24)) HR0 U2).
    - repeat (first [left; reflexivity | right]).
    - exact (pil_sv_sh E 19 26 v 24 E19 E26 ltac:(lia) ltac:(lia) ltac:(lia)).
    - change (8 * Z.of_N 8) with 64. lia.
    - cbn. lia. }
  assert (V16 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (spZ regs2 + 16) (N.to_nat 8) (v + 32)).
  { apply (pi_field SEGS E _ 2 (spZ regs2) _ 0 40 0 40 16 8 (SOff 19 32) (v + 32) HR0 U2).
    - repeat (first [left; reflexivity | right]).
    - exact (pil_sv_off E 19 v 32 E19 ltac:(lia) ltac:(lia)).
    - change (8 * Z.of_N 8) with 64. lia.
    - cbn. lia. }
  assert (V8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (spZ regs2 + 8) (N.to_nat 8) (pi_sh (v + 32))).
  { apply (pi_field SEGS E _ 2 (spZ regs2) _ 0 40 0 40 8 8
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 32) (SLit 3)) (SOff 26 0)) (pi_sh (v + 32)) HR0 U2).
    - repeat (first [left; reflexivity | right]).
    - exact (pil_sv_sh E 19 26 v 32 E19 E26 ltac:(lia) ltac:(lia) ltac:(lia)).
    - change (8 * Z.of_N 8) with 64. lia.
    - cbn. lia. }
  change (N.to_nat 8) with 8%nat in V0, V32, V24, V16, V8. rewrite Z.add_0_r in V0.
  assert (K22 : getr (ms_regs ms3) 22 = w64 (v + 40)).
  { rewrite (st_ok_pi_restrict_reg (w_H W2) E _ ms3 22%bv HS).
    replace (sr_get (ss_regs ss3) 22%bv) with (SOff 19 40) by (vm_compute; reflexivity).
    exact (pil_sv_off E 19 v 40 E19 ltac:(lia) ltac:(lia)). }
  assert (K24 : getr (ms_regs ms3) 24 = w64 (pi_sh (v + 40))).
  { rewrite (st_ok_pi_restrict_reg (w_H W2) E _ ms3 24%bv HS).
    replace (sr_get (ss_regs ss3) 24%bv) with (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 40) (SLit 3)) (SOff 26 0))
      by (vm_compute; reflexivity).
    exact (pil_sv_sh E 19 26 v 40 E19 E26 ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (KK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 25; 26; 27]%bv -> getr (ms_regs ms3) r = getr regs2 r).
  { intros r Hr.
    repeat (destruct Hr as [<- | Hr]; [apply (KREG ms3 ss3 _ HS); vm_compute; reflexivity |]). destruct Hr. }
  pmkst HS.
  lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
    replace pcw with (w64 (VALb A_TEXT + PIATb PI_O_BODY)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
  exact (KBODY HZ _ _ _ _ HJ2 HPM KK K22 K24 AGR V0 V32 V24 V16 V8).
Qed.

(* ---- readers across a write that keeps every byte outside a band ---- *)
Lemma pil_aview_agr : forall F (H : word -> bool) (m m' : word -> option byte) a,
  pi_agr F (mrestrict H m) (mrestrict H m') -> F a -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros F H m m' a HA Ha. apply (aview_eq_of SEGS). exact (HA a Ha). Qed.

Lemma pil_ra_agr : forall F (H : word -> bool) (m m' : word -> option byte) a n,
  pi_agr F (mrestrict H m) (mrestrict H m') -> (forall x, a <= x < a + n -> F (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable (aview SEGS H m) SHADOW_OFF a n -> range_addressable (aview SEGS H m') SHADOW_OFF a n.
Proof. intros F H m m' a n HA HF Hr x Hx. rewrite (pil_aview_agr F H m m' _ HA (HF x Hx)). exact (Hr x Hx). Qed.

Lemma pil_hull_agr : forall F (H : word -> bool) (m m' : word -> option byte) x n,
  pi_agr F (mrestrict H m) (mrestrict H m') ->
  (forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> F s) ->
  shadow_hull_vis (aview SEGS H m) x n -> shadow_hull_vis (aview SEGS H m') x n.
Proof. intros F H m m' x n HA HF Hv s Hs. rewrite (pil_aview_agr F H m m' s HA (HF s Hs)). exact (Hv s Hs). Qed.

Lemma pil_stk_grow_ge : 4096 <= STK_grow.
Proof.
unfold STK_grow, STK_fuzz_realloc.
pose proof (pi_frame_nonneg F_grow). pose proof (pi_frame_nonneg F_fuzz_realloc).
pose proof (pil_zmaxl_in STK_RT_ECALL [STK_RT_ALLOC; STK_RT_ECALL; STK_own; STK_fuzz_malloc] ltac:(cbn; tauto)) as HZM.
unfold STK_RT_ECALL, ESTACK in *. lia.
Qed.

(* the ledger survives a write above alloc_ceiling + 8 *)
Lemma pil_ledger_agr : forall F ly S Hp (W : world SEGS) mem md mem' Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md ->
  (forall a, 0 <= a < YM05.alloc_ceiling + 8 -> F a) ->
  pi_agr F (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  prh_ledger (L := Lb) (PA := PIb) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (L := Lb) (PA := PIb) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros F ly S Hp W mem md mem' Lam peak cnt fail ran most own HA HF HAG HL.
pose proof HL as G. apply prh_ledger_glob in G. pose proof HL as HN. apply prh_ledger_nodup in HN.
pose proof HL as HB. apply prh_ledger_blocks in HB. pose proof HL as HP. apply prh_ledger_heads in HP.
pose proof (@alloc_ceiling_lt rc) as Hac. pose proof (@ASAN_CEIL_range rc) as CR. unfold ASAN_CEIL in CR.
pose proof (@cf_head_nonneg cp) as Hh.
assert (HPST : forall g (z : nat) v0, In (g, Z.of_nat z) prh_pst ->
  val_mem SEGS (mrestrict (w_H W) mem) g z v0 -> val_mem SEGS (mrestrict (w_H W) mem') g z v0).
{ intros g z v0 Hin Hv. apply (pi_val_agr SEGS F _ _ _ _ _ HAG); [|exact Hv]. intros k Hk. apply HF.
  assert (Hx : Exists (in_zr (g + Z.of_nat k)) prh_pst)
    by (apply Exists_exists; exists (g, Z.of_nat z); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (pa_segs_low (PAImg := PIb) _ (PIL_PSTIMG _ Hx)) as Hl. unfold kLowMemEnd in Hl. lia. }
split; [|split; [exact HN | split; [| exact HP]]].
- (* the glob, cell by cell and not by position: each val_mem cell is a static of prh_pst (g_most's and
     g_own_ran_out's cells inside prh_most / prh_own, beside their value bounds), the bounds read no memory *)
  unfold prh_glob in G |- *.
  repeat (lazymatch type of G with _ /\ _ => idtac end;
    let Gc := fresh "Gc" in destruct G as [Gc G]; split;
    [ first [ exact Gc | apply HPST; [unfold prh_pst; repeat (first [left; reflexivity | right]) | exact Gc]
            | destruct Gc as [Gcv Gcb]; split;
              [apply HPST; [unfold prh_pst; repeat (first [left; reflexivity | right]) | exact Gcv] | exact Gcb] ] | ]).
  first [ exact G | apply HPST; [unfold prh_pst; repeat (first [left; reflexivity | right]) | exact G] ].
- eapply Forall_impl; [|exact HB]. intros [a k] (Hk & Hb & Hhp & Hm & Hv). cbn [fst snd] in *.
  split; [exact Hk|]. split; [exact Hb|]. split; [exact Hhp|]. split; [exact Hm|].
  apply (pi_val_agr SEGS F _ _ _ _ _ HAG); [|exact Hv]. intros j Hj. apply HF.
  destruct (pil_blk_bnd ly S Hp W mem md _ _ HA Hb) as (Hb4 & Hbc).
  assert (Hr : 0 < req_size (k + cf_head)) by (apply pil_req_pos0; lia). lia.
Qed.

(* the cursor record survives a write that keeps the low memory (below alloc_ceiling + 8) and the cursor's 24 bytes *)
Lemma pil_cur_agr : forall F (regs0 : bvmap 5 word) e q v text len tb d ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 mem3 pc
  Lam2 peak2 cnt2 fail2 ran2 most2 own2,
  ARx ly2 S2 Hp2 W2 mem2 md2 -> 0 <= v -> v + 56 <= 2 ^ 47 -> 0 <= q -> q + 24 <= 2 ^ 47 ->
  (forall a, 0 <= a < YM05.alloc_ceiling + 8 -> F a) -> (forall a, q <= a < q + 24 -> F a) ->
  pi_agr F (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) mem3) ->
  pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb d ly2 S2 Hp2 W2 mem2 pc Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb d ly2 S2 Hp2 W2 mem3 pc Lam2 peak2 cnt2 fail2 ran2 most2 own2.
Proof.
intros F regs0 e q v text len tb d ly2 S2 Hp2 W2 mem2 md2 mem3 pc Lam2 peak2 cnt2 fail2 ran2 most2 own2 HA Hv0 Hv47 Hq0
  Hq47 HFlo HFq HAG
  (HIN & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof (@alloc_ceiling_lt rc) as Hac. pose proof (@ASAN_CEIL_range rc) as CR. unfold ASAN_CEIL in CR.
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & Hthv).
pose proof HIN as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG & Hdqt & Hd032).
assert (HSHF : forall x, 0 <= x < 2 ^ 47 -> F (shadow_of_addr SHADOW_OFF x))
  by (intros x Hx; apply HFlo; unfold shadow_of_addr, SHADOW_OFF; lia).
assert (Htxt : forall x, text <= x < text + Z.of_nat (length tb) -> F x) by (intros x Hx; apply HFlo; lia).
split.
{ split; [apply (pi_val_agr SEGS F _ _ _ _ _ HAG); [intros k Hk; apply HFq; lia | exact Vp]|].
  split; [apply (pi_val_agr SEGS F _ _ _ _ _ HAG); [intros k Hk; apply HFq; lia | exact Ve]|].
  split; [apply (pi_val_agr SEGS F _ _ _ _ _ HAG); [intros k Hk; apply HFq; lia | exact Vd]|].
  split; [apply (pi_rw_agr SEGS F _ _ _ _ HAG); [intros x Hx; apply HFq; lia | exact Hrw]|].
  split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|]. split; [exact Hple|]. split; [exact Hlen|].
  split; [apply (pi_garr8_agr SEGS F _ _ _ _ HAG); [exact Htxt | exact HG]|].
  split; [exact Hdqt | exact Hd032]. }
split.
{ apply (pil_ra_agr F _ mem2 mem3 q 24 HAG); [|exact HRA]. intros x Hx. apply HSHF. lia. }
split.
{ split; [apply (pi_garr8_agr SEGS F _ _ _ _ HAG); [exact Htxt | exact HGt]|].
  split; [exact Ht4|]. split; [exact Htc|]. split; [exact Htam|].
  split; [apply (pil_ra_agr F _ mem2 mem3 text _ HAG); [intros x Hx; apply HSHF; lia | exact Htra]|].
  intros Hpos. apply (pil_hull_agr F _ mem2 mem3 text _ HAG); [|exact (Hthv Hpos)].
  intros s0 Hs0. apply HFlo. unfold shadow_addr, SHADOW_OFF in Hs0. lia. }
split; [exact HHOME|]. split; [exact HPLAT|].
split.
{ apply (pil_ra_agr F _ mem2 mem3 v 56 HAG); [|exact HRAV]. intros x Hx. apply HSHF. lia. }
split; [exact (pil_ledger_agr F ly2 S2 Hp2 W2 mem2 md2 mem3 Lam2 peak2 cnt2 fail2 ran2 most2 own2 HA HFlo HAG HLG)
       | exact HCNT].
Qed.

(* the slot clause of pi_cont, as grow's text asks it *)
Lemma pil_slots_of_cont : forall m lblk (o : bool) v kids keys (n cap : nat) acc Di,
  pi_cont (L := Lb) (PA := PIb) m lblk o v kids keys n cap acc Di ->
  pj_slots_atR lblk (if o then 6 else 5) kids keys (Z.of_nat n) (Z.of_nat cap).
Proof.
intros m lblk o v kids keys n cap acc Di (Hh & Hn & Hle & H54 & Hsl & Hk0 & _).
unfold pj_slots_atR. split; [destruct o; lia|]. split; [lia|].
destruct Hsl as [(Hc0 & Hk & Hy) | (Hc & Hk & Hy)].
- split; [intros _; split; [exact Hk | intros _; exact Hy] | intros Hc; lia].
- split; [intros Hc0; lia|]. intros _. split; [exact Hk|]. intros H6. apply Hy. destruct o; [reflexivity | lia].
Qed.

Lemma pil_rest_ne : forall tb text p, text <= p < text + Z.of_nat (length tb) -> rest_atR tb text p <> [].
Proof.
intros tb text p H E. apply (f_equal (@length Z)) in E. unfold rest_atR in E. rewrite length_skipn in E.
cbn [length] in E. lia.
Qed.

(* a slot block is a block of the call state the entry did not have *)
Lemma pil_fp_sub : forall ly S lyc Sc Hpc (Wc : world SEGS) mm Lamc peakc cntc failc ranc mostc ownc (o : bool) q v kids
  keys (cap : nat) Di D0 STK sp0 own,
  prh_ledger (L := Lb) (PA := PIb) B lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc mostc ownc ->
  incl (pi_sblk o kids keys cap) Lamc -> Permutation D0 (pi_sblk o kids keys cap ++ Di) ->
  (forall a k, In (a, k) D0 -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) ->
  fp_sub_x B STK sp0 (rd_fp q v) (pil_fp1 o v kids keys cap) ly S own lyc Sc.
Proof.
intros ly S lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc mostc ownc o q v kids keys cap Di D0 STK sp0 own HL Hinc HP0 HB1
  a Ha.
destruct (pil_fp1_cases o v kids keys cap a Ha) as [Hv | (s & ks & Hs & Has)].
- left. exists (v, v + 56). split; [cbn [rd_fp In]; right; right; left; reflexivity | cbn [fst snd]; lia].
- right; left. exists (s - cf_head), (ks + cf_head).
  split; [exact (pil_slots_ab lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc mostc ownc o kids keys cap HL Hinc s ks Hs)|].
  split; [apply HB1; apply (Permutation_in _ (Permutation_sym HP0)); apply in_or_app; left; exact Hs | exact Has].
Qed.

(* grow's footprint lies below the ceiling *)
Lemma pil_fp1_low : forall lyc Sc Hpc (Wc : world SEGS) memc mm mdc Lamc peakc cntc failc ranc most own (o : bool) v kids
  keys (cap : nat),
  ARx lyc Sc Hpc Wc memc mdc ->
  prh_ledger (L := Lb) (PA := PIb) B lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own ->
  incl (pi_sblk o kids keys cap) Lamc -> v + 56 <= YM05.alloc_ceiling ->
  forall y, inFP (pil_fp1 o v kids keys cap) y -> y < YM05.alloc_ceiling.
Proof.
intros lyc Sc Hpc Wc memc mm mdc Lamc peakc cntc failc ranc most own o v kids keys cap HA HL Hinc Hvl y Hy.
destruct (pil_fp1_cases o v kids keys cap y Hy) as [Hv | (s & ks & Hs & Hys)]; [lia|].
pose proof (pil_slots_ab lyc Sc Hpc Wc mm Lamc peakc cntc failc ranc most own o kids keys cap HL Hinc s ks Hs) as HQ.
destruct (pil_blk_bnd lyc Sc Hpc Wc memc mdc _ _ HA HQ) as (_ & Hc). lia.
Qed.

(* a container's footprint lies below the ceiling *)
Lemma pil_foot_low : forall ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 v D,
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  prh_ledger (L := Lb) (PA := PIb) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  incl D Lam2 -> 0 <= v -> v + 56 <= YM05.alloc_ceiling ->
  forall x, pj_footR v D x -> 0 <= x < YM05.alloc_ceiling.
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 v D HA HL Hinc Hv0 Hvl x [Hx | ((a & k) & Hb & Hx)];
  [lia|].
unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
destruct (pil_lam_blk ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 a k HL (Hinc _ Hb)) as (Hk & HP & _).
destruct (pil_blk_bnd ly2 S2 Hp2 W2 mem2 md2 _ _ HA HP) as (H4 & Hc). pose proof (@cf_head_nonneg cp) as Hh.
assert (Hr : k + cf_head <= req_size (k + cf_head)) by (apply pil_req_ge0; lia). lia.
Qed.

(* the bytes pi_cont reads (PItems_value_model.v pvm_cont_ufoot: the node, the n member slots, an object's n key
   pointers, the members' blocks) lie below the ceiling *)
Lemma pil_ufoot_low : forall ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 m (o : bool) v kids
  keys (n cap : nat) acc Di,
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  prh_ledger (L := Lb) (PA := PIb) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  pi_cont (L := Lb) (PA := PIb) m (prh_lin Lam2) o v kids keys n cap acc Di ->
  incl Di Lam2 -> 0 <= v -> v + 56 <= YM05.alloc_ceiling ->
  forall x, pvm_cont_ufoot o v kids keys n Di x -> 0 <= x < YM05.alloc_ceiling.
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 m o v kids keys n cap acc Di HA HL HC Hinc Hv0 Hvl
  x Hx.
pose proof HC as (_ & _ & Hle & _ & Hsl & _).
pose proof (@cf_head_nonneg cp) as Hh.
assert (HB : forall a k, In (a, k) Lam2 -> 0 <= k /\ 4096 <= a - cf_head /\ a + k <= YM05.alloc_ceiling).
{ intros a k Hin.
  destruct (pil_lam_blk ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 a k HL Hin) as (Hk & HP & _).
  destruct (pil_blk_bnd ly2 S2 Hp2 W2 mem2 md2 _ _ HA HP) as (H4 & Hc).
  assert (Hr : k + cf_head <= req_size (k + cf_head)) by (apply pil_req_ge0; lia). lia. }
destruct Hx as [Hx | [(i & Hi & Hx) | [(Ho & i & Hi & Hx) | ((a & k) & Hb & Hx)]]].
- lia.
- destruct Hsl as [(Hc0 & _) | (Hcp & Hk & _)]; [lia|].
  destruct (HB _ _ Hk) as (_ & H4 & Hc). lia.
- destruct Hsl as [(Hc0 & _) | (Hcp & _ & Hy)]; [lia|].
  destruct (HB _ _ (Hy Ho)) as (_ & H4 & Hc). lia.
- unfold pj_holdsR in Hx. cbn [fst snd] in Hx. destruct (HB a k (Hinc _ Hb)) as (Hk & H4 & Hc). lia.
Qed.

Theorem pi_loop_holds : forall d CTX0 CW,
  (forall N, pi_body_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW N) ->
  pi_loop_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW.
Proof.
intros d CTX0 CW HBODY fxc fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
  lyc Sc Hpc Wc memc mdc k regs WS0 HJw HWS HPRE.
unfold pi_ajR in HJw.
(* THE BUDGETED JOURNAL, at wle' segs RZ_cf (grow frees): the runs and the (unbudgeted) grow call take
   the empty-budget journal rebased at this block's depot (YCbqGwild.ajournal_xw_rebaseR); HWD covers the moved depot's
   wild part, which every exit's step back to WS0 needs (ajournal_xw_unbase0R). Grow stores no wild trace, so the budget
   stays WS0. *)
pose proof (ajxR_wild HJw) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ.
pose proof HPRE as (HFP & HENT & HMNc & HFRM & HREGS & H21 & f & n & cap & acc & kids & keys & Di & pc & ok0 & tr0
  & D0 & Lamc & peakc & cntc & failc & ranc & HCUR & HCNT & HCONT & HDEP & HAP & HPERM & HFU & HEQ & HLED
  & HBLK & HPOSB & HLIVE & HBB & HOK & HLS & HROOM & HGRANT & HCAPN & HNCAPS & af & HFO & HFLE).
pose proof HENT as (Emn & Esec & E24 & Ein & Eclo & Ecent & Echn & Ecur & E10 & E11 & E12 & Egp & Etp & RDP & Eplt & Enth
  & Eroom & Efch & Efrm & Erod & Ecw & Ewr & Ehull).
pose proof RDP as (_ & _ & _ & _ & HIN0 & Hfwin & Hspq & Hqe & _ & HSRC0 & HHOME0 & _ & HPV & Hqv & Htv & Hvw & HL0
  & HdM & HCNT0 & Htxt).
pose proof HPV as (Hv4096 & Hv8 & _).
pose proof HFRM as (Fsp & F3 & F4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fwin & Fret & He0 & He16).
assert (Fsp' : spZ regs = spZ regs0 - 144) by (rewrite Fsp; reflexivity).
pose proof HREGS as (Q9 & Q19 & Q18 & Q8 & Q20 & Q26 & Q27 & Q25 & Q23).
pose proof HCUR as (HIN & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNTc).
pose proof HIN as (Vp & Ve & Vdp & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG0 & Hdqt & Hd032).
pose proof HIN0 as (_ & _ & _ & _ & _ & _ & _ & Hple0 & Hlen0 & _).
pose proof HLED as (Ho0 & Hc0 & Hfa0 & HPL & HPS & HLEN & HPK).
pose proof HBLK as (B1 & B2 & B3 & B4).
pose proof HJ as (HARc & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & Hastk & _ & _).
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as CH0.
pose proof (pil_stk_grow d) as HSTKB. pose proof pil_stk_grow_ge as HSTKG. pose proof (pi_frame_nonneg F_grow) as HGR0.
assert (Hsp4 : YM05.alloc_ceiling + 4096 <= spZ regs) by (unfold PI_FRAME in HSTKB; lia).
assert (Hinc : incl (pi_sblk o kids keys cap ++ Di) Lamc).
{ intros b Hb. apply (Permutation_in b (Permutation_sym HPL)). apply in_or_app. left.
  exact (Permutation_in b (Permutation_sym HPERM) Hb). }
assert (Hinc' : incl (pi_sblk o kids keys cap) Lamc) by (intros b Hb; apply Hinc; apply in_or_app; left; exact Hb).
assert (HND : NoDup (pi_sblk o kids keys cap ++ Di)).
{ pose proof HLG as HN. apply prh_ledger_nodup in HN. apply NoDup_ListNoDup. apply (Permutation_NoDup HPERM).
  apply NoDup_ListNoDup. apply (pis_nodup_l _ _ Lam). apply NoDup_ListNoDup.
  apply (Permutation_NoDup HPL). apply (NoDup_map_inv fst).
  first [exact HN | apply NoDup_ListNoDup; exact HN]. }
pose proof HCONT as (_ & _ & _ & _ & _ & _ & _ & HapD & _).
pose proof (pil_v_low lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc most own regs0 e v HARc HLG HPLAT Hvw) as Hvl.
destruct f as [|f']; [exfalso; lia|].
set (y := rest_atR tb text pc) in *.
pose proof (pil_gt_split f' (Nat.succ d) o n cap (rev acc) y) as HGS.
assert (HROOMg : rd_room Sc (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap) ++
  snd (fst (pi_jrb f' (Nat.succ d) o n (pil_gcap n cap) (rev acc) y [])))) by (rewrite <- HGS; exact HROOM).
(* tgrow_specX's two live-count premises at the call state: the entry's (pi_ent) along the whole call's granted
   events, cut at the loop head by the block's pi_live (PItems_value_model.v pvm_lc_call: K the loop's continuation, the
   jrl of pi_run_eq; T2 grow's granted trace, the prefix of K's by pil_gt_split), with grow's event list the model's
   (prhPg_evs_model at PIL_HEAD) *)
assert (HGEV : prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap) [] =
  PresetReqAt.rd_hevs (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap))).
{ rewrite pil_ty6. exact (prhPg_evs_model o (Z.of_nat n) (Z.of_nat cap) [] ltac:(lia) ltac:(lia) PIL_HEAD). }
assert (HT3 : exists T3, snd (fst (jrl prh_jr_strtod (Nat.succ f') (Nat.succ d) o n cap (rev acc) y [])) =
  PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap) ++ T3) by (eexists; exact HGS).
assert (HLSEC : Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
    (prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap) [])) <=
  PresetLiveBounds.LSEC + PresetLiveBounds.DRV).
{ rewrite HGEV.
  exact (pvm_lc_call YGcfRoomLive.rl_sec_req _ _ d o (rest_atR tb text p) ok0 tr0
    (jrl prh_jr_strtod (Nat.succ f') (Nat.succ d) o n cap (rev acc) y)
    (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap)) _ HEQ HOK HLIVE HT3 Esec). }
assert (HL24 : Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
    (prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap) [])) <=
  PresetLiveBounds.L24 + PresetLiveBounds.DRV).
{ rewrite HGEV.
  exact (pvm_lc_call (PresetRoom.in_cls YG00.kBatchClass) _ _ d o (rest_atR tb text p) ok0 tr0
    (jrl prh_jr_strtod (Nat.succ f') (Nat.succ d) o n cap (rev acc) y)
    (PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap)) _ HEQ HOK HLIVE HT3 E24). }
(* tgrow_specX's hull budget at the call state: the entry's (pi_ent's hull budget) over the call's all-granted events,
   split at the loop head as the live counts are (the prefix tr0, grow's granted trace, the member's rest:
   PItems_value_model.v pvm_gt_grant, pil_gt_split), paid by the block's hull use (PItems_posb.pi_posb_budget) *)
assert (HGT : PRH_Charge.prhPi_gtrace d o (rest_atR tb text p) =
  tr0 ++ PRH_Charge.prhPg_gtrace o (Z.of_nat n) (Z.of_nat cap) ++
    snd (fst (pi_jrb f' (Nat.succ d) o n (pil_gcap n cap) (rev acc) y []))).
{ unfold PRH_Charge.prhPi_gtrace.
  rewrite (pvm_gt_grant d o (rest_atR tb text p) ok0 tr0 (jrl prh_jr_strtod (Nat.succ f') (Nat.succ d) o n cap (rev acc) y)
    HEQ HGRANT).
  cbn [snd]. f_equal. exact HGS. }
assert (HHB : PresetHullBudget.hull_budget Sc (prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat n) (Z.of_nat cap) [])).
{ rewrite HGEV. rewrite HGT, !PresetReqAt.rd_hevs_app in Ehull.
  exact (PItems_posb.pi_posb_budget S Sc tr0 _ _ _ Ehull HPOSB eq_refl). }
(* ---- the run to the call: 0x87b70 `mv a0, s3`, 0x87b74 `jal grow` ---- *)
unfold pi_goalR, cfg_at.
remember (Eimg (PI := PIb) (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VALb A_LIM E) by (subst E; apply Eimg_env).
assert (EK : forall nk (rk : bv 5), Z.of_nat nk = bv_unsigned rk -> ew E nk = getr regs rk).
{ intros nk rk Hk. pose proof (bv_unsigned_in_range 5 rk) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs [] nk rk Hk). }
assert (HS : st_ok_pi (fx := fxc) SEGS VALb E (mkSS (PIATb PI_O_LOOP) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (@YK11.mkst fxc regs (Z_to_bv 64 (VALb A_TEXT + PIATb PI_O_LOOP)) memc (seg_rom SEGS)))).
{ rewrite (restrict_mkst_fx (fx := fxc)).
  apply (pa_entry_st_ok_full (fx := fxc) (L := Lb) (PI := PIb) E (PIATb PI_O_LOOP) sr_atoms regs []
    (mkFacts [] [] []) (mrestrict (w_H Wc) memc)).
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute; reflexivity.
  - constructor.
  - cbn; exact I.
  - repeat split; exact I. }
assert (SHOK : sh_ok SEGS (SLit 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
(* the runner that carries memnorm across the run (YC1fPx's _invR runner at YSRrMemnorm's memnorm laws, at wle') *)
pose (RUN := paj_run_x_invR (fx := fxc) (SK := SK) (L := Lb) (PL := PLb) (PI := PIb) B prh_pst ARx LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
change (w64 (VALb A_TEXT + PIATb PI_O_LOOP)) with (Z_to_bv 64 (VALb A_TEXT + PIATb PI_O_LOOP)).
pose proof HMNc as HPM.
paj_run_tok_x_inv RUN HS HJ SHOK HPM BAND_SPAN.
{ apply awr_ok_nil. }
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (8%bv : bv 5) R8.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
cbn [ss_mem] in HF, HFr.
assert (MEQ : mrestrict (w_H Wc) (ms_mem ms) = mrestrict (w_H Wc) memc).
{ apply functional_extensionality; intros x. apply HFr. intros (r & Hin & _). exact (in_nil Hin). }
clear HF HFr HG.
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & _). rewrite Hlen in Htc, Htam, Htra.
assert (Hq0 : YM05.alloc_ceiling <= q) by lia.
pose proof (pil_cur_rdeq regs0 e q v text len tb d lyc Sc Hpc Wc memc (ms_mem ms) pc Lamc peakc cntc failc ranc most own
  MEQ HCUR)
  as HCURm.
pose proof HCURm as (HINm & HRAm & HSRCm & _ & _ & HRAVm & HLGm & _).
assert (HCONTm : pi_cont (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamc) o v kids keys n cap acc Di)
  by (rewrite MEQ; exact HCONT).
assert (HNCAPSm : pi_ncaps (mrestrict (w_H Wc) (ms_mem ms)) kids acc) by (rewrite MEQ; exact HNCAPS).
assert (HFOm : pi_forder (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamc) o kids keys n Di acc af)
  by (rewrite MEQ; exact HFO).
pose proof HJ as (HARm & _).
assert (Usp : spZ (ms_regs ms) = spZ regs) by (unfold spZ; rewrite R2, (EK 2%nat 2%bv eq_refl); reflexivity).
assert (Us0 : s0Z (ms_regs ms) = q + 16).
{ unfold s0Z. rewrite R8, (EK 8%nat 8%bv eq_refl), Q8. apply unsigned_lit_small. lia. }
assert (Ra0 : getr (ms_regs ms) 10 = w64 v) by (rewrite R10, (EK 19%nat 19%bv eq_refl); exact Q19).
(* the chain the call sees from parse_items' s0 = q + 16 (as the KEY segment's skip_ws call) *)
assert (HCH : exists ch1, achain lyc (aview SEGS (w_H Wc) (ms_mem ms)) (spZ regs) (q + 16) ch1).
{ destruct (Z_lt_le_dec (q + 16) (ly_top lyc - 16)) as [Hlt | Hge].
  - exists [(q + 16, text + len, pc)]. right.
    split; [lia|]. split; [exact Hlt|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|].
    split.
    + cbn [fpchain]. split; [reflexivity|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|].
      split; [replace (q + 16 - 8) with (q + 8) by lia;
              apply (pil_rdword_of_val (w_H Wc) (ms_mem ms) (q + 8) (text + len)); [rewrite MEQ; exact Ve | lia]|].
      split; [replace (q + 16 - 16) with q by lia;
              apply (pil_rdword_of_val (w_H Wc) (ms_mem ms) q pc); [rewrite MEQ; exact Vp | lia]|].
      split; [lia|].
      unfold bad_next. replace (pc <=? q + 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    + constructor; [cbn [fst]; lia | constructor].
  - exists []. left. split; [right; left; lia | reflexivity]. }
destruct HCH as (ch1 & HCH).
(* the old slot arrays' bytes, when every slot is in use *)
assert (HKB : exists kb yb, n = cap -> bytes_at (L := Lb) (PA := PIb) Wc (ms_mem ms) kids kb /\
  Z.of_nat (length kb) = 56 * Z.of_nat cap /\
  (o = true -> bytes_at (L := Lb) (PA := PIb) Wc (ms_mem ms) keys yb /\ Z.of_nat (length yb) = 8 * Z.of_nat cap)).
{ pose proof HCONT as (_ & _ & _ & _ & Hsl & _).
  destruct Hsl as [(Hc00 & Hk00 & Hy00) | (Hcp & Hkin & Hyin)].
  - exists [], []. intros _. rewrite Hc00. cbn. split; [intros j Hj; cbn in Hj; lia|]. split; [lia|].
    intros _. split; [intros j Hj; cbn in Hj; lia | lia].
  - destruct (pil_lam_bytes lyc Sc Hpc Wc (ms_mem ms) _ Lamc peakc cntc failc ranc most own kids (56 * Z.of_nat cap)
      HARm HLGm Hkin) as (kb & Hkb & Hlkb).
    destruct o.
    + destruct (pil_lam_bytes lyc Sc Hpc Wc (ms_mem ms) _ Lamc peakc cntc failc ranc most own keys (8 * Z.of_nat cap)
        HARm HLGm (Hyin eq_refl)) as (yb & Hyb & Hlyb).
      exists kb, yb. intros _. split; [exact Hkb|]. split; [exact Hlkb|]. intros _. split; [exact Hyb | exact Hlyb].
    + exists kb, []. intros _. split; [exact Hkb|]. split; [exact Hlkb|]. intros C. discriminate C. }
destruct HKB as (kb & yb & HKB).
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (aj_call_xW_spR (SK := SK) SEGS B prh_pst ARx LAWS (pa_segs_low (PAImg := PIb))
    (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc E _ ms
    (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v) ly _ Hp W mem md [] lyc Sc Hpc _ k
    STK_grow (PI_FRAME + e) (pil_fp1 o v kids keys cap) (- (PI_FRAME + e)) _ ch1
    (fQmn (ms_mem ms) (pil_gpost B (if o then 6 else 5) 0 0 v kids keys
       (Z.of_nat n) (Z.of_nat cap) kb yb lyc Sc Hpc Wc (ms_mem ms) Lamc peakc cntc failc ranc most own))
    HS eq_refl HJ).
  - rewrite Usp, Fsp. unfold PI_FRAME. lia.
  - unfold PI_FRAME. rewrite Z.mod_opp_l_z; [reflexivity | lia | rewrite Z.add_mod, He16 by lia; reflexivity].
  - unfold PI_FRAME. lia.
  - pose proof HSTKG. lia.
  - unfold PI_FRAME in *. lia.
  - unfold PI_FRAME. lia.
  - unfold PI_FRAME. rewrite Z.add_mod, He16 by lia; reflexivity.
  - lia.
  - rewrite R3, (EK 3%nat 3%bv eq_refl), F3. exact Egp.
  - rewrite R4, (EK 4%nat 4%bv eq_refl), F4. exact Etp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - pose proof (pa_B_ok (PAImg := PIb)) as HB. pose proof (pa_val_range (PAImg := PIb) A_TEXT) as HBr.
    rewrite unsigned_lit_small by lia. vm_compute. discriminate.
  - replace (spZ regs0 + e + - (PI_FRAME + e)) with (spZ regs) by (unfold PI_FRAME; lia). rewrite Us0. exact HCH.
  - intros HAF HWIN. cbv [ss_pc setpc].
    refine (TGROW fxc CTX0 most own lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ ch1
      (PI_FRAME + e) v (if o then 6 else 5) 0 0 kids keys (Z.of_nat n) (Z.of_nat cap) kb yb Lamc peakc cntc failc ranc
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + split; [exact HAF|]. split.
      { apply (pil_rod_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); [|exact Erod].
        intros (r & Hr & H0). cbn [rd_fp In] in Hr.
        destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in H0; lia. }
      split; [pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _); rewrite Usp; lia|].
      (* fpre's return-address bound: the return site 0x87b78 is a text address, below CEIL_MIN; and its rounding
         mode at entry (FRM0-ENTRY): the pre's pi_fpok at the current float state *)
      split; [|exact (proj1 HFP)].
      unfold raZ. rewrite R1. pose proof (@YM05.alloc_ceiling_val rc) as ((HCm & _) & _).
      eapply Z.lt_le_trans; [| exact HCm]. vm_compute. reflexivity.
    + exact Eclo.
    + exists []. rewrite pil_s0g. apply achain_low. lia.
    + exact (proj1 HROOM).
    + exact HLSEC.
    + exact HL24.
    + exact HHB.
    + exact Ra0.
    + lia.
    + exact Hv8.
    + pose proof HCONTm as (Hh0 & _). exact Hh0.
    + exact (pil_slots_of_cont _ _ o v kids keys n cap acc Di HCONT).
    + exact HAP.
    + exact HWIN.
    + apply (pil_at_widen lyc Sc Lamc regs0 (ms_regs ms) e v); [rewrite Usp; exact Fsp' | exact He0 | exact HPLAT].
    + exact HRAVm.
    + intros Hnc. pose proof (HKB ltac:(lia)) as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
      intros H6. destruct o; [exact (H3 eq_refl) | discriminate H6].
    + exact HLGm.
    + lia.
    + intros Hnc. exact (pil_grow_room o n cap _ Sc ltac:(lia) HROOMg).
  - exact (pil_fp_sub ly _ lyc Sc Hpc Wc (ms_mem ms) Lamc peakc cntc failc ranc most own o q v kids keys cap Di D0
      (STK_parse_items d + e) (spZ regs0 + e) [] HLGm Hinc' HPERM B1). }
(* ---- back at the return site 0x87b78 ---- *)
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HX & HP & HK & HKmn).
replace (spZ regs0 + e + - (PI_FRAME + e)) with (spZ regs0 - PI_FRAME) in HJ1, HX by (unfold PI_FRAME; lia).
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  assert (KREG : forall (r : bv 5), sr_get (ss_regs ssx) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
    getr (ms_regs msx) r = getr regs r)
end.
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms r HS), Hr. cbn [sv_denot].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply EK. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  unfold bv_modulus in Hr5. cbn in Hr5. lia. }
assert (HKS : aregs_preserved regs regs2).
{ intros r Hr. rewrite (HP r Hr). unfold acallee_saved in Hr.
  assert (Hc : In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) by (cbn [In]; lia).
  repeat (destruct Hc as [<- | Hc]; [apply KREG; vm_compute; reflexivity |]). destruct Hc. }
assert (G9 : getr regs2 9 = w64 q) by (rewrite <- Q9; exact (HKS 9 ltac:(unfold acallee_saved; lia))).
assert (G8 : getr regs2 8 = w64 (q + 16)) by (rewrite <- Q8; exact (HKS 8 ltac:(unfold acallee_saved; lia))).
assert (G18 : getr regs2 18 = w64 (if o then 1 else 0)) by (rewrite <- Q18; exact (HKS 18 ltac:(unfold acallee_saved; lia))).
assert (G19 : getr regs2 19 = w64 v) by (rewrite <- Q19; exact (HKS 19 ltac:(unfold acallee_saved; lia))).
assert (G20 : getr regs2 20 = w64 (q + 8)) by (rewrite <- Q20; exact (HKS 20 ltac:(unfold acallee_saved; lia))).
assert (G21 : getr regs2 21 = w64 (-1)) by (rewrite <- H21; exact (HKS 21 ltac:(unfold acallee_saved; lia))).
assert (G23 : getr regs2 23 = w64 (pi_sh (q + 8))) by (rewrite <- Q23; exact (HKS 23 ltac:(unfold acallee_saved; lia))).
assert (G25 : getr regs2 25 = w64 (pi_sh (q + 16))) by (rewrite <- Q25; exact (HKS 25 ltac:(unfold acallee_saved; lia))).
assert (G26 : getr regs2 26 = w64 SHADOW_OFF) by (rewrite <- Q26; exact (HKS 26 ltac:(unfold acallee_saved; lia))).
assert (G27 : getr regs2 27 = w64 (pi_sh q)) by (rewrite <- Q27; exact (HKS 27 ltac:(unfold acallee_saved; lia))).
assert (G2 : getr regs2 2 = getr regs 2) by exact (HKS 2 ltac:(unfold acallee_saved; lia)).
assert (G3' : getr regs2 3 = getr regs 3) by exact (HKS 3 ltac:(unfold acallee_saved; lia)).
assert (G4' : getr regs2 4 = getr regs 4) by exact (HKS 4 ltac:(unfold acallee_saved; lia)).
assert (Rsp2 : spZ regs2 = spZ regs) by (unfold spZ; rewrite G2; reflexivity).
pose proof HJ1 as (HAR2 & _ & _ & _ & _ & Hfr1 & _). cbn [app] in Hfr1.
pose proof HJ2 as (_ & HLY2 & _).
pose proof HLY2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo2 & Eshi2 & _).
pose proof (@alloc_ceiling_lt rc) as Hac.
assert (Hlen0' : 0 < len) by lia.
pose proof HL0 as Hcnt64. apply prh_ledger_bounds in Hcnt64. destruct Hcnt64 as (_ & _ & Hcnt64 & _).
assert (HFL := pil_fp1_low lyc Sc Hpc Wc (ms_mem ms) (ms_mem ms) _ Lamc peakc cntc failc ranc most own o v kids keys cap
  HARm HLGm Hinc' Hvl).
(* ---- the grow step: the model's grow and the ledger move, on every arm of grow's post ---- *)
pose proof (pil_grow_step B ARx LAWS PIL_HEAD) as STEP. unfold pil_grow_step_stmt in STEP.
assert (HOUT := STEP ly S d o tb text len p q v e regs0 Lam peak cnt fail ran most own kr lyc Sc Hpc Wc (ms_mem ms)
  (Nat.succ f') n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc af kb yb ly2 S2 Hp2 W2 regs2 mem2 md2
  HPM HCURm HCNT HCONTm HDEP HAP HPERM HFU HEQ
  (pil_rest_ne tb text p ltac:(lia)) ltac:(lia) HLED HBLK HPOSB HLIVE HBB HOK HLS HROOM HGRANT HCAPN HNCAPSm HFOm HFLE
  HKB HK HKmn
  (pil_kdi _ lyc Sc Hpc Wc (ms_mem ms) (ms_mem ms) _ Lamc peakc cntc failc ranc most own o v kids keys cap Di _ _ ly2 S2
     Hp2 W2 mem2 md2 k1 HARm HLGm Hinc HND HapD HJ1)
  HAR2
  (pil_newv _ lyc Sc Hpc Wc (ms_mem ms) (ms_mem ms) _ Lamc peakc cntc failc ranc most own regs0 e o v kids keys cap _ _ ly2
     S2 Hp2 W2 mem2 md2 k1 HARm HLGm Hinc' HAP HPLAT Hvw HJ1)
  (pil_kcur _ ly S Hp W mem Lam peak cnt fail ran most own regs0 e q v text len tb d lyc Sc Hpc Wc (ms_mem ms) _ pc Lamc
     peakc cntc failc ranc o kids keys cap Di D0 (spZ regs0 - PI_FRAME) ly2 S2 Hp2 W2 mem2 md2 k1 HL0 HHOME0 Hlen0'
     (Htv Hlen0')
     Hvw Hspq Hqe ltac:(lia) HARm HCURm HPERM B1 B2 Hinc' HAP eq_refl He0 HJ1 HX ltac:(lia) ltac:(lia))
  ltac:(rewrite Hfr1; apply Permutation_refl)).
(* ---- the return site ---- *)
lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
  replace pcw with (w64 (VALb A_TEXT + PIATb PIL_O_RET)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
assert (Hneg : w64 0 <> w64 (-1)) by (intros C; apply (f_equal bv_unsigned) in C; vm_compute in C; discriminate C).
assert (WIN : forall mem3, (forall a, spZ regs + 40 <= a < spZ regs0 + e -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  forall a, spZ regs + 40 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H Wc) memc a).
{ intros mem3 H3 a Ha Hn. rewrite (H3 a Ha). rewrite HX; [| unfold PI_FRAME; lia | intros Hf; pose proof (HFL a Hf); lia].
  exact (pil_aview_mr _ _ _ a MEQ). }
apply (pil_ret_run fxc d e regs0 q v ly _ Hp W mem md ly2 S2 Hp2 W2 mem2 md2 (k + k1) regs2 _ HJ2).
- rewrite Rsp2. lia.
- rewrite Rsp2, Fsp'. lia.
- rewrite Rsp2, Fsp'. lia.
- rewrite Rsp2. exact Fsp'.
- exact He0.
- unfold PI_FRAME in *. lia.
- exact G19.
- exact G26.
- lia.
- lia.
- exact (HKmn HPM).
- (* TAKEN: grow refused; the kit's None arm at the epilogue *)
  intros HNZ regs3 mem3 md3 k3 HJ3 HMN3 MEQ3 Rsp3 R3x R4x R21x.
  destruct HOUT as [(H10 & _) | (H10 & _ & HPOST)]; [exfalso; exact (HNZ H10)|].
  apply (pil_epi_exit d (YCbqGwild.wbudget CW 0) fxc fx0 ly S Hp W mem md regs0 e q v o tb text len p Lam peak cnt fail
    ran most own kr ly2 S2 Hp2 W2 mem3 md3 k3 regs3 WS0
    (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
       _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HWD) HWS
    HFP HMN3).
  + apply (pil_frame_win regs0 regs regs3 W mem Wc W2 memc mem3 e q v HFRM).
    * rewrite Rsp3. exact Rsp2.
    * rewrite R3x. exact G3'.
    * rewrite R4x. exact G4'.
    * exact Hspq.
    * left; lia.
    * apply WIN. intros a Ha. exact (pil_aview_mr _ _ _ a MEQ3).
  + rewrite R21x. exact G21.
  + intros regs' H10'.
    apply (pil_post_stable ly S d o tb text len p q v Lam peak cnt fail ran most own kr
      ly2 S2 Hp2 W2 regs' mem2 mem3 md2 md3);
      [intros x; rewrite MEQ3; reflexivity | exact (HPOST regs' md2 H10')].
- (* NOT TAKEN: grow returned 0; the frame cache, then PI_O_BODY *)
  intros HZ regs3 mem3 md3 k3 HJ3 HMN3 KK3 K22 K24 AGR V0 V32 V24 V16 V8.
  destruct HOUT as [(_ & _ & f2 & cap' & kids' & keys' & ok0' & tr0' & D0' & Lam' & peak' & cnt' & fail' & ran' & Ef & HCUR2
    & Hncap2 & HCONT2 & HDEP2 & HAP2 & HPERM2 & HFU2 & HEQ2 & HLED2 & HBLK2 & HPOSB2 & HLIVE2 & HBB2 & HOK2 & HLS2
    & HROOM2 & HGRANT2 & HCAPN2 & HNCAPS2 & af2 & HFO2 & HFL2) | (H10 & _)];
    [| exfalso; rewrite HZ in H10; exact (Hneg H10)].
  assert (KK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 25; 26; 27]%bv -> getr regs3 r = getr regs2 r)
    by exact KK3.
  assert (Rsp3 : spZ regs3 = spZ regs2) by (unfold spZ; rewrite (KK 2%bv); [reflexivity | repeat (first [left; reflexivity | right])]).
  assert (HFlo : forall a, 0 <= a < YM05.alloc_ceiling + 8 -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs2 <= a < spZ regs2 + 40))
    by (intros a Ha; split; [lia | rewrite Rsp2; lia]).
  assert (HFq : forall a, q <= a < q + 24 -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs2 <= a < spZ regs2 + 40))
    by (intros a Ha; split; [lia | rewrite Rsp2, Fsp'; lia]).
  pose proof HCUR2 as (_ & _ & _ & _ & _ & _ & HLG2 & _).
  pose proof HLED2 as (_ & _ & _ & HPL2 & _).
  assert (Hinc2 : incl (pi_sblk o kids' keys' cap' ++ Di) Lam').
  { intros b Hb. apply (Permutation_in b (Permutation_sym HPL2)). apply in_or_app. left.
    exact (Permutation_in b (Permutation_sym HPERM2) Hb). }
  (* The batch kit's invariants across the cache stores: they write only [sp, sp + 40), above every byte pi_cont reads *)
  assert (HAGRu : pj_agreeR SEGS (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) mem3)
    (pvm_cont_ufoot o v kids' keys' n Di)).
  { intros x Hx.
    pose proof (pil_ufoot_low ly2 S2 Hp2 W2 mem2 md2 Lam' peak' cnt' fail' ran' most own _ o v kids' keys' n cap' acc Di
      HAR2 HLG2 HCONT2 (fun b Hb => Hinc2 b (in_or_app _ _ _ (or_intror Hb))) ltac:(lia) Hvl x Hx) as Hxl.
    assert (Fx : 0 <= x < 2 ^ 64 /\ ~ (spZ regs2 <= x < spZ regs2 + 40)) by (split; [lia | rewrite Rsp2; lia]).
    split; [unfold mbyte; rewrite (AGR x Fx); reflexivity|].
    intros Hw. exact (pi_wr_agr SEGS _ _ _ x AGR Fx Hw). }
  apply (HBODY (length (rest_atR tb text pc)) fxc fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt
    fail ran most own kr ly2 S2 Hp2 W2 mem3 md3 k3 regs3 WS0).
  + unfold pi_ajR.
    exact (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HWD).
  + exact HWS.
  + split; [exact HFP|]. split; [exact HENT|]. split; [exact HMN3|].
    split.
    { apply (pil_frame_win regs0 regs regs3 W mem Wc W2 memc mem3 e q v HFRM).
      - rewrite Rsp3. exact Rsp2.
      - rewrite (KK 3%bv); [exact G3' | repeat (first [left; reflexivity | right])].
      - rewrite (KK 4%bv); [exact G4' | repeat (first [left; reflexivity | right])].
      - exact Hspq.
      - left; lia.
      - apply WIN. intros a Ha. apply (pil_aview_agr _ _ mem2 mem3 a AGR). split; [lia | rewrite Rsp2; lia]. }
    split.
    { unfold pi_regs.
      rewrite (KK 9%bv), (KK 19%bv), (KK 18%bv), (KK 8%bv), (KK 20%bv), (KK 26%bv), (KK 27%bv), (KK 25%bv), (KK 23%bv);
        try (repeat (first [left; reflexivity | right])).
      repeat split; assumption. }
    split.
    { unfold pi_regs_body. rewrite Rsp3. split; [exact K22|]. split; [exact K24|].
      split; [exact V0|]. split; [exact V32|]. split; [exact V24|]. split; [exact V16 | exact V8]. }
    split; [rewrite (KK 21%bv); [exact G21 | repeat (first [left; reflexivity | right])]|].
    exists f2, n, cap', acc, kids', keys', Di, pc, ok0', tr0', D0', Lam', peak', cnt', fail', ran'.
    split.
    { apply (pil_cur_agr (fun a => 0 <= a < 2 ^ 64 /\ ~ (spZ regs2 <= a < spZ regs2 + 40)) regs0 e q v text len tb d
        ly2 S2 Hp2 W2 mem2 md2 mem3 pc Lam' peak' cnt' fail' ran' most own HAR2);
        first [exact AGR | exact HCUR2 | exact HFlo | exact HFq | lia]. }
    split; [lia|]. split; [exact Hncap2|].
    split.
    { apply (pi_cont_frame (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) mem3) (prh_lin Lam') o v kids' keys' n cap' acc Di
        HCONT2).
      intros x Hx.
      pose proof (pil_foot_low ly2 S2 Hp2 W2 mem2 md2 Lam' peak' cnt' fail' ran' most own v _ HAR2 HLG2 Hinc2 ltac:(lia)
        Hvl x Hx)
        as Hxl.
      assert (Fx : 0 <= x < 2 ^ 64 /\ ~ (spZ regs2 <= x < spZ regs2 + 40)) by (split; [lia | rewrite Rsp2; lia]).
      split; [unfold mbyte; rewrite (AGR x Fx); reflexivity|].
      intros Hw. exact (pi_wr_agr SEGS _ _ _ x AGR Fx Hw). }
    split; [exact HDEP2|]. split; [exact HAP2|]. split; [exact HPERM2|]. split; [exact HFU2|]. split; [exact HEQ2|].
    split; [exact HLED2|]. split; [exact HBLK2|]. split; [exact HPOSB2|]. split; [exact HLIVE2|].
    split; [exact HBB2|]. split; [exact HOK2|].
    split; [exact HLS2|]. split; [exact HROOM2|].
    split; [exact HGRANT2|]. split; [exact HCAPN2|].
    split; [exact (pvm_ncaps_frame (w_H W2) mem2 (mrestrict (w_H W2) mem3) (prh_lin Lam') o v kids' keys' n cap' acc Di
      HCONT2 HNCAPS2 HAGRu)|].
    exists af2. split; [|exact HFL2].
    exact (pvm_forder_frame (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) mem3) (prh_lin Lam') (prh_lin Lam') o v kids'
      keys' n Di acc af2 HFO2 (fun _ _ H => H) HAGRu).
Qed.

End body.

(* the closures of this file's two top lemmas (no Axiom of the development, no Admitted) *)
Print Assumptions pi_loop_holds.
Print Assumptions pil_grow_step.
