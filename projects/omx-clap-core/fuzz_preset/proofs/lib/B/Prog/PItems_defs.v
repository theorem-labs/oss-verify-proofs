(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_entry.v, with its module paths and module names changed; 301 of its 347 lines of code are new or changed and 1519 lines of the source are left out. *)
(* Theorem Labs, 2026-10: the shared layer of parse_items' image-B walk: the block offsets of the body, the Section
   every segment file opens, the run / branch / kept tactics, and
   the small kept-memory lemmas. No segment lemma and no walk is here.
   LISTING: the whole-range image-B listing, lib/B/Listing_prog.v + PAImg_prog.v
   (Listing_prog.v (sha256 066bcdad7974; internal record) / PAImg_prog.v (sha256 c718279e6395; internal record), made with pg-tools tools/pau-listing/
   mklisting.py (sha256 f9c5f7b1b975; internal record); 7,484 B slots, checker 0 failing). The walk states over {L} {PL} {PI} and the top instantiates with
   B_prog_listing / PL_prog_B / PI_prog_B, both passed explicitly.
   ENGINE: YC1fPx's paj_run_x / paj_run_to_x (YC80x's runner over YCbqG's ajournal_x), as the leaf walks use
   YC1fP's; the tactic wrappers below are lib/B/Prog/skip_ws_x.v's
   (skip_ws_x.v (sha256 4fd6abc9040c; internal record)) in the pi form, and the four kept lemmas are that file's, unchanged but for the listing's segments.
   OFFSETS: every pc is the listing offset of the function's entry plus a byte offset INSIDE the body, so no numeral
   here is an ADDRESS: pa_sigma AS_parse_items is the only image number, and it comes from the listing.
   Numerals: the PI_O_* offsets are LENGTH (byte offsets inside one 1,732-byte body, read off the neutral listing
   the internal file parse_items.fuzz_preset.asan-ubsan.s); 8, 16, 24, 40, 56, 144 are
   structure / frame LENGTHs; 2 ^ 64 is DERIVED. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YC80xf YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YI00 YI04 YI16 YK06 YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun PresetRoom PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
(* the travelling run position and live requests of this walk (the post-implication form (b)) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_posb.
(* THE RE-HIDING MOVE and THE HULL (route (b)): the walk runs at the world relation wle' segs RZ_cf (YA0nH; preset's
   zone YGcfRehidePost.RZ_cf), since its callees free; the R runners and the branch over R (YC1fPx, YC80xf, YSRrG);
   the entry's hull budget (PresetHullBudget) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the copied cgif core files turn the Euclidean-division equations OFF globally; this file and every segment file
   that reasons about / or mod sets the flag itself (23:38Z) *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* THE TEXT this walk proves is the kit's lib/A/PRH_FnParse.v `tparse_items_specX (d : nat) (CTX : list (list Z))`
   (as an earlier kit states it, the reading chain's POST-IMPLICATION form (b)): the caller-window float post fpostWFm
   at window e, FP = rd_fp q v, the premises bundled in rd_pre (with the ledger's g_most / g_own_ran_out cells, most
   and own), the model PjGrammar.jr_items over prh_jr_strtod, no entry position; the post states the position
   transfer and the live requests over the instance's trace tr.
   THE WINDOW-FORM CALL RULE is lib/A/Prog/PRW_CallerJ.v (taken by path at
   PRW_CallerJ.v (sha256 f850efcb519e; internal record); as stated 23:44Z: the rule has an owner and is imported,
   never rewritten): fwin_x, fpostW_x, fpostWF_x, cj_kept / cj_kept_refl / cj_kept_of_journal / cj_kept_trans /
   cj_kept_exec, ajournal_x_init_W (the entry journal widened to the caller window), ajournal_x_sub_W and
   aj_call_xW (a call whose callee concludes in the window post). The float twins aj_call_xF / aj_call_xWF are
   YCbqGcall.v's (patch the internal file kit-aj_call_xF.patch); a segment that calls parse_value needs
   aj_call_xWF and carries it as a Section hypothesis with that exact text until it lands. *)

(* ---- the blocks of the body, as byte offsets from the entry (the neutral listing of image B) ---- *)
Definition PI_O_ENTRY : Z := 0.          (* 0x87a38 prologue, the node and depth checks *)
Definition PI_O_SKW0 : Z := 0xe8.        (* jal skip_ws, the first one (after in->p++) *)
Definition PI_O_HEAD : Z := 0xec.        (* back from it: the empty-container test *)
Definition PI_O_LOOP : Z := 0x138.       (* the member loop's head: grow (v) *)
Definition PI_O_BODY : Z := 0x184.       (* back from grow, the shadow-address cache written *)
Definition PI_O_KEY : Z := 0x188.        (* the object key: skip_ws, the quote test, parse_string, the colon *)
Definition PI_O_PSTR : Z := 0x1d4.       (* jal parse_string *)
Definition PI_O_VAL : Z := 0x2a0.        (* the kid slot: the two bound checks and the memset *)
Definition PI_O_MSET : Z := 0x2fc.       (* jal checked_memset *)
Definition PI_O_PVAL : Z := 0x35c.       (* jal parse_value *)
Definition PI_O_AFTV : Z := 0x360.       (* back from it: v->n++, skip_ws, the ',' test *)
Definition PI_O_SKW2 : Z := 0x380.       (* jal skip_ws, the one after a value *)
Definition PI_O_GROW2 : Z := 0x3dc.      (* jal grow, the one after a ',' *)
Definition PI_O_CLS0 : Z := 0x40c.       (* the array closer test of the empty-container path *)
Definition PI_O_CLOSE : Z := 0x414.      (* the closer: in->p++, in->depth--, res = 0 *)
Definition PI_O_EPI : Z := 0x450.        (* the epilogue: a0 = res, restore, ret *)
Definition PI_O_FREE : Z := 0x490.       (* the missing-colon path: free the key just read *)
Definition PI_O_FFREE : Z := 0x4f8.      (* jal fuzz_free in that path *)
Definition PI_O_CLS1 : Z := 0x500.       (* the closer test after a value (B's duplicate close block) *)
Definition PI_O_TRAP : Z := 0x568.       (* the one `unimp`: every UBSan check branches here *)
Definition PI_O_END : Z := 0x6c4.        (* one past the last instruction of the body (0x6c0, the jal to
                                            errpath_store8): the entry of parse_string, 0x880fc - 0x87a38 *)

(* the stack frame of image B's parse_items: `addi sp, sp, -144` at the entry *)
Definition PI_FRAME : Z := 144.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section g.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
(* the listing offset of the entry, and of each block *)
Definition PI_AT (o : Z) : Z := pa_sigma AS_parse_items - BASE + o.

Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.  (* AR_laws_x's head length (the engine fold, YCbqG.v (sha256 a9125950ebd4; internal record)): cf_head at the instance *)
Hypothesis LAWS : AR_laws_x pa_segs B ARx HL.
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img pa_segs a /\ ~ Exists (in_zr a) (as_owned_static B).

(* the runners the segment files use: RUN steps to the next stop, RUNTO to a named offset *)
Definition PI_RUN := @paj_run_x fx rc SK L PL PI B PST ARx HL LAWS.
Definition PI_RUNTO := @paj_run_to_x fx rc SK L PL PI B PST ARx HL LAWS.
Definition PI_RUNM := @paj_run_x_m fx rc SK L PL PI B PST ARx HL LAWS PST_ok.
Definition PI_RUNTOM := @paj_run_to_x_m fx rc SK L PL PI B PST ARx HL LAWS PST_ok.
(* the CALLER-FRAME runners (YC80xf.v): a run that stores into the node v must use these, because v
   may lie in a caller's fake frame (prhReader_at's third case) and only awr_ok_fr (= awr_byte \/ wr_fp_frame FP)
   admits such a store (caught 01:0xZ) *)
Definition PI_RUNF := @paj_run_xf fx rc SK L PL PI B PST ARx HL LAWS.
Definition PI_RUNTOF := @paj_run_to_xf fx rc SK L PL PI B PST ARx HL LAWS.
Definition PI_RUNMF := @paj_run_xmf fx rc SK L PL PI B PST ARx HL LAWS PST_ok.
Definition PI_RUNTOMF := @paj_run_to_xmf fx rc SK L PL PI B PST ARx HL LAWS PST_ok.
(* THE RUNNERS OVER THE WALK'S RELATION wle' pa_segs RZ_cf (YC1fPx.v / YC80xf.v R forms at R := wle'): the same
   binders, the journal at wle', the conclusion YA0nH.SRr' pa_segs RZ_cf; pi_run / pi_run_to drive them unchanged *)
Definition PI_RUNR := @paj_run_xR fx rc SK L PL PI B PST ARx HL LAWS (wle' pa_segs YGcfRehidePost.RZ_cf)
  (wle'_refl pa_segs YGcfRehidePost.RZ_cf) (wle'_trans pa_segs YGcfRehidePost.RZ_cf).
Definition PI_RUNTOR := @paj_run_to_xR fx rc SK L PL PI B PST ARx HL LAWS (wle' pa_segs YGcfRehidePost.RZ_cf)
  (wle'_refl pa_segs YGcfRehidePost.RZ_cf) (wle'_trans pa_segs YGcfRehidePost.RZ_cf).
Definition PI_RUNMR := @paj_run_x_mR fx rc SK L PL PI B PST ARx HL LAWS PST_ok (wle' pa_segs YGcfRehidePost.RZ_cf)
  (wle'_refl pa_segs YGcfRehidePost.RZ_cf) (wle'_trans pa_segs YGcfRehidePost.RZ_cf).
Definition PI_RUNTOMR := @paj_run_to_x_mR fx rc SK L PL PI B PST ARx HL LAWS PST_ok (wle' pa_segs YGcfRehidePost.RZ_cf)
  (wle'_refl pa_segs YGcfRehidePost.RZ_cf) (wle'_trans pa_segs YGcfRehidePost.RZ_cf).
Definition PI_RUNFR := @paj_run_xfR fx rc SK L PL PI B PST ARx HL LAWS (wle' pa_segs YGcfRehidePost.RZ_cf)
  (wle'_refl pa_segs YGcfRehidePost.RZ_cf) (wle'_trans pa_segs YGcfRehidePost.RZ_cf).
Definition PI_RUNTOFR := @paj_run_to_xfR fx rc SK L PL PI B PST ARx HL LAWS (wle' pa_segs YGcfRehidePost.RZ_cf)
  (wle'_refl pa_segs YGcfRehidePost.RZ_cf) (wle'_trans pa_segs YGcfRehidePost.RZ_cf).
Definition PI_RUNMFR := @paj_run_xmfR fx rc SK L PL PI B PST ARx HL LAWS PST_ok (wle' pa_segs YGcfRehidePost.RZ_cf)
  (wle'_refl pa_segs YGcfRehidePost.RZ_cf) (wle'_trans pa_segs YGcfRehidePost.RZ_cf).
Definition PI_RUNTOMFR := @paj_run_to_xmfR fx rc SK L PL PI B PST ARx HL LAWS PST_ok
  (wle' pa_segs YGcfRehidePost.RZ_cf) (wle'_refl pa_segs YGcfRehidePost.RZ_cf) (wle'_trans pa_segs YGcfRehidePost.RZ_cf).

(* ---- the kept-memory lemmas (skip_ws_x.v (sha256 4fd6abc9040c; internal record), over this listing's segments) ---- *)
Lemma pi_kept : forall E rs H (m m' : word -> option byte) (Zs : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Zs HFR Hw a Ha Hn. apply (aview_eq_of SEGS). apply HFR. rewrite unsigned_lit_small by lia.
intros Hin. destruct (in_wrange_windows E rs a Hin) as (b & wlo & whi & Hi & Hr). exact (Hn (Hw b wlo whi a Hi Hr)).
Qed.

Lemma pi_garr8_kept : forall H (m m' : word -> option byte) p Ls,
(forall a, p <= a < p + Z.of_nat (length Ls) -> aview SEGS H m' a = aview SEGS H m a) ->
garr8 SEGS (mrestrict H m) p Ls -> garr8 SEGS (mrestrict H m') p Ls.
Proof.
intros H m m' p Ls HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. cbn in Hk. rewrite (mbyte_of_aview SEGS H H m m' (p + Z.of_nat j + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.

Lemma pi_val_kept : forall H (m m' : word -> option byte) a n v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS H m' x = aview SEGS H m x) ->
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' a n v HE Hv kk Hk. rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.

Lemma pi_ra_kept : forall H (m m' : word -> option byte) a n,
(forall x, a <= x < a + n -> aview SEGS H m' (shadow_of_addr SHADOW_OFF x) = aview SEGS H m (shadow_of_addr SHADOW_OFF x)) ->
range_addressable (aview SEGS H m) SHADOW_OFF a n -> range_addressable (aview SEGS H m') SHADOW_OFF a n.
Proof. intros H m m' a n HE HR x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. rewrite (HE x Hx). auto. Qed.

(* the callee-saved set image B's parse_items keeps (ra, sp, gp, tp and s0 .. s11 are reloaded by the epilogue) *)
Definition PI_KEPT : list (bv 5) := [1; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma pi_aregs : forall regs regs' : bvmap 5 word,
(forall r, In r PI_KEPT -> getr regs' r = getr regs r) -> getr regs' 2 = getr regs 2 -> aregs_preserved regs regs'.
Proof.
intros regs regs' HK H2 r Hr. unfold acallee_saved in Hr.
destruct (Z.eq_dec r 2) as [->|Hr2]; [exact H2|].
assert (Hc : In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) by (cbn; lia).
apply HK. clear -Hc. cbn in Hc.
unfold PI_KEPT. repeat destruct Hc as [<- | Hc]; try contradiction; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]).
Qed.

End g.
End d.

(* ---- the tactics (skip_ws_x.v's, in YC1fPx's pi form) ---- *)
Ltac pi_run RUN HS HJ SHOK := paj_run_tok_x RUN HS HJ SHOK BAND_SPAN.
Ltac pi_run_to RUNTO HS HJ SHOK stop := paj_run_to_tok_x RUNTO HS HJ SHOK BAND_SPAN stop.

(* a branch of the body: both arms, with the condition in Hc *)
Ltac pi_branch HS :=
lazymatch type of HS with
| st_ok_pi ?sg ?vl ?E ?ss (restrict (w_H ?W) ?ms) =>
apply (paj_branch W E ss ms _ _ _ _ _ HS); clear HS;
let Hc := fresh "Hc" in intros Hc HS
| _ => fail "pi_branch: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
(* pi_branch over the walk's relation wle' pa_segs RZ_cf (YSRrG.paj_branchR) *)
Ltac pi_branchR HS :=
lazymatch type of HS with
| st_ok_pi ?sg ?vl ?E ?ss (restrict (w_H ?W) ?ms) =>
apply (paj_branchR (wle' pa_segs YGcfRehidePost.RZ_cf) W E ss ms _ _ _ _ _ HS); clear HS;
let Hc := fresh "Hc" in intros Hc HS
| _ => fail "pi_branchR: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.


(* the frame_of a run leaves, turned into a kept-byte statement outside the set Zs *)
Ltac pi_kept_of SEGSN HFr Zs ev :=
lazymatch type of HFr with frame_of ?E ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
let KP := fresh "KEPT" in
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGSN H m' a = aview SEGSN H m a);
[ apply (pi_kept E rs H m m' Zs HFr); intros b_ wlo_ whi_ a0_ Hin_ Hrr_; vm_compute in Hin_;
  repeat (destruct Hin_ as [Hq_ | Hin_]; [injection Hq_ as <- <- <-; cbn [base_val] in Hrr_; ev Hrr_; cbv beta; lia|]);
  destruct Hin_
| cbv beta in KP ]
end.

(* ================================================================================================== *)
(* The block invariants of the body. Every segment lemma of the walk takes one of these as its pre and
   concludes the function's own post (the kit's fpostWF at the ENTRY registers), so the segments compose by
   the journal, exactly as the skip_ws walk's loop lemma does.
   REGISTERS image B pins for the whole body (RISC-V numbers: s0 = x8 .. s11 = x27):
     s1 = q, s3 = v, s2 = (o ? 1 : 0), s0 = q + 16 (the depth word), s4 = q + 8 (the end word),
     s10 = the shadow base, s11 = shadow (q), s9 = shadow (q + 16), s7 = shadow (q + 8), s5 = the result,
   and from the loop body on, with the kid-array pointers cached in the frame:
     s6 = v + 40 (the n field), s8 = shadow (v + 40),
     [sp]      = 2 ^ 60      (the overflow constant of the slot-size checks),
     [sp + 32] = v + 24 (kids), [sp + 24] = shadow (v + 24),
     [sp + 16] = v + 32 (keys), [sp + 8]  = shadow (v + 32).
   The shadow base is SHADOW_OFF: the walk reads it from the GOT word and AR's constant law
   (ARx_const_law, YCbqG.v) says that cell holds SHADOW_OFF. *)
Section inv. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the PrhNames class is gone (the kit's lib/A/PRH_Base.v (sha256 168022d10e46; internal record)): the room is ROOM_cf_k (YGcfRoomKeep.v), so no
   instance argument and no float-state coupling remain *)
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the shadow address of a byte *)
Definition pi_sh (a : Z) : Z := SHADOW_OFF + a / 8.

(* the registers every block of the body holds (s5, the result, is separate: it changes) *)
Definition pi_regs (regs : bvmap 5 word) (q v : Z) (o : bool) : Prop :=
  getr regs 9 = w64 q /\ getr regs 19 = w64 v /\ getr regs 18 = w64 (if o then 1 else 0) /\
  getr regs 8 = w64 (q + 16) /\ getr regs 20 = w64 (q + 8) /\
  getr regs 26 = w64 SHADOW_OFF /\ getr regs 27 = w64 (pi_sh q) /\
  getr regs 25 = w64 (pi_sh (q + 16)) /\ getr regs 23 = w64 (pi_sh (q + 8)).

(* what the loop body adds: the n pointer and its shadow in registers, the four cached words in the frame *)
Definition pi_regs_body (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte) (v : Z) : Prop :=
  getr regs 22 = w64 (v + 40) /\ getr regs 24 = w64 (pi_sh (v + 40)) /\
  val_mem segs (rdW W mem) (spZ regs) 8 (2 ^ 60) /\
  val_mem segs (rdW W mem) (spZ regs + 32) 8 (v + 24) /\
  val_mem segs (rdW W mem) (spZ regs + 24) 8 (pi_sh (v + 24)) /\
  val_mem segs (rdW W mem) (spZ regs + 16) 8 (v + 32) /\
  val_mem segs (rdW W mem) (spZ regs + 8) 8 (pi_sh (v + 32)).

(* the half-built container at v: the header, the slot arrays, and the members read so far (acc, newest
   first is NOT used - acc is in reading order here, as jrl's `rev` at the end makes it) *)
Definition pi_cont (m : word -> option byte) (lblk : Z -> Z -> Prop) (o : bool)
  (v kids keys : Z) (n cap : nat) (acc : list (list Z * PjTree.jv)) (Di : list (Z * Z)) : Prop :=
  pj_hdrR segs m v (if o then 6 else 5) 0 0 kids keys (Z.of_nat n) (Z.of_nat cap) /\
  n = length acc /\ (n <= cap)%nat /\ Z.of_nat cap <= 2 ^ 54 /\
  ((cap = 0%nat /\ kids = 0 /\ keys = 0) \/
   (0 < cap)%nat /\ lblk kids (56 * Z.of_nat cap) /\ (o = true -> lblk keys (8 * Z.of_nat cap))) /\
  (* an array keeps keys = 0, which pj_nodeR (JArr ..) asks at the closer (the loop segment's G6) *)
  (o = false -> keys = 0) /\
  NoDup Di /\ pj_apartR Di v /\
  (if o then pj_memsR segs m lblk (pj_nodeR segs m lblk) kids keys acc Di
   else pj_itemsR (pj_nodeR segs m lblk) kids (map snd acc) Di).

(* ==== THE BATCH KIT'S INVARIANTS of the loop (the batch kit 240b06ed4fd4; a Theorem Labs lane's A' template VrdIElem.v vrd_imodel) ====
   preset-tree-at-2026-10-30T00-42-43Z.tsv (sha256 08fbb565c497; internal record)) ====
   (1)/(4) THE GRANTED PREFIX: every allocator call the walk passed was granted, because every refusal leaves the loop; so the ok
   list the prefix ate is one `true` per call (the template's ip_ok P = repeat true ..). It makes the prefix's refusal peak 0
   (PRH_Base.prh_refused_peak_granted) and lets the outcome compare the run with the all-granted one (PjGrammar.agrees_jr_items). *)
Definition pi_grant (ok0 : list bool) (tr0 : list PjGrammar.ev) : Prop := ok0 = repeat true (PjGrammar.calls tr0).

(* an all-granted prefix refused no call (PRH_Base.prh_granted, the injected reading's conclusion) *)
Lemma pi_grant_granted : forall ok0 tr0 cnt fail k, pi_grant ok0 tr0 -> prh_granted ok0 cnt fail k.
Proof.
intros ok0 tr0 cnt fail k HG i _ Hn. unfold pi_grant in HG. subst ok0.
rewrite nth_repeat in Hn. discriminate Hn.
Qed.

(* (3) THE CAPACITIES (CAP, PRH_Reader.pj_ncapR): each member read so far is a tree whose containers have
   cap = ncap of their count; the container's own cap is ncap n at the loop head and ncap (S n) after its grow *)
Definition pi_ncaps (m : word -> option byte) (kids : Z) (acc : list (list Z * PjTree.jv)) : Prop :=
  pj_kidsR (fun a (mb : list Z * PjTree.jv) => pj_ncapR segs m a (snd mb)) kids acc.

(* (2) THE FREE ORDER (FREEORD-NONE): the completed slots' order list in pj_free's order (PRH_PjOrder.pf_oitemsR:
   each slot's value subtree, then its key), at every depth bound the post states, maps to af, the accumulator of
   the kit's model PresetReqAt.jfl at this point of the loop *)
Definition pi_forder (m : word -> option byte) (lblk : Z -> Z -> Prop) (o : bool) (kids keys : Z) (n : nat)
  (Di : list (Z * Z)) (acc : list (list Z * PjTree.jv)) (af : list Z) : Prop :=
  (* at EVERY depth bound that covers the members read so far (the 02:0xZ finding: the closer's Some arm asks
     the container at every n >= depth t, below MAXD - d too; a refusal exit's n >= MAXD - d is covered by the loop
     pres' depth conjunct, every member at most MAXD - S d) *)
  cf_head = PresetReqAt.HEAD -> forall nn, Forall (fun mb => (PjTree.depth (snd mb) <= nn)%nat) acc ->
  exists Facc, PRH_PjOrder.pf_oitemsR segs m lblk (PRH_PjOrder.pj_foR segs m lblk nn) o kids keys n Di Facc /\
    map (fun b => snd b + cf_head) Facc = af.

(* the model's free list of the whole call factors through jfl at this point of the loop, as pi_run_eq does for the
   run: at the LOOP HEAD (before the member's grow) *)
Definition pi_fl_eq (d : nat) (o : bool) (x0 : list Z) (ok0 : list bool) (f n cap : nat) (af y : list Z) : Prop :=
  forall ok1, prhPi_frees d o x0 (ok0 ++ ok1) = PresetReqAt.jfl ReaderRes.jr_strtod f (S d) o n cap af y ok1.

(* jfl's body after a granted grow (PresetReqAt.v:279-292, verbatim), the twin of pi_jrb *)
Definition pi_jfb (f d : nat) (o : bool) (n cap1 : nat) (af y : list Z) (ok1 : list bool) : list Z :=
  match PjGrammar.jr_name o y ok1 with
  | (None, _, _) => af ++ PresetReqAt.arrz o cap1
  | (Some (_, y1), tn, ok2) =>
    let af1 := af ++ PresetReqAt.jfv ReaderRes.jr_strtod f d y1 ok2 ++ PresetReqAt.lf tn in
    match PjGrammar.jrv ReaderRes.jr_strtod f d y1 ok2 with
    | (Some (_, r), _, ok3) =>
      match PjGrammar.skip r with
      | c :: r1 => if c =? 44 then PresetReqAt.jfl ReaderRes.jr_strtod f d o (S n) cap1 af1 r1 ok3
                   else af1 ++ PresetReqAt.arrz o cap1
      | [] => af1 ++ PresetReqAt.arrz o cap1
      end
    | (None, _, _) => af1 ++ PresetReqAt.arrz o cap1
    end
  end.
(* AFTER THE GROW (PI_O_BODY, PI_O_KEY, PI_O_FREE) *)
Definition pi_fl_eqB (d : nat) (o : bool) (x0 : list Z) (ok0 : list bool) (f n cap1 : nat) (af y : list Z) : Prop :=
  forall ok1, prhPi_frees d o x0 (ok0 ++ ok1) = pi_jfb f (S d) o n cap1 af y ok1.

(* jfl's body after the key (lk = PresetReqAt.lf of the key's trace: its one block, [] for an array), the twin of
   pi_val_k *)
Definition pi_jfv_k (f d : nat) (o : bool) (n cap1 : nat) (af lk y1 : list Z) (ok2 : list bool) : list Z :=
  let af1 := af ++ PresetReqAt.jfv ReaderRes.jr_strtod f d y1 ok2 ++ lk in
  match PjGrammar.jrv ReaderRes.jr_strtod f d y1 ok2 with
  | (Some (_, r), _, ok3) =>
    match PjGrammar.skip r with
    | c :: r1 => if c =? 44 then PresetReqAt.jfl ReaderRes.jr_strtod f d o (S n) cap1 af1 r1 ok3
                 else af1 ++ PresetReqAt.arrz o cap1
    | [] => af1 ++ PresetReqAt.arrz o cap1
    end
  | (None, _, _) => af1 ++ PresetReqAt.arrz o cap1
  end.
(* AT THE VALUE (PI_O_VAL and the value segment) *)
Definition pi_fl_eqV (d : nat) (o : bool) (x0 : list Z) (ok0 : list bool) (f n cap1 : nat) (af lk y1 : list Z) : Prop :=
  forall ok1, prhPi_frees d o x0 (ok0 ++ ok1) = pi_jfv_k f (S d) o n cap1 af lk y1 ok1.

(* the unfoldings: jfl one member deep is grow then pi_jfb; pi_jfb past a kept key is pi_jfv_k *)
Lemma pi_jfl_unfold : forall f d o n cap af y ok,
  PresetReqAt.jfl ReaderRes.jr_strtod (S f) d o n cap af y ok =
  match PjGrammar.grow o n cap ok with
  | (None, tg, _) => af ++ PresetReqAt.gheld o cap tg
  | (Some cap1, _, ok1) => pi_jfb f d o n cap1 af y ok1
  end.
Proof. reflexivity. Qed.
Lemma pi_jfb_key : forall f d o n cap1 af y ok1 nm y1 tn ok2,
  PjGrammar.jr_name o y ok1 = (Some (nm, y1), tn, ok2) ->
  pi_jfb f d o n cap1 af y ok1 = pi_jfv_k f d o n cap1 af (PresetReqAt.lf tn) y1 ok2.
Proof. intros f d o n cap1 af y ok1 nm y1 tn ok2 E. unfold pi_jfb. rewrite E. reflexivity. Qed.

(* the grammar continuation: the run of the whole call splits at this block into the prefix (ok0, tr0) and
   the loop state (fuel f, depth S d, o, n, cap, acc) at the cursor's rest y. `jrl` is PjGrammar's member
   loop; jr_items enters it with fuel 2 * length x + 2, n = cap = 0 and acc = [] (PjGrammar.v jr_cont).
   jrl's accumulator is NEWEST FIRST (it conses each member and reverses at the closer), while pi_cont reads
   acc in READING order, so jrl gets `rev acc` (caught 00:4xZ). *)
Definition pi_run_eq (d : nat) (o : bool) (x0 : list Z) (ok0 : list bool) (tr0 : list PjGrammar.ev)
  (f n cap : nat) (acc : list (list Z * PjTree.jv)) (y : list Z) : Prop :=
  forall ok1 r t ok2,
    PjGrammar.jrl prh_jr_strtod f (S d) o n cap (rev acc) y ok1 = (r, t, ok2) ->
    PjGrammar.jr_items prh_jr_strtod d o x0 (ok0 ++ ok1) = (r, tr0 ++ t, ok2).

(* the ledger has moved by the prefix trace, and the blocks the prefix allocated are D0. The batch kit (8ba304fe2f93): the move
   preset-tree-at-2026-10-29T23-27-23Z.tsv (sha256 1f0ae5f9ecde; internal record): the move takes g_most and the call's
   ALL-GRANTED trace, whose helds price a refusal's peak. Every block of the loop is reached only while every allocation so
   far was GRANTED (a refused or chosen-failed call exits), so the prefix's granted trace is the prefix itself: gt := tr0 *)
Definition pi_led (Lam : list (Z * Z)) (peak cnt fail ran most : Z) (ok0 : list bool) (tr0 : list PjGrammar.ev)
  (D0 : list (Z * Z)) (Lam0 : list (Z * Z)) (peak0 cnt0 fail0 ran0 : Z) : Prop :=
  rd_ledger_move Lam peak cnt fail ran most ok0 tr0 tr0 D0 Lam0 peak0 cnt0 fail0 ran0.

(* the blocks the prefix allocated are NEW (no block of the entry state) and are exactly what the allocator gained
   since the entry (06:0xZ): a kid slot in such a block is an in_tmp_block for the call rules, and the
   post's rd_blocks_move is read off it at every exit *)
Definition pi_blk (ly : alayout) (S : astate) (lyc : alayout) (Sc : astate) (D0 : list (Z * Z)) : Prop :=
  (forall a k, In (a, k) D0 -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) /\
  Permutation (ablocks B lyc Sc) (prhReader_ab D0 ++ ablocks B ly S).

Lemma pi_blk_of_move : forall ly S lyc Sc D0 tr rest d,
  rd_blocks_move B ly S lyc Sc D0 tr rest d -> pi_blk ly S lyc Sc D0.
Proof. intros ly S lyc Sc D0 tr rest d (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* ---- THE FLOAT-STATE CONVENTION every segment file follows (a proposal adopted 00:3xZ):
   parse_value may run musl strtod, so after its call the CURRENT float state differs from the ENTRY one.
   A segment file opens `Context {fx : YK11.FPState}` for the CURRENT state (its cfg_at runs there), takes the
   ENTRY state as a binder `fx0 : YK11.FPState`, concludes `fpostWF (fx := fx0) ...` at the entry registers, and
   every pre carries `frm_zero (@YK11.fp_csr fx) /\ fregs_kept_x fx0 fx` (pi_fpok below). Before the parse_value
   call fx = fx0 and pi_fpok is `frm_zero` plus reflexivity. ---- *)
Definition pi_fpok (fx0 fx1 : YK11.FPState) : Prop := frm_zero (@YK11.fp_csr fx1) /\ fregs_kept_x fx0 fx1.

(* ---- THE RUN POSITION OF THE ENTRY-KEYED FORM (the batch's position pair, the kit owner 14:11Z). THIS WALK NO LONGER USES
   pi_pos OR ITS FIVE LEMMAS: since form (b) the texts state the position in their post, keyed on
   their own trace, and the travelling facts of every block are PItems_posb.v's pi_posb S Sc tr0 (the position
   relation from the entry state to the block state over the prefix trace) and pi_live (the live requests moved by
   that trace). pi_pos and its lemmas stay because other trees cite them. ---- *)
Definition pi_pos (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_H0 : list Z) (i : nat) (S' : astate) : Prop :=
  exists i' hist', (i <= i')%nat /\ PresetRoomPos.iface_room_pos rp_sm rp_x rp_os i' rp_H0 hist' S'.

Lemma pi_pos_of : forall rp_sm rp_x rp_os rp_H0 i hist S,
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os i rp_H0 hist S -> pi_pos rp_sm rp_x rp_os rp_H0 i S.
Proof. intros rp_sm rp_x rp_os rp_H0 i hist S H. exists i, hist. split; [lia | exact H]. Qed.

(* the position composes along a chain of calls: what a callee gives at its own entry index carries the caller's *)
Lemma pi_pos_trans : forall rp_sm rp_x rp_os rp_H0 i S1 S2,
  pi_pos rp_sm rp_x rp_os rp_H0 i S1 ->
  (forall j hist, PresetRoomPos.iface_room_pos rp_sm rp_x rp_os j rp_H0 hist S1 ->
     pi_pos rp_sm rp_x rp_os rp_H0 j S2) ->
  pi_pos rp_sm rp_x rp_os rp_H0 i S2.
Proof.
intros rp_sm rp_x rp_os rp_H0 i S1 S2 (i1 & h1 & Hle & H1) HS.
destruct (HS i1 h1 H1) as (i2 & h2 & Hle2 & H2). exists i2, h2. split; [lia | exact H2].
Qed.

(* a step that does not change the state keeps it *)
Lemma pi_pos_eq : forall rp_sm rp_x rp_os rp_H0 i S1 S2, S2 = S1 ->
  pi_pos rp_sm rp_x rp_os rp_H0 i S1 -> pi_pos rp_sm rp_x rp_os rp_H0 i S2.
Proof. intros rp_sm rp_x rp_os rp_H0 i S1 S2 E H. rewrite E. exact H. Qed.

(* the two a CALL needs (14:3xZ): the caller must name the index the callee's text takes BEFORE
   the SRr, and the callee gives its post at that index, which lowers back to the caller's *)
Lemma pi_pos_elim : forall rp_sm rp_x rp_os rp_H0 i S (P : Prop),
  pi_pos rp_sm rp_x rp_os rp_H0 i S ->
  (forall j hist, (i <= j)%nat -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os j rp_H0 hist S -> P) -> P.
Proof. intros rp_sm rp_x rp_os rp_H0 i S P (j & hist & Hle & H) K. exact (K j hist Hle H). Qed.

Lemma pi_pos_mono : forall rp_sm rp_x rp_os rp_H0 i j S,
  (i <= j)%nat -> pi_pos rp_sm rp_x rp_os rp_H0 j S -> pi_pos rp_sm rp_x rp_os rp_H0 i S.
Proof. intros rp_sm rp_x rp_os rp_H0 i j S Hij (j' & hist & Hle & H). exists j', hist. split; [lia | exact H]. Qed.

(* ---- the ENTRY premises, the kit's text's own (kit walkkit-next f97c8b2f046b, lib/A/PRH_FnParse.v tparse_items_specX d
   CTX CTX0 DW), at the entry float state fx0 and entry registers regs0: every segment carries them unchanged, because
   the callee premises at each call site are derived from them. The room is the invariant room_live_cf; the kr binder
   of pi_ent and of every segment pre is VESTIGIAL (kept so the segment files' argument lists do not renumber), dropped at the
   top. most / own are the ledger's g_most / g_own_ran_out values (prh_ledger's two cells since the E sweep); every
   reader text keeps them, so they are the same at every block and in the post. CTX0 / DW (the call-graph universe closure
   closure over the run's data words, the kit 4eb03b7b7e8) are the LAST two arguments of pi_ent and of every pre, and
   LAST two arguments of pi_ent and of every pre, and parameters of every spec. Added beside the text's own: the entry gp /
   tp (afn_pre_x's, which the window call rule aj_call_xW asks at every call site; 02:1xZ) and fpre's read-only view. ---- *)
Definition pi_ent (fx0 : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs0 : bvmap 5 word) (mem : word -> option byte) (ch : list (Z * Z * Z)) (CTX : list (list Z))
  (Lam : list (Z * Z)) (peak cnt fail ran most own e q text len p : Z) (d kr : nat) (tb : list Z) (v : Z) (o : bool)
  (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  (* the overlay is normal at entry (kit the internal file preset-tree-at-2026-10-29T13-54-32Z.tsv (sha256 14e543909afe; internal
     record)), and THE LIVE COUNTS AT THE INNER CALLS (PRH_FnParse.v blob 105eb463e190 :311-314, verbatim): the peak
     of the secondary and of the class-24 count along the ALL-GRANTED events of the call, from the entry's live requests.
     Position-free; a block derives a callee's count premise from them by PItems_posb.pi_lc_at at its own pi_live *)
  YAkMemnorm.memnorm segs mem /\
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  In (raZ regs0 :: spine ch) CTX /\
  prh_univ_closure B CTX0 /\
  prh_cur_entry W mem regs0 q /\
  (* the entry chain at the entry view, up to its spine; chain independence at each call comes from the closure *)
  (exists ch', achain ly (aview segs (w_H W) mem) (spZ regs0) (s0Z regs0) ch' /\ spine ch' = spine ch) /\
  (* the PARTITIONED cursor chain (the kit owner's 06:39Z ruling), its chain arm from prh_s0 F_parse_string q *)
  ((spZ regs0 <= q < spZ regs0 + 16) \/
   (spZ regs0 + 16 <= q /\ exists ch', achain ly (aview segs (w_H W) mem) (spZ regs0) (prh_s0 F_parse_string q) ch')) /\
  getr regs0 10 = w64 q /\ getr regs0 11 = w64 v /\ getr regs0 12 = w64 (if o then 1 else 0) /\
  getr regs0 3 = w64 (as_gp B) /\ getr regs0 4 = w64 (as_tp B) /\
  rd_pre (fx := fx0) B (STK_parse_items d) ly S Hp W regs0 mem Lam peak cnt fail ran most own e q text len p d tb v /\
  p < text + len /\ nth_error tb (Z.to_nat (p - text)) = Some (if o then 123 else 91) /\
  rd_room S (prhPi_gtrace d o (rest_atR tb text p)) /\
  (* the chain the missing-colon free reads, from s0 = prh_s0 F_parse_items q (q + 16 on B; the kit owner's (2), replacing D4) *)
  (exists ch0, achain ly (aview segs (w_H W) mem) (spZ regs0 - pi_frame F_parse_items) (prh_s0 F_parse_items q) ch0) /\
  Z.of_nat (length (frames S)) + Z.of_nat (PjGrammar.MAXD - d) <= fs_frames 0 /\
  (* fpre's read-only view at the entry: every callee text's fpre needs it at its call state, and the journal's
     image clause carries it there (01:2xZ) *)
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  (* THE CURSOR SET (the batch kit 240b06ed4fd4, PRH_FnParse.v ed236011cf99:385 / :407, verbatim): every cursor free trace
     at q is CW's (or its word is pj_parse's code word), and the depot at entry has room for CW with no fresh slot *)
  prh_cw_entry B CW W mem regs0 q /\
  YCbqGwild.wild_room (as_universe B) CW 0 (st_depot S) /\
  (* THE HULL BUDGET (route (b), the text's premise): room for the all-granted events; every callee's budget is paid
     from it at its block (PItems_posb.pi_posb_budget) *)
  PresetHullBudget.hull_budget S (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))).

(* the hull budget, read by name *)
Lemma pi_ent_hull : forall fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o
  CTX0 CW,
  pi_ent fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW ->
  PresetHullBudget.hull_budget S (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))).
Proof.
intros fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW H.
unfold pi_ent in H.
repeat lazymatch type of H with PresetHullBudget.hull_budget _ _ => fail | _ /\ _ => destruct H as [_ H] end.
exact H.
Qed.

(* ---- the harness-block shadow law (YGcfHeadSh.v ARx_hshadow_law_cf at ARx): past the head, the user range of a
   live block whose base is in Hp has a block shadow and a visible hull. The kid slots (memset, parse_value's node)
   and the key slots (keys + 8n) are user bytes of harness blocks, which ARx_shadow_law does not reach. ONE text for
   every segment, a Section hypothesis there, discharged at ARx := ARcf by YGcfHeadSh.v ARx_hshadow_law_cf_ok. ---- *)
Definition pi_hshadow_law (hl : Z) : Prop :=
  forall ly S Hp W mem md b n, ARx ly S Hp W mem md -> In (b, n) (ablocks B ly S) -> In b Hp ->
  block_shadow (aview segs (w_H W) mem) SHADOW_OFF (b + hl) (req_size n - hl) /\
  (hl < req_size n -> shadow_hull_vis (aview segs (w_H W) mem) (b + hl) (req_size n - hl)).

(* ---- the FRAME image B's prologue builds (`addi sp, sp, -144`, then ra and s0 .. s11 at sp + 136 down to
   sp + 40), the entry gp / tp, and the caller window kept outside FP: what the epilogue reads back and what
   fpostWF's window clause needs. Offsets are the listing's (0x87a3c .. 0x87a6c). ---- *)
Definition pi_frame (regs0 regs : bvmap 5 word) (W : world segs) (mem : word -> option byte)
  (Wc : world segs) (memc : word -> option byte) (e q v : Z) : Prop :=
  spZ regs = spZ regs0 - PI_FRAME /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
  val_mem segs (rdW Wc memc) (spZ regs + 136) 8 (bv_unsigned (getr regs0 1)) /\
  val_mem segs (rdW Wc memc) (spZ regs + 128) 8 (bv_unsigned (getr regs0 8)) /\
  val_mem segs (rdW Wc memc) (spZ regs + 120) 8 (bv_unsigned (getr regs0 9)) /\
  val_mem segs (rdW Wc memc) (spZ regs + 112) 8 (bv_unsigned (getr regs0 18)) /\
  val_mem segs (rdW Wc memc) (spZ regs + 104) 8 (bv_unsigned (getr regs0 19)) /\
  val_mem segs (rdW Wc memc) (spZ regs + 96) 8 (bv_unsigned (getr regs0 20)) /\
  val_mem segs (rdW Wc memc) (spZ regs + 88) 8 (bv_unsigned (getr regs0 21)) /\
  val_mem segs (rdW Wc memc) (spZ regs + 80) 8 (bv_unsigned (getr regs0 22)) /\
  val_mem segs (rdW Wc memc) (spZ regs + 72) 8 (bv_unsigned (getr regs0 23)) /\
  val_mem segs (rdW Wc memc) (spZ regs + 64) 8 (bv_unsigned (getr regs0 24)) /\
  val_mem segs (rdW Wc memc) (spZ regs + 56) 8 (bv_unsigned (getr regs0 25)) /\
  val_mem segs (rdW Wc memc) (spZ regs + 48) 8 (bv_unsigned (getr regs0 26)) /\
  val_mem segs (rdW Wc memc) (spZ regs + 40) 8 (bv_unsigned (getr regs0 27)) /\
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview segs (w_H Wc) memc a = aview segs (w_H W) mem a) /\
  (* the epilogue's `ret` and its sp facts (01:1xZ): fpostWF's return pc is getr regs0 1, whose
     ret_ok only afn_pre_x at the entry carries; e's sign and alignment come from rd_pre's fwin *)
  YK0s.ret_ok (getr regs0 1) /\ 0 <= e /\ e mod 16 = 0.

End inv.
