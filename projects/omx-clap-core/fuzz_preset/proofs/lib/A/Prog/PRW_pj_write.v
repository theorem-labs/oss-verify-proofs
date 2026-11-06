(* fuzz_preset image A, slice S7b (WalkS7b.S7bPjWrite / .S7bPjWrite2): the program walk of pj_write
   (A 0x86c10, 31 instructions) over the ONE image-A program listing (lib/A/Listing_prog.v, a Theorem Labs lane), generic in
   the image facts (Context PAImg) and in the allocator relation ARx (LAWS : AR_laws_x), concluding the batch kit's text
   tpj_write_specX for every depth n.
   KIT: the kit's cut 7cdbb61b5fa0 (re-fitted on the batch kit's tip 44123abafeb7, merged forward onto the cut
   unchanged; the cut's blobs: PRH_Base, PRH_FnWriter
   d89d3c67b78c, PRH_FnAlloc 4d8aeba047e5): tpj_write_specX keys the run's strtod model (ReaderRes.jr_strtod), takes
   the closure without DW (prh_univ_closure B CTX0), the CONSUMER WINDOW prh_cons_from over its own events, its run
   events as an ENTRY premise (prh_run_at .. rp_i (prhWriter_pjw_evs [] cnt fail P)) and its entry budget
   blocks_bytes S + LIVE_pj_write .. <= LIVE_MAX, and posts prh_oks over the run's requests (prhWriter_reqs) and
   most, NO REFUSAL (prh_granted, DEAD-PJWRITE), the EXACT advance under prh_granted and the refusal peak
   prhWriter_rpeak, in the FLOAT form fpostFm at the ENTRY float state. twrite_value_specX / tput_specX take the
   consumer window (supplied here by pjw_cons_wv / pjw_cons_put, PRH_Base.prh_cons_from_app_iff) and the live room AT
   EACH EVENT prh_live_evs (supplied from pj_write's entry budget by pjw_live0 / pjw_live_put: along the
   all-granted run the live list is the entry's plus the buffer, every capacity in the doubling chain below
   newcap 0 (len (wdoc t p) + 1)), and post prhWriter_ret_ok with prh_granted (S7a_WriterRet's prhWriter_blk_of_ret_ok
   / prhWriter_ret_ok_of_blk / prhW_app_model compose them). tfuzz_free_specX takes `admits` (a FIXED trace here, so
   YG01.admits_fix: no gap) and posts the BUDGETED fpostbm (PRH_Base.fpost_of_fpostb_fix reads it back); its arms
   transfer a position at E = [] (p = 0) or [HFr (n + cf_head)] (p <> 0). The put family's case 1 is the kit's form (a),
   which this walk does not use - both its calls are case 2.
   ENGINE: the cut's (int102 f44822dff082's engine with the P'' set of the engine's univ-widening; YCbqG),
   listing of
   record: the cut's lib/A/Listing_prog.v 7ed1529926bd / PAImg_prog.v 505a51ff7d08.
   THE FLOAT STATE: the walk runs at the Section's fx (the ENTRY float state) up to write_value's return, which is at
   SOME fx' (frm_zero, fs0-fs11 kept: YCbqGcallW.aj_call_xWF); the symbolic state moves there by
   YCbqGcall.st_ok_restrict_xfx (pjw_xfx), and everything after it runs at fx' with the runners, the branch and the
   return taken AT fx' (named-implicit spelling), the put and fuzz_free texts as Section hypotheses quantified over
   the float state (HPUT / HFREE), and pjw_tail generic in the current float state (its binder fxc, with
   frm_zero fxc and fregs_kept_x fx fxc). The final post is fpostF at the ENTRY fx.
   Engine use: YC80x / YC1fPx (paj_run_x_invR / paj_run_to_x_invR: the runs carry the memory invariant Pm by its
   laws srr_inv_laws) over YCbqG's ajournal_xR; the journal-free steps are YSRrG's paj_branchR and YC1fP's return;
   the calls of write_value / put are YCbqGcallW's aj_call_xWFR / aj_call_xWR (their texts are in the caller-window
   forms fpostWFmR / fpostWmR, at the window d = pj_write's own frame); the call of __asan_memset is YGcallMxmn's
   aj_intrin_at_xmR (the memnorm row); the call of fuzz_free is aj_call_xWR at e1 = 0 (its budgeted post read back
   by fpost_of_fpostb_fix, then fpostW_x_of_apostR); the after-call steps are PRW_StepKit's. Each call's memory keep
   crosses by srr_inv_call.
   RE-FIT TO THE KIT'S PRIMED TEXTS: write_value, put
   and fuzz_free conclude SRr' SEGS RZ_cf with their posts at wle' SEGS RZ_cf, and tpj_write_specX concludes SRr'
   (fpostFm, already at wle'). So the walk runs at wle' SEGS RZ_cf from its entry journal (ajournal_x_initR) on, the
   memset and the returns lift by SRr_SRrG, and pjw_walk / pjw_tail conclude SRr'. The hull drafts' texts add
   `length rp_os <= 4` (passed to write_value and put) and fuzz_free's `p <> 0 -> hull_budget S []`, paid from the
   run position (pjw_hull_pay, under the instance fact HHCAP). Callee posts and journals are read BY SHAPE / BY
   NAME (pjw_split / pjw_pick, the ajxR_* projections), so an appended or inserted conjunct does not shift a pattern.
   SHAPE: pjw_tail is the ONE tail from the join at A 0x86c64 (pj_write's slot 21, state pjw_ssT), which BOTH arms
   of `beqz s0` reach (the pretty = 0 arm by a run and a stretch into the atom band 65..80, the pretty <> 0 arm by
   the put call and its re-seat into the same band; the branch fact is dropped by pjw_drop_cond). pjw_walk is the
   walk, generic in Pm; pjw_holds_lc instantiates Pm once (the YAkMemnorm keep) and concludes the batch kit's text.
   THE ONE OPEN ARGUMENT: pj_write's single fuzz_free call site frees a non-NULL buffer only on its failure path, and
   there tfuzz_free_specX asks `p <> 0 -> YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV`, which
   no text of pj_write bounds; it is the named ARGUMENT pjw_ARGCNT of pjw_holds_lc (a Theorem Labs lane 08:06Z), to be
   discharged by a Theorem Labs lane's counts_of_room_pos_rl / counts_of_room_pos_ok from the model-run position this walk holds
   at that state (supplied under the p <> 0 arm; its shape is unchanged).
   THE POSITION (pjw_tail): write_value's post gives the exact advance under its outcomes ok1; the newline put's
   event is read off the entry list while the writer has not failed (pjw_evs_ok_or_failed); the join carries the
   exact advance under the composed outcomes (pjw_len_one: the event count is a function of the end state,
   pjw_evs_len); the fuzz_free (buf) of a failed writer is the next event of the entry list exactly when no grow was
   refused (pjw_granted), which is the kit's prh_granted condition: fuzz_free's p <> 0 arm transfers the position at
   E = [HFr (cap + cf_head)], its p = 0 arm at E = []. The writer's outcome-list lemmas here are local copies
   of the shapes in S7a_WriterRet.v (prhW_putN_ok_or_failed / prhW_putN_agree_c) for prhWriter_evs.
   NO IMAGE VALUE IS TYPED HERE: pj_write's offset is 4 * its generated slot (PAImg_prog A_prog_slot), and the one
   .rodata address the code forms (.str.3, the newline put when pretty <> 0) is read out of the generated listing
   itself (pjw_addhi_atom / pjw_addhi_off read the atom and the addend of the PAddHi at a named slot), so a re-pin is
   a regeneration, not a rewrite.
   Numerals: 4 (LENGTH: instruction bytes), 64 (LENGTH: pj_write's own frame, the N of its `addi sp, sp, -64`),
   8 / 24 / 32 / 56 (LENGTH: the struct's field offsets and its size, PRH_FnWriter prhWriter_out), 2 ^ 46 / 2 ^ 47
   (LENGTH: the stack atom's range), 2 ^ 44 (LENGTH: the shadow span), 9 / 14 / 15 / 18 / 20 / 21 / 24 / 25
   (DERIVED: pj_write's own slots, counted from its entry), 65 / 80 / 81 / 82 / 83 (DERIVED: free atom bands of the
   symbolic environment). No ADDRESS.
   Structural reference only (read, never Required or cited): a working branch e09c6006f5b
   lib/A/Prog/pj_write.v (the old-framework walk of the ORIGINAL image). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMx YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfTreeVis YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn.
(* the re-hiding move (the kit's primed texts): the step relation over a world relation and its instance at wle' (SRrG,
   wle', SRr'; YSRrG's SRr'_mono and paj_branchR) and the fixed zone RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
(* the hull payment at fuzz_free's call, from the run position at preset's CfParams (hull_budget_of_room_pos) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetSecTotal PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Img PRH_Reader PRH_FnAlloc PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit S7a_WriterRet S7a_WriterLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* no implicit sink: lib/A has no ASan sink instance, and the plain one (YI5b) would resolve silently *)
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.

(* ---- pj_write's place in the generated listing, and the .rodata addend the listing carries ---- *)
Definition PJW_SLOT : nat := A_prog_slot AS_pj_write.
Definition AF_pj_write : Z := 4 * Z.of_nat PJW_SLOT.
Definition pjw_addhi_off (k : nat) : Z :=
  match nth (PJW_SLOT + k) A_prog_listing (PW 0) with
  | PAddHi _ _ _ _ off => off
  | PLdHi _ _ _ _ off _ _ => off
  | _ => 0
  end.
Definition pjw_addhi_atom (k : nat) : nat :=
  match nth (PJW_SLOT + k) A_prog_listing (PW 0) with
  | PAddHi _ _ _ a _ => a
  | PLdHi _ _ _ a _ _ _ => a
  | _ => O
  end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Section f.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation VAL := (@pa_val rc A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).
(* the fixed re-hideable zone of the cf layer (YGcfRehidePost.v), at this Section's run ceiling *)
#[local] Notation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

(* the newline literal .str.3 the pretty arm puts: the PAddHi at pj_write + 4 * 18 *)
Definition PJW_NL : Z := VAL (pjw_addhi_atom 18) + pjw_addhi_off 18.

Definition PJW_Bx : sv := SLit SHADOW_OFF.
Definition PJW_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the symbolic entry state: the own frame (64 bytes below the entry sp, atom 2) in three regions, so a call that
   writes the struct keeps the other two: the saved registers [-24, 0), the struct o [-56, -24), the pad [-64, -56) *)
Definition pjw_save : YP09.region := YP09.mkRegion (Some 2%nat) (-24) 0 (-24) 0 [].
Definition pjw_o : YP09.region := YP09.mkRegion (Some 2%nat) (-56) (-24) (-56) (-24) [].
(* the struct again, after the writing calls, with the two fields the tail loads (A 0x86c64 lw a1, 32(sp) is
   w_failed, A 0x86c68 ld a0, 8(sp) is buf) as fresh atoms 82 and 81 (the engine decides on a literal, so a value it
   must branch on is an atom; 81 is the first free atom above the join band 65..80) *)
Definition pjw_oA : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-56) (-24) (-56) (-24)
    [ YP09.mkChunk (-56) (CVal 8%N (SOff 81 0)); YP09.mkChunk (-32) (CVal 4%N (SOff 82 0)) ].
Definition pjw_pad : YP09.region := YP09.mkRegion (Some 2%nat) (-64) (-56) (-64) (-56) [].
Definition pjw_regions : smem := [ pjw_save; pjw_o; pjw_pad ].
Definition pjw_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ] [] [].
Definition pjw_ss : sstate := mkSS AF_pj_write sr_atoms pjw_regions None pjw_facts.
(* ---- THE JOIN (A 0x86c64, pj_write's slot 21): the two arms of `beqz s0` (A 0x86c4c, pretty) meet here. The
   pretty = 0 arm reaches it by a run, the pretty <> 0 arm by the put call and its re-seat; both are put into THIS
   ONE state (MEASURED, the internal file build-20261029T132158Z.log markers JOIN0 / JOIN1, byte for byte equal): the caller-saved
   registers havocked into the free band 65..80, the saved-register region with ra / s0 / s1 as they were stored
   (atoms 1, 11, 10: the prologue's `sd ra`, `mv s0, a1`, `mv s1, a0`), the struct and pad regions dropped, and
   the branch fact dropped (pjw_drop_cond). ---- *)
Definition pjw_saveJ : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-24) 0 (-24) 0
    [ YP09.mkChunk (-24) (CVal 8%N (SOff 9 0)); YP09.mkChunk (-16) (CVal 8%N (SOff 8 0));
      YP09.mkChunk (-8) (CVal 8%N (SOff 1 0)) ].
Definition pjw_regsJ : list sv :=
  [ SLit 0; SOff 65 0; SOff 2 (-64); SOff 3 0; SOff 4 0; SOff 66 0; SOff 67 0; SOff 68 0; SOff 11 0; SOff 10 0;
    SOff 69 0; SOff 70 0; SOff 71 0; SOff 72 0; SOff 73 0; SOff 74 0; SOff 75 0; SOff 76 0; SOff 18 0; SOff 19 0;
    SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 77 0; SOff 78 0;
    SOff 79 0; SOff 80 0 ].
Definition pjw_ssT : sstate := mkSS (AF_pj_write + 4 * 21) pjw_regsJ [ pjw_saveJ ] None pjw_facts.
Definition pjw_E (regs : bvmap 5 word) : env := Eimg (Ereg regs []).

(* pj_write's three call return sites (slots 15, 21, 25: after `jal write_value`, `jal put`, `jal fuzz_free`) are
   slots of the listing, so below the allocator's ceiling: the kit fpre's `raZ regs < YM05.alloc_ceiling` at its three
   call sites (PRW_StepKit.pa_slot_lt_ceil_b on a closed boolean) *)
Lemma pjw_ret_ceil : forall k, In k [AF_pj_write + 4 * 15; AF_pj_write + 4 * 21; AF_pj_write + 4 * 25] ->
  BASE + k < YM05.alloc_ceiling.
Proof.
intros k Hk. apply (pa_slot_lt_ceil_b (L := A_prog_listing) (PL := PL_prog_A) (PI := PA)).
- assert (HA : 0 <= AF_pj_write < 2 ^ 39) by (unfold AF_pj_write; split; [lia | vm_compute; reflexivity]).
  destruct Hk as [<- | [<- | [<- | []]]]; lia.
- destruct Hk as [<- | [<- | [<- | []]]]; vm_compute; reflexivity.
Qed.
Ltac pjw_ret_ceil_tac :=
  apply pjw_ret_ceil; vm_compute;
  first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity].

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis segs_low : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd.
(* image fact of the instance, discharged at PI_prog_A by A_entry_pj_write *)
Hypothesis Hent : SIGMA AS_pj_write = BASE + AF_pj_write.
(* R2's memset text at its entry, the memnorm row (YGcallMxmn.v blob b47cf7942c3d: YGcallMx.v's aintrin_realizes_x
   with the YAkMemnorm keep as its last post conjunct) *)
Hypothesis AMS : YGcallMxmn.aintrin_realizes_xm SEGS B ARx OSet (SIGMA AS___asan_memset).
(* the universe closure's parameter, as the cut's texts take it (cut 7cdbb61b5fa0: no DW) *)
Variable CTX0 : list (list Z).
(* The batch kit's callee texts (lib/A/PRH_FnWriter.v blob d89d3c67b78c, lib/A/PRH_FnAlloc.v blob 4d8aeba047e5):
   S7bWriteValue's walk, WalkS7a's put walk, and the allocator lane's fuzz_free walk prove them. write_value is
   called at the ENTRY float state (the Section's fx); put and fuzz_free run after write_value's return, at the float
   state it returns at, so their texts are taken at EVERY float state *)
Hypothesis HWV : forall n, twrite_value_specX (PA := PA) B ARx SK CTX0 n.
Hypothesis HPUT : forall fx0 : YK11.FPState, tput_specX (fx := fx0) (PA := PA) B ARx SK CTX0.
Hypothesis HFREE : forall fx0 : YK11.FPState, tfuzz_free_specX (fx := fx0) (PA := PA) B ARx SK.
(* image facts of the instance, discharged at PI_prog_A *)
(* the free call's return site: pj_write's `jal fuzz_free` is its slot 24, so its return site is slot 25 *)
Hypothesis HRET : nth 0 (pi_ret_sites F_pj_write RT_fuzz_free) 0 = BASE + AF_pj_write + 4 * 25.
(* no static of alloc.c lies in the read-only band (they are RW), so the journal's image clause keeps the band *)
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a ->
  ~ Exists (in_zr a) (@prh_pst prh_img_A).
(* YC1fPx's PST_ok: alloc.c's seven statics are image bytes the runtime does not own *)
Hypothesis PST_ok : forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* the newline literal .str.3 the pretty arm puts (IMAGE FACT, discharged at PI_prog_A): its byte is the image's,
   and its shadow is zero (a registered read-only global: LAWS's alx_zshadow at its as_zero_shadow range). This is
   what put's src_rd and prhWriter_src_home's read-only case ask. *)
Hypothesis HLIT : forall ly' S' Hp' (W' : world SEGS) m' md',
  ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m') ->
  src_rd W' m' PJW_NL [10] /\ kept_at (PA := PA) B [] PJW_NL 1.
Hypothesis HIMGNL : in_img SEGS PJW_NL.
(* the cf instance behind ARx (the preset's allocator), as a Theorem Labs lane spelled it: the tree's blocks are visible
   because a8's tree_vis_of_blocks_cf proves it from ARcf alone. *)
Hypothesis S9_CF : forall ly S Hp W mem md, ARx ly S Hp W mem md -> YG0ncf.ARcf pa_segs B ly S Hp W mem md.
(* INSTANCE FACT (discharged at CfParams_preset by reflexivity, as S7a_put_inst.v discharges put's HCAP): the
   instance's hull caps are at least preset's, the caps PresetHullPay.hull_budget_of_room_pos pays under. Needed
   since tfuzz_free_specX takes `p <> 0 -> hull_budget S []` (the hull drafts, PRH_FnAlloc.v), which pj_write pays
   from its run position at the free's state (pjw_hull_pay) *)
Hypothesis HHCAP : @YGcfNames.cf_kmax CfParamsPreset.CfParams_preset <= YGcfNames.cf_kmax /\
  @YGcfNames.cf_T_max CfParamsPreset.CfParams_preset <= YGcfNames.cf_T_max.

(* THE HULL PAYMENT at pj_write's fuzz_free call: the run's position at the call's state, in a run of at most 4
   calls, leaves preset's top budget (PresetHullPay.hull_budget_of_room_pos); a free's event list for the budget is
   empty (a free makes no secondary entry); HHCAP carries preset's caps to cp *)
Lemma pjw_hull_pay : forall sm x (os : list (option nat * option nat * option nat)) i H0 hist (S : astate),
  (length os <= 4)%nat -> PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PresetHullBudget.hull_budget S [].
Proof.
intros sm x os i H0 hist S Hl HP.
assert (HN1 : Z.of_nat (PresetSecTotal.nsec []) <= PresetSecTotal.NCALL)
  by (rewrite PresetSecTotal.NCALL_value; change (PresetSecTotal.nsec []) with 0%nat; lia).
assert (HT1 : PresetSecTotal.tsec [] <= PresetSecTotal.TCALL)
  by (rewrite PresetSecTotal.TCALL_value; change (PresetSecTotal.tsec []) with 0; lia).
destruct (PresetHullPay.hull_budget_of_room_pos sm x os i H0 hist S [] Hl HP HN1 HT1) as (B1 & B2).
destruct HHCAP as (C1 & C2). unfold PresetHullBudget.hull_budget. split; lia.
Qed.

(* A CALLEE'S POST READ BY SHAPE: split every top-level conjunction of H into fresh hypotheses, so the walk names
   each conjunct it uses by its TYPE (a lazymatch on the conjunct's statement) and a conjunct a later text appends
   or inserts does not shift a positional destruct pattern *)
Ltac pjw_split H :=
  lazymatch type of H with
  | _ /\ _ =>
      let H1 := fresh "Hcj" in let H2 := fresh "Hcj" in
      destruct H as [H1 H2]; pjw_split H1; pjw_split H2
  | _ => idtac
  end.
(* the newest hypothesis whose type mentions the constant c, renamed H' *)
Ltac pjw_pick c H' := match goal with H : ?T |- _ => lazymatch T with context [c] => rename H into H' end end.

(* ---- generic helpers of this walk ---- *)

(* a byte window the view reads as zero is a zero value of any width (PRW_StepKit.val_mem_zero8 at any n) *)
Lemma pjw_zero : forall (H : word -> bool) (m : word -> option byte) (a : Z) (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> aview SEGS H m (a + i) = Some 0) -> val_mem SEGS (mrestrict H m) a n 0.
Proof.
intros H m a n Hz j Hj.
destruct (aview_byte SEGS H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by
  (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])). lia.
Qed.

(* a byte outside the image has no ROM backing, so the view determines the memory *)
Lemma pjw_rom_none : forall a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> seg_rom SEGS (Z_to_bv 64 a) = None.
Proof.
intros a Ha Hn. apply MemNorm.seg_rom_unmapped. rewrite unsigned_lit_small by exact Ha.
destruct (find_segment SEGS a 1) as [s|] eqn:E; [exfalso | reflexivity].
destruct (find_segment_hit SEGS a 1 s E) as (Hin & Hlo & Hhi). apply Hn. exists s. split; [exact Hin | lia].
Qed.

Lemma pjw_mrestrict_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  aview SEGS H' m' a = aview SEGS H m a ->
  mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H H' m m' a Ha Hn Heq. pose proof (mbyte_of_aview SEGS H H' m m' a Heq) as X.
unfold mbyte in X. rewrite (pjw_rom_none a Ha Hn) in X.
destruct (mrestrict H' m' (Z_to_bv 64 a)) as [b'|]; destruct (mrestrict H m (Z_to_bv 64 a)) as [b|];
  first [reflexivity | discriminate X | exact X].
Qed.

(* the tree's frame premise from the journal's keep clauses: the view agrees on a non-image byte set *)
Lemma pjw_agree_of_aview : forall (W1 W2 : world SEGS) (m1 m2 : word -> option byte) (X : Z -> Prop),
  (forall x, X x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x) ->
  (forall x, X x -> aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x) ->
  pj_agreeR SEGS (mrestrict (w_H W1) m1) (mrestrict (w_H W2) m2) X.
Proof.
intros W1 W2 m1 m2 X Hr Heq x Hx. destruct (Hr x Hx) as [Hb Hi]. split.
- apply (mbyte_of_aview SEGS). exact (Heq x Hx).
- apply (writable_at_eq SEGS). exact (pjw_mrestrict_of_aview _ _ _ _ x Hb Hi (Heq x Hx)).
Qed.

(* the real stack's shadow is zero (LAWS's alx_zshadow_byte), so a stack window is addressable *)
Lemma pjw_ra_stack : forall ly S Hp W mem md a n,
  ARx ly S Hp W mem md -> ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S Hp W mem md a n HAR Hlo Hhi x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. apply (alx_zshadow_byte SEGS B ARx LAWS ly S Hp W mem md x HAR). lia.
Qed.

(* and its hull is visible: every shadow byte of the hull is the shadow byte of a stack address, and the hull
   reaches at most 63 bytes below and 56 bytes above the window (fpre's third conjunct covers the upper side) *)
Lemma pjw_hull_stack : forall ly S Hp W mem md a n,
  ARx ly S Hp W mem md -> ly_stk_lo ly + 128 <= a -> a + n + 64 <= ly_stk_hi ly -> 0 <= n ->
  shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Proof.
intros ly S Hp W mem md a n HAR Hlo Hhi Hn s Hs. unfold shadow_addr in Hs.
pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ma.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Db. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Mb.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Dc.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Mc.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Dd.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Md.
assert (Hx : SHADOW_OFF + (8 * (s - SHADOW_OFF)) / 8 = s)
  by (rewrite Z.mul_comm, Z.div_mul by lia; lia).
rewrite <- Hx.
rewrite (alx_zshadow_byte SEGS B ARx LAWS ly S Hp W mem md (8 * (s - SHADOW_OFF)) HAR) by
  (unfold SHADOW_OFF in *; lia).
discriminate.
Qed.

Lemma pjw_entry : forall STK ly S Hp W regs mem md ch,
  64 <= STK -> afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (pjw_E regs) pjw_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_pj_write)) mem (seg_rom SEGS))) /\
  sh_ok SEGS PJW_Bx [] (pjw_E regs) (mrestrict (w_H W) mem).
Proof.
intros STK ly S Hp W regs mem md ch H64 HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := pjw_E regs).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs []) k)
  by (intros k Hk; subst E; unfold pjw_E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (unfold YM05.alloc_ceiling in *; lia).
split.
- unfold pjw_ss. apply pa_entry_st_ok_full.
  + unfold E, pjw_E. apply (regs_ok_agree 32 (Ereg regs [])).
    * split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
    * vm_compute. reflexivity.
    * apply regs_ok_Ereg.
  + vm_compute. reflexivity.
  + unfold pjw_regions, pjw_save, pjw_o, pjw_pad. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite Usp;
    (split; [lia|]); (split; [lia|]); (split; [|constructor]);
    intros a Ha; apply (apresent_writable SEGS); apply Hpres; lia.
  + unfold pjw_regions, pjw_save, pjw_o, pjw_pad. cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [pjw_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
- unfold sh_ok. constructor.
Qed.

(* a branch fact dropped: the two arms of `beqz s0` (A 0x86c4c) meet at A 0x86c64 in ONE symbolic state. At ANY float
   state: the join stands after write_value's return, at the float state that call returns at *)
Lemma pjw_drop_cond : forall (fxc : YK11.FPState) E pc regs fregs mem resv A c C AL ms,
  st_ok_pi (fx := fxc) SEGS VAL E (mkSST pc regs fregs mem resv (mkFacts A (c :: C) AL)) ms ->
  st_ok_pi (fx := fxc) SEGS VAL E (mkSST pc regs fregs mem resv (mkFacts A C AL)) ms.
Proof.
intros fxc E pc regs fregs mem resv A c C AL ms HS. unfold st_ok_pi in *.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
assert (H9' : facts_ok E (mkFacts A (c :: C) AL)) by exact H9.
change (facts_ok E (mkFacts A C AL)).
destruct H9' as (HA & HC & HL). split; [exact HA|]. split; [exact (proj2 HC) | exact HL].
Qed.

(* the symbolic state moves to the float state a float-form callee returns at (YCbqGcall.st_ok_restrict_xfx): the
   re-seated machine state is in mkst form, so its float half is the float state's *)
Lemma pjw_xfx : forall (fx1 fx2 : YK11.FPState) E ss (H : word -> bool) regs pc mem,
  st_ok_pi (fx := fx1) SEGS VAL E ss (restrict H (@YK11.mkst fx1 regs pc mem (YK11.seg_rom SEGS))) ->
  st_ok_pi (fx := fx2) SEGS VAL E ss (restrict H (@YK11.mkst fx2 regs pc mem (YK11.seg_rom SEGS))).
Proof.
intros fx1 fx2 E ss H regs pc mem HS. unfold st_ok_pi in *.
exact (YCbqGcall.st_ok_restrict_xfx fx1 fx2 SEGS E _ H regs pc mem HS).
Qed.

(* ---- what pj_write's own steps leave: every byte outside its frame and the ESTACK window below it is kept ---- *)
Definition pjw_wr (sp a : Z) : Prop := sp - (64 + ESTACK) <= a < sp.

(* a run's frame (its regions' write windows inside P) keeps the bytes outside P *)
Lemma pjw_keep_frame : forall (H : word -> bool) E rs (m0 m1 m2 : word -> option byte) (P : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m1 a = aview SEGS H m0 a) ->
  frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
  (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
intros H E rs m0 m1 m2 P K1 Hfr Hsub a Ha Hp. rewrite <- (K1 a Ha Hp).
apply (aview_eq_of SEGS). apply Hfr. rewrite unsigned_lit_small by exact Ha. intros Hw. exact (Hp (Hsub a Hw)).
Qed.

Lemma pjw_vm_keep : forall (H H' : word -> bool) (m m' : word -> option byte) a (w : nat) x,
  (forall j, (j < w)%nat -> aview SEGS H' m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  val_mem SEGS (mrestrict H m) a w x -> val_mem SEGS (mrestrict H' m') a w x.
Proof. intros H H' m m' a w x Hk Hv j Hj. rewrite (mbyte_of_aview SEGS H H' m m' _ (Hk j Hj)). exact (Hv j Hj). Qed.

(* ---- THE READS OF prh_ledger / prh_glob OF THIS FILE: PRH_Base's named projections, and pjw_ledger_keep's walk
   over the seven cells of prh_glob (#102: g_most and g_own_ran_out appended, prh_pst's sixth and seventh) ---- *)
Lemma pjw_led_hb : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own a k,
  prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B ly S) /\ In (a - cf_head) Hp /\ a mod 16 = 0 /\
  val_mem SEGS (mrestrict (w_H W) mem) (a - cf_head) 8 k.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin.
pose proof HL as HF. apply prh_ledger_blocks in HF.
rewrite Forall_forall in HF. exact (HF (a, k) Hin).
Qed.

Lemma pjw_led_cnt : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own,
  prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own -> 0 <= cnt < 2 ^ 64.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own HL.
apply prh_ledger_bounds in HL. destruct HL as (_ & _ & Hc & _). exact Hc.
Qed.

Lemma pjw_led_nodup : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own,
  prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own -> NoDup (map fst Lam).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own HL.
apply prh_ledger_nodup in HL. exact HL.
Qed.

(* the ledger's bytes (the statics in the image, the harness heads in blocks) all lie below YM05.alloc_ceiling + 8 *)
Lemma pjw_ledger_keep : forall ly S Hp W md mem mem' Lam peak cnt fail ran most own (P : Z -> Prop),
  ARx ly S Hp W mem md ->
  prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, 0 <= a < YM05.alloc_ceiling + 8 -> ~ P a) ->
  prh_ledger (PI := prh_img_A) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W md mem mem' Lam peak cnt fail ran most own P HAR (HG & HND & HHB & HPm) HK HP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HS : forall b (w : nat) j, In (b, Z.of_nat w) (@prh_pst prh_img_A) -> (j < w)%nat ->
  aview SEGS (w_H W) mem' (b + Z.of_nat j) = aview SEGS (w_H W) mem (b + Z.of_nat j)).
{ intros b w j Hin Hj.
  destruct (PST_ok (b + Z.of_nat j)) as [Himg _].
  { apply Exists_exists. exists (b, Z.of_nat w). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (segs_low _ Himg) as Hl. apply HK; [unfold kLowMemEnd in Hl; lia | apply HP; unfold kLowMemEnd in Hl; lia]. }
destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & Gr).
split; [|split; [exact HND | split; [|exact HPm]]].
- split; [refine (pjw_vm_keep _ _ _ _ _ _ _ _ G1); intros j Hj; eapply (HS _ _ j); [unfold prh_pst; left; reflexivity | exact Hj]|].
  split; [refine (pjw_vm_keep _ _ _ _ _ _ _ _ G2); intros j Hj; eapply (HS _ _ j);
    [unfold prh_pst; right; left; reflexivity | exact Hj]|].
  split; [refine (pjw_vm_keep _ _ _ _ _ _ _ _ G3); intros j Hj; eapply (HS _ _ j);
    [unfold prh_pst; right; right; left; reflexivity | exact Hj]|].
  split; [refine (pjw_vm_keep _ _ _ _ _ _ _ _ G4); intros j Hj; eapply (HS _ _ j);
    [unfold prh_pst; right; right; right; left; reflexivity | exact Hj]|].
  split; [refine (pjw_vm_keep _ _ _ _ _ _ _ _ G5); intros j Hj; eapply (HS _ _ j);
    [unfold prh_pst; right; right; right; right; left; reflexivity | exact Hj]|].
  split; [split; [refine (pjw_vm_keep _ _ _ _ _ _ _ _ G6); intros j Hj; eapply (HS _ _ j);
    [unfold prh_pst; right; right; right; right; right; left; reflexivity | exact Hj] | exact G6r]|].
  split; [split; [refine (pjw_vm_keep _ _ _ _ _ _ _ _ G7); intros j Hj; eapply (HS _ _ j);
    [unfold prh_pst; right; right; right; right; right; right; left; reflexivity | exact Hj] | exact G7r]|].
  exact Gr.
- rewrite Forall_forall in HHB |- *. intros [a k] Hin. destruct (HHB _ Hin) as (H1 & H2 & H3 & H4 & H5).
  cbn [fst snd] in *.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR H2) as (Hb16 & Hb4096 & Hbc & _).
  pose proof cf_head_nonneg as Hc0.
  assert (Hrq : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  refine (pjw_vm_keep _ _ _ _ _ _ _ _ H5). intros j Hj. apply HK; [lia | apply HP; lia].
Qed.

(* the tree's footprint: below YM05.alloc_ceiling (a harness block or a fake frame) or at or above the entry sp (the real
   stack, the kit v-bound), never in the image *)
Lemma pjw_foot_ok : forall STK ly S Hp W regs mem md ch Lam peak cnt fail ran most own v D,
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch ->
  prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/ (exists x y, In (x, y) Lam /\ x <= v /\ v + 56 <= x + y) \/
   prhWriter_in_frame ly S v) ->
  (forall a k, In (a, k) D -> In (a, k) Lam) ->
  forall x, pj_footR v D x -> 0 <= x < 2 ^ 47 /\ ~ in_img SEGS x /\ (x < YM05.alloc_ceiling \/ spZ regs <= x).
Proof.
intros STK ly S Hp W regs mem md ch Lam peak cnt fail ran most own v D HPRE (HG & HND & HHB & HPm) HLOC HDL x Hx.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HBLK : forall a k y, In (a, k) Lam -> a <= y < a + k -> 0 <= y < 2 ^ 47 /\ ~ in_img SEGS y /\ y < YM05.alloc_ceiling).
{ intros a k y Hin Hy. rewrite Forall_forall in HHB. destruct (HHB _ Hin) as (Hk & Hab & _). cbn [fst snd] in *.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
  pose proof cf_head_nonneg.
  assert (Hrq : k + cf_head <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  split; [lia|]. split; [|lia].
  refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md y HAR _)). left.
  exists (a - cf_head), (k + cf_head). split; [exact Hab | lia]. }
destruct Hx as [Hv | ([a k] & Hb & Hh)].
- destruct HLOC as [[H1 H2] | [(x0 & y0 & Hin & H1 & H2) | (cid & pos & Hin & H1 & H2)]].
  + split; [lia|]. split; [| right; lia]. intros Himg. pose proof (segs_low x Himg). unfold kLowMemEnd in *; lia.
  + destruct (HBLK x0 y0 x Hin ltac:(lia)) as (A1 & A2 & A3). auto.
  + destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (F1 & F2 & _).
    split; [lia|]. split; [|left; lia].
    refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md x HAR _)). right. left.
    exists cid, pos. split; [exact Hin | lia].
- unfold pj_holdsR in Hh. cbn [fst snd] in Hh. destruct (HBLK a k x (HDL a k Hb) Hh) as (A1 & A2 & A3). auto.
Qed.

(* The kit's location premise of write_value (PRH_FnWriter.v twrite_value_specX) at write_value's entry sp below pj_write's,
   from pj_write's (both carry the v-bound), with no buffer yet (buf = 0: a harness block's base is not 0) *)
Lemma pjw_loc : forall ly S Hp W mem md Lam peak cnt fail ran most own v sp0 sp1,
  ARx ly S Hp W mem md -> prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own -> sp1 <= sp0 ->
  ((sp0 <= v /\ v + 56 <= ly_stk_hi ly) \/ (exists x y, In (x, y) Lam /\ x <= v /\ v + 56 <= x + y) \/
   prhWriter_in_frame ly S v) ->
  ((sp1 <= v /\ v + 56 <= ly_stk_hi ly) \/ (exists x y, In (x, y) Lam /\ x <> 0 /\ x <= v /\ v + 56 <= x + y) \/
   prhWriter_in_frame ly S v).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own v sp0 sp1 HAR (HG & HND & HHB & HPm) Hsp HLOC.
destruct HLOC as [[H1 H2] | [(x & y & Hin & H1 & H2) | Hf]]; [left; lia | right; left | right; right; exact Hf].
exists x, y. split; [exact Hin|]. split; [|lia].
rewrite Forall_forall in HHB. destruct (HHB _ Hin) as (Hk & Hab & _). cbn [fst snd] in *.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & _).
pose proof cf_head_nonneg. lia.
Qed.

(* a shadow address of a byte below 2 ^ 47 lies below YM05.alloc_ceiling *)
Lemma pjw_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= SHADOW_OFF + x / 8 < YM05.alloc_ceiling.
Proof.
intros x Hx. pose proof asan_consts as (C1 & _).
assert (0 <= x / 8) by (apply Z.div_pos; lia). assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
unfold SHADOW_OFF. lia.
Qed.

(* the tree's blocks stay visible when every byte below YM05.alloc_ceiling is kept *)
Lemma pjw_tree_vis_keep : forall (W W' : world SEGS) mem mem' D (P : Z -> Prop),
  prhWriter_tree_vis W mem D ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> ~ P a) ->
  prhWriter_tree_vis W' mem' D.
Proof.
intros W W' mem mem' D P HT HK HP a k Hin. destruct (HT a k Hin) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the granule round-up of the block's end is at least its end (tree_vis_cf's bound) *)
pose proof (Z.div_mod (a + k + 7) 8 ltac:(lia)) as Dg. pose proof (Z.mod_pos_bound (a + k + 7) 8 ltac:(lia)) as Mg.
assert (HKa : forall y, 0 <= y < YM05.alloc_ceiling -> aview SEGS (w_H W') mem' y = aview SEGS (w_H W) mem y)
  by (intros y Hy; apply HK; [lia | apply HP; lia]).
split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4|]. split; [|split].
- apply (range_addressable_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W') mem') SHADOW_OFF a k); [|exact T5].
  intros x Hx. apply HKa. unfold shadow_of_addr. apply pjw_shadow_low. lia.
- intros Hk0 s Hs. assert (Hsb : 0 <= s < YM05.alloc_ceiling).
  { unfold shadow_addr in Hs.
    pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
    pose proof (Z.div_mod (a + k - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a + k - 1) 8 ltac:(lia)).
    pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (SHADOW_OFF + (a + k - 1) / 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + k - 1) / 8) 8 ltac:(lia)).
    unfold SHADOW_OFF in *. lia. }
  rewrite (HKa s Hsb). exact (T6 Hk0 s Hs).
- intros x Hx. rewrite (HKa x) by lia. exact (T7 x Hx).
Qed.

(* v's shadow stays addressable when every byte below YM05.alloc_ceiling is kept *)
Lemma pjw_ra_keep : forall (W W' : world SEGS) mem mem' v (P : Z -> Prop),
  0 <= v -> v + 56 <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> ~ P a) ->
  range_addressable (aview SEGS (w_H W') mem') SHADOW_OFF v 56.
Proof.
intros W W' mem mem' v P Hv0 Hv1 HR HK HP. pose proof asan_consts as (C1 & _).
apply (range_addressable_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W') mem') SHADOW_OFF v 56); [|exact HR].
intros x Hx. unfold shadow_of_addr. pose proof (pjw_shadow_low x ltac:(lia)) as Hs.
apply HK; [lia | apply HP; lia].
Qed.

(* the tree is kept when its footprint (non-image, outside P) is *)
Lemma pjw_nodeR_keep : forall (W W' : world SEGS) mem mem' Lam v t D (P : Z -> Prop),
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v t D ->
  (forall x, pj_footR v D x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ ~ P x) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v t D.
Proof.
intros W W' mem mem' Lam v t D P HN Hf HK. apply (pj_nodeR_frame SEGS t _ _ _ _ _ HN).
apply pjw_agree_of_aview.
- intros x Hx. destruct (Hf x Hx) as (A1 & A2 & _). auto.
- intros x Hx. destruct (Hf x Hx) as (A1 & _ & A3). apply HK; assumption.
Qed.

(* the read-only view is image bytes, all below YM05.alloc_ceiling *)
Lemma pjw_arodata_keep : forall (W W' : world SEGS) mem mem' (P : Z -> Prop),
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> ~ P a) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem').
Proof.
intros W W' mem mem' P HRO HK HP a Hro Ho He. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(s & Hs & _ & Hlo & Hhi) | Hr]; [exists s; split; [exact Hs | lia] | apply pa_relro_img; exact Hr]).
pose proof (segs_low a Himg) as Hl.
rewrite HK; [exact (HRO a Hro Ho He) | unfold kLowMemEnd in Hl; lia | apply HP; unfold kLowMemEnd in Hl; lia].
Qed.

(* and through a journal whose footprint spares the sink: the image clause keeps the read-only band (no static of
   alloc.c lies in it, HPSTRO). Over any world relation R (the walk's journals are at wle' after write_value, a
   crossing call); the image clause read BY NAME (ajxR_img) *)
Lemma pjw_arodata_kept : forall (R : world SEGS -> world SEGS -> Prop) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W2
    mem2 md2 k,
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W2 mem2 md2 k ->
  (forall a, fp_spares (SK := SK) FP a) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W2 mem2 md2 k HJ Hsp HRO a Hro Ho He.
pose proof (ajxR_img HJ) as F3.
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(s & Hs & _ & Hlo & Hhi) | Hr]; [exists s; split; [exact Hs | lia] | apply pa_relro_img; exact Hr]).
rewrite (F3 a Himg Ho He (HPSTRO a Hro) (Hsp a)). exact (HRO a Hro Ho He).
Qed.

(* the struct after __asan_memset: no buffer, no text, cap 0, not failed *)
Lemma pjw_out0 : forall (W : world SEGS) m o Lam cnt fail,
  o mod 8 = 0 -> (forall i, 0 <= i < 32 -> aview SEGS (w_H W) m (o + i) = Some 0) ->
  prhWriter_out W m Lam o 0 (WriterApp.w0 cnt fail).
Proof.
intros W m o Lam cnt fail Ho Hz. unfold prhWriter_out, WriterApp.w0.
cbn [WriterApp.w_cap WriterApp.w_text WriterApp.w_failed length Z.of_nat].
split; [exact Ho|]. split; [lia|]. split; [lia|].
split; [apply pjw_zero; intros i Hi; apply Hz; lia|].
split; [apply pjw_zero; intros i Hi; replace (o + 8 + i) with (o + (8 + i)) by lia; apply Hz; lia|].
split; [apply pjw_zero; intros i Hi; replace (o + 16 + i) with (o + (16 + i)) by lia; apply Hz; lia|].
split; [apply pjw_zero; intros i Hi; replace (o + 24 + i) with (o + (24 + i)) by lia; apply Hz; lia|].
split; [left; reflexivity|]. split; [constructor|].
left. repeat split.
Qed.

(* ---- THE LIVE ROOM AT EACH EVENT (the batch kit's PRH_Base.prh_live_evs, :619) of write_value's and put's runs, from pj_write's
   entry budget blocks_bytes S + LIVE_pj_write t p <= LIVE_MAX (the batch kit's PRH_FnWriter.v:810): along the all-granted run the
   live list is the entry's plus the current buffer (each grow's HRe frees the buffer it replaces), and every
   capacity of the run stays in the doubling chain below R = newcap 0 (len (wdoc t p) + 1) (S7a_WriterLive's
   prhWL_chain_step / prhWL_chain_run). ---- *)
Lemma pjw_rm1_sum : forall z l, In z l ->
  fold_right Z.add 0 (PresetReqAt.rm1 z l) = fold_right Z.add 0 l - z.
Proof.
intros z l. induction l as [|y l IH]; intros Hin; [destruct Hin|].
cbn [PresetReqAt.rm1 fold_right]. destruct (Z.eqb_spec y z) as [Ey|Hne]; [lia|].
destruct Hin as [Ey | Hin]; [exfalso; exact (Hne Ey)|].
cbn [fold_right]. rewrite (IH Hin). lia.
Qed.

(* a put that does not grow keeps the capacity *)
Lemma pjw_put1_cap : forall st b, prhWriter_grows st b = false ->
  WriterApp.w_cap (WriterApp.put1 st b) = WriterApp.w_cap st.
Proof.
intros st b Hg. unfold prhWriter_grows, prhWriter_need in Hg. unfold WriterApp.put1. cbv zeta.
apply andb_false_iff in Hg. destruct Hg as [Hg | Hg].
- rewrite Hg. reflexivity.
- apply Z.ltb_ge in Hg. destruct (WriterApp.w_failed st =? 0); cbn [negb]; [|reflexivity].
  rewrite (proj2 (Z.leb_le _ _) Hg). reflexivity.
Qed.

Lemma pjw_live_run : forall (R B0 : Z) P st (l : list Z),
  0 < R -> 0 <= cf_head -> 0 <= WriterApp.w_cap st ->
  (exists m : nat, R = prhWL_base (WriterApp.w_cap st) * 2 ^ Z.of_nat m) ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat P)) + 1 <= R ->
  fold_right Z.add 0 l = B0 + prhWriter_buf_bytes st ->
  (WriterApp.w_cap st <> 0 -> In (WriterApp.w_cap st + cf_head) l) ->
  B0 + 2 * (R + cf_head) <= LIVE_MAX ->
  forall j e, nth_error (prhWriter_evs [] st P) j = Some e ->
    fold_right Z.add 0 (PresetReqAt.hlive_from l (firstn j (prhWriter_evs [] st P))) + prh_ev_req e <= LIVE_MAX.
Proof.
intros R B0 P. induction P as [|b P IH]; intros st l HR Hh Hc0 HRm HRl Hl Hin HB j e Hj.
{ destruct j; discriminate Hj. }
(* a capacity in the chain of R lies below R, and its base is positive *)
assert (HbR : forall c, 0 <= c -> (exists m : nat, R = prhWL_base c * 2 ^ Z.of_nat m) -> c <= R /\ 0 < prhWL_base c).
{ intros c Hc [m Hm]. unfold prhWL_base in Hm |- *.
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat m) ltac:(lia) ltac:(lia)) as Hp.
  destruct (Z.eqb_spec c 0) as [E|E].
  - subst c. cbn [Z.eqb] in Hm |- *. split; lia.
  - cbv iota in Hm |- *. split; nia. }
destruct (HbR _ Hc0 HRm) as (HcR & Hb0).
destruct (prhWriter_grows st b) eqn:Eg.
- destruct (WriterApp.w_cnt st =? WriterApp.w_fail st) eqn:Ecf.
  + (* the allocation set to fail: no event, and the writer is failed after it *)
    assert (Hf : WriterApp.w_failed (prhWriter_put1 true st b) <> 0)
      by (unfold prhWriter_put1; rewrite Eg, Ecf; cbn; lia).
    cbn [prhWriter_evs] in Hj. rewrite Eg, Ecf in Hj. cbn [hd tl orb app] in Hj.
    rewrite (prhWriter_evs_failed P [] _ Hf) in Hj. destruct j; discriminate Hj.
  + (* a granted grow: its event, then the rest from the grown writer *)
    assert (Est : prhWriter_put1 true st b =
                  WriterApp.mkW 0 (WriterApp.w_text st ++ b)
                    (WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b))
                    ((WriterApp.w_cnt st + 1) mod 2 ^ 64) (WriterApp.w_fail st)
                    (WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b)]))
      by (unfold prhWriter_put1; rewrite Eg, Ecf; reflexivity).
    pose proof (prhWL_chain_step R 1 st (prhWriter_put1 true st b) b P HR ltac:(lia) (conj HRm HRl)
                  (prhWL_hput1_step true st b)) as (HRm' & HRl').
    rewrite Est in HRm', HRl'. cbn [WriterApp.w_cap WriterApp.w_text] in HRm', HRl'.
    assert (Hcp : 0 < WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b)).
    { rewrite prhWL_newcap_eq.
      pose proof (prhWL_dbl_ge_c 64 (prhWL_base (WriterApp.w_cap st)) (prhWriter_need st b) ltac:(lia)). lia. }
    destruct (HbR (WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b)) ltac:(lia) HRm') as (Hc'R & _).
    assert (Hcn : WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b) <> 0) by lia.
    cbn [prhWriter_evs] in Hj |- *. rewrite Eg, Ecf in Hj |- *. cbn [hd tl orb negb app] in Hj |- *.
    rewrite Est in Hj |- *.
    destruct j as [|j].
    * cbn [nth_error] in Hj. injection Hj as <-. cbn [firstn PresetReqAt.hlive_from fold_left].
      rewrite Hl. unfold prhWriter_ev, prhWriter_buf_bytes.
      destruct (Z.eqb_spec (WriterApp.w_cap st) 0); cbn [prh_ev_req]; lia.
    * cbn [nth_error] in Hj. cbn [firstn].
      apply (IH _ (PresetReqAt.hstep l (prhWriter_ev st b))).
      -- exact HR.
      -- exact Hh.
      -- cbn [WriterApp.w_cap]. lia.
      -- exact HRm'.
      -- exact HRl'.
      -- unfold prhWriter_ev, prhWriter_buf_bytes. cbn [WriterApp.w_cap].
         rewrite (proj2 (Z.eqb_neq _ 0) Hcn).
         destruct (Z.eqb_spec (WriterApp.w_cap st) 0) as [E0|En].
         ++ cbn [PresetReqAt.hstep fold_right]. rewrite Hl. unfold prhWriter_buf_bytes.
            rewrite (proj2 (Z.eqb_eq _ 0) E0). lia.
         ++ cbn [PresetReqAt.hstep fold_right]. rewrite (pjw_rm1_sum _ _ (Hin En)), Hl.
            unfold prhWriter_buf_bytes. rewrite (proj2 (Z.eqb_neq _ 0) En). lia.
      -- intros _. cbn [WriterApp.w_cap]. unfold prhWriter_ev.
         destruct (WriterApp.w_cap st =? 0); cbn [PresetReqAt.hstep]; left; reflexivity.
      -- exact HB.
      -- exact Hj.
- (* no grow: no event, the capacity kept *)
  cbn [prhWriter_evs] in Hj |- *. rewrite Eg in Hj |- *. cbv iota in Hj |- *.
  pose proof (pjw_put1_cap st b Eg) as Ecap.
  pose proof (prhWL_chain_step R 1 st (WriterApp.put1 st b) b P HR ltac:(lia) (conj HRm HRl)
                (prhWL_put1_step st b)) as (HRm' & HRl').
  apply (IH (WriterApp.put1 st b) l); try assumption.
  + rewrite Ecap. exact Hc0.
  + unfold prhWriter_buf_bytes. rewrite Ecap. exact Hl.
  + rewrite Ecap. exact Hin.
Qed.

(* the live list of a state is its live requests, so its sum is blocks_bytes (a Theorem Labs lane's blocks_bytes_zsum's body) *)
Lemma pjw_bb_live : forall S, fold_right Z.add 0 (map snd (YG01.blocks S)) = blocks_bytes S.
Proof.
intros S. unfold blocks_bytes, YG01.blocks. generalize (st_chunks S) as l.
induction l as [|k l IH]; [reflexivity|].
cbn [List.filter]. destruct (is_alloc k) eqn:Ek; cbn [map fold_right snd]; rewrite Ek, <- IH; reflexivity.
Qed.

(* write_value's live room (the batch kit's twrite_value_specX, PRH_FnWriter.v:745) from pj_write's entry budget (:810) *)
Lemma pjw_live0 : forall S cnt fail t p,
  0 <= cf_head ->
  blocks_bytes S + LIVE_pj_write t p <= LIVE_MAX ->
  Z.of_nat (length (WriterValue.wdoc t p)) + 1 <= prhWriter_WMAX ->
  prh_live_evs S (prhWriter_evs [] (WriterApp.w0 cnt fail) (WriterValue.wvpieces t p 0)).
Proof.
intros S cnt fail t p Hh HB HW j e Hj. unfold prh_live_at.
pose proof (prhWL_dbl_ge_y 64 4096 (Z.of_nat (length (WriterValue.wdoc t p)) + 1) ltac:(lia)
  ltac:(change (2 ^ Z.of_nat 64) with 18446744073709551616; change prhWriter_WMAX with 268435456 in HW; lia)) as HRy.
destruct (prhWL_dbl_pow 64 4096 (Z.of_nat (length (WriterValue.wdoc t p)) + 1)) as [k Hk].
assert (HL : (length (concat (WriterValue.wvpieces t p 0)) <= length (WriterValue.wdoc t p))%nat)
  by (unfold WriterValue.wdoc, WriterValue.wdpieces; rewrite concat_app, length_app; lia).
apply (pjw_live_run (WriterSpec.dbl 64 4096 (Z.of_nat (length (WriterValue.wdoc t p)) + 1)) (blocks_bytes S)).
- lia.
- exact Hh.
- cbn [WriterApp.w0 WriterApp.w_cap]. lia.
- exists k. exact Hk.
- cbn [WriterApp.w0 WriterApp.w_text length Z.of_nat]. lia.
- unfold YGcfRoom.room_of_cf. cbn [PresetRoom.rs_live]. rewrite pjw_bb_live.
  unfold prhWriter_buf_bytes. cbn [WriterApp.w0 WriterApp.w_cap Z.eqb]. lia.
- intros Hc. exfalso. apply Hc. reflexivity.
- unfold LIVE_pj_write in HB. exact HB.
- exact Hj.
Qed.

(* put's live room after write_value (the batch kit's tput_specX, PRH_FnWriter.v:471), from pj_write's entry budget: the writer
   write_value left is in the doubling chain of pj_write's final capacity with the newline still to come, and its
   buffer is the block write_value's run added to the entry's live list *)
Lemma pjw_live_put : forall S S3 ok1 cnt fail t,
  0 <= cf_head ->
  blocks_bytes S + LIVE_pj_write t true <= LIVE_MAX ->
  Z.of_nat (length (WriterValue.wdoc t true)) + 1 <= prhWriter_WMAX ->
  blocks_bytes S3 = blocks_bytes S +
    prhWriter_buf_bytes (prhWriter_putN ok1 (WriterApp.w0 cnt fail) (WriterValue.wvpieces t true 0)) ->
  (WriterApp.w_cap (prhWriter_putN ok1 (WriterApp.w0 cnt fail) (WriterValue.wvpieces t true 0)) <> 0 ->
     In (WriterApp.w_cap (prhWriter_putN ok1 (WriterApp.w0 cnt fail) (WriterValue.wvpieces t true 0)) + cf_head)
       (map snd (YG01.blocks S3))) ->
  prh_live_evs S3
    (prhWriter_evs [] (prhWriter_putN ok1 (WriterApp.w0 cnt fail) (WriterValue.wvpieces t true 0)) [[10]]).
Proof.
intros S S3 ok1 cnt fail t Hh HB HW HB3 HIN j e Hj. unfold prh_live_at.
pose proof (prhWL_dbl_ge_y 64 4096 (Z.of_nat (length (WriterValue.wdoc t true)) + 1) ltac:(lia)
  ltac:(change (2 ^ Z.of_nat 64) with 18446744073709551616; change prhWriter_WMAX with 268435456 in HW; lia)) as HRy.
destruct (prhWL_dbl_pow 64 4096 (Z.of_nat (length (WriterValue.wdoc t true)) + 1)) as [k Hk].
assert (HL : (length (WriterValue.wdoc t true) = length (concat (WriterValue.wvpieces t true 0)) + 1)%nat)
  by (unfold WriterValue.wdoc, WriterValue.wdpieces; rewrite concat_app, length_app; cbn; lia).
destruct (prhWL_chain_run (WriterSpec.dbl 64 4096 (Z.of_nat (length (WriterValue.wdoc t true)) + 1)) 2 ok1
            (WriterValue.wvpieces t true 0) (WriterApp.w0 cnt fail) ltac:(lia) ltac:(lia)
            ltac:(split; [exists k; exact Hk | cbn [WriterApp.w0 WriterApp.w_text length Z.of_nat]; lia]))
  as ((m & Hm) & Hl1).
assert (Hb1 : 0 < prhWL_base (WriterApp.w_cap (prhWriter_putN ok1 (WriterApp.w0 cnt fail) (WriterValue.wvpieces t true 0))))
  by (apply (prhWL_pos_of_mul _ m); rewrite <- Hm; lia).
apply (pjw_live_run (WriterSpec.dbl 64 4096 (Z.of_nat (length (WriterValue.wdoc t true)) + 1)) (blocks_bytes S)).
- lia.
- exact Hh.
- unfold prhWL_base in Hb1.
  destruct (Z.eqb_spec (WriterApp.w_cap (prhWriter_putN ok1 (WriterApp.w0 cnt fail) (WriterValue.wvpieces t true 0))) 0)
    as [E|E]; [lia | cbv iota in Hb1; lia].
- exists m. exact Hm.
- cbn [concat app length Z.of_nat]. lia.
- unfold YGcfRoom.room_of_cf. cbn [PresetRoom.rs_live]. rewrite pjw_bb_live. exact HB3.
- exact HIN.
- unfold LIVE_pj_write in HB. exact HB.
- exact Hj.
Qed.

(* the allocator bytes under a permutation of the block list *)
Lemma pjw_bsum_perm : forall l1 l2, Permutation l1 l2 -> bsum l1 = bsum l2.
Proof.
intros l1 l2 H. induction H; unfold bsum in *; cbn [fold_right] in *; lia.
Qed.

Lemma pjw_bb_grow : forall ly1 S1 ly2 S2 x,
  Permutation (ablocks B ly2 S2) (x :: ablocks B ly1 S1) -> blocks_bytes S2 = blocks_bytes S1 + snd x.
Proof.
intros ly1 S1 ly2 S2 x Hp. rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly1 S1).
rewrite (pjw_bsum_perm _ _ Hp). unfold bsum. cbn [fold_right]. lia.
Qed.

Definition pjw_pair_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* a list with two occurrences of x splits around both *)
Lemma pjw_two_in_split : forall (x : Z * Z) (l : list (Z * Z)),
  (2 <= count_occ pjw_pair_dec l x)%nat ->
  exists l1 l2 l3, l = l1 ++ x :: l2 ++ x :: l3.
Proof.
intros x l. induction l as [|a l IH]; cbn [count_occ]; [lia|].
destruct (pjw_pair_dec a x) as [->|Hne]; intros Hc.
- assert (Hin : In x l) by (apply (count_occ_In pjw_pair_dec); lia).
  apply in_split in Hin as (m1 & m2 & ->). exists [], m1, m2. reflexivity.
- destruct (IH Hc) as (l1 & l2 & l3 & ->). exists (a :: l1), l2, l3. reflexivity.
Qed.

(* a block at the head of a permutation of the later block list is NOT a block of the earlier one: two copies of a
   nonempty block would break the allocator's pairwise disjointness *)
Lemma pjw_fresh_block : forall ly2 S2 Hp2 W2 mem2 md2 x l,
  ARx ly2 S2 Hp2 W2 mem2 md2 -> Permutation (ablocks B ly2 S2) (x :: l) -> 0 < req_size (snd x) ->
  ~ In x l.
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 x l HAR Hperm Hpos Hin.
assert (Hx2 : In x (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (Hc : (2 <= count_occ pjw_pair_dec (ablocks B ly2 S2) x)%nat).
{ rewrite (proj1 (Permutation_count_occ pjw_pair_dec _ _) Hperm x).
  cbn [count_occ]. destruct (pjw_pair_dec x x) as [_|Hne]; [|exfalso; exact (Hne eq_refl)].
  pose proof (proj1 (count_occ_In pjw_pair_dec l x) Hin). lia. }
destruct (pjw_two_in_split x _ Hc) as (m1 & m2 & m3 & Hsp).
destruct x as [p nn]. cbn [fst snd] in *.
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 p nn HAR Hx2) as (_ & _ & _ & _ & _ & Hpw).
pose proof (YCbq.pairwise_In2 zdisjoint
  (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B ly2 S2))
  (p, req_size nn) (p, req_size nn)
  (map (fun b : Z * Z => (fst b, req_size (snd b))) m1)
  (map (fun b : Z * Z => (fst b, req_size (snd b))) m2)
  (map (fun b : Z * Z => (fst b, req_size (snd b))) m3) Hpw) as Hd.
rewrite Hsp, !map_app in Hd. cbn [map] in Hd. rewrite ?map_app in Hd. cbn [map] in Hd. specialize (Hd eq_refl).
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma pjw_bb_same : forall ly1 S1 ly2 S2,
  Permutation (ablocks B ly2 S2) (ablocks B ly1 S1) -> blocks_bytes S2 = blocks_bytes S1.
Proof.
intros ly1 S1 ly2 S2 Hp. rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly1 S1).
exact (pjw_bsum_perm _ _ Hp).
Qed.

(* the live bytes after write_value's run from the empty writer (S7a_WriterRet's prhWriter_blk / prhWriter_blk_bb):
   the entry's plus the buffer, which is a live block of the end state *)
Lemma pjw_blk_live : forall ly S Lam peak cnt fail ly' S' Lam' peak' buf' st',
  prhWriter_blk B ly S Lam peak 0 (WriterApp.w0 cnt fail) ly' S' Lam' peak' buf' st' ->
  blocks_bytes S' = blocks_bytes S + prhWriter_buf_bytes st' /\
  (WriterApp.w_cap st' <> 0 -> In (WriterApp.w_cap st' + cf_head) (map snd (YG01.blocks S'))).
Proof.
intros ly S Lam peak cnt fail ly' S' Lam' peak' buf' st' Hb. split.
- assert (E : blocks_bytes S' - prhWriter_buf_bytes st' =
              blocks_bytes S - prhWriter_buf_bytes (WriterApp.w0 cnt fail))
    by (eapply prhWriter_blk_bb; [cbn; lia | exact Hb]).
  change (prhWriter_buf_bytes (WriterApp.w0 cnt fail)) with 0 in E. lia.
- intros Hc. destruct Hb as [(Ec & _) | (_ & l1 & l2 & b1 & b2 & _ & _ & _ & Hp)].
  + exfalso. apply Hc. rewrite Ec. reflexivity.
  + assert (Hin : In (buf' - cf_head, WriterApp.w_cap st' + cf_head) (ablocks B ly' S'))
      by (eapply Permutation_in; [apply Permutation_sym; exact Hp | left; reflexivity]).
    apply (in_map snd) in Hin. unfold ablocks in Hin. rewrite map_map in Hin. exact Hin.
Qed.

(* the writer struct and its buffer are kept when every byte below YM05.alloc_ceiling and the struct's 32 bytes are *)
Lemma pjw_out_keep : forall ly1 S1 Hp1 (W1 W2 : world SEGS) mem1 mem2 md1 Lam peak1 cnt1 fail1 ran1 most1 own1 o buf st
  (P : Z -> Prop),
  ARx ly1 S1 Hp1 W1 mem1 md1 ->
  prh_ledger (PI := prh_img_A) B ly1 S1 Hp1 W1 mem1 Lam peak1 cnt1 fail1 ran1 most1 own1 ->
  prhWriter_out W1 mem1 Lam o buf st ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> ~ P a) ->
  (forall a, o <= a < o + 32 -> 0 <= a < 2 ^ 64 /\ ~ P a) ->
  prhWriter_out W2 mem2 Lam o buf st.
Proof.
intros ly1 S1 Hp1 W1 W2 mem1 mem2 md1 Lam peak1 cnt1 fail1 ran1 most1 own1 o buf st P HAR HLEDx HO HK HP HOP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HO as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10).
assert (HKo : forall a (w : nat), o <= a -> a + Z.of_nat w <= o + 32 ->
  forall j, (j < w)%nat -> aview SEGS (w_H W2) mem2 (a + Z.of_nat j) = aview SEGS (w_H W1) mem1 (a + Z.of_nat j)).
{ intros a w Hlo Hhi j Hj. destruct (HOP (a + Z.of_nat j) ltac:(lia)) as [R1 R2]. apply HK; assumption. }
split; [exact O1|]. split; [exact O2|]. split; [exact O3|].
split; [refine (pjw_vm_keep _ _ _ _ _ _ _ _ O4); apply (HKo o 8%nat); lia|].
split; [refine (pjw_vm_keep _ _ _ _ _ _ _ _ O5); apply (HKo (o + 8) 8%nat); lia|].
split; [refine (pjw_vm_keep _ _ _ _ _ _ _ _ O6); apply (HKo (o + 16) 8%nat); lia|].
split; [refine (pjw_vm_keep _ _ _ _ _ _ _ _ O7); apply (HKo (o + 24) 4%nat); lia|].
split; [exact O8|]. split; [exact O9|].
destruct O10 as [Hz | (Hgrid & Hin & Hlen & (rest & Hr1 & Hr2) & Hsh)]; [left; exact Hz|].
pose proof HLEDx as (_ & _ & HHB & _). rewrite Forall_forall in HHB.
destruct (HHB _ Hin) as (Hk & Hab & _). cbn [fst snd] in Hk, Hab.
destruct (alx_blocks SEGS B ARx LAWS ly1 S1 Hp1 W1 mem1 md1 _ _ HAR Hab) as (_ & H4096 & Hc & _).
pose proof cf_head_nonneg.
assert (Hrq : WriterApp.w_cap st + cf_head <= req_size (WriterApp.w_cap st + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (WriterApp.w_cap st + cf_head) 0); lia).
assert (HKb : forall a, buf <= a < buf + WriterApp.w_cap st ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a) by (intros a Ha; apply HK; [lia | apply HP; lia]).
right. split; [exact Hgrid|]. split; [exact Hin|]. split; [exact Hlen|]. split.
- exists rest. split; [exact Hr1|]. unfold PRH_Base.bytes_at, garr8 in Hr2 |- *. intros j Hj.
  destruct (Hr2 j Hj) as [Hv Hb]. split; [|exact Hb].
  refine (pjw_vm_keep _ _ _ _ _ _ _ _ Hv). intros i Hi. apply HKb. cbn in Hj. lia.
- intros Hf0. destruct (Hsh Hf0) as [Hra0 Hhull]. split.
  + apply (range_addressable_agree (aview SEGS (w_H W1) mem1) (aview SEGS (w_H W2) mem2) SHADOW_OFF buf
      (WriterApp.w_cap st)); [|exact Hra0].
    intros x Hx. unfold shadow_of_addr. pose proof (pjw_shadow_low x ltac:(lia)) as Hs. apply HK; [lia | apply HP; lia].
  + intros s Hs. assert (Hsb : 0 <= s < YM05.alloc_ceiling).
    { unfold shadow_addr in Hs.
      pose proof (Z.div_mod buf 8 ltac:(lia)). pose proof (Z.mod_pos_bound buf 8 ltac:(lia)).
      pose proof (Z.div_mod (buf + WriterApp.w_cap st - 1) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (buf + WriterApp.w_cap st - 1) 8 ltac:(lia)).
      pose proof (Z.div_mod (SHADOW_OFF + buf / 8) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (SHADOW_OFF + buf / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SHADOW_OFF + (buf + WriterApp.w_cap st - 1) / 8) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (SHADOW_OFF + (buf + WriterApp.w_cap st - 1) / 8) 8 ltac:(lia)).
      unfold SHADOW_OFF in *. lia. }
    rewrite (HK s ltac:(lia) (HP s Hsb)). exact (Hhull s Hs).
Qed.

(* every JSON value writes at least one piece (the arms are a cons; a string's is spieces) *)
Lemma pjw_wvpieces_nonempty : forall t p d, WriterValue.wvpieces t p d <> [].
Proof.
intros [| | | txt z | s | items | members] p d; cbn [WriterValue.wvpieces]; try unfold WriterSpec.spieces; discriminate.
Qed.

(* ... so the whole document's piece list is nonempty too *)
Lemma pjw_wdpieces_nonempty : forall t p, WriterValue.wdpieces t p <> [].
Proof.
intros t p H. unfold WriterValue.wdpieces in H.
destruct (app_eq_nil _ _ H) as [H1 _]. exact (pjw_wvpieces_nonempty t p 0 H1).
Qed.

(* the writer's return relation (its outcomes ok named, the kit's prhWriter_ret_ok) moves to a later memory that keeps
   every byte below the ceiling and the struct *)
Lemma pjw_ret_keep : forall ok ly S Lam peak ran most own o buf st P ly' S' Hp' (W' : world SEGS) regs' mem' md'
    regs'' mem'' md'' (Q : Z -> Prop),
  ARx ly' S' Hp' W' mem' md' ->
  prhWriter_ret_ok (PI := prh_img_A) B ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Q a -> aview SEGS (w_H W') mem'' a = aview SEGS (w_H W') mem' a) ->
  (forall a, 0 <= a < YM05.alloc_ceiling + 8 -> ~ Q a) ->
  (forall a, o <= a < o + 32 -> 0 <= a < 2 ^ 64 /\ ~ Q a) ->
  prhWriter_ret_ok (PI := prh_img_A) B ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs'' mem'' md''.
Proof.
intros ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' regs'' mem'' md'' Q HAR HR HK HP8 HOFF.
unfold prhWriter_ret_ok in HR |- *. cbv zeta in HR |- *.
destruct HR as (ran' & buf' & Lam' & peak' & H1 & H2 & H3 & H4).
exists ran', buf', Lam', peak'.
split; [exact H1|]. split.
- eapply (pjw_out_keep ly' S' Hp' W' W' mem' mem'' md' Lam' peak' _ _ ran');
    [exact HAR | exact H3 | exact H2 | exact HK | intros a Ha; apply HP8; lia | exact HOFF].
- split; [| exact H4].
  eapply pjw_ledger_keep; [exact HAR | exact H3 | exact HK | exact HP8].
Qed.

(* THE TREE AT THE END OF pj_write: the walk's own journal (FP = []) keeps every byte of the node's footprint, so
   the kit's post states the ENTRY tree at the end memory. The node is on the real stack above the entry sp (the
   journal's high clause), in a harness block live at both states (its block clause) or in an entry fake frame
   (its frame clause); its blocks D are harness blocks of Lam, which the end ledger still holds. Over any world
   relation R (the walk's journal is at wle' after write_value); the clauses read BY NAME (ajxR_hi / _blk / _frm) *)
Lemma pjw_nodeR_end : forall (R : world SEGS -> world SEGS -> Prop) STK ly S Hp (W : world SEGS) regs mem md ch Lam
    peak cnt fail ran most own v t D ly' S' Hp' (W' : world SEGS) mem' md' k Lam' peak' cnt' fail' ran' most' own',
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch ->
  prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PI := prh_img_A) B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most' own' ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx R STK (spZ regs) []
    ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/ (exists x y, In (x, y) Lam /\ x <= v /\ v + 56 <= x + y) \/
   prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam) ->
  (forall a k0, In (a, k0) Lam -> In (a, k0) Lam') ->
  pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v t D.
Proof.
intros R STK ly S Hp W regs mem md ch Lam peak cnt fail ran most own v t D ly' S' Hp' W' mem' md' k Lam' peak' cnt'
  fail' ran' most' own'
  HPRE HLED HLED' HJ HNODE HLOC HDL HSUB.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hch.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (pjw_foot_ok STK ly S Hp W regs mem md ch Lam peak cnt fail ran most own v D HPRE HLED HLOC HDL) as FOOT.
pose proof (ajxR_hi HJ) as KEEPHI. pose proof (ajxR_blk HJ) as KEEPBLK. pose proof (ajxR_frm HJ) as KEEPFR.
(* a byte of a harness block of Lam is kept: its allocator block is live at both states and FP is empty *)
assert (HBK : forall a k0 x, In (a, k0) Lam -> a <= x < a + k0 ->
  aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x).
{ intros a k0 x Hin Hx.
  destruct (pjw_led_hb ly S Hp W mem Lam peak cnt fail ran most own a k0 HLED Hin) as (Hk0 & Hab & _).
  destruct (pjw_led_hb ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most' own' a k0 HLED' (HSUB a k0 Hin))
    as (_ & Hab' & _).
  assert (Hrq : k0 + cf_head <= req_size (k0 + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
  assert (Hib : 0 <= x - (a - cf_head) < req_size (k0 + cf_head)) by lia.
  replace x with (a - cf_head + (x - (a - cf_head))) by lia.
  apply (KEEPBLK (a - cf_head) (k0 + cf_head) (x - (a - cf_head)) Hab Hab' Hib).
  apply inFP_nil. }
apply (pj_nodeR_frame SEGS t _ _ _ _ _ HNODE).
apply pjw_agree_of_aview.
- intros x Hx. destruct (FOOT x Hx) as (F1 & F2 & _). split; [lia | exact F2].
- intros x Hx. destruct Hx as [Hhdr | ([a k0] & HbD & Hb)].
  + destruct HLOC as [(Hv1 & Hv2) | [(y0 & z0 & Hin & Hyv & Hvy) | (cid & pos & Hfr & Hf1 & Hf2)]].
    * apply KEEPHI; [pose proof (@YM05.alloc_ceiling_value rc) as HCV; lia | lia].
    * apply (HBK y0 z0 x Hin); lia.
    * apply (KEEPFR cid pos x Hfr);
        [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | apply inFP_nil].
  + unfold pj_holdsR in Hb. cbn [fst snd] in Hb. apply (HBK a k0 x (HDL a k0 HbD)); lia.
Qed.

(* a run that writes something and does not fail ends with a buffer: the first put of a nonempty piece grows from
   cap 0, and a grow either fails or leaves newcap, which is never 0 *)
Lemma pjw_cap_nz : forall ok cnt0 fail0 P, P <> [] ->
  WriterApp.w_failed (prhWriter_putN ok (WriterApp.w0 cnt0 fail0) P) = 0 ->
  WriterApp.w_cap (prhWriter_putN ok (WriterApp.w0 cnt0 fail0) P) <> 0.
Proof.
intros ok cnt0 fail0 P HP Hf. destruct P as [|b P']; [exfalso; exact (HP eq_refl)|].
assert (Hg : prhWriter_grows (WriterApp.w0 cnt0 fail0) b = true).
{ unfold prhWriter_grows, prhWriter_need, WriterApp.w0.
  cbn [WriterApp.w_failed WriterApp.w_cap WriterApp.w_text length Z.of_nat].
  rewrite Z.eqb_refl. cbn [andb]. apply Z.ltb_lt. lia. }
rewrite (prhW_putN_cons_grow ok _ b P' Hg) in Hf |- *.
destruct (prhW_put1_grow_cases (hd true ok) (WriterApp.w0 cnt0 fail0) b Hg)
  as [(_ & Hf1 & _) | [(_ & _ & Hf0 & _ & Hc1) | (_ & _ & Hf1 & _ & _)]].
- rewrite (prhW_putN_failed P' (tl ok) (prhWriter_put1 (hd true ok) (WriterApp.w0 cnt0 fail0) b) ltac:(lia)) in Hf. lia.
- destruct (prhW_cap_after P' (tl ok) (prhWriter_put1 (hd true ok) (WriterApp.w0 cnt0 fail0) b)) as [He | Hne];
  [rewrite He, Hc1; apply prhW_newcap_nz | exact Hne].
- rewrite (prhW_putN_failed P' (tl ok) (prhWriter_put1 (hd true ok) (WriterApp.w0 cnt0 fail0) b) ltac:(lia)) in Hf. lia.
Qed.

(* the tree's blocks are visible at any state of this allocator: a8's tree_vis_of_blocks_cf over the ledger *)
Lemma pjw_tree_vis_of : forall ly S Hp W mem md Lam peak cnt fail ran most own D,
  ARx ly S Hp W mem md ->
  prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a k, In (a, k) D -> In (a, k) Lam) ->
  prhWriter_tree_vis W mem D.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own D HAR (_ & _ & HHB & _) HDL.
unfold prhWriter_tree_vis.
apply (YGcfTreeVis.tree_vis_of_blocks_cf SEGS B ly S Hp W mem md D (S9_CF _ _ _ _ _ _ HAR)).
intros a k Hin. rewrite Forall_forall in HHB. destruct (HHB _ (HDL a k Hin)) as (_ & Hab & Hhp & _ & _).
cbn [fst snd] in Hab, Hhp. split; [exact Hab | exact Hhp].
Qed.

(* a run that does not fail wrote exactly its pieces *)
Lemma pjw_text_putN : forall P ok st, WriterApp.w_failed (prhWriter_putN ok st P) = 0 ->
  WriterApp.w_text (prhWriter_putN ok st P) = WriterApp.w_text st ++ concat P.
Proof.
induction P as [|b P IH]; intros ok st Hf; cbn [concat].
- rewrite app_nil_r. reflexivity.
- destruct (prhWriter_grows st b) eqn:Hg.
  + rewrite (prhW_putN_cons_grow ok st b P Hg) in Hf |- *.
    rewrite (IH (tl ok) _ Hf).
    assert (Htx : WriterApp.w_text (prhWriter_put1 (hd true ok) st b) = WriterApp.w_text st ++ b).
    { destruct (prhW_put1_grow_cases (hd true ok) st b Hg)
        as [(Ec & Hf1 & _) | [(Ec & Hok & _ & _ & _) | (Ec & Hok & Hf1 & _ & _)]].
      - exfalso.
        rewrite (prhW_putN_failed P (tl ok) (prhWriter_put1 (hd true ok) st b) ltac:(lia)) in Hf. lia.
      - unfold prhWriter_put1. rewrite Hg, Hok.
        destruct (Z.eqb_spec (WriterApp.w_cnt st) (WriterApp.w_fail st)) as [E | E]; [exfalso; exact (Ec E)|].
        cbn [WriterApp.w_text]. reflexivity.
      - exfalso.
        rewrite (prhW_putN_failed P (tl ok) (prhWriter_put1 (hd true ok) st b) ltac:(lia)) in Hf. lia. }
    rewrite Htx, app_assoc. reflexivity.
  + rewrite (prhW_putN_cons_nogrow ok st b P Hg) in Hf |- *.
    rewrite (IH ok _ Hf).
    assert (Hf0 : WriterApp.w_failed st = 0).
    { destruct (Z.eqb_spec (WriterApp.w_failed st) 0) as [E | E]; [exact E | exfalso].
      assert (Hp1 : WriterApp.put1 st b = st)
        by (unfold WriterApp.put1; rewrite (proj2 (Z.eqb_neq _ _) E); cbn [negb]; reflexivity).
      rewrite Hp1 in Hf. rewrite (prhW_putN_failed P ok st E) in Hf. lia. }
    assert (Hneed : prhWriter_need st b <= WriterApp.w_cap st).
    { unfold prhWriter_grows in Hg. rewrite Hf0, Z.eqb_refl in Hg. cbn [andb] in Hg.
      apply Z.ltb_ge in Hg. lia. }
    unfold WriterApp.put1. rewrite Hf0. cbn [Z.eqb negb].
    unfold prhWriter_need in Hneed. rewrite (proj2 (Z.leb_le _ _) Hneed).
    cbn [WriterApp.w_text]. rewrite app_assoc. reflexivity.
Qed.

(* ---- The kit's run events of a run of puts (PRH_FnWriter.v d89d3c67b78c at the cut: prhWriter_evs / prhWriter_pjw_evs), one step,
   and the facts pj_write's exact advance needs ---- *)
Lemma pjw_evs_cons_grow : forall ok st b P, prhWriter_grows st b = true ->
  prhWriter_evs ok st (b :: P) =
    (if (WriterApp.w_cnt st =? WriterApp.w_fail st) || negb (hd true ok) then [] else [prhWriter_ev st b]) ++
    prhWriter_evs (tl ok) (prhWriter_put1 (hd true ok) st b) P.
Proof. intros ok st b P H. cbn [prhWriter_evs]. rewrite H. reflexivity. Qed.

Lemma pjw_evs_cons_nogrow : forall ok st b P, prhWriter_grows st b = false ->
  prhWriter_evs ok st (b :: P) = prhWriter_evs ok (WriterApp.put1 st b) P.
Proof. intros ok st b P H. cbn [prhWriter_evs]. rewrite H. reflexivity. Qed.

(* a run that ends not failed met no refusal: its events are the all-granted run's (S7a's prhW_putN_ok_or_failed,
   for the events) *)
Lemma pjw_evs_ok_or_failed : forall P ok st,
  prhWriter_evs ok st P = prhWriter_evs [] st P \/ WriterApp.w_failed (prhWriter_putN ok st P) <> 0.
Proof.
induction P as [|b P IH]; intros ok st; [left; reflexivity|].
destruct (prhWriter_grows st b) eqn:Hg.
- rewrite (pjw_evs_cons_grow ok st b P Hg), (pjw_evs_cons_grow [] st b P Hg), (prhW_putN_cons_grow ok st b P Hg).
  cbn [tl hd].
  destruct (prhW_put1_grow_cases (hd true ok) st b Hg) as [(Hc & _) | [(Hc & Ho & _) | (Hc & Ho & Hf & _)]].
  + rewrite (proj2 (Z.eqb_eq _ _) Hc). cbn [orb].
    rewrite (prhW_put1_chosen (hd true ok) true st b Hc).
    destruct (IH (tl ok) (prhWriter_put1 true st b)) as [E | E]; [left; rewrite E; reflexivity | right; exact E].
  + rewrite Ho, (proj2 (Z.eqb_neq _ _) Hc). cbn [orb negb].
    destruct (IH (tl ok) (prhWriter_put1 true st b)) as [E | E]; [left; rewrite E; reflexivity | right; exact E].
  + right. rewrite (prhW_putN_failed P (tl ok) (prhWriter_put1 (hd true ok) st b)) by lia. lia.
- rewrite (pjw_evs_cons_nogrow ok st b P Hg), (pjw_evs_cons_nogrow [] st b P Hg), (prhW_putN_cons_nogrow ok st b P Hg).
  apply IH.
Qed.

(* the events read only the outcome bits of the calls the counter does not decide (S7a's prhW_putN_agree_c, for the
   events) *)
Lemma pjw_evs_agree_c : forall P ok ok' st,
  0 <= WriterApp.w_cnt st < 2 ^ 64 ->
  (forall i, (i < prhWriter_k ok st P)%nat ->
     (WriterApp.w_cnt st + Z.of_nat i) mod 2 ^ 64 <> WriterApp.w_fail st -> nth i ok' true = nth i ok true) ->
  prhWriter_evs ok' st P = prhWriter_evs ok st P.
Proof.
induction P as [|b P IH]; intros ok ok' st Hr H; [reflexivity|].
destruct (prhWriter_grows st b) eqn:Hg.
- rewrite (pjw_evs_cons_grow ok' st b P Hg), (pjw_evs_cons_grow ok st b P Hg).
  destruct (Z.eq_dec (WriterApp.w_cnt st) (WriterApp.w_fail st)) as [E|E].
  + rewrite (proj2 (Z.eqb_eq _ _) E). cbn [orb].
    rewrite (prhW_put1_chosen (hd true ok') (hd true ok) st b E).
    destruct (prhW_put1_grow_cases (hd true ok) st b Hg) as [(_ & Hf & _) | [(Hc & _) | (Hc & _)]];
      [| exfalso; exact (Hc E) | exfalso; exact (Hc E)].
    rewrite !(prhWriter_evs_failed P) by lia. reflexivity.
  + assert (H0 : hd true ok' = hd true ok).
    { rewrite <- !prhW_nth0. apply H.
      - rewrite (prhW_k_grow ok st b P Hg). lia.
      - change (Z.of_nat 0) with 0. rewrite Z.add_0_r, Z.mod_small by exact Hr. exact E. }
    rewrite H0. f_equal. apply IH.
    * rewrite (prhW_put1_grow_cnt (hd true ok) st b Hg). apply Z.mod_pos_bound.
      apply Z.pow_pos_nonneg; lia.
    * intros i Hi Hm. rewrite !prhW_nth_tl. apply H.
      -- rewrite (prhW_k_grow ok st b P Hg). lia.
      -- assert (Hfl : WriterApp.w_fail (prhWriter_put1 (hd true ok) st b) = WriterApp.w_fail st).
         { destruct (prhW_put1_grow_cases (hd true ok) st b Hg)
             as [(Hc & _) | [(_ & _ & _ & Hfl & _) | (_ & _ & _ & Hfl & _)]];
             [exfalso; exact (E Hc) | exact Hfl | exact Hfl]. }
         rewrite (prhW_put1_grow_cnt (hd true ok) st b Hg), Hfl in Hm.
         rewrite Z.add_mod_idemp_l in Hm by (apply Z.pow_nonzero; lia).
         replace (WriterApp.w_cnt st + Z.of_nat (S i)) with (WriterApp.w_cnt st + 1 + Z.of_nat i) by lia.
         exact Hm.
- rewrite (pjw_evs_cons_nogrow ok' st b P Hg), (pjw_evs_cons_nogrow ok st b P Hg).
  destruct (prhW_nogrow_f st b Hg) as (_ & _ & Hc & Hf & _).
  apply IH.
  + rewrite Hc. exact Hr.
  + intros i Hi Hm. apply H.
    * rewrite (prhW_k_nogrow ok st b P Hg). exact Hi.
    * rewrite Hc, Hf in Hm. exact Hm.
Qed.

(* NO REFUSAL (the kit's prh_granted, PRH_Base at the cut): the run under ok IS the all-granted run, same state and
   same events (a false bit is only ever the one the counter decides, where the model ignores it) *)
Lemma pjw_granted : forall ok st P,
  0 <= WriterApp.w_cnt st < 2 ^ 64 -> 0 <= WriterApp.w_fail st < 2 ^ 64 ->
  prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) ->
  prhWriter_putN ok st P = prhWriter_putN [] st P /\ prhWriter_evs ok st P = prhWriter_evs [] st P.
Proof.
intros ok st P Hr Hf Hg.
assert (A : forall i, (i < prhWriter_k ok st P)%nat ->
  (WriterApp.w_cnt st + Z.of_nat i) mod 2 ^ 64 <> WriterApp.w_fail st -> nth i [] true = nth i ok true).
{ intros i Hi Hm. assert (E : nth i (@nil bool) true = true) by (destruct i; reflexivity). rewrite E.
  destruct (nth i ok true) eqn:En; [reflexivity|]. exfalso. apply Hm.
  rewrite (Hg i Hi En). apply Z.mod_small. exact Hf. }
split; symmetry; [exact (prhW_putN_agree_c P ok [] st Hr A) | exact (pjw_evs_agree_c P ok [] st Hr A)].
Qed.

(* THE CONSUMER WINDOW (the batch kit's prh_cons_from, PRH_FnWriter.v:793-794) split for pj_write's two callees
   (PRH_Base.prh_cons_from_app_iff): write_value's window is the head of pj_write's; put's newline starts where
   write_value's granted run (prh_granted, its post) ended *)
Lemma pjw_cons_wv : forall sm x os i cnt fail P1 P2,
  prh_cons_from sm x os i (length (prhWriter_pjw_evs [] cnt fail (P1 ++ P2))) ->
  prh_cons_from sm x os i (length (prhWriter_evs [] (WriterApp.w0 cnt fail) P1)).
Proof.
intros sm x os i cnt fail P1 P2 H.
unfold prhWriter_pjw_evs in H. cbv zeta in H. rewrite prhWriter_evs_app0, !length_app in H.
apply prh_cons_from_app_iff in H as (H & _). apply prh_cons_from_app_iff in H as (H & _). exact H.
Qed.

Lemma pjw_cons_put : forall sm x os i cnt fail P1 P2 ok1,
  0 <= cnt < 2 ^ 64 -> 0 <= fail < 2 ^ 64 ->
  prh_granted ok1 cnt fail (prhWriter_k ok1 (WriterApp.w0 cnt fail) P1) ->
  prh_cons_from sm x os i (length (prhWriter_pjw_evs [] cnt fail (P1 ++ P2))) ->
  prh_cons_from sm x os (i + length (prhWriter_evs ok1 (WriterApp.w0 cnt fail) P1))
    (length (prhWriter_evs [] (prhWriter_putN ok1 (WriterApp.w0 cnt fail) P1) P2)).
Proof.
intros sm x os i cnt fail P1 P2 ok1 Hc Hf G H.
destruct (pjw_granted ok1 (WriterApp.w0 cnt fail) P1 Hc Hf G) as (EP & EE).
rewrite EP, EE.
unfold prhWriter_pjw_evs in H. cbv zeta in H. rewrite prhWriter_evs_app0, !length_app in H.
apply prh_cons_from_app_iff in H as (H & _). apply prh_cons_from_app_iff in H as (_ & H). exact H.
Qed.

(* pj_write's own event list (the kit's prhWriter_pjw_evs) in its three cases *)
Lemma pjw_evs_nf : forall ok cnt fail P,
  WriterApp.w_failed (prhWriter_putN ok (WriterApp.w0 cnt fail) P) = 0 ->
  prhWriter_pjw_evs ok cnt fail P = prhWriter_evs ok (WriterApp.w0 cnt fail) P.
Proof.
intros ok cnt fail P H. unfold prhWriter_pjw_evs. cbv zeta. rewrite H, Z.eqb_refl. cbn [orb]. apply app_nil_r.
Qed.

Lemma pjw_evs_nobuf : forall ok cnt fail P,
  WriterApp.w_cap (prhWriter_putN ok (WriterApp.w0 cnt fail) P) = 0 ->
  prhWriter_pjw_evs ok cnt fail P = prhWriter_evs ok (WriterApp.w0 cnt fail) P.
Proof.
intros ok cnt fail P H. unfold prhWriter_pjw_evs. cbv zeta. rewrite H, Z.eqb_refl, orb_true_r. apply app_nil_r.
Qed.

Lemma pjw_evs_free : forall ok cnt fail P,
  WriterApp.w_failed (prhWriter_putN ok (WriterApp.w0 cnt fail) P) <> 0 ->
  WriterApp.w_cap (prhWriter_putN ok (WriterApp.w0 cnt fail) P) <> 0 ->
  prhWriter_pjw_evs ok cnt fail P = prhWriter_evs ok (WriterApp.w0 cnt fail) P ++
    [PresetReqAt.HFr (WriterApp.w_cap (prhWriter_putN ok (WriterApp.w0 cnt fail) P) + cf_head)].
Proof.
intros ok cnt fail P H1 H2. unfold prhWriter_pjw_evs. cbv zeta.
rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity.
Qed.

(* the number of events is a function of the start and end states: one per call, less the one call that failed the
   writer (the allocation set to fail, or a refusal), if any *)
Lemma pjw_evs_len : forall P ok st,
  (length (prhWriter_evs ok st P) +
   (if (WriterApp.w_failed st =? 0)%Z && negb (WriterApp.w_failed (prhWriter_putN ok st P) =? 0)%Z then 1 else 0))%nat
  = prhWriter_k ok st P.
Proof.
induction P as [|b P IH]; intros ok st.
- rewrite prhW_k_nil. cbn [prhWriter_evs prhWriter_putN length].
  destruct (WriterApp.w_failed st =? 0); reflexivity.
- destruct (prhWriter_grows st b) eqn:Hg.
  + assert (Hf0 : WriterApp.w_failed st = 0)
      by (unfold prhWriter_grows in Hg; apply andb_prop in Hg as (Hg' & _); apply Z.eqb_eq in Hg'; exact Hg').
    rewrite (pjw_evs_cons_grow ok st b P Hg), (prhW_putN_cons_grow ok st b P Hg), (prhW_k_grow ok st b P Hg).
    rewrite Hf0, Z.eqb_refl. cbn [andb].
    destruct (prhW_put1_grow_cases (hd true ok) st b Hg)
      as [(Hc & Hf1 & _) | [(Hc & Ho & Hf1 & _) | (Hc & Ho & Hf1 & _)]].
    * rewrite (proj2 (Z.eqb_eq _ _) Hc). cbn [orb app].
      rewrite (prhWriter_evs_failed P) by lia.
      rewrite (prhW_putN_failed P (tl ok) (prhWriter_put1 (hd true ok) st b)) by lia.
      rewrite (prhW_k_failed (tl ok) (prhWriter_put1 (hd true ok) st b) P) by lia.
      rewrite Hf1. reflexivity.
    * pose proof (IH (tl ok) (prhWriter_put1 (hd true ok) st b)) as IH1.
      rewrite Hf1, Z.eqb_refl in IH1. cbn [andb] in IH1.
      rewrite Ho in IH1 |- *. rewrite (proj2 (Z.eqb_neq _ _) Hc). cbn [orb negb app length].
      lia.
    * rewrite Ho in Hf1 |- *. rewrite (proj2 (Z.eqb_neq _ _) Hc). cbn [orb negb app].
      rewrite (prhWriter_evs_failed P) by lia.
      rewrite (prhW_putN_failed P (tl ok) (prhWriter_put1 false st b)) by lia.
      rewrite (prhW_k_failed (tl ok) (prhWriter_put1 false st b) P) by lia.
      rewrite Hf1. reflexivity.
  + rewrite (pjw_evs_cons_nogrow ok st b P Hg), (prhW_putN_cons_nogrow ok st b P Hg), (prhW_k_nogrow ok st b P Hg).
    destruct (prhW_nogrow_f st b Hg) as (Hf & _).
    rewrite <- Hf. apply IH.
Qed.

(* the events of a run P1 followed by one put b, from an empty-call writer that has not failed: the first run's,
   plus ONE if that put grew and left the writer not failed (S7a's prhW_app_model gives the run's end state) *)
Lemma pjw_len_one : forall st P1 b okJ ok1 ok2,
  WriterApp.w_failed st = 0 -> WriterApp.w_calls st = [] ->
  prhWriter_putN okJ st (P1 ++ [b]) = prhWriter_putN ok2 (prhWriter_putN ok1 st P1) [b] ->
  length (prhWriter_evs okJ st (P1 ++ [b])) =
    (length (prhWriter_evs ok1 st P1) +
     (if prhWriter_grows (prhWriter_putN ok1 st P1) b &&
         (WriterApp.w_failed (prhWriter_putN ok2 (prhWriter_putN ok1 st P1) [b]) =? 0)%Z then 1 else 0))%nat.
Proof.
intros st P1 b okJ ok1 ok2 Hf0 Hcs Hput.
pose proof (pjw_evs_len (P1 ++ [b]) okJ st) as LJ. pose proof (pjw_evs_len P1 ok1 st) as L1.
unfold prhWriter_k in LJ, L1. rewrite Hput in LJ. rewrite Hf0, Hcs in LJ, L1. cbn [Z.eqb andb length] in LJ, L1.
set (st1 := prhWriter_putN ok1 st P1) in *.
destruct (prhWriter_grows st1 b) eqn:Hg.
- assert (E2 : prhWriter_putN ok2 st1 [b] = prhWriter_put1 (hd true ok2) st1 b)
    by (rewrite (prhW_putN_cons_grow ok2 st1 b [] Hg); reflexivity).
  rewrite E2 in LJ |- *. rewrite (prhW_put1_grow_calls (hd true ok2) st1 b Hg), length_app in LJ.
  cbn [length] in LJ.
  assert (Hf1 : WriterApp.w_failed st1 = 0)
    by (unfold prhWriter_grows in Hg; apply andb_prop in Hg as (Hg' & _); apply Z.eqb_eq in Hg'; exact Hg').
  rewrite Hf1 in L1. cbn [Z.eqb negb] in L1.
  revert LJ. destruct (Z.eqb_spec (WriterApp.w_failed (prhWriter_put1 (hd true ok2) st1 b)) 0) as [Hz | Hnz];
    intros LJ; cbn [negb andb] in LJ |- *; lia.
- assert (E2 : prhWriter_putN ok2 st1 [b] = WriterApp.put1 st1 b)
    by (rewrite (prhW_putN_cons_nogrow ok2 st1 b [] Hg); reflexivity).
  rewrite E2 in LJ. destruct (prhW_nogrow_f st1 b Hg) as (Ef & _ & _ & _ & Ec).
  rewrite Ef, Ec in LJ. cbn [andb]. lia.
Qed.

(* the cut's post of tpj_write_specX (lib/A/PRH_FnWriter.v blob d89d3c67b78c at the cut 7cdbb61b5fa0,
   :812-850, its `fun ly' S' Hp' W' regs' mem' md' =>` body), VERBATIM and named ONCE: pjw_walk carries it under the
   memory invariant, and pjw_holds_lc checks it against the cut's text by conversion *)
Definition pjw_Q (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z) (ly : alayout) (S : astate) (v pretty : Z) (t : PjTree.jv) (D Lam : list (Z * Z))
  (peak cnt fail ran most own : Z) :
  alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
       exists ok ran' q Lam' peak',
       let P := WriterValue.wdpieces t (negb (pretty =? 0)) in
       let st' := prhWriter_putN ok (WriterApp.w0 cnt fail) P in
       prh_oks ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P) (prhWriter_reqs ok (WriterApp.w0 cnt fail) P) most
         ran ran' /\
       getr regs' 10 = w64 q /\
       room_live_cf S' /\
       prh_granted ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P) /\
       (prh_granted ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P) ->
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length (prhWriter_pjw_evs ok cnt fail P))%nat
            rp_H0 hist' S') /\
       pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v t D /\
       prhWriter_tree_vis W' mem' D /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt st') (WriterApp.w_fail st') ran' most own /\
       ((WriterApp.w_failed st' = 0 /\ q <> 0 /\ ~ In (q - cf_head, WriterApp.w_cap st' + cf_head) (ablocks B ly S) /\
         Lam' = (q, WriterApp.w_cap st') :: Lam /\ peak' = Z.max peak (Ledger.lsum Lam + WriterApp.w_cap st') /\
         Permutation (ablocks B ly' S') ((q - cf_head, WriterApp.w_cap st' + cf_head) :: ablocks B ly S) /\
         Z.of_nat (length (WriterValue.wdoc t (negb (pretty =? 0)))) < WriterApp.w_cap st' /\
         bytes_at W' mem' q (WriterValue.wdoc t (negb (pretty =? 0)) ++ [0]))
        \/
        (WriterApp.w_failed st' <> 0 /\ q = 0 /\ Lam' = Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
         ((WriterApp.w_cap st' = 0 /\ peak' = Z.max peak (prhWriter_rpeak ok Lam (WriterApp.w0 cnt fail) P)) \/
          (WriterApp.w_cap st' <> 0 /\
           peak' = Z.max (Z.max peak (Ledger.lsum Lam + WriterApp.w_cap st'))
             (prhWriter_rpeak ok Lam (WriterApp.w0 cnt fail) P))))).

(* the template's float post (fpostF and the invariant at the end memory) at the memnorm keep is the kit's m-form float
   post fpostFm *)
Lemma pjw_post_m : forall STK FP regs ly S Hp W mem md Q W' c',
  fpostF B ARx SK STK FP regs ly S Hp W mem md Q W' c' ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS (ms_mem (cfg_ms c'))) ->
  fpostFm B ARx SK STK FP regs ly S Hp W mem md Q W' c'.
Proof.
intros STK FP regs ly S Hp W mem md Q W' c'
  (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & -> & HZ' & HK' & HJ' & HR' & HQ') HM.
exists fx', ly', S', Hp', regs', mem', md', k. split; [reflexivity|]. split; [exact HZ'|]. split; [exact HK'|].
split; [exact HJ'|]. split; [exact HR'|]. split; [exact HQ' | exact HM].
Qed.

(* ---- THE ONE RULED ARGUMENT of the one fuzz_free call site (no stand-in; a Theorem Labs lane 08:06Z): the class-24 bound
   tfuzz_free_specX asks for a non-NULL free. It is stated at a state pj_write's OWN journal reaches from its entry
   state, with the room invariant and a model-run position there, which is where the free call stands. The journal
   is at wle' SEGS RZ_cf: the free call stands after write_value, whose primed text (SRr' SEGS RZ_cf, post at wle')
   leaves the walk's journal at that relation. ---- *)
Definition pjw_ARGCNT (STK : Z) (rp_sm : list Z -> Z * Z) (rp_x : list Z)
  (rp_os : list (option nat * option nat * option nat)) (rp_H0 : list Z)
  ly S Hp (W : world SEGS) regs mem md : Prop :=
  forall ly' S' Hp' (W' : world SEGS) mem' md' k' rp_i' rp_hist',
    ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) STK (spZ regs) []
      ly S Hp W mem md [] ly' S' Hp' W' mem' md' k' ->
    room_live_cf S' -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i' rp_H0 rp_hist' S' ->
    YGcfRoomLive.ccnt24 S' <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
(* ---- THE WALK, generic in the memory invariant Pm (a Theorem Labs lane 12:18Z, template WalkNumEnd's vrd_num_end_stmt):
   Pm of the entry memory is a premise, Pm of the end memory a conjunct of the post; the runs carry it by its laws
   (YSRrMemnorm paj_run_x_inv / paj_run_to_x_inv), the four calls by their m-form keeps (srr_inv_call). Pm stays
   ABSTRACT here; pjw_holds instantiates it once.
   THE RE-HIDING MOVE (the kit's primed texts, PRH_FnWriter.v / PRH_FnAlloc.v): write_value, put and fuzz_free each
   conclude SRr' SEGS RZ_cf with their posts at wle' SEGS RZ_cf, so the walk runs at that relation from its entry
   journal (ajournal_x_initR) on: the _invR runners, paj_branchR, the call rules aj_call_xWFR / aj_call_xWR, the
   memset rule aj_intrin_at_xmR (SRr, lifted by SRr_SRrG), the terminal ret lifted by SRr_SRrG; the walk and its
   tail conclude SRr'. ---- *)
Section p.
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Hypothesis PCALL : srr_inv_call SEGS Pm.
Let RUNI := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).

(* ---- THE TAIL FROM THE JOIN (A 0x86c64, pj_write's slot 21): the two loads, `bnez a1`, and both exits. The two
   arms of the branch on pretty reach pjw_ssT, so this is proved ONCE. It runs after write_value's return, so it is
   stated at the CURRENT float state fxc (frm 0, fs0-fs11 those of the entry float state fx), and its post is the
   float form at the ENTRY float state. ---- *)
Lemma pjw_tail : forall (fxc : YK11.FPState) STK (rp_sm : list Z -> Z * Z) (rp_x : list Z)
    (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z) (most own : Z)
    ly S Hp (W : world SEGS) regs mem md ch v pretty (t : PjTree.jv) D Lam peak cnt fail ran
    ly3 S3 Hp3 (W3 : world SEGS) (EJ : env) msJ mdJ kJ regs9 md9,
  frm_zero (@YK11.fp_csr fxc) -> fregs_kept_x fx fxc ->
  64 + ESTACK <= STK -> STK_fuzz_free + 64 <= STK ->
  fpre (fx := fx) B ARx STK ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 ->
  getr regs 11 = w64 pretty -> 0 <= pretty < 2 ^ 31 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/ (exists x y, In (x, y) Lam /\ x <= v /\ v + 56 <= x + y) \/
   prhWriter_in_frame ly S v) ->
  (forall a k, In (a, k) D -> In (a, k) Lam) ->
  st_ok_pi (fx := fxc) SEGS VAL EJ pjw_ssT (restrict (w_H W3) msJ) ->
  sh_ok SEGS PJW_Bx [] EJ (mrestrict (w_H W3) (ms_mem msJ)) ->
  img_env VAL A_LIM EJ ->
  (forall m, (m < 33)%nat -> ew EJ m = ew (Ereg regs []) m) ->
  env_agree 32 (Ereg regs []) EJ ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) STK (spZ regs) []
    ly S Hp W mem md [] ly3 S3 Hp3 W3 (ms_mem msJ) mdJ kJ ->
  Pm (ms_mem msJ) ->
  room_live_cf S3 ->
  (* the texts' bound on the run's outcome list (the hull drafts): fuzz_free's hull budget is paid from the
     position below in a run of at most 4 calls (pjw_hull_pay) *)
  (length rp_os <= 4)%nat ->
  (* pj_write's run events from its entry position (the kit's entry premise, prhWriter_pjw_evs) *)
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_pjw_evs [] cnt fail (WriterValue.wdpieces t (negb (pretty =? 0)))) ->
  (* the writer after its pieces, its outcomes okJ named with no refusal (the batch kit's DEAD family: prh_granted), and the
     position at the EXACT advance under them *)
  (exists okJ, prhWriter_ret_ok B okJ ly S Lam peak ran most own (spZ regs - 56) 0 (WriterApp.w0 cnt fail)
     (WriterValue.wdpieces t (negb (pretty =? 0))) ly3 S3 Hp3 W3 regs9 (ms_mem msJ) md9 /\
   prh_granted okJ cnt fail (prhWriter_k okJ (WriterApp.w0 cnt fail) (WriterValue.wdpieces t (negb (pretty =? 0)))) /\
   exists rp_hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
     (rp_i + length (prhWriter_evs okJ (WriterApp.w0 cnt fail) (WriterValue.wdpieces t (negb (pretty =? 0)%Z))))%nat
     rp_H0 rp_hist' S3) ->
  pjw_ARGCNT STK rp_sm rp_x rp_os rp_H0 ly S Hp W regs mem md ->
  SRr' SEGS RZ_cf W3 (mkCfg msJ mdJ)
    (fun W' c' => fpostF (fx := fx) B ARx SK STK [] regs ly S Hp W mem md
                    (pjw_Q rp_sm rp_x rp_os rp_i rp_H0 ly S v pretty t D Lam peak cnt fail ran most own) W' c'
                  /\ Pm (ms_mem (cfg_ms c'))).
Proof.
intros fxc STK rp_sm rp_x rp_os rp_i rp_H0 most own ly S Hp W regs mem md ch v pretty t D Lam peak cnt fail ran
  ly3 S3 Hp3 W3 EJ msJ mdJ kJ regs9 md9
  HFZc HFKc HSTK HFFSTK HPRE HUNIV H11 HPR HLED HNODE HLOC HDL HS SHOK HEI AG2 HAEJ HJ3 HPM HROOM3 HOS HEVS HRET3
  ARGCNT.
(* the walk's relation wle' SEGS RZ_cf: the runners, the branch rule and the binds below conclude SRrG at it *)
unfold SRr'.
(* the runner, the branch and the return AT the current float state fxc *)
pose (RUNIc := @paj_run_x_invR fxc rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
pose (BRc := YSRrG.paj_branchR (fx := fxc) (PI := PA) (wle' SEGS RZ_cf)).
pose (RETc := paj_ret_at (fx := fxc) (PL := PL_prog_A) (PI := PA)).
pose proof HPRE as (HPRE1 & HRO & HTOP & HRAZE & HFRM).
pose proof HPRE1 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hch0.
pose proof (@YM05.alloc_ceiling_value rc) as HCV.
pose proof (pjw_foot_ok STK ly S Hp W regs mem md ch Lam peak cnt fail ran most own v D HPRE1 HLED HLOC HDL) as FOOT.
assert (VB : 0 <= v /\ v + 56 <= 2 ^ 47)
  by (destruct (FOOT (v + 55) ltac:(left; lia)) as (F1 & _); destruct (FOOT v ltac:(left; lia)) as (F2 & _); lia).
unfold ESTACK in HSTK.
norm_ss HS.
pose proof (ajxR_ar HJ3) as HAR3m.
pose proof (ajxR_pres HJ3) as HPRES4.
assert (Usp2 : bv_unsigned (ew EJ 2) = spZ regs)
  by (rewrite (AG2 2%nat) by lia; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
destruct HRET3 as (ok1 & HRET3 & HGR1 & rp_hist1 & HPOS1).
(* The batch kit's prhWriter_ret_ok under no refusal (prh_granted): S7a_WriterRet's blocks arms (prhWriter_blk) *)
apply prhWriter_blk_of_ret_ok in HRET3; [| exact HGR1].
destruct HRET3 as (ran1 & buf1 & Lam1 & peak1 & HOKS1 & HOUT1 & HLED1 & HBLK1).
set (rp_i1 := (rp_i + length (prhWriter_evs ok1 (WriterApp.w0 cnt fail)
                 (WriterValue.wdpieces t (negb (pretty =? 0)%Z))))%nat) in HPOS1.
set (stT := prhWriter_putN ok1 (WriterApp.w0 cnt fail) (WriterValue.wdpieces t (negb (pretty =? 0)))) in *.
pose proof HOUT1 as (TO1 & TO2 & TO3 & TO4 & TO5 & TO6 & TO7 & TO8 & TO9 & TO10).
assert (TO4' : val_mem SEGS (mrestrict (w_H W3) (ms_mem msJ)) (spZ regs + -56) 8 buf1)
  by (replace (spZ regs + -56) with (spZ regs - 56) by lia; exact TO4).
assert (TO7' : val_mem SEGS (mrestrict (w_H W3) (ms_mem msJ)) (spZ regs + -32) 4 (WriterApp.w_failed stT))
  by (replace (spZ regs + -32) with (spZ regs - 56 + 24) by lia; exact TO7).
destruct (ex_intro (fun x => x = WriterApp.w_failed stT) _ eq_refl) as [fl Efl].
rewrite <- Efl in TO7', TO8.
assert (FLR : 0 <= fl < 2 ^ 32) by (destruct TO8 as [-> | ->]; lia).
(* the two loaded fields as the fresh atoms 81 (buf) and 82 (failed) *)
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssc ?msc =>
  assert (HSB : st_ok_pi (fx := fxc) SEGS VAL (havoc EJ 81 [Z_to_bv 64 buf1; Z_to_bv 64 fl]) ssc msc)
    by (unfold st_ok_pi in *; eapply st_ok_agree_p;
        [ exact HS | apply (env_agree_p_havoc 81 A_TEXT); cbn [length]; unfold A_TEXT; lia
        | vm_compute; reflexivity ])
end.
clear HS. set (EB := havoc EJ 81 [Z_to_bv 64 buf1; Z_to_bv 64 fl]) in HSB. rename HSB into HS.
pose proof HEI as HEIe2. clear HEI.
assert (HEI : img_env VAL A_LIM EB)
  by (unfold EB; apply img_env_havoc; [exact HEIe2 | cbn [length]; unfold A_TEXT; lia]).
assert (AG3 : forall m, (m < 33)%nat -> ew EB m = ew (Ereg regs []) m)
  by (intros m Hm; unfold EB; rewrite ew_havoc_old by lia; apply AG2; lia).
assert (Usp3 : bv_unsigned (ew EB 2) = spZ regs)
  by (rewrite (AG3 2%nat) by lia; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E65 : ew EB 81 = Z_to_bv 64 buf1)
  by (exact (ew_havoc_new EJ 81 [Z_to_bv 64 buf1; Z_to_bv 64 fl] 0 (Z_to_bv 64 0) ltac:(cbn [length]; lia))).
assert (E66 : ew EB 82 = Z_to_bv 64 fl)
  by (exact (ew_havoc_new EJ 81 [Z_to_bv 64 buf1; Z_to_bv 64 fl] 1 (Z_to_bv 64 0) ltac:(cbn [length]; lia))).
assert (SHOK3 : sh_ok SEGS PJW_Bx [] EB (mrestrict (w_H W3) (ms_mem msJ))) by constructor.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssc ?msc =>
  assert (HWF : region_wf pjw_oA = true) by (vm_compute; reflexivity);
  assert (HROK : region_ok SEGS EB (ms_mem msc) pjw_oA);
  [ unfold pjw_oA, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite Usp3;
    split; [lia|]; split; [lia|]; split;
    [ intros a Ha; apply (apresent_writable SEGS); apply HPRES4; lia
    | repeat apply Forall_cons; try apply Forall_nil;
      [ eapply (chunk_ok_val SEGS EB _ _ (-56) 8%N (SOff 81 0) buf1);
        [ cbn [sv_denot]; rewrite E65, Z.add_0_r, unsigned_lit_small by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
        | change (Z.of_N 8) with 8; lia
        | cbn [ms_mem restrict]; exact TO4']
      | eapply (chunk_ok_val SEGS EB _ _ (-32) 4%N (SOff 82 0) fl);
        [ cbn [sv_denot]; rewrite E66, Z.add_0_r, unsigned_lit_small by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia
        | change (Z.of_N 4) with 4; lia
        | cbn [ms_mem restrict]; exact TO7'] ] ]
  | assert (HDIS : all_disjoint EB pjw_oA (ss_mem ssc));
    [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, pjw_oA;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?Usp3;
      repeat split; first [ left; lia | right; lia | exact I ]
    | pose proof (st_ok_pi_add_region EB ssc msc pjw_oA HS HWF HROK HDIS) as HSR ] ]
end.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSR. clear HS. rename HSR into HS.
(* ---- the loads and the branch on failed (A 0x86c64 .. 0x86c6c) ---- *)
paj_run_tok_x_inv RUNIc HS HJ3 SHOK3 HPM PJW_Bspan.
{ cbn [ss_mem].
  unfold pjw_oA, pjw_saveJ; repeat (eapply awr_ok_cons_stack;
    [reflexivity | exact Usp3 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]); apply awr_ok_nil. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msA end.
assert (KEEPA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 56 <= a < spZ regs) ->
  aview SEGS (w_H W3) (ms_mem msA) a = aview SEGS (w_H W3) (ms_mem msJ) a).
{ eapply pjw_keep_frame; [ intros; reflexivity | exact HFr |].
  intros a (r & Hr & Ha). unfold pjw_oA, pjw_saveJ in Hr.
  lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change rs0 with rs1 in Hr end.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp3 in Ha; lia |]).
  destruct Hr. }
clear HF HFr HG.
assert (UFL : U EB (SExt true 32 (SOff 82 0)) = fl)
  by (destruct TO8 as [E0 | E0]; rewrite U_SExt, (U_atom EB 82 fl E66 ltac:(lia)), E0;
      vm_compute; reflexivity).
psrr_branch_tok RUNIc BRc HS SHOK3 PJW_Bspan.
- (* failed = 0: no free; the epilogue returns buf *)
  rewrite branch_eq_U, UFL, (U_lit EB 0 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
  paj_run_tok_x_inv RUNIc HS HJ3 SHOK3 HPM PJW_Bspan.
  { cbn [ss_mem]. unfold pjw_oA, pjw_saveJ; repeat (eapply awr_ok_cons_stack;
      [reflexivity | exact Usp3 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]); apply awr_ok_nil. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msB end.
  prreg HS (1%bv : bv 5) Rra5. prreg HS (10%bv : bv 5) Ra0f.
  assert (HAE3 : env_agree 32 (Ereg regs []) EB)
    by (unfold EB; apply env_agree_havoc_ge; [lia | exact HAEJ]).
  assert (HPRES5 : aregs_preserved regs (ms_regs msB)).
  { pose proof HS as HSu; red in HSu.
    eapply (aregs_preserved_of_st_ok (fx := fxc) SEGS (w_H W3) EB _ _ regs []);
      [exact HSu | exact HAE3 | vm_compute; reflexivity]. }
  assert (RA5 : getr (ms_regs msB) 1 = getr regs 1).
  { rewrite Rra5; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (AG3 1%nat) by lia.
    exact (ew_Ereg_nat regs _ 1 1%bv eq_refl). }
  assert (RB5 : getr (ms_regs msB) 10 = w64 buf1)
    by (rewrite Ra0f; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E65).
  assert (KEEPB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 56 <= a < spZ regs) ->
    aview SEGS (w_H W3) (ms_mem msB) a = aview SEGS (w_H W3) (ms_mem msJ) a).
  { eapply pjw_keep_frame; [ exact KEEPA | exact HFr |].
    intros a (r & Hr & Ha). unfold pjw_oA, pjw_saveJ in Hr.
    lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change rs0 with rs1 in Hr end.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp3 in Ha; lia |]).
    destruct Hr. }
  assert (HDL1 : forall a k, In (a, k) D -> In (a, k) Lam1).
  { intros a k Hin. destruct HBLK1 as [(_ & _ & EL & _) | (_ & l1 & l2 & b1 & b2 & Hcc & EL & _)].
    - rewrite EL. exact (HDL a k Hin).
    - destruct Hcc as [(_ & -> & -> & _ & _) | (Hne & _)];
        [| exfalso; cbn [WriterApp.w0 WriterApp.w_cap] in Hne; exact (Hne eq_refl)].
      rewrite EL. cbn [app]. right. exact (HDL a k Hin). }
  assert (HSUB1 : forall a k, In (a, k) Lam -> In (a, k) Lam1).
  { intros a k Hin. destruct HBLK1 as [(_ & _ & EL & _) | (_ & l1 & l2 & b1 & b2 & Hcc & EL & _)].
    - rewrite EL. exact Hin.
    - destruct Hcc as [(_ & -> & -> & _ & _) | (Hne & _)];
        [| exfalso; cbn [WriterApp.w0 WriterApp.w_cap] in Hne; exact (Hne eq_refl)].
      rewrite EL. cbn [app]. right. exact Hin. }
  assert (TLED3 : prh_ledger (PI := prh_img_A) B ly3 S3 Hp3 W3 (ms_mem msB) Lam1 peak1
                    (WriterApp.w_cnt stT) (WriterApp.w_fail stT) ran1 most own)
    by (eapply pjw_ledger_keep; [exact HAR3m | exact HLED1 | exact KEEPB | intros a Ha; cbv beta; lia]).
  (* the return keeps the world: its SRr lifts into the walk's relation (SRr_SRrG at wle_wle') *)
  apply (SRr_SRrG SEGS (wle' SEGS RZ_cf) (wle_wle' SEGS RZ_cf)).
  eapply (RETc W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  (* ---- the success post (failed = 0: the document is in the new block), the float form at the ENTRY fx: the end
     float state is the current one, fxc ---- *)
  split; [| exact HPM].
  unfold fpostF, apost_base_xFR, pjw_Q.
  lazymatch goal with
  | |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists fxc, ly3, S3, Hp3, rg, m, d
  end.
  eexists.
  split; [ unfold YK0s.ret_ok in Hra; cbn [ms_regs ms_mem]; rewrite RA5, Hra; reflexivity |].
  split; [ exact HFZc |].
  split; [ exact HFKc |].
  split; [ eapply ajournal_x_materializeR;
           first [exact LAWS | exact (@pa_segs_low _ A_prog_listing PA) | exact PST_ok | exact HJ3] |].
  split; [ exact HPRES5 |].
  exists ok1, ran1, buf1, Lam1, peak1.
  cbn [WriterApp.w0 WriterApp.w_cnt WriterApp.w_fail] in HOKS1.
  split; [ exact HOKS1 |].
  split; [ exact RB5 |].
  split; [ exact HROOM3 |].
  (* DEAD-PJWRITE: no grow of ok1 was refused (the composed callee posts' prh_granted) *)
  split; [ exact HGR1 |].
  (* the exact advance: no free on this exit, so pj_write's events are its puts' *)
  split; [ intros _; exists rp_hist1;
           rewrite pjw_evs_nf by (change (WriterApp.w_failed stT = 0); rewrite <- Efl; exact Hc);
           exact HPOS1 |].
  split; [ eapply (pjw_nodeR_end _ STK ly S Hp W regs mem md ch Lam peak cnt fail ran most own v t D
                     ly3 S3 Hp3 W3 (ms_mem msB) _ _ Lam1 peak1 _ _ ran1 most own);
           [exact HPRE1 | exact HLED | exact TLED3 | exact HJ3 | exact HNODE | exact HLOC | exact HDL
            | exact HSUB1] |].
  split; [ eapply pjw_tree_vis_of; [exact (ajxR_ar HJ3) | exact TLED3 | exact HDL1] |].
  split; [ exact TLED3 |].
  (* the run did not fail, so it grew a block and the document is in it *)
  assert (HFL0 : WriterApp.w_failed stT = 0) by (rewrite <- Efl; exact Hc).
  assert (HCAP : WriterApp.w_cap stT <> 0)
    by (apply pjw_cap_nz; [apply pjw_wdpieces_nonempty | exact HFL0]).
  assert (HBUFNZ : 4096 <= buf1).
  { destruct TO10 as [(Hz & _) | (_ & Hin1 & _)]; [exfalso; exact (HCAP Hz) |].
    destruct (pjw_led_hb ly3 S3 Hp3 W3 (ms_mem msJ) Lam1 peak1 _ _ ran1 _ _ _ _ HLED1 Hin1) as (_ & Hab1 & _).
    destruct (alx_blocks SEGS B ARx LAWS ly3 S3 Hp3 W3 (ms_mem msJ) mdJ _ _ HAR3m Hab1) as (_ & H4096 & _). lia. }
  assert (HTXT : WriterApp.w_text stT = WriterValue.wdoc t (negb (pretty =? 0))).
  { unfold WriterValue.wdoc, stT. rewrite (pjw_text_putN _ ok1 (WriterApp.w0 cnt fail) HFL0).
    cbn [WriterApp.w0 WriterApp.w_text]. reflexivity. }
  left. split; [exact HFL0 |]. split; [lia |].
  destruct HBLK1 as [(Ec & Eb & EL & Ep & Hperm) | (Hlt & l1 & l2 & b1 & b2 & Hcc & EL & Ep & Hperm)].
  { exfalso. apply HCAP. cbn [WriterApp.w0 WriterApp.w_cap] in Ec. exact Ec. }
  destruct Hcc as [(_ & -> & -> & -> & ->) | (Hne & _)];
    [| exfalso; cbn [WriterApp.w0 WriterApp.w_cap] in Hne; exact (Hne eq_refl)].
  cbn [app] in Hperm, EL.
  assert (Hrq : 0 < req_size (WriterApp.w_cap stT + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (WriterApp.w_cap stT + cf_head) 0); lia).
  split; [ exact (pjw_fresh_block ly3 S3 Hp3 W3 (ms_mem msJ) mdJ
                    (buf1 - cf_head, WriterApp.w_cap stT + cf_head) (ablocks B ly S) HAR3m Hperm Hrq) |].
  split; [ exact EL |]. split; [ exact Ep |]. split; [ exact Hperm |].
  destruct TO10 as [(Hz & _) | (_ & Hin1 & Hlen1 & (rest & Hr1 & Hr2) & _)];
    [exfalso; exact (HCAP Hz) |].
  destruct (pjw_led_hb ly3 S3 Hp3 W3 (ms_mem msJ) Lam1 peak1 _ _ ran1 _ _ _ _ HLED1 Hin1) as (_ & Hab1 & _).
  destruct (alx_blocks SEGS B ARx LAWS ly3 S3 Hp3 W3 (ms_mem msJ) mdJ _ _ HAR3m Hab1) as (_ & H4096 & Hbc & _).
  assert (Hrq2 : WriterApp.w_cap stT + cf_head <= req_size (WriterApp.w_cap stT + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (WriterApp.w_cap stT + cf_head) 0); lia).
  rewrite HTXT in Hlen1, Hr2.
  split; [ exact Hlen1 |].
  assert (HSPL : WriterValue.wdoc t (negb (pretty =? 0)) ++ 0 :: rest
                 = (WriterValue.wdoc t (negb (pretty =? 0)) ++ [0]) ++ rest)
    by (rewrite <- app_assoc; reflexivity).
  rewrite HSPL in Hr2.
  pose proof (proj1 (garr8_app SEGS _ buf1
                      (WriterValue.wdoc t (negb (pretty =? 0)) ++ [0]) rest) Hr2) as [Hpre _].
  unfold PRH_Base.bytes_at. unfold PRH_Base.bytes_at in Hpre.
  intros j Hj. destruct (Hpre j Hj) as [Hv Hb]. split; [| exact Hb].
  refine (pjw_vm_keep _ _ _ _ _ _ _ _ Hv). intros i Hi.
  rewrite length_app in Hj. cbn [length] in Hj.
  apply KEEPB; lia.
- (* failed <> 0: fuzz_free (buf) at A 0x86c70, then return 0 *)
  rewrite branch_eq_U, UFL, (U_lit EB 0 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
  pose proof Hc as Hc0f.
  paj_run_tok_x_inv RUNIc HS HJ3 SHOK3 HPM PJW_Bspan.
  { cbn [ss_mem]. unfold pjw_oA, pjw_saveJ; repeat (eapply awr_ok_cons_stack;
      [reflexivity | exact Usp3 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]); apply awr_ok_nil. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msC
  | st_ok _ _ _ (restrict _ ?m) => rename m into msC
  end.
  prreg HS (10%bv : bv 5) Rf0. prreg HS (1%bv : bv 5) Rfra. prreg HS (2%bv : bv 5) Rfsp.
  prreg HS (3%bv : bv 5) Rfgp. prreg HS (4%bv : bv 5) Rftp. prreg HS (8%bv : bv 5) Rfs0.
  assert (SPZ6 : spZ (ms_regs msC) = spZ regs - 64)
    by (unfold spZ; rewrite Rfsp; rewrite unsigned_lit_small by (rewrite Usp3; lia); rewrite Usp3; unfold spZ; lia).
  (* the freed block is one the writer made *)
  assert (HTMPT : forall a, inFP (if buf1 =? 0 then []
                    else ablocks_fp [(buf1 - cf_head, WriterApp.w_cap stT + cf_head)]) a ->
                  in_tmp_block (ablocks B ly S) (ablocks B ly3 S3) a).
  { destruct (Z.eqb_spec buf1 0) as [Hb0 | Hbn]; [intros a Ha; destruct (inFP_nil a Ha) |].
    destruct HBLK1 as [(Ec & Eb & EL & Ep & Hperm) | (Hlt & l1 & l2 & b1 & b2 & Hcc & EL & Ep & Hperm)].
    - exfalso. apply Hbn. exact Eb.
    - destruct Hcc as [(_ & -> & -> & -> & ->) | (Hne & _)];
        [| exfalso; cbn [WriterApp.w0 WriterApp.w_cap] in Hne; exact (Hne eq_refl)].
      cbn [app] in Hperm.
      intros a Ha. apply inFP_ablocks_fp_inv in Ha. destruct Ha as (p0 & n0 & [Hq | []] & Hr0).
      injection Hq as <- <-. exists (buf1 - cf_head), (WriterApp.w_cap stT + cf_head).
      assert (Hrq : 0 < req_size (WriterApp.w_cap stT + cf_head))
        by (unfold req_size; destruct (Z.eqb_spec (WriterApp.w_cap stT + cf_head) 0); lia).
      split; [ eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity] |].
      split; [ exact (pjw_fresh_block ly3 S3 Hp3 W3 (ms_mem msJ) mdJ
                        (buf1 - cf_head, WriterApp.w_cap stT + cf_head) (ablocks B ly S) HAR3m Hperm Hrq)
             | exact Hr0 ]. }
  assert (HFF0 : 0 <= STK_fuzz_free)
    by (assert (HFF : pi_frame F_fuzz_free = 32) by (vm_compute; reflexivity);
        unfold STK_fuzz_free, zmaxl; cbn [fold_right]; rewrite HFF; lia).
  (* the freed pointer: the writer's buffer (0 when it never grew) *)
  assert (HPIN : buf1 = 0 \/ In (buf1, WriterApp.w_cap stT) Lam1)
    by (destruct TO10 as [(_ & Hb0 & _) | (_ & Hin1 & _)]; [left; exact Hb0 | right; exact Hin1]).
  assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 56 <= a < spZ regs) ->
    aview SEGS (w_H W3) (ms_mem msC) a = aview SEGS (w_H W3) (ms_mem msJ) a).
  { eapply pjw_keep_frame; [ exact KEEPA | exact HFr |].
    intros a (r & Hr & Ha). unfold pjw_oA, pjw_saveJ in Hr.
    lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change rs0 with rs1 in Hr end.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp3 in Ha; lia |]).
    destruct Hr. }
  clear HF HFr HG.
  assert (ARO6 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem msC)))
    by (eapply pjw_arodata_kept;
        [exact HJ3 | intros a; apply fp_spares_closed; intros (r & Hr & _); destruct Hr | exact HRO]).
  assert (TLEDF : prh_ledger (PI := prh_img_A) B ly3 S3 Hp3 W3 (ms_mem msC) Lam1 peak1
                    (WriterApp.w_cnt stT) (WriterApp.w_fail stT) ran1 most own)
    by (eapply pjw_ledger_keep; [exact HAR3m | exact HLED1 | exact KEEPC | intros a Ha; cbv beta; lia]).
  assert (HAFV : AF_pj_write = ltac:(let x := eval vm_compute in AF_pj_write in exact x))
    by (vm_compute; reflexivity).
  assert (ESHI3T : ly_stk_hi ly3 = ly_stk_hi ly).
  { pose proof (ajxR_ly HJ3) as Hly3.
    destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi & _). exact Eshi. }
  assert (HRAZ : raZ (ms_regs msC) = nth 0 (pi_ret_sites F_pj_write RT_fuzz_free) 0).
  { unfold raZ. rewrite Rfra, HRET, HAFV.
    rewrite unsigned_lit_small by (pose proof (@pa_B_ok _ _ PA); lia). lia. }
  assert (HTRIN : In (nth 0 (pi_ret_sites F_pj_write RT_fuzz_free) 0) (pi_ret_sites F_pj_write RT_fuzz_free))
    by (apply nth_In; vm_compute; lia).
  (* THE FREE'S TRACE (the batch kit's tfuzz_free_specX `admits` premise, PRH_FnAlloc.v:340): pj_write's free site is a FIXED
     trace (prh_univ_closure's clauses 1-2, prh_univ_closure_lit), so there is NO GAP here: YG01.admits_fix gives
     the engine's form at the free's state, from universe_ok (the cf instance's amc_universe) *)
  assert (HTRACE : In (call_trace ly3 (pc_free_ra0 (as_code B)) (ms_regs msC) []) (u_fix (as_universe B))).
  { unfold call_trace. destruct (frame0_ok ly3 (ms_regs msC)) eqn:Hf0.
    - replace (unwind_of_chain (pc_free_ra0 (as_code B))
                 [(spZ (ms_regs msC), raZ (ms_regs msC), s0Z (ms_regs msC))])
        with (prh_trace (prh_pc0 B RT_fuzz_free) (raZ (ms_regs msC)) [])
        by (unfold prh_trace, prh_pc0, unwind_of_chain; cbn [flat_map]; reflexivity).
      rewrite HRAZ. eapply prh_univ_closure_lit; [exact HUNIV | exact HTRIN].
    - exact (proj1 HUNIV RT_fuzz_free). }
  assert (HUOK : universe_ok (as_universe B))
    by (destruct (S9_CF _ _ _ _ _ _ HAR3m) as (M & _); eapply YG0ncf.amc_universe; exact M).
  pose proof (admits_fix (as_universe B) _ S3 HUOK HTRACE) as HADM.
  pmkst HS.
  (* fuzz_free's primed text concludes SRr' SEGS RZ_cf: the call rule over the walk's relation (aj_call_xWR) *)
  eapply (SRrG_bind SEGS (wle' SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
  { eapply (aj_call_xWR (fx := fxc) SEGS B (@prh_pst prh_img_A) ARx LAWS segs_low (wle' SEGS RZ_cf)
      (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) W3 _ _ _ STK (spZ regs) [] ly S Hp W
      mem md []
      ly3 S3 Hp3 _ _ STK_fuzz_free 0
      (if buf1 =? 0 then [] else ablocks_fp [(buf1 - cf_head, WriterApp.w_cap stT + cf_head)]) (-64) _ [] _ HJ3).
    all: first
       [ lazymatch goal with
         | |- afn_pre_x _ _ _ _ _ _ _ _ _ _ _ _ -> _ =>
           let HPRE6 := fresh "HPRE6" in let HWIN6 := fresh "HWIN6" in intros HPRE6 HWIN6;
           eapply (SRrG_mono SEGS (wle' SEGS RZ_cf));
           [ eapply (HFREE fxc most own ly3 S3 Hp3 W3 _ _ _ [] buf1 (WriterApp.w_cap stT) Lam1 peak1);
             first
             [ (* the room invariant, asked for a non-NULL free *)
               intros _; exact HROOM3
             | lazymatch goal with
               | |- fpre _ _ _ _ _ _ _ _ _ _ _ =>
                 split;
                 [ exact HPRE6
                 | split;
                   [ exact ARO6
                   | split;
                     [ rewrite ESHI3T, SPZ6; lia
                     | split;
                       [ unfold raZ; rewrite Rfra;
                         rewrite unsigned_lit_small by (pose proof (@pa_B_ok _ _ PA); lia);
                         pjw_ret_ceil_tac
                       | (* the rounding mode of the current float state *) exact HFZc ] ] ] ]
               end
             | exact HPIN
             | rewrite Rf0; exact E65
             | exact HADM
             | exact TLEDF
             | (* the live-count bound of a non-NULL free: the ruled ARGUMENT of this call *)
               intros _; exact (ARGCNT ly3 S3 Hp3 W3 (ms_mem msC) _ _ rp_i1 rp_hist1 HJ3 HROOM3 HPOS1)
             | (* the hull budget of a non-NULL free (the hull drafts): from the run position at this state *)
               intros _; exact (pjw_hull_pay _ _ _ _ _ _ _ HOS HPOS1) ]
           | (* The batch kit's post is BUDGETED at this call's own trace (fpostbm, wbudget [tr] 0); the trace is FIXED, so
                PRH_Base.fpost_of_fpostb_fix reads the post back at wle' (fpostR), the caller-window form at e = 0 *)
             let Wq := fresh "Wq" in let cq := fresh "cq" in let Hle := fresh "Hle" in let HQ := fresh "HQ" in
             intros Wq cq Hle HQ; eapply fpost_of_fpostb_fix in HQ; [| exact HTRACE];
             eapply fpostW_x_of_apostR; exact HQ ]
         end
       | exact Rfra
       | rewrite SPZ6; lia
       | reflexivity
       | lia
       | rewrite Rfgp, (AG3 3%nat) by lia; exact Hgp
       | rewrite Rftp, (AG3 4%nat) by lia; exact Htp
       | apply ret_ok_codeptr_v; [lia | vm_compute; reflexivity]
       | rewrite unsigned_lit_small by (pose proof (@pa_B_ok _ _ PA); lia); pose proof (@pa_B_ok _ _ PA); lia
       | apply achain_low; unfold s0Z; rewrite Rfs0, (AG3 11%nat) by lia;
         rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), H11; unfold w64;
         rewrite unsigned_lit_small by lia; lia
       | let a := fresh "a" in let Ha := fresh "Ha" in
         intros a Ha; right; left; exact (HTMPT a Ha) ]. }
  (* ---- after fuzz_free (A 0x86c74): a0 = 0, the epilogue, the failure post ---- *)
  cbv beta. intros W6 c6 Hwle6 (ly6 & S6 & Hp6 & regs6 & mem6 & md6 & k6 & -> & HJ6 & HJW6 & HKW6 & HP6 & HQ6).
  (* fuzz_free's post READ BY SHAPE (the hull drafts inserted `hull_used S S' []` as its second conjunct): each
     conjunct this walk uses is named by its statement *)
  unfold fQmn in HQ6. cbv beta in HQ6. pjw_split HQ6.
  lazymatch goal with H : buf1 <> 0 -> room_live_cf S6 |- _ => rename H into HROOM6 end.
  lazymatch goal with H : buf1 = 0 -> _ |- _ => rename H into HPF0 end.
  match goal with H : buf1 <> 0 -> ?T |- _ =>
    lazymatch T with context [PresetReqAt.HFr] => rename H into HPFR end end.
  lazymatch goal with H : (buf1 = 0 /\ _) \/ _ |- _ => rename H into HFARM end.
  lazymatch goal with H : YAkMemnorm.memnorm _ _ -> YAkMemnorm.memnorm _ mem6 |- _ => rename H into HMN6 end.
  (* the memory invariant across fuzz_free (its m-form keep, srr_inv_call) *)
  pose proof (PCALL _ _ HMN6 HPM) as HPM6. clear HPM HMN6. rename HPM6 into HPM.
  pose proof (ajxR_hi HJW6) as KEEPHI6.
  pose proof (ajxR_pres HJ6) as HPRES6.
  (* re-seat: only the saved-register region survives (the struct is dead; the free's window is below sp - 64) *)
  jafter_call_keep_pi HS 83%nat regs6 (mrestrict (w_H W6) mem6) HP6 (1%nat :: @nil nat) HS6.
  match type of HS6 with ?Q -> _ =>
    assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
      split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp3; intros a Ha;
      [ apply (mbyte_of_aview SEGS); apply KEEPHI6; lia
      | intros _; apply (apresent_writable SEGS); apply HPRES6; lia ]
    | specialize (HS6 HQ); clear HQ ] end.
  clear HS. rewrite <- (restrict_mkst_fx (fx := fxc)) in HS6. rename HS6 into HS.
  pose proof HEI as HEIe3. clear HEI.
  set (EF := havoc EB 83 (map (getr regs6) CLOB)) in HS.
  assert (HEI : img_env VAL A_LIM EF)
    by (unfold EF; apply img_env_havoc; [exact HEIe3 | vm_compute; lia]).
  assert (AG5 : forall m, (m < 33)%nat -> ew EF m = ew (Ereg regs []) m)
    by (intros m Hm; unfold EF; rewrite ew_havoc_old by lia; apply AG3; lia).
  assert (Usp5 : bv_unsigned (ew EF 2) = spZ regs)
    by (rewrite (AG5 2%nat) by lia; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  assert (SHOK5 : sh_ok SEGS PJW_Bx [] EF (mrestrict (w_H W6) mem6)) by constructor.
  (* ---- the epilogue (A 0x86c74 .. 0x86c88): a0 = 0, the saved registers, sp, ret ---- *)
  paj_run_tok_x_inv RUNIc HS HJ6 SHOK5 HPM PJW_Bspan.
  { cbn [ss_mem]. unfold pjw_saveJ; repeat (eapply awr_ok_cons_stack;
      [reflexivity | exact Usp5 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]); apply awr_ok_nil. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msD end.
  assert (KEEPE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 24 <= a < spZ regs) ->
    aview SEGS (w_H W6) (ms_mem msD) a = aview SEGS (w_H W6) mem6 a).
  { eapply pjw_keep_frame; [ intros; reflexivity | exact HFr |].
    intros a (r & Hr & Ha). unfold pjw_saveJ in Hr.
    lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change rs0 with rs1 in Hr end.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp5 in Ha; lia |]).
    destruct Hr. }
  clear HF HFr HG.
  prreg HS (1%bv : bv 5) Rra7. prreg HS (10%bv : bv 5) Ra07.
  assert (HAEB : env_agree 32 (Ereg regs []) EB)
    by (unfold EB; apply env_agree_havoc_ge; [lia | exact HAEJ]).
  assert (HAE7 : env_agree 32 (Ereg regs []) EF)
    by (unfold EF; apply env_agree_havoc_ge; [lia | exact HAEB]).
  assert (HPRES7 : aregs_preserved regs (ms_regs msD)).
  { pose proof HS as HSu; red in HSu.
    eapply (aregs_preserved_of_st_ok (fx := fxc) SEGS (w_H W6) EF _ _ regs []);
      [exact HSu | exact HAE7 | vm_compute; reflexivity]. }
  assert (RA7 : getr (ms_regs msD) 1 = getr regs 1).
  { rewrite Rra7; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (AG5 1%nat) by lia.
    exact (ew_Ereg_nat regs _ 1 1%bv eq_refl). }
  assert (RB7 : getr (ms_regs msD) 10 = w64 0)
    by (rewrite Ra07; cbn [sv_denot]; reflexivity).
  (* the model at the end: the buffer (if any) is gone from the ledger, and Lam is the entry's *)
  assert (HBUF0 : buf1 = 0 -> WriterApp.w_cap stT = 0).
  { intros Hb0. destruct TO10 as [(Hz & _) | (_ & Hin1 & _)]; [exact Hz |].
    exfalso. destruct (pjw_led_hb ly3 S3 Hp3 W3 (ms_mem msJ) Lam1 peak1 _ _ ran1 _ _ _ _ HLED1 Hin1) as (_ & Hab1 & _).
    destruct (alx_blocks SEGS B ARx LAWS ly3 S3 Hp3 W3 (ms_mem msJ) mdJ _ _ HAR3m Hab1) as (_ & H4096 & _). lia. }
  assert (HEND : prh_ledger (PI := prh_img_A) B ly6 S6 Hp6 W6 mem6 Lam peak1
                   (WriterApp.w_cnt stT) (WriterApp.w_fail stT) ran1 most own /\
                 Permutation (ablocks B ly6 S6) (ablocks B ly S) /\
                 ((WriterApp.w_cap stT = 0 /\ peak1 = peak) \/
                  (WriterApp.w_cap stT <> 0 /\ peak1 = Z.max peak (Ledger.lsum Lam + WriterApp.w_cap stT)))).
  { destruct HBLK1 as [(Ec & Eb & EL & Ep & Hperm) | (Hlt & l1 & l2 & b1 & b2 & Hcc & EL & Ep & Hperm)].
    - cbn [WriterApp.w0 WriterApp.w_cap] in Ec.
      (* the arm READ BY SHAPE: its ledger and its block list named by their statements *)
      destruct HFARM as [HA | (Hpn & _)]; [| exfalso; exact (Hpn Eb)].
      pjw_split HA. pjw_pick @prh_ledger HLED6.
      lazymatch goal with H : ablocks B ly6 S6 = _ |- _ => rename H into EAB end.
      rewrite EL in HLED6. rewrite EAB.
      split; [exact HLED6 |]. split; [exact Hperm | left; split; [exact Ec | exact Ep]].
    - cbn [WriterApp.w0 WriterApp.w_cap] in Hlt.
      destruct Hcc as [(_ & -> & -> & -> & ->) | (Hne & _)];
        [| exfalso; cbn [WriterApp.w0 WriterApp.w_cap] in Hne; exact (Hne eq_refl)].
      cbn [app] in EL, Ep, Hperm.
      assert (Hbn : buf1 <> 0) by (intros Hb0; pose proof (HBUF0 Hb0); lia).
      (* the arm READ BY SHAPE: its block split and its ledger split named by their statements *)
      destruct HFARM as [(Hp0 & _) | HB]; [exfalso; exact (Hbn Hp0) |].
      pjw_split HB.
      match goal with H : ex ?P |- _ =>
        lazymatch P with context [ablocks] => destruct H as (b1' & b2' & EAB3 & EAB6) end end.
      match goal with H : ex ?P |- _ =>
        lazymatch P with context [prh_ledger] => destruct H as (l1' & l2' & ELam & HLED6) end end.
      assert (Hnd : NoDup (map fst Lam1))
        by (exact (pjw_led_nodup ly3 S3 Hp3 W3 (ms_mem msJ) Lam1 peak1 _ _ ran1 _ _ HLED1)).
      rewrite EL in Hnd, ELam.
      destruct (prhW_nodup_head (buf1, WriterApp.w_cap stT) Lam l1' l2' Hnd ELam) as [-> ->].
      cbn [app] in HLED6.
      split; [exact HLED6 |]. split; [| right; split; [lia | exact Ep]].
      rewrite EAB6. rewrite EAB3 in Hperm.
      apply Permutation_sym. eapply Permutation_cons_app_inv. apply Permutation_sym. exact Hperm. }
  destruct HEND as (HLED6 & HPERM6 & HPEAK6).
  (* the room invariant at the end: a non-NULL free gives it; a NULL free keeps the state *)
  assert (HROOM6' : room_live_cf S6).
  { destruct (Z.eq_dec buf1 0) as [Hb0 | Hbn]; [| exact (HROOM6 Hbn)].
    destruct HFARM as [(_ & ES6 & _) | (Hpn & _)]; [rewrite ES6; exact HROOM3 | exfalso; exact (Hpn Hb0)]. }
  assert (TLEDE : prh_ledger (PI := prh_img_A) B ly6 S6 Hp6 W6 (ms_mem msD) Lam peak1
                    (WriterApp.w_cnt stT) (WriterApp.w_fail stT) ran1 most own)
    by (eapply pjw_ledger_keep; [exact (ajxR_ar HJW6) | exact HLED6 | exact KEEPE | intros a Ha; cbv beta; lia]).
  (* the return keeps the world: its SRr lifts into the walk's relation (SRr_SRrG at wle_wle') *)
  apply (SRr_SRrG SEGS (wle' SEGS RZ_cf) (wle_wle' SEGS RZ_cf)).
  eapply (RETc W6 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat7.
  split; [| exact HPM].
  unfold fpostF, apost_base_xFR, pjw_Q.
  lazymatch goal with
  | |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists fxc, ly6, S6, Hp6, rg, m, d
  end.
  eexists.
  split; [ unfold YK0s.ret_ok in Hra; cbn [ms_regs ms_mem]; rewrite RA7, Hra; reflexivity |].
  split; [ exact HFZc |].
  split; [ exact HFKc |].
  split; [ eapply ajournal_x_materializeR;
           first [exact LAWS | exact (@pa_segs_low _ A_prog_listing PA) | exact PST_ok | exact HJ6] |].
  split; [ exact HPRES7 |].
  exists ok1, ran1, 0, Lam, peak1.
  cbn [WriterApp.w0 WriterApp.w_cnt WriterApp.w_fail] in HOKS1.
  split; [ exact HOKS1 |].
  split; [ exact RB7 |].
  split; [ exact HROOM6' |].
  (* DEAD-PJWRITE: no grow of ok1 was refused (the composed callee posts' prh_granted) *)
  split; [ exact HGR1 |].
  split.
  { (* THE EXACT ADVANCE, under no refusal (the kit's prh_granted): then the run IS the all-granted run, whose next
       event after the puts' is this fuzz_free (buf) (prhWriter_pjw_evs): fuzz_free's p <> 0 arm transfers the
       position at E = [HFr (cap + cf_head)]; with no buffer the free is NULL, its p = 0 arm at E = [] *)
    intros HGR.
    assert (HFAILn : WriterApp.w_failed stT <> 0) by (rewrite <- Efl; exact Hc0f).
    destruct (Z.eq_dec buf1 0) as [Hb0 | Hbn].
    - assert (E0 : forall X : nat, (X + length (@nil PresetReqAt.hev))%nat = X) by (intros; cbn [length]; lia).
      destruct (HPF0 Hb0 rp_sm rp_x rp_os rp_i1 rp_H0 rp_hist1 HPOS1 ltac:(unfold prh_run_at; reflexivity))
        as (rp_hist2 & Hpos2).
      rewrite E0 in Hpos2.
      rewrite pjw_evs_nobuf by (change (WriterApp.w_cap stT = 0); exact (HBUF0 Hb0)).
      exists rp_hist2. exact Hpos2.
    - assert (HCAPn : WriterApp.w_cap stT <> 0).
      { destruct TO10 as [(_ & Hb & _) | ((j & Hj & Ej) & _)]; [exfalso; exact (Hbn Hb) |].
        rewrite Ej. pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) ltac:(lia)). lia. }
      pose proof HLED as HLB. apply prh_ledger_bounds in HLB. destruct HLB as (_ & _ & HCB & HFB & _).
      destruct (pjw_granted ok1 (WriterApp.w0 cnt fail) (WriterValue.wdpieces t (negb (pretty =? 0)))
                  ltac:(cbn [WriterApp.w0 WriterApp.w_cnt]; lia) ltac:(cbn [WriterApp.w0 WriterApp.w_fail]; lia) HGR)
        as (EPUT & EEVS).
      fold stT in EPUT.
      pose proof HEVS as HEV1.
      rewrite (pjw_evs_free [] cnt fail (WriterValue.wdpieces t (negb (pretty =? 0))))
        in HEV1 by (rewrite <- EPUT; assumption).
      apply prh_run_at_app_iff in HEV1 as (_ & HEV2).
      rewrite <- EPUT, <- EEVS in HEV2.
      destruct (HPFR Hbn rp_sm rp_x rp_os rp_i1 rp_H0 rp_hist1 HPOS1 HEV2) as (rp_hist2 & Hpos2).
      exists rp_hist2.
      rewrite (pjw_evs_free ok1 cnt fail (WriterValue.wdpieces t (negb (pretty =? 0))) HFAILn HCAPn).
      rewrite length_app. cbn [length] in Hpos2 |- *. rewrite Nat.add_assoc. exact Hpos2. }
  split; [ eapply (pjw_nodeR_end _ STK ly S Hp W regs mem md ch Lam peak cnt fail ran most own v t D
                     ly6 S6 Hp6 W6 (ms_mem msD) _ _ Lam peak1 _ _ ran1 most own);
           [exact HPRE1 | exact HLED | exact TLEDE | exact HJ6 | exact HNODE | exact HLOC | exact HDL
            | intros a k Hin; exact Hin] |].
  split; [ eapply pjw_tree_vis_of; [exact (ajxR_ar HJ6) | exact TLEDE | exact HDL] |].
  split; [ exact TLEDE |].
  right.
  split; [ change (WriterApp.w_failed stT <> 0); rewrite <- Efl; exact Hc0f |].
  split; [reflexivity |]. split; [reflexivity |].
  split; [ exact HPERM6 |].
  (* the refusal peak is 0 under prh_granted (S7a_WriterRet's prhW_rpeak_granted), and peak >= 0 (the ledger) *)
  rewrite (prhW_rpeak_granted ok1 Lam (WriterApp.w0 cnt fail) _ HGR1).
  pose proof HLED as HLB0. apply prh_ledger_bounds in HLB0. destruct HLB0 as (HLB0 & _).
  fold stT.
  destruct HPEAK6 as [(HcE & HpE) | (HcE & HpE)]; [left | right]; (split; [exact HcE | lia]).
Qed.

Theorem pjw_walk : forall (n : nat)
  (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk) (most own : Z)
  ly S Hp W regs mem md ch v pretty (t : PjTree.jv) D Lam peak cnt fail ran,
  fpre B ARx (STK_pj_write n) ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* the texts' bound on the run's outcome list (the hull drafts): write_value's and put's texts take it, and the
     tail pays fuzz_free's hull budget under it *)
  (length rp_os <= 4)%nat ->
  prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_pjw_evs [] cnt fail (WriterValue.wdpieces t (negb (pretty =? 0))))) ->
  getr regs 10 = w64 v -> getr regs 11 = w64 pretty -> 0 <= pretty < 2 ^ 31 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_pjw_evs [] cnt fail (WriterValue.wdpieces t (negb (pretty =? 0)))) ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/ (exists x y, In (x, y) Lam /\ x <= v /\ v + 56 <= x + y) \/
   prhWriter_in_frame ly S v) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  prhWriter_tree_vis W mem D ->
  (forall a k, In (a, k) D -> In (a, k) Lam) ->
  (PjTree.depth t <= n)%nat -> Z.of_nat (PjTree.depth t) <= 2 ^ 31 - 1 ->
  Z.of_nat (length (frames S)) < fs_frames 0 ->
  Z.of_nat (length (WriterValue.wdoc t (negb (pretty =? 0)))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  blocks_bytes S + LIVE_pj_write t (negb (pretty =? 0)) <= LIVE_MAX ->
  pjw_ARGCNT (STK_pj_write n) rp_sm rp_x rp_os rp_H0 ly S Hp W regs mem md ->
  Pm mem ->
  SRr' SEGS RZ_cf W (cfg_at SEGS (SIGMA AS_pj_write) regs mem md)
    (fun W' c' =>
       fpostF B ARx SK (STK_pj_write n) [] regs ly S Hp W mem md
         (pjw_Q rp_sm rp_x rp_os rp_i rp_H0 ly S v pretty t D Lam peak cnt fail ran most own) W' c' /\
       Pm (ms_mem (cfg_ms c'))).
Proof.
intros n rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own.
intros ly S Hp W regs mem md ch v pretty t D Lam peak cnt fail ran.
intros HPRE HUNIV HROOM HPOS HOS HCONS H10 H11 HPR HLED HEVS HNODE HLOC HRA HTV HDL HDEP HDEP2 HFRS HWMAX HMAX2
  HLIVE ARGCNT HPM.
(* the walk's relation wle' SEGS RZ_cf: the runners, the branch rule and the binds below conclude SRrG at it *)
unfold SRr'.
pose proof HPRE as (HPRE1 & HRO & HTOP & HRAZE & HFRM).
(* write_value's run events: the first part of pj_write's (PRH_FnWriter prhWriter_evs_app0, PRH_Base
   prh_run_at_app_iff) *)
assert (HEVWV : prh_run_at rp_sm rp_x rp_os rp_i
                  (prhWriter_evs [] (WriterApp.w0 cnt fail) (WriterValue.wvpieces t (negb (pretty =? 0)) 0))).
{ pose proof HEVS as H0. unfold prhWriter_pjw_evs, WriterValue.wdpieces in H0. cbv zeta in H0.
  rewrite prhWriter_evs_app0, <- app_assoc in H0. apply prh_run_at_app_iff in H0 as (H0 & _). exact H0. }
assert (HPJF : pi_frame F_pj_write = 64) by (vm_compute; reflexivity).
set (STK := STK_pj_write n) in *.
assert (HSTK : 64 + ESTACK <= STK)
  by (unfold STK, STK_pj_write, zmaxl; cbn [fold_right]; rewrite HPJF; unfold STK_RT_ECALL; lia).
unfold ESTACK in HSTK.
assert (HWVSTK : STK_write_value n + 64 <= STK)
  by (unfold STK, STK_pj_write, zmaxl; cbn [fold_right]; rewrite HPJF; lia).
assert (HFFSTK : STK_fuzz_free + 64 <= STK)
  by (unfold STK, STK_pj_write, zmaxl; cbn [fold_right]; rewrite HPJF; lia).
destruct (pjw_entry STK ly S Hp W regs mem md ch ltac:(lia) HPRE1) as [HS SHOK].
pose proof HPRE1 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* ---- the facts of the entry state the whole walk uses ---- *)
assert (HWVF : pi_frame F_write_value = 176) by (vm_compute; reflexivity).
assert (HWV0 : 8192 <= STK_write_value n)
  by (unfold STK_write_value, zmaxl, STK_RT_STR, ESTACK; cbn [fold_right]; rewrite HWVF; lia).
assert (HSTK2 : 8256 <= STK) by lia.
(* everything pj_write's own steps may write lies in pjw_wr; the heap, the image and the tree are outside *)
assert (HLOWWR8 : forall a, 0 <= a < YM05.alloc_ceiling + 8 -> ~ pjw_wr (spZ regs) a)
  by (intros a Ha; unfold pjw_wr, ESTACK; lia).
assert (HLOWWR : forall a, 0 <= a < YM05.alloc_ceiling -> ~ pjw_wr (spZ regs) a)
  by (intros a Ha; unfold pjw_wr, ESTACK; lia).
pose proof (pjw_foot_ok STK ly S Hp W regs mem md ch Lam peak cnt fail ran most own v D HPRE1 HLED HLOC HDL) as FOOT.
assert (FOOTWR : forall x, pj_footR v D x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ ~ pjw_wr (spZ regs) x).
{ intros x Hx. destruct (FOOT x Hx) as (F1 & F2 & F3). split; [lia|]. split; [exact F2|].
  unfold pjw_wr, ESTACK. lia. }
assert (VB : 0 <= v /\ v + 56 <= 2 ^ 47)
  by (destruct (FOOT (v + 55) ltac:(left; lia)) as (F1 & _); destruct (FOOT v ltac:(left; lia)) as (F2 & _); lia).
assert (DNZ : forall a k, In (a, k) D -> a <> 0).
{ intros a k Hin. pose proof HLED as (_ & _ & HHB & _). rewrite Forall_forall in HHB.
  destruct (HHB _ (HDL a k Hin)) as (_ & Hab & _). cbn [fst snd] in Hab.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & _).
  pose proof cf_head_nonneg. lia. }
assert (WM : Z.of_nat (length (concat (WriterValue.wvpieces t (negb (pretty =? 0)) 0))) + 1 <= prhWriter_WMAX).
{ unfold WriterValue.wdoc, WriterValue.wdpieces in HWMAX. rewrite concat_app, length_app, Nat2Z.inj_add in HWMAX. lia. }
(* write_value's consumer window and live room at each event (the batch kit's PRH_FnWriter.v:672-673, :745): the head of
   pj_write's window (pjw_cons_wv), and the per-event room from pj_write's entry budget (pjw_live0) *)
assert (HCWV : prh_cons_from rp_sm rp_x rp_os rp_i
                 (length (prhWriter_evs [] (WriterApp.w0 cnt fail) (WriterValue.wvpieces t (negb (pretty =? 0)) 0)))).
{ pose proof HCONS as H0. unfold WriterValue.wdpieces in H0. exact (pjw_cons_wv _ _ _ _ _ _ _ _ H0). }
assert (HLVWV : prh_live_evs S
                  (prhWriter_evs [] (WriterApp.w0 cnt fail) (WriterValue.wvpieces t (negb (pretty =? 0)) 0)))
  by (apply pjw_live0; [exact cf_head_nonneg | exact HLIVE | exact HWMAX]).
assert (HO8 : (spZ regs - 56) mod 8 = 0).
{ replace (spZ regs - 56) with ((2 * (spZ regs / 16) - 7) * 8)
    by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)); lia).
  apply Z_mod_mult. }
(* the entry journal at the walk's relation (ajournal_x_initR at wle' SEGS RZ_cf, reflexive) *)
assert (HJ : ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) STK (spZ regs) []
  ly S Hp W mem md [] ly S Hp W mem md 0).
{ eapply (ajournal_x_initR (SK := SK)); first [exact (wle'_refl SEGS RZ_cf) | exact HPRE1 | exact LAWS | idtac]. }
set (E := pjw_E regs) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold pjw_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; unfold pjw_E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; unfold pjw_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold cfg_at. rewrite Hent. change (w64 (BASE + AF_pj_write)) with (Z_to_bv 64 (BASE + AF_pj_write)).
paj_run_tok_x_inv RUNI HS HJ SHOK HPM PJW_Bspan.
{ unfold pjw_ss, pjw_regions, pjw_save, pjw_o, pjw_pad. cbn [ss_mem].
  repeat (eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]).
  apply awr_ok_nil. }
assert (AG : forall m, (m < 33)%nat -> ew E m = ew (Ereg regs []) m)
  by (intros m Hm; unfold E, pjw_E; apply Eimg_low; unfold A_TEXT; lia).
(* the prologue wrote only the frame *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ pjw_wr (spZ regs) a ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ eapply pjw_keep_frame; [intros; reflexivity | exact HFr |].
  intros a (r & Hr & Ha).
  lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change rs0 with rs1 in Hr end.
  unfold pjw_wr, ESTACK.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha; lia |]).
  destruct Hr. }
clear HF HFr HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
(* __asan_memset keeps the world (W2 = W): its rule over the journal at wle' SEGS RZ_cf concludes SRr, lifted into
   the walk's relation by SRr_SRrG at wle_wle' *)
eapply (SRrG_bind SEGS (wle' SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
{ apply (SRr_SRrG SEGS (wle' SEGS RZ_cf) (wle_wle' SEGS RZ_cf)).
  eapply (YGcallMxmn.aj_intrin_at_xmR SEGS B (@prh_pst prh_img_A) ARx LAWS segs_low (wle' SEGS RZ_cf) OSet
    (SIGMA AS___asan_memset) AMS W _ _ STK (spZ regs) [] ly S Hp W mem md [] ly S Hp _ _ (spZ regs - 56) 0 32 (-64)
    _ HJ).
  all: first
     [ rewrite Ra0, Usp; unfold w64; f_equal; lia
     | rewrite Ra1; reflexivity
     | rewrite Ra2; reflexivity
     | rewrite Rgp, (AG 3%nat) by lia; exact Hgp
     | rewrite Rtp, (AG 4%nat) by lia; exact Htp
     | exact Rra
     | unfold spZ; rewrite Rsp; rewrite unsigned_lit_small by (rewrite Usp; lia); rewrite Usp; unfold spZ; lia
     | reflexivity
     | unfold ESTACK; lia
     | lia
     | exact I
     | apply ret_ok_codeptr_v; [lia | vm_compute; reflexivity]
     | intros a Ha; split; [left; lia | unfold ESTACK; lia]
     | unfold amem_range, kHighMemBeg, kHighMemEnd in *; lia
     | eapply pjw_ra_stack; [exact (ajxR_ar HJ) | lia | lia]
     | intros _; eapply pjw_hull_stack; [exact (ajxR_ar HJ) | lia | lia | lia] ]. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Hset & Hfr & Hpres2 & HMNs).
(* the memory invariant across __asan_memset (its m-form keep, srr_inv_call) *)
pose proof (PCALL _ _ HMNs HPM) as HPM2. clear HPM HMNs. rename HPM2 into HPM.
(* the memset wrote only the struct and its own ESTACK window *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ pjw_wr (spZ regs) a ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hw. rewrite Hfr; [apply KEEP1; assumption | exact Ha | unfold pjw_wr, ESTACK in *; lia
  | unfold pjw_wr, ESTACK in *; lia]. }
(* the struct is zero now; the saved registers are kept, the struct and the pad regions are dropped. The kit's
   `reseat` does not fit here: its K lazymatch has the st_ok case at three arguments. *)
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W) mem2) HP2 (0%nat :: @nil nat) HS2.
match type of HS2 with ?Q -> _ =>
  assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
                     kept_intrin Hfr Hpres2 AG Usp
                   | specialize (HS2 HQ); clear HQ ] end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
pose proof HEI as HEIe. clear HEI. set (E1 := havoc E 33 (map (getr regs2) CLOB)) in HS.
assert (HEI : img_env VAL A_LIM E1) by (unfold E1; apply img_env_havoc; [exact HEIe | vm_compute; lia]).
assert (AG1 : forall m, (m < 33)%nat -> ew E1 m = ew (Ereg regs []) m)
  by (intros m Hm; unfold E1; rewrite ew_havoc_old by lia; apply AG; lia).
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite (AG1 2%nat) by lia; rewrite <- (AG 2%nat) by lia; exact Usp).
assert (SHOK1 : sh_ok SEGS PJW_Bx [] E1 (mrestrict (w_H W) mem2)) by constructor.
paj_run_tok_x_inv RUNI HS HJ2 SHOK1 HPM PJW_Bspan.
{ cbn [ss_mem]. eapply awr_ok_cons_stack;
    [reflexivity | exact Usp1 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
(* the second stretch (A 0x86c38 .. 0x86c48) writes nothing but registers *)
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ pjw_wr (spZ regs) a ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ eapply pjw_keep_frame; [exact KEEP2 | exact HFr |].
  intros a (r & Hr & Ha).
  lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change rs0 with rs1 in Hr end.
  unfold pjw_wr, ESTACK.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp1 in Ha; lia |]).
  destruct Hr. }
assert (Z0 : forall i, 0 <= i < 32 -> aview SEGS (w_H W) (ms_mem ms0) (spZ regs - 56 + i) = Some 0).
{ intros i Hi.
  assert (Hm : aview SEGS (w_H W) (ms_mem ms0) (spZ regs - 56 + i) = aview SEGS (w_H W) mem2 (spZ regs - 56 + i)).
  { apply (aview_eq_of SEGS). apply HFr. rewrite unsigned_lit_small by lia. intros (r & Hr & Ha).
    lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change rs0 with rs1 in Hr end.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp1 in Ha; lia |]).
    destruct Hr. }
  rewrite Hm, Hset by lia. reflexivity. }
clear HF HFr HG Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) Rs0.
assert (SPZ3 : spZ (ms_regs ms0) = spZ regs - 64)
  by (unfold spZ; rewrite Rsp; rewrite unsigned_lit_small by (rewrite Usp1; lia); rewrite Usp1; unfold spZ; lia).
pmkst HS.
(* ---- write_value (o, v, pretty, 0) at A 0x86c48, caller window 64 = pj_write's frame; its text is in the
   window-and-float form at wle' (the kit's primed twrite_value_specX: SRr' SEGS RZ_cf, the post fpostWFmR at
   wle' SEGS RZ_cf), so the call rule is aj_call_xWFR at that relation and the continuation runs at the float state
   it returns at ---- *)
eapply (SRrG_bind SEGS (wle' SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
{ eapply (aj_call_xWFR SEGS B (@prh_pst prh_img_A) ARx LAWS segs_low (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf)
    (wle'_trans SEGS RZ_cf) W _ _ _ STK (spZ regs) [] ly S Hp W mem md []
    ly S Hp _ _ (STK_write_value n) 64 (prhWriter_cfp (spZ regs - 56) 0 0) (-64) _ [] _ HJ2).
  all: first
     [ exact Rra
     | rewrite SPZ3; lia
     | reflexivity
     | lia
     | rewrite Rgp, (AG1 3%nat) by lia; exact Hgp
     | rewrite Rtp, (AG1 4%nat) by lia; exact Htp
     | apply ret_ok_codeptr_v; [lia | vm_compute; reflexivity]
     | rewrite unsigned_lit_small by (pose proof (@pa_B_ok _ _ PA); lia); pose proof (@pa_B_ok _ _ PA); lia
     | apply achain_low; unfold s0Z; rewrite Rs0, (AG1 11%nat) by lia;
       rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), H11; unfold w64;
       rewrite unsigned_lit_small by lia; lia
     | let a := fresh "a" in let Ha := fresh "Ha" in let r := fresh "r" in let Hr := fresh "Hr" in
       intros a Ha; unfold prhWriter_cfp, prhWriter_fp in Ha; cbn in Ha;
       destruct Ha as (r & [<- | []] & Hr); cbn [fst snd] in Hr; right; right; right; lia
     | (* the callee: the kit's write_value text (its one use) *)
       let HPRE2 := fresh "HPRE2" in let HWIN2 := fresh "HWIN2" in intros HPRE2 HWIN2;
       eapply (HWV n rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W _ _ _ [] (spZ regs - 56) v pretty 0 64 0
                 (WriterApp.w0 cnt fail) t D Lam peak ran);
       first
       [ exact HROOM | exact HPOS | exact HOS | exact HEVWV | exact HUNIV | exact HDEP | exact HWIN2 | exact HFRS
       | exact HMAX2 | exact HCWV | exact HLVWV
       | split; [exact HPRE2 | split; [eapply pjw_arodata_keep; [exact HRO | exact KEEP3 | exact HLOWWR]
                                      | split; [rewrite SPZ3; lia
                                               | split; [unfold raZ; rewrite Rra;
                                                         rewrite unsigned_lit_small
                                                           by (pose proof (@pa_B_ok _ _ PA); lia);
                                                         pjw_ret_ceil_tac
                                                        | (* the entry rounding mode *) exact HFRM]]]]
       | rewrite Ra0, Usp1; unfold w64; f_equal; lia
       | rewrite Ra1, (AG1 10%nat) by lia; exact H10
       | rewrite Ra2, (AG1 11%nat) by lia; exact H11
       | exact Ra3
       | rewrite SPZ3; lia
       | lia
       | apply pjw_out0; [exact HO8 | exact Z0]
       | eapply pjw_ledger_keep; [exact HAR | exact HLED | exact KEEP3 | exact HLOWWR8]
       | eapply pjw_nodeR_keep; [exact HNODE | exact FOOTWR | exact KEEP3]
       | eapply (pjw_loc ly S Hp W mem md Lam peak cnt fail ran most own v (spZ regs));
           [exact HAR | exact HLED | rewrite SPZ3; lia | exact HLOC]
       | eapply pjw_ra_keep; [lia | lia | exact HRA | exact KEEP3 | exact HLOWWR]
       | eapply pjw_tree_vis_keep; [exact HTV | exact KEEP3 | exact HLOWWR]
       | let a := fresh "a" in let k := fresh "k" in let Hin := fresh "Hin" in
         intros a k Hin; split; [exact (HDL a k Hin) | exact (DNZ a k Hin)]
       | let x := fresh "x" in let Hx := fresh "Hx" in let Hf := fresh "Hf" in
         intros x Hx Hf; destruct (FOOT x Hf) as (_ & _ & [Hlt | Hge]); lia
       | (* wv_s0 (the kit's premise of twrite_value_specX, PRH_FnWriter.v d89d3c67b78c at the cut): pj_write's s0 is pretty < 2 ^ 31 < alloc_ceiling *)
         right; unfold s0Z; rewrite Rs0, (AG1 11%nat) by lia;
         rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), H11; unfold w64;
         rewrite unsigned_lit_small by lia; pose proof (@YM05.alloc_ceiling_value rc); lia
       | cbn [WriterApp.w0 WriterApp.w_text length Z.of_nat]; lia ] ]. }
cbv beta. intros W3 c3 Hwle3
  (fx3 & ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & -> & HFZ3 & HFK3 & HJ3 & HJW3 & HKW3 & HP3 & HQ3).
(* The kit's post (PRH_FnWriter.v twrite_value_specX), READ BY SHAPE: the room, the tree, and the writer with its
   outcomes ok and the exact advance under them; the float state fx3 it returns at has frm 0 and the entry's
   fs0-fs11 *)
unfold fQmn in HQ3. cbv beta in HQ3. pjw_split HQ3.
lazymatch goal with H : room_live_cf S3 |- _ => rename H into HROOM3 end.
match goal with H : ex ?P |- _ => lazymatch P with context [prhWriter_ret_ok] => rename H into HRET3 end end.
lazymatch goal with H : YAkMemnorm.memnorm _ _ -> YAkMemnorm.memnorm _ mem3 |- _ => rename H into HMN3 end.
(* the memory invariant across write_value (its m-form keep, srr_inv_call) *)
pose proof (PCALL _ _ HMN3 HPM) as HPM3. clear HPM HMN3. rename HPM3 into HPM.
pose proof (ajxR_ar HJ3) as HAR3. pose proof (ajxR_pres HJ3) as HPRES3.
(* re-seat after write_value: the saved registers are outside its footprint (the struct), so its window clause keeps
   them, and pj_write's journal keeps them present *)
jafter_call_keep_pi HS 49%nat regs3 (mrestrict (w_H W3) mem3) HP3 (0%nat :: @nil nat) HS3.
match type of HS3 with ?Q -> _ =>
  assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp1; intros a Ha;
    [ apply (mbyte_of_aview SEGS); apply HKW3;
      [ lia
      | let r := fresh "r" in let Hr := fresh "Hr" in let Hra := fresh "Hra" in
        intros (r & Hr & Hra); unfold prhWriter_cfp, prhWriter_fp in Hr; cbn in Hr;
        destruct Hr as [<- | []]; cbn [fst snd] in Hra; lia ]
    | intros _; apply (apresent_writable SEGS); apply HPRES3; lia ]
  | specialize (HS3 HQ); clear HQ ] end.
clear HS. rewrite <- (restrict_mkst_fx (fx := fx)) in HS3.
(* the symbolic state moves to write_value's return float state; from here every step runs at fx3 *)
apply (pjw_xfx fx fx3) in HS3. rename HS3 into HS.
pose (RUNI3 := @paj_run_x_invR fx3 rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
pose (RUNTOI3 := @paj_run_to_x_invR fx3 rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
pose (BR3 := YSRrG.paj_branchR (fx := fx3) (PI := PA) (wle' SEGS RZ_cf)).
pose proof HEI as HEIe1. clear HEI. set (EW := havoc E1 49 (map (getr regs3) CLOB)) in HS.
assert (HEI : img_env VAL A_LIM EW) by (unfold EW; apply img_env_havoc; [exact HEIe1 | vm_compute; lia]).
assert (AG2 : forall m, (m < 33)%nat -> ew EW m = ew (Ereg regs []) m)
  by (intros m Hm; unfold EW; rewrite ew_havoc_old by lia; apply AG1; lia).
assert (Usp2 : bv_unsigned (ew EW 2) = spZ regs) by (rewrite (AG2 2%nat) by lia; rewrite <- (AG 2%nat) by lia; exact Usp).
assert (SHOK2 : sh_ok SEGS PJW_Bx [] EW (mrestrict (w_H W3) mem3)) by constructor.
(* ---- the branch on pretty (A 0x86c4c `beqz s0`) ---- *)
psrr_branch_tok RUNI3 BR3 HS SHOK2 PJW_Bspan.
- (* pretty = 0: no newline; the branch goes straight to the loads (A 0x86c64), the join *)
  paj_run_to_tok_x_inv RUNTOI3 HS HJ3 SHOK2 HPM PJW_Bspan (AF_pj_write + 4 * 21).
  { cbn [ss_mem]. eapply awr_ok_cons_stack;
      [reflexivity | exact Usp2 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msT end.
  assert (HEW11 : ew EW 11 = Z_to_bv 64 pretty)
    by (rewrite (AG2 11%nat) by lia; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  rewrite branch_eq_U, (U_atom EW 11 pretty HEW11 ltac:(lia)), (U_lit EW 0 ltac:(lia)) in Hc.
  assert (Hpt : negb (pretty =? 0) = false) by (rewrite Hc; reflexivity).
  (* the branch stretch writes nothing *)
  assert (KEEPT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 24 <= a < spZ regs) ->
    aview SEGS (w_H W3) (ms_mem msT) a = aview SEGS (w_H W3) mem3 a).
  { eapply pjw_keep_frame; [intros; reflexivity | exact HFr |].
    intros a (r & Hr & Ha).
    lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change rs0 with rs1 in Hr end.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp2 in Ha; lia |]).
    destruct Hr. }
  clear HF HFr HG.
  (* the writer's return relation at the join memory (the branch stretch moved nothing), its outcomes and its exact
     advance as write_value's post gave them (pretty = 0: pj_write's pieces are write_value's) *)
  assert (HRETJ : exists okJ, prhWriter_ret_ok B okJ ly S Lam peak ran most own (spZ regs - 56) 0 (WriterApp.w0 cnt fail)
                    (WriterValue.wdpieces t (negb (pretty =? 0))) ly3 S3 Hp3 W3 regs3 (ms_mem msT) md3 /\
                  prh_granted okJ cnt fail
                    (prhWriter_k okJ (WriterApp.w0 cnt fail) (WriterValue.wdpieces t (negb (pretty =? 0)))) /\
                  exists rp_hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
                    (rp_i + length (prhWriter_evs okJ (WriterApp.w0 cnt fail)
                                      (WriterValue.wdpieces t (negb (pretty =? 0)%Z))))%nat rp_H0 rp_hist' S3).
  { replace (WriterValue.wdpieces t (negb (pretty =? 0)))
      with (WriterValue.wvpieces t (negb (pretty =? 0)) 0)
      by (unfold WriterValue.wdpieces; rewrite Hpt; symmetry; apply app_nil_r).
    (* the existential's body READ BY SHAPE: its conjuncts are discharged by the hypotheses of their types *)
    destruct HRET3 as (ok1 & HRw). pjw_split HRw. exists ok1. split; [| split; [assumption | assumption]].
    eapply (pjw_ret_keep ok1 ly S Lam peak ran most own (spZ regs - 56) 0 _ _ ly3 S3 Hp3 W3 regs3 mem3 md3
              regs3 (ms_mem msT) md3 (fun a => spZ regs - 24 <= a < spZ regs));
      [ exact (ajxR_ar HJW3) | eassumption | exact KEEPT
      | intros a Ha; cbv beta; lia | intros a Ha; cbv beta; split; lia ]. }
  (* THE JOIN: the caller-saved registers into the band 65..80, the branch fact dropped *)
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssm _ =>
    let pcm := eval vm_compute in (ss_pc ssm) in
    jafter_stretch_pi HS 65%nat (ms_regs msT) (mrestrict (w_H W3) (ms_mem msT)) CLOB pcm HS2
  end.
  specialize (HS2 ltac:(intros; reflexivity)).
  specialize (HS2 ltac:(repeat apply Forall_cons; try apply Forall_nil; split; intros; [reflexivity | assumption])).
  apply (pjw_drop_cond fx3) in HS2.
  lazymatch type of HS2 with st_ok_pi _ _ _ ?s _ =>
    replace s with pjw_ssT in HS2 by (vm_compute; reflexivity) end.
  clear HS. rewrite <- (restrict_mkst_fx (fx := fx3)) in HS2. rename HS2 into HS.
  pose proof HEI as HEIe4. clear HEI.
  set (EJ := havoc EW 65 (map (getr (ms_regs msT)) CLOB)) in HS.
  assert (HEI : img_env VAL A_LIM EJ)
    by (unfold EJ; apply img_env_havoc; [exact HEIe4 | vm_compute; lia]).
  assert (AGJ : forall m, (m < 33)%nat -> ew EJ m = ew (Ereg regs []) m)
    by (intros m Hm; unfold EJ; rewrite ew_havoc_old by lia; apply AG2; lia).
  assert (HAEJ : env_agree 32 (Ereg regs []) EJ)
    by (split; [intros m Hm; first [apply AGJ | symmetry; apply AGJ]; lia | reflexivity]).
  assert (SHOKJ : sh_ok SEGS PJW_Bx [] EJ (mrestrict (w_H W3) (ms_mem msT))) by constructor.
  eapply (pjw_tail fx3);
    first [ exact HFZ3 | exact HFK3 | exact HSTK | exact HFFSTK | exact HPRE | exact HUNIV | exact H11 | exact HPR
          | exact HLED | exact HNODE | exact HLOC | exact HDL | exact HS | exact SHOKJ | exact HEI | exact AGJ
          | exact HAEJ | exact HJ3 | exact HPM | exact HROOM3 | exact HOS | exact HEVS | exact HRETJ
          | exact ARGCNT ].
- (* pretty <> 0: the newline put (A 0x86c60), then the same tail *)
  idtac.
  paj_run_tok_x_inv RUNI3 HS HJ3 SHOK2 HPM PJW_Bspan.
  { cbn [ss_mem]. eapply awr_ok_cons_stack;
      [reflexivity | exact Usp2 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
  (* the stretch 0x86c50 .. 0x86c60 writes nothing *)
  assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 24 <= a < spZ regs) ->
    aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) mem3 a).
  { eapply pjw_keep_frame; [intros; reflexivity | exact HFr |].
    intros a (r & Hr & Ha).
    lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change rs0 with rs1 in Hr end.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp2 in Ha; lia |]).
    destruct Hr. }
  assert (KLOW4 : forall a, 0 <= a < YM05.alloc_ceiling -> ~ (spZ regs - 24 <= a < spZ regs)) by (intros a Ha; lia).
  assert (KOFF4 : forall a, spZ regs - 56 <= a < spZ regs - 56 + 32 ->
    0 <= a < 2 ^ 64 /\ ~ (spZ regs - 24 <= a < spZ regs)) by (intros a Ha; split; lia).
  (* write_value's writer conjunct READ BY SHAPE: ret_ok, granted and the position, named by their statements *)
  destruct HRET3 as (ok1 & HRw). pjw_split HRw.
  pjw_pick @prhWriter_ret_ok HRET3. pjw_pick @prh_granted HGR1.
  match goal with H : ex ?P |- _ =>
    lazymatch P with context [PresetRoomPos.iface_room_pos] => destruct H as (rp_hist1 & HPOS1) end end.
  apply prhWriter_blk_of_ret_ok in HRET3; [| exact HGR1].
  destruct HRET3 as (ran1 & buf1 & Lam1 & peak1 & HOKS1 & HOUT1 & HLED1 & HBLK1).
  set (rp_i1 := (rp_i + length (prhWriter_evs ok1 (WriterApp.w0 cnt fail)
                   (WriterValue.wvpieces t (negb (pretty =? 0)%Z) 0)))%nat) in HPOS1.
  pose proof (ajxR_ar HJW3) as HAR3m.
  clear Ra0 Ra1 Ra2 Ra3 Rra Rsp Rgp Rtp Rs0.
  prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
  prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
  prreg HS (8%bv : bv 5) Rs0.
  assert (SPZ4 : spZ (ms_regs ms1) = spZ regs - 64)
    by (unfold spZ; rewrite Rsp; rewrite unsigned_lit_small by (rewrite Usp2; lia); rewrite Usp2; unfold spZ; lia).
  (* the PAddHi at slot 18 (.str.3): its atom is the read-only band's, A_OBJ 2; its addend is MEASURED on the
     listing of record by vm_compute (no hand-kept literal) *)
  assert (HNL : pjw_addhi_atom 18 = A_OBJ 2 /\
                pjw_addhi_off 18 = ltac:(let x := eval vm_compute in (pjw_addhi_off 18) in exact x))
    by (split; vm_compute; reflexivity).
  assert (HPUT0 : 0 <= STK_put)
    by (assert (HPF : pi_frame F_put = 112) by (vm_compute; reflexivity);
        unfold STK_put, zmaxl; cbn [fold_right]; rewrite HPF; lia).
  assert (HPUTSTK : STK_put + 64 <= STK)
    by (unfold STK, STK_pj_write, zmaxl; cbn [fold_right]; rewrite HPJF; lia).
  pose proof (ajxR_ar HJ3) as HAR4.
  assert (ARO4 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms1))).
  { eapply pjw_arodata_kept;
      [exact HJ3 | intros a; apply fp_spares_closed; intros (r & Hr & _); destruct Hr | exact HRO]. }
  assert (ESHI3 : ly_stk_hi ly3 = ly_stk_hi ly).
  { pose proof (ajxR_ly HJ3) as Hly.
    destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi & _). exact Eshi. }
  assert (RNL : getr (ms_regs ms1) 11 = w64 PJW_NL).
  { rewrite Ra1. unfold PJW_NL. rewrite (proj1 HNL), (proj2 HNL).
    cbn [sv_denot]. rewrite (HEI 243%nat ltac:(unfold A_TEXT, A_LIM; lia)).
    unfold w64, A_OBJ. reflexivity. }
  assert (HEW11 : ew EW 11 = Z_to_bv 64 pretty)
    by (rewrite (AG2 11%nat) by lia; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  rewrite branch_eq_U, (U_atom EW 11 pretty HEW11 ltac:(lia)), (U_lit EW 0 ltac:(lia)) in Hc.
  assert (Hpt : negb (pretty =? 0) = true) by (rewrite Hc; reflexivity).
  set (st1 := prhWriter_putN ok1 (WriterApp.w0 cnt fail) (WriterValue.wvpieces t (negb (pretty =? 0)) 0)) in *.
  (* put's run event (the kit's per-arm tput_specX): while the writer has not failed, write_value's outcomes were the
     all-granted run's (pjw_evs_ok_or_failed, S7a's prhW_putN_ok_or_failed), so the newline's grow is the next event
     of pj_write's list *)
  assert (HEVNL : prhWriter_grows st1 [10] = true -> WriterApp.w_cnt st1 <> WriterApp.w_fail st1 ->
    nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i1 = Some (prhWriter_ev st1 [10])).
  { intros Hg Hcf.
    assert (Hf0 : WriterApp.w_failed st1 = 0)
      by (unfold prhWriter_grows in Hg; apply andb_prop in Hg as (Hg' & _); apply Z.eqb_eq in Hg'; exact Hg').
    destruct (prhW_putN_ok_or_failed (WriterValue.wvpieces t (negb (pretty =? 0)) 0) ok1 (WriterApp.w0 cnt fail))
      as [Es | Ef]; [| exfalso; exact (Ef Hf0)].
    destruct (pjw_evs_ok_or_failed (WriterValue.wvpieces t (negb (pretty =? 0)) 0) ok1 (WriterApp.w0 cnt fail))
      as [Ee | Ef]; [| exfalso; exact (Ef Hf0)].
    pose proof HEVS as H0. unfold prhWriter_pjw_evs in H0. cbv zeta in H0. unfold WriterValue.wdpieces in H0.
    replace (if negb (pretty =? 0) then [[10]] else []) with [[10]] in H0 by (rewrite Hpt; reflexivity).
    rewrite prhWriter_evs_app0, <- !app_assoc in H0.
    apply prh_run_at_app_iff in H0 as (_ & H0).
    rewrite <- Es in H0. fold st1 in H0.
    rewrite (pjw_evs_cons_grow [] st1 [10] [] Hg) in H0. cbn [hd tl] in H0.
    rewrite (proj2 (Z.eqb_neq _ _) Hcf) in H0. cbn [orb negb] in H0.
    rewrite <- !app_assoc in H0.
    apply prh_run_at_app_iff in H0 as (H0 & _). apply prh_run_at_one in H0.
    change rp_i1 with (rp_i + length (prhWriter_evs ok1 (WriterApp.w0 cnt fail)
                                       (WriterValue.wvpieces t (negb (pretty =? 0)%Z) 0)))%nat.
    rewrite Ee. exact H0. }
  (* the writer's buffer, if it grew, is a block write_value made: live at the call, not a block of the entry *)
  assert (HBB : blocks_bytes S3 = blocks_bytes S + prhWriter_buf_bytes st1 /\
                (forall a, inFP (prhWriter_fp buf1 (WriterApp.w_cap st1)) a ->
                   in_tmp_block (ablocks B ly S) (ablocks B ly3 S3) a)).
  { unfold prhWriter_buf_bytes, prhWriter_fp.
    destruct HBLK1 as [(Ec & Eb & EL & Ep & Hperm) | (Hlt & l1 & l2 & b1 & b2 & Hcc & EL & Ep & Hperm)].
    - rewrite Ec. cbn [WriterApp.w0 WriterApp.w_cap]. rewrite Z.eqb_refl.
      split; [rewrite (pjw_bb_same ly S ly3 S3 Hperm); lia | intros a Ha; destruct (inFP_nil a Ha)].
    - cbn [WriterApp.w0 WriterApp.w_cap] in Hlt, Hcc.
      destruct Hcc as [(_ & -> & -> & -> & ->) | (Hne & _)]; [|exfalso; exact (Hne eq_refl)].
      cbn [app] in Hperm.
      assert (Hnz : WriterApp.w_cap st1 <> 0) by lia.
      rewrite (proj2 (Z.eqb_neq (WriterApp.w_cap st1) 0) Hnz).
      split.
      + rewrite (pjw_bb_grow ly S ly3 S3 (buf1 - cf_head, WriterApp.w_cap st1 + cf_head) Hperm). cbn [snd]. lia.
      + intros a Ha. apply inFP_ablocks_fp_inv in Ha. destruct Ha as (p0 & n0 & [Hq | []] & Hr0).
        injection Hq as <- <-. exists (buf1 - cf_head), (WriterApp.w_cap st1 + cf_head). split.
        * eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity].
        * split; [| exact Hr0].
          pose proof cf_head_nonneg.
          assert (Hrq : 0 < req_size (WriterApp.w_cap st1 + cf_head))
            by (unfold req_size; destruct (Z.eqb_spec (WriterApp.w_cap st1 + cf_head) 0); lia).
          exact (pjw_fresh_block ly3 S3 Hp3 W3 mem3 md3 (buf1 - cf_head, WriterApp.w_cap st1 + cf_head)
                   (ablocks B ly S) HAR3m Hperm Hrq). }
  destruct HBB as [HBBe HTMP].
  (* put's consumer window (the batch kit's tput_specX :421): the newline's events start where write_value's granted run ended
     (pjw_cons_put); its live room at each event from pj_write's entry budget (pjw_blk_live, pjw_live_put) *)
  assert (HCPUT : prh_cons_from rp_sm rp_x rp_os rp_i1 (length (prhWriter_evs [] st1 [[10]]))).
  { pose proof HCONS as H0. unfold WriterValue.wdpieces in H0.
    replace (if negb (pretty =? 0) then [[10]] else []) with [[10]] in H0 by (rewrite Hpt; reflexivity).
    pose proof HLED as HLB. apply prh_ledger_bounds in HLB. destruct HLB as (_ & _ & HCB & HFB & _).
    exact (pjw_cons_put _ _ _ _ _ _ _ _ ok1 HCB HFB HGR1 H0). }
  assert (HLVPUT : prh_live_evs S3 (prhWriter_evs [] st1 [[10]])).
  { destruct (pjw_blk_live _ _ _ _ _ _ _ _ _ _ _ _ HBLK1) as (HBB3 & HIN3).
    unfold st1 in HBB3, HIN3 |- *. rewrite Hpt in HBB3, HIN3, HLIVE, HWMAX |- *.
    exact (pjw_live_put S S3 ok1 cnt fail t cf_head_nonneg HLIVE HWMAX HBB3 HIN3). }
  pmkst HS.
  (* put's primed text concludes SRr' SEGS RZ_cf (post fpostWmR at wle'): the call rule over the walk's relation *)
  eapply (SRrG_bind SEGS (wle' SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
  { eapply (aj_call_xWR (fx := fx3) SEGS B (@prh_pst prh_img_A) ARx LAWS segs_low (wle' SEGS RZ_cf)
      (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) W3 _ _ _ STK (spZ regs) [] ly S Hp W
      mem md []
      ly3 S3 Hp3 _ _ STK_put 64 (prhWriter_cfp (spZ regs - 56) buf1 (WriterApp.w_cap st1)) (-64) _ [] _ HJ3).
    all: first
       [ exact Rra
       | rewrite SPZ4; lia
       | reflexivity
       | lia
       | rewrite Rgp, (AG2 3%nat) by lia; exact Hgp
       | rewrite Rtp, (AG2 4%nat) by lia; exact Htp
       | apply ret_ok_codeptr_v; [lia | vm_compute; reflexivity]
       | rewrite unsigned_lit_small by (pose proof (@pa_B_ok _ _ PA); lia); pose proof (@pa_B_ok _ _ PA); lia
       | apply achain_low; unfold s0Z; rewrite Rs0, (AG2 11%nat) by lia;
         rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), H11; unfold w64;
         rewrite unsigned_lit_small by lia; lia
       | (* the footprint: the struct is pj_write's own window, the buffer is a block write_value made *)
         let a := fresh "a" in let Ha := fresh "Ha" in
         intros a Ha; unfold prhWriter_cfp in Ha; cbn [app] in Ha; apply inFP_cons in Ha;
         destruct Ha as [Hs | Hb]; [right; right; right; split; lia | right; left; exact (HTMP a Hb)]
       | (* the callee: the kit's put text (its one use), at write_value's return float state fx3 *)
         let HPRE4 := fresh "HPRE4" in let HWIN4 := fresh "HWIN4" in intros HPRE4 HWIN4;
         eapply (HPUT fx3 rp_sm rp_x rp_os rp_i1 rp_H0 rp_hist1 most own ly3 S3 Hp3 W3 _ _ _ []
                   (spZ regs - 56) PJW_NL 1 64 buf1 st1 [10] Lam1 peak1 ran1);
         first
         [ lazymatch goal with
           | |- fpre _ _ _ _ _ _ _ _ _ _ _ =>
              split; [exact HPRE4 | split; [exact ARO4 | split; [rewrite SPZ4, ESHI3; lia
                                                           | split; [unfold raZ; rewrite Rra;
                                                                     rewrite unsigned_lit_small
                                                                       by (pose proof (@pa_B_ok _ _ PA); lia);
                                                                     pjw_ret_ceil_tac
                                                                    | (* write_value returns frm 0 *)
                                                                      exact HFZ3]]]]
           | |- getr _ _ = w64 PJW_NL => exact RNL
           | |- src_rd _ _ PJW_NL _ => exact (proj1 (HLIT ly3 S3 Hp3 W3 _ _ HAR4 ARO4))
           | |- prhWriter_src_home _ _ _ _ _ _ _ _ =>
               (* the source's home: the read-only band; it misses the buffer (an image byte is in no block) *)
                 split;
                 [ left; destruct (proj2 (HLIT ly3 S3 Hp3 W3 _ _ HAR4 ARO4)) as [(b0 & m0 & Hb0 & _) | Hzs];
                   [destruct Hb0 | right; exact Hzs]
                 | destruct (Z.eqb_spec (WriterApp.w_cap st1) 0) as [Hc0 | Hcn]; [left; exact Hc0|];
                   right; pose proof HLED1 as (_ & _ & HHB1 & _); rewrite Forall_forall in HHB1;
                   destruct HOUT1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz0 & _) | (_ & Hin1 & _)]);
                   [exfalso; exact (Hcn Hz0)|];
                   destruct (HHB1 _ Hin1) as (Hk1 & Hab1 & _); cbn [fst snd] in Hk1, Hab1;
                   pose proof cf_head_nonneg;
                   destruct (alx_blocks SEGS B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 _ _ HAR3m Hab1) as (_ & Hb4 & Hbc & _);
                   assert (Hrq1 : WriterApp.w_cap st1 + cf_head <= req_size (WriterApp.w_cap st1 + cf_head))
                     by (unfold req_size; destruct (Z.eqb_spec (WriterApp.w_cap st1 + cf_head) 0); lia);
                   destruct (Z_le_gt_dec (PJW_NL + 1) buf1) as [Hle | Hgt]; [left; lia|]; right;
                   destruct (Z_le_gt_dec (buf1 + WriterApp.w_cap st1) PJW_NL) as [Hle2 | Hgt2]; [lia|];
                   exfalso;
                   refine (proj2 (alx_client_img SEGS B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 PJW_NL HAR3m _) HIMGNL);
                   left; exists (buf1 - cf_head), (WriterApp.w_cap st1 + cf_head); split; [exact Hab1 | lia] ]
           | |- _ <= prhWriter_WMAX =>
               (* the text so far plus the newline is below WMAX *)
                 pose proof (prhWriter_putN_len_le ok1 (WriterApp.w0 cnt fail)
                   (WriterValue.wvpieces t (negb (pretty =? 0)) 0)) as HL1;
                 change (length (WriterApp.w_text (WriterApp.w0 cnt fail))) with 0%nat in HL1; fold st1 in HL1;
                 unfold WriterValue.wdoc, WriterValue.wdpieces in HWMAX;
                 replace (if negb (pretty =? 0) then [[10]] else []) with [[10]] in HWMAX
                   by (rewrite Hpt; reflexivity);
                 rewrite concat_app, length_app in HWMAX; cbn [concat length app] in HWMAX; lia
           end
         | exact HROOM3 | exact HPOS1 | exact HOS | exact HEVNL | exact HUNIV | exact HWIN4 | exact HMAX2
         | reflexivity
         | exact HCPUT | exact HLVPUT
         | rewrite Ra0, Usp2; unfold w64; f_equal; lia
         | exact Ra2
         | rewrite SPZ4; lia
         | lia
         | eapply (pjw_out_keep ly3 S3 Hp3 W3 W3 mem3 _ md3 Lam1 peak1 _ _ ran1 most own);
           [exact HAR3m | exact HLED1 | exact HOUT1 | exact KEEP4 | exact KLOW4 | exact KOFF4]
         | eapply pjw_ledger_keep; [exact HAR3m | exact HLED1 | exact KEEP4 |
             intros a Ha; cbv beta; unfold pjw_wr; lia]
         ]
       ]. }
  cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & Hp5 & regs5 & mem5 & md5 & k5 & -> & HJ5 & HJW5 & HKW5 & HP5 & HQ5).
  (* The kit's per-arm post (the position keyed on whether the newline grew and on the failed word it left), READ BY
     SHAPE: each conjunct this walk uses is named by its statement *)
  unfold fQmn in HQ5. cbv beta in HQ5. pjw_split HQ5.
  lazymatch goal with H : room_live_cf S5 |- _ => rename H into HROOM5 end.
  lazymatch goal with H : prhWriter_grows st1 [10] = false -> _ |- _ => rename H into HPNG5 end.
  lazymatch goal with H : prhWriter_grows st1 [10] = true -> _ |- _ => rename H into HPG5 end.
  match goal with H : ex ?P |- _ => lazymatch P with context [prhWriter_ret_ok] => rename H into HRET5 end end.
  lazymatch goal with H : YAkMemnorm.memnorm _ _ -> YAkMemnorm.memnorm _ mem5 |- _ => rename H into HMN5 end.
  (* the memory invariant across put (its m-form keep, srr_inv_call) *)
  pose proof (PCALL _ _ HMN5 HPM) as HPM5. clear HPM HMN5. rename HPM5 into HPM.
  pose proof (ajxR_ar HJ5) as HAR5. pose proof (ajxR_pres HJ5) as HPRES5.
  (* re-seat after put into the atoms 65.. (the band the pretty = 0 arm re-seats into at the join): the saved
     registers are outside put's footprint (the struct, and the buffer block, which lies below the ceiling) *)
  jafter_call_keep_pi HS 65%nat regs5 (mrestrict (w_H W5) mem5) HP5 (0%nat :: @nil nat) HS5.
  match type of HS5 with ?Q -> _ =>
    assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
      split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp2; intros a Ha;
      [ apply (mbyte_of_aview SEGS); apply HKW5;
        [ lia
        | let Hin := fresh "Hin" in let Hs := fresh "Hs" in let Hb := fresh "Hb" in
          let b0 := fresh "b0" in let n0 := fresh "n0" in let Hbin := fresh "Hbin" in let Hbr := fresh "Hbr" in
          let Hbc := fresh "Hbc" in
          intros Hin; unfold prhWriter_cfp in Hin; apply inFP_cons in Hin;
          destruct Hin as [Hs | Hb]; [lia |];
          destruct (HTMP a Hb) as (b0 & n0 & Hbin & _ & Hbr);
          destruct (alx_blocks SEGS B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 _ _ HAR3m Hbin) as (_ & _ & Hbc & _);
          lia ]
      | intros _; apply (apresent_writable SEGS); apply HPRES5; lia ]
    | specialize (HS5 HQ); clear HQ ] end.
  clear HS. rewrite <- (restrict_mkst_fx (fx := fx3)) in HS5. rename HS5 into HS.
  apply (pjw_drop_cond fx3) in HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
    replace s with pjw_ssT in HS by (vm_compute; reflexivity) end.
  (* the two runs composed: the value's pieces, then the newline (S7a's prhWriter_ret_app) *)
  assert (HRETJ : exists okJ, prhWriter_ret_ok B okJ ly S Lam peak ran most own (spZ regs - 56) 0 (WriterApp.w0 cnt fail)
                    (WriterValue.wdpieces t (negb (pretty =? 0))) ly5 S5 Hp5 W5 regs5 mem5 md5 /\
                  prh_granted okJ cnt fail
                    (prhWriter_k okJ (WriterApp.w0 cnt fail) (WriterValue.wdpieces t (negb (pretty =? 0)))) /\
                  exists rp_hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
                    (rp_i + length (prhWriter_evs okJ (WriterApp.w0 cnt fail)
                                      (WriterValue.wdpieces t (negb (pretty =? 0)%Z))))%nat rp_H0 rp_hist' S5).
  { replace (WriterValue.wdpieces t (negb (pretty =? 0)))
      with (WriterValue.wvpieces t (negb (pretty =? 0)) 0 ++ [[10]])
      by (unfold WriterValue.wdpieces; rewrite Hpt; reflexivity).
    destruct HRET5 as (ok2 & HRw5). pjw_split HRw5.
    pjw_pick @prhWriter_ret_ok HR5. pjw_pick @prh_granted HG2.
    apply prhWriter_blk_of_ret_ok in HR5; [| exact HG2].
    destruct HR5 as (ran2 & buf2 & Lam2 & peak2 & Hok2 & Hout2 & Hled2 & Hblk2).
    pose proof HLED1 as HB1. apply prh_ledger_bounds in HB1. destruct HB1 as (_ & _ & Hr1 & Hf1 & _).
    pose proof (pjw_led_nodup ly3 S3 Hp3 W3 mem3 Lam1 peak1 _ _ ran1 _ _ HLED1) as Hnd1.
    destruct (prhW_app_model (WriterApp.w0 cnt fail) (WriterValue.wvpieces t (negb (pretty =? 0)) 0) [[10]]
                ok1 ok2 most ran ran1 ran2
                ltac:(cbn [WriterApp.w0 WriterApp.w_cnt];
                      pose proof (pjw_led_cnt ly S Hp W mem Lam peak cnt fail ran most own HLED); lia)
                Hr1 Hf1 HOKS1 Hok2) as (okJ & Hput & HoksJ & HGJ).
    exists okJ. split; [| split; [exact (HGJ HGR1 HG2) |]].
    - eapply prhWriter_ret_ok_of_blk;
        [ exact HoksJ | rewrite Hput; exact Hout2 | rewrite Hput; exact Hled2
        | rewrite Hput;
          eapply prhW_blk_trans;
            [ exact Hnd1
            | exact (prhW_cap_after (WriterValue.wvpieces t (negb (pretty =? 0)) 0) ok1 (WriterApp.w0 cnt fail))
            | exact HBLK1 | exact Hblk2 ]
        | exact (HGJ HGR1 HG2) ].
    - (* THE EXACT ADVANCE after the newline: write_value's events plus one if it grew and left the writer
         not failed (pjw_len_one), which is the arm put's per-arm post gives *)
      pose proof (pjw_len_one (WriterApp.w0 cnt fail) (WriterValue.wvpieces t (negb (pretty =? 0)) 0) [10]
                    okJ ok1 ok2 eq_refl eq_refl Hput) as LEN.
      fold st1 in LEN. rewrite LEN.
      pose proof Hout2 as (_ & _ & _ & _ & _ & _ & Hvf2 & Hf012 & _).
      assert (EQS : forall X : nat, (rp_i + (X + 1))%nat = Datatypes.S (rp_i + X)) by (intros; lia).
      destruct (prhWriter_grows st1 [10]) eqn:Hg.
      + destruct (Z.eq_dec (WriterApp.w_failed (prhWriter_putN ok2 st1 [[10]])) 0) as [Hz | Hnz].
        * pose proof (HPG5 eq_refl _ Hvf2) as HPGa. pjw_split HPGa.
          lazymatch goal with H : _ = 0 -> _ |- _ => destruct (H Hz) as (h2 & Hp2) end.
          exists h2.
          rewrite Hz. cbn [Z.eqb andb]. rewrite EQS. exact Hp2.
        * (* put's refused arm is keyed on f' = 1: prhWriter_out's failed word is 0 or 1 *)
          assert (Hf1' : WriterApp.w_failed (prhWriter_putN ok2 st1 [[10]]) = 1)
            by (destruct Hf012 as [Ef0 | Ef1]; [exfalso; exact (Hnz Ef0) | exact Ef1]).
          pose proof (HPG5 eq_refl _ Hvf2) as HPGa. pjw_split HPGa.
          lazymatch goal with H : _ = 1 -> _ |- _ => destruct (H Hf1') as (h2 & Hp2) end.
          exists h2.
          rewrite (proj2 (Z.eqb_neq _ _) Hnz). cbn [andb]. rewrite Nat.add_0_r. exact Hp2.
      + pose proof (HPNG5 eq_refl) as Hp2. exists rp_hist1. cbn [andb]. rewrite Nat.add_0_r. exact Hp2. }
  pose proof HEI as HEIe4. clear HEI.
  set (EJ := havoc EW 65 (map (getr regs5) CLOB)) in HS.
  assert (HEI : img_env VAL A_LIM EJ)
    by (unfold EJ; apply img_env_havoc; [exact HEIe4 | vm_compute; lia]).
  assert (AGJ : forall m, (m < 33)%nat -> ew EJ m = ew (Ereg regs []) m)
    by (intros m Hm; unfold EJ; rewrite ew_havoc_old by lia; apply AG2; lia).
  assert (HAEJ : env_agree 32 (Ereg regs []) EJ)
    by (split; [intros m Hm; first [apply AGJ | symmetry; apply AGJ]; lia | reflexivity]).
  assert (SHOKJ : sh_ok SEGS PJW_Bx [] EJ (mrestrict (w_H W5) mem5)) by constructor.
  eapply (pjw_tail fx3);
    first [ exact HFZ3 | exact HFK3 | exact HSTK | exact HFFSTK | exact HPRE | exact HUNIV | exact H11 | exact HPR
          | exact HLED | exact HNODE | exact HLOC | exact HDL | exact HS | exact SHOKJ | exact HEI | exact AGJ
          | exact HAEJ | exact HJ5 | exact HPM | exact HROOM5 | exact HOS | exact HEVS | exact HRETJ
          | exact ARGCNT ].
Qed.
End p.

(* ---- THE CONTRACT: the cut's tpj_write_specX (lib/A/PRH_FnWriter.v blob d89d3c67b78c, cut 7cdbb61b5fa0,
   :773-850) with the ONE ruled ARGUMENT of pj_write's single fuzz_free call site (a Theorem Labs lane 08:06Z):
   tfuzz_free_specX (PRH_FnAlloc.v blob 4d8aeba047e5, :329) asks `p <> 0 -> YGcfRoomLive.ccnt24 S <=
   PresetLiveBounds.L24 + PresetLiveBounds.DRV` at its entry and nothing in pj_write's own text bounds it;
   a Theorem Labs lane's counts_of_room_pos_rl / counts_of_room_pos_ok derive it from the model-run position, which this walk
   has at that state (iface_room_pos rp_* S3). Its `admits` premise (:340) has NO gap at this site (a fixed trace,
   YG01.admits_fix in pjw_tail). The batch kit keys the run's strtod model (rp_sm := ReaderRes.jr_strtod, :779); the walk is
   generic in rp_sm and is instantiated there. Shape as WalkS5a's grow_holds_lc. The memory invariant is
   instantiated HERE, once: Pm := fun m => memnorm segs mem -> memnorm segs m. The post is the batch kit's float form fpostFm at
   the ENTRY float state (the Section's fx), under the kit's primed SRr' SEGS RZ_cf. The text's premises are taken BY
   SHAPE: each premise of pjw_walk is discharged by the hypothesis of its type, so a premise the text inserts (the
   hull drafts' `length rp_os <= 4`) does not shift a positional intro list. ---- *)
Theorem pjw_holds_lc : forall n,
  (forall rp_sm rp_x rp_os rp_H0 ly S Hp (W : world SEGS) regs mem md,
     pjw_ARGCNT (STK_pj_write n) rp_sm rp_x rp_os rp_H0 ly S Hp W regs mem md) ->
  tpj_write_specX (PI := prh_img_A) (PA := PA) B ARx SK CTX0 n.
Proof.
intros n HARG rp_x rp_os rp_i rp_H0 rp_hist most own.
intros ly S Hp W regs mem md ch v pretty t D Lam peak cnt fail ran.
intros.
eapply (SRr'_mono SEGS RZ_cf).
- eapply (pjw_walk (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
            (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))
            (srr_inv_call_imp SEGS mem)
            n ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch v pretty t D Lam
            peak cnt fail ran);
    first [ assumption | apply HARG | let HM := fresh "HM" in intros HM; exact HM ].
- let Wq := fresh "Wq" in let cq := fresh "cq" in let Hle := fresh "Hle" in
  let HQ := fresh "HQ" in let HM := fresh "HM" in
  intros Wq cq Hle (HQ & HM); exact (pjw_post_m _ _ _ _ _ _ _ _ _ _ _ _ HQ HM).
Qed.

Print Assumptions pjw_holds_lc.
Set Printing All.
Check @pjw_holds_lc.
Unset Printing All.

End h.
End f.
End d.
