(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 665 of its 733 lines of code are new or changed and 4985 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B10b_c.v, with its module names changed; 471 of its 561 lines of code are new or changed and 643 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): stretches SB9_7,
   SB9_8 and SB9_9 of segment B9 of reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B9_d.v): the strcasecmp chain
   J6 0x88588 -> ROLE 0x88630 or J7, J7 0x8859c -> MODEL 0x886d4 or J8, J8 0x885b0 -> IGN 0x887e0 or J9.
   A B9 sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: stretches SB9_7, SB9_8, SB9_9 of segment
   B9).
    ADAPTED from commit 217af09c8626 lib/A/Prog/pf_a9_s2.v (A9's plain runs to an art call and
   the a9_core transport b2_core_move / b2_vis / b2_keep_inbuf, here over B9's b9_core) and lib/A/Prog/pf_a9_d.v
   (A9's strcasecmp dispatch 0x88150 .. 0x8818c), re-derived on image B's code with the image-B forms of
   lib/B/Prog/pf_seg_B9_s1.v (the B9 segment lane: the art call at s1) and lib/B/Prog/pf_seg_B5_r2.v (the B5 segment lane: a
   branch split by psrr_branch_pi and the taken side run on by paj_run_to_sh).

   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), one compare per stretch, k = 0, 1, 2:
     JC k   beqz a0 -> EXIT k              (a0 = strcasecmp(key, lit k), INV_JC's iff)
            auipc a0; addi a1,a0,off       a1 = lit (k + 1): listing objects 44 / 45 / 46 (PHi / PAddHi pair)
            mv a0,s7                       a0 = kp, the key in buf
            jal strcasecmp                 the trampoline SS___interceptor_trampoline_strcasecmp (0x43aa8)
     k = 0: 0x88588 beqz -> ROLE 0x88630; 0x8858c auipc; 0x88590 addi a1 = 0x21800 "model";  0x88594 mv; 0x88598 jal
     k = 1: 0x8859c beqz -> MODEL 0x886d4; 0x885a0 auipc; 0x885a4 addi a1 = 0x218e0 "ignore"; 0x885a8 mv; 0x885ac jal
     k = 2: 0x885b0 beqz -> IGN 0x887e0;  0x885b4 auipc; 0x885b8 addi a1 = 0x21960 "knock";  0x885bc mv; 0x885c0 jal
   15 instructions (5 per stretch), no inline check, no UBSan trap, no store.

   THE PROOF of each stretch: a seed at JC k (every register its own atom, no region, no fact; s7_seed), the branch
   split by psrr_branch_pi (the executor cannot decide `beqz a0` on a0's atom); s7_beqz turns each side's condition
   into a0 = 0 / a0 <> 0, so INV_JC's iff gives the k-th compare's answer.
   - taken: one plain run to EXIT k (paj_run_to_sh), which writes nothing (kept_of_frame) and keeps every callee-saved
     register (regs_kept_of_st_ok_pi); s7_exit rebuilds pf_pieces.v's INV_KV there (pf_kv from the '=' index ei and
     the key / value strings kept in buf, slot 0x70, PF_RL ++ PF_RM), and H_ROLE / H_MODEL / H_IGN closes it with the
     strcasecmp facts (= 0 for this literal from the branch, <> 0 for the earlier ones from INV_JC).
   - not taken: one plain run to the call (paj_run_shc: a0 = kp from s7's atom, a1 = the next literal's object atom,
     s7_atom_*, from OBJ), then s7_call: the call by PaArt.aj_art_at with RtSeg.astrcasecmp_realizes (window
     2 * ESTACK at s1; premises from pf_seg_B9_c.v b9_strcasecmp_pre at the call's state), and INV_JC (k + 1) at the
     return state by s7_next: b9_core by pf_seg_B9_k.v b9_move0 (s7_core_move: the entry writes only its window below
     s1, every visible byte stays visible by the journal's presence clause, s7_vis), the key and value kept in buf
     (s7_keep_inbuf), slot 0x70 kept, the registers by aregs_preserved, the earlier compares <> 0 (this one from the
     branch), and the answer bridged into SegModel.strcasecmp by pf_seg_B9_f.v b9_strcasecmp_iff (s7_iff).

   POSITIONAL NAMES checked against image B's own table (lib/B/Prog/SegAddr.v seg_objs, by address): listing objects
   44, 45, 46 are 0x21800 (.str.16 S_model), 0x218e0 (.str.21 S_ignore), 0x21960 (.str.23 S_knock) on image B
   (atoms A_OBJ 44 = 285, 286, 287); s7_atom_* check each by computation against SegInstB's seg_litA_rc.

   SECTION HYPOTHESES (the brief's texts): ASTRCASECMP (the strcasecmp carrier at the listing's trampoline), OBJ (the
   listing's object atoms: the three literal pointers), TL (PALib: the errno cell, which the art step needs). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B9_d pf_seg_B9_f
  pf_seg_B9_k pf_seg_B9_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools (pf_seg_B9_s1.v's b9s1_bvr / b9s1_m16 / b9s1_aview_mod) ---------- *)
Lemma s7_bvr : forall rr (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma s7_m16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. pose proof (Z.div_mod a 32 ltac:(lia)) as Da. pose proof (Z.div_mod b 16 ltac:(lia)) as Db.
rewrite Ha in Da. rewrite Hb in Db.
replace (a - b) with ((2 * (a / 32) - b / 16) * 16) by lia. apply Z_mod_mult.
Qed.
(* a reader at a reads the byte at a mod 2 ^ 64 (mbyte goes through Z_to_bv 64) *)
Lemma s7_aview_mod : forall segs H m a, aview segs H m a = aview segs H m (a mod 2 ^ 64).
Proof.
intros segs H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Zmod_mod. reflexivity.
Qed.
Ltac s7_in := cbn [In app]; repeat first [left; reflexivity | right].

(* the registers no instruction of the three stretches writes (callee-saved ones and gp / tp / sp) *)
Definition s7_kept : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
(* a register list carried to a register file that agrees on the registers ks it names (pf_a9_s2.v b2_rg_kept) *)
Lemma s7_rg_kept : forall (r1 r2 : bvmap 5 word) (ks : list Z) L,
  (forall r, In r (map (Z_to_bv 5) ks) -> getr r2 r = getr r1 r) ->
  Forall (fun rv => In (fst rv) ks) L -> pf_rg r1 L -> pf_rg r2 L.
Proof.
intros r1 r2 ks L HK HL H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HK (Z_to_bv 5 (fst rv)) (in_map _ _ _ (HL rv Hin))). exact (H rv Hin).
Qed.

(* `beqz a0` (beq a0, zero) on a0's atom: taken exactly when a0 = 0 *)
Lemma s7_beqz : forall E (w : word) b, ew E 10 = w ->
  branch_taken BC_EQ (sv_denot E (SOff 10 0)) (sv_denot E (SLit 0)) = b -> (w = w64 0 <-> b = true).
Proof.
intros E w b Hw Hc.
pose proof (bv_unsigned_in_range 64 w) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
assert (Ua : U E (SOff 10 0) = bv_unsigned w)
  by (apply U_atom; [rewrite Hw; symmetry; apply Z_to_bv_bv_unsigned | lia]).
assert (Ul : U E (SLit 0) = 0) by (apply U_lit; lia).
rewrite branch_eq_U, Ua, Ul in Hc. subst b.
split; [intros ->; reflexivity | intros H; apply Z.eqb_eq in H; apply bv_eq; rewrite H; reflexivity].
Qed.

(* the four literals the chain compares with: NUL-free, and their bytes read back as themselves *)
Lemma s7_nin0 : forall l, existsb (Z.eqb 0) l = false -> ~ In 0 l.
Proof.
intros l H Hin.
assert (E : existsb (Z.eqb 0) l = true) by (apply existsb_exists; exists 0; split; [exact Hin | apply Z.eqb_refl]).
rewrite H in E. discriminate E.
Qed.
Lemma s7_lit_ok : forall w, In w [S_role; S_model; S_ignore; S_knock] ->
  ~ In 0 w /\ seg_spec.zs (seg_spec.zb w) = w.
Proof.
intros w Hw. destruct Hw as [<- | [<- | [<- | [<- | []]]]];
  (split; [apply s7_nin0; vm_compute; reflexivity | vm_compute; reflexivity]).
Qed.
(* the return pcs J7, J8, J9 (and J6) are code offsets a return address can hold *)
Lemma s7_ret_ok : forall k, (k < 4)%nat -> 0 <= B9_JC k < 2 ^ 40 /\ B9_JC k mod 2 = 0.
Proof.
intros k Hk. destruct k as [|[|[|[|k]]]]; [| | | | lia];
  unfold B9_JC, B9_J6, B9_J7, B9_J8, B9_J9, AF_reac_segconf_parse_file; cbn [nth];
  (split; [lia | reflexivity]).
Qed.
(* the interceptor's answer, read as SegModel's (pf_seg_B9_f.v b9_strcasecmp_iff) *)
Lemma s7_iff : forall (rr : bvmap 5 word) key w, ~ In 0 key -> ~ In 0 w ->
  seg_spec.zs (seg_spec.zb key) = key -> seg_spec.zs (seg_spec.zb w) = w ->
  (getr rr 10 = w64 0 <->
     map RtSeg.lc (seg_spec.zs (seg_spec.zb key) ++ [0]) = map RtSeg.lc (seg_spec.zs (seg_spec.zb w) ++ [0])) ->
  (getr rr 10 = w64 0 <-> strcasecmp key w = 0).
Proof.
intros rr key w Hk Hw Ek Ew H. rewrite Ek, Ew in H. rewrite <- (b9_strcasecmp_iff key w Hk Hw). exact H.
Qed.

(* the seed at a cut pc: every register its own atom, no region, no fact *)
Definition s7_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis ASTRCASECMP : forall fx0 : YK11.FPState, @RtSeg.astrcasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcasecmp).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis TL : PALib B.

(* the literal pointers the auipc / addi pairs form: listing objects 44, 45, 46 (lib/B/Prog/SegAddr.v seg_objs) *)
Lemma s7_atom_model : forall E, img_env VAL A_LIM E -> ew E 285%nat = w64 (seg_litA_rc S_model).
Proof.
intros E HE. rewrite (img_env_atomP E 285%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 285%nat with (A_OBJ 44). rewrite (OBJ 44%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.
Lemma s7_atom_ignore : forall E, img_env VAL A_LIM E -> ew E 286%nat = w64 (seg_litA_rc S_ignore).
Proof.
intros E HE. rewrite (img_env_atomP E 286%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 286%nat with (A_OBJ 45). rewrite (OBJ 45%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.
Lemma s7_atom_knock : forall E, img_env VAL A_LIM E -> ew E 287%nat = w64 (seg_litA_rc S_knock).
Proof.
intros E HE. rewrite (img_env_atomP E 287%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 287%nat with (A_OBJ 46). rewrite (OBJ 46%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

(* the register lists of a JC cut (pf_fi's, B9_R, s7 = kp): callee-saved, and among s7_kept *)
Lemma s7_cs_all : forall x kp, Forall (fun rv => acallee_saved (fst rv)) (b9_FI B (y_v x) ++ B9_R x ++ [(23, kp)]).
Proof.
intros x kp. unfold b9_FI, B9_R, PF_RL, PF_RM. cbn [app].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
Qed.
Lemma s7_ks_all : forall x kp, Forall (fun rv => In (fst rv) s7_kept) (b9_FI B (y_v x) ++ B9_R x ++ [(23, kp)]).
Proof.
intros x kp. unfold b9_FI, B9_R, PF_RL, PF_RM, s7_kept. cbn [app].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; s7_in.
Qed.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.
Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).
Lemma s7_seed : forall pc (Wc : world SEGS) (rX : bvmap 5 word) memc,
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) (s7_ss pc)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros pc Wc rX memc. rewrite restrict_mkst_fx. unfold s7_ss. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | split; [exact I | split; exact I]].
Qed.


(* a plain run's write obligation when the seed has no region *)
Ltac s7_awr :=
  first [ apply awr_ok_nil
        | cbn; apply awr_ok_nil
        | let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in
          intros a (r & Hr & _); vm_compute in Hr; destruct Hr ].

(* ======================= the transport of a JC cut across a step ======================= *)
(* the reader after a step that keeps every byte off [lo, s1), whose new journal keeps parse_file's window present:
   every mapped byte stays mapped (pf_a9_s2.v b2_vis with no written set) *)
Lemma s7_vis : forall v pos lyc Sc' (Wc : world SEGS) memc memc' mdc' lo,
  b9_G v pos ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc' Wc memc' mdc' 0 ->
  pf_sp0 v - STK_reac_segconf_parse_file <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < pf_s1 v) -> rdW Wc memc' a = rdW Wc memc a) ->
  forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None.
Proof.
intros v pos lyc Sc' Wc memc memc' mdc' lo G HJ Hlo HK a0 Hv0.
pose proof G as (G1 & G2 & G3 & G4 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
rewrite s7_aview_mod in Hv0 |- *.
pose proof (Z.mod_pos_bound a0 (2 ^ 64) ltac:(lia)) as Ha.
remember (a0 mod 2 ^ 64) as a eqn:Ea. clear Ea.
destruct (Z_lt_le_dec a lo) as [H1 | H1]; [|destruct (Z_lt_le_dec a (pf_s1 v)) as [H2 | H2]].
- rewrite HK; [exact Hv0 | exact Ha | lia].
- apply (aview_some_of_apresent SEGS). apply Hpres. lia.
- rewrite HK; [exact Hv0 | exact Ha | lia].
Qed.

(* b9_core after such a step (pf_seg_B9_k.v b9_move0 for pf_base, b9_keep_fsh, b9_keep_st) *)
Lemma s7_core_move : forall n x lyc Sc Wc rX memc mdc rX' memc' mdc' lo,
  b9_core B n x lyc Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memc' mdc' 0 ->
  pf_sp0 (y_v x) - STK_reac_segconf_parse_file <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < pf_s1 (y_v x)) -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_rg rX' (b9_FI B (y_v x)) ->
  b9_core B n x lyc Sc Wc rX' memc' mdc' /\ (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None).
Proof.
intros n x lyc Sc Wc rX memc mdc rX' memc' mdc' lo HC HJ' Hlo HK HRG.
destruct HC as (HB & HM & HS & HL & HD0 & HDL).
pose proof (b9_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
pose proof HB as (_ & _ & HOBJ & _ & HFSH).
assert (HC5 : sa_heap B lyc Sc (p_c (y_v x)) seg_spec.SEG_C_SIZE)
  by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None)
  by exact (s7_vis (y_v x) (y_pos x) lyc Sc Wc memc memc' mdc' lo G HJ' Hlo HK).
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx (y_v x) (y_pos x) true a -> rdW Wc memc' a = rdW Wc memc a).
{ intros a Ha Hw. apply HK; [exact Ha|]. intros Hn. apply Hw. left. lia. }
assert (HB' : pf_base B (y_v x) (y_pos x) lyc Sc Wc rX' memc' mdc' PF_SC_LINE).
{ eapply (b9_move0 B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc rX' memc' mdc' PF_SC_LINE HB HJ');
    [exists (st_fs Sc); destruct Sc; reflexivity | apply Permutation_refl | exact KW | exact KV | exact HRG |].
  eapply b9_keep_fsh; [exact G | exact KW | exact HFSH]. }
split; [|exact KV].
split; [exact HB'|]. split; [exact HM|].
split; [eapply b9_keep_st; eassumption|].
split; [exact HL|]. split; [exact HD0 | exact HDL].
Qed.

(* a C string of buf after such a step (pf_a9_s2.v b2_keep_inbuf with no written set): buf lies below the
   allocator's ceiling, under every window below s1 *)
Lemma s7_keep_inbuf : forall x (Wc : world SEGS) memc memc' lo q s,
  b9_G (y_v x) (y_pos x) ->
  pf_sp0 (y_v x) - STK_reac_segconf_parse_file <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < pf_s1 (y_v x)) -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  b9_inbuf (rdW Wc memc) x q s -> b9_inbuf (rdW Wc memc') x q s.
Proof.
intros x Wc memc memc' lo q s G Hlo HK HV (((Hz & Hn) & Ht) & Hb1 & Hb2).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
unfold b9_buf, PF_O_BUF in Hb1, Hb2.
split; [|split; [exact Hb1 | exact Hb2]].
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite HK; [exact (Hz i Hi) | lia | lia].
- intros y Hy. apply HV. exact (Ht y Hy).
Qed.

(* ======================= the two ends of a stretch ======================= *)
(* the exit EXIT k after a run that kept every byte and every register of s7_kept: pf_pieces.v's INV_KV *)
Lemma s7_exit : forall n x ei kp vp gi k lyc Sc Wc rX memc mdc rX' memc' mdc',
  INV_JC B n x ei kp vp gi k lyc Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall r, In r (map (Z_to_bv 5) s7_kept) -> getr rX' r = getr rX r) ->
  INV_KV B n (y_v x) (y_pos x) lyc Sc Wc rX' memc' mdc' (y_cf x) (y_nm x) (y_o x) (y_ln x) (y_d x) gi kp vp
    (b9_key x ei) (b9_val x ei).
Proof.
intros n x ei kp vp gi k lyc Sc Wc rX memc mdc rX' memc' mdc' HI HJ' KM HKR.
destruct HI as (HC & Hcur & HCH & HKEY & HVAL & HSL & _ & _ & HRG).
pose proof (b9_geo B _ _ _ _ _ _ _ _ _ (proj1 HC)) as (_ & _ & _ & G & _).
pose proof G as (G1 & G2 & G3 & G4 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof (b9_fi_regs B _ _ _ _ _ _ _ _ _ (proj1 HC)) as HFI.
assert (HRA : pf_rg rX (b9_FI B (y_v x) ++ B9_R x ++ [(23, kp)]))
  by (apply b9_rg_app; split; [exact HFI | exact HRG]).
pose proof (s7_rg_kept rX rX' s7_kept _ HKR (s7_ks_all x kp) HRA) as HRA'.
apply b9_rg_app in HRA' as (HFI' & HRG').
apply b9_rg_app in HRG' as (HR' & _).
assert (Hlo : pf_sp0 (y_v x) - STK_reac_segconf_parse_file <= pf_s1 (y_v x)) by (rewrite SPF; lia).
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 (y_v x) <= a < pf_s1 (y_v x)) -> rdW Wc memc' a = rdW Wc memc a)
  by (intros a Ha _; exact (KM a Ha)).
destruct (s7_core_move n x lyc Sc Wc rX memc mdc rX' memc' mdc' (pf_s1 (y_v x)) HC HJ' Hlo HK HFI') as (HC' & KV).
destruct HC' as (HB' & HM' & HS' & _).
rewrite Hcur in HS'.
destruct (s7_keep_inbuf x Wc memc memc' (pf_s1 (y_v x)) kp (b9_key x ei) G Hlo HK KV HKEY) as (HK1 & HK2).
destruct (s7_keep_inbuf x Wc memc memc' (pf_s1 (y_v x)) vp (b9_val x ei) G Hlo HK KV HVAL) as (HV1 & HV2).
split; [exact HB'|]. split; [exact HM'|]. split; [exact HS'|].
split.
{ split; [exists ei; split; [exact HCH | split; reflexivity]|].
  split; [exact HK1|]. split; [exact HK2|]. split; [exact HV1 | exact HV2]. }
split; [|exact HR'].
exact (b9_keep_slot70 (y_v x) (y_pos x) (rdW Wc memc) (rdW Wc memc') vp G (fun a Ha _ => KM a Ha) HSL).
Qed.

(* the next cut JC (k + 1) after the call (the k-th compare known <> 0 from the branch) *)
Lemma s7_next : forall n x ei kp vp gi k lyc Sc Wc rX memc mdc rX' memc' mdc' lo,
  INV_JC B n x ei kp vp gi k lyc Sc Wc rX memc mdc ->
  getr rX 10 <> w64 0 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memc' mdc' 0 ->
  pf_sp0 (y_v x) - STK_reac_segconf_parse_file <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < pf_s1 (y_v x)) -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_rg rX' (b9_FI B (y_v x) ++ B9_R x ++ [(23, kp)]) ->
  (getr rX' 10 = w64 0 <-> strcasecmp (b9_key x ei) (nth (S k) b9_lits []) = 0) ->
  INV_JC B n x ei kp vp gi (S k) lyc Sc Wc rX' memc' mdc'.
Proof.
intros n x ei kp vp gi k lyc Sc Wc rX memc mdc rX' memc' mdc' lo HI HW HJ' Hlo HK HRA HIFF'.
destruct HI as (HC & Hcur & HCH & HKEY & HVAL & HSL & HPREV & HIFF & _).
pose proof (b9_geo B _ _ _ _ _ _ _ _ _ (proj1 HC)) as (_ & _ & _ & G & _).
pose proof G as (G1 & G2 & G3 & G4 & _).
apply b9_rg_app in HRA as (HFI' & HRG').
destruct (s7_core_move n x lyc Sc Wc rX memc mdc rX' memc' mdc' lo HC HJ' Hlo HK HFI') as (HC' & KV).
split; [exact HC'|]. split; [exact Hcur|]. split; [exact HCH|].
split; [exact (s7_keep_inbuf x Wc memc memc' lo kp (b9_key x ei) G Hlo HK KV HKEY)|].
split; [exact (s7_keep_inbuf x Wc memc memc' lo vp (b9_val x ei) G Hlo HK KV HVAL)|].
split.
{ apply (b9_keep_slot70 (y_v x) (y_pos x) (rdW Wc memc) (rdW Wc memc') vp G); [|exact HSL].
  intros a Ha Hw. apply HK; [exact Ha|]. intros Hn. apply Hw. left. lia. }
split.
{ intros j Hj. destruct (Nat.lt_ge_cases j k) as [Hjk | Hjk]; [exact (HPREV j Hjk)|].
  assert (j = k) as -> by lia. intros Heq. apply HW. apply HIFF. exact Heq. }
split; [exact HIFF' | exact HRG'].
Qed.

(* the call strcasecmp(key, lit (k + 1)) at a state that kept every byte and every register of s7_kept of the cut
   JC k, with ra = BASE + J(k+1), a0 = kp, a1 = the literal: aj_art_at with ASTRCASECMP, then JC (k + 1) *)
Lemma s7_call : forall n x ei kp vp gi k lyc Sc Wc rX memc mdc regsT memT mdT,
  INV_JC B n x ei kp vp gi k lyc Sc Wc rX memc mdc ->
  getr rX 10 <> w64 0 -> (S k < 4)%nat ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memT mdT 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memT a = rdW Wc memc a) ->
  (forall r, In r (map (Z_to_bv 5) s7_kept) -> getr regsT r = getr rX r) ->
  getr regsT 1 = Z_to_bv 64 (BASE + B9_JC (S k)) ->
  getr regsT 10 = w64 kp ->
  getr regsT 11 = w64 (seg_litA_rc (nth (S k) b9_lits [])) ->
  b9_from B (B9_JC (S k)) (INV_JC B n x ei kp vp gi (S k)) x ->
  SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (SIG SS___interceptor_trampoline_strcasecmp)) memT (seg_rom SEGS)) mdT)
    (b9_goal B x).
Proof.
intros n x ei kp vp gi k lyc Sc Wc rX memc mdc regsT memT mdT HI HW Hk HJT KT HKR R1 R10 R11 HNEXT.
pose proof HI as (HC & _ & _ & HKEY & _ & _ & _ & _ & HRG).
pose proof (b9_geo B _ _ _ _ _ _ _ _ _ (proj1 HC)) as (_ & _ & _ & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof (b9_fi_regs B _ _ _ _ _ _ _ _ _ (proj1 HC)) as HFI.
assert (HRA : pf_rg rX (b9_FI B (y_v x) ++ B9_R x ++ [(23, kp)]))
  by (apply b9_rg_app; split; [exact HFI | exact HRG]).
pose proof (s7_rg_kept rX regsT s7_kept _ HKR (s7_ks_all x kp) HRA) as HRAT.
pose proof HRAT as HFIT. apply b9_rg_app in HFIT as (HFIT & _).
assert (Hlo0 : pf_sp0 (y_v x) - STK_reac_segconf_parse_file <= pf_s1 (y_v x)) by (rewrite SPF; lia).
assert (KT' : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 (y_v x) <= a < pf_s1 (y_v x)) -> rdW Wc memT a = rdW Wc memc a)
  by (intros a Ha _; exact (KT a Ha)).
destruct (s7_core_move n x lyc Sc Wc rX memc mdc regsT memT mdT (pf_s1 (y_v x)) HC HJT Hlo0 KT' HFIT)
  as (HCT & KVT).
pose proof (b9_st_of_base B _ _ _ _ _ _ _ _ (proj1 HCT)) as HSTT.
destruct (s7_keep_inbuf x Wc memc memT (pf_s1 (y_v x)) kp (b9_key x ei) G Hlo0 KT' KVT HKEY) as (HKS & HKI).
destruct HKEY as (((_ & HNZ) & _) & _).
assert (HwIn : In (nth (S k) b9_lits []) [S_role; S_model; S_ignore; S_knock])
  by (unfold b9_lits; apply nth_In; cbn [length]; lia).
destruct (s7_lit_ok _ HwIn) as (HNZw & HZSw).
destruct (b9_astr_of_sa Wc memT kp (b9_key x ei) HKS) as (_ & _ & _ & HZS & _).
(* the registers at the call *)
assert (R2 : getr regsT 2 = w64 (pf_s1 (y_v x))).
{ apply (s7_bvr _ 2%bv 2); [reflexivity|]. apply (b9_rg_get regsT _ 2 _ HFIT). unfold b9_FI. s7_in. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ apply (s7_bvr _ 3%bv 3); [reflexivity|]. apply (b9_rg_get regsT _ 3 _ HFIT). unfold b9_FI. s7_in. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ apply (s7_bvr _ 4%bv 4); [reflexivity|]. apply (b9_rg_get regsT _ 4 _ HFIT). unfold b9_FI. s7_in. }
assert (Hsp : spZ regsT = pf_sp0 (y_v x) + (pf_s1 (y_v x) - pf_sp0 (y_v x))).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Ho16 : (pf_s1 (y_v x) - pf_sp0 (y_v x)) mod 16 = 0) by (apply s7_m16; [exact G5 | exact G3]).
assert (HraT : YK0s.ret_ok (getr regsT 1)).
{ rewrite R1. destruct (s7_ret_ok (S k) Hk) as (Hr1 & Hr2). apply ret_ok_codeptr_v; [exact Hr1 | exact Hr2]. }
destruct (b9_strcasecmp_pre B (y_v x) (y_pos x) lyc Sc Wc memT mdT regsT kp (b9_key x ei) (nth (S k) b9_lits [])
  HSTT ltac:(rewrite Hsp; lia) HraT R3 R4 HwIn R10 R11 HKS HKI)
  as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
(* the call *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False)
    (SIG SS___interceptor_trampoline_strcasecmp) Wc regsT memT STK_reac_segconf_parse_file (pf_sp0 (y_v x))
    (seg_spec.RC_PARSE_W (p_c (y_v x))) (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x))
    (p_md (y_v x)) [(5, y_pos x)] lyc Sc mdT 0 (pf_s1 (y_v x) - pf_sp0 (y_v x)) (Z_to_bv 64 (BASE + B9_JC (S k))) _
    HJT Hsp Ho16 ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(rewrite SPF; unfold ESTACK; lia) R1
    (fun a (H : False) => False_ind _ H)).
  exact (ASTRCASECMP fx lyc Sc Wc regsT memT mdT kp (seg_litA_rc (nth (S k) b9_lits [])) (seg_spec.zb (b9_key x ei))
    (seg_spec.zb (nth (S k) b9_lits [])) P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14). }
(* back at J(k+1), at the same FP state *)
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ & HK3).
change (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + B9_JC (S k))) mem3 (seg_rom SEGS)) md3)
  with (cfg_at SEGS (BASE + B9_JC (S k)) regs3 mem3 md3).
apply (HNEXT lyc Sc Wc regs3 mem3 md3).
apply (s7_next n x ei kp vp gi k lyc Sc Wc rX memc mdc regs3 mem3 md3 (pf_s1 (y_v x) - 2 * ESTACK) HI HW HJ3).
- rewrite SPF. unfold ESTACK. lia.
- intros a Ha Hn. rewrite HK3; [exact (KT a Ha) | exact Ha | lia | tauto].
- exact (b9_rg_pres regsT regs3 _ HP3 (s7_cs_all x kp) HRAT).
- exact (s7_iff regs3 (b9_key x ei) (nth (S k) b9_lits []) HNZ HNZw HZS HZSw HQ).
Qed.

(* ======================= the three stretches ======================= *)
(** ** SB9_7: J6 0x88588 -> ROLE 0x88630 (the key is "role") or J7 0x8859c (strcasecmp(key, "model")) *)
Lemma b9_s7 : SB9_7 B.
Proof.
unfold SB9_7, from_JC. intros n HEX HNX x ei kp vp gi. unfold b9_from. intros lyc Sc Wc rX memc mdc HI.
pose proof HI as (HC & Hcur & HCH & HKEY & HVAL & HSL & HPREV & HIFF & HRG).
pose proof HC as (HB & _).
pose proof HB as (_ & HFI & _).
pose proof HFI as (HJ & _).
(* the seed at J6 *)
pose proof (s7_seed B9_J6 Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (HA0 : env_agree 32 (Ereg rX []) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
change (cfg_at SEGS (BASE + B9_JC 0) rX memc mdc)
  with (mkCfg (mkst rX (Z_to_bv 64 (BASE + B9_J6)) memc (seg_rom SEGS)) mdc).
(* 0x88588 beqz a0 *)
psrr_branch_pi RUNP BR HS.
- (* taken: a0 = 0, the key is "role"; to ROLE *)
  assert (HW : getr rX 10 = w64 0)
    by exact (proj2 (s7_beqz E (getr rX 10) true (EE 10%nat 10%bv eq_refl) Hc) eq_refl).
  clear Hc.
  paj_run_to_sh RUNTO HS HJ PF_ROLE.
  { s7_awr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  clear HFr HG HF.
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX [] (map (Z_to_bv 5) s7_kept) HS HA0 ltac:(vm_compute; reflexivity))
    as HKR.
  cbn [ms_regs restrict] in HKR.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_ROLE) rg mm mdx) end.
  unfold b9_goal. rewrite Hcur. unfold b9_line.
  apply (HEX (y_v x) (y_pos x) lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (y_cf x) (y_nm x) (y_o x) (y_ln x) (y_d x)
    gi kp vp (b9_key x ei) (b9_val x ei)).
  + exact (s7_exit n x ei kp vp gi 0 lyc Sc Wc rX memc mdc (ms_regs ms) (ms_mem ms) mdv HI HJ KM HKR).
  + exact (proj1 HIFF HW).
- (* not taken: a0 <> 0; 0x8858c auipc, 0x88590 addi a1 = "model", 0x88594 mv a0,s7, 0x88598 jal strcasecmp *)
  assert (HW : getr rX 10 <> w64 0).
  { intros H0. pose proof (proj1 (s7_beqz E (getr rX 10) false (EE 10%nat 10%bv eq_refl) Hc) H0) as Hf.
    discriminate Hf. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJ.
  { s7_awr. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  clear HFr HG HF.
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ rX [] (map (Z_to_bv 5) s7_kept) HS HA0 ltac:(vm_compute; reflexivity))
    as HKR.
  cbn [ms_regs restrict] in HKR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  pmkst HS.
  assert (R23 : getr rX 23 = w64 kp).
  { apply (s7_bvr _ 23%bv 23); [reflexivity|]. apply (b9_rg_get rX _ 23 _ HRG).
    apply in_or_app. right. left. reflexivity. }
  apply (s7_call n x ei kp vp gi 0 lyc Sc Wc rX memc mdc (ms_regs ms) (ms_mem ms) mdv HI HW ltac:(lia) HJ KM HKR).
  + rewrite Q1. reflexivity.
  + rewrite Q10, (EE 23%nat 23%bv eq_refl). exact R23.
  + rewrite Q11. exact (s7_atom_model E HEI).
  + exact (HNX x ei kp vp gi).
Qed.

(** ** SB9_8: J7 0x8859c -> MODEL 0x886d4 (the key is "model") or J8 0x885b0 (strcasecmp(key, "ignore")) *)
Lemma b9_s8 : SB9_8 B.
Proof.
unfold SB9_8, from_JC. intros n HEX HNX x ei kp vp gi. unfold b9_from. intros lyc Sc Wc rX memc mdc HI.
pose proof HI as (HC & Hcur & HCH & HKEY & HVAL & HSL & HPREV & HIFF & HRG).
pose proof HC as (HB & _).
pose proof HB as (_ & HFI & _).
pose proof HFI as (HJ & _).
(* the seed at J7 *)
pose proof (s7_seed B9_J7 Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (HA0 : env_agree 32 (Ereg rX []) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
change (cfg_at SEGS (BASE + B9_JC 1) rX memc mdc)
  with (mkCfg (mkst rX (Z_to_bv 64 (BASE + B9_J7)) memc (seg_rom SEGS)) mdc).
(* 0x8859c beqz a0 *)
psrr_branch_pi RUNP BR HS.
- (* taken: a0 = 0, the key is "model" (and not "role"); to MODEL *)
  assert (HW : getr rX 10 = w64 0)
    by exact (proj2 (s7_beqz E (getr rX 10) true (EE 10%nat 10%bv eq_refl) Hc) eq_refl).
  clear Hc.
  paj_run_to_sh RUNTO HS HJ PF_MODEL.
  { s7_awr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  clear HFr HG HF.
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX [] (map (Z_to_bv 5) s7_kept) HS HA0 ltac:(vm_compute; reflexivity))
    as HKR.
  cbn [ms_regs restrict] in HKR.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_MODEL) rg mm mdx) end.
  unfold b9_goal. rewrite Hcur. unfold b9_line.
  apply (HEX (y_v x) (y_pos x) lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (y_cf x) (y_nm x) (y_o x) (y_ln x) (y_d x)
    gi kp vp (b9_key x ei) (b9_val x ei)).
  + exact (s7_exit n x ei kp vp gi 1 lyc Sc Wc rX memc mdc (ms_regs ms) (ms_mem ms) mdv HI HJ KM HKR).
  + exact (HPREV 0%nat ltac:(lia)).
  + exact (proj1 HIFF HW).
- (* not taken: a0 <> 0; 0x885a0 auipc, 0x885a4 addi a1 = "ignore", 0x885a8 mv a0,s7, 0x885ac jal strcasecmp *)
  assert (HW : getr rX 10 <> w64 0).
  { intros H0. pose proof (proj1 (s7_beqz E (getr rX 10) false (EE 10%nat 10%bv eq_refl) Hc) H0) as Hf.
    discriminate Hf. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJ.
  { s7_awr. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  clear HFr HG HF.
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ rX [] (map (Z_to_bv 5) s7_kept) HS HA0 ltac:(vm_compute; reflexivity))
    as HKR.
  cbn [ms_regs restrict] in HKR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  pmkst HS.
  assert (R23 : getr rX 23 = w64 kp).
  { apply (s7_bvr _ 23%bv 23); [reflexivity|]. apply (b9_rg_get rX _ 23 _ HRG).
    apply in_or_app. right. left. reflexivity. }
  apply (s7_call n x ei kp vp gi 1 lyc Sc Wc rX memc mdc (ms_regs ms) (ms_mem ms) mdv HI HW ltac:(lia) HJ KM HKR).
  + rewrite Q1. reflexivity.
  + rewrite Q10, (EE 23%nat 23%bv eq_refl). exact R23.
  + rewrite Q11. exact (s7_atom_ignore E HEI).
  + exact (HNX x ei kp vp gi).
Qed.

(** ** SB9_9: J8 0x885b0 -> IGN 0x887e0 (the key is "ignore") or J9 0x885c4 (strcasecmp(key, "knock")) *)
Lemma b9_s9 : SB9_9 B.
Proof.
unfold SB9_9, from_JC. intros n HEX HNX x ei kp vp gi. unfold b9_from. intros lyc Sc Wc rX memc mdc HI.
pose proof HI as (HC & Hcur & HCH & HKEY & HVAL & HSL & HPREV & HIFF & HRG).
pose proof HC as (HB & _).
pose proof HB as (_ & HFI & _).
pose proof HFI as (HJ & _).
(* the seed at J8 *)
pose proof (s7_seed B9_J8 Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (HA0 : env_agree 32 (Ereg rX []) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
change (cfg_at SEGS (BASE + B9_JC 2) rX memc mdc)
  with (mkCfg (mkst rX (Z_to_bv 64 (BASE + B9_J8)) memc (seg_rom SEGS)) mdc).
(* 0x885b0 beqz a0 *)
psrr_branch_pi RUNP BR HS.
- (* taken: a0 = 0, the key is "ignore" (and neither "role" nor "model"); to IGN *)
  assert (HW : getr rX 10 = w64 0)
    by exact (proj2 (s7_beqz E (getr rX 10) true (EE 10%nat 10%bv eq_refl) Hc) eq_refl).
  clear Hc.
  paj_run_to_sh RUNTO HS HJ PF_IGN.
  { s7_awr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  clear HFr HG HF.
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX [] (map (Z_to_bv 5) s7_kept) HS HA0 ltac:(vm_compute; reflexivity))
    as HKR.
  cbn [ms_regs restrict] in HKR.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_IGN) rg mm mdx) end.
  unfold b9_goal. rewrite Hcur. unfold b9_line.
  apply (HEX (y_v x) (y_pos x) lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (y_cf x) (y_nm x) (y_o x) (y_ln x) (y_d x)
    gi kp vp (b9_key x ei) (b9_val x ei)).
  + exact (s7_exit n x ei kp vp gi 2 lyc Sc Wc rX memc mdc (ms_regs ms) (ms_mem ms) mdv HI HJ KM HKR).
  + exact (HPREV 0%nat ltac:(lia)).
  + exact (HPREV 1%nat ltac:(lia)).
  + exact (proj1 HIFF HW).
- (* not taken: a0 <> 0; 0x885b4 auipc, 0x885b8 addi a1 = "knock", 0x885bc mv a0,s7, 0x885c0 jal strcasecmp *)
  assert (HW : getr rX 10 <> w64 0).
  { intros H0. pose proof (proj1 (s7_beqz E (getr rX 10) false (EE 10%nat 10%bv eq_refl) Hc) H0) as Hf.
    discriminate Hf. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJ.
  { s7_awr. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  clear HFr HG HF.
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ rX [] (map (Z_to_bv 5) s7_kept) HS HA0 ltac:(vm_compute; reflexivity))
    as HKR.
  cbn [ms_regs restrict] in HKR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  pmkst HS.
  assert (R23 : getr rX 23 = w64 kp).
  { apply (s7_bvr _ 23%bv 23); [reflexivity|]. apply (b9_rg_get rX _ 23 _ HRG).
    apply in_or_app. right. left. reflexivity. }
  apply (s7_call n x ei kp vp gi 2 lyc Sc Wc rX memc mdc (ms_regs ms) (ms_mem ms) mdv HI HW ltac:(lia) HJ KM HKR).
  + rewrite Q1. reflexivity.
  + rewrite Q10, (EE 23%nat 23%bv eq_refl). exact R23.
  + rewrite Q11. exact (s7_atom_knock E HEI).
  + exact (HNX x ei kp vp gi).
Qed.
End x.
End d.
