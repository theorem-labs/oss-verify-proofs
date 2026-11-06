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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaNoChain PaArt PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtStack RtShadow RtAlloc RtAlloc04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdChk CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c rec_clear_c verbs_receive_c
  sup_reply_code_c joined_c send_message_c rec_calls_copy_c rec_calls_equal_c rec_calls_free_c check_round_trip_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_rep check_round_trip_k check_round_trip_m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- the realigned stack pointer: (sp - 256) & -32 ---------- *)
Lemma crt_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma crt_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite crt_land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma crt_denot_and_m32_add0 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit (-32))) (SLit 0)) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r.
unfold U. rewrite (crt_denot_and_m32 E n v c Hn H0 H1 Hv). rewrite unsigned_lit_small; [apply zcanon_id|];
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)); (split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia] | unfold M64; lia]).
Qed.
Lemma crt_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma crt_preg : forall r1 r2 (r : bv 5), aregs_preserved r1 r2 -> acallee_saved (bv_unsigned r) -> getr r2 r = getr r1 r.
Proof. intros r1 r2 r HP Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma crt_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma crt_den_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma crt_le_byte_range : forall v n k, 0 <= YG0f.le_byte v n k < 256.
Proof. intros v n k. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

(* the 13 registers the prologue saves, at sp0 - 8 - 8 j: ra, s0, s1, s2 .. s11 *)
Definition crt_saved : list nat := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma crt_saved_len : length crt_saved = 13%nat. Proof. reflexivity. Qed.
(* the entry state: every register its own atom, atom 32 the shadow base, atom 33 the use-after-return cell; the 256-byte
   frame, the shadow GOT word and cell, the use-after-return GOT word and cell *)
Definition crt_ssE : sstate := mkSS AF_check_round_trip sr_atoms
  [stack_region 256; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33] None
  (mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0)] [] []).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma crt_val_of_aval : forall H (m : word -> option byte) a n v,
  aval_mem (aview SEGS H m) a n v -> val_mem SEGS (mrestrict H m) a n v.
Proof.
intros H m a n v Hv k Hk. destruct (aview_byte SEGS H m (a + Z.of_nat k) _ (Hv k Hk)) as (b & Hb & Hbv & _).
rewrite Hb. f_equal. change (YO0f.le_byte v n k) with (YG0f.le_byte v n k). rewrite Hbv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma crt_aval_of_val : forall H (m : word -> option byte) a n v,
  val_mem SEGS (mrestrict H m) a n v -> aval_mem (aview SEGS H m) a n v.
Proof.
intros H m a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
change (YO0f.le_byte v n k) with (YG0f.le_byte v n k). apply Z.mod_small. apply crt_le_byte_range.
Qed.
Lemma crt_aval_kept : forall (rd rd' : reader) a n v,
  (forall k, 0 <= k < Z.of_nat n -> rd' (a + k) = rd (a + k)) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Hk Hv k Hkn. rewrite Hk by lia. apply Hv. exact Hkn. Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
(* the statement's own hypotheses (check_round_trip_c.v): the program callees' contracts, the runtime entries, the
   bridge from the image's addresses to the listing's atoms *)
Hypothesis HSEND : forall fx0 : YK11.FPState, @tsend_message_spec fx0 rc SK PI B MT.
Hypothesis HJOINED : forall fx0 : YK11.FPState, @tjoined_spec fx0 rc SK PI B MT.
Hypothesis HRCC : forall fx0 : YK11.FPState, @trec_calls_copy_spec fx0 rc SK PI B MT.
Hypothesis HRCE : forall fx0 : YK11.FPState, @trec_calls_equal_spec fx0 rc SK PI B MT.
Hypothesis HRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Variable PC_STRDUP_RA0 : Z.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASTRDUP4 : forall fx0 : YK11.FPState, @astrdup04_rule fx0 rc SK SEGS B MT (SIG CS___interceptor_trampoline_strdup) PC_STRDUP_RA0.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis ASM5 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 5.
Hypothesis ASF5 : forall fx0 : YK11.FPState, @astack_free_cls_realizes fx0 rc SEGS B (SIG CS___asan_stack_free_5) 5.
Hypothesis ASH00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0.
Hypothesis ASHF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8.
Hypothesis HVAL : cmd_val_objs.
(* the per-binary record (the walk hypotheses, by cgif's names): the image's symbol record,
   the runtime trampolines (TL) and side-stack entries (TLF), the model and meter laws, the program-call targets, the
   program statics, and the image facts (IMG) *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.
(* the record's facts, from CmdRecFacts.v: the read-only range lies in the image and below
   the overflow-list head, the program statics lie in the image and outside the read-only range; at every AR state the
   record's checks give the shadow (cmd_addressable_chk), a live block its word tail (cmd_heap_tail_vis), arodata_okP
   the read-only view rt_rom_view (cmd_rom_view_on) and cmd_ro_ok (cmd_ro_ok_of_aro, at its uses) *)
Let cif_ro_img : forall a, in_roP SEGS CMD_RLO CMD_RHI a -> in_img SEGS a :=
  fun a H => proj1 (cmd_ro_prog_apart SEGS B LAWS HB IMG a H).
Let RRO : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a := RRO SEGS B LAWS HB IMG.
Let RPG : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a := RPG SEGS B LAWS HB IMG.
#[local] Instance ROB : ro_below_ofl SEGS CMD_RLO CMD_RHI := ROB SEGS B LAWS HB IMG.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a := cif_prog_img _ _ IMG.
Let cmd_addressable_chk : forall ly S (W : world SEGS) mem md a n, AR SEGS B ly S W mem md -> cmd_addr_b a n = true ->
  range_addressable (rdW W mem) SHADOW_OFF a n := cmd_addressable_chk SEGS B LAWS HB.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e := cmd_heap_tail_vis SEGS B LAWS HB.
Let cmd_rom_view_on : forall (W : world SEGS) mem, arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> rt_rom_view SEGS B W mem :=
  cmd_rom_view_on SEGS B LAWS HB IMG CMD_RLO CMD_RHI.
(* ---------- budget facts the segments share ---------- *)
(* the events of a route, of the reply and of the call after the reply are sums of non-negative counts: every
   recorder entry's count is a constant plus its spill-arm frees (rec_spill_frees, CmdRep.v), a count of list lengths *)
Lemma crtev_vr_nn_rsf : forall R0, 0 <= rec_spill_frees R0.
Proof. intros R0. unfold rec_spill_frees. destruct (Nat.ltb _ _); lia. Qed.
Lemma crt_ev_args_nn : forall R0, 0 <= ev_args R0.
Proof. intros R0. unfold ev_args. induction (r_calls R0) as [|c l IH]; cbn [fold_right]; lia. Qed.
Lemma crt_jn_nn : forall l, 0 <= PJoinR.join_need l.
Proof. intros l. unfold PJoinR.join_need. induction l as [|w l IH]; cbn [fold_right]; lia. Qed.
Ltac crtev_vr_nn_codZ t := lazymatch t with Z => idtac | _ -> ?u => crtev_vr_nn_codZ u end.
(* unfold every event count (a constant whose type ends in Z), but not the arithmetic and not the two counts that
   stay atoms *)
Ltac crtev_vr_nn_unf :=
  repeat match goal with
  | |- context [?c] => is_const c;
    lazymatch c with
    | rec_spill_frees => fail | ev_args => fail
    | Z.add => fail | Z.mul => fail | Z.sub => fail | Z.max => fail | Z.min => fail | Z.of_nat => fail
    | Z.opp => fail | Z.pow => fail | Z.div => fail | Z.modulo => fail | Z.succ => fail | Z.pred => fail
    | Z.abs => fail | Z.of_N => fail | bv_unsigned => fail
    | _ => let t := type of c in crtev_vr_nn_codZ t; unfold c
    end
  end.
Ltac crtev_vr_nn_split :=
  repeat (match goal with |- context [match ?x with _ => _ end] => destruct x end; cbv beta iota zeta).
Ltac crtev_vr_nn_gen :=
  repeat match goal with
  | |- context [rec_spill_frees ?r] =>
    let H := fresh "Hn" in pose proof (crtev_vr_nn_rsf r) as H; revert H; generalize (rec_spill_frees r); intros ? ?
  | |- context [ev_args ?r] =>
    let H := fresh "Hn" in pose proof (crt_ev_args_nn r) as H; revert H; generalize (ev_args r); intros ? ?
  end.
Ltac crtev_vr_nn_tac := crtev_vr_nn_unf; crtev_vr_nn_split; crtev_vr_nn_gen; lia.
Lemma crtev_vr_nn_route : forall R0 ln tk s, 0 <= ev_route R0 ln tk s.
Proof. intros R0 ln tk s. crtev_vr_nn_tac. Qed.
Lemma crtev_vr_nn_after : forall R2 af, 0 <= ev_after R2 af.
Proof. intros R2 af. crtev_vr_nn_tac. Qed.
Lemma crt_ev_vr_nn : forall R D, 0 <= ev_vr R D.
Proof.
intros R D. unfold ev_vr. crtev_vr_nn_split.
lazymatch goal with |- context [ev_route ?a ?b ?c ?d] =>
  pose proof (crtev_vr_nn_route a b c d) as H1; set (r1 := ev_route a b c d) in * end.
lazymatch goal with |- context [ev_after ?a ?b] =>
  pose proof (crtev_vr_nn_after a b) as H2; set (r2 := ev_after a b) in * end.
clearbody r1 r2. crtev_vr_nn_unf. lia.
Qed.
Lemma crt_ev_send_nn : forall R D, 0 <= EV_SEND_MESSAGE R D.
Proof.
intros R D. unfold EV_SEND_MESSAGE, EV_REC_CLEAR.
pose proof (crt_ev_vr_nn (RecModel.rec_clear R) D). pose proof (crt_ev_args_nn R). lia.
Qed.
Lemma crt_xm_vr_nn : forall R D, 0 <= XM_VERBS_RECEIVE MT R D.
Proof.
intros R D. unfold XM_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ.
pose proof (mo_malloc_nonneg MT MTL 8194 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). pose proof (crt_ev_vr_nn R D).
nia.
Qed.
Lemma crt_xm_send_nn : forall R D, 0 <= XM_SEND_MESSAGE MT R D.
Proof.
intros R D. unfold XM_SEND_MESSAGE, XM_REC_CLEAR.
pose proof (mo_malloc_nonneg MT MTL 8192 ltac:(lia)). pose proof (mo_free_nonneg MT MTL).
pose proof (crt_xm_vr_nn (RecModel.rec_clear R) D). pose proof (crt_ev_args_nn R).
nia.
Qed.
Lemma crtlive_rcc_fold : forall (l : list (list byte)) a,
  fold_right (fun x acc => LIVE_XSTRDUP x + acc) a l = fold_right (fun x acc => LIVE_XSTRDUP x + acc) 0 l + a.
Proof. induction l as [|x l IH]; intros a; cbn [fold_right]; [lia | rewrite IH; lia]. Qed.
Lemma crtlive_rcc_one : forall l : list (list byte), Forall (fun s => Z.of_nat (length s) <= LMAX) l ->
  fold_right (fun x acc => LIVE_XSTRDUP x + acc) 0 l <= Z.of_nat (length l) * (LMAX + 1).
Proof.
induction l as [|x l IH]; intros HF; cbn [fold_right length]; [lia|].
apply Forall_cons_iff in HF as [Hx Hr]. specialize (IH Hr). change (LIVE_XSTRDUP x) with (Z.of_nat (length x) + 1).
unfold LMAX in *. lia.
Qed.
Lemma crtlive_rcc_all : forall cs : list rcall,
  (forall c, In c cs -> (length (snd c) <= 6)%nat /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)) ->
  fold_right (fun x acc => LIVE_XSTRDUP x + acc) 0 (concat (map snd cs)) <= Z.of_nat (length cs) * (6 * (LMAX + 1)).
Proof.
induction cs as [|c cs IH]; intros Hcs; [cbn; lia|].
cbn [map concat length]. rewrite fold_right_app, crtlive_rcc_fold.
destruct (Hcs c (or_introl eq_refl)) as [H6 HL].
pose proof (crtlive_rcc_one (snd c) HL) as H1.
pose proof (IH (fun c' Hc' => Hcs c' (or_intror Hc'))) as H2.
unfold LMAX in *. lia.
Qed.
Lemma crt_live_rcc : forall ly' S' rd R' O', rec_repA B ly' S' rd R' O' -> (length (r_calls R') <= 2)%nat -> LIVE_REC_CALLS_COPY R' <= 12 * (LMAX + 1).
Proof.
intros ly' S' rd R' O' (Q & HA & _) HN.
destruct HA as (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & _).
assert (HC : forall c, In c (r_calls R') ->
  (length (snd c) <= 6)%nat /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)).
{ intros c Hc. apply In_nth_error in Hc as (i & Hi).
  assert (Hil : (i < length (l_calls Q))%nat) by (rewrite C2; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (l_calls Q) i) as [P|] eqn:EP; [|apply nth_error_None in EP; lia].
  destruct (C4 i c P Hi EP) as [(_ & H6 & _) HL]. split; [exact H6 | exact HL]. }
unfold LIVE_REC_CALLS_COPY, PRcc.rcc_args.
pose proof (crtlive_rcc_all (r_calls R') HC) as H. unfold LMAX in *. lia.
Qed.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
Let crt_RUNP := SRr_run_pi_AJ B LAWS.
Let crt_RUNC := SRr_run_pi_AJ_call B LAWS.
(* ---------- helpers the segments share ---------- *)
(* a member of a literal list *)
Ltac crt_in := cbn [In]; repeat first [left; reflexivity | right].
(* a register read by its numeral or by its bit-vector name *)
Lemma crt_reg_bv : forall (rr : bvmap 5 word) (k : Z) (r : bv 5) v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr k r v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma crt_reg_lit : forall (rr : bvmap 5 word) (k : Z) (r : bv 5) v, bv_unsigned r = k -> getr rr r = v -> getr rr (Z_to_bv 5 k) = v.
Proof. intros rr k r v Hr H. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.
(* the seeds' fact on sp and s1 (between 2^46 and 2^47, 32-byte aligned), and the shadow cell of a value with atom 32
   the shadow base *)
Definition crt_SPF : afact := mkAF (2^46) (2^47) 5.
Definition crt_shy (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff 32 0).
(* the reply's copy: at most LMAX + 2 bytes (CmdRep.v areply_at) *)
Lemma crt_reply_len : forall bl rd gr y q0 x, areply_at bl rd gr y q0 -> y = Some x -> Z.of_nat (length x) <= LMAX + 2.
Proof.
intros bl rd gr y q0 x H ->. destruct q0 as [pn|]; cbn [areply_at] in H; [|contradiction].
destruct H as (_ & _ & _ & _ & _ & _ & _ & H8). exact H8.
Qed.
(* the two GOT words *)
Lemma crt_got : forall (rd : reader) a (l : list byte) v, abytes_atR rd a l -> length l = 8%nat ->
  (forall k, (k < 8)%nat -> bv_unsigned (nth k l (Z_to_bv 8 0)) = YG0f.le_byte v 8 k) -> aval_mem rd a 8 v.
Proof. intros rd a l v Hl Hlen Hb k Hk. rewrite (Hl k ltac:(lia)), (Hb k Hk). reflexivity. Qed.
Lemma crt_got_q : forall (rd : reader), cmd_ro_ok rd -> aval_mem rd 0xa7080 8 A_G_QUITTING.
Proof.
intros rd (HB0 & _). apply (crt_got rd 0xa7080 RO_ptr_a7080); [|reflexivity|].
- unfold cmd_ro_bytes in HB0. repeat (destruct HB0 as [_ HB0]). exact HB0.
- intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma crt_got_r : forall (rd : reader), cmd_ro_ok rd -> aval_mem rd 0xa7068 8 A_G_REC.
Proof.
intros rd (HB0 & _). apply (crt_got rd 0xa7068 RO_ptr_a7068); [|reflexivity|].
- unfold cmd_ro_bytes in HB0.
  repeat (match type of HB0 with abytes_atR _ 0xa7068 _ /\ _ => fail 1 | _ /\ _ => destruct HB0 as [_ HB0] end).
  exact (proj1 HB0).
- intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.
(* g_rec, record.spill and g_quitting are program statics: no runtime entry owns them, and they are not errno *)
Lemma crt_pg_prog : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof.
intros a Ha. rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC.
destruct Ha as (r & Hr & Ha). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma crt_pg : forall a, inFP cmd_PG a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof. intros a Ha. destruct (prog_static_sep B a (ts_ok B HB) (crt_pg_prog a Ha)) as (H1 & H2 & _). auto. Qed.
Lemma crt_inrec_pg : forall a, rcf_inrec a -> inFP cmd_PG a.
Proof.
intros a [H | H].
- exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in H; lia].
- exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in H; lia].
Qed.
(* a run whose regions have no write window leaves every byte (rec_calls_free.v frame_nowin) *)
Lemma crt_frame_nowin : forall E (rs : smem) H (m m' : word -> option byte),
 frame_of E rs (mrestrict H m) (mrestrict H m') ->
 (forall b wlo whi, In (b, wlo, whi) (windows rs) -> whi <= wlo) ->
 forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hw a Ha. apply (kept_of_frame E rs H m m' (fun _ => False) HF); [|exact Ha | tauto].
intros b wlo whi a' Hin Hr. pose proof (Hw b wlo whi Hin). lia.
Qed.
Ltac crt_nowin := let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let Hin := fresh "Hin" in
  intros b wlo whi Hin; vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]); destruct Hin.
(* the live blocks are distinct (rec_calls_free.v pw_nodup) *)
Lemma crt_pw_nodup : forall (l : list (Z * Z)), Forall (fun b => 0 <= snd b) l ->
 pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hn H; [constructor|]. cbn [map pairwise] in H. destruct H as [Hf Hp].
apply Forall_cons_iff in Hn as [Hx Hn]. constructor; [|exact (IH Hn Hp)].
intros Hin. apply (in_map (fun b => (fst b, req_size (snd b)))) in Hin. rewrite Forall_forall in Hf.
pose proof (Hf _ Hin) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos (snd x) Hx). lia.
Qed.
Lemma crt_nodup : forall lyc Sc (Wc : world SEGS) mc dc, AR SEGS B lyc Sc Wc mc dc -> List.NoDup (ablocks B lyc Sc).
Proof.
intros lyc Sc Wc mc dc HAR.
destruct (al_sep _ _ LAWS lyc Sc Wc mc dc HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
apply (crt_pw_nodup _); [|exact Hp]. apply Forall_forall. intros [p n] Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn). cbn [snd]. lia.
Qed.

Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (W0 sb hb arr q : Z) (wp : list Z) (ws : list (list byte)) (R : rstate) (O rest : list (Z * Z)).
Hypothesis HPRE : afn_pre SEGS B CHECK_ROUND_TRIP_STK ly S W regs mem md ch.
(* the machine stack from the entry sp to its top is present (pass 5b): kept to joined's call for its premise *)
Hypothesis HPRES : astack_pres ly (w_H W) mem (spZ regs).
(* rounding mode 0 at the entry (pass 4): send_message's premise *)
Hypothesis HFRM : Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
Hypothesis HROD : arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem).
Hypothesis HCNT : count_cid 5 (frames S) < fs_frames 5.
Hypothesis HNFR : Z.of_nat (length (frames S)) <= 2.
Hypothesis H10 : getr regs 10 = w64 W0.
Hypothesis H11 : getr regs 11 = w64 sb.
Hypothesis H12 : getr regs 12 = w64 hb.
Hypothesis HSB : 0 <= sb < 2 ^ 64.
Hypothesis HHB : 0 <= hb < 2 ^ 64.
Hypothesis HW1 : spZ regs <= W0 + 16.
Hypothesis HW2 : W0 + 32 <= ly_stk_hi ly.
Hypothesis HW8 : W0 mod 8 = 0.
Hypothesis HLEN : length wp = length ws.
Hypothesis HN31 : Z.of_nat (length ws) < 2 ^ 31.
Hypothesis HVN : aval_mem (rdW W mem) (W0 + 24) 4 (Z.of_nat (length ws)).
Hypothesis HVA : aval_mem (rdW W mem) (W0 + 16) 8 arr.
Hypothesis HARR : 0 <= arr < 2 ^ 64.
Hypothesis HARR8 : arr mod 8 = 0.
Hypothesis HPERM : Permutation (ablocks B ly S) (O ++ rest).
Hypothesis HAB : in_blockA rest arr (8 * Z.of_nat (length ws)).
Hypothesis HWS : forall k, (k < length ws)%nat ->
  aval_mem (rdW W mem) (arr + 8 * Z.of_nat k) 8 (nth k wp 0) /\ 0 <= nth k wp 0 < 2 ^ 64 /\
  in_blockA (ablocks B ly S) (nth k wp 0) (Z.of_nat (length (nth k ws [])) + 1) /\
  astr_atR (rdW W mem) (nth k wp 0) (nth k ws []).
Hypothesis HNEED : PJoinR.join_need ws + 1 <= LMAX + 2.
Hypothesis HREP : rec_repA B ly S (rdW W mem) R O.
Hypothesis HNC : (length (r_calls R) <= 2)%nat.
Hypothesis HDECL : r_refuse R <> 0 -> declared (r_code R) = true.
Hypothesis HREPLY : PCrt.acted_m R q = true -> exists X, r_reply R = Some (X ++ [Z_to_bv 8 0]) /\ no0 X.
Hypothesis HQ : 0 <= q < 2 ^ 32.
Hypothesis HVQ : aval_mem (rdW W mem) A_G_QUITTING 4 q.
Hypothesis HRT : rt_okA R q sb hb ws.
Hypothesis HEV : st_nev S + EV_CHECK_ROUND_TRIP R ws <= EV_MAX.
Hypothesis HLIVE : blocks_bytes S + LIVE_CHECK_ROUND_TRIP <= LIVE_MAX.
Hypothesis MOK : mo_ok MT S (XM_CHECK_ROUND_TRIP MT R ws).

#[local] Notation sp0 := (spZ regs).
#[local] Notation STK := CHECK_ROUND_TRIP_STK.
Definition crt_FP : list (Z * Z) := ablocks_fp O ++ cmd_PG.
(* the realigned stack pointer, s1 at every point after the prologue *)
Definition crt_sp1 : Z := 32 * ((sp0 - 256) / 32).
(* the class-5 side-stack frame, its flag word and its shadow *)
Definition crt_F (pos : Z) : Z := frame_addr ly 5 pos.
Definition crt_FL (pos : Z) : Z := flag_addr ly 5 pos.
Definition crt_SH (pos : Z) : Z := SHADOW_OFF + crt_F pos / 8.
Definition crt_Q : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (O' : list (Z * Z)),
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 r_calls R' = r_calls R /\ r_reply R' = r_reply R /\
 r_refuse R' = r_refuse R /\ r_code R' = r_code R /\ r_spill R' = r_spill R /\
 r_state R' = r_state R /\ r_host R' = r_host R /\
 aval_mem (rdW W' mem') A_G_QUITTING 4 q /\
 Permutation (ablocks B ly' S') (O' ++ rest) /\
 (forall p n i, In (p, n) rest -> 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_CHECK_ROUND_TRIP /\
 mo_le MT S S' (XM_CHECK_ROUND_TRIP MT R ws).
Definition crt_post : world SEGS -> config -> Prop :=
apost_base SEGS B STK crt_FP regs ly S W mem md (EV_CHECK_ROUND_TRIP R ws) crt_Q.
(* the statement's post (pass 4): FP-existential, the post of the points before send_message's return *)
Definition crt_postF : world SEGS -> config -> Prop :=
apost_baseF SEGS B STK crt_FP regs ly S W mem md (EV_CHECK_ROUND_TRIP R ws) crt_Q.
Definition cfgP (pc : Z) (rX : bvmap 5 word) (mX : word -> option byte) (dX : Model) : config :=
mkCfg (mkst rX (Z_to_bv 64 (BASE + pc)) mX (seg_rom SEGS)) dX.
(* the configuration and apost_base at a given FP state: the point after send_message's return at the FP state fx1
   send_message returns (ST_Gx) *)
Definition cfgPx (f : YK11.FPState) (pc : Z) (rX : bvmap 5 word) (mX : word -> option byte) (dX : Model) : config :=
mkCfg (@mkst f rX (Z_to_bv 64 (BASE + pc)) mX (seg_rom SEGS)) dX.
Definition crt_postx (f : YK11.FPState) : world SEGS -> config -> Prop :=
apost_base (fx := f) SEGS B STK crt_FP regs ly S W mem md (EV_CHECK_ROUND_TRIP R ws) crt_Q.
(* the 13 saved registers, in the prologue's frame *)
Definition crt_frame (rd : reader) : Prop :=
forall j r, nth_error crt_saved j = Some r ->
  aval_mem rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r)))).
(* the entry's image bytes (outside what the runtime owns and the errno cell), and the entry's live blocks *)
Definition crt_KI (Wc : world SEGS) (mc : word -> option byte) : Prop :=
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  rdW Wc mc a = rdW W mem a.
Definition crt_KB (Wc : world SEGS) (mc : word -> option byte) : Prop :=
forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < n -> rdW Wc mc (p + i) = rdW W mem (p + i).

Definition crt_J (pos : Z) lyc Sc (Wc : world SEGS) mc dc (k : Z) : Prop :=
 ajournal SEGS B STK sp0 crt_FP ly S W mem md [(5, pos)] lyc Sc Wc mc dc k.
(* the frame of the prologue, the class-5 frame's flag word, and its addressable middle (shadow +4 .. +115) *)
Definition crt_fr (pos : Z) (Wc : world SEGS) (mc : word -> option byte) : Prop :=
 crt_frame (rdW Wc mc) /\
 rdword (rdW Wc mc) (crt_F pos + fs_frame_bytes 5 - 8) = Some (crt_FL pos) /\
 (forall i, 4 <= i < 116 -> rdW Wc mc (crt_SH pos + i) = Some 0).
Definition crt_regs (rX : bvmap 5 word) (L : list (Z * Z)) : Prop :=
 Forall (fun rv => getr rX (Z_to_bv 5 (fst rv)) = w64 (snd rv)) L.
(* the 8-byte slots of the realigned frame at s1 + o *)
Definition crt_slots (Wc : world SEGS) (mc : word -> option byte) (L : list (Z * Z)) : Prop :=
 Forall (fun ov => aval_mem (rdW Wc mc) (crt_sp1 + fst ov) 8 (snd ov)) L.
Definition crt_shx (a : Z) : Z := SHADOW_OFF + a / 8.
(* lw's sign extension of a 32-bit value, as a 64-bit unsigned value *)
Definition crt_sx (v : Z) : Z := bv_swrap 32 v mod 2 ^ 64.
Definition crt_nC : Z := Z.of_nat (length (r_calls R)).
Definition crt_R1 : rstate := set_host (set_state R sb) hb.
Definition crt_D : list byte := join_sp ws.
Definition crt_jn : Z := PJoinR.join_need ws + 1.
(* the copies rec_calls_copy made in first[] (s2 + 32 = F + 32): one entry per recorded call, each argument in a fresh
   block of |s| + 1 bytes (rec_calls_copy_c.v's post) *)
Definition crt_tbl (pos : Z) lyc Sc (Wc : world SEGS) mc (qs : list (list (Z * Z))) : Prop :=
 length qs = length (r_calls R) /\ NoDup (map fst (concat qs)) /\
 (forall i c P, nth_error (r_calls R) i = Some c -> nth_error qs i = Some P ->
   acall_at (ablocks B lyc Sc) (rdW Wc mc) (crt_F pos + 32 + CALL_SIZE * Z.of_nat i) c P /\
   forall a s pn, nth_error (snd c) a = Some s -> nth_error P a = Some pn -> snd pn = Z.of_nat (length s) + 1) /\
 (forall pn q0, In pn (concat qs) -> In q0 (ablocks B ly S) -> iv_apart (fst pn) (snd pn) (fst q0) (snd q0)).
(* the recorder after the round trip, at the shared epilogue *)
Definition crt_QF lyc Sc (Wc : world SEGS) mc (Rf : rstate) (Of : list (Z * Z)) : Prop :=
 rec_repA B lyc Sc (rdW Wc mc) Rf Of /\
 r_calls Rf = r_calls R /\ r_reply Rf = r_reply R /\ r_refuse Rf = r_refuse R /\ r_code Rf = r_code R /\
 r_spill Rf = r_spill R /\ r_state Rf = r_state R /\ r_host Rf = r_host R /\
 aval_mem (rdW Wc mc) A_G_QUITTING 4 q /\
 Permutation (ablocks B lyc Sc) (Of ++ rest) /\
 blocks_bytes Sc <= blocks_bytes S + LIVE_CHECK_ROUND_TRIP /\
 mo_le MT S Sc (XM_CHECK_ROUND_TRIP MT R ws).
(* the prologue's frame, kept by a step that leaves [sp0 - 104, sp0) *)
Lemma crt_frame_keep : forall (rd rd' : reader), (forall a, sp0 - 104 <= a < sp0 -> rd' a = rd a) ->
  crt_frame rd -> crt_frame rd'.
Proof.
intros rd rd' K HF j r Hj.
assert (Hj13 : (j < 13)%nat) by (rewrite <- crt_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
apply (crt_aval_kept rd); [|exact (HF j r Hj)]. intros kk Hkk. apply K. lia.
Qed.

(* ---------- helpers on the points and the footprint, shared by the segments ---------- *)
(* a register of a point's list, by its numeral or through any name of the register; a slot of a point's list *)
Lemma crt_reg : forall rX L r v, crt_regs rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma crt_rg : forall rX L n v (r : bv 5), crt_regs rX L -> In (n, v) L -> bv_unsigned r = n -> getr rX r = w64 v.
Proof. intros rX L n v r H Hin Hr. exact (crt_reg_bv rX n r _ Hr (crt_reg rX L n v H Hin)). Qed.
Lemma crt_slot : forall (Wc : world SEGS) mc L o v, crt_slots Wc mc L -> In (o, v) L -> aval_mem (rdW Wc mc) (crt_sp1 + o) 8 v.
Proof. intros Wc mc L o v H Hin. exact (proj1 (Forall_forall _ _) H (o, v) Hin). Qed.
(* a call that preserves the callee-saved registers keeps a list of them *)
Lemma crt_regs_pres : forall r1 r2 L, aregs_preserved r1 r2 -> Forall (fun rv => acallee_saved (fst rv)) L ->
  crt_regs r1 L -> crt_regs r2 L.
Proof.
intros r1 r2 L HP HC H. unfold crt_regs in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HP _ (HC rv Hin)). exact (H rv Hin).
Qed.
(* the class-5 frame of the journal: it does not move with the layout, it is live, and it is bounded *)
Lemma crt_JF : forall pos lyc Sc (Wc : world SEGS) mc dc k, crt_J pos lyc Sc Wc mc dc k ->
 frame_addr lyc 5 pos = crt_F pos /\ flag_addr lyc 5 pos = crt_FL pos /\ In (5, pos) (frames Sc) /\
 4096 <= crt_F pos /\ crt_F pos + 2048 <= alloc_ceiling.
Proof.
intros pos lyc Sc Wc mc dc k HJ. unfold crt_J in HJ.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
destruct Hly as (_ & _ & _ & _ & _ & EFF & _).
assert (EF : frame_addr lyc 5 pos = crt_F pos) by (unfold crt_F, frame_addr; rewrite EFF; reflexivity).
assert (EL : flag_addr lyc 5 pos = crt_FL pos) by (unfold crt_FL, flag_addr; rewrite EFF; reflexivity).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc mc dc 5 pos HAR Hin) as (H1 & H2 & _).
rewrite EF in H1, H2. replace (fs_frame_bytes 5) with 2048 in H2 by (vm_compute; reflexivity).
split; [exact EF|]. split; [exact EL|]. split; [exact Hin|]. split; [exact H1 | exact H2].
Qed.
(* the walk's footprint: the recorder's blocks of O and the record's statics, all below alloc_ceiling and outside the
   read-only range, so the read-only bytes hold at every point of the walk *)
Lemma crt_O_live : forall pn, In pn O -> In pn (ablocks B ly S).
Proof. intros pn H. eapply Permutation_in; [apply Permutation_sym; exact HPERM | apply in_or_app; left; exact H]. Qed.
Lemma crt_fp_cases : forall a, inFP crt_FP a ->
  (exists p n, In (p, n) O /\ p <= a < p + req_size n) \/ (inFP cmd_PG a /\ a < 0x5e3c64).
Proof.
intros a (r & Hr & Ha). unfold crt_FP in Hr. apply in_app_or in Hr as [Hr | Hr].
- left. apply inFP_ablocks_fp_inv. exists r. split; [exact Hr | exact Ha].
- right. split; [exists r; split; [exact Hr | exact Ha]|].
  unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.
Lemma crt_fp_low : forall a, inFP crt_FP a -> a < alloc_ceiling.
Proof.
intros a Hf. pose proof HPRE as (HAR & _). pose proof asan_consts as (C1 & _).
destruct (crt_fp_cases a Hf) as [(p & n & Hin & Hr) | (_ & Hr)]; [|lia].
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (crt_O_live _ Hin)) as (_ & _ & Hc & _). lia.
Qed.
Lemma crt_ro_fp : forall a, in_roP SEGS CMD_RLO CMD_RHI a -> ~ inFP crt_FP a.
Proof.
intros a Hro Hf. pose proof HPRE as (HAR & _).
destruct (crt_fp_cases a Hf) as [(p & n & Hin & Hr) | (Hpg & _)].
- apply (blk_img SEGS B LAWS ly S W mem md p n a HAR (crt_O_live _ Hin) Hr).
  destruct Hro as [(s & Hs & _ & Hr') | Hg]; [exists s; split; [exact Hs | exact Hr'] | exact (RRO a Hg)].
- exact (RPG a Hpg Hro).
Qed.
Lemma crt_rod : forall own lyc Sc Wc mc dc k, ajournal SEGS B STK sp0 crt_FP ly S W mem md own lyc Sc Wc mc dc k ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW Wc mc).
Proof.
intros own lyc Sc Wc mc dc k HJ.
exact (arodata_ok_journalP SEGS CMD_RLO CMD_RHI RRO B STK sp0 crt_FP ly S W mem md own lyc Sc Wc mc dc k HJ crt_ro_fp HROD).
Qed.

(* ---------- the entry state's facts ---------- *)
Lemma crt_STK : STK = 17376. Proof. reflexivity. Qed.
Lemma crt_sp0 : alloc_ceiling + 17376 <= sp0 /\ sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0 /\ sp0 <= ly_top ly /\ ly_top ly <= ly_stk_hi ly.
Proof.
destruct HPRE as (_ & _ & _ & _ & _ & (Hal & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2) & _).
rewrite crt_STK in Hslo. lia.
Qed.
Lemma crt_sp1_bounds : sp0 - 272 <= crt_sp1 <= sp0 - 256 /\ crt_sp1 mod 32 = 0 /\ crt_sp1 mod 16 = 0 /\
  (crt_sp1 - sp0) mod 16 = 0.
Proof.
pose proof crt_sp0 as (S1 & S2 & S3 & _). pose proof asan_consts as (C1 & _).
destruct (crt_sp1_facts (sp0 - 256) ltac:(lia) ltac:(rewrite Zminus_mod, S3; reflexivity)) as (A1 & A2 & A3).
unfold crt_sp1. split; [lia|]. split; [exact A2|]. split; [exact A3|].
rewrite Zminus_mod, A3, S3. reflexivity.
Qed.
(* the frame chain at a call (pass 5): s0 = sp0, the frame pointer. Its first record is the prologue's (ra at sp0 - 8,
   the entry s0 at sp0 - 16: crt_frame), on top of afn_pre's chain from the entry s0, which the walk keeps (it writes
   nothing above sp0 outside its footprint); achain_push (YCbq.v), or the empty chain when sp0 is within 16 bytes of
   the stack top *)
Lemma crt_chain : forall pos lyc Sc (Wc : world SEGS) mc dc k, crt_J pos lyc Sc Wc mc dc k -> crt_frame (rdW Wc mc) ->
  exists ch1, achain lyc (rdW Wc mc) crt_sp1 sp0 ch1.
Proof.
intros pos lyc Sc Wc mc dc k HJ HF.
pose proof HPRE as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _). pose proof Hstk as (_ & _ & _ & _ & _ & H47 & _).
pose proof crt_sp0 as (S1 & S2 & S3 & S4 & S5). pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4).
pose proof asan_consts as (C1 & _).
unfold crt_J in HJ. pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (Z_lt_le_dec sp0 (ly_top ly - 16)) as [Hlt | Hge].
- exists ((sp0, raZ regs, s0Z regs) :: ch). apply (achain_ly_top ly lyc); [exact Etop|].
  apply (achain_push ly (rdW W mem) (rdW Wc mc) sp0 (s0Z regs) (raZ regs) ch crt_sp1 Hch).
  + lia.
  + intros a Ha. apply F1; [lia | lia | intros Hf; pose proof (crt_fp_low a Hf); lia].
  + apply (rdword_of_val_mem SEGS); [|unfold raZ; apply u64_range]. apply crt_val_of_aval.
    assert (E1 : Z_to_bv 5 (Z.of_nat 1) = (1%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HF 0%nat 1%nat eq_refl) as H1. rewrite E1 in H1.
    replace (sp0 - 8) with (sp0 - 8 - 8 * Z.of_nat 0) by lia. exact H1.
  + apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply u64_range]. apply crt_val_of_aval.
    assert (E8 : Z_to_bv 5 (Z.of_nat 8) = (8%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HF 1%nat 8%nat eq_refl) as H8. rewrite E8 in H8.
    replace (sp0 - 16) with (sp0 - 8 - 8 * Z.of_nat 1) by lia. exact H8.
  + exact Hra4.
  + lia.
  + pose proof (Z.div_mod sp0 16 ltac:(lia)) as D16. rewrite S3, Z.add_0_r in D16. rewrite D16.
    replace (16 * (sp0 / 16)) with (2 * (sp0 / 16) * 8) by lia. apply Z_mod_mult.
  + exact Hlt.
  + lia.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.
Definition crt_EE : env := Eimg (Ereg regs [w64 SB; w64 (as_uar_cell B)]).
Lemma crt_EE_reg : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew crt_EE n = getr regs r.
Proof. intros n r Hn. unfold crt_EE. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma crt_entry_seed :
 st_ok_pi SEGS VAL crt_EE crt_ssE (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_round_trip)) mem (seg_rom SEGS))).
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof crt_sp0 as (S1 & S2 & S3 & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := crt_EE).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (subst E; rewrite (crt_EE_reg 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 SB) by (subst E; unfold crt_EE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (as_uar_cell B)) by (subst E; unfold crt_EE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 1)) as R1. pose proof (pa_val_range (A_OBJ 12)) as R12.
pose proof (palf_uar_img B TLF) as [HU1 HU2]. pose proof (palf_uar_al B TLF) as HU4.
assert (U241 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite E241; apply unsigned_lit_small; lia).
assert (U242 : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1)) by (rewrite E242; apply unsigned_lit_small; lia).
assert (U253 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (rewrite E253; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = as_uar_cell B) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 1 ltac:(lia)) as HuarR.
pose proof (palf_sep B TLF) as HSEP. unfold zseps, zseps_from in HSEP. cbn [fst snd] in HSEP.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & Kuar & Kgot & Kgu).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kgu.
rewrite restrict_mkst_fx. unfold crt_ssE. apply pa_entry_st_ok_full.
- subst E. unfold crt_EE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite crt_STK. lia.
  + rewrite U241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite U253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
      | unfold SB; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite U242. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
      | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgu).
  + rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS _ _ _ _ Kuar).
- apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U241, U253, U242, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat split; try lia; exact S3.
Qed.
(* a run whose only write window is the prologue's frame keeps every other byte *)
Lemma crt_frame_stk : forall E rs H (m m' : word -> option byte), frame_of E rs (mrestrict H m) (mrestrict H m') ->
 bv_unsigned (ew E 2) = sp0 ->
 (forall b wlo whi, In (b, wlo, whi) (windows rs) -> whi <= wlo \/ (b = Some 2%nat /\ wlo = -256 /\ whi = 0)) ->
 forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 256 <= a < sp0) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hsp Hw a Ha Hn. apply (kept_of_frame E rs H m m' (fun a => sp0 - 256 <= a < sp0) HF); [|exact Ha | exact Hn].
intros b wlo whi a' Hin Hr. destruct (Hw b wlo whi Hin) as [Hl | (-> & -> & ->)]; [lia|].
cbn [base_val] in Hr. rewrite Hsp in Hr. lia.
Qed.
(* the frame the prologue stores: the 13 saved registers at sp0 - 8 .. sp0 - 104 *)
Lemma crt_entry_frame : forall H (m2 : word -> option byte) cs,
 region_ok SEGS crt_EE (mrestrict H m2) (YP09.mkRegion (Some 2%nat) (-256) 0 (-256) 0 cs) ->
 (forall j r, nth_error crt_saved j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff r 0))) cs) ->
 crt_frame (aview SEGS H m2).
Proof.
intros H m2 cs HR Hs.
assert (Usp : bv_unsigned (ew crt_EE 2) = sp0) by (rewrite (crt_EE_reg 2 2%bv eq_refl); reflexivity).
intros j r Hj. assert (Hr27 : (r <= 27)%nat) by (apply nth_error_In in Hj; cbn in Hj; intuition lia).
assert (Hj13 : (j < 13)%nat) by (rewrite <- crt_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
apply crt_aval_of_val. replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia.
change 8%nat with (N.to_nat 8).
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (Z.of_nat r)))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
apply (field_of_region crt_EE _ 2 sp0 cs (-256) 0 (-256) 0 _ 8 (SOff r 0) _ HR Usp (Hs j r Hj)).
+ rewrite crt_den_atom0, (crt_EE_reg r (Z_to_bv 5 (Z.of_nat r))); [rewrite Z_to_bv_bv_unsigned; reflexivity|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity.
+ cbn. lia.
+ cbn. lia.
Qed.
Ltac crt_winstk := let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let Hin := fresh "Hin" in
  intros b wlo whi Hin; vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; first [left; lia | right; auto] |]); destruct Hin.
Ltac crt_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac crt_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.
Ltac clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.

(* ---------- after the side-stack frame (0x88050) ---------- *)
Definition ST_B : Prop := forall Sc mc dc rB pos,
 ajournal SEGS B STK sp0 crt_FP ly S W mem md [(5, pos)] ly Sc W mc dc 0 ->
 frames Sc = (5, pos) :: frames S -> ~ In (5, pos) (frames S) ->
 ablocks B ly Sc = ablocks B ly S -> st_nev Sc = st_nev S -> blocks_bytes Sc = blocks_bytes S -> mo_le MT S Sc 0 ->
 zero_shadow (rdW W mc) SHADOW_OFF (crt_F pos) (fs_frame_bytes 5) ->
 rdword (rdW W mc) (crt_F pos + fs_frame_bytes 5 - 8) = Some (crt_FL pos) ->
 crt_frame (rdW W mc) -> crt_KI W mc -> crt_KB W mc ->
 getr rB 2 = w64 crt_sp1 -> getr rB 9 = w64 crt_sp1 -> getr rB 8 = w64 sp0 ->
 getr rB 3 = w64 (as_gp B) -> getr rB 4 = w64 (as_tp B) ->
 getr rB 10 = w64 (crt_F pos) -> getr rB 22 = w64 W0 -> getr rB 23 = w64 hb -> getr rB 24 = w64 sb ->
 getr rB 27 = w64 SHADOW_OFF ->
 SRr SEGS W (cfgP 7020 rB mc dc) crt_postF.

(* ---------- the entry (0x87fd8 .. 0x8804c): the prologue, the realignment, the use-after-return flag (set: the
   record pins it, AR_const_law), the class-5 frame from __asan_stack_malloc_5 ---------- *)
Lemma crt_s0 : ST_B -> SRr SEGS W (cfg_at SEGS (BASE + AF_check_round_trip) regs mem md) crt_postF.
Proof.
intros HSTB.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof crt_sp0 as (S1 & S2 & S3 & S4 & S5). pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof crt_entry_seed as HS.
pose proof (ajournal_init SEGS B STK crt_FP ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM crt_EE) by (unfold crt_EE; apply Eimg_env).
assert (Usp : bv_unsigned (ew crt_EE 2) = sp0) by (rewrite (crt_EE_reg 2 2%bv eq_refl); reflexivity).
assert (E2 : ew crt_EE 2 = Z_to_bv 64 sp0) by (rewrite (crt_EE_reg 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E32 : ew crt_EE 32 = Z_to_bv 64 SB) by (unfold crt_EE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] crt_EE (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
unfold cfg_at. change (w64 (BASE + AF_check_round_trip)) with (Z_to_bv 64 (BASE + AF_check_round_trip)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
pose proof (crt_frame_stk _ _ _ _ _ HFr Usp ltac:(crt_winstk)) as K0. clear HF HFr HG. clear_md.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg end.
cbn [ms_mem restrict] in HRg.
assert (HFR0 : crt_frame (rdW W (ms_mem ms))).
{ apply (crt_entry_frame _ _ _ HRg).
  intros j r Hr. do 13 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]).
  cbn in Hr. destruct j; discriminate Hr. }
clear HRg.
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 7020)) by (crt_rreg HS; apply (codeptr_val _ 7020 HEI)).
assert (R2 : getr (ms_regs ms) 2 = w64 crt_sp1)
  by (crt_rreg HS; unfold crt_sp1, w64; apply (crt_denot_and_m32 crt_EE 2 sp0 (-256) E2); lia).
assert (R9 : getr (ms_regs ms) 9 = w64 crt_sp1)
  by (crt_rreg HS; unfold crt_sp1, w64; apply (crt_denot_and_m32_add0 crt_EE 2 sp0 (-256) E2); lia).
assert (R8 : getr (ms_regs ms) 8 = w64 sp0) by (crt_rreg HS; rewrite crt_den_atom0, E2; reflexivity).
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (crt_rreg HS; rewrite crt_den_atom0, (crt_EE_reg 3 3%bv eq_refl); exact Hgp).
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (crt_rreg HS; rewrite crt_den_atom0, (crt_EE_reg 4 4%bv eq_refl); exact Htp).
assert (R22 : getr (ms_regs ms) 22 = w64 W0) by (crt_rreg HS; rewrite crt_den_atom0, (crt_EE_reg 10 10%bv eq_refl); exact H10).
assert (R23 : getr (ms_regs ms) 23 = w64 hb) by (crt_rreg HS; rewrite crt_den_atom0, (crt_EE_reg 12 12%bv eq_refl); exact H12).
assert (R24 : getr (ms_regs ms) 24 = w64 sb) by (crt_rreg HS; rewrite crt_den_atom0, (crt_EE_reg 11 11%bv eq_refl); exact H11).
assert (R27 : getr (ms_regs ms) 27 = w64 SHADOW_OFF) by (crt_rreg HS; rewrite crt_den_atom0, E32; reflexivity).
pmkst HS.
change (SIG CS___asan_stack_malloc_5) with (pa_sigma (cs_stack_malloc 5)).
rewrite (palf_sm B TLF 5 ltac:(cbn; tauto)).
eapply SRr_bind.
{ apply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low errno_low ML SMP 5 (ASM5 fx) ltac:(lia) W (ms_regs ms) (ms_mem ms) STK sp0 crt_FP
    ly S W mem md [] ly S _ 0 (crt_sp1 - sp0) (Z_to_bv 64 (BASE + 7020)) HJ).
  - unfold spZ at 1. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact P4.
  - lia.
  - unfold ESTACK. rewrite crt_STK. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HCNT. }
cbv beta. intros W2 c2 _ (-> & S2' & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & _ & (f & ES2)).
replace (sp0 + (crt_sp1 - sp0)) with crt_sp1 in HK by lia.
destruct HK as (K1 & K2 & K3 & K4 & _).
apply (HSTB S2' mem2 md2 regs2 pos).
- exact HJ2.
- exact Hfrs2.
- exact Hnin.
- exact Eab.
- exact Hnev2.
- exact Hbb2.
- rewrite ES2. apply (mo_le_set_fs_r MT MTFL). apply (mo_le_refl MT MTL).
- exact Hz.
- exact Hflag.
- intros j r Hj. assert (Hj13 : (j < 13)%nat) by (rewrite <- crt_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
  apply (crt_aval_kept (rdW W (ms_mem ms))); [|exact (HFR0 j r Hj)].
  intros kk Hkk. apply K1; [lia | unfold ESTACK; lia].
- intros a Hi Ho He. rewrite (K3 a Hi Ho He). pose proof (pa_img_range a Hi) as HIa. apply K0; lia.
- intros p n i Hin Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
  pose proof (req_size_pos n (proj1 Hm)) as [Hq1 Hq2].
  rewrite (K2 p n i Hin ltac:(lia) ltac:(tauto)). apply K0; lia.
- rewrite (crt_preg _ _ 2%bv HP2) by crt_cs. exact R2.
- rewrite (crt_preg _ _ 9%bv HP2) by crt_cs. exact R9.
- rewrite (crt_preg _ _ 8%bv HP2) by crt_cs. exact R8.
- rewrite (crt_preg _ _ 3%bv HP2) by crt_cs. exact R3.
- rewrite (crt_preg _ _ 4%bv HP2) by crt_cs. exact R4.
- exact Ha0.
- rewrite (crt_preg _ _ 22%bv HP2) by crt_cs. exact R22.
- rewrite (crt_preg _ _ 23%bv HP2) by crt_cs. exact R23.
- rewrite (crt_preg _ _ 24%bv HP2) by crt_cs. exact R24.
- rewrite (crt_preg _ _ 27%bv HP2) by crt_cs. exact R27.
Qed.

(* ---------- the points between two calls: each is the statement the walk from that point proves ---------- *)
Definition crt_RC (pos : Z) : list (Z * Z) :=
 [(2, crt_sp1); (9, crt_sp1); (8, sp0); (3, as_gp B); (4, as_tp B); (18, crt_F pos); (19, crt_SH pos);
  (20, crt_F pos); (21, crt_SH pos + 4); (22, W0); (23, hb); (24, sb); (27, SHADOW_OFF)].
(* after __asan_set_shadow_f8 (0x880d4) *)
Definition ST_B2 : Prop := forall Sc mc dc rX pos,
 crt_J pos ly Sc W mc dc 0 ->
 ablocks B ly Sc = ablocks B ly S -> st_nev Sc = st_nev S -> blocks_bytes Sc = blocks_bytes S -> mo_le MT S Sc 0 ->
 crt_frame (rdW W mc) -> rdword (rdW W mc) (crt_F pos + fs_frame_bytes 5 - 8) = Some (crt_FL pos) ->
 crt_KI W mc -> crt_KB W mc -> crt_regs rX (crt_RC pos) ->
 SRr SEGS W (cfgP 7152 rX mc dc) crt_postF.
(* after __asan_set_shadow_00 (0x88124): the frame's shadow laid *)
Definition ST_C : Prop := forall Sc mc dc rX pos,
 crt_J pos ly Sc W mc dc 0 ->
 ablocks B ly Sc = ablocks B ly S -> st_nev Sc = st_nev S -> blocks_bytes Sc = blocks_bytes S -> mo_le MT S Sc 0 ->
 crt_fr pos W mc -> crt_KI W mc -> crt_KB W mc -> crt_regs rX (crt_RC pos) ->
 SRr SEGS W (cfgP 7232 rX mc dc) crt_postF.
(* after rec_calls_copy (0x88198) *)
Definition crt_RD (pos : Z) : list (Z * Z) :=
 [(2, crt_sp1); (9, crt_sp1); (8, sp0); (3, as_gp B); (4, as_tp B); (10, crt_nC); (18, crt_F pos); (19, crt_SH pos);
  (20, crt_F pos); (21, crt_SH pos + 4); (23, hb); (25, A_G_QUITTING); (26, crt_shx A_G_QUITTING); (27, SHADOW_OFF)].
Definition ST_D : Prop := forall lyc Sc Wc mc dc rX pos qs,
 crt_J pos lyc Sc Wc mc dc (EV_REC_CALLS_COPY R) ->
 crt_fr pos Wc mc -> crt_tbl pos lyc Sc Wc mc qs ->
 Permutation (ablocks B lyc Sc) (ablocks B ly S ++ concat qs) ->
 rec_repA B lyc Sc (rdW Wc mc) R O -> aval_mem (rdW Wc mc) A_G_QUITTING 4 q ->
 crt_KI Wc mc -> crt_KB Wc mc ->
 blocks_bytes Sc <= blocks_bytes S + LIVE_REC_CALLS_COPY R -> mo_le MT S Sc (XM_REC_CALLS_COPY MT R) ->
 ws <> [] -> PCrt.acted_m R q = true ->
 crt_slots Wc mc [(104, crt_F pos + 32); (112, sb); (120, W0)] ->
 crt_regs rX (crt_RD pos) ->
 SRr SEGS Wc (cfgP 7348 rX mc dc) crt_postF.
(* after the strdup wrapper (0x88224) *)
Definition crt_RE (pos res : Z) : list (Z * Z) :=
 [(2, crt_sp1); (9, crt_sp1); (8, sp0); (3, as_gp B); (4, as_tp B); (10, res); (18, crt_F pos);
  (20, crt_shx (A_G_REC + 928)); (22, hb); (23, crt_shx (A_G_REC + 952)); (24, A_G_REC); (25, A_G_QUITTING);
  (26, crt_shx (A_G_REC + 944)); (27, SHADOW_OFF)].
Definition crt_SLE (pos : Z) : list (Z * Z) :=
 [(104, crt_F pos + 32); (112, sb); (120, W0); (96, crt_nC); (88, crt_shx A_G_QUITTING); (80, crt_sx q);
  (72, r_state R); (64, r_host R); (56, crt_F pos); (48, crt_SH pos + 4)].
Definition ST_E : Prop := forall lyc Sc Wc mc dc rX pos qs res (X : list byte),
 crt_J pos lyc Sc Wc mc dc (EV_REC_CALLS_COPY R + 1) ->
 crt_fr pos Wc mc -> crt_tbl pos lyc Sc Wc mc qs ->
 Permutation (ablocks B lyc Sc) (ablocks B ly S ++ concat qs ++ [(res, Z.of_nat (length X) + 1)]) ->
 rec_repA B lyc Sc (rdW Wc mc) R O -> aval_mem (rdW Wc mc) A_G_QUITTING 4 q ->
 crt_KI Wc mc -> crt_KB Wc mc ->
 r_reply R = Some (X ++ [Z_to_bv 8 0]) -> no0 X ->
 abytes_atR (rdW Wc mc) res (X ++ [Z_to_bv 8 0]) -> 4096 <= res ->
 blocks_bytes Sc <= blocks_bytes S + LIVE_REC_CALLS_COPY R + (Z.of_nat (length X) + 1) ->
 mo_le MT S Sc (XM_REC_CALLS_COPY MT R + mo_malloc MT (Z.of_nat (length X) + 1)) ->
 ws <> [] -> PCrt.acted_m R q = true ->
 crt_slots Wc mc (crt_SLE pos) -> crt_regs rX (crt_RE pos res) ->
 SRr SEGS Wc (cfgP 7488 rX mc dc) crt_postF.
(* after joined (0x88254) *)
Definition crt_RF (pos res line : Z) : list (Z * Z) :=
 [(2, crt_sp1); (9, crt_sp1); (8, sp0); (3, as_gp B); (4, as_tp B); (10, line); (18, crt_F pos);
  (20, crt_shx (A_G_REC + 928)); (21, res); (23, crt_shx (A_G_REC + 952)); (24, A_G_REC); (25, A_G_QUITTING);
  (26, crt_shx (A_G_REC + 944)); (27, SHADOW_OFF)].
Definition crt_SLF (pos : Z) : list (Z * Z) := (144, Z.of_nat (length crt_D)) :: crt_SLE pos.
Definition ST_F : Prop := forall lyc Sc Wc mc dc rX pos qs res (X : list byte) line,
 crt_J pos lyc Sc Wc mc dc (EV_REC_CALLS_COPY R + 1 + EV_JOINED) ->
 crt_fr pos Wc mc -> crt_tbl pos lyc Sc Wc mc qs ->
 Permutation (ablocks B lyc Sc) (O ++ rest ++ concat qs ++ [(res, Z.of_nat (length X) + 1); (line, crt_jn)]) ->
 rec_repA B lyc Sc (rdW Wc mc) crt_R1 O ->
 aval_mem (rdW Wc mc) A_G_QUITTING 4 q ->
 r_reply R = Some (X ++ [Z_to_bv 8 0]) -> no0 X ->
 abytes_atR (rdW Wc mc) res (X ++ [Z_to_bv 8 0]) -> 4096 <= res ->
 abytes_atR (rdW Wc mc) line (crt_D ++ [Z_to_bv 8 0]) -> 4096 <= line ->
 blocks_bytes Sc <= blocks_bytes S + LIVE_REC_CALLS_COPY R + (Z.of_nat (length X) + 1) + LIVE_JOINED ->
 mo_le MT S Sc (XM_REC_CALLS_COPY MT R + mo_malloc MT (Z.of_nat (length X) + 1) + XM_JOINED MT ws) ->
 ws <> [] -> PCrt.acted_m R q = true ->
 crt_slots Wc mc (crt_SLF pos) -> crt_regs rX (crt_RF pos res line) ->
 SRr SEGS Wc (cfgP 7536 rX mc dc) crt_postF.
(* the meter and the events spent up to send_message's return *)
Definition crt_EVG : Z := EV_REC_CALLS_COPY R + 1 + EV_JOINED + EV_SEND_MESSAGE R crt_D.
Definition crt_XMG : Z := XM_REC_CALLS_COPY MT R + mo_malloc MT (LMAX + 2) + XM_JOINED MT ws + XM_SEND_MESSAGE MT R crt_D.
(* the recorder after send_message: the round trip holds (rt_okA), and refuse / code / spill survive *)
Definition crt_R2ok (R2 : rstate) : Prop :=
 r_calls R2 = r_calls R /\ r_reply R2 = r_reply R /\ r_refuse R2 = r_refuse R /\ r_code R2 = r_code R /\
 r_spill R2 = r_spill R /\ r_state R2 = r_state R /\ r_host R2 = r_host R.
Definition crt_RG (pos res line : Z) : list (Z * Z) :=
 [(2, crt_sp1); (9, crt_sp1); (8, sp0); (3, as_gp B); (4, as_tp B); (18, crt_F pos);
  (20, crt_shx (A_G_REC + 928)); (21, res); (22, line); (23, crt_shx (A_G_REC + 952)); (24, A_G_REC); (25, A_G_QUITTING);
  (26, crt_shx (A_G_REC + 944)); (27, SHADOW_OFF)].
(* after send_message (0x88260) *)
Definition ST_G : Prop := forall lyc Sc Wc mc dc rX pos qs res (X : list byte) line R2 O2,
 crt_J pos lyc Sc Wc mc dc crt_EVG ->
 crt_fr pos Wc mc -> crt_tbl pos lyc Sc Wc mc qs ->
 Permutation (ablocks B lyc Sc) (O2 ++ rest ++ concat qs ++ [(res, Z.of_nat (length X) + 1); (line, crt_jn)]) ->
 rec_repA B lyc Sc (rdW Wc mc) R2 O2 -> crt_R2ok R2 ->
 aval_mem (rdW Wc mc) A_G_QUITTING 4 q ->
 r_reply R = Some (X ++ [Z_to_bv 8 0]) -> no0 X ->
 abytes_atR (rdW Wc mc) res (X ++ [Z_to_bv 8 0]) -> 4096 <= res -> 4096 <= line ->
 blocks_bytes Sc <= blocks_bytes S + LIVE_CHECK_ROUND_TRIP -> mo_le MT S Sc crt_XMG ->
 crt_slots Wc mc (crt_SLE pos) -> crt_regs rX (crt_RG pos res line) ->
 SRr SEGS Wc (cfgP 7548 rX mc dc) crt_post.
(* ST_G at a given FP state: send_message returns at some fx1 (crt_s6 takes ST_Gx at every fx1 fxrel to fx; after the
   sections close, crt_G is ST_G at fx1, which is ST_Gx fx1 by conversion) *)
Definition ST_Gx (f : YK11.FPState) : Prop := forall lyc Sc Wc mc dc rX pos qs res (X : list byte) line R2 O2,
 crt_J pos lyc Sc Wc mc dc crt_EVG ->
 crt_fr pos Wc mc -> crt_tbl pos lyc Sc Wc mc qs ->
 Permutation (ablocks B lyc Sc) (O2 ++ rest ++ concat qs ++ [(res, Z.of_nat (length X) + 1); (line, crt_jn)]) ->
 rec_repA B lyc Sc (rdW Wc mc) R2 O2 -> crt_R2ok R2 ->
 aval_mem (rdW Wc mc) A_G_QUITTING 4 q ->
 r_reply R = Some (X ++ [Z_to_bv 8 0]) -> no0 X ->
 abytes_atR (rdW Wc mc) res (X ++ [Z_to_bv 8 0]) -> 4096 <= res -> 4096 <= line ->
 blocks_bytes Sc <= blocks_bytes S + LIVE_CHECK_ROUND_TRIP -> mo_le MT S Sc crt_XMG ->
 crt_slots Wc mc (crt_SLE pos) -> crt_regs rX (crt_RG pos res line) ->
 SRr SEGS Wc (cfgPx f 7548 rX mc dc) (crt_postx f).
Definition crt_RH (pos res : Z) : list (Z * Z) :=
 [(2, crt_sp1); (9, crt_sp1); (8, sp0); (3, as_gp B); (4, as_tp B); (18, crt_F pos);
  (20, crt_shx (A_G_REC + 928)); (21, res); (23, crt_shx (A_G_REC + 952)); (24, A_G_REC); (25, A_G_QUITTING);
  (26, crt_shx (A_G_REC + 944)); (27, SHADOW_OFF)].
(* after free(line) (0x88268) *)
Definition ST_H : Prop := forall lyc Sc Wc mc dc rX pos qs res (X : list byte) R2 O2,
 crt_J pos lyc Sc Wc mc dc (crt_EVG + 1) ->
 crt_fr pos Wc mc -> crt_tbl pos lyc Sc Wc mc qs ->
 Permutation (ablocks B lyc Sc) (O2 ++ rest ++ concat qs ++ [(res, Z.of_nat (length X) + 1)]) ->
 rec_repA B lyc Sc (rdW Wc mc) R2 O2 -> crt_R2ok R2 ->
 aval_mem (rdW Wc mc) A_G_QUITTING 4 q ->
 r_reply R = Some (X ++ [Z_to_bv 8 0]) -> no0 X ->
 abytes_atR (rdW Wc mc) res (X ++ [Z_to_bv 8 0]) -> 4096 <= res ->
 blocks_bytes Sc <= blocks_bytes S + LIVE_CHECK_ROUND_TRIP -> mo_le MT S Sc (crt_XMG + mo_free MT) ->
 crt_slots Wc mc (crt_SLE pos) -> crt_regs rX (crt_RH pos res) ->
 SRr SEGS Wc (cfgP 7556 rX mc dc) crt_post.
Definition crt_RI (pos res a0 : Z) : list (Z * Z) :=
 [(2, crt_sp1); (9, crt_sp1); (8, sp0); (3, as_gp B); (4, as_tp B); (10, a0); (18, crt_F pos);
  (20, crt_shx (A_G_REC + 928)); (21, res); (22, crt_F pos + 32); (23, crt_shx (A_G_REC + 952)); (24, A_G_REC);
  (25, A_G_QUITTING); (26, crt_shx (A_G_REC + 944)); (27, crt_nC)].
(* after rec_calls_equal (0x88298): the copies equal the recorder's calls; after the strcmp wrapper (0x882b4): the
   reply equals its copy *)
Definition ST_I (pc a0 : Z) : Prop := forall lyc Sc Wc mc dc rX pos qs res (X : list byte) R2 O2,
 crt_J pos lyc Sc Wc mc dc (crt_EVG + 1) ->
 crt_fr pos Wc mc -> crt_tbl pos lyc Sc Wc mc qs ->
 Permutation (ablocks B lyc Sc) (O2 ++ rest ++ concat qs ++ [(res, Z.of_nat (length X) + 1)]) ->
 rec_repA B lyc Sc (rdW Wc mc) R2 O2 -> crt_R2ok R2 ->
 aval_mem (rdW Wc mc) A_G_QUITTING 4 q ->
 r_reply R = Some (X ++ [Z_to_bv 8 0]) -> no0 X ->
 abytes_atR (rdW Wc mc) res (X ++ [Z_to_bv 8 0]) -> 4096 <= res ->
 blocks_bytes Sc <= blocks_bytes S + LIVE_CHECK_ROUND_TRIP -> mo_le MT S Sc (crt_XMG + mo_free MT) ->
 crt_slots Wc mc (crt_SLE pos) -> crt_regs rX (crt_RI pos res a0) ->
 SRr SEGS Wc (cfgP pc rX mc dc) crt_post.
(* after rec_calls_free (0x88304): the copies freed *)
Definition ST_K : Prop := forall lyc Sc Wc mc dc rX pos res (X : list byte) R2 O2,
 crt_J pos lyc Sc Wc mc dc (crt_EVG + 1 + ev_args R) ->
 crt_fr pos Wc mc ->
 Permutation (ablocks B lyc Sc) (O2 ++ rest ++ [(res, Z.of_nat (length X) + 1)]) ->
 rec_repA B lyc Sc (rdW Wc mc) R2 O2 -> crt_R2ok R2 ->
 aval_mem (rdW Wc mc) A_G_QUITTING 4 q -> 4096 <= res ->
 blocks_bytes Sc <= blocks_bytes S + LIVE_CHECK_ROUND_TRIP ->
 mo_le MT S Sc (crt_XMG + mo_free MT + ev_args R * mo_free MT) ->
 crt_slots Wc mc [(56, crt_F pos); (48, crt_SH pos + 4)] ->
 crt_regs rX [(2, crt_sp1); (9, crt_sp1); (8, sp0); (3, as_gp B); (4, as_tp B); (18, crt_F pos); (21, res)] ->
 SRr SEGS Wc (cfgP 7712 rX mc dc) crt_post.
(* after free(reply_first) (0x8830c) *)
Definition ST_L : Prop := forall lyc Sc Wc mc dc rX pos R2 O2,
 crt_J pos lyc Sc Wc mc dc (EV_CHECK_ROUND_TRIP R ws) ->
 crt_fr pos Wc mc ->
 Permutation (ablocks B lyc Sc) (O2 ++ rest) ->
 rec_repA B lyc Sc (rdW Wc mc) R2 O2 -> crt_R2ok R2 ->
 aval_mem (rdW Wc mc) A_G_QUITTING 4 q ->
 blocks_bytes Sc <= blocks_bytes S + LIVE_CHECK_ROUND_TRIP -> mo_le MT S Sc (XM_CHECK_ROUND_TRIP MT R ws) ->
 crt_slots Wc mc [(56, crt_F pos); (48, crt_SH pos + 4)] ->
 crt_regs rX [(2, crt_sp1); (9, crt_sp1); (8, sp0); (3, as_gp B); (4, as_tp B); (18, crt_F pos)] ->
 SRr SEGS Wc (cfgP 7720 rX mc dc) crt_post.
(* the shared epilogue (0x88314): the skip path joins here *)
Definition ST_EPI : Prop := forall lyc Sc Wc mc dc rX pos k Rf Of,
 crt_J pos lyc Sc Wc mc dc k -> k <= EV_CHECK_ROUND_TRIP R ws ->
 crt_frame (rdW Wc mc) -> rdword (rdW Wc mc) (crt_F pos + fs_frame_bytes 5 - 8) = Some (crt_FL pos) ->
 crt_QF lyc Sc Wc mc Rf Of ->
 crt_regs rX [(2, crt_sp1); (8, sp0); (3, as_gp B); (4, as_tp B); (18, crt_F pos); (20, crt_F pos); (21, crt_SH pos + 4)] ->
 SRr SEGS Wc (cfgP 7728 rX mc dc) crt_post.

(* ---------- the segments ---------- *)
(* ---------- s1 (0x88050 .. the call of __asan_set_shadow_f8 at 0x880d0, return 0x880d4 = 7152): s4 = s2 = F; F at
   s1 + 136; the frame header F + 0 / 8 / 16; s3 = (F >> 3) + s11 = SH; the shadow f1 at SH + 0 .. 3; s5 = SH + 4; the
   fill of SH + 4 .. 115 with f8. The run has no inline check, so it is the plain executor's (RUNP / RUNC, as in
   xstrdup.v): the tokens' executor refuses a write window inside the shadow band. ---------- *)
(* atom 32 is SH: the alias rewrites s3 to it, so the four shadow stores go through a region on atom 32 *)
Definition crts1_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 27 0).
Definition crts1_ss : sstate := mkSS 7020 sr_atoms
  [YP09.mkRegion (Some 9%nat) 136 144 136 144 []; YP09.mkRegion (Some 10%nat) 0 24 0 24 [];
   YP09.mkRegion (Some 32%nat) 0 4 0 4 []] None
  (mkFacts [(10%nat, mkAF 4096 (2 ^ 47) 0)] [] [(crts1_shx, SOff 32 0)]).
(* every byte s1, s2 and their two shadow fills may write: the slot s1 + 136 and the 4096 bytes below s1 (the runtime
   entries' stack), the frame header, the frame's shadow *)
Definition crts1_Wr (pos a : Z) : Prop :=
  (crt_sp1 - 4096 <= a < crt_sp1 + 144) \/ (crt_F pos <= a < crt_F pos + 24) \/ (crt_SH pos <= a < crt_SH pos + 256).
Lemma crts1_RC_cs : forall pos, Forall (fun rv => acallee_saved (fst rv)) (crt_RC pos).
Proof. intros pos. unfold crt_RC. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. Qed.
(* the frame of class 5: its place, and its shadow between the two application ranges *)
Lemma crts1_geo : forall Sc mc dc pos, AR SEGS B ly Sc W mc dc -> In (5, pos) (frames Sc) ->
  4096 <= crt_F pos /\ crt_F pos + 2048 <= alloc_ceiling /\
  (crt_F pos + 2048 <= 0x7fff7000 \/ 0x10007fff8000 <= crt_F pos) /\
  0x7fff8000 <= crt_SH pos /\ crt_SH pos + 256 <= 0x10007fff7000.
Proof.
intros Sc mc dc pos HAR Hin.
destruct (frames_bounds SEGS B LAWS ly Sc W mc dc 5 pos HAR Hin) as (Hf0 & Hfc & Happ).
pose proof asan_consts as (C1 & _).
change (frame_addr ly 5 pos) with (crt_F pos) in Hf0, Hfc, Happ. change (fs_frame_bytes 5) with 2048 in Hfc, Happ.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
assert (Hq0 : 0 <= crt_F pos / 8) by (apply Z.div_pos; lia).
assert (Hq1 : crt_F pos / 8 <= 0xfffffefff00) by (apply Z.div_le_upper_bound; lia).
assert (ESH : crt_SH pos = 0x7fff8000 + crt_F pos / 8) by reflexivity.
rewrite ESH. set (qF := crt_F pos / 8) in *. clearbody qF.
split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.
(* a memory that differs from mc only on crts1_Wr keeps the saved registers, the flag word, the image and the live
   blocks *)
Lemma crts1_keep : forall Sc mc dc pos (mc' : word -> option byte),
  AR SEGS B ly Sc W mc dc -> In (5, pos) (frames Sc) -> ablocks B ly Sc = ablocks B ly S ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ crts1_Wr pos a -> rdW W mc' a = rdW W mc a) ->
  crt_frame (rdW W mc) -> rdword (rdW W mc) (crt_F pos + fs_frame_bytes 5 - 8) = Some (crt_FL pos) ->
  crt_KI W mc -> crt_KB W mc ->
  crt_frame (rdW W mc') /\ rdword (rdW W mc') (crt_F pos + fs_frame_bytes 5 - 8) = Some (crt_FL pos) /\
  crt_KI W mc' /\ crt_KB W mc'.
Proof.
intros Sc mc dc pos mc' HAR Hin Eab HK HFR HFL HKI HKB.
pose proof crt_sp0 as (S1 & S2 & _). pose proof crt_sp1_bounds as (P1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (crts1_geo Sc mc dc pos HAR Hin) as (G1 & G2 & G3 & G4 & G5).
pose proof (frm_img SEGS B LAWS ly Sc W mc dc 5 pos) as Hfi.
change (frame_addr ly 5 pos) with (crt_F pos) in Hfi. change (fs_frame_bytes 5) with 2048 in Hfi |- *.
split; [|split; [|split]].
- intros j r Hj. assert (Hj13 : (j < 13)%nat) by (rewrite <- crt_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
  apply (crt_aval_kept (rdW W mc)); [|exact (HFR j r Hj)].
  intros k Hk. apply HK; [lia|]. unfold crts1_Wr. lia.
- rewrite (YCbq.rdword_ext (rdW W mc) (rdW W mc')); [exact HFL|].
  intros k Hk. apply HK; [lia|]. unfold crts1_Wr. lia.
- intros a Hi Ho He. pose proof (pa_segs_low a Hi) as Hlo. rewrite (HK a); [exact (HKI a Hi Ho He) | lia |].
  unfold crts1_Wr. intros [Hw | [Hw | Hw]]; [lia | exact (Hfi a HAR Hin ltac:(lia) Hi) | lia].
- intros p n i Hp Hi.
  assert (Hp' : In (p, n) (ablocks B ly Sc)) by (rewrite Eab; exact Hp).
  destruct (al_blocks _ _ LAWS ly Sc W mc dc p n HAR Hp') as (_ & H4096 & Hceil & Happb & _ & _ & Hn).
  pose proof (req_size_pos n (proj1 Hn)) as [Hq1 Hq2].
  pose proof (sep_block_frame SEGS B LAWS ly Sc W mc dc p n 5 pos HAR Hp' Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr ly 5 pos) with (crt_F pos) in Hd.
  change (fs_frame_bytes 5) with 2048 in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happb.
  rewrite (HK (p + i)); [exact (HKB p n i Hp Hi) | lia | unfold crts1_Wr; lia].
Qed.
(* the seed at 0x88050: every register its own atom, atom 32 the frame's shadow SH *)
Lemma crts1_seed : forall Sc mc dc rB pos,
  crt_J pos ly Sc W mc dc 0 -> frames Sc = (5, pos) :: frames S ->
  getr rB 9 = w64 crt_sp1 -> getr rB 10 = w64 (crt_F pos) -> getr rB 27 = w64 SHADOW_OFF ->
  st_ok_pi SEGS VAL (Eimg (Ereg rB [w64 (crt_SH pos)])) crts1_ss
   (restrict (w_H W) (mkst rB (Z_to_bv 64 (BASE + 7020)) mc (seg_rom SEGS))).
Proof.
intros Sc mc dc rB pos HJ Hfrs R9 R10 R27. unfold crt_J in HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof crt_sp0 as (S1 & S2 & _). pose proof crt_sp1_bounds as (P1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof (crts1_geo Sc mc dc pos HAR Hin) as (G1 & G2 & G3 & G4 & G5).
destruct (al_frames _ _ LAWS ly Sc W mc dc 5 pos HAR Hin) as (_ & _ & Hfb & Hsh).
change (shadow_addr (frame_addr ly 5 pos)) with (crt_SH pos) in Hsh. change (fs_frame_bytes 5 / 8) with 256 in Hsh.
change (frame_addr ly 5 pos) with (crt_F pos) in Hfb. change (fs_frame_bytes 5) with 2048 in Hfb.
set (E := Eimg (Ereg rB [w64 (crt_SH pos)])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rB r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 (crt_SH pos)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rB _ 0)).
assert (U9 : bv_unsigned (ew E 9) = crt_sp1) by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = crt_F pos)
  by (rewrite (EE 10%nat 10%bv eq_refl), R10; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = crt_SH pos) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold crts1_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite crt_STK. lia.
  + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hfb (crt_F pos + o) ltac:(lia))).
  + rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hsh o ltac:(lia))).
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U10, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10, Z.pow_0_r, Z.mod_1_r.
    repeat split; lia.
  + cbn [f_alias alias_ok]. split; [|exact I]. unfold crts1_shx. apply U_inj.
    rewrite U_SAlu, U_srl3.
    rewrite (U_atom E 10 (crt_F pos) ltac:(rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity) ltac:(lia)).
    rewrite (U_atom E 27 SHADOW_OFF ltac:(rewrite (EE 27%nat 27%bv eq_refl), R27; reflexivity) ltac:(unfold SHADOW_OFF; lia)).
    rewrite (U_atom E 32 (crt_SH pos) E32 ltac:(lia)).
    assert (EF8 : crt_F pos / 8 + SHADOW_OFF = crt_SH pos) by (unfold crt_SH; ring).
    cbn [zalu_raw]. rewrite EF8. apply zcanon_id. unfold M64. lia.
Qed.
Lemma crt_s1 : ST_B2 -> ST_B.
Proof.
intros HB2 Sc mc dc rB pos HJ Hfrs Hnin Eab Hnev Hbb Hmo Hz Hflag HFR0 HKI HKB R2 R9 R8 R3 R4 R10 R22 R23 R24 R27.
pose proof HJ as (HAR & _).
pose proof crt_sp0 as (S1 & S2 & _). pose proof crt_sp1_bounds as (P1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin5 : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof (crts1_geo Sc mc dc pos HAR Hin5) as (G1 & G2 & G3 & G4 & G5).
pose proof (crts1_seed Sc mc dc rB pos HJ Hfrs R9 R10 R27) as HS.
set (E := Eimg (Ereg rB [w64 (crt_SH pos)])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rB r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 (crt_SH pos)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rB _ 0)).
assert (U9 : bv_unsigned (ew E 9) = crt_sp1) by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = crt_F pos)
  by (rewrite (EE 10%nat 10%bv eq_refl), R10; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = crt_SH pos) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
unfold cfgP.
paj_run_shc crt_RUNP crt_RUNC HS HJ.
{ intros a (r & Hr & Ha). unfold crts1_ss in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - left. rewrite U9 in Ha. rewrite crt_STK. lia.
  - right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    change (frame_addr ly 5 pos) with (crt_F pos). change (fs_frame_bytes 5) with 2048. rewrite U10 in Ha. lia.
  - right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    change (shadow_addr (frame_addr ly 5 pos)) with (crt_SH pos). change (fs_frame_bytes 5 / 8) with 256.
    rewrite U32 in Ha. lia. }
clear_md.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ crts1_Wr pos a -> rdW W (ms_mem ms) a = rdW W mc a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E (ss_mem crts1_ss) (w_H W) mc (ms_mem ms) (crts1_Wr pos) HFr);
    [|exact Ha | exact Hn].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U10, ?U32 in Hrr; unfold crts1_Wr; lia |]).
  destruct Hin. }
clear HF HFr HG.
pmkst HS.
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 7152)) by (crt_rreg HS; apply (codeptr_val _ 7152 HEI)).
assert (Q2 : getr (ms_regs ms) 2 = w64 crt_sp1) by (crt_rreg HS; rewrite crt_den_atom0, (EE 2%nat 2%bv eq_refl); exact R2).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (crt_rreg HS; rewrite crt_den_atom0, (EE 3%nat 3%bv eq_refl); exact R3).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (crt_rreg HS; rewrite crt_den_atom0, (EE 4%nat 4%bv eq_refl); exact R4).
assert (Q10 : getr (ms_regs ms) 10 = w64 (crt_SH pos + 4)) by (crt_rreg HS; exact (crt_den_off E 32 (crt_SH pos) 4 E32 ltac:(lia))).
assert (Q11 : getr (ms_regs ms) 11 = w64 112) by (crt_rreg HS; reflexivity).
assert (QRC : crt_regs (ms_regs ms) (crt_RC pos)).
{ unfold crt_regs, crt_RC. repeat apply Forall_cons; cbn [fst snd].
  - crt_rreg HS. rewrite crt_den_atom0, (EE 2%nat 2%bv eq_refl). exact R2.
  - crt_rreg HS. rewrite crt_den_atom0, (EE 9%nat 9%bv eq_refl). exact R9.
  - crt_rreg HS. rewrite crt_den_atom0, (EE 8%nat 8%bv eq_refl). exact R8.
  - crt_rreg HS. rewrite crt_den_atom0, (EE 3%nat 3%bv eq_refl). exact R3.
  - crt_rreg HS. rewrite crt_den_atom0, (EE 4%nat 4%bv eq_refl). exact R4.
  - crt_rreg HS. rewrite crt_den_atom0, (EE 10%nat 10%bv eq_refl). exact R10.
  - crt_rreg HS. rewrite crt_den_atom0. exact E32.
  - crt_rreg HS. rewrite crt_den_atom0, (EE 10%nat 10%bv eq_refl). exact R10.
  - crt_rreg HS. exact (crt_den_off E 32 (crt_SH pos) 4 E32 ltac:(lia)).
  - crt_rreg HS. rewrite crt_den_atom0, (EE 22%nat 22%bv eq_refl). exact R22.
  - crt_rreg HS. rewrite crt_den_atom0, (EE 23%nat 23%bv eq_refl). exact R23.
  - crt_rreg HS. rewrite crt_den_atom0, (EE 24%nat 24%bv eq_refl). exact R24.
  - crt_rreg HS. rewrite crt_den_atom0, (EE 27%nat 27%bv eq_refl). exact R27.
  - apply Forall_nil. }
eapply SRr_bind.
{ apply (aj_set_shadow_atS SEGS B LAWS pa_segs_low (SIG CS___asan_set_shadow_f8) 0xf8 (ASHF8 fx) W (ms_regs ms) (ms_mem ms)
    STK sp0 crt_FP ly S W mem md [(5, pos)] ly Sc _ 0 (crt_sp1 - sp0) (Z_to_bv 64 (BASE + 7152)) 5 pos
    (crt_SH pos + 4) 112 HJ).
  - left. reflexivity.
  - unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact (proj2 (proj2 (proj2 crt_sp1_bounds))).
  - lia.
  - unfold ESTACK. rewrite crt_STK. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Q10.
  - exact Q11.
  - lia.
  - change (shadow_addr (frame_addr ly 5 pos)) with (crt_SH pos). lia.
  - change (shadow_addr (frame_addr ly 5 pos)) with (crt_SH pos). change (fs_frame_bytes 5 / 8) with 256. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hval & HK2).
assert (Kall : forall a, 0 <= a < 2 ^ 64 -> ~ crts1_Wr pos a -> rdW W mem2 a = rdW W mc a).
{ intros a Ha Hn. rewrite (HK2 a Ha).
  - exact (K1 a Ha Hn).
  - intros Hq. apply Hn. unfold crts1_Wr. lia.
  - unfold ESTACK. intros Hq. apply Hn. unfold crts1_Wr. lia. }
destruct (crts1_keep Sc mc dc pos mem2 HAR Hin5 Eab Kall HFR0 Hflag HKI HKB) as (N1 & N2 & N3 & N4).
apply (HB2 Sc mem2 md2 regs2 pos).
- exact HJ2.
- exact Eab.
- exact Hnev.
- exact Hbb.
- exact Hmo.
- exact N1.
- exact N2.
- exact N3.
- exact N4.
- exact (crt_regs_pres (ms_regs ms) regs2 (crt_RC pos) HP2 (crts1_RC_cs pos) QRC).
Qed.
(* ---------- s2 (0x880d4 .. the call of __asan_set_shadow_00 at 0x88120, return 0x88124 = 7232): sixteen stores of f3
   at SH + 116 .. 131 through s3, then the fill of SH + 4 .. 115 with 0. The plain executor, as in s1. ---------- *)
Definition crts2_ss : sstate := mkSS 7152 sr_atoms [YP09.mkRegion (Some 19%nat) 116 132 116 132 []] None (mkFacts [] [] []).
Lemma crts2_seed : forall Sc mc dc rX pos, crt_J pos ly Sc W mc dc 0 -> crt_regs rX (crt_RC pos) ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) crts2_ss (restrict (w_H W) (mkst rX (Z_to_bv 64 (BASE + 7152)) mc (seg_rom SEGS))).
Proof.
intros Sc mc dc rX pos HJ HRC. unfold crt_J in HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin5 : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (crts1_geo Sc mc dc pos HAR Hin5) as (G1 & G2 & G3 & G4 & G5).
destruct (al_frames _ _ LAWS ly Sc W mc dc 5 pos HAR Hin5) as (_ & _ & _ & Hsh).
change (shadow_addr (frame_addr ly 5 pos)) with (crt_SH pos) in Hsh. change (fs_frame_bytes 5 / 8) with 256 in Hsh.
assert (R19 : getr rX (Z_to_bv 5 19) = w64 (crt_SH pos))
  by (apply (crt_reg rX (crt_RC pos)); [exact HRC | unfold crt_RC; crt_in]).
assert (U19 : bv_unsigned (ew (Eimg (Ereg rX [])) 19) = crt_SH pos)
  by (rewrite (ew_Eimg_Ereg_nat rX [] 19 (Z_to_bv 5 19) eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold crts2_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hsh o ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [exact I | split; exact I].
Qed.
Lemma crt_s2 : ST_C -> ST_B2.
Proof.
intros HC Sc mc dc rX pos HJ Eab Hnev Hbb Hmo HFR0 Hflag HKI HKB HRC.
pose proof HJ as HJ0. unfold crt_J in HJ0. destruct HJ0 as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin5 : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof crt_sp0 as (S1 & S2 & _). pose proof crt_sp1_bounds as (P1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (crts1_geo Sc mc dc pos HAR Hin5) as (G1 & G2 & G3 & G4 & G5).
assert (RG : forall r v, In (r, v) (crt_RC pos) -> getr rX (Z_to_bv 5 r) = w64 v)
  by (intros r v Hin; exact (crt_reg rX (crt_RC pos) r v HRC Hin)).
assert (R2 : getr rX (Z_to_bv 5 2) = w64 crt_sp1) by (apply RG; unfold crt_RC; cbn [In]; repeat (first [left; reflexivity | right])).
assert (R3 : getr rX (Z_to_bv 5 3) = w64 (as_gp B)) by (apply RG; unfold crt_RC; cbn [In]; repeat (first [left; reflexivity | right])).
assert (R4 : getr rX (Z_to_bv 5 4) = w64 (as_tp B)) by (apply RG; unfold crt_RC; cbn [In]; repeat (first [left; reflexivity | right])).
assert (R19 : getr rX (Z_to_bv 5 19) = w64 (crt_SH pos)) by (apply RG; unfold crt_RC; cbn [In]; repeat (first [left; reflexivity | right])).
assert (R21 : getr rX (Z_to_bv 5 21) = w64 (crt_SH pos + 4)) by (apply RG; unfold crt_RC; cbn [In]; repeat (first [left; reflexivity | right])).
pose proof (crts2_seed Sc mc dc rX pos HJ HRC) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U19 : bv_unsigned (ew E 19) = crt_SH pos)
  by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
unfold crt_J in HJ. unfold cfgP.
paj_run_shc crt_RUNP crt_RUNC HS HJ.
{ intros a (r & Hr & Ha). unfold crts2_ss in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
  change (shadow_addr (frame_addr ly 5 pos)) with (crt_SH pos). change (fs_frame_bytes 5 / 8) with 256.
  rewrite U19 in Ha. lia. }
clear_md.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ crts1_Wr pos a -> rdW W (ms_mem ms) a = rdW W mc a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E (ss_mem crts2_ss) (w_H W) mc (ms_mem ms) (crts1_Wr pos) HFr);
    [|exact Ha | exact Hn].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U19 in Hrr; unfold crts1_Wr; lia |]).
  destruct Hin. }
clear HF HFr HG.
assert (HPR : aregs_preserved rX (ms_regs ms)).
{ apply (aregs_preserved_of_st_ok SEGS (w_H W) E _ ms rX [] HS).
  - split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  - vm_compute. reflexivity. }
pmkst HS.
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 7232)) by (crt_rreg HS; apply (codeptr_val _ 7232 HEI)).
assert (Q2 : getr (ms_regs ms) 2 = w64 crt_sp1)
  by (crt_rreg HS; rewrite crt_den_atom0, (EE 2%nat (Z_to_bv 5 2) eq_refl); exact R2).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (crt_rreg HS; rewrite crt_den_atom0, (EE 3%nat (Z_to_bv 5 3) eq_refl); exact R3).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (crt_rreg HS; rewrite crt_den_atom0, (EE 4%nat (Z_to_bv 5 4) eq_refl); exact R4).
assert (Q10 : getr (ms_regs ms) 10 = w64 (crt_SH pos + 4))
  by (crt_rreg HS; rewrite crt_den_atom0, (EE 21%nat (Z_to_bv 5 21) eq_refl); exact R21).
assert (Q11 : getr (ms_regs ms) 11 = w64 112) by (crt_rreg HS; reflexivity).
eapply SRr_bind.
{ apply (aj_set_shadow_atS SEGS B LAWS pa_segs_low (SIG CS___asan_set_shadow_00) 0 (ASH00 fx) W (ms_regs ms) (ms_mem ms)
    STK sp0 crt_FP ly S W mem md [(5, pos)] ly Sc _ 0 (crt_sp1 - sp0) (Z_to_bv 64 (BASE + 7232)) 5 pos
    (crt_SH pos + 4) 112 HJ).
  - left. reflexivity.
  - unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact (proj2 (proj2 (proj2 crt_sp1_bounds))).
  - lia.
  - unfold ESTACK. rewrite crt_STK. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Q10.
  - exact Q11.
  - lia.
  - change (shadow_addr (frame_addr ly 5 pos)) with (crt_SH pos). lia.
  - change (shadow_addr (frame_addr ly 5 pos)) with (crt_SH pos). change (fs_frame_bytes 5 / 8) with 256. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hval & HK2).
assert (Kall : forall a, 0 <= a < 2 ^ 64 -> ~ crts1_Wr pos a -> rdW W mem2 a = rdW W mc a).
{ intros a Ha Hn. rewrite (HK2 a Ha).
  - exact (K1 a Ha Hn).
  - intros Hq. apply Hn. unfold crts1_Wr. lia.
  - unfold ESTACK. intros Hq. apply Hn. unfold crts1_Wr. lia. }
destruct (crts1_keep Sc mc dc pos mem2 HAR Hin5 Eab Kall HFR0 Hflag HKI HKB) as (N1 & N2 & N3 & N4).
apply (HC Sc mem2 md2 regs2 pos).
- exact HJ2.
- exact Eab.
- exact Hnev.
- exact Hbb.
- exact Hmo.
- unfold crt_fr. split; [exact N1|]. split; [exact N2|].
  intros i Hi. replace (crt_SH pos + i) with (crt_SH pos + 4 + (i - 4)) by lia. apply Hval. lia.
- exact N3.
- exact N4.
- exact (crt_regs_pres rX regs2 (crt_RC pos) (aregs_preserved_trans rX (ms_regs ms) regs2 HPR HP2) (crts1_RC_cs pos) HRC).
Qed.
(* ---------- s3: 0x88124 .. 0x88194 (the guards, then rec_calls_copy) ---------- *)
Lemma crts3_kpg : forall (Wc : world SEGS) mc, crt_KI Wc mc -> forall a, inFP cmd_PG a -> rdW Wc mc a = rdW W mem a.
Proof. intros Wc mc KI a Ha. destruct (crt_pg a Ha) as [Ho He]. exact (KI a (cif_prog_img a Ha) Ho He). Qed.
(* the read-only bytes, at a later reader that kept the image *)
Lemma crts3_rod : forall (Wc : world SEGS) mc, crt_KI Wc mc -> arodata_okP SEGS CMD_RLO CMD_RHI B (rdW Wc mc).
Proof.
intros Wc mc KI a Hro Ho He. rewrite (KI a); [exact (HROD a Hro Ho He) | | exact Ho | exact He].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (RRO a Hr)].
Qed.
Lemma crts3_rook : forall lyc Sc (Wc : world SEGS) mc dc, AR SEGS B lyc Sc Wc mc dc -> crt_KI Wc mc -> cmd_ro_ok (rdW Wc mc).
Proof. intros lyc Sc Wc mc dc HARc KI. exact (cmd_ro_ok_of_aro SEGS B LAWS HB IMG lyc Sc Wc mc dc HARc (crts3_rod Wc mc KI)). Qed.
(* the recorder at the entry's state Sc (no block freed or grown), at a reader that kept g_rec and the blocks *)
Lemma crts3_rep : forall Sc (Wc : world SEGS) mc, ablocks B ly Sc = ablocks B ly S -> crt_KI Wc mc -> crt_KB Wc mc ->
  rec_repA B ly Sc (rdW Wc mc) R O.
Proof.
intros Sc Wc mc Hab KI KB.
apply (rcf_rep_repA B ly S ly Sc (rdW W mem) (rdW Wc mc) R O [] HREP).
- intros a Ha. exact (crts3_kpg Wc mc KI a (crt_inrec_pg a Ha)).
- rewrite Hab, app_nil_r. apply Permutation_refl.
- intros pn [].
- intros p n i Hin Hi. rewrite Hab in Hin. exact (KB p n i Hin Hi).
Qed.
Lemma crts3_ncalls : forall lyc Sc (rd : reader), rec_repA B lyc Sc rd R O -> aval_mem rd (A_G_REC + 8) 4 crt_nC.
Proof. intros lyc Sc rd (Q & HA & _). destruct HA as (_ & _ & _ & (_ & _ & HN & _) & _). exact HN. Qed.
Lemma crts3_quit : forall (Wc : world SEGS) mc, crt_KI Wc mc -> aval_mem (rdW Wc mc) A_G_QUITTING 4 q.
Proof.
intros Wc mc KI. apply (crt_aval_kept (rdW W mem)); [|exact HVQ].
intros k Hk. apply (crts3_kpg Wc mc KI). exists (A_G_QUITTING, A_G_QUITTING + 4).
split; [right; right; left; reflexivity | cbn [fst snd]; cbn in Hk; lia].
Qed.
(* the caller's word n at W0 + 24: on the caller's stack above this call's window, kept by the journal *)
Lemma crts3_n : forall pos lyc Sc (Wc : world SEGS) mc dc k, crt_J pos lyc Sc Wc mc dc k ->
  aval_mem (rdW Wc mc) (W0 + 24) 4 (Z.of_nat (length ws)).
Proof.
intros pos lyc Sc Wc mc dc k HJ. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof crt_sp0 as (S1 & S2 & S3 & S4 & S5). pose proof asan_consts as (C1 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _). pose proof Hstk as (_ & _ & _ & _ & Hshi & H47 & _).
apply (crt_aval_kept (rdW W mem)); [|exact HVN].
intros kk Hk. cbn in Hk. apply F1; [lia | rewrite crt_STK; lia | intros Hf; apply crt_fp_low in Hf; lia].
Qed.
(* the guards' seed at 0x88124: every register its own atom; n, &g_quitting, q, &g_rec, ncalls the atoms 32 .. 36;
   the word n on the caller's stack, the two GOT words, g_quitting and g_rec.ncalls *)
Definition crts3_E (rX : bvmap 5 word) : env :=
  Eimg (Ereg rX [w64 (Z.of_nat (length ws)); w64 A_G_QUITTING; w64 q; w64 A_G_REC; w64 crt_nC]).
Definition crts3_ss : sstate := mkSS 7232 sr_atoms
  [YP09.mkRegion (Some 22%nat) 24 28 0 0 [YP09.mkChunk 24 (CVal 4 (SOff 32 0))];
   YP09.mkRegion (Some (A_OBJ 6)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
   YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))];
   YP09.mkRegion (Some (A_OBJ 2)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 35 0))];
   YP09.mkRegion (Some 35%nat) 8 12 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 36 0))]] None
  (mkFacts [(27%nat, mkAF SB SB 0); (22%nat, mkAF (2^46) (2^47 - 32) 0); (32%nat, mkAF 0 (2^31 - 1) 0);
            (33%nat, mkAF A_G_QUITTING A_G_QUITTING 3); (34%nat, mkAF 0 (2^32 - 1) 0);
            (35%nat, mkAF A_G_REC A_G_REC 3); (36%nat, mkAF 0 2 0)] [] []).
Section s3E.
Variables (rX : bvmap 5 word) (pos : Z).
Hypothesis HR : crt_regs rX (crt_RC pos).
Lemma crts3_EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (crts3_E rX) n = getr rX r.
Proof. intros n r Hn. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma crts3_EX : forall j, (j < 5)%nat -> ew (crts3_E rX) (32 + j) =
  nth j [w64 (Z.of_nat (length ws)); w64 A_G_QUITTING; w64 q; w64 A_G_REC; w64 crt_nC] (Z_to_bv 64 0).
Proof. intros j Hj. unfold crts3_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma crts3_Ereg : forall (r : nat) v, In (Z.of_nat r, v) (crt_RC pos) -> (r < 32)%nat -> ew (crts3_E rX) r = w64 v.
Proof.
intros r v Hin Hr. rewrite (crts3_EE r (Z_to_bv 5 (Z.of_nat r))).
- exact (crt_reg rX (crt_RC pos) _ v HR Hin).
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma crts3_EG : forall i v, (i < length CmdAddr.cmd_objs)%nat -> nth i CmdAddr.cmd_objs 0 = v ->
  ew (crts3_E rX) (A_OBJ i) = Z_to_bv 64 v.
Proof.
intros i v Hi Hv. unfold crts3_E. rewrite Eimg_img; [rewrite (HVAL i Hi), Hv; reflexivity|].
split; [unfold A_OBJ, A_TEXT; lia|]. unfold A_OBJ, A_LIM. cbn in Hi. lia.
Qed.
End s3E.
Lemma crts3_seed : forall Sc mc dc rX pos, crt_J pos ly Sc W mc dc 0 -> ablocks B ly Sc = ablocks B ly S ->
  crt_KI W mc -> crt_KB W mc -> crt_regs rX (crt_RC pos) ->
  st_ok_pi SEGS VAL (crts3_E rX) crts3_ss (restrict (w_H W) (mkst rX (Z_to_bv 64 (BASE + 7232)) mc (seg_rom SEGS))).
Proof.
intros Sc mc dc rX pos HJ Hab KI KB HR.
pose proof crt_sp0 as (S1 & S2 & S3 & S4 & S5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & _ & Hslo & Hshi & H47 & _).
assert (E22 : bv_unsigned (ew (crts3_E rX) 22) = W0).
{ rewrite (crts3_Ereg rX pos HR 22 W0) by (first [unfold crt_RC; crt_in | lia]). apply unsigned_lit_small. lia. }
assert (E27 : bv_unsigned (ew (crts3_E rX) 27) = SB).
{ rewrite (crts3_Ereg rX pos HR 27 SHADOW_OFF) by (first [unfold crt_RC; crt_in | lia]). apply unsigned_lit_small. unfold SB, SHADOW_OFF; lia. }
assert (E32 : ew (crts3_E rX) 32 = w64 (Z.of_nat (length ws))) by exact (crts3_EX rX 0 ltac:(lia)).
assert (E33 : ew (crts3_E rX) 33 = w64 A_G_QUITTING) by exact (crts3_EX rX 1 ltac:(lia)).
assert (E34 : ew (crts3_E rX) 34 = w64 q) by exact (crts3_EX rX 2 ltac:(lia)).
assert (E35 : ew (crts3_E rX) 35 = w64 A_G_REC) by exact (crts3_EX rX 3 ltac:(lia)).
assert (E36 : ew (crts3_E rX) 36 = w64 crt_nC) by exact (crts3_EX rX 4 ltac:(lia)).
assert (EG6 : ew (crts3_E rX) (A_OBJ 6) = Z_to_bv 64 0xa7080) by (apply crts3_EG; [vm_compute; lia | reflexivity]).
assert (EG2 : ew (crts3_E rX) (A_OBJ 2) = Z_to_bv 64 0xa7068) by (apply crts3_EG; [vm_compute; lia | reflexivity]).
assert (HnC : 0 <= crt_nC <= 2) by (unfold crt_nC; lia).
assert (U32 : bv_unsigned (ew (crts3_E rX) 32) = Z.of_nat (length ws)) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (crts3_E rX) 33) = A_G_QUITTING) by (rewrite E33; apply unsigned_lit_small; unfold A_G_QUITTING; lia).
assert (U34 : bv_unsigned (ew (crts3_E rX) 34) = q) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew (crts3_E rX) 35) = A_G_REC) by (rewrite E35; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (U36 : bv_unsigned (ew (crts3_E rX) 36) = crt_nC) by (rewrite E36; apply unsigned_lit_small; lia).
assert (UG6 : bv_unsigned (ew (crts3_E rX) (A_OBJ 6)) = 0xa7080) by (rewrite EG6; apply unsigned_lit_small; lia).
assert (UG2 : bv_unsigned (ew (crts3_E rX) (A_OBJ 2)) = 0xa7068) by (rewrite EG2; apply unsigned_lit_small; lia).
pose proof (crts3_rook ly Sc W mc dc (proj1 HJ) KI) as HRO.
pose proof (crts3_rep Sc W mc Hab KI KB) as HREPc.
rewrite restrict_mkst_fx. unfold crts3_ss. apply pa_entry_st_ok_full.
- unfold crts3_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ W0 24 4 (SOff 32 0) (Z.of_nat (length ws)));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    apply crt_val_of_aval. exact (crts3_n pos ly Sc W mc dc 0 HJ).
  + rewrite UG6. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ 0xa7080 0 8 (SOff 33 0) A_G_QUITTING);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold A_G_QUITTING; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. apply crt_val_of_aval. exact (crt_got_q _ HRO).
  + rewrite U33. split; [unfold A_G_QUITTING; lia|]. split; [unfold A_G_QUITTING; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ A_G_QUITTING 0 4 (SOff 34 0) q);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. apply crt_val_of_aval. exact (crts3_quit W mc KI).
  + rewrite UG2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ 0xa7068 0 8 (SOff 35 0) A_G_REC);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold A_G_REC; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. apply crt_val_of_aval. exact (crt_got_r _ HRO).
  + rewrite U35. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ A_G_REC 8 4 (SOff 36 0) crt_nC);
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    apply crt_val_of_aval. exact (crts3_ncalls _ _ _ HREPc).
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E22, UG6, U33, UG2, U35.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_G_QUITTING, A_G_REC. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E27, E22, U32, U33, U34, U35, U36. change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
  unfold SB, A_G_QUITTING, A_G_REC. repeat split; try lia; reflexivity.
Qed.

(* a stack range at zero shadow: AR keeps [ly_stk_lo, ly_stk_hi) so (joined.v jw_stack_ra) *)
Lemma crts3_stack_ra : forall lyc Sc (Wc : world SEGS) mc dc a n,
  AR SEGS B lyc Sc Wc mc dc -> ly_stk_lo lyc <= a -> a + n <= ly_stk_hi lyc ->
  range_addressable (rdW Wc mc) SHADOW_OFF a n.
Proof.
intros lyc Sc Wc mc dc a n HAR Hlo Hhi.
pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO. destruct (lo_top _ LO) as (_ & _ & _ & _ & Hpl & Hph & _).
unfold page_aligned in Hpl, Hph. try unfold PGSZ in Hpl, Hph.
assert (A8 : forall x, x mod 4096 = 0 -> x mod 8 = 0).
{ intros x Hx. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hx; [|lia].
  apply (Z.divide_trans 8 4096); [exists 512; reflexivity | exact Hx]. }
apply (range_addressable_sub _ _ (ly_stk_lo lyc) (ly_stk_hi lyc - ly_stk_lo lyc)); [|lia|lia].
apply zero_shadow_range; [exact (A8 _ Hpl) | rewrite Zminus_mod, (A8 _ Hpl), (A8 _ Hph); reflexivity |].
exact (al_zshadow _ _ LAWS lyc Sc Wc mc dc _ HAR ltac:(left; reflexivity)).
Qed.
(* the registers that hold their entry atom after a run keep the entry's values *)
Lemma crts3_keep_regs : forall rX E' ss (H : word -> bool) ms' (rl : list Z) (L : list (Z * Z)),
  st_ok_pi SEGS VAL E' ss (restrict H ms') ->
  (forall n, (n < 32)%nat -> ew E' n = ew (crts3_E rX) n) ->
  forallb (fun r => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0) && (0 <=? r) && (r <? 32)) rl = true ->
  Forall (fun rv => In (fst rv) rl /\ getr rX (Z_to_bv 5 (fst rv)) = w64 (snd rv)) L ->
  crt_regs (ms_regs ms') L.
Proof.
intros rX E' ss H ms' rl L HS HE Hrl HL. unfold crt_regs. eapply Forall_impl; [|exact HL].
intros [r v] [Hin Hv]. cbn [fst snd] in *.
pose proof (proj1 (forallb_forall _ _) Hrl r Hin) as Hb. apply andb_prop in Hb as [Hb H32]. apply andb_prop in Hb as [Hb H0].
apply Z.ltb_lt in H32. apply Z.leb_le in H0.
rewrite (st_ok_pi_restrict_reg H E' ss ms' _ HS), (sv_eqb_eq _ _ Hb), crt_den_atom0, HE by lia.
rewrite (crts3_EE rX (Z.to_nat r) (Z_to_bv 5 r)); [exact Hv|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
Qed.
(* a run whose only write window is [lo, hi) (above the blocks and frames, below the prologue's frame) keeps the facts
   the next point needs, at the new memory *)
Lemma crts3_go : forall pos Sc mc mc' dc lo hi, crt_J pos ly Sc W mc dc 0 -> alloc_ceiling <= lo -> hi <= sp0 - 104 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rdW W mc' a = rdW W mc a) ->
  crt_fr pos W mc -> crt_KI W mc -> crt_KB W mc -> crt_fr pos W mc' /\ crt_KI W mc' /\ crt_KB W mc'.
Proof.
intros pos Sc mc mc' dc lo hi HJ Hlo Hhi K (FR1 & FR2 & FR3) KI KB.
pose proof HPRE as (HAR0 & _).
pose proof crt_sp0 as (S1 & S2 & S3 & S4 & S5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly Sc W mc dc 5 pos HARc Hfin) as (Hf1 & Hf2 & _).
assert (Hfb : fs_frame_bytes 5 = 2048) by reflexivity. rewrite Hfb in Hf2.
split; [split; [|split]|split].
- intros j r Hj. assert (Hj13 : (j < 13)%nat) by (rewrite <- crt_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
  apply (crt_aval_kept (rdW W mc)); [|exact (FR1 j r Hj)]. intros kk Hkk. apply K; lia.
- rewrite (rdword_ext (rdW W mc) (rdW W mc')); [exact FR2|]. intros kk Hkk. apply K; rewrite Hfb; unfold crt_F; lia.
- intros i Hi. rewrite K; [exact (FR3 i Hi)| |]; unfold crt_SH, crt_F, SHADOW_OFF;
  (assert (Hd : 0 <= frame_addr ly 5 pos / 8 /\ 8 * (frame_addr ly 5 pos / 8) <= frame_addr ly 5 pos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]));
  set (f8 := frame_addr ly 5 pos / 8) in *; clearbody f8; lia.
- intros a Hi Ho He. rewrite K; [exact (KI a Hi Ho He)| |]; pose proof (pa_img_range a Hi); lia.
- intros p n i Hin Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
  pose proof (req_size_pos n (proj1 Hm)) as [Hq1 Hq2]. rewrite K; [exact (KB p n i Hin Hi)| |]; lia.
Qed.
(* nonnegative costs *)
Lemma crts3_fold_nn : forall (f : list byte -> Z) l, (forall x, 0 <= f x) -> 0 <= fold_right (fun x acc => f x + acc) 0 l.
Proof. intros f l Hf. induction l as [|x l IH]; cbn [fold_right]; [lia|]. specialize (Hf x). lia. Qed.
Lemma crts3_xm_rcc_nn : 0 <= XM_REC_CALLS_COPY MT R.
Proof.
unfold XM_REC_CALLS_COPY. apply crts3_fold_nn. intros x. unfold XM_XSTRDUP. apply (mo_malloc_nonneg MT MTL). lia.
Qed.
Lemma crts3_xm_le : XM_REC_CALLS_COPY MT R <= XM_CHECK_ROUND_TRIP MT R ws.
Proof.
unfold XM_CHECK_ROUND_TRIP.
pose proof (mo_malloc_nonneg MT MTL (LMAX + 2) ltac:(unfold LMAX; lia)).
assert (0 <= XM_JOINED MT ws).
{ unfold XM_JOINED. apply (mo_malloc_nonneg MT MTL). unfold PJoin.join_need.
  pose proof (crts3_fold_nn (fun w => Z.of_nat (length w) + 1) ws ltac:(intros; cbv beta; lia)) as Hf. cbv beta in Hf. lia. }
pose proof (crt_xm_send_nn R (join_sp ws)). pose proof (mo_free_nonneg MT MTL). pose proof (crt_ev_args_nn R).
pose proof (Z.mul_nonneg_nonneg (ev_args R) (mo_free MT) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma crts3_ev_le : EV_REC_CALLS_COPY R <= EV_CHECK_ROUND_TRIP R ws.
Proof.
pose proof (crt_ev_send_nn R (join_sp ws)). pose proof (crt_ev_args_nn R).
unfold EV_CHECK_ROUND_TRIP, EV_JOINED. lia.
Qed.
Lemma crts3_ev_nn : 0 <= EV_REC_CALLS_COPY R.
Proof. pose proof (crt_ev_args_nn R). unfold EV_REC_CALLS_COPY, EV_XSTRDUP. lia. Qed.
Lemma crts3_live_nn : 0 <= LIVE_CHECK_ROUND_TRIP.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* the skip path: n = 0, or g_quitting = 0 and no recorded call; on to the shared epilogue, nothing done *)
Lemma crts3_skip : ST_EPI -> forall Sc mc dc rX pos, crt_J pos ly Sc W mc dc 0 ->
  ablocks B ly Sc = ablocks B ly S -> blocks_bytes Sc = blocks_bytes S -> mo_le MT S Sc 0 ->
  crt_fr pos W mc -> crt_KI W mc -> crt_KB W mc ->
  crt_regs rX [(2, crt_sp1); (8, sp0); (3, as_gp B); (4, as_tp B); (18, crt_F pos); (20, crt_F pos); (21, crt_SH pos + 4)] ->
  SRr SEGS W (cfgP 7728 rX mc dc) crt_postF.
Proof.
intros HEPI Sc mc dc rX pos HJ Hab Hbb Hmo (FR1 & FR2 & _) KI KB HR.
(* ST_EPI proves apost_base at the ambient FP state: apost_baseF's left disjunct (fx' := fx) *)
eapply SRr_mono.
{ apply (HEPI ly Sc W mc dc rX pos 0 R O HJ); [ | exact FR1 | exact FR2 | | exact HR].
  - pose proof crts3_ev_le. pose proof crts3_ev_nn. lia.
  - split; [exact (crts3_rep Sc W mc Hab KI KB)|].
    do 7 (split; [reflexivity|]).
    split; [exact (crts3_quit W mc KI)|].
    split; [rewrite Hab; exact HPERM|].
    split; [pose proof crts3_live_nn; lia|].
    apply (mle_weaken MT S Sc 0 _ MTL Hmo). pose proof crts3_xm_rcc_nn. pose proof crts3_xm_le. lia. }
intros W' c' _ HP. unfold crt_postF. unfold crt_post in HP.
exact (apost_baseF_of_base SEGS _ _ _ _ _ _ _ _ _ _ _ W' c' HP).
Qed.
(* the main path: the registers at 0x88184 *)
Definition crts3_RM (pos : Z) : list (Z * Z) := crt_RC pos ++ [(25, A_G_QUITTING); (26, crt_shx A_G_QUITTING)].
(* the symbolic-run bookkeeping of the guards: every byte kept (no write window) *)
Ltac crts3_upd := lazymatch goal with Hfr : frame_of _ _ (mrestrict ?H _) (mrestrict ?H ?m2) |- _ =>
  let K := fresh "K" in
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr
    ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin)) as K;
  clear Hfr;
  lazymatch goal with Kc : forall a, 0 <= a < 2 ^ 64 -> aview _ _ _ a = aview _ _ ?m0 a |- _ =>
    let Kn := fresh "Kn" in
    assert (Kn : forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m2 a = aview SEGS H m0 a)
      by (intros a Ha; rewrite (K a Ha (fun x => x)); exact (Kc a Ha));
    clear Kc K; rename Kn into Kc end end;
  repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.
Ltac crts3_old := intros ?n ?Hn; rewrite ?ew_ewset_other by lia; reflexivity.
Ltac crts3_srcregs HR := repeat (apply Forall_cons; [split; [cbn [fst In]; repeat first [left; reflexivity | right]
  | apply (crt_reg _ _ _ _ HR); unfold crts3_RM, crt_RC; cbn [fst snd app]; crt_in] |]); apply Forall_nil.
Lemma crts3_U : forall E' rX n v, (forall m, (m < 1024)%nat -> ew E' m = ew (crts3_E rX) m) ->
  ew (crts3_E rX) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> (n < 1024)%nat -> U E' (SOff n 0) = v.
Proof. intros E' rX n v HE Hn Hv Hlt. apply U_atom; [rewrite HE by lia; exact Hn | exact Hv]. Qed.
Lemma crts3_Uoff : forall E' rX n v c, (forall m, (m < 1024)%nat -> ew E' m = ew (crts3_E rX) m) ->
  ew (crts3_E rX) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> (n < 1024)%nat -> U E' (SOff n c) = v + c.
Proof. intros E' rX n v c HE Hn Hv Hc Hlt. apply U_atom_off; [rewrite HE by lia; exact Hn | exact Hv | exact Hc]. Qed.
(* lw's sign extension of a 32-bit value (rec_calls_equal.v rce_U_sext32) *)
Lemma crts3_U_sext32 : forall E a0 r, U E a0 = r -> 0 <= r < 2 ^ 32 ->
  U E (SExt true 32 a0) = (if r <? 2 ^ 31 then r else r - 2 ^ 32 + 2 ^ 64).
Proof.
intros E a0 r Ha Hr. rewrite U_SExt, Ha. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small r) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
destruct (Z.ltb_spec r (2 ^ 31)) as [Hl | Hh].
- rewrite (Z.mod_small (r + 2 ^ 31)) by lia. replace (r + 2 ^ 31 - 2 ^ 31) with r by lia. apply zcanon_id. unfold M64. lia.
- replace ((r + 2 ^ 31) mod 2 ^ 32) with (r + 2 ^ 31 - 2 ^ 32).
  2:{ replace (r + 2 ^ 31) with ((r + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) at 2 by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
  unfold zcanon, M64. replace (r + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with ((r - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
(* s10 = (s9 >> 3) + s11 = g_quitting's shadow byte *)
Lemma crts3_den_shx : forall E, ew E 33 = Z_to_bv 64 A_G_QUITTING -> ew E 27 = Z_to_bv 64 SB ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 0) (SLit 3)) (SOff 27 0)) = w64 (crt_shx A_G_QUITTING).
Proof. intros E H33 H27. cbn [sv_denot]. rewrite H33, H27. apply bv_eq. vm_compute. reflexivity. Qed.
Ltac crts3_q2526 HS E33 E27 :=
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd];
  [ crt_rreg HS; rewrite crt_den_atom0; rewrite ?ew_ewset_other by lia; exact E33
  | crt_rreg HS; apply crts3_den_shx; rewrite ?ew_ewset_other by lia; assumption ].
Lemma crts3_bge : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof.
intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia.
assert (Hs : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z).
{ intros z Hz. unfold bv_swrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
  rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia. }
rewrite !Hs by lia. reflexivity.
Qed.

(* ---------- the main path: 0x88184 .. 0x88194, rec_calls_copy(first) ---------- *)
Lemma crts3_regRC : forall rX pos, crt_regs rX (crts3_RM pos) -> crt_regs rX (crt_RC pos).
Proof. intros rX pos H. unfold crts3_RM, crt_regs in H. apply Forall_app in H. exact (proj1 H). Qed.
Lemma crts3_keep_regs_c : forall rX E' ss (H : word -> bool) ms' (rl : list Z) (L : list (Z * Z)),
  st_ok SEGS E' ss (restrict H ms') ->
  (forall n, (n < 32)%nat -> ew E' n = ew (crts3_E rX) n) ->
  forallb (fun r => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0) && (0 <=? r) && (r <? 32)) rl = true ->
  Forall (fun rv => In (fst rv) rl /\ getr rX (Z_to_bv 5 (fst rv)) = w64 (snd rv)) L ->
  crt_regs (ms_regs ms') L.
Proof.
intros rX E' ss H ms' rl L HS HE Hrl HL. unfold crt_regs. eapply Forall_impl; [|exact HL].
intros [r v] [Hin Hv]. cbn [fst snd] in *.
pose proof (proj1 (forallb_forall _ _) Hrl r Hin) as Hb. apply andb_prop in Hb as [Hb H32]. apply andb_prop in Hb as [Hb H0].
apply Z.ltb_lt in H32. apply Z.leb_le in H0.
rewrite (st_ok_restrict_reg SEGS H E' ss ms' _ HS), (sv_eqb_eq _ _ Hb), crt_den_atom0, HE by lia.
rewrite (crts3_EE rX (Z.to_nat r) (Z_to_bv 5 r)); [exact Hv|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
Qed.
Lemma crts3_F8 : forall F, F mod 32 = 0 -> F mod 8 = 0 /\ 8 * (F / 8) = F.
Proof.
intros F H. apply Z.mod_divide in H; [|lia]. destruct H as [k ->]. replace (k * 32) with ((4 * k) * 8) by lia.
rewrite Z.div_mul by lia. split; [apply Z_mod_mult | lia].
Qed.
(* an 8-byte slot of a symbolic region, read back *)
Lemma crts3_chunk8 : forall E H (m : word -> option byte) (nb : nat) b lo hi wlo whi cs off (n : nat) c v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some nb) lo hi wlo whi cs) ->
  bv_unsigned (ew E nb) = b -> In (YP09.mkChunk off (CVal 8 (SOff n c))) cs ->
  bv_unsigned (ew E n) + c = v -> 0 <= v < 2 ^ 64 -> aval_mem (aview SEGS H m) (b + off) 8 v.
Proof.
intros E H m nb b lo hi wlo whi cs off n c v HR Hb Hin Hv Hr.
pose proof (field_of_region_any E _ nb b cs lo hi wlo whi off 8%N (SOff n c) HR Hb Hin ltac:(cbn; lia)) as Hm.
cbn [sv_denot] in Hm. rewrite Hv in Hm. rewrite unsigned_lit_small in Hm by lia.
change (8 * Z.of_N 8) with 64 in Hm. rewrite Z.mod_small in Hm by lia. change (N.to_nat 8) with 8%nat in Hm.
apply crt_aval_of_val. exact Hm.
Qed.
Definition crts3_ssM : sstate := mkSS 7328 sr_atoms [YP09.mkRegion (Some 9%nat) 104 128 104 128 []] None
  (mkFacts [(9%nat, mkAF (2^46) (2^47) 5)] [] []).
Lemma crts3_seedM : forall Sc mc dc rX pos, crt_J pos ly Sc W mc dc 0 -> crt_regs rX (crts3_RM pos) ->
  st_ok_pi SEGS VAL (crts3_E rX) crts3_ssM (restrict (w_H W) (mkst rX (Z_to_bv 64 (BASE + 7328)) mc (seg_rom SEGS))).
Proof.
intros Sc mc dc rX pos HJ HR. pose proof (crts3_regRC rX pos HR) as HRC.
pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4). pose proof crt_sp0 as (S1 & S2 & S3 & S4 & S5). pose proof asan_consts as (C1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (E9 : bv_unsigned (ew (crts3_E rX) 9) = crt_sp1).
{ rewrite (crts3_Ereg rX pos HRC 9 crt_sp1) by (first [unfold crt_RC; crt_in | lia]). apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. unfold crts3_ssM. apply pa_entry_st_ok_full.
- unfold crts3_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite crt_STK. lia.
- split; exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E9.
  change (2 ^ 5) with 32. repeat split; try lia; exact P2.
Qed.
Lemma crts3_main : ST_D -> forall Sc mc dc rX pos, crt_J pos ly Sc W mc dc 0 ->
  ablocks B ly Sc = ablocks B ly S -> st_nev Sc = st_nev S -> blocks_bytes Sc = blocks_bytes S -> mo_le MT S Sc 0 ->
  crt_fr pos W mc -> crt_KI W mc -> crt_KB W mc -> crt_regs rX (crts3_RM pos) ->
  ws <> [] -> PCrt.acted_m R q = true ->
  SRr SEGS W (cfgP 7328 rX mc dc) crt_postF.
Proof.
intros HSTD Sc mc dc rX pos HJ Hab Hnev Hbb Hmo Hfr KI KB HR Hws Hact.
pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4). pose proof crt_sp0 as (Sp1 & Sp2 & Sp3 & Sp4 & Sp5).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof pa_B_ok as (HB0 & HB1 & _). pose proof pa_base_lo as HBlo.
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _). pose proof Hstk as (_ & _ & _ & Hslo & Hshi & H47 & _).
pose proof (crts3_regRC rX pos HR) as HRC.
pose proof (crts3_seedM Sc mc dc rX pos HJ HR) as HS.
assert (HEI : img_env VAL A_LIM (crts3_E rX)) by (unfold crts3_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 27 0) [] (crts3_E rX) (mrestrict (w_H W) mc)) by (unfold sh_ok; apply Forall_nil).
assert (WS : REC_CALLS_COPY_STK = 16560) by reflexivity.
assert (HnC : 0 <= crt_nC <= 2) by (unfold crt_nC; lia).
(* the frame *)
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly Sc W mc dc 5 pos HARc Hfin) as (Hf1 & Hf2 & Hfapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ 5 pos HARc Hfin) as (Hf32 & _).
destruct (crts3_F8 _ Hf32) as (Hf8 & HF8).
assert (Hfb : fs_frame_bytes 5 = 2048) by reflexivity. rewrite Hfb in Hf2, Hfapp.
assert (HFR : 0 <= crt_F pos < 2 ^ 64) by (unfold crt_F; lia).
assert (HCF : 4096 <= crt_F pos /\ crt_F pos + 2048 <= alloc_ceiling) by (unfold crt_F; lia).
(* the register values the run reads *)
assert (U9 : bv_unsigned (ew (crts3_E rX) 9) = crt_sp1).
{ rewrite (crts3_Ereg rX pos HRC 9 crt_sp1) by (first [unfold crt_RC; crt_in | lia]). apply unsigned_lit_small. lia. }
assert (E2 : ew (crts3_E rX) 2 = w64 crt_sp1) by (apply (crts3_Ereg rX pos HRC 2 crt_sp1); [unfold crt_RC; crt_in | lia]).
assert (E3 : ew (crts3_E rX) 3 = w64 (as_gp B)) by (apply (crts3_Ereg rX pos HRC 3 (as_gp B)); [unfold crt_RC; crt_in | lia]).
assert (E4 : ew (crts3_E rX) 4 = w64 (as_tp B)) by (apply (crts3_Ereg rX pos HRC 4 (as_tp B)); [unfold crt_RC; crt_in | lia]).
assert (E8 : ew (crts3_E rX) 8 = w64 sp0) by (apply (crts3_Ereg rX pos HRC 8 sp0); [unfold crt_RC; crt_in | lia]).
assert (E18 : ew (crts3_E rX) 18 = w64 (crt_F pos)) by (apply (crts3_Ereg rX pos HRC 18 (crt_F pos)); [unfold crt_RC; crt_in | lia]).
assert (E22 : ew (crts3_E rX) 22 = w64 W0) by (apply (crts3_Ereg rX pos HRC 22 W0); [unfold crt_RC; crt_in | lia]).
assert (E24 : ew (crts3_E rX) 24 = w64 sb) by (apply (crts3_Ereg rX pos HRC 24 sb); [unfold crt_RC; crt_in | lia]).
pose proof HJ as HJ0.
unfold cfgP. unfold crt_J in HJ.
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?f0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc f0 lyx own) end.
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 9%nat) (d := crt_sp1 - sp0);
    [reflexivity | rewrite U9; lia | cbn; rewrite crt_STK; lia | cbn; lia | apply awr_ok_nil]. }
lazymatch goal with Hfr' : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => crt_sp1 + 104 <= a < crt_sp1 + 128) Hfr'
    ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite U9 in Hrr; cbv beta; lia|]);
      destruct Hin)) as K1 end.
repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.
clear_md. pmkst HS.
(* the call target *)
rewrite (SIGP CS_rec_calls_copy ltac:(vm_compute; tauto)).
replace (VAL A_TEXT + cmd_af CS_rec_calls_copy) with (BASE + AF_rec_calls_copy)
  by (unfold cmd_af, AF_rec_calls_copy; vm_compute; reflexivity).
(* the three slots the run stored *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg end.
cbn [ms_mem restrict] in HRg.
assert (L104 : aval_mem (rdW W (ms_mem ms)) (crt_sp1 + 104) 8 (crt_F pos + 32)).
{ apply (crts3_chunk8 _ _ _ _ _ _ _ _ _ _ 104 18 32 _ HRg U9); [cbn [In]; repeat first [left; reflexivity | right] | | lia].
  rewrite E18. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (L112 : aval_mem (rdW W (ms_mem ms)) (crt_sp1 + 112) 8 sb).
{ apply (crts3_chunk8 _ _ _ _ _ _ _ _ _ _ 112 24 0 _ HRg U9); [cbn [In]; repeat first [left; reflexivity | right] | | lia].
  rewrite E24. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (L120 : aval_mem (rdW W (ms_mem ms)) (crt_sp1 + 120) 8 W0).
{ apply (crts3_chunk8 _ _ _ _ _ _ _ _ _ _ 120 22 0 _ HRg U9); [cbn [In]; repeat first [left; reflexivity | right] | |].
  - rewrite E22. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - pose proof HPRE as (_ & _ & _ & _ & _ & Hstk' & _). pose proof Hstk' as (_ & _ & _ & _ & Hshi' & H47' & _). lia. }
clear HRg.
(* the registers at the call *)
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 7348)) by (crt_rreg HS; apply (codeptr_val _ 7348 HEI)).
assert (R2 : getr (ms_regs ms) 2 = w64 crt_sp1) by (crt_rreg HS; rewrite crt_den_atom0; exact E2).
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (crt_rreg HS; rewrite crt_den_atom0; exact E3).
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (crt_rreg HS; rewrite crt_den_atom0; exact E4).
assert (R8 : getr (ms_regs ms) 8 = w64 sp0) by (crt_rreg HS; rewrite crt_den_atom0; exact E8).
assert (R10 : getr (ms_regs ms) 10 = w64 (crt_F pos + 32)) by (crt_rreg HS; exact (crt_den_off _ 18 (crt_F pos) 32 E18 HFR)).
assert (Hsp : spZ (ms_regs ms) = crt_sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z (ms_regs ms) = sp0) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
assert (Hregsc : crt_regs (ms_regs ms) (crts3_RM pos)).
{ apply (crts3_keep_regs_c rX _ _ (w_H W) _ [2; 9; 8; 3; 4; 18; 19; 20; 21; 22; 23; 24; 27; 25; 26] _ HS
    ltac:(crts3_old) ltac:(vm_compute; reflexivity)).
  unfold crts3_RM, crt_RC. cbn [app]. crts3_srcregs HR. }
(* the facts of the entry, at the call *)
destruct (crts3_go pos Sc mc (ms_mem ms) dc (crt_sp1 + 104) (crt_sp1 + 128) HJ0 ltac:(lia) ltac:(lia) K1 Hfr KI KB)
  as ((FRf & FRl & FRs) & KI1 & KB1).
pose proof (crts3_rod W _ KI1) as HRODc.
pose proof (crts3_rep Sc W _ Hab KI1 KB1) as HREPc.
assert (HOBJ : afobj SEGS B ly Sc W (ms_mem ms) (crt_F pos + 32) (CALL_SIZE * Z.of_nat (length (r_calls R)))).
{ split; [exists 5, pos; split; [exact Hfin|]; split; [lia|]; split; [exact Hf8|]; split;
    [unfold crt_F; lia | rewrite Hfb; unfold CALL_SIZE, crt_F; lia]|].
  assert (HF32 : (crt_F pos + 32) mod 8 = 0) by (unfold crt_F; rewrite Z.add_mod, Hf8 by lia; reflexivity).
  split; [exact HF32|].
  apply (range_addressable_sub _ _ (crt_F pos + 32) 896); [| lia | unfold CALL_SIZE; lia].
  apply zero_shadow_range; [exact HF32 | reflexivity |].
  intros i Hi. change (896 / 8) with 112 in Hi. replace (crt_F pos + 32) with (crt_F pos + 8 * 4) by lia.
  rewrite shadow_of_addr_add8. unfold shadow_of_addr.
  replace (SHADOW_OFF + crt_F pos / 8 + 4 + i) with (crt_SH pos + (4 + i)) by (unfold crt_SH; ring).
  apply FRs. lia. }
assert (HEVc : st_nev Sc + EV_REC_CALLS_COPY R <= EV_MAX) by (pose proof crts3_ev_le; lia).
assert (HLIVEc : blocks_bytes Sc + LIVE_REC_CALLS_COPY R <= LIVE_MAX).
{ pose proof (crt_live_rcc ly Sc (rdW W (ms_mem ms)) R O HREPc HNC).
  assert (12 * (LMAX + 1) <= LIVE_CHECK_ROUND_TRIP) by (apply Z.leb_le; vm_compute; reflexivity). lia. }
assert (HMOKc : mo_ok MT Sc (XM_REC_CALLS_COPY MT R)).
{ apply (mok_station MT S Sc (XM_CHECK_ROUND_TRIP MT R ws) 0 _ MTL MOK Hmo crts3_xm_rcc_nn). pose proof crts3_xm_le. lia. }
(* the frame chain at the call: the prologue's frame record on afn_pre's chain (s0 = sp0) *)
destruct (crt_chain pos ly Sc W (ms_mem ms) _ 0 HJ FRf) as [ch1 Hch0].
assert (Hch1 : achain ly (rdW W (ms_mem ms)) (sp0 + (crt_sp1 - sp0)) (s0Z (ms_regs ms)) ch1)
  by (rewrite Hs0; replace (sp0 + (crt_sp1 - sp0)) with crt_sp1 by lia; exact Hch0).
(* the call: rec_calls_copy writes first[] in this call's class-5 frame *)
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms) (ms_mem ms) _ STK sp0 crt_FP ly S W mem md [(5, pos)] ly Sc _ 0
    REC_CALLS_COPY_STK [(crt_F pos + 32, crt_F pos + 32 + CALL_SIZE * Z.of_nat (length (r_calls R)))]
    (EV_REC_CALLS_COPY R) (crt_sp1 - sp0) (getr (ms_regs ms) 1) ch1 _ HJ).
  - rewrite Hsp. lia.
  - exact P4.
  - lia.
  - rewrite WS. lia.
  - rewrite WS, crt_STK. lia.
  - exact R3.
  - exact R4.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite R1, unsigned_lit_small; lia.
  - exact Hch1.
  - intros HPRE1. exact (HRCC fx ly Sc W (ms_regs ms) (ms_mem ms) _ ch1 (crt_F pos + 32) R O HPRE1 HRODc R10 HREPc HNC
      HOBJ HEVc HLIVEc HMOKc).
  - intros a Ha. right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    destruct Ha as (r & [<- | []] & Ha). cbn [fst snd] in Ha. rewrite Hfb. unfold crt_F, CALL_SIZE in *. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. destruct Ha as (r & [<- | []] & Ha). cbn [fst snd] in Ha.
    rewrite crt_STK in Hw. unfold crt_F, CALL_SIZE in *. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & qs & R10' & Hlen & Htab & Hperm & HND & Hap
  & HKB2 & HREP2 & HBB2 & MLE2).
rewrite R1.
pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _ & G3 & G4 & _).
assert (HnFP : forall a, inFP [(crt_F pos + 32, crt_F pos + 32 + CALL_SIZE * Z.of_nat (length (r_calls R)))] a ->
  crt_F pos + 32 <= a < crt_F pos + 32 + CALL_SIZE * Z.of_nat (length (r_calls R))).
{ intros a (r & [<- | []] & Ha). exact Ha. }
(* the entry's image bytes and live blocks, after the call *)
assert (KI2 : crt_KI W2 mem2).
{ intros a Hi Ho He. rewrite (G3 a Hi Ho He); [exact (KI1 a Hi Ho He)|].
  apply fp_spares_closed; [apply sink_closed_pos; apply Forall_cons; [cbn [fst]; unfold crt_F in *; lia | apply Forall_nil]|].
  intros Hf. apply HnFP in Hf. apply (frm_img SEGS B LAWS ly Sc W mc dc 5 pos a HARc Hfin); [|exact Hi].
  rewrite Hfb. unfold crt_F, CALL_SIZE in *. lia. }
assert (KB2 : crt_KB W2 mem2).
{ intros p n i Hin Hi. rewrite (HKB2 p n i ltac:(rewrite Hab; exact Hin) Hi). exact (KB1 p n i Hin Hi). }
(* this call's frame, after the call: the saved registers, the flag word, the zero shadow *)
assert (FR2 : crt_fr pos W2 mem2).
{ split; [|split].
  - intros j r Hj. assert (Hj13 : (j < 13)%nat) by (rewrite <- crt_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
    apply (crt_aval_kept (rdW W (ms_mem ms))); [|exact (FRf j r Hj)]. intros kk Hkk.
    apply G1; [lia | rewrite WS; lia | intros Hf; apply HnFP in Hf; unfold crt_F, CALL_SIZE in *; lia].
  - rewrite Hfb in FRl |- *. rewrite (rdword_ext (rdW W (ms_mem ms)) (rdW W2 mem2)); [exact FRl|]. intros kk Hkk.
    apply (G4 5 pos); [exact Hfin | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; unfold crt_F; lia |].
    intros Hf. apply HnFP in Hf. unfold crt_F, CALL_SIZE in *. lia.
  - intros i Hi. rewrite (G4 5 pos); [exact (FRs i Hi) | exact Hfin | |].
    + right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Hfb. change (2048 / 8) with 256. unfold crt_SH, crt_F.
      set (f8 := frame_addr ly 5 pos / 8) in *. clearbody f8. lia.
    + intros Hf. apply HnFP in Hf. unfold crt_SH, crt_F, CALL_SIZE in *.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
      set (f8 := frame_addr ly 5 pos / 8) in *. clearbody f8. lia. }
(* the three slots, after the call *)
assert (SL : forall o v, aval_mem (rdW W (ms_mem ms)) (crt_sp1 + o) 8 v -> 104 <= o <= 120 ->
  aval_mem (rdW W2 mem2) (crt_sp1 + o) 8 v).
{ intros o v Hv Ho. apply (crt_aval_kept (rdW W (ms_mem ms))); [|exact Hv]. intros kk Hkk.
  apply G1; [lia | rewrite WS; lia | intros Hf; apply HnFP in Hf; unfold crt_F, CALL_SIZE in *; lia]. }
(* the registers after the call: callee-saved, and a0 = the call count *)
assert (Hregs2 : crt_regs regs2 (crt_RD pos)).
{ unfold crt_RD, crt_regs.
  repeat (apply Forall_cons; [cbv beta; cbn [fst snd];
    first [ replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity); exact R10'
          | lazymatch goal with |- getr _ (Z_to_bv 5 ?r) = _ => rewrite (HP2 r ltac:(unfold acallee_saved; lia)) end;
            apply (crt_reg _ _ _ _ Hregsc); unfold crts3_RM, crt_RC; cbn [app]; crt_in ] |]).
  apply Forall_nil. }
apply (HSTD ly2 S2 W2 mem2 md2 regs2 pos qs).
- unfold crt_J. replace (EV_REC_CALLS_COPY R) with (0 + EV_REC_CALLS_COPY R) by lia. exact HJ2.
- exact FR2.
- split; [exact Hlen|]. split; [exact HND|]. split; [exact Htab|].
  intros pn q0 Hpn Hq0. apply (Hap pn q0 Hpn). rewrite Hab. exact Hq0.
- rewrite <- Hab. exact Hperm.
- exact HREP2.
- exact (crts3_quit W2 mem2 KI2).
- exact KI2.
- exact KB2.
- lia.
- replace (XM_REC_CALLS_COPY MT R) with (0 + XM_REC_CALLS_COPY MT R) by lia. exact (mle_station MT S Sc S2 0 _ MTL Hmo MLE2).
- exact Hws.
- exact Hact.
- unfold crt_slots. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd];
    apply SL; first [assumption | lia].
- exact Hregs2.
Qed.
Lemma crt_s3 : ST_D -> ST_EPI -> ST_C.
Proof.
intros HSTD HEPI Sc mc dc rX pos HJ Hab Hnev Hbb Hmo Hfr KI KB HR.
pose proof crt_sp0 as (S1 & S2 & S3 & S4 & S5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _). pose proof Hstk as (_ & _ & _ & Hslo & Hshi & H47 & _).
pose proof (crts3_seed Sc mc dc rX pos HJ Hab KI KB HR) as HS.
assert (HEI : img_env VAL A_LIM (crts3_E rX)) by (unfold crts3_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 27 0) [] (crts3_E rX) (mrestrict (w_H W) mc)) by (unfold sh_ok; apply Forall_nil).
assert (Kc : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) mc a = aview SEGS (w_H W) mc a) by reflexivity.
assert (E27 : ew (crts3_E rX) 27 = Z_to_bv 64 SB) by (apply (crts3_Ereg rX pos HR 27 SHADOW_OFF); [unfold crt_RC; crt_in | lia]).
assert (E22 : ew (crts3_E rX) 22 = Z_to_bv 64 W0) by (apply (crts3_Ereg rX pos HR 22 W0); [unfold crt_RC; crt_in | lia]).
assert (E32 : ew (crts3_E rX) 32 = Z_to_bv 64 (Z.of_nat (length ws))) by exact (crts3_EX rX 0 ltac:(lia)).
assert (E33 : ew (crts3_E rX) 33 = Z_to_bv 64 A_G_QUITTING) by exact (crts3_EX rX 1 ltac:(lia)).
assert (E34 : ew (crts3_E rX) 34 = Z_to_bv 64 q) by exact (crts3_EX rX 2 ltac:(lia)).
assert (E35 : ew (crts3_E rX) 35 = Z_to_bv 64 A_G_REC) by exact (crts3_EX rX 3 ltac:(lia)).
assert (E36 : ew (crts3_E rX) 36 = Z_to_bv 64 crt_nC) by exact (crts3_EX rX 4 ltac:(lia)).
assert (HnC : 0 <= crt_nC <= 2) by (unfold crt_nC; lia).
pose proof HJ as HJ0.
unfold cfgP. unfold crt_J in HJ.
(* 0x88124 .. 0x8813c: n's check and load *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem mkst]. rewrite <- (aview_rd_of SEGS).
  rewrite (U_atom _ 27 SB E27) by (unfold SB; lia). rewrite (U_atom_off _ 22 W0 24 E22) by lia.
  apply (crts3_stack_ra ly Sc W mc dc); [exact (proj1 HJ) | rewrite crt_STK in Hslo; lia | lia]. }
{ awr_ok_tac. }
crts3_upd. clear_md.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* beqz taken: n = 0, on to the shared epilogue 0x88314 *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 7728.
  { awr_ok_tac. }
  crts3_upd. clear_md. pmkst HS.
  destruct (crts3_go pos Sc mc _ dc alloc_ceiling alloc_ceiling HJ0 (Z.le_refl _) ltac:(lia) (fun a Ha _ => Kc a Ha) Hfr KI KB)
    as (FR' & KI' & KB').
  apply (crts3_skip HEPI Sc _ _ _ pos HJ Hab Hbb Hmo FR' KI' KB').
  apply (crts3_keep_regs rX _ _ (w_H W) _ [2; 8; 3; 4; 18; 20; 21] _ HS ltac:(crts3_old) ltac:(vm_compute; reflexivity)).
  crts3_srcregs HR.
- (* n <> 0 *)
  rewrite branch_eq_U, U_SLit in Hc. erewrite (crts3_U _ rX 32) in Hc; [| crts3_old | exact E32 | lia | lia].
  assert (Hws : ws <> []) by (intros Hn; rewrite Hn in Hc; vm_compute in Hc; discriminate Hc).
  clear Hc.
  (* 0x88140 .. 0x8815c: &g_quitting from its GOT word, its check and load *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { rewrite <- (aview_rd_of SEGS).
    erewrite (crts3_U _ rX 27 SB); [| crts3_old | exact E27 | unfold SB; lia | lia].
    erewrite (crts3_U _ rX 33 A_G_QUITTING); [| crts3_old | exact E33 | unfold A_G_QUITTING; lia | lia].
    apply (cmd_addressable_chk ly Sc W _ _ _ _ (proj1 HJ)). vm_compute. reflexivity. }
  { awr_ok_tac. }
  crts3_upd. clear_md.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* bnez taken: g_quitting <> 0, the round trip *)
    rewrite branch_ne_U, U_SLit in Hc.
    erewrite (crts3_U_sext32 _ _ q) in Hc; [| erewrite (crts3_U _ rX 34 q); [reflexivity | crts3_old | exact E34 | lia | lia] | exact HQ].
    assert (Hact : PCrt.acted_m R q = true).
    { unfold PCrt.acted_m. destruct (Z.eqb_spec q 0) as [Hq0 | Hq0]; [|reflexivity].
      exfalso. rewrite Hq0 in Hc. vm_compute in Hc. discriminate Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 7328.
    { awr_ok_tac. }
    crts3_upd. clear_md. pmkst HS.
    destruct (crts3_go pos Sc mc _ dc alloc_ceiling alloc_ceiling HJ0 (Z.le_refl _) ltac:(lia) (fun a Ha _ => Kc a Ha) Hfr KI KB)
      as (FR' & KI' & KB').
    apply (crts3_main HSTD Sc _ _ _ pos HJ Hab Hnev Hbb Hmo FR' KI' KB'); [| exact Hws | exact Hact].
    unfold crts3_RM, crt_regs. apply Forall_app. split.
    * apply (crts3_keep_regs rX _ _ (w_H W) _ [2; 9; 8; 3; 4; 18; 19; 20; 21; 22; 23; 24; 27] _ HS
        ltac:(crts3_old) ltac:(vm_compute; reflexivity)).
      crts3_srcregs HR.
    * crts3_q2526 HS E33 E27.
  + (* g_quitting = 0 *)
    clear Hc.
    (* 0x88160 .. 0x88180: &g_rec from its GOT word, the check and load of g_rec.ncalls *)
    paj_run_tok RUN HS HJ SHOK Bspan.
    { rewrite <- (aview_rd_of SEGS).
      erewrite (crts3_U _ rX 27 SB); [| crts3_old | exact E27 | unfold SB; lia | lia].
      erewrite (crts3_Uoff _ rX 35 A_G_REC 8); [| crts3_old | exact E35 | unfold A_G_REC; lia | unfold A_G_REC; lia | lia].
      apply (cmd_addressable_chk ly Sc W _ _ _ _ (proj1 HJ)). vm_compute. reflexivity. }
    { awr_ok_tac. }
    crts3_upd. clear_md.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* blez taken: no recorded call, on to the shared epilogue *)
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan 7728.
      { awr_ok_tac. }
      crts3_upd. clear_md. pmkst HS.
      destruct (crts3_go pos Sc mc _ dc alloc_ceiling alloc_ceiling HJ0 (Z.le_refl _) ltac:(lia) (fun a Ha _ => Kc a Ha) Hfr KI KB)
        as (FR' & KI' & KB').
      apply (crts3_skip HEPI Sc _ _ _ pos HJ Hab Hbb Hmo FR' KI' KB').
      apply (crts3_keep_regs rX _ _ (w_H W) _ [2; 8; 3; 4; 18; 20; 21] _ HS ltac:(crts3_old) ltac:(vm_compute; reflexivity)).
      crts3_srcregs HR.
    * (* recorded calls: the round trip *)
      rewrite crt_den_atom0 in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite E36 in Hc. cbn [sv_denot] in Hc.
      rewrite crts3_bge in Hc by lia.
      assert (Hact : PCrt.acted_m R q = true).
      { unfold PCrt.acted_m. apply orb_true_iff. right. apply negb_true_iff, Nat.eqb_neq. unfold crt_nC in Hc.
        intros H0. rewrite H0 in Hc. vm_compute in Hc. discriminate Hc. }
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan 7328.
      { awr_ok_tac. }
      crts3_upd. clear_md. pmkst HS.
      destruct (crts3_go pos Sc mc _ dc alloc_ceiling alloc_ceiling HJ0 (Z.le_refl _) ltac:(lia) (fun a Ha _ => Kc a Ha) Hfr KI KB)
        as (FR' & KI' & KB').
      apply (crts3_main HSTD Sc _ _ _ pos HJ Hab Hnev Hbb Hmo FR' KI' KB'); [| exact Hws | exact Hact].
      unfold crts3_RM, crt_regs. apply Forall_app. split.
      -- apply (crts3_keep_regs rX _ _ (w_H W) _ [2; 9; 8; 3; 4; 18; 19; 20; 21; 22; 23; 24; 27] _ HS
           ltac:(crts3_old) ltac:(vm_compute; reflexivity)).
         crts3_srcregs HR.
      -- crts3_q2526 HS E33 E27.
Qed.
(* ---------- segment s4 helpers: 0x88198 .. the strdup wrapper (0x88220) ---------- *)
(* the symbolic state at 0x88198: s10 the shadow of g_quitting; the stack window s1 + 24 .. s1 + 104 the run writes; the
   GOT word of g_rec (atom 33); g_quitting (atom 32 = q); g_rec.reply / .state / .host (atoms 34, 35, 36) *)
Definition crts4_shq : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 27 0).
Definition crts4_ss : sstate := mkSS 7348 (sr_set sr_atoms (Z_to_bv 5 26) crts4_shq)
  [YP09.mkRegion (Some 9%nat) 0 256 24 104 [];
   YP09.mkRegion (Some (A_OBJ 2)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
   YP09.mkRegion (Some 25%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))];
   YP09.mkRegion (Some 33%nat) 928 960 0 0 [YP09.mkChunk 928 (CVal 8 (SOff 34 0)); YP09.mkChunk 944 (CVal 8 (SOff 35 0));
     YP09.mkChunk 952 (CVal 8 (SOff 36 0))]] None
  (mkFacts [(2%nat, mkAF (2^46) (2^47) 5); (9%nat, mkAF (2^46) (2^47) 5); (27%nat, mkAF SB SB 0);
            (25%nat, mkAF 0x5e3c60 0x5e3c60 3); (33%nat, mkAF 0x5e3740 0x5e3740 3); (32%nat, mkAF 0 (2^32 - 1) 0);
            (34%nat, mkAF 4096 (2^47) 0)] [] []).
Definition crts4_extra (rp : Z) : list word := [w64 q; w64 A_G_REC; w64 rp; w64 (r_state R); w64 (r_host R)].
Definition crts4_E (rX : bvmap 5 word) (rp : Z) : env := Eimg (Ereg rX (crts4_extra rp)).
Lemma crts4_E_atoms : forall rX rp,
  ew (crts4_E rX rp) 32 = w64 q /\ ew (crts4_E rX rp) 33 = w64 A_G_REC /\ ew (crts4_E rX rp) 34 = w64 rp /\
  ew (crts4_E rX rp) 35 = w64 (r_state R) /\ ew (crts4_E rX rp) 36 = w64 (r_host R).
Proof.
intros rX rp. unfold crts4_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
exact (conj (ew_Ereg_extra rX _ 0) (conj (ew_Ereg_extra rX _ 1) (conj (ew_Ereg_extra rX _ 2)
  (conj (ew_Ereg_extra rX _ 3) (ew_Ereg_extra rX _ 4))))).
Qed.
Lemma crts4_U_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + k < 2 ^ 64 ->
  U E (SOff n k) = v + k.
Proof. intros E n v k H Hv Hk. rewrite U_SOff, H, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. Qed.
(* the record's statics *)
Lemma crts4_gq_pg : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> inFP cmd_PG a.
Proof.
intros a H. exists (A_G_QUITTING, A_G_QUITTING + 4). split; [right; right; left; reflexivity | cbn [fst snd]; lia].
Qed.
(* a run whose only write window is s1 + 24 .. s1 + 104 keeps every other byte *)
Lemma crts4_frame_win : forall E rs H (m m' : word -> option byte), frame_of E rs (mrestrict H m) (mrestrict H m') ->
 bv_unsigned (ew E 9) = crt_sp1 ->
 (forall b wlo whi, In (b, wlo, whi) (windows rs) -> whi <= wlo \/ (b = Some 9%nat /\ wlo = 24 /\ whi = 104)) ->
 forall a, 0 <= a < 2 ^ 64 -> ~ (crt_sp1 + 24 <= a < crt_sp1 + 104) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hsp Hw a Ha Hn.
apply (kept_of_frame E rs H m m' (fun a => crt_sp1 + 24 <= a < crt_sp1 + 104) HF); [|exact Ha | exact Hn].
intros b wlo whi a' Hin Hr. destruct (Hw b wlo whi Hin) as [Hl | (-> & -> & ->)]; [lia|].
cbn [base_val] in Hr. rewrite Hsp in Hr. lia.
Qed.
(* the recorder's representation over a larger block list, its bytes kept *)
Lemma crts4_rep_grow : forall ly1 S1 ly2 S2 (rd rd' : reader) R0 O0,
  rec_repA B ly1 S1 rd R0 O0 -> (forall a, rcf_inrec a -> rd' a = rd a) ->
  (forall pn, In pn (ablocks B ly1 S1) -> In pn (ablocks B ly2 S2)) ->
  (forall p n i, In (p, n) (ablocks B ly1 S1) -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
  rec_repA B ly2 S2 rd' R0 O0.
Proof.
intros ly1 S1 ly2 S2 rd rd' R0 O0 (Q & HA & HO) K Hsub HK.
exists Q. split; [|exact HO].
destruct HA as (H1 & H2 & H3 & HC & HAn & HRp & HX & HW).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
assert (KG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; left; exact Hx).
assert (KS : forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; right; exact Hx).
assert (KB : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly1 S1) ->
  In pn (ablocks B ly2 S2) /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros [p n] _ Hb. split; [exact (Hsub _ Hb)|]. intros i Hi. exact (HK p n i Hb Hi). }
unfold arep_at. refine (conj H1 (conj H2 (conj H3 (conj _ (conj _ (conj _ (conj _ HW))))))).
- unfold ag1_calls. refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
  + apply (rcfr_aval_keep rd _ _ _ _ C3). intros k Hk. apply KG. unfold OFF_NCALLS, REC_SIZE. lia.
  + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
    assert (Hi : (i < length (r_calls R0))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
    apply (rcfr_call_keep _ _ rd rd' _ c P Hc).
    * intros x Hx. apply KG. unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
    * intros pn Hpn Hb. apply KB; [|exact Hb]. unfold lay_blocks. apply in_or_app. left.
      apply in_concat. exists P. split; [exact (nth_error_In _ _ EP) | exact Hpn].
  + apply (rcfr_call_keep _ _ rd rd' _ _ _ C5).
    * intros x Hx. apply KS. unfold CALL_SIZE, SC_SIZE in *. lia.
    * intros pn Hpn Hb. apply KB; [|exact Hb]. unfold lay_blocks. apply in_or_app. right.
      apply in_or_app. left. exact Hpn.
- apply (rcfr_answer_keep _ _ rd rd' _ _ _ HAn).
  + intros x Hx. apply KG. unfold OFF_ANSWER, REC_SIZE in *. lia.
  + intros pn Hpn Hb. apply KB; [|exact Hb]. unfold lay_blocks. apply in_or_app. right.
    apply in_or_app. right. apply in_or_app. left. exact Hpn.
- apply (rcfr_reply_keep _ _ rd rd' _ _ _ HRp).
  + intros x Hx. apply KG. unfold OFF_REPLY, OFF_REPLY_SIZE, REC_SIZE in *. lia.
  + intros pn Hpn Hb. apply KB; [|exact Hb]. unfold lay_blocks. apply in_or_app. right.
    apply in_or_app. right. apply in_or_app. right. exact Hpn.
- apply (rcfr_scalars_keep rd _ _ _ HX). intros x Hx. apply KG. unfold REC_SIZE. lia.
Qed.
(* the block strdup returns is apart from every block of the call's state *)
Lemma crts4_new_apart : forall (bl : list (Z * Z)) p m res n,
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (bl ++ [(res, n)])) -> In (p, m) bl ->
  zdisjoint (p, req_size m) (res, req_size n).
Proof.
intros bl p m res n Hp Hin. apply in_split in Hin as (l1 & l2 & ->).
apply (pairwise_In2 zdisjoint _ _ _ (map (fun b : Z * Z => (fst b, req_size (snd b))) l1)
  (map (fun b : Z * Z => (fst b, req_size (snd b))) l2) [] Hp).
rewrite <- app_assoc. cbn [app]. rewrite map_app. cbn [map]. rewrite map_app. cbn [map]. reflexivity.
Qed.
(* the strdup wrapper's rule at a call of the walk: astrdup04_rule (RtAlloc04.v) composed with the journal of the
   caller, in the form PaCall.v's amalloc04_sub has *)
Lemma crts4_strdup_sub : forall W1 regsT memT STK0 sp00 FP0 ly0 S0 W00 mem0 md0 own0 lyc Sc mdc k x s (o : Z) raw ch0,
ajournal SEGS B STK0 sp00 FP0 ly0 S0 W00 mem0 md0 own0 lyc Sc W1 memT mdc k ->
getr regsT 10 = w64 x -> 0 < x ->
astr_atR (aview SEGS (w_H W1) memT) x s ->
aread_ok SEGS ASTACK W1 regsT memT x (astr_len s + 1) ->
(forall a, x <= a < x + (astr_len s + 1) -> adup_src_kept SEGS B lyc Sc a) ->
rt_rom_view SEGS B W1 memT ->
0 <= astr_len s + 1 < MALLOC_MAX -> blocks_bytes Sc + (astr_len s + 1) <= LIVE_MAX ->
spZ regsT = sp00 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK0 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview SEGS (w_H W1) memT) regsT ch0 ->
mo_ok MT Sc (mo_malloc MT (astr_len s + 1)) ->
SRr SEGS W1 (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS___interceptor_trampoline_strdup)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK0 sp00 FP0 ly0 S0 W00 mem0 md0 own0 ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, astr_len s + 1)] /\
acall_kept SEGS B lyc Sc W1 memT W2 mem2 (sp00 + o - ASTACK) (sp00 + o)
  (fun a => res <= a < res + req_size (astr_len s + 1)) /\
abytes_atR (aview SEGS (w_H W2) mem2) res (s ++ [Z_to_bv 8 0]) /\
mo_le MT Sc S2 (mo_malloc MT (astr_len s + 1))).
Proof.
intros W1 regsT memT STK0 sp00 FP0 ly0 S0 W00 mem0 md0 own0 lyc Sc mdc k x s o raw ch0
  HJ Ha0 Hx Hstr Hread Hkept Hrom Hn Hlive Hsp Ho16 Ho Hstk Hgp Htp Hra Hraw Hnev Hch MOK0.
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
pose proof (ajournal_sub_init SEGS B STK0 sp00 FP0 ly0 S0 W00 mem0 md0 own0 lyc Sc W1 memT mdc k ASTACK (sp00 + o) [] o
  HJ eq_refl Ho16 Ho ltac:(lia) Hstk) as HJ1.
eapply SRr_mono.
{ apply (ASTRDUP4 fx W1 regsT memT ASTACK (sp00 + o) [] lyc Sc W1 memT mdc [] lyc Sc mdc 0 x s 0 raw ch0 HJ1 Ha0 Hx Hstr Hread
    Hkept Hrom Hn Hlive);
  first [exact Hgp | exact Htp | exact Hra | exact Hraw | exact Hnev | exact Hch | exact MOK0 | reflexivity | lia]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP & Hres & Hfr & Hr4 & Hbl & HK & Hby & MLE).
exists ly2, S2, regs2, mem2, md2, res. split; [reflexivity|].
split.
{ change own0 with ([] ++ own0). eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJ | exact HJ2 | lia | lia |].
  intros a (r & Hr & _). destruct Hr. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact Hr4|]. split; [exact Hbl|].
replace (sp00 + o + 0 - ASTACK) with (sp00 + o - ASTACK) in HK by lia. replace (sp00 + o + 0) with (sp00 + o) in HK by lia.
split; [exact HK|]. split; [exact Hby | exact MLE].
Qed.
Ltac crts4_slot HRg V9 off e v :=
  apply crt_aval_of_val; change 8%nat with (N.to_nat 8);
  apply (field_of_region _ _ 9%nat crt_sp1 _ 0 256 24 104 off 8%N e v HRg V9);
  [vm_compute; repeat first [left; reflexivity | right] | | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) | cbn; lia].

Lemma crt_s4 : ST_E -> ST_D.
Proof.
intros HSTE lyc Sc Wc mc dc rX pos qs HJ HFR HTBL HPM HREPc HVQc HKI HKB HBB HMO HWSn HACT HSL HRD.
pose proof crt_sp0 as (S01 & S02 & S03 & S04 & S05). pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_base_lo (L := cmd_listing)) as HBLO. pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _).
pose proof HPRE as (HAR0 & _ & _ & Hgp & Htp & _).
assert (FSB : fs_frame_bytes 5 = 2048) by reflexivity.
unfold crt_J in HJ.
pose proof HJ as (HARc & Hlyc & _ & _ & _ & Hfrc & Hnevc & _ & _ & _ & _ & _ & _ & Hstkp & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc HAR0 Hlyc) as (_ & Efa & _).
assert (Hin5 : In (5, pos) (frames Sc)) by (rewrite Hfrc; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc mc dc 5 pos HARc Hin5) as (FB1 & FB2 & _).
rewrite Efa in FB1, FB2. fold (crt_F pos) in FB1, FB2. rewrite FSB in FB2.
(* lia here treats a division as an atom (PaDenot.v turns zify's division handling off) *)
pose proof (Z.mul_div_le (crt_F pos) 8 ltac:(lia)) as DV1. pose proof (Z.div_pos (crt_F pos) 8 ltac:(lia) ltac:(lia)) as DV2.
assert (FSB8 : fs_frame_bytes 5 / 8 = 256) by reflexivity.
destruct (HREPLY HACT) as (X & HRX & HX0).
(* the reply's block, g_rec.state and g_rec.host *)
pose proof HREPc as (Qr & HA & _).
destruct HA as (_ & _ & _ & _ & _ & HRPL & HSCAL & _).
rewrite HRX in HRPL.
destruct (l_reply Qr) as [[rp m]|] eqn:EQR; [|contradiction].
cbn [areply_at fst snd] in HRPL.
destruct HRPL as (RP1 & _ & RP3 & _ & RP5 & RP6 & RP7 & _).
destruct HSCAL as (_ & _ & _ & SST & SHO & _ & _ & _ & RST & RHO).
destruct (al_blocks _ _ LAWS _ _ _ _ _ rp m HARc RP5) as (Bp16 & Bp4096 & Bpceil & Bpapp & Bppres & _ & Bm).
pose proof (req_size_pos m ltac:(lia)) as [Rq1 Rq2].
rewrite length_app in RP6. cbn [length] in RP6.
assert (HXl : Z.of_nat (length X) + 1 <= m) by lia.
(* the registers and slots at 0x88198 *)
unfold crt_regs, crt_RD in HRD.
apply Forall_cons_iff in HRD as [R2 HRD]. apply Forall_cons_iff in HRD as [R9 HRD].
apply Forall_cons_iff in HRD as [R8 HRD]. apply Forall_cons_iff in HRD as [R3 HRD].
apply Forall_cons_iff in HRD as [R4 HRD]. apply Forall_cons_iff in HRD as [R10 HRD].
apply Forall_cons_iff in HRD as [R18 HRD]. apply Forall_cons_iff in HRD as [R19 HRD].
apply Forall_cons_iff in HRD as [R20 HRD]. apply Forall_cons_iff in HRD as [R21 HRD].
apply Forall_cons_iff in HRD as [R23 HRD]. apply Forall_cons_iff in HRD as [R25 HRD].
apply Forall_cons_iff in HRD as [R26 HRD]. apply Forall_cons_iff in HRD as [R27 _].
cbn [fst snd] in R2, R9, R8, R3, R4, R10, R18, R19, R20, R21, R23, R25, R26, R27.
unfold crt_slots in HSL.
apply Forall_cons_iff in HSL as [SL104 HSL]. apply Forall_cons_iff in HSL as [SL112 HSL].
apply Forall_cons_iff in HSL as [SL120 _]. cbn [fst snd] in SL104, SL112, SL120.
(* the valuation of the seed *)
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (crts4_E rX rp) n = getr rX r)
  by (intros n0 r0 Hn0; unfold crts4_E; apply ew_Eimg_Ereg_nat; exact Hn0).
destruct (crts4_E_atoms rX rp) as (E32 & E33 & E34 & E35 & E36).
assert (HEI : img_env VAL A_LIM (crts4_E rX rp)) by (unfold crts4_E; apply Eimg_env).
assert (E2 : ew (crts4_E rX rp) 2 = w64 crt_sp1) by (rewrite (ER 2%nat (Z_to_bv 5 2) eq_refl); exact R2).
assert (E9 : ew (crts4_E rX rp) 9 = w64 crt_sp1) by (rewrite (ER 9%nat (Z_to_bv 5 9) eq_refl); exact R9).
assert (E8 : ew (crts4_E rX rp) 8 = w64 sp0) by (rewrite (ER 8%nat (Z_to_bv 5 8) eq_refl); exact R8).
assert (E3 : ew (crts4_E rX rp) 3 = w64 (as_gp B)) by (rewrite (ER 3%nat (Z_to_bv 5 3) eq_refl); exact R3).
assert (E4 : ew (crts4_E rX rp) 4 = w64 (as_tp B)) by (rewrite (ER 4%nat (Z_to_bv 5 4) eq_refl); exact R4).
assert (E10 : ew (crts4_E rX rp) 10 = w64 crt_nC) by (rewrite (ER 10%nat (Z_to_bv 5 10) eq_refl); exact R10).
assert (E18 : ew (crts4_E rX rp) 18 = w64 (crt_F pos)) by (rewrite (ER 18%nat (Z_to_bv 5 18) eq_refl); exact R18).
assert (E20 : ew (crts4_E rX rp) 20 = w64 (crt_F pos)) by (rewrite (ER 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (E21 : ew (crts4_E rX rp) 21 = w64 (crt_SH pos + 4)) by (rewrite (ER 21%nat (Z_to_bv 5 21) eq_refl); exact R21).
assert (E23 : ew (crts4_E rX rp) 23 = w64 hb) by (rewrite (ER 23%nat (Z_to_bv 5 23) eq_refl); exact R23).
assert (E25 : ew (crts4_E rX rp) 25 = w64 A_G_QUITTING) by (rewrite (ER 25%nat (Z_to_bv 5 25) eq_refl); exact R25).
assert (E27 : ew (crts4_E rX rp) 27 = w64 SHADOW_OFF) by (rewrite (ER 27%nat (Z_to_bv 5 27) eq_refl); exact R27).
assert (HQ64 : 0 <= q < 2 ^ 64) by lia.
assert (HNC2 : 0 <= crt_nC <= 2) by (unfold crt_nC; lia).
assert (U2 : bv_unsigned (ew (crts4_E rX rp) 2) = crt_sp1) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew (crts4_E rX rp) 9) = crt_sp1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew (crts4_E rX rp) 25) = A_G_QUITTING)
  by (rewrite E25; apply unsigned_lit_small; unfold A_G_QUITTING; lia).
assert (U27 : bv_unsigned (ew (crts4_E rX rp) 27) = SHADOW_OFF)
  by (rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew (crts4_E rX rp) 32) = q) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (crts4_E rX rp) 33) = A_G_REC) by (rewrite E33; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (U34 : bv_unsigned (ew (crts4_E rX rp) 34) = rp) by (rewrite E34; apply unsigned_lit_small; lia).
assert (VG : VAL (A_OBJ 2) = 0xa7068).
{ rewrite (HVAL 2%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)). vm_compute. reflexivity. }
assert (UG : bv_unsigned (ew (crts4_E rX rp) (A_OBJ 2)) = 0xa7068).
{ unfold crts4_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite VG. apply unsigned_lit_small. lia. }
(* the GOT word, read through the read-only bytes at this state *)
assert (HGOT : aval_mem (rdW Wc mc) 0xa7068 8 A_G_REC)
  by (apply crt_got_r; exact (cmd_ro_ok_of_aro SEGS B LAWS HB IMG _ _ _ _ _ (proj1 HJ) (crt_rod _ _ _ _ _ _ _ HJ))).
assert (HS : st_ok_pi SEGS VAL (crts4_E rX rp) crts4_ss
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + 7348)) mc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold crts4_ss. apply pa_entry_st_ok_full.
  - intros r. destruct (decide (r = Z_to_bv 5 26)) as [->|Hne].
    + rewrite sr_get_set_same by reflexivity. rewrite R26. unfold crts4_shq.
      rewrite (denot_shx _ 25 27 0 A_G_QUITTING SHADOW_OFF E25 E27) by (unfold A_G_QUITTING, SHADOW_OFF; lia).
      rewrite Z.add_0_r. reflexivity.
    + rewrite sr_get_set_other by exact Hne. exact (regs_ok_Eimg_Ereg rX (crts4_extra rp) r).
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hstkp. rewrite crt_STK. lia.
    + rewrite UG. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS _ _ 0xa7068 0 8 (SOff 33 0) A_G_REC);
        [rewrite crt_den_atom0, E33; reflexivity | unfold A_G_REC; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply crt_val_of_aval. exact HGOT.
    + rewrite U25. split; [unfold A_G_QUITTING; lia|]. split; [unfold A_G_QUITTING; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS _ _ A_G_QUITTING 0 4 (SOff 32 0) q);
        [rewrite crt_den_atom0, E32; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply crt_val_of_aval. exact HVQc.
    + rewrite U33. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val SEGS _ _ A_G_REC 928 8 (SOff 34 0) rp);
          [rewrite crt_den_atom0, E34; reflexivity | cbn; lia | cbn; lia |].
        apply crt_val_of_aval. exact RP1.
      * apply (chunk_ok_val SEGS _ _ A_G_REC 944 8 (SOff 35 0) (r_state R));
          [rewrite crt_den_atom0, E35; reflexivity | cbn; lia | cbn; lia |].
        apply crt_val_of_aval. exact SST.
      * apply (chunk_ok_val SEGS _ _ A_G_REC 952 8 (SOff 36 0) (r_host R));
          [rewrite crt_den_atom0, E36; reflexivity | cbn; lia | cbn; lia |].
        apply crt_val_of_aval. exact SHO.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, UG, U25, U33.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_G_REC, A_G_QUITTING. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U27, U25, U33, U32, U34.
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB, SHADOW_OFF, A_G_QUITTING, A_G_REC. repeat split; try lia. }
assert (SHOK : sh_ok SEGS (SOff 27 0) [] (crts4_E rX rp) (mrestrict (w_H Wc) mc)) by (unfold sh_ok; apply Forall_nil).
assert (UB : U (crts4_E rX rp) (SOff 27 0) = SHADOW_OFF)
  by (apply U_atom; [exact E27 | unfold SHADOW_OFF; lia]).
assert (UQ : U (crts4_E rX rp) (SOff 25 0) = A_G_QUITTING)
  by (apply U_atom; [exact E25 | unfold A_G_QUITTING; lia]).
assert (U928 : U (crts4_E rX rp) (SOff 33 928) = A_G_REC + 928)
  by (apply crts4_U_off; [exact E33 | unfold A_G_REC; lia | unfold A_G_REC; lia]).
assert (U944 : U (crts4_E rX rp) (SOff 33 944) = A_G_REC + 944)
  by (apply crts4_U_off; [exact E33 | unfold A_G_REC; lia | unfold A_G_REC; lia]).
assert (U952 : U (crts4_E rX rp) (SOff 33 952) = A_G_REC + 952)
  by (apply crts4_U_off; [exact E33 | unfold A_G_REC; lia | unfold A_G_REC; lia]).
unfold cfgP.
(* 0x88198 .. 0x88220: the slots, the four shadow checks, the loads of g_rec's reply, state and host *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ apply (obl_of_range SEGS _ _ _ _ _ _ (A_G_REC + 928) 8);
    [apply (cmd_addressable_chk _ _ _ _ _ (A_G_REC + 928) 8 HARc); vm_compute; reflexivity | exact UB | rewrite U928; lia | rewrite U928; lia]. }
{ apply (obl_of_range SEGS _ _ _ _ _ _ (A_G_REC + 952) 8);
    [apply (cmd_addressable_chk _ _ _ _ _ (A_G_REC + 952) 8 HARc); vm_compute; reflexivity | exact UB | rewrite U952; lia | rewrite U952; lia]. }
{ apply (obl_of_range SEGS _ _ _ _ _ _ (A_G_REC + 944) 8);
    [apply (cmd_addressable_chk _ _ _ _ _ (A_G_REC + 944) 8 HARc); vm_compute; reflexivity | exact UB | rewrite U944; lia | rewrite U944; lia]. }
{ apply (obl_of_range SEGS _ _ _ _ _ _ A_G_QUITTING 4);
    [apply (cmd_addressable_chk _ _ _ _ _ A_G_QUITTING 4 HARc); vm_compute; reflexivity | exact UB | rewrite UQ; lia | rewrite UQ; lia]. }
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 9%nat (crt_sp1 - sp0));
    [reflexivity | rewrite U9; lia | cbn -[CHECK_ROUND_TRIP_STK crt_sp1 spZ]; rewrite crt_STK; lia
    | cbn -[CHECK_ROUND_TRIP_STK crt_sp1 spZ]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (crts4_frame_win _ _ _ _ _ HFr U9 ltac:(crt_winstk)) as K0. clear HF HFr HG. clear_md.
pose proof HJ as (HARr & _).
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E' := Ex) in * end.
assert (AG : forall n, (n < 64)%nat -> ew E' n = ew (crts4_E rX rp) n)
  by (intros n Hn; unfold E'; repeat rewrite ew_ewset_other by lia; reflexivity).
clearbody E'.
assert (HEI' : img_env VAL A_LIM E') by (lazymatch goal with H : img_env _ _ E' |- _ => exact H end).
assert (F2 : ew E' 2 = w64 crt_sp1) by (rewrite AG by lia; exact E2).
assert (F9 : ew E' 9 = w64 crt_sp1) by (rewrite AG by lia; exact E9).
assert (F8 : ew E' 8 = w64 sp0) by (rewrite AG by lia; exact E8).
assert (F3 : ew E' 3 = w64 (as_gp B)) by (rewrite AG by lia; exact E3).
assert (F4 : ew E' 4 = w64 (as_tp B)) by (rewrite AG by lia; exact E4).
assert (F10 : ew E' 10 = w64 crt_nC) by (rewrite AG by lia; exact E10).
assert (F18 : ew E' 18 = w64 (crt_F pos)) by (rewrite AG by lia; exact E18).
assert (F20 : ew E' 20 = w64 (crt_F pos)) by (rewrite AG by lia; exact E20).
assert (F21 : ew E' 21 = w64 (crt_SH pos + 4)) by (rewrite AG by lia; exact E21).
assert (F23 : ew E' 23 = w64 hb) by (rewrite AG by lia; exact E23).
assert (F25 : ew E' 25 = w64 A_G_QUITTING) by (rewrite AG by lia; exact E25).
assert (F27 : ew E' 27 = w64 SHADOW_OFF) by (rewrite AG by lia; exact E27).
assert (F32 : ew E' 32 = w64 q) by (rewrite AG by lia; exact E32).
assert (F33 : ew E' 33 = w64 A_G_REC) by (rewrite AG by lia; exact E33).
assert (F34 : ew E' 34 = w64 rp) by (rewrite AG by lia; exact E34).
assert (F35 : ew E' 35 = w64 (r_state R)) by (rewrite AG by lia; exact E35).
assert (F36 : ew E' 36 = w64 (r_host R)) by (rewrite AG by lia; exact E36).
assert (V9 : bv_unsigned (ew E' 9) = crt_sp1) by (rewrite F9; apply unsigned_lit_small; lia).
(* the slots the run wrote *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg end.
cbn [ms_mem restrict] in HRg.
assert (V96 : aval_mem (rdW Wc (ms_mem ms)) (crt_sp1 + 96) 8 crt_nC).
{ crts4_slot HRg V9 96 (SOff 10 0) crt_nC; [rewrite crt_den_atom0; exact F10 | lia]. }
assert (V88 : aval_mem (rdW Wc (ms_mem ms)) (crt_sp1 + 88) 8 (crt_shx A_G_QUITTING)).
{ crts4_slot HRg V9 88 crts4_shq (crt_shx A_G_QUITTING).
  - unfold crts4_shq. rewrite (denot_shx _ 25 27 0 A_G_QUITTING SHADOW_OFF F25 F27) by (unfold A_G_QUITTING, SHADOW_OFF; lia).
    rewrite Z.add_0_r. reflexivity.
  - unfold crt_shx. pose proof (Z.mul_div_le A_G_QUITTING 8 ltac:(lia)).
    pose proof (Z.div_pos A_G_QUITTING 8 ltac:(unfold A_G_QUITTING; lia) ltac:(lia)).
    unfold A_G_QUITTING, SHADOW_OFF in *. lia. }
assert (V80 : aval_mem (rdW Wc (ms_mem ms)) (crt_sp1 + 80) 8 (crt_sx q)).
{ crts4_slot HRg V9 80 (SExt true 32 (SOff 32 0)) (crt_sx q).
  - rewrite denot_lit_U. f_equal. rewrite U_SExt, (U_atom E' 32 q F32 HQ64).
    change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small q (2 ^ 32)) by lia. unfold crt_sx, zcanon, M64. reflexivity.
  - unfold crt_sx. apply Z.mod_pos_bound. lia. }
assert (V72 : aval_mem (rdW Wc (ms_mem ms)) (crt_sp1 + 72) 8 (r_state R)).
{ crts4_slot HRg V9 72 (SOff 35 0) (r_state R); [rewrite crt_den_atom0; exact F35 | lia]. }
assert (V64 : aval_mem (rdW Wc (ms_mem ms)) (crt_sp1 + 64) 8 (r_host R)).
{ crts4_slot HRg V9 64 (SOff 36 0) (r_host R); [rewrite crt_den_atom0; exact F36 | lia]. }
assert (V56 : aval_mem (rdW Wc (ms_mem ms)) (crt_sp1 + 56) 8 (crt_F pos)).
{ crts4_slot HRg V9 56 (SOff 20 0) (crt_F pos); [rewrite crt_den_atom0; exact F20 | lia]. }
assert (V48 : aval_mem (rdW Wc (ms_mem ms)) (crt_sp1 + 48) 8 (crt_SH pos + 4)).
{ crts4_slot HRg V9 48 (SOff 21 0) (crt_SH pos + 4); [rewrite crt_den_atom0; exact F21 | unfold crt_SH, SHADOW_OFF; lia]. }
clear HRg.
(* the registers at the call *)
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 7488)) by (crt_rreg HS; exact (codeptr_val _ 7488 HEI')).
assert (Q2 : getr (ms_regs ms) 2 = w64 crt_sp1) by (crt_rreg HS; rewrite crt_den_atom0; exact F2).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (crt_rreg HS; rewrite crt_den_atom0; exact F3).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (crt_rreg HS; rewrite crt_den_atom0; exact F4).
assert (Q8 : getr (ms_regs ms) 8 = w64 sp0) by (crt_rreg HS; rewrite crt_den_atom0; exact F8).
assert (Q10 : getr (ms_regs ms) 10 = w64 rp) by (crt_rreg HS; rewrite crt_den_atom0; exact F34).
(* the reply, kept by the run *)
assert (HSTR : astr_atR (rdW Wc (ms_mem ms)) rp X).
{ split; [|exact HX0]. apply (rcfr_bytes_keep (rdW Wc mc) _ _ _ RP7). intros i Hi.
  rewrite length_app in Hi. cbn [length] in Hi. apply K0; lia. }
(* the frame chain at the call: the prologue's frame record on afn_pre's chain (s0 = sp0) *)
assert (FRT : crt_frame (rdW Wc (ms_mem ms)))
  by (apply (crt_frame_keep (rdW Wc mc)); [intros a Ha; apply K0; lia | exact (proj1 HFR)]).
destruct (crt_chain pos lyc Sc Wc (ms_mem ms) _ _ HJ FRT) as (ch1 & Hch1).
(* the budgets *)
pose proof (crt_live_rcc ly S (rdW W mem) R O HREP HNC) as HLR.
pose proof (crt_ev_send_nn R (join_sp ws)) as HEVS. pose proof (crt_xm_send_nn R (join_sp ws)) as HXMS.
pose proof (crt_ev_args_nn R) as HARGS. pose proof (mo_free_nonneg MT MTL) as HMF.
pmkst HS.
eapply SRr_bind.
{ apply (crts4_strdup_sub Wc (ms_regs ms) (ms_mem ms) STK sp0 crt_FP ly S W mem md [(5, pos)] lyc Sc _
    (EV_REC_CALLS_COPY R) rp X (crt_sp1 - sp0) (Z_to_bv 64 (BASE + 7488)) ch1 HJ).
  - exact Q10.
  - lia.
  - exact HSTR.
  - apply (aread_ok_of_block SEGS B LAWS ASTACK lyc Sc Wc (ms_regs ms) (ms_mem ms) _ rp m rp (astr_len X + 1) HARr RP5);
      unfold astr_len; try lia.
    unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. unfold ASTACK. lia.
  - intros a Ha. unfold astr_len in Ha. split.
    + intros Herr. pose proof errno_low as (_ & ERRIMG & _).
      exact (blk_img SEGS B LAWS lyc Sc Wc mc dc rp m a HARc RP5 ltac:(lia) (ERRIMG a Herr)).
    + right. right. exists rp, m. split; [exact RP5 | lia].
  - exact (cmd_rom_view_on Wc (ms_mem ms) (crt_rod _ _ _ _ _ _ _ HJ)).
  - unfold astr_len, MALLOC_MAX, LMAX in *. lia.
  - unfold LIVE_CHECK_ROUND_TRIP, LIVE_JOINED, LIVE_SEND_MESSAGE, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS,
      VERBS_RECEIVE_REQ, MALLOC_MAX in HLIVE.
    unfold astr_len. unfold LMAX in *. lia.
  - unfold spZ at 1. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact P4.
  - lia.
  - unfold ASTACK. rewrite crt_STK. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold EV_CHECK_ROUND_TRIP, EV_JOINED in HEV. lia.
  - apply (achain_chain_pre lyc _ crt_sp1 sp0 ch1 (ms_regs ms) Hch1).
    + unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia.
    + unfold s0Z. rewrite Q8. unfold w64. apply unsigned_lit_small. lia.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - apply (mok_station MT S Sc (XM_CHECK_ROUND_TRIP MT R ws) (XM_REC_CALLS_COPY MT R) _ MTL MOK HMO).
    + apply (mo_malloc_nonneg MT MTL). unfold astr_len. lia.
    + unfold XM_CHECK_ROUND_TRIP.
      pose proof (mo_malloc_mono MT MTL (astr_len X + 1) (LMAX + 2) ltac:(unfold astr_len; lia)).
      assert (0 <= XM_JOINED MT ws) by (unfold XM_JOINED; apply (mo_malloc_nonneg MT MTL); pose proof (crt_jn_nn ws); lia).
      nia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Hres & Hfr2 & Hr4 & Hbl & HK & Hby & MLE).
pose proof HJ2 as (HAR2 & Hly2 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR0 Hly2) as (_ & Efa2 & _).
destruct HK as (K1 & K2 & K3 & K4 & _).
replace (sp0 + (crt_sp1 - sp0)) with crt_sp1 in K1 by lia.
assert (Hinr : In (res, astr_len X + 1) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (astr_len X + 1) HAR2 Hinr) as (_ & _ & Rceil & Rapp & _ & Hpw & _).
rewrite Hbl in Hpw.
pose proof (req_size_pos (astr_len X + 1) ltac:(unfold astr_len; lia)) as [Rr1 Rr2].
(* the new block is apart from the old blocks, the class-5 frame and its shadow *)
assert (NB : forall p m0 a, In (p, m0) (ablocks B lyc Sc) -> p <= a < p + req_size m0 ->
  ~ (res <= a < res + req_size (astr_len X + 1))).
{ intros p m0 a Hin Ha. pose proof (crts4_new_apart _ p m0 res _ Hpw Hin) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (NF : forall a, crt_F pos <= a < crt_F pos + fs_frame_bytes 5 -> ~ (res <= a < res + req_size (astr_len X + 1))).
{ intros a Ha. pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 res _ 5 pos HAR2 Hinr
    ltac:(rewrite Hfr2; exact Hin5)) as Hd.
  rewrite Efa2 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold crt_F in Ha. lia. }
assert (NS : forall a, crt_SH pos <= a < crt_SH pos + fs_frame_bytes 5 / 8 -> ~ (res <= a < res + req_size (astr_len X + 1))).
{ intros a Ha. rewrite FSB8 in Ha. unfold crt_SH in Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Rapp.
  unfold SHADOW_OFF in Ha. lia. }
(* what the call keeps *)
assert (KSw : forall a, crt_sp1 <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc (ms_mem ms) a) by (intros a Ha; apply K1; lia).
assert (KSt : forall a, crt_sp1 <= a < 2 ^ 64 -> ~ (crt_sp1 + 24 <= a < crt_sp1 + 104) -> rdW W2 mem2 a = rdW Wc mc a)
  by (intros a Ha Hn; rewrite (KSw a Ha); apply K0; lia).
assert (KIm : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  rdW W2 mem2 a = rdW Wc mc a).
{ intros a Hi Ho He. rewrite (K3 a Hi Ho He). pose proof (pa_segs_low a Hi). apply K0; lia. }
assert (KBk : forall p m0 i, In (p, m0) (ablocks B lyc Sc) -> 0 <= i < req_size m0 -> rdW W2 mem2 (p + i) = rdW Wc mc (p + i)).
{ intros p m0 i Hin Hi. rewrite (K2 p m0 i Hin Hi (NB p m0 (p + i) Hin ltac:(lia))).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m0 HARc Hin) as (_ & Hp4 & Hc & _). apply K0; lia. }
assert (KF : forall a, crt_F pos <= a < crt_F pos + fs_frame_bytes 5 \/ crt_SH pos <= a < crt_SH pos + fs_frame_bytes 5 / 8 ->
  rdW W2 mem2 a = rdW Wc mc a).
{ intros a Ha. rewrite (K4 5 pos a Hin5).
  - rewrite FSB8, FSB in Ha. unfold crt_SH, SHADOW_OFF in Ha.
    assert (a < alloc_ceiling) by lia.
    apply K0; lia.
  - destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng, shadow_addr, crt_SH, crt_F in *; cbn [fst snd];
    rewrite Efa; lia.
  - destruct Ha as [Ha | Ha]; [exact (NF a Ha) | exact (NS a Ha)]. }
apply (HSTE ly2 S2 W2 mem2 md2 regs2 pos qs res X).
- unfold crt_J. exact HJ2.
- destruct HFR as (FR1 & FR2 & FR3). split; [|split].
  + intros j r Hj. assert (Hj13 : (j < 13)%nat) by (rewrite <- crt_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
    apply (crt_aval_kept (rdW Wc mc)); [|exact (FR1 j r Hj)].
    intros kk Hkk. apply KSt; lia.
  + rewrite (rdword_ext (rdW Wc mc) (rdW W2 mem2)); [exact FR2|].
    intros kk Hkk. apply KF. left. rewrite FSB. lia.
  + intros i Hi. rewrite KF; [exact (FR3 i Hi)|]. right. rewrite FSB8. lia.
- destruct HTBL as (T1 & T2 & T3 & T4). split; [exact T1|]. split; [exact T2|]. split; [|exact T4].
  intros i c P Hc HPi. destruct (T3 i c P Hc HPi) as [Hca Hsz]. split; [|exact Hsz].
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  apply (rcfr_call_keep (ablocks B lyc Sc) (ablocks B ly2 S2) (rdW Wc mc) (rdW W2 mem2) _ c P Hca).
  + intros x Hx. apply KF. left. rewrite FSB. unfold CALL_SIZE in *. lia.
  + intros [p0 m0] Hpn Hb. split; [rewrite Hbl; apply in_or_app; left; exact Hb|].
    intros i0 Hi0. cbn [fst snd] in *.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p0 m0 HARc Hb) as (_ & _ & _ & _ & _ & _ & Hm0).
    pose proof (req_size_pos m0 ltac:(lia)) as [_ Hq0]. apply (KBk p0 m0 i0); [exact Hb | lia].
- rewrite Hbl. unfold astr_len. rewrite app_assoc. apply Permutation_app_tail. exact HPM.
- apply (crts4_rep_grow lyc Sc ly2 S2 (rdW Wc mc) (rdW W2 mem2) R O HREPc).
  + intros a Ha. pose proof (crt_inrec_pg a Ha) as Hpg. destruct (crt_pg a Hpg) as (Ho & He). exact (KIm a (cif_prog_img a Hpg) Ho He).
  + intros pn Hpn. rewrite Hbl. apply in_or_app. left. exact Hpn.
  + intros p n i Hin Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hq]. apply (KBk p n i); [exact Hin | lia].
- apply (crt_aval_kept (rdW Wc mc)); [|exact HVQc].
  intros kk Hkk. pose proof (crts4_gq_pg (A_G_QUITTING + kk) ltac:(lia)) as Hpg. destruct (crt_pg _ Hpg) as (Ho & He).
  exact (KIm _ (cif_prog_img _ Hpg) Ho He).
- intros a Hi Ho He. rewrite (KIm a Hi Ho He). exact (HKI a Hi Ho He).
- intros p n i Hin Hi. assert (Hin' : In (p, n) (ablocks B lyc Sc)).
  { apply (Permutation_in _ (Permutation_sym HPM)). apply in_or_app. left. exact Hin. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hq]. rewrite (KBk p n i Hin' ltac:(lia)). exact (HKB p n i Hin Hi).
- exact HRX.
- exact HX0.
- exact Hby.
- exact Hr4.
- assert (BB2 : blocks_bytes S2 = blocks_bytes Sc + (astr_len X + 1)).
  { rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B lyc Sc), Hbl, bsum_app. cbn [bsum fold_right snd]. lia. }
  rewrite BB2. unfold astr_len. lia.
- exact (mle_station MT S Sc S2 _ _ MTL HMO MLE).
- exact HWSn.
- exact HACT.
- unfold crt_slots, crt_SLE. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
  + apply (crt_aval_kept (rdW Wc mc)); [intros kk Hkk; apply KSt; lia | exact SL104].
  + apply (crt_aval_kept (rdW Wc mc)); [intros kk Hkk; apply KSt; lia | exact SL112].
  + apply (crt_aval_kept (rdW Wc mc)); [intros kk Hkk; apply KSt; lia | exact SL120].
  + apply (crt_aval_kept (rdW Wc (ms_mem ms))); [intros kk Hkk; apply KSw; lia | exact V96].
  + apply (crt_aval_kept (rdW Wc (ms_mem ms))); [intros kk Hkk; apply KSw; lia | exact V88].
  + apply (crt_aval_kept (rdW Wc (ms_mem ms))); [intros kk Hkk; apply KSw; lia | exact V80].
  + apply (crt_aval_kept (rdW Wc (ms_mem ms))); [intros kk Hkk; apply KSw; lia | exact V72].
  + apply (crt_aval_kept (rdW Wc (ms_mem ms))); [intros kk Hkk; apply KSw; lia | exact V64].
  + apply (crt_aval_kept (rdW Wc (ms_mem ms))); [intros kk Hkk; apply KSw; lia | exact V56].
  + apply (crt_aval_kept (rdW Wc (ms_mem ms))); [intros kk Hkk; apply KSw; lia | exact V48].
- unfold crt_regs, crt_RE. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
  + rewrite (crt_preg _ _ _ HP2) by crt_cs. crt_rreg HS. rewrite crt_den_atom0. exact F2.
  + rewrite (crt_preg _ _ _ HP2) by crt_cs. crt_rreg HS. rewrite crt_den_atom0. exact F9.
  + rewrite (crt_preg _ _ _ HP2) by crt_cs. crt_rreg HS. rewrite crt_den_atom0. exact F8.
  + rewrite (crt_preg _ _ _ HP2) by crt_cs. crt_rreg HS. rewrite crt_den_atom0. exact F3.
  + rewrite (crt_preg _ _ _ HP2) by crt_cs. crt_rreg HS. rewrite crt_den_atom0. exact F4.
  + rewrite <- Hres. f_equal; apply bv_eq; reflexivity.
  + rewrite (crt_preg _ _ _ HP2) by crt_cs. crt_rreg HS. rewrite crt_den_atom0. exact F18.
  + rewrite (crt_preg _ _ _ HP2) by crt_cs. crt_rreg HS.
    rewrite (denot_shx _ 33 27 928 A_G_REC SHADOW_OFF F33 F27) by (unfold A_G_REC, SHADOW_OFF; lia). reflexivity.
  + rewrite (crt_preg _ _ _ HP2) by crt_cs. crt_rreg HS. rewrite crt_den_atom0. exact F23.
  + rewrite (crt_preg _ _ _ HP2) by crt_cs. crt_rreg HS.
    rewrite (denot_shx _ 33 27 952 A_G_REC SHADOW_OFF F33 F27) by (unfold A_G_REC, SHADOW_OFF; lia). reflexivity.
  + rewrite (crt_preg _ _ _ HP2) by crt_cs. crt_rreg HS. rewrite crt_den_atom0. exact F33.
  + rewrite (crt_preg _ _ _ HP2) by crt_cs. crt_rreg HS. rewrite crt_den_atom0. exact F25.
  + rewrite (crt_preg _ _ _ HP2) by crt_cs. crt_rreg HS.
    rewrite (denot_shx _ 33 27 944 A_G_REC SHADOW_OFF F33 F27) by (unfold A_G_REC, SHADOW_OFF; lia). reflexivity.
  + rewrite (crt_preg _ _ _ HP2) by crt_cs. crt_rreg HS. rewrite crt_den_atom0. exact F27.
Qed.
(* ---------- s5: 0x88224 .. 0x88250, after the strdup wrapper up to joined ---------- *)
Definition crts5_shx (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff 27 0).
(* the seed at 0x88224: a0 = the strdup block (atom 10), s10 / s7 the shadow cells of g_rec + 944 / + 952 (atom 24 =
   g_rec, atom 27 = the shadow offset), slots 112 (sb, atom 32) and 120 (W0, atom 33), the two stored words *)
Definition crts5_ss : sstate := mkSS 7488
  (sr_set (sr_set sr_atoms 26 (crts5_shx (SOff 24 944))) 23 (crts5_shx (SOff 24 952)))
  [YP09.mkRegion (Some 9%nat) 0 256 0 0 [YP09.mkChunk 112 (CVal 8 (SOff 32 0)); YP09.mkChunk 120 (CVal 8 (SOff 33 0))];
   YP09.mkRegion (Some 24%nat) 944 960 944 960 []] None
  (mkFacts [(2%nat, crt_SPF); (9%nat, crt_SPF); (27%nat, mkAF SB SB 0); (24%nat, mkAF 0x5e3740 0x5e3740 3);
            (10%nat, mkAF 4096 (2^47) 4)] [] []).
Definition crts5_E (rX : bvmap 5 word) : env := Eimg (Ereg rX [w64 sb; w64 W0]).
Lemma crts5_E_reg : forall rX n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (crts5_E rX) n = getr rX r.
Proof. intros rX n r Hn. unfold crts5_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma crts5_Eat : forall rX L (n : nat) v, crt_regs rX L -> In (Z.of_nat n, v) L -> (n < 32)%nat ->
  ew (crts5_E rX) n = w64 v.
Proof.
intros rX L n v H Hin Hn. rewrite (crts5_E_reg rX n (Z_to_bv 5 (Z.of_nat n))); [exact (crt_reg rX L _ v H Hin)|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma crts5_pg_of : forall a, A_G_REC <= a < A_G_REC + 960 -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia]. Qed.
Lemma crts5_W0 : sp0 - 16 <= W0 /\ W0 + 32 <= 2 ^ 47.
Proof. destruct HPRE as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hshi & H47 & _) & _). lia. Qed.
Lemma crts5_seed : forall (Wc : world SEGS) mc rX pos res,
 crt_regs rX (crt_RE pos res) -> crt_slots Wc mc (crt_SLE pos) -> 4096 <= res <= 2 ^ 47 -> res mod 16 = 0 ->
 st_ok_pi SEGS VAL (crts5_E rX) crts5_ss (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + 7488)) mc (seg_rom SEGS))).
Proof.
intros Wc mc rX pos res HR HL Hres Hres16.
pose proof crt_sp0 as (S1 & S2 & S3 & S4 & S5). pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof crts5_W0 as (W0a & W0b).
set (E := crts5_E rX).
assert (E2 : ew E 2 = w64 crt_sp1) by (apply (crts5_Eat rX _ 2 _ HR); [unfold crt_RE; crt_in | lia]).
assert (E9 : ew E 9 = w64 crt_sp1) by (apply (crts5_Eat rX _ 9 _ HR); [unfold crt_RE; crt_in | lia]).
assert (E10 : ew E 10 = w64 res) by (apply (crts5_Eat rX _ 10 _ HR); [unfold crt_RE; crt_in | lia]).
assert (E24 : ew E 24 = w64 A_G_REC) by (apply (crts5_Eat rX _ 24 _ HR); [unfold crt_RE; crt_in | lia]).
assert (E27 : ew E 27 = w64 SHADOW_OFF) by (apply (crts5_Eat rX _ 27 _ HR); [unfold crt_RE; crt_in | lia]).
assert (E32 : ew E 32 = w64 sb) by (subst E; unfold crts5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 W0) by (subst E; unfold crts5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (U2 : bv_unsigned (ew E 2) = crt_sp1) by (rewrite E2; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = crt_sp1) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = res) by (rewrite E10; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = A_G_REC) by (rewrite E24; unfold w64; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF) by (rewrite E27; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
rewrite restrict_mkst_fx. unfold crts5_ss. apply pa_entry_st_ok_full.
- intros r.
  destruct (decide (r = 23%bv)) as [->|N23].
  { rewrite sr_get_set_same by reflexivity.
    replace (23%bv : bv 5) with (Z_to_bv 5 23) by (apply bv_eq; reflexivity).
    rewrite (crt_reg rX _ 23 _ HR) by (unfold crt_RE; crt_in).
    unfold crts5_shx. cbn [sv_denot]. rewrite E24, E27. apply bv_eq. vm_compute. reflexivity. }
  rewrite sr_get_set_other by exact N23.
  destruct (decide (r = 26%bv)) as [->|N26].
  { rewrite sr_get_set_same by reflexivity.
    replace (26%bv : bv 5) with (Z_to_bv 5 26) by (apply bv_eq; reflexivity).
    rewrite (crt_reg rX _ 26 _ HR) by (unfold crt_RE; crt_in).
    unfold crts5_shx. cbn [sv_denot]. rewrite E24, E27. apply bv_eq. vm_compute. reflexivity. }
  rewrite sr_get_set_other by exact N26.
  exact (regs_ok_Eimg_Ereg rX _ r).
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ crt_sp1 112 8 (SOff 32 0) sb);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      apply crt_val_of_aval. exact (crt_slot Wc mc _ 112 sb HL ltac:(unfold crt_SLE; crt_in)).
    * apply (chunk_ok_val SEGS E _ crt_sp1 120 8 (SOff 33 0) W0);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      apply crt_val_of_aval. exact (crt_slot Wc mc _ 120 W0 HL ltac:(unfold crt_SLE; crt_in)).
  + rewrite U24. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|].
    split; [|constructor].
    intros o Ho. apply PRW. exact (crt_pg_prog _ (crts5_pg_of (A_G_REC + o) ltac:(lia))).
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U24.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_G_REC. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, crt_SPF. cbn [af_lo af_hi af_al2].
  rewrite U2, U9, U27, U24, U10.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
  unfold SB, SHADOW_OFF, A_G_REC. repeat split; try lia.
Qed.
(* ---------- s5: list, footprint and budget facts ---------- *)
Lemma crts5_pg_rng : forall a, inFP cmd_PG a -> 0x5e3740 <= a < 0x5e3c64.
Proof.
intros a (r & Hr & Ha). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.
Lemma crts5_inFP1 : forall x y a, inFP [(x, y)] a -> x <= a < y.
Proof. intros x y a (r & [<- | []] & Hr). exact Hr. Qed.
Lemma crts5_sink1 : forall x, 0 < x -> ~ YI16.sink_open_fp [(x, x + 8)].
Proof. intros x Hx (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia. Qed.
Lemma crts5_sle_rng : forall pos o v, In (o, v) (crt_SLE pos) -> 48 <= o <= 120.
Proof.
intros pos o v Hin. unfold crt_SLE in Hin.
repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- _; lia |]). destruct Hin.
Qed.
(* ---------- s5: the recorder after the two stores sd sb, 944(g_rec) / sd hb, 952(g_rec) ---------- *)
Lemma crts5_rep_set : forall bl bl' (rd rd' : reader) R0 Q sb' hb',
  arep_at bl rd A_G_REC A_REC_SPILL R0 Q ->
  (forall a, rcf_inrec a -> ~ (A_G_REC + 944 <= a < A_G_REC + 960) -> rd' a = rd a) ->
  aval_mem rd' (A_G_REC + OFF_STATE) 8 sb' -> aval_mem rd' (A_G_REC + OFF_HOST) 8 hb' ->
  0 <= sb' < 2 ^ 64 -> 0 <= hb' < 2 ^ 64 ->
  (forall pn, In pn bl -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  arep_at bl' rd' A_G_REC A_REC_SPILL (set_host (set_state R0 sb') hb') Q.
Proof.
intros bl bl' rd rd' R0 Q sb' hb' HA K Hs Hh Hsb Hhb KB.
destruct HA as (H1 & H2 & H3 & HC & HAn & HRp & HX & HW).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
assert (KG : forall x, A_G_REC <= x < A_G_REC + 944 -> rd' x = rd x).
{ intros x Hx. apply K; [unfold rcf_inrec; left; unfold REC_SIZE; lia | lia]. }
assert (KS : forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> rd' x = rd x).
{ intros x Hx. apply K; [unfold rcf_inrec; right; exact Hx | unfold A_REC_SPILL, A_G_REC, SC_SIZE in *; lia]. }
unfold arep_at. cbn [set_host set_state r_refuse r_code r_calls r_spill r_answer r_nreplies r_reply r_state r_host].
refine (conj H1 (conj H2 (conj H3 (conj _ (conj _ (conj _ (conj _ HW))))))).
- unfold ag1_calls. refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
  + apply (rcfr_aval_keep rd _ _ _ _ C3). intros k Hk. apply KG. unfold OFF_NCALLS. lia.
  + intros i c P Ec EP. cbn [set_host set_state r_calls] in Ec. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
    assert (Hi : (i < length (r_calls R0))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
    apply (rcfr_call_keep bl bl' rd rd' _ c P Hc).
    * intros x Hx. apply KG. unfold OFF_CALLS, CALL_SIZE in *. lia.
    * intros pn _ Hb. exact (KB pn Hb).
  + apply (rcfr_call_keep bl bl' rd rd' _ _ _ C5).
    * intros x Hx. apply KS. unfold CALL_SIZE, SC_SIZE in *. lia.
    * intros pn _ Hb. exact (KB pn Hb).
- apply (rcfr_answer_keep bl bl' rd rd' _ _ _ HAn).
  + intros x Hx. apply KG. unfold OFF_ANSWER in Hx. lia.
  + intros pn _ Hb. exact (KB pn Hb).
- apply (rcfr_reply_keep bl bl' rd rd' _ _ _ HRp).
  + intros x Hx. apply KG. unfold OFF_REPLY, OFF_REPLY_SIZE in Hx. lia.
  + intros pn _ Hb. exact (KB pn Hb).
- destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  unfold ag1_scalars. cbn [set_host set_state r_refuse r_code r_nreplies r_state r_host].
  unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  split; [apply (rcfr_aval_keep rd _ _ _ _ X1); intros k Hk; apply KG; lia|].
  split; [apply (rcfr_aval_keep rd _ _ _ _ X2); intros k Hk; apply KG; lia|].
  split; [apply (rcfr_aval_keep rd _ _ _ _ X3); intros k Hk; apply KG; lia|].
  split; [exact Hs|]. split; [exact Hh|]. repeat split; lia.
Qed.
Lemma crts5_repA_set : forall ly0 S0 ly' S' (rd rd' : reader) R0 O0 sb' hb',
  rec_repA B ly0 S0 rd R0 O0 ->
  (forall a, rcf_inrec a -> ~ (A_G_REC + 944 <= a < A_G_REC + 960) -> rd' a = rd a) ->
  aval_mem rd' (A_G_REC + OFF_STATE) 8 sb' -> aval_mem rd' (A_G_REC + OFF_HOST) 8 hb' ->
  0 <= sb' < 2 ^ 64 -> 0 <= hb' < 2 ^ 64 ->
  (forall pn, In pn (ablocks B ly0 S0) -> In pn (ablocks B ly' S') /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  rec_repA B ly' S' rd' (set_host (set_state R0 sb') hb') O0.
Proof.
intros ly0 S0 ly' S' rd rd' R0 O0 sb' hb' (Q & HA & HO) K Hs Hh Hsb Hhb KB.
exists Q. split; [|exact HO]. exact (crts5_rep_set _ _ rd rd' R0 Q sb' hb' HA K Hs Hh Hsb Hhb KB).
Qed.
(* ---------- s5: joined's post (joined_c.v) at this call ---------- *)
Definition crts5_K (lyc : alayout) (Sc : astate) (Wc : world SEGS) (mc : word -> option byte) (outp : Z) :
  alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists res : Z,
 getr regs' 10 = w64 res /\ 4096 <= res < 2 ^ 64 /\
 Permutation (ablocks B ly' S') ((res, PJoinR.join_need ws + 1) :: ablocks B lyc Sc) /\
 Forall (fun qk => iv_apart res (PJoinR.join_need ws + 1) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
 in_blockA (ablocks B ly' S') res (PJoinR.join_need ws + 1) /\
 abytes_atR (rdW W' mem') res (join_sp ws ++ [Z_to_bv 8 0]) /\
 aval_mem (rdW W' mem') outp 8 (Z.of_nat (length (join_sp ws))) /\
 (forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < n -> rdW W' mem' (p + i) = rdW Wc mc (p + i)) /\
 blocks_bytes S' <= blocks_bytes Sc + LIVE_JOINED /\
 mo_le MT Sc S' (XM_JOINED MT ws).
Ltac crts5_ratom HS EE HRE :=
  crt_rreg HS; rewrite crt_den_atom0, EE by lia; apply (crts5_Eat _ _ _ _ HRE); [unfold crt_RE; crt_in | lia].

Lemma crt_s5 : ST_F -> ST_E.
Proof.
intros HSTF lyc Sc Wc mc dc rX pos qs res X HJ Hfr Htbl HPm HREPc HVQc HKI HKB HRPL HX0 HRES H4096 HBB HMLE Hws Hact HSL HRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof crt_sp0 as (S1 & S2a & S3 & S4 & S5). pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof crts5_W0 as (W0a & W0b).
pose proof pa_B_ok as (HB0 & HB1 & _).
assert (Hfs : fs_frame_bytes 5 = 2048) by reflexivity.
assert (HAS : ASTACK = 16384) by reflexivity.
unfold crt_J in HJ.
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc HAR Hly) as (_ & Efa & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HinSc : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B lyc Sc)).
{ intros pn Hp. eapply Permutation_in; [apply Permutation_sym; exact HPm|]. apply in_or_app; left; exact Hp. }
assert (HinRS : forall pn, In pn rest -> In pn (ablocks B ly S)).
{ intros pn Hp. eapply Permutation_in; [apply Permutation_sym; exact HPERM|]. apply in_or_app; right; exact Hp. }
assert (Hresin : In (res, Z.of_nat (length X) + 1) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPm|]. apply in_or_app; right. apply in_or_app; right. left; reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hresin) as (Hres16 & _ & Hresc & _).
pose proof (req_size_pos (Z.of_nat (length X) + 1) ltac:(lia)) as [Hrq1 Hrq2].
pose proof (crts5_seed Wc mc rX pos res HRE HSL ltac:(lia) Hres16) as HS.
set (E := crts5_E rX) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold crts5_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 27 0) [] E (mrestrict (w_H Wc) mc)) by (unfold sh_ok; apply Forall_nil).
assert (E9 : ew E 9 = w64 crt_sp1) by (apply (crts5_Eat rX _ 9 _ HRE); [unfold crt_RE; crt_in | lia]).
assert (E22 : ew E 22 = w64 hb) by (apply (crts5_Eat rX _ 22 _ HRE); [unfold crt_RE; crt_in | lia]).
assert (E24 : ew E 24 = w64 A_G_REC) by (apply (crts5_Eat rX _ 24 _ HRE); [unfold crt_RE; crt_in | lia]).
assert (E27 : ew E 27 = w64 SHADOW_OFF) by (apply (crts5_Eat rX _ 27 _ HRE); [unfold crt_RE; crt_in | lia]).
assert (E32 : ew E 32 = w64 sb) by (subst E; unfold crts5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 W0) by (subst E; unfold crts5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (U24 : bv_unsigned (ew E 24) = A_G_REC) by (rewrite E24; unfold w64; apply unsigned_lit_small; unfold A_G_REC; lia).
unfold cfgP.
(* 0x88224 .. 0x88250: the abort edge (a0 >= 4096), the two checked stores, a1 = s1 + 144, a0 = W0, the call *)
paj_run_tok RUN HS HJ SHOK Bspan.
1-2: cbn [ms_mem mkst]; rewrite <- (aview_rd_of SEGS);
  rewrite (U_atom_off E 27 SHADOW_OFF 0 E27), (U_atom_off E 24 A_G_REC _ E24) by (unfold SHADOW_OFF, A_G_REC; lia);
  rewrite Z.add_0_r; apply (cmd_addressable_chk lyc Sc Wc mc dc _ _ HARc); vm_compute; reflexivity.
{ unfold crts5_ss. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U24 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. unfold awr_byte, awr_prog_or_caller. right; right; right; right. left.
  pose proof (crts5_pg_of a ltac:(lia)) as Hpg.
  split; [unfold crt_FP; apply inFP_app; right; exact Hpg|].
  split; [exact (crt_pg_prog a Hpg) | exact (cif_prog_img a Hpg)]. }
clear_md.
assert (EE : forall n, (n < 1024)%nat -> ew (ewset (ewset E 1024 w) 1025 w0) n = ew E n)
  by (intros n Hn; rewrite !ew_ewset_other by lia; reflexivity).
(* the run wrote g_rec + 944 .. + 960 only *)
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_REC + 944 <= a < A_G_REC + 960) -> rdW Wc (ms_mem ms) a = rdW Wc mc a).
{ intros a Ha Hn. apply (kept_of_frame E (ss_mem crts5_ss) (w_H Wc) mc (ms_mem ms) (fun x => A_G_REC + 944 <= x < A_G_REC + 960) HFr);
    [|exact Ha | exact Hn].
  intros b wlo whi a' Hin Hr. unfold crts5_ss in Hin. vm_compute in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hr; try rewrite U24 in Hr; lia |]).
  destruct Hin. }
(* the two stored words *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRg end.
cbn [ms_mem restrict] in HRg.
assert (HVsb : aval_mem (rdW Wc (ms_mem ms)) (A_G_REC + 944) 8 sb).
{ apply crt_aval_of_val. change 8%nat with (N.to_nat 8).
  apply (field_of_region _ _ 24 A_G_REC _ 944 960 944 960 944 8 (SOff 32 0) sb HRg).
  - rewrite EE by lia. exact U24.
  - right; left; reflexivity.
  - rewrite crt_den_atom0, EE by lia. exact E32.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HSB.
  - cbn; lia. }
assert (HVhb : aval_mem (rdW Wc (ms_mem ms)) (A_G_REC + 952) 8 hb).
{ apply crt_aval_of_val. change 8%nat with (N.to_nat 8).
  apply (field_of_region _ _ 24 A_G_REC _ 944 960 944 960 952 8 (SOff 22 0) hb HRg).
  - rewrite EE by lia. exact U24.
  - left; reflexivity.
  - rewrite crt_den_atom0, EE by lia. exact E22.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HHB.
  - cbn; lia. }
clear HRg.
(* the registers at the call *)
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 7536)) by (crt_rreg HS; apply (codeptr_val _ 7536 HEI0)).
assert (R2 : getr (ms_regs ms) 2 = w64 crt_sp1) by crts5_ratom HS EE HRE.
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by crts5_ratom HS EE HRE.
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by crts5_ratom HS EE HRE.
assert (R8 : getr (ms_regs ms) 8 = w64 sp0) by crts5_ratom HS EE HRE.
assert (R10 : getr (ms_regs ms) 10 = w64 W0) by (crt_rreg HS; rewrite crt_den_atom0, EE by lia; exact E33).
assert (R11 : getr (ms_regs ms) 11 = w64 (crt_sp1 + 144))
  by (crt_rreg HS; unfold w64; apply (crt_den_off _ 9 crt_sp1 144); [rewrite EE by lia; exact E9 | lia]).
assert (Z2 : getr (ms_regs ms) (Z_to_bv 5 2) = w64 crt_sp1) by crts5_ratom HS EE HRE.
assert (Z9 : getr (ms_regs ms) (Z_to_bv 5 9) = w64 crt_sp1) by crts5_ratom HS EE HRE.
assert (Z8 : getr (ms_regs ms) (Z_to_bv 5 8) = w64 sp0) by crts5_ratom HS EE HRE.
assert (Z3 : getr (ms_regs ms) (Z_to_bv 5 3) = w64 (as_gp B)) by crts5_ratom HS EE HRE.
assert (Z4 : getr (ms_regs ms) (Z_to_bv 5 4) = w64 (as_tp B)) by crts5_ratom HS EE HRE.
assert (Z18 : getr (ms_regs ms) (Z_to_bv 5 18) = w64 (crt_F pos)) by crts5_ratom HS EE HRE.
assert (Z20 : getr (ms_regs ms) (Z_to_bv 5 20) = w64 (crt_shx (A_G_REC + 928))) by crts5_ratom HS EE HRE.
assert (Z21 : getr (ms_regs ms) (Z_to_bv 5 21) = w64 res) by crts5_ratom HS EE HRE.
assert (Z24 : getr (ms_regs ms) (Z_to_bv 5 24) = w64 A_G_REC) by crts5_ratom HS EE HRE.
assert (Z25 : getr (ms_regs ms) (Z_to_bv 5 25) = w64 A_G_QUITTING) by crts5_ratom HS EE HRE.
assert (Z27 : getr (ms_regs ms) (Z_to_bv 5 27) = w64 SHADOW_OFF) by crts5_ratom HS EE HRE.
assert (Z23 : getr (ms_regs ms) (Z_to_bv 5 23) = w64 (crt_shx (A_G_REC + 952)))
  by (crt_rreg HS; cbn [sv_denot]; rewrite !EE by lia; rewrite E24, E27; apply bv_eq; vm_compute; reflexivity).
assert (Z26 : getr (ms_regs ms) (Z_to_bv 5 26) = w64 (crt_shx (A_G_REC + 944)))
  by (crt_rreg HS; cbn [sv_denot]; rewrite !EE by lia; rewrite E24, E27; apply bv_eq; vm_compute; reflexivity).
pmkst HS.
rewrite (SIGP CS_joined ltac:(vm_compute; tauto)).
replace (cmd_af CS_joined) with AF_joined by (vm_compute; reflexivity).
set (rT := ms_regs ms) in *. set (mT := ms_mem ms) in *.
assert (HspT : spZ rT = crt_sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
pose proof HJ as (HARt & _ & _ & _ & _ & _ & HnevT & _ & F1 & _).
(* the entry's blocks and the caller's stack above sp0, at the call *)
assert (KBS : forall p n x, In (p, n) (ablocks B ly S) -> p <= x < p + n -> rdW Wc mT x = rdW W mem x).
{ intros p n x Hin Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hp4 & Hpc & _ & _ & _ & Hm).
  pose proof (req_size_pos n (proj1 Hm)) as [_ Hq].
  rewrite K0; [| lia | intros Hg; exact (blk_img SEGS B LAWS ly S W mem md p n x HAR Hin ltac:(lia)
    (cif_prog_img x (crts5_pg_of x ltac:(lia))))].
  replace x with (p + (x - p)) by lia. exact (HKB p n (x - p) Hin ltac:(lia)). }
assert (KST : forall x, sp0 <= x < 2 ^ 64 -> rdW Wc mT x = rdW W mem x).
{ intros x Hx. apply F1; [lia | lia | intros Hf; pose proof (crt_fp_low x Hf); lia]. }
(* joined's pre-condition: len's 8 bytes lie in this frame's window, present by the journal (pass 5) *)
assert (HOPR : forall i, 0 <= i < 8 -> apresent (w_H Wc) mT (crt_sp1 + 144 + i)).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hprs & _). intros i Hi. apply Hprs.
  rewrite crt_STK. lia. }
assert (HRODT : arodata_okP SEGS CMD_RLO CMD_RHI B (rdW Wc mT))
  by exact (crt_rod _ _ _ _ _ _ _ HJ).
assert (HW1' : spZ rT <= W0 + 16) by lia.
assert (HW2' : W0 + 32 <= ly_stk_hi lyc) by lia.
assert (HVN' : aval_mem (rdW Wc mT) (W0 + 24) 4 (Z.of_nat (length ws)))
  by (apply (crt_aval_kept (rdW W mem)); [intros kk Hkk; apply KST; lia | exact HVN]).
assert (HVA' : aval_mem (rdW Wc mT) (W0 + 16) 8 arr)
  by (apply (crt_aval_kept (rdW W mem)); [intros kk Hkk; apply KST; lia | exact HVA]).
assert (HAB' : in_blockA (ablocks B lyc Sc) arr (8 * Z.of_nat (length ws))).
{ destruct HAB as (pa & ka & Hpa & Hpa1 & Hpa2). exists pa, ka. split; [exact (HinSc _ (HinRS _ Hpa)) | lia]. }
assert (HWS' : forall k, (k < length ws)%nat ->
  aval_mem (rdW Wc mT) (arr + 8 * Z.of_nat k) 8 (nth k wp 0) /\ 0 <= nth k wp 0 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) (nth k wp 0) (Z.of_nat (length (nth k ws [])) + 1) /\
  astr_atR (rdW Wc mT) (nth k wp 0) (nth k ws [])).
{ intros k Hk. destruct (HWS k Hk) as (Hv & Hr & (pw & kw & Hpw & Hpw1 & Hpw2) & Hstr).
  destruct HAB as (pa & ka & Hpa & Hpa1 & Hpa2).
  split; [|split; [exact Hr | split]].
  - apply (crt_aval_kept (rdW W mem)); [|exact Hv]. intros kk Hkk. apply (KBS pa ka); [exact (HinRS _ Hpa) | lia].
  - exists pw, kw. split; [exact (HinSc _ Hpw) | lia].
  - apply (rcfr_str_keep (rdW W mem) _ _ _ Hstr). intros i Hi. apply (KBS pw kw); [exact Hpw | lia]. }
assert (HNEED' : PJoinR.join_need ws + 1 < MALLOC_MAX) by (unfold MALLOC_MAX, LMAX in *; lia).
assert (HO1 : spZ rT <= crt_sp1 + 144) by lia.
assert (HO2 : crt_sp1 + 144 + 8 <= ly_top lyc) by lia.
assert (HO3 : (crt_sp1 + 144) mod 8 = 0).
{ replace (crt_sp1 + 144) with ((4 * ((sp0 - 256) / 32) + 18) * 8) by (unfold crt_sp1; lia). apply Z_mod_mult. }
assert (HO4 : crt_sp1 + 144 + 8 <= W0 + 16 \/ W0 + 32 <= crt_sp1 + 144) by lia.
pose proof HREPc as (Qc & (_ & _ & _ & _ & _ & HRp & _) & _).
pose proof (crt_reply_len _ _ _ _ _ _ HRp HRPL) as HL2. rewrite length_app in HL2. cbn [length] in HL2.
assert (HEVc : st_nev Sc + EV_JOINED <= EV_MAX).
{ pose proof (crt_ev_send_nn R (join_sp ws)). pose proof (crt_ev_args_nn R).
  unfold EV_CHECK_ROUND_TRIP, EV_JOINED in HEV. unfold EV_JOINED. lia. }
assert (HLIVEc : blocks_bytes Sc + LIVE_JOINED <= LIVE_MAX).
{ pose proof (crt_live_rcc _ _ _ _ _ HREP HNC) as HL1.
  unfold LIVE_CHECK_ROUND_TRIP, LIVE_SEND_MESSAGE, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in HLIVE.
  unfold LMAX in *. lia. }
assert (HMOKc : mo_ok MT Sc (XM_JOINED MT ws)).
{ apply (mok_station MT S Sc (XM_CHECK_ROUND_TRIP MT R ws) (XM_REC_CALLS_COPY MT R + mo_malloc MT (Z.of_nat (length X) + 1)) _ MTL MOK HMLE).
  - unfold XM_JOINED. apply (mo_malloc_nonneg MT MTL). pose proof (crt_jn_nn ws). lia.
  - pose proof (mo_malloc_mono MT MTL (Z.of_nat (length X) + 1) (LMAX + 2) ltac:(lia)).
    pose proof (crt_xm_send_nn R (join_sp ws)). pose proof (mo_free_nonneg MT MTL). pose proof (crt_ev_args_nn R).
    assert (0 <= ev_args R * mo_free MT) by (apply Z.mul_nonneg_nonneg; lia).
    unfold XM_CHECK_ROUND_TRIP. lia. }
assert (Hs0 : s0Z rT = sp0) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
(* the frame chain at the call: the prologue's frame record on afn_pre's chain (s0 = sp0) *)
assert (FRT : crt_frame (rdW Wc mT))
  by (apply (crt_frame_keep (rdW Wc mc)); [intros a Ha; apply K0; [lia | unfold A_G_REC; lia] | exact (proj1 Hfr)]).
destruct (crt_chain pos lyc Sc Wc mT mdv _ HJ FRT) as [ch1 Hch1].
(* joined's premise on the stack above len - 16 (pass 5b): this frame's window, present by the journal, and above sp0
   the statement's astack_pres, kept by the journal (astack_pres_journal) *)
assert (HPRSJ : astack_pres lyc (w_H Wc) mT (crt_sp1 + 144 - 16)).
{ apply (astack_pres_mono _ _ _ (sp0 - STK)); [rewrite crt_STK; lia|].
  apply (astack_pres_journal SEGS B pa_segs_low _ _ _ ly S W mem md [(5, pos)] lyc Sc Wc mT mdv _ HJ HPRES).
  intros x Hf Hx. exfalso. pose proof (crt_fp_low x Hf). lia. }
(* the call of joined (0x88250), len at s1 + 144 *)
eapply SRr_bind.
{ apply (cl_callS_wide B LAWS Wc rT mT (Z_to_bv 64 (BASE + AF_joined)) STK sp0 crt_FP ly S W mem md [(5, pos)] lyc Sc mdv
    (EV_REC_CALLS_COPY R + 1) JOINED_STK [(crt_sp1 + 144, crt_sp1 + 144 + 8)] EV_JOINED (crt_sp1 - sp0) (getr rT 1) ch1
    (crts5_K lyc Sc Wc mT (crt_sp1 + 144))).
  - exact HJ.
  - rewrite HspT. lia.
  - exact P4.
  - lia.
  - unfold JOINED_STK. lia.
  - unfold JOINED_STK. rewrite crt_STK. lia.
  - exact R3.
  - exact R4.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite R1, unsigned_lit_small by lia. lia.
  - rewrite Hs0. replace (sp0 + (crt_sp1 - sp0)) with crt_sp1 by lia. exact Hch1.
  - intros HPRE1.
    exact (HJOINED fx lyc Sc Wc rT mT mdv ch1 W0 arr (crt_sp1 + 144) wp ws HPRE1 HRODT R10 R11 HW1' HW2' HW8 HLEN HN31
      HVN' HVA' HARR HARR8 HAB' HWS' HNEED' HO1 HO2 HO3 HO4 HOPR HPRSJ HEVc HLIVEc HMOKc).
  - intros a Ha. apply crts5_inFP1 in Ha. unfold awr_byte. left. rewrite crt_STK. lia.
  - intros ly2' S2' W2' regs2' mem2' md2' HK a Ha _ _.
    unfold crts5_K in HK. destruct HK as (r0 & _ & _ & _ & _ & _ & _ & Hout & _).
    apply crts5_inFP1 in Ha.
    replace a with (crt_sp1 + 144 + Z.of_nat (Z.to_nat (a - (crt_sp1 + 144)))) by lia.
    rewrite (Hout (Z.to_nat (a - (crt_sp1 + 144))) ltac:(lia)). discriminate. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
unfold crts5_K in HK2. destruct HK2 as (line & Ha02 & Hl4096 & HPm2 & HAP2 & HIB2 & HBY2 & HLN2 & HKB2 & HBB2 & MLE2).
replace (sp0 + (crt_sp1 - sp0)) with crt_sp1 in HJc2 by lia.
pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _ & G3 & G4 & _).
rewrite R1.
(* what the run and joined kept *)
assert (Hin5 : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc mT mdv 5 pos HARt Hin5) as (Hf4 & Hfc & _).
rewrite Efa in Hf4, Hfc.
assert (Hin2 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2)).
{ intros pn Hp. eapply Permutation_in; [apply Permutation_sym; exact HPm2|]. right; exact Hp. }
assert (KF : forall a, (crt_F pos <= a < crt_F pos + fs_frame_bytes 5) \/ (crt_SH pos <= a < crt_SH pos + fs_frame_bytes 5 / 8) ->
  rdW W2 mem2 a = rdW Wc mc a).
{ intros a Ha. unfold crt_SH, crt_F in Ha. rewrite Hfs in Ha, Hfc. change (2048 / 8) with 256 in Ha.
  assert (HFq : 0 <= frame_addr ly 5 pos / 8 /\ 8 * (frame_addr ly 5 pos / 8) <= frame_addr ly 5 pos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  set (q8 := frame_addr ly 5 pos / 8) in *.
  rewrite (G4 5 pos a Hin5).
  - apply K0; [unfold SHADOW_OFF in Ha; lia|].
    intros Hg. destruct Ha as [Ha | Ha]; [|unfold SHADOW_OFF, A_G_REC in *; lia].
    apply (frm_img SEGS B LAWS lyc Sc Wc mT mdv 5 pos a HARt Hin5); [rewrite Efa, Hfs; exact Ha|].
    exact (cif_prog_img a (crts5_pg_of a ltac:(lia))).
  - unfold in_zr, frame_rng, shadow_addr. cbn [fst snd]. rewrite Efa, Hfs. change (2048 / 8) with 256. fold q8. lia.
  - intros Hf. apply crts5_inFP1 in Hf. unfold SHADOW_OFF in Ha. lia. }
assert (KS : forall a, crt_sp1 <= a < 2 ^ 64 -> ~ (crt_sp1 + 144 <= a < crt_sp1 + 152) -> rdW W2 mem2 a = rdW Wc mc a).
{ intros a Ha Hn. rewrite G1; [apply K0; [lia | unfold A_G_REC in *; lia] | lia | unfold JOINED_STK; lia |].
  intros Hf. apply crts5_inFP1 in Hf. lia. }
assert (KB : forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < n -> rdW W2 mem2 (p + i) = rdW Wc mc (p + i)).
{ intros p n i Hin Hi. rewrite (HKB2 p n i Hin Hi).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hin) as (_ & Hp4 & Hpc & _ & _ & _ & Hm).
  pose proof (req_size_pos n (proj1 Hm)) as [_ Hq].
  apply K0; [lia|]. intros Hg.
  exact (blk_img SEGS B LAWS lyc Sc Wc mc dc p n (p + i) HARc Hin ltac:(lia) (cif_prog_img (p + i) (crts5_pg_of (p + i) ltac:(lia)))). }
assert (KI : forall a, inFP cmd_PG a -> rdW W2 mem2 a = rdW Wc mT a).
{ intros a Hpg. destruct (crt_pg a Hpg) as (Ho & He).
  apply G3; [exact (cif_prog_img a Hpg) | exact Ho | exact He |].
  apply fp_spares_closed; [apply crts5_sink1; lia | intros Hf; apply crts5_inFP1 in Hf; pose proof (crts5_pg_rng a Hpg); lia]. }
apply (HSTF ly2 S2 W2 mem2 md2 regs2 pos qs res X line).
- exact HJ2.
- destruct Hfr as (Hfr1 & Hfr2 & Hfr3). split; [|split].
  + intros j r Hj. assert (Hj13 : (j < 13)%nat) by (rewrite <- crt_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
    apply (crt_aval_kept (rdW Wc mc)); [|exact (Hfr1 j r Hj)]. intros kk Hkk. apply KS; lia.
  + rewrite (rdword_ext (rdW Wc mc) (rdW W2 mem2)); [exact Hfr2|]. intros kk Hkk. apply KF. left. rewrite Hfs. lia.
  + intros i Hi. rewrite KF; [exact (Hfr3 i Hi)|]. right. rewrite Hfs. change (2048 / 8) with 256. lia.
- destruct Htbl as (Hlq & Hnd & Hcall & Hap). split; [exact Hlq|]. split; [exact Hnd|]. split; [|exact Hap].
  intros i c P Hc HP. destruct (Hcall i c P Hc HP) as [Hac Hsz]. split; [|exact Hsz].
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  apply (rcfr_call_keep (ablocks B lyc Sc) (ablocks B ly2 S2) (rdW Wc mc) (rdW W2 mem2) _ c P Hac).
  + intros x Hx. apply KF. left. rewrite Hfs. unfold CALL_SIZE in *. lia.
  + intros [p n] _ Hb. split; [exact (Hin2 _ Hb)|]. intros j Hj. exact (KB p n j Hb Hj).
- eapply Permutation_trans; [exact HPm2|].
  change [(res, Z.of_nat (length X) + 1); (line, crt_jn)] with ([(res, Z.of_nat (length X) + 1)] ++ [(line, crt_jn)]).
  rewrite !app_assoc.
  eapply Permutation_trans; [|apply Permutation_cons_append].
  apply perm_skip. eapply Permutation_trans; [exact HPm|]. rewrite !app_assoc.
  apply Permutation_app_tail. apply Permutation_app_tail. exact HPERM.
- unfold crt_R1. apply (crts5_repA_set lyc Sc ly2 S2 (rdW Wc mc) (rdW W2 mem2) R O sb hb HREPc).
  + intros a Ha Hn. pose proof (crt_inrec_pg a Ha) as Hpg. rewrite (KI a Hpg).
    apply K0; [pose proof (crts5_pg_rng a Hpg); lia | exact Hn].
  + unfold OFF_STATE. apply (crt_aval_kept (rdW Wc mT)); [|exact HVsb]. intros kk Hkk. apply KI. apply crts5_pg_of. lia.
  + unfold OFF_HOST. apply (crt_aval_kept (rdW Wc mT)); [|exact HVhb]. intros kk Hkk. apply KI. apply crts5_pg_of. lia.
  + exact HSB.
  + exact HHB.
  + intros [p n] Hb. split; [exact (Hin2 _ Hb)|]. intros j Hj. exact (KB p n j Hb Hj).
- apply (crt_aval_kept (rdW Wc mc)); [|exact HVQc]. intros kk Hkk.
  assert (Hpg : inFP cmd_PG (A_G_QUITTING + kk))
    by (exists (A_G_QUITTING, A_G_QUITTING + 4); split; [right; right; left; reflexivity | cbn [fst snd]; lia]).
  rewrite (KI _ Hpg). apply K0; unfold A_G_QUITTING, A_G_REC; lia.
- exact HRPL.
- exact HX0.
- apply (rcfr_bytes_keep (rdW Wc mc) _ _ _ HRES). intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  apply (KB res _ i Hresin). lia.
- exact H4096.
- exact HBY2.
- lia.
- lia.
- exact (mle_station MT S Sc S2 _ _ MTL HMLE MLE2).
- exact Hws.
- exact Hact.
- unfold crt_SLF, crt_slots. apply Forall_cons.
  + cbn [fst snd]. unfold crt_D. exact HLN2.
  + apply Forall_forall. intros [o v] Hin. cbn [fst snd].
    pose proof (crts5_sle_rng pos o v Hin) as Ho.
    apply (crt_aval_kept (rdW Wc mc)); [|exact (crt_slot Wc mc _ o v HSL Hin)].
    intros kk Hkk. apply KS; lia.
- unfold crt_regs, crt_RF. repeat apply Forall_cons; [..| apply Forall_nil]; cbn [fst snd].
  all: first [ replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity); exact Ha02
             | rewrite (crt_preg rT regs2 _ HP2) by crt_cs; assumption ].
Qed.
(* ---------- s6: 0x88254 .. 0x8825c (len from slot 144, line kept in s6), then send_message ---------- *)
(* the seed at 0x88254: slot 144 of the realigned frame holds |crt_D| (atom 32) *)
Definition crts6_ss : sstate := mkSS 7536 sr_atoms
  [YP09.mkRegion (Some 9%nat) 144 152 0 0 [YP09.mkChunk 144 (CVal 8 (SOff 32 0))]] None
  (mkFacts [(2%nat, crt_SPF); (9%nat, crt_SPF)] [] []).
Definition crts6_E (rX : bvmap 5 word) (n : Z) : env := Eimg (Ereg rX [w64 n]).
Lemma crts6_Ereg : forall rX n (k : nat) (z : Z), Z.of_nat k = z -> 0 <= z < 32 ->
  ew (crts6_E rX n) k = getr rX (Z_to_bv 5 z).
Proof.
intros rX n k z Hk Hz. unfold crts6_E. apply ew_Eimg_Ereg_nat.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact Hk.
Qed.
Lemma crts6_E32 : forall rX n, ew (crts6_E rX n) 32 = w64 n.
Proof. intros rX n. unfold crts6_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra rX _ 0). Qed.
(* the joined line: its length is join_need - 1 (lib/Prog/joined.v jsp_len over the plain model) *)
Lemma crts6_jsp_len : forall l : list (list byte), l <> [] -> Z.of_nat (length (join_sp l)) + 1 = PJoinR.join_need l.
Proof.
induction l as [|x l IH]; intros NE; [congruence|].
destruct l as [|y l'].
- unfold PJoinR.join_need. cbn [join_sp fold_right]. lia.
- specialize (IH ltac:(discriminate)).
  replace (join_sp (x :: y :: l')) with (x ++ SPACE :: join_sp (y :: l')) by reflexivity.
  replace (PJoinR.join_need (x :: y :: l')) with (Z.of_nat (length x) + 1 + PJoinR.join_need (y :: l')) by reflexivity.
  rewrite length_app. cbn [length]. lia.
Qed.
Lemma crts6_jsp_le : forall l : list (list byte), Z.of_nat (length (join_sp l)) <= PJoinR.join_need l.
Proof. intros [|x l]; [unfold PJoinR.join_need; cbn; lia|]. rewrite <- (crts6_jsp_len (x :: l)) by discriminate. lia. Qed.
Lemma crts6_seed : forall (Wc : world SEGS) mc rX pos res line,
 crt_regs rX (crt_RF pos res line) -> crt_slots Wc mc (crt_SLF pos) ->
 st_ok_pi SEGS VAL (crts6_E rX (Z.of_nat (length crt_D))) crts6_ss
   (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + 7536)) mc (seg_rom SEGS))).
Proof.
intros Wc mc rX pos res line HR HL.
pose proof crt_sp0 as (S1 & S2 & S3 & S4 & S5). pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (crts6_jsp_le ws) as JL. change (join_sp ws) with crt_D in JL.
assert (U2 : bv_unsigned (ew (crts6_E rX (Z.of_nat (length crt_D))) 2) = crt_sp1).
{ rewrite (crts6_Ereg rX _ 2 2 eq_refl ltac:(lia)). rewrite (crt_reg rX _ 2 crt_sp1 HR) by (unfold crt_RF; crt_in).
  unfold w64. apply unsigned_lit_small. lia. }
assert (U9 : bv_unsigned (ew (crts6_E rX (Z.of_nat (length crt_D))) 9) = crt_sp1).
{ rewrite (crts6_Ereg rX _ 9 9 eq_refl ltac:(lia)). rewrite (crt_reg rX _ 9 crt_sp1 HR) by (unfold crt_RF; crt_in).
  unfold w64. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. unfold crts6_ss. apply pa_entry_st_ok_full.
- unfold crts6_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS _ _ crt_sp1 144 8 (SOff 32 0) (Z.of_nat (length crt_D)));
    [cbn [sv_denot]; rewrite crts6_E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (unfold LMAX in HNEED; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold LMAX in HNEED; lia | cbn; lia |].
  apply crt_val_of_aval. exact (crt_slot Wc mc _ 144 _ HL ltac:(unfold crt_SLF; apply in_eq)).
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, crt_SPF. cbn [af_lo af_hi af_al2].
  rewrite U2, U9. change (2 ^ 5) with 32. repeat split; try lia.
Qed.

(* a register the run left alone: its value at the seed (crt_RF) *)
Ltac crts6_unch HS RX k z :=
  crt_rreg HS; rewrite crt_den_atom0, (crts6_Ereg _ _ k z eq_refl ltac:(lia)); apply RX; unfold crt_RF; crt_in.

Lemma crt_s6 : (forall f : YK11.FPState, fxrel fx f -> ST_Gx f) -> ST_F.
Proof.
intros HSTG lyc Sc Wc mc dc rX pos qs res X line HJ Hfr Htbl HPm HREP1 HVQ1 HRep Hno0 Hres Hres4 Hline Hline4 HBB HMLE
  Hws Hact HSL HRF.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof crt_sp0 as (SP1 & SP2 & SP3 & SP4 & SP5). pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_B_ok _ _ PI) as HBASE. pose proof (pa_base_lo (L := cmd_listing)) as HBLO.
pose proof (crts6_jsp_len ws Hws) as JL. change (join_sp ws) with crt_D in JL.
assert (Hjn_def : crt_jn = PJoinR.join_need ws + 1) by reflexivity.
assert (HXL : Z.of_nat (length X) + 1 <= LMAX + 2).
{ pose proof HREP as (Q0 & HA0 & _). destruct HA0 as (_ & _ & _ & _ & _ & HRp0 & _).
  pose proof (crt_reply_len _ _ _ _ _ _ HRp0 HRep) as HL0. rewrite length_app in HL0. cbn [length] in HL0. lia. }
pose proof (crt_live_rcc ly S (rdW W mem) R O HREP HNC) as HLR.
pose proof (crt_ev_args_nn R) as HEA.
unfold crt_J in HJ.
pose proof HJ as (HARc0 & Hly & _ & _ & _ & Hfrs & Hnev & _).
(* the joined line's block *)
assert (Hlin : In (line, crt_jn) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPm|].
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. right; left; reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc0 Hlin) as (_ & _ & Hlc & _ & _ & _ & Hjn).
pose proof (req_size_pos crt_jn ltac:(lia)) as [_ Hjq].
(* the class-5 frame at the call's layout *)
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc HAR Hly) as (_ & Efa & _).
assert (Hin5 : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc mc dc 5 pos HARc0 Hin5) as (Hf4096 & Hfceil & _).
assert (FB : fs_frame_bytes 5 = 2048) by reflexivity.
rewrite Efa, FB in Hfceil. rewrite Efa in Hf4096.
change (frame_addr ly 5 pos) with (crt_F pos) in Hf4096, Hfceil.
pose proof (crt_nodup _ _ _ _ _ HARc0) as HNDc.
(* 0x88254 .. 0x8825c: a1 = |crt_D| from slot 144, s6 = line, the call *)
pose proof (crts6_seed Wc mc rX pos res line HRF HSL) as HS.
assert (HEI : img_env VAL A_LIM (crts6_E rX (Z.of_nat (length crt_D)))) by (unfold crts6_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 27 0) [] (crts6_E rX (Z.of_nat (length crt_D))) (mrestrict (w_H Wc) mc))
  by (unfold sh_ok; apply Forall_nil).
unfold cfgP.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
pose proof (crt_frame_nowin _ _ _ _ _ HFr ltac:(crt_nowin)) as K0. clear HF HFr HG. clear_md.
assert (RX : forall n v, In (n, v) (crt_RF pos res line) -> getr rX (Z_to_bv 5 n) = w64 v)
  by (intros n v Hin; exact (crt_reg rX _ n v HRF Hin)).
assert (T1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 7548)) by (crt_rreg HS; apply (codeptr_val _ 7548 HEI)).
assert (Tl2 : getr (ms_regs ms) 2 = w64 crt_sp1) by crts6_unch HS RX 2%nat 2.
assert (Tl3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by crts6_unch HS RX 3%nat 3.
assert (Tl4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by crts6_unch HS RX 4%nat 4.
assert (Tl8 : getr (ms_regs ms) 8 = w64 sp0) by crts6_unch HS RX 8%nat 8.
assert (T10 : getr (ms_regs ms) 10 = w64 line) by crts6_unch HS RX 10%nat 10.
assert (T11 : getr (ms_regs ms) 11 = w64 (Z.of_nat (length crt_D)))
  by (crt_rreg HS; rewrite crt_den_atom0; exact (crts6_E32 rX _)).
assert (T2 : getr (ms_regs ms) (Z_to_bv 5 2) = w64 crt_sp1) by crts6_unch HS RX 2%nat 2.
assert (T9 : getr (ms_regs ms) (Z_to_bv 5 9) = w64 crt_sp1) by crts6_unch HS RX 9%nat 9.
assert (T8 : getr (ms_regs ms) (Z_to_bv 5 8) = w64 sp0) by crts6_unch HS RX 8%nat 8.
assert (T3 : getr (ms_regs ms) (Z_to_bv 5 3) = w64 (as_gp B)) by crts6_unch HS RX 3%nat 3.
assert (T4 : getr (ms_regs ms) (Z_to_bv 5 4) = w64 (as_tp B)) by crts6_unch HS RX 4%nat 4.
assert (T18 : getr (ms_regs ms) (Z_to_bv 5 18) = w64 (crt_F pos)) by crts6_unch HS RX 18%nat 18.
assert (T20 : getr (ms_regs ms) (Z_to_bv 5 20) = w64 (crt_shx (A_G_REC + 928))) by crts6_unch HS RX 20%nat 20.
assert (T21 : getr (ms_regs ms) (Z_to_bv 5 21) = w64 res) by crts6_unch HS RX 21%nat 21.
assert (T22 : getr (ms_regs ms) (Z_to_bv 5 22) = w64 line) by crts6_unch HS RX 10%nat 10.
assert (T23 : getr (ms_regs ms) (Z_to_bv 5 23) = w64 (crt_shx (A_G_REC + 952))) by crts6_unch HS RX 23%nat 23.
assert (T24 : getr (ms_regs ms) (Z_to_bv 5 24) = w64 A_G_REC) by crts6_unch HS RX 24%nat 24.
assert (T25 : getr (ms_regs ms) (Z_to_bv 5 25) = w64 A_G_QUITTING) by crts6_unch HS RX 25%nat 25.
assert (T26 : getr (ms_regs ms) (Z_to_bv 5 26) = w64 (crt_shx (A_G_REC + 944))) by crts6_unch HS RX 26%nat 26.
assert (T27 : getr (ms_regs ms) (Z_to_bv 5 27) = w64 SHADOW_OFF) by crts6_unch HS RX 27%nat 27.
pmkst HS.
rewrite (SIGP CS_send_message ltac:(vm_compute; tauto)).
replace (VAL A_TEXT + cmd_af CS_send_message) with (BASE + AF_send_message)
  by (unfold cmd_af, AF_send_message; vm_compute; reflexivity).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ => set (rT0 := rT) in *; set (mT0 := mT) in * end.
(* send_message's premises at the call *)
assert (HspT : spZ rT0 = crt_sp1) by (unfold spZ at 1; rewrite Tl2; unfold w64; rewrite unsigned_lit_small by lia; lia).
(* the frame chain at the call: the prologue's frame record on afn_pre's chain (s0 = sp0) *)
assert (FRT : crt_frame (rdW Wc mT0))
  by (apply (crt_frame_keep (rdW Wc mc)); [intros a Ha; apply K0; lia | exact (proj1 Hfr)]).
destruct (crt_chain pos lyc Sc Wc mT0 mdv _ HJ FRT) as (ch1 & Hch0).
assert (Hch1 : achain lyc (rdW Wc mT0) (sp0 + (crt_sp1 - sp0)) (s0Z rT0) ch1).
{ replace (sp0 + (crt_sp1 - sp0)) with crt_sp1 by lia. unfold s0Z. rewrite Tl8. unfold w64.
  rewrite unsigned_lit_small by lia. exact Hch0. }
pose proof (crt_rod _ _ _ _ _ _ _ HJ) as HRODT.
assert (HROKT : cmd_ro_ok (rdW Wc mT0)) by exact (cmd_ro_ok_of_aro SEGS B LAWS HB IMG _ _ _ _ _ (proj1 HJ) HRODT).
assert (HFRT : Z.of_nat (length (frames Sc)) <= 3) by (rewrite Hfrs; cbn [length app]; lia).
assert (Hline64 : 0 <= line < 2 ^ 64) by lia.
assert (HnD : 0 <= Z.of_nat (length crt_D) <= 8192) by (unfold LMAX in HNEED; lia).
assert (HDT : abytes_atR (rdW Wc mT0) line crt_D).
{ intros i Hi. rewrite K0 by lia.
  pose proof (Hline i ltac:(rewrite length_app; cbn [length]; lia)) as H. rewrite app_nth1 in H by exact Hi. exact H. }
assert (HINB : Z.of_nat (length crt_D) <> 0 ->
  in_blockA (rest ++ concat qs ++ [(res, Z.of_nat (length X) + 1); (line, crt_jn)]) line (Z.of_nat (length crt_D))).
{ intros _. exists line, crt_jn. split; [|lia].
  apply in_or_app; right. apply in_or_app; right. right; left; reflexivity. }
assert (HREPT : rec_repA B lyc Sc (rdW Wc mT0) crt_R1 O).
{ apply (rcf_rep_repA B lyc Sc lyc Sc (rdW Wc mc) (rdW Wc mT0) crt_R1 O [] HREP1).
  - intros a Ha. apply K0. unfold rcf_inrec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha. lia.
  - rewrite app_nil_r. apply Permutation_refl.
  - intros pn [].
  - intros p n i Hin Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc0 Hin) as (_ & Hp4 & Hpc & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hq]. apply K0. lia. }
assert (HEVT : st_nev Sc + EV_SEND_MESSAGE crt_R1 crt_D <= EV_MAX).
{ unfold crt_R1. rewrite crt_ev_send_sh. unfold EV_CHECK_ROUND_TRIP in HEV. unfold crt_D. lia. }
assert (HLIVET : blocks_bytes Sc + LIVE_SEND_MESSAGE <= LIVE_MAX) by (unfold LIVE_CHECK_ROUND_TRIP in HLIVE; lia).
assert (HMOKT : mo_ok MT Sc (XM_SEND_MESSAGE MT crt_R1 crt_D)).
{ unfold crt_R1. rewrite crt_xm_send_sh.
  apply (mo_ok_step MT MTL S Sc (XM_REC_CALLS_COPY MT R + mo_malloc MT (Z.of_nat (length X) + 1) + XM_JOINED MT ws));
    [|exact HMLE].
  apply (mo_ok_le MT MTL S _ (XM_CHECK_ROUND_TRIP MT R ws) MOK).
  pose proof (mo_malloc_mono MT MTL (Z.of_nat (length X) + 1) (LMAX + 2) ltac:(lia)) as HMM.
  pose proof (mo_free_nonneg MT MTL) as HF0. pose proof (Z.mul_nonneg_nonneg _ _ HEA HF0) as HEF.
  unfold XM_CHECK_ROUND_TRIP, crt_D. lia. }
(* send_message reaches the printf wrappers: its post is FP-existential, so the call is PaFx.v's cl_callS_wideF and the
   walk goes on at the FP state fx1 it returns, where the point after it holds (HSTG at fx1); srr_after_callF_base lifts
   that apost_base at fx1 to crt_postF at fx *)
unfold crt_postF.
eapply (srr_after_callF_base SEGS).
{ eapply (cl_callS_wideF B LAWS Wc rT0 mT0 _ STK sp0 crt_FP ly S W mem md [(5, pos)] lyc Sc mdv
    (EV_REC_CALLS_COPY R + 1 + EV_JOINED) SEND_MESSAGE_STK crt_FP (EV_SEND_MESSAGE crt_R1 crt_D)
    (crt_sp1 - sp0) (getr rT0 1) ch1).
  - exact HJ.
  - rewrite HspT. lia.
  - exact P4.
  - lia.
  - unfold SEND_MESSAGE_STK. pose proof (Z.le_max_l ASTACK (Z.max REC_CLEAR_STK VERBS_RECEIVE_STK)).
    unfold ASTACK in *. lia.
  - pose proof crt_STK as HSTK. unfold CHECK_ROUND_TRIP_STK in HSTK.
    pose proof (Z.le_max_l SEND_MESSAGE_STK REC_CALLS_COPY_STK). rewrite crt_STK. lia.
  - exact Tl3.
  - exact Tl4.
  - reflexivity.
  - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite T1. rewrite unsigned_lit_small by lia. lia.
  - exact Hch1.
  - intros HPRE1.
    exact (HSEND fx lyc Sc Wc rT0 mT0 mdv ch1 line (Z.of_nat (length crt_D)) crt_D crt_R1 O
      (rest ++ concat qs ++ [(res, Z.of_nat (length X) + 1); (line, crt_jn)])
      HPRE1 HFRM HFRT HRODT HROKT HVAL T10 Hline64 T11 HnD eq_refl HDT HINB HPm HREPT HNC HDECL HEVT HLIVET HMOKT).
  - intros a Hf. unfold awr_byte, awr_prog_or_caller. destruct (crt_fp_cases a Hf) as [(p & n & Hin & Hr) | (Hpg & _)].
    + right. left. split; [exact Hf|]. exists p, n. split; [|exact Hr].
      eapply Permutation_in; [apply Permutation_sym; exact HPm | apply in_or_app; left; exact Hin].
    + right. right. right. right. left. split; [exact Hf|]. split; [exact (crt_pg_prog a Hpg) | exact (cif_prog_img a Hpg)].
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Hf Ha _. exfalso. pose proof (crt_fp_low a Hf). rewrite crt_STK in Ha. lia. }
cbv beta. intros fx1 ly2 S2 W2 regs2 mem2 md2 _ Hfx (HJ2 & HJc2 & HP2 & HK).
rewrite T1. cbv beta in HK.
(* the recorder after the round trip: rt_okA, and refuse / code / spill through run_receive *)
unfold vr_runA, crt_R1, crt_D in HK.
pose proof HRT as HRT1. unfold rt_okA in HRT1. specialize (HRT1 Hws Hact).
pose proof (crt_rr_rc atoi_a reply_code_a (RecModel.rec_clear (set_host (set_state R sb) hb)) (join_sp ws)) as RC.
pose proof (crt_rr_spill atoi_a reply_code_a (RecModel.rec_clear (set_host (set_state R sb) hb)) (join_sp ws)
  ltac:(cbn; lia)) as RS.
destruct (VerbsRun.run_receive atoi_a reply_code_a (RecModel.rec_clear (set_host (set_state R sb) hb)) (join_sp ws))
  as [[R2 xr] quit] eqn:EVR.
destruct HK as (O2 & HREP2 & HQ2 & HPm2 & HBB2 & MLE2).
destruct HRT1 as (E1 & E2 & E3 & E4 & E5).
cbn [fst] in RC, RS. cbn [RecModel.rec_clear set_host set_state r_refuse r_code r_spill] in RC, RS.
destruct RC as [RC1 RC2].
(* what send_message kept: the caller's stack above its window, the class-5 frame and its shadow, the other blocks *)
pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _ & G4 & _).
assert (KS : forall a, crt_sp1 <= a < sp0 -> rdW W2 mem2 a = rdW Wc mc a).
{ intros a Ha. rewrite <- (K0 a) by lia. apply G1; [lia | lia | intros Hf; pose proof (crt_fp_low a Hf); lia]. }
assert (KF : forall x, crt_F pos <= x < crt_F pos + 2048 -> rdW W2 mem2 x = rdW Wc mc x).
{ intros x Hx. rewrite <- (K0 x) by lia. apply (G4 5 pos x Hin5).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa, FB. exact Hx.
  - intros Hf. destruct (crt_fp_cases x Hf) as [(p & n & Hin & Hr) | (Hpg & _)].
    + assert (Hinb : In (p, n) (ablocks B lyc Sc))
        by (eapply Permutation_in; [apply Permutation_sym; exact HPm | apply in_or_app; left; exact Hin]).
      pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc mc dc p n 5 pos HARc0 Hinb Hin5) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efa, FB in Hd. unfold crt_F in Hx. lia.
    + apply (frm_img SEGS B LAWS lyc Sc Wc mc dc 5 pos x HARc0 Hin5); [rewrite Efa, FB; unfold crt_F in Hx; lia |].
      exact (cif_prog_img x Hpg). }
assert (HSH : 0x7fff8000 <= crt_SH pos /\ crt_SH pos + 256 < 0x10007fff8000).
{ pose proof (Z.div_lt_upper_bound (crt_F pos) 8 0xfffffff0000 ltac:(lia) ltac:(lia)) as H1.
  pose proof (Z.div_pos (crt_F pos) 8 ltac:(lia) ltac:(lia)) as H2.
  unfold crt_SH, SHADOW_OFF. revert H1 H2. generalize (crt_F pos / 8). intros f H1 H2. clear - H1 H2. lia. }
assert (KSH : forall i, 0 <= i < 256 -> rdW W2 mem2 (crt_SH pos + i) = rdW Wc mc (crt_SH pos + i)).
{ intros i Hi. rewrite <- (K0 (crt_SH pos + i)) by (clear - HSH Hi; lia). apply (G4 5 pos (crt_SH pos + i) Hin5).
  - right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Efa, FB.
    change (SHADOW_OFF + frame_addr ly 5 pos / 8) with (crt_SH pos). change (2048 / 8) with 256. clear - Hi. lia.
  - intros Hf. destruct (crt_fp_cases _ Hf) as [(p & n & Hin & Hr) | (_ & Hr)].
    + assert (Hinb : In (p, n) (ablocks B lyc Sc))
        by (eapply Permutation_in; [apply Permutation_sym; exact HPm | apply in_or_app; left; exact Hin]).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc0 Hinb) as (_ & _ & _ & Happ & _).
      unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. destruct Happ as [_ [Hlo | [Hhi _]]]; [clear - Hlo Hr HSH Hi; lia | clear - Hhi Hr HSH Hi; lia].
    + clear - Hr HSH Hi. lia. }
assert (KR : forall p n i, In (p, n) (rest ++ concat qs ++ [(res, Z.of_nat (length X) + 1); (line, crt_jn)]) ->
  0 <= i < n -> rdW W2 mem2 (p + i) = rdW Wc mc (p + i)).
{ intros p n i Hin Hi.
  assert (Hinc : In (p, n) (ablocks B lyc Sc))
    by (eapply Permutation_in; [apply Permutation_sym; exact HPm | apply in_or_app; right; exact Hin]).
  assert (Hin2 : In (p, n) (ablocks B ly2 S2))
    by (eapply Permutation_in; [apply Permutation_sym; exact HPm2 | apply in_or_app; right; exact Hin]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc0 Hinc) as (_ & Hp4 & Hpc & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
  rewrite <- (K0 (p + i)) by lia.
  apply (G2 p n i Hinc Hin2); [lia|].
  intros Hf. destruct (crt_fp_cases _ Hf) as [(p' & n' & Hin' & Hr) | (Hpg & _)].
  - assert (Hinc' : In (p', n') (ablocks B lyc Sc))
      by (eapply Permutation_in; [apply Permutation_sym; exact HPm | apply in_or_app; left; exact Hin']).
    assert (Hdec : (p', n') = (p, n) \/ (p', n') <> (p, n))
      by (destruct (Z.eq_dec p' p), (Z.eq_dec n' n); [left; congruence | right; congruence | right; congruence | right; congruence]).
    destruct Hdec as [Eq | Ne].
    + rewrite Eq in Hin'. pose proof (Permutation_NoDup HPm HNDc) as ND. apply NoDup_ListNoDup in ND.
      exact (rcfr_nodup_disj _ _ _ (p, n) ND Hin' Hin).
    + pose proof (sep_blocks SEGS B LAWS lyc Sc Wc mc dc p' n' p n HARc0 Hinc' Hinc Ne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - exact (blk_img SEGS B LAWS lyc Sc Wc mc dc p n (p + i) HARc0 Hinc ltac:(lia) (cif_prog_img _ Hpg)). }
change (SRr SEGS W2 (cfgPx fx1 7548 regs2 mem2 md2) (crt_postx fx1)).
apply (HSTG fx1 Hfx ly2 S2 W2 mem2 md2 regs2 pos qs res X line R2 O2).
- unfold crt_J, crt_EVG. rewrite <- (crt_ev_send_sh R sb hb crt_D). exact HJ2.
- destruct Hfr as (Hfr1 & Hfr2 & Hfr3). split; [|split].
  + intros j r Hj. assert (Hj13 : (j < 13)%nat) by (rewrite <- crt_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
    apply (crt_aval_kept (rdW Wc mc)); [|exact (Hfr1 j r Hj)].
    intros kk Hkk. apply KS. lia.
  + unfold rdword in Hfr2 |- *. rewrite !KF by (rewrite FB; lia). exact Hfr2.
  + intros i Hi. rewrite KSH by lia. exact (Hfr3 i Hi).
- destruct Htbl as (HTL & HTND & HTC & HTA). split; [exact HTL|]. split; [exact HTND|]. split; [|exact HTA].
  intros i c P Hc HP. destruct (HTC i c P Hc HP) as [Hca Hlen]. split; [|exact Hlen].
  assert (Hi2 : (i < 2)%nat) by (pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)); lia).
  apply (rcfr_call_keep (ablocks B lyc Sc) (ablocks B ly2 S2) (rdW Wc mc) (rdW W2 mem2) _ c P Hca).
  + intros x Hx. apply KF. unfold CALL_SIZE in Hx. lia.
  + intros pn Hpn _.
    assert (Hr' : In pn (rest ++ concat qs ++ [(res, Z.of_nat (length X) + 1); (line, crt_jn)])).
    { apply in_or_app; right. apply in_or_app; left. apply in_concat. exists P. split; [exact (nth_error_In _ _ HP) | exact Hpn]. }
    split; [eapply Permutation_in; [apply Permutation_sym; exact HPm2 | apply in_or_app; right; exact Hr'] |].
    intros k Hk. destruct pn as [p n]. exact (KR p n k Hr' Hk).
- exact HPm2.
- exact HREP2.
- exact (conj E1 (conj E2 (conj RC1 (conj RC2 (conj RS (conj E4 E5)))))).
- rewrite E3 in HQ2. exact HQ2.
- exact HRep.
- exact Hno0.
- apply (rcfr_bytes_keep (rdW Wc mc) _ _ _ Hres). intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  apply (KR res (Z.of_nat (length X) + 1) i); [|lia].
  apply in_or_app; right. apply in_or_app; right. left; reflexivity.
- exact Hres4.
- exact Hline4.
- unfold LIVE_CHECK_ROUND_TRIP. lia.
- unfold crt_XMG. rewrite crt_xm_send_sh in MLE2.
  apply (mle_weaken MT S S2 _ _ MTL (mle_station MT S Sc S2 _ _ MTL HMLE MLE2)).
  pose proof (mo_malloc_mono MT MTL (Z.of_nat (length X) + 1) (LMAX + 2) ltac:(lia)). unfold crt_D. lia.
- assert (HSLE : crt_slots Wc mc (crt_SLE pos)) by (unfold crt_slots, crt_SLF in HSL |- *; exact (Forall_inv_tail HSL)).
  assert (HB8 : Forall (fun ov => 0 <= fst ov <= 248) (crt_SLE pos))
    by (unfold crt_SLE; repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil).
  unfold crt_slots in HSLE |- *. rewrite Forall_forall in HSLE, HB8 |- *. intros ov Hin.
  pose proof (HB8 ov Hin) as Ho. apply (crt_aval_kept (rdW Wc mc)); [|exact (HSLE ov Hin)].
  intros kk Hkk. apply KS. lia.
- unfold aregs_preserved in HP2. unfold crt_regs, crt_RG.
  repeat (apply Forall_cons; [cbn [fst snd]; rewrite HP2 by (unfold acallee_saved; lia); assumption |]).
  apply Forall_nil.
Qed.
(* ---------- the two free calls (0x88260 free(line), 0x88304 free(reply_first)): shared helpers ---------- *)
(* the seed of a point whose run is `mv a0, sX; jal wrapper_free`: every register its own atom, atom 32 the shadow base *)
Definition crts7_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [(32%nat, mkAF SB SB 0)] [] []).
Definition crts7_E (rX : bvmap 5 word) : env := Eimg (Ereg rX [w64 SB]).
Lemma crts7_seed : forall pc rX (Wc : world SEGS) mc,
 st_ok_pi SEGS VAL (crts7_E rX) (crts7_ss pc) (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) mc (seg_rom SEGS))).
Proof.
intros pc rX Wc mc.
assert (E32 : ew (crts7_E rX) 32 = w64 SB)
  by (unfold crts7_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
rewrite restrict_mkst_fx. unfold crts7_ss. apply pa_entry_st_ok_full.
- unfold crts7_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E32. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). rewrite Z.pow_0_r, Z.mod_1_r.
  repeat split; lia.
Qed.
Lemma crts7_regs_sub : forall rX L L', (forall x, In x L' -> In x L) -> crt_regs rX L -> crt_regs rX L'.
Proof. intros rX L L' Hs H. unfold crt_regs in *. rewrite Forall_forall in *. intros x Hx. exact (H x (Hs x Hx)). Qed.
(* a block the entry had is either the recorder's (in the footprint) or among `rest` *)
Lemma crts7_cov : forall pa na (L : list (Z * Z)), ~ In (pa, na) L -> (forall y, In y rest -> In y L) ->
 In (pa, na) (ablocks B ly S) -> forall i, 0 <= i < req_size na -> inFP crt_FP (pa + i).
Proof.
intros pa na L Hn Hsub Hin i Hi.
apply (Permutation_in _ HPERM) in Hin. apply in_app_or in Hin as [Hin | Hin].
- destruct (inFP_ablocks_fp O pa na i Hin Hi) as (r & Hr & Hx). unfold crt_FP, inFP. exists r.
  split; [apply in_or_app; left; exact Hr | exact Hx].
- exfalso. exact (Hn (Hsub _ Hin)).
Qed.
Lemma crts7_notin : forall (bl L : list (Z * Z)) x, List.NoDup bl -> Permutation bl (L ++ [x]) -> ~ In x L.
Proof.
intros bl L x ND HP. pose proof (Permutation_NoDup HP ND) as ND2.
pose proof (List.NoDup_remove_2 L [] x ND2) as H. rewrite app_nil_r in H. exact H.
Qed.
(* what a free of the block (pa, na) from the realigned frame keeps, over the reader before the run to the call *)
Definition crts7_kept lyc Sc (Wc : world SEGS) mc (W2 : world SEGS) mem2 (pa na : Z) : Prop :=
 (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (crt_sp1 - ASTACK <= a < crt_sp1) -> rdW W2 mem2 a = rdW Wc mc a) /\
 (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (pa <= b + i < pa + req_size na) ->
   rdW W2 mem2 (b + i) = rdW Wc mc (b + i)) /\
 (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   rdW W2 mem2 a = rdW Wc mc a) /\
 (forall cid pos a, In (cid, pos) (frames Sc) ->
   (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
   ~ (pa <= a < pa + req_size na) -> rdW W2 mem2 a = rdW Wc mc a).
Lemma crts7_kept_of : forall lyc Sc (Wc : world SEGS) mc dc mT (W2 : world SEGS) mem2 pa na,
 AR SEGS B lyc Sc Wc mc dc ->
 (forall a, 0 <= a < 2 ^ 64 -> rdW Wc mT a = rdW Wc mc a) ->
 acall_kept SEGS B lyc Sc Wc mT W2 mem2 (crt_sp1 - ASTACK) crt_sp1 (fun a => pa <= a < pa + req_size na) ->
 crts7_kept lyc Sc Wc mc W2 mem2 pa na.
Proof.
intros lyc Sc Wc mc dc mT W2 mem2 pa na HAR K0 (A1 & A2 & A3 & A4 & _).
pose proof asan_consts as (C1 & _).
split; [|split; [|split]].
- intros a Ha Hn. rewrite (A1 a Ha Hn). apply K0. lia.
- intros b m i Hin Hi Hn. rewrite (A2 b m i Hin Hi Hn). apply K0.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hc & _). lia.
- intros a Hi Ho He. rewrite (A3 a Hi Ho He). apply K0. pose proof (pa_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia.
- intros cid pos a Hin Hr Hn. rewrite (A4 cid pos a Hin Hr Hn). apply K0.
  destruct (frames_bounds SEGS B LAWS lyc Sc Wc mc dc cid pos HAR Hin) as (F1 & F2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  assert (D : (0 <= frame_addr lyc cid pos / 8 <= frame_addr lyc cid pos) /\ (0 <= fs_frame_bytes cid / 8 <= fs_frame_bytes cid)).
  { split; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hr. cbn [fst snd] in Hr.
  set (d1 := frame_addr lyc cid pos / 8) in *. set (d2 := fs_frame_bytes cid / 8) in *. clearbody d1 d2. lia.
Qed.
(* the class-5 frame at a point of the walk, against a live block *)
Lemma crts7_ff : forall pos lyc Sc (Wc : world SEGS) mc dc k pa na, crt_J pos lyc Sc Wc mc dc k -> In (pa, na) (ablocks B lyc Sc) ->
 In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = crt_F pos /\
 4096 <= crt_F pos /\ crt_F pos + fs_frame_bytes 5 <= alloc_ceiling /\
 (pa + req_size na <= crt_F pos \/ crt_F pos + fs_frame_bytes 5 <= pa) /\ in_app pa (req_size na) /\ fs_frame_bytes 5 = 2048.
Proof.
intros pos lyc Sc Wc mc dc k pa na HJ Hin. pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (Hfin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (Efa : frame_addr lyc 5 pos = crt_F pos)
  by (unfold crt_F, frame_addr; destruct Hly as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc mc dc 5 pos HAR Hfin) as (F1 & F2 & _).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc mc dc pa na 5 pos HAR Hin Hfin) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pa na HAR Hin) as (_ & _ & _ & Happ & _).
rewrite Efa in F1, F2, Hd.
split; [exact Hfin|]. split; [exact Efa|]. split; [exact F1|]. split; [exact F2|]. split; [exact Hd|].
split; [exact Happ | reflexivity].
Qed.
Lemma crts7_fr_keep : forall pos lyc Sc (Wc : world SEGS) mc dc k (W2 : world SEGS) mem2 pa na,
 crt_J pos lyc Sc Wc mc dc k -> In (pa, na) (ablocks B lyc Sc) ->
 crts7_kept lyc Sc Wc mc W2 mem2 pa na -> crt_fr pos Wc mc -> crt_fr pos W2 mem2.
Proof.
intros pos lyc Sc Wc mc dc k W2 mem2 pa na HJ Hin (K1 & _ & _ & K4) (FR & FL & FS).
destruct (crts7_ff pos lyc Sc Wc mc dc k pa na HJ Hin) as (Hfin & Efa & F1 & F2 & Hd & Happ & FS5).
pose proof crt_sp0 as (S1 & S2 & S3 & S4 & S5). pose proof crt_sp1_bounds as (P1 & _).
pose proof asan_consts as (C1 & _).
split; [|split].
- intros j r Hj. assert (Hj13 : (j < 13)%nat) by (rewrite <- crt_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
  apply (crt_aval_kept (rdW Wc mc)); [|exact (FR j r Hj)].
  intros kk Hkk. apply K1; lia.
- rewrite (rdword_ext (rdW Wc mc) (rdW W2 mem2) (crt_F pos + fs_frame_bytes 5 - 8)); [exact FL|].
  intros kk Hkk. apply (K4 5 pos); [exact Hfin | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa; lia | lia].
- intros i Hi.
  pose proof (Z.div_pos (crt_F pos) 8 ltac:(lia) ltac:(lia)) as D1.
  pose proof (Z.mul_div_le (crt_F pos) 8 ltac:(lia)) as D2.
  assert (FS8 : fs_frame_bytes 5 / 8 = 256) by (rewrite FS5; reflexivity).
  rewrite (K4 5 pos (crt_SH pos + i) Hfin); [exact (FS i Hi) | |].
  + right. unfold in_zr, crt_SH, shadow_addr. cbn [fst snd]. rewrite Efa, FS8.
    set (d := crt_F pos / 8) in *. clearbody d. lia.
  + unfold crt_SH, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
    set (d := crt_F pos / 8) in *. clearbody d. lia.
Qed.
Lemma crts7_slots_keep : forall lyc Sc (Wc : world SEGS) mc (W2 : world SEGS) mem2 pa na L,
 crts7_kept lyc Sc Wc mc W2 mem2 pa na -> Forall (fun ov => 0 <= fst ov <= 248) L ->
 crt_slots Wc mc L -> crt_slots W2 mem2 L.
Proof.
intros lyc Sc Wc mc W2 mem2 pa na L (K1 & _) HL HS.
pose proof crt_sp0 as (S1 & S2 & S3 & S4 & S5). pose proof crt_sp1_bounds as (P1 & _).
unfold crt_slots in *. rewrite Forall_forall in *. intros ov Hin. pose proof (HL ov Hin) as Hb.
apply (crt_aval_kept (rdW Wc mc)); [|exact (HS ov Hin)].
intros kk Hkk. apply K1; lia.
Qed.
Lemma crts7_q_keep : forall lyc Sc (Wc : world SEGS) mc (W2 : world SEGS) mem2 pa na v,
 crts7_kept lyc Sc Wc mc W2 mem2 pa na -> aval_mem (rdW Wc mc) A_G_QUITTING 4 v -> aval_mem (rdW W2 mem2) A_G_QUITTING 4 v.
Proof.
intros lyc Sc Wc mc W2 mem2 pa na v (_ & _ & K3 & _) H.
apply (crt_aval_kept (rdW Wc mc)); [|exact H].
intros kk Hkk.
assert (Hpg : inFP cmd_PG (A_G_QUITTING + kk))
  by (exists (A_G_QUITTING, A_G_QUITTING + 4); split; [right; right; left; reflexivity | cbn [fst snd]; lia]).
destruct (crt_pg _ Hpg) as [Ho He]. exact (K3 _ (cif_prog_img _ Hpg) Ho He).
Qed.
Lemma crts7_rep_keep : forall lyc Sc (Wc : world SEGS) mc ly2 S2 (W2 : world SEGS) mem2 pa na R2 O2,
 crts7_kept lyc Sc Wc mc W2 mem2 pa na ->
 Permutation (ablocks B lyc Sc) (ablocks B ly2 S2 ++ [(pa, na)]) ->
 (forall p n i, In (p, n) (ablocks B ly2 S2) -> 0 <= i < n -> rdW W2 mem2 (p + i) = rdW Wc mc (p + i)) ->
 ~ In (pa, na) O2 ->
 rec_repA B lyc Sc (rdW Wc mc) R2 O2 -> rec_repA B ly2 S2 (rdW W2 mem2) R2 O2.
Proof.
intros lyc Sc Wc mc ly2 S2 W2 mem2 pa na R2 O2 (_ & _ & K3 & _) PF KBL Hn HR.
apply (rcf_rep_repA B lyc Sc ly2 S2 (rdW Wc mc) (rdW W2 mem2) R2 O2 [(pa, na)] HR); [| exact PF | | exact KBL].
- intros a Ha. pose proof (crt_inrec_pg a Ha) as Hpg. destruct (crt_pg a Hpg) as [Ho He].
  exact (K3 a (cif_prog_img a Hpg) Ho He).
- intros pn [Hp | []]. rewrite <- Hp. exact Hn.
Qed.
Lemma crts7_tbl_keep : forall pos lyc Sc (Wc : world SEGS) mc dc k ly2 S2 (W2 : world SEGS) mem2 pa na qs,
 crt_J pos lyc Sc Wc mc dc k -> In (pa, na) (ablocks B lyc Sc) ->
 crts7_kept lyc Sc Wc mc W2 mem2 pa na ->
 Permutation (ablocks B lyc Sc) (ablocks B ly2 S2 ++ [(pa, na)]) ->
 (forall p n i, In (p, n) (ablocks B ly2 S2) -> 0 <= i < n -> rdW W2 mem2 (p + i) = rdW Wc mc (p + i)) ->
 ~ In (pa, na) (concat qs) ->
 crt_tbl pos lyc Sc Wc mc qs -> crt_tbl pos ly2 S2 W2 mem2 qs.
Proof.
intros pos lyc Sc Wc mc dc k ly2 S2 W2 mem2 pa na qs HJ Hin (K1 & K2 & K3 & K4) PF KBL Hnq (T1 & T2 & T3 & T4).
destruct (crts7_ff pos lyc Sc Wc mc dc k pa na HJ Hin) as (Hfin & Efa & F1 & F2 & Hd & Happ & FS5).
split; [exact T1|]. split; [exact T2|]. split; [|exact T4].
intros i c P Hc HPq. destruct (T3 i c P Hc HPq) as [HA HS]. split; [|exact HS].
assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
apply (rcfr_call_keep (ablocks B lyc Sc) (ablocks B ly2 S2) (rdW Wc mc) (rdW W2 mem2) _ c P HA).
- intros x Hx. unfold CALL_SIZE in *.
  apply (K4 5 pos x Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa; lia | lia].
- intros pn HinP Hinb.
  apply (rcfr_blk_keep (ablocks B lyc Sc) (ablocks B ly2 S2) [(pa, na)] (rdW Wc mc) (rdW W2 mem2) pn PF); [|exact KBL|exact Hinb].
  intros [Hp | []]. apply Hnq. rewrite Hp. apply in_concat. exists P. split; [exact (nth_error_In _ _ HPq) | exact HinP].
Qed.
(* after the free: the blocks left, their bytes, the live bytes *)
Lemma crts7_common : forall pos lyc Sc (Wc : world SEGS) mc dc k ly2 S2 (W2 : world SEGS) mem2 pa na l1 l2 L,
 crt_J pos lyc Sc Wc mc dc k -> crts7_kept lyc Sc Wc mc W2 mem2 pa na ->
 ablocks B lyc Sc = l1 ++ (pa, na) :: l2 -> ablocks B ly2 S2 = l1 ++ l2 ->
 Permutation (ablocks B lyc Sc) (L ++ [(pa, na)]) ->
 Permutation (ablocks B ly2 S2) L /\
 Permutation (ablocks B lyc Sc) (ablocks B ly2 S2 ++ [(pa, na)]) /\
 (forall p n i, In (p, n) (ablocks B ly2 S2) -> 0 <= i < n -> rdW W2 mem2 (p + i) = rdW Wc mc (p + i)) /\
 blocks_bytes S2 <= blocks_bytes Sc.
Proof.
intros pos lyc Sc Wc mc dc k ly2 S2 W2 mem2 pa na l1 l2 L HJ (K1 & K2 & K3 & K4) Ebl Ebl2 HP.
pose proof HJ as (HAR & _).
pose proof (crt_nodup lyc Sc Wc mc dc HAR) as ND.
assert (PF : Permutation (ablocks B lyc Sc) (ablocks B ly2 S2 ++ [(pa, na)])).
{ rewrite Ebl, Ebl2, <- app_assoc. apply Permutation_app_head. apply Permutation_cons_append. }
assert (Hx : In (pa, na) (ablocks B lyc Sc)) by (rewrite Ebl; apply in_or_app; right; left; reflexivity).
assert (Hnx : ~ In (pa, na) (l1 ++ l2)) by (rewrite Ebl in ND; exact (List.NoDup_remove_2 l1 l2 (pa, na) ND)).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pa na HAR Hx) as (_ & _ & _ & _ & _ & _ & Hna).
split; [|split; [exact PF|split]].
- exact (Permutation_app_inv_r [(pa, na)] _ _ (Permutation_trans (Permutation_sym PF) HP)).
- intros p n i Hin Hi. rewrite Ebl2 in Hin.
  assert (Hne : (p, n) <> (pa, na)) by (intros E; rewrite E in Hin; exact (Hnx Hin)).
  assert (Hinc : In (p, n) (ablocks B lyc Sc))
    by (rewrite Ebl; apply in_app_or in Hin as [H|H]; [apply in_or_app; left; exact H | apply in_or_app; right; right; exact H]).
  pose proof (sep_blocks SEGS B LAWS lyc Sc Wc mc dc p n pa na HAR Hinc Hx Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hinc) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos n (proj1 Hn)) as [_ Hrs].
  apply (K2 p n i); [exact Hinc | lia | lia].
- rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B lyc Sc), Ebl, Ebl2, !YCbq.bsum_app, YCbq.bsum_cons.
  cbn [snd]. lia.
Qed.
(* the run `mv a0, sX; jal wrapper_free` from 0x88260 (s6 = line) or 0x88304 (s5 = reply_first) *)
Lemma crts7_run : forall pc (src : bv 5) lyc Sc (Wc : world SEGS) mc dc rX pos k (Q : world SEGS -> config -> Prop),
 (pc = 7548 /\ src = 22%bv) \/ (pc = 7712 /\ src = 21%bv) ->
 crt_J pos lyc Sc Wc mc dc k ->
 (forall (rT : bvmap 5 word) (mT : word -> option byte) (dT : Model),
   crt_J pos lyc Sc Wc mT dT k ->
   (forall a, 0 <= a < 2 ^ 64 -> rdW Wc mT a = rdW Wc mc a) ->
   getr rT 10 = getr rX src -> getr rT 1 = Z_to_bv 64 (BASE + (pc + 8)) -> aregs_preserved rX rT ->
   SRr SEGS Wc (mkCfg (mkst rT (Z_to_bv 64 (pc_wrap_free (as_code B))) mT (seg_rom SEGS)) dT) Q) ->
 SRr SEGS Wc (cfgP pc rX mc dc) Q.
Proof.
intros pc src lyc Sc Wc mc dc rX pos k Q Hpc HJ HK.
pose proof (crts7_seed pc rX Wc mc) as HS.
assert (HEI : img_env VAL A_LIM (crts7_E rX)) by (unfold crts7_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (crts7_E rX) (mrestrict (w_H Wc) mc)) by (unfold sh_ok; apply Forall_nil).
unfold crt_J in HJ. unfold cfgP.
destruct Hpc as [[-> ->] | [-> ->]].
- paj_run_tok RUN HS HJ SHOK Bspan.
  { apply awr_ok_nil. }
  pose proof (crt_frame_nowin _ _ _ _ _ HFr ltac:(crt_nowin)) as K1. clear HF HFr HG. clear_md.
  pmkst HS. ppcs.
  eapply HK.
  + exact HJ.
  + exact K1.
  + crt_rreg HS. rewrite crt_den_atom0. unfold crts7_E. apply ew_Eimg_Ereg_nat. reflexivity.
  + crt_rreg HS. apply (codeptr_val _ _ HEI).
  + apply (aregs_preserved_of_st_ok SEGS _ _ _ _ rX [w64 SB] HS); [|vm_compute; reflexivity].
    split; [intros n Hn; unfold crts7_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- paj_run_tok RUN HS HJ SHOK Bspan.
  { apply awr_ok_nil. }
  pose proof (crt_frame_nowin _ _ _ _ _ HFr ltac:(crt_nowin)) as K1. clear HF HFr HG. clear_md.
  pmkst HS. ppcs.
  eapply HK.
  + exact HJ.
  + exact K1.
  + crt_rreg HS. rewrite crt_den_atom0. unfold crts7_E. apply ew_Eimg_Ereg_nat. reflexivity.
  + crt_rreg HS. apply (codeptr_val _ _ HEI).
  + apply (aregs_preserved_of_st_ok SEGS _ _ _ _ rX [w64 SB] HS); [|vm_compute; reflexivity].
    split; [intros n Hn; unfold crts7_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.
(* the free call itself (afree04_sub), from either point, back at pc + 8 *)
Lemma crts7_free : forall pc (src : bv 5) lyc Sc (Wc : world SEGS) mc dc rX pos k pa na,
 (pc = 7548 /\ src = 22%bv) \/ (pc = 7712 /\ src = 21%bv) ->
 crt_J pos lyc Sc Wc mc dc k -> crt_frame (rdW Wc mc) -> st_nev S + k < EV_MAX ->
 In (pa, na) (ablocks B lyc Sc) -> getr rX src = w64 pa ->
 getr rX 2 = w64 crt_sp1 -> getr rX 8 = w64 sp0 -> getr rX 3 = w64 (as_gp B) -> getr rX 4 = w64 (as_tp B) ->
 (In (pa, na) (ablocks B ly S) -> forall i, 0 <= i < req_size na -> inFP crt_FP (pa + i)) ->
 mo_ok MT Sc (mo_free MT) ->
 (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 l1 l2,
   crt_J pos ly2 S2 W2 mem2 md2 (k + 1) -> aregs_preserved rX regs2 ->
   ablocks B lyc Sc = l1 ++ (pa, na) :: l2 -> ablocks B ly2 S2 = l1 ++ l2 ->
   crts7_kept lyc Sc Wc mc W2 mem2 pa na -> mo_le MT Sc S2 (mo_free MT) ->
   SRr SEGS W2 (cfgP (pc + 8) regs2 mem2 md2) crt_post) ->
 SRr SEGS Wc (cfgP pc rX mc dc) crt_post.
Proof.
intros pc src lyc Sc Wc mc dc rX pos k pa na Hpc HJ HFRc Hev Hin Hsrc R2 R8 R3 R4 Hcov HMOK HC.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & _).
pose proof crt_sp0 as (S1 & S2' & S3 & S4 & S5). pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4).
pose proof asan_consts as (C1 & _).
pose proof (pa_base_lo (L := cmd_listing)) as HBLO. pose proof (@pa_B_ok _ _ PI) as HBASE.
pose proof HPRE as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & H47 & _ & _ & Htop2) & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (Hpc8 : 0 <= pc + 8 < 2 ^ 40 /\ (pc + 8) mod 2 = 0) by (destruct Hpc as [[-> _] | [-> _]]; (split; [lia | reflexivity])).
apply (crts7_run pc src lyc Sc Wc mc dc rX pos k crt_post Hpc HJ).
intros rT mT dT HJT K1 R10 R1 HPR.
assert (Q2 : getr rT 2 = w64 crt_sp1) by (rewrite (crt_preg _ _ 2%bv HPR) by crt_cs; exact R2).
assert (Q8 : getr rT 8 = w64 sp0) by (rewrite (crt_preg _ _ 8%bv HPR) by crt_cs; exact R8).
assert (Q3 : getr rT 3 = w64 (as_gp B)) by (rewrite (crt_preg _ _ 3%bv HPR) by crt_cs; exact R3).
assert (Q4 : getr rT 4 = w64 (as_tp B)) by (rewrite (crt_preg _ _ 4%bv HPR) by crt_cs; exact R4).
assert (Q10 : getr rT 10 = w64 pa) by (rewrite R10; exact Hsrc).
(* the frame chain at the call: the prologue's frame record on afn_pre's chain (s0 = sp0) *)
assert (FRT : crt_frame (rdW Wc mT)) by (apply (crt_frame_keep (rdW Wc mc)); [intros a Ha; apply K1; lia | exact HFRc]).
destruct (crt_chain pos lyc Sc Wc mT dT k HJT FRT) as (chT & Hch).
eapply SRr_bind.
{ apply (afree04_sub SEGS B LAWS pa_segs_low MT (AFREE4 fx) Wc rT mT STK sp0 crt_FP ly S W mem md [(5, pos)] lyc Sc dT k
    pa na (crt_sp1 - sp0) (Z_to_bv 64 (BASE + (pc + 8))) chT HJT).
  - exact Hin.
  - exact Q10.
  - unfold spZ at 1. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact P4.
  - lia.
  - rewrite crt_STK. unfold ASTACK. lia.
  - exact Q3.
  - exact Q4.
  - exact R1.
  - apply ret_ok_codeptr_v; [exact (proj1 Hpc8) | exact (proj2 Hpc8)].
  - lia.
  - apply (achain_chain_pre lyc _ crt_sp1 sp0 chT rT Hch).
    + unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia.
    + unfold s0Z. rewrite Q8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + unfold raZ. rewrite R1. rewrite unsigned_lit_small by lia. lia.
  - exact Hcov.
  - exact HMOK. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl & Ebl2) & Hfrs2 & HK & MLE & _).
replace (sp0 + (crt_sp1 - sp0)) with crt_sp1 in HK by lia.
apply (HC ly2 S2 W2 regs2 mem2 md2 l1 l2 HJ2 (aregs_preserved_trans _ _ _ HPR HP2) Ebl Ebl2).
- exact (crts7_kept_of lyc Sc Wc mc dc mT W2 mem2 pa na HAR K1 HK).
- exact MLE.
Qed.

(* ---------- after send_message (0x88260): free(line) ---------- *)
Lemma crt_s7 : ST_H -> ST_G.
Proof.
intros HSTH lyc Sc Wc mc dc rX pos qs res X line R2 O2 HJ HFR HTBL HPM HREP2 HR2 HQ2 HRPL HX0 HRES H4096 HL4096 HBB HMO HSL HRG.
pose proof HJ as (HAR & _).
set (L := O2 ++ rest ++ concat qs ++ [(res, Z.of_nat (length X) + 1)]).
assert (HPL : Permutation (ablocks B lyc Sc) (L ++ [(line, crt_jn)])) by (unfold L; rewrite <- !app_assoc; exact HPM).
pose proof (crt_nodup lyc Sc Wc mc dc HAR) as ND.
pose proof (crts7_notin _ _ _ ND HPL) as Hnx.
assert (Hin : In (line, crt_jn) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; right; left; reflexivity).
pose proof (crt_ev_args_nn R) as HEVA. pose proof (mo_free_nonneg MT MTL) as HMF.
assert (HMA : 0 <= ev_args R * mo_free MT) by (apply Z.mul_nonneg_nonneg; lia).
apply (crts7_free 7548 22%bv lyc Sc Wc mc dc rX pos crt_EVG line crt_jn (or_introl (conj eq_refl eq_refl)) HJ (proj1 HFR)).
- pose proof HEV as HEV'. unfold EV_CHECK_ROUND_TRIP in HEV'. unfold crt_EVG, crt_D. lia.
- exact Hin.
- refine (crt_rg rX (crt_RG pos res line) _ _ _ HRG _ eq_refl). unfold crt_RG; crt_in.
- refine (crt_rg rX (crt_RG pos res line) _ _ _ HRG _ eq_refl). unfold crt_RG; crt_in.
- refine (crt_rg rX (crt_RG pos res line) _ _ _ HRG _ eq_refl). unfold crt_RG; crt_in.
- refine (crt_rg rX (crt_RG pos res line) _ _ _ HRG _ eq_refl). unfold crt_RG; crt_in.
- refine (crt_rg rX (crt_RG pos res line) _ _ _ HRG _ eq_refl). unfold crt_RG; crt_in.
- apply (crts7_cov line crt_jn L Hnx). intros y Hy. unfold L. apply in_or_app. right. apply in_or_app. left. exact Hy.
- apply (mok_station MT S Sc (XM_CHECK_ROUND_TRIP MT R ws) crt_XMG (mo_free MT) MTL MOK HMO HMF).
  unfold XM_CHECK_ROUND_TRIP, crt_XMG, crt_D. lia.
- intros ly2 S2 W2 regs2 mem2 md2 l1 l2 HJ2 HP2 Ebl Ebl2 HK MLE.
  destruct (crts7_common pos lyc Sc Wc mc dc crt_EVG ly2 S2 W2 mem2 line crt_jn l1 l2 L HJ HK Ebl Ebl2 HPL)
    as (HPL2 & PF & KBL & HBB2).
  assert (HnO : ~ In (line, crt_jn) O2) by (intros H; apply Hnx; unfold L; apply in_or_app; left; exact H).
  assert (Hnq : ~ In (line, crt_jn) (concat qs))
    by (intros H; apply Hnx; unfold L; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact H).
  assert (Hres2 : In (res, Z.of_nat (length X) + 1) (ablocks B ly2 S2)).
  { apply (Permutation_in _ (Permutation_sym HPL2)). unfold L.
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; left; reflexivity. }
  apply (HSTH ly2 S2 W2 mem2 md2 regs2 pos qs res X R2 O2).
  + exact HJ2.
  + exact (crts7_fr_keep pos lyc Sc Wc mc dc crt_EVG W2 mem2 line crt_jn HJ Hin HK HFR).
  + exact (crts7_tbl_keep pos lyc Sc Wc mc dc crt_EVG ly2 S2 W2 mem2 line crt_jn qs HJ Hin HK PF KBL Hnq HTBL).
  + exact HPL2.
  + exact (crts7_rep_keep lyc Sc Wc mc ly2 S2 W2 mem2 line crt_jn R2 O2 HK PF KBL HnO HREP2).
  + exact HR2.
  + exact (crts7_q_keep lyc Sc Wc mc W2 mem2 line crt_jn q HK HQ2).
  + exact HRPL.
  + exact HX0.
  + apply (rcfr_bytes_keep (rdW Wc mc) _ _ _ HRES). intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    apply (KBL res (Z.of_nat (length X) + 1) i Hres2). lia.
  + exact H4096.
  + lia.
  + exact (mo_le_trans MT MTL _ _ _ _ _ HMO MLE).
  + apply (crts7_slots_keep lyc Sc Wc mc W2 mem2 line crt_jn); [exact HK | | exact HSL].
    unfold crt_SLE. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia.
  + apply (crt_regs_pres rX regs2); [exact HP2 | |].
    * unfold crt_RH. repeat apply Forall_cons; try apply Forall_nil; unfold acallee_saved; cbn [fst]; lia.
    * apply (crts7_regs_sub rX (crt_RG pos res line)); [|exact HRG].
      intros x Hx. unfold crt_RH, crt_RG in Hx |- *. cbn [In] in Hx |- *. tauto.
Qed.
(* ---------- s8 / s9: the facts of the points ST_H and ST_I across a run without stores and across a call ---------- *)
(* a reader of the view depends on the address only through its 64-bit word *)
Lemma crts8_view_mod : forall H (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity.
Qed.
Lemma crts8_view_all : forall H (m m' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' HK a. rewrite (crts8_view_mod H m' a), (crts8_view_mod H m a). apply HK. apply Z.mod_pos_bound. lia.
Qed.
(* what the facts of ST_H / ST_I read: the realigned frame and above, the program statics, the live blocks, the
   class-5 frame and its shadow *)
Definition crts8_kp (pos : Z) lyc Sc (rd rd' : reader) : Prop :=
 (forall a, crt_sp1 <= a < 2 ^ 64 -> rd' a = rd a) /\
 (forall a, inFP cmd_PG a -> rd' a = rd a) /\
 (forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < n -> rd' (p + i) = rd (p + i)) /\
 (forall a, crt_F pos <= a < crt_F pos + fs_frame_bytes 5 \/ crt_SH pos <= a < crt_SH pos + fs_frame_bytes 5 / 8 ->
   rd' a = rd a).
Lemma crts8_kp_trans : forall pos lyc Sc rd1 rd2 rd3, crts8_kp pos lyc Sc rd1 rd2 -> crts8_kp pos lyc Sc rd2 rd3 ->
  crts8_kp pos lyc Sc rd1 rd3.
Proof.
intros pos lyc Sc rd1 rd2 rd3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4).
split; [intros a Ha; rewrite (B1 a Ha); exact (A1 a Ha)|].
split; [intros a Ha; rewrite (B2 a Ha); exact (A2 a Ha)|].
split; [intros p n i Hin Hi; rewrite (B3 p n i Hin Hi); exact (A3 p n i Hin Hi)|].
intros a Ha. rewrite (B4 a Ha). exact (A4 a Ha).
Qed.
Lemma crts8_kp_all : forall pos lyc Sc H (m m' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a) -> crts8_kp pos lyc Sc (aview SEGS H m) (aview SEGS H m').
Proof.
intros pos lyc Sc H m m' HK. pose proof (crts8_view_all H m m' HK) as HA.
split; [intros; apply HA|]. split; [intros; apply HA|]. split; [intros; apply HA|]. intros; apply HA.
Qed.
(* a call that may change only a stack window below s1 *)
Lemma crts8_kp_win : forall pos lyc Sc H (m m' : word -> option byte) lo,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < crt_sp1) -> aview SEGS H m' a = aview SEGS H m a) ->
  alloc_ceiling <= lo ->
  (forall p n, In (p, n) (ablocks B lyc Sc) -> 0 <= p /\ p + n <= alloc_ceiling) ->
  0 <= crt_F pos -> crt_F pos + fs_frame_bytes 5 <= alloc_ceiling ->
  crts8_kp pos lyc Sc (aview SEGS H m) (aview SEGS H m').
Proof.
intros pos lyc Sc H m m' lo HK Hlo HBL H0 HF.
pose proof alloc_ceiling_value as (ACv & _). pose proof crt_sp0 as (S1 & S2 & _). pose proof crt_sp1_bounds as (P1 & _).
assert (Hfb : fs_frame_bytes 5 = 2048) by reflexivity. assert (Hfb8 : fs_frame_bytes 5 / 8 = 256) by reflexivity.
split; [intros a Ha; apply HK; lia|].
split.
{ intros a (r & Hr & Ha). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; apply HK; lia. }
split; [intros p n i Hin Hi; destruct (HBL p n Hin); apply HK; lia|].
intros a Ha. rewrite Hfb8, Hfb in Ha. unfold crt_SH, SHADOW_OFF in Ha.
assert (Hq1 : 0 <= crt_F pos / 8) by (apply Z.div_pos; lia).
assert (Hq2 : crt_F pos / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
apply HK; lia.
Qed.
(* a callee whose footprint is empty, called with sp = s1 *)
Lemma crts8_kp_journal : forall pos lyc Sc (Wa Wb : world SEGS) ma mda mb mdb STK1 k,
  ajournal SEGS B STK1 crt_sp1 [] lyc Sc Wa ma mda [] lyc Sc Wb mb mdb k ->
  In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = crt_F pos ->
  crts8_kp pos lyc Sc (rdW Wa ma) (rdW Wb mb).
Proof.
intros pos lyc Sc Wa Wb ma mda mb mdb STK1 k HJ Hfin Efa.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
pose proof crt_sp0 as (S1 & S2 & _). pose proof crt_sp1_bounds as (P1 & _).
assert (HSP : ~ YI16.sink_open_fp []) by (apply sink_closed_pos; apply Forall_nil).
split; [intros a Ha; apply F1; [lia | lia | apply inFP_nil]|].
split.
{ intros a Ha. destruct (crt_pg a Ha) as [Ho He].
  apply F3; [exact (cif_prog_img a Ha) | exact Ho | exact He | apply fp_spares_closed; [exact HSP | apply inFP_nil]]. }
split.
{ intros p n i Hin Hi. pose proof (req_size_pos n ltac:(lia)) as [_ Hq]. apply (F2 p n i); [exact Hin | exact Hin | lia | apply inFP_nil]. }
intros a Ha. apply (F4 5 pos a Hfin); [|apply inFP_nil].
unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. unfold shadow_addr. unfold crt_SH in Ha. lia.
Qed.
(* the class-5 frame at a point of the walk *)
Lemma crts8_frame : forall pos lyc Sc Wc mc dc k, crt_J pos lyc Sc Wc mc dc k ->
  In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = crt_F pos /\ 4096 <= crt_F pos /\
  crt_F pos + fs_frame_bytes 5 <= alloc_ceiling /\ crt_F pos mod 8 = 0 /\ crt_F pos = 8 * (crt_F pos / 8).
Proof.
intros pos lyc Sc Wc mc dc k HJ.
pose proof HPRE as (HAR & _).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc HAR Hly) as (_ & Efa & _).
assert (Hfin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc mc dc 5 pos HARc Hfin) as (H1 & H2 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 5 pos HARc Hfin) as (H3 & _).
assert (H4 : frame_addr lyc 5 pos mod 8 = 0 /\ frame_addr lyc 5 pos = 8 * (frame_addr lyc 5 pos / 8)).
{ pose proof (Z.div_mod (frame_addr lyc 5 pos) 32 ltac:(lia)) as D32.
  pose proof (Z.div_mod (frame_addr lyc 5 pos) 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound (frame_addr lyc 5 pos) 8 ltac:(lia)) as M8. lia. }
unfold crt_F. rewrite <- (Efa 5 pos).
split; [exact Hfin|]. split; [reflexivity|]. split; [exact H1|]. split; [exact H2 | exact H4].
Qed.
(* the facts of ST_H / ST_I carried to a reader that keeps what they read *)
Lemma crts8_keep : forall pos lyc Sc (Wa Wb : world SEGS) ma mb qs res (X : list byte) R2 O2,
  crts8_kp pos lyc Sc (rdW Wa ma) (rdW Wb mb) ->
  crt_fr pos Wa ma -> crt_tbl pos lyc Sc Wa ma qs -> rec_repA B lyc Sc (rdW Wa ma) R2 O2 ->
  aval_mem (rdW Wa ma) A_G_QUITTING 4 q -> abytes_atR (rdW Wa ma) res (X ++ [Z_to_bv 8 0]) ->
  In (res, Z.of_nat (length X) + 1) (ablocks B lyc Sc) -> crt_slots Wa ma (crt_SLE pos) ->
  crt_fr pos Wb mb /\ crt_tbl pos lyc Sc Wb mb qs /\ rec_repA B lyc Sc (rdW Wb mb) R2 O2 /\
  aval_mem (rdW Wb mb) A_G_QUITTING 4 q /\ abytes_atR (rdW Wb mb) res (X ++ [Z_to_bv 8 0]) /\ crt_slots Wb mb (crt_SLE pos).
Proof.
intros pos lyc Sc Wa Wb ma mb qs res X R2 O2 (K1 & K2 & K3 & K4) (Hfr & Hfl & Hsh) (Hlq & HND & Htb & Hap) HREP' HVQ' HRES' Hres HSL'.
pose proof crt_sp0 as (S1 & S2 & _). pose proof crt_sp1_bounds as (P1 & _).
assert (Hfb : fs_frame_bytes 5 = 2048) by reflexivity.
split; [split; [|split]|].
- intros j r Hj. assert (Hj13 : (j < 13)%nat) by (rewrite <- crt_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
  apply (crt_aval_kept (rdW Wa ma)); [|exact (Hfr j r Hj)]. intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply K1. lia.
- rewrite (rdword_ext (rdW Wa ma) (rdW Wb mb)); [exact Hfl|]. intros kk Hkk. apply K4. left. rewrite Hfb. lia.
- intros i Hi. rewrite (K4 (crt_SH pos + i)) by (right; change (fs_frame_bytes 5 / 8) with 256; lia). exact (Hsh i Hi).
- split; [|split; [|split; [|split]]].
  + split; [exact Hlq|]. split; [exact HND|]. split; [|exact Hap].
    intros i c P Hc HP. destruct (Htb i c P Hc HP) as (Hcall & Hsz). split; [|exact Hsz].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    apply (rcfr_call_keep (ablocks B lyc Sc) (ablocks B lyc Sc) (rdW Wa ma) (rdW Wb mb) _ c P Hcall).
    * intros x Hx. apply K4. left. rewrite Hfb. unfold CALL_SIZE in Hx |- *. lia.
    * intros [p n] HpP Hpb. split; [exact Hpb|]. intros ii Hii. cbn [fst snd] in Hii |- *. exact (K3 p n ii Hpb Hii).
  + apply (rcf_rep_repA B lyc Sc lyc Sc (rdW Wa ma) (rdW Wb mb) R2 O2 [] HREP').
    * intros a Ha. apply K2. exact (crt_inrec_pg a Ha).
    * rewrite app_nil_r. apply Permutation_refl.
    * intros pn [].
    * exact K3.
  + apply (rcfr_aval_keep (rdW Wa ma) _ _ _ _ HVQ'). intros kk Hkk. apply K2.
    exists (A_G_QUITTING, A_G_QUITTING + 4). split; [right; right; left; reflexivity | cbn [fst snd]; lia].
  + apply (rcfr_bytes_keep (rdW Wa ma) _ _ _ HRES'). intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    apply (K3 res (Z.of_nat (length X) + 1) i Hres). lia.
  + apply Forall_forall. intros [o v] Hin. pose proof (proj1 (Forall_forall _ _) HSL' (o, v) Hin) as Hv. cbn [fst snd] in Hv |- *.
    assert (Ho : 0 <= o <= 120).
    { unfold crt_SLE in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- _; lia|]). destruct Hin. }
    apply (crt_aval_kept (rdW Wa ma)); [|exact Hv]. intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply K1. lia.
Qed.
Ltac crts8_in := cbn [crt_RH crt_RI crt_SLE]; crt_in.
(* a register of the run's end state that is its own atom: its value at the segment's entry *)
Ltac crts8_own HS EE HRG k kn v Q :=
  let P := fresh "P" in prreg HS (Z_to_bv 5 k) P;
  lazymatch type of P with getr ?rr _ = _ =>
  assert (Q : getr rr (Z_to_bv 5 k) = w64 v)
    by (rewrite P, (EE kn (Z_to_bv 5 k) eq_refl); exact (crt_reg _ _ k v HRG ltac:(crts8_in))) end;
  clear P.
(* a register set in the seed to an expression of its value *)
Lemma crts8_pin : forall E ss ms (r : bv 5) e,
  st_ok_pi SEGS VAL E ss ms -> getr (ms_regs ms) r = sv_denot E e -> bv_eqb r 0 = false ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr Hr0. unfold st_ok_pi, abs_ss, setpc in HS |- *.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in HS |- *.
apply (st_ok_regs SEGS E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
  (sr_set (ss_regs ss) r e) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. pose proof (st_ok_reg SEGS E _ ms r HS) as Hq. cbn [ss_regs] in Hq. rewrite <- Hq, Hr. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
Lemma crts8_n8 : 8 * Z.of_N 8 = 64. Proof. reflexivity. Qed.
Lemma crts8_n4 : 8 * Z.of_N 4 = 32. Proof. reflexivity. Qed.

(* ---------- the two tables rec_calls_equal compares ---------- *)
Fixpoint crts8_args (ss : list (list byte)) (P : list (Z * Z)) : list (word * list byte) :=
 match ss, P with
 | s :: ss', pn :: P' => (Z_to_bv 64 (fst pn), s) :: crts8_args ss' P'
 | _, _ => []
 end.
Fixpoint crts8_ents (cs : list rcall) (Ps : list (list (Z * Z))) : list PRce.rc_entry :=
 match cs, Ps with
 | c :: cs', P :: Ps' => (fst c, crts8_args (snd c) P) :: crts8_ents cs' Ps'
 | _, _ => []
 end.
Lemma crts8_args_len : forall ss P, length P = length ss -> length (crts8_args ss P) = length ss.
Proof.
induction ss as [|s ss IH]; intros [|pn P] H; cbn in H |- *; try reflexivity; try discriminate.
f_equal. apply IH. lia.
Qed.
Lemma crts8_ents_len : forall cs Ps, length Ps = length cs -> length (crts8_ents cs Ps) = length cs.
Proof.
induction cs as [|c cs IH]; intros [|P Ps] H; cbn in H |- *; try reflexivity; try discriminate.
f_equal. apply IH. lia.
Qed.
Lemma crts8_args_nth : forall ss P k p, nth_error (crts8_args ss P) k = Some p ->
  exists s pn, nth_error ss k = Some s /\ nth_error P k = Some pn /\ p = (Z_to_bv 64 (fst pn), s).
Proof.
induction ss as [|s ss IH]; intros [|pn P] [|k] p H; cbn in H; try discriminate.
- injection H as <-. exists s, pn. split; [reflexivity|]. split; reflexivity.
- exact (IH P k p H).
Qed.
Lemma crts8_ents_nth : forall cs Ps i e, nth_error (crts8_ents cs Ps) i = Some e ->
  exists c P, nth_error cs i = Some c /\ nth_error Ps i = Some P /\ e = (fst c, crts8_args (snd c) P).
Proof.
induction cs as [|c cs IH]; intros [|P Ps] [|i] e H; cbn in H; try discriminate.
- injection H as <-. exists c, P. split; [reflexivity|]. split; reflexivity.
- exact (IH Ps i e H).
Qed.
Lemma crts8_cstr_refl : forall s, PRce.cstr_eqb s s = true.
Proof.
intros s. unfold PRce.cstr_eqb.
destruct (list_eq_dec Z.eq_dec (map bv_unsigned s) (map bv_unsigned s)) as [_|Hn]; [reflexivity | exfalso; exact (Hn eq_refl)].
Qed.
Lemma crts8_args_eqb : forall ss P1 P2, length P1 = length ss -> length P2 = length ss ->
  PRce.args_eqb (crts8_args ss P1) (crts8_args ss P2) = true.
Proof.
induction ss as [|s ss IH]; intros [|p1 P1] [|p2 P2] H1 H2; cbn in H1, H2 |- *; try reflexivity; try discriminate.
rewrite crts8_cstr_refl. cbn [andb]. apply IH; lia.
Qed.
Lemma crts8_calls_eqb : forall cs Ps1 Ps2, length Ps1 = length cs -> length Ps2 = length cs ->
  (forall i c P1 P2, nth_error cs i = Some c -> nth_error Ps1 i = Some P1 -> nth_error Ps2 i = Some P2 ->
    length P1 = length (snd c) /\ length P2 = length (snd c)) ->
  PRce.calls_eqb (crts8_ents cs Ps1) (crts8_ents cs Ps2) = true.
Proof.
induction cs as [|c cs IH]; intros [|P1 Ps1] [|P2 Ps2] H1 H2 HL; cbn in H1, H2 |- *; try reflexivity; try discriminate.
destruct (HL 0%nat c P1 P2 eq_refl eq_refl eq_refl) as [L1 L2].
rewrite Z.eqb_refl, (crts8_args_eqb (snd c) P1 P2 L1 L2). cbn [andb].
apply IH; [lia | lia |]. intros i c' P1' P2' Hc Hp1 Hp2. exact (HL (Datatypes.S i) c' P1' P2' Hc Hp1 Hp2).
Qed.
(* a table of recorded calls (acall_at at each slot) at an 8-aligned base is rec_calls_equal's rce_calls *)
Lemma crts8_rce : forall lyc Sc (Wc : world SEGS) mc dc t cs Ps,
  AR SEGS B lyc Sc Wc mc dc -> (length cs <= 16)%nat -> length Ps = length cs -> t mod 8 = 0 ->
  rce_home B lyc Sc Wc mc t (CALL_SIZE * Z.of_nat (length cs)) ->
  (forall i c P, nth_error cs i = Some c -> nth_error Ps i = Some P ->
    acall_at (ablocks B lyc Sc) (rdW Wc mc) (t + CALL_SIZE * Z.of_nat i) c P) ->
  rce_calls B lyc Sc Wc mc t (crts8_ents cs Ps).
Proof.
intros lyc Sc Wc mc dc t cs Ps HAR H16 HL Ht8 Hh Hc.
rewrite <- (crts8_ents_len cs Ps HL) in H16, Hh.
split; [exact H16|]. split; [exact Ht8|]. split; [exact Hh|].
intros i e He. destruct (crts8_ents_nth cs Ps i e He) as (c & P & Hci & HPi & ->). cbn [fst snd].
destruct (Hc i c P Hci HPi) as (Hfn & Hn6 & HlP & Vfn & Vna & _ & Hargs).
rewrite (crts8_args_len (snd c) P HlP).
split; [unfold REC_FN_COUNT in Hfn; lia|]. split; [exact Hn6|]. split; [exact Vfn|]. split; [exact Vna|].
intros k p Hp. destruct (crts8_args_nth (snd c) P k p Hp) as (s & pn & Hs & Hpn & ->). cbn [fst snd].
destruct (Hargs k s pn Hs Hpn) as (Va & _ & Hin & Hsz & Hstr).
destruct pn as [pp nn]. cbn [fst snd] in Va, Hin, Hsz, Hstr |- *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp nn HAR Hin) as (_ & Hp4 & Hpc & _ & _ & _ & Hm).
pose proof alloc_ceiling_lt as HAC. pose proof (req_size_pos nn ltac:(lia)) as [_ Hq].
rewrite unsigned_lit_small by lia.
split; [exact Va|]. split; [exists pp, nn; split; [exact Hin | lia]|]. exact Hstr.
Qed.
(* the copies' table lies in the class-5 frame (first[], s2 + 32), its shadow laid usable *)
Lemma crts8_home_tbl : forall pos lyc Sc (Wc : world SEGS) mc dc k,
  crt_J pos lyc Sc Wc mc dc k -> crt_fr pos Wc mc ->
  rce_home B lyc Sc Wc mc (crt_F pos + 32) (CALL_SIZE * Z.of_nat (length (r_calls R))).
Proof.
intros pos lyc Sc Wc mc dc k HJ (_ & _ & Hsh).
destruct (crts8_frame pos lyc Sc Wc mc dc k HJ) as (Hfin & Efa & HF4 & HFc & HF8 & HF8').
assert (Hfb : fs_frame_bytes 5 = 2048) by reflexivity.
right. right. split; [|split].
- exists 5, pos. rewrite Efa, Hfb. unfold CALL_SIZE. split; [exact Hfin|]. split; [lia|]. split; [exact HF8|]. split; lia.
- rewrite Z.add_mod, HF8 by lia. reflexivity.
- intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr, CALL_SIZE in Hx |- *.
  replace (SHADOW_OFF + x / 8) with (crt_SH pos + (x - crt_F pos) / 8).
  + apply Hsh. split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia.
  + unfold crt_SH. replace x with ((x - crt_F pos) + (crt_F pos / 8) * 8) at 2 by lia.
    rewrite Z.div_add by lia. lia.
Qed.

(* ---------- s8: from 0x88268 to the call of rec_calls_equal ---------- *)
Definition crts8_ss : sstate := mkSS 7556 sr_atoms
  [YP09.mkRegion (Some 9%nat) 96 112 0 0 [YP09.mkChunk 96 (CVal 8 (SOff 33 0)); YP09.mkChunk 104 (CVal 8 (SOff 34 0))];
   YP09.mkRegion (Some 24%nat) 8 12 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 32 0))]] None
  (mkFacts [(2%nat, mkAF (2^46) (2^47) 5); (9%nat, mkAF (2^46) (2^47) 5); (27%nat, mkAF SB SB 0);
            (24%nat, mkAF A_G_REC A_G_REC 3); (32%nat, mkAF 0 16 0)] [] []).
Lemma crt_s8 : ST_I 7604 1 -> ST_H.
Proof.
intros HSTI lyc Sc Wc mc dc rX pos qs res X R2 O2 HJ HFR HTBL HPm HREP2 HR2 HVQ2 HRPL HNO0 HRES H4096 HBB HMLE HSL HRG.
pose proof crt_sp0 as (SP1 & SP2 & SP3 & SP4 & SP5). pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4).
pose proof alloc_ceiling_value as (ACv & _). pose proof alloc_ceiling_lt as HAC.
pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBlo.
pose proof HR2 as (EC2 & ER2 & _).
destruct (crts8_frame pos lyc Sc Wc mc dc _ HJ) as (Hfin & Efa & HF4 & HFc & HF8 & HF8').
assert (Hfb : fs_frame_bytes 5 = 2048) by reflexivity.
assert (Hres : In (res, Z.of_nat (length X) + 1) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPm|].
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. left; reflexivity. }
pose proof HREP2 as (Q & (_ & _ & _ & (HC16 & HCl & HNCv & _) & _) & _).
rewrite EC2 in HC16, HCl, HNCv.
(* the entry state of the segment: atoms 32, 33 the call count, atom 34 first[] *)
remember (Eimg (Ereg rX [w64 crt_nC; w64 crt_nC; w64 (crt_F pos + 32)])) as E eqn:HE.
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr rX r)
  by (intros nn r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 crt_nC) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 crt_nC) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew E 34 = w64 (crt_F pos + 32)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
pose proof (crt_reg rX _ 2 crt_sp1 HRG ltac:(crts8_in)) as R2r.
pose proof (crt_reg rX _ 9 crt_sp1 HRG ltac:(crts8_in)) as R9r.
pose proof (crt_reg rX _ 24 A_G_REC HRG ltac:(crts8_in)) as R24r.
pose proof (crt_reg rX _ 27 SHADOW_OFF HRG ltac:(crts8_in)) as R27r.
assert (E24 : ew E 24 = Z_to_bv 64 A_G_REC) by (rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl); exact R24r).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl); exact R27r).
assert (U2 : bv_unsigned (ew E 2) = crt_sp1)
  by (rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), R2r; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = crt_sp1)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9r; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = A_G_REC) by (rewrite E24; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF) by (rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = crt_nC) by (rewrite E32; apply unsigned_lit_small; unfold crt_nC; lia).
assert (HS : st_ok_pi SEGS VAL E crts8_ss (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + 7556)) mc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold crts8_ss. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS E _ crt_sp1 96 8 (SOff 33 0) crt_nC);
          [rewrite crt_den_atom0, E33; reflexivity | rewrite crts8_n8; unfold crt_nC; lia | change (Z.of_N 8) with 8; lia |].
        apply crt_val_of_aval. exact (crt_slot Wc mc _ 96 crt_nC HSL ltac:(crts8_in)).
      * apply (chunk_ok_val SEGS E _ crt_sp1 104 8 (SOff 34 0) (crt_F pos + 32));
          [rewrite crt_den_atom0, E34; reflexivity | rewrite crts8_n8; lia | change (Z.of_N 8) with 8; lia |].
        apply crt_val_of_aval. exact (crt_slot Wc mc _ 104 (crt_F pos + 32) HSL ltac:(crts8_in)).
    + rewrite U24. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ A_G_REC 8 4 (SOff 32 0) crt_nC);
        [rewrite crt_den_atom0, E32; reflexivity | rewrite crts8_n4; unfold crt_nC; lia | change (Z.of_N 4) with 4; lia |].
      apply crt_val_of_aval. exact HNCv.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U24.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_G_REC. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U27, U24, U32. rewrite ?Z.pow_0_r, ?Z.mod_1_r. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
    unfold SB, SHADOW_OFF, A_G_REC, crt_nC. repeat split; try reflexivity; try lia. }
assert (U27u : U E (SOff 27 0) = SHADOW_OFF)
  by (rewrite (U_atom_off E 27 SHADOW_OFF 0 E27) by (unfold SHADOW_OFF; lia); lia).
assert (U24u : U E (SOff 24 8) = A_G_REC + 8)
  by (rewrite (U_atom_off E 24 A_G_REC 8 E24) by (unfold A_G_REC; lia); reflexivity).
assert (SHOK : sh_ok SEGS (SOff 27 0) [] E (mrestrict (w_H Wc) mc)) by (unfold sh_ok; apply Forall_nil).
clear HE.
unfold cfgP. unfold crt_J in HJ.
(* 0x88268 .. 0x88294: the check of g_rec + 8, the call count, first[] and its count from slots 104 and 96 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ rewrite U27u, U24u. exact (cmd_addressable_chk lyc Sc Wc mc dc (A_G_REC + 8) 8 (proj1 HJ) ltac:(vm_compute; reflexivity)). }
{ awr_ok_tac. }
clear_md.
pose proof (crt_frame_nowin _ _ _ _ _ HFr ltac:(crt_nowin)) as K0. clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Pr1. prreg HS (10%bv : bv 5) Pr10. prreg HS (11%bv : bv 5) Pr11.
prreg HS (12%bv : bv 5) Pr12. prreg HS (13%bv : bv 5) Pr13.
prreg HS (Z_to_bv 5 22) Pr22. prreg HS (Z_to_bv 5 27) Pr27.
crts8_own HS EE HRG 2 2%nat crt_sp1 Q2. crts8_own HS EE HRG 9 9%nat crt_sp1 Q9.
crts8_own HS EE HRG 8 8%nat (spZ regs) Q8. crts8_own HS EE HRG 3 3%nat (as_gp B) Q3.
crts8_own HS EE HRG 4 4%nat (as_tp B) Q4. crts8_own HS EE HRG 18 18%nat (crt_F pos) Q18.
crts8_own HS EE HRG 20 20%nat (crt_shx (A_G_REC + 928)) Q20. crts8_own HS EE HRG 21 21%nat res Q21.
crts8_own HS EE HRG 23 23%nat (crt_shx (A_G_REC + 952)) Q23. crts8_own HS EE HRG 24 24%nat A_G_REC Q24.
crts8_own HS EE HRG 25 25%nat A_G_QUITTING Q25. crts8_own HS EE HRG 26 26%nat (crt_shx (A_G_REC + 944)) Q26.
lazymatch type of Pr22 with getr ?rr _ = _ =>
  assert (Q22 : getr rr (Z_to_bv 5 22) = w64 (crt_F pos + 32)) by (rewrite Pr22; exact E34);
  assert (Q27 : getr rr (Z_to_bv 5 27) = w64 crt_nC) by (rewrite Pr27; exact E33) end.
clear Pr22 Pr27.
rewrite (SIGP CS_rec_calls_equal ltac:(vm_compute; tauto)).
replace (VAL A_TEXT + cmd_af CS_rec_calls_equal) with (BASE + AF_rec_calls_equal)
  by (unfold cmd_af, AF_rec_calls_equal; vm_compute; reflexivity).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ => set (rT0 := rT) in *; set (mT0 := mT) in * end.
(* the facts at the call *)
pose proof (crts8_kp_all pos lyc Sc (w_H Wc) mc mT0 K0) as KP0.
destruct (crts8_keep pos lyc Sc Wc Wc mc mT0 qs res X R2 O2 KP0 HFR HTBL HREP2 HVQ2 HRES Hres HSL)
  as (HFR1 & HTBL1 & HREP1 & _ & _ & _).
pose proof (proj1 HJ) as HAR1.
pose proof HTBL1 as (Hlq & _ & Htb1 & _).
pose proof HREP1 as (Q1 & (_ & _ & _ & (HC16' & HCl' & _ & HCtab' & _) & _) & _).
rewrite EC2 in HC16', HCl', HCtab'.
set (ca := crts8_ents (r_calls R) qs). set (cb := crts8_ents (r_calls R) (l_calls Q1)).
assert (HCA : rce_calls B lyc Sc Wc mT0 (crt_F pos + 32) ca).
{ destruct (crts8_frame pos lyc Sc Wc mT0 mdv _ HJ) as (_ & _ & _ & _ & Hf8 & _).
  apply (crts8_rce lyc Sc Wc mT0 mdv); [exact HAR1 | lia | exact Hlq | | |].
  - rewrite Z.add_mod, Hf8 by lia. reflexivity.
  - exact (crts8_home_tbl pos lyc Sc Wc mT0 mdv _ HJ HFR1).
  - intros i c P Hc HP. exact (proj1 (Htb1 i c P Hc HP)). }
assert (HCB : rce_calls B lyc Sc Wc mT0 (A_G_REC + OFF_CALLS) cb).
{ apply (crts8_rce lyc Sc Wc mT0 mdv); [exact HAR1 | exact HC16' | exact HCl' | | |].
  - unfold A_G_REC, OFF_CALLS. reflexivity.
  - left. unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE. lia.
  - intros i c P Hc HP. exact (proj1 (HCtab' i c P Hc HP)). }
assert (Heqb : PRce.calls_eqb ca cb = true).
{ apply crts8_calls_eqb; [exact Hlq | exact HCl' |].
  intros i c P1' P2' Hc H1' H2'. split.
  - destruct (proj1 (Htb1 i c P1' Hc H1')) as (_ & _ & HlP & _). exact HlP.
  - destruct (proj1 (HCtab' i c P2' Hc H2')) as (_ & _ & HlP & _). exact HlP. }
assert (HEV1 : st_nev Sc + EV_REC_CALLS_EQUAL <= EV_MAX).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _). pose proof (crt_ev_args_nn R) as Hea.
  assert (Hle : crt_EVG + 1 <= EV_CHECK_ROUND_TRIP R ws) by (unfold crt_EVG, EV_CHECK_ROUND_TRIP, crt_D; lia).
  unfold EV_REC_CALLS_EQUAL. lia. }
pose proof (crt_rod _ lyc Sc Wc mT0 mdv _ HJ) as HROD1.
assert (G10 : getr rT0 10 = w64 (crt_F pos + 32)) by (rewrite Pr10; exact E34).
assert (G11 : getr rT0 11 = w64 (Z.of_nat (length ca))) by (rewrite Pr11, E33; unfold ca; rewrite (crts8_ents_len _ _ Hlq); reflexivity).
assert (G12 : getr rT0 12 = w64 (A_G_REC + OFF_CALLS)) by (rewrite Pr12, U24; reflexivity).
assert (G13 : getr rT0 13 = w64 (Z.of_nat (length cb))) by (rewrite Pr13, E32; unfold cb; rewrite (crts8_ents_len _ _ HCl'); reflexivity).
assert (HspT : spZ rT0 = sp0 + (crt_sp1 - sp0)).
{ unfold spZ at 1. rewrite (crt_reg_bv rT0 2 2%bv _ eq_refl Q2). unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (G3 : getr rT0 3 = w64 (as_gp B)) by exact (crt_reg_bv rT0 3 3%bv _ eq_refl Q3).
assert (G4 : getr rT0 4 = w64 (as_tp B)) by exact (crt_reg_bv rT0 4 4%bv _ eq_refl Q4).
assert (HraT : YK0s.ret_ok (getr rT0 1)) by (rewrite Pr1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4T : 4096 <= bv_unsigned (getr rT0 1)) by (rewrite Pr1, unsigned_lit_small by lia; lia).
(* the call of rec_calls_equal (0x88294) *)
eapply SRr_bind.
{ apply (cl_callS_na B LAWS Wc rT0 mT0 (Z_to_bv 64 (BASE + AF_rec_calls_equal)) STK sp0 crt_FP ly S W mem md [(5, pos)] lyc Sc mdv
    (crt_EVG + 1) REC_CALLS_EQUAL_STK [] EV_REC_CALLS_EQUAL (crt_sp1 - sp0) (getr rT0 1)
    (fun ly' S' W' regs' mem' md' => getr regs' 10 = w64 (if PRce.calls_eqb ca cb then 1 else 0) /\
       Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\ ly' = lyc /\ S' = Sc)).
  - exact HJ.
  - exact HspT.
  - exact P4.
  - lia.
  - unfold REC_CALLS_EQUAL_STK, ESTACK. lia.
  - rewrite crt_STK. unfold REC_CALLS_EQUAL_STK, ESTACK. lia.
  - exact G3.
  - exact G4.
  - reflexivity.
  - exact HraT.
  - exact Hra4T.
  - intros HPRE1.
    exact (HRCE fx lyc Sc Wc rT0 mT0 mdv (crt_F pos + 32) (A_G_REC + OFF_CALLS) ca cb HPRE1 HROD1 G10 G11 G12 G13 HCA HCB HEV1).
  - intros x Hx. exfalso. exact (inFP_nil x Hx). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & Ha0 & _ & -> & ->).
rewrite Heqb in Ha0.
rewrite Pr1.
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 7604)) mem2 (seg_rom SEGS)) md2) with (cfgP 7604 regs2 mem2 md2).
replace (sp0 + (crt_sp1 - sp0)) with crt_sp1 in HJc2 by lia.
pose proof (crts8_kp_journal pos lyc Sc Wc W2 mT0 mdv mem2 md2 _ _ HJc2 Hfin Efa) as KP1.
destruct (crts8_keep pos lyc Sc Wc W2 mc mem2 qs res X R2 O2 (crts8_kp_trans _ _ _ _ _ _ KP0 KP1)
  HFR HTBL HREP2 HVQ2 HRES Hres HSL) as (HFR2 & HTBL2 & HREP3 & HVQ3 & HRES3 & HSL3).
apply (HSTI lyc Sc W2 mem2 md2 regs2 pos qs res X R2 O2).
- unfold crt_J. unfold EV_REC_CALLS_EQUAL in HJ2. rewrite Z.add_0_r in HJ2. exact HJ2.
- exact HFR2.
- exact HTBL2.
- exact HPm.
- exact HREP3.
- exact HR2.
- exact HVQ3.
- exact HRPL.
- exact HNO0.
- exact HRES3.
- exact H4096.
- exact HBB.
- exact HMLE.
- exact HSL3.
- unfold crt_regs, crt_RI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  all: first [ exact (crt_reg_lit regs2 10 10%bv _ eq_refl Ha0)
             | rewrite (crt_preg rT0 regs2 _ HP2) by crt_cs; assumption ].
Qed.
(* ---------- s9: from 0x88298 to the call of the strcmp wrapper ---------- *)
(* atom 32 the shadow base, atom 33 g_rec's reply pointer; a0 = 1 and s4 = the shadow of g_rec + 928 are pinned *)
Definition crts9_ss0 : sstate := mkSS 7604 sr_atoms
  [YP09.mkRegion (Some 24%nat) 928 936 0 0 [YP09.mkChunk 928 (CVal 8 (SOff 33 0))]] None
  (mkFacts [(2%nat, mkAF (2^46) (2^47) 5); (9%nat, mkAF (2^46) (2^47) 5); (32%nat, mkAF SB SB 0);
            (24%nat, mkAF A_G_REC A_G_REC 3); (33%nat, mkAF 4096 (2^47) 0)] [] []).
Lemma crt_s9 : ST_I 7632 0 -> ST_I 7604 1.
Proof.
intros HSTI lyc Sc Wc mc dc rX pos qs res X R2 O2 HJ HFR HTBL HPm HREP2 HR2 HVQ2 HRPL HNO0 HRES H4096 HBB HMLE HSL HRG.
pose proof crt_sp0 as (SP1 & SP2 & SP3 & SP4 & SP5). pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4).
pose proof alloc_ceiling_value as (ACv & _). pose proof alloc_ceiling_lt as HAC.
pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBlo.
pose proof HR2 as (EC2 & ER2 & _).
destruct (crts8_frame pos lyc Sc Wc mc dc _ HJ) as (Hfin & Efa & HF4 & HFc & HF8 & HF8').
assert (Hfb : fs_frame_bytes 5 = 2048) by reflexivity.
assert (Hres : In (res, Z.of_nat (length X) + 1) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPm|].
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. left; reflexivity. }
pose proof (proj1 HJ) as HAR0.
assert (HBL : forall p n, In (p, n) (ablocks B lyc Sc) -> 0 <= p /\ p + n <= alloc_ceiling).
{ intros p n Hin. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 Hin) as (_ & Hp4 & Hpc & _ & _ & _ & Hm).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hq]. lia. }
(* the reply: g_rec's reply pointer, a live block holding X and its terminator *)
pose proof HREP2 as (Q & (_ & _ & _ & _ & _ & HRP & _) & _).
rewrite ER2, HRPL in HRP.
destruct (l_reply Q) as [[rp rn]|]; [|destruct HRP].
cbn [areply_at fst snd] in HRP. destruct HRP as (VRP & _ & Hrp0 & _ & Hrpin & Hrpsz & HRPb & _).
rewrite length_app in Hrpsz. cbn [length] in Hrpsz.
destruct (al_blocks _ _ LAWS _ _ _ _ _ rp rn HAR0 Hrpin) as (_ & Hrp4 & Hrpc & _ & _ & _ & Hrnm).
pose proof (req_size_pos rn ltac:(lia)) as [_ Hrq].
destruct (al_blocks _ _ LAWS _ _ _ _ _ res _ HAR0 Hres) as (_ & Hrs4 & Hrsc & _ & _ & _ & Hrsm).
pose proof (req_size_pos (Z.of_nat (length X) + 1) ltac:(lia)) as [_ Hrsq].
(* the entry state of the segment *)
remember (Eimg (Ereg rX [w64 SB; w64 rp])) as E eqn:HE.
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr rX r)
  by (intros nn r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 SB) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 rp) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
pose proof (crt_reg rX _ 2 crt_sp1 HRG ltac:(crts8_in)) as R2r.
pose proof (crt_reg rX _ 9 crt_sp1 HRG ltac:(crts8_in)) as R9r.
pose proof (crt_reg rX _ 10 1 HRG ltac:(crts8_in)) as R10r.
pose proof (crt_reg rX _ 20 (crt_shx (A_G_REC + 928)) HRG ltac:(crts8_in)) as R20r.
pose proof (crt_reg rX _ 21 res HRG ltac:(crts8_in)) as R21r.
pose proof (crt_reg rX _ 24 A_G_REC HRG ltac:(crts8_in)) as R24r.
assert (E24 : ew E 24 = Z_to_bv 64 A_G_REC) by (rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl); exact R24r).
assert (U2 : bv_unsigned (ew E 2) = crt_sp1)
  by (rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), R2r; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = crt_sp1)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9r; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = A_G_REC) by (rewrite E24; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (U32 : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (U33 : bv_unsigned (ew E 33) = rp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HS0 : st_ok_pi SEGS VAL E crts9_ss0 (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + 7604)) mc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold crts9_ss0. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U24. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ A_G_REC 928 8 (SOff 33 0) rp);
      [rewrite crt_den_atom0, E33; reflexivity | rewrite crts8_n8; lia | change (Z.of_N 8) with 8; lia |].
    apply crt_val_of_aval. exact VRP.
  - split; exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U32, U24, U33. rewrite ?Z.pow_0_r, ?Z.mod_1_r. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
    unfold SB, A_G_REC. repeat split; try reflexivity; try lia. }
pose proof (crts8_pin E crts9_ss0 _ (10%bv : bv 5) (SLit 1) HS0 (crt_reg_bv rX 10 10%bv _ eq_refl R10r) eq_refl) as HS1.
assert (G20 : getr rX (20%bv : bv 5) = sv_denot E (crt_shy (SOff 24 928))).
{ rewrite (crt_reg_bv rX 20 20%bv _ eq_refl R20r). unfold crt_shy. cbn [sv_denot]. rewrite E24, E32.
  apply bv_eq. vm_compute. reflexivity. }
pose proof (crts8_pin E _ _ (20%bv : bv 5) (crt_shy (SOff 24 928)) HS1 G20 eq_refl) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts crts9_ss0] in HS. clear HS0 HS1.
assert (U32u : U E (SOff 32 0) = SB)
  by (rewrite (U_atom_off E 32 SB 0 E32) by (unfold SB; lia); lia).
assert (U24u : U E (SOff 24 928) = A_G_REC + 928)
  by (rewrite (U_atom_off E 24 A_G_REC 928 E24) by (unfold A_G_REC; lia); reflexivity).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) mc)) by (unfold sh_ok; apply Forall_nil).
clear HE.
unfold cfgP. unfold crt_J in HJ.
(* 0x88298 .. 0x882b0: a0 = 1, the check of g_rec + 928, the reply pointer (a block, not NULL), a1 = the copy *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ rewrite U32u, U24u.
  exact (cmd_addressable_chk lyc Sc Wc mc dc (A_G_REC + 928) 8 (proj1 HJ) ltac:(vm_compute; reflexivity)). }
{ awr_ok_tac. }
clear_md.
pose proof (crt_frame_nowin _ _ _ _ _ HFr ltac:(crt_nowin)) as K0. clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Pr1. prreg HS (10%bv : bv 5) Pr10. prreg HS (11%bv : bv 5) Pr11.
prreg HS (Z_to_bv 5 20) Pr20.
crts8_own HS EE HRG 2 2%nat crt_sp1 Q2. crts8_own HS EE HRG 9 9%nat crt_sp1 Q9.
crts8_own HS EE HRG 8 8%nat (spZ regs) Q8. crts8_own HS EE HRG 3 3%nat (as_gp B) Q3.
crts8_own HS EE HRG 4 4%nat (as_tp B) Q4. crts8_own HS EE HRG 18 18%nat (crt_F pos) Q18.
crts8_own HS EE HRG 21 21%nat res Q21. crts8_own HS EE HRG 22 22%nat (crt_F pos + 32) Q22.
crts8_own HS EE HRG 23 23%nat (crt_shx (A_G_REC + 952)) Q23. crts8_own HS EE HRG 24 24%nat A_G_REC Q24.
crts8_own HS EE HRG 25 25%nat A_G_QUITTING Q25. crts8_own HS EE HRG 26 26%nat (crt_shx (A_G_REC + 944)) Q26.
crts8_own HS EE HRG 27 27%nat crt_nC Q27.
lazymatch type of Pr20 with getr ?rr _ = _ =>
  assert (Q20 : getr rr (Z_to_bv 5 20) = w64 (crt_shx (A_G_REC + 928)))
    by (rewrite Pr20; rewrite ?E24, ?E32; apply bv_eq; vm_compute; reflexivity) end.
clear Pr20.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ => set (rT0 := rT) in *; set (mT0 := mT) in * end.
(* the facts at the call *)
pose proof (crts8_kp_all pos lyc Sc (w_H Wc) mc mT0 K0) as KP0.
pose proof (crts8_view_all (w_H Wc) mc mT0 K0) as K0a.
destruct (crts8_keep pos lyc Sc Wc Wc mc mT0 qs res X R2 O2 KP0 HFR HTBL HREP2 HVQ2 HRES Hres HSL)
  as (_ & _ & _ & _ & HRES1 & _).
pose proof (proj1 HJ) as HAR1.
assert (G10 : getr rT0 10 = w64 rp) by (rewrite Pr10; exact E33).
assert (G11 : getr rT0 11 = w64 res) by (rewrite Pr11, (EE 21%nat (Z_to_bv 5 21) eq_refl); exact R21r).
assert (HspT : spZ rT0 = sp0 + (crt_sp1 - sp0)).
{ unfold spZ at 1. rewrite (crt_reg_bv rT0 2 2%bv _ eq_refl Q2). unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (G3 : getr rT0 3 = w64 (as_gp B)) by exact (crt_reg_bv rT0 3 3%bv _ eq_refl Q3).
assert (G4 : getr rT0 4 = w64 (as_tp B)) by exact (crt_reg_bv rT0 4 4%bv _ eq_refl Q4).
assert (HraT : YK0s.ret_ok (getr rT0 1)) by (rewrite Pr1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (STRa : astr_at SEGS Wc mT0 rp X).
{ apply (astr_atR_view SEGS). split; [|exact HNO0]. intros i Hi. rewrite K0a. exact (HRPb i Hi). }
assert (STRb : astr_at SEGS Wc mT0 res X).
{ apply (astr_atR_view SEGS). split; [exact HRES1 | exact HNO0]. }
assert (RDa : aread_ok SEGS (2 * ESTACK) Wc rT0 mT0 rp (astr_len X + 1)).
{ apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) lyc Sc Wc rT0 mT0 mdv rp rn rp (astr_len X + 1) HAR1 Hrpin);
    unfold astr_len; [lia | lia | lia | rewrite HspT; unfold ESTACK; lia]. }
assert (RDb : aread_ok SEGS (2 * ESTACK) Wc rT0 mT0 res (astr_len X + 1)).
{ apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) lyc Sc Wc rT0 mT0 mdv res _ res (astr_len X + 1) HAR1 Hres);
    unfold astr_len; [lia | lia | lia | rewrite HspT; unfold ESTACK; lia]. }
assert (TLa : atail_vis SEGS Wc mT0 (rp + astr_len X))
  by (apply (cmd_heap_tail_vis lyc Sc Wc mT0 mdv rp rn); [exact HAR1 | exact Hrpin | unfold astr_len; lia]).
assert (TLb : atail_vis SEGS Wc mT0 (res + astr_len X))
  by (apply (cmd_heap_tail_vis lyc Sc Wc mT0 mdv res (Z.of_nat (length X) + 1)); [exact HAR1 | exact Hres | unfold astr_len; lia]).
pose proof (cmd_rom_view_on Wc mT0 (crt_rod _ lyc Sc Wc mT0 mdv _ HJ)) as HROM.
(* the call of the strcmp wrapper (0x882b0) on the reply and its copy, the same C string X *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False) (SIG CS___interceptor_trampoline_strcmp)
    Wc rT0 mT0 STK sp0 crt_FP ly S W mem md [(5, pos)] lyc Sc mdv (crt_EVG + 1) (crt_sp1 - sp0) (getr rT0 1) _ HJ HspT P4
    ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(rewrite crt_STK; unfold ESTACK; lia) eq_refl (fun a0 (H : False) => False_ind _ H)).
  apply (ASTRCMP fx lyc Sc Wc rT0 mT0 mdv rp res X X).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) STK sp0 crt_FP ly S W mem md [(5, pos)] lyc Sc Wc mT0 mdv (crt_EVG + 1) rT0
      (crt_sp1 - sp0) HJ HspT P4 ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(rewrite crt_STK; unfold ESTACK; lia) HraT G3 G4).
  - exact G10.
  - exact G11.
  - lia.
  - lia.
  - exact STRa.
  - exact STRb.
  - exact RDa.
  - exact RDb.
  - exact TLa.
  - exact TLb.
  - exact HROM. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
pose proof (proj2 HQ2 eq_refl) as Ha0.
rewrite Pr1.
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 7632)) mem2 (seg_rom SEGS)) md2) with (cfgP 7632 regs2 mem2 md2).
assert (KK : forall a, 0 <= a < 2 ^ 64 -> ~ (crt_sp1 - 2 * ESTACK <= a < crt_sp1) ->
  aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) mT0 a)
  by (intros a Ha Hn; apply HK2; [exact Ha | lia | tauto]).
pose proof (crts8_kp_win pos lyc Sc (w_H Wc) mT0 mem2 (crt_sp1 - 2 * ESTACK) KK ltac:(unfold ESTACK; lia) HBL
  ltac:(lia) ltac:(lia)) as KP1.
destruct (crts8_keep pos lyc Sc Wc Wc mc mem2 qs res X R2 O2 (crts8_kp_trans _ _ _ _ _ _ KP0 KP1)
  HFR HTBL HREP2 HVQ2 HRES Hres HSL) as (HFR2 & HTBL2 & HREP3 & HVQ3 & HRES3 & HSL3).
apply (HSTI lyc Sc Wc mem2 md2 regs2 pos qs res X R2 O2).
- exact HJ2.
- exact HFR2.
- exact HTBL2.
- exact HPm.
- exact HREP3.
- exact HR2.
- exact HVQ3.
- exact HRPL.
- exact HNO0.
- exact HRES3.
- exact H4096.
- exact HBB.
- exact HMLE.
- exact HSL3.
- unfold crt_regs, crt_RI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  all: first [ exact (crt_reg_lit regs2 10 10%bv _ eq_refl Ha0)
             | rewrite (crt_preg rT0 regs2 _ HP2) by crt_cs; assumption ].
Qed.
(* ---------- s10: 0x882b4 .. the rec_calls_free call (0x88300), then ST_K at its return (0x88304) ---------- *)
Definition crts10_sregs : list sv := Eval vm_compute in
  sr_set (sr_set (sr_set sr_atoms 26 (crt_shy (SOff 24 944))) 23 (crt_shy (SOff 24 952))) 10 (SLit 0).
(* the four slots the code reads (s1 + 64 .. s1 + 96), g_quitting, g_rec's state and host *)
Definition crts10_stk : YP09.region := YP09.mkRegion (Some 9%nat) 64 96 0 0
  [YP09.mkChunk 88 (CVal 8 (crt_shy (SOff 25 0))); YP09.mkChunk 80 (CVal 8 (SExt true 32 (SOff 33 0)));
   YP09.mkChunk 72 (CVal 8 (SOff 34 0)); YP09.mkChunk 64 (CVal 8 (SOff 35 0))].
Definition crts10_gq : YP09.region := YP09.mkRegion (Some 25%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition crts10_gr : YP09.region := YP09.mkRegion (Some 24%nat) 944 960 0 0
  [YP09.mkChunk 944 (CVal 8 (SOff 34 0)); YP09.mkChunk 952 (CVal 8 (SOff 35 0))].
Definition crts10_ss : sstate := mkSS 7632 crts10_sregs [crts10_stk; crts10_gq; crts10_gr] None
  (mkFacts [(2%nat, mkAF (2^46) (2^47) 5); (9%nat, mkAF (2^46) (2^47) 5); (32%nat, mkAF SB SB 0);
            (24%nat, mkAF A_G_REC A_G_REC 3); (25%nat, mkAF A_G_QUITTING A_G_QUITTING 3);
            (33%nat, mkAF 0 (2^32 - 1) 0)] [] []).
(* rec_calls_free's footprint: a nargs field of the table, or a byte of a freed block *)
Lemma crts10_fp_cases : forall c (ps : list (list (Z * Z))) a, inFP (rcf_fp c ps) a ->
  (exists i, (i < length ps)%nat /\
     c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS <= a < c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS + 4) \/
  (exists p n, In (p, n) (concat ps) /\ p <= a < p + req_size n).
Proof.
intros c ps a (r & Hr & Ha). unfold rcf_fp in Hr. apply in_app_iff in Hr as [Hr | Hr].
- apply in_map_iff in Hr as (i & <- & Hi). apply in_seq in Hi. left. exists i. cbn [fst snd] in Ha. split; [lia | exact Ha].
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). right. exists p, n. cbn [fst snd] in Ha.
  split; [exact Hin | exact Ha].
Qed.
(* the argument slots of a table whose entries carry the recorded calls' arguments *)
Lemma crts10_concat_len : forall (cs : list rcall) (ps : list (list (Z * Z))), length ps = length cs ->
  (forall i c P, nth_error cs i = Some c -> nth_error ps i = Some P -> length P = length (snd c)) ->
  Z.of_nat (length (concat ps)) = fold_right (fun c acc => Z.of_nat (length (snd c)) + acc) 0 cs.
Proof.
induction cs as [|c cs IH]; intros ps Hl Hp; destruct ps as [|P ps]; cbn [length] in Hl; try discriminate.
- reflexivity.
- cbn [concat fold_right]. rewrite length_app, Nat2Z.inj_add, (Hp 0%nat c P eq_refl eq_refl).
  rewrite (IH ps ltac:(lia) (fun i c' P' H1 H2 => Hp (Datatypes.S i) c' P' H1 H2)). reflexivity.
Qed.
Lemma crts10_apart : forall a n b m, 0 <= n -> 0 < m -> (forall x, a <= x < a + Z.max n 1 -> ~ (b <= x < b + m)) ->
  iv_apart a n b m.
Proof.
intros a n b m Hn Hm H. unfold iv_apart.
destruct (Z_le_gt_dec (a + n) b) as [H1 | H1]; [left; exact H1|].
destruct (Z_le_gt_dec (b + m) a) as [H2 | H2]; [right; exact H2|].
exfalso. apply (H (Z.max a b)); lia.
Qed.

Lemma crt_s10 : ST_K -> ST_I 7632 0.
Proof.
intros HSTK lyc Sc Wc mc dc rX pos qs res X RR2 OO2 HJ HFR HTBL HPm HREP2 HOK2 HVQ2 HRPL HX0 HRES HRES4 HBB HMLE HSL HRX.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof crt_sp0 as (SP1 & SP2 & SP3 & SP4 & SP5). pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_base_lo (L := cmd_listing)) as HBLO. pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & Hnev & Hk0 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc HAR Hly) as (_ & Efa & _).
assert (Hfin : In (5, pos) (frames Sc)) by (rewrite Hfrs; cbn [app In]; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 5 pos HARc Hfin) as (Hf32 & Hfapp & _ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 5 pos HARc Hfin) as (Hf4096 & Hfceil & _).
rewrite Efa in Hf32, Hfapp, Hf4096, Hfceil. fold (crt_F pos) in Hf32, Hfapp, Hf4096, Hfceil.
change (fs_frame_bytes 5) with 2048 in Hfapp, Hfceil.
destruct (proj1 (Z.mod_divide (crt_F pos) 32 ltac:(lia)) Hf32) as [kF HkF].
assert (HF8 : crt_F pos / 8 = kF * 4).
{ rewrite HkF. replace (kF * 32) with (kF * 4 * 8) by lia. apply Z.div_mul. lia. }
pose proof HOK2 as (EC2 & ERp2 & ERf2 & ECd2 & ESp2 & ESt2 & EHo2).
pose proof HFR as (HFR1 & HFR2 & HFR3).
destruct HTBL as (Hlenq & HND & HCALL & HAPq).
(* the registers and slots of the point *)
pose proof (crt_rg _ _ 2 crt_sp1 2%bv HRX ltac:(unfold crt_RI; crt_in) eq_refl) as R2.
pose proof (crt_rg _ _ 9 crt_sp1 9%bv HRX ltac:(unfold crt_RI; crt_in) eq_refl) as R9.
pose proof (crt_rg _ _ 8 sp0 8%bv HRX ltac:(unfold crt_RI; crt_in) eq_refl) as R8.
pose proof (crt_rg _ _ 3 (as_gp B) 3%bv HRX ltac:(unfold crt_RI; crt_in) eq_refl) as R3.
pose proof (crt_rg _ _ 4 (as_tp B) 4%bv HRX ltac:(unfold crt_RI; crt_in) eq_refl) as R4.
pose proof (crt_rg _ _ 10 0 10%bv HRX ltac:(unfold crt_RI; crt_in) eq_refl) as R10.
pose proof (crt_rg _ _ 18 (crt_F pos) 18%bv HRX ltac:(unfold crt_RI; crt_in) eq_refl) as R18.
pose proof (crt_rg _ _ 21 res 21%bv HRX ltac:(unfold crt_RI; crt_in) eq_refl) as R21.
pose proof (crt_rg _ _ 22 (crt_F pos + 32) 22%bv HRX ltac:(unfold crt_RI; crt_in) eq_refl) as R22.
pose proof (crt_rg _ _ 23 (crt_shx (A_G_REC + 952)) 23%bv HRX ltac:(unfold crt_RI; crt_in) eq_refl) as R23.
pose proof (crt_rg _ _ 24 A_G_REC 24%bv HRX ltac:(unfold crt_RI; crt_in) eq_refl) as R24.
pose proof (crt_rg _ _ 25 A_G_QUITTING 25%bv HRX ltac:(unfold crt_RI; crt_in) eq_refl) as R25.
pose proof (crt_rg _ _ 26 (crt_shx (A_G_REC + 944)) 26%bv HRX ltac:(unfold crt_RI; crt_in) eq_refl) as R26.
pose proof (crt_rg _ _ 27 crt_nC 27%bv HRX ltac:(unfold crt_RI; crt_in) eq_refl) as R27.
assert (L88 := crt_slot _ _ _ 88 (crt_shx A_G_QUITTING) HSL ltac:(unfold crt_SLE; crt_in)).
assert (L80 := crt_slot _ _ _ 80 (crt_sx q) HSL ltac:(unfold crt_SLE; crt_in)).
assert (L72 := crt_slot _ _ _ 72 (r_state R) HSL ltac:(unfold crt_SLE; crt_in)).
assert (L64 := crt_slot _ _ _ 64 (r_host R) HSL ltac:(unfold crt_SLE; crt_in)).
assert (L56 := crt_slot _ _ _ 56 (crt_F pos) HSL ltac:(unfold crt_SLE; crt_in)).
assert (L48 := crt_slot _ _ _ 48 (crt_SH pos + 4) HSL ltac:(unfold crt_SLE; crt_in)).
(* g_rec's state and host, the recorder's (= R's) *)
pose proof HREP2 as (QQ & (_ & _ & _ & _ & _ & _ & (XR1 & XR2 & XR3 & XST & XHO & _ & _ & _ & XSTr & XHOr) & _) & _).
rewrite ESt2 in XST, XSTr. rewrite EHo2 in XHO, XHOr. unfold OFF_STATE in XST. unfold OFF_HOST in XHO.
(* the copies: their blocks live, each at least one byte, their count the recorder's argument count *)
assert (HQIN : forall pn, In pn (concat qs) -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym HPm)).
  apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hpn. }
assert (Hpos : forall pn, In pn (concat qs) -> 1 <= snd pn).
{ intros pn Hpn. apply in_concat in Hpn as (P & HP & Hpn).
  apply In_nth_error in HP as (i & Hi). apply In_nth_error in Hpn as (a & Ha).
  assert (Hil : (i < length qs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
  destruct (HCALL i c P Hc Hi) as ((_ & _ & HlP & _ & _ & _ & Hargs) & _).
  assert (Hal : (a < length P)%nat) by (apply nth_error_Some; rewrite Ha; discriminate).
  destruct (nth_error (snd c) a) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
  destruct (Hargs a s pn Hs Ha) as (_ & _ & _ & Hn & _). lia. }
assert (HEVA : EV_REC_CALLS_FREE qs = ev_args R).
{ unfold EV_REC_CALLS_FREE, ev_args. apply crts10_concat_len; [exact Hlenq|].
  intros i c P Hc HP. exact (proj1 (proj2 (proj2 (proj1 (HCALL i c P Hc HP))))). }
assert (HXMA : XM_REC_CALLS_FREE MT qs = ev_args R * mo_free MT)
  by (unfold XM_REC_CALLS_FREE; unfold EV_REC_CALLS_FREE in HEVA; rewrite HEVA; reflexivity).
assert (HEV0 : 0 <= ev_args R) by (rewrite <- HEVA; unfold EV_REC_CALLS_FREE; lia).
pose proof (mo_free_nonneg MT MTL) as HMF.
(* the footprint of the call: the table in our class-5 frame, the copies' blocks *)
assert (HFPC : forall a, inFP (rcf_fp (crt_F pos + 32) qs) a ->
  (crt_F pos + 32 <= a < crt_F pos + 32 + CALL_SIZE * Z.of_nat (length qs)) \/
  (exists p n, In (p, n) (concat qs) /\ In (p, n) (ablocks B lyc Sc) /\ p <= a < p + req_size n)).
{ intros a Hf. destruct (crts10_fp_cases _ _ a Hf) as [(i & Hi & Ha) | (p & n & Hpq & Hr)].
  - left. unfold CALL_SIZE, CALL_OFF_NARGS in *. lia.
  - right. exists p, n. split; [exact Hpq|]. split; [exact (HQIN _ Hpq) | exact Hr]. }
assert (Hfpb : forall a, inFP (rcf_fp (crt_F pos + 32) qs) a -> 4096 <= a < alloc_ceiling /\ ~ in_img SEGS a).
{ intros a Hf. destruct (HFPC a Hf) as [Ht | (p & n & _ & Hpc & Hr)].
  - split; [unfold CALL_SIZE in Ht; lia|].
    apply (frm_img SEGS B LAWS lyc Sc Wc mc dc 5 pos a HARc Hfin).
    rewrite Efa. change (fs_frame_bytes 5) with 2048. fold (crt_F pos). unfold CALL_SIZE in Ht. lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hpc) as (_ & Hp4 & Hpce & _).
    split; [lia|]. exact (blk_img SEGS B LAWS lyc Sc Wc mc dc p n a HARc Hpc Hr). }
(* the seed: atoms 32 SB, 33 q, 34 state, 35 host *)
set (E := Eimg (Ereg rX [Z_to_bv 64 SB; Z_to_bv 64 q; Z_to_bv 64 (r_state R); Z_to_bv 64 (r_host R)])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 q) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (r_state R)) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (r_host R)) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 3)).
assert (E9 : ew E 9 = Z_to_bv 64 crt_sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E24 : ew E 24 = Z_to_bv 64 A_G_REC) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = Z_to_bv 64 A_G_QUITTING) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (U9 : bv_unsigned (ew E 9) = crt_sp1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = crt_sp1)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = A_G_REC) by (rewrite E24; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (U25 : bv_unsigned (ew E 25) = A_G_QUITTING) by (rewrite E25; apply unsigned_lit_small; unfold A_G_QUITTING; lia).
assert (HS : st_ok_pi SEGS VAL E crts10_ss (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + 7632)) mc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold crts10_ss. apply pa_entry_st_ok_full.
  - change crts10_sregs with
      (sr_set (sr_set (sr_set sr_atoms 26 (crt_shy (SOff 24 944))) 23 (crt_shy (SOff 24 952))) 10 (SLit 0)).
    apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |] | reflexivity |] | reflexivity |].
    + unfold crt_shy. rewrite (denot_shx E 24 32 944 A_G_REC SB E24 E32) by (unfold A_G_REC, SB; lia).
      rewrite R26. unfold crt_shx, w64. reflexivity.
    + unfold crt_shy. rewrite (denot_shx E 24 32 952 A_G_REC SB E24 E32) by (unfold A_G_REC, SB; lia).
      rewrite R23. unfold crt_shx, w64. reflexivity.
    + rewrite R10. reflexivity.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, crts10_stk, crts10_gq, crts10_gr;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ crt_sp1 88 8 (crt_shy (SOff 25 0)) (crt_shx A_G_QUITTING));
          [ unfold crt_shy, crt_shx; rewrite (denot_shx E 25 32 0 A_G_QUITTING SB E25 E32) by (unfold A_G_QUITTING, SB; lia);
            rewrite Z.add_0_r; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); vm_compute; split; [intros Hx; discriminate Hx | reflexivity]
          | change (Z.of_N 8) with 8; lia | apply crt_val_of_aval; exact L88 ].
      * apply (chunk_ok_val SEGS E _ crt_sp1 80 8 (SExt true 32 (SOff 33 0)) (crt_sx q));
          [ rewrite denot_lit_U, U_SExt, (U_atom E 33 q E33 ltac:(lia)); change (2 ^ Z.of_N 32) with (2 ^ 32);
            rewrite (Z.mod_small q (2 ^ 32)) by lia; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold crt_sx; apply Z.mod_pos_bound; lia
          | change (Z.of_N 8) with 8; lia | apply crt_val_of_aval; exact L80 ].
      * apply (chunk_ok_val SEGS E _ crt_sp1 72 8 (SOff 34 0) (r_state R));
          [ cbn [sv_denot]; rewrite E34, Z.add_0_r, unsigned_lit_small by lia; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia
          | apply crt_val_of_aval; exact L72 ].
      * apply (chunk_ok_val SEGS E _ crt_sp1 64 8 (SOff 35 0) (r_host R));
          [ cbn [sv_denot]; rewrite E35, Z.add_0_r, unsigned_lit_small by lia; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia
          | apply crt_val_of_aval; exact L64 ].
    + rewrite U25. split; [unfold A_G_QUITTING; lia|]. split; [unfold A_G_QUITTING; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ A_G_QUITTING 0 4 (SOff 33 0) q);
        [ cbn [sv_denot]; rewrite E33, Z.add_0_r, unsigned_lit_small by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | change (Z.of_N 4) with 4; lia
        | rewrite Z.add_0_r; apply crt_val_of_aval; exact HVQ2 ].
    + rewrite U24. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ A_G_REC 944 8 (SOff 34 0) (r_state R));
          [ cbn [sv_denot]; rewrite E34, Z.add_0_r, unsigned_lit_small by lia; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia
          | apply crt_val_of_aval; exact XST ].
      * apply (chunk_ok_val SEGS E _ A_G_REC 952 8 (SOff 35 0) (r_host R));
          [ cbn [sv_denot]; rewrite E35, Z.add_0_r, unsigned_lit_small by lia; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia
          | apply crt_val_of_aval; exact XHO ].
  - apply pairwise_disjoint_of_extents. unfold extent_of_region, crts10_stk, crts10_gq, crts10_gr.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25, U24.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_G_REC, A_G_QUITTING. repeat split; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U24, U25, E32, E33. rewrite !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite Z.pow_0_r, !Z.mod_1_r.
    unfold SB, A_G_REC, A_G_QUITTING. repeat split; try lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) mc)) by (unfold sh_ok; apply Forall_nil).
unfold cfgP.
(* 0x882b4 .. 0x88300: the bnez on strcmp, the three checks and compares, the call *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem mkst]. rewrite <- (aview_rd_of SEGS), (U_atom E 32 SB E32 ltac:(unfold SB; lia)).
  rewrite U_SOff, E24, unsigned_lit_small, zcanon_id by (unfold A_G_REC, M64; lia). rewrite SB_SHADOW_OFF.
  apply (cmd_addressable_chk lyc Sc Wc mc dc _ _ HARc). vm_compute. reflexivity. }
{ cbn [ms_mem mkst]. rewrite <- (aview_rd_of SEGS), (U_atom E 32 SB E32 ltac:(unfold SB; lia)).
  rewrite U_SOff, E24, unsigned_lit_small, zcanon_id by (unfold A_G_REC, M64; lia). rewrite SB_SHADOW_OFF.
  apply (cmd_addressable_chk lyc Sc Wc mc dc _ _ HARc). vm_compute. reflexivity. }
{ cbn [ms_mem mkst]. rewrite <- (aview_rd_of SEGS), (U_atom E 32 SB E32 ltac:(unfold SB; lia)).
  rewrite (U_atom E 25 A_G_QUITTING E25 ltac:(unfold A_G_QUITTING; lia)). rewrite SB_SHADOW_OFF.
  apply (cmd_addressable_chk lyc Sc Wc mc dc _ _ HARc). vm_compute. reflexivity. }
{ unfold crts10_ss. cbn [ss_mem].
  apply awr_ok_cons_ro; [unfold crts10_stk; cbn [YP09.r_whi YP09.r_wlo]; lia|].
  apply awr_ok_cons_ro; [unfold crts10_gq; cbn [YP09.r_whi YP09.r_wlo]; lia|].
  apply awr_ok_cons_ro; [unfold crts10_gr; cbn [YP09.r_whi YP09.r_wlo]; lia|].
  apply awr_ok_nil. }
(* the run writes nothing *)
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin)) as K0.
clear HF HFr HG. clear_md.
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
prreg HS (18%bv : bv 5) T18. prreg HS (21%bv : bv 5) T21.
rewrite (SIGP CS_rec_calls_free ltac:(vm_compute; tauto)).
replace (VAL A_TEXT + cmd_af CS_rec_calls_free) with (BASE + AF_rec_calls_free)
  by (unfold cmd_af, AF_rec_calls_free; vm_compute; reflexivity).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ => set (rT0 := rT) in *; set (mT0 := mT) in *; set (dT0 := dT) in * end.
clear HS SHOK.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc mT0 a = rdW Wc mc a)
  by (intros a Ha; apply K0; [exact Ha | exact (fun H => H)]).
clear K0.
(* the registers at the call *)
assert (HspT : spZ rT0 = crt_sp1) by (unfold spZ at 1; rewrite T2; exact U2).
assert (G3 : getr rT0 3 = w64 (as_gp B)) by (rewrite T3, (EE 3%nat 3%bv eq_refl); exact R3).
assert (G4 : getr rT0 4 = w64 (as_tp B)) by (rewrite T4, (EE 4%nat 4%bv eq_refl); exact R4).
assert (G10 : getr rT0 10 = w64 (crt_F pos + 32)) by (rewrite T10, (EE 22%nat 22%bv eq_refl); exact R22).
assert (G11 : getr rT0 11 = w64 (Z.of_nat (length qs)))
  by (rewrite T11, (EE 27%nat 27%bv eq_refl), R27; unfold crt_nC; rewrite Hlenq; reflexivity).
assert (Hs0 : s0Z rT0 = sp0) by (unfold s0Z; rewrite T8, (EE 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (HraT : YK0s.ret_ok (getr rT0 1)) by (rewrite T1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4T : 4096 <= bv_unsigned (getr rT0 1)) by (rewrite T1, unsigned_lit_small; lia).
(* the stack and the read-only bytes at the call *)
assert (HROD1 : arodata_okP SEGS CMD_RLO CMD_RHI B (rdW Wc mT0)) by exact (crt_rod _ _ _ _ _ _ _ HJ).
(* rec_calls_free's premises: the table in our frame (afobj), its entries, the events and the meter *)
assert (HN2 : (length qs <= 2)%nat) by (rewrite Hlenq; exact HNC).
assert (HHOME : rcf_home B lyc Sc Wc mT0 (crt_F pos + 32) (CALL_SIZE * Z.of_nat (length qs))).
{ right; right. split; [|split].
  - exists 5, pos. split; [exact Hfin|]. rewrite Efa. fold (crt_F pos). change (fs_frame_bytes 5) with 2048.
    split; [lia|]. split; [rewrite HkF; replace (kF * 32) with (kF * 4 * 8) by lia; apply Z_mod_mult|].
    unfold CALL_SIZE. lia.
  - rewrite HkF. replace (kF * 32 + 32) with ((kF * 4 + 4) * 8) by lia. apply Z_mod_mult.
  - apply zero_shadow_range.
    + rewrite HkF. replace (kF * 32 + 32) with ((kF * 4 + 4) * 8) by lia. apply Z_mod_mult.
    + unfold CALL_SIZE. replace (56 * Z.of_nat (length qs)) with (Z.of_nat (length qs) * 7 * 8) by lia. apply Z_mod_mult.
    + intros i Hi. unfold CALL_SIZE in Hi.
      replace (56 * Z.of_nat (length qs)) with (Z.of_nat (length qs) * 7 * 8) in Hi by lia.
      rewrite Z.div_mul in Hi by lia. unfold shadow_of_addr.
      replace (SHADOW_OFF + (crt_F pos + 32) / 8 + i) with (crt_SH pos + (4 + i)).
      * rewrite KM; [apply HFR3; lia|]. unfold crt_SH. rewrite HF8. unfold SHADOW_OFF. lia.
      * unfold crt_SH. rewrite HF8, HkF. replace (kF * 32 + 32) with ((kF * 4 + 4) * 8) by lia.
        rewrite Z.div_mul by lia. lia. }
assert (HSLOTS : forall i P, nth_error qs i = Some P ->
  (length P <= 6)%nat /\
  aval_mem (rdW Wc mT0) (crt_F pos + 32 + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 (Z.of_nat (length P)) /\
  forall a pn, nth_error P a = Some pn ->
    aval_mem (rdW Wc mT0) (crt_F pos + 32 + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\
    In pn (ablocks B lyc Sc)).
{ intros i P HP. assert (Hil : (i < length qs)%nat) by (apply nth_error_Some; rewrite HP; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
  destruct (HCALL i c P Hc HP) as ((_ & H6 & HlP & _ & HNA & _ & HARG) & _).
  split; [lia|]. split.
  - rewrite HlP. apply (crt_aval_kept (rdW Wc mc)); [|exact HNA].
    intros kk Hkk. apply KM. unfold CALL_SIZE, CALL_OFF_NARGS. lia.
  - intros a pn Hpn. assert (Hal : (a < length P)%nat) by (apply nth_error_Some; rewrite Hpn; discriminate).
    destruct (nth_error (snd c) a) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
    destruct (HARG a s pn Hs Hpn) as (HV & _ & Hin & _). split; [|exact Hin].
    apply (crt_aval_kept (rdW Wc mc)); [|exact HV].
    intros kk Hkk. apply KM. unfold CALL_SIZE, CALL_OFF_ARGS. lia. }
assert (HEVc : st_nev Sc + EV_REC_CALLS_FREE qs <= EV_MAX).
{ rewrite HEVA. unfold EV_CHECK_ROUND_TRIP in HEV. unfold crt_EVG, crt_D in Hnev. lia. }
assert (HMOKc : mo_ok MT Sc (XM_REC_CALLS_FREE MT qs)).
{ apply (mok_station MT S Sc (XM_CHECK_ROUND_TRIP MT R ws) (crt_XMG + mo_free MT) _ MTL MOK HMLE).
  - rewrite HXMA. apply Z.mul_nonneg_nonneg; [exact HEV0 | exact HMF].
  - rewrite HXMA. unfold XM_CHECK_ROUND_TRIP, crt_XMG, crt_D. lia. }
(* the table first[] at F + 32 is 8-aligned (the class-5 frame is 32-aligned) *)
assert (HC8 : (crt_F pos + 32) mod 8 = 0) by (rewrite Z.add_mod, (proj1 (crts3_F8 _ Hf32)) by lia; reflexivity).
(* the frame chain at the call: the prologue's frame record on afn_pre's chain (s0 = sp0) *)
assert (FRT : crt_frame (rdW Wc mT0)) by (apply (crt_frame_keep (rdW Wc mc)); [intros a Ha; apply KM; lia | exact HFR1]).
destruct (crt_chain pos lyc Sc Wc mT0 dT0 _ HJ FRT) as [ch1 Hch1].
(* 0x88300: rec_calls_free(F + 32, n) *)
eapply SRr_bind.
{ apply (cl_callS_wide B LAWS Wc rT0 mT0 (Z_to_bv 64 (BASE + AF_rec_calls_free)) STK sp0 crt_FP ly S W mem md [(5, pos)]
    lyc Sc dT0 (crt_EVG + 1) REC_CALLS_FREE_STK (rcf_fp (crt_F pos + 32) qs) (EV_REC_CALLS_FREE qs) (crt_sp1 - sp0)
    (getr rT0 1) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
      Permutation (ablocks B lyc Sc) (ablocks B ly2 S2 ++ concat qs) /\
      (forall R' O', rec_repA B lyc Sc (rdW Wc mT0) R' O' ->
        iv_apart (crt_F pos + 32) (CALL_SIZE * Z.of_nat (length qs)) A_G_REC REC_SIZE ->
        iv_apart (crt_F pos + 32) (CALL_SIZE * Z.of_nat (length qs)) A_REC_SPILL SC_SIZE ->
        (forall pn, In pn (concat qs) -> ~ In pn O') -> rec_repA B ly2 S2 (rdW W2 mem2) R' O') /\
      blocks_bytes S2 <= blocks_bytes Sc + LIVE_REC_CALLS_FREE /\ mo_le MT Sc S2 (XM_REC_CALLS_FREE MT qs))).
  - exact HJ.
  - rewrite HspT. lia.
  - exact P4.
  - lia.
  - unfold REC_CALLS_FREE_STK, ASTACK. lia.
  - rewrite crt_STK. unfold REC_CALLS_FREE_STK, ASTACK. lia.
  - exact G3.
  - exact G4.
  - reflexivity.
  - exact HraT.
  - exact Hra4T.
  - replace (sp0 + (crt_sp1 - sp0)) with crt_sp1 by lia. rewrite Hs0. exact Hch1.
  - intros HPRE1. eapply SRr_mono.
    { exact (HRCF fx lyc Sc Wc rT0 mT0 dT0 ch1 (crt_F pos + 32) qs HPRE1 HROD1 G10 G11
        HN2 HHOME HC8 HSLOTS HND HEVc HMOKc). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & HQP).
    exists ly2, S2, regs2, mem2, md2. split; [exact Hc2|]. split; [exact HJ2|]. split; [exact HP2|].
    destruct HQP as (Q1 & _ & _ & _ & _ & _ & Q7 & Q8 & Q9). exact (conj Q1 (conj Q7 (conj Q8 Q9))).
  - intros a Hf. destruct (HFPC a Hf) as [Ht | (p & n & Hpq & Hpc & Hr)].
    + right; right; right; left. exists 5, pos. split; [cbn [In]; left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      rewrite Efa. change (fs_frame_bytes 5) with 2048. fold (crt_F pos). unfold CALL_SIZE in Ht. lia.
    + right; right; left. exists p, n. split; [exact Hpc|]. split; [|exact Hr].
      intros Hps. pose proof (HAPq (p, n) (p, n) Hpq Hps) as Hap. pose proof (Hpos (p, n) Hpq) as Hn1.
      cbn [fst snd] in Hap, Hn1. unfold iv_apart in Hap. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Hf Ha _. exfalso. pose proof (proj1 (Hfpb a Hf)). rewrite crt_STK in Ha. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HQ1 & HQ7 & HQ8 & HQ9).
rewrite T1.
(* what rec_calls_free kept: the stack above its window, our frame outside the table, g_quitting *)
replace (sp0 + (crt_sp1 - sp0)) with crt_sp1 in HJc2 by lia.
pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
assert (KS : forall a, crt_sp1 <= a < sp0 -> rdW W2 mem2 a = rdW Wc mc a).
{ intros a Ha. transitivity (rdW Wc mT0 a).
  - apply J1; [lia | lia | intros Hf; pose proof (proj1 (Hfpb a Hf)); lia].
  - apply KM. lia. }
assert (KF : forall a, crt_F pos <= a < crt_F pos + 2048 -> ~ inFP (rcf_fp (crt_F pos + 32) qs) a ->
  rdW W2 mem2 a = rdW Wc mc a).
{ intros a Ha Hn. transitivity (rdW Wc mT0 a).
  - apply (J4 5 pos a Hfin); [|exact Hn]. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa.
    change (fs_frame_bytes 5) with 2048. fold (crt_F pos). lia.
  - apply KM. lia. }
assert (KH : forall i, 4 <= i < 116 -> rdW W2 mem2 (crt_SH pos + i) = rdW Wc mc (crt_SH pos + i)).
{ intros i Hi. transitivity (rdW Wc mT0 (crt_SH pos + i)).
  - apply (J4 5 pos _ Hfin).
    + right. unfold in_zr, crt_SH. cbn [fst snd]. unfold shadow_addr. rewrite Efa. fold (crt_F pos).
      change (fs_frame_bytes 5 / 8) with 256. rewrite HF8. lia.
    + intros Hf. destruct (HFPC _ Hf) as [Ht | (p & n & _ & Hpc & Hr)].
      * unfold crt_SH, CALL_SIZE in Ht. rewrite HF8 in Ht. unfold SHADOW_OFF in Ht.
        rewrite HkF in Ht, Hfapp, Hfceil, Hf4096. zlia.
      * destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hpc) as (_ & Hp4 & Hpce & Hpapp & _).
        unfold crt_SH in Hr. rewrite HF8 in Hr. unfold SHADOW_OFF in Hr. rewrite HkF in Hfceil. zlia.
  - apply KM. unfold crt_SH. rewrite HF8. unfold SHADOW_OFF. lia. }
assert (KFl : forall i, 0 <= i < 8 -> rdW W2 mem2 (crt_F pos + 2048 - 8 + i) = rdW Wc mc (crt_F pos + 2048 - 8 + i)).
{ intros i Hi. apply KF; [lia|]. intros Hf. destruct (HFPC _ Hf) as [Ht | (p & n & _ & Hpc & Hr)].
  - unfold CALL_SIZE in Ht. lia.
  - pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc mc dc p n 5 pos HARc Hpc Hfin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efa in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
    fold (crt_F pos) in Hd. lia. }
assert (KQ : forall k, 0 <= k < 4 -> rdW W2 mem2 (A_G_QUITTING + k) = rdW Wc mc (A_G_QUITTING + k)).
{ intros k Hk.
  assert (Hpg : inFP cmd_PG (A_G_QUITTING + k)).
  { exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; cbn [In]; right; right; left; reflexivity | cbn [fst snd]; lia]. }
  destruct (crt_pg _ Hpg) as (Ho & He).
  transitivity (rdW Wc mT0 (A_G_QUITTING + k)).
  - apply J3; [exact (cif_prog_img _ Hpg) | exact Ho | exact He |].
    apply fp_spares_closed.
    + intros H0. pose proof (proj1 (Hfpb 0 H0)). lia.
    + intros Hf. exact (proj2 (Hfpb _ Hf) (cif_prog_img _ Hpg)).
  - apply KM. unfold A_G_QUITTING. lia. }
(* the recorder after the call: the copies were none of its blocks, the table apart from g_rec and the spill *)
assert (HREPm : rec_repA B lyc Sc (rdW Wc mT0) RR2 OO2).
{ apply (rcf_rep_repA B lyc Sc lyc Sc (rdW Wc mc) (rdW Wc mT0) RR2 OO2 [] HREP2).
  - intros a Ha. apply KM. unfold rcf_inrec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in *. lia.
  - rewrite app_nil_r. apply Permutation_refl.
  - intros pn [].
  - intros p n i Hin Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hin) as (_ & Hp4 & Hpc & _ & _ & _ & Hm).
    pose proof (req_size_pos n (proj1 Hm)) as [_ Hq]. apply KM. lia. }
assert (Hap1 : iv_apart (crt_F pos + 32) (CALL_SIZE * Z.of_nat (length qs)) A_G_REC REC_SIZE).
{ apply crts10_apart; [unfold CALL_SIZE; lia | unfold REC_SIZE; lia|].
  intros x Hx Hg. apply (frm_img SEGS B LAWS lyc Sc Wc mc dc 5 pos x HARc Hfin).
  - rewrite Efa. change (fs_frame_bytes 5) with 2048. fold (crt_F pos). unfold CALL_SIZE in Hx. lia.
  - apply cif_prog_img. exists (A_G_REC, A_G_REC + 960).
    split; [unfold cmd_PG; cbn [In]; left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Hg; lia]. }
assert (Hap2 : iv_apart (crt_F pos + 32) (CALL_SIZE * Z.of_nat (length qs)) A_REC_SPILL SC_SIZE).
{ apply crts10_apart; [unfold CALL_SIZE; lia | unfold SC_SIZE; lia|].
  intros x Hx Hg. apply (frm_img SEGS B LAWS lyc Sc Wc mc dc 5 pos x HARc Hfin).
  - rewrite Efa. change (fs_frame_bytes 5) with 2048. fold (crt_F pos). unfold CALL_SIZE in Hx. lia.
  - apply cif_prog_img. exists (A_REC_SPILL, A_REC_SPILL + 56).
    split; [unfold cmd_PG; cbn [In]; right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Hg; lia]. }
pose proof (crt_nodup _ _ _ _ _ HARc) as HND2.
assert (Hnot : forall pn, In pn (concat qs) -> ~ In pn OO2).
{ intros pn Hpn Ho. apply (rcfr_nodup_disj _ OO2 (rest ++ concat qs ++ [(res, Z.of_nat (length X) + 1)]) pn
    (proj2 (NoDup_ListNoDup _) (Permutation_NoDup HPm HND2)) Ho).
  apply in_or_app; right; apply in_or_app; left; exact Hpn. }
(* ST_K at 0x88304 *)
change (SRr SEGS W2 (cfgP 7712 regs2 mem2 md2) crt_post).
apply (HSTK ly2 S2 W2 mem2 md2 regs2 pos res X RR2 OO2).
- unfold crt_J. rewrite <- HEVA. exact HJ2.
- split; [|split].
  + intros j r Hj. assert (Hj13 : (j < 13)%nat) by (rewrite <- crt_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
    apply (crt_aval_kept (rdW Wc mc)); [|exact (HFR1 j r Hj)]. intros kk Hkk. apply KS. lia.
  + change (fs_frame_bytes 5) with 2048. rewrite (YCbq.rdword_ext (rdW Wc mc) (rdW W2 mem2)); [exact HFR2|].
    intros i Hi. exact (KFl i Hi).
  + intros i Hi. rewrite KH by exact Hi. exact (HFR3 i Hi).
- apply (Permutation_app_inv_r (concat qs)).
  eapply Permutation_trans; [apply Permutation_sym; exact HQ1|].
  eapply Permutation_trans; [exact HPm|].
  rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm.
- exact (HQ7 RR2 OO2 HREPm Hap1 Hap2 Hnot).
- exact HOK2.
- apply (crt_aval_kept (rdW Wc mc)); [intros k Hk; apply KQ; lia | exact HVQ2].
- exact HRES4.
- unfold LIVE_REC_CALLS_FREE in HQ8. lia.
- replace (crt_XMG + mo_free MT + ev_args R * mo_free MT) with ((crt_XMG + mo_free MT) + XM_REC_CALLS_FREE MT qs)
    by (rewrite HXMA; lia).
  exact (mle_station MT S Sc S2 _ _ MTL HMLE HQ9).
- unfold crt_slots. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
  + apply (crt_aval_kept (rdW Wc mc)); [intros kk Hkk; apply KS; lia | exact L56].
  + apply (crt_aval_kept (rdW Wc mc)); [intros kk Hkk; apply KS; lia | exact L48].
- unfold crt_regs. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  + apply (crt_reg_lit _ _ 2%bv); [reflexivity|]. rewrite (crt_preg _ _ 2%bv HP2) by crt_cs.
    rewrite T2, (EE 2%nat 2%bv eq_refl). exact R2.
  + apply (crt_reg_lit _ _ 9%bv); [reflexivity|]. rewrite (crt_preg _ _ 9%bv HP2) by crt_cs.
    rewrite T9, (EE 9%nat 9%bv eq_refl). exact R9.
  + apply (crt_reg_lit _ _ 8%bv); [reflexivity|]. rewrite (crt_preg _ _ 8%bv HP2) by crt_cs.
    rewrite T8, (EE 8%nat 8%bv eq_refl). exact R8.
  + apply (crt_reg_lit _ _ 3%bv); [reflexivity|]. rewrite (crt_preg _ _ 3%bv HP2) by crt_cs. exact G3.
  + apply (crt_reg_lit _ _ 4%bv); [reflexivity|]. rewrite (crt_preg _ _ 4%bv HP2) by crt_cs. exact G4.
  + apply (crt_reg_lit _ _ 18%bv); [reflexivity|]. rewrite (crt_preg _ _ 18%bv HP2) by crt_cs.
    rewrite T18, (EE 18%nat 18%bv eq_refl). exact R18.
  + apply (crt_reg_lit _ _ 21%bv); [reflexivity|]. rewrite (crt_preg _ _ 21%bv HP2) by crt_cs.
    rewrite T21, (EE 21%nat 21%bv eq_refl). exact R21.
Qed.
(* ---------- after rec_calls_free (0x88304): free(reply_first); the helpers are crt/s7.v's crts7_* ---------- *)
Lemma crt_s11 : ST_L -> ST_K.
Proof.
intros HSTL lyc Sc Wc mc dc rX pos res X R2 O2 HJ HFR HPM HREP2 HR2 HQ2 H4096 HBB HMO HSL HRK.
pose proof HJ as (HAR & _).
set (L := O2 ++ rest).
assert (HPL : Permutation (ablocks B lyc Sc) (L ++ [(res, Z.of_nat (length X) + 1)])) by (unfold L; rewrite <- app_assoc; exact HPM).
pose proof (crt_nodup lyc Sc Wc mc dc HAR) as ND.
pose proof (crts7_notin _ _ _ ND HPL) as Hnx.
assert (Hin : In (res, Z.of_nat (length X) + 1) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; right; left; reflexivity).
pose proof (crt_ev_args_nn R) as HEVA. pose proof (mo_free_nonneg MT MTL) as HMF.
assert (HMA : 0 <= ev_args R * mo_free MT) by (apply Z.mul_nonneg_nonneg; lia).
apply (crts7_free 7712 21%bv lyc Sc Wc mc dc rX pos (crt_EVG + 1 + ev_args R) res (Z.of_nat (length X) + 1)
  (or_intror (conj eq_refl eq_refl)) HJ (proj1 HFR)).
- pose proof HEV as HEV'. unfold EV_CHECK_ROUND_TRIP in HEV'. unfold crt_EVG, crt_D. lia.
- exact Hin.
- refine (crt_rg rX _ _ _ _ HRK _ eq_refl). crt_in.
- refine (crt_rg rX _ _ _ _ HRK _ eq_refl). crt_in.
- refine (crt_rg rX _ _ _ _ HRK _ eq_refl). crt_in.
- refine (crt_rg rX _ _ _ _ HRK _ eq_refl). crt_in.
- refine (crt_rg rX _ _ _ _ HRK _ eq_refl). crt_in.
- apply (crts7_cov res (Z.of_nat (length X) + 1) L Hnx). intros y Hy. unfold L. apply in_or_app. right. exact Hy.
- apply (mok_station MT S Sc (XM_CHECK_ROUND_TRIP MT R ws) (crt_XMG + mo_free MT + ev_args R * mo_free MT) (mo_free MT)
    MTL MOK HMO HMF).
  unfold XM_CHECK_ROUND_TRIP, crt_XMG, crt_D. lia.
- intros ly2 S2 W2 regs2 mem2 md2 l1 l2 HJ2 HP2 Ebl Ebl2 HK MLE.
  destruct (crts7_common pos lyc Sc Wc mc dc (crt_EVG + 1 + ev_args R) ly2 S2 W2 mem2 res (Z.of_nat (length X) + 1) l1 l2 L
    HJ HK Ebl Ebl2 HPL) as (HPL2 & PF & KBL & HBB2).
  assert (HnO : ~ In (res, Z.of_nat (length X) + 1) O2) by (intros H; apply Hnx; unfold L; apply in_or_app; left; exact H).
  apply (HSTL ly2 S2 W2 mem2 md2 regs2 pos R2 O2).
  + replace (EV_CHECK_ROUND_TRIP R ws) with (crt_EVG + 1 + ev_args R + 1)
      by (unfold EV_CHECK_ROUND_TRIP, crt_EVG, crt_D; lia).
    exact HJ2.
  + exact (crts7_fr_keep pos lyc Sc Wc mc dc _ W2 mem2 res (Z.of_nat (length X) + 1) HJ Hin HK HFR).
  + exact HPL2.
  + exact (crts7_rep_keep lyc Sc Wc mc ly2 S2 W2 mem2 res (Z.of_nat (length X) + 1) R2 O2 HK PF KBL HnO HREP2).
  + exact HR2.
  + exact (crts7_q_keep lyc Sc Wc mc W2 mem2 res (Z.of_nat (length X) + 1) q HK HQ2).
  + lia.
  + replace (XM_CHECK_ROUND_TRIP MT R ws) with (crt_XMG + mo_free MT + ev_args R * mo_free MT + mo_free MT)
      by (unfold XM_CHECK_ROUND_TRIP, crt_XMG, crt_D; lia).
    exact (mo_le_trans MT MTL _ _ _ _ _ HMO MLE).
  + apply (crts7_slots_keep lyc Sc Wc mc W2 mem2 res (Z.of_nat (length X) + 1)); [exact HK | | exact HSL].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia.
  + apply (crt_regs_pres rX regs2); [exact HP2 | |].
    * repeat apply Forall_cons; try apply Forall_nil; unfold acallee_saved; cbn [fst]; lia.
    * eapply crts7_regs_sub; [|exact HRK]. intros x Hx. cbn [In] in Hx |- *. tauto.
Qed.
(* ---------- s12 (0x8830c .. 0x88314): s4 = ld 56(s1) = F, s5 = ld 48(s1) = SH+4, then straight into the shared
   epilogue. Nothing is written, so every fact of ST_L travels to ST_EPI unchanged. ---------- *)
(* the recorder's picture survives a change of memory that keeps every byte *)
Lemma crts12_QF_keep : forall lyc Sc (Wc : world SEGS) mc mc' dc Rf Of,
 AR SEGS B lyc Sc Wc mc dc ->
 (forall a, 0 <= a < 2 ^ 64 -> rdW Wc mc' a = rdW Wc mc a) ->
 crt_QF lyc Sc Wc mc Rf Of -> crt_QF lyc Sc Wc mc' Rf Of.
Proof.
intros lyc Sc Wc mc mc' dc Rf Of HAR K (HRPc & E1 & E2 & E3 & E4 & E5 & E6 & E7 & HVQc & HPM & HBB & HMO).
pose proof asan_consts as (C1 & _).
split.
{ apply (rcf_rep_repA B lyc Sc lyc Sc (rdW Wc mc) (rdW Wc mc') Rf Of [] HRPc).
  - intros a Ha. apply K. unfold rcf_inrec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha. lia.
  - rewrite app_nil_r. apply Permutation_refl.
  - intros pn Hpn. destruct Hpn.
  - intros p n i Hin Hi.
    destruct (al_blocks _ _ LAWS lyc Sc Wc mc dc p n HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
    pose proof (req_size_pos n (proj1 Hm)) as [Hq1 Hq2]. apply K. lia. }
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
split; [exact E5|]. split; [exact E6|]. split; [exact E7|].
split; [apply (crt_aval_kept (rdW Wc mc)); [intros kk Hkk; apply K; unfold A_G_QUITTING; lia | exact HVQc]|].
split; [exact HPM|]. split; [exact HBB | exact HMO].
Qed.
Definition crts12_E (rX : bvmap 5 word) (pos : Z) : env :=
 Eimg (Ereg rX [w64 SB; w64 (crt_F pos); w64 (crt_SH pos + 4)]).
Lemma crts12_reg : forall rX pos n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (crts12_E rX pos) n = getr rX r.
Proof. intros rX pos n r Hn. unfold crts12_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma crts12_atoms : forall rX pos,
 ew (crts12_E rX pos) 32 = w64 SB /\ ew (crts12_E rX pos) 33 = w64 (crt_F pos) /\
 ew (crts12_E rX pos) 34 = w64 (crt_SH pos + 4).
Proof.
intros rX pos. unfold crts12_E.
split; [|split]; rewrite Eimg_low by (unfold A_TEXT; lia).
- exact (ew_Ereg_extra rX _ 0).
- exact (ew_Ereg_extra rX _ 1).
- exact (ew_Ereg_extra rX _ 2).
Qed.
Definition crts12_ss : sstate := mkSS 7720 sr_atoms
  [YP09.mkRegion (Some 9%nat) 48 64 0 0
     [YP09.mkChunk 56 (CVal 8 (SOff 33 0)); YP09.mkChunk 48 (CVal 8 (SOff 34 0))]] None
  (mkFacts [(32%nat, mkAF SB SB 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Lemma crt_s12 : ST_EPI -> ST_L.
Proof.
intros HEPI lyc Sc Wc mc dc rX pos R2 O2 HJ HFR HPM HREP2 HR2 HVQ2 HBB HMO HSL HRG.
pose proof crt_sp0 as (S1 & S2 & S3 & S4 & S5). pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (crt_JF pos lyc Sc Wc mc dc (EV_CHECK_ROUND_TRIP R ws) HJ) as (EF & _ & Hin5 & HF1 & HF2).
pose proof HJ as HJ0. unfold crt_J in HJ0. pose proof HJ0 as (HAR & _).
pose proof HFR as (HFRc & HFL & _).
assert (HSHr : 0 <= crt_SH pos /\ crt_SH pos + 256 < 2 ^ 64).
{ unfold crt_SH, SHADOW_OFF. pose proof (Z.div_pos (crt_F pos) 8 ltac:(lia)) as D1.
  assert (D2 : crt_F pos / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia). lia. }
destruct HSHr as (HSHlo & HSHhi).
pose proof (crt_rg rX _ 2 crt_sp1 2%bv HRG ltac:(cbn; tauto) eq_refl) as R2r.
pose proof (crt_rg rX _ 9 crt_sp1 9%bv HRG ltac:(cbn; tauto) eq_refl) as R9r.
pose proof (crt_rg rX _ 8 sp0 8%bv HRG ltac:(cbn; tauto) eq_refl) as R8r.
pose proof (crt_rg rX _ 3 (as_gp B) 3%bv HRG ltac:(cbn; tauto) eq_refl) as R3r.
pose proof (crt_rg rX _ 4 (as_tp B) 4%bv HRG ltac:(cbn; tauto) eq_refl) as R4r.
pose proof (crt_rg rX _ 18 (crt_F pos) 18%bv HRG ltac:(cbn; tauto) eq_refl) as R18r.
pose proof (crt_slot Wc mc _ 56 (crt_F pos) HSL ltac:(cbn; tauto)) as V56.
pose proof (crt_slot Wc mc _ 48 (crt_SH pos + 4) HSL ltac:(cbn; tauto)) as V48.
assert (HEI : img_env VAL A_LIM (crts12_E rX pos)) by (unfold crts12_E; apply Eimg_env).
destruct (crts12_atoms rX pos) as (E32 & E33 & E34).
assert (U9 : bv_unsigned (ew (crts12_E rX pos) 9) = crt_sp1)
  by (rewrite (crts12_reg rX pos 9 9%bv eq_refl), R9r; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL (crts12_E rX pos) crts12_ss
   (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + 7720)) mc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold crts12_ss. apply pa_entry_st_ok_full.
  - unfold crts12_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val SEGS _ _ crt_sp1 56 8 (SOff 33 0) (crt_F pos));
      [rewrite crt_den_atom0, E33; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      apply crt_val_of_aval. exact V56.
    + apply (chunk_ok_val SEGS _ _ crt_sp1 48 8 (SOff 34 0) (crt_SH pos + 4));
      [rewrite crt_den_atom0, E34; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      apply crt_val_of_aval. exact V48.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, E32. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. change (2 ^ 5) with 32.
    repeat split; try lia; try exact P2. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (crts12_E rX pos) (mrestrict (w_H Wc) mc))
  by (unfold sh_ok; apply Forall_nil).
unfold cfgP. unfold crt_J in HJ.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 7728.
{ awr_ok_tac. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
        destruct Hin)) as K0.
clear HF HFr HG. clear_md.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc mc a)
  by (intros a Ha; apply K0; [lia | cbv beta; tauto]).
pmkst HS.
apply (HEPI lyc Sc Wc (ms_mem ms) _ (ms_regs ms) pos (EV_CHECK_ROUND_TRIP R ws) R2 O2).
- unfold crt_J. exact HJ.
- lia.
- intros j r Hj. assert (Hj13 : (j < 13)%nat)
    by (rewrite <- crt_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
  apply (crt_aval_kept (rdW Wc mc)); [intros kk Hkk; apply KA; lia | exact (HFRc j r Hj)].
- rewrite (rdword_ext (rdW Wc mc) (rdW Wc (ms_mem ms))); [exact HFL|].
  intros kk Hkk. apply KA. replace (fs_frame_bytes 5) with 2048 by (vm_compute; reflexivity). lia.
- apply (crts12_QF_keep lyc Sc Wc mc _ _ R2 O2 HAR KA).
  split; [exact HREP2|].
  destruct HR2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
  split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|].
  split; [exact HVQ2|]. split; [exact HPM|]. split; [exact HBB | exact HMO].
- unfold crt_regs. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  + crt_rreg HS. rewrite crt_den_atom0, (crts12_reg rX pos 2 2%bv eq_refl). exact R2r.
  + crt_rreg HS. rewrite crt_den_atom0, (crts12_reg rX pos 8 8%bv eq_refl). exact R8r.
  + crt_rreg HS. rewrite crt_den_atom0, (crts12_reg rX pos 3 3%bv eq_refl). exact R3r.
  + crt_rreg HS. rewrite crt_den_atom0, (crts12_reg rX pos 4 4%bv eq_refl). exact R4r.
  + crt_rreg HS. rewrite crt_den_atom0, (crts12_reg rX pos 18 18%bv eq_refl). exact R18r.
  + crt_rreg HS. rewrite crt_den_atom0. exact E33.
  + crt_rreg HS. rewrite crt_den_atom0. exact E34.
Qed.
(* ---------- epi (0x88314 .. 0x88388): the shared epilogue. __asan_set_shadow_f8(SH+4,112) paints the frame's
   middle, the frame-done magic goes to F, the branch on s4 is not taken (F >= 4096), __asan_stack_free_5(F,1056)
   releases the class-5 frame, sp goes back to s0 - 256, the 13 saved registers are reloaded and ret returns.
   The three runs write only F+0..8; the two runtime entries write only the frame's shadow, its flag word and
   their own stack window, so every byte the post speaks of -- the prologue's frame, the recorder's statics, the
   live blocks -- is kept, and crt_QF travels from ST_EPI to crt_Q. ---------- *)
(* every byte the epilogue may write: the frame's shadow, the first word of the frame, the frame's flag word,
   and the stack window the two runtime entries use *)
Definition crtepi_Wr (pos a : Z) : Prop :=
 (crt_SH pos <= a < crt_SH pos + 256) \/ (crt_F pos <= a < crt_F pos + 8) \/ a = crt_FL pos \/
 (crt_sp1 - 4096 <= a < crt_sp1).
Lemma crtepi_apart : forall lyc Sc (Wc : world SEGS) m0 d0 pos,
 AR SEGS B lyc Sc Wc m0 d0 -> In (5, pos) (frames Sc) ->
 frame_addr lyc 5 pos = crt_F pos -> flag_addr lyc 5 pos = crt_FL pos ->
 (forall a, in_img SEGS a -> ~ crtepi_Wr pos a) /\
 (forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n -> ~ crtepi_Wr pos (p + i)) /\
 (forall a, sp0 - 104 <= a < sp0 -> ~ crtepi_Wr pos a) /\
 (forall a, crt_F pos + 8 <= a < crt_F pos + 2048 -> ~ crtepi_Wr pos a).
Proof.
intros lyc Sc Wc m0 d0 pos HAR Hin EF EL.
pose proof crt_sp0 as (S1 & S2 & S3 & S4 & S5). pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc m0 d0 5 pos HAR Hin) as (B1 & B2 & B3).
rewrite EF in B1, B2, B3. replace (fs_frame_bytes 5) with 2048 in B2, B3 by (vm_compute; reflexivity).
destruct (al_flag _ _ LAWS lyc Sc Wc m0 d0 5 pos HAR Hin) as (_ & Hfo & _ & Hflt). rewrite EL in Hfo, Hflt.
assert (HSH : SHADOW_OFF <= crt_SH pos /\ crt_SH pos + 256 < kHighMemBeg).
{ unfold crt_SH, SHADOW_OFF, kHighMemBeg in *.
  pose proof (Z.div_pos (crt_F pos) 8 ltac:(lia)) as D1.
  assert (D2 : crt_F pos / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia). lia. }
assert (HFimg : ~ in_img SEGS (crt_FL pos)).
{ refine (proj2 (al_client_img _ _ LAWS lyc Sc Wc m0 d0 (crt_FL pos) HAR _)).
  right. right. exists 5, pos. split; [exact Hin | rewrite EL; reflexivity]. }
unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg, kLowMemEnd in *.
split.
{ intros a Hi [Hw | [Hw | [Hw | Hw]]].
  - pose proof (pa_segs_low a Hi) as Hlw. unfold kLowMemEnd in Hlw. lia.
  - refine (frm_img SEGS B LAWS lyc Sc Wc m0 d0 5 pos a HAR Hin _ Hi).
    rewrite EF. replace (fs_frame_bytes 5) with 2048 by (vm_compute; reflexivity). lia.
  - rewrite Hw in Hi. exact (HFimg Hi).
  - pose proof (pa_segs_low a Hi) as Hlw. unfold kLowMemEnd in Hlw. lia. }
split.
{ intros p n i Hb Hi [Hw | [Hw | [Hw | Hw]]].
  - destruct (al_blocks _ _ LAWS lyc Sc Wc m0 d0 p n HAR Hb) as (_ & H4096 & Hceil & Happ & _ & _ & _).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia.
  - pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc m0 d0 p n 5 pos HAR Hb Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd.
    replace (fs_frame_bytes 5) with 2048 in Hd by (vm_compute; reflexivity). lia.
  - destruct (al_blocks _ _ LAWS lyc Sc Wc m0 d0 p n HAR Hb) as (_ & _ & _ & _ & Hpo & _ & _).
    destruct (Hpo (p + i) ltac:(lia)) as (_ & Hno). rewrite Hw in Hno. exact (Hno Hfo).
  - destruct (al_blocks _ _ LAWS lyc Sc Wc m0 d0 p n HAR Hb) as (_ & H4096 & Hceil & _ & _ & _ & _).
    unfold ASAN_CEIL in *. lia. }
split.
{ intros a Ha [Hw | [Hw | [Hw | Hw]]]; unfold ASAN_CEIL in *; lia. }
{ intros a Ha [Hw | [Hw | [Hw | Hw]]]; unfold ASAN_CEIL in *; try lia.
  - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in B3. lia.
  - destruct (al_frames _ _ LAWS lyc Sc Wc m0 d0 5 pos HAR Hin) as (_ & _ & Hfr & _).
    refine (match Hfr a _ with conj _ Hno => Hno _ end).
    + rewrite EF. replace (fs_frame_bytes 5) with 2048 by (vm_compute; reflexivity). lia.
    + rewrite Hw. exact Hfo. }
Qed.
(* the recorder's picture travels across a memory change that keeps every byte outside crtepi_Wr *)
Lemma crtepi_QF_keep : forall lyc Sc Sc' (Wc : world SEGS) mc mc' dc pos Rf Of,
 AR SEGS B lyc Sc Wc mc dc -> In (5, pos) (frames Sc) ->
 frame_addr lyc 5 pos = crt_F pos -> flag_addr lyc 5 pos = crt_FL pos ->
 ablocks B lyc Sc' = ablocks B lyc Sc -> blocks_bytes Sc' = blocks_bytes Sc ->
 (forall m, mo_le MT S Sc m -> mo_le MT S Sc' m) ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ crtepi_Wr pos a -> rdW Wc mc' a = rdW Wc mc a) ->
 crt_QF lyc Sc Wc mc Rf Of -> crt_QF lyc Sc' Wc mc' Rf Of.
Proof.
intros lyc Sc Sc' Wc mc mc' dc pos Rf Of HAR Hin EF EL Eab Ebb Emo K
  (HRPc & E1 & E2 & E3 & E4 & E5 & E6 & E7 & HVQc & HPM & HBB & HMO).
pose proof asan_consts as (C1 & _).
destruct (crtepi_apart lyc Sc Wc mc dc pos HAR Hin EF EL) as (AP1 & AP2 & _).
assert (KI : forall a, inFP cmd_PG a -> rdW Wc mc' a = rdW Wc mc a).
{ intros a Ha. pose proof (cif_prog_img a Ha) as Hi. pose proof (pa_img_range a Hi) as Hr.
  apply K; [lia | exact (AP1 a Hi)]. }
assert (KB : forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n ->
  rdW Wc mc' (p + i) = rdW Wc mc (p + i)).
{ intros p n i Hb Hi.
  destruct (al_blocks _ _ LAWS lyc Sc Wc mc dc p n HAR Hb) as (_ & H4096 & Hceil & _ & _ & _ & _).
  apply K; [lia | exact (AP2 p n i Hb Hi)]. }
split.
{ apply (rcf_rep_repA B lyc Sc lyc Sc' (rdW Wc mc) (rdW Wc mc') Rf Of [] HRPc).
  - intros a Ha. apply KI. exact (crt_inrec_pg a Ha).
  - rewrite Eab, app_nil_r. apply Permutation_refl.
  - intros pn Hpn. destruct Hpn.
  - intros p n i Hb Hi. rewrite Eab in Hb.
    destruct (al_blocks _ _ LAWS lyc Sc Wc mc dc p n HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (req_size_pos n (proj1 Hm)) as [Hq1 Hq2]. exact (KB p n i Hb ltac:(lia)). }
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
split; [exact E5|]. split; [exact E6|]. split; [exact E7|].
split.
{ apply (crt_aval_kept (rdW Wc mc)); [|exact HVQc]. intros kk Hkk. apply KI.
  exists (A_G_QUITTING, A_G_QUITTING + 4). split; [right; right; left; reflexivity | cbn [fst snd]; lia]. }
split; [rewrite Eab; exact HPM|]. split; [rewrite Ebb; exact HBB | exact (Emo _ HMO)].
Qed.
(* the live blocks of the entry state are pairwise distinct, so no block of rest is a block of O *)
Lemma crtepi_rest_fp : forall p n i, In (p, n) rest -> 0 <= i < req_size n -> ~ inFP crt_FP (p + i).
Proof.
intros p n i Hin Hi. pose proof HPRE as (HAR0 & _).
assert (Hin0 : In (p, n) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; exact Hin).
intros Hf. unfold crt_FP in Hf. apply inFP_app in Hf as [Hf | Hf].
- destruct Hf as (r0 & Hr & Hb). unfold ablocks_fp in Hr.
  apply in_map_iff in Hr as (qm & Eq & Hq). subst r0. destruct qm as (qb & mb). cbn [fst snd] in Hb.
  assert (HqS : In (qb, mb) (ablocks B ly S))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hq).
  destruct (Z.eq_dec qb p) as [Eqp | Nqp]; [destruct (Z.eq_dec mb n) as [Emn | Nmn]|].
  + subst qb mb. pose proof (Permutation_NoDup HPERM (crt_nodup ly S W mem md HAR0)) as ND.
    apply NoDup_ListNoDup in ND. exact (rcfr_nodup_disj _ _ _ (p, n) ND Hq Hin).
  + pose proof (sep_blocks SEGS B LAWS ly S W mem md qb mb p n HAR0 HqS Hin0 ltac:(congruence)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  + pose proof (sep_blocks SEGS B LAWS ly S W mem md qb mb p n HAR0 HqS Hin0 ltac:(congruence)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- exact (blk_img SEGS B LAWS ly S W mem md p n (p + i) HAR0 Hin0 ltac:(lia) (cif_prog_img _ Hf)).
Qed.
(* ---------- the seeds ---------- *)
Definition crtepi_EA (rX : bvmap 5 word) : env := Eimg (Ereg rX [w64 SB]).
Lemma crtepi_rega : forall rX n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (crtepi_EA rX) n = getr rX r.
Proof. intros rX n r Hn. unfold crtepi_EA. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma crtepi_a32 : forall rX, ew (crtepi_EA rX) 32 = w64 SB.
Proof.
intros rX. unfold crtepi_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra rX _ 0).
Qed.
Definition crtepi_ssA : sstate := mkSS 7728 sr_atoms [] None (mkFacts [(32%nat, mkAF SB SB 0)] [] []).
Definition crtepi_ssB : sstate := mkSS 7740 sr_atoms
  [YP09.mkRegion (Some 18%nat) 0 8 0 8 []] None
  (mkFacts [(32%nat, mkAF SB SB 0); (20%nat, PTR 5)] [] []).
Definition crtepi_SHB : list shent := [mkSHE 18 8 0].
Definition crtepi_extra : list word := w64 SB :: map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) crt_saved.
Definition crtepi_EC (rX : bvmap 5 word) : env := Eimg (Ereg rX crtepi_extra).
Lemma crtepi_regc : forall rX n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (crtepi_EC rX) n = getr rX r.
Proof. intros rX n r Hn. unfold crtepi_EC. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma crtepi_c32 : forall rX, ew (crtepi_EC rX) 32 = w64 SB.
Proof.
intros rX. unfold crtepi_EC. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra rX _ 0).
Qed.
Lemma crtepi_ES : forall rX j r, nth_error crt_saved j = Some r ->
 ew (crtepi_EC rX) (33 + j)%nat = getr regs (Z_to_bv 5 (Z.of_nat r)).
Proof.
intros rX j r Hj. assert (Hj13 : (j < 13)%nat)
  by (rewrite <- crt_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
unfold crtepi_EC. replace (33 + j)%nat with (32 + Datatypes.S j)%nat by lia.
rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. unfold crtepi_extra.
cbn [nth]. rewrite (nth_indep _ _ (getr regs (Z_to_bv 5 (Z.of_nat 0))))
  by (rewrite length_map, crt_saved_len; exact Hj13).
rewrite (map_nth (fun r0 => getr regs (Z_to_bv 5 (Z.of_nat r0)))).
rewrite (nth_error_nth crt_saved j 0%nat Hj). reflexivity.
Qed.
Definition crtepi_stk : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 0 0
  (map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (33 + j) 0))) (seq 0 13)).
Definition crtepi_ssC : sstate := mkSS 7768 sr_atoms [crtepi_stk] None
  (mkFacts [(32%nat, mkAF SB SB 0); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Lemma crtepi_rg_stk : forall rX (m : word -> option byte), bv_unsigned (ew (crtepi_EC rX) 8) = sp0 ->
 (forall j r, nth_error crt_saved j = Some r ->
   val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r))))) ->
 region_ok SEGS (crtepi_EC rX) m crtepi_stk.
Proof.
intros rX m H8 HV. pose proof crt_sp0 as (S1 & S2 & S3 & S4 & S5). pose proof asan_consts as (C1 & _).
unfold region_ok, crtepi_stk.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite H8.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros ck Hck. apply in_map_iff in Hck as (j & <- & Hj). apply in_seq in Hj.
destruct (nth_error crt_saved j) as [r|] eqn:Er;
  [|apply nth_error_None in Er; rewrite crt_saved_len in Er; lia].
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (Z.of_nat r)))) as HR.
change (bv_modulus 64) with (2 ^ 64) in HR.
apply (chunk_ok_val SEGS (crtepi_EC rX) m sp0 (-8 - 8 * Z.of_nat j) 8 (SOff (33 + j) 0)
  (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r)))));
  [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
- rewrite crt_den_atom0, (crtepi_ES rX j r Er), Z_to_bv_bv_unsigned. reflexivity.
- replace (sp0 + (-8 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia. exact (HV j r Er).
Qed.
Lemma crt_epi : ST_EPI.
Proof.
intros lyc Sc Wc mc dc rX pos k Rf Of HJ Hk HFRc HFL HQF HRG.
pose proof crt_sp0 as (S1 & S2 & S3 & S4 & S5). pose proof crt_sp1_bounds as (P1 & P2 & P3 & P4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
destruct (crt_JF pos lyc Sc Wc mc dc k HJ) as (EF & EL & Hin5 & HF1 & HF2).
pose proof HJ as HJ0. unfold crt_J in HJ0. pose proof HJ0 as (HAR & _).
destruct (crtepi_apart lyc Sc Wc mc dc pos HAR Hin5 EF EL) as (AP1 & AP2 & AP3 & AP4).
assert (HSH1 : SHADOW_OFF <= crt_SH pos /\ crt_SH pos + 256 < kHighMemBeg).
{ unfold crt_SH, SHADOW_OFF, kHighMemBeg in *.
  pose proof (Z.div_pos (crt_F pos) 8 ltac:(lia)) as D1.
  assert (D2 : crt_F pos / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia). lia. }
destruct HSH1 as (HSHlo & HSHhi).
assert (ESA : shadow_addr (crt_F pos) = crt_SH pos) by reflexivity.
pose proof (crt_rg rX _ 2 crt_sp1 2%bv HRG ltac:(cbn; tauto) eq_refl) as R2r.
pose proof (crt_rg rX _ 8 sp0 8%bv HRG ltac:(cbn; tauto) eq_refl) as R8r.
pose proof (crt_rg rX _ 3 (as_gp B) 3%bv HRG ltac:(cbn; tauto) eq_refl) as R3r.
pose proof (crt_rg rX _ 4 (as_tp B) 4%bv HRG ltac:(cbn; tauto) eq_refl) as R4r.
pose proof (crt_rg rX _ 18 (crt_F pos) 18%bv HRG ltac:(cbn; tauto) eq_refl) as R18r.
pose proof (crt_rg rX _ 20 (crt_F pos) 20%bv HRG ltac:(cbn; tauto) eq_refl) as R20r.
pose proof (crt_rg rX _ 21 (crt_SH pos + 4) 21%bv HRG ltac:(cbn; tauto) eq_refl) as R21r.
(* ---- run A: a1 = 112, a0 = s5, jal __asan_set_shadow_f8 ---- *)
assert (HEIA : img_env VAL A_LIM (crtepi_EA rX)) by (unfold crtepi_EA; apply Eimg_env).
pose proof (crtepi_a32 rX) as EA32.
assert (HSA : st_ok_pi SEGS VAL (crtepi_EA rX) crtepi_ssA
   (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + 7728)) mc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold crtepi_ssA. apply pa_entry_st_ok_full.
  - unfold crtepi_EA. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite EA32. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
assert (SHOKA : sh_ok SEGS (SOff 32 0) [] (crtepi_EA rX) (mrestrict (w_H Wc) mc))
  by (unfold sh_ok; apply Forall_nil).
unfold cfgP. unfold crt_J in HJ.
paj_run_tok RUN HSA HJ SHOKA Bspan.
{ awr_ok_tac. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
        destruct Hin)) as K0A.
clear HF HFr HG. clear_md.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc mc a)
  by (intros a Ha; apply K0A; [lia | cbv beta; tauto]).
assert (QA1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 7740))
  by (crt_rreg HSA; apply (codeptr_val _ 7740 HEIA)).
assert (QA2 : getr (ms_regs ms) 2 = w64 crt_sp1)
  by (crt_rreg HSA; rewrite crt_den_atom0, (crtepi_rega rX 2 2%bv eq_refl); exact R2r).
assert (QA3 : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (crt_rreg HSA; rewrite crt_den_atom0, (crtepi_rega rX 3 3%bv eq_refl); exact R3r).
assert (QA4 : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (crt_rreg HSA; rewrite crt_den_atom0, (crtepi_rega rX 4 4%bv eq_refl); exact R4r).
assert (QA8 : getr (ms_regs ms) 8 = w64 sp0)
  by (crt_rreg HSA; rewrite crt_den_atom0, (crtepi_rega rX 8 8%bv eq_refl); exact R8r).
assert (QA10 : getr (ms_regs ms) 10 = w64 (crt_SH pos + 4))
  by (crt_rreg HSA; rewrite crt_den_atom0, (crtepi_rega rX 21 21%bv eq_refl); exact R21r).
assert (QA11 : getr (ms_regs ms) 11 = w64 112)
  by (crt_rreg HSA; unfold w64; rewrite denot_lit_U, U_SLit; reflexivity).
assert (QA18 : getr (ms_regs ms) 18 = w64 (crt_F pos))
  by (crt_rreg HSA; rewrite crt_den_atom0, (crtepi_rega rX 18 18%bv eq_refl); exact R18r).
assert (QA20 : getr (ms_regs ms) 20 = w64 (crt_F pos))
  by (crt_rreg HSA; rewrite crt_den_atom0, (crtepi_rega rX 20 20%bv eq_refl); exact R20r).
pmkst HSA.
eapply SRr_bind.
{ apply (aj_set_shadow_atS SEGS B LAWS pa_segs_low (SIG CS___asan_set_shadow_f8) 248 (ASHF8 fx)
    Wc (ms_regs ms) (ms_mem ms) STK sp0 crt_FP ly S W mem md [(5, pos)] lyc Sc _ k
    (crt_sp1 - sp0) (Z_to_bv 64 (BASE + 7740)) 5 pos (crt_SH pos + 4) 112 HJ).
  - left. reflexivity.
  - unfold spZ at 1. rewrite QA2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact P4.
  - lia.
  - unfold ESTACK. rewrite crt_STK. lia.
  - exact QA3.
  - exact QA4.
  - exact QA1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact QA10.
  - exact QA11.
  - lia.
  - rewrite EF, ESA. lia.
  - rewrite EF, ESA. replace (fs_frame_bytes 5 / 8) with 256 by (vm_compute; reflexivity). lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & K1).
(* ---- run B: the frame-done magic at F, bnez s4 (not taken), jal __asan_stack_free_5 ---- *)
assert (QB2 : getr regs2 2 = w64 crt_sp1) by (rewrite (crt_preg _ _ 2%bv HP2) by crt_cs; exact QA2).
assert (QB3 : getr regs2 3 = w64 (as_gp B)) by (rewrite (crt_preg _ _ 3%bv HP2) by crt_cs; exact QA3).
assert (QB4 : getr regs2 4 = w64 (as_tp B)) by (rewrite (crt_preg _ _ 4%bv HP2) by crt_cs; exact QA4).
assert (QB8 : getr regs2 8 = w64 sp0) by (rewrite (crt_preg _ _ 8%bv HP2) by crt_cs; exact QA8).
assert (QB18 : getr regs2 18 = w64 (crt_F pos)) by (rewrite (crt_preg _ _ 18%bv HP2) by crt_cs; exact QA18).
assert (QB20 : getr regs2 20 = w64 (crt_F pos)) by (rewrite (crt_preg _ _ 20%bv HP2) by crt_cs; exact QA20).
assert (HEIB : img_env VAL A_LIM (crtepi_EA regs2)) by (unfold crtepi_EA; apply Eimg_env).
pose proof (crtepi_a32 regs2) as EB32.
assert (UB18 : bv_unsigned (ew (crtepi_EA regs2) 18) = crt_F pos)
  by (rewrite (crtepi_rega regs2 18 18%bv eq_refl), QB18; unfold w64; apply unsigned_lit_small; lia).
assert (UB20 : bv_unsigned (ew (crtepi_EA regs2) 20) = crt_F pos)
  by (rewrite (crtepi_rega regs2 20 20%bv eq_refl), QB20; unfold w64; apply unsigned_lit_small; lia).
assert (UBB : U (crtepi_EA regs2) (SOff 32 0) = SHADOW_OFF)
  by (apply U_atom; [rewrite EB32; reflexivity | unfold SB, SHADOW_OFF; lia]).
pose proof HJ2 as HJ2c. pose proof HJ2c as (HAR2 & _).
assert (HSSB : st_ok_pi SEGS VAL (crtepi_EA regs2) crtepi_ssB
   (restrict (w_H Wc) (mkst regs2 (Z_to_bv 64 (BASE + 7740)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold crtepi_ssB. apply pa_entry_st_ok_full.
  - unfold crtepi_EA. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite UB18. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS).
    destruct (al_frames _ _ LAWS lyc Sc Wc mem2 md2 5 pos HAR2 Hin5) as (_ & _ & Hfp & _).
    refine (proj1 (Hfp (crt_F pos + o) _)). rewrite EF.
    replace (fs_frame_bytes 5) with 2048 by (vm_compute; reflexivity). lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite UB20, EB32. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. unfold PTR. cbn [af_lo af_hi af_al2]. change (2 ^ 5) with 32.
    destruct (al_frames _ _ LAWS lyc Sc Wc mem2 md2 5 pos HAR2 Hin5) as (Hal32 & _).
    rewrite EF in Hal32. repeat split; try lia; try exact Hal32. }
assert (SHOKB : sh_ok SEGS (SOff 32 0) crtepi_SHB (crtepi_EA regs2) (mrestrict (w_H Wc) mem2)).
{ unfold sh_ok, crtepi_SHB. apply Forall_cons; [|apply Forall_nil].
  apply (shent_app_of_frame SEGS B LAWS lyc Sc Wc mem2 md2 (crtepi_EA regs2) (SOff 32 0) 18%nat
    (crt_F pos) 5 pos 0 8 (mrestrict (w_H Wc) mem2) HAR2 Hin5 UBB);
  [ apply U_atom; [rewrite (crtepi_rega regs2 18 18%bv eq_refl), QB18; reflexivity | lia]
  | rewrite EF; lia | lia
  | rewrite EF; replace (fs_frame_bytes 5) with 2048 by (vm_compute; reflexivity); lia ]. }
paj_run_tok RUN HSSB HJ2 SHOKB Bspan.
{ unfold crtepi_ssB. cbn [ss_mem].
  eapply awr_ok_cons_gen; [reflexivity | exact UB18 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite EF.
  replace (fs_frame_bytes 5) with 2048 by (vm_compute; reflexivity). lia. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => crt_F pos <= a < crt_F pos + 8) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
                [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite UB18 in Hrr; lia |]);
        destruct Hin)) as K2.
clear HF HFr HG. clear_md.
assert (QC1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + 7768))
  by (crt_rreg HSSB; apply (codeptr_val _ 7768 HEIB)).
assert (QC2 : getr (ms_regs ms0) 2 = w64 crt_sp1)
  by (crt_rreg HSSB; rewrite crt_den_atom0, (crtepi_rega regs2 2 2%bv eq_refl); exact QB2).
assert (QC3 : getr (ms_regs ms0) 3 = w64 (as_gp B))
  by (crt_rreg HSSB; rewrite crt_den_atom0, (crtepi_rega regs2 3 3%bv eq_refl); exact QB3).
assert (QC4 : getr (ms_regs ms0) 4 = w64 (as_tp B))
  by (crt_rreg HSSB; rewrite crt_den_atom0, (crtepi_rega regs2 4 4%bv eq_refl); exact QB4).
assert (QC8 : getr (ms_regs ms0) 8 = w64 sp0)
  by (crt_rreg HSSB; rewrite crt_den_atom0, (crtepi_rega regs2 8 8%bv eq_refl); exact QB8).
assert (QC10 : getr (ms_regs ms0) 10 = w64 (crt_F pos))
  by (crt_rreg HSSB; rewrite crt_den_atom0, (crtepi_rega regs2 20 20%bv eq_refl); exact QB20).
assert (QC11 : getr (ms_regs ms0) 11 = w64 1056)
  by (crt_rreg HSSB; unfold w64; rewrite denot_lit_U, U_SLit; reflexivity).
(* the memory at the stack_free call: everything outside crtepi_Wr is the memory of ST_EPI *)
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ crtepi_Wr pos a -> rdW Wc (ms_mem ms0) a = rdW Wc mc a).
{ intros a Ha Hn. unfold crtepi_Wr in Hn.
  rewrite (K2 a Ha ltac:(cbv beta; lia)). rewrite (K1 a Ha ltac:(lia) ltac:(unfold ESTACK; lia)). exact (KA a Ha). }
pmkst HSSB.
eapply SRr_bind.
{ apply (aj_stack_free_cls_atS SEGS B LAWS pa_segs_low ML (SIG CS___asan_stack_free_5) 5 (ASF5 fx) ltac:(lia)
    Wc (ms_regs ms0) (ms_mem ms0) STK sp0 crt_FP ly S W mem md [] lyc Sc _ k
    (crt_sp1 - sp0) (Z_to_bv 64 (BASE + 7768)) pos 1056 HJ2).
  - unfold spZ at 1. rewrite QC2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact P4.
  - lia.
  - unfold ESTACK. rewrite crt_STK. lia.
  - exact QC3.
  - exact QC4.
  - exact QC1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite EF. exact QC10.
  - exact QC11.
  - rewrite EF, EL. rewrite (rdword_ext (rdW Wc mc) (rdW Wc (ms_mem ms0))); [exact HFL|].
    intros kk Hkk. apply K3;
      [replace (fs_frame_bytes 5) with 2048 by (vm_compute; reflexivity); lia
      | apply AP4; replace (fs_frame_bytes 5) with 2048 by (vm_compute; reflexivity); lia]. }
cbv beta. intros W3 c3 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & K4).
(* ---- run C: sp = s0 - 256, the 13 saved registers reloaded, ret ---- *)
assert (QD2 : getr regs4 2 = w64 crt_sp1) by (rewrite (crt_preg _ _ 2%bv HP4) by crt_cs; exact QC2).
assert (QD3 : getr regs4 3 = w64 (as_gp B)) by (rewrite (crt_preg _ _ 3%bv HP4) by crt_cs; exact QC3).
assert (QD4 : getr regs4 4 = w64 (as_tp B)) by (rewrite (crt_preg _ _ 4%bv HP4) by crt_cs; exact QC4).
assert (QD8 : getr regs4 8 = w64 sp0) by (rewrite (crt_preg _ _ 8%bv HP4) by crt_cs; exact QC8).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ crtepi_Wr pos a -> rdW Wc mem4 a = rdW Wc mc a).
{ intros a Ha Hn. pose proof Hn as Hn'. unfold crtepi_Wr in Hn'.
  rewrite (K4 a Ha ltac:(rewrite EF, ESA; replace (fs_frame_bytes 5 / 8) with 256 by (vm_compute; reflexivity); lia)
            ltac:(rewrite EL; lia) ltac:(unfold ESTACK; lia)).
  exact (K3 a Ha Hn). }
assert (HFR4 : crt_frame (rdW Wc mem4)).
{ intros j r Hj. assert (Hj13 : (j < 13)%nat)
    by (rewrite <- crt_saved_len; apply nth_error_Some; rewrite Hj; discriminate).
  apply (crt_aval_kept (rdW Wc mc)); [|exact (HFRc j r Hj)].
  intros kk Hkk. apply KEEP; [lia | apply AP3; lia]. }
assert (HEIC : img_env VAL A_LIM (crtepi_EC regs4)) by (unfold crtepi_EC; apply Eimg_env).
pose proof (crtepi_c32 regs4) as EC32.
assert (UC8 : bv_unsigned (ew (crtepi_EC regs4) 8) = sp0)
  by (rewrite (crtepi_regc regs4 8 8%bv eq_refl), QD8; unfold w64; apply unsigned_lit_small; lia).
assert (HSC : st_ok_pi SEGS VAL (crtepi_EC regs4) crtepi_ssC
   (restrict (w_H Wc) (mkst regs4 (Z_to_bv 64 (BASE + 7768)) mem4 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold crtepi_ssC. apply pa_entry_st_ok_full.
  - unfold crtepi_EC. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. apply (crtepi_rg_stk regs4 _ UC8).
    intros j r Hj. apply crt_val_of_aval. exact (HFR4 j r Hj).
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite UC8, EC32. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. change (2 ^ 4) with 16. repeat split; try lia; try exact S3. }
assert (SHOKC : sh_ok SEGS (SOff 32 0) [] (crtepi_EC regs4) (mrestrict (w_H Wc) mem4))
  by (unfold sh_ok; apply Forall_nil).
paj_run_tok RUN HSC HJ4 SHOKC Bspan.
{ awr_ok_tac. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
        destruct Hin)) as K5.
clear HF HFr HG. clear_md.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ crtepi_Wr pos a -> rdW Wc (ms_mem ms1) a = rdW Wc mc a)
  by (intros a Ha Hn; rewrite (K5 a Ha ltac:(cbv beta; tauto)); exact (KEEP a Ha Hn)).
pose proof (crtepi_ES regs4) as ES.
eapply (RET Wc _ _ _ _ _ HSC eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
assert (Q1 : getr (ms_regs ms1) 1 = getr regs 1)
  by (crt_rreg HSC; rewrite crt_den_atom0; exact (ES 0%nat 1%nat eq_refl)).
rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra.
unfold crt_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
  exists lyc, (stack_free_state 5 pos Sc), r, m, d end.
split; [reflexivity|].
split.
{ eapply ajournal_mono_k; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ4 | exact Hk]. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr. repeat match type of Hc with _ \/ _ => destruct Hc as [-> | Hc] | ?x = _ => subst x end.
  all: crt_rreg HSC.
  all: rewrite crt_den_atom0.
  all: first
   [ rewrite (crtepi_regc regs4 8 8%bv eq_refl), QD8; unfold w64, spZ;
     rewrite Z_to_bv_bv_unsigned; reflexivity
   | rewrite (crtepi_regc regs4 3 3%bv eq_refl), QD3; rewrite <- Hgp; reflexivity
   | rewrite (crtepi_regc regs4 4 4%bv eq_refl), QD4; rewrite <- Htp; reflexivity
   | match goal with |- ew _ ?n = getr regs (Z_to_bv 5 ?r) => exact (ES (n - 33)%nat (Z.to_nat r) eq_refl) end ]. }
(* ---- the post: the recorder after the round trip, the rest blocks kept ---- *)
assert (EAB : ablocks B lyc (stack_free_state 5 pos Sc) = ablocks B lyc Sc)
  by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
assert (EBB : blocks_bytes (stack_free_state 5 pos Sc) = blocks_bytes Sc) by reflexivity.
assert (HQF4 : crt_QF lyc (stack_free_state 5 pos Sc) Wc (ms_mem ms1) Rf Of).
{ apply (crtepi_QF_keep lyc Sc (stack_free_state 5 pos Sc) Wc mc (ms_mem ms1) dc pos Rf Of
    HAR Hin5 EF EL EAB EBB); [|exact KF | exact HQF].
  intros m Hm. unfold stack_free_state. apply (mo_le_set_fs_r MT MTFL). exact Hm. }
destruct HQF4 as (HREPF & F1 & F2 & F3 & F4 & F5 & F6 & F7 & HVQF & HPMF & HBBF & HMOF).
unfold crt_Q. exists Rf, Of.
split; [exact HREPF|]. split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|].
split; [exact F5|]. split; [exact F6|]. split; [exact F7|].
split; [exact HVQF|]. split; [exact HPMF|].
split.
{ intros p n i Hin Hi.
  pose proof (ajournal_materialize SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ4) as HJF.
  pose proof HJF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FB & _).
  assert (Hin0 : In (p, n) (ablocks B ly S))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; exact Hin).
  assert (Hin1 : In (p, n) (ablocks B lyc (stack_free_state 5 pos Sc)))
    by (rewrite EAB; apply (Permutation_in _ (Permutation_sym HPMF)); apply in_or_app; right; exact Hin).
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR0 Hin0) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos n (proj1 Hm)) as [Hq1 Hq2].
  exact (FB p n i Hin0 Hin1 ltac:(lia) (crtepi_rest_fp p n i Hin ltac:(lia))). }
split; [exact HBBF | exact HMOF].
Qed.
(* the points after send_message's return, at the ambient FP state. `Proof using All`: every Section variable is a
   premise, so that tcheck_round_trip_spec_holds gives them positionally at the FP state send_message returns *)
Lemma crt_G : ST_G.
Proof using All.
apply crt_s7. apply crt_s8. apply crt_s9. apply crt_s10. apply crt_s11. apply crt_s12. exact crt_epi.
Qed.
(* the walk up to send_message's return, from the points after it at every FP state send_message may return *)
Lemma crt_walk_pre : (forall f : YK11.FPState, fxrel fx f -> ST_Gx f) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_check_round_trip) regs mem md) crt_postF.
Proof using All.
intros HG. apply crt_s0. apply crt_s1. apply crt_s2. apply crt_s3; [|exact crt_epi].
apply crt_s4. apply crt_s5. apply crt_s6. exact HG.
Qed.

End w.
End e.
End d.
End b.

(* ---------- the theorem ---------- *)
(* Once the sections close, crt_G holds at every FP state: the theorem uses it at the FP state fx1 send_message
   returns (rounding mode 0 at fx1 from HFRM by PaFx.v's fxrel_frm0), and crt_walk_pre at the entry's. The Section
   hypotheses are crt_G's and crt_walk_pre's (check_round_trip_c.v's own and the per-binary record), in their order. *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HSEND : forall fx0 : YK11.FPState, @tsend_message_spec fx0 rc SK PI B MT.
Hypothesis HJOINED : forall fx0 : YK11.FPState, @tjoined_spec fx0 rc SK PI B MT.
Hypothesis HRCC : forall fx0 : YK11.FPState, @trec_calls_copy_spec fx0 rc SK PI B MT.
Hypothesis HRCE : forall fx0 : YK11.FPState, @trec_calls_equal_spec fx0 rc SK PI B MT.
Hypothesis HRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Variable PC_STRDUP_RA0 : Z.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASTRDUP4 : forall fx0 : YK11.FPState, @astrdup04_rule fx0 rc SK SEGS B MT (SIG CS___interceptor_trampoline_strdup) PC_STRDUP_RA0.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis ASM5 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 5.
Hypothesis ASF5 : forall fx0 : YK11.FPState, @astack_free_cls_realizes fx0 rc SEGS B (SIG CS___asan_stack_free_5) 5.
Hypothesis ASH00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0.
Hypothesis ASHF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8.
Hypothesis HVAL : cmd_val_objs.
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.
Theorem tcheck_round_trip_spec_holds : tcheck_round_trip_spec B MT.
Proof.
unfold tcheck_round_trip_spec.
intros ly S W regs mem md ch W0 sb hb arr q wp ws R O rest HPRE HPRES HFRM HROD _ HCNT HNFR H10 H11 H12 HSB HHB HW1 HW2
  HW8 HLEN HN31 HVN HVA HARR HARR8 HPERM HAB HWS HNEED HREP HNC HDECL HREPLY HQ HVQ HRT HEV HLIVE MOK.
(* the statement's cmd_ro_ok premise is not needed: cmd_ro_ok_of_aro gives cmd_ro_ok wherever arodata_okP holds *)
apply (crt_walk_pre B MT HSEND HJOINED HRCC HRCE HRCF PC_STRDUP_RA0 AFREE4 ASTRDUP4 ASTRCMP ASM5 ASF5 ASH00 ASHF8 HVAL
  HB TL TLF ML SMP MTL MTFL SIGP PRW IMG ly S W regs mem md ch W0 sb hb arr q wp ws R O rest
  HPRE HPRES HFRM HROD HCNT HNFR H10 H11 H12 HSB HHB HW1 HW2 HW8 HLEN HN31 HVN HVA HARR HARR8 HPERM HAB HWS HNEED HREP
  HNC HDECL HREPLY HQ HVQ HRT HEV HLIVE MOK).
intros fx1 Hfx.
exact (@crt_G fx1 rc SK PI B MT HSEND HJOINED HRCC HRCE HRCF PC_STRDUP_RA0 AFREE4 ASTRDUP4 ASTRCMP ASM5 ASF5 ASH00 ASHF8
  HVAL HB TL TLF ML SMP MTL MTFL SIGP PRW IMG ly S W regs mem md ch W0 sb hb arr q wp ws R O rest
  HPRE HPRES (fxrel_frm0 fx fx1 HFRM Hfx) HROD HCNT HNFR H10 H11 H12 HSB HHB HW1 HW2 HW8 HLEN HN31 HVN HVA HARR HARR8
  HPERM HAB HWS HNEED HREP HNC HDECL HREPLY HQ HVQ HRT HEV HLIVE MOK).
Qed.
End t.
