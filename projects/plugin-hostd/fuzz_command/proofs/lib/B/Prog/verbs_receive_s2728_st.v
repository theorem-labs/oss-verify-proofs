(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the state facts the walk of segments S27 (INST) and S28 (CONNBROAD) of
   verbs_receive on the ASan+UBSan build (image B) carries across a program call (interface:
   lib/B/Prog/verbs_receive_iface.v); the B twin of lib/A/Prog/verbs_receive_s2728_st.v. What differs from A: B's
   event constants (s28_ev_after), B's GOT words (cmd_got_of_ro, as the kit's vr_got_of_ro), B's frame budget
   VERBS_RECEIVE_STK, and the seeded spill slots (B's map: s1+8 = shadow_addr F, +16 = +24 = F, +32 =
   shadow_addr F + 4, +40 = F + 32 (tok), +56 = q).

   Each boundary state of the interface is `vr_core`; a call changes the allocator state, the recorder and the memory
   the callee's footprint names, and keeps the rest. What the callee keeps is read off the journal the call rule
   returns (lib/Reusable/YCbq.v ajournal): the clauses for the bytes at or above alloc_ceiling, the bytes of a live
   block, the bytes of the image and the bytes of a frame. Each of those asks the address to lie outside the callee's
   footprint FP1; every FP1 of the recorder callees lies inside g_rec, record.spill and the recorder's own blocks
   (s28_FPrec), and the frameless callees (is_instance_verb, verb_is) have none.
   - q_rcallF: a recorder callee (printf-reaching, apost_baseF) through PaFx's cl_callS_wideF; its frame chain is
     q_achain's (s0 holds this frame's sp0: achain_push on afn_pre's chain with the prologue's saved ra and s0);
   - q_na_call: a frameless callee through cl_callS_na;
   - s28_post_new / s28_post_same: the boundary after a recorder call that returned a fresh text block / none;
   - q_keep_na: the boundary after a frameless call;
   - q_core_same and its siblings: the boundary at a state whose memory reads the same (after a symbolic run);
   - q_jmp: the jump from a return pc to a join (the S08 lane's vr_jmp).
   The reader transports (q_rdeq ...) and q_jmp are copied from the S08 lane's verbs_receive_s08_lib.v
   (a working branch 1413152415c). The blocks after a recorder call are re-assembled into the interface's
   Permutation with vr_perm_new / vr_perm_same, which need the live-block list to have no duplicate (the kit's
   RecBLemmas.recb_ablocks_nodup_m). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route verbs_receive_pre.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c xmalloc_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_live verbs_receive_s2728_fn PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module PP8 := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_pre.

(* ------------------------------------------------------------------------------------------------------------
   list plumbing. `NoDup` of this development is stdpp's (the semantics import it), so every lemma here names
   Stdlib's `List.NoDup`, which is what `NoDup_Permutation` asks for. *)
Lemma nodup_app3 : forall {X : Type} (l1 l2 : list X),
List.NoDup l1 -> List.NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> List.NoDup (l1 ++ l2).
Proof.
intros X l1. induction l1 as [|x l1 IH]; intros l2 H1 H2 Hd; cbn [app]; [exact H2|].
apply List.NoDup_cons_iff in H1 as [Hnin Hnd]. apply List.NoDup_cons_iff. split.
- intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hnin Hin) | exact (Hd x (or_introl eq_refl) Hin)].
- apply IH; [exact Hnd | exact H2 | intros y Hy; apply Hd; right; exact Hy].
Qed.

Lemma nodup_app_r : forall {X : Type} (l1 l2 : list X), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
intros X l1. induction l1 as [|x l1 IH]; intros l2 H; cbn [app] in H; [exact H|].
apply List.NoDup_cons_iff in H as [_ Hnd]. exact (IH l2 Hnd).
Qed.

Lemma nodup_app_disj : forall {X : Type} (l1 l2 : list X),
List.NoDup (l1 ++ l2) -> forall x, In x l1 -> ~ In x l2.
Proof.
intros X l1. induction l1 as [|y l1 IH]; intros l2 H x Hx Hin; [destruct Hx|].
apply List.NoDup_cons_iff in H as [Hnin Hnd].
destruct Hx as [<- | Hx]; [exact (Hnin (in_or_app _ _ _ (or_intror Hin))) | exact (IH l2 Hnd x Hx Hin)].
Qed.

Lemma perm_nodup2 : forall {X : Type} (l1 l2 : list X),
Permutation l1 l2 -> List.NoDup l1 -> List.NoDup l2.
Proof.
intros X l1 l2 HP. induction HP as [|x l1 l2 HP IH|x y l|l1 l2 l3 HP1 IH1 HP2 IH2]; intros H.
- exact H.
- apply List.NoDup_cons_iff in H as [Hn H]. apply List.NoDup_cons_iff. split; [|exact (IH H)].
  intros Hin. exact (Hn (Permutation_in _ (Permutation_sym HP) Hin)).
- apply List.NoDup_cons_iff in H as [Hn H]. apply List.NoDup_cons_iff in H as [Hm H].
  apply List.NoDup_cons_iff. split.
  + intros [Hq | Hq]; [subst y; exact (Hn (or_introl eq_refl)) | exact (Hm Hq)].
  + apply List.NoDup_cons_iff. split; [intros Hq; exact (Hn (or_intror Hq)) | exact H].
- exact (IH2 (IH1 H)).
Qed.

Definition pn_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma nodup_filter : forall (f : Z * Z -> bool) l, List.NoDup l -> List.NoDup (List.filter f l).
Proof.
intros f l H. induction l as [|x l IH]; cbn [List.filter]; [apply List.NoDup_nil|].
apply List.NoDup_cons_iff in H as [Hnin Hnd]. destruct (f x); [|exact (IH Hnd)].
apply List.NoDup_cons_iff. split;
  [intros Hin; exact (Hnin (proj1 (proj1 (List.filter_In f x l) Hin))) | exact (IH Hnd)].
Qed.

Lemma perm_of_nodup : forall (l1 l2 : list (Z * Z)),
List.NoDup l1 -> List.NoDup l2 -> (forall x, In x l1 <-> In x l2) -> Permutation l1 l2.
Proof. intros l1 l2 H1 H2 HE. apply NoDup_Permutation; assumption. Qed.

(* an 8-byte little-endian word read off a byte list *)
Lemma aval_of_abytes8 : forall rd a (l : list byte) v,
abytes_atR rd a l ->
(forall k, (k < 8)%nat -> bv_unsigned (nth k l (Z_to_bv 8 0)) = le_byte v 8 k) ->
(8 <= length l)%nat ->
aval_mem rd a 8 v.
Proof. intros rd a l v Hb Hk Hl i Hi. rewrite (Hb i ltac:(lia)). f_equal. exact (Hk i Hi). Qed.

(* the store side condition of a run whose regions are all read-only *)
Ltac q_awr :=
lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* strip cmd_ro_bytes' conjunction down to the conjunct about address a. A search with backtracking over the
   209 conjuncts costs minutes; this walks the spine once. *)
Ltac ro_strip H a :=
  repeat (lazymatch type of H with
          | abytes_atR _ a _ /\ _ => fail
          | _ /\ _ => destruct H as [_ H]
          end).

(* ------------------------------------------------------------------------------------------------------------
   Readers that read the same (the S08 lane's verbs_receive_s08_lib.v) *)
Definition q_rdeq (rd rd' : reader) : Prop := forall a, rd' a = rd a.

Lemma q_aval_eq : forall rd rd' a n v, q_rdeq rd rd' -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v E H k Hk. rewrite E. exact (H k Hk). Qed.
Lemma q_abytes_eq : forall rd rd' a l, q_rdeq rd rd' -> abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l E H i Hi. rewrite E. exact (H i Hi). Qed.
Lemma q_astr_eq : forall rd rd' a s, q_rdeq rd rd' -> astr_atR rd a s -> astr_atR rd' a s.
Proof. intros rd rd' a s E [H1 H2]. split; [exact (q_abytes_eq rd rd' a _ E H1) | exact H2]. Qed.
Lemma q_rdword_eq : forall rd rd' a, q_rdeq rd rd' -> rdword rd' a = rdword rd a.
Proof. intros rd rd' a E. apply rdword_ext. intros k _. apply E. Qed.
Lemma q_rd32_eq : forall rd rd' a v, q_rdeq rd rd' -> rd32 rd a v -> rd32 rd' a v.
Proof. intros rd rd' a v E H k Hk. rewrite E. exact (H k Hk). Qed.
Lemma q_atoks_eq : forall rd rd' tok ptrs tks cb ncb, q_rdeq rd rd' ->
atoks_atA rd tok ptrs tks cb ncb -> atoks_atA rd' tok ptrs tks cb ncb.
Proof.
intros rd rd' tok ptrs tks cb ncb E (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
- intros i p Hp. exact (q_aval_eq rd rd' _ 8 p E (H3 i p Hp)).
- intros i p w Hp Hw. destruct (H4 i p w Hp Hw) as (A1 & A2 & A3 & A4).
  split; [exact (q_astr_eq rd rd' p w E A1) | auto].
Qed.
Lemma q_got_eq : forall rd rd', q_rdeq rd rd' -> cmd_got_ok rd -> cmd_got_ok rd'.
Proof.
intros rd rd' E (H1 & H2 & H3 & H4).
split; [exact (q_aval_eq _ _ _ _ _ E H1)|]. split; [exact (q_aval_eq _ _ _ _ _ E H2)|].
split; [exact (q_aval_eq _ _ _ _ _ E H3) | exact (q_aval_eq _ _ _ _ _ E H4)].
Qed.
Lemma q_ro_ok_eq : forall rd rd', q_rdeq rd rd' -> cmd_ro_ok rd -> cmd_ro_ok rd'.
Proof.
intros rd rd' E [Hb Ht]. split.
- unfold cmd_ro_bytes in *. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (eapply q_abytes_eq; [exact E | eassumption]).
- intros e' He a Ha. rewrite E. exact (Ht e' He a Ha).
Qed.

(* the 8-byte value of aval_mem, as rdword reads it *)
Lemma q_rdword_of_aval : forall (rd : reader) a v, aval_mem rd a 8 v -> 0 <= v < 2 ^ 64 -> rdword rd a = Some v.
Proof.
intros rd a v H Hr. unfold rdword.
assert (B0 : rd a = Some (le_byte v 8 0)) by (rewrite <- (Z.add_0_r a) at 1; exact (H 0%nat ltac:(lia))).
change (rd (a + 1)) with (rd (a + Z.of_nat 1)). change (rd (a + 2)) with (rd (a + Z.of_nat 2)).
change (rd (a + 3)) with (rd (a + Z.of_nat 3)). change (rd (a + 4)) with (rd (a + Z.of_nat 4)).
change (rd (a + 5)) with (rd (a + Z.of_nat 5)). change (rd (a + 6)) with (rd (a + Z.of_nat 6)).
change (rd (a + 7)) with (rd (a + Z.of_nat 7)).
rewrite B0, (H 1%nat), (H 2%nat), (H 3%nat), (H 4%nat), (H 5%nat), (H 6%nat), (H 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   Small model facts *)
Lemma q_spill0 : forall R, r_calls R = [] -> rec_spill_frees R = 0.
Proof. intros R H. unfold rec_spill_frees. rewrite H. reflexivity. Qed.

Lemma s28_rsf : forall R, 0 <= rec_spill_frees R.
Proof. intros R. unfold rec_spill_frees. destruct (Nat.ltb _ _); lia. Qed.

Lemma s28_ev_reply : 0 <= EV_REPLY.
Proof. vm_compute. intro H. discriminate H. Qed.

Lemma s28_ev_after : forall R af, 0 <= ev_after R af.
Proof.
intros R [x|]; cbn [ev_after]; [|lia]. unfold EV_SUP_AFTER_REPLY, EV_RECORD, EV_ARG_S, EV_XMALLOC.
pose proof (s28_rsf R). lia.
Qed.

(* the events after the handler: the reply and the call after it *)
Lemma q_k1_ev : forall R D, vr_k1 R D + 2 + EV_REPLY <= ev_vr R D.
Proof.
intros R D. rewrite ev_vr_eq. unfold vr_k3, vr_k2. pose proof (s28_ev_after (vr_R2 R D) (vr_aft D)). lia.
Qed.

(* the recorder after sup_broadcast holds one call more *)
Lemma s28_bcast_calls : forall R ln, r_calls R = [] -> length (r_calls (fst (sup_broadcast_m R ln))) = 1%nat.
Proof.
intros R ln HR. unfold sup_broadcast_m, rec_stub, rec_answer, rec_record, hand_back, rec_mix,
  set_answer, set_state, set_calls, set_spill.
rewrite HR. cbn [length Nat.ltb Nat.leb]. cbn [fst snd r_calls r_refuse].
destruct (r_refuse R =? 0); cbn [fst snd r_calls]; reflexivity.
Qed.

Lemma s28_bcast_spill : forall R ln, r_calls R = [] -> rec_spill_frees (fst (sup_broadcast_m R ln)) = 0.
Proof.
intros R ln HR. unfold rec_spill_frees. rewrite (s28_bcast_calls R ln HR). reflexivity.
Qed.

Lemma s28_toks_le : forall D, (length (Verbs.toks D) <= 64)%nat.
Proof. intros D. unfold Verbs.toks. rewrite length_firstn. unfold Verbs.line_words_max. lia. Qed.

Lemma q_strnlen_le : forall n D, 0 <= n -> 0 <= StrFun.strnlen_res n D <= n.
Proof.
intros n D Hn. unfold StrFun.strnlen_res.
destruct (StrFun.find_byte 0 (firstn (Z.to_nat n) D)) as [i|] eqn:Fb; [|lia].
destruct (StrFun.find_byte_Some _ _ _ Fb) as (Hl & _). rewrite length_firstn in Hl. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma q_val_mem_of_aval : forall H mem a n v,
aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte SEGS H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.

(* the four GOT words verbs_receive's callees load are read-only bytes of the image (B's CmdRo.v; the proof is the
   kit's vr_got_of_ro, verbs_receive_s30_kit.v, which takes that file's section hypotheses) *)
Lemma cmd_got_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [Hb _]. unfold cmd_ro_bytes in Hb. decompose [and] Hb. clear Hb.
unfold cmd_got_ok. split; [|split; [|split]];
(eapply aval_of_abytes8; [eassumption | | vm_compute; lia];
 intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia).
Qed.

Lemma s28_s1_facts : forall e, vr_sp0 e mod 16 = 0 ->
vr_s1 e mod 16 = 0 /\ vr_sp0 e - 208 <= vr_s1 e <= vr_sp0 e - 192 /\ (vr_s1 e - vr_sp0 e) mod 16 = 0.
Proof.
intros e H. unfold vr_s1. set (sp := vr_sp0 e) in *.
pose proof (Z.mod_pos_bound (sp - 192) 32 ltac:(lia)) as M.
pose proof (Z.div_mod (sp - 192) 32 ltac:(lia)) as D.
pose proof (Z.div_mod sp 16 ltac:(lia)) as D2.
set (qq := (sp - 192) / 32) in *. set (r := (sp - 192) mod 32) in *.
split; [|split].
- replace (sp - 192 - r) with ((2 * qq) * 16) by lia. apply Z.mod_mul. lia.
- lia.
- replace (sp - 192 - r - sp) with ((2 * qq - sp / 16) * 16) by lia. apply Z.mod_mul. lia.
Qed.

(* the symbolic state at a return pc: the registers alone *)
Definition q_ss_ret (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

Lemma q_env_agree : forall (regs : bvmap 5 word) extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma q_kept_regs : forall E ss ms (regs0 : bvmap 5 word) extra (zs : list Z),
st_ok SEGS E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) (map (Z_to_bv 5) zs) = true ->
forall r, In r zs -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros E ss ms regs0 extra zs HS HA Hl r Hr.
apply (regs_kept_of_st_ok SEGS E ss ms regs0 extra (map (Z_to_bv 5) zs) HS HA Hl). apply in_map. exact Hr.
Qed.

Lemma q_rdeq_of_frame : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
q_rdeq (aview SEGS H m) (aview SEGS H m').
Proof.
intros E rs H m m' Hf Hro a. apply (aview_eq_of SEGS). apply Hf.
intros (r & Hr & Ha). rewrite Forall_forall in Hro. pose proof (Hro r Hr). lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the jump of a return pc to a join (one `j`), run from a state that names only the registers (the S08 lane's
   vr_jmp) *)
Lemma q_jmp : forall retk stopk, 0 <= retk ->
sym_run_toN_pi pl_tpi FUEL stopk (q_ss_ret retk) = (q_ss_ret stopk, PRS_running) ->
forall W2 (regs2 : bvmap 5 word) mem2 md2 (Q : world SEGS -> config -> Prop) STK sp0 FP ly S W0 mem md own ly2 S2 kk,
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 kk ->
(forall regs3 mem3 md3, (forall r, getr regs3 r = getr regs2 r) -> q_rdeq (rdW W2 mem2) (rdW W2 mem3) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem3 md3 kk ->
  Q W2 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + stopk)) mem3 (seg_rom SEGS)) md3)) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros retk stopk Hk Hrun W2 regs2 mem2 md2 Q STK sp0 FP ly S W0 mem md own ly2 S2 kk HJ HQ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs2 [])) (q_ss_ret retk)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold q_ss_ret. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
eapply (SRr_run_to_pi_AJ B LAWS W2 FUEL stopk (Eimg (Ereg regs2 [])) (q_ss_ret retk) (q_ss_ret stopk) PRS_running _
  STK sp0 FP ly S W0 mem md own ly2 S2 md2 kk Q HEI HS Hrun I HJ).
- apply awr_ok_nil.
- intros ms' mat HS' HJ' HF HFr HG.
  rewrite (st_ok_pi_restrict_mkst (w_H W2) _ (q_ss_ret stopk) ms' HS' eq_refl). cbn [ss_pc q_ss_ret].
  apply SRr_ret. apply HQ.
  + intros r. rewrite (st_ok_pi_restrict_reg (w_H W2) _ (q_ss_ret stopk) ms' r HS'). cbn [ss_regs q_ss_ret].
    symmetry. exact (regs_ok_Eimg_Ereg regs2 [] r).
  + cbn [ms_mem mkst ss_mem q_ss_ret] in HFr. exact (q_rdeq_of_frame _ [] _ _ _ HFr (Forall_nil _)).
  + exact HJ'.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The boundary state at a state whose memory reads the same (the S08 lane's vr_core_same and siblings) *)
Lemma q_aro_eq : forall rd rd', q_rdeq rd rd' -> arodata_okP SEGS RLO RHI B rd -> arodata_okP SEGS RLO RHI B rd'.
Proof. intros rd rd' E H a H1 H2 H3. rewrite E. exact (H a H1 H2 H3). Qed.

Lemma q_env_same : forall W mem W' mem', q_rdeq (rdW W mem) (rdW W' mem') ->
vr_env B W mem -> vr_env B W' mem'.
Proof.
intros W mem W' mem' E (H1 & H2 & H3 & (G1 & c & G2) & H5 & ev & H6).
split; [exact (q_aro_eq _ _ E H1)|]. split; [exact (q_got_eq _ _ E H2)|].
split; [exact (q_ro_ok_eq _ _ E H3)|].
split; [split; [rewrite (q_rdword_eq _ _ _ E); exact G1 | exists c; rewrite (q_rdword_eq _ _ _ E); exact G2]|].
split; [rewrite E; exact H5 | exists ev; exact (q_rd32_eq _ _ _ _ E H6)].
Qed.

Lemma q_core_same : forall e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md W' regs' mem' md',
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W' mem' md' k ->
q_rdeq (rdW W mem) (rdW W' mem') ->
vr_rv regs' (vr_base B e ++ rl') ->
vr_core B MT e pos F tmps sh sl rl' Rc Oc qv k kmax nm nmax lyc Sc W' regs' mem' md'.
Proof.
intros e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md W' regs' mem' md'
(HJ & Hk & Hm & Hnm & (HF1 & HF2 & HF3) & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq) HJ' E Hrv'.
split; [exact HJ'|]. split; [exact Hk|]. split; [exact Hm|]. split; [exact Hnm|].
split; [split; [exact HF1|]; split; [rewrite (q_rdword_eq _ _ _ E); exact HF2 | intros i Hi; rewrite E; exact (HF3 i Hi)]|].
split; [exact Hrv'|].
split; [intros j r Hj; exact (q_aval_eq _ _ _ _ _ E (Hsv j r Hj))|].
split; [unfold vr_spill in *; eapply Forall_impl; [|exact Hsp]; intros ov Hov; exact (q_aval_eq _ _ _ _ _ E Hov)|].
split; [exact (q_env_same W mem W' mem' E Henv)|].
split.
{ apply (rec_repA_agree B _ _ _ _ _ _ Rc Oc Hrec (fun pn _ Hb => Hb)); intros; apply E. }
split; [exact Hdat|]. split; [exact Hperm | exact (q_aval_eq _ _ _ _ _ E Hq)].
Qed.

Lemma q_line_same : forall e q W mem W' mem', q_rdeq (rdW W mem) (rdW W' mem') ->
vr_line B e q W mem -> vr_line B e q W' mem'.
Proof. intros e q W mem W' mem' E [H1 H2]. split; [exact H1 | exact (q_astr_eq _ _ _ _ E H2)]. Qed.
Lemma q_copy_same : forall e F c tp W mem W' mem', q_rdeq (rdW W mem) (rdW W' mem') ->
vr_copy B e F c tp W mem -> vr_copy B e F c tp W' mem'.
Proof. intros e F c tp W mem W' mem' E [H1 H2]. split; [exact H1 | exact (q_atoks_eq _ _ _ _ _ _ _ E H2)]. Qed.

(* reading and writing the register list of a boundary *)
Lemma vr_rv_get : forall (regs : bvmap 5 word) l r v, vr_rv regs l -> In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs l r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma q_rv_intro : forall regs l, (forall r v, In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v) -> vr_rv regs l.
Proof. intros regs l H. unfold vr_rv. apply Forall_forall. intros [r v] Hin. exact (H r v Hin). Qed.
(* the registers of a new state: the base ones kept, each listed one kept or set *)
Lemma q_rv_keep : forall e (regs regsc : bvmap 5 word) rl rl',
vr_rv regsc (vr_base B e ++ rl) ->
(forall r, In r [2; 3; 4; 8; 9] -> getr regs (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) ->
(forall r v, In (r, v) rl' ->
  (In (r, v) rl /\ getr regs (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) \/ getr regs (Z_to_bv 5 r) = w64 v) ->
vr_rv regs (vr_base B e ++ rl').
Proof.
intros e regs regsc rl rl' Hrv Hb Hl. apply q_rv_intro. intros r v Hin. apply in_app_or in Hin as [Hin|Hin].
- assert (Hr : In r [2; 3; 4; 8; 9]).
  { unfold vr_base in Hin. cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _; cbn; tauto. }
  rewrite (Hb r Hr). apply (vr_rv_get regsc _ _ _ Hrv). apply in_or_app; left; exact Hin.
- destruct (Hl r v Hin) as [[H1 H2] | H]; [|exact H].
  rewrite H2. apply (vr_rv_get regsc _ _ _ Hrv). apply in_or_app; right; exact H1.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The two reassemblies of the interface's Permutation after a call *)

(* the blocks after a recorder call that returned the fresh text block (q, n) *)
Lemma vr_perm_new : forall ly S ly' S' (W' : world SEGS) mem' md' (O tmps rest O' : list (Z * Z)) (q n : Z),
AR SEGS B ly' S' W' mem' md' ->
List.NoDup (ablocks B ly S) ->
Permutation (ablocks B ly S) (O ++ tmps ++ rest) ->
(forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) ->
(forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) ->
(forall pn, In pn O' -> In pn (ablocks B ly' S')) ->
In (q, n) (ablocks B ly' S') -> (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, n)) -> ~ In (q, n) O' ->
exists O1, (forall pn, In pn O1 <-> In pn O') /\
Permutation (ablocks B ly' S') (O1 ++ ((q, n) :: tmps) ++ rest).
Proof.
intros ly S ly' S' W' mem' md' O tmps rest O' q n HAR HND HP Hin1 Hin2 Hin3 Hin4 Hq1 Hq2 Hq3.
pose proof (RecBLemmas.recb_ablocks_nodup_m B ly' S' W' mem' md' HAR) as HND'.
pose proof (perm_nodup2 _ _ HP HND) as HNDO.
pose proof (nodup_app_r O (tmps ++ rest) HNDO) as HNDT.
pose proof (nodup_app_disj O (tmps ++ rest) HNDO) as HDIS.
set (O1 := List.filter (fun pn => if in_dec pn_eq_dec pn O' then true else false) (ablocks B ly' S')) in *.
assert (HO1 : forall pn, In pn O1 <-> In pn O').
{ intros pn. unfold O1. rewrite List.filter_In. split.
  - intros [_ H]. destruct (in_dec pn_eq_dec pn O') as [Hy|Hn]; [exact Hy | discriminate H].
  - intros H. split; [exact (Hin4 pn H)|]. destruct (in_dec pn_eq_dec pn O') as [_|Hn]; [reflexivity | contradiction]. }
assert (HND1 : List.NoDup O1) by (unfold O1; apply nodup_filter; exact HND').
assert (HTR : forall pn, In pn (tmps ++ rest) <-> (In pn (ablocks B ly S) /\ ~ In pn O)).
{ intros pn. split.
  - intros H. split.
    + apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact H.
    + intros HO. exact (HDIS pn HO H).
  - intros [Hin HO]. pose proof (Permutation_in _ HP Hin) as H.
    apply in_app_or in H as [H|H]; [contradiction | exact H]. }
exists O1. split; [exact HO1|].
apply perm_of_nodup; [exact HND' | |].
- apply nodup_app3; [exact HND1 | |].
  + apply List.NoDup_cons_iff. split; [|exact HNDT]. intros Hin. apply HTR in Hin as [Hin HO]. exact (Hq2 _ Hin HO eq_refl).
  + intros pn Hpn Hin. apply HO1 in Hpn. destruct Hin as [Hq | Hin].
    * subst pn. exact (Hq3 Hpn).
    * apply HTR in Hin as [Hin HO]. destruct (Hin3 pn Hpn) as [H|H]; [exact (HO H) | exact (H Hin)].
- intros pn. split.
  + intros Hin. destruct (Hin1 pn Hin) as [[Ha Hb] | [Ha | Ha]].
    * apply in_or_app. right. right. apply HTR. split; assumption.
    * apply in_or_app. left. apply HO1. exact Ha.
    * subst pn. apply in_or_app. right. left. reflexivity.
  + intros Hin. apply in_app_or in Hin as [Hin | Hin].
    * exact (Hin4 pn (proj1 (HO1 pn) Hin)).
    * destruct Hin as [Hq | Hin]; [subst pn; exact Hq1|].
      apply HTR in Hin as [Ha Hb]. exact (Hin2 pn Ha Hb).
Qed.

(* the blocks after a recorder call that returned no block (sup_host_setting) *)
Lemma vr_perm_same : forall ly S ly' S' (W' : world SEGS) mem' md' (O tmps rest O' : list (Z * Z)),
AR SEGS B ly' S' W' mem' md' ->
List.NoDup (ablocks B ly S) ->
Permutation (ablocks B ly S) (O ++ tmps ++ rest) ->
(forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) ->
(forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) ->
(forall pn, In pn O' -> In pn (ablocks B ly' S')) ->
exists O1, (forall pn, In pn O1 <-> In pn O') /\
Permutation (ablocks B ly' S') (O1 ++ tmps ++ rest).
Proof.
intros ly S ly' S' W' mem' md' O tmps rest O' HAR HND HP Hin1 Hin2 Hin3 Hin4.
pose proof (RecBLemmas.recb_ablocks_nodup_m B ly' S' W' mem' md' HAR) as HND'.
pose proof (perm_nodup2 _ _ HP HND) as HNDO.
pose proof (nodup_app_r O (tmps ++ rest) HNDO) as HNDT.
pose proof (nodup_app_disj O (tmps ++ rest) HNDO) as HDIS.
set (O1 := List.filter (fun pn => if in_dec pn_eq_dec pn O' then true else false) (ablocks B ly' S')) in *.
assert (HO1 : forall pn, In pn O1 <-> In pn O').
{ intros pn. unfold O1. rewrite List.filter_In. split.
  - intros [_ H]. destruct (in_dec pn_eq_dec pn O') as [Hy|Hn]; [exact Hy | discriminate H].
  - intros H. split; [exact (Hin4 pn H)|]. destruct (in_dec pn_eq_dec pn O') as [_|Hn]; [reflexivity | contradiction]. }
assert (HND1 : List.NoDup O1) by (unfold O1; apply nodup_filter; exact HND').
assert (HTR : forall pn, In pn (tmps ++ rest) <-> (In pn (ablocks B ly S) /\ ~ In pn O)).
{ intros pn. split.
  - intros H. split.
    + apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact H.
    + intros HO. exact (HDIS pn HO H).
  - intros [Hin HO]. pose proof (Permutation_in _ HP Hin) as H.
    apply in_app_or in H as [H|H]; [contradiction | exact H]. }
exists O1. split; [exact HO1|].
apply perm_of_nodup; [exact HND' | |].
- apply nodup_app3; [exact HND1 | exact HNDT |].
  intros pn Hpn Hin. apply HO1 in Hpn. apply HTR in Hin as [Hin HO].
  destruct (Hin3 pn Hpn) as [H|H]; [exact (HO H) | exact (H Hin)].
- intros pn. split.
  + intros Hin. destruct (Hin1 pn Hin) as [[Ha Hb] | Ha].
    * apply in_or_app. right. apply HTR. split; assumption.
    * apply in_or_app. left. apply HO1. exact Ha.
  + intros Hin. apply in_app_or in Hin as [Hin | Hin].
    * exact (Hin4 pn (proj1 (HO1 pn) Hin)).
    * apply HTR in Hin as [Ha Hb]. exact (Hin2 pn Ha Hb).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The entry facts at a later FP state: only rounding mode 0 names the FP state, and fxrel keeps it (the lead's
   verbs_receive.v vr_ent_fxr, under this file's name) *)
Lemma q_ent_fxr : forall f0 f1 e, vr_ent (fx := f0) B MT e -> fxrel f0 f1 -> vr_ent (fx := f1) B MT e.
Proof.
intros f0 f1 e He Hr. revert He. unfold vr_ent. cbv zeta. intros He.
repeat lazymatch type of He with
| _ /\ _ => let H1 := fresh "H" in destruct He as [H1 He]; split; [exact H1|]
end.
exact (fxrel_frm0 f0 f1 He Hr).
Qed.

(* rounding mode 0 at the entry FP state: vr_ent's last conjunct *)
Lemma q_ent_frm0 : forall e, vr_ent B MT e -> frm0 fx.
Proof.
intros e He. unfold vr_ent in He. cbv zeta in He.
repeat lazymatch type of He with _ /\ _ => apply proj2 in He end. exact He.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The meter across a call whose account X is at most am mallocs of at most VERBS_RECEIVE_REQ bytes and af frees,
   each at most the ev events the call spends: the callee's mo_ok premise (the interface's vri_meter_ok) and the
   boundary's vr_meter after its mo_le (vri_meter_step) *)
Lemma q_meter : forall (e : vrE) Sc k nm X am af ev,
ameter_laws MT -> vr_ent B MT e -> vr_meter MT e Sc k nm ->
X <= am * mo_malloc MT VERBS_RECEIVE_REQ + af * mo_free MT -> 0 <= am <= ev -> 0 <= af <= ev ->
k + ev <= ev_vr (e_R e) (e_D e) ->
mo_ok MT Sc X /\ (forall S2, mo_le MT Sc S2 X -> vr_meter MT e S2 (k + ev) (nm + am)).
Proof.
intros e Sc k nm X am af ev ML Hent Hm HX Ha Hb Hk. split.
- exact (vri_meter_ok B MT e Sc k nm X am af ev ML Hent Hm HX Ha Hb Hk).
- intros S2 Hle. exact (vri_meter_step MT e Sc S2 k nm X am af ev ML Hm Hle HX Ha Hb).
Qed.

(* one malloc of at most VERBS_RECEIVE_REQ bytes *)
Lemma q_mall : forall n, ameter_laws MT -> 0 <= n <= VERBS_RECEIVE_REQ -> mo_malloc MT n <= mo_malloc MT VERBS_RECEIVE_REQ.
Proof. intros n ML Hn. apply (mo_malloc_mono MT ML). lia. Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The record facts of the brief (names and types as the segment files carry them) *)
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.

Lemma vr_roP_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)].
Qed.

(* vr_env at any AR state whose read-only bytes are the image's *)
Lemma vr_env_of : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> arodata_okP SEGS RLO RHI B (rdW W mem) -> vr_env B W mem.
Proof.
intros ly S W mem md HAR HRO.
pose proof (ROA ly S W mem md HAR HRO) as HCR.
destruct (RECC ly S W mem md HAR) as (HFL & HAG & HER).
split; [exact HRO|]. split; [exact (cmd_got_of_ro _ HCR)|]. split; [exact HCR|].
split; [exact HAG|]. split; [exact HFL | exact HER].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The recorder's statics, and the footprint of a recorder callee *)
Definition s28_recrng (a : Z) : Prop :=
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).
Definition s28_FPrec (Oc FP1 : list (Z * Z)) : Prop :=
forall a, inFP FP1 a -> s28_recrng a \/ (exists p n, In (p, n) Oc /\ p <= a < p + req_size n).

Lemma s28_pg_img : forall a, s28_recrng a \/ (A_G_QUITTING <= a < A_G_QUITTING + 4) -> inFP cmd_PG a.
Proof.
intros a H. unfold cmd_PG, s28_recrng, REC_SIZE, SC_SIZE in *.
destruct H as [[H | H] | H]; [exists (A_G_REC, A_G_REC + 960) | exists (A_REC_SPILL, A_REC_SPILL + 56)
  | exists (A_G_QUITTING, A_G_QUITTING + 4)]; (split; [cbn; tauto | cbn [fst snd]; lia]).
Qed.

Lemma s28_FP_conn : forall O,
s28_FPrec O ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
  (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O).
Proof.
intros O a H. unfold s28_recrng, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_STATE, REC_SIZE in *.
apply inFP_cons in H as [H|H]; [left; left; lia|].
apply inFP_cons in H as [H|H]; [left; left; lia|].
apply inFP_cons in H as [H|H]; [left; left; lia|].
apply inFP_cons in H as [H|H]; [left; right; lia|].
right. exact (inFP_ablocks_fp_inv O a H).
Qed.

Lemma s28_FP_hs : forall O,
s28_FPrec O ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O).
Proof.
intros O a H. unfold s28_recrng in *.
apply inFP_cons in H as [H|H]; [left; left; lia|].
apply inFP_cons in H as [H|H]; [left; right; lia|].
right. exact (inFP_ablocks_fp_inv O a H).
Qed.

Lemma s28_FP_nil : forall O, s28_FPrec O [].
Proof. intros O a H. exfalso. exact (inFP_nil a H). Qed.

Lemma s28_frames_own : forall STK sp0 FP ly S W mem md pos lyc Sc Wc memc mdc k,
ajournal SEGS B STK sp0 FP ly S W mem md [(4, pos)] lyc Sc Wc memc mdc k -> In (4, pos) (frames Sc).
Proof.
intros STK sp0 FP ly S W mem md pos lyc Sc Wc memc mdc k HJ.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity.
Qed.

Lemma s28_frame_bounds : forall lyc Sc Wc memc mdc pos,
AR SEGS B lyc Sc Wc memc mdc -> In (4, pos) (frames Sc) ->
4096 <= frame_addr lyc 4 pos /\ frame_addr lyc 4 pos + 1024 <= alloc_ceiling /\
shadow_addr (frame_addr lyc 4 pos) + 128 <= alloc_ceiling /\ in_app (frame_addr lyc 4 pos) 1024.
Proof.
intros lyc Sc Wc memc mdc pos HAR Hin.
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 4 pos HAR Hin) as (H1 & H2 & H3).
assert (E : fs_frame_bytes 4 = 1024) by reflexivity. rewrite E in H2, H3.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
set (F := frame_addr lyc 4 pos) in *.
pose proof (Z.div_mod F 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M.
split; [exact H1|]. split; [exact H2|]. split; [|exact H3]. unfold shadow_addr, SHADOW_OFF. lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   What a recorder call keeps of a boundary state *)
Lemma s28_keep : forall e pos F q c rl tmps Rc Oc qv k kmax nm nmax lyc Sc (W : world SEGS) regsc memc mdc
  STK1 FP1 EV1 ly2 S2 (W2 : world SEGS) mem2 md2,
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc ->
ajournal SEGS B STK1 (vr_s1 e) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 ->
s28_FPrec Oc FP1 ->
vr_frame ly2 W2 mem2 pos F vr_sh2 /\
vr_saved e W2 mem2 /\ vr_spill e W2 mem2 (vr_sl3 F q c) /\
vr_env B W2 mem2 /\
aval_mem (rdW W2 mem2) A_G_QUITTING 4 qv /\
(forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) Oc -> In (p, n) (ablocks B ly2 S2) ->
   0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W memc (p + i)) /\
(forall a, (F <= a < F + 1024) \/ (shadow_addr F <= a < shadow_addr F + 128) -> rdW W2 mem2 a = rdW W memc a).
Proof.
intros e pos F q c rl tmps Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc STK1 FP1 EV1 ly2 S2 W2 mem2 md2
  Hcore HJc HFP.
pose proof Hcore as (HJ & Hkk & Hmeter & Hnm & Hframe & Hrv & Hsaved & Hspill & Henv & Hrec & HdO & Hperm & Hquit).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HJc as (HAR2 & Hlyc & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof Hlyc as (_ & _ & _ & _ & _ & EF & _).
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
destruct (s28_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
pose proof (s28_frames_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hin4.
destruct Hframe as (HFa & Hflag & Hshf).
destruct (s28_frame_bounds lyc Sc W memc mdc pos HAR Hin4) as (BF1 & BF2 & BF3 & BF4).
rewrite <- HFa in BF1, BF2, BF3, BF4.
assert (HOin : forall pn, In pn Oc -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
assert (HFPlo : forall a, inFP FP1 a -> 4096 <= a < alloc_ceiling).
{ intros a Ha. destruct (HFP a Ha) as [[H | H] | (p & n & Hpn & Hr)];
  [unfold A_G_REC, REC_SIZE in H; lia | unfold A_REC_SPILL, SC_SIZE in H; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HOin _ Hpn)) as (_ & H4 & Hc & _). lia. }
assert (Hpg : forall a, s28_recrng a -> in_img SEGS a)
  by (intros a H; exact (proj1 (PROGU a (s28_pg_img a (or_introl H))))).
assert (HFPblk : forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) Oc -> 0 <= i < req_size n ->
  ~ inFP FP1 (p + i)).
{ intros p n i Hpn HnO Hi Hf. destruct (HFP _ Hf) as [H | (b & m & Hbm & Hr)].
  - exact (blk_img SEGS B LAWS _ _ _ _ _ p n (p + i) HAR Hpn ltac:(lia) (Hpg _ H)).
  - assert (Hne : (b, m) <> (p, n)) by (intros E1; rewrite E1 in Hbm; exact (HnO Hbm)).
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ b m p n HAR (HOin _ Hbm) Hpn Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HFPfr : forall a, (F <= a < F + 1024) \/ (shadow_addr F <= a < shadow_addr F + 128) -> ~ inFP FP1 a).
{ intros a Ha Hf. destruct (HFP _ Hf) as [H | (b & m & Hbm & Hr)].
  - destruct Ha as [Ha | Ha].
    + apply (frm_img SEGS B LAWS _ _ _ _ _ 4 pos a HAR Hin4); [rewrite <- HFa; change (fs_frame_bytes 4) with 1024; lia|].
      exact (Hpg _ H).
    + unfold s28_recrng, shadow_addr, SHADOW_OFF, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *.
      pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR (HOin _ Hbm)) as (_ & _ & _ & Happ & _).
    destruct Ha as [Ha | Ha].
    + pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 4 pos HAR (HOin _ Hbm) Hin4) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite <- HFa in Hd.
      change (fs_frame_bytes 4) with 1024 in Hd. lia.
    + unfold shadow_addr, SHADOW_OFF in Ha.
      exact (fshadow_not_app F 128 b (req_size m) a ltac:(lia) ltac:(lia) Happ ltac:(lia) Hr). }
assert (Hspare : forall a, ~ inFP FP1 a -> fp_spares FP1 a).
{ intros a Hn. apply fp_spares_closed; [|exact Hn].
  intros Ho. assert (Hf : inFP FP1 0) by (destruct Ho as (r & Hr & H); exists r; split; assumption).
  pose proof (HFPlo 0 Hf). lia. }
assert (KF : forall a, (F <= a < F + 1024) \/ (shadow_addr F <= a < shadow_addr F + 128) ->
  rdW W2 mem2 a = rdW W memc a).
{ intros a Ha. apply (G4 4 pos a Hin4); [|exact (HFPfr a Ha)].
  unfold frame_rng, in_zr. cbn [fst snd]. rewrite <- HFa.
  change (fs_frame_bytes 4) with 1024. change (1024 / 8) with 128. lia. }
assert (KS : forall a, vr_s1 e <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memc a).
{ intros a Ha. apply G1.
  - lia.
  - lia.
  - intros Hf. pose proof (HFPlo a Hf). lia. }
assert (KB : forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) Oc -> In (p, n) (ablocks B ly2 S2) ->
  0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W memc (p + i))
  by (intros p n i H1 H2 H3 Hi; apply (G2 p n i H1 H3 Hi); exact (HFPblk p n i H1 H2 Hi)).
assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> ~ inFP FP1 a -> rdW W2 mem2 a = rdW W memc a)
  by (intros a H1 H2 H3 H4; apply (G3 a H1 H2 H3); exact (Hspare a H4)).
split.
{ split; [rewrite HFa; unfold frame_addr; rewrite EF; reflexivity|].
  split.
  - assert (Efl : flag_addr ly2 4 pos = flag_addr lyc 4 pos) by (unfold flag_addr; rewrite EF; reflexivity).
    rewrite Efl. rewrite (rdword_ext (rdW W memc) (rdW W2 mem2)); [exact Hflag|].
    intros kk Hkb. apply KF. lia.
  - intros i Hi. rewrite KF by lia. exact (Hshf i Hi). }
split.
{ intros j r Hj. pose proof (Hsaved j r Hj) as Hs.
  assert (Hj13 : (j < 13)%nat)
    by (change 13%nat with (length vr_saved_regs); apply nth_error_Some; rewrite Hj; discriminate).
  apply (aval_mem_agree _ _ _ 8 _ Hs). intros kk Hkb. apply KS. unfold vr_sp0 in *. lia. }
split.
{ unfold vr_spill in *. rewrite Forall_forall in Hspill |- *. intros ov Hov.
  pose proof (Hspill ov Hov) as Hs.
  assert (Hb : 0 <= fst ov <= 72)
    by (unfold vr_sl3 in Hov; cbn in Hov; repeat (destruct Hov as [<- | Hov]; [cbn; lia|]); destruct Hov).
  apply (aval_mem_agree _ _ _ 8 _ Hs). intros kk Hkb. apply KS. unfold vr_sp0 in *. lia. }
split.
{ apply (vr_env_of _ _ _ _ _ HAR2).
  pose proof Henv as (HRO & _).
  intros a Hro Ho He.
  assert (Hi : in_img SEGS a) by exact (vr_roP_img a Hro).
  assert (Hnf : ~ inFP FP1 a).
  { intros Hf. destruct (HFP a Hf) as [H | (p & n & Hpn & Hr)].
    - exact (RPG a (s28_pg_img a (or_introl H)) Hro).
    - exact (blk_img SEGS B LAWS _ _ _ _ _ p n a HAR (HOin _ Hpn) Hr Hi). }
  rewrite (KI a Hi Ho He Hnf). exact (HRO a Hro Ho He). }
split.
{ apply (aval_mem_agree _ _ _ 4 _ Hquit). intros kk Hkb.
  assert (Hq4 : A_G_QUITTING <= A_G_QUITTING + kk < A_G_QUITTING + 4) by (cbn in Hkb; lia).
  destruct (PROGU (A_G_QUITTING + kk) (s28_pg_img _ (or_intror Hq4))) as (Hi & Ho & He).
  apply (KI _ Hi Ho He). intros Hf. destruct (HFP _ Hf) as [H | (p & n & Hpn & Hr)].
  - unfold s28_recrng, A_G_QUITTING, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *. lia.
  - exact (blk_img SEGS B LAWS _ _ _ _ _ p n _ HAR (HOin _ Hpn) Hr Hi). }
split; [exact KB | exact KF].
Qed.

(* the line and the copy after a call that keeps the blocks that are none of the recorder's *)
Lemma q_line_copy_keep : forall e F q c tp lyc Sc (W : world SEGS) memc ly2 S2 (W2 : world SEGS) mem2 Oc,
vr_ent B MT e ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
In (vr_lb e q) (ablocks B lyc Sc) -> ~ In (vr_lb e q) Oc -> In (vr_lb e q) (ablocks B ly2 S2) ->
In (vr_cb e c) (ablocks B lyc Sc) -> ~ In (vr_cb e c) Oc -> In (vr_cb e c) (ablocks B ly2 S2) ->
(forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) Oc -> In (p, n) (ablocks B ly2 S2) ->
   0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W memc (p + i)) ->
(forall a, F <= a < F + 1024 -> rdW W2 mem2 a = rdW W memc a) ->
vr_line B e q W2 mem2 /\ vr_copy B e F c tp W2 mem2.
Proof.
intros e F q c tp lyc Sc W memc ly2 S2 W2 mem2 Oc Hent Hline Hcopy Hlb HlbO Hlb2 Hcb HcbO Hcb2 KB KF.
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (_ & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _).
assert (HL : 0 <= vr_l (e_n e) (e_D e) <= e_n e) by (apply PP8.strnlen_res_le; lia).
assert (HLL : Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e))
  by (apply vr_line_le_l; exact HlenD).
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as [Hrq1 Hrq2].
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [Hrc1 Hrc2].
split.
- destruct Hline as (Hfr & Hs). split; [exact Hfr|].
  apply (astr_atR_agree _ _ q _ (Z.of_nat (length (Verbs.line (e_D e))) + 1) Hs); [lia|].
  intros kk Hkb. apply (KB q (vr_l (e_n e) (e_D e) + 1) kk Hlb HlbO Hlb2). lia.
- destruct Hcopy as (Hfr & Hal & Hlen & Hptr & Hw). split; [exact Hfr|].
  assert (Htk : (length (Verbs.toks (e_D e)) <= 64)%nat) by apply s28_toks_le.
  split; [exact Hal|]. split; [exact Hlen|]. split.
  + intros i p Hi. pose proof (proj1 (nth_error_Some tp i) ltac:(rewrite Hi; discriminate)) as Hi'.
    apply (aval_mem_agree _ _ _ 8 _ (Hptr i p Hi)). intros kk Hkb. apply KF. lia.
  + intros i p w Hi Hwi. destruct (Hw i p w Hi Hwi) as (Hs & Hl8 & Hp1 & Hp2).
    split; [|split; [exact Hl8 | split; [exact Hp1 | exact Hp2]]].
    apply (astr_atR_agree _ _ p _ (Z.of_nat (length w) + 1) Hs); [lia|].
    intros kk Hkb. replace (p + kk) with (c + (p - c + kk)) by lia.
    apply (KB c (Z.of_nat (length (Verbs.line (e_D e))) + 1) (p - c + kk) Hcb HcbO Hcb2). lia.
Qed.

(* the walk's own blocks are none of the recorder's, and live *)
Lemma q_tmps : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc (W : world SEGS) regs mem md,
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
(forall x, In x tmps -> In x (ablocks B lyc Sc)) /\ (forall x, In x tmps -> ~ In x Oc) /\
(forall pn, In pn Oc -> In pn (ablocks B lyc Sc)).
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md
  (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hrec & _ & Hperm & _).
pose proof (proj1 HJ) as HAR.
assert (HND : List.NoDup (Oc ++ tmps ++ e_rest e))
  by (apply (Permutation_NoDup Hperm); exact (RecBLemmas.recb_ablocks_nodup_m B _ _ _ _ _ HAR)).
split; [|split].
- intros x Hx. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right.
  apply in_or_app. left. exact Hx.
- intros x Hx Hx1. exact (nodup_app_disj Oc (tmps ++ e_rest e) HND x Hx1 (in_or_app _ _ _ (or_introl Hx))).
- intros pn Hpn. exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn).
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The boundary after a recorder call that returned a fresh text block, and after one that returned none *)
Lemma s28_post_new : forall e pos F q c tp rl rl' tmps Rc Oc k kmax nm nmax lyc Sc (W : world SEGS) regsc memc mdc
  STK1 FP1 EV1 ly2 S2 (W2 : world SEGS) mem2 md2 regs2 R' O' qt n' k' kmax' nm' nmax',
vr_ent B MT e ->
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc (e_q0 e) k kmax nm nmax lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
ajournal SEGS B STK1 (vr_s1 e) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  ly2 S2 W2 mem2 md2 k' ->
s28_FPrec Oc FP1 ->
k' <= kmax' -> vr_meter MT e S2 k' nm' -> nm' <= nmax' ->
rec_repA B ly2 S2 (rdW W2 mem2) R' O' ->
(forall pn, In pn O' -> In pn Oc \/ ~ In pn (ablocks B lyc Sc)) ->
(forall pn, In pn (ablocks B lyc Sc) -> ~ In pn Oc -> In pn (ablocks B ly2 S2)) ->
(forall pn, In pn (ablocks B ly2 S2) -> (In pn (ablocks B lyc Sc) /\ ~ In pn Oc) \/ In pn O' \/ pn = (qt, n')) ->
In (qt, n') (ablocks B ly2 S2) -> (forall pn, In pn (ablocks B lyc Sc) -> ~ In pn Oc -> pn <> (qt, n')) ->
~ In qt (map fst O') ->
vr_rv regs2 (vr_base B e ++ rl') ->
exists O1, (forall pn, In pn O1 <-> In pn O') /\
vr_core B MT e pos F ((qt, n') :: tmps) vr_sh2 (vr_sl3 F q c) rl' R' O1 (e_q0 e) k' kmax' nm' nmax'
  ly2 S2 W2 regs2 mem2 md2 /\
vr_line B e q W2 mem2 /\ vr_copy B e F c tp W2 mem2.
Proof.
intros e pos F q c tp rl rl' tmps Rc Oc k kmax nm nmax lyc Sc W regsc memc mdc STK1 FP1 EV1 ly2 S2 W2 mem2 md2
  regs2 R' O' qt n' k' kmax' nm' nmax'
  Hent Hcore Hline Hcopy Hlbt Hcbt HJc HJ2 HFP Hkk' Hmeter' Hnm' Hrec' HO'1 HB1 HB2 Hqin Hqnot HqO' Hrv'.
destruct (s28_keep e pos F q c rl tmps Rc Oc (e_q0 e) k kmax nm nmax lyc Sc W regsc memc mdc STK1 FP1 EV1
  ly2 S2 W2 mem2 md2 Hcore HJc HFP) as (Kframe & Ksaved & Kspill & Kenv & Kquit & KB & KF).
pose proof Hcore as (HJ & Hkk & Hmeter & Hnm & Hframe & Hrv & Hsaved & Hspill & Henv & Hrec & HdO & Hperm & Hquit).
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ2) as HAR2.
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & HinD & HnotD & _ & _ & HREC0 & _ & _ & _ & _ & _
  & HpermE & _).
destruct (q_tmps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as (HtB & HtO & HOin).
assert (HO'b : forall pn, In pn O' -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec' Hpn)).
assert (Hq3 : ~ In (qt, n') O')
  by (intros Hq; apply HqO'; apply in_map_iff; exists (qt, n'); split; [reflexivity | exact Hq]).
destruct (vr_perm_new lyc Sc ly2 S2 W2 mem2 md2 Oc tmps (e_rest e) O' qt n' HAR2
  (RecBLemmas.recb_ablocks_nodup_m B _ _ _ _ _ HAR) Hperm HB2 HB1 HO'1 HO'b Hqin Hqnot Hq3) as (O1 & HO1 & HPerm1).
exists O1. split; [exact HO1|].
assert (Hlb2 : In (vr_lb e q) (ablocks B ly2 S2)) by (apply HB1; [apply HtB; exact Hlbt | apply HtO; exact Hlbt]).
assert (Hcb2 : In (vr_cb e c) (ablocks B ly2 S2)) by (apply HB1; [apply HtB; exact Hcbt | apply HtO; exact Hcbt]).
destruct (q_line_copy_keep e F q c tp lyc Sc W memc ly2 S2 W2 mem2 Oc Hent Hline Hcopy (HtB _ Hlbt) (HtO _ Hlbt) Hlb2
  (HtB _ Hcbt) (HtO _ Hcbt) Hcb2 KB (fun a Ha => KF a (or_introl Ha))) as [Hline2 Hcopy2].
split; [|split; [exact Hline2 | exact Hcopy2]].
split; [exact HJ2|]. split; [exact Hkk'|]. split; [exact Hmeter'|]. split; [exact Hnm'|].
split; [exact Kframe|]. split; [exact Hrv'|]. split; [exact Ksaved|]. split; [exact Kspill|].
split; [exact Kenv|].
split.
{ destruct Hrec' as (Q & HA & HOQ). exists Q. split; [exact HA|]. intros pn. rewrite (HO1 pn). exact (HOQ pn). }
split.
{ intros Hd1. apply HO1 in Hd1.
  assert (Hd2 : In (e_data e, Z.max (e_n e) 1) (e_rest e)).
  { apply (Permutation_in _ HpermE) in HinD. apply in_app_or in HinD as [H | H];
    [exfalso; exact (HnotD H) | exact H]. }
  assert (Hd3 : In (e_data e, Z.max (e_n e) 1) (ablocks B lyc Sc)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. right. exact Hd2. }
  destruct (HO'1 _ Hd1) as [H | H]; [exact (HdO H) | exact (H Hd3)]. }
split; [exact HPerm1 | exact Kquit].
Qed.

Lemma s28_post_same : forall e pos F q c tp rl rl' tmps Rc Oc k kmax nm nmax lyc Sc (W : world SEGS) regsc memc mdc
  STK1 FP1 EV1 ly2 S2 (W2 : world SEGS) mem2 md2 regs2 R' O' k' kmax' nm' nmax',
vr_ent B MT e ->
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc (e_q0 e) k kmax nm nmax lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
ajournal SEGS B STK1 (vr_s1 e) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  ly2 S2 W2 mem2 md2 k' ->
s28_FPrec Oc FP1 ->
k' <= kmax' -> vr_meter MT e S2 k' nm' -> nm' <= nmax' ->
rec_repA B ly2 S2 (rdW W2 mem2) R' O' ->
(forall pn, In pn O' -> In pn Oc \/ ~ In pn (ablocks B lyc Sc)) ->
(forall pn, In pn (ablocks B lyc Sc) -> ~ In pn Oc -> In pn (ablocks B ly2 S2)) ->
(forall pn, In pn (ablocks B ly2 S2) -> (In pn (ablocks B lyc Sc) /\ ~ In pn Oc) \/ In pn O') ->
vr_rv regs2 (vr_base B e ++ rl') ->
exists O1, (forall pn, In pn O1 <-> In pn O') /\
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl' R' O1 (e_q0 e) k' kmax' nm' nmax'
  ly2 S2 W2 regs2 mem2 md2 /\
vr_line B e q W2 mem2 /\ vr_copy B e F c tp W2 mem2.
Proof.
intros e pos F q c tp rl rl' tmps Rc Oc k kmax nm nmax lyc Sc W regsc memc mdc STK1 FP1 EV1 ly2 S2 W2 mem2 md2
  regs2 R' O' k' kmax' nm' nmax'
  Hent Hcore Hline Hcopy Hlbt Hcbt HJc HJ2 HFP Hkk' Hmeter' Hnm' Hrec' HO'1 HB1 HB2 Hrv'.
destruct (s28_keep e pos F q c rl tmps Rc Oc (e_q0 e) k kmax nm nmax lyc Sc W regsc memc mdc STK1 FP1 EV1
  ly2 S2 W2 mem2 md2 Hcore HJc HFP) as (Kframe & Ksaved & Kspill & Kenv & Kquit & KB & KF).
pose proof Hcore as (HJ & Hkk & Hmeter & Hnm & Hframe & Hrv & Hsaved & Hspill & Henv & Hrec & HdO & Hperm & Hquit).
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ2) as HAR2.
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & HinD & HnotD & _ & _ & HREC0 & _ & _ & _ & _ & _
  & HpermE & _).
destruct (q_tmps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as (HtB & HtO & HOin).
assert (HO'b : forall pn, In pn O' -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec' Hpn)).
destruct (vr_perm_same lyc Sc ly2 S2 W2 mem2 md2 Oc tmps (e_rest e) O' HAR2
  (RecBLemmas.recb_ablocks_nodup_m B _ _ _ _ _ HAR) Hperm HB2 HB1 HO'1 HO'b) as (O1 & HO1 & HPerm1).
exists O1. split; [exact HO1|].
assert (Hlb2 : In (vr_lb e q) (ablocks B ly2 S2)) by (apply HB1; [apply HtB; exact Hlbt | apply HtO; exact Hlbt]).
assert (Hcb2 : In (vr_cb e c) (ablocks B ly2 S2)) by (apply HB1; [apply HtB; exact Hcbt | apply HtO; exact Hcbt]).
destruct (q_line_copy_keep e F q c tp lyc Sc W memc ly2 S2 W2 mem2 Oc Hent Hline Hcopy (HtB _ Hlbt) (HtO _ Hlbt) Hlb2
  (HtB _ Hcbt) (HtO _ Hcbt) Hcb2 KB (fun a Ha => KF a (or_introl Ha))) as [Hline2 Hcopy2].
split; [|split; [exact Hline2 | exact Hcopy2]].
split; [exact HJ2|]. split; [exact Hkk'|]. split; [exact Hmeter'|]. split; [exact Hnm'|].
split; [exact Kframe|]. split; [exact Hrv'|]. split; [exact Ksaved|]. split; [exact Kspill|].
split; [exact Kenv|].
split.
{ destruct Hrec' as (Q & HA & HOQ). exists Q. split; [exact HA|]. intros pn. rewrite (HO1 pn). exact (HOQ pn). }
split.
{ intros Hd1. apply HO1 in Hd1.
  assert (Hd2 : In (e_data e, Z.max (e_n e) 1) (e_rest e)).
  { apply (Permutation_in _ HpermE) in HinD. apply in_app_or in HinD as [H | H];
    [exfalso; exact (HnotD H) | exact H]. }
  assert (Hd3 : In (e_data e, Z.max (e_n e) 1) (ablocks B lyc Sc)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. right. exact Hd2. }
  destruct (HO'1 _ Hd1) as [H | H]; [exact (HdO H) | exact (H Hd3)]. }
split; [exact HPerm1 | exact Kquit].
Qed.

(* the boundary after a frameless call (is_instance_verb, verb_is): same allocator state, the recorder's statics
   and blocks, the frame and the stack above the call kept *)
Lemma q_keep_na : forall e pos F q c tp tmps rl rl' Rc Oc k kmax nm nmax lyc Sc (W : world SEGS) regs mem md
  STK1 EV1 (W2 : world SEGS) regs2 mem2 md2,
vr_ent B MT e ->
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl Rc Oc (e_q0 e) k kmax nm nmax lyc Sc W regs mem md ->
vr_line B e q W mem -> vr_copy B e F c tp W mem ->
In (vr_lb e q) tmps -> In (vr_cb e c) tmps ->
ajournal SEGS B STK1 (vr_s1 e) [] lyc Sc W mem md [] lyc Sc W2 mem2 md2 EV1 ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W2 mem2 md2 k ->
vr_rv regs2 (vr_base B e ++ rl') ->
vr_core B MT e pos F tmps vr_sh2 (vr_sl3 F q c) rl' Rc Oc (e_q0 e) k kmax nm nmax lyc Sc W2 regs2 mem2 md2 /\
vr_line B e q W2 mem2 /\ vr_copy B e F c tp W2 mem2.
Proof.
intros e pos F q c tp tmps rl rl' Rc Oc k kmax nm nmax lyc Sc W regs mem md STK1 EV1 W2 regs2 mem2 md2
  Hent Hcore Hline Hcopy Hlbt Hcbt HJc HJ2 Hrv'.
destruct (s28_keep e pos F q c rl tmps Rc Oc (e_q0 e) k kmax nm nmax lyc Sc W regs mem md STK1 [] EV1
  lyc Sc W2 mem2 md2 Hcore HJc (s28_FP_nil Oc)) as (Kframe & Ksaved & Kspill & Kenv & Kquit & KB & KF).
pose proof Hcore as (HJ & Hkk & Hmeter & Hnm & Hframe & Hrv & Hsaved & Hspill & Henv & Hrec & HdO & Hperm & Hquit).
pose proof (proj1 HJ) as HAR.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & G3 & _).
destruct (q_tmps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as (HtB & HtO & HOin).
destruct (q_line_copy_keep e F q c tp lyc Sc W mem lyc Sc W2 mem2 Oc Hent Hline Hcopy (HtB _ Hlbt) (HtO _ Hlbt)
  (HtB _ Hlbt) (HtB _ Hcbt) (HtO _ Hcbt) (HtB _ Hcbt) KB (fun a Ha => KF a (or_introl Ha))) as [Hline2 Hcopy2].
split; [|split; [exact Hline2 | exact Hcopy2]].
assert (Hsp0 : forall a, fp_spares [] a)
  by (intros a; split; [intros (r & Hr & _); destruct Hr | exact (inFP_nil a)]).
assert (KI : forall a, inFP cmd_PG a -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. destruct (PROGU a Ha) as (Hi & Ho & He). exact (G3 a Hi Ho He (Hsp0 a)). }
split; [exact HJ2|]. split; [exact Hkk|]. split; [exact Hmeter|]. split; [exact Hnm|].
split; [exact Kframe|]. split; [exact Hrv'|]. split; [exact Ksaved|]. split; [exact Kspill|].
split; [exact Kenv|].
split.
{ apply (rec_repA_agree B _ _ _ _ _ _ Rc Oc Hrec (fun pn _ Hb => Hb)).
  - intros kk Hk. apply KI. apply s28_pg_img. left. left. unfold REC_SIZE in *. lia.
  - intros kk Hk. apply KI. apply s28_pg_img. left. right. unfold SC_SIZE in *. lia.
  - intros [p n] Hpn kk Hk. cbn [fst snd] in *.
    pose proof (HOin _ Hpn) as Hb.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hb) as (_ & _ & _ & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
    apply (G2 p n kk Hb Hb ltac:(lia)). exact (inFP_nil _). }
split; [exact HdO|]. split; [exact Hperm | exact Kquit].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   A string argument that lies in a live block of the walk's own *)
Lemma s28_arg_blk : forall lyc Sc (Wc : world SEGS) memc mdc Oc p n b nb,
AR SEGS B lyc Sc Wc memc mdc -> (forall pn, In pn Oc -> In pn (ablocks B lyc Sc)) ->
In (b, nb) (ablocks B lyc Sc) -> ~ In (b, nb) Oc -> b <= p -> p + n <= b + nb -> 0 <= nb ->
in_blockA (ablocks B lyc Sc) p n /\ Forall (fun qk => iv_apart p n (fst qk) (snd qk)) Oc.
Proof.
intros lyc Sc Wc memc mdc Oc p n b nb HAR HOin Hin HnO H1 H2 H3.
split; [exists b, nb; split; [exact Hin | lia]|].
apply Forall_forall. intros [x m] Hx. cbn [fst snd].
assert (Hne : (x, m) <> (b, nb)) by (intros E1; rewrite E1 in Hx; exact (HnO Hx)).
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ x m b nb HAR (HOin _ Hx) Hin Hne) as Hd.
destruct (al_blocks _ _ LAWS _ _ _ _ _ x m HAR (HOin _ Hx)) as (_ & _ & _ & _ & _ & _ & Hm0).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrm].
pose proof (req_size_pos nb ltac:(lia)) as [_ Hrn].
unfold zdisjoint, iv_apart in *. cbn [fst snd] in Hd. lia.
Qed.

(* the line, as the recorder callees take it (in its strndup block, none of the recorder's) *)
Lemma q_line_arg : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc (W : world SEGS) regs mem md q,
vr_ent B MT e ->
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
In (vr_lb e q) tmps -> vr_line B e q W mem ->
in_blockA (ablocks B lyc Sc) q (Z.of_nat (length (Verbs.line (e_D e))) + 1) /\
Forall (fun qk => iv_apart q (Z.of_nat (length (Verbs.line (e_D e))) + 1) (fst qk) (snd qk)) Oc /\
astr_atR (rdW W mem) q (Verbs.line (e_D e)) /\ Z.of_nat (length (Verbs.line (e_D e))) + 1 <= LMAX + 1.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md q Hent Hcore Hlbt Hline.
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (_ & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _).
destruct (q_tmps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as (HtB & HtO & HOin).
assert (HL : 0 <= vr_l (e_n e) (e_D e) <= e_n e) by (apply PP8.strnlen_res_le; lia).
assert (HLL : Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e))
  by (apply vr_line_le_l; exact HlenD).
destruct (s28_arg_blk lyc Sc W mem md Oc q (Z.of_nat (length (Verbs.line (e_D e))) + 1) q (vr_l (e_n e) (e_D e) + 1)
  (proj1 (proj1 Hcore)) HOin (HtB _ Hlbt) (HtO _ Hlbt) ltac:(lia) ltac:(lia) ltac:(lia)) as [H1 H2].
split; [exact H1|]. split; [exact H2|]. split; [exact (proj2 Hline)|]. unfold LMAX. lia.
Qed.

(* a word of tok[] handed to a recorder function: a C string in the copy block, none of the recorder's *)
Lemma q_tok_arg : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc (W : world SEGS) regs mem md c tp i p w,
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
In (vr_cb e c) tmps -> vr_copy B e F c tp W mem ->
nth_error tp i = Some p -> nth_error (Verbs.toks (e_D e)) i = Some w ->
(in_blockA (ablocks B lyc Sc) p (Z.of_nat (length w) + 1) /\
 Forall (fun qk => iv_apart p (Z.of_nat (length w) + 1) (fst qk) (snd qk)) Oc /\
 astr_atR (rdW W mem) p w /\ Z.of_nat (length w) + 1 <= LMAX + 1) /\
aval_mem (rdW W mem) (F + 32 + 8 * Z.of_nat i) 8 p /\ 4096 <= p /\ p + Z.of_nat (length w) + 1 <= alloc_ceiling /\
p + Z.of_nat (length w) + 1 <= c + Z.of_nat (length (Verbs.line (e_D e))) + 1 /\ c <= p.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md c tp i p w Hcore Hcbt (Hfc & (Hmod & HlenP & Hptr & Hw)) Hp Hwi.
destruct (Hw i p w Hp Hwi) as (A1 & A2 & A3 & A4).
destruct (q_tmps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as (HtB & HtO & HOin).
pose proof (proj1 (proj1 Hcore)) as HAR.
pose proof (HtB _ Hcbt) as Hcb. pose proof (HtO _ Hcbt) as HcbO.
unfold vr_cb in Hcb, HcbO.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn).
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrs.
destruct (s28_arg_blk lyc Sc W mem md Oc p (Z.of_nat (length w) + 1) c (Z.of_nat (length (Verbs.line (e_D e))) + 1)
  HAR HOin Hcb HcbO ltac:(lia) ltac:(lia) ltac:(lia)) as [H1 H2].
split; [split; [exact H1|]; split; [exact H2|]; split; [exact A1 | unfold LMAX; lia]|].
split; [exact (Hptr i p Hp)|]. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The footprint of the entry's frame lies below the allocation ceiling, and the frame chain at a call of this frame *)
Lemma q_fp_low : forall e a, vr_ent B MT e -> inFP (vr_fp e) a -> a < alloc_ceiling.
Proof.
intros e a Hent Ha.
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrec0 & _).
pose proof HPRE0 as (HAR0 & _).
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
destruct Ha as (r & Hr & Hra). unfold vr_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
- unfold VERBS_RECEIVE_PG in Hr. cbn in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn in Hra;
  unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, A_G_QUITTING in Hra; lia.
- apply in_map_iff in Hr as ([p n] & <- & Hpn). cbn in Hra.
  pose proof (rec_repA_in_blocks B _ _ _ _ _ _ Hrec0 Hpn) as Hb.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 Hb) as (_ & _ & Hc & _). lia.
Qed.

(* the frame chain at a call of this frame: s0 holds this function's sp0 (class B, a Theorem Labs lane's S0-SITES.md), whose ra
   and s0 the prologue stored at sp0 - 8 and sp0 - 16 (vr_saved, j = 0 and j = 1): achain_push on afn_pre's chain
   (vr_ent's 1st conjunct), the words from sp0 up kept by the journal (its footprint lies below alloc_ceiling); when
   sp0 >= ly_top - 16 the chain is empty (the S14 lane's vr_achain, verbs_receive_s14_c.v:87, under this file's
   name) *)
Lemma q_achain : forall e pos lyc Sc (W : world SEGS) mem md k,
vr_ent B MT e ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem md k ->
vr_saved e W mem ->
exists ch1, achain lyc (rdW W mem) (vr_s1 e) (vr_sp0 e) ch1.
Proof.
intros e pos lyc Sc W mem md k Hent HJ Hsav.
pose proof Hent as (HPRE & _).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk0 & Hpres & Hch & HQT).
pose proof Hstk0 as (Hal16 & HS0 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
change (spZ (e_regs e)) with (vr_sp0 e) in *.
destruct (s28_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
destruct (Z_lt_le_dec (vr_sp0 e) (ly_top (e_ly e) - 16)) as [Hlt | Hge].
- exists ((vr_sp0 e, raZ (e_regs e), s0Z (e_regs e)) :: e_ch e).
  apply (achain_ly_top (e_ly e) lyc); [exact Etop|].
  apply (achain_push (e_ly e) (rdW (e_W e) (e_mem e)) (rdW W mem) (vr_sp0 e) (s0Z (e_regs e)) (raZ (e_regs e)) (e_ch e)
    (vr_s1 e)).
  + exact Hch.
  + lia.
  + intros a Ha. apply F1; [lia | lia |]. intros Hf. pose proof (q_fp_low e a Hent Hf). lia.
  + apply q_rdword_of_aval; [|unfold raZ; pose proof (bv_unsigned_in_range 64 (getr (e_regs e) 1)) as R;
      change (bv_modulus 64) with (2 ^ 64) in R; exact R].
    pose proof (Hsav 0%nat 1 eq_refl) as H. replace (vr_sp0 e - 8) with (vr_sp0 e - 8 - 8 * Z.of_nat 0) by lia. exact H.
  + apply q_rdword_of_aval; [|unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr (e_regs e) 8)) as R;
      change (bv_modulus 64) with (2 ^ 64) in R; exact R].
    pose proof (Hsav 1%nat 8 eq_refl) as H. replace (vr_sp0 e - 16) with (vr_sp0 e - 8 - 8 * Z.of_nat 1) by lia. exact H.
  + exact Hra4.
  + lia.
  + pose proof (Z.div_mod (vr_sp0 e) 16 ltac:(lia)) as Dm. rewrite Hal16 in Dm.
    pose proof (Z.div_mod (vr_sp0 e) 8 ltac:(lia)) as Dm8. pose proof (Z.mod_pos_bound (vr_sp0 e) 8 ltac:(lia)).
    assert (Hq : vr_sp0 e / 8 = 2 * (vr_sp0 e / 16)) by lia. lia.
  + exact Hlt.
  + lia.
- exists []. left. split; [right; left; rewrite Etop; exact Hge | reflexivity].
Qed.

(* a recorder callee from a boundary state, through PaFx's cl_callS_wideF (every recorder callee is printf-reaching
   since statement pass 4: its post is apost_baseF, it returns at some FP state fx' with fxrel fx fx'); its frame
   chain is q_achain's *)
Lemma q_rcallF : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc (W : world SEGS) regs mem md
  AF STK1 FP1 EV1 retk (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
vr_ent B MT e ->
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
getr regs 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK ->
s28_FPrec Oc FP1 ->
(forall ch, afn_pre SEGS B STK1 lyc Sc W regs mem md ch ->
  SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md) (apost_baseF SEGS B STK1 FP1 regs lyc Sc W mem md EV1 K)) ->
SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md)
(fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2, fxrel fx fx' /\
  c2 = mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 /\
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
    ly2 S2 W2 mem2 md2 (k + EV1) /\
  ajournal SEGS B STK1 (vr_s1 e) FP1 lyc Sc W mem md [] ly2 S2 W2 mem2 md2 EV1 /\
  aregs_preserved regs regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md AF STK1 FP1 EV1 retk K
  Hent Hcore R1 Hretk Hretk2 HST0 HSTK1 HFP CALL.
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & Hsaved & _ & _ & Hrec & _ & Hperm & _).
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpermE & _).
pose proof HPRE0 as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
pose proof (proj1 HJ) as HAR.
destruct (s28_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
assert (R2 : getr regs 2 = w64 (vr_s1 e)) by (apply (vr_rv_get regs _ 2 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R3 : getr regs 3 = w64 (as_gp B)) by (apply (vr_rv_get regs _ 3 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R4 : getr regs 4 = w64 (as_tp B)) by (apply (vr_rv_get regs _ 4 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R8 : getr regs 8 = w64 (vr_sp0 e)) by (apply (vr_rv_get regs _ 8 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (Hsp1 : spZ regs = vr_s1 e) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regs = vr_sp0 e) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
destruct (q_achain e pos lyc Sc W mem md k Hent HJ Hsaved) as (ch1 & Hch1).
assert (HOin : forall pn, In pn Oc -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
assert (HND : List.NoDup (Oc ++ tmps ++ e_rest e))
  by (apply (Permutation_NoDup Hperm); exact (RecBLemmas.recb_ablocks_nodup_m B _ _ _ _ _ HAR)).
assert (HFPlo : forall a, inFP FP1 a -> a < alloc_ceiling).
{ intros a Ha. destruct (HFP a Ha) as [[G|G]|(p & n & Hpn & Hr)];
  [unfold A_G_REC, REC_SIZE in G; lia | unfold A_REC_SPILL, SC_SIZE in G; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HOin _ Hpn)) as (_ & _ & Hc & _). lia. }
unfold cfg_at, w64.
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS W regs mem _ VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e)
    (e_md e) [(4, pos)] lyc Sc md k STK1 FP1 EV1 (vr_s1 e - vr_sp0 e) (Z_to_bv 64 (BASE + retk)) ch1 K HJ).
  - rewrite Hsp1. lia.
  - exact Hs1o.
  - lia.
  - exact HST0.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; lia.
  - rewrite unsigned_lit_small by lia. lia.
  - replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) by lia. rewrite Hs0. exact Hch1.
  - intros HPRE1. eapply SRr_mono; [exact (CALL ch1 HPRE1)|].
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & HR' & HC' & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. rewrite R1. split; [reflexivity|].
    split; [exact HR'|]. split; [exact HC'|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. destruct (HFP a Ha) as [[G|G]|(p & n & Hpn & Hr)].
    + right; right; right; right; left. split; [exists (A_G_REC, A_G_REC + REC_SIZE); split;
        [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; left; reflexivity | exact G]|].
      split; [|exact (proj1 (PROGU a (s28_pg_img a (or_introl (or_introl G)))))].
      rewrite (YF0m.ts_prog _ HB). unfold YF0m.TFIB_PROG_STATIC. apply Exists_cons_hd.
      unfold in_zr, A_G_REC, REC_SIZE in *. cbn [fst snd]. lia.
    + right; right; right; right; left. split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split;
        [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; right; left; reflexivity | exact G]|].
      split; [|exact (proj1 (PROGU a (s28_pg_img a (or_introl (or_intror G)))))].
      rewrite (YF0m.ts_prog _ HB). unfold YF0m.TFIB_PROG_STATIC. apply Exists_cons_tl. apply Exists_cons_hd.
      unfold in_zr, A_REC_SPILL, SC_SIZE in *. cbn [fst snd]. lia.
    + destruct (in_dec pn_eq_dec (p, n) (ablocks B (e_ly e) (e_S e))) as [Hold | Hnew].
      * (* a block the entry had: the recorder's at the entry, so in the footprint *)
        right; left. split; [|exists p, n; split; [exact (HOin _ Hpn) | exact Hr]].
        assert (HpO : In (p, n) (e_O e)).
        { apply (Permutation_in _ HpermE) in Hold. apply in_app_or in Hold as [H|H]; [exact H|].
          exfalso. exact (nodup_app_disj Oc (tmps ++ e_rest e) HND (p, n) Hpn (in_or_app _ _ _ (or_intror H))). }
        exists (p, p + req_size n). split; [|cbn; lia].
        unfold vr_fp. apply in_or_app. right. unfold ablocks_fp.
        exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (p, n) HpO).
      * right; right; left. exists p, n. split; [exact (HOin _ Hpn)|]. split; [exact Hnew | exact Hr].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (HFPlo a Ha). lia. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJc & HP & HK).
exists fx', ly2, S2, regs2, mem2, md2. split; [exact Hfx|]. split; [reflexivity|]. split; [exact HJ2|].
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
split; [exact HJc|]. split; [exact HP | exact HK].
Qed.

(* a frameless callee from a boundary state, through cl_callS_na *)
Lemma q_na_call : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc (W : world SEGS) regs mem md
  AF STK1 EV1 retk (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
vr_sp0 e mod 16 = 0 ->
getr regs 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK ->
(afn_pre_na SEGS B STK1 lyc Sc W regs mem md ->
  SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md) (apost_base SEGS B STK1 [] regs lyc Sc W mem md EV1 K)) ->
SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 /\
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
    ly2 S2 W2 mem2 md2 (k + EV1) /\
  ajournal SEGS B STK1 (vr_s1 e) [] lyc Sc W mem md [] ly2 S2 W2 mem2 md2 EV1 /\
  aregs_preserved regs regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md AF STK1 EV1 retk K
  Hcore Hal16 R1 Hretk Hretk2 HST0 HSTK1 CALL.
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & _).
destruct (s28_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
assert (R2 : getr regs 2 = w64 (vr_s1 e)) by (apply (vr_rv_get regs _ 2 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R3 : getr regs 3 = w64 (as_gp B)) by (apply (vr_rv_get regs _ 3 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R4 : getr regs 4 = w64 (as_tp B)) by (apply (vr_rv_get regs _ 4 _ Hrv); apply in_or_app; left; cbn; tauto).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
assert (Hsp1 : spZ regs = vr_s1 e) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
unfold cfg_at, w64.
eapply SRr_mono.
{ eapply (cl_callS_na B LAWS W regs mem _ VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e)
    (e_md e) [(4, pos)] lyc Sc md k STK1 [] EV1 (vr_s1 e - vr_sp0 e) (Z_to_bv 64 (BASE + retk)) K HJ).
  - rewrite Hsp1. lia.
  - exact Hs1o.
  - lia.
  - exact HST0.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; lia.
  - rewrite unsigned_lit_small by lia. lia.
  - intros HPRE1. eapply SRr_mono; [exact (CALL HPRE1)|].
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. rewrite R1. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|].
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
split; [exact HJc|]. split; [exact HP | exact HK].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The live bytes at a boundary of the scan's routes: the entry's, the recorder's, and the walk's own blocks *)
Lemma q_live : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc (W : world SEGS) regs mem md L1 nc,
vr_ent B MT e ->
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
(length (r_calls Rc) <= nc)%nat ->
(6 * Z.of_nat nc + 8) * (LMAX + 2) + bsum tmps + L1 <= LIVE_VERBS_RECEIVE ->
blocks_bytes Sc + L1 <= LIVE_MAX.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md L1 nc Hent Hcore Hnc HL.
pose proof Hcore as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hrec & _ & Hperm & _).
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpermE & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & Hlive & _).
pose proof (vr_live_le SEGS B LAWS (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) lyc Sc W mem md (rdW W mem) Rc
  (e_O e) Oc tmps (e_rest e) (proj1 HPRE0) (proj1 HJ) HpermE Hperm Hrec) as HLL.
assert (Hm : (6 * Z.of_nat (length (r_calls Rc)) + 8) * (LMAX + 2) <= (6 * Z.of_nat nc + 8) * (LMAX + 2))
  by (apply Z.mul_le_mono_nonneg_r; [unfold LMAX; lia | lia]).
unfold LMAX in *. lia.
Qed.

(* the events at a boundary leave room for a callee's *)
Lemma q_nev : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc (W : world SEGS) regs mem md X,
vr_ent B MT e ->
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
kmax + X <= ev_vr (e_R e) (e_D e) ->
st_nev Sc + X <= EV_MAX.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md X Hent Hcore HX.
pose proof Hcore as (HJ & Hkk & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & Hev & _).
lia.
Qed.

(* the recorder's code is an int *)
Lemma q_code_range : forall ly S rd R O, rec_repA B ly S rd R O -> -2^31 <= r_code R < 2^31.
Proof. intros ly S rd R O (Q & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HC & _) & _) & _). exact HC. Qed.

End e.

(* ---------------------------------------------------------------------------------------------------------------
   The symbolic states the legs seed: the registers as atoms; B's spill slots s1+8 (shadow_addr F), s1+16 and s1+24
   (F), s1+32 (shadow_addr F + 4), s1+40 (tok = F + 32) and s1+56 (line) as one region; the word array's slots
   tok[1] = F+40 and tok[2] = F+48 (B reloads tok into s3 from s1+40 and reads 8(s3), 16(s3)). Extra atoms:
   32 = line block, 33 = frame, 34 = tok[1], 35 = tok[2], 36 = shadow_addr F. *)
Definition q_rsp : YP09.region := YP09.mkRegion (Some 9%nat) 8 64 8 8
  [YP09.mkChunk 8 (CVal 8 (SOff 36 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 33 0));
   YP09.mkChunk 32 (CVal 8 (SOff 36 4)); YP09.mkChunk 40 (CVal 8 (SOff 33 32)); YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition q_rtok1 : YP09.region := YP09.mkRegion (Some 33%nat) 40 48 40 40
  [YP09.mkChunk 40 (CVal 8 (SOff 34 0))].
Definition q_rtok2 : YP09.region := YP09.mkRegion (Some 33%nat) 40 56 40 40
  [YP09.mkChunk 40 (CVal 8 (SOff 34 0)); YP09.mkChunk 48 (CVal 8 (SOff 35 0))].
Definition q_ss (pc : Z) (rs : smem) : sstate := mkSS pc sr_atoms rs None (mkFacts [] [] []).
Definition q_extra (q F p1 p2 : Z) : list word := map (Z_to_bv 64) [q; F; p1; p2; shadow_addr F].

Lemma q_ro_rsp : Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) [q_rsp].
Proof. repeat constructor; cbn; lia. Qed.
Lemma q_ro_rt1 : Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) [q_rsp; q_rtok1].
Proof. repeat constructor; cbn; lia. Qed.
Lemma q_ro_rt2 : Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) [q_rsp; q_rtok2].
Proof. repeat constructor; cbn; lia. Qed.

(* the shadow word of a frame below the ceiling is a small address *)
Lemma q_shadow_range : forall F, 4096 <= F -> F + 1024 <= alloc_ceiling ->
0 <= shadow_addr F /\ shadow_addr F + 128 <= 2 ^ 47.
Proof.
intros F H1 H2. pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
pose proof (Z.div_mod F 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M.
unfold shadow_addr, SHADOW_OFF. lia.
Qed.

(* B's six spill slots the legs read, as the boundary's vr_sl3 names them *)
Definition q_sl (F q : Z) : list (Z * Z) :=
[(8, shadow_addr F); (16, F); (24, F); (32, shadow_addr F + 4); (40, F + 32); (56, q)].
Lemma q_sl_of_sl3 : forall F q c o v, In (o, v) (q_sl F q) -> In (o, v) (vr_sl3 F q c).
Proof. intros F q c o v H. unfold q_sl, vr_sl3 in *. cbn in H |- *. tauto. Qed.

Lemma q_seedS : forall (W : world SEGS) (regs : bvmap 5 word) mem pc s1 q F p1 p2,
getr regs (Z_to_bv 5 9) = w64 s1 -> alloc_ceiling <= s1 -> s1 + 64 <= 2 ^ 47 ->
0 <= q < 2 ^ 64 -> 4096 <= F -> F + 1024 <= alloc_ceiling -> 0 <= p1 < 2 ^ 64 -> 0 <= p2 < 2 ^ 64 ->
(forall o v, In (o, v) (q_sl F q) -> aval_mem (rdW W mem) (s1 + o) 8 v) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (q_extra q F p1 p2))) (q_ss pc [q_rsp])
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc s1 q F p1 p2 H9 Ha Hb Hq HF1 HF2 Hp1 Hp2 MS.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
destruct (q_shadow_range F HF1 HF2) as [HS1 HS2].
set (E := Eimg (Ereg regs (q_extra q F p1 p2))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (q_extra q F p1 p2) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (U9 : bv_unsigned (ew E 9) = s1).
{ rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (XV : forall (j : nat) v off, (j < 5)%nat -> nth j (q_extra q F p1 p2) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> sv_denot E (SOff (32 + j) off) = Z_to_bv 64 (v + off)).
{ intros j v off Hj Hv Hr. cbn [sv_denot]. rewrite (EX j Hj), Hv, unsigned_lit_small by exact Hr. reflexivity. }
assert (M8 := MS 8 _ ltac:(unfold q_sl; cbn; tauto)). assert (M16 := MS 16 _ ltac:(unfold q_sl; cbn; tauto)).
assert (M24 := MS 24 _ ltac:(unfold q_sl; cbn; tauto)). assert (M32 := MS 32 _ ltac:(unfold q_sl; cbn; tauto)).
assert (M40 := MS 40 _ ltac:(unfold q_sl; cbn; tauto)). assert (M56 := MS 56 _ ltac:(unfold q_sl; cbn; tauto)).
rewrite restrict_mkst_fx. unfold q_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, q_rsp;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ s1 8 8 (SOff (32 + 4) 0) (shadow_addr F));
    [rewrite (XV 4%nat (shadow_addr F) 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M8].
  + apply (chunk_ok_val SEGS E _ s1 16 8 (SOff (32 + 1) 0) F);
    [rewrite (XV 1%nat F 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M16].
  + apply (chunk_ok_val SEGS E _ s1 24 8 (SOff (32 + 1) 0) F);
    [rewrite (XV 1%nat F 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M24].
  + apply (chunk_ok_val SEGS E _ s1 32 8 (SOff (32 + 4) 4) (shadow_addr F + 4));
    [rewrite (XV 4%nat (shadow_addr F) 4) by (reflexivity || lia); reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M32].
  + apply (chunk_ok_val SEGS E _ s1 40 8 (SOff (32 + 1) 32) (F + 32));
    [rewrite (XV 1%nat F 32) by (reflexivity || lia); reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M40].
  + apply (chunk_ok_val SEGS E _ s1 56 8 (SOff (32 + 0) 0) q);
    [rewrite (XV 0%nat q 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M56].
- apply pairwise_disjoint_of_extents. unfold q_rsp, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite U9.
  cbn [zpairwise_disjoint zall_disjoint]. tauto.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

Lemma q_seedT1 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc s1 q F p1 p2,
getr regs (Z_to_bv 5 9) = w64 s1 -> alloc_ceiling <= s1 -> s1 + 64 <= 2 ^ 47 ->
0 <= q < 2 ^ 64 -> 4096 <= F -> F + 1024 <= alloc_ceiling -> 0 <= p1 < 2 ^ 64 -> 0 <= p2 < 2 ^ 64 ->
(forall o v, In (o, v) (q_sl F q) -> aval_mem (rdW W mem) (s1 + o) 8 v) ->
aval_mem (rdW W mem) (F + 40) 8 p1 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (q_extra q F p1 p2))) (q_ss pc [q_rsp; q_rtok1])
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc s1 q F p1 p2 H9 Ha Hb Hq HF1 HF2 Hp1 Hp2 MS M40t.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
destruct (q_shadow_range F HF1 HF2) as [HS1 HS2].
set (E := Eimg (Ereg regs (q_extra q F p1 p2))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (q_extra q F p1 p2) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (U9 : bv_unsigned (ew E 9) = s1).
{ rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew E 33) = F).
{ change 33%nat with (32 + 1)%nat. rewrite (EX 1%nat ltac:(lia)). cbn [q_extra map nth].
  apply unsigned_lit_small. lia. }
assert (XV : forall (j : nat) v off, (j < 5)%nat -> nth j (q_extra q F p1 p2) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> sv_denot E (SOff (32 + j) off) = Z_to_bv 64 (v + off)).
{ intros j v off Hj Hv Hr. cbn [sv_denot]. rewrite (EX j Hj), Hv, unsigned_lit_small by exact Hr. reflexivity. }
assert (M8 := MS 8 _ ltac:(unfold q_sl; cbn; tauto)). assert (M16 := MS 16 _ ltac:(unfold q_sl; cbn; tauto)).
assert (M24 := MS 24 _ ltac:(unfold q_sl; cbn; tauto)). assert (M32 := MS 32 _ ltac:(unfold q_sl; cbn; tauto)).
assert (M40 := MS 40 _ ltac:(unfold q_sl; cbn; tauto)). assert (M56 := MS 56 _ ltac:(unfold q_sl; cbn; tauto)).
rewrite restrict_mkst_fx. unfold q_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, q_rsp, q_rtok1;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ s1 8 8 (SOff (32 + 4) 0) (shadow_addr F));
      [rewrite (XV 4%nat (shadow_addr F) 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M8].
    * apply (chunk_ok_val SEGS E _ s1 16 8 (SOff (32 + 1) 0) F);
      [rewrite (XV 1%nat F 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M16].
    * apply (chunk_ok_val SEGS E _ s1 24 8 (SOff (32 + 1) 0) F);
      [rewrite (XV 1%nat F 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M24].
    * apply (chunk_ok_val SEGS E _ s1 32 8 (SOff (32 + 4) 4) (shadow_addr F + 4));
      [rewrite (XV 4%nat (shadow_addr F) 4) by (reflexivity || lia); reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M32].
    * apply (chunk_ok_val SEGS E _ s1 40 8 (SOff (32 + 1) 32) (F + 32));
      [rewrite (XV 1%nat F 32) by (reflexivity || lia); reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M40].
    * apply (chunk_ok_val SEGS E _ s1 56 8 (SOff (32 + 0) 0) q);
      [rewrite (XV 0%nat q 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M56].
  + rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ F 40 8 (SOff (32 + 2) 0) p1);
      [rewrite (XV 2%nat p1 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M40t].
- apply pairwise_disjoint_of_extents. unfold q_rsp, q_rtok1, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite U9, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

Lemma q_seedT2 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc s1 q F p1 p2,
getr regs (Z_to_bv 5 9) = w64 s1 -> alloc_ceiling <= s1 -> s1 + 64 <= 2 ^ 47 ->
0 <= q < 2 ^ 64 -> 4096 <= F -> F + 1024 <= alloc_ceiling -> 0 <= p1 < 2 ^ 64 -> 0 <= p2 < 2 ^ 64 ->
(forall o v, In (o, v) (q_sl F q) -> aval_mem (rdW W mem) (s1 + o) 8 v) ->
aval_mem (rdW W mem) (F + 40) 8 p1 -> aval_mem (rdW W mem) (F + 48) 8 p2 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (q_extra q F p1 p2))) (q_ss pc [q_rsp; q_rtok2])
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc s1 q F p1 p2 H9 Ha Hb Hq HF1 HF2 Hp1 Hp2 MS M40t M48t.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
destruct (q_shadow_range F HF1 HF2) as [HS1 HS2].
set (E := Eimg (Ereg regs (q_extra q F p1 p2))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (q_extra q F p1 p2) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (U9 : bv_unsigned (ew E 9) = s1).
{ rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew E 33) = F).
{ change 33%nat with (32 + 1)%nat. rewrite (EX 1%nat ltac:(lia)). cbn [q_extra map nth].
  apply unsigned_lit_small. lia. }
assert (XV : forall (j : nat) v off, (j < 5)%nat -> nth j (q_extra q F p1 p2) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> sv_denot E (SOff (32 + j) off) = Z_to_bv 64 (v + off)).
{ intros j v off Hj Hv Hr. cbn [sv_denot]. rewrite (EX j Hj), Hv, unsigned_lit_small by exact Hr. reflexivity. }
assert (M8 := MS 8 _ ltac:(unfold q_sl; cbn; tauto)). assert (M16 := MS 16 _ ltac:(unfold q_sl; cbn; tauto)).
assert (M24 := MS 24 _ ltac:(unfold q_sl; cbn; tauto)). assert (M32 := MS 32 _ ltac:(unfold q_sl; cbn; tauto)).
assert (M40 := MS 40 _ ltac:(unfold q_sl; cbn; tauto)). assert (M56 := MS 56 _ ltac:(unfold q_sl; cbn; tauto)).
rewrite restrict_mkst_fx. unfold q_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, q_rsp, q_rtok2;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ s1 8 8 (SOff (32 + 4) 0) (shadow_addr F));
      [rewrite (XV 4%nat (shadow_addr F) 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M8].
    * apply (chunk_ok_val SEGS E _ s1 16 8 (SOff (32 + 1) 0) F);
      [rewrite (XV 1%nat F 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M16].
    * apply (chunk_ok_val SEGS E _ s1 24 8 (SOff (32 + 1) 0) F);
      [rewrite (XV 1%nat F 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M24].
    * apply (chunk_ok_val SEGS E _ s1 32 8 (SOff (32 + 4) 4) (shadow_addr F + 4));
      [rewrite (XV 4%nat (shadow_addr F) 4) by (reflexivity || lia); reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M32].
    * apply (chunk_ok_val SEGS E _ s1 40 8 (SOff (32 + 1) 32) (F + 32));
      [rewrite (XV 1%nat F 32) by (reflexivity || lia); reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M40].
    * apply (chunk_ok_val SEGS E _ s1 56 8 (SOff (32 + 0) 0) q);
      [rewrite (XV 0%nat q 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M56].
  + rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ F 40 8 (SOff (32 + 2) 0) p1);
      [rewrite (XV 2%nat p1 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M40t].
    * apply (chunk_ok_val SEGS E _ F 48 8 (SOff (32 + 3) 0) p2);
      [rewrite (XV 3%nat p2 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply q_val_mem_of_aval; exact M48t].
- apply pairwise_disjoint_of_extents. unfold q_rsp, q_rtok2, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite U9, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

(* the state at a return pc, from the registers alone *)
Lemma q_seed0 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (q_ss_ret pc)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx. unfold q_ss_ret. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.

End f.
End d.
