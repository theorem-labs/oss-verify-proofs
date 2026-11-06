(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: helpers of segment S06 (DISP, 0x8d6fc-0x8d8a4) of the walk of verbs_receive
   on the ASan build of plugin-hostd/fuzz_command (interface lib/A/Prog/verbs_receive_iface.v): the order of the
   dispatch's tests (v6_tests, the plain route function lib/Prog/verbs_receive_route.v as a cascade), the state
   between two tests (v6_dm), the carry of a boundary state across a memory that changed only in the stack window
   below s1 (v6_carry), the symbolic state a test starts from (v6_seed), the literals the tests read and the steps
   through the comparison entries (the runtime contracts through PaArt.aj_art_at). All names carry the prefix v6_ so
   that this file can be imported next to the other segments' files. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require strcspn_c VerbsFacts verbs_receive_route verbs_receive_pre.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString RtNumber RtAlloc04 RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verb_is_c verbs_receive_c verbs_receive_iface verbs_receive_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.
Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.
Module PVF := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.VerbsFacts.
Module PCs := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strcspn_c.
Module PVP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_pre.
Ltac v6_lia2 := first [lia | (split; lia) | (intros [? ?]; lia) | (split; [lia | split; lia])].

(* ---------------------------------------------------------------------------------------------------------------
   The dispatch's tests, in the order of the code (L/src/verbs.c:124-215 inlined, the listing 0x8d718-0x8d8a4):
   16 comparisons of the first word with a literal, the inline verb_is(remove) and verb_is(quit). The route the
   model takes (lib/Prog/verbs_receive_route.v route) is the first test that holds, or route_tail. *)
Definition v6_tests : list ((list byte -> bool) * VRR.vroute) :=
[(fun v => PV.list_eqb v PV.Lit.verb_add, VRR.RAdd);
 (fun v => PV.list_eqb v PV.Lit.verb_descriptor_get, VRR.RDget);
 (fun v => PV.list_eqb v PV.Lit.verb_panel_get, VRR.RPget);
 (fun v => PV.verb_is_m v PV.Lit.fmt_remove, VRR.RRemove);
 (fun v => PV.list_eqb v PV.Lit.verb_worker_list, VRR.RWlist);
 (fun v => PV.list_eqb v PV.Lit.verb_instance_info, VRR.RIinfo);
 (fun v => PV.list_eqb v PV.Lit.verb_supervisor_reset, VRR.RReset);
 (fun v => PV.list_eqb v PV.Lit.verb_quarantine_clear, VRR.RQclear);
 (fun v => PV.list_eqb v PV.Lit.verb_policy_set, VRR.RPolicy);
 (fun v => PV.list_eqb v PV.Lit.verb_lv2_worker_set, VRR.RLv2);
 (fun v => PV.list_eqb v PV.Lit.verb_pool_config, VRR.RPool);
 (fun v => PV.list_eqb v PV.Lit.verb_worker_env, VRR.REnv);
 (fun v => PV.list_eqb v PV.Lit.verb_chain, VRR.RChain);
 (fun v => PV.list_eqb v PV.Lit.verb_chain_clear, VRR.RChclear);
 (fun v => PV.list_eqb v PV.Lit.verb_pin_set, VRR.RPinset);
 (fun v => PV.list_eqb v PV.Lit.verb_pin_accept, VRR.RPinacc);
 (fun v => PV.list_eqb v PV.Lit.verb_pin_clear, VRR.RPinclr);
 (fun v => PV.verb_is_m v PV.Lit.fmt_quit, VRR.RQuit)].
Definition v6_casc (l : list ((list byte -> bool) * VRR.vroute)) (v : list byte) (args : list (list byte)) : VRR.vroute :=
fold_right (fun (tr : (list byte -> bool) * VRR.vroute) (acc : VRR.vroute) => if fst tr v then snd tr else acc)
  (VRR.route_tail v args) l.
Lemma v6_route_casc : forall v args, VRR.route (v :: args) = v6_casc v6_tests v args.
Proof. intros v args. reflexivity. Qed.
Lemma v6_route_casc_ne : forall tk, tk <> [] -> VRR.route tk = v6_casc v6_tests (hd [] tk) (tl tk).
Proof. intros [|v args] H; [exfalso; exact (H eq_refl) | exact (v6_route_casc v args)]. Qed.
Lemma v6_casc_cons : forall t r l v args,
v6_casc ((t, r) :: l) v args = if t v then r else v6_casc l v args.
Proof. reflexivity. Qed.
Lemma v6_casc_nil : forall v args, v6_casc [] v args = VRR.route_tail v args.
Proof. reflexivity. Qed.
Lemma v6_skipn_S : forall {A} (xs : list A) i t l, skipn i xs = t :: l -> skipn (S i) xs = l.
Proof.
intros A xs. induction xs as [|x xs IH]; intros i t l H; destruct i as [|i]; cbn in H |- *; try discriminate.
- injection H as _ ->. reflexivity.
- exact (IH i t l H).
Qed.
(* the dispatch at test i: the test holds and the route is its own, or it fails and the route is that of the rest *)
Lemma v6_hit : forall i t r l tk, skipn i v6_tests = (t, r) :: l ->
VRR.route tk = v6_casc (skipn i v6_tests) (hd [] tk) (tl tk) -> t (hd [] tk) = true -> VRR.route tk = r.
Proof. intros i t r l tk Hs Hr Ht. rewrite Hr, Hs, v6_casc_cons, Ht. reflexivity. Qed.
Lemma v6_miss : forall i t r l tk, skipn i v6_tests = (t, r) :: l ->
VRR.route tk = v6_casc (skipn i v6_tests) (hd [] tk) (tl tk) -> t (hd [] tk) = false ->
VRR.route tk = v6_casc (skipn (S i) v6_tests) (hd [] tk) (tl tk).
Proof. intros i t r l tk Hs Hr Ht. rewrite Hr, Hs, v6_casc_cons, Ht, (v6_skipn_S _ _ _ _ Hs). reflexivity. Qed.
(* the routes behind the last test all start at 0x8dd70 and reload s2, s4, s11 *)
Lemma v6_tail_pc : forall v args, vr_route_pc (VRR.route_tail v args) = 0x8dd70 /\ vr_rgroup (VRR.route_tail v args) = 2%nat.
Proof.
intros v args. unfold VRR.route_tail, VRR.route_conn, VRR.route_cd.
destruct (PV.ledger_of v PV.Lit.instance_info_verbs); [split; reflexivity|].
destruct args as [|a [|b [|c rest]]]; cbn; try (split; reflexivity);
repeat match goal with |- context [if ?x then _ else _] => destruct x end; split; reflexivity.
Qed.

(* the literals the comparison entries read (all of them in CmdRo.v's cmd_ro_bytes) *)
Lemma v6_ro_lits : forall rd, cmd_ro_ok rd ->
abytes_atR rd 0x224c0 RO_lit_224c0 /\ abytes_atR rd 0x22560 RO_lit_22560 /\ abytes_atR rd 0x22580 RO_lit_22580 /\
abytes_atR rd 0x225a0 RO_lit_225a0 /\ abytes_atR rd 0x225c0 RO_lit_225c0 /\ abytes_atR rd 0x225e0 RO_lit_225e0 /\
abytes_atR rd 0x22600 RO_lit_22600 /\ abytes_atR rd 0x22620 RO_lit_22620 /\ abytes_atR rd 0x22680 RO_lit_22680 /\
abytes_atR rd 0x226c0 RO_lit_226c0 /\ abytes_atR rd 0x226e0 RO_lit_226e0 /\ abytes_atR rd 0x22700 RO_lit_22700 /\
abytes_atR rd 0x22720 RO_lit_22720 /\ abytes_atR rd 0x22740 RO_lit_22740 /\ abytes_atR rd 0x22760 RO_lit_22760 /\
abytes_atR rd 0x22780 RO_lit_22780 /\ abytes_atR rd 0x227a0 RO_lit_227a0 /\ abytes_atR rd 0x227c0 RO_lit_227c0 /\
abytes_atR rd 0x227e0 RO_lit_227e0.
Proof. intros rd [H _]. unfold cmd_ro_bytes in H. decompose [and] H. repeat split; assumption. Qed.

(* cmd_ro_ok reads only the low image *)
Lemma v6_abytes_low : forall rd rd' a l, abytes_atR rd a l ->
(forall x, 0 <= x < 0x606000 -> rd' x = rd x) -> ((0 <=? a) && (a + Z.of_nat (length l) <=? 0x606000))%bool = true ->
abytes_atR rd' a l.
Proof.
intros rd rd' a l H K Hb i Hi. apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
rewrite K by lia. exact (H i Hi).
Qed.
Lemma v6_ro_ok_low : forall rd rd', cmd_ro_ok rd -> (forall x, 0 <= x < 0x606000 -> rd' x = rd x) -> cmd_ro_ok rd'.
Proof.
intros rd rd' [Hb Ht] K. split.
- unfold cmd_ro_bytes in *.
  repeat match goal with H : _ /\ _ |- _ /\ _ => let H1 := fresh "H1" in destruct H as [H1 H];
    split; [apply (v6_abytes_low rd rd' _ _ H1 K); vm_compute; reflexivity | clear H1] end.
  match goal with H : abytes_atR rd _ _ |- _ => apply (v6_abytes_low rd rd' _ _ H K); vm_compute; reflexivity end.
- intros e He a Ha.
  assert (Hall : forallb (fun x => (0 <=? x) && (x + 8 <=? 0x606000)) cmd_ro_ends = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall e He). apply andb_true_iff in Hall as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
  rewrite K by lia. exact (Ht e He a Ha).
Qed.
Lemma v6_got_ok_low : forall rd rd', cmd_got_ok rd -> (forall x, 0 <= x < 0x606000 -> rd' x = rd x) -> cmd_got_ok rd'.
Proof.
intros rd rd' (H1 & H2 & H3 & H4) K.
unfold A_G_REC, A_G_QUITTING in *.
split; [|split; [|split]]; intros i Hi; rewrite K by lia; [apply H1 | apply H2 | apply H3 | apply H4]; exact Hi.
Qed.
(* cmd_got_ok's four words are among cmd_ro_ok's bytes (verbatim the S25 kit's vr_got_of_ro) *)
Lemma v6_got_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [H _]. unfold cmd_ro_bytes in H.
repeat match goal with G : _ /\ _ |- _ => destruct G end.
unfold cmd_got_ok.
split; [|split; [|split]]; intros k Hk.
- match goal with G : abytes_atR rd 0xa7068 RO_ptr_a7068 |- _ => rewrite (G k) by (vm_compute; lia) end.
  do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
- match goal with G : abytes_atR rd 0xa7070 RO_ptr_a7070 |- _ => rewrite (G k) by (vm_compute; lia) end.
  do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
- match goal with G : abytes_atR rd 0xa7078 RO_ptr_a7078 |- _ => rewrite (G k) by (vm_compute; lia) end.
  do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
- match goal with G : abytes_atR rd 0xa7080 RO_ptr_a7080 |- _ => rewrite (G k) by (vm_compute; lia) end.
  do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

(* the length strndup copies bounds the trimmed line *)
Lemma v6_line_le : forall D n, Z.of_nat (length D) = n -> Z.of_nat (length (Verbs.line D)) <= vr_l n D.
Proof.
intros D n Hn. unfold vr_l. rewrite <- Hn. rewrite (proj2 (PVP.strnlen_upto D)).
unfold Verbs.line, Verbs.trim. rewrite length_rev.
pose proof (VRR.dropw_len Verbs.is_trail (rev (Verbs.upto0 D))) as L. rewrite length_rev in L. lia.
Qed.

(* s1 after `andi sp,sp,-32` *)
Lemma v6_s1_rng : forall sp0, sp0 mod 16 = 0 ->
(sp0 - 192 - (sp0 - 192) mod 32) mod 16 = 0 /\ sp0 - 208 <= sp0 - 192 - (sp0 - 192) mod 32 <= sp0 - 192.
Proof.
intros sp0 H. pose proof (Z.div_mod (sp0 - 192) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (sp0 - 192) 32 ltac:(lia)) as M.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2. rewrite H in D2.
split; [|lia].
replace (sp0 - 192 - (sp0 - 192) mod 32) with ((2 * ((sp0 - 192) / 32)) * 16) by lia. apply Z.mod_mul. lia.
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

(* the registers a test reads, by the reload group: before 0x8d73c, after it, after 0x8d7e8 *)
Definition v6_rl (e : vrE) (F q v : Z) (g : nat) : list (Z * Z) :=
let nt := vr_ntok (e_D e) in
[(19, SHADOW_OFF); (21, nt); (22, F + 32); (25, nt); (26, v)] ++
match g with
| 0%nat => [(27, nt - 1)]
| 1%nat => [(18, q); (27, nt - 1)]
| _ => [(18, q); (20, F); (27, shadow_addr F + 4)]
end.
Lemma v6_rl_rt : forall e F q v r, vr_rl_rt e F q v r = v6_rl e F q v (vr_rgroup r).
Proof. intros. unfold vr_rl_rt, v6_rl. destruct (vr_rgroup r) as [|[|]]; reflexivity. Qed.

(* the memory a test leaves: the entries it calls write only below s1 *)
Definition v6_KO (e : vrE) (W : world SEGS) (m m' : word -> option byte) : Prop :=
kept_out (rdW W m) (rdW W m') (vr_s1 e - VERB_IS_STK) (vr_s1 e).
Lemma v6_KO_refl : forall e W m, v6_KO e W m m.
Proof. intros e W m a _ _. reflexivity. Qed.
Lemma v6_KO_trans : forall e W m1 m2 m3, v6_KO e W m1 m2 -> v6_KO e W m2 m3 -> v6_KO e W m1 m3.
Proof. intros e W m1 m2 m3 H1 H2 a Ha Hn. rewrite (H2 a Ha Hn). exact (H1 a Ha Hn). Qed.
Lemma v6_KO_eq : forall e W m1 m2, (forall a, 0 <= a < 2 ^ 64 -> rdW W m2 a = rdW W m1 a) -> v6_KO e W m1 m2.
Proof. intros e W m1 m2 H a Ha _. exact (H a Ha). Qed.

Lemma v6_rv_get : forall regs l r v, vr_rv regs l -> In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs l r v H Hin. unfold vr_rv in H. rewrite Forall_forall in H. exact (H (r, v) Hin). Qed.
Lemma v6_rv_intro : forall regs l, (forall r v, In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v) -> vr_rv regs l.
Proof. intros regs l H. unfold vr_rv. apply Forall_forall. intros [r v] Hin. exact (H r v Hin). Qed.

Lemma v6_rdW_mod : forall (W : world SEGS) m a, rdW W m a = rdW W m (a mod 2 ^ 64).
Proof.
intros W m a. unfold aview, mbyte, mrestrict.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* the readers of two states that agree everywhere *)
Lemma v6_rdeq_frame : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hf Hro a. apply (aview_eq_of SEGS). apply Hf.
intros (r & Hr & Ha). rewrite Forall_forall in Hro. pose proof (Hro r Hr). lia.
Qed.
Lemma v6_kept_regs : forall E ss ms (regs0 : bvmap 5 word) extra (zs : list Z),
st_ok SEGS E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) (map (Z_to_bv 5) zs) = true ->
forall r, In r zs -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros E ss ms regs0 extra zs HS HA Hl r Hr.
apply (regs_kept_of_st_ok SEGS E ss ms regs0 extra (map (Z_to_bv 5) zs) HS HA Hl). apply in_map. exact Hr.
Qed.
Lemma v6_env_agree : forall (regs : bvmap 5 word) extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma v6_env_agree_havoc : forall (regs : bvmap 5 word) extra E k ws, (32 <= k)%nat ->
env_agree 32 (Ereg regs extra) E -> env_agree 32 (Ereg regs extra) (havoc E k ws).
Proof.
intros regs extra E k ws Hk [H1 H2]. split; [|exact H2].
intros n Hn. rewrite ew_havoc_old by lia. exact (H1 n Hn).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis TL : PALib B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* a state between two tests: the dispatch has failed the first i tests; s10 holds tok[0] *)
Definition v6_dm (e : vrE) (pc : Z) (g i : nat) : world SEGS -> config -> Prop := fun Wc cf =>
exists pos F q c tp lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc pc) regsc memc mdc /\ Verbs.toks (e_D e) <> [] /\
VRR.route (Verbs.toks (e_D e)) = v6_casc (skipn i v6_tests) (hd [] (Verbs.toks (e_D e))) (tl (Verbs.toks (e_D e))) /\
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (v6_rl e F q (hd 0 tp) g) (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc Wc regsc memc mdc /\
vr_line B e q Wc memc /\ vr_copy B e F c tp Wc memc.

(* the boundary state's facts carried across a memory that changed only in the window below s1 *)
Lemma v6_env_kept : forall (W : world SEGS) memc mem lo hi,
vr_env B W memc -> kept_out (rdW W memc) (rdW W mem) lo hi ->
(forall a, lo <= a < hi -> rdW W memc a <> None) -> alloc_ceiling <= lo -> lo < hi -> hi <= 2 ^ 64 ->
vr_env B W mem.
Proof.
intros W memc mem lo hi (HRO & HGOT & HROK & HAG & HFL & ev & HER) K Hvis Hlo Hlh Hhi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (pal_env B TL) as ((He0 & He1) & _).
assert (KL : forall x, 0 <= x < 0x606000 -> rdW W mem x = rdW W memc x) by (intros x Hx; apply K; lia).
split.
{ intros a Hro Ho He. rewrite (v6_rdW_mod W mem a).
  pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as M.
  destruct (Z_lt_le_dec (a mod 2 ^ 64) lo) as [H1|H1]; [|destruct (Z_lt_le_dec (a mod 2 ^ 64) hi) as [H2|H2]].
  - rewrite (K _ M) by lia. rewrite <- v6_rdW_mod. exact (HRO a Hro Ho He).
  - exfalso. pose proof (HRO a Hro Ho He) as E. rewrite (v6_rdW_mod W memc a) in E.
    pose proof (Hvis _ (conj H1 H2)) as Hv.
    replace (Z_to_bv 64 a) with (Z_to_bv 64 (a mod 2 ^ 64)) in E
      by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); rewrite Z.mod_mod by lia; reflexivity).
    assert (Hs : seg_rom SEGS (Z_to_bv 64 (a mod 2 ^ 64)) <> None) by (intros Hn; rewrite Hn in E; cbn in E; exact (Hv E)).
    pose proof (pa_img_range _ (seg_rom_in_img SEGS (a mod 2 ^ 64) M Hs)). lia.
  - rewrite (K _ M) by lia. rewrite <- v6_rdW_mod. exact (HRO a Hro Ho He). }
split; [exact (v6_got_ok_low _ _ HGOT KL)|].
split; [exact (v6_ro_ok_low _ _ HROK KL)|].
split; [exact (aguard_ok_kept SEGS W memc mem lo hi _ _ K HAG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))|].
split; [rewrite K by lia; exact HFL|].
exists ev. exact (rd32_kept _ _ lo hi _ ev K HER ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma v6_aval_val : forall (W : world SEGS) m a n v, aval_mem (rdW W m) a n v -> val_mem SEGS (mrestrict (w_H W) m) a n v.
Proof.
intros W m a n v H k Hk. specialize (H k Hk).
destruct (aview_byte SEGS _ _ _ _ H) as (b & Hb & Hv & _). rewrite Hb. f_equal.
assert (E : YO0f.le_byte v n k = bv_unsigned b) by (rewrite <- Hv; reflexivity).
rewrite E. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma v6_aval_kept : forall rd rd' lo hi a n v, kept_out rd rd' lo hi -> aval_mem rd a n v -> 0 <= a ->
(a + Z.of_nat n <= lo \/ hi <= a) -> a + Z.of_nat n <= 2 ^ 64 -> aval_mem rd' a n v.
Proof. intros rd rd' lo hi a n v K H H0 Hd H64 k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma v6_rv_base : forall e regs rl, vr_rv regs (vr_base B e ++ rl) ->
getr regs (Z_to_bv 5 2) = w64 (vr_s1 e) /\ getr regs (Z_to_bv 5 3) = w64 (as_gp B) /\
getr regs (Z_to_bv 5 4) = w64 (as_tp B) /\ getr regs (Z_to_bv 5 8) = w64 (vr_sp0 e) /\
getr regs (Z_to_bv 5 9) = w64 (vr_s1 e).
Proof.
intros e regs rl H. unfold vr_rv in H. apply Forall_app in H as [H _]. unfold vr_base in H.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [? H] end.
cbn [fst snd] in *. repeat split; assumption.
Qed.
Lemma v6_rv_rest : forall e regs rl, vr_rv regs (vr_base B e ++ rl) -> vr_rv regs rl.
Proof. intros e regs rl H. unfold vr_rv in *. apply Forall_app in H as [_ H]. exact H. Qed.
(* the registers of a later state: the base registers kept, each listed register kept or set to its value *)
Lemma v6_rv_keep : forall e (regs regsc : bvmap 5 word) rl rl',
vr_rv regsc (vr_base B e ++ rl) ->
(forall r, In r [2; 3; 4; 8; 9] -> getr regs (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) ->
(forall r v, In (r, v) rl' ->
  (In (r, v) rl /\ getr regs (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) \/ getr regs (Z_to_bv 5 r) = w64 v) ->
vr_rv regs (vr_base B e ++ rl').
Proof.
intros e regs regsc rl rl' Hrv Hb Hl. apply v6_rv_intro. intros r v Hin. apply in_app_or in Hin as [Hin|Hin].
- assert (Hr : In r [2; 3; 4; 8; 9]).
  { unfold vr_base in Hin. cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _; cbn; tauto. }
  rewrite (Hb r Hr). apply (v6_rv_get regsc _ _ _ Hrv). apply in_or_app; left; exact Hin.
- destruct (Hl r v Hin) as [[H1 H2] | H]; [|exact H].
  rewrite H2. apply (v6_rv_get regsc _ _ _ Hrv). apply in_or_app; right; exact H1.
Qed.

(* the boundary state carried across a memory that changed only in the window below s1, with new registers *)
Lemma v6_carry : forall e pos F tmps sh sl rl rl' R O qv k kmax nm nmax lyc Sc (W : world SEGS) regsc memc mdc regsF memF mdF,
vr_core B MT e pos F tmps sh sl rl R O qv k kmax nm nmax lyc Sc W regsc memc mdc ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W memF mdF k ->
v6_KO e W memc memF ->
Forall (fun ov => 0 <= fst ov <= 1024) sl ->
vr_rv regsF (vr_base B e ++ rl') ->
vr_core B MT e pos F tmps sh sl rl' R O qv k kmax nm nmax lyc Sc W regsF memF mdF.
Proof.
intros e pos F tmps sh sl rl rl' R O qv k kmax nm nmax lyc Sc W regsc memc mdc regsF memF mdF
(HJ & Hkk & HMET & Hnm & (HFa & HFl & HFs) & HRV & HSV & HSP & HENV & HREC & HnO & HPERM & HQ) HJ' K Hsl HRV'.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstk & Hext & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (VRS : VERBS_RECEIVE_STK = 16992) by reflexivity. assert (VIS : VERB_IS_STK = 8224) by reflexivity.
pose proof (v6_s1_rng (vr_sp0 e) Hal16) as [S1a S1b]. fold (vr_s1 e) in S1a, S1b.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin4) as (HF0 & HFc & _). rewrite <- HFa in HF0, HFc.
change (fs_frame_bytes 4) with 1024 in HFc.
assert (FS4 : fs_frame_bytes 4 = 1024) by reflexivity.
unfold v6_KO in K.
unfold vr_core.
split; [exact HJ'|]. split; [exact Hkk|]. split; [exact HMET|]. split; [exact Hnm|].
split.
{ split; [exact HFa|]. split.
  - apply (rdword_kept _ _ (vr_s1 e - VERB_IS_STK) (vr_s1 e) _ _ K HFl); lia.
  - intros i Hi. pose proof (shadow_addr_bounds (F + 1024) ltac:(lia)). pose proof (shadow_addr_bounds F ltac:(lia)).
    pose proof (shadow_range_end F 1024 ltac:(lia)). change (1024 / 8) with 128 in *.
    unfold kept_out in K. rewrite K.
    + exact (HFs i Hi).
    + split; [lia|]. lia.
    + intros [Hx1 Hx2]. lia. }
split; [exact HRV'|].
split.
{ intros j r Hj. pose proof (HSV j r Hj) as H.
  assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length vr_saved_regs] in Hj13.
  apply (v6_aval_kept _ _ (vr_s1 e - VERB_IS_STK) (vr_s1 e) _ _ _ K H); unfold vr_sp0 in *; lia. }
split.
{ unfold vr_spill in *. rewrite Forall_forall in HSP, Hsl |- *. intros [off v] Hin. specialize (HSP _ Hin). specialize (Hsl _ Hin).
  cbn [fst snd] in *. apply (v6_aval_kept _ _ (vr_s1 e - VERB_IS_STK) (vr_s1 e) _ _ _ K HSP); unfold vr_sp0 in *; lia. }
split.
{ apply (v6_env_kept W memc memF (vr_s1 e - VERB_IS_STK) (vr_s1 e) HENV K); [|unfold vr_sp0 in *; lia | lia | unfold vr_sp0 in *; lia].
  intros a Ha. apply (aview_some_of_apresent SEGS). apply Hpres. unfold vr_sp0 in *. lia. }
split.
{ apply (rec_repA_agree B lyc Sc lyc Sc _ _ R O HREC (fun pn _ Hb => Hb)).
  - intros kk Hk2. apply K; unfold A_G_REC, REC_SIZE in *; lia.
  - intros kk Hk2. apply K; unfold A_REC_SPILL, SC_SIZE in *; lia.
  - intros [p n] Hpn kk Hk2. cbn [fst snd] in *.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (rec_repA_in_blocks B _ _ _ _ _ _ HREC Hpn)) as (_ & H4 & Hc & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hr]. apply K; lia. }
split; [exact HnO|]. split; [exact HPERM|].
apply (v6_aval_kept _ _ (vr_s1 e - VERB_IS_STK) (vr_s1 e) _ _ _ K HQ); unfold A_G_QUITTING; lia.
Qed.

(* the line and the copy carried the same way *)
Lemma v6_lc_carry : forall e pos F q c tp lyc Sc (W : world SEGS) memc mdc memF lo hi,
AR SEGS B lyc Sc W memc mdc -> In (vr_lb e q) (ablocks B lyc Sc) -> In (vr_cb e c) (ablocks B lyc Sc) ->
In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos -> Z.of_nat (length (e_D e)) = e_n e ->
kept_out (rdW W memc) (rdW W memF) lo hi -> alloc_ceiling <= lo -> lo < 2 ^ 64 ->
vr_line B e q W memc -> vr_copy B e F c tp W memc -> vr_line B e q W memF /\ vr_copy B e F c tp W memF.
Proof.
intros e pos F q c tp lyc Sc W memc mdc memF lo hi HAR Hlb Hcb Hin4 HFa Hn K Hlo Hlo64 (Hfr & Hstr) (Hfc & Hm8 & Hlen & Hptr & Hw).
pose proof asan_consts as (C1 & _).
unfold vr_lb, vr_cb in *. cbn [fst snd] in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hlb) as (_ & Hq4 & Hqc & _ & _ & _ & Hqn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4 & Hcc & _ & _ & _ & Hcn).
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as [_ Rq].
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [_ Rc].
pose proof (v6_line_le (e_D e) (e_n e) Hn) as Ll.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin4) as (HF0 & HFc & _). rewrite <- HFa in HF0, HFc.
change (fs_frame_bytes 4) with 1024 in HFc.
assert (FS4 : fs_frame_bytes 4 = 1024) by reflexivity.
split.
- split; [exact Hfr|]. apply (astr_atR_kept _ _ lo hi q _ K Hstr); lia.
- split; [exact Hfc|]. split; [exact Hm8|]. split; [exact Hlen|]. split.
  + intros i p Hi. pose proof (Hptr i p Hi) as H.
    assert (Hil : (i < length tp)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    pose proof (Verbs.toks_length (e_D e)). rewrite Hlen in Hil.
    apply (v6_aval_kept _ _ lo hi _ _ _ K H); lia.
  + intros i p w Hi Hwi. destruct (Hw i p w Hi Hwi) as (Hs & Hl8 & Hcp & Hpe).
    split; [|split; [exact Hl8 | split; [exact Hcp | exact Hpe]]].
    apply (astr_atR_kept _ _ lo hi p w K Hs); lia.
Qed.

(* a boundary state's tmps and frame facts *)
Lemma v6_core_blocks : forall e pos F q c sh sl rl R O qv k kmax nm nmax lyc Sc (W : world SEGS) regsc memc mdc,
vr_core B MT e pos F [vr_lb e q; vr_cb e c] sh sl rl R O qv k kmax nm nmax lyc Sc W regsc memc mdc ->
In (vr_lb e q) (ablocks B lyc Sc) /\ In (vr_cb e c) (ablocks B lyc Sc) /\ In (4, pos) (frames Sc) /\ F = frame_addr lyc 4 pos.
Proof.
intros e pos F q c sh sl rl R O qv k kmax nm nmax lyc Sc W regsc memc mdc
(HJ & _ & _ & _ & (HFa & _) & _ & _ & _ & _ & _ & _ & HPERM & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
split; [apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; left; reflexivity|].
split; [apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; right; left; reflexivity|].
split; [rewrite Hfrs; left; reflexivity | exact HFa].
Qed.

Lemma v6_ent_len : forall e, vr_ent B MT e -> Z.of_nat (length (e_D e)) = e_n e.
Proof. intros e H. unfold vr_ent in H. cbv zeta in H. tauto. Qed.
Lemma v6_ent_ro : forall e, vr_ent B MT e -> cmd_ro_in (in_roP SEGS RLO RHI) /\ cmd_val_objs.
Proof. intros e H. unfold vr_ent in H. cbv zeta in H. tauto. Qed.

(* the exit of a test: the boundary state at the new memory, with the new registers *)
Lemma v6_exit : forall e pos F q c tp lyc Sc (W : world SEGS) regsc memc mdc k nm rl regsF memF mdF rl',
vr_ent B MT e ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W memF mdF k ->
v6_KO e W memc memF -> vr_rv regsF (vr_base B e ++ rl') ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl' (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regsF memF mdF /\
vr_line B e q W memF /\ vr_copy B e F c tp W memF.
Proof.
intros e pos F q c tp lyc Sc W regsc memc mdc k nm rl regsF memF mdF rl' He HC HL HCP HJ' K HRV'.
destruct (v6_core_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as (Hlb & Hcb & Hin4 & HFa).
pose proof HC as (HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (v6_s1_rng (vr_sp0 e) Hal16) as [S1a S1b]. fold (vr_s1 e) in S1a, S1b.
assert (VRS : VERBS_RECEIVE_STK = 16992) by reflexivity. assert (VIS : VERB_IS_STK = 8224) by reflexivity.
pose proof (v6_ent_len e He) as HDn.
split; [apply (v6_carry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC HJ' K); [|exact HRV']|].
- unfold vr_sl3. repeat constructor; cbn [fst]; lia.
- apply (v6_lc_carry e pos F q c tp lyc Sc W memc mdc memF (vr_s1 e - VERB_IS_STK) (vr_s1 e) HAR Hlb Hcb Hin4 HFa HDn K);
  [unfold vr_sp0 in *; lia | unfold vr_sp0 in *; lia | exact HL | exact HCP].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The symbolic state a test starts from: the registers as atoms, three more atoms (F, the line q, the shadow of F)
   and the spill slots s1+16 .. s1+47 the tests reload (read-only) *)
Definition v6_region : YP09.region := YP09.mkRegion (Some 9%nat) 16 48 16 16
[YP09.mkChunk 16 (CVal 8 (SOff 32 32)); YP09.mkChunk 24 (CVal 8 (SOff 33 0));
 YP09.mkChunk 32 (CVal 8 (SOff 34 4)); YP09.mkChunk 40 (CVal 8 (SOff 32 0))].
Definition v6_ss (pc : Z) : sstate := mkSS (AF_verbs_receive + (pc - 0x8d480)) sr_atoms [v6_region] None (mkFacts [] [] []).
Definition v6_extra (F q : Z) : list word := map (Z_to_bv 64) [F; q; shadow_addr F].
Lemma v6_E_reg : forall regs extra n, (n < 32)%nat -> ew (Eimg (Ereg regs extra)) n = getr regs (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros regs extra n Hn. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma v6_E_ex : forall regs F q,
ew (Eimg (Ereg regs (v6_extra F q))) 32 = Z_to_bv 64 F /\ ew (Eimg (Ereg regs (v6_extra F q))) 33 = Z_to_bv 64 q /\
ew (Eimg (Ereg regs (v6_extra F q))) 34 = Z_to_bv 64 (shadow_addr F).
Proof.
intros regs F q. rewrite !Eimg_low by (unfold A_TEXT; lia).
change 32%nat with (32 + 0)%nat at 1. change 33%nat with (32 + 1)%nat. change 34%nat with (32 + 2)%nat.
rewrite !ew_Ereg_extra. split; [|split]; reflexivity.
Qed.
Lemma v6_pc_eq : forall pc, vr_pc pc = BASE + (AF_verbs_receive + (pc - 0x8d480)).
Proof. reflexivity. Qed.
Lemma v6_cfg : forall regs mem md pc, mkCfg (mkst regs (Z_to_bv 64 (BASE + (AF_verbs_receive + (pc - 0x8d480)))) mem (seg_rom SEGS)) md =
cfg_at SEGS (vr_pc pc) regs mem md.
Proof. intros. unfold cfg_at, vr_pc, w64. reflexivity. Qed.
Lemma v6_cfg2 : forall regs mem md pc off, off = AF_verbs_receive + (pc - 0x8d480) ->
mkCfg (mkst regs (Z_to_bv 64 (BASE + off)) mem (seg_rom SEGS)) md = cfg_at SEGS (vr_pc pc) regs mem md.
Proof. intros regs mem md pc off ->. unfold cfg_at, vr_pc, w64. reflexivity. Qed.

Lemma v6_seed : forall e pos F q c lyc Sc (W : world SEGS) regsc memc mdc k nm rl pc,
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (v6_extra F q))) (v6_ss pc)
(restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + (AF_verbs_receive + (pc - 0x8d480)))) memc (seg_rom SEGS))).
Proof.
intros e pos F q c lyc Sc W regsc memc mdc k nm rl pc HC.
destruct (v6_core_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as (Hlb & Hcb & Hin4 & HFa).
destruct HC as (HJ & _ & _ & _ & _ & HRV & _ & HSP & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (v6_s1_rng (vr_sp0 e) Hal16) as [S1a S1b]. fold (vr_s1 e) in S1a, S1b.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin4) as (HF0 & HFc & _). rewrite <- HFa in HF0, HFc.
change (fs_frame_bytes 4) with 1024 in HFc.
unfold vr_lb in Hlb. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hlb) as (_ & Hq4 & Hqc & _ & _ & _ & Hqn).
pose proof (req_size_pos _ (proj1 Hqn)) as [Rq1 _].
assert (VRS : VERBS_RECEIVE_STK = 16992) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (shadow_addr_bounds F ltac:(lia)) as SB.
assert (E9 : bv_unsigned (ew (Eimg (Ereg regsc (v6_extra F q))) 9) = vr_s1 e).
{ rewrite v6_E_reg by v6_lia2. change (Z.of_nat 9) with 9. rewrite (proj2 (proj2 (proj2 (proj2 (v6_rv_base e regsc rl HRV))))).
  unfold w64. apply unsigned_lit_small. lia. }
assert (R1 : 0 <= F + 32 < 2 ^ 64) by v6_lia2. assert (R2 : 0 <= q < 2 ^ 64) by v6_lia2.
assert (R3 : 0 <= shadow_addr F + 4 < 2 ^ 64) by v6_lia2. assert (R4 : 0 <= F < 2 ^ 64) by v6_lia2.
assert (R5 : 0 <= vr_s1 e + 16 /\ vr_s1 e + 48 <= 2 ^ 64) by v6_lia2.
unfold vr_spill, vr_sl3 in HSP. rewrite Forall_forall in HSP.
rewrite restrict_mkst_fx. unfold v6_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, v6_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS _ _ (vr_s1 e) 16 8 (SOff 32 32) (F + 32));
    [cbn [sv_denot]; rewrite (proj1 (v6_E_ex regsc F q)), (unsigned_lit_small F) by exact R4; reflexivity | cbn; v6_lia2 | cbn; v6_lia2 |].
    apply v6_aval_val. exact (HSP (16, F + 32) ltac:(cbn; tauto)).
  + apply (chunk_ok_val SEGS _ _ (vr_s1 e) 24 8 (SOff 33 0) q);
    [cbn [sv_denot]; rewrite (proj1 (proj2 (v6_E_ex regsc F q))), (unsigned_lit_small q) by exact R2; rewrite Z.add_0_r; reflexivity
    | cbn; v6_lia2 | cbn; v6_lia2 |].
    apply v6_aval_val. exact (HSP (24, q) ltac:(cbn; tauto)).
  + apply (chunk_ok_val SEGS _ _ (vr_s1 e) 32 8 (SOff 34 4) (shadow_addr F + 4));
    [cbn [sv_denot]; rewrite (proj2 (proj2 (v6_E_ex regsc F q))), (unsigned_lit_small (shadow_addr F)) by lia; reflexivity
    | cbn; v6_lia2 | cbn; v6_lia2 |].
    apply v6_aval_val. exact (HSP (32, shadow_addr F + 4) ltac:(cbn; tauto)).
  + apply (chunk_ok_val SEGS _ _ (vr_s1 e) 40 8 (SOff 32 0) F);
    [cbn [sv_denot]; rewrite (proj1 (v6_E_ex regsc F q)), (unsigned_lit_small F) by exact R4; rewrite Z.add_0_r; reflexivity
    | cbn; v6_lia2 | cbn; v6_lia2 |].
    apply v6_aval_val. exact (HSP (40, F) ltac:(cbn; tauto)).
- cbn. tauto.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The literals the tests compare the first word with *)
Definition v6_lit (y : Z) (sy : list byte) : Prop :=
(forall rd, cmd_ro_ok rd -> abytes_atR rd y (sy ++ [Z_to_bv 8 0])) /\
In (y, Z.of_nat (length sy) + 1) vr_shr /\
existsb (Z.eqb (y + Z.of_nat (length sy))) cmd_ro_ends = true /\
~ In (Z_to_bv 8 0) sy /\ 0x10000 <= y /\ y + Z.of_nat (length sy) + 1 <= 0x606000.
Lemma v6_no0 : forall s, forallb (fun b : byte => negb (bv_unsigned b =? 0)) s = true -> ~ In (Z_to_bv 8 0) s.
Proof. intros s H Hin. rewrite forallb_forall in H. specialize (H _ Hin). vm_compute in H. discriminate H. Qed.
Ltac v6_lit_tac :=
split; [intros rd H; pose proof (v6_ro_lits rd H) as X; decompose [and] X; assumption|];
split; [unfold vr_shr, vr_lits; cbn [map app fst snd]; repeat (first [left; reflexivity | right])|];
split; [vm_compute; reflexivity|];
split; [apply v6_no0; vm_compute; reflexivity|];
split; apply Z.leb_le; vm_compute; reflexivity.
Lemma v6_lit_sep : v6_lit 0x224c0 (map (Z_to_bv 8) [32; 9]). Proof. v6_lit_tac. Qed.
Lemma v6_lit_add : v6_lit 0x22560 PV.Lit.verb_add. Proof. v6_lit_tac. Qed.
Lemma v6_lit_dget : v6_lit 0x22580 PV.Lit.verb_descriptor_get. Proof. v6_lit_tac. Qed.
Lemma v6_lit_pget : v6_lit 0x225a0 PV.Lit.verb_panel_get. Proof. v6_lit_tac. Qed.
Lemma v6_lit_remove : v6_lit 0x225c0 PV.Lit.fmt_remove. Proof. v6_lit_tac. Qed.
Lemma v6_lit_wlist : v6_lit 0x225e0 PV.Lit.verb_worker_list. Proof. v6_lit_tac. Qed.
Lemma v6_lit_iinfo : v6_lit 0x22600 PV.Lit.verb_instance_info. Proof. v6_lit_tac. Qed.
Lemma v6_lit_reset : v6_lit 0x22620 PV.Lit.verb_supervisor_reset. Proof. v6_lit_tac. Qed.
Lemma v6_lit_qclear : v6_lit 0x22680 PV.Lit.verb_quarantine_clear. Proof. v6_lit_tac. Qed.
Lemma v6_lit_policy : v6_lit 0x226c0 PV.Lit.verb_policy_set. Proof. v6_lit_tac. Qed.
Lemma v6_lit_lv2 : v6_lit 0x226e0 PV.Lit.verb_lv2_worker_set. Proof. v6_lit_tac. Qed.
Lemma v6_lit_pool : v6_lit 0x22700 PV.Lit.verb_pool_config. Proof. v6_lit_tac. Qed.
Lemma v6_lit_env : v6_lit 0x22720 PV.Lit.verb_worker_env. Proof. v6_lit_tac. Qed.
Lemma v6_lit_chain : v6_lit 0x22740 PV.Lit.verb_chain. Proof. v6_lit_tac. Qed.
Lemma v6_lit_chclear : v6_lit 0x22760 PV.Lit.verb_chain_clear. Proof. v6_lit_tac. Qed.
Lemma v6_lit_pinset : v6_lit 0x22780 PV.Lit.verb_pin_set. Proof. v6_lit_tac. Qed.
Lemma v6_lit_pinacc : v6_lit 0x227a0 PV.Lit.verb_pin_accept. Proof. v6_lit_tac. Qed.
Lemma v6_lit_pinclr : v6_lit 0x227c0 PV.Lit.verb_pin_clear. Proof. v6_lit_tac. Qed.
Lemma v6_lit_quit : v6_lit 0x227e0 PV.Lit.fmt_quit. Proof. v6_lit_tac. Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The calls of a test: the comparison entries (the runtime contracts) and verb_is *)
Hypothesis SHOK : vr_shadow_ok B.
Hypothesis BLKT : vr_blktail B.

Lemma v6_mem_at : forall e pos F tmps sh sl rl R O qv k kmax nm nmax lyc Sc (W : world SEGS) regsc memc mdc mem md,
vr_core B MT e pos F tmps sh sl rl R O qv k kmax nm nmax lyc Sc W regsc memc mdc ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem md k ->
v6_KO e W memc mem ->
AR SEGS B lyc Sc W mem md /\ vr_env B W mem /\ alloc_ceiling <= vr_s1 e - VERB_IS_STK /\
vr_sp0 e - 208 <= vr_s1 e <= vr_sp0 e - 192 /\ vr_s1 e mod 16 = 0 /\ (vr_s1 e - vr_sp0 e) mod 16 = 0 /\
vr_sp0 e <= 2 ^ 47 /\ vr_sp0 e - VERBS_RECEIVE_STK <= vr_s1 e - VERB_IS_STK.
Proof.
intros e pos F tmps sh sl rl R O qv k kmax nm nmax lyc Sc W regsc memc mdc mem md HC HJ K.
destruct HC as (HJc & _ & _ & _ & _ & _ & _ & _ & HENV & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (v6_s1_rng (vr_sp0 e) Hal16) as [S1a S1b]. fold (vr_s1 e) in S1a, S1b.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (VRS : VERBS_RECEIVE_STK = 16992) by reflexivity. assert (VIS : VERB_IS_STK = 8224) by reflexivity.
split; [exact (proj1 HJ)|].
split.
{ apply (v6_env_kept W memc mem (vr_s1 e - VERB_IS_STK) (vr_s1 e) HENV K); [| lia | lia | lia].
  intros a Ha. apply (aview_some_of_apresent SEGS). apply Hpres. lia. }
split; [lia|]. split; [lia|]. split; [exact S1a|].
split.
{ replace (vr_s1 e - vr_sp0 e) with ((vr_s1 e / 16 - vr_sp0 e / 16) * 16).
  - apply Z.mod_mul. lia.
  - pose proof (Z.div_mod (vr_s1 e) 16 ltac:(lia)). pose proof (Z.div_mod (vr_sp0 e) 16 ltac:(lia)). lia. }
split; lia.
Qed.

Lemma v6_pre_at : forall e pos lyc Sc (W : world SEGS) mem md k (regs : bvmap 5 word) stk,
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem md k ->
spZ regs = vr_s1 e -> YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
ESTACK <= stk <= VERB_IS_STK ->
ecall_pre_stk SEGS B stk lyc Sc W regs mem md.
Proof.
intros e pos lyc Sc W mem md k regs stk HJ Hsp Hra Hgp Htp Hstk1.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _).
pose proof (v6_s1_rng (vr_sp0 e) Hal16) as [S1a S1b]. fold (vr_s1 e) in S1a, S1b.
assert (VRS : VERBS_RECEIVE_STK = 16992) by reflexivity. assert (VIS : VERB_IS_STK = 8224) by reflexivity.
apply (ecall_pre_stk_at SEGS B stk VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  [(4, pos)] lyc Sc W mem md k regs (vr_s1 e - vr_sp0 e) HJ).
- lia.
- replace (vr_s1 e - vr_sp0 e) with ((vr_s1 e / 16 - vr_sp0 e / 16) * 16).
  + apply Z.mod_mul. lia.
  + pose proof (Z.div_mod (vr_s1 e) 16 ltac:(lia)). pose proof (Z.div_mod (vr_sp0 e) 16 ltac:(lia)). lia.
- lia. - lia. - lia.
- exact Hra. - exact Hgp. - exact Htp.
Qed.

(* the first word at a call: a string in the copy block, below the window *)
Lemma v6_verb_at : forall e pos F q c tp lyc Sc (W : world SEGS) regsc memc mdc k nm rl mem md,
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_copy B e F c tp W memc -> Verbs.toks (e_D e) <> [] ->
AR SEGS B lyc Sc W mem md -> v6_KO e W memc mem -> alloc_ceiling <= vr_s1 e - VERB_IS_STK -> vr_s1 e <= 2 ^ 47 ->
astr_atR (rdW W mem) (hd 0 tp) (hd [] (Verbs.toks (e_D e))) /\ 4096 <= hd 0 tp /\
hd 0 tp + Z.of_nat (length (hd [] (Verbs.toks (e_D e)))) + 1 <= alloc_ceiling /\
in_blockA (ablocks B lyc Sc) (hd 0 tp) (Z.of_nat (length (hd [] (Verbs.toks (e_D e)))) + 1) /\
Z.of_nat (length (hd [] (Verbs.toks (e_D e)))) <= 8192 /\
atail_vis SEGS W mem (hd 0 tp + Z.of_nat (length (hd [] (Verbs.toks (e_D e))))) /\
(forall stk (regs : bvmap 5 word) n', alloc_ceiling <= spZ regs - stk ->
 0 <= n' <= Z.of_nat (length (hd [] (Verbs.toks (e_D e)))) + 1 -> aread_ok SEGS stk W regs mem (hd 0 tp) n') /\
(forall b, In b (hd [] (Verbs.toks (e_D e))) -> bv_unsigned b <> 32 /\ bv_unsigned b <> 9 /\ bv_unsigned b <> 0).
Proof.
intros e pos F q c tp lyc Sc W regsc memc mdc k nm rl mem md HC (Hfc & Hm8 & Hlen & Hptr & Hw) Hne HAR HKO Hlo Hhi.
assert (VIS : VERB_IS_STK = 8224) by reflexivity.
destruct (v6_core_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as (Hlb & Hcb & Hin4 & HFa).
assert (Hwd : forall vb, hd [] (Verbs.toks (e_D e)) = vb -> Verbs.toks (e_D e) <> [] -> In vb (Verbs.toks (e_D e))).
{ intros vb <- Hn. destruct (Verbs.toks (e_D e)); [contradiction | left; reflexivity]. }
pose proof (Hwd _ eq_refl Hne) as Hin. clear Hwd.
destruct (Verbs.toks (e_D e)) as [|vb args] eqn:Et; [contradiction|].
destruct tp as [|v tps]; [cbn in Hlen; discriminate|]. cbn [hd] in *.
destruct (Hw 0%nat v vb eq_refl eq_refl) as (Hs & Hl8 & Hcv & Hve).
unfold vr_cb in Hcb. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4 & Hcc & _ & _ & _ & Hcn).
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [_ Rc].
pose proof asan_consts as (C1 & _).
rewrite <- Et in Hin. destruct (Verbs.toks_word (e_D e) vb Hin) as (_ & Hch).
split; [apply (astr_atR_kept _ _ _ _ v vb HKO Hs); lia|].
split; [lia|]. split; [lia|].
split; [exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1); split; [exact Hcb | lia]|].
split; [lia|].
split; [apply (BLKT lyc Sc W mem md c _ (v + Z.of_nat (length vb)) HAR Hcb); lia|].
split; [intros stk regs n' Hs' Hn'; apply (aread_ok_of_block SEGS B LAWS stk lyc Sc W regs mem md c _ v _ HAR Hcb); lia|].
exact Hch.
Qed.

(* a literal at a call *)
Lemma v6_lit_at : forall (W : world SEGS) mem ly S md y sy, v6_lit y sy -> vr_env B W mem -> AR SEGS B ly S W mem md ->
astr_atR (rdW W mem) y sy /\
(forall stk (regs : bvmap 5 word) n', alloc_ceiling <= spZ regs - stk -> 0 <= n' <= Z.of_nat (length sy) + 1 ->
 aread_ok SEGS stk W regs mem y n') /\
atail_vis SEGS W mem (y + Z.of_nat (length sy)) /\
range_addressable (rdW W mem) SHADOW_OFF y (Z.of_nat (length sy) + 1) /\ shadow_hull_vis (rdW W mem) y (Z.of_nat (length sy) + 1) /\
0x10000 <= y /\ y + Z.of_nat (length sy) + 1 <= 0x606000.
Proof.
intros W mem ly S md y sy (Hb & Hsh & Hend & Hn0 & Hy & Hye) HENV HAR.
pose proof HENV as (_ & _ & HROK & _).
pose proof (Hb _ HROK) as Hab.
destruct (SHOK ly S W mem md y _ HAR Hsh) as [Hra Hhv].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hvis : forall a, y <= a < y + (Z.of_nat (length sy) + 1) -> rdW W mem a <> None).
{ intros a Ha. assert (Hab' := Hab (Z.to_nat (a - y)) ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite Z2Nat.id in Hab' by lia. replace (y + (a - y)) with a in Hab' by lia. rewrite Hab'. discriminate. }
split; [split; [exact Hab | exact Hn0]|].
split.
{ intros stk regs n' Hsp Hn'. unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; split; [apply Hvis; lia | unfold ascratch_stk; lia]|].
  split; [left; lia|]. split; [apply (range_addressable_sub _ _ y (Z.of_nat (length sy) + 1) y n' Hra); lia|].
  intros Hn0'. unfold shadow_hull_vis in *. intros s Hs. apply Hhv.
  assert (A1 : shadow_addr (y + n' - 1) <= shadow_addr (y + (Z.of_nat (length sy) + 1) - 1))
    by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  assert (A2 : shadow_addr (y + n' - 1) / 8 <= shadow_addr (y + (Z.of_nat (length sy) + 1) - 1) / 8) by (apply Z.div_le_mono; lia).
  lia. }
split.
{ destruct HROK as [_ HT]. apply existsb_exists in Hend as (e' & He' & Hq). apply Z.eqb_eq in Hq. subst e'.
  intros a Ha. exact (HT _ He' a Ha). }
split; [exact Hra|]. split; [exact Hhv|]. lia.
Qed.

(* the comparison entries in the statement's form since pass 4b (verbs_receive_c.v:238-240): at every FP state *)
Hypothesis STRCMP : forall fx0 : YK11.FPState, @RtString.astrcmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcmp).
Hypothesis STRNCMP : forall fx0 : YK11.FPState, @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
Hypothesis STRCSPN : forall fx0 : YK11.FPState, @RtString.astrcspn_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.

(* a test's comparison: strcmp(tok[0], lit), the runtime contract through the kit's aj_art_at *)
Lemma v6_strcmp_step : forall e pos F q c tp lyc Sc (W : world SEGS) regsc memc mdc k nm rl
  (regs : bvmap 5 word) mem md y sy raw K,
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_copy B e F c tp W memc -> Verbs.toks (e_D e) <> [] ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem md k ->
v6_KO e W memc mem ->
spZ regs = vr_s1 e -> getr regs 1 = raw -> YK0s.ret_ok raw -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 (hd 0 tp) -> getr regs 11 = w64 y -> v6_lit y sy ->
(forall regs2 mem2 md2,
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
    lyc Sc W mem2 md2 k ->
  aregs_preserved regs regs2 -> (getr regs2 10 = w64 0 <-> hd [] (Verbs.toks (e_D e)) = sy) -> v6_KO e W memc mem2 ->
  SRr SEGS W (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) K) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (SIGMA CS___interceptor_trampoline_strcmp)) mem (seg_rom SEGS)) md) K.
Proof.
intros e pos F q c tp lyc Sc W regsc memc mdc k nm rl regs mem md y sy raw K HC HCP Hne HJ HKO Hsp Hra Hraok Hgp Htp H10 H11 Hlit HK.
destruct (v6_mem_at e pos F _ _ _ rl _ _ _ k _ nm _ lyc Sc W regsc memc mdc mem md HC HJ HKO) as (HAR & HENV & Hlo & S1 & S1m & So & H47 & Hwl).
destruct (v6_verb_at e pos F q c tp lyc Sc W regsc memc mdc k nm rl mem md HC HCP Hne HAR HKO Hlo ltac:(lia)) as (Hstr & Hv4 & Hvc & Hblk & Hl8 & HTV & HRD & Hch).
destruct (v6_lit_at W mem lyc Sc md y sy Hlit HENV HAR) as (HLs & HLr & HLt & _ & _ & Hy & Hye).
assert (VIS : VERB_IS_STK = 8224) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre_stk SEGS B (2 * ESTACK) lyc Sc W regs mem md)
  by (apply (v6_pre_at e pos lyc Sc W mem md k regs); [exact HJ | exact Hsp | rewrite Hra; exact Hraok | exact Hgp | exact Htp | lia]).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False) _ W regs mem VERBS_RECEIVE_STK
    (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc md k (vr_s1 e - vr_sp0 e) raw
    (fun regs' _ => getr regs' 10 = w64 0 <-> hd [] (Verbs.toks (e_D e)) = sy) HJ);
  [lia | exact So | lia | lia | assert (VRS : VERBS_RECEIVE_STK = 16992) by reflexivity; lia | exact Hra | intros a [] |].
  apply (STRCMP fx lyc Sc W regs mem md (hd 0 tp) y (hd [] (Verbs.toks (e_D e))) sy HPRE H10 H11);
  [lia | lia | apply astr_atR_view; exact Hstr | apply astr_atR_view; exact HLs | apply HRD; unfold astr_len; lia
  | apply HLr; unfold astr_len; lia | exact HTV | exact HLt | exact (vr_rtrom_ok B W mem (proj1 HENV))]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HW2).
apply (HK regs2 mem2 md2 HJ2 HP2 HQ2).
apply (v6_KO_trans e W memc mem mem2 HKO). intros a Ha Hn. apply HW2; [exact Ha | lia | intros []].
Qed.

(* the span test of the inline verb_is(remove): strcspn(tok[0], " \t") *)
Lemma v6_strcspn_step : forall e pos F q c tp lyc Sc (W : world SEGS) regsc memc mdc k nm rl
  (regs : bvmap 5 word) mem md raw K,
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_copy B e F c tp W memc -> Verbs.toks (e_D e) <> [] ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem md k ->
v6_KO e W memc mem ->
spZ regs = vr_s1 e -> getr regs 1 = raw -> YK0s.ret_ok raw -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 (hd 0 tp) -> getr regs 11 = w64 0x224c0 ->
(forall regs2 mem2 md2,
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
    lyc Sc W mem2 md2 k ->
  aregs_preserved regs regs2 ->
  getr regs2 10 = w64 (Z.of_nat (length (PV.tfirst (hd [] (Verbs.toks (e_D e)))))) -> v6_KO e W memc mem2 ->
  SRr SEGS W (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) K) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (SIGMA CS___interceptor_trampoline_strcspn)) mem (seg_rom SEGS)) md) K.
Proof.
intros e pos F q c tp lyc Sc W regsc memc mdc k nm rl regs mem md raw K HC HCP Hne HJ HKO Hsp Hra Hraok Hgp Htp H10 H11 HK.
destruct (v6_mem_at e pos F _ _ _ rl _ _ _ k _ nm _ lyc Sc W regsc memc mdc mem md HC HJ HKO) as (HAR & HENV & Hlo & S1 & S1m & So & H47 & Hwl).
destruct (v6_verb_at e pos F q c tp lyc Sc W regsc memc mdc k nm rl mem md HC HCP Hne HAR HKO Hlo ltac:(lia)) as (Hstr & Hv4 & Hvc & Hblk & Hl8 & HTV & HRD & Hch).
destruct (v6_lit_at W mem lyc Sc md _ _ v6_lit_sep HENV HAR) as (HLs & HLr & HLt & _ & _ & Hy & Hye).
assert (VIS : VERB_IS_STK = 8224) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre_stk SEGS B (2 * ESTACK) lyc Sc W regs mem md)
  by (apply (v6_pre_at e pos lyc Sc W mem md k regs); [exact HJ | exact Hsp | rewrite Hra; exact Hraok | exact Hgp | exact Htp | lia]).
pose proof HENV as (_ & _ & _ & HAG & _).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False) _ W regs mem VERBS_RECEIVE_STK
    (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc md k (vr_s1 e - vr_sp0 e) raw
    (fun regs' _ => getr regs' 10 = w64 (Z.of_nat (PCs.cspn_len (map (Z_to_bv 8) [32; 9]) (hd [] (Verbs.toks (e_D e)))))) HJ);
  [lia | exact So | lia | lia | assert (VRS : VERBS_RECEIVE_STK = 16992) by reflexivity; lia | exact Hra | intros a [] |].
  apply (STRCSPN fx lyc Sc W regs mem md (hd 0 tp) 0x224c0 (hd [] (Verbs.toks (e_D e))) (map (Z_to_bv 8) [32; 9]) HAG HPRE H10 H11);
  [lia | lia | apply astr_atR_view; exact Hstr | apply astr_atR_view; exact HLs | apply HRD; unfold astr_len; lia
  | apply (amem8_of_blockA SEGS B LAWS lyc Sc W mem md); [exact HAR | exact Hblk | unfold astr_len; lia]
  | apply HLr; unfold astr_len; lia | apply amem8_of_low; unfold astr_len, kLowMemEnd; lia
  | exact HTV | exact HLt | exact (vr_rtrom_ok B W mem (proj1 HENV))]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HW2).
rewrite PVF.cspn_tfirst in HQ2.
apply (HK regs2 mem2 md2 HJ2 HP2 HQ2).
apply (v6_KO_trans e W memc mem mem2 HKO). intros a Ha Hn. apply HW2; [exact Ha | lia | intros []].
Qed.

(* the prefix test of the inline verb_is(remove), reached when the first word is 6 bytes long:
   strncmp(tok[0], "remove %i", 6) *)
Lemma v6_tfirst_word : forall vb, (forall b, In b vb -> bv_unsigned b <> 32 /\ bv_unsigned b <> 9 /\ bv_unsigned b <> 0) ->
PV.tfirst vb = vb.
Proof.
intros vb H. unfold PV.tfirst. induction vb as [|b vb IH]; [reflexivity|]. cbn [PV.upto].
destruct (H b (or_introl eq_refl)) as (H1 & H2 & _).
assert (Hs : PV.is_sep b = false).
{ unfold PV.is_sep. rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity. }
rewrite Hs, IH; [reflexivity|]. intros b' Hb'. apply H. right. exact Hb'.
Qed.
Lemma v6_strncmp_step : forall e pos F q c tp lyc Sc (W : world SEGS) regsc memc mdc k nm rl
  (regs : bvmap 5 word) mem md raw K,
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_copy B e F c tp W memc -> Verbs.toks (e_D e) <> [] ->
Z.of_nat (length (PV.tfirst (hd [] (Verbs.toks (e_D e))))) = 6 ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem md k ->
v6_KO e W memc mem ->
spZ regs = vr_s1 e -> getr regs 1 = raw -> YK0s.ret_ok raw -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 (hd 0 tp) -> getr regs 11 = w64 0x225c0 -> getr regs 12 = w64 6 ->
(forall regs2 mem2 md2,
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
    lyc Sc W mem2 md2 k ->
  aregs_preserved regs regs2 ->
  (getr regs2 10 = w64 0 <-> PV.verb_is_m (hd [] (Verbs.toks (e_D e))) PV.Lit.fmt_remove = true) -> v6_KO e W memc mem2 ->
  SRr SEGS W (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) K) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (SIGMA CS___interceptor_trampoline_strncmp)) mem (seg_rom SEGS)) md) K.
Proof.
intros e pos F q c tp lyc Sc W regsc memc mdc k nm rl regs mem md raw K HC HCP Hne H6 HJ HKO Hsp Hra Hraok Hgp Htp H10 H11 H12 HK.
destruct (v6_mem_at e pos F _ _ _ rl _ _ _ k _ nm _ lyc Sc W regsc memc mdc mem md HC HJ HKO) as (HAR & HENV & Hlo & S1 & S1m & So & H47 & Hwl).
destruct (v6_verb_at e pos F q c tp lyc Sc W regsc memc mdc k nm rl mem md HC HCP Hne HAR HKO Hlo ltac:(lia)) as (Hstr & Hv4 & Hvc & Hblk & Hl8 & HTV & HRD & Hch).
destruct (v6_lit_at W mem lyc Sc md _ _ v6_lit_remove HENV HAR) as (HLs & HLr & HLt & _ & _ & Hy & Hye).
assert (VIS : VERB_IS_STK = 8224) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre_stk SEGS B (2 * ESTACK) lyc Sc W regs mem md)
  by (apply (v6_pre_at e pos lyc Sc W mem md k regs); [exact HJ | exact Hsp | rewrite Hra; exact Hraok | exact Hgp | exact Htp | lia]).
set (vb := hd [] (Verbs.toks (e_D e))) in *.
pose proof (v6_tfirst_word vb Hch) as Tv. rewrite Tv in H6.
assert (Lr : length PV.Lit.fmt_remove = 9%nat) by reflexivity.
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False) _ W regs mem VERBS_RECEIVE_STK
    (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc md k (vr_s1 e - vr_sp0 e) raw
    (fun regs' _ => getr regs' 10 = w64 0 <->
       StrFun.strncmp_model (vb ++ [Z_to_bv 8 0]) (PV.Lit.fmt_remove ++ [Z_to_bv 8 0]) 6 = Some 0) HJ);
  [lia | exact So | lia | lia | assert (VRS : VERBS_RECEIVE_STK = 16992) by reflexivity; lia | exact Hra | intros a [] |].
  apply (STRNCMP fx lyc Sc W regs mem md (hd 0 tp) 0x225c0 6 vb PV.Lit.fmt_remove HPRE H10 H11 H12);
  [lia | lia | lia | apply astr_atR_view; exact Hstr | apply astr_atR_view; exact HLs | apply HRD; unfold astr_len; lia
  | apply (amem8_of_blockA SEGS B LAWS lyc Sc W mem md); [exact HAR | exact Hblk | unfold astr_len; lia]
  | apply HLr; unfold astr_len; try rewrite Lr; lia | apply amem8_of_low; unfold astr_len, kLowMemEnd; lia
  | exact HTV | exact HLt | exact (vr_rtrom_ok B W mem (proj1 HENV))]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HW2).
apply (HK regs2 mem2 md2 HJ2 HP2).
- assert (Nv : Forall (fun b => bv_unsigned b <> 0) vb) by (apply Forall_forall; intros b Hb; exact (proj2 (proj2 (Hch b Hb)))).
  assert (Nf : Forall (fun b => bv_unsigned b <> 0) PV.Lit.fmt_remove) by (repeat constructor; vm_compute; discriminate).
  assert (Hlen : length (PV.tfirst vb) = length (PV.vfirst PV.Lit.fmt_remove)) by (rewrite Tv; change (length (PV.vfirst PV.Lit.fmt_remove)) with 6%nat; lia).
  destruct (PVF.strncmp_verb vb PV.Lit.fmt_remove [] Nv Nf Hlen) as (v & Hv & _ & Hv0).
  change (Z.of_nat (length (PV.vfirst PV.Lit.fmt_remove))) with 6 in Hv.
  rewrite HQ2, Hv. rewrite <- Hv0. split; intros H.
  + injection H as ->. reflexivity.
  + apply Z.eqb_eq in H. subst v. reflexivity.
- apply (v6_KO_trans e W memc mem mem2 HKO). intros a Ha Hn. apply HW2; [exact Ha | lia | intros []].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The message object of the caller's frame and its shadow, kept by the journal of the walk (the S02 kit's
   vr_caller_kept and its helpers, lib/A/Prog/verbs_receive_s02_kit.v, under this file's
   names) *)
Lemma v6_fp_not_shadow : forall e lyc Sc (Wc : world SEGS) memc mdc a,
AR SEGS B lyc Sc Wc memc mdc ->
(forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc)) ->
kLowMemEnd <= a < kHighMemBeg -> ~ inFP (vr_fp e) a.
Proof.
intros e lyc Sc Wc memc mdc a HAR HO Ha (r & Hin & Hr).
unfold vr_fp, VERBS_RECEIVE_PG in Hin. apply in_app_or in Hin as [Hin | Hin].
- unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, REC_SIZE, SC_SIZE, kLowMemEnd, kHighMemBeg in *.
  cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
- apply in_map_iff in Hin as ([p m] & <- & Hpm). cbn [fst snd] in Hr.
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p m HAR (HO _ Hpm)) as (_ & _ & _ & [Hh1 Hh2] & _).
  unfold in_app, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. zlia.
Qed.
Lemma v6_shadow_band : forall x n, 0 <= x -> 0 <= n -> x + n <= alloc_ceiling ->
kLowMemEnd <= shadow_addr x /\ shadow_addr (x + n) < kHighMemBeg.
Proof.
intros x n Hx Hn Hxn. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (H1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (H2 : (x + n) / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; [lia | zlia]).
unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg. zlia.
Qed.
Lemma v6_al8_of_al64 : forall x, x mod 64 = 0 -> x mod 8 = 0.
Proof.
intros x H. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia].
destruct H as [c Hc]. exists (8 * c). lia.
Qed.
Lemma v6_fp_not_frame : forall e ly S (Wc : world SEGS) memc mdc cid pos' a,
AR SEGS B ly S Wc memc mdc ->
(forall pn, In pn (e_O e) -> In pn (ablocks B ly S)) ->
In (cid, pos') (frames S) ->
frame_addr ly cid pos' <= a < frame_addr ly cid pos' + fs_frame_bytes cid ->
~ inFP (vr_fp e) a.
Proof.
intros e ly S Wc memc mdc cid pos' a HAR HO Hin Ha (r & Hr & Hrr).
pose proof (frm_off_imgP B ly S Wc memc mdc cid pos' HAR Hin) as Hoff. unfold off_img in Hoff.
unfold vr_fp, VERBS_RECEIVE_PG in Hr. apply in_app_or in Hr as [Hr | Hr].
- unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, REC_SIZE, SC_SIZE in *.
  cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrr; zlia.
- apply in_map_iff in Hr as ([p m] & <- & Hpm). cbn [fst snd] in Hrr.
  pose proof (sep_block_frame SEGS B LAWS ly S Wc memc mdc p m cid pos' HAR (HO _ Hpm) Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
Qed.
Lemma v6_caller_kept : forall e own lyc Sc (Wc : world SEGS) memc mdc kk a,
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  own lyc Sc Wc memc mdc kk ->
AR SEGS B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) ->
afobj SEGS B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_msg e) 24 ->
(forall pn, In pn (e_O e) -> In pn (ablocks B (e_ly e) (e_S e))) ->
(e_msg e <= a < e_msg e + 24 \/ (exists i, 0 <= i < 3 /\ a = shadow_addr (e_msg e) + i)) ->
rdW Wc memc a = rdW (e_W e) (e_mem e) a.
Proof.
intros e own lyc Sc Wc memc mdc kk a HJ HAR0 ((cid & pos' & Hin & Hcid & Hal & Hlo & Hhi) & Hmod & _) HO Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
pose proof (shadow_mono (frame_addr (e_ly e) cid pos') (e_msg e) Hlo) as M1.
pose proof (shadow_range_end (frame_addr (e_ly e) cid pos') (fs_frame_bytes cid) Hfb) as M2.
pose proof (shadow_mono (e_msg e + 24) (frame_addr (e_ly e) cid pos' + fs_frame_bytes cid) Hhi) as M3.
destruct (frames_bounds SEGS B LAWS (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) cid pos' HAR0 Hin) as (Hf0 & Hfc & Hfapp).
apply F4 with (cid := cid) (pos := pos'); [exact Hin | |].
- destruct Ha as [Ha | (i & Hi & ->)].
  + left. unfold in_zr, frame_rng. cbn [fst snd]. zlia.
  + right. unfold in_zr. cbn [fst snd].
    destruct (frame_al64 SEGS B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) cid pos' HAR0 Hin)
      as (Ha64 & Hb64 & Hge64).
    pose proof (v6_al8_of_al64 _ Ha64) as Hf8. pose proof (v6_al8_of_al64 _ Hb64) as Hs8.
    pose proof (Z.div_mod (e_msg e) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (e_msg e) 8 ltac:(lia)) as P1.
    pose proof (Z.div_mod (frame_addr (e_ly e) cid pos') 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (frame_addr (e_ly e) cid pos') 8 ltac:(lia)) as P2.
    pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D3.
    pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)) as P3.
    unfold shadow_addr, SHADOW_OFF in *. zlia.
- destruct Ha as [Ha | (i & Hi & ->)].
  + exact (v6_fp_not_frame e (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) cid pos' a HAR0 HO Hin ltac:(zlia)).
  + destruct (v6_shadow_band (e_msg e) 24 ltac:(zlia) ltac:(lia) ltac:(zlia)) as [Hb1 Hb2].
    apply (v6_fp_not_shadow e (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) _ HAR0 HO).
    pose proof (shadow_mono (e_msg e) (e_msg e + 24) ltac:(lia)) as Hmo.
    pose proof (Z.div_mod (e_msg e) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (e_msg e) 8 ltac:(lia)) as P1.
    pose proof (Z.div_mod (e_msg e + 24) 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (e_msg e + 24) 8 ltac:(lia)) as P2.
    unfold shadow_addr, SHADOW_OFF in *. zlia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The carry of a boundary state across a frameless program call (verb_is, cl_callS_na): the callee's journal
   keeps the stack above its window, the blocks, the frames and the unowned image bytes; the read-only words, the
   guard cells, the flag byte and the errno cell come back from the record facts at the new state *)
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.

Lemma v6_spares_nil : forall a, fp_spares [] a.
Proof. intros a. apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | apply inFP_nil]. Qed.
Lemma v6_PG_rec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity | unfold REC_SIZE in Ha; cbn; lia]. Qed.
Lemma v6_PG_spill : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity | unfold SC_SIZE in Ha; cbn; lia]. Qed.
Lemma v6_PG_quit : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; right; right; left; reflexivity | cbn; lia]. Qed.

Lemma v6_core_j : forall e pos F tmps sh sl rl rl' R O qv k kmax nm nmax lyc Sc (W : world SEGS) regs mem md W2 regs2 mem2 md2
  mdx ev1,
vr_core B MT e pos F tmps sh sl rl R O qv k kmax nm nmax lyc Sc W regs mem md ->
ajournal SEGS B VERB_IS_STK (vr_s1 e) [] lyc Sc W mem mdx [] lyc Sc W2 mem2 md2 ev1 ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W2 mem2 md2 k ->
Forall (fun ov => 0 <= fst ov <= 1024) sl ->
vr_rv regs2 (vr_base B e ++ rl') ->
vr_core B MT e pos F tmps sh sl rl' R O qv k kmax nm nmax lyc Sc W2 regs2 mem2 md2.
Proof.
intros e pos F tmps sh sl rl rl' R O qv k kmax nm nmax lyc Sc W regs mem md W2 regs2 mem2 md2 mdx ev1
(HJ & Hkk & HMET & Hnm & (HFa & HFl & HFs) & HRV & HSV & HSP & HENV & HREC & HnO & HPERM & HQ) J HJ' Hsl HRV'.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof J as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof (proj1 HJ') as HAR2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (VRS : VERBS_RECEIVE_STK = 16992) by reflexivity. assert (VIS : VERB_IS_STK = 8224) by reflexivity.
pose proof (v6_s1_rng (vr_sp0 e) Hal16) as [S1a S1b]. fold (vr_s1 e) in S1a, S1b.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin4) as (HF0 & HFc & _). rewrite <- HFa in HF0, HFc.
change (fs_frame_bytes 4) with 1024 in HFc.
assert (KS : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (vr_s1 e - VERB_IS_STK <= a < vr_s1 e) -> rdW W2 mem2 a = rdW W mem a)
  by (intros a Ha Hw; apply G1; [exact Ha | exact Hw | apply inFP_nil]).
assert (KF : forall a, (F <= a < F + 1024 \/ shadow_addr F <= a < shadow_addr F + 128) -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. apply (G4 4 pos a Hin4); [|apply inFP_nil]. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- HFa.
  change (fs_frame_bytes 4) with 1024. change (1024 / 8) with 128. exact Ha. }
assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  rdW W2 mem2 a = rdW W mem a)
  by (intros a H1 H2 H3; apply G3; [exact H1 | exact H2 | exact H3 | apply v6_spares_nil]).
assert (KB : forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W mem (p + i))
  by (intros p n i Hb Hi; apply (G2 p n i); [exact Hb | exact Hb | exact Hi | apply inFP_nil]).
unfold vr_core.
split; [exact HJ'|]. split; [exact Hkk|]. split; [exact HMET|]. split; [exact Hnm|].
split.
{ split; [exact HFa|]. split.
  - rewrite (rdword_ext (rdW W mem) (rdW W2 mem2) (F + 1016)); [exact HFl|]. intros kk Hk. apply KF. left. lia.
  - intros i Hi. rewrite (KF (shadow_addr F + Z.of_nat i)); [exact (HFs i Hi)|]. right. lia. }
split; [exact HRV'|].
split.
{ intros j r Hj. pose proof (HSV j r Hj) as H.
  assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length vr_saved_regs] in Hj13.
  intros kk Hkx. rewrite KS; [exact (H kk Hkx) | unfold vr_sp0 in *; lia | unfold vr_sp0 in *; lia]. }
split.
{ unfold vr_spill in *. rewrite Forall_forall in HSP, Hsl |- *. intros [off v] Hin. specialize (HSP _ Hin). specialize (Hsl _ Hin).
  cbn [fst snd] in *. intros kk Hkx. rewrite KS; [exact (HSP kk Hkx) | unfold vr_sp0 in *; lia | unfold vr_sp0 in *; lia]. }
split.
{ destruct HENV as (HRO & _).
  assert (HRO2 : arodata_okP SEGS RLO RHI B (rdW W2 mem2)).
  { intros a Hro Ho He. rewrite KI; [exact (HRO a Hro Ho He) | | exact Ho | exact He].
    destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]. }
  pose proof (ROA _ _ _ _ _ HAR2 HRO2) as HROK2.
  destruct (RECC _ _ _ _ _ HAR2) as (Hfl & Hag & Her).
  split; [exact HRO2|]. split; [exact (v6_got_of_ro _ HROK2)|]. split; [exact HROK2|].
  split; [exact Hag|]. split; [exact Hfl | exact Her]. }
split.
{ apply (rec_repA_agree B lyc Sc lyc Sc _ _ R O HREC (fun pn _ Hb => Hb)).
  - intros kk Hk2. destruct (PROGU (A_G_REC + kk) (v6_PG_rec (A_G_REC + kk) ltac:(clear - Hk2; split; lia))) as (H1 & H2 & H3).
    exact (KI _ H1 H2 H3).
  - intros kk Hk2. destruct (PROGU (A_REC_SPILL + kk) (v6_PG_spill (A_REC_SPILL + kk) ltac:(clear - Hk2; split; lia)))
      as (H1 & H2 & H3). exact (KI _ H1 H2 H3).
  - intros [p n] Hpn kk Hk2. cbn [fst snd] in *.
    pose proof (rec_repA_in_blocks B _ _ _ _ _ _ HREC Hpn) as Hb.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hb) as (_ & _ & _ & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hr]. exact (KB p n kk Hb ltac:(lia)). }
split; [exact HnO|]. split; [exact HPERM|].
intros kk Hkx. destruct (PROGU (A_G_QUITTING + Z.of_nat kk) (v6_PG_quit (A_G_QUITTING + Z.of_nat kk) ltac:(clear - Hkx; split; lia)))
  as (H1 & H2 & H3).
rewrite (KI _ H1 H2 H3). exact (HQ kk Hkx).
Qed.

Lemma v6_lc_j : forall e pos F q c tp lyc Sc (W : world SEGS) mem md W2 mem2 md2 ev1,
AR SEGS B lyc Sc W mem md -> In (vr_lb e q) (ablocks B lyc Sc) -> In (vr_cb e c) (ablocks B lyc Sc) ->
In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos -> Z.of_nat (length (e_D e)) = e_n e ->
ajournal SEGS B VERB_IS_STK (vr_s1 e) [] lyc Sc W mem md [] lyc Sc W2 mem2 md2 ev1 ->
vr_line B e q W mem -> vr_copy B e F c tp W mem -> vr_line B e q W2 mem2 /\ vr_copy B e F c tp W2 mem2.
Proof.
intros e pos F q c tp lyc Sc W mem md W2 mem2 md2 ev1 HAR Hlb Hcb Hin4 HFa Hn J (Hfr & Hstr) (Hfc & Hm8 & Hlen & Hptr & Hw).
pose proof J as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
assert (KF : forall a, F <= a < F + 1024 -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. apply (G4 4 pos a Hin4); [|apply inFP_nil]. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- HFa.
  change (fs_frame_bytes 4) with 1024. exact Ha. }
assert (KB : forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W mem (p + i))
  by (intros p n i Hb Hi; apply (G2 p n i); [exact Hb | exact Hb | exact Hi | apply inFP_nil]).
unfold vr_lb, vr_cb in *. cbn [fst snd] in *.
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hlb) as (_ & _ & _ & _ & _ & _ & Hqn); lia)) as [_ Rq].
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [_ Rc].
pose proof (v6_line_le (e_D e) (e_n e) Hn) as Ll.
split.
- split; [exact Hfr|]. apply (astr_atR_agree _ _ q _ (vr_l (e_n e) (e_D e) + 1) Hstr); [lia|].
  intros kk Hk. apply (KB q _ kk Hlb). lia.
- split; [exact Hfc|]. split; [exact Hm8|]. split; [exact Hlen|]. split.
  + intros i p Hi. pose proof (Hptr i p Hi) as H.
    assert (Hil : (i < length tp)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    pose proof (Verbs.toks_length (e_D e)). rewrite Hlen in Hil.
    intros kk Hkk. rewrite KF; [exact (H kk Hkk) | lia].
  + intros i p w Hi Hwi. destruct (Hw i p w Hi Hwi) as (Hs & Hl8 & Hcp & Hpe).
    split; [|split; [exact Hl8 | split; [exact Hcp | exact Hpe]]].
    apply (astr_atR_agree _ _ p w (Z.of_nat (length w) + 1) Hs); [lia|].
    intros kk Hk. replace (p + kk) with (c + (p - c + kk)) by lia. apply (KB c _ (p - c + kk) Hcb). lia.
Qed.

(* verb_is(tok[0], "quit"): verb_is's contract (frameless, PaNoChain's cl_callS_na); the format through astr_argA's
   read-only branch (its bytes in the read-only range by vr_ent's cmd_ro_in, unowned by the record, the record's
   shadow checks by computation) *)
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
(* verb_is's contract in the statement's form since pass 4 (verbs_receive_c.v:226): at every FP state *)
Hypothesis TVERB_IS : forall fx0 : YK11.FPState, @tverb_is_spec fx0 rc SK PI B MT.

Lemma v6_quit_ro : forall i, 0 <= i < 5 -> ~ Exists (in_zr (0x227e0 + i)) (as_owned_static B) /\
~ (as_errno B <= 0x227e0 + i < as_errno B + 4).
Proof.
intros i Hi. rewrite (AF0m.ts_owned B HB), (AF0m.ts_errno B HB). split.
- assert (Hall : forallb (fun r => (fst r + snd r <=? 0x227e0) || (0x227e5 <=? fst r)) AF0m.Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. intros Hex. apply Exists_exists in Hex as (r & Hr & Hz).
  specialize (Hall r Hr). unfold in_zr in Hz. apply orb_true_iff in Hall as [H | H]; apply Z.leb_le in H; lia.
- unfold AF0m.TFIB_ERRNO. lia.
Qed.

Lemma v6_vi_step : forall e pos F q c tp lyc Sc (W : world SEGS) regsc memc mdc k nm rl
  (regs : bvmap 5 word) mem md raw K,
vr_ent B MT e ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_copy B e F c tp W memc -> Verbs.toks (e_D e) <> [] ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem md k ->
v6_KO e W memc mem -> st_nev Sc + EV_VERB_IS <= EV_MAX ->
spZ regs = vr_s1 e -> getr regs 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 (hd 0 tp) -> getr regs 11 = w64 0x227e0 ->
(forall W2 regs2 mem2 md2,
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
    lyc Sc W2 mem2 md2 k ->
  ajournal SEGS B VERB_IS_STK (vr_s1 e) [] lyc Sc W mem md [] lyc Sc W2 mem2 md2 EV_VERB_IS ->
  aregs_preserved regs regs2 ->
  getr regs2 10 = w64 (if PV.verb_is_m (hd [] (Verbs.toks (e_D e))) PV.Lit.fmt_quit then 1 else 0) ->
  SRr SEGS W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) K) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (SIGMA CS_verb_is)) mem (seg_rom SEGS)) md) K.
Proof.
intros e pos F q c tp lyc Sc W regsc memc mdc k nm rl regs mem md raw K He HC HCP Hne HJ HKO Hev
  Hsp Hra Hraok Hra4 Hgp Htp H10 H11 HK.
destruct (v6_mem_at e pos F _ _ _ rl _ _ _ k _ nm _ lyc Sc W regsc memc mdc mem md HC HJ HKO) as (HAR & HENV & Hlo & S1 & S1m & So & H47 & Hwl).
destruct (v6_verb_at e pos F q c tp lyc Sc W regsc memc mdc k nm rl mem md HC HCP Hne HAR HKO Hlo ltac:(lia)) as (Hstr & Hv4 & Hvc & Hblk & Hl8 & HTV & HRD & Hch).
destruct (v6_lit_at W mem lyc Sc md _ _ v6_lit_quit HENV HAR) as (HLs & HLr & HLt & HLra & HLhv & Hy & Hye).
destruct (v6_ent_ro e He) as (HRIN & HVO).
pose proof HENV as (HROD & _ & HROK & HAG & _).
assert (VIS : VERB_IS_STK = 8224) by reflexivity. assert (VRS : VERBS_RECEIVE_STK = 16992) by reflexivity.
rewrite (SIGP CS_verb_is) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_verb_is) with AF_verb_is.
eapply SRr_bind.
{ apply (cl_callS_na B LAWS W regs mem _ VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(4, pos)] lyc Sc md k VERB_IS_STK [] EV_VERB_IS (vr_s1 e - vr_sp0 e) raw
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       getr regs2 10 = w64 (if PV.verb_is_m (hd [] (Verbs.toks (e_D e))) PV.Lit.fmt_quit then 1 else 0) /\
       Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ ly2 = lyc /\ S2 = Sc) HJ);
  [lia | exact So | lia | lia | lia | exact Hgp | exact Htp | exact Hra | exact Hraok | exact Hra4 | |
   intros a Ha; exfalso; exact (inFP_nil a Ha)].
  intros HPRE.
  eapply SRr_mono.
  { apply (TVERB_IS fx lyc Sc W regs mem md (hd 0 tp) 0x227e0 (hd [] (Verbs.toks (e_D e))) PV.Lit.fmt_quit HPRE HROD H10
      ltac:(lia) H11 ltac:(lia) Hblk Hstr ltac:(unfold LMAX; lia)).
    - split; [lia|]. split; [exact HLs|]. split; [unfold LMAX; cbn; lia|]. right.
      split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | apply In_of_existsb; vm_compute; reflexivity]]].
      intros i Hi. change (Z.of_nat (length PV.Lit.fmt_quit) + 1) with 5 in Hi.
      split; [|exact (v6_quit_ro i Hi)].
      unfold cmd_ro_in in HRIN. decompose [and] HRIN.
      match goal with H : forall i, 0 <= i < 5 -> in_roP SEGS RLO RHI (0x227e0 + i) |- _ => exact (H i Hi) end.
    - exact HLt.
    - exact HROK.
    - exact HVO.
    - exact Hev. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HQ).
  exists ly2, S2, regs2, mem2, md2. split; [rewrite Hra; reflexivity|].
  split; [exact HJ1|]. split; [exact HP | exact HQ]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & (HQ & _ & -> & ->)).
unfold EV_VERB_IS in HJ2. rewrite Z.add_0_r in HJ2.
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
exact (HK W2 regs2 mem2 md2 HJ2 HJc HP HQ).
Qed.

End e.
End f.
End d.
