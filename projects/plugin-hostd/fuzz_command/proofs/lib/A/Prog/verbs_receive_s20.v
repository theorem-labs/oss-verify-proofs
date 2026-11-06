(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the segment S20 (chain_clear, 0x8dce0-0x8dd04) of the walk of
   verbs_receive on the ASan build of plugin-hostd/fuzz_command (lib/A/Prog/verbs_receive_iface.v vr_s20_stmt). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdAddr CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c answer_c answer_code_c hand_back_c arg_i_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_live verbs_receive_s20_k PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* the symbolic states of S20: at 0x8dce0 the spill word s1+56 (the copy c, atom 32) and on the two-word path tok[1]
   (atom 33); at 0x8dcf8, number's return, the result cell s1+84 (4 bytes, atom 32) when the word was a number *)
Definition r_sp20 : YP09.region := YP09.mkRegion (Some 9%nat) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition r_tok20 : YP09.region := YP09.mkRegion (Some 22%nat) 8 16 8 8 [YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition ss20r : sstate := mkSS 30716 sr_atoms [r_sp20] None (mkFacts [] [] []).
Definition ss20t : sstate := mkSS 30716 sr_atoms [r_sp20; r_tok20] None (mkFacts [] [] []).
Definition r_out20 : YP09.region := YP09.mkRegion (Some 9%nat) 84 88 84 84 [YP09.mkChunk 84 (CVal 4 (SOff 32 0))].
Definition ss20s : sstate := mkSS 30740 sr_atoms [r_out20] None (mkFacts [] [] []).

(* the model: the route RChclear; with one argument that is a number, sup_chain_clear(id); else reject *)
Lemma chclear_two : forall R D v a, Verbs.toks D = [v; a] -> VRR.route (Verbs.toks D) = VRR.RChclear ->
  match Verbs.number_m a with
  | Some id => vr_h R D = (sup_chain_clear_m R id, false) /\ vr_k1 R D = 2 + EV_SUP_CHAIN_CLEAR R
  | None => vr_h R D = (R, resp (-902), false) /\ vr_k1 R D = 2 + EV_SUP_RESP
  end.
Proof.
intros R D v a T Hr. rewrite T in Hr.
pose proof (route_chclear_v v [a] Hr) as Hv.
assert (Hc1 : Verbs.list_eqb v Verbs.Lit.verb_chain = false) by (rewrite Hv; vm_compute; reflexivity).
assert (Hc2 : Verbs.list_eqb v Verbs.Lit.verb_pin_set = false) by (rewrite Hv; vm_compute; reflexivity).
assert (St : vr_st D = VRR.plan_at VRR.RChclear atoi_a (Verbs.line D) [v; a]).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. rewrite Hr. reflexivity. }
cbn [VRR.plan_at] in St.
destruct (Verbs.number_m a) as [id|] eqn:Enm; rewrite ?Enm in St.
- split.
  + unfold vr_h. rewrite St. reflexivity.
  + unfold vr_k1. rewrite St, T. rewrite (ev_route_not_cp _ _ _ _ _ Hc1 Hc2). reflexivity.
- split.
  + unfold vr_h. rewrite St. reflexivity.
  + unfold vr_k1. rewrite St, T. rewrite (ev_route_not_cp _ _ _ _ _ Hc1 Hc2). reflexivity.
Qed.

Lemma chclear_rej : forall R D, VRR.route (Verbs.toks D) = VRR.RChclear -> Verbs.toks D <> [] ->
  length (Verbs.toks D) <> 2%nat ->
  vr_h R D = (R, resp (-902), false) /\ vr_k1 R D = 2 + EV_SUP_RESP.
Proof.
intros R D Hr Hne Hl. destruct (Verbs.toks D) as [|v args] eqn:T; [congruence|].
pose proof (route_chclear_v v args Hr) as Hv.
assert (Hc1 : Verbs.list_eqb v Verbs.Lit.verb_chain = false) by (rewrite Hv; vm_compute; reflexivity).
assert (Hc2 : Verbs.list_eqb v Verbs.Lit.verb_pin_set = false) by (rewrite Hv; vm_compute; reflexivity).
assert (St : vr_st D = Verbs.reject).
{ unfold vr_st, Verbs.receive. rewrite T. cbv beta iota. cbn [fst].
  rewrite VRR.plan_route by discriminate. rewrite Hr. cbn [VRR.plan_at].
  destruct args as [|a [|b args]]; [reflexivity | cbn in Hl; lia | reflexivity]. }
split.
- unfold vr_h. rewrite St. reflexivity.
- unfold vr_k1. rewrite St, T. rewrite (ev_route_not_cp _ _ _ _ _ Hc1 Hc2). reflexivity.
Qed.

Lemma hd_ntok_d3c : forall nt, (1 <= nt)%nat -> vr_hd_ntok 0x8dd3c nt.
Proof. intros nt H. unfold vr_hd_ntok. exact H. Qed.
Lemma pr_ntok_d34 : forall nt, (1 <= nt)%nat -> vr_pr_ntok 0x8dd34 nt.
Proof. intros nt H. unfold vr_pr_ntok. exact H. Qed.

(* a register of a boundary list: kept by the run (KR) or the value the run gave it *)
Ltac s20_rv HS KR Hrv fin :=
  lazymatch goal with
  | |- getr _ ?r = w64 _ =>
    first [ rewrite KR by (cbn; tauto); apply (vk_rv_get _ _ _ _ Hrv); apply in_or_app;
            first [left; cbn; tauto | right; cbn; tauto]
          | let Hx := fresh "Hx" in prreg HS r Hx; rewrite Hx; clear Hx;
            first [fin | (rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; fin)] ]
  end.

Section dt. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section ft.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section et.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the jump 0x8dd04 -> 0x8dd3c after sup_chain_clear returned, and the handler's state there (statement pass 4:
   sup_chain_clear's post is FP-existential, so this runs at the FP state it returns at; proved in its own section, it
   holds at every FP state) *)
Lemma s20_join : forall e pos F q c tp tq R1 t k nm ly2 S2 W2 regs2 mem2 md2 Ox id,
  Verbs.toks (e_D e) <> [] ->
  vr_h (e_R e) (e_D e) = (sup_chain_clear_m (e_R e) id, false) -> sup_chain_clear_m (e_R e) id = (R1, t) ->
  k + EV_SUP_CHAIN_CLEAR (e_R e) <= vr_k1 (e_R e) (e_D e) -> nm + 3 <= VR_NM_HD -> 4096 <= tq ->
  astr_atR (rdW W2 mem2) tq t ->
  vr_core B MT e pos F ((tq, Z.of_nat (length t) + 1) :: [vr_lb e q; vr_cb e c]) vr_sh2 (vr_sl3 F q c)
    [(10, tq); (18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)]
    R1 Ox (e_q0 e) (k + EV_SUP_CHAIN_CLEAR (e_R e)) (vr_k1 (e_R e) (e_D e)) (nm + 3) VR_NM_HD ly2 S2 W2 regs2 mem2 md2 ->
  vr_line B e q W2 mem2 -> vr_copy B e F c tp W2 mem2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 30752)) mem2 (seg_rom SEGS)) md2) (vr_athd B MT 0x8dd3c e).
Proof.
intros e pos F q c tp tq R1 t k nm ly2 S2 W2 regs2 mem2 md2 Ox id Hne Hvh Em Hkk Hnn Htq Hstr HC2 HL2 HCP2.
pose proof HC2 as (HJ2 & _ & _ & _ & _ & Hrv2 & _).
apply (vk_jmp B 30752 30808 ltac:(lia) ltac:(vm_compute; reflexivity) W2 regs2 mem2 md2 _ _ _ _ _ _ _ _ _ _
  ly2 S2 _ HJ2).
intros regs3 md3 Er HJ3.
unfold vr_athd, vr_hd.
exists tq, Ox, pos, F, q, c, tp, ly2, S2, regs3, mem2, md3, (k + EV_SUP_CHAIN_CLEAR (e_R e)), (nm + 3).
assert (EX : vr_x (e_R e) (e_D e) = t) by (unfold vr_x; rewrite Hvh, Em; reflexivity).
assert (ER1 : vr_R1 (e_R e) (e_D e) = R1) by (unfold vr_R1; rewrite Hvh, Em; reflexivity).
assert (EQV : vr_qv e = e_q0 e) by (unfold vr_qv, vr_quit; rewrite Hvh; reflexivity).
split; [unfold cfg_at, w64; replace (vr_pc 0x8dd3c) with (BASE + 30808) by (unfold vr_pc, AF_verbs_receive; lia);
  reflexivity|].
split; [apply hd_ntok_d3c; destruct (Verbs.toks (e_D e)); [congruence | cbn [length]; lia]|].
split; [lia|].
split; [rewrite EX; exact Hstr|].
rewrite EX, ER1, EQV.
split; [|split; [exact HL2 | exact HCP2]].
eapply (vk_regs B MT); [exact HC2 | exact HJ3 |].
apply (vk_rv_kept regs2 _ _ Hrv2). intros r v _. apply Er.
Qed.

End et.
End ft.
End dt.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma val_mem_mod32 : forall m a v, val_mem SEGS m a 4 v -> val_mem SEGS m a 4 (v mod 2 ^ 32).
Proof.
intros m a v H k Hk. rewrite (H k Hk). do 2 f_equal.
lazymatch goal with |- ?f v ?w k = ?f (v mod 2 ^ 32) ?w k => let g := eval red in f in change (g v w k = g (v mod 2 ^ 32) w k) end.
cbv beta. change (8 * Z.of_nat 4) with 32. rewrite Zmod_mod. reflexivity.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the callees' contracts (verbs_receive_c.v:197, 205) and the named record facts *)
Hypothesis TNUMBER : forall fx0 : YK11.FPState, @tnumber_spec fx0 rc SK PI B MT.
Hypothesis TSUP_CHAIN_CLEAR : forall fx0 : YK11.FPState, @tsup_chain_clear_spec fx0 rc SK PI B MT.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis ROA : vr_ro_of_aro B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).

(* the refusal stub 0x8dd34 (sup_resp(-902) in S29), reached with the recorder untouched *)
Lemma s20_pr : forall e pos F q c tp k nm lyc Sc W regsc memc mdc,
  vr_ent B MT e -> Verbs.toks (e_D e) <> [] ->
  vr_h (e_R e) (e_D e) = (e_R e, resp (-902), false) -> vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_RESP ->
  vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
    [(18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)]
    (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
  vr_line B e q W memc -> vr_copy B e F c tp W memc ->
  vr_atpr B MT 0x8dd34 e W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + 30800)) memc (seg_rom SEGS)) mdc).
Proof.
intros e pos F q c tp k nm lyc Sc W regsc memc mdc He Hne Hvh Hk1 HC HL HCP.
unfold vr_atpr, vr_pr.
exists (-902), (e_R e), (e_O e), pos, F, q, c, tp, lyc, Sc, regsc, memc, mdc, k, nm.
split; [unfold cfg_at, w64; replace (vr_pc 0x8dd34) with (BASE + 30800) by (unfold vr_pc, AF_verbs_receive; lia);
  reflexivity|].
split; [intros _; reflexivity|]. split; [lia|]. split; [exact Hvh|]. split; [exact Hne|].
split; [apply pr_ntok_d34; destruct (Verbs.toks (e_D e)); [congruence | cbn [length]; lia]|].
split; [|split; [exact HL | exact HCP]].
change (vr_rl_pr e F q c 0x8dd34 (-902))
  with [(18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)].
eapply (vk_loosen B MT); [exact HC | rewrite Hk1; lia | unfold VR_NM_PRE, VR_NM_PR; lia].
Qed.

Lemma vr_s20 : vr_s20_stmt B MT.
Proof.
intros e W cf He HP.
destruct HP as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & Hcf & Hroute & Hne & HC & HL & HCP).
pose proof HC as (HJ & Hk & _ & Hnm & (EF & _ & _) & Hrv & _ & Hsp & _ & Hrec & _ & Hperm & _).
pose proof He as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HDn & _ & _ & _ & _ & _ & Hcalls & _).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (vr_s1_bounds e) as Hs1b.
assert (HV : 224 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hfr4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hfr4) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
pose proof (shadow_addr_bounds F ltac:(lia)) as HshF.
assert (Hnt : 0 <= vr_ntok (e_D e) <= 64).
{ unfold vr_ntok, Verbs.toks, Verbs.line_words_max. rewrite length_firstn. lia. }
assert (R9 : getr regsc (Z_to_bv 5 9) = w64 (vr_s1 e))
  by (apply (vk_rv_get regsc _ _ _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R21 : getr regsc (Z_to_bv 5 21) = w64 (vr_ntok (e_D e)))
  by (apply (vk_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn; tauto).
assert (R22 : getr regsc (Z_to_bv 5 22) = w64 (F + 32))
  by (apply (vk_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn; tauto).
assert (Hav56 : aval_mem (rdW W memc) (vr_s1 e + 56) 8 c).
{ unfold vr_spill in Hsp; rewrite Forall_forall in Hsp. exact (Hsp (56, c) ltac:(unfold vr_sl3; cbn; tauto)). }
pose proof (vk_k1_le (e_R e) (e_D e)) as Hk1ev.
pose proof (vk_bsum2 B MT e q c He) as Hbs.
pose proof HCP as (_ & (_ & Htkl & _ & _)).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. right; left; reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4096 & Hcc & _).
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrsc.
subst cf. unfold cfg_at, w64.
replace (vr_pc (vr_route_pc VRR.RChclear)) with (BASE + 30716) by (unfold vr_pc, vr_route_pc, AF_verbs_receive; lia).
set (rl1 := [(18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)]).
destruct (Nat.eq_dec (length (Verbs.toks (e_D e))) 2) as [H2 | H2].
- (* two words: number(tok[1], s1+84) *)
  destruct (Verbs.toks (e_D e)) as [|v [|a [|b rest]]] eqn:T; try (cbn in H2; lia).
  pose proof (chclear_two (e_R e) (e_D e) v a T ltac:(rewrite T; exact Hroute)) as Hmod.
  assert (Hne' : Verbs.toks (e_D e) <> []) by (rewrite T; discriminate).
  assert (HlenP : length tp = 2%nat) by (rewrite Htkl; reflexivity).
  destruct tp as [|p0 [|p1 [|p2 tp']]]; cbn in HlenP; try lia.
  destruct (vk_tok_arg B e F c [p0; p1] lyc Sc W memc mdc (e_O e) [vr_lb e q; vr_cb e c] 1 p1 a HAR Hperm
    (or_intror (or_introl eq_refl)) HCP eq_refl ltac:(rewrite T; reflexivity))
    as (Hblk & Hap & Hstra & Hlena & Hp1m & Hp14 & Hp1c).
  set (E := Eimg (Ereg regsc [w64 c; w64 p1])).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc [w64 c; w64 p1]) E) by (subst E; apply vk_env_agree).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  assert (E9 : bv_unsigned (ew E 9%nat) = vr_s1 e).
  { subst E. rewrite (ew_Eimg_Ereg_nat regsc _ 9%nat (Z_to_bv 5 9) eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
  assert (E22 : bv_unsigned (ew E 22%nat) = F + 32).
  { subst E. rewrite (ew_Eimg_Ereg_nat regsc _ 22%nat (Z_to_bv 5 22) eq_refl), R22. unfold w64. apply unsigned_lit_small. lia. }
  assert (E32 : ew E 32%nat = w64 c).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    pose proof (ew_Ereg_extra regsc [w64 c; w64 p1] 0%nat) as HH. cbn [Nat.add nth] in HH. exact HH. }
  assert (E33 : ew E 33%nat = w64 p1).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    pose proof (ew_Ereg_extra regsc [w64 c; w64 p1] 1%nat) as HH. cbn [Nat.add nth] in HH. exact HH. }
  assert (HS : st_ok_pi SEGS VAL E ss20t (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 30716)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss20t. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor]].
      + unfold r_sp20, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (vr_s1 e) 56 8%N (SOff 32 0) c).
        * cbn [sv_denot]. rewrite E32. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        * cbn. lia.
        * apply aval_val_mem. exact Hav56.
      + unfold r_tok20, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (F + 32) 8 8%N (SOff 33 0) p1).
        * cbn [sv_denot]. rewrite E33. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        * cbn. lia.
        * apply aval_val_mem. replace (F + 32 + 8) with (F + 32 + 8 * Z.of_nat 1) by lia. exact Hp1m.
    - cbn [pairwise_disjoint all_disjoint]. split; [|split; exact I]. split; [|exact I].
      unfold extent_disjoint, r_sp20, r_tok20. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E22. right. lia.
    - split; [exact I | split; exact I]. }
  (* 0x8dce0: li a0,2; ld s3,56(s1) *)
  paj_run_shc RUNP RUNC HS HJ.
  { unfold ss20t; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  assert (Hro1 : rs_read_only (ss_mem ss20t) = true) by (vm_compute; reflexivity).
  pose proof (frame_of_read_only _ _ _ _ Hro1 HF) as Hm1. clear HF HFr HG.
  (* 0x8dce8: bne s5,a0,0x8dd34 *)
  psrr_branch_pi RUNP BR HS.
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    unfold vr_ntok in Hc. rewrite T in Hc. vm_compute in Hc. discriminate Hc.
  + (* 0x8dcec: ld a0,8(s6); addi a1,s1,84; jal number *)
    clear Hc.
    paj_run_shc RUNP RUNC HS HJ.
    { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
        let rs' := eval vm_compute in rs in change rs with rs' end.
      apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
    set (mdv2 := with_vm_backing (m_vm_lazy mdv) mat0 mdv) in *. clearbody mdv2.
    lazymatch goal with
    | Hfx : frame_of _ ?rs (ms_mem _) (ms_mem _) |- _ =>
      assert (Hro2 : rs_read_only rs = true) by (vm_compute; reflexivity);
      pose proof (frame_of_read_only _ _ _ _ Hro2 Hfx) as Hm2
    end.
    clear HF HFr HG.
    assert (Hmm : ms_mem ms0 = memc) by (rewrite Hm2; exact Hm1).
    rewrite Hmm in HJ.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    pose proof (vk_kept_regs E _ _ regsc [w64 c; w64 p1]
      [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    assert (Q10' : getr (ms_regs ms0) 10 = w64 p1)
      by (rewrite Q10; first [exact E33 | (rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E33)]).
    assert (Q11' : getr (ms_regs ms0) 11 = w64 (vr_s1 e + 84)) by (rewrite Q11; unfold w64; rewrite E9; reflexivity).
    assert (Hrv1 : vr_rv (ms_regs ms0) (vr_base B e ++ rl1)).
    { unfold vr_rv, vr_base, rl1. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      s20_rv HS KR Hrv ltac:(first [exact E32 | exact E33]). }
    assert (HC1 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl1
      (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs ms0) memc mdv2)
      by (eapply (vk_regs B MT); [exact HC | exact HJ | exact Hrv1]).
    pmkst HS. rewrite Hmm.
    rewrite (SIGP CS_number ltac:(unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
    change (cmd_af CS_number) with AF_number.
    assert (Hkev0 : k <= ev_vr (e_R e) (e_D e)).
    { assert (Hk2 : 2 <= vr_k1 (e_R e) (e_D e)).
      { revert Hmod. destruct (Verbs.number_m a); intros [_ ->].
        - unfold EV_SUP_CHAIN_CLEAR, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP. pose proof (vk_rsf_nonneg (e_R e)). lia.
        - unfold EV_SUP_RESP, EV_XSTRDUP. lia. }
      lia. }
    apply (vk_number B MT RRO RECC PROGU ROA HB MTFL (TNUMBER fx) e pos F q c [p0; p1] [vr_lb e q; vr_cb e c] rl1
      (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W (ms_regs ms0) memc mdv2 p1 a 30740
      (fun t => [(10, t); (18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)]) _
      He HC1 HL HCP (or_introl eq_refl) (or_intror (or_introl eq_refl)) Q1 ltac:(lia) eq_refl Q10' ltac:(lia) Q11'
      Hblk Hstra Hlena Hkev0).
    * intros t r0 v0 Hin. cbn [In] in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]; injection E1 as <- <-;
        [left; split; reflexivity | right; split; [unfold acallee_saved; lia | unfold rl1; cbn; tauto] ..].
    * (* after number: 0x8dcf8 beqz a0,0x8dd34 *)
      intros ly2 S2 W2 regs2 mem2 md2 HC2 HL2 HCP2 Hnum.
      destruct (Verbs.number_m a) as [id|] eqn:Enm.
      { (* a number: lw a0,84(s1); jal sup_chain_clear *)
        destruct Hmod as [Hvh Hk1].
        pose proof (Verbs.number_m_range a id Enm) as Hidr.
        pose proof (Hnum id eq_refl) as Hout.
        pose proof HC2 as (HJ2 & _ & _ & _ & _ & Hrv2 & _).
        assert (R92 : getr regs2 (Z_to_bv 5 9) = w64 (vr_s1 e))
          by (apply (vk_rv_get regs2 _ _ _ Hrv2); apply in_or_app; left; cbn; tauto).
        assert (R102 : getr regs2 (Z_to_bv 5 10) = w64 1)
          by (apply (vk_rv_get regs2 _ _ _ Hrv2); apply in_or_app; right; cbn; tauto).
        set (E2 := Eimg (Ereg regs2 [w64 (id mod 2 ^ 32)])).
        assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
        assert (HAE2 : env_agree 32 (Ereg regs2 [w64 (id mod 2 ^ 32)]) E2) by (subst E2; apply vk_env_agree).
        assert (E92 : bv_unsigned (ew E2 9%nat) = vr_s1 e).
        { subst E2. rewrite (ew_Eimg_Ereg_nat regs2 _ 9%nat (Z_to_bv 5 9) eq_refl), R92.
          unfold w64. apply unsigned_lit_small. lia. }
        assert (E322 : ew E2 32%nat = w64 (id mod 2 ^ 32)).
        { subst E2. rewrite Eimg_low by (unfold A_TEXT; lia).
          pose proof (ew_Ereg_extra regs2 [w64 (id mod 2 ^ 32)] 0%nat) as HH. cbn [Nat.add nth] in HH. exact HH. }
        assert (E102 : ew E2 10%nat = Z_to_bv 64 1)
          by (subst E2; rewrite (ew_Eimg_Ereg_nat regs2 _ 10%nat (Z_to_bv 5 10) eq_refl); exact R102).
        pose proof (Z.mod_pos_bound id (2 ^ 32) ltac:(lia)) as Hidm.
        assert (HS2 : st_ok_pi SEGS VAL E2 ss20s
          (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 30740)) mem2 (seg_rom SEGS)))).
        { rewrite restrict_mkst_fx. unfold ss20s. apply pa_entry_st_ok_full.
          - subst E2. apply regs_ok_Eimg_Ereg.
          - vm_compute. reflexivity.
          - constructor; [|constructor]. unfold r_out20, region_ok.
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
            rewrite E92. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
            constructor; [|constructor].
            apply (chunk_ok_val SEGS E2 _ (vr_s1 e) 84 4%N (SOff 32 0) (id mod 2 ^ 32)).
            + cbn [sv_denot]. rewrite E322. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
            + change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
            + cbn. lia.
            + apply val_mem_mod32. apply aval_val_mem. exact Hout.
          - cbn. tauto.
          - split; [exact I | split; exact I]. }
        paj_run_shc RUNP RUNC HS2 HJ2.
        { unfold ss20s; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
        lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdv3 := m) in *; clearbody mdv3 end.
        assert (Hro3 : rs_read_only (ss_mem ss20s) = true) by (vm_compute; reflexivity).
        lazymatch goal with
        | Hfx : frame_of _ _ _ (ms_mem _) |- _ =>
          pose proof (frame_of_read_only _ _ _ _ Hro3 Hfx) as Hm3; cbn [ms_mem mkst] in Hm3
        end.
        clear HF HFr HG.
        psrr_branch_pi RUNP BR HS2.
        { exfalso. rewrite branch_eq_U in Hc. rewrite (U_atom E2 10 1 E102) in Hc by lia.
          change (U E2 (SLit 0)) with 0 in Hc. vm_compute in Hc. discriminate Hc. }
        clear Hc.
        paj_run_shc RUNP RUNC HS2 HJ2.
        { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
            let rs' := eval vm_compute in rs in change rs with rs' end.
          apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
        lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdv4 := m) in *; clearbody mdv4 end.
        lazymatch goal with
        | Hfx : frame_of _ ?rs (ms_mem _) (ms_mem _) |- _ =>
          assert (Hro4 : rs_read_only rs = true) by (vm_compute; reflexivity);
          pose proof (frame_of_read_only _ _ _ _ Hro4 Hfx) as Hm4
        end.
        clear HF HFr HG.
        lazymatch type of Hm4 with ms_mem ?m4 = ms_mem ?m3 =>
          assert (Hmm2 : ms_mem m4 = mem2) by (rewrite Hm4; exact Hm3) end.
        rewrite Hmm2 in HJ2.
        prreg HS2 (1%bv : bv 5) Q1b. prreg HS2 (10%bv : bv 5) Q10b.
        pose proof (vk_kept_regs E2 _ _ regs2 [w64 (id mod 2 ^ 32)] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 27] HS2 HAE2
          ltac:(vm_compute; reflexivity)) as KR2. cbn [ms_regs restrict] in KR2.
        lazymatch type of Q1b with getr (ms_regs ?m4) _ = _ => rename m4 into ms4 end.
        assert (Hrv4 : vr_rv (ms_regs ms4) (vr_base B e ++ rl1)).
        { unfold vr_rv, vr_base, rl1. cbn [app].
          repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          (rewrite KR2 by (cbn; tauto); apply (vk_rv_get _ _ _ _ Hrv2); apply in_or_app;
           first [left; cbn; tauto | right; cbn; tauto]). }
        assert (Q10b' : getr (ms_regs ms4) 10 = w64 id).
        { rewrite Q10b. unfold w64.
          first [ rewrite E322; unfold w64; exact (vk_lw_val id ltac:(lia))
                | (cbn [sv_denot]; rewrite E322; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact (vk_lw_val id ltac:(lia))) ]. }
        assert (HC4 : vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl1
          (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE ly2 S2 W2 (ms_regs ms4) mem2 mdv4)
          by (eapply (vk_regs B MT); [exact HC2 | exact HJ2 | exact Hrv4]).
        pmkst HS2. rewrite Hmm2.
        rewrite (SIGP CS_sup_chain_clear ltac:(unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
        change (cmd_af CS_sup_chain_clear) with AF_sup_chain_clear.
        assert (Hsf0 : rec_spill_frees (e_R e) = 0) by (unfold rec_spill_frees; rewrite Hcalls; reflexivity).
        assert (HEVC : EV_SUP_CHAIN_CLEAR (e_R e) = 4)
          by (unfold EV_SUP_CHAIN_CLEAR, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP; rewrite Hsf0; reflexivity).
        pose proof HC4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrec4 & _).
        pose proof (vk_code_range B ly2 S2 _ (e_R e) _ Hrec4) as Hcode0.
        assert (Ht0 : (length (snd (sup_chain_clear_m (e_R e) id)) <= 28)%nat)
          by (unfold sup_chain_clear_m, daemon_shape; apply vk_stub_len; exact Hcode0).
        pose proof (dec_length id ltac:(lia)) as Hdl.
        apply (vk_chain_clear B MT RRO RPG RECC PROGU ROA MTL HB (TSUP_CHAIN_CLEAR fx) e pos F q c [p0; p1]
          [vr_lb e q; vr_cb e c] rl1 (e_R e) (e_O e) (e_q0 e) k 2 (vr_k1 (e_R e) (e_D e)) nm VR_NM_PRE VR_NM_HD
          ly2 S2 W2 (ms_regs ms4) mem2 mdv4 id 30752
          (fun tq => [(10, tq); (18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)])
          _ He HC4 HL2 HCP2 (or_introl eq_refl) (or_intror (or_introl eq_refl)) Q1b ltac:(lia) eq_refl Q10b'
          ltac:(lia) Hsf0).
        - rewrite Hk1 in Hk1ev. lia.
        - rewrite Hk1. lia.
        - unfold VERBS_RECEIVE_MALLOCS, VR_NM_PRE in *. lia.
        - unfold VR_NM_HD, VR_NM_PRE in *. lia.
        - rewrite Hcalls. unfold LIVE_SUP_CHAIN_CLEAR, LIVE_ARG_I, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP.
          cbn [length]. unfold LMAX, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ. lia.
        - intros tq r0 v0 Hin. cbn [In] in Hin.
          destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]; injection E1 as <- <-;
            [left; split; reflexivity | right; split; [unfold acallee_saved; lia | unfold rl1; cbn; tauto] ..].
        - intros fx' R1 t tq Oc1 ly3 S3 W3 regs3 mem3 md3 Hfx Em Htq Hstr HC3 HL3 HCP3.
          eapply SRr_mono; [exact (s20_join (fx := fx') B MT e pos F q c [p0; p1] tq R1 t k nm ly3 S3 W3 regs3 mem3 md3 _ id
            Hne' Hvh Em ltac:(lia) ltac:(unfold VR_NM_HD, VR_NM_PRE in *; lia) Htq Hstr HC3 HL3 HCP3)|].
          intros W' c' _ Hh. exists fx'. split; [exact Hfx|]. unfold vrF_or, vr_or, vrF_hd. right. exact Hh. }
      { (* not a number: the refusal stub 0x8dd34 *)
        destruct Hmod as [Hvh Hk1].
        pose proof HC2 as (HJ2 & _ & _ & _ & _ & Hrv2 & _).
        assert (R102 : getr regs2 (Z_to_bv 5 10) = w64 0)
          by (apply (vk_rv_get regs2 _ _ _ Hrv2); apply in_or_app; right; cbn; tauto).
        set (E2 := Eimg (Ereg regs2 [])).
        assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
        assert (HAE2 : env_agree 32 (Ereg regs2 []) E2) by (subst E2; apply vk_env_agree).
        assert (E102 : ew E2 10%nat = Z_to_bv 64 0)
          by (subst E2; rewrite (ew_Eimg_Ereg_nat regs2 _ 10%nat (Z_to_bv 5 10) eq_refl); exact R102).
        assert (HS2 : st_ok_pi SEGS VAL E2 (vk_ss_ret 30740)
          (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 30740)) mem2 (seg_rom SEGS)))).
        { rewrite restrict_mkst_fx. unfold vk_ss_ret. apply pa_entry_st_ok_full.
          - subst E2. apply regs_ok_Eimg_Ereg.
          - reflexivity.
          - constructor.
          - exact I.
          - split; [exact I | split; exact I]. }
        paj_run_shc RUNP RUNC HS2 HJ2.
        { apply awr_ok_nil. }
        lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdv3 := m) in *; clearbody mdv3 end.
        lazymatch goal with
        | Hfx : frame_of _ ?rs _ (ms_mem _) |- _ =>
          assert (Hro3 : rs_read_only rs = true) by (vm_compute; reflexivity);
          pose proof (frame_of_read_only _ _ _ _ Hro3 Hfx) as Hm3; cbn [ms_mem mkst] in Hm3
        end.
        clear HF HFr HG.
        psrr_branch_pi RUNP BR HS2.
        { (* a0 = 0: to 0x8dd34 *)
          paj_run_to_shc RUNTO HS2 HJ2 30800.
          { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
              let rs' := eval vm_compute in rs in change rs with rs' end.
            apply awr_ok_nil. }
          lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdv4 := m) in *; clearbody mdv4 end.
          lazymatch goal with
          | Hfx : frame_of _ ?rs (ms_mem _) (ms_mem _) |- _ =>
            assert (Hro4 : rs_read_only rs = true) by (vm_compute; reflexivity);
            pose proof (frame_of_read_only _ _ _ _ Hro4 Hfx) as Hm4
          end.
          clear HF HFr HG.
          lazymatch type of Hm4 with ms_mem ?m4 = ms_mem ?m3 =>
            assert (Hmm2 : ms_mem m4 = mem2) by (rewrite Hm4; exact Hm3) end.
          rewrite Hmm2 in HJ2.
          pose proof (vk_kept_regs E2 _ _ regs2 [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 27] HS2 HAE2
            ltac:(vm_compute; reflexivity)) as KR2. cbn [ms_regs restrict] in KR2.
          lazymatch type of KR2 with forall r, _ -> getr (ms_regs ?m4) _ = _ => rename m4 into ms4 end.
          assert (Hrv4 : vr_rv (ms_regs ms4) (vr_base B e ++ rl1)).
          { unfold vr_rv, vr_base, rl1. cbn [app].
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
            (rewrite KR2 by (cbn; tauto); apply (vk_rv_get _ _ _ _ Hrv2); apply in_or_app;
             first [left; cbn; tauto | right; cbn; tauto]). }
          pmkst HS2. rewrite Hmm2.
          apply SRr_ret. exists fx. split; [apply fxrel_refl|]. unfold vrF_or, vr_or, vrF_pr. left.
          apply (s20_pr e pos F q c [p0; p1] k nm ly2 S2 W2 (ms_regs ms4) mem2 mdv4 He Hne' Hvh Hk1); [|exact HL2 | exact HCP2].
          eapply (vk_regs B MT); [exact HC2 | exact HJ2 | exact Hrv4]. }
        { exfalso. rewrite branch_eq_U in Hc. rewrite (U_atom E2 10 0 E102) in Hc by lia.
          change (U E2 (SLit 0)) with 0 in Hc. vm_compute in Hc. discriminate Hc. } }
- (* not two words: to the refusal stub 0x8dd34 *)
  destruct (chclear_rej (e_R e) (e_D e) Hroute Hne H2) as [Hvh Hk1].
  set (E := Eimg (Ereg regsc [w64 c])).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsc [w64 c]) E) by (subst E; apply vk_env_agree).
  assert (E21 : ew E 21 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl), R21; reflexivity).
  assert (E9 : bv_unsigned (ew E 9%nat) = vr_s1 e).
  { subst E. rewrite (ew_Eimg_Ereg_nat regsc _ 9%nat (Z_to_bv 5 9) eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
  assert (E32 : ew E 32%nat = w64 c).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    pose proof (ew_Ereg_extra regsc [w64 c] 0%nat) as HH. cbn [Nat.add nth] in HH. exact HH. }
  assert (HS : st_ok_pi SEGS VAL E ss20r (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 30716)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss20r. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor].
      unfold r_sp20, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (vr_s1 e) 56 8%N (SOff 32 0) c).
      + cbn [sv_denot]. rewrite E32. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      + cbn. lia.
      + apply aval_val_mem. exact Hav56.
    - cbn. tauto.
    - split; [exact I | split; exact I]. }
  paj_run_shc RUNP RUNC HS HJ.
  { unfold ss20r; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
  assert (Hro1 : rs_read_only (ss_mem ss20r) = true) by (vm_compute; reflexivity).
  pose proof (frame_of_read_only _ _ _ _ Hro1 HF) as Hm1. clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  + paj_run_to_shc RUNTO HS HJ 30800.
    { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
        let rs' := eval vm_compute in rs in change rs with rs' end.
      apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdv2 := m) in *; clearbody mdv2 end.
    lazymatch goal with
    | Hfx : frame_of _ ?rs (ms_mem _) (ms_mem _) |- _ =>
      assert (Hro2 : rs_read_only rs = true) by (vm_compute; reflexivity);
      pose proof (frame_of_read_only _ _ _ _ Hro2 Hfx) as Hm2
    end.
    clear HF HFr HG.
    lazymatch type of Hm2 with ms_mem ?m2 = ms_mem ?m1 =>
      assert (Hmm : ms_mem m2 = memc) by (rewrite Hm2; exact Hm1) end.
    rewrite Hmm in HJ.
    pose proof (vk_kept_regs E _ _ regsc [w64 c] [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] HS HAE
      ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    lazymatch type of KR with forall r, _ -> getr (ms_regs ?m2) _ = _ => rename m2 into ms2 end.
    assert (Hrv1 : vr_rv (ms_regs ms2) (vr_base B e ++ rl1)).
    { unfold vr_rv, vr_base, rl1. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      s20_rv HS KR Hrv ltac:(first [exact E32]). }
    pmkst HS. rewrite Hmm.
    apply SRr_ret. exists fx. split; [apply fxrel_refl|]. unfold vrF_or, vr_or, vrF_pr. left.
    apply (s20_pr e pos F q c tp k nm lyc Sc W (ms_regs ms2) memc mdv2 He Hne Hvh Hk1); [|exact HL | exact HCP].
    eapply (vk_regs B MT); [exact HC | exact HJ | exact Hrv1].
  + exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 21 _ E21) in Hc by lia.
    change (U E (SLit 2)) with 2 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold vr_ntok in Hc. lia.
Qed.

End e.
End f.
End d.
