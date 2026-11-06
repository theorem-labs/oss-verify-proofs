(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S26 LEDGER (0x8d894-0x8d8c0) of the walk of verbs_receive on the
   ASan+UBSan build (image B) of plugin-hostd/fuzz_command (interface: lib/B/Prog/verbs_receive_iface.v,
   vr_s26_stmt): the scan matched row j of g_instance_info_verbs (s11 = the row); the inline check of the row's
   ledger word (lb of its shadow byte at s3, 0 by the table's zero shadow, so the slow path 0x8d9a8-0x8d9b8 is not
   taken), the load of the ledger word, the reload of the line from the spill slot s1+56, the call
   sup_instance_verb(line, ledger) through its statement and the call rule PaFx.cl_callS_wideF, s10 = the reply
   text, the reloads of s4, s6, s9, s11 and the jump to the join JA 0x8d6a0. The B twin of
   lib/A/Prog/verbs_receive_s26.v, its runs redone on B's code, registers and spill map. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route verbs_receive_pre verbs_receive_tail_m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_line_c arg_s_c answer_c xmalloc_c rec_canonical_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_s30_kit verbs_receive_s25_k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the listing offsets: AF_verbs_receive = 0x691c = 26908 is 0x8ce4c *)
Definition S26_PC : Z := 29540.    (* 0x8d894 *)
Definition S26_RET : Z := 29564.   (* 0x8d8ac, after jal sup_instance_verb *)
Definition S26_JA : Z := 29040.    (* 0x8d6a0, the join JA *)

(* the symbolic state at 0x8d894: the registers as atoms; the spill slots s1+8 .. s1+56 B reads (atoms 32, 33, 35
   hold q, F, shadow(F); atom 34 is c), the shadow byte of the ledger word (at s3) and the ledger word (at s11+8,
   atom 36) *)
Definition s26_rsp : YP09.region := YP09.mkRegion (Some 9%nat) 0 64 0 0
  [YP09.mkChunk 8 (CVal 8 (SOff 35 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 33 0));
   YP09.mkChunk 32 (CVal 8 (SOff 35 4)); YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition s26_rsh : YP09.region := YP09.mkRegion (Some 19%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition s26_rled : YP09.region := YP09.mkRegion (Some 27%nat) 8 12 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 36 0))].
Definition s26_ss : sstate := mkSS S26_PC sr_atoms [s26_rsp; s26_rsh; s26_rled] None (mkFacts [] [] []).
(* the symbolic state at the return address 0x8d8ac: the registers as atoms and the spill slots s1+8..s1+56 *)
Definition s26_ss2 : sstate := mkSS S26_RET sr_atoms [s26_rsp] None (mkFacts [] [] []).
Definition s26_extra (q F c led : Z) : list word :=
[Z_to_bv 64 q; Z_to_bv 64 F; Z_to_bv 64 c; Z_to_bv 64 (shadow_addr F); Z_to_bv 64 led].

Ltac s26_awr :=
lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma s26_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 sh row q F c led,
getr regs (Z_to_bv 5 9) = w64 s1 -> getr regs (Z_to_bv 5 19) = w64 sh -> getr regs (Z_to_bv 5 27) = w64 row ->
alloc_ceiling <= s1 -> s1 + 64 <= 2 ^ 47 -> 0x10000 <= row -> row + 16 <= 0x606000 ->
0x606000 <= sh -> sh + 1 <= alloc_ceiling ->
0 <= q < 2 ^ 64 -> 0 <= F -> F + 32 < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= shadow_addr F -> shadow_addr F + 4 < 2 ^ 64 ->
0 <= led < 2 ^ 31 ->
aval_mem (rdW W mem) (s1 + 8) 8 (shadow_addr F) -> aval_mem (rdW W mem) (s1 + 16) 8 F ->
aval_mem (rdW W mem) (s1 + 24) 8 F -> aval_mem (rdW W mem) (s1 + 32) 8 (shadow_addr F + 4) ->
aval_mem (rdW W mem) (s1 + 56) 8 q ->
rdW W mem sh = Some 0 -> aval_mem (rdW W mem) (row + 8) 4 led ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (s26_extra q F c led))) s26_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S26_PC)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 sh row q F c led H9 H19 H27 Hs1a Hs1b Hr1 Hr2 Hsh1 Hsh2 Hq HF1 HF2 Hc HS1 HS2 Hled
M8 M16 M24 M32 M56 Msh Mled.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
set (E := Eimg (Ereg regs (s26_extra q F c led))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. subst E. apply ew_Eimg_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (s26_extra q F c led) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (U9 : bv_unsigned (ew E 9) = s1).
{ rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (U19 : bv_unsigned (ew E 19) = sh).
{ rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), H19. unfold w64. apply unsigned_lit_small. lia. }
assert (U27 : bv_unsigned (ew E 27) = row).
{ rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl), H27. unfold w64. apply unsigned_lit_small. lia. }
assert (XV : forall (j : nat) v off, (j < 5)%nat -> nth j (s26_extra q F c led) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> sv_denot E (SOff (32 + j) off) = Z_to_bv 64 (v + off)).
{ intros j v off Hj Hv Hr. cbn [sv_denot]. rewrite (EX j Hj), Hv, unsigned_lit_small by exact Hr. reflexivity. }
rewrite restrict_mkst_fx. unfold s26_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, s26_rsp, s26_rsh, s26_rled;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ s1 8 8 (SOff (32 + 3) 0) (shadow_addr F));
      [rewrite (XV 3%nat (shadow_addr F) 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply vr_val_mem_of_aval; exact M8].
    * apply (chunk_ok_val SEGS E _ s1 16 8 (SOff (32 + 1) 0) F);
      [rewrite (XV 1%nat F 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply vr_val_mem_of_aval; exact M16].
    * apply (chunk_ok_val SEGS E _ s1 24 8 (SOff (32 + 1) 0) F);
      [rewrite (XV 1%nat F 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply vr_val_mem_of_aval; exact M24].
    * apply (chunk_ok_val SEGS E _ s1 32 8 (SOff (32 + 3) 4) (shadow_addr F + 4));
      [rewrite (XV 3%nat (shadow_addr F) 4) by (reflexivity || lia); reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply vr_val_mem_of_aval; exact M32].
    * apply (chunk_ok_val SEGS E _ s1 56 8 (SOff (32 + 0) 0) q);
      [rewrite (XV 0%nat q 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply vr_val_mem_of_aval; exact M56].
  + rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ sh 0 1 (SLit 0) 0);
    [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
    apply vr_val_mem_of_aval. intros kk Hkk. destruct kk as [|kk]; [|cbn in Hkk; lia].
    rewrite ?Z.add_0_r. cbn [Z.of_nat]. rewrite ?Z.add_0_r. rewrite Msh. reflexivity.
  + rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ row 8 4 (SOff (32 + 4) 0) led);
    [rewrite (XV 4%nat led 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia | apply vr_val_mem_of_aval; exact Mled].
- apply pairwise_disjoint_of_extents. unfold s26_rsp, s26_rsh, s26_rled, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite U9, U19, U27.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [exact I | split; exact I].
Qed.

(* the state at the return address 0x8d8ac, seeded afresh: the walk after the call runs at the FP state the callee
   returns at (statement pass 4), so it does not start from the symbolic state before the call *)
Lemma s26_seed2 : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 q F c,
getr regs (Z_to_bv 5 9) = w64 s1 ->
alloc_ceiling <= s1 -> s1 + 64 <= 2 ^ 47 ->
0 <= q < 2 ^ 64 -> 0 <= F -> F + 32 < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= shadow_addr F -> shadow_addr F + 4 < 2 ^ 64 ->
aval_mem (rdW W mem) (s1 + 8) 8 (shadow_addr F) -> aval_mem (rdW W mem) (s1 + 16) 8 F ->
aval_mem (rdW W mem) (s1 + 24) 8 F -> aval_mem (rdW W mem) (s1 + 32) 8 (shadow_addr F + 4) ->
aval_mem (rdW W mem) (s1 + 56) 8 q ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (s26_extra q F c 0))) s26_ss2
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S26_RET)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 q F c H9 Hs1a Hs1b Hq HF1 HF2 Hc HS1 HS2 M8 M16 M24 M32 M56.
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
set (E := Eimg (Ereg regs (s26_extra q F c 0))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. subst E. apply ew_Eimg_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (s26_extra q F c 0) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (U9 : bv_unsigned (ew E 9) = s1).
{ rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (XV : forall (j : nat) v off, (j < 5)%nat -> nth j (s26_extra q F c 0) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> sv_denot E (SOff (32 + j) off) = Z_to_bv 64 (v + off)).
{ intros j v off Hj Hv Hr. cbn [sv_denot]. rewrite (EX j Hj), Hv, unsigned_lit_small by exact Hr. reflexivity. }
rewrite restrict_mkst_fx. unfold s26_ss2. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, s26_rsp;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ s1 8 8 (SOff (32 + 3) 0) (shadow_addr F));
    [rewrite (XV 3%nat (shadow_addr F) 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply vr_val_mem_of_aval; exact M8].
  + apply (chunk_ok_val SEGS E _ s1 16 8 (SOff (32 + 1) 0) F);
    [rewrite (XV 1%nat F 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply vr_val_mem_of_aval; exact M16].
  + apply (chunk_ok_val SEGS E _ s1 24 8 (SOff (32 + 1) 0) F);
    [rewrite (XV 1%nat F 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply vr_val_mem_of_aval; exact M24].
  + apply (chunk_ok_val SEGS E _ s1 32 8 (SOff (32 + 3) 4) (shadow_addr F + 4));
    [rewrite (XV 3%nat (shadow_addr F) 4) by (reflexivity || lia); reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply vr_val_mem_of_aval; exact M32].
  + apply (chunk_ok_val SEGS E _ s1 56 8 (SOff (32 + 0) 0) q);
    [rewrite (XV 0%nat q 0) by (reflexivity || lia); rewrite Z.add_0_r; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | apply vr_val_mem_of_aval; exact M56].
- apply pairwise_disjoint_of_extents. unfold s26_rsp, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. try rewrite U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [exact I | split; exact I].
Qed.

(* vr_ent at one FP state gives vr_ent at another with rounding mode 0: only its last conjunct names the FP state *)
Lemma vr_ent_fx : forall (f1 : YK11.FPState) B MT e,
vr_ent (fx := fx) B MT e -> frm0 f1 -> vr_ent (fx := f1) B MT e.
Proof.
intros f1 B MT e H Hf. unfold vr_ent in *. cbv zeta in *.
repeat lazymatch type of H with _ /\ _ => let H1 := fresh "H" in destruct H as [H1 H] end.
repeat (split; [assumption|]). exact Hf.
Qed.

(* the walk after sup_instance_verb returns (0x8d8ac to the join JA) and the facts it needs: sup_instance_verb's post
   is FP-existential (statement pass 4), so this part runs at the FP state the call returns at. It is proved in its
   own section, at that section's FP state, and vr_s26 uses it at the callee's (the brief's pattern E) *)
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis MTL : ameter_laws MT.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.

Lemma s26_bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof. intros l l' H. induction H; unfold bsum in *; cbn [fold_right] in *; lia. Qed.

Lemma s26_rsf : forall R, 0 <= rec_spill_frees R.
Proof. intros R. unfold rec_spill_frees. destruct (Nat.ltb _ _); lia. Qed.

Lemma s26_ev_after : forall R af, 0 <= ev_after R af.
Proof.
intros R [x|]; cbn [ev_after]; [|lia]. unfold EV_SUP_AFTER_REPLY, EV_RECORD, EV_ARG_S, EV_XMALLOC.
pose proof (s26_rsf R). lia.
Qed.

Lemma s26_ev_reply : 0 <= EV_REPLY.
Proof. vm_compute. intro H. discriminate H. Qed.

Lemma s26_dec_len : forall led, (led = 0 \/ led = 1) -> length (dec led) = 1%nat.
Proof. intros led [-> | ->]; reflexivity. Qed.

Lemma s26_text_len : forall R line led, (length (snd (sup_instance_verb_m R line led)) <= 4096)%nat.
Proof.
intros R line led. pose proof (verbs_receive_tail_m.tlm_call_text R (Verbs.sup_instance_verb line led)) as [_ Ht].
exact Ht.
Qed.

Lemma s26_live : forall e lyc Sc bq bc line led R,
blocks_bytes (e_S e) + LIVE_VERBS_RECEIVE <= LIVE_MAX ->
Permutation (ablocks B (e_ly e) (e_S e)) (e_O e ++ e_rest e) ->
Permutation (ablocks B lyc Sc) (e_O e ++ [bq; bc] ++ e_rest e) ->
snd bq <= 8193 -> snd bc <= 8193 -> Z.of_nat (length line) <= 8192 -> (led = 0 \/ led = 1) ->
blocks_bytes Sc + LIVE_SUP_INSTANCE_VERB R line led <= LIVE_MAX.
Proof.
intros e lyc Sc bq bc line led R H H0 H1 Hq Hc Hl Hled.
rewrite (blocks_bytes_bsum B lyc Sc). rewrite (blocks_bytes_bsum B (e_ly e) (e_S e)) in H.
rewrite (s26_bsum_perm _ _ H1). rewrite (s26_bsum_perm _ _ H0) in H.
rewrite !YCbq.bsum_app in *. unfold bsum at 2. cbn [fold_right].
unfold LIVE_SUP_INSTANCE_VERB, LIVE_ARG_LINE, LIVE_REC_CANONICAL, LIVE_ARG_S, LIVE_ANSWER, LIVE_HAND_BACK,
  LIVE_XMALLOC. cbn [sarg].
rewrite (s26_dec_len led Hled). pose proof (s26_text_len R line led) as Ht.
unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in H. lia.
Qed.

(* the meter of the ledger call, in one lemma: sup_instance_verb's account is at most 4 mallocs of at most
   VERBS_RECEIVE_REQ bytes (rec_canonical's and arg_s's copies, answer's two) and rec_spill_frees R + 1 frees (record()'s
   spill arm, answer's free of the old answer), both within its EV_SUP_INSTANCE_VERB R = rec_spill_frees R + 5
   events; the interface's vri_meter_ok gives the callee's mo_ok premise, vri_meter_step the boundary's vr_meter after
   its mo_le *)
Lemma s26_meter_call : forall e Sc k nm line led,
vr_ent B MT e -> vr_meter MT e Sc k nm -> Z.of_nat (length line) <= 8192 -> (led = 0 \/ led = 1) ->
k + EV_SUP_INSTANCE_VERB (e_R e) <= ev_vr (e_R e) (e_D e) ->
mo_ok MT Sc (XM_SUP_INSTANCE_VERB MT (e_R e) line led) /\
(forall S2, mo_le MT Sc S2 (XM_SUP_INSTANCE_VERB MT (e_R e) line led) ->
  vr_meter MT e S2 (k + EV_SUP_INSTANCE_VERB (e_R e)) (nm + 4)).
Proof.
intros e Sc k nm line led Hent Hm Hl Hled Hk.
pose proof (s26_rsf (e_R e)) as Hrs.
assert (HEV : EV_SUP_INSTANCE_VERB (e_R e) = rec_spill_frees (e_R e) + 5)
  by (unfold EV_SUP_INSTANCE_VERB, EV_RECORD, EV_ARG_LINE, EV_REC_CANONICAL, EV_ARG_S, EV_ANSWER, EV_HAND_BACK,
        EV_XMALLOC; lia).
assert (HX : XM_SUP_INSTANCE_VERB MT (e_R e) line led <=
  4 * mo_malloc MT VERBS_RECEIVE_REQ + (rec_spill_frees (e_R e) + 1) * mo_free MT).
{ set (mm := mo_malloc MT VERBS_RECEIVE_REQ). set (mf := mo_free MT).
  pose proof (s26_text_len (e_R e) line led) as Ht.
  assert (M1 : mo_malloc MT (Z.max (Z.of_nat (length line) + 1) 1) <= mm)
    by (apply (mo_malloc_mono MT MTL); unfold VERBS_RECEIVE_REQ; lia).
  assert (M2 : mo_malloc MT (Z.max (Z.of_nat (length (dec led)) + 1) 1) <= mm)
    by (apply (mo_malloc_mono MT MTL); rewrite (s26_dec_len led Hled); unfold VERBS_RECEIVE_REQ; lia).
  assert (M3 : mo_malloc MT (Z.max (Z.of_nat (length (snd (sup_instance_verb_m (e_R e) line led))) + 1) 1) <= mm)
    by (apply (mo_malloc_mono MT MTL); unfold VERBS_RECEIVE_REQ; lia).
  unfold XM_SUP_INSTANCE_VERB, XM_RECORD, XM_ARG_LINE, XM_REC_CANONICAL, XM_ARG_S, XM_ANSWER, XM_HAND_BACK,
    XM_XMALLOC, LIVE_XMALLOC. cbn [sarg].
  fold mf. nia. }
split.
- exact (vri_meter_ok B MT e Sc k nm _ 4 (rec_spill_frees (e_R e) + 1) (EV_SUP_INSTANCE_VERB (e_R e)) MTL Hent Hm HX
    ltac:(lia) ltac:(lia) Hk).
- intros S2 Hle.
  exact (vri_meter_step MT e Sc S2 k nm _ 4 (rec_spill_frees (e_R e) + 1) (EV_SUP_INSTANCE_VERB (e_R e)) MTL Hm Hle HX
    ltac:(lia) ltac:(lia)).
Qed.

Definition s26_FP1 (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma s26_inFP1 : forall O a, inFP (s26_FP1 O) a ->
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof.
intros O a H. unfold s26_FP1 in H. apply inFP_cons in H as [H | H]; [left; exact H|].
apply inFP_cons in H as [H | H]; [right; left; exact H|].
right; right. exact (inFP_ablocks_fp_inv O a H).
Qed.

Lemma s26_pg_img : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
(A_G_QUITTING <= a < A_G_QUITTING + 4) -> inFP cmd_PG a.
Proof.
intros a H. unfold cmd_PG, REC_SIZE, SC_SIZE in *.
destruct H as [H | [H | H]]; [exists (A_G_REC, A_G_REC + 960) | exists (A_REC_SPILL, A_REC_SPILL + 56)
  | exists (A_G_QUITTING, A_G_QUITTING + 4)]; (split; [cbn; tauto | cbn [fst snd]; lia]).
Qed.

Lemma s26_nodup_disj : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|y l1 IH]; intros l2 x H H1 H2; [destruct H1|].
inversion H as [|? ? Hy Hd]; subst. destruct H1 as [<- | H1].
- apply Hy. apply in_or_app. right. exact H2.
- exact (IH l2 x Hd H1 H2).
Qed.

Lemma s26_nodup_app : forall (l1 l2 : list (Z * Z)), List.NoDup l1 -> List.NoDup l2 ->
(forall x, In x l1 -> In x l2 -> False) -> List.NoDup (l1 ++ l2).
Proof.
induction l1 as [|y l1 IH]; intros l2 H1 H2 Hd; [exact H2|].
inversion H1 as [|? ? Hy Hd1]; subst. cbn [app]. constructor.
- intros Hin. apply in_app_or in Hin as [Hin | Hin]; [exact (Hy Hin)|]. exact (Hd y (or_introl eq_refl) Hin).
- apply IH; [exact Hd1 | exact H2 | intros x Hx1 Hx2; exact (Hd x (or_intror Hx1) Hx2)].
Qed.

Definition s26_zz_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma s26_env_of : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> vr_env B W mem.
Proof.
intros ly S W mem md HAR HRO. pose proof (ROA _ _ _ _ _ HAR HRO) as HROk.
destruct (RECC _ _ _ _ _ HAR) as (Hfl & Hg & Her).
split; [exact HRO|]. split; [exact (vr_got_of_ro B MT RRO RPG RECC PROGU ROA _ HROk)|]. split; [exact HROk|].
split; [exact Hg|]. split; [exact Hfl | exact Her].
Qed.

(* the state after sup_instance_verb returns: every fact of the boundary is kept outside the callee's footprint
   (g_rec, record.spill and the recorder's blocks), and the recorder holds the call *)
Lemma s26_post : forall e j nmj led pos F q c tp lyc Sc W memc mdc k nm regsc ly2 S2 W2 mem2 md2 R' t qt O' regs' rl',
vr_ent B MT e ->
nth_error vr_tbl j = Some (nmj, led) ->
VRR.route (Verbs.toks (e_D e)) = VRR.RLedger led -> Verbs.toks (e_D e) <> [] ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(19, SHADOW_OFF + (0xa5c48 + 16 * Z.of_nat j) / 8); (21, vr_ntok (e_D e)); (26, hd 0 tp);
   (27, 0xa5c40 + 16 * Z.of_nat j)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  ly2 S2 W2 mem2 md2 (k + EV_SUP_INSTANCE_VERB (e_R e)) ->
ajournal SEGS B SUP_INSTANCE_VERB_STK (vr_s1 e) (s26_FP1 (e_O e)) lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2
  (EV_SUP_INSTANCE_VERB (e_R e)) ->
sup_instance_verb_m (e_R e) (Verbs.line (e_D e)) led = (R', t) ->
4096 <= qt ->
rec_repA B ly2 S2 (rdW W2 mem2) R' O' ->
(forall pn, In pn O' -> In pn (e_O e) \/ ~ In pn (ablocks B lyc Sc)) ->
In (qt, Z.of_nat (length t) + 1) (ablocks B ly2 S2) ->
(forall pn, In pn (ablocks B lyc Sc) -> ~ In pn (e_O e) -> pn <> (qt, Z.of_nat (length t) + 1)) -> ~ In qt (map fst O') ->
astr_atR (rdW W2 mem2) qt t ->
(forall pn, In pn (ablocks B lyc Sc) -> ~ In pn (e_O e) ->
  In pn (ablocks B ly2 S2) /\ iv_apart (fst pn) (snd pn) qt (Z.of_nat (length t) + 1)) ->
(forall pn, In pn (ablocks B ly2 S2) ->
  (In pn (ablocks B lyc Sc) /\ ~ In pn (e_O e)) \/ In pn O' \/ pn = (qt, Z.of_nat (length t) + 1)) ->
mo_le MT Sc S2 (XM_SUP_INSTANCE_VERB MT (e_R e) (Verbs.line (e_D e)) led) ->
vr_rv regs' (vr_base B e ++ rl') ->
exists O1, astr_atR (rdW W2 mem2) qt (vr_x (e_R e) (e_D e)) /\
vr_core B MT e pos F [(qt, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c] vr_sh2
  (vr_sl3 F q c) rl' (vr_R1 (e_R e) (e_D e)) O1 (vr_qv e)
  (k + EV_SUP_INSTANCE_VERB (e_R e)) (vr_k1 (e_R e) (e_D e)) (nm + 4) VR_NM_HD ly2 S2 W2 regs' mem2 md2 /\
vr_line B e q W2 mem2 /\ vr_copy B e F c tp W2 mem2.
Proof.
intros e j nmj led pos F q c tp lyc Sc W memc mdc k nm regsc ly2 S2 W2 mem2 md2 R' t qt O' regs' rl'
  Hent Hnth Hroute Htoks Hcore Hline Hcopy HJ2 HJc Hm Hq4096 Hrec' HO'1 Hqin Hqnot HqO' Hstr HB1 HB2 Hmle Hrv'.
destruct (vr_led_model (e_R e) (e_D e) led Hroute Htoks) as [Hh Hk1].
assert (Hxe : vr_x (e_R e) (e_D e) = t) by (unfold vr_x; rewrite Hh, Hm; reflexivity).
assert (HR1 : vr_R1 (e_R e) (e_D e) = R') by (unfold vr_R1; rewrite Hh, Hm; reflexivity).
assert (Hqv : vr_qv e = e_q0 e) by (unfold vr_qv, vr_quit; rewrite Hh; reflexivity).
rewrite Hxe, HR1, Hqv.
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & HinD & HnotD & _ & _ & HREC0 & _ & _ & _ & _ & _
  & HpermE & _).
pose proof Hcore as (HJ & Hkk & Hmeter & Hnm & Hframe & Hrv & Hsaved & Hspill & Henv & Hrec & HdO & Hperm & Hquit).
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ2) as HAR2.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HJc as (_ & Hlyc & _ & _ & _ & Hfrsc & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof Hlyc as (_ & _ & _ & _ & _ & EF & _).
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
assert (HSTKc : SUP_INSTANCE_VERB_STK + 208 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSTKp : 2 * 4096 <= SUP_INSTANCE_VERB_STK) by (apply Z.leb_le; vm_compute; reflexivity).
destruct (vr_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
pose proof (vr_frames_own B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hin4.
destruct Hframe as (HFa & Hflag & Hshf).
destruct (vr_frame_bounds B _ _ _ _ _ pos HAR Hin4) as (BF1 & BF2 & BF3). rewrite <- HFa in BF1, BF2, BF3.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin4) as (_ & _ & HFapp). rewrite <- HFa in HFapp.
assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc)) by (eapply vr_core_blocks; [exact Hcore | left; reflexivity]).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)) by (eapply vr_core_blocks; [exact Hcore | right; left; reflexivity]).
assert (HOin : forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
assert (HND : List.NoDup (e_O e ++ [vr_lb e q; vr_cb e c] ++ e_rest e)).
{ apply (Permutation_NoDup Hperm). exact (RecBLemmas.recb_ablocks_nodup_m B _ _ _ _ _ HAR). }
assert (HtO : forall x, In x ([vr_lb e q; vr_cb e c] ++ e_rest e) -> ~ In x (e_O e)).
{ intros x Hx2 Hx1. exact (s26_nodup_disj _ _ x HND Hx1 Hx2). }
assert (HtB : forall x, In x ([vr_lb e q; vr_cb e c] ++ e_rest e) -> In x (ablocks B lyc Sc)).
{ intros x Hx. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hx. }
(* the callee's footprint lies below the ceiling, and misses the boundary's own bytes *)
assert (HFP1 : forall a, inFP (s26_FP1 (e_O e)) a ->
  ((A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE)) \/
  exists p n, In (p, n) (ablocks B lyc Sc) /\ In (p, n) (e_O e) /\ p <= a < p + req_size n).
{ intros a Ha. destruct (s26_inFP1 _ _ Ha) as [H | [H | (p & n & Hpn & Hr)]]; [left; left; exact H | left; right; exact H|].
  right. exists p, n. split; [exact (HOin _ Hpn) | split; [exact Hpn | exact Hr]]. }
assert (HFPlo : forall a, inFP (s26_FP1 (e_O e)) a -> a < alloc_ceiling).
{ intros a Ha. destruct (HFP1 a Ha) as [H | (p & n & Hpn & _ & Hr)]; [unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in H; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpn) as (_ & _ & Hc & _). lia. }
assert (Hpg : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) -> in_img SEGS a).
{ intros a H. apply (proj1 (PROGU a (s26_pg_img a ltac:(tauto)))). }
assert (HFPblk : forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (e_O e) -> 0 <= i < req_size n ->
  ~ inFP (s26_FP1 (e_O e)) (p + i)).
{ intros p n i Hpn HnO Hi Hf. destruct (HFP1 _ Hf) as [H | (b & m & Hbm & HbO & Hr)].
  - exact (blk_img SEGS B LAWS _ _ _ _ _ p n (p + i) HAR Hpn ltac:(lia) (Hpg _ H)).
  - assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in HbO; exact (HnO HbO)).
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ b m p n HAR Hbm Hpn Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HFPfr : forall a, (F <= a < F + 1024) \/ (shadow_addr F <= a < shadow_addr F + 128) ->
  ~ inFP (s26_FP1 (e_O e)) a).
{ intros a Ha Hf. destruct (HFP1 _ Hf) as [H | (b & m & Hbm & _ & Hr)].
  - destruct Ha as [Ha | Ha].
    + apply (frm_img SEGS B LAWS _ _ _ _ _ 4 pos a HAR Hin4); [rewrite <- HFa; change (fs_frame_bytes 4) with 1024; lia|].
      exact (Hpg _ H).
    + unfold shadow_addr, SHADOW_OFF, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *.
      pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hbm) as (_ & _ & _ & Happ & _).
    destruct Ha as [Ha | Ha].
    + pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 4 pos HAR Hbm Hin4) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite <- HFa in Hd. change (fs_frame_bytes 4) with 1024 in Hd. lia.
    + unfold shadow_addr, SHADOW_OFF in Ha.
      exact (fshadow_not_app F 128 b (req_size m) a ltac:(lia) ltac:(lia) Happ ltac:(lia) Hr). }
assert (Hspare : forall a, ~ inFP (s26_FP1 (e_O e)) a -> fp_spares (s26_FP1 (e_O e)) a).
{ intros a Hn. split; [|exact Hn]. intros Hso. exfalso.
  destruct (HFP1 0 Hso) as [H | (p & n & Hpn & _ & Hr)]; [unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in H; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpn) as (_ & H4 & _). lia. }
(* the blocks of the boundary survive the call *)
assert (Hlb2 : In (vr_lb e q) (ablocks B ly2 S2)) by (apply (HB1 _ Hlb); apply HtO; left; reflexivity).
assert (Hcb2 : In (vr_cb e c) (ablocks B ly2 S2)) by (apply (HB1 _ Hcb); apply HtO; right; left; reflexivity).
assert (KB : forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (e_O e) -> In (p, n) (ablocks B ly2 S2) ->
  0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W memc (p + i)).
{ intros p n i Hpn HnO Hpn2 Hi. apply (G2 p n i Hpn Hpn2 Hi). exact (HFPblk p n i Hpn HnO Hi). }
assert (KF : forall a, (F <= a < F + 1024) \/ (shadow_addr F <= a < shadow_addr F + 128) ->
  rdW W2 mem2 a = rdW W memc a).
{ intros a Ha. apply (G4 4 pos a Hin4); [|exact (HFPfr a Ha)].
  unfold frame_rng, in_zr. cbn [fst snd]. rewrite <- HFa. change (fs_frame_bytes 4) with 1024. change (1024 / 8) with 128. lia. }
assert (KS : forall a, vr_s1 e <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memc a).
{ intros a Ha. apply G1; [lia | lia | intros Hf; pose proof (HFPlo a Hf); lia]. }
assert (HL : 0 <= vr_l (e_n e) (e_D e) <= e_n e) by (apply verbs_receive_pre.strnlen_res_le; lia).
assert (HLL : Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e)).
{ pose proof (vr_line_le (e_D e)). pose proof (verbs_receive_pre.strnlen_upto (e_D e)) as [_ L2].
  rewrite HlenD in L2. unfold vr_l. lia. }
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as [Hrq1 Hrq2].
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [Hrc1 Hrc2].
assert (HlbO : ~ In (vr_lb e q) (e_O e)) by (apply HtO; left; reflexivity).
assert (HcbO : ~ In (vr_cb e c) (e_O e)) by (apply HtO; right; left; reflexivity).
exists (List.nodup s26_zz_dec O').
split; [exact Hstr|].
split; [|split].
- split; [exact HJ2|].
  split; [rewrite Hk1; lia|].
  split.
  { destruct (vr_row_facts j nmj led Hnth) as (_ & Hled01 & _).
    refine (proj2 (s26_meter_call e Sc k nm (Verbs.line (e_D e)) led Hent Hmeter _ Hled01 _) S2 Hmle); [lia|].
    rewrite ev_vr_eq. unfold vr_k3, vr_k2. rewrite Hk1.
    pose proof s26_ev_reply. pose proof (s26_ev_after (vr_R2 (e_R e) (e_D e)) (vr_aft (e_D e))). lia. }
  split; [unfold VR_NM_PRE, VR_NM_HD in *; lia|].
  split.
  { split; [rewrite HFa; unfold frame_addr; rewrite EF; reflexivity|].
    split.
    - assert (Efl : flag_addr ly2 4 pos = flag_addr lyc 4 pos) by (unfold flag_addr; rewrite EF; reflexivity).
      rewrite Efl. rewrite (rdword_ext (rdW W memc) (rdW W2 mem2)); [exact Hflag|].
      intros kk Hkb. apply KF. lia.
    - intros i Hi. rewrite KF by lia. exact (Hshf i Hi). }
  split; [exact Hrv'|].
  split.
  { intros jj r Hj. pose proof (Hsaved jj r Hj) as Hs.
    assert (Hj13 : (jj < 13)%nat) by (change 13%nat with (length vr_saved_regs); apply nth_error_Some; rewrite Hj; discriminate).
    apply (aval_mem_agree _ _ _ 8 _ Hs). intros kk Hkb. apply KS. unfold vr_sp0 in *. lia. }
  split.
  { unfold vr_spill in *. rewrite Forall_forall in Hspill |- *. intros ov Hov.
    pose proof (Hspill ov Hov) as Hs.
    assert (Hb : 0 <= fst ov <= 72) by (unfold vr_sl3 in Hov; cbn in Hov; repeat (destruct Hov as [<- | Hov]; [cbn; lia|]); destruct Hov).
    apply (aval_mem_agree _ _ _ 8 _ Hs). intros kk Hkb. apply KS. unfold vr_sp0 in *. lia. }
  split.
  { apply (s26_env_of _ _ _ _ _ HAR2).
    pose proof Henv as (HRO & _).
    intros a Hro Ho He.
    assert (Hi : in_img SEGS a).
    { destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]. }
    assert (Hnf : ~ inFP (s26_FP1 (e_O e)) a).
    { intros Hf. destruct (HFP1 a Hf) as [H | (p & n & Hpn & _ & Hr)].
      - exact (RPG a (s26_pg_img a ltac:(tauto)) Hro).
      - exact (blk_img SEGS B LAWS _ _ _ _ _ p n a HAR Hpn Hr Hi). }
    rewrite (G3 a Hi Ho He (Hspare a Hnf)). exact (HRO a Hro Ho He). }
  split.
  { destruct Hrec' as (Q & HA & HOQ). exists Q. split; [exact HA|]. intros pn. rewrite nodup_In. exact (HOQ pn). }
  split.
  { rewrite nodup_In. intros HdO'.
    assert (Hd1 : In (e_data e, Z.max (e_n e) 1) (e_rest e)).
    { apply (Permutation_in _ HpermE) in HinD. apply in_app_or in HinD as [H | H]; [exfalso; exact (HnotD H) | exact H]. }
    assert (Hd2 : In (e_data e, Z.max (e_n e) 1) (ablocks B lyc Sc)) by (apply HtB; right; right; exact Hd1).
    destruct (HO'1 _ HdO') as [H | H]; [exact (HnotD H) | exact (H Hd2)]. }
  split.
  { apply NoDup_Permutation.
    - exact (RecBLemmas.recb_ablocks_nodup_m B _ _ _ _ _ HAR2).
    - apply s26_nodup_app; [apply NoDup_nodup|..].
      + constructor.
        * intros Hin. exact (Hqnot _ (HtB _ Hin) (HtO _ Hin) eq_refl).
        * exact (NoDup_app_remove_l _ _ HND).
      + intros x Hx1 Hx2. rewrite nodup_In in Hx1.
        destruct Hx2 as [<- | Hx2].
        * apply HqO'. apply in_map_iff. exists (qt, Z.of_nat (length t) + 1). split; [reflexivity | exact Hx1].
        * destruct (HO'1 _ Hx1) as [H | H]; [exact (HtO x Hx2 H) | exact (H (HtB x Hx2))].
    - intros x. split.
      + intros Hx. destruct (HB2 x Hx) as [(Hxc & HxO) | [Hx' | ->]].
        * apply (Permutation_in _ Hperm) in Hxc. apply in_app_or in Hxc as [H | H]; [contradiction|].
          apply in_or_app. right. right. exact H.
        * apply in_or_app. left. rewrite nodup_In. exact Hx'.
        * apply in_or_app. right. left. reflexivity.
      + intros Hx. apply in_app_or in Hx as [Hx | [<- | Hx]].
        * rewrite nodup_In in Hx. exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec' Hx).
        * exact Hqin.
        * exact (proj1 (HB1 x (HtB x Hx) (HtO x Hx))). }
  { assert (Hqi : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> rdW W2 mem2 a = rdW W memc a).
    { intros a Ha. destruct (PROGU a (s26_pg_img a ltac:(tauto))) as (Hi & Ho & He).
      apply (G3 a Hi Ho He). apply Hspare. intros Hf. destruct (HFP1 a Hf) as [H | (p & n & Hpn & _ & Hr)].
      - unfold A_G_QUITTING, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *. lia.
      - exact (blk_img SEGS B LAWS _ _ _ _ _ p n a HAR Hpn Hr Hi). }
    apply (aval_mem_agree _ _ _ 4 _ Hquit). intros kk Hkb. apply Hqi. cbn in Hkk. lia. }
- destruct Hline as (Hfr & Hs). split; [exact Hfr|].
  apply (astr_atR_agree _ _ q _ (Z.of_nat (length (Verbs.line (e_D e))) + 1) Hs); [lia|].
  intros kk Hkb. apply (KB q (vr_l (e_n e) (e_D e) + 1) kk Hlb HlbO Hlb2). lia.
- destruct Hcopy as (Hfr & Hal & Hlen & Hptr & Hw). split; [exact Hfr|].
  assert (Htk : (length (Verbs.toks (e_D e)) <= 64)%nat).
  { unfold Verbs.toks. rewrite length_firstn. unfold Verbs.line_words_max. lia. }
  split; [exact Hal|]. split; [exact Hlen|]. split.
  + intros i p Hi. pose proof (proj1 (nth_error_Some tp i) ltac:(rewrite Hi; discriminate)) as Hi'.
    apply (aval_mem_agree _ _ _ 8 _ (Hptr i p Hi)). intros kk Hkb. apply KF. left. lia.
  + intros i p w Hi Hwi. destruct (Hw i p w Hi Hwi) as (Hs & Hl8 & Hp1 & Hp2).
    split; [|split; [exact Hl8 | split; [exact Hp1 | exact Hp2]]].
    apply (astr_atR_agree _ _ p _ (Z.of_nat (length w) + 1) Hs); [lia|].
    intros kk Hkb. replace (p + kk) with (c + (p - c + kk)) by lia.
    apply (KB c (Z.of_nat (length (Verbs.line (e_D e))) + 1) (p - c + kk) Hcb HcbO Hcb2). lia.
Qed.

(* the walk from the return address 0x8d8ac to the join JA 0x8d6a0: s10 = the reply text and the reloads of s4, s6,
   s9 and s11 from the spill slots; with s26_post, the boundary vr_hd at JA *)
Lemma s26_cont : forall e j nmj led pos F q c tp lyc Sc W memc mdc k nm regsc ly2 S2 W2 mem2 md2 R' t qt O' regs2,
vr_ent B MT e ->
nth_error vr_tbl j = Some (nmj, led) ->
VRR.route (Verbs.toks (e_D e)) = VRR.RLedger led -> Verbs.toks (e_D e) <> [] ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(19, SHADOW_OFF + (0xa5c48 + 16 * Z.of_nat j) / 8); (21, vr_ntok (e_D e)); (26, hd 0 tp);
   (27, 0xa5c40 + 16 * Z.of_nat j)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  ly2 S2 W2 mem2 md2 (k + EV_SUP_INSTANCE_VERB (e_R e)) ->
ajournal SEGS B SUP_INSTANCE_VERB_STK (vr_s1 e) (s26_FP1 (e_O e)) lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2
  (EV_SUP_INSTANCE_VERB (e_R e)) ->
sup_instance_verb_m (e_R e) (Verbs.line (e_D e)) led = (R', t) ->
4096 <= qt < 2 ^ 64 ->
rec_repA B ly2 S2 (rdW W2 mem2) R' O' ->
(forall pn, In pn O' -> In pn (e_O e) \/ ~ In pn (ablocks B lyc Sc)) ->
In (qt, Z.of_nat (length t) + 1) (ablocks B ly2 S2) ->
(forall pn, In pn (ablocks B lyc Sc) -> ~ In pn (e_O e) -> pn <> (qt, Z.of_nat (length t) + 1)) -> ~ In qt (map fst O') ->
astr_atR (rdW W2 mem2) qt t ->
(forall pn, In pn (ablocks B lyc Sc) -> ~ In pn (e_O e) ->
  In pn (ablocks B ly2 S2) /\ iv_apart (fst pn) (snd pn) qt (Z.of_nat (length t) + 1)) ->
(forall pn, In pn (ablocks B ly2 S2) ->
  (In pn (ablocks B lyc Sc) /\ ~ In pn (e_O e)) \/ In pn O' \/ pn = (qt, Z.of_nat (length t) + 1)) ->
mo_le MT Sc S2 (XM_SUP_INSTANCE_VERB MT (e_R e) (Verbs.line (e_D e)) led) ->
vr_rv regs2 (vr_base B e ++ [(10, qt); (18, q); (21, vr_ntok (e_D e))]) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + S26_RET)) mem2 (seg_rom SEGS)) md2) (vr_athd B MT 0x8d6a0 e).
Proof.
intros e j nmj led pos F q c tp lyc Sc W memc mdc k nm regsc ly2 S2 W2 mem2 md2 R' t qt O' regs2
  Hent Hnth Hroute Htoks Hcore Hline Hcopy HJ2 HJc Hm Hqt Hrec' HO'1 Hqin Hqnot HqO' Hstr HB1 HB2 Hmle Hrv2.
destruct (s26_post e j nmj led pos F q c tp lyc Sc W memc mdc k nm regsc ly2 S2 W2 mem2 md2 R' t qt O' regs2 _
  Hent Hnth Hroute Htoks Hcore Hline Hcopy HJ2 HJc Hm (proj1 Hqt) Hrec' HO'1 Hqin Hqnot HqO' Hstr HB1 HB2 Hmle Hrv2)
  as (O1 & Hstr1 & Hcore2 & Hline2 & Hcopy2).
destruct (vr_led_model (e_R e) (e_D e) led Hroute Htoks) as [Hh Hk1].
assert (Hxe : vr_x (e_R e) (e_D e) = t) by (unfold vr_x; rewrite Hh, Hm; reflexivity).
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (_ & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _).
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
assert (HSTK0 : 224 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
destruct (vr_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
pose proof Hcore2 as (_ & _ & _ & _ & (HFa & _) & _ & _ & Hspill & _).
pose proof (vr_frames_own B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as Hin4.
destruct (vr_frame_bounds B _ _ _ _ _ pos HAR2 Hin4) as (BF1 & BF2 & BF3). rewrite <- HFa in BF1, BF2, BF3.
assert (Hlb : In (vr_lb e q) (ablocks B ly2 S2)) by (eapply vr_core_blocks; [exact Hcore2 | right; left; reflexivity]).
assert (Hcb : In (vr_cb e c) (ablocks B ly2 S2)) by (eapply vr_core_blocks; [exact Hcore2 | right; right; left; reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hlb) as (_ & Hq4096 & Hqc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hcb) as (_ & Hc4096 & Hcc & _).
unfold vr_lb, vr_cb in Hq4096, Hqc, Hc4096, Hcc. cbn [fst snd] in Hq4096, Hqc, Hc4096, Hcc.
assert (HL : 0 <= vr_l (e_n e) (e_D e) <= e_n e) by (apply verbs_receive_pre.strnlen_res_le; lia).
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as [Hrq1 Hrq2].
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [Hrc1 Hrc2].
assert (Hrows : forall r v, In (r, v) (vr_base B e ++ [(10, qt); (18, q); (21, vr_ntok (e_D e))]) ->
  getr regs2 (Z_to_bv 5 r) = w64 v) by (intros r v Hin; exact (vr_rv_get _ _ r v Hrv2 Hin)).
assert (R2 := Hrows 2 (vr_s1 e) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R3 := Hrows 3 (as_gp B) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R4 := Hrows 4 (as_tp B) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R8 := Hrows 8 (vr_sp0 e) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R9 := Hrows 9 (vr_s1 e) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R10 := Hrows 10 qt ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R18 := Hrows 18 q ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R21 := Hrows 21 _ ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (Hsp : forall o v, In (o, v) (vr_sl3 F q c) -> aval_mem (rdW W2 mem2) (vr_s1 e + o) 8 v)
  by (intros o v Hin; exact (vr_spill_get e W2 mem2 _ o v Hspill Hin)).
pose proof (s26_seed2 W2 regs2 mem2 (vr_s1 e) q F c R9 ltac:(unfold vr_sp0 in *; lia) ltac:(unfold vr_sp0 in *; lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos F 8); lia) ltac:(lia)
  (Hsp 8 _ ltac:(cbn; tauto)) (Hsp 16 _ ltac:(cbn; tauto)) (Hsp 24 _ ltac:(cbn; tauto))
  (Hsp 32 _ ltac:(cbn; tauto)) (Hsp 56 _ ltac:(cbn; tauto))) as HS.
remember (Eimg (Ereg regs2 (s26_extra q F c 0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r).
{ intros n r Hn. rewrite HE. apply ew_Eimg_Ereg_nat. exact Hn. }
assert (EX : forall i, (i < 5)%nat -> ew E (32 + i) = nth i (s26_extra q F c 0) (Z_to_bv 64 0)).
{ intros i Hi. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
pose proof HJ2 as HJ2m.
paj_run_to_sh RUNTO HS HJ2 S26_JA.
{ s26_awr. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq' | Hin]; [injection Hq' as <- <- <-; cbn in Hrr; lia|]); destruct Hin)) as UN2.
clear HF HFr HG.
match goal with |- context [with_vm_backing (m_vm_lazy md2) ?mt md2] =>
  set (mdv2 := with_vm_backing (m_vm_lazy md2) mt md2) in * end.
clearbody mdv2.
match goal with H : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => set (ms4 := m) in * end.
assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms4) a = rdW W2 mem2 a) by (intros a Ha; exact (UN2 a Ha (fun x => x))).
assert (K2 : vr_kept W2 mem2 (ms_mem ms4) (vr_s1 e)) by (intros a Ha _; exact (KM2 a Ha)).
prreg HS (Z_to_bv 5 2) T2. prreg HS (Z_to_bv 5 3) T3. prreg HS (Z_to_bv 5 4) T4.
prreg HS (Z_to_bv 5 8) T8. prreg HS (Z_to_bv 5 9) T9.
prreg HS (Z_to_bv 5 18) T18. prreg HS (Z_to_bv 5 20) T20. prreg HS (Z_to_bv 5 21) T21.
prreg HS (Z_to_bv 5 22) T22. prreg HS (Z_to_bv 5 25) T25.
prreg HS (Z_to_bv 5 26) T26. prreg HS (Z_to_bv 5 27) T27.
assert (X1 : ew E 33 = Z_to_bv 64 F) by exact (EX 1%nat ltac:(lia)).
assert (X3 : ew E 35 = Z_to_bv 64 (shadow_addr F)) by exact (EX 3%nat ltac:(lia)).
assert (HFsh : 0 <= shadow_addr F /\ shadow_addr F + 4 < 2 ^ 64)
  by (unfold shadow_addr, SHADOW_OFF in *; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia).
assert (Hrv4 : vr_rv (ms_regs ms4) (vr_base B e ++ vr_rl_hd e F q c 0x8d6a0 qt)).
{ replace (vr_rl_hd e F q c 0x8d6a0 qt) with [(26, qt); (20, F); (21, vr_ntok (e_D e)); (25, shadow_addr F); (18, q);
    (22, F); (27, shadow_addr F + 4)] by reflexivity.
  unfold vr_rv, vr_base. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn beta; cbn [fst snd].
  - rewrite T2, (EE 2%nat (Z_to_bv 5 2) eq_refl). exact R2.
  - rewrite T3, (EE 3%nat (Z_to_bv 5 3) eq_refl). exact R3.
  - rewrite T4, (EE 4%nat (Z_to_bv 5 4) eq_refl). exact R4.
  - rewrite T8, (EE 8%nat (Z_to_bv 5 8) eq_refl). exact R8.
  - rewrite T9, (EE 9%nat (Z_to_bv 5 9) eq_refl). exact R9.
  - rewrite T26, (EE 10%nat (Z_to_bv 5 10) eq_refl). exact R10.
  - rewrite T20, X1. reflexivity.
  - rewrite T21, (EE 21%nat (Z_to_bv 5 21) eq_refl). exact R21.
  - rewrite T25, X3. reflexivity.
  - rewrite T18, (EE 18%nat (Z_to_bv 5 18) eq_refl). exact R18.
  - rewrite T22, X1. reflexivity.
  - rewrite T27, X3, unsigned_lit_small by lia. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hqin) as (_ & _ & Hqc2 & _).
pose proof (req_size_pos (Z.of_nat (length t) + 1) ltac:(lia)) as [_ Hrt].
pmkst HS.
apply SRr_ret.
unfold vr_athd, vr_hd.
exists qt, O1, pos, F, q, c, tp, ly2, S2, (ms_regs ms4), (ms_mem ms4), mdv2, (k + EV_SUP_INSTANCE_VERB (e_R e)), (nm + 4).
split.
{ unfold cfg_at, vr_pc, w64, S26_JA, AF_verbs_receive. do 3 f_equal; try lia. }
split.
{ change (1 <= length (Verbs.toks (e_D e)))%nat.
  destruct (Verbs.toks (e_D e)) as [|t0 ts] eqn:Et; [contradiction|]. cbn [length]. lia. }
split; [exact (proj1 Hqt)|].
split.
{ apply (astr_atR_agree _ _ qt _ (Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1) Hstr1); [lia|].
  intros kk Hkb. rewrite Hxe in Hkb. apply KM2. lia. }
split.
{ exact (vr_core_kept B MT ROA RECC RRO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms4) (ms_mem ms4) mdv2
    Hcore2 HJ2 K2 ltac:(unfold vr_sl3; repeat constructor; cbn [fst]; lia) Hrv4). }
pose proof (vr_frames_own B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2m) as Hin42.
split.
{ apply (vr_line_kept B MT e q ly2 S2 W2 mem2 md2 (ms_mem ms4) (vr_s1 e) HAR2 Hent); [exact Hlb | exact Hline2 | exact K2]. }
{ apply (vr_copy_kept B e F c tp pos ly2 S2 W2 mem2 md2 (ms_mem ms4) (vr_s1 e) HAR2 Hin42 HFa); [exact Hcb | exact Hcopy2 | exact K2]. }
Qed.

End c.
End f.
End d.

Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis TSUP_INSTANCE_VERB : forall fx0 : YK11.FPState, @tsup_instance_verb_spec fx0 rc SK PI B MT.
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis SHOK : vr_shadow_ok B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

Lemma vr_s26 : vr_s26_stmt B MT.
Proof.
intros e W cf Hent Hled.
destruct Hled as (j & nmj & led & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hnth & Hroute
  & Htoks & Hcore & Hline & Hcopy).
destruct (vr_row_facts j nmj led Hnth) as (Hj10 & Hled01 & Hlit & Hnz & Hlen15 & Hrp1 & Hrp2 & Hend & Hshr).
destruct (vr_led_model (e_R e) (e_D e) led Hroute Htoks) as [Hh Hk1].
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE0 & HROD0 & _ & _ & _ & _ & _ & Hn8 & HlenD & HinD & HnotD & _ & _ & HREC0 & _ & _ & _ & _ & _
  & HpermE & _ & _ & _ & _ & _ & _ & _ & _ & Hfr4 & Hev & Hlive & Hmok & Hfrm).
pose proof Hcore as (HJ & Hkk & Hmeter & Hnm & Hframe & Hrv & Hsaved & Hspill & Henv & Hrec & HdO & Hperm & Hquit).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & Hnev & Hk0 & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
assert (HSTKc : SUP_INSTANCE_VERB_STK + 208 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSTKp : 2 * 4096 <= SUP_INSTANCE_VERB_STK) by (apply Z.leb_le; vm_compute; reflexivity).
destruct (vr_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
pose proof (vr_frames_own B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hin4.
destruct Hframe as (HFa & Hflag & Hshf).
destruct (vr_frame_bounds B _ _ _ _ _ pos HAR Hin4) as (BF1 & BF2 & BF3). rewrite <- HFa in BF1, BF2, BF3.
assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc)) by (eapply vr_core_blocks; [exact Hcore | left; reflexivity]).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)) by (eapply vr_core_blocks; [exact Hcore | right; left; reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hlb) as (_ & Hq4096 & Hqc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4096 & Hcc & _).
unfold vr_lb, vr_cb in Hq4096, Hqc, Hc4096, Hcc. cbn [fst snd] in Hq4096, Hqc, Hc4096, Hcc.
assert (HL : 0 <= vr_l (e_n e) (e_D e) <= e_n e) by (apply verbs_receive_pre.strnlen_res_le; lia).
assert (HLL : Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e)).
{ pose proof (vr_line_le (e_D e)). pose proof (verbs_receive_pre.strnlen_upto (e_D e)) as [_ L2].
  rewrite HlenD in L2. unfold vr_l. lia. }
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as [Hrq1 Hrq2].
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [Hrc1 Hrc2].
pose proof Henv as (HRO & HGOT & HROk & HGD & HFL & HERR).
assert (Hrows : forall r v, In (r, v) (vr_base B e ++
  [(19, SHADOW_OFF + (0xa5c48 + 16 * Z.of_nat j) / 8); (21, vr_ntok (e_D e)); (26, hd 0 tp);
   (27, 0xa5c40 + 16 * Z.of_nat j)]) ->
  getr regsc (Z_to_bv 5 r) = w64 v) by (intros r v Hin; exact (vr_rv_get _ _ r v Hrv Hin)).
assert (R2 := Hrows 2 (vr_s1 e) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R9 := Hrows 9 (vr_s1 e) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R8 := Hrows 8 (vr_sp0 e) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R3 := Hrows 3 (as_gp B) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R4 := Hrows 4 (as_tp B) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R19 := Hrows 19 _ ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R21 := Hrows 21 _ ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R27 := Hrows 27 _ ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (Esh : (0xa5c48 + 16 * Z.of_nat j) / 8 = 0x14b89 + 2 * Z.of_nat j)
  by (symmetry; apply Z.div_unique with (r := 0); lia).
rewrite Esh in R19.
assert (Msh : rdW W memc (SHADOW_OFF + (0x14b89 + 2 * Z.of_nat j)) = Some 0).
{ replace (SHADOW_OFF + (0x14b89 + 2 * Z.of_nat j)) with (SHADOW_OFF + 0x14b88 + (2 * Z.of_nat j + 1)) by lia.
  exact (vr_tab_shadow0 B SHOK _ _ _ _ _ (2 * Z.of_nat j + 1) HAR ltac:(lia)). }
assert (Mled : aval_mem (rdW W memc) (0xa5c40 + 16 * Z.of_nat j + 8) 4 led).
{ destruct (vr_tab_word _ (vr_tab_bytes _ HROk) j Hj10) as [_ Hw]. rewrite (vr_row_led j nmj led Hnth) in Hw.
  replace (0xa5c40 + 16 * Z.of_nat j + 8) with (0xa5c48 + 16 * Z.of_nat j) by lia. exact Hw. }
assert (Hsp : forall o v, In (o, v) (vr_sl3 F q c) -> aval_mem (rdW W memc) (vr_s1 e + o) 8 v)
  by (intros o v Hin; exact (vr_spill_get e W memc _ o v Hspill Hin)).
pose proof (s26_seed W regsc memc (vr_s1 e) (SHADOW_OFF + (0x14b89 + 2 * Z.of_nat j)) (0xa5c40 + 16 * Z.of_nat j)
  q F c led R9 R19 R27 ltac:(unfold vr_sp0 in *; lia) ltac:(unfold vr_sp0 in *; lia) ltac:(lia) ltac:(lia)
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos F 8); lia) ltac:(lia)
  ltac:(destruct Hled01 as [-> | ->]; lia)
  (Hsp 8 _ ltac:(cbn; tauto)) (Hsp 16 _ ltac:(cbn; tauto)) (Hsp 24 _ ltac:(cbn; tauto))
  (Hsp 32 _ ltac:(cbn; tauto)) (Hsp 56 _ ltac:(cbn; tauto)) Msh Mled) as HS.
assert (Hcfg : cfg_at SEGS (vr_pc 0x8d894) regsc memc mdc =
  mkCfg (mkst regsc (Z_to_bv 64 (BASE + S26_PC)) memc (seg_rom SEGS)) mdc).
{ unfold cfg_at, vr_pc, w64, S26_PC, AF_verbs_receive. do 3 f_equal; try lia. }
rewrite Hcfg. clear Hcfg.
remember (Eimg (Ereg regsc (s26_extra q F c led))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. rewrite HE. apply ew_Eimg_Ereg_nat. exact Hn. }
assert (EX : forall i, (i < 5)%nat -> ew E (32 + i) = nth i (s26_extra q F c led) (Z_to_bv 64 0)).
{ intros i Hi. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
paj_run_shc RUNP RUNC HS HJ.
{ s26_awr. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr
  ltac:(intros b wlo whi a Hin Hrr; unfold s26_ss in Hin; vm_compute in Hin;
        repeat (destruct Hin as [Hq' | Hin]; [injection Hq' as <- <- <-; cbn in Hrr; lia|]); destruct Hin)) as UN1.
clear HF HFr HG.
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W memc a) by (intros a Ha; exact (UN1 a Ha (fun x => x))).
assert (K1 : vr_kept W memc (ms_mem ms) (vr_s1 e)) by (intros a Ha _; exact (KM a Ha)).
prreg HS (Z_to_bv 5 1) Q1. prreg HS (Z_to_bv 5 2) Q2. prreg HS (Z_to_bv 5 3) Q3. prreg HS (Z_to_bv 5 4) Q4.
prreg HS (Z_to_bv 5 8) Q8. prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11.
prreg HS (Z_to_bv 5 9) Q9. prreg HS (Z_to_bv 5 18) Q18. prreg HS (Z_to_bv 5 21) Q21.
rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9 in Q9.
rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21 in Q21.
rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), R2 in Q2.
rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl), R3 in Q3.
rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl), R4 in Q4.
rewrite (EE 8%nat (Z_to_bv 5 8) eq_refl), R8 in Q8.
assert (X0 : ew E 32 = Z_to_bv 64 q) by exact (EX 0%nat ltac:(lia)).
assert (X4 : ew E 36 = Z_to_bv 64 led) by exact (EX 4%nat ltac:(lia)).
rewrite X0 in Q10. rewrite X0 in Q18.
assert (Q11' : getr (ms_regs ms) (Z_to_bv 5 11) = w64 led).
{ rewrite Q11, X4.
  unfold w64. destruct Hled01 as [-> | ->]; apply bv_eq; vm_compute; reflexivity. }
clear Q11.
assert (Qsp : spZ (ms_regs ms) = vr_sp0 e + (vr_s1 e - vr_sp0 e)).
{ change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) (Z_to_bv 5 2))). rewrite Q2. unfold w64.
  rewrite unsigned_lit_small by (unfold vr_sp0 in *; lia). lia. }
pose proof (proj1 HJ) as HAR1.
pmkst HS.
(* the boundary at the call's memory *)
pose proof (vr_core_kept B MT ROA RECC RRO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regsc (ms_mem ms) mdv Hcore HJ K1
  ltac:(unfold vr_sl3; repeat constructor; cbn [fst]; lia) Hrv) as Hcore1.
pose proof (vr_line_kept B MT _ _ _ _ _ _ _ _ _ HAR Hent Hlb Hline K1) as Hline1.
pose proof (vr_copy_kept B _ _ _ _ _ _ _ _ _ _ _ _ HAR Hin4 HFa Hcb Hcopy K1) as Hcopy1.
(* the frame chain at the call: verbs_receive's own record on top of its caller's chain (the B kit's vr_chain_at) *)
pose proof Hcore1 as (_ & _ & _ & _ & _ & _ & Hsaved1 & _).
destruct (vr_chain_at B MT RRO RPG RECC PROGU ROA e lyc Sc W (ms_mem ms) mdv k pos (ms_regs ms) Hent HJ Hsaved1 Q8)
  as (ch1 & Hch1).
assert (Hch2 : achain lyc (rdW W (ms_mem ms)) (vr_sp0 e + (vr_s1 e - vr_sp0 e)) (s0Z (ms_regs ms)) ch1)
  by (replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) by lia; exact Hch1).
assert (HND : List.NoDup (e_O e ++ [vr_lb e q; vr_cb e c] ++ e_rest e)).
{ apply (Permutation_NoDup Hperm). exact (RecBLemmas.recb_ablocks_nodup_m B _ _ _ _ _ HAR). }
assert (HlbO : ~ In (vr_lb e q) (e_O e)).
{ intros H. exact (s26_nodup_disj _ _ _ HND H (or_introl eq_refl)). }
assert (HOin : forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
assert (HFPlo : forall a, inFP (s26_FP1 (e_O e)) a -> a < alloc_ceiling).
{ intros a Ha. destruct (s26_inFP1 _ _ Ha) as [H | [H | (p & n & Hpn & Hr)]];
  [unfold A_G_REC, REC_SIZE in H; lia | unfold A_REC_SPILL, SC_SIZE in H; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HOin _ Hpn)) as (_ & _ & Hc & _). lia. }
assert (HROm : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms))).
{ intros a Hro Ho He. assert (Hi : in_img SEGS a).
  { destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]. }
  pose proof (pa_img_range a Hi). rewrite KM by lia. exact (HRO a Hro Ho He). }
assert (HkEV : k + EV_SUP_INSTANCE_VERB (e_R e) <= ev_vr (e_R e) (e_D e)).
{ rewrite ev_vr_eq. unfold vr_k3, vr_k2. rewrite Hk1.
  pose proof s26_ev_reply. pose proof (s26_ev_after (vr_R2 (e_R e) (e_D e)) (vr_aft (e_D e))). lia. }
assert (HevS : st_nev Sc + EV_SUP_INSTANCE_VERB (e_R e) <= EV_MAX).
{ rewrite ev_vr_eq in Hev. unfold vr_k3, vr_k2 in Hev. rewrite Hk1 in Hev.
  pose proof s26_ev_reply. pose proof (s26_ev_after (vr_R2 (e_R e) (e_D e)) (vr_aft (e_D e))). lia. }
eapply SRr_bind.
{ eapply (cl_callS_wideF B LAWS W (ms_regs ms) (ms_mem ms) _ VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e)
    (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdv k SUP_INSTANCE_VERB_STK (s26_FP1 (e_O e))
    (EV_SUP_INSTANCE_VERB (e_R e)) (vr_s1 e - vr_sp0 e) (Z_to_bv 64 (BASE + S26_RET)) ch1
    (fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (qt : Z) (O' : list (Z * Z)),
       sup_instance_verb_m (e_R e) (Verbs.line (e_D e)) led = (R', t) /\
       getr regs' 10 = w64 qt /\ 4096 <= qt < 2 ^ 64 /\
       rec_repA B ly' S' (rdW W' mem') R' O' /\
       (forall pn, In pn O' -> In pn (e_O e) \/ ~ In pn (ablocks B lyc Sc)) /\
       In (qt, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
       (forall pn, In pn (ablocks B lyc Sc) -> ~ In pn (e_O e) -> pn <> (qt, Z.of_nat (length t) + 1)) /\
       ~ In qt (map fst O') /\
       astr_atR (rdW W' mem') qt t /\
       (forall pn, In pn (ablocks B lyc Sc) -> ~ In pn (e_O e) ->
          In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) qt (Z.of_nat (length t) + 1)) /\
       (forall pn, In pn (ablocks B ly' S') ->
          (In pn (ablocks B lyc Sc) /\ ~ In pn (e_O e)) \/ In pn O' \/ pn = (qt, Z.of_nat (length t) + 1)) /\
       blocks_bytes S' <= blocks_bytes Sc + LIVE_SUP_INSTANCE_VERB (e_R e) (Verbs.line (e_D e)) led /\
       mo_le MT Sc S' (XM_SUP_INSTANCE_VERB MT (e_R e) (Verbs.line (e_D e)) led)) HJ).
  - exact Qsp.
  - exact Hs1o.
  - lia.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold S26_RET; lia | reflexivity].
  - rewrite unsigned_lit_small by (pose proof pa_B_ok; unfold S26_RET; lia). pose proof pa_base_lo. unfold S26_RET. lia.
  - exact Hch2.
  - intros HPRE1.
    rewrite (SIGP CS_sup_instance_verb) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
    change (cmd_af CS_sup_instance_verb) with AF_sup_instance_verb.
    eapply SRr_mono.
    { apply (TSUP_INSTANCE_VERB fx lyc Sc W (ms_regs ms) (ms_mem ms) mdv ch1 q led (Verbs.line (e_D e)) (e_R e) (e_O e)
        HPRE1 Hfrm HROm (ROA _ _ _ _ _ HAR1 HROm) Q10 ltac:(lia) Q11' ltac:(destruct Hled01 as [-> | ->]; lia)).
      - exists q, (vr_l (e_n e) (e_D e) + 1). split; [exact Hlb | lia].
      - destruct Hline1 as (_ & Hs). exact Hs.
      - unfold LMAX; lia.
      - rewrite Forall_forall. intros [b m] Hbm. cbn [fst snd].
        pose proof (HOin _ Hbm) as Hbm'.
        assert (Hne : (b, m) <> vr_lb e q) by (intros E1; rewrite E1 in Hbm; exact (HlbO Hbm)).
        pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ b m q (vr_l (e_n e) (e_D e) + 1) HAR Hbm' Hlb Hne) as Hd.
        destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hbm') as (_ & _ & _ & _ & _ & _ & Hm0).
        pose proof (req_size_pos m ltac:(lia)) as [_ Hrm].
        unfold zdisjoint, iv_apart in *. cbn [fst snd] in Hd. lia.
      - exact (vr_rec_kept B _ _ _ _ _ _ _ _ _ HAR Hrec K1).
      - rewrite Hfrs. cbn [app length]. lia.
      - exact HevS.
      - apply (s26_live B e lyc Sc (vr_lb e q) (vr_cb e c)); [exact Hlive | exact HpermE | exact Hperm | unfold vr_lb; cbn; lia
          | unfold vr_cb; cbn; lia | lia | exact Hled01].
      - exact (proj1 (s26_meter_call B MT MTL e Sc k nm (Verbs.line (e_D e)) led Hent Hmeter ltac:(lia) Hled01 HkEV)). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & HR & HC & HJc & HP & HQ).
    exists fx', ly', S', regs', mem', md'. split; [unfold S26_RET; rewrite <- Q1; reflexivity|].
    split; [exact HR|]. split; [exact HC|]. split; [exact HJc|]. split; [exact HP | exact HQ].
  - intros a Ha. destruct (s26_inFP1 _ _ Ha) as [H | [H | (p & n & Hpn & Hr)]].
    + right; right; right; right; left.
      split; [exists (A_G_REC, A_G_REC + REC_SIZE); split; [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; left; reflexivity | exact H]|].
      split; [rewrite (YF0m.ts_prog B HB); unfold YF0m.TFIB_PROG_STATIC;
        repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold A_G_REC, REC_SIZE in *; lia | apply Exists_cons_tl])|].
      exact (proj1 (PROGU a (s26_pg_img a ltac:(tauto)))).
    + right; right; right; right; left.
      split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split; [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; right; left; reflexivity | exact H]|].
      split; [rewrite (YF0m.ts_prog B HB); unfold YF0m.TFIB_PROG_STATIC;
        repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold A_REC_SPILL, SC_SIZE in *; lia | apply Exists_cons_tl])|].
      exact (proj1 (PROGU a (s26_pg_img a ltac:(tauto)))).
    + right; left. split.
      * exists (p, p + req_size n). split; [|cbn [fst snd]; lia].
        unfold vr_fp. apply in_or_app. right. unfold ablocks_fp. apply in_map_iff. exists (p, n). split; [reflexivity | exact Hpn].
      * exists p, n. split; [exact (HOin _ Hpn) | exact Hr].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (HFPlo a Ha). lia. }
cbv beta. intros W3 c3 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJc & HP &
  (R' & t & qt & O' & Hm & Ha0 & Hqt & Hrec' & HO'1 & Hqin & Hqnot & HqO' & Hstr & HB1 & HB2 & Hbb & Hmle)).
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
(* the registers after the call: the callee-saved ones as at the call, a0 the reply text *)
assert (Hrv2 : vr_rv regs2 (vr_base B e ++ [(10, qt); (18, q); (21, vr_ntok (e_D e))])).
{ unfold vr_rv, vr_base. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn beta; cbn [fst snd].
  - rewrite (HP 2 ltac:(unfold acallee_saved; lia)). exact Q2.
  - rewrite (HP 3 ltac:(unfold acallee_saved; lia)). exact Q3.
  - rewrite (HP 4 ltac:(unfold acallee_saved; lia)). exact Q4.
  - rewrite (HP 8 ltac:(unfold acallee_saved; lia)). exact Q8.
  - rewrite (HP 9 ltac:(unfold acallee_saved; lia)). exact Q9.
  - exact Ha0.
  - rewrite (HP 18 ltac:(unfold acallee_saved; lia)). exact Q18.
  - rewrite (HP 21 ltac:(unfold acallee_saved; lia)). exact Q21. }
(* the walk after the call, at the FP state fx' the callee returned at *)
eapply SRr_mono.
{ exact (s26_cont (fx := fx') B MT MTL ROA RRO RPG RECC PROGU e j nmj led pos F q c tp lyc Sc W (ms_mem ms) mdv k nm regsc
    ly2 S2 W3 mem2 md2 R' t qt O' regs2 (vr_ent_fx (fx := fx) fx' B MT e Hent (fxrel_frm0 fx fx' Hfrm Hfx))
    Hnth Hroute Htoks Hcore1 Hline1 Hcopy1 HJ2 HJc Hm Hqt Hrec' HO'1 Hqin Hqnot HqO' Hstr HB1 HB2 Hmle Hrv2). }
cbv beta. intros W' cf' _ H. exists fx'. split; [exact Hfx | exact H].
Qed.

End e.

End f2.
End d2.
