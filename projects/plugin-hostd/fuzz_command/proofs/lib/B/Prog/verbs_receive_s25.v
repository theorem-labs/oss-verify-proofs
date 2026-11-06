(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S25 SCAN (0x8d7e0-0x8d82c) of the walk of verbs_receive on the ASan+UBSan
   build (image B) of plugin-hostd/fuzz_command (interface: lib/B/Prog/verbs_receive_iface.v, vr_s25_stmt): for a verb
   whose route lies behind the scan (vr_rt_tail), the loop over the 10 rows of g_instance_info_verbs (0xa5c40): per row
   the inline check of the name word (lbu of its shadow byte at s7, 0 by the table's zero shadow; the report call at
   0x8d9bc is not reached), the load of the name pointer through s11 = s4 + s2 and strcmp(verb, name) through a Theorem Labs lane's
   contract and PaArt.aj_art_at; a match leaves for the ledger call 0x8d894 (vr_led), ten misses for 0x8d830
   (vr_s27in). One lemma proves a pass at any row j from the header state 0x8d804 (the table and its data are image
   constants, so each pass runs concretely); the ten passes are chained by induction on the rows left. The B twin of
   lib/A/Prog/verbs_receive_s25.v, its runs redone on B's code and registers (s2 = 16 j, s4 = the table, s6 = 160,
   s7 / s3 = the shadow bytes of the row's name / ledger word). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_s30_kit verbs_receive_s25_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the listing offsets: AF_verbs_receive = 0x691c = 26908 is 0x8ce4c *)
Definition S25_E : Z := 29360.     (* 0x8d7e0, the scan's entry *)
Definition S25_H : Z := 29396.     (* 0x8d804, the loop header *)
Definition S25_LED : Z := 29540.   (* 0x8d894, a row matched *)
Definition S25_X : Z := 29440.     (* 0x8d830, no row matched *)

(* the symbolic state at the header of pass j: the registers as atoms; the shadow byte of the row's name word (at
   s7) and the name word (at s11 = s4 + s2, atom 32 by the alias fact; its value is atom 33) *)
Definition s25_r0 : YP09.region := YP09.mkRegion (Some 23%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition s25_r1 : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition s25_ss : sstate := mkSS S25_H sr_atoms [s25_r0; s25_r1] None
  (mkFacts [] [] [(SAlu ALU_ADD (SOff 20 0) (SOff 18 0), SOff 32 0)]).
Definition s25_extra (j : nat) : list word := [Z_to_bv 64 (0xa5c40 + 16 * Z.of_nat j); Z_to_bv 64 (vr_rowp j)].
(* the symbolic state at the scan's entry: the registers as atoms, no memory read *)
Definition s25_ss0 : sstate := mkSS S25_E sr_atoms [] None (mkFacts [] [] []).

Ltac s25_awr :=
lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Ltac s25_unchanged segs UN HFr :=
pose proof (kept_of_frame (segs := segs) _ _ _ _ _ (fun _ => False) HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
        let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
        intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn in Hrr; lia|]); destruct Hin)) as UN.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the registers at the header of pass j (B's allocation): s2 = 16 j, s3/s7 = the shadow bytes of the row's ledger
   and name words, s4 = the table, s5 = s9 = the word count, s6 = 160, s10 = the verb *)
Definition vr_rl_scan (e : vrE) (v : Z) (j : nat) : list (Z * Z) :=
[(18, 16 * Z.of_nat j); (19, SHADOW_OFF + 0x14b89 + 2 * Z.of_nat j); (20, 0xa5c40); (21, vr_ntok (e_D e));
 (22, 160); (23, SHADOW_OFF + 0x14b88 + 2 * Z.of_nat j); (25, vr_ntok (e_D e)); (26, v)].


Lemma s25_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem j, (j < 10)%nat ->
getr regs (Z_to_bv 5 20) = w64 0xa5c40 -> getr regs (Z_to_bv 5 18) = w64 (16 * Z.of_nat j) ->
getr regs (Z_to_bv 5 23) = w64 (SHADOW_OFF + 0x14b88 + 2 * Z.of_nat j) ->
rdW W mem (SHADOW_OFF + 0x14b88 + 2 * Z.of_nat j) = Some 0 ->
aval_mem (rdW W mem) (0xa5c40 + 16 * Z.of_nat j) 8 (vr_rowp j) ->
0x22920 <= vr_rowp j <= 0x22a50 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (s25_extra j))) s25_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S25_H)) mem (seg_rom SEGS))).
Proof.
intros W regs mem j Hj H20 H18 H23 Msh Mw Hrp.
set (E := Eimg (Ereg regs (s25_extra j))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. subst E. apply ew_Eimg_Ereg_nat. exact Hn. }
assert (X0 : ew E 32 = Z_to_bv 64 (0xa5c40 + 16 * Z.of_nat j)).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs (s25_extra j) 0). }
assert (X1 : ew E 33 = Z_to_bv 64 (vr_rowp j)).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs (s25_extra j) 1). }
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF + 0x14b88 + 2 * Z.of_nat j).
{ rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), H23. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (U32 : bv_unsigned (ew E 32) = 0xa5c40 + 16 * Z.of_nat j).
{ rewrite X0. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. unfold s25_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, s25_r0, s25_r1;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U23. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (SHADOW_OFF + 0x14b88 + 2 * Z.of_nat j) 0 1 (SLit 0) 0);
    [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
    apply vr_val_mem_of_aval. intros kk Hkk. destruct kk as [|kk]; [|cbn in Hkk; lia].
    rewrite ?Z.add_0_r. cbn [Z.of_nat]. rewrite ?Z.add_0_r. rewrite Msh. reflexivity.
  + rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (0xa5c40 + 16 * Z.of_nat j) 0 8 (SOff 33 0) (vr_rowp j));
    [cbn [sv_denot]; rewrite X1, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | rewrite Z.add_0_r; apply vr_val_mem_of_aval; exact Mw].
- apply pairwise_disjoint_of_extents. unfold s25_r0, s25_r1, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite U23, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, SHADOW_OFF. cbn [fst snd]. repeat split; lia.
- split; [exact I|]. split; [exact I|]. split; [|exact I].
  cbn [sv_denot]. rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), (EE 18%nat (Z_to_bv 5 18) eq_refl), H20, H18, X0.
  unfold w64. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
  rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw].
  rewrite (zcanon_id 0xa5c40) by (unfold M64; lia). rewrite (zcanon_id (16 * Z.of_nat j)) by (unfold M64; lia).
  apply Z_to_bv64_canon.
Qed.


Lemma s25_cfg : forall regs mem md pc off, off = AF_verbs_receive + (pc - 0x8ce4c) ->
mkCfg (mkst regs (Z_to_bv 64 (BASE + off)) mem (seg_rom SEGS)) md = cfg_at SEGS (vr_pc pc) regs mem md.
Proof. intros regs mem md pc off Ho. unfold cfg_at, vr_pc, w64. rewrite Ho. reflexivity. Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis STRCMP : forall fx0 : YK11.FPState, @RtString.astrcmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcmp).
Hypothesis TL : PALib B.
Hypothesis SHOK : vr_shadow_ok B.
Hypothesis BLKT : vr_blktail B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RECC : vr_rec_cells B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let ART := aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL).

(* the state at the header of pass j: the rows before j did not match the verb *)
Definition vr_hdr (e : vrE) (j : nat) : world SEGS -> config -> Prop := fun Wc cf =>
exists r pos F q c tp lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc 0x8d804) regsc memc mdc /\
vr_is_tail r = true /\ VRR.route (Verbs.toks (e_D e)) = r /\ Verbs.toks (e_D e) <> [] /\
Verbs.ledger_of (hd [] (Verbs.toks (e_D e))) (firstn j vr_tbl) = None /\
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_scan e (hd 0 tp) j)
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc Wc regsc memc mdc /\
vr_line B e q Wc memc /\ vr_copy B e F c tp Wc memc.

(* a boundary of the scan from the one before: same allocator state, memory kept, new registers *)
Lemma s25_mk : forall e pos F q c tp lyc Sc W regsc memc mdc k nm rl rl' regs' mem' md',
vr_ent B MT e ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem' md' k ->
vr_kept W memc mem' (vr_s1 e) ->
vr_rv regs' (vr_base B e ++ rl') ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl' (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc W regs' mem' md' /\ vr_line B e q W mem' /\ vr_copy B e F c tp W mem'.
Proof.
intros e pos F q c tp lyc Sc W regsc memc mdc k nm rl rl' regs' mem' md' Hent Hcore Hline Hcopy HJ' K Hrv'.
pose proof Hcore as (HJ & _ & _ & _ & (HFa & _) & _).
pose proof (proj1 HJ) as HAR.
split; [exact (vr_core_kept B MT ROA RECC RRO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs' mem' md' Hcore HJ' K
  ltac:(unfold vr_sl3; repeat constructor; cbn [fst]; lia) Hrv')|].
split.
- apply (vr_line_kept B MT e q lyc Sc W memc mdc mem' (vr_s1 e) HAR Hent); [|exact Hline | exact K].
  eapply vr_core_blocks; [exact Hcore | left; reflexivity].
- apply (vr_copy_kept B e F c tp pos lyc Sc W memc mdc mem' (vr_s1 e) HAR); [| exact HFa | | exact Hcopy | exact K].
  + exact (vr_frames_own B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
  + eapply vr_core_blocks; [exact Hcore | right; left; reflexivity].
Qed.


Lemma s25_pass : forall e j W cf, vr_ent B MT e -> (j < 10)%nat -> vr_hdr e j W cf ->
SRr SEGS W cf (fun W' cf' => vr_led B MT e W' cf' \/ vr_s27in B MT e W' cf' \/
  ((j < 9)%nat /\ vr_hdr e (S j) W' cf')).
Proof.
intros e j W cf Hent Hj Hhdr.
destruct Hhdr as (r & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Htail & Hroute & Htoks
  & Hlf & Hcore & Hline & Hcopy).
destruct (nth_error vr_tbl j) as [[nmj led]|] eqn:Hnth;
  [|exfalso; apply nth_error_None in Hnth; rewrite vr_tbl_len in Hnth; lia].
destruct (vr_row_facts j nmj led Hnth) as (_ & Hled01 & Hlit & Hnz & Hlen15 & Hrp1 & Hrp2 & Hend & Hshr).
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _).
pose proof Hcore as (HJ & Hkk & Hmeter & Hnm & Hframe & Hrv & Hsaved & Hspill & Henv & Hrec & HdO & Hperm & Hquit).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
assert (HSTK : 2 * 4096 + 224 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HES : ESTACK = 4096) by reflexivity.
destruct (vr_s1_facts e Hal16) as (Hs1m & Hs1b & Hs1o).
pose proof Henv as (HRO & HGOT & HROk & HGD & HFL & HERR).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)) by (eapply vr_core_blocks; [exact Hcore | right; left; reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4096 & Hcc & _).
unfold vr_cb in Hc4096, Hcc. cbn [fst snd] in Hc4096, Hcc.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [Hrc1 Hrc2].
assert (Hw : exists w args, Verbs.toks (e_D e) = w :: args)
  by (destruct (Verbs.toks (e_D e)) as [|w args]; [contradiction | eauto]).
destruct Hw as (w & args & Et).
pose proof Hcopy as (Hfr & Hal & Hlen & Hptr & Hwrd).
assert (Htp : exists v tps, tp = v :: tps) by (destruct tp as [|v tps]; [rewrite Et in Hlen; discriminate Hlen | eauto]).
destruct Htp as (v & tps & ->).
destruct (Hwrd 0%nat v w eq_refl ltac:(rewrite Et; reflexivity)) as (Hvw & Hw8 & Hcv & Hvc).
assert (Hrows : forall rr vv, In (rr, vv) (vr_base B e ++ vr_rl_scan e (hd 0 (v :: tps)) j) ->
  getr regsc (Z_to_bv 5 rr) = w64 vv) by (intros rr vv Hin; exact (vr_rv_get _ _ rr vv Hrv Hin)).
assert (R2 := Hrows 2 (vr_s1 e) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R3 := Hrows 3 (as_gp B) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R4 := Hrows 4 (as_tp B) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R8 := Hrows 8 (vr_sp0 e) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R9 := Hrows 9 (vr_s1 e) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R18 := Hrows 18 _ ltac:(unfold vr_base, vr_rl_scan; cbn [app In]; tauto)).
assert (R19 := Hrows 19 _ ltac:(unfold vr_base, vr_rl_scan; cbn [app In]; tauto)).
assert (R20 := Hrows 20 _ ltac:(unfold vr_base, vr_rl_scan; cbn [app In]; tauto)).
assert (R21 := Hrows 21 _ ltac:(unfold vr_base, vr_rl_scan; cbn [app In]; tauto)).
assert (R22 := Hrows 22 _ ltac:(unfold vr_base, vr_rl_scan; cbn [app In]; tauto)).
assert (R23 := Hrows 23 _ ltac:(unfold vr_base, vr_rl_scan; cbn [app In]; tauto)).
assert (R25 := Hrows 25 _ ltac:(unfold vr_base, vr_rl_scan; cbn [app In]; tauto)).
assert (R26 := Hrows 26 v ltac:(unfold vr_base, vr_rl_scan; cbn [app In hd]; tauto)).
pose proof (s25_seed W regsc memc j Hj R20 R18 R23
  (vr_tab_shadow0 B SHOK lyc Sc W memc mdc (2 * Z.of_nat j) HAR ltac:(lia))
  (proj1 (vr_tab_word _ (vr_tab_bytes _ HROk) j Hj)) ltac:(lia)) as HS.
rewrite <- (s25_cfg regsc memc mdc 0x8d804 S25_H ltac:(unfold S25_H, AF_verbs_receive; lia)).
remember (Eimg (Ereg regsc (s25_extra j))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regsc rr).
{ intros n rr Hn. rewrite HE. apply ew_Eimg_Ereg_nat. exact Hn. }
assert (X0 : ew E 32 = Z_to_bv 64 (0xa5c40 + 16 * Z.of_nat j)).
{ rewrite HE, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regsc (s25_extra j) 0). }
assert (X1 : ew E 33 = Z_to_bv 64 (vr_rowp j)).
{ rewrite HE, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regsc (s25_extra j) 1). }
paj_run_shc RUNP RUNC HS HJ.
{ s25_awr. }
s25_unchanged (@pa_segs _ cmd_listing PI) UN1 HFr. clear HF HFr HG.
match goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] =>
  set (mdv := with_vm_backing (m_vm_lazy mdc) mt mdc) in * end.
clearbody mdv.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W memc a) by (intros a Ha; exact (UN1 a Ha (fun x => x))).
assert (K1 : vr_kept W memc (ms_mem ms) (vr_s1 e)) by (intros a Ha _; exact (KM a Ha)).
prreg HS (Z_to_bv 5 1) Q1. prreg HS (Z_to_bv 5 2) Q2. prreg HS (Z_to_bv 5 3) Q3. prreg HS (Z_to_bv 5 4) Q4.
prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11.
rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), R2 in Q2.
rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl), R3 in Q3.
rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl), R4 in Q4.
rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), R26 in Q10.
rewrite X1 in Q11.
assert (Qsp : spZ (ms_regs ms) = vr_sp0 e + (vr_s1 e - vr_sp0 e)).
{ change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) (Z_to_bv 5 2))). rewrite Q2. unfold w64.
  rewrite unsigned_lit_small by (unfold vr_sp0 in *; lia). lia. }
assert (Hra : YK0s.ret_ok (getr (ms_regs ms) (Z_to_bv 5 1))) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
pmkst HS.
pose proof (proj1 HJ) as HAR1.
pose proof (ecall_pre_stk_at SEGS B (2 * ESTACK) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e)
  (e_md e) [(4, pos)] lyc Sc W (ms_mem ms) mdv k (ms_regs ms) (vr_s1 e - vr_sp0 e) HJ Qsp Hs1o ltac:(lia) ltac:(lia)
  ltac:(lia) Hra Q3 Q4) as HPRE1.
assert (HROm : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms))).
{ intros a Hro Ho He. assert (Hi : in_img SEGS a).
  { destruct Hro as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | exact Hr] | exact (RRO a Hr)]. }
  pose proof (pa_img_range a Hi). rewrite KM by lia. exact (HRO a Hro Ho He). }
pose proof (ROA _ _ _ _ _ HAR1 HROm) as HROkm.
assert (Hlitm : abytes_atR (rdW W (ms_mem ms)) (vr_rowp j) (nmj ++ [Z_to_bv 8 0])).
{ rewrite <- Hlit. exact (vr_row_bytes _ HROkm j Hj). }
assert (Hvwm : astr_atR (rdW W (ms_mem ms)) v w).
{ apply (astr_atR_agree _ _ v w (Z.of_nat (length w) + 1) Hvw); [lia|]. intros kk Hkb. apply KM. lia. }
assert (Hcbm : In (vr_cb e c) (ablocks B lyc Sc)) by exact Hcb.
eapply SRr_bind.
{ eapply (ART (2 * ESTACK) (fun _ => False) _ W (ms_regs ms) (ms_mem ms) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e)
    (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdv k (vr_s1 e - vr_sp0 e) _
    (fun regs' _ => getr regs' 10 = w64 0 <-> w = nmj) HJ);
  [exact Qsp | exact Hs1o | lia | lia | lia | exact Q1 | intros a [] |].
  apply (STRCMP fx lyc Sc W (ms_regs ms) (ms_mem ms) mdv v (vr_rowp j) w nmj HPRE1 Q10 Q11).
  - lia.
  - lia.
  - apply astr_atR_view. exact Hvwm.
  - apply astr_atR_view. split; [exact Hlitm | exact Hnz].
  - apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) lyc Sc W (ms_regs ms) (ms_mem ms) mdv c
      (Z.of_nat (length (Verbs.line (e_D e))) + 1) v (astr_len w + 1) HAR1 Hcb); unfold astr_len; [lia | lia | lia |].
    rewrite Qsp. unfold vr_sp0 in *. lia.
  - unfold astr_len. destruct (SHOK lyc Sc W (ms_mem ms) mdv _ _ HAR1 Hshr) as [HRA HHV].
    rewrite Hlit, length_app in HRA, HHV. cbn [length] in HRA, HHV. rewrite Nat2Z.inj_add in HRA, HHV. cbn [Z.of_nat Pos.of_succ_nat] in HRA, HHV.
    split; [lia|]. split; [lia|]. split; [lia|].
    split.
    { intros a Ha. split.
      - replace a with (vr_rowp j + Z.of_nat (Z.to_nat (a - vr_rowp j))) by lia.
        rewrite (Hlitm (Z.to_nat (a - vr_rowp j))); [discriminate|]. rewrite length_app. cbn [length]. lia.
      - unfold ascratch_stk. rewrite Qsp. unfold vr_sp0 in *. lia. }
    split; [left; unfold kLowMemEnd; lia|]. split; [exact HRA | intros _; exact HHV].
  - unfold astr_len. apply (BLKT lyc Sc W (ms_mem ms) mdv c (Z.of_nat (length (Verbs.line (e_D e))) + 1)); [exact HAR1 | exact Hcb | lia].
  - unfold astr_len. destruct HROkm as [_ HT]. intros a Ha. exact (HT _ Hend a Ha).
  - exact (vr_rtrom_ok B W (ms_mem ms) HROm). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2').
assert (K2 : vr_kept W (ms_mem ms) mem2 (vr_s1 e)).
{ intros a Ha Hb. apply HK2'; [exact Ha | | intros []]. unfold vr_sp0 in *. lia. }
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
lazymatch type of HS2 with ?P -> _ => assert (HQ : P); [constructor | specialize (HS2 HQ); clear HQ] end.
rewrite <- restrict_mkst_fx in HS2.
pose proof (img_env_havoc_hi E 1024 (map (getr regs2) CLOB) HEI ltac:(unfold A_LIM; lia)) as HEI2.
assert (Ua0 : U (havoc E 1024 (map (getr regs2) CLOB)) (SOff 1028 0) = bv_unsigned (getr regs2 10)).
{ unfold U. cbn [sv_denot]. change 1028%nat with (1024 + 4)%nat.
  rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbn; lia). unfold CLOB. cbn [map nth].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Esh : (0xa5c48 + 16 * Z.of_nat j) / 8 = 0x14b89 + 2 * Z.of_nat j)
  by (symmetry; apply Z.div_unique with (r := 0); lia).
assert (Hroute' : vr_is_tail (VRR.route (w :: args)) = true) by (rewrite <- Et, Hroute; exact Htail).
rewrite Et in Hlf. cbn [hd] in Hlf.
assert (EO : forall n, (n < 1024)%nat -> ew (havoc E 1024 (map (getr regs2) CLOB)) n = ew E n)
  by (intros n Hn; apply ew_havoc_old; exact Hn).
psrr_branch_pi RUNP BR HS2.
- (* strcmp returned 0: the verb is the row's name *)
  rewrite branch_eq_U, Ua0 in Hc.
  assert (H0 : getr regs2 10 = w64 0).
  { apply Z.eqb_eq in Hc. unfold U in Hc. cbn [sv_denot] in Hc. rewrite unsigned_lit_small in Hc by lia.
    apply bv_eq. rewrite Hc. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  apply HQ2 in H0.
  paj_run_to_sh RUNTO HS2 HJ2 S25_LED.
  { s25_awr. }
  s25_unchanged (@pa_segs _ cmd_listing PI) UN3 HFr. clear HF HFr HG.
  match goal with |- context [with_vm_backing (m_vm_lazy md2) ?mt md2] =>
    set (mdv3 := with_vm_backing (m_vm_lazy md2) mt md2) in * end.
  clearbody mdv3.
  match goal with H : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => set (ms3 := m) in * end.
  assert (K : vr_kept W memc (ms_mem ms3) (vr_s1 e)).
  { apply (vr_kept_trans W memc (ms_mem ms) (ms_mem ms3) (vr_s1 e) K1).
    apply (vr_kept_trans W (ms_mem ms) mem2 (ms_mem ms3) (vr_s1 e) K2).
    intros a Ha _. exact (UN3 a Ha (fun x => x)). }
  prreg HS2 (Z_to_bv 5 2) T2. prreg HS2 (Z_to_bv 5 3) T3. prreg HS2 (Z_to_bv 5 4) T4.
  prreg HS2 (Z_to_bv 5 8) T8. prreg HS2 (Z_to_bv 5 9) T9.
  prreg HS2 (Z_to_bv 5 19) T19. prreg HS2 (Z_to_bv 5 21) T21.
  prreg HS2 (Z_to_bv 5 26) T26. prreg HS2 (Z_to_bv 5 27) T27.
  assert (Hrv3 : vr_rv (ms_regs ms3) (vr_base B e ++
    [(19, SHADOW_OFF + (0xa5c48 + 16 * Z.of_nat j) / 8); (21, vr_ntok (e_D e)); (26, hd 0 (v :: tps));
     (27, 0xa5c40 + 16 * Z.of_nat j)])).
  { rewrite Esh. unfold vr_rv, vr_base. cbn [app hd].
    repeat apply Forall_cons; try apply Forall_nil; cbn beta; cbn [fst snd].
    - rewrite T2, (EE 2%nat (Z_to_bv 5 2) eq_refl). exact R2.
    - rewrite T3, (EE 3%nat (Z_to_bv 5 3) eq_refl). exact R3.
    - rewrite T4, (EE 4%nat (Z_to_bv 5 4) eq_refl). exact R4.
    - rewrite T8, (EE 8%nat (Z_to_bv 5 8) eq_refl). exact R8.
    - rewrite T9, (EE 9%nat (Z_to_bv 5 9) eq_refl). exact R9.
    - rewrite T19, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19. f_equal. lia.
    - rewrite T21, (EE 21%nat (Z_to_bv 5 21) eq_refl). exact R21.
    - rewrite T26, (EE 26%nat (Z_to_bv 5 26) eq_refl). exact R26.
    - rewrite T27, X0. reflexivity. }
  pmkst HS2. apply SRr_ret. left.
  exists j, nmj, led, pos, F, q, c, (v :: tps), lyc, Sc, (ms_regs ms3), (ms_mem ms3), mdv3, k, nm.
  split; [apply s25_cfg; unfold S25_LED, AF_verbs_receive; lia|].
  split; [exact Hnth|].
  split.
  { rewrite Et, (vr_route_tail w args Hroute'). unfold VRR.route_tail. fold vr_tbl.
    rewrite (vr_ledger_hit w j nmj led Hlf Hnth H0). reflexivity. }
  split; [exact Htoks|].
  exact (s25_mk e pos F q c (v :: tps) lyc Sc W regsc memc mdc k nm _ _ _ _ _ Hent Hcore Hline Hcopy HJ2 K Hrv3).
- (* strcmp returned a nonzero value: the next row *)
  rewrite branch_eq_U, Ua0 in Hc.
  assert (H0 : w <> nmj).
  { intros Heq. apply HQ2 in Heq. rewrite Heq in Hc. vm_compute in Hc. discriminate Hc. }
  pose proof (vr_ledger_miss w j nmj led Hlf Hnth H0) as Hlf1. clear Hc.
  paj_run_sh RUNP HS2 HJ2.
  { s25_awr. }
  s25_unchanged (@pa_segs _ cmd_listing PI) UN3 HFr. clear HF HFr HG.
  match goal with |- context [with_vm_backing (m_vm_lazy md2) ?mt md2] =>
    set (mdv3 := with_vm_backing (m_vm_lazy md2) mt md2) in * end.
  clearbody mdv3.
  match goal with H : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => set (ms3 := m) in * end.
  assert (K3 : vr_kept W memc (ms_mem ms3) (vr_s1 e)).
  { apply (vr_kept_trans W memc (ms_mem ms) (ms_mem ms3) (vr_s1 e) K1).
    apply (vr_kept_trans W (ms_mem ms) mem2 (ms_mem ms3) (vr_s1 e) K2).
    intros a Ha _. exact (UN3 a Ha (fun x => x)). }
  assert (E18 : ew (havoc E 1024 (map (getr regs2) CLOB)) 18 = Z_to_bv 64 (16 * Z.of_nat j))
    by (rewrite EO, (EE 18%nat (Z_to_bv 5 18) eq_refl), R18 by lia; reflexivity).
  assert (E22 : ew (havoc E 1024 (map (getr regs2) CLOB)) 22 = Z_to_bv 64 160)
    by (rewrite EO, (EE 22%nat (Z_to_bv 5 22) eq_refl), R22 by lia; reflexivity).
  psrr_branch_pi RUNP BR HS2.
  + (* s2 + 16 <> 160: back to the header *)
    rewrite branch_ne_U, (U_atom_off _ 18 (16 * Z.of_nat j) 16 E18 ltac:(lia) ltac:(lia)),
      (U_atom _ 22 160 E22 ltac:(lia)) in Hc.
    assert (Hj9 : (j < 9)%nat) by (destruct (Z.eqb_spec (16 * Z.of_nat j + 16) 160) as [Hq | Hq]; [discriminate Hc | lia]).
    paj_run_to_sh RUNTO HS2 HJ2 S25_H.
    { s25_awr. }
    s25_unchanged (@pa_segs _ cmd_listing PI) UN4 HFr. clear HF HFr HG.
    match goal with |- context [with_vm_backing (m_vm_lazy mdv3) ?mt mdv3] =>
      set (mdv4 := with_vm_backing (m_vm_lazy mdv3) mt mdv3) in * end.
    clearbody mdv4.
    match goal with H : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => set (ms4 := m) in * end.
    assert (K : vr_kept W memc (ms_mem ms4) (vr_s1 e)).
    { apply (vr_kept_trans W memc (ms_mem ms3) (ms_mem ms4) (vr_s1 e) K3).
      intros a Ha _. exact (UN4 a Ha (fun x => x)). }
    prreg HS2 (Z_to_bv 5 2) T2. prreg HS2 (Z_to_bv 5 3) T3. prreg HS2 (Z_to_bv 5 4) T4.
    prreg HS2 (Z_to_bv 5 8) T8. prreg HS2 (Z_to_bv 5 9) T9.
    prreg HS2 (Z_to_bv 5 18) T18. prreg HS2 (Z_to_bv 5 19) T19. prreg HS2 (Z_to_bv 5 20) T20.
    prreg HS2 (Z_to_bv 5 21) T21. prreg HS2 (Z_to_bv 5 22) T22. prreg HS2 (Z_to_bv 5 23) T23.
    prreg HS2 (Z_to_bv 5 25) T25. prreg HS2 (Z_to_bv 5 26) T26.
    assert (Hrv4 : vr_rv (ms_regs ms4) (vr_base B e ++ vr_rl_scan e (hd 0 (v :: tps)) (S j))).
    { unfold vr_rv, vr_base, vr_rl_scan. cbn [app hd].
      repeat apply Forall_cons; try apply Forall_nil; cbn beta; cbn [fst snd].
      - rewrite T2, (EE 2%nat (Z_to_bv 5 2) eq_refl). exact R2.
      - rewrite T3, (EE 3%nat (Z_to_bv 5 3) eq_refl). exact R3.
      - rewrite T4, (EE 4%nat (Z_to_bv 5 4) eq_refl). exact R4.
      - rewrite T8, (EE 8%nat (Z_to_bv 5 8) eq_refl). exact R8.
      - rewrite T9, (EE 9%nat (Z_to_bv 5 9) eq_refl). exact R9.
      - rewrite T18, (EE 18%nat (Z_to_bv 5 18) eq_refl), R18. unfold w64.
        rewrite unsigned_lit_small by lia. f_equal. lia.
      - rewrite T19, (EE 19%nat (Z_to_bv 5 19) eq_refl), R19. unfold w64.
        rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). f_equal. lia.
      - rewrite T20, (EE 20%nat (Z_to_bv 5 20) eq_refl). exact R20.
      - rewrite T21, (EE 21%nat (Z_to_bv 5 21) eq_refl). exact R21.
      - rewrite T22, (EE 22%nat (Z_to_bv 5 22) eq_refl). exact R22.
      - rewrite T23, (EE 23%nat (Z_to_bv 5 23) eq_refl), R23. unfold w64.
        rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). f_equal. lia.
      - rewrite T25, (EE 25%nat (Z_to_bv 5 25) eq_refl). exact R25.
      - rewrite T26, (EE 26%nat (Z_to_bv 5 26) eq_refl). exact R26. }
    pmkst HS2. apply SRr_ret. right. right. split; [exact Hj9|].
    exists r, pos, F, q, c, (v :: tps), lyc, Sc, (ms_regs ms4), (ms_mem ms4), mdv4, k, nm.
    split; [apply s25_cfg; unfold S25_H, AF_verbs_receive; lia|].
    split; [exact Htail|]. split; [exact Hroute|]. split; [exact Htoks|].
    split; [rewrite Et; exact Hlf1|].
    exact (s25_mk e pos F q c (v :: tps) lyc Sc W regsc memc mdc k nm _ _ _ _ _ Hent Hcore Hline Hcopy HJ2 K Hrv4).
  + (* s2 + 16 = 160: the last row missed *)
    rewrite branch_ne_U, (U_atom_off _ 18 (16 * Z.of_nat j) 16 E18 ltac:(lia) ltac:(lia)),
      (U_atom _ 22 160 E22 ltac:(lia)) in Hc.
    assert (Hj9 : j = 9%nat) by (destruct (Z.eqb_spec (16 * Z.of_nat j + 16) 160) as [Hq | Hq]; [lia | discriminate Hc]).
    paj_run_to_sh RUNTO HS2 HJ2 S25_X.
    { s25_awr. }
    s25_unchanged (@pa_segs _ cmd_listing PI) UN4 HFr. clear HF HFr HG.
    match goal with |- context [with_vm_backing (m_vm_lazy mdv3) ?mt mdv3] =>
      set (mdv4 := with_vm_backing (m_vm_lazy mdv3) mt mdv3) in * end.
    clearbody mdv4.
    match goal with H : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => set (ms4 := m) in * end.
    assert (K : vr_kept W memc (ms_mem ms4) (vr_s1 e)).
    { apply (vr_kept_trans W memc (ms_mem ms3) (ms_mem ms4) (vr_s1 e) K3).
      intros a Ha _. exact (UN4 a Ha (fun x => x)). }
    prreg HS2 (Z_to_bv 5 2) T2. prreg HS2 (Z_to_bv 5 3) T3. prreg HS2 (Z_to_bv 5 4) T4.
    prreg HS2 (Z_to_bv 5 8) T8. prreg HS2 (Z_to_bv 5 9) T9.
    prreg HS2 (Z_to_bv 5 21) T21. prreg HS2 (Z_to_bv 5 25) T25. prreg HS2 (Z_to_bv 5 26) T26.
    assert (Hrv4 : vr_rv (ms_regs ms4) (vr_base B e ++
      [(21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, hd 0 (v :: tps))])).
    { unfold vr_rv, vr_base. cbn [app hd].
      repeat apply Forall_cons; try apply Forall_nil; cbn beta; cbn [fst snd].
      - rewrite T2, (EE 2%nat (Z_to_bv 5 2) eq_refl). exact R2.
      - rewrite T3, (EE 3%nat (Z_to_bv 5 3) eq_refl). exact R3.
      - rewrite T4, (EE 4%nat (Z_to_bv 5 4) eq_refl). exact R4.
      - rewrite T8, (EE 8%nat (Z_to_bv 5 8) eq_refl). exact R8.
      - rewrite T9, (EE 9%nat (Z_to_bv 5 9) eq_refl). exact R9.
      - rewrite T21, (EE 21%nat (Z_to_bv 5 21) eq_refl). exact R21.
      - rewrite T25, (EE 25%nat (Z_to_bv 5 25) eq_refl). exact R25.
      - rewrite T26, (EE 26%nat (Z_to_bv 5 26) eq_refl). exact R26. }
    pmkst HS2. apply SRr_ret. right. left.
    exists pos, F, q, c, (v :: tps), lyc, Sc, (ms_regs ms4), (ms_mem ms4), mdv4, k, nm.
    split; [apply s25_cfg; unfold S25_X, AF_verbs_receive; lia|].
    split.
    { rewrite Et. subst j. pose proof (vr_ledger_all w Hlf1) as Hnone. split; [exact Hnone|].
      rewrite (vr_route_tail w args Hroute'). unfold VRR.route_tail. fold vr_tbl. rewrite Hnone. reflexivity. }
    exact (s25_mk e pos F q c (v :: tps) lyc Sc W regsc memc mdc k nm _ _ _ _ _ Hent Hcore Hline Hcopy HJ2 K Hrv4).
Qed.


Lemma s25_loop : forall n e j W cf, vr_ent B MT e -> (j + n = 9)%nat -> vr_hdr e j W cf ->
SRr SEGS W cf (vr_or (vr_led B MT) (vr_s27in B MT) e).
Proof.
induction n as [|n IH]; intros e j W cf Hent Hjn Hh.
- eapply SRr_bind; [exact (s25_pass e j W cf Hent ltac:(lia) Hh)|].
  intros W' cf' _ [H | [H | [Hj _]]]; [apply SRr_ret; left; exact H | apply SRr_ret; right; exact H | lia].
- eapply SRr_bind; [exact (s25_pass e j W cf Hent ltac:(lia) Hh)|].
  intros W' cf' _ [H | [H | [_ H]]]; [apply SRr_ret; left; exact H | apply SRr_ret; right; exact H|].
  exact (IH e (S j) W' cf' Hent ltac:(lia) H).
Qed.

Lemma s25_entry : forall e W cf, vr_ent B MT e -> vr_rt_tail B MT e W cf -> SRr SEGS W cf (vr_hdr e 0).
Proof.
intros e W cf Hent (r & Htail & Hrt).
destruct Hrt as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Htoks & Hcore & Hline & Hcopy).
assert (Hpc : vr_route_pc r = 0x8d7e0) by (destruct r; try discriminate Htail; reflexivity).
rewrite Hpc.
pose proof Hent as Hent'. unfold vr_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & HVOBJ & _).
pose proof Hcore as (HJ & Hkk & Hmeter & Hnm & Hframe & Hrv & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof ASAN_CEIL_range as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
unfold vr_rl_rt in Hrv. cbv zeta in Hrv.
assert (Hrows : forall rr vv, In (rr, vv) (vr_base B e ++ [(18, q); (19, SHADOW_OFF); (21, vr_ntok (e_D e)); (22, F);
  (23, vr_ntok (e_D e) - 1); (25, vr_ntok (e_D e)); (26, hd 0 tp); (27, shadow_addr F + 4)]) ->
  getr regsc (Z_to_bv 5 rr) = w64 vv) by (intros rr vv Hin; exact (vr_rv_get _ _ rr vv Hrv Hin)).
assert (R2 := Hrows 2 (vr_s1 e) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R3 := Hrows 3 (as_gp B) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R4 := Hrows 4 (as_tp B) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R8 := Hrows 8 (vr_sp0 e) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R9 := Hrows 9 (vr_s1 e) ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R19 := Hrows 19 _ ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R21 := Hrows 21 _ ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R25 := Hrows 25 _ ltac:(unfold vr_base; cbn [app In]; tauto)).
assert (R26 := Hrows 26 _ ltac:(unfold vr_base; cbn [app In]; tauto)).
rewrite <- (s25_cfg regsc memc mdc 0x8d7e0 S25_E ltac:(unfold S25_E, AF_verbs_receive; lia)).
remember (Eimg (Ereg regsc [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regsc rr).
{ intros n rr Hn. rewrite HE. apply ew_Eimg_Ereg_nat. exact Hn. }
assert (HS : st_ok_pi SEGS VAL E s25_ss0 (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + S25_E)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold s25_ss0. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
paj_run_to_sh RUNTO HS HJ S25_H.
{ s25_awr. }
s25_unchanged (@pa_segs _ cmd_listing PI) UN HFr. clear HF HFr HG.
match goal with |- context [with_vm_backing (m_vm_lazy mdc) ?mt mdc] =>
  set (mdv := with_vm_backing (m_vm_lazy mdc) mt mdc) in * end.
clearbody mdv.
match goal with H : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => set (ms1 := m) in * end.
assert (K : vr_kept W memc (ms_mem ms1) (vr_s1 e)) by (intros a Ha _; exact (UN a Ha (fun x => x))).
assert (X358 : ew E 358 = Z_to_bv 64 0xa5c40).
{ rewrite (img_env_atomP E 358 HEI ltac:(unfold A_TEXT, A_LIM; lia)).
  change 358%nat with (A_OBJ 117). rewrite (HVOBJ 117%nat ltac:(vm_compute; lia)). reflexivity. }
assert (X19 : ew E 19 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl); exact R19).
prreg HS (Z_to_bv 5 2) T2. prreg HS (Z_to_bv 5 3) T3. prreg HS (Z_to_bv 5 4) T4.
prreg HS (Z_to_bv 5 8) T8. prreg HS (Z_to_bv 5 9) T9.
prreg HS (Z_to_bv 5 18) T18. prreg HS (Z_to_bv 5 19) T19. prreg HS (Z_to_bv 5 20) T20.
prreg HS (Z_to_bv 5 21) T21. prreg HS (Z_to_bv 5 22) T22. prreg HS (Z_to_bv 5 23) T23.
prreg HS (Z_to_bv 5 25) T25. prreg HS (Z_to_bv 5 26) T26.
assert (Hrv1 : vr_rv (ms_regs ms1) (vr_base B e ++ vr_rl_scan e (hd 0 tp) 0)).
{ unfold vr_rv, vr_base, vr_rl_scan. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn beta; cbn [fst snd].
  - rewrite T2, (EE 2%nat (Z_to_bv 5 2) eq_refl). exact R2.
  - rewrite T3, (EE 3%nat (Z_to_bv 5 3) eq_refl). exact R3.
  - rewrite T4, (EE 4%nat (Z_to_bv 5 4) eq_refl). exact R4.
  - rewrite T8, (EE 8%nat (Z_to_bv 5 8) eq_refl). exact R8.
  - rewrite T9, (EE 9%nat (Z_to_bv 5 9) eq_refl). exact R9.
  - rewrite T18. reflexivity.
  - rewrite T19, X19, X358. unfold w64, SHADOW_OFF. apply bv_eq. vm_compute. reflexivity.
  - rewrite T20, X358. reflexivity.
  - rewrite T21, (EE 21%nat (Z_to_bv 5 21) eq_refl). exact R21.
  - rewrite T22. reflexivity.
  - rewrite T23, X19, X358. unfold w64, SHADOW_OFF. apply bv_eq. vm_compute. reflexivity.
  - rewrite T25, (EE 25%nat (Z_to_bv 5 25) eq_refl). exact R25.
  - rewrite T26, (EE 26%nat (Z_to_bv 5 26) eq_refl). exact R26. }
pmkst HS. apply SRr_ret.
exists r, pos, F, q, c, tp, lyc, Sc, (ms_regs ms1), (ms_mem ms1), mdv, k, nm.
split; [apply s25_cfg; unfold S25_H, AF_verbs_receive; lia|].
split; [exact Htail|]. split; [exact Hroute|]. split; [exact Htoks|].
split; [reflexivity|].
exact (s25_mk e pos F q c tp lyc Sc W regsc memc mdc k nm _ _ _ _ _ Hent Hcore Hline Hcopy HJ K Hrv1).
Qed.

Lemma vr_s25 : vr_s25_stmt B MT.
Proof.
intros e W cf Hent Ht.
eapply SRr_bind; [exact (s25_entry e W cf Hent Ht)|].
intros W' cf' _ Hh. exact (s25_loop 9 e 0 W' cf' Hent eq_refl Hh).
Qed.

End e.

End f.
End d.
