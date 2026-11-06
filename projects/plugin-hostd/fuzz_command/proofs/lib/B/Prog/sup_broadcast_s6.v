(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the last segment of the sup_broadcast walk on fuzz_command.asan-ubsan: the run
   from arg_line's return 0x8b518 to the tail jump `j answer` (0x8b538: a1 := the shape 0x21d20 by PHi/PAddHi of
   A_OBJ 42, a2 := 1, a0 := s1, the frame restored, sp += 32) over the verified symbolic executor; the state at
   answer's entry (sbb_at_ans: answer's premises, the entry's frame chain by achain_kept, PASS4-REFIT.md section B);
   the tail call through PaFx.v's cl_callS_pgF with answer_c.v's contract at the walk's FP state; and the post of
   the statement from answer's post and the block history (sup_broadcast_s2.v sbb_post_blocks). The shape of
   a Theorem Labs lane's A walk (lib/A/Prog/sup_broadcast_s3.v at a5a5ff08765) and of the worked re-fit
   lib/A/Prog/sup_remove_all_refit_s3.v (the F tail call). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts PaNoChain PaCallPg PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas RecBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_canonical_c hand_back_c mix_call_c record_c arg_line_c answer_c sup_broadcast_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_broadcast_s1 sup_broadcast_s2 sup_broadcast_s3 sup_broadcast_s4 sup_broadcast_s5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at arg_line's return: every register its own atom, the three saved words of the frame as the
   extra atoms 32 (ra), 33 (s0), 34 (s1); the frame is only read *)
Definition sbb_t_stack : YP09.region := YP09.mkRegion (Some 2%nat) 8 32 0 0
[YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 32 0))].
Definition ss_sbb_t : sstate := mkSS SBB_RET_AL sr_atoms [sbb_t_stack] None (mkFacts [] [] []).
Definition sbb_t_extra (ra s0 s1 : Z) : list word := map (Z_to_bv 64) [ra; s0; s1].

(* membership in the filter of answer's footprint (the filter these files see; A: sup_broadcast_s3.v sb_in_filter) *)
Lemma sbb_in_filter : forall (l : list (Z * Z)) (old : Z) x, In x (filter (fun pn => fst pn =? old) l) -> In x l.
Proof.
induction l as [|y l IH]; intros old x H; [exact H|].
cbn in H. repeat match type of H with context [if ?c then _ else _] => destruct c end;
first [destruct H as [H | H]; [left; exact H | right; exact (IH old x H)] | right; exact (IH old x H)].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the tail segment's symbolic entry *)
Lemma sbb_t_entry : forall (W : world SEGS) regsA memA (ra s0 s1 : Z),
0 <= ra < 2 ^ 64 -> 0 <= s0 < 2 ^ 64 -> 0 <= s1 < 2 ^ 64 -> 0 <= spZ regsA -> spZ regsA + 32 <= 2 ^ 64 ->
aval_mem (rdW W memA) (spZ regsA + 24) 8 ra -> aval_mem (rdW W memA) (spZ regsA + 16) 8 s0 ->
aval_mem (rdW W memA) (spZ regsA + 8) 8 s1 ->
st_ok_pi SEGS VAL (Eimg (Ereg regsA (sbb_t_extra ra s0 s1))) ss_sbb_t
(restrict (w_H W) (mkst regsA (Z_to_bv 64 (BASE + SBB_RET_AL)) memA (seg_rom SEGS))) /\
sh_ok SEGS sbb_Bx sbb_SH (Eimg (Ereg regsA (sbb_t_extra ra s0 s1))) (mrestrict (w_H W) memA).
Proof.
intros W regsA memA ra s0 s1 Hra Hs0 Hs1 Hsp0 Hsp Vra Vs0 Vs1.
set (E := Eimg (Ereg regsA (sbb_t_extra ra s0 s1))).
assert (E2 : ew E 2 = getr regsA 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsA _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsA) by (rewrite E2; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 ra) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 s0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 s1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 2)).
split.
- rewrite restrict_mkst_fx. unfold ss_sbb_t. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, sbb_t_stack.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    [ apply (chunk_ok_val SEGS E _ (spZ regsA) 8 8 (SOff 34 0) s1);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact (val_mem_view _ _ _ _ _ _ Vs1)]
    | apply (chunk_ok_val SEGS E _ (spZ regsA) 16 8 (SOff 33 0) s0);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact (val_mem_view _ _ _ _ _ _ Vs0)]
    | apply (chunk_ok_val SEGS E _ (spZ regsA) 24 8 (SOff 32 0) ra);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact (val_mem_view _ _ _ _ _ _ Vra)] ].
  + cbn. repeat split.
  + cbn. repeat split.
- unfold sh_ok, sbb_SH. apply Forall_nil.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Let RUN := paj_run B LAWS.

(* the call target of answer *)
Lemma sbb_sig_answer : SIGMA CS_answer = BASE + AF_answer.
Proof. rewrite (SIGP CS_answer); [reflexivity | cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right])]. Qed.

(* the run 0x8b518 .. `j answer`: the facts at answer's entry go to the continuation *)
Lemma sbb_reach_tail : forall ly S W regs mem md O lyA SA (WA : world SEGS) regsA memA mdA k c
  (Qk : world SEGS -> config -> Prop),
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] lyA SA WA memA mdA k ->
spZ regsA = spZ regs - 32 -> 32 <= spZ regs -> getr regsA 9 = w64 c ->
sbb_frame regs (rdW WA memA) ->
(forall regsT memT mdT,
 ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] lyA SA WA memT mdT k ->
 getr regsT 1 = getr regs 1 -> getr regsT 2 = getr regs 2 -> getr regsT 8 = getr regs 8 -> getr regsT 9 = getr regs 9 ->
 getr regsT 10 = w64 c -> getr regsT 11 = w64 SBB_SHAPE_ADDR -> getr regsT 12 = Z_to_bv 64 1 ->
 (forall r, In r [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr regsT (Z_to_bv 5 r) = getr regsA (Z_to_bv 5 r)) ->
 (forall a, rdW WA memT a = rdW WA memA a) ->
 SRr SEGS WA (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA CS_answer)) memT (seg_rom SEGS)) mdT) Qk) ->
SRr SEGS WA (cfg_at SEGS (BASE + SBB_RET_AL) regsA memA mdA) Qk.
Proof.
intros ly S W regs mem md O lyA SA WA regsA memA mdA k c Qk HJ Hsp Hsp32 H9 (Vra & Vs0 & Vs1) HK.
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr2. change (bv_modulus 64) with (2 ^ 64) in Hr2.
destruct (sbb_t_entry WA regsA memA (raZ regs) (s0Z regs) (bv_unsigned (getr regs 9))) as [HS SHOK];
[apply bv_unsigned_in_range | apply bv_unsigned_in_range | apply bv_unsigned_in_range | unfold spZ in *; lia | unfold spZ in *; lia
| rewrite Hsp; replace (spZ regs - 32 + 24) with (spZ regs - 8) by lia; exact Vra
| rewrite Hsp; replace (spZ regs - 32 + 16) with (spZ regs - 16) by lia; exact Vs0
| rewrite Hsp; replace (spZ regs - 32 + 8) with (spZ regs - 24) by lia; exact Vs1 |].
remember (sbb_t_extra (raZ regs) (s0Z regs) (bv_unsigned (getr regs 9))) as X eqn:HX.
remember (Eimg (Ereg regsA X)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsA X) E) by (rewrite HE; split; [intros n Hn'; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsA r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = getr regs 1).
{ subst E X. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regsA _ 0). apply Z_to_bv_bv_unsigned. }
assert (E33 : ew E 33 = getr regs 8).
{ subst E X. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regsA _ 1). apply Z_to_bv_bv_unsigned. }
assert (E34 : ew E 34 = getr regs 9).
{ subst E X. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regsA _ 2). apply Z_to_bv_bv_unsigned. }
assert (E283 : ew E 283 = Z_to_bv 64 SBB_SHAPE_ADDR).
{ pose proof (HEI 283%nat ltac:(unfold A_TEXT, A_LIM; lia)) as H.
  change (VAL 283%nat) with (VAL (A_OBJ 42)) in H. rewrite (VOBJS 42%nat ltac:(vm_compute; lia)) in H.
  apply bv_eq. rewrite H. unfold SBB_SHAPE_ADDR. rewrite unsigned_lit_small by lia. vm_compute. reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 32) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
clear HE.
unfold cfg_at. change (w64 (BASE + SBB_RET_AL)) with (Z_to_bv 64 (BASE + SBB_RET_AL)).
paj_run_tok RUN HS HJ SHOK sbb_Bspan.
{ awr_ok_tac. }
pmkst HS.
lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv := with_vm_backing x y z) in *; clearbody mdv end.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> rdW WA (ms_mem ms) a = rdW WA memA a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) E _ (w_H WA) memA (ms_mem ms) (fun _ => False) HFr).
  - intros b wlo whi a' Hin Hr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]). destruct Hin.
  - exact Ha.
  - intros []. }
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
pose proof (regs_kept_of_st_ok SEGS E _ _ regsA X (map (Z_to_bv 5) [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) HS HAE
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
clear HF HFr HG.
apply HK.
- exact HJ.
- rewrite T1. exact E32.
- rewrite T2, Usp. replace (spZ regs - 32 + 32) with (spZ regs) by lia. apply Z_to_bv_bv_unsigned.
- rewrite T8. exact E33.
- rewrite T9. exact E34.
- rewrite T10, (EE 9%nat 9%bv eq_refl). exact H9.
- rewrite T11. exact E283.
- rewrite T12. reflexivity.
- intros r Hr. apply KR. apply in_map. exact Hr.
- exact (sbb_keep_all (w_H WA) memA (ms_mem ms) KEEP).
Qed.

(* the shape "resp 0" as answer's astr_argA takes it: its bytes are read-only, unowned and not the errno cell
   (cif_ro_unowned, CmdRecRo's cmd_ro_in_img), the record's shadow checks of 0x21d20 .. 0x21d26 and its end hold by
   computation (A: lib/A/Prog/sup_remove_all_refit_s3.v s3_shape_arg at 0x21ce0) *)
Lemma sbb_shape_arg : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O SBB_SHAPE_ADDR (Some REC_MOD_HOST_SHAPE) /\ fits REC_MOD_HOST_SHAPE.
Proof.
intros ly S W mem md O HAR HROD. split; [|apply Z.leb_le; vm_compute; reflexivity].
assert (HOBJ : forall i, 0 <= i < 7 -> Exists (in_zr (0x21d20 + i)) cmd_ro_objs).
{ intros i Hi. apply Exists_exists. exists (0x21d20, 7). split; [|unfold in_zr; cbn [fst snd]; lia].
  unfold cmd_ro_objs. repeat (first [left; reflexivity | right]). }
assert (HLIT : abytes_atR (rdW W mem) 0x21d20 RO_lit_21d20).
{ apply (cmd_ro_obj_bytes SEGS B LAWS HB IMG ly S W mem md (0x21d20, RO_lit_21d20) HAR HROD).
  unfold cmd_ro_list. repeat (first [left; reflexivity | right]). }
assert (HSTR : astr_atR (rdW W mem) 0x21d20 REC_MOD_HOST_SHAPE).
{ split.
  - first
    [ replace (REC_MOD_HOST_SHAPE ++ [Z_to_bv 8 0]) with RO_lit_21d20 by (vm_compute; reflexivity); exact HLIT
    | intros i Hi; change (length (REC_MOD_HOST_SHAPE ++ [Z_to_bv 8 0])) with 7%nat in Hi;
      rewrite (HLIT i ltac:(change (length RO_lit_21d20) with 7%nat; exact Hi)); f_equal;
      do 7 (destruct i as [|i]; [vm_compute; reflexivity|]); lia ].
  - intros Hin. apply (in_map (fun b : byte => bv_unsigned b)) in Hin. vm_compute in Hin.
    repeat (destruct Hin as [Hin | Hin]; [discriminate Hin|]). exact Hin. }
assert (HEND : In (0x21d20 + Z.of_nat (length REC_MOD_HOST_SHAPE)) cmd_ro_ends).
{ change (0x21d20 + Z.of_nat (length REC_MOD_HOST_SHAPE)) with 0x21d26. unfold cmd_ro_ends.
  repeat (first [left; reflexivity | right]). }
unfold astr_argA, SBB_SHAPE_ADDR. cbv beta iota zeta.
change (Z.of_nat (length REC_MOD_HOST_SHAPE) + 1) with 7.
split; [lia|]. split; [exact HSTR|]. split; [unfold LMAX; lia|]. right.
split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | exact HEND]]].
intros i Hi. split.
- exact (cmd_ro_in_to _ (cmd_ro_in_img SEGS B LAWS HB IMG) _ (HOBJ i Hi)).
- exact (cmd_ro_in_to _ (cif_ro_unowned _ _ IMG) _ (HOBJ i Hi)).
Qed.

(* answer's entry state *)
Lemma sbb_at_ans_of : forall ly S W regs mem md ch pl line R O ly1 S1 F O1 lyA SA (WA : world SEGS) regsA memA mdA p
  regsT memT mdT,
sbb_ent B MT ly S W regs mem md ch pl line R O ->
sbb_ret_al B MT ly S W regs mem md line R O ly1 S1 F O1 lyA SA WA regsA memA mdA p ->
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] lyA SA WA memT mdT (EV_RECORD R + EV_ARG_LINE) ->
getr regsT 1 = getr regs 1 -> getr regsT 2 = getr regs 2 -> getr regsT 8 = getr regs 8 -> getr regsT 9 = getr regs 9 ->
getr regsT 10 = w64 (rec_slot R) -> getr regsT 11 = w64 SBB_SHAPE_ADDR -> getr regsT 12 = Z_to_bv 64 1 ->
(forall r, In r [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr regsT (Z_to_bv 5 r) = getr regsA (Z_to_bv 5 r)) ->
(forall a, rdW WA memT a = rdW WA memA a) ->
exists old, sbb_at_ans B MT ly S W regs mem md ch line R O ly1 S1 F O1 lyA SA WA regsT memT mdT p old.
Proof.
intros ly S W regs mem md ch pl line R O ly1 S1 F O1 lyA SA WA regsA memA mdA p regsT memT mdT HENT HRET HJT
  T1 T2 T8 T9 T10 T11 T12 TR KEEP.
destruct HENT as (HPRE & HFRM & Hfr8 & HROD & H10 & Hpl & HBLK0 & HAP & HSTR0 & HLEN & HREC & Hev & Hlive & HMOK).
destruct HRET as (HJA & HspA & A9 & ACS & VF & HRODA & HRECA & HO1 & HP0 & HFO & HO1b & HPm & HAp & Hp4096 & HbbA & HBB & HMLE).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJT as (HART & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres1 & Hstatic & F5 & HQT1).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
destruct (sbb_stk) as (WSTK & WREC & WAL & WANS).
assert (HOb : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hpn; exact (proj2 (sbb_rep_pos B _ _ _ _ _ pn HREC Hpn))).
pose proof (sbb_rec_slot_ok B ly S _ R O HREC) as Hsl. pose proof (sb_slot_range _ Hsl) as Hslr.
set (k := Z.of_nat (length line) + 1) in *.
assert (HRECT : rec_repA B lyA SA (rdW WA memT) (rec_record R REC_BROADCAST [canon line]) ((p, k) :: O1))
  by (apply (rec_repA_kept B lyA SA (rdW WA memA) lyA SA (rdW WA memT) _ _ HRECA);
      [intros pn Hpn; exact (proj2 (sbb_rep_pos B _ _ _ _ _ pn HRECA Hpn)) | intros a _; apply KEEP]).
assert (HRODT : arodata_okP SEGS RLO RHI B (rdW WA memT)) by (intros a H1 H2 H3; rewrite KEEP; exact (HRODA a H1 H2 H3)).
destruct (sbb_rep_old B lyA SA _ _ _ HRECT) as (old & Hold & Hold').
exists old.
assert (E3 : getr regsT 3 = getr regs 3).
{ etransitivity; [exact (TR 3 ltac:(cbn; tauto))|]. exact (ACS 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (E4 : getr regsT 4 = getr regs 4).
{ etransitivity; [exact (TR 4 ltac:(cbn; tauto))|]. exact (ACS 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (Es0 : s0Z regsT = s0Z regs) by (unfold s0Z; rewrite T8; reflexivity).
split; [exact HJT|].
split; [unfold spZ; rewrite T2; lia|].
split; [exact T1|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
  destruct (Z.eq_dec r 2) as [-> | N2]; [exact T2|].
  destruct (Z.eq_dec r 8) as [-> | N8]; [exact T8|].
  destruct (Z.eq_dec r 9) as [-> | N9]; [exact T9|].
  rewrite (TR r ltac:(cbn [In]; lia)). apply ACS; [unfold acallee_saved; lia | exact N2 | exact N8 | exact N9]. }
split.
{ rewrite Z.add_0_r, Es0. apply (achain_ly_top ly lyA); [exact Etop|].
  apply (achain_kept ly (rdW W mem) (rdW WA memT) (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
  intros a Ha. apply F1; [lia | lia |]. intros Hf. pose proof (sb_FP_low B LAWS ly S W mem md O a HAR HOb Hf). lia. }
split; [rewrite Hfrs; exact Hfr8|].
split; [exact HRODT|].
split; [exact (cmd_ro_ok_of_aro SEGS B LAWS HB IMG lyA SA WA memT mdT HART HRODT)|].
split; [exact T10|]. split; [unfold A_G_REC, A_REC_SPILL in Hslr; lia|].
split; [exact T11|]. split; [unfold SBB_SHAPE_ADDR; lia|].
split; [rewrite T12; vm_compute; reflexivity|].
split; [exact HRECT|]. split; [exact Hold|].
split.
{ destruct Hold' as [-> | (ko & Hko)]; [lia|].
  destruct (sbb_blk B LAWS lyA SA WA memT mdT old ko HART (proj2 (sbb_rep_pos B _ _ _ _ _ _ HRECT Hko))) as (H4 & Hc & _ & Hr1 & _).
  lia. }
split; [exact Hold'|].
split; [intros _; exact (sbb_shape_arg lyA SA WA memT mdT _ HART HRODT)|].
split.
{ intros _ _. destruct (rec_slot_entry R REC_BROADCAST [canon line]) as [H1 | (H1 & H2)]; [left; exact H1 | right; split; [exact H1 | exact H2]]. }
split; [unfold EV_SUP_BROADCAST in Hev; lia|].
split.
{ unfold LIVE_SUP_BROADCAST in Hlive. lia. }
split.
{ apply (mok_station MT S SA (XM_SUP_BROADCAST MT R line (snd (sup_broadcast_m R line))) (XM_RECORD MT R + XM_ARG_LINE MT line) _
    MTL HMOK HMLE).
  - unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
    pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length (snd (sup_broadcast_m R line))) + 1))
      ltac:(unfold LIVE_XMALLOC; lia)). lia.
  - unfold XM_SUP_BROADCAST. lia. }
split; [exact HO1|]. split; [exact HP0|]. split; [exact HFO|]. split; [exact HO1b|].
split; [exact HPm|]. split; [exact HAp|]. split; [exact HbbA|]. split; [exact HBB | exact HMLE].
Qed.

(* every byte of answer's footprint is a byte the walk may write: g_rec's answer and state words (program statics in
   the walk's footprint), and the old answer's block (a block of O, or arg_line's new block) *)
Lemma sbb_ans_fp_ok : forall ly S (W : world SEGS) mem md O ly1 S1 F O1 lyT ST p k old,
AR SEGS B ly S W mem md ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) ->
Permutation (ablocks B ly S) (ablocks B ly1 S1 ++ F) -> (forall pn, In pn F -> In pn O) ->
(forall pn, In pn O1 -> In pn (ablocks B ly1 S1)) ->
Permutation (ablocks B lyT ST) ((p, k) :: ablocks B ly1 S1) ->
Forall (fun qk => iv_apart p k (fst qk) (snd qk)) (ablocks B ly1 S1) -> 0 < k ->
forall a, inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
  ablocks_fp (filter (fun pn => fst pn =? old) ((p, k) :: O1))) a ->
(inFP (sb_FP O) a /\ ((exists b n, In (b, n) (ablocks B lyT ST) /\ b <= a < b + req_size n) \/
 (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a))) \/ in_tmp_block (ablocks B ly S) (ablocks B lyT ST) a.
Proof.
intros ly S W mem md O ly1 S1 F O1 lyT ST p k old HAR HO1 HP0 HFO HO1b HPm HAp Hk a Ha.
assert (HPG : forall a, A_G_REC <= a < A_G_REC + 960 -> inFP cmd_PG a)
  by (intros a0 Ha0; exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; lia]).
assert (Hb1T : forall pn, In pn (ablocks B ly1 S1) -> In pn (ablocks B lyT ST))
  by (intros pn H; apply (Permutation_in _ (Permutation_sym HPm)); right; exact H).
apply inFP_cons in Ha as [Ha | Ha]; [|apply inFP_cons in Ha as [Ha | Ha]].
- left. split.
  + unfold sb_FP. apply inFP_cons; right. apply inFP_cons; left. unfold A_G_REC, OFF_CALLS, OFF_ANSWER in *. lia.
  + right. apply (sbb_pg_prog B HB IMG). apply HPG. unfold A_G_REC, OFF_ANSWER in *. lia.
- left. split.
  + unfold sb_FP. apply inFP_cons; right. apply inFP_cons; right. apply inFP_cons; left. exact Ha.
  + right. apply (sbb_pg_prog B HB IMG). apply HPG. unfold A_G_REC, OFF_STATE in *. lia.
- destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hin & Hr). apply sbb_in_filter in Hin.
  assert (HinFP : In (b, m) O -> inFP (sb_FP O) a).
  { intros HO. unfold sb_FP. do 4 (apply inFP_cons; right). replace a with (b + (a - b)) by lia.
    apply (inFP_ablocks_fp O b m (a - b)); [exact HO | lia]. }
  destruct Hin as [Epk | HinM].
  + injection Epk as <- <-.
    assert (HpT : In (p, k) (ablocks B lyT ST)) by (apply (Permutation_in _ (Permutation_sym HPm)); left; reflexivity).
    destruct (in_dec sbb_zz_eq_dec (p, k) (ablocks B ly S)) as [H0 | H0].
    * left. split; [|left; exists p, k; split; [exact HpT | exact Hr]].
      apply HinFP. apply (Permutation_in _ HP0) in H0. apply in_app_or in H0 as [H0 | H0]; [|exact (HFO _ H0)].
      exfalso. pose proof (proj1 (Forall_forall _ _) HAp _ H0) as Hd. unfold iv_apart in Hd. cbn [fst snd] in Hd. lia.
    * right. exists p, k. split; [exact HpT|]. split; [exact H0 | exact Hr].
  + left. split; [exact (HinFP (proj1 (proj1 (HO1 _) HinM)))|].
    left. exists b, m. split; [exact (Hb1T _ (HO1b _ HinM)) | exact Hr].
Qed.

(* the tail call of answer: cl_callS_pgF with answer's contract at the walk's FP state *)
Lemma sbb_call_answer : forall ly S W regs mem md ch pl line R O ly1 S1 F O1 lyT ST (WT : world SEGS) regsT memT mdT p old,
sbb_ent B MT ly S W regs mem md ch pl line R O ->
sbb_at_ans B MT ly S W regs mem md ch line R O ly1 S1 F O1 lyT ST WT regsT memT mdT p old ->
SRr SEGS WT (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA CS_answer)) memT (seg_rom SEGS)) mdT)
(sbb_post_ans B MT ly S W regs mem md line R O lyT ST regsT ((p, Z.of_nat (length line) + 1) :: O1) old).
Proof.
intros ly S W regs mem md ch pl line R O ly1 S1 F O1 lyT ST WT regsT memT mdT p old HENT HAT.
destruct HENT as (HPRE & HFRM & Hfr8 & HROD & H10 & Hpl & HBLK0 & HAP & HSTR0 & HLEN & HREC & Hev & Hlive & HMOK).
destruct HAT as (HJT & HspT & T1 & HPT & HchT & HfrT & HRODT & HROKT & T10 & Hc64 & T11 & Hsh64 & T12 & HRECT & Hold
  & Hold64 & Hold' & HARG & HSLOT & HEVT & HLIVET & HMOKT & HO1 & HP0 & HFO & HO1b & HPm & HAp & HbbT & HBB & HMLE).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (sbb_stk) as (WSTK & WREC & WAL & WANS).
assert (E3 : getr regsT 3 = getr regs 3) by exact (HPT 3 ltac:(unfold acallee_saved; lia)).
assert (E4 : getr regsT 4 = getr regs 4) by exact (HPT 4 ltac:(unfold acallee_saved; lia)).
unfold sbb_post_ans.
eapply SRr_mono.
{ refine (cl_callS_pgF B LAWS WT regsT memT (Z_to_bv 64 (SIGMA CS_answer)) SUP_BROADCAST_STK (spZ regs) (sb_FP O)
    ly S W mem md [] lyT ST mdT (EV_RECORD R + EV_ARG_LINE) ANSWER_STK
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
      ablocks_fp (filter (fun pn => fst pn =? old) ((p, Z.of_nat (length line) + 1) :: O1)))
    EV_ANSWER 0 (getr regsT 1) ch (sbb_ans_Q B MT lyT ST line R ((p, Z.of_nat (length line) + 1) :: O1) old)
    HJT HspT ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite E3; exact Hgp) ltac:(rewrite E4; exact Htp)
    eq_refl ltac:(rewrite T1; exact Hra) ltac:(rewrite T1; exact Hra4) HchT _ _).
  - intros HPRE2. rewrite sbb_sig_answer.
    exact (TANSWER fx lyT ST WT regsT memT mdT ch (rec_slot R) SBB_SHAPE_ADDR old (REC_BROADCAST, [canon line])
      REC_MOD_HOST_SHAPE true (rec_record R REC_BROADCAST [canon line]) ((p, Z.of_nat (length line) + 1) :: O1)
      HPRE2 HFRM HfrT HRODT HROKT T10 Hc64 T11 Hsh64 T12 HRECT Hold Hold64 HARG HSLOT HEVT HLIVET HMOKT).
  - exact (sbb_ans_fp_ok ly S W mem md O ly1 S1 F O1 lyT ST p (Z.of_nat (length line) + 1) old HAR HO1 HP0 HFO HO1b HPm HAp
      ltac:(lia)). }
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & [G1 G2] & Hc & HJ2 & _ & HP2 & HQ).
exists fx1, ly2, S2, regs2, mem2, md2.
split; [rewrite Hc, T1; reflexivity|]. split; [exact G1|]. split; [exact G2|].
split; [exact HJ2|]. split; [exact HP2 | exact HQ].
Qed.

(* the statement's post from answer's post and the walk's history *)
Lemma sbb_final : forall ly S W regs mem md ch pl line R O ly1 S1 F O1 lyT ST (WT : world SEGS) regsT memT mdT p old
  (W2 : world SEGS) c2,
sbb_ent B MT ly S W regs mem md ch pl line R O ->
sbb_at_ans B MT ly S W regs mem md ch line R O ly1 S1 F O1 lyT ST WT regsT memT mdT p old ->
sbb_post_ans B MT ly S W regs mem md line R O lyT ST regsT ((p, Z.of_nat (length line) + 1) :: O1) old W2 c2 ->
apost_baseF SEGS B SUP_BROADCAST_STK (sb_FP O) regs ly S W mem md (EV_SUP_BROADCAST R) (sb_post B MT ly S R line O) W2 c2.
Proof.
intros ly S W regs mem md ch pl line R O ly1 S1 F O1 lyT ST WT regsT memT mdT p old W2 c2 HENT HAT
  (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hc & G1 & G2 & HJ2 & HP2 & HQ).
destruct HENT as (HPRE & HFRM & Hfr8 & HROD & H10 & Hpl & HBLK0 & HAP & HSTR0 & HLEN & HREC & Hev & Hlive & HMOK).
destruct HAT as (HJT & HspT & T1 & HPT & HchT & HfrT & HRODT & HROKT & T10 & Hc64 & T11 & Hsh64 & T12 & HRECT & Hold
  & Hold64 & Hold' & HARG & HSLOT & HEVT & HLIVET & HMOKT & HO1 & HP0 & HFO & HO1b & HPm & HAp & HbbT & HBB & HMLE).
pose proof HPRE as (HAR & _).
pose proof (proj1 HJT) as HART. pose proof (proj1 HJ2) as HAR2.
destruct HQ as (p1 & p2 & O' & Q10 & Q4096 & Qne & Qfr & QBL & QREP & QO & QSTR & QBB & QMLE).
exists fx1, ly2, S2, regs2, mem2, md2.
split; [exact Hc|]. split; [exact G1|]. split; [exact G2|].
split; [unfold EV_SUP_BROADCAST; exact HJ2|].
split; [exact (aregs_preserved_trans _ _ _ HPT HP2)|].
unfold sb_post. cbv zeta.
exists (fst (sup_broadcast_m R line)), O', p2.
split; [apply surjective_pairing|].
assert (Hnz : forall pn, In pn (ablocks B ly S) -> fst pn <> 0).
{ intros [b m] Hb. destruct (sbb_blk B LAWS ly S W mem md b m HAR Hb) as (H4 & _). cbn [fst]. lia. }
destruct (sbb_post_blocks (ablocks B ly S) (ablocks B ly1 S1) (ablocks B lyT ST) (ablocks B ly2 S2) O F O1 O' p
  (Z.of_nat (length line) + 1) p1 p2 (Z.of_nat (length (snd (sup_broadcast_m R line))) + 1) old
  (sb_blocks_nodup B LAWS ly S W mem md HAR) (sb_blocks_nodup B LAWS lyT ST WT memT mdT HART)
  (sb_blocks_nodup B LAWS ly2 S2 W2 mem2 md2 HAR2)
  (fun pn Hpn => proj2 (sbb_rep_pos B _ _ _ _ _ pn HREC Hpn)) HP0 HFO HO1 HO1b HPm HAp ltac:(lia)
  QBL Qfr Qne QO Hold' Hnz (fun pn Hpn => proj2 (sbb_rep_pos B _ _ _ _ _ pn QREP Hpn))) as (P1 & P2 & P3 & P4 & P5 & P6).
split; [exact Q10|]. split; [exact Q4096|]. split; [exact QREP|].
split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
split; [exact P6|]. split; [exact QSTR|].
split; [unfold LIVE_SUP_BROADCAST; lia|].
unfold XM_SUP_BROADCAST. exact (mle_station MT S ST S2 _ _ MTL HMLE QMLE).
Qed.

End e.
End f.
End d.
