(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment D of check_words' ASan walk (plugin-hostd/fuzz_command, 0x87c90 .. 0x87d64), in the form of lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (seeds, symbolic runs, calls). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_sD.v, with its numbers changed; 406 of its 575 lines of code are new or changed and 1491 lines of the source are left out. *)
(* check_words' ASan walk (plugin-hostd/fuzz_command, entry 0x878b4): segment R, `seg_R : ST_REL B MT` -- from REL
   (0x87db8, after the call loop) to check_words' post: free(line), the side-stack frame's release, the return. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's hypotheses (check_words_c.v:88-104), word for word *)
Hypothesis HJOINED : tjoined_spec B MT.
Hypothesis HADD : tcheck_words_add_spec B MT.
Hypothesis HCHAIN : tcheck_words_chain_spec B MT.
Hypothesis HPIN : tcwps_spec B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis ASMALLOC0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASTRSPN : astrspn_realizes SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8.
Hypothesis ASTRCSPN : astrcspn_realizes SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis ASTRCMP : astrcmp_realizes SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis AATOI : aatoi_realizes SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8.
Hypothesis ASNPRINTF : asnprintf_realizes SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
(* the per-binary walk facts *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis RRO : RRO_P.
Hypothesis SIGP : cmd_sig_prog.
(* the record facts of lib/A/Prog/CmdRecFacts.v, carried until that file lands *)
Hypothesis cmd_rec_cells : cmd_rec_cells_P B.
Hypothesis cmd_rom_view_on : cmd_rom_view_on_P B.
Hypothesis cmd_heap_tail_vis : cmd_heap_tail_vis_P B.
Hypothesis cmd_prog_unowned : cmd_prog_unowned_P B.
Hypothesis ZSH_cw : CW_ZSH_P B.
Hypothesis cw_ro_unowned : cw_ro_unowned_P B.
Hypothesis cmd_tail_vis : cmd_tail_vis_P B.
Hypothesis cmd_got_rec : cmd_got_rec_P B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* ---------------------------------------------------------------------------------------------------------- *)
(* Segment R (0x87db8 .. 0x87e74; listing 0x18d4 .. 0x1990): `free(line)`, the release of the class-0 side-stack
   frame F (number's shadow 0xf8 0xf8, the magic 0x45e0360e at F, the frame's 8 shadow bytes 0xf5, the flag byte
   at [F + 56] := 0), the restore of the 13 saved registers and `ret`.
   Three steps: (1) a token run from REL (one load of line from s1 + 144) stops at the free call; (2) the call
   through afree04_sub, whose frame chain comes from the entry's astack_pres (chain_pre_any); (3) from a fresh
   state at the return address (every base and chunk value an atom), one plain run under aj_flag_store_pi to the
   `ret`, then paj_ret_at and check_words' post. *)
Definition RBx : sv := SOff 23 0.
Definition RBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition CW_PC_AF : Z := 0x18dc.   (* 0x87dc0, the free call's return address *)
(* the seed at REL: atoms 9 sp1, 23 SB; extra atom 32 line *)
Definition r_line : YP09.region := YP09.mkRegion (Some 9%nat) 144 152 0 0 [YP09.mkChunk 144 (CVal 8 (SOff 32 0))].
Definition r1_facts : facts := mkFacts [ (9%nat, mkAF (2^46) (2^47) 5); (23%nat, mkAF SB SB 0) ] [] [].
Definition ssR1 : sstate := mkSS CW_PC_REL sr_atoms [r_line] None r1_facts.
(* the seed after the free: atoms 8 sp0, 9 sp1; extra atoms 32 F, 33 SB + F / 8, 34 the flag's address FL,
   35 .. 47 the values of the 13 saved registers (cw_saved) *)
Definition r_flag : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 1 [].
Definition r_fsh : YP09.region := fshadow_region 33 0 0 8 [].
Definition r_frame : YP09.region := fframe_region 32 34 0 [].
Definition r_scr : YP09.region :=
YP09.mkRegion (Some 9%nat) 16 40 0 0
[YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 32 (CVal 8 (SOff 32 0))].
Definition r_sav : YP09.region :=
YP09.mkRegion (Some 8%nat) (-104) 0 0 0
(map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (35 + j) 0))) (seq 0 13)).
Definition r2_regions : smem := [r_flag; r_fsh; r_frame; r_scr; r_sav].
Definition r2_facts : facts := mkFacts [ (8%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF (2^46) (2^47) 5); (32%nat, HPTR 5) ] [] [].
Definition ssR2 : sstate := mkSS CW_PC_AF sr_atoms r2_regions None r2_facts.
Definition r2_extra (regs0 : bvmap 5 word) (F FL : Z) : list word :=
[Z_to_bv 64 F; Z_to_bv 64 (CW_SB + F / 8); Z_to_bv 64 FL] ++ map (fun r => getr regs0 (Z_to_bv 5 r)) cw_saved.

(* ---------------------------------------------------------------------------------------------------------- *)
(* small facts *)
Lemma cwr_den0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma cwr_val_of_aval : forall H (m : word -> option byte) a n v,
aval_mem (aview SEGS H m) a n v -> val_mem SEGS (mrestrict H m) a n v.
Proof.
intros H m a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Hb; [|discriminate Hv].
cbn in Hv. injection Hv as Hv. rewrite <- (Z_to_bv_bv_unsigned _ b) at 1. do 2 f_equal. exact Hv.
Qed.
Lemma cwr_aval_kept : forall (rd rd' : reader) a n v,
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Hk H k Hk'. rewrite (Hk k Hk'). exact (H k Hk'). Qed.
Lemma cwr_bytes_kept : forall (rd rd' : reader) a l,
(forall i, (i < length l)%nat -> rd' (a + Z.of_nat i) = rd (a + Z.of_nat i)) -> abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l Hk H i Hi. rewrite (Hk i Hi). exact (H i Hi). Qed.
Lemma cwr_str_kept : forall (rd rd' : reader) p s n,
(forall i, 0 <= i < n -> rd' (p + i) = rd (p + i)) -> Z.of_nat (length s) + 1 <= n ->
astr_atR rd p s -> astr_atR rd' p s.
Proof.
intros rd rd' p s n Hk Hn [Hb Hnul]. split; [|exact Hnul].
apply (cwr_bytes_kept rd); [|exact Hb]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
(* the memory a run over regions without a write window leaves *)
Lemma cwr_keep_ro : forall E rs H (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a Hf Hro Ha. apply aview_eq_of. apply Hf. intros (r & Hin & Hr).
rewrite Forall_forall in Hro. specialize (Hro r Hin). rewrite unsigned_lit_small in Hr by lia. lia.
Qed.
Lemma cwr_sv_nth : forall (regs0 : bvmap 5 word) j r, nth_error cw_saved j = Some r ->
nth j (map (fun r => getr regs0 (Z_to_bv 5 r)) cw_saved) (Z_to_bv 64 0) = getr regs0 (Z_to_bv 5 r).
Proof. intros regs0 j r H. apply nth_error_nth. rewrite nth_error_map, H. reflexivity. Qed.
Lemma cwr_saved_lt : forall j r, nth_error cw_saved j = Some r -> (j < 13)%nat.
Proof. intros j r H. assert (Hl : (j < length cw_saved)%nat) by (apply nth_error_Some; rewrite H; discriminate). exact Hl. Qed.
Lemma cwr_JN_pos : forall e, 1 <= cw_JN e.
Proof.
intros e. unfold cw_JN. assert (H : forall ws, 0 <= PJn.join_need ws).
{ induction ws as [|w ws IH]; unfold PJn.join_need in *; cbn [fold_right] in *; lia. }
specialize (H (e_ws e)). lia.
Qed.
Lemma cwr_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. pose proof (Z.div_mod a 32 ltac:(lia)) as Ea. rewrite Ha, Z.add_0_r in Ea.
pose proof (Z.div_mod b 16 ltac:(lia)) as Eb. rewrite Hb, Z.add_0_r in Eb. rewrite Ea, Eb.
replace (32 * (a / 32) - 16 * (b / 16)) with ((2 * (a / 32) - b / 16) * 16) by lia. apply Z_mod_mult.
Qed.
Ltac cwr_rreg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
end.

(* ---------------------------------------------------------------------------------------------------------- *)
Ltac cwr_saved_reg HS E2SV :=
lazymatch goal with |- getr _ (Z_to_bv 5 ?r0) = _ =>
  let X := fresh "X" in cwr_rreg HS (Z_to_bv 5 r0) X; rewrite X, cwr_den0 end;
first [ exact (E2SV 1%nat _ eq_refl) | exact (E2SV 2%nat _ eq_refl) | exact (E2SV 3%nat _ eq_refl)
| exact (E2SV 4%nat _ eq_refl) | exact (E2SV 5%nat _ eq_refl) | exact (E2SV 6%nat _ eq_refl)
| exact (E2SV 7%nat _ eq_refl) | exact (E2SV 8%nat _ eq_refl) | exact (E2SV 9%nat _ eq_refl)
| exact (E2SV 10%nat _ eq_refl) | exact (E2SV 11%nat _ eq_refl) | exact (E2SV 12%nat _ eq_refl) ].

(* the recorder's state at a later state of the call: g_rec and record.spill are program statics no runtime entry
   owns (cmd_prog_unowned), so the journal's image clause keeps their bytes; the blocks the recorder points to are
   live at both ends, so the journal's block clause keeps theirs *)
Lemma cwr_call_kept : forall bl bl' (rd rd' : reader) a c P,
(forall x, a <= x < a + 56 -> rd' x = rd x) ->
(forall p n, In (p, n) bl -> In (p, n) bl' /\ forall i, 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
acall_at bl rd a c P -> acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P HA HB (H1 & H2 & H3 & H4 & H5 & H6 & H7).
unfold acall_at. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (cwr_aval_kept rd); [intros k Hk; apply HA; unfold CALL_OFF_FN; lia | exact H4]|].
split; [apply (cwr_aval_kept rd); [intros k Hk; apply HA; unfold CALL_OFF_NARGS; lia | exact H5]|].
split; [exact H6|].
intros k s [p n] Hs Hpn. destruct (H7 k s (p, n) Hs Hpn) as (V & Hnz & Hin & Hsz & Hstr). cbn [fst snd] in *.
assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
destruct (HB p n Hin) as [Hin' Hb].
split; [apply (cwr_aval_kept rd); [intros j Hj; apply HA; unfold CALL_OFF_ARGS; lia | exact V]|].
split; [exact Hnz|]. split; [exact Hin'|]. split; [exact Hsz|].
apply (cwr_str_kept rd rd' p s n); [exact Hb | lia | exact Hstr].
Qed.
Lemma cwr_rep_kept : forall bl bl' (rd rd' : reader) R Q,
(forall x, A_G_REC <= x < A_G_REC + 960 -> rd' x = rd x) ->
(forall x, A_REC_SPILL <= x < A_REC_SPILL + 56 -> rd' x = rd x) ->
(forall p n, In (p, n) bl -> In (p, n) bl' /\ forall i, 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
arep_at bl rd A_G_REC A_REC_SPILL R Q -> arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q HG HS HB (Ha1 & Ha2 & Hap & (Hl & HlQ & Hnc & Hcalls & Hsp & Hspl) & Hans & Hrep & Hsc & Hown).
assert (AV : forall off n v, 0 <= off -> off + Z.of_nat n <= 960 -> aval_mem rd (A_G_REC + off) n v ->
  aval_mem rd' (A_G_REC + off) n v).
{ intros off n v H0 H1 Hv. apply (cwr_aval_kept rd); [intros k Hk; apply HG; lia | exact Hv]. }
unfold arep_at. split; [exact Ha1|]. split; [exact Ha2|]. split; [exact Hap|].
split.
{ unfold ag1_calls. split; [exact Hl|]. split; [exact HlQ|].
  split; [apply AV; [unfold OFF_NCALLS; lia | unfold OFF_NCALLS; lia | exact Hnc]|].
  split; [|split; [apply (cwr_call_kept bl bl' rd rd' A_REC_SPILL); [exact HS | exact HB | exact Hsp] | exact Hspl]].
  intros i c P Hc HP. destruct (Hcalls i c P Hc HP) as [Hca Hf]. split; [|exact Hf].
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  apply (cwr_call_kept bl bl' rd rd'); [| exact HB | exact Hca]. intros x Hx. apply HG. unfold OFF_CALLS, CALL_SIZE in *. lia. }
split.
{ unfold aanswer_at in *. destruct (r_answer R) as [x|], (l_answer Q) as [[p n]|]; cbv iota beta in Hans |- *;
  try contradiction.
  - destruct Hans as (V & Hnz & Hin & Hsz & Hstr & Hx). cbn [fst snd] in *. destruct (HB p n Hin) as [Hin' Hb].
    split; [apply AV; [unfold OFF_ANSWER; lia | unfold OFF_ANSWER; lia | exact V]|].
    split; [exact Hnz|]. split; [exact Hin'|]. split; [exact Hsz|]. split; [|exact Hx].
    apply (cwr_str_kept rd rd' p x n); [exact Hb | lia | exact Hstr].
  - apply AV; [unfold OFF_ANSWER; lia | unfold OFF_ANSWER; lia | exact Hans]. }
split.
{ unfold areply_at in *. destruct (r_reply R) as [x|], (l_reply Q) as [[p n]|]; cbv iota beta in Hrep |- *;
  try contradiction.
  - destruct Hrep as (V1 & V2 & Hnz & Hne & Hin & Hsz & Hb0 & Hx). cbn [fst snd] in *. destruct (HB p n Hin) as [Hin' Hb].
    split; [apply AV; [unfold OFF_REPLY; lia | unfold OFF_REPLY; lia | exact V1]|].
    split; [apply AV; [unfold OFF_REPLY_SIZE; lia | unfold OFF_REPLY_SIZE; lia | exact V2]|].
    split; [exact Hnz|]. split; [exact Hne|]. split; [exact Hin'|]. split; [exact Hsz|]. split; [|exact Hx].
    apply (cwr_bytes_kept rd rd' p x); [intros i Hi; apply Hb; lia | exact Hb0].
  - destruct Hrep as [V1 V2].
    split; [apply AV; [unfold OFF_REPLY; lia | unfold OFF_REPLY; lia | exact V1]|].
    apply AV; [unfold OFF_REPLY_SIZE; lia | unfold OFF_REPLY_SIZE; lia | exact V2]. }
split; [|exact Hown].
destruct Hsc as (V1 & V2 & V3 & V4 & V5 & Rr). unfold ag1_scalars.
split; [apply AV; [unfold OFF_REFUSE; lia | unfold OFF_REFUSE; lia | exact V1]|].
split; [apply AV; [unfold OFF_CODE; lia | unfold OFF_CODE; lia | exact V2]|].
split; [apply AV; [unfold OFF_NREPLIES; lia | unfold OFF_NREPLIES; lia | exact V3]|].
split; [apply AV; [unfold OFF_STATE; lia | unfold OFF_STATE; lia | exact V4]|].
split; [apply AV; [unfold OFF_HOST; lia | unfold OFF_HOST; lia | exact V5]|].
exact Rr.
Qed.
Lemma cwr_rec_journal : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k R O,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
(forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly' S')) ->
rec_repA B ly S (rdW W mem) R O -> rec_repA B ly' S' (rdW W' mem') R O.
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k R O HJ Hbl (Q & HQ & HO).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & F3 & _).
assert (PG : forall a, inFP cmd_PG a -> rdW W' mem' a = rdW W mem a).
{ intros a Ha. destruct (cmd_prog_unowned a Ha) as (Himg & Hno & Hne).
  apply F3; [exact Himg | exact Hno | exact Hne |].
  apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | apply inFP_nil]. }
exists Q. split; [|exact HO].
apply (cwr_rep_kept (ablocks B ly S) _ (rdW W mem)); [| | | exact HQ].
- intros x Hx. apply PG. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity | cbn [fst snd]; lia].
- intros x Hx. apply PG. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity | cbn [fst snd]; lia].
- intros p n Hin. split; [exact (Hbl _ Hin)|]. intros i Hi.
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
  apply (F2 p n i); [exact Hin | exact (Hbl _ Hin) | lia | apply inFP_nil].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the seeds *)
Lemma cwr_seed1 : forall (W : world SEGS) (regsc : bvmap 5 word) memc sp1 line,
getr regsc 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> getr regsc 23 = w64 CW_SB ->
0 <= line < 2 ^ 64 -> aval_mem (rdW W memc) (sp1 + 144) 8 line ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc [Z_to_bv 64 line])) ssR1
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + CW_PC_REL)) memc (seg_rom SEGS))) /\
sh_ok SEGS RBx [] (Eimg (Ereg regsc [Z_to_bv 64 line])) (mrestrict (w_H W) memc).
Proof.
intros W regsc memc sp1 line H9 Hsp Hsp32 H23 Hl V144.
assert (E9 : ew (Eimg (Ereg regsc [Z_to_bv 64 line])) 9 = Z_to_bv 64 sp1)
  by (rewrite (ew_Eimg_Ereg_nat regsc _ 9 9%bv eq_refl); exact H9).
assert (E23 : ew (Eimg (Ereg regsc [Z_to_bv 64 line])) 23 = Z_to_bv 64 CW_SB)
  by (rewrite (ew_Eimg_Ereg_nat regsc _ 23 23%bv eq_refl); exact H23).
assert (E32 : ew (Eimg (Ereg regsc [Z_to_bv 64 line])) 32 = Z_to_bv 64 line)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
split.
- unfold ssR1. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold r_line, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ sp1 144 8 (SOff 32 0) line); [rewrite cwr_den0, E32; reflexivity | lia | lia |].
    exact (cwr_val_of_aval _ _ _ _ _ V144).
  + apply pairwise_disjoint_of_extents. cbn. tauto.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok r1_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E23, !unsigned_lit_small by (unfold CW_SB; lia). change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
    unfold SB, CW_SB. repeat split; first [exact I | lia].
- unfold sh_ok. apply Forall_nil.
Qed.

(* the extra atoms of the seed after the free *)
Lemma cwr_E2 : forall (regs2 regs0 : bvmap 5 word) F FL,
ew (Eimg (Ereg regs2 (r2_extra regs0 F FL))) 32 = Z_to_bv 64 F /\
ew (Eimg (Ereg regs2 (r2_extra regs0 F FL))) 33 = Z_to_bv 64 (CW_SB + F / 8) /\
ew (Eimg (Ereg regs2 (r2_extra regs0 F FL))) 34 = Z_to_bv 64 FL /\
(forall j r, nth_error cw_saved j = Some r ->
 ew (Eimg (Ereg regs2 (r2_extra regs0 F FL))) (35 + j) = getr regs0 (Z_to_bv 5 r)).
Proof.
intros regs2 regs0 F FL.
assert (EX : forall j, (32 + j < A_TEXT)%nat ->
  ew (Eimg (Ereg regs2 (r2_extra regs0 F FL))) (32 + j) = nth j (r2_extra regs0 F FL) (Z_to_bv 64 0))
  by (intros j Hj; rewrite Eimg_low by exact Hj; apply ew_Ereg_extra).
split; [exact (EX 0%nat ltac:(unfold A_TEXT; lia))|].
split; [exact (EX 1%nat ltac:(unfold A_TEXT; lia))|].
split; [exact (EX 2%nat ltac:(unfold A_TEXT; lia))|].
intros j r Hj. pose proof (cwr_saved_lt j r Hj) as Hj13.
replace (35 + j)%nat with (32 + (3 + j))%nat by lia. rewrite EX by (unfold A_TEXT; lia).
unfold r2_extra. cbn [Nat.add nth app]. exact (cwr_sv_nth regs0 j r Hj).
Qed.

Lemma cwr_seed2 : forall (W : world SEGS) (regs2 regs0 : bvmap 5 word) mem2 sp0 sp1 F FL,
getr regs2 8 = w64 sp0 -> getr regs2 9 = w64 sp1 ->
2 ^ 46 <= sp1 -> alloc_ceiling <= sp1 -> sp1 + 288 <= sp0 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 -> sp1 mod 32 = 0 ->
4096 <= F -> F + 64 <= alloc_ceiling -> F mod 32 = 0 -> in_app F 64 ->
4096 <= FL -> FL < alloc_ceiling -> ~ (F <= FL < F + 64) -> ~ (CW_SB + F / 8 <= FL < CW_SB + F / 8 + 8) ->
aval_mem (rdW W mem2) (sp1 + 16) 8 (CW_SB + F / 8) -> aval_mem (rdW W mem2) (sp1 + 24) 8 F ->
aval_mem (rdW W mem2) (sp1 + 32) 8 F -> aval_mem (rdW W mem2) (F + 56) 8 FL ->
cw_saves (rdW W mem2) sp0 regs0 ->
(forall a, F <= a < F + 64 -> apresent (w_H W) mem2 a) ->
(forall i, 0 <= i < 8 -> apresent (w_H W) mem2 (CW_SB + F / 8 + i)) ->
apresent (w_H W) mem2 FL ->
st_ok_pi SEGS VAL (Eimg (Ereg regs2 (r2_extra regs0 F FL))) ssR2
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + CW_PC_AF)) mem2 (seg_rom SEGS))).
Proof.
intros W regs2 regs0 mem2 sp0 sp1 F FL H8 H9 Hsp1 Hsp1c Hsp01 Hsp0 Hsp0al Hsp1al HF4096 HFceil HFal HFapp
  HFL4096 HFLceil HFLF HFLS V16 V24 V32 VFL VSV PF PS PFL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
assert (Hfb8 : fs_frame_bytes 0 / 8 = 8) by reflexivity.
set (E := Eimg (Ereg regs2 (r2_extra regs0 F FL))).
assert (E8 : ew E 8 = Z_to_bv 64 sp0) by (subst E; rewrite (ew_Eimg_Ereg_nat regs2 _ 8 8%bv eq_refl); exact H8).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (subst E; rewrite (ew_Eimg_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
destruct (cwr_E2 regs2 regs0 F FL) as (E32 & E33 & E34 & ESV). fold E in E32, E33, E34, ESV.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (BF8 : 0 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (Z.mul_div_le F 8 ltac:(lia)) as BF8b.
unfold CW_SB in *.
rewrite restrict_mkst_fx. unfold ssR2. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold r2_regions, r_flag, r_fsh, fshadow_region, r_frame, fframe_region, r_scr, r_sav. rewrite Hfb8, Hfb.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks app].
  + rewrite (VB 34%nat FL E34) by lia. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact PFL | apply Forall_nil].
  + rewrite (VB 33%nat (2147450880 + F / 8) E33) by lia. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply PS; lia | apply Forall_nil].
  + rewrite (VB 32%nat F E32) by lia. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply PF; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ F (64 - 8) 8 (SOff 34 0) FL); [rewrite cwr_den0, E34; reflexivity | lia | lia |].
    replace (F + (64 - 8)) with (F + 56) by lia. exact (cwr_val_of_aval _ _ _ _ _ VFL).
  + rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp1 16 8 (SOff 33 0) (2147450880 + F / 8)); [rewrite cwr_den0, E33; reflexivity | lia | lia |].
      exact (cwr_val_of_aval _ _ _ _ _ V16).
    * apply (chunk_ok_val SEGS E _ sp1 24 8 (SOff 32 0) F); [rewrite cwr_den0, E32; reflexivity | lia | lia |].
      exact (cwr_val_of_aval _ _ _ _ _ V24).
    * apply (chunk_ok_val SEGS E _ sp1 32 8 (SOff 32 0) F); [rewrite cwr_den0, E32; reflexivity | lia | lia |].
      exact (cwr_val_of_aval _ _ _ _ _ V32).
  + rewrite (VB 8%nat sp0 E8) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
    destruct (nth_error cw_saved j) as [r|] eqn:Hr; [| exfalso; apply nth_error_None in Hr; cbn in Hr; lia].
    apply (chunk_ok_val SEGS E _ sp0 (-8 - 8 * Z.of_nat j) 8 (SOff (35 + j) 0) (bv_unsigned (getr regs0 (Z_to_bv 5 r)))).
    * rewrite cwr_den0, (ESV j r Hr). symmetry. apply Z_to_bv_bv_unsigned.
    * pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 r))) as RR. change (bv_modulus 64) with (2 ^ 64) in RR.
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * lia.
    * replace (sp0 + (-8 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia.
      exact (cwr_val_of_aval _ _ _ _ _ (VSV j r Hr)).
- apply pairwise_disjoint_of_extents.
  unfold r2_regions, r_flag, r_fsh, fshadow_region, r_frame, fframe_region, r_scr, r_sav, extent_of_region.
  rewrite Hfb8, Hfb. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 34%nat FL E34) by lia. rewrite (VB 33%nat (2147450880 + F / 8) E33) by lia.
  rewrite (VB 32%nat F E32) by lia. rewrite (VB 9%nat sp1 E9) by lia. rewrite (VB 8%nat sp0 E8) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | [HH1 HH2]]);
  repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok r2_facts]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
  rewrite E8, E9, E32, !unsigned_lit_small by lia. change (2 ^ 5) with 32. change (2 ^ 4) with 16.
  repeat split; first [exact I | lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.

Lemma seg_R : ST_REL B MT.
Proof.
unfold ST_REL. intros e lyc Sc Wc regsc memc mdc pos sp1 line Hent HI.
pose proof Hent as Hent'. unfold cw_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREC & _ & _ & _ & Hev & _ & MOK & _).
pose proof HPRE as (HAR0 & Hra & Hra40 & Hgp & Htp & Hstk & _ & Hch0 & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & HtopA & HtopB).
destruct HI as (HC & HL & H144).
unfold cw_core in HC. cbv zeta in HC.
destruct HC as (HJ & Hsp & Hsp32 & Hsprng & H3 & H4 & H8 & H9 & H23 & Hsaves & V16 & V24 & V32 & _ & VFL & _ & _).
destruct HL as (HPerm & H4096 & Hapart & _ & MLE).
unfold cw_sp0 in *.
set (sp0 := spZ (e_regs e)) in *.
set (F := frame_addr (e_ly e) 0 pos) in *.
set (FL := flag_addr (e_ly e) 0 pos) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : CHECK_WORDS_STK = 16800) by reflexivity.
assert (HAS : ASTACK = 16384) by reflexivity.
assert (EVJ : EV_JOINED = 1) by reflexivity.
assert (EVC : EV_CHECK_WORDS = 2) by reflexivity.
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
assert (Hfb8 : fs_frame_bytes 0 / 8 = 8) by reflexivity.
pose proof pa_B_ok as HBo.
assert (Hsp1c : alloc_ceiling <= sp1) by lia.
(* the journal at REL: the layout keeps the frame's address, the frame and the block line *)
pose proof HJ as (HAR1 & Hly1 & _ & _ & _ & Hfrs1 & Hnev1 & _).
assert (EF1 : ly_F lyc = ly_F (e_ly e)) by (destruct Hly1 as (_ & _ & _ & _ & _ & EF & _); exact EF).
assert (EFA1 : frame_addr lyc 0 pos = F) by (unfold F, frame_addr; rewrite EF1; reflexivity).
assert (Hin1 : In (0, pos) (frames Sc)) by (rewrite Hfrs1; left; reflexivity).
assert (Hinl : In (line, cw_JN e) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HPerm)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 Hinl) as (_ & _ & Hlceil & _ & _ & _ & HlJN).
pose proof (cwr_JN_pos e) as HJN1.
pose proof (req_size_pos (cw_JN e) ltac:(lia)) as [Hrq1 Hrq2].
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ 0 pos HAR1 Hinl Hin1) as Hdis.
unfold zdisjoint in Hdis. cbn [fst snd] in Hdis. rewrite EFA1, Hfb in Hdis.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR1 Hin1) as (HF4096 & HFceil & HFapp).
rewrite EFA1 in HF4096. rewrite EFA1, Hfb in HFceil, HFapp.
assert (BF8 : 0 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
(* step 1: the token run from REL to the free call *)
destruct (cwr_seed1 Wc regsc memc sp1 line H9 ltac:(lia) Hsp32 H23 ltac:(lia) H144) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc [Z_to_bv 64 line]))) by apply Eimg_env.
assert (E1_32 : ew (Eimg (Ereg regsc [Z_to_bv 64 line])) 32 = Z_to_bv 64 line)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
unfold cw_at.
paj_run_tok RUN HS HJ SHOK RBspan; [awr_ok_tac |].
set (mdv := with_vm_backing _ _ _) in *. clearbody mdv.
cwr_rreg HS (10%bv : bv 5) Ra0. rewrite cwr_den0, E1_32 in Ra0.
cwr_rreg HS (1%bv : bv 5) Rra. cbn [sv_denot] in Rra. rewrite (img_env_codeptr _ HEI) in Rra.
cwr_rreg HS (2%bv : bv 5) R2. rewrite cwr_den0, (ew_Eimg_Ereg_nat regsc _ 2 2%bv eq_refl) in R2.
cwr_rreg HS (3%bv : bv 5) R3. rewrite cwr_den0, (ew_Eimg_Ereg_nat regsc _ 3 3%bv eq_refl) in R3.
cwr_rreg HS (4%bv : bv 5) R4. rewrite cwr_den0, (ew_Eimg_Ereg_nat regsc _ 4 4%bv eq_refl) in R4.
cwr_rreg HS (8%bv : bv 5) R8. rewrite cwr_den0, (ew_Eimg_Ereg_nat regsc _ 8 8%bv eq_refl) in R8.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?m1) |- _ =>
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> rdW Wc m1 a = rdW Wc memc a)
  by (intros a Ha; apply (cwr_keep_ro _ _ _ _ _ a HFr); [unfold ssR1; cbn [ss_mem]; apply Forall_cons; [cbn; lia | apply Forall_nil] | exact Ha])
end.
pmkst HS. rewrite (pal_free B TL).
(* step 2: free(line) *)
assert (HspT : spZ (ms_regs ms) = sp0 + (sp1 - sp0)) by (unfold spZ at 1; rewrite R2; change (bv_unsigned (getr regsc 2)) with (spZ regsc); lia).
assert (Hra4T : 4096 <= raZ (ms_regs ms)) by (unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia).
assert (Hs0T : s0Z (ms_regs ms) = sp0) by (unfold s0Z; rewrite R8, H8; reflexivity).
(* the free's frame chain: check_words' s0 is sp0, its frame pointer (measured at the free). The prologue stored the
   entry's ra and s0 at sp0 - 8 and sp0 - 16, so afn_pre's chain at sp0 grows by that frame (achain_push), kept to
   the call by the journal's clause for the memory above sp0; when sp0 lies within 16 bytes of the stack top the
   chain is empty *)
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & JF1 & _).
assert (ET1 : ly_top lyc = ly_top (e_ly e)) by (destruct Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _); exact ET).
assert (KA : forall a, sp0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW (e_W e) (e_mem e) a).
{ intros a Ha. apply JF1; [lia | lia | apply inFP_nil]. }
assert (HchT : exists chA, achain lyc (rdW Wc (ms_mem ms)) sp1 sp0 chA).
{ destruct (Z_lt_le_dec sp0 (ly_top (e_ly e) - 16)) as [Hlt | Hge].
  - pose proof (Hsaves 0%nat 1 eq_refl) as SV0. pose proof (Hsaves 1%nat 8 eq_refl) as SV1.
    change (Z.of_nat 0) with 0 in SV0. change (Z.of_nat 1) with 1 in SV1.
    replace (sp0 - 8 - 8 * 0) with (sp0 - 8) in SV0 by lia. replace (sp0 - 8 - 8 * 1) with (sp0 - 16) in SV1 by lia.
    change (bv_unsigned (getr (e_regs e) (Z_to_bv 5 1))) with (raZ (e_regs e)) in SV0.
    change (bv_unsigned (getr (e_regs e) (Z_to_bv 5 8))) with (s0Z (e_regs e)) in SV1.
    assert (RD8 : rdword (rdW Wc (ms_mem ms)) (sp0 - 8) = Some (raZ (e_regs e))).
    { apply (rdword_of_val_mem SEGS). apply cwr_val_of_aval.
      - apply (cwr_aval_kept (rdW Wc memc)); [intros k Hk; apply KR; lia | exact SV0].
      - exact (bv_unsigned_in_range 64 (getr (e_regs e) 1)). }
    assert (RD16 : rdword (rdW Wc (ms_mem ms)) (sp0 - 16) = Some (s0Z (e_regs e))).
    { apply (rdword_of_val_mem SEGS). apply cwr_val_of_aval.
      - apply (cwr_aval_kept (rdW Wc memc)); [intros k Hk; apply KR; lia | exact SV1].
      - exact (bv_unsigned_in_range 64 (getr (e_regs e) 8)). }
    assert (Hal8 : sp0 mod 8 = 0).
    { apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. apply Z.mod_divide; [lia|]. exists (2 * q). lia. }
    exists ((sp0, raZ (e_regs e), s0Z (e_regs e)) :: e_ch e).
    apply (achain_ly_top (e_ly e) lyc _ _ _ _ ET1).
    exact (achain_push (e_ly e) (rdW (e_W e) (e_mem e)) (rdW Wc (ms_mem ms)) sp0 (s0Z (e_regs e)) (raZ (e_regs e))
      (e_ch e) sp1 Hch0 ltac:(lia) KA RD8 RD16 Hra40 ltac:(lia) Hal8 Hlt ltac:(lia)).
  - exists []. left. split; [right; left; rewrite ET1; lia | reflexivity]. }
destruct HchT as (ch & HchA).
pose proof (achain_chain_pre lyc (rdW Wc (ms_mem ms)) sp1 sp0 ch (ms_regs ms) HchA ltac:(rewrite HspT; lia) Hs0T Hra4T)
  as Hch1.
assert (Hcov : In (line, cw_JN e) (ablocks B (e_ly e) (e_S e)) ->
  forall i, 0 <= i < req_size (cw_JN e) -> inFP [] (line + i)).
{ intros Hl. exfalso. pose proof (proj1 (Forall_forall _ _) Hapart _ Hl) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart in Hap. lia. }
pose proof MOK as MOK'. unfold XM_CHECK_WORDS in MOK'.
assert (MOKf : mo_ok MT Sc (mo_free MT)) by exact (mo_ok_step MT MTL _ _ _ _ MOK' MLE).
assert (HgpT : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite R3, H3; exact Hgp).
assert (HtpT : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite R4, H4; exact Htp).
eapply SRr_bind.
{ exact (afree04_sub SEGS B LAWS pa_segs_low MT AFREE4 Wc (ms_regs ms) (ms_mem ms) CHECK_WORDS_STK sp0 []
    (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)] lyc Sc mdv EV_JOINED line (cw_JN e) (sp1 - sp0)
    (Z_to_bv 64 (BASE + 6364)) ch HJ Hinl Ra0 HspT (cwr_mod16 sp1 sp0 Hsp32 Hal16) ltac:(lia) ltac:(lia) HgpT HtpT Rra
    (ret_ok_codeptr_v 6364 ltac:(lia) eq_refl) ltac:(lia) Hch1 Hcov MOKf). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl1 & Ebl2) & Hfrs2 & HK2 & MLE2 & _).
(* the state after the free *)
pose proof HJ2 as (HAR2 & Hly2 & _).
assert (EF2 : ly_F ly2 = ly_F (e_ly e)) by (destruct Hly2 as (_ & _ & _ & _ & _ & EF & _); exact EF).
assert (EFA2 : frame_addr ly2 0 pos = F) by (unfold F, frame_addr; rewrite EF2; reflexivity).
assert (EFL2 : flag_addr ly2 0 pos = FL) by (unfold FL, flag_addr; rewrite EF2; reflexivity).
assert (Hin2 : In (0, pos) (frames S2)) by (rewrite Hfrs2; exact Hin1).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR2 Hin2) as (HFal & _ & HFpres & HFSpres).
rewrite EFA2 in HFal. rewrite EFA2, Hfb in HFpres. rewrite EFA2, Hfb8 in HFSpres.
destruct (FFL _ _ _ _ _ 0 pos HAR2 Hin2) as (HFLpres & HFLown & _ & (HFL4096 & _ & HFLceil)).
rewrite EFL2 in HFLpres, HFLown, HFL4096, HFLceil.
assert (HFLF : ~ (F <= FL < F + 64)) by (intros Hx; exact (proj2 (HFpres FL Hx) HFLown)).
assert (HFLS : ~ (CW_SB + F / 8 <= FL < CW_SB + F / 8 + 8)).
{ intros Hx. apply (proj2 (HFSpres (FL - (CW_SB + F / 8)) ltac:(lia))). unfold shadow_addr, SHADOW_OFF, CW_SB in *.
  replace (2147450880 + F / 8 + (FL - (2147450880 + F / 8))) with FL by lia. exact HFLown. }
destruct HK2 as (K1 & _ & _ & K4 & _ & _).
assert (KS : forall a, sp1 <= a < sp0 -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. rewrite (K1 a ltac:(lia) ltac:(lia)). apply KR. lia. }
assert (KF : forall a, F <= a < F + 64 -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. rewrite (K4 0 pos a Hin1 ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA1, Hfb; lia) ltac:(cbv beta; lia)).
  apply KR. lia. }
assert (R28 : getr regs2 8 = w64 sp0).
{ change (getr regs2 8) with (getr regs2 (Z_to_bv 5 8)). rewrite (HP2 8 ltac:(unfold acallee_saved; lia)).
  change (getr (ms_regs ms) (Z_to_bv 5 8)) with (getr (ms_regs ms) 8). rewrite R8, H8. unfold w64, sp0, spZ.
  symmetry. apply Z_to_bv_bv_unsigned. }
assert (R29 : getr regs2 9 = w64 sp1).
{ change (getr regs2 9) with (getr regs2 (Z_to_bv 5 9)). rewrite (HP2 9 ltac:(unfold acallee_saved; lia)).
  cwr_rreg HS (9%bv : bv 5) R9. rewrite cwr_den0, (ew_Eimg_Ereg_nat regsc _ 9 9%bv eq_refl) in R9.
  change (getr (ms_regs ms) (Z_to_bv 5 9)) with (getr (ms_regs ms) 9). rewrite R9. exact H9. }
assert (V16' : aval_mem (rdW W2 mem2) (sp1 + 16) 8 (CW_SB + F / 8)).
{ apply (cwr_aval_kept (rdW Wc memc)); [intros k Hk; apply KS; lia | exact V16]. }
assert (V24' : aval_mem (rdW W2 mem2) (sp1 + 24) 8 F).
{ apply (cwr_aval_kept (rdW Wc memc)); [intros k Hk; apply KS; lia | exact V24]. }
assert (V32' : aval_mem (rdW W2 mem2) (sp1 + 32) 8 F).
{ apply (cwr_aval_kept (rdW Wc memc)); [intros k Hk; apply KS; lia | exact V32]. }
assert (VFL' : aval_mem (rdW W2 mem2) (F + 56) 8 FL).
{ apply (cwr_aval_kept (rdW Wc memc)); [intros k Hk; apply KF; lia | exact VFL]. }
assert (VSV' : cw_saves (rdW W2 mem2) sp0 (e_regs e)).
{ intros j r Hj. pose proof (cwr_saved_lt j r Hj) as Hj13.
  apply (cwr_aval_kept (rdW Wc memc)); [intros k Hk; apply KS; lia | exact (Hsaves j r Hj)]. }
assert (PS' : forall i, 0 <= i < 8 -> apresent (w_H W2) mem2 (CW_SB + F / 8 + i)).
{ intros i Hi. pose proof (proj1 (HFSpres i Hi)) as P. unfold shadow_addr, SHADOW_OFF in P. unfold CW_SB. exact P. }
pose proof (cwr_seed2 W2 regs2 (e_regs e) mem2 sp0 sp1 F FL R28 R29 ltac:(lia) Hsp1c ltac:(lia) ltac:(lia) Hal16 Hsp32
  HF4096 HFceil HFal HFapp HFL4096 HFLceil HFLF HFLS V16' V24' V32' VFL' VSV'
  (fun a Ha => proj1 (HFpres a Ha)) PS' HFLpres) as HS2.
assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg regs2 (r2_extra (e_regs e) F FL)))) by apply Eimg_env.
destruct (cwr_E2 regs2 (e_regs e) F FL) as (E2_32 & E2_33 & E2_34 & E2SV).
assert (B34 : bv_unsigned (ew (Eimg (Ereg regs2 (r2_extra (e_regs e) F FL))) 34) = FL) by (rewrite E2_34; apply unsigned_lit_small; lia).
assert (B33 : bv_unsigned (ew (Eimg (Ereg regs2 (r2_extra (e_regs e) F FL))) 33) = CW_SB + F / 8)
  by (rewrite E2_33; apply unsigned_lit_small; unfold CW_SB; lia).
assert (B32 : bv_unsigned (ew (Eimg (Ereg regs2 (r2_extra (e_regs e) F FL))) 32) = F) by (rewrite E2_32; apply unsigned_lit_small; lia).
clear HS SHOK HEI.
(* step 3: the frame's release, the restore and the return *)
paj_run_flag_sh RUNF HS2 HJ2.
- lia.
- intros a (r & Hin & Hr). unfold ssR2, r2_regions in Hin. cbn [ss_mem] in Hin.
  unfold r_flag, r_fsh, fshadow_region, r_frame, fframe_region, r_scr, r_sav in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  + right. rewrite EFL2. rewrite B34 in Hr. lia.
  + left. right; right; right; left. exists 0, pos. split; [left; reflexivity|]. right.
    rewrite B33 in Hr. unfold in_zr. cbn [fst snd]. rewrite EFA2, Hfb8. unfold shadow_addr, SHADOW_OFF, CW_SB in *. lia.
  + left. right; right; right; left. exists 0, pos. split; [left; reflexivity|]. left.
    rewrite B32, Hfb in Hr. unfold in_zr. cbn [fst snd]. rewrite EFA2, Hfb. lia.
  + exfalso. lia.
  + exfalso. lia.
- intros msr HSr. rewrite EFL2.
  pose proof (st_ok_pi_region_nth _ _ msr 0 _ HSr eq_refl) as HR.
  pose proof (field_of_region _ (ms_mem msr) 34 FL _ _ _ _ _ 0 1%N (SLit 0) 0 HR B34 (or_introl eq_refl) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  specialize (V 0%nat ltac:(cbn; lia)). replace (FL + 0 + Z.of_nat 0) with FL in V by lia. rewrite V. reflexivity.
- set (mdw := with_vm_backing _ _ _) in *. clearbody mdw.
  lazymatch goal with HSf : st_ok_pi _ _ _ ?ssf (restrict _ ?msf) |- _ =>
    apply (RET W2 _ ssf msf mdw (cw_post B MT e) HSf eq_refl ltac:(vm_compute; reflexivity)) end.
  intros mat2.
  lazymatch goal with |- cw_post _ _ e W2 (mkCfg (mkst (ms_regs ?msf) _ _ _) _) => rename msf into msF end.
  assert (HPf : Permutation (ablocks B ly2 (stack_free_state 0 pos S2)) (ablocks B (e_ly e) (e_S e))).
  { change (ablocks B ly2 (stack_free_state 0 pos S2)) with (ablocks B ly2 S2). rewrite Ebl2.
    assert (Hx : Permutation ((line, cw_JN e) :: ablocks B (e_ly e) (e_S e)) (l1 ++ (line, cw_JN e) :: l2))
      by (rewrite <- Ebl1; apply Permutation_sym; exact HPerm).
    exact (Permutation_sym (Permutation_cons_app_inv _ _ Hx)). }
  cwr_rreg HS2 (1%bv : bv 5) F1. rewrite cwr_den0 in F1.
  unfold cw_post. apply (apost_baseF_of_base SEGS). unfold apost_base.
  exists ly2, (stack_free_state 0 pos S2), (ms_regs msF), (ms_mem msF), (with_vm_backing (m_vm_lazy mdw) mat2 mdw).
  split.
  { rewrite F1. change (ew (Eimg (Ereg regs2 (r2_extra (e_regs e) F FL))) 35) with
      (ew (Eimg (Ereg regs2 (r2_extra (e_regs e) F FL))) (35 + 0)). rewrite (E2SV 0%nat 1 eq_refl).
    change (getr (e_regs e) (Z_to_bv 5 1)) with (getr (e_regs e) 1). unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split.
  { exact (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ (EV_JOINED + 1) EV_CHECK_WORDS
      (ajournal_materialize SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat2 HJ2) ltac:(lia)). }
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia. clear Hr.
    destruct Hr' as [-> | [-> | [-> | Hr']]].
    - cwr_rreg HS2 (Z_to_bv 5 2) X. rewrite X, cwr_den0, (ew_Eimg_Ereg_nat regs2 _ 8 8%bv eq_refl), R28.
      unfold w64, sp0, spZ. apply Z_to_bv_bv_unsigned.
    - cwr_rreg HS2 (Z_to_bv 5 3) X. rewrite X, cwr_den0, (ew_Eimg_Ereg_nat regs2 _ 3 (Z_to_bv 5 3) eq_refl).
      rewrite (HP2 3 ltac:(unfold acallee_saved; lia)). exact (eq_trans R3 H3).
    - cwr_rreg HS2 (Z_to_bv 5 4) X. rewrite X, cwr_den0, (ew_Eimg_Ereg_nat regs2 _ 4 (Z_to_bv 5 4) eq_refl).
      rewrite (HP2 4 ltac:(unfold acallee_saved; lia)). exact (eq_trans R4 H4).
    - repeat (destruct Hr' as [Hr0 | Hr']; [subst r; cwr_saved_reg HS2 E2SV|]). subst r. cwr_saved_reg HS2 E2SV. }
  split; [exact HPf|].
  split; [exact (cwr_rec_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 (fun pn H => Permutation_in _ (Permutation_sym HPf) H) HREC)|].
  split.
  { rewrite (blocks_bytes_bsum B ly2 (stack_free_state 0 pos S2)), (blocks_bytes_bsum B (e_ly e) (e_S e)), (bsum_perm _ _ HPf).
    assert (LIVE_CHECK_WORDS = 268435456) by reflexivity. lia. }
  unfold stack_free_state. apply (mo_le_set_fs_r MT MTFL). exact (mo_le_trans MT MTL _ _ _ _ _ MLE MLE2).
Qed.
End e.
End f.
End d.
