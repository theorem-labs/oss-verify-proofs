(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: send_message's walk segment s3 on plugin-hostd/fuzz_command's ASan image, from
   0x86c48 (after the copy) to rec_clear's return 0x86c70, ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v,
   AChc.v and ACke.v at c8557374ad2e (cgif_close's segment chain and its program-callee steps) with the class-1 frame
   and inline-check steps of A/ACk1.v (cgif_newgif). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow CmdSyms CmdList CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaJournal CmdPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YE00 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep CmdObj CmdRo CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_clear_c verbs_receive_c send_message_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import send_message_k send_message_l PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the symbolic state at 0x86c48 (SM_J)
   Atoms 0..31 are the registers at 0x86c48; atom 32 is g_quitting's address, the value of its GOT word 0xa7080
   (A_OBJ 6), kept symbolic so that the shadow address (x >> 3) + s9 of the inline check stays in the form the
   token executor matches. s9 (atom 25) is the shadow base, the check's Bx. Regions: the GOT word (read-only),
   g_quitting's 4 bytes (written by `sw zero`), msg.data / msg.data_size at s5 + 8 .. s5 + 24 (s5 = F + 32). The
   frame's shadow is not a region: the run reads only g_quitting's shadow byte, which the token executor turns into
   a token and an obligation. *)
Definition sm3_extra : list word := map (Z_to_bv 64) [A_G_QUITTING].
Definition sm3_regions : smem :=
[ obj8_region 6 (SOff 32 0); YP09.mkRegion (Some 32%nat) 0 4 0 4 []; YP09.mkRegion (Some 21%nat) 8 24 8 24 [] ].
Definition sm3_atoms : list (nat * afact) :=
[ (21%nat, HPTR 5); (25%nat, mkAF SB SB 0); (32%nat, mkAF 0x10000 0x606000 2) ].
Definition ss_sm3 : sstate := mkSS SM_J sr_atoms sm3_regions None (mkFacts sm3_atoms [] []).
Definition SM3x : sv := SOff 25 0.

Lemma val_mem_of_aval : forall segs H mem a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma aval_of_val_mem : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte, YG0f.le_byte. apply Z.mod_mod. lia.
Qed.
Lemma inFP_app_inv : forall l1 l2 a, inFP (l1 ++ l2) a -> inFP l1 a \/ inFP l2 a.
Proof. intros l1 l2 a (r & Hr & Ha). apply in_app_or in Hr as [Hr|Hr]; [left|right]; exists r; auto. Qed.
Lemma inFP_app_l : forall l1 l2 a, inFP l1 a -> inFP (l1 ++ l2) a.
Proof. intros l1 l2 a (r & Hr & Ha). exists r. split; [apply in_or_app; left; exact Hr | exact Ha]. Qed.
Lemma inFP_app_r : forall l1 l2 a, inFP l2 a -> inFP (l1 ++ l2) a.
Proof. intros l1 l2 a (r & Hr & Ha). exists r. split; [apply in_or_app; right; exact Hr | exact Ha]. Qed.
Lemma ev_args_nonneg : forall R, 0 <= ev_args R.
Proof. intros R. unfold ev_args. induction (r_calls R) as [|c l IH]; cbn [fold_right]; lia. Qed.
(* distinct live blocks: the allocator's blocks are pairwise disjoint and each covers at least one byte *)
Lemma nodup_blocks : forall l : list (Z * Z), Forall (fun b => 0 <= snd b) l ->
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
induction l as [|x l IH]; cbn [map pairwise]; intros Hn Hp; [constructor|].
destruct Hp as [Hf Hp]. inversion Hn as [|? ? Hx Hl]; subst. constructor; [|exact (IH Hl Hp)].
intros Hin. rewrite Forall_forall in Hf. specialize (Hf _ (in_map (fun b => (fst b, req_size (snd b))) _ _ Hin)).
pose proof (req_size_pos (snd x) Hx) as [H1 _]. unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Lemma perm_filter_split : forall {A} (f : A -> bool) l,
Permutation l (List.filter f l ++ List.filter (fun x => negb (f x)) l).
Proof.
intros A f l. induction l as [|x l IH]; cbn [List.filter]; [constructor|].
destruct (f x); cbn [negb app].
- constructor. exact IH.
- eapply perm_trans; [apply perm_skip; exact IH | apply Permutation_middle].
Qed.
Definition zz_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Definition zz_inb (D : list (Z * Z)) (x : Z * Z) : bool := if in_dec zz_dec x D then true else false.
(* the blocks after rec_clear: its freed set D is the part of the recorder's blocks O it no longer owns, so the
   blocks left are O minus D, the copy's block and the others *)
Lemma sm3_perm : forall (A0 A2 O O' Dfr rest : list (Z * Z)) r,
List.NoDup (A0 ++ [r]) -> Permutation A0 (O ++ rest) -> Permutation (A0 ++ [r]) (A2 ++ Dfr) ->
(forall pn, In pn Dfr <-> In pn O /\ ~ In pn O') ->
Permutation A2 (List.filter (fun x => negb (zz_inb Dfr x)) O ++ r :: rest).
Proof.
intros A0 A2 O O' Dfr rest r HND HP0 HP1 HD.
set (O1 := List.filter (fun x => negb (zz_inb Dfr x)) O). set (D' := List.filter (zz_inb Dfr) O).
assert (HND1 : List.NoDup (A2 ++ Dfr)) by (exact (Permutation.Permutation_NoDup HP1 HND)).
assert (HNDD : List.NoDup Dfr) by (exact (List.NoDup_app_remove_l _ _ HND1)).
assert (HNDO : List.NoDup O).
{ assert (H : List.NoDup (O ++ rest ++ [r])).
  { apply (Permutation.Permutation_NoDup (l := A0 ++ [r])); [|exact HND]. rewrite app_assoc. apply Permutation_app_tail. exact HP0. }
  exact (List.NoDup_app_remove_r _ _ H). }
assert (HDD : Permutation D' Dfr).
{ apply Permutation.NoDup_Permutation; [apply List.NoDup_filter; exact HNDO | exact HNDD |].
  intros x. unfold D'. rewrite List.filter_In. unfold zz_inb. destruct (in_dec zz_dec x Dfr) as [Hx|Hx]; split; intros H.
  - exact Hx.
  - split; [exact (proj1 (proj1 (HD x) H)) | reflexivity].
  - destruct H as [_ H]; discriminate H.
  - exfalso; exact (Hx H). }
apply (Permutation_app_inv_r Dfr).
eapply perm_trans; [apply Permutation_sym; exact HP1 |].
eapply perm_trans; [apply Permutation_app_tail; exact HP0 |].
eapply perm_trans; [apply Permutation_app_tail; apply Permutation_app_tail; exact (perm_filter_split (zz_inb Dfr) O) |].
eapply perm_trans; [|apply Permutation_app_head; exact HDD].
fold D' O1. rewrite <- !app_assoc. cbn [app].
eapply perm_trans; [apply Permutation_app_comm |].
rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma sm3_O1_iff : forall (O O' Dfr : list (Z * Z)), (forall pn, In pn O' -> In pn O) ->
(forall pn, In pn Dfr <-> In pn O /\ ~ In pn O') ->
forall pn, In pn (List.filter (fun x => negb (zz_inb Dfr x)) O) <-> In pn O'.
Proof.
intros O O' Dfr HI HD pn. rewrite List.filter_In. unfold zz_inb. destruct (in_dec zz_dec pn Dfr) as [Hx|Hx]; cbn [negb].
- split; [intros [_ H]; discriminate H | intros H; exfalso; exact (proj2 (proj1 (HD pn) Hx) H)].
- split; [intros [H _] | intros H; split; [exact (HI pn H) | reflexivity]].
  destruct (in_dec zz_dec pn O') as [Hy|Hy]; [exact Hy | exfalso; apply Hx; apply (proj2 (HD pn)); split; assumption].
Qed.
Lemma sm_regs_core_pres : forall regs regs1 regs2 F n src,
sm_regs_core regs regs1 F n src -> aregs_preserved regs1 regs2 -> sm_regs_core regs regs2 F n src.
Proof.
intros regs regs1 regs2 F n src (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q23 & Q24 & Q25 & Q26 & Q27) HP.
refine (conj (eq_trans (HP 2 _) Q2) (conj (eq_trans (HP 3 _) Q3) (conj (eq_trans (HP 4 _) Q4)
(conj (eq_trans (HP 8 _) Q8) (conj (eq_trans (HP 9 _) Q9) (conj (eq_trans (HP 18 _) Q18) (conj (eq_trans (HP 19 _) Q19)
(conj (eq_trans (HP 20 _) Q20) (conj (eq_trans (HP 23 _) Q23) (conj (eq_trans (HP 24 _) Q24) (conj (eq_trans (HP 25 _) Q25)
(conj (eq_trans (HP 26 _) Q26) (eq_trans (HP 27 _) Q27)))))))))))));
unfold acallee_saved; lia.
Qed.
(* g_quitting's GOT word 0xa7080 holds g_quitting's address: cmd_ro_ok's RO_ptr_a7080 (CmdRo.v), read as a word *)
Lemma sm_got80 : forall rd, cmd_ro_ok rd -> aval_mem rd 0xa7080 8 A_G_QUITTING.
Proof.
intros rd [HB _]. unfold cmd_ro_bytes in HB. repeat (destruct HB as [_ HB]).
intros k Hk. rewrite (HB k ltac:(change (length RO_ptr_a7080) with 8%nat; exact Hk)).
do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
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
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the walk hypotheses, with cgif's names *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
(* the read-only range facts *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Context {RO : ro_below_ofl SEGS RLO RHI}.
(* the callee statement *)
Hypothesis RCL : forall fx0 : YK11.FPState, @trec_clear_spec fx0 rc SK PI B MT.
(* the per-binary record (the walk hypothesis HB), which cmd_addressable_chk (CmdRecBase.v) takes, and the
   image facts (CmdRecBase.v cmd_img_facts) *)
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
(* the per-binary record fact cmd_prog_unowned (CmdRecImg.v) *)
Let cmd_prog_unowned := CmdRecImg.cmd_prog_unowned SEGS B LAWS HB IMG.
(* the program statics' writability (PRW, for cmd_PG; send_message.v's sm_P0 gives it) *)
Hypothesis cmd_prog_writable : forall ly S W mem md a, AR SEGS B ly S W mem md -> inFP cmd_PG a ->
writable_at SEGS (mrestrict (w_H W) mem) a.
(* narrow per-binary facts this segment adds (the send_message walk's names; cmd_sig_prog, CmdBSyms's ts_prog
   pins and CmdRo give them) *)
Hypothesis CMD_PG_NOT_RO : forall a, inFP cmd_PG a -> ~ in_roP SEGS RLO RHI a.
Hypothesis CMD_GOT_UNOWNED : forall a, 0xa7068 <= a < 0xa7088 ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis SIGMA_rec_clear : SIGMA CS_rec_clear = BASE + AF_rec_clear.
Hypothesis G_QUITTING_PROG : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> Exists (in_zr a) (as_prog_static B).
Hypothesis G_REC_PROG : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) (as_prog_static B).

Lemma sm3_seed : forall Wc lyc Sc memc mdc (regs1 : bvmap 5 word) F fpos,
AR SEGS B lyc Sc Wc memc mdc -> In (1, fpos) (frames Sc) -> frame_addr lyc 1 fpos = F ->
getr regs1 21 = w64 (F + 32) -> getr regs1 25 = w64 SB ->
aval_mem (rdW Wc memc) 0xa7080 8 A_G_QUITTING -> cmd_val_objs ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 sm3_extra)) ss_sm3
(restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + SM_J)) memc (seg_rom SEGS))).
Proof.
intros Wc lyc Sc memc mdc regs1 F fpos HAR Hfin EF R21 R25 HGOT VOBJ.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR Hfin) as (HFal & HFapp & HFpres & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR Hfin) as (HF4096 & HFceil & _).
assert (HFimg : off_img (frame_addr lyc 1 fpos) (fs_frame_bytes 1)) by (eapply frm_off_imgP; eassumption).
rewrite EF in HFal, HFapp, HFpres, HF4096, HFceil, HFimg.
change (fs_frame_bytes 1) with 128 in HFpres, HFceil, HFimg.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (V6 : VAL (A_OBJ 6) = 0xa7080) by (rewrite (VOBJ 6%nat) by nat_side; reflexivity).
set (E := Eimg (Ereg regs1 sm3_extra)).
assert (E21 : ew E 21 = Z_to_bv 64 (F + 32))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 21 21%bv eq_refl); exact R21).
assert (E25 : ew E 25 = Z_to_bv 64 SB)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew E 32 = Z_to_bv 64 A_G_QUITTING)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 sm3_extra 0)).
assert (E247 : ew E (A_OBJ 6) = Z_to_bv 64 (VAL (A_OBJ 6))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (B247 : base_val E (Some (A_OBJ 6)) = 0xa7080)
by (rewrite (VB (A_OBJ 6) (VAL (A_OBJ 6)) E247) by (pose proof (pa_val_range (A_OBJ 6)); lia); exact V6).
assert (B32 : base_val E (Some 32%nat) = A_G_QUITTING) by (apply VB; [exact E32 | unfold A_G_QUITTING; lia]).
assert (B21 : base_val E (Some 21%nat) = F + 32) by (apply VB; [exact E21 | lia]).
rewrite restrict_mkst_fx. unfold ss_sm3. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sm3_regions, obj8_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ rewrite B247. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ 0xa7080 0 8 (SOff 32 0) A_G_QUITTING);
[rewrite sv_denot_SOff0; exact E32 | unfold A_G_QUITTING; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_aval _ _ _ _ _ _ HGOT).
+ rewrite B32. split; [unfold A_G_QUITTING; lia|]. split; [unfold A_G_QUITTING; lia|]. split; [|constructor].
intros o Ho. apply (cmd_prog_writable lyc Sc Wc memc mdc _ HAR).
exists (A_G_QUITTING, A_G_QUITTING + 4). split; [right; right; left; reflexivity | cbn [fst snd]; lia].
+ rewrite B21. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFpres (F + 32 + o) ltac:(lia))).
- apply pairwise_disjoint_of_extents.
unfold sm3_regions, obj8_region, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite B247, B32, B21.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert HFimg HF4096 HFceil C1. clear. unfold off_img, A_G_QUITTING. intros.
repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok sm3_atoms]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E21, E25, E32. rewrite !unsigned_lit_small by (unfold SB, A_G_QUITTING; lia).
change (2 ^ 5) with 32. change (2 ^ 2) with 4. rewrite Z.pow_0_r, Z.mod_1_r.
assert (HF32 : (F + 32) mod 32 = 0) by (replace (F + 32) with (F + 1 * 32) by lia; rewrite Z.mod_add by lia; exact HFal).
revert HF32 HF4096 HFceil C1. clear. unfold SB, A_G_QUITTING. intros.
repeat match goal with |- _ /\ _ => split end; first [exact I | reflexivity | lia].
Qed.

Theorem sm_s3 : SM_P3_stmt B MT -> SM_P2_stmt B MT.
Proof.
intros P3 ly S W regs mem md ch src n D R O rest lyc Sc Wc regs1 memc mdc k fpos res
CX JR Hk RC R21 R22 SAV FRM Eab Hres Hnin BYT MOLE.
pose proof CX as (HPRE & HFRM & Hfr3 & HROD & HROK & VOBJ & H10 & Hsrcr & H11 & Hn & HlenD & HBYT0 & Hsrc &
HPerm & HREP & Hcalls & Hdecl & Hev & Hlive & HMOK).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof JR as (HJ0 & Hfrs).
pose proof HJ0 as (HARc & Hly & Hsecs & Hwle & Hio & Hfrs' & Hnev & Hk0 & F1 & F2 & F3 & F4 & Hgone & Hpres' & Hstk' & F5 & HQTc).
pose proof RC as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q23 & Q24 & Q25 & Q26 & Q27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EFc : frame_addr lyc 1 fpos = frame_addr ly 1 fpos)
by (destruct Hly as (_ & _ & _ & _ & _ & L6 & _); unfold frame_addr; rewrite L6; reflexivity).
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
assert (Hfin : In (1, fpos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HARc Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HARc Hfin) as (HF4096 & HFceil & _).
assert (HFimg : off_img (frame_addr lyc 1 fpos) (fs_frame_bytes 1)) by (eapply frm_off_imgP; eassumption).
rewrite EFc in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil, HFimg.
change (fs_frame_bytes 1) with 128 in HFpres, HFSpres, HFceil, HFimg, HFapp.
(* (1) the recorder and the GOT word at 0x86c48 *)
assert (HinO : forall pn, In pn O -> In pn (ablocks B ly S))
by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPerm)); apply in_or_app; left; exact Hpn).
assert (HinOc : forall pn, In pn O -> In pn (ablocks B lyc Sc))
by (intros pn Hpn; rewrite Eab; apply in_or_app; left; apply HinO; exact Hpn).
assert (HPGk : forall a, inFP cmd_PG a -> rdW Wc memc a = rdW W mem a).
{ intros a Ha. destruct (cmd_prog_unowned a Ha) as (Hi & Ho & He).
  apply F3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [exact sink_closed_nil | apply inFP_nil]]. }
assert (HPG1 : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP cmd_PG a)
by (intros a Ha; exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Ha; lia]).
assert (HPG2 : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP cmd_PG a)
by (intros a Ha; exists (A_REC_SPILL, A_REC_SPILL + 56); split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Ha; lia]).
assert (HPG3 : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> inFP cmd_PG a)
by (intros a Ha; exists (A_G_QUITTING, A_G_QUITTING + 4); split; [right; right; left; reflexivity | cbn [fst snd]; lia]).
assert (HREPc : rec_repA B lyc Sc (rdW Wc memc) R O).
{ eapply (rec_repA_kept B); [exact HREP | exact HinOc |].
  intros a [Ha | [Ha | Ha]]; [apply HPGk, HPG1, Ha | apply HPGk, HPG2, Ha |].
  destruct (inFP_ablocks_fp_inv _ _ Ha) as (p & m & Hpm & Hpa).
  replace a with (p + (a - p)) by lia. apply (F2 p m (a - p) (HinO _ Hpm) (HinOc _ Hpm)); [lia | apply inFP_nil]. }
assert (HG80 : forall a, 0xa7080 <= a < 0xa7088 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
by (intros a Ha; apply CMD_GOT_UNOWNED; lia).
assert (HGOTc : aval_mem (rdW Wc memc) 0xa7080 8 A_G_QUITTING).
{ apply (aval_mem_kept_r (rdW W mem)); [|exact (sm_got80 _ HROK)].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. destruct (HG80 x ltac:(lia)) as (Hi & Ho & He).
  apply F3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [exact sink_closed_nil | apply inFP_nil]]. }
(* (2) the journal's footprint widened to the recorder's blocks and the program's statics *)
set (FP := ablocks_fp O ++ cmd_PG).
assert (HFPc : ~ YI16.sink_open_fp FP).
{ unfold FP. apply sink_closed_app; [apply sink_closed_ablocks_fp |].
  - apply Forall_forall. intros [p m] Hpm. cbn [fst].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR0 (HinO _ Hpm)) as (_ & H4096 & _). lia.
  - apply sink_closed_pos. unfold cmd_PG. repeat apply Forall_cons; try apply Forall_nil; cbn [fst];
    unfold A_G_REC, A_REC_SPILL, A_G_QUITTING; lia. }
assert (HJ : ajournal SEGS B SEND_MESSAGE_STK (spZ regs) FP ly S W mem md [(1, fpos)] lyc Sc Wc memc mdc k).
{ eapply ajournal_fp_widen; [exact HJ0 | intros a Ha; destruct (inFP_nil a Ha) | exact HFPc]. }
(* (3) the symbolic state at 0x86c48 and the run to the call of rec_clear *)
pose proof (sm3_seed Wc lyc Sc memc mdc regs1 F fpos HARc Hfin EFc R21 Q25 HGOTc VOBJ) as HS.
set (E := Eimg (Ereg regs1 sm3_extra)) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E21 : ew E 21 = Z_to_bv 64 (F + 32))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 21 21%bv eq_refl); exact R21).
assert (E25 : ew E 25 = Z_to_bv 64 SB)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 25 25%bv eq_refl); exact Q25).
assert (E32 : ew E 32 = Z_to_bv 64 A_G_QUITTING)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 sm3_extra 0)).
assert (E19 : ew E 19 = Z_to_bv 64 n)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 19 19%bv eq_refl); exact Q19).
assert (E22 : ew E 22 = Z_to_bv 64 res)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 22 22%bv eq_refl); exact R22).
assert (HAG0 : forall n0, (n0 < 32)%nat -> ew E n0 = ew (Ereg regs1 sm3_extra) n0)
by (intros n0 Hn0; subst E; apply Eimg_low; unfold A_TEXT; lia).
(* the copy's block and the recorder's blocks at 0x86c48 *)
assert (Hrin : In (res, Z.max n 1) (ablocks B lyc Sc)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hrin) as (_ & _ & Hrceil & Hrapp & _ & HPW & _).
assert (Hrimg : off_img res (req_size (Z.max n 1))) by (eapply blk_off_imgP; eassumption).
assert (Hrq : req_size (Z.max n 1) = Z.max n 1) by (unfold req_size; destruct (Z.eqb_spec (Z.max n 1) 0); lia).
rewrite Hrq in Hrceil, Hrapp, Hrimg.
assert (HrF : zdisjoint (res, Z.max n 1) (F, 128)).
{ pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ 1 fpos HARc Hrin Hfin) as H. rewrite Hrq, EFc in H. exact H. }
assert (HrnO : ~ In (res, Z.max n 1) O) by (intros H; exact (Hnin (HinO _ H))).
assert (HOb : forall p m, In (p, m) O -> 0 <= m /\ 4096 <= p /\ p + req_size m <= alloc_ceiling /\
  in_app p (req_size m) /\ off_img p (req_size m) /\ zdisjoint (p, req_size m) (F, 128) /\
  zdisjoint (p, req_size m) (res, Z.max n 1)).
{ intros p m Hpm. pose proof (HinOc _ Hpm) as Hpm'.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hpm') as (_ & H4096 & Hpc & Hpa & _ & _ & Hm).
  split; [lia|]. split; [exact H4096|]. split; [exact Hpc|]. split; [exact Hpa|].
  split; [eapply blk_off_imgP; eassumption|].
  split; [pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ 1 fpos HARc Hpm' Hfin) as H; rewrite EFc in H; exact H|].
  pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HARc Hpm' Hrin ltac:(intros E0; apply HrnO; rewrite <- E0; exact Hpm)) as H.
  rewrite Hrq in H. exact H. }
assert (HND : List.NoDup (ablocks B lyc Sc)).
{ apply nodup_blocks; [|exact HPW]. apply Forall_forall. intros [p m] Hpm.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hpm) as (_ & _ & _ & _ & _ & _ & Hm). cbn [snd]. lia. }
assert (HF8 : 8 * (F / 8) <= F < 8 * (F / 8) + 8)
by (pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
(* rec_clear's footprint *)
set (FP1 := (A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O).
assert (HnFP1 : forall a, ~ (A_G_REC <= a < A_G_REC + REC_SIZE) ->
  (forall p m, In (p, m) O -> ~ (p <= a < p + req_size m)) -> ~ inFP FP1 a).
{ intros a H1 H2 Ha. unfold FP1 in Ha. apply inFP_cons in Ha as [Ha | Ha]; [exact (H1 Ha)|].
  destruct (inFP_ablocks_fp_inv _ _ Ha) as (p & m & Hpm & Hpa). exact (H2 p m Hpm Hpa). }
assert (HFP1c : ~ YI16.sink_open_fp FP1).
{ unfold FP1. apply sink_closed_cons; [cbn [fst]; unfold A_G_REC; lia|]. apply sink_closed_ablocks_fp.
  apply Forall_forall. intros [p m] Hpm. cbn [fst]. destruct (HOb p m Hpm) as (_ & H4096 & _). lia. }
(* the stack: the realigned stack pointer sp1 at the call *)
assert (HSTKv : 112 <= SEND_MESSAGE_STK) by (vm_compute; discriminate).
assert (Hsp96 : (spZ regs - 96) mod 16 = 0)
by (replace (spZ regs - 96) with (spZ regs + (-6) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
destruct (sp1_facts (spZ regs - 96) ltac:(lia) Hsp96) as (Hs1 & Hs32 & Hs16).
fold (sm_sp1 (spZ regs)) in Hs1, Hs32, Hs16.
destruct (sm_achain B [] ly S W regs mem md ch fpos lyc Sc Wc memc mdc k HPRE JR
  ltac:(intros a _ Ha; exact (inFP_nil a Ha)) SAV) as [ch1 HCH].
(* the run: GOT load, msg.data / msg.data_size, the check (token), g_quitting = 0, up to `jal rec_clear` *)
shok_auto SHOK SM3x E (mrestrict (w_H Wc) memc).
pose (RUN := paj_run B LAWS).
paj_run_tok RUN HS HJ SHOK SMBspan.
{ eapply obl_of_range;
  [exact (cmd_addressable_chk SEGS B LAWS HB lyc Sc Wc memc mdc A_G_QUITTING 4 HARc ltac:(vm_compute; reflexivity)) | | |].
  - unfold SM3x. rewrite (U_atom E 25 SB E25) by (unfold SB; lia). exact SB_SHADOW_OFF.
  - rewrite (U_atom E 32 A_G_QUITTING E32) by (unfold A_G_QUITTING; lia). lia.
  - rewrite (U_atom E 32 A_G_QUITTING E32) by (unfold A_G_QUITTING; lia). lia. }
{ unfold ss_sm3, sm3_regions, obj8_region. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  eapply awr_ok_cons_gen; [reflexivity | rewrite E32; apply unsigned_lit_small; unfold A_G_QUITTING; lia | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; right; left.
    split; [unfold FP; apply inFP_app_r; apply HPG3; lia|]. split; [apply G_QUITTING_PROG; lia|].
    exact (proj1 (cmd_prog_unowned a (HPG3 a ltac:(lia)))). }
  eapply awr_ok_cons_gen; [reflexivity | rewrite E21; apply unsigned_lit_small; lia | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 1, fpos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EFc. change (fs_frame_bytes 1) with 128. lia. }
  apply awr_ok_nil. }
(* at the call: registers *)
prreg HS (1%bv : bv 5) Rra.
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E' := Ex) in * end.
assert (HAG : env_agree 32 (Ereg regs1 sm3_extra) E').
{ split; [|reflexivity]. intros n0 Hn0. unfold E'. rewrite !ew_ewset_other by lia. apply HAG0. exact Hn0. }
assert (E'21 : ew E' 21 = Z_to_bv 64 (F + 32)) by (unfold E'; rewrite !ew_ewset_other by lia; exact E21).
assert (E'19 : ew E' 19 = Z_to_bv 64 n) by (unfold E'; rewrite !ew_ewset_other by lia; exact E19).
assert (E'22 : ew E' 22 = Z_to_bv 64 res) by (unfold E'; rewrite !ew_ewset_other by lia; exact E22).
assert (E'32 : ew E' 32 = Z_to_bv 64 A_G_QUITTING) by (unfold E'; rewrite !ew_ewset_other by lia; exact E32).
pose proof (aregs_preserved_of_st_ok SEGS (w_H Wc) E' _ ms regs1 sm3_extra HS HAG ltac:(vm_compute; reflexivity)) as HPRc.
(* at the call: memory *)
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
  pose proof (st_ok_region_nth E' ssx msx 1%nat _ HS eq_refl) as HR1;
  pose proof (st_ok_region_nth E' ssx msx 2%nat _ HS eq_refl) as HR2 end.
pmkst HS.
rewrite SIGMA_rec_clear.
set (mdk := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
set (regsc := ms_regs ms) in *. set (memk := ms_mem ms) in *.
assert (V40 : val_mem SEGS (mrestrict (w_H Wc) memk) (F + 40) 8 res).
{ replace (F + 40) with (F + 32 + 8) by lia.
  refine (field_of_region E' _ 21 (F + 32) _ 8 24 8 24 8 8%N (SOff 22 0) res HR2 _ _ _ _ _).
  - rewrite E'21. apply unsigned_lit_small. lia.
  - right; left; reflexivity.
  - rewrite sv_denot_SOff0. exact E'22.
  - change (8 * Z.of_N 8) with 64. lia.
  - change (Z.of_N 8) with 8. lia. }
assert (V48 : val_mem SEGS (mrestrict (w_H Wc) memk) (F + 48) 8 n).
{ replace (F + 48) with (F + 32 + 16) by lia.
  refine (field_of_region E' _ 21 (F + 32) _ 8 24 8 24 16 8%N (SOff 19 0) n HR2 _ _ _ _ _).
  - rewrite E'21. apply unsigned_lit_small. lia.
  - left; reflexivity.
  - rewrite sv_denot_SOff0. exact E'19.
  - change (8 * Z.of_N 8) with 64. lia.
  - change (Z.of_N 8) with 8. lia. }
assert (V0 : val_mem SEGS (mrestrict (w_H Wc) memk) (A_G_QUITTING + 0) 4 0).
{ refine (field_of_region E' _ 32 A_G_QUITTING _ 0 4 0 4 0 4%N (SLit 0) 0 HR1 _ _ _ _ _).
  - rewrite E'32. apply unsigned_lit_small. unfold A_G_QUITTING; lia.
  - left; reflexivity.
  - reflexivity.
  - change (8 * Z.of_N 4) with 32. lia.
  - change (Z.of_N 4) with 4. lia. }
rewrite Z.add_0_r in V0.
assert (HKr : forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_QUITTING <= a < A_G_QUITTING + 4) -> ~ (F + 40 <= a < F + 56) ->
  rdW Wc memk a = rdW Wc memc a).
{ intros a Ha H1 H2.
  apply (kept_of_frame (segs := SEGS) E (ss_mem ss_sm3) (w_H Wc) memc memk
    (fun x => A_G_QUITTING <= x < A_G_QUITTING + 4 \/ F + 40 <= x < F + 56) HFr); [| exact Ha | intros [Hx | Hx]; auto].
  intros b wlo whi x Hin Hx. unfold ss_sm3, sm3_regions, obj8_region in Hin.
  cbn [ss_mem windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
  destruct Hin as [Hb | [Hb | [Hb | []]]]; injection Hb as Hb1 Hb2 Hb3; subst b wlo whi; cbn [base_val] in Hx.
  - lia.
  - rewrite E32, unsigned_lit_small in Hx by (unfold A_G_QUITTING; lia). left; lia.
  - rewrite E21, unsigned_lit_small in Hx by lia. right; lia. }
(* the recorder at the call *)
assert (HREPk : rec_repA B lyc Sc (rdW Wc memk) R O).
{ eapply (rec_repA_kept B); [exact HREPc | exact HinOc |].
  intros a Ha. apply HKr.
  - destruct Ha as [Ha | [Ha | Ha]]; [unfold A_G_REC, REC_SIZE in Ha; lia | unfold A_REC_SPILL, SC_SIZE in Ha; lia |].
    destruct (inFP_ablocks_fp_inv _ _ Ha) as (p & m & Hpm & Hpa). destruct (HOb p m Hpm) as (_ & H4096 & Hpc & _). lia.
  - destruct Ha as [Ha | [Ha | Ha]]; [unfold A_G_REC, REC_SIZE, A_G_QUITTING in *; lia | unfold A_REC_SPILL, SC_SIZE, A_G_QUITTING in *; lia |].
    destruct (inFP_ablocks_fp_inv _ _ Ha) as (p & m & Hpm & Hpa). destruct (HOb p m Hpm) as (_ & _ & _ & _ & Himg & _).
    unfold off_img, A_G_QUITTING in *. lia.
  - destruct Ha as [Ha | [Ha | Ha]]; [unfold A_G_REC, REC_SIZE, off_img in *; lia | unfold A_REC_SPILL, SC_SIZE, off_img in *; lia |].
    destruct (inFP_ablocks_fp_inv _ _ Ha) as (p & m & Hpm & Hpa). destruct (HOb p m Hpm) as (_ & _ & _ & _ & _ & HdF & _).
    unfold zdisjoint in HdF; cbn [fst snd] in HdF. lia. }
(* rec_clear's premises at the call *)
assert (HRODk : arodata_okP SEGS RLO RHI B (rdW Wc memk)).
{ eapply (arodata_ok_journalP SEGS RLO RHI RELRO_IMG); [exact HJ | | exact HROD].
  intros a Hro Ha. unfold FP in Ha. apply inFP_app_inv in Ha as [Ha | Ha]; [| exact (CMD_PG_NOT_RO a Ha Hro)].
  destruct (inFP_ablocks_fp_inv _ _ Ha) as (p & m & Hpm & Hpa).
  apply (blk_img SEGS B LAWS ly S W mem md p m a HAR0 (HinO _ Hpm) Hpa).
  destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hr)]. }
assert (Hev1 : st_nev Sc + EV_REC_CLEAR R <= EV_MAX).
{ pose proof (ev_vr_nonneg (RecModel.rec_clear R) D). unfold EV_SEND_MESSAGE in Hev. lia. }
assert (HMO1 : mo_ok MT Sc (XM_REC_CLEAR MT R)).
{ pose proof (ev_args_nonneg R) as Ha. pose proof (mo_free_nonneg MT MTL) as Hf.
  pose proof (mo_malloc_nonneg MT MTL VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as Hm.
  pose proof (mo_malloc_mono MT MTL (Z.max n 1) 8192 ltac:(lia)) as Hmm.
  pose proof (ev_vr_nonneg (RecModel.rec_clear R) D) as Hv.
  apply (mok_station MT S Sc (XM_SEND_MESSAGE MT R D) (mo_malloc MT (Z.max n 1)) (XM_REC_CLEAR MT R) MTL HMOK MOLE).
  - unfold XM_REC_CLEAR. apply Z.mul_nonneg_nonneg; lia.
  - unfold XM_SEND_MESSAGE, XM_VERBS_RECEIVE.
    assert (0 <= ev_vr (RecModel.rec_clear R) D * (mo_malloc MT VERBS_RECEIVE_REQ + mo_free MT))
    by (apply Z.mul_nonneg_nonneg; lia). lia. }
(* the call step's premises *)
pose proof (sm_regs_core_pres _ _ _ _ _ _ RC HPRc) as (K2 & K3 & K4 & K8 & K9 & _).
set (sp1 := sm_sp1 (spZ regs)) in *.
set (o := sp1 - spZ regs).
assert (Hspc : spZ regsc = spZ regs + o) by (unfold spZ at 1; rewrite K2; unfold w64; rewrite unsigned_lit_small by lia; unfold o; lia).
assert (Ho16 : o mod 16 = 0) by (unfold o; rewrite Zminus_mod, Hs16, Hal16; reflexivity).
assert (HRSTK : 0 <= REC_CLEAR_STK) by (vm_compute; discriminate).
assert (HRSTK2 : REC_CLEAR_STK - o <= SEND_MESSAGE_STK) by (unfold SEND_MESSAGE_STK, o; lia).
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PI := PI)) as HBLO.
assert (Hraw4 : 4096 <= bv_unsigned (getr regsc 1)) by (rewrite Rra, unsigned_lit_small by lia; lia).
assert (Hrawok : YK0s.ret_ok (getr regsc 1)) by (rewrite Rra; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (HCHk : achain lyc (rdW Wc memk) (spZ regs + o) (s0Z regsc) ch1).
{ replace (spZ regs + o) with sp1 by (unfold o; lia).
  replace (s0Z regsc) with (spZ regs) by (unfold s0Z, spZ; rewrite K8; reflexivity).
  apply (achain_kept lyc (rdW Wc memc) (rdW Wc memk) sp1 (spZ regs) ch1 alloc_ceiling HCH).
  - lia.
  - destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & L9 & _). rewrite L9. lia.
  - intros a Ha. apply HKr; [lia | unfold A_G_QUITTING; lia | lia]. }
(* (4) rec_clear through the kit's call step for a callee that writes a program static (PaCallPg.v cl_callS_pg) *)
eapply SRr_bind.
{ apply (cl_callS_pg B LAWS Wc regsc memk (Z_to_bv 64 (BASE + AF_rec_clear)) SEND_MESSAGE_STK (spZ regs) FP ly S W mem md
    [(1, fpos)] lyc Sc mdk k REC_CLEAR_STK FP1 (EV_REC_CLEAR R) o (getr regsc 1) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 => exists (O' Dfr : list (Z * Z)),
      rec_repA B ly2 S2 (rdW W2 mem2) (RecModel.rec_clear R) O' /\ (forall pn, In pn O' -> In pn O) /\
      (forall pn, In pn Dfr <-> In pn O /\ ~ In pn O') /\ Permutation (ablocks B lyc Sc) (ablocks B ly2 S2 ++ Dfr) /\
      blocks_bytes S2 <= blocks_bytes Sc + LIVE_REC_CLEAR /\ mo_le MT Sc S2 (XM_REC_CLEAR MT R))
    HJ Hspc Ho16 ltac:(unfold o; lia) HRSTK HRSTK2 ltac:(rewrite K3; exact Hgp) ltac:(rewrite K4; exact Htp) eq_refl
    Hrawok Hraw4 HCHk).
  - intros HPRE1. eapply SRr_mono;
    [exact (RCL fx lyc Sc Wc regsc memk mdk ch1 R O HPRE1 HRODk HREPk Hcalls Hev1 HMO1) |].
    intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & HP2 & HQ).
    exists ly2, S2, regs2, mem2, md2. exact (conj Ec (conj HJ2 (conj HP2 HQ))).
  - intros a Ha. left. unfold FP1 in Ha. apply inFP_cons in Ha as [Ha | Ha].
    + split; [unfold FP; apply inFP_app_r, HPG1; exact Ha |]. right.
      split; [apply G_REC_PROG; exact Ha | exact (proj1 (cmd_prog_unowned a (HPG1 a Ha)))].
    + split; [unfold FP; apply inFP_app_l; exact Ha |]. left.
      destruct (inFP_ablocks_fp_inv _ _ Ha) as (p & m & Hpm & Hpa). exists p, m. split; [exact (HinOc _ Hpm) | exact Hpa]. }
(* (5) rec_clear's return 0x86c70: the next point's statement *)
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2c & HP2 &
  (O' & Dfr & HREP2 & HINC & HDfr & HPERM2 & HBB2 & HMO2)).
pose proof HJ2c as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & Hfrs2 & _).
assert (HP12 : aregs_preserved regs1 regs2) by (exact (aregs_preserved_trans _ _ _ HPRc HP2)).
set (O1 := List.filter (fun x => negb (zz_inb Dfr x)) O).
assert (HPERM1 : Permutation (ablocks B ly2 S2) (O1 ++ (res, Z.max n 1) :: rest)).
{ apply (sm3_perm (ablocks B ly S) _ O O' Dfr rest (res, Z.max n 1)); [rewrite <- Eab; exact HND | exact HPerm |
  rewrite <- Eab; exact HPERM2 | exact HDfr]. }
assert (HrS2 : In (res, Z.max n 1) (ablocks B ly2 S2))
by (apply (Permutation_in _ (Permutation_sym HPERM1)); apply in_or_app; right; left; reflexivity).
(* what rec_clear keeps: its own frame window lies below sp1, its footprint is g_rec and O's blocks *)
assert (HKF : forall a, F <= a < F + 128 -> rdW W2 mem2 a = rdW Wc memk a).
{ intros a Ha. apply (G4 1 fpos a Hfin).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFc. change (fs_frame_bytes 1) with 128. lia.
  - apply HnFP1; [unfold off_img, A_G_REC, REC_SIZE in *; lia |].
    intros p m Hpm Hpa. destruct (HOb p m Hpm) as (_ & _ & _ & _ & _ & HdF & _). unfold zdisjoint in HdF; cbn [fst snd] in HdF. lia. }
assert (HKS : forall i, 0 <= i < 16 -> rdW W2 mem2 (shadow_addr F + i) = rdW Wc memk (shadow_addr F + i)).
{ intros i Hi. apply (G4 1 fpos _ Hfin).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFc. change (fs_frame_bytes 1 / 8) with 16. lia.
  - apply HnFP1; [unfold shadow_addr, SHADOW_OFF, A_G_REC, REC_SIZE; lia |].
    intros p m Hpm Hpa. destruct (HOb p m Hpm) as (_ & _ & _ & Hpapp & _).
    unfold in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kLowMemEnd in *. lia. }
assert (HKs : forall a, spZ regs - 88 <= a < spZ regs -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. transitivity (rdW Wc memk a).
  - apply G1; [lia | unfold o; lia |].
    apply HnFP1; [unfold A_G_REC, REC_SIZE; lia |]. intros p m Hpm Hpa. destruct (HOb p m Hpm) as (_ & _ & Hpc & _). lia.
  - apply HKr; [lia | unfold A_G_QUITTING; lia | lia]. }
assert (HKb : forall i, 0 <= i < Z.max n 1 -> rdW W2 mem2 (res + i) = rdW Wc memc (res + i)).
{ intros i Hi. transitivity (rdW Wc memk (res + i)).
  - apply (G2 res (Z.max n 1) i Hrin HrS2); [rewrite Hrq; lia |].
    apply HnFP1; [unfold off_img, A_G_REC, REC_SIZE in *; lia |].
    intros p m Hpm Hpa. destruct (HOb p m Hpm) as (_ & _ & _ & _ & _ & _ & Hdr). unfold zdisjoint in Hdr; cbn [fst snd] in Hdr. lia.
  - apply HKr; [lia | unfold off_img, A_G_QUITTING in *; lia | unfold zdisjoint in HrF; cbn [fst snd] in HrF; lia]. }
assert (HKq : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> rdW W2 mem2 a = rdW Wc memk a).
{ intros a Ha. destruct (cmd_prog_unowned a (HPG3 a Ha)) as (Hi & Ho & He). apply G3; [exact Hi | exact Ho | exact He |].
  apply fp_spares_closed; [exact HFP1c |]. apply HnFP1; [unfold A_G_REC, REC_SIZE, A_G_QUITTING in *; lia |].
  intros p m Hpm Hpa. destruct (HOb p m Hpm) as (_ & _ & _ & _ & Himg & _). unfold off_img, A_G_QUITTING in *. lia. }
rewrite Rra.
apply (P3 ly S W regs mem md ch src n D R O rest ly2 S2 W2 regs2 mem2 md2 (k + EV_REC_CLEAR R) fpos res O1).
- exact CX.
- split; [exact HJ2 | rewrite Hfrs2; reflexivity].
- lia.
- exact (sm_regs_core_pres _ _ _ _ _ _ RC HP12).
- exact (eq_trans (HP12 21 ltac:(unfold acallee_saved; lia)) R21).
- exact (eq_trans (HP12 22 ltac:(unfold acallee_saved; lia)) R22).
- intros o0 r0 Hin. pose proof (SAV o0 r0 Hin) as Hv.
  assert (Ho0 : -88 <= o0 <= -8) by (cbn in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]); destruct Hin).
  eapply val_mem_kept; [|exact Hv]. intros j0 Hj0. change (Z.of_nat 8) with 8 in Hj0. apply HKs. lia.
- destruct FRM as (V120 & V32 & VS4 & VS5 & VS6).
  split; [eapply val_mem_kept; [|exact V120]; intros j0 Hj0; change (Z.of_nat 8) with 8 in Hj0;
    rewrite HKF by lia; apply HKr; [lia | unfold off_img, A_G_QUITTING in *; lia | lia] |].
  split; [eapply val_mem_kept; [|exact V32]; intros j0 Hj0; change (Z.of_nat 4) with 4 in Hj0;
    rewrite HKF by lia; apply HKr; [lia | unfold off_img, A_G_QUITTING in *; lia | lia] |].
  assert (HSF : forall j, 0 <= j < 16 -> rdW W2 mem2 (SB_F F + j) = rdW Wc memc (SB_F F + j)).
  { intros j Hj. replace (SB_F F + j) with (shadow_addr F + j) by (unfold SB_F, shadow_addr, SB, SHADOW_OFF; lia).
    rewrite HKS by lia. apply HKr; unfold in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kLowMemEnd, A_G_QUITTING in *; lia. }
  split; [|split]; [eapply val_mem_kept; [|exact VS4] | eapply val_mem_kept; [|exact VS5] | eapply val_mem_kept; [|exact VS6]];
  intros j0 Hj0; change (Z.of_nat 1) with 1 in Hj0; rewrite <- Z.add_assoc; apply HSF; lia.
- eapply val_mem_kept; [|exact V40]. intros j0 Hj0. change (Z.of_nat 8) with 8 in Hj0. apply HKF. lia.
- eapply val_mem_kept; [|exact V48]. intros j0 Hj0. change (Z.of_nat 8) with 8 in Hj0. apply HKF. lia.
- exact Hres.
- exact Hnin.
- exact HPERM1.
- intros x Hx. exact (proj1 (proj1 (List.filter_In _ _ _) Hx)).
- intros H. apply HrnO. exact (proj1 (proj1 (List.filter_In _ _ _) H)).
- apply (abytes_atR_kept_r (rdW Wc memc)); [|exact BYT].
  intros x Hx. rewrite HlenD in Hx. replace x with (res + (x - res)) by lia. apply HKb. lia.
- destruct HREP2 as (Q & HA & HO). unfold rec_repA. exists Q. split; [exact HA |].
  intros pn. rewrite <- (HO pn). exact (sm3_O1_iff O O' Dfr HINC HDfr pn).
- apply (aval_mem_kept_r (rdW Wc memk)); [| exact (aval_of_val_mem _ _ _ _ _ _ V0)].
  intros x Hx. change (Z.of_nat 4) with 4 in Hx. apply HKq. lia.
- (* the live bytes: the copy's block on top of the entry's, and rec_clear adds none *)
  assert (Eb : blocks_bytes Sc = bsum (ablocks B lyc Sc)) by apply blocks_bytes_bsum.
  assert (Eb0 : blocks_bytes S = bsum (ablocks B ly S)) by apply blocks_bytes_bsum.
  rewrite Eab, bsum_app, <- Eb0 in Eb. unfold bsum in Eb. cbn [fold_right snd] in Eb.
  unfold LIVE_REC_CLEAR in HBB2. lia.
- apply (mle_weaken MT S S2 (mo_malloc MT (Z.max n 1) + XM_REC_CLEAR MT R) _ MTL (mle_station MT S Sc S2 _ _ MTL MOLE HMO2)).
  pose proof (mo_malloc_mono MT MTL (Z.max n 1) 8192 ltac:(lia)). lia.
Qed.

End e.
End f.
End d.
