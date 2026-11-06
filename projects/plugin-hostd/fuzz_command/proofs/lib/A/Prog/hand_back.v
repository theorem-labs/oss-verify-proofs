(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of rec_shape_of (plugin-hostd/fuzz_command, 0x891ec, 69 instructions),
   in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (the entry state with the GOT word and the shadow cell)
   and A/ACh5.v (the composition of the segments into the contract): the prologue up to the loop head (0x891ec ..
   0x89254), then the loop of lib/A/Prog/rec_shape_of_s.v for the 28 rows, from the image's read-only table g_shapes
   and the literals it points to (lib/A/Prog/CmdRo.v). The per-binary facts are the lemmas of CmdRecFacts' groups in
   lib/A/Prog/CmdRecBase.v, CmdRecRo.v and CmdRecImg.v, under the walk hypotheses
   (with cgif's names). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_shape_of.v, with its module paths and module names changed; 1105 of its 1157 lines of code are new or changed and 266 lines of the source are left out. *)
(* The ASan walk of hand_back (plugin-hostd/fuzz_command): thand_back_spec_holds proves `thand_back_spec B MT`
   exactly as hand_back_c.v states it.

   Shape: cgif_file_fuzzer's cgif_close walk (A/ACh1.v..ACh5.v, AChc.v): the verified symbolic executor over
   the position-abstract listing (CmdPaLib's paj_run_shc / PaLibF's SRr_run_pi_AJ), the two xstrdup calls
   through PaCall's plain cl_callS (xstrdup's footprint is empty), and the free through the 04 allocator rules
   (afree04_sub when the answer is set, afree_null04_sub when it is 0).

   Statement passes 4, 4b and 5: xstrdup's contract and the free entries hold at every FP
   state (forall fx0); no callee changes the FP state (xstrdup's post is apost_base), so the walk uses all three at
   the entry's fx and the post stays apost_base. Pass 5 removed astack_pres: the walk no longer derives it for
   xstrdup; the frame chains at the three calls come from achain_low (s0 = the text, below alloc_ceiling) and from
   afn_pre's chain kept by achain_kept (the tail call, entry s0).

   hand_back (recorder.c:243-248, 18 instructions at BASE + AF_hand_back = 0x8a478, no inline check, no loop,
   no side-stack frame) loads g_rec.answer (the listing's A_OBJ 57 = 0x5e3ad0 = g_rec + 912), frees it through
   the free wrapper, calls xstrdup(text), stores the copy into g_rec.answer, and tail-calls xstrdup(text) again
   for the caller's copy.

   What the walk needs beyond cgif's shape: the store `sd a0,1608(s1)` addresses the answer word as
   SOff (A_HI 122) 1608 while the load names it A_OBJ 57, so the symbolic state carries the single alias
   (SOff (A_HI 122) 1608, SOff (A_OBJ 57) 0), sound by VHIS + VOBJS (0x5e3488 + 1608 = 0x5e3ad0). The journal
   admits the store because the answer word is in the footprint and in as_prog_static B (the core's
   awr_prog_or_caller, YCbq.v:503; HPROG below, from the record's ts_prog).

   Per-binary facts are named Section hypotheses under cgif's names, the
   rest comes from CmdRecFacts.v: IMG (cmd_img_facts) gives the program statics in the image (cif_prog_img), the
   read-only range in the image and apart from the statics (RRO / RPG) and below the sink's overflow head
   (cif_ro_below_ofl, CmdBase.v's ro_below_ofl); PRW (the core's prog_rw) gives the answer word's write window
   (PROG_WRITABLE). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YI00 YI04 YI16 YN3v YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdAddr CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaLibF PaLibG PaLibH PaDenot PaCall PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c hand_back_c.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the statement's footprint filters the recorder's blocks with a boolean predicate through stdpp's filter;
   these are the two directions of its membership, proved here so the walk needs no stdpp list import *)
Lemma hb_in_filter : forall (f : Z * Z -> bool) (pn : Z * Z) (l : list (Z * Z)),
In pn l -> f pn = true -> In pn (filter (fun q : Z * Z => f q) l).
Proof.
intros f pn l Hin Hf. induction l as [|q l IH]; [destruct Hin|].
cbn [In] in Hin. cbn. destruct (decide (f q)) as [Hq|Hq].
- cbn [In]. destruct Hin as [Heq|Hin]; [left; exact Heq | right; exact (IH Hin)].
- destruct Hin as [Heq|Hin]; [exfalso; apply Hq; subst q; rewrite Hf; exact I | exact (IH Hin)].
Qed.
Lemma hb_filter_in : forall (f : Z * Z -> bool) (pn : Z * Z) (l : list (Z * Z)),
In pn (filter (fun q : Z * Z => f q) l) -> In pn l /\ f pn = true.
Proof.
intros f pn l. induction l as [|q l IH]; [intros []|].
cbn. destruct (decide (f q)) as [Hq|Hq].
- intros [Heq|Hin].
  + split; [left; exact Heq|]. subst q. destruct (f pn) eqn:Ef; [reflexivity | destruct Hq].
  + destruct (IH Hin) as [H1 H2]. split; [right; exact H1 | exact H2].
- intros Hin. destruct (IH Hin) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

(* the answer word of g_rec, as the listing names it on each side of the walk *)
Definition HB_ANS_OBJ : nat := 57.
Definition HB_ANS_HI : nat := 122.
Definition kOld : nat := 32%nat.
Definition hb_ans : YP09.region :=
YP09.mkRegion (Some (A_OBJ HB_ANS_OBJ)) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff kOld 0))].
Definition hb_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [].
Definition hb_regions : smem := [hb_stack; hb_ans].
Definition hb_facts : facts :=
mkFacts [] [] [(SOff (A_HI HB_ANS_HI) 1608, SOff (A_OBJ HB_ANS_OBJ) 0)].
Definition ss_hb : sstate := mkSS AF_hand_back sr_atoms hb_regions None hb_facts.

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
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* cgif's per-binary walk facts, with cgif's names *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
(* the listing's atoms against the image's addresses (CmdObj.v) *)
Hypothesis VOBJS : cmd_val_objs.
Hypothesis VHIS : cmd_val_his.
Hypothesis SIGP : cmd_sig_prog.
(* the per-binary record: the program's own writable statics come from its ts_prog (AF0m.v:4898) *)
Hypothesis HB : CmdBSyms B.
(* the image facts (CmdRecBase.v) and the program statics' write window (the core's prog_rw, YCbq.v) *)
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis PRW : prog_rw SEGS B.
(* the read-only range lies below the sink's overflow head, as cgif's walks take it (A/ACj5.v:35) *)
#[local] Instance RO : ro_below_ofl SEGS RLO RHI := cif_ro_below_ofl _ _ IMG.
(* the statement's own Section hypotheses (hand_back_c.v:57-59), at every FP state *)
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE_NULL4 : forall fx0 : YK11.FPState, @afree_null04_rule fx0 rc SK SEGS B MT.

Let HBfree := pal_free B TL.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* this port's one name, for every walk, for the program-static side condition of awr_byte (YCbq.v:501) *)
Lemma HPROG : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof.
intros a Ha. rewrite (ts_prog _ HB). unfold cmd_PG in Ha.
apply (proj1 (inFP_cons _ _ _ a)) in Ha as [Ha | Ha]; [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold A_G_REC in *; lia|].
apply (proj1 (inFP_cons _ _ _ a)) in Ha as [Ha | Ha];
[apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold A_REC_SPILL in *; lia|].
apply (proj1 (inFP_cons _ _ _ a)) in Ha as [Ha | Ha];
[apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold A_G_QUITTING in *; lia|].
destruct Ha as (r & [] & _).
Qed.

Lemma hb_val_ans : VAL (A_OBJ HB_ANS_OBJ) = A_G_REC + OFF_ANSWER.
Proof. rewrite (VOBJS HB_ANS_OBJ ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma hb_val_hi : VAL (A_HI HB_ANS_HI) = A_G_REC + OFF_ANSWER - 1608.
Proof. rewrite (VHIS HB_ANS_HI ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma hb_ans_range : 0x10000 <= A_G_REC + OFF_ANSWER /\ A_G_REC + OFF_ANSWER + 8 <= 0x606000.
Proof. vm_compute. split; intros H; discriminate H. Qed.

Lemma hb_inFP_ans : forall a, A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8 -> inFP cmd_PG a.
Proof.
intros a Ha. apply (proj2 (inFP_cons _ _ _ a)). left. unfold A_G_REC, OFF_ANSWER in *. lia.
Qed.
Lemma hb_prog_ans : forall a, A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8 ->
Exists (in_zr a) (as_prog_static B).
Proof. intros a Ha. apply HPROG. apply hb_inFP_ans. exact Ha. Qed.

Lemma hb_alias_ok : forall E, img_env VAL A_LIM E ->
sv_denot E (SOff (A_HI HB_ANS_HI) 1608) = sv_denot E (SOff (A_OBJ HB_ANS_OBJ) 0).
Proof.
intros E HE. cbn [sv_denot].
rewrite (img_env_atomP (PI := PI) E (A_HI HB_ANS_HI) HE ltac:(unfold A_HI, A_TEXT, A_LIM, HB_ANS_HI; lia)).
rewrite (img_env_atomP (PI := PI) E (A_OBJ HB_ANS_OBJ) HE ltac:(unfold A_OBJ, A_TEXT, A_LIM, HB_ANS_OBJ; lia)).
rewrite hb_val_ans, hb_val_hi. f_equal; lia.
Qed.

(* the listing's call target for xstrdup is its entry in the statement's form *)
Lemma hb_sig_xstrdup : SIGMA CS_xstrdup = BASE + AF_xstrdup.
Proof.
rewrite (SIGP CS_xstrdup ltac:(unfold cmd_prog_syms; cbn [In]; repeat (try (now left); right))).
try (f_equal; vm_compute; reflexivity).
Qed.

Lemma hb_val_mem : forall H mem a n v,
aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as Hv. apply (f_equal (Z_to_bv 8)) in Hv. rewrite Z_to_bv_bv_unsigned in Hv.
rewrite Hv. reflexivity.
Qed.

Lemma hb_stk_val : HAND_BACK_STK = 16448.
Proof. vm_compute. reflexivity. Qed.

(* the symbolic state the walk starts from: the own 32-byte frame, and the answer word of g_rec, whose value
   the walk carries in the extra atom kOld *)
Lemma hb_entry : forall ly S W (regs : bvmap 5 word) mem md ch (old : Z),
afn_pre SEGS B HAND_BACK_STK ly S W regs mem md ch ->
0 <= old < 2 ^ 64 ->
aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 old ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 old])) ss_hb
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_hand_back)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch old HPRE Hold Hval.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof hb_stk_val as HBS.
set (E := Eimg (Ereg regs [Z_to_bv 64 old])) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (EkO : ew E kOld = Z_to_bv 64 old)
by (subst E; rewrite Eimg_low by (unfold A_TEXT, kOld; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Eans : bv_unsigned (ew E (A_OBJ HB_ANS_OBJ)) = A_G_REC + OFF_ANSWER)
by (rewrite (HEI (A_OBJ HB_ANS_OBJ) ltac:(unfold A_OBJ, A_TEXT, A_LIM, HB_ANS_OBJ; lia)); exact hb_val_ans).
(* the same fact with the atom in the form the executor's states carry it *)
assert (Eans' : bv_unsigned (ew E 298%nat) = A_G_REC + OFF_ANSWER)
by (unfold A_OBJ, HB_ANS_OBJ in Eans; exact Eans).
rewrite restrict_mkst_fx. unfold ss_hb. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold hb_regions, hb_stack, hb_ans. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + cbn [base_val]. rewrite Eans. split; [vm_compute; intros Hx; discriminate Hx|].
    split; [vm_compute; intros Hx; discriminate Hx|].
    split.
    * intros o Ho. apply (PROG_WRITABLE SEGS B LAWS HB PRW). apply hb_inFP_ans. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (A_G_REC + OFF_ANSWER) 0 8 (SOff kOld 0) old);
      [cbn [sv_denot]; rewrite EkO, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. change (N.to_nat 8) with 8%nat. apply hb_val_mem. exact Hval.
- apply pairwise_disjoint_of_extents. unfold hb_regions, hb_stack, hb_ans, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Eans, Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hceil Hshi H47 C1 HBS. unfold A_G_REC, OFF_ANSWER. clear. intros. repeat split; lia.
- split; [exact I|]. split; [exact I|]. cbn [hb_facts f_alias alias_ok].
  split; [apply hb_alias_ok; exact HEI | exact I].
Qed.

(* transport of the recorder's fields and strings across a range the call kept *)
Lemma hb_aval_kept_rng : forall (rd rd' : reader) a n v (lo hi : Z),
(forall b, lo <= b < hi -> rd' b = rd b) -> lo <= a -> a + Z.of_nat n <= hi -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v lo hi HK Hlo Hhi H k Hk. rewrite (HK (a + Z.of_nat k) ltac:(lia)). exact (H k Hk). Qed.
Lemma hb_abytes_kept_rng : forall (rd rd' : reader) p l (lo hi : Z),
(forall b, lo <= b < hi -> rd' b = rd b) -> lo <= p -> p + Z.of_nat (length l) <= hi ->
abytes_atR rd p l -> abytes_atR rd' p l.
Proof. intros rd rd' p l lo hi HK Hlo Hhi H i Hi. rewrite (HK (p + Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.

Lemma hb_astr_kept_rng : forall (rd rd' : reader) p s (lo hi : Z),
(forall b, lo <= b < hi -> rd' b = rd b) -> lo <= p -> p + Z.of_nat (length s) + 1 <= hi ->
astr_atR rd p s -> astr_atR rd' p s.
Proof.
intros rd rd' p s lo hi HK Hlo Hhi [Hb Hnz]. split; [|exact Hnz]. intros i Hi.
rewrite length_app in Hi. cbn [length] in Hi.
rewrite (HK (p + Z.of_nat i) ltac:(lia)). exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.

Lemma hb_le_byte_range : forall z w k, 0 <= le_byte z w k < 256.
Proof. intros z w k. unfold le_byte. apply Z.mod_pos_bound. lia. Qed.

Lemma hb_val_mem_rev : forall H mem a n v,
val_mem SEGS (mrestrict H mem) a n v -> aval_mem (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. apply hb_le_byte_range.
Qed.

Lemma hb_aval_det : forall H mem a v1 v2, 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 ->
aval_mem (aview SEGS H mem) a 8 v1 -> aval_mem (aview SEGS H mem) a 8 v2 -> v1 = v2.
Proof.
intros H mem a v1 v2 Hv1 Hv2 H1 H2.
pose proof (rdword_of_val_mem SEGS H mem a v1 (hb_val_mem H mem a 8 v1 H1) Hv1) as E1.
pose proof (rdword_of_val_mem SEGS H mem a v2 (hb_val_mem H mem a 8 v2 H2) Hv2) as E2.
rewrite E1 in E2. injection E2 as E2. exact E2.
Qed.

(* no two live blocks start at the same address: the allocator's separation law (al_sep) *)
Lemma hb_two_at : forall ly S W mem md p m1 m2 l1 l2,
AR SEGS B ly S W mem md -> ablocks B ly S = l1 ++ (p, m1) :: l2 -> In (p, m2) (l1 ++ l2) -> False.
Proof.
intros ly S W mem md p m1 m2 l1 l2 HAR Heq Hin.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
assert (Hdec : exists a1 a2 a3, ablocks B ly S = a1 ++ (p, m1) :: a2 ++ (p, m2) :: a3
 \/ ablocks B ly S = a1 ++ (p, m2) :: a2 ++ (p, m1) :: a3).
{ apply in_app_or in Hin as [Hin | Hin]; apply in_split in Hin as (b1 & b2 & Hb).
  - exists b1, b2, l2. right.
    rewrite Heq, Hb, <- app_assoc. reflexivity.
  - exists l1, b1, b2. left. rewrite Heq, Hb. reflexivity. }
assert (Hin1 : In (p, m1) (ablocks B ly S)) by (rewrite Heq; apply in_or_app; right; left; reflexivity).
assert (Hin2 : In (p, m2) (ablocks B ly S)).
{ rewrite Heq. apply in_app_or in Hin as [Hq | Hq]; apply in_or_app; [left; exact Hq | right; right; exact Hq]. }
destruct (al_blocks _ _ LAWS ly S W mem md p m1 HAR Hin1) as (_ & _ & _ & _ & _ & _ & Hm1).
destruct (al_blocks _ _ LAWS ly S W mem md p m2 HAR Hin2) as (_ & _ & _ & _ & _ & _ & Hm2).
pose proof (pairwise_zdisjoint_split _ (p, req_size m1) (p, req_size m2) Hp
(map_split_2 (fun b : Z * Z => (fst b, req_size (snd b))) _ _ _ Hdec)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (req_size_pos m1 ltac:(lia)). pose proof (req_size_pos m2 ltac:(lia)). lia.
Qed.

(* the 8-byte word that holds a byte below an 8-aligned bound ends at or below it *)
Lemma hb_tail_below8 : forall e c, 0 <= e < c -> c mod 8 = 0 -> e - e mod 8 + 8 <= c.
Proof.
intros e c He Hc. assert (Hlt : e / 8 < c / 8) by (apply Z.div_lt_upper_bound; [lia|];
  pose proof (Z_div_mod_eq_full c 8); lia).
pose proof (Z_div_mod_eq_full e 8). pose proof (Z_div_mod_eq_full c 8). lia.
Qed.

(* the shadow byte of an address inside a frame lies in the frame's shadow range *)
Lemma hb_shadow_in_frame : forall fa fs p n x,
fa mod 8 = 0 -> fs = 8 * (fs / 8) -> fa <= p -> p + n <= fa + fs -> p <= x < p + n ->
shadow_addr fa <= SHADOW_OFF + x / 8 < shadow_addr fa + fs / 8.
Proof.
intros fa fs p n x Hal Hfs Hp Hpn Hx. pose proof (Z_div_mod_eq_full fa 8) as Hfa. rewrite Hal, Z.add_0_r in Hfa.
assert (Hle : fa / 8 <= x / 8) by (apply Z.div_le_mono; lia).
assert (Hlt : x / 8 < fa / 8 + fs / 8) by (apply Z.div_lt_upper_bound; lia).
unfold shadow_addr. lia.
Qed.

(* every block the recorder owns is a live block: RecInv's rep_at_blocks over arep_at *)
Lemma hb_call_in : forall bl rd a c P pn, acall_at bl rd a c P -> In pn P -> In pn bl.
Proof.
intros bl rd a c P pn (_ & Hc6 & Hlen & _ & _ & _ & Hk) Hin.
destruct (In_nth_error _ _ Hin) as [k Ek].
assert (Hk' : (k < length (snd c))%nat) by (rewrite <- Hlen; apply nth_error_Some; rewrite Ek; discriminate).
destruct (nth_error (snd c) k) as [sv|] eqn:Es; [|exfalso; apply nth_error_None in Es; lia].
destruct (Hk k sv pn Es Ek) as (_ & _ & Hb & _). exact Hb.
Qed.

Lemma hb_rest_lay : forall Q pn,
In pn (concat (l_calls Q) ++ l_spill Q ++ oblk (l_reply Q)) -> In pn (lay_blocks Q).
Proof.
intros Q pn Hin. unfold lay_blocks.
apply in_app_or in Hin as [Hc | Hin]; [apply in_or_app; left; exact Hc|].
apply in_app_or in Hin as [Hs | Hr]; apply in_or_app; right;
[apply in_or_app; left; exact Hs | apply in_or_app; right; apply in_or_app; right; exact Hr].
Qed.

Lemma hb_nodup_del : forall (L1 L2 L3 : list Z) (a : Z),
NoDup (L1 ++ L2 ++ a :: L3) -> NoDup (L1 ++ L2 ++ L3).
Proof.
intros L1 L2 L3 a H. apply NoDup_ListNoDup. apply NoDup_ListNoDup in H.
rewrite app_assoc in H. rewrite app_assoc. exact (NoDup_remove_1 _ _ _ H).
Qed.

Lemma hb_nodup_ins : forall (L1 L2 L3 : list Z) (b : Z),
NoDup (L1 ++ L2 ++ L3) -> ~ In b (L1 ++ L2 ++ L3) -> NoDup (L1 ++ L2 ++ b :: L3).
Proof.
intros L1 L2 L3 b Hnd Hni. apply NoDup_ListNoDup. apply NoDup_ListNoDup in Hnd.
rewrite app_assoc. apply (Permutation_NoDup (l := b :: ((L1 ++ L2) ++ L3))).
- apply Permutation_middle.
- constructor; [rewrite <- app_assoc; exact Hni | rewrite <- app_assoc; exact Hnd].
Qed.

Lemma hb_lay_rest : forall Q pn, In pn (lay_blocks Q) ->
In pn (concat (l_calls Q) ++ l_spill Q ++ oblk (l_reply Q)) \/ l_answer Q = Some pn.
Proof.
intros Q pn Hin. unfold lay_blocks in Hin.
apply in_app_or in Hin as [Hc | Hin]; [left; apply in_or_app; left; exact Hc|].
apply in_app_or in Hin as [Hs | Hin]; [left; apply in_or_app; right; apply in_or_app; left; exact Hs|].
apply in_app_or in Hin as [Ha | Hr];
[|left; apply in_or_app; right; apply in_or_app; right; exact Hr].
right. destruct (l_answer Q) as [q|]; cbn [oblk] in Ha; [destruct Ha as [<- | []]; reflexivity | destruct Ha].
Qed.

Lemma hb_lay_in : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> In pn bl.
Proof.
intros bl rd gr sc R Q pn (_ & _ & _ & HC & HA & HP & _ & _) Hin.
pose proof HC as (Hlen16 & Hlenq & _ & Hcalls & Hspill & _).
unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_concat in Hin as (P & HP0 & Hpn).
  destruct (In_nth_error _ _ HP0) as [i Ei].
  assert (Hi : (i < length (r_calls R))%nat)
  by (rewrite <- Hlenq; apply nth_error_Some; rewrite Ei; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|exfalso; apply nth_error_None in Ec; lia].
  exact (hb_call_in bl rd _ c P pn (proj1 (Hcalls i c P Ec Ei)) Hpn).
- apply in_app_or in Hin as [Hin | Hin]; [exact (hb_call_in bl rd sc (r_spill R) (l_spill Q) pn Hspill Hin)|].
  apply in_app_or in Hin as [Hin | Hin].
  + revert HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [q|]; cbn [oblk] in Hin;
    try (destruct Hin; fail); try (intros HA; destruct HA; fail).
    intros (_ & _ & Hb & _). destruct Hin as [<- | []]. exact Hb.
  + revert HP. destruct (r_reply R) as [y|]; destruct (l_reply Q) as [q|]; cbn [oblk] in Hin;
    try (destruct Hin; fail); try (intros HP; destruct HP; fail).
    intros (_ & _ & _ & _ & Hb & _). destruct Hin as [<- | []]. exact Hb.
Qed.

Theorem thand_back_spec_holds : thand_back_spec B MT.
Proof.
pose proof (RRO SEGS B LAWS HB IMG) as RO_IMG. pose proof (RPG SEGS B LAWS HB IMG) as RO_PG.
unfold thand_back_spec.
intros ly S W regs mem md ch s old x R O HPRE HROD H10 Hsrng Hstr Hlen Hobj HREC Hans OLD_RANGE Hev Hlive HMOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof hb_stk_val as HBS.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
set (OLD := old mod 2 ^ 64) in *.
assert (HOLD : 0 <= OLD < 2 ^ 64) by (unfold OLD; apply Z.mod_pos_bound; lia).
assert (HOeq : OLD = old) by (unfold OLD; apply Z.mod_small; exact OLD_RANGE).
assert (HansO : aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 OLD).
{ intros k Hk. rewrite (Hans k Hk). f_equal. unfold OLD, le_byte. rewrite Zmod_mod. reflexivity. }
destruct HREC as (Q & HAREP & HOQ).
assert (HObl : forall pn, In pn O -> In pn (ablocks B ly S))
by (intros pn Hpn; exact (hb_lay_in _ _ _ _ _ _ _ HAREP (proj1 (HOQ pn) Hpn))).
assert (HROFP : forall a, in_roP SEGS RLO RHI a ->
  ~ inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8)
          :: ablocks_fp (filter (fun pn => fst pn =? old) O)) a).
{ intros a Hro Hin. apply (proj1 (inFP_cons _ _ _ a)) in Hin as [Hin | Hin].
  - exact (RO_PG a (hb_inFP_ans a Hin) Hro).
  - destruct (inFP_ablocks_fp_inv _ a Hin) as (p & n & Hpn & Hr).
    destruct (hb_filter_in _ _ _ Hpn) as [HinO _].
    pose proof (HObl _ HinO) as Hinb.
    pose proof (blk_off_imgP B ly S W mem md p n HAR Hinb) as Hoff. unfold off_img in Hoff.
    assert (Himg : in_img SEGS a)
    by (destruct Hro as [(sg & Hsg & _ & Hrng) | Hrr]; [exists sg; split; [exact Hsg | exact Hrng] | exact (RO_IMG a Hrr)]).
    pose proof (pa_img_range a Himg) as Hrange.
    destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hinb) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hrq]. cbn [fst snd] in Hr. lia. }
(* nothing of the footprint lies at or above the allocator's ceiling *)
assert (HFPhi : forall a, alloc_ceiling <= a ->
  ~ inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8)
          :: ablocks_fp (filter (fun pn => fst pn =? old) O)) a).
{ intros a Ha Hin. apply (proj1 (inFP_cons _ _ _ a)) in Hin as [Hin | Hin]; [unfold A_G_REC, OFF_ANSWER in Hin; lia|].
  destruct (inFP_ablocks_fp_inv _ a Hin) as (p & n & Hpn & Hr).
  destruct (hb_filter_in _ _ _ Hpn) as [HinO _].
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HObl _ HinO)) as (_ & _ & Hpc & _ & _ & _ & Hn0).
  cbn [fst snd] in Hr. lia. }
pose proof (hb_entry ly S W regs mem md ch OLD HPRE HOLD HansO) as HS.
set (E := Eimg (Ereg regs [Z_to_bv 64 OLD])) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 OLD]) E)
by (unfold E; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall nn (q : bv 5), Z.of_nat nn = bv_unsigned q -> ew E nn = getr regs q)
by (intros nn q Hq; unfold E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (Eans : bv_unsigned (ew E (A_OBJ HB_ANS_OBJ)) = A_G_REC + OFF_ANSWER)
by (rewrite (HEI (A_OBJ HB_ANS_OBJ) ltac:(unfold A_OBJ, A_TEXT, A_LIM, HB_ANS_OBJ; lia)); exact hb_val_ans).
(* the same fact with the atom in the form the executor's states carry it *)
assert (Eans' : bv_unsigned (ew E 298%nat) = A_G_REC + OFF_ANSWER)
by (unfold A_OBJ, HB_ANS_OBJ in Eans; exact Eans).
pose proof (ajournal_init SEGS B HAND_BACK_STK
((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O))
ly S W regs mem md ch HPRE) as HJ.
unfold cfg_at. change (w64 (BASE + AF_hand_back)) with (Z_to_bv 64 (BASE + AF_hand_back)).
paj_run_shc RUNP RUNC HS HJ.
{ intros a Ha. unfold in_wrange, ss_hb, hb_regions, hb_stack, hb_ans in Ha. cbn [ss_mem] in Ha.
  destruct Ha as (r & Hin & Hr). cbn [In] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  - left. rewrite Usp in Hr. lia.
  - right. right. right. right. left. rewrite Eans in Hr.
    split; [apply (proj2 (inFP_cons _ _ _ a)); left; lia|].
    split; [apply hb_prog_ans; lia | apply (cif_prog_img _ _ IMG); apply hb_inFP_ans; lia]. }
(* at the free wrapper: a0 is the old answer, the frame holds ra/s0/s1, s0 is the caller's text *)
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
rewrite HBfree.
destruct Hobj as ((cid & pos & Hfr & Hcid & Hfal & Hfle & Hfhi) & Hs8 & Hsra).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfr) as (Hf4096 & Hfceil & Hfapp).
assert (Hs4096 : 4096 <= s) by lia.
assert (Hsceil : s + (Z.of_nat (length x) + 1) <= alloc_ceiling) by lia.
assert (Hxlen : 0 <= Z.of_nat (length x)) by lia.
assert (HspT : spZ (ms_regs ms) = spZ regs + -32)
by (unfold spZ at 1; rewrite P2, Usp; rewrite unsigned_lit_small by lia; reflexivity).
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact Htp).
assert (P10' : getr (ms_regs ms) 10 = w64 OLD) by (rewrite P10; reflexivity).
assert (Hs0T : s0Z (ms_regs ms) = s)
by (unfold s0Z; rewrite P8, (EE 10%nat 10%bv eq_refl), H10; apply unsigned_lit_small; lia).
assert (HraT : YK0s.ret_ok (Z_to_bv 64 (BASE + 16312)))
by (apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (HchT : chain_pre ly (rdW W (ms_mem ms)) (ms_regs ms) []).
{ eapply (achain_chain_pre ly (rdW W (ms_mem ms)) (spZ regs + -32) s [] (ms_regs ms)).
  - apply achain_low. lia.
  - rewrite HspT. lia.
  - exact Hs0T.
  - unfold raZ. rewrite P1. rewrite unsigned_lit_small by lia. lia. }
assert (Hnev : st_nev S < EV_MAX) by (unfold EV_HAND_BACK, EV_XSTRDUP in Hev; lia).
assert (Hmfree : mo_ok MT S (mo_free MT)).
{ apply (mo_ok_le MT MTL S (mo_free MT) (XM_HAND_BACK MT x) HMOK).
  unfold XM_HAND_BACK, XM_XSTRDUP.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length x) + 1) ltac:(lia)). lia. }
eapply SRr_bind with (R := fun (W1 : world SEGS) (c1 : config) => exists ly1 S1 regs1 mem1 md1,
c1 = mkCfg (mkst regs1 (Z_to_bv 64 (BASE + 16312)) mem1 (seg_rom SEGS)) md1 /\
ajournal SEGS B HAND_BACK_STK (spZ regs)
  ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O))
  ly S W mem md [] ly1 S1 W1 mem1 md1 1 /\
aregs_preserved (ms_regs ms) regs1 /\
(forall pn, In pn (ablocks B ly1 S1) <-> In pn (ablocks B ly S) /\ fst pn <> OLD) /\
frames S1 = frames S /\
blocks_bytes S1 <= blocks_bytes S /\
mo_le MT S S1 (mo_free MT) /\
(exists Ef : Z -> Prop,
 (forall a, Ef a -> exists k, In (OLD, k) (ablocks B ly S) /\ OLD <= a < OLD + req_size k) /\
 acall_kept SEGS B ly S W (ms_mem ms) W1 mem1 (spZ regs + -32 - ASTACK) (spZ regs + -32) Ef)).
{ destruct (Z.eq_dec OLD 0) as [HO0 | HOne].
  - eapply SRr_mono.
    { eapply (afree_null04_sub SEGS B LAWS Hsegs MT (AFREE_NULL4 fx) W (ms_regs ms) (ms_mem ms)
        HAND_BACK_STK (spZ regs) _ ly S W mem md [] ly S _ 0 (-32) (Z_to_bv 64 (BASE + 16312)) [] HJ);
      [ rewrite P10', HO0; reflexivity | exact HspT | reflexivity | lia
      | rewrite HBS; unfold ASTACK; lia | exact P3' | exact P4' | exact P1 | exact HraT
      | exact Hnev | exact HchT | exact Hmfree ]. }
    cbv beta. intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & HP1 & HPerm1 & Hfrs1 & HK1 & MLE1 & _).
    cbv beta. exists ly1, S1, regs1, mem1, md1. split; [reflexivity|]. split; [exact HJ1|]. split; [exact HP1|].
    split.
    { intros pn. split.
      - intros Hin. split; [eapply Permutation_in; [exact HPerm1 | exact Hin]|].
        intros Hf. assert (Hin0 : In pn (ablocks B ly S)) by (eapply Permutation_in; [exact HPerm1 | exact Hin]).
        destruct pn as [pa pk]. cbn [fst] in Hf. subst pa.
        destruct (al_blocks _ _ LAWS ly S W mem md OLD pk HAR Hin0) as (_ & H4096 & _). lia.
      - intros [Hin _]. eapply Permutation_in; [apply Permutation_sym; exact HPerm1 | exact Hin]. }
    split; [exact Hfrs1|].
    split; [rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly S);
            rewrite (bsum_perm _ _ HPerm1); lia|].
    split; [exact MLE1|].
    exists (fun _ : Z => False). split; [intros a Hq; destruct Hq | exact HK1].
  - pose proof HAREP as (Hgr8 & Hsc8 & Hapart & HCALLS & HANS & HREPLY & HSCAL & HOWN).
    destruct (r_answer R) as [t|] eqn:ERA; destruct (l_answer Q) as [[pa pk]|] eqn:ELA; try (exfalso; exact HANS).
    + destruct HANS as (Hva & Hpa0 & Hpain & Hpak & Hstra & Hlent).
      destruct (al_blocks _ _ LAWS ly S W mem md pa pk HAR Hpain) as (_ & Hpa4096 & Hpaceil & _ & _ & _ & Hpkr).
      pose proof (req_size_pos pk ltac:(lia)) as [Hrq1 Hrq2].
      assert (HpaO : pa = OLD) by (apply (hb_aval_det (w_H W) mem (A_G_REC + OFF_ANSWER)); [lia | lia | exact Hva | exact HansO]).
      eapply SRr_mono.
      { eapply (afree04_sub SEGS B LAWS Hsegs MT (AFREE4 fx) W (ms_regs ms) (ms_mem ms)
          HAND_BACK_STK (spZ regs) _ ly S W mem md [] ly S _ 0 pa pk (-32) (Z_to_bv 64 (BASE + 16312)) [] HJ Hpain);
        [ rewrite P10', HpaO; reflexivity | exact HspT | reflexivity | lia
        | rewrite HBS; unfold ASTACK; lia | exact P3' | exact P4' | exact P1 | exact HraT
        | exact Hnev | exact HchT | | exact Hmfree ].
        intros _ i Hi. apply (proj2 (inFP_cons _ _ _ (pa + i))). right.
        apply (inFP_ablocks_fp _ pa pk i); [|exact Hi].
        apply hb_in_filter.
        - apply HOQ. unfold lay_blocks. rewrite ELA.
          apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity.
        - cbn [fst]. apply Z.eqb_eq. rewrite HpaO. exact HOeq. }
      cbv beta. intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & HP1 & (l1 & l2 & Ebl & Ebl2) & Hfrs1 & HK1 & MLE1 & _).
      cbv beta. exists ly1, S1, regs1, mem1, md1. split; [reflexivity|]. split; [exact HJ1|]. split; [exact HP1|].
      split.
      { intros pn. rewrite Ebl2. split.
        - intros Hin. split; [rewrite Ebl; apply in_app_or in Hin as [Hq|Hq]; apply in_or_app;
          [left; exact Hq | right; right; exact Hq]|].
          intros Hf. destruct pn as [pb pm]. cbn [fst] in Hf. rewrite <- HpaO in Hf. subst pb.
          exact (hb_two_at ly S W mem md pa pk pm l1 l2 HAR Ebl Hin).
        - intros [Hin Hf]. rewrite Ebl in Hin. apply in_app_or in Hin as [Hq|Hq]; apply in_or_app; [left; exact Hq|].
          destruct Hq as [Hq|Hq]; [exfalso; rewrite <- Hq in Hf; cbn [fst] in Hf; rewrite HpaO in Hf; exact (Hf eq_refl) | right; exact Hq]. }
      split; [exact Hfrs1|].
      split; [rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly S);
              rewrite Ebl2, Ebl, !bsum_app, bsum_cons; cbn [snd]; lia|].
      split; [exact MLE1|].
      exists (fun a => pa <= a < pa + req_size pk). split; [|exact HK1].
      intros a Ha. exists pk. split; [rewrite <- HpaO; exact Hpain | rewrite <- HpaO; exact Ha].
    + exfalso. apply HOne.
      apply (hb_aval_det (w_H W) mem (A_G_REC + OFF_ANSWER) OLD 0); [lia | lia | exact HansO | exact HANS]. }
cbv beta.
intros W1 c1 Hwle1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & HP1 & HBL1 & HFRS1 & HBB1 & MLE1 & Ef & HEf & HK1).
(* back at 0x3fb8, with the old answer freed: a0 := the text, then the call of xstrdup *)
pose proof HJ1 as (HAR1 & Hly1 & _ & Hwle1' & _ & Hfrs1' & Hnev1 & _ & _ & _ & _ & _ & _ & Hpres1 & _).
assert (HSYMS : asyms_ok B) by exact (am_syms _ _ _ _ (proj1 HAR)).
jafter_call_keep_pi HS 33%nat regs1 (mrestrict (w_H W1) mem1) HP1 [0; 1]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
    + apply (mbyte_of_aview SEGS). apply (proj1 HK1); lia.
    + intros _. apply (apresent_writable SEGS). apply Hpres1. rewrite HBS. lia.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Eans'; intros a Ha.
    + apply (mbyte_of_aview SEGS).
      destruct (prog_static_sep B a HSYMS (hb_prog_ans a ltac:(lia))) as (Hno & Hne & _).
      apply (proj1 (proj2 (proj2 HK1))); [apply (cif_prog_img _ _ IMG); apply hb_inFP_ans; lia | exact Hno | exact Hne].
    + intros _. apply (PROG_WRITABLE SEGS B LAWS HB PRW). apply hb_inFP_ans. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 33 (map (getr regs1) CLOB)) as E1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall n, (n < 33)%nat -> ew E1 n = ew E n)
by (intros n Hn; rewrite HE1; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE1 : env_agree 32 (Ereg regs [Z_to_bv 64 OLD]) E1)
by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE1.
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite OLD1 by (cbv; lia); exact Usp).
assert (Eans1 : bv_unsigned (ew E1 298%nat) = A_G_REC + OFF_ANSWER)
by (rewrite (HEI1 298%nat ltac:(unfold A_TEXT, A_LIM; lia));
    change (VAL 298%nat) with (VAL (A_OBJ HB_ANS_OBJ)); exact hb_val_ans).
assert (E1s : ew E1 10 = w64 s) by (rewrite OLD1 by (cbv; lia); rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E1gp : ew E1 3 = w64 (as_gp B)) by (rewrite OLD1 by (cbv; lia); rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (E1tp : ew E1 4 = w64 (as_tp B)) by (rewrite OLD1 by (cbv; lia); rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
(* 0x3fb8 .. 0x3fbc: a0 := the text, then the call of xstrdup *)
paj_run_shc RUNP RUNC HS HJ1.
{ intros a Ha. destruct Ha as (r & Hin & Hr). cbn [In] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  - left. rewrite Usp1 in Hr. lia.
  - right. right. right. right. left. rewrite Eans1 in Hr.
    split; [apply (proj2 (inFP_cons _ _ _ a)); left; lia|].
    split; [apply hb_prog_ans; lia | apply (cif_prog_img _ _ IMG); apply hb_inFP_ans; lia]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv0 := mdx) in *; clearbody mdv0 end.
(* what the walk has kept of the caller's buffer: the entry run writes only the own frame and the answer word,
   the free only its own window and the block it releases *)
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  ~ (A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha H1 H2.
  apply (kept_of_frame (segs := SEGS) E (ss_mem ss_hb) (w_H W) mem (ms_mem ms)
    (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8)) HFr).
  - intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?Eans' in Hrr; lia|]). destruct Hin.
  - exact Ha.
  - tauto. }

assert (Hfrs1S : In (cid, pos) (frames S1)) by (rewrite HFRS1; exact Hfr).
assert (Hfadr1 : frame_addr ly1 cid pos = frame_addr ly cid pos)
by (unfold frame_addr; destruct Hly1 as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
assert (HnotEf : forall a, (in_zr a (frame_rng ly (cid, pos)) \/
  in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) -> ~ Ef a).
{ intros a Ha HE. destruct (HEf a HE) as (k & Hink & Hak).
  destruct (al_blocks _ _ LAWS ly S W mem md OLD k HAR Hink) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbk).
  destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha.
  - pose proof (sep_block_frame SEGS B LAWS ly S W mem md OLD k cid pos HAR Hink Hfr) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - exact (fshadow_not_app (frame_addr ly cid pos) (fs_frame_bytes cid / 8) OLD (req_size k) a
      ltac:(lia) ltac:(pose proof (fs_frame_bytes_nonneg cid); pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)); lia)
      Hbapp ltac:(unfold shadow_addr, SHADOW_OFF in Ha; lia) Hak). }
assert (HFRB : forall a, (in_zr a (frame_rng ly (cid, pos)) \/
  in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  0 <= a < 2 ^ 64 /\ ~ (spZ regs - 32 <= a < spZ regs) /\
  ~ (A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8)).
{ intros a Ha.
  destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfr) as (Hb1 & Hb2 & Hb3).
  pose proof (fs_frame_bytes_nonneg cid) as Hfsnn.
  assert (Hsh8 : 8 * (fs_frame_bytes cid / 8) <= fs_frame_bytes cid) by (apply Z.mul_div_le; lia).
  assert (Hsh0 : 0 <= fs_frame_bytes cid / 8) by (apply Z.div_pos; lia).
  assert (Hdv1 : 0 <= frame_addr ly cid pos / 8) by (apply Z.div_pos; lia).
  assert (Hdv2 : 8 * (frame_addr ly cid pos / 8) <= frame_addr ly cid pos) by (apply Z.mul_div_le; lia).
  pose proof (frm_off_imgP B ly S W mem md cid pos HAR Hfr) as Hfimg. unfold off_img in Hfimg.
  destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Ha; cbn [fst snd] in Ha;
  unfold A_G_REC, OFF_ANSWER; repeat split; lia. }
assert (HKF : forall a, (in_zr a (frame_rng ly (cid, pos)) \/
  in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) -> rdW W1 mem1 a = rdW W mem a).
{ intros a Ha. destruct (HFRB a Ha) as (Hb64 & Hbst & Hbans).
  rewrite ((proj1 (proj2 (proj2 (proj2 HK1)))) cid pos a Hfr Ha (HnotEf a Ha)).
  apply KEEP0; [exact Hb64 | exact Hbst | exact Hbans]. }
(* the two instructions since the free write nothing *)
lazymatch goal with
| HF2 : frame_of E1 _ (mrestrict _ _) (mrestrict _ ?mT) |- _ =>
  assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
    ~ (A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8) -> rdW W1 mT a = rdW W1 mem1 a)
  by (intros a Ha H1 H2;
      apply (kept_of_frame (segs := SEGS) E1 _ (w_H W1) mem1 mT
        (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8)) HF2);
      [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
          [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp1, ?Eans1 in Hrr; lia|]); destruct Hin
      | exact Ha | tauto ])
end.
(* the caller's text at the call state, and the rest of xstrdup's premises *)
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
rewrite hb_sig_xstrdup.
assert (Hfs8 : fs_frame_bytes cid = 8 * (fs_frame_bytes cid / 8)).
{ rewrite (fs_frame_bytes_eq cid ltac:(lia)).
  replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia. rewrite Z.div_mul by lia. lia. }
assert (Hxn : 1 <= Z.of_nat (length x) + 1) by lia.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ =>
  set (rTv := r) in *; set (mTv := m) in *; set (dTv := d) in * end.
assert (HKF2 : forall a, (in_zr a (frame_rng ly (cid, pos)) \/
  in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) -> rdW W1 mTv a = rdW W mem a);
[ intros a Ha; destruct (HFRB a Ha) as (Hb64 & Hbst & Hbans);
  rewrite (KEEP1 a Hb64 Hbst Hbans); exact (HKF a Ha) | ].
assert (HSTR1 : astr_atR (rdW W1 mTv) s x);
[ destruct Hstr as [Hb Hnz]; split; [|exact Hnz]; intros i Hi;
  rewrite (HKF2 (s + Z.of_nat i)); [exact (Hb i Hi)|];
  left; unfold in_zr, frame_rng; cbn [fst snd];
  rewrite length_app in Hi; cbn [length] in Hi; lia | ].
assert (HRA1 : range_addressable (rdW W1 mTv) SHADOW_OFF s (Z.of_nat (length x) + 1));
[ intros y Hy; destruct (Hsra y Hy) as (sv & Hsv & Hok); exists sv; split; [|exact Hok];
  rewrite (HKF2 (shadow_of_addr SHADOW_OFF y)); [exact Hsv|];
  right; unfold in_zr; cbn [fst snd]; unfold shadow_of_addr;
  exact (hb_shadow_in_frame (frame_addr ly cid pos) (fs_frame_bytes cid) s (Z.of_nat (length x) + 1) y
          Hfal Hfs8 Hfle Hfhi Hy) | ].
assert (HAFOBJ1 : afobj SEGS B ly1 S1 W1 mTv s (Z.of_nat (length x) + 1));
[ split; [exists cid, pos; rewrite Hfadr1; repeat split; assumption | split; [exact Hs8 | exact HRA1]] | ].
assert (HTAIL1 : atail_vis SEGS W1 mTv (s + Z.of_nat (length x)));
[ intros a Ha;
  assert (Hfsm : fs_frame_bytes cid mod 8 = 0)
  by (rewrite (fs_frame_bytes_eq cid ltac:(lia)); replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia;
      apply Z.mod_mul; lia);
  assert (Hc8 : (frame_addr ly cid pos + fs_frame_bytes cid) mod 8 = 0)
  by (rewrite Zplus_mod, Hfal, Hfsm; reflexivity);
  pose proof (hb_tail_below8 (s + Z.of_nat (length x)) (frame_addr ly cid pos + fs_frame_bytes cid)
    ltac:(lia) Hc8) as Htb;
  destruct (al_frames _ _ LAWS ly1 S1 W1 mTv dTv cid pos (proj1 HJ1) Hfrs1S) as (_ & _ & Hfpres & _);
  rewrite Hfadr1 in Hfpres;
  apply (aview_some_of_apresent SEGS); apply (proj1 (Hfpres a ltac:(lia))) | ].
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW W1 mTv));
[ exact (arodata_ok_journalP SEGS RLO RHI RO_IMG B HAND_BACK_STK (spZ regs)
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O))
    ly S W mem md [] ly1 S1 W1 mTv dTv 1 HJ1 HROFP HROD) | ].
assert (HEV1 : st_nev S1 + EV_XSTRDUP <= EV_MAX)
by (unfold EV_HAND_BACK, EV_XSTRDUP in *; lia).
assert (HLIVE1 : blocks_bytes S1 + LIVE_XSTRDUP x <= LIVE_MAX)
by (unfold LIVE_HAND_BACK, LIVE_XSTRDUP in *; lia).
assert (HMOK1 : mo_ok MT S1 (XM_XSTRDUP MT x));
[ apply (mok_station MT S S1 (XM_HAND_BACK MT x) (mo_free MT) (XM_XSTRDUP MT x) MTL HMOK MLE1);
  [ unfold XM_XSTRDUP; apply mo_malloc_nonneg; [exact MTL | lia]
  | unfold XM_HAND_BACK, XM_XSTRDUP; pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length x) + 1) ltac:(lia)); lia ] | ].
assert (HspT2 : spZ rTv = spZ regs + -32)
by (unfold spZ at 1; rewrite Q2, Usp1; rewrite unsigned_lit_small by lia; reflexivity).
assert (Q3' : getr rTv 3 = w64 (as_gp B)) by (rewrite Q3, E1gp; reflexivity).
assert (Q4' : getr rTv 4 = w64 (as_tp B)) by (rewrite Q4, E1tp; reflexivity).
assert (Q10' : getr rTv 10 = w64 s) by (rewrite Q10, E1s; reflexivity).
assert (Hs0T2 : s0Z rTv = s) by (unfold s0Z; rewrite Q8, E1s; apply unsigned_lit_small; lia).
assert (HchT2 : achain ly1 (rdW W1 mTv) (spZ regs + -32) (s0Z rTv) [])
by (rewrite Hs0T2; apply achain_low; lia).
assert (HARG : astr_argA B ly1 S1 (rdW W1 mTv) (in_roP SEGS RLO RHI) [] s (Some x) \/
  (astr_atR (rdW W1 mTv) s x /\ Z.of_nat (length x) + 1 <= LMAX + 1 /\
   afobj SEGS B ly1 S1 W1 mTv s (Z.of_nat (length x) + 1)))
by (right; split; [exact HSTR1 | split; [lia | exact HAFOBJ1]]).
(* xstrdup(text), through the kit's call rule: its footprint is empty, so plain cl_callS composes *)
eapply SRr_bind with (R := fun (W2 : world SEGS) (c2 : config) =>
  exists ly2 S2 regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 16320)) mem2 (seg_rom SEGS)) md2 /\
  ajournal SEGS B HAND_BACK_STK (spZ regs)
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O))
    ly S W mem md [] ly2 S2 W2 mem2 md2 (1 + EV_XSTRDUP) /\
  ajournal SEGS B XSTRDUP_STK (spZ regs + -32) [] ly1 S1 W1 mTv dTv [] ly2 S2 W2 mem2 md2 EV_XSTRDUP /\
  aregs_preserved rTv regs2 /\
  (exists p : Z, getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
     Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP x) :: ablocks B ly1 S1) /\
     Forall (fun qk => iv_apart p (LIVE_XSTRDUP x) (fst qk) (snd qk)) (ablocks B ly1 S1) /\
     in_blockA (ablocks B ly2 S2) p (LIVE_XSTRDUP x) /\
     astr_atR (rdW W2 mem2) p x /\ astr_atR (rdW W2 mem2) s x /\
     blocks_bytes S2 <= blocks_bytes S1 + LIVE_XSTRDUP x /\
     mo_le MT S1 S2 (XM_XSTRDUP MT x))).
{ eapply SRr_mono.
  { eapply (cl_callS B LAWS W1 rTv mTv (Z_to_bv 64 (BASE + AF_xstrdup)) HAND_BACK_STK (spZ regs)
      ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O))
      ly S W mem md [] ly1 S1 dTv 1 XSTRDUP_STK [] EV_XSTRDUP (-32) (Z_to_bv 64 (BASE + 16320)) []
      (fun ly2 S2 W2 regs2 mem2 md2 => exists p : Z, getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
         Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP x) :: ablocks B ly1 S1) /\
         Forall (fun qk => iv_apart p (LIVE_XSTRDUP x) (fst qk) (snd qk)) (ablocks B ly1 S1) /\
         in_blockA (ablocks B ly2 S2) p (LIVE_XSTRDUP x) /\
         astr_atR (rdW W2 mem2) p x /\ astr_atR (rdW W2 mem2) s x /\
         blocks_bytes S2 <= blocks_bytes S1 + LIVE_XSTRDUP x /\
         mo_le MT S1 S2 (XM_XSTRDUP MT x))
      HJ1 HspT2 eq_refl ltac:(lia) ltac:(unfold XSTRDUP_STK, ASTACK; lia)
      ltac:(rewrite HBS; unfold XSTRDUP_STK, ASTACK; lia) Q3' Q4' Q1
      ltac:(apply ret_ok_codeptr_v; [lia | reflexivity]) ltac:(rewrite unsigned_lit_small; lia) HchT2).
    - intros HPREc. eapply SRr_mono.
      { exact (TXSTRDUP fx ly1 S1 W1 rTv mTv dTv [] s x HPREc HROD1 Q10' HARG HTAIL1 HEV1 HLIVE1 HMOK1). }
      cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2).
      exists ly2, S2, regs2, mem2, md2. split; [rewrite Q1; reflexivity|].
      split; [exact HJ2|]. split; [exact HP2 | exact HQ2].
    - intros a Ha. destruct (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2c & HP2 & HQ2).
  exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HJ2c|].
  split; [exact HP2 | exact HQ2]. }
cbv beta.
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2c & HP2 & p1 & Hp1r & Hp14096 & Hp1perm & Hp1apart & Hp1blk & Hp1str & Hsstr2 & Hp1bb & MLE2).
(* 0x3fc0 .. 0x3fd8: the copy goes into g_rec.answer, the frame is popped, xstrdup is tail-called *)
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof HJ2c as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & F2c & F3c & F4c & _).
jafter_call_keep_pi HS 64%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK2 : t); [|specialize (HS2 HRK2); clear HRK2] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp1; intros a Ha.
    + apply (mbyte_of_aview SEGS).
      apply F1c; [lia | unfold XSTRDUP_STK, ASTACK; lia | apply inFP_nil].
    + intros _. apply (apresent_writable SEGS). apply Hpres2. rewrite HBS. lia.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Eans1; intros a Ha.
    + apply (mbyte_of_aview SEGS).
      destruct (prog_static_sep B a HSYMS (hb_prog_ans a ltac:(lia))) as (Hno & Hne & _).
      apply F3c;
      [apply (cif_prog_img _ _ IMG); apply hb_inFP_ans; lia | exact Hno | exact Hne
      | apply fp_spares_closed; [apply sink_closed_pos; apply Forall_nil | apply inFP_nil]].
    + intros _. apply (PROG_WRITABLE SEGS B LAWS HB PRW). apply hb_inFP_ans. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E1 64 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
assert (OLD2 : forall n, (n < 64)%nat -> ew E2 n = ew E1 n)
by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 OLD]) E2)
by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
(* the copy's address is the a0 atom of the second havoc *)
assert (E2a0 : ew E2 68 = getr regs2 10) by (rewrite HE2; reflexivity).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by (cbv; lia); exact Usp1).
assert (Eans2 : bv_unsigned (ew E2 298%nat) = A_G_REC + OFF_ANSWER)
by (rewrite (HEI2 298%nat ltac:(unfold A_TEXT, A_LIM; lia));
    change (VAL 298%nat) with (VAL (A_OBJ HB_ANS_OBJ)); exact hb_val_ans).
paj_run_shc RUNP RUNC HS HJ2.
{ intros a Ha. destruct Ha as (r & Hin & Hr). cbn [In] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  - left. rewrite Usp2 in Hr. lia.
  - right. right. right. right. left. rewrite Eans2 in Hr.
    split; [apply (proj2 (inFP_cons _ _ _ a)); left; lia|].
    split; [apply hb_prog_ans; lia | apply (cif_prog_img _ _ IMG); apply hb_inFP_ans; lia]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv2 := mdx) in *; clearbody mdv2 end.
(* at the tail call: the frame is popped, a0 is the text again, and g_rec.answer holds the first copy *)
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3.
prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10.
rewrite hb_sig_xstrdup.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ =>
  set (rT3 := r) in *; set (mT3 := m) in *; set (dT3 := d) in * end.
assert (Hp1in2 : In (p1, LIVE_XSTRDUP x) (ablocks B ly2 S2))
by (eapply Permutation_in; [apply Permutation_sym; exact Hp1perm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p1 _ HAR2 Hp1in2) as (_ & Hp1g & Hp1c & Hp1app & _ & _ & Hp1n).
assert (Hp1rng : 0 <= p1 < 2 ^ 64) by (pose proof (req_size_pos (LIVE_XSTRDUP x) ltac:(lia)); lia).
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let rg := eval vm_compute in (nth 1 (ss_mem ssx) hb_stack) in
  pose proof (st_ok_region_nth E2 ssx (restrict (w_H W2) msx) 1 rg HS ltac:(vm_compute; reflexivity)) as HRg3;
  cbn [ms_mem restrict mkst] in HRg3 end.
pose proof (field_of_region E2 _ 298%nat (A_G_REC + OFF_ANSWER) _ _ _ _ _ 0 8 (SOff 68 0) p1 HRg3 Eans2
  ltac:(left; reflexivity)
  ltac:(cbn [sv_denot]; rewrite E2a0, Hp1r, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as Vans.
rewrite Z.add_0_r in Vans. change (N.to_nat 8) with 8%nat in Vans.
(* the store run wrote only the own frame and the answer word *)
lazymatch goal with
| HF3 : frame_of E2 _ (mrestrict _ mem2) (mrestrict _ _) |- _ =>
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
    ~ (A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8) -> rdW W2 mT3 a = rdW W2 mem2 a)
  by (intros a Ha H1 H2;
      apply (kept_of_frame (segs := SEGS) E2 _ (w_H W2) mem2 mT3
        (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8)) HF3);
      [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
          [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2, ?Eans2 in Hrr; lia|]); destruct Hin
      | exact Ha | tauto ])
end.
(* the caller's buffer at the tail call *)
pose proof HJ2c as (_ & Hly2c & _ & _ & _ & Hfrs2c & _).
assert (Hfrs2S : In (cid, pos) (frames S2)) by (rewrite Hfrs2c; exact Hfrs1S).
assert (Hfadr2 : frame_addr ly2 cid pos = frame_addr ly cid pos)
by (rewrite <- Hfadr1; unfold frame_addr; destruct Hly2c as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
assert (HKF3 : forall a, (in_zr a (frame_rng ly (cid, pos)) \/
  in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) -> rdW W2 mT3 a = rdW W1 mTv a).
{ intros a Ha. destruct (HFRB a Ha) as (Hb64 & Hbst & Hbans).
  rewrite (KEEP3 a Hb64 Hbst Hbans).
  apply (F4c cid pos a Hfrs1S); [| apply inFP_nil].
  unfold frame_rng in Ha |- *. cbn [fst snd] in Ha |- *. rewrite Hfadr1. exact Ha. }
assert (HSTR3 : astr_atR (rdW W2 mT3) s x).
{ destruct Hsstr2 as [Hb Hnz]. split; [|exact Hnz]. intros i Hi.
  destruct (HFRB (s + Z.of_nat i)) as (Hb64 & Hbst & Hbans);
  [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite length_app in Hi; cbn [length] in Hi; lia|].
  rewrite (KEEP3 _ Hb64 Hbst Hbans). exact (Hb i Hi). }
assert (HRA3 : range_addressable (rdW W2 mT3) SHADOW_OFF s (Z.of_nat (length x) + 1)).
{ intros y Hy. destruct (HRA1 y Hy) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  rewrite (HKF3 (shadow_of_addr SHADOW_OFF y)); [exact Hsv|].
  right. unfold in_zr; cbn [fst snd]. unfold shadow_of_addr.
  exact (hb_shadow_in_frame (frame_addr ly cid pos) (fs_frame_bytes cid) s (Z.of_nat (length x) + 1) y
          Hfal Hfs8 Hfle Hfhi Hy). }
assert (HAFOBJ3 : afobj SEGS B ly2 S2 W2 mT3 s (Z.of_nat (length x) + 1)).
{ split; [exists cid, pos; rewrite Hfadr2; repeat split; assumption | split; [exact Hs8 | exact HRA3]]. }
assert (HTAIL3 : atail_vis SEGS W2 mT3 (s + Z.of_nat (length x))).
{ intros a Ha.
  assert (Hfsm : fs_frame_bytes cid mod 8 = 0)
  by (rewrite (fs_frame_bytes_eq cid ltac:(lia)); replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia;
      apply Z.mod_mul; lia).
  assert (Hc8 : (frame_addr ly cid pos + fs_frame_bytes cid) mod 8 = 0) by (rewrite Zplus_mod, Hfal, Hfsm; reflexivity).
  pose proof (hb_tail_below8 (s + Z.of_nat (length x)) (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(lia) Hc8) as Htb.
  destruct (al_frames _ _ LAWS ly2 S2 W2 mT3 _ cid pos (proj1 HJ2) Hfrs2S) as (_ & _ & Hfpres & _).
  rewrite Hfadr2 in Hfpres. apply (aview_some_of_apresent SEGS). apply (proj1 (Hfpres a ltac:(lia))). }
assert (HARG3 : astr_argA B ly2 S2 (rdW W2 mT3) (in_roP SEGS RLO RHI) [] s (Some x) \/
  (astr_atR (rdW W2 mT3) s x /\ Z.of_nat (length x) + 1 <= LMAX + 1 /\
   afobj SEGS B ly2 S2 W2 mT3 s (Z.of_nat (length x) + 1)))
by (right; split; [exact HSTR3 | split; [lia | exact HAFOBJ3]]).
assert (HROD3 : arodata_okP SEGS RLO RHI B (rdW W2 mT3))
by exact (arodata_ok_journalP SEGS RLO RHI RO_IMG B HAND_BACK_STK (spZ regs)
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O))
    ly S W mem md [] ly2 S2 W2 mT3 _ _ HJ2 HROFP HROD).
pose proof HJ2 as (_ & Hly2o & _ & _ & _ & _ & Hnev2o & _).
assert (HEV3 : st_nev S2 + EV_XSTRDUP <= EV_MAX) by (unfold EV_HAND_BACK, EV_XSTRDUP in *; lia).
assert (HBB2 : blocks_bytes S2 = LIVE_XSTRDUP x + blocks_bytes S1)
by (rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly1 S1), (bsum_perm _ _ Hp1perm), bsum_cons; reflexivity).
assert (HLIVE3 : blocks_bytes S2 + LIVE_XSTRDUP x <= LIVE_MAX)
by (unfold LIVE_HAND_BACK, LIVE_XSTRDUP in *; lia).
assert (MLE12 : mo_le MT S S2 (mo_free MT + XM_XSTRDUP MT x)) by exact (mle_station MT S S1 S2 _ _ MTL MLE1 MLE2).
assert (HMOK3 : mo_ok MT S2 (XM_XSTRDUP MT x)).
{ apply (mok_station MT S S2 (XM_HAND_BACK MT x) (mo_free MT + XM_XSTRDUP MT x) (XM_XSTRDUP MT x) MTL HMOK MLE12).
  - unfold XM_XSTRDUP. apply mo_malloc_nonneg; [exact MTL | lia].
  - unfold XM_HAND_BACK. lia. }
assert (T1' : getr rT3 1 = getr regs 1)
by (rewrite T1, OLD2, OLD1, (EE 1%nat 1%bv eq_refl) by (cbv; lia); reflexivity).
assert (T2' : spZ rT3 = spZ regs + 0)
by (unfold spZ at 1; rewrite T2, OLD2 by (cbv; lia); rewrite OLD1 by (cbv; lia); rewrite Usp; lia).
assert (T3' : getr rT3 3 = w64 (as_gp B)) by (rewrite T3, OLD2 by (cbv; lia); exact E1gp).
assert (T4' : getr rT3 4 = w64 (as_tp B)) by (rewrite T4, OLD2 by (cbv; lia); exact E1tp).
assert (T10' : getr rT3 10 = w64 s) by (rewrite T10, OLD2 by (cbv; lia); exact E1s).
assert (Hs0T3 : s0Z rT3 = s0Z regs)
by (unfold s0Z; rewrite T8, OLD2, OLD1, (EE 8%nat 8%bv eq_refl) by (cbv; lia); reflexivity).
assert (HchT3 : achain ly2 (rdW W2 mT3) (spZ regs + 0) (s0Z rT3) ch).
{ rewrite Hs0T3, Z.add_0_r.
  apply (achain_ly_top ly ly2); [destruct Hly2o as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _); exact ET|].
  apply (achain_kept ly (rdW W mem) (rdW W2 mT3) (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
  intros a Ha. exact (aview_above_of_journal B HAND_BACK_STK (spZ regs) _ ly S W mem md [] ly2 S2 W2 mT3 _ _ HJ2 a Ha
    (HFPhi a ltac:(lia))). }
(* the tail call: xstrdup returns straight to hand_back's caller *)
eapply SRr_mono.
{ eapply (cl_callS B LAWS W2 rT3 mT3 (Z_to_bv 64 (BASE + AF_xstrdup)) HAND_BACK_STK (spZ regs)
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O))
    ly S W mem md [] ly2 S2 dT3 (1 + EV_XSTRDUP) XSTRDUP_STK [] EV_XSTRDUP 0 (getr regs 1) ch
    (fun ly3 S3 W3 regs3 mem3 md3 => exists p : Z, getr regs3 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
       Permutation (ablocks B ly3 S3) ((p, LIVE_XSTRDUP x) :: ablocks B ly2 S2) /\
       Forall (fun qk => iv_apart p (LIVE_XSTRDUP x) (fst qk) (snd qk)) (ablocks B ly2 S2) /\
       in_blockA (ablocks B ly3 S3) p (LIVE_XSTRDUP x) /\
       astr_atR (rdW W3 mem3) p x /\ astr_atR (rdW W3 mem3) s x /\
       blocks_bytes S3 <= blocks_bytes S2 + LIVE_XSTRDUP x /\
       mo_le MT S2 S3 (XM_XSTRDUP MT x))
    HJ2 T2' eq_refl ltac:(lia) ltac:(unfold XSTRDUP_STK, ASTACK; lia)
    ltac:(rewrite HBS; unfold XSTRDUP_STK, ASTACK; lia) T3' T4' T1' Hra Hra4 HchT3).
  - intros HPREc. eapply SRr_mono.
    { exact (TXSTRDUP fx ly2 S2 W2 rT3 mT3 dT3 ch s x HPREc HROD3 T10' HARG3 HTAIL3 HEV3 HLIVE3 HMOK3). }
    cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3).
    exists ly3, S3, regs3, mem3, md3. split; [rewrite T1'; reflexivity|].
    split; [exact HJ3|]. split; [exact HP3 | exact HQ3].
  - intros a Ha. destruct (inFP_nil a Ha). }
cbv beta.
intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJ3c & HP3 & p2 & Hp2r & Hp24096 & Hp2perm & Hp2apart & Hp2blk & Hp2str & Hsstr3 & Hp2bb & MLE3).
(* what the whole call kept: the image outside the answer word, and every live block it did not free *)
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & _ & _ & F2o & F3o & _).
pose proof HJ3c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2d & F3d & _).
assert (HFPblk : forall p n i, In (p, n) (ablocks B ly S) -> fst (p, n) <> old -> 0 <= i < req_size n ->
  ~ inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8)
          :: ablocks_fp (filter (fun pn => fst pn =? old) O)) (p + i)).
{ intros p n i Hin Hne Hi Hfp.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hp4096 & Hpc & _ & _ & _ & Hn0).
  pose proof (blk_off_imgP B ly S W mem md p n HAR Hin) as Hoff. unfold off_img in Hoff.
  apply (proj1 (inFP_cons _ _ _ (p + i))) in Hfp as [Hfp | Hfp]; [unfold A_G_REC, OFF_ANSWER in *; lia|].
  destruct (inFP_ablocks_fp_inv _ (p + i) Hfp) as (q & m & Hqm & Hr).
  destruct (hb_filter_in _ _ _ Hqm) as [HinO Hfq]. cbn [fst] in Hfq. apply Z.eqb_eq in Hfq.
  pose proof (HObl _ HinO) as Hinq.
  destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hinq) as (_ & _ & _ & _ & _ & _ & Hm0).
  cbn [fst snd] in Hr, Hne.
  assert (Hne2 : (q, m) <> (p, n)) by (intros Heq; injection Heq as <- <-; exact (Hne Hfq)).
  pose proof (sep_blocks SEGS B LAWS ly S W mem md q m p n HAR Hinq Hin Hne2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (KEEPG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8) -> rdW W3 mem3 a = rdW W mem a).
{ intros a Himg Hown Herr Hans2. apply F3o; [exact Himg | exact Hown | exact Herr|].
  apply fp_spares_closed.
  - apply sink_closed_cons; [cbn [fst]; unfold A_G_REC, OFF_ANSWER; lia|].
    apply sink_closed_ablocks_fp. apply Forall_forall. intros pn Hpn.
    destruct (hb_filter_in _ _ _ Hpn) as [HinO _].
    destruct pn as [pq nq].
    destruct (al_blocks _ _ LAWS ly S W mem md pq nq HAR (HObl _ HinO)) as (_ & Hq4096 & _).
    cbn [fst]. lia.
  - intros Hfp. apply (proj1 (inFP_cons _ _ _ a)) in Hfp as [Hfp | Hfp]; [exact (Hans2 Hfp)|].
    destruct (inFP_ablocks_fp_inv _ a Hfp) as (q & m & Hqm & Hr).
    destruct (hb_filter_in _ _ _ Hqm) as [HinO _]. pose proof (HObl _ HinO) as Hinq.
    pose proof (blk_off_imgP B ly S W mem md q m HAR Hinq) as Hoff. unfold off_img in Hoff.
    pose proof (pa_img_range a Himg). cbn [fst snd] in Hr.
    destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hinq) as (_ & _ & _ & _ & _ & _ & Hm0). lia. }
assert (KEEPB : forall p n i, In (p, n) (ablocks B ly S) -> fst (p, n) <> old -> In (p, n) (ablocks B ly3 S3) ->
  0 <= i < req_size n -> rdW W3 mem3 (p + i) = rdW W mem (p + i))
by (intros p n i Hin Hne Hin3 Hi; exact (F2o p n i Hin Hin3 Hi (HFPblk p n i Hin Hne Hi))).
(* the first copy's block and the answer word after the tail call *)
assert (Hp1in3 : In (p1, LIVE_XSTRDUP x) (ablocks B ly3 S3))
by (eapply Permutation_in; [apply Permutation_sym; exact Hp2perm | right; exact Hp1in2]).
assert (Hrqn : req_size (LIVE_XSTRDUP x) = LIVE_XSTRDUP x)
by (unfold req_size, LIVE_XSTRDUP; destruct (Z.eqb_spec (Z.of_nat (length x) + 1) 0); [lia | reflexivity]).
pose proof (blk_off_imgP B ly2 S2 W2 mem2 md2 p1 _ HAR2 Hp1in2) as Hp1off. unfold off_img in Hp1off.
assert (KEEPP1 : forall i, 0 <= i < LIVE_XSTRDUP x -> rdW W3 mem3 (p1 + i) = rdW W2 mem2 (p1 + i)).
{ intros i Hi. rewrite (F2d p1 _ i Hp1in2 Hp1in3 ltac:(lia) (inFP_nil _)).
  apply KEEP3; [lia | lia | rewrite Hrqn in Hp1off; unfold A_G_REC, OFF_ANSWER; lia]. }
assert (Hp1str3 : astr_atR (rdW W3 mem3) p1 x).
{ destruct Hp1str as [Hb Hnz]. split; [|exact Hnz]. intros i Hi.
  rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (KEEPP1 (Z.of_nat i) ltac:(unfold LIVE_XSTRDUP; lia)). exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)). }
assert (Vans3 : aval_mem (rdW W3 mem3) (A_G_REC + OFF_ANSWER) 8 p1).
{ intros k Hk.
  destruct (prog_static_sep B (A_G_REC + OFF_ANSWER + Z.of_nat k) HSYMS
    (hb_prog_ans (A_G_REC + OFF_ANSWER + Z.of_nat k) ltac:(lia))) as (Hno & Hne & _).
  rewrite (F3d (A_G_REC + OFF_ANSWER + Z.of_nat k));
  [ exact (hb_val_mem_rev _ _ _ _ _ Vans k Hk)
  | apply (cif_prog_img _ _ IMG); apply hb_inFP_ans; lia | exact Hno | exact Hne
  | apply fp_spares_closed; [apply sink_closed_pos; apply Forall_nil | apply inFP_nil] ]. }
(* the post of hand_back *)
assert (Hp12 : p1 <> p2).
{ intros Heq. pose proof (proj1 (Forall_forall _ _) Hp2apart (p1, LIVE_XSTRDUP x) Hp1in2) as Hap.
  cbn [fst snd] in Hap. unfold iv_apart, LIVE_XSTRDUP in Hap. lia. }
assert (HFRESH1 : forall pn, In pn (ablocks B ly S) -> fst pn <> old -> pn <> (p1, Z.of_nat (length x) + 1)).
{ intros pn Hin Hne Heq. subst pn.
  assert (Hin1 : In (p1, LIVE_XSTRDUP x) (ablocks B ly1 S1))
  by (apply (proj2 (HBL1 _)); split; [exact Hin | cbn [fst] in Hne |- *; rewrite HOeq; exact Hne]).
  pose proof (proj1 (Forall_forall _ _) Hp1apart _ Hin1) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart, LIVE_XSTRDUP in Hap. lia. }
assert (HFRESH2 : forall pn, In pn (ablocks B ly S) -> fst pn <> old -> pn <> (p2, Z.of_nat (length x) + 1)).
{ intros pn Hin Hne Heq. subst pn.
  assert (Hin1 : In (p2, LIVE_XSTRDUP x) (ablocks B ly1 S1))
  by (apply (proj2 (HBL1 _)); split; [exact Hin | cbn [fst] in Hne |- *; rewrite HOeq; exact Hne]).
  assert (Hin2 : In (p2, LIVE_XSTRDUP x) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hp1perm | right; exact Hin1]).
  pose proof (proj1 (Forall_forall _ _) Hp2apart _ Hin2) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart, LIVE_XSTRDUP in Hap. lia. }
assert (Hp2in3 : In (p2, LIVE_XSTRDUP x) (ablocks B ly3 S3))
by (eapply Permutation_in; [apply Permutation_sym; exact Hp2perm | left; reflexivity]).
unfold apost_base. exists ly3, S3, regs3, mem3, md3.
split; [reflexivity|].
split; [unfold EV_HAND_BACK, EV_XSTRDUP in *; exact HJ3|].
split.
{ eapply aregs_preserved_trans; [|exact HP3].
  exact (aregs_preserved_of_st_ok SEGS _ E2 _ _ regs [Z_to_bv 64 OLD] HS HAE2 ltac:(vm_compute; reflexivity)). }
exists p1, p2, (lay_blocks (RLay (l_calls Q) (l_spill Q) (Some (p1, Z.of_nat (length x) + 1)) (l_reply Q))).
cbv zeta.
split; [exact Hp2r|].
split; [exact Hp24096|].
split; [exact Hp12|].
split; [intros pn Hin Hne; split; [exact (HFRESH1 pn Hin Hne) | exact (HFRESH2 pn Hin Hne)]|].
split.
{ intros pn. split.
  - intros Hin3. apply (Permutation_in _ Hp2perm) in Hin3. destruct Hin3 as [Heq | Hin2];
    [right; right; symmetry; unfold LIVE_XSTRDUP in Heq; exact Heq|].
    apply (Permutation_in _ Hp1perm) in Hin2. destruct Hin2 as [Heq | Hin1];
    [right; left; symmetry; unfold LIVE_XSTRDUP in Heq; exact Heq|].
    left. destruct (proj1 (HBL1 pn) Hin1) as [HA1 HB1]. split; [exact HA1 | rewrite <- HOeq; exact HB1].
  - intros [[HA1 HB1] | [Heq | Heq]].
    + apply (Permutation_in _ (Permutation_sym Hp2perm)). right.
      apply (Permutation_in _ (Permutation_sym Hp1perm)). right.
      apply (proj2 (HBL1 pn)). split; [exact HA1 | rewrite HOeq; exact HB1].
    + rewrite Heq. unfold LIVE_XSTRDUP in Hp1in3. exact Hp1in3.
    + rewrite Heq. unfold LIVE_XSTRDUP in Hp2in3. exact Hp2in3. }
(* the answer slot of the recorder's layout, and that nothing else of it starts at the old answer *)
assert (HOTH : forall pn, In pn (concat (l_calls Q) ++ l_spill Q ++ oblk (l_reply Q)) -> fst pn <> old).
{ pose proof HAREP as (_ & _ & _ & _ & HANS2 & _ & _ & HOWN2).
  intros pn Hin.
  assert (HinQ : In pn (lay_blocks Q)).
  { unfold lay_blocks. apply in_app_or in Hin as [Hc | Hin]; [apply in_or_app; left; exact Hc|].
    apply in_app_or in Hin as [Hs | Hr]; apply in_or_app; right;
    [apply in_or_app; left; exact Hs | apply in_or_app; right; apply in_or_app; right; exact Hr]. }
  destruct (r_answer R) as [t|] eqn:ERA; destruct (l_answer Q) as [[pa pk]|] eqn:ELA;
  try (exfalso; exact HANS2).
  - destruct HANS2 as (Hva & _ & Hpain & _).
    destruct (al_blocks _ _ LAWS ly S W mem md pa pk HAR Hpain) as (_ & Hpa4096 & Hpaceil & _ & _ & _ & Hpkr).
    pose proof (req_size_pos pk ltac:(lia)) as [Hrq1 Hrq2].
    assert (HpaO : pa = old)
    by (rewrite <- HOeq; apply (hb_aval_det (w_H W) mem (A_G_REC + OFF_ANSWER)); [lia | lia | exact Hva | exact HansO]).
    rewrite <- HpaO. pose proof (proj1 HOWN2) as Hnd. unfold lay_blocks in Hnd. rewrite ELA in Hnd.
    cbn [oblk] in Hnd. rewrite !map_app in Hnd. cbn [map] in Hnd. rewrite app_assoc in Hnd.
    cbn [app fst] in Hnd. first [apply NoDup_ListNoDup in Hnd | idtac].
    pose proof (NoDup_remove_2 _ _ _ Hnd) as Hni. intros Hfp. apply Hni. rewrite <- Hfp.
    rewrite <- !map_app. apply in_map. rewrite <- app_assoc. exact Hin.
  - assert (Hold0 : old = 0)
    by (rewrite <- HOeq; apply (hb_aval_det (w_H W) mem (A_G_REC + OFF_ANSWER)); [lia | lia | exact HansO | exact HANS2]).
    destruct pn as [pq nq]. destruct (al_blocks _ _ LAWS ly S W mem md pq nq HAR
      (hb_lay_in _ _ _ _ _ _ _ HAREP HinQ)) as (_ & Hq4096 & _). cbn [fst]. lia. }
assert (HANSOLD : forall pa pk, l_answer Q = Some (pa, pk) -> pa = old).
{ pose proof HAREP as (_ & _ & _ & _ & HANS2 & _).
  intros pa pk ELA. destruct (r_answer R) as [t|] eqn:ERA; rewrite ELA in HANS2;
  [|exfalso; exact HANS2].
  destruct HANS2 as (Hva & _ & Hpain & _).
  destruct (al_blocks _ _ LAWS ly S W mem md pa pk HAR Hpain) as (_ & Hpa4096 & Hpaceil & _ & _ & _ & Hpkr).
  pose proof (req_size_pos pk ltac:(lia)) as [Hrq1 Hrq2].
  rewrite <- HOeq. apply (hb_aval_det (w_H W) mem (A_G_REC + OFF_ANSWER)); [lia | lia | exact Hva | exact HansO]. }
split.
2:{ split.
    2:{ split.
        2:{ split.
            - unfold LIVE_HAND_BACK. lia.
            - unfold XM_HAND_BACK. exact (mle_station MT S S2 S3 _ _ MTL MLE12 MLE3). }
        cbn [hand_back snd]. exact Hp2str. }
    (* the recorder's own blocks after the call *)
    intros pn. unfold lay_blocks at 1. cbn [l_calls l_spill l_answer l_reply oblk].
    split.
    - intros Hin. apply in_app_or in Hin as [Hc | Hin].
      + left. split; [apply HOQ; unfold lay_blocks; apply in_or_app; left; exact Hc|].
        apply HOTH. apply in_or_app. left. exact Hc.
      + apply in_app_or in Hin as [Hs | Hin].
        * left. split; [apply HOQ; unfold lay_blocks; apply in_or_app; right; apply in_or_app; left; exact Hs|].
          apply HOTH. apply in_or_app. right. apply in_or_app. left. exact Hs.
        * apply in_app_or in Hin as [Ha | Hr].
          -- destruct Ha as [Heq | []]. right. symmetry. exact Heq.
          -- left. split; [apply HOQ; unfold lay_blocks; apply in_or_app; right; apply in_or_app; right;
               apply in_or_app; right; exact Hr|].
             apply HOTH. apply in_or_app. right. apply in_or_app. right. exact Hr.
    - intros [[HA1 HB1] | Heq].
      + apply HOQ in HA1. unfold lay_blocks in HA1.
        apply in_app_or in HA1 as [Hc | HA1]; [apply in_or_app; left; exact Hc|].
        apply in_app_or in HA1 as [Hs | HA1]; [apply in_or_app; right; apply in_or_app; left; exact Hs|].
        apply in_app_or in HA1 as [Ha | Hr].
        * exfalso. destruct (l_answer Q) as [[pa pk]|] eqn:ELA; cbn [oblk] in Ha; [|destruct Ha].
          destruct Ha as [Heq | []]. rewrite <- Heq in HB1. cbn [fst] in HB1.
          exact (HB1 (HANSOLD pa pk ltac:(first [exact ELA | reflexivity]))).
        * apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hr.
      + rewrite Heq. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
(* the recorder's state after the call *)
assert (KEEPREC : forall a, (A_G_REC <= a < A_G_REC + 960 \/ A_REC_SPILL <= a < A_REC_SPILL + 56) ->
  ~ (A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8) -> rdW W3 mem3 a = rdW W mem a).
{ intros a Ha Hne.
  assert (HinPG : inFP cmd_PG a).
  { unfold cmd_PG. destruct Ha as [Ha | Ha];
    [apply (proj2 (inFP_cons _ _ _ a)); left; cbn [fst snd]; lia
    | apply (proj2 (inFP_cons _ _ _ a)); right; apply (proj2 (inFP_cons _ _ _ a)); left; cbn [fst snd]; lia]. }
  destruct (prog_static_sep B a HSYMS (HPROG a HinPG)) as (Hno & Herr & _).
  exact (KEEPG a (cif_prog_img _ _ IMG a HinPG) Hno Herr Hne). }
assert (HKEEPIN : forall pn, In pn (ablocks B ly S) -> fst pn <> old -> In pn (ablocks B ly3 S3)).
{ intros pn HA1 HB1. apply (Permutation_in _ (Permutation_sym Hp2perm)). right.
  apply (Permutation_in _ (Permutation_sym Hp1perm)). right.
  apply (proj2 (HBL1 pn)). split; [exact HA1 | rewrite HOeq; exact HB1]. }
assert (HCALLKEEP : forall a c P, (forall b, a <= b < a + CALL_SIZE -> rdW W3 mem3 b = rdW W mem b) ->
  (forall pn, In pn P -> In pn (concat (l_calls Q) ++ l_spill Q ++ oblk (l_reply Q))) ->
  acall_at (ablocks B ly S) (rdW W mem) a c P -> acall_at (ablocks B ly3 S3) (rdW W3 mem3) a c P).
{ intros a c P HK HPQ (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [exact (hb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (a + CALL_OFF_FN) 4 (fst c) a (a + CALL_SIZE)
    HK ltac:(unfold CALL_OFF_FN; lia) ltac:(unfold CALL_OFF_FN, CALL_SIZE; cbn; lia) H4)|].
  split; [exact (hb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (a + CALL_OFF_NARGS) 4 (Z.of_nat (length (snd c)))
    a (a + CALL_SIZE) HK ltac:(unfold CALL_OFF_NARGS; lia) ltac:(unfold CALL_OFF_NARGS, CALL_SIZE; cbn; lia) H5)|].
  split; [exact H6|].
  intros k sv pn Hs Hp. destruct (H7 k sv pn Hs Hp) as (G1 & G2 & G3 & G4 & G5).
  assert (Hk6 : (k < 6)%nat).
  { assert (Hk' : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Hs; discriminate). lia. }
  assert (Hne : fst pn <> old) by (apply HOTH; apply HPQ; eapply nth_error_In; exact Hp).
  destruct pn as [pq nq]. cbn [fst snd] in *.
  destruct (al_blocks _ _ LAWS ly S W mem md pq nq HAR G3) as (_ & Hq4096 & _ & _ & _ & _ & Hnq0).
  pose proof (req_size_pos nq ltac:(lia)) as [Hrq1 Hrq2].
  assert (HKq : forall b, pq <= b < pq + req_size nq -> rdW W3 mem3 b = rdW W mem b)
  by (intros b Hb; replace b with (pq + (b - pq)) by lia; exact (KEEPB pq nq (b - pq) G3 Hne (HKEEPIN _ G3 Hne) ltac:(lia))).
  split; [exact (hb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (a + CALL_OFF_ARGS + 8 * Z.of_nat k) 8 pq
    a (a + CALL_SIZE) HK ltac:(unfold CALL_OFF_ARGS; lia) ltac:(unfold CALL_OFF_ARGS, CALL_SIZE; cbn; lia) G1)|].
  split; [exact G2|]. split; [exact (HKEEPIN _ G3 Hne)|]. split; [exact G4|].
  exact (hb_astr_kept_rng (rdW W mem) (rdW W3 mem3) pq sv pq (pq + req_size nq) HKq ltac:(lia) ltac:(lia) G5). }
assert (KREC : forall lo hi, A_G_REC <= lo -> hi <= A_G_REC + 960 ->
  (hi <= A_G_REC + OFF_ANSWER \/ A_G_REC + OFF_ANSWER + 8 <= lo) ->
  forall b, lo <= b < hi -> rdW W3 mem3 b = rdW W mem b)
by (intros lo hi H1 H2 H3 b Hb; apply KEEPREC; [left; lia | unfold OFF_ANSWER in *; lia]).
assert (KSPL : forall b, A_REC_SPILL <= b < A_REC_SPILL + 56 -> rdW W3 mem3 b = rdW W mem b)
by (intros b Hb; apply KEEPREC; [right; exact Hb | unfold A_G_REC, A_REC_SPILL, OFF_ANSWER in *; lia]).
pose proof HAREP as (Hg8 & Hsc8b & Hapb & HC & HA & HPb & HSC & HOW).
cbn [hand_back fst].
exists (RLay (l_calls Q) (l_spill Q) (Some (p1, Z.of_nat (length x) + 1)) (l_reply Q)).
split; [|intros pn; split; intros Hin; exact Hin].
split; [exact Hg8|]. split; [exact Hsc8b|]. split; [exact Hapb|].
destruct HC as (Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6).
split.
{ cbn [l_calls l_spill r_calls r_spill set_answer].
  split; [exact Hc1|]. split; [exact Hc2|].
  split.
  { eapply (hb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_NCALLS) 4
      (Z.of_nat (length (r_calls R))) (A_G_REC + OFF_NCALLS) (A_G_REC + OFF_NCALLS + 4)).
    - apply KREC; unfold OFF_NCALLS, OFF_ANSWER; [lia | lia | left; lia].
    - lia.
    - cbn. lia.
    - exact Hc3. }
  split.
  { intros i c P Hi HP'. cbn [l_calls l_spill l_answer l_reply] in HP', Hi.
    destruct (Hc4 i c P Hi HP') as [Hca Hfa]. split; [|exact Hfa].
    assert (Hi16 : (i < 16)%nat).
    { assert (Hi' : (i < length (l_calls Q))%nat) by (apply nth_error_Some; rewrite HP'; discriminate). lia. }
    apply (HCALLKEEP _ c P).
    - apply (KREC (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i)
        (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + CALL_SIZE));
      [unfold OFF_CALLS, CALL_SIZE; lia | unfold OFF_CALLS, CALL_SIZE; lia
      | left; unfold OFF_CALLS, CALL_SIZE, OFF_ANSWER; lia].
    - intros pn Hpn. apply in_or_app. left. apply in_concat. exists P.
      split; [eapply nth_error_In; exact HP' | exact Hpn].
    - exact Hca. }
  split; [|exact Hc6].
  apply (HCALLKEEP _ (r_spill R) (l_spill Q)).
  - intros b Hb. apply KSPL. unfold CALL_SIZE in Hb. lia.
  - intros pn Hpn. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - exact Hc5. }
split.
{ (* the answer is the first copy *)
  cbn [r_answer set_answer l_answer].
  repeat split.
  - exact Vans3.
  - cbn [fst]. lia.
  - cbn [fst snd]. unfold LIVE_XSTRDUP in Hp1in3. exact Hp1in3.
  - cbn [snd]. lia.
  - cbn [snd]. unfold LMAX in *. lia.
  - cbn [fst]. exact (proj1 Hp1str3).
  - cbn [fst]. exact (proj2 Hp1str3).
  - exact Hlen. }
split.
{ (* the reply is untouched *)
  cbn [r_reply set_answer l_reply].
  revert HPb. destruct (r_reply R) as [y|] eqn:ERY; destruct (l_reply Q) as [[pr nr]|] eqn:ELY;
  try (intros HPb; destruct HPb; fail).
  - intros (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
    assert (Hrne : fst (pr, nr) <> old)
    by (apply HOTH; apply in_or_app; right; apply in_or_app; right;
        first [rewrite ELY | idtac]; cbn [oblk]; left; reflexivity).
    destruct (al_blocks _ _ LAWS ly S W mem md pr nr HAR R5) as (_ & Hr4096 & _ & _ & _ & _ & Hnr0).
    pose proof (req_size_pos nr ltac:(lia)) as [Hrq1 Hrq2].
    assert (HKr : forall b, pr <= b < pr + req_size nr -> rdW W3 mem3 b = rdW W mem b)
    by (intros b Hb; replace b with (pr + (b - pr)) by lia;
        exact (KEEPB pr nr (b - pr) R5 Hrne (HKEEPIN _ R5 Hrne) ltac:(lia))).
    cbn [areply_at fst snd] in *.
    split; [eapply (hb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_REPLY) 8 pr
      (A_G_REC + OFF_REPLY) (A_G_REC + OFF_REPLY + 8));
      [apply KREC; unfold OFF_REPLY, OFF_ANSWER; [lia | lia | right; lia] | lia | cbn; lia | exact R1]|].
    split; [eapply (hb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_REPLY_SIZE) 8
      (Z.of_nat (length y)) (A_G_REC + OFF_REPLY_SIZE) (A_G_REC + OFF_REPLY_SIZE + 8));
      [apply KREC; unfold OFF_REPLY_SIZE, OFF_ANSWER; [lia | lia | right; lia] | lia | cbn; lia | exact R2]|].
    split; [exact R3|]. split; [exact R4|]. split; [exact (HKEEPIN _ R5 Hrne)|]. split; [exact R6|].
    split; [| exact R8].
    exact (hb_abytes_kept_rng (rdW W mem) (rdW W3 mem3) pr y pr (pr + req_size nr) HKr ltac:(lia) ltac:(lia) R7).
  - intros (R1 & R2). cbn [areply_at] in *.
    split; [eapply (hb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_REPLY) 8 0
      (A_G_REC + OFF_REPLY) (A_G_REC + OFF_REPLY + 8));
      [apply KREC; unfold OFF_REPLY, OFF_ANSWER; [lia | lia | right; lia] | lia | cbn; lia | exact R1]|].
    eapply (hb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_REPLY_SIZE) 8 0
      (A_G_REC + OFF_REPLY_SIZE) (A_G_REC + OFF_REPLY_SIZE + 8));
    [apply KREC; unfold OFF_REPLY_SIZE, OFF_ANSWER; [lia | lia | right; lia] | lia | cbn; lia | exact R2]. }
split.
{ (* the scalar fields are untouched *)
  destruct HSC as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  cbn [r_refuse r_code r_nreplies r_state r_host set_answer].
  split; [eapply (hb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_REFUSE) 4 (r_refuse R)
    (A_G_REC + OFF_REFUSE) (A_G_REC + OFF_REFUSE + 4));
    [apply KREC; unfold OFF_REFUSE, OFF_ANSWER; [lia | lia | left; lia] | lia | cbn; lia | exact X1]|].
  split; [eapply (hb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_CODE) 4 (r_code R)
    (A_G_REC + OFF_CODE) (A_G_REC + OFF_CODE + 4));
    [apply KREC; unfold OFF_CODE, OFF_ANSWER; [lia | lia | left; lia] | lia | cbn; lia | exact X2]|].
  split; [eapply (hb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_NREPLIES) 4 (r_nreplies R)
    (A_G_REC + OFF_NREPLIES) (A_G_REC + OFF_NREPLIES + 4));
    [apply KREC; unfold OFF_NREPLIES, OFF_ANSWER; [lia | lia | right; lia] | lia | cbn; lia | exact X3]|].
  split; [eapply (hb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_STATE) 8 (r_state R)
    (A_G_REC + OFF_STATE) (A_G_REC + OFF_STATE + 8));
    [apply KREC; unfold OFF_STATE, OFF_ANSWER; [lia | lia | right; lia] | lia | cbn; lia | exact X4]|].
  split; [eapply (hb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_HOST) 8 (r_host R)
    (A_G_REC + OFF_HOST) (A_G_REC + OFF_HOST + 8));
    [apply KREC; unfold OFF_HOST, OFF_ANSWER; [lia | lia | right; lia] | lia | cbn; lia | exact X5]|].
  split; [exact X6|]. split; [exact X7|]. split; [exact X8|]. split; [exact X9 | exact X10]. }
(* the recorder's own blocks: the answer slot now holds the first copy *)
assert (HNIp1 : ~ In p1 (map fst (concat (l_calls Q) ++ l_spill Q ++ oblk (l_reply Q)))).
{ intros Hin. apply in_map_iff in Hin as (pn & Hfst & Hpn).
  assert (Hne : fst pn <> old) by (apply HOTH; exact Hpn).
  assert (HinS : In pn (ablocks B ly S)) by (apply HObl; apply HOQ; apply hb_rest_lay; exact Hpn).
  assert (Hin1 : In pn (ablocks B ly1 S1))
  by (apply (proj2 (HBL1 _)); split; [exact HinS | rewrite HOeq; exact Hne]).
  destruct (Z.eq_dec (snd pn) (Z.of_nat (length x) + 1)) as [Hsz | Hsz].
  - pose proof (proj1 (Forall_forall _ _) Hp1apart _ Hin1) as Hap. cbv beta in Hap.
    rewrite Hfst, Hsz in Hap. unfold iv_apart, LIVE_XSTRDUP in Hap. lia.
  - assert (Hin2 : In pn (ablocks B ly2 S2))
    by (eapply Permutation_in; [apply Permutation_sym; exact Hp1perm | right; exact Hin1]).
    destruct pn as [pq nq]. cbn [fst snd] in Hfst, Hsz. subst pq.
    assert (Hne2 : (p1, nq) <> (p1, LIVE_XSTRDUP x))
    by (intros Heq; injection Heq as Heq; unfold LIVE_XSTRDUP in Hsz; exact (Hsz Heq)).
    pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 p1 nq p1 _ HAR2 Hin2 Hp1in2 Hne2) as Hd.
    destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p1 nq HAR2 Hin2) as (_ & _ & _ & _ & _ & _ & Hnq0).
    pose proof (req_size_pos nq ltac:(lia)) as [Hq1 Hq2].
    pose proof (req_size_pos (LIVE_XSTRDUP x) ltac:(unfold LIVE_XSTRDUP; lia)) as [Hq3 Hq4].
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
split.
{ unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply oblk].
  rewrite !map_app. cbn [map].
  apply hb_nodup_ins.
  - pose proof (proj1 HOW) as Hnd. unfold lay_blocks in Hnd. rewrite !map_app in Hnd.
    destruct (l_answer Q) as [[pa pk]|] eqn:ELA; cbn [oblk map] in Hnd; [|exact Hnd].
    exact (hb_nodup_del _ _ _ _ Hnd).
  - rewrite <- !map_app. exact HNIp1. }
intros pn Hin. unfold lay_blocks in Hin. cbn [l_calls l_spill l_answer l_reply oblk] in Hin.
apply in_app_or in Hin as [Hc | Hin].
- exact (proj2 HOW pn (hb_rest_lay Q pn (in_or_app _ _ _ (or_introl Hc)))).
- apply in_app_or in Hin as [Hs | Hin].
  + exact (proj2 HOW pn (hb_rest_lay Q pn (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hs)))))).
  + destruct Hin as [Heq | Hr].
    * rewrite <- Heq. cbn [fst snd]. rewrite Hrqn in Hp1off.
      unfold iv_apart, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, LIVE_XSTRDUP in *. split; lia.
    * exact (proj2 HOW pn (hb_rest_lay Q pn
        (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hr)))))).
Qed.

End e.
End f.
End d.
Print Assumptions thand_back_spec_holds.
