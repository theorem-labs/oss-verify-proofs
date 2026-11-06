(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the loop segment of answer's ASan walk (plugin-hostd/fuzz_command, 0x8a4c0):
   syntax_instantiate's loop from its head HEAD (0x8a670) to JOIN (0x8a734), an_head_ok : AN_JOIN_stmt ->
   AN_HEAD_stmt (lib/A/Prog/answer_s1.v), by strong induction on the bytes of the shape left, in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v (tcbb_loopX, a loop with inline checks, re-seeded at each iteration). The
   plain proof of the same loop is lib/Prog/answer.v:120-226 (an_loop). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtStack RtShadow RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import mix_call_c hand_back_c answer_c answer_s1.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
(* lia without the Euclidean-division equations: the flag value these proofs were checked with, which PaDenot.v
   gave them until an earlier commit made its redefinition Local *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at HEAD, one iteration's seed ----
   Every register is its own atom except a3 = '<' and a4 = '>', which are pinned. Atom 10 = a0 and atom 19 = s3 are
   the shape cursor A = sh + j, 11 = a1 = |out|, 12 = a2 = d, 21 = s5 = buf, 26 = s10 = the shadow base; the extra
   atom 32 is buf's cursor P = buf + |out| (the alias says s5 + a1 = P) and 33 the shape byte at A. The regions are
   the shape byte (read only) and buf's byte at P (written). The one shadow entry covers buf's byte at P, so the
   stores' inline checks need nothing; the load's check at HEAD leaves the obligation that A is addressable. *)
Definition al_regs : list sv := sr_set (sr_set sr_atoms 13%bv (SLit 60)) 14%bv (SLit 62).
Definition al_regions : smem :=
[ YP09.mkRegion (Some 19%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))];
  YP09.mkRegion (Some 32%nat) 0 1 0 1 [] ].
Definition al_facts : facts :=
mkFacts [ (10%nat, PTR 0); (19%nat, PTR 0); (11%nat, mkAF 0 4095 0); (12%nat, mkAF 0 8192 0);
          (32%nat, PTR 0); (33%nat, mkAF 0 255 0); (26%nat, mkAF SB SB 0) ]
[] [ (SAlu ALU_ADD (SOff 21 0) (SOff 11 0), SOff 32 0) ].
Definition al_ss : sstate := mkSS AN_HEAD al_regs al_regions None al_facts.
Definition al_Bx : sv := SOff 26 0.
Definition al_SH : list shent := [mkSHE 32 0 1].
(* the registers an iteration does not touch *)
Definition AL_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* ---- the recorder's bytes (a copy of lib/A/Prog/answer_e1.v:93-176, the entry segment of the same walk) ---- *)
Definition al_in_rec (a : Z) : Prop :=
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.
Definition al_rk_set (bl : list (Z * Z)) (a : Z) : Prop :=
al_in_rec a \/ exists p n, In (p, n) bl /\ p <= a < p + n.
Definition al_rkeep (bl : list (Z * Z)) (rd rd' : reader) : Prop :=
forall a, al_rk_set bl a -> rd' a = rd a.
Lemma al_aval_mem_kept_on : forall (rd rd' : reader) a n v,
aval_mem rd a n v -> (forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hlt. rewrite (Hk k Hlt). exact (H k Hlt). Qed.
Lemma al_abytes_atR_kept_on : forall (rd rd' : reader) p l,
abytes_atR rd p l -> (forall i, 0 <= i < Z.of_nat (length l) -> rd' (p + i) = rd (p + i)) -> abytes_atR rd' p l.
Proof. intros rd rd' p l H Hk i Hi. rewrite (Hk (Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma al_astr_atR_kept_on : forall (rd rd' : reader) p s,
astr_atR rd p s -> (forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (p + i) = rd (p + i)) -> astr_atR rd' p s.
Proof.
intros rd rd' p s [H1 H2] Hk. split; [|exact H2]. apply (al_abytes_atR_kept_on rd rd' p _ H1).
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma al_nth_error_lt : forall {A} (l : list A) i x, nth_error l i = Some x -> (i < length l)%nat.
Proof. intros A l i x H. apply nth_error_Some. rewrite H. discriminate. Qed.
Lemma al_rec_repA_kept : forall B ly S ly' S' (rd rd' : reader) R O,
rec_repA B ly S rd R O -> al_rkeep (ablocks B ly S) rd rd' -> ablocks B ly' S' = ablocks B ly S ->
rec_repA B ly' S' rd' R O.
Proof.
intros B ly S ly' S' rd rd' R O (Q & HA & HO) HK Eab. exists Q. split; [|exact HO]. rewrite Eab.
set (bl := ablocks B ly S) in *.
assert (KR : forall a, al_in_rec a -> rd' a = rd a) by (intros a Ha; apply HK; left; exact Ha).
assert (KB : forall p n i, In (p, n) bl -> 0 <= i < n -> rd' (p + i) = rd (p + i))
by (intros p n i Hin Hi; apply HK; right; exists p, n; split; [exact Hin | lia]).
assert (KV : forall a n v, (forall k, (k < n)%nat -> al_in_rec (a + Z.of_nat k)) -> aval_mem rd a n v -> aval_mem rd' a n v)
by (intros a n v Hr Hv; apply (al_aval_mem_kept_on rd rd' a n v Hv); intros k Hk; apply KR, Hr, Hk).
assert (KT : forall pn s, In pn bl -> Z.of_nat (length s) + 1 <= snd pn -> astr_atR rd (fst pn) s -> astr_atR rd' (fst pn) s).
{ intros [p n] s Hin Hl Hs. cbn [fst snd] in *. apply (al_astr_atR_kept_on rd rd' p s Hs). intros i Hi. apply (KB p n i Hin). lia. }
assert (KY : forall pn l, In pn bl -> Z.of_nat (length l) <= snd pn -> abytes_atR rd (fst pn) l -> abytes_atR rd' (fst pn) l).
{ intros [p n] l Hin Hl Hs. cbn [fst snd] in *. apply (al_abytes_atR_kept_on rd rd' p l Hs). intros i Hi. apply (KB p n i Hin). lia. }
assert (KC : forall a c P, (forall o, 0 <= o < CALL_SIZE -> al_in_rec (a + o)) -> acall_at bl rd a c P -> acall_at bl rd' a c P).
{ intros a c P Ha (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold acall_at.
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
  split; [apply KV; [intros k Hk; rewrite <- Z.add_assoc; apply Ha; unfold CALL_OFF_FN, CALL_SIZE; lia | exact C4]|].
  split; [apply KV; [intros k Hk; rewrite <- Z.add_assoc; apply Ha; unfold CALL_OFF_NARGS, CALL_SIZE; lia | exact C5]|].
  split; [exact C6|].
  intros k s pn Hs Hp. destruct (C7 k s pn Hs Hp) as (D1 & D2 & D3 & D4 & D5).
  assert (Hk6 : (k < 6)%nat) by (pose proof (al_nth_error_lt _ _ _ Hs); lia).
  split; [apply KV; [intros j Hj; rewrite <- !Z.add_assoc; apply Ha; unfold CALL_OFF_ARGS, CALL_SIZE; lia | exact D1]|].
  split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. exact (KT pn s D3 ltac:(lia) D5). }
destruct HA as (Hg8 & Hs8 & Hap & HC & HAn & HRp & HSc & HOwn).
unfold arep_at. split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ destruct HC as (C1 & C2 & C3 & C4 & C5 & C6). split; [exact C1|]. split; [exact C2|].
  split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_NCALLS, REC_SIZE; lia | exact C3]|].
  split.
  - intros i c P Hc HP. destruct (C4 i c P Hc HP) as [D1 D2]. split; [|exact D2].
    assert (Hi : (i < 16)%nat) by (pose proof (al_nth_error_lt _ _ _ Hc); lia).
    apply KC; [|exact D1]. intros o Ho. left. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
  - split; [|exact C6]. apply KC; [|exact C5]. intros o Ho. right. unfold A_REC_SPILL, CALL_SIZE, SC_SIZE in *. lia. }
split.
{ unfold aanswer_at in *. destruct (r_answer R) as [x|]; destruct (l_answer Q) as [pn|]; try exact HAn.
  - destruct HAn as (A1 & A2 & A3 & A4 & A5 & A6).
    split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_ANSWER, REC_SIZE; lia | exact A1]|].
    split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact (KT pn x A3 ltac:(lia) A5) | exact A6].
  - apply KV; [intros k Hk; left; unfold A_G_REC, OFF_ANSWER, REC_SIZE; lia | exact HAn]. }
split.
{ unfold areply_at in *. destruct (r_reply R) as [x|]; destruct (l_reply Q) as [pn|]; try exact HRp.
  - destruct HRp as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_REPLY, REC_SIZE; lia | exact A1]|].
    split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_REPLY_SIZE, REC_SIZE; lia | exact A2]|].
    split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
    split; [exact (KY pn x A5 ltac:(lia) A7) | exact A8].
  - destruct HRp as [A1 A2].
    split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_REPLY, REC_SIZE; lia | exact A1]|].
    apply KV; [intros k Hk; left; unfold A_G_REC, OFF_REPLY_SIZE, REC_SIZE; lia | exact A2]. }
split; [|exact HOwn].
destruct HSc as (S1 & S2 & S3 & S4 & S5 & S6).
split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_REFUSE, REC_SIZE; lia | exact S1]|].
split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_CODE, REC_SIZE; lia | exact S2]|].
split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_NREPLIES, REC_SIZE; lia | exact S3]|].
split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_STATE, REC_SIZE; lia | exact S4]|].
split; [apply KV; [intros k Hk; left; unfold A_G_REC, OFF_HOST, REC_SIZE; lia | exact S5]|].
exact S6.
Qed.

(* ---- the shape: the instantiated text has no NUL byte (lib/Prog/answer.v:679-690) ---- *)
Lemma al_inst_go_no0 : forall s d, no0 s -> no0 (inst_go d s).
Proof.
unfold no0. induction s as [|b s IH]; intros d H; cbn [inst_go]; [intro F; exact F|].
assert (Hs : ~ In (Z_to_bv 8 0) s) by (intro F; apply H; right; exact F).
assert (Hb : b <> Z_to_bv 8 0) by (intro E; apply H; left; exact E).
destruct d as [|d'].
- destruct (bv_unsigned b =? 60).
  + intros [E|F]; [vm_compute in E; discriminate E | exact (IH 1%nat Hs F)].
  + intros [E|F]; [exact (Hb E) | exact (IH O Hs F)].
- destruct (bv_unsigned b =? 60); [exact (IH _ Hs)|].
  destruct (bv_unsigned b =? 62); exact (IH _ Hs).
Qed.
Lemma al_skipn_nth : forall {X} (l : list X) j d, (j < length l)%nat -> skipn j l = nth j l d :: skipn (S j) l.
Proof.
intros X l. induction l as [|y l IH]; intros j d H; [cbn in H; lia|].
destruct j as [|j]; [reflexivity|]. cbn [skipn nth length] in *. apply IH. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the environment of an iteration: the registers at HEAD, then P and the shape byte *)
Definition al_E (regs1 : bvmap 5 word) (P Cz : Z) : env := Eimg (Ereg regs1 [Z_to_bv 64 P; Z_to_bv 64 Cz]).

Lemma al_ew_reg : forall regs1 P Cz n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (al_E regs1 P Cz) n = getr regs1 r.
Proof.
intros regs1 P Cz n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold al_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma al_ew32 : forall regs1 P Cz, ew (al_E regs1 P Cz) 32 = Z_to_bv 64 P.
Proof. intros. unfold al_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 0). Qed.
Lemma al_ew33 : forall regs1 P Cz, ew (al_E regs1 P Cz) 33 = Z_to_bv 64 Cz.
Proof. intros. unfold al_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 1). Qed.
Lemma al_env_agree : forall regs1 P Cz, env_agree 32 (Ereg regs1 [Z_to_bv 64 P; Z_to_bv 64 Cz]) (al_E regs1 P Cz).
Proof. intros. split; [intros n Hn; unfold al_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the read-only range is fixed (CmdGlob.v CMD_RLO / CMD_RHI) *)
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis LAWS : AR_laws SEGS B.

(* the seed of an iteration *)
Lemma al_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc A O D F P Cz,
getr regs1 10 = w64 A -> getr regs1 19 = w64 A -> getr regs1 11 = w64 O -> getr regs1 12 = w64 D ->
getr regs1 13 = w64 60 -> getr regs1 14 = w64 62 -> getr regs1 21 = w64 (F + 32) -> getr regs1 26 = w64 SB ->
4096 <= A <= 140737479966720 -> 0 <= O <= 4095 -> 0 <= D <= 8192 -> P = F + 32 + O -> 0 <= F ->
4096 <= P <= 140737479966720 -> 0 <= Cz <= 255 ->
rdW W memc A = Some Cz -> apresent (w_H W) memc P -> (A + 1 <= P \/ P + 1 <= A) ->
st_ok_pi SEGS VAL (al_E regs1 P Cz) al_ss (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + AN_HEAD)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc A O D F P Cz H10 H19 H11 H12 H13 H14 H21 H26 HA HO HD HP HF HPr HC HrdA HpP Hdisj.
set (E := al_E regs1 P Cz).
assert (E10 : ew E 10 = Z_to_bv 64 A) by (subst E; rewrite (al_ew_reg regs1 P Cz 10 10%bv eq_refl); exact H10).
assert (E19 : ew E 19 = Z_to_bv 64 A) by (subst E; rewrite (al_ew_reg regs1 P Cz 19 19%bv eq_refl); exact H19).
assert (E11 : ew E 11 = Z_to_bv 64 O) by (subst E; rewrite (al_ew_reg regs1 P Cz 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 D) by (subst E; rewrite (al_ew_reg regs1 P Cz 12 12%bv eq_refl); exact H12).
assert (E21 : ew E 21 = Z_to_bv 64 (F + 32)) by (subst E; rewrite (al_ew_reg regs1 P Cz 21 21%bv eq_refl); exact H21).
assert (E26 : ew E 26 = Z_to_bv 64 SB) by (subst E; rewrite (al_ew_reg regs1 P Cz 26 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 P) by (subst E; apply al_ew32).
assert (E33 : ew E 33 = Z_to_bv 64 Cz) by (subst E; apply al_ew33).
rewrite restrict_mkst_fx. unfold al_ss. apply pa_entry_st_ok_full.
- unfold al_regs. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H13] | intros X; discriminate X | cbn [sv_denot]; exact H14].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
    destruct (aview_byte SEGS (w_H W) memc A Cz HrdA) as (b & Hb & Hv & _).
    exists b. split.
    * cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E33.
      rewrite !Z.add_0_r, (unsigned_lit_small Cz), (unsigned_lit_small Cz) by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
      subst Cz. apply Z_to_bv_bv_unsigned.
    * rewrite !Z.add_0_r. exact Hb.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. assert (o = 0) as -> by lia. rewrite Z.add_0_r. apply (apresent_writable SEGS). exact HpP.
- unfold al_regions. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  rewrite E19, E32, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [al_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite E10, E19, E11, E12, E32, E33, E26, !unsigned_lit_small by (unfold SB; lia).
    rewrite Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
  + cbn [al_facts f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom _ 21 (F + 32) E21), (U_atom _ 11 O E11), (U_atom _ 32 P E32) by lia.
    subst P. apply zcanon_id. unfold M64. lia.
Qed.

(* the shadow entry: buf's byte at P is addressable and is not a shadow byte *)
Lemma al_shok : forall (W : world SEGS) (regs1 : bvmap 5 word) memc P Cz,
getr regs1 26 = w64 SB -> 4096 <= P < 2 ^ 47 ->
range_addressable (rdW W memc) SHADOW_OFF P 1 -> ~ (SB <= P < SB + 17592186044416) ->
sh_ok SEGS al_Bx al_SH (al_E regs1 P Cz) (mrestrict (w_H W) memc).
Proof.
intros W regs1 memc P Cz H26 HP Hra Hap.
assert (E26 : ew (al_E regs1 P Cz) 26 = Z_to_bv 64 SB) by (rewrite (al_ew_reg regs1 P Cz 26 26%bv eq_refl); exact H26).
assert (UB : U (al_E regs1 P Cz) al_Bx = SB) by (unfold al_Bx; apply (U_atom _ 26 SB E26); unfold SB; lia).
assert (UP : U (al_E regs1 P Cz) (SOff 32 0) = P) by (apply (U_atom _ 32 P (al_ew32 regs1 P Cz)); lia).
constructor; [|constructor]. split.
- cbn [she_m she_lo she_hi]. rewrite UB, UP, Z.add_0_r. change (1 - 0) with 1. rewrite SB_SHADOW_OFF. exact Hra.
- intros a. cbn [she_m she_lo she_hi]. rewrite UB, UP. change (Z.min 0 1) with 0. change (Z.max 0 1) with 1. lia.
Qed.

(* the writes of an iteration: buf's byte at P, in answer's own frame *)
Lemma al_awr : forall E cs0 cs1 STK sp0 FP bl0 blc fr0 lyc pos,
frame_addr lyc 7 pos <= bv_unsigned (ew E 32) < frame_addr lyc 7 pos + fs_frame_bytes 7 ->
awr_ok SEGS B E [YP09.mkRegion (Some 19%nat) 0 1 0 0 cs0; YP09.mkRegion (Some 32%nat) 0 1 0 1 cs1]
STK sp0 FP bl0 blc fr0 lyc [(7, pos)].
Proof.
intros E cs0 cs1 STK sp0 FP bl0 blc fr0 lyc pos HP.
eapply awr_ok_cons_gen; [reflexivity | reflexivity | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; lia |].
eapply awr_ok_cons_gen; [reflexivity | reflexivity | | apply awr_ok_nil].
cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. left.
exists 7, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* ---- what an iteration knows about answer's frame, the shape and the stack ---- *)
Lemma al_iter_facts : forall ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc memc mdc pos sp1 j d out,
an_pre B MT ly S W regs mem md ch c sh old e x chg R O -> r_refuse R = 0 ->
an_mid B MT ly S W regs mem md (an_R1 R e chg) old O lyc Sc Wc memc mdc pos 0 sp1 ->
out ++ inst_go d (skipn j x) = inst x ->
4096 <= frame_addr lyc 7 pos /\ frame_addr lyc 7 pos + 8192 <= alloc_ceiling /\ frame_addr lyc 7 pos mod 32 = 0 /\
off_img (frame_addr lyc 7 pos) 8192 /\ in_app (frame_addr lyc 7 pos) 8192 /\
(forall a, frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8192 -> apresent (w_H Wc) memc a) /\
(forall b k a, In (b, k) (ablocks B lyc Sc) -> b <= a < b + k ->
  0 <= a < alloc_ceiling /\ ~ (frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8192)) /\
4096 <= sh /\ sh + Z.of_nat (length x) + 1 <= alloc_ceiling /\
(forall a, sh <= a < sh + Z.of_nat (length x) + 1 -> ~ (frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8192)) /\
Z.of_nat (length (inst x)) <= 4095 /\ Z.of_nat (length out) <= 4095 /\ Z.of_nat (length x) <= 8192 /\ no0 x /\
alloc_ceiling + 256 <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
intros ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc memc mdc pos sp1 j d out HPRE Href HMID Hinv.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HPRE as (HFN & _ & _ & _ & _ & _ & _ & _ & _ & HSTR & _).
destruct (HSTR Href) as (HARG & HFIT).
pose proof HFN as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (WS : 4096 <= ANSWER_STK) by (unfold ANSWER_STK, ESTACK; lia).
destruct HMID as (HJ & _ & Hperm & _).
pose proof (proj1 HJ) as HAR.
assert (Hin : In (7, pos) (frames Sc)).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfr & _). rewrite Hfr. left. reflexivity. }
assert (FB : fs_frame_bytes 7 = 8192) by reflexivity.
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 7 pos HAR Hin) as (Hf1 & Hf2 & Hf3). rewrite FB in Hf2, Hf3.
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 7 pos HAR Hin) as (Hf32 & _ & Hfp & _). rewrite FB in Hfp.
pose proof (frm_off_imgP B lyc Sc Wc memc mdc 7 pos HAR Hin) as Hoff. rewrite FB in Hoff.
assert (HBLK : forall b k a, In (b, k) (ablocks B lyc Sc) -> b <= a < b + k ->
  0 <= a < alloc_ceiling /\ ~ (frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8192)).
{ intros b k a Hbk Ha.
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b k HAR Hbk) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hk).
  pose proof (req_size_pos k ltac:(lia)) as [_ Hrk].
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b k 7 pos HAR Hbk Hin) as Hsep.
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite FB in Hsep. lia. }
assert (HL : (length out <= length (inst x))%nat) by (rewrite <- Hinv, length_app; lia).
unfold fits, PHD_LINE_MAX in HFIT.
destruct HARG as (Hsh0 & HSX & Hn & Hloc).
assert (HSH : 4096 <= sh /\ sh + Z.of_nat (length x) + 1 <= alloc_ceiling /\
  (forall a, sh <= a < sh + Z.of_nat (length x) + 1 -> ~ (frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8192))).
{ destruct Hloc as [[(p & k & Hpk & Hp1 & Hp2) _] | (HRO & _ & _)].
  - assert (Hpk' : In (p, k) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hpk).
    destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p k HAR Hpk') as (_ & Hp4096 & Hpceil & _ & _ & _ & Hk).
    pose proof (req_size_pos k ltac:(lia)) as [_ Hrk].
    split; [lia|]. split; [lia|]. intros a Ha. exact (proj2 (HBLK p k a Hpk' ltac:(lia))).
  - assert (Himg : forall i, 0 <= i < Z.of_nat (length x) + 1 -> 0x10000 <= sh + i < 0x606000).
    { intros i Hi. destruct (proj1 (HRO i Hi)) as [(s & Hs & _ & Hs1) | Hr].
      - apply pa_img_range. exists s. split; [exact Hs | lia].
      - unfold CMD_RLO, CMD_RHI in Hr. lia. }
    pose proof (Himg 0 ltac:(lia)) as I0. pose proof (Himg (Z.of_nat (length x)) ltac:(lia)) as I1.
    split; [lia|]. split; [lia|]. intros a Ha. pose proof (Himg (a - sh) ltac:(lia)) as Ia.
    unfold off_img in Hoff. lia. }
destruct HSH as (HS1 & HS2 & HS3).
split; [lia|]. split; [lia|]. split; [exact Hf32|]. split; [exact Hoff|]. split; [exact Hf3|].
split; [intros a Ha; exact (proj1 (Hfp a Ha))|]. split; [exact HBLK|].
split; [exact HS1|]. split; [exact HS2|]. split; [exact HS3|].
split; [lia|]. split; [lia|]. split; [unfold LMAX in Hn; lia|]. split; [exact (proj2 HSX)|]. lia.
Qed.

(* ---- the body invariant survives a step that writes only buf's byte at P ---- *)
Lemma al_mid_kept : forall ly S W regs mem md R1 old O lyc Sc Wc memc mdc memc' mdc' pos sp1 Pz,
an_mid B MT ly S W regs mem md R1 old O lyc Sc Wc memc mdc pos 0 sp1 ->
ajournal SEGS B ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [(7, pos)] lyc Sc Wc memc' mdc' 0 ->
(forall a, 0 <= a < 2 ^ 64 -> a <> Pz -> rdW Wc memc' a = rdW Wc memc a) ->
frame_addr lyc 7 pos + 32 <= Pz < frame_addr lyc 7 pos + 32 + 4096 ->
4096 <= frame_addr lyc 7 pos -> frame_addr lyc 7 pos + 8192 <= alloc_ceiling ->
off_img (frame_addr lyc 7 pos) 8192 -> in_app (frame_addr lyc 7 pos) 8192 ->
(forall b k a, In (b, k) (ablocks B lyc Sc) -> b <= a < b + k ->
  0 <= a < alloc_ceiling /\ ~ (frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8192)) ->
alloc_ceiling + 256 <= spZ regs -> spZ regs <= 2 ^ 47 ->
an_mid B MT ly S W regs mem md R1 old O lyc Sc Wc memc' mdc' pos 0 sp1.
Proof.
intros ly S W regs mem md R1 old O lyc Sc Wc memc mdc memc' mdc' pos sp1 Pz HMID HJ' KEEP HP HF1 HF2 Hoff Happ Hblk Hsp0 Hsp1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HMID as (HJ & Hmo & Hperm & Hsp & Hsaved & Hflag & Hzero & Hrep & Hans).
set (F := frame_addr lyc 7 pos) in *.
unfold off_img in Hoff. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
split; [exact HJ'|]. split; [exact Hmo|]. split; [exact Hperm|]. split; [exact Hsp|].
split.
{ intros jj r Hr. apply (al_aval_mem_kept_on _ _ _ _ _ (Hsaved jj r Hr)). intros k Hk.
  pose proof (al_nth_error_lt _ _ _ Hr) as Hjj. change (length an_saved) with 13%nat in Hjj.
  apply KEEP; lia. }
split.
{ change (fs_frame_bytes 7) with 8192 in *.
  rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc')); [exact Hflag|]. intros k Hk. apply KEEP; lia. }
split.
{ intros i Hi. change (4096 / 8) with 512 in Hi.
  pose proof (Z.div_mod (F + 32) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (F + 32) 8 ltac:(lia)) as MB.
  assert (KS : 0 <= shadow_of_addr SHADOW_OFF (F + 32) + i < 2 ^ 64 /\ shadow_of_addr SHADOW_OFF (F + 32) + i <> Pz)
    by (unfold shadow_of_addr, SHADOW_OFF; lia).
  etransitivity; [exact (KEEP _ (proj1 KS) (proj2 KS)) | exact (Hzero i Hi)]. }
split.
{ apply (al_rec_repA_kept B lyc Sc lyc Sc _ _ _ _ Hrep); [|reflexivity].
  intros a [Ha | (b & k & Hbk & Ha)].
  - unfold al_in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha. apply KEEP; lia.
  - destruct (Hblk b k a Hbk Ha) as [Ha1 Ha2]. apply KEEP; lia. }
apply (al_aval_mem_kept_on _ _ _ _ _ Hans). intros k Hk. unfold A_G_REC, OFF_ANSWER. apply KEEP; lia.
Qed.

(* buf's bytes after a step: `out` stays, and a written byte extends it *)
Lemma al_out_kept : forall (rd rd' : reader) Fb out out' Pz,
abytes_atR rd Fb out -> Pz = Fb + Z.of_nat (length out) -> 0 <= Fb -> Pz < 2 ^ 64 ->
(forall a, 0 <= a < 2 ^ 64 -> a <> Pz -> rd' a = rd a) ->
(out' = out \/ exists b, out' = out ++ [b] /\ rd' Pz = Some (bv_unsigned b)) ->
abytes_atR rd' Fb out'.
Proof.
intros rd rd' Fb out out' Pz HO HP HF HP64 KEEP [-> | (b & -> & Hb)].
- apply (al_abytes_atR_kept_on rd rd' Fb out HO). intros i Hi. apply KEEP; lia.
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.eq_dec i (length out)) as [->|Hne].
  + rewrite app_nth2, Nat.sub_diag by lia. cbn [nth]. rewrite <- HP. exact Hb.
  + rewrite app_nth1 by lia. rewrite KEEP by lia. apply HO. lia.
Qed.

(* ---- an iteration that ends at HEAD with one byte of the shape consumed ---- *)
Definition an_head_n (n : nat) : Prop :=
forall ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1 j d out,
(length x - j = n)%nat ->
an_pre B MT ly S W regs mem md ch c sh old e x chg R O -> r_refuse R = 0 ->
an_mid B MT ly S W regs mem md (an_R1 R e chg) old O lyc Sc Wc memc mdc pos 0 sp1 ->
an_regs_body B regs regs1 sp1 (frame_addr lyc 7 pos) -> getr regs1 27 = w64 A_G_REC ->
(j <= length x)%nat -> (d <= j)%nat -> out ++ inst_go d (skipn j x) = inst x ->
getr regs1 10 = w64 (sh + Z.of_nat j) -> getr regs1 19 = w64 (sh + Z.of_nat j) ->
getr regs1 11 = w64 (Z.of_nat (length out)) -> getr regs1 12 = w64 (Z.of_nat d) ->
getr regs1 13 = w64 60 -> getr regs1 14 = w64 62 ->
abytes_atR (rdW Wc memc) (frame_addr lyc 7 pos + 32) out ->
astr_atR (rdW Wc memc) sh x ->
range_addressable (rdW Wc memc) SHADOW_OFF sh (Z.of_nat (length x) + 1) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AN_HEAD)) memc (seg_rom SEGS)) mdc)
(an_post B MT regs ly S W mem md R e x chg old O).

Lemma al_regs_body_kept : forall regs regs1 regs1' sp1 F,
an_regs_body B regs regs1 sp1 F -> (forall r, In r AL_KEPT -> getr regs1' r = getr regs1 r) ->
an_regs_body B regs regs1' sp1 F.
Proof.
intros regs regs1 regs1' sp1 F (R2 & R3 & R4 & R8 & R9 & R18 & R25 & R20 & R21 & R22 & R23 & R24 & R26) K.
unfold an_regs_body.
rewrite !K by (cbv [AL_KEPT In]; tauto).
repeat split; assumption.
Qed.

Lemma al_reenter : forall n, an_head_n n ->
forall ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1 j d out regs1' memc' mdc' d' out',
(length x - Datatypes.S j = n)%nat ->
an_pre B MT ly S W regs mem md ch c sh old e x chg R O -> r_refuse R = 0 ->
an_mid B MT ly S W regs mem md (an_R1 R e chg) old O lyc Sc Wc memc mdc pos 0 sp1 ->
an_regs_body B regs regs1 sp1 (frame_addr lyc 7 pos) -> getr regs1 27 = w64 A_G_REC ->
(Datatypes.S j <= length x)%nat -> out ++ inst_go d (skipn j x) = inst x ->
(d' <= Datatypes.S j)%nat -> out' ++ inst_go d' (skipn (Datatypes.S j) x) = inst x ->
abytes_atR (rdW Wc memc) (frame_addr lyc 7 pos + 32) out ->
astr_atR (rdW Wc memc) sh x ->
range_addressable (rdW Wc memc) SHADOW_OFF sh (Z.of_nat (length x) + 1) ->
ajournal SEGS B ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [(7, pos)] lyc Sc Wc memc' mdc' 0 ->
(forall a, 0 <= a < 2 ^ 64 -> a <> frame_addr lyc 7 pos + 32 + Z.of_nat (length out) -> rdW Wc memc' a = rdW Wc memc a) ->
(out' = out \/ exists b, out' = out ++ [b] /\
  rdW Wc memc' (frame_addr lyc 7 pos + 32 + Z.of_nat (length out)) = Some (bv_unsigned b)) ->
(forall r, In r AL_KEPT -> getr regs1' r = getr regs1 r) ->
getr regs1' 10 = w64 (sh + Z.of_nat (Datatypes.S j)) -> getr regs1' 19 = w64 (sh + Z.of_nat (Datatypes.S j)) ->
getr regs1' 11 = w64 (Z.of_nat (length out')) -> getr regs1' 12 = w64 (Z.of_nat d') ->
getr regs1' 13 = w64 60 -> getr regs1' 14 = w64 62 ->
SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + AN_HEAD)) memc' (seg_rom SEGS)) mdc')
(an_post B MT regs ly S W mem md R e x chg old O).
Proof.
intros n IH ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1 j d out regs1' memc' mdc' d' out'
Hn HPRE Href HMID HRB H27 Hj Hinv Hd' Hinv' HOUT HX HRA HJ' KEEP HW HK N10 N19 N11 N12 N13 N14.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_iter_facts ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc memc mdc pos sp1 j d out HPRE Href HMID Hinv)
as (HF1 & HF2 & HF32 & Hoff & Happ & HFp & HBLK & HS1 & HS2 & HS3 & HIL & HOL & HXL & HX0 & Hsp0 & Hsp1).
set (F := frame_addr lyc 7 pos) in *.
assert (Happ' := Happ). unfold off_img in Hoff. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ'.
set (Pz := F + 32 + Z.of_nat (length out)) in *.
eapply (IH ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1' memc' mdc' pos sp1 (Datatypes.S j) d' out'); try assumption.
- exact (al_mid_kept ly S W regs mem md _ old O lyc Sc Wc memc mdc memc' mdc' pos sp1 Pz HMID HJ' KEEP
    ltac:(subst Pz; lia) HF1 HF2 Hoff Happ HBLK Hsp0 Hsp1).
- exact (al_regs_body_kept regs regs1 regs1' sp1 F HRB HK).
- rewrite (HK 27%bv) by (cbv [AL_KEPT In]; tauto). exact H27.
- apply (al_out_kept (rdW Wc memc) (rdW Wc memc') (F + 32) out out' Pz HOUT); [reflexivity | lia | lia | exact KEEP | exact HW].
- apply (al_astr_atR_kept_on _ _ sh x HX). intros i Hi. apply KEEP; [lia|].
  intros E. apply (HS3 (sh + i)); [lia|]. subst Pz. lia.
- apply (range_addressable_agree (rdW Wc memc) (rdW Wc memc') SHADOW_OFF sh _); [|exact HRA].
  intros y Hy. pose proof (Z.div_mod y 8 ltac:(lia)) as DMy. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as MBy.
  unfold shadow_of_addr, SHADOW_OFF. apply KEEP; [lia|]. subst Pz. lia.
Qed.

(* ---- the loop's exit: buf holds inst x and its terminator ---- *)
Lemma al_exit : AN_JOIN_stmt B MT ->
forall ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1 out regs1' memc' mdc',
an_pre B MT ly S W regs mem md ch c sh old e x chg R O -> r_refuse R = 0 ->
an_mid B MT ly S W regs mem md (an_R1 R e chg) old O lyc Sc Wc memc mdc pos 0 sp1 ->
an_regs_body B regs regs1 sp1 (frame_addr lyc 7 pos) -> getr regs1 27 = w64 A_G_REC ->
out = inst x ->
abytes_atR (rdW Wc memc) (frame_addr lyc 7 pos + 32) out ->
ajournal SEGS B ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [(7, pos)] lyc Sc Wc memc' mdc' 0 ->
(forall a, 0 <= a < 2 ^ 64 -> a <> frame_addr lyc 7 pos + 32 + Z.of_nat (length out) -> rdW Wc memc' a = rdW Wc memc a) ->
rdW Wc memc' (frame_addr lyc 7 pos + 32 + Z.of_nat (length out)) = Some 0 ->
(forall r, In r AL_KEPT -> getr regs1' r = getr regs1 r) ->
SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + AN_JOIN)) memc' (seg_rom SEGS)) mdc')
(an_post B MT regs ly S W mem md R e x chg old O).
Proof.
intros HJOIN ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1 out regs1' memc' mdc'
HPRE Href HMID HRB H27 Hout HOUT HJ' KEEP H0 HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hinv : out ++ inst_go 0 (skipn (length x) x) = inst x) by (rewrite skipn_all, app_nil_r; exact Hout).
destruct (al_iter_facts ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc memc mdc pos sp1 _ _ out HPRE Href HMID Hinv)
as (HF1 & HF2 & HF32 & Hoff & Happ & HFp & HBLK & HS1 & HS2 & HS3 & HIL & HOL & HXL & HX0 & Hsp0 & Hsp1).
set (F := frame_addr lyc 7 pos) in *.
set (Pz := F + 32 + Z.of_nat (length out)) in *.
apply (HJOIN ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1' memc' mdc' pos sp1 HPRE).
- exact (al_mid_kept ly S W regs mem md _ old O lyc Sc Wc memc mdc memc' mdc' pos sp1 Pz HMID HJ' KEEP
    ltac:(subst Pz; lia) HF1 HF2 Hoff Happ HBLK Hsp0 Hsp1).
- exact (al_regs_body_kept regs regs1 regs1' sp1 F HRB HK).
- rewrite (HK 27%bv) by (cbv [AL_KEPT In]; tauto). exact H27.
- unfold rec_answer. rewrite Href. cbn [Z.eqb hand_back snd]. rewrite <- Hout. split.
  + apply (al_out_kept (rdW Wc memc) (rdW Wc memc') (F + 32) out (out ++ [Z_to_bv 8 0]) Pz HOUT);
      [reflexivity | lia | lia | exact KEEP | right; exists (Z_to_bv 8 0); split; [reflexivity | exact H0]].
  + rewrite Hout. exact (al_inst_go_no0 x 0 HX0).
Qed.

(* ---- the facts the symbolic runs of an iteration leave ---- *)
(* a run writes at most buf's byte at P (the windows of the two regions) *)
Lemma al_keep_step : forall E cs0 cs1 (m0 m m' : word -> option byte) (H : word -> bool) Pz,
frame_of E [YP09.mkRegion (Some 19%nat) 0 1 0 0 cs0; YP09.mkRegion (Some 32%nat) 0 1 0 1 cs1] (mrestrict H m) (mrestrict H m') ->
bv_unsigned (ew E 32) = Pz ->
(forall a, 0 <= a < 2 ^ 64 -> a <> Pz -> aview SEGS H m a = aview SEGS H m0 a) ->
forall a, 0 <= a < 2 ^ 64 -> a <> Pz -> aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E cs0 cs1 m0 m m' H Pz HFr H32 KM a Ha Hn.
assert (HW : forall b wlo whi a', In (b, wlo, whi) (windows [YP09.mkRegion (Some 19%nat) 0 1 0 0 cs0; YP09.mkRegion (Some 32%nat) 0 1 0 1 cs1]) ->
  base_val E b + wlo <= a' < base_val E b + whi -> a' = Pz).
{ intros b wlo whi a' Hin Hr. cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hr; lia. }
rewrite (kept_of_frame (segs := SEGS) E _ H m m' (fun a' => a' = Pz) HFr HW a Ha Hn). exact (KM a Ha Hn).
Qed.
(* the byte a run wrote at P *)
Lemma al_wbyte : forall E ss ms (H : word -> bool) Pz v,
st_ok_pi SEGS VAL E ss (restrict H ms) ->
nth_error (ss_mem ss) 1 = Some (YP09.mkRegion (Some 32%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 v)]) ->
bv_unsigned (ew E 32) = Pz ->
aview SEGS H (ms_mem ms) Pz = Some (bv_unsigned (sv_denot E v) mod 256).
Proof.
intros E ss ms H Pz v HS Hn H32.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) 1 _ HS Hn) as Hr.
pose proof (field_of_region_any E _ 32 Pz _ 0 1 0 1 0 1%N v Hr H32 (or_introl eq_refl) ltac:(lia)) as V.
cbn [ms_mem restrict] in V. rewrite Z.add_0_r in V. change (2 ^ (8 * Z.of_N 1)) with 256 in V.
apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.
Lemma al_ag32 : forall (regs1 : bvmap 5 word) extra E0 E,
env_agree 32 (Ereg regs1 extra) E0 -> env_agree 34 E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma al_ag_ew : forall E0 E n v, env_agree 34 E0 E -> (n < 34)%nat -> ew E0 n = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E0 E n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
Lemma al_u32 : forall E0 E P, env_agree 34 E0 E -> ew E0 32 = Z_to_bv 64 P -> 0 <= P < 2 ^ 64 -> bv_unsigned (ew E 32) = P.
Proof. intros E0 E P H H0 HP. rewrite (proj1 H 32%nat ltac:(lia)), H0. apply unsigned_lit_small. exact HP. Qed.
Lemma al_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. reflexivity. Qed.
(* the branches of an iteration *)
Lemma al_br_eq : forall E n v z b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = b -> (v =? z) = b.
Proof.
intros E n v z b H Hv Hz Hc. rewrite (al_den_off E n v 0 H Hv), Z.add_0_r in Hc. cbn [sv_denot] in Hc.
rewrite YO0c.branch_eq, !unsigned_lit_small in Hc by lia. exact Hc.
Qed.
Lemma al_br_lt : forall E n v b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = b -> (0 <? v) = b.
Proof.
intros E n v b H Hv Hc. rewrite (al_den_off E n v 0 H ltac:(lia)), Z.add_0_r in Hc. cbn [sv_denot] in Hc.
rewrite YO0c.branch_lt, !unsigned_lit_small, !YO0b.s64_small in Hc by lia. exact Hc.
Qed.
Lemma al_br_ge : forall E n v b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = b -> negb (0 <? v) = b.
Proof.
intros E n v b H Hv Hc. rewrite (al_den_off E n v 0 H ltac:(lia)), Z.add_0_r in Hc. cbn [sv_denot] in Hc.
rewrite YO0c.branch_ge, !unsigned_lit_small, !YO0b.s64_small in Hc by lia. exact Hc.
Qed.
(* the buffer-full test `srli a7,a6,12; bnez a7` before a store: |out| + 1 < 4096 *)
Lemma al_br_srl : forall E n v b, ew E n = Z_to_bv 64 v -> 0 <= v -> v + 1 < 4096 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_SRL (SOff n 1) (SLit 12))) (sv_denot E (SLit 0)) = b -> b = false.
Proof.
intros E n v b H Hv Hv1 Hc. rewrite branch_ne_U, U_SAlu, (U_atom_off E n v 1 H) in Hc by lia.
rewrite !U_lit in Hc by lia. cbn [zalu_raw] in Hc. change (Z.land 12 63) with 12 in Hc.
rewrite Z.shiftr_div_pow2 in Hc by lia. change (2 ^ 12) with 4096 in Hc. rewrite Z.div_small in Hc by lia.
rewrite <- Hc. reflexivity.
Qed.

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* after a run (TRAP 1 first): the environment still agrees with the seed's E0 below 34 (HAE), and the memory with
   memc off P (KM); every name the tactic reads is an argument *)
Ltac al_after E0 P E32 HAE KM :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let U := fresh "U32" in
    assert (U : bv_unsigned (ew Eo 32) = P) by (apply (al_u32 _ _ _ HAE E32); lia);
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in
    assert (HAEn : env_agree 34 E0 En) by (env_agree_chain HAE);
    pose proof (al_keep_step Eo _ _ _ _ _ _ P HFr U KM) as KMn;
    clear U HFr HAE KM; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
Ltac al_awr_tac HAE E32 :=
  apply al_awr; rewrite (al_u32 _ _ _ HAE E32 ltac:(lia));
  change (fs_frame_bytes 7) with 8192; lia.
(* a leaf back at HEAD: the kept registers (HK) and a0, s3, a1, a2, a3, a4 *)
Ltac al_regs HS regs1 HA0 HAE E10 E19 E11 E12 HK N10 N19 N11 N12 N13 N14 :=
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ AL_KEPT HS (al_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK;
  cbn [ms_regs restrict] in HK;
  prreg HS (10%bv : bv 5) N10; prreg HS (19%bv : bv 5) N19; prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12;
  prreg HS (13%bv : bv 5) N13; prreg HS (14%bv : bv 5) N14;
  try rewrite E10 in N10; try rewrite E19 in N19; try rewrite E11 in N11; try rewrite E12 in N12;
  try (rewrite unsigned_lit_small in N10 by lia); try (rewrite unsigned_lit_small in N19 by lia);
  try (rewrite unsigned_lit_small in N11 by lia); try (rewrite unsigned_lit_small in N12 by lia).
Ltac al_reg_eq N := rewrite N; unfold w64; rewrite ?length_app; cbn [length]; f_equal; lia.

(* ---- one iteration: HEAD back to HEAD with one byte of the shape consumed, or the exit to JOIN ---- *)
Lemma al_step : AN_JOIN_stmt B MT -> forall n, (forall m, (m < n)%nat -> an_head_n m) -> an_head_n n.
Proof.
intros HJOIN n IHn ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1 j d out
  Hn HPRE Href HMID HRB H27 Hj Hdj Hinv H10 H19 H11 H12 H13 H14 HOUT HX HRA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_iter_facts ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc memc mdc pos sp1 j d out HPRE Href HMID Hinv)
  as (HF1 & HF2 & HF32 & Hoff & Happ & HFp & HBLK & HS1 & HS2 & HS3 & HIL & HOL & HXL & HX0 & Hsp0 & Hsp1).
pose proof HMID as (HJ & _ & _ & _ & _ & _ & HZS & _ & _).
pose proof HRB as (_ & _ & _ & _ & _ & _ & _ & _ & R21 & _ & _ & _ & R26).
set (F := frame_addr lyc 7 pos) in *.
assert (HFd : F = frame_addr lyc 7 pos) by reflexivity.
assert (Happ' := Happ). unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ'.
set (P := F + 32 + Z.of_nat (length out)).
assert (HPd : P = F + 32 + Z.of_nat (length out)) by reflexivity.
(* a leaf back at HEAD re-enters through al_reenter and the induction hypothesis *)
assert (CLOSE : forall regs1' memc' mdc' d' out',
  (d' <= Datatypes.S j)%nat -> out' ++ inst_go d' (skipn (Datatypes.S j) x) = inst x -> (j < length x)%nat ->
  ajournal SEGS B ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [(7, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> P -> rdW Wc memc' a = rdW Wc memc a) ->
  (out' = out \/ exists b, out' = out ++ [b] /\ rdW Wc memc' P = Some (bv_unsigned b)) ->
  (forall r, In r AL_KEPT -> getr regs1' r = getr regs1 r) ->
  getr regs1' 10 = w64 (sh + Z.of_nat (Datatypes.S j)) -> getr regs1' 19 = w64 (sh + Z.of_nat (Datatypes.S j)) ->
  getr regs1' 11 = w64 (Z.of_nat (length out')) -> getr regs1' 12 = w64 (Z.of_nat d') ->
  getr regs1' 13 = w64 60 -> getr regs1' 14 = w64 62 ->
  SRr SEGS Wc (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + AN_HEAD)) memc' (seg_rom SEGS)) mdc')
  (an_post B MT regs ly S W mem md R e x chg old O)).
{ intros regs1' memc' mdc' d' out' Hd' Hinv' Hjl HJ' KEEP HW HK N10 N19 N11 N12 N13 N14.
  exact (al_reenter (length x - Datatypes.S j)%nat (IHn (length x - Datatypes.S j)%nat ltac:(lia)) ly S W regs mem md ch c sh old e x
    chg R O lyc Sc Wc regs1 memc mdc pos sp1 j d out regs1' memc' mdc' d' out' eq_refl HPRE Href HMID HRB H27 ltac:(lia) Hinv
    Hd' Hinv' HOUT HX HRA HJ' KEEP HW HK N10 N19 N11 N12 N13 N14). }
(* the shape byte at sh + j: a byte of x, or the terminator when j = |x| *)
assert (HCbx : exists Cb, nth j (x ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = Cb) by (eexists; reflexivity).
destruct HCbx as (Cb & HCbe).
assert (HCb : rdW Wc memc (sh + Z.of_nat j) = Some (bv_unsigned Cb)).
{ rewrite <- HCbe. apply (proj1 HX). rewrite length_app. cbn [length]. lia. }
assert (HCbr : 0 <= bv_unsigned Cb < 256)
  by (pose proof (bv_unsigned_in_range 8 Cb) as Hr; change (bv_modulus 8) with 256 in Hr; lia).
assert (HCbs : (j < length x)%nat -> skipn j x = Cb :: skipn (Datatypes.S j) x /\ bv_unsigned Cb <> 0).
{ intros Hjl. rewrite <- HCbe, app_nth1 by exact Hjl. split; [apply al_skipn_nth; exact Hjl|].
  intros Hz. apply HX0. assert (H0 : nth j x (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; rewrite Hz; reflexivity).
  rewrite <- H0. apply nth_In. exact Hjl. }
assert (HCbe0 : j = length x -> bv_unsigned Cb = 0).
{ intros Hjx. rewrite <- HCbe, Hjx, app_nth2, Nat.sub_diag by lia. reflexivity. }
(* the seed at HEAD *)
assert (E10 : ew (al_E regs1 P (bv_unsigned Cb)) 10 = Z_to_bv 64 (sh + Z.of_nat j))
  by (rewrite (al_ew_reg regs1 P _ 10 10%bv eq_refl); exact H10).
assert (E19 : ew (al_E regs1 P (bv_unsigned Cb)) 19 = Z_to_bv 64 (sh + Z.of_nat j))
  by (rewrite (al_ew_reg regs1 P _ 19 19%bv eq_refl); exact H19).
assert (E11 : ew (al_E regs1 P (bv_unsigned Cb)) 11 = Z_to_bv 64 (Z.of_nat (length out)))
  by (rewrite (al_ew_reg regs1 P _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew (al_E regs1 P (bv_unsigned Cb)) 12 = Z_to_bv 64 (Z.of_nat d))
  by (rewrite (al_ew_reg regs1 P _ 12 12%bv eq_refl); exact H12).
assert (E26 : ew (al_E regs1 P (bv_unsigned Cb)) 26 = Z_to_bv 64 SB)
  by (rewrite (al_ew_reg regs1 P _ 26 26%bv eq_refl); exact R26).
pose proof (al_ew32 regs1 P (bv_unsigned Cb)) as E32.
pose proof (al_ew33 regs1 P (bv_unsigned Cb)) as E33.
assert (HPr : apresent (w_H Wc) memc P) by (apply HFp; lia).
pose proof (HS3 (sh + Z.of_nat j) ltac:(lia)) as HA3.
pose proof (al_entry Wc regs1 memc (sh + Z.of_nat j) (Z.of_nat (length out)) (Z.of_nat d) F P (bv_unsigned Cb)
  H10 H19 H11 H12 H13 H14 R21 R26 ltac:(lia) ltac:(lia) ltac:(lia) HPd ltac:(lia) ltac:(lia) ltac:(lia) HCb HPr ltac:(lia)) as HS.
assert (F8 : (F + 32) mod 8 = 0).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as DF. rewrite HF32 in DF.
  replace (F + 32) with ((4 * (F / 32) + 4) * 8) by lia. apply Z_mod_mult. }
pose proof (zero_shadow_range _ _ (F + 32) 4096 F8 eq_refl HZS) as HZR.
pose proof (al_shok Wc regs1 memc P (bv_unsigned Cb) R26 ltac:(lia)
  (range_addressable_sub _ _ (F + 32) 4096 P 1 HZR ltac:(lia) ltac:(lia)) ltac:(unfold SB; lia)) as SHOK.
assert (HEI : img_env VAL A_LIM (al_E regs1 P (bv_unsigned Cb))) by (unfold al_E; apply Eimg_env).
pose proof (al_env_agree regs1 P (bv_unsigned Cb)) as HA0.
revert HS SHOK HEI HA0 E10 E19 E11 E12 E26 E32 E33.
generalize (al_E regs1 P (bv_unsigned Cb)) as E0.
intros E0 HS SHOK HEI HA0 E10 E19 E11 E12 E26 E32 E33.
pose proof (env_agree_refl 34 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> P -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
(* 0x8a670 .. 0x8a684: the inline check of the shape byte, its load, `beq a5,a3` ('<') *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem]. unfold al_Bx. rewrite (U_atom _ 26 SB E26), (U_atom _ 10 _ E10) by (unfold SB; lia). rewrite SB_SHADOW_OFF.
  exact (range_addressable_sub _ _ sh (Z.of_nat (length x) + 1) (sh + Z.of_nat j) 1 HRA ltac:(lia) ltac:(lia)). }
{ al_awr_tac HAE E32. }
al_after E0 P E32 HAE KM.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* C = '<' *)
  pose proof (al_br_eq _ 33 _ 60 _ (al_ag_ew _ _ 33 _ HAE ltac:(lia) E33) ltac:(lia) ltac:(lia) Hc) as C60. apply Z.eqb_eq in C60. clear Hc.
  assert (Hjl : (j < length x)%nat)
    by (destruct (Nat.eq_dec j (length x)) as [Ex|Ex]; [rewrite (HCbe0 Ex) in C60; discriminate | lia]).
  destruct (HCbs Hjl) as [HSK _].
  paj_run_to_tok RUNTO HS HJ SHOK Bspan AN_HEAD. { al_awr_tac HAE E32. }
  al_after E0 P E32 HAE KM.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* d = 0: '1' goes out, the depth becomes 1 *)
    pose proof (al_br_eq _ 12 _ 0 _ (al_ag_ew _ _ 12 _ HAE ltac:(lia) E12) ltac:(lia) ltac:(lia) Hc) as D0. apply Z.eqb_eq in D0. clear Hc.
    destruct d as [|d0]; [|lia].
    assert (Hinv' : (out ++ [Z_to_bv 8 49]) ++ inst_go 1 (skipn (Datatypes.S j) x) = inst x).
    { rewrite HSK in Hinv. cbn [inst_go] in Hinv. rewrite (proj2 (Z.eqb_eq _ _) C60) in Hinv. rewrite <- app_assoc. exact Hinv. }
    assert (HO1 : Z.of_nat (length out) + 1 <= 4095)
      by (pose proof (f_equal (@length _) Hinv') as L; rewrite !length_app in L; cbn [length] in L; lia).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan AN_HEAD. { al_awr_tac HAE E32. }
    al_after E0 P E32 HAE KM.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * exfalso. pose proof (al_br_srl _ 11 _ _ (al_ag_ew _ _ 11 _ HAE ltac:(lia) E11) ltac:(lia) ltac:(lia) Hc) as X. discriminate X.
    * clear Hc. paj_run_to_tok RUNTO HS HJ SHOK Bspan AN_HEAD. { al_awr_tac HAE E32. }
      al_after E0 P E32 HAE KM.
      pose proof (al_wbyte _ _ _ _ P (SLit 49) HS ltac:(vm_compute; reflexivity)
        (al_u32 _ _ _ HAE E32 ltac:(lia))) as HWB.
      cbn [sv_denot] in HWB. rewrite unsigned_lit_small in HWB by lia.
      al_regs HS regs1 HA0 HAE E10 E19 E11 E12 HK N10 N19 N11 N12 N13 N14.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
      exact (CLOSE rg mm mdn 1%nat (out ++ [Z_to_bv 8 49]) ltac:(lia) Hinv' Hjl HJ KM
        ltac:(right; exists (Z_to_bv 8 49); split; [reflexivity | etransitivity; [exact HWB | reflexivity]]) HK
        ltac:(al_reg_eq N10) ltac:(al_reg_eq N19) ltac:(al_reg_eq N11) ltac:(al_reg_eq N12) N13 N14) end.
  + (* d > 0: the depth grows *)
    pose proof (al_br_eq _ 12 _ 0 _ (al_ag_ew _ _ 12 _ HAE ltac:(lia) E12) ltac:(lia) ltac:(lia) Hc) as D0. apply Z.eqb_neq in D0. clear Hc.
    destruct d as [|d0]; [lia|].
    assert (Hinv' : out ++ inst_go (Datatypes.S (Datatypes.S d0)) (skipn (Datatypes.S j) x) = inst x).
    { rewrite HSK in Hinv. cbn [inst_go] in Hinv. rewrite (proj2 (Z.eqb_eq _ _) C60) in Hinv. exact Hinv. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan AN_HEAD. { al_awr_tac HAE E32. }
    al_after E0 P E32 HAE KM.
    al_regs HS regs1 HA0 HAE E10 E19 E11 E12 HK N10 N19 N11 N12 N13 N14.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    exact (CLOSE rg mm mdn (Datatypes.S (Datatypes.S d0)) out ltac:(lia) Hinv' Hjl HJ KM (or_introl eq_refl) HK
      ltac:(al_reg_eq N10) ltac:(al_reg_eq N19) ltac:(al_reg_eq N11) ltac:(al_reg_eq N12) N13 N14) end.
- (* C <> '<' *)
  pose proof (al_br_eq _ 33 _ 60 _ (al_ag_ew _ _ 33 _ HAE ltac:(lia) E33) ltac:(lia) ltac:(lia) Hc) as C60. apply Z.eqb_neq in C60. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan AN_HEAD. { al_awr_tac HAE E32. }
  al_after E0 P E32 HAE KM.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* C = '>' *)
    pose proof (al_br_eq _ 33 _ 62 _ (al_ag_ew _ _ 33 _ HAE ltac:(lia) E33) ltac:(lia) ltac:(lia) Hc) as C62. apply Z.eqb_eq in C62. clear Hc.
    assert (Hjl : (j < length x)%nat)
      by (destruct (Nat.eq_dec j (length x)) as [Ex|Ex]; [rewrite (HCbe0 Ex) in C62; discriminate | lia]).
    destruct (HCbs Hjl) as [HSK _].
    paj_run_to_tok RUNTO HS HJ SHOK Bspan AN_HEAD. { al_awr_tac HAE E32. }
    al_after E0 P E32 HAE KM.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* d = 0: '>' goes out *)
      pose proof (al_br_ge _ 12 _ _ (al_ag_ew _ _ 12 _ HAE ltac:(lia) E12) ltac:(lia) Hc) as D0. clear Hc.
      destruct d as [|d0]; [|cbn in D0; discriminate D0].
      assert (Hinv' : (out ++ [Cb]) ++ inst_go 0 (skipn (Datatypes.S j) x) = inst x).
      { rewrite HSK in Hinv. cbn [inst_go] in Hinv. rewrite (proj2 (Z.eqb_neq _ _) C60) in Hinv. rewrite <- app_assoc. exact Hinv. }
      assert (HO1 : Z.of_nat (length out) + 1 <= 4095)
        by (pose proof (f_equal (@length _) Hinv') as L; rewrite !length_app in L; cbn [length] in L; lia).
      paj_run_to_tok RUNTO HS HJ SHOK Bspan AN_HEAD. { al_awr_tac HAE E32. }
      al_after E0 P E32 HAE KM.
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- exfalso. pose proof (al_br_srl _ 11 _ _ (al_ag_ew _ _ 11 _ HAE ltac:(lia) E11) ltac:(lia) ltac:(lia) Hc) as X. discriminate X.
      -- clear Hc. paj_run_to_tok RUNTO HS HJ SHOK Bspan AN_HEAD. { al_awr_tac HAE E32. }
         al_after E0 P E32 HAE KM.
         pose proof (al_wbyte _ _ _ _ P (SLit 62) HS ltac:(vm_compute; reflexivity)
           (al_u32 _ _ _ HAE E32 ltac:(lia))) as HWB.
         cbn [sv_denot] in HWB. rewrite unsigned_lit_small in HWB by lia.
         al_regs HS regs1 HA0 HAE E10 E19 E11 E12 HK N10 N19 N11 N12 N13 N14.
         pmkst HS.
         lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
         exact (CLOSE rg mm mdn 0%nat (out ++ [Cb]) ltac:(lia) Hinv' Hjl HJ KM
           ltac:(right; exists Cb; split; [reflexivity | etransitivity; [exact HWB | rewrite C62; reflexivity]]) HK
           ltac:(al_reg_eq N10) ltac:(al_reg_eq N19) ltac:(al_reg_eq N11) ltac:(al_reg_eq N12) N13 N14) end.
    * (* d > 0: the depth shrinks *)
      pose proof (al_br_ge _ 12 _ _ (al_ag_ew _ _ 12 _ HAE ltac:(lia) E12) ltac:(lia) Hc) as D0. clear Hc.
      destruct d as [|d0]; [cbn in D0; discriminate D0|].
      assert (Hinv' : out ++ inst_go d0 (skipn (Datatypes.S j) x) = inst x).
      { rewrite HSK in Hinv. cbn [inst_go] in Hinv.
        rewrite (proj2 (Z.eqb_neq _ _) C60), (proj2 (Z.eqb_eq _ _) C62) in Hinv. exact Hinv. }
      paj_run_to_tok RUNTO HS HJ SHOK Bspan AN_HEAD. { al_awr_tac HAE E32. }
      al_after E0 P E32 HAE KM.
      al_regs HS regs1 HA0 HAE E10 E19 E11 E12 HK N10 N19 N11 N12 N13 N14.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
      exact (CLOSE rg mm mdn d0 out ltac:(lia) Hinv' Hjl HJ KM (or_introl eq_refl) HK
        ltac:(al_reg_eq N10) ltac:(al_reg_eq N19) ltac:(al_reg_eq N11) ltac:(al_reg_eq N12) N13 N14) end.
  + (* C <> '>' *)
    pose proof (al_br_eq _ 33 _ 62 _ (al_ag_ew _ _ 33 _ HAE ltac:(lia) E33) ltac:(lia) ltac:(lia) Hc) as C62. apply Z.eqb_neq in C62. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan AN_HEAD. { al_awr_tac HAE E32. }
    al_after E0 P E32 HAE KM.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* C = 0: the terminator, buf's terminator, JOIN *)
      pose proof (al_br_eq _ 33 _ 0 _ (al_ag_ew _ _ 33 _ HAE ltac:(lia) E33) ltac:(lia) ltac:(lia) Hc) as C0. apply Z.eqb_eq in C0. clear Hc.
      assert (Hjx : j = length x)
        by (destruct (Nat.lt_ge_cases j (length x)) as [Hl|Hl]; [exfalso; exact (proj2 (HCbs Hl) C0) | lia]).
      assert (Hout : out = inst x).
      { rewrite Hjx, skipn_all in Hinv. cbn [inst_go] in Hinv. rewrite app_nil_r in Hinv. exact Hinv. }
      paj_run_to_tok RUNTO HS HJ SHOK Bspan AN_JOIN. { al_awr_tac HAE E32. }
      al_after E0 P E32 HAE KM.
      pose proof (al_wbyte _ _ _ _ P (SLit 0) HS ltac:(vm_compute; reflexivity)
        (al_u32 _ _ _ HAE E32 ltac:(lia))) as HWB.
      cbn [sv_denot] in HWB. rewrite unsigned_lit_small in HWB by lia. change (0 mod 256) with 0 in HWB.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ AL_KEPT HS (al_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msn) _ _ _) ?mdn) _ =>
      exact (al_exit HJOIN ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1 out
        (ms_regs msn) (ms_mem msn) mdn HPRE Href HMID HRB H27 Hout HOUT HJ KM HWB HK) end.
    * (* another byte *)
      pose proof (al_br_eq _ 33 _ 0 _ (al_ag_ew _ _ 33 _ HAE ltac:(lia) E33) ltac:(lia) ltac:(lia) Hc) as C0. apply Z.eqb_neq in C0. clear Hc.
      assert (Hjl : (j < length x)%nat)
        by (destruct (Nat.eq_dec j (length x)) as [Ex|Ex]; [exfalso; exact (C0 (HCbe0 Ex)) | lia]).
      destruct (HCbs Hjl) as [HSK _].
      paj_run_to_tok RUNTO HS HJ SHOK Bspan AN_HEAD. { al_awr_tac HAE E32. }
      al_after E0 P E32 HAE KM.
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- (* d > 0: dropped *)
         pose proof (al_br_lt _ 12 _ _ (al_ag_ew _ _ 12 _ HAE ltac:(lia) E12) ltac:(lia) Hc) as D0. clear Hc.
         destruct d as [|d0]; [cbn in D0; discriminate D0|].
         assert (Hinv' : out ++ inst_go (Datatypes.S d0) (skipn (Datatypes.S j) x) = inst x).
         { rewrite HSK in Hinv. cbn [inst_go] in Hinv.
           rewrite (proj2 (Z.eqb_neq _ _) C60), (proj2 (Z.eqb_neq _ _) C62) in Hinv. exact Hinv. }
         paj_run_to_tok RUNTO HS HJ SHOK Bspan AN_HEAD. { al_awr_tac HAE E32. }
         al_after E0 P E32 HAE KM.
         al_regs HS regs1 HA0 HAE E10 E19 E11 E12 HK N10 N19 N11 N12 N13 N14.
         pmkst HS.
         lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
         exact (CLOSE rg mm mdn (Datatypes.S d0) out ltac:(lia) Hinv' Hjl HJ KM (or_introl eq_refl) HK
           ltac:(al_reg_eq N10) ltac:(al_reg_eq N19) ltac:(al_reg_eq N11) ltac:(al_reg_eq N12) N13 N14) end.
      -- (* d = 0: the byte goes out *)
         pose proof (al_br_lt _ 12 _ _ (al_ag_ew _ _ 12 _ HAE ltac:(lia) E12) ltac:(lia) Hc) as D0. clear Hc.
         destruct d as [|d0]; [|cbn in D0; discriminate D0].
         assert (Hinv' : (out ++ [Cb]) ++ inst_go 0 (skipn (Datatypes.S j) x) = inst x).
         { rewrite HSK in Hinv. cbn [inst_go] in Hinv. rewrite (proj2 (Z.eqb_neq _ _) C60) in Hinv. rewrite <- app_assoc. exact Hinv. }
         assert (HO1 : Z.of_nat (length out) + 1 <= 4095)
           by (pose proof (f_equal (@length _) Hinv') as L; rewrite !length_app in L; cbn [length] in L; lia).
         paj_run_to_tok RUNTO HS HJ SHOK Bspan AN_HEAD. { al_awr_tac HAE E32. }
         al_after E0 P E32 HAE KM.
         psrr_branch_tok RUN BR HS SHOK Bspan.
         ++ exfalso. pose proof (al_br_srl _ 11 _ _ (al_ag_ew _ _ 11 _ HAE ltac:(lia) E11) ltac:(lia) ltac:(lia) Hc) as X. discriminate X.
         ++ clear Hc. paj_run_to_tok RUNTO HS HJ SHOK Bspan AN_HEAD. { al_awr_tac HAE E32. }
            al_after E0 P E32 HAE KM.
            pose proof (al_wbyte _ _ _ _ P (SOff 33 0) HS ltac:(vm_compute; reflexivity)
              (al_u32 _ _ _ HAE E32 ltac:(lia))) as HWB.
            rewrite (al_den_off _ 33 (bv_unsigned Cb) 0 (al_ag_ew _ _ 33 _ HAE ltac:(lia) E33) ltac:(lia)), Z.add_0_r in HWB.
            rewrite unsigned_lit_small, Z.mod_small in HWB by lia.
            al_regs HS regs1 HA0 HAE E10 E19 E11 E12 HK N10 N19 N11 N12 N13 N14.
            pmkst HS.
            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
            exact (CLOSE rg mm mdn 0%nat (out ++ [Cb]) ltac:(lia) Hinv' Hjl HJ KM
              (or_intror (ex_intro _ Cb (conj eq_refl HWB))) HK
              ltac:(al_reg_eq N10) ltac:(al_reg_eq N19) ltac:(al_reg_eq N11) ltac:(al_reg_eq N12) N13 N14) end.
Qed.

(* ---- HEAD: by strong induction on the bytes of the shape left ---- *)
Lemma an_head_ok : AN_JOIN_stmt B MT -> AN_HEAD_stmt B MT.
Proof.
intros HJOIN.
assert (ALL : forall k m, (m <= k)%nat -> an_head_n m).
{ induction k as [|k IHk]; intros m Hm.
  - apply (al_step HJOIN m). intros m' Hm'. lia.
  - apply (al_step HJOIN m). intros m' Hm'. apply (IHk m'). lia. }
unfold AN_HEAD_stmt.
intros ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1 j d out
  HPRE Href HMID HRB H27 Hj Hdj Hinv H10 H19 H11 H12 H13 H14 HOUT HX HRA.
exact (ALL (length x - j)%nat (length x - j)%nat (le_n _) ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc
  pos sp1 j d out eq_refl HPRE Href HMID HRB H27 Hj Hdj Hinv H10 H19 H11 H12 H13 H14 HOUT HX HRA).
Qed.

End e.
End f.
End d.
