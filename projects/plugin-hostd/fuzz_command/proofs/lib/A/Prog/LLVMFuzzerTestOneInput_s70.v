(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of segment F of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86974 .. 0x8699c: the three frees of the words blocks and the latch), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (wcb_entry: the symbolic seed of a point of the function) and A/ACh2.v:122-290 (the step through a call and back, with the facts carried over it). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---- readers that agree on a set of addresses ---- *)
Lemma ltf_aval_ext : forall (rd rd' : reader) a n v,
  (forall i, 0 <= i < Z.of_nat n -> rd' (a + i) = rd (a + i)) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v HK H k Hk. rewrite (HK (Z.of_nat k)) by lia. exact (H k Hk). Qed.
Lemma ltf_abytes_ext : forall (rd rd' : reader) a l,
  (forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l HK H i Hi. rewrite (HK (Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma ltf_astr_ext : forall (rd rd' : reader) p s,
  (forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (p + i) = rd (p + i)) -> astr_atR rd p s -> astr_atR rd' p s.
Proof.
intros rd rd' p s HK [H1 H2]. split; [|exact H2].
apply (ltf_abytes_ext rd rd' p _ ); [|exact H1]. rewrite length_app. cbn [length]. intros i Hi. apply HK. lia.
Qed.

(* the addresses a point of the walk reads of the recorder: the program's own statics (cmd_PG: g_rec,
   record.spill, g_quitting) and the bytes of the blocks the recorder owns *)
Definition ltf_rk (O : list (Z * Z)) (a : Z) : Prop :=
  inFP cmd_PG a \/ exists b n, In (b, n) O /\ b <= a < b + req_size n.
Lemma ltf_PG_rec : forall o, 0 <= o < 960 -> inFP cmd_PG (A_G_REC + o).
Proof. intros o Ho. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia]. Qed.
Lemma ltf_PG_spill : forall o, 0 <= o < 56 -> inFP cmd_PG (A_REC_SPILL + o).
Proof. intros o Ho. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; lia]. Qed.
Lemma ltf_PG_quit : forall o, 0 <= o < 4 -> inFP cmd_PG (A_G_QUITTING + o).
Proof. intros o Ho. exists (A_G_QUITTING, A_G_QUITTING + 4). split; [right; right; left; reflexivity | cbn [fst snd]; lia]. Qed.
Lemma ltf_rk_of_rec : forall O a, A_G_REC <= a -> a + 56 <= A_G_REC + 960 ->
  forall i, 0 <= i < 56 -> ltf_rk O (a + i).
Proof. intros O a Ha Hb i Hi. left. replace (a + i) with (A_G_REC + (a + i - A_G_REC)) by ring. apply ltf_PG_rec. lia. Qed.
Lemma ltf_rk_of_spill : forall O, forall i, 0 <= i < 56 -> ltf_rk O (A_REC_SPILL + i).
Proof. intros O i Hi. left. apply ltf_PG_spill. lia. Qed.
Lemma ltf_rk_blk : forall O b n a m, In (b, n) O -> b <= a -> a + Z.of_nat m <= b + n -> 0 <= n ->
  forall i, 0 <= i < Z.of_nat m -> ltf_rk O (a + i).
Proof.
intros O b n a m Hin Hb Ha Hn i Hi. right. exists b, n. split; [exact Hin|].
pose proof (req_size_pos n Hn) as [_ Hr]. lia.
Qed.

(* every byte acall_at reads of a call record lies in the 56-byte slot, every string it reads in one of its own
   blocks, so a reader that keeps ltf_rk keeps acall_at (the block list may change as long as the call's blocks
   stay live) *)
Lemma ltf_acall_ext : forall bl bl' (rd rd' : reader) a c P O,
  acall_at bl rd a c P ->
  (forall pn, In pn P -> In pn O) -> (forall pn, In pn P -> In pn bl') ->
  (forall i, 0 <= i < 56 -> ltf_rk O (a + i)) ->
  (forall x, ltf_rk O x -> rd' x = rd x) ->
  acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P O (H1 & H2 & H3 & H4 & H5 & H6 & H7) HPO HPb HRng HK.
assert (HKr : forall x w, a <= x -> x + w <= a + 56 -> forall i, 0 <= i < w -> rd' (x + i) = rd (x + i)).
{ intros x w Hx Hw i Hi. apply HK. replace (x + i) with (a + (x + i - a)) by ring. apply HRng. lia. }
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (ltf_aval_ext rd rd'); [apply (HKr _ 4); unfold CALL_OFF_FN; lia | exact H4]|].
split; [apply (ltf_aval_ext rd rd'); [apply (HKr _ 4); unfold CALL_OFF_NARGS; lia | exact H5]|].
split; [exact H6|].
intros k s pn Hs Hp. destruct (H7 k s pn Hs Hp) as (Q1 & Q2 & Q3 & Q4 & Q5).
assert (Hk6 : (k < 6)%nat).
{ assert (Hkl : (k < length (snd c))%nat) by (apply (proj1 (nth_error_Some (snd c) k)); rewrite Hs; discriminate). lia. }
split.
{ apply (ltf_aval_ext rd rd'); [|exact Q1].
  apply (HKr _ 8); unfold CALL_OFF_ARGS; lia. }
split; [exact Q2|]. split; [exact (HPb pn (nth_error_In _ _ Hp))|]. split; [exact Q4|].
apply (ltf_astr_ext rd rd'); [|exact Q5].
intros i Hi. apply HK. apply (ltf_rk_blk O (fst pn) (snd pn) (fst pn) (Datatypes.S (length s)));
  [ destruct pn; exact (HPO _ (nth_error_In _ _ Hp)) | lia | rewrite Nat2Z.inj_succ; lia | lia | rewrite Nat2Z.inj_succ; lia ].
Qed.

Lemma ltf_in_lay_calls : forall Q P pn, In P (l_calls Q) -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q P pn HP Hpn. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P. auto.
Qed.
Lemma ltf_in_lay_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.
Lemma ltf_in_lay_answer : forall Q pn, l_answer Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
rewrite H. left. reflexivity.
Qed.
Lemma ltf_in_lay_reply : forall Q pn, l_reply Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
rewrite H. left. reflexivity.
Qed.

Lemma ltf_arep_ext : forall bl bl' (rd rd' : reader) R Q O,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (forall pn, In pn (lay_blocks Q) -> In pn O) -> (forall pn, In pn (lay_blocks Q) -> In pn bl') ->
  (forall x, ltf_rk O x -> rd' x = rd x) ->
  arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q O (G1 & G2 & G3 & HC & HA & HR & HS & HO) HQO HQb HK.
assert (HKrec : forall x w, A_G_REC <= x -> x + w <= A_G_REC + 960 -> forall i, 0 <= i < w ->
  rd' (x + i) = rd (x + i)).
{ intros x w Hx Hw i Hi. apply HK. left. replace (x + i) with (A_G_REC + (x + i - A_G_REC)) by ring.
  apply ltf_PG_rec. lia. }
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
(* ag1_calls *)
split.
{ destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  split; [exact C1|]. split; [exact C2|].
  split; [apply (ltf_aval_ext rd rd'); [apply (HKrec _ 4); unfold OFF_NCALLS, A_G_REC; lia | exact C3]|].
  split.
  { intros i c P Hc HP. destruct (C4 i c P Hc HP) as [Hca Hfa]. split; [|exact Hfa].
    assert (Hi16 : (i < 16)%nat).
    { assert (Hil : (i < length (r_calls R))%nat) by (apply (proj1 (nth_error_Some (r_calls R) i)); rewrite Hc; discriminate). lia. }
    apply (ltf_acall_ext bl bl' rd rd' _ c P O Hca);
      [ intros pn Hpn; apply HQO; exact (ltf_in_lay_calls Q P pn (nth_error_In _ _ HP) Hpn)
      | intros pn Hpn; apply HQb; exact (ltf_in_lay_calls Q P pn (nth_error_In _ _ HP) Hpn)
      | apply (ltf_rk_of_rec O); unfold OFF_CALLS, CALL_SIZE, A_G_REC; lia
      | exact HK ]. }
  split; [|exact C6].
  apply (ltf_acall_ext bl bl' rd rd' _ (r_spill R) (l_spill Q) O C5);
    [ intros pn Hpn; apply HQO; exact (ltf_in_lay_spill Q pn Hpn)
    | intros pn Hpn; apply HQb; exact (ltf_in_lay_spill Q pn Hpn)
    | exact (ltf_rk_of_spill O) | exact HK ]. }
(* aanswer_at *)
split.
{ unfold aanswer_at in *. revert HA.
  destruct (r_answer R) as [x|] eqn:Ea; destruct (l_answer Q) as [pa|] eqn:Eq; intros HA; try contradiction.
  - destruct HA as (A1 & A2 & A3 & A4 & A5 & A6).
    split; [apply (ltf_aval_ext rd rd'); [apply (HKrec _ 8); unfold OFF_ANSWER, A_G_REC; lia | exact A1]|].
    split; [exact A2|]. split; [exact (HQb pa (ltf_in_lay_answer Q pa Eq))|]. split; [exact A4|]. split; [|exact A6].
    apply (ltf_astr_ext rd rd'); [|exact A5].
    intros i Hi. apply HK. apply (ltf_rk_blk O (fst pa) (snd pa) (fst pa) (Datatypes.S (length x)));
      [ destruct pa; exact (HQO _ (ltf_in_lay_answer Q _ Eq)) | lia | rewrite Nat2Z.inj_succ; lia | lia | rewrite Nat2Z.inj_succ; lia ].
  - apply (ltf_aval_ext rd rd'); [apply (HKrec _ 8); unfold OFF_ANSWER, A_G_REC; lia | exact HA]. }
(* areply_at *)
split.
{ unfold areply_at in *. revert HR.
  destruct (r_reply R) as [x|] eqn:Ea; destruct (l_reply Q) as [pa|] eqn:Eq; intros HR; try contradiction.
  - destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply (ltf_aval_ext rd rd'); [apply (HKrec _ 8); unfold OFF_REPLY, A_G_REC; lia | exact A1]|].
    split; [apply (ltf_aval_ext rd rd'); [apply (HKrec _ 8); unfold OFF_REPLY_SIZE, A_G_REC; lia | exact A2]|].
    split; [exact A3|]. split; [exact A4|]. split; [exact (HQb pa (ltf_in_lay_reply Q pa Eq))|]. split; [exact A6|].
    split; [|exact A8].
    apply (ltf_abytes_ext rd rd'); [|exact A7].
    intros i Hi. apply HK. apply (ltf_rk_blk O (fst pa) (snd pa) (fst pa) (length x));
      [ destruct pa; exact (HQO _ (ltf_in_lay_reply Q _ Eq)) | lia | lia | lia | lia ].
  - destruct HR as [A1 A2]. split.
    + apply (ltf_aval_ext rd rd'); [apply (HKrec _ 8); unfold OFF_REPLY, A_G_REC; lia | exact A1].
    + apply (ltf_aval_ext rd rd'); [apply (HKrec _ 8); unfold OFF_REPLY_SIZE, A_G_REC; lia | exact A2]. }
(* ag1_scalars *)
split; [|exact HO].
destruct HS as (S1 & S2 & S3 & S4 & S5 & S6).
split; [apply (ltf_aval_ext rd rd'); [apply (HKrec _ 4); unfold OFF_REFUSE, A_G_REC; lia | exact S1]|].
split; [apply (ltf_aval_ext rd rd'); [apply (HKrec _ 4); unfold OFF_CODE, A_G_REC; lia | exact S2]|].
split; [apply (ltf_aval_ext rd rd'); [apply (HKrec _ 4); unfold OFF_NREPLIES, A_G_REC; lia | exact S3]|].
split; [apply (ltf_aval_ext rd rd'); [apply (HKrec _ 8); unfold OFF_STATE, A_G_REC; lia | exact S4]|].
split; [|exact S6].
apply (ltf_aval_ext rd rd'); [apply (HKrec _ 8); unfold OFF_HOST, A_G_REC; lia | exact S5].
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

(* the symbolic seed of a point of the segment: every register is its own atom, atom 32 is the shadow base, no
   region (the eleven instructions make no memory access) and no shadow entry (no inline check) *)
Definition ltf_facts : facts := mkFacts [ (32%nat, mkAF SB SB 0) ] [] [].
Definition ltf_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None ltf_facts.
Definition ltf_Bx : sv := SOff 32 0.
Definition ltf_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ltf_extra : list word := [Z_to_bv 64 SB].
Definition ltf_E (regs : bvmap 5 word) : env := Eimg (Ereg regs ltf_extra).

Lemma ltf_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
  st_ok_pi SEGS VAL (ltf_E regs) (ltf_ss pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS ltf_Bx [] (ltf_E regs) (mrestrict (w_H W) mem)
  /\ img_env VAL A_LIM (ltf_E regs)
  /\ env_agree 32 (Ereg regs ltf_extra) (ltf_E regs)
  /\ (forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (ltf_E regs) n = getr regs rr).
Proof.
intros W regs mem pc.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (ltf_E regs) n = ew (Ereg regs ltf_extra) n)
  by (intros n Hn; unfold ltf_E; apply Eimg_low; exact Hn).
assert (E32 : ew (ltf_E regs) 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
split.
- unfold ltf_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold ltf_E. apply regs_ok_Eimg_Ereg.
  + reflexivity.
  + apply Forall_nil.
  + first [ exact I | constructor
          | apply pairwise_disjoint_of_extents; cbn; first [exact I | constructor | repeat split] ].
  + split; [|split; [exact I | exact I]].
    cbn [ltf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, unsigned_lit_small by (unfold SB; lia). rewrite Z.pow_0_r, Z.mod_1_r.
    unfold SB. repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
- split; [apply Forall_nil|].
  split; [unfold ltf_E; apply Eimg_env|].
  split; [split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | reflexivity]|].
  intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

(* reading a callee-saved register out of aregs_preserved *)
Lemma ltf_pres_get : forall (regs regs' : bvmap 5 word) (r : Z) (rr : bv 5),
  aregs_preserved regs regs' -> acallee_saved r -> Z_to_bv 5 r = rr -> getr regs' rr = getr regs rr.
Proof. intros regs regs' r rr HP Hr <-. exact (HP r Hr). Qed.

(* bit-vector shapes the latch's three arithmetic instructions leave *)
Lemma ltf_addw1 : forall E (n : nat) v, ew E n = Z_to_bv 64 (Z.of_nat v) -> (v < 32)%nat ->
  sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 1)) = Z_to_bv 64 (Z.of_nat (Datatypes.S v)).
Proof.
intros E n v Hn Hv.
assert (Hu : U E (SOff n 0) = Z.of_nat v).
{ apply U_atom; [exact Hn | lia]. }
rewrite (denot_lit_U E (SAluw ALU_ADD (SOff n 0) (SLit 1))). f_equal.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite Hu, U_lit by lia.
rewrite !Z.mod_small by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite (Z.mod_small (Z.of_nat v + 1 + 2 ^ 31)) by lia.
change (bv_modulus 64) with (2 ^ 64). rewrite Nat2Z.inj_succ. rewrite Z.mod_small by lia. lia.
Qed.
Lemma ltf_add_atoms : forall E (n1 n2 : nat) v1 v2,
  ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 -> 0 <= v1 -> 0 <= v2 -> v1 + v2 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = Z_to_bv 64 (v1 + v2).
Proof.
intros E n1 n2 v1 v2 H1 H2 Hv1 Hv2 Hs.
rewrite (denot_lit_U E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0))). f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n1 v1 H1 ltac:(lia)), (U_atom E n2 v2 H2 ltac:(lia)).
apply zcanon_id. unfold M64. lia.
Qed.

(* NoDup of the live blocks and the separation of two of them, under the names this file uses (the shape of the
   section arguments of lt_ablocks_NoDup and of YCbq's sep_blocks is settled here, once) *)
Lemma ltf_nodup : forall (B : asyms), AR_laws SEGS B ->
  forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros B LAWS ly S W mem md HAR.
exact (lt_ablocks_NoDup B LAWS ly S W mem md HAR).
Qed.
Lemma ltf_sep : forall (B : asyms), AR_laws SEGS B ->
  forall ly S (W : world SEGS) mem md b m p n,
  AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
  zdisjoint (b, req_size m) (p, req_size n).
Proof.
intros B LAWS ly S W mem md b m p n HAR H1 H2 Hne.
first [ exact (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR H1 H2 Hne)
      | exact (sep_blocks SEGS B LAWS pa_segs_low ly S W mem md b m p n HAR H1 H2 Hne) ].
Qed.

(* ---- what one free keeps, and the state between two frees ---- *)

(* The reads the rest of the segment makes: the recorder's statics and the blocks it owns, the walk's own frame
   (from sp = x_sp1 up to the entry's sp: the eleven words, the struct, the two spills and the thirteen saved
   registers all lie there), and the payload's block. The 16 KB below sp are the free wrapper's own window, which
   it may write, and this segment reads nothing there. *)
Definition ltf_keep (B : asyms) (cx : lcx) (O : list (Z * Z)) (rd0 rd : reader) : Prop :=
  forall a, ltf_rk O a \/ (x_sp1 cx <= a < x_sp0 cx) \/
            (exists b n, In (b, n) (x_bl0 B cx) /\ b <= a < b + req_size n) ->
  rd a = rd0 a.
Lemma ltf_keep_refl : forall B cx O rd, ltf_keep B cx O rd rd.
Proof. intros B cx O rd a _. reflexivity. Qed.
Lemma ltf_keep_trans : forall B cx O rd0 rd1 rd2,
  ltf_keep B cx O rd0 rd1 -> ltf_keep B cx O rd1 rd2 -> ltf_keep B cx O rd0 rd2.
Proof. intros B cx O rd0 rd1 rd2 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

(* the point between two frees: the journal from the entry, the blocks still to free, what is kept, and the
   callee-saved registers of the segment's own first state regs0 *)
Definition ltf_pt (B : asyms) (cx : lcx) (O : list (Z * Z)) (left : list (Z * Z)) (regs0 : bvmap 5 word)
  ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k : Z) (rd0 : reader) : Prop :=
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md k /\
  Permutation (ablocks B ly S) (left ++ O ++ x_bl0 B cx) /\
  ltf_keep B cx O rd0 (rdW W mem) /\
  aregs_preserved regs0 regs.

Lemma ltf_nodup_mid : forall {X} (l1 l2 l3 : list X) x, List.NoDup (l1 ++ l2 ++ x :: l3) -> In x l2 -> False.
Proof.
intros X l1 l2 l3 x HND Hin.
apply NoDup_app_remove_l in HND. apply NoDup_remove_2 in HND. apply HND. apply in_or_app. left. exact Hin.
Qed.

(* one free: the run from pc to the free wrapper, the call, and back at pc + 8. The facts of the walk are explicit
   arguments (the walk hypotheses LAWS, TL, the statement's AFREE4, and the record fact cmd_prog_unowned),
   so that the segment's own file states them once and applies this lemma with them. *)
Lemma ltf_free : forall (B : asyms) (MT : ameter_ops),
  AR_laws SEGS B -> PALib B -> afree04_rule SEGS B MT ->
  (forall a, inFP cmd_PG a -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
     ~ (as_errno B <= a < as_errno B + 4)) ->
  forall cx O pa n left regs0 ly S (W : world SEGS) regs mem md k rd0 (pc : Z) (rr : bv 5) Q,
  lt_base B MT cx ->
  (pc = 0x490 /\ rr = 24%bv) \/ (pc = 0x498 /\ rr = 23%bv) \/ (pc = 0x4a0 /\ rr = 25%bv) ->
  ltf_pt B cx O ((pa, n) :: left) regs0 ly S W regs mem md k rd0 ->
  spZ regs0 = x_sp1 cx -> getr regs0 3 = getr (x_regs cx) 3 -> getr regs0 4 = getr (x_regs cx) 4 ->
  getr regs0 8 = w64 32 -> getr regs0 rr = w64 pa ->
  st_nev S < EV_MAX -> mo_ok MT S (mo_free MT) ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
     ltf_pt B cx O left regs0 ly2 S2 W2 regs2 mem2 md2 (k + 1) rd0 ->
     mo_le MT S S2 (mo_free MT) ->
     SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + (pc + 8))) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)) md) Q.
Proof.
intros B MT LAWS TL AFREE4 cmd_prog_unowned.
pose proof (paj_run B LAWS) as RUN.
intros cx O pa n left regs0 ly S W regs mem md k rd0 pc rr Q HBASE Hpc HPT Hsp00 Hgp00 Htp00 H800 Hpa Hnev MOK HC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
pose proof HBASE as (HPRE0 & _).
pose proof HPT as (HJ & HPerm & HK0 & HPR0).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
assert (WS : LTOI_STK = 32768) by reflexivity.
assert (HFR : x_sp1 cx = x_sp0 cx - LT_FRAME) by reflexivity.
(* sp, gp, tp and s0 at this point, from the segment's first state *)
assert (Hsp : spZ regs = x_sp1 cx).
{ rewrite <- Hsp00. unfold spZ. f_equal.
  exact (ltf_pres_get regs0 regs 2 2%bv HPR0 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)). }
assert (Hgp : getr regs 3 = w64 (as_gp B)).
{ exact (eq_trans (ltf_pres_get regs0 regs 3 3%bv HPR0 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity))
    (eq_trans Hgp00 Hgp0)). }
assert (Htp : getr regs 4 = w64 (as_tp B)).
{ exact (eq_trans (ltf_pres_get regs0 regs 4 4%bv HPR0 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity))
    (eq_trans Htp00 Htp0)). }
assert (H8 : getr regs 8 = w64 32).
{ exact (eq_trans (ltf_pres_get regs0 regs 8 8%bv HPR0 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity))
    H800). }
(* the block to free is live, and it is not one of the entry's *)
assert (Hin : In (pa, n) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HPerm)). left. reflexivity. }
assert (HND : List.NoDup (ablocks B ly S)) by exact (ltf_nodup B LAWS ly S W mem md HAR).
assert (Hnb0 : ~ In (pa, n) (x_bl0 B cx)).
{ intros Hb. pose proof (Permutation_NoDup HPerm HND) as HND2. cbn [app] in HND2.
  apply NoDup_cons_iff in HND2 as [Hni _]. apply Hni. apply in_or_app. right. apply in_or_app. right. exact Hb. }
assert (HnO : ~ In (pa, n) O).
{ intros Hb. pose proof (Permutation_NoDup HPerm HND) as HND2. cbn [app] in HND2.
  apply NoDup_cons_iff in HND2 as [Hni _]. apply Hni. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (Hsp32 : 0x10000 <= x_sp1 cx) by (rewrite HFR; unfold LT_FRAME; rewrite WS in Hslo; lia).
assert (Hsp1c : alloc_ceiling <= x_sp1 cx) by (rewrite HFR; unfold LT_FRAME; rewrite WS in Hslo; lia).
assert (Hcov : In (pa, n) (ablocks B (x_ly cx) (x_S cx)) -> forall i, 0 <= i < req_size n -> inFP cmd_PG (pa + i)).
{ intros Hb. exfalso. apply Hnb0. unfold x_bl0. exact Hb. }
(* every address this segment reads is a machine address *)
assert (HBND : forall a, ltf_rk O a \/ (x_sp1 cx <= a < x_sp0 cx) \/
                 (exists b m, In (b, m) (x_bl0 B cx) /\ b <= a < b + req_size m) -> 0 <= a < 2 ^ 64).
{ intros a [[Hfp | (b & m & Hb & Hr)] | [Hs | (b & m & Hb & Hr)]].
  - destruct (cmd_prog_unowned a Hfp) as (Himg & _). pose proof (pa_img_range a Himg). lia.
  - assert (Hbl : In (b, m) (ablocks B ly S))
      by (apply (Permutation_in _ (Permutation_sym HPerm)); right; apply in_or_app; right; apply in_or_app; left; exact Hb).
    destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbl) as (_ & Hb4 & Hbc & _). lia.
  - rewrite HFR in Hs. rewrite WS in Hslo. unfold LT_FRAME in Hs. lia.
  - destruct (al_blocks _ _ LAWS (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) b m (proj1 HPRE0) Hb)
      as (_ & Hb4 & Hbc & _). lia. }
(* the symbolic run from pc to the free wrapper *)
destruct (ltf_seed W regs mem pc) as (HS & SHOK & HEI & HAE & EEo).
remember (ltf_E regs) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (apply EEo; reflexivity).
assert (E23 : ew E 23 = getr regs 23) by (apply EEo; reflexivity).
assert (E24 : ew E 24 = getr regs 24) by (apply EEo; reflexivity).
assert (E25 : ew E 25 = getr regs 25) by (apply EEo; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
clear HE.
destruct Hpc as [[-> ->] | [[-> ->] | [-> ->]]];
  [ unfold ltf_ss in HS, SHOK | unfold ltf_ss in HS, SHOK | unfold ltf_ss in HS, SHOK ];
(paj_run_tok RUN HS HJ SHOK ltf_Bspan; try solve [apply awr_ok_nil]);
(lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end);
pmkst HS;
rewrite (pal_free B TL);
prreg HS (1%bv : bv 5) P1; prreg HS (10%bv : bv 5) P10; prreg HS (2%bv : bv 5) P2.
all: lazymatch goal with
| HFr : frame_of ?E0 _ (mrestrict _ _) (mrestrict _ ?m1) |- _ =>
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> rdW W m1 a = rdW W mem a)
    by (intros a Ha; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
        [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin'; destruct Hin' | exact Ha | intros Hff; destruct Hff ])
end.
all: lazymatch goal with
| |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  assert (HPT1 : aregs_preserved regs rT)
    by (eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs ltf_extra HS); [exact HAE | vm_compute; reflexivity]);
  assert (HspT : spZ rT = spZ regs) by (unfold spZ; f_equal; exact (eq_trans P2 E2));
  assert (Ha0 : getr rT 10 = w64 pa) by
    (etransitivity; [exact P10|];
     first [ exact (eq_trans E23 (eq_trans (ltf_pres_get regs0 regs 23 23%bv HPR0 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)) Hpa))
           | exact (eq_trans E24 (eq_trans (ltf_pres_get regs0 regs 24 24%bv HPR0 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)) Hpa))
           | exact (eq_trans E25 (eq_trans (ltf_pres_get regs0 regs 25 25%bv HPR0 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)) Hpa)) ]);
  assert (Hgp' : getr rT 3 = w64 (as_gp B))
    by exact (eq_trans (ltf_pres_get regs rT 3 3%bv HPT1 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)) Hgp);
  assert (Htp' : getr rT 4 = w64 (as_tp B))
    by exact (eq_trans (ltf_pres_get regs rT 4 4%bv HPT1 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)) Htp);
  assert (H8' : getr rT 8 = w64 32)
    by exact (eq_trans (ltf_pres_get regs rT 8 8%bv HPT1 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)) H8);
  assert (HraT : YK0s.ret_ok (getr rT 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]);
  assert (Hs0 : s0Z rT = 32)
    by (unfold s0Z; transitivity (bv_unsigned (w64 32)); [f_equal; exact H8' | unfold w64; apply unsigned_lit_small; lia]);
  assert (HraZ : 4096 <= raZ rT)
    by (unfold raZ; change (4096 <= bv_unsigned (getr rT (1%bv : bv 5)));
        rewrite P1; rewrite unsigned_lit_small by lia; lia);
  assert (Hch : chain_pre ly (rdW W mT) rT [])
    by (split;
        [ exact HraZ
        | destruct (frame0_ok ly rT) eqn:Hf0; [|reflexivity];
          replace (bad_next (spZ rT) (ly_top ly) (s0Z rT)) with true; [reflexivity|];
          unfold bad_next; rewrite Hs0;
          symmetry; apply orb_true_intro; left; apply orb_true_intro; left; apply Z.leb_le; rewrite HspT, Hsp; lia ])
end.
all: eapply SRr_bind;
  [ lazymatch goal with
    | |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
      exact (afree04_sub SEGS B LAWS Hsegs MT AFREE4 W rT mT LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx)
        (x_W cx) (x_mem cx) (x_md cx) [] ly S dT k pa n (- LT_FRAME) (getr rT 1) [] HJ Hin Ha0
        ltac:(rewrite HspT, Hsp, HFR; unfold LT_FRAME; lia) ltac:(reflexivity) ltac:(unfold LT_FRAME; lia)
        ltac:(rewrite WS; unfold ASTACK, LT_FRAME; lia)
        Hgp' Htp' eq_refl HraT Hnev Hch Hcov MOK)
    end
  | ].
all: cbv beta; intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl & Ebl2) & Hfr2 & HK2 & MLE & HJin).
all: rewrite P1; apply (HC ly2 S2 W2 regs2 mem2 md2); [| exact MLE]; split; [exact HJ2|]; split;
  [ (* the blocks left *)
    apply (Permutation_app_inv_l [(pa, n)]); cbn [app];
    eapply Permutation_trans; [| exact HPerm];
    rewrite Ebl2 in *; eapply Permutation_trans; [apply Permutation_middle | rewrite <- Ebl; apply Permutation_refl]
  | split;
    [ (* what is kept *)
      intros a Ha; etransitivity; [|exact (HK0 a Ha)]; etransitivity; [|exact (KEEP a (HBND a Ha))];
      destruct HK2 as (K1 & K2 & K3 & K4 & _);
      destruct Ha as [[Hfp | (b & m & Hb & Hr)] | [Hs | (b & m & Hb & Hr)]];
      [ destruct (cmd_prog_unowned a Hfp) as (Himg & Hown & Herr); exact (K3 a Himg Hown Herr)
      | assert (Hbl : In (b, m) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HPerm)); right; apply in_or_app; right; apply in_or_app; left; exact Hb);
        assert (Hne : (b, m) <> (pa, n)) by (intros Eq; injection Eq as -> ->; exact (HnO Hb));
        pose proof (ltf_sep B LAWS ly S W mem md b m pa n HAR Hbl Hin Hne) as Hdis;
        unfold zdisjoint in Hdis; cbn [fst snd] in Hdis;
        replace a with (b + (a - b)) by ring;
        apply (K2 b m (a - b) Hbl ltac:(lia));
        intros Hbad; cbv beta in Hbad; lia
      | apply (K1 a);
        [ lia
        | rewrite HFR in Hs; unfold ASTACK, LT_FRAME in *; lia ]
      | assert (Hbl : In (b, m) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HPerm)); right; apply in_or_app; right; apply in_or_app; right; exact Hb);
        assert (Hne : (b, m) <> (pa, n)) by (intros Eq; injection Eq as -> ->; exact (Hnb0 Hb));
        pose proof (ltf_sep B LAWS ly S W mem md b m pa n HAR Hbl Hin Hne) as Hdis;
        unfold zdisjoint in Hdis; cbn [fst snd] in Hdis;
        replace a with (b + (a - b)) by ring;
        apply (K2 b m (a - b) Hbl ltac:(lia));
        intros Hbad; cbv beta in Hbad; lia ]
    | exact (aregs_preserved_trans _ _ _ HPR0 (aregs_preserved_trans _ _ _ HPT1 HP2)) ] ].
Qed.


End f.
End d.
