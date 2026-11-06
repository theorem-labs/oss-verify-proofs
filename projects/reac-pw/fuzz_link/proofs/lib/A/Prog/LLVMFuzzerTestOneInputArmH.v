(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 176 of its 230 lines of code are new or changed and 350 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: the arm walks' helper kit (first written for op_decide,
   LLVMFuzzerTestOneInputOp4.v, and shared with op_write): register-only and one-slot symbolic entry states, the
   registers a stretch or a call leaves alone (d4_keepL), spill-slot words across a run or a callee, the text_of
   answer across a run, the fresh text block's separation facts, and four small tactics.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c model_decide_c check_verdict_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputFree.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputTxo.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputTxa LLVMFuzzerTestOneInputArmR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.


Ltac d4chk := repeat (apply Forall_cons; [vm_compute; reflexivity|]); apply Forall_nil.
Ltac kreg K r b H := pose proof (K r ltac:(cbn; tauto)) as H;
  replace (Z_to_bv 5 r) with b in H by (apply bv_eq; reflexivity).
(* a register of a run's state given by its entry atom *)
Ltac ew_reg EL r b Q := rewrite EL in Q by (unfold A_TEXT; lia);
  rewrite (ew_Ereg_nat _ _ r b eq_refl) in Q.
(* a callee-saved register across a call *)
Ltac preg HP r b H := pose proof (HP r ltac:(unfold acallee_saved; lia)) as H;
  replace (Z_to_bv 5 r) with b in H by (apply bv_eq; reflexivity).

(* a register-only stretch: the registers as their atoms, no region, no fact *)
Definition d4_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.


(* the entry state of a register-only stretch at any pc *)
Lemma d4_entry : forall (fy : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) mem pc,
  st_ok_pi (fx := fy) SEGS VAL (Eimg (Ereg regs [])) (d4_ss pc)
    (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros fy W regs mem pc. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [|split; exact I]. exact I.
Qed.

Lemma d4_dec_run : forall ly S (m m' : word -> option byte) s t,
  kagree SEGS (fun _ => False) m m' -> dec_ans B ly S m s t -> dec_ans B ly S m' s t.
Proof.
  intros ly S m m' s t HK [Ht | (k & Hin & Hk & Hcs)]; [left; exact Ht|].
  right. exists k. split; [exact Hin|]. split; [exact Hk|]. exact (acstr_keep SEGS _ _ _ s t HK (fun _ _ H => H) Hcs).
Qed.

(* a stretch that loads one spill slot at s1 + off: the region on s1's atom 9, the slot's word as atom 32 *)
Definition d4_slot (off : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) off (off + 8) off off [YP09.mkChunk off (CVal 8 (SOff 32 0))].
Definition d4_facts_l : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 0 (2 ^ 64 - 1) 0)] [] [].
Definition d4_ssl (pc off : Z) : sstate := mkSS pc sr_atoms [d4_slot off] None d4_facts_l.

Lemma d4_entry_l : forall (fy : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) mem pc off v,
  2 ^ 46 <= bv_unsigned (getr regs 9) <= 2 ^ 47 -> bv_unsigned (getr regs 9) mod 32 = 0 ->
  0 <= off < 2 ^ 12 -> 0 <= v < 2 ^ 64 ->
  regions_wf [d4_slot off] = true ->
  val_mem SEGS (mrestrict (w_H W) mem) (bv_unsigned (getr regs 9) + off) 8 v ->
  st_ok_pi (fx := fy) SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 v])) (d4_ssl pc off)
    (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros fy W regs mem pc off v H9 H32 Hoff Hv Hwf Hval.
  set (E := Eimg (Ereg regs [Z_to_bv 64 v])).
  assert (E9 : ew E 9 = getr regs 9)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 v)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  rewrite restrict_mkst_fx. unfold d4_ssl. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - exact Hwf.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, d4_slot.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    fold E. rewrite E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (bv_unsigned (getr regs 9)) off 8 (SOff 32 0) v);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia |].
    exact Hval.
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [d4_facts_l f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite E9, E32. rewrite unsigned_lit_small by lia.
    change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* a spill-slot word above s1 across a callee whose write set misses it, and across a run *)
Lemma d4_slot_callee : forall cx K ly3 S3 ly2 S2 (W3 : world SEGS) mem3 (W2 : world SEGS) mem2 (E : Z -> Prop) a v,
  lf_call B cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E ->
  lf_sp1 cx <= a -> a + 8 <= spZ (c_regs cx) -> (forall i, 0 <= i < 8 -> ~ E (a + i)) ->
  rdword (aview SEGS (w_H W3) mem3) a = Some v -> rdword (aview SEGS (w_H W2) mem2) a = Some v.
Proof.
  intros cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E a v HC H1 H2 HE Hr.
  pose proof HC as (HK & Hc & _).
  rewrite <- ard_aview in *.
  apply (rdword_keep SEGS _ _ _ a v (lf_call_kagree B cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E HC)); [|exact Hr].
  intros i Hi. apply (lfx_above B cx K ly3 S3 ly2 S2 E (a + i) HK Hc); [lia | exact (HE i Hi)].
Qed.

Lemma d4_slot_run : forall (W : world SEGS) (m m' : word -> option byte) a v,
  kagree SEGS (fun _ => False) (rdW W m) (rdW W m') ->
  rdword (aview SEGS (w_H W) m) a = Some v -> rdword (aview SEGS (w_H W) m') a = Some v.
Proof.
  intros W m m' a v HK Hr. rewrite <- ard_aview in *.
  exact (rdword_keep SEGS _ _ _ a v HK (fun _ _ H => H) Hr).
Qed.

(* the registers a stretch of the arm leaves alone *)
Definition d4_keepL (rs : list Z) (r1 r2 : bvmap 5 word) : Prop :=
  forall r, In r rs -> getr r2 (Z_to_bv 5 r) = getr r1 (Z_to_bv 5 r).
Definition D4R : list Z := [2; 3; 4; 8; 9; 19; 22; 23; 24; 25; 26; 27].

Lemma d4_keep_trans : forall rs a b c, d4_keepL rs a b -> d4_keepL rs b c -> d4_keepL rs a c.
Proof. intros rs a b c H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma d4_keep_pres : forall rs a b, (forall r, In r rs -> acallee_saved r) -> aregs_preserved a b -> d4_keepL rs a b.
Proof. intros rs a b Hc HP r Hr. exact (HP r (Hc r Hr)). Qed.

Lemma d4_keep_run : forall (fy : YK11.FPState) (W : world SEGS) E ss ms regs0 ex rs,
  st_ok (fx := fy) SEGS E ss (restrict (w_H W) ms) ->
  (forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs0 ex) n) ->
  (forall r, In r rs -> Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r)) ->
  Forall (fun r => sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff (Z.to_nat r) 0) rs ->
  d4_keepL rs regs0 (ms_regs ms).
Proof.
  intros fy W E ss ms regs0 ex rs HS EL Hrs HF r Hr.
  rewrite Forall_forall in HF. pose proof (HF r Hr) as Hs. pose proof (Hrs r Hr) as R.
  pose proof (bv_unsigned_in_range 5 (Z_to_bv 5 r)) as Rr. change (bv_modulus 5) with 32 in Rr.
  rewrite (st_ok_restrict_reg (fx := fy) SEGS (w_H W) E ss ms _ HS), Hs.
  cbn [sv_denot]. rewrite EL by (unfold A_TEXT; lia).
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply ew_Ereg_nat. exact R.
Qed.

Lemma D4R_saved : forall r, In r D4R -> acallee_saved r.
Proof. intros r Hr. unfold acallee_saved. cbn in Hr. lia. Qed.
Lemma D4R_low : forall r, In r D4R -> Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r).
Proof. intros r Hr. cbn in Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. Qed.
Lemma D4S5_saved : forall r, In r [21] -> acallee_saved r.
Proof. intros r Hr. unfold acallee_saved. cbn in Hr. lia. Qed.
Lemma D4S5_low : forall r, In r [21] -> Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r).
Proof. intros r Hr. cbn in Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. Qed.


(* the four cursor / out-slot words of op_decide *)
Definition d4_sl4 (cx : lcx) (W : world SEGS) (m : word -> option byte) (P N o1 o2 : Z) : Prop :=
  rdword (aview SEGS (w_H W) m) (lf_sp1 cx + LS_P) = Some P /\
  rdword (aview SEGS (w_H W) m) (lf_sp1 cx + LS_N) = Some N /\
  rdword (aview SEGS (w_H W) m) (lf_sp1 cx + LS_T130) = Some o1 /\
  rdword (aview SEGS (w_H W) m) (lf_sp1 cx + LS_T128) = Some o2.

Lemma d4_sl4_run : forall cx (W : world SEGS) m m' P N o1 o2,
  kagree SEGS (fun _ => False) (rdW W m) (rdW W m') -> d4_sl4 cx W m P N o1 o2 -> d4_sl4 cx W m' P N o1 o2.
Proof.
  intros cx W m m' P N o1 o2 HK (H1 & H2 & H3 & H4).
  split; [exact (d4_slot_run W m m' _ _ HK H1)|]. split; [exact (d4_slot_run W m m' _ _ HK H2)|].
  split; [exact (d4_slot_run W m m' _ _ HK H3) | exact (d4_slot_run W m m' _ _ HK H4)].
Qed.

Lemma d4_sl4_callee : forall cx K ly3 S3 ly2 S2 (W3 : world SEGS) mem3 (W2 : world SEGS) mem2 (E : Z -> Prop)
    P N o1 o2,
  lf_call B cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E ->
  (forall a, E a -> ~ (lf_sp1 cx + LS_P <= a < lf_sp1 cx + LS_T130 + 8)) ->
  lf_sp1 cx + LS_T130 + 8 <= spZ (c_regs cx) ->
  d4_sl4 cx W3 mem3 P N o1 o2 -> d4_sl4 cx W2 mem2 P N o1 o2.
Proof.
  intros cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E P N o1 o2 HC HE Hhi (H1 & H2 & H3 & H4).
  unfold d4_sl4. unfold LS_P, LS_N, LS_T128, LS_T130 in *.
  split; [apply (d4_slot_callee cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E _ P HC); [lia | lia | | exact H1];
          intros j Hj HEj; apply (HE _ HEj); lia|].
  split; [apply (d4_slot_callee cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E _ N HC); [lia | lia | | exact H2];
          intros j Hj HEj; apply (HE _ HEj); lia|].
  split; [apply (d4_slot_callee cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E _ o1 HC); [lia | lia | | exact H3];
          intros j Hj HEj; apply (HE _ HEj); lia|].
  apply (d4_slot_callee cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E _ o2 HC); [lia | lia | | exact H4].
  intros j Hj HEj; apply (HE _ HEj); lia.
Qed.

Lemma d4_nb_in : forall own1 nb ly S ly' S', tx_nb own1 nb ->
  (own1 <> 0 -> ablocks B ly' S' = ablocks B ly S ++ nb) -> forall b, In b nb -> In b (ablocks B ly' S').
Proof.
  intros own1 nb ly S ly' S' [(_ & ->) | (k1 & Hne & _ & _ & ->)] H b Hb; [destruct Hb|].
  rewrite (H Hne). apply in_or_app. right. exact Hb.
Qed.

Lemma d4_nb_req : forall own1 nb, tx_nb own1 nb -> forall b, In b nb -> 1 <= req_size (snd b).
Proof.
  intros own1 nb [(_ & ->) | (k1 & _ & _ & Hk & ->)] b Hb; [destruct Hb|]. destruct Hb as [<- | []].
  cbn [snd]. unfold req_size. destruct (k1 =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia].
Qed.

Lemma d4_fresh_ok : forall cx md mk T3 own ly S nb,
  lf_bl B cx own T3 ly S -> In (md, MD_SIZE) (ablocks B ly S) -> In (mk, MK_SIZE) (ablocks B ly S) ->
  incl T3 (ablocks B ly S) -> (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly S)) ->
  (forall c b, In c (ablocks B ly S) -> In b nb -> zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b))) ->
  (forall b, In b nb -> 1 <= req_size (snd b)) ->
  forall b, In b nb -> ~ In b (ablocks B (c_ly cx) (c_S cx)) /\
    (forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
       zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b))).
Proof.
  intros cx md mk T3 own ly S nb (D & HT & HP) Hmd Hmk Hinc HPB Hap Hreq b Hb. split.
  - intros Hin. assert (Hin' : In b (ablocks B ly S)).
    { apply (Permutation_in b (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. right. exact Hin. }
    pose proof (Hap b b Hin' Hb) as D'. unfold zdisjoint in D'. cbn [fst snd] in D'. pose proof (Hreq b Hb). lia.
  - intros c [-> | [-> | [Hc | (Hn & ->)]]].
    + exact (Hap _ b Hmd Hb).
    + exact (Hap _ b Hmk Hb).
    + exact (Hap c b (Hinc c Hc) Hb).
    + exact (Hap _ b (HPB Hn) Hb).
Qed.

Lemma d4_keep_run_pi : forall (fy : YK11.FPState) (W : world SEGS) E ss ms regs0 ex rs,
  st_ok_pi (fx := fy) SEGS pa_val E ss (restrict (w_H W) ms) ->
  (forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs0 ex) n) ->
  (forall r, In r rs -> Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r)) ->
  Forall (fun r => sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff (Z.to_nat r) 0) rs ->
  d4_keepL rs regs0 (ms_regs ms).
Proof.
  intros fy W E ss ms regs0 ex rs HS EL Hrs HF r Hr.
  rewrite Forall_forall in HF. pose proof (HF r Hr) as Hs. pose proof (Hrs r Hr) as R.
  pose proof (bv_unsigned_in_range 5 (Z_to_bv 5 r)) as Rr. change (bv_modulus 5) with 32 in Rr.
  rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W) E ss ms _ HS), Hs.
  cbn [sv_denot]. rewrite EL by (unfold A_TEXT; lia).
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply ew_Ereg_nat. exact R.
Qed.


End a.
