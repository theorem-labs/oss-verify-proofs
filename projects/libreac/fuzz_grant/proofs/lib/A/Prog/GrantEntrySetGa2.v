(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetGa2), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* The set loop of fuzz_grant's entry function LLVMFuzzerTestOneInput on the ASan build:
   the piece GA2 → G78 | the call at 0x80c20 (fuzz/fuzz_grant.c:208-226), for a cell whose
   three bytes the turn read (GrantEntrySetDefs.v, `seg_ga2_stmt`).

     0x80b58 .. 0x80b60  s9 = the set's answer; a parameter below 3 goes to 0x80b84.
     0x80b64 .. 0x80b80  a parameter of 3 or more: reac_headamp_tx_effective (call at
                         0x80b70) and reac_headamp_default (call at 0x80b7c) must both
                         answer 0, else the error path at 0x81a0c (__asan_handle_no_return,
                         then the C library's process stop). They answer 0:
                         HeadampModel.eff_p3 and dflt.
     0x80b84 .. 0x80c10  the harness's own answer: -1 for a channel of 48 or more, else 0
                         exactly when the value is legal for the parameter. An answer of
                         the set that differs goes to 0x81a0c; the turn's facts exclude it
                         (HeadampModel.legalb). Then s9 = 0 goes to the call at 0x80c20
                         (call_e2_stmt), any other s9 to 0x80c78 (G78).

   The piece is cut at the two returns, 0x80b74 and 0x80b80 (GAR), and at 0x80b84 (GAB):
   each part builds its own symbolic state from the machine state the cut describes. No
   part reads or writes memory itself: the memory facts carry over the runs (each run's
   frame is empty) and over the two calls (gkeep_call0: FP = []). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1g YC1h YC85 YC88 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs GrantEntrySetDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import HeadampTxEffective HeadampDefault.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegSetModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the model facts the checks rest on (HeadampModel.v: dflt :6, legalb :58) ---- *)
Lemma dflt_ne2 : forall q, q <> 2 -> dflt q = 0.
Proof. intros q H. unfold dflt. rewrite (proj2 (Z.eqb_neq q 2) H). reflexivity. Qed.

(* For a parameter other than 2 the harness tests `param < 3 && value < 2`. *)
Lemma legalb_ne2 : forall q v, q <> 2 -> 0 <= q -> legalb q v = (v <? 2) && (q <? 3).
Proof.
  intros q v Hq H0. unfold legalb.
  destruct (Z.ltb_spec q 2), (Z.ltb_spec q 3), (Z.eqb_spec q 2), (Z.leb_spec v 1), (Z.ltb_spec v 2);
    cbn [andb orb]; first [reflexivity | exfalso; lia].
Qed.

(* For the parameter 2 it tests `value < 56`. *)
Lemma legalb_2 : forall v, legalb 2 v = (v <? 56).
Proof.
  intros v. unfold legalb. destruct (Z.leb_spec v 55), (Z.ltb_spec v 56); cbn; first [reflexivity | exfalso; lia].
Qed.

(* ---- the values the branches compare ---- *)
Lemma U_w64 : forall E n v, ew E n = w64 v -> U E (SOff n 0) = v mod 2 ^ 64.
Proof.
  intros E n v H. rewrite U_SOff, H, Z.add_0_r. unfold w64. rewrite Z_to_bv_unsigned.
  unfold zcanon, bv_wrap, M64. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.

(* a0 at 0x80c0c for a parameter other than 2: ((s8 <u 2) & (s7 <u 3)) - 1. *)
Lemma U_chk3 : forall E q v, ew E 23 = w64 q -> ew E 24 = w64 v -> 0 <= q < 256 -> 0 <= v < 256 ->
  U E (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_SLTU (SOff 24 0) (SLit 2)) (SAlu ALU_SLTU (SOff 23 0) (SLit 3)))
         (SLit (-1)))
  = (if (v <? 2) && (q <? 3) then 0 else -1) mod 2 ^ 64.
Proof.
  intros E q v E23 E24 Hq Hv.
  rewrite !U_SAlu, (U_atom E 23 q E23), (U_atom E 24 v E24), !U_SLit by lia.
  change (zcanon 2) with 2. change (zcanon 3) with 3. cbn [zalu_raw].
  destruct (v <? 2), (q <? 3); vm_compute; reflexivity.
Qed.

(* a0 at 0x80c0c for the parameter 2: (s8 <u 56) - 1. *)
Lemma U_chk56 : forall E v, ew E 24 = w64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 24 0) (SLit 56)) (SLit (-1))) = (if v <? 56 then 0 else -1) mod 2 ^ 64.
Proof.
  intros E v E24 Hv. rewrite !U_SAlu, (U_atom E 24 v E24), !U_SLit by lia.
  change (zcanon 56) with 56. cbn [zalu_raw].
  destruct (v <? 56); vm_compute; reflexivity.
Qed.

(* ---- walk tactics ---- *)
Ltac curms HS := lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?m) => m
  | st_ok _ _ _ (restrict _ ?m) => m
  end.
(* The memory after runs whose frames are empty is the memory before them. *)
Ltac memeq ms0 :=
  let a := fresh "a" in intros a; cbn [ms_mem mkst];
  repeat match goal with
  | |- aview _ _ (ms_mem ms0) _ = _ => reflexivity
  | H : frame_of _ _ (ms_mem ?m1) (ms_mem ?m2) |- aview _ _ (ms_mem ?m2) _ = _ =>
      rewrite (frame_nil_eq _ _ _ _ _ eq_refl H a)
  end.
(* A register the run kept: its atom is the register at the cut. *)
Ltac kgoal HS ER :=
  lazymatch goal with |- getr _ ?r = getr _ _ =>
    let X := fresh "X" in prreg HS r X; rewrite X; apply ER; reflexivity end.
(* A register whose value the cut's atoms give. *)
Ltac vgoal HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    let X := fresh "X" in prreg HS r X; rewrite X;
    first [ reflexivity | assumption | (unfold w64; f_equal; lia) ] end.

Section a.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis CALLE2 : call_e2_stmt B MT.
Hypothesis EFFH : theadamp_tx_effective_spec B.
Hypothesis DFLH : treac_headamp_default_spec B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- the cuts inside the piece ---- *)
(* What 0x80b74, 0x80b80 and 0x80b84 share: turn i, the table the set left, the arrays
   of turn i, s9 = the set's answer, s2 s7 s8 = the channel, the parameter and the value,
   s10 = the cursor past the cell. *)
Definition gb_at (pc : Z) (n i : nat) (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate)
  (W3 : world SEGS) (ms3 : machine_state) (t : Z) : Prop :=
  gcore B MT cx fp k acc ly3 S3 ms3 pc n i t /\
  gmem cx fp W3 ms3 t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i)
       (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))) /\
  getr (ms_regs ms3) 25 = w64 (if gacc (c_pl cx) i then 0 else -1) /\
  getr (ms_regs ms3) 18 = w64 (gc (c_pl cx) i) /\ getr (ms_regs ms3) 23 = w64 (gq (c_pl cx) i) /\
  getr (ms_regs ms3) 24 = w64 (gv (c_pl cx) i) /\
  getr (ms_regs ms3) 26 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))).

(* 0x80b84: the harness computes its own answer. *)
Definition GAB (n i : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t, gb_at 0x4d4 n i cx fp k acc ly3 S3 W3 ms3 t.

(* 0x80b74 (pc 0x4c4) and 0x80b80 (pc 0x4d0): a callee returned 0 for a parameter of 3
   or more. *)
Definition GAR (pc : Z) (n i : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t, gb_at pc n i cx fp k acc ly3 S3 W3 ms3 t /\ 3 <= gq (c_pl cx) i /\ getr (ms_regs ms3) 10 = w64 0.

(* ---- the symbolic state of a cut: every register its own atom, no memory ---- *)
Definition ssg (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

Lemma g_st0 : forall (W3 : world SEGS) (regs : bvmap 5 word) mem pc E, E = Eimg (Ereg regs []) ->
  st_ok_pi SEGS VAL E (ssg pc) (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros W3 regs mem pc E ->. rewrite restrict_mkst_fx. unfold ssg. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I].
Qed.

Lemma g_ER : forall (regs : bvmap 5 word) E, E = Eimg (Ereg regs []) ->
  forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r.
Proof. intros regs E -> m r Hr. apply ew_Eimg_Ereg_nat. exact Hr. Qed.

(* ---- landing in a cut ---- *)
Lemma g_landB : forall pc1 n i cx fp k acc ly3 S3 W3 ms3 msF t pc0,
  gcore B MT cx fp k acc ly3 S3 ms3 pc0 n i t ->
  ms_pc_val msF = w64 (BASE + pc1) -> ms_resv msF = None -> ms_svc_pending msF = None ->
  ms_rom msF = seg_rom SEGS -> ms_fregs msF = fp_regs -> ms_fcsr msF = fp_csr ->
  getr (ms_regs msF) 2 = getr (ms_regs ms3) 2 -> getr (ms_regs msF) 3 = getr (ms_regs ms3) 3 ->
  getr (ms_regs msF) 4 = getr (ms_regs ms3) 4 -> getr (ms_regs msF) 8 = getr (ms_regs ms3) 8 ->
  getr (ms_regs msF) 9 = getr (ms_regs ms3) 9 -> getr (ms_regs msF) 19 = getr (ms_regs ms3) 19 ->
  getr (ms_regs msF) 20 = getr (ms_regs ms3) 20 -> getr (ms_regs msF) 22 = getr (ms_regs ms3) 22 ->
  getr (ms_regs msF) 27 = getr (ms_regs ms3) 27 ->
  gmem cx fp W3 msF t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i)
       (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))) ->
  getr (ms_regs msF) 25 = w64 (if gacc (c_pl cx) i then 0 else -1) ->
  getr (ms_regs msF) 18 = w64 (gc (c_pl cx) i) -> getr (ms_regs msF) 23 = w64 (gq (c_pl cx) i) ->
  getr (ms_regs msF) 24 = w64 (gv (c_pl cx) i) ->
  getr (ms_regs msF) 26 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))) ->
  gb_at pc1 n i cx fp k acc ly3 S3 W3 msF t.
Proof.
  intros pc1 n i cx fp k acc ly3 S3 W3 ms3 msF t pc0
    ((_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4) & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H22 & H27)
    Pc Prv Psv Pro Pfr Pfc K2 K3 K4 K8 K9 K19 K20 K22 K27 HM R25 R18 R23 R24 R26.
  unfold gb_at, gcore, gmach, gregs. splits; try assumption; congruence.
Qed.

(* A refused set lands in G78: the arrays are those of turn i, which are those of turn
   i + 1 (GrantEntrySetDefs.gtables_S). *)
Lemma g_land78 : forall n i cx fp k acc ly3 S3 W3 ms3 msF md t pc0,
  gcore B MT cx fp k acc ly3 S3 ms3 pc0 n i t ->
  gmem cx fp W3 ms3 t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i)
       (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))) ->
  getr (ms_regs ms3) 26 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))) ->
  gacc (c_pl cx) i = false ->
  ms_pc_val msF = w64 (BASE + 0x5c8) -> ms_resv msF = None -> ms_svc_pending msF = None ->
  ms_rom msF = seg_rom SEGS -> ms_fregs msF = fp_regs -> ms_fcsr msF = fp_csr ->
  getr (ms_regs msF) 2 = getr (ms_regs ms3) 2 -> getr (ms_regs msF) 3 = getr (ms_regs ms3) 3 ->
  getr (ms_regs msF) 4 = getr (ms_regs ms3) 4 -> getr (ms_regs msF) 8 = getr (ms_regs ms3) 8 ->
  getr (ms_regs msF) 9 = getr (ms_regs ms3) 9 -> getr (ms_regs msF) 19 = getr (ms_regs ms3) 19 ->
  getr (ms_regs msF) 20 = getr (ms_regs ms3) 20 -> getr (ms_regs msF) 22 = getr (ms_regs ms3) 22 ->
  getr (ms_regs msF) 27 = getr (ms_regs ms3) 27 -> getr (ms_regs msF) 21 = getr (ms_regs ms3) 26 ->
  (forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  G78 B MT n i cx fp k acc ly3 S3 W3 msF md.
Proof.
  intros n i cx fp k acc ly3 S3 W3 ms3 msF md t pc0
    ((_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4) & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H22 & H27)
    HM R26 Hgq Pc Prv Psv Pro Pfr Pfc K2 K3 K4 K8 K9 K19 K20 K22 K27 K21 HMEQ.
  destruct (gtables_S (c_pl cx) i) as (_ & EW & ES). rewrite Hgq in EW, ES.
  exists t. split; [|split].
  - unfold gcore, gmach, gregs. splits; try assumption; congruence.
  - rewrite EW, ES. exact (gmem_tr cx fp W3 ms3 msF t _ _ _ _ HMEQ HM).
  - rewrite K21. exact R26.
Qed.

(* ---- 0x80b84 .. 0x80c20: the harness's answer, the check, and the exit ---- *)
Lemma ga2_tail : forall POST n i,
  ge_from B MT POST (G78 B MT n i) -> ge_from B MT POST (GE2 B MT n i) -> ge_from B MT POST (GAB n i).
Proof.
  intros POST n i HN HE2 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO (t & HC & HM & R25 & R18 & R23 & R24 & R26).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H22 & H27).
  pose proof HMA as (_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4).
  pose proof (gcell_ok (c_pl cx) i) as (Hc0 & Hq0 & Hv0).
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  set (c := gc (c_pl cx) i) in *. set (q := gq (c_pl cx) i) in *. set (v := gv (c_pl cx) i) in *.
  assert (HGA : gacc (c_pl cx) i = (c <? 48) && legalb q v) by reflexivity.
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  pose proof (g_ER _ _ HE) as ER.
  assert (E2 : ew E 2 = w64 (c_sp1 cx)) by (rewrite (ER 2%nat 2%bv eq_refl); exact G2).
  assert (E3 : ew E 3 = getr (c_regs cx) 3) by (rewrite (ER 3%nat 3%bv eq_refl); exact G3).
  assert (E4 : ew E 4 = getr (c_regs cx) 4) by (rewrite (ER 4%nat 4%bv eq_refl); exact G4).
  assert (E8 : ew E 8 = w64 (spZ (c_regs cx))) by (rewrite (ER 8%nat 8%bv eq_refl); exact G8).
  assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact G9).
  assert (E18 : ew E 18 = w64 c) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  assert (E19 : ew E 19 = w64 (gF cx fp)) by (rewrite (ER 19%nat 19%bv eq_refl); exact H19).
  assert (E20 : ew E 20 = w64 t) by (rewrite (ER 20%nat 20%bv eq_refl); exact H20).
  assert (E22 : ew E 22 = w64 (gF cx fp)) by (rewrite (ER 22%nat 22%bv eq_refl); exact H22).
  assert (E23 : ew E 23 = w64 q) by (rewrite (ER 23%nat 23%bv eq_refl); exact R23).
  assert (E24 : ew E 24 = w64 v) by (rewrite (ER 24%nat 24%bv eq_refl); exact R24).
  assert (E25 : ew E 25 = w64 (if gacc (c_pl cx) i then 0 else -1)) by (rewrite (ER 25%nat 25%bv eq_refl); exact R25).
  assert (E26 : ew E 26 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i)))) by (rewrite (ER 26%nat 26%bv eq_refl); exact R26).
  assert (E27 : ew E 27 = w64 (Z.of_nat (S n))) by (rewrite (ER 27%nat 27%bv eq_refl); exact H27).
  pose proof (g_st0 W3 (ms_regs ms3) (ms_mem ms3) 0x4d4 E HE) as HS.
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  unfold ssg in HS.
  paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
  (* 0x80b88: bgeu s2, 48 *)
  psrr_branch_tok RUN BR HS SHOK GBspan; rewrite branch_geu_U, (U_atom E 18 c E18), U_lit in Hc by lia.
  - (* the channel is 48 or more: the set refused it, and so does the harness (a0 = -1) *)
    apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hc48.
    assert (HGF : gacc (c_pl cx) i = false) by (rewrite HGA, (proj2 (Z.ltb_ge c 48) Hc48); reflexivity).
    rewrite HGF in E25.
    paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
    (* 0x80c0c: bne s9, a0 into 0x81a0c *)
    psrr_branch_tok RUN BR HS SHOK GBspan;
      rewrite branch_ne_U, (U_w64 E 25 _ E25), U_lit in Hc by lia; vm_compute in Hc.
    + discriminate Hc.
    + clear Hc. paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
      (* 0x80c10: bnez s9 *)
      psrr_branch_tok RUN BR HS SHOK GBspan;
        rewrite branch_ne_U, (U_w64 E 25 _ E25), U_lit in Hc by lia; vm_compute in Hc.
      * clear Hc. paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x5c8; [first [apply awr_ok_nil | gshow] |].
        let msF := curms HS in apply (HN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO).
        destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
        apply (g_land78 n i cx fp k acc ly3 S3 W3 ms3 _ _ t 0x4d4 HC HM R26 HGF Pc Prv Psv Pro Pfr Pfc).
        all: first [kgoal HS ER | memeq ms3].
      * discriminate Hc.
  - (* the channel is below 48 *)
    apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hc48.
    paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
    (* 0x80b90: bne s7, 2 *)
    psrr_branch_tok RUN BR HS SHOK GBspan; rewrite branch_ne_U, (U_atom E 23 q E23), U_lit in Hc by lia.
    + (* a parameter other than 2 *)
      apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hqn2.
      assert (Hgq : gacc (c_pl cx) i = (v <? 2) && (q <? 3))
        by (rewrite HGA, (proj2 (Z.ltb_lt c 48) Hc48), legalb_ne2 by lia; reflexivity).
      rewrite Hgq in E25.
      paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
      (* 0x80c0c: bne s9, a0 into 0x81a0c *)
      psrr_branch_tok RUN BR HS SHOK GBspan;
        rewrite branch_ne_U, (U_w64 E 25 _ E25), (U_chk3 E q v E23 E24) in Hc by lia.
      * rewrite Z.eqb_refl in Hc. cbn in Hc. discriminate Hc.
      * clear Hc. paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
        (* 0x80c10: bnez s9 *)
        psrr_branch_tok RUN BR HS SHOK GBspan;
          rewrite branch_ne_U, (U_w64 E 25 _ E25), U_lit in Hc by lia;
          revert Hc; destruct ((v <? 2) && (q <? 3)) eqn:HB2; intros Hc; vm_compute in Hc.
        -- discriminate Hc.
        -- assert (HGF : gacc (c_pl cx) i = false) by (rewrite Hgq; first [reflexivity | exact HB2]). clear Hc.
           paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x5c8; [first [apply awr_ok_nil | gshow] |].
           let msF := curms HS in apply (HN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO).
           destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
           apply (g_land78 n i cx fp k acc ly3 S3 W3 ms3 _ _ t 0x4d4 HC HM R26 HGF Pc Prv Psv Pro Pfr Pfc).
           all: first [kgoal HS ER | memeq ms3].
        -- assert (HGT : gacc (c_pl cx) i = true) by (rewrite Hgq; first [reflexivity | exact HB2]). clear Hc.
           paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
           pmkst HS. rewrite pa_sigma_reac_headamp_tx_effective.
           apply (CALLE2 POST n i cx fp k acc ly3 S3 W3 _ _ _ t HE2 HB HJ HFR HMO Hk Hacc Hbl Ht0 Hn Hns HGT).
           all: first [vgoal HS | (apply (gmem_tr cx fp W3 ms3); [memeq ms3 | exact HM])].
        -- discriminate Hc.
    + (* the parameter 2 *)
      apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hq2.
      assert (Hgq : gacc (c_pl cx) i = (v <? 56))
        by (rewrite HGA, (proj2 (Z.ltb_lt c 48) Hc48), Hq2, legalb_2; reflexivity).
      rewrite Hgq in E25.
      paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
      (* 0x80c0c: bne s9, a0 into 0x81a0c *)
      psrr_branch_tok RUN BR HS SHOK GBspan;
        rewrite branch_ne_U, (U_w64 E 25 _ E25), (U_chk56 E v E24) in Hc by lia.
      * rewrite Z.eqb_refl in Hc. cbn in Hc. discriminate Hc.
      * clear Hc. paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
        (* 0x80c10: bnez s9 *)
        psrr_branch_tok RUN BR HS SHOK GBspan;
          rewrite branch_ne_U, (U_w64 E 25 _ E25), U_lit in Hc by lia;
          revert Hc; destruct (v <? 56) eqn:HB2; intros Hc; vm_compute in Hc.
        -- discriminate Hc.
        -- assert (HGF : gacc (c_pl cx) i = false) by (rewrite Hgq; first [reflexivity | exact HB2]). clear Hc.
           paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x5c8; [first [apply awr_ok_nil | gshow] |].
           let msF := curms HS in apply (HN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO).
           destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
           apply (g_land78 n i cx fp k acc ly3 S3 W3 ms3 _ _ t 0x4d4 HC HM R26 HGF Pc Prv Psv Pro Pfr Pfc).
           all: first [kgoal HS ER | memeq ms3].
        -- assert (HGT : gacc (c_pl cx) i = true) by (rewrite Hgq; first [reflexivity | exact HB2]). clear Hc.
           paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
           pmkst HS. rewrite pa_sigma_reac_headamp_tx_effective.
           apply (CALLE2 POST n i cx fp k acc ly3 S3 W3 _ _ _ t HE2 HB HJ HFR HMO Hk Hacc Hbl Ht0 Hn Hns HGT).
           all: first [vgoal HS | (apply (gmem_tr cx fp W3 ms3); [memeq ms3 | exact HM])].
        -- discriminate Hc.
Qed.

(* ---- 0x80b80: reac_headamp_default answered 0 ---- *)
Lemma ga2_r2 : forall POST n i, ge_from B MT POST (GAB n i) -> ge_from B MT POST (GAR 0x4d0 n i).
Proof.
  intros POST n i HTB cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO
    (t & (HC & HM & R25 & R18 & R23 & R24 & R26) & Hq3 & R10).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H22 & H27).
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  pose proof (g_ER _ _ HE) as ER.
  assert (E10 : ew E 10 = w64 0) by (rewrite (ER 10%nat 10%bv eq_refl); exact R10).
  assert (E18 : ew E 18 = w64 (gc (c_pl cx) i)) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  assert (E23 : ew E 23 = w64 (gq (c_pl cx) i)) by (rewrite (ER 23%nat 23%bv eq_refl); exact R23).
  assert (E24 : ew E 24 = w64 (gv (c_pl cx) i)) by (rewrite (ER 24%nat 24%bv eq_refl); exact R24).
  assert (E25 : ew E 25 = w64 (if gacc (c_pl cx) i then 0 else -1)) by (rewrite (ER 25%nat 25%bv eq_refl); exact R25).
  assert (E26 : ew E 26 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i)))) by (rewrite (ER 26%nat 26%bv eq_refl); exact R26).
  pose proof (g_st0 W3 (ms_regs ms3) (ms_mem ms3) 0x4d0 E HE) as HS.
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  unfold ssg in HS.
  paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
  (* 0x80b80: bnez a0 into 0x81a0c *)
  psrr_branch_tok RUN BR HS SHOK GBspan; rewrite branch_ne_U, (U_atom E 10 0 E10), U_lit in Hc by lia.
  - cbn in Hc. discriminate Hc.
  - paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x4d4; [first [apply awr_ok_nil | gshow] |].
    let msF := curms HS in apply (HTB cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO).
    destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
    exists t. apply (g_landB 0x4d4 n i cx fp k acc ly3 S3 W3 ms3 _ t 0x4d0 HC Pc Prv Psv Pro Pfr Pfc).
    all: first [kgoal HS ER | vgoal HS | (apply (gmem_tr cx fp W3 ms3); [memeq ms3 | exact HM])].
Qed.

(* ---- 0x80b74: reac_headamp_tx_effective answered 0; the call of reac_headamp_default ---- *)
Lemma ga2_r1 : forall POST n i, ge_from B MT POST (GAR 0x4d0 n i) -> ge_from B MT POST (GAR 0x4c4 n i).
Proof.
  intros POST n i HTR cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO
    (t & (HC & HM & R25 & R18 & R23 & R24 & R26) & Hq3 & R10).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H22 & H27).
  pose proof HMA as (_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4).
  pose proof (gcell_ok (c_pl cx) i) as (Hc0 & Hq0 & Hv0).
  pose proof (gtables_inv (c_pl cx) i) as (LT & LW & LS & _ & _).
  pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  set (q := gq (c_pl cx) i) in *.
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  pose proof (g_ER _ _ HE) as ER.
  assert (E2 : ew E 2 = w64 (c_sp1 cx)) by (rewrite (ER 2%nat 2%bv eq_refl); exact G2).
  assert (E3 : ew E 3 = getr (c_regs cx) 3) by (rewrite (ER 3%nat 3%bv eq_refl); exact G3).
  assert (E4 : ew E 4 = getr (c_regs cx) 4) by (rewrite (ER 4%nat 4%bv eq_refl); exact G4).
  assert (E8 : ew E 8 = w64 (spZ (c_regs cx))) by (rewrite (ER 8%nat 8%bv eq_refl); exact G8).
  assert (E10 : ew E 10 = w64 0) by (rewrite (ER 10%nat 10%bv eq_refl); exact R10).
  assert (E18 : ew E 18 = w64 (gc (c_pl cx) i)) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  assert (E23 : ew E 23 = w64 q) by (rewrite (ER 23%nat 23%bv eq_refl); exact R23).
  assert (E24 : ew E 24 = w64 (gv (c_pl cx) i)) by (rewrite (ER 24%nat 24%bv eq_refl); exact R24).
  assert (E25 : ew E 25 = w64 (if gacc (c_pl cx) i then 0 else -1)) by (rewrite (ER 25%nat 25%bv eq_refl); exact R25).
  assert (E26 : ew E 26 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i)))) by (rewrite (ER 26%nat 26%bv eq_refl); exact R26).
  pose proof (g_st0 W3 (ms_regs ms3) (ms_mem ms3) 0x4c4 E HE) as HS.
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  unfold ssg in HS.
  paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
  (* 0x80b74: bnez a0 into 0x81a0c *)
  psrr_branch_tok RUN BR HS SHOK GBspan; rewrite branch_ne_U, (U_atom E 10 0 E10), U_lit in Hc by lia.
  - cbn in Hc. discriminate Hc.
  - (* a0 = s7; the call of reac_headamp_default at 0x80b7c *)
    paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
    pmkst HS. rewrite pa_sigma_reac_headamp_default.
    let msC := curms HS in
    assert (HMC : gmem cx fp W3 msC t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i)
                    (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))))
      by (apply (gmem_tr cx fp W3 ms3); [memeq ms3 | exact HM]);
    pose proof HMC as ((Hra & Hsv) & _);
    assert (Hs0 : rdword (aview SEGS (w_H W3) (ms_mem msC)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)))
      by (pose proof (Hsv 0 ltac:(lia)) as H0; replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia;
          exact H0);
    assert (Q1 : getr (ms_regs msC) 1 = Z_to_bv 64 (BASE + 0x4d0)) by vgoal HS;
    assert (Q2 : getr (ms_regs msC) 2 = w64 (c_sp1 cx)) by vgoal HS;
    assert (Q3 : getr (ms_regs msC) 3 = getr (c_regs cx) 3) by vgoal HS;
    assert (Q4 : getr (ms_regs msC) 4 = getr (c_regs cx) 4) by vgoal HS;
    assert (Q8 : getr (ms_regs msC) 8 = w64 (spZ (c_regs cx))) by vgoal HS;
    assert (Q10 : getr (ms_regs msC) 10 = w64 q) by vgoal HS;
    eapply (gcall B MT LAWS REAC_HEADAMP_DEFAULT_STK []
      (fun ly' S' W' regs' mem' md' => getr regs' 10 = w64 (dflt q) /\ ly' = ly3 /\ S' = S3 /\ W' = W3 /\
         (forall x, mem' x = ms_mem msC x) /\ Permutation (ablocks B ly' S') (ablocks B ly3 S3))
      _ 0x4d0 POST cx fp k ly3 S3 W3 _ _ _ HB HJ Q2 Q8 Q3 Q4 Q1 ltac:(lia) eq_refl Hra Hs0
      ltac:(unfold REAC_HEADAMP_DEFAULT_STK, ESTACK; lia) ltac:(intros a Ha; destruct (inFP_nil a Ha))).
    + intros HPRE. exact (DFLH ly3 S3 W3 _ _ _ (gch cx) q HPRE Q10 ltac:(lia)).
    + intros W2 ly2 S2 regs2 mem2 md2 HJ2 HJc HP (H10' & -> & -> & -> & _ & _).
      apply (HTR cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0x4d0)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
      let msC := curms HS in
      assert (P2 : getr regs2 2 = getr (ms_regs msC) 2) by exact (HP 2 ltac:(unfold acallee_saved; lia));
      assert (P3 : getr regs2 3 = getr (ms_regs msC) 3) by exact (HP 3 ltac:(unfold acallee_saved; lia));
      assert (P4 : getr regs2 4 = getr (ms_regs msC) 4) by exact (HP 4 ltac:(unfold acallee_saved; lia));
      assert (P8 : getr regs2 8 = getr (ms_regs msC) 8) by exact (HP 8 ltac:(unfold acallee_saved; lia));
      assert (P9 : getr regs2 9 = getr (ms_regs msC) 9) by exact (HP 9 ltac:(unfold acallee_saved; lia));
      assert (P18 : getr regs2 18 = getr (ms_regs msC) 18) by exact (HP 18 ltac:(unfold acallee_saved; lia));
      assert (P19 : getr regs2 19 = getr (ms_regs msC) 19) by exact (HP 19 ltac:(unfold acallee_saved; lia));
      assert (P20 : getr regs2 20 = getr (ms_regs msC) 20) by exact (HP 20 ltac:(unfold acallee_saved; lia));
      assert (P22 : getr regs2 22 = getr (ms_regs msC) 22) by exact (HP 22 ltac:(unfold acallee_saved; lia));
      assert (P23 : getr regs2 23 = getr (ms_regs msC) 23) by exact (HP 23 ltac:(unfold acallee_saved; lia));
      assert (P24 : getr regs2 24 = getr (ms_regs msC) 24) by exact (HP 24 ltac:(unfold acallee_saved; lia));
      assert (P25 : getr regs2 25 = getr (ms_regs msC) 25) by exact (HP 25 ltac:(unfold acallee_saved; lia));
      assert (P26 : getr regs2 26 = getr (ms_regs msC) 26) by exact (HP 26 ltac:(unfold acallee_saved; lia));
      assert (P27 : getr regs2 27 = getr (ms_regs msC) 27) by exact (HP 27 ltac:(unfold acallee_saved; lia));
      exists t; split; [|split; [exact Hq3 | cbn [ms_regs mkst]; rewrite H10', dflt_ne2 by lia; reflexivity]];
      apply (g_landB 0x4d0 n i cx fp k acc ly3 S3 W3 ms3 _ t 0x4c4 HC); try reflexivity;
      first [ (apply (gmem_trK cx fp t ly3 W3 msC);
                [exact HL | exact LW | exact LS
                | intros a Ha; exact (gkeep_call0 B MT LAWS cx fp k ly3 S3 W3 _ _ REAC_HEADAMP_DEFAULT_STK mem2 md2 t
                    HB HJ HFR Hbl ltac:(unfold REAC_HEADAMP_DEFAULT_STK, ESTACK; lia) HJc a Ha)
                | exact HMC])
            | (cbn [ms_regs mkst]; rewrite ?P2, ?P3, ?P4, ?P8, ?P9, ?P18, ?P19, ?P20, ?P22, ?P23, ?P24, ?P25, ?P26, ?P27;
               first [kgoal HS ER | vgoal HS]) ].
Qed.

(* ---- 0x80b58 .. 0x80b70: the set's answer, the parameter test, and the call of
   reac_headamp_tx_effective for a parameter of 3 or more ---- *)
Lemma ga2_main : forall POST n i,
  ge_from B MT POST (GAB n i) -> ge_from B MT POST (GAR 0x4c4 n i) -> ge_from B MT POST (GA2 B MT n i).
Proof.
  intros POST n i HTB HTR cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO
    (t & HC & Hlen & HM & R10 & R18 & R23 & R24 & R26).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H22 & H27).
  pose proof HMA as (_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4).
  pose proof (gcell_ok (c_pl cx) i) as (Hc0 & Hq0 & Hv0).
  pose proof (gtables_inv (c_pl cx) i) as (LT & LW & LS & _ & _).
  pose proof (gtables_inv (c_pl cx) (S i)) as (LT1 & _ & _ & _ & _).
  pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  set (c := gc (c_pl cx) i) in *. set (q := gq (c_pl cx) i) in *.
  assert (HinT : In (t, TX_SIZE) (ablocks B ly3 S3))
    by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; right; left; reflexivity).
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  pose proof (g_ER _ _ HE) as ER.
  assert (E2 : ew E 2 = w64 (c_sp1 cx)) by (rewrite (ER 2%nat 2%bv eq_refl); exact G2).
  assert (E3 : ew E 3 = getr (c_regs cx) 3) by (rewrite (ER 3%nat 3%bv eq_refl); exact G3).
  assert (E4 : ew E 4 = getr (c_regs cx) 4) by (rewrite (ER 4%nat 4%bv eq_refl); exact G4).
  assert (E8 : ew E 8 = w64 (spZ (c_regs cx))) by (rewrite (ER 8%nat 8%bv eq_refl); exact G8).
  assert (E10 : ew E 10 = w64 (if gacc (c_pl cx) i then 0 else -1)) by (rewrite (ER 10%nat 10%bv eq_refl); exact R10).
  assert (E18 : ew E 18 = w64 c) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  assert (E20 : ew E 20 = w64 t) by (rewrite (ER 20%nat 20%bv eq_refl); exact H20).
  assert (E23 : ew E 23 = w64 q) by (rewrite (ER 23%nat 23%bv eq_refl); exact R23).
  assert (E24 : ew E 24 = w64 (gv (c_pl cx) i)) by (rewrite (ER 24%nat 24%bv eq_refl); exact R24).
  assert (E26 : ew E 26 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i)))) by (rewrite (ER 26%nat 26%bv eq_refl); exact R26).
  pose proof (g_st0 W3 (ms_regs ms3) (ms_mem ms3) 0x4a8 E HE) as HS.
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  unfold ssg in HS.
  paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
  (* 0x80b60: bltu s7, 3 *)
  psrr_branch_tok RUN BR HS SHOK GBspan; rewrite branch_ltu_U, (U_atom E 23 q E23), U_lit in Hc by lia.
  - (* a parameter below 3: on to 0x80b84 *)
    paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x4d4; [first [apply awr_ok_nil | gshow] |].
    let msF := curms HS in apply (HTB cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO).
    destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
    exists t. apply (g_landB 0x4d4 n i cx fp k acc ly3 S3 W3 ms3 _ t 0x4a8 HC Pc Prv Psv Pro Pfr Pfc).
    all: first [kgoal HS ER | vgoal HS | (apply (gmem_tr cx fp W3 ms3); [memeq ms3 | exact HM])].
  - (* a parameter of 3 or more: the call of reac_headamp_tx_effective at 0x80b70 *)
    apply Z.ltb_ge in Hc.
    paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
    pmkst HS. rewrite pa_sigma_reac_headamp_tx_effective.
    let msC := curms HS in
    assert (HMC : gmem cx fp W3 msC t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i)
                    (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))))
      by (apply (gmem_tr cx fp W3 ms3); [memeq ms3 | exact HM]);
    pose proof HMC as ((Hra & Hsv) & _ & _ & _ & _ & _ & _ & HT & _);
    assert (Hs0 : rdword (aview SEGS (w_H W3) (ms_mem msC)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)))
      by (pose proof (Hsv 0 ltac:(lia)) as H0; replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia;
          exact H0);
    assert (Q1 : getr (ms_regs msC) 1 = Z_to_bv 64 (BASE + 0x4c4)) by vgoal HS;
    assert (Q2 : getr (ms_regs msC) 2 = w64 (c_sp1 cx)) by vgoal HS;
    assert (Q3 : getr (ms_regs msC) 3 = getr (c_regs cx) 3) by vgoal HS;
    assert (Q4 : getr (ms_regs msC) 4 = getr (c_regs cx) 4) by vgoal HS;
    assert (Q8 : getr (ms_regs msC) 8 = w64 (spZ (c_regs cx))) by vgoal HS;
    assert (Q10 : getr (ms_regs msC) 10 = w64 t) by vgoal HS;
    assert (Q11 : getr (ms_regs msC) 11 = w64 c) by vgoal HS;
    assert (Q12 : getr (ms_regs msC) 12 = w64 q) by vgoal HS;
    eapply (gcall B MT LAWS TEFF_STK []
      (fun ly' S' W' regs' mem' md' => ly' = ly3 /\ S' = S3 /\ W' = W3 /\
         getr regs' 10 = w64 (eff (gTi (c_pl cx) (S i)) t c q) /\
         obj_at SEGS (mrestrict (w_H W3) mem') t LAY_TX (tx_vals (gTi (c_pl cx) (S i))))
      _ 0x4c4 POST cx fp k ly3 S3 W3 _ _ _ HB HJ Q2 Q8 Q3 Q4 Q1 ltac:(lia) eq_refl Hra Hs0
      ltac:(unfold TEFF_STK, ESTACK; lia) ltac:(intros a Ha; destruct (inFP_nil a Ha))).
    + intros HPRE. exact (EFFH ly3 S3 W3 _ _ _ (gch cx) t c q (gTi (c_pl cx) (S i))
        HPRE Q10 Q11 Q12 ltac:(lia) ltac:(lia) HinT LT1 (gtabb_obj W3 _ t _ HT)).
    + intros W2 ly2 S2 regs2 mem2 md2 HJ2 HJc HP (-> & -> & -> & H10' & _).
      apply (HTR cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0x4c4)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
      let msC := curms HS in
      assert (P2 : getr regs2 2 = getr (ms_regs msC) 2) by exact (HP 2 ltac:(unfold acallee_saved; lia));
      assert (P3 : getr regs2 3 = getr (ms_regs msC) 3) by exact (HP 3 ltac:(unfold acallee_saved; lia));
      assert (P4 : getr regs2 4 = getr (ms_regs msC) 4) by exact (HP 4 ltac:(unfold acallee_saved; lia));
      assert (P8 : getr regs2 8 = getr (ms_regs msC) 8) by exact (HP 8 ltac:(unfold acallee_saved; lia));
      assert (P9 : getr regs2 9 = getr (ms_regs msC) 9) by exact (HP 9 ltac:(unfold acallee_saved; lia));
      assert (P18 : getr regs2 18 = getr (ms_regs msC) 18) by exact (HP 18 ltac:(unfold acallee_saved; lia));
      assert (P19 : getr regs2 19 = getr (ms_regs msC) 19) by exact (HP 19 ltac:(unfold acallee_saved; lia));
      assert (P20 : getr regs2 20 = getr (ms_regs msC) 20) by exact (HP 20 ltac:(unfold acallee_saved; lia));
      assert (P22 : getr regs2 22 = getr (ms_regs msC) 22) by exact (HP 22 ltac:(unfold acallee_saved; lia));
      assert (P23 : getr regs2 23 = getr (ms_regs msC) 23) by exact (HP 23 ltac:(unfold acallee_saved; lia));
      assert (P24 : getr regs2 24 = getr (ms_regs msC) 24) by exact (HP 24 ltac:(unfold acallee_saved; lia));
      assert (P25 : getr regs2 25 = getr (ms_regs msC) 25) by exact (HP 25 ltac:(unfold acallee_saved; lia));
      assert (P26 : getr regs2 26 = getr (ms_regs msC) 26) by exact (HP 26 ltac:(unfold acallee_saved; lia));
      assert (P27 : getr regs2 27 = getr (ms_regs msC) 27) by exact (HP 27 ltac:(unfold acallee_saved; lia));
      exists t; split; [|split; [exact Hc | cbn [ms_regs mkst]; rewrite H10', eff_p3 by lia; reflexivity]];
      apply (g_landB 0x4c4 n i cx fp k acc ly3 S3 W3 ms3 _ t 0x4a8 HC); try reflexivity;
      first [ (apply (gmem_trK cx fp t ly3 W3 msC);
                [exact HL | exact LW | exact LS
                | intros a Ha; exact (gkeep_call0 B MT LAWS cx fp k ly3 S3 W3 _ _ TEFF_STK mem2 md2 t
                    HB HJ HFR Hbl ltac:(unfold TEFF_STK, ESTACK; lia) HJc a Ha)
                | exact HMC])
            | (cbn [ms_regs mkst]; rewrite ?P2, ?P3, ?P4, ?P8, ?P9, ?P18, ?P19, ?P20, ?P22, ?P23, ?P24, ?P25, ?P26, ?P27;
               first [kgoal HS ER | vgoal HS]) ].
Qed.

(* ---- the piece ---- *)
Lemma ge_set_ga2 : seg_ga2_stmt B MT.
Proof.
  intros POST n i HN HE2.
  pose proof (ga2_tail POST n i HN HE2) as HTB.
  exact (ga2_main POST n i HTB (ga2_r1 POST n i (ga2_r2 POST n i HTB))).
Qed.

End a.
