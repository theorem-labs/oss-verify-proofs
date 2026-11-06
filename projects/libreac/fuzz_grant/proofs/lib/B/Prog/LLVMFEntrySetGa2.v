(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetGa2), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySetGa2.v. *)
(* Image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantEntrySetGa2.v, ported from a working branch
   7c8c67da870 (blob 0fe84021d1d; the image-A file carries no licence lines, so none are copied).

   The set loop of LLVMFuzzerTestOneInput on image B: the piece GA2 → G78 | the call at 0x810b0
   (fuzz/fuzz_grant.c:208-226), for a cell whose two or three bytes the turn read (`seg_ga2_stmt`).

     0x80ffc .. 0x81004  s10 = the set's answer; a parameter below 3 goes to 0x81028 (GAB).
     0x81008 .. 0x81024  a parameter of 3 or more: reac_headamp_tx_effective (call at 0x81014, return
                         0x81018 = GAR 0x5dc) and reac_headamp_default (call at 0x81020, return 0x81024 =
                         GAR 0x5e8), each of whose answers must be 0 (`bnez a0` into the abort 0x81d98).
     0x81028 .. 0x810b0  GAB: the channel test `bgeu s2,48` (0x8102c); a2 := slot 104, the bytes left; for a
                         channel below 48 the parameter test `bne s8,2` (0x81038) and the harness's answer,
                         (s9 < 56) - 1 for the parameter 2 (0x8103c), (s8 < 3 && s9 < 2) - 1 else (0x81050);
                         for a channel of 48 or more the answer -1 (0x81070); the check `bne s10,a0` /
                         `beq s10,a0` into 0x81d98 (0x81064, 0x8107c); `bnez s10` at 0x8109c to 0x81140 for a
                         refused set, else the call of reac_headamp_tx_effective at 0x810b0.
   Image B reloads the bytes left from slot 104 at 0x81030 / 0x81078 (image A kept them in slot 120 and
   never reloaded them in this stretch), so GAB's symbolic state carries that slot as a read-only region. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC85 HeadampDefault.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntryDefs LLVMFEntrySetDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegSetModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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

(* a0 at 0x81064 for a parameter other than 2: ((s9 <u 2) & (s8 <u 3)) - 1. *)
Lemma U_chk3 : forall E q v, ew E 24 = w64 q -> ew E 25 = w64 v -> 0 <= q < 256 -> 0 <= v < 256 ->
  U E (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_SLTU (SOff 25 0) (SLit 2)) (SAlu ALU_SLTU (SOff 24 0) (SLit 3)))
         (SLit (-1)))
  = (if (v <? 2) && (q <? 3) then 0 else -1) mod 2 ^ 64.
Proof.
  intros E q v E24 E25 Hq Hv.
  rewrite !U_SAlu, (U_atom E 24 q E24), (U_atom E 25 v E25), !U_SLit by lia.
  change (zcanon 2) with 2. change (zcanon 3) with 3. cbn [zalu_raw].
  destruct (v <? 2), (q <? 3); vm_compute; reflexivity.
Qed.

(* a0 at 0x81064 for the parameter 2: (s9 <u 56) - 1. *)
Lemma U_chk56 : forall E v, ew E 25 = w64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 25 0) (SLit 56)) (SLit (-1))) = (if v <? 56 then 0 else -1) mod 2 ^ 64.
Proof.
  intros E v E25 Hv. rewrite !U_SAlu, (U_atom E 25 v E25), !U_SLit by lia.
  change (zcanon 56) with 56. cbn [zalu_raw].
  destruct (v <? 56); vm_compute; reflexivity.
Qed.

(* ---- walk tactics ---- *)
Ltac curms HS := lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?m) => m
  | st_ok _ _ _ (restrict _ ?m) => m
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

(* ---- the symbolic states of the cuts ---- *)
(* Every register its own atom, no memory. *)
Definition ssg (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
(* a0 pinned to 0: a callee answered 0. *)
Definition ssg0 (pc : Z) : sstate := mkSS pc (sr_set sr_atoms 10%bv (SLit 0)) [] None (mkFacts [] [] []).
(* At GAB: slot 104 (the bytes left after the cell, atom 32), read-only. *)
Definition R104 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 104 112 104 104 [YP09.mkChunk 104 (CVal 8 (SOff 32 0))].
Definition ss_gab : sstate := mkSS 0x5ec sr_atoms [R104] None (mkFacts [] [] []).

Section a.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis CALLE2 : call_e2_stmt B MT.
Hypothesis EFFH : tb_reac_headamp_tx_effective_spec B.
Hypothesis DFLH : treac_headamp_default_spec B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

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

Lemma g_st00 : forall (W3 : world SEGS) (regs : bvmap 5 word) mem pc E, E = Eimg (Ereg regs []) ->
  getr regs 10 = w64 0 ->
  st_ok_pi SEGS VAL E (ssg0 pc) (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros W3 regs mem pc E HE R10.
  apply (st_ok_pi_set_reg E (ssg pc) _ (10%bv : bv 5) (SLit 0) (g_st0 W3 regs mem pc E HE)); [discriminate|].
  cbn [ms_regs restrict mkst sv_denot]. exact R10.
Qed.

Lemma g_ER : forall (regs : bvmap 5 word) extra E, E = Eimg (Ereg regs extra) ->
  forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r.
Proof. intros regs extra E -> m r Hr. apply ew_Eimg_Ereg_nat. exact Hr. Qed.

(* A frame whose windows are all empty keeps every byte. *)
Lemma frame_ro_eq : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, ~ in_wrange E rs a) ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' HF HR a. apply aview_eq_of. apply HF. intros Hw. exact (HR _ Hw).
Qed.

Ltac ro_win :=
  let x := fresh "x" in let r := fresh "r" in let Hr := fresh "Hr" in let Hx := fresh "Hx" in
  intros x (r & Hr & Hx); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [Hr | Hr]; [ subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia | ]);
  try destruct Hr.

(* The memory after runs whose frames write nothing (no region, or read-only regions) is
   the memory before them. *)
Ltac memeq_body ms0 :=
  cbn [ms_mem mkst];
  repeat match goal with
  | |- aview _ _ (ms_mem ms0) _ = _ => reflexivity
  | |- ?x = ?x => reflexivity
  | HFr : frame_of ?Ex ?rs (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m1) |- aview _ _ ?m1 ?a = _ =>
      rewrite (frame_ro_eq Ex rs Hh m0 m1 HFr ltac:(ro_win) a)
  | H : frame_of _ _ (ms_mem ?m1) (ms_mem ?m2) |- aview _ _ (ms_mem ?m2) ?a = _ =>
      rewrite (frame_nil_eq _ _ _ _ _ eq_refl H a)
  end.
Ltac memeq ms0 := let a := fresh "a" in intros a; memeq_body ms0.
Ltac memeqR ms0 := memeq ms0.

(* The runs over read-only regions write nothing. *)
Ltac ro_awr :=
  lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fpl ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fpl b0 bc lyy own) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia |]);
  apply awr_ok_nil.

(* A spill slot carries over to a memory that keeps the machine stack at and above s1. *)
Lemma gslot_keep : forall cx (W3 : world SEGS) (ms ms' : machine_state) off v,
  (forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a) ->
  0 <= off -> c_sp1 cx + off + 8 <= 2 ^ 64 ->
  gslot cx W3 ms off v -> gslot cx W3 ms' off v.
Proof.
  intros cx W3 ms ms' off v HK H0 H1 H. unfold gslot in *.
  rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms)) (aview SEGS (w_H W3) (ms_mem ms')) (c_sp1 cx + off)); [exact H|].
  intros j Hj. apply HK. lia.
Qed.

(* ---- landing in a cut ---- *)
Lemma g_landB : forall pc1 n i cx fp k acc ly3 S3 W3 ms3 msF t pc0,
  gcore B MT cx fp k acc ly3 S3 ms3 pc0 n i t ->
  ms_pc_val msF = w64 (BASE + pc1) -> ms_resv msF = None -> ms_svc_pending msF = None ->
  ms_rom msF = seg_rom SEGS -> ms_fregs msF = fp_regs -> ms_fcsr msF = fp_csr ->
  getr (ms_regs msF) 2 = getr (ms_regs ms3) 2 -> getr (ms_regs msF) 3 = getr (ms_regs ms3) 3 ->
  getr (ms_regs msF) 4 = getr (ms_regs ms3) 4 -> getr (ms_regs msF) 8 = getr (ms_regs ms3) 8 ->
  getr (ms_regs msF) 9 = getr (ms_regs ms3) 9 -> getr (ms_regs msF) 19 = getr (ms_regs ms3) 19 ->
  getr (ms_regs msF) 20 = getr (ms_regs ms3) 20 -> getr (ms_regs msF) 21 = getr (ms_regs ms3) 21 ->
  gmem cx fp W3 msF t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) ->
  gslot cx W3 msF 104 (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))) ->
  getr (ms_regs msF) 26 = w64 (if gacc (c_pl cx) i then 0 else -1) ->
  getr (ms_regs msF) 18 = w64 (gc (c_pl cx) i) -> getr (ms_regs msF) 24 = w64 (gq (c_pl cx) i) ->
  getr (ms_regs msF) 25 = w64 (gv (c_pl cx) i) ->
  getr (ms_regs msF) 27 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))) ->
  gb_at B MT pc1 n i cx fp k acc ly3 S3 W3 msF t.
Proof.
  intros pc1 n i cx fp k acc ly3 S3 W3 ms3 msF t pc0
    ((_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4) & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H21)
    Pc Prv Psv Pro Pfr Pfc K2 K3 K4 K8 K9 K19 K20 K21 HM H104 R26 R18 R24 R25 R27.
  unfold gb_at, gcore, gmach, gregs. splits; try assumption; congruence.
Qed.

(* A refused set lands in G78: the arrays are those of turn i, which are those of turn
   i + 1 (gtables_S). *)
Lemma g_land78 : forall n i cx fp k acc ly3 S3 W3 ms3 msF md t pc0,
  gcore B MT cx fp k acc ly3 S3 ms3 pc0 n i t ->
  gmem cx fp W3 ms3 t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) ->
  gacc (c_pl cx) i = false ->
  ms_pc_val msF = w64 (BASE + 0x704) -> ms_resv msF = None -> ms_svc_pending msF = None ->
  ms_rom msF = seg_rom SEGS -> ms_fregs msF = fp_regs -> ms_fcsr msF = fp_csr ->
  getr (ms_regs msF) 2 = getr (ms_regs ms3) 2 -> getr (ms_regs msF) 3 = getr (ms_regs ms3) 3 ->
  getr (ms_regs msF) 4 = getr (ms_regs ms3) 4 -> getr (ms_regs msF) 8 = getr (ms_regs ms3) 8 ->
  getr (ms_regs msF) 9 = getr (ms_regs ms3) 9 -> getr (ms_regs msF) 19 = getr (ms_regs ms3) 19 ->
  getr (ms_regs msF) 20 = getr (ms_regs ms3) 20 -> getr (ms_regs msF) 21 = getr (ms_regs ms3) 21 ->
  getr (ms_regs msF) 23 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))) ->
  getr (ms_regs msF) 12 = w64 (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))) ->
  (forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  G78 B MT n i cx fp k acc ly3 S3 W3 msF md.
Proof.
  intros n i cx fp k acc ly3 S3 W3 ms3 msF md t pc0
    ((_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4) & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H21)
    HM Hgq Pc Prv Psv Pro Pfr Pfc K2 K3 K4 K8 K9 K19 K20 K21 K23 K12 HMEQ.
  destruct (gtables_S (c_pl cx) i) as (_ & EW & ES). rewrite Hgq in EW, ES.
  exists t. split; [|split; [|split]].
  - unfold gcore, gmach, gregs. splits; try assumption; congruence.
  - rewrite EW, ES. exact (gmem_tr cx fp W3 ms3 msF t _ _ _ HMEQ HM).
  - exact K23.
  - exact K12.
Qed.

(* ---- 0x81028 .. 0x810b0: the harness's answer, the check, and the exit ---- *)
Lemma ga2_tail : forall POST n i,
  ge_from B MT POST (G78 B MT n i) -> ge_from B MT POST (GE2 B MT n i) -> ge_from B MT POST (GAB B MT n i).
Proof.
  intros POST n i HN HE2 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO (t & HC & HM & H104 & R26 & R18 & R24 & R25 & R27).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H21).
  pose proof HMA as (_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4).
  pose proof (gcell_ok (c_pl cx) i) as (Hc0 & Hq0 & Hv0).
  pose proof (gpos_le (c_pl cx) (S i)) as Hpl.
  pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & _).
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  assert (Ecn : c_n cx = Z.of_nat (length (c_pl cx))) by reflexivity.
  set (c := gc (c_pl cx) i) in *. set (q := gq (c_pl cx) i) in *. set (v := gv (c_pl cx) i) in *.
  set (bl := c_n cx - Z.of_nat (gpos (c_pl cx) (S i))) in *.
  assert (Hbl0 : 0 <= bl < 2 ^ 26) by (unfold bl; lia).
  assert (HGA : gacc (c_pl cx) i = (c <? 48) && legalb q v) by reflexivity.
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 bl])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  pose proof (g_ER _ _ _ HE) as ER.
  assert (E2 : ew E 2 = w64 (c_sp1 cx)) by (rewrite (ER 2%nat 2%bv eq_refl); exact G2).
  assert (E3 : ew E 3 = getr (c_regs cx) 3) by (rewrite (ER 3%nat 3%bv eq_refl); exact G3).
  assert (E4 : ew E 4 = getr (c_regs cx) 4) by (rewrite (ER 4%nat 4%bv eq_refl); exact G4).
  assert (E8 : ew E 8 = w64 (spZ (c_regs cx))) by (rewrite (ER 8%nat 8%bv eq_refl); exact G8).
  assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact G9).
  assert (E18 : ew E 18 = w64 c) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  assert (E19 : ew E 19 = w64 (gSH cx fp)) by (rewrite (ER 19%nat 19%bv eq_refl); exact H19).
  assert (E20 : ew E 20 = w64 t) by (rewrite (ER 20%nat 20%bv eq_refl); exact H20).
  assert (E21 : ew E 21 = w64 (Z.of_nat (S n))) by (rewrite (ER 21%nat 21%bv eq_refl); exact H21).
  assert (E24 : ew E 24 = w64 q) by (rewrite (ER 24%nat 24%bv eq_refl); exact R24).
  assert (E25 : ew E 25 = w64 v) by (rewrite (ER 25%nat 25%bv eq_refl); exact R25).
  assert (E26 : ew E 26 = w64 (if gacc (c_pl cx) i then 0 else -1)) by (rewrite (ER 26%nat 26%bv eq_refl); exact R26).
  assert (E27 : ew E 27 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i)))) by (rewrite (ER 27%nat 27%bv eq_refl); exact R27).
  assert (EX : forall j, (j < 1)%nat -> ew E (32 + j) = nth j [Z_to_bv 64 bl] (Z_to_bv 64 0))
    by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  assert (E32 : ew E 32 = w64 bl) by exact (EX 0%nat ltac:(lia)).
  assert (HS : st_ok_pi SEGS VAL E ss_gab (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + 0x5ec)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_gab. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold region_ok, R104. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      pose proof (proj1 alloc_ceiling_val) as AC.
      rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. unfold gslot in H104.
      apply (chunk_ok_val SEGS E _ (c_sp1 cx) 104 8 (SOff 32 0) bl); [apply gsv0; [exact E32 | lia] | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ H104).
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  paj_run_tok RUN HS HJ SHOK GBspan; [ro_awr |].
  (* 0x8102c: bgeu s2, 48 *)
  psrr_branch_tok RUN BR HS SHOK GBspan; rewrite branch_geu_U, (U_atom E 18 c E18), U_lit in Hc by lia.
  - (* the channel is 48 or more: the set refused it, and so does the harness (a0 = -1) *)
    apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hc48.
    assert (HGF : gacc (c_pl cx) i = false) by (rewrite HGA, (proj2 (Z.ltb_ge c 48) Hc48); reflexivity).
    rewrite HGF in E26.
    paj_run_tok RUN HS HJ SHOK GBspan; [ro_awr |].
    (* 0x8107c: beq s10, a0 (= -1), else into 0x81d98 *)
    psrr_branch_tok RUN BR HS SHOK GBspan;
      rewrite branch_eq_U, (U_w64 E 26 _ E26), U_lit in Hc by lia; vm_compute in Hc.
    + clear Hc. paj_run_tok RUN HS HJ SHOK GBspan; [ro_awr |].
      (* 0x8109c: bnez s10 *)
      psrr_branch_tok RUN BR HS SHOK GBspan;
        rewrite branch_ne_U, (U_w64 E 26 _ E26), U_lit in Hc by lia; vm_compute in Hc.
      * clear Hc. paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x704; [ro_awr |].
        let msF := curms HS in apply (HN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO).
        destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
        apply (g_land78 n i cx fp k acc ly3 S3 W3 ms3 _ _ t 0x5ec HC HM HGF Pc Prv Psv Pro Pfr Pfc).
        all: first [kgoal HS ER | vgoal HS | memeqR ms3].
      * discriminate Hc.
    + discriminate Hc.
  - (* the channel is below 48 *)
    apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hc48.
    paj_run_tok RUN HS HJ SHOK GBspan; [ro_awr |].
    (* 0x81038: bne s8, 2 *)
    psrr_branch_tok RUN BR HS SHOK GBspan; rewrite branch_ne_U, (U_atom E 24 q E24), U_lit in Hc by lia.
    + (* a parameter other than 2 *)
      apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hqn2.
      assert (Hgq : gacc (c_pl cx) i = (v <? 2) && (q <? 3))
        by (rewrite HGA, (proj2 (Z.ltb_lt c 48) Hc48), legalb_ne2 by lia; reflexivity).
      rewrite Hgq in E26.
      paj_run_tok RUN HS HJ SHOK GBspan; [ro_awr |].
      (* 0x81064: bne s10, a0 into 0x81d98 *)
      psrr_branch_tok RUN BR HS SHOK GBspan;
        rewrite branch_ne_U, (U_w64 E 26 _ E26), (U_chk3 E q v E24 E25) in Hc by lia.
      * rewrite Z.eqb_refl in Hc. cbn in Hc. discriminate Hc.
      * clear Hc. paj_run_tok RUN HS HJ SHOK GBspan; [ro_awr |].
        (* 0x8109c: bnez s10 *)
        psrr_branch_tok RUN BR HS SHOK GBspan;
          rewrite branch_ne_U, (U_w64 E 26 _ E26), U_lit in Hc by lia;
          revert Hc; destruct ((v <? 2) && (q <? 3)) eqn:HB2; intros Hc; vm_compute in Hc.
        -- discriminate Hc.
        -- assert (HGF : gacc (c_pl cx) i = false) by (rewrite Hgq; first [reflexivity | exact HB2]). clear Hc.
           paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x704; [ro_awr |].
           let msF := curms HS in apply (HN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO).
           destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
           apply (g_land78 n i cx fp k acc ly3 S3 W3 ms3 _ _ t 0x5ec HC HM HGF Pc Prv Psv Pro Pfr Pfc).
           all: first [kgoal HS ER | vgoal HS | memeqR ms3].
        -- assert (HGT : gacc (c_pl cx) i = true) by (rewrite Hgq; first [reflexivity | exact HB2]). clear Hc.
           paj_run_tok RUN HS HJ SHOK GBspan; [ro_awr |].
           pmkst HS. rewrite pa_sigma_reac_headamp_tx_effective.
           apply (CALLE2 POST n i cx fp k acc ly3 S3 W3 _ _ _ t HE2 HB HJ HFR HMO Hk Hacc Hbl Ht0 Hn Hns HGT).
           all: first [vgoal HS | (apply (gmem_tr cx fp W3 ms3); [memeqR ms3 | exact HM])].
        -- discriminate Hc.
    + (* the parameter 2 *)
      apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hq2.
      assert (Hgq : gacc (c_pl cx) i = (v <? 56))
        by (rewrite HGA, (proj2 (Z.ltb_lt c 48) Hc48), Hq2, legalb_2; reflexivity).
      rewrite Hgq in E26.
      paj_run_tok RUN HS HJ SHOK GBspan; [ro_awr |].
      (* 0x81064: bne s10, a0 into 0x81d98 *)
      psrr_branch_tok RUN BR HS SHOK GBspan;
        rewrite branch_ne_U, (U_w64 E 26 _ E26), (U_chk56 E v E25) in Hc by lia.
      * rewrite Z.eqb_refl in Hc. cbn in Hc. discriminate Hc.
      * clear Hc. paj_run_tok RUN HS HJ SHOK GBspan; [ro_awr |].
        (* 0x8109c: bnez s10 *)
        psrr_branch_tok RUN BR HS SHOK GBspan;
          rewrite branch_ne_U, (U_w64 E 26 _ E26), U_lit in Hc by lia;
          revert Hc; destruct (v <? 56) eqn:HB2; intros Hc; vm_compute in Hc.
        -- discriminate Hc.
        -- assert (HGF : gacc (c_pl cx) i = false) by (rewrite Hgq; first [reflexivity | exact HB2]). clear Hc.
           paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x704; [ro_awr |].
           let msF := curms HS in apply (HN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO).
           destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
           apply (g_land78 n i cx fp k acc ly3 S3 W3 ms3 _ _ t 0x5ec HC HM HGF Pc Prv Psv Pro Pfr Pfc).
           all: first [kgoal HS ER | vgoal HS | memeqR ms3].
        -- assert (HGT : gacc (c_pl cx) i = true) by (rewrite Hgq; first [reflexivity | exact HB2]). clear Hc.
           paj_run_tok RUN HS HJ SHOK GBspan; [ro_awr |].
           pmkst HS. rewrite pa_sigma_reac_headamp_tx_effective.
           apply (CALLE2 POST n i cx fp k acc ly3 S3 W3 _ _ _ t HE2 HB HJ HFR HMO Hk Hacc Hbl Ht0 Hn Hns HGT).
           all: first [vgoal HS | (apply (gmem_tr cx fp W3 ms3); [memeqR ms3 | exact HM])].
        -- discriminate Hc.
Qed.

(* ---- 0x81024: reac_headamp_default answered 0 ---- *)
Lemma ga2_r2 : forall POST n i, ge_from B MT POST (GAB B MT n i) -> ge_from B MT POST (GAR B MT 0x5e8 n i).
Proof.
  intros POST n i HTB cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO
    (t & (HC & HM & H104 & R26 & R18 & R24 & R25 & R27) & Hq3 & R10).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H21).
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
  pose proof HL as (_ & _ & L3 & L4 & _).
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  pose proof (g_ER _ _ _ HE) as ER.
  pose proof (g_st00 W3 (ms_regs ms3) (ms_mem ms3) 0x5e8 E HE R10) as HS.
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  (* 0x81024: bnez a0 into 0x81d98, decided: a0 = 0 *)
  paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x5ec; [apply awr_ok_nil |].
  let msF := curms HS in apply (HTB cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO).
  destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
  exists t. apply (g_landB 0x5ec n i cx fp k acc ly3 S3 W3 ms3 _ t 0x5e8 HC Pc Prv Psv Pro Pfr Pfc).
  all: first [ kgoal HS ER
             | (apply (gmem_tr cx fp W3 ms3); [memeq ms3 | exact HM])
             | (apply (gslot_keep cx W3 ms3); [intros a _; memeq_body ms3 | lia | lia | exact H104])
             | (prreg HS (26%bv : bv 5) X26; rewrite X26, (ER 26%nat 26%bv eq_refl); exact R26)
             | (prreg HS (18%bv : bv 5) X18; rewrite X18, (ER 18%nat 18%bv eq_refl); exact R18)
             | (prreg HS (24%bv : bv 5) X24; rewrite X24, (ER 24%nat 24%bv eq_refl); exact R24)
             | (prreg HS (25%bv : bv 5) X25; rewrite X25, (ER 25%nat 25%bv eq_refl); exact R25)
             | (prreg HS (27%bv : bv 5) X27; rewrite X27, (ER 27%nat 27%bv eq_refl); exact R27) ].
Qed.

(* ---- 0x81018: reac_headamp_tx_effective answered 0; the call of reac_headamp_default ---- *)
Lemma ga2_r1 : forall POST n i, ge_from B MT POST (GAR B MT 0x5e8 n i) -> ge_from B MT POST (GAR B MT 0x5dc n i).
Proof.
  intros POST n i HTR cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO
    (t & (HC & HM & H104 & R26 & R18 & R24 & R25 & R27) & Hq3 & R10).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H21).
  pose proof HMA as (_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4).
  pose proof (gcell_ok (c_pl cx) i) as (Hc0 & Hq0 & Hv0).
  pose proof (gtables_inv (c_pl cx) i) as (LT & LW & LS & _ & _).
  pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & _).
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  set (q := gq (c_pl cx) i) in *.
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  pose proof (g_ER _ _ _ HE) as ER.
  assert (E2 : ew E 2 = w64 (c_sp1 cx)) by (rewrite (ER 2%nat 2%bv eq_refl); exact G2).
  assert (E3 : ew E 3 = getr (c_regs cx) 3) by (rewrite (ER 3%nat 3%bv eq_refl); exact G3).
  assert (E4 : ew E 4 = getr (c_regs cx) 4) by (rewrite (ER 4%nat 4%bv eq_refl); exact G4).
  assert (E8 : ew E 8 = w64 (spZ (c_regs cx))) by (rewrite (ER 8%nat 8%bv eq_refl); exact G8).
  assert (E24 : ew E 24 = w64 q) by (rewrite (ER 24%nat 24%bv eq_refl); exact R24).
  assert (E18 : ew E 18 = w64 (gc (c_pl cx) i)) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  assert (E25 : ew E 25 = w64 (gv (c_pl cx) i)) by (rewrite (ER 25%nat 25%bv eq_refl); exact R25).
  assert (E26 : ew E 26 = w64 (if gacc (c_pl cx) i then 0 else -1)) by (rewrite (ER 26%nat 26%bv eq_refl); exact R26).
  assert (E27 : ew E 27 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i)))) by (rewrite (ER 27%nat 27%bv eq_refl); exact R27).
  pose proof (g_st00 W3 (ms_regs ms3) (ms_mem ms3) 0x5dc E HE R10) as HS.
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  (* 0x81018: bnez a0 into 0x81d98, decided: a0 = 0; a0 := s8, the call of
     reac_headamp_default at 0x81020 *)
  paj_run_tok RUN HS HJ SHOK GBspan; [apply awr_ok_nil |].
  pmkst HS. rewrite pa_sigma_reac_headamp_default.
  let msC := curms HS in
  assert (HMC : gmem cx fp W3 msC t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i))
    by (apply (gmem_tr cx fp W3 ms3); [memeq ms3 | exact HM]);
  pose proof HMC as ((Hra & Hsv) & _);
  assert (H104C : gslot cx W3 msC 104 (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))))
    by (apply (gslot_keep cx W3 ms3); [intros a _; memeq_body ms3 | lia | lia | exact H104]);
  assert (Hs0 : rdword (aview SEGS (w_H W3) (ms_mem msC)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)))
    by (pose proof (Hsv 0 ltac:(lia)) as H0; replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia;
        exact H0);
  assert (Q1 : getr (ms_regs msC) 1 = Z_to_bv 64 (BASE + 0x5e8)) by vgoal HS;
  assert (Q2 : getr (ms_regs msC) 2 = w64 (c_sp1 cx)) by vgoal HS;
  assert (Q3 : getr (ms_regs msC) 3 = getr (c_regs cx) 3) by vgoal HS;
  assert (Q4 : getr (ms_regs msC) 4 = getr (c_regs cx) 4) by vgoal HS;
  assert (Q8 : getr (ms_regs msC) 8 = w64 (spZ (c_regs cx))) by vgoal HS;
  assert (Q10 : getr (ms_regs msC) 10 = w64 q) by vgoal HS;
  eapply (gcall B MT LAWS REAC_HEADAMP_DEFAULT_STK []
    (fun ly' S' W' regs' mem' md' => getr regs' 10 = w64 (dflt q) /\ ly' = ly3 /\ S' = S3 /\ W' = W3 /\
       (forall x, mem' x = ms_mem msC x) /\ Permutation (ablocks B ly' S') (ablocks B ly3 S3))
    _ 0x5e8 POST cx fp k ly3 S3 W3 _ _ _ HB HJ Q2 Q8 Q3 Q4 Q1 ltac:(lia) eq_refl Hra Hs0
    ltac:(unfold REAC_HEADAMP_DEFAULT_STK, ESTACK; lia) ltac:(intros a Ha; destruct (inFP_nil a Ha))).
  - intros HPRE. exact (DFLH ly3 S3 W3 _ _ _ (gch cx) q HPRE Q10 ltac:(lia)).
  - intros W2 ly2 S2 regs2 mem2 md2 HJ2 HJc HP (H10' & -> & -> & -> & HMEQ & _).
    apply (HTR cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0x5e8)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
    let msC := curms HS in
    assert (P2 : getr regs2 2 = getr (ms_regs msC) 2) by exact (HP 2 ltac:(unfold acallee_saved; lia));
    assert (P3 : getr regs2 3 = getr (ms_regs msC) 3) by exact (HP 3 ltac:(unfold acallee_saved; lia));
    assert (P4 : getr regs2 4 = getr (ms_regs msC) 4) by exact (HP 4 ltac:(unfold acallee_saved; lia));
    assert (P8 : getr regs2 8 = getr (ms_regs msC) 8) by exact (HP 8 ltac:(unfold acallee_saved; lia));
    assert (P9 : getr regs2 9 = getr (ms_regs msC) 9) by exact (HP 9 ltac:(unfold acallee_saved; lia));
    assert (P18 : getr regs2 18 = getr (ms_regs msC) 18) by exact (HP 18 ltac:(unfold acallee_saved; lia));
    assert (P19 : getr regs2 19 = getr (ms_regs msC) 19) by exact (HP 19 ltac:(unfold acallee_saved; lia));
    assert (P20 : getr regs2 20 = getr (ms_regs msC) 20) by exact (HP 20 ltac:(unfold acallee_saved; lia));
    assert (P21 : getr regs2 21 = getr (ms_regs msC) 21) by exact (HP 21 ltac:(unfold acallee_saved; lia));
    assert (P24 : getr regs2 24 = getr (ms_regs msC) 24) by exact (HP 24 ltac:(unfold acallee_saved; lia));
    assert (P25 : getr regs2 25 = getr (ms_regs msC) 25) by exact (HP 25 ltac:(unfold acallee_saved; lia));
    assert (P26 : getr regs2 26 = getr (ms_regs msC) 26) by exact (HP 26 ltac:(unfold acallee_saved; lia));
    assert (P27 : getr regs2 27 = getr (ms_regs msC) 27) by exact (HP 27 ltac:(unfold acallee_saved; lia));
    assert (HMEQ' : forall a, aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem msC) a)
      by (intros a; unfold aview, mbyte, mrestrict; rewrite HMEQ; reflexivity);
    exists t; split; [|split; [exact Hq3 | cbn [ms_regs mkst]; rewrite H10', dflt_ne2 by lia; reflexivity]];
    apply (g_landB 0x5e8 n i cx fp k acc ly3 S3 W3 ms3 _ t 0x5dc HC); try reflexivity;
    first [ exact (gmem_tr cx fp W3 msC (mkst regs2 (Z_to_bv 64 (BASE + 0x5e8)) mem2 (seg_rom SEGS)) t _ _ _ HMEQ' HMC)
          | exact (gslot_keep cx W3 msC (mkst regs2 (Z_to_bv 64 (BASE + 0x5e8)) mem2 (seg_rom SEGS)) 104 _
                     (fun a _ => HMEQ' a) ltac:(lia) ltac:(lia) H104C)
          | (cbn [ms_regs mkst]; rewrite ?P2, ?P3, ?P4, ?P8, ?P9, ?P18, ?P19, ?P20, ?P21, ?P24, ?P25, ?P26, ?P27;
             first [kgoal HS ER | vgoal HS]) ].
Qed.

(* ---- 0x80ffc .. 0x81014: the set's answer, the parameter test, and the call of
   reac_headamp_tx_effective for a parameter of 3 or more ---- *)
Lemma ga2_main : forall POST n i,
  ge_from B MT POST (GAB B MT n i) -> ge_from B MT POST (GAR B MT 0x5dc n i) -> ge_from B MT POST (GA2 B MT n i).
Proof.
  intros POST n i HTB HTR cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO
    (t & HC & Hlen & HM & H104 & R10 & R18 & R24 & R25 & R27).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H21).
  pose proof HMA as (_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4).
  pose proof (gcell_ok (c_pl cx) i) as (Hc0 & Hq0 & Hv0).
  pose proof (gtables_inv (c_pl cx) i) as (LT & LW & LS & _ & _).
  pose proof (gtables_inv (c_pl cx) (S i)) as (LT1 & _ & _ & _ & _).
  pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & _).
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  set (c := gc (c_pl cx) i) in *. set (q := gq (c_pl cx) i) in *.
  assert (HinT : In (t, ALay.TX_SIZE) (ablocks B ly3 S3))
    by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; right; left; reflexivity).
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  pose proof (g_ER _ _ _ HE) as ER.
  assert (E2 : ew E 2 = w64 (c_sp1 cx)) by (rewrite (ER 2%nat 2%bv eq_refl); exact G2).
  assert (E3 : ew E 3 = getr (c_regs cx) 3) by (rewrite (ER 3%nat 3%bv eq_refl); exact G3).
  assert (E4 : ew E 4 = getr (c_regs cx) 4) by (rewrite (ER 4%nat 4%bv eq_refl); exact G4).
  assert (E8 : ew E 8 = w64 (spZ (c_regs cx))) by (rewrite (ER 8%nat 8%bv eq_refl); exact G8).
  assert (E10 : ew E 10 = w64 (if gacc (c_pl cx) i then 0 else -1)) by (rewrite (ER 10%nat 10%bv eq_refl); exact R10).
  assert (E18 : ew E 18 = w64 c) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  assert (E20 : ew E 20 = w64 t) by (rewrite (ER 20%nat 20%bv eq_refl); exact H20).
  assert (E24 : ew E 24 = w64 q) by (rewrite (ER 24%nat 24%bv eq_refl); exact R24).
  assert (E25 : ew E 25 = w64 (gv (c_pl cx) i)) by (rewrite (ER 25%nat 25%bv eq_refl); exact R25).
  assert (E27 : ew E 27 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i)))) by (rewrite (ER 27%nat 27%bv eq_refl); exact R27).
  pose proof (g_st0 W3 (ms_regs ms3) (ms_mem ms3) 0x5c0 E HE) as HS.
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  unfold ssg in HS.
  paj_run_tok RUN HS HJ SHOK GBspan; [apply awr_ok_nil |].
  (* 0x81004: bltu s8, 3 *)
  psrr_branch_tok RUN BR HS SHOK GBspan; rewrite branch_ltu_U, (U_atom E 24 q E24), U_lit in Hc by lia.
  - (* a parameter below 3: on to 0x81028 *)
    paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x5ec; [apply awr_ok_nil |].
    let msF := curms HS in apply (HTB cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO).
    destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
    exists t. apply (g_landB 0x5ec n i cx fp k acc ly3 S3 W3 ms3 _ t 0x5c0 HC Pc Prv Psv Pro Pfr Pfc).
    all: first [ kgoal HS ER | vgoal HS
               | (apply (gmem_tr cx fp W3 ms3); [memeq ms3 | exact HM])
               | (apply (gslot_keep cx W3 ms3); [intros a _; memeq_body ms3 | lia | lia | exact H104]) ].
  - (* a parameter of 3 or more: the call of reac_headamp_tx_effective at 0x81014 *)
    apply Z.ltb_ge in Hc.
    paj_run_tok RUN HS HJ SHOK GBspan; [apply awr_ok_nil |].
    pmkst HS. rewrite pa_sigma_reac_headamp_tx_effective.
    let msC := curms HS in
    assert (HMC : gmem cx fp W3 msC t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i))
      by (apply (gmem_tr cx fp W3 ms3); [memeq ms3 | exact HM]);
    pose proof HMC as ((Hra & Hsv) & _ & _ & _ & _ & HT & _);
    assert (H104C : gslot cx W3 msC 104 (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))))
      by (apply (gslot_keep cx W3 ms3); [intros a _; memeq_body ms3 | lia | lia | exact H104]);
    assert (Hs0 : rdword (aview SEGS (w_H W3) (ms_mem msC)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)))
      by (pose proof (Hsv 0 ltac:(lia)) as H0; replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia;
          exact H0);
    assert (Q1 : getr (ms_regs msC) 1 = Z_to_bv 64 (BASE + 0x5dc)) by vgoal HS;
    assert (Q2 : getr (ms_regs msC) 2 = w64 (c_sp1 cx)) by vgoal HS;
    assert (Q3 : getr (ms_regs msC) 3 = getr (c_regs cx) 3) by vgoal HS;
    assert (Q4 : getr (ms_regs msC) 4 = getr (c_regs cx) 4) by vgoal HS;
    assert (Q8 : getr (ms_regs msC) 8 = w64 (spZ (c_regs cx))) by vgoal HS;
    assert (Q10 : getr (ms_regs msC) 10 = w64 t) by vgoal HS;
    assert (Q11 : getr (ms_regs msC) 11 = w64 c) by vgoal HS;
    assert (Q12 : getr (ms_regs msC) 12 = w64 q) by vgoal HS;
    eapply (gcall B MT LAWS STK_reac_headamp_tx_effective []
      (fun ly' S' W' regs' mem' md' => ly' = ly3 /\ S' = S3 /\ W' = W3 /\
         getr regs' 10 = w64 (eff (gTi (c_pl cx) (S i)) t c q) /\
         (t <> 0 -> obj_at SEGS (mrestrict (w_H W3) mem') t ALay.LAY_TX (ALay.tx_vals (gTi (c_pl cx) (S i)))))
      _ 0x5dc POST cx fp k ly3 S3 W3 _ _ _ HB HJ Q2 Q8 Q3 Q4 Q1 ltac:(lia) eq_refl Hra Hs0
      ltac:(unfold STK_reac_headamp_tx_effective, ESTACK; lia) ltac:(intros a Ha; destruct (inFP_nil a Ha))).
    + intros HPRE. exact (EFFH ly3 S3 W3 _ _ _ (gch cx) t c q (gTi (c_pl cx) (S i))
        HPRE Q10 Q11 Q12 ltac:(lia) ltac:(lia) LT1 (or_intror (conj HinT (gtabb_obj W3 _ t _ HT)))).
    + intros W2 ly2 S2 regs2 mem2 md2 HJ2 HJc HP (-> & -> & -> & H10' & _).
      apply (HTR cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0x5dc)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
      let msC := curms HS in
      assert (P2 : getr regs2 2 = getr (ms_regs msC) 2) by exact (HP 2 ltac:(unfold acallee_saved; lia));
      assert (P3 : getr regs2 3 = getr (ms_regs msC) 3) by exact (HP 3 ltac:(unfold acallee_saved; lia));
      assert (P4 : getr regs2 4 = getr (ms_regs msC) 4) by exact (HP 4 ltac:(unfold acallee_saved; lia));
      assert (P8 : getr regs2 8 = getr (ms_regs msC) 8) by exact (HP 8 ltac:(unfold acallee_saved; lia));
      assert (P9 : getr regs2 9 = getr (ms_regs msC) 9) by exact (HP 9 ltac:(unfold acallee_saved; lia));
      assert (P18 : getr regs2 18 = getr (ms_regs msC) 18) by exact (HP 18 ltac:(unfold acallee_saved; lia));
      assert (P19 : getr regs2 19 = getr (ms_regs msC) 19) by exact (HP 19 ltac:(unfold acallee_saved; lia));
      assert (P20 : getr regs2 20 = getr (ms_regs msC) 20) by exact (HP 20 ltac:(unfold acallee_saved; lia));
      assert (P21 : getr regs2 21 = getr (ms_regs msC) 21) by exact (HP 21 ltac:(unfold acallee_saved; lia));
      assert (P24 : getr regs2 24 = getr (ms_regs msC) 24) by exact (HP 24 ltac:(unfold acallee_saved; lia));
      assert (P25 : getr regs2 25 = getr (ms_regs msC) 25) by exact (HP 25 ltac:(unfold acallee_saved; lia));
      assert (P26 : getr regs2 26 = getr (ms_regs msC) 26) by exact (HP 26 ltac:(unfold acallee_saved; lia));
      assert (P27 : getr regs2 27 = getr (ms_regs msC) 27) by exact (HP 27 ltac:(unfold acallee_saved; lia));
      assert (KC : forall a, gkeep_at cx fp t a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem msC) a)
        by (intros a Ha; exact (gkeep_call0 B MT LAWS cx fp k ly3 S3 W3 _ _ STK_reac_headamp_tx_effective mem2 md2 t
              HB HJ HFR Hbl ltac:(unfold STK_reac_headamp_tx_effective, ESTACK; lia) HJc a Ha));
      exists t; split; [|split; [exact Hc | cbn [ms_regs mkst]; rewrite H10', eff_p3 by lia; reflexivity]];
      apply (g_landB 0x5dc n i cx fp k acc ly3 S3 W3 ms3 _ t 0x5c0 HC); try reflexivity;
      first [ (apply (gmem_trK cx fp t ly3 W3 msC); [exact HL | exact LW | exact LS | exact KC | exact HMC])
            | exact (gslot_keep cx W3 msC (mkst regs2 (Z_to_bv 64 (BASE + 0x5dc)) mem2 (seg_rom SEGS)) 104 _
                       (fun a Ha => KC a (or_introl Ha)) ltac:(lia) ltac:(lia) H104C)
            | (cbn [ms_regs mkst]; rewrite ?P2, ?P3, ?P4, ?P8, ?P9, ?P18, ?P19, ?P20, ?P21, ?P24, ?P25, ?P26, ?P27;
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
