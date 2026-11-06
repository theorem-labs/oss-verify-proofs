(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first half of the walk of sup_chain_clear on plugin-hostd/fuzz_command.asan
   (the entry and the two arms of the inlined record() up to their join), in the walk style of
   lib/A/Prog/sup_chain_clear_s2.v; the entry seed after lib/A/Prog/sup_worker_list.v.
   The join and the rest of the walk are sup_chain_clear_s2.v's `scc_join`.
   Statement passes 4, 4b and 5: the rounding-mode-0 premise in place of astack_pres,
   handed to scc_join; the callees' contracts at every FP state, rec_calls_free's taken at the entry's. *)

(* sup_chain_clear (recorder.c:481-487, entry BASE + AF_sup_chain_clear = 0x8c558): this file walks 0x8c558 ..
   0x8c5c4: the prologue (a 32-byte frame holding ra, s0, s1, s2), the loads of g_rec.ncalls and of the shadow base,
   and record()'s `bne ncalls, 16`. The table arm stores ncalls + 1 and takes the slot g_rec + 16 + 56 * ncalls;
   the spill arm calls rec_calls_free(record.spill, 1) and takes record.spill. Both arms meet at 0x8c5c4. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  rec_calls_free_c arg_i_c rec_shape_of_c answer_c sup_chain_clear_c xstrdup_c hand_back_c mix_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaNoChain sup_chain_clear_s1 sup_chain_clear_s2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the listing offsets of this half: record()'s branch (0x8c58c) and the return from rec_calls_free (0x8c5a4) *)
Definition SCC_BR : Z := AF_sup_chain_clear + 0x34.
Definition SCC_RA_RCF : Z := AF_sup_chain_clear + 0x4c.
(* the symbolic state at the entry: atom 32 holds the shadow base, atom 33 the call count g_rec.ncalls *)
Definition scc_frame0 : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [].
Definition scc_ncalls : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 (SOff 33 0))].
Definition scc_rs0 : YP09.smem := [scc_frame0; got_regionP; bcell_regionP 32%nat; scc_ncalls].
Definition scc_facts0 : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 16 0);
         (A_OBJ 44, mkAF A_G_REC A_G_REC 3)] [] [].
Definition ss_entry : sstate := mkSS AF_sup_chain_clear sr_atoms scc_rs0 None scc_facts0.
Definition scc_Bx0 : sv := SOff 32 0.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition EE (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 n]).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the walk hypotheses of sup_chain_clear_s2.v's Section e, under the same names and in the same forms *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
(* the callee of record()'s spill arm *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* specialize the Section hypotheses a lemma of sup_chain_clear_s2.v takes after its Section closed *)
Ltac inst_sec J := repeat lazymatch type of J with
  | ?P -> _ => let h := fresh "h" in assert (h : P) by assumption; specialize (J h); clear h
  end.

(* sup_chain_clear_s2.v's lemmas at this Section's hypotheses *)
Lemma scc_awr_rec_w : forall STK sp0 O bl0 blc fr0 lyc own a,
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
awr_byte SEGS B STK sp0 (scc_FP O) bl0 blc fr0 lyc own a.
Proof. intros. pose proof (scc_awr_rec B) as J. inst_sec J. apply J. assumption. Qed.

Lemma scc_ro_off_w : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
forall a, in_roP SEGS RLO RHI a -> ~ inFP (scc_FP O) a.
Proof. intros. pose proof (scc_ro_off B) as J. inst_sec J. eapply J; eassumption. Qed.

Lemma scc_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

Lemma scc_entry_seed : forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) n,
AR SEGS B ly S W mem md ->
2 ^ 46 + 32 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) mem a) ->
0 <= n <= 16 -> aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n ->
st_ok_pi SEGS VAL (EE regs n) ss_entry
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_chain_clear)) mem (seg_rom SEGS)))
/\ sh_ok SEGS scc_Bx0 [] (EE regs n) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs n HAR Hsp Hsp16 Hpres Hn HNC.
set (E := EE regs n).
assert (HEI : img_env VAL A_LIM E) by (unfold E, EE; apply Eimg_env).
assert (EL : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r).
{ intros k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E, EE. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (E32 : ew E 32 = Z_to_bv 64 SB).
{ unfold E, EE. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0%nat). }
assert (E33 : ew E 33 = Z_to_bv 64 n).
{ unfold E, EE. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1%nat). }
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EL 2%nat 2%bv eq_refl); reflexivity).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hgot_r. pose proof (pa_obj_img 12%nat ltac:(lia)) as Hcell_r.
assert (EG : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC).
{ rewrite (img_env_atomP E (A_OBJ 44) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). reflexivity. }
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (exact (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (exact (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (EV0 : VAL (A_OBJ 0) = 0xa63f0)
  by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (EV12 : VAL (A_OBJ 12) = 0xb10b8)
  by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (VB2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact E2).
split; [| unfold sh_ok; apply Forall_nil].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- unfold E, EE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold scc_rs0, scc_frame0, got_regionP, bcell_regionP, scc_ncalls.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite VB2. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
    constructor.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); pose proof (pa_val_range (A_OBJ 12)); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); cbv [SHADOW_OFF]; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB (A_OBJ 44) A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|].
      apply scc_in_PG. left. unfold OFF_NCALLS, REC_SIZE, A_G_REC in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 (SOff 33 0) n);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H W) mem (A_G_REC + OFF_NCALLS) 4%nat n HNC).
- apply pairwise_disjoint_of_extents.
  unfold scc_rs0, scc_frame0, got_regionP, bcell_regionP, scc_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB (A_OBJ 44) A_G_REC EG) by (unfold A_G_REC; lia).
  rewrite VB2, EV0, EV12.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, OFF_NCALLS in *. repeat split; lia.
- unfold scc_facts0, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  split; [|split; [|split; [|split; [|exact I]]]].
  + apply (scc_afact E 2%nat (spZ regs)); [rewrite <- E2; symmetry; apply Z_to_bv_bv_unsigned | lia | lia
    | change (2 ^ 4) with 16; exact Hsp16 | lia].
  + apply (scc_afact E 32%nat SB); [exact E32 | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
  + apply (scc_afact E 33%nat n); [exact E33 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
  + apply (scc_afact E (A_OBJ 44) A_G_REC); [exact EG | unfold A_G_REC; lia | lia
    | change (2 ^ 3) with 8; unfold A_G_REC; reflexivity | lia].
Qed.

Lemma scc_sig_rcf : SIG CS_rec_calls_free = BASE + AF_rec_calls_free.
Proof. pose proof scc_sig as J. inst_sec J. exact (proj1 J). Qed.

(* the slot the table arm computes: g_rec + 16 + 56 * ncalls (slli / slli / sub folded to one multiplication) *)
Lemma scc_slot_val : forall E n, ew E 33 = Z_to_bv 64 n -> 0 <= n <= 16 -> ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC ->
alu64 ALU_ADD (alu64 ALU_ADD (mul_div M_MUL (ew E 33) (Z_to_bv 64 56)) (Z_to_bv 64 16)) (ew E (A_OBJ 44)) =
Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * n).
Proof.
intros E n HN Hn HG. rewrite HN, HG. apply bv_eq.
assert (Hc : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
  n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16) by lia.
repeat (destruct Hc as [-> | Hc]; [vm_compute; reflexivity|]). subst n. vm_compute. reflexivity.
Qed.

(* a live block lies below the allocator's ceiling, apart from the stack *)
Lemma scc_blk_bnd : forall ly S (W : world SEGS) mem md p k i, AR SEGS B ly S W mem md ->
In (p, k) (ablocks B ly S) -> 0 <= i < req_size k -> 4096 <= p + i < alloc_ceiling.
Proof.
intros ly S W mem md p k i HAR Hin Hi.
destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hin) as (_ & H4 & Hc & _). lia.
Qed.

(* a frame word the prologue stored, read back *)
Lemma scc_frame_rd : forall Ex (W' : world SEGS) m sp0 cs od (k : nat) (v : word),
region_ok SEGS Ex (mrestrict (w_H W') m) (YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 cs) ->
bv_unsigned (ew Ex 2) = sp0 -> In (YP09.mkChunk od (CVal 8 (SOff k 0))) cs -> ew Ex k = v ->
rdword (rdW W' m) (sp0 + od) = Some (bv_unsigned v).
Proof.
intros Ex W' m sp0 cs od k v HR Hsp Hin Hk.
pose proof (bv_unsigned_in_range 64 v) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
apply rdword_of_val_mem; [|exact Hr].
apply (field_of_region (segs := SEGS) Ex _ 2%nat sp0 cs (-32) 0 (-32) 0 od 8 (SOff k 0) (bv_unsigned v) HR Hsp Hin);
[cbn [sv_denot]; rewrite Hk, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hr | cbn; lia].
Qed.

Lemma scc_hi_regs : forall (rg regs : bvmap 5 word),
getr rg (19%bv : bv 5) = getr regs (19%bv : bv 5) -> getr rg (20%bv : bv 5) = getr regs (20%bv : bv 5) ->
getr rg (21%bv : bv 5) = getr regs (21%bv : bv 5) -> getr rg (22%bv : bv 5) = getr regs (22%bv : bv 5) ->
getr rg (23%bv : bv 5) = getr regs (23%bv : bv 5) -> getr rg (24%bv : bv 5) = getr regs (24%bv : bv 5) ->
getr rg (25%bv : bv 5) = getr regs (25%bv : bv 5) -> getr rg (26%bv : bv 5) = getr regs (26%bv : bv 5) ->
getr rg (27%bv : bv 5) = getr regs (27%bv : bv 5) ->
forall r, acallee_saved r -> 19 <= r -> getr rg (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
intros rg regs H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr Hge. unfold acallee_saved in Hr.
assert (Hcases : r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). exact H19.
- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). exact H20.
- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). exact H21.
- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). exact H22.
- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). exact H23.
- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). exact H24.
- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). exact H25.
- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). exact H26.
- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). exact H27.
Qed.

(* record()'s `bne ncalls, 16` over the call count's atom *)
Lemma scc_bne : forall E n, ew E 33 = Z_to_bv 64 n -> 0 <= n <= 16 ->
branch_taken BC_NE (sv_denot E (SOff 33 0)) (sv_denot E (SLit 16)) = negb (n =? 16).
Proof.
intros E n H Hn. rewrite branch_ne_U.
assert (U1 : U E (SOff 33 0) = n).
{ unfold U. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia. }
rewrite U1, U_SLit. reflexivity.
Qed.

Lemma scc_region_nth : forall E ss ms i r, st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. apply (st_ok_region_nth E (abs_ss VAL ss) ms i r HS). destruct ss; exact Hi. Qed.

(* two memories holding the same value at a field agree on its bytes *)
Lemma scc_rd_of_val : forall (W : world SEGS) m m' a n v x,
val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v -> a <= x < a + Z.of_nat n ->
rdW W m' x = rdW W m x.
Proof.
intros W m m' a n v x H H' Hx. replace x with (a + (x - a)) by lia. unfold aview.
rewrite (val_mem_agree SEGS _ _ a n v H H' (x - a) ltac:(lia)). reflexivity.
Qed.

Lemma scc_bsum_nonneg : forall l, (forall x, In x l -> 0 <= snd x) -> 0 <= bsum l.
Proof.
unfold bsum. induction l as [|y l IH]; intros H; cbn [fold_right]; [lia|].
pose proof (H y (or_introl eq_refl)). pose proof (IH (fun x Hx => H x (or_intror Hx))). lia.
Qed.

(* rec_calls_free's footprint for record.spill with one entry: its nargs field and its argument blocks *)
Lemma scc_rcf_fp_in : forall (P : list (Z * Z)) a, inFP (rcf_fp A_REC_SPILL [P]) a ->
(A_REC_SPILL + CALL_OFF_NARGS <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) \/
exists b k, In (b, k) P /\ b <= a < b + req_size k.
Proof.
intros P a (r & Hr & Ha). unfold rcf_fp in Hr. cbn [length seq map concat] in Hr.
apply in_app_or in Hr as [Hr | Hr].
- destruct Hr as [<- | []]. left. cbn [fst snd] in Ha. unfold CALL_SIZE in Ha. lia.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b k] & <- & Hin). rewrite app_nil_r in Hin.
  cbn [fst snd] in Ha. exists b, k. split; [exact Hin | exact Ha].
Qed.

(* the writable windows of the entry's regions: the frame and g_rec.ncalls *)
Definition scc_win (sp0 a : Z) : Prop :=
sp0 - 32 <= a < sp0 \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4.

Ltac scc_win_tac Usp UG :=
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin];
  [injection Hq as <- <- <-; cbn [base_val] in Hrr; unfold scc_win;
   first [lia | rewrite Usp in Hrr; lia
         | change 285%nat with (A_OBJ 44) in Hrr; rewrite UG in Hrr; unfold OFF_NCALLS; lia]|]);
destruct Hin.

(* the walk's writes before the join: the frame, and g_rec.ncalls on the table arm *)
Ltac scc_awr4 Usp UG WS :=
lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact Usp | cbn; rewrite WS; lia | cbn; lia |];
apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
eapply awr_ok_cons_gen with (n := A_OBJ 44); [reflexivity | exact UG | | apply awr_ok_nil];
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply scc_awr_rec_w; left; unfold OFF_NCALLS, REC_SIZE in *; lia.

Theorem tsup_chain_clear_holds : tsup_chain_clear_spec B MT.
Proof.
unfold tsup_chain_clear_spec.
intros ly S W regs mem md ch id R O HPRE HFRM HROD HROOK H10 Hid HREP HFR HEV HLIVE HMOK.
change (SRr SEGS W (cfg_at SEGS (BASE + AF_sup_chain_clear) regs mem md)
  (apost_baseF SEGS B SUP_CHAIN_CLEAR_STK (scc_FP O) regs ly S W mem md (EV_SUP_CHAIN_CLEAR R) (scc_Q B MT ly S id R O))).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (WS : SUP_CHAIN_CLEAR_STK = 16592) by reflexivity.
assert (Hsp46 : 2 ^ 46 + 32 <= spZ regs <= 2 ^ 47).
{ change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328. rewrite WS in Hslo. lia. }
set (sp0 := spZ regs) in *.
assert (Hstklo : alloc_ceiling + 16592 <= sp0) by (rewrite WS in Hslo; lia).
destruct (rec_repA_ncalls B ly S _ R O HREP) as [Hlen HNC].
assert (HOS : forall pn, In pn O -> In pn (ablocks B ly S))
  by (intros pn Hpn; exact (proj1 (rec_repA_blocks B ly S _ R O HREP pn Hpn))).
set (n := Z.of_nat (length (r_calls R))) in *.
assert (Hn : 0 <= n <= 16) by (unfold n; lia).
destruct (scc_entry_seed ly S W mem md regs n HAR Hsp46 Hsp16
  ltac:(intros a Ha; apply Hpres; rewrite WS; lia) Hn HNC) as [HS SHOK].
set (E := EE regs n) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, EE; apply Eimg_env).
assert (EL : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r).
{ intros k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E, EE. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (E32 : ew E 32 = Z_to_bv 64 SB).
{ unfold E, EE. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0%nat). }
assert (E33 : ew E 33 = Z_to_bv 64 n).
{ unfold E, EE. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1%nat). }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EL 2%nat 2%bv eq_refl); reflexivity).
assert (EG : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC).
{ rewrite (img_env_atomP E (A_OBJ 44) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). reflexivity. }
assert (ESP : ew E (A_OBJ 51) = Z_to_bv 64 A_REC_SPILL).
{ rewrite (img_env_atomP E (A_OBJ 51) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). reflexivity. }
assert (UG : bv_unsigned (ew E (A_OBJ 44)) = A_G_REC) by (rewrite EG; apply unsigned_lit_small; unfold A_G_REC; lia).
clearbody E.
pose proof (ajournal_init SEGS B SUP_CHAIN_CLEAR_STK (scc_FP O) ly S W regs mem md ch HPRE) as HJ.
unfold cfg_at, w64.
(* 0x8c558 .. 0x8c58c: the prologue, the loads of g_rec.ncalls and of the shadow base, up to record()'s branch *)
paj_run_tok RUN HS HJ SHOK scc_Bspan.
{ scc_awr4 Usp UG WS. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (md1 := mdq) in *; clearbody md1 end.
pose proof (kept_of_frame (segs := SEGS) E _ (w_H W) mem _ (scc_win sp0) HFr
  ltac:(scc_win_tac Usp UG)) as UN1.
clear HF HFr HG.
pose proof (scc_join B MT) as J. inst_sec J.
psrr_branch_tok RUN BR HS SHOK scc_Bspan.
- (* record()'s table arm: ncalls <> 16 *)
  rewrite (scc_bne E n E33 Hn) in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  assert (Hlt16 : (length (r_calls R) < 16)%nat) by (unfold n in Hc; lia).
  set (c := A_G_REC + OFF_CALLS + CALL_SIZE * n).
  assert (Ec : c = rec_slotA R) by (unfold c, rec_slotA, n; rewrite (proj2 (Nat.ltb_lt _ _) Hlt16); reflexivity).
  assert (Hcb : A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + REC_SIZE)
    by (unfold c, A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE; lia).
  (* 0x8c5a8 .. 0x8c5c4: ncalls := n + 1, s0 := g_rec + 16 + 56 * n *)
  paj_run_to_tok RUNTO HS HJ SHOK scc_Bspan SCC_JOIN.
  { scc_awr4 Usp UG WS. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
  prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) scc_frame0) in
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) scc_ncalls) in
    pose proof (scc_region_nth E ssx (restrict (w_H W) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRf;
    pose proof (scc_region_nth E ssx (restrict (w_H W) msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRn
  end.
  cbn [ms_mem restrict mkst] in HRf, HRn.
  pose proof (kept_of_frame (segs := SEGS) E _ (w_H W) _ _ (scc_win sp0) HFr ltac:(scc_win_tac Usp UG)) as UN2.
  clear HF HFr HG.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    set (rgJ := rg) in *; set (mJ := mm) in *; set (mdJ := mdq) in *; clearbody mdJ end.
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ scc_win sp0 a -> rdW W mJ a = rdW W mem a)
    by (intros a Ha Hw; rewrite (UN2 a Ha Hw); exact (UN1 a Ha Hw)).
  (* the join's memory: ncalls holds n + 1, the frame the four saved registers *)
  assert (Vnc : val_mem SEGS (mrestrict (w_H W) mJ) (A_G_REC + OFF_NCALLS) 4 (n + 1)).
  { exact (field_of_region (segs := SEGS) E _ _ A_G_REC _ _ _ _ _ 8 4 (SOff 33 1) (n + 1) HRn UG ltac:(cbn; tauto)
      ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity)
      ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)). }
  assert (F0 : rdword (rdW W mJ) (sp0 - 32) = Some (bv_unsigned (getr regs 18))).
  { replace (sp0 - 32) with (sp0 + -32) by lia.
    exact (scc_frame_rd E W mJ sp0 _ (-32) 18 (getr regs 18) HRf Usp ltac:(cbn; tauto) (EL 18%nat 18%bv eq_refl)). }
  assert (F8 : rdword (rdW W mJ) (sp0 - 24) = Some (bv_unsigned (getr regs 9))).
  { replace (sp0 - 24) with (sp0 + -24) by lia.
    exact (scc_frame_rd E W mJ sp0 _ (-24) 9 (getr regs 9) HRf Usp ltac:(cbn; tauto) (EL 9%nat 9%bv eq_refl)). }
  assert (F16 : rdword (rdW W mJ) (sp0 - 16) = Some (bv_unsigned (getr regs 8))).
  { replace (sp0 - 16) with (sp0 + -16) by lia.
    exact (scc_frame_rd E W mJ sp0 _ (-16) 8 (getr regs 8) HRf Usp ltac:(cbn; tauto) (EL 8%nat 8%bv eq_refl)). }
  assert (F24 : rdword (rdW W mJ) (sp0 - 8) = Some (bv_unsigned (getr regs 1))).
  { replace (sp0 - 8) with (sp0 + -8) by lia.
    exact (scc_frame_rd E W mJ sp0 _ (-8) 1 (getr regs 1) HRf Usp ltac:(cbn; tauto) (EL 1%nat 1%bv eq_refl)). }
  (* the join's registers *)
  assert (Hspc : spZ rgJ = sp0 - 32) by (unfold spZ; rewrite P2, Usp, unsigned_lit_small by lia; lia).
  assert (H8 : getr rgJ 8 = w64 c).
  { rewrite P8. change (ew E 285) with (ew E (A_OBJ 44)). exact (scc_slot_val E n E33 Hn EG). }
  assert (H9 : getr rgJ 9 = w64 id) by (rewrite P9, (EL 10%nat 10%bv eq_refl); exact H10).
  assert (H18 : getr rgJ 18 = w64 SB) by (rewrite P18, E32; reflexivity).
  assert (H3 : getr rgJ 3 = getr regs 3) by (rewrite P3; exact (EL 3%nat 3%bv eq_refl)).
  assert (H4 : getr rgJ 4 = getr regs 4) by (rewrite P4; exact (EL 4%nat 4%bv eq_refl)).
  assert (Hcs : forall r, acallee_saved r -> 19 <= r -> getr rgJ (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { apply scc_hi_regs;
    [rewrite P19; exact (EL 19%nat 19%bv eq_refl) | rewrite P20; exact (EL 20%nat 20%bv eq_refl)
    | rewrite P21; exact (EL 21%nat 21%bv eq_refl) | rewrite P22; exact (EL 22%nat 22%bv eq_refl)
    | rewrite P23; exact (EL 23%nat 23%bv eq_refl) | rewrite P24; exact (EL 24%nat 24%bv eq_refl)
    | rewrite P25; exact (EL 25%nat 25%bv eq_refl) | rewrite P26; exact (EL 26%nat 26%bv eq_refl)
    | rewrite P27; exact (EL 27%nat 27%bv eq_refl)]. }
  (* the recorder once the inlined record() has stored fn and nargs to the slot (s1's rec_repA_record_lt) *)
  assert (HPEND : forall rd', (forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rd' a = rdW W mJ a) ->
     aval_mem rd' c 4 REC_CHAIN_CLEAR -> aval_mem rd' (c + 4) 4 0 ->
     rec_repA B ly S rd' (rec_record R REC_CHAIN_CLEAR []) O).
  { intros rd' Hrd Hfn Hna.
    apply (rec_repA_record_lt B ly S (rdW W mem) ly S rd' R O REC_CHAIN_CLEAR HREP Hlt16).
    - unfold REC_CHAIN_CLEAR, REC_FN_COUNT. lia.
    - apply (aval_mem_keep (rdW W mJ)); [exact (aval_mem_view SEGS (w_H W) mJ _ 4 (n + 1) Vnc)|].
      intros x Hx. apply Hrd; unfold c, A_G_REC, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
    - rewrite <- Ec. unfold CALL_OFF_FN. rewrite Z.add_0_r. exact Hfn.
    - rewrite <- Ec. unfold CALL_OFF_NARGS. exact Hna.
    - intros a Ha Hn1 Hn2. rewrite <- Ec in Hn2.
      assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold in_recA, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia).
      rewrite (Hrd a Ha64 Hn2). apply UN; [exact Ha64|]. unfold scc_win.
      unfold in_recA, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
    - intros [p k] Hpn. destruct (rec_repA_blocks B ly S _ R O HREP (p, k) Hpn) as (Hin & _ & Hap1 & _).
      split; [exact Hin|]. intros i Hi. cbn [fst snd] in Hi |- *.
      pose proof (req_size_pos k ltac:(lia)) as [_ Rk].
      pose proof (scc_blk_bnd ly S W mem md p k i HAR Hin ltac:(lia)) as Hb.
      unfold iv_apart in Hap1. cbn [fst snd] in Hap1.
      rewrite (Hrd (p + i) ltac:(lia) ltac:(unfold c, A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia)).
      apply UN; [lia|]. unfold scc_win. unfold A_G_REC, OFF_NCALLS, REC_SIZE in *. lia. }
  assert (Hsf0 : rec_spill_frees R = 0)
    by (unfold rec_spill_frees; rewrite (proj2 (Nat.ltb_lt _ _) Hlt16); reflexivity).
  assert (Hkc : 0 <= rec_spill_frees R) by lia.
  assert (HMLE : mo_le MT S S (rec_spill_frees R * mo_free MT))
    by (rewrite Hsf0, Z.mul_0_l; exact (mle_start MT S MTL)).
  exact (J ly S W regs mem md ch id R O ly S W rgJ mJ mdJ 0 O c HPRE HFRM HROD HROOK H10 Hid HFR HEV HLIVE HMOK
    Hlen HOS HJ Hkc HMLE (Z.le_refl _) Ec HPEND (fun pn H => H) (fun pn H _ => H) (fun _ pn H => H)
    (fun pn H => H) (fun pn H _ => H) Hspc H8 H9 H18 H3 H4 Hcs F0 F8 F16 F24).
- (* record()'s spill arm: ncalls = 16 *)
  rewrite (scc_bne E n E33 Hn) in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  assert (H16 : length (r_calls R) = 16%nat) by (unfold n in Hc; lia).
  assert (Hsf : rec_spill_frees R = Z.of_nat (length (snd (r_spill R))))
    by (unfold rec_spill_frees; rewrite H16; reflexivity).
  assert (Ec : A_REC_SPILL = rec_slotA R) by (unfold rec_slotA; rewrite H16; reflexivity).
  (* 0x8c590 .. 0x8c5a0: s0 := record.spill, a0 := s0, a1 := 1, the call of rec_calls_free *)
  paj_run_tok RUN HS HJ SHOK scc_Bspan.
  { scc_awr4 Usp UG WS. }
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) scc_ncalls) in
    pose proof (st_ok_region_nth E ssx (restrict (w_H W) msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRn
  end.
  cbn [ms_mem restrict mkst] in HRn.
  pose proof (kept_of_frame (segs := SEGS) E _ (w_H W) _ _ (scc_win sp0) HFr ltac:(scc_win_tac Usp UG)) as UN2.
  clear HF HFr HG.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    set (rgA := rg) in *; set (mA := mm) in *; set (mdA := mdq) in *; clearbody mdA end.
  (* the call's memory: the recorder as at the entry (ncalls still n, the frame aside) *)
  assert (Vnc : val_mem SEGS (mrestrict (w_H W) mA) (A_G_REC + OFF_NCALLS) 4 n).
  { exact (field_of_region (segs := SEGS) E _ _ A_G_REC _ _ _ _ _ 8 4 (SOff 33 0) n HRn UG ltac:(cbn; tauto)
      ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)). }
  assert (UNa : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> rdW W mA a = rdW W mem a).
  { intros a Ha Hw.
    assert (Hd : (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) \/
                 ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)) by lia.
    destruct Hd as [Hd | Hd].
    - exact (scc_rd_of_val W mem mA (A_G_REC + OFF_NCALLS) 4 n a (val_mem_view SEGS (w_H W) mem _ 4 n HNC) Vnc
        ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
    - rewrite (UN2 a Ha ltac:(unfold scc_win; lia)). exact (UN1 a Ha ltac:(unfold scc_win; lia)). }
  assert (KREC : forall a, in_recA a -> rdW W mA a = rdW W mem a).
  { intros a Ha. unfold in_recA, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. apply UNa; lia. }
  assert (KBLK : forall pn, In pn (ablocks B ly S) -> forall i, 0 <= i < snd pn ->
    rdW W mA (fst pn + i) = rdW W mem (fst pn + i)).
  { intros [p k] Hin i Hi. cbn [fst snd] in *. pose proof (req_size_pos k ltac:(lia)) as [_ Rk].
    pose proof (scc_blk_bnd ly S W mem md p k i HAR Hin ltac:(lia)) as Hb. apply UNa; lia. }
  assert (HREPa : rec_repA B ly S (rdW W mA) R O).
  { apply (rec_repA_keep B ly S (rdW W mem) ly S (rdW W mA) R O HREP KREC).
    intros pn Hpn. split; [exact (HOS _ Hpn) | exact (KBLK pn (HOS _ Hpn))]. }
  destruct (rec_repA_spill B ly S (rdW W mA) R O HREPa) as (Q & HAQ & HOQ & Hls6 & Hlsl & HNA & HARGS & HND & HLB).
  set (ps := [l_spill Q]).
  set (O1 := concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)).
  assert (Hcps : forall pn, In pn (concat ps) -> In pn (l_spill Q))
    by (intros pn Hpn; unfold ps in Hpn; cbn [concat] in Hpn; rewrite app_nil_r in Hpn; exact Hpn).
  assert (Hlps : Z.of_nat (length (concat ps)) = rec_spill_frees R)
    by (unfold ps; cbn [concat]; rewrite app_nil_r, Hlsl, Hsf; reflexivity).
  assert (HspO : forall pn, In pn (l_spill Q) -> In pn O)
    by (intros pn Hpn; apply HOQ, HLB; right; exact Hpn).
  pose proof (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ
    (scc_ro_off_w ly S W mem md O HAR HOS) HROD) as HRODa.
  assert (HXa : 0 <= XM_ARG_I MT id /\ 0 <= XM_ANSWER MT (snd (sup_chain_clear_m R id))).
  { unfold XM_ARG_I, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
    pose proof (mo_free_nonneg MT MTL). pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (dec id)) + 1) ltac:(lia)).
    pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_chain_clear_m R id))) + 1) ltac:(lia)). lia. }
  pose proof (mo_free_nonneg MT MTL) as Hmf.
  assert (Hsfn : 0 <= rec_spill_frees R) by (rewrite Hsf; lia).
  assert (P10' : getr rgA 10 = w64 A_REC_SPILL) by (rewrite P10; change (ew E 292) with (ew E (A_OBJ 51)); exact ESP).
  assert (P11' : getr rgA 11 = w64 (Z.of_nat (length ps))) by (rewrite P11; reflexivity).
  (* the call of rec_calls_free(record.spill, 1): it frees the spill's argument blocks and zeroes its nargs *)
  rewrite scc_sig_rcf.
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS W rgA mA _ SUP_CHAIN_CLEAR_STK sp0 (scc_FP O) ly S W mem md [] ly S mdA 0
      REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL ps) (EV_REC_CALLS_FREE ps) (-32) (getr rgA 1) []
      (fun ly' S' W' (regs' : bvmap 5 word) mem' (md' : Model) =>
         Permutation (ablocks B ly S) (ablocks B ly' S' ++ concat ps) /\
         rec_repA B ly' S' (rdW W' mem') (set_spill R (fst (r_spill R), [])) O1 /\
         mo_le MT S S' (XM_REC_CALLS_FREE MT ps)) HJ).
    - unfold spZ. rewrite P2, Usp, unsigned_lit_small by lia. lia.
    - reflexivity.
    - lia.
    - unfold REC_CALLS_FREE_STK, ASTACK. lia.
    - rewrite WS. unfold REC_CALLS_FREE_STK, ASTACK. lia.
    - rewrite P3, (EL 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite P4, (EL 4%nat 4%bv eq_refl). exact Htp.
    - reflexivity.
    - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite P1, unsigned_lit_small by lia. lia.
    - apply achain_low. unfold s0Z. rewrite P8. change (ew E 292) with (ew E (A_OBJ 51)).
      rewrite ESP, unsigned_lit_small by (unfold A_REC_SPILL; lia). unfold A_REC_SPILL. lia.
    - intros HPRE1. eapply SRr_mono.
      + refine (TRCF fx ly S W rgA mA mdA [] A_REC_SPILL ps HPRE1 HRODa P10' P11' _ _ _ _ _ _ _).
        * unfold ps. cbn. lia.
        * right; left. unfold ps. cbn [length]. unfold CALL_SIZE, SC_SIZE. lia.
        * unfold A_REC_SPILL. reflexivity.
        * intros i P Hi. destruct i as [|i]; unfold ps in Hi; cbn in Hi; [injection Hi as <- | destruct i; discriminate Hi].
          split; [exact Hls6|].
          replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0) with A_REC_SPILL by (cbn; lia).
          split; [exact HNA|]. intros a pn Ha. exact (HARGS a pn Ha).
        * unfold ps. cbn [concat]. rewrite app_nil_r. exact HND.
        * unfold EV_REC_CALLS_FREE. rewrite Hlps.
          unfold EV_SUP_CHAIN_CLEAR, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in HEV. lia.
        * apply (mok_station MT S S (XM_SUP_CHAIN_CLEAR MT R id) 0 _ MTL HMOK (mle_start MT S MTL));
            unfold XM_REC_CALLS_FREE; rewrite Hlps; [apply Z.mul_nonneg_nonneg; lia | unfold XM_SUP_CHAIN_CLEAR; lia].
      + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hperm & _ & _ & _ & _ & HSP & _ & _ & HMLE2).
        exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
        split; [exact Hperm|]. split; [exact (HSP R Q HAQ eq_refl eq_refl) | exact HMLE2].
    - intros a Ha. destruct (scc_rcf_fp_in _ a Ha) as [Hn' | (b & k & Hbk & Hba)].
      + apply scc_awr_rec_w. right. unfold A_REC_SPILL, CALL_OFF_NARGS, SC_SIZE in *. lia.
      + right; left. split.
        * exists (b, b + req_size k). split; [|cbn [fst snd]; lia].
          right; right. unfold ablocks_fp. apply in_map_iff. exists (b, k). split; [reflexivity | exact (HspO _ Hbk)].
        * exists b, k. split; [exact (HOS _ (HspO _ Hbk)) | exact Hba].
    - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
      destruct (scc_rcf_fp_in _ a Ha) as [Hn' | (b & k & Hbk & Hba)];
        [rewrite WS in Hw; unfold A_REC_SPILL, CALL_OFF_NARGS in Hn'; lia|].
      pose proof (scc_blk_bnd ly S W mem md b k (a - b) HAR (HOS _ (HspO _ Hbk)) ltac:(lia)).
      rewrite WS in Hw. lia. }
  cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HK3). rewrite P1.
  jafter_call_keep_pi HS 40%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
  match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    eapply (region_kept_stack_sub SEGS B);
      [exact HJc3 | exact HJ3 | exact Usp | lia | rewrite WS; lia | lia | cbn; lia | cbn; lia |].
    intros a Ha Hf. destruct (scc_rcf_fp_in _ a Hf) as [Hn' | (b & k & Hbk & Hba)];
      [unfold A_REC_SPILL, CALL_OFF_NARGS in Hn'; lia|].
    pose proof (scc_blk_bnd ly S W mem md b k (a - b) HAR (HOS _ (HspO _ Hbk)) ltac:(lia)). lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  remember (havoc E 40 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall k, (k < 40)%nat -> ew Ea k = ew E k)
    by (intros k Hk; rewrite HEa; apply YN3v.ew_havoc_old; exact Hk).
  clear HEa.
  assert (Uspa : bv_unsigned (ew Ea 2) = sp0) by (rewrite (OLDa 2%nat ltac:(lia)); exact Usp).
  (* 0x8c5a4: j 0x8c5c4 *)
  assert (SHOKa : sh_ok SEGS scc_Bx0 [] Ea (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
  paj_run_to_tok RUNTO HS HJ3 SHOKa scc_Bspan SCC_JOIN.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_stack with (n := 2%nat);
      [reflexivity | exact Uspa | cbn; rewrite WS; lia | cbn; lia | apply awr_ok_nil]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) scc_frame0) in
    pose proof (scc_region_nth Ea ssx (restrict (w_H W3) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRf
  end.
  cbn [ms_mem restrict mkst] in HRf.
  pose proof (kept_of_frame (segs := SEGS) Ea _ (w_H W3) _ _ (fun a => sp0 - 32 <= a < sp0) HFr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
            rewrite Uspa in Hrr; lia|]); destruct Hin)) as UN3.
  clear HF HFr HG.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    set (rgJ := rg) in *; set (mJ := mm) in *; set (mdJ := mdq) in *; clearbody mdJ end.
  destruct HK3 as (Hperm & HREP3m & HMLE3).
  pose proof (proj1 HJ3) as HAR3.
  (* the recorder at the join: rec_calls_free's post, the jump to the join wrote nothing of it *)
  assert (HREP3 : rec_repA B ly3 S3 (rdW W3 mJ) (set_spill R (fst (r_spill R), [])) O1).
  { apply (rec_repA_keep B ly3 S3 (rdW W3 mem3) ly3 S3 (rdW W3 mJ) _ O1 HREP3m).
    - intros a Ha. unfold in_recA, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. apply UN3; lia.
    - intros [p k] Hpn. destruct (rec_repA_blocks B ly3 S3 _ _ O1 HREP3m (p, k) Hpn) as (Hin3 & _).
      split; [exact Hin3|]. intros i Hi. cbn [fst snd] in Hi |- *.
      pose proof (req_size_pos k ltac:(lia)) as [_ Rk].
      pose proof (scc_blk_bnd ly3 S3 W3 mJ mdJ p k i HAR3 Hin3 ltac:(lia)). apply UN3; lia. }
  assert (HPEND : forall rd', (forall a, 0 <= a < 2 ^ 64 -> ~ (A_REC_SPILL <= a < A_REC_SPILL + 8) -> rd' a = rdW W3 mJ a) ->
     aval_mem rd' A_REC_SPILL 4 REC_CHAIN_CLEAR -> aval_mem rd' (A_REC_SPILL + 4) 4 0 ->
     rec_repA B ly3 S3 rd' (rec_record R REC_CHAIN_CLEAR []) O1).
  { intros rd' Hrd Hfn Hna. rewrite (rec_record_spill R REC_CHAIN_CLEAR [] H16).
    refine (rec_repA_spill_fn B ly3 S3 (rdW W3 mJ) ly3 S3 rd' (set_spill R (fst (r_spill R), [])) O1 REC_CHAIN_CLEAR
      HREP3 eq_refl _ _ _ _ _).
    - unfold REC_CHAIN_CLEAR, REC_FN_COUNT. lia.
    - unfold CALL_OFF_FN. rewrite Z.add_0_r. exact Hfn.
    - unfold CALL_OFF_NARGS. exact Hna.
    - intros a Ha Hn'. apply Hrd; [unfold in_recA, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia | exact Hn'].
    - intros [p k] Hpn. destruct (rec_repA_blocks B ly3 S3 _ _ O1 HREP3 (p, k) Hpn) as (Hin3 & _ & _ & Hap).
      split; [exact Hin3|]. intros i Hi. cbn [fst snd] in Hi, Hap |- *.
      pose proof (req_size_pos k ltac:(lia)) as [_ Rk].
      pose proof (scc_blk_bnd ly3 S3 W3 mJ mdJ p k i HAR3 Hin3 ltac:(lia)).
      unfold iv_apart in Hap. apply Hrd; [lia | unfold SC_SIZE in Hap; lia]. }
  (* the join's memory and registers *)
  assert (F0 : rdword (rdW W3 mJ) (sp0 - 32) = Some (bv_unsigned (getr regs 18))).
  { replace (sp0 - 32) with (sp0 + -32) by lia.
    exact (scc_frame_rd Ea W3 mJ sp0 _ (-32) 18 (getr regs 18) HRf Uspa ltac:(cbn; tauto)
      ltac:(rewrite (OLDa 18%nat ltac:(lia)); exact (EL 18%nat 18%bv eq_refl))). }
  assert (F8 : rdword (rdW W3 mJ) (sp0 - 24) = Some (bv_unsigned (getr regs 9))).
  { replace (sp0 - 24) with (sp0 + -24) by lia.
    exact (scc_frame_rd Ea W3 mJ sp0 _ (-24) 9 (getr regs 9) HRf Uspa ltac:(cbn; tauto)
      ltac:(rewrite (OLDa 9%nat ltac:(lia)); exact (EL 9%nat 9%bv eq_refl))). }
  assert (F16 : rdword (rdW W3 mJ) (sp0 - 16) = Some (bv_unsigned (getr regs 8))).
  { replace (sp0 - 16) with (sp0 + -16) by lia.
    exact (scc_frame_rd Ea W3 mJ sp0 _ (-16) 8 (getr regs 8) HRf Uspa ltac:(cbn; tauto)
      ltac:(rewrite (OLDa 8%nat ltac:(lia)); exact (EL 8%nat 8%bv eq_refl))). }
  assert (F24 : rdword (rdW W3 mJ) (sp0 - 8) = Some (bv_unsigned (getr regs 1))).
  { replace (sp0 - 8) with (sp0 + -8) by lia.
    exact (scc_frame_rd Ea W3 mJ sp0 _ (-8) 1 (getr regs 1) HRf Uspa ltac:(cbn; tauto)
      ltac:(rewrite (OLDa 1%nat ltac:(lia)); exact (EL 1%nat 1%bv eq_refl))). }
  assert (Hspc : spZ rgJ = sp0 - 32) by (unfold spZ; rewrite Q2, Uspa, unsigned_lit_small by lia; lia).
  assert (H8 : getr rgJ 8 = w64 A_REC_SPILL).
  { rewrite Q8. change (ew Ea 292) with (ew Ea (A_OBJ 51)).
    rewrite (img_env_atomP Ea (A_OBJ 51) HEIa ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). reflexivity. }
  assert (H9 : getr rgJ 9 = w64 id) by (rewrite Q9, (OLDa 10%nat ltac:(lia)), (EL 10%nat 10%bv eq_refl); exact H10).
  assert (H18 : getr rgJ 18 = w64 SB) by (rewrite Q18, (OLDa 32%nat ltac:(lia)), E32; reflexivity).
  assert (H3 : getr rgJ 3 = getr regs 3) by (rewrite Q3, (OLDa 3%nat ltac:(lia)); exact (EL 3%nat 3%bv eq_refl)).
  assert (H4 : getr rgJ 4 = getr regs 4) by (rewrite Q4, (OLDa 4%nat ltac:(lia)); exact (EL 4%nat 4%bv eq_refl)).
  assert (Hcs : forall r, acallee_saved r -> 19 <= r -> getr rgJ (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { apply scc_hi_regs;
    [rewrite Q19, (OLDa 19%nat ltac:(lia)); exact (EL 19%nat 19%bv eq_refl)
    | rewrite Q20, (OLDa 20%nat ltac:(lia)); exact (EL 20%nat 20%bv eq_refl)
    | rewrite Q21, (OLDa 21%nat ltac:(lia)); exact (EL 21%nat 21%bv eq_refl)
    | rewrite Q22, (OLDa 22%nat ltac:(lia)); exact (EL 22%nat 22%bv eq_refl)
    | rewrite Q23, (OLDa 23%nat ltac:(lia)); exact (EL 23%nat 23%bv eq_refl)
    | rewrite Q24, (OLDa 24%nat ltac:(lia)); exact (EL 24%nat 24%bv eq_refl)
    | rewrite Q25, (OLDa 25%nat ltac:(lia)); exact (EL 25%nat 25%bv eq_refl)
    | rewrite Q26, (OLDa 26%nat ltac:(lia)); exact (EL 26%nat 26%bv eq_refl)
    | rewrite Q27, (OLDa 27%nat ltac:(lia)); exact (EL 27%nat 27%bv eq_refl)]. }
  (* the block bookkeeping across rec_calls_free *)
  assert (Hkc : 0 + EV_REC_CALLS_FREE ps <= rec_spill_frees R) by (unfold EV_REC_CALLS_FREE; rewrite Hlps; lia).
  assert (HMLE : mo_le MT S S3 (rec_spill_frees R * mo_free MT))
    by (unfold XM_REC_CALLS_FREE in HMLE3; rewrite Hlps in HMLE3; exact HMLE3).
  assert (Hbb : blocks_bytes S3 <= blocks_bytes S).
  { rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B ly S), (bsum_perm _ _ Hperm), bsum_app.
    assert (Hnn : 0 <= bsum (concat ps)).
    { apply scc_bsum_nonneg. intros [p k] Hx. cbn [snd].
      destruct (al_blocks _ _ LAWS ly S W mem md p k HAR (HOS _ (HspO _ (Hcps _ Hx)))) as (_ & _ & _ & _ & _ & _ & Hk).
      lia. }
    lia. }
  assert (HB1 : forall pn, In pn (ablocks B ly3 S3) -> In pn (ablocks B ly S))
    by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hpn).
  assert (HB2 : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly3 S3)).
  { intros pn Hpn HnO. pose proof (Permutation_in _ Hperm Hpn) as H'. apply in_app_or in H' as [H' | H']; [exact H'|].
    exfalso. exact (HnO (HspO _ (Hcps _ H'))). }
  assert (HB3 : (length (r_calls R) < 16)%nat -> forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly3 S3))
    by (intros Hl; exfalso; lia).
  assert (HO1 : forall pn, In pn O1 -> In pn O) by (intros pn Hpn; apply HOQ, HLB; left; exact Hpn).
  assert (HO2 : forall pn, In pn O -> In pn (ablocks B ly3 S3) -> In pn O1).
  { intros pn HpO Hp3. apply HOQ, HLB in HpO as [H' | H']; [exact H'|]. exfalso.
    apply (list_nodup_app_disj (ablocks B ly3 S3) (concat ps) pn);
      [exact (Permutation_NoDup Hperm (recb_ablocks_nodup_m B ly S W mem md HAR)) | exact Hp3
      | unfold ps; cbn [concat]; rewrite app_nil_r; exact H']. }
  exact (J ly S W regs mem md ch id R O ly3 S3 W3 rgJ mJ mdJ (0 + EV_REC_CALLS_FREE ps) O1 A_REC_SPILL
    HPRE HFRM HROD HROOK H10 Hid HFR HEV HLIVE HMOK Hlen HOS HJ3 Hkc HMLE Hbb Ec HPEND HB1 HB2 HB3 HO1 HO2
    Hspc H8 H9 H18 H3 H4 Hcs F0 F8 F16 F24).
Qed.

End e.
End f.
End d.
