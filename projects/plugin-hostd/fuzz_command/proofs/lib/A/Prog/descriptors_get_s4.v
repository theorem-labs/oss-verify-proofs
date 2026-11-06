(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of descriptors_get's ASan walk (plugin-hostd/fuzz_command), after
   lib/A/Prog/sup_chain.v and sup_chain_s1.v (the entry seed and the run to record()'s join), RecBTemplate.v and
   sup_worker_list.v (the call count's atom bounds per arm), descriptors_add_s1.v / descriptors_add_s2.v (cl_callS and
   jafter_call_keep_pi) over fuzz_command's listing. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c hand_back_c rec_shape_of_c answer_c descriptors_get_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
descriptors_get_s1 RecBLemmas descriptors_get_s2 descriptors_get_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* descriptors_get from its entry (0x8cfa0) to the join of record()'s two arms (0x8d014). The symbolic entry state
   takes every register as its own atom, atom 32 the shadow base the GOT cell gives, atom 33 the call count
   g_rec.ncalls; its regions are the 48-byte frame, the GOT word, the shadow-base cell and g_rec.ncalls. The call
   count's chunk and atom bounds are chosen per arm (RecBTemplate.v's rbt_facts): on the table arm the atom with
   [0, 15] and a writable word, on the spill arm the literal 16 and a read-only word, so the executor decides
   record()'s `bne ncalls, 16` itself and the spill arm's runs write the frame only. *)
Definition DG_GREC : nat := A_OBJ 44.
Definition DG_SPILL : nat := A_OBJ 51.
Definition dg_Bx0 : sv := SOff 32 0.
Definition dg_ncallsR (nv : sv) (w : Z) : YP09.region :=
YP09.mkRegion (Some DG_GREC) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + w) [YP09.mkChunk OFF_NCALLS (CVal 4 nv)].
Definition dg_rs0 (nv : sv) (w : Z) : smem := [stack_region 48; got_regionP; bcell_regionP 32; dg_ncallsR nv w].
Definition dg_facts0 (lo hi : Z) : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF lo hi 0);
         (DG_GREC, mkAF A_G_REC A_G_REC 3)] [] [].
Definition ss_dg0 (nv : sv) (w lo hi : Z) : sstate := mkSS AF_descriptors_get sr_atoms (dg_rs0 nv w) None (dg_facts0 lo hi).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition dg_E0 (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 n]).

Lemma dg_E0_reg : forall regs n m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (dg_E0 regs n) m = getr regs r.
Proof.
intros regs n m r Hm. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold dg_E0. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm.
Qed.
Lemma dg_E0_32 : forall regs n, ew (dg_E0 regs n) 32 = Z_to_bv 64 SB.
Proof. intros regs n. unfold dg_E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma dg_E0_33 : forall regs n, ew (dg_E0 regs n) 33 = Z_to_bv 64 n.
Proof. intros regs n. unfold dg_E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
(* the walk from the join (descriptors_get_s3.v's dg_walkJ_stmt): this file's one interface *)
Hypothesis DGJ : dg_walkJ_stmt B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.

Lemma dg_grec_val : VAL DG_GREC = A_G_REC.
Proof. unfold DG_GREC. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma dg_spill_val : VAL DG_SPILL = A_REC_SPILL.
Proof. unfold DG_SPILL. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* the entry state *)
Lemma dg_entry_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem ly S md (n : Z) nv w lo hi,
AR SEGS B ly S W mem md ->
astk_ok DESCRIPTORS_GET_STK ly (spZ regs) ->
(forall a, spZ regs - DESCRIPTORS_GET_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n -> 0 <= n <= 16 -> lo <= n <= hi ->
sv_denot (dg_E0 regs n) nv = Z_to_bv 64 n -> 0 <= w <= 4 -> regions_wf (dg_rs0 nv w) = true ->
st_ok_pi SEGS VAL (dg_E0 regs n) (ss_dg0 nv w lo hi)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_descriptors_get)) mem (seg_rom SEGS)))
/\ sh_ok SEGS dg_Bx0 [] (dg_E0 regs n) (mrestrict (w_H W) mem).
Proof.
intros W regs mem ly S md n nv w lo hi HAR Hstk Hpres HNC Hn Hlh HV Hw Hwf.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : 48 <= DESCRIPTORS_GET_STK) by (vm_compute; discriminate).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as HO0. pose proof (pa_obj_img 12%nat ltac:(lia)) as HO12.
pose proof (pal_got_cell B TL) as Hgc.
set (E := dg_E0 regs n) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, dg_E0; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2) by exact (dg_E0_reg regs n 2 2%bv eq_refl).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (dg_E0_32 regs n).
assert (E33 : ew E 33 = Z_to_bv 64 n) by exact (dg_E0_33 regs n).
assert (V0 : VAL (A_OBJ 0) = 0xa63f0) by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (V12 : VAL (A_OBJ 12) = 0xb10b8) by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (EG : ew E DG_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E DG_GREC HEI ltac:(unfold DG_GREC, A_OBJ, A_TEXT, A_LIM; lia)), dg_grec_val; reflexivity).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (rewrite (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); reflexivity).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (rewrite (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
split; [| unfold sh_ok; apply Forall_nil].
unfold ss_dg0. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold E, dg_E0. apply regs_ok_Eimg_Ereg.
- exact Hwf.
- unfold dg_rs0, stack_region, got_regionP, bcell_regionP, dg_ncallsR.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
    constructor.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 dg_Bx0 SB);
    [cbn [sv_denot dg_Bx0]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB DG_GREC A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|].
      apply recb_grec_in. unfold OFF_NCALLS, REC_SIZE in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 nv n); [exact HV | zside | zside |].
    exact (val_mem_view SEGS (w_H W) mem _ 4 n HNC).
- apply pairwise_disjoint_of_extents.
  unfold dg_rs0, stack_region, got_regionP, bcell_regionP, dg_ncallsR, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB DG_GREC A_G_REC EG) by (unfold A_G_REC; lia).
  cbn [base_val]. rewrite Usp, V0, V12.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, OFF_NCALLS in *.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [dg_facts0 f_atoms atoms_ok].
  split; [|split; [|split; [|split; [|exact I]]]].
  + assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite <- Usp, Z_to_bv_bv_unsigned; reflexivity).
    apply (dg_afact E 2%nat (spZ regs)); [exact E2' | lia | lia | change (2 ^ 4) with 16; exact Hal16 | lia].
  + apply (dg_afact E 32%nat SB); [exact E32 | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
  + apply (dg_afact E 33%nat n); [exact E33 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
  + apply (dg_afact E DG_GREC A_G_REC);
    [exact EG | unfold A_G_REC; lia | lia | change (2 ^ 3) with 8; unfold A_G_REC; reflexivity | lia].
Qed.

Ltac dg_fold_md :=
repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?mt ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) mt m) in *; clearbody mdv end.

(* a register's symbolic value without normalising its denotation *)
Ltac dg_preg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

(* the frame membership of the six saved registers, for a region read off a symbolic state *)
Ltac dg_frame_in :=
let j := fresh "j" in let r := fresh "r" in let Hj := fresh "Hj" in
intros j r Hj; unfold dg_saved in Hj;
do 6 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn; tauto|]); destruct j; cbn in Hj; discriminate Hj.

Lemma dg_sig_rcf : SIG CS_rec_calls_free = BASE + AF_rec_calls_free.
Proof. rewrite (SIGP CS_rec_calls_free ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.

(* the slot the table arm computes: g_rec + 16 + 56 * ncalls, as the symbolic executor writes it *)
Lemma dg_den_slot : forall E m g n,
ew E m = Z_to_bv 64 n -> 0 <= n <= 16 -> ew E g = Z_to_bv 64 A_G_REC ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff m 0) (SLit 56)) (SLit 16)) (SOff g 0))
= Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * n).
Proof.
intros E m g n Hm Hn Hg.
assert (ZC : forall x, 0 <= x < 2 ^ 64 -> zcanon x = x)
  by (intros x Hx; unfold zcanon, M64; apply Z.mod_small; lia).
assert (Hmul : U E (SMd M_MUL (SOff m 0) (SLit 56)) = 56 * n).
{ change (SMd M_MUL (SOff m 0) (SLit 56)) with (mono m 56).
  rewrite mono_sound, Hm, unsigned_lit_small by lia. unfold M64. apply Z.mod_small. lia. }
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff m 0) (SLit 56)) (SLit 16)) (SOff g 0))
        = A_G_REC + OFF_CALLS + CALL_SIZE * n).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite Hmul, U_SLit, U_SOff, Hg, unsigned_lit_small by (unfold A_G_REC; lia).
assert (Z16 : zcanon 16 = 16) by (apply ZC; lia).
assert (ZG : zcanon (A_G_REC + 0) = A_G_REC) by (apply ZC; unfold A_G_REC; lia).
rewrite Z16, ZG.
assert (Z1 : zcanon (56 * n + 16) = 56 * n + 16) by (apply ZC; lia).
rewrite Z1.
assert (Z2 : zcanon (56 * n + 16 + A_G_REC) = 56 * n + 16 + A_G_REC) by (apply ZC; unfold A_G_REC; lia).
rewrite Z2. unfold A_G_REC, OFF_CALLS, CALL_SIZE. lia.
Qed.

(* the caller's saved registers, read off the frame region of a symbolic state *)
Lemma dg_frame_of_region : forall E (H : word -> bool) (mem : word -> option byte) sp0 (regs : bvmap 5 word) cs,
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 cs) ->
bv_unsigned (ew E 2) = sp0 ->
(forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr regs rr) ->
(forall j r, nth_error dg_saved j = Some r ->
   In (YP09.mkChunk (- 8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
dg_frame_ok (aview SEGS H mem) sp0 regs.
Proof.
intros E H mem sp0 regs cs HR Hsp HE HIn j r Hj.
assert (Hr32 : 0 <= r < 32).
{ assert (HF : Forall (fun x => 0 <= x < 32) dg_saved) by (unfold dg_saved; repeat constructor; lia).
  rewrite Forall_forall in HF. apply HF. eapply nth_error_In. exact Hj. }
assert (Hr5 : Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r)).
{ rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. symmetry. apply Z.mod_small. lia. }
apply (aval_mem_view SEGS H mem).
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (- 8 - 8 * Z.of_nat j)) by lia.
change 8%nat with (N.to_nat 8).
apply (field_of_region E (mrestrict H mem) 2%nat sp0 cs (-48) 0 (-48) 0 (- 8 - 8 * Z.of_nat j) 8
  (SOff (Z.to_nat r) 0) _ HR Hsp (HIn j r Hj)).
- cbn [sv_denot]. rewrite (HE (Z.to_nat r) (Z_to_bv 5 r) Hr5), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. cbn. lia.
- cbn. lia.
Qed.

Lemma dg_frame_ok_kept : forall (rd rd' : reader) sp0 regs, dg_frame_ok rd sp0 regs ->
(forall a, sp0 - 48 <= a < sp0 -> rd' a = rd a) -> dg_frame_ok rd' sp0 regs.
Proof.
intros rd rd' sp0 regs H Hk j r Hj k Hk8.
assert (Hj6 : (j < 6)%nat) by (change 6%nat with (length dg_saved); apply nth_error_Some; rewrite Hj; discriminate).
rewrite Hk by lia. exact (H j r Hj k Hk8).
Qed.

(* a byte of a live block: below the allocator's ceiling, not an image byte *)
Lemma dg_blk_req : forall ly S (W : world SEGS) mem md q k a, AR SEGS B ly S W mem md -> In (q, k) (ablocks B ly S) ->
q <= a < q + req_size k -> 4096 <= a < alloc_ceiling /\ ~ in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Proof.
intros ly S W mem md q k a HAR Hin Ha.
destruct (al_blocks _ _ LAWS ly S W mem md q k HAR Hin) as (_ & H4096 & Hc & _).
pose proof (recb_heap_noimg_m B ly S W mem md q k a HAR Hin Ha) as Hni.
split; [lia|]. split; [exact Hni|]. intros HP. exact (Hni (cmd_prog_img a HP)).
Qed.
Lemma dg_blk_byte : forall ly S (W : world SEGS) mem md q k a, AR SEGS B ly S W mem md -> In (q, k) (ablocks B ly S) ->
q <= a < q + k -> 4096 <= a < alloc_ceiling /\ ~ in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Proof.
intros ly S W mem md q k a HAR Hin Ha.
destruct (al_blocks _ _ LAWS ly S W mem md q k HAR Hin) as (_ & _ & _ & _ & _ & _ & Hk).
pose proof (req_size_pos k ltac:(lia)) as [_ Hr].
apply (dg_blk_req ly S W mem md q k a HAR Hin). lia.
Qed.

(* the block holding the string argument is none of the owner's blocks (the statement's Forall iv_apart premise) *)
Lemma dg_str_notO : forall (O : list (Z * Z)) p n q k, 0 < n ->
Forall (fun qk => iv_apart p n (fst qk) (snd qk)) O -> q <= p -> p + n <= q + k -> ~ In (q, k) O.
Proof.
intros O p n q k Hn HF Hq1 Hq2 HO. rewrite Forall_forall in HF. specialize (HF (q, k) HO).
unfold iv_apart in HF. cbn [fst snd] in HF. lia.
Qed.

(* the string argument at a later state of the walk: its block is still live and its bytes are kept *)
Lemma dg_strJ : forall ly S (W : world SEGS) mem lyc Sc (Wc : world SEGS) memc p x,
in_blockA (ablocks B ly S) p (Z.of_nat (length x) + 1) -> astr_atR (rdW W mem) p x ->
Z.of_nat (length x) + 1 <= LMAX + 1 ->
(forall q k, In (q, k) (ablocks B ly S) -> q <= p -> p + (Z.of_nat (length x) + 1) <= q + k ->
   In (q, k) (ablocks B lyc Sc) /\
   forall i, 0 <= i < Z.of_nat (length x) + 1 -> rdW Wc memc (p + i) = rdW W mem (p + i)) ->
dg_str_atJ B lyc Sc Wc memc p (Some x).
Proof.
intros ly S W mem lyc Sc Wc memc p x (q & k & Hin & Hq1 & Hq2) Hs Hl HK.
destruct (HK q k Hin Hq1 Hq2) as [Hin' Heq].
exists x. split; [reflexivity|]. split; [exists q, k; split; [exact Hin' | lia]|].
split; [exact (rastr_kept (rdW W mem) (rdW Wc memc) p x Hs Heq) | exact Hl].
Qed.

(* the recorder's representation over a reader that agrees on g_rec, record.spill and the recorder's blocks *)
Lemma dg_arep_agree : forall bl (rd rd' : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
arep_at bl rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl rd rd' R Q HA Hg Hb.
assert (Hgr : rd_agree rd rd' A_G_REC REC_SIZE) by (intros i Hi; apply Hg; left; lia).
pose proof HA as (Hg8 & Hs8 & Hap & HC & HAn & HR & HSC & HOWN).
pose proof HSC as (_ & _ & Vnr & _ & _ & _ & _ & Rnr & _ & _).
assert (HRe : areply_at bl rd' A_G_REC (r_reply R) (l_reply Q)).
{ unfold areply_at in *. destruct (r_reply R) as [x|] eqn:Ey, (l_reply Q) as [pn|] eqn:Eq; try contradiction.
  - destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    assert (Hpn : In pn (lay_blocks Q))
      by (unfold lay_blocks; rewrite Eq; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    split; [apply (aval_mem_agree_in rd rd' A_G_REC REC_SIZE); [exact A1 | exact Hgr | unfold OFF_REPLY; lia | unfold OFF_REPLY, REC_SIZE; cbn; lia]|].
    split; [apply (aval_mem_agree_in rd rd' A_G_REC REC_SIZE); [exact A2 | exact Hgr | unfold OFF_REPLY_SIZE; lia | unfold OFF_REPLY_SIZE, REC_SIZE; cbn; lia]|].
    split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
    split; [|exact A8]. apply (rabytes_kept rd); [exact A7|]. intros i Hi. apply (Hb pn i Hpn). lia.
  - destruct HR as [A1 A2].
    split; apply (aval_mem_agree_in rd rd' A_G_REC REC_SIZE);
    first [exact A1 | exact A2 | exact Hgr | unfold OFF_REPLY, OFF_REPLY_SIZE, REC_SIZE; cbn; lia]. }
assert (Hnew : forall pn, l_reply Q = Some pn -> iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\
  iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE /\ ~ In (fst pn) (map fst (lay_rest Q))).
{ intros pn Hq. destruct HOWN as [HND Hap2].
  assert (Hpn : In pn (lay_blocks Q)) by (rewrite lay_blocks_rest, Hq; apply in_or_app; right; left; reflexivity).
  destruct (Hap2 pn Hpn) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
  intros Hin. rewrite lay_blocks_rest, Hq in HND. apply NoDup_ListNoDup in HND. rewrite map_app in HND.
  exact (list_nodup_app_disj _ _ (fst pn) HND Hin (or_introl eq_refl)). }
assert (Hrest : forall pn, In pn (lay_rest Q) -> In pn bl /\ rd_agree rd rd' (fst pn) (snd pn)).
{ intros pn Hpn. assert (Hpl : In pn (lay_blocks Q)) by (rewrite lay_blocks_rest; apply in_or_app; left; exact Hpn).
  split; [exact (lay_blocks_in _ _ _ _ _ _ HA pn Hpl) | intros i Hi; exact (Hb pn i Hpl Hi)]. }
pose proof (arep_at_set_reply bl bl rd rd' R Q (r_nreplies R) (r_reply R) (l_reply Q) HA
  ltac:(apply (rd_agree_sub rd rd' A_G_REC REC_SIZE); [exact Hgr | lia | unfold OFF_NREPLIES, REC_SIZE; lia])
  ltac:(apply (rd_agree_sub rd rd' A_G_REC REC_SIZE); [exact Hgr | unfold OFF_STATE; lia | unfold OFF_STATE, REC_SIZE; lia])
  ltac:(intros i Hi; apply Hg; right; lia)
  Hrest
  ltac:(apply (aval_mem_agree_in rd rd' A_G_REC REC_SIZE); [exact Vnr | exact Hgr | unfold OFF_NREPLIES; lia | unfold OFF_NREPLIES, REC_SIZE; cbn; lia])
  Rnr HRe Hnew) as H.
destruct R, Q. exact H.
Qed.

(* the footprint of rec_calls_free(record.spill, 1): the spill's nargs field and its argument blocks *)
Lemma dg_rcf_cases : forall P a, inFP (rcf_fp A_REC_SPILL [P]) a ->
(A_REC_SPILL + CALL_OFF_NARGS <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) \/
exists b m, In (b, m) P /\ b <= a < b + req_size m.
Proof.
intros P a (r & Hr & Ha). unfold rcf_fp in Hr. cbn [length seq map] in Hr. apply in_app_or in Hr as [Hr | Hr].
- left. destruct Hr as [<- | []]. cbn [fst snd] in Ha. unfold CALL_SIZE in Ha. lia.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b m] & <- & Hin). cbn [fst snd] in Ha.
  cbn [concat] in Hin. rewrite app_nil_r in Hin. exists b, m. split; [exact Hin | lia].
Qed.

Lemma dg_rcf_low : forall ly S (W : world SEGS) mem md P a, AR SEGS B ly S W mem md ->
(forall pn, In pn P -> In pn (ablocks B ly S)) -> inFP (rcf_fp A_REC_SPILL [P]) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md P a HAR HP Hf. pose proof asan_consts as (C1 & _).
destruct (dg_rcf_cases P a Hf) as [Ha | (b & m & Hin & Ha)].
- unfold A_REC_SPILL, CALL_OFF_NARGS in Ha. lia.
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR (HP _ Hin)) as (_ & _ & Hc & _). lia.
Qed.

Lemma dg_notin_rcf : forall ly S (W : world SEGS) mem md P q k a, AR SEGS B ly S W mem md ->
(forall pn, In pn P -> In pn (ablocks B ly S)) -> In (q, k) (ablocks B ly S) -> ~ In (q, k) P ->
q <= a < q + req_size k -> ~ inFP (rcf_fp A_REC_SPILL [P]) a.
Proof.
intros ly S W mem md P q k a HAR HP Hin Hn Ha Hf.
destruct (dg_rcf_cases P a Hf) as [Hs | (b & m & Hbm & Hb)].
- apply (recb_heap_noimg_m B ly S W mem md q k a HAR Hin Ha). apply cmd_prog_img. apply recb_spill_in.
  unfold CALL_OFF_NARGS, SC_SIZE in *. lia.
- assert (Hne : (b, m) <> (q, k)) by (intros E; apply Hn; rewrite <- E; exact Hbm).
  pose proof (sep_blocks SEGS B LAWS ly S W mem md b m q k HAR (HP _ Hbm) Hin Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* rec_calls_free's post (rec_calls_free_c.v:94-115) *)
Definition dg_rcf_post (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (c : Z)
  (ps : list (list (Z * Z))) : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 Permutation (ablocks B ly S) (ablocks B ly' S' ++ concat ps) /\
 (forall i, (i < length ps)%nat -> aval_mem (rdW W' mem') (c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 0) /\
 (forall j, 0 <= j < CALL_SIZE * Z.of_nat (length ps) -> ~ PRcf.nargs_field c (length ps) (c + j) ->
    rdW W' mem' (c + j) = rdW W mem (c + j)) /\
 (forall p n i, In (p, n) (ablocks B ly' S') -> 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
 (forall R Q, arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
    c = A_G_REC + OFF_CALLS -> ps = l_calls Q ->
    rec_repA B ly' S' (rdW W' mem') (set_calls R (rcf_cleared (r_calls R)))
      (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q))) /\
 (forall R Q, arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
    c = A_REC_SPILL -> ps = [l_spill Q] ->
    rec_repA B ly' S' (rdW W' mem') (set_spill R (fst (r_spill R), []))
      (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q))) /\
 (forall R O, rec_repA B ly S (rdW W mem) R O ->
    iv_apart c (CALL_SIZE * Z.of_nat (length ps)) A_G_REC REC_SIZE ->
    iv_apart c (CALL_SIZE * Z.of_nat (length ps)) A_REC_SPILL SC_SIZE ->
    (forall pn, In pn (concat ps) -> ~ In pn O) ->
    rec_repA B ly' S' (rdW W' mem') R O) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_REC_CALLS_FREE /\
 mo_le MT S S' (XM_REC_CALLS_FREE MT ps).

(* the setup both arms share: the entry facts, the recorder at the entry, the journal's start *)
Ltac dg_setup :=
intros ly S W regs mem md ch pu uri R O HPRE HFRM HROD H10 Hpu HSTR HREP HFR8 HEV HLV HMOK Harm;
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof pa_B_ok as HBASE; pose proof pa_base_lo as HBLO;
assert (HTS : DESCRIPTORS_GET_STK = 16592) by (vm_compute; reflexivity);
pose proof HREP as (Q & HAQ & HOQ);
pose proof HAQ as (Hg8 & Hs8 & Hap & HC & HANS & HRPL & HSCAL & HOWN);
pose proof HC as (HL16 & HLQ & HNC & HCALLS & HSPILL & HSPLEN);
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S))
  by (intros pn Hpn; exact (lay_blocks_in _ _ _ _ _ _ HAQ pn (proj1 (HOQ pn) Hpn)));
destruct HSTR as (x & -> & XB & XS & XL & XO);
pose proof (ajournal_init SEGS B DESCRIPTORS_GET_STK (dg_FP O) ly S W regs mem md ch HPRE) as HJ.

(* the regions' windows of a run, as a predicate on addresses *)
Ltac dg_wins Usp EGu :=
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin];
  [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?EGu in Hrr; unfold OFF_NCALLS, A_G_REC in *;
   first [left; lia | right; lia]|]); destruct Hin.

(* --- record()'s table arm: the call takes the slot g_rec.calls[ncalls] ------------------------------------- *)
Lemma dg_slot_arm : forall ly S W (regs : bvmap 5 word) mem md ch (pu : Z) (uri : option (list byte)) (R : rstate)
  (O : list (Z * Z)),
afn_pre SEGS B DESCRIPTORS_GET_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 pu -> 0 <= pu < 2 ^ 64 ->
(exists x, uri = Some x /\
 in_blockA (ablocks B ly S) pu (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pu x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pu (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O) ->
rec_repA B ly S (rdW W mem) R O ->
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_DESCRIPTORS_GET R <= EV_MAX -> blocks_bytes S + LIVE_DESCRIPTORS_GET R uri <= LIVE_MAX ->
mo_ok MT S (XM_DESCRIPTORS_GET MT R uri) ->
(length (r_calls R) < 16)%nat ->
SRr SEGS W (cfg_at SEGS (BASE + AF_descriptors_get) regs mem md)
(apost_baseF SEGS B DESCRIPTORS_GET_STK (dg_FP O) regs ly S W mem md (EV_DESCRIPTORS_GET R) (dg_post B MT ly S R O uri)).
Proof.
dg_setup.
destruct (dg_entry_seed W regs mem ly S md (Z.of_nat (length (r_calls R))) (SOff 33 0) 4 0 15 HAR Hstk Hpres HNC
  ltac:(lia) ltac:(lia) ltac:(cbn [sv_denot]; rewrite dg_E0_33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(lia) ltac:(vm_compute; reflexivity)) as [HS SHOK].
remember (Z.of_nat (length (r_calls R))) as n eqn:Hn_def.
assert (Hn : 0 <= n <= 15) by lia.
set (E := dg_E0 regs n) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, dg_E0; apply Eimg_env).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
  by (intros m r Hm; exact (dg_E0_reg regs n m r Hm)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (dg_E0_32 regs n).
assert (E33 : ew E 33 = Z_to_bv 64 n) by exact (dg_E0_33 regs n).
assert (EGz : ew E DG_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E DG_GREC HEI ltac:(unfold DG_GREC, A_OBJ, A_TEXT, A_LIM; lia)), dg_grec_val; reflexivity).
assert (EGu : bv_unsigned (ew E DG_GREC) = A_G_REC) by (rewrite EGz; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (EG285 : bv_unsigned (ew E 285%nat) = A_G_REC) by exact EGu.
unfold cfg_at, w64.
(* 0x8cfa0 .. 0x8d014: the prologue, the call count, the table arm's count + 1 and slot *)
paj_run_to_tok RUNTO HS HJ SHOK dg_Bspan DG_J.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | rewrite HTS; cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact EGu | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply (dg_awr_grec B HB cmd_prog_img). unfold OFF_NCALLS, REC_SIZE in *. lia. }
dg_fold_md.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => spZ regs - 48 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr
  ltac:(dg_wins Usp EG285)) as UN.
clear HF HFr HG.
pmkst HS.
prreg HS (2%bv : bv 5) P2. dg_preg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (19%bv : bv 5) P19.
prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
pose proof (regs_kept_of_st_ok_pi E _ _ regs [Z_to_bv 64 SB; Z_to_bv 64 n]
  (map (Z_to_bv 5) [18; 20; 21; 22; 23; 24; 25; 26; 27]) HS
  ltac:(split; [intros m Hm; unfold E, dg_E0; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
               | reflexivity])
  ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict] in HKR.
assert (R2 : getr (ms_regs ms) 2 = w64 (spZ regs - 48)) by (rewrite P2, Usp; unfold w64; f_equal; lia).
assert (R3 : getr (ms_regs ms) 3 = getr regs 3) by (rewrite P3; exact (EE 3%nat 3%bv eq_refl)).
assert (R4 : getr (ms_regs ms) 4 = getr regs 4) by (rewrite P4; exact (EE 4%nat 4%bv eq_refl)).
assert (R8 : getr (ms_regs ms) 8 = w64 (A_G_REC + OFF_CALLS + CALL_SIZE * n))
  by (rewrite P8; exact (dg_den_slot E 33 DG_GREC n E33 ltac:(lia) EGz)).
assert (R9 : getr (ms_regs ms) 9 = w64 pu) by (rewrite P9, (EE 10%nat 10%bv eq_refl); exact H10).
assert (R19 : getr (ms_regs ms) 19 = w64 SB) by (rewrite P19, E32; reflexivity).
assert (Rhi : forall r, (r = 18 \/ 20 <= r <= 27) -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
  by (intros r Hr; apply HKR; apply in_map; cbn; lia).
(* the frame and g_rec.ncalls at the join *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRg end.
cbn [ms_mem restrict mkst] in HR0, HRg.
pose proof (dg_frame_of_region E (w_H W) (ms_mem ms) (spZ regs) regs _ HR0 Usp EE ltac:(dg_frame_in)) as HFRJ.
pose proof (field_of_region E _ DG_GREC A_G_REC _ _ _ _ _ 8 4 (SOff 33 1) (n + 1) HRg EGu ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnc.
assert (HJc := HJ).
eapply (DGJ ly S W regs mem md ch pu (Some x) R O ly S W (ms_regs ms) (ms_mem ms) mdv 0 (A_G_REC + OFF_CALLS + CALL_SIZE * n));
[ exact HPRE | exact HFRM | exact HROD | exact Hpu | exact HOin | exact HFR8 | exact HEV | exact HLV | exact HMOK
| exact HJc | | | | exact HFRJ | | | ].
- unfold rec_spill_frees. destruct (Nat.ltb (length (r_calls R)) 16); lia.
- unfold rec_spill_frees. rewrite (proj2 (Nat.ltb_lt _ _) Harm), Z.mul_0_l. exact (mo_le_refl MT MTL S).
- unfold dg_regs_ok. repeat split; first [exact R2 | exact R3 | exact R4 | exact R8 | exact R9 | exact R19 | exact Rhi].
- left. unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE. split; [lia|]. split; [lia|].
  replace (6174528 + 16 + 56 * n) with (8 * (771818 + 7 * n)) by lia. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
- apply (dg_strJ ly S W mem ly S W (ms_mem ms) pu x XB XS XL).
  intros q k Hin Hq1 Hq2. split; [exact Hin|]. intros i Hi.
  destruct (dg_blk_byte ly S W mem md q k (pu + i) HAR Hin ltac:(lia)) as (Hb1 & Hb2 & _).
  apply UN; [lia|]. intros [Hf | Hf]; [lia|].
  apply Hb2. apply cmd_prog_img. apply recb_grec_in. unfold OFF_NCALLS, REC_SIZE in *. lia.
- exists [], (ablocks B ly S), (rdW W mem), R, Q.
  split; [exact HAQ|]. split; [reflexivity|]. split; [left; split; [exact Harm | rewrite Hn_def; reflexivity]|].
  split.
  { rewrite (rec_record_calls R _ _ Harm). cbn [r_calls set_calls]. rewrite length_app. cbn [length].
    rewrite Nat2Z.inj_add, <- Hn_def. change (Z.of_nat 1) with 1. exact (aval_mem_view SEGS _ _ _ _ _ Vnc). }
  split.
  { intros a Ha Hna. apply UN; [unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia|].
    intros [Hf | Hf]; [unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia | exact (Hna Hf)]. }
  split.
  { intros [b m] Hpn. pose proof (lay_blocks_in _ _ _ _ _ _ HAQ _ Hpn) as Hin. split; [exact Hin|].
    intros i Hi. cbn [fst snd] in *.
    destruct (dg_blk_byte ly S W mem md b m (b + i) HAR Hin ltac:(lia)) as (Hb1 & Hb2 & _).
    apply UN; [lia|]. intros [Hf | Hf]; [lia|].
    apply Hb2. apply cmd_prog_img. apply recb_grec_in. unfold OFF_NCALLS, REC_SIZE in *. lia. }
  split; [intros pn Hpn; apply HOQ; exact Hpn|].
  split; [rewrite app_nil_r; apply Permutation_refl|].
  split; [intros pn []|].
  split; [intros pn Hpn _; apply HOQ; exact Hpn|].
  intros Hne. exfalso. exact (Hne eq_refl).
Qed.

(* --- record()'s spill arm: the table holds 16 calls; the spill's arguments are freed --------------------- *)
Lemma dg_spill_arm : forall ly S W (regs : bvmap 5 word) mem md ch (pu : Z) (uri : option (list byte)) (R : rstate)
  (O : list (Z * Z)),
afn_pre SEGS B DESCRIPTORS_GET_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 pu -> 0 <= pu < 2 ^ 64 ->
(exists x, uri = Some x /\
 in_blockA (ablocks B ly S) pu (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pu x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pu (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O) ->
rec_repA B ly S (rdW W mem) R O ->
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_DESCRIPTORS_GET R <= EV_MAX -> blocks_bytes S + LIVE_DESCRIPTORS_GET R uri <= LIVE_MAX ->
mo_ok MT S (XM_DESCRIPTORS_GET MT R uri) ->
length (r_calls R) = 16%nat ->
SRr SEGS W (cfg_at SEGS (BASE + AF_descriptors_get) regs mem md)
(apost_baseF SEGS B DESCRIPTORS_GET_STK (dg_FP O) regs ly S W mem md (EV_DESCRIPTORS_GET R) (dg_post B MT ly S R O uri)).
Proof.
dg_setup.
assert (H16z : Z.of_nat (length (r_calls R)) = 16) by (rewrite Harm; reflexivity).
rewrite H16z in HNC.
assert (HLT : Nat.ltb (length (r_calls R)) 16 = false) by (rewrite Harm; reflexivity).
assert (HPsp : forall pn, In pn (l_spill Q) -> In pn (ablocks B ly S)).
{ intros pn Hpn. apply (lay_blocks_in _ _ _ _ _ _ HAQ). unfold lay_blocks.
  apply in_or_app; right; apply in_or_app; left; exact Hpn. }
destruct (dg_entry_seed W regs mem ly S md 16 (SLit 16) 0 16 16 HAR Hstk Hpres HNC ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(lia) ltac:(vm_compute; reflexivity)) as [HS SHOK].
set (E := dg_E0 regs 16) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, dg_E0; apply Eimg_env).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
  by (intros m r Hm; exact (dg_E0_reg regs 16 m r Hm)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (dg_E0_32 regs 16).
assert (ES : ew E 292 = Z_to_bv 64 A_REC_SPILL).
{ change 292%nat with DG_SPILL.
  rewrite (img_env_atomP E DG_SPILL HEI ltac:(unfold DG_SPILL, A_OBJ, A_TEXT, A_LIM; lia)), dg_spill_val. reflexivity. }
assert (EGu : bv_unsigned (ew E DG_GREC) = A_G_REC).
{ rewrite (img_env_atomP E DG_GREC HEI ltac:(unfold DG_GREC, A_OBJ, A_TEXT, A_LIM; lia)), dg_grec_val.
  apply unsigned_lit_small. unfold A_G_REC. lia. }
assert (EG285 : bv_unsigned (ew E 285%nat) = A_G_REC) by exact EGu.
unfold cfg_at, w64.
(* 0x8cfa0 .. 0x8cff0: the prologue, the call count 16, s0 := record.spill, the call of rec_calls_free *)
paj_run_tok RUN HS HJ SHOK dg_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | rewrite HTS; cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_nil. }
dg_fold_md.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => spZ regs - 48 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS) HFr
  ltac:(dg_wins Usp EG285)) as UN1.
clear HF HFr HG.
pose proof (proj1 HJ) as HARc.
rename ms into msc.
(* the frame at the call *)
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth E ssx (restrict (w_H W) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
cbn [ms_mem restrict mkst] in HR0.
pose proof (dg_frame_of_region E (w_H W) (ms_mem msc) (spZ regs) regs _ HR0 Usp EE ltac:(dg_frame_in)) as HFRc.
(* the recorder at the call: the run wrote the frame only *)
assert (HAQc : arep_at (ablocks B ly S) (rdW W (ms_mem msc)) A_G_REC A_REC_SPILL R Q).
{ apply (dg_arep_agree _ (rdW W mem)); [exact HAQ | |].
  - intros a Ha. unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. apply UN1; cbv beta; unfold A_G_REC, OFF_NCALLS; lia.
  - intros [b m] i Hpn Hi. cbn [fst snd] in *. pose proof (lay_blocks_in _ _ _ _ _ _ HAQ _ Hpn) as Hin.
    destruct (dg_blk_byte ly S W mem md b m (b + i) HAR Hin ltac:(lia)) as (Hb1 & _ & _).
    apply UN1; cbv beta; lia. }
pose proof HAQc as (_ & _ & _ & (_ & _ & _ & _ & HSPc & _) & _).
pose proof HSPc as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (Rsp : spZ (ms_regs msc) = spZ regs + -48) by (unfold spZ at 1; rewrite Q2, Usp, unsigned_lit_small by lia; lia).
assert (R3 : getr (ms_regs msc) 3 = w64 (as_gp B)) by (rewrite Q3, (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (R4 : getr (ms_regs msc) 4 = w64 (as_tp B)) by (rewrite Q4, (EE 4%nat 4%bv eq_refl); exact Htp).
assert (R10 : getr (ms_regs msc) 10 = w64 A_REC_SPILL) by (rewrite Q10, ES; reflexivity).
assert (R11 : getr (ms_regs msc) 11 = w64 (Z.of_nat (length [l_spill Q]))) by (rewrite Q11; reflexivity).
assert (R8 : s0Z (ms_regs msc) = A_REC_SPILL) by (unfold s0Z; rewrite Q8, ES; apply unsigned_lit_small; unfold A_REC_SPILL; lia).
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W (ms_mem msc)))
  by exact (dg_aro_at B RRO RELRO_IMG cmd_ro_prog_apart ly S W mem md ly S W (ms_mem msc) mdv O 0 (spZ regs)
    HJ HAR HOin HROD).
(* the call rec_calls_free(record.spill, 1) *)
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs msc) (ms_mem msc) _ DESCRIPTORS_GET_STK (spZ regs) (dg_FP O) ly S W mem md []
    ly S mdv 0 REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [l_spill Q]) (EV_REC_CALLS_FREE [l_spill Q]) (-48)
    (getr (ms_regs msc) 1) [] (dg_rcf_post ly S W (ms_mem msc) A_REC_SPILL [l_spill Q]) HJ Rsp).
  - reflexivity.
  - lia.
  - unfold REC_CALLS_FREE_STK, ASTACK. lia.
  - rewrite HTS. unfold REC_CALLS_FREE_STK, ASTACK. lia.
  - exact R3.
  - exact R4.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity].
  - rewrite Q1, unsigned_lit_small by lia. lia.
  - apply achain_low. rewrite R8. unfold A_REC_SPILL. lia.
  - intros HPRE1. rewrite dg_sig_rcf. eapply SRr_mono.
    + eapply (TRCF fx ly S W (ms_regs msc) (ms_mem msc) mdv [] A_REC_SPILL [l_spill Q] HPRE1).
      * exact HRODc.
      * exact R10.
      * exact R11.
      * cbn. lia.
      * right; left. unfold CALL_SIZE, SC_SIZE. cbn. lia.
      * unfold A_REC_SPILL. reflexivity.
      * intros i P HiP. destruct i as [|i]; [|destruct i; discriminate HiP].
        cbn in HiP. injection HiP as HP0. subst P.
        split; [rewrite G3; exact G2|].
        split.
        { replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_NARGS) with (A_REC_SPILL + CALL_OFF_NARGS) by (cbn; lia).
          rewrite G3. exact G5. }
        intros a pn Hpn.
        assert (Ha : (a < length (snd (r_spill R)))%nat) by (rewrite <- G3; apply nth_error_Some; rewrite Hpn; discriminate).
        destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Hs; [|apply nth_error_Some in Ha; contradiction].
        destruct (G7 a s pn Hs Hpn) as (V & _ & Hin & _).
        split; [|exact Hin].
        replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_ARGS + 8 * Z.of_nat a)
          with (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat a) by (cbn; lia).
        exact V.
      * cbn [concat]. rewrite app_nil_r. exact G6.
      * pose proof HEV as HEV'. unfold EV_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r, G3.
        unfold EV_DESCRIPTORS_GET, rec_spill_frees in HEV'. rewrite HLT in HEV'.
        unfold EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in HEV'. lia.
      * apply (mo_ok_le MT MTL S _ (XM_DESCRIPTORS_GET MT R (Some x)) HMOK).
        unfold XM_REC_CALLS_FREE, XM_DESCRIPTORS_GET, rec_spill_frees, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
        rewrite HLT. cbn [concat]. rewrite app_nil_r, G3.
        pose proof (mo_free_nonneg MT MTL).
        pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg (Some x))) + 1) ltac:(lia)).
        pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (descriptors_get_m R (Some x)))) + 1) ltac:(lia)).
        lia.
    + cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK3).
      exists ly3, S3, regs3, mem3, md3. split; [reflexivity | split; [exact HJ1 | split; [exact HP | exact HK3]]].
  - intros a Hf. destruct (dg_rcf_cases (l_spill Q) a Hf) as [Hs | (b & m & Hin & Hb)].
    + right; right; right; right; left.
      assert (Hsp : A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) by (unfold CALL_OFF_NARGS, SC_SIZE in *; lia).
      split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split; [right; left; reflexivity | cbn [fst snd]; lia]|].
      split; [rewrite (ts_prog B HB); exact (recb_spill_in a Hsp) | exact (cmd_prog_img a (recb_spill_in a Hsp))].
    + right; left. split; [|exists b, m; split; [exact (HPsp _ Hin) | exact Hb]].
      exists (b, b + req_size m). split; [|cbn [fst snd]; lia].
      right; right. unfold ablocks_fp. apply in_map_iff. exists (b, m). split; [reflexivity|].
      apply HOQ. unfold lay_blocks. apply in_or_app; right; apply in_or_app; left; exact Hin.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Hf Hw Hn. exfalso.
    pose proof (dg_rcf_low ly S W (ms_mem msc) mdv (l_spill Q) a HARc HPsp Hf). lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
pose proof HK2 as (Kperm & Knarg & Ktab & Kblk & Kgrec & Kspill & Kother & Kbb & Kmo).
pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & Kc1 & Kc2 & _).
(* back at 0x8cff4 *)
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rewrite Q1.
remember (havoc E 40 (map (getr regs2) CLOB)) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall m, (m < 40)%nat -> ew E2 m = ew E m) by (intros m Hm; rewrite HE2; apply YN3v.ew_havoc_old; exact Hm).
assert (SHOK2 : sh_ok SEGS dg_Bx0 [] E2 (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
(* 0x8cff4: j 0x8d014 *)
paj_run_to_tok RUNTO HS HJ2 SHOK2 dg_Bspan DG_J.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_nil. }
dg_fold_md.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr
  ltac:(let Hin := fresh "Hin" in intros ? ? ? ? Hin; vm_compute in Hin; destruct Hin)) as UN3.
clear HF HFr HG.
pose proof (proj1 HJ2) as HAR3.
pmkst HS.
prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (19%bv : bv 5) P19.
prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
pose proof (regs_kept_of_st_ok_pi E2 _ _ regs [Z_to_bv 64 SB; Z_to_bv 64 16]
  (map (Z_to_bv 5) [18; 20; 21; 22; 23; 24; 25; 26; 27]) HS
  ltac:(split; [intros m Hm; rewrite OLD2 by lia; unfold E, dg_E0; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
               | rewrite HE2; reflexivity])
  ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict] in HKR.
assert (R2 : getr (ms_regs ms) 2 = w64 (spZ regs - 48)) by (rewrite P2, OLD2, Usp by lia; unfold w64; f_equal; lia).
assert (R3' : getr (ms_regs ms) 3 = getr regs 3) by (rewrite P3, OLD2 by lia; exact (EE 3%nat 3%bv eq_refl)).
assert (R4' : getr (ms_regs ms) 4 = getr regs 4) by (rewrite P4, OLD2 by lia; exact (EE 4%nat 4%bv eq_refl)).
assert (R8' : getr (ms_regs ms) 8 = w64 A_REC_SPILL)
  by (rewrite P8; change 292%nat with DG_SPILL;
      rewrite (img_env_atomP E2 DG_SPILL HEI2 ltac:(unfold DG_SPILL, A_OBJ, A_TEXT, A_LIM; lia)), dg_spill_val; reflexivity).
assert (R9 : getr (ms_regs ms) 9 = w64 pu) by (rewrite P9, OLD2, (EE 10%nat 10%bv eq_refl) by lia; exact H10).
assert (R19 : getr (ms_regs ms) 19 = w64 SB) by (rewrite P19, OLD2, E32 by lia; reflexivity).
assert (Rhi : forall r, (r = 18 \/ 20 <= r <= 27) -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
  by (intros r Hr; apply HKR; apply in_map; cbn; lia).
assert (HKP : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms) a = rdW W2 mem2 a)
  by (intros a Ha; apply UN3; [exact Ha | cbv beta; tauto]).
(* the frame at the join: the run kept it, and rec_calls_free's journal keeps the caller's stack above its own *)
assert (HFRJ : dg_frame_ok (rdW W2 (ms_mem ms)) (spZ regs) regs).
{ apply (dg_frame_ok_kept (rdW W (ms_mem msc)) _ _ _ HFRc). intros a Ha.
  rewrite HKP by lia.
  apply Kc1; [lia | lia |]. intros Hf. pose proof (dg_rcf_low ly S W (ms_mem msc) mdv (l_spill Q) a HARc HPsp Hf). lia. }
(* the recorder after rec_calls_free: the spill cleared, its arguments freed *)
destruct (Kspill R Q HAQc eq_refl eq_refl) as (Qb & HAb & HOb).
assert (HRb16 : length (r_calls (set_spill R (fst (r_spill R), []))) = 16%nat) by exact Harm.
assert (HJc := HJ2).
eapply (DGJ ly S W regs mem md ch pu (Some x) R O ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdv0 (0 + EV_REC_CALLS_FREE [l_spill Q])
  A_REC_SPILL);
[ exact HPRE | exact HFRM | exact HROD | exact Hpu | exact HOin | exact HFR8 | exact HEV | exact HLV | exact HMOK
| exact HJc | | | | exact HFRJ | right; reflexivity | | ].
- unfold EV_REC_CALLS_FREE, rec_spill_frees. rewrite HLT. cbn [concat]. rewrite app_nil_r, G3. lia.
- unfold rec_spill_frees. rewrite HLT. unfold XM_REC_CALLS_FREE in Kmo. cbn [concat] in Kmo. rewrite app_nil_r, G3 in Kmo.
  exact Kmo.
- unfold dg_regs_ok. repeat split; first [exact R2 | exact R3' | exact R4' | exact R8' | exact R9 | exact R19 | exact Rhi].
- apply (dg_strJ ly S W mem ly2 S2 W2 (ms_mem ms) pu x XB XS XL).
  intros q k Hin Hq1 Hq2.
  assert (HnO : ~ In (q, k) O) by exact (dg_str_notO O pu (Z.of_nat (length x) + 1) q k ltac:(lia) XO Hq1 Hq2).
  assert (HnP : ~ In (q, k) (l_spill Q)).
  { intros Hp. apply HnO. apply HOQ. unfold lay_blocks. apply in_or_app; right; apply in_or_app; left; exact Hp. }
  assert (Hin2 : In (q, k) (ablocks B ly2 S2)).
  { pose proof (Permutation_in _ Kperm Hin) as H2. apply in_app_or in H2 as [H2 | H2]; [exact H2|].
    exfalso. apply HnP. cbn [concat] in H2. rewrite app_nil_r in H2. exact H2. }
  split; [exact Hin2|]. intros i Hi.
  destruct (al_blocks _ _ LAWS ly S W mem md q k HAR Hin) as (_ & _ & _ & _ & _ & _ & Hk).
  pose proof (req_size_pos k ltac:(lia)) as [_ Hr].
  destruct (dg_blk_byte ly S W mem md q k (pu + i) HAR Hin ltac:(lia)) as (Hb1 & _ & _).
  rewrite HKP by lia.
  replace (pu + i) with (q + (pu + i - q)) by lia.
  rewrite (Kc2 q k (pu + i - q) Hin Hin2 ltac:(lia)).
  + replace (q + (pu + i - q)) with (pu + i) by lia. apply UN1; cbv beta; lia.
  + replace (q + (pu + i - q)) with (pu + i) by lia.
    exact (dg_notin_rcf ly S W (ms_mem msc) mdv (l_spill Q) q k (pu + i) HARc HPsp Hin HnP ltac:(lia)).
- exists (concat [l_spill Q]), (ablocks B ly2 S2), (rdW W2 mem2), (set_spill R (fst (r_spill R), [])), Qb.
  split; [exact HAb|].
  split; [intros A; rewrite (rec_record_spill _ _ _ HRb16), (rec_record_spill _ _ _ Harm); reflexivity|].
  split.
  { right. split; [exact HRb16|]. split; [reflexivity|].
    pose proof HAb as (_ & _ & _ & (_ & _ & _ & _ & HSPb & _) & _). pose proof HSPb as (_ & _ & L3 & _).
    cbn [r_spill set_spill snd length] in L3. apply length_zero_iff_nil. exact L3. }
  split.
  { rewrite (rec_record_spill _ _ _ HRb16). cbn [r_calls set_spill]. rewrite Harm.
    pose proof HAb as (_ & _ & _ & (_ & _ & Vb & _) & _). cbn [r_calls set_spill] in Vb. rewrite Harm in Vb.
    apply (aval_mem_kept (rdW W2 mem2)); [exact Vb|]. intros k Hk. apply HKP. unfold A_G_REC, OFF_NCALLS. lia. }
  split; [intros a Ha _; apply HKP; unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia|].
  split.
  { intros [b m] Hpn. pose proof (lay_blocks_in _ _ _ _ _ _ HAb _ Hpn) as Hin. split; [exact Hin|].
    intros i Hi. cbn [fst snd] in *.
    destruct (dg_blk_byte ly2 S2 W2 mem2 md2 b m (b + i) (proj1 HJc2) Hin ltac:(lia)) as (Hb1 & _ & _).
    apply HKP. lia. }
  split.
  { intros pn Hpn. apply HOQ. apply (proj2 (HOb pn)) in Hpn. unfold lay_blocks.
    apply in_app_or in Hpn as [H | H]; apply in_or_app; [left; exact H | right; apply in_or_app; right; exact H]. }
  split; [exact Kperm|].
  split.
  { intros pn Hpn. apply HOQ. cbn [concat] in Hpn. rewrite app_nil_r in Hpn. unfold lay_blocks.
    apply in_or_app; right; apply in_or_app; left; exact Hpn. }
  split.
  { intros pn HpnO Hpn2. apply (proj1 (HOb pn)). apply HOQ in HpnO. unfold lay_blocks in HpnO.
    apply in_app_or in HpnO as [H | H]; [apply in_or_app; left; exact H|].
    apply in_app_or in H as [H | H]; [|apply in_or_app; right; exact H].
    exfalso. pose proof (recb_ablocks_nodup_m B ly S W mem md HAR) as ND. apply (Permutation_NoDup Kperm) in ND.
    apply (list_nodup_app_disj _ _ pn ND Hpn2). cbn [concat]. rewrite app_nil_r. exact H. }
  intros _. rewrite Harm. lia.
Qed.

Theorem dg_entry_holds : tdescriptors_get_spec B MT.
Proof.
unfold tdescriptors_get_spec.
intros ly S W regs mem md ch pu uri R O HPRE HFRM HROD HROOK H10 Hpu HSTR HREP HFR8 HEV HLV HMOK.
destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hlt | Hge].
- exact (dg_slot_arm ly S W regs mem md ch pu uri R O HPRE HFRM HROD H10 Hpu HSTR HREP HFR8 HEV HLV HMOK Hlt).
- assert (H16 : length (r_calls R) = 16%nat).
  { destruct HREP as (Q & (_ & _ & _ & (HL & _) & _) & _). lia. }
  exact (dg_spill_arm ly S W regs mem md ch pu uri R O HPRE HFRM HROD H10 Hpu HSTR HREP HFR8 HEV HLV HMOK H16).
Qed.

End e.
End f.
End d.
