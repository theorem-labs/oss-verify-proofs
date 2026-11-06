(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the prologue of sup_call's ASan walk (plugin-hostd/fuzz_command, 0x8a95c ..
   0x8a9cc): the frame, the test of g_rec.ncalls against 16 and record()'s two arms, up to the join 0x8a9d0, where
   the body's statement (sup_call_s3.v's SC_B_stmt) takes over in the state `sc_mid`.

   Pass-4/5 re-fit: rec_calls_free's contract is taken at every FP state and used at the
   entry's fx (its post is apost_base, so the kit rule cl_callS_wide is unchanged). Statement pass 5 removed
   astack_pres, so the walk no longer derives it for rec_calls_free; the frame chain at that call is the empty one
   (s0 holds the line, a heap pointer below alloc_ceiling: achain_low). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaSB PaDenot PaLibG PaLibH PaCall CmdBase CmdRep CmdObj CmdZsh CmdAddr CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_i_c arg_line_c answer_c sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
sup_call_s0 sup_call_s1 sup_call_s2 sup_call_s3 PaNoChain PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase CmdRecCells.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* The entry state of the prologue: sup_call_s1.v's sc_entry with g_rec.ncalls as the atom 33 (an extra of the
   environment, 0 <= n <= 16) in place of the literal, so that the test against 16 splits the run in two. *)
Definition sc_a_extra (n : Z) : list word := map (Z_to_bv 64) [SB; n].
Definition sc_a_E (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs (sc_a_extra n)).
Definition sc_a_ncalls : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) 8 12 8 12 [YP09.mkChunk 8 (CVal 4 (SOff 33 0))].
Definition sc_a_regions : smem := [stack_region 48; got_regionP; bcell_regionP 32; sc_a_ncalls].
(* the atom of g_rec carries its address as a fact, so the ncalls window is known to lie outside the shadow *)
Definition sc_a_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 16 0);
(A_OBJ 44, mkAF A_G_REC A_G_REC 0)] [] [].
Definition sc_a_ss : sstate := mkSS AF_sup_call sr_atoms sc_a_regions None sc_a_facts.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's contract of rec_calls_free, at every FP state (sup_call_c.v:64) *)
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the image's per-binary facts: cif_prog_img _ _ IMG (CmdRecBase.v) and
   PROG_WRITABLE SEGS B LAWS HB PRW (CmdRecCells.v) *)
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis PRW : prog_rw SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma sc_a_obj0 : VAL (A_OBJ 0) = 0xa63f0.
Proof. rewrite (VOBJS 0%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sc_a_obj12 : VAL (A_OBJ 12) = 0xb10b8.
Proof. rewrite (VOBJS 12%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sc_a_obj44 : VAL (A_OBJ 44) = A_G_REC.
Proof. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sc_a_obj51 : VAL (A_OBJ 51) = A_REC_SPILL.
Proof. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* every byte of g_rec, record.spill and g_quitting is one of the program's writable statics (CmdBSyms' ts_prog) *)
Lemma sc_a_prog : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof.
intros a (r & Hin & Hr). rewrite (ts_prog B HB). unfold cmd_PG in Hin. unfold TFIB_PROG_STATIC.
cbn [In] in Hin. unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma sc_a_grec_pg : forall a, A_G_REC <= a < A_G_REC + 960 -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia]. Qed.

(* the ncalls field's window is a footprint byte of the program's statics (awr_byte's program-static case) *)
Lemma sc_a_awr_ncalls : forall E cs rs STK sp0 O bl0 blc fr0 lyc own,
bv_unsigned (ew E (A_OBJ 44)) = A_G_REC ->
awr_ok SEGS B E rs STK sp0 (SC_FP O) bl0 blc fr0 lyc own ->
awr_ok SEGS B E (YP09.mkRegion (Some (A_OBJ 44)) 8 12 8 12 cs :: rs) STK sp0 (SC_FP O) bl0 blc fr0 lyc own.
Proof.
intros E cs rs STK sp0 O bl0 blc fr0 lyc own HU H.
eapply awr_ok_cons_gen; [reflexivity | exact HU | | exact H].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. do 4 right. unfold awr_prog_or_caller. left.
split; [|split; [apply sc_a_prog, sc_a_grec_pg; unfold A_G_REC in *; lia
               | apply (cif_prog_img _ _ IMG), sc_a_grec_pg; unfold A_G_REC in *; lia]].
exists (A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4). split; [left; reflexivity | cbn [fst snd]; unfold OFF_NCALLS; lia].
Qed.

Lemma sc_a_sig_rcf : SIGMA CS_rec_calls_free = BASE + AF_rec_calls_free.
Proof.
rewrite (SIGP CS_rec_calls_free); [reflexivity|].
cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]).
Qed.

(* a 64-bit value in range is its own canonical form *)
Lemma sc_a_zc : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. exact Hz. Qed.

(* a saved register read back out of the frame region of a symbolic state *)
Lemma sc_a_chunk : forall E (W : world SEGS) m (sp0 : Z) cs (od : Z) (k : nat) (rr : bv 5)
(regs0 : bvmap 5 word) (a : Z),
region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 cs) ->
bv_unsigned (ew E 2) = sp0 ->
In (YP09.mkChunk od (CVal 8 (SOff k 0))) cs ->
ew E k = getr regs0 rr -> sp0 + od = a ->
aval_mem (aview SEGS (w_H W) m) a 8 (bv_unsigned (getr regs0 rr)).
Proof.
intros E W m sp0 cs od k rr regs0 a HR Hsp Hin Hk <-.
apply sc_aval_of_val_mem.
exact (field_of_region E (mrestrict (w_H W) m) 2%nat sp0 cs (-48) 0 (-48) 0 od 8%N (SOff k 0)
  (bv_unsigned (getr regs0 rr)) HR Hsp Hin
  ltac:(cbn [sv_denot]; rewrite Hk, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(pose proof (bv_unsigned_in_range 64 (getr regs0 rr)) as HX;
        change (bv_modulus 64) with (2 ^ 64) in HX; cbn; lia)
  ltac:(cbn; lia)).
Qed.

(* The entry state, ncalls as the atom 33 *)
Lemma sc_a_entry : forall W ly S (regs : bvmap 5 word) mem md ch (n : Z),
afn_pre SEGS B SUP_CALL_STK ly S W regs mem md ch ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n -> 0 <= n <= 16 ->
st_ok_pi SEGS VAL (sc_a_E regs n) sc_a_ss
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_call)) mem (seg_rom SEGS)))
/\ sh_ok SEGS sc_Bx sc_SH (sc_a_E regs n) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch n HPRE Hn Hn16.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := sc_a_E regs n). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; unfold sc_a_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; unfold sc_a_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n)
  by (subst E; unfold sc_a_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E240 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold sc_a_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E252 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold sc_a_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E284 : ew E (A_OBJ 44) = Z_to_bv 64 (VAL (A_OBJ 44)))
  by (subst E; unfold sc_a_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof sc_a_obj0 as V0. pose proof sc_a_obj12 as V12. pose proof sc_a_obj44 as V44.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (HW : forall o, 8 <= o < 12 -> writable_at SEGS (mrestrict (w_H W) mem) (A_G_REC + o)).
{ intros o Ho. apply (PROG_WRITABLE SEGS B LAWS HB PRW). apply sc_a_grec_pg. lia. }
assert (CK : YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) A_G_REC (YP09.mkChunk 8 (CVal 4 (SOff 33 0)))).
{ apply (chunk_ok_val SEGS E _ A_G_REC 8 4 (SOff 33 0) n);
  [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
  exact (sc_val_mem_of_aval SEGS (w_H W) mem (A_G_REC + OFF_NCALLS) 4 n Hn). }
assert (RG : forall r, In r [got_regionP; bcell_regionP 32] -> YP09.region_ok SEGS E (mrestrict (w_H W) mem) r).
{ intros r [<- | [<- | []]]; unfold region_ok, got_regionP, bcell_regionP;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  - rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E240) by (rewrite V0; lia). split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E252, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | rewrite V12; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E252) by (rewrite V12; lia). split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 sc_Bx SB);
    [cbn [sv_denot sc_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell). }
assert (WS : 48 <= SUP_CALL_STK) by (vm_compute; intros Hx; discriminate Hx).
assert (RS : YP09.region_ok SEGS E (mrestrict (w_H W) mem) (stack_region 48)).
{ unfold region_ok, stack_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
assert (RN : YP09.region_ok SEGS E (mrestrict (w_H W) mem) sc_a_ncalls).
{ unfold region_ok, sc_a_ncalls.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 44) (VAL (A_OBJ 44)) E284) by (rewrite V44; unfold A_G_REC; lia).
  rewrite V44. unfold A_G_REC. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply HW; lia|].
  constructor; [exact CK | constructor]. }
assert (HG : facts_ok E sc_a_facts).
{ split; [|split; [exact I | exact I]].
  cbn [sc_a_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E33, E284, V44, !unsigned_lit_small by (unfold SB, A_G_REC; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil Hal16 C1 Hstk0 Hn16. clear. unfold SB, A_G_REC. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
split; [|unfold sh_ok, sc_SH; apply Forall_nil].
unfold sc_a_ss. apply pa_entry_st_ok_full.
- subst E. unfold sc_a_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sc_a_regions. constructor; [exact RS|]. constructor; [apply RG; left; reflexivity|].
  constructor; [apply RG; right; left; reflexivity|]. constructor; [exact RN | constructor].
- apply pairwise_disjoint_of_extents.
  unfold sc_a_regions, stack_region, got_regionP, bcell_regionP, sc_a_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E240) by (rewrite V0; lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E252) by (rewrite V12; lia).
  rewrite (VB (A_OBJ 44) (VAL (A_OBJ 44)) E284) by (rewrite V44; unfold A_G_REC; lia).
  cbn [base_val]. rewrite Usp, V0, V12, V44. unfold A_G_REC.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 C3 Hstk0. clear. intros.
  repeat split; lia.
- exact HG.
Qed.

(* a field read back through a reader that agrees with another on its bytes *)
Lemma sc_a_aval_keep : forall (rd rd' : reader) a n v,
  (forall b, a <= b < a + Z.of_nat n -> rd' b = rd b) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v HK H k Hk. rewrite HK by lia. exact (H k Hk). Qed.

(* blocks of positive extent that are pairwise disjoint are listed once each *)
Lemma sc_a_nodup_pw : forall l : list (Z * Z),
  YG0f.pairwise YG0f.zdisjoint (map (fun b => (fst b, req_size (snd b))) l) ->
  (forall b, In b l -> 0 <= snd b) -> List.NoDup l.
Proof.
induction l as [|b l IH]; intros Hp Hn; [constructor|].
cbn [map YG0f.pairwise] in Hp. destruct Hp as [HF Hp]. constructor.
- intros Hin. rewrite Forall_forall in HF.
  pose proof (HF (fst b, req_size (snd b)) (in_map (fun b => (fst b, req_size (snd b))) l b Hin)) as HD.
  unfold YG0f.zdisjoint in HD. cbn [fst snd] in HD.
  pose proof (req_size_pos (snd b) (Hn b (or_introl eq_refl))) as [H1 _]. lia.
- apply IH; [exact Hp | intros b' Hb'; apply Hn; right; exact Hb'].
Qed.

(* no live block is listed twice (AR_blocks_law's pairwise disjointness) *)
Lemma sc_a_blocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
destruct (ablocks B ly S) as [|[p0 n0] l0] eqn:Hbl; [constructor|].
rewrite <- Hbl.
destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR ltac:(rewrite Hbl; left; reflexivity))
  as (_ & _ & _ & _ & _ & Hpw & _).
apply sc_a_nodup_pw; [exact Hpw|].
intros [p n] Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
cbn [snd]. lia.
Qed.

Lemma sc_a_nodup_app : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
induction l1 as [|y l1 IH]; intros l2 x HN Hx Hx2; [destruct Hx|].
cbn [app] in HN. inversion HN as [|? ? Hy HN']; subst.
destruct Hx as [<- | Hx].
- apply Hy. apply in_or_app. right. exact Hx2.
- exact (IH l2 x HN' Hx Hx2).
Qed.

(* none of the program's statics is owned by the runtime or is the errno cell *)
Lemma sc_a_pg_unowned : forall a, inFP cmd_PG a ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB).
destruct Ha as (r & Hr & Hb).
assert (HOW : forallb (fun q : Z * Z => forallb (fun p : Z * Z =>
((fst q + snd q <=? fst p) || (snd p <=? fst q))%bool) cmd_PG) Tfib_owned_static = true)
by (vm_compute; reflexivity).
assert (HER : forallb (fun p : Z * Z => ((snd p <=? TFIB_ERRNO) || (TFIB_ERRNO + 4 <=? fst p))%bool) cmd_PG = true)
by (vm_compute; reflexivity).
split.
- intros HE. rewrite Exists_exists in HE. destruct HE as (q & Hq & Hz). unfold in_zr in Hz.
  rewrite forallb_forall in HOW. specialize (HOW q Hq). rewrite forallb_forall in HOW. specialize (HOW r Hr).
  apply Bool.orb_prop in HOW as [H1 | H1]; apply Z.leb_le in H1; lia.
- rewrite forallb_forall in HER. specialize (HER r Hr).
  apply Bool.orb_prop in HER as [H1 | H1]; apply Z.leb_le in H1; lia.
Qed.

Lemma sc_prologue : SC_B_stmt B MT ->
  forall ly S W (regs : bvmap 5 word) mem md ch (id pl : Z) (line : list byte) (R : rstate) (O : list (Z * Z)),
  let t := snd (sup_call_m R id line) in
  sc_pre B MT ly S W regs mem md ch id pl line R O t ->
  sc_line_blk B ly S O pl line ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_sup_call) regs mem md) (sc_post B MT ly S W regs mem md id line R O t).
Proof.
intros HBS ly S W regs mem md ch id pl line R O t HPRE0 HLB.
pose proof HPRE0 as (HPRE & HFRM & Hfr8 & HROD & HROK & H10 & Hid & H11 & Hpl & HSTR & HREP & Hev & Hlive & HMOK).
pose proof HREP as (Q & HARP & HOQ).
pose proof HARP as (Hgr8 & Hsc8 & Hgs & HCALLS & HANS & HREPL & HSCAL & HOWN).
pose proof HCALLS as (Hn16 & HlenQ & HNC & HTAB & HSPILL & HSPL).
destruct (sc_a_entry W ly S regs mem md ch (Z.of_nat (length (r_calls R))) HPRE HNC ltac:(lia)) as [HS SHOK].
pose proof (ajournal_init SEGS B SUP_CALL_STK (SC_FP O) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (WS : 48 + REC_CALLS_FREE_STK <= SUP_CALL_STK) by (vm_compute; intros Hx; discriminate Hx).
assert (HRCF : 0 <= REC_CALLS_FREE_STK) by (vm_compute; intros Hx; discriminate Hx).
assert (Hlo48 : alloc_ceiling <= spZ regs - 48) by lia.
remember (sc_a_E regs (Z.of_nat (length (r_calls R)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn'; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
unfold sc_a_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn').
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; unfold sc_a_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (length (r_calls R))))
  by (subst E; unfold sc_a_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U44 : bv_unsigned (ew E 285%nat) = A_G_REC).
{ change 285%nat with (A_OBJ 44).
  rewrite (HEI (A_OBJ 44) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), sc_a_obj44. reflexivity. }
assert (HAE : env_agree 32 (Ereg regs (sc_a_extra (Z.of_nat (length (r_calls R))))) E)
  by (rewrite HE; split; [intros n Hn'; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_sup_call)) with (Z_to_bv 64 (BASE + AF_sup_call)).
unfold sc_a_ss, sc_a_regions, sc_a_ncalls in HS.
(* 0x8a95c .. 0x8a998: the frame, s0 := line, a1 := g_rec, a2 := g_rec.ncalls, s3 := the shadow base, s2 := id *)
paj_run_tok RUN HS HJ SHOK sc_Bspan.
{ awr_ok_tac; first [exact Usp | apply sc_a_awr_ncalls; [exact U44 | apply awr_ok_nil]]. }
lazymatch goal with |- context [with_vm_backing ?a ?b ?c] => set (mdv0 := with_vm_backing a b c) in * end.
clearbody mdv0.
rename HF into HF1. rename HFr into HFr1. rename HG into HG1.
psrr_branch_tok RUN BR HS SHOK sc_Bspan.
- (* n <> 16: the table arm 0x8a9b4 .. 0x8a9cc, up to the join *)
  assert (Hlt : (length (r_calls R) < 16)%nat).
  { rewrite branch_ne_U, (U_atom E 33%nat (Z.of_nat (length (r_calls R))) E33) in Hc by lia.
    rewrite U_lit in Hc by lia. apply Bool.negb_true_iff, Z.eqb_neq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK sc_Bspan sc_mid_pc.
  { awr_ok_tac; first [exact Usp | apply sc_a_awr_ncalls; [exact U44 | apply awr_ok_nil]]. }
  lazymatch goal with |- context [with_vm_backing ?a ?b ?c] => set (mdv1 := with_vm_backing a b c) in * end.
  clearbody mdv1.
  (* the registers, the frame and the new ncalls at the join *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict ?H ?msx) =>
    pose proof (st_ok_pi_region_nth E ssx (restrict H msx) 0 _ HS eq_refl) as HRF;
    pose proof (st_ok_pi_region_nth E ssx (restrict H msx) 3 _ HS eq_refl) as HRN end.
  cbn [ms_mem restrict mkst] in HRF, HRN.
  prreg HS (2%bv : bv 5) P2. prreg HS (19%bv : bv 5) P19. prreg HS (18%bv : bv 5) P18.
  prreg HS (8%bv : bv 5) P8. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  assert (P9 : getr (ms_regs ms0) 9 = sv_denot E
    (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit 56)) (SLit 16)) (SOff 285 0))).
  { lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict ?H ?msx) =>
      pose proof (st_ok_pi_restrict_reg H E ssx msx (9%bv : bv 5) HS) as HR9;
      change (sr_get (ss_regs ssx) (9%bv : bv 5)) with
        (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit 56)) (SLit 16)) (SOff 285 0)) in HR9;
      cbn [ms_regs restrict mkst] in HR9; exact HR9 end. }
  assert (Hn15 : 0 <= Z.of_nat (length (r_calls R)) <= 15) by lia.
  assert (Un33 : U E (SOff 33 0) = Z.of_nat (length (r_calls R))).
  { rewrite U_SOff, E33, unsigned_lit_small by lia. rewrite Z.add_0_r. apply sc_a_zc. lia. }
  assert (Un285 : U E (SOff 285 0) = A_G_REC).
  { rewrite U_SOff, U44, Z.add_0_r. apply sc_a_zc. unfold A_G_REC. lia. }
  assert (HU9 : U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit 56)) (SLit 16)) (SOff 285 0))
    = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
    rewrite Un33, Un285, !U_SLit.
    rewrite (sc_a_zc 56 ltac:(lia)), (sc_a_zc 16 ltac:(lia)).
    rewrite (sc_a_zc (Z.of_nat (length (r_calls R)) * 56) ltac:(lia)).
    rewrite (sc_a_zc (Z.of_nat (length (r_calls R)) * 56 + 16) ltac:(lia)).
    unfold A_G_REC, OFF_CALLS, CALL_SIZE in *.
    rewrite (sc_a_zc (Z.of_nat (length (r_calls R)) * 56 + 16 + 6174528) ltac:(lia)). lia. }
  assert (H9 : getr (ms_regs ms0) 9 = w64 (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)))).
  { rewrite P9, <- HU9. unfold w64, U. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (Hsp' : spZ (ms_regs ms0) = spZ regs - 48).
  { unfold spZ at 1. rewrite P2, Usp, unsigned_lit_small by lia. lia. }
  assert (HRSF : rec_spill_frees R = 0).
  { unfold rec_spill_frees. rewrite (proj2 (Nat.ltb_lt _ _) Hlt). reflexivity. }
  (* the memory at the join differs from the entry's only in the frame and in the ncalls field *)
  assert (KO : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) ->
    ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W (ms_mem ms0) a = rdW W mem a).
  { intros a Ha H1 H2.
    assert (Hmid : rdW W (ms_mem ms0) a = rdW W (ms_mem ms) a).
    { apply (kept_of_frame (segs:=SEGS) E _ (w_H W) (ms_mem ms) (ms_mem ms0)
        (fun a => (spZ regs - 48 <= a < spZ regs) \/
                  (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)) HFr);
      [ intros b wlo whi a' Hin Hr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
          [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?Usp, ?U44 in Hr;
           unfold A_G_REC, OFF_NCALLS in *; lia|]); destruct Hin
      | exact Ha | tauto ]. }
    rewrite Hmid.
    apply (kept_of_frame (segs:=SEGS) E _ (w_H W) mem (ms_mem ms)
      (fun a => (spZ regs - 48 <= a < spZ regs) \/
                (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)) HFr1);
    [ intros b wlo whi a' Hin Hr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?Usp, ?U44 in Hr;
         unfold A_G_REC, OFF_NCALLS in *; lia|]); destruct Hin
    | exact Ha | tauto ]. }
  (* every block of the entry lies below the allocation ceiling, so the run kept its bytes *)
  assert (HBLK : forall p m i, In (p, m) (ablocks B ly S) -> 0 <= i < m ->
    rdW W (ms_mem ms0) (p + i) = rdW W mem (p + i)).
  { intros p m i Hin Hi.
    destruct (al_blocks _ _ LAWS ly S W mem md p m HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
    pose proof (blk_off_imgP B ly S W mem md p m HAR Hin) as Hoff. unfold off_img in Hoff.
    apply KO; revert Hi Hp4096 Hpceil Hreq Hoff Hlo48 C1; unfold A_G_REC, OFF_NCALLS; clear; intros; lia. }
  pmkst HS.
  assert (HMID : sc_mid B MT ly S W regs mem md R O ly S W (ms_regs ms0) (ms_mem ms0) mdv1 0
    (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)))).
  { split; [exact HJ|]. split; [rewrite HRSF; lia|].
    split; [left; exists (Z.of_nat (length (r_calls R))); split; [unfold REC_CALLS_MAX; lia | reflexivity]|].
    split.
    { split; [exact Hsp'|]. split; [exact H9|].
      split; [rewrite P19, E32; reflexivity|].
      split; [rewrite P18, (EE 10%nat (10%bv : bv 5) eq_refl); reflexivity|].
      split; [rewrite P8, (EE 11%nat (11%bv : bv 5) eq_refl); reflexivity|].
      split; [rewrite P3, (EE 3%nat (3%bv : bv 5) eq_refl); reflexivity|].
      split; [rewrite P4, (EE 4%nat (4%bv : bv 5) eq_refl); reflexivity|].
      intros r Hr.
      assert (Hcases : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ prreg HS (Z_to_bv 5 20) Q20; rewrite Q20; exact (EE 20%nat (Z_to_bv 5 20) ltac:(vm_compute; reflexivity))
      | prreg HS (Z_to_bv 5 21) Q21; rewrite Q21; exact (EE 21%nat (Z_to_bv 5 21) ltac:(vm_compute; reflexivity))
      | prreg HS (Z_to_bv 5 22) Q22; rewrite Q22; exact (EE 22%nat (Z_to_bv 5 22) ltac:(vm_compute; reflexivity))
      | prreg HS (Z_to_bv 5 23) Q23; rewrite Q23; exact (EE 23%nat (Z_to_bv 5 23) ltac:(vm_compute; reflexivity))
      | prreg HS (Z_to_bv 5 24) Q24; rewrite Q24; exact (EE 24%nat (Z_to_bv 5 24) ltac:(vm_compute; reflexivity))
      | prreg HS (Z_to_bv 5 25) Q25; rewrite Q25; exact (EE 25%nat (Z_to_bv 5 25) ltac:(vm_compute; reflexivity))
      | prreg HS (Z_to_bv 5 26) Q26; rewrite Q26; exact (EE 26%nat (Z_to_bv 5 26) ltac:(vm_compute; reflexivity))
      | prreg HS (Z_to_bv 5 27) Q27; rewrite Q27; exact (EE 27%nat (Z_to_bv 5 27) ltac:(vm_compute; reflexivity)) ]. }
    split.
    { intros j r Hj. destruct j as [|[|[|[|[|[|j]]]]]]; cbn [nth_error sc_saved] in Hj; try discriminate Hj;
      injection Hj as <-.
      - refine (sc_a_chunk E W (ms_mem ms0) (spZ regs) _ (-8) 1%nat (Z_to_bv 5 1) regs _ HRF Usp _
          (EE 1%nat (Z_to_bv 5 1) ltac:(vm_compute; reflexivity)) _);
        [cbn [In]; repeat (first [left; reflexivity | right]) | cbn [Z.of_nat]; lia].
      - refine (sc_a_chunk E W (ms_mem ms0) (spZ regs) _ (-16) 8%nat (Z_to_bv 5 8) regs _ HRF Usp _
          (EE 8%nat (Z_to_bv 5 8) ltac:(vm_compute; reflexivity)) _);
        [cbn [In]; repeat (first [left; reflexivity | right]) | cbn [Z.of_nat]; lia].
      - refine (sc_a_chunk E W (ms_mem ms0) (spZ regs) _ (-24) 9%nat (Z_to_bv 5 9) regs _ HRF Usp _
          (EE 9%nat (Z_to_bv 5 9) ltac:(vm_compute; reflexivity)) _);
        [cbn [In]; repeat (first [left; reflexivity | right]) | cbn [Z.of_nat]; lia].
      - refine (sc_a_chunk E W (ms_mem ms0) (spZ regs) _ (-32) 18%nat (Z_to_bv 5 18) regs _ HRF Usp _
          (EE 18%nat (Z_to_bv 5 18) ltac:(vm_compute; reflexivity)) _);
        [cbn [In]; repeat (first [left; reflexivity | right]) | cbn [Z.of_nat]; lia].
      - refine (sc_a_chunk E W (ms_mem ms0) (spZ regs) _ (-40) 19%nat (Z_to_bv 5 19) regs _ HRF Usp _
          (EE 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)) _);
        [cbn [In]; repeat (first [left; reflexivity | right]) | cbn [Z.of_nat]; lia]. }
    split; [reflexivity|]. split; [lia|].
    split; [rewrite HRSF; rewrite Z.mul_0_l; exact (mle_start MT S MTL)|].
    split; [intros pn Hpn _; exact Hpn|].
    exists Q. split; [exact HARP|]. split; [exact HOQ|].
    left. split; [exact Hlt|].
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { apply sc_aval_of_val_mem.
      exact (field_of_region E (mrestrict (w_H W) (ms_mem ms0)) 285%nat A_G_REC _ 8 12 8 12 8 4%N (SOff 33 1)
        (Z.of_nat (length (r_calls R)) + 1) HRN U44
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity)
        ltac:(cbn; lia) ltac:(cbn; lia)). }
    split; [intros a Ha Hna; apply KO; unfold A_G_REC, REC_SIZE, OFF_NCALLS in *; lia|].
    split; [intros a Ha; apply KO; unfold A_G_REC, A_REC_SPILL, SC_SIZE, OFF_NCALLS in *; lia|].
    exact HBLK. }
  exact (HBS ly S W regs mem md ch id pl line R O ly S W (ms_regs ms0) (ms_mem ms0) mdv1 0
    (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))) HPRE0 HLB HMID).
- (* n = 16: the spill arm 0x8a99c .. 0x8a9b0, with the call of rec_calls_free *)
  assert (H16 : (length (r_calls R) = 16)%nat).
  { rewrite branch_ne_U, (U_atom E 33%nat (Z.of_nat (length (r_calls R))) E33) in Hc by lia.
    rewrite U_lit in Hc by lia. apply Bool.negb_false_iff, Z.eqb_eq in Hc. lia. }
  paj_run_tok RUN HS HJ SHOK sc_Bspan.
  { awr_ok_tac; first [exact Usp | apply sc_a_awr_ncalls; [exact U44 | apply awr_ok_nil]]. }
  lazymatch goal with |- context [with_vm_backing ?a ?b ?c] => set (mdv2 := with_vm_backing a b c) in * end.
  clearbody mdv2.
  rename HF into HFs. rename HFr into HFrs. rename HG into HGs.
  (* the state at the call 0x8a9ac: a0 = s1 = &record.spill, a1 = 1, ra = 0x8a9b0, s0 = the line *)
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  assert (U292 : bv_unsigned (ew E (A_OBJ 51)) = A_REC_SPILL).
  { rewrite (HEI (A_OBJ 51) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), sc_a_obj51. reflexivity. }
  assert (E292 : ew E (A_OBJ 51) = Z_to_bv 64 A_REC_SPILL) by (rewrite <- U292, Z_to_bv_bv_unsigned; reflexivity).
  change (ew E 292%nat) with (ew E (A_OBJ 51)) in P10. rewrite E292 in P10.
  assert (HspC : spZ (ms_regs ms0) = spZ regs + -48).
  { unfold spZ at 1. rewrite P2, Usp, unsigned_lit_small by lia. lia. }
  (* g_rec.ncalls still holds n at the call *)
  assert (VNc : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (A_G_REC + 8) 4 (Z.of_nat (length (r_calls R)))).
  { lazymatch type of HS with st_ok _ _ ?ssx (restrict ?H ?msx) =>
      pose proof (st_ok_region_nth (segs:=SEGS) E ssx (restrict H msx) 3%nat _ HS eq_refl) as HRNc end.
    cbn [ms_mem restrict mkst] in HRNc.
    exact (field_of_region E (mrestrict (w_H W) (ms_mem ms0)) 285%nat A_G_REC _ 8 12 8 12 8 4%N (SOff 33 0)
      (Z.of_nat (length (r_calls R))) HRNc U44
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)). }
  (* the memory at the call differs from the entry's only in the frame *)
  assert (KOs : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) ->
    ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W (ms_mem ms0) a = rdW W mem a).
  { intros a Ha H1 H2.
    assert (Hmid : rdW W (ms_mem ms0) a = rdW W (ms_mem ms) a).
    { apply (kept_of_frame (segs:=SEGS) E _ (w_H W) (ms_mem ms) (ms_mem ms0)
        (fun a => (spZ regs - 48 <= a < spZ regs) \/
                  (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)) HFrs);
      [ intros b wlo whi a' Hin Hr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
          [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?Usp, ?U44 in Hr;
           unfold A_G_REC, OFF_NCALLS in *; lia|]); destruct Hin
      | exact Ha | tauto ]. }
    rewrite Hmid.
    apply (kept_of_frame (segs:=SEGS) E _ (w_H W) mem (ms_mem ms)
      (fun a => (spZ regs - 48 <= a < spZ regs) \/
                (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)) HFr1);
    [ intros b wlo whi a' Hin Hr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?Usp, ?U44 in Hr;
         unfold A_G_REC, OFF_NCALLS in *; lia|]); destruct Hin
    | exact Ha | tauto ]. }
  assert (KEEPc : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem ms0) a = rdW W mem a).
  { intros a Ha. unfold OFF_NCALLS in KOs, HNC.
    destruct (Z_lt_le_dec a (A_G_REC + 8)) as [Hl | Hl];
      [|destruct (Z_lt_le_dec a (A_G_REC + 8 + 4)) as [Hh | Hh]].
    - apply KOs; lia.
    - pose proof (sc_aval_of_val_mem SEGS (w_H W) (ms_mem ms0) _ _ _ VNc (Z.to_nat (a - (A_G_REC + 8)))
        ltac:(lia)) as V1.
      pose proof (HNC (Z.to_nat (a - (A_G_REC + 8))) ltac:(lia)) as V2.
      rewrite Z2Nat.id in V1, V2 by lia.
      replace (A_G_REC + 8 + (a - (A_G_REC + 8))) with a in V1, V2 by lia.
      rewrite V1, V2. reflexivity.
    - apply KOs; lia. }
  (* the read-only bytes and the stack the callee asks for, at the call *)
  assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms0))).
  { intros a Hro Ho He. rewrite KEEPc; [exact (HROD a Hro Ho He)|].
    destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
    - pose proof (Hsegs a (ex_intro _ sg (conj Hsg Hr))) as Hlow. lia.
    - unfold CMD_RLO, CMD_RHI in Hr. lia. }
  (* s0 holds the line, which lies in a live block below alloc_ceiling *)
  assert (HPLc : pl < alloc_ceiling).
  { pose proof HLB as (p0 & k0 & Hin0 & _ & Hp0 & Hpk0).
    destruct (al_blocks _ _ LAWS ly S W mem md p0 k0 HAR Hin0) as (_ & _ & Hc0 & _ & _ & _ & Hk0).
    pose proof (req_size_pos k0 ltac:(lia)) as [_ Hr0]. lia. }
  (* the spill's call: its arguments are live blocks of the recorder *)
  set (PS := l_spill Q) in *.
  pose proof HSPILL as (_ & Hl6 & HlenP & _ & Hnav & HndP & Hargs).
  assert (PSbl : forall pn, In pn PS -> In pn (ablocks B ly S)).
  { intros pn Hin. destruct (In_nth_error _ _ Hin) as [k Hk].
    assert (Hk' : (k < length (snd (r_spill R)))%nat)
      by (rewrite <- HlenP; apply nth_error_Some; rewrite Hk; discriminate).
    destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
    exact (proj1 (proj2 (proj2 (Hargs k s pn Hs Hk)))). }
  assert (PSO : forall pn, In pn PS -> In pn O).
  { intros pn Hin. apply HOQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hin. }
  assert (Hsf : rec_spill_frees R = Z.of_nat (length PS)).
  { unfold rec_spill_frees. rewrite H16. cbn. rewrite HlenP. reflexivity. }
  assert (HEV3 : 0 <= EV_ARG_I + EV_ARG_LINE + EV_ANSWER) by (vm_compute; intros Hx; discriminate Hx).
  assert (HXM3 : 0 <= XM_ARG_I MT id + XM_ARG_LINE MT line + XM_ANSWER MT t).
  { unfold XM_ARG_I, XM_ARG_LINE, XM_ANSWER,
      OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.hand_back_c.XM_HAND_BACK,
      OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.xstrdup_c.XM_XSTRDUP,
      OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.rec_canonical_c.XM_REC_CANONICAL.
    pose proof (mo_free_nonneg MT MTL).
    pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (dec id)) + 1) ltac:(lia)).
    pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length line) + 1) ltac:(lia)).
    pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length t) + 1) ltac:(lia)). lia. }
  (* the callee's footprint: the spill's nargs field and the spill's argument blocks, all below alloc_ceiling *)
  assert (FP1lo : forall a, inFP (rcf_fp A_REC_SPILL [PS]) a ->
    (A_REC_SPILL + CALL_OFF_NARGS <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) \/
    exists p k, In (p, k) PS /\ p <= a < p + req_size k).
  { intros a Ha. unfold rcf_fp in Ha. apply inFP_app in Ha as [Ha | Ha].
    - left. cbn [length seq map] in Ha. apply inFP_cons in Ha as [Ha | Ha]; [|destruct (inFP_nil a Ha)].
      unfold CALL_SIZE in Ha. cbn [Z.of_nat] in Ha. lia.
    - right. cbn [concat] in Ha. rewrite app_nil_r in Ha. exact (inFP_ablocks_fp_inv PS a Ha). }
  assert (FP1cl : ~ YI16.sink_open_fp (rcf_fp A_REC_SPILL [PS])).
  { intros (r & Hr & H0). destruct (FP1lo 0 (ex_intro _ r (conj Hr H0))) as [Hs | (p & k & Hin & Hpk)].
    - unfold A_REC_SPILL, CALL_OFF_NARGS in Hs. lia.
    - destruct (al_blocks _ _ LAWS ly S W mem md p k HAR (PSbl _ Hin)) as (_ & Hp & _). lia. }
  pmkst HS. rewrite sc_a_sig_rcf.
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS W (ms_regs ms0) (ms_mem ms0) _ SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md [] ly S
      mdv2 0 REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [PS]) (EV_REC_CALLS_FREE [PS]) (-48)
      (Z_to_bv 64 (BASE + 17612)) []).
    - exact HJ.
    - exact HspC.
    - reflexivity.
    - lia.
    - exact HRCF.
    - lia.
    - rewrite P3, (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite P4, (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact P1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite unsigned_lit_small by lia. lia.
    - apply achain_low. unfold s0Z. rewrite P8, (EE 11%nat 11%bv eq_refl), H11. unfold w64.
      rewrite unsigned_lit_small by lia. exact HPLc.
    - intros Hpre'. eapply SRr_mono.
      + apply (TREC_CALLS_FREE fx ly S W (ms_regs ms0) (ms_mem ms0) mdv2 [] A_REC_SPILL [PS]).
        * exact Hpre'.
        * exact HRODc.
        * exact P10.
        * rewrite P11. reflexivity.
        * cbn. lia.
        * right. left. unfold CALL_SIZE, SC_SIZE. cbn. lia.
        * (* record.spill is 8-aligned: rec_calls_free's `c mod 8 = 0` *)
          unfold A_REC_SPILL. reflexivity.
        * intros i P' Hi. destruct i as [|i]; [|destruct i; discriminate Hi]. cbn in Hi. injection Hi as <-.
          split; [rewrite HlenP; exact Hl6|]. split.
          { replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_NARGS) with (A_REC_SPILL + CALL_OFF_NARGS) by lia.
            rewrite HlenP. apply (sc_a_aval_keep (rdW W mem)); [|exact Hnav].
            intros b Hb. apply KEEPc. cbn [Z.of_nat] in Hb. unfold A_REC_SPILL, CALL_OFF_NARGS in *. lia. }
          intros a pn Ha.
          assert (Ha' : (a < length (snd (r_spill R)))%nat)
            by (rewrite <- HlenP; apply nth_error_Some; rewrite Ha; discriminate).
          destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
          destruct (Hargs a s pn Hs Ha) as (G1 & _ & G3 & _).
          split; [|exact G3].
          replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_ARGS + 8 * Z.of_nat a)
            with (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat a) by lia.
          apply (sc_a_aval_keep (rdW W mem)); [|exact G1].
          intros b Hb. apply KEEPc. cbn [Z.of_nat] in Hb. unfold A_REC_SPILL, CALL_OFF_ARGS in *. lia.
        * cbn [concat]. rewrite app_nil_r. exact HndP.
        * unfold EV_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r. unfold EV_SUP_CALL in Hev. lia.
        * apply (mo_ok_le MT MTL S _ (XM_SUP_CALL MT R id line t) HMOK). unfold XM_REC_CALLS_FREE, XM_SUP_CALL.
          cbn [concat]. rewrite app_nil_r. rewrite Hsf. lia.
      + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & HQ2).
        exists ly2, S2, regs2, mem2, md2. rewrite P1 in Hc2. split; [exact Hc2|]. split; [exact HJ2|].
        split; [exact HP2|]. exact HQ2.
    - intros a Hfp. destruct (FP1lo a Hfp) as [Hs | (p & k & Hin & Hpk)].
      + do 4 right. unfold awr_prog_or_caller. left.
        assert (Hpg : inFP cmd_PG a).
        { exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity|].
          cbn [fst snd]. unfold CALL_OFF_NARGS in Hs. lia. }
        split; [|split; [exact (sc_a_prog a Hpg) | exact (cif_prog_img _ _ IMG a Hpg)]].
        exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; right; right; left; reflexivity|].
        cbn [fst snd]. unfold SC_SIZE, CALL_OFF_NARGS in *. lia.
      + right. left. split.
        * exists (p, p + req_size k). split; [|cbn [fst snd]; lia].
          right; right; right; right. unfold ablocks_fp. apply in_map_iff.
          exists (p, k). split; [reflexivity | exact (PSO _ Hin)].
        * exists p, k. split; [exact (PSbl _ Hin) | exact Hpk].
    - intros ly2 S2 W2 regs2 mem2 md2 _ a Hfp Hw _. exfalso.
      destruct (FP1lo a Hfp) as [Hs | (p & k & Hin & Hpk)].
      + unfold A_REC_SPILL, CALL_OFF_NARGS in Hs. lia.
      + destruct (al_blocks _ _ LAWS ly S W mem md p k HAR (PSbl _ Hin)) as (_ & _ & Hc0 & _). lia. }
  clear SHOK. cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ1 & HP2 & HK2).
  (* back at 0x8a9b0, with the frame kept *)
  jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
  match type of HS2 with ?T -> _ => assert (HRK : T); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
    - apply (mbyte_of_aview SEGS). apply G1; [lia | lia |].
      intros Hfp. destruct (FP1lo a Hfp) as [Hs | (p & k & Hin & Hpk)].
      + unfold A_REC_SPILL, CALL_OFF_NARGS in Hs. lia.
      + destruct (al_blocks _ _ LAWS ly S W mem md p k HAR (PSbl _ Hin)) as (_ & _ & Hc0 & _). lia.
    - intros _. apply (apresent_writable SEGS). apply Hpres2. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 40 (map (getr regs2) CLOB)) as Ec eqn:HEc.
  assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDc : forall k, (k < 40)%nat -> ew Ec k = ew E k)
    by (intros k Hk; rewrite HEc; apply YN3v.ew_havoc_old; exact Hk).
  clear HEc.
  assert (Uspc : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLDc by lia; exact Usp).
  assert (EEc : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ec n = getr regs r).
  { intros n r Hn'. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    rewrite OLDc by lia. exact (EE n r Hn'). }
  assert (SHOKc : sh_ok SEGS sc_Bx sc_SH Ec (mrestrict (w_H W2) mem2)) by (unfold sh_ok, sc_SH; apply Forall_nil).
  (* 0x8a9b0: j 0x8a9d0, the join *)
  paj_run_to_tok RUNTO HS HJ2 SHOKc sc_Bspan sc_mid_pc.
  { awr_ok_tac; first [exact Uspc | apply awr_ok_nil]. }
  lazymatch goal with |- context [with_vm_backing ?a ?b ?c] => set (mdv3 := with_vm_backing a b c) in * end.
  clearbody mdv3.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msJ end.
  prreg HS (2%bv : bv 5) J2. prreg HS (9%bv : bv 5) J9. prreg HS (19%bv : bv 5) J19. prreg HS (18%bv : bv 5) J18.
  prreg HS (8%bv : bv 5) J8. prreg HS (3%bv : bv 5) J3. prreg HS (4%bv : bv 5) J4.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict ?H ?msx) =>
    pose proof (st_ok_pi_region_nth Ec ssx (restrict H msx) 0 _ HS eq_refl) as HRFc end.
  cbn [ms_mem restrict mkst] in HRFc.
  (* the j run wrote nothing; the call kept every byte outside its footprint *)
  assert (KJ : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> rdW W2 (ms_mem msJ) a = rdW W2 mem2 a).
  { intros a Ha Hn.
    apply (kept_of_frame (segs:=SEGS) Ec _ (w_H W2) mem2 (ms_mem msJ) (fun a => spZ regs - 48 <= a < spZ regs) HFr);
    [ intros b wlo whi a' Hin Hr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?Uspc in Hr; lia|]);
      destruct Hin
    | exact Ha | exact Hn ]. }
  destruct HK2 as (HPerm2 & _ & _ & HKB & _ & _ & _ & HBB2 & MLE1).
  cbn [concat] in HPerm2. rewrite app_nil_r in HPerm2.
  pose proof (Permutation_NoDup HPerm2 (sc_a_blocks_nodup ly S W mem md HAR)) as HND2.
  assert (HIFF : forall pn, In pn (ablocks B ly2 S2) <-> In pn (ablocks B ly S) /\ ~ In pn PS).
  { intros pn. split.
    - intros Hin. split.
      + apply (Permutation_in _ (Permutation_sym HPerm2)). apply in_or_app. left. exact Hin.
      + exact (sc_a_nodup_app _ _ pn HND2 Hin).
    - intros [Hin Hns]. pose proof (Permutation_in _ HPerm2 Hin) as H2.
      apply in_app_or in H2 as [H2 | H2]; [exact H2 | contradiction]. }
  assert (HGREC : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rdW W2 (ms_mem msJ) a = rdW W mem a).
  { intros a Ha. unfold REC_SIZE in Ha.
    rewrite KJ by (unfold A_G_REC in *; lia).
    pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
    assert (Hpg : inFP cmd_PG a) by (apply sc_a_grec_pg; lia).
    destruct (sc_a_pg_unowned a Hpg) as [Hno He].
    rewrite (F3 a (cif_prog_img _ _ IMG a Hpg) Hno He).
    - apply KEEPc. unfold A_G_REC in *. lia.
    - apply fp_spares_closed; [exact FP1cl|]. intros Hf. destruct (FP1lo a Hf) as [Hs | (p & k & Hin & Hpk)].
      + unfold A_G_REC, A_REC_SPILL, CALL_OFF_NARGS in *. lia.
      + pose proof (blk_off_imgP B ly S W mem md p k HAR (PSbl _ Hin)) as Hoff. unfold off_img in Hoff.
        unfold A_G_REC in *. lia. }
  assert (HBLKS : forall p m i, In (p, m) (ablocks B ly S) -> ~ In (p, m) PS -> 0 <= i < m ->
    rdW W2 (ms_mem msJ) (p + i) = rdW W mem (p + i)).
  { intros p m i Hin Hns Hi.
    destruct (al_blocks _ _ LAWS ly S W mem md p m HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
    rewrite KJ by lia.
    rewrite (HKB p m i (proj2 (HIFF (p, m)) (conj Hin Hns)) Hi).
    apply KEEPc. lia. }
  pmkst HS.
  assert (HMID : sc_mid B MT ly S W regs mem md R O ly2 S2 W2 (ms_regs msJ) (ms_mem msJ) mdv3
    (0 + EV_REC_CALLS_FREE [PS]) A_REC_SPILL).
  { split; [exact HJ2|].
    split; [unfold EV_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r, Hsf; lia|].
    split; [right; reflexivity|].
    split.
    { split; [unfold spZ at 1; rewrite J2, Uspc, unsigned_lit_small by lia; lia|].
      split.
      { rewrite J9. change (ew Ec 292%nat) with (ew Ec (A_OBJ 51)).
        assert (U292c : bv_unsigned (ew Ec (A_OBJ 51)) = A_REC_SPILL).
        { rewrite (HEIc (A_OBJ 51) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), sc_a_obj51. reflexivity. }
        rewrite <- U292c. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
      split; [rewrite J19, (OLDc 32%nat ltac:(lia)), E32; reflexivity|].
      split; [rewrite J18; exact (EEc 10%nat (10%bv : bv 5) eq_refl)|].
      split; [rewrite J8; exact (EEc 11%nat (11%bv : bv 5) eq_refl)|].
      split; [rewrite J3; exact (EEc 3%nat (3%bv : bv 5) eq_refl)|].
      split; [rewrite J4; exact (EEc 4%nat (4%bv : bv 5) eq_refl)|].
      intros r Hr.
      assert (Hcases : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ prreg HS (Z_to_bv 5 20) R20; rewrite R20; exact (EEc 20%nat (Z_to_bv 5 20) ltac:(vm_compute; reflexivity))
      | prreg HS (Z_to_bv 5 21) R21; rewrite R21; exact (EEc 21%nat (Z_to_bv 5 21) ltac:(vm_compute; reflexivity))
      | prreg HS (Z_to_bv 5 22) R22; rewrite R22; exact (EEc 22%nat (Z_to_bv 5 22) ltac:(vm_compute; reflexivity))
      | prreg HS (Z_to_bv 5 23) R23; rewrite R23; exact (EEc 23%nat (Z_to_bv 5 23) ltac:(vm_compute; reflexivity))
      | prreg HS (Z_to_bv 5 24) R24; rewrite R24; exact (EEc 24%nat (Z_to_bv 5 24) ltac:(vm_compute; reflexivity))
      | prreg HS (Z_to_bv 5 25) R25; rewrite R25; exact (EEc 25%nat (Z_to_bv 5 25) ltac:(vm_compute; reflexivity))
      | prreg HS (Z_to_bv 5 26) R26; rewrite R26; exact (EEc 26%nat (Z_to_bv 5 26) ltac:(vm_compute; reflexivity))
      | prreg HS (Z_to_bv 5 27) R27; rewrite R27; exact (EEc 27%nat (Z_to_bv 5 27) ltac:(vm_compute; reflexivity)) ]. }
    split.
    { intros j r Hj. destruct j as [|[|[|[|[|[|j]]]]]]; cbn [nth_error sc_saved] in Hj; try discriminate Hj;
      injection Hj as <-.
      - refine (sc_a_chunk Ec W2 (ms_mem msJ) (spZ regs) _ (-8) 1%nat (Z_to_bv 5 1) regs _ HRFc Uspc _
          (EEc 1%nat (Z_to_bv 5 1) ltac:(vm_compute; reflexivity)) _);
        [cbn [In]; repeat (first [left; reflexivity | right]) | cbn [Z.of_nat]; lia].
      - refine (sc_a_chunk Ec W2 (ms_mem msJ) (spZ regs) _ (-16) 8%nat (Z_to_bv 5 8) regs _ HRFc Uspc _
          (EEc 8%nat (Z_to_bv 5 8) ltac:(vm_compute; reflexivity)) _);
        [cbn [In]; repeat (first [left; reflexivity | right]) | cbn [Z.of_nat]; lia].
      - refine (sc_a_chunk Ec W2 (ms_mem msJ) (spZ regs) _ (-24) 9%nat (Z_to_bv 5 9) regs _ HRFc Uspc _
          (EEc 9%nat (Z_to_bv 5 9) ltac:(vm_compute; reflexivity)) _);
        [cbn [In]; repeat (first [left; reflexivity | right]) | cbn [Z.of_nat]; lia].
      - refine (sc_a_chunk Ec W2 (ms_mem msJ) (spZ regs) _ (-32) 18%nat (Z_to_bv 5 18) regs _ HRFc Uspc _
          (EEc 18%nat (Z_to_bv 5 18) ltac:(vm_compute; reflexivity)) _);
        [cbn [In]; repeat (first [left; reflexivity | right]) | cbn [Z.of_nat]; lia].
      - refine (sc_a_chunk Ec W2 (ms_mem msJ) (spZ regs) _ (-40) 19%nat (Z_to_bv 5 19) regs _ HRFc Uspc _
          (EEc 19%nat (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)) _);
        [cbn [In]; repeat (first [left; reflexivity | right]) | cbn [Z.of_nat]; lia]. }
    split; [pose proof HJ2 as (_ & _ & _ & _ & _ & HFR2 & _); exact HFR2|].
    split; [unfold LIVE_REC_CALLS_FREE in HBB2; lia|].
    split; [rewrite Hsf; unfold XM_REC_CALLS_FREE in MLE1; cbn [concat] in MLE1; rewrite app_nil_r in MLE1;
            exact MLE1|].
    split; [intros pn Hin HnO; apply HIFF; split; [exact Hin | intros Hps; exact (HnO (PSO pn Hps))]|].
    exists Q. split; [exact HARP|]. split; [exact HOQ|].
    right. split; [exact H16|]. split; [reflexivity|].
    split; [exact HIFF|]. split; [exact HGREC|]. exact HBLKS. }
  exact (HBS ly S W regs mem md ch id pl line R O ly2 S2 W2 (ms_regs msJ) (ms_mem msJ) mdv3
    (0 + EV_REC_CALLS_FREE [PS]) A_REC_SPILL HPRE0 HLB HMID).
Qed.

End e.
End f.
End w.
About sc_prologue.
Print Assumptions sc_prologue.
