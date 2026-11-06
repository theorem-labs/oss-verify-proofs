(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of sup_instance_verb's ASan walk (plugin-hostd/fuzz_command,
   0x8b3b8 .. 0x8b42c: the prologue and the two arms of the inlined record() up to their join), after
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v, the entry walk of an earlier version of lib/A/Prog/sup_worker_list.v and
   the table arm of lib/A/Prog/sup_chain.v (sc_segA_table). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaArt PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  rec_calls_free_c arg_line_c arg_i_c rec_shape_of_c answer_c sup_instance_verb_c hand_back_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  RecBTemplateSiv sup_instance_verb_s2 sup_instance_verb_s3 sup_instance_verb_s4 sup_instance_verb_s5 sup_instance_verb_s6 sup_instance_verb_s7 sup_instance_verb_s8 sup_instance_verb_s9 sup_instance_verb_s10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require strspn_c strcspn_c.
(* the plain proof's lemmas on the line's first word (lib/Prog/sup_instance_verb.v:210-276); its module shares the
   base name of the walk, so it is named by its full path *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require sup_instance_verb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the write-permission obligation of every run of this segment: the frame, the two read-only cells that carry the
   shadow base, and g_rec.ncalls, which is in the footprint and is a program static (sup_chain.v's sc_awr) *)
Ltac siv_awr Usp HEI AWRG VOBJSx :=
lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
eapply awr_ok_cons_stack with (n := 2%nat);
[ reflexivity | exact Usp | vm_compute; discriminate | vm_compute; discriminate |];
apply awr_ok_cons_ro; [cbn; lia|];
apply awr_ok_cons_ro; [cbn; lia|];
eapply awr_ok_cons_gen with (n := RB_GREC) (b := A_G_REC);
[ reflexivity
| rewrite (img_env_atomP _ RB_GREC HEI ltac:(unfold RB_GREC, A_OBJ, A_TEXT, A_LIM; lia)), (rbs_grec_val VOBJSx);
  apply unsigned_lit_small; unfold A_G_REC; lia
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
  apply AWRG; unfold OFF_NCALLS, REC_SIZE, A_G_REC in *; lia
| apply awr_ok_nil ].

(* a register's symbolic value without normalising the denotation, which CmdPaLib's prreg does
   (sup_chain.v's preg) *)
Ltac siv_preg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the five saved words of the frame, read off the stack region of the symbolic state (sup_chain.v's
   sc_frame_of_region at this member's frame) *)
Lemma siv_saved_range : forall j r, nth_error siv_saved j = Some r -> 0 <= r < 32.
Proof.
intros j r Hj.
assert (H32 : Forall (fun x => 0 <= x < 32) siv_saved) by (unfold siv_saved; repeat constructor; lia).
rewrite Forall_forall in H32. apply H32. eapply nth_error_In. exact Hj.
Qed.

Lemma siv_frame_of_region : forall E (m : word -> option byte) sp0 (regs : bvmap 5 word) lo hi wlo whi cs,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = sp0 ->
(forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr regs rr) ->
(forall j r, nth_error siv_saved j = Some r ->
   In (YP09.mkChunk (- 8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
siv_frame_ok m sp0 regs.
Proof.
intros E m sp0 regs lo hi wlo whi cs HR Hsp HE HIn j r Hj.
pose proof (siv_saved_range j r Hj) as Hr32.
assert (Hr5 : Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r)).
{ rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. symmetry. apply Z.mod_small. lia. }
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (- 8 - 8 * Z.of_nat j)) by lia.
change 8%nat with (N.to_nat 8).
apply (field_of_region E m 2%nat sp0 cs lo hi wlo whi (- 8 - 8 * Z.of_nat j) 8
  (SOff (Z.to_nat r) 0) _ HR Hsp (HIn j r Hj)).
- cbn [sv_denot]. rewrite (HE (Z.to_nat r) (Z_to_bv 5 r) Hr5), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. cbn. lia.
- cbn. lia.
Qed.

(* the slot the table arm computes, g_rec + 16 + 56 * ncalls, as the symbolic executor writes it
   (sup_chain.v's sc_den_slot) *)
Lemma siv_den_slot : forall E m g n,
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

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* a write of the walk to g_rec: the footprint's program-static disjunct of awr_byte (sup_worker_list.v's
   swl_awr_grec over siv_FP) *)
Lemma siv_awr_grec : CmdBSyms B -> (forall a, Exists (in_zr a) recb_PG -> in_img SEGS a) ->
forall STK sp0 O bl0 blc fr0 lyc own a,
A_G_REC <= a < A_G_REC + REC_SIZE ->
awr_byte SEGS B STK sp0 (siv_FP O) bl0 blc fr0 lyc own a.
Proof.
intros HB PIMG STK sp0 O bl0 blc fr0 lyc own a Ha.
right; right; right; right. left.
split; [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | exact Ha]|].
split; [rewrite (recb_ts_prog_m B HB); exact (recb_grec_in a Ha) | exact (PIMG a (recb_grec_in a Ha))].
Qed.

(* record()'s spill arm from the call of rec_calls_free (0x8b408) on: the call frees the spill entry's
   arguments, the `j` reaches the join, and the join's segment closes the walk *)
Lemma siv_E_rcf : siv_hyps B MT -> siv_J_goal B MT ->
forall ly S W (regs : bvmap 5 word) mem md ch pl ledger line R O (regsc : bvmap 5 word) memc mdc,
siv_cx B MT ly S W regs mem md ch pl ledger line R O -> frm0 fx ->
(16 <= length (r_calls R))%nat ->
ajournal SEGS B SUP_INSTANCE_VERB_STK (spZ regs) (siv_FP O) ly S W mem md [] ly S W memc mdc 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SUP_INSTANCE_VERB_STK <= a < spZ regs) ->
   rdW W memc a = rdW W mem a) ->
siv_frame_ok (mrestrict (w_H W) memc) (spZ regs) regs ->
spZ regsc = spZ regs - 48 ->
getr regsc 1 = w64 (BASE + SIV_RCF_RET) ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 A_REC_SPILL -> getr regsc 9 = w64 pl -> getr regsc 10 = w64 A_REC_SPILL ->
getr regsc 11 = w64 1 -> getr regsc 18 = w64 ledger -> getr regsc 19 = w64 SB ->
(forall r, 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_rec_calls_free)) memc (seg_rom SEGS)) mdc)
  (siv_post B MT ly S W regs mem md line ledger R O).
Proof.
intros HY HJG ly S W regs mem md ch pl ledger line R O regsc memc mdc CX HFRM H16 HJ KEEP HF Rsp
  R1 R3 R4 R8 R9 R10 R11 R18 R19 Rhi.
destruct HY as [TRCF TARG_LINE TARG_I TRSO TANSWER ASTRSPN ASTRCSPN VOBJS TL HB MTL PIMG PWR SIGP ROK RRO RELRO HTV
  RECC ROMV ZSH HULLL ROPA].
pose proof CX as (HPRE & HROD & HRO & H10 & Hpl64 & H11 & Hled & HLB & HLSTR0 & HLL & HLAP & HREP & HFR8 & HEV
  & HLIVE & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (WS : SUP_INSTANCE_VERB_STK = 16592) by reflexivity.
assert (WR : REC_CALLS_FREE_STK = 16496) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hsp46 : 2 ^ 46 <= sp0 - 48 <= 2 ^ 47).
{ change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328.
  clear - Hceil Hslo Hshi H47 Hstk0 C1 WS. lia. }
assert (Hlow : alloc_ceiling + SUP_INSTANCE_VERB_STK <= sp0) by (clear - Hceil Hslo; lia).
assert (HrepE : rec_repA B ly S (rdW W mem) R O) by exact HREP.
destruct HREP as (Q & HAQ & HOQ).
pose proof HAQ as (_ & _ & _ & HG1 & _).
pose proof HG1 as (Hlen16 & HLQ & HNC & HSLOTS & HSPILL & HSPLEN).
assert (Hn16 : length (r_calls R) = 16%nat) by lia.
(* every byte of a block the recorder owns is below the allocator's ceiling, so outside the frame *)
assert (HBLK : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn ->
  0 <= fst pn + i < 2 ^ 64 /\ fst pn + i < alloc_ceiling).
{ intros [p k] i Hpn Hi. cbn [fst snd] in *.
  pose proof (lay_blocks_in _ _ _ _ _ _ HAQ (p, k) Hpn) as Hin.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR Hin) as (_ & H4096 & Hcl & _ & _ & _ & Hk0).
  pose proof (req_size_pos k ltac:(lia)) as [_ Hreq]. lia. }
(* the recorder at the memory of the call *)
assert (HAQc : arep_at (ablocks B ly S) (rdW W memc) A_G_REC A_REC_SPILL R Q).
{ apply (siv_arep_kept (ablocks B ly S) (ablocks B ly S) (rdW W mem) (rdW W memc) R Q HAQ).
  - intros pn Hpn. exact (lay_blocks_in _ _ _ _ _ _ HAQ pn Hpn).
  - intros a Ha. apply KEEP; unfold A_G_REC in *; lia.
  - intros a Ha. apply KEEP; unfold A_REC_SPILL in *; lia.
  - intros p k i Hpn Hi. destruct (HBLK (p, k) i Hpn Hi) as (Hb1 & Hb2). cbn [fst snd] in *.
    apply KEEP; lia. }
pose proof HAQc as (_ & _ & _ & HG1c & _).
pose proof HG1c as (_ & _ & HNCc & _ & HSPILLc & _).
pose proof HSPILLc as (Hfn & Hna6 & HlenP & Hvfn & Hvnargs & HND & HARGS).
assert (Hconcat : concat [l_spill Q] = l_spill Q) by (cbn [concat]; apply app_nil_r).
assert (HEVrcf : EV_REC_CALLS_FREE [l_spill Q] = rec_spill_frees R).
{ unfold EV_REC_CALLS_FREE, rec_spill_frees. rewrite Hconcat, HlenP.
  rewrite (proj2 (Nat.ltb_ge (length (r_calls R)) 16) ltac:(lia)). reflexivity. }
assert (HXMrcf : XM_REC_CALLS_FREE MT [l_spill Q] = rec_spill_frees R * mo_free MT).
{ unfold XM_REC_CALLS_FREE, rec_spill_frees. rewrite Hconcat, HlenP.
  rewrite (proj2 (Nat.ltb_ge (length (r_calls R)) 16) ltac:(lia)). reflexivity. }
assert (HXnn : 0 <= XM_ARG_LINE MT line + XM_ARG_I MT ledger +
                    XM_ANSWER MT (snd (sup_instance_verb_m R line ledger))).
{ unfold XM_ARG_LINE, rec_canonical_c.XM_REC_CANONICAL, XM_ARG_I, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
  pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length line) + 1) ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (dec ledger)) + 1) ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL
    (Z.of_nat (length (snd (sup_instance_verb_m R line ledger))) + 1) ltac:(lia)).
  lia. }
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W memc))
  by exact (siv_aro_kept B RRO RELRO ROPA ly S W mem md _ R O ly S W memc _ _ _ _ _ HAR HrepE HJ HROD).
(* the footprint of the call lies below the allocator's ceiling *)
assert (HFP1 : forall a, inFP (rcf_fp A_REC_SPILL [l_spill Q]) a -> a < alloc_ceiling).
{ intros a (r & Hr & Har). unfold rcf_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - cbn [length seq map] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Har.
    unfold A_REC_SPILL, CALL_SIZE, CALL_OFF_NARGS in Har. lia.
  - rewrite Hconcat in Hr.
    destruct (inFP_ablocks_fp_inv (l_spill Q) a (ex_intro _ r (conj Hr Har))) as (p & k & Hpk & Hpa).
    assert (Hin : In (p, k) (lay_blocks Q))
      by (unfold lay_blocks; apply in_or_app; right; apply in_or_app; left; exact Hpk).
    pose proof (lay_blocks_in _ _ _ _ _ _ HAQ (p, k) Hin) as HinS.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR HinS) as (_ & _ & Hcl & _). lia. }
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W regsc memc (Z_to_bv 64 (BASE + AF_rec_calls_free)) SUP_INSTANCE_VERB_STK sp0
    (siv_FP O) ly S W mem md [] ly S mdc 0 REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [l_spill Q])
    (EV_REC_CALLS_FREE [l_spill Q]) (-48) (getr regsc 1) [] _ HJ).
  - lia.
  - reflexivity.
  - lia.
  - rewrite WR. lia.
  - rewrite WR, WS. lia.
  - exact R3.
  - exact R4.
  - reflexivity.
  - rewrite R1. unfold w64. apply ret_ok_codeptr_v; [unfold SIV_RCF_RET, AF_sup_instance_verb; lia | reflexivity].
  - rewrite R1. unfold w64. rewrite unsigned_lit_small by (unfold SIV_RCF_RET, AF_sup_instance_verb; lia).
    unfold SIV_RCF_RET, AF_sup_instance_verb. lia.
  - apply achain_low. unfold s0Z. rewrite R8. unfold w64.
    rewrite unsigned_lit_small by (unfold A_REC_SPILL; lia). unfold A_REC_SPILL. lia.
  - intros HPRE1. unfold trec_calls_free_spec in TRCF.
    eapply (TRCF fx ly S W regsc memc mdc [] A_REC_SPILL [l_spill Q] HPRE1 HRODc).
    + exact R10.
    + cbn [length]. exact R11.
    + cbn [length]. lia.
    + right. left. cbn [length]. unfold CALL_SIZE, SC_SIZE. lia.
    + reflexivity.
    + intros i P Hi. destruct i as [|i]; [|cbn in Hi; destruct i; discriminate Hi].
      cbn in Hi. injection Hi as <-.
      split; [lia|].
      split.
      * replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_NARGS) with (A_REC_SPILL + CALL_OFF_NARGS)
          by (cbn [Z.of_nat]; lia).
        rewrite HlenP. exact Hvnargs.
      * intros a pn Ha.
        assert (Hs : exists s, nth_error (snd (r_spill R)) a = Some s).
        { destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Es; [exists s; reflexivity|].
          exfalso. apply nth_error_None in Es.
          pose proof (proj1 (nth_error_Some (l_spill Q) a) ltac:(rewrite Ha; discriminate)). lia. }
        destruct Hs as (s & Hs). destruct (HARGS a s pn Hs Ha) as (Hv & _ & Hin & _).
        split; [|exact Hin].
        replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_ARGS + 8 * Z.of_nat a)
          with (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat a) by (cbn [Z.of_nat]; lia).
        exact Hv.
    + rewrite Hconcat. exact HND.
    + rewrite HEVrcf.
      cbv [EV_SUP_INSTANCE_VERB EV_ARG_LINE rec_canonical_c.EV_REC_CANONICAL EV_ARG_I EV_XSTRDUP
        EV_ANSWER EV_HAND_BACK] in HEV. lia.
    + rewrite HXMrcf.
      apply (mo_ok_le MT MTL S (rec_spill_frees R * mo_free MT)
        (XM_SUP_INSTANCE_VERB MT R line ledger) HMOK).
      unfold XM_SUP_INSTANCE_VERB. lia.
  - intros a Hfp.
    destruct Hfp as (r & Hr & Har). unfold rcf_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
    + cbn [length seq map] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Har.
      right; right; right; right. left.
      assert (Hin : A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE)
        by (unfold CALL_SIZE, CALL_OFF_NARGS, SC_SIZE in *; lia).
      split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE);
              split; [right; left; reflexivity | cbn [fst snd]; exact Hin]|].
      split; [rewrite (recb_ts_prog_m B HB); exact (recb_spill_in a Hin)
             | exact (PIMG a (recb_spill_in a Hin))].
    + rewrite Hconcat in Hr.
      destruct (inFP_ablocks_fp_inv (l_spill Q) a (ex_intro _ r (conj Hr Har))) as (p & k & Hpk & Hpa).
      assert (Hin : In (p, k) (lay_blocks Q))
        by (unfold lay_blocks; apply in_or_app; right; apply in_or_app; left; exact Hpk).
      assert (HinO : In (p, k) O) by (apply HOQ; exact Hin).
      right; left. split.
      * destruct (inFP_ablocks_fp O p k (a - p) HinO ltac:(lia)) as (r' & Hr' & Ha').
        exists r'. split; [right; right; exact Hr' | replace a with (p + (a - p)) by lia; exact Ha'].
      * exists p, k. split; [exact (lay_blocks_in _ _ _ _ _ _ HAQ (p, k) Hin) | exact Hpa].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Hfp Hw _. exfalso.
    pose proof (HFP1 a Hfp). lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2i & HP2 & HK2).
destruct HK2 as (HPerm & HN0 & HKT & HKB & _ & HSP & _ & HBB2 & HMLE2).
pose proof (HSP R Q HAQc eq_refl eq_refl) as HREP2.
destruct HREP2 as (Q0 & HAQ0 & HOQ0).
pose proof (proj1 HJ2i) as HAR2.
pose proof HJ2i as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
assert (KEEPF : forall a, sp0 - 48 <= a < sp0 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha. apply G1; [clear - Ha Hlow WS C1 Hsp46; lia | clear - Ha WR; lia |].
  intros Hfp. pose proof (HFP1 a Hfp). clear - Ha Hlow WS H. lia. }
assert (HF2 : siv_frame_ok (mrestrict (w_H W2) mem2) sp0 regs)
  by exact (siv_frame_kept (w_H W) (w_H W2) memc mem2 sp0 regs HF KEEPF).
assert (T2 : getr regs2 2 = getr regsc 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
assert (Tsp : spZ regs2 = sp0 - 48) by (unfold spZ; rewrite T2; exact Rsp).
assert (Hslot : siv_slot R = A_REC_SPILL)
  by (unfold siv_slot; rewrite (proj2 (Nat.ltb_ge (length (r_calls R)) 16) ltac:(lia)); reflexivity).
destruct (siv_seed_mid B HB VOBJS SIV_RCF_RET sr_atoms ly2 S2 W2 mem2 md2 regs regs2 sp0
  (Z.of_nat (length (r_calls R))) A_REC_SPILL HAR2 Hsp46 Hal16 ltac:(lia) ltac:(right; reflexivity)
  Tsp HF2 ltac:(unfold siv_E; apply regs_ok_Eimg_Ereg)) as [HS2 SHOK2].
pose proof (siv_env regs regs2 (Z.of_nat (length (r_calls R))) A_REC_SPILL) as HEb.
pose proof HEb as (HEI2 & E2w & ESB2 & EN2 & EC2).
set (Ex := siv_E regs regs2 (Z.of_nat (length (r_calls R))) A_REC_SPILL) in *.
assert (EEo2 : forall m0 (rr : bv 5), Z.of_nat m0 = bv_unsigned rr -> ew Ex m0 = getr regs2 rr)
  by (intros m0 rr Hm0; apply siv_E_reg; exact Hm0).
rewrite R1. unfold w64 at 1.
paj_run_to_tok RUNTO HS2 HJ2 SHOK2 siv_Bspan SIV_J.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
pmkst HS2.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem ?m3)) |- _ =>
  pose proof (siv_aview_eq (w_H W2) mem2 (ms_mem m3) (siv_nowin Ex _ _ HFr)) as RDQ end.
prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4.
prreg HS2 (8%bv : bv 5) Q8. prreg HS2 (9%bv : bv 5) Q9. prreg HS2 (18%bv : bv 5) Q18.
prreg HS2 (19%bv : bv 5) Q19.
assert (Thi2' : forall r, 20 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
  by (intros r Hr; rewrite (HP2 r ltac:(unfold acallee_saved; lia)); exact (Rhi r Hr)).
assert (Thi2 : forall r, 20 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite <- (Thi2' r Hr).
  assert (Hr8 : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  (rewrite (st_ok_pi_restrict_reg (w_H W2) Ex _ _ _ HS2); cbn [ms_regs];
   lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
     let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
   cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; apply EEo2; reflexivity). }
assert (HO1sub : forall pn, In pn (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) ->
  In pn (lay_blocks Q)).
{ intros pn Hpn. unfold lay_blocks. apply in_app_or in Hpn as [Hx | Hx];
  [apply in_or_app; left; exact Hx | apply in_or_app; right; apply in_or_app; right; exact Hx]. }
assert (HND2 : List.NoDup (ablocks B ly2 S2 ++ concat [l_spill Q]))
  by exact (Permutation_NoDup HPerm (recb_ablocks_nodup_m B ly S W mem md HAR)).
assert (Hreclen : Z.of_nat (length (r_calls (rec_record R REC_INSTANCE_VERB []))) =
  Z.of_nat (length (r_calls (set_spill R (fst (r_spill R), []))))).
{ unfold rec_record. rewrite (proj2 (Nat.ltb_ge (length (r_calls R)) 16) ltac:(lia)).
  cbn [set_spill r_calls]. reflexivity. }
change (Z_to_bv 64 (BASE + 20296)) with (Z_to_bv 64 (BASE + SIV_J)).
eapply (HJG ly S W regs mem md ch pl ledger line R O ly2 S2 W2 _ _ _
  (0 + EV_REC_CALLS_FREE [l_spill Q]) (set_spill R (fst (r_spill R), [])) Q0 (rdW W2 mem2)).
{ exact CX. }
{ exact HFRM. }
{ exact HJ2. }
{ rewrite HEVrcf. unfold rec_spill_frees.
  rewrite (proj2 (Nat.ltb_ge (length (r_calls R)) 16) ltac:(lia)). lia. }
{ exact (siv_frame_kept (w_H W2) (w_H W2) mem2 _ sp0 regs HF2 (fun a _ => RDQ a)). }
{ unfold siv_regs_ok.
  split; [unfold spZ at 1; rewrite Q2, E2w, unsigned_lit_small by lia; lia|].
  split; [rewrite Q3, (EEo2 3%nat 3%bv eq_refl);
          exact (eq_trans (HP2 3 ltac:(unfold acallee_saved; lia)) R3)|].
  split; [rewrite Q4, (EEo2 4%nat 4%bv eq_refl);
          exact (eq_trans (HP2 4 ltac:(unfold acallee_saved; lia)) R4)|].
  split; [|exact Thi2].
  rewrite Hslot, Q8, (EEo2 8%nat 8%bv eq_refl).
  exact (eq_trans (HP2 8 ltac:(unfold acallee_saved; lia)) R8). }
{ rewrite Q9, (EEo2 9%nat 9%bv eq_refl). exact (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) R9). }
{ rewrite Q18, (EEo2 18%nat 18%bv eq_refl). exact (eq_trans (HP2 18 ltac:(unfold acallee_saved; lia)) R18). }
{ rewrite Q19, (EEo2 19%nat 19%bv eq_refl). exact (eq_trans (HP2 19 ltac:(unfold acallee_saved; lia)) R19). }
{ right. split; [lia | reflexivity]. }
{ exact HAQ0. }
{ intros a _ _. exact (RDQ a). }
{ intros pn i _ _. exact (RDQ (fst pn + i)). }
{ pose proof HAQ0 as (_ & _ & _ & (_ & _ & HNC0 & _) & _).
  rewrite Hreclen. apply (aval_mem_kept (rdW W2 mem2)); [exact HNC0 | intros k _; exact (RDQ _)]. }
{ intros pn Hpn. left. apply HOQ. apply HO1sub. apply HOQ0. exact Hpn. }
{ intros pn Hpn Hno.
  destruct (in_app_or _ _ pn (Permutation_in pn HPerm Hpn)) as [Hx | Hx]; [exact Hx|].
  exfalso. rewrite Hconcat in Hx. apply Hno. apply HOQ. unfold lay_blocks.
  apply in_or_app; right; apply in_or_app; left; exact Hx. }
{ intros pn Hpn.
  assert (HinS : In pn (ablocks B ly S))
    by (apply (Permutation_in pn (Permutation_sym HPerm)); apply in_or_app; left; exact Hpn).
  destruct (siv_in_dec pn O) as [Ho | Hno]; [|left; split; assumption].
  right. apply HOQ0. apply HOQ in Ho. unfold lay_blocks in Ho.
  apply in_app_or in Ho as [Hx | Ho]; [apply in_or_app; left; exact Hx|].
  apply in_app_or in Ho as [Hx | Ho].
  - exfalso. apply (list_nodup_app_disj (ablocks B ly2 S2) (concat [l_spill Q]) pn HND2 Hpn).
    rewrite Hconcat. exact Hx.
  - apply in_or_app; right; exact Ho. }
{ rewrite <- HXMrcf. exact HMLE2. }
{ unfold LIVE_REC_CALLS_FREE in HBB2. lia. }
Qed.

(* the whole walk from the entry: the prologue, then record()'s branch on g_rec.ncalls; the table arm runs to the
   join, the spill arm to the call of rec_calls_free (siv_E_rcf) *)
Lemma siv_seg_E : siv_hyps B MT -> siv_J_goal B MT -> siv_walk_goal B MT.
Proof.
intros HY HJG. unfold siv_walk_goal. intros ly S W regs mem md ch pl ledger line R O CX HFRM.
pose proof HY as HY0.
destruct HY as [TRCF TARG_LINE TARG_I TRSO TANSWER ASTRSPN ASTRCSPN VOBJS TL HB MTL PIMG PWR SIGP ROK RRO RELRO HTV
  RECC ROMV ZSH HULLL ROPA].
pose proof CX as (HPRE & HROD & HRO & H10 & Hpl64 & H11 & Hled & HLB & HLSTR0 & HLL & HLAP & HREP & HFR8 & HEV
  & HLIVE & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (ZC : forall x, 0 <= x < 2 ^ 64 -> zcanon x = x)
  by (intros x Hx; unfold zcanon, M64; apply Z.mod_small; lia).
assert (WS : SUP_INSTANCE_VERB_STK = 16592) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hsp46 : 2 ^ 46 <= sp0 <= 2 ^ 47).
{ change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328. clear - Hceil Hslo Hshi H47 Hstk0 C1 WS. lia. }
assert (HrepE : rec_repA B ly S (rdW W mem) R O) by exact HREP.
destruct HREP as (Q & HAQ & HOQ).
pose proof HAQ as (_ & _ & _ & (Hlen16 & _ & HNC & _) & _).
set (n := Z.of_nat (length (r_calls R))) in *.
set (c := siv_slot R) in *.
assert (Hn : 0 <= n <= 16) by (unfold n; lia).
assert (Hcok : rbs_slot_ok c) by (unfold c; apply siv_slot_ok; exact Hlen16).
destruct (siv_seed_entry B TL HB VOBJS PWR ly S W mem md regs n c HAR Hsp46 Hal16 Hn Hcok
  ltac:(intros a Ha; apply Hpres; rewrite WS; lia) HNC) as [HS SHOK].
pose proof (ajournal_init SEGS B SUP_INSTANCE_VERB_STK (siv_FP O) ly S W regs mem md ch HPRE) as HJ.
pose proof (siv_env regs regs n c) as HE. pose proof HE as (HEI & E2 & ESB & EN & EC).
set (E := siv_E regs regs n c) in *.
assert (EEo : forall m0 (rr : bv 5), Z.of_nat m0 = bv_unsigned rr -> ew E m0 = getr regs rr)
  by (intros m0 rr Hm0; apply siv_E_reg; exact Hm0).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; apply unsigned_lit_small; lia).
assert (EN' : ew E 33%nat = Z_to_bv 64 n) by (change 33%nat with RB_N; exact EN).
assert (ESB' : ew E 32%nat = Z_to_bv 64 SB) by (change 32%nat with RB_SB; exact ESB).
assert (EGz : ew E 285%nat = Z_to_bv 64 A_G_REC).
{ change 285%nat with RB_GREC.
  rewrite (img_env_atomP E RB_GREC HEI ltac:(unfold RB_GREC, A_OBJ, A_TEXT, A_LIM; lia)), (rbs_grec_val VOBJS).
  reflexivity. }
assert (EGu : bv_unsigned (ew E 285%nat) = A_G_REC)
  by (rewrite EGz; apply unsigned_lit_small; unfold A_G_REC; lia).
(* every byte of a block the recorder owns is below the allocator's ceiling, so outside the frame, and is not an
   image byte, so not g_rec.ncalls *)
assert (HBLK : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn ->
  0 <= fst pn + i < 2 ^ 64 /\ ~ (sp0 - SUP_INSTANCE_VERB_STK <= fst pn + i < sp0) /\
  ~ (A_G_REC + OFF_NCALLS <= fst pn + i < A_G_REC + OFF_NCALLS + 4)).
{ intros [p k] i Hpn Hi. cbn [fst snd] in *.
  pose proof (lay_blocks_in _ _ _ _ _ _ HAQ (p, k) Hpn) as Hin.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR Hin) as (_ & H4096 & Hcl & _ & _ & _ & Hk0).
  pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
  split; [lia|]. split; [lia|].
  intros Hnc. apply (recb_heap_noimg_m B ly S W mem md p k (p + i) HAR Hin ltac:(lia)).
  apply PIMG. apply recb_grec_in. unfold OFF_NCALLS, REC_SIZE in *. lia. }
pose proof (siv_awr_grec HB PIMG) as AWRG.
unfold cfg_at.
paj_run_tok RUN HS HJ SHOK siv_Bspan.
{ siv_awr Usp HEI AWRG VOBJS. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => sp0 - SUP_INSTANCE_VERB_STK <= a < sp0 \/
            A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?EGu in Hrr;
       unfold OFF_NCALLS, A_G_REC in *; first [left; lia | right; lia]|]); destruct Hin)) as UN1.
clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
psrr_branch_tok RUN BR HS SHOK siv_Bspan.
- (* record()'s table arm: the branch was taken, so the table has room *)
  (* the branch condition: ncalls <> 16 *)
  assert (Hlt : (length (r_calls R) < 16)%nat).
  { rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    rewrite U_SOff, EN', unsigned_lit_small in Hc by lia.
    rewrite U_SLit, (ZC (n + 0)) in Hc by lia. rewrite (ZC 16) in Hc by lia.
    change n with (Z.of_nat (length (r_calls R))) in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK siv_Bspan SIV_J.
  { siv_awr Usp HEI AWRG VOBJS. }
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
    (fun a => sp0 - SUP_INSTANCE_VERB_STK <= a < sp0 \/
              A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?EGu in Hrr;
         unfold OFF_NCALLS, A_G_REC in *; first [left; lia | right; lia]|]); destruct Hin)) as UN2.
  clear HF HFr HG.
  lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
    assert (UN : forall a, 0 <= a < 2 ^ 64 ->
      ~ (sp0 - SUP_INSTANCE_VERB_STK <= a < sp0 \/
         A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
      aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hna; rewrite (UN2 a Ha Hna); exact (UN1 a Ha Hna)) end.
  clear UN1 UN2.
  (* g_rec.ncalls now counts the call *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict mkst] in HRg end.
  pose proof (field_of_region E _ 285%nat A_G_REC _ _ _ _ _ 8 4 (SOff 33%nat 1) (n + 1) HRg EGu
    ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite EN', unsigned_lit_small by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as Vnc.
  change (N.to_nat 4) with 4%nat in Vnc.
  (* the frame the prologue wrote *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
    cbn [ms_mem restrict mkst] in HR0 end.
  assert (HFc : siv_frame_ok (mrestrict (w_H W) (ms_mem ms0)) sp0 regs).
  { apply (siv_frame_of_region E _ sp0 regs _ _ _ _ _ HR0 Usp EEo).
    intros j r Hj. unfold siv_saved in Hj.
    do 5 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn; tauto|]);
      destruct j; cbn in Hj; discriminate Hj. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  siv_preg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
  assert (Thi : forall r, 20 <= r <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. assert (Hr8 : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    (rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS); cbn [ms_regs];
     lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
       let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
     cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; apply EEo; reflexivity). }
  assert (Hcv : c = A_G_REC + OFF_CALLS + CALL_SIZE * n)
    by (unfold c, siv_slot; rewrite (proj2 (Nat.ltb_lt _ _) Hlt); reflexivity).
  assert (Hrec : Z.of_nat (length (r_calls (rec_record R REC_INSTANCE_VERB []))) = n + 1).
  { unfold rec_record. rewrite (proj2 (Nat.ltb_lt _ _) Hlt). cbn [set_calls r_calls].
    rewrite length_app. cbn [length]. unfold n. lia. }
  change (Z_to_bv 64 (BASE + 20296)) with (Z_to_bv 64 (BASE + SIV_J)).
  eapply (HJG ly S W regs mem md ch pl ledger line R O ly S W _ _ _ 0 R Q (rdW W mem)).
  { exact CX. }
  { exact HFRM. }
  { exact HJ. }
  { unfold rec_spill_frees. destruct (Nat.ltb (length (r_calls R)) 16); lia. }
  { exact HFc. }
  { unfold siv_regs_ok.
    split; [unfold spZ at 1; rewrite P2, Usp, unsigned_lit_small by lia; lia|].
    split; [rewrite P3, (EEo 3%nat 3%bv eq_refl); exact Hgp|].
    split; [rewrite P4, (EEo 4%nat 4%bv eq_refl); exact Htp|].
    split; [|exact Thi].
    fold c. rewrite Hcv, P8. exact (siv_den_slot E 33%nat 285%nat n EN' Hn EGz). }
  { rewrite P9, (EEo 10%nat 10%bv eq_refl). exact H10. }
  { rewrite P18, (EEo 11%nat 11%bv eq_refl). exact H11. }
  { rewrite P19, ESB'. reflexivity. }
  { left. split; [reflexivity | exact Hlt]. }
  { exact HAQ. }
  { intros a Ha Hnc. apply UN; [unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in *; lia|].
    intros [Hx | Hx]; [unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in *; lia | exact (Hnc Hx)]. }
  { intros pn i Hpn Hi. destruct (HBLK pn i Hpn Hi) as (Hb1 & Hb2 & Hb3).
    apply UN; [lia | intros [Hx | Hx]; [exact (Hb2 Hx) | exact (Hb3 Hx)]]. }
  { rewrite Hrec. apply (aval_mem_view SEGS). exact Vnc. }
  { intros pn Hpn. left. apply HOQ. exact Hpn. }
  { intros pn Hpn _. exact Hpn. }
  { intros pn Hpn. destruct (siv_in_dec pn O) as [Ho | Hno]; [right; apply HOQ; exact Ho | left; split; assumption]. }
  { apply (mle_weaken MT S S 0 _ MTL (mle_start MT S MTL)).
    pose proof (mo_free_nonneg MT MTL). unfold rec_spill_frees.
    destruct (Nat.ltb (length (r_calls R)) 16); [lia|]. apply Z.mul_nonneg_nonneg; lia. }
  { lia. }
- (* record()'s spill arm: the branch fell through, so the table is full and the call takes record.spill *)
  assert (H16 : (16 <= length (r_calls R))%nat).
  { rewrite branch_ne_U in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    rewrite U_SOff, EN', unsigned_lit_small in Hc by lia.
    rewrite U_SLit, (ZC (n + 0)) in Hc by lia. rewrite (ZC 16) in Hc by lia.
    change n with (Z.of_nat (length (r_calls R))) in Hc. lia. }
  assert (ESp : ew E 292%nat = Z_to_bv 64 A_REC_SPILL).
  { change 292%nat with RB_SPILL.
    rewrite (img_env_atomP E RB_SPILL HEI ltac:(unfold RB_SPILL, A_OBJ, A_TEXT, A_LIM; lia)),
      (rbs_spill_val VOBJS). reflexivity. }
  paj_run_tok RUN HS HJ SHOK siv_Bspan.
  { siv_awr Usp HEI AWRG VOBJS. }
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
    (fun a => sp0 - SUP_INSTANCE_VERB_STK <= a < sp0 \/
              A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?EGu in Hrr;
         unfold OFF_NCALLS, A_G_REC in *; first [left; lia | right; lia]|]); destruct Hin)) as UN2.
  clear HF HFr HG.
  lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
    assert (UN : forall a, 0 <= a < 2 ^ 64 ->
      ~ (sp0 - SUP_INSTANCE_VERB_STK <= a < sp0 \/
         A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
      aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hna; rewrite (UN2 a Ha Hna); exact (UN1 a Ha Hna)) end.
  clear UN1 UN2.
  (* g_rec.ncalls is untouched on this arm *)
  lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict mkst] in HRg end.
  pose proof (field_of_region E _ 285%nat A_G_REC _ _ _ _ _ 8 4 (SOff 33%nat 0) n HRg EGu
    ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite EN', unsigned_lit_small by lia;
      rewrite Z.add_0_r; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as Vnc0.
  change (N.to_nat 4) with 4%nat in Vnc0.
  (* the memory at the call: the entry's outside this walk's frame *)
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SUP_INSTANCE_VERB_STK <= a < sp0) ->
      rdW W (ms_mem msx) a = rdW W mem a) end.
  { intros a Ha Hna.
    destruct (Z_le_gt_dec (A_G_REC + OFF_NCALLS) a) as [Hl | Hl];
      [destruct (Z_lt_ge_dec a (A_G_REC + OFF_NCALLS + 4)) as [Hh | Hh] | ].
    - pose proof (aval_mem_view SEGS (w_H W) _ (A_G_REC + OFF_NCALLS) 4%nat n Vnc0
        (Z.to_nat (a - (A_G_REC + OFF_NCALLS))) ltac:(lia)) as Hv1.
      pose proof (HNC (Z.to_nat (a - (A_G_REC + OFF_NCALLS))) ltac:(lia)) as Hv2.
      rewrite Z2Nat.id in Hv1, Hv2 by lia.
      replace (A_G_REC + OFF_NCALLS + (a - (A_G_REC + OFF_NCALLS))) with a in Hv1, Hv2 by lia.
      rewrite Hv1, Hv2. reflexivity.
    - apply UN; [lia | intros [Hx | Hx]; [exact (Hna Hx) | lia]].
    - apply UN; [lia | intros [Hx | Hx]; [exact (Hna Hx) | lia]]. }
  (* the frame the prologue wrote *)
  lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
    cbn [ms_mem restrict mkst] in HR0 end.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    assert (HFc : siv_frame_ok (mrestrict (w_H W) (ms_mem msx)) sp0 regs) end.
  { apply (siv_frame_of_region E _ sp0 regs _ _ _ _ _ HR0 Usp EEo).
    intros j r Hj. unfold siv_saved in Hj.
    do 5 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn; tauto|]);
      destruct j; cbn in Hj; discriminate Hj. }
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
  prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (18%bv : bv 5) P18.
  prreg HS (19%bv : bv 5) P19.
  assert (Thi : forall r, 20 <= r <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. assert (Hr8 : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    (rewrite (st_ok_restrict_reg SEGS (w_H W) E _ _ _ HS); cbn [ms_regs];
     lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
       let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
     cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; apply EEo; reflexivity). }
  assert (Hin_rcf : In CS_rec_calls_free cmd_prog_syms)
    by (unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right])).
  rewrite (siv_sig CS_rec_calls_free SIGP Hin_rcf).
  replace (cmd_af CS_rec_calls_free) with AF_rec_calls_free by (vm_compute; reflexivity).
  eapply (siv_E_rcf HY0 HJG ly S W regs mem md ch pl ledger line R O).
  { exact CX. }
  { exact HFRM. }
  { exact H16. }
  { exact HJ. }
  { exact KEEPC. }
  { exact HFc. }
  { unfold spZ at 1. rewrite P2, Usp, unsigned_lit_small by lia. lia. }
  { rewrite P1. unfold w64. f_equal; unfold SIV_RCF_RET, AF_sup_instance_verb; lia. }
  { rewrite P3, (EEo 3%nat 3%bv eq_refl). exact Hgp. }
  { rewrite P4, (EEo 4%nat 4%bv eq_refl). exact Htp. }
  { rewrite P8, ESp. reflexivity. }
  { rewrite P9, (EEo 10%nat 10%bv eq_refl). exact H10. }
  { rewrite P10, ESp. reflexivity. }
  { rewrite P11. reflexivity. }
  { rewrite P18, (EEo 11%nat 11%bv eq_refl). exact H11. }
  { rewrite P19, ESB'. reflexivity. }
  { exact Thi. }
Qed.

End e.
End f.
End d.
