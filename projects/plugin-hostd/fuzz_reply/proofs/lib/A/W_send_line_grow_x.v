(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the growth half of a data round of fuzz_reply's ASan send_line loop, with
   run tactics and block lemmas restated from W_send_line_loop.v, W_gsaddb.v and W_drain_top.v. *)
(* Modified by Theorem Labs, 2026-10: the ARx-generic twin of lib/A/W_send_line_grow.v (that file is not edited), in
   the room form: W_send_line_grow_cx_x.v sl_grow_stmt_x, from SLN_x at 0x82824 (A_sl_n) to the join 0x82850
   (A_sl_join), where the continuation takes SLM_x:
     run 1  0x82824 ld s3,260(s10) [g_nout]; ld a0,864(s8) [g_capout]; add s3,s2,s3;
            0x82830 bgeu a0,s3 (taken: refuted by SLN_x's capN < no + sent + n);
            ld a0,892(s4) [g_out]; slli s3,s3,1; mv a1,s3; 0x82840 jal realloc
     call   realloc(g_out, 2 (no + sent + n)): W_journal_x.v arealloc_cf_rule_x (AREALLOC), its forced success
            4096 <= res; the room it charges (2 + kr') is SLN_x's room for the rounds still owed (MT_rk counts this
            round's realloc as 2), its count premise follows from the entry's count premise (sl_pk = 2) through the
            two block permutations, and the room it leaves (kr') is SLM_x's
     run 2  0x82844 beqz a0 (decided by the fact 4096 <= res of the result atom); sd a0,892(s4) [g_out := res];
            sd s3,864(s8) [g_capout := 2 (no + sent + n)]; 0x82850.
   The two stores go through the hi atoms of s4 and s8 (plain stores, not PLdHi slots), so after the call the state
   is re-seated with two empty writable regions on A_HI 24 + 892 and A_HI 23 + 864.
   Over a generic allocator relation ARx with its laws: the AR walk's al_* reads are AR_laws_x's alx_* fields; the
   generic blocks law has no MALLOC_MAX bound, so a live block's request size is >= 1 by the shadow law over an empty
   range (gr_blk_req_pos_x) and the line's length is below alloc_ceiling (alx_blocks) where the AR walk read 2 ^ 32.
   The C3 peak lemma sl_tr_peak_grow (W_send_line_loop.v) is reused.
   The Section header is W_send_line_grow_cx_x.v's, verbatim. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require send_line_c send_line_b_c RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_frame W_sites W_contract W_send_line_cx W_send_line_datab_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_send_line_loop W_send_line_grow_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_tr_peak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_journal_x W_sites_x W_contract_x W_send_line_cx_x W_send_line_datab_cx_x W_send_line_grow_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
(* route R: the send_line contract texts at a world relation R (a Theorem Labs lane's W_send_line_xR.v) and SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_send_line_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* a Theorem Labs lane's HP0 ruling: the generic relation holds at the empty ghost list only *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* W_send_line_cx_x.v's header (W_send_line_grow_cx.v's is W_send_line_cx.v's) *)
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis HGR : forall a, inG (G_SL B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
(* The realloc site rule in its caller-context form (W_journal_x.v Section hc), as the top's ARE_x states it
   (CTX_AREALLOC, ACk0.v:45, holds [0x82844]); send_line hands the rule a cut chain (ch = []), so the trace is the
   return address alone (W7's ccd62d4c6f6 form). *)
Variable CTX_R : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_slr : In [BASE + AF_fr_send_line + 0x110] CTX_R.   (* realloc returns to 0x82844 *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
(* errno's 4 bytes in an 8-aligned zero-shadow range (W_contract.azs; W_drain_cx_x.v:189's form): the loop's errno
   stores need range_addressable of errno at an ARx state (W_contract_x.azs_range_addressable_x) *)
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV10 : VAL (A_OBJ 10) = rg_client_broken RG.
Hypothesis HV11 : VAL (A_OBJ 11) = rg_send_eintr RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HV13 : VAL (A_OBJ 13) = rg_nout RG.
Hypothesis HV14 : VAL (A_OBJ 14) = rg_capout RG.
Hypothesis HV15 : VAL (A_OBJ 15) = rg_out RG.
Hypothesis HH17 : VAL (A_HI 17) + 92 = rg_client_broken RG.
Hypothesis HH19 : VAL (A_HI 19) + 248 = rg_send_eintr RG.
Hypothesis HH21 : VAL (A_HI 21) + 140 = rg_send_max RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Hypothesis HH22 : VAL (A_HI 22) + 260 = rg_nout RG.
Hypothesis HH23 : VAL (A_HI 23) + 864 = rg_capout RG.
Hypothesis HH24 : VAL (A_HI 24) + 892 = rg_out RG.
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)].

(* the run chain is W_journal_x's, whose journal carries the two ghost lists Hp / Hpc among the inferred arguments
   (16 holes in place of 14, W_kit_x.v paj_run_tok_x) *)
Let RUN := paj_run_x_x B PST ARx LAWS (G_SL B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_SL B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

(* W_send_line_loop.v's run tactics (section-local there, so restated): one round's fuel, the G_SL membership of a
   writable window, and the empty window.  The run chain is W_journal_x's: 16 holes in place of 14. *)
Ltac ing_tac := unfold G_SL; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ].
Ltac lrun RUN HS HJ SHOK Bspan :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUN with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_runN_pi_tok tpi tw K Bx Bspan SH L_FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi_tok tpi tw K Bx Bspan SH L_FUEL ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env val _ E |- _ => HEI | _ => fail "lrun: no img_env" end in
eapply (RUN W L_FUEL E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(repeat match goal with H : _ |- _ => clear H end; unfold A_LIM; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok HS HJ SHOK ]
end end
end
end.
Ltac lrun_to RUNTO HS HJ SHOK Bspan stop :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUNTO with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_pi_tok tpi tw K Bx Bspan SH L_FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_pi_tok tpi tw K Bx Bspan SH L_FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env val _ E |- _ => HEI | _ => fail "lrun_to: no img_env" end in
eapply (RUNTO W L_FUEL stop E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(repeat match goal with H : _ |- _ => clear H end; unfold A_LIM; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok HS HJ SHOK ]
end end
end
end.
Ltac awr_empty :=
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; intros a Ha; exfalso; clear - Ha; lia.
Ltac awr_g m H :=
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
  lazymatch goal with BVE : forall _, _ -> base_val _ _ = _ |- _ =>
    rewrite (BVE m) by (repeat match goal with H : _ |- _ => clear H end; unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia) end;
  intros a Ha; clear - Ha H; ing_tac.

(* ---- the symbolic state at 0x82824 ----
   s4, s8, s10 are the listing's hi atoms (the three PLdHi slots load through them); g_nout, g_capout and g_out are
   three regions whose values are the extra atoms 32, 33, 34 (the stores after the call go through two other,
   empty regions on the hi atoms; see sl_grow). *)
Definition gr_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms 20%bv (SOff (A_HI 24) 0)) 24%bv (SOff (A_HI 23) 0)) 26%bv (SOff (A_HI 22) 0).
Definition gr_nout : YP09.region := YP09.mkRegion (Some (A_OBJ 13)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition gr_cap : YP09.region := YP09.mkRegion (Some (A_OBJ 14)) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition gr_out : YP09.region := YP09.mkRegion (Some (A_OBJ 15)) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition gr_regions : smem := [gr_nout; gr_cap; gr_out].
Definition gr_facts : facts :=
mkFacts [ (32%nat, mkAF 0 (2^47) 0); (33%nat, mkAF 0 (2^47) 0); (34%nat, mkAF 0 (2^47) 0);
  (A_OBJ 13, OBJF); (A_OBJ 14, OBJF); (A_OBJ 15, OBJF);
  (A_HI 22, HIF); (A_HI 23, HIF); (A_HI 24, HIF) ] [] [].
Definition ss_G : sstate := mkSS A_sl_n gr_regs gr_regions None gr_facts.
Definition gr_extra (no' capN outN : Z) : list word := map (Z_to_bv 64) [no'; capN; outN].

Lemma gr_seat : forall (WN : world SEGS) regsN memN no' capN outN,
getr regsN 20 = w64 (VAL (A_HI 24)) -> getr regsN 24 = w64 (VAL (A_HI 23)) -> getr regsN 26 = w64 (VAL (A_HI 22)) ->
val_mem SEGS (arm WN memN) (rg_nout RG) 8 no' ->
val_mem SEGS (arm WN memN) (rg_capout RG) 8 capN -> awr WN memN (rg_capout RG) 8 ->
val_mem SEGS (arm WN memN) (rg_out RG) 8 outN -> awr WN memN (rg_out RG) 8 ->
0 <= no' <= 2 ^ 47 -> 0 <= capN <= 2 ^ 47 -> 0 <= outN <= 2 ^ 47 ->
st_ok_pi SEGS VAL (Eimg (Ereg regsN (gr_extra no' capN outN))) ss_G
(restrict (w_H WN) (mkst regsN (Z_to_bv 64 (BASE + A_sl_n)) memN (seg_rom SEGS))).
Proof.
intros WN regsN memN no' capN outN R20 R24 R26 Vno Vcap Wcap Vout Wout Rno Rcap Rout.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsN (gr_extra no' capN outN))).
assert (E32 : ew E 32 = Z_to_bv 64 no') by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsN _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 capN) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsN _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 outN) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsN _ 2)).
assert (UV : forall n, (A_TEXT <= n < A_LIM)%nat -> bv_unsigned (ew E n) = VAL n).
{ intros n Hn. subst E. rewrite Eimg_img by exact Hn. apply unsigned_lit_small. apply pa_val_range. }
assert (BV : forall n, (A_TEXT <= n < A_LIM)%nat -> base_val E (Some n) = VAL n).
{ intros n Hn. cbn [base_val]. exact (UV n Hn). }
assert (SVH : forall n, (A_TEXT <= n < A_LIM)%nat -> sv_denot E (SOff n 0) = w64 (VAL n)).
{ intros n Hn. cbn [sv_denot]. rewrite (UV n Hn). rewrite Z.add_0_r. reflexivity. }
pose proof (pa_obj_img 13 ltac:(lia)) as Q13. pose proof (pa_obj_img 14 ltac:(lia)) as Q14.
pose proof (pa_obj_img 15 ltac:(lia)) as Q15.
unfold ss_G. apply pa_entry_st_ok_full.
- unfold gr_regs.
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 22)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R26].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 23)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R24].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 24)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R20].
  subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold gr_regions, gr_nout, gr_cap, gr_out.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (BV (A_OBJ 13)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite HV13.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_nout RG) 0 8 (SOff 32 0) no');
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Vno.
  + rewrite (BV (A_OBJ 14)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite HV14.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wcap; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_capout RG) 0 8 (SOff 33 0) capN);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Vcap.
  + rewrite (BV (A_OBJ 15)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite HV15.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wout; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_out RG) 0 8 (SOff 34 0) outN);
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Vout.
- apply pairwise_disjoint_of_extents.
  unfold gr_regions, gr_nout, gr_cap, gr_out, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (BV (A_OBJ 13)), (BV (A_OBJ 14)), (BV (A_OBJ 15)) by (unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia).
  rewrite HV13, HV14, HV15.
  pose proof (sl_rgd B RG HRGD 7 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D78.
  pose proof (sl_rgd B RG HRGD 7 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D79.
  pose proof (sl_rgd B RG HRGD 8 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D89.
  cbn [nth] in D78, D79, D89. unfold zdisj in D78, D79, D89. cbn [fst snd] in D78, D79, D89.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [ exact I | lia ].
- split; [|split; [exact I | exact I]].
  cbn [gr_facts f_atoms atoms_ok]. unfold afact_ok, OBJF, HIF. cbn [af_lo af_hi af_al2].
  rewrite E32, E33, E34.
  rewrite (UV (A_OBJ 13)), (UV (A_OBJ 14)), (UV (A_OBJ 15)), (UV (A_HI 22)), (UV (A_HI 23)), (UV (A_HI 24))
    by (unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia).
  rewrite !unsigned_lit_small by lia.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  rewrite HV13 in Q13. rewrite HV14 in Q14. rewrite HV15 in Q15.
  repeat match goal with |- _ /\ _ => split end; try exact I;
  solve [ clear - Rno Rcap Rout Q13 Q14 Q15 HV13 HV14 HV15 HH22 HH23 HH24; lia ].
Qed.

(* ---- small arithmetic of symbolic values ---- *)
Lemma gr_U_add : forall E x y, 0 <= U E x + U E y < 2 ^ 64 -> U E (SAlu ALU_ADD x y) = U E x + U E y.
Proof.
intros E x y H. rewrite U_SAlu. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia.
Qed.
Lemma gr_U_sll1 : forall E x, 0 <= U E x * 2 < 2 ^ 64 -> U E (SAlu ALU_SLL x (SLit 1)) = U E x * 2.
Proof.
intros E x H. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 1) 63) with 1.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. apply zcanon_id. unfold M64. lia.
Qed.

(* ---- the live blocks (W_gsaddb.v gb_ablocks_nodup; W_drain_top.v dt_sep_head, dt_grow_perm), over ARx ---- *)
(* a live block's request size is at least 1: cgif's blocks law ends with `0 <= n < MALLOC_MAX` (YG0d.v:438), which
   the generic ARx_blocks_law drops; the shadow law over an empty range gives it (the W7 lane's blk_req_pos_x proof,
   a working branch f1f2f35d92a lib/A/W_w7_x.v, which A's top does not carry) *)
Lemma gr_blk_req_pos_x : forall ly S Hp W mem md p n,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 1 <= req_size n.
Proof.
intros ly S Hp W mem md p n HAR Hin.
destruct (Z_lt_le_dec 0 (req_size n)) as [Q|Q]; [lia|]. exfalso.
destruct (alx_shadow _ _ _ LAWS ly S Hp W mem md p n HAR Hin ltac:(intros h _ Hh; lia)) as [(_ & Q0 & _) _].
revert Q Q0. unfold req_size. destruct (Z.eqb_spec n 0); cbv beta iota; intros; lia.
Qed.
(* cgif YCbq.v:2587 sep_blocks_perm over YGcallx.sep_blocks_pos_x (the W7 lane's sep_blocks_perm_x proof, same file) *)
Lemma gr_sep_blocks_perm_x : forall ly S Hp W mem md x y l,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (x :: y :: l) ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S Hp W mem md x y l HAR HP.
assert (Hx : In x (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
apply in_split in Hx as (a1 & a2 & E1).
assert (HP2 : Permutation (a1 ++ a2) (y :: l)).
{ apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ a1 a2 x). rewrite <- E1. apply Permutation_sym. exact HP. }
assert (Hy : In y (a1 ++ a2)) by (eapply Permutation_in; [apply Permutation_sym; exact HP2 | left; reflexivity]).
apply in_app_or in Hy as [Hy | Hy]; apply in_split in Hy as (b1 & b2 & E2).
- assert (Hd : zdisjoint (block_rng y) (block_rng x)).
  { eapply (YGcallx.sep_blocks_pos_x SEGS B ARx LAWS ly S Hp W mem md y x b1 b2 a2 HAR).
    rewrite E1, E2, <- app_assoc. reflexivity. }
  unfold zdisjoint in *. lia.
- eapply (YGcallx.sep_blocks_pos_x SEGS B ARx LAWS ly S Hp W mem md x y a1 b1 b2 HAR).
  rewrite E1, E2. reflexivity.
Qed.
Lemma gr_ablocks_nodup_x : forall ly S Hp W mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S Hp W mem md HAR.
assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
{ apply Forall_forall. intros [pp nn] Hin.
  cbn [snd]. exact (gr_blk_req_pos_x ly S Hp W mem md pp nn HAR Hin). }
destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hq _]. apply pairwise_app_l in Hq as [Hq _].
revert Hpos Hq. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hq; [constructor|].
inversion Hpos as [|b0 l0 Hb Hl]; subst.
cbn [map pairwise] in Hq. destruct Hq as [Hf Hq]. constructor; [|exact (IH Hl Hq)].
intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Lemma gr_sep_head_x : forall ly S Hp (W : world SEGS) m md x L y,
ARx ly S Hp W m md -> Permutation (ablocks B ly S) (x :: L) -> In y L ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S Hp W m md x L y HAR HP Hy. destruct (in_split _ _ Hy) as (l1 & l2 & ->).
apply (gr_sep_blocks_perm_x ly S Hp W m md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle.
Qed.

(* ---- the room round ---- *)
(* MT_rk (W_contract_x.v, the allocator-call count) is a meter *)
Lemma gr_rk_laws : ameter_laws MT_rk.
Proof. constructor; cbn [mo_ok mo_le mo_malloc mo_free MT_rk]; intros; solve [exact I | lia]. Qed.
(* g_out's block list holds at most one block *)
Lemma gr_acnt_aout : forall P cap out, (ReplyCnt.acnt P (aout_blks cap out) <= 1)%nat.
Proof.
intros P cap out. unfold aout_blks. destruct (cap =? 0); [rewrite acnt_nil; lia|].
rewrite acnt_cons, acnt_nil. cbn [snd]. destruct (P cap); lia.
Qed.
(* the count premise of a realloc at a round's state: the round's live blocks are g_out's (at most one) and the rest
   the entry had, so each live count is at most one above the entry's, under sl_pk = 2 *)
Lemma gr_cnt_round : forall l0 l1 cap out capN outN rest,
cnt_ok_pk RP sl_pk l0 -> Permutation l0 (aout_blks cap out ++ rest) -> Permutation l1 (aout_blks capN outN ++ rest) ->
cnt_ok RP l1.
Proof.
intros l0 l1 cap out capN outN rest H HQ0 HQ1. unfold cnt_ok.
eapply cnt_ok_pk_mono; [|exact H].
intros P. unfold sl_pk. cbv beta.
rewrite (ReplyCnt.acnt_perm P _ _ HQ0), (ReplyCnt.acnt_perm P _ _ HQ1), !ReplyCnt.acnt_app.
pose proof (gr_acnt_aout P capN outN). lia.
Qed.
(* the live blocks after the realloc of g_out: the new block, then the rest *)
Lemma gr_perm : forall ly1 S1 ly2 S2 capN outN rest res nc,
Permutation (ablocks B ly1 S1) (aout_blks capN outN ++ rest) ->
(capN = 0 -> outN = 0) -> (capN <> 0 -> outN <> 0) ->
(outN = 0 -> Permutation (ablocks B ly2 S2) ((res, nc) :: ablocks B ly1 S1)) ->
(outN <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (outN, capN) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, nc) :: l1 ++ l2)) ->
Permutation (ablocks B ly2 S2) ((res, nc) :: rest).
Proof.
intros ly1 S1 ly2 S2 capN outN rest res nc HP Hz Hnz HA HB'.
unfold aout_blks in HP. revert HP. destruct (capN =? 0) eqn:Ec; intros HP; cbn [app] in HP.
- apply Z.eqb_eq in Ec. eapply Permutation_trans; [exact (HA (Hz Ec))|]. apply perm_skip. exact HP.
- apply Z.eqb_neq in Ec. destruct (HB' (Hnz Ec)) as (l1 & l2 & E1 & P2).
  eapply Permutation_trans; [exact P2|]. apply perm_skip.
  apply (Permutation_cons_inv (a := (outN, capN))).
  eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- E1.
  first [exact HP | exact (Permutation_sym HP)].
Qed.
(* the live bytes after the call: the old block of capN bytes (none when g_out is NULL) freed, the new one of nc
   bytes live (W_tr_peak.v bb_after_realloc0 / bb_after_realloc) *)
Lemma gr_bb : forall ly1 S1 ly2 S2 capN outN res nc,
(outN = 0 -> capN = 0) ->
(outN = 0 -> Permutation (ablocks B ly2 S2) ((res, nc) :: ablocks B ly1 S1)) ->
(outN <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (outN, capN) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, nc) :: l1 ++ l2)) ->
blocks_bytes S2 = blocks_bytes S1 - capN + nc.
Proof.
intros ly1 S1 ly2 S2 capN outN res nc Hz HA HB'.
destruct (Z.eq_dec outN 0) as [Ho|Ho].
- rewrite (W_tr_peak.bb_after_realloc0 B ly1 S1 ly2 S2 res nc (HA Ho)), (Hz Ho). lia.
- exact (W_tr_peak.bb_after_realloc B ly1 S1 ly2 S2 outN capN res nc (HB' Ho)).
Qed.

(* ---- bytes across two worlds (W_drain_top.v dt_wr_kept2, dt_img_wr, dt_garr8_shift, dt_newbuf) ---- *)
Lemma gr_in_zr_dec : forall x r, {in_zr x r} + {~ in_zr x r}.
Proof.
intros x r. unfold in_zr. destruct (Z_le_gt_dec (fst r) x); destruct (Z_lt_ge_dec x (fst r + snd r));
[left; lia | right; lia | right; lia | right; lia].
Qed.
Lemma gr_wr_kept2 : forall (H H2 : word -> bool) (m m2 : word -> option byte) a,
(apresent H m a -> apresent H2 m2 a) -> writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H2 m2) a.
Proof.
intros H H2 m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; destruct (H2 (Z_to_bv 64 a)) eqn:EH2; intros Hw.
- exact Hw.
- destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
- destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [|exact Hw].
  destruct (Hp (conj EH (ex_intro _ b Em))) as [Hc _]. rewrite Hc in EH2. discriminate.
- destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
  + destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
  + destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma gr_img_wr : forall (W : world SEGS) m a,
in_img SEGS a -> ~ in_rom SEGS a -> aview SEGS (w_H W) m a <> None -> writable_at SEGS (arm W m) a.
Proof.
intros W m a Hi Hr Hv.
assert (Ha : bv_unsigned (Z_to_bv 64 a) = a)
  by (apply unsigned_lit_small; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia).
assert (HA : w_H W (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
assert (Hfn : find_segment SEGS a 1 <> None) by (apply find_segment_img; exact Hi).
destruct (find_segment SEGS a 1) as [sg|] eqn:Hf; [|exfalso; exact (Hfn eq_refl)].
destruct (find_segment_some_spec _ _ _ _ Hf) as (Hin & Hlo & Hhi).
assert (Hw : seg_writable sg = true).
{ destruct (seg_writable sg) eqn:E; [reflexivity|]. exfalso. apply Hr. exists sg.
  split; [exact Hin|]. split; [exact E|]. lia. }
revert Hv. unfold aview, writable_at, arm, mbyte, wview, mrestrict, seg_rom, memory_read.
rewrite HA. rewrite ?Ha.
destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; discriminate|].
change (Z.of_N 1) with 1. rewrite Hf. cbv beta iota zeta. rewrite Hw. cbv beta iota.
destruct (seg_readable sg); [|intros H; exfalso; apply H; reflexivity].
change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
destruct (segment_byte_at _ _); [intros _; discriminate | intros H; exfalso; apply H; reflexivity].
Qed.
Lemma gr_vm_kept : forall (W W' : world SEGS) m m' a n v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W') m') a n v.
Proof.
intros W W' m m' a n v HK Hv k Hk.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat k)); [exact (Hv k Hk)|].
apply HK. lia.
Qed.
Lemma gr_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.
Lemma gr_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.
Lemma gr_bz_bv8 : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof.
intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. reflexivity.
Qed.
Lemma gr_garr8_at : forall mem b l b', garr8 SEGS mem b l -> b = b' -> garr8 SEGS mem b' l.
Proof. intros mem b l b' H <-. exact H. Qed.
Lemma gr_garr8_kept : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof.
intros W m W' m' a l H KL. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (KL x Hx).
Qed.
Lemma gr_garr8_shift : forall (W : world SEGS) m (W' : world SEGS) m' a a' l,
garr8 SEGS (arm W m) a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS (w_H W') m' (a' + i) = aview SEGS (w_H W) m (a + i)) ->
garr8 SEGS (arm W' m') a' l.
Proof.
intros W m W' m' a a' l H K j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. specialize (Hv k Hk). rewrite <- Hv.
replace (Z.of_nat k) with 0 by lia. rewrite !Z.add_0_r. unfold arm.
pose proof (K (Z.of_nat j) ltac:(lia)) as E. unfold aview in E.
destruct (mbyte SEGS (mrestrict (w_H W') m') (a' + Z.of_nat j)) as [b'|],
  (mbyte SEGS (mrestrict (w_H W) m) (a + Z.of_nat j)) as [b|]; cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma gr_bzs_of_garr8 : forall mem a (l : list Z), garr8 SEGS mem a l -> bzs (map (Z_to_bv 8) l) = l.
Proof.
intros mem a l H. unfold bzs.
apply (nth_ext _ _ 0 0); [rewrite !length_map; reflexivity|].
intros j Hj. rewrite !length_map in Hj.
rewrite (nth_indep (map bz (map (Z_to_bv 8) l)) 0 (bz (Z_to_bv 8 0))) by (rewrite !length_map; exact Hj).
rewrite List.map_nth, List.map_nth, gr_bz_bv8. destruct (H j Hj) as [_ Hr]. apply Z.mod_small. exact Hr.
Qed.
(* g_out's new block: the copy of the old block's cap bytes (O ++ junk), then the block's own bytes *)
Lemma gr_newbuf : forall (W1 : world SEGS) m1 (W2 : world SEGS) m2 (O' : list byte) no' capN outN res nc,
((capN = 0 /\ no' = 0) \/
 (0 < capN /\ exists junk, Z.of_nat (length junk) = capN - no' /\ garr8 SEGS (arm W1 m1) outN (bzs (O' ++ junk)))) ->
Z.of_nat (length O') = no' -> 0 <= capN <= nc ->
(0 < capN -> forall i, 0 <= i < capN -> aview SEGS (w_H W2) m2 (res + i) = aview SEGS (w_H W1) m1 (outN + i)) ->
(forall x, res <= x < res + nc -> apresent (w_H W2) m2 x) ->
exists junk, Z.of_nat (length junk) = nc - no' /\ garr8 SEGS (arm W2 m2) res (bzs (O' ++ junk)).
Proof.
intros W1 m1 W2 m2 O' no' capN outN res nc Hb HU Hc Hcp Hpr.
assert (Hfresh : forall a k, res <= a -> a + Z.of_nat k <= res + nc ->
  exists l : list byte, length l = k /\ garr8 SEGS (arm W2 m2) a (bzs l)).
{ intros a k H1 H2.
  destruct (garr8_of_present SEGS (arm W2 m2) a k) as (l & Hl & Hg).
  { intros x Hx. destruct (Hpr x ltac:(lia)) as (Hh & bb & Hbb). exists bb.
    unfold arm, mrestrict. rewrite Hh, Hbb. reflexivity. }
  exists (map (Z_to_bv 8) l). split; [rewrite length_map; exact Hl|].
  rewrite (gr_bzs_of_garr8 _ _ _ Hg). exact Hg. }
destruct Hb as [(Hc0 & Hu0) | (Hcp0 & junk0 & HJk & Hg)].
- assert (HU0 : O' = []) by (destruct O'; [reflexivity | cbn [length] in HU; lia]).
  assert (Hk : res + Z.of_nat (Z.to_nat nc) <= res + nc) by (rewrite Z2Nat.id by lia; lia).
  destruct (Hfresh res (Z.to_nat nc) ltac:(lia) Hk) as (l & Hl & Hg).
  exists l. rewrite HU0, Hu0. cbn [app]. split; [rewrite Hl, Z2Nat.id by lia; lia | exact Hg].
- assert (Hk : res + capN + Z.of_nat (Z.to_nat (nc - capN)) <= res + nc)
    by (rewrite Z2Nat.id by lia; lia).
  destruct (Hfresh (res + capN) (Z.to_nat (nc - capN)) ltac:(lia) Hk) as (l & Hl & Hg2).
  exists (junk0 ++ l). split; [rewrite length_app, Nat2Z.inj_add, Hl, Z2Nat.id by lia; lia|].
  rewrite app_assoc, gr_bzs_app. apply garr8_app. split.
  + apply (gr_garr8_shift W1 m1 W2 m2 outN res); [exact Hg|].
    intros i Hi. apply (Hcp Hcp0). rewrite gr_bzs_len, length_app, Nat2Z.inj_add in Hi. lia.
  + apply (gr_garr8_at _ _ _ _ Hg2). rewrite gr_bzs_len, length_app, Nat2Z.inj_add. lia.
Qed.

(* The entry's ghost list is HpE (the proof's own `Hp` names stay as they were); kr is the entry's room budget. *)
Theorem sl_grow_x : sl_grow_stmt_x B PST ARx MT RP MMAX RG.
Proof.
unfold sl_grow_stmt_x. intros regsE ly S HpE W mem md c O mx no cap out line Bl WN regsN memN mdN sent n kr HN K.
unfold SLN_x in HN. cbv zeta in HN.
destruct HN as (lyN & SN & HpN & kN & evL & capN & outN & spent & rest & HJ & Hsp & H3 & H4 & Hgp & Htp & HraE & HR &
  M8 & M16 & HSV & Hcl & Hbr & Hdd & Hsent & Hn & Hev & HOUT & Hgrow & HGL & Hline0 & Hline1 & HROM & HLOK & HLG &
  Hcapq & HMM & HLM & HAPK & HMOK & HMLE & HCOST & HPerm0 & HPerm1 & HFR & HRM & HCNT).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & Hag) & _).
pose proof HJi as (HARN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresN & HstkN & _).
pose proof HstkN as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
rewrite !Z.add_0_r in Hal16, Hstk0, Hslo, Hshi, Hbot, Htop2, HpresN.
assert (WS : SL_STK = 16512) by reflexivity.
assert (HSF : SL_FRAME = 128) by reflexivity.
pose proof HOUT as (Vmx & Wmx & Vno & Wno & Vcap & Wcap & Vout & Wout & Vcl & Wcl & Vbr & Wbr &
  Vdd & Wdd & Vei & Wei & Vev & Wev & Rev & Hclr & Hbrr & Hddr & Heir & Hmxr & HlenO & Hblk).
cbn [ct_cl ct_br ct_dd ct_ei ct_ev] in Vmx, Vno, Vcap, Vout, Vcl, Vbr, Vdd, Vei, Vev, Rev, Hclr, Hbrr, Hddr, Heir.
assert (Rcapout : 0 <= capN /\ 0 <= outN /\ no + sent <= 2 ^ 47 /\ capN <= 2 ^ 47 /\ outN <= 2 ^ 47).
{ destruct Hblk as [(Hc0 & Ho0 & Hn0) | (Hc1 & Hn1 & Hin1 & _)].
  - repeat split; lia.
  - destruct (alx_blocks _ _ _ LAWS lyN SN HpN WN memN mdN outN capN HARN Hin1) as (_ & Hp4 & Hpc & _).
    assert (Hrq : req_size capN = capN) by (unfold req_size; destruct (Z.eqb_spec capN 0); lia).
    rewrite Hrq in Hpc. repeat split; lia. }
destruct Rcapout as (Rc0 & Ro0 & Rn47 & Rc47 & Ro47).
set (len := Z.of_nat (length Bl)) in *.
pose proof HR as HRc.
destruct HRc as (R8 & R9 & R18 & R22 & R23 & R20 & R21 & R24 & R25 & R26 & R27).
pose proof (gr_seat WN regsN memN (no + sent) capN outN R20 R24 R26 Vno Vcap Wcap Vout Wout
  ltac:(clear - Rn47 HlenO; lia) ltac:(clear - Rc0 Rc47; lia) ltac:(clear - Ro0 Ro47; lia)) as HS.

remember (Eimg (Ereg regsN (gr_extra (no + sent) capN outN))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (BVE : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val E (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEI m Hm)).
assert (EA : forall i, (i < 32)%nat -> ew E i = getr regsN (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew].
  destruct (Nat.ltb_spec i 32); [reflexivity | lia]. }
assert (E32 : ew E 32 = w64 (no + sent)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsN _ 0)).
assert (E33 : ew E 33 = w64 capN) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsN _ 1)).
assert (E34 : ew E 34 = w64 outN) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsN _ 2)).
clear HE.
assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H WN) memN)) by constructor.
lrun RUN HS HJ SHOK LBspan.
{ unfold ss_G; cbn [ss_mem]; unfold gr_regions, gr_nout, gr_cap, gr_out.
  apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 14) HV14|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 15) HV15|].
  apply awr_ok_x_nil. }

psrr_branch_tok RUN BR HS SHOK LBspan.

all: assert (E18 : ew E 18 = w64 n) by (rewrite (EA 18%nat ltac:(lia)); exact R18).
all: assert (Hnn : 0 < n <= len - sent) by (rewrite Hn; apply sl_n_range; clear - Hmxr Hsent; lia).
all: assert (Hlen63 : len < 2 ^ 63) by (clear - Hline0 Hline1; lia).
all: assert (UADD : U E (SAlu ALU_ADD (SOff 18 0) (SOff 32 0)) = n + (no + sent))
  by (rewrite U_SAlu, (U_atom E 18 n E18), (U_atom E 32 (no + sent) E32) by (clear - Hnn Hsent Hlen63 Rn47 HlenO; lia);
      cbn [zalu_raw]; apply zcanon_id; unfold M64; clear - Hnn Hsent Hlen63 Rn47 HlenO; lia).
1: { exfalso. rewrite branch_geu_U, (U_atom E 33 capN E33), UADD in Hc by (clear - Rc0 Rc47; lia).
  apply negb_true_iff, Z.ltb_ge in Hc. clear - Hc Hgrow; lia. }
rewrite branch_geu_U, (U_atom E 33 capN E33), UADD in Hc by (clear - Rc0 Rc47; lia).
assert (N14 : VAL 255%nat = rg_capout RG) by exact HV14.
assert (N15 : VAL 256%nat = rg_out RG) by exact HV15.
lrun RUN HS HJ SHOK LBspan.
{ apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 255%nat N14|].
  apply awr_ok_x_cons_g; [awr_g 256%nat N15|].
  apply awr_ok_x_nil. }

lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.

(* the line lies below alloc_ceiling: in a live block (alx_blocks; the generic blocks law has no MALLOC_MAX bound,
   where the AR walk read len < 2 ^ 32) or in the image *)
assert (HlenA : len < alloc_ceiling).
{ destruct HLOK as [H0 | [(q & m & Hin & _ & Hq & Hqm) | (Himg & _ & _)]].
  - clear - H0 Hsent; lia.
  - destruct (alx_blocks _ _ _ LAWS lyN SN HpN WN memN mdN q m HARN Hin) as (_ & Hq4 & Hqc & _).
    clear - Hq Hqm Hq4 Hqc; lia.
  - pose proof (pa_img_range _ (Himg line ltac:(clear - Hsent; lia))) as P1.
    pose proof (pa_img_range _ (Himg (line + len - 1) ltac:(clear - Hsent; lia))) as P2. clear - P1 P2 Hsent C1; lia. }
assert (Hlen47 : len < 2 ^ 47) by (clear - HlenA C1; lia).
set (NC := (no + sent + n) * 2) in *.
assert (HNC1 : 1 <= NC) by (unfold NC; clear - Hnn Hsent HlenO; lia).
pose proof (st_ok_restrict_reg _ _ _ _ _ 11%bv HS) as G11'.
lazymatch type of G11' with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in G11' end.
cbn [ms_regs restrict mkst] in G11'.
assert (G11 : getr (ms_regs ms1) 11 = w64 NC).
{ rewrite G11', denot_lit_U. unfold w64. f_equal.
  assert (U18 : U E (SOff 18 0) = n) by (apply (U_atom E 18 n E18); clear - Hnn Hlen47 Hsent; lia).
  assert (U32 : U E (SOff 32 0) = no + sent) by (apply (U_atom E 32 (no + sent) E32); clear - Rn47 HlenO; lia).
  assert (S18 : U E (SAlu ALU_SLL (SOff 18 0) (SLit 1)) = n * 2)
    by (rewrite gr_U_sll1; rewrite U18; clear - Hnn Hlen47 Hsent; lia).
  assert (S32 : U E (SAlu ALU_SLL (SOff 32 0) (SLit 1)) = (no + sent) * 2)
    by (rewrite gr_U_sll1; rewrite U32; clear - Rn47 HlenO; lia).
  rewrite gr_U_add; rewrite S18, S32; unfold NC; clear - Hnn Hlen47 Hsent Rn47 HlenO; lia. }

(* ---- the model: this round grows g_out to NC ---- *)
assert (Hmx0 : 0 <= mx) by (clear - Hmxr; lia).
assert (Hrem : 0 < len - sent) by (clear - Hsent; lia).
assert (GROW : (capN <? no + sent + sl_n mx (len - sent)) = true) by (rewrite <- Hn; apply Z.ltb_lt; exact Hgrow).
rewrite (sl_max_run_step mx (no + sent) capN (len - sent) Hmx0 Hrem), GROW in HMM.
(* C3: the peak of the rest of the trace gives realloc's room (HLR) and, the old block freed, the peak after it *)
destruct (sl_tr_peak_grow mx (no + sent) capN (len - sent) (blocks_bytes SN) LIVE_MAX Hmx0 Hrem
  (proj1 (Z.ltb_lt _ _) GROW) HLM) as (HLR & HLM2).
rewrite (sl_cost_run_step MT mx (no + sent) capN (len - sent) Hmx0 Hrem), GROW in HCOST.
rewrite (sl_cost_run_step MT_rk mx (no + sent) capN (len - sent) Hmx0 Hrem), GROW in HRM.
rewrite (send_line_cap_step mx (no + sent) capN (len - sent) Hmx0 Hrem) in Hcapq.
unfold sl_capn in HCOST, HRM, Hcapq. rewrite GROW in HCOST, HRM, Hcapq.
rewrite <- Hn in HMM, HLR, HLM2, HCOST, HRM, Hcapq.
fold NC in HMM, HLR, HLM2, HCOST, HRM, Hcapq.
pose proof (sl_cost_run_nonneg MT (Z.to_nat (len - sent - n)) mx (no + sent + n) NC (len - sent - n) MTL
  ltac:(clear - Hsent Hnn HlenO; lia) Hmx0) as HCnn.
assert (HmoN : 0 <= mo_malloc MT NC + mo_free MT).
{ pose proof (mo_malloc_nonneg MT MTL NC ltac:(unfold NC; clear - Hsent Hnn HlenO; lia)).
  pose proof (mo_free_nonneg MT MTL). lia. }
(* the room: MT_rk counts this round's realloc as 2, the rounds after it leave RR on top of kr *)
pose proof (sl_cost_run_nonneg MT_rk (Z.to_nat (len - sent - n)) mx (no + sent + n) NC (len - sent - n) gr_rk_laws
  ltac:(clear - Hsent Hnn HlenO; lia) Hmx0) as HRnn.
change (mo_malloc MT_rk NC + mo_free MT_rk) with 2 in HRM.
set (RR := sl_cost_run MT_rk (Z.to_nat (len - sent - n)) mx (no + sent + n) NC (len - sent - n)) in HRM, HRnn.
assert (HRM1 : rp_RM RP SN (2 + (Z.to_nat RR + kr))).
{ replace (2 + (Z.to_nat RR + kr))%nat with (Z.to_nat (2 + RR) + kr)%nat by (clear - HRnn; lia). exact HRM. }
clear HRM.

(* ---- the old block of g_out: NULL exactly when g_capout is 0 ---- *)
assert (Hcz : capN = 0 -> outN = 0)
  by (intros Hcc; destruct Hblk as [(_ & Ho & _) | (Hc1 & _)]; [exact Ho | clear - Hcc Hc1; lia]).
assert (Hcnz : capN <> 0 -> outN <> 0 /\ In (outN, capN) (ablocks B lyN SN)).
{ intros Hcc. destruct Hblk as [(Hc0 & _) | (_ & _ & Hin1 & _)]; [contradiction|].
  destruct (alx_blocks _ _ _ LAWS lyN SN HpN WN memN mdN outN capN HARN Hin1) as (_ & Hp4 & _). split; [lia | exact Hin1]. }
assert (Hocz : outN <> 0 -> capN <> 0) by (intros Ho Hcc; exact (Ho (Hcz Hcc))).
assert (Hozc : outN = 0 -> capN = 0)
  by (intros Ho; destruct (Z.eq_dec capN 0) as [Hcc|Hcc]; [exact Hcc | exfalso; exact (proj1 (Hcnz Hcc) Ho)]).
pose proof (gr_ablocks_nodup_x lyN SN HpN WN memN mdN HARN) as NDN.
destruct HJ as (HSTK1 & HXO1 & (memS1 & HJi1 & HAG1) & HOUT1). rewrite !Z.add_0_r in HJi1.
assert (Hsp1 : spZ (ms_regs ms1) = spZ regsE + - SL_FRAME).
{ unfold spZ at 1. rewrite Q2, (EA 2%nat ltac:(lia)). change (bv_unsigned (getr regsN 2) = spZ regsE + - SL_FRAME).
  fold (spZ regsN). rewrite Hsp. lia. }
eapply SRr_bind.
{ eapply (AREALLOC WN (ms_regs ms1) (ms_mem ms1) SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out)) ly S HpE W memS1 md []
    lyN SN HpN _ kN outN capN NC (- SL_FRAME) _ [] (Z.to_nat RR + kr)%nat HJi1).
  - destruct (Z.eq_dec capN 0) as [Hcc | Hcc]; [left; exact (Hcz Hcc) | right; exact (proj2 (Hcnz Hcc))].
  - rewrite Q10, E34. reflexivity.
  - exact G11.
  - unfold NC in *. clear - HMM Hsent Hnn HlenO. lia.
  - clear - HLR. lia.
  - exact (gr_cnt_round _ _ cap out capN outN rest HCNT HPerm0 HPerm1).
  - exact Hsp1.
  - rewrite HSF. reflexivity.
  - rewrite HSF. lia.
  - rewrite WS, HSF. unfold ASTACK. lia.
  - eapply (aj_stack_room_x SEGS B PST ARx); [exact HJi1 | exact Hsp1 | rewrite WS, HSF; unfold ASTACK; lia].
  - rewrite Q3, (EA 3%nat ltac:(lia)). change (getr regsN 3 = w64 (as_gp B)). rewrite H3. exact Hgp.
  - rewrite Q4, (EA 4%nat ltac:(lia)). change (getr regsN 4 = w64 (as_tp B)). rewrite H4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - apply (achain_chain_pre lyN _ (spZ (ms_regs ms1)) (s0Z (ms_regs ms1)) [] (ms_regs ms1)).
    + apply achain_low. unfold s0Z. rewrite Q8, (EA 8%nat ltac:(lia)). change (bv_unsigned (getr regsN 8) < alloc_ceiling).
      rewrite R8. unfold w64. rewrite unsigned_lit_small by (clear - Hlen47 Hsent; lia). clear - HlenA C1. lia.
    + rewrite Hsp1. rewrite WS, HSF in *. clear - Hceil Hslo Hshi H47. lia.
    + reflexivity.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - (* the caller-context fact: the chain is cut, so the trace is the return address alone (HCTX_slr; W7's step,
       a working branch 7561b427559 lib/A/W_send_line_grow.v:614-618) *)
    unfold raZ. cbn [spine map]. rewrite Q1. rewrite unsigned_lit_small by lia.
    match goal with |- In [?x] _ =>
      replace x with (BASE + AF_fr_send_line + 0x110) by (try unfold AF_fr_send_line; try unfold BASE; ring) end.
    exact HCTX_slr.
  - exact HRM1.
  - intros Hp0 HinS i Hi.
    apply (Permutation_in _ HPerm0) in HinS. apply in_app_or in HinS. destruct HinS as [HinA | HinR].
    + exists (outN, outN + req_size capN). split; [|cbn [fst snd]; lia].
      unfold ablocks_fp. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ _ HinA).
    + exfalso. pose proof (Permutation_NoDup HPerm1 NDN) as ND1. unfold aout_blks in ND1.
      rewrite (proj2 (Z.eqb_neq capN 0) (Hocz Hp0)) in ND1. cbn [app] in ND1.
      apply NoDup_cons_iff in ND1 as [Hn1 _]. exact (Hn1 HinR).
  - apply (mok_station MT S SN (sl_cost MT c mx no cap len) spent _ MTL HMOK HMLE HmoN). clear - HCOST HCnn. lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & -> & HJ2i & HP2 & Hres10 & Hfrs2 & Hres4096 &
  HpermA & HpermB & Hcopy & Hkept2 & Hmle2 & HRM2 & Herr2 & Hpres2).

(* ---- after the call ---- *)
pose proof (proj1 HJi1) as HAR1.
pose proof (proj1 HJ2i) as HAR2.
destruct Hkept2 as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (gr_perm lyN SN ly2 S2 capN outN rest res NC HPerm1 Hcz (fun h => proj1 (Hcnz h)) HpermA HpermB) as P2.
assert (HRIN2 : In (res, NC) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym P2)); left; reflexivity).
assert (RQN : req_size NC = NC) by (unfold req_size; destruct (Z.eqb_spec NC 0) as [E0|E0]; [exfalso; unfold NC in E0; clear - E0 Hnn Hsent HlenO; lia | reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 res NC HAR2 HRIN2) as (Hr16 & Hr4096 & Hrceil & _ & Hrpres & _).
rewrite RQN in Hrceil, Hrpres.
assert (NOWN : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B lyN SN a /\ ~ aowned B ly2 S2 a).
{ intros a Hi Hno. split; intros Ho; apply Hno;
    [exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR1 Hi) Ho) | exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR2 Hi) Ho)]. }
assert (NBLK : forall a, in_img SEGS a -> ~ ((res <= a < res + req_size NC) \/ (outN <> 0 /\ outN <= a < outN + req_size capN))).
{ intros a Hi [Hr | (Hz & Ho)].
  - exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res NC a HAR2 HRIN2 Hr Hi).
  - exact (blk_img_x SEGS B ARx LAWS lyN SN HpN WN (ms_mem ms1) _ outN capN a HAR1 (proj2 (Hcnz (Hocz Hz))) Ho Hi). }
assert (GK : forall a, inG (G_SL B RG) a \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] a ->
  ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H WN) (ms_mem ms1) a /\
  (apresent (w_H WN) (ms_mem ms1) a -> apresent (w_H W2) mem2 a)).
{ intros a Hg He. assert (IO : in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B))
    by (destruct Hg as [Hg|Hg]; [exact (conj (proj1 (HG a Hg)) (proj1 (proj2 (HG a Hg)))) | exact (conj (proj1 (HGO a Hg)) (proj1 (proj2 (HGO a Hg))))]).
  destruct IO as [Hi Hno]. destruct (NOWN a Hi Hno) as [N1 N2].
  split; [exact (K3 a Hi Hno He) | exact (Hpres2 a Hi N1 N2 He (NBLK a Hi))]. }
pose proof (sl_rgd B RG HRGD 7 10 ltac:(lia) ltac:(lia) ltac:(lia)) as DE7.
pose proof (sl_rgd B RG HRGD 8 10 ltac:(lia) ltac:(lia) ltac:(lia)) as DE8.
pose proof (sl_rgd B RG HRGD 9 10 ltac:(lia) ltac:(lia) ltac:(lia)) as DE9.
cbn [nth] in DE7, DE8, DE9. unfold zdisj in DE7, DE8, DE9. cbn [fst snd] in DE7, DE8, DE9.
assert (N13 : VAL 254%nat = rg_nout RG) by exact HV13.
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 ([] : list nat) HS2.

match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (Ea40 : ew Ea 40 = w64 res) by (rewrite HEa; exact Hres10).
clear HEa.
(* g_capout and g_out are written through s8 and s4 (0x82848 / 0x8284c store through the hi atoms): two empty
   writable regions on those atoms *)
pose proof (pa_obj_img 14 ltac:(lia)) as Q14. pose proof (pa_obj_img 15 ltac:(lia)) as Q15.
rewrite HV14 in Q14. rewrite HV15 in Q15.
assert (N23 : VAL 303%nat + 864 = rg_capout RG) by exact HH23.
assert (N24 : VAL 304%nat + 892 = rg_out RG) by exact HH24.
assert (WR1 : forall a, (rg_capout RG <= a < rg_capout RG + 8) \/ (rg_out RG <= a < rg_out RG + 8) ->
  writable_at SEGS (mrestrict (w_H W2) mem2) a).
{ intros a Ha.
  assert (Hg : inG (G_SL B RG) a) by (clear - Ha; destruct Ha as [Ha|Ha]; ing_tac).
  assert (He : ~ (as_errno B <= a < as_errno B + 4)) by (clear - Ha DE8 DE9; lia).
  apply (gr_wr_kept2 _ _ _ _ a (proj2 (GK a (or_introl Hg) He))).
  apply (gr_wr_kept2 (w_H WN) (w_H WN) memN (ms_mem ms1) a).
  - intros Hp. apply (apresent_grows _ _ _ _ HG1). apply (apresent_grows _ _ _ _ HG0). exact Hp.
  - destruct Ha as [Ha|Ha].
    + replace a with (rg_capout RG + (a - rg_capout RG)) by lia. apply Wcap. lia.
    + replace a with (rg_out RG + (a - rg_out RG)) by lia. apply Wout. lia. }
assert (BV303 : base_val Ea (Some 303%nat) = VAL 303%nat) by (cbn [base_val]; exact (HEIa 303%nat ltac:(cbv; lia))).
assert (BV304 : base_val Ea (Some 304%nat) = VAL 304%nat) by (cbn [base_val]; exact (HEIa 304%nat ltac:(cbv; lia))).
pose proof (st_ok_pi_add_region Ea _ _ (YP09.mkRegion (Some 304%nat) 892 900 892 900 []) HS eq_refl) as HSa.
match type of HSa with ?t1 -> ?t2 -> _ => assert (RO1 : t1); [|assert (RD1 : t2); [|specialize (HSa RO1 RD1)]] end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
  rewrite BV304. split; [clear - N24 Q15; lia|]. split; [clear - N24 Q15; lia|].
  split; [intros o Ho; apply WR1; right; clear - Ho N24; lia | apply Forall_nil]. }
{ cbn. exact I. }
clear HS RO1 RD1. rename HSa into HS.
pose proof (st_ok_pi_add_region Ea _ _ (YP09.mkRegion (Some 303%nat) 864 872 864 872 []) HS eq_refl) as HSa.
match type of HSa with ?t1 -> ?t2 -> _ => assert (RO1 : t1); [|assert (RD1 : t2); [|specialize (HSa RO1 RD1)]] end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
  rewrite BV303. split; [clear - N23 Q14; lia|]. split; [clear - N23 Q14; lia|].
  split; [intros o Ho; apply WR1; left; clear - Ho N23; lia | apply Forall_nil]. }
{ pose proof (sl_rgd B RG HRGD 8 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D89.
  cbn [nth] in D89. unfold zdisj in D89. cbn [fst snd] in D89.
  cbn [ss_mem all_disjoint]. split; [|exact I]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV303, BV304. clear - D89 N23 N24; lia. }
clear HS RO1 RD1. rename HSa into HS.
assert (HFa : afact_ok Ea 40 (mkAF 4096 (2 ^ 47) 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ea40. unfold w64. rewrite unsigned_lit_small by (clear - Hrceil Hr4096 C1 HNC1; lia).
  change (2 ^ 4) with 16. rewrite Hr16. clear - Hrceil Hr4096 C1 HNC1; lia. }
pose proof (st_ok_pi_add_fact Ea _ _ 40%nat _ HS HFa) as HSa. clear HS HFa. rename HSa into HS.
assert (HJ2 : ajournal_gx_x SEGS B PST ARx (G_SL B RG) 0 [] SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out)) ly S HpE W mem md []
  ly2 S2 Hp2 W2 mem2 md2 (kN + 3)).
{ apply (ajournal_gx_pack_x SEGS B PST ARx (G_SL B RG) 0 [] SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out)) ly S HpE W mem md []
    ly2 S2 Hp2 W2 mem2 md2 (kN + 3) memS1); [lia | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG1 | apply out_none]. }
clear BVE.
assert (BVE : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val Ea (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEIa m Hm)).
assert (SHOK2 : sh_ok SEGS BxL [] Ea (mrestrict (w_H W2) mem2)) by constructor.
lrun_to RUNTO HS HJ2 SHOK2 LBspan 1380%Z.
{ apply awr_ok_x_cons_g; [awr_g 303%nat N23|].
  apply awr_ok_x_cons_g; [awr_g 304%nat N24|].
  apply awr_ok_x_nil. }

lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms3 end.
pose proof (ajournal_gx_AR_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR3.
(* ---- what each stretch kept ---- *)
assert (KV1 : forall x, 0 <= x < 2 ^ 64 -> ~ (rg_capout RG <= x < rg_capout RG + 8) -> ~ (rg_out RG <= x < rg_out RG + 8) ->
  aview SEGS (w_H WN) (ms_mem ms1) x = aview SEGS (w_H WN) memN x).
{ intros x Hx N1 N2.
  rewrite (aview_kept_out E _ (w_H WN) (ms_mem ms) (ms_mem ms1) HFr0 x Hx).
  - apply (aview_kept_out E _ (w_H WN) memN (ms_mem ms) HFr x Hx).
    intros (rr & Hin & Hr). vm_compute in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?(HEI 255%nat ltac:(cbv; lia)), ?(HEI 256%nat ltac:(cbv; lia)), ?N14, ?N15 in Hr; clear - Hr N1 N2; lia.
  - intros (rr & Hin & Hr). vm_compute in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?(HEI 255%nat ltac:(cbv; lia)), ?(HEI 256%nat ltac:(cbv; lia)), ?N14, ?N15 in Hr; clear - Hr N1 N2; lia. }
assert (KP1 : forall x, apresent (w_H WN) memN x -> apresent (w_H WN) (ms_mem ms1) x)
  by (intros x Hp; apply (apresent_grows _ _ _ _ HG1); apply (apresent_grows _ _ _ _ HG0); exact Hp).
assert (KV3 : forall x, 0 <= x < 2 ^ 64 -> ~ (rg_capout RG <= x < rg_capout RG + 8) -> ~ (rg_out RG <= x < rg_out RG + 8) ->
  aview SEGS (w_H W2) (ms_mem ms3) x = aview SEGS (w_H W2) mem2 x).
{ intros x Hx N1 N2. apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem ms3) HFr1 x Hx).
  intros (rr & Hin & Hr). vm_compute in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?(HEIa 303%nat ltac:(cbv; lia)), ?(HEIa 304%nat ltac:(cbv; lia)) in Hr; clear - Hr N1 N2 N23 N24; lia. }
assert (KP3 : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) (ms_mem ms3) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ HG2 Hp)).

assert (SPB : alloc_ceiling + SL_STK <= spZ regsE /\ spZ regsE <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47; lia).
assert (CI : forall x, (rg_capout RG <= x < rg_capout RG + 8) \/ (rg_out RG <= x < rg_out RG + 8) -> in_img SEGS x)
  by (intros x Hx; assert (Hg : inG (G_SL B RG) x) by (clear - Hx; destruct Hx as [Hx|Hx]; ing_tac); exact (proj1 (HG x Hg))).
assert (FK : forall x, spZ regsE - SL_FRAME <= x < spZ regsE ->
  aview SEGS (w_H W2) (ms_mem ms3) x = aview SEGS (w_H WN) memN x)
  by (intros x Hx; assert (Hx64 : alloc_ceiling <= x < 2 ^ 64) by (rewrite WS, HSF in *; clear - Hx SPB C1; lia);
  assert (N1 : ~ (rg_capout RG <= x < rg_capout RG + 8)) by (clear - Hx64 Q14 C1; lia);
  assert (N2 : ~ (rg_out RG <= x < rg_out RG + 8)) by (clear - Hx64 Q15 C1; lia);
  rewrite (KV3 x ltac:(clear - Hx64 C1; lia) N1 N2);
  rewrite (K1 x Hx64 ltac:(rewrite HSF in *; clear - Hx; lia)); exact (KV1 x ltac:(clear - Hx64 C1; lia) N1 N2)).
assert (ERRN : forall x, as_errno B <= x < as_errno B + 4 -> aview SEGS (w_H WN) memN x <> None)
  by (intros x Hx; unfold aview; unfold arm in Vev;
  pose proof (Vev (Z.to_nat (x - as_errno B)) ltac:(clear - Hx; lia)) as Hvv;
  replace (as_errno B + Z.of_nat (Z.to_nat (x - as_errno B))) with x in Hvv by (clear - Hx; lia);
  rewrite Hvv; cbn [option_map]; discriminate).
assert (CV : forall x, inG (G_SL B RG) x \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x ->
  ~ (rg_capout RG <= x < rg_capout RG + 8) -> ~ (rg_out RG <= x < rg_out RG + 8) ->
  aview SEGS (w_H W2) (ms_mem ms3) x = aview SEGS (w_H WN) memN x)
  by (intros x Hg N1 N2;
  assert (Hi : in_img SEGS x) by (destruct Hg as [Hg|Hg]; [exact (proj1 (HG x Hg)) | exact (proj1 (HGO x Hg))]);
  assert (Hx64 : 0 <= x < 2 ^ 64) by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl C5; unfold kLowMemEnd in *; lia);
  rewrite (KV3 x Hx64 N1 N2), <- (KV1 x Hx64 N1 N2);
  destruct (Z_le_gt_dec (as_errno B) x) as [He1|He1]; [destruct (Z_lt_ge_dec x (as_errno B + 4)) as [He2|He2]|];
  [ pose proof (Herr2 (x - as_errno B) ltac:(lia)) as Hee;
    replace (as_errno B + (x - as_errno B)) with x in Hee by lia; exact Hee
  | exact (proj1 (GK x Hg ltac:(lia)))
  | exact (proj1 (GK x Hg ltac:(lia))) ]).
assert (CK : forall x, inG (G_SL B RG) x \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x ->
  ~ (rg_capout RG <= x < rg_capout RG + 8) -> ~ (rg_out RG <= x < rg_out RG + 8) ->
  abyte_kept WN memN W2 (ms_mem ms3) x)
  by (intros x Hg N1 N2; split; [exact (CV x Hg N1 N2)|]; intros Hw;
  assert (Hi : in_img SEGS x) by (destruct Hg as [Hg'|Hg']; [exact (proj1 (HG x Hg')) | exact (proj1 (HGO x Hg'))]);
  destruct (Z_le_gt_dec (as_errno B) x) as [He1|He1]; [destruct (Z_lt_ge_dec x (as_errno B + 4)) as [He2|He2]|];
  [ assert (Hge : inG (G_SL B RG) x) by (clear - He1 He2; ing_tac);
    apply (gr_img_wr W2 (ms_mem ms3) x Hi (HGR x Hge)); rewrite (CV x Hg N1 N2); exact (ERRN x ltac:(lia))
  | apply (gr_wr_kept2 (w_H WN) (w_H W2) memN (ms_mem ms3) x); [|exact Hw];
    intros Hp; apply KP3; apply (proj2 (GK x Hg ltac:(lia))); apply KP1; exact Hp
  | apply (gr_wr_kept2 (w_H WN) (w_H W2) memN (ms_mem ms3) x); [|exact Hw];
    intros Hp; apply KP3; apply (proj2 (GK x Hg ltac:(lia))); apply KP1; exact Hp ]).

assert (LBLK : forall q m, In (q, m) (ablocks B lyN SN) -> q <> outN -> In (q, m) rest)
  by (intros q m Hin Hq; apply (Permutation_in _ HPerm1) in Hin; apply in_app_or in Hin;
  destruct Hin as [Hin | Hin]; [|exact Hin]; exfalso; unfold aout_blks in Hin;
  destruct (capN =? 0); [destruct Hin | destruct Hin as [Heq | []]; injection Heq as <- <-; exact (Hq eq_refl)]).
assert (LK : forall x, line <= x < line + len -> aview SEGS (w_H W2) (ms_mem ms3) x = aview SEGS (w_H WN) memN x)
  by (intros x Hx;
  assert (Hx64 : 0 <= x < 2 ^ 64) by (clear - Hx Hline0 Hline1; lia);
  assert (N1 : ~ (rg_capout RG <= x < rg_capout RG + 8)) by (intros HcX; apply (HLG x Hx); clear - HcX; ing_tac);
  assert (N2 : ~ (rg_out RG <= x < rg_out RG + 8)) by (intros HcX; apply (HLG x Hx); clear - HcX; ing_tac);
  rewrite (KV3 x Hx64 N1 N2), <- (KV1 x Hx64 N1 N2);
  destruct HLOK as [H0 | [(q & m & Hin & Hq & Hql & Hqm) | (Himg & _ & Hno)]];
  [ clear - H0 Hsent; lia
  | pose proof (gr_sep_head_x ly2 S2 Hp2 W2 mem2 md2 (res, NC) rest (q, m) HAR2 P2 (LBLK q m Hin Hq)) as DR;
    unfold zdisjoint, block_rng in DR; cbn [fst snd] in DR; rewrite RQN in DR;
    assert (NE : ~ ((res <= q + (x - q) < res + req_size NC) \/
                    (outN <> 0 /\ outN <= q + (x - q) < outN + req_size capN)))
      by (rewrite RQN; intros [Hr | (Ho0 & Ho)]; [clear - Hr DR Hql Hqm Hx; lia|];
          destruct (Hcnz (Hocz Ho0)) as (_ & Hoin);
          pose proof (sep_blocks_x SEGS B ARx LAWS lyN SN HpN WN memN mdN q m outN capN HARN Hin Hoin
            ltac:(intros Heq; injection Heq as Heq _; exact (Hq Heq))) as DO;
          unfold zdisjoint in DO; cbn [fst snd] in DO; clear - Ho DO Hql Hqm Hx; lia);
    pose proof (K2 q m (x - q) Hin ltac:(clear - Hql Hqm Hx; lia) NE) as Kq;
    replace (q + (x - q)) with x in Kq by lia; exact Kq
  | assert (Hi : in_img SEGS x) by exact (Himg x Hx);
    destruct (Z_le_gt_dec (as_errno B) x) as [He1|He1]; [destruct (Z_lt_ge_dec x (as_errno B + 4)) as [He2|He2]|];
    [ pose proof (Herr2 (x - as_errno B) ltac:(lia)) as Hee;
      replace (as_errno B + (x - as_errno B)) with x in Hee by lia; exact Hee
    | exact (K3 x Hi (Hno x Hx) ltac:(lia))
    | exact (K3 x Hi (Hno x Hx) ltac:(lia)) ] ]).
assert (ROM3 : rom_view SEGS W2 (ms_mem ms3))
  by (intros x Hx; destruct (HROMO x Hx) as (HnG & Hpin & Hne & _);
  destruct (Exists_dec (in_zr x) (as_owned_static B) (gr_in_zr_dec x)) as [Hown | Hno];
  [ eapply (rom_pinned_view_x SEGS B ARx LAWS); [exact HAR3 | exact (Hpin Hown)]
  | assert (Hi : in_img SEGS x) by (destruct Hx as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]);
    assert (Hx64 : 0 <= x < 2 ^ 64) by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl C5; unfold kLowMemEnd in *; lia);
    assert (N1 : ~ (rg_capout RG <= x < rg_capout RG + 8)) by (intros HcX; apply HnG; clear - HcX; ing_tac);
    assert (N2 : ~ (rg_out RG <= x < rg_out RG + 8)) by (intros HcX; apply HnG; clear - HcX; ing_tac);
    rewrite (KV3 x Hx64 N1 N2), (K3 x Hi Hno Hne), (KV1 x Hx64 N1 N2); exact (HROM x Hx) ]).
assert (APK3 : apres_kept B W mem W2 (ms_mem ms3))
  by (intros x Hi Hno He Hp; apply KP3; destruct (NOWN x Hi Hno) as [O1 O2];
  apply (Hpres2 x Hi O1 O2 He (NBLK x Hi)); apply KP1; exact (HAPK x Hi Hno He Hp)).

assert (NBUF : exists junk, Z.of_nat (length junk) = NC - (no + sent) /\
  garr8 SEGS (arm W2 (ms_mem ms3)) res (bzs ((O ++ firstn (Z.to_nat sent) Bl) ++ junk)))
  by (apply (gr_newbuf WN memN W2 (ms_mem ms3) _ (no + sent) capN outN res NC);
  [ destruct Hblk as [(Hc0 & _ & Hn0) | (Hc1 & _ & _ & HJk)]; [left; split; assumption | right; split; [exact Hc1 | exact HJk]]
  | exact HlenO
  | unfold NC; clear - Hgrow Rc0 Hnn HlenO; lia
  | intros Hc1 i Hi;
    destruct (Hcnz ltac:(clear - Hc1; lia)) as (Ho0 & Hoin);
    destruct (alx_blocks _ _ _ LAWS lyN SN HpN WN memN mdN outN capN HARN Hoin) as (_ & Ho4096 & Hoceil & _);
    assert (RQC : req_size capN = capN) by (unfold req_size; destruct (Z.eqb_spec capN 0); [clear - Hc1 e; lia | reflexivity]);
    rewrite RQC in Hoceil;
    assert (Nr : ~ in_img SEGS (res + i))
      by (intros Hi'; apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res NC (res + i) HAR2 HRIN2); [rewrite RQN; clear - Hi Hgrow; unfold NC in *; lia | exact Hi']);
    assert (No : ~ in_img SEGS (outN + i))
      by (intros Hi'; apply (blk_img_x SEGS B ARx LAWS lyN SN HpN WN memN mdN outN capN (outN + i) HARN Hoin); [rewrite RQC; clear - Hi; lia | exact Hi']);
    rewrite (KV3 (res + i) ltac:(clear - Hi Hrceil Hr4096 C1 Hgrow; unfold NC in *; lia)
      ltac:(intros HcX; apply Nr; apply CI; left; exact HcX) ltac:(intros HcX; apply Nr; apply CI; right; exact HcX));
    rewrite (Hcopy Ho0 i ltac:(rewrite Z.min_l by (unfold NC in *; clear - Hgrow Hnn HlenO; lia); exact Hi));
    exact (KV1 (outN + i) ltac:(clear - Hi Hoceil Ho4096 C1; lia)
      ltac:(intros HcX; apply No; apply CI; left; exact HcX) ltac:(intros HcX; apply No; apply CI; right; exact HcX))
  | intros x Hx; apply KP3; exact (proj1 (Hrpres x Hx)) ]).
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RCAP.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as ROUT.
cbn [ms_mem restrict] in RCAP, ROUT.
assert (UNC : U Ea (SAlu ALU_ADD (SAlu ALU_SLL (SOff 18 0) (SLit 1)) (SAlu ALU_SLL (SOff 32 0) (SLit 1))) = NC)
  by (assert (U18 : U Ea (SOff 18 0) = n) by (apply (U_atom Ea 18 n (eq_trans (OLDa 18%nat ltac:(lia)) E18)); clear - Hnn Hlen47 Hsent; lia);
  assert (U32 : U Ea (SOff 32 0) = no + sent) by (apply (U_atom Ea 32 (no + sent) (eq_trans (OLDa 32%nat ltac:(lia)) E32)); clear - Rn47 HlenO; lia);
  assert (S18 : U Ea (SAlu ALU_SLL (SOff 18 0) (SLit 1)) = n * 2)
    by (rewrite gr_U_sll1; rewrite U18; clear - Hnn Hlen47 Hsent; lia);
  assert (S32 : U Ea (SAlu ALU_SLL (SOff 32 0) (SLit 1)) = (no + sent) * 2)
    by (rewrite gr_U_sll1; rewrite U32; clear - Rn47 HlenO; lia);
  rewrite gr_U_add; rewrite S18, S32; unfold NC; clear - Hnn Hlen47 Hsent Rn47 HlenO; lia).
assert (VCAP : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (rg_capout RG) 8 NC)
  by (rewrite <- N23; refine (field_of_region Ea _ 303 (VAL 303%nat) _ _ _ _ _ 864 8%N _ NC RCAP _ _ _ _ _);
  [ exact (HEIa 303%nat ltac:(cbv; lia)) | cbn [In]; left; reflexivity | rewrite denot_lit_U, UNC; reflexivity
  | change (8 * Z.of_N 8) with 64; unfold NC in *; clear - Hnn Hlen47 Hsent Rn47 HlenO; lia | cbn; lia ]).
assert (VOUT : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (rg_out RG) 8 res)
  by (rewrite <- N24; refine (field_of_region Ea _ 304 (VAL 304%nat) _ _ _ _ _ 892 8%N _ res ROUT _ _ _ _ _);
  [ exact (HEIa 304%nat ltac:(cbv; lia)) | cbn [In]; left; reflexivity | exact (den_atom0 Ea 40 res Ea40 ltac:(clear - Hrceil Hr4096 C1 HNC1; lia))
  | change (8 * Z.of_N 8) with 64; clear - Hrceil Hr4096 C1 HNC1; lia | cbn; lia ]).
assert (WCAP : awr W2 (ms_mem ms3) (rg_capout RG) 8)
  by (intros i Hi; destruct RCAP as (_ & _ & RW & _); cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in RW;
  pose proof (RW (864 + i) ltac:(clear - Hi; lia)) as Hw; rewrite BV303 in Hw;
  replace (VAL 303%nat + (864 + i)) with (rg_capout RG + i) in Hw by (clear - N23; lia); exact Hw).
assert (WOUT : awr W2 (ms_mem ms3) (rg_out RG) 8)
  by (intros i Hi; destruct ROUT as (_ & _ & RW & _); cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in RW;
  pose proof (RW (892 + i) ltac:(clear - Hi; lia)) as Hw; rewrite BV304 in Hw;
  replace (VAL 304%nat + (892 + i)) with (rg_out RG + i) in Hw by (clear - N24; lia); exact Hw).
pose proof (sl_rgd B RG HRGD 2 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D2_8.
pose proof (sl_rgd B RG HRGD 2 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D2_9.
pose proof (sl_rgd B RG HRGD 3 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D3_8.
pose proof (sl_rgd B RG HRGD 3 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D3_9.
pose proof (sl_rgd B RG HRGD 4 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D4_8.
pose proof (sl_rgd B RG HRGD 4 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D4_9.
pose proof (sl_rgd B RG HRGD 5 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D5_8.
pose proof (sl_rgd B RG HRGD 5 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D5_9.
pose proof (sl_rgd B RG HRGD 6 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D6_8.
pose proof (sl_rgd B RG HRGD 6 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D6_9.
pose proof (sl_rgd B RG HRGD 7 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D7_8.
pose proof (sl_rgd B RG HRGD 7 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D7_9.
pose proof (sl_rgd B RG HRGD 10 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D10_8.
pose proof (sl_rgd B RG HRGD 10 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D10_9.
cbn [nth] in D2_8, D2_9, D3_8, D3_9, D4_8, D4_9, D5_8, D5_9, D6_8, D6_9, D7_8, D7_9, D10_8, D10_9. unfold zdisj in D2_8, D2_9, D3_8, D3_9, D4_8, D4_9, D5_8, D5_9, D6_8, D6_9, D7_8, D7_9, D10_8, D10_9. cbn [fst snd] in D2_8, D2_9, D3_8, D3_9, D4_8, D4_9, D5_8, D5_9, D6_8, D6_9, D7_8, D7_9, D10_8, D10_9.

assert (OUT3 : aout_at B RG ly2 S2 W2 (ms_mem ms3) (CTL 3 0 0 0 evL) (O ++ firstn (Z.to_nat sent) Bl) mx (no + sent) NC res).
{ unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  split; [apply (akept_vm WN memN); [intros x Hx; simpl Z.of_nat in Hx; apply CK; [right; clear - Hx; repeat first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl] | clear - Hx D6_8; lia | clear - Hx D6_9; lia] | exact Vmx]|].
  split; [apply (akept_awr WN memN); [intros x Hx; apply CK; [right; clear - Hx; repeat first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl] | clear - Hx D6_8; lia | clear - Hx D6_9; lia] | exact Wmx]|].
  split; [apply (akept_vm WN memN); [intros x Hx; simpl Z.of_nat in Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D7_8; lia | clear - Hx D7_9; lia] | exact Vno]|].
  split; [apply (akept_awr WN memN); [intros x Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D7_8; lia | clear - Hx D7_9; lia] | exact Wno]|].
  split; [exact VCAP|]. split; [exact WCAP|]. split; [exact VOUT|]. split; [exact WOUT|].
  split; [apply (akept_vm WN memN); [intros x Hx; simpl Z.of_nat in Hx; apply CK; [right; clear - Hx; repeat first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl] | clear - Hx D2_8; lia | clear - Hx D2_9; lia] | exact Vcl]|].
  split; [apply (akept_awr WN memN); [intros x Hx; apply CK; [right; clear - Hx; repeat first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl] | clear - Hx D2_8; lia | clear - Hx D2_9; lia] | exact Wcl]|].
  split; [apply (akept_vm WN memN); [intros x Hx; simpl Z.of_nat in Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D3_8; lia | clear - Hx D3_9; lia] | exact Vbr]|].
  split; [apply (akept_awr WN memN); [intros x Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D3_8; lia | clear - Hx D3_9; lia] | exact Wbr]|].
  split; [apply (akept_vm WN memN); [intros x Hx; simpl Z.of_nat in Hx; apply CK; [right; clear - Hx; repeat first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl] | clear - Hx D5_8; lia | clear - Hx D5_9; lia] | exact Vdd]|].
  split; [apply (akept_awr WN memN); [intros x Hx; apply CK; [right; clear - Hx; repeat first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl] | clear - Hx D5_8; lia | clear - Hx D5_9; lia] | exact Wdd]|].
  split; [apply (akept_vm WN memN); [intros x Hx; simpl Z.of_nat in Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D4_8; lia | clear - Hx D4_9; lia] | exact Vei]|].
  split; [apply (akept_awr WN memN); [intros x Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D4_8; lia | clear - Hx D4_9; lia] | exact Wei]|].
  split; [apply (akept_vm WN memN); [intros x Hx; simpl Z.of_nat in Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D10_8; lia | clear - Hx D10_9; lia] | exact Vev]|].
  split; [apply (akept_awr WN memN); [intros x Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D10_8; lia | clear - Hx D10_9; lia] | exact Wev]|].
  split; [exact Rev|]. split; [exact Hclr|]. split; [exact Hbrr|]. split; [exact Hddr|]. split; [exact Heir|].
  split; [exact Hmxr|]. split; [exact HlenO|].
  right. split; [unfold NC in *; clear - Hnn Hsent HlenO; lia|]. split; [unfold NC in *; clear - Hnn Hsent HlenO; lia|].
  split; [exact HRIN2 | exact NBUF]. }

pmkst HS.
prreg HS (2%bv : bv 5) J2. prreg HS (3%bv : bv 5) J3. prreg HS (4%bv : bv 5) J4.
prreg HS (8%bv : bv 5) J8. prreg HS (9%bv : bv 5) J9. prreg HS (18%bv : bv 5) J18. prreg HS (22%bv : bv 5) J22.
prreg HS (23%bv : bv 5) J23. prreg HS (20%bv : bv 5) J20. prreg HS (21%bv : bv 5) J21. prreg HS (24%bv : bv 5) J24.
prreg HS (25%bv : bv 5) J25. prreg HS (26%bv : bv 5) J26. prreg HS (27%bv : bv 5) J27.
apply (K W2 (ms_regs ms3) (ms_mem ms3) _).
unfold SLM_x. cbv zeta. change (Z.of_nat (length Bl)) with len.
exists ly2, S2, Hp2, (kN + 3), evL, NC, res, (spent + (mo_malloc MT NC + mo_free MT)), rest.
split; [exact HJ2|].
split; [unfold spZ at 1; rewrite J2, (OLDa 2%nat ltac:(lia)), (EA 2%nat ltac:(lia)); exact Hsp|].
split; [rewrite J3, (OLDa 3%nat ltac:(lia)), (EA 3%nat ltac:(lia)); exact H3|].
split; [rewrite J4, (OLDa 4%nat ltac:(lia)), (EA 4%nat ltac:(lia)); exact H4|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact HraE|].
split.
{ unfold sl_regsM.
  split; [rewrite J8, (OLDa 8%nat ltac:(lia)), (EA 8%nat ltac:(lia)); exact R8|].
  split; [rewrite J9, (OLDa 9%nat ltac:(lia)), (EA 9%nat ltac:(lia)); exact R9|].
  split; [rewrite J18, (OLDa 18%nat ltac:(lia)), (EA 18%nat ltac:(lia)); exact R18|].
  split; [rewrite J22, (OLDa 22%nat ltac:(lia)), (EA 22%nat ltac:(lia)); exact R22|].
  split; [rewrite J23, (OLDa 23%nat ltac:(lia)), (EA 23%nat ltac:(lia)); exact R23|].
  split; [rewrite J20, (ew_img Ea 304%nat HEIa) by (cbv; lia); reflexivity|].
  split; [rewrite J21, (OLDa 21%nat ltac:(lia)), (EA 21%nat ltac:(lia)); exact R21|].
  split; [rewrite J24, (ew_img Ea 303%nat HEIa) by (cbv; lia); reflexivity|].
  split; [rewrite J25, (OLDa 25%nat ltac:(lia)), (EA 25%nat ltac:(lia)); exact R25|].
  split; [rewrite J26, (ew_img Ea 302%nat HEIa) by (cbv; lia); reflexivity|].
  rewrite J27, (OLDa 27%nat ltac:(lia)), (EA 27%nat ltac:(lia)); exact R27. }
split; [apply (gr_vm_kept WN W2 memN (ms_mem ms3)); [intros x Hx; simpl Z.of_nat in Hx; apply FK; rewrite HSF in *; clear - Hx; lia | exact M8]|].
split; [apply (gr_vm_kept WN W2 memN (ms_mem ms3)); [intros x Hx; simpl Z.of_nat in Hx; apply FK; rewrite HSF in *; clear - Hx; lia | exact M16]|].
split; [intros i Hi; apply (gr_vm_kept WN W2 memN (ms_mem ms3));
  [intros x Hx; simpl Z.of_nat in Hx; apply FK; rewrite HSF in *; clear - Hx Hi; lia | exact (HSV i Hi)]|].
split; [exact Hcl|]. split; [exact Hbr|]. split; [exact Hdd|]. split; [exact Hsent|]. split; [exact Hn|]. split; [exact Hev|].
split; [exact OUT3|].
split; [unfold NC; clear - Hnn HlenO; lia|].
split; [apply (gr_garr8_kept WN memN W2 (ms_mem ms3) line (bzs Bl) HGL); intros x Hx; rewrite gr_bzs_len in Hx; exact (LK x Hx)|].
split; [exact Hline0|]. split; [exact Hline1|]. split; [exact ROM3|].
split.
{ destruct HLOK as [H0 | [(q & m & Hin & Hq & Hql & Hqm) | Himg]]; [left; exact H0 | right; left | right; right; exact Himg].
  exists q, m.
  pose proof (gr_sep_head_x ly2 S2 Hp2 W2 mem2 md2 (res, NC) rest (q, m) HAR2 P2 (LBLK q m Hin Hq)) as DR.
  unfold zdisjoint, block_rng in DR. cbn [fst snd] in DR. rewrite RQN in DR.
  pose proof (gr_blk_req_pos_x lyN SN HpN WN memN mdN q m HARN Hin) as Rq1.
  split; [apply (Permutation_in _ (Permutation_sym P2)); right; exact (LBLK q m Hin Hq)|].
  split; [intros Hqr; subst q; clear - DR Rq1 HNC1; lia|].
  split; [exact Hql | exact Hqm]. }
split; [exact HLG|].
split; [exact Hcapq|].
split; [clear - HMM; lia|].
split; [pose proof (gr_bb lyN SN ly2 S2 capN outN res NC Hozc HpermA HpermB) as HBB; clear - HBB HLM2; lia|].
split; [exact APK3|].
split; [exact HMOK|].
split; [exact (mle_station MT S SN S2 spent _ MTL HMLE Hmle2)|].
split; [clear - HCOST; lia|].
split; [exact HPerm0|].
split; [unfold aout_blks; rewrite (proj2 (Z.eqb_neq NC 0) ltac:(clear - HNC1; lia)); cbn [app]; exact P2|].
split; [rewrite Hfrs2; exact HFR|].
(* the room the realloc left is SLM_x's (the rounds after this one, on top of kr); the count premise is the entry's *)
split; [exact HRM2 | exact HCNT].
Qed.
(* Header hypotheses sl_grow_x uses (About through a scratch file): LAWS HG HGR HROMO HGO MTL CTX_R AREALLOC HCTX_slr
   HV13 HV14 HV15 HH22 HH23 HH24 HRGD.  Unused: HP0 TL AERRNO AMEMCPY HERRNO HERRZ HERRW HV9 HV10 HV11 HV12 HH17 HH19
   HH21 HSM (errno's cell stays writable by gr_img_wr: an image byte off the ROM (HGR) whose view the call keeps, so
   HERRW is not needed). *)

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): this Section's texts at a world relation R.  Each <name>_xR below is <name>_x
   with the journal ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, sl_post_x / sl_spec_x -> their R
   twins (W_send_line_xR.v, R right after ARx), every carrier or walk it names -> its R twin, and the walk on
   W_journal_x.v's G chain (RUNG / RUNTOG, W_kit_x.v's paj_run_tok_xR / paj_run_to_tok_xR, W_kit.v's paj_branch_xR
   as BRR, SRrG_bind / SRrG_mono / SRrG_ret); every other token is the strict text's.  At R := wle each is its strict twin by conversion. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Variable HA : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis HA_call : forall lyc Sc regsT ch p n, mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n.
Hypothesis AREALLOC_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HA CTX_R R (SIGMA WS_realloc).
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_SL B RG) HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_SL B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
(* W_send_line_grow_x.v:513 sl_grow_x at R *)
Theorem sl_grow_xR : sl_grow_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold sl_grow_stmt_xR. intros regsE ly S HpE W mem md c O mx no cap out line Bl WN regsN memN mdN sent n kr HN K.
unfold SLN_xR in HN. cbv zeta in HN.
destruct HN as (lyN & SN & HpN & kN & evL & capN & outN & spent & rest & HJ & Hsp & H3 & H4 & Hgp & Htp & HraE & HR &
  M8 & M16 & HSV & Hcl & Hbr & Hdd & Hsent & Hn & Hev & HOUT & Hgrow & HGL & Hline0 & Hline1 & HROM & HLOK & HLG &
  Hcapq & HMM & HLM & HAPK & HMOK & HMLE & HCOST & HPerm0 & HPerm1 & HFR & HRM & HCNT).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & Hag) & _).
pose proof HJi as (HARN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresN & HstkN & _).
pose proof HstkN as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
rewrite !Z.add_0_r in Hal16, Hstk0, Hslo, Hshi, Hbot, Htop2, HpresN.
assert (WS : SL_STK = 16512) by reflexivity.
assert (HSF : SL_FRAME = 128) by reflexivity.
pose proof HOUT as (Vmx & Wmx & Vno & Wno & Vcap & Wcap & Vout & Wout & Vcl & Wcl & Vbr & Wbr &
  Vdd & Wdd & Vei & Wei & Vev & Wev & Rev & Hclr & Hbrr & Hddr & Heir & Hmxr & HlenO & Hblk).
cbn [ct_cl ct_br ct_dd ct_ei ct_ev] in Vmx, Vno, Vcap, Vout, Vcl, Vbr, Vdd, Vei, Vev, Rev, Hclr, Hbrr, Hddr, Heir.
assert (Rcapout : 0 <= capN /\ 0 <= outN /\ no + sent <= 2 ^ 47 /\ capN <= 2 ^ 47 /\ outN <= 2 ^ 47).
{ destruct Hblk as [(Hc0 & Ho0 & Hn0) | (Hc1 & Hn1 & Hin1 & _)].
  - repeat split; lia.
  - destruct (alx_blocks _ _ _ LAWS lyN SN HpN WN memN mdN outN capN HARN Hin1) as (_ & Hp4 & Hpc & _).
    assert (Hrq : req_size capN = capN) by (unfold req_size; destruct (Z.eqb_spec capN 0); lia).
    rewrite Hrq in Hpc. repeat split; lia. }
destruct Rcapout as (Rc0 & Ro0 & Rn47 & Rc47 & Ro47).
set (len := Z.of_nat (length Bl)) in *.
pose proof HR as HRc.
destruct HRc as (R8 & R9 & R18 & R22 & R23 & R20 & R21 & R24 & R25 & R26 & R27).
pose proof (gr_seat WN regsN memN (no + sent) capN outN R20 R24 R26 Vno Vcap Wcap Vout Wout
  ltac:(clear - Rn47 HlenO; lia) ltac:(clear - Rc0 Rc47; lia) ltac:(clear - Ro0 Ro47; lia)) as HS.

remember (Eimg (Ereg regsN (gr_extra (no + sent) capN outN))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (BVE : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val E (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEI m Hm)).
assert (EA : forall i, (i < 32)%nat -> ew E i = getr regsN (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew].
  destruct (Nat.ltb_spec i 32); [reflexivity | lia]. }
assert (E32 : ew E 32 = w64 (no + sent)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsN _ 0)).
assert (E33 : ew E 33 = w64 capN) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsN _ 1)).
assert (E34 : ew E 34 = w64 outN) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsN _ 2)).
clear HE.
assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H WN) memN)) by constructor.
lrun RUNG HS HJ SHOK LBspan.
{ unfold ss_G; cbn [ss_mem]; unfold gr_regions, gr_nout, gr_cap, gr_out.
  apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 14) HV14|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 15) HV15|].
  apply awr_ok_x_nil. }

psrr_branch_tok RUNG BRR HS SHOK LBspan.

all: assert (E18 : ew E 18 = w64 n) by (rewrite (EA 18%nat ltac:(lia)); exact R18).
all: assert (Hnn : 0 < n <= len - sent) by (rewrite Hn; apply sl_n_range; clear - Hmxr Hsent; lia).
all: assert (Hlen63 : len < 2 ^ 63) by (clear - Hline0 Hline1; lia).
all: assert (UADD : U E (SAlu ALU_ADD (SOff 18 0) (SOff 32 0)) = n + (no + sent))
  by (rewrite U_SAlu, (U_atom E 18 n E18), (U_atom E 32 (no + sent) E32) by (clear - Hnn Hsent Hlen63 Rn47 HlenO; lia);
      cbn [zalu_raw]; apply zcanon_id; unfold M64; clear - Hnn Hsent Hlen63 Rn47 HlenO; lia).
1: { exfalso. rewrite branch_geu_U, (U_atom E 33 capN E33), UADD in Hc by (clear - Rc0 Rc47; lia).
  apply negb_true_iff, Z.ltb_ge in Hc. clear - Hc Hgrow; lia. }
rewrite branch_geu_U, (U_atom E 33 capN E33), UADD in Hc by (clear - Rc0 Rc47; lia).
assert (N14 : VAL 255%nat = rg_capout RG) by exact HV14.
assert (N15 : VAL 256%nat = rg_out RG) by exact HV15.
lrun RUNG HS HJ SHOK LBspan.
{ apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 255%nat N14|].
  apply awr_ok_x_cons_g; [awr_g 256%nat N15|].
  apply awr_ok_x_nil. }

lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.

(* the line lies below alloc_ceiling: in a live block (alx_blocks; the generic blocks law has no MALLOC_MAX bound,
   where the AR walk read len < 2 ^ 32) or in the image *)
assert (HlenA : len < alloc_ceiling).
{ destruct HLOK as [H0 | [(q & m & Hin & _ & Hq & Hqm) | (Himg & _ & _)]].
  - clear - H0 Hsent; lia.
  - destruct (alx_blocks _ _ _ LAWS lyN SN HpN WN memN mdN q m HARN Hin) as (_ & Hq4 & Hqc & _).
    clear - Hq Hqm Hq4 Hqc; lia.
  - pose proof (pa_img_range _ (Himg line ltac:(clear - Hsent; lia))) as P1.
    pose proof (pa_img_range _ (Himg (line + len - 1) ltac:(clear - Hsent; lia))) as P2. clear - P1 P2 Hsent C1; lia. }
assert (Hlen47 : len < 2 ^ 47) by (clear - HlenA C1; lia).
set (NC := (no + sent + n) * 2) in *.
assert (HNC1 : 1 <= NC) by (unfold NC; clear - Hnn Hsent HlenO; lia).
pose proof (st_ok_restrict_reg _ _ _ _ _ 11%bv HS) as G11'.
lazymatch type of G11' with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in G11' end.
cbn [ms_regs restrict mkst] in G11'.
assert (G11 : getr (ms_regs ms1) 11 = w64 NC).
{ rewrite G11', denot_lit_U. unfold w64. f_equal.
  assert (U18 : U E (SOff 18 0) = n) by (apply (U_atom E 18 n E18); clear - Hnn Hlen47 Hsent; lia).
  assert (U32 : U E (SOff 32 0) = no + sent) by (apply (U_atom E 32 (no + sent) E32); clear - Rn47 HlenO; lia).
  assert (S18 : U E (SAlu ALU_SLL (SOff 18 0) (SLit 1)) = n * 2)
    by (rewrite gr_U_sll1; rewrite U18; clear - Hnn Hlen47 Hsent; lia).
  assert (S32 : U E (SAlu ALU_SLL (SOff 32 0) (SLit 1)) = (no + sent) * 2)
    by (rewrite gr_U_sll1; rewrite U32; clear - Rn47 HlenO; lia).
  rewrite gr_U_add; rewrite S18, S32; unfold NC; clear - Hnn Hlen47 Hsent Rn47 HlenO; lia. }

(* ---- the model: this round grows g_out to NC ---- *)
assert (Hmx0 : 0 <= mx) by (clear - Hmxr; lia).
assert (Hrem : 0 < len - sent) by (clear - Hsent; lia).
assert (GROW : (capN <? no + sent + sl_n mx (len - sent)) = true) by (rewrite <- Hn; apply Z.ltb_lt; exact Hgrow).
rewrite (sl_max_run_step mx (no + sent) capN (len - sent) Hmx0 Hrem), GROW in HMM.
(* C3: the peak of the rest of the trace gives realloc's room (HLR) and, the old block freed, the peak after it *)
destruct (sl_tr_peak_grow mx (no + sent) capN (len - sent) (blocks_bytes SN) LIVE_MAX Hmx0 Hrem
  (proj1 (Z.ltb_lt _ _) GROW) HLM) as (HLR & HLM2).
rewrite (sl_cost_run_step MT mx (no + sent) capN (len - sent) Hmx0 Hrem), GROW in HCOST.
rewrite (sl_cost_run_step MT_rk mx (no + sent) capN (len - sent) Hmx0 Hrem), GROW in HRM.
rewrite (send_line_cap_step mx (no + sent) capN (len - sent) Hmx0 Hrem) in Hcapq.
unfold sl_capn in HCOST, HRM, Hcapq. rewrite GROW in HCOST, HRM, Hcapq.
rewrite <- Hn in HMM, HLR, HLM2, HCOST, HRM, Hcapq.
fold NC in HMM, HLR, HLM2, HCOST, HRM, Hcapq.
pose proof (sl_cost_run_nonneg MT (Z.to_nat (len - sent - n)) mx (no + sent + n) NC (len - sent - n) MTL
  ltac:(clear - Hsent Hnn HlenO; lia) Hmx0) as HCnn.
assert (HmoN : 0 <= mo_malloc MT NC + mo_free MT).
{ pose proof (mo_malloc_nonneg MT MTL NC ltac:(unfold NC; clear - Hsent Hnn HlenO; lia)).
  pose proof (mo_free_nonneg MT MTL). lia. }
(* the room: MT_rk counts this round's realloc as 2, the rounds after it leave RR on top of kr *)
pose proof (sl_cost_run_nonneg MT_rk (Z.to_nat (len - sent - n)) mx (no + sent + n) NC (len - sent - n) gr_rk_laws
  ltac:(clear - Hsent Hnn HlenO; lia) Hmx0) as HRnn.
change (mo_malloc MT_rk NC + mo_free MT_rk) with 2 in HRM.
set (RR := sl_cost_run MT_rk (Z.to_nat (len - sent - n)) mx (no + sent + n) NC (len - sent - n)) in HRM, HRnn.
assert (HRM1 : rp_RM RP SN (2 + (Z.to_nat RR + kr))).
{ replace (2 + (Z.to_nat RR + kr))%nat with (Z.to_nat (2 + RR) + kr)%nat by (clear - HRnn; lia). exact HRM. }
clear HRM.

(* ---- the old block of g_out: NULL exactly when g_capout is 0 ---- *)
assert (Hcz : capN = 0 -> outN = 0)
  by (intros Hcc; destruct Hblk as [(_ & Ho & _) | (Hc1 & _)]; [exact Ho | clear - Hcc Hc1; lia]).
assert (Hcnz : capN <> 0 -> outN <> 0 /\ In (outN, capN) (ablocks B lyN SN)).
{ intros Hcc. destruct Hblk as [(Hc0 & _) | (_ & _ & Hin1 & _)]; [contradiction|].
  destruct (alx_blocks _ _ _ LAWS lyN SN HpN WN memN mdN outN capN HARN Hin1) as (_ & Hp4 & _). split; [lia | exact Hin1]. }
assert (Hocz : outN <> 0 -> capN <> 0) by (intros Ho Hcc; exact (Ho (Hcz Hcc))).
assert (Hozc : outN = 0 -> capN = 0)
  by (intros Ho; destruct (Z.eq_dec capN 0) as [Hcc|Hcc]; [exact Hcc | exfalso; exact (proj1 (Hcnz Hcc) Ho)]).
pose proof (gr_ablocks_nodup_x lyN SN HpN WN memN mdN HARN) as NDN.
destruct HJ as (HSTK1 & HXO1 & (memS1 & HJi1 & HAG1) & HOUT1). rewrite !Z.add_0_r in HJi1.
assert (Hsp1 : spZ (ms_regs ms1) = spZ regsE + - SL_FRAME).
{ unfold spZ at 1. rewrite Q2, (EA 2%nat ltac:(lia)). change (bv_unsigned (getr regsN 2) = spZ regsE + - SL_FRAME).
  fold (spZ regsN). rewrite Hsp. lia. }
eapply (SRrG_bind SEGS R R_trans).
{ eapply (AREALLOC_R WN (ms_regs ms1) (ms_mem ms1) SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out)) ly S HpE W memS1 md []
    lyN SN HpN _ kN outN capN NC (- SL_FRAME) _ [] (Z.to_nat RR + kr)%nat HJi1).
  - destruct (Z.eq_dec capN 0) as [Hcc | Hcc]; [left; exact (Hcz Hcc) | right; exact (proj2 (Hcnz Hcc))].
  - rewrite Q10, E34. reflexivity.
  - exact G11.
  - unfold NC in *. clear - HMM Hsent Hnn HlenO. lia.
  - clear - HLR. lia.
  - exact (gr_cnt_round _ _ cap out capN outN rest HCNT HPerm0 HPerm1).
  - exact Hsp1.
  - rewrite HSF. reflexivity.
  - rewrite HSF. lia.
  - rewrite WS, HSF. unfold ASTACK. lia.
  - eapply (aj_stack_room_xR SEGS B PST ARx); [exact HJi1 | exact Hsp1 | rewrite WS, HSF; unfold ASTACK; lia].
  - rewrite Q3, (EA 3%nat ltac:(lia)). change (getr regsN 3 = w64 (as_gp B)). rewrite H3. exact Hgp.
  - rewrite Q4, (EA 4%nat ltac:(lia)). change (getr regsN 4 = w64 (as_tp B)). rewrite H4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - apply (achain_chain_pre lyN _ (spZ (ms_regs ms1)) (s0Z (ms_regs ms1)) [] (ms_regs ms1)).
    + apply achain_low. unfold s0Z. rewrite Q8, (EA 8%nat ltac:(lia)). change (bv_unsigned (getr regsN 8) < alloc_ceiling).
      rewrite R8. unfold w64. rewrite unsigned_lit_small by (clear - Hlen47 Hsent; lia). clear - HlenA C1. lia.
    + rewrite Hsp1. rewrite WS, HSF in *. clear - Hceil Hslo Hshi H47. lia.
    + reflexivity.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - (* route R: the realloc rule's call-boundary premises at the call memory (RO_ARx from the journal's ARx, HA from
       the call's mo_ok) *)
    exact (RO_ARx _ _ _ _ _ _ (proj1 HJi1)).
  - apply HA_call. apply (mok_station MT S SN (sl_cost MT c mx no cap len) spent _ MTL HMOK HMLE HmoN). clear - HCOST HCnn. lia.
  - (* the caller-context fact: the chain is cut, so the trace is the return address alone (HCTX_slr; W7's step,
       a working branch 7561b427559 lib/A/W_send_line_grow.v:614-618) *)
    unfold raZ. cbn [spine map]. rewrite Q1. rewrite unsigned_lit_small by lia.
    match goal with |- In [?x] _ =>
      replace x with (BASE + AF_fr_send_line + 0x110) by (try unfold AF_fr_send_line; try unfold BASE; ring) end.
    exact HCTX_slr.
  - exact HRM1.
  - intros Hp0 HinS i Hi.
    apply (Permutation_in _ HPerm0) in HinS. apply in_app_or in HinS. destruct HinS as [HinA | HinR].
    + exists (outN, outN + req_size capN). split; [|cbn [fst snd]; lia].
      unfold ablocks_fp. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ _ HinA).
    + exfalso. pose proof (Permutation_NoDup HPerm1 NDN) as ND1. unfold aout_blks in ND1.
      rewrite (proj2 (Z.eqb_neq capN 0) (Hocz Hp0)) in ND1. cbn [app] in ND1.
      apply NoDup_cons_iff in ND1 as [Hn1 _]. exact (Hn1 HinR).
  - apply (mok_station MT S SN (sl_cost MT c mx no cap len) spent _ MTL HMOK HMLE HmoN). clear - HCOST HCnn. lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & -> & HJ2i & HP2 & Hres10 & Hfrs2 & Hres4096 &
  HpermA & HpermB & Hcopy & Hkept2 & Hmle2 & HRM2 & Herr2 & Hpres2).

(* ---- after the call ---- *)
pose proof (proj1 HJi1) as HAR1.
pose proof (proj1 HJ2i) as HAR2.
destruct Hkept2 as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (gr_perm lyN SN ly2 S2 capN outN rest res NC HPerm1 Hcz (fun h => proj1 (Hcnz h)) HpermA HpermB) as P2.
assert (HRIN2 : In (res, NC) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym P2)); left; reflexivity).
assert (RQN : req_size NC = NC) by (unfold req_size; destruct (Z.eqb_spec NC 0) as [E0|E0]; [exfalso; unfold NC in E0; clear - E0 Hnn Hsent HlenO; lia | reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 res NC HAR2 HRIN2) as (Hr16 & Hr4096 & Hrceil & _ & Hrpres & _).
rewrite RQN in Hrceil, Hrpres.
assert (NOWN : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B lyN SN a /\ ~ aowned B ly2 S2 a).
{ intros a Hi Hno. split; intros Ho; apply Hno;
    [exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR1 Hi) Ho) | exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR2 Hi) Ho)]. }
assert (NBLK : forall a, in_img SEGS a -> ~ ((res <= a < res + req_size NC) \/ (outN <> 0 /\ outN <= a < outN + req_size capN))).
{ intros a Hi [Hr | (Hz & Ho)].
  - exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res NC a HAR2 HRIN2 Hr Hi).
  - exact (blk_img_x SEGS B ARx LAWS lyN SN HpN WN (ms_mem ms1) _ outN capN a HAR1 (proj2 (Hcnz (Hocz Hz))) Ho Hi). }
assert (GK : forall a, inG (G_SL B RG) a \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] a ->
  ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H WN) (ms_mem ms1) a /\
  (apresent (w_H WN) (ms_mem ms1) a -> apresent (w_H W2) mem2 a)).
{ intros a Hg He. assert (IO : in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B))
    by (destruct Hg as [Hg|Hg]; [exact (conj (proj1 (HG a Hg)) (proj1 (proj2 (HG a Hg)))) | exact (conj (proj1 (HGO a Hg)) (proj1 (proj2 (HGO a Hg))))]).
  destruct IO as [Hi Hno]. destruct (NOWN a Hi Hno) as [N1 N2].
  split; [exact (K3 a Hi Hno He) | exact (Hpres2 a Hi N1 N2 He (NBLK a Hi))]. }
pose proof (sl_rgd B RG HRGD 7 10 ltac:(lia) ltac:(lia) ltac:(lia)) as DE7.
pose proof (sl_rgd B RG HRGD 8 10 ltac:(lia) ltac:(lia) ltac:(lia)) as DE8.
pose proof (sl_rgd B RG HRGD 9 10 ltac:(lia) ltac:(lia) ltac:(lia)) as DE9.
cbn [nth] in DE7, DE8, DE9. unfold zdisj in DE7, DE8, DE9. cbn [fst snd] in DE7, DE8, DE9.
assert (N13 : VAL 254%nat = rg_nout RG) by exact HV13.
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 ([] : list nat) HS2.

match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (Ea40 : ew Ea 40 = w64 res) by (rewrite HEa; exact Hres10).
clear HEa.
(* g_capout and g_out are written through s8 and s4 (0x82848 / 0x8284c store through the hi atoms): two empty
   writable regions on those atoms *)
pose proof (pa_obj_img 14 ltac:(lia)) as Q14. pose proof (pa_obj_img 15 ltac:(lia)) as Q15.
rewrite HV14 in Q14. rewrite HV15 in Q15.
assert (N23 : VAL 303%nat + 864 = rg_capout RG) by exact HH23.
assert (N24 : VAL 304%nat + 892 = rg_out RG) by exact HH24.
assert (WR1 : forall a, (rg_capout RG <= a < rg_capout RG + 8) \/ (rg_out RG <= a < rg_out RG + 8) ->
  writable_at SEGS (mrestrict (w_H W2) mem2) a).
{ intros a Ha.
  assert (Hg : inG (G_SL B RG) a) by (clear - Ha; destruct Ha as [Ha|Ha]; ing_tac).
  assert (He : ~ (as_errno B <= a < as_errno B + 4)) by (clear - Ha DE8 DE9; lia).
  apply (gr_wr_kept2 _ _ _ _ a (proj2 (GK a (or_introl Hg) He))).
  apply (gr_wr_kept2 (w_H WN) (w_H WN) memN (ms_mem ms1) a).
  - intros Hp. apply (apresent_grows _ _ _ _ HG1). apply (apresent_grows _ _ _ _ HG0). exact Hp.
  - destruct Ha as [Ha|Ha].
    + replace a with (rg_capout RG + (a - rg_capout RG)) by lia. apply Wcap. lia.
    + replace a with (rg_out RG + (a - rg_out RG)) by lia. apply Wout. lia. }
assert (BV303 : base_val Ea (Some 303%nat) = VAL 303%nat) by (cbn [base_val]; exact (HEIa 303%nat ltac:(cbv; lia))).
assert (BV304 : base_val Ea (Some 304%nat) = VAL 304%nat) by (cbn [base_val]; exact (HEIa 304%nat ltac:(cbv; lia))).
pose proof (st_ok_pi_add_region Ea _ _ (YP09.mkRegion (Some 304%nat) 892 900 892 900 []) HS eq_refl) as HSa.
match type of HSa with ?t1 -> ?t2 -> _ => assert (RO1 : t1); [|assert (RD1 : t2); [|specialize (HSa RO1 RD1)]] end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
  rewrite BV304. split; [clear - N24 Q15; lia|]. split; [clear - N24 Q15; lia|].
  split; [intros o Ho; apply WR1; right; clear - Ho N24; lia | apply Forall_nil]. }
{ cbn. exact I. }
clear HS RO1 RD1. rename HSa into HS.
pose proof (st_ok_pi_add_region Ea _ _ (YP09.mkRegion (Some 303%nat) 864 872 864 872 []) HS eq_refl) as HSa.
match type of HSa with ?t1 -> ?t2 -> _ => assert (RO1 : t1); [|assert (RD1 : t2); [|specialize (HSa RO1 RD1)]] end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
  rewrite BV303. split; [clear - N23 Q14; lia|]. split; [clear - N23 Q14; lia|].
  split; [intros o Ho; apply WR1; left; clear - Ho N23; lia | apply Forall_nil]. }
{ pose proof (sl_rgd B RG HRGD 8 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D89.
  cbn [nth] in D89. unfold zdisj in D89. cbn [fst snd] in D89.
  cbn [ss_mem all_disjoint]. split; [|exact I]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV303, BV304. clear - D89 N23 N24; lia. }
clear HS RO1 RD1. rename HSa into HS.
assert (HFa : afact_ok Ea 40 (mkAF 4096 (2 ^ 47) 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ea40. unfold w64. rewrite unsigned_lit_small by (clear - Hrceil Hr4096 C1 HNC1; lia).
  change (2 ^ 4) with 16. rewrite Hr16. clear - Hrceil Hr4096 C1 HNC1; lia. }
pose proof (st_ok_pi_add_fact Ea _ _ 40%nat _ HS HFa) as HSa. clear HS HFa. rename HSa into HS.
assert (HJ2 : ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out)) ly S HpE W mem md []
  ly2 S2 Hp2 W2 mem2 md2 (kN + 3)).
{ apply (ajournal_gx_pack_xR SEGS B PST ARx (G_SL B RG) 0 [] SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out)) ly S HpE W mem md []
    ly2 S2 Hp2 W2 mem2 md2 (kN + 3) memS1); [lia | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG1 | apply out_none]. }
clear BVE.
assert (BVE : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val Ea (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEIa m Hm)).
assert (SHOK2 : sh_ok SEGS BxL [] Ea (mrestrict (w_H W2) mem2)) by constructor.
lrun_to RUNTOG HS HJ2 SHOK2 LBspan 1380%Z.
{ apply awr_ok_x_cons_g; [awr_g 303%nat N23|].
  apply awr_ok_x_cons_g; [awr_g 304%nat N24|].
  apply awr_ok_x_nil. }

lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms3 end.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR3.
(* ---- what each stretch kept ---- *)
assert (KV1 : forall x, 0 <= x < 2 ^ 64 -> ~ (rg_capout RG <= x < rg_capout RG + 8) -> ~ (rg_out RG <= x < rg_out RG + 8) ->
  aview SEGS (w_H WN) (ms_mem ms1) x = aview SEGS (w_H WN) memN x).
{ intros x Hx N1 N2.
  rewrite (aview_kept_out E _ (w_H WN) (ms_mem ms) (ms_mem ms1) HFr0 x Hx).
  - apply (aview_kept_out E _ (w_H WN) memN (ms_mem ms) HFr x Hx).
    intros (rr & Hin & Hr). vm_compute in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?(HEI 255%nat ltac:(cbv; lia)), ?(HEI 256%nat ltac:(cbv; lia)), ?N14, ?N15 in Hr; clear - Hr N1 N2; lia.
  - intros (rr & Hin & Hr). vm_compute in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?(HEI 255%nat ltac:(cbv; lia)), ?(HEI 256%nat ltac:(cbv; lia)), ?N14, ?N15 in Hr; clear - Hr N1 N2; lia. }
assert (KP1 : forall x, apresent (w_H WN) memN x -> apresent (w_H WN) (ms_mem ms1) x)
  by (intros x Hp; apply (apresent_grows _ _ _ _ HG1); apply (apresent_grows _ _ _ _ HG0); exact Hp).
assert (KV3 : forall x, 0 <= x < 2 ^ 64 -> ~ (rg_capout RG <= x < rg_capout RG + 8) -> ~ (rg_out RG <= x < rg_out RG + 8) ->
  aview SEGS (w_H W2) (ms_mem ms3) x = aview SEGS (w_H W2) mem2 x).
{ intros x Hx N1 N2. apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem ms3) HFr1 x Hx).
  intros (rr & Hin & Hr). vm_compute in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?(HEIa 303%nat ltac:(cbv; lia)), ?(HEIa 304%nat ltac:(cbv; lia)) in Hr; clear - Hr N1 N2 N23 N24; lia. }
assert (KP3 : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) (ms_mem ms3) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ HG2 Hp)).

assert (SPB : alloc_ceiling + SL_STK <= spZ regsE /\ spZ regsE <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47; lia).
assert (CI : forall x, (rg_capout RG <= x < rg_capout RG + 8) \/ (rg_out RG <= x < rg_out RG + 8) -> in_img SEGS x)
  by (intros x Hx; assert (Hg : inG (G_SL B RG) x) by (clear - Hx; destruct Hx as [Hx|Hx]; ing_tac); exact (proj1 (HG x Hg))).
assert (FK : forall x, spZ regsE - SL_FRAME <= x < spZ regsE ->
  aview SEGS (w_H W2) (ms_mem ms3) x = aview SEGS (w_H WN) memN x)
  by (intros x Hx; assert (Hx64 : alloc_ceiling <= x < 2 ^ 64) by (rewrite WS, HSF in *; clear - Hx SPB C1; lia);
  assert (N1 : ~ (rg_capout RG <= x < rg_capout RG + 8)) by (clear - Hx64 Q14 C1; lia);
  assert (N2 : ~ (rg_out RG <= x < rg_out RG + 8)) by (clear - Hx64 Q15 C1; lia);
  rewrite (KV3 x ltac:(clear - Hx64 C1; lia) N1 N2);
  rewrite (K1 x Hx64 ltac:(rewrite HSF in *; clear - Hx; lia)); exact (KV1 x ltac:(clear - Hx64 C1; lia) N1 N2)).
assert (ERRN : forall x, as_errno B <= x < as_errno B + 4 -> aview SEGS (w_H WN) memN x <> None)
  by (intros x Hx; unfold aview; unfold arm in Vev;
  pose proof (Vev (Z.to_nat (x - as_errno B)) ltac:(clear - Hx; lia)) as Hvv;
  replace (as_errno B + Z.of_nat (Z.to_nat (x - as_errno B))) with x in Hvv by (clear - Hx; lia);
  rewrite Hvv; cbn [option_map]; discriminate).
assert (CV : forall x, inG (G_SL B RG) x \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x ->
  ~ (rg_capout RG <= x < rg_capout RG + 8) -> ~ (rg_out RG <= x < rg_out RG + 8) ->
  aview SEGS (w_H W2) (ms_mem ms3) x = aview SEGS (w_H WN) memN x)
  by (intros x Hg N1 N2;
  assert (Hi : in_img SEGS x) by (destruct Hg as [Hg|Hg]; [exact (proj1 (HG x Hg)) | exact (proj1 (HGO x Hg))]);
  assert (Hx64 : 0 <= x < 2 ^ 64) by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl C5; unfold kLowMemEnd in *; lia);
  rewrite (KV3 x Hx64 N1 N2), <- (KV1 x Hx64 N1 N2);
  destruct (Z_le_gt_dec (as_errno B) x) as [He1|He1]; [destruct (Z_lt_ge_dec x (as_errno B + 4)) as [He2|He2]|];
  [ pose proof (Herr2 (x - as_errno B) ltac:(lia)) as Hee;
    replace (as_errno B + (x - as_errno B)) with x in Hee by lia; exact Hee
  | exact (proj1 (GK x Hg ltac:(lia)))
  | exact (proj1 (GK x Hg ltac:(lia))) ]).
assert (CK : forall x, inG (G_SL B RG) x \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x ->
  ~ (rg_capout RG <= x < rg_capout RG + 8) -> ~ (rg_out RG <= x < rg_out RG + 8) ->
  abyte_kept WN memN W2 (ms_mem ms3) x)
  by (intros x Hg N1 N2; split; [exact (CV x Hg N1 N2)|]; intros Hw;
  assert (Hi : in_img SEGS x) by (destruct Hg as [Hg'|Hg']; [exact (proj1 (HG x Hg')) | exact (proj1 (HGO x Hg'))]);
  destruct (Z_le_gt_dec (as_errno B) x) as [He1|He1]; [destruct (Z_lt_ge_dec x (as_errno B + 4)) as [He2|He2]|];
  [ assert (Hge : inG (G_SL B RG) x) by (clear - He1 He2; ing_tac);
    apply (gr_img_wr W2 (ms_mem ms3) x Hi (HGR x Hge)); rewrite (CV x Hg N1 N2); exact (ERRN x ltac:(lia))
  | apply (gr_wr_kept2 (w_H WN) (w_H W2) memN (ms_mem ms3) x); [|exact Hw];
    intros Hp; apply KP3; apply (proj2 (GK x Hg ltac:(lia))); apply KP1; exact Hp
  | apply (gr_wr_kept2 (w_H WN) (w_H W2) memN (ms_mem ms3) x); [|exact Hw];
    intros Hp; apply KP3; apply (proj2 (GK x Hg ltac:(lia))); apply KP1; exact Hp ]).

assert (LBLK : forall q m, In (q, m) (ablocks B lyN SN) -> q <> outN -> In (q, m) rest)
  by (intros q m Hin Hq; apply (Permutation_in _ HPerm1) in Hin; apply in_app_or in Hin;
  destruct Hin as [Hin | Hin]; [|exact Hin]; exfalso; unfold aout_blks in Hin;
  destruct (capN =? 0); [destruct Hin | destruct Hin as [Heq | []]; injection Heq as <- <-; exact (Hq eq_refl)]).
assert (LK : forall x, line <= x < line + len -> aview SEGS (w_H W2) (ms_mem ms3) x = aview SEGS (w_H WN) memN x)
  by (intros x Hx;
  assert (Hx64 : 0 <= x < 2 ^ 64) by (clear - Hx Hline0 Hline1; lia);
  assert (N1 : ~ (rg_capout RG <= x < rg_capout RG + 8)) by (intros HcX; apply (HLG x Hx); clear - HcX; ing_tac);
  assert (N2 : ~ (rg_out RG <= x < rg_out RG + 8)) by (intros HcX; apply (HLG x Hx); clear - HcX; ing_tac);
  rewrite (KV3 x Hx64 N1 N2), <- (KV1 x Hx64 N1 N2);
  destruct HLOK as [H0 | [(q & m & Hin & Hq & Hql & Hqm) | (Himg & _ & Hno)]];
  [ clear - H0 Hsent; lia
  | pose proof (gr_sep_head_x ly2 S2 Hp2 W2 mem2 md2 (res, NC) rest (q, m) HAR2 P2 (LBLK q m Hin Hq)) as DR;
    unfold zdisjoint, block_rng in DR; cbn [fst snd] in DR; rewrite RQN in DR;
    assert (NE : ~ ((res <= q + (x - q) < res + req_size NC) \/
                    (outN <> 0 /\ outN <= q + (x - q) < outN + req_size capN)))
      by (rewrite RQN; intros [Hr | (Ho0 & Ho)]; [clear - Hr DR Hql Hqm Hx; lia|];
          destruct (Hcnz (Hocz Ho0)) as (_ & Hoin);
          pose proof (sep_blocks_x SEGS B ARx LAWS lyN SN HpN WN memN mdN q m outN capN HARN Hin Hoin
            ltac:(intros Heq; injection Heq as Heq _; exact (Hq Heq))) as DO;
          unfold zdisjoint in DO; cbn [fst snd] in DO; clear - Ho DO Hql Hqm Hx; lia);
    pose proof (K2 q m (x - q) Hin ltac:(clear - Hql Hqm Hx; lia) NE) as Kq;
    replace (q + (x - q)) with x in Kq by lia; exact Kq
  | assert (Hi : in_img SEGS x) by exact (Himg x Hx);
    destruct (Z_le_gt_dec (as_errno B) x) as [He1|He1]; [destruct (Z_lt_ge_dec x (as_errno B + 4)) as [He2|He2]|];
    [ pose proof (Herr2 (x - as_errno B) ltac:(lia)) as Hee;
      replace (as_errno B + (x - as_errno B)) with x in Hee by lia; exact Hee
    | exact (K3 x Hi (Hno x Hx) ltac:(lia))
    | exact (K3 x Hi (Hno x Hx) ltac:(lia)) ] ]).
assert (ROM3 : rom_view SEGS W2 (ms_mem ms3))
  by (intros x Hx; destruct (HROMO x Hx) as (HnG & Hpin & Hne & _);
  destruct (Exists_dec (in_zr x) (as_owned_static B) (gr_in_zr_dec x)) as [Hown | Hno];
  [ eapply (rom_pinned_view_x SEGS B ARx LAWS); [exact HAR3 | exact (Hpin Hown)]
  | assert (Hi : in_img SEGS x) by (destruct Hx as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]);
    assert (Hx64 : 0 <= x < 2 ^ 64) by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl C5; unfold kLowMemEnd in *; lia);
    assert (N1 : ~ (rg_capout RG <= x < rg_capout RG + 8)) by (intros HcX; apply HnG; clear - HcX; ing_tac);
    assert (N2 : ~ (rg_out RG <= x < rg_out RG + 8)) by (intros HcX; apply HnG; clear - HcX; ing_tac);
    rewrite (KV3 x Hx64 N1 N2), (K3 x Hi Hno Hne), (KV1 x Hx64 N1 N2); exact (HROM x Hx) ]).
assert (APK3 : apres_kept B W mem W2 (ms_mem ms3))
  by (intros x Hi Hno He Hp; apply KP3; destruct (NOWN x Hi Hno) as [O1 O2];
  apply (Hpres2 x Hi O1 O2 He (NBLK x Hi)); apply KP1; exact (HAPK x Hi Hno He Hp)).

assert (NBUF : exists junk, Z.of_nat (length junk) = NC - (no + sent) /\
  garr8 SEGS (arm W2 (ms_mem ms3)) res (bzs ((O ++ firstn (Z.to_nat sent) Bl) ++ junk)))
  by (apply (gr_newbuf WN memN W2 (ms_mem ms3) _ (no + sent) capN outN res NC);
  [ destruct Hblk as [(Hc0 & _ & Hn0) | (Hc1 & _ & _ & HJk)]; [left; split; assumption | right; split; [exact Hc1 | exact HJk]]
  | exact HlenO
  | unfold NC; clear - Hgrow Rc0 Hnn HlenO; lia
  | intros Hc1 i Hi;
    destruct (Hcnz ltac:(clear - Hc1; lia)) as (Ho0 & Hoin);
    destruct (alx_blocks _ _ _ LAWS lyN SN HpN WN memN mdN outN capN HARN Hoin) as (_ & Ho4096 & Hoceil & _);
    assert (RQC : req_size capN = capN) by (unfold req_size; destruct (Z.eqb_spec capN 0); [clear - Hc1 e; lia | reflexivity]);
    rewrite RQC in Hoceil;
    assert (Nr : ~ in_img SEGS (res + i))
      by (intros Hi'; apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res NC (res + i) HAR2 HRIN2); [rewrite RQN; clear - Hi Hgrow; unfold NC in *; lia | exact Hi']);
    assert (No : ~ in_img SEGS (outN + i))
      by (intros Hi'; apply (blk_img_x SEGS B ARx LAWS lyN SN HpN WN memN mdN outN capN (outN + i) HARN Hoin); [rewrite RQC; clear - Hi; lia | exact Hi']);
    rewrite (KV3 (res + i) ltac:(clear - Hi Hrceil Hr4096 C1 Hgrow; unfold NC in *; lia)
      ltac:(intros HcX; apply Nr; apply CI; left; exact HcX) ltac:(intros HcX; apply Nr; apply CI; right; exact HcX));
    rewrite (Hcopy Ho0 i ltac:(rewrite Z.min_l by (unfold NC in *; clear - Hgrow Hnn HlenO; lia); exact Hi));
    exact (KV1 (outN + i) ltac:(clear - Hi Hoceil Ho4096 C1; lia)
      ltac:(intros HcX; apply No; apply CI; left; exact HcX) ltac:(intros HcX; apply No; apply CI; right; exact HcX))
  | intros x Hx; apply KP3; exact (proj1 (Hrpres x Hx)) ]).
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RCAP.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as ROUT.
cbn [ms_mem restrict] in RCAP, ROUT.
assert (UNC : U Ea (SAlu ALU_ADD (SAlu ALU_SLL (SOff 18 0) (SLit 1)) (SAlu ALU_SLL (SOff 32 0) (SLit 1))) = NC)
  by (assert (U18 : U Ea (SOff 18 0) = n) by (apply (U_atom Ea 18 n (eq_trans (OLDa 18%nat ltac:(lia)) E18)); clear - Hnn Hlen47 Hsent; lia);
  assert (U32 : U Ea (SOff 32 0) = no + sent) by (apply (U_atom Ea 32 (no + sent) (eq_trans (OLDa 32%nat ltac:(lia)) E32)); clear - Rn47 HlenO; lia);
  assert (S18 : U Ea (SAlu ALU_SLL (SOff 18 0) (SLit 1)) = n * 2)
    by (rewrite gr_U_sll1; rewrite U18; clear - Hnn Hlen47 Hsent; lia);
  assert (S32 : U Ea (SAlu ALU_SLL (SOff 32 0) (SLit 1)) = (no + sent) * 2)
    by (rewrite gr_U_sll1; rewrite U32; clear - Rn47 HlenO; lia);
  rewrite gr_U_add; rewrite S18, S32; unfold NC; clear - Hnn Hlen47 Hsent Rn47 HlenO; lia).
assert (VCAP : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (rg_capout RG) 8 NC)
  by (rewrite <- N23; refine (field_of_region Ea _ 303 (VAL 303%nat) _ _ _ _ _ 864 8%N _ NC RCAP _ _ _ _ _);
  [ exact (HEIa 303%nat ltac:(cbv; lia)) | cbn [In]; left; reflexivity | rewrite denot_lit_U, UNC; reflexivity
  | change (8 * Z.of_N 8) with 64; unfold NC in *; clear - Hnn Hlen47 Hsent Rn47 HlenO; lia | cbn; lia ]).
assert (VOUT : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (rg_out RG) 8 res)
  by (rewrite <- N24; refine (field_of_region Ea _ 304 (VAL 304%nat) _ _ _ _ _ 892 8%N _ res ROUT _ _ _ _ _);
  [ exact (HEIa 304%nat ltac:(cbv; lia)) | cbn [In]; left; reflexivity | exact (den_atom0 Ea 40 res Ea40 ltac:(clear - Hrceil Hr4096 C1 HNC1; lia))
  | change (8 * Z.of_N 8) with 64; clear - Hrceil Hr4096 C1 HNC1; lia | cbn; lia ]).
assert (WCAP : awr W2 (ms_mem ms3) (rg_capout RG) 8)
  by (intros i Hi; destruct RCAP as (_ & _ & RW & _); cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in RW;
  pose proof (RW (864 + i) ltac:(clear - Hi; lia)) as Hw; rewrite BV303 in Hw;
  replace (VAL 303%nat + (864 + i)) with (rg_capout RG + i) in Hw by (clear - N23; lia); exact Hw).
assert (WOUT : awr W2 (ms_mem ms3) (rg_out RG) 8)
  by (intros i Hi; destruct ROUT as (_ & _ & RW & _); cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in RW;
  pose proof (RW (892 + i) ltac:(clear - Hi; lia)) as Hw; rewrite BV304 in Hw;
  replace (VAL 304%nat + (892 + i)) with (rg_out RG + i) in Hw by (clear - N24; lia); exact Hw).
pose proof (sl_rgd B RG HRGD 2 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D2_8.
pose proof (sl_rgd B RG HRGD 2 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D2_9.
pose proof (sl_rgd B RG HRGD 3 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D3_8.
pose proof (sl_rgd B RG HRGD 3 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D3_9.
pose proof (sl_rgd B RG HRGD 4 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D4_8.
pose proof (sl_rgd B RG HRGD 4 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D4_9.
pose proof (sl_rgd B RG HRGD 5 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D5_8.
pose proof (sl_rgd B RG HRGD 5 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D5_9.
pose proof (sl_rgd B RG HRGD 6 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D6_8.
pose proof (sl_rgd B RG HRGD 6 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D6_9.
pose proof (sl_rgd B RG HRGD 7 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D7_8.
pose proof (sl_rgd B RG HRGD 7 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D7_9.
pose proof (sl_rgd B RG HRGD 10 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D10_8.
pose proof (sl_rgd B RG HRGD 10 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D10_9.
cbn [nth] in D2_8, D2_9, D3_8, D3_9, D4_8, D4_9, D5_8, D5_9, D6_8, D6_9, D7_8, D7_9, D10_8, D10_9. unfold zdisj in D2_8, D2_9, D3_8, D3_9, D4_8, D4_9, D5_8, D5_9, D6_8, D6_9, D7_8, D7_9, D10_8, D10_9. cbn [fst snd] in D2_8, D2_9, D3_8, D3_9, D4_8, D4_9, D5_8, D5_9, D6_8, D6_9, D7_8, D7_9, D10_8, D10_9.

assert (OUT3 : aout_at B RG ly2 S2 W2 (ms_mem ms3) (CTL 3 0 0 0 evL) (O ++ firstn (Z.to_nat sent) Bl) mx (no + sent) NC res).
{ unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  split; [apply (akept_vm WN memN); [intros x Hx; simpl Z.of_nat in Hx; apply CK; [right; clear - Hx; repeat first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl] | clear - Hx D6_8; lia | clear - Hx D6_9; lia] | exact Vmx]|].
  split; [apply (akept_awr WN memN); [intros x Hx; apply CK; [right; clear - Hx; repeat first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl] | clear - Hx D6_8; lia | clear - Hx D6_9; lia] | exact Wmx]|].
  split; [apply (akept_vm WN memN); [intros x Hx; simpl Z.of_nat in Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D7_8; lia | clear - Hx D7_9; lia] | exact Vno]|].
  split; [apply (akept_awr WN memN); [intros x Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D7_8; lia | clear - Hx D7_9; lia] | exact Wno]|].
  split; [exact VCAP|]. split; [exact WCAP|]. split; [exact VOUT|]. split; [exact WOUT|].
  split; [apply (akept_vm WN memN); [intros x Hx; simpl Z.of_nat in Hx; apply CK; [right; clear - Hx; repeat first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl] | clear - Hx D2_8; lia | clear - Hx D2_9; lia] | exact Vcl]|].
  split; [apply (akept_awr WN memN); [intros x Hx; apply CK; [right; clear - Hx; repeat first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl] | clear - Hx D2_8; lia | clear - Hx D2_9; lia] | exact Wcl]|].
  split; [apply (akept_vm WN memN); [intros x Hx; simpl Z.of_nat in Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D3_8; lia | clear - Hx D3_9; lia] | exact Vbr]|].
  split; [apply (akept_awr WN memN); [intros x Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D3_8; lia | clear - Hx D3_9; lia] | exact Wbr]|].
  split; [apply (akept_vm WN memN); [intros x Hx; simpl Z.of_nat in Hx; apply CK; [right; clear - Hx; repeat first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl] | clear - Hx D5_8; lia | clear - Hx D5_9; lia] | exact Vdd]|].
  split; [apply (akept_awr WN memN); [intros x Hx; apply CK; [right; clear - Hx; repeat first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl] | clear - Hx D5_8; lia | clear - Hx D5_9; lia] | exact Wdd]|].
  split; [apply (akept_vm WN memN); [intros x Hx; simpl Z.of_nat in Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D4_8; lia | clear - Hx D4_9; lia] | exact Vei]|].
  split; [apply (akept_awr WN memN); [intros x Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D4_8; lia | clear - Hx D4_9; lia] | exact Wei]|].
  split; [apply (akept_vm WN memN); [intros x Hx; simpl Z.of_nat in Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D10_8; lia | clear - Hx D10_9; lia] | exact Vev]|].
  split; [apply (akept_awr WN memN); [intros x Hx; apply CK; [left; clear - Hx; ing_tac | clear - Hx D10_8; lia | clear - Hx D10_9; lia] | exact Wev]|].
  split; [exact Rev|]. split; [exact Hclr|]. split; [exact Hbrr|]. split; [exact Hddr|]. split; [exact Heir|].
  split; [exact Hmxr|]. split; [exact HlenO|].
  right. split; [unfold NC in *; clear - Hnn Hsent HlenO; lia|]. split; [unfold NC in *; clear - Hnn Hsent HlenO; lia|].
  split; [exact HRIN2 | exact NBUF]. }

pmkst HS.
prreg HS (2%bv : bv 5) J2. prreg HS (3%bv : bv 5) J3. prreg HS (4%bv : bv 5) J4.
prreg HS (8%bv : bv 5) J8. prreg HS (9%bv : bv 5) J9. prreg HS (18%bv : bv 5) J18. prreg HS (22%bv : bv 5) J22.
prreg HS (23%bv : bv 5) J23. prreg HS (20%bv : bv 5) J20. prreg HS (21%bv : bv 5) J21. prreg HS (24%bv : bv 5) J24.
prreg HS (25%bv : bv 5) J25. prreg HS (26%bv : bv 5) J26. prreg HS (27%bv : bv 5) J27.
apply (K W2 (ms_regs ms3) (ms_mem ms3) _).
unfold SLM_xR. cbv zeta. change (Z.of_nat (length Bl)) with len.
exists ly2, S2, Hp2, (kN + 3), evL, NC, res, (spent + (mo_malloc MT NC + mo_free MT)), rest.
split; [exact HJ2|].
split; [unfold spZ at 1; rewrite J2, (OLDa 2%nat ltac:(lia)), (EA 2%nat ltac:(lia)); exact Hsp|].
split; [rewrite J3, (OLDa 3%nat ltac:(lia)), (EA 3%nat ltac:(lia)); exact H3|].
split; [rewrite J4, (OLDa 4%nat ltac:(lia)), (EA 4%nat ltac:(lia)); exact H4|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact HraE|].
split.
{ unfold sl_regsM.
  split; [rewrite J8, (OLDa 8%nat ltac:(lia)), (EA 8%nat ltac:(lia)); exact R8|].
  split; [rewrite J9, (OLDa 9%nat ltac:(lia)), (EA 9%nat ltac:(lia)); exact R9|].
  split; [rewrite J18, (OLDa 18%nat ltac:(lia)), (EA 18%nat ltac:(lia)); exact R18|].
  split; [rewrite J22, (OLDa 22%nat ltac:(lia)), (EA 22%nat ltac:(lia)); exact R22|].
  split; [rewrite J23, (OLDa 23%nat ltac:(lia)), (EA 23%nat ltac:(lia)); exact R23|].
  split; [rewrite J20, (ew_img Ea 304%nat HEIa) by (cbv; lia); reflexivity|].
  split; [rewrite J21, (OLDa 21%nat ltac:(lia)), (EA 21%nat ltac:(lia)); exact R21|].
  split; [rewrite J24, (ew_img Ea 303%nat HEIa) by (cbv; lia); reflexivity|].
  split; [rewrite J25, (OLDa 25%nat ltac:(lia)), (EA 25%nat ltac:(lia)); exact R25|].
  split; [rewrite J26, (ew_img Ea 302%nat HEIa) by (cbv; lia); reflexivity|].
  rewrite J27, (OLDa 27%nat ltac:(lia)), (EA 27%nat ltac:(lia)); exact R27. }
split; [apply (gr_vm_kept WN W2 memN (ms_mem ms3)); [intros x Hx; simpl Z.of_nat in Hx; apply FK; rewrite HSF in *; clear - Hx; lia | exact M8]|].
split; [apply (gr_vm_kept WN W2 memN (ms_mem ms3)); [intros x Hx; simpl Z.of_nat in Hx; apply FK; rewrite HSF in *; clear - Hx; lia | exact M16]|].
split; [intros i Hi; apply (gr_vm_kept WN W2 memN (ms_mem ms3));
  [intros x Hx; simpl Z.of_nat in Hx; apply FK; rewrite HSF in *; clear - Hx Hi; lia | exact (HSV i Hi)]|].
split; [exact Hcl|]. split; [exact Hbr|]. split; [exact Hdd|]. split; [exact Hsent|]. split; [exact Hn|]. split; [exact Hev|].
split; [exact OUT3|].
split; [unfold NC; clear - Hnn HlenO; lia|].
split; [apply (gr_garr8_kept WN memN W2 (ms_mem ms3) line (bzs Bl) HGL); intros x Hx; rewrite gr_bzs_len in Hx; exact (LK x Hx)|].
split; [exact Hline0|]. split; [exact Hline1|]. split; [exact ROM3|].
split.
{ destruct HLOK as [H0 | [(q & m & Hin & Hq & Hql & Hqm) | Himg]]; [left; exact H0 | right; left | right; right; exact Himg].
  exists q, m.
  pose proof (gr_sep_head_x ly2 S2 Hp2 W2 mem2 md2 (res, NC) rest (q, m) HAR2 P2 (LBLK q m Hin Hq)) as DR.
  unfold zdisjoint, block_rng in DR. cbn [fst snd] in DR. rewrite RQN in DR.
  pose proof (gr_blk_req_pos_x lyN SN HpN WN memN mdN q m HARN Hin) as Rq1.
  split; [apply (Permutation_in _ (Permutation_sym P2)); right; exact (LBLK q m Hin Hq)|].
  split; [intros Hqr; subst q; clear - DR Rq1 HNC1; lia|].
  split; [exact Hql | exact Hqm]. }
split; [exact HLG|].
split; [exact Hcapq|].
split; [clear - HMM; lia|].
split; [pose proof (gr_bb lyN SN ly2 S2 capN outN res NC Hozc HpermA HpermB) as HBB; clear - HBB HLM2; lia|].
split; [exact APK3|].
split; [exact HMOK|].
split; [exact (mle_station MT S SN S2 spent _ MTL HMLE Hmle2)|].
split; [clear - HCOST; lia|].
split; [exact HPerm0|].
split; [unfold aout_blks; rewrite (proj2 (Z.eqb_neq NC 0) ltac:(clear - HNC1; lia)); cbn [app]; exact P2|].
split; [rewrite Hfrs2; exact HFR|].
(* the room the realloc left is SLM_xR's (the rounds after this one, on top of kr); the count premise is the entry's *)
split; [exact HRM2 | exact HCNT].
Qed.
End wR.
End c.
End b.
End a.
