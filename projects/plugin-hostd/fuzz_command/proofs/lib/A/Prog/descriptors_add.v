(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of descriptors_add (plugin-hostd/fuzz_command, 0x8ce34, 91
   instructions): record()'s table arm, and the assembly of the three segments
   (descriptors_add_s3.v's spill arm, descriptors_add_s4.v's middle segment, descriptors_add_s2.v's last segment),
   after proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v .. ACh8.v (the segment walk of cgif_close). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG PaLibH PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c xstrdup_c mix_call_c descriptors_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
RecBLemmas descriptors_add_s1 descriptors_add_m descriptors_add_s2 descriptors_add_s3 descriptors_add_s4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
(* the statement's own hypotheses (descriptors_add_c.v:62-65) *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's hypotheses: the facts the statement does not give yet, with the recorder walks' shared names
   (lib/A/Prog/CmdRecFacts.v states each as a lemma of the same name) *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
#[local] Set Default Proof Using "All".
#[local] Notation S1 f := (f B TL HB VOBJS cmd_prog_img cmd_prog_writable).
#[local] Notation S2 f := (f B MT TL HB VOBJS cmd_prog_img cmd_prog_writable SIGP TXSTRDUP TMIX_CALL MTL
  cmd_ro_ok_of_aro RRO RELRO_IMG cmd_ro_prog_apart cmd_heap_tail_vis).
#[local] Notation S3 f := (f B MT TL HB VOBJS cmd_prog_img cmd_prog_writable SIGP TXSTRDUP TMIX_CALL MTL
  cmd_ro_ok_of_aro RRO RELRO_IMG cmd_ro_prog_apart cmd_heap_tail_vis TRCF).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.

(* the address record() computes for the next entry of the table: g_rec + 16 + 56 * ncalls, in the form the
   symbolic executor leaves it (after YI04.v:270's denot_add_mul3) *)
Lemma da_denot_slot : forall E n m i b,
ew E n = Z_to_bv 64 i -> 0 <= i < 16 -> ew E m = Z_to_bv 64 b -> 0 <= b -> b + 16 + 56 * i < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 56)) (SLit 16)) (SOff m 0))
  = Z_to_bv 64 (b + 16 + 56 * i).
Proof.
intros E n m i b Hn Hi Hm Hb Hw. rewrite denot_lit_U. f_equal.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E n i Hn) by lia. rewrite (U_atom E m b Hm) by lia. rewrite !U_SLit.
rewrite (zcanon_id 56) by (unfold M64; lia). rewrite (zcanon_id 16) by (unfold M64; lia).
rewrite (zcanon_id (i * 56)) by (unfold M64; lia). rewrite (zcanon_id (i * 56 + 16)) by (unfold M64; lia).
rewrite (zcanon_id (i * 56 + 16 + b)) by (unfold M64; lia). lia.
Qed.

Theorem tdescriptors_add_holds : tdescriptors_add_spec B MT.
Proof.
unfold tdescriptors_add_spec.
intros ly S W regs mem md ch pu uri R O HPRE HROD HROK H10 Hpu HSTR HREP HEV HLIVE HMOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HTS : DESCRIPTORS_ADD_STK = 16560) by reflexivity.
destruct HREP as (Q & HA0 & HOQ).
pose proof HA0 as (Hg8 & Hs8 & Hap & HC0 & HAN0 & HRP0 & HSC0 & HOWN0).
pose proof HC0 as (Hlen16 & HlenQ & Vnc & HCA0 & HSP0' & HSPL0).
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S))
  by (intros pn Hpn; exact (proj1 (arep_lay_in _ _ _ _ R Q pn HA0 (proj1 (HOQ pn) Hpn)))).
(* the middle and last segments, from the join of record()'s two arms *)
assert (K : da_join_K B MT ly S W regs mem md R uri O pu)
  by (exact (S2 da_segB ly S W regs mem md ch pu uri R O HPRE HROD H10 Hpu HO HEV HLIVE HMOK)).
destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt | Hge].
- (* record() takes the next entry of g_rec.calls: 0x8ce34 .. 0x8ceac, no call *)
  set (n := Z.of_nat (length (r_calls R))) in *.
  destruct (S1 da_entry ly S W mem md regs n 0 15 HAR Hstk Hpres Vnc ltac:(lia) ltac:(lia)) as [HS SHOK].
  pose proof (ajournal_init SEGS B DESCRIPTORS_ADD_STK (da_FP O) ly S W regs mem md ch HPRE) as HJ.
  assert (HEI : img_env VAL A_LIM (da_E0 regs n)) by (unfold da_E0; apply Eimg_env).
  assert (Usp : bv_unsigned (ew (da_E0 regs n) 2) = spZ regs).
  { unfold da_E0. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
  assert (UG : bv_unsigned (ew (da_E0 regs n) DA_GREC) = A_G_REC).
  { rewrite (img_env_atomP (da_E0 regs n) DA_GREC HEI ltac:(unfold DA_GREC, A_OBJ, A_TEXT, A_LIM; lia)).
    rewrite (S1 da_grec_val). apply unsigned_lit_small. unfold A_G_REC; lia. }
  unfold cfg_at.
  paj_run_to_tok RUNTO HS HJ SHOK da_Bspan DA_JOIN.
  { unfold ss_da0, da_rs0, stack_region, got_regionP, bcell_regionP, da_ncalls. cbn [ss_mem].
    eapply awr_ok_cons_stack with (n := 2%nat);
      [reflexivity | exact Usp | cbn [YP09.r_wlo]; rewrite HTS; lia | cbn [YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen with (n := DA_GREC); [reflexivity | exact UG | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    apply (S1 da_awr_grec). unfold OFF_NCALLS, REC_SIZE in *. lia. }
  da_fold_md. rename HFr into HFr0. rename HG into HG0. clear HF.
  set (E := da_E0 regs n) in *.
  assert (E33 : ew E 33 = Z_to_bv 64 n).
  { subst E. unfold da_E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
  assert (E32 : ew E 32 = Z_to_bv 64 DA_SB).
  { subst E. unfold da_E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  assert (EG : ew E DA_GREC = Z_to_bv 64 A_G_REC)
    by (rewrite (img_env_atomP E DA_GREC HEI ltac:(unfold DA_GREC, A_OBJ, A_TEXT, A_LIM; lia)),
        (S1 da_grec_val); reflexivity).
  assert (ER : forall (r : bv 5), ew E (Z.to_nat (bv_unsigned r)) = getr regs r).
  { intros r. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    subst E. unfold da_E0. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
  (* the slot record() picked, and the write of the new call count *)
  set (c := A_G_REC + OFF_CALLS + CALL_SIZE * n) in *.
  assert (Hcok : da_slot_ok c) by (left; exists n; unfold REC_CALLS_MAX; split; [lia | reflexivity]).
  assert (HcJ : c = da_slot n)
    by (unfold da_slot; destruct (Z.eqb_spec n 16) as [He|_]; [lia | reflexivity]).
  assert (Hk0 : 0 = rec_spill_frees R)
    by (unfold rec_spill_frees; rewrite (proj2 (Nat.ltb_lt _ _) Hlt); reflexivity).
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19.
  prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  prreg HS (27%bv : bv 5) Q27.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ ?mm _; cfg_model := ?mdq |} _ =>
  (* the two windows this arm wrote: its own frame and g_rec.ncalls *)
  assert (KPE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
     ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W mm a = rdW W mem a) by
    (intros a Ha N1 N2; apply (aview_eq_of SEGS); apply HFr0;
     rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
     rewrite Z.mod_small by lia;
     intros (r & Hin & Hr); vm_compute in Hin;
     repeat (destruct Hin as [Hq | Hin];
       [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        try change 285%nat with DA_GREC in Hr;
        rewrite ?Usp, ?UG in Hr; unfold OFF_NCALLS in *; lia|]);
     destruct Hin);
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) da_frameM) in
    pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRf;
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) da_frameM) in
    pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRn;
    cbn [ms_mem restrict mkst] in HRf, HRn end;
  assert (HfrJ : da_frame_at (mrestrict (w_H W) mm) (spZ regs) regs) by
    (intros j r Hj;
     assert (Hj7 : (j < length da_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate);
     cbn [length da_saved] in Hj7;
     assert (Hj6 : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6)%nat) by lia;
     repeat (destruct Hj6 as [-> | Hj6]); [| | | | | | subst j];
     cbn [nth_error da_saved] in Hj; injection Hj as <-;
     match goal with |- val_mem _ _ (spZ regs - 8 - 8 * Z.of_nat ?jj) _ (bv_unsigned (getr regs (Z_to_bv 5 ?rr))) =>
       eapply (S2 da_field E _ 2%nat (spZ regs) _ (-64) 0 (-64) 0 (-8 - 8 * Z.of_nat jj) 8 (SOff (Z.to_nat rr) 0)
                 (bv_unsigned (getr regs (Z_to_bv 5 rr))));
       [ exact HRf | exact Usp | repeat (first [left; reflexivity | right])
       | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned;
         change (Z.to_nat rr) with (Z.to_nat (bv_unsigned (Z_to_bv 5 rr))); rewrite ER; reflexivity
       | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 rr))) as Hbr;
         change (bv_modulus 64) with (2 ^ 64) in Hbr; change (8 * Z.of_N 8) with 64; lia
       | change (Z.of_N 8) with 8; lia | lia | reflexivity ]
     end);
  assert (HNC1J : (length (r_calls R) < 16)%nat ->
     aval_mem (rdW W mm) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1)) by
    (intros _; apply (aval_mem_view SEGS);
     eapply (S2 da_field E _ DA_GREC A_G_REC _ 8 12 8 12 8 4 (SOff 33 1) (n + 1));
     [exact HRn | rewrite EG; apply unsigned_lit_small; unfold A_G_REC; lia
      | repeat (first [left; reflexivity | right])
      | cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity
      | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia
      | unfold OFF_NCALLS; lia | reflexivity]);
  assert (Hdec : forall a b : Z * Z, {a = b} + {a <> b}) by (decide equality; apply Z.eq_dec);
  apply (K ly S W rg mm mdq 0 (ablocks B ly S) (rdW W mem) R Q c HJ Hk0)
  end.
  + (* the registers at the join *)
    unfold da_regsJ.
    split; [rewrite Q2; cbn [sv_denot]; rewrite Usp; reflexivity|].
    split; [rewrite Q3; exact (ER 3%bv)|].
    split; [rewrite Q4; exact (ER 4%bv)|].
    split; [rewrite Q8;
      transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit 56)) (SLit 16)) (SOff DA_GREC 0)));
      [ cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | rewrite (da_denot_slot E 33%nat DA_GREC n A_G_REC E33 ltac:(lia) EG ltac:(unfold A_G_REC; lia)
                  ltac:(unfold A_G_REC in *; lia));
        change c with (A_G_REC + OFF_CALLS + CALL_SIZE * n); f_equal; unfold OFF_CALLS, CALL_SIZE; lia ]|].
    split; [rewrite Q9; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite (ER 10%bv); exact H10|].
    split; [rewrite Q19; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact EG|].
    split; [rewrite Q20; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E32|].
    intros r Hr.
    assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hr' as [-> | Hr']); [| | | | | subst r];
    [ replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Q22
    | replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Q23
    | replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Q24
    | replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Q25
    | replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Q26
    | replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Q27 ];
    match goal with |- _ = getr regs ?rb => exact (ER rb) end.
  + exact HfrJ.
  + exact HA0.
  + reflexivity.
  + exact HcJ.
  + exact HNC1J.
  + intros Hge'. lia.
  + intros a Ha N3. apply KPE;
    [ unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia
    | unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia
    | intros Hn4; apply N3; split; [exact Hlt | exact Hn4] ].
  + intros q kk i Hin Hi. pose proof (req_size_pos kk ltac:(lia)) as [_ Hrq].
    destruct (S2 da_blk_not_PG ly S W mem md q kk (q + i) HAR Hin ltac:(lia)) as [Hnp Hr].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q kk HAR Hin) as (_ & H4096 & Hcl & _).
    apply KPE; [exact Hr | lia |].
    intros Hn4. apply Hnp. apply recb_grec_in. unfold OFF_NCALLS, REC_SIZE in *. lia.
  + reflexivity.
  + intros pn Hpn. exact (proj2 (HOQ pn) Hpn).
  + intros pn Hpn _. exact Hpn.
  + intros pn Hpn. destruct (List.in_dec Hdec pn O) as [Ho | Ho];
    [right; exact (proj1 (HOQ pn) Ho) | left; split; [exact Hpn | exact Ho]].
  + rewrite <- Hk0. replace (0 * mo_free MT) with 0 by lia. exact (mo_le_refl MT MTL S).
  + lia.
  + (* the string at the join: its block is untouched (no call), its bytes are outside the two windows *)
    destruct HSTR as (x0 & -> & HBLK & HSTRx & HNL & _).
    exists x0. split; [reflexivity|]. split; [exact HBLK|]. split; [|exact HNL].
    apply (rastr_kept (rdW W mem)); [exact HSTRx|]. intros i Hi.
    pose proof HBLK as (q & kk & Hin & Hq1 & Hq2).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q kk HAR Hin) as (_ & H4096 & Hcl & _ & _ & _ & Hkk).
    pose proof (req_size_pos kk ltac:(lia)) as [_ Hrq].
    destruct (S2 da_blk_not_PG ly S W mem md q kk (pu + i) HAR Hin ltac:(lia)) as [Hnp Hr].
    apply KPE; [exact Hr | lia |].
    intros Hn4. apply Hnp. apply recb_grec_in. unfold OFF_NCALLS, REC_SIZE in *. lia.
- (* record() spills: 0x8ce34 .. 0x8ce8c, the call of rec_calls_free *)
  exact (S3 da_spill ly S W regs mem md ch pu uri R O HPRE HROD H10 Hpu HSTR
    (ex_intro _ Q (conj HA0 HOQ)) Hge HEV HMOK K).
Qed.

End e.
End f.
End d.
