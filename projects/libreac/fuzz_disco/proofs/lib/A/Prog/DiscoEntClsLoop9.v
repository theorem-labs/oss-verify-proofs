(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_set_resweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxSetResweep.v, with its module paths, module names and numbers changed; 174 of its 248 lines of code are new or changed and 208 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacHuntHeardAnything.v, with its module names changed; 158 of its 194 lines of code are new or changed and 212 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody
ClassifyCore ReacDiscoClassify ReacDiscoClassifyOnSegment CheckSighting ReacDiscoGateShouldPush DiscoEntClsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From Stdlib Require Import FunctionalExtensionality.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma cl9_w : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.add_mod_idemp_l. lia.
Qed.

Ltac cl9_rg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.

Ltac cl9_meq M :=
  lazymatch goal with HF : frame_of _ _ (ms_mem ?a) (ms_mem ?b) |- _ =>
    assert (M : ms_mem b = ms_mem a)
      by (apply functional_extensionality; intros x; apply HF; intros (r & Hr & _); vm_compute in Hr; destruct Hr);
    cbn [ms_mem mkst] in M;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma cl9_den : forall (regs : bvmap 5 word) (q : nat) (r : bv 5) x c, Z.of_nat q = bv_unsigned r -> (q < A_TEXT)%nat ->
  getr regs r = w64 x -> sv_denot (Eimg (Ereg regs [])) (SOff q c) = w64 (x + c).
Proof.
intros regs q r x c Hq Hl Hr. cbn [sv_denot]. rewrite (Eimg_low (Ereg regs []) q Hl), (ew_Ereg_nat regs [] q r Hq), Hr.
unfold w64. apply cl9_w.
Qed.

Lemma cl9_U : forall (regs : bvmap 5 word) (q : nat) (r : bv 5) x c, Z.of_nat q = bv_unsigned r -> (q < A_TEXT)%nat ->
  getr regs r = w64 x -> 0 <= x + c < 2 ^ 64 -> U (Eimg (Ereg regs [])) (SOff q c) = x + c.
Proof.
intros regs q r x c Hq Hl Hr Hb. unfold U. rewrite (cl9_den regs q r x c Hq Hl Hr). unfold w64.
apply unsigned_lit_small. exact Hb.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).

Lemma cl9_rL : forall cx (regs regs' : bvmap 5 word), d_rL B cx regs ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 8 = getr regs 8 ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 20 = getr regs 20 ->
  getr regs' 25 = getr regs 25 -> d_rL B cx regs'.
Proof.
intros cx regs regs' (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25) E2 E3 E4 E8 E9 E18 E20 E25.
unfold d_rL, spZ in *. rewrite E2, E3, E4, E8, E9, E18, E20, E25. repeat split; assumption.
Qed.

Lemma cl9_lmem : forall cx h i n now op nb fr len nn (regs regs' : bvmap 5 word) ly S (W : world SEGS) m,
  cl_lmem B cx h i n now op nb fr len nn regs ly S W m -> d_rL B cx regs' ->
  cl_lmem B cx h i n now op nb fr len nn regs' ly S W m.
Proof.
intros cx h i n now op nb fr len nn regs regs' ly S W m
  (Sg & G & push & (B1 & B2 & B3 & B4 & B5 & _ & Brest) & HSg & HG & HGn & HSpl) HrL.
exists Sg, G, push. split; [|split; [exact HSg | split; [exact HG | split; [exact HGn | exact HSpl]]]].
exact (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj HrL Brest)))))).
Qed.

Lemma cl9_at : forall cx pc kmax accmax
  (P : bvmap 5 word -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop)
  (fq : YK11.FPState) ly3 S3 (W : world SEGS) (ms : machine_state) md (mem3 : word -> option byte) kk acc,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md kk ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] -> 0 <= kk <= kmax -> st_nev S3 <= st_nev (c_S cx) + kmax ->
  mo_le MT (c_S cx) S3 acc -> acc <= accmax ->
  ms = mkst (fx := fq) (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (ms_mem ms) (seg_rom SEGS) ->
  ms_mem ms = mem3 ->
  P (ms_regs ms) ly3 S3 W mem3 md ->
  DAT cx pc kmax accmax P W (mkCfg ms md).
Proof.
intros cx pc kmax accmax P fq ly3 S3 W ms md mem3 kk acc Hfrm HB HJ HF Hk Hev Hmo Hacc Hms Hm HP.
exists fq, ly3, S3, (ms_regs ms), mem3, md, kk, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hm; reflexivity|].
rewrite Hm in HJ. repeat (split; [assumption|]). exact HP.
Qed.

Theorem cl_L9 : cl_L9_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold cl_L9_stmt. intros cx h i n now op nb fr len nn k j W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & kk & acc & -> & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  HLM & HJR & Ha0).
pose proof HLM as (Sg & G & push & HCB & _ & HG & HGn & _).
pose proof HG as (_ & _ & _ & HGr & _).
rewrite HGn in HGr.
pose proof HJR as (Hkj & Hjn & R23 & R24 & R21 & R26 & R19 & R22 & R27).
pose proof HCB as (_ & _ & _ & _ & _ & HrL & _).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EV : forall (q : nat) (r : bv 5) x c0, Z.of_nat q = bv_unsigned r -> (q < A_TEXT)%nat -> getr regs r = w64 x ->
  sv_denot E (SOff q c0) = w64 (x + c0)) by (intros; subst E; apply (cl9_den regs q r); assumption).
assert (UV : forall (q : nat) (r : bv 5) x c0, Z.of_nat q = bv_unsigned r -> (q < A_TEXT)%nat -> getr regs r = w64 x ->
  0 <= x + c0 < 2 ^ 64 -> U E (SOff q c0) = x + c0) by (intros; subst E; apply (cl9_U regs q r); assumption).
assert (UL : U E (SLit 0) = 0) by (apply U_lit; lia).
assert (U10 : U E (SOff 10 0) = bv_unsigned (getr regs 10)).
{ subst E. unfold U. rewrite sv_denot_SOff0, Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl). reflexivity. }
assert (HS : st_ok_pi (fx := fq) SEGS VAL E (mkSS 0xdb0 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + 0xdb0)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. subst E.
  apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
unfold cfg_at. change (w64 (BASE + 0xdb0)) with (Z_to_bv 64 (BASE + 0xdb0)).
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_disco) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
apply (BR W _ _ _ _ _ BC_NE (SOff 10 0) (SLit 0) HS); intros Hc HS1; clear HS;
  [| exfalso; rewrite branch_ne_U, U10, UL in Hc; apply negb_false_iff, Z.eqb_eq in Hc;
     apply Ha0; apply bv_eq; rewrite Hc; reflexivity ].
paj_run_to_sh RUNTO HS1 HJ 0xda0; [awr_ok_tac|].
cl9_meq M1.
apply (BR W _ _ _ _ _ BC_NE (SOff 27 (-1)) (SLit 0) HS1); intros Hc2 HS2; clear HS1;
  rewrite branch_ne_U, (UV 27%nat 27%bv (nn - j) (-1) eq_refl ltac:(unfold A_TEXT; lia) R27 ltac:(lia)), UL in Hc2.
- apply negb_true_iff, Z.eqb_neq in Hc2.
  paj_run_to_sh RUNTO HS2 HJ 0xda0; [awr_ok_tac|].
  cl9_meq M2.
  apply SRr_ret. left. unfold cl_LJ.
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?msf) =>
    apply (cl9_at cx 0xda0 _ _ _ fq ly3 S3 W msf _ mem3 kk acc Hfrm Hbase HJ Hfrs Hk Hnev Hmo Hacc);
    [ exact (st_ok_pi_restrict_mkst _ _ _ _ HS2 eq_refl) | congruence | cbv beta ];
    cl9_rg HS2 (22%bv : bv 5) G22; cl9_rg HS2 (27%bv : bv 5) G27;
    pose proof (regs_kept_of_st_ok_pi E _ _ regs [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26]%bv HS2 HAE
      ltac:(vm_compute; reflexivity)) as RK;
    cbn [ms_regs restrict] in RK
  end.
  rewrite (EV 22%nat 22%bv _ 32 eq_refl ltac:(unfold A_TEXT; lia) R22) in G22.
  rewrite (EV 27%nat 27%bv _ (-1) eq_refl ltac:(unfold A_TEXT; lia) R27) in G27.
  split.
  + apply (cl9_lmem _ _ _ _ _ _ _ _ _ _ regs _ _ _ _ _ HLM).
    apply (cl9_rL cx regs _ HrL); apply RK; cbn; tauto.
  + unfold cl_jregs. rewrite G22, G27, !RK by (cbn; tauto).
    split; [lia|]. split; [lia|]. split; [exact R23|]. split; [exact R24|]. split; [exact R21|].
    split; [exact R26|]. split; [exact R19|]. split; f_equal; lia.
- apply negb_false_iff, Z.eqb_eq in Hc2.
  paj_run_to_sh RUNTO HS2 HJ 0xd80; [awr_ok_tac|].
  cl9_meq M2.
  apply (BR W _ _ _ _ _ BC_NE (SOff 23 0) (SOff 24 0) HS2); intros Hc3 HS3; clear HS2;
    rewrite branch_ne_U, (UV 23%nat 23%bv (k + 1) 0 eq_refl ltac:(unfold A_TEXT; lia) R23 ltac:(lia)),
      (UV 24%nat 24%bv nn 0 eq_refl ltac:(unfold A_TEXT; lia) R24 ltac:(lia)) in Hc3;
    [| exfalso; apply negb_false_iff, Z.eqb_eq in Hc3; lia ].
  paj_run_to_sh RUNTO HS3 HJ 0xd80; [awr_ok_tac|].
  cl9_meq M3.
  apply SRr_ret. right. left. unfold cl_LI.
  lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msf) =>
    apply (cl9_at cx 0xd80 _ _ _ fq ly3 S3 W msf _ mem3 kk acc Hfrm Hbase HJ Hfrs Hk Hnev Hmo Hacc);
    [ exact (st_ok_pi_restrict_mkst _ _ _ _ HS3 eq_refl) | congruence | cbv beta ];
    cl9_rg HS3 (21%bv : bv 5) G21; cl9_rg HS3 (26%bv : bv 5) G26;
    pose proof (regs_kept_of_st_ok_pi E _ _ regs [] [2; 3; 4; 8; 9; 18; 20; 23; 24; 25]%bv HS3 HAE
      ltac:(vm_compute; reflexivity)) as RK;
    cbn [ms_regs restrict] in RK
  end.
  rewrite (EV 21%nat 21%bv _ 32 eq_refl ltac:(unfold A_TEXT; lia) R21) in G21.
  rewrite (EV 26%nat 26%bv _ (-1) eq_refl ltac:(unfold A_TEXT; lia) R26) in G26.
  split.
  + apply (cl9_lmem _ _ _ _ _ _ _ _ _ _ regs _ _ _ _ _ HLM).
    apply (cl9_rL cx regs _ HrL); apply RK; cbn; tauto.
  + rewrite G21, G26, !RK by (cbn; tauto).
    split; [lia|]. split; [exact R23|]. split; [exact R24|]. split; f_equal; lia.
Qed.

End h.
End f.
End d.
