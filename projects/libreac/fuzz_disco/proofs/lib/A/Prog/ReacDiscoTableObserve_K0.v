(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 308 of its 345 lines of code are new or changed and 32 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI0m.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3u.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow DiscoSyms DiscoList DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve ReacDiscoTableObserve_C.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacDiscoTableObserve_M.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve_X.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_observe_c reac_disco_table_observe.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
Module DTC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table_c.
Module RDOC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe_c.
Module RDO := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe.
Module DT := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table.
Module FM := OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib.Mem.
Module TM := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog.ReacDiscoTableObserve_M.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac tk_agree := split; [intros ? ?; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity].
Ltac tk_vl := repeat first
  [ rewrite FM.length_Z_to_le_bytes
  | rewrite DT.length_sub by lia
  | rewrite RDO.upd_len by (tk_vl; lia)
  | rewrite TM.ent_len by (first [assumption | lia])
  | progress cbn [length] ].
Ltac tk_nth := repeat first
  [ rewrite TM.upd_nth_out by (tk_vl; lia)
  | rewrite TM.upd_nth_in by (tk_vl; lia) ].
Ltac tk_close := lazymatch goal with |- nth_error ?l ?x = nth_error ?l ?y => replace y with x by lia; reflexivity end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma tk_sext32 : forall E d s, 0 <= s -> (Z.to_nat s + 4 <= length (ed E d))%nat ->
  sv_denot E (SExt true 32 (SData d s 4)) = Z_to_bv 64 (DTC.s32_at (ed E d) s).
Proof.
intros E d s Hs Hl. cbn [sv_denot]. unfold data_word, DTC.s32_at, DTC.u_at, DTC.sub.
exact (DT.lw_val (firstn 4 (skipn (Z.to_nat s) (ed E d))) ltac:(rewrite length_firstn, length_skipn; lia)).
Qed.
Lemma tk_sx_G : forall G E, ed E 1 = G -> length G = 24%nat ->
  sv_denot E (SExt true 32 (SData 1 8 4)) = Z_to_bv 64 (DTC.s32_at G 8).
Proof. intros G E He Hl. rewrite tk_sext32 by (try rewrite He; lia). rewrite He. reflexivity. Qed.
Lemma tk_sx_e : forall Tc r E, ed E 2 = DTC.sub Tc (48 * r) 48 -> length Tc = 400%nat -> 0 <= r < 8 ->
  sv_denot E (SExt true 32 (SData 2 8 4)) = Z_to_bv 64 (DTC.s32_at Tc (48 * r + 8)).
Proof.
intros Tc r E He Hl Hr. rewrite tk_sext32 by (try rewrite He; try rewrite DT.length_sub by lia; lia).
rewrite He. unfold DTC.s32_at. change (DTC.sub Tc (48 * r) 48) with (TM.ent Tc r).
rewrite TM.u_at_ent by (first [exact Hl | lia]). reflexivity.
Qed.
Lemma tk_dG : forall G E s, ed E 1 = G -> sv_denot E (SData 1 s 1) = Z_to_bv 64 (DTC.u_at G s 1).
Proof. intros G E s He. cbn [sv_denot]. unfold data_word. rewrite He. reflexivity. Qed.
Lemma tk_dE : forall Tc r E s, ed E 2 = DTC.sub Tc (48 * r) 48 -> length Tc = 400%nat -> 0 <= r < 8 -> 0 <= s < 48 ->
  sv_denot E (SData 2 s 1) = Z_to_bv 64 (DTC.u_at Tc (48 * r + s) 1).
Proof.
intros Tc r E s He Hl Hr Hs. cbn [sv_denot]. unfold data_word. rewrite He.
change (bytes_le_to_Z (firstn (N.to_nat 1) (skipn (Z.to_nat s) (DTC.sub Tc (48 * r) 48)))) with (DTC.u_at (TM.ent Tc r) s 1).
rewrite TM.u_at_ent by (first [exact Hl | lia]). reflexivity.
Qed.
Lemma tk_byte_le8 : forall v i, 0 <= v < 2 ^ 64 -> 0 <= i < 8 ->
  Some (byte_of_word (Z_to_bv 64 v) i) = nth_error (Z_to_le_bytes 8 v) (Z.to_nat i).
Proof.
intros v i Hv Hi. destruct (Z_of_nat_complete i ltac:(lia)) as (k & ->). rewrite Nat2Z.id.
assert (Hb : bytes_le_to_Z (Z_to_le_bytes 8 v) = v).
{ rewrite FM.bytes_le_to_Z_to_le_bytes by lia. apply Z.mod_small. change (8 * Z.of_nat 8) with 64. lia. }
rewrite <- Hb at 1.
rewrite byte_of_word_le by (rewrite FM.length_Z_to_le_bytes; lia).
symmetry. apply nth_error_nth'. rewrite FM.length_Z_to_le_bytes. lia.
Qed.
Lemma tk_byte_data : forall E d s (n : N) i, 0 <= s -> (Z.to_nat s + N.to_nat n <= length (ed E d))%nat ->
  (N.to_nat n <= 8)%nat -> 0 <= i < Z.of_N n ->
  Some (byte_of_word (Z_to_bv 64 (data_word E d s n)) i) = nth_error (ed E d) (Z.to_nat (s + i)).
Proof.
intros E d s n i Hs Hl Hn Hi. destruct (Z_of_nat_complete i ltac:(lia)) as (k & ->).
rewrite (byte_of_data_word E d s n k Hs Hl Hn ltac:(lia)). f_equal. lia.
Qed.
Lemma tk_reg_lit : forall E ss ms H (q : bv 5) z, st_ok_pi SEGS VAL E ss (restrict H ms) ->
  sr_get (ss_regs ss) q = SLit z -> YK11.getr (ms_regs ms) q = Z_to_bv 64 z.
Proof. intros E ss ms H q z HS Hq. rewrite (st_ok_pi_restrict_reg H E ss ms q HS), Hq. reflexivity. Qed.
Lemma tk_atom_denot : forall c regs1 Tc r E n (x : bv 5) v, YP06.env_agree 64 (tobs_env c regs1 Tc r) E ->
  (n < 32)%nat -> Z.of_nat n = bv_unsigned x -> YK11.getr regs1 x = w64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros c regs1 Tc r E n x v [HA _] Hn Hx Hv. cbn [sv_denot]. rewrite HA by lia.
rewrite (tobs_env_reg c regs1 Tc r n x Hx), Hv. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma tk_frame_step : forall k E0 E rs0 rs m0 m1 m2,
  frame_of E0 rs0 m0 m1 -> frame_of E rs m1 m2 ->
  YP06.env_agree k E0 E -> mem_atoms_lt k rs0 = true -> skeleton rs = skeleton rs0 ->
  frame_of E0 rs0 m0 m2.
Proof.
intros k E0 E rs0 rs m0 m1 m2 H01 H12 HA Hat Hsk.
eapply frame_of_trans; [symmetry; exact Hsk | exact H01 |].
exact (frame_of_agree_skel k E0 E rs0 rs m1 m2 HA Hat Hsk H12).
Qed.
Lemma tk_regs_kept : forall c regs1 Tc r E ss ms H l,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  regs_ok (tobs_env c regs1 Tc r) tobs_sr regs1 ->
  YP06.env_agree 32 (tobs_env c regs1 Tc r) E ->
  forallb (fun q => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 q)) (sr_get tobs_sr (Z_to_bv 5 q)) &&
    sv_atoms_lt 32 (sr_get tobs_sr (Z_to_bv 5 q))) l = true ->
  forall q, In q l -> YK11.getr (ms_regs ms) (Z_to_bv 5 q) = YK11.getr regs1 (Z_to_bv 5 q).
Proof.
intros c regs1 Tc r E ss ms H l HS HR HA Hl q Hq.
rewrite forallb_forall in Hl. destruct (andb_prop _ _ (Hl q Hq)) as [Heq Hat].
apply sv_eqb_eq in Heq.
rewrite (st_ok_pi_restrict_reg H E ss ms (Z_to_bv 5 q) HS), Heq, (sv_denot_agree 32 _ _ _ HA Hat).
symmetry. exact (HR (Z_to_bv 5 q)).
Qed.
Lemma tk_reg_same : forall c regs1 Tc r E ss ms H (q : bv 5),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> regs_ok (tobs_env c regs1 Tc r) tobs_sr regs1 ->
  sr_get (ss_regs ss) q = sr_get tobs_sr q -> sv_atoms_lt 32 (sr_get tobs_sr q) = true ->
  YP06.env_agree 32 (tobs_env c regs1 Tc r) E -> YK11.getr (ms_regs ms) q = YK11.getr regs1 q.
Proof.
intros c regs1 Tc r E ss ms H q HS HR Hq Hat HA.
rewrite (st_ok_pi_restrict_reg H E ss ms q HS), Hq, (sv_denot_agree 32 _ _ _ HA Hat).
symmetry. exact (HR q).
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Lemma tk_b8 : forall c regs1 m1 md1 Tc r, tpre B c -> tobs_m B c regs1 m1 md1 Tc ->
  base_val (tobs_env c regs1 Tc r) (Some 8%nat) = tt c.
Proof.
intros c regs1 m1 md1 Tc r HP HM. pose proof (tp_t0 _ _ HP). pose proof (tp_t63 _ _ HP).
cbn [base_val]. rewrite (tobs_env_reg c regs1 Tc r 8 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM).
apply unsigned_lit_small. lia.
Qed.
Lemma tk_b19 : forall c regs1 Tc r, tpre B c -> 0 <= r < 8 -> YK11.getr regs1 19 = w64 (tt c + 48 * r) ->
  base_val (tobs_env c regs1 Tc r) (Some 19%nat) = tt c + 48 * r.
Proof.
intros c regs1 Tc r HP Hr H19. pose proof (tp_t0 _ _ HP). pose proof (tp_t63 _ _ HP).
cbn [base_val]. rewrite (tobs_env_reg c regs1 Tc r 19 19%bv eq_refl), H19.
apply unsigned_lit_small. lia.
Qed.
Lemma tk_awr : forall c E0 E rs r, tpre B c -> YP06.env_agree 64 E0 E -> skeleton rs = skeleton (tobs_regions true 0) ->
  base_val E0 (Some 8%nat) = tt c -> base_val E0 (Some 19%nat) = tt c + 48 * r -> 0 <= r < 8 ->
  awr_ok E rs (tSTK c) (tsp0 c) (tFP c) (ablocks B (tly c) (tS c)) (ablocks B (tlyc c) (tSc c)) (tlyc c) (town c).
Proof.
intros c E0 E rs r HP HA Hsk B8 B19 Hr a Ha.
assert (B8' : base_val E (Some 8%nat) = tt c) by (rewrite (base_val_agree 64 E0 E (Some 8%nat) HA eq_refl); exact B8).
assert (B19' : base_val E (Some 19%nat) = tt c + 48 * r) by (rewrite (base_val_agree 64 E0 E (Some 19%nat) HA eq_refl); exact B19).
exact (tobs_awr B c E true 0 r HP B8' (fun _ => conj B19' Hr) a (in_wrange_skeleton E rs (tobs_regions true 0) a Hsk Ha)).
Qed.
Lemma tk_exit : forall c regs1 m1 md1 Tc r ms md2 E ss cs Tc' L,
  tpre B c -> tobs_m B c regs1 m1 md1 Tc -> 0 <= r < 8 -> YK11.getr regs1 19 = w64 (tt c + 48 * r) ->
  st_ok_pi SEGS VAL E ss (restrict (w_H (tW c)) ms) ->
  YP06.env_agree 64 (tobs_env c regs1 Tc r) E ->
  frame_of (tobs_env c regs1 Tc r) (tobs_regions true 0) (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) (ms_mem ms)) ->
  mem_grows (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) (ms_mem ms)) ->
  ajournal SEGS B (tSTK c) (tsp0 c) (tFP c) (tly c) (tS c) (tW0 c) (tmem0 c) (tmd0 c) (town c)
    (tlyc c) (tSc c) (tW c) (ms_mem ms) md2 (tk c) ->
  nth_error (ss_mem ss) 1 = Some R_hdr ->
  nth_error (ss_mem ss) 2 = Some (YP09.mkRegion (Some 19%nat) 0 48 0 48 cs) ->
  covers_b cs 0 48 = true ->
  length Tc' = 400%nat ->
  (forall i, 0 <= i < 400 -> ~ (48 * r <= i < 48 * r + 48) -> nth_error Tc' (Z.to_nat i) = nth_error Tc (Z.to_nat i)) ->
  TM.ent Tc' r = L ->
  Forall (cagree E (tt c + 48 * r) 0 L) cs ->
  forallb (fun q => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 q)) (sr_get tobs_sr (Z_to_bv 5 q)) &&
    sv_atoms_lt 32 (sr_get tobs_sr (Z_to_bv 5 q))) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 27] = true ->
  tobs_m B c (ms_regs ms) (ms_mem ms) md2 Tc' /\
  (forall q, In q [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 27] ->
     YK11.getr (ms_regs ms) (Z_to_bv 5 q) = YK11.getr regs1 (Z_to_bv 5 q)).
Proof.
intros c regs1 m1 md1 Tc r ms md2 E ss cs Tc' L HP HM Hr H19 HS HA HFR HMG HJ2 Hn1 Hn2 Hcov HL' Hout HL Hag Hsr.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63.
pose proof (tm_Tl _ _ _ _ _ _ HM) as HTl.
pose proof (tk_b8 c regs1 m1 md1 Tc r HP HM) as B8.
pose proof (tk_b19 c regs1 Tc r HP Hr H19) as B19.
assert (B8' : base_val E (Some 8%nat) = tt c) by (rewrite (base_val_agree 64 _ E (Some 8%nat) HA eq_refl); exact B8).
assert (B19' : base_val E (Some 19%nat) = tt c + 48 * r) by (rewrite (base_val_agree 64 _ E (Some 19%nat) HA eq_refl); exact B19).
assert (Hed0 : ed E 0 = Tc) by (destruct HA as [_ HD]; rewrite HD; reflexivity).
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS Hn1) as Hreg1. cbn [ms_mem restrict] in Hreg1.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS Hn2) as Hreg2. cbn [ms_mem restrict] in Hreg2.
pose proof (tobs_regs_ok c regs1 Tc r (tm_s0 _ _ _ _ _ _ HM) (tm_s5 _ _ _ _ _ _ HM) (tm_s6 _ _ _ _ _ _ HM)
  (tm_s8 _ _ _ _ _ _ HM) ltac:(lia) ltac:(lia)) as HR0.
assert (HA32 : YP06.env_agree 32 (tobs_env c regs1 Tc r) E)
  by (destruct HA as [HA1 HA2]; split; [intros n Hn; apply HA1; lia | exact HA2]).
pose proof (tk_regs_kept c regs1 Tc r E ss ms _ _ HS HR0 HA32 Hsr) as HRK.
split; [|exact HRK].
apply (tobs_exit_run B LAWS c regs1 m1 md1 Tc (tobs_env c regs1 Tc r) true 0 r (ms_regs ms) (ms_mem ms) md2 Tc'
  HP HM B8 (fun _ => conj B19 Hr) HFR HMG HJ2 HL').
- intros i Hi _ He. exact (Hout i Hi (He eq_refl)).
- intros i Hi. unfold R_hdr in Hreg1.
  rewrite (region_bytes E _ 8 384 400 384 400 _ (tt c) (DTC.sub Tc 384 16) Hreg1 B8' ltac:(vm_compute; reflexivity)) by
    (first [ lia
           | apply Forall_cons; [|apply Forall_nil]; apply cagree_cdata; [lia|]; intros k Hk; rewrite Hed0;
             rewrite nth_error_sub by lia; f_equal; lia ]).
  rewrite nth_error_sub by lia. rewrite (Hout i ltac:(lia) ltac:(lia)). f_equal. lia.
- intros _ i Hi. replace (tt c + i) with (tt c + 48 * r + (i - 48 * r)) by lia.
  rewrite (region_bytes E _ 19 0 48 0 48 cs (tt c + 48 * r) L Hreg2 B19' Hcov Hag (i - 48 * r)) by lia.
  rewrite <- HL. replace (Z.to_nat (i - 48 * r - 0)) with (Z.to_nat (i - 48 * r)) by (f_equal; lia).
  rewrite TM.ent_nth by lia. f_equal. lia.
- intros q Hq. apply HRK. cbn in Hq |- *. tauto.
Qed.
Ltac tk_chain FR MG HJ :=
  match goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    tryif constr_eq HFr FR then fail else
  match goal with HG : mem_grows _ _ |- _ =>
    tryif constr_eq HG MG then fail else
  let FR' := fresh "FR'" in let MG' := fresh "MG'" in
  pose proof (tk_frame_step 64 _ _ _ _ _ _ _ FR HFr) as FR';
  specialize (FR' ltac:(tk_agree) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
  pose proof (mem_grows_trans _ _ _ MG HG) as MG';
  clear FR MG HFr HG; rename FR' into FR; rename MG' into MG
  end end;
  repeat match goal with H : frame_of _ _ (ms_mem _) (ms_mem _) |- _ => clear H end;
  repeat rewrite wvb_collapse in HJ.
Ltac tk_run0 c regs1 r HP B8 B19 Hr HS HJ SHOK FR MG :=
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x51b4;
  [ apply (tk_awr c (tobs_env c regs1 (tT c) r) _ _ r HP); [tk_agree | vm_compute; reflexivity | exact B8 | exact B19 | exact Hr]
  | tk_chain FR MG HJ ].
Ltac tk_split HS SHOK := psrr_branch_tok RUN BR HS SHOK TBspan.
Ltac tk_cv0 Hc c r HTl HGl Hr :=
  rewrite ?(tk_sx_G (tG c)) in Hc by first [reflexivity | exact HGl];
  rewrite ?(tk_sx_e (tT c) r) in Hc by first [reflexivity | exact HTl | exact Hr];
  cbn [sv_denot branch_taken] in Hc;
  rewrite ?RDO.eqb_s32, ?RDO.eqb_s32_c in Hc by lia;
  rewrite ?negb_true_iff, ?negb_false_iff in Hc.
Ltac tk_cg0 c regs1 r HM Ef :=
  first
  [ apply cagree_cdata; [lia|]; intros ? ?;
    change (ed Ef 2) with (TM.ent (tT c) r); tk_nth; tk_close
  | let ii := fresh "ii" in let Hii := fresh "Hii" in
    intros ii Hii; cbn [YP09.cbyte YP09.c_val YP09.c_off YP09.c_len YP09.cv_len Z.of_N] in Hii |- *;
    rewrite (tk_atom_denot c regs1 (tT c) r Ef 20 20%bv (tnow c) ltac:(tk_agree) ltac:(lia) eq_refl (tm_s4 _ _ _ _ _ _ HM));
    rewrite tk_byte_le8 by lia; tk_nth; tk_close
  | let ii := fresh "ii" in let Hii := fresh "Hii" in
    intros ii Hii; cbn [YP09.cbyte YP09.c_val YP09.c_off YP09.c_len YP09.cv_len Z.of_N] in Hii |- *;
    cbn [sv_denot]; rewrite (byte_of_word_low32 true) by lia;
    rewrite tk_byte_data by (first [lia | simpl; lia | change (ed Ef 1) with (tG c); simpl; lia]);
    change (ed Ef 1) with (tG c); tk_nth; rewrite nth_error_sub by lia; tk_close ].
Ltac tk_fin0 c regs1 m1 md1 r HK HP HM Hf H18 H19 HTl HGl Hr LB Hout L b HcR HS HJ FR MG :=
  let HL := fresh "HL" in
  assert (HL : TM.ent (RDO.kB (tT c) (tG c) (tnow c) r) r = L)
    by (rewrite (TM.ent_kB _ _ _ _ HTl HGl Hr), HcR, (TM.ent_kA _ _ _ HTl Hr); reflexivity);
  lazymatch type of HS with st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msf) =>
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdf) _ =>
  let rg := eval vm_compute in (nth_error (ss_mem ssf) 2) in
  lazymatch rg with Some (YP09.mkRegion _ _ _ _ _ ?cs) =>
  let HCG := fresh "HCG" in let HM2 := fresh "HM2" in let HRK := fresh "HRK" in
  assert (HCG : Forall (cagree Ef (tt c + 48 * r) 0 L) cs)
    by (repeat apply Forall_cons; try apply Forall_nil; tk_cg0 c regs1 r HM Ef);
  destruct (tk_exit c regs1 m1 md1 (tT c) r msf mdf Ef ssf cs (RDO.kB (tT c) (tG c) (tnow c) r) L HP HM Hr H19 HS
    ltac:(tk_agree) FR MG HJ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    LB Hout HL HCG ltac:(vm_compute; reflexivity)) as [HM2 HRK];
  pmkst HS;
  apply (HK _ _ _ r HP HM2);
  [ etransitivity; [exact (HRK 18 ltac:(cbn; tauto)) | exact H18]
  | etransitivity; [exact (HRK 19 ltac:(cbn; tauto)) | exact H19]
  | rewrite (tk_reg_lit _ _ _ _ 12 (Z.b2z b) HS ltac:(vm_compute; reflexivity)); unfold tf1; rewrite HcR; reflexivity
  | exact Hf ]
  end end end.
Lemma seg_found : forall c, SegK1 B c -> SegFound B c.
Proof.
intros c HK regs1 m1 md1 r HP HM H18 H19 Hf.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63.
pose proof (tp_T1 _ _ HP) as HT1. unfold DTC.tbl_T1 in HT1.
pose proof (tp_Tl _ _ HP) as HTl. pose proof (tp_Gl _ _ HP) as HGl.
pose proof (tp_now _ _ HP) as Hnow.
assert (Hr : 0 <= r < 8) by (destruct Hf as (Hr & _); lia).
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
pose proof (tk_b8 c regs1 m1 md1 (tT c) r HP HM) as B8.
pose proof (tk_b19 c regs1 (tT c) r HP Hr H19) as B19.
pose proof (tobs_env_img c regs1 (tT c) r) as HEI.
destruct (TM.stage_len (tT c) (tG c) (tow c) (tnow c) r HTl HGl Hr) as (LA & LB & _).
assert (Hout : forall i, 0 <= i < 400 -> ~ (48 * r <= i < 48 * r + 48) ->
  nth_error (RDO.kB (tT c) (tG c) (tnow c) r) (Z.to_nat i) = nth_error (tT c) (Z.to_nat i))
  by (intros i Hi He; exact (proj1 (proj2 (TM.stage_out (tT c) (tG c) (tow c) (tnow c) r i HTl HGl Hr Hi He)))).
destruct (tobs_enter B c regs1 m1 md1 (tT c) 0x514c true r 0 HP HM ltac:(left; reflexivity)
  ltac:(rewrite H18; f_equal; lia) ltac:(intros _; split; [exact Hr | exact H19])) as [HS SHOK].
unfold cfgB.
paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x51b4.
{ exact (tobs_awr B c _ true 0 r HP B8 ltac:(intros _; split; [exact B19 | exact Hr])). }
rename HFr into FR. rename HG into MG. clear HF.
tk_split HS SHOK.
- tk_cv0 Hc c r HTl HGl Hr.
  assert (HcR : RDO.cR (tT c) (tG c) r = false) by (unfold RDO.cR, DTC.s_role, DTC.role_of_e; rewrite Hc; reflexivity).
  tk_run0 c regs1 r HP B8 B19 Hr HS HJ SHOK FR MG.
  tk_fin0 c regs1 m1 md1 r HK HP HM Hf H18 H19 HTl HGl Hr LB Hout
    (DTC.upd (TM.ent (tT c) r) 40 (Z_to_le_bytes 8 (tnow c))) false HcR HS HJ FR MG.
- tk_cv0 Hc c r HTl HGl Hr. rename Hc into HcA.
  tk_run0 c regs1 r HP B8 B19 Hr HS HJ SHOK FR MG.
  tk_split HS SHOK.
  + tk_cv0 Hc c r HTl HGl Hr.
    assert (HcR : RDO.cR (tT c) (tG c) r = false)
      by (unfold RDO.cR, DTC.s_role, DTC.role_of_e; rewrite HcA, Hc; reflexivity).
    tk_run0 c regs1 r HP B8 B19 Hr HS HJ SHOK FR MG.
    tk_fin0 c regs1 m1 md1 r HK HP HM Hf H18 H19 HTl HGl Hr LB Hout
      (DTC.upd (TM.ent (tT c) r) 40 (Z_to_le_bytes 8 (tnow c))) false HcR HS HJ FR MG.
  + tk_cv0 Hc c r HTl HGl Hr. rename Hc into HcB.
    tk_run0 c regs1 r HP B8 B19 Hr HS HJ SHOK FR MG.
    tk_split HS SHOK.
    * tk_cv0 Hc c r HTl HGl Hr.
      assert (HcR : RDO.cR (tT c) (tG c) r = true)
        by (unfold RDO.cR, DTC.s_role, DTC.role_of_e; rewrite HcA, HcB, Hc, andb_false_r; reflexivity).
      tk_run0 c regs1 r HP B8 B19 Hr HS HJ SHOK FR MG.
      tk_fin0 c regs1 m1 md1 r HK HP HM Hf H18 H19 HTl HGl Hr LB Hout
        (DTC.upd (DTC.upd (TM.ent (tT c) r) 40 (Z_to_le_bytes 8 (tnow c))) 8 (DTC.sub (tG c) 8 4)) true HcR HS HJ FR MG.
    * tk_cv0 Hc c r HTl HGl Hr. rename Hc into HcC.
      tk_run0 c regs1 r HP B8 B19 Hr HS HJ SHOK FR MG.
      tk_split HS SHOK.
      -- tk_cv0 Hc c r HTl HGl Hr.
         assert (HcR : RDO.cR (tT c) (tG c) r = true)
           by (unfold RDO.cR, DTC.s_role, DTC.role_of_e; rewrite HcA, HcB, HcC, Hc; reflexivity).
         tk_run0 c regs1 r HP B8 B19 Hr HS HJ SHOK FR MG.
         tk_fin0 c regs1 m1 md1 r HK HP HM Hf H18 H19 HTl HGl Hr LB Hout
           (DTC.upd (DTC.upd (TM.ent (tT c) r) 40 (Z_to_le_bytes 8 (tnow c))) 8 (DTC.sub (tG c) 8 4)) true HcR HS HJ FR MG.
      -- tk_cv0 Hc c r HTl HGl Hr.
         assert (HcR : RDO.cR (tT c) (tG c) r = false)
           by (unfold RDO.cR, DTC.s_role, DTC.role_of_e; rewrite HcA, HcB, HcC, Hc; reflexivity).
         tk_run0 c regs1 r HP B8 B19 Hr HS HJ SHOK FR MG.
         tk_fin0 c regs1 m1 md1 r HK HP HM Hf H18 H19 HTl HGl Hr LB Hout
           (DTC.upd (TM.ent (tT c) r) 40 (Z_to_le_bytes 8 (tnow c))) false HcR HS HJ FR MG.
Qed.
End h.
End f.
End d.
