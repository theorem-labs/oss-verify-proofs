(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 409 of its 446 lines of code are new or changed and 32 lines of the source are left out. *)
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
Module DTC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table_c.
Module RDOC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe_c.
Module RDO := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe.
Module TM := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog.ReacDiscoTableObserve_M.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma dw1_eq : forall E d i, data_word E d i 1 = DTC.u_at (ed E d) i 1.
Proof. intros E d i. unfold data_word, DTC.u_at, DTC.sub. reflexivity. Qed.
Lemma u_at1_range : forall L k, 0 <= DTC.u_at L k 1 < 256.
Proof.
intros L k. pose proof (RDO.u_at_range L k 1) as Hq.
replace (2 ^ (8 * Z.of_nat 1)) with 256 in Hq by reflexivity. exact Hq.
Qed.
Lemma U_data1 : forall E d i, U E (SData d i 1) = DTC.u_at (ed E d) i 1.
Proof.
intros E d i. unfold U. cbn [sv_denot]. rewrite dw1_eq.
pose proof (u_at1_range (ed E d) i) as Hq. apply unsigned_lit_small. lia.
Qed.
Lemma sub1_nth : forall (L : list byte) k, 0 <= k -> k + 1 <= Z.of_nat (length L) ->
  nth_error (DTC.sub L k 1) 0 = Some (Z_to_bv 8 (DTC.u_at L k 1)).
Proof.
intros L k Hk Hl.
assert (Hlen : length (DTC.sub L k 1) = 1%nat) by (apply length_sub_le; [lia | cbn; lia]).
unfold DTC.u_at.
destruct (DTC.sub L k 1) as [|b tl] eqn:Hs; [discriminate|].
destruct tl as [|b2 tl2]; [|cbn in Hlen; lia].
cbn [nth_error]. f_equal. rewrite bytes_le_single. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma byte_of_word_0 : forall z, 0 <= z < 2 ^ 64 -> byte_of_word (Z_to_bv 64 z) 0 = Z_to_bv 8 z.
Proof.
intros z Hz. unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r, unsigned_lit_small by lia. reflexivity.
Qed.
Lemma ed_at_agree : forall (E E' : env) d (L : list byte), env_agree 64 E E' -> ed E d = L -> ed E' d = L.
Proof. intros E E' d L HA H. rewrite <- H. exact (f_equal (fun f => f d) (proj2 HA)). Qed.
Lemma bv_at_agree : forall (E E' : env) n v, env_agree 64 E E' -> obase_lt 64 (Some n) = true ->
  base_val E (Some n) = v -> base_val E' (Some n) = v.
Proof. intros E E' n v HA Hn H. rewrite (base_val_agree 64 E E' (Some n) HA Hn). exact H. Qed.
Ltac tobs_ag := split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity].
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma k2_reg_same_pi : forall c regs1 Tc r E' ss ms H (q : bv 5),
  st_ok_pi SEGS VAL E' ss (restrict H ms) -> regs_ok (tobs_env c regs1 Tc r) tobs_sr regs1 ->
  sr_get (ss_regs ss) q = sr_get tobs_sr q -> sv_atoms_lt 32 (sr_get tobs_sr q) = true ->
  env_agree 32 (tobs_env c regs1 Tc r) E' ->
  YK11.getr (ms_regs ms) q = YK11.getr regs1 q.
Proof.
intros c regs1 Tc r E' ss ms H q HS HR Hq Hat HA.
rewrite (st_ok_pi_restrict_reg H E' ss ms q HS), Hq, (sv_denot_agree 32 _ _ _ HA Hat).
symmetry. exact (HR q).
Qed.
Lemma tobs_ent_bytes_id : forall c Tc r E' m2,
  0 <= r < 8 -> length Tc = 400%nat ->
  YP09.region_ok SEGS E' m2 R_ent -> base_val E' (Some 19%nat) = tt c + 48 * r ->
  ed E' 2 = TM.ent Tc r ->
  forall i, 48 * r <= i < 48 * r + 48 -> mbyte SEGS m2 (tt c + i) = nth_error Tc (Z.to_nat i).
Proof.
intros c Tc r E' m2 Hr HTl Hreg B19' Hed i Hi.
replace (tt c + i) with (tt c + 48 * r + (i - 48 * r)) by lia.
unfold R_ent in Hreg.
rewrite (region_bytes E' m2 19 0 48 0 48 _ (tt c + 48 * r) (TM.ent Tc r) Hreg B19'
  ltac:(vm_compute; reflexivity)) by
  (first [ lia
         | apply Forall_cons; [|apply Forall_nil]; apply cagree_cdata; [lia|];
           intros k Hk; rewrite Hed; cbn [YP09.c_off]; unfold TM.ent; f_equal; lia ]).
rewrite (TM.ent_nth Tc r (i - 48 * r - 0) HTl Hr ltac:(lia)). f_equal. lia.
Qed.
Lemma tobs_ent_bytes_st : forall c Tc Tc' r E' m2 (v : sv) k,
  0 <= r < 8 -> length Tc = 400%nat -> length Tc' = 400%nat -> k = 15 \/ k = 16 ->
  YP09.region_ok SEGS E' m2 (YP09.mkRegion (Some 19%nat) 0 48 0 48
     [YP09.mkChunk k (CVal 1 v); YP09.mkChunk 0 (CData 2 0 k);
      YP09.mkChunk (k + 1) (CData 2 (k + 1) (47 - k))]) ->
  base_val E' (Some 19%nat) = tt c + 48 * r ->
  ed E' 2 = TM.ent Tc r -> length (tG c) = 24%nat ->
  sv_denot E' v = Z_to_bv 64 (DTC.u_at (tG c) k 1) ->
  TM.ent Tc' r = DTC.upd (TM.ent Tc r) k (DTC.sub (tG c) k 1) ->
  forall i, 48 * r <= i < 48 * r + 48 -> mbyte SEGS m2 (tt c + i) = nth_error Tc' (Z.to_nat i).
Proof.
intros c Tc Tc' r E' m2 v k Hr HTl HTl' Hk Hreg B19' Hed HGl Hsv HentD i Hi.
assert (HLsub : length (DTC.sub (tG c) k 1) = 1%nat) by (apply length_sub_le; [lia | cbn; lia]).
assert (HLent : length (TM.ent Tc r) = 48%nat) by (apply TM.ent_len; [exact HTl | exact Hr]).
assert (HAg : Forall (cagree E' (tt c + 48 * r) 0 (TM.ent Tc' r))
  [YP09.mkChunk k (CVal 1 v); YP09.mkChunk 0 (CData 2 0 k);
   YP09.mkChunk (k + 1) (CData 2 (k + 1) (47 - k))]).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - intros j Hj. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len] in Hj |- *.
    assert (Hj0 : j = 0) by lia. subst j.
    cbn [YP09.cbyte]. rewrite Hsv, byte_of_word_0 by (pose proof (u_at1_range (tG c) k); lia).
    rewrite HentD.
    lazymatch goal with |- _ = nth_error _ (Z.to_nat ?e) =>
      replace (Z.to_nat e) with (Z.to_nat k) by (f_equal; lia) end.
    rewrite (TM.upd_nth_in (TM.ent Tc r) (DTC.sub (tG c) k 1) k k
      ltac:(lia) ltac:(rewrite HLsub, HLent; cbn; lia) ltac:(rewrite HLsub; cbn; lia)).
    replace (Z.to_nat (k - k)) with 0%nat by (f_equal; lia).
    rewrite (sub1_nth (tG c) k ltac:(lia) ltac:(rewrite HGl; cbn; lia)). reflexivity.
  - apply cagree_cdata; [lia|]. intros j Hj. rewrite Hed, HentD.
    lazymatch goal with |- _ = nth_error _ (Z.to_nat ?e) =>
      rewrite (TM.upd_nth_out (TM.ent Tc r) (DTC.sub (tG c) k 1) k e
        ltac:(lia) ltac:(rewrite HLsub, HLent; cbn; lia) ltac:(lia) ltac:(rewrite HLsub; cbn; lia)) end.
    f_equal. lia.
  - apply cagree_cdata; [lia|]. intros j Hj. rewrite Hed, HentD.
    lazymatch goal with |- _ = nth_error _ (Z.to_nat ?e) =>
      rewrite (TM.upd_nth_out (TM.ent Tc r) (DTC.sub (tG c) k 1) k e
        ltac:(lia) ltac:(rewrite HLsub, HLent; cbn; lia) ltac:(lia) ltac:(rewrite HLsub; cbn; lia)) end.
    f_equal. lia. }
replace (tt c + i) with (tt c + 48 * r + (i - 48 * r)) by lia.
rewrite (region_bytes E' m2 19 0 48 0 48 _ (tt c + 48 * r) (TM.ent Tc' r) Hreg B19'
  ltac:(destruct Hk as [-> | ->]; vm_compute; reflexivity) HAg) by lia.
rewrite (TM.ent_nth Tc' r (i - 48 * r - 0) HTl' Hr ltac:(lia)). f_equal. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Ltac tobs_regq HS HR0 :=
  eapply (k2_reg_same_pi _ _ _ _ _ _ _ _ _ HS HR0);
  [ vm_compute; reflexivity | vm_compute; reflexivity | tobs_ag ].
Lemma tobs_awr_ent : forall c regs1 Tc r E',
  env_agree 64 (tobs_env c regs1 Tc r) E' -> tpre B c ->
  base_val (tobs_env c regs1 Tc r) (Some 8%nat) = tt c ->
  base_val (tobs_env c regs1 Tc r) (Some 19%nat) = tt c + 48 * r -> 0 <= r < 8 ->
  awr_ok E' (tobs_regions true 0) (tSTK c) (tsp0 c) (tFP c) (ablocks B (tly c) (tS c))
    (ablocks B (tlyc c) (tSc c)) (tlyc c) (town c).
Proof.
intros c regs1 Tc r E' HA HP B8 B19 Hr.
apply (tobs_awr B c E' true 0 r HP).
- rewrite (base_val_agree 64 _ E' (Some 8%nat) HA eq_refl). exact B8.
- intros _. split; [|exact Hr]. rewrite (base_val_agree 64 _ E' (Some 19%nat) HA eq_refl). exact B19.
Qed.
Lemma tobs_exit_ent : forall c regs1 m1 md1 Tc E' m2 md2 regs2 Tc' r,
  tpre B c -> tobs_m B c regs1 m1 md1 Tc -> 0 <= r < 8 ->
  YK11.getr regs1 19 = w64 (tt c + 48 * r) ->
  frame_of (tobs_env c regs1 Tc r) (tobs_regions true 0)
    (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) m2) ->
  mem_grows (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) m2) ->
  ajournal SEGS B (tSTK c) (tsp0 c) (tFP c) (tly c) (tS c) (tW0 c) (tmem0 c) (tmd0 c) (town c)
    (tlyc c) (tSc c) (tW c) m2 md2 (tk c) ->
  YP09.region_ok SEGS E' (mrestrict (w_H (tW c)) m2) R_hdr ->
  base_val E' (Some 8%nat) = tt c -> ed E' 0 = Tc ->
  length Tc' = 400%nat ->
  (forall i, 0 <= i < 400 -> ~ (48 * r <= i < 48 * r + 48) ->
     nth_error Tc' (Z.to_nat i) = nth_error Tc (Z.to_nat i)) ->
  (forall i, 48 * r <= i < 48 * r + 48 ->
     mbyte SEGS (mrestrict (w_H (tW c)) m2) (tt c + i) = nth_error Tc' (Z.to_nat i)) ->
  (forall q : Z, In q [2; 3; 4; 8; 9; 20; 21; 22; 24; 27] ->
     YK11.getr regs2 (Z_to_bv 5 q) = YK11.getr regs1 (Z_to_bv 5 q)) ->
  tobs_m B c regs2 m2 md2 Tc'.
Proof.
intros c regs1 m1 md1 Tc E' m2 md2 regs2 Tc' r HP HM Hr H19 HF HG HJ2 Hreg B8' Hed HL' Hout Hent Hregs.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63.
assert (B8 : base_val (tobs_env c regs1 Tc r) (Some 8%nat) = tt c).
{ cbn [base_val]. rewrite (tobs_env_reg c regs1 Tc r 8 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM).
  apply unsigned_lit_small. lia. }
assert (B19 : base_val (tobs_env c regs1 Tc r) (Some 19%nat) = tt c + 48 * r).
{ cbn [base_val]. rewrite (tobs_env_reg c regs1 Tc r 19 19%bv eq_refl), H19.
  unfold w64. apply unsigned_lit_small. lia. }
apply (tobs_exit_run B LAWS c regs1 m1 md1 Tc (tobs_env c regs1 Tc r) true 0 r regs2 m2 md2 Tc' HP HM B8
  ltac:(intros _; split; [exact B19 | exact Hr]) HF HG HJ2 HL').
- intros i Hi Hh He. apply Hout; [lia | exact (He eq_refl)].
- intros i Hi. rewrite (Hout i ltac:(lia) ltac:(lia)).
  unfold R_hdr in Hreg.
  rewrite (region_bytes E' _ 8 384 400 384 400 _ (tt c) (DTC.sub Tc 384 16) Hreg B8'
    ltac:(vm_compute; reflexivity)) by
    (first [ lia
           | apply Forall_cons; [|apply Forall_nil]; apply cagree_cdata; [lia|]; intros k Hk; rewrite Hed;
             rewrite nth_error_sub by lia; f_equal; lia ]).
  rewrite nth_error_sub by lia. f_equal. lia.
- intros _ i Hi. exact (Hent i Hi).
- exact Hregs.
Qed.
Lemma seg_K2 : forall c, SegK3 B c -> SegK2 B c.
Proof.
intros c HK regs1 m1 md1 r HP HM H18 H19 H12 HFnd.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63.
pose proof (tp_s0 _ _ HP) as Hs0. pose proof (tp_s63 _ _ HP) as Hs63.
pose proof (tp_Tl _ _ HP) as HTl. pose proof (tp_Gl _ _ HP) as HGl.
pose proof (tp_T1 _ _ HP) as HT1. unfold DTC.tbl_T1 in HT1.
pose proof (proj1 HFnd) as Hrn.
assert (Hr : 0 <= r < 8) by lia.
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
destruct (TM.stage_len (tT c) (tG c) (tow c) (tnow c) r HTl HGl Hr) as (_ & _ & HLC & HLD & _).
pose proof (tobs_env_img c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) as HEI.
pose proof (tobs_regs_ok c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r
  (tm_s0 _ _ _ _ _ _ HM) (tm_s5 _ _ _ _ _ _ HM) (tm_s6 _ _ _ _ _ _ HM) (tm_s8 _ _ _ _ _ _ HM)
  ltac:(lia) ltac:(lia)) as HR0.
assert (B8 : base_val (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) (Some 8%nat) = tt c).
{ cbn [base_val].
  rewrite (tobs_env_reg c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r 8 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM).
  apply unsigned_lit_small. lia. }
assert (B19 : base_val (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) (Some 19%nat) = tt c + 48 * r).
{ cbn [base_val].
  rewrite (tobs_env_reg c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r 19 19%bv eq_refl), H19.
  unfold w64. apply unsigned_lit_small. lia. }
assert (HdG : ed (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) 1 = tG c) by reflexivity.
assert (HdE : ed (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) 2
              = TM.ent (RDO.kC (tT c) (tG c) (tnow c) r) r) by reflexivity.
assert (HdT : ed (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) 0
              = RDO.kC (tT c) (tG c) (tnow c) r) by reflexivity.
assert (Hslots : DTC.u_at (TM.ent (RDO.kC (tT c) (tG c) (tnow c) r) r) 16 1 = RDOC.slots_of (tT c) r).
{ rewrite (TM.u_at_ent (RDO.kC (tT c) (tG c) (tnow c) r) r 16 1 HLC Hr ltac:(lia) ltac:(cbn; lia)).
  destruct (TM.stage_reads (tT c) (tG c) (tow c) (tnow c) r HTl HGl Hr) as (_ & _ & _ & _ & SR & _).
  rewrite SR. reflexivity. }
destruct (tobs_enter B c regs1 m1 md1 (RDO.kC (tT c) (tG c) (tnow c) r) 0x52c8 true r 0 HP HM
  ltac:(left; reflexivity) ltac:(rewrite H18; f_equal; lia)
  ltac:(intros _; split; [exact Hr | exact H19])) as [HS SHOK].
unfold cfgB.
paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x5310.
{ lazymatch goal with |- awr_ok ?Ex _ _ _ _ _ _ _ _ =>
    apply (tobs_awr_ent c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r Ex);
      [ tobs_ag | exact HP | exact B8 | exact B19 | exact Hr ] end. }
lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
  assert (HFa : frame_of (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) (tobs_regions true 0)
    (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) (ms_mem msx))) by exact HFr;
  assert (HGa : mem_grows (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) (ms_mem msx))) by exact HG
end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK TBspan.
- (* the sighting's slots byte is zero: no update of the entry *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (HAb : env_agree 64 (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
  rewrite branch_eq_U, U_data1, (ed_at_agree _ _ 1 (tG c) HAb HdG) in Hc.
  rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  assert (HcS : RDO.cS (tT c) (tG c) r = false)
    by (unfold RDO.cS, DTC.s_slots; rewrite Hc; reflexivity).
  assert (HkDC : RDO.kD (tT c) (tG c) (tnow c) r = RDO.kC (tT c) (tG c) (tnow c) r)
    by (unfold RDO.kD; rewrite HcS; reflexivity).
  assert (Htf3 : tf3 c r = tf2 c r) by (unfold tf3; rewrite HcS; apply orb_false_r).
  clear HAb.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x5310.
  { lazymatch goal with |- awr_ok ?Ex _ _ _ _ _ _ _ _ =>
      apply (tobs_awr_ent c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r Ex);
        [ tobs_ag | exact HP | exact B8 | exact B19 | exact Hr ] end. }
  lazymatch type of HFr with frame_of ?Ex _ _ _ =>
    assert (HAr : env_agree 64 (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (HAs : env_agree 64 (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HregH. cbn [ms_mem restrict] in HregH.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as HregE. cbn [ms_mem restrict] in HregE.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := ?mdx |} _ =>
    assert (HM2 : tobs_m B c (ms_regs msx) (ms_mem msx) mdx (RDO.kC (tT c) (tG c) (tnow c) r))
  end.
  { eapply (tobs_exit_ent c regs1 m1 md1 (RDO.kC (tT c) (tG c) (tnow c) r) _ _ _ _
      (RDO.kC (tT c) (tG c) (tnow c) r) r HP HM Hr H19).
    - eapply (frame_of_trans _ (tobs_regions true 0) (tobs_regions true 0));
        [reflexivity | exact HFa |].
      eapply (frame_of_agree_skel 64 _ _ (tobs_regions true 0) (tobs_regions true 0));
        [ exact HAr | vm_compute; reflexivity | vm_compute; reflexivity | exact HFr ].
    - eapply mem_grows_trans; [exact HGa | exact HG].
    - exact HJ.
    - exact HregH.
    - exact (bv_at_agree _ _ 8%nat _ HAs eq_refl B8).
    - exact (ed_at_agree _ _ 0 _ HAs HdT).
    - exact HLC.
    - intros i Hi Hni. reflexivity.
    - apply (tobs_ent_bytes_id c (RDO.kC (tT c) (tG c) (tnow c) r) r _ _ Hr HLC HregE).
      + exact (bv_at_agree _ _ 19%nat _ HAs eq_refl B19).
      + exact (ed_at_agree _ _ 2 _ HAs HdE).
    - intros q Hq. cbn in Hq.
      repeat (destruct Hq as [<- | Hq]; [tobs_regq HS HR0 |]). destruct Hq. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
    assert (S18 : YK11.getr (ms_regs msx) 18 = w64 (ts c)) by (rewrite <- H18; tobs_regq HS HR0) end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
    assert (S19 : YK11.getr (ms_regs msx) 19 = w64 (tt c + 48 * r)) by (rewrite <- H19; tobs_regq HS HR0) end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
    assert (S12 : YK11.getr (ms_regs msx) 12 = w64 (Z.b2z (tf3 c r)))
      by (rewrite Htf3, <- H12; tobs_regq HS HR0) end.
  pmkst HS.
  exact (HK _ _ _ r HP ltac:(rewrite HkDC; exact HM2) S18 S19 S12 HFnd).
- (* the sighting's slots byte is non-zero *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (HAb : env_agree 64 (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
  rewrite branch_eq_U, U_data1, (ed_at_agree _ _ 1 (tG c) HAb HdG) in Hc.
  rewrite U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  clear HAb.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x5310.
  { lazymatch goal with |- awr_ok ?Ex _ _ _ _ _ _ _ _ =>
      apply (tobs_awr_ent c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r Ex);
        [ tobs_ag | exact HP | exact B8 | exact B19 | exact Hr ] end. }
  lazymatch type of HFr with frame_of ?Ex _ _ _ =>
    assert (HAr : env_agree 64 (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
    assert (HFb : frame_of (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) (tobs_regions true 0)
      (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) (ms_mem msx)));
    [ | assert (HGb : mem_grows (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) (ms_mem msx)))
          by (eapply mem_grows_trans; [exact HGa | exact HG]) ]
  end.
  { eapply (frame_of_trans _ (tobs_regions true 0) (tobs_regions true 0));
      [reflexivity | exact HFa |].
    eapply (frame_of_agree_skel 64 _ _ (tobs_regions true 0) (tobs_regions true 0));
      [ exact HAr | vm_compute; reflexivity | vm_compute; reflexivity | exact HFr ]. }
  clear HF HFr HG HFa HGa HAr.
  psrr_branch_tok RUN BR HS SHOK TBspan.
  + (* the entry's slots byte already agrees: no update *)
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (HAb : env_agree 64 (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
    rewrite branch_eq_U, !U_data1, (ed_at_agree _ _ 2 _ HAb HdE),
      (ed_at_agree _ _ 1 (tG c) HAb HdG), Hslots in Hc0.
    apply Z.eqb_eq in Hc0.
    assert (HcS : RDO.cS (tT c) (tG c) r = false)
      by (unfold RDO.cS, DTC.s_slots; rewrite Hc0, Z.eqb_refl; cbn [negb]; apply andb_false_r).
    assert (HkDC : RDO.kD (tT c) (tG c) (tnow c) r = RDO.kC (tT c) (tG c) (tnow c) r)
      by (unfold RDO.kD; rewrite HcS; reflexivity).
    assert (Htf3 : tf3 c r = tf2 c r) by (unfold tf3; rewrite HcS; apply orb_false_r).
    clear HAb.
    paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x5310.
    { lazymatch goal with |- awr_ok ?Ex _ _ _ _ _ _ _ _ =>
        apply (tobs_awr_ent c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r Ex);
          [ tobs_ag | exact HP | exact B8 | exact B19 | exact Hr ] end. }
    lazymatch type of HFr with frame_of ?Ex _ _ _ =>
      assert (HAr : env_agree 64 (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (HAs : env_agree 64 (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HregH. cbn [ms_mem restrict] in HregH.
    pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as HregE. cbn [ms_mem restrict] in HregE.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := ?mdx |} _ =>
      assert (HM2 : tobs_m B c (ms_regs msx) (ms_mem msx) mdx (RDO.kC (tT c) (tG c) (tnow c) r))
    end.
    { eapply (tobs_exit_ent c regs1 m1 md1 (RDO.kC (tT c) (tG c) (tnow c) r) _ _ _ _
        (RDO.kC (tT c) (tG c) (tnow c) r) r HP HM Hr H19).
      - eapply (frame_of_trans _ (tobs_regions true 0) (tobs_regions true 0));
          [reflexivity | exact HFb |].
        eapply (frame_of_agree_skel 64 _ _ (tobs_regions true 0) (tobs_regions true 0));
          [ exact HAr | vm_compute; reflexivity | vm_compute; reflexivity | exact HFr ].
      - eapply mem_grows_trans; [exact HGb | exact HG].
      - exact HJ.
      - exact HregH.
      - exact (bv_at_agree _ _ 8%nat _ HAs eq_refl B8).
      - exact (ed_at_agree _ _ 0 _ HAs HdT).
      - exact HLC.
      - intros i Hi Hni. reflexivity.
      - apply (tobs_ent_bytes_id c (RDO.kC (tT c) (tG c) (tnow c) r) r _ _ Hr HLC HregE).
        + exact (bv_at_agree _ _ 19%nat _ HAs eq_refl B19).
        + exact (ed_at_agree _ _ 2 _ HAs HdE).
      - intros q Hq. cbn in Hq.
        repeat (destruct Hq as [<- | Hq]; [tobs_regq HS HR0 |]). destruct Hq. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
      assert (S18 : YK11.getr (ms_regs msx) 18 = w64 (ts c)) by (rewrite <- H18; tobs_regq HS HR0) end.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
      assert (S19 : YK11.getr (ms_regs msx) 19 = w64 (tt c + 48 * r)) by (rewrite <- H19; tobs_regq HS HR0) end.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
      assert (S12 : YK11.getr (ms_regs msx) 12 = w64 (Z.b2z (tf3 c r)))
        by (rewrite Htf3, <- H12; tobs_regq HS HR0) end.
    pmkst HS.
    exact (HK _ _ _ r HP ltac:(rewrite HkDC; exact HM2) S18 S19 S12 HFnd).
  + (* the entry's slots byte differs: the store *)
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (HAb : env_agree 64 (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
    rewrite branch_eq_U, !U_data1, (ed_at_agree _ _ 2 _ HAb HdE),
      (ed_at_agree _ _ 1 (tG c) HAb HdG), Hslots in Hc0.
    apply Z.eqb_neq in Hc0.
    assert (HcS : RDO.cS (tT c) (tG c) r = true).
    { unfold RDO.cS, DTC.s_slots. apply andb_true_intro.
      split; apply negb_true_iff; apply Z.eqb_neq; [exact Hc | exact Hc0]. }
    assert (HentD : TM.ent (RDO.kD (tT c) (tG c) (tnow c) r) r
                    = DTC.upd (TM.ent (RDO.kC (tT c) (tG c) (tnow c) r) r) 16 (DTC.sub (tG c) 16 1))
      by (rewrite (TM.ent_kD (tT c) (tG c) (tnow c) r HTl HGl Hr), HcS; reflexivity).
    assert (Htf3 : tf3 c r = true) by (unfold tf3; rewrite HcS; apply orb_true_r).
    clear HAb.
    paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x5310.
    { lazymatch goal with |- awr_ok ?Ex _ _ _ _ _ _ _ _ =>
        apply (tobs_awr_ent c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r Ex);
          [ tobs_ag | exact HP | exact B8 | exact B19 | exact Hr ] end. }
    lazymatch type of HFr with frame_of ?Ex _ _ _ =>
      assert (HAr : env_agree 64 (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (HAs : env_agree 64 (tobs_env c regs1 (RDO.kC (tT c) (tG c) (tnow c) r) r) Ex) by tobs_ag end.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HregH. cbn [ms_mem restrict] in HregH.
    pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as HregE. cbn [ms_mem restrict] in HregE.
    prreg HS (12%bv : bv 5) Q12.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := ?mdx |} _ =>
      assert (HM2 : tobs_m B c (ms_regs msx) (ms_mem msx) mdx (RDO.kD (tT c) (tG c) (tnow c) r))
    end.
    { eapply (tobs_exit_ent c regs1 m1 md1 (RDO.kC (tT c) (tG c) (tnow c) r) _ _ _ _
        (RDO.kD (tT c) (tG c) (tnow c) r) r HP HM Hr H19).
      - eapply (frame_of_trans _ (tobs_regions true 0) (tobs_regions true 0));
          [reflexivity | exact HFb |].
        eapply (frame_of_agree_skel 64 _ _ (tobs_regions true 0) (tobs_regions true 0));
          [ exact HAr | vm_compute; reflexivity | vm_compute; reflexivity | exact HFr ].
      - eapply mem_grows_trans; [exact HGb | exact HG].
      - exact HJ.
      - exact HregH.
      - exact (bv_at_agree _ _ 8%nat _ HAs eq_refl B8).
      - exact (ed_at_agree _ _ 0 _ HAs HdT).
      - exact HLD.
      - intros i Hi Hni.
        destruct (TM.stage_out (tT c) (tG c) (tow c) (tnow c) r i HTl HGl Hr ltac:(lia) ltac:(lia))
          as (_ & _ & OC & OD & _).
        rewrite OD, OC. reflexivity.
      - apply (tobs_ent_bytes_st c (RDO.kC (tT c) (tG c) (tnow c) r) (RDO.kD (tT c) (tG c) (tnow c) r) r
          _ _ _ 16 Hr HLC HLD ltac:(right; reflexivity) HregE).
        + exact (bv_at_agree _ _ 19%nat _ HAs eq_refl B19).
        + exact (ed_at_agree _ _ 2 _ HAs HdE).
        + exact HGl.
        + cbn [sv_denot]. rewrite dw1_eq, (ed_at_agree _ _ 1 (tG c) HAs HdG). reflexivity.
        + exact HentD.
      - intros q Hq. cbn in Hq.
        repeat (destruct Hq as [<- | Hq]; [tobs_regq HS HR0 |]). destruct Hq. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
      assert (S18 : YK11.getr (ms_regs msx) 18 = w64 (ts c)) by (rewrite <- H18; tobs_regq HS HR0) end.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
      assert (S19 : YK11.getr (ms_regs msx) 19 = w64 (tt c + 48 * r)) by (rewrite <- H19; tobs_regq HS HR0) end.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ =>
      assert (S12 : YK11.getr (ms_regs msx) 12 = w64 (Z.b2z (tf3 c r)));
      [ rewrite Htf3; cbn [Z.b2z]; unfold w64; exact Q12 | ] end.
    pmkst HS.
    exact (HK _ _ _ r HP HM2 S18 S19 S12 HFnd).
Qed.
End h.
End f.
End d.
