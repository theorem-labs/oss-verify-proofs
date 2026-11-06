(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec SeqExec StoreOk ShapeAlg MallocDefs StreamSim.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec EnframeDefs TargetSpec TargetKDefs UbWorld UbTargetPre SumWalkTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan SymSlots SymPlanSoundA.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbATB UbTargetEntry_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require UbWseg.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
Local Abbreviation cs_ok := (SPSA.cs_ok RSEGS) (only parsing).
Local Abbreviation vm_ok := (SPSA.vm_ok RSEGS) (only parsing).
Local Abbreviation slots_ok := (SSL.slots_ok RSEGS) (only parsing).
Local Abbreviation slot_ok := (SSL.slot_ok RSEGS) (only parsing).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition vals_T (sp0 gm area tid : Z) (content : list byte) (brkv mas e c sv : Z) (R : bvmap 5 word) : list word :=
  [Z_to_bv 64 sp0; Z_to_bv 64 gm; Z_to_bv 64 area; Z_to_bv 64 tid;
   Z_to_bv 64 (hdr_paylen content); Z_to_bv 64 (hdr_cfglen content);
   Z_to_bv 64 (hdr_b0 content);
   Z_to_bv 64 (hdr_b1 content);
   Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0)));
   Z_to_bv 64 brkv; Z_to_bv 64 mas; Z_to_bv 64 e] ++ junk_vals R ++ [Z_to_bv 64 c; Z_to_bv 64 sv].

Definition E_T (sp0 gm area tid : Z) (content : list byte) (brkv mas e c sv : Z) (R : bvmap 5 word) : env :=
  Env (vals_ev (vals_T sp0 gm area tid content brkv mas e c sv R)) (blobs_ev [content]).

(* [comment removed for export] *)
Lemma ref_wseg_T : wseg_ok RSEGS (0x26000 : word) 204800%nat = true.
Proof. exact UbWseg.wseg_data_lit. Qed.

Lemma store_ok_data : forall m (a : word) n,
  (0x26000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x58000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
  intros m a n Hlo Hhi.
  apply UbWseg.store_ok_data_win; [exact Hlo | exact Hhi].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma vadd_ZZ' : forall x y, v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
  intros. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- Z.add_mod by (cbn; lia). reflexivity.
Qed.

Lemma v_addi_Z : forall x k, (0 <= x < 2 ^ 64)%Z -> v_addi (Z_to_bv 64 x) k = Z_to_bv 64 (x + k).
Proof. intros. unfold v_addi. rewrite u_small by lia. reflexivity. Qed.

Lemma flat_intro : forall E b k n,
  (0 <= bv_unsigned (edenot E b) + k)%Z -> (0 <= n)%Z ->
  (bv_unsigned (edenot E b) + k < 2 ^ 64)%Z ->
  (bv_unsigned (edenot E b) + k + n <= 2 ^ 64)%Z ->
  flat E (SA b k) n.
Proof. intros. unfold flat, estart. cbn [a_base a_off]. lia. Qed.

(* [comment removed for export] *)
Lemma rdn1_of_mem : forall M (a : word) (b : byte), M a = Some b -> rdn RSEGS M a 1 = Some [b].
Proof.
  intros M a b H. cbn [rdn]. rewrite H. reflexivity.
Qed.

Lemma w2b1 : forall z, (0 <= z < 256)%Z -> word_to_le_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z Hz. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal. rewrite u_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma store_ok_of_defined : forall M (a : Z) (n : Z),
  (forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) <> None) ->
  (0 <= a)%Z -> (a + n <= 2 ^ 64)%Z ->
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= n)%Z -> store_ok RSEGS M (Z_to_bv 64 (a + d)) m = true.
Proof.
  intros M a n Hdef Ha Hn d m Hd Hm. destruct m as [|m']; [reflexivity|].
  apply store_ok_of_all; [rewrite u_small by lia; lia|].
  intros x Hx. rewrite u_small in Hx by lia.
  replace x with (Z_to_bv 64 (a + (bv_unsigned x - a))) by (apply bv_eq; rewrite u_small by lia; lia).
  pose proof (Hdef (bv_unsigned x - a) ltac:(lia)) as Hm'.
  unfold wview. destruct (M (Z_to_bv 64 (a + (bv_unsigned x - a)))); [discriminate | contradiction].
Qed.

(* [comment removed for export] *)
Lemma rdn_defined_nth : forall M (a : Z) n bs,
  rdn RSEGS M (Z_to_bv 64 a) n = Some bs ->
  (forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) <> None) ->
  (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Proof.
  intros M a n bs Hr Hdef Ha Hn i Hi.
  pose proof (rdn_nth RSEGS M n (Z_to_bv 64 a) bs (Z.to_nat i) Hr ltac:(lia)) as B.
  rewrite w_add_nat, u_small in B by lia. rewrite Z2Nat.id in B by lia.
  cbn [rdn] in B.
  destruct (M (Z_to_bv 64 (a + i))) as [b|] eqn:Hm.
  - cbn in B. injection B as B'. rewrite B'. reflexivity.
  - exfalso. exact (Hdef i Hi Hm).
Qed.

(* [comment removed for export] *)
Lemma seps_conv : forall l, UbTargetPre.seps l -> SPSA.seps l.
Proof.
  intros l H. induction H; constructor; auto.
Qed.

Lemma live_bytes_bound : forall (l : list (word * word)) n b,
  (length l <= n)%nat ->
  Forall (fun p => (0 < bv_unsigned (snd p) <= b)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) l ->
  (0 <= b)%Z -> (live_bytes l <= Z.of_nat n * b)%Z.
Proof.
  intros l. induction l as [|[a sz] l IH]; intros n b Hlen HF Hb; cbn [live_bytes length] in *.
  - lia.
  - apply Forall_cons_iff in HF as [[H1 _] HF]. cbn [snd] in H1.
    destruct n as [|n]; [lia|]. specialize (IH n b ltac:(lia) HF Hb). lia.
Qed.

(* [comment removed for export] *)
Definition ivs_cover (lo hi : Z) : bool :=
  existsb (fun iv => (fst iv <=? lo) && (hi <=? snd iv))%bool img_clear_ivs.

Lemma img_clear_cover : forall M lo hi,
  Forall (fun iv => img_clear M (fst iv) (snd iv)) img_clear_ivs ->
  ivs_cover lo hi = true -> forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.
Proof.
  intros M lo hi HF Hc i Hi. unfold ivs_cover in Hc. apply existsb_exists in Hc as (iv & Hin & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply (proj1 (Forall_forall _ _) HF iv Hin). lia.
Qed.

Definition all_regs : list Prelude.reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Entry.
  Variables (sp0 gm area brkv mas tid : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte).
  Variables (VM : VmMaps) (model : Model) (nlo nhi : Z).
  Hypothesis TP : target_pre sp0 gm area brkv mas tid content R M.
  Hypothesis TV : target_vm sp0 gm area VM.
  Hypothesis Mfds : m_fds model = fds_std.
  Hypothesis Mvm : m_vmmaps model = VM.
  Hypothesis Mhalt : m_halted model = None.
  Hypothesis Mlazy : m_vm_lazy model = [].
  Hypothesis Mmat : m_vm_materialized model = [].
  Hypothesis Hn : nlo <= hdr_paylen content <= nhi.
  Variable e : Z.
  Hypothesis He : 0 <= e < 2 ^ 32.
  Hypothesis Ce : cell M 0x36bbc 4 e.
  Variable c : Z.
  Hypothesis Cc : cell M 0x56ca0 8 c.

  Variable sv : Z.
  Hypothesis Cs1 : cell M ctx_secret 8 sv.
  Hypothesis Cs2 : cell M area 8 sv.

  Let E : env := E_T sp0 gm area tid content brkv mas e c sv R.
  Let L : Z := Z.of_nat (length content).

  (* [comment removed for export] *)
  Lemma EV0 : ev E 0 = Z_to_bv 64 sp0. Proof. reflexivity. Qed.
  Lemma EV1 : ev E 1 = Z_to_bv 64 gm. Proof. reflexivity. Qed.
  Lemma EV2 : ev E 2 = Z_to_bv 64 area. Proof. reflexivity. Qed.
  Lemma EV3 : ev E 3 = Z_to_bv 64 tid. Proof. reflexivity. Qed.
  Lemma EV4 : ev E 4 = Z_to_bv 64 (hdr_paylen content). Proof. reflexivity. Qed.
  Lemma EV5 : ev E 5 = Z_to_bv 64 (hdr_cfglen content). Proof. reflexivity. Qed.
  Lemma EV6 : ev E 6 = Z_to_bv 64 (hdr_b0 content). Proof. reflexivity. Qed.
  Lemma EV7 : ev E 7 = Z_to_bv 64 (hdr_b1 content). Proof. reflexivity. Qed.
  Lemma EV8 : ev E 8 = Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0))). Proof. reflexivity. Qed.
  Lemma EV9 : ev E 9 = Z_to_bv 64 brkv. Proof. reflexivity. Qed.
  Lemma EV10 : ev E 10 = Z_to_bv 64 mas. Proof. reflexivity. Qed.
  Lemma EV11 : ev E 11 = Z_to_bv 64 e. Proof. reflexivity. Qed.
  Lemma EVJ : forall i, (i < 32)%N -> ev E (12 + i) = getr R (Z_to_bv 5 (Z.of_N i)).
  Proof.
    intros i Hi. unfold E, E_T. cbn [ev]. unfold vals_T, vals_ev.
    rewrite app_nth2 by (cbn [length]; lia).
    replace (N.to_nat (12 + i) - length [Z_to_bv 64 sp0; Z_to_bv 64 gm; Z_to_bv 64 area; Z_to_bv 64 tid;
       Z_to_bv 64 (hdr_paylen content); Z_to_bv 64 (hdr_cfglen content); Z_to_bv 64 (hdr_b0 content);
       Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0)));
       Z_to_bv 64 brkv; Z_to_bv 64 mas; Z_to_bv 64 e : word])%nat with (N.to_nat i) by (cbn [length]; lia).
    rewrite app_nth1 by (unfold junk_vals; rewrite length_map, length_seq; lia).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by lia.
    rewrite N_nat_Z. reflexivity.
  Qed.
  Lemma EV44 : ev E 44 = Z_to_bv 64 c. Proof. reflexivity. Qed.
  Lemma EV45 : ev E 45 = Z_to_bv 64 sv. Proof. reflexivity. Qed.
  Lemma EB0 : eb E 0 = content. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma b0_rng : 0 <= hdr_b0 content < 256. Proof. unfold hdr_b0. pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256%Z in Hr. lia. Qed.
  Lemma b1_rng : 0 <= hdr_b1 content < 256. Proof. unfold hdr_b1. pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256%Z in Hr. lia. Qed.
  Lemma b2_rng : 0 <= bv_unsigned (nth 2 content (Z_to_bv 8 0)) < 256. Proof. pose proof (bv_unsigned_in_range _ (nth 2 content (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256%Z in Hr. lia. Qed.
  Lemma cfglen_rng : 0 <= hdr_cfglen content < 32768.
  Proof. unfold hdr_cfglen. apply Z.mod_pos_bound. lia. Qed.

  (* [comment removed for export] *)
  Ltac enorm :=
    cbn [edenot a_base a_off];
    rewrite ?alu_add, ?EV0, ?EV1, ?EV2, ?EV3, ?EV4, ?EV5, ?EV6, ?EV7, ?EV8, ?EV9, ?EV10, ?EV11, ?EV44, ?EV45;
    rewrite ?vadd_ZZ'.
  Ltac anorm := unfold adenot, estart, elenZ; enorm; rewrite ?v_addi_Z by lia; rewrite ?u_small by lia.

  Ltac kimg Wimg := split; [lia|]; split; [lia|]; apply (img_clear_cover _ _ _ Wimg); vm_compute; reflexivity.
  Ltac karith := anorm; lia.
  Ltac kflat := apply flat_intro; unfold elenZ; enorm; rewrite ?u_small by lia; lia.
  Ltac kwr_stack Hst := split; [kflat|]; intros d m Hd Hm; unfold elenZ in Hm; cbn [edenot] in Hm; rewrite ?u_small in Hm by lia; anorm;
                    replace (sp0 + -8388608 + d) with (sp0 - 8388608 + d) by lia; apply Hst; lia.
  Ltac kwr_def Hdef := split; [kflat|]; intros d m Hd Hm; unfold elenZ in Hm; cbn [edenot] in Hm; rewrite ?u_small in Hm by lia; anorm; rewrite ?Z.add_0_r;
                    first [ apply (store_ok_of_defined _ _ _ Hdef); lia
                          | replace (area + 0 + d) with (area + d) by lia; apply (store_ok_of_defined _ _ _ Hdef); lia
                          | replace (gm + 0 + d) with (gm + d) by lia; apply (store_ok_of_defined _ _ _ Hdef); lia ].
  Ltac kwr_data := split; [kflat|]; intros d m Hd Hm; unfold elenZ in Hm; cbn [edenot] in Hm; rewrite ?u_small in Hm by lia; anorm; apply store_ok_data; rewrite u_small by lia; lia.
  Ltac kword_abs aexp C := split; [cbn; lia|]; split; [kflat|]; anorm;
                    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => change (Z_to_bv 64 a) with (Z_to_bv 64 aexp : word) end;
                    first [ exact C | unfold cell in C; rewrite C; reflexivity ].
  Ltac kword_rel aexp C := split; [cbn; lia|]; split; [kflat|]; anorm;
                    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with aexp by lia end;
                    first [ exact C | unfold cell in C; rewrite C; first [reflexivity | f_equal] ].
  Ltac kbyte_rel aexp C := split; [cbn; lia|]; split; [kflat|]; anorm;
                    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with aexp by lia end;
                    rewrite (rdn1_of_mem _ _ _ C); rewrite w2b1 by lia; reflexivity.
  Ltac kzero aexp C := split; [kflat|]; intros i Hi; revert i Hi; anorm; intros i Hi;
                    lazymatch goal with |- _ (Z_to_bv 64 ?a) = _ => replace a with (aexp + i) by lia end;
                    apply C; lia.
  Ltac kblob HTC Hdef := split; [kflat|]; split; [rewrite EB0; anorm; lia|];
                intros i Hi; revert i Hi; anorm; rewrite EB0; intros i Hi;
                lazymatch goal with |- _ (Z_to_bv 64 ?a) = _ => replace a with (gm + 32 + i) by lia end;
                apply (rdn_defined_nth _ (gm + 32) (length content) content HTC); try lia;
                intros j Hj; replace (gm + 32 + j) with (gm + (32 + j)) by lia; apply Hdef; lia.

  Theorem target_entry_ok_e :
    cs_ok E (cs_T nlo nhi) R M model.
  Proof.
    pose proof TP as TP'.
    destruct TP' as [tp_ra tp_sp tp_gp tp_tp tp_a0 tp_a1 tp_a2 tp_a3 tp_s0 tp_s1 tp_s2 tp_s3 tp_s4 tp_s5 tp_s6
                     tp_sp0 tp_len tp_stack TF TW TC].
    pose proof TW as TW'. destruct TW'.
    lazymatch goal with H : enframe_post _ _ _ _ _ _ |- _ => pose proof H as EP0; destruct H end.
    lazymatch goal with x := gm + 16 + 16 * 1 |- _ => subst x end.
    lazymatch goal with x := gm + 16 + 69616 - 4 |- _ => subst x end.
    lazymatch goal with x := 69616 - 4 - 65536 - 16 * 1 |- _ => subst x end.
    lazymatch goal with x := 69616 * 0 / 16 + 1 |- _ => subst x end.
    destruct TF as [mf_ra mf_s0 mf_s1 mf_s2 mf_s3 mf_s4 mf_s5 mf_s6 mf_s7].
    (* [comment removed for export] *)
    pose proof TV as TV'. destruct TV' as [_ _ _ _ _ _ _ Vsp' Vgmtop Vartop].
    assert (Hatop : alloc_top VM = sp0 - 8388608).
    { unfold alloc_top, stack_max_size. rewrite Vsp'. rewrite u_small by lia. reflexivity. }
    rewrite Hatop in Vgmtop, Vartop.
    pose proof b0_rng as Hb0. pose proof b1_rng as Hb1. pose proof b2_rng as Hb2. pose proof cfglen_rng as Hcl.
    assert (HL : hdr_paylen content + hdr_cfglen content + 6 = L) by (unfold hdr_paylen; subst L; lia).
    (* [comment removed for export] *)
    replace (gm + 16 + 16 * 1 - 4) with (gm + 28) in Pm4 by lia.
    replace (gm + 16 + 16 * 1 - 3) with (gm + 29) in Pm3 by lia.
    replace (gm + 16 + 16 * 1 - 2) with (gm + 30) in Pm2 by lia.
    replace (gm + 16 + 16 * 1 + 65536) with (gm + 65568) in Pzr by lia.
    replace (gm + 16 + 69616 - 4 - 5) with (gm + 69623) in Pe5 by lia.
    replace (gm + 16 + 69616 - 4 - 4) with (gm + 69624) in Pe4 by lia.
    replace (gm + 16 - 3) with (gm + 13) in Ps3 by lia.
    replace (gm + 16 - 2) with (gm + 14) in Ps2 by lia.
    change (69616 - 4 - 65536 - 16 * 1) with 4060 in Pm3, Pzr, Pe5, Pe4, Pr.
    change (69616 * 0 / 16 + 1) with 1 in Pm2, Pr.
    change (0 + 32 * res_code 4060) with 160 in Pm3.
    specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
    specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
    constructor.
    - (* [comment removed for export] *)
      intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
      { assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity. }
      pose proof (ridx_range r) as Hri. rewrite <- (ridx_roundtrip r) at 1.
      cbn [c_ss cs_T s_regs].
      generalize (ridx r) Hri. clear r Hr0 Hri. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
        [ .. | lia]; rewrite <- nth_all_regs by lia; cbn [nth sr_T all_regs];
        lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                  change (edenot E (EVar n)) with (ev E n);
                  first [ rewrite (EVJ (n - 12)) by lia; reflexivity
                        | rewrite ?EV4, ?EV5; first [exact tp_a1 | exact tp_a3 | exact tp_s2 | exact tp_s4 | idtac] ]
              | |- _ => idtac end;
        try (enorm; first [ reflexivity | exact tp_ra | exact tp_gp | exact tp_tp
                          | rewrite tp_sp; f_equal; lia
                          | rewrite tp_a0; f_equal; lia | rewrite tp_s1; f_equal; lia
                          | rewrite tp_s0; f_equal; lia | rewrite tp_s3; f_equal; lia
                          | rewrite tp_s6; f_equal; lia
                          | rewrite tp_a2; f_equal; lia ]).
      (* [comment removed for export] *)
      rewrite tp_s5. cbn [edenot]. rewrite EV7. unfold ext_val, ext_Z. rewrite u_small by lia.
      change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.div_1_r, (Z.mod_small _ 256) by lia.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold bv_swrap, bv_wrap.
      change (bv_half_modulus (8 * N.of_nat 1)) with 128. change (bv_modulus (8 * N.of_nat 1)) with 256.
      destruct (Z.ltb_spec0 (hdr_b1 content) 128).
      + rewrite (Z.mod_small (_ + 128) 256) by lia. f_equal. lia.
      + replace ((hdr_b1 content + 128) mod 256) with (hdr_b1 content + 128 - 256) by
          (apply Z.mod_unique with (q := 1); lia).
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        apply Z.mod_unique with (q := -1); [lia|]. rewrite Z.mod_small by lia. lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - (* [comment removed for export] *)
      cbn [c_ss cs_T s_know]. unfold kn_T, kn_T0, know_ok.
      repeat (apply Forall_cons; [|try apply Forall_nil]).
      all: cbn [kentry_ok].
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *)
        anorm. pose proof (Z.le_min_l 32767 (65529 - nlo)). pose proof (Z.le_min_r 32767 (65529 - nlo)).
        pose proof (Z.min_spec 32767 (65529 - nlo)). lia.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) kwr_stack tp_stack.
      + (* [comment removed for export] *) kword_rel (sp0 - 56) mf_ra.
      + (* [comment removed for export] *) kword_rel (sp0 - 64) mf_s0.
      + (* [comment removed for export] *) kword_rel (sp0 - 72) mf_s1.
      + (* [comment removed for export] *) kword_rel (sp0 - 80) mf_s2.
      + (* [comment removed for export] *) kword_rel (sp0 - 88) mf_s3.
      + (* [comment removed for export] *) kword_rel (sp0 - 96) mf_s4.
      + (* [comment removed for export] *) kword_rel (sp0 - 104) mf_s5.
      + (* [comment removed for export] *) kword_rel (sp0 - 112) mf_s6.
      + (* [comment removed for export] *) kword_rel (sp0 - 120) mf_s7.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) kwr_def w_grp_def.
      + (* [comment removed for export] *) kwr_def w_area_def.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) kword_rel area Cs2.
      + (* [comment removed for export] *) kword_rel (area + 8) w_area_next.
      + (* [comment removed for export] *) kword_rel (area + 16) w_area_ns.
      + (* [comment removed for export] *) kword_rel (area + 24) w_slot0_prev.
      + (* [comment removed for export] *) kword_rel (area + 32) w_slot0_next.
      + (* [comment removed for export] *) kword_rel (area + 40) w_slot0_mem.
      + (* [comment removed for export] *) kword_rel (area + 48) w_slot0_msk.
      + (* [comment removed for export] *) kword_rel (area + 56) w_slot0_W.
      + (* [comment removed for export] *) kzero (area + 64) w_area_rest.
      + (* [comment removed for export] *) kword_rel gm w_grp_meta.
      + (* [comment removed for export] *) kword_rel (gm + 8) w_grp_aidx.
      + (* [comment removed for export] *) kzero (gm + 9) w_grp_pad.
      + (* [comment removed for export] *) kbyte_rel (gm + 13) Ps3.
      + (* [comment removed for export] *) kword_rel (gm + 14) Ps2.
      + (* [comment removed for export] *) kbyte_rel (gm + 28) Pm4.
      + (* [comment removed for export] *) kbyte_rel (gm + 29) Pm3.
      + (* [comment removed for export] *) kword_rel (gm + 30) Pm2.
      + (* [comment removed for export] *) kbyte_rel (gm + 65568) Pzr.
      + (* [comment removed for export] *) kbyte_rel (gm + 69623) Pe5.
      + (* [comment removed for export] *) kword_rel (gm + 69624) Pe4.
      + (* [comment removed for export] *) kzero (gm + 69628) w_grp_tail.
      + (* [comment removed for export] *) kblob TC w_grp_def.
      + (* [comment removed for export] *) kwr_data.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kword_abs (224152) w_self.
      + (* [comment removed for export] *) kword_abs (224184) w_tid.
      + (* [comment removed for export] *) kword_abs (224188) Ce.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kword_abs (355488) Cc.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kword_abs (356120) w_pagesz.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kword_abs (ctx_secret) Cs1.
      + (* [comment removed for export] *) kword_abs (ctx_init_done) w_init.
      + (* [comment removed for export] *) kword_abs (ctx_mmap_counter) w_ctr.
      + (* [comment removed for export] *) kword_abs (ctx_free_meta_head) w_fmh.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta) w_am.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta_count) w_amc.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta_area_count) w_amac.
      + (* [comment removed for export] *) kword_abs (ctx_meta_alloc_shift) w_mas.
      + (* [comment removed for export] *) kword_abs (ctx_meta_area_head) w_mah.
      + (* [comment removed for export] *) kword_abs (ctx_meta_area_tail) w_mat.
      + (* [comment removed for export] *) kword_abs (ctx_avail_meta_areas) w_amas.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kword_abs (ctx_active 44) w_active44.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kword_abs (ctx_usage 44) w_usage44.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kword_abs (ctx_seq) w_seq.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) kword_abs (ctx_brk) w_brk.
      + (* [comment removed for export] *) kimg w_img.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
      + (* [comment removed for export] *) karith.
    - (* [comment removed for export] *) reflexivity.
    - (* [comment removed for export] *) exact Mhalt.
    - (* [comment removed for export] *) exact Mlazy.
    - (* [comment removed for export] *) exact Mmat.
    - (* [comment removed for export] *) exact Mfds.
    - (* [comment removed for export] *)
      rewrite Mvm.
      destruct TV as [Vres Vhas Varea Vlen Vsmall Vseps Vlim Vsp Vgt Vat].
      constructor; cbn [c_maps c_nmaps c_live cs_T].
      + exact Vres.
      + unfold maps_T. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold smap_ok; cbn [sm_base sm_len sm_exact edenot];
          rewrite ?EV1, ?EV2; rewrite ?u_small by lia.
        * split; [lia|]. split; [lia|]. exact Vhas.
        * split; [lia|]. split; [lia|]. exact Varea.
      + lia.
      + unfold vm_live_bytes. pose proof (live_bytes_bound (vm_maps VM) 4 69632 Vlen Vsmall ltac:(lia)). lia.
      + eapply Forall_impl; [|exact Vsmall]. intros p [H1 H2]. lia.
      + eapply Forall_impl; [|exact Vsmall]. intros p [H1 H2]. lia.
      + apply seps_conv. exact Vseps.
      + exact Vlim.
      + (* [comment removed for export] *) unfold e_sp0. cbn [edenot]. rewrite EV0, Vsp. reflexivity.
      + (* [comment removed for export] *) rewrite Vsp, u_small by lia. unfold sp_window_lo, sp_window_hi. lia.
    - (* [comment removed for export] *)
      cbn [c_slots cs_T]. unfold slots_T, slots_ok. apply Forall_cons; [|apply Forall_nil].
      unfold slot_ok. cbn [sl_start sl_stride sl_n sl_off sl_W sl_idx sl_p split_lit is_lit]. unfold uE. enorm.
      rewrite !u_small by lia.
      split; [exact EP0 | repeat split; try lia].
      (* [comment removed for export] *)
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      lazymatch goal with H : gm mod 4096 = 0 |- _ => clear -H; lia end.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
End Entry.

Theorem target_entry_ok :
  forall (sp0 gm area brkv mas tid : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model) (nlo nhi : Z),
    target_pre sp0 gm area brkv mas tid content R M ->
    target_vm sp0 gm area VM ->
    m_fds model = fds_std -> m_vmmaps model = VM -> m_halted model = None ->
    m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    nlo <= hdr_paylen content <= nhi ->
    exists e c sv, 0 <= e < 2 ^ 32 /\
      cs_ok (E_T sp0 gm area tid content brkv mas e c sv R) (cs_T nlo nhi) R M model.
Proof.
  intros sp0 gm area brkv mas tid content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn.
  destruct (w_errno _ _ _ _ _ _ (tp_world _ _ _ _ _ _ _ _ _ TP)) as (e & He & Ce).
  destruct (w_canary _ _ _ _ _ _ (tp_world _ _ _ _ _ _ _ _ _ TP)) as (c & Cc).
  destruct (w_secret _ _ _ _ _ _ (tp_world _ _ _ _ _ _ _ _ _ TP)) as (sv & _ & Cs1 & Cs2).
  exists e, c, sv. split; [exact He|].
  apply (target_entry_ok_e sp0 gm area brkv mas tid content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn e He Ce c Cc sv Cs1 Cs2).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
