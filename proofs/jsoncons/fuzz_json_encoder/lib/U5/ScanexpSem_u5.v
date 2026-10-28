(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan L5Defs L5Core FrmInv FpBridge CutVF CutVFX.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import DecIface_u5 DecScanPure_u5 DecOkDefs_u5 DecOkSem_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import DecLemTac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD DecAssume.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module PSX.
Definition is_sign (c : Z) : bool := (c =? 43) || (c =? 45).
Definition nthz (l : list Z) (i : Z) : Z := nth (Z.to_nat i) (l ++ [0]) 0.
Lemma nthz_cons : forall c r j, 0 <= j -> nthz (c :: r) (j + 1) = nthz r j.
Proof. intros c r j Hj. unfold nthz. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. reflexivity. Qed.
Lemma nthz_0 : forall c r, nthz (c :: r) 0 = c. Proof. reflexivity. Qed.
Lemma span_digs : forall l m, 0 <= m <= Z.of_nat (length l) -> (forall j, 0 <= j < m -> PD.is_dig (nthz l j) = true) -> PD.is_dig (nthz l m) = false ->
  fst (PD.span PD.is_dig l) = m.
Proof.
  induction l as [|c r IH]; intros m Hm Hd Hs.
  - cbn [length] in Hm. cbn. lia.
  - cbn [PD.span]. destruct (Z.eq_dec m 0) as [->|Hne].
    + rewrite nthz_0 in Hs. rewrite Hs. reflexivity.
    + pose proof (Hd 0 ltac:(lia)) as H0. rewrite nthz_0 in H0. rewrite H0.
      specialize (IH (m - 1)). destruct (PD.span PD.is_dig r) as [n r']. cbn [fst] in *. cbn [length] in Hm. rewrite IH; [lia | lia | |].
      * intros j Hj. rewrite <- (nthz_cons c r j) by lia. apply Hd. lia.
      * rewrite <- (nthz_cons c r (m - 1)) by lia. replace (m - 1 + 1) with m by lia. exact Hs.
Qed.
Lemma dig_not_sign : forall c, PD.is_dig c = true -> is_sign c = false.
Proof. intros c H. unfold PD.is_dig, is_sign in *. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. apply orb_false_iff. split; apply Z.eqb_neq; lia. Qed.
(* [comment removed for export] *)
Lemma exp_scan_some : forall l sg m, (sg = 0 \/ (sg = 1 /\ is_sign (nthz l 0) = true)) -> sg < m <= Z.of_nat (length l) ->
  (forall j, sg <= j < m -> PD.is_dig (nthz l j) = true) -> PD.is_dig (nthz l m) = false -> PD.exp_scan l = Some m.
Proof.
  intros l sg m Hsg Hm Hd Hs. unfold PD.exp_scan. destruct l as [|c r]; [cbn [length] in Hm; lia|]. fold (is_sign c).
  destruct Hsg as [-> | [-> Hc]].
  - pose proof (Hd 0 ltac:(lia)) as H0. rewrite nthz_0 in H0. rewrite (dig_not_sign c H0).
    pose proof (span_digs (c :: r) m ltac:(lia) Hd Hs) as X. destruct (PD.span PD.is_dig (c :: r)) as [n r']. cbn [fst] in X. subst n.
    destruct (Z.eqb_spec m 0); [lia|]. reflexivity.
  - rewrite nthz_0 in Hc. rewrite Hc. cbn [length] in Hm.
    assert (X : fst (PD.span PD.is_dig r) = m - 1).
    { apply span_digs; [lia | |].
      - intros j Hj. rewrite <- (nthz_cons c r j) by lia. apply Hd. lia.
      - rewrite <- (nthz_cons c r (m - 1)) by lia. replace (m - 1 + 1) with m by lia. exact Hs. }
    destruct (PD.span PD.is_dig r) as [n r']. cbn [fst] in X. subst n. destruct (Z.eqb_spec (m - 1) 0); [lia|]. f_equal. lia.
Qed.
Lemma exp_scan_none : forall l, (is_sign (nthz l 0) = false /\ PD.is_dig (nthz l 0) = false) \/ (is_sign (nthz l 0) = true /\ PD.is_dig (nthz l 1) = false) -> PD.exp_scan l = None.
Proof.
  intros l H. unfold PD.exp_scan. destruct l as [|c r]; [reflexivity|]. fold (is_sign c). rewrite !nthz_0 in H. destruct H as [[H1 H2] | [H1 H2]]; rewrite H1.
  - cbn [PD.span]. rewrite H2. reflexivity.
  - change 1 with (0 + 1) in H2. rewrite nthz_cons in H2 by lia. destruct r as [|d r']; [reflexivity|]. rewrite nthz_0 in H2. cbn [PD.span]. rewrite H2. reflexivity.
Qed.
End PSX.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module SXS.
(* [comment removed for export] *)
Definition NF : nat := 34.
Definition NMAX : Z := 67108864.
Definition nk_e : expr := EAlu ALU_ADD (EVar 33) (EMd M_MUL (ELit (-1)) (EVar 34)).                      (* [comment removed for export] *)
Definition rpos_e : expr := EAlu ALU_ADD (EAlu ALU_ADD (EVar 32) nk_e) (ELit 1).                         (* [comment removed for export] *)
Definition named_a : saddr := SA (EAlu ALU_ADD (EAlu ALU_ADD (EVar 32) nk_e) (ELit (-1))) 1.             (* [comment removed for export] *)
Definition next_a : saddr := SA (EAlu ALU_ADD (EVar 32) nk_e) 1.                                         (* [comment removed for export] *)
Definition rpos_a : saddr := SA (EVar 10) 8.
Definition FOOT : list SGP.region := [(EVar 2, -80, ELit 80); (EVar 10, 8, ELit 8)].
Definition CSAVED : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition LMIN : Z := 9223372036854775808.

Inductive kind : Type := KE | KL (sg : Z) | KDead.
Definition rng_in := DOS.rng_in.
Definition kind_of (c : CC.cutpoint) : kind :=
  match reg_e c 2 with
  | EVar 2 => KE
  | _ => let kn := CC.cp_know c in
         if rng_in kn (EVar 38) 48 57 then KL 0 else if (rng_in kn (EVar 38) 43 43 || rng_in kn (EVar 38) 45 45)%bool then KL 1 else KDead
  end.
Definition cut_chk (c : CC.cutpoint) : bool :=
  let kn := CC.cp_know c in
  (Nat.leb NF (CC.cp_nx c) && regions_eqb (CC.cp_F c) FOOT
   && match kind_of c with
      | KE => true
      | KL _ => Nat.ltb 38 (CC.cp_nx c) && has kn (KWord rpos_a 8 rpos_e) && has kn (KRange nk_e 0 (4 * NMAX)) && has kn (KRange (EVar 34) 1 NMAX)
                && has kn (KWord named_a 1 (EVar 35)) && rng_in kn (EVar 35) 48 57 && has kn (KWord (SA (EVar 32) 0) 1 (EVar 38))
      | KDead => false
      end)%bool.
(* [comment removed for export] *)
Definition goto_chk2 (c cj : CC.cutpoint) (s : CC.subst) : bool :=
  let k' := CC.slook s 34 in
  match kind_of c, kind_of cj with
  | KE, KL sg => expr_eqb k' (if sg =? 0 then EVar 33 else EAlu ALU_ADD (EVar 33) (ELit (-1)))
  | KL sg, KL sg' => (Z.eqb sg sg' && expr_eqb k' (EAlu ALU_ADD (EVar 34) (ELit (-1))))%bool
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition only_var (v : nat) (K : kentry) : bool := (DLT.kpure K && forallb (Nat.eqb v) (DLT.kvars K))%bool.
Definition bfacts (cells : list kentry) (v : nat) : list kentry := List.filter (only_var v) cells.
Definition bytes_sat (cells : list kentry) (v : nat) (P : Z -> bool) : bool :=
  (rng_in cells (EVar v) 0 255
   && forallb (fun z => implb (forallb (DLT.kb (fun _ => z)) (bfacts cells v)) (P z)) (map Z.of_nat (seq 0 256)))%bool.
Definition byte_vars (cells : list kentry) : list nat := flat_map (fun K => match K with KRange (EVar v) 0 255 => [v] | _ => [] end) cells.
Definition dead_chk (cells : list kentry) : bool := existsb (fun v => bytes_sat cells v (fun _ => false)) (byte_vars cells).
Definition saddr_eqb (a b : saddr) : bool := (expr_eqb (a_base a) (a_base b) && Z.eqb (a_off a) (a_off b))%bool.
Fixpoint find_byte (kn : list kentry) (a : saddr) : option nat :=
  match kn with
  | [] => None
  | KWord a' 1 (EVar v) :: r => if saddr_eqb a' a then Some v else find_byte r a
  | _ :: r => find_byte r a
  end.
Fixpoint find_rpos (kn : list kentry) : option expr :=
  match kn with
  | [] => None
  | KWord a' 8 v :: r => if saddr_eqb a' rpos_a then Some v else find_rpos r
  | _ :: r => find_rpos r
  end.
Definition not_dig (z : Z) : bool := negb (PD.is_dig z).
Definition none_chk (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in let kn := CC.cp_know c in
  (match kind_of c with KE => true | _ => false end
   && CL.ps_reg_is ps 10 (ELit LMIN)
   && match find_rpos cells with Some v => expr_eqb v (EVar 32) | None => false end
   && (has kn (KRange (EVar 33) 0 0)
       || match find_byte cells (SA (EVar 32) 0) with
          | Some v0 =>
              bytes_sat cells v0 (fun z => negb (PSX.is_sign z) && not_dig z)
              || (bytes_sat cells v0 PSX.is_sign
                  && (has kn (KRange (EVar 33) 1 1)
                      || (rng_in kn (EVar 33) 1 NMAX && match find_byte cells (SA (EVar 32) 1) with Some v1 => bytes_sat cells v1 not_dig | None => false end)))
          | None => false
          end))%bool.
Definition a0_chk (cells : list kentry) (a0 : expr) : bool :=
  (CX.fact2_ok cells (KRange a0 0 (LMIN - 1)) || CX.fact2_ok cells (KRange (APC.esub (ELit 0) a0) 0 (LMIN - 1)))%bool.
Definition some_chk (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (match kind_of c with KL _ => true | _ => false end
   && existsb (fun ie : nat * expr => Nat.eqb (fst ie) 10 && a0_chk cells (snd ie))%bool (SR.ps_regs ps)
   && match find_rpos cells with Some v => expr_eqb v rpos_e | None => false end
   && (has cells (KRange (EVar 34) 1 1)
       || match find_byte cells next_a with Some v => bytes_sat cells v not_dig | None => false end))%bool.
Definition exit_chk (RET_PC : Z) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (Z.eqb (SR.ps_pc ps) RET_PC && CL.ps_keeps ps CSAVED && (dead_chk (SR.ps_cells ps) || none_chk c ps || some_chk c ps))%bool.
Definition leaf_chk (CPS : list CC.cutpoint) (RET_PC : Z) (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j s => match nth_error CPS j with Some cj => goto_chk2 c cj s | None => false end
  | CC.TOther _ => exit_chk RET_PC c ps
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lin_form := unfold lden; repeat (match goal with |- context [lin_of ?e] => let l := fresh "l" in set (l := lin_of e); vm_compute in l; subst l end);
                 cbn [fst snd tden]; unfold AX2S.uE; cbn [edenot].

Lemma u_lin_mod : forall E e v, lden E (lin_of e) = v -> bv_unsigned (edenot E e) = v mod 2 ^ 64.
Proof.
  intros E e v H. pose proof (lin_of_sound E e) as [q Hq]. unfold AX2S.uE in Hq. rewrite H in Hq. pose proof (u64_range (edenot E e)) as Hu. unfold two64 in Hu.
  rewrite Hq. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. exact Hu.
Qed.

Section Sem.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.
Variable CPS : list CC.cutpoint.
Variable RET_PC : Z.
Variable txt : list Z.
Variables Q F SP : Z.
Variable E0 : env.
Variable M0 : word -> option byte.
Variable model0 : Model.
Definition N : Z := Z.of_nat (length txt).
Hypothesis E0_sp : bv_unsigned (ev E0 2) = SP.
Hypothesis E0_F : bv_unsigned (ev E0 10) = F.
Hypothesis E0_Q : bv_unsigned (ev E0 32) = Q.
Hypothesis E0_N : bv_unsigned (ev E0 33) = N.
Hypothesis R_SP : PDC.STK_FLOOR + 80 <= SP <= 2 ^ 47.
Hypothesis R_F : PDC.STK_FLOOR <= F /\ F + 256 <= 2 ^ 47.
Hypothesis R_Q : 4096 <= Q /\ Q + N < 2 ^ 47 /\ N < 2 ^ 26.
Hypothesis T_bytes : L5.bytes_at segs M0 Q txt.
Hypothesis T_nul : L5.u8_at segs M0 (Q + N) 0.
Hypothesis T_rng : Forall (fun c => 0 <= c < 256) txt.
Hypothesis AP_TS : PDC.apart Q (N + 1) (SP - 80) 80.
Hypothesis AP_TF : PDC.apart Q (N + 1) (F + 8) 192.

Definition nz (i : Z) : Z := PSX.nthz txt i.
Lemma N_nonneg : 0 <= N. Proof. unfold N. lia. Qed.
Lemma nz_N : nz N = 0.
Proof. unfold nz, PSX.nthz, N. rewrite Nat2Z.id. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.
(* [comment removed for export] *)
Lemma text_byte : forall i, 0 <= i <= N -> L5.u8_at segs M0 (Q + i) (nz i) /\ 0 <= nz i < 256.
Proof.
  intros i Hi. destruct (Z.eq_dec i N) as [->|Hne]; [rewrite nz_N; split; [exact T_nul | lia]|].
  unfold nz, PSX.nthz. assert (Hlt : (Z.to_nat i < length txt)%nat) by (unfold N in *; lia). rewrite app_nth1 by exact Hlt. split.
  - pose proof (T_bytes (Z.to_nat i) Hlt) as B. rewrite Z2Nat.id in B by lia. exact B.
  - rewrite Forall_forall in T_rng. apply T_rng. apply nth_In. exact Hlt.
Qed.

(* [comment removed for export] *)
Definition out2 (a : Z) : Prop := ~ (SP - 80 <= a < SP) /\ ~ (F + 8 <= a < F + 16).
Lemma outside_F0 : forall x : word, out2 (bv_unsigned x) -> SGP.outside E0 FOOT x.
Proof.
  intros x (H1 & H2). unfold SGP.outside, FOOT. pose proof R_SP. pose proof R_F. unfold PDC.STK_FLOOR in *.
  repeat (apply Forall_cons); [| | apply Forall_nil]; rewrite ?(DOS.estart_reg E0 2 _ SP E0_sp), ?(DOS.estart_reg E0 10 _ F E0_F); rewrite !DOS.elen_lit by lia; lia.
Qed.
Lemma F0_out2 : forall x : word, SGP.outside E0 FOOT x -> out2 (bv_unsigned x).
Proof.
  intros x H. unfold SGP.outside, FOOT in H. pose proof R_SP. pose proof R_F. unfold PDC.STK_FLOOR in *.
  apply Forall_cons_iff in H as [A1 H]. apply Forall_cons_iff in H as [A2 _].
  rewrite ?(DOS.estart_reg E0 2 _ SP E0_sp), ?(DOS.estart_reg E0 10 _ F E0_F) in *. rewrite !DOS.elen_lit in * by lia. unfold out2. lia.
Qed.
Lemma cut_nf : forall c, cut_chk c = true -> (NF <= CC.cp_nx c)%nat.
Proof. intros c H. unfold cut_chk in H. do 2 (apply andb_prop in H as [H _]). apply Nat.leb_le. exact H. Qed.
Lemma sub_F_ok : forall c, cut_chk c = true -> CL.sub_F NF E0 FOOT c.
Proof.
  intros c H. unfold cut_chk in H. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. apply regions_eqb_eq in H.
  intros E a Hag Ho. rewrite H. exact (CL.outside_agree_F0 NF E0 FOOT eq_refl E a Hag Ho).
Qed.
Lemma ev_frozen : forall E n, env_agree NF E0 E -> (n < 34)%nat -> ev E n = ev E0 n.
Proof. intros E n [H _] Hn. symmetry. apply H. exact Hn. Qed.

(* [comment removed for export] *)
Lemma byte_link : forall E (M : word -> option byte) a v i, (forall x : word, SGP.outside E0 FOOT x -> M x = M0 x) ->
  kentry_ok segs E M (KWord a 1 (EVar v)) -> estart E a = Q + i -> 0 <= i <= N -> 0 <= bv_unsigned (ev E v) <= 255 -> nz i = bv_unsigned (ev E v).
Proof.
  intros E M a v i Hfr HK Ha Hi Hv. pose proof R_Q as (RQ1 & RQ2 & RQ3). pose proof R_SP. pose proof R_F. unfold PDC.STK_FLOOR in *.
  apply (kword8_elim segs E M a (EVar v) (Q + i)) in HK; [|exact Ha]. cbn [edenot] in HK. rewrite Z.mod_small in HK by lia.
  destruct (text_byte i Hi) as [Ht Rt].
  assert (Hm0 : L5.u8_at segs M0 (Q + i) (bv_unsigned (ev E v))).
  { apply (u8_at_same segs M M0 (Q + i) _ ltac:(lia) ltac:(lia)); [|exact HK].
    intros x Hx. symmetry. apply Hfr. apply outside_F0. unfold out2. rewrite Hx. destruct AP_TS as [A|A], AP_TF as [B|B]; lia. }
  exact (u8_at_inj segs M0 _ _ _ Ht Hm0 Rt ltac:(lia)).
Qed.

(* [comment removed for export] *)
Lemma bytes_sat_sound : forall cells v P E M, bytes_sat cells v P = true -> know_ok segs E M cells ->
  0 <= bv_unsigned (ev E v) <= 255 /\ P (bv_unsigned (ev E v)) = true.
Proof.
  intros cells v P E M H HK. unfold bytes_sat in H. apply andb_prop in H as [Hr Hall].
  pose proof (DOS.rng_in_sem segs E M cells (EVar v) 0 255 HK Hr) as Rv. unfold uE in Rv. cbn [edenot] in Rv. split; [exact Rv|].
  set (z := bv_unsigned (ev E v)) in *.
  pose proof (DOS.byte_enum _ Hall z Rv) as X. cbv beta in X.
  assert (Hf : forallb (DLT.kb (fun _ => z)) (bfacts cells v) = true).
  { apply forallb_forall. intros K HKin. unfold bfacts in HKin. apply filter_In in HKin as [Hin Ho]. unfold only_var in Ho. apply andb_prop in Ho as [Hp Hvs].
    apply (proj2 (DLT.kb_sound segs E M K (fun _ => z) Hp ltac:(intros n Hn; rewrite forallb_forall in Hvs; specialize (Hvs n Hn); apply Nat.eqb_eq in Hvs; subst n; reflexivity))).
    exact (proj1 (Forall_forall _ _) HK K Hin). }
  rewrite Hf in X. exact X.
Qed.
Lemma dead_sound : forall cells E M, dead_chk cells = true -> know_ok segs E M cells -> False.
Proof.
  intros cells E M H HK. unfold dead_chk in H. apply existsb_exists in H as (v & _ & Hv).
  destruct (bytes_sat_sound cells v _ E M Hv HK) as [_ X]. discriminate X.
Qed.
Lemma find_byte_In : forall kn a v, find_byte kn a = Some v -> exists a', In (KWord a' 1 (EVar v)) kn /\ a' = a.
Proof.
  induction kn as [|K r IH]; intros a v H; [discriminate|]. cbn [find_byte] in H.
  assert (G : find_byte r a = Some v -> exists a', In (KWord a' 1 (EVar v)) (K :: r) /\ a' = a) by (intros X; destruct (IH a v X) as (a' & Hin & He); exists a'; split; [right; exact Hin | exact He]).
  destruct K as [a' w v'| | | | | | | | |]; try exact (G H).
  do 2 (destruct w as [|w]; try exact (G H)). destruct v' as [|v'| | | | | |]; try exact (G H).
  destruct (saddr_eqb a' a) eqn:Ea; [|exact (G H)]. injection H as ->. exists a'. split; [left; reflexivity|].
  unfold saddr_eqb in Ea. apply andb_prop in Ea as [E1 E2]. apply expr_eqb_eq in E1. apply Z.eqb_eq in E2. destruct a', a. cbn [a_base a_off] in *. subst. reflexivity.
Qed.
Lemma find_rpos_In : forall kn v, find_rpos kn = Some v -> In (KWord rpos_a 8 v) kn.
Proof.
  induction kn as [|K r IH]; intros v H; [discriminate|]. cbn [find_rpos] in H.
  destruct K as [a' w v'| | | | | | | | |]; try (right; exact (IH _ H)).
  do 9 (destruct w as [|w]; try (right; exact (IH _ H))).
  destruct (saddr_eqb a' rpos_a) eqn:Ea; [|right; exact (IH _ H)]. injection H as ->. left.
  unfold saddr_eqb in Ea. apply andb_prop in Ea as [E1 E2]. apply expr_eqb_eq in E1. apply Z.eqb_eq in E2. destruct a'. cbn [a_base a_off] in *. subst. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma arrive : forall c sg E R (M : word -> option byte), cut_chk c = true -> kind_of c = KL sg -> CC.At segs c E R M -> env_agree NF E0 E ->
  (forall x : word, SGP.outside E0 FOOT x -> M x = M0 x) ->
  let k := bv_unsigned (ev E 34) in
  1 <= k <= N /\ L5.u64_at segs M (F + 8) (Q + (N + 1 - k)) /\ PD.is_dig (nz (N - k)) = true /\ (sg = 0 \/ (sg = 1 /\ PSX.is_sign (nz 0) = true))
  /\ (sg = 0 -> PD.is_dig (nz 0) = true).
Proof.
  intros c sg E R M H Hk [_ HK] Hag Hfr k. unfold cut_chk in H. rewrite Hk in H. apply andb_prop in H as [_ H]. do 6 (apply andb_prop in H as [H ?X]). clear H.
  pose proof R_SP. pose proof R_F. pose proof R_Q as (RQ1 & RQ2 & RQ3). pose proof N_nonneg. unfold PDC.STK_FLOOR in *.
  assert (UQ : bv_unsigned (ev E 32) = Q) by (rewrite (ev_frozen E 32 Hag) by lia; exact E0_Q).
  assert (UN : bv_unsigned (ev E 33) = N) by (rewrite (ev_frozen E 33 Hag) by lia; exact E0_N).
  assert (UF : bv_unsigned (ev E 10) = F) by (rewrite (ev_frozen E 10 Hag) by lia; exact E0_F).
  assert (Bk : 0 <= k < 2 ^ 64) by (pose proof (u64_range (ev E 34)) as B; unfold two64 in B; exact B).
  pose proof (DOS.know_in segs E M _ _ HK X4) as Hrp. pose proof (DOS.know_in segs E M _ _ HK X3) as Hnk. pose proof (DOS.know_in segs E M _ _ HK X2) as Hk1.
  pose proof (DOS.know_in segs E M _ _ HK X1) as Hnb. pose proof (DOS.rng_in_sem segs E M _ _ _ _ HK X0) as Rc. pose proof (DOS.know_in segs E M _ _ HK X) as Hc0.
  cbn [kentry_ok edenot] in Hk1. fold k in Hk1. unfold NMAX in *. unfold uE in Rc. cbn [edenot] in Rc.
  (* [comment removed for export] *)
  assert (Hkn : k <= N).
  { destruct (Z_le_gt_dec k N) as [?|Hgt]; [assumption|]. exfalso. cbn [kentry_ok] in Hnk.
    assert (Ev : bv_unsigned (edenot E nk_e) = (N - k) mod 2 ^ 64) by (apply u_lin_mod; lin_form; rewrite UN; fold k; lia).
    replace (N - k) with (N - k + 2 ^ 64 + (-1) * 2 ^ 64) in Ev by lia. rewrite Z.mod_add in Ev by lia. rewrite Z.mod_small in Ev by lia. lia. }
  split; [lia|]. split; [|split].
  - apply (CL5.kword64_elim segs E M rpos_a rpos_e (F + 8) _ Hrp); [apply (DOS.estart_reg E 10 8 F UF)|].
    apply CL5.u_lin; [lin_form; rewrite UQ, UN; fold k; lia | lia].
  - assert (Ea : estart E named_a = Q + (N - k)).
    { unfold named_a. rewrite (CL5.estart_lin E _ 1 (Q + (N - k) - 1)); [lia | lin_form; rewrite UQ, UN; fold k; lia | lia]. }
    rewrite (byte_link E M named_a 35 (N - k) Hfr Hnb Ea ltac:(lia) ltac:(lia)). unfold PD.is_dig. apply andb_true_intro. split; apply Z.leb_le; lia.
  - assert (Ea : estart E (SA (EVar 32) 0) = Q + 0) by (apply (DOS.estart_reg E 32 0 Q UQ)).
    unfold kind_of in Hk. destruct (reg_e c 2) as [|[|[|[|n]]]| | | | | |] eqn:E2; try discriminate Hk;
      (destruct (rng_in (CC.cp_know c) (EVar 38) 48 57) eqn:R0;
       [injection Hk as <-; pose proof (DOS.rng_in_sem segs E M _ _ _ _ HK R0) as Rv; unfold uE in Rv; cbn [edenot] in Rv;
        pose proof (byte_link E M _ 38 0 Hfr Hc0 Ea ltac:(lia) ltac:(lia)) as L0;
        split; [left; reflexivity | intros _; rewrite L0; unfold PD.is_dig; apply andb_true_intro; split; apply Z.leb_le; lia]
       |destruct (rng_in (CC.cp_know c) (EVar 38) 43 43 || rng_in (CC.cp_know c) (EVar 38) 45 45)%bool eqn:R1; [|discriminate Hk]; injection Hk as <-;
        split; [right; split; [reflexivity|] | intros; lia];
        apply orb_prop in R1 as [R1|R1]; pose proof (DOS.rng_in_sem segs E M _ _ _ _ HK R1) as Rv; unfold uE in Rv; cbn [edenot] in Rv;
        rewrite (byte_link E M _ 38 0 Hfr Hc0 Ea ltac:(lia) ltac:(lia)); unfold PSX.is_sign; apply orb_true_iff; [left | right]; apply Z.eqb_eq; lia]).
Qed.

(* [comment removed for export] *)
Definition XI (i : nat) (E : env) (M : word -> option byte) : Prop :=
  match nth_error CPS i with
  | Some c => match kind_of c with
              | KE => True
              | KL sg => let m := N + 1 - bv_unsigned (ev E 34) in sg < m /\ forall j, sg <= j < m -> PD.is_dig (nz j) = true
              | KDead => False
              end
  | None => False
  end.
Definition Amb := CVX.AmbX NF E0 M0 model0 FOOT XI.

Lemma u_m1 : forall E e v, bv_unsigned (edenot E e) = v -> bv_unsigned (edenot E (EAlu ALU_ADD e (ELit (-1)))) = (v - 1) mod 2 ^ 64.
Proof.
  intros E e v H. cbn [edenot]. rewrite u_add64, H. change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1).
  replace (v + (2 ^ 64 - 1)) with (v - 1 + 1 * 2 ^ 64) by lia. apply Z.mod_add. lia.
Qed.

Lemma xi_goto : forall i c ps j cj s E R (M : word -> option byte) model E' R' M',
  nth_error CPS i = Some c -> nth_error CPS j = Some cj -> cut_chk c = true -> cut_chk cj = true ->
  CC.goto_chk NF c ps cj s = true -> goto_chk2 c cj s = true ->
  CC.At segs c E R M -> Amb i E M model -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts segs c ps E' R' M M' ->
  XI j (CC.env_over NF s E') M'.
Proof.
  intros i c ps j cj s E R M model E' R' M' Hc Hcj Ci Cj Hg H2 HAt [HAmb HX] Hag HLF.
  destruct (CC.goto_chk_sound segs NF c ps cj s E E' R' M M' Hg Hag HLF) as (_ & HAt' & _ & _).
  set (E2 := CC.env_over NF s E') in *.
  assert (HAmb' : CL.pure_amb NF E0 M0 model0 FOOT j E2 M' model).
  { eapply CL.pure_amb_step with (c := c); [exact (sub_F_ok c Ci) | exact (cut_nf c Ci) | exact HAmb | exact Hag | exact HLF | apply CC.env_over_agree]. }
  pose proof HAmb as (_ & Hag0 & Hfr & _). destruct HAmb' as (_ & Hag02 & Hfr' & _).
  assert (Hag0' : env_agree NF E0 E') by (eapply CC.env_agree_trans; [exact Hag0 | eapply CC.env_agree_le; [exact Hag | exact (cut_nf c Ci)]]).
  pose proof N_nonneg as HN0. pose proof R_Q as (RQ1 & RQ2 & RQ3).
  assert (K34 : ev E2 34 = edenot E' (CC.slook s 34)) by reflexivity.
  assert (UN' : bv_unsigned (ev E' 33) = N) by (rewrite (ev_frozen E' 33 Hag0') by lia; exact E0_N).
  unfold XI in *. rewrite Hc in HX. rewrite Hcj. unfold goto_chk2 in H2.
  destruct (kind_of c) as [|sg|] eqn:Kc; destruct (kind_of cj) as [|sg'|] eqn:Kj; try discriminate H2.
  - (* [comment removed for export] *)
    pose proof (arrive cj sg' E2 R' M' Cj Kj HAt' Hag02 Hfr') as (A1 & _ & A3 & A4 & A5). cbv zeta in A1, A3.
    apply expr_eqb_eq in H2. rewrite K34, H2 in A1, A3 |- *.
    destruct (Z.eqb_spec sg' 0) as [->|Hne].
    + cbn [edenot] in A1, A3 |- *. rewrite UN' in *. cbv zeta. split; [lia|]. intros j0 Hj0. replace j0 with (N - N) by lia. exact A3.
    + destruct A4 as [?|[-> _]]; [contradiction|].
      rewrite (u_m1 E' (EVar 33) N UN') in A1, A3 |- *.
      assert (HN1 : 1 <= N). { destruct (Z_le_gt_dec 1 N); [assumption|]. assert (N = 0) by lia. subst. rewrite H in A1. change ((0 - 1) mod 2 ^ 64) with (2 ^ 64 - 1) in A1. lia. }
      rewrite Z.mod_small in A1, A3 |- * by lia. cbv zeta. split; [lia|]. intros j0 Hj0. replace j0 with (N - (N - 1)) by lia. exact A3.
  - (* [comment removed for export] *)
    apply andb_prop in H2 as [Hs H2]. apply Z.eqb_eq in Hs. subst sg'. apply expr_eqb_eq in H2.
    pose proof (arrive c sg E R M Ci Kc HAt Hag0 Hfr) as (B1 & _). cbv zeta in B1.
    pose proof (arrive cj sg E2 R' M' Cj Kj HAt' Hag02 Hfr') as (A1 & _ & A3 & _). cbv zeta in A1, A3.
    assert (Hnx : (38 < CC.cp_nx c)%nat).
    { unfold cut_chk in Ci. rewrite Kc in Ci. apply andb_prop in Ci as [_ Ci]. do 6 (apply andb_prop in Ci as [Ci _]). apply Nat.ltb_lt. exact Ci. }
    assert (U34 : bv_unsigned (edenot E' (EVar 34)) = bv_unsigned (ev E 34)) by (cbn [edenot]; rewrite <- (proj1 Hag 34%nat) by lia; reflexivity).
    set (k := bv_unsigned (ev E 34)) in *.
    rewrite K34, H2, (u_m1 E' (EVar 34) k U34) in A3 |- *. rewrite Z.mod_small in A3 |- * by lia.
    cbv zeta in HX |- *. destruct HX as [HX1 HX2]. split; [lia|]. intros j0 Hj0.
    destruct (Z_lt_le_dec j0 (N + 1 - k)) as [Hlt|Hge]; [apply HX2; lia|]. replace j0 with (N - (k - 1)) by lia. exact A3.
Qed.

(* [comment removed for export] *)
Lemma exit_ok : forall i c ps E R (M : word -> option byte) model E' R' M',
  nth_error CPS i = Some c -> cut_chk c = true -> exit_chk RET_PC c ps = true ->
  CC.At segs c E R M -> Amb i E M model -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts segs c ps E' R' M M' ->
  SR.ps_pc ps = RET_PC /\ model = model0 /\ (forall x, In x CSAVED -> getr R' (Z_to_bv 5 (Z.of_nat x)) = ev E0 x)
  /\ (forall a : word, out2 (bv_unsigned a) -> M' a = M0 a) /\ mem_grows M0 M'
  /\ match PD.exp_scan txt with
     | Some n => L5.u64_at segs M' (F + 8) (Q + n) /\ PDC.rz R' 10 <> 2 ^ 63
     | None => L5.u64_at segs M' (F + 8) Q /\ PDC.rz R' 10 = 2 ^ 63
     end.
Proof.
  intros i c ps E R M model E' R' M' Hc Ci Hx HAt [HAmb HX] Hag HLF.
  assert (HA' : CL.pure_amb NF E0 M0 model0 FOOT 0%nat E' M' model).
  { eapply CL.pure_amb_step with (c := c); [exact (sub_F_ok c Ci) | exact (cut_nf c Ci) | exact HAmb | exact Hag | exact HLF | apply CC.env_agree_refl]. }
  pose proof HAmb as (_ & Hag0 & Hfr & _). destruct HA' as (Hm & Hag0' & Hfr' & Hgr').
  unfold exit_chk in Hx. do 2 (apply andb_prop in Hx as [Hx ?Y]). apply Z.eqb_eq in Hx.
  split; [exact Hx|]. split; [exact Hm|]. split; [|split; [|split; [exact Hgr'|]]].
  - intros x Hin. unfold CL.ps_keeps in Y0. rewrite forallb_forall in Y0.
    rewrite (CL.ps_reg_is_sound segs c ps E' R' M M' x (EVar x) HLF (Y0 x Hin)). cbn [edenot]. apply (ev_frozen E' x Hag0').
    unfold CSAVED in Hin. cbn [In] in Hin. lia.
  - intros a Ha. apply Hfr'. apply outside_F0. exact Ha.
  - assert (HK' : know_ok segs E' M' (SR.ps_cells ps)) by (apply Forall_forall; intros Z HZ; exact (CC.lf_cells _ _ _ _ _ _ _ HLF Z HZ)).
    pose proof R_SP. pose proof R_F. pose proof R_Q as (RQ1 & RQ2 & RQ3). pose proof N_nonneg as HN0. unfold PDC.STK_FLOOR in *.
    assert (UQ' : bv_unsigned (ev E' 32) = Q) by (rewrite (ev_frozen E' 32 Hag0') by lia; exact E0_Q).
    assert (UN' : bv_unsigned (ev E' 33) = N) by (rewrite (ev_frozen E' 33 Hag0') by lia; exact E0_N).
    assert (UF' : bv_unsigned (ev E' 10) = F) by (rewrite (ev_frozen E' 10 Hag0') by lia; exact E0_F).
    assert (UNe : bv_unsigned (ev E 33) = N) by (rewrite (ev_frozen E 33 Hag0) by lia; exact E0_N).
    apply orb_prop in Y as [Y|Y]; [apply orb_prop in Y as [Y|Y]|].
    + exfalso. exact (dead_sound _ E' M' Y HK').
    + (* [comment removed for export] *)
      unfold none_chk in Y. do 3 (apply andb_prop in Y as [Y ?Z]). clear Y. destruct HAt as [_ HKc].
      assert (Hnone : PD.exp_scan txt = None).
      { apply PSX.exp_scan_none. fold (nz 0) (nz 1). apply orb_prop in Z as [Z|Z].
        - left. pose proof (DOS.know_in segs E M _ _ HKc Z) as X. cbn [kentry_ok edenot] in X. assert (N = 0) by lia.
          assert (E0z : nz 0 = 0) by (pose proof nz_N as X0; rewrite H1 in X0; exact X0). rewrite E0z. split; reflexivity.
        - destruct (find_byte (SR.ps_cells ps) (SA (EVar 32) 0)) as [v0|] eqn:F0; [|discriminate Z].
          destruct (find_byte_In _ _ _ F0) as (a0 & Hin0 & ->).
          assert (L0 : forall P, bytes_sat (SR.ps_cells ps) v0 P = true -> P (nz 0) = true).
          { intros P HP. destruct (bytes_sat_sound _ v0 P E' M' HP HK') as [Rv Pv].
            rewrite (byte_link E' M' _ v0 0 Hfr' (proj1 (Forall_forall _ _) HK' _ Hin0) (DOS.estart_reg E' 32 0 Q UQ') ltac:(lia) Rv). exact Pv. }
          apply orb_prop in Z as [Z|Z].
          + left. apply L0 in Z. apply andb_prop in Z as [W1 W2]. unfold not_dig in W2. apply negb_true_iff in W1, W2. split; assumption.
          + right. apply andb_prop in Z as [W1 Z2]. split; [exact (L0 _ W1)|]. apply orb_prop in Z2 as [Z2|Z2].
            * pose proof (DOS.know_in segs E M _ _ HKc Z2) as X. cbn [kentry_ok edenot] in X. assert (N = 1) by lia.
              assert (E1z : nz 1 = 0) by (pose proof nz_N as X0; rewrite H1 in X0; exact X0). rewrite E1z. reflexivity.
            * apply andb_prop in Z2 as [Z2 Z3]. pose proof (DOS.rng_in_sem segs E M _ _ _ _ HKc Z2) as X. unfold uE in X. cbn [edenot] in X.
              destruct (find_byte (SR.ps_cells ps) (SA (EVar 32) 1)) as [v1|] eqn:F1; [|discriminate Z3].
              destruct (find_byte_In _ _ _ F1) as (a1 & Hin1 & ->).
              destruct (bytes_sat_sound _ v1 _ E' M' Z3 HK') as [Rv Pv].
              rewrite (byte_link E' M' _ v1 1 Hfr' (proj1 (Forall_forall _ _) HK' _ Hin1) (DOS.estart_reg E' 32 1 Q UQ') ltac:(lia) Rv).
              unfold not_dig in Pv. apply negb_true_iff in Pv. exact Pv. }
      rewrite Hnone. split.
      * destruct (find_rpos (SR.ps_cells ps)) as [v|] eqn:Fr; [|discriminate Z0]. apply expr_eqb_eq in Z0. subst v. apply find_rpos_In in Fr.
        apply (CL5.kword64_elim segs E' M' rpos_a (EVar 32) (F + 8) _ (proj1 (Forall_forall _ _) HK' _ Fr) (DOS.estart_reg E' 10 8 F UF')). cbn [edenot]. exact UQ'.
      * unfold PDC.rz, PDC.reg_of. rewrite (CL.ps_reg_is_sound segs c ps E' R' M M' 10 _ HLF Z1). cbn [edenot]. reflexivity.
    + (* [comment removed for export] *)
      unfold some_chk in Y. do 3 (apply andb_prop in Y as [Y ?Z]). destruct (kind_of c) as [|sg|] eqn:Kc; try discriminate Y. clear Y.
      pose proof (arrive c sg E R M Ci Kc HAt Hag0 Hfr) as (B1 & _ & _ & B4 & _). cbv zeta in B1.
      assert (Hnx : (38 < CC.cp_nx c)%nat).
      { unfold cut_chk in Ci. rewrite Kc in Ci. apply andb_prop in Ci as [_ Ci]. do 6 (apply andb_prop in Ci as [Ci _]). apply Nat.ltb_lt. exact Ci. }
      assert (U34 : bv_unsigned (ev E' 34) = bv_unsigned (ev E 34)) by (rewrite <- (proj1 Hag 34%nat) by lia; reflexivity).
      unfold XI in HX. rewrite Hc, Kc in HX. cbv zeta in HX. destruct HX as [HX1 HX2].
      set (k := bv_unsigned (ev E 34)) in *. set (m := N + 1 - k) in *.
      assert (Hstop : PD.is_dig (nz m) = false).
      { apply orb_prop in Z as [Z|Z].
        - pose proof (DOS.know_in segs E' M' _ _ HK' Z) as X. cbn [kentry_ok edenot] in X. rewrite U34 in X. replace m with N by (unfold m; lia). rewrite nz_N. reflexivity.
        - destruct (find_byte (SR.ps_cells ps) next_a) as [v|] eqn:Fb; [|discriminate Z]. destruct (find_byte_In _ _ _ Fb) as (a1 & Hin1 & ->).
          destruct (bytes_sat_sound _ v _ E' M' Z HK') as [Rv Pv].
          assert (Ea : estart E' next_a = Q + m).
          { unfold next_a. rewrite (CL5.estart_lin E' _ 1 (Q + (N - k))); [unfold m; lia | lin_form; rewrite UQ', UN', U34; fold k; lia | lia]. }
          rewrite (byte_link E' M' _ v m Hfr' (proj1 (Forall_forall _ _) HK' _ Hin1) Ea ltac:(unfold m; lia) Rv).
          unfold not_dig in Pv. apply negb_true_iff in Pv. exact Pv. }
      rewrite (PSX.exp_scan_some txt sg m B4 ltac:(unfold m, N in *; lia) HX2 Hstop). split.
      * destruct (find_rpos (SR.ps_cells ps)) as [v|] eqn:Fr; [|discriminate Z0]. apply expr_eqb_eq in Z0. subst v. apply find_rpos_In in Fr.
        apply (CL5.kword64_elim segs E' M' rpos_a rpos_e (F + 8) _ (proj1 (Forall_forall _ _) HK' _ Fr) (DOS.estart_reg E' 10 8 F UF')).
        apply CL5.u_lin; [lin_form; rewrite UQ', UN', U34; fold k; unfold m; lia | unfold m; lia].
      * apply existsb_exists in Z1 as ([r e] & Hin & Hb). cbn [fst snd] in Hb. apply andb_prop in Hb as [Hr Ha]. apply Nat.eqb_eq in Hr. subst r.
        unfold PDC.rz, PDC.reg_of. rewrite (CL.leaf_reg segs c ps E' R' M M' 10 e HLF Hin). unfold a0_chk in Ha. unfold LMIN in Ha.
        apply orb_prop in Ha as [Ha|Ha]; pose proof (CX.fact2_ok_sound segs E' M' _ _ HK' Ha) as X; cbn [kentry_ok] in X.
        -- lia.
        -- unfold APC.esub in X. rewrite mkAlu_denot, u_sub64 in X. cbn [edenot] in X. intros Heq. rewrite Heq in X. vm_compute in X. destruct X as [_ X]. apply X. reflexivity.
Qed.
End Sem.
End SXS.
