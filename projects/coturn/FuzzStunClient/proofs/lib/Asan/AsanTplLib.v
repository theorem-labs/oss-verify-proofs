(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import FContractAsan AsanNodesFX AsanNodesFSoundG AsanNodesUGSoundG AsanNodesLC AsanNodesLCSoundG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2 AX2S.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sregion : Type := (saddr * Z)%type.

(* [comment removed for export] *)
Fixpoint entry_covered (rs : list sregion) (a : saddr) (w : nat) : bool :=
  match rs with
  | [] => false
  | (SA rb rk, n) :: rest =>
      (expr_eqb (a_base a) rb && Z.leb rk (a_off a) && Z.leb (a_off a + Z.of_nat w) (rk + n))%bool
      || entry_covered rest a w
  end.
Fixpoint log_covered (rs : list sregion) (log : list sentry) : bool :=
  match log with
  | [] => true
  | SE a w _ :: rest => entry_covered rs a w && log_covered rs rest
  end.

Lemma entry_covered_in : forall E rs a w x,
  entry_covered rs a w = true -> estart E a <= x < estart E a + Z.of_nat w ->
  exists r, In r rs /\ estart E (fst r) <= x < estart E (fst r) + snd r.
Proof.
  intros E rs a w x. induction rs as [|[[rb rk] n] rest IH]; cbn [entry_covered]; intros Hc Hx; [discriminate|].
  apply orb_prop in Hc as [Hc|Hc].
  - apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    exists (SA rb rk, n). split; [left; reflexivity|]. cbn [fst snd]. unfold estart in *. cbn [a_base a_off] in *. rewrite <- H1. lia.
  - destruct (IH Hc Hx) as (r & Hin & Hr). exists r. split; [right; exact Hin | exact Hr].
Qed.

Theorem log_frame : forall E base rs log (x : word),
  log_covered rs log = true -> log_flat E log ->
  (forall r, In r rs -> ~ (estart E (fst r) <= bv_unsigned x < estart E (fst r) + snd r)) ->
  mem_denot E base log x = base x.
Proof.
  intros E base rs log x. induction log as [|[a w v] rest IH]; cbn [log_covered mem_denot log_flat]; intros Hc Hlf Hout; [reflexivity|].
  apply andb_prop in Hc as [H1 H2]. destruct Hlf as (Hw & Hfa & Hlf').
  pose proof (flat_u E a _ Hfa) as Hu. destruct Hfa as (F1 & F2 & F3 & F4).
  rewrite wbytes_out; [exact (IH H2 Hlf' Hout) | rewrite length_N_to_le_bytes, Hu; lia |].
  rewrite length_N_to_le_bytes, Hu.
  destruct (Z.lt_ge_cases (bv_unsigned x) (estart E a)) as [Hlt|Hge]; [left; exact Hlt|].
  destruct (Z.lt_ge_cases (bv_unsigned x) (estart E a + Z.of_nat w)) as [Hin|Hout2]; [|right; exact Hout2].
  exfalso. destruct (entry_covered_in E rs a w (bv_unsigned x) H1 ltac:(lia)) as (r & Hr & Hrx). exact (Hout r Hr Hrx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Module TPL.
(* [comment removed for export] *)
Record tplp : Type := TP { tp_fuel : nat; tp_shz : list Z }.

(* [comment removed for export] *)
Definition NXT (T : LCN.lctab) : N := (32 + N.of_nat (length (LCN.lc_vcells T)))%N.
Fixpoint vfacts (j : N) (l : list Z) : list kentry :=
  match l with [] => [] | a :: r => KWord (SA (ELit 0) a) 8 (EVar j) :: vfacts (N.succ j) r end.
(* [comment removed for export] *)
Definition KEPT : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Definition reg_expr (T : LCN.lctab) (i : nat) : expr :=
  match i with
  | 0%nat => ELit 0
  | 1%nat => ELit (LCN.lc_ret T)
  | 2%nat => EVar 0
  | _ => match find (fun rv : nat * Z => Nat.eqb (fst rv) i) (LCN.lc_regs T) with Some rv => ELit (snd rv) | None => EVar (N.of_nat i) end
  end.
Definition tpl_sr (T : LCN.lctab) : list expr := map (reg_expr T) (seq 0 32).

(* [comment removed for export] *)
Definition shz_expr (SB d : Z) : expr :=
  EMd M_MUL (ELit 8) (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 0) (ELit (- d))) (ELit 3)) (ELit SB)) (ELit 3)).

Definition tpl_kn (SB : Z) (P : tplp) (T : LCN.lctab) : list kentry :=
  KAlign (EVar 0) 16 :: KRange (EVar 0) (LCN.LC_SPLO + LCN.lc_win T) LCN.LC_SPHI
  :: KWr (SA (EVar 0) (- LCN.lc_win T)) (ELit (LCN.lc_win T))
  :: map (fun c : Z * nat * Z => let '(a, w, v) := c in KWord (SA (ELit 0) a) w (ELit v)) (LCN.lc_cells T)
  ++ vfacts 32 (LCN.lc_vcells T)
  ++ map (fun r : Z * Z => KWr (SA (ELit 0) (fst r)) (ELit (snd r))) (LCN.lc_wr T)
  ++ map (fun d : Z => KZero (SA (shz_expr SB d) 0) (ELit 8)) (tp_shz P).

Definition tpl_regions (T : LCN.lctab) : list sregion :=
  (SA (EVar 0) (- LCN.lc_win T), LCN.lc_win T) :: map (fun r : Z * Z => (SA (ELit 0) (fst r), snd r)) (LCN.lc_wr T).

(* [comment removed for export] *)
Definition tpl_env (sp : Z) (regs : bvmap 5 word) (xs : list word) : env :=
  Env (fun n : N => match n with
                | 0%N => Z_to_bv 64 sp
                | _ => if N.ltb n 32 then getr regs (Z_to_bv 5 (Z.of_N n)) else nth (N.to_nat (n - 32)) xs (Z_to_bv 64 0)
                end) (fun _ => []).

(* [comment removed for export] *)
Definition tpl_check (segs : list Segment) (t : itab) (SB : Z) (P : tplp) (T : LCN.lctab) : bool :=
  let sr := tpl_sr T in
  let kn := tpl_kn SB P T in
  let ss' := sym_execTX segs t 0 (tp_fuel P) true [LCN.lc_ret T] (SS (LCN.lc_entry T) sr [] kn (NXT T)) in
  let '(kn', scs, _) := carry (s_log ss') (s_know ss') [] in
  forallb (fun b : bool => b)
    [ Z.eqb (s_pc ss') (LCN.lc_ret T)
    ; forallb (fun i : nat => expr_eqb (nth i (s_regs ss') (ELit 0)) (nth i sr (ELit 0))) KEPT
    ; expr_eqb (nth 10 (s_regs ss') (ELit 0)) (ELit (LCN.lc_a0 T))
    ; log_covered (tpl_regions T) (s_log ss')
    ; match scs with [] => true | _ => false end
    ; forallb (fun c : Z * nat * Z => let '(a, w, v) := c in
                 match APC.kreadZ segs kn' (ELit 0) a w with Some z => Z.eqb z v | None => false end) (LCN.lc_post T)
    ; sr_vars_lt (NXT T) sr
    ; kn_vars_lt (NXT T) kn
    ; forallb (fun d : Z => (Z.leb 64 d && Z.leb (d + 128) (LCN.lc_win T))%bool) (tp_shz P) ].

(* [comment removed for export] *)
Definition tpl_diag (segs : list Segment) (t : itab) (SB : Z) (P : tplp) (T : LCN.lctab) : Z * nat * N * nat :=
  let sr := tpl_sr T in
  let kn := tpl_kn SB P T in
  let ss' := sym_execTX segs t 0 (tp_fuel P) true [LCN.lc_ret T] (SS (LCN.lc_entry T) sr [] kn (NXT T)) in
  let '(kn', scs, _) := carry (s_log ss') (s_know ss') [] in
  (s_pc ss', length (s_log ss'), s_next ss',
   LCN.first_false 1
    [ Z.eqb (s_pc ss') (LCN.lc_ret T)
    ; forallb (fun i : nat => expr_eqb (nth i (s_regs ss') (ELit 0)) (nth i sr (ELit 0))) KEPT
    ; expr_eqb (nth 10 (s_regs ss') (ELit 0)) (ELit (LCN.lc_a0 T))
    ; log_covered (tpl_regions T) (s_log ss')
    ; match scs with [] => true | _ => false end
    ; forallb (fun c : Z * nat * Z => let '(a, w, v) := c in
                 match APC.kreadZ segs kn' (ELit 0) a w with Some z => Z.eqb z v | None => false end) (LCN.lc_post T)
    ; sr_vars_lt (NXT T) sr
    ; kn_vars_lt (NXT T) kn
    ; forallb (fun d : Z => (Z.leb 64 d && Z.leb (d + 128) (LCN.lc_win T))%bool) (tp_shz P) ]).
End TPL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_store_ok : forall segs (M : word -> option byte) lo hi,
  (forall j, lo <= j < hi -> store_ok segs M (Z_to_bv 64 j) 1 = true) -> 0 <= lo -> hi <= 2 ^ 64 ->
  forall (a : word) (n : nat), lo <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= hi -> store_ok segs M a n = true.
Proof.
  intros segs M lo hi H Hlo Hhi a n Ha Hn. apply store_ok_of_all; [lia|].
  intros x Hx. pose proof (H (bv_unsigned x) ltac:(lia)) as Hb. rewrite Z_to_bv_bv_unsigned in Hb.
  cbn [store_ok] in Hb. destruct (wview segs M x); [discriminate | discriminate Hb].
Qed.

(* [comment removed for export] *)
Lemma shz_den : forall E sp SB d,
  ev E 0%N = Z_to_bv 64 sp -> 0 <= d <= sp -> sp < 2 ^ 62 -> 0 <= SB < 2 ^ 62 ->
  bv_unsigned (edenot E (TPL.shz_expr SB d)) = 8 * (((sp - d) / 8 + SB) / 8).
Proof.
  intros E sp SB d H0 Hd Hsp HSB. unfold TPL.shz_expr. cbn [edenot]. rewrite H0.
  assert (Q1 : 0 <= (sp - d) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Q2 : 0 <= ((sp - d) / 8 + SB) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  set (w1 := alu64 ALU_ADD (Z_to_bv 64 sp) (Z_to_bv 64 (- d))).
  assert (U1 : bv_unsigned w1 = sp - d) by (unfold w1; rewrite u_sub_lit by (rewrite u64_lit by lia; lia); rewrite u64_lit by lia; reflexivity).
  set (w2 := alu64 ALU_SRL w1 (Z_to_bv 64 3)).
  assert (U2 : bv_unsigned w2 = (sp - d) / 8).
  { unfold w2. rewrite (srl3_div8 w1 (Z_to_bv 64 3)) by (rewrite u64_lit by lia; reflexivity). rewrite U1. apply u64_lit. lia. }
  set (w3 := alu64 ALU_ADD w2 (Z_to_bv 64 SB)).
  assert (U3 : bv_unsigned w3 = (sp - d) / 8 + SB) by (unfold w3; rewrite (u_add_small w2 SB) by (rewrite ?U2; lia); rewrite U2; reflexivity).
  set (w4 := alu64 ALU_SRL w3 (Z_to_bv 64 3)).
  assert (U4 : bv_unsigned w4 = ((sp - d) / 8 + SB) / 8).
  { unfold w4. rewrite (srl3_div8 w3 (Z_to_bv 64 3)) by (rewrite u64_lit by lia; reflexivity). rewrite U3. apply u64_lit. lia. }
  rewrite u_mul64. rewrite (u64_lit 8) by lia. rewrite U4.
  apply Z.mod_small. lia.
Qed.

Lemma shz_window : forall sp win SB d,
  sp mod 16 = 0 -> win mod 64 = 0 -> 64 <= d -> d + 128 <= win -> win <= sp -> 0 <= SB ->
  SB + (sp - win) / 8 <= 8 * (((sp - d) / 8 + SB) / 8) /\ 8 * (((sp - d) / 8 + SB) / 8) + 8 <= SB + sp / 8.
Proof.
  intros sp win SB d H16 H64 Hd1 Hd2 Hw HSB.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section TplSound.
Variable segs : list Segment.
Variable t : itab.
Variable SB : Z.
Hypothesis Ht : itab_sound segs t.
Hypothesis HSB : 0 <= SB < 2 ^ 62.

Lemma forall_ex_list : forall (X Y : Type) (Q : X -> Y -> Prop) (l : list X),
  Forall (fun a => exists b, Q a b) l -> exists bs, Forall2 Q l bs.
Proof.
  intros X Y Q l H. induction H as [|a l [b Hb] _ [bs IH]]; [exists []; constructor|]. exists (b :: bs). constructor; assumption.
Qed.

Lemma vfacts_ok : forall E mem l xs j,
  Forall2 (fun (a : Z) (x : word) => rdn segs mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 x)) l xs ->
  Forall (fun a : Z => 0 <= a /\ a + 8 <= 2 ^ 64) l ->
  (forall i, (i < length xs)%nat -> ev E (j + N.of_nat i)%N = nth i xs (Z_to_bv 64 0)) ->
  know_ok segs E mem (TPL.vfacts j l).
Proof.
  intros E mem l xs j H. revert j. induction H as [|a x l xs Hax _ IH]; intros j Hb Hev; cbn [TPL.vfacts]; [constructor|].
  apply Forall_cons_iff in Hb as [[B1 B2] Hb]. apply Forall_cons.
  - eapply (kword_intro segs E mem (ELit 0) (Z_to_bv 64 0) a 8 (EVar j) x); try reflexivity; try lia; rewrite ?u64_lit by lia; try lia.
    + cbn [edenot]. pose proof (Hev 0%nat ltac:(cbn; lia)) as H0. change (N.of_nat 0) with 0%N in H0. rewrite N.add_0_r in H0. rewrite H0. reflexivity.
    + rewrite Z.add_0_l. exact Hax.
  - apply (IH (N.succ j) Hb). intros i Hi. replace (N.succ j + N.of_nat i)%N with (j + N.of_nat (S i))%N by lia. rewrite (Hev (S i) ltac:(cbn [length]; lia)). reflexivity.
Qed.

Lemma tpl_regs_ok : forall T regs sp xs,
  getr regs 2%bv = Z_to_bv 64 sp -> getr regs 1%bv = Z_to_bv 64 (LCN.lc_ret T) ->
  Forall (fun rv : nat * Z => getr regs (Z_to_bv 5 (Z.of_nat (fst rv))) = Z_to_bv 64 (snd rv)) (LCN.lc_regs T) ->
  regs_ok (TPL.tpl_env sp regs xs) (TPL.tpl_sr T) regs.
Proof.
  intros T regs sp xs H2 H1 HR r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - unfold getr. rewrite Hr0. reflexivity.
  - assert (Hlt : (ridx r < 32)%nat).
    { unfold ridx. pose proof (bv_unsigned_in_range 5 r) as X. change (bv_modulus 5) with 32 in X. lia. }
    pose proof (APSX.reg_of_ridx r (ridx r) eq_refl) as Hr.
    unfold TPL.tpl_sr. change (ELit 0) with (TPL.reg_expr T 0). rewrite map_nth. rewrite seq_nth by exact Hlt. cbn [Nat.add].
    set (i := ridx r) in *. clearbody i.
    destruct i as [|[|[|i]]].
    + exfalso. rewrite Hr in Hr0. discriminate Hr0.
    + cbn [TPL.reg_expr edenot]. rewrite Hr. rewrite <- H1. f_equal.
    + cbn [TPL.reg_expr edenot TPL.tpl_env ev]. rewrite Hr. rewrite <- H2. f_equal.
    + cbn [TPL.reg_expr].
      destruct (find (fun rv : nat * Z => Nat.eqb (fst rv) (S (S (S i)))) (LCN.lc_regs T)) as [rv|] eqn:Hf.
      * apply find_some in Hf as [Hin Heq]. apply Nat.eqb_eq in Heq.
        pose proof (proj1 (Forall_forall _ _) HR rv Hin) as Hv. cbn beta in Hv. rewrite Heq in Hv.
        cbn [edenot]. rewrite Hr. exact Hv.
      * cbn [edenot TPL.tpl_env ev]. rewrite Hr.
        destruct (N.of_nat (S (S (S i)))) as [|q] eqn:Hq; [lia|]. rewrite <- Hq.
        replace (N.ltb (N.of_nat (S (S (S i)))) 32) with true by (symmetry; apply N.ltb_lt; lia).
        rewrite nat_N_Z. reflexivity.
Qed.

Theorem tpl_sound : forall P T, lc_wf T = true -> TPL.tpl_check segs t SB P T = true -> lc_spec segs SB T.
Proof.
  intros P T WF CHK mem rom regs sp Hsp Hal Hrng Hra Hregs Hcells Hvcells Hwin Hzero Hwr.
  (* [comment removed for export] *)
  pose proof WF as WF'. unfold lc_wf in WF'. cbn [forallb] in WF'.
  repeat match type of WF' with (?a && ?b)%bool = true => apply andb_prop in WF'; destruct WF' as [?X WF']; revert X end.
  intros WFwr WFpost WFvcells WFcells WFregs WFa1 WFa0 WFw2 WFw1 WFw0. clear WF'.
  apply Z.ltb_lt in WFw0. apply Z.eqb_eq in WFw1. apply Z.ltb_lt in WFw2. apply Z.leb_le in WFa0. apply Z.ltb_lt in WFa1.
  set (win := LCN.lc_win T) in *.
  unfold LCN.LC_SPLO, LCN.LC_SPHI in Hrng, WFw2.
  (* [comment removed for export] *)
  unfold TPL.tpl_check in CHK.
  set (sr := TPL.tpl_sr T) in *. set (kn := TPL.tpl_kn SB P T) in *.
  set (ss' := sym_execTX segs t 0 (TPL.tp_fuel P) true [LCN.lc_ret T] (SS (LCN.lc_entry T) sr [] kn (TPL.NXT T))) in *.
  destruct (carry (s_log ss') (s_know ss') []) as [[kn' scs] hs'] eqn:Hcarry.
  cbn [forallb] in CHK.
  repeat match type of CHK with (?a && ?b)%bool = true => apply andb_prop in CHK; destruct CHK as [?X CHK]; revert X end.
  intros Cshz Cknv Csrv Cpost Cscs Clog Ca0 Ckept Cpc. clear CHK.
  apply Z.eqb_eq in Cpc. apply expr_eqb_eq in Ca0.
  destruct scs; [|discriminate]. clear Cscs.
  (* [comment removed for export] *)
  destruct (forall_ex_list _ _ _ _ Hvcells) as (xs & Hxs).
  set (E := TPL.tpl_env sp regs xs).
  assert (E0 : ev E 0%N = Z_to_bv 64 sp) by reflexivity.
  assert (U0 : bv_unsigned (edenot E (EVar 0)) = sp) by (cbn [edenot]; rewrite E0; apply u64_lit; lia).
  pose proof (tpl_regs_ok T regs sp xs Hsp Hra Hregs) as HR. fold E sr in HR.
  assert (HK : know_ok segs E mem kn).
  { unfold kn, TPL.tpl_kn. fold win. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split]]]]].
    - apply kalign_intro; [lia | rewrite U0; exact Hal].
    - apply krange_intro. rewrite U0. unfold LCN.LC_SPLO, LCN.LC_SPHI. lia.
    - apply (kwr_of_stk_ok segs E mem (EVar 0) (Z_to_bv 64 sp) win); [exact E0 | | rewrite u64_lit by lia; lia].
      intros a n Ha Hn. rewrite u64_lit in Ha, Hn by lia.
      exact (bytes_store_ok segs mem (sp - win) sp Hwin ltac:(lia) ltac:(lia) a n Ha Hn).
    - apply Forall_forall. intros K HKin. apply in_map_iff in HKin as ([[a w] v] & <- & Hin).
      pose proof (proj1 (Forall_forall _ _) Hcells _ Hin) as Hrd. pose proof (proj1 (forallb_forall _ _) WFcells _ Hin) as Hw.
      destruct (cell_wf_inv a w v Hw) as (C1 & C2 & C3 & C4).
      eapply (kword_intro segs E mem (ELit 0) (Z_to_bv 64 0) a w (ELit v) (Z_to_bv 64 v)); try reflexivity; try lia;
        rewrite ?u64_lit by lia; try lia.
      rewrite Z.add_0_l. exact Hrd.
    - apply (vfacts_ok E mem (LCN.lc_vcells T) xs 32 Hxs).
      + apply Forall_forall. intros a Hin. pose proof (proj1 (forallb_forall _ _) WFvcells _ Hin) as Hw. cbn beta in Hw.
        apply andb_prop in Hw as [W1 W2]. apply Z.leb_le in W1. apply Z.leb_le in W2. lia.
      + intros i Hi. unfold E, TPL.tpl_env. cbn [ev]. destruct (32 + N.of_nat i)%N as [|m] eqn:Hm; [lia|]. rewrite <- Hm.
        replace (N.ltb (32 + N.of_nat i) 32) with false by (symmetry; apply N.ltb_ge; lia).
        replace (N.to_nat (32 + N.of_nat i - 32)) with i by lia. reflexivity.
    - apply Forall_forall. intros K HKin. apply in_map_iff in HKin as ([a n] & <- & Hin). cbn [fst snd].
      pose proof (proj1 (Forall_forall _ _) Hwr _ Hin) as Hst. pose proof (proj1 (forallb_forall _ _) WFwr _ Hin) as Hw.
      cbn beta in Hst, Hw. cbn [fst snd] in Hw. unfold in_wr in Hst. cbn [fst snd] in Hst.
      apply andb_prop in Hw as [Hw W3]. apply andb_prop in Hw as [W1 W2]. apply Z.leb_le in W1. apply Z.ltb_lt in W2. apply Z.ltb_lt in W3.
      cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite !u64_lit by lia. split; [lia|].
      intros d m Hd Hm. rewrite Z.add_0_l.
      apply (bytes_store_ok segs mem a (a + n) Hst ltac:(lia) ltac:(lia)); rewrite u64_lit by lia; lia.
    - apply Forall_forall. intros K HKin. apply in_map_iff in HKin as (d & <- & Hin).
      pose proof (proj1 (forallb_forall _ _) Cshz _ Hin) as Hd. cbn beta in Hd. apply andb_prop in Hd as [D1 D2].
      apply Z.leb_le in D1. apply Z.leb_le in D2. fold win in D2.
      pose proof (shz_den E sp SB d E0 ltac:(lia) ltac:(lia) HSB) as Den.
      destruct (shz_window sp win SB d Hal WFw1 D1 D2 ltac:(lia) ltac:(lia)) as [S1 S2].
      assert (Q8 : 0 <= sp / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      assert (Q9 : 0 <= (sp - win) / 8) by (apply Z.div_pos; lia).
      apply (kzero_intro segs E mem (TPL.shz_expr SB d) (edenot E (TPL.shz_expr SB d)) 0 (ELit 8) 8).
      + reflexivity.
      + cbn [edenot]. apply u64_lit. lia.
      + rewrite Den. lia.
      + lia.
      + rewrite Den. lia.
      + intros i Hi. rewrite Den. apply Hzero. fold win. lia. }
  (* [comment removed for export] *)
  destruct (runTX_sound segs t 0 (TPL.tp_fuel P) [LCN.lc_ret T] (LCN.lc_entry T) sr kn (TPL.NXT T) E mem rom regs Ht HR HK Csrv Cknv)
    as (E' & R & Hag & Hle & HR' & Hlf & HK' & Hms & _).
  fold ss' in Hle, HR', Hlf, HK', Hms.
  pose proof (regs_ok_agree (TPL.NXT T) E E' sr regs Hag Csrv HR) as HRE'.
  assert (E0' : ev E' 0%N = Z_to_bv 64 sp) by (rewrite <- (proj1 Hag 0%N ltac:(unfold TPL.NXT; lia)); exact E0).
  exists R, (mem_denot E' mem (s_log ss')).
  split; [rewrite <- Cpc; exact Hms|].
  split.
  { (* [comment removed for export] *)
    intros r Hr0 Hnc.
    assert (Hb : bv_eqb r 0 = false).
    { unfold bv_eqb. apply Z.eqb_neq. intros Hc. apply Hr0. apply bv_eq. exact Hc. }
    rewrite (HR' r), (HRE' r). unfold sr_get. rewrite Hb.
    assert (Hin : In (ridx r) TPL.KEPT).
    { assert (Hlt : (ridx r < 32)%nat).
      { unfold ridx. pose proof (bv_unsigned_in_range 5 r) as X. change (bv_modulus 5) with 32 in X. lia. }
      assert (Hnz : ridx r <> 0%nat).
      { intros H0. apply Hr0. rewrite (APSX.reg_of_ridx r (ridx r) eq_refl), H0. apply bv_eq. reflexivity. }
      unfold APC.caller_saved in Hnc. unfold TPL.KEPT.
      set (n := ridx r) in *. clearbody n.
      do 32 (destruct n as [|n]; [ first [ exfalso; apply Hnz; reflexivity | exfalso; apply Hnc; cbn; tauto | cbn; tauto ] |]).
      exfalso. lia. }
    pose proof (proj1 (forallb_forall _ _) Ckept _ Hin) as Heq. cbn beta in Heq. apply expr_eqb_eq in Heq. rewrite Heq. reflexivity. }
  split.
  { (* [comment removed for export] *)
    rewrite (HR' 10%bv). unfold sr_get. change (bv_eqb (10%bv : reg) 0) with false. cbv iota.
    change (ridx (10%bv : reg)) with 10%nat. rewrite Ca0. reflexivity. }
  split; [apply mem_denot_grows|].
  split.
  { (* [comment removed for export] *)
    intros x Hxw Hxr. apply (log_frame E' mem (TPL.tpl_regions T) (s_log ss') x Clog Hlf).
    intros r Hin. unfold TPL.tpl_regions in Hin. fold win in Hin. destruct Hin as [<-|Hin].
    - cbn [fst snd]. unfold estart. cbn [a_base a_off edenot]. rewrite E0'. rewrite u64_lit by lia.
      intros Hc. apply Hxw. lia.
    - apply in_map_iff in Hin as ([a n] & <- & Hin). cbn [fst snd].
      pose proof (proj1 (forallb_forall _ _) WFwr _ Hin) as Hw. cbn beta in Hw. cbn [fst snd] in Hw.
      apply andb_prop in Hw as [Hw W3]. apply andb_prop in Hw as [W1 W2]. apply Z.leb_le in W1.
      unfold estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. rewrite Z.add_0_l.
      exact (proj1 (Forall_forall _ _) Hxr _ Hin). }
  (* [comment removed for export] *)
  assert (HK2 : know_ok segs E' (mem_denot E' mem (s_log ss')) kn').
  { apply (carry_after segs E' mem (s_log ss') (s_know ss') [] kn' [] hs' Hcarry Hlf HK'). constructor. }
  apply Forall_forall. intros [[a w] v] Hin.
  pose proof (proj1 (forallb_forall _ _) Cpost _ Hin) as Hb. pose proof (proj1 (forallb_forall _ _) WFpost _ Hin) as Hw.
  cbn beta iota in Hb. destruct (cell_wf_inv a w v Hw) as (C1 & C2 & C3 & C4).
  eapply (kreadZ_rd segs E' _ kn' a w v HK2); try lia. exact Hb.
Qed.

(* [comment removed for export] *)
Theorem tpl_all_sound : forall PS TS,
  length PS = length TS -> forallb lc_wf TS = true ->
  forallb (fun PT : TPL.tplp * LCN.lctab => TPL.tpl_check segs t SB (fst PT) (snd PT)) (combine PS TS) = true ->
  Forall (fun T => lc_wf T = true /\ lc_spec segs SB T) TS.
Proof.
  intros PS TS. revert PS. induction TS as [|T TS IH]; intros PS Hlen Hwf Hchk; [constructor|].
  destruct PS as [|P PS]; [discriminate Hlen|]. cbn [forallb combine fst snd] in Hwf, Hchk.
  apply andb_prop in Hwf as [W1 W2]. apply andb_prop in Hchk as [C1 C2]. injection Hlen as Hlen.
  constructor; [split; [exact W1 | exact (tpl_sound P T W1 C1)] | exact (IH PS Hlen W2 C2)].
Qed.
End TplSound.
