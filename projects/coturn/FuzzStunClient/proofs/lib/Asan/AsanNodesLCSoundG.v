(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import FContractAsan AsanNodesFX AsanNodesFSoundG AsanNodesUGSoundG AsanNodesLC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2 AX2S APC AP APS APSX.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition in_wr (x : Z) (r : Z * Z) : Prop := fst r <= x < fst r + snd r.

Definition lc_spec (SEGS : list Segment) (SB : Z) (T : LCN.lctab) : Prop :=
  forall (mem rom : word -> option byte) (regs : bvmap 5 word) (sp : Z),
    getr regs 2%bv = Z_to_bv 64 sp -> sp mod 16 = 0 -> LCN.LC_SPLO + LCN.lc_win T <= sp <= LCN.LC_SPHI ->
    getr regs 1%bv = Z_to_bv 64 (LCN.lc_ret T) ->
    Forall (fun rv : nat * Z => getr regs (Z_to_bv 5 (Z.of_nat (fst rv))) = Z_to_bv 64 (snd rv)) (LCN.lc_regs T) ->
    Forall (rd_ok SEGS mem) (LCN.lc_cells T) ->
    Forall (fun a : Z => exists x : word, rdn SEGS mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 x)) (LCN.lc_vcells T) ->
    (forall j, sp - LCN.lc_win T <= j < sp -> store_ok SEGS mem (Z_to_bv 64 j) 1 = true) ->
    (forall j, SB + (sp - LCN.lc_win T) / 8 <= j < SB + sp / 8 -> mem (Z_to_bv 64 j) = Some (Z_to_bv 8 0)) ->
    Forall (fun r : Z * Z => forall j, in_wr j r -> store_ok SEGS mem (Z_to_bv 64 j) 1 = true) (LCN.lc_wr T) ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps SEGS (mkst regs (Z_to_bv 64 (LCN.lc_entry T)) mem rom) (mkst regs' (Z_to_bv 64 (LCN.lc_ret T)) mem' rom)
      /\ kept_ok regs regs'
      /\ getr regs' 10%bv = Z_to_bv 64 (LCN.lc_a0 T)
      /\ mem_grows mem mem'
      /\ (forall x : word, ~ (sp - LCN.lc_win T <= bv_unsigned x < sp) -> Forall (fun r => ~ in_wr (bv_unsigned x) r) (LCN.lc_wr T) -> mem' x = mem x)
      /\ Forall (rd_ok SEGS mem') (LCN.lc_post T).

(* [comment removed for export] *)
Definition cell_wf (c : Z * nat * Z) : bool :=
  let '(a, w, v) := c in forallb (fun b : bool => b) [Z.leb 0 a; Z.leb (a + Z.of_nat w) (2 ^ 64); Nat.leb 1 w; Nat.leb w 8; Z.leb 0 v; Z.ltb v (2 ^ 64)].
Definition lc_wf (T : LCN.lctab) : bool :=
  forallb (fun b : bool => b)
  [ Z.ltb 0 (LCN.lc_win T); Z.eqb (LCN.lc_win T mod 64) 0; Z.ltb (LCN.lc_win T) LCN.LC_SPLO
  ; Z.leb 0 (LCN.lc_a0 T); Z.ltb (LCN.lc_a0 T) (2 ^ 64)
  ; forallb (fun rv : nat * Z => (Nat.ltb 0 (fst rv) && Nat.ltb (fst rv) 32)%bool) (LCN.lc_regs T)
  ; forallb cell_wf (LCN.lc_cells T)
  ; forallb (fun a : Z => (Z.leb 0 a && Z.leb (a + 8) (2 ^ 64))%bool) (LCN.lc_vcells T)
  ; forallb cell_wf (LCN.lc_post T)
  ; forallb (fun r : Z * Z => (Z.leb 0 (fst r) && Z.ltb 0 (snd r) && Z.ltb (fst r + snd r) (2 ^ 64))%bool) (LCN.lc_wr T) ].

Lemma cell_wf_inv : forall a w v, cell_wf (a, w, v) = true ->
  0 <= a /\ a + Z.of_nat w <= 2 ^ 64 /\ (1 <= w <= 8)%nat /\ 0 <= v < 2 ^ 64.
Proof.
  intros a w v H. unfold cell_wf in H. cbn [forallb] in H.
  repeat match type of H with (?x && ?y)%bool = true => apply andb_prop in H; destruct H as [?X H]; revert X end.
  intros C6 C5 C4 C3 C2 C1. apply Z.leb_le in C1. apply Z.leb_le in C2. apply Nat.leb_le in C3. apply Nat.leb_le in C4.
  apply Z.leb_le in C5. apply Z.ltb_lt in C6. lia.
Qed.

Lemma forallb_map_lc : forall (X Y : Type) (f : X -> Y) (p : Y -> bool) (l : list X),
  forallb p (map f l) = forallb (fun x => p (f x)) l.
Proof. intros X Y f p l. induction l as [|x l IH]; [reflexivity|]. cbn [map forallb]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : N.
Variable LIMIT : Z.
Hypothesis SEGS_wx : AsanAcct.wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Hypothesis SEGS_wr : segs_wr_ok SEGS.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis nx0_ge7 : APS.nx0_ok nx0.
Variable FS0 : Fs.Fs.
Hypothesis SHADOW_ok : shadow_ok A.

#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).

(* [comment removed for export] *)
Lemma store_ok_bytes : forall M (s n : Z), 0 <= s -> 0 <= n -> s + n <= 2 ^ 64 ->
  store_ok SEGS M (Z_to_bv 64 s) (Z.to_nat n) = true ->
  forall j, s <= j < s + n -> store_ok SEGS M (Z_to_bv 64 j) 1 = true.
Proof.
  intros M s n Hs Hn Hsn Hst j Hj.
  pose proof (store_ok_all SEGS M (Z.to_nat n) (Z_to_bv 64 s) ltac:(rewrite u64_lit by lia; rewrite Z2Nat.id by lia; lia) Hst
                (Z_to_bv 64 j) ltac:(rewrite !u64_lit by lia; rewrite Z2Nat.id by lia; lia)) as X.
  cbn [store_ok]. destruct (wview SEGS M (Z_to_bv 64 j)); [reflexivity | exfalso; exact (X eq_refl)].
Qed.

Theorem node_lc_sound : forall T, lc_wf T = true -> lc_spec SEGS (shadow_off A) T ->
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (LCN.node_lc_ref SEGS A nx0 T).
Proof.
  intros T WF SPEC cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  unfold LCN.node_lc_ref in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hall; [|discriminate] end.
  unfold LCN.tests in Hall.
  set (win := LCN.lc_win T) in *.
  set (sp := reg cs 2) in *.
  destruct (split_lit sp) as [spb spk] eqn:Hssp.
  destruct (shadow_of A (kn cs) (eaddz sp (- win)) (ELit win)) as [[shb shk] shn] eqn:Hsh.
  cbn [forallb] in Hall.
  repeat match type of Hall with (?a && ?b)%bool = true => apply andb_prop in Hall; destruct Hall as [?X Hall]; revert X end.
  intros Hwr Hvcells Hcells Hz7 Hw6 Hrng Hal Hregs Hret Hpc. clear Hall.
  apply andb_prop in Hz7 as [Hzero Hzf]. apply andb_prop in Hw6 as [Hwin Hwf].
  apply Z.eqb_eq in Hpc. apply Z.leb_le in Hal.
  (* [comment removed for export] *)
  pose proof WF as WF'. unfold lc_wf in WF'. cbn [forallb] in WF'. fold win in WF'.
  repeat match type of WF' with (?a && ?b)%bool = true => apply andb_prop in WF'; destruct WF' as [?X WF']; revert X end.
  intros WFwr WFpost WFvcells WFcells WFregs WFa1 WFa0 WFw2 WFw1 WFw0. clear WF'.
  apply Z.ltb_lt in WFw0. apply Z.eqb_eq in WFw1. apply Z.ltb_lt in WFw2. apply Z.leb_le in WFa0. apply Z.ltb_lt in WFa1.
  unfold LCN.LC_SPLO in WFw2.
  (* [comment removed for export] *)
  destruct (ret_lit cs) as [r|] eqn:Hrl; [|discriminate]. apply Z.eqb_eq in Hret. subst r.
  destruct (ret_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model (LCN.lc_ret T) HC Hrl) as (R1 & Hrok & Hretr).
  replace (Z_to_bv 5 1) with (1%bv : bv 5) in R1 by (apply bv_eq; reflexivity).
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 2 HC ltac:(lia)) as R2. fold sp in R2.
  replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in R2 by (apply bv_eq; reflexivity).
  set (spw := edenot E sp) in *. set (usp := bv_unsigned spw).
  pose proof (u64_range spw) as Rsp. fold usp in Rsp.
  assert (RR : Forall (fun rv : nat * Z => getr R (Z_to_bv 5 (Z.of_nat (fst rv))) = Z_to_bv 64 (snd rv)) (LCN.lc_regs T)).
  { apply Forall_forall. intros rv Hin.
    pose proof (proj1 (forallb_forall _ _) Hregs rv Hin) as Hb. pose proof (proj1 (forallb_forall _ _) WFregs rv Hin) as Hw.
    cbn beta in Hb, Hw. apply andb_prop in Hw as [W0 W32]. apply Nat.ltb_lt in W0. apply Nat.ltb_lt in W32.
    destruct (reg_lit cs (fst rv)) as [z|] eqn:Hz; [|discriminate]. apply Z.eqb_eq in Hb. subst z.
    exact (proj1 (w_reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model (fst rv) (snd rv) HC ltac:(lia) Hz)). }
  (* [comment removed for export] *)
  destruct (ealign_sound SEGS E M (kn cs) sp HKN) as [_ ALs]. fold spw usp in ALs.
  assert (Husp16 : usp mod 16 = 0) by (change 16 with (2 ^ 4); eapply mod_of_align; [exact ALs | lia]).
  destruct (xlo (kn cs) sp) as [splo|] eqn:Xlo; [|discriminate]. destruct (xhi (kn cs) sp) as [sphi|] eqn:Xhi; [|discriminate].
  apply andb_prop in Hrng as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.leb_le in Hr2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Xlo) as Bsplo. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Xhi) as Bsphi.
  fold spw usp in Bsplo, Bsphi.
  assert (Psp : LCN.LC_SPLO + win <= usp <= LCN.LC_SPHI) by lia.
  unfold LCN.LC_SPLO, LCN.LC_SPHI in Psp.
  (* [comment removed for export] *)
  destruct (rw_lit_sound SEGS SEGS_wr E M (kn cs) spb (spk - win) win HKN WFw0
              ltac:(unfold FN.rw_lit; rewrite Hwin, Hwf; reflexivity)) as (W1st & W1st1 & _ & W1lo & W1hi).
  assert (Husp_eq : usp = estart E (SA spb spk)).
  { pose proof (w_split_lit_denot E sp spb spk Hssp) as D. fold spw in D. apply (f_equal bv_unsigned) in D. fold usp in D.
    unfold estart in W1lo, W1hi |- *. cbn [a_base a_off] in W1lo, W1hi |- *.
    rewrite u_lit64 in D. unfold two64 in D.
    destruct (Z.eq_dec (bv_unsigned (edenot E spb) + spk) (2 ^ 64)) as [EQ|NE].
    - exfalso. rewrite EQ in D. rewrite Z.mod_same in D by lia. lia.
    - rewrite Z.mod_small in D by lia. exact D. }
  assert (Esp : estart E (SA spb (spk - win)) = usp - win).
  { rewrite Husp_eq. unfold estart. cbn [a_base a_off]. lia. }
  assert (PW : forall j, usp - win <= j < usp -> store_ok SEGS M (Z_to_bv 64 j) 1 = true).
  { intros j Hj. replace j with (estart E (SA spb (spk - win)) + (j - (usp - win))) by lia. apply W1st1. lia. }
  (* [comment removed for export] *)
  pose proof SHADOW_ok as SO. unfold shadow_ok in SO.
  destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) shb shk shn HKN HKN Hzero) as (Zb & Zlo & Zhi).
  destruct (flat_x_sound SEGS E M (kn cs) shb shk shn HKN Hzf) as (_ & _ & Zpos). fold (elenZ E shn) in Zpos.
  assert (Dsub : bv_unsigned (edenot E (eaddz sp (- win))) = usp - win).
  { unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. fold spw. rewrite (u_sub_lit spw win) by (fold usp; lia). reflexivity. }
  assert (Hq8 : 0 <= (usp - win) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct (shadow_of_den SEGS A SHADOW_ok E M (kn cs) (eaddz sp (- win)) (ELit win) shb shk shn (elenZ E shn) HKN Hsh Zlo Zhi Zpos
              ltac:(rewrite Dsub; lia)) as (Esh & Lsh).
  rewrite Dsub in Esh. cbn [edenot] in Lsh. rewrite u64_lit in Lsh by lia.
  assert (Hdiv : (usp - win) / 8 + win / 8 = usp / 8).
  { clear - WFw1 Husp16 WFw0 Psp.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (PZ : forall j, shadow_off A + (usp - win) / 8 <= j < shadow_off A + usp / 8 -> M (Z_to_bv 64 j) = Some (Z_to_bv 8 0)).
  { intros j Hj. replace j with (estart E (SA shb shk) + (j - estart E (SA shb shk))) by lia. apply Zb. rewrite Esh, Lsh. lia. }
  (* [comment removed for export] *)
  assert (RD : Forall (rd_ok SEGS M) (LCN.lc_cells T)).
  { apply Forall_forall. intros [[a w] v] Hin.
    pose proof (proj1 (forallb_forall _ _) Hcells _ Hin) as Hb. pose proof (proj1 (forallb_forall _ _) WFcells _ Hin) as Hw.
    cbn beta iota in Hb. destruct (cell_wf_inv a w v Hw) as (C1 & C2 & C3 & C4).
    eapply (kreadZ_rd SEGS E M (kn cs) a w v HKN); try lia. exact Hb. }
  assert (RDV : Forall (fun a : Z => exists x : word, rdn SEGS M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 x)) (LCN.lc_vcells T)).
  { apply Forall_forall. intros a Hin.
    pose proof (proj1 (forallb_forall _ _) Hvcells _ Hin) as Hb. cbn beta in Hb.
    destruct (FN.cell_expr SEGS (kn cs) (ELit 0) a) as [e|] eqn:He; [|discriminate].
    destruct (cell_expr_sound SEGS E M (kn cs) (ELit 0) a e HKN He) as (Hrd & _ & _). rewrite estart_lit0 in Hrd.
    exists (edenot E e). exact Hrd. }
  (* [comment removed for export] *)
  assert (WR : Forall (fun r : Z * Z => forall j, in_wr j r -> store_ok SEGS M (Z_to_bv 64 j) 1 = true) (LCN.lc_wr T)).
  { apply Forall_forall. intros [a n] Hin j Hj. unfold in_wr in Hj. cbn [fst snd] in Hj.
    pose proof (proj1 (forallb_forall _ _) Hwr _ Hin) as Hb. pose proof (proj1 (forallb_forall _ _) WFwr _ Hin) as Hw.
    cbn beta in Hb, Hw. cbn [fst snd] in Hb, Hw.
    apply andb_prop in Hw as [Hw W3]. apply andb_prop in Hw as [W1 W2]. apply Z.leb_le in W1. apply Z.ltb_lt in W2. apply Z.ltb_lt in W3.
    destruct (rw_lit_sound SEGS SEGS_wr E M (kn cs) (ELit 0) a n HKN W2 ltac:(unfold FN.rw_lit; exact Hb)) as (_ & St1 & _ & _ & _).
    rewrite estart_lit0 in St1. replace j with (a + (j - a)) by lia. apply St1. lia. }
  (* [comment removed for export] *)
  destruct (SPEC M (seg_rom SEGS) R usp ltac:(rewrite R2; symmetry; apply Z_to_bv_bv_unsigned) Husp16
              ltac:(unfold LCN.LC_SPLO, LCN.LC_SPHI; fold win; lia) R1 RR RD RDV PW PZ WR)
    as (regs' & mem' & MS & KEPT & A0 & Hgrows & Hout & POST).
  fold win in Hout.
  (* [comment removed for export] *)
  eapply (call_node_sound SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
            cs cs' E R FULL model TT (LCN.lc_ret T) (Some (ELit (LCN.lc_a0 T))) _ regs' mem' HC Hn).
  - rewrite Hpc. exact MS.
  - exact KEPT.
  - cbn [edenot]. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). exact A0.
  - (* [comment removed for export] *)
    apply Forall_app. split.
    + apply Forall_forall. intros K HK. apply in_map_iff in HK as ([[a w] v] & <- & Hin).
      pose proof (proj1 (Forall_forall _ _) POST _ Hin) as Hrd. pose proof (proj1 (forallb_forall _ _) WFpost _ Hin) as Hw.
      destruct (cell_wf_inv a w v Hw) as (C1 & C2 & C3 & C4). unfold LCN.post_fact.
      eapply (kword_intro SEGS E mem' (ELit 0) (Z_to_bv 64 0) a w (ELit v) (Z_to_bv 64 v)); try reflexivity; try lia;
        rewrite ?u64_lit by lia; try lia.
      rewrite Z.add_0_l. exact Hrd.
    + apply (havocs_sound SEGS E (LCN.lc_ws T spb spk) M mem' (kn cs) HKN Hgrows).
      intros x Hx. unfold LCN.lc_ws in Hx. fold win in Hx. cbn [forallb] in Hx. apply andb_prop in Hx as [N1 Hx].
      set (ux := bv_unsigned x) in *.
      apply Hout.
      * unfold inr in N1. rewrite Esp in N1.
        replace (elenZ E (ELit win)) with win in N1 by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
        fold ux in N1. intros Hc. destruct (Z.leb_spec (usp - win) ux); destruct (Z.ltb_spec ux (usp - win + win)); cbn in N1; try discriminate; lia.
      * apply Forall_forall. intros [a n] Hin Hc. unfold in_wr in Hc. cbn [fst snd] in Hc. fold ux in Hc.
        pose proof (proj1 (forallb_forall _ _) WFwr _ Hin) as Hw. cbn beta in Hw. cbn [fst snd] in Hw.
        apply andb_prop in Hw as [Hw W3]. apply andb_prop in Hw as [W1 W2]. apply Z.leb_le in W1. apply Z.ltb_lt in W2. apply Z.ltb_lt in W3.
        rewrite forallb_map_lc in Hx.
        pose proof (proj1 (forallb_forall _ _) Hx _ Hin) as Hb. cbn beta in Hb. cbn [fst snd] in Hb.
        unfold inr in Hb. rewrite estart_lit0 in Hb.
        replace (elenZ E (ELit n)) with n in Hb by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
        fold ux in Hb. destruct (Z.leb_spec a ux); destruct (Z.ltb_spec ux (a + n)); cbn in Hb; try discriminate; lia.
  - intros E' R' FULL' model' Hag HC' Hfs. exact (Hk E' R' FULL' model' Hag HC' Hfs).
Qed.

(* [comment removed for export] *)
Theorem lc_xn_sound : forall TS,
  Forall (fun T => lc_wf T = true /\ lc_spec SEGS (shadow_off A) T) TS ->
  ext_stmt SEGS A nx0 LIMIT (LCN.xn SEGS A nx0 TS) SINV argH FS0.
Proof.
  intros TS HTS id args. unfold LCN.xn. destruct (Nat.eqb id 122).
  - destruct args as [|[i| | | | | | |] [|? ?]]; try (intros cs cs' E R FULL model TT _ _ H; discriminate H).
    destruct (nth_error TS (Z.to_nat i)) as [T|] eqn:HT; [|intros cs cs' E R FULL model TT _ _ H; discriminate H].
    pose proof (proj1 (Forall_forall _ _) HTS T (nth_error_In _ _ HT)) as [WF SPEC].
    intros cs cs' E R FULL model TT HC Hpre Hn Hk. rewrite LCN.node_lc_eq in Hn.
    exact (node_lc_sound T WF SPEC cs cs' E R FULL model TT HC Hpre Hn Hk).
  - intros cs cs' E R FULL model TT _ _ H. discriminate H.
Qed.
End Sound.
