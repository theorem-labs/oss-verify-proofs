(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStepTac BHoare BWalkTac BStoreOk BLibAtomic.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BFrame BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BSymAux.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BAgentLib BSumWalkTac BsCarryKeep.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Section Kit.
  Context {fx : DFP}.
Variable segs : list Segment.

Lemma pc_add4 : forall pc : Z, (0 <= pc)%Z -> v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4).
Proof.
  intros pc H. apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma cas8_msteps : forall (pc : Z) (rd rs1 rexp rnew rt : reg) (imm : bv 13) aq rl aq' rl' (w0 w1 w2 : bv 32)
                           regs mem rom (v : word),
  fetch_word segs (Z_to_bv 64 pc) = Some w0 -> is_ecall w0 = false -> decode_any w0 = Some (Lr AD aq rl rd rs1, 4%Z) ->
  fetch_word segs (Z_to_bv 64 (pc + 4)) = Some w1 -> is_ecall w1 = false ->
  decode_any w1 = Some (Branch BC_NE rd rexp imm, 4%Z) ->
  fetch_word segs (Z_to_bv 64 (pc + 8)) = Some w2 -> is_ecall w2 = false ->
  decode_any w2 = Some (Sc AD aq' rl' rt rs1 rnew, 4%Z) ->
  rd <> 0 -> rt <> 0 -> rd <> rs1 -> rd <> rnew -> rd <> rexp -> (0 <= pc)%Z ->
  getr regs rexp = v -> (bv_unsigned (getr regs rs1) mod 8 = 0)%Z ->
  rdn segs mem (getr regs rs1) 8%nat = Some (word_to_le_bytes 8 v) ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 8%nat = true ->
  msteps segs (mkst regs (Z_to_bv 64 pc) mem rom)
              (mkst (regupd (regupd regs rd v) rt (Z_to_bv 64 0)) (Z_to_bv 64 (pc + 12))
                    (wbytes mem (getr regs rs1) (word_to_le_bytes 8 (getr regs rnew))) rom).
Proof.
  intros pc rd rs1 rexp rnew rt imm aq rl aq' rl' w0 w1 w2 regs mem rom v F0 E0 D0 F1 E1 D1 F2 E2 D2
         Nrd Nrt Nrs1 Nrnew Nrexp Hpc Rexp Hal Mlock Sok.
  assert (Hrd0 : bv_eqb rd 0 = false) by (apply bv_eqb_neq; exact Nrd).
  assert (Hrt0 : bv_eqb rt 0 = false) by (apply bv_eqb_neq; exact Nrt).
  assert (G1 : getr (regupd regs rd v) rs1 = getr regs rs1) by (apply getr_other; auto).
  assert (G2 : getr (regupd regs rd v) rnew = getr regs rnew) by (apply getr_other; auto).
  assert (G3 : getr (regupd regs rd v) rexp = v) by (rewrite getr_other by auto; exact Rexp).
  assert (G4 : getr (regupd regs rd v) rd = v) by (apply getr_same; exact Nrd).
  eapply mst_step; [reflexivity
    | eapply step_lr_d with (bs := word_to_le_bytes 8 v) (v := v);
      [ exact F0 | exact E0 | exact D0 | exact Hal | exact Mlock | apply bytes_le_to_Z_8 ]
    | ].
  rewrite Hrd0.
  eapply mst_step; [reflexivity
    | eapply step_bne_ft_r; [ | exact E1 | exact D1 | ] | ].
  { rewrite pc_add4 by exact Hpc. exact F1. }
  { rewrite G4, G3. apply c_eq_refl. }
  eapply mst_step; [reflexivity
    | eapply step_sc_d_ok; [ | exact E2 | exact D2 | | | ] | ].
  { rewrite !pc_add4 by lia. replace (pc + 4 + 4)%Z with (pc + 8)%Z by lia. exact F2. }
  { rewrite G1. exact Hal. }
  { rewrite G1. reflexivity. }
  { rewrite G1. exact Sok. }
  rewrite Hrt0, G1, G2.
  rewrite !pc_add4 by lia. replace (pc + 4 + 4 + 4)%Z with (pc + 12)%Z by lia. apply mst_refl.
Qed.

Definition lw_z (c : Z) : Z := if (c <? 2 ^ 31)%Z then c else (c + 2 ^ 64 - 2 ^ 32)%Z.

Lemma v_lw_lit : forall c : Z, (0 <= c < 2 ^ 32)%Z -> v_lw (Z_to_bv 64 c) = Z_to_bv 64 (lw_z c).
Proof.
  intros c Hc. unfold v_lw, lw_z. apply bv_eq. rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 c) by (unfold bv_modulus; cbn; lia).
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn.
  change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  destruct (Z.ltb_spec c (2 ^ 31)) as [H|H].
  - rewrite (Z.mod_small (c + 2 ^ 31) (2 ^ 32)) by lia. replace (c + 2 ^ 31 - 2 ^ 31)%Z with c by lia. reflexivity.
  - replace (c + 2 ^ 31)%Z with ((c - 2 ^ 31) + 1 * 2 ^ 32)%Z by lia.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (c - 2 ^ 31) (2 ^ 32)) by lia.
    replace (c - 2 ^ 31 - 2 ^ 31)%Z with ((c + 2 ^ 64 - 2 ^ 32) + (-1) * 2 ^ 64)%Z by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma cas4_msteps : forall (pc : Z) (rd rs1 rexp rnew rt : reg) (imm : bv 13) aq rl aq' rl' (w0 w1 w2 : bv 32)
                           regs mem rom (c : Z),
  fetch_word segs (Z_to_bv 64 pc) = Some w0 -> is_ecall w0 = false -> decode_any w0 = Some (Lr AW aq rl rd rs1, 4%Z) ->
  fetch_word segs (Z_to_bv 64 (pc + 4)) = Some w1 -> is_ecall w1 = false ->
  decode_any w1 = Some (Branch BC_NE rd rexp imm, 4%Z) ->
  fetch_word segs (Z_to_bv 64 (pc + 8)) = Some w2 -> is_ecall w2 = false ->
  decode_any w2 = Some (Sc AW aq' rl' rt rs1 rnew, 4%Z) ->
  rd <> 0 -> rt <> 0 -> rd <> rs1 -> rd <> rnew -> rd <> rexp -> (0 <= pc)%Z -> (0 <= c < 2 ^ 32)%Z ->
  getr regs rexp = Z_to_bv 64 (lw_z c) -> (bv_unsigned (getr regs rs1) mod 4 = 0)%Z ->
  rdn segs mem (getr regs rs1) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 c)) ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 4%nat = true ->
  msteps segs (mkst regs (Z_to_bv 64 pc) mem rom)
              (mkst (regupd (regupd regs rd (Z_to_bv 64 (lw_z c))) rt (Z_to_bv 64 0)) (Z_to_bv 64 (pc + 12))
                    (wbytes mem (getr regs rs1) (word_to_le_bytes 4 (getr regs rnew))) rom).
Proof.
  intros pc rd rs1 rexp rnew rt imm aq rl aq' rl' w0 w1 w2 regs mem rom c F0 E0 D0 F1 E1 D1 F2 E2 D2
         Nrd Nrt Nrs1 Nrnew Nrexp Hpc Hc Rexp Hal Mlock Sok.
  set (v := Z_to_bv 64 (lw_z c)) in *.
  assert (Hrd0 : bv_eqb rd 0 = false) by (apply bv_eqb_neq; exact Nrd).
  assert (Hrt0 : bv_eqb rt 0 = false) by (apply bv_eqb_neq; exact Nrt).
  assert (G1 : getr (regupd regs rd v) rs1 = getr regs rs1) by (apply getr_other; auto).
  assert (G2 : getr (regupd regs rd v) rnew = getr regs rnew) by (apply getr_other; auto).
  assert (G3 : getr (regupd regs rd v) rexp = v) by (rewrite getr_other by auto; exact Rexp).
  assert (G4 : getr (regupd regs rd v) rd = v) by (apply getr_same; exact Nrd).
  assert (Hu : bv_unsigned (Z_to_bv 64 c) = c) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia).
  eapply mst_step; [reflexivity
    | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 c)) (v := Z_to_bv 64 c);
      [ exact F0 | exact E0 | exact D0 | exact Hal | exact Mlock | apply bytes_le_to_Z_4; lia ]
    | ].
  rewrite Hrd0, (v_lw_lit c Hc). fold v.
  eapply mst_step; [reflexivity
    | eapply step_bne_ft_r; [ | exact E1 | exact D1 | ] | ].
  { rewrite pc_add4 by exact Hpc. exact F1. }
  { rewrite G4, G3. apply c_eq_refl. }
  eapply mst_step; [reflexivity
    | eapply step_sc_w_ok; [ | exact E2 | exact D2 | | | ] | ].
  { rewrite !pc_add4 by lia. replace (pc + 4 + 4)%Z with (pc + 8)%Z by lia. exact F2. }
  { rewrite G1. exact Hal. }
  { rewrite G1. reflexivity. }
  { rewrite G1. exact Sok. }
  rewrite Hrt0, G1, G2.
  rewrite !pc_add4 by lia. replace (pc + 4 + 4 + 4)%Z with (pc + 12)%Z by lia. apply mst_refl.
Qed.

Definition xscr0 : scripts := SCR [] [] [].

Inductive xseg : Type :=
| XRun (fuel : N) (stops : list Z) (dirs : list bool) (keep : kentry -> bool)
| XCas (w : nat).

Record xst : Type := XS { xs_pc : Z; xs_sr : list expr; xs_kn : list kentry }.

Definition dec_at (pc : Z) : option (instr * bv 32) :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w => if is_ecall w then None else
              match decode_any w with Some (i, sz) => if Z.eqb sz 4 then Some (i, w) else None | None => None end
  | None => None
  end.

Lemma dec_at_sound : forall pc i w, dec_at pc = Some (i, w) ->
  fetch_word segs (Z_to_bv 64 pc) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z).
Proof.
  intros pc i w H. unfold dec_at in H.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w'|] eqn:F; [|discriminate].
  destruct (is_ecall w') eqn:E; [discriminate|].
  destruct (decode_any w') as [[i' sz]|] eqn:D; [|discriminate].
  destruct (Z.eqb_spec sz 4) as [->|]; [|discriminate]. injection H as <- <-. auto.
Qed.

Definition rneq (a b : reg) : bool := negb (bv_eqb a b).

Lemma rneq_sound : forall a b, rneq a b = true -> a <> b.
Proof. intros a b H E. subst b. unfold rneq in H. rewrite bv_eqb_refl in H. discriminate. Qed.

Definition aligned_chk (kn : list kentry) (b : expr) (k : Z) (w : Z) : bool :=
  match b with
  | ELit z => Z.eqb ((z + k) mod w)%Z 0
  | _ => existsb (fun K => match K with
                          | KAlign e m => (expr_eqb e b && Z.eqb (m mod w) 0 && Z.eqb (k mod w) 0 && Z.ltb 0 m)%bool
                          | _ => false end) kn
  end.

Lemma mod_2_64_dvd : forall x w, (w = 4 \/ w = 8)%Z -> ((x mod 2 ^ 64) mod w = x mod w)%Z.
Proof.
  intros x w Hw. apply Z.mod_mod_divide.
  destruct Hw as [->| ->]; [exists (2 ^ 62)%Z | exists (2 ^ 61)%Z]; reflexivity.
Qed.

Lemma split_lit_denot_x : forall E e b k, split_lit e = (b, k) -> edenot E e = adenot E (SA b k).
Proof.
  intros E e b k H. unfold adenot, v_addi. cbn [a_base a_off].
  assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
  { intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
  unfold split_lit in H.
  destruct e; try (injection H as <- <-; apply G).
  - injection H as <- <-. cbn [edenot]. rewrite u64_lit by lia. rewrite Z.add_0_l. reflexivity.
  - lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
    lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
    injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

Lemma aligned_chk_sound : forall E M kn b k (w : nat),
  (w = 4 \/ w = 8)%nat -> aligned_chk kn b k (Z.of_nat w) = true -> know_ok segs E M kn ->
  (bv_unsigned (adenot E (SA b k)) mod Z.of_nat w = 0)%Z.
Proof.
  intros E M kn b k w Hw Hc HK.
  assert (Hw' : (Z.of_nat w = 4 \/ Z.of_nat w = 8)%Z) by lia.
  unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z_to_bv_unsigned, bv_wrap64_mod, mod_2_64_dvd by exact Hw'.
  unfold aligned_chk in Hc. destruct b as [z| | | | | | |];
    try (apply existsb_exists in Hc as (K & HIn & HKc);
         destruct K; try discriminate;
         repeat match type of HKc with (_ && _)%bool = true => apply andb_prop in HKc as [HKc ?] end;
         apply expr_eqb_eq in HKc; subst;
         pose proof (proj1 (Forall_forall _ _) HK _ HIn) as (Hm0 & Hm);
         repeat match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H end;
         match goal with H : (0 <? _)%Z = true |- _ => apply Z.ltb_lt in H end;
         rewrite Z.add_mod by lia;
         match goal with H : (?m mod _ = 0)%Z |- context [ (bv_unsigned ?x mod _)%Z ] =>
           assert (Hx : (bv_unsigned x mod Z.of_nat w = 0)%Z)
             by (apply Z.mod_divide in H; [| lia]; destruct H as [q Hq];
                 apply Z.mod_divide in Hm; [| lia]; destruct Hm as [p Hp];
                 apply Z.mod_divide; [lia|]; exists (p * q)%Z; lia) end;
         rewrite Hx; match goal with H : (k mod _ = 0)%Z |- _ => rewrite H end; reflexivity).

  apply Z.eqb_eq in Hc. cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite Z.add_mod by lia. rewrite mod_2_64_dvd by exact Hw'. rewrite <- Z.add_mod by lia. exact Hc.
Qed.

Definition kwr_chk (kn : list kentry) (b : expr) (k : Z) (w : nat) : bool := existsb (is_kwr_cov b k (Z.of_nat w)) kn.

Lemma kwr_chk_sound : forall E M kn b k (w : nat),
  (1 <= w)%nat -> kwr_chk kn b k w = true -> know_ok segs E M kn ->
  flat E (SA b k) (Z.of_nat w) /\ RiscvSemantics.store_ok segs M (adenot E (SA b k)) w = true.
Proof.
  intros E M kn b k w Hw1 Hc HK. unfold kwr_chk in Hc. apply existsb_exists in Hc as (K & HIn & HKc).
  destruct K as [| | | | | |[c kk] len|]; try discriminate. unfold is_kwr_cov in HKc.
  apply andb_prop in HKc as [HKc H2]. apply andb_prop in HKc as [H0 H1].
  apply expr_eqb_eq in H0. subst c. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HK _ HIn) as (Hfl & Hst). cbn [kentry_ok] in *.
  unfold flat, estart in Hfl. cbn [a_base a_off] in Hfl.
  split.
  - unfold flat, estart. cbn [a_base a_off]. lia.
  - specialize (Hst (k - kk)%Z w ltac:(lia) ltac:(lia)).
    unfold estart in Hst. cbn [a_base a_off] in Hst.
    replace (bv_unsigned (edenot E b) + kk + (k - kk))%Z with (bv_unsigned (edenot E b) + k)%Z in Hst by lia.
    unfold adenot, v_addi. cbn [a_base a_off]. exact Hst.
Qed.

Definition xcas_tail (w : nat) (pc : Z) (sr : list expr) (kn : list kentry) (aw aw' : awidth) (rd rs1 rexp rt rnew : reg)
  : option (xst * sentry) :=
  let '(b, k) := split_lit (sr_get sr rs1) in
  match aw, aw', w with
  | AD, AD, 8%nat =>
      match kread segs kn b k 8 with
      | Some v =>
          if (expr_eqb v (sr_get sr rexp) && aligned_chk kn b k 8 && kwr_chk kn b k 8)%bool then
            Some (XS (pc + 12) (sr_upd (sr_upd sr (ridx rd) v) (ridx rt) (ELit 0)) kn, SE (SA b k) 8 (sr_get sr rnew))
          else None
      | None => None
      end
  | AW, AW, 4%nat =>
      match kread segs kn b k 4 with
      | Some (ELit c) =>
          if ((0 <=? c) && (c <? 2 ^ 32) && expr_eqb (sr_get sr rexp) (ELit (lw_z c))
              && aligned_chk kn b k 4 && kwr_chk kn b k 4)%Z%bool then
            Some (XS (pc + 12) (sr_upd (sr_upd sr (ridx rd) (ELit (lw_z c))) (ridx rt) (ELit 0)) kn,
                  SE (SA b k) 4 (sr_get sr rnew))
          else None
      | _ => None
      end
  | _, _, _ => None
  end.

Definition xcas (w : nat) (st : xst) : option (xst * sentry) :=
  let pc := xs_pc st in let sr := xs_sr st in let kn := xs_kn st in
  match dec_at pc with
  | Some (Lr aw aq rl rd rs1, _) =>
    match dec_at (pc + 4) with
    | Some (Branch BC_NE rd' rexp imm, _) =>
      match dec_at (pc + 8) with
      | Some (Sc aw' aq' rl' rt rs1' rnew, _) =>
          if (bv_eqb rd rd' && bv_eqb rs1 rs1' && rneq rd 0 && rneq rt 0 && rneq rd rs1 && rneq rd rnew && rneq rd rexp
              && Z.leb 0 pc)%bool
          then xcas_tail w pc sr kn aw aw' rd rs1 rexp rt rnew
          else None
      | _ => None
      end
    | _ => None
    end
  | _ => None
  end.

Lemma bv_eqb_true : forall (a b : reg), bv_eqb a b = true -> a = b.
Proof. intros a b H. apply bv_eq. unfold bv_eqb in H. apply Z.eqb_eq in H. exact H. Qed.

Lemma xcas_inv : forall w st st' e, xcas w st = Some (st', e) ->
  exists aw aq rl rd rs1 rexp (imm : bv 13) aw' aq' rl' rt rnew w0 w1 w2,
    dec_at (xs_pc st) = Some (Lr aw aq rl rd rs1, w0) /\ dec_at (xs_pc st + 4) = Some (Branch BC_NE rd rexp imm, w1)
    /\ dec_at (xs_pc st + 8) = Some (Sc aw' aq' rl' rt rs1 rnew, w2)
    /\ rd <> 0 /\ rt <> 0 /\ rd <> rs1 /\ rd <> rnew /\ rd <> rexp /\ (0 <= xs_pc st)%Z
    /\ xcas_tail w (xs_pc st) (xs_sr st) (xs_kn st) aw aw' rd rs1 rexp rt rnew = Some (st', e).
Proof.
  intros w [pc sr kn] st' e H. unfold xcas in H. cbn [xs_pc xs_sr xs_kn] in *.
  destruct (dec_at pc) as [[i0 x0]|] eqn:D0; [|discriminate]. destruct i0; try discriminate.
  destruct (dec_at (pc + 4)) as [[i1 x1]|] eqn:D1; [|discriminate]. destruct i1; try discriminate. destruct c; try discriminate.
  destruct (dec_at (pc + 8)) as [[i2 x2]|] eqn:D2; [|discriminate]. destruct i2; try discriminate.
  lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?] end.
  repeat match goal with Hn : rneq _ _ = true |- _ => apply rneq_sound in Hn end.
  repeat match goal with Hb : bv_eqb _ _ = true |- _ => apply bv_eqb_true in Hb; subst end.
  match goal with Hp : (0 <=? pc)%Z = true |- _ => apply Z.leb_le in Hp end.
  do 15 eexists. repeat split; eassumption.
Qed.

Lemma xcas_sound : forall w st st' e E M R rom,
  xcas w st = Some (st', e) ->
  regs_ok E (xs_sr st) R -> know_ok segs E M (xs_kn st) ->
  exists R', msteps segs (mkst R (Z_to_bv 64 (xs_pc st)) M rom) (mkst R' (Z_to_bv 64 (xs_pc st')) (mem_denot E M [e]) rom)
    /\ regs_ok E (xs_sr st') R' /\ log_flat E [e] /\ xs_kn st' = xs_kn st.
Proof.
  intros w [pc sr kn] st' e E M R rom H HR HK.
  destruct (xcas_inv w _ _ _ H) as (aw & aq & rl & rd & rs1 & rexp & imm & aw' & aq' & rl' & rt & rnew & w0 & w1 & w2 &
                                     D0 & D1 & D2 & Nrd & Nrt & Nrs1 & Nrnew & Nrexp & Hpc & H').
  clear H. cbn [xs_pc xs_sr xs_kn] in *. rename H' into H.
  apply dec_at_sound in D0 as (F0 & E0 & DD0). apply dec_at_sound in D1 as (F1 & E1 & DD1). apply dec_at_sound in D2 as (F2 & E2 & DD2).
  unfold xcas_tail in H.
  destruct (split_lit (sr_get sr rs1)) as [b k] eqn:Hsl.
  assert (Ha : getr R rs1 = adenot E (SA b k)) by (rewrite (HR rs1); apply split_lit_denot_x; exact Hsl).
  destruct aw, aw'; try discriminate.
  -
    destruct w as [|[|[|[|[|]]]]]; try discriminate.
    destruct (kread segs kn b k 4) as [[c| | | | | | |]|] eqn:Hkr; try discriminate.
    lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc2; [|discriminate] end.
    injection H as <- <-. cbn [xs_pc xs_sr xs_kn].
    repeat match type of Hc2 with (_ && _)%bool = true => apply andb_prop in Hc2 as [Hc2 ?] end.
    apply Z.leb_le in Hc2. match goal with H : (c <? 2 ^ 32)%Z = true |- _ => apply Z.ltb_lt in H end.
    match goal with H : expr_eqb _ (ELit (lw_z c)) = true |- _ => apply expr_eqb_eq in H; rename H into Hx end.
    match goal with H : kwr_chk kn b k 4 = true |- _ => destruct (kwr_chk_sound E M kn b k 4 ltac:(lia) H HK) as [Hfl Hsok] end.
    match goal with H : aligned_chk kn b k _ = true |- _ => pose proof (aligned_chk_sound E M kn b k 4 ltac:(lia) H HK) as Hal end.
    pose proof (kread_rdn segs E M kn b k 4 (ELit c) HK Hkr ltac:(lia) ltac:(lia) Hfl) as Hrd. rewrite edenot_lit in Hrd.
    assert (HMd : mem_denot E M [SE (SA b k) 4 (sr_get sr rnew)] = wbytes M (getr R rs1) (word_to_le_bytes 4 (getr R rnew)))
      by (cbn [mem_denot]; rewrite Ha, (HR rnew); reflexivity).
    rewrite HMd. eexists. split; [| split; [| split; [| reflexivity]]].
    + assert (Hrexp : getr R rexp = Z_to_bv 64 (lw_z c)) by (rewrite (HR rexp), Hx; apply edenot_lit).
      change (Z.of_nat 4) with 4%Z in Hal. rewrite <- Ha in Hal, Hrd, Hsok.
      eapply (cas4_msteps pc); try eassumption; lia.
    + apply regs_ok_set; [apply regs_ok_set; [exact HR | assumption | apply edenot_lit] | assumption | apply edenot_lit].
    + cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
  -
    destruct w as [|[|[|[|[|[|[|[|[|]]]]]]]]]; try discriminate.
    destruct (kread segs kn b k 8) as [v|] eqn:Hkr; [|discriminate].
    lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc2; [|discriminate] end.
    injection H as <- <-. cbn [xs_pc xs_sr xs_kn].
    repeat match type of Hc2 with (_ && _)%bool = true => apply andb_prop in Hc2 as [Hc2 ?] end.
    apply expr_eqb_eq in Hc2.
    match goal with H : kwr_chk kn b k 8 = true |- _ => destruct (kwr_chk_sound E M kn b k 8 ltac:(lia) H HK) as [Hfl Hsok] end.
    match goal with H : aligned_chk kn b k _ = true |- _ => pose proof (aligned_chk_sound E M kn b k 8 ltac:(lia) H HK) as Hal end.
    pose proof (kread_rdn segs E M kn b k 8 v HK Hkr ltac:(lia) ltac:(lia) Hfl) as Hrd.
    assert (HMd : mem_denot E M [SE (SA b k) 8 (sr_get sr rnew)] = wbytes M (getr R rs1) (word_to_le_bytes 8 (getr R rnew)))
      by (cbn [mem_denot]; rewrite Ha, (HR rnew); reflexivity).
    rewrite HMd. eexists. split; [| split; [| split; [| reflexivity]]].
    + assert (Hrexp : getr R rexp = edenot E v) by (rewrite (HR rexp), <- Hc2; reflexivity).
      change (Z.of_nat 8) with 8%Z in Hal. rewrite <- Ha in Hal, Hrd, Hsok.
      eapply (cas8_msteps pc); try eassumption; lia.
    + apply regs_ok_set; [apply regs_ok_set; [exact HR | assumption | reflexivity] | assumption | apply edenot_lit].
    + cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact I].
Qed.

Lemma lxor_ones64 : forall a : Z, (0 <= a < 2 ^ 64)%Z -> Z.lxor a (2 ^ 64 - 1) = (2 ^ 64 - 1 - a)%Z.
Proof.
  intros a Ha.
  assert (E1 : Z.lxor a (2 ^ 64 - 1) = Z.land (Z.lnot a) (Z.ones 64)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by exact Hi.
    replace (2 ^ 64 - 1)%Z with (Z.ones 64) by (rewrite Z.ones_equiv; reflexivity).
    destruct (Z.lt_ge_cases i 64) as [Hlt|Hge].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit a i); reflexivity.
    - rewrite Z.ones_spec_high by lia.
      replace a with (a mod 2 ^ 64)%Z by (apply Z.mod_small; exact Ha).
      rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite E1, Z.land_ones by lia. unfold Z.lnot.
  symmetry. apply Z.mod_unique with (q := (-1)%Z); [left; lia | lia].
Qed.

Definition xrange (kn : list kentry) (e : expr) : option (Z * Z) :=
  match e with
  | EAlu ALU_XOR x (ELit m) =>
      if Z.eqb (m mod 2 ^ 64) (2 ^ 64 - 1) then
        match erange kn x with Some (lo, hi) => Some ((2 ^ 64 - 1 - hi)%Z, (2 ^ 64 - 1 - lo)%Z) | None => None end
      else erange kn e
  | _ => erange kn e
  end.

Lemma xrange_sound : forall E M kn e lo hi, know_ok segs E M kn -> xrange kn e = Some (lo, hi) ->
  (lo <= bv_unsigned (edenot E e) <= hi)%Z.
Proof.
  intros E M kn e lo hi HK H. unfold xrange in H.
  destruct e as [| |op x y| | | | |]; try (eapply erange_sound; eassumption).
  destruct op; try (eapply erange_sound; eassumption).
  destruct y as [m| | | | | | |]; try (eapply erange_sound; eassumption).
  destruct (Z.eqb_spec (m mod 2 ^ 64) (2 ^ 64 - 1)) as [Hm|Hm]; [|eapply erange_sound; eassumption].
  destruct (erange kn x) as [[xl xh]|] eqn:Hx; [|discriminate]. injection H as <- <-.
  pose proof (erange_sound segs E M kn x xl xh HK Hx) as Hr.
  cbn [edenot]. rewrite u_xor64. rewrite Z_to_bv_unsigned, bv_wrap64_mod, Hm.
  rewrite lxor_ones64 by apply u64_range. lia.
Qed.

Definition scbr_ok (kn : list kentry) (sc : sidecond) : bool :=
  match sc with
  | SCBr t c a b =>
      match xrange kn a, xrange kn b with
      | Some (al, ah), Some (bl, bh) =>
          match range_branch c al ah bl bh with Some t' => Bool.eqb t t' | None => false end
      | _, _ => false
      end
  | _ => false
  end.

Definition scs_chk (kn : list kentry) (scs : list sidecond) : bool := forallb (scbr_ok kn) scs.

Lemma scs_chk_sound : forall E M M' kn scs, know_ok segs E M kn -> scs_chk kn scs = true -> scs_denot segs M' E scs.
Proof.
  intros E M M' kn scs HK H. unfold scs_chk in H. unfold scs_denot. apply Forall_forall. intros sc Hin.
  pose proof (proj1 (forallb_forall _ _) H sc Hin) as Hs. clear H Hin.
  destruct sc as [t c a b| | | | | |]; try discriminate. cbn [scbr_ok] in Hs. cbn [sc_denot].
  destruct (xrange kn a) as [[al ah]|] eqn:Ha; [|discriminate].
  destruct (xrange kn b) as [[bl bh]|] eqn:Hb; [|discriminate].
  destruct (range_branch c al ah bl bh) as [t'|] eqn:Hrb; [|discriminate].
  apply Bool.eqb_prop in Hs. subst t'.
  eapply range_branch_sound; [eapply xrange_sound; eassumption | eapply xrange_sound; eassumption | exact Hrb].
Qed.

Fixpoint xchain (rs : list sregion) (nv : nat) (sg : list xseg) (st : xst) : option xst :=
  match sg with
  | [] => Some st
  | XRun fuel stops dirs keep :: rest =>
      match sym_exec segs (N.to_nat fuel) true stops (SCR dirs [] []) (SS (xs_pc st) (xs_sr st) [] (xs_kn st) nv) [] with
      | (ss', scs, _) =>
          if (scs_chk (xs_kn st) scs && log_covered rs (s_log ss'))%bool then
            match carry_keep keep (s_log ss') (xs_kn st) [] with
            | (kn', [], _) => xchain rs nv rest (XS (s_pc ss') (s_regs ss') kn')
            | _ => None
            end
          else None
      end
  | XCas w :: rest =>
      match xcas w st with
      | Some (st1, e) =>
          if log_covered rs [e] then
            match carry [e] (xs_kn st) [] with
            | (kn', [], _) => xchain rs nv rest (XS (xs_pc st1) (xs_sr st1) kn')
            | _ => None
            end
          else None
      | None => None
      end
  end.

Theorem xchain_sound : forall rs nv sg st st' E M R rom,
  xchain rs nv sg st = Some st' ->
  regions_flat E rs -> regs_ok E (xs_sr st) R -> know_ok segs E M (xs_kn st) ->
  exists R' M', msteps segs (mkst R (Z_to_bv 64 (xs_pc st)) M rom) (mkst R' (Z_to_bv 64 (xs_pc st')) M' rom)
     /\ regs_ok E (xs_sr st') R' /\ know_ok segs E M' (xs_kn st') /\ frame_mod M M' (map (rdenot E) rs).
Proof.
  intros rs nv sg. induction sg as [|sg0 rest IH]; intros st st' E M R rom H RF HR HK.
  - cbn [xchain] in H. injection H as <-. exists R, M. split; [apply mst_refl|]. split; [exact HR|]. split; [exact HK|].
    apply frame_mod_refl.
  - destruct sg0 as [fuel stops dirs keep | w]; cbn [xchain] in H.
    + destruct (sym_exec segs (N.to_nat fuel) true stops (SCR dirs [] []) (SS (xs_pc st) (xs_sr st) [] (xs_kn st) nv) []) as [[ss' scs] scr'] eqn:Hex.
      destruct (scs_chk (xs_kn st) scs) eqn:Hchk; [|discriminate].
      destruct (log_covered rs (s_log ss')) eqn:Hcov; [|discriminate].
      cbn [andb] in H.
      destruct (carry_keep keep (s_log ss') (xs_kn st) []) as [[kn' scs2] hs2] eqn:Hc.
      destruct scs2; [|discriminate].
      destruct (run_sound segs (N.to_nat fuel) stops (SCR dirs [] []) (xs_pc st) (xs_sr st) (xs_kn st) nv ss' scs scr' E M rom R Hex HR HK
                  (scs_chk_sound E M M (xs_kn st) scs HK Hchk)) as (R1 & HR1 & Hlf & Hms).
      pose proof (carry_keep_sound segs keep E M M (s_log ss') (xs_kn st) [] kn' [] hs2 Hc Hlf HK ltac:(constructor)) as HK1.
      pose proof (log_covered_frame E M rs (s_log ss') Hcov RF Hlf) as Hfr1.
      destruct (IH _ _ E _ R1 rom H RF HR1 HK1) as (R' & M' & Hms' & HR' & HK' & Hfr').
      cbn [xs_pc] in Hms'.
      exists R', M'. split; [eapply msteps_trans; [exact Hms | exact Hms']|].
      split; [exact HR'|]. split; [exact HK'|]. eapply frame_mod_trans_same; [exact Hfr1 | exact Hfr'].
    + destruct (xcas w st) as [[st1 e]|] eqn:Hx; [|discriminate].
      destruct (log_covered rs [e]) eqn:Hcov; [|discriminate].
      destruct (carry [e] (xs_kn st) []) as [[kn' scs2] hs2] eqn:Hc.
      destruct scs2; [|discriminate].
      destruct (xcas_sound w st st1 e E M R rom Hx HR HK) as (R1 & Hms & HR1 & Hlf & Hkn).
      pose proof (carry_after segs E M [e] (xs_kn st) [] kn' [] hs2 Hc Hlf HK ltac:(constructor)) as HK1.
      pose proof (log_covered_frame E M rs [e] Hcov RF Hlf) as Hfr1.
      destruct (IH _ _ E _ R1 rom H RF HR1 HK1) as (R' & M' & Hms' & HR' & HK' & Hfr').
      cbn [xs_pc] in Hms'.
      exists R', M'. split; [eapply msteps_trans; [exact Hms | exact Hms']|].
      split; [exact HR'|]. split; [exact HK'|]. eapply frame_mod_trans_same; [exact Hfr1 | exact Hfr'].
Qed.

Definition xchain_end (rs : list sregion) (nv : nat) (sg : list xseg) (st : xst) (pc : Z) (chk : list expr -> bool) : bool :=
  match xchain rs nv sg st with Some st' => (Z.eqb (xs_pc st') pc && chk (xs_sr st'))%bool | None => false end.

Lemma xchain_end_sound : forall rs nv sg st pc chk,
  xchain_end rs nv sg st pc chk = true -> exists st', xchain rs nv sg st = Some st' /\ xs_pc st' = pc /\ chk (xs_sr st') = true.
Proof.
  intros rs nv sg st pc chk H. unfold xchain_end in H. destruct (xchain rs nv sg st) as [st'|]; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. eauto.
Qed.

Definition rflat1 (kn : list kentry) (r : sregion) : bool :=
  match r with
  | (SA b k, n) =>
      match base_range kn b with
      | Some (lo, hi) => (Z.leb 0 (lo + k) && Z.ltb (hi + k) (2 ^ 64) && Z.leb 0 n && Z.leb (hi + k + n) (2 ^ 64))%bool
      | None => false
      end
  end.
Definition rflat_chk (kn : list kentry) (rs : list sregion) : bool := forallb (rflat1 kn) rs.

Lemma rflat_chk_sound : forall E M kn rs, know_ok segs E M kn -> rflat_chk kn rs = true -> regions_flat E rs.
Proof.
  intros E M kn rs HK H r Hin. unfold rflat_chk in H. pose proof (proj1 (forallb_forall _ _) H r Hin) as Hr.
  destruct r as [[b k] n]. cbn [rflat1] in Hr.
  destruct (base_range kn b) as [[lo hi]|] eqn:Hb; [|discriminate].
  repeat match type of Hr with (_ && _)%bool = true => apply andb_prop in Hr as [Hr ?] end.
  apply Z.leb_le in Hr.
  repeat match goal with H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H end.
  destruct (base_range_sound segs E M kn b lo hi HK Hb) as [Hlo Hhi].
  unfold flat, estart. cbn [fst snd a_base a_off]. lia.
Qed.

Definition kentry_eqb (x y : kentry) : bool :=
  match x, y with
  | KWord a w v, KWord a' w' v' => saddr_eqb a a' && Nat.eqb w w' && expr_eqb v v'
  | KZero a n, KZero a' n' => saddr_eqb a a' && expr_eqb n n'
  | KBlob a n k, KBlob a' n' k' => saddr_eqb a a' && expr_eqb n n' && Nat.eqb k k'
  | KImg lo hi, KImg lo' hi' => Z.eqb lo lo' && Z.eqb hi hi'
  | KAlign e m, KAlign e' m' => expr_eqb e e' && Z.eqb m m'
  | KRange e lo hi, KRange e' lo' hi' => expr_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | KWr a n, KWr a' n' => saddr_eqb a a' && Z.eqb n n'
  | KDisj a1 n1 a2 n2, KDisj a1' n1' a2' n2' => saddr_eqb a1 a1' && Z.eqb n1 n1' && saddr_eqb a2 a2' && Z.eqb n2 n2'
  | _, _ => false
  end%bool.

Lemma kentry_eqb_eq : forall x y, kentry_eqb x y = true -> x = y.
Proof.
  intros x y H. destruct x, y; cbn [kentry_eqb] in H; try discriminate;
    repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?] end;
    repeat match goal with
           | Hs : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in Hs; subst
           | He : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in He; subst
           | Hn : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in Hn; subst
           | Hz : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hz; subst
           end; reflexivity.
Qed.

Definition kn_incl (sub kn : list kentry) : bool := forallb (fun K => existsb (kentry_eqb K) kn) sub.

Lemma kn_incl_sound : forall E M sub kn, kn_incl sub kn = true -> know_ok segs E M kn -> know_ok segs E M sub.
Proof.
  intros E M sub kn H HK. unfold kn_incl in H. unfold know_ok. apply Forall_forall. intros K HIn.
  pose proof (proj1 (forallb_forall _ _) H K HIn) as HK1. apply existsb_exists in HK1 as (K' & HIn' & Heq).
  apply kentry_eqb_eq in Heq. subst K'. exact (proj1 (Forall_forall _ _) HK K HIn').
Qed.

Fixpoint sr_eqb (a b : list expr) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => expr_eqb x y && sr_eqb a' b'
  | _, _ => false
  end.

Lemma sr_eqb_eq : forall a b, sr_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [sr_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. rewrite H1, (IH b H2). reflexivity.
Qed.

Lemma expr_vars_lt_mono : forall a b e, (a <= b)%nat -> expr_vars_lt a e = true -> expr_vars_lt b e = true.
Proof.
  intros a b e Hab. induction e; cbn [expr_vars_lt]; intros H; try reflexivity;
    repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [? ?] end;
    try (apply andb_true_intro; split; auto).
  - apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
  - auto.
Qed.

Lemma sr_vars_lt_mono : forall a b sr, (a <= b)%nat -> sr_vars_lt a sr = true -> sr_vars_lt b sr = true.
Proof.
  intros a b sr Hab. induction sr as [|e sr IH]; cbn [sr_vars_lt]; intros H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply andb_true_intro. split; [eapply expr_vars_lt_mono; eauto | auto].
Qed.

Definition rebase_chk (nv nvt : nat) (sr : list expr) (kept : list nat) (sr_t : list expr) (kn kn_t : list kentry) : bool :=
  (Nat.leb nv nvt && sr_vars_lt nv sr && kn_vars_lt nv kn_t && kn_incl kn_t kn
   && negb (existsb (Nat.eqb 0) kept) && forallb (fun i => Nat.ltb i 32) kept
   && sr_eqb (sr_after_call_j sr kept nvt) sr_t)%bool.

Theorem rebase_sound : forall vals ebs R M nvt sr kept sr_t kn kn_t pad,
  rebase_chk (length vals) nvt sr kept sr_t kn kn_t = true ->
  length pad = (nvt - length vals)%nat ->
  regs_ok (Env (vals_ev vals) ebs) sr R -> know_ok segs (Env (vals_ev vals) ebs) M kn ->
  regs_ok (Env (vals_ev (vals ++ pad ++ junk_vals R)) ebs) sr_t R
  /\ know_ok segs (Env (vals_ev (vals ++ pad ++ junk_vals R)) ebs) M kn_t
  /\ (forall n, (n < length vals)%nat -> vals_ev (vals ++ pad ++ junk_vals R) n = vals_ev vals n).
Proof.
  intros vals ebs R M nvt sr kept sr_t kn kn_t pad Hc Hpad HR HK.
  unfold rebase_chk in Hc.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?] end.
  rename Hc into Hle. apply Nat.leb_le in Hle.
  match goal with H : sr_eqb _ sr_t = true |- _ => apply sr_eqb_eq in H; subst sr_t end.
  assert (Hlen : length (vals ++ pad) = nvt) by (rewrite length_app; lia).
  split; [| split].
  - rewrite app_assoc. rewrite <- Hlen.
    apply (regs_after_call (vals ++ pad) ebs sr R R kept).
    + eapply sr_vars_lt_mono; [| eassumption]. rewrite length_app. lia.
    + apply env_app_regs; assumption.
    + intros i Hi. split; [| reflexivity].
      match goal with H : forallb _ kept = true |- _ => pose proof (proj1 (forallb_forall _ _) H i Hi) as Hi32 end.
      apply Nat.ltb_lt in Hi32. exact Hi32.
    + intros Hin0. match goal with H : negb (existsb _ kept) = true |- _ => apply negb_true_iff in H; rename H into Hn end.
      assert (Hx : existsb (Nat.eqb 0) kept = true) by (apply existsb_exists; exists 0%nat; split; [exact Hin0 | reflexivity]).
      rewrite Hx in Hn. discriminate.
  - apply env_app_know; [assumption | eapply kn_incl_sound; eassumption].
  - intros n Hn. apply vals_ev_app_l. exact Hn.
Qed.

Definition xchain_rebase (rs : list sregion) (nv nvt : nat) (sg : list xseg) (st : xst) (pc : Z)
    (kept : list nat) (sr_t : list expr) (kn_t : list kentry) : bool :=
  match xchain rs nv sg st with
  | Some st' => (Z.eqb (xs_pc st') pc && rebase_chk nv nvt (xs_sr st') kept sr_t (xs_kn st') kn_t)%bool
  | None => false
  end.

Theorem xchain_rebase_sound : forall rs nvt sg st pc kept sr_t kn_t vals ebs R M rom pad,
  xchain_rebase rs (length vals) nvt sg st pc kept sr_t kn_t = true ->
  length pad = (nvt - length vals)%nat ->
  regions_flat (Env (vals_ev vals) ebs) rs ->
  regs_ok (Env (vals_ev vals) ebs) (xs_sr st) R -> know_ok segs (Env (vals_ev vals) ebs) M (xs_kn st) ->
  exists R' M', msteps segs (mkst R (Z_to_bv 64 (xs_pc st)) M rom) (mkst R' (Z_to_bv 64 pc) M' rom)
    /\ regs_ok (Env (vals_ev (vals ++ pad ++ junk_vals R')) ebs) sr_t R'
    /\ know_ok segs (Env (vals_ev (vals ++ pad ++ junk_vals R')) ebs) M' kn_t
    /\ frame_mod M M' (map (rdenot (Env (vals_ev vals) ebs)) rs)
    /\ (forall n, (n < length vals)%nat -> vals_ev (vals ++ pad ++ junk_vals R') n = vals_ev vals n).
Proof.
  intros rs nvt sg st pc kept sr_t kn_t vals ebs R M rom pad H Hpad RF HR HK.
  unfold xchain_rebase in H. destruct (xchain rs (length vals) sg st) as [st'|] eqn:Hx; [|discriminate].
  apply andb_prop in H as [Hpc Hrb]. apply Z.eqb_eq in Hpc.
  destruct (xchain_sound rs (length vals) sg st st' _ M R rom Hx RF HR HK) as (R' & M' & Hms & HR' & HK' & Hfr).
  destruct (rebase_sound vals ebs R' M' nvt (xs_sr st') kept sr_t (xs_kn st') kn_t pad Hrb Hpad HR' HK') as (A & B & C).
  exists R', M'. rewrite <- Hpc. auto.
Qed.

End Kit.
