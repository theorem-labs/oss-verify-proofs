(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CSL.
Definition mem := (word -> option byte).

(* [comment removed for export] *)
Definition dec_load1 (w : bv 32) : option (bool * reg * reg * bv 12) :=
  match decode_any w with Some (Load SZ1 sx rd rs imm, 4) => Some (sx, rd, rs, imm) | _ => None end.
Definition dec_br0 (w : bv 32) : option (branch_cond * reg * reg * bv 13) :=
  match decode_any w with Some (Branch bc r1 r2 imm, 4) => Some (bc, r1, r2, imm) | _ => None end.
Lemma dec_load1_sound : forall w sx rd rs imm, dec_load1 w = Some (sx, rd, rs, imm) -> decode_any w = Some (Load SZ1 sx rd rs imm, 4).
Proof.
  intros w sx rd rs imm H. unfold dec_load1 in H. destruct (decode_any w) as [[ins z]|]; [|discriminate]. destruct ins; try discriminate.
  lazymatch type of H with match ?m with _ => _ end = _ => destruct m eqn:Em; try discriminate end.
  destruct z as [|p|]; try discriminate. do 3 (try (destruct p; try discriminate)). congruence.
Qed.
Lemma dec_br0_sound : forall w bc r1 r2 imm, dec_br0 w = Some (bc, r1, r2, imm) -> decode_any w = Some (Branch bc r1 r2 imm, 4).
Proof.
  intros w bc r1 r2 imm H. unfold dec_br0 in H. destruct (decode_any w) as [[ins z]|]; [|discriminate]. destruct ins; try discriminate.
  destruct z as [|p|]; try discriminate. do 3 (try (destruct p; try discriminate)). congruence.
Qed.
Definition site_chk (segs : list Segment) (pc : Z) : option (nat * nat * Z) :=
  match fetch_word segs (Z_to_bv 64 pc), fetch_word segs (Z_to_bv 64 (pc + 4)) with
  | Some w1, Some w2 =>
      if (is_ecall w1 || is_ecall w2)%bool then None else
      match dec_load1 w1, dec_br0 w2 with
      | Some (_, rd, rs, imm), Some (bc, r1, r2, off) =>
          if (Z.eqb (bv_signed imm) 0 && negb (bv_eqb rd 0%bv) && bv_eqb r1 rd && bv_eqb r2 0%bv)%bool then
            match bc with
            | BC_NE => Some (ridx rd, ridx rs, pc + 8)
            | BC_EQ => Some (ridx rd, ridx rs, pc + 4 + bv_signed off)
            | _ => None
            end
          else None
      | _, _ => None
      end
  | _, _ => None
  end.
Lemma site_chk_sound : forall segs pc rd rs pc2, site_chk segs pc = Some (rd, rs, pc2) ->
  exists w1 w2 sx rdr rsr imm bc off,
    fetch_word segs (Z_to_bv 64 pc) = Some w1 /\ is_ecall w1 = false /\ decode_any w1 = Some (Load SZ1 sx rdr rsr imm, 4) /\ bv_signed imm = 0 /\
    fetch_word segs (Z_to_bv 64 (pc + 4)) = Some w2 /\ is_ecall w2 = false /\ decode_any w2 = Some (Branch bc rdr 0%bv off, 4) /\
    rdr <> 0%bv /\ ridx rdr = rd /\ ridx rsr = rs /\ ((bc = BC_NE /\ pc2 = pc + 8) \/ (bc = BC_EQ /\ pc2 = pc + 4 + bv_signed off)).
Proof.
  intros segs pc rd rs pc2 H. unfold site_chk in H.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w1|] eqn:Hf1; [|discriminate].
  destruct (fetch_word segs (Z_to_bv 64 (pc + 4))) as [w2|] eqn:Hf2; [|discriminate].
  destruct (is_ecall w1) eqn:He1; [discriminate|]. destruct (is_ecall w2) eqn:He2; [discriminate|]. cbn [orb] in H.
  destruct (dec_load1 w1) as [[[[sx rdr] rsr] imm]|] eqn:Hd1; [|discriminate].
  destruct (dec_br0 w2) as [[[[bc r1] r2] off]|] eqn:Hd2; [|discriminate].
  lazymatch type of H with (if ?bb then _ else _) = _ => destruct bb eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb Hr2]. apply andb_prop in Hb as [Hb Hr1]. apply andb_prop in Hb as [Himm Hrd0].
  apply Z.eqb_eq in Himm. apply negb_true_iff in Hrd0.
  assert (r1 = rdr) as -> by (apply bv_eq; unfold bv_eqb in Hr1; apply Z.eqb_eq in Hr1; exact Hr1).
  assert (r2 = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Hr2; apply Z.eqb_eq in Hr2; exact Hr2).
  exists w1, w2, sx, rdr, rsr, imm, bc, off.
  split; [reflexivity|]. split; [exact He1|]. split; [exact (dec_load1_sound _ _ _ _ _ Hd1)|]. split; [exact Himm|].
  split; [reflexivity|]. split; [exact He2|]. split; [exact (dec_br0_sound _ _ _ _ _ Hd2)|].
  split; [intros ->; rewrite bv_eqb_refl in Hrd0; discriminate|| (intros EE; subst; cbn in Hrd0; discriminate)|].
  destruct bc; try discriminate H; injection H as <- <- <-; (split; [reflexivity|]); (split; [reflexivity|]); first [left; split; reflexivity | right; split; reflexivity].
Qed.

(* [comment removed for export] *)
Definition reg_is (regs : list (nat * expr)) (r : nat) (e : expr) : bool :=
  existsb (fun ie : nat * expr => (Nat.eqb (fst ie) r && expr_eqb (snd ie) e)%bool) regs.
Definition kvar_ok (cells : list kentry) (kv : nat) : bool :=
  existsb (fun X => match X with KRange (EVar v) lo hi => (Nat.eqb v kv && Z.leb 0 lo && Z.leb hi 1099511627776)%bool | _ => false end) cells.
Definition meas_form (kv : nat) (a : Z) : expr := APC.eaddz (APC.escale 64 (EVar kv)) a.

Definition shl_chk (NF : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (s : CC.subst) (rd rs : nat) (pc2 : Z) (cur : expr) (SBz : Z) (kv : nat) (a b : Z) : bool :=
  (Z.eqb (CC.cp_pc cj) pc2
   && Nat.leb NF (CC.cp_nx c) && Nat.ltb 0 rd && Nat.ltb rd 32 && Nat.ltb 0 rs && Nat.ltb rs 32
   && reg_is (SR.ps_regs ps) rs (EAlu ALU_ADD (EAlu ALU_SRL cur (ELit 3)) (ELit SBz))
   && forallb (fun r => if Nat.eqb r rd then expr_eqb (CC.esubstL NF s (nth r (CC.cp_regs cj) (ELit 0))) (ELit 0)
                        else reg_is (SR.ps_regs ps) r (CC.esubstL NF s (nth r (CC.cp_regs cj) (ELit 0)))) (seq 1 31)
   && forallb (fun X => let X' := CC.ksubstL NF s X in (CC.has_cell (SR.ps_cells ps) X' || CX.fact2_ok (SR.ps_cells ps) X')%bool) (CC.cp_know cj)
   && APC.expr_vars_lt (CC.cp_nx c) (CC.cp_meas c)
   && expr_eqb (CC.cp_meas c) (meas_form kv a) && expr_eqb (CC.esubstL NF s (CC.cp_meas cj)) (meas_form kv b)
   && Z.leb 0 b && Z.ltb b a && Z.leb a 64 && Nat.ltb kv (CC.cp_nx c) && kvar_ok (SR.ps_cells ps) kv)%bool.

Lemma reg_is_sound : forall regs r e, reg_is regs r e = true -> In (r, e) regs.
Proof.
  intros regs r e H. unfold reg_is in H. apply existsb_exists in H as ([i x] & Hin & Hb). cbn [fst snd] in Hb.
  apply andb_prop in Hb as [H1 H2]. apply Nat.eqb_eq in H1. apply expr_eqb_eq in H2. subst. exact Hin.
Qed.

Lemma rdn1 : forall segs (M : mem) (a : word) b, M a = Some b -> rdn segs M a 1 = Some [b].
Proof. intros segs M a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

Lemma pc4 : forall pc z, 0 <= pc -> pc + z < 2 ^ 64 -> 0 <= z -> v_addi (Z_to_bv 64 pc) z = Z_to_bv 64 (pc + z).
Proof.
  intros pc z H1 H2 H3. unfold v_addi. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma u_meas_form : forall E kv a, 0 <= a <= 64 -> 0 <= bv_unsigned (ev E kv) <= 1099511627776 ->
  bv_unsigned (edenot E (meas_form kv a)) = 64 * bv_unsigned (ev E kv) + a.
Proof.
  intros E kv a Ha Hk. unfold meas_form, APC.eaddz, APC.escale. rewrite mkAlu_denot, u_add64, mkMd_denot, u_mul64. cbn [edenot].
  rewrite !u_lit64. change two64 with (2 ^ 64). rewrite (Z.mod_small 64) by lia. rewrite (Z.mod_small a) by lia.
  rewrite (Z.mod_small (64 * _)) by lia. apply Z.mod_small. lia.
Qed.

Section Leaf.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBrest : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable Cred : nat -> env -> credit -> Prop.
Variable D0 : Z.
Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBrest FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Variable XI : nat -> env -> list (Z * Z) -> mem -> Model -> Prop.

Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).
Abbreviation AMBX := (CHA.ambX L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 XI).

(* [comment removed for export] *)
Theorem shload_leaf : forall i c ps j cj s rd rs pc2 cur SBz kv a b,
  nth_error CPS j = Some cj ->
  site_chk (hl_segs L) (SR.ps_pc ps) = Some (rd, rs, pc2) ->
  shl_chk NF c ps cj s rd rs pc2 cur SBz kv a b = true ->
  CHA.goto_amb_chk NF d c (nth i BLS []) (nth j BLS []) (nth i FFS []) (nth j FFS []) s = true ->
  0 <= SR.ps_pc ps /\ SR.ps_pc ps + 8 < 2 ^ 64 /\ 0 <= pc2 < 2 ^ 64 ->
  (forall E E' R R' A M model M1 model1,
     CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> XI i E A M model -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
     (exists base gr, In (KZero (SA (EAlu ALU_SRL base (ELit 3)) SBz) gr) (SR.ps_cells ps) /\
        bv_unsigned (edenot E' base) mod 8 = 0 /\ bv_unsigned (edenot E' base) <= bv_unsigned (edenot E' cur) < bv_unsigned (edenot E' base) + 8 * bv_unsigned (edenot E' gr))
     /\ XI j (CC.env_over NF s E') A M1 model1) ->
  (forall E E' R' M M' cr, env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr -> Cred j (CC.env_over NF s E') cr) ->
  CCA.leaf_ok (hl_segs L) CPS AMBX K FPI i c ps.
Proof.
  intros i c ps j cj s rd rs pc2 cur SBz kv a b Hcj Hsite Hchk Hgchk Hpc USER CRED fx' E R A M model E' R' M1 model1 HAt [HA HXI] HFP Hag HLF HIH.
  (* [comment removed for export] *)
  unfold shl_chk in Hchk.
  apply andb_prop in Hchk as [Hchk Xkvar]. apply andb_prop in Hchk as [Hchk Xklt]. apply andb_prop in Hchk as [Hchk Xa64]. apply andb_prop in Hchk as [Hchk Xba]. apply andb_prop in Hchk as [Hchk Xb0].
  apply andb_prop in Hchk as [Hchk Xmj]. apply andb_prop in Hchk as [Hchk Xmi]. apply andb_prop in Hchk as [Hchk Xmv]. apply andb_prop in Hchk as [Hchk Xkn]. apply andb_prop in Hchk as [Hchk Xregs].
  apply andb_prop in Hchk as [Hchk Xrs]. apply andb_prop in Hchk as [Hchk Xrs32]. apply andb_prop in Hchk as [Hchk Xrs0]. apply andb_prop in Hchk as [Hchk Xrd32]. apply andb_prop in Hchk as [Hchk Xrd0].
  apply andb_prop in Hchk as [Hchk Xnf].
  apply Z.eqb_eq in Hchk. apply Nat.leb_le in Xnf. apply Nat.ltb_lt in Xrd0. apply Nat.ltb_lt in Xrd32. apply Nat.ltb_lt in Xrs0. apply Nat.ltb_lt in Xrs32.
  apply reg_is_sound in Xrs. apply expr_eqb_eq in Xmi. apply expr_eqb_eq in Xmj. apply Z.leb_le in Xb0. apply Z.ltb_lt in Xba. apply Z.leb_le in Xa64. apply Nat.ltb_lt in Xklt.
  (* [comment removed for export] *)
  destruct (site_chk_sound _ _ _ _ _ Hsite) as (w1 & w2 & sx & rd0 & rs0 & imm & bc & imm0 & Hf1 & He1 & Hd1 & Himm & Hf2 & He2 & Hd2 & Hrdnz & Erd & Ers0 & Hbc).
  (* [comment removed for export] *)
  pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
  destruct (USER E E' R R' A M model M1 model1 HAt HA HXI Hag HLF) as ((base & gr & Hinz & Hal & Hlo & Hhi) & HXIj).
  pose proof (CC.lf_cells _ _ _ _ _ _ _ HLFv _ Hinz) as (Hflz & Hz). unfold elenZ in Hz.
  set (ub := bv_unsigned (edenot E' base)) in *. set (uc := bv_unsigned (edenot E' cur)) in *. set (ug := bv_unsigned (edenot E' gr)) in *.
  destruct Hflz as (F1 & F2 & F3 & F4). unfold estart, elenZ in F1, F2, F3, F4, Hz. cbn [a_base a_off] in F1, F2, F3, F4, Hz.
  rewrite u_srl_lit in F1, F2, F4, Hz. change (2 ^ ((3 mod two64) mod 64)) with 8 in F1, F2, F4, Hz. fold ub in F1, F2, F4, Hz. fold ug in F3, F4, Hz.
  pose proof (u64_range (edenot E' cur)) as Rc. fold uc in Rc. change two64 with (2 ^ 64) in Rc.
  (* [comment removed for export] *)
  destruct (CC.lf_regs _ _ _ _ _ _ _ HLFv _ _ Xrs) as [_ Hrs].
  set (rsr := (Z_to_bv 5 (Z.of_nat rs)) : reg) in Hrs.
  assert (Ers : rs0 = rsr) by (unfold rsr; rewrite <- Ers0; symmetry; apply CC.reg_of_ridx).
  assert (Hrsv : bv_unsigned (getr R' rs0) = (uc / 8 + SBz) mod 2 ^ 64).
  { rewrite Ers, Hrs. change (edenot E' (EAlu ALU_ADD (EAlu ALU_SRL cur (ELit 3)) (ELit SBz))) with (alu64 ALU_ADD (edenot E' (EAlu ALU_SRL cur (ELit 3))) (Z_to_bv 64 SBz)).
    rewrite u_add64, u_srl_lit. change (2 ^ ((3 mod two64) mod 64)) with 8. fold uc. rewrite u_lit64. change two64 with (2 ^ 64). apply Z.add_mod_idemp_r. lia. }
  (* [comment removed for export] *)
  assert (Hz0 : CCA.vis A model1 M1 (getr R' rs0) = Some (Z_to_bv 8 0)).
  { assert (Hq : ub = 8 * (ub / 8)) by (pose proof (Z.div_mod ub 8 ltac:(lia)) as DM; lia).
    assert (Hidx : 0 <= uc / 8 - ub / 8 < ug).
    { split; [apply Z.le_0_sub; apply Z.div_le_mono; lia|].
      assert (uc / 8 < ub / 8 + ug); [apply Z.div_lt_upper_bound; lia | lia]. }
    specialize (Hz (uc / 8 - ub / 8) Hidx). rewrite <- Hz. f_equal. rewrite <- (Z_to_bv_bv_unsigned 64 (getr R' rs0)), Hrsv.
    rewrite Z.mod_small by lia. f_equal. lia. }
  (* [comment removed for export] *)
  pose proof (CHA.leaf_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
                i c ps E E' R R' A M model M1 model1) as HA1.
  unfold CHA.goto_amb_chk in Hgchk. pose proof Hgchk as Hgchk'. apply andb_prop in Hgchk' as [Hgchk' _]. apply andb_prop in Hgchk' as [Hfoot _].
  specialize (HA1 Hfoot HAt HA Hag HLF).
  destruct (CHA.aamb_model L ar C HI HIok LY_below NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i E A M1 model1 HA1) as (Hh1 & HMI1 & HAwf & Hoff1).
  set (H1 := ahid A model1).
  set (R2 := regupd R' rd0 (Z_to_bv 64 0)).
  destruct Hpc as (Hpc0 & Hpc8 & Hpc2).
  assert (X0R : getr R' 0%bv = Z_to_bv 64 0) by (exact (CC.lf_x0 _ _ _ _ _ _ _ HLFv)).
  assert (MS : msteps (hl_segs L) (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) (mrestrict H1 M1) (seg_rom (hl_segs L)))
                                  (@mkst fx' R2 (Z_to_bv 64 pc2) (mrestrict H1 M1) (seg_rom (hl_segs L)))).
  { eapply mst_step; [reflexivity | |].
    - destruct sx.
      + rewrite (step_lb (hl_segs L) R' (Z_to_bv 64 (SR.ps_pc ps)) (mrestrict H1 M1) (seg_rom (hl_segs L)) w1 rd0 rs0 imm (Z_to_bv 8 0) Hf1 He1 Hd1).
        * rewrite (proj2 (bv_eqb_neq rd0 0%bv) Hrdnz) || (destruct (bv_eqb rd0 0%bv) eqn:EE; [exfalso; apply Hrdnz; apply bv_eq; unfold bv_eqb in EE; apply Z.eqb_eq in EE; exact EE|]).
          rewrite pc4 by lia. reflexivity.
        * rewrite Himm. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply rdn1. exact Hz0.
      + rewrite (step_lbu (hl_segs L) R' (Z_to_bv 64 (SR.ps_pc ps)) (mrestrict H1 M1) (seg_rom (hl_segs L)) w1 rd0 rs0 imm (Z_to_bv 8 0) Hf1 He1 Hd1).
        * rewrite (proj2 (bv_eqb_neq rd0 0%bv) Hrdnz) || (destruct (bv_eqb rd0 0%bv) eqn:EE; [exfalso; apply Hrdnz; apply bv_eq; unfold bv_eqb in EE; apply Z.eqb_eq in EE; exact EE|]).
          rewrite pc4 by lia. reflexivity.
        * rewrite Himm. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply rdn1. exact Hz0.
    - assert (Hc : c_eq (getr R2 rd0) (getr R2 0%bv) = true).
      { unfold R2. rewrite (getr_same _ _ _ Hrdnz). rewrite getr_other by (intros EE; apply Hrdnz; symmetry; exact EE). rewrite X0R. unfold c_eq. apply bv_eqb_refl || (unfold bv_eqb; apply Z.eqb_refl). }
      eapply mst_step; [reflexivity | | apply mst_refl].
      destruct Hbc as [[-> Hpc2'] | [-> Hpc2']].
      + (* [comment removed for export] *) rewrite (step_bne_ft (hl_segs L) R2 (Z_to_bv 64 (SR.ps_pc ps + 4)) (mrestrict H1 M1) (seg_rom (hl_segs L)) w2 rd0 0%bv imm0 Hf2 He2 Hd2 Hc).
        rewrite pc4 by lia. rewrite Hpc2'. replace (SR.ps_pc ps + 4 + 4) with (SR.ps_pc ps + 8) by lia. reflexivity.
      + (* [comment removed for export] *) rewrite (step_beq_tk (hl_segs L) R2 (Z_to_bv 64 (SR.ps_pc ps + 4)) (mrestrict H1 M1) (seg_rom (hl_segs L)) w2 rd0 0%bv imm0 Hf2 He2 Hd2 Hc).
        unfold btgt, v_addi. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small (SR.ps_pc ps + 4)) by lia.
        rewrite Hpc2'. reflexivity. }
  eapply (L5LZ.cps_of_msteps_lazy (hl_segs L) H1 A fx' fx' R' _ M1 R2 _ (mrestrict H1 M1) model1 K Hoff1 LY_nowrap (L5LZ.lazy_cover_ahid A model1) HAwf HMI1 Hh1 MS).
  intros model2 HMI2 HS12 _.
  replace (munrestrict H1 M1 (mrestrict H1 M1)) with M1
    by (apply FunctionalExtensionality.functional_extensionality; intros x; unfold munrestrict, mrestrict; destruct (H1 x); reflexivity).
  (* [comment removed for export] *)
  assert (HLF2 : CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model2).
  { constructor.
    - rewrite (CCA.vis_sbm A model1 model2 M1 HS12). exact HLFv.
    - exact (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF).
    - exact (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF).
    - exact (CCA.lfa_hid _ _ _ _ _ _ _ _ _ _ HLF).
    - exact (same_but_materialized_trans _ _ _ (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF) HS12).
    - exact HMI2. }
  rewrite <- Hchk.
  set (E2 := CC.env_over NF s E').
  apply (HIH j cj fx' E2 R2 A M1 model2 Hcj).
  - (* [comment removed for export] *)
    split.
    + intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
      * assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er; apply Z.eqb_eq in Er; exact Er).
        cbn [edenot]. unfold R2. rewrite getr_other by (intros EE; apply Hrdnz; symmetry; exact EE). exact X0R.
      * assert (Hr : (1 <= ridx r < 32)%nat).
        { unfold ridx. pose proof (bv_unsigned_in_range _ r) as B. change (bv_modulus 5) with 32 in B.
          unfold bv_eqb in Er. apply Z.eqb_neq in Er. change (bv_unsigned (0%bv : bv 5)) with 0 in Er. lia. }
        rewrite forallb_forall in Xregs. specialize (Xregs (ridx r) ltac:(apply in_seq; lia)).
        destruct (Nat.eqb (ridx r) rd) eqn:Erd'.
        -- apply Nat.eqb_eq in Erd'. assert (Err : r = rd0) by (rewrite <- (CC.reg_of_ridx r), <- (CC.reg_of_ridx rd0); rewrite Erd', Erd; reflexivity).
           apply expr_eqb_eq in Xregs. unfold R2. rewrite Err, (getr_same _ _ _ Hrdnz). unfold E2. rewrite <- CC.esubstL_denot. rewrite Erd, <- Erd', Xregs. reflexivity.
        -- apply Nat.eqb_neq in Erd'. apply reg_is_sound in Xregs. destruct (CC.lf_regs _ _ _ _ _ _ _ HLFv _ _ Xregs) as [_ Hg]. rewrite CC.reg_of_ridx in Hg.
           unfold R2. rewrite getr_other by (intros EE; apply Erd'; rewrite EE; exact Erd). rewrite Hg. unfold E2. apply CC.esubstL_denot.
    + rewrite (CCA.vis_sbm A model1 model2 M1 HS12).
      unfold know_ok. apply Forall_forall. intros X' HX'. rewrite forallb_forall in Xkn. specialize (Xkn X' HX'). cbv zeta in Xkn.
      apply (CC.kentry_ok_ksubstL (hl_segs L) NF s E' _ X'). apply orb_prop in Xkn. destruct Xkn as [Xkn|Xkn].
      * apply CC.has_cell_In in Xkn. exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ Xkn).
      * apply (CX.fact2_ok_sound (hl_segs L) E' _ (SR.ps_cells ps) _ ltac:(unfold know_ok; apply Forall_forall; intros Y HY; exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HY)) Xkn).
  - (* [comment removed for export] *)
    split.
    + exact (CHA.goto_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
               i c ps j s Hgchk CRED E R A M model E' R' M1 model2 HAt HA Hag HLF2).
    + (* [comment removed for export] *) exact (proj2 (USER E E' R R' A M model M1 model2 HAt HA HXI Hag HLF2)).
  - exact HFP.
  - (* [comment removed for export] *)
    unfold CC.meas. unfold E2. rewrite <- CC.esubstL_denot, Xmj. rewrite Xmi. rewrite Xmi in Xmv.
    rewrite (SR.edenot_agree_AP _ E E' _ Hag Xmv).
    unfold kvar_ok in Xkvar. apply existsb_exists in Xkvar as (Xk & HXk & Hkb). destruct Xk as [| | | | |ek lo hi| | | |]; try discriminate Hkb.
    destruct ek as [|v| | | | | |]; try discriminate Hkb. apply andb_prop in Hkb as [Hkb Hkhi]. apply andb_prop in Hkb as [Hv Hklo].
    apply Nat.eqb_eq in Hv. apply Z.leb_le in Hklo. apply Z.leb_le in Hkhi. subst v.
    pose proof (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HXk) as HK. cbn [kentry_ok edenot] in HK.
    rewrite !u_meas_form by lia. lia.
Qed.
End Leaf.
End CSL.
