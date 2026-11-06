(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs StepSoundBase StepSoundAlu StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import VdStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Acc AccStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require VDestroy.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepA PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module VDA.
Section WithSegs.
Variable segs : list Segment.

Definition instr_at (pc : int) : option finstr :=
  match fetch_word segs (Z_to_bv 64 (to_Z pc)) with
  | Some w =>
      if is_ecall w then None else
      match decode_any w with
      | Some (i, z) => if Z.eqb z 4 then of_instr i else None
      | None => None
      end
  | None => None
  end.

Lemma instr_at_spec : forall pc fi, instr_at pc = Some fi ->
  exists w i, fetch_word segs (Z_to_bv 64 (to_Z pc)) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z) /\ of_instr i = Some fi.
Proof.
  intros pc fi H. unfold instr_at in H.
  destruct (fetch_word segs (Z_to_bv 64 (to_Z pc))) as [w|] eqn:F; [|discriminate].
  destruct (is_ecall w) eqn:EC; [discriminate|].
  destruct (decode_any w) as [[i z]|] eqn:D; [|discriminate].
  destruct (Z.eqb_spec z 4); [|discriminate]. subst z. exists w, i. auto.
Qed.

Section WithPc.
Variable PC : int.
Variables CUR BEG LIM : r5.
Variable S : int.
Variable NG : nat.

Fixpoint pc_after (pc : int) (n : nat) : int :=
  match n with O => pc | Datatypes.S n' => pc_after (PrimInt63.add pc 4%uint63) n' end.

Definition pcA : int := pc_after PC NG.
Definition pcB : int := PrimInt63.add pcA 4%uint63.
Definition EXIT : int := PrimInt63.add pcB 4%uint63.

Definition is_guard (fi : finstr) : bool :=
  match fi with
  | IBranch BC_GEU r1 r2 _ => r5_eqb r1 LIM && r5_eqb r2 CUR
  | IBranch BC_LTU r1 r2 _ => r5_eqb r1 CUR && r5_eqb r2 LIM
  | IBranch BC_EQ r1 r2 _ => (r5_eqb r1 CUR && r5_eqb r2 LIM) || (r5_eqb r1 LIM && r5_eqb r2 CUR)
  | _ => false
  end.

Fixpoint guards_ok (pc : int) (n : nat) : bool :=
  match n with
  | O => true
  | Datatypes.S n' => match instr_at pc with Some fi => is_guard fi && guards_ok (PrimInt63.add pc 4%uint63) n' | None => false end
  end.

Definition dec_ok (fi : finstr) : bool :=
  match fi with
  | IOpImm ALU_ADD rd rs v => r5_eqb rd CUR && r5_eqb rs CUR && weqb v (wsub wzero (wlit S))
  | _ => false
  end.
Definition latch_ok (fi : finstr) : bool :=
  match fi with
  | IBranch BC_NE r1 r2 off =>
      ((r5_eqb r1 CUR && r5_eqb r2 BEG) || (r5_eqb r1 BEG && r5_eqb r2 CUR))
      && match pc_add pcB off with Some t => PrimInt63.eqb t PC | None => false end
  | _ => false
  end.

Definition VD_MAX : w64 := wlit 288230376151711744%uint63.

Definition f1_match (fs : list fact) (cur beg : sv) (f : fact) : option int :=
  match f with
  | FEq e (VAlu ALU_ADD b (VMd M_MUL (VP j o) (VL s))) =>
      if weqb o wzero && weqb s (wlit S) && dec_true (decide_eq fs e cur) && dec_true (decide_eq fs b beg) then Some j else None
  | _ => None
  end.
Fixpoint find_f1 (fs0 fs : list fact) (cur beg : sv) : option int :=
  match fs with
  | [] => None
  | f :: fs' => match f1_match fs0 cur beg f with Some j => Some j | None => find_f1 fs0 fs' cur beg end
  end.

Definition BEG_MAX : w64 := wlit 4611686018427387904%uint63.
Definition cur_shape (fs : list fact) (cur beg : sv) : option int :=
  match cur, beg with
  | VAlu ALU_ADD (VP kb ob) (VMd M_MUL (VP j o) (VL s)), VP kb' ob' =>

      if weqb o wzero && weqb s (wlit S) && PrimInt63.eqb kb kb' && weqb ob' wzero && negb (wt ob)
         && PrimInt63.leb (wl ob) 512%uint63 && PrimInt63.eqb (PrimInt63.mod (wl ob) S) 0%uint63
         && wleu (snd (sv_bounds fs beg)) BEG_MAX
      then Some j else None
  | _, _ => None
  end.

Definition aligned8 (fs : list fact) (v : sv) : bool :=
  match v with
  | VAlu ALU_ADD a c => aligned fs a 3%uint63 && aligned fs c 3%uint63
  | _ => aligned fs v 3%uint63
  end.
Definition align_ok (fs : list fact) (cur beg : sv) : bool :=
  PrimInt63.eqb S 8%uint63 && aligned8 fs cur && aligned8 fs beg.

Definition vd_apply (st : sstate) : option (list sstate) :=
  let fs := s_facts st in let cur := getr st CUR in let beg := getr st BEG in
  match getr st LIM with
  | VL l =>
      if negb (r5_eqb CUR X0) && negb (r5_eqb CUR BEG) && negb (r5_eqb CUR LIM)
         && PrimInt63.ltb PC bit62i && Nat.leb NG 8 && PrimInt63.ltb EXIT bit62i
         && PrimInt63.leb 1%uint63 S && PrimInt63.leb S 32%uint63
         && guards_ok PC NG
         && match instr_at pcA with Some fi => dec_ok fi | None => false end
         && match instr_at pcB with Some fi => latch_ok fi | None => false end
         && match cur_shape fs cur beg with
            | Some j => dec_false (decide_ltu fs (VL VD_MAX) (VP j wzero))
            | None =>
                if dec_false (decide_ltu fs cur beg) then
                  match find_f1 fs fs cur beg with
                  | Some j => dec_false (decide_ltu fs (VL VD_MAX) (VP j wzero))
                  | None => align_ok fs cur beg
                  end
                else false
            end
         && dec_true (decide_ltu fs (VL l) beg)
         && dec_false (decide_eq fs cur beg)
      then Some [setpc (setr st CUR beg) EXIT] else None
  | _ => None
  end.

Definition vd_contract : contract := Contract PC vd_apply.

Section Sound.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Lemma noacc : forall i fi, of_instr i = Some fi ->
  match fi with IBranch _ _ _ _ => True | IOpImm _ _ _ _ => True | _ => False end ->
  forall c a n, Acc.mem_acc i c a n -> False.
Proof.
  intros i fi Hof FI c a n M. destruct i; cbn [Acc.mem_acc] in M; try exact M; cbn [of_instr] in Hof;
    repeat match type of Hof with
           | Some _ = Some _ => injection Hof as <-; exact FI
           | None = Some _ => discriminate Hof
           | (if ?b then _ else _) = Some _ => destruct b
           | match ?x with _ => _ end = Some _ => destruct x
           end.
Qed.

Lemma aligned8_sound : forall E fs v, facts_hold E fs -> aligned8 fs v = true -> bv_unsigned (den E v) mod 8 = 0.
Proof.
  intros E fs v FH H.
  assert (A1 : forall a, aligned fs a 3%uint63 = true -> bv_unsigned (den E a) mod 8 = 0).
  { intros a Ha. pose proof (aligned_sound E fs FH a 3%uint63 Ha ltac:(change (to_Z 3%uint63) with 3; lia)) as M.
    change (to_Z 3%uint63) with 3 in M. change (2 ^ 3) with 8 in M. exact M. }
  destruct v as [| |op a c| | | | | | | |]; try exact (A1 _ H). destruct op; try exact (A1 _ H).
  cbn [aligned8] in H. apply andb_prop in H as [Ha Hc].
  change (den E (VAlu ALU_ADD a c)) with (bv_add (den E a) (den E c)). rewrite bv_add_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
  change 8 with (2 ^ 3). rewrite (mod64_mod _ 3) by lia. change (2 ^ 3) with 8. rewrite Zplus_mod, (A1 a Ha), (A1 c Hc). reflexivity.
Qed.

Lemma rf_set_set : forall A (x : rf A) r v v', rf_set (rf_set x r v) r v' = rf_set x r v'.
Proof. intros A x r v v'; destruct r; reflexivity. Qed.

Lemma to_Z_add4 : forall pc, to_Z pc + 4 < 2 ^ 63 -> to_Z (PrimInt63.add pc 4%uint63) = to_Z pc + 4.
Proof.
  intros pc H. rewrite Uint63.add_spec. change (to_Z 4%uint63) with 4. apply Z.mod_small.
  pose proof (Uint63.to_Z_bounded pc). change wB with (2 ^ 63). lia.
Qed.

Lemma to_Z_pc_after : forall n pc, to_Z pc + 4 * Z.of_nat n < 2 ^ 63 -> to_Z (pc_after pc n) = to_Z pc + 4 * Z.of_nat n.
Proof.
  induction n as [|n IH]; intros pc H; cbn [pc_after]; [lia|].
  rewrite IH; rewrite to_Z_add4 by lia; lia.
Qed.

Lemma ltb62 : forall pc, to_Z pc < 2 ^ 62 -> PrimInt63.ltb pc bit62i = true.
Proof. intros pc H. apply Uint63.ltb_spec. change (to_Z bit62i) with (2 ^ 62). exact H. Qed.

Section Loop.
Variable E : env.
Variable K : TSet.
Variable st0 : sstate.
Variable l : w64.
Variables B Sz : Z.
Hypothesis HX0 : r5_eqb CUR X0 = false.
Hypothesis HCB : CUR <> BEG.
Hypothesis HCL : CUR <> LIM.
Hypothesis HLIM : getr st0 LIM = VL l.
Hypothesis HBEG : bv_unsigned (den E (getr st0 BEG)) = B.
Hypothesis HLB : w2Z l < B.
Hypothesis HSz : Sz = to_Z S.
Hypothesis HSR : 1 <= Sz <= 32.
Hypothesis HPC : to_Z PC < 2 ^ 62.
Hypothesis HNG : (NG <= 8)%nat.
Hypothesis HEX : to_Z EXIT < 2 ^ 62.
Hypothesis HG : guards_ok PC NG = true.
Hypothesis HD : match instr_at pcA with Some fi => dec_ok fi | None => false end = true.
Hypothesis HLA : match instr_at pcB with Some fi => latch_ok fi | None => false end = true.

Definition mk (p : int) (x : sv) : sstate := setpc (setr st0 CUR x) p.

Lemma mk_setpc : forall p x q, setpc (mk p x) q = mk q x.
Proof. reflexivity. Qed.
Lemma mk_setr : forall p x y q, setpc (setr (mk p x) CUR y) q = mk q y.
Proof.
  intros p x y q. unfold mk. rewrite !(setr_eq _ CUR _ HX0). unfold setpc. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  rewrite rf_set_set. reflexivity.
Qed.
Lemma mk_pc : forall p x, s_pc (mk p x) = p.
Proof. reflexivity. Qed.
Lemma mk_cur : forall p x, getr (mk p x) CUR = x.
Proof. intros p x. unfold mk, getr. rewrite (setr_eq _ CUR _ HX0). cbn [setpc s_rf]. apply rf_get_set_same. Qed.
Lemma mk_other : forall p x r, CUR <> r -> getr (mk p x) r = getr st0 r.
Proof. intros p x r NE. unfold mk, getr. rewrite (setr_eq _ CUR _ HX0). cbn [setpc s_rf]. apply rf_get_set_other. exact NE. Qed.

Lemma pcs : to_Z pcA = to_Z PC + 4 * Z.of_nat NG /\ to_Z pcB = to_Z pcA + 4 /\ to_Z EXIT = to_Z pcB + 4.
Proof.
  assert (A : to_Z pcA = to_Z PC + 4 * Z.of_nat NG) by (unfold pcA; apply to_Z_pc_after; lia).
  assert (Bq : to_Z pcB = to_Z pcA + 4) by (unfold pcB; apply to_Z_add4; lia).
  split; [exact A|]. split; [exact Bq|]. unfold EXIT. apply to_Z_add4. lia.
Qed.

Lemma astep : forall st' ms ms' model w i fi,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) -> of_instr i = Some fi ->
  match fi with IBranch _ _ _ _ => True | IOpImm _ _ _ _ => True | _ => False end ->
  RiscvSemantics.step segs ms = MachineOk ms' -> st_ok segs OPS E st' ms' model -> MP model ->
  ms_svc_pending ms = None -> m_halted model = None ->
  (forall mo', st_ok segs OPS E st' ms' mo' -> MP mo' -> realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros st' ms ms' model w i fi Hf He Hd Hof FI STEP HS' HMP Hsvc Hh HK.
  destruct (AccStep.st_ok_account_mp segs OPS (AccStep.CH_cov OPS) (AccStep.LAW_cov OPS) MP HMPA E st' ms ms' model w i Hf He Hd STEP HS' HMP) as (mo' & AS & HS2 & HMP2).
  { intros a n j M _. exfalso. exact (noacc i fi Hof FI _ a n M). }
  exact (rz_astep segs ms model ms' mo' K Hh Hsvc AS (HK mo' HS2 HMP2)).
Qed.

Lemma guards_cps : forall n pc x ms model,
  guards_ok pc n = true -> to_Z pc + 4 * Z.of_nat n < 2 ^ 62 ->
  st_ok segs OPS E (mk pc x) ms model -> MP model -> w2Z l < bv_unsigned (den E x) ->
  (forall ms' mo', st_ok segs OPS E (mk (pc_after pc n) x) ms' mo' -> MP mo' -> realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  induction n as [|n IH]; intros pc x ms model G Hb HS HMP HL HK; cbn [pc_after guards_ok] in *; [exact (HK ms model HS HMP)|].
  destruct (instr_at pc) as [fi|] eqn:IA; [|discriminate G]. apply andb_prop in G as [GI G].
  destruct (instr_at_spec pc fi IA) as (w & i & Hf & He & Hd & Hof).
  assert (Hf' : fetch_word segs (ms_pc_val ms) = Some w) by (rewrite (so_pc _ _ _ _ _ _ HS), mk_pc; exact Hf).
  assert (Hpc : PrimInt63.ltb (s_pc (mk pc x)) bit62i = true) by (rewrite mk_pc; apply ltb62; lia).
  assert (DL : den E (getr (mk pc x) LIM) = wbv l) by (rewrite (mk_other pc x LIM HCL), HLIM; reflexivity).
  assert (DC : den E (getr (mk pc x) CUR) = den E x) by (rewrite mk_cur; reflexivity).
  assert (NT : forall c r1 r2 off, fi = IBranch c r1 r2 off -> is_guard fi = true ->
               branch_taken c (den E (getr (mk pc x) r1)) (den E (getr (mk pc x) r2)) = false).
  { intros c r1 r2 off -> GG. cbn [is_guard] in GG. destruct c; try discriminate GG.
    -   apply orb_prop in GG as [GG|GG]; apply andb_prop in GG as [G1 G2]; apply r5_eqb_spec in G1, G2; subst r1 r2;
        rewrite DL, DC; cbn [branch_taken]; unfold bv_eqb; rewrite wbv_unsigned; apply Z.eqb_neq; lia.
    -   apply andb_prop in GG as [G1 G2]. apply r5_eqb_spec in G1, G2. subst r1 r2.
      rewrite DL, DC. cbn [branch_taken]. unfold bv_ltu. rewrite wbv_unsigned. apply Z.ltb_ge. lia.
    -   apply andb_prop in GG as [G1 G2]. apply r5_eqb_spec in G1, G2. subst r1 r2.
      rewrite DL, DC. cbn [branch_taken]. unfold bv_ltu. rewrite wbv_unsigned. apply negb_false_iff. apply Z.ltb_lt. lia. }
  destruct fi; try discriminate GI.
  destruct (VdStep.m_branch segs OPS E (mk pc x) ms model w i c rs1 rs2 off (pc4 (mk pc x)) HS Hpc Hf' He Hd Hof) as (ms' & STEP & HS').
  { rewrite (NT c rs1 rs2 off eq_refl GI). reflexivity. }
  apply (astep _ ms ms' model w i _ Hf' He Hd Hof I STEP HS' HMP (so_svc _ _ _ _ _ _ HS) (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS))). intros mo1 HS1' HMP1.
  unfold pc4 in HS1'. rewrite mk_pc, mk_setpc in HS1'.
  apply (IH (PrimInt63.add pc 4%uint63) x ms' mo1 G); [rewrite to_Z_add4 by lia; lia| exact HS1'| exact HMP1| exact HL| exact HK].
Qed.

Lemma loop_cps : forall (n : nat) (x : sv) ms model,
  st_ok segs OPS E (mk PC x) ms model -> MP model ->
  bv_unsigned (den E x) = B + Sz * (Z.of_nat n + 1) -> B + Sz * (Z.of_nat n + 1) < two64 ->
  (forall ms' mo', st_ok segs OPS E (mk EXIT (getr st0 BEG)) ms' mo' -> MP mo' -> realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  destruct pcs as (PA & PBq & PE).
  pose proof (bv_unsigned_in_range _ (den E (getr st0 BEG))) as RB. rewrite bv_modulus_64, HBEG in RB.
  induction n as [|n IH]; intros x ms model0 HS HMP0 HU HW HK.
  all: apply (guards_cps NG PC x ms model0 HG ltac:(lia) HS HMP0 ltac:(rewrite HU; nia)); fold pcA; intros ms1 model HS1 HMP.
  all: destruct (instr_at pcA) as [fa|] eqn:IA; [|discriminate HD]; destruct (instr_at_spec pcA fa IA) as (wa & ia & Hfa & Hea & Hda & Hofa);
       destruct fa; try discriminate HD; destruct op; try discriminate HD; cbn [dec_ok] in HD;
       apply andb_prop in HD as [HD HV]; apply andb_prop in HD as [HD1 HD2]; apply r5_eqb_spec in HD1, HD2; subst rd rs1;
       apply (proj1 (weqb_ok _ _)) in HV; subst v.
  all: destruct (instr_at pcB) as [fb|] eqn:IB; [|discriminate HLA]; destruct (instr_at_spec pcB fb IB) as (wb & ib & Hfb & Heb & Hdb & Hofb);
       destruct fb; try discriminate HLA; destruct c; try discriminate HLA; cbn [latch_ok] in HLA;
       apply andb_prop in HLA as [HR HT]; destruct (pc_add pcB off) as [t|] eqn:PADD; [|discriminate HT];
       apply Uint63.eqb_correct in HT; subst t.
  -
    set (y := getr st0 BEG).
    assert (Hfa' : fetch_word segs (ms_pc_val ms1) = Some wa) by (rewrite (so_pc _ _ _ _ _ _ HS1), mk_pc; exact Hfa).
    destruct (VdStep.m_addi segs OPS E (mk pcA x) ms1 model wa ia CUR CUR _ y HS1 ltac:(rewrite mk_pc; apply ltb62; lia) Hfa' Hea Hda Hofa) as (ms2 & STEP2 & HS2).
    { rewrite mk_cur. apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned, wsub_ok, wzero_ok, wlit_ok, HU, <- HSz. subst y. rewrite HBEG.
      unfold bv_wrap. rewrite bv_modulus_64. unfold two64 in *.
      replace ((0 - Sz) mod 18446744073709551616) with (18446744073709551616 - Sz) by (symmetry; rewrite <- (Z.mod_small (18446744073709551616 - Sz) 18446744073709551616) by lia; rewrite <- Z.mod_add with (b := 1) by lia; f_equal; lia).
      replace (B + Sz * (Z.of_nat 0 + 1) + (18446744073709551616 - Sz)) with (B + 1 * 18446744073709551616) by lia.
      rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
    apply (astep _ ms1 ms2 model wa ia _ Hfa' Hea Hda Hofa I STEP2 HS2 HMP (so_svc _ _ _ _ _ _ HS1) (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS1))). clear HS2. intros model2 HS2 HMP2.
    unfold pc4 in HS2. rewrite mk_pc, mk_setr in HS2. fold pcB in HS2.
    assert (Hfb' : fetch_word segs (ms_pc_val ms2) = Some wb) by (rewrite (so_pc _ _ _ _ _ _ HS2), mk_pc; exact Hfb).
    destruct (VdStep.m_branch segs OPS E (mk pcB y) ms2 model2 wb ib BC_NE rs1 rs2 off (pc4 (mk pcB y)) HS2 ltac:(rewrite mk_pc; apply ltb62; lia) Hfb' Heb Hdb Hofb) as (ms3 & STEP3 & HS3).
    { assert (EQ : branch_taken BC_NE (den E (getr (mk pcB y) rs1)) (den E (getr (mk pcB y) rs2)) = false).
      { cbn [branch_taken]. apply negb_false_iff. unfold bv_eqb. apply Z.eqb_eq.
        apply orb_prop in HR as [HR|HR]; apply andb_prop in HR as [R1 R2]; apply r5_eqb_spec in R1, R2; subst rs1 rs2;
          rewrite mk_cur, (mk_other pcB y BEG HCB); reflexivity. }
      rewrite EQ. reflexivity. }
    apply (astep _ ms2 ms3 model2 wb ib _ Hfb' Heb Hdb Hofb I STEP3 HS3 HMP2 (so_svc _ _ _ _ _ _ HS2) (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS2))). clear HS3. intros model3 HS3 HMP3.
    unfold pc4 in HS3. rewrite mk_pc, mk_setpc in HS3. fold EXIT in HS3. exact (HK ms3 model3 HS3 HMP3).
  -
    set (z := B + Sz * (Z.of_nat n + 1)).
    assert (Zr : 0 <= z < two64) by (subst z; rewrite Nat2Z.inj_succ in HW; nia).
    set (y := VL (Z2w z)).
    assert (Uy : bv_unsigned (den E y) = z) by (subst y; rewrite den_VL, Z2w_ok; apply Z.mod_small; exact Zr).
    assert (Hfa' : fetch_word segs (ms_pc_val ms1) = Some wa) by (rewrite (so_pc _ _ _ _ _ _ HS1), mk_pc; exact Hfa).
    destruct (VdStep.m_addi segs OPS E (mk pcA x) ms1 model wa ia CUR CUR _ y HS1 ltac:(rewrite mk_pc; apply ltb62; lia) Hfa' Hea Hda Hofa) as (ms2 & STEP2 & HS2).
    { rewrite mk_cur. apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned, wsub_ok, wzero_ok, wlit_ok, HU, <- HSz, Uy. subst z.
      unfold bv_wrap. rewrite bv_modulus_64. unfold two64 in *. rewrite Nat2Z.inj_succ in *.
      replace ((0 - Sz) mod 18446744073709551616) with (18446744073709551616 - Sz) by (symmetry; rewrite <- (Z.mod_small (18446744073709551616 - Sz) 18446744073709551616) by lia; rewrite <- Z.mod_add with (b := 1) by lia; f_equal; lia).
      replace (B + Sz * (Z.succ (Z.of_nat n) + 1) + (18446744073709551616 - Sz)) with (B + Sz * (Z.of_nat n + 1) + 1 * 18446744073709551616) by lia.
      rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
    apply (astep _ ms1 ms2 model wa ia _ Hfa' Hea Hda Hofa I STEP2 HS2 HMP (so_svc _ _ _ _ _ _ HS1) (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS1))). clear HS2. intros model2 HS2 HMP2.
    unfold pc4 in HS2. rewrite mk_pc, mk_setr in HS2. fold pcB in HS2.
    assert (Hfb' : fetch_word segs (ms_pc_val ms2) = Some wb) by (rewrite (so_pc _ _ _ _ _ _ HS2), mk_pc; exact Hfb).
    destruct (VdStep.m_branch segs OPS E (mk pcB y) ms2 model2 wb ib BC_NE rs1 rs2 off PC HS2 ltac:(rewrite mk_pc; apply ltb62; lia) Hfb' Heb Hdb Hofb) as (ms3 & STEP3 & HS3).
    { assert (NEQ : branch_taken BC_NE (den E (getr (mk pcB y) rs1)) (den E (getr (mk pcB y) rs2)) = true).
      { cbn [branch_taken]. apply negb_true_iff. unfold bv_eqb. apply Z.eqb_neq.
        apply orb_prop in HR as [HR|HR]; apply andb_prop in HR as [R1 R2]; apply r5_eqb_spec in R1, R2; subst rs1 rs2;
          rewrite mk_cur, (mk_other pcB y BEG HCB), Uy, HBEG; subst z; nia. }
      rewrite NEQ, mk_pc. exact PADD. }
    apply (astep _ ms2 ms3 model2 wb ib _ Hfb' Heb Hdb Hofb I STEP3 HS3 HMP2 (so_svc _ _ _ _ _ _ HS2) (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS2))). clear HS3. intros model3 HS3 HMP3.
    rewrite mk_setpc in HS3.
    apply (IH y ms3 model3 HS3 HMP3); [rewrite Uy; subst z; lia| subst z; lia| exact HK].
Qed.

End Loop.

Lemma rf_set_get : forall A (x : rf A) r, rf_set x r (rf_get x r) = x.
Proof. intros A x r; destruct x, r; reflexivity. Qed.

Lemma mk_self : forall st, r5_eqb CUR X0 = false -> s_pc st = PC -> mk st PC (getr st CUR) = st.
Proof.
  intros st HX0 Hpc. unfold mk. rewrite (setr_eq _ CUR _ HX0). unfold setpc, getr. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  rewrite rf_set_get, <- Hpc. destruct st; reflexivity.
Qed.

Lemma find_f1_In : forall fs0 fs cur beg j, find_f1 fs0 fs cur beg = Some j ->
  exists f, In f fs /\ f1_match fs0 cur beg f = Some j.
Proof.
  induction fs as [|f fs IH]; intros cur beg j H; cbn [find_f1] in H; [discriminate|].
  destruct (f1_match fs0 cur beg f) as [j'|] eqn:M.
  - injection H as <-. exists f. split; [left; reflexivity| exact M].
  - destruct (IH cur beg j H) as (f' & I & M'). exists f'. split; [right; exact I| exact M'].
Qed.

Theorem vd_sound : contract_sound segs OPS MP PB vd_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [vd_contract c_apply c_pc] in HA, Hpc. unfold vd_apply in HA.
  destruct (getr st LIM) as [l| | | | | | | | | |] eqn:HLIM; try discriminate HA.
  match type of HA with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate HA] end. injection HA as <-.
  apply andb_prop in COND as [COND Cne]. apply andb_prop in COND as [COND Clim].
  apply andb_prop in COND as [COND Cwit]. apply andb_prop in COND as [COND Clatch]. apply andb_prop in COND as [COND Cdec].
  apply andb_prop in COND as [COND Cg]. apply andb_prop in COND as [COND Cs32]. apply andb_prop in COND as [COND Cs1].
  apply andb_prop in COND as [COND Cex]. apply andb_prop in COND as [COND Cng]. apply andb_prop in COND as [COND Cpc].
  apply andb_prop in COND as [COND Ccl]. apply andb_prop in COND as [Cx0 Ccb].
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.

  apply negb_true_iff in Cx0.
  assert (HCB : CUR <> BEG) by (intros X; rewrite <- X, r5_eqb_refl in Ccb; discriminate Ccb).
  assert (HCL : CUR <> LIM) by (intros X; rewrite <- X, r5_eqb_refl in Ccl; discriminate Ccl).
  apply Uint63.ltb_spec in Cpc, Cex. change (to_Z bit62i) with (2 ^ 62) in Cpc, Cex. apply Nat.leb_le in Cng.
  apply Uint63.leb_spec in Cs1, Cs32. change (to_Z 1%uint63) with 1 in Cs1. change (to_Z 32%uint63) with 32 in Cs32.
  unfold dec_false, dec_true in Clim, Cne.
  destruct (decide_ltu (s_facts st) (VL l) (getr st BEG)) as [[|]|] eqn:D1; try discriminate Clim.
  destruct (decide_eq (s_facts st) (getr st CUR) (getr st BEG)) as [[|]|] eqn:D0; try discriminate Cne.
  apply (decide_ltu_sound E _ FH) in D1. apply (decide_eq_sound E _ FH) in D0.
  unfold bv_ltu in D1. unfold bv_eqb in D0. apply Z.ltb_lt in D1. apply Z.eqb_neq in D0.
  rewrite den_VL in D1.
  set (Bz := bv_unsigned (den E (getr st BEG))) in *. set (Cz := bv_unsigned (den E (getr st CUR))) in *. set (Sz := to_Z S) in *.
  pose proof (bv_unsigned_in_range _ (den E (getr st BEG))) as RB. rewrite bv_modulus_64 in RB. fold Bz in RB.

  assert (F2Z : forall j, dec_false (decide_ltu (s_facts st) (VL VD_MAX) (VP j wzero)) = true -> bv_unsigned (ev E j) <= 288230376151711744).
  { intros j Cf2. unfold dec_false in Cf2.
    destruct (decide_ltu (s_facts st) (VL VD_MAX) (VP j wzero)) as [[|]|] eqn:D3; try discriminate Cf2.
    apply (decide_ltu_sound E _ FH) in D3. unfold bv_ltu in D3. apply Z.ltb_ge in D3.
    rewrite den_VL in D3. rewrite (den_VP0 E j wzero (weqb_refl _)) in D3.
    unfold VD_MAX in D3. rewrite wlit_ok in D3. change (to_Z 288230376151711744%uint63) with 288230376151711744 in D3. exact D3. }

  assert (COUNT : forall j, Bz <= Cz -> dec_false (decide_ltu (s_facts st) (VL VD_MAX) (VP j wzero)) = true ->
            Cz = (Bz + (bv_unsigned (ev E j) * Sz) mod two64) mod two64 -> exists J, Cz = Bz + J * Sz /\ 1 <= J).
  { intros j D2 Cf2 Hf. pose proof (F2Z j Cf2) as D3.
    set (J := bv_unsigned (ev E j)) in *.
    pose proof (bv_unsigned_in_range _ (ev E j)) as RJ. rewrite bv_modulus_64 in RJ. fold J in RJ. unfold two64 in *.
    assert (JS : 0 <= J * Sz < 18446744073709551616) by nia.
    rewrite (Z.mod_small (J * Sz)) in Hf by exact JS.
    assert (CE : Cz = Bz + J * Sz).
    { destruct (Z_lt_le_dec (Bz + J * Sz) 18446744073709551616) as [LT|GE]; [rewrite Z.mod_small in Hf by lia; exact Hf|].
      exfalso. replace (Bz + J * Sz) with (Bz + J * Sz - 18446744073709551616 + 1 * 18446744073709551616) in Hf by lia.
      rewrite Z.mod_add, Z.mod_small in Hf by lia. lia. }
    exists J. split; [exact CE| nia]. }
  assert (WIT : exists J, Cz = Bz + J * Sz /\ 1 <= J).
  { destruct (cur_shape (s_facts st) (getr st CUR) (getr st BEG)) as [j|] eqn:CS.
    -
      pose proof (F2Z j Cwit) as D3. unfold cur_shape in CS.
      destruct (getr st CUR) as [?|? ?|op b m|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?] eqn:GC; try discriminate CS. destruct op; try discriminate CS.
      destruct b as [?|kb ob|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate CS.
      destruct m as [?|? ?|? ? ?|? ? ?|mo mj ms_|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate CS. destruct mo; try discriminate CS.
      destruct mj as [?|j' o|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate CS.
      destruct ms_ as [s|? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate CS.
      destruct (getr st BEG) as [?|kb' ob'|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?] eqn:GB; try discriminate CS.
      match type of CS with (if ?c then _ else _) = _ => destruct c eqn:FC; [|discriminate CS] end. injection CS as ->.
      apply andb_prop in FC as [FC QHI]. apply andb_prop in FC as [FC QMOD]. apply andb_prop in FC as [FC QLE].
      apply andb_prop in FC as [FC QT]. apply andb_prop in FC as [FC QB0]. apply andb_prop in FC as [FC QK]. apply andb_prop in FC as [QO QS].
      apply (proj1 (weqb_ok _ _)) in QS. subst s. apply Uint63.eqb_correct in QK. subst kb'.
      apply negb_true_iff in QT. apply Uint63.leb_spec in QLE. change (to_Z 512%uint63) with 512 in QLE.
      apply Uint63.eqb_correct in QMOD. apply (f_equal to_Z) in QMOD. rewrite Uint63.mod_spec in QMOD. change (to_Z 0%uint63) with 0 in QMOD. fold Sz in QMOD.

      pose proof (sv_bounds_sound E (s_facts st) FH (VP kb ob')) as BB. unfold inb in BB. destruct BB as [_ BB].
      rewrite wleu_w2Z in QHI. apply Z.leb_le in QHI. unfold BEG_MAX in QHI. rewrite wlit_ok in QHI.
      change (to_Z 4611686018427387904%uint63) with 4611686018427387904 in QHI. fold Bz in BB.
      assert (BZ62 : Bz <= 4611686018427387904) by lia.

      assert (BV : Bz = bv_unsigned (ev E kb)) by (subst Bz; exact (den_VP0 E kb ob' QB0)).
      assert (OBZ : w2Z ob = to_Z (wl ob)) by (unfold w2Z; rewrite QT; reflexivity).
      pose proof (Uint63.to_Z_bounded (wl ob)) as RO.
      set (J := bv_unsigned (ev E j)) in *.
      pose proof (bv_unsigned_in_range _ (ev E j)) as RJ. rewrite bv_modulus_64 in RJ. fold J in RJ.
      assert (CV : Cz = Bz + to_Z (wl ob) + J * Sz).
      { subst Cz.
        change (den E (VAlu ALU_ADD (VP kb ob) (VMd M_MUL (VP j o) (VL (wlit S))))) with (bv_add (den E (VP kb ob)) (bv_mul (den E (VP j o)) (den E (VL (wlit S))))).
        rewrite bv_add_unsigned, bv_mul_unsigned, (den_VP0 E j o QO), den_VL, wlit_ok. fold J Sz.
        cbn [den]. rewrite bv_add_unsigned, wbv_unsigned, OBZ, <- BV. unfold bv_wrap. rewrite bv_modulus_64. unfold two64 in *.
        rewrite (Z.mod_small (Bz + to_Z (wl ob))) by lia. rewrite (Z.mod_small (J * Sz)) by nia. rewrite Z.mod_small by nia. lia. }
      pose proof (Z_div_mod_eq_full (to_Z (wl ob)) Sz) as DQ. rewrite QMOD in DQ.
      assert (QN : 0 <= to_Z (wl ob) / Sz) by (apply Z.div_pos; lia).
      exists (J + to_Z (wl ob) / Sz). split; [rewrite CV; nia|].
      assert (NEQ : Cz <> Bz) by exact D0. rewrite CV in NEQ. nia.
    - match type of Cwit with (if ?c then _ else _) = true => destruct c eqn:Cnw; [|discriminate Cwit] end.
      unfold dec_false in Cnw.
      destruct (decide_ltu (s_facts st) (getr st CUR) (getr st BEG)) as [[|]|] eqn:D2; try discriminate Cnw.
      apply (decide_ltu_sound E _ FH) in D2. unfold bv_ltu in D2. apply Z.ltb_ge in D2. fold Bz Cz in D2.
      destruct (find_f1 (s_facts st) (s_facts st) (getr st CUR) (getr st BEG)) as [j|] eqn:FF.
      +
        apply (COUNT j D2 Cwit).
        destruct (find_f1_In _ _ _ _ _ FF) as (f & INf & FM).
        pose proof (proj1 (Forall_forall _ _) FH f INf) as Hf.
        unfold f1_match in FM. destruct f as [? ? ?|? ?|? ?|? ?|e rhs|? ?|? ?|? ?]; try discriminate FM.
        destruct rhs as [?|? ?|op b m|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate FM. destruct op; try discriminate FM.
        destruct m as [?|? ?|? ? ?|? ? ?|mo mj ms_|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate FM. destruct mo; try discriminate FM.
        destruct mj as [?|j' o|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate FM.
        destruct ms_ as [s|? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate FM.
        match type of FM with (if ?c then _ else _) = _ => destruct c eqn:FC; [|discriminate FM] end. injection FM as ->.
        repeat match type of FC with (_ && _) = true => let X := fresh "Q" in apply andb_prop in FC as [FC X] end.
        unfold dec_true in Q0, Q.
        destruct (decide_eq (s_facts st) e (getr st CUR)) as [[|]|] eqn:DE; try discriminate Q0.
        destruct (decide_eq (s_facts st) b (getr st BEG)) as [[|]|] eqn:DB; try discriminate Q.
        apply (decide_eq_sound E _ FH) in DE, DB. unfold bv_eqb in DE, DB. apply Z.eqb_eq in DE, DB.
        apply (proj1 (weqb_ok _ _)) in Q1. subst s.
        cbn [fact_holds] in Hf. apply (f_equal bv_unsigned) in Hf.
        change (den E (VAlu ALU_ADD b (VMd M_MUL (VP j o) (VL (wlit S))))) with (bv_add (den E b) (bv_mul (den E (VP j o)) (den E (VL (wlit S))))) in Hf.
        rewrite bv_add_unsigned, bv_mul_unsigned, (den_VP0 E j o FC), den_VL, wlit_ok, DE, DB in Hf.
        unfold bv_wrap in Hf. rewrite bv_modulus_64 in Hf. fold Bz Cz Sz in Hf. exact Hf.
      +
        unfold align_ok in Cwit. apply andb_prop in Cwit as [Cwit ALB]. apply andb_prop in Cwit as [ES ALC].
        apply Uint63.eqb_correct in ES.
        assert (S8 : Sz = 8) by (subst Sz; rewrite ES; reflexivity).
        pose proof (aligned8_sound E (s_facts st) (getr st CUR) FH ALC) as MC.
        pose proof (aligned8_sound E (s_facts st) (getr st BEG) FH ALB) as MB.
        fold Cz in MC. fold Bz in MB.
        exists ((Cz - Bz) / 8). rewrite S8.
        assert (DM : (Cz - Bz) mod 8 = 0) by (rewrite Zminus_mod, MC, MB; reflexivity).
        pose proof (Z_div_mod_eq_full (Cz - Bz) 8) as DE. rewrite DM in DE. split; lia. }
  destruct WIT as (J & CE & J1).

  rewrite <- (mk_self st Cx0 Hpc) in HS.
  apply (loop_cps E K st l Bz Sz Cx0 HCB HCL HLIM eq_refl D1 eq_refl ltac:(lia) Cpc Cng Cex Cg Cdec Clatch (Z.to_nat (J - 1)) (getr st CUR) ms model HS HMP).
  - fold Cz. rewrite CE, Z2Nat.id by lia. lia.
  - rewrite Z2Nat.id by lia. pose proof (bv_unsigned_in_range _ (den E (getr st CUR))) as RC. rewrite bv_modulus_64 in RC. fold Cz in RC. unfold two64 in *. nia.
  - intros ms' mo' HS' HMP'. exact (Hk _ (or_introl eq_refl) E ms' mo' (env_ext_refl (s_next st) E) HMP' HS').
Qed.

Lemma vd_contract_eq : vd_contract = VDestroy.VD.vd_contract segs PC CUR BEG LIM S NG.
Proof. reflexivity. Qed.
Theorem vd_sound_acc : contract_sound segs OPS MP PB (VDestroy.VD.vd_contract segs PC CUR BEG LIM S NG).
Proof. rewrite <- vd_contract_eq. exact vd_sound. Qed.

End Sound.
End WithPc.
End WithSegs.
End VDA.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Notation OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundAlu OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.VdStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAcc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Acc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.AccStep.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepA PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module VDA.
Section WithSegs.
Variable segs : list Segment.

Definition instr_at (pc : int) : option finstr :=
  match fetch_word segs (Z_to_bv 64 (to_Z pc)) with
  | Some w =>
      if is_ecall w then None else
      match decode_any w with
      | Some (i, z) => if Z.eqb z 4 then of_instr i else None
      | None => None
      end
  | None => None
  end.

Lemma instr_at_spec : forall pc fi, instr_at pc = Some fi ->
  exists w i, fetch_word segs (Z_to_bv 64 (to_Z pc)) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z) /\ of_instr i = Some fi.
Proof.
  intros pc fi H. unfold instr_at in H.
  destruct (fetch_word segs (Z_to_bv 64 (to_Z pc))) as [w|] eqn:F; [|discriminate].
  destruct (is_ecall w) eqn:EC; [discriminate|].
  destruct (decode_any w) as [[i z]|] eqn:D; [|discriminate].
  destruct (Z.eqb_spec z 4); [|discriminate]. subst z. exists w, i. auto.
Qed.

Section WithPc.
Variable PC : int.
Variables CUR BEG LIM : r5.
Variable S : int.
Variable NG : nat.

Fixpoint pc_after (pc : int) (n : nat) : int :=
  match n with O => pc | Datatypes.S n' => pc_after (PrimInt63.add pc 4%uint63) n' end.

Definition pcA : int := pc_after PC NG.
Definition pcB : int := PrimInt63.add pcA 4%uint63.
Definition EXIT : int := PrimInt63.add pcB 4%uint63.

Definition is_guard (fi : finstr) : bool :=
  match fi with
  | IBranch BC_GEU r1 r2 _ => r5_eqb r1 LIM && r5_eqb r2 CUR
  | IBranch BC_LTU r1 r2 _ => r5_eqb r1 CUR && r5_eqb r2 LIM
  | IBranch BC_EQ r1 r2 _ => (r5_eqb r1 CUR && r5_eqb r2 LIM) || (r5_eqb r1 LIM && r5_eqb r2 CUR)
  | _ => false
  end.

Fixpoint guards_ok (pc : int) (n : nat) : bool :=
  match n with
  | O => true
  | Datatypes.S n' => match instr_at pc with Some fi => is_guard fi && guards_ok (PrimInt63.add pc 4%uint63) n' | None => false end
  end.

Definition dec_ok (fi : finstr) : bool :=
  match fi with
  | IOpImm ALU_ADD rd rs v => r5_eqb rd CUR && r5_eqb rs CUR && weqb v (wsub wzero (wlit S))
  | _ => false
  end.
Definition latch_ok (fi : finstr) : bool :=
  match fi with
  | IBranch BC_NE r1 r2 off =>
      ((r5_eqb r1 CUR && r5_eqb r2 BEG) || (r5_eqb r1 BEG && r5_eqb r2 CUR))
      && match pc_add pcB off with Some t => PrimInt63.eqb t PC | None => false end
  | _ => false
  end.

Definition VD_MAX : w64 := wlit 288230376151711744%uint63.

Definition f1_match (fs : list fact) (cur beg : sv) (f : fact) : option int :=
  match f with
  | FEq e (VAlu ALU_ADD b (VMd M_MUL (VP j o) (VL s))) =>
      if weqb o wzero && weqb s (wlit S) && dec_true (decide_eq fs e cur) && dec_true (decide_eq fs b beg) then Some j else None
  | _ => None
  end.
Fixpoint find_f1 (fs0 fs : list fact) (cur beg : sv) : option int :=
  match fs with
  | [] => None
  | f :: fs' => match f1_match fs0 cur beg f with Some j => Some j | None => find_f1 fs0 fs' cur beg end
  end.

Definition BEG_MAX : w64 := wlit 4611686018427387904%uint63.
Definition cur_shape (fs : list fact) (cur beg : sv) : option int :=
  match cur, beg with
  | VAlu ALU_ADD (VP kb ob) (VMd M_MUL (VP j o) (VL s)), VP kb' ob' =>

      if weqb o wzero && weqb s (wlit S) && PrimInt63.eqb kb kb' && weqb ob' wzero && negb (wt ob)
         && PrimInt63.leb (wl ob) 512%uint63 && PrimInt63.eqb (PrimInt63.mod (wl ob) S) 0%uint63
         && wleu (snd (sv_bounds fs beg)) BEG_MAX
      then Some j else None
  | _, _ => None
  end.

Definition aligned8 (fs : list fact) (v : sv) : bool :=
  match v with
  | VAlu ALU_ADD a c => aligned fs a 3%uint63 && aligned fs c 3%uint63
  | _ => aligned fs v 3%uint63
  end.
Definition align_ok (fs : list fact) (cur beg : sv) : bool :=
  PrimInt63.eqb S 8%uint63 && aligned8 fs cur && aligned8 fs beg.

Definition vd_apply (st : sstate) : option (list sstate) :=
  let fs := s_facts st in let cur := getr st CUR in let beg := getr st BEG in
  match getr st LIM with
  | VL l =>
      if negb (r5_eqb CUR X0) && negb (r5_eqb CUR BEG) && negb (r5_eqb CUR LIM)
         && PrimInt63.ltb PC bit62i && Nat.leb NG 8 && PrimInt63.ltb EXIT bit62i
         && PrimInt63.leb 1%uint63 S && PrimInt63.leb S 32%uint63
         && guards_ok PC NG
         && match instr_at pcA with Some fi => dec_ok fi | None => false end
         && match instr_at pcB with Some fi => latch_ok fi | None => false end
         && match cur_shape fs cur beg with
            | Some j => dec_false (decide_ltu fs (VL VD_MAX) (VP j wzero))
            | None =>
                if dec_false (decide_ltu fs cur beg) then
                  match find_f1 fs fs cur beg with
                  | Some j => dec_false (decide_ltu fs (VL VD_MAX) (VP j wzero))
                  | None => align_ok fs cur beg
                  end
                else false
            end
         && dec_true (decide_ltu fs (VL l) beg)
         && dec_false (decide_eq fs cur beg)
      then Some [setpc (setr st CUR beg) EXIT] else None
  | _ => None
  end.

Definition vd_contract : contract := Contract PC vd_apply.

Section Sound.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Lemma noacc : forall i fi, of_instr i = Some fi ->
  match fi with IBranch _ _ _ _ => True | IOpImm _ _ _ _ => True | _ => False end ->
  forall c a n, Acc.mem_acc i c a n -> False.
Proof.
  intros i fi Hof FI c a n M. destruct i; cbn [Acc.mem_acc] in M; try exact M; cbn [of_instr] in Hof;
    repeat match type of Hof with
           | Some _ = Some _ => injection Hof as <-; exact FI
           | None = Some _ => discriminate Hof
           | (if ?b then _ else _) = Some _ => destruct b
           | match ?x with _ => _ end = Some _ => destruct x
           end.
Qed.

Lemma aligned8_sound : forall E fs v, facts_hold E fs -> aligned8 fs v = true -> bv_unsigned (den E v) mod 8 = 0.
Proof.
  intros E fs v FH H.
  assert (A1 : forall a, aligned fs a 3%uint63 = true -> bv_unsigned (den E a) mod 8 = 0).
  { intros a Ha. pose proof (aligned_sound E fs FH a 3%uint63 Ha ltac:(change (to_Z 3%uint63) with 3; lia)) as M.
    change (to_Z 3%uint63) with 3 in M. change (2 ^ 3) with 8 in M. exact M. }
  destruct v as [| |op a c| | | | | | | |]; try exact (A1 _ H). destruct op; try exact (A1 _ H).
  cbn [aligned8] in H. apply andb_prop in H as [Ha Hc].
  change (den E (VAlu ALU_ADD a c)) with (bv_add (den E a) (den E c)). rewrite bv_add_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
  change 8 with (2 ^ 3). rewrite (mod64_mod _ 3) by lia. change (2 ^ 3) with 8. rewrite Zplus_mod, (A1 a Ha), (A1 c Hc). reflexivity.
Qed.

Lemma rf_set_set : forall A (x : rf A) r v v', rf_set (rf_set x r v) r v' = rf_set x r v'.
Proof. intros A x r v v'; destruct r; reflexivity. Qed.

Lemma to_Z_add4 : forall pc, to_Z pc + 4 < 2 ^ 63 -> to_Z (PrimInt63.add pc 4%uint63) = to_Z pc + 4.
Proof.
  intros pc H. rewrite Uint63.add_spec. change (to_Z 4%uint63) with 4. apply Z.mod_small.
  pose proof (Uint63.to_Z_bounded pc). change wB with (2 ^ 63). lia.
Qed.

Lemma to_Z_pc_after : forall n pc, to_Z pc + 4 * Z.of_nat n < 2 ^ 63 -> to_Z (pc_after pc n) = to_Z pc + 4 * Z.of_nat n.
Proof.
  induction n as [|n IH]; intros pc H; cbn [pc_after]; [lia|].
  rewrite IH; rewrite to_Z_add4 by lia; lia.
Qed.

Lemma ltb62 : forall pc, to_Z pc < 2 ^ 62 -> PrimInt63.ltb pc bit62i = true.
Proof. intros pc H. apply Uint63.ltb_spec. change (to_Z bit62i) with (2 ^ 62). exact H. Qed.

Section Loop.
Variable E : env.
Variable K : TSet.
Variable st0 : sstate.
Variable l : w64.
Variables B Sz : Z.
Hypothesis HX0 : r5_eqb CUR X0 = false.
Hypothesis HCB : CUR <> BEG.
Hypothesis HCL : CUR <> LIM.
Hypothesis HLIM : getr st0 LIM = VL l.
Hypothesis HBEG : bv_unsigned (den E (getr st0 BEG)) = B.
Hypothesis HLB : w2Z l < B.
Hypothesis HSz : Sz = to_Z S.
Hypothesis HSR : 1 <= Sz <= 32.
Hypothesis HPC : to_Z PC < 2 ^ 62.
Hypothesis HNG : (NG <= 8)%nat.
Hypothesis HEX : to_Z EXIT < 2 ^ 62.
Hypothesis HG : guards_ok PC NG = true.
Hypothesis HD : match instr_at pcA with Some fi => dec_ok fi | None => false end = true.
Hypothesis HLA : match instr_at pcB with Some fi => latch_ok fi | None => false end = true.

Definition mk (p : int) (x : sv) : sstate := setpc (setr st0 CUR x) p.

Lemma mk_setpc : forall p x q, setpc (mk p x) q = mk q x.
Proof. reflexivity. Qed.
Lemma mk_setr : forall p x y q, setpc (setr (mk p x) CUR y) q = mk q y.
Proof.
  intros p x y q. unfold mk. rewrite !(setr_eq _ CUR _ HX0). unfold setpc. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  rewrite rf_set_set. reflexivity.
Qed.
Lemma mk_pc : forall p x, s_pc (mk p x) = p.
Proof. reflexivity. Qed.
Lemma mk_cur : forall p x, getr (mk p x) CUR = x.
Proof. intros p x. unfold mk, getr. rewrite (setr_eq _ CUR _ HX0). cbn [setpc s_rf]. apply rf_get_set_same. Qed.
Lemma mk_other : forall p x r, CUR <> r -> getr (mk p x) r = getr st0 r.
Proof. intros p x r NE. unfold mk, getr. rewrite (setr_eq _ CUR _ HX0). cbn [setpc s_rf]. apply rf_get_set_other. exact NE. Qed.

Lemma pcs : to_Z pcA = to_Z PC + 4 * Z.of_nat NG /\ to_Z pcB = to_Z pcA + 4 /\ to_Z EXIT = to_Z pcB + 4.
Proof.
  assert (A : to_Z pcA = to_Z PC + 4 * Z.of_nat NG) by (unfold pcA; apply to_Z_pc_after; lia).
  assert (Bq : to_Z pcB = to_Z pcA + 4) by (unfold pcB; apply to_Z_add4; lia).
  split; [exact A|]. split; [exact Bq|]. unfold EXIT. apply to_Z_add4. lia.
Qed.

Lemma astep : forall st' ms ms' model w i fi,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) -> of_instr i = Some fi ->
  match fi with IBranch _ _ _ _ => True | IOpImm _ _ _ _ => True | _ => False end ->
  RiscvSemantics.step segs ms = MachineOk ms' -> st_ok segs OPS E st' ms' model -> MP model ->
  ms_svc_pending ms = None -> m_halted model = None ->
  (forall mo', st_ok segs OPS E st' ms' mo' -> MP mo' -> realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros st' ms ms' model w i fi Hf He Hd Hof FI STEP HS' HMP Hsvc Hh HK.
  destruct (AccStep.st_ok_account_mp segs OPS (AccStep.CH_cov OPS) (AccStep.LAW_cov OPS) MP HMPA E st' ms ms' model w i Hf He Hd STEP HS' HMP) as (mo' & AS & HS2 & HMP2).
  { intros a n j M _. exfalso. exact (noacc i fi Hof FI _ a n M). }
  exact (rz_astep segs ms model ms' mo' K Hh Hsvc AS (HK mo' HS2 HMP2)).
Qed.

Lemma guards_cps : forall n pc x ms model,
  guards_ok pc n = true -> to_Z pc + 4 * Z.of_nat n < 2 ^ 62 ->
  st_ok segs OPS E (mk pc x) ms model -> MP model -> w2Z l < bv_unsigned (den E x) ->
  (forall ms' mo', st_ok segs OPS E (mk (pc_after pc n) x) ms' mo' -> MP mo' -> realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  induction n as [|n IH]; intros pc x ms model G Hb HS HMP HL HK; cbn [pc_after guards_ok] in *; [exact (HK ms model HS HMP)|].
  destruct (instr_at pc) as [fi|] eqn:IA; [|discriminate G]. apply andb_prop in G as [GI G].
  destruct (instr_at_spec pc fi IA) as (w & i & Hf & He & Hd & Hof).
  assert (Hf' : fetch_word segs (ms_pc_val ms) = Some w) by (rewrite (so_pc _ _ _ _ _ _ HS), mk_pc; exact Hf).
  assert (Hpc : PrimInt63.ltb (s_pc (mk pc x)) bit62i = true) by (rewrite mk_pc; apply ltb62; lia).
  assert (DL : den E (getr (mk pc x) LIM) = wbv l) by (rewrite (mk_other pc x LIM HCL), HLIM; reflexivity).
  assert (DC : den E (getr (mk pc x) CUR) = den E x) by (rewrite mk_cur; reflexivity).
  assert (NT : forall c r1 r2 off, fi = IBranch c r1 r2 off -> is_guard fi = true ->
               branch_taken c (den E (getr (mk pc x) r1)) (den E (getr (mk pc x) r2)) = false).
  { intros c r1 r2 off -> GG. cbn [is_guard] in GG. destruct c; try discriminate GG.
    -   apply orb_prop in GG as [GG|GG]; apply andb_prop in GG as [G1 G2]; apply r5_eqb_spec in G1, G2; subst r1 r2;
        rewrite DL, DC; cbn [branch_taken]; unfold bv_eqb; rewrite wbv_unsigned; apply Z.eqb_neq; lia.
    -   apply andb_prop in GG as [G1 G2]. apply r5_eqb_spec in G1, G2. subst r1 r2.
      rewrite DL, DC. cbn [branch_taken]. unfold bv_ltu. rewrite wbv_unsigned. apply Z.ltb_ge. lia.
    -   apply andb_prop in GG as [G1 G2]. apply r5_eqb_spec in G1, G2. subst r1 r2.
      rewrite DL, DC. cbn [branch_taken]. unfold bv_ltu. rewrite wbv_unsigned. apply negb_false_iff. apply Z.ltb_lt. lia. }
  destruct fi; try discriminate GI.
  destruct (VdStep.m_branch segs OPS E (mk pc x) ms model w i c rs1 rs2 off (pc4 (mk pc x)) HS Hpc Hf' He Hd Hof) as (ms' & STEP & HS').
  { rewrite (NT c rs1 rs2 off eq_refl GI). reflexivity. }
  apply (astep _ ms ms' model w i _ Hf' He Hd Hof I STEP HS' HMP (so_svc _ _ _ _ _ _ HS) (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS))). intros mo1 HS1' HMP1.
  unfold pc4 in HS1'. rewrite mk_pc, mk_setpc in HS1'.
  apply (IH (PrimInt63.add pc 4%uint63) x ms' mo1 G); [rewrite to_Z_add4 by lia; lia| exact HS1'| exact HMP1| exact HL| exact HK].
Qed.

Lemma loop_cps : forall (n : nat) (x : sv) ms model,
  st_ok segs OPS E (mk PC x) ms model -> MP model ->
  bv_unsigned (den E x) = B + Sz * (Z.of_nat n + 1) -> B + Sz * (Z.of_nat n + 1) < two64 ->
  (forall ms' mo', st_ok segs OPS E (mk EXIT (getr st0 BEG)) ms' mo' -> MP mo' -> realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  destruct pcs as (PA & PBq & PE).
  pose proof (bv_unsigned_in_range _ (den E (getr st0 BEG))) as RB. rewrite bv_modulus_64, HBEG in RB.
  induction n as [|n IH]; intros x ms model0 HS HMP0 HU HW HK.
  all: apply (guards_cps NG PC x ms model0 HG ltac:(lia) HS HMP0 ltac:(rewrite HU; nia)); fold pcA; intros ms1 model HS1 HMP.
  all: destruct (instr_at pcA) as [fa|] eqn:IA; [|discriminate HD]; destruct (instr_at_spec pcA fa IA) as (wa & ia & Hfa & Hea & Hda & Hofa);
       destruct fa; try discriminate HD; destruct op; try discriminate HD; cbn [dec_ok] in HD;
       apply andb_prop in HD as [HD HV]; apply andb_prop in HD as [HD1 HD2]; apply r5_eqb_spec in HD1, HD2; subst rd rs1;
       apply (proj1 (weqb_ok _ _)) in HV; subst v.
  all: destruct (instr_at pcB) as [fb|] eqn:IB; [|discriminate HLA]; destruct (instr_at_spec pcB fb IB) as (wb & ib & Hfb & Heb & Hdb & Hofb);
       destruct fb; try discriminate HLA; destruct c; try discriminate HLA; cbn [latch_ok] in HLA;
       apply andb_prop in HLA as [HR HT]; destruct (pc_add pcB off) as [t|] eqn:PADD; [|discriminate HT];
       apply Uint63.eqb_correct in HT; subst t.
  -
    set (y := getr st0 BEG).
    assert (Hfa' : fetch_word segs (ms_pc_val ms1) = Some wa) by (rewrite (so_pc _ _ _ _ _ _ HS1), mk_pc; exact Hfa).
    destruct (VdStep.m_addi segs OPS E (mk pcA x) ms1 model wa ia CUR CUR _ y HS1 ltac:(rewrite mk_pc; apply ltb62; lia) Hfa' Hea Hda Hofa) as (ms2 & STEP2 & HS2).
    { rewrite mk_cur. apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned, wsub_ok, wzero_ok, wlit_ok, HU, <- HSz. subst y. rewrite HBEG.
      unfold bv_wrap. rewrite bv_modulus_64. unfold two64 in *.
      replace ((0 - Sz) mod 18446744073709551616) with (18446744073709551616 - Sz) by (symmetry; rewrite <- (Z.mod_small (18446744073709551616 - Sz) 18446744073709551616) by lia; rewrite <- Z.mod_add with (b := 1) by lia; f_equal; lia).
      replace (B + Sz * (Z.of_nat 0 + 1) + (18446744073709551616 - Sz)) with (B + 1 * 18446744073709551616) by lia.
      rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
    apply (astep _ ms1 ms2 model wa ia _ Hfa' Hea Hda Hofa I STEP2 HS2 HMP (so_svc _ _ _ _ _ _ HS1) (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS1))). clear HS2. intros model2 HS2 HMP2.
    unfold pc4 in HS2. rewrite mk_pc, mk_setr in HS2. fold pcB in HS2.
    assert (Hfb' : fetch_word segs (ms_pc_val ms2) = Some wb) by (rewrite (so_pc _ _ _ _ _ _ HS2), mk_pc; exact Hfb).
    destruct (VdStep.m_branch segs OPS E (mk pcB y) ms2 model2 wb ib BC_NE rs1 rs2 off (pc4 (mk pcB y)) HS2 ltac:(rewrite mk_pc; apply ltb62; lia) Hfb' Heb Hdb Hofb) as (ms3 & STEP3 & HS3).
    { assert (EQ : branch_taken BC_NE (den E (getr (mk pcB y) rs1)) (den E (getr (mk pcB y) rs2)) = false).
      { cbn [branch_taken]. apply negb_false_iff. unfold bv_eqb. apply Z.eqb_eq.
        apply orb_prop in HR as [HR|HR]; apply andb_prop in HR as [R1 R2]; apply r5_eqb_spec in R1, R2; subst rs1 rs2;
          rewrite mk_cur, (mk_other pcB y BEG HCB); reflexivity. }
      rewrite EQ. reflexivity. }
    apply (astep _ ms2 ms3 model2 wb ib _ Hfb' Heb Hdb Hofb I STEP3 HS3 HMP2 (so_svc _ _ _ _ _ _ HS2) (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS2))). clear HS3. intros model3 HS3 HMP3.
    unfold pc4 in HS3. rewrite mk_pc, mk_setpc in HS3. fold EXIT in HS3. exact (HK ms3 model3 HS3 HMP3).
  -
    set (z := B + Sz * (Z.of_nat n + 1)).
    assert (Zr : 0 <= z < two64) by (subst z; rewrite Nat2Z.inj_succ in HW; nia).
    set (y := VL (Z2w z)).
    assert (Uy : bv_unsigned (den E y) = z) by (subst y; rewrite den_VL, Z2w_ok; apply Z.mod_small; exact Zr).
    assert (Hfa' : fetch_word segs (ms_pc_val ms1) = Some wa) by (rewrite (so_pc _ _ _ _ _ _ HS1), mk_pc; exact Hfa).
    destruct (VdStep.m_addi segs OPS E (mk pcA x) ms1 model wa ia CUR CUR _ y HS1 ltac:(rewrite mk_pc; apply ltb62; lia) Hfa' Hea Hda Hofa) as (ms2 & STEP2 & HS2).
    { rewrite mk_cur. apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned, wsub_ok, wzero_ok, wlit_ok, HU, <- HSz, Uy. subst z.
      unfold bv_wrap. rewrite bv_modulus_64. unfold two64 in *. rewrite Nat2Z.inj_succ in *.
      replace ((0 - Sz) mod 18446744073709551616) with (18446744073709551616 - Sz) by (symmetry; rewrite <- (Z.mod_small (18446744073709551616 - Sz) 18446744073709551616) by lia; rewrite <- Z.mod_add with (b := 1) by lia; f_equal; lia).
      replace (B + Sz * (Z.succ (Z.of_nat n) + 1) + (18446744073709551616 - Sz)) with (B + Sz * (Z.of_nat n + 1) + 1 * 18446744073709551616) by lia.
      rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
    apply (astep _ ms1 ms2 model wa ia _ Hfa' Hea Hda Hofa I STEP2 HS2 HMP (so_svc _ _ _ _ _ _ HS1) (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS1))). clear HS2. intros model2 HS2 HMP2.
    unfold pc4 in HS2. rewrite mk_pc, mk_setr in HS2. fold pcB in HS2.
    assert (Hfb' : fetch_word segs (ms_pc_val ms2) = Some wb) by (rewrite (so_pc _ _ _ _ _ _ HS2), mk_pc; exact Hfb).
    destruct (VdStep.m_branch segs OPS E (mk pcB y) ms2 model2 wb ib BC_NE rs1 rs2 off PC HS2 ltac:(rewrite mk_pc; apply ltb62; lia) Hfb' Heb Hdb Hofb) as (ms3 & STEP3 & HS3).
    { assert (NEQ : branch_taken BC_NE (den E (getr (mk pcB y) rs1)) (den E (getr (mk pcB y) rs2)) = true).
      { cbn [branch_taken]. apply negb_true_iff. unfold bv_eqb. apply Z.eqb_neq.
        apply orb_prop in HR as [HR|HR]; apply andb_prop in HR as [R1 R2]; apply r5_eqb_spec in R1, R2; subst rs1 rs2;
          rewrite mk_cur, (mk_other pcB y BEG HCB), Uy, HBEG; subst z; nia. }
      rewrite NEQ, mk_pc. exact PADD. }
    apply (astep _ ms2 ms3 model2 wb ib _ Hfb' Heb Hdb Hofb I STEP3 HS3 HMP2 (so_svc _ _ _ _ _ _ HS2) (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS2))). clear HS3. intros model3 HS3 HMP3.
    rewrite mk_setpc in HS3.
    apply (IH y ms3 model3 HS3 HMP3); [rewrite Uy; subst z; lia| subst z; lia| exact HK].
Qed.

End Loop.

Lemma rf_set_get : forall A (x : rf A) r, rf_set x r (rf_get x r) = x.
Proof. intros A x r; destruct x, r; reflexivity. Qed.

Lemma mk_self : forall st, r5_eqb CUR X0 = false -> s_pc st = PC -> mk st PC (getr st CUR) = st.
Proof.
  intros st HX0 Hpc. unfold mk. rewrite (setr_eq _ CUR _ HX0). unfold setpc, getr. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  rewrite rf_set_get, <- Hpc. destruct st; reflexivity.
Qed.

Lemma find_f1_In : forall fs0 fs cur beg j, find_f1 fs0 fs cur beg = Some j ->
  exists f, In f fs /\ f1_match fs0 cur beg f = Some j.
Proof.
  induction fs as [|f fs IH]; intros cur beg j H; cbn [find_f1] in H; [discriminate|].
  destruct (f1_match fs0 cur beg f) as [j'|] eqn:M.
  - injection H as <-. exists f. split; [left; reflexivity| exact M].
  - destruct (IH cur beg j H) as (f' & I & M'). exists f'. split; [right; exact I| exact M'].
Qed.

Theorem vd_sound : contract_sound segs OPS MP PB vd_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [vd_contract c_apply c_pc] in HA, Hpc. unfold vd_apply in HA.
  destruct (getr st LIM) as [l| | | | | | | | | |] eqn:HLIM; try discriminate HA.
  match type of HA with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate HA] end. injection HA as <-.
  apply andb_prop in COND as [COND Cne]. apply andb_prop in COND as [COND Clim].
  apply andb_prop in COND as [COND Cwit]. apply andb_prop in COND as [COND Clatch]. apply andb_prop in COND as [COND Cdec].
  apply andb_prop in COND as [COND Cg]. apply andb_prop in COND as [COND Cs32]. apply andb_prop in COND as [COND Cs1].
  apply andb_prop in COND as [COND Cex]. apply andb_prop in COND as [COND Cng]. apply andb_prop in COND as [COND Cpc].
  apply andb_prop in COND as [COND Ccl]. apply andb_prop in COND as [Cx0 Ccb].
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.

  apply negb_true_iff in Cx0.
  assert (HCB : CUR <> BEG) by (intros X; rewrite <- X, r5_eqb_refl in Ccb; discriminate Ccb).
  assert (HCL : CUR <> LIM) by (intros X; rewrite <- X, r5_eqb_refl in Ccl; discriminate Ccl).
  apply Uint63.ltb_spec in Cpc, Cex. change (to_Z bit62i) with (2 ^ 62) in Cpc, Cex. apply Nat.leb_le in Cng.
  apply Uint63.leb_spec in Cs1, Cs32. change (to_Z 1%uint63) with 1 in Cs1. change (to_Z 32%uint63) with 32 in Cs32.
  unfold dec_false, dec_true in Clim, Cne.
  destruct (decide_ltu (s_facts st) (VL l) (getr st BEG)) as [[|]|] eqn:D1; try discriminate Clim.
  destruct (decide_eq (s_facts st) (getr st CUR) (getr st BEG)) as [[|]|] eqn:D0; try discriminate Cne.
  apply (decide_ltu_sound E _ FH) in D1. apply (decide_eq_sound E _ FH) in D0.
  unfold bv_ltu in D1. unfold bv_eqb in D0. apply Z.ltb_lt in D1. apply Z.eqb_neq in D0.
  rewrite den_VL in D1.
  set (Bz := bv_unsigned (den E (getr st BEG))) in *. set (Cz := bv_unsigned (den E (getr st CUR))) in *. set (Sz := to_Z S) in *.
  pose proof (bv_unsigned_in_range _ (den E (getr st BEG))) as RB. rewrite bv_modulus_64 in RB. fold Bz in RB.

  assert (F2Z : forall j, dec_false (decide_ltu (s_facts st) (VL VD_MAX) (VP j wzero)) = true -> bv_unsigned (ev E j) <= 288230376151711744).
  { intros j Cf2. unfold dec_false in Cf2.
    destruct (decide_ltu (s_facts st) (VL VD_MAX) (VP j wzero)) as [[|]|] eqn:D3; try discriminate Cf2.
    apply (decide_ltu_sound E _ FH) in D3. unfold bv_ltu in D3. apply Z.ltb_ge in D3.
    rewrite den_VL in D3. rewrite (den_VP0 E j wzero (weqb_refl _)) in D3.
    unfold VD_MAX in D3. rewrite wlit_ok in D3. change (to_Z 288230376151711744%uint63) with 288230376151711744 in D3. exact D3. }

  assert (COUNT : forall j, Bz <= Cz -> dec_false (decide_ltu (s_facts st) (VL VD_MAX) (VP j wzero)) = true ->
            Cz = (Bz + (bv_unsigned (ev E j) * Sz) mod two64) mod two64 -> exists J, Cz = Bz + J * Sz /\ 1 <= J).
  { intros j D2 Cf2 Hf. pose proof (F2Z j Cf2) as D3.
    set (J := bv_unsigned (ev E j)) in *.
    pose proof (bv_unsigned_in_range _ (ev E j)) as RJ. rewrite bv_modulus_64 in RJ. fold J in RJ. unfold two64 in *.
    assert (JS : 0 <= J * Sz < 18446744073709551616) by nia.
    rewrite (Z.mod_small (J * Sz)) in Hf by exact JS.
    assert (CE : Cz = Bz + J * Sz).
    { destruct (Z_lt_le_dec (Bz + J * Sz) 18446744073709551616) as [LT|GE]; [rewrite Z.mod_small in Hf by lia; exact Hf|].
      exfalso. replace (Bz + J * Sz) with (Bz + J * Sz - 18446744073709551616 + 1 * 18446744073709551616) in Hf by lia.
      rewrite Z.mod_add, Z.mod_small in Hf by lia. lia. }
    exists J. split; [exact CE| nia]. }
  assert (WIT : exists J, Cz = Bz + J * Sz /\ 1 <= J).
  { destruct (cur_shape (s_facts st) (getr st CUR) (getr st BEG)) as [j|] eqn:CS.
    -
      pose proof (F2Z j Cwit) as D3. unfold cur_shape in CS.
      destruct (getr st CUR) as [?|? ?|op b m|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?] eqn:GC; try discriminate CS. destruct op; try discriminate CS.
      destruct b as [?|kb ob|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate CS.
      destruct m as [?|? ?|? ? ?|? ? ?|mo mj ms_|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate CS. destruct mo; try discriminate CS.
      destruct mj as [?|j' o|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate CS.
      destruct ms_ as [s|? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate CS.
      destruct (getr st BEG) as [?|kb' ob'|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?] eqn:GB; try discriminate CS.
      match type of CS with (if ?c then _ else _) = _ => destruct c eqn:FC; [|discriminate CS] end. injection CS as ->.
      apply andb_prop in FC as [FC QHI]. apply andb_prop in FC as [FC QMOD]. apply andb_prop in FC as [FC QLE].
      apply andb_prop in FC as [FC QT]. apply andb_prop in FC as [FC QB0]. apply andb_prop in FC as [FC QK]. apply andb_prop in FC as [QO QS].
      apply (proj1 (weqb_ok _ _)) in QS. subst s. apply Uint63.eqb_correct in QK. subst kb'.
      apply negb_true_iff in QT. apply Uint63.leb_spec in QLE. change (to_Z 512%uint63) with 512 in QLE.
      apply Uint63.eqb_correct in QMOD. apply (f_equal to_Z) in QMOD. rewrite Uint63.mod_spec in QMOD. change (to_Z 0%uint63) with 0 in QMOD. fold Sz in QMOD.

      pose proof (sv_bounds_sound E (s_facts st) FH (VP kb ob')) as BB. unfold inb in BB. destruct BB as [_ BB].
      rewrite wleu_w2Z in QHI. apply Z.leb_le in QHI. unfold BEG_MAX in QHI. rewrite wlit_ok in QHI.
      change (to_Z 4611686018427387904%uint63) with 4611686018427387904 in QHI. fold Bz in BB.
      assert (BZ62 : Bz <= 4611686018427387904) by lia.

      assert (BV : Bz = bv_unsigned (ev E kb)) by (subst Bz; exact (den_VP0 E kb ob' QB0)).
      assert (OBZ : w2Z ob = to_Z (wl ob)) by (unfold w2Z; rewrite QT; reflexivity).
      pose proof (Uint63.to_Z_bounded (wl ob)) as RO.
      set (J := bv_unsigned (ev E j)) in *.
      pose proof (bv_unsigned_in_range _ (ev E j)) as RJ. rewrite bv_modulus_64 in RJ. fold J in RJ.
      assert (CV : Cz = Bz + to_Z (wl ob) + J * Sz).
      { subst Cz.
        change (den E (VAlu ALU_ADD (VP kb ob) (VMd M_MUL (VP j o) (VL (wlit S))))) with (bv_add (den E (VP kb ob)) (bv_mul (den E (VP j o)) (den E (VL (wlit S))))).
        rewrite bv_add_unsigned, bv_mul_unsigned, (den_VP0 E j o QO), den_VL, wlit_ok. fold J Sz.
        cbn [den]. rewrite bv_add_unsigned, wbv_unsigned, OBZ, <- BV. unfold bv_wrap. rewrite bv_modulus_64. unfold two64 in *.
        rewrite (Z.mod_small (Bz + to_Z (wl ob))) by lia. rewrite (Z.mod_small (J * Sz)) by nia. rewrite Z.mod_small by nia. lia. }
      pose proof (Z_div_mod_eq_full (to_Z (wl ob)) Sz) as DQ. rewrite QMOD in DQ.
      assert (QN : 0 <= to_Z (wl ob) / Sz) by (apply Z.div_pos; lia).
      exists (J + to_Z (wl ob) / Sz). split; [rewrite CV; nia|].
      assert (NEQ : Cz <> Bz) by exact D0. rewrite CV in NEQ. nia.
    - match type of Cwit with (if ?c then _ else _) = true => destruct c eqn:Cnw; [|discriminate Cwit] end.
      unfold dec_false in Cnw.
      destruct (decide_ltu (s_facts st) (getr st CUR) (getr st BEG)) as [[|]|] eqn:D2; try discriminate Cnw.
      apply (decide_ltu_sound E _ FH) in D2. unfold bv_ltu in D2. apply Z.ltb_ge in D2. fold Bz Cz in D2.
      destruct (find_f1 (s_facts st) (s_facts st) (getr st CUR) (getr st BEG)) as [j|] eqn:FF.
      +
        apply (COUNT j D2 Cwit).
        destruct (find_f1_In _ _ _ _ _ FF) as (f & INf & FM).
        pose proof (proj1 (Forall_forall _ _) FH f INf) as Hf.
        unfold f1_match in FM. destruct f as [? ? ?|? ?|? ?|? ?|e rhs|? ?|? ?|? ?]; try discriminate FM.
        destruct rhs as [?|? ?|op b m|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate FM. destruct op; try discriminate FM.
        destruct m as [?|? ?|? ? ?|? ? ?|mo mj ms_|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate FM. destruct mo; try discriminate FM.
        destruct mj as [?|j' o|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate FM.
        destruct ms_ as [s|? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try discriminate FM.
        match type of FM with (if ?c then _ else _) = _ => destruct c eqn:FC; [|discriminate FM] end. injection FM as ->.
        repeat match type of FC with (_ && _) = true => let X := fresh "Q" in apply andb_prop in FC as [FC X] end.
        unfold dec_true in Q0, Q.
        destruct (decide_eq (s_facts st) e (getr st CUR)) as [[|]|] eqn:DE; try discriminate Q0.
        destruct (decide_eq (s_facts st) b (getr st BEG)) as [[|]|] eqn:DB; try discriminate Q.
        apply (decide_eq_sound E _ FH) in DE, DB. unfold bv_eqb in DE, DB. apply Z.eqb_eq in DE, DB.
        apply (proj1 (weqb_ok _ _)) in Q1. subst s.
        cbn [fact_holds] in Hf. apply (f_equal bv_unsigned) in Hf.
        change (den E (VAlu ALU_ADD b (VMd M_MUL (VP j o) (VL (wlit S))))) with (bv_add (den E b) (bv_mul (den E (VP j o)) (den E (VL (wlit S))))) in Hf.
        rewrite bv_add_unsigned, bv_mul_unsigned, (den_VP0 E j o FC), den_VL, wlit_ok, DE, DB in Hf.
        unfold bv_wrap in Hf. rewrite bv_modulus_64 in Hf. fold Bz Cz Sz in Hf. exact Hf.
      +
        unfold align_ok in Cwit. apply andb_prop in Cwit as [Cwit ALB]. apply andb_prop in Cwit as [ES ALC].
        apply Uint63.eqb_correct in ES.
        assert (S8 : Sz = 8) by (subst Sz; rewrite ES; reflexivity).
        pose proof (aligned8_sound E (s_facts st) (getr st CUR) FH ALC) as MC.
        pose proof (aligned8_sound E (s_facts st) (getr st BEG) FH ALB) as MB.
        fold Cz in MC. fold Bz in MB.
        exists ((Cz - Bz) / 8). rewrite S8.
        assert (DM : (Cz - Bz) mod 8 = 0) by (rewrite Zminus_mod, MC, MB; reflexivity).
        pose proof (Z_div_mod_eq_full (Cz - Bz) 8) as DE. rewrite DM in DE. split; lia. }
  destruct WIT as (J & CE & J1).

  rewrite <- (mk_self st Cx0 Hpc) in HS.
  apply (loop_cps E K st l Bz Sz Cx0 HCB HCL HLIM eq_refl D1 eq_refl ltac:(lia) Cpc Cng Cex Cg Cdec Clatch (Z.to_nat (J - 1)) (getr st CUR) ms model HS HMP).
  - fold Cz. rewrite CE, Z2Nat.id by lia. lia.
  - rewrite Z2Nat.id by lia. pose proof (bv_unsigned_in_range _ (den E (getr st CUR))) as RC. rewrite bv_modulus_64 in RC. fold Cz in RC. unfold two64 in *. nia.
  - intros ms' mo' HS' HMP'. exact (Hk _ (or_introl eq_refl) E ms' mo' (env_ext_refl (s_next st) E) HMP' HS').
Qed.

Lemma vd_contract_eq : vd_contract = VDestroy.VD.vd_contract segs PC CUR BEG LIM S NG.
Proof. reflexivity. Qed.
Theorem vd_sound_acc : contract_sound segs OPS MP PB (VDestroy.VD.vd_contract segs PC CUR BEG LIM S NG).
Proof. rewrite <- vd_contract_eq. exact vd_sound. Qed.

End Sound.
End WithPc.
End WithSegs.
End VDA.
End TwinB.
