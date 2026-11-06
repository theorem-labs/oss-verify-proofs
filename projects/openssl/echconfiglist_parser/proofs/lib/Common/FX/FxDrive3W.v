(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector bitvector.tactics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg LazyCfg LazyAccCfg AllocLazyCfg EagerCfg CountCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn
  FxLazy FxSys FxDrive FxCellFrame FxDrive3 FxDrive3N FxDrive3S FxDrive3H FxDrive3T FxDrive3O.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WBytes.
Variable IM : fimage.

(* [comment removed for export] *)
Fixpoint wl_bytes (M : itrie region) (a : fval) (k : int) (cnt : nat) (acc : w64) : option w64 :=
  match cnt with
  | O => Some acc
  | S cnt' =>
      match fv_alu M ALU_ADD a (FV 0 (W64 0 k)) with
      | Some ak =>
          match fm_load_abs IM M ak SZ1 false with
          | Some b => if (vtag b =? 0)%uint63
                      then wl_bytes M a (k + 1)%uint63 cnt' (w_insert k 1 acc (vw b))
                      else None
          | None => None
          end
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition wl_load (M : itrie region) (a : fval) (sz : msize) (sgn : bool) : option fval :=
  match wl_bytes M a 0 (msz_nat sz) w_zero with
  | Some acc => Some (FV 0 (ext_load sz sgn (w_extract 0 (msz_int sz) acc)))
  | None => None
  end.
End WBytes.

Section WBytesSound.
Variable segs : list Segment.
Variable IM : fimage.
Variable rho : int -> word.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.

Lemma ov_read1 m a bs : ov_read_bytes segs m a 1 = Some bs -> exists b, bs = [b] /\ rview segs m a = Some b.
Proof.
  cbn [ov_read_bytes]. unfold rview.
  destruct (match m a with Some b => Some b | None => _ end) as [b|]; [|discriminate].
  intros H. injection H as <-. exists b. split; reflexivity.
Qed.

Lemma load_result_1 (b : byte) : bv_unsigned (load_result SZ1 false [b]) = bv_unsigned b.
Proof.
  unfold load_result, le_bytes_to_word. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  unfold zext. rewrite bv_zero_extend_unsigned by (cbv; discriminate).
  rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ Z.of_N 8) with 256.
  rewrite (Z.mod_small (bv_unsigned b) (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma aoff_alu_add (a : word) (k : int) :
  alu64 ALU_ADD a (dv rho (FV 0 (W64 0 k))) = aoff a (Z.to_nat (to_Z k)).
Proof.
  rewrite (dv_conc rho Hrho0). unfold alu64, alu, aoff. f_equal. unfold wbv, wZ. cbn [wtop wlo].
  change (to_Z 0 mod 2) with 0. rewrite Z.mul_0_l, Z.add_0_l. f_equal.
  pose proof (i63_range k). lia.
Qed.

Theorem wl_bytes_sound M m a : regs_ok rho M -> mem_ok segs IM rho M m ->
  forall cnt k acc acc',
    to_Z k + Z.of_nat cnt <= 8 ->
    wl_bytes IM M a k cnt acc = Some acc' ->
    (forall j, (j < Z.to_nat (to_Z k))%nat -> nth_error (w_bytes acc') j = nth_error (w_bytes acc) j)
    /\ (forall j, (Z.to_nat (to_Z k) <= j < Z.to_nat (to_Z k) + cnt)%nat ->
           rview segs m (aoff (dv rho a) j) = nth_error (w_bytes acc') j
           /\ acc_claimed IM rho M (aoff (dv rho a) j) 1).
Proof.
  intros HM Hmok. induction cnt as [|cnt IH]; intros k acc acc' Hk H.
  - cbn [wl_bytes] in H. injection H as <-. split; [reflexivity | intros j Hj; lia].
  - cbn [wl_bytes] in H.
    destruct (fv_alu M ALU_ADD a (FV 0 (W64 0 k))) as [ak|] eqn:Ea; [|discriminate].
    destruct (fm_load_abs IM M ak SZ1 false) as [b|] eqn:El0; [|discriminate].
    destruct (vtag b =? 0)%uint63 eqn:Et; [|discriminate].
    destruct (fm_load_abs_inv rho Hrho0 IM _ _ _ _ _ HM El0) as (a' & Ea' & El).
    apply (fv_alu_sound rho Hrho0 _ _ _ _ _ HM) in Ea. rewrite aoff_alu_add in Ea. rewrite Ea in Ea'.
    destruct (fm_load_sound segs IM rho Hrho0 _ _ _ _ _ _ Hmok El) as (bs & Hbs & Hres).
    pose proof (fm_load_claimed segs IM rho _ _ _ _ _ _ Hmok El) as Hcl.
    rewrite Ea' in Hbs, Hcl. cbn [msz_nat] in Hbs, Hcl.
    destruct (ov_read1 _ _ _ Hbs) as (b0 & -> & Hrv).
    assert (Eb0 : Z_to_bv 8 (wZ (vw b)) = b0).
    { rewrite <- (Z_to_bv_bv_unsigned _ b0). f_equal.
      rewrite <- (load_result_1 b0), Hres, (dv_tag0' rho Hrho0 b Et). symmetry. apply wbv_unsigned. }
    pose proof (i63_range k) as Hk0.
    assert (Ek1 : to_Z (k + 1)%uint63 = to_Z k + 1).
    { rewrite Uint63.add_spec. change (to_Z 1) with 1. apply Z.mod_small. change wB with (2 ^ 63). lia. }
    destruct (IH (k + 1)%uint63 _ _ ltac:(lia) H) as [IH1 IH2]. rewrite Ek1 in IH1, IH2.
    assert (Hins : forall j, (j < 8)%nat ->
              nth_error (w_bytes (w_insert k 1 acc (vw b))) j =
              if (j =? Z.to_nat (to_Z k))%nat then Some b0 else nth_error (w_bytes acc) j).
    { intros j Hj. rewrite (insert_bytes_nth k 1 acc (vw b) j ltac:(change (to_Z 1) with 1; lia)
                              ltac:(change (to_Z 1) with 1; lia) Hj).
      change (Z.to_nat (to_Z 1)) with 1%nat.
      destruct (j =? Z.to_nat (to_Z k))%nat eqn:Ej.
      - apply Nat.eqb_eq in Ej. subst j.
        replace ((Z.to_nat (to_Z k) <=? Z.to_nat (to_Z k))%nat && (Z.to_nat (to_Z k) <? Z.to_nat (to_Z k) + 1)%nat)
          with true by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
        rewrite Nat.sub_diag. cbn [Z_to_le_bytes nth_error]. rewrite Eb0. reflexivity.
      - apply Nat.eqb_neq in Ej.
        replace ((Z.to_nat (to_Z k) <=? j)%nat && (j <? Z.to_nat (to_Z k) + 1)%nat) with false; [reflexivity|].
        symmetry. apply andb_false_iff.
        destruct (Nat.leb_spec (Z.to_nat (to_Z k)) j); [right; apply Nat.ltb_ge; lia | left; reflexivity]. }
    split.
    + intros j Hj. rewrite (IH1 j ltac:(lia)), (Hins j ltac:(lia)).
      replace (j =? Z.to_nat (to_Z k))%nat with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
    + intros j Hj. destruct (Nat.eq_dec j (Z.to_nat (to_Z k))) as [->|Hne].
      * split; [|exact Hcl]. rewrite (IH1 (Z.to_nat (to_Z k)) ltac:(lia)), (Hins (Z.to_nat (to_Z k)) ltac:(lia)), Nat.eqb_refl.
        exact Hrv.
      * apply IH2. lia.
Qed.

(* [comment removed for export] *)
Theorem wl_load_sound M m a sz sgn v : regs_ok rho M -> mem_ok segs IM rho M m ->
  wl_load IM M a sz sgn = Some v ->
  (exists bs, ov_read_bytes segs m (dv rho a) (msz_nat sz) = Some bs /\ load_result sz sgn bs = dv rho v)
  /\ (forall j, (j < msz_nat sz)%nat -> acc_claimed IM rho M (aoff (dv rho a) j) 1).
Proof.
  intros HM Hmok H. unfold wl_load in H.
  destruct (wl_bytes IM M a 0 (msz_nat sz) w_zero) as [acc|] eqn:Eb; [|discriminate]. injection H as <-.
  pose proof (msz_nat_pos sz) as Hsz.
  assert (H08 : to_Z 0 + Z.of_nat (msz_nat sz) <= 8) by (change (to_Z 0) with 0; lia).
  destruct (wl_bytes_sound M m a HM Hmok (msz_nat sz) 0%uint63 w_zero acc H08 Eb) as [_ H2].
  change (Z.to_nat (to_Z 0)) with 0%nat in H2.
  split; [|intros j Hj; exact (proj2 (H2 j ltac:(lia)))].
  exists (firstn (msz_nat sz) (w_bytes acc)). split.
  - apply ov_read_bytes_intro.
    + rewrite firstn_length_le; [reflexivity|]. rewrite length_w_bytes. lia.
    + intros j Hj. rewrite (nth_error_firstn_lt _ _ _ Hj). exact (proj1 (H2 j ltac:(lia))).
  - rewrite (dv_conc rho Hrho0).
    exact (load_result_any sz sgn acc 0%uint63 H08).
Qed.
End WBytesSound.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WStep.
Variable segs : list Segment.
Variable IM : fimage.
Variable rho : int -> word.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.

Local Abbreviation Rr := (R segs IM rho).

Ltac shape_tac :=
  cbn [ms_fregs ms_fcsr ms_of];
  repeat (progress (cbn [c_fregs c_fcsr with_resv with_pc core_of];
                    rewrite ?sem_rset_fregs, ?sem_rset_fcsr, ?inval_resv_fregs, ?inval_resv_fcsr));
  reflexivity.

Lemma fx_step_wload : forall F ms sz sgn rd rs1 imm a v,
  Rr F ms -> iget (f_pc F) code = Some (FLoad sz sgn rd rs1 imm) ->
  fv_alu (f_mem F) ALU_ADD (FxState.rget F rs1) (FV 0 imm) = Some a ->
  wl_load IM (f_mem F) a sz sgn = Some v ->
  exists ms', step segs ms = MachineOk ms'
    /\ ms_mem ms' = ms_mem ms /\ ms_rom ms' = ms_rom ms /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms
    /\ Rr (FxState.rset F rd v (f_pc F + 4)%uint63) ms'.
Proof.
  intros F ms sz sgn rd rs1 imm a v HR Hi Ea Hl.
  destruct (code_entry segs IM rho code Hcode F ms _ HR Hi) as (Hpc & w & Hf & [[He Hfi] | (He & i & Hd & Hc)]);
    [discriminate Hfi|].
  rewrite (step_decode segs ms w i Hf He Hd).
  pose proof (R_regs_ok segs IM rho F ms HR) as HM.
  pose proof (R_pc _ _ _ _ _ HR) as Epc.
  pose proof (pc_plus4 _ Hpc) as Enpc.
  pose proof (R_regs _ _ _ _ _ HR) as Hregs.
  destruct i; cbn [compile] in Hc; try discriminate Hc;
    try (destruct (pc_of_word _); [|discriminate Hc]; try (destruct (pc_of_word _)); discriminate Hc).
  apply some_inj in Hc. injection Hc as -> -> -> -> ->.
  apply (fv_alu_sound rho Hrho0 _ _ _ _ _ HM) in Ea. rewrite (dv_conc rho Hrho0), wbv_w_of_bv, <- Hregs in Ea.
  unfold alu64, alu in Ea.
  destruct (wl_load_sound segs IM rho Hrho0 _ _ _ _ _ _ HM (R_mem _ _ _ _ _ HR) Hl) as [(bs & Hbs & Hres) _].
  unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. rewrite <- Ea.
  rewrite (interp_load_val _ _ _ _ _ _ bs Hbs). eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [shape_tac|]. split; [shape_tac|].
  apply R_after_reg; [exact Hrho0 | exact HR | symmetry; exact Hres].
Qed.

(* [comment removed for export] *)
Lemma wload_touch_ok lazy A : forall F ms sz sgn rd rs1 imm a v,
  Rr F ms -> iget (f_pc F) code = Some (FLoad sz sgn rd rs1 imm) ->
  fv_alu (f_mem F) ALU_ADD (FxState.rget F rs1) (FV 0 imm) = Some a ->
  wl_load IM (f_mem F) a sz sgn = Some v ->
  LZ IM rho lazy A (f_mem F) -> touch_ok segs lazy A ms.
Proof.
  intros F ms sz sgn rd rs1 imm a v HR Hi Ea Hl HL report Hacc. apply touch_allowed_bytes.
  destruct (code_entry segs IM rho code Hcode F ms _ HR Hi) as (Hpc & w & Hf & [[He Hfi] | (He & i & Hd & Hc)]);
    [discriminate Hfi|].
  pose proof (step_accesses_exact segs ms w i 4 report Hf He Hd Hacc) as Hex.
  change (lz_core ms) with (core_of ms) in Hex.
  pose proof (R_regs_ok segs IM rho F ms HR) as HM.
  pose proof (R_regs _ _ _ _ _ HR) as Hregs.
  destruct i; cbn [compile] in Hc; try discriminate Hc;
    try (destruct (pc_of_word _); [|discriminate Hc]; try (destruct (pc_of_word _)); discriminate Hc).
  apply some_inj in Hc. injection Hc as -> -> -> -> ->.
  apply (fv_alu_sound rho Hrho0 _ _ _ _ _ HM) in Ea. rewrite (dv_conc rho Hrho0), wbv_w_of_bv, <- Hregs in Ea.
  unfold alu64, alu in Ea.
  destruct (wl_load_sound segs IM rho Hrho0 _ _ _ _ _ _ HM (R_mem _ _ _ _ _ HR) Hl) as [_ Hcl].
  rewrite Ea in Hcl.
  eapply Forall_impl; [|exact Hex]. intros r [E1 E2] i0 Hi0. rewrite E1. rewrite E2 in Hi0.
  cbn [exec_addr exec_nbytes] in Hi0 |- *.
  match goal with |- context [page_base_of (bv_unsigned ?x + i0)] => set (A0 := x) in * end.
  match type of Hl with wl_load _ _ _ ?s _ = _ =>
    assert (Hn : (Z.to_nat i0 < msz_nat s)%nat) by (clear - Hi0; destruct s; cbn [msz_nat]; lia);
    pose proof (msz_nat_pos s) as Hsz
  end.
  (* [comment removed for export] *)
  assert (HA0 : bv_unsigned A0 < 2 ^ 63).
  { destruct (Hcl 0%nat ltac:(lia)) as (t & rg & pn & p & j & Hg & Hpn & Hp & Hj0 & Hj & Hjl & Eadr).
    rewrite aoff_0 in Eadr. rewrite Eadr.
    destruct (proj1 (R_mem _ _ _ _ _ HR) t rg Hg) as [Hreg _].
    pose proof (region_ok_nowrap_lz rho t rg Hreg) as Hnw. pose proof (i63_range pn) as Hpn0.
    rewrite adr_unsigned; lia. }
  destruct (Hcl (Z.to_nat i0) Hn) as (t & rg & pn & p & j & Hg & Hpn & Hp & Hj0 & Hj & Hjl & Eadr).
  destruct (proj1 (R_mem _ _ _ _ _ HR) t rg Hg) as [Hreg _].
  pose proof (region_ok_nowrap_lz rho t rg Hreg) as Hnw. pose proof (i63_range pn) as Hpn0.
  assert (Eu : bv_unsigned A0 + i0 = bv_unsigned (rho t) + to_Z pn * 4096 + j).
  { transitivity (bv_unsigned (aoff A0 (Z.to_nat i0))).
    - unfold aoff. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Z2Nat.id by lia. rewrite (Z.mod_small i0) by lia. symmetry. apply Z.mod_small.
      pose proof (bv_unsigned_in_range _ A0). lia.
    - rewrite Eadr, adr_unsigned; lia. }
  rewrite Eu. apply (HL t rg pn p j Hg Hpn Hp); lia.
Qed.
End WStep.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Drive3W.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Variable R0 : list (word * word).
Variable Lim : Z.
Variable keep : list int.
Variable mem0 : word -> option byte.
Variable XI : (int -> word) -> Model -> Prop.
Variable xtags : list int.
Hypothesis XI_rho : forall rho rho' m, (forall t, In t xtags -> rho' t = rho t) -> XI rho m -> XI rho' m.
Variable fr0 : bvmap 5 word.
Variable fc0 : bv 32.
Variable rom0 : word -> option byte.
Variable hi : word -> Prop.
Variable wb0 : word.
Variable na0 lz0 : list (word * word).
Variable brk0 : word.
Variable A0 : list (Z * Z).

Local Abbreviation D3 := (DInv3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation Rn := (FxRn.Rn segs IM).
Local Abbreviation PX := (pext IM).
Local Abbreviation POK := (pc_ok3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation reach := (FxDrive3T.reach cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation rpok := (FxDrive3T.reach_POK cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).

(* [comment removed for export] *)
Lemma step_node_t n rho F F' L3 ms ms' m :
  D3 n rho F L3 ms m ->
  f_mem F' = f_mem F -> Rn n rho F' ms' ->
  step segs ms = MachineOk ms' ->
  ms_mem ms' = ms_mem ms -> ms_rom ms' = ms_rom ms -> ms_fregs ms' = ms_fregs ms -> ms_fcsr ms' = ms_fcsr ms ->
  touch_ok segs (m_vm_lazy m) (allowed A0 rho L3) ms ->
  exists m1, D3 n rho F' L3 ms' m1 /\ PX n rho F L3 ms m n rho F' L3 ms' m1
    /\ asteps segs 1 (ms, m) = MachineOk (ms', m1).
Proof.
  intros HD EM HRn' Hstep Emem Erom Efr Efc Htouch.
  pose proof HD as (HDI & HL & HS & HX).
  pose proof HDI as (HRn & H0 & Hh & _).
  pose proof (Rn_R segs IM n rho F ms HRn H0) as HR.
  pose proof (R_svc _ _ _ _ _ HR) as Hsvc.
  pose proof (lp_pi _ _ _ _ _ _ _ _ _ _ _ HL) as Hpi.
  assert (Hr1 : rsteps segs 1 ms = MachineOk ms').
  { cbn [rsteps]. rewrite Hsvc, Hstep. reflexivity. }
  assert (Ht : forall j msj, (j < 1)%nat -> rsteps segs j ms = MachineOk msj ->
                 touch_ok segs (m_vm_lazy m) (allowed A0 rho L3) msj).
  { intros j msj Hj Hrj. assert (j = 0)%nat by lia. subst j. cbn [rsteps] in Hrj. injection Hrj as <-. exact Htouch. }
  destruct (asteps_pages segs (allowed A0 rho L3) 1 ms ms' m Hr1 Hpi Ht) as (m1 & Ha & Hfr & Hpi1).
  pose proof (asteps_mat_lazy segs _ ms m ms' m1 Ha (lp_mat _ _ _ _ _ _ _ _ _ _ _ HL)) as Hml1.
  exists m1. split; [|split; [|exact Ha]].
  - apply (DInv3_regstep cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
             n rho F F' L3 ms ms' m m1 HD); assumption.
  - destruct (lazy_frame_facts m m1 Hfr) as (_ & Evm & _). split.
    + split; [lia|]. split; [intros t _; reflexivity|]. split; [exact (lazy_frame_same_but_vm m m1 Hfr)|].
      rewrite Evm. repeat split; reflexivity.
    + exists []. split; [symmetry; apply app_nil_r|]. split; [constructor|]. split; [|split].
      * intros y _ _. rewrite Emem. reflexivity.
      * intros y (t & rg & pn & p & j & Hg & Hpn & Hp & Hw & Hj & Hjl & ->). left.
        rewrite EM in Hg. exists t, rg, pn, p, j. repeat (split; [assumption|]). reflexivity.
      * intros y (t & rg & pn & p & ci & Hg & Hp & Hci & j & Hj & ->). left.
        exists t, rg, pn, p, ci. rewrite EM. split; [exact Hg|]. split; [exact Hp|].
        split; [exact Hci|]. exists j. split; [exact Hj|]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xpc_wload (F : fstate) (L3 : fledger3) (n : int) : option dres3 :=
  match iget (f_pc F) code with
  | Some (FLoad sz sgn rd rs1 imm) =>
      match fv_alu (f_mem F) ALU_ADD (FxState.rget F rs1) (FV 0 imm) with
      | Some a =>
          match wl_load IM (f_mem F) a sz sgn with
          | Some v => Some (D3One (FxState.rset F rd v (f_pc F + 4)%uint63) L3 n)
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Theorem xpc_wload_sound n rho F L3 ms m res :
  xpc_wload F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  intros Hx HD. unfold xpc_wload in Hx.
  destruct (iget (f_pc F) code) as [fi|] eqn:Hi; [|discriminate].
  destruct fi as [| | | |sz sgn rd rs1 imm| | | | | | | | | | | |]; try discriminate Hx.
  destruct (fv_alu (f_mem F) ALU_ADD (FxState.rget F rs1) (FV 0 imm)) as [a|] eqn:Ea; [|discriminate].
  destruct (wl_load IM (f_mem F) a sz sgn) as [v|] eqn:Hl; [|discriminate]. injection Hx as <-.
  pose proof HD as (HDI & HL & HS & HX).
  pose proof HDI as (HRn & H0 & Hh & _).
  change (m_halted (FxDrive3.erase wb0 m)) with (m_halted m) in Hh.
  pose proof (Rn_R segs IM n rho F ms HRn H0) as HR.
  destruct (fx_step_wload segs IM rho H0 code Hcode F ms sz sgn rd rs1 imm a v HR Hi Ea Hl)
    as (ms' & Hstep & Emem & Erom & Efr & Efc & HR').
  set (F' := FxState.rset F rd v (f_pc F + 4)%uint63).
  assert (HRn' : Rn n rho F' ms').
  { intros rho2 Hag2. pose proof (HRn rho2 Hag2) as HR2.
    pose proof (proj1 Hag2) as H02.
    destruct (fx_step_wload segs IM rho2 H02 code Hcode F ms sz sgn rd rs1 imm a v HR2 Hi Ea Hl)
      as (ms2 & Hstep2 & _ & _ & _ & _ & HR2').
    rewrite Hstep in Hstep2. injection Hstep2 as <-. exact HR2'. }
  pose proof (wload_touch_ok segs IM rho H0 code Hcode (m_vm_lazy m) (allowed A0 rho L3)
                F ms sz sgn rd rs1 imm a v HR Hi Ea Hl
                (lazy_part_LZ IM R0 Lim na0 lz0 A0 n rho F L3 m HL)) as Htouch.
  assert (EM : f_mem F' = f_mem F) by reflexivity.
  destruct (step_node_t n rho F F' L3 ms ms' m HD EM HRn' Hstep Emem Erom Efr Efc Htouch)
    as (m1 & HD' & HPX & Ha).
  apply rpok. split.
  - intros T HT. apply (rzc_asteps cfg segs 1 ms m ms' m1 T Hh Ha).
    exact (HT n rho F' L3 ms' m1 eq_refl HD' HPX).
  - exists n, rho, F', L3, ms', m1. split; [reflexivity|]. split; [exact HD'|]. split; [exact HPX|].
    exact (asteps_star_cfg cfg segs 1 ms m ms' m1 Hh Ha).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xpc_builtin6 : fstate -> fledger3 -> int -> option dres3 :=
  xpc_or (xpc_order code) (xpc_or (xpc_ltu code) (xpc_or (xpc_sltu code) (xpc_or (xpc_pgnz code)
         (xpc_or (xpc_align2 code) (xpc_or (xpc_table IM code) (xpc_or xpc_wload (xpc_opaque code))))))).

Theorem xpc_builtin6_sound n rho F L3 ms m res :
  xpc_builtin6 F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  pose proof (xpc_or_sound cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0) as Hor.
  apply Hor; [exact (xpc_order_sound cfg segs IM code Hcode R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0)|].
  apply Hor; [exact (xpc_ltu_sound cfg segs IM code Hcode R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0)|].
  apply Hor; [exact (xpc_sltu_sound cfg segs IM code Hcode R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0)|].
  apply Hor; [exact (xpc_pgnz_sound cfg segs IM code Hcode R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0)|].
  apply Hor; [exact (xpc_align2_sound cfg segs IM code Hcode R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0)|].
  apply Hor; [exact (xpc_table_sound cfg segs IM code Hcode R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0)|].
  apply Hor; [exact xpc_wload_sound|].
  exact (xpc_opaque_sound cfg segs IM code Hcode R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma DInv3_ord_facts n rho F L3 ms m : D3 n rho F L3 ms m -> Forall (ord_ok n rho) (fl_ord L3).
Proof. intros (_ & HL & _ & _). exact (lp_ord _ _ _ _ _ _ _ _ _ _ _ HL). Qed.

Lemma DInv3_res_facts n rho F L3 ms m : D3 n rho F L3 ms m -> Forall (res_ok n rho) (fl_res L3).
Proof. intros (_ & HL & _ & _). exact (lp_res _ _ _ _ _ _ _ _ _ _ _ HL). Qed.

End Drive3W.
