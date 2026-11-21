(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (MInvIR gains the vDSO conjunct, written as plain text, with MInvIR_MInvI and MInvIR_vdso; MInvIm added, the same over a memory; MInvR_IR re-proved; the coercions, the vDSO hint and the minvir_split and minvir_dest tactics added; the malloc contract's auxv view per CONFIG_RSEQ, computed from the launch's auxv object InitState.O_aux with its computing equations and key lemmas, auxv_init restated in plain text as the exists over the flag of auxv_init_r, auxv_init_mono and auxv_init_brk0 re-proved, and the shared auxv lemmas auxv_ok_of_init_gen, auxv_init_ext_gen, auxv_init_frame_gen and auxv_init_rdext_gen added). *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "prod"; "list"; "nat"; "bool"; "option"; "orb"; "None"; "pair"; "Some"; "false"; "app"; "length"; "andb"; "true"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "eqb"; "lt"; "of_nat"; "mul"; "leb"; "modulo"; "pow"; "opp"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "rw"; "valuation"; "rm"; "sobj"; "sv"; "FcsrFrm0"; "mkSS"; "sstate"; "SLit"; "SPUle"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "region"; "astate"; "IB"; "PGSZ"; "alloc_slot"; "ameta"; "kreq"; "st_regions"; "RkMap"; "am_last"; "am_sc"; "class_size"; "mslot"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "st_init_done"; "st_metas"; "stride_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "MA"; "ma_L"; "layout_extends"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "AS_D"; "alloc_slot_sumI"; "ie_as_ret"; "IEC"; "IEC_P"; "IEC_U"; "as_stack"; "ie_as_entry"; "tier"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "pre_fregs"; "cut_regs"; "pre_regs"; "segsP"; "segsU"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.ContractsI"; "am_reads"; "MInvIR"; "auxv_init"; "J_as_pre"; "Posts_as"; "Pre_as"; "canary_kept"; "JL_as_fail"; "JL_as_ok"; "L_as_fail"; "L_as_ok"; "am_auxv_keys"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "rd_of"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "stack_win"; "NPOSTM"; "V_RES"; "mem_kept"; "MInvR"; "V_DEPTH"; "ok_sideK"; "top_high"; "tp_ok"; "vm_insensitive"; "wok_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "layout"; "ly_brk0"; "yields"; "U0"; "active_hd"; "le_byte"; "ly_reg"; "ly_sec"; "region_of"; "usedX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith"; "need"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup"; "heads_below"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "C_U"; "mc_auxv"; "mc_chk_guard"; "mc_chk_guard_got"; "wz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymFrame SymSummary SymCall SymComplete ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter MallocWfArith NestTier MallocIface MallocIfaceI MallocWfFrame MallocWfGroup Contract ZEval Zones2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record ientry_consts := IEC {
  ie_as_entry : Z; ie_as_ret : Z;
  ie_am_entry : Z; ie_am_ret : Z
}.
Definition IEC_P : ientry_consts := IEC 0x20b2c 0x213c8 0x204e4 0x20788.
Definition IEC_U : ientry_consts := ltac2:(tb__ "0|1|
S4cS16Z20b2cZ740M0A2S16Z213c8G0A2S16Z204e4G0A2S16Z20788G0A2A4").

Definition as_stack (t : Z) : Z := ltac2:(tb__ "0|1|
S16S1bZ90M0S16Vt;Z1A2A2G0A2").
Definition AS_D : Z := 288.

Definition tier (sc : Z) : nat := ltac2:(tb__ "0|2|
SbSaL_;M0S18Vsc;Z17A2U0M1G0SdSdSdS18Vsc;Z13A2S18Vsc;Z11A2A2S18Vsc;ZcA2A2S18Vsc;ZeA2A2U1G0SdSdSdSdS18Vsc;ZfA2S18Vsc;ZdA2A2S18Vsc;Z7A2A2S18Vsc;Z8A2A2S18Vsc;ZaA2A2U2G0S14S1cZ0Vsc;A2S1cVsc;ZbA2A2U3G1Xbx2Xbx2Xbx2Xbx2").

(* LPS 727298f3: the auxv the malloc contract reads is the launch's own, [InitState.O_aux] (object 3 of the
   start state).  Its length depends on the kernel's CONFIG_RSEQ flag [r]: 27 pairs (432 bytes), 29 with
   CONFIG_RSEQ (464), AT_RANDOM (25) at pair 24, AT_NULL last.  The view below is computed from that
   object; [am_auxv_vals] and the key lemmas check it by computation, one flag value at a time. *)

(* The literal value of the cell at literal offset [off] of [cs] (-1 when there is none). *)
Fixpoint aux_cell_lit (cs : list cell) (off : Z) : Z :=
  match cs with
  | [] => -1
  | c :: rest =>
      match c_off c with
      | SLit o => if Z.eqb o off then (match c_val c with SLit v => v | _ => -1 end) else aux_cell_lit rest off
      | _ => aux_cell_lit rest off
      end
  end.

(* An auxv object's keys: the literal at offset [16 j], for each pair [j] below its length [hi / 16]. *)
Definition aux_keys_of (o : sobj) : list Z :=
  match ob_hi o with
  | SLit hi => map (fun j : nat => aux_cell_lit (ob_cells o) (16 * Z.of_nat j)) (seq 0%nat (Z.to_nat (hi / 16)))
  | _ => []
  end.

(* The index of key [k] in [l] ([length l] when it is absent). *)
Fixpoint aux_key_index (k : Z) (l : list Z) : nat :=
  match l with
  | [] => O
  | x :: rest => if Z.eqb x k then O else S (aux_key_index k rest)
  end.

Definition am_auxv_obj (r : bool) : sobj := InitState.O_aux 0 (mkPhdrInfo 0%N 0%N 0%N) r.
Definition am_auxv_keys (r : bool) : list Z := aux_keys_of (am_auxv_obj r).
Definition AM_AUXV_N (r : bool) : nat := length (am_auxv_keys r).
Definition AM_AUXV_RIDX (r : bool) : nat := aux_key_index 25 (am_auxv_keys r).
Definition AM_AUXV_RANDOFF (r : bool) : Z := 16 * Z.of_nat (AM_AUXV_RIDX r) + 8.
Definition AM_AUXV_BYTES (r : bool) : Z := 16 * Z.of_nat (AM_AUXV_N r).

Lemma am_auxv_vals : forall r : bool,
  AM_AUXV_N r = (if r then 29 else 27)%nat /\ AM_AUXV_RIDX r = 24%nat /\
  AM_AUXV_RANDOFF r = 392 /\ AM_AUXV_BYTES r = (if r then 464 else 432).
Proof. intros [|]; (split; [|split; [|split]]); vm_compute; reflexivity. Qed.

(* The keys do not depend on the image (entry point, program headers). *)
Lemma am_auxv_keys_any : forall (pc : Z) (ph : PhdrInfo) (r : bool),
  aux_keys_of (InitState.O_aux pc ph r) = am_auxv_keys r.
Proof. intros pc ph [|]; vm_compute; reflexivity. Qed.

Lemma am_auxv_bytes_eq : forall r : bool, AM_AUXV_BYTES r = 16 * Z.of_nat (AM_AUXV_N r).
Proof. intros [|]; reflexivity. Qed.

Lemma am_auxv_randoff_eq : forall r : bool, AM_AUXV_RANDOFF r = 16 * Z.of_nat (AM_AUXV_RIDX r) + 8.
Proof. intros [|]; reflexivity. Qed.

Lemma am_auxv_ridx_lt : forall r : bool, (AM_AUXV_RIDX r < AM_AUXV_N r - 1)%nat.
Proof. intros r. destruct (am_auxv_vals r) as (EN & ER & _ & _). rewrite EN, ER. destruct r; simpl; lia. Qed.

(* The same over [Z], with no subtraction, for [lia] where many other facts are in context. *)
Lemma am_auxv_ridx_ltZ : forall r : bool, Z.of_nat (AM_AUXV_RIDX r) + 2 <= Z.of_nat (AM_AUXV_N r).
Proof. intros r. pose proof (am_auxv_ridx_lt r). lia. Qed.

Lemma am_auxv_key_rand : forall r : bool, nth (AM_AUXV_RIDX r) (am_auxv_keys r) 0 = 25.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma am_auxv_key_last : forall r : bool, nth (AM_AUXV_N r - 1)%nat (am_auxv_keys r) 0 = 0.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma am_auxv_keys_nz : forall (r : bool) (j : nat),
  (j < AM_AUXV_N r - 1)%nat -> nth j (am_auxv_keys r) 0 <> 0.
Proof.
  intros r j Hj.
  assert (X : forallb (fun i => negb (nth i (am_auxv_keys r) 0 =? 0)) (seq 0 (AM_AUXV_N r - 1)%nat) = true)
    by (destruct r; vm_compute; reflexivity).
  rewrite forallb_forall in X. specialize (X j ltac:(apply in_seq; lia)).
  apply Bool.negb_true_iff in X. apply Z.eqb_neq in X. exact X.
Qed.

Lemma am_auxv_keys_early : forall (r : bool) (j : nat),
  (j < AM_AUXV_RIDX r)%nat -> nth j (am_auxv_keys r) 0 <> 0 /\ nth j (am_auxv_keys r) 0 <> 25.
Proof.
  intros r j Hj.
  assert (X : forallb (fun i => negb (nth i (am_auxv_keys r) 0 =? 0) && negb (nth i (am_auxv_keys r) 0 =? 25))
                (seq 0 (AM_AUXV_RIDX r)) = true)
    by (destruct r; vm_compute; reflexivity).
  rewrite forallb_forall in X. specialize (X j ltac:(apply in_seq; lia)).
  apply andb_prop in X as [X1 X2]. apply Bool.negb_true_iff in X1. apply Bool.negb_true_iff in X2.
  apply Z.eqb_neq in X1. apply Z.eqb_neq in X2. auto.
Qed.

Lemma am_auxv_keys_late : forall (r : bool) (j : nat),
  (AM_AUXV_RIDX r < j < AM_AUXV_N r)%nat -> nth j (am_auxv_keys r) 0 <> 25.
Proof.
  intros r j Hj.
  assert (X : forallb (fun i => negb (nth i (am_auxv_keys r) 0 =? 25))
                (seq (S (AM_AUXV_RIDX r)) (AM_AUXV_N r - S (AM_AUXV_RIDX r))%nat) = true)
    by (destruct r; vm_compute; reflexivity).
  rewrite forallb_forall in X. specialize (X j ltac:(apply in_seq; lia)).
  apply Bool.negb_true_iff in X. apply Z.eqb_neq in X. exact X.
Qed.

Lemma auxv_u64 (z : Z) : 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Section ContractsI.
Variable segs : list Segment.
Variable C : mconsts.
Variable E : ientry_consts.

(* LPS 727298f3: with [Contract.vdso_ok md], as [MInvR]. *)
Definition MInvIR (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (A : MA) (rho : valuation) (md : Model) : Prop :=
  MInvI C X R U A (rd_of segs (rm rho)) (wok_of segs (rm rho)) (m_vmmaps md) /\ vdso_ok md.

Lemma MInvIR_MInvI (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (A : MA) (rho : valuation) (md : Model) :
  MInvIR X R U A rho md -> MInvI C X R U A (rd_of segs (rm rho)) (wok_of segs (rm rho)) (m_vmmaps md).
Proof. intros [H _]. exact H. Qed.
Lemma MInvIR_vdso (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (A : MA) (rho : valuation) (md : Model) :
  MInvIR X R U A rho md -> vdso_ok md.
Proof. intros [_ H]. exact H. Qed.

(* The same with a memory [m] in place of a valuation's: the frees' K-invariants carry it. *)
Definition MInvIm (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (A : MA) (m : word -> option byte) (md : Model) : Prop :=
  MInvI C X R U A (rd_of segs m) (wok_of segs m) (m_vmmaps md) /\ vdso_ok md.
Lemma MInvIm_MInvI (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (A : MA) (m : word -> option byte) (md : Model) :
  MInvIm X R U A m md -> MInvI C X R U A (rd_of segs m) (wok_of segs m) (m_vmmaps md).
Proof. intros [H _]. exact H. Qed.

Lemma MInvR_IR : ltac2:(tb__ "0|0|
S43S23S52S4S70Vsegs;VC;R3R2R1A5S0S5dS7S2dA1SeS8S2dS5A2A1S81R3R2R1A6S79S42R3A1A1A2A2Fmd;Frho;FA;").
Proof using .
  intros A rho md. unfold MInvR, MInvIR. split.
  - intros [H Hv]. apply MInv_MInvI in H. destruct H as [H1 H2]. split; [split; [exact H1 | exact Hv] | exact H2].
  - intros [[H1 Hv] H2]. split; [apply MInv_MInvI; split; [exact H1 | exact H2] | exact Hv].
Qed.

Definition maps_kept (A : MA) (m0 m1 : word -> option byte) : Prop := ltac2:(tb__ "0|2|
SaS2eS1ScS2eA1S86S42VA;A1R2A2S10S2eR1A2A3S1S3eS3bR2A1S36A3S1SbS3dR3A1S15A3S5S0S17S84S44VA;A1R6A2M0R1A2S19R1S16G0S3cR5A1A2A2A2S1ScS47Q8A1A1Vm1;S48Q40R2A2M1A1Vm0;G1A1A3F_;Fa;F_;F_;F_;Frg;Fk;").

Definition canary_kept (m0 m1 : word -> option byte) : Prop := ltac2:(tb__ "0|4|
S5S3S0S17S94VC;A1M0R1A2S19R1S16G0Z8M1A2A2A2S0S17S93VC;A1M2R1A2S19R1S16G2G1A2A2A2A2S1ScS47Q8A1A1S68Vsegs;Vm1;S48Q40R2A2M3A3S68Vsegs;Vm0;G3A3A3F_;Fa;").

Definition am_reads (m : word -> option byte) (a : Z) (w : nat) (v : Z) : Prop := ltac2:(tb__ "0|2|
SaS7cR1Vw;A2S1ScS47Q8M0A1M1A1S68Vsegs;Vm;S95S16Va;S1aR2A1A2A1A3S10G1S48G0S83Vv;Vw;R2A3A2A2A3F_;Fk;").

(* LPS 727298f3: the auxv requirement for the launch layout of CONFIG_RSEQ flag [r] (above); [auxv_init]
   holds for the run's own flag, so every contract that reads it keeps its statement. *)
Definition auxv_init_r (r : bool) (L : layout) (rho : valuation) : Prop :=
  let m := rm rho in
  let sp := bv_unsigned (rw rho 10%positive) in
  exists av q : Z,
    am_reads m (mc_auxv C) 8%nat av /\
    (forall j : nat, (j < AM_AUXV_N r)%nat -> am_reads m (av + 16 * Z.of_nat j) 8%nat (nth j (am_auxv_keys r) 0)) /\
    (forall j : nat, (j < AM_AUXV_N r)%nat -> exists v : Z, am_reads m (av + 16 * Z.of_nat j + 8) 8%nat v) /\
    am_reads m (av + AM_AUXV_RANDOFF r) 8%nat q /\
    am_reads m (q + 8) 8%nat (ly_sec L) /\
    av mod 8 = 0 /\
    q mod 8 = 0 /\
    sp <= av /\
    av + AM_AUXV_BYTES r <= 2 ^ 48 /\
    sp <= q + 8 /\
    q + 16 <= 2 ^ 48 /\
    (av + AM_AUXV_BYTES r <= q + 8 \/ q + 16 <= av) /\
    (PGSZ <= ly_brk0 L /\ ly_brk0 L < 46912496111616).

Definition auxv_init (L : layout) (rho : valuation) : Prop := exists r : bool, auxv_init_r r L rho.

Lemma auxv_init_mono : ltac2:(tb__ "0|2|
S7eS23S23S1S47Q40M0A1ScS47Q8A1A1F_;S24R1A1S24R2A1A3S17S46G0S22R2PaM1A2A2S46G0S22R3G1A2A2A2S5eR5R4A2S5eR6R4A2F_;F_;F_;Frho';Frho;FL;").
Proof using .
  intros L rho rho' Hm Hsp (r & av & q & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  exists r. unfold auxv_init_r. rewrite Hm. exists av, q. repeat split; try assumption; lia.
Qed.

Lemma auxv_init_brk0 : ltac2:(tb__ "0|1|
S7eS23S5eR2R1A2S0S17S31S7fR3A1M0A2S19G0Z2aaaaaaa9000A2A2F_;Frho;FL;").
Proof using . intros L rho (r & av & q & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

(* The auxv requirement read as [MallocLayout.auxv_ok], and kept across a change of the valuation, for
   either flag: the P and U walks use these through their own one-line instances. *)
Lemma am_reads_holds_gen (m : word -> option byte) (a : Z) (w : nat) (v : Z) :
  0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> am_reads m a w v ->
  MallocLayout.holds (byteview_of (Contract.rd_of segs m) (fun _ : word => true)) a w v.
Proof.
  intros Ha Hw H k Hk. specialize (H k Hk). unfold byteview_of.
  replace ((0 <=? a + Z.of_nat k) && (a + Z.of_nat k <? 2 ^ 64) && true)%bool with true
    by (symmetry; rewrite Bool.andb_true_r; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  unfold wz in H. rewrite H. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8%N) with 256. unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma auxv_ok_of_init_gen (Ly : layout) (rho : valuation) :
  0 <= mc_auxv C /\ mc_auxv C + 8 <= 2 ^ 64 ->
  auxv_init Ly rho ->
  topL Ly + 8 <= bv_unsigned (rw rho 10%positive) ->
  auxv_ok C Ly (byteview_of (Contract.rd_of segs (rm rho)) (fun _ : word => true)).
Proof.
  intros HC (f & av & q & R1 & R2 & R3 & R4 & R5 & M1 & M2 & S1 & S2 & S3 & S4 & DJ & A13) Hsp.
  pose proof (topL_range Ly) as TR.
  pose proof (am_auxv_bytes_eq f) as HB. pose proof (am_auxv_randoff_eq f) as HO.
  pose proof (am_auxv_ridx_ltZ f) as HRI.
  exists av, q, (Z.of_nat (AM_AUXV_RIDX f)).
  split; [apply am_reads_holds_gen; [lia | change (Z.of_nat 8) with 8; lia | exact R1]|].
  split.
  { pose proof (R2 (AM_AUXV_RIDX f) ltac:(lia)) as K. rewrite am_auxv_key_rand in K.
    apply am_reads_holds_gen; [lia | change (Z.of_nat 8) with 8; lia | exact K]. }
  split.
  { replace (av + 16 * Z.of_nat (AM_AUXV_RIDX f) + 8) with (av + AM_AUXV_RANDOFF f) by lia.
    apply am_reads_holds_gen; [lia | change (Z.of_nat 8) with 8; lia | exact R4]. }
  split; [apply am_reads_holds_gen; [lia | change (Z.of_nat 8) with 8; lia | exact R5]|].
  split.
  { intros i Hi. destruct (R3 (Z.to_nat i) ltac:(lia)) as [v Rv]. rewrite Z2Nat.id in Rv by lia.
    exists (nth (Z.to_nat i) (am_auxv_keys f) 0), v.
    pose proof (R2 (Z.to_nat i) ltac:(lia)) as Rk. rewrite Z2Nat.id in Rk by lia.
    destruct (am_auxv_keys_early f (Z.to_nat i) ltac:(lia)) as [K0 K25].
    split; [apply am_reads_holds_gen; [lia | change (Z.of_nat 8) with 8; lia | exact Rk]|].
    split; [exact K0|]. split; [apply am_reads_holds_gen; [lia | change (Z.of_nat 8) with 8; lia | exact Rv]|].
    intros EK. exfalso. exact (K25 EK). }
  split.
  { exists (Z.of_nat (AM_AUXV_N f - 1)%nat). split; [lia|].
    split.
    { pose proof (R2 (AM_AUXV_N f - 1)%nat ltac:(lia)) as K. rewrite am_auxv_key_last in K.
      apply am_reads_holds_gen; [lia | change (Z.of_nat 8) with 8; lia | exact K]. }
    intros i Hi. exists (nth (Z.to_nat i) (am_auxv_keys f) 0).
    pose proof (R2 (Z.to_nat i) ltac:(lia)) as Rk. rewrite Z2Nat.id in Rk by lia.
    split; [apply am_reads_holds_gen; [lia | change (Z.of_nat 8) with 8; lia | exact Rk]|].
    split; [exact (am_auxv_keys_nz f (Z.to_nat i) ltac:(lia)) | exact (am_auxv_keys_late f (Z.to_nat i) ltac:(lia))]. }
  lia.
Qed.

Lemma auxv_init_ext_gen (Ly : layout) (rho1 rho2 : valuation) :
  bv_unsigned (rw rho2 10%positive) <= bv_unsigned (rw rho1 10%positive) ->
  (forall a : word, bv_unsigned (rw rho1 10%positive) <= bv_unsigned a -> rm rho2 a = rm rho1 a) ->
  (forall k : Z, 0 <= k < 8 -> rm rho2 (Z_to_bv 64 (mc_auxv C + k)) = rm rho1 (Z_to_bv 64 (mc_auxv C + k))) ->
  auxv_init Ly rho1 -> auxv_init Ly rho2.
Proof.
  intros E10 Ehi Eav (f & av & q & R1 & R2 & R3 & R4 & R5 & M1 & M2 & S1 & S2 & S3 & S4 & DJ & A13).
  pose proof (am_auxv_bytes_eq f) as HB. pose proof (am_auxv_randoff_eq f) as HO.
  pose proof (am_auxv_ridx_ltZ f) as HRI.
  pose proof (bv_unsigned_in_range 64 (rw rho1 10%positive)) as U1.
  assert (RD : forall a w vv, (forall k, (k < w)%nat -> rm rho2 (wz (a + Z.of_nat k)) = rm rho1 (wz (a + Z.of_nat k))) ->
               am_reads (rm rho1) a w vv -> am_reads (rm rho2) a w vv).
  { intros a w vv Ek H k Hk. unfold Contract.rd_of in *. rewrite (Ek k Hk). exact (H k Hk). }
  assert (HI : forall a w vv, bv_unsigned (rw rho1 10%positive) <= a -> a + Z.of_nat w <= 2 ^ 64 ->
               am_reads (rm rho1) a w vv -> am_reads (rm rho2) a w vv).
  { intros a w vv Ha Hw. apply RD. intros k Hk. apply Ehi. unfold wz. rewrite auxv_u64 by lia. lia. }
  exists f. unfold auxv_init_r. exists av, q.
  split; [apply RD; [intros k Hk; unfold wz; apply Eav; lia | exact R1]|].
  split; [intros j Hj; apply HI; [lia | change (Z.of_nat 8) with 8; lia | exact (R2 j Hj)]|].
  split; [intros j Hj; destruct (R3 j Hj) as [vv Hv]; exists vv; apply HI; [lia | change (Z.of_nat 8) with 8; lia | exact Hv]|].
  split; [apply HI; [lia | change (Z.of_nat 8) with 8; lia | exact R4]|].
  split; [apply HI; [lia | change (Z.of_nat 8) with 8; lia | exact R5]|].
  repeat split; try assumption; lia.
Qed.

Lemma auxv_init_frame_gen (Ly : layout) (rho rho' : valuation) (lo : Z) :
  0 <= mc_auxv C /\ mc_auxv C + 8 <= 2 ^ 64 ->
  auxv_init Ly rho ->
  mc_auxv C + 8 <= lo ->
  (forall a : word, bv_unsigned a < lo \/ bv_unsigned (rw rho 10%positive) <= bv_unsigned a -> rm rho' a = rm rho a) ->
  bv_unsigned (rw rho' 10%positive) <= bv_unsigned (rw rho 10%positive) ->
  auxv_init Ly rho'.
Proof.
  intros HC (f & av & q & R1 & R2 & R3 & R4 & R5 & M1 & M2 & S1 & S2 & S3 & S4 & REST) Hlo AG Hsp.
  pose proof (am_auxv_bytes_eq f) as HB. pose proof (am_auxv_randoff_eq f) as HO.
  pose proof (am_auxv_ridx_ltZ f) as HRI.
  pose proof (bv_unsigned_in_range 64 (rw rho 10%positive)) as U10.
  set (sp := bv_unsigned (rw rho 10%positive)) in *.
  assert (TR : forall a w v, (a + Z.of_nat w <= lo \/ sp <= a) -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
               am_reads (rm rho) a w v -> am_reads (rm rho') a w v).
  { intros a w v Hr Ha Hw H k Hk. specialize (H k Hk). unfold Contract.rd_of in *.
    rewrite (AG (wz (a + Z.of_nat k))); [exact H|].
    unfold wz. rewrite auxv_u64 by lia. lia. }
  exists f. unfold auxv_init_r. exists av, q.
  split; [apply TR; [left; change (Z.of_nat 8) with 8; lia | lia | change (Z.of_nat 8) with 8; lia | exact R1]|].
  split; [intros j Hj; apply TR; [right; lia | lia | change (Z.of_nat 8) with 8; lia | exact (R2 j Hj)]|].
  split; [intros j Hj; destruct (R3 j Hj) as [v Hv]; exists v; apply TR; [right; lia | lia | change (Z.of_nat 8) with 8; lia | exact Hv]|].
  split; [apply TR; [right; lia | lia | change (Z.of_nat 8) with 8; lia | exact R4]|].
  split; [apply TR; [right; lia | lia | change (Z.of_nat 8) with 8; lia | exact R5]|].
  repeat (split; [first [assumption | lia]|]). destruct REST as [? ?]. lia.
Qed.

Lemma auxv_init_rdext_gen (Ly : layout) (rho rho' : valuation) :
  auxv_init Ly rho ->
  (forall a : word, Contract.rd_of segs (rm rho') a = Contract.rd_of segs (rm rho) a) ->
  rw rho' 10%positive = rw rho 10%positive ->
  auxv_init Ly rho'.
Proof.
  intros (f & av & q & R1 & R2 & R3 & R4 & R5 & REST) AG Hsp.
  assert (T : forall a w v, am_reads (rm rho) a w v -> am_reads (rm rho') a w v).
  { intros a w v H k Hk. rewrite AG. exact (H k Hk). }
  exists f. unfold auxv_init_r. exists av, q. rewrite Hsp.
  split; [apply T; exact R1|]. split; [intros j Hj; apply T; exact (R2 j Hj)|].
  split; [intros j Hj; destruct (R3 j Hj) as [v Hv]; exists v; apply T; exact Hv|].
  split; [apply T; exact R4|]. split; [apply T; exact R5|]. exact REST.
Qed.

Definition Pre_as : sstate := ltac2:(tb__ "0|0|
S28S50VE;A1S58S56S27SeS26A1S6S25S6cS49A1S7S25A1A3S12S21S6S21S6aS6S21S6bS49A1S7S21A1A3A3S69S49A1A3S55S11A9").

Definition L_as_fail : sstate := ltac2:(tb__ "0|1|
S28S4bVE;A1S5bS57S55A1S6S8SaS26A2M0SfSaS26UaS2aS20S1eZ2Z40A2Z1A2A1A4S7G0A1A3A2S56S27SeS26A1S6S25S6cS49A1S7S25A1A3S12S21S6S21S6aS6S21S6bS49A1S7S21A1A3A3S69S49A1A3S6dS11A9").
Definition L_as_ok : sstate := ltac2:(tb__ "0|0|
S28S4bVE;A1S57S55A1S56S27SeS26A1S6S25S6cS49A1S7S25A1A3S12S21S6S21S2bS2cS6eA1S2aZ1fA1A2S6S21S6aS6S21S6bS49A1S7S21A1A3A3A3S69S49A1A3S6dS11A9").

Definition J_as_pre (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|4|
S23S9S53A1S52S0S5dVX;SeS8S2dS5A2A1VU;VA;R3R1A6S0S7aVX;S42VA;A1M0A2S0VKc;R2R1A2S0S46Q40M1S22R3PcA2A2S5S46G1S22R4PdA2A2S5S0S0S17Z0M2R2A2S19R2Z30A2A2S0S17G2R1A2S0S17S16R1S30A2S39R2A1A2S17S96Z40S46G1S22R5S71A2A2A2S1fS4fS1aS51R2A1A1A1A1A2A2A2A2Treq;Tsc;S0S74VC;R3A2S0S1SbS3fG0A1S11A3S0S5eS44VA;A1R4A2S1S9S8S2dS3aA2M3A1S40G0A1S7G3A1A3A2F_;S73VA;R3A2A2A2A2A2A2A2Lmd;Ltr;Lrho;").

Definition JL_as_fail (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|6|
S23S23S9S53A1S52S46Q40M0S22R4PcA2A2S5S46G0S22R5PdA2A2S5S2S43S43S0S5dVX;SeS8S2dS5A2A1VU;R1R6R4A6S0S7aVX;S42R1A1M1A2S0S45S44VA;A1S44R1A1S13S2eS35S42VA;A1M2A1A2A3S0S8aG2G1R3A3S0S89G2G1A2S0S6fVsegs;VC;VA;R1S24R7A1M3S24R6A1M4A6S0S62G3G4A2S0SaS7bS88R4A1R1A2S2S9S8S34S5A2A1M5G5S80S8S5S2fA2S32R3R6R5G2A4R1SfS5S2fN1S42R4A1A4A4Lktr;A2F_;Ffuel;VKc;R5R4A2A2A2A2A2A2A2A2A2LA';A2Treq;Tsc;Lmd;Ltr;Lrho';Lrho0;").

Definition JL_as_ok (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|6|
S23S23S9S53A1S52S46Q40M0S22R4PcA2A2S5S46G0S22R5PdA2A2S5S46G0S22R5S6eA2A2S5S2S43S43S2S2dS2dS2S33S33S0S5dVX;S10S8S2dS5A2SfS2dS5R2R4A4A2VU;R3R9R7A6S0S7aVX;S42R3A1M1A2S0S45S44VA;A1S44R3A1S13S2eS35S42VA;A1M2A1A2A3S0S1ScS2dA1S82G1R6A2S10S2dR2A2A3S0S87VX;G1R2R1A4S0S1S5S38R1A1R6A3S0S17S16R5S30A2S41R1A1A2S0S0S17Z0R4A2S17R4S37R1A1A2A2S0S8aG2G1R6A3S0S89G2G1A2S0S6fVsegs;VC;VA;R3S24RaA1M3S24R9A1M4A6S0S62G3G4A2S0SaS7bS88R7A1R1A2S2S9S8S34S5A2A1M5G5S80S8S5S2fA2S32R3R9R8G2A4R1SfS5S2fR7S42R6A1A4A4Lktr;A2F_;Ffuel;VKc;R8R7A2A2A2A2A2A2A2A2A2A2A2A2A2A2Lam;A2Lg;A2LA';A2Tidx;Treq;Tsc;Lmd;Ltr;Lrho';Lrho0;").

Definition Posts_as X U A Kc : list (sstate * jpost) := ltac2:(tb__ "0|1|
S6S8S29S77A2M0SfS29S77S65S63VX;VU;VA;VKc;A4A4S6G0SfS29S77S66S64VX;VU;VA;VKc;A4A4S7G0A1A3A3").

Definition alloc_slot_sumI : Prop := ltac2:(tb__ "0|0|
S8eOF_;S9S2dA1S5S5F_;S43S9S53A1S52OF_;F_;S23S72Vsegs;R6R2A3S79S42R4A1A1S8dVsegs;R8S7dVsegs;S5fR7R6R5R4A4S61R3A4S78Vsegs;S55R3S60R7R6R5R4A4A4A4F_;F_;Frho;FKc;FA;FU;FX;Fok;").

Definition alloc_slot_sumI_ex : Prop := ltac2:(tb__ "0|0|
S9S2dA1S5S5F_;S43S9S53A1S52OF_;F_;S23S75R2A1S79S42R4A1A1S8cVsegs;S7dVsegs;S5fR7R6R5R4A4S61R3A4S78Vsegs;S55R3S60R7R6R5R4A4A4A3F_;F_;Frho;FKc;FA;FU;FX;").

End ContractsI.

(* As [Contract.MInvR_MInv]: an [MInvIR] hypothesis read as its invariant half [MInvI]. *)
Coercion MInvIR_MInvI : MInvIR >-> MInvI.
Coercion MInvIm_MInvI : MInvIm >-> MInvI.
#[global] Hint Extern 4 (vdso_ok ?m) =>
  match goal with
  | H : MInvIR _ _ _ _ _ _ _ ?m |- _ => exact (proj2 H)
  | H : MInvIm _ _ _ _ _ _ _ ?m |- _ => exact (proj2 H)
  end : typeclass_instances.

(* An [MInvIR] goal / hypothesis: as [minvr_split] / [minvr_dest] (Contract.v). *)
Ltac minvir_split :=
  lazymatch goal with
  | |- MInvIR _ _ _ _ _ _ _ ?m =>
      let V := fresh "VDs" in
      assert (V : vdso_ok m) by vdso_close;
      unfold MInvIR; refine (conj _ V)
  | _ => fail "minvir_split: the goal is not an MInvIR"
  end.
Ltac minvir_dest H :=
  let V := fresh "VD" in
  lazymatch type of H with
  | MInvIR _ _ _ _ _ _ _ _ => unfold MInvIR in H; destruct H as [H V]
  | _ => fail "minvir_dest: not an MInvIR"
  end.

Definition alloc_slot_sumI_P : Prop := ltac2:(tb__ "0|0|
S4aS59S90S4dA3").
Definition alloc_slot_sumI_U : Prop := ltac2:(tb__ "0|0|
S4aS5aS91S4eA3").
