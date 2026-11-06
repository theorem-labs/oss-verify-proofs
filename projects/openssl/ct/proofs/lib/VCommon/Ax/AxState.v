(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxAcct.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem StoreOk.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie ExBytes.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxMem AxMemC AxZZ.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ri (r : reg) : int := of_Z (bv_unsigned r).

Lemma phi_ri (r : reg) : to_Z (ri r) = bv_unsigned r.
Proof.
  unfold ri. rewrite of_Z_spec. apply Z.mod_small. pose proof (bv_unsigned_in_range 5 r) as H.
  change (bv_modulus 5) with 32 in H. change wB with (2^63). lia.
Qed.

Inductive dinstr : Type :=
| DLui (rd : int) (v : w64)
| DAuipc (rd : int) (v : w64)
| DJal (rd : int) (off : w64)
| DJalr (rd rs1 : int) (off : w64)
| DBranch (bc : branch_cond) (rs1 rs2 : int) (off : w64)
| DLoad (sz : msize) (sg : bool) (rd rs1 : int) (off : w64)
| DStore (sz : msize) (rs1 rs2 : int) (off : w64)
| DOpImm (op : aluop) (rd rs1 : int) (imm : w64)
| DShiftImm (op : aluop) (rd rs1 : int) (sh : w64)
| DOp (op : aluop) (rd rs1 rs2 : int)
| DOpImm32 (rd rs1 : int) (imm : w64)
| DShiftImm32 (op : aluop) (rd rs1 : int) (sh : w64)
| DOp32 (op : aluop) (rd rs1 rs2 : int)
| DMul (op : mulop) (rd rs1 rs2 : int)
| DMul32 (op : mulop) (rd rs1 rs2 : int)
| DFence
| DLr (wd : awidth) (rd rs1 : int)
| DSc (wd : awidth) (rd rs1 rs2 : int)
| DAmo (op : amoop) (wd : awidth) (rd rs1 rs2 : int)
| DUnsupported.

Definition dec (i : instr) : dinstr :=
  match i with
  | Lui rd imm => DLui (ri rd) (w_of_bv (sext 64 (bv_concat 32 imm (Z_to_bv 12 0))))
  | Auipc rd imm => DAuipc (ri rd) (w_of_bv (sext 64 (bv_concat 32 imm (Z_to_bv 12 0))))
  | Jal rd imm => DJal (ri rd) (w_of_bv (sext 64 imm))
  | Jalr rd rs1 imm => DJalr (ri rd) (ri rs1) (w_of_bv (sext 64 imm))
  | Branch bc rs1 rs2 imm => DBranch bc (ri rs1) (ri rs2) (w_of_bv (sext 64 imm))
  | Load sz sg rd rs1 imm => DLoad sz sg (ri rd) (ri rs1) (w_of_bv (sext 64 imm))
  | Store sz rs1 rs2 imm => DStore sz (ri rs1) (ri rs2) (w_of_bv (sext 64 imm))
  | OpImm op rd rs1 imm => DOpImm op (ri rd) (ri rs1) (w_of_bv (sext 64 imm))
  | ShiftImm op rd rs1 sh => DShiftImm op (ri rd) (ri rs1) (w_of_bv (zext 64 sh))
  | Op op rd rs1 rs2 => DOp op (ri rd) (ri rs1) (ri rs2)
  | OpImm32 rd rs1 imm => DOpImm32 (ri rd) (ri rs1) (w_of_bv (sext 64 imm))
  | ShiftImm32 op rd rs1 sh => DShiftImm32 op (ri rd) (ri rs1) (w_of_bv (zext 64 sh))
  | Op32 op rd rs1 rs2 => DOp32 op (ri rd) (ri rs1) (ri rs2)
  | Mul op rd rs1 rs2 => DMul op (ri rd) (ri rs1) (ri rs2)
  | Mul32 op rd rs1 rs2 => DMul32 op (ri rd) (ri rs1) (ri rs2)
  | Fence _ _ _ _ _ => DFence
  | FenceI _ _ _ => DFence
  | Lr wd _ _ rd rs1 => DLr wd (ri rd) (ri rs1)
  | Sc wd _ _ rd rs1 rs2 => DSc wd (ri rd) (ri rs1) (ri rs2)
  | Amo op wd _ _ rd rs1 rs2 => DAmo op wd (ri rd) (ri rs1) (ri rs2)
  | _ => DUnsupported
  end.

(* [comment removed for export] *)
Inductive icent : Type :=
| ICEcall (w : bv 32)
| ICInstr (w : bv 32) (i : instr) (d : dinstr).

Definition ic_depth : nat := 24.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition aregs := itrie xv.

(* [comment removed for export] *)
Definition aget (m : aregs) (r : int) : xv :=
  if (r =? 0)%uint63 then XL w_zero else match iget 5 m r with Some v => v | None => XL w_zero end.

Definition aset (m : aregs) (r : int) (v : xv) : aregs :=
  if (r =? 0)%uint63 then m else iset 5 m r v.

Definition reg_a0 : int := 10%uint63.

(* [comment removed for export] *)
Inductive rsv : Type :=
| RNone
| RSome (v : xv)
| RUnk.

Record astate (M : Type) : Type := AS {
  a_pc : w64;
  a_regs : aregs;
  a_resv : rsv;
  a_mem : list region;
  a_facts : store;
  a_model : M;
  a_budget : Z;       (* [comment removed for export] *)
  a_steps : Z
}.
Arguments AS {M}.
Arguments a_pc {M}.
Arguments a_regs {M}.
Arguments a_resv {M}.
Arguments a_mem {M}.
Arguments a_facts {M}.
Arguments a_model {M}.
Arguments a_budget {M}.
Arguments a_steps {M}.

Definition w_four : w64 := W false 4%uint63.

Lemma wbv_four : wbv w_four = Z_to_bv 64 4.
Proof. reflexivity. Qed.

Definition npc {M : Type} (A : astate M) : w64 := w_add (a_pc A) w_four.

(* [comment removed for export] *)
Definition pc_ok (pc : w64) : bool :=
  if wh pc then false else ((wl pc land 3 =? 0)%uint63 &&& (wl pc <? 67108864)%uint63).

Lemma pc_ok_spec (pc : w64) : pc_ok pc = true -> wZ pc mod 4 = 0 /\ wZ pc < 2 ^ 26.
Proof.
  unfold pc_ok. destruct pc as [h l]. cbn [wh wl]. destruct h; [discriminate|]. intros H.
  destruct (eqbP (l land 3)%uint63 0%uint63) as [E1|E1]; [|discriminate].
  destruct (ltbP l 67108864) as [E2|E2]; [|discriminate].
  unfold wZ. cbn [wh wl]. rewrite Z.add_0_l. split; [|exact E2].
  rewrite land_spec' in E1. change (to_Z 0%uint63) with 0 in E1. change (to_Z 3%uint63) with (Z.ones 2) in E1. rewrite Z.land_ones in E1 by lia.
  exact E1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sh_off : Z := 2147450880.

Definition in_segs (segs : list Segment) (z : Z) : Prop :=
  exists sg, In sg segs /\ Z.of_N (seg_base sg) <= z < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).

(* [comment removed for export] *)
Definition in_ledger (segs : list Segment) (h : VmMaps) (z : Z) : Prop :=
  in_segs segs z \/ alloc_top h <= z \/ inl (vm_maps h) z.

(* [comment removed for export] *)
Definition ro_at (segs : list Segment) (z : Z) : bool :=
  match find_segment segs z 1 with Some sg => negb (seg_writable sg) | None => false end.

(* [comment removed for export] *)
Definition in_ledger_w (segs : list Segment) (h : VmMaps) (z : Z) : Prop :=
  (in_segs segs z /\ ro_at segs z = false) \/ alloc_top h <= z \/ inl (vm_maps h) z.

Lemma in_ledger_w_in (segs : list Segment) (h : VmMaps) (z : Z) : in_ledger_w segs h z -> in_ledger segs h z.
Proof. intros [[H _]|[H|H]]; [left; exact H | right; left; exact H | right; right; exact H]. Qed.

Definition mem_cov (segs : list Segment) (model : Model) (m : word -> option byte) : Prop :=
  forall x : word, m x <> None -> in_ledger_w segs (m_vmmaps model) (bv_unsigned x).

(* [comment removed for export] *)
Lemma in_ledger_of_w (segs : list Segment) (h h' : VmMaps) :
  (forall q, in_ledger_w segs h q -> in_ledger_w segs h' q) -> forall q, in_ledger segs h q -> in_ledger segs h' q.
Proof.
  intros H q [Hq|Hq]; [left; exact Hq|]. apply (in_ledger_w_in segs h' q). apply H. right. exact Hq.
Qed.

Lemma in_ledger_of_w_out (segs : list Segment) (h h' : VmMaps) (P : Z -> Prop) :
  (forall q, P q -> in_ledger_w segs h q -> in_ledger_w segs h' q) -> forall q, P q -> in_ledger segs h q -> in_ledger segs h' q.
Proof.
  intros H q HP [Hq|Hq]; [left; exact Hq|]. apply (in_ledger_w_in segs h' q). apply (H q HP). right. exact Hq.
Qed.

Lemma mem_cov_in (segs : list Segment) (model : Model) (m : word -> option byte) :
  mem_cov segs model m -> forall x : word, m x <> None -> in_ledger segs (m_vmmaps model) (bv_unsigned x).
Proof. intros H x Hx. exact (in_ledger_w_in segs _ _ (H x Hx)). Qed.

(* [comment removed for export] *)
Definition preimage (z q : Z) : Prop := 8 * (z - sh_off) <= q < 8 * (z - sh_off) + 8.

Definition comp_inv (segs : list Segment) (ρ : valuation) (A : list region) (model : Model) : Prop :=
  forall R, In R A -> is_shadow R = true ->
    forall z, in_rg ρ R z -> in_ss z /\ forall q, preimage z q -> in_ledger segs (m_vmmaps model) q.

Definition na_ok (segs : list Segment) (ρ : valuation) (A : list region) (model : Model) (m : word -> option byte) : Prop :=
  (forall x : word, m x <> None -> ~ inl (vm_noaccess (m_vmmaps model)) (bv_unsigned x))
  /\ (forall z, in_segs segs z -> ~ inl (vm_noaccess (m_vmmaps model)) z)
  /\ (forall R, In R A -> is_shadow R = true ->
        forall z, in_rg ρ R z -> forall q, preimage z q -> ~ inl (vm_noaccess (m_vmmaps model)) q).

Section Ledger.
Variable segs : list Segment.

Lemma mem_cov_backing (model : Model) (m : word -> option byte) (lz : list (word * word)) (pages : list word) :
  mem_cov segs model m -> mem_cov segs (with_vm_backing lz pages model) m.
Proof. intros H. exact H. Qed.

Lemma comp_inv_backing (ρ : valuation) (A : list region) (model : Model) (lz : list (word * word)) (pages : list word) :
  comp_inv segs ρ A model -> comp_inv segs ρ A (with_vm_backing lz pages model).
Proof. intros H. exact H. Qed.

Lemma na_ok_backing (ρ : valuation) (A : list region) (model : Model) (m : word -> option byte) (lz : list (word * word)) (pages : list word) :
  na_ok segs ρ A model m -> na_ok segs ρ A (with_vm_backing lz pages model) m.
Proof. intros H. exact H. Qed.

Lemma in_rg_same (ρ : valuation) (R R' : region) (z : Z) : same_fields R R' -> in_rg ρ R' z -> in_rg ρ R z.
Proof. intros HS. unfold in_rg. rewrite (rbase_same ρ R R' HS). destruct HS as [_ [_ [E3 _]]]. rewrite E3. exact (fun X => X). Qed.

Lemma comp_inv_geom (ρ : valuation) (A A' : list region) (model : Model) :
  Forall2 same_fields A A' -> comp_inv segs ρ A model -> comp_inv segs ρ A' model.
Proof.
  intros HF H R' HIn Hs z Hz. destruct (Forall2_In_l _ A A' R' HF HIn) as [R0 [HR0 HS]].
  rewrite (is_shadow_same R0 R' HS) in Hs. exact (H R0 HR0 Hs z (in_rg_same ρ R0 R' z HS Hz)).
Qed.

Lemma na_ok_geom (ρ : valuation) (A A' : list region) (model : Model) (m : word -> option byte) :
  Forall2 same_fields A A' -> na_ok segs ρ A model m -> na_ok segs ρ A' model m.
Proof.
  intros HF [N1 [N2 N3]]. split; [exact N1|]. split; [exact N2|]. intros R' HIn Hs z Hz.
  destruct (Forall2_In_l _ A A' R' HF HIn) as [R0 [HR0 HS]].
  rewrite (is_shadow_same R0 R' HS) in Hs. exact (N3 R0 HR0 Hs z (in_rg_same ρ R0 R' z HS Hz)).
Qed.

(* [comment removed for export] *)
Lemma wview_cases (m : word -> option byte) (y : word) :
  wview segs m y <> None -> m y <> None \/ in_segs segs (bv_unsigned y).
Proof.
  unfold wview. destruct (m y) as [b|]; [left; discriminate|]. intros H. right.
  destruct (find_segment segs (bv_unsigned y) 1) as [sg|] eqn:Ef; [|exfalso; apply H; reflexivity].
  destruct (find_segment_at' segs (bv_unsigned y) sg Ef) as [HIn Hr]. exists sg. split; [exact HIn | exact Hr].
Qed.

(* [comment removed for export] *)
Lemma wview_cases_w (m : word -> option byte) (y : word) :
  wview segs m y <> None -> m y <> None \/ (in_segs segs (bv_unsigned y) /\ ro_at segs (bv_unsigned y) = false).
Proof.
  unfold wview, ro_at. destruct (m y) as [b|]; [left; discriminate|]. intros H. right.
  destruct (find_segment segs (bv_unsigned y) 1) as [sg|] eqn:Ef; [|exfalso; apply H; reflexivity].
  destruct (find_segment_at' segs (bv_unsigned y) sg Ef) as [HIn Hr]. split; [exists sg; split; [exact HIn | exact Hr]|].
  destruct (seg_writable sg); [reflexivity | exfalso; apply H; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma mem_cov_range (model : Model) (m m' : word -> option byte) (a : Z) (n : nat) :
  mem_cov segs model m -> 0 <= a -> a + Z.of_nat n <= two64 -> store_ok segs m (wz a) n = true ->
  (forall x : word, ~ (a <= bv_unsigned x < a + Z.of_nat n) -> m' x = m x) -> mem_cov segs model m'.
Proof.
  intros H Ha Hn Hok Hout x Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) a) as [L|L]; [rewrite Hout in Hx by lia; exact (H x Hx)|].
  destruct (Z_lt_le_dec (bv_unsigned x) (a + Z.of_nat n)) as [L2|L2]; [|rewrite Hout in Hx by lia; exact (H x Hx)].
  pose proof (store_ok_wview segs m n a Ha Hn Hok (bv_unsigned x) ltac:(lia)) as Hw.
  replace (wz (bv_unsigned x)) with x in Hw by (apply bv_eq; rewrite u_wz; [reflexivity | pose proof (bvu_range x); unfold two64 in *; lia]).
  destruct (wview_cases_w m x Hw) as [Hm|Hs]; [exact (H x Hm) | left; exact Hs].
Qed.

Lemma na_ok_range (ρ : valuation) (A : list region) (model : Model) (m m' : word -> option byte) (a : Z) (n : nat) :
  na_ok segs ρ A model m -> 0 <= a -> a + Z.of_nat n <= two64 -> store_ok segs m (wz a) n = true ->
  (forall x : word, ~ (a <= bv_unsigned x < a + Z.of_nat n) -> m' x = m x) -> na_ok segs ρ A model m'.
Proof.
  intros [N1 [N2 N3]] Ha Hn Hok Hout. split; [|split; [exact N2 | exact N3]]. intros x Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) a) as [L|L]; [rewrite Hout in Hx by lia; exact (N1 x Hx)|].
  destruct (Z_lt_le_dec (bv_unsigned x) (a + Z.of_nat n)) as [L2|L2]; [|rewrite Hout in Hx by lia; exact (N1 x Hx)].
  pose proof (store_ok_wview segs m n a Ha Hn Hok (bv_unsigned x) ltac:(lia)) as Hw.
  replace (wz (bv_unsigned x)) with x in Hw by (apply bv_eq; rewrite u_wz; [reflexivity | pose proof (bvu_range x); unfold two64 in *; lia]).
  destruct (wview_cases m x Hw) as [Hm|Hs]; [exact (N1 x Hm) | exact (N2 _ Hs)].
Qed.

Lemma write_outside (m : word -> option byte) (a : word) (bs : list byte) (x : word) :
  bv_unsigned a + Z.of_nat (length bs) <= two64 ->
  ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs)) -> write_to_mem m a bs x = m x.
Proof.
  intros H64 Hx. pose proof (bvu_range a) as Har.
  replace a with (wz (bv_unsigned a)) at 1 by (apply bv_eq; rewrite u_wz; [reflexivity | unfold two64 in *; lia]).
  rewrite write_to_mem_spec by (unfold two64 in *; lia).
  replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + Z.of_nat (length bs))) with false; [reflexivity|].
  symmetry. apply Bool.not_true_iff_false. intros Hc. apply andb_prop in Hc as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_written (m : word -> option byte) : forall (bs : list byte) (a x : word),
  store_ok segs m a (length bs) = true -> write_to_mem m a bs x <> None -> m x <> None \/ wview segs m x <> None.
Proof.
  intros bs. revert m. induction bs as [|b bs IH]; intros m a x Hok Hx; cbn [write_to_mem length store_ok] in *; [left; exact Hx|].
  destruct (wview segs m a) as [b0|] eqn:Ew; [|discriminate].
  destruct (bv_eqb x a) eqn:Exa.
  - right. assert (x = a) by (apply bv_eq; unfold bv_eqb in Exa; apply Z.eqb_eq in Exa; exact Exa). subst x. rewrite Ew. discriminate.
  - assert (Hok' : store_ok segs (fun y => if bv_eqb y a then Some b else m y) (a + 1)%bv (length bs) = true).
    { apply (store_ok_mono segs _ m); [|exact Hok]. intros y Hy. destruct (bv_eqb y a); [discriminate | exact Hy]. }
    destruct (IH _ (a + 1)%bv x Hok' Hx) as [H1|H1].
    + rewrite Exa in H1. left. exact H1.
    + unfold wview in H1 |- *. rewrite Exa in H1. right. exact H1.
Qed.

Lemma mem_cov_write (model : Model) (m : word -> option byte) (a : word) (bs : list byte) :
  mem_cov segs model m -> store_ok segs m a (length bs) = true -> mem_cov segs model (write_to_mem m a bs).
Proof.
  intros H Hok x Hx. destruct (store_ok_written m bs a x Hok Hx) as [Hm|Hw]; [exact (H x Hm)|].
  destruct (wview_cases_w m x Hw) as [Hm|Hs]; [exact (H x Hm) | left; exact Hs].
Qed.

Lemma na_ok_write (ρ : valuation) (A : list region) (model : Model) (m : word -> option byte) (a : word) (bs : list byte) :
  na_ok segs ρ A model m -> store_ok segs m a (length bs) = true -> na_ok segs ρ A model (write_to_mem m a bs).
Proof.
  intros [N1 [N2 N3]] Hok. split; [|split; [exact N2 | exact N3]]. intros x Hx.
  destruct (store_ok_written m bs a x Hok Hx) as [Hm|Hw]; [exact (N1 x Hm)|].
  destruct (wview_cases m x Hw) as [Hm|Hs]; [exact (N1 x Hm) | exact (N2 _ Hs)].
Qed.

End Ledger.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Rel.
Variable segs : list Segment.
Variable M : Type.
Variable MRρ : M -> Model -> Prop.        (* [comment removed for export] *)
Variable LIM : Z.                         (* [comment removed for export] *)
Variable ρ : valuation.

Definition RRegs (am : aregs) (ms : machine_state) : Prop :=
  forall r : reg, xv_val ρ (aget am (ri r)) (rg ms r).

Definition RResv (r : rsv) (mr : option word) : Prop :=
  match r with
  | RNone => mr = None
  | RSome v => exists a, mr = Some a /\ xv_val ρ v a
  | RUnk => True
  end.

Definition icent_ok (pcz : Z) (e : icent) : Prop :=
  match e with
  | ICEcall w => fetch_word segs (Z_to_bv 64 pcz) = Some w /\ is_ecall w = true
  | ICInstr w i d => fetch_word segs (Z_to_bv 64 pcz) = Some w /\ is_ecall w = false
                     /\ decode_any w = Some (i, 4) /\ d = dec i
  end.

Definition ICok (ic : itrie icent) : Prop :=
  forall (k : int) e, to_Z k < 2 ^ Z.of_nat ic_depth -> iget ic_depth ic k = Some e -> icent_ok (4 * to_Z k) e.

Record R (A : astate M) (c : config) : Prop := {
  r_pc : ms_pc_val (cfg_ms c) = wbv (a_pc A);
  r_al : wZ (a_pc A) mod 4 = 0 /\ wZ (a_pc A) < 2 ^ 26;
  r_svc : ms_svc_pending (cfg_ms c) = None;
  r_regs : RRegs (a_regs A) (cfg_ms c);
  r_resv : RResv (a_resv A) (ms_resv (cfg_ms c));
  r_rom : ms_rom (cfg_ms c) = seg_rom segs;
  r_mem : RMem segs ρ (a_mem A) (ms_mem (cfg_ms c));
  r_model : MRρ (a_model A) (cfg_model c);
  r_halted : m_halted (cfg_model c) = None;
  r_budget : vm_backing_used (cfg_model c) <= a_budget A /\ vm_limit (m_vmmaps (cfg_model c)) = LIM;
  r_sat : sat ρ (a_facts A);
  r_hs : hs_ok ρ (a_mem A) (ms_mem (cfg_ms c));
  r_cov : mem_cov segs (cfg_model c) (ms_mem (cfg_ms c));
  r_comp : comp_inv segs ρ (a_mem A) (cfg_model c);
  r_na : na_ok segs ρ (a_mem A) (cfg_model c) (ms_mem (cfg_ms c))
}.

End Rel.

(* [comment removed for export] *)
Lemma ri_inj (r1 r2 : reg) : ri r1 = ri r2 -> r1 = r2.
Proof. intros H. apply bv_eq. rewrite <- !phi_ri, H. reflexivity. Qed.

Lemma aget_aset_int (m : aregs) (r r' : int) (v : xv) : to_Z r < 32 -> to_Z r' < 32 ->
  aget (aset m r v) r' = if (r' =? 0)%uint63 then XL w_zero else if (r =? r')%uint63 then v else aget m r'.
Proof.
  intros Hr Hr'. unfold aget, aset. destruct (eqbP r' 0%uint63) as [E0|E0]; [reflexivity|].
  destruct (eqbP r 0%uint63) as [Er|Er].
  - destruct (eqbP r r') as [E|E]; [exfalso; apply E0; rewrite <- E; exact Er | reflexivity].
  - rewrite iget_iset. pose proof (to_Z_bounded r). pose proof (to_Z_bounded r'). change (2 ^ Z.of_nat 5) with 32.
    rewrite !Z.mod_small by lia.
    destruct (eqbP r r') as [E|E].
    + rewrite E, Z.eqb_refl. reflexivity.
    + destruct (Z.eqb_spec (to_Z r) (to_Z r')) as [E2|E2]; [contradiction | reflexivity].
Qed.

Lemma ri_lt32 (r : reg) : to_Z (ri r) < 32.
Proof. rewrite phi_ri. pose proof (bv_unsigned_in_range 5 r) as H. change (bv_modulus 5) with 32 in H. lia. Qed.

Lemma aget_aset (m : aregs) (rd r : reg) (v : xv) :
  aget (aset m (ri rd) v) (ri r) =
  if (bv_unsigned r =? 0) then XL w_zero else if (bv_unsigned rd =? bv_unsigned r) then v else aget m (ri r).
Proof.
  unfold aget, aset. pose proof (bv_unsigned_in_range 5 rd) as Hd. pose proof (bv_unsigned_in_range 5 r) as Hr.
  change (bv_modulus 5) with 32 in *.
  assert (E0 : forall x : reg, (ri x =? 0)%uint63 = (bv_unsigned x =? 0)).
  { intros x. destruct (eqbP (ri x) 0) as [E|E]; rewrite phi_ri in E; change (to_Z 0%uint63) with 0 in E; symmetry;
      [apply Z.eqb_eq | apply Z.eqb_neq]; exact E. }
  rewrite !E0. destruct (Z.eqb_spec (bv_unsigned r) 0) as [Hr0|Hr0]; [reflexivity|].
  destruct (Z.eqb_spec (bv_unsigned rd) 0) as [Hd0|Hd0].
  - destruct (Z.eqb_spec (bv_unsigned rd) (bv_unsigned r)); [lia | reflexivity].
  - rewrite iget_iset. rewrite !phi_ri. rewrite !Z.mod_small by (change (2 ^ Z.of_nat 5) with 32; lia).
    destruct (Z.eqb_spec (bv_unsigned rd) (bv_unsigned r)); reflexivity.
Qed.

Lemma rg_setx (ms : machine_state) (rd r : reg) (x pc : word) (resv : option word) (mem : word -> option byte) :
  rg (setx ms rd x pc resv mem) r = if is_x0 r then w0 else if is_x0 rd then rg ms r else if bv_eqb rd r then x else rg ms r.
Proof.
  unfold rg, setx. cbn [ms_regs]. destruct (is_x0 r) eqn:Er; [reflexivity|]. destruct (is_x0 rd) eqn:Ed; [reflexivity|].
  unfold reg_get. destruct (bv_eqb rd r) eqn:E.
  - unfold bv_eqb in E. apply Z.eqb_eq in E. assert (rd = r) by (apply bv_eq; exact E). subst. rewrite bvmap_get_set_same. reflexivity.
  - rewrite bvmap_get_set_other; [reflexivity|]. intros C. subst. unfold bv_eqb in E. rewrite Z.eqb_refl in E. discriminate.
Qed.

Lemma RRegs_set (ρ : valuation) (m : aregs) (ms : machine_state) (rd : reg) (v : xv) (x pc : word) resv mem :
  RRegs ρ m ms -> xv_val ρ v x -> RRegs ρ (aset m (ri rd) v) (setx ms rd x pc resv mem).
Proof.
  intros H Hv r. rewrite aget_aset, rg_setx. unfold is_x0, bv_eqb.
  destruct (Z.eqb_spec (bv_unsigned r) 0) as [Hr|Hr]; [cbn [xv_val]; reflexivity|].
  destruct (Z.eqb_spec (bv_unsigned rd) 0) as [Hd|Hd].
  - destruct (Z.eqb_spec (bv_unsigned rd) (bv_unsigned r)); [lia|]. specialize (H r). unfold rg, is_x0 in H.
    rewrite (proj2 (Z.eqb_neq _ _) Hr) in H. unfold rg, is_x0. rewrite (proj2 (Z.eqb_neq _ _) Hr). exact H.
  - destruct (Z.eqb_spec (bv_unsigned rd) (bv_unsigned r)); [exact Hv|]. exact (H r).
Qed.

Lemma RRegs_set0 (ρ : valuation) (m : aregs) (ms : machine_state) (x pc : word) resv mem :
  RRegs ρ m ms -> RRegs ρ m (setx ms 0 x pc resv mem).
Proof.
  intros H r. rewrite rg_setx. change (is_x0 0) with true. cbn. destruct (is_x0 r) eqn:E; [|exact (H r)].
  specialize (H r). unfold rg in H. rewrite E in H. exact H.
Qed.
