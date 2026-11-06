(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie AxFetchFast AxFetchFast2 AxDecInt.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import MState Mem Exec.
From OSSVerify.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section StepSound.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition core_of (ms : machine_state) : core :=
  Core (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms).

Definition Rregs (rho : valuation) (Rg : regfile hval) (c : core) : Prop :=
  forall r : reg, den rho (rf_get vzero Rg (rix_of_reg r)) (Sem.rget c r).

Definition Rresv (rho : valuation) (r : hresv) (x : option word) : Prop :=
  match r with
  | RNone => x = None
  | RSome a => exists w, x = Some w /\ den rho a w
  | RUnk => True
  end.

Definition R (rho : valuation) (S : sstate) (ms : machine_state) : Prop :=
  ms_svc_pending ms = None /\ ms_pc_val ms = wbv (s_pc S) /\ Rregs rho (s_regs S) (core_of ms)
  /\ Rresv rho (s_resv S) (ms_resv ms) /\ Rmem segs rho (s_mem S) (ms_mem ms).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rix_of_reg_inj (r r' : reg) : rix_of_reg r = rix_of_reg r' -> r = r'.
Proof. intros H. apply bv_eq. rewrite <- !rix_of_reg_Z. rewrite H. reflexivity. Qed.

Lemma rix_of_reg_X0 (r : reg) : rix_of_reg r = X0 <-> is_x0 r = true.
Proof.
  unfold is_x0. rewrite Z.eqb_eq. rewrite <- rix_of_reg_Z. split; [intros ->; reflexivity|].
  intros H. apply rix_Z_inj. exact H.
Qed.

Lemma rget_rset (c : core) (rd r : reg) (v : word) :
  Sem.rget (Sem.rset rd v c) r = if is_x0 r then w0 else if is_x0 rd then Sem.rget c r else if decide (rd = r) then v else Sem.rget c r.
Proof.
  unfold Sem.rget, Sem.rset. destruct (is_x0 r) eqn:E0; [destruct (is_x0 rd); reflexivity|].
  destruct (is_x0 rd) eqn:Ed; [reflexivity|]. destruct c as [Rg F pc fc rv]. cbn [with_regs c_regs].
  destruct (decide (rd = r)) as [->|Hne]; [apply reg_get_set_same | apply reg_get_set_other; exact Hne].
Qed.

Lemma Rregs_set (rho : valuation) (Rg : regfile hval) (c : core) (rd : reg) (hv : hval) (v : word) :
  Rregs rho Rg c -> den rho hv v -> Rregs rho (rf_set Rg (rix_of_reg rd) hv) (Sem.rset rd v c).
Proof.
  intros HR Hv r. rewrite rget_rset. destruct (is_x0 r) eqn:E0.
  - apply rix_of_reg_X0 in E0. rewrite E0. destruct (rix_of_reg rd); exact (den_vzero rho).
  - destruct (is_x0 rd) eqn:Ed.
    + apply rix_of_reg_X0 in Ed. rewrite Ed. cbn [rf_set]. exact (HR r).
    + destruct (decide (rd = r)) as [->|Hne].
      * rewrite rf_get_set_same; [exact Hv|]. intros X. apply rix_of_reg_X0 in X. congruence.
      * rewrite rf_get_set_other; [exact (HR r)|]. intros X. apply rix_of_reg_inj in X. exact (Hne X).
Qed.

Lemma Rregs_core (rho : valuation) (Rg : regfile hval) (c c' : core) : c_regs c' = c_regs c -> Rregs rho Rg c -> Rregs rho Rg c'.
Proof. intros E H r. unfold Sem.rget. rewrite E. exact (H r). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ic_ok (ic : icache) : Prop :=
  forall pc d, pc_ok pc = true -> ic_get ic pc = Some d ->
    exists w i, fetch_word segs (wbv pc) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4) /\ d = predec i.

Lemma ic_ok_empty : ic_ok IEmpty.
Proof. intros pc d _ H. unfold ic_get in H. rewrite iget_empty in H. discriminate. Qed.

Lemma pc_ok_spec (pc : w64) : pc_ok pc = true -> wh pc = false /\ to_Z (wl pc) mod 4 = 0 /\ to_Z (wl pc) < 2 ^ 26.
Proof.
  unfold pc_ok. destruct (wh pc); [discriminate|]. intros H. apply andb_prop in H as [H1 H2].
  destruct (eqbP (wl pc land 3)%uint63 0%uint63) as [E1|E1]; [|discriminate].
  apply ltb_spec in H2. split; [reflexivity|]. split; [|exact H2].
  rewrite land_spec' in E1. change (to_Z 0%uint63) with 0 in E1. change (to_Z 3%uint63) with (Z.ones 2) in E1.
  rewrite Z.land_ones in E1 by lia. exact E1.
Qed.

Lemma ic_key_inj (pc pc' : w64) : pc_ok pc = true -> pc_ok pc' = true ->
  to_Z (ic_key pc) mod 2 ^ Z.of_nat ICD = to_Z (ic_key pc') mod 2 ^ Z.of_nat ICD -> pc = pc'.
Proof.
  intros H H' E. destruct (pc_ok_spec pc H) as (Hh & Hm & Hl). destruct (pc_ok_spec pc' H') as (Hh' & Hm' & Hl').
  unfold ic_key in E. rewrite !lsr_spec in E. change (2 ^ to_Z 2%uint63) with 4 in E.
  pose proof (to_Z_bounded (wl pc)) as B. pose proof (to_Z_bounded (wl pc')) as B'.
  change (2 ^ Z.of_nat ICD) with (2 ^ 24) in E.
  rewrite !Z.mod_small in E by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (to_Z (wl pc) = to_Z (wl pc')).
  { rewrite (Z.div_mod (to_Z (wl pc)) 4), (Z.div_mod (to_Z (wl pc')) 4) by lia. rewrite E, Hm, Hm'. reflexivity. }
  destruct pc as [h l], pc' as [h' l']. cbn [wh wl] in *. subst h h'. f_equal. apply to_Z_inj. assumption.
Qed.

Lemma ic_get_set (ic : icache) (pc pc' : w64) (d : dinstr) : pc_ok pc = true -> pc_ok pc' = true ->
  ic_get (ic_set ic pc d) pc' = if w_eqb pc pc' then Some d else ic_get ic pc'.
Proof.
  intros H H'. unfold ic_get, ic_set. rewrite iget_iset.
  destruct (Z.eqb_spec (to_Z (ic_key pc) mod 2 ^ Z.of_nat ICD) (to_Z (ic_key pc') mod 2 ^ Z.of_nat ICD)) as [E|E].
  - rewrite (ic_key_inj pc pc' H H' E). replace (w_eqb pc' pc') with true; [reflexivity|]. symmetry. apply w_eqb_true_iff. reflexivity.
  - destruct (w_eqb pc pc') eqn:Ew; [|reflexivity]. apply w_eqb_true_iff in Ew. subst pc'. exfalso. apply E. reflexivity.
Qed.

Lemma hx_fetch_sound (ic ic' : icache) (pc : w64) (d : dinstr) :
  ic_ok ic -> hx_fetch segs ic pc = Some (d, ic') ->
  ic_ok ic' /\ exists w i, fetch_word segs (wbv pc) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4) /\ d = predec i.
Proof.
  intros Hic H. unfold hx_fetch in H. destruct (pc_ok pc) eqn:Epc; [|discriminate].
  destruct (ic_get ic pc) as [d0|] eqn:Eg.
  - injection H as <- <-. split; [exact Hic | exact (Hic pc d0 Epc Eg)].
  - rewrite fetch_fast2_eq in H. destruct (fetch_word segs (wbv pc)) as [w|] eqn:Ef; [|discriminate].
    rewrite is_ecall_fast_eq in H. destruct (is_ecall w) eqn:Ee; [discriminate|].
    rewrite fdecode_eq in H. destruct (decode_any w) as [[i isz]|] eqn:Ed; [|discriminate].
    destruct (Z.eqb_spec isz 4) as [->|]; [|discriminate].
    destruct (is_unsupported (predec i)); [discriminate|].
    assert (E1 : d = predec i) by congruence. assert (E2 : ic' = ic_set ic pc (predec i)) by congruence. clear H. subst d ic'.
    assert (Hthis : exists w0 i0, fetch_word segs (wbv pc) = Some w0 /\ is_ecall w0 = false /\ decode_any w0 = Some (i0, 4) /\ predec i = predec i0)
      by (exists w, i; auto).
    split; [|exists w, i; auto]. intros pc' d' Epc' Eg'. rewrite (ic_get_set ic pc pc' (predec i) Epc Epc') in Eg'.
    destruct (w_eqb pc pc') eqn:Ew.
    + apply w_eqb_true_iff in Ew. subst pc'. injection Eg' as <-. exact Hthis.
    + exact (Hic pc' d' Epc' Eg').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma core_eta (c : core) : Core (c_regs c) (c_fregs c) (c_pc c) (c_fcsr c) (c_resv c) = c.
Proof. destruct c; reflexivity. Qed.

Lemma rset_pc (rd : reg) (v : word) (c : core) : c_pc (Sem.rset rd v c) = c_pc c.
Proof. unfold Sem.rset. destruct (is_x0 rd); destruct c; reflexivity. Qed.
Lemma rset_resv (rd : reg) (v : word) (c : core) : c_resv (Sem.rset rd v c) = c_resv c.
Proof. unfold Sem.rset. destruct (is_x0 rd); destruct c; reflexivity. Qed.
Lemma rset_fregs (rd : reg) (v : word) (c : core) : c_fregs (Sem.rset rd v c) = c_fregs c.
Proof. unfold Sem.rset. destruct (is_x0 rd); destruct c; reflexivity. Qed.
Lemma rset_fcsr (rd : reg) (v : word) (c : core) : c_fcsr (Sem.rset rd v c) = c_fcsr c.
Proof. unfold Sem.rset. destruct (is_x0 rd); destruct c; reflexivity. Qed.

Lemma inval_resv_fields (a : word) (c : core) :
  c_pc (Sem.inval_resv a c) = c_pc c /\ c_regs (Sem.inval_resv a c) = c_regs c
  /\ c_fregs (Sem.inval_resv a c) = c_fregs c /\ c_fcsr (Sem.inval_resv a c) = c_fcsr c.
Proof.
  destruct c as [Rg0 F0 pc0 fc0 [r|]]; unfold Sem.inval_resv; simpl; [destruct (bv_unsigned r =? bv_unsigned a)|]; simpl; auto.
Qed.

Lemma wbv_four : wbv w_four = Z_to_bv 64 4.
Proof. reflexivity. Qed.

Lemma wbv_notone : wbv w_notone = bv_not w1.
Proof. apply bv_eq. reflexivity. Qed.

Lemma den_imm (rho : valuation) (x : word) : den rho (VC (w_of_bv x)) x.
Proof. cbn [den]. symmetry. apply wbv_w_of_bv. Qed.

(* [comment removed for export] *)
Definition regs_step (Rg Rg' : bvmap 5 word) : Prop :=
  Rg' = Rg \/ exists (rd : reg) (v : word), is_x0 rd = false /\ Rg' = bvmap_set rd v Rg.

Lemma regs_step_rset (rd : reg) (v : word) (c : core) : regs_step (c_regs c) (c_regs (Sem.rset rd v c)).
Proof.
  unfold Sem.rset. destruct (is_x0 rd) eqn:E; [left; reflexivity|]. right. exists rd, v. split; [exact E|]. destruct c; reflexivity.
Qed.

(* [comment removed for export] *)
Definition mem_step (rho : valuation) (M : mem) (m m' : word -> option byte) : Prop :=
  m' = m \/ exists t rg off bs, mget M t = Some rg /\ rg_wr rg = true
                                /\ m' = write_to_mem m (wa (rbase rho t rg + to_Z off)) bs
                                /\ to_Z off + Z.of_nat (length bs) <= to_Z (rg_size rg).

(* [comment removed for export] *)
Lemma R_done (rho : valuation) (pc' : w64) (Rg' : regfile hval) (r' : hresv) (M' : mem) (abs : abstab) (nx : int)
    (c' : core) (m' ro : word -> option byte) :
  c_pc c' = wbv pc' -> Rregs rho Rg' c' -> Rresv rho r' (c_resv c') -> Rmem segs rho M' m' ->
  R rho (SS pc' Rg' r' M' abs nx) (MS_of_core c' m' ro).
Proof.
  intros Hpc Hr Hv Hm. unfold R, MS_of_core, MS, core_of. cbn [ms_svc_pending ms_pc_val ms_regs ms_fregs ms_fcsr ms_resv ms_mem s_pc s_regs s_resv s_mem].
  rewrite core_eta. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma veq_sound (rho : valuation) (a b : hval) (d : bool) (x y : word) :
  veq a b = Some d -> den rho a x -> den rho b y -> (bv_unsigned x =? bv_unsigned y) = d.
Proof.
  intros H Ha Hb. destruct a as [wa'|ta oa| |]; destruct b as [wb'|tb ob| |]; cbn [veq] in H; try discriminate; cbn [den] in *; subst x y.
  - injection H as <-. rewrite !wbv_unsigned. symmetry. apply w_eqb_spec.
  - destruct (eqbP ta tb) as [E|E]; [|discriminate]. injection H as <-. apply to_Z_inj in E. subst tb.
    exact (bv_eqb_pword rho ta oa ob).
Qed.

Lemma inval_sound (rho : valuation) (r : hresv) (a : hval) (x : word) (c : core) :
  Rresv rho r (c_resv c) -> den rho a x -> Rresv rho (inval r a) (c_resv (Sem.inval_resv x c)).
Proof.
  intros Hr Ha. unfold Sem.inval_resv. destruct r as [|xv|]; cbn [inval Rresv] in *.
  - rewrite Hr. exact Hr.
  - destruct Hr as (w & Ew & Hw). rewrite Ew. destruct (veq xv a) as [[|]|] eqn:Ev; cbn [Rresv].
    + rewrite (veq_sound rho xv a true w x Ev Hw Ha). destruct c; reflexivity.
    + rewrite (veq_sound rho xv a false w x Ev Hw Ha). exists w. split; [exact Ew | exact Hw].
    + exact I.
  - exact I.
Qed.

Section Exec.
Variables (rho : valuation) (Rg F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) (m ro : word -> option byte).

Notation c0 := (Core Rg F pc fc rv).
Notation sz4 := (Z_to_bv 64 4).

(* [comment removed for export] *)
Definition exec_post (S S' : sstate) (r : machine_result (core * (word -> option byte))) : Prop :=
  exists c' m', r = MachineOk (c', m') /\ R rho S' (MS_of_core c' m' ro) /\ c_fregs c' = F /\ c_fcsr c' = fc
                /\ mem_step rho (s_mem S) m m' /\ regs_step Rg (c_regs c').

Lemma post_reg (S : sstate) (rd : reg) (hv : hval) (v : word) (npc : w64) (npcv : word) :
  R rho S (MS Rg F pc fc rv m ro) -> den rho hv v -> npcv = wbv npc ->
  exec_post S (with_reg_pc S (rix_of_reg rd) hv npc) (MachineOk (Sem.rset rd v (Sem.with_pc npcv c0), m)).
Proof.
  intros (_ & _ & Hr & Hv & Hm) Hd ->. eexists _, _. split; [reflexivity|]. split; [|split; [|split; [|split]]].
  - unfold with_reg_pc. apply R_done.
    + rewrite rset_pc. reflexivity.
    + apply Rregs_set; [|exact Hd]. exact Hr.
    + rewrite rset_resv. exact Hv.
    + exact Hm.
  - rewrite rset_fregs. reflexivity.
  - rewrite rset_fcsr. reflexivity.
  - left. reflexivity.
  - exact (regs_step_rset rd v (Sem.with_pc (wbv npc) c0)).
Qed.

Lemma post_pc (S : sstate) (npc : w64) (npcv : word) :
  R rho S (MS Rg F pc fc rv m ro) -> npcv = wbv npc ->
  exec_post S (with_pc S npc) (MachineOk (Sem.with_pc npcv c0, m)).
Proof.
  intros (_ & _ & Hr & Hv & Hm) ->. eexists _, _. split; [reflexivity|]. split; [|split; [|split; [|split]]]; try reflexivity.
  - unfold with_pc. apply R_done; [reflexivity | exact Hr | exact Hv | exact Hm].
  - left. reflexivity.
  - left. reflexivity.
Qed.

Lemma npc_ok (S : sstate) : R rho S (MS Rg F pc fc rv m ro) -> bv_add pc sz4 = wbv (w_add (s_pc S) w_four).
Proof. intros (_ & Hpc & _). cbn [ms_pc_val MS] in Hpc. rewrite wbv_add, wbv_four, Hpc. reflexivity. Qed.

Lemma pc_off_ok (S : sstate) (x : word) : R rho S (MS Rg F pc fc rv m ro) -> bv_add pc x = wbv (w_add (s_pc S) (w_of_bv x)).
Proof. intros (_ & Hpc & _). cbn [ms_pc_val MS] in Hpc. rewrite wbv_add, wbv_w_of_bv, Hpc. reflexivity. Qed.

Lemma rget_ok (S : sstate) (r : reg) : R rho S (MS Rg F pc fc rv m ro) -> den rho (rget S (rix_of_reg r)) (Sem.rget c0 r).
Proof. intros (_ & _ & Hr & _). exact (Hr r). Qed.

Lemma ctx_ok_R (S : sstate) : R rho S (MS Rg F pc fc rv m ro) -> ctx_ok rho (ctx_of (s_mem S)).
Proof. intros (_ & _ & _ & _ & Hm). exact (ctx_of_ok segs rho (s_mem S) m Hm). Qed.

End Exec.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_low_mod (x : int) (k : Z) (mk : int) : 0 <= k <= 3 -> to_Z mk = 2 ^ k - 1 ->
  (x land mk =? 0)%uint63 = true -> to_Z x mod 2 ^ k = 0.
Proof.
  intros Hk Hm H. destruct (eqbP (x land mk)%uint63 0%uint63) as [E|E]; [|discriminate].
  rewrite land_spec', Hm in E. change (to_Z 0%uint63) with 0 in E. change (2 ^ k - 1) with (Z.pred (2 ^ k)) in E.
  rewrite <- Z.ones_equiv in E. rewrite Z.land_ones in E by lia. exact E.
Qed.

Lemma amo_al_sound (rho : valuation) (ctx : vctx) (wd : awidth) (a : hval) (x : word) :
  ctx_ok rho ctx -> amo_al ctx wd a = true -> den rho a x -> amo_aligned wd x = true.
Proof.
  intros Hc H Ha. unfold amo_aligned. apply Z.eqb_eq.
  set (k := match wd with AW => 2 | AD => 3 end).
  assert (Ek : amo_bytes wd = 2 ^ k) by (destruct wd; reflexivity). rewrite Ek.
  assert (Hk : 0 <= k <= 3) by (destruct wd; cbn; lia).
  assert (Hmk : to_Z (match wd with AW => 3 | AD => 7 end)%uint63 = 2 ^ k - 1) by (destruct wd; reflexivity).
  assert (P : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (D63 : (two63 mod 2 ^ k = 0)) by (destruct wd; reflexivity).
  destruct a as [w|t o| |]; cbn [amo_al den] in *; [| |discriminate|discriminate].
  - subst x. rewrite wbv_unsigned. pose proof (land_low_mod (wl w) k _ Hk Hmk H) as E. rewrite wZ_split.
    rewrite Z.add_mod, Z.mul_mod, D63, Z.mul_0_r, Z.mod_0_l, Z.add_0_l, Z.mod_mod, E by lia. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [Hi Hl]. subst x.
    destruct (inb_spec rho ctx t o Hc Hi) as [_ ->]. pose proof (land_low_mod (wl o) k _ Hk Hmk Hl) as E.
    destruct (ctx t) as [[al sz]|] eqn:Ect; [|discriminate]. apply leb_spec in H3. change (to_Z 3%uint63) with 3 in H3.
    destruct (Hc t al sz Ect) as (Hal & Hmod & _ & _).
    assert (Hr : rho t mod 2 ^ k = 0).
    { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hmod; [|apply Z.pow_nonzero; lia].
      apply (Z.divide_trans _ (2 ^ to_Z al)); [|exact Hmod]. exists (2 ^ (to_Z al - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    rewrite wZ_split. rewrite Z.add_assoc, Z.add_mod, E, Z.add_0_r, Z.mod_mod by lia.
    rewrite Z.add_mod, Z.mul_mod, D63, Z.mul_0_r, Z.mod_0_l, Z.add_0_r, Z.mod_mod, Hr by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Exec2.
Variables (rho : valuation) (Rg F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) (m ro : word -> option byte).

Notation c0 := (Core Rg F pc fc rv).
Notation sz4 := (Z_to_bv 64 4).

Lemma interp_load (sz : msize) (sg : bool) (a : word) (k : word -> eff) (bs : list byte) :
  ov_read_bytes segs m a (msz_nat sz) = Some bs ->
  interp_eff segs (load_val sz sg a k) m = interp_eff segs (k (load_word sz sg bs)) m.
Proof.
  intros H. destruct sz; cbn [load_val interp_eff width_bytes msz_nat] in *; rewrite H; destruct sg; reflexivity.
Qed.

Lemma interp_store (sz : msize) (a v : word) (k : eff) :
  store_ok segs m a (msz_nat sz) = true ->
  interp_eff segs (store_val sz a v k) m = interp_eff segs k (write_to_mem m a (Z_to_le_bytes (msz_nat sz) (bv_unsigned v))).
Proof.
  intros H. destruct sz; cbn [store_val interp_eff width_bytes msz_nat] in *; rewrite H.
  - rewrite store_bytes_1. reflexivity.
  - rewrite store_bytes_2. reflexivity.
  - rewrite store_bytes_4. reflexivity.
  - reflexivity.
Qed.

Theorem hx_exec_sound (S S' : sstate) (i : instr) :
  R rho S (MS Rg F pc fc rv m ro) -> hx_exec segs (predec i) S = SNext S' ->
  match i with Lr _ _ _ _ _ | Sc _ _ _ _ _ _ | Amo _ _ _ _ _ _ _ => False | _ => True end ->
  exec_post rho Rg F fc m ro S S' (interp_eff segs (exec sz4 i c0) m).
Proof.
  intros HR H Hna. pose proof (npc_ok rho Rg F pc fc rv m ro S HR) as Hnpc. pose proof (ctx_ok_R rho Rg F pc fc rv m ro S HR) as Hctx.
  destruct i; cbn [predec hx_exec] in H; try discriminate; try (destruct Hna); cbn [exec interp_eff].
  - (* [comment removed for export] *) injection H as <-. apply post_reg; [exact HR | apply den_imm | exact Hnpc].
  - (* [comment removed for export] *) injection H as <-. apply post_reg; [exact HR | | exact Hnpc].
    cbn [den c_pc]. apply (pc_off_ok rho Rg F pc fc rv m ro S _ HR).
  - (* [comment removed for export] *) injection H as <-. apply post_reg; [exact HR | cbn [den]; exact Hnpc | apply (pc_off_ok rho Rg F pc fc rv m ro S _ HR)].
  - (* [comment removed for export] *)
    pose proof (rget_ok rho Rg F pc fc rv m ro S rs1 HR) as Ha. destruct (rget S (rix_of_reg rs1)) as [a| | |]; try discriminate.
    injection H as <-. cbn [den] in Ha. apply post_reg; [exact HR | cbn [den]; exact Hnpc |].
    rewrite Ha. rewrite wbv_and, wbv_add, wbv_w_of_bv, wbv_notone. reflexivity.
  - (* [comment removed for export] *)
    pose proof (rget_ok rho Rg F pc fc rv m ro S rs1 HR) as Ha. pose proof (rget_ok rho Rg F pc fc rv m ro S rs2 HR) as Hb.
    destruct (v_branch (ctx_of (s_mem S)) c (rget S (rix_of_reg rs1)) (rget S (rix_of_reg rs2))) as [[|]|] eqn:Eb; try discriminate;
      injection H as <-; rewrite (v_branch_ok rho _ c _ _ _ _ _ Hctx Eb Ha Hb).
    + apply post_pc; [exact HR | apply (pc_off_ok rho Rg F pc fc rv m ro S _ HR)].
    + apply post_pc; [exact HR | exact Hnpc].
  - (* [comment removed for export] *)
    pose proof (rget_ok rho Rg F pc fc rv m ro S rs1 HR) as Ha.
    pose proof (v_alu64_ok rho _ ALU_ADD _ _ _ _ Hctx Ha (den_imm rho (sext 64 imm))) as Hadr.
    change (alu64 ALU_ADD (Sem.rget c0 rs1) (sext 64 imm)) with (bv_add (Sem.rget c0 rs1) (sext 64 imm)) in Hadr.
    destruct (hx_load segs (s_mem S) (s_abs S) _ sz signed) as [v|] eqn:El; [|discriminate]. injection H as <-.
    destruct HR as (H0 & H1 & H2 & H3 & Hm).
    destruct (hx_load_sound segs rho (s_mem S) (s_abs S) m _ sz signed v _ Hm Hadr El) as (bs & Ebs & Hv).
    rewrite (interp_load sz signed _ _ bs Ebs). cbn [interp_eff].
    apply post_reg; [exact (conj H0 (conj H1 (conj H2 (conj H3 Hm)))) | exact Hv | exact Hnpc].
  - (* [comment removed for export] *)
    pose proof (rget_ok rho Rg F pc fc rv m ro S rs1 HR) as Ha. pose proof (rget_ok rho Rg F pc fc rv m ro S rs2 HR) as Hb.
    pose proof (v_alu64_ok rho _ ALU_ADD _ _ _ _ Hctx Ha (den_imm rho (sext 64 imm))) as Hadr.
    change (alu64 ALU_ADD (Sem.rget c0 rs1) (sext 64 imm)) with (bv_add (Sem.rget c0 rs1) (sext 64 imm)) in Hadr.
    destruct (hx_store segs (s_mem S) (s_abs S) _ sz (rget S (rix_of_reg rs2))) as [M'|] eqn:Es; [|discriminate]. injection H as <-.
    destruct HR as (H0 & H1 & H2 & H3 & Hm).
    destruct (hx_store_sound segs rho (s_mem S) M' (s_abs S) m _ _ sz _ _ Hm Hadr Hb Es) as (Hok & Hm' & (t & rg & off & Eg & Ewr & Ex & Hin & _)).
    rewrite (interp_store sz _ _ _ Hok). cbn [interp_eff].
    eexists _, _. split; [reflexivity|]. split; [|split; [|split; [|split]]].
    + change (c_pc c0) with pc. unfold with_mem_pc. destruct (inval_resv_fields (bv_add (Sem.rget c0 rs1) (sext 64 imm)) (Sem.with_pc (bv_add pc sz4) c0)) as (I1 & I2 & I3 & I4).
      apply R_done.
      * rewrite I1. exact Hnpc.
      * eapply Rregs_core; [exact I2 | exact H2].
      * apply inval_sound; [exact H3 | exact Hadr].
      * exact Hm'.
    + exact (proj1 (proj2 (proj2 (inval_resv_fields _ _)))).
    + exact (proj2 (proj2 (proj2 (inval_resv_fields _ _)))).
    + right. exists t, rg, off, (Z_to_le_bytes (msz_nat sz) (bv_unsigned (Sem.rget c0 rs2))).
      rewrite length_Z_to_le_bytes. rewrite <- Ex. auto.
    + left. exact (proj1 (proj2 (inval_resv_fields _ _))).
  - (* [comment removed for export] *) injection H as <-. apply post_reg; [exact HR | | exact Hnpc].
    apply (v_alu64_ok rho _ op _ _ _ _ Hctx (rget_ok rho Rg F pc fc rv m ro S rs1 HR) (den_imm rho (sext 64 imm))).
  - (* [comment removed for export] *) injection H as <-. apply post_reg; [exact HR | | exact Hnpc].
    apply (v_alu64_ok rho _ op _ _ _ _ Hctx (rget_ok rho Rg F pc fc rv m ro S rs1 HR) (den_imm rho (zext 64 shamt))).
  - (* [comment removed for export] *) injection H as <-. apply post_reg; [exact HR | | exact Hnpc].
    apply (v_alu64_ok rho _ op _ _ _ _ Hctx (rget_ok rho Rg F pc fc rv m ro S rs1 HR) (rget_ok rho Rg F pc fc rv m ro S rs2 HR)).
  - (* [comment removed for export] *) injection H as <-. apply post_reg; [exact HR | | exact Hnpc].
    pose proof (v_op32_ok rho ALU_ADD _ _ _ _ (rget_ok rho Rg F pc fc rv m ro S rs1 HR) (den_imm rho (sext 64 (sext 32 imm)))) as Hv.
    replace (low32 (sext 64 (sext 32 imm))) with (sext 32 imm : bv 32) in Hv; [exact Hv|].
    apply bv_eq. unfold low32, sext. rewrite bv_extract_unsigned, Z.shiftr_0_r.
    rewrite (bv_sign_extend_unsigned 64), bv_wrap_bv_wrap by lia. rewrite bv_sign_extend_signed by lia.
    rewrite bv_sign_extend_unsigned. reflexivity.
  - (* [comment removed for export] *) injection H as <-. apply post_reg; [exact HR | | exact Hnpc].
    pose proof (v_op32_ok rho op _ _ _ _ (rget_ok rho Rg F pc fc rv m ro S rs1 HR) (den_imm rho (zext 64 (zext 32 shamt)))) as Hv.
    replace (low32 (zext 64 (zext 32 shamt))) with (zext 32 shamt : bv 32) in Hv; [exact Hv|].
    apply bv_eq. unfold low32, zext. rewrite bv_extract_unsigned, Z.shiftr_0_r. rewrite !bv_zero_extend_unsigned by lia.
    symmetry. apply bv_wrap_small. pose proof (bv_unsigned_in_range 5 shamt) as Hs. unfold bv_modulus in *.
    assert (2 ^ Z.of_N 5 <= 2 ^ Z.of_N 32) by (apply Z.pow_le_mono_r; lia). lia.
  - (* [comment removed for export] *) injection H as <-. apply post_reg; [exact HR | | exact Hnpc].
    apply (v_op32_ok rho op _ _ _ _ (rget_ok rho Rg F pc fc rv m ro S rs1 HR) (rget_ok rho Rg F pc fc rv m ro S rs2 HR)).
  - (* [comment removed for export] *) injection H as <-. apply post_pc; [exact HR | exact Hnpc].
  - (* [comment removed for export] *) injection H as <-. apply post_pc; [exact HR | exact Hnpc].
  - (* [comment removed for export] *) injection H as <-. apply post_reg; [exact HR | | exact Hnpc].
    apply (v_muldiv_ok rho op _ _ _ _ (rget_ok rho Rg F pc fc rv m ro S rs1 HR) (rget_ok rho Rg F pc fc rv m ro S rs2 HR)).
  - (* [comment removed for export] *) injection H as <-. apply post_reg; [exact HR | | exact Hnpc].
    apply (v_muldiv32_ok rho op _ _ _ _ (rget_ok rho Rg F pc fc rv m ro S rs1 HR) (rget_ok rho Rg F pc fc rv m ro S rs2 HR)).
Qed.

(* [comment removed for export] *)
Lemma post_all (S : sstate) (rd : reg) (hv : hval) (v : word) (r' : hresv) (rv' : option word) (npc : w64) (npcv : word) :
  R rho S (MS Rg F pc fc rv m ro) -> den rho hv v -> npcv = wbv npc -> Rresv rho r' rv' ->
  exec_post rho Rg F fc m ro S (with_all S (rix_of_reg rd) hv r' (s_mem S) npc)
    (MachineOk (Sem.with_resv rv' (Sem.rset rd v (Sem.with_pc npcv c0)), m)).
Proof.
  intros (_ & _ & Hr & Hv & Hm) Hd -> Hrv. eexists _, _. split; [reflexivity|]. split; [|split; [|split; [|split]]].
  - unfold with_all. apply R_done.
    + unfold Sem.with_resv. cbn [c_pc]. rewrite rset_pc. reflexivity.
    + apply (Rregs_core rho _ (Sem.rset rd v (Sem.with_pc (wbv npc) c0))); [reflexivity|]. apply Rregs_set; [exact Hr | exact Hd].
    + exact Hrv.
    + exact Hm.
  - unfold Sem.with_resv. cbn [c_fregs]. rewrite rset_fregs. reflexivity.
  - unfold Sem.with_resv. cbn [c_fcsr]. rewrite rset_fcsr. reflexivity.
  - left. reflexivity.
  - exact (regs_step_rset rd v (Sem.with_pc (wbv npc) c0)).
Qed.

(* [comment removed for export] *)
Lemma post_all_store (S : sstate) (rd : reg) (hv : hval) (v : word) (r' : hresv) (c1 : core) (M' : mem) (m' : word -> option byte)
    (npc : w64) :
  c_pc c1 = wbv npc -> c_regs c1 = Rg -> c_fregs c1 = F -> c_fcsr c1 = fc ->
  R rho S (MS Rg F pc fc rv m ro) -> den rho hv v -> Rresv rho r' (c_resv c1) -> Rmem segs rho M' m' -> mem_step rho (s_mem S) m m' ->
  exec_post rho Rg F fc m ro S (with_all S (rix_of_reg rd) hv r' M' npc) (MachineOk (Sem.rset rd v c1, m')).
Proof.
  intros E1 E2 E3 E4 (_ & _ & Hr & _ & _) Hd Hrv Hm' Hst. eexists _, _. split; [reflexivity|]. split; [|split; [|split; [|split]]].
  - unfold with_all. apply R_done.
    + rewrite rset_pc. exact E1.
    + apply Rregs_set; [|exact Hd]. apply (Rregs_core rho _ (core_of (MS Rg F pc fc rv m ro))); [exact E2 | exact Hr].
    + rewrite rset_resv. exact Hrv.
    + exact Hm'.
  - rewrite rset_fregs. exact E3.
  - rewrite rset_fcsr. exact E4.
  - exact Hst.
  - rewrite <- E2. exact (regs_step_rset rd v c1).
Qed.

Lemma interp_estore32 (a v : word) (k : eff) : store_ok segs m a 4 = true ->
  interp_eff segs (EStore 32 a (low32 v) k) m = interp_eff segs k (write_to_mem m a (Z_to_le_bytes 4 (bv_unsigned v))).
Proof. intros H. exact (interp_store SZ4 a v k H). Qed.

Lemma interp_estore64 (a v : word) (k : eff) : store_ok segs m a 8 = true ->
  interp_eff segs (EStore 64 a v k) m = interp_eff segs k (write_to_mem m a (Z_to_le_bytes 8 (bv_unsigned v))).
Proof. intros H. exact (interp_store SZ8 a v k H). Qed.

Lemma rget_any_resv (rv1 rv2 : option word) (r : reg) : Sem.rget (Core Rg F pc fc rv1) r = Sem.rget (Core Rg F pc fc rv2) r.
Proof. reflexivity. Qed.

Lemma amo_sz_nat (wd : awidth) : msz_nat (amo_sz wd) = match wd with AW => 4%nat | AD => 8%nat end.
Proof. destruct wd; reflexivity. Qed.

Lemma low32_sext (v : bv 32) : low32 (sext 64 v) = v.
Proof.
  apply bv_eq. unfold low32, sext. rewrite bv_extract_unsigned, Z.shiftr_0_r, bv_sign_extend_unsigned, bv_wrap_bv_wrap by lia.
  unfold bv_signed, bv_swrap, bv_wrap. rewrite Zminus_mod_idemp_l.
  replace (bv_unsigned v + bv_half_modulus 32 - bv_half_modulus 32) with (bv_unsigned v) by ring.
  apply Z.mod_small. apply bv_unsigned_in_range.
Qed.

Theorem hx_exec_sound_atomic (S S' : sstate) (i : instr) :
  R rho S (MS Rg F pc fc rv m ro) -> hx_exec segs (predec i) S = SNext S' ->
  match i with Lr _ _ _ _ _ | Sc _ _ _ _ _ _ | Amo _ _ _ _ _ _ _ => True | _ => False end ->
  exec_post rho Rg F fc m ro S S' (interp_eff segs (exec sz4 i c0) m).
Proof.
  intros HR H Hat. pose proof (npc_ok rho Rg F pc fc rv m ro S HR) as Hnpc. pose proof (ctx_ok_R rho Rg F pc fc rv m ro S HR) as Hctx.
  destruct i; try (destruct Hat); cbn [predec hx_exec] in H.
  - (* [comment removed for export] *)
    pose proof (rget_ok rho Rg F pc fc rv m ro S rs1 HR) as Ha.
    destruct (amo_al (ctx_of (s_mem S)) w (rget S (rix_of_reg rs1))) eqn:Eal; [|discriminate].
    pose proof (amo_al_sound rho _ w _ _ Hctx Eal Ha) as Hal.
    destruct (hx_load segs (s_mem S) (s_abs S) _ (amo_sz w) true) as [v|] eqn:El; [|discriminate]. injection H as <-.
    pose proof HR as (H0 & H1 & H2 & H3 & Hm).
    destruct (hx_load_sound segs rho (s_mem S) (s_abs S) m _ (amo_sz w) true v _ Hm Ha El) as (bs & Ebs & Hv).
    cbn [exec]. rewrite Hal. cbn [negb]. destruct w; cbn [amo_sz msz_nat] in *; cbn [interp_eff width_bytes]; rewrite Ebs; cbn [interp_eff].
    + apply post_all; [exact HR | exact Hv | exact Hnpc | exists (Sem.rget c0 rs1); split; [reflexivity | exact Ha]].
    + apply post_all; [exact HR | exact Hv | exact Hnpc | exists (Sem.rget c0 rs1); split; [reflexivity | exact Ha]].
  - (* [comment removed for export] *)
    pose proof (rget_ok rho Rg F pc fc rv m ro S rs1 HR) as Ha. pose proof (rget_ok rho Rg F pc fc rv m ro S rs2 HR) as Hb.
    destruct (amo_al (ctx_of (s_mem S)) w (rget S (rix_of_reg rs1))) eqn:Eal; [|discriminate].
    pose proof (amo_al_sound rho _ w _ _ Hctx Eal Ha) as Hal.
    pose proof HR as (H0 & H1 & H2 & H3 & Hm). cbn [ms_resv MS] in H3. cbn [exec]. rewrite Hal. cbn [negb c_resv]. change (c_pc c0) with pc.
    assert (Hfail : forall r', exec_post rho Rg F fc m ro S (with_all S (rix_of_reg rd) (VC w_one) RNone (s_mem S) (w_add (s_pc S) w_four))
                                 (MachineOk (Sem.rset rd w1 (Sem.with_resv None (Sem.with_pc (bv_add pc sz4) c0)), m)) -> r' = tt -> True) by auto.
    clear Hfail.
    assert (Hno : exec_post rho Rg F fc m ro S (with_all S (rix_of_reg rd) (VC w_one) RNone (s_mem S) (w_add (s_pc S) w_four))
                    (MachineOk (Sem.rset rd w1 (Sem.with_resv None (Sem.with_pc (bv_add pc sz4) c0)), m))).
    { apply post_all_store; [exact Hnpc | reflexivity | reflexivity | reflexivity | exact HR | reflexivity | reflexivity | exact Hm | left; reflexivity]. }
    destruct (s_resv S) as [|xr|] eqn:Er; cbn [Rresv] in H3.
    + injection H as <-. rewrite H3 in Hno |- *. exact Hno.
    + destruct H3 as (w0 & Ew0 & Hw0). rewrite Ew0 in Hno |- *. rewrite ?(rget_any_resv (Some w0) rv) in Hno. rewrite ?(rget_any_resv (Some w0) rv).
      destruct (veq xr (rget S (rix_of_reg rs1))) as [[|]|] eqn:Ev; [| |discriminate].
      * rewrite (veq_sound rho _ _ true _ _ Ev Hw0 Ha).
        destruct (hx_store segs (s_mem S) (s_abs S) _ (amo_sz w) (rget S (rix_of_reg rs2))) as [M'|] eqn:Es; [|discriminate]. injection H as <-.
        destruct (hx_store_sound segs rho (s_mem S) M' (s_abs S) m _ _ (amo_sz w) _ _ Hm Ha Hb Es) as (Hok & Hm' & (t & rg & off & Eg & Ewr & Ex & Hin & _)).
        assert (Hst : mem_step rho (s_mem S) m (write_to_mem m (Sem.rget c0 rs1) (Z_to_le_bytes (msz_nat (amo_sz w)) (bv_unsigned (Sem.rget c0 rs2))))).
        { right. exists t, rg, off, (Z_to_le_bytes (msz_nat (amo_sz w)) (bv_unsigned (Sem.rget c0 rs2))). rewrite length_Z_to_le_bytes, <- Ex. auto. }
        destruct w; cbn [amo_sz msz_nat] in *.
        -- rewrite (interp_estore32 _ _ _ Hok). cbn [interp_eff].
           apply post_all_store; [exact Hnpc | reflexivity | reflexivity | reflexivity | exact HR | reflexivity | reflexivity | exact Hm' | exact Hst].
        -- rewrite (interp_estore64 _ _ _ Hok). cbn [interp_eff].
           apply post_all_store; [exact Hnpc | reflexivity | reflexivity | reflexivity | exact HR | reflexivity | reflexivity | exact Hm' | exact Hst].
      * rewrite (veq_sound rho _ _ false _ _ Ev Hw0 Ha). injection H as <-. exact Hno.
    + discriminate.
  - (* [comment removed for export] *)
    pose proof (rget_ok rho Rg F pc fc rv m ro S rs1 HR) as Ha. pose proof (rget_ok rho Rg F pc fc rv m ro S rs2 HR) as Hb.
    destruct (amo_al (ctx_of (s_mem S)) w (rget S (rix_of_reg rs1))) eqn:Eal; [|discriminate].
    pose proof (amo_al_sound rho _ w _ _ Hctx Eal Ha) as Hal.
    destruct (hx_load segs (s_mem S) (s_abs S) _ (amo_sz w) true) as [[old| | |]|] eqn:El; try discriminate.
    destruct (rget S (rix_of_reg rs2)) as [src| | |] eqn:Esrc; try discriminate.
    destruct (hx_store segs (s_mem S) (s_abs S) _ (amo_sz w) (VC (amo_new op w old src))) as [M'|] eqn:Es; [|discriminate]. injection H as <-.
    pose proof HR as (H0 & H1 & H2 & H3 & Hm).
    destruct (hx_load_sound segs rho (s_mem S) (s_abs S) m _ (amo_sz w) true _ _ Hm Ha El) as (bs & Ebs & Hold).
    destruct (hx_store_sound segs rho (s_mem S) M' (s_abs S) m _ (VC (amo_new op w old src)) (amo_sz w) _ (wbv (amo_new op w old src)) Hm Ha eq_refl Es)
      as (Hok & Hm' & (t & rg & off & Eg & Ewr & Ex & Hin & _)).
    cbn [den] in Hold, Hb. cbn [exec]. rewrite Hal. cbn [negb]. change (c_pc c0) with pc.
    destruct (inval_resv_fields (Sem.rget c0 rs1) (Sem.with_pc (bv_add pc sz4) c0)) as (I1 & I2 & I3 & I4).
    destruct w; cbn [amo_sz msz_nat amo_new] in *; cbn [interp_eff width_bytes]; rewrite Ebs; cbn [interp_eff width_bytes].
    + (* [comment removed for export] *)
      assert (Eo : low32 (wbv old) = bv_extract 0 32 (le_bytes_to_word bs)).
      { rewrite <- Hold. cbn [load_word]. apply low32_sext. }
      rewrite <- Eo, Hb. rewrite Hok. cbn [interp_eff].
      assert (Eby : Z_to_le_bytes 4 (bv_unsigned (amo_val op (low32 (wbv old)) (low32 (wbv src))))
                    = Z_to_le_bytes 4 (bv_unsigned (wbv (w_of_bv (zext 64 (amo_val op (low32 (wbv old)) (low32 (wbv src)))))))).
      { rewrite wbv_w_of_bv. unfold zext. rewrite bv_zero_extend_unsigned by lia. reflexivity. }
      rewrite Eby.
      replace (sext 64 (low32 (wbv old))) with (wbv old) by (rewrite Eo; symmetry; exact Hold).
      apply post_all_store; [rewrite I1; exact Hnpc | exact I2 | exact I3 | exact I4 | exact HR | reflexivity | apply inval_sound; [exact H3 | exact Ha] | exact Hm' |].
      right. eexists t, rg, off, _. rewrite length_Z_to_le_bytes, <- Ex. auto.
    + (* [comment removed for export] *)
      assert (Eo : wbv old = bv_extract 0 64 (le_bytes_to_word bs)) by (rewrite <- Hold; reflexivity).
      rewrite <- Eo, Hb. rewrite Hok. cbn [interp_eff].
      rewrite wbv_w_of_bv in Hm'. 
      apply post_all_store; [rewrite I1; exact Hnpc | exact I2 | exact I3 | exact I4 | exact HR | reflexivity | apply inval_sound; [exact H3 | exact Ha] | exact Hm' |].
      right. eexists t, rg, off, _. rewrite length_Z_to_le_bytes, <- Ex. auto.
Qed.

End Exec2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_atomic (i : instr) : bool :=
  match i with Lr _ _ _ _ _ | Sc _ _ _ _ _ _ | Amo _ _ _ _ _ _ _ => true | _ => false end.

Theorem hx_step_sound (rho : valuation) (ic ic' : icache) (S S' : sstate) (ms : machine_state) :
  ic_ok ic -> R rho S ms -> hx_step segs ic S = (ic', SNext S') ->
  ic_ok ic' /\ exists ms', mstep segs ms ms' /\ R rho S' ms'
                           /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms /\ ms_rom ms' = ms_rom ms
                           /\ mem_step rho (s_mem S) (ms_mem ms) (ms_mem ms') /\ regs_step (ms_regs ms) (ms_regs ms').
Proof.
  intros Hic HR H. unfold hx_step in H. destruct (hx_fetch segs ic (s_pc S)) as [[d ic1]|] eqn:Ef; [|discriminate].
  injection H as <- H. destruct (hx_fetch_sound ic ic1 (s_pc S) d Hic Ef) as (Hic1 & w & i & Hfw & Hec & Hdec & ->).
  split; [exact Hic1|]. pose proof HR as (Hsvc & Hpc & _).
  rewrite (MS_eta ms Hsvc) in HR |- *. rewrite <- Hpc in Hfw.
  set (Rg := ms_regs ms) in *. set (F := ms_fregs ms) in *. set (pc := ms_pc_val ms) in *. set (fc := ms_fcsr ms) in *.
  set (rv := ms_resv ms) in *. set (m := ms_mem ms) in *. set (ro := ms_rom ms) in *.
  assert (Hpost : exec_post rho Rg F fc m ro S S' (interp_eff segs (exec (Z_to_bv 64 4) i (Core Rg F pc fc rv)) m)).
  { destruct (is_atomic i) eqn:Eat.
    - apply (hx_exec_sound_atomic rho Rg F pc fc rv m ro S S' i HR H). destruct i; try discriminate; exact I.
    - apply (hx_exec_sound rho Rg F pc fc rv m ro S S' i HR H). destruct i; try discriminate; exact I. }
  destruct Hpost as (c' & m' & Eres & HR' & Hf & Hc & Hst & Hrs).
  exists (MS_of_core c' m' ro). split; [|split; [exact HR'|]].
  - split; [reflexivity|]. rewrite (step_gen segs Rg F pc fc rv m ro w i 4 Hfw Hec Hdec). rewrite Eres. reflexivity.
  - unfold MS_of_core, MS. cbn [ms_fregs ms_fcsr ms_rom ms_mem]. auto.
Qed.

End StepSound.
