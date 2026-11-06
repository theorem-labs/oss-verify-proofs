(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanWMemset AsanSMat AsanWMat AsanWMsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition MZ_WORDS : list (Z * Z) :=
  [(0x0, 0x00c5b023); (0x4, 0x00c5b423); (0x8, 0x00c5b823); (0xc, 0x00c5bc23);
   (0x10, 0xfe070713); (0x14, 0x02058593); (0x18, 0xfee6e4e3)]%Z.

Local Ltac dec := wdec.
Lemma DZ_0  : decode_any (Z_to_bv 32 0x00c5b023) = Some (Store SZ8 11 12 0, 4%Z). Proof. dec. Qed.
Lemma DZ_4  : decode_any (Z_to_bv 32 0x00c5b423) = Some (Store SZ8 11 12 8, 4%Z). Proof. dec. Qed.
Lemma DZ_8  : decode_any (Z_to_bv 32 0x00c5b823) = Some (Store SZ8 11 12 16, 4%Z). Proof. dec. Qed.
Lemma DZ_c  : decode_any (Z_to_bv 32 0x00c5bc23) = Some (Store SZ8 11 12 24, 4%Z). Proof. dec. Qed.
Lemma DZ_10 : decode_any (Z_to_bv 32 0xfe070713) = Some (OpImm ALU_ADD 14 14 4064, 4%Z). Proof. dec. Qed.
Lemma DZ_14 : decode_any (Z_to_bv 32 0x02058593) = Some (OpImm ALU_ADD 11 11 32, 4%Z). Proof. dec. Qed.
Lemma DZ_18 : decode_any (Z_to_bv 32 0xfee6e4e3) = Some (Branch BC_LTU 13 14 8168, 4%Z). Proof. dec. Qed.

(* [comment removed for export] *)
Record MZCode (segs : list Segment) (e : Z) : Prop := {
  mzc_W : words_ok segs e MZ_WORDS = true;
  mzc_bnd : (0 <= e /\ e + 0x20 <= 2 ^ 47 /\ e mod 4 = 0)%Z
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record MZR (ms0 ms : machine_state) : Prop := {
  mzr_svc : ms_svc_pending ms = None;
  mzr_rom : ms_rom ms = ms_rom ms0;
  mzr_fregs : ms_fregs ms = ms_fregs ms0;
  mzr_fcsr : ms_fcsr ms = ms_fcsr ms0;
  mzr_resv : ms_resv ms = ms_resv ms0 \/ ms_resv ms = None;
  mzr_regs : forall r, r <> 11 -> r <> 14 -> rg ms r = rg ms0 r
}.

Lemma MZR_refl : forall S, ms_svc_pending S = None -> MZR S S.
Proof.
  intros S H. constructor; [exact H | reflexivity | reflexivity | reflexivity | left; reflexivity | intros; reflexivity].
Qed.

Lemma MZR_setx : forall ms0 S rd v p r m,
  MZR ms0 S -> (rd = 0 \/ rd = 11 \/ rd = 14) -> r = ms_resv S -> m = ms_mem S ->
  MZR ms0 (setx S rd v p r m).
Proof.
  intros ms0 S rd v p r m [H1 H2 H3 H4 H5 H6] Hrd -> ->.
  constructor; [reflexivity | exact H2 | exact H3 | exact H4 | exact H5 |].
  intros r0 R1 R2. rewrite <- (H6 r0 R1 R2).
  destruct Hrd as [ -> |[ -> | -> ]]; [apply rg_setx_x0 | apply rg_setx_other; exact R1 | apply rg_setx_other; exact R2].
Qed.

Lemma MZR_store : forall ms0 S v p (a : word) r m,
  MZR ms0 S -> r = inval a (ms_resv S) -> MZR ms0 (setx S 0 v p r m).
Proof.
  intros ms0 S v p a r m [H1 H2 H3 H4 H5 H6] ->.
  constructor; [reflexivity | exact H2 | exact H3 | exact H4 | | ].
  - rewrite resv_setx. destruct (inval_cases a (ms_resv S)) as [E|E]; rewrite E; [exact H5 | right; reflexivity].
  - intros r0 R1 R2. rewrite rg_setx_x0. exact (H6 r0 R1 R2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mz_n_facts : forall c : Z, (32 <= c < 2 ^ 63)%Z -> (0 <= c - 32 * (c / 32) < 32 /\ 32 <= 32 * (c / 32))%Z.
Proof.
  intros c Hc. pose proof (Z.div_mod c 32 ltac:(lia)). pose proof (Z.mod_pos_bound c 32 ltac:(lia)).
  assert (1 <= c / 32)%Z by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Section MZW.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable e : Z.
Hypothesis HC : MZCode segs e.

Local Ltac inw := repeat (first [left; reflexivity | right]).
Local Ltac fw := apply (words_get segs e MZ_WORDS); [exact (mzc_W _ _ HC) | inw | lia].

Lemma FZ_0  : fetch_word segs (pcw e 0x0)  = Some (Z_to_bv 32 0x00c5b023). Proof. fw. Qed.
Lemma FZ_4  : fetch_word segs (pcw e 0x4)  = Some (Z_to_bv 32 0x00c5b423). Proof. fw. Qed.
Lemma FZ_8  : fetch_word segs (pcw e 0x8)  = Some (Z_to_bv 32 0x00c5b823). Proof. fw. Qed.
Lemma FZ_c  : fetch_word segs (pcw e 0xc)  = Some (Z_to_bv 32 0x00c5bc23). Proof. fw. Qed.
Lemma FZ_10 : fetch_word segs (pcw e 0x10) = Some (Z_to_bv 32 0xfe070713). Proof. fw. Qed.
Lemma FZ_14 : fetch_word segs (pcw e 0x14) = Some (Z_to_bv 32 0x02058593). Proof. fw. Qed.
Lemma FZ_18 : fetch_word segs (pcw e 0x18) = Some (Z_to_bv 32 0xfee6e4e3). Proof. fw. Qed.

Section LoopM.
Variable model0 : Model.
Variable K : TSet.
Variable ms0 : machine_state.
Variables (dst c b : Z).
Hypothesis Hh0 : m_halted model0 = None.
Hypothesis Hb : (0 <= b < 256)%Z.
Hypothesis Hdst : (0 <= dst)%Z.
Hypothesis Hc : (32 <= c < 2 ^ 63)%Z.
Let n : Z := (32 * (c / 32))%Z.
Hypothesis Hdn : (dst + n <= 2 ^ 47)%Z.
Hypothesis Hsok : store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Z.to_nat n) = true.
Let L : list word := range_pages dst (Z.to_nat n).
Hypothesis Hbud : (vm_backing_used model0 + Z.of_nat (length L) * page_size <= vm_limit (m_vmmaps model0))%Z.
Let v : byte := Z_to_bv 8 b.
Hypothesis HK : forall ms' m', MZR ms0 ms' ->
  filled (ms_mem ms') (ms_mem ms0) dst (dst + n) v ->
  ms_pc_val ms' = pcw e 0x1c -> rg ms' 11 = Z_to_bv 64 (dst + n) -> rg ms' 14 = Z_to_bv 64 (c - n) ->
  matin model0 m' L -> realizes_cfg segs cfg (mkCfg ms' m') K.

Lemma n_facts : (0 <= c - n < 32 /\ 32 <= n)%Z.
Proof. exact (mz_n_facts c Hc). Qed.

Lemma mhaltZ : forall m, matin model0 m L -> m_halted m = None.
Proof. intros m Hm. rewrite (matin_halted _ _ _ Hm). exact Hh0. Qed.

Local Ltac mnext := let m' := fresh "mdl" in let H' := fresh "Hmn" in intros m' H';
  repeat match goal with
         | H : matin model0 ?x L |- _ => lazymatch x with m' => fail | _ => clear H end
         | H : m_halted ?x = None |- _ => lazymatch x with m' => fail | model0 => fail | _ => clear H end
         end;
  let Hm := fresh "Hm" in rename H' into Hm; let Hh := fresh "Hhm" in pose proof (mhaltZ m' Hm) as Hh.

Lemma sok_subZ : forall m (a : Z) k, filled m (ms_mem ms0) dst (dst + (a - dst)) v ->
  (dst <= a)%Z -> (a + Z.of_nat k <= dst + n)%Z -> store_ok segs m (Z_to_bv 64 a) k = true.
Proof.
  intros m a k Hf Ha Hk. pose proof n_facts.
  eapply store_ok_sub; [ | eapply store_ok_mono; [exact (filled_grows _ _ _ _ _ Hf) | exact Hsok] | | ];
    rewrite ?bvu_z by lia; rewrite ?Z2Nat.id by lia; lia.
Qed.

Local Ltac mzr_chain HS :=
  repeat first
   [ (eapply MZR_store; [ | reflexivity ])
   | (eapply MZR_setx; [ | first [ left; reflexivity | right; left; reflexivity | right; right; reflexivity ] | reflexivity | reflexivity ]) ];
  exact HS.

Local Ltac inL := apply range_pages_incl; rewrite bvu_z by lia; cbn [msz_n Z.of_nat Pos.of_succ_nat Pos.succ];
                  rewrite ?Z2Nat.id by lia; lia.

(* [comment removed for export] *)
Lemma zloop : forall (d : nat) S (i : Z) m, matin model0 m L ->
  (n - i = 32 * Z.of_nat d)%Z -> (0 <= i < n)%Z ->
  MZR ms0 S -> ms_pc_val S = pcw e 0x0 ->
  rg S 11 = Z_to_bv 64 (dst + i) -> rg S 12 = Z_to_bv 64 (rep 8 b) -> rg S 13 = Z_to_bv 64 31 ->
  rg S 14 = Z_to_bv 64 (c - i) ->
  filled (ms_mem S) (ms_mem ms0) dst (dst + i) v ->
  realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  induction d as [|d IH]; intros S i m Hm Hd Hi HS Hpc H11 H12 H13 H14 Hf; [lia|].
  pose proof (mhaltZ m Hm) as Hhm. pose proof (mzr_svc _ _ HS) as Hsvc. pose proof n_facts as Hnf.
  (* [comment removed for export] *)
  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | exact Hsvc
     | eapply wacc_Store; [ rewrite Hpc; exact FZ_0 | reflexivity | exact DZ_0 | ] | | exact Hbud | ].
  { rewrite H11. mnorm. apply (sok_subZ _ (dst + i) 8); [ replace (dst + (dst + i - dst))%Z with (dst + i)%Z by lia; exact Hf | lia | cbn; lia ]. }
  { rewrite H11. mnorm. inL. } mnext.
  rewrite Hpc. pcn. rewrite H11, H12. mnorm. rewrite store8_rep by lia. fold v.
  assert (Hf1 : filled (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + i)) (repeat v 8)) (ms_mem ms0) dst (dst + (i + 8)) v).
  { replace (dst + (i + 8))%Z with (dst + i + Z.of_nat 8)%Z by lia. apply filled_step; [lia | lia | cbn; lia | exact Hf]. }
  (* [comment removed for export] *)
  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity
     | eapply wacc_Store; [ fetch_tac FZ_4 | reflexivity | exact DZ_4 | ] | | exact Hbud | ].
  { rewrite ?mem_setx. rgn. rewrite H11. mnorm. apply (sok_subZ _ (dst + i + 8) 8); [ replace (dst + (dst + i + 8 - dst))%Z with (dst + (i + 8))%Z by lia; exact Hf1 | lia | cbn; lia ]. }
  { rgn. rewrite H11. mnorm. inL. } mnext.
  pcn. rgn. rewrite H11, H12. mnorm. rewrite store8_rep by lia. fold v.
  assert (Hf2 : filled (write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + i)) (repeat v 8)) (Z_to_bv 64 (dst + i + 8)) (repeat v 8))
                  (ms_mem ms0) dst (dst + (i + 16)) v).
  { replace (dst + (i + 16))%Z with (dst + (i + 8) + Z.of_nat 8)%Z by lia.
    replace (dst + i + 8)%Z with (dst + (i + 8))%Z by lia. apply filled_step; [lia | lia | cbn; lia | exact Hf1]. }
  (* [comment removed for export] *)
  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity
     | eapply wacc_Store; [ fetch_tac FZ_8 | reflexivity | exact DZ_8 | ] | | exact Hbud | ].
  { rewrite ?mem_setx. rgn. rewrite H11. mnorm. apply (sok_subZ _ (dst + i + 16) 8); [ replace (dst + (dst + i + 16 - dst))%Z with (dst + (i + 16))%Z by lia; exact Hf2 | lia | cbn; lia ]. }
  { rgn. rewrite H11. mnorm. inL. } mnext.
  pcn. rgn. rewrite H11, H12. mnorm. rewrite store8_rep by lia. fold v.
  assert (Hf3 : filled (write_to_mem (write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + i)) (repeat v 8)) (Z_to_bv 64 (dst + i + 8)) (repeat v 8))
                          (Z_to_bv 64 (dst + i + 16)) (repeat v 8))
                  (ms_mem ms0) dst (dst + (i + 24)) v).
  { replace (dst + (i + 24))%Z with (dst + (i + 16) + Z.of_nat 8)%Z by lia.
    replace (dst + i + 16)%Z with (dst + (i + 16))%Z by lia. apply filled_step; [lia | lia | cbn; lia | exact Hf2]. }
  (* [comment removed for export] *)
  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity
     | eapply wacc_Store; [ fetch_tac FZ_c | reflexivity | exact DZ_c | ] | | exact Hbud | ].
  { rewrite ?mem_setx. rgn. rewrite H11. mnorm. apply (sok_subZ _ (dst + i + 24) 8); [ replace (dst + (dst + i + 24 - dst))%Z with (dst + (i + 24))%Z by lia; exact Hf3 | lia | cbn; lia ]. }
  { rgn. rewrite H11. mnorm. inL. } mnext.
  pcn. rgn. rewrite H11, H12. mnorm. rewrite store8_rep by lia. fold v.
  assert (Hf4 : filled (write_to_mem (write_to_mem (write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + i)) (repeat v 8))
                          (Z_to_bv 64 (dst + i + 8)) (repeat v 8)) (Z_to_bv 64 (dst + i + 16)) (repeat v 8)) (Z_to_bv 64 (dst + i + 24)) (repeat v 8))
                  (ms_mem ms0) dst (dst + (i + 32)) v).
  { replace (dst + (i + 32))%Z with (dst + (i + 24) + Z.of_nat 8)%Z by lia.
    replace (dst + i + 24)%Z with (dst + (i + 24))%Z by lia. apply filled_step; [lia | lia | cbn; lia | exact Hf3]. }
  (* [comment removed for export] *)
  wst wacc_OpImm FZ_10 DZ_10. mnorm. rewrite H14. mnorm.
  (* [comment removed for export] *)
  wst wacc_OpImm FZ_14 DZ_14. mnorm. rewrite H11. mnorm.
  (* [comment removed for export] *)
  eapply rzc_acc; [ exact Hhm | reflexivity | eapply wacc_Branch; [ fetch_tac FZ_18 | reflexivity | exact DZ_18 ] | apply acc_ok_nil | ].
  mnorm. rewrite H13. rewrite branch_ltu_z by lia. pcn.
  destruct (Z.ltb_spec 31 (c - i + -32)) as [Lt|Ge]; pcn.
  - apply (IH _ (i + 32)%Z _ Hm); [lia | lia | mzr_chain HS | reflexivity | | | | | ].
    + rgn. f_equal. lia.
    + rgn. exact H12.
    + rgn. exact H13.
    + rgn. f_equal. lia.
    + rewrite ?mem_setx. exact Hf4.
  - assert (Ein : (i + 32 = n)%Z) by lia.
    apply HK.
    + mzr_chain HS.
    + rewrite ?mem_setx. rewrite <- Ein. exact Hf4.
    + reflexivity.
    + rgn. f_equal. lia.
    + rgn. f_equal. lia.
    + exact Hm.
Qed.

End LoopM.
End MZW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem mzero_loop_sum_mat : forall (segs : list Segment) (cfg : SpuriousCfg) (e : Z), MZCode segs e ->
  forall (ms : machine_state) (model : Model) (K : TSet) (dst c b : Z),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw e 0 -> m_halted model = None ->
  rg ms 11 = Z_to_bv 64 dst -> rg ms 12 = Z_to_bv 64 (rep 8 b) -> rg ms 13 = Z_to_bv 64 31 -> rg ms 14 = Z_to_bv 64 c ->
  (0 <= b < 256)%Z -> (0 <= dst)%Z -> (32 <= c < 2 ^ 63)%Z -> (dst + 32 * (c / 32) <= 2 ^ 47)%Z ->
  store_ok segs (ms_mem ms) (Z_to_bv 64 dst) (Z.to_nat (32 * (c / 32))) = true ->
  (vm_backing_used model + ms_pages (32 * (c / 32)) * page_size <= vm_limit (m_vmmaps model))%Z ->
  (forall ms' model', MZR ms ms' ->
     filled (ms_mem ms') (ms_mem ms) dst (dst + 32 * (c / 32)) (Z_to_bv 8 b) ->
     ms_pc_val ms' = pcw e 0x1c ->
     rg ms' 11 = Z_to_bv 64 (dst + 32 * (c / 32)) -> rg ms' 14 = Z_to_bv 64 (c - 32 * (c / 32)) ->
     mat_of model model' (ms_pages (32 * (c / 32))) -> realizes_cfg segs cfg (mkCfg ms' model') K) ->
  realizes_cfg segs cfg (mkCfg ms model) K.
Proof.
  intros segs cfg e HC ms model K dst c b Hsvc Hpc Hh H11 H12 H13 H14 Hb Hdst Hc Hdn Hsok Hbud HK.
  set (n := (32 * (c / 32))%Z) in *.
  assert (Hn : (0 <= n)%Z) by (unfold n; pose proof (Z.div_pos c 32 ltac:(lia) ltac:(lia)); lia).
  pose proof (ms_pages_L dst n Hdst Hn Hdn) as HL.
  assert (Hbud' : (vm_backing_used model + Z.of_nat (length (range_pages dst (Z.to_nat n))) * page_size
                     <= vm_limit (m_vmmaps model))%Z) by (unfold page_size in *; lia).
  assert (Hnf : (32 <= n)%Z) by exact (proj2 (mz_n_facts c Hc)).
  refine (zloop segs cfg e HC model K ms dst c b Hh Hb Hdst Hc Hdn Hsok Hbud' _ (Z.to_nat (c / 32)) ms 0%Z model
            (matin_refl model _) _ _ (MZR_refl ms Hsvc) Hpc _ H12 H13 _ _).
  - intros ms' m' HS Hf Hp G11 G14 Hm. apply HK; [exact HS | exact Hf | exact Hp | exact G11 | exact G14 |].
    eapply mat_of_mono; [exact (matin_mat_of _ _ _ Hm) | exact HL].
  - rewrite Z2Nat.id by (apply Z.div_pos; lia). fold n. lia.
  - fold n. lia.
  - rewrite Z.add_0_r. exact H11.
  - rewrite Z.sub_0_r. exact H14.
  - rewrite Z.add_0_r. apply filled_refl.
Qed.
