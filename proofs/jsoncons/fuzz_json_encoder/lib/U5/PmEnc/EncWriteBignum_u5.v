(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncBridges_u5 EncAppendK_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_write_bignum_xsrc_T_u5 Cut_write_bignum_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EWB.
Import PMES.
Module G := Cut_write_bignum_xsrc_u5.
Module GT := Cut_write_bignum_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.
Definition RETPC : Z := Eval vm_compute in hd 0 GT.ENDS.
Definition S2E : expr := EVar 32.
Definition F0 : list SGP.region := [(EVar 2, -8672, ELit 8672); (EVar 10, 296, ELit 8)].

Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition sink_j (f : CC.cutpoint -> SR.post_spec -> CC.cutpoint -> CA.blocks -> CA.blocks -> option CH2.cinfo) (i k j : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (match CH2.ret_of G.RETS i k with Some j' => Nat.eqb j' j | None => false end &&
   match nth_error G.CPS j with Some cj => isSome (f c ps cj (nth i G.BLS []) (nth j G.BLS [])) | None => false end)%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  (SP.F_sub (CC.cp_F c) F0 && Nat.leb GT.NF (CC.cp_nx c)) &&
  match t with
  | CC.TGoto j s => false
  | CC.TOther pc =>
      if Z.eqb pc PML.PC_STR_APPEND then
        (Nat.eqb i 0 && Z.eqb (SR.ps_pc ps) PML.PC_STR_APPEND && sink_j (EB.sink_chk GT.NF G.HDECL S2E 0) i k 1 c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (EVar 33) && expr_eqb (nth 12 regs (ELit 0)) (EVar 34))%bool
      else (Nat.eqb i 1 && PB.exit_base_chk GT.NF RETPC c ps)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.

Section WriteBignumOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis APPEND_OK : str_append_x_spec L HI.

(* [comment removed for export] *)
Section Stretch.
Variables (E0 : env) (sp V S2 : Z).
Hypothesis U2 : bv_unsigned (ev E0 2) = sp.
Hypothesis U10 : bv_unsigned (ev E0 10) = V.
Hypothesis SPR : hl_ceil L + 8672 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis OBJS : objs_enc L sp V S2.

Lemma out_F0 : forall (F : list SGP.region) E' a, SP.F_sub F F0 = true -> env_agree GT.NF E0 E' -> 0 <= a < 2 ^ 64 ->
  ~ (sp - 8672 <= a < sp) -> ~ (V + 296 <= a < V + 304) -> SGP.outside E' F (Z_to_bv 64 a).
Proof.
  intros F E' a HF Hag Ha N1 N2. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  pose proof (SP.F_sub_in _ _ _ HF Hin) as Hin0. rewrite L5.unsigned_lit by lia.
  destruct OBJS as ((A1 & A2 & A3) & _). unfold ENC_SIZE in *. destruct SPR as (P1 & P2 & P3).
  unfold F0 in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|[X|[]]]; injection X as <- <- <-.
  - rewrite (PB.estart_agree GT.NF E0 E' (EVar 2) (-8672) Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U2. rewrite (u64_of_Z 8672) by lia. lia.
  - rewrite (PB.estart_agree GT.NF E0 E' (EVar 10) 296 Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U10. rewrite (u64_of_Z 8) by lia. lia.
Qed.

Lemma inv_stretch : forall (F : list SGP.region) E' (M M' : mem) g, SP.F_sub F F0 = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) -> mem_grows M M' ->
  (forall b, In b (g_lbv g) -> block_range L (fst b) (snd b)) ->
  enc_inv M V S2 g -> enc_inv M' V S2 g.
Proof.
  intros F E' M M' g HF Hag HFR HG HB HI0.
  destruct OBJS as ((A1 & A2 & A3) & (B1 & B2 & B3) & C). unfold ENC_SIZE, PML.apart in *. destruct SPR as (P1 & P2 & P3).
  assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - 8672 \/ sp <= a) -> (a + n <= V + 296 \/ V + 304 <= a) -> L5C.agree_on M M' a n).
  { intros a n H0 H1 H2 H3 i Hi. apply HFR. apply (out_F0 F E' i HF Hag); lia. }
  apply (EK.enc_inv_agree M M' V S2 g); try (unfold ENC_SIZE; lia).
  - apply AG; unfold O_COLUMN; lia.
  - apply AG; unfold O_COLON, ENC_SIZE; lia.
  - destruct HI0 as (I1 & _). destruct I1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _).
    intros i Hi. apply HG. apply X. exact Hi.
  - apply AG; lia.
  - intros b Hb. destruct (HB b Hb) as (R0 & R1 & R2 & R3 & R4). split; [lia|]. split; [lia|]. apply AG; lia.
  - exact HI0.
Qed.

(* [comment removed for export] *)
Lemma blk_stretch : forall (F : list SGP.region) E' (M M' : mem) bb bm a n, SP.F_sub F F0 = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) -> block_range L bb bm -> bb <= a -> a + n <= bb + bm -> L5C.agree_on M M' a n.
Proof.
  intros F E' M M' bb bm a n HF Hag HFR (R0 & R1 & R2 & R3 & R4) Ha Hn i Hi.
  destruct OBJS as ((A1 & A2 & A3) & _). unfold ENC_SIZE in *. destruct SPR as (P1 & P2 & P3).
  apply HFR. apply (out_F0 F E' i HF Hag); lia.
Qed.
End Stretch.

(* [comment removed for export] *)
Lemma other_block : forall (LBo GB : list (Z * Z)) cr (M : mem) VM rep (b : Z * Z),
  hi_heap HI (LBo ++ GB) cr M VM -> In b LBo -> incl (PML.srep_blocks rep) GB ->
  ~ In b (PML.srep_blocks rep) /\ block_range L (fst b) (snd b) /\
  match rep with PML.SShort _ => True | PML.SLong cap p _ => block_range L p cap /\ (fst b + snd b <= p \/ p + cap <= fst b) end.
Proof.
  intros LBo GB cr M VM rep b HH Hb Hinc. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  assert (HbL : In b (LBo ++ GB)) by (apply in_or_app; left; exact Hb).
  destruct (Hwf b HbL) as (BR & _ & BA).
  destruct rep as [s|cap p s]; cbn [PML.srep_blocks] in *; [split; [intros []|split; [exact BR | exact I]]|].
  assert (HpG : In (p, cap) GB) by (apply Hinc; left; reflexivity).
  assert (Hne : fst b <> p).
  { intros E. rewrite map_app in Hnd. apply (EK.nodup_app_l' _ _ p Hnd); [apply (in_map fst _ _ HpG) | rewrite <- E; apply (in_map fst _ _ Hb)]. }
  split; [intros [X|[]]; apply Hne; rewrite <- X; reflexivity|]. split; [exact BR|].
  assert (HpL : In (p, cap) (LBo ++ GB)) by (apply in_or_app; right; exact HpG).
  split; [exact (proj1 (Hwf _ HpL))|].
  specialize (BA (p, cap) (L5C.in_lb_remove_neq (fst b) p cap _ HpL ltac:(intros X; apply Hne; symmetry; exact X))). cbn [fst snd] in BA. lia.
Qed.

End WriteBignumOk.
End EWB.
