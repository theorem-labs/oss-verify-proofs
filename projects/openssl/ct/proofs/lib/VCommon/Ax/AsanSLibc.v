(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec StepTac MuslStrlen StoreOk CatSim ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSBase AsanSWord.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ENVP_WORDS : list (Z * Z) := [(0, 0x0004b503); (4, 0x00848493); (8, 0xfe051ce3)]%Z.

Lemma D_e0 : decode_any (Z_to_bv 32 0x0004b503) = Some (Load SZ8 true 10 9 0, 4%Z). Proof. wdec. Qed.
Lemma D_e4 : decode_any (Z_to_bv 32 0x00848493) = Some (OpImm ALU_ADD 9 9 8, 4%Z). Proof. wdec. Qed.
Lemma D_e8 : decode_any (Z_to_bv 32 0xfe051ce3) = Some (Branch BC_NE 10 0 8184, 4%Z). Proof. wdec. Qed.

Lemma br_ne_ld8 : forall l : list byte, length l = 8%nat ->
  branch_taken BC_NE (load_word SZ8 true l) w0 = negb (bytes_le_to_Z l =? 0)%Z.
Proof.
  intros l Hl. cbn [branch_taken]. unfold bv_eqb, w0. rewrite u_ld8 by exact Hl. rewrite bvu_z by lia. reflexivity.
Qed.

Lemma ld8_zero : forall l : list byte, length l = 8%nat -> bytes_le_to_Z l = 0%Z -> load_word SZ8 true l = w0.
Proof. intros l Hl H. apply bv_eq. rewrite u_ld8 by exact Hl. rewrite H. reflexivity. Qed.

Lemma rdn_length : forall segs mem n (a : word) l, rdn segs mem a n = Some l -> length l = n.
Proof.
  intros segs mem n. induction n as [|n IH]; intros a l H; cbn [rdn] in H.
  - injection H as <-. reflexivity.
  - destruct (match mem a with Some b => Some b | None => seg_rom segs a end); [|discriminate].
    destruct (rdn segs mem (a + 1) n) as [rest|] eqn:E; [|discriminate].
    injection H as <-. cbn [length]. rewrite (IH _ _ E). reflexivity.
Qed.

Section Envp.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable b : Z.
Hypothesis HW : words_ok segs b ENVP_WORDS = true.

Local Ltac inw := repeat (first [left; reflexivity | right]).
Local Ltac fw := apply (words_get segs b ENVP_WORDS); [exact HW | inw | lia].
Lemma F_e0 : fetch_word segs (pcw b 0) = Some (Z_to_bv 32 0x0004b503). Proof. fw. Qed.
Lemma F_e4 : fetch_word segs (pcw b 4) = Some (Z_to_bv 32 0x00848493). Proof. fw. Qed.
Lemma F_e8 : fetch_word segs (pcw b 8) = Some (Z_to_bv 32 0xfe051ce3). Proof. fw. Qed.

Section Loop.
Variable model : Model.
Hypothesis Hh : m_halted model = None.
Variable ms0 : machine_state.
Variable T : TSet.
Variable p : word.
Variable k : nat.
Hypothesis Hw : forall j, (j <= k)%nat -> exists l, rdn segs (ms_mem ms0) (p + Z_to_bv 64 (8 * Z.of_nat j)) 8 = Some l
                                              /\ (bytes_le_to_Z l =? 0)%Z = (j =? k)%nat.
Hypothesis Hnw : (bv_unsigned p + 8 * Z.of_nat (S k) <= 2 ^ 64)%Z.
Hypothesis Hnl : no_lazy model (bv_unsigned p) (bv_unsigned p + 8 * Z.of_nat (S k)).
Hypothesis HK : forall ms', FR [9; 10] ms0 ms' -> ms_pc_val ms' = pcw b 12 ->
  rg ms' 9 = p + Z_to_bv 64 (8 * Z.of_nat (S k)) -> rg ms' 10 = w0 -> realizes_cfg segs cfg (mkCfg ms' model) T.

Lemma acc8 : forall j, (j <= k)%nat -> acc_ok model [(p + Z_to_bv 64 (8 * Z.of_nat j), 8%nat)].
Proof.
  intros j Hj. apply acc_ok_one.
  - rewrite u_add_small by lia. lia.
  - rewrite u_add_small by lia. apply (no_lazy_sub model _ _ _ _ Hnl); lia.
Qed.

Lemma envp_loop : forall d j ms, (j + d = k)%nat ->
  ms_pc_val ms = pcw b 0 -> FR [9; 10] ms0 ms -> rg ms 9 = p + Z_to_bv 64 (8 * Z.of_nat j) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  induction d as [|d IH]; intros j ms Hjd Hpc HF H9;
    pose proof HF as (Hsvc & _ & _ & _ & _ & Hmem & _);
    destruct (Hw j ltac:(lia)) as (l & Hl & Hz); pose proof (rdn_length _ _ _ _ _ Hl) as Hlen.
  all: eapply rzc_acc; [ assumption | assumption
       | eapply wacc_Load; [ fetch_tac F_e0 | reflexivity | exact D_e0 | rewrite H9, add_sext0, Hmem; exact Hl ]
       | rewrite H9, add_sext0; apply acc8; lia
       | rewrite Hpc; pcn; nrm ].
  all: wsx wacc_OpImm F_e4 D_e4. all: rgn. all: rewrite H9, alu_add, w_add_sext_z. all: lits.
  all: wsx wacc_Branch F_e8 D_e8. all: rgn. all: rewrite br_ne_ld8 by exact Hlen.
  - assert (Hj : j = k) by lia. subst j. rewrite Nat.eqb_refl in Hz. rewrite Hz. cbn [negb]. pcn.
    apply HK; [ frs HF | reflexivity | rgn; apply (f_equal (fun z => p + Z_to_bv 64 z)); lia | rgn; apply ld8_zero; [exact Hlen | apply Z.eqb_eq; exact Hz] ].
  - rewrite (proj2 (Nat.eqb_neq j k) ltac:(lia)) in Hz. rewrite Hz. cbn [negb]. pcn.
    apply (IH (S j)); [ lia | reflexivity | frs HF | rgn; apply (f_equal (fun z => p + Z_to_bv 64 z)); lia ].
Qed.
End Loop.

(* [comment removed for export] *)
Theorem envp_sum : forall (ms : machine_state) (model : Model) (T : TSet) (p : word) (k : nat),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw b 0 -> m_halted model = None ->
  rg ms 9 = p ->
  (forall j, (j <= k)%nat -> exists l, rdn segs (ms_mem ms) (p + Z_to_bv 64 (8 * Z.of_nat j)) 8 = Some l
                                   /\ (bytes_le_to_Z l =? 0)%Z = (j =? k)%nat) ->
  (bv_unsigned p + 8 * Z.of_nat (S k) <= 2 ^ 64)%Z ->
  no_lazy model (bv_unsigned p) (bv_unsigned p + 8 * Z.of_nat (S k)) ->
  (forall ms', FR [9; 10] ms ms' -> ms_pc_val ms' = pcw b 12 ->
     rg ms' 9 = p + Z_to_bv 64 (8 * Z.of_nat (S k)) -> rg ms' 10 = w0 -> realizes_cfg segs cfg (mkCfg ms' model) T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model T p k Hsvc Hpc Hh H9 Hw Hnw Hnl HK.
  apply (envp_loop model Hh ms T p k Hw Hnw Hnl HK k 0 ms); [ lia | exact Hpc | apply FR_refl; exact Hsvc | ].
  rewrite H9. rewrite Z.mul_0_r, w_add_0. reflexivity.
Qed.
End Envp.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PROG_WORDS : list (Z * Z) :=
  [(0, 0x00b53023); (4, 0x00158593); (8, 0xfff5c683); (12, 0xfec68ae3); (16, 0xfe069ae3)]%Z.

Lemma D_p0  : decode_any (Z_to_bv 32 0x00b53023) = Some (Store SZ8 10 11 0, 4%Z). Proof. wdec. Qed.
Lemma D_p4  : decode_any (Z_to_bv 32 0x00158593) = Some (OpImm ALU_ADD 11 11 1, 4%Z). Proof. wdec. Qed.
Lemma D_p8  : decode_any (Z_to_bv 32 0xfff5c683) = Some (Load SZ1 false 13 11 4095, 4%Z). Proof. wdec. Qed.
Lemma D_p12 : decode_any (Z_to_bv 32 0xfec68ae3) = Some (Branch BC_EQ 13 12 8180, 4%Z). Proof. wdec. Qed.
Lemma D_p16 : decode_any (Z_to_bv 32 0xfe069ae3) = Some (Branch BC_NE 13 0 8180, 4%Z). Proof. wdec. Qed.

(* [comment removed for export] *)
Definition PF (S S' : machine_state) : Prop :=
  ms_svc_pending S' = None /\ ms_rom S' = ms_rom S /\ ms_fregs S' = ms_fregs S /\ ms_fcsr S' = ms_fcsr S /\
  (ms_resv S' = ms_resv S \/ ms_resv S' = None) /\ (forall r, ~ In r [11; 13] -> rg S' r = rg S r).

Lemma PF_refl : forall S, ms_svc_pending S = None -> PF S S.
Proof. intros S H. unfold PF. repeat split; try reflexivity; [exact H | left; reflexivity]. Qed.

Lemma PF_setxn : forall S S1 rd v p r m,
  PF S S1 -> (rd = 0 \/ In rd [11; 13]) -> (r = ms_resv S1 \/ exists a, r = inval a (ms_resv S1)) ->
  PF S (setx S1 rd v p r m).
Proof.
  intros S S1 rd v p r m (H1 & H2 & H3 & H4 & H5 & H6) Hrd Hr.
  split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split.
  - rewrite resv_setx. destruct Hr as [->|(a & ->)]; [exact H5|].
    destruct (inval_cases a (ms_resv S1)) as [E|E]; rewrite E; [exact H5 | right; reflexivity].
  - intros r0 Hr0. rewrite <- (H6 r0 Hr0).
    destruct Hrd as [->|Hin]; [apply rg_setx_x0|].
    apply rg_setx_other. intros ->. exact (Hr0 Hin).
Qed.

Ltac pfs HF :=
  repeat first [ exact HF
               | apply PF_setxn; [ | first [ left; reflexivity | right; memb ]
                                   | first [ left; reflexivity | right; eexists; reflexivity ] ] ].

(* [comment removed for export] *)
Definition prog_mem (mem : word -> option byte) (cell pn : word) (k : nat) : word -> option byte :=
  if (k =? 0)%nat then mem else write_to_mem mem cell (store_bytes SZ8 (pn + Z_to_bv 64 (Z.of_nat k))).

Lemma store_ok_ext : forall segs n m m' (a : word), (forall x, m x = m' x) ->
  store_ok segs m a n = store_ok segs m' a n.
Proof.
  intros segs n. induction n as [|n IH]; intros m m' a H; [reflexivity|].
  cbn [store_ok]. unfold wview. rewrite H.
  destruct (m' a); [apply IH; exact H|].
  destruct (find_segment _ _ _) as [seg|]; [|reflexivity].
  destruct (seg_writable seg); [|reflexivity].
  destruct (segment_byte_at _ _); [apply IH; exact H | reflexivity].
Qed.

Lemma bv_eqb_eq_w : forall (a x : word), bv_eqb x a = true -> x = a.
Proof. intros a x H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma w2m_outside : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  write_to_mem m a bs x = m x.
Proof.
  induction bs as [|c bs IH]; intros m a x Hnw Hx; [reflexivity|].
  cbn [write_to_mem length] in *. pose proof (u64_range a).
  destruct bs as [|c' bs'].
  - cbn [write_to_mem]. destruct (bv_eqb x a) eqn:E; [|reflexivity].
    apply bv_eqb_eq_w in E. subst. cbn [length] in Hx. lia.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; cbn [length] in Hnw; lia).
    rewrite IH; [|cbn [length] in *; lia|cbn [length] in *; lia].
    destruct (bv_eqb x a) eqn:E; [|reflexivity].
    apply bv_eqb_eq_w in E. subst. lia.
Qed.

Lemma w2m_inside_indep : forall bs m1 m2 (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs))%Z ->
  write_to_mem m1 a bs x = write_to_mem m2 a bs x.
Proof.
  induction bs as [|c bs IH]; intros m1 m2 a x Hnw Hx; [cbn [length] in Hx; lia|].
  cbn [write_to_mem length] in *. pose proof (u64_range a).
  destruct bs as [|c' bs'].
  - cbn [write_to_mem]. destruct (bv_eqb x a) eqn:E; [reflexivity|].
    exfalso. cbn [length] in Hx. assert (x = a) by (apply bv_eq; lia). subst x.
    unfold bv_eqb in E. rewrite Z.eqb_refl in E. discriminate E.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; cbn [length] in Hnw; lia).
    destruct (bv_eq_dec 64 x a) as [->|NE].
    + rewrite !(w2m_outside (c' :: bs')) by (cbn [length] in *; lia).
      unfold bv_eqb. rewrite Z.eqb_refl. reflexivity.
    + assert (bv_unsigned x <> bv_unsigned a) by (intros E; apply NE; apply bv_eq; exact E).
      apply IH; cbn [length] in *; lia.
Qed.

Lemma store_bytes8_len : forall v, length (store_bytes SZ8 v) = 8%nat.
Proof. reflexivity. Qed.

Lemma after_last_slash_app : forall l l' i acc,
  after_last_slash (l ++ l') i acc = after_last_slash l' (i + length l)%nat (after_last_slash l i acc).
Proof.
  induction l as [|c l IH]; intros l' i acc; cbn [after_last_slash app length].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH. f_equal. lia.
Qed.

Lemma als_firstn_S : forall (a0 : list byte) i, (i < length a0)%nat ->
  after_last_slash (firstn (S i) a0) 0 0
  = if (bv_unsigned (nth i a0 (Z_to_bv 8 0)) =? 47)%Z then S i else after_last_slash (firstn i a0) 0 0.
Proof.
  intros a0 i Hi.
  rewrite <- (firstn_skipn i (firstn (S i) a0)).
  rewrite firstn_firstn, Nat.min_l by lia.
  rewrite skipn_firstn_comm. replace (S i - i)%nat with 1%nat by lia.
  rewrite after_last_slash_app, firstn_length_le by lia.
  destruct (skipn i a0) as [|c r] eqn:Es.
  - exfalso. pose proof (f_equal (@length byte) Es) as HL. rewrite length_skipn in HL. cbn in HL. lia.
  - change (firstn 1 (c :: r)) with [c]. cbn [after_last_slash]. rewrite Nat.add_0_l.
    replace (nth i a0 (Z_to_bv 8 0)) with c.
    2:{ rewrite <- (firstn_skipn i a0), app_nth2 by (rewrite firstn_length_le; lia).
        rewrite firstn_length_le, Nat.sub_diag, Es by lia. reflexivity. }
    destruct (bv_unsigned c =? 47)%Z; reflexivity.
Qed.

Lemma branch_eq_47 : forall x : byte,
  branch_taken BC_EQ (Z_to_bv 64 (bv_unsigned x)) (Z_to_bv 64 47) = (bv_unsigned x =? 47)%Z.
Proof. intros x. pose proof (byte_range x). apply branch_eq_z; lia. Qed.

Section Prog.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable b : Z.
Hypothesis HW : words_ok segs b PROG_WORDS = true.

Local Ltac inw := repeat (first [left; reflexivity | right]).
Local Ltac fw := apply (words_get segs b PROG_WORDS); [exact HW | inw | lia].
Lemma F_p0  : fetch_word segs (pcw b 0)  = Some (Z_to_bv 32 0x00b53023). Proof. fw. Qed.
Lemma F_p4  : fetch_word segs (pcw b 4)  = Some (Z_to_bv 32 0x00158593). Proof. fw. Qed.
Lemma F_p8  : fetch_word segs (pcw b 8)  = Some (Z_to_bv 32 0xfff5c683). Proof. fw. Qed.
Lemma F_p12 : fetch_word segs (pcw b 12) = Some (Z_to_bv 32 0xfec68ae3). Proof. fw. Qed.
Lemma F_p16 : fetch_word segs (pcw b 16) = Some (Z_to_bv 32 0xfe069ae3). Proof. fw. Qed.

Section Loop.
Variable model : Model.
Hypothesis Hh : m_halted model = None.
Variable ms0 : machine_state.
Variable T : TSet.
Variables (pn cell : word) (bs : list byte).
Local Notation L := (Z.of_nat (length bs)).
Hypothesis Hstr : cstr segs (ms_mem ms0) pn bs.
Hypothesis Hnw : (bv_unsigned pn + L + 1 <= 2 ^ 64)%Z.
Hypothesis Hnl : no_lazy model (bv_unsigned pn) (bv_unsigned pn + L + 1).
Hypothesis Hok : store_ok segs (ms_mem ms0) cell 8 = true.
Hypothesis Hcnw : (bv_unsigned cell + 8 <= 2 ^ 64)%Z.
Hypothesis Hcnl : no_lazy model (bv_unsigned cell) (bv_unsigned cell + 8).
Hypothesis Hdisj : (bv_unsigned cell + 8 <= bv_unsigned pn \/ bv_unsigned pn + L + 1 <= bv_unsigned cell)%Z.
Hypothesis H10 : rg ms0 10 = cell.
Hypothesis H12 : rg ms0 12 = Z_to_bv 64 47.
Hypothesis HK : forall ms', PF ms0 ms' -> ms_pc_val ms' = pcw b 20 -> rg ms' 11 = pn + Z_to_bv 64 (L + 1) ->
  rg ms' 13 = w0 -> (forall x, ms_mem ms' x = prog_mem (ms_mem ms0) cell pn (pn_off bs) x) ->
  realizes_cfg segs cfg (mkCfg ms' model) T.

Definition B (j : Z) : byte := nth (Z.to_nat j) (bs ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).

Lemma B_nz : forall j, (0 <= j < L)%Z -> bv_unsigned (B j) <> 0%Z.
Proof.
  intros j Hj. unfold B. rewrite nth_app_l by lia. apply nul_free_nth; [exact (proj2 Hstr) | lia].
Qed.
Lemma B_z : bv_unsigned (B L) = 0%Z.
Proof. unfold B. rewrite Nat2Z.id, nth_app_last. reflexivity. Qed.

(* [comment removed for export] *)
Lemma prog_mem_str : forall k x, (bv_unsigned pn <= bv_unsigned x < bv_unsigned pn + L + 1)%Z ->
  prog_mem (ms_mem ms0) cell pn k x = ms_mem ms0 x.
Proof.
  intros k x Hx. unfold prog_mem. destruct (k =? 0)%nat; [reflexivity|].
  apply w2m_outside; rewrite store_bytes8_len; cbn; lia.
Qed.

Lemma rd1p : forall (i : nat) mem, (i <= length bs)%nat ->
  (forall x, mem x = prog_mem (ms_mem ms0) cell pn (after_last_slash (firstn i bs) 0 0) x) ->
  rdn segs mem (pn + Z_to_bv 64 (Z.of_nat i)) 1 = Some [B (Z.of_nat i)].
Proof.
  intros i mem Hi Hm.
  pose proof (bat_of_rdn segs (ms_mem ms0) _ pn _ i (proj1 Hstr) ltac:(lia)) as H.
  apply rdn_1. unfold bat in *. rewrite Hm, prog_mem_str.
  - unfold B. rewrite Nat2Z.id. exact H.
  - rewrite u_add_small by lia. lia.
Qed.

Lemma store_ok_pm : forall k mem, (forall x, mem x = prog_mem (ms_mem ms0) cell pn k x) ->
  store_ok segs mem cell 8 = true.
Proof.
  intros k mem Hm. rewrite (store_ok_ext segs 8 mem (prog_mem (ms_mem ms0) cell pn k)) by exact Hm.
  unfold prog_mem. destruct (k =? 0)%nat; [exact Hok|].
  apply (store_ok_mono segs 8 (ms_mem ms0)); [apply write_to_mem_grows | exact Hok].
Qed.

Lemma prog_loop : forall d (i : nat) ms, (i + d = length bs)%nat ->
  ms_pc_val ms = pcw b 8 -> PF ms0 ms -> rg ms 11 = pn + Z_to_bv 64 (Z.of_nat i + 1) ->
  (forall x, ms_mem ms x = prog_mem (ms_mem ms0) cell pn (after_last_slash (firstn i bs) 0 0) x) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  induction d as [|d IH]; intros i ms Hid Hpc HF H11 Hm;
    pose proof HF as (Hsvc & _ & _ & _ & _ & HR);
    assert (H10' : rg ms 10 = cell) by (rewrite HR by (cbn; intuition discriminate); exact H10);
    assert (H12' : rg ms 12 = Z_to_bv 64 47) by (rewrite HR by (cbn; intuition discriminate); exact H12).
  all: eapply rzc_acc; [ assumption | assumption
       | eapply wacc_Load; [ fetch_tac F_p8 | reflexivity | exact D_p8
                           | rewrite H11, w_add_sext_z; lits; replace (Z.of_nat i + 1 + -1)%Z with (Z.of_nat i) by lia;
                             apply (rd1p i); [lia | exact Hm] ]
       | apply acc_ok_one; rewrite H11, w_add_sext_z; lits; replace (Z.of_nat i + 1 + -1)%Z with (Z.of_nat i) by lia;
         cbn [msz_n]; rewrite u_add_small by lia; [ lia | apply (no_lazy_sub model _ _ _ _ Hnl); lia ]
       | rewrite Hpc; pcn; rewrite lbu_val; nrm ].
  all: wsx wacc_Branch F_p12 D_p12. all: rgn. all: rewrite H12', branch_eq_47.
  - (* [comment removed for export] *)
    assert (Hi : i = length bs) by lia. subst i. rewrite B_z. cbn [Z.eqb]. pcn.
    wsx wacc_Branch F_p16 D_p16. rgn. rewrite (br_ne0 0) by lia. cbn [Z.eqb negb]. pcn.
    apply HK.
    + pfs HF.
    + reflexivity.
    + rgn. rewrite H11. f_equal.
    + rgn. reflexivity.
    + intros x. cbn [ms_mem setx]. rewrite Hm, firstn_all. reflexivity.
  - (* [comment removed for export] *)
    pose proof (B_nz (Z.of_nat i) ltac:(lia)) as Hnz.
    destruct (Z.eqb_spec (bv_unsigned (B (Z.of_nat i))) 47) as [Hsl|Hnsl].
    + (* [comment removed for export] *)
      pcn.
      eapply rzc_acc; [ assumption | reflexivity
        | eapply wacc_Store; [ fetch_tac F_p0 | reflexivity | exact D_p0
                             | rgn; rewrite H10', add_sext0; cbn [msz_n ms_mem setx]; apply (store_ok_pm _ _ Hm) ]
        | apply acc_ok_one; rgn; rewrite H10', add_sext0; cbn [msz_n]; [ lia | exact Hcnl ]
        | pcn; nrm ].
      wsx wacc_OpImm F_p4 D_p4. rgn. rewrite H11, alu_add, w_add_sext_z. lits.
      apply (IH (S i)); [ lia | reflexivity | pfs HF | rgn; f_equal; f_equal; lia | ].
      intros x. cbn [ms_mem setx]. rgn. rewrite ?H10', ?add_sext0, ?H11.
      rewrite (als_firstn_S bs i ltac:(lia)).
      replace (nth i bs (Z_to_bv 8 0)) with (B (Z.of_nat i)) by (unfold B; rewrite Nat2Z.id, nth_app_l by lia; reflexivity).
      rewrite Hsl, Z.eqb_refl. unfold prog_mem. cbn [Nat.eqb].
      destruct (Z_le_dec (bv_unsigned cell) (bv_unsigned x)) as [Hlo|Hlo];
        [destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned cell + 8)) as [Hhi|Hhi] |].
      * replace (pn + Z_to_bv 64 (Z.of_nat i + 1)) with (pn + Z_to_bv 64 (Z.of_nat (S i))) by (f_equal; f_equal; lia).
        apply w2m_inside_indep; rewrite store_bytes8_len; cbn; lia.
      * rewrite !w2m_outside by (rewrite store_bytes8_len; cbn; lia). rewrite Hm. unfold prog_mem.
        destruct (after_last_slash (firstn i bs) 0 0 =? 0)%nat; [reflexivity|].
        apply w2m_outside; rewrite store_bytes8_len; cbn; lia.
      * rewrite !w2m_outside by (rewrite store_bytes8_len; cbn; lia). rewrite Hm. unfold prog_mem.
        destruct (after_last_slash (firstn i bs) 0 0 =? 0)%nat; [reflexivity|].
        apply w2m_outside; rewrite store_bytes8_len; cbn; lia.
    + (* [comment removed for export] *)
      pcn.
      wsx wacc_Branch F_p16 D_p16. rgn. rewrite (br_ne0 (bv_unsigned (B (Z.of_nat i)))) by (pose proof (byte_range (B (Z.of_nat i))); lia).
      rewrite (proj2 (Z.eqb_neq _ 0%Z) Hnz). cbn [negb]. pcn.
      wsx wacc_OpImm F_p4 D_p4. rgn. rewrite H11, alu_add, w_add_sext_z. lits.
      apply (IH (S i)); [ lia | reflexivity | pfs HF | rgn; f_equal; f_equal; lia | ].
      intros x. cbn [ms_mem setx]. rewrite Hm.
      rewrite (als_firstn_S bs i ltac:(lia)).
      replace (nth i bs (Z_to_bv 8 0)) with (B (Z.of_nat i)) by (unfold B; rewrite Nat2Z.id, nth_app_l by lia; reflexivity).
      rewrite (proj2 (Z.eqb_neq _ 47%Z) Hnsl). reflexivity.
Qed.
End Loop.

(* [comment removed for export] *)
Theorem prog_sum : forall (ms : machine_state) (model : Model) (T : TSet) (pn cell : word) (bs : list byte),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw b 8 -> m_halted model = None ->
  rg ms 10 = cell -> rg ms 11 = pn + Z_to_bv 64 1 -> rg ms 12 = Z_to_bv 64 47 ->
  cstr segs (ms_mem ms) pn bs ->
  (bv_unsigned pn + Z.of_nat (length bs) + 1 <= 2 ^ 64)%Z ->
  no_lazy model (bv_unsigned pn) (bv_unsigned pn + Z.of_nat (length bs) + 1) ->
  store_ok segs (ms_mem ms) cell 8 = true ->
  (bv_unsigned cell + 8 <= 2 ^ 64)%Z ->
  no_lazy model (bv_unsigned cell) (bv_unsigned cell + 8) ->
  (bv_unsigned cell + 8 <= bv_unsigned pn \/ bv_unsigned pn + Z.of_nat (length bs) + 1 <= bv_unsigned cell)%Z ->
  (forall ms', PF ms ms' -> ms_pc_val ms' = pcw b 20 -> rg ms' 11 = pn + Z_to_bv 64 (Z.of_nat (length bs) + 1) ->
     rg ms' 13 = w0 -> (forall x, ms_mem ms' x = prog_mem (ms_mem ms) cell pn (pn_off bs) x) ->
     realizes_cfg segs cfg (mkCfg ms' model) T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model T pn cell bs Hsvc Hpc Hh H10 H11 H12 Hstr Hnw Hnl Hok Hcnw Hcnl Hdisj HK.
  apply (prog_loop model Hh ms T pn cell bs Hstr Hnw Hnl Hok Hcnw Hcnl Hdisj H10 H12 HK (length bs) 0 ms);
    [ lia | exact Hpc | apply PF_refl; exact Hsvc | rewrite H11; reflexivity | ].
  intros x. reflexivity.
Qed.
End Prog.
