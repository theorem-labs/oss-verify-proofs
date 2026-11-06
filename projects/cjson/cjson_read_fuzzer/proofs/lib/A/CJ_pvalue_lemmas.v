(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Image FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.      (* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_split_app : forall m A cs1 cs2,
  rw_cells asegs m A (cs1 ++ cs2) <-> rw_cells asegs m A cs1 /\ rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)). rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_recell : forall m A cs cs',
  rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf HB] HW] Hwf' HE. split; [split; [exact Hwf'| rewrite HE; exact HB]|].
  rewrite <- (cells_bytes_length cs' Hwf'), HE, (cells_bytes_length cs Hwf). exact HW.
Qed.

(* [comment removed for export] *)
Lemma zero_node_cells : forall m A,
  rw_cells asegs m A [CB 64 (repeat (Z_to_bv 8 0) 64)] ->
  rw_cells asegs m A (node_cells 0 (wz 0) 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0).
Proof. intros m A H. eapply rw_cells_recell; [exact H| cbn; repeat split; exact I| reflexivity]. Qed.

Lemma zero_node_cells' : forall m A,
  rw_cells asegs m A [CB (Z.to_nat 64) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 64))] ->
  rw_cells asegs m A (node_cells 0 (wz 0) 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0).
Proof. intros m A H. apply zero_node_cells. exact H. Qed.

(* [comment removed for export] *)
Lemma zero_node_words : forall m A,
  rw_cells asegs m A [CB 64 (repeat (Z_to_bv 8 0) 64)] ->
  rw_cells asegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof. intros m A H. eapply rw_cells_recell; [exact H| cbn; repeat split; exact I| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma zero_node_cells_prev : forall m A pv,
  rw_cells asegs m A [C8 (Z_to_bv 64 0); C8 pv; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m A (node_cells 0 pv 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0).
Proof. intros m A pv H. eapply rw_cells_recell; [exact H| cbn; repeat split; exact I| reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition NUM_MASK : Z := 288230376218820613.

Lemma num_mask_numch : forall s, 0 <= s <= 58 -> Z.land (Z.shiftr NUM_MASK s) 1 <> 0 -> is_numch (s + 43) = true.
Proof.
  intros s Hs H. rewrite <- (Z2Nat.id s) in H |- * by lia. remember (Z.to_nat s) as k eqn:Ek.
  assert (Hk : (k <= 58)%nat) by lia. clear Ek Hs s.
  do 59 (destruct k as [|k]; [first [vm_compute; reflexivity | exfalso; apply H; vm_compute; reflexivity] |]). lia.
Qed.

Lemma digit_numch : forall c, 48 <= c <= 57 -> is_numch c = true.
Proof. intros c Hc. unfold is_numch. replace (48 <=? c) with true by (symmetry; apply Z.leb_le; lia). replace (c <=? 57) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Lemma dot_numch : is_numch 46 = true.
Proof. reflexivity. Qed.

Lemma numch_not_x : forall c, is_numch c = true -> c <> 120 /\ c <> 88.
Proof. intros c H. unfold is_numch in H. split; intros ->; discriminate. Qed.

Lemma numch_range : forall c, is_numch c = true -> 0 <= c < 256.
Proof.
  intros c H. unfold is_numch in H.
  repeat match type of H with
  | (?a || ?b) = true => apply Bool.orb_true_iff in H; destruct H as [H|H]
  end.
  - apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
  - apply Z.eqb_eq in H. lia.
  - apply Z.eqb_eq in H. lia.
  - apply Z.eqb_eq in H. lia.
  - apply Z.eqb_eq in H. lia.
  - apply Z.eqb_eq in H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Chains.
  Variable AI : art_iface.

  (* [comment removed for export] *)
  Lemma cj_chain_set_prev : forall sp0 SPB LBX LF TRS BB m0 mo g R T m m' d p B pv',
    ART AI sp0 SPB LBX LF TRS BB m0 mo g -> Permutation (B ++ R) LBX ->
    cj_chain T m d p B -> p <> 0 ->
    munch [(p + 8, p + 16)] m m' -> wmono asegs m m' ->
    (forall nx pv ch ty p1 vs vi p2 vd ky, rw_cells asegs m p (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
                                          rw_cells asegs m' p (node_cells nx pv' ch ty p1 vs vi p2 vd ky)) ->
    cj_chain T m' d p B.
  Proof.
    intros sp0 SPB LBX LF TRS BB m0 mo g R T m m' d p B pv' HL HP CH NZ MU WM HND.
    destruct (cj_chain_cons_inv _ _ _ _ _ CH NZ)
      as (d0 & nx & pv & ch & ty & p1 & vs & vi & p2 & vd & ky & Bv & Bk & Bc & Bn & -> & ND & TY & HT & SV & SK & CHC & CHN & ->).
    assert (DJ : forall A n, In (A, n) (Bv ++ Bk ++ Bc ++ Bn) -> disjoint_from [(p + 8, p + 16)] A n).
    { intros A n Hin. cbn. split; [|exact I].
      assert (HP' : Permutation ((p, 64) :: (Bv ++ Bk ++ Bc ++ Bn) ++ R) LBX) by exact HP.
      destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HP' A n ltac:(apply in_or_app; left; exact Hin)) as [_ D]. lia. }
    eapply cj_chain_cons; [exact NZ| exact (HND _ _ _ _ _ _ _ _ _ _ ND)| exact TY| exact HT| | | |].
    - eapply cj_str_frame; [exact SV| exact MU| exact WM|]. intros A n Hin. apply DJ. apply in_or_app; left; exact Hin.
    - eapply cj_str_frame; [exact SK| exact MU| exact WM|]. intros A n Hin. apply DJ. apply in_or_app; right; apply in_or_app; left; exact Hin.
    - eapply cj_chain_frame; [exact CHC| exact MU| exact WM|]. intros A n Hin. apply DJ. do 2 (apply in_or_app; right). apply in_or_app; left; exact Hin.
    - eapply cj_chain_frame; [exact CHN| exact MU| exact WM|]. intros A n Hin. apply DJ. do 3 (apply in_or_app; right). exact Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma cj_chain_relink : forall sp0 SPB LBX LF TRS BB m0 mo g R T m m' d p nx pv' ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn,
    ART AI sp0 SPB LBX LF TRS BB m0 mo g -> Permutation (((p, 64) :: Bv ++ Bk ++ Bc ++ Bn) ++ R) LBX ->
    p <> 0 -> 0 <= ty < 256 -> T ty ->
    cj_str m vs Bv -> cj_str m ky Bk -> cj_chain T m d ch Bc -> cj_chain T m (S d) nx Bn ->
    munch [(p + 8, p + 16)] m m' -> wmono asegs m m' ->
    rw_cells asegs m' p (node_cells nx pv' ch ty p1 vs vi p2 vd ky) ->
    cj_chain T m' (S d) p ((p, 64) :: Bv ++ Bk ++ Bc ++ Bn).
  Proof.
    intros until Bn. intros HL HP NZ TY HT SV SK CHC CHN MU WM ND.
    assert (DJ : forall A n, In (A, n) (Bv ++ Bk ++ Bc ++ Bn) -> disjoint_from [(p + 8, p + 16)] A n).
    { intros A n Hin. cbn. split; [|exact I].
      destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HP A n ltac:(apply in_or_app; left; exact Hin)) as [_ D]. lia. }
    eapply cj_chain_cons; [exact NZ| exact ND| exact TY| exact HT| | | |].
    - eapply cj_str_frame; [exact SV| exact MU| exact WM|]. intros A n Hin. apply DJ. apply in_or_app; left; exact Hin.
    - eapply cj_str_frame; [exact SK| exact MU| exact WM|]. intros A n Hin. apply DJ. apply in_or_app; right; apply in_or_app; left; exact Hin.
    - eapply cj_chain_frame; [exact CHC| exact MU| exact WM|]. intros A n Hin. apply DJ. do 2 (apply in_or_app; right). apply in_or_app; left; exact Hin.
    - eapply cj_chain_frame; [exact CHN| exact MU| exact WM|]. intros A n Hin. apply DJ. do 3 (apply in_or_app; right). exact Hin.
  Qed.
End Chains.

(* [comment removed for export] *)
Section FromART2.
  Variable AI : art_iface.

  (* [comment removed for export] *)
  Lemma art_icpt_cells : forall sp0 SPB LB LF TRS BB m mo g, ART AI sp0 SPB LB LF TRS BB m mo g -> icpt_cells m.
  Proof.
    intros until g. intros HL. pose proof (art_rtcells AI _ _ _ _ _ _ _ _ _ HL) as H.
    unfold ARTCELLS in H. unfold A_MUSL_MEMCPY, A_MUSL_MEMSET, A_MUSL_STRLEN in *.
    decompose [and ex] H; clear H.
    unfold icpt_cells, shbase_cells, ro_cells.
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma art_uar_cells : forall sp0 SPB LB LF TRS BB m mo g, ART AI sp0 SPB LB LF TRS BB m mo g -> uar_cells m.
  Proof. intros until g. intros HL. destruct (art_rtcells AI _ _ _ _ _ _ _ _ _ HL) as (_ & [G1 G2] & _). split; assumption. Qed.

  (* [comment removed for export] *)
  Lemma art_blocks_high_apart : forall sp0 SPB LB LF TRS BB m mo g P,
    ART AI sp0 SPB LB LF TRS BB m mo g -> In (P - 32, 1) LF ->
    forall A n, In (A, n) LB -> AIMG_HI <= A /\ (A + n <= P \/ P + 56 <= A).
  Proof.
    intros until P. intros HL PLF A n Hin.
    pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) as (R1 & _ & _ & _).
    destruct (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL PLF) as (_ & _ & _ & _ & _ & _ & _ & FD).
    destruct (FD A n Hin); change (fsz 1) with 128 in *; split; try exact R1; lia.
  Qed.
End FromART2.

(* [comment removed for export] *)
Definition astkmalloc_post' (AI : art_iface) (k : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z) (lo : Z) (errv : word)
    (m : word -> option byte) (mo : Model) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (Fr : Z) (junk : list byte) (fl : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' AERRNO [C4 errv]
    /\ cj_pres sp0 LB LF (bv_unsigned sp) m m' /\ g' = g /\ mo' = mo
    /\ a0 = wz Fr /\ Fr mod fsz k = 0 /\ AIMG_HI <= Fr /\ Fr + fsz k <= alloc_ceiling /\ ~ In Fr (map fst LF)
    /\ (forall A n, In (A, n) LB -> A + n <= Fr \/ Fr + fsz k <= A)
    /\ ART AI sp0 SPB LB ((Fr, k) :: LF) TRS B m' mo' g'
    /\ rw_cells asegs m' Fr [CB (Z.to_nat (fsz k - 8)) junk]
    /\ cells_at asegs m' (Fr + fsz k - 8) [C8 (wz fl)]
    /\ rw_cells asegs m' (SH Fr) (shcells (repeat 0 (Z.to_nat (fsz k / 8)))).

Definition stkmalloc_stmt' (AI : art_iface) (k : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z) (lo : Z) (errv : word),
    ART AI sp0 SPB LB LF TRS B m mo g ->
    bv_unsigned sp <= SPB ->
    stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ASTKMALLOC_STACK ->
    rw_cells asegs m AERRNO [C4 errv] -> mem_inv asegs m -> tp = wz ATP ->
    lf_count k LF < fcap k ->
    LSCPS asegs (astkmalloc_post' AI k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LB LF TRS B lo errv m mo g)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz (if k =? 1 then ASTKMALLOC1 else ASTKMALLOC2)) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
Lemma ppres_cj_lseg : forall sp0 LR LF SP P m m' T d p q B,
  ppres sp0 LR LF SP P m m' -> cj_lseg T m d p q B -> (forall b, In b B -> In b LR) ->
  (forall A n, In (A, n) B -> AIMG_HI <= A /\ (A + n <= P \/ P + 56 <= A)) ->
  cj_lseg T m' d p q B.
Proof.
  intros sp0 LR LF SP P m m' T d p q B HP H HB HR. eapply cj_lseg_magree; [exact H| exact HP|].
  intros a (A & n & Hin & Ha). destruct (HR A n Hin) as [H1 H2].
  split; [right; right; left; exists A, n; split; [apply HB; exact Hin| exact Ha]|]. unfold sclr, AERRNO, ATP, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. lia.
Qed.

(* [comment removed for export] *)
Lemma cj_lseg_snoc0 : forall T m d p q B nx pv ch ty p1 vs vi p2 vd Bv Bc,
  cj_lseg T m d p q B -> q <> 0 ->
  rw_cells asegs m q (node_cells nx pv ch ty p1 vs vi p2 vd 0) ->
  0 <= ty < 256 -> T ty -> cj_str m vs Bv -> cj_chain T m d ch Bc ->
  cj_lseg T m d p nx (B ++ (q, 64) :: Bv ++ Bc).
Proof.
  intros. replace (Bv ++ Bc) with (Bv ++ [] ++ Bc) by reflexivity.
  eapply cj_lseg_snoc; eauto. apply cj_str_null.
Qed.

Lemma CJ_PRINTABLE_range : forall ty, CJ_PRINTABLE ty -> 0 <= ty < 256.
Proof. intros ty H. unfold CJ_PRINTABLE in H. cbn in H. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Fagree_set : forall F F' (k : bv 5) v,
  Fagree F F' -> (bv_unsigned k = 10 \/ bv_unsigned k = 14 \/ bv_unsigned k = 15) -> Fagree F (bvmap_set k v F').
Proof.
  intros F F' k v HA Hk r H10 H14 H15. rewrite freg_get_other; [apply HA; assumption|].
  unfold bv_eqb. apply Z.eqb_neq. lia.
Qed.

Lemma Fagree_of_strtod : forall F F',
  (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k) ->
  Fagree F F'.
Proof. intros F F' H k A B C. apply H; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LIT_NULL : Z := 0x211c0.
Definition LIT_FALSE : Z := 0x211e0.
Definition LIT_TRUE : Z := 0x21200.
Definition lit_null : list byte := map wb [110; 117; 108; 108; 0].
Definition lit_false : list byte := map wb [102; 97; 108; 115; 101; 0].
Definition lit_true : list byte := map wb [116; 114; 117; 101; 0].

Lemma lit_null_at : forall m, mem_inv asegs m -> bytes_at asegs m LIT_NULL lit_null.
Proof. intros m MI. apply (ro_bytes_at asegs m LIT_NULL lit_null MI); [unfold LIT_NULL; lia| cbn; unfold LIT_NULL; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma lit_false_at : forall m, mem_inv asegs m -> bytes_at asegs m LIT_FALSE lit_false.
Proof. intros m MI. apply (ro_bytes_at asegs m LIT_FALSE lit_false MI); [unfold LIT_FALSE; lia| cbn; unfold LIT_FALSE; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma lit_true_at : forall m, mem_inv asegs m -> bytes_at asegs m LIT_TRUE lit_true.
Proof. intros m MI. apply (ro_bytes_at asegs m LIT_TRUE lit_true MI); [unfold LIT_TRUE; lia| cbn; unfold LIT_TRUE; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lit_slots : In (LIT_NULL, 5) AGLOB_STRS /\ In (LIT_FALSE, 6) AGLOB_STRS /\ In (LIT_TRUE, 5) AGLOB_STRS.
Proof. unfold AGLOB_STRS, LIT_NULL, LIT_FALSE, LIT_TRUE. cbn. repeat split; tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma perm_pick_head : forall (u h : cblock) (R LR : list cblock),
  Permutation (h :: R ++ u :: LR) (u :: (h :: R) ++ LR).
Proof.
  intros. change (Permutation ((h :: R) ++ u :: LR) (u :: (h :: R) ++ LR)). apply Permutation_sym. apply (Permutation_middle (h :: R) LR u).
Qed.

Lemma perm_pick_mid : forall (u c : cblock) (B1 T LR : list cblock),
  Permutation (c :: (B1 ++ T) ++ u :: LR) (u :: (B1 ++ c :: T) ++ LR).
Proof.
  intros. transitivity (u :: c :: (B1 ++ T) ++ LR).
  - change (Permutation ((c :: B1 ++ T) ++ u :: LR) (u :: (c :: B1 ++ T) ++ LR)). apply Permutation_sym. apply (Permutation_middle (c :: B1 ++ T) LR u).
  - apply perm_skip. rewrite <- !app_assoc. change (Permutation (c :: B1 ++ (T ++ LR)) (B1 ++ c :: (T ++ LR))). apply (Permutation_middle B1 (T ++ LR) c).
Qed.

(* [comment removed for export] *)
Lemma perm_new_done : forall (u a : cblock) (T X LR : list cblock),
  Permutation (a :: T ++ u :: X ++ LR) (u :: (X ++ a :: T) ++ LR).
Proof.
  intros. transitivity (u :: a :: T ++ X ++ LR).
  - change (Permutation ((a :: T) ++ u :: X ++ LR) (u :: (a :: T) ++ X ++ LR)). apply Permutation_sym. apply (Permutation_middle (a :: T) (X ++ LR) u).
  - apply perm_skip. rewrite <- app_assoc. cbn [app].
    transitivity (a :: (X ++ T ++ LR)).
    + apply perm_skip. rewrite (app_assoc T X LR), (app_assoc X T LR). apply Permutation_app_tail. apply Permutation_app_comm.
    + apply (Permutation_middle X (T ++ LR) a).
Qed.

(* [comment removed for export] *)
Lemma perm_new_done_k : forall (u a sk : cblock) (Bv Bc X LR : list cblock),
  Permutation (a :: (Bv ++ Bc) ++ sk :: u :: X ++ LR) (u :: (X ++ a :: Bv ++ [sk] ++ Bc) ++ LR).
Proof.
  intros. transitivity (a :: (Bv ++ [sk] ++ Bc) ++ u :: X ++ LR); [| apply perm_new_done].
  apply perm_skip. rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
  apply Permutation_sym. apply (Permutation_middle Bc (u :: X ++ LR) sk).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma munch_nil_eq : forall m m', munch [] m m' -> m' = m.
Proof. intros m m' H. apply functional_extensionality. intros x. apply H. exact I. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition dch (depth : Z) : nat := Z.to_nat (999 - depth).

Definition pv_pure (STK : Z) (sp tp : word) (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe)
    (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z) : Prop :=
  Permutation ((U, 64) :: LR) LB
  /\ (In (D, n) LR /\ D <= CA /\ CA + blen <= D + n)
  /\ Z.of_nat (length bs) = blen /\ blen < 2^31
  /\ alloc_ceiling <= lo /\ ASTACK_BOTTOM sp0 <= lo /\ lo <= bv_unsigned sp - STK
  /\ (In (P - 32, 1) LF /\ AIMG_HI <= P - 32 /\ P - 32 + 128 <= alloc_ceiling /\ (P - 32) mod 128 = 0)
  /\ (0 <= bv_unsigned sp /\ bv_unsigned sp <= SPB /\ SPB < 2^62 /\ bv_unsigned sp + 16 < ASTACK_TOP sp0
      /\ sp0 <= 2^47 /\ bv_unsigned sp mod 16 = 0)
  /\ 0 <= off <= blen /\ 0 <= depth <= 1000
  /\ tp = wz ATP
  /\ ablock_range U 64 /\ ablock_range D n /\ (U + 64 <= D \/ D + n <= U)
  /\ (U + 64 + 16 <= P - 32 \/ P - 32 + 128 <= U - 16) /\ (D + n + 16 <= P - 32 \/ P - 32 + 128 <= D - 16)
  (* [comment removed for export] *)
  /\ sclr U 64 /\ sclr (P - 32) 128 /\ sclr D (Z.max n 1).   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma pvc_lits : forall STK sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo,
  pv_pure STK sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo ->
  Permutation ((U, 64) :: LR) LB /\ (In (D, n) LR /\ D <= CA /\ CA + blen <= D + n)
  /\ Z.of_nat (length bs) = blen /\ blen < 2^31
  /\ alloc_ceiling <= lo /\ ASTACK_BOTTOM sp0 <= lo /\ lo <= bv_unsigned sp - STK
  /\ (In (P - 32, 1) LF /\ 0x5ff000 <= P - 32 /\ P - 32 + 128 <= alloc_ceiling /\ (P - 32) mod 128 = 0)
  /\ (0 <= bv_unsigned sp /\ bv_unsigned sp <= SPB /\ SPB < 2^62 /\ bv_unsigned sp + 16 < ASTACK_TOP sp0
      /\ sp0 <= 2^47 /\ bv_unsigned sp mod 16 = 0)
  /\ 0 <= off <= blen /\ 0 <= depth <= 1000 /\ tp = wz ATP
  /\ (0x5ff000 <= U /\ U mod 16 = 0 /\ 0 <= 64 /\ U + 64 <= alloc_ceiling)
  /\ (0x5ff000 <= D /\ D mod 16 = 0 /\ 0 <= n /\ D + Z.max n 1 <= alloc_ceiling)
  /\ (U + 64 <= D \/ D + n <= U)
  /\ (U + 64 + 16 <= P - 32 \/ P - 32 + 128 <= U - 16) /\ (D + n + 16 <= P - 32 \/ P - 32 + 128 <= D - 16)
  /\ 0 <= bv_unsigned sp < 2^64
  /\ sp0 - 0xa0 <= ASTACK_TOP sp0 <= sp0 - 0xa0 + 4095 /\ ASTACK_BOTTOM sp0 = ASTACK_TOP sp0 - 0x800000
  (* [comment removed for export] *)
  /\ (U + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= U) /\ (P - 32 + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= P - 32)
  /\ (D + Z.max n 1 <= 0x7fff7000 \/ 0x10007fff8000 <= D).
Proof.
  intros until lo. intros H. unfold sclr, pv_pure, ablock_range, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in H. try rewrite alloc_ceiling_eq in H.
  pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2^64) in R.
  pose proof (ASTACK_TOP_le sp0) as T.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & (A13 & A14 & A15 & A16) & A17 & A18 & A19 & A20 & A21 & A22).
  replace (U + Z.max 64 1) with (U + 64) in A16 by lia.
  repeat (split; [assumption|]). split; [repeat split; assumption|]. split; [assumption|]. split; [assumption|].
  split; [assumption|]. split; [assumption|]. split; [exact R|]. split; [exact T|]. split; [reflexivity|]. split; [exact A21| exact A22].
Qed.

(* [comment removed for export] *)
Lemma pv_pure_intro : forall (AI : art_iface) (TI : trs_iface) STK m mo g sp tp sp0 SPB LB LR LF TRS np B U P CA blen off depth bs D n lo errv
    nx pv ch ty p1 vs vi p2 vd ky,
  parse_inv AI TI m mo g sp0 SPB LB [] LR LF TRS np B U P CA blen bs D n lo (bv_unsigned sp) errv ->
  rw_cells asegs m U (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
  0 <= off <= blen -> 0 <= depth <= 1000 -> lo <= bv_unsigned sp - STK -> tp = wz ATP ->
  pv_pure STK sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo.
Proof.
  intros until ky.
  intros (HL & HPU & HD & DCA & CAD & BY & LEN & BLEN & ERR & MI & ST & CEIL & TV & PLF & PSH & SP1 & SP2 & SP3 & SP4 & SP5 & BOT & AL) ND OFF DEP LO TP.
  cbn [app] in HPU.
  assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU).
  assert (IND : In (D, n) LB) by (eapply Permutation_in; [exact HPU| right; exact HD]).
  assert (UD : U <> D).
  { intros ->. pose proof (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL)) as NDP.
    apply (NoDup_map_fst_perm _ _ (Permutation_sym HPU)) in NDP. rewrite NoDup_ListNoDup in NDP. cbn in NDP.
    inversion NDP; subst. apply H1. apply (in_map fst) in HD. exact HD. }
  pose proof (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL PLF) as (_ & FAL & FLO & FHI & _ & _ & _ & FD). change (fsz 1) with 128 in *.
  split; [exact HPU|]. split; [split; [exact HD| split; [exact DCA| exact CAD]]|]. split; [exact LEN|]. split; [exact BLEN|].
  split; [exact CEIL|]. split; [exact BOT|]. split; [exact LO|].
  split; [split; [exact PLF| split; [exact FLO| split; [exact FHI| exact FAL]]]|].
  split; [repeat split; assumption|]. split; [exact OFF|]. split; [exact DEP|]. split; [exact TP|].
  split; [eapply (art_block_range AI); [exact HL| exact INU]|].
  split; [eapply (art_block_range AI); [exact HL| exact IND]|].
  split; [destruct (art_blocks_disjoint AI _ _ _ _ _ _ _ _ _ _ _ _ _ HL INU IND UD); lia|].
  split; [destruct (FD U 64 INU); lia|]. split; [destruct (FD D n IND); lia|].
  split; [eapply (art_block_sclr AI); [exact HL| exact INU| lia| lia]|].
  split; [eapply (art_frame_sclr AI); [exact HL| exact PLF| lia| change (fsz 1) with 128; lia]
         | eapply (art_block_sclr AI); [exact HL| exact IND| lia| lia]].
Qed.


End CeilWrap.
