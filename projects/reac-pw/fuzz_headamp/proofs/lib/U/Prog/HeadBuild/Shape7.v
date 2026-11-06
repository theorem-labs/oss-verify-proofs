(** One property of a Struct-shaped object (shape 7) in the UBSan builder, 0x132a8 -> 0x13fb0 (pod.h:399-404):
    sel = fuzz_u8 (its value unused; the UBSan check on in->p + 1 not taken), the shape test, then the Int pod 0:
    memset(e->body, 0, 96), e->type = e->size = 4, pod_write_ent(pp, e). Proved against Model.prop_step 7.

    Also here, shared with [Int7]: a memset of frame bytes above the cells the builder reads back, a pod_write_ent
    call from a block image (through [PweFacts]), and the frame stores of e at sp + 0xb8. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c
  reac_headamp_prop_parse_result_c memset_c pod_write_ent_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadBuild Require Import Facts Cut Close PweFacts UTac Key.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** ** Frame cells below sp + 0xb8 *)
(** A fact about memory that reads only [sp, sp + 0xb8) (the preheader's cells, the object's, seen_params and
    `first`): every write that misses that range keeps it. *)
Definition kept_on (sp : word) (P : (word -> option byte) -> Prop) : Prop :=
  forall W m1 m2, munch W m1 m2 -> (forall x, bv_unsigned sp <= x < bv_unsigned sp + 0xb8 -> outside W x) ->
  P m1 -> P m2.

Lemma kept_frame : forall sp P, kept_on sp P -> frame_only sp P.
Proof. intros sp P H W m1 m2 MU HW. apply (H W m1 m2 MU). intros x Hx. apply HW. unfold FRAME_LOCALS. lia. Qed.

Lemma cell8_kept : forall (sp : word) W m1 m2 o v, munch W m1 m2 ->
  (forall x, bv_unsigned sp <= x < bv_unsigned sp + 0xb8 -> outside W x) -> 0 <= o -> o + 8 <= 0xb8 ->
  cell8 m1 (bv_unsigned sp + o) v -> cell8 m2 (bv_unsigned sp + o) v.
Proof.
  intros sp W m1 m2 o v MU HW H1 H2 H. unfold cell8 in *. apply (bytes_at_keep W m1 m2 _ _ H MU).
  rewrite length_le8. intros x Hx. apply HW. lia.
Qed.

Ltac cells_kept MU HW :=
  repeat match goal with |- _ /\ _ => split end;
  (apply (cell8_kept _ _ _ _ _ _ MU HW); [lia | lia | assumption]).

Lemma CFIX_kept : forall sp pp cap, kept_on sp (CFIX sp pp cap).
Proof.
  intros sp pp cap W m1 m2 MU HW H. unfold CFIX in *.
  destruct H as (C00 & C18 & C30 & C48 & C50 & C58 & C60 & C70 & C68 & C78 & C80 & C98 & CA0 & C08). cells_kept MU HW.
Qed.

Lemma CPROP_kept : forall sp fl sh np, kept_on sp (CPROP sp fl sh np).
Proof. intros sp fl sh np W m1 m2 MU HW H. unfold CPROP in *. destruct H as (C10 & C20 & C90). cells_kept MU HW. Qed.

Definition FS (sp : word) (pp fl cap sh np : Z) (m1 : word -> option byte) : Prop :=
  CFIX sp pp cap m1 /\ CPROP sp fl sh np m1.

Lemma FS_kept : forall sp pp fl cap sh np, kept_on sp (FS sp pp fl cap sh np).
Proof.
  intros sp pp fl cap sh np W m1 m2 MU HW [CF CP].
  split; [exact (CFIX_kept sp pp cap W m1 m2 MU HW CF) | exact (CPROP_kept sp fl sh np W m1 m2 MU HW CP)].
Qed.

(** A store above sp + 0xb8 (e and the body memsets) or below sp keeps such a fact. *)
Lemma kept_write : forall sp P, kept_on sp P -> forall m1 (w : word) a bs, P m1 -> w = wa a -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2^64 -> (bv_unsigned sp + 0xb8 <= a \/ a + Z.of_nat (length bs) <= bv_unsigned sp) ->
  P (write_to_mem m1 w bs).
Proof.
  intros sp P HP m1 w a bs H1 -> Ha Hb Hd.
  apply (HP [(a, a + Z.of_nat (length bs))] m1); [apply munch_of_write; lia | | exact H1].
  intros x Hx. cbn [outside]. split; [lia | exact I].
Qed.

(** ** The frame's locals as a callee's cells *)
Lemma MBr_frame_cells : forall sp m rest src pp lo, BOK sp rest src pp lo ->
  forall Ib m1 (o : Z) (n : nat), MBr sp m rest src pp lo Ib m1 -> 0 <= o -> o + Z.of_nat n <= FRAME_LOCALS ->
  exists junk, rw_cells rsegs m1 (bv_unsigned sp + o) [CB n junk].
Proof.
  intros sp m rest src pp lo HOK Ib m1 o n MB Ho Hn.
  pose proof MB as (_ & _ & _ & _ & _ & _ & _ & HS & _).
  pose proof HOK as (_ & _ & _ & _ & HM1 & HL0 & HSP & _).
  unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in *.
  destruct (stk_split rsegs m1 lo (bv_unsigned sp + o) _ HS ltac:(lia)) as [_ SB].
  destruct (stk_split rsegs m1 (bv_unsigned sp + o) (bv_unsigned sp + o + Z.of_nat n) _ SB ltac:(lia)) as [SC _].
  destruct (stk_bytes rsegs m1 _ _ SC ltac:(lia)) as (bs & Hl & HB).
  pose proof (stk_wr m1 _ _ SC ltac:(lia)) as HW.
  exists bs. split.
  - split; [cbn [cells_wf cell_wf]; split; [lia | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB].
  - cbn [cells_size csize]. rewrite Nat.add_0_r.
    replace (Z.of_nat n) with (bv_unsigned sp + o + Z.of_nat n - (bv_unsigned sp + o)) by lia. exact HW.
Qed.

(** A call that wrote only [sp + o, sp + o + n) of the frame's locals (memset of e's body). *)
Lemma MBr_call_frame : forall sp m rest src pp lo, BOK sp rest src pp lo ->
  forall Ib m1 m2 (o : Z) (n : nat) bs, MBr sp m rest src pp lo Ib m1 ->
  munch [(bv_unsigned sp + o, bv_unsigned sp + o + Z.of_nat n)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (bv_unsigned sp + o) [CB n bs] -> 0 <= o -> o + Z.of_nat n <= FRAME_LOCALS ->
  MBr sp m rest src pp lo Ib m2.
Proof.
  intros sp m rest src pp lo HOK Ib m1 m2 o n bs MB MU WM MI CB Ho Hn.
  pose proof MB as (_ & _ & _ & _ & _ & _ & _ & HS & _).
  pose proof HOK as (HS0 & HS1 & HP1 & HDJ & HM1 & HL0 & HSP & HPP & _ & _).
  unfold POD_PROPS, MID_STACK, PARSE_STACK, FRAME_LOCALS in *.
  pose proof (stk_of_rw_cells rsegs m2 _ _ CB) as SM. cbn [cells_size csize] in SM. rewrite Nat.add_0_r in SM.
  destruct (stk_split rsegs m1 lo (bv_unsigned sp + o) _ HS ltac:(lia)) as [SA SB].
  destruct (stk_split rsegs m1 (bv_unsigned sp + o) (bv_unsigned sp + o + Z.of_nat n) _ SB ltac:(lia)) as [_ SC].
  apply (MBr_call sp m rest src pp lo HOK Ib m1 m2 _ MB MU WM MI).
  - unfold FRAME_LOCALS. apply (stk_merge rsegs m2 lo (bv_unsigned sp + o)); [| | lia].
    + apply (stk_transport_disjoint rsegs _ m1 m2 _ _ SA MU WM). cbn [disjoint_from]. split; [lia | exact I].
    + apply (stk_merge rsegs m2 _ (bv_unsigned sp + o + Z.of_nat n)); [exact SM | | lia].
      apply (stk_transport_disjoint rsegs _ m1 m2 _ _ SC MU WM). cbn [disjoint_from]. split; [lia | exact I].
  - unfold sub_fp. cbn [outside]. unfold MID_STACK, PARSE_STACK, FRAME_LOCALS. intros x (H1 & _). split; [lia | exact I].
  - cbn [disjoint_from]. unfold POD_PROPS. split; [lia | exact I].
  - cbn [disjoint_from]. split; [lia | exact I].
Qed.

(** ** memset(sp + o, 0, n) at 0x1db4c: the block and a kept_on fact stay, the n bytes become 0 *)
Lemma mset_at : forall sp gp tp F fc m rest src pp lo, BOK sp rest src pp lo -> memset_c.memset_contract ->
  forall (Q : machine_state -> Prop) (P : (word -> option byte) -> Prop) Ib (o : Z) (n : nat)
    (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m1,
  kept_on sp P -> P m1 -> MBr sp m rest src pp lo Ib m1 ->
  bv_unsigned a0 = bv_unsigned sp + o -> bv_unsigned a1 = 0 -> bv_unsigned a2 = Z.of_nat n ->
  0xb8 <= o -> o + Z.of_nat n <= FRAME_LOCALS ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m2,
     MBr sp m rest src pp lo Ib m2 -> P m2 -> bytes_at rsegs m2 (bv_unsigned sp + o) (zeros n) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (ret_pc ra) fc None m2 (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 MEMSET) fc None m1 (seg_rom rsegs)).
Proof.
  intros sp gp tp F fc m rest src pp lo HOK MSET Q P Ib o n ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
    s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1 KP FK MB Ha0 Ha1 Ha2 Ho Hn K.
  destruct (MBr_frame_cells sp m rest src pp lo HOK Ib m1 o n MB ltac:(lia) Hn) as [J HJ].
  eapply evt_cut.
  { eapply MSET with (junk := J).
    - rewrite Ha0, Ha2, Nat2Z.id. exact HJ.
    - exact (MBr_mem_inv sp m rest src pp lo _ m1 MB). }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & -> &
                     MU & WM & MI & CB).
  rewrite Ha0, Ha2 in MU. rewrite Ha0, Ha1, Ha2, Nat2Z.id in CB.
  apply K.
  - exact (MBr_call_frame sp m rest src pp lo HOK Ib m1 m2 o n _ MB MU WM MI CB ltac:(lia) Hn).
  - apply (KP _ m1 m2 MU); [| exact FK]. intros x Hx. cbn [outside]. split; [lia | exact I].
  - exact (rw_cells_CB_bytes _ _ _ _ CB).
Qed.

(** ** pod_write_ent(pp, sp + 0xb8) at 0x14b5c, from a block image *)
Lemma pwe_at : forall sp gp tp F fc m rest src pp lo, BOK sp rest src pp lo -> pp mod 16 = 0 ->
  bv_unsigned sp mod 16 = 0 -> pod_write_ent_c.pod_write_ent_contract ->
  forall (Q : machine_state -> Prop) (P : (word -> option byte) -> Prop) b isp hasp pst es e
    (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m1,
  frame_only sp P -> P m1 -> MBr sp m rest src pp lo (pp_image b isp hasp pst es false) m1 ->
  bytes_at rsegs m1 (bv_unsigned sp + 184) (ent_mem e) -> ent_wf e ->
  Z.of_nat (length b) mod 8 = 0 -> Z.of_nat (length b) + Z.of_nat (length (enc_pod e)) <= POD_BUF_MAX ->
  bv_unsigned a0 = pp -> bv_unsigned a1 = bv_unsigned sp + 184 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m2,
     MBr sp m rest src pp lo (pp_image (b ++ enc_pod e) isp hasp pst es false) m2 -> P m2 ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (ret_pc ra) fc None m2 (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 POD_WRITE_ENT) fc None m1 (seg_rom rsegs)).
Proof.
  intros sp gp tp F fc m rest src pp lo HOK HPPA HSPA PWE Q P b isp hasp pst es e ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4
    a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1 KP FK MB HE HEW HL8 HLn Ha0 Ha1 K.
  pose proof HOK as (HS0 & HS1 & HP1 & _ & HM1 & HL0 & HSP & HPP & _ & HSROM).
  unfold POD_PROPS, MID_STACK, PARSE_STACK, FRAME_LOCALS in HP1, HM1, HSP, HSROM. unfold POD_BUF_MAX in HLn.
  pose proof HEW as (Hty & Hbody & Hsz).
  eapply evt_cut.
  { eapply PWE with (e := e) (len := Z.of_nat (length b)) (lo := lo).
    - rewrite Ha0. apply mod_16_8. exact HPPA.
    - rewrite Ha0. unfold PWE_LEN.
      apply (MBr_len_cell sp m rest src pp lo _ _ _ _ _ _ m1 MB). unfold POD_BUF_MAX. lia.
    - lia.
    - exact HL8.
    - unfold PWE_LEN. lia.
    - rewrite Ha0. apply (MBr_buf_cells sp m rest src pp lo _ _ _ _ _ _ m1 _ MB). unfold POD_BUF_MAX. lia.
    - rewrite Ha1. apply mod_16_add4; [exact HSPA | reflexivity].
    - rewrite Ha1. exact HE.
    - rewrite Hbody. lia.
    - unfold PWE_BODY. lia.
    - left. rewrite Ha0, Ha1. unfold PWE_REC. lia.
    - exact (MBr_stk_sp sp m rest src pp lo HOK _ m1 MB).
    - unfold PWE_STACK. lia.
    - intros x Hx. apply HSROM. lia.
    - left. rewrite Ha0. unfold PWE_REC. lia.
    - right. rewrite Ha1. lia.
    - exact (MBr_mem_inv sp m rest src pp lo _ m1 MB). }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> &
              MU2 & WM2 & MI2 & ST2 & HX2 & HY2).
  rewrite Ha0 in MU2, HX2, HY2. unfold PWE_STACK, PWE_LEN in MU2, HY2.
  apply K.
  - exact (MBr_pwe_post sp m rest src pp lo HOK _ _ _ _ _ _ (enc_pod e) m1 m2 MB MU2 WM2 MI2 ST2 HX2 HY2
             ltac:(unfold POD_BUF_MAX; lia)).
  - apply (KP _ m1 m2 MU2); [| exact FK].
    intros x Hx. cbn [outside]. unfold FRAME_LOCALS in Hx. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

(** ** Stores into the frame's locals *)
Ltac lenlia := rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; cbn [length]; lia.

(** The store at the goal's memory, sp-relative address a (n bytes): store_ok from [MBr], the step, the other
    bytes_at facts carried, [MBr] kept, FK kept by KW (a keeper of the form of [kept_write]), the stored bytes as
    a fact ST; the new memory is generalized. *)
Ltac fr_step HOK MB FK KW a n :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm (wa a) n = true)
        by (eapply MBr_stk_ok_w; [exact HOK | exact MB | reflexivity | lia | unfold FRAME_LOCALS; lia]);
      zstep; clear HS;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm ?w ?bs) _) =>
          let E := fresh "Ew" in
          assert (E : w = wa a) by (unfold wa; first [reflexivity | f_equal; lia]);
          replace (write_to_mem mm w bs) with (write_to_mem mm (wa a) bs) by (rewrite E; reflexivity);
          clear E;
          let MB' := fresh "MBn" in let ST := fresh "ST" in let FK' := fresh "FKn" in
          destruct (MBr_stk_store_w _ _ _ _ _ _ HOK _ mm (wa a) a bs MB eq_refl ltac:(lia)
                      ltac:(unfold MID_STACK, PARSE_STACK; lia) ltac:(unfold FRAME_LOCALS; lenlia)) as (MB' & ST & _);
          pose proof (KW mm (wa a) a bs FK eq_refl ltac:(lia) ltac:(lenlia) ltac:(lenlia)) as FK';
          keep_cells;
          clear MB FK; rename MB' into MB; rename FK' into FK;
          let m' := fresh "m" in remember (write_to_mem mm (wa a) bs) as m' eqn:Hm; clear Hm
      end
  end.

(** Bytes laid end to end. *)
Lemma bytes_at_cat3 : forall m1 A B C x y z, bytes_at rsegs m1 A x -> bytes_at rsegs m1 B y -> bytes_at rsegs m1 C z ->
  B = A + Z.of_nat (length x) -> C = B + Z.of_nat (length y) -> bytes_at rsegs m1 A (x ++ y ++ z).
Proof.
  intros m1 A B C x y z HX HY HZ -> ->. apply bytes_at_app. split; [exact HX|].
  apply bytes_at_app. split; [exact HY | exact HZ].
Qed.

Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(** ** The record after an Int property *)
Lemma seen_app_other : forall ps k v, k <> POD_PROP_PARAMS -> seen_of (ps ++ [(k, v)]) = seen_of ps.
Proof.
  intros ps k v Hk. unfold seen_of. rewrite existsb_app. cbn [existsb fst].
  rewrite (proj2 (Z.eqb_neq k POD_PROP_PARAMS) Hk). rewrite !orb_false_r. reflexivity.
Qed.

Lemma pc_wf_int : forall sh ps k v, pc_wf sh ps -> 0 <= k < 2^32 -> (length ps <= 2)%nat ->
  pc_wf sh (ps ++ [(k, PInt v)]).
Proof.
  intros sh ps k v (H1 & H2 & H3 & H4) Hk Hp.
  split; [exact H1|]. split.
  - apply Forall_app. split; [exact H2|]. constructor; [|constructor].
    cbn [fst snd pval_wf]. split; [exact Hk | exact I].
  - split.
    + unfold all_ents. rewrite flat_map_app. cbn [flat_map snd app]. rewrite !app_nil_r. exact H3.
    + rewrite length_app. cbn [length]. lia.
Qed.

(** Shape 7: the pod (pod.h:404) is the whole property, and key 0 is not SPA_PROP_params. *)
Lemma shape7_image : forall ps,
  pp_image (pc_buf (PbCut 7 ps None) ++ enc_pod (Ent 4 4 (le32 0))) (is_props (PodRec 7 ps None))
    (has_params (PodRec 7 ps None)) (params_struct (PodRec 7 ps None)) (pc_ents (PbCut 7 ps None)) false
  = pc_image (PbCut 7 (ps ++ [(0, PInt 0)]) None).
Proof.
  intros ps. unfold pc_image. cbn [pc_shape pc_props].
  rewrite <- pc_buf_prop.
  assert (FP : first_params (ps ++ [(0, PInt 0)]) = first_params ps)
    by (rewrite first_params_app; destruct (first_params ps); reflexivity).
  unfold has_params, params_struct, pc_ents. cbn [p_props pc_props pc_open]. rewrite FP. reflexivity.
Qed.

Lemma ent40_wf : ent_wf (Ent 4 4 (le32 0)).
Proof. unfold ent_wf. cbn [e_type e_size e_body]. split; [lia | split; [reflexivity | lia]]. Qed.

(** ** The walk *)
Local Ltac refute T := exfalso; zify_cond T; rewrite ?lnot_mod, ?pred_opp_mod in T by lia; lia.
Local Ltac tk T := if_cases T; [ | refute T ].

Section Shape7.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl src pp lo cap : Z).
Hypothesis HOK : BOK sp rest src pp lo.
Hypothesis HPPA : pp mod 16 = 0.
Hypothesis HSPA : bv_unsigned sp mod 16 = 0.
Hypothesis MSET : memset_c.memset_contract.
Hypothesis PWE : pod_write_ent_c.pod_write_ent_contract.

(** 0x132d0, sel read: the shape test, memset(e->body), e->type = e->size = 4, pod_write_ent, the latch. *)
Lemma shape7_from_sel : forall np ps r (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) m1,
  suffix rest r -> pc_wf 7 ps -> 0 <= np < 4 -> (length ps < Z.to_nat np)%nat ->
  MBr sp m rest src pp lo (pc_image (PbCut 7 ps None)) m1 -> CFIX sp pp cap m1 -> CPROP sp fl 7 np m1 ->
  evt rsegs (PROPL sp gp tp F fc m rest fl src pp lo cap 7 np (length ps) (ps ++ [(0, PInt 0)]) r)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) (Z_to_bv 64 (Z.b2z (seen_of ps)))
             a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (Z.of_nat (length ps)))
             (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 MULT10) (Z_to_bv 64 (Z.lnot pp)) (Z_to_bv 64 np)
             (Z_to_bv 64 (cur rest src r)) (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) (Z_to_bv 64 S0V)
             (Z_to_bv 64 7) (Z_to_bv 64 4) t3 t4 t5 t6)
        F (Z_to_bv 64 0x132d0) fc None m1 (seg_rom rsegs)).
Proof.
  intros np ps r ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 m1 Hsuf Hwf Hnp Hlt MB CF CP.
  pose proof HOK as (HS0 & HS1 & HP1 & _ & HM1 & HL0 & HSP & HPP & _ & _).
  unfold POD_PROPS, MID_STACK, PARSE_STACK, FRAME_LOCALS in HP1, HM1, HSP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with 18446744073709551616 in SPR.
  destruct (pc_buf_cap 7 ps Hwf ltac:(lia)) as [HB8 HD8].
  change (pc_image (PbCut 7 ps None))
    with (pp_image (pc_buf (PbCut 7 ps None)) (is_props (PodRec 7 ps None)) (has_params (PodRec 7 ps None))
            (params_struct (PodRec 7 ps None)) (pc_ents (PbCut 7 ps None)) false) in MB.
  pose proof CP as (_ & _ & C90). pose proof (cell8_read _ _ _ C90) as R90.
  assert (FK : FS sp pp fl cap 7 np m1) by (split; assumption).
  pose proof (FS_kept sp pp fl cap 7 np) as KP.
  clear C90 CF CP.
  (* 0x132d0 ld a1,0x90(sp); 0x132d4 bne a1,s10 (shape 7: not taken) *)
  zstep. clear R90. zstep. if_cases E7; [exfalso; zify_cond E7; lia|].
  (* 0x132d8 addi a2,zero,0x60; addi a0,sp,0xc0; mv a1,zero; mv s10,a7; 0x132e8 jal memset *)
  zstep. zstep. zstep. zstep. zstep.
  eapply (mset_at sp gp tp F fc m rest src pp lo HOK MSET) with (o := 192) (n := 96%nat).
  { exact KP. } { exact FK. } { exact MB. }
  { rewrite unsigned_lit by lia. reflexivity. }
  { first [reflexivity | rewrite unsigned_lit by lia; reflexivity]. }
  { first [reflexivity | rewrite unsigned_lit by lia; reflexivity]. }
  { lia. } { unfold FRAME_LOCALS. lia. }
  intros u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m2 MB2 FK2 HZ.
  fix_ret.
  (* 0x132ec sw s11,0xb8(sp); 0x132f0 sw s11,0xbc(sp) *)
  fr_step HOK MB2 FK2 (kept_write _ _ KP) (bv_unsigned sp + 184) 4%nat.
  fr_step HOK MB2 FK2 (kept_write _ _ KP) (bv_unsigned sp + 188) 4%nat.
  (* e = Ent 4 4 (le32 0) at sp + 0xb8 *)
  lazymatch goal with
  | S1 : bytes_at rsegs ?mm (bv_unsigned sp + 184) ?x, S2 : bytes_at rsegs ?mm (bv_unsigned sp + 188) ?y,
    S3 : bytes_at rsegs ?mm (bv_unsigned sp + 192) ?z |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HE : bytes_at rsegs mm (bv_unsigned sp + 184) (ent_mem (Ent 4 4 (le32 0))))
        by (eapply bytes_at_ext; [apply (bytes_at_cat3 mm _ _ _ x y z S1 S2 S3); lenlia | vm_compute; reflexivity]);
      clear S1 S2 S3
  end.
  (* 0x132f4 addi a1,sp,0xb8; 0x132f8 mv a0,s8; 0x132fc jal pod_write_ent *)
  zstep. zstep. zstep.
  eapply (pwe_at sp gp tp F fc m rest src pp lo HOK HPPA HSPA PWE).
  { exact (kept_frame _ _ KP). } { exact FK2. } { exact MB2. } { exact HE. } { exact ent40_wf. }
  { apply (proj2 (Z.mod_divide _ 8 ltac:(lia))). exact HD8. }
  { assert (Hn : length (enc_pod (Ent 4 4 (le32 0))) = 16%nat) by (vm_compute; reflexivity).
    rewrite Hn. unfold POD_BUF_MAX. lia. }
  { rewrite unsigned_lit by lia. reflexivity. }
  { rewrite unsigned_lit by lia. reflexivity. }
  intros v0 v1 v2 va0 va1 va2 va3 va4 va5 va6 va7 v3 v4 v5 v6 m4 MB4 FK4.
  fix_ret.
  (* 0x13300 mv a7,s10; 0x13304 addi s10,zero,7; 0x13308 j 0x13fb0 *)
  zstep. zstep. zstep.
  destruct FK4 as (CF4 & CP4).
  apply evt_done. unfold PROPL. do 16 eexists.
  split; [rewrite (seen_app_other ps 0 (PInt 0)) by (unfold POD_PROP_PARAMS; lia); reflexivity|].
  split; [rewrite <- shape7_image; exact MB4|].
  split; [exact CF4|]. split; [exact CP4|]. split; [exact Hsuf|].
  split; [apply pc_wf_int; [exact Hwf | lia | lia]|]. split; [exact Hnp|].
  rewrite length_app. cbn [length]. split; lia.
Qed.

(** 0x132a8 -> 0x13fb0: sel = fuzz_u8 (fuzz.h:39-43), then [shape7_from_sel]. *)
Lemma shape7_walk : forall np ps r ms,
  PROPH sp gp tp F fc m rest fl src pp lo cap 7 np ps r ms ->
  evt rsegs (PROPL sp gp tp F fc m rest fl src pp lo cap 7 np (length ps) (ps ++ [(0, PInt 0)]) (snd (fuzz_u8 r))) ms.
Proof.
  intros np ps r ms
    (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & t3 & t4 & t5 & t6 & m1 & -> &
     MB & CF & CP & Hsuf & Hwf & Hnp & Hlt).
  pose proof HOK as (HS0 & HS1 & HP1 & HDJ & HM1 & HL0 & HSP & HPP & HROM & HSROM).
  pose proof Hsuf as [j [Hj Er]].
  assert (Hcur : cur rest src r = src + Z.of_nat j) by (unfold cur; rewrite Er, length_skipn; lia).
  assert (Hrl : Z.of_nat (length r) = Z.of_nat (length rest) - Z.of_nat j) by (rewrite Er, length_skipn; lia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with 18446744073709551616 in SPR.
  unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in HM1, HSP.
  unfold PROP_HEAD.
  (* 0x132a8 beqz s2 *)
  zstep. if_cases E0; zify_cond E0.
  - destruct r as [|b r1]; [|cbn [length] in E0, Hrl; lia].
    (* 0x132cc mv a0,zero *)
    zstep. cbn [fuzz_u8 fst snd].
    eapply shape7_from_sel; eassumption.
  - destruct r as [|b r1]; [cbn [length] in E0, Hrl; lia|].
    assert (HB : ov_read_bytes rsegs m1 (wa (src + Z.of_nat j)) 1 = Some [b])
      by (eapply MBr_byte; [exact MB | symmetry; exact Er]).
    (* 0x132ac addi a1,s6,1; addi a0,zero,1; bltu a0,a1 (else trap) *)
    zstep. zstep. zstep. tk T0.
    (* 0x132bc lbu a0,0(s6); addi s2,s2,-1; mv s6,a1; j 0x132d0 *)
    zstep. zstep. zstep. zstep.
    cbn [fuzz_u8 fst snd].
    replace (Z.of_nat (length (b :: r1)) + -1) with (Z.of_nat (length r1)) by (cbn [length]; lia).
    replace (cur rest src (b :: r1) + 1) with (cur rest src r1) by (unfold cur; cbn [length]; lia).
    eapply shape7_from_sel; try eassumption.
    exists (S j). split.
    + destruct (Nat.le_gt_cases (S j) (length rest)) as [H|H]; [exact H|].
      exfalso. rewrite skipn_all2 in Er by lia. discriminate.
    + rewrite <- (skipn_skipn 1 j). rewrite <- Er. reflexivity.
Qed.

End Shape7.

Theorem shape7_holds : memset_c.memset_contract -> pod_write_ent_c.pod_write_ent_contract ->
  forall sp gp tp F fc m rest fl src pp lo cap, BOK sp rest src pp lo -> pp mod 16 = 0 -> bv_unsigned sp mod 16 = 0 ->
  forall np ps r ms, PROPH sp gp tp F fc m rest fl src pp lo cap 7 np ps r ms ->
  evt rsegs (PROPL sp gp tp F fc m rest fl src pp lo cap 7 np (length ps) (ps ++ [fst (prop_step 7 r)])
               (snd (prop_step 7 r))) ms.
Proof.
  intros MSET PWE sp gp tp F fc m rest fl src pp lo cap HOK HPPA HSPA np ps r ms HP.
  assert (EP : prop_step 7 r = ((0, PInt 0), snd (fuzz_u8 r)))
    by (unfold prop_step; destruct (fuzz_u8 r); reflexivity).
  rewrite EP. cbn [fst snd].
  exact (shape7_walk sp gp tp F fc m rest fl src pp lo cap HOK HPPA HSPA MSET PWE np ps r ms HP).
Qed.
