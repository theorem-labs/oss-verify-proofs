(** One property of the object, 0x130cc -> 0x13e68 of the plain image (pod.h:399-438): the selector byte, then
    for a Struct object the value pod `Int 0` ([PropPath.s7_ok]); otherwise the key and the flags, `first` and
    `seen_params`, and either an Int pod ([PropPath.int_ok]) or a params Struct with its pods
    ([PropLoop.str_ok]). [prop_holds] is the statement RoleBuild/Cut.v fixes for this piece. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c
  memset_c memcpy_c strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleBuild Require Import Facts Cut EntCut Write Post
  PropKit PropPath PropLoop.
Import ListNotations.
Open Scope Z_scope.

(** prop_step after its selector byte (Pod/Model.v), for an object that is not a Struct. *)
Definition ptail (sel : Z) (r1 : list byte) : (Z * pval) * list byte :=
  if sel mod 4 =? 0 then ((POD_PROP_VOLUME, PInt 7), r1)
  else if Z.testbit sel 4 then ((POD_PROP_PARAMS, PInt 7), r1)
  else ((POD_PROP_PARAMS, PStruct (fst (ents_loop (Z.to_nat (fst (fuzz_u8 r1) mod 33)) (snd (fuzz_u8 r1))))),
        snd (ents_loop (Z.to_nat (fst (fuzz_u8 r1) mod 33)) (snd (fuzz_u8 r1)))).

Lemma prop_step_tail : forall sh r, prop_step sh r =
  if sh =? 7 then ((0, PInt 0), snd (fuzz_u8 r)) else ptail (fst (fuzz_u8 r)) (snd (fuzz_u8 r)).
Proof.
  intros sh r. unfold prop_step, ptail. destruct (fuzz_u8 r) as [sel r1]. cbn [fst snd].
  destruct (sh =? 7); [reflexivity|]. destruct (sel mod 4 =? 0); [reflexivity|].
  destruct (Z.testbit sel 4); [reflexivity|]. destruct (fuzz_u8 r1) as [c r2]. cbn [fst snd].
  destruct (ents_loop (Z.to_nat (c mod 33)) r2). reflexivity.
Qed.

(** `snez a2,a1 ; seqz a3,t3 ; and a2,a2,a3`: `first`, the key is SPA_PROP_params and none was seen yet
    (pod.h:409). *)
Lemma first_word0 : forall a (s : bool), a = 0 ->
  Z_to_bv 64 (Z.land (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 a)))
                     (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.b2z s)) 1))) = Z_to_bv 64 0.
Proof. intros a s ->. destruct s; reflexivity. Qed.

Lemma first_word1 : forall a (s : bool), 0 < a < 4 ->
  Z_to_bv 64 (Z.land (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 a)))
                     (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.b2z s)) 1))) = Z_to_bv 64 (Z.b2z (negb s)).
Proof. intros a s Ha. unfold v_sltu, c_ltu. rewrite (ltu_T 0 a) by lia. destruct s; reflexivity. Qed.

Section OneProp.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.
Hypothesis MSET : memset_contract.
Hypothesis ENT : rb_ent_contract.
Hypothesis SW : S_write sp gp tp F fc m rest fl src pp lo.
Hypothesis HSPA : bv_unsigned sp mod 16 = 0.
Variables (sh np : Z) (ps : list (Z * pval)).
Hypothesis HWF : pc_wf sh ps.
Hypothesis HPS : (length ps <= 2)%nat.

Abbreviation L := (Lp sh ps).
Abbreviation B := (bp sh ps).
Abbreviation IM := (IMq sh ps).
Abbreviation PQ0 := (PQ sp gp tp F fc m rest fl src pp lo sh np ps).
Abbreviation XB0 := (XB fl pp sh np).

(** ** 0x131f8 -> 0x13e68: the key and the flags (pod.h:407-408), `first` and `seen_params` (pod.h:409-411),
       then the property's value *)
Lemma kf_ok : forall K sel r1 (ra t1 a3 a4 a5 s5 s6 t4 t5 t6 : word) m1,
  sh <> 7 -> 0 <= sel < 256 -> suffix rest r1 ->
  (K = 65539 /\ sel mod 4 = 0) \/ (K = 524289 /\ sel mod 4 <> 0) ->
  MQ sp m rest src pp lo ((0x48, Z.of_nat (length ps)) :: XB0) (IM B) L m1 ->
  evt rsegs (PQ0 (fst (ptail sel r1)) (snd (ptail sel r1)))
    (MS (mkR ra sp gp tp (Z_to_bv 64 (-16385)) t1 (Z_to_bv 64 np)
             (Z_to_bv 64 (bv_unsigned sp + 296)) (Z_to_bv 64 (bv_unsigned sp + 240))
             (Z_to_bv 64 sel) (Z_to_bv 64 (sel mod 4)) (Z_to_bv 64 K) a3 a4 a5 (Z_to_bv 64 (pp + 16384))
             (Z_to_bv 64 (-16381)) (Z_to_bv 64 MULT10) (Z_to_bv 64 (cur rest src r1))
             (Z_to_bv 64 (Z.of_nat (length r1))) s5 s6 (Z_to_bv 64 L) (Z_to_bv 64 95)
             (Z_to_bv 64 (Z.b2z (sh =? 7))) (Z_to_bv 64 10) (Z_to_bv 64 pp) (Z_to_bv 64 (Z.b2z (seen_of ps)))
             t4 t5 t6)
        F (Z_to_bv 64 0x131f8) fc None m1 (seg_rom rsegs)).
Proof.
  intros K sel r1 ra t1 a3 a4 a5 s5 s6 t4 t5 t6 m1 H7 Hsel Hs HK MQ0.
  pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  destruct (Lp_rng sh ps HWF HPS) as (LP1 & LP2). pose proof (Lp_def sh ps) as LPD.
  assert (HKr : K = 65539 \/ K = 524289) by (destruct HK as [[-> _] | [-> _]]; [left | right]; reflexivity).
  (* 0x131f8 add s7,s11,s7 ; srli a3,a2,0x10 ; 0x13200 .. 0x1320c: the key *)
  step. step.
  sbq (Lp sh ps). sbq (L + 1). sbq (L + 2). sbq (L + 3). c4 (Lp sh ps).
  lazymatch goal with MQH : MQ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite (lbkey K HKr) in MQH end.
  (* 0x13210 ld s7,0(a6) ; addi s7,s7,4 ; add a2,s7,a7 ; sd s7,0(a6) *)
  ldl. step. step. sdl. fput.
  (* 0x13220 bltu a2,t0 ; add s7,s11,s7 ; 0x13228 .. 0x13234: the flags 0 *)
  step. capF. step.
  sbq (L + 4). sbq (L + 4 + 1). sbq (L + 4 + 2). sbq (L + 4 + 3). c4 (L + 4). lbq 0.
  ldl. step. sdl. fput.
  (* 0x13244 mv a4,t3 ; beqz a1,8 *)
  step. step.
  destruct HK as [[-> E4] | [-> E4]].
  - (* SPA_PROP_VOLUME: 0x13250 snez a2,a1 ; seqz a3,t3 ; and a2,a2,a3 ; sd a2,0x70(sp) *)
    brT. step. step. step.
    rewrite (first_word0 (sel mod 4) (seen_of ps) E4).
    sdc 0x70 0.
    (* 0x13260 add a2,s7,a7 ; 0x13264 beqz a1: the Int pod *)
    step. step. brT.
    unfold ptail. rewrite (proj2 (Z.eqb_eq (sel mod 4) 0) E4). cbn [fst snd].
    eapply int_ok with (K := 65539) (f := false).
    all: first [ eassumption | lia
               | (apply wf_snoc; [exact HWF | exact HPS | cbn; split; [lia | exact I] | apply Forall_nil])
               | (rewrite seen_snoc; cbn [fst]; replace (65539 =? POD_PROP_PARAMS) with false by reflexivity;
                  rewrite orb_false_r; reflexivity)
               | (symmetry; apply img_same; apply fp_other; cbn [fst]; unfold POD_PROP_PARAMS; lia) ].
  - (* SPA_PROP_params: 0x1324c addi a4,zero,1 ; snez ; seqz ; and ; sd a2,0x70(sp) *)
    brF. step. step. step. step.
    rewrite (first_word1 (sel mod 4) (seen_of ps)) by lia.
    change (negb (seen_of ps)) with (first_of ps).
    sdc 0x70 (Z.b2z (first_of ps)).
    (* 0x13260 add a2,s7,a7 ; beqz a1 ; andi a0,a0,0x10 ; bnez a0 *)
    step. step. brF. step. rewrite (land16 sel) by lia. step.
    destruct (Z.testbit sel 4) eqn:EB.
    + (* the Int pod *)
      brT.
      unfold ptail. replace (sel mod 4 =? 0) with false by (symmetry; apply Z.eqb_neq; exact E4).
      rewrite EB. cbn [fst snd].
      eapply int_ok with (K := 524289) (f := first_of ps).
      all: first [ eassumption | lia
                 | (apply wf_snoc; [exact HWF | exact HPS | cbn; split; [lia | exact I] | apply Forall_nil])
                 | (rewrite seen_snoc; cbn [fst]; rewrite Z.eqb_refl, orb_true_r; reflexivity)
                 | (unfold first_of; destruct (seen_of ps) eqn:ES; cbn [negb];
                    [symmetry; apply img_same; apply fp_seen; exact ES | apply img_int_first; assumption]) ].
    + (* a params Struct *)
      brF.
      unfold ptail. replace (sel mod 4 =? 0) with false by (symmetry; apply Z.eqb_neq; exact E4).
      rewrite EB. cbn [fst snd].
      eapply str_ok.
      all: first [ eassumption | lia ].
Qed.

(** ** 0x130e4 -> 0x131f8: an object that is not a Struct; the selector's two low bits pick the key *)
Lemma ns_ok : forall sel r1 (ra t1 a2 a3 a4 a5 s5 s6 s7 t4 t5 t6 : word) m1,
  sh <> 7 -> 0 <= sel < 256 -> suffix rest r1 ->
  MQ sp m rest src pp lo XB0 (IM B) L m1 ->
  evt rsegs (PQ0 (fst (ptail sel r1)) (snd (ptail sel r1)))
    (MS (mkR ra sp gp tp (Z_to_bv 64 (-16385)) t1 (Z_to_bv 64 np)
             (Z_to_bv 64 (bv_unsigned sp + 296)) (Z_to_bv 64 (bv_unsigned sp + 240))
             (Z_to_bv 64 sel) (Z_to_bv 64 (Z.of_nat (length ps))) a2 a3 a4 a5 (Z_to_bv 64 (pp + 16384))
             (Z_to_bv 64 (-16381)) (Z_to_bv 64 MULT10) (Z_to_bv 64 (cur rest src r1))
             (Z_to_bv 64 (Z.of_nat (length r1))) s5 s6 s7 (Z_to_bv 64 95) (Z_to_bv 64 (Z.b2z (sh =? 7)))
             (Z_to_bv 64 10) (Z_to_bv 64 pp) (Z_to_bv 64 (Z.b2z (seen_of ps))) t4 t5 t6)
        F (Z_to_bv 64 0x130e4) fc None m1 (seg_rom rsegs)).
Proof.
  intros sel r1 ra t1 a2 a3 a4 a5 s5 s6 s7 t4 t5 t6 m1 H7 Hsel Hs MQ0.
  pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  destruct (Lp_rng sh ps HWF HPS) as (LP1 & LP2). pose proof (Lp_def sh ps) as LPD.
  (* 0x130e4 ld s7,0(a6) ; 0x130e8 add a2,s7,a7 ; 0x130ec beqz s9 *)
  ldl. step. step.
  assert (B7 : bv_eqb (Z_to_bv 64 (Z.b2z (sh =? 7))) (Z_to_bv 64 0) = true)
    by (replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact H7); reflexivity).
  rewrite B7; cbv iota. clear B7.
  (* 0x131e0 sd a1,0x48(sp) ; 0x131e4 andi a1,a0,3 ; 0x131e8 bltu a2,t0 *)
  sdc 0x48 (Z.of_nat (length ps)). step. rewrite (land3 sel) by lia. step. capF.
  (* 0x131ec ld a2,0x20(sp) ; 0x131f0 bnez a1,8 *)
  ldc 0x20. step.
  destruct (Z.eq_dec (sel mod 4) 0) as [E4 | E4].
  - (* 0x131f4 ld a2,0x10(sp): SPA_PROP_VOLUME *)
    brF. ldc 0x10.
    eapply kf_ok with (K := 65539).
    all: first [ eassumption | (left; split; [reflexivity | exact E4]) | lia ].
  - brT.
    eapply kf_ok with (K := 524289).
    all: first [ eassumption | (right; split; [reflexivity | exact E4]) | lia ].
Qed.

(** The memory at the property loop's head, as this piece carries it. *)
Lemma mq_head : forall m1, MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 -> CFIX sp pp m1 ->
  cell8 m1 (bv_unsigned sp) fl -> cell8 m1 (bv_unsigned sp + 0x8) np ->
  cell8 m1 (bv_unsigned sp + 0x18) (Z.b2z (sh =? 7)) ->
  MQ sp m rest src pp lo XB0 (IM B) L m1.
Proof.
  intros m1 MB (F10 & F20 & F38 & F40 & F50 & F60 & F68 & F80) C0 C8 C18.
  destruct (Lp_rng sh ps HWF HPS) as (LP1 & LP2). pose proof (Lp_def sh ps) as LPD.
  split; [exact MB|]. split.
  - rewrite <- (Z.add_0_r (bv_unsigned sp)) in C0. unfold FC, XB.
    repeat (apply Forall_cons; [unfold cok; cbn [fst snd]; split; [lia|]; split; [lia | assumption] |]).
    apply Forall_nil.
  - eapply len_bytes_of; [exact MB |]. change (pc_buf (PbCut sh ps None)) with B. lia.
Qed.

(** ** 0x130cc -> 0x13e68 *)
Lemma prop_step_s7 : forall r, sh = 7 -> prop_step sh r = ((0, PInt 0), snd (fuzz_u8 r)).
Proof.
  intros r E7. rewrite prop_step_tail. replace (sh =? 7) with true by (symmetry; apply Z.eqb_eq; exact E7).
  reflexivity.
Qed.

Lemma prop_step_ns : forall r, sh <> 7 -> prop_step sh r = ptail (fst (fuzz_u8 r)) (snd (fuzz_u8 r)).
Proof.
  intros r E7. rewrite prop_step_tail. replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact E7).
  reflexivity.
Qed.

Lemma prop_ok : forall r ms, PROPH sp gp tp F fc m rest fl src pp lo sh np ps r ms ->
  evt rsegs (PQ0 (fst (prop_step sh r)) (snd (prop_step sh r))) ms.
Proof.
  intros r ms HP.
  destruct HP as (ra & t1 & a0 & a2 & a3 & a4 & a5 & s5 & s6 & s7 & t4 & t5 & t6 & m1 &
                  Ems & MB & CF & C0 & C8 & C18 & Hs & Hw).
  subst ms.
  pose proof (mq_head m1 MB CF C0 C8 C18) as MQ0. clear MB CF C0 C8 C18.
  pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  pose proof (suffix_len rest r Hs) as Hlr.
  assert (W0 : pc_wf sh (ps ++ [(0, PInt 0)]))
    by (apply wf_snoc; [exact HWF | exact HPS | cbn; split; [lia | exact I] | apply Forall_nil]).
  unfold PROP_HEAD, POD_LEN_OFF, S8V, S10V.
  (* 0x130cc beqz s4 *)
  step.
  destruct r as [|x r1].
  - (* no byte left: 0x130e0 mv a0,zero, the selector is 0 *)
    brT. step.
    destruct (Z.eq_dec sh 7) as [E7 | E7].
    + rewrite (prop_step_s7 [] E7). cbn [fuzz_u8 fst snd].
      eapply s7_ok; first [eassumption | exact E7].
    + rewrite (prop_step_ns [] E7). cbn [fuzz_u8 fst snd].
      eapply ns_ok; first [eassumption | lia].
  - change (length (x :: r1)) with (S (length r1)) in *.
    brF.
    (* 0x130d0 lbu a0,0(s3) ; addi s3,s3,1 ; addi s4,s4,-1 ; j *)
    assert (HRx : ov_read_bytes rsegs m1 (wa (cur rest src (x :: r1))) 1 = Some [x])
      by (eapply mq_byte; eassumption).
    step. clear HRx. step. step. step.
    rewrite (cur_cons rest src x r1).
    replace (Z.of_nat (S (length r1)) + -1) with (Z.of_nat (length r1)) by lia.
    pose proof (byte_range x) as Hx.
    pose proof (suffix_skipn rest (x :: r1) 1 Hs) as Hs1. cbn [skipn] in Hs1.
    destruct (Z.eq_dec sh 7) as [E7 | E7].
    + rewrite (prop_step_s7 (x :: r1) E7). cbn [fuzz_u8 fst snd].
      eapply s7_ok; first [eassumption | exact E7].
    + rewrite (prop_step_ns (x :: r1) E7). cbn [fuzz_u8 fst snd].
      change (zxb x) with (Z_to_bv 64 (bv_unsigned x)).
      eapply ns_ok; first [eassumption | lia].
Qed.

End OneProp.

(** 0x130cc -> 0x13e68: one property of the object (pod.h:399-438), the pod loop of a params Struct included. *)
Theorem prop_holds : forall sp gp tp F fc m rest fl src pp lo,
  memset_c.memset_contract -> memcpy_c.memcpy_contract -> strlen_c.strlen_contract ->
  EntCut.rb_ent_contract ->
  Cut.S_write sp gp tp F fc m rest fl src pp lo ->
  Cut.S_prop sp gp tp F fc m rest fl src pp lo.
Proof.
  intros sp gp tp F fc m rest fl src pp lo MSET MCPY STRL ENT SW HOK sh np ps r ms HP Hlt H3 HSPA.
  assert (HPS : (length ps <= 2)%nat) by lia.
  assert (HWF : pc_wf sh ps).
  { destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw).
    exact Hw. }
  eapply prop_ok; eassumption.
Qed.
