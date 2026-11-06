(** One property of the object, 0x13334 -> 0x140e4 of the plain image (pod.h:399-438): the selector byte, then
    for a Struct object the value pod `Int 0` ([PropPath.s7_ok]); otherwise the key and the flags, `first` and
    `seen_params`, and either an Int pod ([PropPath.int_ok]) or a params Struct with its pods
    ([PropLoop.str_ok]). [prop_holds] is the statement RateBuild/Cut.v fixes for this piece. Ported from
    reac-pw/fuzz_role's Prog/RoleBuild/Prop.v (role 0x130cc -> 0x13e68) at
    rate's registers, frame cells (the property index at 0x78, `first` at 0xa0, the header run [sp, sp + 0x38)) and
    pcs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c
  memset_c memcpy_c strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild Require Import Facts Cut EntCut Write Post
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
Variables (rest : list byte) (fl mask buflen b3 b4 b5 b6 src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.
Hypothesis MSET : memset_contract.
Hypothesis ENT : rb_ent_contract.
Hypothesis SW : S_write sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo.
Hypothesis HSPA : bv_unsigned sp mod 16 = 0.
Variables (sh np : Z) (ps : list (Z * pval)).
Hypothesis HWF : pc_wf sh ps.
Hypothesis HPS : (length ps <= 2)%nat.

Abbreviation L := (Lp sh ps).
Abbreviation B := (bp sh ps).
Abbreviation IM := (IMq sh ps).
Abbreviation PQ0 := (PQ sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo sh np ps).
Abbreviation XB0 := (XB fl mask buflen b3 b4 b5 b6 pp sh np).

(** ** 0x13460 -> 0x140e4: the key and the flags (pod.h:407-408), `first` and `seen_params` (pod.h:409-411),
       then the property's value *)
Lemma kf_ok : forall K sel r1 (ra t1 a3 a4 s7 s8 s9 t4 t5 t6 : word) m1,
  sh <> 7 -> 0 <= sel < 256 -> suffix rest r1 ->
  (K = 65539 /\ sel mod 4 = 0) \/ (K = 524289 /\ sel mod 4 <> 0) ->
  MQ sp m rest src pp lo ((0x78, Z.of_nat (length ps)) :: XB0) (IM B) L m1 ->
  evt rsegs (PQ0 (fst (ptail sel r1)) (snd (ptail sel r1)))
    (MS (mkR ra sp gp tp (Z_to_bv 64 (-16385)) t1 (Z_to_bv 64 np) (Z_to_bv 64 95) (Z_to_bv 64 pp)
             (Z_to_bv 64 sel) (Z_to_bv 64 (sel mod 4)) (Z_to_bv 64 K) a3 a4 (Z_to_bv 64 (Z.b2z (sh =? 7)))
             (Z_to_bv 64 (pp + 16384)) (Z_to_bv 64 (-16381))
             (Z_to_bv 64 L) (Z_to_bv 64 10) (Z_to_bv 64 MULT10) (Z_to_bv 64 (cur rest src r1))
             (Z_to_bv 64 (Z.of_nat (length r1))) s7 s8 s9
             (Z_to_bv 64 (bv_unsigned sp + 0x158)) (Z_to_bv 64 (bv_unsigned sp + 0x120))
             (Z_to_bv 64 (Z.b2z (seen_of ps))) t4 t5 t6)
        F (Z_to_bv 64 0x13460) fc None m1 (seg_rom rsegs)).
Proof.
  intros K sel r1 ra t1 a3 a4 s7 s8 s9 t4 t5 t6 m1 H7 Hsel Hs HK MQ0.
  pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  destruct (Lp_rng sh ps HWF HPS) as (LP1 & LP2). pose proof (Lp_def sh ps) as LPD.
  assert (HKr : K = 65539 \/ K = 524289) by (destruct HK as [[-> _] | [-> _]]; [left | right]; reflexivity).
  (* 0x13460 add s2,s1,s2 ; srli a3,a2,0x10 ; 0x13468 .. 0x13474: the key *)
  step. step.
  sbq (Lp sh ps). sbq (L + 1). sbq (L + 2). sbq (L + 3). c4 (Lp sh ps).
  lazymatch goal with MQH : MQ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite (lbkey K HKr) in MQH end.
  (* 0x13478 ld s2,0(a6) ; addi s2,s2,4 ; add a2,s2,a7 ; sd s2,0(a6) *)
  ldl. step. step. sdl. fput.
  (* 0x13488 bltu a2,t0 ; add s2,s1,s2 ; 0x13490 .. 0x1349c: the flags 0 *)
  step. capF. step.
  sbq (L + 4). sbq (L + 4 + 1). sbq (L + 4 + 2). sbq (L + 4 + 3). c4 (L + 4). lbq 0.
  ldl. step. sdl. fput.
  (* 0x134ac mv a4,t3 ; beqz a1,8 *)
  step. step.
  destruct HK as [[-> E4] | [-> E4]].
  - (* SPA_PROP_VOLUME: 0x134b8 snez a2,a1 ; seqz a3,t3 ; and a2,a2,a3 ; sd a2,0xa0(sp) *)
    brT. step. step. step.
    rewrite (first_word0 (sel mod 4) (seen_of ps) E4).
    sdc 0xa0 0.
    (* 0x134c8 add a2,s2,a7 ; 0x134cc beqz a1: the Int pod *)
    step. step. brT.
    unfold ptail. rewrite (proj2 (Z.eqb_eq (sel mod 4) 0) E4). cbn [fst snd].
    eapply int_ok with (K := 65539) (f := false).
    all: first [ eassumption | lia
               | (apply wf_snoc; [exact HWF | exact HPS | cbn; split; [lia | exact I] | apply Forall_nil])
               | (rewrite seen_snoc; cbn [fst]; replace (65539 =? POD_PROP_PARAMS) with false by reflexivity;
                  rewrite orb_false_r; reflexivity)
               | (symmetry; apply img_same; apply fp_other; cbn [fst]; unfold POD_PROP_PARAMS; lia) ].
  - (* SPA_PROP_params: 0x134b4 addi a4,zero,1 ; snez ; seqz ; and ; sd a2,0xa0(sp) *)
    brF. step. step. step. step.
    rewrite (first_word1 (sel mod 4) (seen_of ps)) by lia.
    change (negb (seen_of ps)) with (first_of ps).
    sdc 0xa0 (Z.b2z (first_of ps)).
    (* 0x134c8 add a2,s2,a7 ; beqz a1 ; andi a0,a0,0x10 ; bnez a0 *)
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

(** ** 0x1334c -> 0x13460: an object that is not a Struct; the selector's two low bits pick the key *)
Lemma ns_ok : forall sel r1 (ra t1 a2 a3 a4 s2 s7 s8 s9 t4 t5 t6 : word) m1,
  sh <> 7 -> 0 <= sel < 256 -> suffix rest r1 ->
  MQ sp m rest src pp lo XB0 (IM B) L m1 ->
  evt rsegs (PQ0 (fst (ptail sel r1)) (snd (ptail sel r1)))
    (MS (mkR ra sp gp tp (Z_to_bv 64 (-16385)) t1 (Z_to_bv 64 np) (Z_to_bv 64 95) (Z_to_bv 64 pp)
             (Z_to_bv 64 sel) (Z_to_bv 64 (Z.of_nat (length ps))) a2 a3 a4 (Z_to_bv 64 (Z.b2z (sh =? 7)))
             (Z_to_bv 64 (pp + 16384)) (Z_to_bv 64 (-16381))
             s2 (Z_to_bv 64 10) (Z_to_bv 64 MULT10) (Z_to_bv 64 (cur rest src r1))
             (Z_to_bv 64 (Z.of_nat (length r1))) s7 s8 s9
             (Z_to_bv 64 (bv_unsigned sp + 0x158)) (Z_to_bv 64 (bv_unsigned sp + 0x120))
             (Z_to_bv 64 (Z.b2z (seen_of ps))) t4 t5 t6)
        F (Z_to_bv 64 0x1334c) fc None m1 (seg_rom rsegs)).
Proof.
  intros sel r1 ra t1 a2 a3 a4 s2 s7 s8 s9 t4 t5 t6 m1 H7 Hsel Hs MQ0.
  pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  destruct (Lp_rng sh ps HWF HPS) as (LP1 & LP2). pose proof (Lp_def sh ps) as LPD.
  (* 0x1334c ld s2,0(a6) ; 0x13350 add a2,s2,a7 ; 0x13354 beqz a5 *)
  ldl. step. step.
  assert (B7 : bv_eqb (Z_to_bv 64 (Z.b2z (sh =? 7))) (Z_to_bv 64 0) = true)
    by (replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact H7); reflexivity).
  rewrite B7; cbv iota. clear B7.
  (* 0x13448 sd a1,0x78(sp) ; 0x1344c andi a1,a0,3 ; 0x13450 bltu a2,t0 *)
  sdc 0x78 (Z.of_nat (length ps)). step. rewrite (land3 sel) by lia. step. capF.
  (* 0x13454 ld a2,0x50(sp) ; 0x13458 bnez a1,8 *)
  ldc 0x50. step.
  destruct (Z.eq_dec (sel mod 4) 0) as [E4 | E4].
  - (* 0x1345c ld a2,0x38(sp): SPA_PROP_VOLUME *)
    brF. ldc 0x38.
    eapply kf_ok with (K := 65539).
    all: first [ eassumption | (left; split; [reflexivity | exact E4]) | lia ].
  - brT.
    eapply kf_ok with (K := 524289).
    all: first [ eassumption | (right; split; [reflexivity | exact E4]) | lia ].
Qed.

(** The memory at the property loop's head, as this piece carries it. *)
Lemma mq_head : forall m1, MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 -> CFIX sp pp m1 ->
  HDR sp fl mask buflen b3 b4 b5 b6 m1 -> cell8 m1 (bv_unsigned sp + 0x48) np ->
  cell8 m1 (bv_unsigned sp + 0x40) (Z.b2z (sh =? 7)) ->
  MQ sp m rest src pp lo XB0 (IM B) L m1.
Proof.
  intros m1 MB (F38 & F50 & F68 & F70 & F80 & F90 & F98 & Fb0) HD C48 C40.
  destruct (HDR_cells sp m fl mask buflen b3 b4 b5 b6 m1 HD) as (H00 & H08 & H10 & H18 & H20 & H28 & H30).
  destruct (Lp_rng sh ps HWF HPS) as (LP1 & LP2). pose proof (Lp_def sh ps) as LPD.
  split; [exact MB|]. split.
  - rewrite <- (Z.add_0_r (bv_unsigned sp)) in H00. unfold FC, XB.
    repeat (apply Forall_cons; [unfold cok; cbn [fst snd]; split; [lia|]; split; [lia | assumption] |]).
    apply Forall_nil.
  - eapply len_bytes_of; [exact MB |]. change (pc_buf (PbCut sh ps None)) with B. lia.
Qed.

(** ** 0x13334 -> 0x140e4 *)
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

Lemma prop_ok : forall r ms, PROPH sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo sh np ps r ms ->
  evt rsegs (PQ0 (fst (prop_step sh r)) (snd (prop_step sh r))) ms.
Proof.
  intros r ms HP.
  destruct HP as (ra & t1 & a0 & a2 & a3 & a4 & s2 & s7 & s8 & s9 & t4 & t5 & t6 & m1 &
                  Ems & MB & CF & HD & C48 & C40 & Hs & Hw).
  subst ms.
  pose proof (mq_head m1 MB CF HD C48 C40) as MQ0. clear MB CF HD C48 C40.
  pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  pose proof (suffix_len rest r Hs) as Hlr.
  assert (W0 : pc_wf sh (ps ++ [(0, PInt 0)]))
    by (apply wf_snoc; [exact HWF | exact HPS | cbn; split; [lia | exact I] | apply Forall_nil]).
  unfold PROP_HEAD, POD_LEN_OFF, S8V, S10V.
  (* 0x13334 beqz s6 *)
  step.
  destruct r as [|x r1].
  - (* no byte left: 0x13348 mv a0,zero, the selector is 0 *)
    brT. step.
    destruct (Z.eq_dec sh 7) as [E7 | E7].
    + rewrite (prop_step_s7 [] E7). cbn [fuzz_u8 fst snd].
      eapply s7_ok; first [eassumption | exact E7].
    + rewrite (prop_step_ns [] E7). cbn [fuzz_u8 fst snd].
      eapply ns_ok; first [eassumption | lia].
  - change (length (x :: r1)) with (S (length r1)) in *.
    brF.
    (* 0x13338 lbu a0,0(s5) ; addi s5,s5,1 ; addi s6,s6,-1 ; j *)
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

(** 0x13334 -> 0x140e4: one property of the object (pod.h:399-438), the pod loop of a params Struct included. *)
Theorem prop_holds : forall sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo,
  memset_c.memset_contract -> memcpy_c.memcpy_contract -> strlen_c.strlen_contract ->
  EntCut.rb_ent_contract ->
  Cut.S_write sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo ->
  Cut.S_prop sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo.
Proof.
  intros sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo MSET MCPY STRL ENT SW HOK sh np ps r ms HP Hlt
    H3 HSPA.
  assert (HPS : (length ps <= 2)%nat) by lia.
  assert (HWF : pc_wf sh ps).
  { destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw).
    exact Hw. }
  eapply prop_ok; eassumption.
Qed.
