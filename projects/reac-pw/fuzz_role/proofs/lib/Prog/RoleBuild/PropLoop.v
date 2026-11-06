(** The params Struct of one property of the inlined pod builder (plain image): the placeholder size word and the
    type (0x13270 -> 0x132c4), the count `fuzz_u8 % 33` (0x132c4 -> 0x132fc, pod.h:424), and the pod loop (0x132fc
    -> 0x13e24, pod.h:425-433) by induction on the pods left. Each turn is [EntCut.rb_ent_contract] (0x132fc ->
    0x1350c) then [Cut.S_write] (0x1350c -> 0x13618); the latch 0x13618 goes back to the head, or out to the
    Struct's end ([PropPath.close_ok]). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleBuild Require Import Facts Cut EntCut Write Post
  PropKit PropPath.
Import ListNotations.
Open Scope Z_scope.

(** `count = fuzz_u8 % 33` (pod.h:424) as the compiler computes it: the high word of c times the magic at .rodata
    0x10530, q; then c - (q << 5 | q). *)
Definition m33 (c : Z) : Z :=
  c - bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64
        (Z.shiftr (c * 558992244657865201) 64))) 5)))
      (bv_unsigned (Z_to_bv 64 (Z.shiftr (c * 558992244657865201) 64))))).

Lemma m33_mod : forall c, 0 <= c < 256 -> Z_to_bv 64 (m33 c) = Z_to_bv 64 (c mod 33).
Proof.
  intros c Hc. apply bv_eq.
  pose proof (all256 (fun c => bv_unsigned (Z_to_bv 64 (m33 c)) =? bv_unsigned (Z_to_bv 64 (c mod 33)))
                ltac:(vm_compute; reflexivity) c Hc) as H.
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma m33_zxb : forall y : byte, Z_to_bv 64 (m33 (bv_unsigned (zxb y))) = Z_to_bv 64 (bv_unsigned y mod 33).
Proof.
  intros y. pose proof (byte_range y) as Hy.
  replace (bv_unsigned (zxb y)) with (bv_unsigned y) by (unfold zxb; rewrite unsigned_lit by lia; reflexivity).
  apply m33_mod. exact Hy.
Qed.

(** The pod loop's turn changes these bytes of the frame (rb_ent_contract's munch). *)
Definition WT (sp : word) : list (Z * Z) :=
  [(bv_unsigned sp - MID_STACK, bv_unsigned sp); (bv_unsigned sp + 0x28, bv_unsigned sp + 0x30);
   (bv_unsigned sp + 0x78, bv_unsigned sp + 0x80); (bv_unsigned sp + 0x88, bv_unsigned sp + FRAME_LOCALS)].

Lemma keepW : forall (sp : word) m1 m2 (A v : Z), cell8 m1 A v -> munch (WT sp) m1 m2 ->
  bv_unsigned sp <= A ->
  (A + 8 <= bv_unsigned sp + 0x28 \/ (bv_unsigned sp + 0x30 <= A /\ A + 8 <= bv_unsigned sp + 0x78) \/
   (bv_unsigned sp + 0x80 <= A /\ A + 8 <= bv_unsigned sp + 0x88)) ->
  cell8 m2 A v.
Proof.
  intros sp m1 m2 A v H MU H1 H2. unfold cell8 in *.
  apply (bytes_at_transport rsegs _ m1 m2 _ _ H MU).
  unfold WT. cbn [disjoint_from]. rewrite length_le8. unfold MID_STACK, FRAME_LOCALS. repeat split; lia.
Qed.

Section Loop.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.
Hypothesis ENT : rb_ent_contract.
Hypothesis SW : S_write sp gp tp F fc m rest fl src pp lo.
Hypothesis HSPA : bv_unsigned sp mod 16 = 0.
Variables (sh np : Z) (ps : list (Z * pval)).
Hypothesis HWF : pc_wf sh ps.
Hypothesis HPS : (length ps <= 2)%nat.
Hypothesis H7 : sh <> 7.

Abbreviation L := (Lp sh ps).
Abbreviation B := (bp sh ps).
Abbreviation IM := (IMq sh ps).
Abbreviation PQ0 := (PQ sp gp tp F fc m rest fl src pp lo sh np ps).
Abbreviation XB0 := (XB fl pp sh np).
Abbreviation XC0 := (XC fl pp sh np ps).

(** The frame cells inside the pod loop. *)
Definition XL (cnt : Z) : list (Z * Z) := (0x58, cnt) :: XC0.

Lemma FC_cnt : forall cnt m1, CFIX sp pp m1 -> CVAR sp fl np sh ps (length ps) cnt m1 -> FC sp m1 (XL cnt).
Proof.
  intros cnt m1 (F10 & F20 & F38 & F40 & F50 & F60 & F68 & F80) (V00 & V08 & V18 & V30 & V48 & V58 & V70).
  rewrite <- (Z.add_0_r (bv_unsigned sp)) in V00.
  unfold FC, XL, XC, XB.
  repeat (apply Forall_cons; [unfold cok; cbn [fst snd]; split; [lia|]; split; [lia | assumption] |]).
  apply Forall_nil.
Qed.

Lemma cells_of : forall cnt m1, FC sp m1 (XL cnt) ->
  CFIX sp pp m1 /\ CVAR sp fl np sh ps (length ps) cnt m1.
Proof.
  intros cnt m1 HF.
  assert (G : forall o v, In (o, v) (XL cnt) -> cell8 m1 (bv_unsigned sp + o) v)
    by (intros o v Hin; exact (FC_get sp m1 _ o v HF Hin)).
  split.
  - unfold CFIX.
    split; [apply G; in_tac|]. split; [apply G; in_tac|]. split; [apply G; in_tac|].
    split; [apply G; in_tac|]. split; [apply G; in_tac|]. split; [apply G; in_tac|].
    split; [apply G; in_tac|]. apply G; in_tac.
  - unfold CVAR.
    split; [rewrite <- (Z.add_0_r (bv_unsigned sp)); apply G; in_tac|].
    split; [apply G; in_tac|]. split; [apply G; in_tac|]. split; [apply G; in_tac|].
    split; [apply G; in_tac|]. split; [apply G; in_tac|]. apply G; in_tac.
Qed.

(** The input byte at the cursor. *)
Lemma mq_byte : forall xs Ib len m1 (y : byte) r2, MQ sp m rest src pp lo xs Ib len m1 ->
  suffix rest (y :: r2) -> ov_read_bytes rsegs m1 (wa (cur rest src (y :: r2))) 1 = Some [y].
Proof.
  intros xs Ib len m1 y r2 (MB & _) (j & Hj & Hr).
  replace (cur rest src (y :: r2)) with (src + Z.of_nat j) by (unfold cur; rewrite Hr, length_skipn; lia).
  eapply MBr_byte; [exact MB | symmetry; exact Hr].
Qed.

(** ** One turn of the pod loop: 0x132fc -> 0x13618 *)
Lemma turn_ok : forall cnt es k r ms (Q : machine_state -> Prop),
  CNTH sp gp tp F fc m rest fl src pp lo sh np ps (length ps) cnt es k r ms ->
  (forall ms', CNTL sp gp tp F fc m rest fl src pp lo sh np ps (length ps) cnt es k
                 (fst (ent_build r)) (snd (ent_build r)) ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros cnt es k r ms Q HH K.
  destruct HH as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s5 & t3 & t4 & t5 & t6 & m1 &
                  Ems & MB & CF & CV & Hsuf & Hwf & H7' & Hes & Hk & Hk32 & Hps2 & Hcnt & Hkc).
  subst ms.
  pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  pose proof (suffix_len rest r Hsuf) as Hlr.
  pose proof Hsuf as (j & Hj & Er).
  assert (Ecur : cur rest src r = src + Z.of_nat j) by (unfold cur; rewrite Er, length_skipn; lia).
  pose proof (MBr_rest sp m rest src pp lo _ m1 j MB Hj) as HR. rewrite <- Er in HR.
  pose proof CF as (F10 & F20 & F38 & F40 & F50 & F60 & F68 & F80).
  pose proof CV as (V00 & V08 & V18 & V30 & V48 & V58 & V70).
  pose proof MB as (_ & _ & _ & _ & _ & _ & MI & ST & TB).
  pose proof HOK as (_ & _ & _ & _ & HMID & _ & _ & _ & _ & HSROM).
  eapply evt_cut.
  { eapply ENT with (src := cur rest src r) (r := r) (pp := pp) (lo := lo).
    all: try reflexivity.
    all: try assumption.
    - unfold cur. lia.
    - rewrite Ecur. exact HR.
    - unfold cur. lia. }
  intros ms' Hpost.
  destruct Hpost as (ra' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & t3' & t4' & t5' & t6' & m2 &
                     Ems & C78 & CE & MU & WM & MI2 & ST2).
  subst ms'.
  eapply evt_cut; [| exact K].
  apply SW; [exact HOK |].
  unfold CNTJ.
  exists ra', t1', t2', a0', a1', a2', a3', a4', a5', t3', t4', t5', t6', m2.
  split.
  { replace (cur rest src r + Z.of_nat (length r) - Z.of_nat (length (snd (ent_build r))))
      with (cur rest src (snd (ent_build r))) by (unfold cur; lia).
    reflexivity. }
  assert (MUW : munch (WT sp) m1 m2) by exact MU.
  split.
  { apply (MBr_call sp m rest src pp lo HOK _ m1 m2 _ MB MU WM MI2 ST2).
    - unfold sub_fp. intros x Hx. cbn [outside] in *. destruct Hx as (Hx & _).
      unfold MID_STACK, FRAME_LOCALS in *. repeat split; lia.
    - cbn [disjoint_from]. unfold MID_STACK, FRAME_LOCALS, POD_PROPS in *. repeat split; lia.
    - cbn [disjoint_from]. unfold MID_STACK, FRAME_LOCALS in *. repeat split; lia. }
  split.
  { unfold CFIX.
    split; [eapply keepW; [exact F10 | exact MUW | lia | lia]|].
    split; [eapply keepW; [exact F20 | exact MUW | lia | lia]|].
    split; [eapply keepW; [exact F38 | exact MUW | lia | lia]|].
    split; [eapply keepW; [exact F40 | exact MUW | lia | lia]|].
    split; [eapply keepW; [exact F50 | exact MUW | lia | lia]|].
    split; [eapply keepW; [exact F60 | exact MUW | lia | lia]|].
    split; [eapply keepW; [exact F68 | exact MUW | lia | lia]|].
    eapply keepW; [exact F80 | exact MUW | lia | lia]. }
  split.
  { unfold CVAR.
    split; [eapply keepW; [exact V00 | exact MUW | lia | lia]|].
    split; [eapply keepW; [exact V08 | exact MUW | lia | lia]|].
    split; [eapply keepW; [exact V18 | exact MUW | lia | lia]|].
    split; [eapply keepW; [exact V30 | exact MUW | lia | lia]|].
    split; [eapply keepW; [exact V48 | exact MUW | lia | lia]|].
    split; [eapply keepW; [exact V58 | exact MUW | lia | lia]|].
    eapply keepW; [exact V70 | exact MUW | lia | lia]. }
  split; [exact C78|]. split; [exact CE|].
  split; [destruct (ent_build_rest r) as [k' Hk']; rewrite Hk'; apply suffix_skipn; exact Hsuf|].
  split; [exact Hwf|]. split; [exact H7'|]. split; [exact Hes|]. split; [exact Hk|].
  split; [exact Hk32|]. split; [apply ent_build_wf|]. split; [exact Hps2|].
  split; [exact Hcnt | exact Hkc].
Qed.

(** ** The pod loop, by induction on the pods left *)
Lemma ents_loop_S : forall n r, ents_loop (S n) r =
  (fst (ent_build r) :: fst (ents_loop n (snd (ent_build r))), snd (ents_loop n (snd (ent_build r)))).
Proof.
  intros n r. cbn [ents_loop]. destruct (ent_build r) as [e r']. cbn [fst snd].
  destruct (ents_loop n r'). reflexivity.
Qed.

Lemma loop_ok : forall n cnt k es r ms,
  (k + n)%nat = Z.to_nat cnt ->
  CNTH sp gp tp F fc m rest fl src pp lo sh np ps (length ps) cnt es k r ms ->
  evt rsegs (PQ0 (POD_PROP_PARAMS, PStruct (es ++ fst (ents_loop n r))) (snd (ents_loop n r))) ms.
Proof.
  induction n as [|n IH]; intros cnt k es r ms Hn HH.
  - exfalso. destruct HH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                             _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcnt & Hkc).
    lia.
  - apply (turn_ok cnt es k r ms _ HH). intros ms' HL.
    rewrite ents_loop_S. cbn [fst snd].
    set (e := fst (ent_build r)) in *. set (r' := snd (ent_build r)) in *. clearbody e r'.
    destruct HL as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a7 & s3 & s5 & t3 & t4 & t5 & t6 & m1 &
                    Ems & MB & CF & CV & Hsuf & Hwf & H7' & Hes & Hk & Hk32 & Hps2 & Hcnt & Hkc).
    subst ms'.
    pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
    destruct (Lp_rng sh ps HWF HPS) as (LP1 & LP2).
    assert (Hel : (length (es ++ [e]) <= 32)%nat) by (rewrite length_app; cbn [length]; lia).
    assert (HLEN : Z.of_nat (length (pc_buf (PbCut sh ps (Some (es ++ [e]))))) <= 5440).
    { destruct HWF as (_ & Hk' & He & _).
      assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps)
        by (eapply Forall_impl; [|exact Hk']; intros kv (_ & H); exact H).
      destruct (pc_buf_len_open sh ps (es ++ [e]) Hv He Hes) as (H1 & _). lia. }
    assert (MQ1 : MQ sp m rest src pp lo (XL cnt) (pc_image (PbCut sh ps (Some (es ++ [e]))))
                     (Z.of_nat (length (pc_buf (PbCut sh ps (Some (es ++ [e])))))) m1).
    { split; [exact MB|]. split; [apply FC_cnt; assumption|].
      eapply len_bytes_of; [exact MB | lia]. }
    unfold CNT_LATCH, POD_LEN_OFF, S8V, S10V.
    (* 0x13618 addiw s9,s9,1 ; 0x1361c ld a0,0x58(sp) ; 0x13620 bne s9,a0 *)
    step. rewrite (addiw1_lit (Z.of_nat k)) by lia.
    ldc 0x58. step.
    destruct n as [|n'].
    + (* the last pod: 0x13624 j 0x13e0c *)
      brF. step.
      (* 0x13e0c ld a0,0(a6) ; mv s3,s6 ; ld t2,8(sp) ; ld s9,0x18(sp) ; ld a7,0x68(sp) ; ld t0,0x60(sp) *)
      ldl. step. ldc 8. ldc 0x18. ldc 0x68. ldc 0x60.
      cbn [ents_loop fst snd]. rewrite ?app_nil_r.
      eapply close_ok.
      all: first [ exact HOK | exact HWF | exact HPS | exact H7 | eassumption | reflexivity
                 | (eapply mq_sub; [eassumption | intros p Hp; right; exact Hp]) ].
    + (* back to the head 0x132fc *)
      brT.
      replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
      replace (es ++ e :: fst (ents_loop (S n') r')) with ((es ++ [e]) ++ fst (ents_loop (S n') r'))
        by (rewrite <- app_assoc; reflexivity).
      apply (IH cnt (S k) (es ++ [e]) r'); [lia|].
      unfold CNTH. do 19 eexists.
      split; [reflexivity|]. split; [exact MB|]. split; [exact CF|]. split; [exact CV|].
      split; [exact Hsuf|]. split; [exact Hwf|]. split; [exact H7'|]. split; [exact Hes|].
      split; [rewrite length_app; cbn [length]; lia|]. split; [lia|]. split; [exact Hps2|].
      split; [exact Hcnt | lia].
Qed.

(** ** 0x13270 -> 0x13e68: a params Struct, its pods, its end *)
Lemma str_ok : forall r1 (A2 S7 : Z) (ra t1 t3 a0 a1 a3 a5 s5 s6 t4 t5 t6 : word) m1,
  suffix rest r1 -> A2 = L + 8 - 16381 -> S7 = L + 8 ->
  MQ sp m rest src pp lo ((0x70, Z.b2z (first_of ps)) :: (0x48, Z.of_nat (length ps)) :: XB0)
     (IM ((B ++ le32 524289) ++ le32 0)) S7 m1 ->
  evt rsegs (PQ0 (POD_PROP_PARAMS, PStruct (fst (ents_loop (Z.to_nat (fst (fuzz_u8 r1) mod 33)) (snd (fuzz_u8 r1)))))
                 (snd (ents_loop (Z.to_nat (fst (fuzz_u8 r1) mod 33)) (snd (fuzz_u8 r1)))))
    (MS (mkR ra sp gp tp (Z_to_bv 64 (-16385)) t1 (Z_to_bv 64 np)
             (Z_to_bv 64 (bv_unsigned sp + 296)) (Z_to_bv 64 (bv_unsigned sp + 240))
             a0 a1 (Z_to_bv 64 A2) a3 (Z_to_bv 64 1) a5 (Z_to_bv 64 (pp + 16384))
             (Z_to_bv 64 (-16381)) (Z_to_bv 64 MULT10) (Z_to_bv 64 (cur rest src r1))
             (Z_to_bv 64 (Z.of_nat (length r1))) s5 s6 (Z_to_bv 64 S7) (Z_to_bv 64 95)
             (Z_to_bv 64 (Z.b2z (sh =? 7))) (Z_to_bv 64 10) (Z_to_bv 64 pp) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13270) fc None m1 (seg_rom rsegs)).
Proof.
  intros r1 A2 S7 ra t1 t3 a0 a1 a3 a5 s5 s6 t4 t5 t6 m1 Hs HA2 HS7 MQ0.
  pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  destruct (Lp_rng sh ps HWF HPS) as (LP1 & LP2). pose proof (Lp_def sh ps) as LPD.
  pose proof (suffix_len rest r1 Hs) as Hlr.
  (* 0x13270 mv a0,s7 ; bltu a2,t0 ; add a0,s11,a0 ; 0x1327c .. 0x13288: the size word 0 *)
  step. step. capF. step.
  sbq (L + 8). sbq (L + 8 + 1). sbq (L + 8 + 2). sbq (L + 8 + 3). c4 (L + 8). lbq 0.
  (* 0x1328c ld a0,0(a6) ; addi a0,a0,4 ; add a1,a0,a7 ; sd a0,0(a6) *)
  ldl. step. step. sdl. fput.
  (* 0x1329c bltu a1,t0 ; add a0,s11,a0 ; addi a1,zero,0xe ; the type word 14 *)
  step. capF. step. step.
  sbq (L + 12). sbq (L + 12 + 1). sbq (L + 12 + 2). sbq (L + 12 + 3). c4 (L + 12). lbq 14.
  ldl. step. sdl. fput.
  (* 0x132c4 sd a4,0x30(sp) ; 0x132c8 beqz s4 *)
  sdc 0x30 1. step.
  assert (EIm : IM ((((B ++ le32 524289) ++ le32 0) ++ le32 0) ++ le32 14) = pc_image (PbCut sh ps (Some [])))
    by (rewrite img_open, <- !app_assoc; reflexivity).
  assert (ELN : S7 + 8 = Z.of_nat (length (pc_buf (PbCut sh ps (Some [])))))
    by (rewrite <- pc_buf_open, !length_app, !length_le32; change (pc_buf (PbCut sh ps None)) with B; lia).
  destruct r1 as [|y r2].
  - (* no byte left: the count is 0, to 0x13e24 *)
    brT.
    cbn [fuzz_u8 fst snd]. replace (Z.to_nat (0 mod 33)) with 0%nat by reflexivity. cbn [ents_loop fst snd].
    eapply close_ok.
    all: first [ exact HOK | exact HWF | exact HPS | exact H7 | eassumption | reflexivity | apply Forall_nil
               | (cbn [length]; lia) ].
  - change (length (y :: r2)) with (S (length r2)) in *.
    brF.
    (* 0x132cc lbu a1,0(s3) *)
    lazymatch goal with
    | MQH : MQ _ _ _ _ _ _ _ _ _ _ |- _ => pose proof (mq_byte _ _ _ _ y r2 MQH Hs) as HRy
    end.
    step. clear HRy.
    (* 0x132d0 auipc a2,0xffffd ; ld a2,0x260(a2): the magic of `% 33` at .rodata 0x10530 *)
    lazymatch goal with
    | MQH : MQ _ _ _ _ _ _ _ _ _ _ |- _ => pose proof MQH as ((_ & _ & _ & _ & _ & _ & HMI & _) & _)
    end.
    step. step. clear HMI.
    (* 0x132d8 addi s4,s4,-1 ; mulhu a2,a1,a2 ; slli a3,a2,5 ; or a2,a3,a2 ; sub a1,a1,a2 *)
    do 5 step.
    fold (m33 (bv_unsigned (zxb y))). rewrite m33_zxb.
    (* 0x132ec addi s6,s3,1 ; sd a1,0x58(sp) ; beqz a1 *)
    step. sdc 0x58 (bv_unsigned y mod 33). step.
    pose proof (byte_range y) as Hy. pose proof (Z.mod_pos_bound (bv_unsigned y) 33 ltac:(lia)) as Hc.
    cbn [fuzz_u8 fst snd].
    destruct (Z.eq_dec (bv_unsigned y mod 33) 0) as [E0 | E0].
    + (* count 0: 0x13dec mv s3,s6 ; ld s9,0x18(sp) ; j 0x13e24 *)
      brT. step. ldc 0x18. step.
      rewrite E0. replace (Z.to_nat 0) with 0%nat by reflexivity. cbn [ents_loop fst snd].
      eapply close_ok.
      all: first [ exact HOK | exact HWF | exact HPS | exact H7 | eassumption | reflexivity | apply Forall_nil
                 | (eapply mq_sub; [eassumption | intros p Hp; right; exact Hp])
                 | exact (suffix_skipn rest (y :: r2) 1 Hs) | (unfold cur; cbn [length]; lia)
                 | (cbn [length]; lia) ].
    + (* count >= 1: 0x132f8 mv s9,zero, to the pod loop's head 0x132fc *)
      brF. step.
      apply (loop_ok (Z.to_nat (bv_unsigned y mod 33)) (bv_unsigned y mod 33) 0 [] r2); [lia |].
      lazymatch goal with MQH : MQ _ _ _ _ _ _ _ _ _ _ |- _ => pose proof MQH as (MB & HF & _) end.
      rewrite EIm in MB.
      destruct (cells_of (bv_unsigned y mod 33) _ HF) as (CF & CV).
      unfold CNTH. do 19 eexists.
      split.
      { rewrite HS7. replace (Z.of_nat (S (length r2)) + -1) with (Z.of_nat (length r2)) by lia.
        rewrite (cur_cons rest src y r2). reflexivity. }
      split; [exact MB|]. split; [exact CF|]. split; [exact CV|].
      split; [exact (suffix_skipn rest (y :: r2) 1 Hs)|]. split; [exact HWF|]. split; [exact H7|].
      split; [apply Forall_nil|]. split; [reflexivity|]. split; [lia|]. split; [exact HPS|].
      split; [lia | cbn [Z.of_nat]; lia].
Qed.

End Loop.
