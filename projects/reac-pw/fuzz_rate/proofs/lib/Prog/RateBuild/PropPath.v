(** The straight-line paths of one property of the inlined pod builder (plain image): the latch 0x140e4, a Struct
    object's property (0x1334c -> 0x140e4, the pod `Int 0`), an Int property (0x13f6c -> 0x140e4, the pod `Int 7`,
    and has_params for the first SPA_PROP_params) and the end of a params Struct (0x140a0 -> 0x140e4, its size word,
    has_params and params_struct). Ported from reac-pw/fuzz_role's Prog/RoleBuild/PropPath.v
    (role 0x130e4 / 0x13cf0 / 0x13e24 -> 0x13e68) at rate's registers
    (role s7 -> s2, s3 -> s5, s4 -> s6, s9 -> a5, s11 -> s1), frame cells (role + 0x30; the header [sp, sp + 0x38))
    and pcs. Unlike role, rate's code keeps the shape test in a5, a caller-saved register, so both memset calls save
    it (s1 at 0x13404, s8 at 0x14020), and `seen_params` (t3) too (s3 at 0x13408, s7 at 0x13ffc). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild Require Import Facts Cut Write Post PropKit.
Import ListNotations.
Open Scope Z_scope.

(** ** The steps of the walk *)
(** A branch whose test compares two words that fit, or a closed test. *)
Ltac cnd1 := first [ apply eqb_T; lia | apply eqb_F; lia | apply ltu_T; lia | apply ltu_F; lia ].
Ltac cnd := first [ reflexivity | cnd1 | apply nb_T; cnd1 | apply nb_F; cnd1 ].
Ltac brT :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let H := fresh "Hbr" in assert (H : c = true) by cnd; rewrite H; cbv iota; clear H
  end.
Ltac brF :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let H := fresh "Hbr" in assert (H : c = false) by cnd; rewrite H; cbv iota; clear H
  end.

(** pod_put's capacity test (pod.h:177), `len + (-0x3ffd) <u -0x4001`, whatever form the sum takes. *)
Lemma cap_dead : forall X, -16381 <= X < 0 -> bv_ltu (Z_to_bv 64 X) (Z_to_bv 64 (-16385)) = false.
Proof. intros X HX. replace X with (X + 16381 + -16381) by lia. apply put_cap_dead. lia. Qed.

(** The pad of a length 4 past a multiple of 8 (pod.h:187). *)
Lemma pad8_4 : forall L z, (8 | L) -> (z - 4 - L) mod 8 = 0 -> pad8 z = 4.
Proof. intros L z [d ->] H. rewrite pad8_alt. lia. Qed.

(** Never taken. *)
Ltac capF :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let H := fresh "Hbr" in
      assert (H : c = false)
        by first [ apply cap_dead; lia | apply put_cap_dead'; lia | apply nb_F; apply cap_dead; lia ];
      rewrite H; cbv iota; clear H
  end.
(** Its `bgeu` form: always taken. *)
Ltac capT :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let H := fresh "Hbr" in
      assert (H : c = true) by (apply nb_T; apply cap_dead; lia);
      rewrite H; cbv iota; clear H
  end.

(** `negw a0,s7 ; andi s4,a0,7`: the pad, 4 for the puts of this piece. *)
Ltac negpad :=
  lazymatch goal with
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 ?z))))) 7] =>
      rewrite (neg_and7 z) by lia;
      lazymatch goal with
      | HD : (8 | ?Lx) |- _ => replace (pad8 z) with 4 by (symmetry; apply (pad8_4 Lx); [exact HD | lia])
      end
  end.

(** A store of J bytes into the block at pp + O. *)
Ltac stq O J :=
  lazymatch goal with
  | MQH : MQ ?a1 ?a2 ?a3 ?a4 ?pp ?a6 ?xs ?Ib ?len ?mm |- _ =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs mm (wa (pp + O)) J = true)
      by (eapply mq_ok; [exact MQH | reflexivity | lia | lia]);
    step; clear HS;
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?w ?bs) _) =>
      let MQ2 := fresh "MQh" in
      assert (MQ2 : MQ a1 a2 a3 a4 pp a6 xs (overwrite Ib (Z.to_nat O) bs) len (write_to_mem mm w bs))
        by (eapply mq_store;
            first [ eassumption
                  | rewrite ?length_le1, ?length_le4, ?length_le8, ?length_le64; lia ]);
      clear MQH; let mn := fresh "m" in gen_mem MQ2 mn
    end
  end.
Ltac sbq O := stq O 1%nat.

(** The four byte stores of a put are one overwrite of the image. *)
Ltac imlen :=
  lazymatch goal with
  | |- context [length (IMq ?s ?p ?b)] =>
      let H := fresh "HIL" in
      assert (H : Z.of_nat (length (IMq s p b)) = 19744)
        by (eapply IMq_len; [eassumption | rewrite ?length_app, ?length_le32, ?length_zeros; lia]);
      lia
  end.
Ltac c4 O :=
  lazymatch goal with
  | MQH : MQ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite (ow4 _ O) in MQH by first [lia | imlen]
  end.
(** The four bytes of a put of a small literal. *)
Ltac lbq V :=
  lazymatch goal with
  | MQH : MQ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite (lb4 V) in MQH by lia
  end.

(** pp->len: its load and its store; the store ends a put. *)
Ltac ldl :=
  lazymatch goal with
  | MQH : MQ _ _ _ _ _ _ _ _ _ _ |- _ =>
      let HR := fresh "HRl" in pose proof MQH as HR; apply mq_rd_len in HR; step; clear HR
  end.
Ltac sdl :=
  lazymatch goal with
  | MQH : MQ ?a1 ?a2 ?a3 ?a4 ?pp ?a6 ?xs ?Ib ?len ?mm |- _ =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs mm (wa (pp + 16384)) 8 = true)
      by (eapply mq_ok; [exact MQH | reflexivity | lia | lia]);
    step; clear HS; rewrite ?le8_lit64;
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?w (le64 ?v)) _) =>
      let MQ2 := fresh "MQh" in
      assert (MQ2 : MQ a1 a2 a3 a4 pp a6 xs (overwrite Ib (Z.to_nat 16384) (le64 v)) v (write_to_mem mm w (le64 v)))
        by (eapply mq_setlen; [eassumption | exact MQH | lia]);
      clear MQH; let mn := fresh "m" in gen_mem MQ2 mn
    end
  end.
Ltac fput :=
  lazymatch goal with
  | MQH : MQ _ _ _ _ _ _ _ _ _ _ |- _ =>
      rewrite img_put in MQH by (rewrite ?length_app, ?length_le32, ?length_zeros; lia)
  end.

(** A frame cell: its load, and its store (which adds it to the list). *)
Ltac in_tac := repeat (first [ apply in_eq | apply in_cons ]).
Ltac ldc O :=
  lazymatch goal with
  | MQH : MQ ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?xs ?Ib ?len ?mm |- _ =>
      let HR := fresh "HRc" in
      epose proof (mq_rd a1 a2 a3 a4 a5 a6 xs Ib len mm O _ MQH ltac:(in_tac)) as HR;
      step; clear HR
  end.
Ltac apart_tac := unfold apart; repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil.
Ltac sdc O V :=
  lazymatch goal with
  | MQH : MQ ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?xs ?Ib ?len ?mm |- _ =>
    let H := fresh "Hsd" in
    assert (H : MQ a1 a2 a3 a4 a5 a6 ((O, V) :: xs) Ib len
                  (write_to_mem mm (Z_to_bv 64 (bv_unsigned a1 + O)) (le8 (Z_to_bv 64 V))) /\
                store_ok rsegs mm (wa (bv_unsigned a1 + O)) 8 = true)
      by (eapply mq_sd; [ eassumption | exact MQH | lia | lia | apart_tac ]);
    let HS := fresh "HS" in let HM := fresh "HM" in
    destruct H as [HM HS]; step; clear HS;
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?w ?bs) _) =>
      let MQ2 := fresh "MQh" in
      assert (MQ2 : MQ a1 a2 a3 a4 a5 a6 ((O, V) :: xs) Ib len (write_to_mem mm w bs)) by exact HM;
      clear HM MQH; let mn := fresh "m" in gen_mem MQ2 mn
    end
  end.

(** memset(pp + O, 0, N) (pod.h:179's put of the pad). *)
Ltac mset O N :=
  lazymatch goal with
  | MQH : MQ ?a1 ?a2 ?a3 ?a4 ?pp ?a6 ?xs ?Ib ?len ?mm, MSET : memset_contract |- _ =>
    let HIL := fresh "HIL" in pose proof (mq_ilen _ _ _ _ _ _ _ _ _ _ MQH) as HIL;
    eapply evt_cut;
    [ eapply MSET;
      [ lazymatch goal with
        | |- rw_cells _ _ (bv_unsigned (Z_to_bv 64 ?X)) [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 ?N'))) _] =>
            rewrite (unsigned_lit X) by lia; rewrite (unsigned_lit N') by lia;
            replace X with (pp + O) by lia; replace N' with N by lia
        end;
        destruct MQH as (MB & _);
        apply (MBr_pp_cells a1 a2 a3 a4 pp a6 _ _ O (Z.to_nat N) MB); lia
      | destruct MQH as ((_ & _ & _ & _ & _ & _ & MI & _) & _); exact MI ]
    | ];
    let ms' := fresh "ms'" in let Hp := fresh "Hpost" in
    intros ms' Hp; unfold memset_post in Hp;
    let m2 := fresh "m" in let Ems := fresh "Ems" in let MU := fresh "MU" in
    let WM := fresh "WM" in let MI := fresh "MI" in let HCB := fresh "HCB" in
    destruct Hp as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Ems & MU & WM & MI & HCB);
    subst ms'; ret_even;
    lazymatch type of HCB with
    | rw_cells _ _ (bv_unsigned (Z_to_bv 64 ?X)) [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 ?N'))) _] =>
        rewrite (unsigned_lit X) in MU, HCB by lia; rewrite (unsigned_lit N') in MU, HCB by lia;
        replace X with (pp + O) in MU, HCB by lia; replace N' with N in MU, HCB by lia
    end;
    rewrite (unsigned_lit 0) in HCB by lia; change (0 mod 256) with 0 in HCB;
    let MQ2 := fresh "MQh" in
    assert (MQ2 : MQ a1 a2 a3 a4 pp a6 xs (overwrite Ib (Z.to_nat O) (zeros (Z.to_nat N))) len m2)
      by (eapply (mq_call a1 a2 a3 a4 pp a6 ltac:(eassumption) xs Ib len mm m2 O N (pp + O));
          [ exact MQH | reflexivity | exact MU | exact WM | exact MI
          | exact (rw_cells_CB_bytes m2 _ _ _ HCB) | rewrite length_zeros; lia | lia | lia | lia ]);
    clear MQH MU WM MI HCB HIL
  end.

Section Path.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl mask buflen b3 b4 b5 b6 src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.
Hypothesis MSET : memset_contract.
Variables (sh np : Z) (ps : list (Z * pval)).
Hypothesis HWF : pc_wf sh ps.
Hypothesis HPS : (length ps <= 2)%nat.

Abbreviation L := (Lp sh ps).
Abbreviation B := (bp sh ps).
Abbreviation IM := (IMq sh ps).

(** The frame cells every path keeps: the preheader's constants (as literals), the seven header cells, nprops and
    the shape test. *)
Definition XB : list (Z * Z) :=
  [(0x38, 65539); (0x50, 524289); (0x68, pp + 16404); (0x70, pp + 19732); (0x80, pp); (0x90, -16385);
   (0x98, -16381); (0xb0, pp + 16384); (0, b5); (0x8, mask); (0x10, b3); (0x18, fl); (0x20, buflen);
   (0x28, b6 * 256); (0x30, b4 * 256); (0x48, np); (0x40, Z.b2z (sh =? 7))].

(** The latch's state for the property kv, the input r' left. *)
Definition PQ (kv : Z * pval) (r' : list byte) : machine_state -> Prop :=
  PROPL sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo sh np (length ps) (ps ++ [kv]) r'.

(** ** 0x140e4, the latch *)
Lemma latch_ok : forall kv r' (xs : list (Z * Z)) Ib len m1 (c3 c4 tv : Z)
    (ra t1 a0 a2 a3 a4 s2 s7 s8 s9 t4 t5 t6 : word),
  MQ sp m rest src pp lo xs Ib len m1 -> (forall p, In p XB -> In p xs) ->
  Ib = pc_image (PbCut sh (ps ++ [kv]) None) -> suffix rest r' -> pc_wf sh (ps ++ [kv]) ->
  c3 = cur rest src r' -> c4 = Z.of_nat (length r') -> tv = Z.b2z (seen_of (ps ++ [kv])) ->
  evt rsegs (PQ kv r')
    (MS (mkR ra sp gp tp (Z_to_bv 64 (-16385)) t1 (Z_to_bv 64 np) (Z_to_bv 64 95) (Z_to_bv 64 pp)
             a0 (Z_to_bv 64 (Z.of_nat (length ps))) a2 a3 a4 (Z_to_bv 64 (Z.b2z (sh =? 7)))
             (Z_to_bv 64 (pp + 16384)) (Z_to_bv 64 (-16381))
             s2 (Z_to_bv 64 10) (Z_to_bv 64 MULT10) (Z_to_bv 64 c3) (Z_to_bv 64 c4) s7 s8 s9
             (Z_to_bv 64 (bv_unsigned sp + 0x158)) (Z_to_bv 64 (bv_unsigned sp + 0x120))
             (Z_to_bv 64 tv) t4 t5 t6)
        F (Z_to_bv 64 0x140e4) fc None m1 (seg_rom rsegs)).
Proof.
  intros kv r' xs Ib len m1 c3 c4 tv ra t1 a0 a2 a3 a4 s2 s7 s8 s9 t4 t5 t6 (MB & HF & _) Hsub -> Hs Hw
    -> -> ->.
  pose proof (FC_sub sp m1 xs XB HF Hsub) as HB.
  assert (G : forall o v, In (o, v) XB -> cell8 m1 (bv_unsigned sp + o) v)
    by (intros o v Hin; exact (FC_get sp m1 XB o v HB Hin)).
  apply evt_done. unfold PQ, PROPL.
  exists ra, t1, a0, a2, a3, a4, s2, s7, s8, s9, t4, t5, t6, m1.
  split; [reflexivity|]. split; [exact MB|].
  split.
  { unfold CFIX.
    split; [apply G; in_tac|]. split; [apply G; in_tac|]. split; [apply G; in_tac|].
    split; [apply G; in_tac|]. split; [apply G; in_tac|]. split; [apply G; in_tac|].
    split; [apply G; in_tac|]. apply G; in_tac. }
  split.
  { apply HDR_of_cells; [rewrite <- (Z.add_0_r (bv_unsigned sp)); apply G; in_tac | apply G; in_tac ..]. }
  split; [apply G; in_tac|]. split; [apply G; in_tac|].
  split; [exact Hs|]. split; [exact Hw|].
  rewrite length_app. cbn [length]. lia.
Qed.

(** ** 0x1334c -> 0x140e4: the property of a Struct object, its value pod `Int 0` only (pod.h:401-405) *)
Lemma pb_s7 : sh = 7 -> prop_bytes sh (0, PInt 0) = le32 4 ++ le32 4 ++ le32 0 ++ zeros 4.
Proof. intros ->. reflexivity. Qed.

Lemma s7_ok : forall r1 (ra t1 a0 a2 a3 a4 s2 s7 s8 s9 t4 t5 t6 : word) m1,
  sh = 7 -> suffix rest r1 -> pc_wf sh (ps ++ [(0, PInt 0)]) ->
  MQ sp m rest src pp lo XB (IM B) L m1 ->
  evt rsegs (PQ (0, PInt 0) r1)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (-16385)) t1 (Z_to_bv 64 np) (Z_to_bv 64 95) (Z_to_bv 64 pp)
             a0 (Z_to_bv 64 (Z.of_nat (length ps))) a2 a3 a4 (Z_to_bv 64 (Z.b2z (sh =? 7)))
             (Z_to_bv 64 (pp + 16384)) (Z_to_bv 64 (-16381))
             s2 (Z_to_bv 64 10) (Z_to_bv 64 MULT10) (Z_to_bv 64 (cur rest src r1))
             (Z_to_bv 64 (Z.of_nat (length r1))) s7 s8 s9
             (Z_to_bv 64 (bv_unsigned sp + 0x158)) (Z_to_bv 64 (bv_unsigned sp + 0x120))
             (Z_to_bv 64 (Z.b2z (seen_of ps))) t4 t5 t6)
        F (Z_to_bv 64 0x1334c) fc None m1 (seg_rom rsegs)).
Proof.
  intros r1 ra t1 a0 a2 a3 a4 s2 s7 s8 s9 t4 t5 t6 m1 E7 Hs Hw MQ0.
  pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  destruct (Lp_rng sh ps HWF HPS) as (LP1 & LP2). pose proof (Lp_def sh ps) as LPD.
  (* 0x1334c ld s2,0(a6) ; 0x13350 add a2,s2,a7 ; 0x13354 beqz a5 *)
  ldl. step. step.
  assert (B7 : bv_eqb (Z_to_bv 64 (Z.b2z (sh =? 7))) (Z_to_bv 64 0) = false) by (rewrite E7; reflexivity).
  rewrite B7; cbv iota. clear B7.
  (* 0x13358 bltu a2,t0 ; 0x1335c add s2,s1,s2 ; 0x13360 addi a2,zero,4 *)
  step. capF. step. step.
  (* 0x13364 .. 0x13370: the size word 4 *)
  sbq (Lp sh ps). sbq (L + 1). sbq (L + 2). sbq (L + 3). c4 (Lp sh ps). lbq 4.
  (* 0x13374 ld s2,0(a6) ; addi s2,s2,4 ; add a0,s2,a7 ; sd s2,0(a6) *)
  ldl. step. step. sdl. fput.
  (* 0x13384 bltu a0,t0 ; 0x13388 add s2,s1,s2 ; 0x1338c .. 0x13398: the type word 4 *)
  step. capF. step.
  sbq (L + 4). sbq (L + 4 + 1). sbq (L + 4 + 2). sbq (L + 4 + 3). c4 (L + 4). lbq 4.
  ldl. step. sdl. fput.
  (* 0x133a8 mv s9,s6 ; add a0,s2,a7 ; bltu a0,t0 ; add s2,s1,s2 ; 0x133b8 .. 0x133c4: the value 0 *)
  step. step. step. capF. step.
  sbq (L + 4 + 4). sbq (L + 4 + 4 + 1). sbq (L + 4 + 4 + 2). sbq (L + 4 + 4 + 3). c4 (L + 4 + 4). lbq 0.
  ldl. step. sdl. fput.
  (* 0x133d4 negw a0,s2 ; andi s6,a0,7: the pad, 4 *)
  step. step.
  negpad.
  (* 0x133dc add a0,s6,s2 ; lui a2,4 ; bltu a2,a0 *)
  step. step. step. capF.
  (* 0x133e8 add a0,s1,s2 .. 0x1340c jal memset (pp, a1, a5 and t2, t3 saved in s2, s1, s5, s3; s5 in s8) *)
  do 10 step.
  mset (L + 12) 4.
  (* 0x13410 .. 0x13424: the saved registers back *)
  do 6 step.
  (* 0x13428 ld t0,0x90(sp) ; ld a7,0x98(sp) ; mv a1,s2 ; ld a6,0xb0(sp) *)
  ldc 0x90. ldc 0x98. step. ldc 0xb0.
  (* 0x13438 ld a0,0(a6) ; add a0,a0,s6 ; sd a0,0(a6) *)
  ldl. step. sdl. fput.
  (* 0x13444 j ; 0x14060 mv s6,s9 ; j *)
  step. step. step.
  eapply latch_ok; [eassumption | intros p Hp; exact Hp | | exact Hs | exact Hw | reflexivity | reflexivity | ].
  - rewrite img_same by (apply fp_other; cbn [fst]; unfold POD_PROP_PARAMS; lia).
    rewrite (pb_s7 E7). rewrite <- !app_assoc. reflexivity.
  - rewrite seen_snoc. cbn [fst]. replace (0 =? POD_PROP_PARAMS) with false by reflexivity.
    rewrite orb_false_r. reflexivity.
Qed.

(** ** 0x13f6c -> 0x140e4: an Int property `Int 7` (pod.h:413-418) *)
Lemma int_ok : forall K (f : bool) (tv A2 S2 : Z) r1 (ra t1 t3 a0 a1 a3 s7 s8 s9 t4 t5 t6 : word) m1,
  sh <> 7 -> suffix rest r1 -> pc_wf sh (ps ++ [(K, PInt 7)]) ->
  tv = Z.b2z (seen_of (ps ++ [(K, PInt 7)])) -> A2 = L + 8 - 16381 -> S2 = L + 8 ->
  (if f then overwrite (IM (B ++ prop_bytes sh (K, PInt 7))) (Z.to_nat 16396) (le4 (Z_to_bv 64 1))
   else IM (B ++ prop_bytes sh (K, PInt 7))) = pc_image (PbCut sh (ps ++ [(K, PInt 7)]) None) ->
  MQ sp m rest src pp lo ((0xa0, Z.b2z f) :: (0x78, Z.of_nat (length ps)) :: XB)
     (IM ((B ++ le32 K) ++ le32 0)) S2 m1 ->
  evt rsegs (PQ (K, PInt 7) r1)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (-16385)) t1 (Z_to_bv 64 np) (Z_to_bv 64 95) (Z_to_bv 64 pp)
             a0 a1 (Z_to_bv 64 A2) a3 (Z_to_bv 64 tv) (Z_to_bv 64 (Z.b2z (sh =? 7)))
             (Z_to_bv 64 (pp + 16384)) (Z_to_bv 64 (-16381))
             (Z_to_bv 64 S2) (Z_to_bv 64 10) (Z_to_bv 64 MULT10) (Z_to_bv 64 (cur rest src r1))
             (Z_to_bv 64 (Z.of_nat (length r1))) s7 s8 s9
             (Z_to_bv 64 (bv_unsigned sp + 0x158)) (Z_to_bv 64 (bv_unsigned sp + 0x120)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f6c) fc None m1 (seg_rom rsegs)).
Proof.
  intros K f tv A2 S2 r1 ra t1 t3 a0 a1 a3 s7 s8 s9 t4 t5 t6 m1 H7 Hs Hw Htv HA2 HS2 Himg MQ0.
  pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  destruct (Lp_rng sh ps HWF HPS) as (LP1 & LP2). pose proof (Lp_def sh ps) as LPD.
  (* 0x13f6c lui a3,4 ; bgeu a2,t0 *)
  step. step. capT.
  (* 0x13f7c add s2,s1,s2 ; addi a2,zero,4 ; 0x13f84 .. 0x13f90: the size word 4 *)
  step. step.
  sbq (L + 4 + 4). sbq (L + 4 + 4 + 1). sbq (L + 4 + 4 + 2). sbq (L + 4 + 4 + 3). c4 (L + 4 + 4). lbq 4.
  (* 0x13f94 ld s2,0(a6) ; addi s2,s2,4 ; add a0,s2,a7 ; sd s2,0(a6) ; ld a1,0x78(sp) *)
  ldl. step. step. sdl. fput. ldc 0x78.
  (* 0x13fa8 bltu a0,t0 ; add s2,s1,s2 ; 0x13fb0 .. 0x13fbc: the type word 4 *)
  step. capF. step.
  sbq (L + 4 + 4 + 4). sbq (L + 4 + 4 + 4 + 1). sbq (L + 4 + 4 + 4 + 2). sbq (L + 4 + 4 + 4 + 3).
  c4 (L + 4 + 4 + 4). lbq 4.
  ldl. step. sdl. fput.
  (* 0x13fcc mv s9,s6 ; add a0,s2,a7 ; bltu a0,t0 ; add s2,s1,s2 ; addi a0,zero,7 ; the value 7 *)
  step. step. step. capF. step. step.
  sbq (L + 4 + 4 + 4 + 4). sbq (L + 4 + 4 + 4 + 4 + 1). sbq (L + 4 + 4 + 4 + 4 + 2).
  sbq (L + 4 + 4 + 4 + 4 + 3). c4 (L + 4 + 4 + 4 + 4). lbq 7.
  ldl. step. sdl. fput.
  (* 0x13ffc mv s7,a4 ; negw a0,s2 ; andi s6,a0,7: the pad, 4 *)
  step. step. step.
  negpad.
  (* 0x14008 add a0,s6,s2 ; bltu a3,a0 *)
  step. step. capF.
  (* 0x14010 add a0,s1,s2 ; mv a1,zero ; mv a2,s6 ; mv s2,t2 ; mv s8,a5 ; jal memset *)
  do 6 step.
  mset (L + 20) 4.
  (* 0x14028 mv a5,s8 ; mv t2,s2 ; ld t0 ; ld a7 ; ld a1 ; ld a6 *)
  step. step. ldc 0x90. ldc 0x98. ldc 0x78. ldc 0xb0.
  (* 0x14040 ld a0,0(a6) ; add a0,a0,s6 ; sd a0,0(a6) *)
  ldl. step. sdl. fput.
  (* 0x1404c ld a0,0xa0(sp) ; beqz a0 *)
  ldc 0xa0. step.
  destruct f.
  - (* the first SPA_PROP_params: 0x14054 addi a0,zero,1 ; sw a0,0xc(a6) *)
    brF. step. stq 16396 4%nat.
    (* 0x1405c mv t3,s7 ; 0x14060 mv s6,s9 ; j *)
    step. step. step.
    eapply latch_ok; [eassumption | intros p Hp; right; right; exact Hp | | exact Hs | exact Hw
                      | reflexivity | reflexivity | exact Htv].
    rewrite <- Himg. rewrite pb_int by exact H7. rewrite <- !app_assoc. reflexivity.
  - brT. step. step. step.
    eapply latch_ok; [eassumption | intros p Hp; right; right; exact Hp | | exact Hs | exact Hw
                      | reflexivity | reflexivity | exact Htv].
    rewrite <- Himg. rewrite pb_int by exact H7. rewrite <- !app_assoc. reflexivity.
Qed.

(** ** 0x140a0 -> 0x140e4: the end of a params Struct (pod.h:434-437) *)
Definition XC : list (Z * Z) := (0x60, 1) :: (0xa0, Z.b2z (first_of ps)) :: (0x78, Z.of_nat (length ps)) :: XB.

Lemma close_ok : forall es r (LEN AT c3 c4 : Z) Ib (ra t1 a1 a2 a3 a4 s7 s8 s9 t3 t4 t5 t6 : word) m1,
  sh <> 7 -> suffix rest r -> Forall ent_wf es -> (length es <= 32)%nat ->
  LEN = Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) -> AT = L + 8 ->
  Ib = pc_image (PbCut sh ps (Some es)) -> c3 = cur rest src r -> c4 = Z.of_nat (length r) ->
  MQ sp m rest src pp lo XC Ib LEN m1 ->
  evt rsegs (PQ (POD_PROP_PARAMS, PStruct es) r)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (-16385)) t1 (Z_to_bv 64 np) (Z_to_bv 64 95) (Z_to_bv 64 pp)
             (Z_to_bv 64 LEN) a1 a2 a3 a4 (Z_to_bv 64 (Z.b2z (sh =? 7)))
             (Z_to_bv 64 (pp + 16384)) (Z_to_bv 64 (-16381))
             (Z_to_bv 64 AT) (Z_to_bv 64 10) (Z_to_bv 64 MULT10) (Z_to_bv 64 c3) (Z_to_bv 64 c4) s7 s8 s9
             (Z_to_bv 64 (bv_unsigned sp + 0x158)) (Z_to_bv 64 (bv_unsigned sp + 0x120)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x140a0) fc None m1 (seg_rom rsegs)).
Proof.
  intros es r LEN AT c3 c4 Ib ra t1 a1 a2 a3 a4 s7 s8 s9 t3 t4 t5 t6 m1 H7 Hs Hes Hel HLEN -> HIb Hc3 Hc4 MQ0.
  pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  destruct (Lp_rng sh ps HWF HPS) as (LP1 & LP2). pose proof (Lp_def sh ps) as LPD.
  pose proof (mq_ilen _ _ _ _ _ _ _ _ _ _ MQ0) as HIL0.
  assert (HLE : L + 16 <= LEN <= 5440).
  { destruct HWF as (_ & Hk & He & _).
    assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps)
      by (eapply Forall_impl; [|exact Hk]; intros kv (_ & H); exact H).
    destruct (pc_buf_len_open sh ps es Hv He Hes) as (H1 & _).
    assert (E : pc_buf (PbCut sh ps (Some es))
                = B ++ le32 POD_PROP_PARAMS ++ le32 0 ++ le32 0 ++ le32 POD_STRUCT ++ flat_map enc_pod es).
    { unfold bp, pc_buf, open_bytes. cbn [pc_shape pc_props pc_open]. rewrite <- !app_assoc. reflexivity. }
    assert (E2 : Z.of_nat (length (pc_buf (PbCut sh ps (Some es))))
                 = L + 16 + Z.of_nat (length (flat_map enc_pod es)))
      by (rewrite E, !length_app, !length_le32; lia).
    lia. }
  (* 0x140a0 subw a0,a0,s2 *)
  step. rewrite (subw_lit LEN (L + 8)) by lia.
  (* 0x140a4 add s2,s1,s2 ; addi a0,a0,-8 ; srli a1,a0,0x18 ; srli a2,a0,0x10 ; srli a3,a0,8 *)
  do 5 step.
  rewrite (unsigned_lit (LEN - (L + 8) + -8)) by lia.
  (* 0x140b8 .. 0x140c4: the size word, pod_patch32 *)
  sbq (L + 8). sbq (L + 8 + 1). sbq (L + 8 + 2). sbq (L + 8 + 3).
  lazymatch goal with
  | MQH : MQ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite (ow32 Ib (L + 8) (LEN - (L + 8) + -8)) in MQH by lia
  end.
  (* 0x140c8 ld a0,0xa0(sp) ; beqz a0 *)
  ldc 0xa0. step.
  destruct (first_of ps) eqn:EF.
  - (* the first SPA_PROP_params: has_params = params_struct = 1 *)
    assert (Hs0 : seen_of ps = false) by (unfold first_of in EF; apply negb_true_iff in EF; exact EF).
    brF. step. stq 16396 4%nat. stq 16400 4%nat.
    (* 0x140dc ld t3,0x60(sp) ; ld a1,0x78(sp) *)
    ldc 0x60. ldc 0x78.
    eapply latch_ok; [eassumption | intros p Hp; right; right; right; exact Hp | | exact Hs
                      | apply struct_wf; assumption | exact Hc3 | exact Hc4 | ].
    + subst Ib. apply img_close_first; assumption.
    + rewrite seen_snoc. cbn [fst]. rewrite Z.eqb_refl, orb_true_r. reflexivity.
  - assert (Hs0 : seen_of ps = true) by (unfold first_of in EF; apply negb_false_iff in EF; exact EF).
    brT. ldc 0x60. ldc 0x78.
    eapply latch_ok; [eassumption | intros p Hp; right; right; right; exact Hp | | exact Hs
                      | apply struct_wf; assumption | exact Hc3 | exact Hc4 | ].
    + subst Ib. apply img_close_other; assumption.
    + rewrite seen_snoc. cbn [fst]. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

End Path.
