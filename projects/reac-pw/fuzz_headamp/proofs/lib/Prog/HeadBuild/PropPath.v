(** The straight-line paths of one property of the inlined pod builder (plain image): the latch 0x13f64, a Struct
    object's property (0x13224 -> 0x13f64, the pod `Int 0`), an Int property (0x13e10 -> 0x13f64, the pod `Int 7`,
    and has_params for the first SPA_PROP_params) and the end of a params Struct (0x13f20 -> 0x13f64, its size word,
    has_params and params_struct). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadBuild Require Import Facts Cut Write Post PropKit.
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

(** Forget the newest frame cell (before a store writes that cell again). *)
Ltac drop1 :=
  lazymatch goal with
  | MQH : MQ ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 (_ :: ?xs) ?Ib ?len ?mm |- _ =>
      let H := fresh "MQh" in
      assert (H : MQ a1 a2 a3 a4 a5 a6 xs Ib len mm)
        by (eapply mq_sub; [exact MQH | intros p Hp; right; exact Hp]);
      clear MQH
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
Variables (rest : list byte) (nl cap src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.
Hypothesis MSET : memset_contract.
Variables (sh np : Z) (ps : list (Z * pval)).
Hypothesis HWF : pc_wf sh ps.
Hypothesis HPS : (length ps <= 2)%nat.

Abbreviation L := (Lp sh ps).
Abbreviation B := (bp sh ps).
Abbreviation IM := (IMq sh ps).

(** The frame cells the property loop's head finds: the preheader's constants (as literals), cap, null, nprops and
    the shape test. *)
Definition XH : list (Z * Z) :=
  [(0x10, 65539); (0x18, 524289); (0x30, pp + 16404); (0x38, pp + 19732); (0x50, pp + 16384); (0x58, pp);
   (0x70, -16385); (0x78, -16381); (0, cap); (8, nl); (0x20, np); (0x40, Z.b2z (sh =? 7))].

(** The frame cells every path keeps: those, and the property index the head stores (0x13208). *)
Definition XB : list (Z * Z) := (0x68, Z.of_nat (length ps)) :: XH.

(** The latch's state for the property kv, the input r' left. *)
Definition PQ (kv : Z * pval) (r' : list byte) : machine_state -> Prop :=
  PROPL sp gp tp F fc m rest nl cap src pp lo sh np (length ps) (ps ++ [kv]) r'.

(** ** 0x13f64, the latch *)
Lemma latch_ok : forall kv r' (xs : list (Z * Z)) Ib len m1 (c3 c4 tv : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 s6 s8 t3 t4 t5 t6 : word),
  MQ sp m rest src pp lo xs Ib len m1 -> (forall p, In p XH -> In p xs) ->
  Ib = pc_image (PbCut sh (ps ++ [kv]) None) -> suffix rest r' -> pc_wf sh (ps ++ [kv]) ->
  c3 = cur rest src r' -> c4 = Z.of_nat (length r') -> tv = Z.b2z (seen_of (ps ++ [kv])) ->
  evt rsegs (PQ kv r')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 336)) (Z_to_bv 64 tv)
             a0 a1 a2 a3 (Z_to_bv 64 np) (Z_to_bv 64 (Z.of_nat (length ps)))
             (Z_to_bv 64 (-16381)) (Z_to_bv 64 (-16385)) (Z_to_bv 64 (pp + 16384))
             (Z_to_bv 64 c3) (Z_to_bv 64 c4) (Z_to_bv 64 pp) s6
             (Z_to_bv 64 95) s8 (Z_to_bv 64 MULT10) (Z_to_bv 64 (bv_unsigned sp + 280)) (Z_to_bv 64 10)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f64) fc None m1 (seg_rom rsegs)).
Proof.
  intros kv r' xs Ib len m1 c3 c4 tv ra t0 t1 t2 a0 a1 a2 a3 s6 s8 t3 t4 t5 t6 (MB & HF & _) Hsub -> Hs Hw
    -> -> ->.
  pose proof (FC_sub sp m1 xs XH HF Hsub) as HB.
  assert (G : forall o v, In (o, v) XH -> cell8 m1 (bv_unsigned sp + o) v)
    by (intros o v Hin; exact (FC_get sp m1 XH o v HB Hin)).
  apply evt_done. unfold PQ, PROPL.
  exists ra, t0, t1, t2, a0, a1, a2, a3, s6, s8, t3, t4, t5, t6, m1.
  split; [reflexivity|]. split; [exact MB|].
  split.
  { unfold CFIX.
    split; [apply G; in_tac|]. split; [apply G; in_tac|]. split; [apply G; in_tac|].
    split; [apply G; in_tac|]. split; [apply G; in_tac|]. split; [apply G; in_tac|].
    split; [apply G; in_tac|]. apply G; in_tac. }
  split.
  { unfold CHAR.
    split; [rewrite <- (Z.add_0_r (bv_unsigned sp)); apply G; in_tac|].
    split; [apply G; in_tac|]. split; [apply G; in_tac|]. apply G; in_tac. }
  split; [exact Hs|]. split; [exact Hw|].
  rewrite length_app. cbn [length]. lia.
Qed.

(** ** 0x13224 -> 0x13f64: the property of a Struct object, its value pod `Int 0` only (pod.h:401-405) *)
Lemma pb_s7 : sh = 7 -> prop_bytes sh (0, PInt 0) = le32 4 ++ le32 4 ++ le32 0 ++ zeros 4.
Proof. intros ->. reflexivity. Qed.

Lemma s7_ok : forall r1 (ra t0 t1 t2 a0 a1 a2 a3 s6 s8 t3 t4 t5 t6 : word) m1,
  sh = 7 -> suffix rest r1 -> pc_wf sh (ps ++ [(0, PInt 0)]) ->
  MQ sp m rest src pp lo XB (IM B) L m1 ->
  evt rsegs (PQ (0, PInt 0) r1)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 336)) (Z_to_bv 64 (Z.b2z (seen_of ps)))
             a0 a1 a2 a3 (Z_to_bv 64 np) (Z_to_bv 64 (Z.of_nat (length ps)))
             (Z_to_bv 64 (-16381)) (Z_to_bv 64 (-16385)) (Z_to_bv 64 (pp + 16384))
             (Z_to_bv 64 (cur rest src r1)) (Z_to_bv 64 (Z.of_nat (length r1))) (Z_to_bv 64 pp) s6
             (Z_to_bv 64 95) s8 (Z_to_bv 64 MULT10) (Z_to_bv 64 (bv_unsigned sp + 280)) (Z_to_bv 64 10)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x13224) fc None m1 (seg_rom rsegs)).
Proof.
  intros r1 ra t0 t1 t2 a0 a1 a2 a3 s6 s8 t3 t4 t5 t6 m1 E7 Hs Hw MQ0.
  pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  destruct (Lp_rng sh ps HWF HPS) as (LP1 & LP2). pose proof (Lp_def sh ps) as LPD.
  (* 0x13224 ld s8,0(s2) ; 0x13228 add a2,s8,a6 ; 0x1322c ld a1,0x40(sp) ; 0x13230 beqz a1 *)
  ldl. step. ldc 0x40. step.
  assert (B7 : bv_eqb (Z_to_bv 64 (Z.b2z (sh =? 7))) (Z_to_bv 64 0) = false) by (rewrite E7; reflexivity).
  rewrite B7; cbv iota. clear B7.
  (* 0x13234 bltu a2,a7 ; 0x13238 add s8,s5,s8 ; 0x1323c addi a1,zero,4 *)
  step. capF. step. step.
  (* 0x13240 .. 0x1324c: the size word 4 *)
  sbq (Lp sh ps). sbq (L + 1). sbq (L + 2). sbq (L + 3). c4 (Lp sh ps). lbq 4.
  (* 0x13250 ld s8,0(s2) ; addi s8,s8,4 ; add a0,s8,a6 ; sd s8,0(s2) *)
  ldl. step. step. sdl. fput.
  (* 0x13260 bltu a0,a7 ; 0x13264 add s8,s5,s8 ; 0x13268 .. 0x13274: the type word 4 *)
  step. capF. step.
  sbq (L + 4). sbq (L + 4 + 1). sbq (L + 4 + 2). sbq (L + 4 + 3). c4 (L + 4). lbq 4.
  ldl. step. sdl. fput.
  (* 0x13284 mv s6,s4 ; add a0,s8,a6 ; bltu a0,a7 ; add s8,s5,s8 ; 0x13294 .. 0x132a0: the value 0 *)
  step. step. step. capF. step.
  sbq (L + 4 + 4). sbq (L + 4 + 4 + 1). sbq (L + 4 + 4 + 2). sbq (L + 4 + 4 + 3). c4 (L + 4 + 4). lbq 0.
  ldl. step. sdl. fput.
  (* 0x132b0 negw a0,s8 ; andi s4,a0,7: the pad, 4 *)
  step. step.
  negpad.
  (* 0x132b8 add a0,s4,s8 ; lui a1,4 ; bltu a1,a0 *)
  step. step. step. capF.
  (* 0x132c4 add a0,s5,s8 ; mv a1,zero ; mv a2,s4 ; mv s8,a4 ; jal memset *)
  do 5 step.
  mset (L + 12) 4.
  (* 0x132d8 mv a4,s8 ; ld a7,0x70(sp) ; ld a6,0x78(sp) *)
  step. ldc 0x70. ldc 0x78.
  (* 0x132e4 ld a0,0(s2) ; add a0,a0,s4 ; sd a0,0(s2) *)
  ldl. step. sdl. fput.
  (* 0x132f0 j ; 0x13ee4 ld a5,0x68(sp) ; mv s4,s6 ; j *)
  step. ldc 0x68. step. step.
  eapply latch_ok; [eassumption | intros p Hp; right; exact Hp | | exact Hs | exact Hw | reflexivity | reflexivity | ].
  - rewrite img_same by (apply fp_other; cbn [fst]; unfold POD_PROP_PARAMS; lia).
    rewrite (pb_s7 E7). rewrite <- !app_assoc. reflexivity.
  - rewrite seen_snoc. cbn [fst]. replace (0 =? POD_PROP_PARAMS) with false by reflexivity.
    rewrite orb_false_r. reflexivity.
Qed.

(** ** 0x13e10 -> 0x13f64: an Int property `Int 7` (pod.h:413-418). The cell sp + 0x48 holds `seen_params` after
       this property (stored at 0x13354 / 0x13360), sp + 0x80 holds `first` (0x13370). *)
Lemma int_ok : forall K (f : bool) (sv A2 S8 : Z) r1 (ra t0 t1 t2 s1 a0 a1 a3 a5 s6 t3 t4 t5 t6 : word) m1,
  sh <> 7 -> suffix rest r1 -> pc_wf sh (ps ++ [(K, PInt 7)]) ->
  sv = Z.b2z (seen_of (ps ++ [(K, PInt 7)])) -> A2 = L + 8 - 16381 -> S8 = L + 8 ->
  (if f then overwrite (IM (B ++ prop_bytes sh (K, PInt 7))) (Z.to_nat 16396) (le4 (Z_to_bv 64 1))
   else IM (B ++ prop_bytes sh (K, PInt 7))) = pc_image (PbCut sh (ps ++ [(K, PInt 7)]) None) ->
  MQ sp m rest src pp lo ((0x80, Z.b2z f) :: (0x48, sv) :: XB) (IM ((B ++ le32 K) ++ le32 0)) S8 m1 ->
  evt rsegs (PQ (K, PInt 7) r1)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 336)) s1
             a0 a1 (Z_to_bv 64 A2) a3 (Z_to_bv 64 np) a5
             (Z_to_bv 64 (-16381)) (Z_to_bv 64 (-16385)) (Z_to_bv 64 (pp + 16384))
             (Z_to_bv 64 (cur rest src r1)) (Z_to_bv 64 (Z.of_nat (length r1))) (Z_to_bv 64 pp) s6
             (Z_to_bv 64 95) (Z_to_bv 64 S8) (Z_to_bv 64 MULT10) (Z_to_bv 64 (bv_unsigned sp + 280)) (Z_to_bv 64 10)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x13e10) fc None m1 (seg_rom rsegs)).
Proof.
  intros K f sv A2 S8 r1 ra t0 t1 t2 s1 a0 a1 a3 a5 s6 t3 t4 t5 t6 m1 H7 Hs Hw Hsv HA2 HS8 Himg MQ0.
  pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  destruct (Lp_rng sh ps HWF HPS) as (LP1 & LP2). pose proof (Lp_def sh ps) as LPD.
  (* 0x13e10 bltu a2,a7 ; 0x13e14 add s8,s5,s8 ; addi a1,zero,4 ; 0x13e1c .. 0x13e28: the size word 4 *)
  step. capF. step. step.
  sbq (L + 4 + 4). sbq (L + 4 + 4 + 1). sbq (L + 4 + 4 + 2). sbq (L + 4 + 4 + 3). c4 (L + 4 + 4). lbq 4.
  (* 0x13e2c ld s8,0(s2) ; addi s8,s8,4 ; add a0,s8,a6 ; sd s8,0(s2) *)
  ldl. step. step. sdl. fput.
  (* 0x13e3c bltu a0,a7 ; add s8,s5,s8 ; 0x13e44 .. 0x13e50: the type word 4 *)
  step. capF. step.
  sbq (L + 4 + 4 + 4). sbq (L + 4 + 4 + 4 + 1). sbq (L + 4 + 4 + 4 + 2). sbq (L + 4 + 4 + 4 + 3).
  c4 (L + 4 + 4 + 4). lbq 4.
  ldl. step. sdl. fput.
  (* 0x13e60 mv s6,s4 ; add a0,s8,a6 ; bltu a0,a7 ; add s8,s5,s8 ; addi a0,zero,7 ; the value 7 *)
  step. step. step. capF. step. step.
  sbq (L + 4 + 4 + 4 + 4). sbq (L + 4 + 4 + 4 + 4 + 1). sbq (L + 4 + 4 + 4 + 4 + 2).
  sbq (L + 4 + 4 + 4 + 4 + 3). c4 (L + 4 + 4 + 4 + 4). lbq 7.
  ldl. step. sdl. fput.
  (* 0x13e90 negw a0,s8 ; andi s4,a0,7: the pad, 4 *)
  step. step.
  negpad.
  (* 0x13e98 add a0,s4,s8 ; lui a1,4 ; bltu a1,a0 *)
  step. step. step. capF.
  (* 0x13ea4 add a0,s5,s8 ; mv a1,zero ; mv a2,s4 ; mv s1,a4 ; jal memset *)
  do 5 step.
  mset (L + 20) 4.
  (* 0x13eb8 mv a4,s1 ; ld a7,0x70(sp) ; ld a6,0x78(sp) *)
  step. ldc 0x70. ldc 0x78.
  (* 0x13ec4 ld a0,0(s2) ; add a0,a0,s4 ; sd a0,0(s2) *)
  ldl. step. sdl. fput.
  (* 0x13ed0 ld a0,0x80(sp) ; beqz a0 *)
  ldc 0x80. step.
  destruct f.
  - (* the first SPA_PROP_params: 0x13ed8 addi a0,zero,1 ; sw a0,0xc(s2) *)
    brF. step. stq 16396 4%nat.
    (* 0x13ee0 ld s1,0x48(sp) ; ld a5,0x68(sp) ; mv s4,s6 ; j *)
    ldc 0x48. ldc 0x68. step. step.
    eapply latch_ok; [eassumption | intros p Hp; right; right; right; exact Hp | | exact Hs | exact Hw
                      | reflexivity | reflexivity | exact Hsv].
    rewrite <- Himg. rewrite pb_int by exact H7. rewrite <- !app_assoc. reflexivity.
  - brT. ldc 0x48. ldc 0x68. step. step.
    eapply latch_ok; [eassumption | intros p Hp; right; right; right; exact Hp | | exact Hs | exact Hw
                      | reflexivity | reflexivity | exact Hsv].
    rewrite <- Himg. rewrite pb_int by exact H7. rewrite <- !app_assoc. reflexivity.
Qed.

(** ** 0x13f20 -> 0x13f64: the end of a params Struct (pod.h:434-437) *)
Definition XC : list (Z * Z) := (0x80, Z.b2z (first_of ps)) :: (0x48, 1) :: XB.

Lemma close_ok : forall es r (LEN AT c3 c4 : Z) Ib (ra t0 t1 t2 s1 a1 a2 a3 a5 s6 t3 t4 t5 t6 : word) m1,
  sh <> 7 -> suffix rest r -> Forall ent_wf es -> (length es <= 32)%nat ->
  LEN = Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) -> AT = L + 8 ->
  Ib = pc_image (PbCut sh ps (Some es)) -> c3 = cur rest src r -> c4 = Z.of_nat (length r) ->
  MQ sp m rest src pp lo XC Ib LEN m1 ->
  evt rsegs (PQ (POD_PROP_PARAMS, PStruct es) r)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 336)) s1
             (Z_to_bv 64 LEN) a1 a2 a3 (Z_to_bv 64 np) a5
             (Z_to_bv 64 (-16381)) (Z_to_bv 64 (-16385)) (Z_to_bv 64 (pp + 16384))
             (Z_to_bv 64 c3) (Z_to_bv 64 c4) (Z_to_bv 64 pp) s6
             (Z_to_bv 64 95) (Z_to_bv 64 AT) (Z_to_bv 64 MULT10) (Z_to_bv 64 (bv_unsigned sp + 280)) (Z_to_bv 64 10)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f20) fc None m1 (seg_rom rsegs)).
Proof.
  intros es r LEN AT c3 c4 Ib ra t0 t1 t2 s1 a1 a2 a3 a5 s6 t3 t4 t5 t6 m1 H7 Hs Hes Hel HLEN -> HIb Hc3 Hc4 MQ0.
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
  (* 0x13f20 subw a0,a0,s8 *)
  step. rewrite (subw_lit LEN (L + 8)) by lia.
  (* 0x13f24 add s8,s5,s8 ; addi a0,a0,-8 ; srli a1,a0,0x18 ; srli a2,a0,0x10 ; srli a3,a0,8 *)
  do 5 step.
  rewrite (unsigned_lit (LEN - (L + 8) + -8)) by lia.
  (* 0x13f38 .. 0x13f44: the size word, pod_patch32 *)
  sbq (L + 8). sbq (L + 8 + 1). sbq (L + 8 + 2). sbq (L + 8 + 3).
  lazymatch goal with
  | MQH : MQ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite (ow32 Ib (L + 8) (LEN - (L + 8) + -8)) in MQH by lia
  end.
  (* 0x13f48 ld a0,0x80(sp) ; beqz a0 *)
  ldc 0x80. step.
  destruct (first_of ps) eqn:EF.
  - (* the first SPA_PROP_params: has_params = params_struct = 1 *)
    assert (Hs0 : seen_of ps = false) by (unfold first_of in EF; apply negb_true_iff in EF; exact EF).
    brF. step. stq 16396 4%nat. stq 16400 4%nat.
    (* 0x13f5c ld s1,0x48(sp) ; ld a5,0x68(sp) *)
    ldc 0x48. ldc 0x68.
    eapply latch_ok; [eassumption | intros p Hp; right; right; right; exact Hp | | exact Hs
                      | apply struct_wf; assumption | exact Hc3 | exact Hc4 | ].
    + subst Ib. apply img_close_first; assumption.
    + rewrite seen_snoc. cbn [fst]. rewrite Z.eqb_refl, orb_true_r. reflexivity.
  - assert (Hs0 : seen_of ps = true) by (unfold first_of in EF; apply negb_false_iff in EF; exact EF).
    brT. ldc 0x48. ldc 0x68.
    eapply latch_ok; [eassumption | intros p Hp; right; right; right; exact Hp | | exact Hs
                      | apply struct_wf; assumption | exact Hc3 | exact Hc4 | ].
    + subst Ib. apply img_close_other; assumption.
    + rewrite seen_snoc. cbn [fst]. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

End Path.
