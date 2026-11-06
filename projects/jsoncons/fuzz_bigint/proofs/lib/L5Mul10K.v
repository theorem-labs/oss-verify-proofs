(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan AsanPlanCore AsanPlan AsanPlanSound Src0PlanKit AsanPlanSoundSums Src0Sums
     BigLinkBase BigLinkGlue BigLinkInlBase BigLinkShl BigLinkReduce BigLinkMulAlg BigLinkMul L5Defs L5Words L5Reduce L5ReduceG
     L5Core L5CoreKit L5CoreKitS L5CoreSpecs L5AReserve L5Reserve L5ResizeP L5Resize L5Mul10P L5Mul10T2 L5Mul10T.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigFactsBase BigFactsDigits.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5MULK.
Import L5CS.
Import L5MULP.
Import L5MULT2.
Import L5MULT.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

(* [comment removed for export] *)
Lemma mul10_after_resize
  (fx : FPState)
  (R : bvmap 5 word)
  (M : word -> option byte)
  (model : Model)
  (K : TSet)
  (LB : list (Z * Z))
  (cr : credit)
  (o : Z)
  (sp : Z)
  (r : Z)
  (fb : Z)
  (len : nat)
  (sto : L5.bstore)
  (ws : list Z)
  (Hlen : Z.of_nat len < 2 ^ 23)
  (RA : L5.ra_ok r)
  (H2 : getr R 2%bv = Z_to_bv 64 sp)
  (Lws : length ws = len)
  (Rws : Forall (fun w : Z => 0 <= w < 2 ^ 64) ws)
  (NEG : L5.bo_neg (L5.BO (fb) (len) (sto)) = false)
  (Ao : o mod 8 = 0)
  (Olo : sp <= o)
  (Ohi : o + 32 <= hl_sptop L)
  (WO : L5.writable RSEGS M o 32)
  (BLK : forall cap q : Z, sto = L5.BDyn cap q -> In (q, 8 * cap) LB)
  (KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) (LB' : list (Z * Z)) (cr' : credit), arith_post L LB cr M M' R R' o sp MUL10_SCR (L5.BO (fb) (len) (sto)) (10 * L5.limbs_val ws) g LB' cr' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') -> srealizes RSEGS SCFG (@cfg fx' R' r M' model') K)
  (Mh : m_halted model = None)
  (Ml : m_vm_lazy model = [])
  (A16 : sp mod 16 = 0)
  (SLO : hl_sptop L - 2 ^ 23 + (48 + (64 + (64 + (64 + (16 + 8224))))) <= sp)
  (SHI : sp <= hl_sptop L)
  (STOP : 140735340871680 <= hl_sptop L <= 2 ^ 47)
  (DEF : L5.defined M (sp - (48 + (64 + (64 + (64 + (16 + 8224)))))) (48 + (64 + (64 + (64 + (16 + 8224))))))
  (Hr : 0 <= r < 2 ^ 47)
  (He : r mod 2 = 0)
  (LBhi : forall bb : Z * Z, In bb LB -> (fst bb) + (snd bb) <= hl_ceil L)
  (LBwf : forall q c : Z, In (q, 8 * c) LB -> (4096 <= q /\ (q + 8 * c <= 65536 \/ 593920 <= q)) /\ q + 8 * c <= hl_ceil L /\ L5.defined M q (8 * c))
  (WR48 : BG.writable M (sp - 48) 48)
  (Hfb : 0 <= fb < 256)
  (OST : match sto with | L5.BInl v0 v1 => Z.testbit fb 0 = false /\ L5.u64_at RSEGS M (o + 16) v0 /\ L5.u64_at RSEGS M (o + 24) v1 /\ (len <= 2)%nat /\ 0 <= v0 < 2 ^ 64 /\ 0 <= v1 < 2 ^ 64 | L5.BDyn cap q => Z.testbit fb 0 = true /\ L5.u64_at RSEGS M (o + 16) cap /\ L5.u64_at RSEGS M (o + 24) q /\ Z.of_nat len <= cap /\ 1 <= cap <= 2 ^ 27 /\ q mod 8 = 0 /\ 4096 <= q /\ q + 8 * cap <= 2 ^ 47 /\ L5.hull_apart RSEGS q (8 * cap) end)
  (WOK : words_ok ws)
  (VB : 0 <= (val ws) < BigModel.W.M ^ Z.of_nat len)
  (Hlen27 : Z.of_nat len <= 2 ^ 27)
  (x0 : Z)
  (Hx0 : 0 <= x0 < 2 ^ 64)
  (X0nth : (1 <= len)%nat -> x0 = nth 0 ws 0)
  (RG1 : 0 <= bv_unsigned (getr R (reg 1)) < 2 ^ 64)
  (RG8 : 0 <= bv_unsigned (getr R (reg 8)) < 2 ^ 64)
  (RG9 : 0 <= bv_unsigned (getr R (reg 9)) < 2 ^ 64)
  (RG18 : 0 <= bv_unsigned (getr R (reg 18)) < 2 ^ 64)
  (RG19 : 0 <= bv_unsigned (getr R (reg 19)) < 2 ^ 64)
  (RG20 : 0 <= bv_unsigned (getr R (reg 20)) < 2 ^ 64)
  (E1 : bv_unsigned (getr R (reg 1)) = r)
  (R1 : bvmap 5 word)
  (M1 : word -> option byte)
  (K1 : forall x : nat, In x KS1 -> getr R1 (reg x) = getr R (reg x))
  (R1_2 : getr R1 (reg 2) = Z_to_bv 64 (sp - 48))
  (R1_8 : getr R1 (reg 8) = Z_to_bv 64 o)
  (R1_9 : getr R1 (reg 9) = Z_to_bv 64 10)
  (R1_18 : getr R1 (reg 18) = Z_to_bv 64 (o + 16))
  (R1_19 : getr R1 (reg 19) = Z_to_bv 64 x0)
  (R1_20 : getr R1 (reg 20) = Z_to_bv 64 (Z.of_nat len))
  (C8 : BG.u64_at M1 (sp - 8) (bv_unsigned (getr R (reg 1))))
  (C16 : BG.u64_at M1 (sp - 16) (bv_unsigned (getr R (reg 8))))
  (C24 : BG.u64_at M1 (sp - 24) (bv_unsigned (getr R (reg 9))))
  (C32 : BG.u64_at M1 (sp - 32) (bv_unsigned (getr R (reg 18))))
  (C40 : BG.u64_at M1 (sp - 40) (bv_unsigned (getr R (reg 19))))
  (C48 : BG.u64_at M1 (sp - 48) (bv_unsigned (getr R (reg 20))))
  (GR1 : mem_grows M M1)
  (FR1z : forall a : Z, 0 <= a < 2 ^ 64 -> ~ sp - 48 <= a < sp -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  (fx2 : FPState)
  (R2 : bvmap 5 word)
  (M2 : word -> option byte)
  (model2 : Model)
  (g : growth)
  (LB' : list (Z * Z))
  (cr' : credit)
  (POST : resize_post L LB cr M1 M2 R1 R2 o (sp - 48) (S len) (L5.BO (fb) (len) (sto)) ws g LB' cr')
  (MBV : model_but_vm model model2)
  (HH2 : hi_heap HI LB' cr' M2 (m_vmmaps model2))
  : srealizes RSEGS SCFG (@cfg fx2 R2 RET1 M2 model2) K.

Proof.
  set (V := val ws) in *.
  pose proof (L5C.halted_but_vm _ _ MBV) as Mh2. rewrite Mh in Mh2. pose proof (L5C.lazy_but_vm _ _ MBV) as Ml2. rewrite Ml in Ml2.
  destruct POST as [RP POST].
  assert (RL: resize_limbs ws (S len) = ws ++ [0]).
  { unfold resize_limbs. rewrite firstn_all2 by lia. rewrite Lws. replace (S len - len)%nat with 1%nat by lia. reflexivity. }
  rewrite RL in POST.
  (* [comment removed for export] *)
  assert (SIT: exists (fbR : Z) (stR : L5.bstore) (grown : bool) (W2 : list L5.range),
            L5.big_at RSEGS M2 o (L5.BO fbR (S len) stR) /\ fbR = (if grown then Z.lor fb 1 else fb)
            /\ L5C.obj_limbs RSEGS M2 (L5.BO fbR (S len) stR) (ws ++ [0])
            /\ L5C.hpres L LB (sp - 48) RESIZE_SCR ((o, 32) :: W2) M1 M2
            /\ (forall a rg, In rg W2 -> L5.in_rng rg a -> L5.bo_data o (L5.BO fb len sto) <= a < L5.bo_data o (L5.BO fb len sto) + 8 * (Z.of_nat len + 1) /\ grown = false)
            /\ (grown = false -> match sto, stR with L5.BDyn c q, L5.BDyn c' q' => c' = c /\ q' = q | L5.BInl _ _, L5.BInl _ _ => (len <= 1)%nat | _, _ => False end)
            /\ match g with
               | Same => grown = false /\ LB' = LB /\ cr' = cr /\ (L5.bo_dyn (L5.BO fb len sto) = true \/ (len <= 1)%nat)
               | Grown A cap => grown = true /\ stR = L5.BDyn cap A /\ len = 2%nat /\ cap = 8 /\ LB' = (A, 64) :: LB
                         /\ cr' = debit L cr 64 /\ L5C.fresh_block L LB M2 A 64 /\ Z.testbit fb 0 = false
               end).
  { destruct g as [|A cap].
    - destruct POST as (HG & HLB & HCR & (stR & OBR & OLR & MATCH) & HP). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data] in OBR, OLR, MATCH, HP.
      exists fb, stR, false, [(L5.bo_data o (L5.BO fb len sto) + 8 * Z.of_nat len, 8 * Z.max 0 (Z.of_nat (S len) - Z.of_nat len))].
      split. exact OBR. split. reflexivity. split. exact OLR. split. exact HP.
      split. { intros a rg [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [|reflexivity]. lia. }
      split. { intros _. destruct sto; destruct stR; try exact MATCH. destruct OBR as (_ & _ & _ & _ & _ & _ & HlR & _). cbn [L5.bo_len] in HlR. lia. }
      split. reflexivity. split. exact HLB. split. exact HCR. destruct HG as [Hd|Hl]. left; exact Hd. right; lia.
    - destruct POST as (B0 & H3 & Hcap & HLB' & Hcr' & FB & OBR & OLR & HP). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data] in OBR, OLR, HP. unfold L5.bo_dyn in B0. cbn [L5.bo_fb] in B0.
      assert (L2: len = 2%nat). { destruct sto as [v0 v1|c q]. destruct OST as (_ & _ & _ & Hl2 & _). lia. destruct OST as (B1 & _). rewrite B1 in B0. discriminate. }
      assert (CAP8: cap = 8). { rewrite Hcap, L2. reflexivity. }
      exists (Z.lor fb 1), (L5.BDyn cap A), true, [].
      split. exact OBR. split. reflexivity. split. exact OLR. split. exact HP.
      split. { intros a rg []. } split. { intros; discriminate. }
      split. reflexivity. split. reflexivity. split. exact L2. split. exact CAP8. split. rewrite HLB', CAP8. reflexivity. split. rewrite Hcr', CAP8. reflexivity.
      split. replace 64 with (8 * cap) by lia. exact FB. exact B0. }
  destruct SIT as (fbR & stR & grown & W2 & OBR & EfbR & OLR & HP & HW2 & MATCH & GCASE).
  set (data := L5.bo_data o (L5.BO fbR (S len) stR)) in *.
  pose proof OBR as (Q0 & HfbR & Q8 & QST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Q0, HfbR, Q8, QST.
  destruct OLR as (_ & _ & LIMR). cbn [L5.bo_st L5.bo_len] in LIMR.
  pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP) as SDEF. pose proof (fun a => L5C.hpres_cdef _ _ _ _ _ _ _ a HP) as CDEF. cbn beta in CDEF.
  unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in SDEF, CDEF.
  assert (NEGR: Z.testbit fbR 1 = false). { rewrite EfbR. destruct grown. rewrite lor1_bit1. exact NEG. exact NEG. }
  (* [comment removed for export] *)
  assert (DG: 4096 <= data /\ data mod 8 = 0 /\ data + 8 * (Z.of_nat len + 1) <= 2 ^ 47 /\ (data + 8 * (Z.of_nat len + 1) <= 0x10000 \/ 0x91000 <= data)
              /\ ((o + 16 = data /\ (len <= 1)%nat /\ exists u0 u1, stR = L5.BInl u0 u1) \/ (data + 8 * (Z.of_nat len + 1) <= hl_ceil L /\ exists cR qR, stR = L5.BDyn cR qR /\ In (qR, 8 * cR) LB' /\ Z.of_nat len + 1 <= cR))
              /\ L5.limbs_at RSEGS M2 data (ws ++ [0])).
  { subst data. destruct stR as [u0 u1|cR qR]; cbn [L5.bo_data L5.bo_st].
    - destruct QST as (_ & Q16 & Q24 & HlR & _). split. lia. split. rewrite <- Z.add_mod_idemp_l by lia. rewrite Ao. reflexivity. split. lia. split. lia.
      split. { left. split. reflexivity. split. lia. exists u0, u1. reflexivity. }
      rewrite LIMR. intros i Hi. rewrite length_firstn in Hi. cbn [length] in Hi. rewrite nth_firstn. replace (Nat.ltb i (S len)) with true by (symmetry; apply Nat.ltb_lt; lia).
      destruct i as [|[|i]]. rewrite Z.mul_0_r, Z.add_0_r. exact Q16. replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) by lia. exact Q24. lia.
    - destruct QST as (_ & Q16 & Q24 & HlcR & HcR & AqR & QloR & QhiR). split. lia. split. exact AqR. split. lia.
      assert (INB: In (qR, 8 * cR) LB').
      { destruct g. destruct GCASE as (G0 & -> & _). destruct sto as [v0 v1|c q]. destruct (MATCH G0). destruct (MATCH G0) as [-> ->]. exact (BLK c q eq_refl).
        destruct GCASE as (_ & SR & _ & HC8 & -> & _). injection SR; intros EC EQ. rewrite EC, EQ, HC8. left; reflexivity. }
      split. { destruct g. destruct GCASE as (G0 & -> & _). destruct (LBwf qR cR INB) as ((X1a & X1b) & X1c & _). lia.
               destruct GCASE as (_ & SR & L2'' & C8'' & _ & _ & ((BR0 & BR1 & _) & _) & _). injection SR; intros; subst. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in BR1. lia. }
      split. { right. split. 2: { exists cR, qR. split. reflexivity. split. exact INB. lia. }
               destruct g. destruct GCASE as (G0 & -> & _). destruct (LBwf qR cR INB) as (X1 & X2 & X3). lia.
               destruct GCASE as (_ & SR & L2' & _ & _ & _ & ((BR0 & BR1 & BR2 & BR3 & BR4) & _) & _). injection SR; intros; subst. lia. }
      exact LIMR. }
  destruct DG as (Dlo & Da & Dhi & Dimg & DW & LIM2).
  assert (LwsA: length (ws ++ [0]) = S len). { rewrite length_app, Lws. cbn. lia. }
  assert (DDEF: L5.defined M2 data (8 * (Z.of_nat len + 1))).
  { pose proof (L5KS.limbs_at_defined_hull M2 data _ LIM2 ltac:(lia) ltac:(apply L5KS.hull_apart_of; rewrite LwsA; destruct Dimg; [left|right]; lia) ltac:(rewrite LwsA; lia)) as D. rewrite LwsA in D.
    replace (8 * (Z.of_nat len + 1)) with (8 * Z.of_nat (S len)) by lia. exact D. }
  (* [comment removed for export] *)
  assert (CL: forall a, sp - 48 <= a < 2 ^ 47 -> ~ (o <= a < o + 32) -> ~ (data <= a < data + 8 * (Z.of_nat len + 1)) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hna Hnd. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). apply (L5C.kept_stack L LB (sp - 48) _ ((o, 32) :: W2)). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. lia.
    unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia. lia. rewrite (ly_errno L LY). lia. lia.
    apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. intros rg Hrg Hin. destruct (HW2 a rg Hrg Hin) as [X G0].
    specialize (MATCH G0). destruct sto as [v0 v1|c q]; destruct stR as [u0 u1|cR qR]; cbn [L5.bo_data L5.bo_st] in X; try contradiction; try lia.
    destruct MATCH as [-> ->]. subst data. cbn [L5.bo_data L5.bo_st] in Hnd. lia. }
  assert (T1: forall a v, sp - 48 <= a -> a + 8 <= sp -> BG.u64_at M1 a v -> BG.u64_at M2 a v).
  { intros a v H1a H2a Hu. eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. destruct DW as [(D1 & _)|(D1 & _)]; lia. lia. lia. exact Hu. }
  assert (WR2 : BG.writable M2 (sp - 48) 48).
  { change (L5.writable RSEGS M2 (sp - 48) 48). eapply (L5C.writable_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. destruct DW as [(D1 & _)|(D1 & _)]; lia. lia. lia.
    eapply L5.writable_grows. exact GR1. exact WR48. }
  assert (AT: at_ret1 R2 M2 o x0 (Z.of_nat len) sp (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9)))
                (bv_unsigned (getr R (reg 18))) (bv_unsigned (getr R (reg 19))) (bv_unsigned (getr R (reg 20)))).
  { unfold at_ret1.
    split. { rewrite <- L5K.rl8, (RP 8%bv ltac:(cbn; tauto)), L5K.rl8. exact R1_8. }
    split. { rewrite <- L5K.rl9, (RP 9%bv ltac:(cbn; tauto)), L5K.rl9. exact R1_9. }
    split. { rewrite <- L5K.rl18, (RP 18%bv ltac:(cbn; tauto)), L5K.rl18. exact R1_18. }
    split. { rewrite <- L5K.rl19, (RP 19%bv ltac:(cbn; tauto)), L5K.rl19. exact R1_19. }
    split. { rewrite <- L5K.rl20, (RP 20%bv ltac:(cbn; tauto)), L5K.rl20. exact R1_20. }
    split. { rewrite <- L5K.rl2, (RP 2%bv ltac:(cbn; tauto)), L5K.rl2. exact R1_2. }
    split. apply T1; [lia|lia|exact C8]. split. apply T1; [lia|lia|exact C16]. split. apply T1; [lia|lia|exact C24].
    split. apply T1; [lia|lia|exact C32]. split. apply T1; [lia|lia|exact C40]. split. apply T1; [lia|lia|exact C48]. lia. }
  (* [comment removed for export] *)
  set (WF := (o, 32) :: match g with Same => [(L5.bo_data o (L5.BO fb len sto), 8 * (Z.of_nat len + 1))] | Grown _ _ => [] end).
  assert (KEEP: forall a, L5C.kept L LB sp (48 + (64 + (64 + (64 + (16 + 8224))))) WF a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a KA. pose proof KA as (Ha & CA & NE & OW). apply L5C.outside_cons_inv in OW as [NW OW2]. unfold L5.in_rng in NW. cbn [fst snd] in NW.
    rewrite (L5C.hpres_kept _ _ _ _ _ _ _ a HP). apply FR1z. lia.
    { destruct CA as [IB|[[S1 S2]|IM]]. destruct IB as (bb & Hb & Hin). pose proof (LBhi bb Hb). lia. lia. rewrite (ly_img_hi L LY) in IM. lia. }
    eapply L5C.kept_inner. exact KA. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia. lia.
    intros _. apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. intros rg Hrg Hin. destruct (HW2 a rg Hrg Hin) as [X G0].
    subst WF. destruct g. apply L5C.outside_cons_inv in OW2 as [NW2 _]. unfold L5.in_rng in NW2. cbn [fst snd] in NW2. lia. destruct GCASE as (G1 & _). rewrite G0 in G1. discriminate. }
  (* [comment removed for export] *)
  assert (KD: forall a, L5C.kept L LB sp (48 + (64 + (64 + (64 + (16 + 8224))))) WF a -> ~ (data <= a < data + 8 * (Z.of_nat len + 1))).
  { intros a KA Hin. pose proof KA as (Ha & CA & NE & OW). apply L5C.outside_cons_inv in OW as [NW OW2]. unfold L5.in_rng in NW. cbn [fst snd] in NW.
    subst WF. destruct g.
    - destruct GCASE as (G0 & _). apply L5C.outside_cons_inv in OW2 as [NW2 _]. unfold L5.in_rng in NW2. cbn [fst snd] in NW2.
      subst data. destruct sto as [v0 v1|c q]; destruct stR as [u0 u1|cR qR]; try (destruct (MATCH G0); fail); cbn [L5.bo_data L5.bo_st] in *. lia.
      destruct (MATCH G0) as [-> ->]. lia.
    - destruct GCASE as (_ & SR & L2' & _ & _ & _ & (FBR & BA & _) & _). subst data. rewrite SR in Hin. cbn [L5.bo_data L5.bo_st] in Hin.
      apply (L5C.kept_not_fresh L LB sp _ _ a A 64 KA BA). exact (proj1 (proj2 FBR)). exact (proj2 (proj2 (proj2 (proj2 FBR)))). exact LBhi. lia. }
  assert (CD2: forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp (48 + (64 + (64 + (64 + (16 + 8224))))) a -> ~ in_errno L a ->
               M (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None).
  { intros a Ha CA NE DM. apply (CDEF a Ha). eapply L5K.client_inner. exact CA. lia. lia. exact NE. apply GR1. exact DM. }
  assert (REGS: forall (R3 : bvmap 5 word) (ks : list nat),
            (forall x, In x ks -> getr R3 (reg x) = getr R2 (reg x)) -> incl [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat ks ->
            getr R3 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))) ->
            getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9))) -> getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R (reg 18))) ->
            getr R3 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R (reg 19))) -> getr R3 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R (reg 20))) ->
            regs_preserved R R3).
  { intros R3 ks K3 Hincl S2 S8 S9 S18 S19 S20. apply L5K.regs_preserved_by_index. intros i Hi.
    cbn in Hi. destruct Hi as [<-|Hi]. { rewrite S2, <- H2, L5K.rl2. reflexivity. }
    destruct Hi as [<-|Hi]. { rewrite (K3 3%nat) by (apply Hincl; cbn; tauto). rewrite <- L5K.rl3, (RP 3%bv) by (cbn; tauto). rewrite L5K.rl3. apply (K1 3%nat). apply L5K.In_of_mem; reflexivity. }
    destruct Hi as [<-|Hi]. { rewrite (K3 4%nat) by (apply Hincl; cbn; tauto). rewrite <- L5K.rl4, (RP 4%bv) by (cbn; tauto). rewrite L5K.rl4. apply (K1 4%nat). apply L5K.In_of_mem; reflexivity. }
    destruct Hi as [<-|Hi]. { rewrite S8. symmetry. apply BG.word_of_unsigned. reflexivity. }
    destruct Hi as [<-|Hi]. { rewrite S9. symmetry. apply BG.word_of_unsigned. reflexivity. }
    destruct Hi as [<-|Hi]. { rewrite S18. symmetry. apply BG.word_of_unsigned. reflexivity. }
    destruct Hi as [<-|Hi]. { rewrite S19. symmetry. apply BG.word_of_unsigned. reflexivity. }
    destruct Hi as [<-|Hi]. { rewrite S20. symmetry. apply BG.word_of_unsigned. reflexivity. }
    assert (G: forall j, In j [21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg j) = getr R (reg j)).
    { intros j Hj.
      assert (M2j: In j ks) by (apply Hincl; cbn in Hj |- *; tauto).
      assert (M1j: In j KS1) by (pose proof Hj as H'; L5K.inlist H').
      assert (MCj: In j L5K.CS) by (pose proof Hj as H'; L5K.inlist H').
      rewrite (K3 j M2j). rewrite (L5K.regs_preserved_index R1 R2 j RP MCj). apply (K1 j M1j). }
    apply G. L5K.inlist Hi. }
  assert (SDEF_of: forall M5 : word -> option byte, (forall a, sp - (48 + (64 + (64 + (64 + (16 + 8224))))) <= a < sp -> M5 (Z_to_bv 64 a) <> None \/ M5 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) ->
                   mem_grows M2 M5 -> L5.defined M5 (sp - (48 + (64 + (64 + (64 + (16 + 8224)))))) (48 + (64 + (64 + (64 + (16 + 8224)))))).
  { intros M5 HM GR i Hi. apply GR.
    destruct (Z_lt_le_dec (sp - (48 + (64 + (64 + (64 + (16 + 8224))))) + i) (sp - 48)) as [Hlt|Hge].
    - replace (sp - (48 + (64 + (64 + (64 + (16 + 8224))))) + i) with (sp - 48 - (64 + (64 + (64 + (16 + 8224)))) + i) by lia. apply SDEF. lia.
    - rewrite CL. apply GR1. apply DEF. lia. lia. lia. destruct DW as [(D1 & _)|(D1 & _)]; lia. }
  (* [comment removed for export] *)
  set (td := match stR with L5.BDyn _ _ => true | L5.BInl _ _ => false end).
  assert (BtR: Z.testbit fbR 0 = td). { subst td. destruct stR; destruct QST as (B & _); exact B. }
  assert (Q24: td = true -> BG.u64_at M2 (o + 24) data /\ 4096 <= data < 2 ^ 47 /\ data mod 8 = 0).
  { subst td data. destruct stR as [w0 w1|c q]. intros; discriminate. intros _. destruct QST as (_ & _ & Q24' & HlcR & HcR & AqR & QloR & QhiR). cbn [L5.bo_data L5.bo_st].
    split. exact Q24'. split. lia. exact AqR. }
  assert (Edata: (if td then data else o + 16) = data). { subst td data. destruct stR; reflexivity. }
  (* [comment removed for export] *)
  assert (DEFO2: L5.defined M2 o 32).
  { intros i Hi. apply (CDEF (o + i)). lia. right; left. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. lia.
    unfold in_errno. rewrite (ly_errno L LY). lia. apply GR1. apply (store_ok1_defined M (o + i)). lia. unfold L5KS.IMG_HI; lia. apply (WO i 1%nat). lia. cbn. lia. }
  (* [comment removed for export] *)
  assert (LBwf2: forall q c, In (q, 8 * c) LB' -> (4096 <= q /\ (q + 8 * c <= 0x10000 \/ 0x91000 <= q)) /\ q + 8 * c <= hl_ceil L /\ L5.defined M2 q (8 * c)).
  { intros q c Hin. pose proof (proj1 (hio_wf L SCFG HI HIok LB' cr' M2 _ HH2) _ Hin) as ((Qa & Qb & Qc & Qd & Qe) & QD & _). cbn [fst snd] in Qa, Qb, Qe, QD.
    rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Qb. split. split. exact Qa. exact Qb. split. exact Qe. exact QD. }
  (* [comment removed for export] *)
  assert (TAILK: forall (fx4 : FPState) R4 M4,
    (forall x, In x KS2 -> In x KSIT -> getr R4 (reg x) = getr R2 (reg x)) ->
    getr R4 (reg 2) = Z_to_bv 64 (sp - 48) -> getr R4 (reg 8) = Z_to_bv 64 o -> getr R4 (reg 9) = Z_to_bv 64 10 ->
    getr R4 (reg 10) = Z_to_bv 64 (8 * Z.of_nat len) -> bv_unsigned (getr R4 (reg 11)) = mcarry 10 V len -> getr R4 (reg 18) = Z_to_bv 64 data ->
    limbs M4 data (wordi (10 * V)) 0 len ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (data <= a < data + 8 * Z.of_nat len) -> M4 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) -> mem_grows M2 M4 ->
    srealizes RSEGS SCFG (mkCfg (st fx4 R4 TAIL M4) model2) K).
  { intros fx4 R4 M4 K4 R4_2 R4_8 R4_9 R4_10 R4_11 R4_18 LIMBS4 MF4 GR4.
      apply (L5MULT.mul10_tail L HI LY HIok fx R M model K LB cr o sp r fb len sto ws Hlen RA Lws Rws Ao Olo Ohi KONT A16 SLO SHI STOP Hr He Hfb VB Hlen27 x0 Hx0 X0nth RG1 RG8 RG9 RG18 RG19 RG20 E1 R2 M2 model2 g LB' cr' MBV HH2 Mh2 Ml2 RL fbR stR grown EfbR MATCH GCASE Q0 HfbR Q8 QST NEGR Dlo Da Dhi Dimg DW LwsA DDEF WR2 AT KEEP KD CD2 REGS SDEF_of BtR Edata DEFO2 LBwf2 fx4 R4 M4 K4 R4_2 R4_8 R4_9 R4_10 R4_11 R4_18 LIMBS4 MF4 GR4). }
  (* [comment removed for export] *)
  destruct (Nat.eq_dec len 0) as [LEN0|LENP].
  + destruct (p2_run td true fx2 R2 M2 o x0 (Z.of_nat len) sp _ _ _ _ _ _ fbR data AT ltac:(lia) ltac:(lia) Hx0 ltac:(lia) A16 ltac:(lia) ltac:(lia) WR2 Ao Olo Q0 HfbR BtR Q24)
      as (fx3 & R3 & M3 & MS3 & K3 & R3_2 & R3_8 & R3_9 & R3_10 & R3_11 & _ & R3_18 & R3_19 & R3_20 & MM3 & GR3).
    eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
    rewrite Edata in R3_18.
    apply (TAILK fx3 R3 M3). { intros x Hx _. apply K3. exact Hx. } exact R3_2. exact R3_8. exact R3_9. exact R3_10.
    { rewrite R3_11, LEN0, mcarry_0. apply BG.unsigned_lit. lia. } exact R3_18.
    { intros j Hj. lia. } { intros a _ _. apply MM3. } exact GR3.
  + destruct (p2_run td false fx2 R2 M2 o x0 (Z.of_nat len) sp _ _ _ _ _ _ fbR data AT ltac:(lia) ltac:(lia) Hx0 ltac:(lia) A16 ltac:(lia) ltac:(lia) WR2 Ao Olo Q0 HfbR BtR Q24)
      as (fx3 & R3 & M3 & MS3 & K3 & R3_2 & R3_8 & R3_9 & R3_10 & R3_11 & RL3 & R3_18 & R3_19 & R3_20 & MM3 & GR3).
    destruct (RL3 eq_refl) as (R3_12 & R3_13 & R3_14). rewrite Edata in R3_12, R3_14, R3_18.
    eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
    assert (NW: (nwords V <= len)%nat). { apply (proj2 (nwords_le_iff V len ltac:(lia))). lia. }
    destruct (loop_run (len - 1) 0 len fx3 R3 M3 data V ltac:(lia) ltac:(lia) ltac:(lia) Dlo ltac:(lia) R3_13
                ltac:(rewrite R3_11, mcarry_0; apply BG.unsigned_lit; lia)
                ltac:(rewrite R3_12; rewrite BG.unsigned_lit by lia; lia)
                ltac:(rewrite R3_14; f_equal; lia)
                ltac:(rewrite R3_19; rewrite BG.unsigned_lit by lia; rewrite (X0nth ltac:(lia)); symmetry; exact (wordi_val ws 0 WOK)))
      as (fx4 & R4 & M4 & MS4 & K4 & R4_11 & R4_12 & R4_13 & R4_14 & R4_19 & L1 & L2 & MF4 & GR4).
    { change (L5.writable RSEGS M3 data (8 * (Z.of_nat len + 1))). apply L5C.writable_of_defined; [|lia|lia]. eapply L5.defined_grows. exact GR3. exact DDEF. }
    { intros j Hj. lia. }
    { intros j Hj. eapply (BG.u64_at_frame M2 M3). lia. lia. intros k Hk. apply MM3.
      pose proof (LIM2 j ltac:(rewrite LwsA; lia)) as X.
      destruct (Nat.eq_dec j len) as [->|NE].
      - rewrite app_nth2 in X by lia. rewrite Lws, Nat.sub_diag in X. cbn [nth] in X. replace (wordi V len) with 0 by (symmetry; apply wordi_high; [lia|exact NW]). exact X.
      - rewrite app_nth1 in X by lia. replace (wordi V j) with (nth j ws 0) by (symmetry; exact (wordi_val ws j WOK)). exact X. }
    eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS4.
    apply (TAILK fx4 R4 M4). { intros x Hx HxI. rewrite (K4 x HxI). apply K3. exact Hx. }
    { rewrite (K4 2%nat) by (apply L5K.In_of_mem; reflexivity). exact R3_2. }
    { rewrite (K4 8%nat) by (apply L5K.In_of_mem; reflexivity). exact R3_8. }
    { rewrite (K4 9%nat) by (apply L5K.In_of_mem; reflexivity). exact R3_9. }
    { rewrite (K4 10%nat) by (apply L5K.In_of_mem; reflexivity). exact R3_10. }
    exact R4_11. { rewrite (K4 18%nat) by (apply L5K.In_of_mem; reflexivity). exact R3_18. }
    exact L1. { intros a Ha Hna. rewrite MF4. apply MM3. rewrite BG.unsigned_lit by lia. lia. } { eapply mem_grows_trans. exact GR3. exact GR4. }
Qed.

End WithHeap.
End SCFG_1.

End L5MULK.
