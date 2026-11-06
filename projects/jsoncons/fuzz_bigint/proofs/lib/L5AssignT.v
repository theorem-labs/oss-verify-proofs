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
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore AsanPlanSoundSums Src0Sums
     BigLinkBase BigLinkGlue BigLinkInlBase BigLinkShl BigLinkReduce L5Defs L5Core L5CoreKit L5CoreKitS L5CoreSpecs L5AReserve L5Reserve L5ResizeP L5Resize L5AssignP.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ASGT.
Import L5CS.
Import L5ASGP.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Lemma assign_fb_eq fb fb' (n : nat) (grown : bool) : (1 <= n)%nat ->
  assign_fb fb fb' n grown = assign_flags (if grown then Z.lor fb 1 else fb) fb'.
Proof. intros Hn. unfold assign_fb, assign_flags. destruct n. lia. cbn [Nat.eqb]. apply Z.lor_comm. Qed.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

(* [comment removed for export] *)
Lemma assign_tail
  (fx : FPState)
  (R : bvmap 5 word)
  (M : word -> option byte)
  (model : Model)
  (K : TSet)
  (LB : list (Z * Z))
  (cr : credit)
  (o : Z)
  (o' : Z)
  (sp : Z)
  (r : Z)
  (fb : Z)
  (len : nat)
  (sto : L5.bstore)
  (fb' : Z)
  (len' : nat)
  (sto' : L5.bstore)
  (ws' : list Z)
  (Hn : Z.of_nat len' <= 2 ^ 23)
  (CAP : L5.bo_dyn (L5.BO (fb) (len) (sto)) = true -> Z.of_nat len' <= L5.bo_cap (L5.BO (fb) (len) (sto)))
  (CR : (3 <= len')%nat -> L5.bo_dyn (L5.BO (fb) (len) (sto)) = false -> credit_ok L cr (8 * round_up (Z.of_nat len')))
  (RA : L5.ra_ok r)
  (Ao : o mod 8 = 0)
  (Olo : sp <= o)
  (Ohi : o + 32 <= hl_sptop L)
  (BLK : forall cap q : Z, sto = L5.BDyn cap q -> In (q, 8 * cap) LB)
  (Lws' : length ws' = len')
  (Rws' : Forall (fun w : Z => 0 <= w < 2 ^ 64) ws')
  (Vws' : match sto' with | L5.BInl v0 v1 => ws' = firstn len' [v0; v1] | L5.BDyn _ q => L5.limbs_at RSEGS M q ws' end)
  (Ao' : o' mod 8 = 0)
  (Olo' : sp <= o')
  (Ohi' : o' + 32 <= hl_sptop L)
  (BLK' : forall cap q : Z, sto' = L5.BDyn cap q -> In (q, 8 * cap) LB)
  (APO : o + 32 <= o' \/ o' + 32 <= o)
  (APQ : forall c q c' q' : Z, sto = L5.BDyn c q -> sto' = L5.BDyn c' q' -> q + 8 * c <= q' \/ q' + 8 * c' <= q)
  (KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) (LB' : list (Z * Z)) (cr' : credit), assign_post L LB cr M M' R R' o o' sp (L5.BO (fb) (len) (sto)) (L5.BO (fb') (len') (sto')) ws' g LB' cr' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') -> srealizes RSEGS SCFG (@cfg fx' R' r M' model') K)
  (A16 : sp mod 16 = 0)
  (SLO : hl_sptop L - 2 ^ 23 + (48 + (64 + (64 + (64 + (16 + 8224))))) <= sp)
  (SHI : sp <= hl_sptop L)
  (STOP : 140735340871680 <= hl_sptop L <= 2 ^ 47)
  (Hr : 0 <= r < 2 ^ 47)
  (He : r mod 2 = 0)
  (LBhi : forall bb : Z * Z, In bb LB -> (fst bb) + (snd bb) <= hl_ceil L)
  (LBwf : forall q c : Z, In (q, 8 * c) LB -> (4096 <= q /\ (q + 8 * c <= 65536 \/ 593920 <= q)) /\ q + 8 * c <= hl_ceil L /\ L5.defined M q (8 * c))
  (Hfb : 0 <= fb < 256)
  (OST : match sto with | L5.BInl v0 v1 => Z.testbit fb 0 = false /\ L5.u64_at RSEGS M (o + 16) v0 /\ L5.u64_at RSEGS M (o + 24) v1 /\ (len <= 2)%nat /\ 0 <= v0 < 2 ^ 64 /\ 0 <= v1 < 2 ^ 64 | L5.BDyn cap q => Z.testbit fb 0 = true /\ L5.u64_at RSEGS M (o + 16) cap /\ L5.u64_at RSEGS M (o + 24) q /\ Z.of_nat len <= cap /\ 1 <= cap <= 2 ^ 27 /\ q mod 8 = 0 /\ 4096 <= q /\ q + 8 * cap <= 2 ^ 47 /\ L5.hull_apart RSEGS q (8 * cap) end)
  (O0' : L5.u8_at RSEGS M o' fb')
  (Hfb' : 0 <= fb' < 256)
  (OST' : match sto' with | L5.BInl v0 v1 => Z.testbit fb' 0 = false /\ L5.u64_at RSEGS M (o' + 16) v0 /\ L5.u64_at RSEGS M (o' + 24) v1 /\ (len' <= 2)%nat /\ 0 <= v0 < 2 ^ 64 /\ 0 <= v1 < 2 ^ 64 | L5.BDyn cap q => Z.testbit fb' 0 = true /\ L5.u64_at RSEGS M (o' + 16) cap /\ L5.u64_at RSEGS M (o' + 24) q /\ Z.of_nat len' <= cap /\ 1 <= cap <= 2 ^ 27 /\ q mod 8 = 0 /\ 4096 <= q /\ q + 8 * cap <= 2 ^ 47 /\ L5.hull_apart RSEGS q (8 * cap) end)
  (y24 : Z)
  (Hy24 : 0 <= y24 < 2 ^ 64)
  (Ey24 : match sto' with | L5.BInl _ v1 => y24 = v1 | L5.BDyn _ q' => y24 = q' end)
  (Hlen : Z.of_nat len <= 2 ^ 27)
  (RG1 : 0 <= bv_unsigned (getr R (reg 1)) < 2 ^ 64)
  (RG8 : 0 <= bv_unsigned (getr R (reg 8)) < 2 ^ 64)
  (RG9 : 0 <= bv_unsigned (getr R (reg 9)) < 2 ^ 64)
  (RG18 : 0 <= bv_unsigned (getr R (reg 18)) < 2 ^ 64)
  (RG19 : 0 <= bv_unsigned (getr R (reg 19)) < 2 ^ 64)
  (RG20 : 0 <= bv_unsigned (getr R (reg 20)) < 2 ^ 64)
  (E1 : bv_unsigned (getr R (reg 1)) = r)
  (NEQ : o <> o')
  (fx2 : FPState)
  (R2 : bvmap 5 word)
  (M2 : word -> option byte)
  (model2 : Model)
  (g : growth)
  (LB' : list (Z * Z))
  (cr' : credit)
  (MBV : model_but_vm model model2)
  (HH2 : hi_heap HI LB' cr' M2 (m_vmmaps model2))
  (Mh2 : m_halted model2 = None)
  (Ml2 : m_vm_lazy model2 = [])
  (fbR : Z)
  (stR : L5.bstore)
  (grown : bool)
  (EfbR : fbR = (if grown then Z.lor fb 1 else fb))
  (BfbR : Z.testbit fbR 0 = grown || Z.testbit fb 0)
  (DDST : L5.defined M2 (L5.bo_data o (L5.BO (fbR) (len') (stR))) (8 * Z.of_nat len'))
  (DSThi : (L5.bo_data o (L5.BO (fbR) (len') (stR))) + 8 * Z.of_nat len' <= 2 ^ 47)
  (DSTlo : 4096 <= (L5.bo_data o (L5.BO (fbR) (len') (stR))))
  (GCASE : match g with | Same => grown = false /\ LB' = LB /\ cr' = cr /\ (L5.bo_dyn (L5.BO (fb) (len) (sto)) = true \/ (len' <= 2)%nat) /\ match sto with | L5.BInl _ _ => match stR with | L5.BInl _ _ => (len' <= 2)%nat | L5.BDyn _ _ => False end | L5.BDyn c q => match stR with | L5.BInl _ _ => False | L5.BDyn c' q' => c' = c /\ q' = q end end | Grown A cap => grown = true /\ stR = L5.BDyn cap A /\ (3 <= len')%nat /\ cap = round_up (Z.of_nat len') /\ LB' = (A, 8 * cap) :: LB /\ cr' = debit L cr (8 * cap) /\ L5C.fresh_block L LB M2 A (8 * cap) /\ Z.testbit fb 0 = false end)
  (Q0 : L5.u8_at RSEGS M2 o fbR)
  (HfbR : 0 <= fbR < 256)
  (Q8 : L5.u64_at RSEGS M2 (o + 8) (Z.of_nat len'))
  (QST : match stR with | L5.BInl v0 v1 => Z.testbit fbR 0 = false /\ L5.u64_at RSEGS M2 (o + 16) v0 /\ L5.u64_at RSEGS M2 (o + 24) v1 /\ (len' <= 2)%nat /\ 0 <= v0 < 2 ^ 64 /\ 0 <= v1 < 2 ^ 64 | L5.BDyn cap q => Z.testbit fbR 0 = true /\ L5.u64_at RSEGS M2 (o + 16) cap /\ L5.u64_at RSEGS M2 (o + 24) q /\ Z.of_nat len' <= cap /\ 1 <= cap <= 2 ^ 27 /\ q mod 8 = 0 /\ 4096 <= q /\ q + 8 * cap <= 2 ^ 47 /\ L5.hull_apart RSEGS q (8 * cap) end)
  (DHI : forall a : Z, grown = false -> L5.bo_data o (L5.BO (fb) (len) (sto)) <= a < L5.bo_data o (L5.BO (fb) (len) (sto)) + 8 * Z.max (Z.of_nat len') (Z.of_nat len) -> a < hl_ceil L \/ o + 16 <= a < o + 32)
  (WR2 : BG.writable M2 (sp - 48) 48)
  (AT : at_ret1 R2 M2 o y24 (Z.of_nat len') o' fb' sp (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9))) (bv_unsigned (getr R (reg 18))) (bv_unsigned (getr R (reg 19))) (bv_unsigned (getr R (reg 20))))
  (KEEP : forall a : Z, L5C.kept L LB sp (48 + (64 + (64 + (64 + (16 + 8224))))) ((o, 32) :: match g with | Same => [(L5.bo_data o (L5.BO (fb) (len) (sto)), 8 * Z.max (Z.of_nat len') (Z.of_nat len))] | Grown _ _ => [] end) a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  (CD2 : forall a : Z, 0 <= a < 2 ^ 64 -> client_addr L LB sp (48 + (64 + (64 + (64 + (16 + 8224))))) a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None)
  (REGS : forall (R3 : bvmap 5 word) (ks : list nat), (forall x : nat, In x ks -> getr R3 (reg x) = getr R2 (reg x)) -> incl [3%nat; 4%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat] ks -> getr R3 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))) -> getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9))) -> getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R (reg 18))) -> getr R3 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R (reg 19))) -> getr R3 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R (reg 20))) -> regs_preserved R R3)
  (SDEF_of : forall M5 : word -> option byte, (forall a : Z, sp - (48 + (64 + (64 + (64 + (16 + 8224))))) <= a < sp -> M5 (Z_to_bv 64 a) <> None \/ M5 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) -> mem_grows M2 M5 -> L5.defined M5 (sp - (48 + (64 + (64 + (64 + (16 + 8224)))))) (48 + (64 + (64 + (64 + (16 + 8224))))))
  (LENP : len' <> 0%nat)
  : srealizes RSEGS SCFG (@cfg fx2 R2 RET1 M2 model2) K.

Proof.
  set (dst := L5.bo_data o (L5.BO fbR len' stR)) in *.
  set (td := match stR with L5.BDyn _ _ => true | L5.BInl _ _ => false end).
  set (od := L5.bo_dyn (L5.BO fb' len' sto')). set (src := L5.bo_data o' (L5.BO fb' len' sto')).
  assert (BtR: Z.testbit fbR 0 = td). { subst td. destruct stR; destruct QST as (B & _); exact B. }
  assert (BtO: Z.testbit fb' 0 = od). { subst od. reflexivity. }
  assert (Q24: td = true -> BG.u64_at M2 (o + 24) dst).
  { subst td dst. destruct stR as [w0 w1|c q]. discriminate. intros _. destruct QST as (_ & _ & Q24 & _). exact Q24. }
  assert (Edst: (if td then dst else o + 16) = dst). { subst td dst. destruct stR; reflexivity. }
  assert (Esrc: (if od then y24 else o' + 16) = src).
  { subst od src. unfold L5.bo_dyn. cbn [L5.bo_fb L5.bo_data L5.bo_st]. destruct sto' as [w0 w1|c q]; destruct OST' as (B & _); rewrite B; [reflexivity|]. exact Ey24. }
  assert (WO1: BG.writable M2 o 1).
  { change (L5.writable RSEGS M2 o 1). apply L5C.writable_of_defined; [|lia|lia]. eapply L5KS.u8_at_defined. exact Q0. unfold L5KS.IMG_HI; lia. lia. }
  (* [comment removed for export] *)
  assert (YK: forall a, o' <= a < o' + 32 \/ (src <= a < src + 8 * Z.of_nat len') ->
              L5C.kept L LB sp (48 + (64 + (64 + (64 + (16 + 8224))))) ((o, 32) :: match g with Same => [(L5.bo_data o (L5.BO fb len sto), 8 * Z.max (Z.of_nat len') (Z.of_nat len))] | Grown _ _ => [] end) a).
  { intros a Ha.
    assert (SRC: src <= a < src + 8 * Z.of_nat len' -> match sto' with L5.BInl _ _ => o' + 16 <= a < o' + 32 | L5.BDyn c' q' => q' <= a < q' + 8 * c' /\ In (q', 8 * c') LB /\ (4096 <= q' /\ (q' + 8 * c' <= 0x10000 \/ 0x91000 <= q')) /\ q' + 8 * c' <= hl_ceil L end).
    { intros Hs. subst src. destruct sto' as [w0 w1|c' q']. destruct OST' as (_ & _ & _ & Hl2' & _). cbn [L5.bo_data L5.bo_st] in Hs. lia.
      destruct OST' as (_ & _ & _ & Hlc' & _). cbn [L5.bo_data L5.bo_st] in Hs. specialize (BLK' c' q' eq_refl). destruct (LBwf q' c' BLK') as (QR' & QB' & QD'). repeat split; try lia. exact BLK'. }
    assert (OUTW: L5.outside ((o, 32) :: match g with Same => [(L5.bo_data o (L5.BO fb len sto), 8 * Z.max (Z.of_nat len') (Z.of_nat len))] | Grown _ _ => [] end) a).
    { apply L5C.outside_cons. { unfold L5.in_rng; cbn. destruct Ha as [Ha|Ha]. lia. specialize (SRC Ha). destruct sto' as [w0 w1|c' q']. lia.
        destruct SRC as (S1 & S2 & S3 & S4). lia. }
      destruct g; [|apply L5C.outside_nil]. apply L5C.outside_cons; [|apply L5C.outside_nil]. unfold L5.in_rng; cbn [fst snd].
      destruct GCASE as (G0 & _). intros Hin. destruct (DHI a G0 Hin) as [D1|D2].
      - (* [comment removed for export] *) destruct sto as [v0 v1|c q]. { destruct OST as (_ & _ & _ & Hl2 & _). cbn [L5.bo_data L5.bo_st] in Hin. lia. }
        cbn [L5.bo_data L5.bo_st] in Hin. destruct OST as (B1 & _ & _ & Hlc & _). destruct (LBwf q c (BLK c q eq_refl)) as (QR & QB & QD).
        specialize (CAP B1). cbn in CAP.
        destruct Ha as [Ha|Ha]. lia. specialize (SRC Ha). destruct sto' as [w0 w1|c' q']. lia. destruct SRC as (S1 & S2 & S3 & S4).
        destruct (APQ c q c' q' eq_refl eq_refl); lia.
      - destruct Ha as [Ha|Ha]. lia. specialize (SRC Ha). destruct sto' as [w0 w1|c' q']. lia. destruct SRC as (S1 & S2 & S3 & S4). lia. }
    destruct Ha as [Ha|Ha].
    - apply L5C.kept_stack. lia. lia. lia. rewrite (ly_errno L LY). lia. lia. exact OUTW.
    - specialize (SRC Ha). destruct sto' as [w0 w1|c' q']. apply L5C.kept_stack. lia. lia. lia. rewrite (ly_errno L LY). lia. lia. exact OUTW.
      destruct SRC as (S1 & S2 & S3 & S4). eapply L5C.kept_block. exact S2. lia. lia. lia. rewrite (ly_errno L LY). lia. exact OUTW. }
  assert (O0m: BG.u8_at M2 o' fb').
  { eapply (L5C.u8_at_agree RSEGS M M2). intros i Hi. apply KEEP. apply YK. lia. lia. lia. exact O0'. }
  destruct (p2_run td od fx2 R2 M2 o y24 (Z.of_nat len') o' fb' sp fbR dst
              ltac:(exact (proj1 AT)) ltac:(exact (proj1 (proj2 AT))) ltac:(exact (proj1 (proj2 (proj2 AT)))) ltac:(exact (proj1 (proj2 (proj2 (proj2 AT)))))
              ltac:(exact (proj1 (proj2 (proj2 (proj2 (proj2 AT)))))) ltac:(exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 AT)))))))
              ltac:(lia) Hy24 ltac:(lia) A16 ltac:(lia) ltac:(lia) WR2 Ao Olo ltac:(lia) WO1 Ao' Olo' ltac:(lia) APO Q0 HfbR BtR Q24 O0m Hfb' BtO)
    as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_8 & R3_10 & R3_11 & R3_12 & R3_18 & R3_19 & R3_20 & R3_9 & F3 & MF3 & GR3).
  rewrite Edst in R3_10. rewrite Esrc in R3_11, R3_9.
  assert (MF3z: forall a, 0 <= a < 2 ^ 64 -> a <> o -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha Hna. apply MF3. rewrite BG.unsigned_lit by lia. lia. }
  (* [comment removed for export] *)
  assert (SRCF: 4096 <= src /\ src + 8 * Z.of_nat len' <= 2 ^ 47 /\ (dst + 8 * Z.of_nat len' <= src \/ src + 8 * Z.of_nat len' <= dst) /\ L5.limbs_at RSEGS M src ws'
                /\ (forall a, src <= a < src + 8 * Z.of_nat len' -> a < hl_ceil L \/ o' + 16 <= a < o' + 32)).
  { subst src. destruct sto' as [w0 w1|c' q'].
    - destruct OST' as (B1' & O16' & O24x & Hl2' & Rw0 & Rw1). cbn [L5.bo_data L5.bo_st] in *.
      split. lia. split. lia. split.
      { subst dst. destruct stR as [u0 u1|cR qR]; cbn [L5.bo_data L5.bo_st]. lia. destruct QST as (_ & _ & _ & HlcR & HcR & AqR & QloR & QhiR).
        destruct g. destruct GCASE as (_ & _ & _ & _ & MM). destruct sto as [|c q]; [contradiction|]. destruct MM as [-> ->]. destruct (LBwf q c (BLK c q eq_refl)) as (X1 & X2 & X3). lia.
        destruct GCASE as (_ & SR & _ & _ & _ & _ & ((BR0 & BR1 & BR2 & BR3 & BR4) & _) & _). injection SR; intros; subst. lia. }
      split. { rewrite Vws'. destruct len' as [|[|[|k]]]; [lia| | |lia]; intros i Hi; cbn in Hi.
               destruct i; [|lia]. cbn. replace (o' + 16 + 8 * Z.of_nat 0) with (o' + 16) by lia. exact O16'.
               destruct i as [|[|i]]; [| |lia]; cbn. replace (o' + 16 + 8 * Z.of_nat 0) with (o' + 16) by lia. exact O16'.
               replace (o' + 16 + 8 * Z.of_nat 1) with (o' + 24) by lia. exact O24x. }
      intros a Ha. right. lia.
    - destruct OST' as (B1' & O16' & O24x & Hlc' & Hc' & Aq' & Qlo' & Qhi'). cbn [L5.bo_data L5.bo_st] in *.
      specialize (BLK' c' q' eq_refl). destruct (LBwf q' c' BLK') as (X1 & X2 & X3).
      split. lia. split. lia. split.
      { subst dst. destruct stR as [u0 u1|cR qR]; cbn [L5.bo_data L5.bo_st]. lia. destruct QST as (_ & _ & _ & HlcR & HcR & AqR & QloR & QhiR).
        destruct g. destruct GCASE as (_ & _ & _ & _ & MM). destruct sto as [|c q]; [contradiction|]. destruct MM as [-> ->]. destruct OST as (B1 & _).
        specialize (CAP B1). cbn in CAP. destruct (APQ c q c' q' eq_refl eq_refl); lia.
        destruct GCASE as (_ & SR & _ & _ & _ & _ & (_ & BA & _) & _). injection SR; intros; subst. destruct (BA _ BLK'); cbn in *; lia. }
      split. exact Vws'. intros a Ha. left. lia. }
  destruct SRCF as (SRClo & SRChi & APART & LIMBS0 & SRCW).
  assert (LIMBS3: L5.limbs_at RSEGS M3 src ws').
  { eapply (L5C.limbs_at_agree RSEGS M M3). 2: lia. 2: lia. 2: exact LIMBS0. intros i Hi. rewrite MF3z. apply KEEP. apply YK. rewrite Lws' in Hi. lia. lia.
    destruct (SRCW i ltac:(rewrite Lws' in Hi; lia)); lia. }
  assert (WD3: L5.writable RSEGS M3 dst (8 * Z.of_nat len')).
  { apply L5C.writable_of_defined; [|lia|lia]. eapply L5.defined_grows. exact GR3. exact DDST. }
  destruct (memcpy_run fx3 R3 M3 dst src RET2 ws' R3_10 R3_11 ltac:(rewrite Lws'; exact R3_12) R3_1 ltac:(split; [unfold RET2; lia|reflexivity])
              ltac:(lia) ltac:(rewrite Lws'; lia) ltac:(lia) ltac:(rewrite Lws'; lia) ltac:(rewrite Lws'; exact APART) ltac:(rewrite Lws'; exact WD3) LIMBS3)
    as (R4 & MS4 & K4 & R4_10).
  set (M4 := wbytes M3 (Z_to_bv 64 dst) (L5K.limb_bytes ws')) in MS4.
  assert (GR4: mem_grows M3 M4) by (subst M4; apply wbytes_grows).
  assert (M4b: forall a, 0 <= a < 2 ^ 64 -> ~ (dst <= a < dst + 8 * Z.of_nat len') -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
  { intros a Ha Hna. subst M4. apply L5K.wbytes_limbs_out1; rewrite ?Lws'; lia. }
  assert (M4out: forall a k, 0 <= a < 2 ^ 64 -> a + Z.of_nat k <= 2 ^ 64 -> (a + Z.of_nat k <= dst \/ dst + 8 * Z.of_nat len' <= a) ->
                 rdn RSEGS M4 (Z_to_bv 64 a) k = rdn RSEGS M3 (Z_to_bv 64 a) k).
  { intros a k Ha Hk Hap. subst M4. apply L5K.wbytes_limbs_out; rewrite ?Lws'; lia. }
  assert (LIMBS4: L5.limbs_at RSEGS M4 dst ws'). { subst M4. apply L5K.limbs_at_of_wbytes. lia. rewrite Lws'. lia. }
  (* [comment removed for export] *)
  assert (DSTW: (o + 16 <= dst /\ dst + 8 * Z.of_nat len' <= o + 32) \/ dst + 8 * Z.of_nat len' <= hl_ceil L).
  { subst dst. destruct stR as [u0 u1|cR qR]; cbn [L5.bo_data L5.bo_st] in *.
    - left. destruct QST as (_ & _ & _ & HlR & _). lia.
    - right. destruct QST as (_ & _ & _ & HlcR & HcR & AqR & QloR & QhiR).
      destruct g. destruct GCASE as (_ & _ & _ & _ & MM). destruct sto as [|c q]; [contradiction|]. destruct MM as [-> ->]. destruct (LBwf q c (BLK c q eq_refl)) as (X1 & X2 & X3). lia.
      destruct GCASE as (_ & SR & _ & _ & _ & _ & ((BR0 & BR1 & BR2 & BR3 & BR4) & _) & _). injection SR; intros; subst. lia. }
  (* [comment removed for export] *)
  assert (AT4: at_ret1 R4 M4 o src (Z.of_nat len') o' fb' sp (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9)))
                 (bv_unsigned (getr R (reg 18))) (bv_unsigned (getr R (reg 19))) (bv_unsigned (getr R (reg 20)))).
  { destruct AT as (_ & _ & _ & _ & _ & _ & D8 & D16 & D24 & D32 & D40 & D48 & RR).
    assert (T3: forall a v, sp - 48 <= a -> a + 8 <= sp -> BG.u64_at M2 a v -> BG.u64_at M4 a v).
    { intros a v H1a H2a Hu. unfold BG.u64_at. rewrite M4out; [|lia|lia|lia]. eapply BG.u64_at_frame. lia. lia. intros j Hj. apply MF3z; lia. exact Hu. }
    unfold at_ret1.
    split. { rewrite (K4 8%nat) by (apply L5K.In_of_mem; reflexivity). exact R3_8. }
    split. { rewrite (K4 9%nat) by (apply L5K.In_of_mem; reflexivity). exact R3_9. }
    split. { rewrite (K4 18%nat) by (apply L5K.In_of_mem; reflexivity). exact R3_18. }
    split. { rewrite (K4 19%nat) by (apply L5K.In_of_mem; reflexivity). exact R3_19. }
    split. { rewrite (K4 20%nat) by (apply L5K.In_of_mem; reflexivity). exact R3_20. }
    split. { rewrite (K4 2%nat) by (apply L5K.In_of_mem; reflexivity). exact R3_2. }
    split. apply T3; [lia|lia|exact D8]. split. apply T3; [lia|lia|exact D16]. split. apply T3; [lia|lia|exact D24].
    split. apply T3; [lia|lia|exact D32]. split. apply T3; [lia|lia|exact D40]. split. apply T3; [lia|lia|exact D48]. exact RR. }
  assert (WR4: BG.writable M4 (sp - 48) 48).
  { change (L5.writable RSEGS M4 (sp - 48) 48). eapply L5.writable_grows. exact GR4. eapply L5.writable_grows. exact GR3. exact WR2. }
  destruct (epilogue_run fx3 R4 M4 RET2 o src (Z.of_nat len') o' fb' sp _ _ _ _ _ _ r (or_intror eq_refl) AT4
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 ltac:(lia) ltac:(lia) WR4 E1 RA)
    as (fx5 & R5 & M5 & MS5 & K5 & R5_1 & R5_2 & R5_8 & R5_9 & R5_18 & R5_19 & R5_20 & R5_10 & MM5 & GR5).
  eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. { eapply msteps_trans. exact MS3. eapply msteps_trans. exact MS4. exact MS5. }
  (* [comment removed for export] *)
  assert (RP5: regs_preserved R R5).
  { apply (REGS R5 [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat).
    { intros x Hx. assert (HxC: In x L5K.CS) by (pose proof Hx as H'; L5K.inlist H'). assert (Hx2: In x KS2) by (pose proof Hx as H'; L5K.inlist H').
      assert (Hx3: In x KS3) by (pose proof Hx as H'; L5K.inlist H').
      rewrite (K5 x Hx3). rewrite (K4 x HxC). apply K3. exact Hx2. }
    intros x Hx; exact Hx. exact R5_2. exact R5_8. exact R5_9. exact R5_18. exact R5_19. exact R5_20. }
  assert (FBn: assign_fb fb fb' len' grown = assign_flags fbR fb'). { rewrite EfbR. apply assign_fb_eq. lia. }
  (* [comment removed for export] *)
  assert (HC5: forall a v, o <= a -> a + 8 <= o + 32 -> (a + 8 <= o + 16 \/ dst + 8 * Z.of_nat len' <= a \/ dst + 8 * Z.of_nat len' <= hl_ceil L) -> o + 1 <= a ->
               BG.u64_at M2 a v -> BG.u64_at M5 a v).
  { intros a v H1a H2a H3a H4a Hu. eapply (BG.u64_at_frame M4 M5). lia. lia. intros j Hj. apply MM5.
    unfold BG.u64_at. rewrite M4out; [|lia|lia|destruct DSTW; lia]. eapply (BG.u64_at_frame M2 M3). lia. lia. intros j Hj. apply MF3z; lia. exact Hu. }
  assert (F5: BG.u8_at M5 o (assign_fb fb fb' len' grown)).
  { rewrite FBn. eapply (BG.u8_at_frame M4 M5). apply MM5. unfold BG.u8_at. rewrite M4out; [exact F3|lia|lia|destruct DSTW; lia]. }
  assert (Q85: BG.u64_at M5 (o + 8) (Z.of_nat len')). { apply HC5; try lia; first [exact Q8 | (left; lia)]. }
  assert (KEEP5: forall a, L5C.kept L LB sp (48 + (64 + (64 + (64 + (16 + 8224))))) ((o, 32) :: match g with Same => [(L5.bo_data o (L5.BO fb len sto), 8 * Z.max (Z.of_nat len') (Z.of_nat len))] | Grown _ _ => [] end) a ->
                  M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a KA. pose proof KA as (Ha & CA & NE & OW). apply L5C.outside_cons_inv in OW as [NW OW2]. unfold L5.in_rng in NW. cbn [fst snd] in NW.
    rewrite (MM5 (Z_to_bv 64 a)). rewrite M4b. rewrite MF3z by lia. apply KEEP. exact KA. lia.
    (* [comment removed for export] *)
    destruct DSTW as [D1|D2]. lia. intros Hin. subst dst. destruct stR as [u0 u1|cR qR]; cbn [L5.bo_data L5.bo_st] in *. lia.
    destruct g.
    - destruct GCASE as (_ & _ & _ & _ & MM). destruct sto as [|c q]; [contradiction|]. destruct MM as [-> ->].
      apply L5C.outside_cons_inv in OW2 as [NW2 _]. unfold L5.in_rng in NW2. cbn [fst snd L5.bo_data L5.bo_st] in NW2. lia.
    - destruct GCASE as (_ & SR & _ & _ & _ & _ & (FBR & BA & _) & _). injection SR; intros; subst.
      apply (L5C.kept_not_fresh L LB sp _ _ a A (8 * cap) KA BA). exact (proj1 (proj2 FBR)).
      exact (proj2 (proj2 (proj2 (proj2 FBR)))). exact LBhi. destruct QST as (_ & _ & _ & HlcR & _). lia. }
  assert (SDEF5: L5.defined M5 (sp - (48 + (64 + (64 + (64 + (16 + 8224)))))) (48 + (64 + (64 + (64 + (16 + 8224)))))).
  { apply SDEF_of. intros a Ha. right. rewrite (MM5 (Z_to_bv 64 a)). rewrite M4b by (destruct DSTW; lia). apply MF3z; lia.
    eapply mem_grows_trans. exact GR3. eapply mem_grows_trans. exact GR4. exact GR5. }
  assert (CD5: forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp (48 + (64 + (64 + (64 + (16 + 8224))))) a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M5 (Z_to_bv 64 a) <> None).
  { intros a Ha CA NE DM. apply GR5. apply GR4. apply GR3. apply CD2; assumption. }
  assert (HH5: forall LBx crx, hi_heap HI LBx crx M2 (m_vmmaps model2) ->
               (forall a, dst <= a < dst + 8 * Z.of_nat len' -> (hl_ceil L <= a < hl_sptop L) \/ in_block LBx a) -> hi_heap HI LBx crx M5 (m_vmmaps model2)).
  { intros LBx crx HHx Hdst. eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HHx. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
    intros a Ha. rewrite (MM5 (Z_to_bv 64 a)). destruct (Z.eq_dec a o) as [->|Hno]. right; left. lia.
    destruct (Z_lt_le_dec a dst) as [X|X]. left. rewrite M4b by lia. apply MF3z; lia.
    destruct (Z_lt_le_dec a (dst + 8 * Z.of_nat len')) as [Y|Y]. right. apply Hdst. lia. left. rewrite M4b by lia. apply MF3z; lia.
    eapply mem_grows_trans. exact GR3. eapply mem_grows_trans. exact GR4. exact GR5. }
  apply (KONT fx5 R5 M5 model2 g LB' cr').
  * split. exact RP5. split. exact R5_10. cbn [L5.bo_len L5.bo_fb L5.bo_st L5.bo_dyn L5.bo_data].
    destruct g as [|A cap].
    -- destruct GCASE as (G0 & -> & -> & HG & MATCH). subst grown.
       split. exact HG. split. reflexivity. split. reflexivity.
       split.
       { (* [comment removed for export] *)
         destruct stR as [u0 u1|cR qR].
         - (* [comment removed for export] *)
           destruct sto as [v0 v1|]; [|contradiction]. subst dst. cbn [L5.bo_data L5.bo_st] in *.
           destruct QST as (BR0 & Q16 & Q24x & HlR & Ru0 & Ru1).
           assert (L1: BG.u64_at M5 (o + 16) (nth 0 ws' 0)).
           { eapply (BG.u64_at_frame M4 M5). lia. lia. intros j Hj. apply MM5. pose proof (LIMBS4 0%nat ltac:(rewrite Lws'; lia)) as X. rewrite Z.mul_0_r, Z.add_0_r in X. exact X. }
           exists (L5.BInl (nth 0 ws' 0) (if Nat.leb 2 len' then nth 1 ws' 0 else u1)).
           split.
           + unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact F5. split. { rewrite FBn. apply assign_flags_range; lia. }
             split. exact Q85. split. { rewrite FBn. unfold assign_flags. rewrite Z.lor_spec, !Z.land_spec. rewrite BtR. cbn. rewrite Bool.andb_false_r. reflexivity. }
             split. exact L1.
             split. { destruct (Nat.leb_spec 2 len').
                      - eapply (BG.u64_at_frame M4 M5). lia. lia. intros j Hj. apply MM5. pose proof (LIMBS4 1%nat ltac:(rewrite Lws'; lia)) as X.
                        replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) in X by lia. exact X.
                      - apply HC5; try lia; first [exact Q24x | (right; left; lia)]. }
             split. exact HlR. rewrite Forall_forall in Rws'.
             split. { apply Rws'. apply nth_In. rewrite Lws'. lia. }
             destruct (Nat.leb_spec 2 len'). apply Rws'. apply nth_In. rewrite Lws'. lia. exact Ru1.
           + split. 2: exact I. split. cbn. lia. split. exact Rws'. cbn [L5.bo_st L5.bo_len].
             destruct ws' as [|w0 [|w1 [|w2 l]]]; cbn in Lws'; try lia; subst len' || (assert (len' = 2%nat) by lia; subst len'); cbn; try reflexivity.
             all: destruct len' as [|[|[|k]]]; cbn; try reflexivity; try lia.
         - (* [comment removed for export] *)
           destruct sto as [|c q]; [contradiction|]. destruct MATCH as [-> ->]. subst dst. cbn [L5.bo_data L5.bo_st] in *.
           destruct QST as (BR0 & Q16 & Q24x & HlcR & HcR & AqR & QloR & QhiR & HAPR).
           exists (L5.BDyn c q). split.
           + unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact F5. split. { rewrite FBn. apply assign_flags_range; lia. }
             split. exact Q85. split. { rewrite FBn. unfold assign_flags. rewrite Z.lor_spec, !Z.land_spec. rewrite BtR. cbn. rewrite Bool.andb_false_r. reflexivity. }
             split. { apply HC5; try lia; first [exact Q16 | (right; right; destruct (LBwf q c (BLK c q eq_refl)) as (X1 & X2 & X3); lia)]. }
             split. { apply HC5; try lia; first [exact Q24x | (right; right; destruct (LBwf q c (BLK c q eq_refl)) as (X1 & X2 & X3); lia)]. }
             repeat split; try lia. exact HAPR.
           + split. 2: (split; reflexivity). split. cbn. lia. split. exact Rws'. cbn [L5.bo_st L5.bo_len].
             eapply (L5C.limbs_at_agree RSEGS M4 M5). intros i Hi. apply MM5. lia. rewrite Lws'. lia. exact LIMBS4. }
       split.
       ++ intros a KA. unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in KA. apply KEEP5. exact KA.
       ++ split. { unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. exact SDEF5. }
          intros a Ha CA NE DM. unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in CA. apply CD5; assumption.
    -- destruct GCASE as (G1 & SR & H3 & Hcap & -> & -> & FB & B0). subst grown stR. subst dst. cbn [L5.bo_data L5.bo_st] in *.
       pose proof FB as ((BR0' & BR1 & BR2 & BR3 & BR4) & BA & DEFA). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in BR1.
       destruct QST as (BR0 & Q16 & Q24x & HlcR & HcR & AqR & QloR & QhiR & HAPR).
       split. { unfold L5.bo_dyn. cbn. exact B0. } split. exact H3. split. exact Hcap. split. reflexivity. split. reflexivity.
       split. { split. exact (proj1 FB). split. exact BA. eapply L5.defined_grows. eapply mem_grows_trans. exact GR3. eapply mem_grows_trans. exact GR4. exact GR5. exact DEFA. }
       split. { unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact F5. split. { rewrite FBn. apply assign_flags_range; lia. }
                split. exact Q85. split. { rewrite FBn. unfold assign_flags. rewrite Z.lor_spec, !Z.land_spec. rewrite BtR. cbn. rewrite Bool.andb_false_r. reflexivity. }
                split. { apply HC5; try lia; first [exact Q16 | (right; right; lia)]. }
                split. { apply HC5; try lia; first [exact Q24x | (right; right; lia)]. }
                repeat split; try lia. exact HAPR. }
       split. { split. cbn. lia. split. exact Rws'. cbn [L5.bo_st L5.bo_len].
                eapply (L5C.limbs_at_agree RSEGS M4 M5). intros i Hi. apply MM5. lia. rewrite Lws'. lia. exact LIMBS4. }
       split.
       ++ intros a KA. unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in KA. apply KEEP5. exact KA.
       ++ split. { unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. exact SDEF5. }
          intros a Ha CA NE DM. unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in CA. apply CD5; assumption.
  * exact MBV.
  * apply HH5. exact HH2. intros a Ha. destruct DSTW as [D1|D2]. left. lia.
    right. subst dst. destruct stR as [u0 u1|cR qR]; cbn [L5.bo_data L5.bo_st] in *. exfalso. destruct QST as (_ & _ & _ & HlR & _). lia.
    destruct g. destruct GCASE as (_ & -> & _ & _ & MM). destruct sto as [|c q]; [contradiction|]. destruct MM as [-> ->].
    exists (q, 8 * c). split. exact (BLK c q eq_refl). cbn. destruct (LBwf q c (BLK c q eq_refl)) as (X1 & X2 & X3). destruct QST as (_ & _ & _ & HlcR & _). lia.
    destruct GCASE as (_ & SR & _ & _ & -> & _). injection SR; intros; subst. exists (A, 8 * cap). split. left; reflexivity. cbn. destruct QST as (_ & _ & _ & HlcR & _). lia.
Qed.

End WithHeap.
End SCFG_1.

End L5ASGT.
