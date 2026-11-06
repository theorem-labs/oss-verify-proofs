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
     L5Core L5CoreKit L5CoreKitS L5CoreSpecs L5AReserve L5Reserve L5ResizeP L5Resize L5Mul10P.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigFactsBase BigFactsDigits.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5MULT2.
Import L5CS.
Import L5MULP.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma limbs_val_val ws : L5.limbs_val ws = val ws.
Proof. induction ws as [|w ws IH]. reflexivity. cbn [L5.limbs_val]. rewrite val_cons, IH, M_val. reflexivity. Qed.

Lemma words_ok_of_Forall ws : Forall (fun w => 0 <= w < 2 ^ 64) ws -> words_ok ws.
Proof. intros F. apply (proj1 (L5W.words_ok_BF ws)). exact F. Qed.

Lemma val_all_zero ws : (forall i, (i < length ws)%nat -> nth i ws 0 = 0) -> val ws = 0.
Proof.
  induction ws as [|w ws IH]; intros Hz. reflexivity.
  rewrite val_cons. pose proof (Hz 0%nat ltac:(cbn; lia)) as H0. cbn in H0. rewrite H0. rewrite IH. lia. intros i Hi. apply (Hz (S i)). cbn. lia.
Qed.

Lemma val_firstn_zeros ws k : (k <= length ws)%nat -> (forall i, (k <= i < length ws)%nat -> nth i ws 0 = 0) -> val (firstn k ws) = val ws.
Proof.
  intros Hk Hz. rewrite (val_firstn_skipn k ws). rewrite (val_all_zero (skipn k ws)). lia.
  intros i Hi. rewrite length_skipn in Hi. rewrite nth_skipn. apply Hz. lia.
Qed.

Lemma wlist_nth' v n i : (i < n)%nat -> nth i (wlist v n) 0 = wordi v i.
Proof. intros Hi. exact (wlist_nth v n i Hi). Qed.

Lemma Forall_wlist v n : Forall (fun w => 0 <= w < 2 ^ 64) (wlist v n).
Proof. apply (proj2 (L5W.words_ok_BF _)). apply wlist_words_ok. Qed.

(* [comment removed for export] *)
Lemma land253_id fb : 0 <= fb < 256 -> Z.testbit fb 1 = false -> Z.land fb 253 = fb.
Proof.
  intros Hfb Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 1) as [->|Hi1]. { rewrite Hb. reflexivity. }
  destruct (Z_lt_le_dec i 8) as [Hlt|Hge].
  - assert (T: Z.testbit 253 i = true).
    { assert (H: In i [0; 2; 3; 4; 5; 6; 7]) by (cbn; lia). cbn in H. repeat (destruct H as [<-|H]; [reflexivity|]). destruct H. }
    rewrite T. apply Bool.andb_true_r.
  - rewrite (Z.bits_above_log2 fb i). reflexivity. lia. apply (Z.le_lt_trans _ (Z.log2 255)). apply Z.log2_le_mono. lia. cbn. lia.
Qed.

Lemma lor1_bit1 fb : Z.testbit (Z.lor fb 1) 1 = Z.testbit fb 1.
Proof. rewrite Z.lor_spec. replace (Z.testbit 1 1) with false by reflexivity. apply Bool.orb_false_r. Qed.

(* [comment removed for export] *)
Lemma store_ok1_defined M (a : Z) : 0 <= a < 2 ^ 64 -> L5KS.IMG_HI <= a -> store_ok RSEGS M (Z_to_bv 64 a) 1 = true -> M (Z_to_bv 64 a) <> None.
Proof.
  intros Ha Hlo HS. cbn [store_ok] in HS. unfold wview in HS. destruct (M (Z_to_bv 64 a)) eqn:E. congruence.
  rewrite (src0_in_hull (Z_to_bv 64 a)) in HS. discriminate.
  unfold APS.in_hull. cbn [APC.img_lo APC.img_hi A0]. rewrite BG.unsigned_lit by lia. apply Bool.andb_false_iff. right. apply Z.ltb_ge. unfold L5KS.IMG_HI in Hlo. lia.
Qed.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

(* [comment removed for export] *)
Lemma mul10_post
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
  (Lws : length ws = len)
  (Rws : Forall (fun w : Z => 0 <= w < 2 ^ 64) ws)
  (Ao : o mod 8 = 0)
  (Olo : sp <= o)
  (Ohi : o + 32 <= hl_sptop L)
  (KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) (LB' : list (Z * Z)) (cr' : credit), arith_post L LB cr M M' R R' o sp MUL10_SCR (L5.BO (fb) (len) (sto)) (10 * L5.limbs_val ws) g LB' cr' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') -> srealizes RSEGS SCFG (@cfg fx' R' r M' model') K)
  (A16 : sp mod 16 = 0)
  (SLO : hl_sptop L - 2 ^ 23 + (48 + (64 + (64 + (64 + (16 + 8224))))) <= sp)
  (SHI : sp <= hl_sptop L)
  (STOP : 140735340871680 <= hl_sptop L <= 2 ^ 47)
  (Hr : 0 <= r < 2 ^ 47)
  (He : r mod 2 = 0)
  (Hfb : 0 <= fb < 256)
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
  (R2 : bvmap 5 word)
  (M2 : word -> option byte)
  (model2 : Model)
  (g : growth)
  (LB' : list (Z * Z))
  (cr' : credit)
  (MBV : model_but_vm model model2)
  (HH2 : hi_heap HI LB' cr' M2 (m_vmmaps model2))
  (RL : resize_limbs ws (S len) = ws ++ [0])
  (fbR : Z)
  (stR : L5.bstore)
  (grown : bool)
  (EfbR : fbR = (if grown then Z.lor fb 1 else fb))
  (MATCH : grown = false -> match sto with | L5.BInl _ _ => match stR with | L5.BInl _ _ => (len <= 1)%nat | L5.BDyn _ _ => False end | L5.BDyn c q => match stR with | L5.BInl _ _ => False | L5.BDyn c' q' => c' = c /\ q' = q end end)
  (GCASE : match g with | Same => grown = false /\ LB' = LB /\ cr' = cr /\ (L5.bo_dyn (L5.BO (fb) (len) (sto)) = true \/ (len <= 1)%nat) | Grown A cap => grown = true /\ stR = L5.BDyn cap A /\ len = 2%nat /\ cap = 8 /\ LB' = (A, 64) :: LB /\ cr' = debit L cr 64 /\ L5C.fresh_block L LB M2 A 64 /\ Z.testbit fb 0 = false end)
  (HfbR : 0 <= fbR < 256)
  (Dlo : 4096 <= (L5.bo_data o (L5.BO (fbR) (S len) (stR))))
  (Da : (L5.bo_data o (L5.BO (fbR) (S len) (stR))) mod 8 = 0)
  (Dhi : (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1) <= 2 ^ 47)
  (Dimg : (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1) <= 65536 \/ 593920 <= (L5.bo_data o (L5.BO (fbR) (S len) (stR))))
  (DW : o + 16 = (L5.bo_data o (L5.BO (fbR) (S len) (stR))) /\ (len <= 1)%nat /\ (exists u0 u1 : Z, stR = L5.BInl u0 u1) \/ (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1) <= hl_ceil L /\ exists cR qR : Z, stR = L5.BDyn cR qR /\ In (qR, 8 * cR) LB' /\ Z.of_nat len + 1 <= cR)
  (LwsA : length (ws ++ [0]) = S len)
  (RR : 0 <= bv_unsigned (getr R (reg 1)) < 2 ^ 64 /\ 0 <= bv_unsigned (getr R (reg 8)) < 2 ^ 64 /\ 0 <= bv_unsigned (getr R (reg 9)) < 2 ^ 64 /\ 0 <= bv_unsigned (getr R (reg 18)) < 2 ^ 64 /\ 0 <= bv_unsigned (getr R (reg 19)) < 2 ^ 64 /\ 0 <= bv_unsigned (getr R (reg 20)) < 2 ^ 64)
  (KEEP : forall a : Z, L5C.kept L LB sp (48 + (64 + (64 + (64 + (16 + 8224))))) ((o, 32) :: match g with | Same => [(L5.bo_data o (L5.BO (fb) (len) (sto)), 8 * (Z.of_nat len + 1))] | Grown _ _ => [] end) a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  (KD : forall a : Z, L5C.kept L LB sp (48 + (64 + (64 + (64 + (16 + 8224))))) ((o, 32) :: match g with | Same => [(L5.bo_data o (L5.BO (fb) (len) (sto)), 8 * (Z.of_nat len + 1))] | Grown _ _ => [] end) a -> ~ (L5.bo_data o (L5.BO (fbR) (S len) (stR))) <= a < (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1))
  (CD2 : forall a : Z, 0 <= a < 2 ^ 64 -> client_addr L LB sp (48 + (64 + (64 + (64 + (16 + 8224))))) a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None)
  (REGS : forall (R3 : bvmap 5 word) (ks : list nat), (forall x : nat, In x ks -> getr R3 (reg x) = getr R2 (reg x)) -> incl [3%nat; 4%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat] ks -> getr R3 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))) -> getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9))) -> getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R (reg 18))) -> getr R3 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R (reg 19))) -> getr R3 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R (reg 20))) -> regs_preserved R R3)
  (SDEF_of : forall M5 : word -> option byte, (forall a : Z, sp - (48 + (64 + (64 + (64 + (16 + 8224))))) <= a < sp -> M5 (Z_to_bv 64 a) <> None \/ M5 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) -> mem_grows M2 M5 -> L5.defined M5 (sp - (48 + (64 + (64 + (64 + (16 + 8224)))))) (48 + (64 + (64 + (64 + (16 + 8224))))))
  (BtR : Z.testbit fbR 0 = (match stR with | L5.BInl _ _ => false | L5.BDyn _ _ => true end))
  (Edata : (if (match stR with | L5.BInl _ _ => false | L5.BDyn _ _ => true end) then (L5.bo_data o (L5.BO (fbR) (S len) (stR))) else o + 16) = (L5.bo_data o (L5.BO (fbR) (S len) (stR))))
  (R4 : bvmap 5 word)
  (K4 : forall x : nat, In x KS2 -> In x KSIT -> getr R4 (reg x) = getr R2 (reg x))
  (R4_11 : bv_unsigned (getr R4 (reg 11)) = mcarry 10 (val ws) len)
  (VB10 : 0 <= 10 * (val ws) < BigModel.W.M ^ Z.of_nat (S len))
  (CARRY : mcarry 10 (val ws) len = wordi (10 * (val ws)) len)
  (CR10 : 0 <= wordi (10 * (val ws)) len < 18446744073709551616)
  (R5 : bvmap 5 word)
  (M5 : word -> option byte)
  (K5 : forall x : nat, In x KS3 -> getr R5 (reg x) = getr R4 (reg x))
  (WL : length (wlist (10 * (val ws)) (S len)) = S len)
  (LIM5 : L5.limbs_at RSEGS M5 (L5.bo_data o (L5.BO (fbR) (S len) (stR))) (wlist (10 * (val ws)) (S len)))
  (R6 : bvmap 5 word)
  (M6 : word -> option byte)
  (OB6 : L5.big_at RSEGS M6 o (L5.BO (fbR) (L5W.rlen (wlist (10 * (val ws)) (S len))) ((match stR with | L5.BInl _ v1 => L5.BInl (wordi (10 * (val ws)) 0) (if (len =? 0)%nat then v1 else wordi (10 * (val ws)) 1) | L5.BDyn c q => L5.BDyn c q end))))
  (RP6 : regs_preserved R5 R6)
  (FL6 : (if (L5W.rlen (wlist (10 * (val ws)) (S len)) =? 0)%nat then Z.land fbR 253 else fbR) = fbR)
  (FR6z : forall a : Z, 0 <= a < 2 ^ 64 -> ~ o <= a < o + 16 -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a))
  (M62 : forall a : Z, 0 <= a < 2 ^ 64 -> ~ o <= a < o + 16 -> ~ (L5.bo_data o (L5.BO (fbR) (S len) (stR))) <= a < (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1) -> M6 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a))
  (GR26 : mem_grows M2 M6)
  (fx7 : FPState)
  (R7 : bvmap 5 word)
  (M7 : word -> option byte)
  (K7 : forall x : nat, In x KS4 -> getr R7 (reg x) = getr R6 (reg x))
  (R7_2 : getr R7 (reg 2) = Z_to_bv 64 sp)
  (R7_8 : getr R7 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))))
  (R7_9 : getr R7 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9))))
  (R7_18 : getr R7 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R (reg 18))))
  (R7_19 : getr R7 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R (reg 19))))
  (R7_20 : getr R7 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R (reg 20))))
  (R7_10 : getr R7 (reg 10) = Z_to_bv 64 o)
  (MM7 : forall a : word, M7 a = M6 a)
  (GR7 : mem_grows M6 M7)
  : srealizes RSEGS SCFG (mkCfg (st fx7 R7 r M7) (model2)) K.

Proof.
  set (V := val ws) in *.
  set (data := L5.bo_data o (L5.BO fbR (S len) stR)) in *.
  set (WF := (o, 32) :: match g with Same => [(L5.bo_data o (L5.BO fb len sto), 8 * (Z.of_nat len + 1))] | Grown _ _ => [] end) in *.
  set (td := match stR with L5.BDyn _ _ => true | L5.BInl _ _ => false end) in *.
  set (wl := wlist (10 * V) (S len)) in *.
  set (stF := match stR with L5.BInl _ v1 => L5.BInl (wordi (10 * V) 0) (if Nat.eqb len 0 then v1 else wordi (10 * V) 1) | L5.BDyn c q => L5.BDyn c q end) in *.
  (* [comment removed for export] *)
  assert (RP7: regs_preserved R R7).
  { apply (REGS R7 [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat).
    { intros x Hx. assert (HxC: In x L5K.CS) by (pose proof Hx as H'; L5K.inlist H'). assert (Hx2: In x KS2) by (pose proof Hx as H'; L5K.inlist H').
      assert (Hx3: In x KS3) by (pose proof Hx as H'; L5K.inlist H'). assert (Hx4: In x KS4) by (pose proof Hx as H'; L5K.inlist H').
      assert (HxI: In x KSIT) by (pose proof Hx as H'; L5K.inlist H').
      rewrite (K7 x Hx4). rewrite (L5K.regs_preserved_index R5 R6 x RP6 HxC). rewrite (K5 x Hx3). apply K4. exact Hx2. exact HxI. }
    intros x Hx; exact Hx. exact R7_2. exact R7_8. exact R7_9. exact R7_18. exact R7_19. exact R7_20. }
  set (ws' := firstn (L5W.rlen wl) wl).
  pose proof (L5W.rlen_le wl) as RLE. rewrite WL in RLE.
  assert (Lws': length ws' = L5W.rlen wl). { subst ws'. rewrite length_firstn, WL. lia. }
  assert (VAL: L5.limbs_val ws' = 10 * L5.limbs_val ws).
  { rewrite !limbs_val_val. change (val ws) with V. subst ws'. rewrite val_firstn_zeros. subst wl. apply val_wlist_small. exact VB10. rewrite WL. lia.
    intros i Hi. apply (L5W.rlen_zeros wl i). rewrite WL. lia. }
  assert (RED: reduced ws').
  { unfold reduced. destruct (Nat.eq_dec (L5W.rlen wl) 0) as [Z0|NZ]. left. subst ws'. rewrite Z0. reflexivity.
    right. rewrite Lws'. subst ws'. rewrite nth_firstn. replace (Nat.ltb (L5W.rlen wl - 1) (L5W.rlen wl)) with true by (symmetry; apply Nat.ltb_lt; lia).
    apply (L5W.rlen_top wl). lia. }
  assert (OB7: L5.big_at RSEGS M7 o (L5.BO fbR (length ws') stF)). { rewrite Lws'. eapply (L5C.big_at_agree RSEGS M6 M7). intros i Hi. apply MM7. lia. lia. exact OB6. }
  assert (OL7: L5C.obj_limbs RSEGS M7 (L5.BO fbR (length ws') stF) ws').
  { split. reflexivity. split. { subst ws' wl. apply Forall_forall. intros w Hw. apply (proj1 (Forall_forall _ _) (Forall_wlist (10 * V) (S len)) w). eapply L5RSZ.in_firstn. exact Hw. }
    cbn [L5.bo_st L5.bo_len]. subst stF. destruct stR as [u0 u1|cR qR].
    - destruct DW as [(D1 & Hl1 & _)|(_ & cR & qR & X & _)]; [|discriminate]. subst ws'. rewrite length_firstn, WL.
      subst wl. destruct len as [|[|k]]; [| |lia].
      + cbn [Nat.eqb]. replace (Nat.min (L5W.rlen (wlist (10 * V) 1)) 1) with (L5W.rlen (wlist (10 * V) 1)) by lia.
        change (wlist (10 * V) 1) with [wordi (10 * V) 0] in *. destruct (L5W.rlen [wordi (10 * V) 0]) as [|[|r2]] eqn:ER; [reflexivity|reflexivity|lia].
      + cbn [Nat.eqb]. replace (Nat.min (L5W.rlen (wlist (10 * V) 2)) 2) with (L5W.rlen (wlist (10 * V) 2)) by lia.
        change (wlist (10 * V) 2) with [wordi (10 * V) 0; wordi (10 * V) 1] in *. reflexivity.
    - destruct DW as [(_ & _ & u0 & u1 & X)|(D1 & cR' & qR' & X & INB & HC)]; [discriminate|]. injection X; intros <- <-. subst data. cbn [L5.bo_data L5.bo_st] in *.
      subst ws'. intros i Hi. rewrite length_firstn, WL in Hi. rewrite nth_firstn. replace (Nat.ltb i (L5W.rlen wl)) with true by (symmetry; apply Nat.ltb_lt; lia).
      eapply (BG.u64_at_frame M5 M7). lia. lia. intros k Hk. rewrite MM7. apply FR6z; lia. apply LIM5. rewrite WL. lia. }
  assert (KEEP7: forall a, L5C.kept L LB sp (48 + (64 + (64 + (64 + (16 + 8224))))) WF a -> M7 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a KA. pose proof KA as (Ha & CA & NE & OW). pose proof (L5C.outside_cons_inv _ _ _ OW) as [NW _]. unfold L5.in_rng in NW. cbn [fst snd] in NW.
    rewrite MM7. rewrite M62. apply KEEP. exact KA. lia. lia. apply KD. exact KA. }
  assert (SDEF7: L5.defined M7 (sp - (48 + (64 + (64 + (64 + (16 + 8224)))))) (48 + (64 + (64 + (64 + (16 + 8224)))))).
  { apply SDEF_of. intros a Ha. right. rewrite MM7. apply M62. lia. lia. destruct DW as [(D1 & _)|(D1 & _)]; lia. eapply mem_grows_trans. exact GR26. exact GR7. }
  assert (CD7: forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp (48 + (64 + (64 + (64 + (16 + 8224))))) a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M7 (Z_to_bv 64 a) <> None).
  { intros a Ha CA NE DM. apply GR7. apply GR26. apply CD2; assumption. }
  assert (HP7: forall W', W' = WF -> L5C.hpres L LB sp MUL10_SCR W' M M7).
  { intros W' ->. split. { intros a KA. apply KEEP7. unfold MUL10_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in KA. exact KA. }
    split. { unfold MUL10_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. exact SDEF7. }
    intros a Ha CA NE DM. unfold MUL10_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in CA. apply CD7; assumption. }
  apply (KONT fx7 R7 M7 model2 g LB' cr').
  * unfold arith_post. cbv zeta. split. exact RP7. split. exact R7_10.
    exists ws', stF. split. exact VAL. split. exact RED. split. { cbn [L5.bo_len]. rewrite Lws'. lia. }
    cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_data].
    destruct g as [|A cap].
    -- destruct GCASE as (G0 & -> & -> & HG). assert (EF: fbR = fb) by (rewrite EfbR, G0; reflexivity). rewrite EF in OB7, OL7.
       split. exact OB7. split. exact OL7. split. exact HG. split. reflexivity. split. reflexivity.
       split. { subst stF. specialize (MATCH G0). destruct sto; destruct stR; try exact MATCH. exact I. }
       apply HP7. subst WF. reflexivity.
    -- destruct GCASE as (G1 & SR & L2 & C8' & -> & -> & FB & B0). assert (EF: fbR = Z.lor fb 1) by (rewrite EfbR, G1; reflexivity). rewrite EF in OB7, OL7.
       split. exact OB7. split. exact OL7. unfold L5.bo_dyn. cbn [L5.bo_fb].
       split. exact B0. split. exact L2. split. exact C8'. split. { subst stF. rewrite SR, C8'. reflexivity. } split. reflexivity. split. reflexivity.
       split. { pose proof FB as (FB1 & BA & DEFA). split. exact FB1. split. exact BA. eapply L5.defined_grows. eapply mem_grows_trans. exact GR26. exact GR7. exact DEFA. }
       apply HP7. subst WF. reflexivity.
  * exact MBV.
  * eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH2. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
    2: { eapply mem_grows_trans. exact GR26. exact GR7. }
    intros a Ha. rewrite MM7.
    assert (IN_DATA: data <= a < data + 8 * (Z.of_nat len + 1) -> (hl_ceil L <= a < hl_sptop L) \/ in_block LB' a).
    { intros Hin. destruct DW as [(D1 & Hl1 & _)|(D1 & cR & qR & SR & INB & HC)]. left. lia.
      right. exists (qR, 8 * cR). split. exact INB. cbn [fst snd]. subst data. rewrite SR in Hin. cbn [L5.bo_data L5.bo_st] in Hin. lia. }
    assert (CASE3: (o <= a < o + 16) \/ (data <= a < data + 8 * (Z.of_nat len + 1)) \/ (~ (o <= a < o + 16) /\ ~ (data <= a < data + 8 * (Z.of_nat len + 1))))
      by (clear - a o data len; lia).
    destruct CASE3 as [X|[X|[X Y]]]. { right; left. clear - X Olo Ohi SLO STOP. lia. } { right. apply IN_DATA. exact X. } { left. apply M62. exact Ha. exact X. exact Y. }
Qed.

End WithHeap.
End SCFG_1.

End L5MULT2.
