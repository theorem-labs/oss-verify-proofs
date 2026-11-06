(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan AsanPlanCore AsanPlan AsanPlanSound Ub0PlanKit AsanPlanSoundSums Ub0Sums
     BigLinkBase BigLinkGlueUb0 BigLinkInlBaseU BigLinkDivBaseU BigLinkMulAlg BigLinkMul BigLinkMulU L5Defs L5Words L5ReduceU L5ReduceGU
     L5Core L5CoreKit L5CoreKitU L5CoreSpecsU L5AReserveU L5ReserveU L5ResizePU L5ResizeU L5Mul10W L5Mul10PU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigFactsBase BigFactsDigits.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5MULT2U.
Import L5CSU.
Import L5MULPU.
Import L5MULW.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.


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
  (SLO : hl_sptop L - 2 ^ 23 + (96 + (64 + (48 + (64 + (16 + 8224))))) <= sp)
  (SHI : sp <= hl_sptop L)
  (STOP : 140735340871680 <= hl_sptop L <= 2 ^ 47)
  (Hr : 0 <= r < 2 ^ 47)
  (He : r mod 2 = 0)
  (LBhi : forall bb : Z * Z, In bb LB -> (fst bb) + (snd bb) <= hl_ceil L)
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
  (RG21 : 0 <= bv_unsigned (getr R (reg 21)) < 2 ^ 64)
  (RG22 : 0 <= bv_unsigned (getr R (reg 22)) < 2 ^ 64)
  (RG23 : 0 <= bv_unsigned (getr R (reg 23)) < 2 ^ 64)
  (RG24 : 0 <= bv_unsigned (getr R (reg 24)) < 2 ^ 64)
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
  (Dimg : (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1) <= 65536 \/ 598016 <= (L5.bo_data o (L5.BO (fbR) (S len) (stR))))
  (DW : o + 16 = (L5.bo_data o (L5.BO (fbR) (S len) (stR))) /\ (len <= 1)%nat /\ (exists u0 u1 : Z, stR = L5.BInl u0 u1) \/ (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1) <= hl_ceil L /\ exists cR qR : Z, stR = L5.BDyn cR qR /\ In (qR, 8 * cR) LB' /\ Z.of_nat len + 1 <= cR)
  (LwsA : length (ws ++ [0]) = S len)
  (RR : 0 <= bv_unsigned (getr R (reg 1)) < 2 ^ 64 /\ 0 <= bv_unsigned (getr R (reg 8)) < 2 ^ 64 /\ 0 <= bv_unsigned (getr R (reg 9)) < 2 ^ 64 /\ 0 <= bv_unsigned (getr R (reg 18)) < 2 ^ 64 /\ 0 <= bv_unsigned (getr R (reg 19)) < 2 ^ 64 /\ 0 <= bv_unsigned (getr R (reg 20)) < 2 ^ 64 /\ 0 <= bv_unsigned (getr R (reg 21)) < 2 ^ 64 /\ 0 <= bv_unsigned (getr R (reg 22)) < 2 ^ 64 /\ 0 <= bv_unsigned (getr R (reg 23)) < 2 ^ 64 /\ 0 <= bv_unsigned (getr R (reg 24)) < 2 ^ 64)
  (KEEP : forall a : Z, L5C.kept L LB sp (96 + (64 + (48 + (64 + (16 + 8224))))) ((o, 32) :: match g with | Same => [(L5.bo_data o (L5.BO (fb) (len) (sto)), 8 * (Z.of_nat len + 1))] | Grown _ _ => [] end) a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  (KD : forall a : Z, L5C.kept L LB sp (96 + (64 + (48 + (64 + (16 + 8224))))) ((o, 32) :: match g with | Same => [(L5.bo_data o (L5.BO (fb) (len) (sto)), 8 * (Z.of_nat len + 1))] | Grown _ _ => [] end) a -> ~ (L5.bo_data o (L5.BO (fbR) (S len) (stR))) <= a < (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1))
  (CD2 : forall a : Z, 0 <= a < 2 ^ 64 -> client_addr L LB sp (96 + (64 + (48 + (64 + (16 + 8224))))) a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None)
  (REGS : forall (R3 : bvmap 5 word) (ks : list nat), (forall x : nat, In x ks -> getr R3 (reg x) = getr R2 (reg x)) -> incl [3%nat; 4%nat; 25%nat; 26%nat; 27%nat] ks -> getr R3 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))) -> getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9))) -> getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R (reg 18))) -> getr R3 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R (reg 19))) -> getr R3 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R (reg 20))) -> getr R3 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R (reg 21))) -> getr R3 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R (reg 22))) -> getr R3 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R (reg 23))) -> getr R3 (reg 24) = Z_to_bv 64 (bv_unsigned (getr R (reg 24))) -> regs_preserved R R3)
  (SDEF_of : forall M5 : word -> option byte, mem_grows M2 M5 -> L5.defined M5 (sp - (96 + (64 + (48 + (64 + (16 + 8224)))))) (96 + (64 + (48 + (64 + (16 + 8224))))))
  (BtR : Z.testbit fbR 0 = (match stR with | L5.BInl _ _ => false | L5.BDyn _ _ => true end))
  (Edata : (if (match stR with | L5.BInl _ _ => false | L5.BDyn _ _ => true end) then (L5.bo_data o (L5.BO (fbR) (S len) (stR))) else o + 16) = (L5.bo_data o (L5.BO (fbR) (S len) (stR))))
  (DJ : (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1) <= sp - 96 \/ sp <= (L5.bo_data o (L5.BO (fbR) (S len) (stR))))
  (R4 : bvmap 5 word)
  (K4 : forall x : nat, In x KS2 -> In x KSIT -> getr R4 (reg x) = getr R2 (reg x))
  (R4_22 : bv_unsigned (getr R4 (reg 22)) = mcarry 10 (val ws) len)
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
  (M62 : forall a : Z, 0 <= a < 2 ^ 64 -> ~ o <= a < o + 16 -> ~ (L5.bo_data o (L5.BO (fbR) (S len) (stR))) <= a < (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1) -> ~ sp - 96 <= a < sp - 80 -> M6 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a))
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
  (R7_21 : getr R7 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R (reg 21))))
  (R7_22 : getr R7 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R (reg 22))))
  (R7_23 : getr R7 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R (reg 23))))
  (R7_24 : getr R7 (reg 24) = Z_to_bv 64 (bv_unsigned (getr R (reg 24))))
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
  { apply (REGS R7 [3; 4; 25; 26; 27]%nat).
    { intros x Hx. assert (HxC: In x L5K.CS) by (pose proof Hx as H'; L5K.inlist H'). assert (Hx2: In x KS2) by (pose proof Hx as H'; L5K.inlist H').
      assert (Hx3: In x KS3) by (pose proof Hx as H'; L5K.inlist H'). assert (Hx4: In x KS4) by (pose proof Hx as H'; L5K.inlist H').
      assert (HxI: In x KSIT) by (pose proof Hx as H'; L5K.inlist H').
      rewrite (K7 x Hx4). rewrite (L5K.regs_preserved_index R5 R6 x RP6 HxC). rewrite (K5 x Hx3). apply K4. exact Hx2. exact HxI. }
    intros x Hx; exact Hx. exact R7_2. exact R7_8. exact R7_9. exact R7_18. exact R7_19. exact R7_20. exact R7_21. exact R7_22. exact R7_23. exact R7_24. }
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
  { split. reflexivity. split. { subst ws' wl. apply Forall_forall. intros w Hw. apply (proj1 (Forall_forall _ _) (Forall_wlist (10 * V) (S len)) w). eapply L5RSZU.in_firstn. exact Hw. }
    cbn [L5.bo_st L5.bo_len]. subst stF. destruct stR as [u0 u1|cR qR].
    - destruct DW as [(D1 & Hl1 & _)|(_ & cR & qR & X & _)]; [|discriminate]. subst ws'. rewrite length_firstn, WL.
      subst wl. destruct len as [|[|k]]; [| |lia].
      + cbn [Nat.eqb]. replace (Nat.min (L5W.rlen (wlist (10 * V) 1)) 1) with (L5W.rlen (wlist (10 * V) 1)) by lia.
        change (wlist (10 * V) 1) with [wordi (10 * V) 0] in *. destruct (L5W.rlen [wordi (10 * V) 0]) as [|[|r2]] eqn:ER; [reflexivity|reflexivity|lia].
      + cbn [Nat.eqb]. replace (Nat.min (L5W.rlen (wlist (10 * V) 2)) 2) with (L5W.rlen (wlist (10 * V) 2)) by lia.
        change (wlist (10 * V) 2) with [wordi (10 * V) 0; wordi (10 * V) 1] in *. reflexivity.
    - destruct DW as [(_ & _ & u0 & u1 & X)|(D1 & cR' & qR' & X & INB & HC)]; [discriminate|]. injection X; intros <- <-. subst data. cbn [L5.bo_data L5.bo_st] in *.
      subst ws'. intros i Hi. rewrite length_firstn, WL in Hi. rewrite nth_firstn. replace (Nat.ltb i (L5W.rlen wl)) with true by (symmetry; apply Nat.ltb_lt; lia).
      eapply (BGU.u64_at_frame M5 M7). lia. lia. intros k Hk. rewrite MM7. apply FR6z; lia. apply LIM5. rewrite WL. lia. }
  (* [comment removed for export] *)
  assert (KV: forall a, L5C.kept L LB sp (96 + (64 + (48 + (64 + (16 + 8224))))) WF a -> ~ (sp - 96 <= a < sp - 80)).
  { intros a (Ha & CA & NE & OW) Hv. destruct CA as [IB|[[S1 S2]|IM]].
    - destruct IB as (bb & Hb & Hin). pose proof (LBhi bb Hb). clear - Hin H Hv SLO. lia.
    - clear - S1 S2 Hv. lia.
    - rewrite (ly_img_hi L LY) in IM. clear - IM Hv SLO STOP. lia. }
  assert (KEEP7: forall a, L5C.kept L LB sp (96 + (64 + (48 + (64 + (16 + 8224))))) WF a -> M7 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a KA. pose proof KA as (Ha & CA & NE & OW). pose proof (L5C.outside_cons_inv _ _ _ OW) as [NW _]. unfold L5.in_rng in NW. cbn [fst snd] in NW.
    rewrite MM7. rewrite M62. apply KEEP. exact KA. lia. lia. apply KD. exact KA. apply KV. exact KA. }
  assert (SDEF7: L5.defined M7 (sp - (96 + (64 + (48 + (64 + (16 + 8224)))))) (96 + (64 + (48 + (64 + (16 + 8224)))))).
  { apply SDEF_of. eapply mem_grows_trans. exact GR26. exact GR7. }
  assert (CD7: forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp (96 + (64 + (48 + (64 + (16 + 8224))))) a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M7 (Z_to_bv 64 a) <> None).
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
    assert (CASE4: (o <= a < o + 16) \/ (data <= a < data + 8 * (Z.of_nat len + 1)) \/ (sp - 96 <= a < sp - 80)
                   \/ (~ (o <= a < o + 16) /\ ~ (data <= a < data + 8 * (Z.of_nat len + 1)) /\ ~ (sp - 96 <= a < sp - 80)))
      by (clear - a o data len sp; lia).
    destruct CASE4 as [X|[X|[X|(X & Y & W)]]]. { right; left. clear - X Olo Ohi SLO STOP. lia. } { right. apply IN_DATA. exact X. }
    { right; left. clear - X SLO SHI STOP. lia. } { left. apply M62. exact Ha. exact X. exact Y. exact W. }
Qed.

End WithHeap.
End SCFG_1.

End L5MULT2U.
