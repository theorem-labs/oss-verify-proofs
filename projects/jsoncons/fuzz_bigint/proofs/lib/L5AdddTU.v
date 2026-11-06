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
     L5Core L5CoreKit L5CoreKitU L5CoreSpecsU L5AReserveU L5ReserveU L5ResizePU L5ResizeU L5Mul10W L5AdddPU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigModel BigFactsBase BigFactsDigits.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADDTU.
Import L5CSU.
Import L5ADDPU.
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
Lemma addd_tail
  (fx : FPState)
  (R : bvmap 5 word)
  (M : word -> option byte)
  (model : Model)
  (K : TSet)
  (LB : list (Z * Z))
  (cr : credit)
  (o : Z)
  (d : Z)
  (sp : Z)
  (r : Z)
  (fb : Z)
  (len : nat)
  (sto : L5.bstore)
  (ws : list Z)
  (Hd : 0 <= d <= 9)
  (Hlen : Z.of_nat len < 2 ^ 23)
  (RA : L5.ra_ok r)
  (Lws : length ws = len)
  (Rws : Forall (fun w : Z => 0 <= w < 2 ^ 64) ws)
  (Ao : o mod 8 = 0)
  (Olo : sp <= o)
  (Ohi : o + 32 <= hl_sptop L)
  (KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) (LB' : list (Z * Z)) (cr' : credit), arith_post L LB cr M M' R R' o sp ADDD_SCR (L5.BO (fb) (len) (sto)) (L5.limbs_val ws + d) g LB' cr' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') -> srealizes RSEGS SCFG (@cfg fx' R' r M' model') K)
  (A16 : sp mod 16 = 0)
  (SLO : hl_sptop L - 2 ^ 23 + (112 + (64 + (48 + (64 + (16 + 8224))))) <= sp)
  (SHI : sp <= hl_sptop L)
  (STOP : 140735340871680 <= hl_sptop L <= 2 ^ 47)
  (Hr : 0 <= r < 2 ^ 47)
  (He : r mod 2 = 0)
  (LBhi : forall bb : Z * Z, In bb LB -> (fst bb) + (snd bb) <= hl_ceil L)
  (Hfb : 0 <= fb < 256)
  (VB : 0 <= (val ws) < W.M ^ Z.of_nat len)
  (Hlen27 : Z.of_nat len <= 2 ^ 27)
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
  (Mh2 : m_halted model2 = None)
  (Ml2 : m_vm_lazy model2 = [])
  (RL : resize_limbs ws (S len) = ws ++ [0])
  (fbR : Z)
  (stR : L5.bstore)
  (grown : bool)
  (EfbR : fbR = (if grown then Z.lor fb 1 else fb))
  (MATCH : grown = false -> match sto with | L5.BInl _ _ => match stR with | L5.BInl _ _ => (len <= 1)%nat | L5.BDyn _ _ => False end | L5.BDyn c q => match stR with | L5.BInl _ _ => False | L5.BDyn c' q' => c' = c /\ q' = q end end)
  (GCASE : match g with | Same => grown = false /\ LB' = LB /\ cr' = cr /\ (L5.bo_dyn (L5.BO (fb) (len) (sto)) = true \/ (len <= 1)%nat) | Grown A cap => grown = true /\ stR = L5.BDyn cap A /\ len = 2%nat /\ cap = 8 /\ LB' = (A, 64) :: LB /\ cr' = debit L cr 64 /\ L5C.fresh_block L LB M2 A 64 /\ Z.testbit fb 0 = false end)
  (Q0 : L5.u8_at RSEGS M2 o fbR)
  (HfbR : 0 <= fbR < 256)
  (Q8 : L5.u64_at RSEGS M2 (o + 8) (Z.of_nat (S len)))
  (QST : match stR with | L5.BInl v0 v1 => Z.testbit fbR 0 = false /\ L5.u64_at RSEGS M2 (o + 16) v0 /\ L5.u64_at RSEGS M2 (o + 24) v1 /\ (S len <= 2)%nat /\ 0 <= v0 < 2 ^ 64 /\ 0 <= v1 < 2 ^ 64 | L5.BDyn cap q => Z.testbit fbR 0 = true /\ L5.u64_at RSEGS M2 (o + 16) cap /\ L5.u64_at RSEGS M2 (o + 24) q /\ Z.of_nat (S len) <= cap /\ 1 <= cap <= 2 ^ 27 /\ q mod 8 = 0 /\ 4096 <= q /\ q + 8 * cap <= 2 ^ 47 /\ L5.hull_apart RSEGS q (8 * cap) end)
  (NEGR : Z.testbit fbR 1 = false)
  (Dlo : 4096 <= (L5.bo_data o (L5.BO (fbR) (S len) (stR))))
  (Da : (L5.bo_data o (L5.BO (fbR) (S len) (stR))) mod 8 = 0)
  (Dhi : (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1) <= 2 ^ 47)
  (Dimg : (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1) <= 65536 \/ 598016 <= (L5.bo_data o (L5.BO (fbR) (S len) (stR))))
  (DW : o + 16 = (L5.bo_data o (L5.BO (fbR) (S len) (stR))) /\ (len <= 1)%nat /\ (exists u0 u1 : Z, stR = L5.BInl u0 u1) \/ (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1) <= hl_ceil L /\ exists cR qR : Z, stR = L5.BDyn cR qR /\ In (qR, 8 * cR) LB' /\ Z.of_nat len + 1 <= cR)
  (LwsA : length (ws ++ [0]) = S len)
  (WR2 : BGU.writable M2 (sp - 112) 112)
  (AT : at_ret1 R2 M2 o d sp (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9))) (bv_unsigned (getr R (reg 18))) (bv_unsigned (getr R (reg 19))) (bv_unsigned (getr R (reg 20))))
  (KEEP : forall a : Z, L5C.kept L LB sp (112 + (64 + (48 + (64 + (16 + 8224))))) ((o, 32) :: match g with | Same => [(L5.bo_data o (L5.BO (fb) (len) (sto)), 8 * (Z.of_nat len + 1))] | Grown _ _ => [] end) a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  (KD : forall a : Z, L5C.kept L LB sp (112 + (64 + (48 + (64 + (16 + 8224))))) ((o, 32) :: match g with | Same => [(L5.bo_data o (L5.BO (fb) (len) (sto)), 8 * (Z.of_nat len + 1))] | Grown _ _ => [] end) a -> ~ (L5.bo_data o (L5.BO (fbR) (S len) (stR))) <= a < (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1))
  (CD2 : forall a : Z, 0 <= a < 2 ^ 64 -> client_addr L LB sp (112 + (64 + (48 + (64 + (16 + 8224))))) a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None)
  (REGS : forall (R3 : bvmap 5 word) (ks : list nat), (forall x : nat, In x ks -> getr R3 (reg x) = getr R2 (reg x)) -> incl [3%nat; 4%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat] ks -> getr R3 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))) -> getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9))) -> getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R (reg 18))) -> getr R3 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R (reg 19))) -> getr R3 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R (reg 20))) -> regs_preserved R R3)
  (SDEF_of : forall M5 : word -> option byte, mem_grows M2 M5 -> L5.defined M5 (sp - (112 + (64 + (48 + (64 + (16 + 8224)))))) (112 + (64 + (48 + (64 + (16 + 8224))))))
  (DEFO2 : L5.defined M2 o 32)
  (BtR : Z.testbit fbR 0 = (match stR with | L5.BInl _ _ => false | L5.BDyn _ _ => true end))
  (Edata : (if (match stR with | L5.BInl _ _ => false | L5.BDyn _ _ => true end) then (L5.bo_data o (L5.BO (fbR) (S len) (stR))) else o + 16) = (L5.bo_data o (L5.BO (fbR) (S len) (stR))))
  (LBwf2 : forall q c : Z, In (q, 8 * c) LB' -> (4096 <= q /\ (q + 8 * c <= 65536 \/ 598016 <= q)) /\ q + 8 * c <= hl_ceil L /\ L5.defined M2 q (8 * c))
  (Hx0R : 0 <= (nth 0 (ws ++ [0]) 0) < 2 ^ 64)
  (X0W : (nth 0 (ws ++ [0]) 0) = wordi (val ws) 0)
  (DJ : (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1) <= sp - 112 \/ sp <= (L5.bo_data o (L5.BO (fbR) (S len) (stR))))
  (fx4 : FPState)
  (R4 : bvmap 5 word)
  (M4 : word -> option byte)
  (K4 : forall x : nat, In x KSF -> getr R4 (reg x) = getr R2 (reg x))
  (LIMBS4 : limbs M4 (L5.bo_data o (L5.BO (fbR) (S len) (stR))) (wordi ((val ws) + d)) 0 (S len))
  (MF4 : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (L5.bo_data o (L5.BO (fbR) (S len) (stR))) <= a < (L5.bo_data o (L5.BO (fbR) (S len) (stR))) + 8 * (Z.of_nat len + 1) -> ~ sp - 80 <= a < sp - 64 -> M4 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a))
  (GR4 : mem_grows M2 M4)
  : srealizes RSEGS SCFG (mkCfg (st fx4 R4 TAIL M4) (model2)) K.

Proof.
  set (V := val ws) in *.
  set (data := L5.bo_data o (L5.BO fbR (S len) stR)) in *.
  set (WF := (o, 32) :: match g with Same => [(L5.bo_data o (L5.BO fb len sto), 8 * (Z.of_nat len + 1))] | Grown _ _ => [] end) in *.
  set (td := match stR with L5.BDyn _ _ => true | L5.BInl _ _ => false end) in *.
  set (x0 := nth 0 (ws ++ [0]) 0) in *.
  (* [comment removed for export] *)
  assert (VBD: 0 <= V + d < W.M ^ Z.of_nat (S len)).
  { destruct len as [|len']. { rewrite M_val in VB |- *. cbn in VB |- *. lia. }
    apply (add_value_bound d V (S len')). unfold wordZ; rewrite M_val; lia. exact VB. lia. }
  destruct AT as (A8 & A9 & A2 & D8 & D16 & D24 & D32 & D40 & D48 & RR).
  assert (R4_2: getr R4 (reg 2) = Z_to_bv 64 (sp - 112)). { rewrite (K4 2%nat) by (apply L5K.In_of_mem; reflexivity). exact A2. }
  assert (R4_8: getr R4 (reg 8) = Z_to_bv 64 o). { rewrite (K4 8%nat) by (apply L5K.In_of_mem; reflexivity). exact A8. }
  assert (WR4: BGU.writable M4 (sp - 112) 112). { change (L5.writable RSEGS M4 (sp - 112) 112). eapply L5.writable_grows. exact GR4. exact WR2. }
  destruct (p4_run fx4 R4 M4 o sp R4_2 R4_8 ltac:(clear - o Olo Ohi SLO STOP; lia) A16 ltac:(clear - sp SLO STOP; lia) ltac:(clear - sp SHI STOP; lia) WR4)
    as (fx5 & R5 & MS5 & K5 & R5_1 & R5_2 & R5_8 & R5_10).
  eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS5.
  (* [comment removed for export] *)
  set (wl := wlist (V + d) (S len)).
  assert (WL: length wl = S len) by (subst wl; apply wlist_length).
  assert (LIM4: L5.limbs_at RSEGS M4 data wl).
  { intros i Hi. rewrite WL in Hi. subst wl. rewrite wlist_nth' by exact Hi. apply LIMBS4. lia. }
  (* [comment removed for export] *)
  set (stF := match stR with L5.BInl _ v1 => L5.BInl (wordi (V + d) 0) (if Nat.eqb len 0 then v1 else wordi (V + d) 1) | L5.BDyn c q => L5.BDyn c q end).
  assert (HK8: forall a v, o <= a -> a + 8 <= o + 32 -> (a + 8 <= o + 16 \/ data + 8 * (Z.of_nat len + 1) <= hl_ceil L) -> BGU.u64_at M2 a v -> BGU.u64_at M4 a v).
  { intros a v H1a H2a H3a Hu. eapply (BGU.u64_at_frame M2 M4). lia. lia. intros k Hk. apply MF4. lia. destruct DW as [(D1 & _)|(D1 & _)]; lia. clear - Hk H1a Olo; lia. exact Hu. }
  assert (OB4: L5.big_at RSEGS M4 o (L5.BO fbR (S len) stF)).
  { unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
    split. { eapply (BGU.u8_at_frame M2 M4). apply MF4. lia. destruct DW as [(D1 & _)|(D1 & _)]; lia. clear - Olo; lia. exact Q0. }
    split. exact HfbR. split. { apply HK8. lia. lia. left; lia. exact Q8. }
    subst stF. destruct stR as [u0 u1|cR qR].
    - destruct QST as (B0 & Q16 & Q24' & HlR & Ru0 & Ru1). destruct DW as [(D1 & Hl1 & _)|(_ & cR & qR & X & _)]; [|discriminate].
      split. exact B0. split. { pose proof (LIM4 0%nat ltac:(rewrite WL; lia)) as X. subst wl. rewrite wlist_nth' in X by lia. rewrite Z.mul_0_r, Z.add_0_r, <- D1 in X. exact X. }
      split. { destruct (Nat.eqb_spec len 0).
               - eapply (BGU.u64_at_frame M2 M4). lia. lia. intros k Hk. apply MF4. lia. rewrite <- D1. lia. clear - Hk Olo; lia. exact Q24'.
               - pose proof (LIM4 1%nat ltac:(rewrite WL; lia)) as X. subst wl. rewrite wlist_nth' in X by lia. rewrite <- D1 in X.
                 replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) in X by lia. exact X. }
      split. exact HlR. split. { pose proof (wordi_range (V + d) 0) as W0. unfold wordZ in W0. rewrite M_val in W0. lia. }
      destruct (Nat.eqb len 0). lia. pose proof (wordi_range (V + d) 1) as W1. unfold wordZ in W1. rewrite M_val in W1. lia.
    - destruct QST as (B0 & Q16 & Q24' & HlcR & HcR & AqR & QloR & QhiR & HAPR). destruct DW as [(_ & _ & u0 & u1 & X)|(D1 & _)]; [discriminate|].
      split. exact B0. split. { apply HK8. lia. lia. right; exact D1. exact Q16. }
      split. { apply HK8. lia. lia. right; exact D1. exact Q24'. } repeat split; try lia. exact HAPR. }
  assert (DATF: L5.bo_data o (L5.BO fbR (S len) stF) = data). { subst stF data. destruct stR; reflexivity. }
  assert (WO4: L5.writable RSEGS M4 o 16).
  { apply L5C.writable_of_defined; [|lia|lia]. eapply L5.defined_grows. exact GR4. eapply L5.defined_sub. exact DEFO2. lia. lia. }
  assert (DCAP: L5.defined M4 (L5.bo_data o (L5.BO fbR (S len) stF)) (8 * L5.bo_cap (L5.BO fbR (S len) stF))).
  { rewrite DATF. subst stF. destruct stR as [u0 u1|cR qR]; cbn [L5.bo_cap L5.bo_st].
    - destruct DW as [(D1 & Hl1 & _)|(_ & cR & qR & X & _)]; [|discriminate]. rewrite <- D1. eapply L5.defined_grows. exact GR4. eapply L5.defined_sub. exact DEFO2. lia. lia.
    - destruct DW as [(_ & _ & u0 & u1 & X)|(D1 & cR' & qR' & X & INB & HC)]; [discriminate|]. injection X; intros <- <-.
      eapply L5.defined_grows. exact GR4. subst data. cbn [L5.bo_data L5.bo_st]. exact (proj2 (proj2 (LBwf2 _ _ INB))). }
  assert (APF: forall cap q, L5.bo_st (L5.BO fbR (S len) stF) = L5.BDyn cap q -> q + 8 * cap <= o \/ o + 32 <= q).
  { cbn [L5.bo_st]. subst stF. destruct stR as [u0 u1|cR qR]. intros; discriminate. intros cap q X. injection X; intros <- <-.
    destruct DW as [(_ & _ & u0 & u1 & X')|(D1 & cR' & qR' & X' & INB & HC)]; [discriminate|]. injection X'; intros <- <-. left. destruct (LBwf2 _ _ INB) as (_ & X2 & _). lia. }
  destruct (L5REDGU.reduce_run fx5 R5 M4 o RET2 (L5.BO fbR (S len) stF) wl R5_10 R5_1 ltac:(split; [unfold RET2; lia|reflexivity]) OB4 Ao ltac:(lia) ltac:(lia)
              WO4 DCAP ltac:(rewrite DATF; exact LIM4) WL (Forall_wlist (V + d) (S len)) APF)
    as (fx6 & R6 & M6 & MS6 & POST6).
  unfold L5REDU.reduce_post in POST6. cbv zeta in POST6. cbn [L5.bo_fb L5.bo_len L5.bo_st] in POST6.
  destruct POST6 as (OB6 & RP6 & R6_10 & FR6 & GR6).
  assert (FL6: (if Nat.eqb (L5W.rlen wl) 0 then Z.land fbR 253 else fbR) = fbR).
  { destruct (Nat.eqb (L5W.rlen wl) 0). apply land253_id. lia. exact NEGR. reflexivity. }
  rewrite FL6 in OB6.
  eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS6.
  assert (FR6z: forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 16) -> M6 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Ha Hna. apply FR6. intros rg [<-|[]]. unfold L5.in_rng. cbn [fst snd]. rewrite BGU.unsigned_lit by lia. lia. }
  assert (M62: forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 16) -> ~ (data <= a < data + 8 * (Z.of_nat len + 1)) -> ~ (sp - 80 <= a < sp - 64) -> M6 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha H1a H2a H3a. rewrite FR6z by lia. apply MF4. lia. exact H2a. exact H3a. }
  assert (GR26: mem_grows M2 M6). { eapply mem_grows_trans. exact GR4. exact GR6. }
  assert (T6: forall a v, sp - 48 <= a -> a + 8 <= sp -> BGU.u64_at M2 a v -> BGU.u64_at M6 a v).
  { intros a v H1a H2a Hu. eapply (BGU.u64_at_frame M2 M6). lia. lia. intros k Hk. apply M62. lia. lia. destruct DW as [(D1 & _)|(D1 & _)]; lia. clear - Hk H1a; lia. exact Hu. }
  assert (WR6: BGU.writable M6 (sp - 112) 112).
  { change (L5.writable RSEGS M6 (sp - 112) 112). eapply L5.writable_grows. exact GR26. exact WR2. }
  assert (R6_8: getr R6 (reg 8) = Z_to_bv 64 o). { rewrite <- L5K.rl8, (RP6 8%bv ltac:(cbn; tauto)), L5K.rl8. exact R5_8. }
  assert (R6_2: getr R6 (reg 2) = Z_to_bv 64 (sp - 112)). { rewrite <- L5K.rl2, (RP6 2%bv ltac:(cbn; tauto)), L5K.rl2. exact R5_2. }
  destruct (p5_run fx6 R6 M6 o sp _ _ _ _ _ _ r R6_8 R6_2
              ltac:(apply T6; [clear - sp; lia|clear - sp; lia|exact D8]) ltac:(apply T6; [clear - sp; lia|clear - sp; lia|exact D16]) ltac:(apply T6; [clear - sp; lia|clear - sp; lia|exact D24])
              ltac:(apply T6; [clear - sp; lia|clear - sp; lia|exact D32]) ltac:(apply T6; [clear - sp; lia|clear - sp; lia|exact D40]) ltac:(apply T6; [clear - sp; lia|clear - sp; lia|exact D48])
              RG1 RG8 RG9 RG18 RG19 RG20 ltac:(clear - o Olo Ohi SLO STOP; lia) A16 ltac:(clear - sp SLO STOP; lia) ltac:(clear - sp SHI STOP; lia) WR6 E1 RA)
    as (fx7 & R7 & M7 & MS7 & K7 & R7_1 & R7_2 & R7_8 & R7_9 & R7_18 & R7_19 & R7_20 & R7_10 & MM7 & GR7).
  eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS7.
  (* [comment removed for export] *)
  assert (RP7: regs_preserved R R7).
  { apply (REGS R7 [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat).
    { intros x Hx. assert (HxC: In x L5K.CS) by (pose proof Hx as H'; L5K.inlist H'). assert (HxF: In x KSF) by (pose proof Hx as H'; L5K.inlist H').
      assert (Hx4: In x KS4) by (pose proof Hx as H'; L5K.inlist H'). assert (Hx5: In x KS5) by (pose proof Hx as H'; L5K.inlist H').
      rewrite (K7 x Hx5). rewrite (L5K.regs_preserved_index R5 R6 x RP6 HxC). rewrite (K5 x Hx4). apply K4. exact HxF. }
    intros x Hx; exact Hx. exact R7_2. exact R7_8. exact R7_9. exact R7_18. exact R7_19. exact R7_20. }
  set (ws' := firstn (L5W.rlen wl) wl).
  pose proof (L5W.rlen_le wl) as RLE. rewrite WL in RLE.
  assert (Lws': length ws' = L5W.rlen wl). { subst ws'. rewrite length_firstn, WL. lia. }
  assert (VAL: L5.limbs_val ws' = L5.limbs_val ws + d).
  { rewrite !limbs_val_val. change (val ws) with V. subst ws'. rewrite val_firstn_zeros. subst wl. apply val_wlist_small. exact VBD. rewrite WL. lia.
    intros i Hi. apply (L5W.rlen_zeros wl i). rewrite WL. lia. }
  assert (RED: reduced ws').
  { unfold reduced. destruct (Nat.eq_dec (L5W.rlen wl) 0) as [Z0|NZ]. left. subst ws'. rewrite Z0. reflexivity.
    right. rewrite Lws'. subst ws'. rewrite nth_firstn. replace (Nat.ltb (L5W.rlen wl - 1) (L5W.rlen wl)) with true by (symmetry; apply Nat.ltb_lt; lia).
    apply (L5W.rlen_top wl). lia. }
  assert (OB7: L5.big_at RSEGS M7 o (L5.BO fbR (length ws') stF)). { rewrite Lws'. eapply (L5C.big_at_agree RSEGS M6 M7). intros i Hi. apply MM7. lia. lia. exact OB6. }
  assert (OL7: L5C.obj_limbs RSEGS M7 (L5.BO fbR (length ws') stF) ws').
  { split. reflexivity. split. { subst ws' wl. apply Forall_forall. intros w Hw. apply (proj1 (Forall_forall _ _) (Forall_wlist (V + d) (S len)) w). eapply L5RSZU.in_firstn. exact Hw. }
    cbn [L5.bo_st L5.bo_len]. subst stF. destruct stR as [u0 u1|cR qR].
    - destruct DW as [(D1 & Hl1 & _)|(_ & cR & qR & X & _)]; [|discriminate]. subst ws'. rewrite length_firstn, WL.
      subst wl. destruct len as [|[|k]]; [| |lia].
      + cbn [Nat.eqb]. replace (Nat.min (L5W.rlen (wlist (V + d) 1)) 1) with (L5W.rlen (wlist (V + d) 1)) by lia.
        change (wlist (V + d) 1) with [wordi (V + d) 0] in *. destruct (L5W.rlen [wordi (V + d) 0]) as [|[|r2]] eqn:ER; [reflexivity|reflexivity|lia].
      + cbn [Nat.eqb]. replace (Nat.min (L5W.rlen (wlist (V + d) 2)) 2) with (L5W.rlen (wlist (V + d) 2)) by lia.
        change (wlist (V + d) 2) with [wordi (V + d) 0; wordi (V + d) 1] in *. reflexivity.
    - destruct DW as [(_ & _ & u0 & u1 & X)|(D1 & cR' & qR' & X & INB & HC)]; [discriminate|]. injection X; intros <- <-. subst data. cbn [L5.bo_data L5.bo_st] in *.
      subst ws'. intros i Hi. rewrite length_firstn, WL in Hi. rewrite nth_firstn. replace (Nat.ltb i (L5W.rlen wl)) with true by (symmetry; apply Nat.ltb_lt; lia).
      eapply (BGU.u64_at_frame M4 M7). lia. lia. intros k Hk. rewrite MM7. apply FR6z; lia. apply LIM4. rewrite WL. lia. }
  (* [comment removed for export] *)
  assert (KV: forall a, L5C.kept L LB sp (112 + (64 + (48 + (64 + (16 + 8224))))) WF a -> ~ (sp - 80 <= a < sp - 64)).
  { intros a (Ha & CA & NE & OW) Hv. destruct CA as [IB|[[S1 S2]|IM]].
    - destruct IB as (bb & Hb & Hin). pose proof (LBhi bb Hb). clear - Hin H Hv SLO. lia.
    - clear - S1 S2 Hv. lia.
    - rewrite (ly_img_hi L LY) in IM. clear - IM Hv SLO STOP. lia. }
  assert (KEEP7: forall a, L5C.kept L LB sp (112 + (64 + (48 + (64 + (16 + 8224))))) WF a -> M7 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a KA. pose proof KA as (Ha & CA & NE & OW). pose proof (L5C.outside_cons_inv _ _ _ OW) as [NW _]. unfold L5.in_rng in NW. cbn [fst snd] in NW.
    rewrite MM7. rewrite M62. apply KEEP. exact KA. lia. lia. apply KD. exact KA. apply KV. exact KA. }
  assert (SDEF7: L5.defined M7 (sp - (112 + (64 + (48 + (64 + (16 + 8224)))))) (112 + (64 + (48 + (64 + (16 + 8224)))))).
  { apply SDEF_of. eapply mem_grows_trans. exact GR26. exact GR7. }
  assert (CD7: forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp (112 + (64 + (48 + (64 + (16 + 8224))))) a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M7 (Z_to_bv 64 a) <> None).
  { intros a Ha CA NE DM. apply GR7. apply GR26. apply CD2; assumption. }
  assert (HP7: forall W', W' = WF -> L5C.hpres L LB sp ADDD_SCR W' M M7).
  { intros W' ->. split. { intros a KA. apply KEEP7. unfold ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in KA. exact KA. }
    split. { unfold ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. exact SDEF7. }
    intros a Ha CA NE DM. unfold ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in CA. apply CD7; assumption. }
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
    assert (CASE4: (o <= a < o + 16) \/ (data <= a < data + 8 * (Z.of_nat len + 1)) \/ (sp - 80 <= a < sp - 64)
                   \/ (~ (o <= a < o + 16) /\ ~ (data <= a < data + 8 * (Z.of_nat len + 1)) /\ ~ (sp - 80 <= a < sp - 64)))
      by (clear - a o data len sp; lia).
    destruct CASE4 as [X|[X|[X|(X & Y & W)]]]. { right; left. clear - X Olo Ohi SLO STOP. lia. } { right. apply IN_DATA. exact X. }
    { right; left. clear - X SLO SHI STOP. lia. } { left. apply M62. exact Ha. exact X. exact Y. exact W. }
Qed.

End WithHeap.
End SCFG_1.

End L5ADDTU.
