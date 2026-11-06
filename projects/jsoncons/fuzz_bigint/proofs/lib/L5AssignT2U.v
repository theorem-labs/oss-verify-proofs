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
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore AsanPlanSoundSums Ub0Sums
     BigLinkBase BigLinkGlueUb0 BigLinkInlBaseU BigLinkDivBaseU L5Defs L5Core L5CoreKit L5CoreKitU L5CoreSpecsU L5AReserveU L5ReserveU L5ResizePU L5ResizeU L5AssignPU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ASGT2U.
Import L5CSU.
Import L5ASGPU.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
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
Lemma assign_tail_post
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
  (CR : (3 <= len')%nat -> L5.bo_dyn (L5.BO (fb) (len) (sto)) = false -> credit_ok L cr (8 * round_up (Z.of_nat len')))
  (Ao : o mod 8 = 0)
  (Olo : sp <= o)
  (Ohi : o + 32 <= hl_sptop L)
  (BLK : forall cap q : Z, sto = L5.BDyn cap q -> In (q, 8 * cap) LB)
  (Lws' : length ws' = len')
  (Rws' : Forall (fun w : Z => 0 <= w < 2 ^ 64) ws')
  (Ao' : o' mod 8 = 0)
  (Olo' : sp <= o')
  (Ohi' : o' + 32 <= hl_sptop L)
  (APO : o + 32 <= o' \/ o' + 32 <= o)
  (KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) (LB' : list (Z * Z)) (cr' : credit), assign_post L LB cr M M' R R' o o' sp (L5.BO (fb) (len) (sto)) (L5.BO (fb') (len') (sto')) ws' g LB' cr' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') -> srealizes RSEGS SCFG (@cfg fx' R' r M' model') K)
  (A16 : sp mod 16 = 0)
  (SLO : hl_sptop L - 2 ^ 23 + (48 + (64 + (48 + (64 + (16 + 8224))))) <= sp)
  (SHI : sp <= hl_sptop L)
  (STOP : 140735340871680 <= hl_sptop L <= 2 ^ 47)
  (Hr : 0 <= r < 2 ^ 47)
  (He : r mod 2 = 0)
  (LBhi : forall bb : Z * Z, In bb LB -> (fst bb) + (snd bb) <= hl_ceil L)
  (LBwf : forall q c : Z, In (q, 8 * c) LB -> (4096 <= q /\ (q + 8 * c <= 65536 \/ 598016 <= q)) /\ q + 8 * c <= hl_ceil L /\ L5.defined M q (8 * c))
  (Hfb : 0 <= fb < 256)
  (Hfb' : 0 <= fb' < 256)
  (y24 : Z)
  (Hy24 : 0 <= y24 < 2 ^ 64)
  (Ey24 : match sto' with | L5.BInl _ v1 => y24 = v1 | L5.BDyn _ q' => y24 = q' end)
  (wsT : list Z)
  (Hlen : Z.of_nat len <= 2 ^ 27)
  (RG1 : 0 <= bv_unsigned (getr R (reg 1)) < 2 ^ 64)
  (RG8 : 0 <= bv_unsigned (getr R (reg 8)) < 2 ^ 64)
  (RG9 : 0 <= bv_unsigned (getr R (reg 9)) < 2 ^ 64)
  (RG18 : 0 <= bv_unsigned (getr R (reg 18)) < 2 ^ 64)
  (RG19 : 0 <= bv_unsigned (getr R (reg 19)) < 2 ^ 64)
  (RG20 : 0 <= bv_unsigned (getr R (reg 20)) < 2 ^ 64)
  (E1 : bv_unsigned (getr R (reg 1)) = r)
  (NEQ : o <> o')
  (BtO : Z.testbit fb' 0 = (L5.bo_dyn (L5.BO (fb') (len') (sto'))))
  (Esrc : (if (L5.bo_dyn (L5.BO (fb') (len') (sto'))) then y24 else o' + 16) = (L5.bo_data o' (L5.BO (fb') (len') (sto'))))
  (SRCr : 4096 <= (L5.bo_data o' (L5.BO (fb') (len') (sto'))) < 2 ^ 47)
  (SRCa : (L5.bo_data o' (L5.BO (fb') (len') (sto'))) mod 8 = 0)
  (SRCe : (L5.bo_data o' (L5.BO (fb') (len') (sto'))) + 8 * Z.of_nat len' <= 2 ^ 47)
  (M1 : word -> option byte)
  (R2 : bvmap 5 word)
  (M2 : word -> option byte)
  (model2 : Model)
  (g : growth)
  (LB' : list (Z * Z))
  (cr' : credit)
  (POST : match g with | Same => (L5.bo_dyn (L5.BO (fb) (len) (sto)) = true \/ (len' <= 2)%nat) /\ LB' = LB /\ cr' = cr /\ (exists st' : L5.bstore, L5.big_at RSEGS M2 o (L5.BO (L5.bo_fb (L5.BO (fb) (len) (sto))) (len') (st')) /\ L5C.obj_limbs RSEGS M2 (L5.BO (L5.bo_fb (L5.BO (fb) (len) (sto))) (len') (st')) (resize_limbs wsT len') /\ match L5.bo_st (L5.BO (fb) (len) (sto)) with | L5.BInl _ _ => match st' with | L5.BInl _ _ => True | L5.BDyn _ _ => False end | L5.BDyn cap q => match st' with | L5.BInl _ _ => False | L5.BDyn cap' q' => cap' = cap /\ q' = q end end) /\ L5C.hpres L LB (sp - 48) RESIZE_SCR [(o, 32); (L5.bo_data o (L5.BO (fb) (len) (sto)) + 8 * Z.of_nat (L5.bo_len (L5.BO (fb) (len) (sto))), 8 * (Z.max (0) ((Z.of_nat len' - Z.of_nat (L5.bo_len (L5.BO (fb) (len) (sto)))))))] M1 M2 | Grown A cap => L5.bo_dyn (L5.BO (fb) (len) (sto)) = false /\ (3 <= len')%nat /\ cap = round_up (Z.of_nat len') /\ LB' = (A, 8 * cap) :: LB /\ cr' = debit L cr (8 * cap) /\ L5C.fresh_block L LB M2 A (8 * cap) /\ L5.big_at RSEGS M2 o (L5.BO (Z.lor (L5.bo_fb (L5.BO (fb) (len) (sto))) 1) (len') (L5.BDyn cap A)) /\ L5C.obj_limbs RSEGS M2 (L5.BO (Z.lor (L5.bo_fb (L5.BO (fb) (len) (sto))) 1) (len') (L5.BDyn cap A)) (resize_limbs wsT len') /\ L5C.hpres L LB (sp - 48) RESIZE_SCR [(o, 32)] M1 M2 end)
  (MBV : model_but_vm model model2)
  (HH2 : hi_heap HI LB' cr' M2 (m_vmmaps model2))
  (fbR : Z)
  (stR : L5.bstore)
  (grown : bool)
  (EfbR : fbR = (if grown then Z.lor fb 1 else fb))
  (BfbR : Z.testbit fbR 0 = grown || Z.testbit fb 0)
  (DSThi : (L5.bo_data o (L5.BO (fbR) (len') (stR))) + 8 * Z.of_nat len' <= 2 ^ 47)
  (DSTlo : 4096 <= (L5.bo_data o (L5.BO (fbR) (len') (stR))))
  (GCASE : match g with | Same => grown = false /\ LB' = LB /\ cr' = cr /\ (L5.bo_dyn (L5.BO (fb) (len) (sto)) = true \/ (len' <= 2)%nat) /\ match sto with | L5.BInl _ _ => match stR with | L5.BInl _ _ => (len' <= 2)%nat | L5.BDyn _ _ => False end | L5.BDyn c q => match stR with | L5.BInl _ _ => False | L5.BDyn c' q' => c' = c /\ q' = q end end | Grown A cap => grown = true /\ stR = L5.BDyn cap A /\ (3 <= len')%nat /\ cap = round_up (Z.of_nat len') /\ LB' = (A, 8 * cap) :: LB /\ cr' = debit L cr (8 * cap) /\ L5C.fresh_block L LB M2 A (8 * cap) /\ Z.testbit fb 0 = false end)
  (HfbR : 0 <= fbR < 256)
  (Q8 : L5.u64_at RSEGS M2 (o + 8) (Z.of_nat len'))
  (QST : match stR with | L5.BInl v0 v1 => Z.testbit fbR 0 = false /\ L5.u64_at RSEGS M2 (o + 16) v0 /\ L5.u64_at RSEGS M2 (o + 24) v1 /\ (len' <= 2)%nat /\ 0 <= v0 < 2 ^ 64 /\ 0 <= v1 < 2 ^ 64 | L5.BDyn cap q => Z.testbit fbR 0 = true /\ L5.u64_at RSEGS M2 (o + 16) cap /\ L5.u64_at RSEGS M2 (o + 24) q /\ Z.of_nat len' <= cap /\ 1 <= cap <= 2 ^ 27 /\ q mod 8 = 0 /\ 4096 <= q /\ q + 8 * cap <= 2 ^ 47 /\ L5.hull_apart RSEGS q (8 * cap) end)
  (KEEP : forall a : Z, L5C.kept L LB sp (48 + (64 + (48 + (64 + (16 + 8224))))) ((o, 32) :: match g with | Same => [(L5.bo_data o (L5.BO (fb) (len) (sto)), 8 * (Z.max (Z.of_nat len') (Z.of_nat len)))] | Grown _ _ => [] end) a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  (CD2 : forall a : Z, 0 <= a < 2 ^ 64 -> client_addr L LB sp (48 + (64 + (48 + (64 + (16 + 8224))))) a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None)
  (REGS : forall (R3 : bvmap 5 word) (ks : list nat), (forall x : nat, In x ks -> getr R3 (reg x) = getr R2 (reg x)) -> incl [3%nat; 4%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat] ks -> getr R3 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))) -> getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9))) -> getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R (reg 18))) -> getr R3 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R (reg 19))) -> regs_preserved R R3)
  (SDEF_of : forall M5 : word -> option byte, (forall a : Z, sp - (48 + (64 + (48 + (64 + (16 + 8224))))) <= a < sp -> M5 (Z_to_bv 64 a) <> None \/ M5 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) -> mem_grows M2 M5 -> L5.defined M5 (sp - (48 + (64 + (48 + (64 + (16 + 8224)))))) (48 + (64 + (48 + (64 + (16 + 8224))))))
  (BtR : Z.testbit fbR 0 = (match stR with | L5.BInl _ _ => false | L5.BDyn _ _ => true end))
  (Edst : (if (match stR with | L5.BInl _ _ => false | L5.BDyn _ _ => true end) then (L5.bo_data o (L5.BO (fbR) (len') (stR))) else o + 16) = (L5.bo_data o (L5.BO (fbR) (len') (stR))))
  (DSTr : 4096 <= (L5.bo_data o (L5.BO (fbR) (len') (stR))) < 2 ^ 47)
  (DSTa : (L5.bo_data o (L5.BO (fbR) (len') (stR))) mod 8 = 0)
  (LENP : len' <> 0%nat)
  (R3 : bvmap 5 word)
  (M3 : word -> option byte)
  (K3 : forall x : nat, In x KS2 -> getr R3 (reg x) = getr R2 (reg x))
  (F3 : BGU.u8_at M3 o (assign_flags fbR fb'))
  (GR3 : mem_grows M2 M3)
  (MF3z : forall a : Z, 0 <= a < 2 ^ 64 -> a <> o -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a))
  (SRClo : 4096 <= (L5.bo_data o' (L5.BO (fb') (len') (sto'))))
  (SRChi : (L5.bo_data o' (L5.BO (fb') (len') (sto'))) + 8 * Z.of_nat len' <= 2 ^ 47)
  (APART : (L5.bo_data o (L5.BO (fbR) (len') (stR))) + 8 * Z.of_nat len' <= (L5.bo_data o' (L5.BO (fb') (len') (sto'))) \/ (L5.bo_data o' (L5.BO (fb') (len') (sto'))) + 8 * Z.of_nat len' <= (L5.bo_data o (L5.BO (fbR) (len') (stR))))
  (R4 : bvmap 5 word)
  (K4 : forall i : nat, In i L5K.CS -> getr R4 (reg i) = getr R3 (reg i))
  (GR4 : mem_grows M3 (wbytes M3 (Z_to_bv 64 (L5.bo_data o (L5.BO (fbR) (len') (stR)))) (L5K.limb_bytes ws')))
  (M4b : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (L5.bo_data o (L5.BO (fbR) (len') (stR))) <= a < (L5.bo_data o (L5.BO (fbR) (len') (stR))) + 8 * Z.of_nat len' -> (wbytes M3 (Z_to_bv 64 (L5.bo_data o (L5.BO (fbR) (len') (stR)))) (L5K.limb_bytes ws')) (Z_to_bv 64 a) = M3 (Z_to_bv 64 a))
  (M4out : forall (a : Z) (k : nat), 0 <= a < 2 ^ 64 -> a + Z.of_nat k <= 2 ^ 64 -> a + Z.of_nat k <= (L5.bo_data o (L5.BO (fbR) (len') (stR))) \/ (L5.bo_data o (L5.BO (fbR) (len') (stR))) + 8 * Z.of_nat len' <= a -> rdn RSEGS (wbytes M3 (Z_to_bv 64 (L5.bo_data o (L5.BO (fbR) (len') (stR)))) (L5K.limb_bytes ws')) (Z_to_bv 64 a) k = rdn RSEGS M3 (Z_to_bv 64 a) k)
  (LIMBS4 : L5.limbs_at RSEGS (wbytes M3 (Z_to_bv 64 (L5.bo_data o (L5.BO (fbR) (len') (stR)))) (L5K.limb_bytes ws')) (L5.bo_data o (L5.BO (fbR) (len') (stR))) ws')
  (DSTW : o + 16 <= (L5.bo_data o (L5.BO (fbR) (len') (stR))) /\ (L5.bo_data o (L5.BO (fbR) (len') (stR))) + 8 * Z.of_nat len' <= o + 32 \/ (L5.bo_data o (L5.BO (fbR) (len') (stR))) + 8 * Z.of_nat len' <= hl_ceil L)
  (fx5 : FPState)
  (R5 : bvmap 5 word)
  (M5 : word -> option byte)
  (K5 : forall x : nat, In x KSZ -> getr R5 (reg x) = getr R4 (reg x))
  (R5_2 : getr R5 (reg 2) = Z_to_bv 64 sp)
  (R5_8 : getr R5 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))))
  (R5_9 : getr R5 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9))))
  (R5_18 : getr R5 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R (reg 18))))
  (R5_19 : getr R5 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R (reg 19))))
  (R5_10 : getr R5 (reg 10) = Z_to_bv 64 o)
  (MM5 : forall a : word, M5 a = (wbytes M3 (Z_to_bv 64 (L5.bo_data o (L5.BO (fbR) (len') (stR)))) (L5K.limb_bytes ws')) a)
  (GR5 : mem_grows (wbytes M3 (Z_to_bv 64 (L5.bo_data o (L5.BO (fbR) (len') (stR)))) (L5K.limb_bytes ws')) M5)
  : srealizes RSEGS SCFG (mkCfg (st fx5 R5 r M5) (model2)) K.

Proof.
  set (od := L5.bo_dyn (L5.BO fb' len' sto')) in *. set (src := L5.bo_data o' (L5.BO fb' len' sto')) in *.
  set (dst := L5.bo_data o (L5.BO fbR len' stR)) in *.
  set (td := match stR with L5.BDyn _ _ => true | L5.BInl _ _ => false end) in *.
  set (M4 := wbytes M3 (Z_to_bv 64 dst) (L5K.limb_bytes ws')) in *.
  (* [comment removed for export] *)
  assert (RP5: regs_preserved R R5).
  { apply (REGS R5 [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat).
    { intros x Hx. assert (HxC: In x L5K.CS) by (pose proof Hx as H'; L5K.inlist H'). assert (Hx2: In x KS2) by (pose proof Hx as H'; L5K.inlist H').
      assert (Hx3: In x KSZ) by (pose proof Hx as H'; L5K.inlist H').
      rewrite (K5 x Hx3). rewrite (K4 x HxC). apply K3. exact Hx2. }
    intros x Hx; exact Hx. exact R5_2. exact R5_8. exact R5_9. exact R5_18. exact R5_19. }
  assert (FBn: assign_fb fb fb' len' grown = assign_flags fbR fb'). { rewrite EfbR. apply assign_fb_eq. lia. }
  (* [comment removed for export] *)
  assert (HC5: forall a v, o <= a -> a + 8 <= o + 32 -> (a + 8 <= o + 16 \/ dst + 8 * Z.of_nat len' <= a \/ dst + 8 * Z.of_nat len' <= hl_ceil L) -> o + 1 <= a ->
               BGU.u64_at M2 a v -> BGU.u64_at M5 a v).
  { intros a v H1a H2a H3a H4a Hu. eapply (BGU.u64_at_frame M4 M5). lia. lia. intros j Hj. apply MM5.
    unfold BGU.u64_at. rewrite M4out; [|lia|lia|destruct DSTW; lia]. eapply (BGU.u64_at_frame M2 M3). lia. lia. intros j Hj. apply MF3z; lia. exact Hu. }
  assert (F5: BGU.u8_at M5 o (assign_fb fb fb' len' grown)).
  { rewrite FBn. eapply (BGU.u8_at_frame M4 M5). apply MM5. unfold BGU.u8_at. rewrite M4out; [exact F3|lia|lia|destruct DSTW; lia]. }
  assert (Q85: BGU.u64_at M5 (o + 8) (Z.of_nat len')). { apply HC5; try lia; first [exact Q8 | (left; lia)]. }
  assert (KEEP5: forall a, L5C.kept L LB sp (48 + (64 + (48 + (64 + (16 + 8224))))) ((o, 32) :: match g with Same => [(L5.bo_data o (L5.BO fb len sto), 8 * Z.max (Z.of_nat len') (Z.of_nat len))] | Grown _ _ => [] end) a ->
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
  assert (SDEF5: L5.defined M5 (sp - (48 + (64 + (48 + (64 + (16 + 8224)))))) (48 + (64 + (48 + (64 + (16 + 8224)))))).
  { apply SDEF_of. intros a Ha. right. rewrite (MM5 (Z_to_bv 64 a)). rewrite M4b by (destruct DSTW; lia). apply MF3z; lia.
    eapply mem_grows_trans. exact GR3. eapply mem_grows_trans. exact GR4. exact GR5. }
  assert (CD5: forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp (48 + (64 + (48 + (64 + (16 + 8224))))) a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M5 (Z_to_bv 64 a) <> None).
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
           assert (L1: BGU.u64_at M5 (o + 16) (nth 0 ws' 0)).
           { eapply (BGU.u64_at_frame M4 M5). lia. lia. intros j Hj. apply MM5. pose proof (LIMBS4 0%nat ltac:(rewrite Lws'; lia)) as X. rewrite Z.mul_0_r, Z.add_0_r in X. exact X. }
           exists (L5.BInl (nth 0 ws' 0) (if Nat.leb 2 len' then nth 1 ws' 0 else u1)).
           split.
           + unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact F5. split. { rewrite FBn. apply assign_flags_range; lia. }
             split. exact Q85. split. { rewrite FBn. unfold assign_flags. rewrite Z.lor_spec, !Z.land_spec. rewrite BtR. cbn. rewrite Bool.andb_false_r. reflexivity. }
             split. exact L1.
             split. { destruct (Nat.leb_spec 2 len').
                      - eapply (BGU.u64_at_frame M4 M5). lia. lia. intros j Hj. apply MM5. pose proof (LIMBS4 1%nat ltac:(rewrite Lws'; lia)) as X.
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

End L5ASGT2U.
