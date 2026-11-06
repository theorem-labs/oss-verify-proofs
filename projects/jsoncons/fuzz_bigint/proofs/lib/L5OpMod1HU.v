(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore AsanAcct
     Ub0_code_201fc_21084 Ub0_code_221b0_23098 BigBranchUb0 BigLinkBase BigLinkGlue BigLinkGlueUb0 BigLinkDivBaseU L5Defs L5Kn L5Core L5CoreSpecsU L5CoreKitU L5Words L5Hp
     L5CmpU L5DivSpecsU L5DivPartsU L5DivNPU L5DivOPU L5OpModPU L5DivTailU L5DivEarlyU L5DivO1HalfU L5OpMod1SU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigFactsBase.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5OPMOD1HU.
Import L5CSU. Import L5DSU. Import L5DIVPU. Import L5DIVNPU. Import L5DIVOPU. Import L5OPMODPU. Import L5OM1SU.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Local Notation preserved_sregs := L5DIVEARLYU.preserved_sregs.
Local Notation u64_at_agree1 := L5DIVEARLYU.u64_at_agree1.
Local Notation u8_at_agree1 := L5DIVEARLYU.u8_at_agree1.
Local Notation big_at_agree1 := L5DIVEARLYU.big_at_agree1.
Local Notation defined_agree1 := L5DIVEARLYU.defined_agree1.
Local Notation model_ok_but_vm := L5DIVEARLYU.model_ok_but_vm.
Local Notation mem_eq := L5DIVEARLYU.mem_eq.
Local Notation mod16_mod8 := L5DIVEARLYU.mod16_mod8.
Local Notation div_saves_kept := L5DIVEARLYU.div_saves_kept.
Local Notation outside1 := L5DIVEARLYU.outside1.
Local Notation outside2 := L5DIVEARLYU.outside2.
Local Notation obj_limbs_agree1 := L5DIVEARLYU.obj_limbs_agree1.
Local Notation outside3 := L5DIVEARLYU.outside3.

Definition cs_all : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma preserved_by_index (R R' : bvmap 5 word) : (forall i, In i cs_all -> getr R' (reg i) = getr R (reg i)) -> regs_preserved R R'.
Proof.
  intros KR x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply KR.
  unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
Qed.
(* [comment removed for export] *)
Lemma defined_byte M a : L5.defined M a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 -> exists b, 0 <= b < 256 /\ L5.u8_at RSEGS M a b.
Proof.
  intros D Ha H1. unfold L5.u8_at. cbn [rdn].
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:E.
  2:{ exfalso. apply (D 0). lia. rewrite Z.add_0_r. exact E. }
  exists (bv_unsigned b). split. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
  cbn. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* [comment removed for export] *)
Lemma segs_below : segs_below_b RSEGS 0x92000 = true. Proof. vm_compute. reflexivity. Qed.
Lemma writable_defined_hi M a n : L5.writable RSEGS M a n -> L5KU.IMG_HI <= a -> 0 <= n -> a + n <= 2 ^ 64 -> L5.defined M a n.
Proof.
  intros W Hlo Hn Hhi i Hi. specialize (W i 1%nat ltac:(lia) ltac:(cbn; lia)). cbn [store_ok] in W.
  unfold wview in W. destruct (M (Z_to_bv 64 (a + i))) eqn:E. congruence.
  unfold L5KU.IMG_HI in Hlo. rewrite BG.unsigned_lit in W by lia. rewrite (find_segment1_none_above RSEGS 0x92000 (a + i) segs_below) in W by lia. discriminate W.
Qed.
Lemma top_frame_kept M M' S R0 : (forall i, S - 32 <= i < S -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= S - 32 -> S <= 2 ^ 64 ->
  top_frame M S R0 -> top_frame M' S R0.
Proof. intros HA Hlo Hhi (A & B & C & D). repeat split; (eapply u64_at_agree1; [intros i Hi; apply HA; lia | lia | lia | eassumption]). Qed.

Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac kreg K i H := etransitivity; [exact (K i ltac:(inl)) | exact H].
Local Ltac uSCR := unfold SCR_OPMOD, DIV_SCR, ASSIGN_SCR, COPY_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.
Local Ltac prune_impl :=
  repeat match goal with
         | H : ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
         | H : _ <-> _ |- _ => clear H
         | H : forall _, _ |- _ => lazymatch type of H with _ -> False => fail | _ => clear H end
         end.
Local Ltac prune_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac prune_mod := repeat match goal with H : _ mod _ = _ |- _ => clear H end.
Local Ltac flia := prune_impl; prune_disj; prune_mod; lia.
Local Ltac fsclia := prune_impl; prune_disj; prune_mod; uSCR; lia.
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].

Lemma al8 a k : a mod 16 = 0 -> (a + 8 * k) mod 8 = 0.
Proof. intros H. replace (a + 8 * k) with (a + k * 8) by lia. rewrite Z_mod_plus_full. apply L5DIVEARLYU.mod16_mod8. exact H. Qed.
Lemma hpres_wmono L LB sp scr W W' M M' : (forall a, L5.outside W' a -> L5.outside W a) -> L5C.hpres L LB sp scr W M M' -> L5C.hpres L LB sp scr W' M M'.
Proof.
  intros HW (P & D & C). split. { intros a (Ha & CA & NE & OW). apply P. split. exact Ha. split. exact CA. split. exact NE. apply HW. exact OW. }
  split. exact D. exact C.
Qed.
Lemma lb_remove_head A n LBx : lb_remove A ((A, n) :: LBx) = LBx.
Proof. cbn. rewrite Z.eqb_refl. reflexivity. Qed.
(* [comment removed for export] *)
Definition VP (E X fq qp qc u1 u8 : Z) (j : nat) : Z :=
  match j with 2%nat => E | 33%nat => X | 36%nat => fq | 37%nat => qp | 38%nat => qc | 43%nat => u1 | 44%nat => u8 | _ => 0 end.
(* [comment removed for export] *)
Definition VF (S r x u1 u8 : Z) (j : nat) : Z :=
  match j with 2%nat => S | 33%nat => r | 34%nat => x | 43%nat => u1 | 44%nat => u8 | _ => 0 end.
(* [comment removed for export] *)
Definition VO (Q X bo fbx c fnum fden nd pd d : Z) (j : nat) : Z :=
  match j with
  | 2%nat => Q | 33%nat => X | 34%nat => bo | 35%nat => Q | 36%nat => X | 37%nat => 1 | 38%nat => fbx
  | 41%nat => fden | 42%nat => nd | 43%nat => pd | 44%nat => fnum | 47%nat => c | 63%nat => d
  | _ => 0
  end.
Lemma SCR_OPMOD_val : SCR_OPMOD = 10240. Proof. reflexivity. Qed.
Lemma DIV_SCR_val : DIV_SCR = 8976. Proof. reflexivity. Qed.
Lemma OPDEL_SCR_val : OPDEL_SCR = 8224. Proof. reflexivity. Qed.
Lemma COPY_SCR_val : COPY_SCR = 8304. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Section WithHeap.
Variables (L : heap_layout) (HI : heap_iface).
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis KPOS : 0 <= hl_k_per_malloc L.
Hypothesis BPOS : 0 <= hl_b_overhead L.
Hypothesis COPYA : copya_spec L HI.
Hypothesis COPYC : copy_spec L HI.
Hypothesis ASSIGN : assign_spec L HI.
Hypothesis RESIZE : resize_spec L HI.
Hypothesis OPDEL : opdel_sized_spec L HI.
Hypothesis CMP : L5CMPU.cmp_spec.

Let IMG := L5DIVEARLYU.IMG L LY.
Let IMGLO := L5DIVEARLYU.IMGLO L LY.
Let ERRNOV := L5DIVEARLYU.ERRNOV L LY.
Let LBdef := @L5DIVEARLYU.LBdef _ L HI HIok.
Let kept_above := L5DIVEARLYU.kept_above L LY.
Let kept_inblock := @L5DIVEARLYU.kept_inblock _ L HI LY HIok.
Let cdef_above := L5DIVEARLYU.cdef_above L LY.
Let cdef_below := L5DIVEARLYU.cdef_below L LY.
Let hi_heap_stackwrite := @L5DIVEARLYU.hi_heap_stackwrite _ L HI LY HIok.
Let early_path := @L5DIVEARLYU.early_path _ L HI LY HIok ASSIGN.
Let half_path := @L5DIVO1HU.half_path _ L HI LY HIok RESIZE ASSIGN.
Let divtail2 := @L5DIVTAILU.divtail2_ok _ L HI LY HIok OPDEL.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet)
          (LB : list (Z * Z)) (cr : credit) (S fbx fco bo : Z) (bb : L5.bigobj) (wb : list Z).
Let capb : Z := L5.bo_cap bb.
Let X : Z := S + 64.
Let Q : Z := S - 64.
Let spd : Z := S - 416.
Hypothesis HH0 : hi_heap HI LB cr M0 (m_vmmaps model0).
Hypothesis MOK0 : model_ok model0.
Hypothesis HK0 : K [].
Hypothesis G10 : getr R0 10%bv = Z_to_bv 64 (S + 96).
Hypothesis G11 : getr R0 11%bv = Z_to_bv 64 (S + 64).
Hypothesis G12 : getr R0 12%bv = Z_to_bv 64 bo.
Hypothesis BO : bo = S + 128.
Hypothesis G1 : getr R0 1%bv = Z_to_bv 64 OPMOD1_RET.
Hypothesis G2 : getr R0 2%bv = Z_to_bv 64 S.
Hypothesis G3 : getr R0 3%bv = Z_to_bv 64 GP.
Hypothesis G4 : getr R0 4%bv = Z_to_bv 64 TP.
Hypothesis STK : L5C.stk (hl_sptop L) M0 S SCR_OPMOD.
Hypothesis HS : S + 240 <= hl_sptop L.
Hypothesis WX : L5.writable RSEGS M0 (S + 64) 64.
Hypothesis IMGC : L5.img_clear M0 0x10000 0x20000.
Hypothesis XA : x_is_a M0 (S + 64) fbx.
Hypothesis FCO : L5.u8_at RSEGS M0 (S + 96) fco.
Hypothesis FCOR : 0 <= fco < 256.
Hypothesis BOK : b_ok LB M0 bo bb wb.
Hypothesis CAPB : L5.bo_cap bb <= 268.
Hypothesis DYN3 : L5.bo_dyn bb = true -> (3 <= L5.bo_len bb)%nat.
Hypothesis CR : credit_for L cr OPMOD1_K (opmod1_bytes capb).
(* [comment removed for export] *)
Hypothesis KN : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
    opmod1_post L LB cr M0 M' R0 R' S bo fco bb wb capb LB' cr' ->
    model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
    srealizes RSEGS SCFG (cfg R' OPMOD1_RET M' model') K.
(* [comment removed for export] *)
Hypothesis KZ : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
    zero_throw_at L LB R0 M0 R' M' S -> model_but_vm model0 model' -> hi_heap HI LB cr M' (m_vmmaps model') ->
    L5.defined M' (S - SCR_OPMOD) SCR_OPMOD -> L5.big_at RSEGS M' bo bb -> L5C.obj_limbs RSEGS M' bb wb -> x_is_a M' (S + 64) fbx ->
    srealizes RSEGS SCFG (cfg R' ZERO_THROW M' model') K.
(* [comment removed for export] *)
Hypothesis KG : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (fnum fden b0 b1 : Z),
    o1_gen_entry L HI LB cr S R0 M0 model0 fbx bo bb wb R' M' model' fnum fden b0 b1 ->
    srealizes RSEGS SCFG (cfg R' GEN M' model') K.

(* [comment removed for export] *)
Lemma SPW : S mod 16 = 0 /\ 0x7fff7f800000 + 10240 <= S /\ S + 240 <= 2 ^ 47 /\ hl_sptop L - 8388608 + 10240 <= S /\ S + 240 <= hl_sptop L
            /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Proof using L M0 S fco bb STK HS FCOR DYN3. pose proof STK as (A & B & C & D & _). uSCR. repeat split; try lia. Qed.
Lemma SCR0 : L5.defined M0 (S - 10240) 10240. Proof. pose proof STK as (_ & _ & _ & _ & W). exact W. Qed.
Lemma UR01 : U R0 1 = OPMOD1_RET.
Proof using R0 S fco bb G1 FCOR DYN3. unfold U. replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G1. apply BG.unsigned_lit. unfold OPMOD1_RET. lia. Qed.
Lemma CAPB1 : 1 <= capb <= 268.
Proof using M0 LB S fco bo bb wb FCOR BOK CAPB DYN3. pose proof CAPB as C. pose proof BOK as (OB & _). unfold capb, L5.bo_cap in C |- *. unfold L5.big_at in OB.
  destruct (L5.bo_st bb) as [v0 v1|c q]. lia. destruct OB as (_ & _ & _ & _ & _ & _ & _ & Hc & _). lia. Qed.
Lemma WX32 : L5.writable RSEGS M0 (S + 64) 32. Proof using M0 S fco bb WX FCOR DYN3. eapply L5.writable_sub. exact WX. lia. lia. Qed.
Lemma WC32 : L5.writable RSEGS M0 (S + 96) 32. Proof using M0 S fco bb WX FCOR DYN3. eapply L5.writable_sub. exact WX. lia. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_FIN (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit) (bx : L5.bigobj) (wx : list Z) :
  let LB1 := blocks_ofst (L5.bo_st bx) ++ LB in
  getr R (reg 2) = Z_to_bv 64 (S - 16) -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 (S + 96) -> getr R (reg 10) = Z_to_bv 64 X ->
  (forall i, In i [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg i) = getr R0 (reg i)) ->
  model_but_vm model0 model -> hi_heap HI LB1 crc M (m_vmmaps model) ->
  credit_after L cr OPMOD1_K (opmod1_bytes capb) (if L5.bo_dyn bx then debit L crc 64 else crc) ->
  (L5.bo_dyn bx = true -> credit_ok L crc 64) ->
  (forall cap q, L5.bo_st bx = L5.BDyn cap q -> cap = 8 /\ L5C.fresh_block L LB M q 64) ->
  L5.defined M (S - SCR_OPMOD) SCR_OPMOD ->
  L5.u64_at RSEGS M (S - 8) (U R0 1) -> L5.u64_at RSEGS M (S - 16) (U R0 8) ->
  L5.big_at RSEGS M X bx -> L5C.obj_limbs RSEGS M bx wx -> L5.bo_neg bx = false ->
  L5.big_at RSEGS M bo bb -> L5C.obj_limbs RSEGS M bb wb -> (1 <= L5.bo_len bb)%nat ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R OPF_BACK M model) K.
Proof.
  cbv zeta. intros H2 H3 H4 H8 H10 HRS MBV HH CRA CROK XDYN SCR T1 T8 OBX OLX NEGX OBB OLB LENB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof ERRNOV as EV. pose proof IMG as IMG'. pose proof IMGLO as IMGLO'. rewrite SCR_OPMOD_val in SCR. pose proof UR01 as UR01'.
  pose proof OBX as OBX'. unfold L5.big_at in OBX'. destruct OBX' as (Xf & Xfr & Xl & XST).
  pose proof BOK as (OB0 & _ & _ & BST).
  assert (CEIL: hl_ceil L <= S - SCR_OPMOD). { unfold hl_ceil. rewrite SCR_OPMOD_val. clear - SLO'. lia. }
  assert (LBceil: forall b, In b LB -> fst b + snd b <= hl_ceil L).
  { intros [A n] Hb. pose proof (LBdef _ _ _ _ HH0 A n Hb) as (_ & _ & Ahi & _). unfold hl_ceil. cbn. exact Ahi. }
  (* [comment removed for export] *)
  assert (KA0: forall a, S <= a < 2 ^ 64 -> ~ (X <= a < X + 32) -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
  { intros a Ha NX. apply (kept_above M0 M LB S SCR_OPMOD _ a HP). fsclia. rewrite SCR_OPMOD_val; clear; lia. flia. exact Ha. apply outside1. exact NX. }
  assert (FCO1: L5.u8_at RSEGS M (S + 96) fco). { eapply u8_at_agree1. 4: exact FCO. intros i Hi; apply KA0; unfold X; flia. flia. flia. }
  (* [comment removed for export] *)
  assert (INX: forall cap q, L5.bo_st bx = L5.BDyn cap q -> In (q, 8 * cap) (blocks_ofst (L5.bo_st bx) ++ LB)).
  { intros cap q E. rewrite E. cbn. left. reflexivity. }
  assert (SUBLB: forall b, In b LB -> In b (blocks_ofst (L5.bo_st bx) ++ LB)). { intros b Hb. apply in_app_iff. right. exact Hb. }
  (* [comment removed for export] *)
  assert (WF16: L5.writable RSEGS M (S - 16) 16). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR. clear; lia. clear; lia. flia. flia. }
  pose proof (dofu2_conc fx R M (VF S (S + 96) X 0 0)) as P. cbn [VF] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(unfold X; flia) H2 H8 H10 ltac:(flia) A16 WF16 ltac:(flia)) as (fx1 & R1 & M1 & _ & FR1 & _ & (MS1 & K1 & A1 & A10 & A11)). clear P.
  pose proof (mem_eq M M1 FR1) as EM1. subst M1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  eapply (COPYC fx1 R1 M model K (blocks_ofst (L5.bo_st bx) ++ LB) crc (S + 96) X (S - 16) COPY_BACK fco bx wx HH MOK HK0 A10 A11).
  - intros DY. pose proof (CROK DY) as CK. unfold L5.bo_cap. unfold L5.bo_dyn in DY. destruct (L5.bo_st bx) as [v0 v1|cap q] eqn:E. { destruct XST as (T & _). rewrite T in DY. discriminate DY. }
    destruct (XDYN cap q eq_refl) as [-> _]. split. clear; lia. exact CK.
  - exact A1.
  - unfold COPY_BACK. split. clear; lia. reflexivity.
  - kreg K1 2%nat H2.
  - kreg K1 4%nat H4.
  - split. { replace (S - 16) with (S + (-1) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. fsclia. split. flia. split. exact SPT. rewrite COPY_SCR_val. eapply L5.defined_sub. exact SCR. clear; lia. clear; lia.
  - exact FCO1. - exact FCOR.
  - rewrite <- Zplus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - clear; lia. - flia.
  - apply (L5C.writable_of_defined RSEGS). eapply (cdef_above M0 M LB S SCR_OPMOD _ (S + 96) 32 HP). fsclia. rewrite SCR_OPMOD_val; clear; lia. flia. clear; lia. flia.
    apply (writable_defined_hi M0 (S + 96) 32 WC32). unfold L5KU.IMG_HI; flia. clear; lia. flia. flia. flia.
  - exact OBX. - exact OLX.
  - unfold X. rewrite <- Zplus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold X; clear; lia. - unfold X; flia.
  - exact INX.
  - right. unfold X; clear; lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & _). destruct POST as (RP2 & GP).
    (* [comment removed for export] *)
    assert (KA2: (forall a, S - 16 <= a < 2 ^ 64 -> ~ (S + 96 <= a < S + 96 + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
                 /\ (forall A n a, In (A, n) (blocks_ofst (L5.bo_st bx) ++ LB) -> A <= a < A + n -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
                 /\ L5.defined M2 (S - 16) 16
                 /\ L5C.hpres L LB S SCR_OPMOD [(X, 32); (S + 96, 32)] M0 M2).
    { assert (HPW: L5C.hpres L LB S SCR_OPMOD [(X, 32); (S + 96, 32)] M0 M).
      { eapply hpres_wmono. 2: exact HP. intros a OW r Hr. apply OW. cbn in Hr |- *. clear - Hr. tauto. }
      destruct g as [|A cap].
      - destruct GP as (_ & _ & _ & _ & FB2 & MG2).
        assert (K2: forall a, 0 <= a < 2 ^ 64 -> ~ (S + 96 <= a < S + 96 + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
        { intros a Ha Hn. apply FB2. apply outside1. rewrite BG.unsigned_lit by exact Ha. exact Hn. }
        split. { intros a Ha Hn. apply K2. flia. exact Hn. }
        split. { intros A n a Hin Ha. pose proof (LBdef _ _ _ _ HH A n Hin) as (_ & (Alo & _) & Ahi & _). apply K2. clear - Ha Alo Ahi SPT SLO'; unfold hl_ceil in *; lia. clear - Ha Ahi SLO'; unfold hl_ceil in *; lia. }
        split. { eapply L5.defined_grows. exact MG2. eapply L5.defined_sub. exact SCR. clear; lia. clear; lia. }
        eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [(X, 32); (S + 96, 32)] M0 M M2 S SCR_OPMOD [(X, 32); (S + 96, 32)]). exact HPW.
        + eapply (L5HP.hpres_piece L LB S SCR_OPMOD _ M M2 (fun a => S + 96 <= a < S + 96 + 32)). exact K2.
          { intros a KA C. apply (L5HP.outside_in _ _ (S + 96) 32 (L5HP.kept_outside_W _ _ _ _ _ _ KA)). cbn. right; left; reflexivity. exact C. }
          rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG2. exact SCR. exact MG2.
        + intros a KA; exact KA. + intros b Hb; exact Hb. + exact CEIL. + flia. + rewrite SCR_OPMOD_val; clear; lia. + rewrite EV; clear; lia. + flia.
      - destruct GP as (_ & _ & _ & _ & _ & _ & _ & HP2).
        split. { intros a Ha Hn. apply (kept_above M M2 _ (S - 16) COPY_SCR _ a HP2). fsclia. rewrite COPY_SCR_val; clear; lia. flia. exact Ha. apply outside1. exact Hn. }
        split. { intros A' n a Hin Ha. pose proof (LBdef _ _ _ _ HH A' n Hin) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG', IMGLO' in Aimg.
                 apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). eapply L5C.kept_block. exact Hin. exact Ha. clear - Alo; lia. clear - Ahi SPT; lia.
                 rewrite EV; clear - Aimg Ha; lia. apply outside1. clear - Ha Ahi SLO'; unfold hl_ceil in *; lia. }
        split. { eapply (cdef_above M M2 _ (S - 16) COPY_SCR _ (S - 16) 16 HP2). fsclia. rewrite COPY_SCR_val; clear; lia. flia. clear; lia. flia.
                 eapply L5.defined_sub. exact SCR. clear; lia. clear; lia. }
        eapply (L5HP.hpres_trans L LB _ S SCR_OPMOD [(X, 32); (S + 96, 32)] M0 M M2 (S - 16) COPY_SCR [(S + 96, 32)]). exact HPW. exact HP2.
        + intros a KA. eapply L5HP.kept_mono. exact KA. exact SUBLB. fsclia. clear; lia.
          intros OW r [<-|[]]. apply OW. cbn. right; left; reflexivity.
        + exact SUBLB. + exact CEIL. + flia. + rewrite SCR_OPMOD_val; clear; lia. + rewrite EV; clear; lia. + flia. }
    destruct KA2 as (KA2 & KB2 & D16 & HPF).
    (* [comment removed for export] *)
    assert (WF16': L5.writable RSEGS M2 (S - 16) 16). { apply (L5C.writable_of_defined RSEGS). exact D16. flia. flia. }
    pose proof (dofu3_conc fx2 R2 M2 (VF S 0 0 (U R0 1) (U R0 8))) as P. cbn [VF] in P.
    destruct (P ltac:(flia) ltac:(unfold U; apply BL.bvu_range) ltac:(unfold U; apply BL.bvu_range)
                ltac:(rewrite (preserved_sregs R1 R2 2 RP2) by inl; kreg K1 2%nat H2) ltac:(flia) A16 WF16'
                ltac:(eapply u64_at_agree1; [intros i Hi; apply KA2; flia | flia | flia | exact T1])
                ltac:(eapply u64_at_agree1; [intros i Hi; apply KA2; flia | flia | flia | exact T8]))
      as (fx3 & R3 & M3 & _ & FR3 & _ & (MS3 & K3 & B1 & B2 & B8)). clear P.
    pose proof (mem_eq M2 M3 FR3) as EM3. subst M3. rewrite UR01' in B1.
    eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2.
    { eapply msteps_trans. exact MS3. apply (BDU.ret_to fx3 R3 M2 OPF_RETI W_20d2c OPMOD1_RET F_20d2c eq_refl D_20d2c B1). unfold OPMOD1_RET; clear; lia. reflexivity. }
    apply (KN fx3 R3 M2 model2 LB2 cr2).
    + split.
      { apply preserved_by_index. intros i Hi. cbn in Hi.
        destruct Hi as [<-|Hi]. { rewrite B2. symmetry. exact G2. }
        destruct Hi as [<-|Hi]. { rewrite (K3 3%nat) by inl. rewrite (preserved_sregs R1 R2 3 RP2) by inl. rewrite (K1 3%nat) by inl. rewrite H3. symmetry. exact G3. }
        destruct Hi as [<-|Hi]. { rewrite (K3 4%nat) by inl. rewrite (preserved_sregs R1 R2 4 RP2) by inl. rewrite (K1 4%nat) by inl. rewrite H4. symmetry. exact G4. }
        destruct Hi as [<-|Hi]. { rewrite B8. unfold U. apply Z_to_bv_bv_unsigned. }
        repeat (destruct Hi as [<-|Hi]; [ rewrite K3 by inl; rewrite (preserved_sregs R1 R2 _ RP2) by inl; rewrite K1 by inl; apply HRS; inl |]). destruct Hi. }
      split.
      { exists bx, wx, (blocks_ofst (L5.bo_st bx) ++ LB).
        assert (OBX2: L5.big_at RSEGS M2 X bx). { eapply big_at_agree1. 4: exact OBX. intros i Hi; apply KA2; unfold X in *; flia. unfold X; flia. unfold X; flia. }
        assert (OLX2: L5C.obj_limbs RSEGS M2 bx wx).
        { eapply obj_limbs_agree1. 3: exact OLX.
          - intros cap q E i Hi. apply (KB2 q (8 * cap) i). apply INX. exact E. pose proof OLX as (Ln & _). rewrite Ln in Hi.
            rewrite E in XST. destruct XST as (_ & _ & _ & Hlc & _). clear - Hi Hlc; lia.
          - intros cap q E. pose proof OLX as (Ln & _). rewrite Ln. rewrite E in XST. destruct XST as (_ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). clear - Hlc Hcap Qlo Qhi; lia. }
        split. exact OBX2. split. exact OLX2. split. exact NEGX.
        split. { destruct (L5.bo_st bx) as [v0 v1|cap q] eqn:E. reflexivity. destruct (XDYN cap q eq_refl) as [-> (BR & BA & BD)].
                 split. reflexivity. split. reflexivity. split. exact BR. split. exact BA.
                 exact (proj1 (LBdef _ _ _ _ HH2 q 64 ltac:(destruct g as [|A' cap']; [destruct GP as (_ & -> & _) | destruct GP as (_ & _ & -> & _)]; [|right]; (rewrite E || idtac); cbn; left; reflexivity))). }
        (* [comment removed for export] *)
        destruct g as [|A cap].
        - destruct GP as (DYF & -> & -> & OC2 & FB2 & _).
          exists (L5.BO (copy_fb fco (L5.bo_fb bx) false) (L5.bo_len bx) (L5.bo_st bx)).
          split. exact OC2. split. { pose proof OLX2 as (Ln & Fw & LA). split. exact Ln. split. exact Fw. cbn [L5.bo_st L5.bo_len]. exact LA. }
          split. reflexivity. split. { cbn [L5.bo_fb]. rewrite DYF. reflexivity. }
          cbn [L5.bo_st]. unfold L5.bo_dyn in DYF. destruct (L5.bo_st bx) as [v0 v1|cap q] eqn:E. repeat split; reflexivity.
          exfalso. try rewrite E in XST. destruct XST as (T & _). rewrite T in DYF. discriminate DYF.
        - destruct GP as (DYT & Hcap & -> & -> & FBc & OC2 & OLc & _).
          exists (L5.BO (copy_fb fco (L5.bo_fb bx) true) (L5.bo_len bx) (L5.BDyn cap A)).
          split. exact OC2. split. exact OLc. split. reflexivity. split. { cbn [L5.bo_fb]. rewrite DYT. reflexivity. }
          cbn [L5.bo_st]. unfold L5.bo_dyn in DYT. unfold L5.bo_cap in Hcap. destruct (L5.bo_st bx) as [v0 v1|cap' q] eqn:E.
          { exfalso. try rewrite E in XST. destruct XST as (T & _). rewrite T in DYT. discriminate DYT. }
          subst cap. split. reflexivity. split. reflexivity. exact FBc. }
      split. { eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KA2; generalize BO; flia. generalize BO; flia. generalize BO; flia. }
      split. { eapply obj_limbs_agree1. 3: exact OLB.
               - intros cap q E i Hi. rewrite E in BST. destruct BST as [INB _]. pose proof OLB as (Ln & _ & _).
                 unfold L5.big_at in OB0. rewrite E in OB0. destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & _).
                 apply (KB2 q (8 * cap) i). apply SUBLB. exact INB. rewrite Ln in Hi. clear - Hi Hlc. lia.
               - intros cap q E. pose proof OLB as (Ln & _ & _). unfold L5.big_at in OB0. rewrite E in OB0.
                 destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite Ln. clear - Hlc Hcap Qlo Qhi. lia. }
      split. exact LENB.
      split. { destruct g as [|A cap]. { destruct GP as (DYF & _ & -> & _). rewrite DYF in CRA. exact CRA. }
               destruct GP as (DYT & Hcap & _ & -> & _). rewrite DYT in CRA. unfold L5.bo_cap in Hcap. unfold L5.bo_dyn in DYT.
               destruct (L5.bo_st bx) as [v0 v1|cap' q] eqn:E. { exfalso. try rewrite E in XST. destruct XST as (T & _). rewrite T in DYT. discriminate DYT. }
               destruct (XDYN cap' q eq_refl) as [-> _]. subst cap. exact CRA. }
      exact HPF.
    + exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
    + exact HH2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_DT2 (fx : FPState) (R Rd : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit)
      (fq : Z) (bx : L5.bigobj) (wx : list Z) (f2 f3 c3 p3 : Z) :
  let BD := (if Z.testbit f3 0 then [(p3, 8 * c3)] else []) in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  model_but_vm model0 model -> hi_heap HI (BD ++ LB) crc M (m_vmmaps model) -> credit_after L cr OPMOD1_K (opmod1_bytes capb) crc ->
  div_entry_regs S R0 Rd -> div_saves M Q Rd -> top_frame M S R0 ->
  L5.u8_at RSEGS M Q fq -> 0 <= fq < 256 -> Z.testbit fq 0 = false ->
  L5.big_at RSEGS M X bx -> L5C.obj_limbs RSEGS M bx wx -> L5.bo_neg bx = false -> (exists v0 v1, L5.bo_st bx = L5.BInl v0 v1) ->
  local_obj M (Q - 184) f2 0 0 -> Z.testbit f2 0 = false -> local_obj M (Q - 136) f3 c3 p3 ->
  (Z.testbit f3 0 = true -> L5C.fresh_block L LB M p3 (8 * c3)) ->
  L5.big_at RSEGS M bo bb -> L5C.obj_limbs RSEGS M bb wb -> (1 <= L5.bo_len bb)%nat ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R L5DIVTAILU.DT2 M model) K.
Proof.
  intros BD H2 H3 H4 MBV HH CRA DER DS TF Qf Qfr Qb0 OBX OLX NEGX [v0 [v1 STX]] LO2 F2b LO3 FRESH3 OBB OLB LENB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP) as SCR. rewrite SCR_OPMOD_val in SCR. pose proof ERRNOV as EV. pose proof IMG as IMG'.
  pose proof DER as (RD1 & RD8 & RDS). pose proof UR01 as UR01'.
  assert (UD1: U Rd 1 = DIV_RET).
  { unfold U. change (getr Rd (Z_to_bv 5 1)) with (getr Rd (reg 1)). rewrite RD1. apply BG.unsigned_lit. unfold DIV_RET; clear; lia. }
  unfold cfg.
  eapply (divtail2 fx R M model K (BD ++ LB) crc Q Rd f2 0 0 f3 c3 p3 HH MOK HK0).
  - replace (Q - 352) with spd by (unfold Q, spd; clear; lia). exact H2.
  - exact H4.
  - replace (Q - 352) with spd by (unfold Q, spd; clear; lia).
    split. { unfold spd. replace (S - 416) with (S + (-26) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; flia. split. exact SPT. unfold spd. uSCR. eapply L5.defined_sub. exact SCR. clear; lia. clear; lia.
  - unfold Q; flia.
  - eapply L5.defined_sub. exact SCR. unfold Q; clear; lia. unfold Q; clear; lia.
  - exact DS.
  - rewrite UD1. unfold DIV_RET. split. clear; lia. reflexivity.
  - exact LO2.
  - exact LO3.
  - intros T. rewrite F2b in T. discriminate T.
  - intros T. unfold lb_free. rewrite F2b. subst BD. rewrite T. apply in_app_iff. left. left. reflexivity.
  - cbv zeta. intros fx5 R5 M5 model5 T2 T3 T4 TS HP5 MBV5 HH5.
    assert (ELB: lb_free f3 p3 (lb_free f2 0 (BD ++ LB)) = LB).
    { unfold lb_free. rewrite F2b. subst BD. destruct (Z.testbit f3 0). cbn [app]. apply lb_remove_head. reflexivity. }
    rewrite ELB in HP5, HH5. clear ELB.
    pose proof (model_ok_but_vm _ _ MOK MBV5) as MOK5. pose proof MOK5 as (Mh5 & Ml5 & _).
    assert (KA5: forall a, spd <= a < 2 ^ 64 -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. apply (kept_above M M5 LB (Q - 352) OPDEL_SCR _ a HP5). unfold Q; fsclia. uSCR; clear; lia. flia. unfold Q, spd in *; flia. apply L5C.outside_nil. }
    assert (D48: L5.defined M5 (S - 64) 48).
    { eapply (cdef_above M M5 LB (Q - 352) OPDEL_SCR _ (S - 64) 48 HP5). unfold Q; fsclia. uSCR; clear; lia. flia. unfold Q; clear; lia. flia.
      eapply L5.defined_sub. exact SCR. clear; lia. clear; lia. }
    (* [comment removed for export] *)
    assert (SCR5: L5.defined M5 (S - 10240) 10240).
    { replace 10240 with (1600 + (8224 + 416)) at 2 by (clear; lia). apply L5C.defined_app. 3: clear; lia.
      { eapply (cdef_below M M5 LB (Q - 352) OPDEL_SCR _ (S - 10240) 1600 HP5). flia. unfold Q; rewrite OPDEL_SCR_val; clear; lia. uSCR; clear; lia. flia. unfold Q; flia.
        eapply L5.defined_sub. exact SCR. clear; lia. clear; lia. }
      apply L5C.defined_app. 3: clear; lia.
      { pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP5) as D. rewrite OPDEL_SCR_val in D. unfold Q in D. exactA D. }
      eapply (cdef_above M M5 LB (Q - 352) OPDEL_SCR _ _ 416 HP5). unfold Q; fsclia. uSCR; clear; lia. flia. unfold Q; clear; lia. flia.
      eapply L5.defined_sub. exact SCR. clear; lia. clear; lia. }
    pose proof (top_frame_kept M M5 S R0 ltac:(intros i Hi; apply KA5; unfold spd; flia) ltac:(flia) ltac:(flia) TF) as (TF1 & TF8 & TF3 & TF4).
    (* [comment removed for export] *)
    pose proof (dopu2i_conc fx5 R5 M5 (VP (S - 16) X fq 0 0 OPF_BACK (S + 96))) as P. cbn [VP] in P.
    destruct (P ltac:(flia) ltac:(unfold X; flia) ltac:(clear - Qfr; lia) ltac:(unfold OPF_BACK; clear; lia) ltac:(flia)
                ltac:(rewrite T2; unfold Q; f_equal; clear; lia) ltac:(rewrite (TS 8%nat) by inl; exact RD8) ltac:(flia)
                ltac:(replace (S - 16) with (S + (-1) * 16) by (clear; lia); unfold aligned; rewrite Z_mod_plus_full; exact A16)
                ltac:(apply (L5C.writable_of_defined RSEGS); [exactA D48 | flia | flia]) ltac:(exactA TF3) ltac:(exactA TF4)
                ltac:(eapply u8_at_agree1; [intros i Hi; apply KA5; unfold Q, spd in *; flia | unfold Q; flia | unfold Q; flia
                                           | replace (S - 16 - 48) with Q by (unfold Q; clear; lia); exact Qf])
                ltac:(clear - Qfr; lia) Qb0)
      as (fx6 & R6 & M6 & _ & FR6 & _ & (MS6 & K6 & B1 & B2 & B8 & B10)). clear P.
    pose proof (mem_eq M5 M6 FR6) as EM. subst M6.
    rewrite UD1. unfold DIV_RET. eapply (L5.cps_of_msteps RSEGS). exact Mh5. exact Ml5.
    { eapply msteps_trans. exact MS6. apply (BDU.ret_to fx6 R6 M5 0x224c4 W_224c4 OPF_BACK F_224c4 eq_refl D_224c4 B1). unfold OPF_BACK; clear; lia. reflexivity. }
    pose proof OBX as OBX'. unfold L5.big_at in OBX'. rewrite STX in OBX'. destruct OBX' as (Xf & Xfr & Xl & Xb0 & _).
    apply (stage_FIN fx6 R6 M5 model5 crc bx wx).
    + exact B2.
    + rewrite (K6 3%nat) by inl. rewrite T3. exact H3.
    + rewrite (K6 4%nat) by inl. rewrite T4. exact H4.
    + exact B8. + exact B10.
    + intros i Hi. rewrite K6. rewrite TS. apply RDS. exact Hi. revert Hi. apply (L5K.incl_b _ _). vm_compute. reflexivity.
      revert Hi. apply (L5K.incl_b _ KS_dopu2i). vm_compute. reflexivity.
    + exact (L5C.model_but_vm_trans _ _ _ MBV MBV5).
    + rewrite STX. cbn [blocks_ofst app]. exact HH5.
    + unfold L5.bo_dyn. rewrite Xb0. exact CRA.
    + unfold L5.bo_dyn. rewrite Xb0. intros F; discriminate F.
    + intros cap q E. rewrite STX in E. discriminate E.
    + rewrite SCR_OPMOD_val. exact SCR5.
    + exact TF1. + exact TF8.
    + eapply big_at_agree1. 4: exact OBX. intros i Hi; apply KA5; unfold X, spd in *; flia. unfold X; flia. unfold X; flia.
    + eapply obj_limbs_agree1. 3: exact OLX. intros cap q E; rewrite STX in E; discriminate E. intros cap q E; rewrite STX in E; discriminate E.
    + exact NEGX.
    + eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KA5; subst bo; unfold spd; flia. subst bo; flia. subst bo; flia.
    + pose proof BOK as (_ & _ & _ & BST). eapply obj_limbs_agree1. 3: exact OLB.
      * intros cap q E i Hi. rewrite E in BST. destruct BST as [INB _]. pose proof OLB as (Ln & _ & _).
        pose proof BOK as (OB0 & _). unfold L5.big_at in OB0. rewrite E in OB0. destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _).
        pose proof (LBdef _ _ _ _ HH q (8 * cap) ltac:(apply in_app_iff; right; exact INB)) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG, IMGLO in Aimg.
        apply (L5C.hpres_kept _ _ _ _ _ _ _ i HP5). eapply L5C.kept_block. exact INB. rewrite Ln in Hi; clear - Hi Hlc; lia. clear - Alo; lia.
        clear - Ahi SPT; lia. rewrite EV; clear - Aimg Hi Hlc Ln; lia. apply L5C.outside_nil.
      * intros cap q E. pose proof OLB as (Ln & _ & _). pose proof BOK as (OB0 & _). unfold L5.big_at in OB0. rewrite E in OB0.
        destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite Ln. clear - Hlc Hcap Qlo Qhi. lia.
    + exact LENB.
    + eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [(X, 32)] M0 M M5 (Q - 352) OPDEL_SCR []). exact HP. exact HP5.
      * intros a KA. eapply L5HP.kept_mono. exact KA. intros b Hb; exact Hb. unfold Q; fsclia. unfold Q; flia. intros _; apply L5C.outside_nil.
      * intros b Hb; exact Hb. * unfold hl_ceil; fsclia. * flia. * rewrite SCR_OPMOD_val; clear; lia. * rewrite EV; clear; lia. * flia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma A0_rng : 0 <= A0 < 2 ^ 64. Proof. unfold A0. split; [vm_compute; discriminate | vm_compute; reflexivity]. Qed.
Lemma A1_rng : 0 <= A1 < 2 ^ 64. Proof. unfold A1. split; [vm_compute; discriminate | vm_compute; reflexivity]. Qed.
Lemma obj_limbs_x M fb : L5C.obj_limbs RSEGS M (L5.BO fb 2 (L5.BInl A0 A1)) [A0; A1].
Proof using S fco bb FCOR DYN3. split. reflexivity. split. pose proof A0_rng. pose proof A1_rng. repeat constructor; lia. reflexivity. Qed.
Lemma local_of_num M o fnum : L5.big_at RSEGS M o (L5.BO fnum 2 (L5.BInl A0 A1)) -> local_obj M o fnum 0 0 /\ Z.testbit fnum 0 = false.
Proof. intros (U0 & F & _ & T & _). cbn [L5.bo_fb] in *. split. split. exact U0. split. exact F. intros T'. rewrite T in T'. discriminate T'. exact T. Qed.
Lemma local_obj_kept M M' o f c p : (forall i, o <= i < o + 32 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= o -> o + 32 <= 2 ^ 64 ->
  local_obj M o f c p -> local_obj M' o f c p.
Proof using S fco bb FCOR DYN3.
  intros HA Ho Hhi (U0 & F & D). split. { eapply u8_at_agree1. 4: exact U0. intros i Hi; apply HA; lia. lia. lia. } split. exact F.
  intros T. destruct (D T) as (C16 & Hc & C24 & Hp). split. { eapply u64_at_agree1. 4: exact C16. intros i Hi; apply HA; lia. lia. lia. }
  split. exact Hc. split. { eapply u64_at_agree1. 4: exact C24. intros i Hi; apply HA; lia. lia. lia. } exact Hp.
Qed.

Lemma after_path (fx : FPState) (R R' Rd : bvmap 5 word) (M M' : word -> option byte) (model model' : Model) (crc : credit)
      (qneg fnum f3 c3 p3 q0 q1 fx2 : Z) (nq nx : nat) (stx : L5.bstore) (wx : list Z) (bxo : L5.bigobj) :
  let BD := (if Z.testbit f3 0 then [(p3, 8 * c3)] else []) in
  (* [comment removed for export] *)
  model_but_vm model0 model -> hi_heap HI (BD ++ LB) crc M (m_vmmaps model) -> credit_after L cr OPMOD1_K (opmod1_bytes capb) crc ->
  div_entry_regs S R0 Rd -> top_frame M S R0 -> 0 <= qneg <= 1 ->
  L5.big_at RSEGS M (Q - 184) (L5.BO fnum 2 (L5.BInl A0 A1)) ->
  local_obj M (Q - 136) f3 c3 p3 -> (Z.testbit f3 0 = true -> L5C.fresh_block L LB M p3 (8 * c3)) ->
  L5.big_at RSEGS M bo bb -> L5C.obj_limbs RSEGS M bb wb -> (1 <= L5.bo_len bb)%nat ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M -> L5.bo_st bxo = L5.BInl A0 A1 -> (L5.bo_len bxo <= 2)%nat ->
  (* [comment removed for export] *)
  getr R' (reg 2) = Z_to_bv 64 (Q - 352) -> getr R' (reg 3) = Z_to_bv 64 GP -> getr R' (reg 4) = Z_to_bv 64 TP ->
  L5.big_at RSEGS M' Q (L5.BO (2 * qneg) nq (L5.BInl q0 q1)) ->
  L5.big_at RSEGS M' X (L5.BO fx2 nx stx) -> L5C.obj_limbs RSEGS M' (L5.BO fx2 nx stx) wx -> Z.testbit fx2 1 = false -> (exists v0 v1, stx = L5.BInl v0 v1) ->
  div_saves M' Q Rd -> (forall a, Q - 184 <= a < Q -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  L5C.hpres L (BD ++ LB) Q DIV_SCR [(X, 32); (L5.bo_data X bxo, 8 * Z.of_nat (L5.bo_len bxo)); (Q, 32)] M M' ->
  model_but_vm model model' -> hi_heap HI (BD ++ LB) crc M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (cfg R' L5DIVTAILU.DT2 M' model') K.
Proof.
  intros BD MBV HH CRA DER TF Hq ON LO3 FRESH3 OBB OLB LENB HP STXO LXO E2 E3 E4 OQ' OX' OL' NEG' [v0 [v1 ->]] DS' KEEP HP' MBV' HH'.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof ERRNOV as EV. pose proof IMG as IMG'.
  unfold L5.bo_data in HP'. rewrite STXO in HP'.
  assert (KA: forall a, Q <= a < 2 ^ 64 -> ~ (X <= a < X + 32) -> ~ (Q <= a < Q + 32) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha NX NQ. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP'). apply L5C.kept_stack. unfold Q; fsclia. rewrite DIV_SCR_val; clear; lia. exact Ha.
    rewrite EV; clear; lia. flia. apply outside3. exact NX. unfold X in NX |- *. clear - NX LXO; lia. exact NQ. }
  assert (KB: forall A n a, In (A, n) LB -> A <= a < A + n -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros A n a Hin Ha. pose proof (LBdef _ _ _ _ HH A n ltac:(apply in_app_iff; right; exact Hin)) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG', IMGLO in Aimg.
    apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP'). eapply L5C.kept_block. apply in_app_iff; right; exact Hin. exact Ha. clear - Alo; lia. clear - Ahi SPT; lia.
    rewrite EV; clear - Aimg Ha; lia. apply outside3; unfold X, Q; clear - Ha Ahi SLO'; lia. }
  pose proof OQ' as OQ2. unfold L5.big_at in OQ2. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OQ2. destruct OQ2 as (Qf & _).
  pose proof (local_of_num M _ _ ON) as [LO2 F2b]. pose proof ON as (_ & Fn & _). cbn [L5.bo_fb] in Fn.
  apply (stage_DT2 fx R' Rd M' model' crc (2 * qneg) (L5.BO fx2 nx (L5.BInl v0 v1)) wx fnum f3 c3 p3).
  - replace spd with (Q - 352) by (unfold Q, spd; clear; lia). exact E2. - exact E3. - exact E4.
  - exact (L5C.model_but_vm_trans _ _ _ MBV MBV').
  - exact HH'. - exact CRA. - exact DER. - exact DS'.
  - eapply top_frame_kept. 4: exact TF. intros i Hi; apply KA; unfold Q, X in *; flia. flia. flia.
  - exact Qf. - clear - Hq; lia. - apply Z.testbit_even_0.
  - exact OX'. - exact OL'. - exact NEG'. - eexists _, _; reflexivity.
  - eapply local_obj_kept. 4: exact LO2. intros i Hi; apply KEEP; flia. unfold Q; flia. unfold Q; flia.
  - exact F2b.
  - eapply local_obj_kept. 4: exact LO3. intros i Hi; apply KEEP; flia. unfold Q; flia. unfold Q; flia.
  - intros T. destruct (FRESH3 T) as (BR & BA & BDf). split. exact BR. split. exact BA.
    pose proof (LBdef _ _ _ _ HH' p3 (8 * c3) ltac:(subst BD; rewrite T; apply in_app_iff; left; left; reflexivity)) as (D' & _). exact D'.
  - eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KA; subst bo; unfold Q, X; flia. subst bo; flia. subst bo; flia.
  - pose proof BOK as (OB0 & _ & _ & BST). eapply obj_limbs_agree1. 3: exact OLB.
    + intros cap q E i Hi. rewrite E in BST. destruct BST as [INB _]. pose proof OLB as (Ln & _ & _).
      unfold L5.big_at in OB0. rewrite E in OB0. destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & _).
      apply (KB q (8 * cap) i INB). rewrite Ln in Hi. clear - Hi Hlc. lia.
    + intros cap q E. pose proof OLB as (Ln & _ & _). unfold L5.big_at in OB0. rewrite E in OB0.
      destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite Ln. clear - Hlc Hcap Qlo Qhi. lia.
  - exact LENB.
  - assert (CEIL: hl_ceil L <= S - SCR_OPMOD). { unfold hl_ceil. rewrite SCR_OPMOD_val. clear - SLO'. lia. }
    assert (LBceil: forall b, In b LB -> fst b + snd b <= hl_ceil L).
    { intros [A n] Hb. pose proof (LBdef _ _ _ _ HH A n ltac:(apply in_app_iff; right; exact Hb)) as (_ & _ & Ahi & _). unfold hl_ceil. cbn. exact Ahi. }
    eapply (L5HP.hpres_trans L LB (BD ++ LB) S SCR_OPMOD [(X, 32)] M0 M M' Q DIV_SCR). exact HP. exact HP'.
    + intros a KAo. eapply L5HP.kept_mono. exact KAo. intros b Hb; apply in_app_iff; right; exact Hb. unfold Q; fsclia. unfold Q; flia.
      intros OW. pose proof (L5HP.kept_not_in_scratch _ _ _ _ _ _ KAo LBceil CEIL ltac:(unfold hl_ceil; rewrite IMG'; clear - SPT; lia)) as NS.
      apply outside3. apply (L5HP.outside_in _ _ X 32 OW). left; reflexivity.
      pose proof (L5HP.outside_in _ _ X 32 OW ltac:(left; reflexivity)) as NX. unfold X in NX |- *. clear - NX LXO; lia.
      rewrite SCR_OPMOD_val in NS. unfold Q. clear - NS; lia.
    + intros b Hb; apply in_app_iff; right; exact Hb. + exact CEIL. + flia. + rewrite SCR_OPMOD_val; clear; lia. + rewrite EV; clear; lia. + flia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_EARLY (fx : FPState) (R Rd : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit) (qneg fnum f3 c3 p3 : Z) :
  let BD := (if Z.testbit f3 0 then [(p3, 8 * c3)] else []) in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 26) = Z_to_bv 64 qneg -> 0 <= qneg <= 1 -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 25) = Z_to_bv 64 0 -> getr R (reg 8) = Z_to_bv 64 X ->
  model_but_vm model0 model -> hi_heap HI (BD ++ LB) crc M (m_vmmaps model) -> credit_after L cr OPMOD1_K (opmod1_bytes capb) crc ->
  div_entry_regs S R0 Rd -> div_saves M Q Rd -> top_frame M S R0 ->
  zero_obj M Q -> x_is_a M X fbx -> L5.defined M X 32 ->
  L5.big_at RSEGS M (Q - 184) (L5.BO fnum 2 (L5.BInl A0 A1)) ->
  local_obj M (Q - 136) f3 c3 p3 -> (Z.testbit f3 0 = true -> L5C.fresh_block L LB M p3 (8 * c3)) ->
  L5.big_at RSEGS M bo bb -> L5C.obj_limbs RSEGS M bb wb -> (1 <= L5.bo_len bb)%nat ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R L5DIVEARLYU.EARLY M model) K.
Proof.
  intros BD H2 H3 H4 H8 Hq H9 H26 H27 MBV HH CRA DER DS TF ZQ [OBX NEGX] DX ON LO3 FRESH3 OBB OLB LENB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK.
  pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP) as SCR. rewrite SCR_OPMOD_val in SCR.
  unfold cfg. eapply (early_path fx R M model K (BD ++ LB) crc Q X Q qneg 0 (L5.BO fbx 2 (L5.BInl A0 A1)) (L5.BO fnum 2 (L5.BInl A0 A1)) [A0; A1] Rd).
  - replace (Q - 352) with spd by (unfold Q, spd; clear; lia). exact H2.
  - exact H3. - exact H4. - exact H8. - exact Hq. - exact H9. - exact H26. - left; reflexivity. - exact H27.
  - exact HH. - exact MOK. - exact HK0.
  - split. { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. unfold Q; fsclia. split. unfold Q; flia. split. exact SPT. unfold Q. rewrite DIV_SCR_val. eapply L5.defined_sub. exact SCR. clear; lia. clear; lia.
  - exact OBX. - cbn; clear; lia.
  - unfold X. rewrite <- Zplus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold Q, X; clear; lia. - unfold X; flia. - exact DX.
  - cbn. intros cap q E; discriminate E.
  - exact ON. - apply obj_limbs_x. - reflexivity.
  - cbn. intros cap q E; discriminate E.
  - cbn. intros c q c' q' E; discriminate E.
  - exact ZQ.
  - unfold Q. rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - clear; lia. - unfold Q; flia.
  - unfold Q. eapply L5.defined_sub. exact SCR. clear; lia. clear; lia.
  - right. unfold Q, X; clear; lia.
  - exact DS.
  - intros fx' R' M' model' q0 q1 stx E2 E3 E4 ES OQ' OX' OL' SM DX' DQ' DS' KEEP HP' MBV' HH'.
    cbn [L5.bo_fb L5.bo_len L5.bo_st] in OX', OL', SM. change L5DIVEARLYU.DT2 with L5DIVTAILU.DT2.
    eapply (after_path fx' R R' Rd M M' model model' crc qneg fnum f3 c3 p3 q0 q1 _ 0%nat 2%nat stx [A0; A1] (L5.BO fbx 2 (L5.BInl A0 A1))
              MBV HH CRA DER TF Hq ON LO3 FRESH3 OBB OLB LENB HP eq_refl ltac:(cbn; clear; lia) E2 E3 E4 OQ' OX' OL').
    + unfold L5DIVEARLYU.early_fb. rewrite Z.lor_0_r, Z.land_spec. apply Bool.andb_false_intro2. reflexivity.
    + destruct stx as [u0 u1|c q]. eexists _, _; reflexivity. contradiction.
    + exact DS'. + exact KEEP. + exact HP'. + exact MBV'. + exact HH'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_HALF (fx : FPState) (R Rd : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit) (qneg d fnum f3 c3 p3 : Z) :
  let BD := (if Z.testbit f3 0 then [(p3, 8 * c3)] else []) in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 26) = Z_to_bv 64 qneg -> 0 <= qneg <= 1 -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 8) = Z_to_bv 64 X ->
  getr R (reg 21) = Z_to_bv 64 d -> 1 <= d < 2 ^ 32 -> getr R (reg 11) = Z_to_bv 64 2 ->
  getr R (reg 25) = Z_to_bv 64 0 ->
  model_but_vm model0 model -> hi_heap HI (BD ++ LB) crc M (m_vmmaps model) -> credit_after L cr OPMOD1_K (opmod1_bytes capb) crc ->
  div_entry_regs S R0 Rd -> div_saves M Q Rd -> top_frame M S R0 ->
  zero_obj M Q -> x_is_a M X fbx -> L5.defined M X 32 ->
  L5.u64_at RSEGS M (Q - 248) (X + 16) -> L5.u64_at RSEGS M (Q - 240) 2 ->
  L5.big_at RSEGS M (Q - 184) (L5.BO fnum 2 (L5.BInl A0 A1)) ->
  local_obj M (Q - 136) f3 c3 p3 -> (Z.testbit f3 0 = true -> L5C.fresh_block L LB M p3 (8 * c3)) ->
  L5.big_at RSEGS M bo bb -> L5C.obj_limbs RSEGS M bb wb -> (1 <= L5.bo_len bb)%nat ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R L5DIVO1HU.HALF M model) K.
Proof.
  intros BD H2 H3 H4 H8 Hq H9 H18 H19 Hd H11 H26 MBV HH CRA DER DS TF ZQ [OBX NEGX] DX VT VTS ON LO3 FRESH3 OBB OLB LENB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK.
  pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP) as SCR. rewrite SCR_OPMOD_val in SCR.
  unfold cfg. eapply (half_path fx R M model K (BD ++ LB) crc Q X Q qneg 0 d fbx A0 A1 Rd).
  - replace (Q - 352) with spd by (unfold Q, spd; clear; lia). exact H2.
  - exact H3. - exact H4. - exact H8. - exact Hq. - exact H9. - exact H18. - exact H19. - exact Hd. - exact H11. - exact H26.
  - left; reflexivity.
  - exact HH. - exact MOK. - exact HK0.
  - split. { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. unfold Q; fsclia. split. unfold Q; flia. split. exact SPT. unfold Q. rewrite DIV_SCR_val. eapply L5.defined_sub. exact SCR. clear; lia. clear; lia.
  - exact OBX.
  - unfold X. rewrite <- Zplus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold Q, X; clear; lia. - unfold X; flia. - exact DX.
  - exact VT. - exact VTS.
  - exact ZQ.
  - unfold Q. rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - clear; lia. - unfold Q; flia.
  - unfold Q. eapply L5.defined_sub. exact SCR. clear; lia. clear; lia.
  - right. unfold Q, X; clear; lia.
  - exact DS.
  - intros fx' R' M' model' nq q0 q1 nr r0 r1 E2 E3 E4 ES OQ' OX' NR1 DX' DQ' DS' KEEP HP' MBV' HH'. change L5DIVO1HU.DT2 with L5DIVTAILU.DT2.
    eapply (after_path fx' R R' Rd M M' model model' crc qneg fnum f3 c3 p3 q0 q1 _ nq nr (L5.BInl r0 r1) (firstn nr [r0; r1]) (L5.BO 0 0 (L5.BInl A0 A1))
              MBV HH CRA DER TF Hq ON LO3 FRESH3 OBB OLB LENB HP eq_refl ltac:(cbn; clear; lia) E2 E3 E4 OQ' OX').
    + pose proof OX' as OX2. unfold L5.big_at in OX2. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OX2. destruct OX2 as (_ & _ & _ & _ & _ & _ & _ & R0' & R1').
      split. { cbn [L5.bo_len]. rewrite length_firstn. cbn [length]. clear - NR1; lia. }
      split. { destruct nr as [|[|n]]; [cbn; constructor | cbn; repeat constructor; clear - R0'; lia | exfalso; clear - NR1; lia]. } reflexivity.
    + unfold L5DIVO1HU.half_fb. rewrite Z.lor_0_r, Z.land_spec. apply Bool.andb_false_intro2. reflexivity.
    + eexists _, _; reflexivity.
    + exact DS'. + exact KEEP.
    + eapply hpres_wmono. 2: exact HP'. intros a OW r Hr. apply OW. cbn in Hr |- *. clear - Hr. tauto.
    + exact MBV'. + exact HH'.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gen_intro (fx4 : FPState) (R4 Rd : bvmap 5 word) (M M4 : word -> option byte) (model : Model) (fnum fden b0 b1 : Z) :
  let nb := L5.bo_len bb in
  getr R4 (reg 2) = Z_to_bv 64 spd -> getr R4 (reg 3) = Z_to_bv 64 GP -> getr R4 (reg 4) = Z_to_bv 64 TP ->
  getr R4 (reg 8) = Z_to_bv 64 X -> getr R4 (reg 9) = Z_to_bv 64 Q -> getr R4 (reg 18) = Z_to_bv 64 X ->
  getr R4 (reg 22) = Z_to_bv 64 (Q - 120) -> getr R4 (reg 23) = Z_to_bv 64 1 -> getr R4 (reg 25) = Z_to_bv 64 0 ->
  getr R4 (reg 26) = Z_to_bv 64 (Z.b2z (Z.testbit (L5.bo_fb bb) 1)) ->
  model_but_vm model0 model -> hi_heap HI LB cr M (m_vmmaps model) ->
  mem_grows M M4 -> (forall i, 0 <= i < 2 ^ 64 -> ~ (Q - 232 <= i < Q - 232 + 16) -> ~ (Q - 248 <= i < Q - 248 + 16) -> M4 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  L5.u64_at RSEGS M4 (Q - 240) 2 -> L5.u64_at RSEGS M4 (Q - 248) (X + 16) -> L5.u64_at RSEGS M4 (Q - 224) 0 -> L5.u64_at RSEGS M4 (Q - 232) (Q + 16) ->
  div_entry_regs S R0 Rd -> div_saves M Q Rd -> top_frame M S R0 -> zero_obj M Q -> x_is_a M X fbx -> L5.defined M X 32 ->
  L5.big_at RSEGS M (Q - 184) (L5.BO fnum 2 (L5.BInl A0 A1)) -> Z.testbit fnum 1 = false ->
  L5.bo_st bb = L5.BInl b0 b1 -> (nb = 1%nat \/ nb = 2%nat) -> L5.big_at RSEGS M (Q - 136) (L5.BO fden nb (L5.BInl b0 b1)) -> Z.testbit fden 1 = false ->
  L5.u64_at RSEGS M (Q - 152) (Q - 120) -> L5.u64_at RSEGS M (Q - 144) (Z.of_nat nb) ->
  L5.big_at RSEGS M bo bb -> L5C.obj_limbs RSEGS M bb wb -> (nb = 1%nat -> 2 ^ 32 <= b0) -> (nb = 2%nat -> BigFactsBase.val wb <= BigFactsBase.val [A0; A1]) ->
  L5C.hpres L LB S SCR_OPMOD [] M0 M -> L5.img_clear M 0x10000 0x20000 ->
  srealizes RSEGS SCFG (cfg R4 GEN M4 model) K.
Proof using SCFG_P L HI LY HIok R0 M0 model0 K LB cr S fbx fco bo bb wb G12 BO STK HS FCOR BOK DYN3 KN KZ KG.
  intros nb H2 H3 H4 H8 H9 H18 H22 H23 H25 H26 MBV HH MG FR VTS VT VQS VQ DER DS TF ZQ [OBX NEGX] DX ON Fn STB NB OD Fd VD VS OBB OLB V1 V2 HP IC.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof ERRNOV as EV. pose proof IMG as IMG'.
  pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP) as SCR. rewrite SCR_OPMOD_val in SCR.
  assert (KA: forall a, Q - 216 <= a < 2 ^ 64 -> M4 (Z_to_bv 64 a) = M (Z_to_bv 64 a)). { intros a Ha. apply FR. unfold Q in *; flia. clear - Ha; lia. clear - Ha; lia. }
  assert (FR1: forall i, 0 <= i < 2 ^ 64 -> ~ (Q - 248 <= i < Q - 216) -> M4 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Hn. apply FR. exact Hi. clear - Hn; lia. clear - Hn; lia. }
  apply (KG fx4 R4 M4 model fnum fden b0 b1). unfold o1_gen_entry.
  split. exact H2. split. exact H3. split. exact H4. split. exact H8. split. exact H9. split. exact H18. split. exact H22. split. exact H23. split. exact H25. split. exact H26.
  split. { eapply (hi_heap_stackwrite LB cr M M4 _ (Q - 248) (Q - 216)). exact HH. exact FR1. unfold Q; flia. unfold Q; flia. flia. exact MG. }
  split. exact MBV.
  split. { rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG. exact SCR. }
  split. { assert (CEIL: hl_ceil L <= S - SCR_OPMOD). { unfold hl_ceil. rewrite SCR_OPMOD_val. clear - SLO'. lia. }
           assert (LBceil: forall b, In b LB -> fst b + snd b <= hl_ceil L).
           { intros [A n] Hb. pose proof (LBdef _ _ _ _ HH A n Hb) as (_ & _ & Ahi & _). unfold hl_ceil. cbn. exact Ahi. }
           eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [] M0 M M4 S SCR_OPMOD []). exact HP.
           - eapply (L5HP.hpres_piece L LB S SCR_OPMOD [] M M4 (fun a => Q - 248 <= a < Q - 216)). exact FR1.
             intros a KA' C. apply (L5HP.kept_not_in_scratch _ _ _ _ _ _ KA' LBceil CEIL ltac:(unfold hl_ceil; rewrite IMG'; clear - SPT; lia)).
             rewrite SCR_OPMOD_val. unfold Q in C. clear - C; lia.
             rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG. exact SCR. exact MG.
           - intros a KA'; exact KA'. - intros b Hb; exact Hb. - exact CEIL. - flia. - rewrite SCR_OPMOD_val; clear; lia. - rewrite EV; clear; lia. - flia. }
  split. { intros i Hi. rewrite FR1. apply IC. exact Hi. clear - Hi; lia. unfold Q; clear - Hi SLO; lia. }
  split. { eapply top_frame_kept. 4: exact TF. intros i Hi; apply KA; unfold Q; flia. flia. flia. }
  split. { eapply (div_saves_o1_saves M4 S R0 Rd). flia. exact DER. eapply div_saves_kept. 4: exact DS. intros i Hi; apply KA; unfold Q in *; flia. unfold Q; flia. unfold Q; flia. }
  split. { eapply big_at_agree1. 4: exact ZQ. intros i Hi; apply KA; unfold Q in *; flia. unfold Q; flia. unfold Q; flia. }
  split. { split. 2: exact NEGX. eapply big_at_agree1. 4: exact OBX. intros i Hi; apply KA; unfold Q, X in *; flia. unfold X; flia. unfold X; flia. }
  split. { eapply L5.defined_grows. exact MG. exact DX. }
  split. { replace (S - 64 - 184) with (Q - 184) by (unfold Q; clear; lia). eapply big_at_agree1. 4: exact ON. intros i Hi; apply KA; unfold Q in *; flia. unfold Q; flia. unfold Q; flia. }
  split. exact Fn. split. exact STB. split. exact NB.
  split. { replace (S - 64 - 136) with (Q - 136) by (unfold Q; clear; lia). eapply big_at_agree1. 4: exact OD. intros i Hi; apply KA; unfold Q in *; flia. unfold Q; flia. unfold Q; flia. }
  split. exact Fd.
  split. { eapply u64_at_agree1. 4: exactA VD. intros i Hi; apply KA; unfold Q in *; flia. unfold Q; flia. unfold Q; flia. }
  split. { eapply u64_at_agree1. 4: exactA VS. intros i Hi; apply KA; unfold Q in *; flia. unfold Q; flia. unfold Q; flia. }
  split. exactA VQ. split. exactA VQS. split. exactA VT. split. exactA VTS.
  split. { eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KA; subst bo; unfold Q; flia. subst bo; flia. subst bo; flia. }
  split. { eapply obj_limbs_agree1. 3: exact OLB. intros cap q E; rewrite STB in E; discriminate E. intros cap q E; rewrite STB in E; discriminate E. }
  split. exact V1. exact V2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_E4 (fx : FPState) (R Rd : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc : list (Z * Z)) (crc : credit)
      (c qneg fnum fden : Z) (std : L5.bstore) :
  let nb := L5.bo_len bb in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 X -> qneg = Z.b2z (Z.testbit (L5.bo_fb bb) 1) -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 10) = Z_to_bv 64 c ->
  getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 22) = Z_to_bv 64 (Q - 120) -> getr R (reg 23) = Z_to_bv 64 1 ->
  getr R (reg 25) = Z_to_bv 64 0 -> getr R (reg 26) = Z_to_bv 64 qneg ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) -> LBc = blocks_ofst std ++ LB ->
  credit_after L cr OPMOD1_K (opmod1_bytes capb) crc ->
  (forall cq p, std = L5.BDyn cq p -> cq = capb /\ L5C.fresh_block L LB M p (8 * cq) /\ L5.bo_dyn bb = true) ->
  (forall v0 v1, std = L5.BInl v0 v1 -> L5.bo_st bb = L5.BInl v0 v1 /\ crc = cr) ->
  div_entry_regs S R0 Rd -> div_saves M Q Rd -> top_frame M S R0 ->
  zero_obj M Q -> x_is_a M X fbx -> L5.defined M X 32 ->
  L5.big_at RSEGS M (Q - 184) (L5.BO fnum 2 (L5.BInl A0 A1)) -> Z.testbit fnum 1 = false ->
  L5.big_at RSEGS M (Q - 136) (L5.BO fden nb std) -> Z.testbit fden 1 = false -> L5C.obj_limbs RSEGS M (L5.BO fden nb std) wb ->
  L5.u64_at RSEGS M (Q - 152) (L5.bo_data (Q - 136) (L5.BO fden nb std)) -> L5.u64_at RSEGS M (Q - 144) (Z.of_nat nb) ->
  (1 <= nb)%nat -> L5CMPU.res_sized c 2 nb -> (2%nat = nb -> c = L5CMPU.cmp_val [A0; A1] wb) ->
  L5.big_at RSEGS M bo bb -> L5C.obj_limbs RSEGS M bb wb ->
  L5C.hpres L LB S SCR_OPMOD [] M0 M -> L5.img_clear M 0x10000 0x20000 ->
  srealizes RSEGS SCFG (cfg R 0x225b8 M model) K.
Proof.
  cbv zeta. intros H2 H3 H4 H8 Hqn H9 H10 H18 H22 H23 H25 H26 MBV HH ELB CRA SDYN SINL DER DS TF ZQ XA' DX ON Fn OD Fd OLD VD VS NB1 RES VEQ OBB OLB HP IC.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP) as SCR. rewrite SCR_OPMOD_val in SCR. pose proof ERRNOV as EV. pose proof IMG as IMG'.
  pose proof XA' as [OBX NEGX]. pose proof OBX as OBX'. unfold L5.big_at in OBX'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OBX'. destruct OBX' as (Xf & Xfr & Xl & Xb0 & _).
  pose proof ON as ON'. unfold L5.big_at in ON'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in ON'. destruct ON' as (Nf & Nfr & Nl & Nb0 & _).
  pose proof OD as OD'. unfold L5.big_at in OD'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OD'. destruct OD' as (Df & Dfr & Dl & DST).
  pose proof ZQ as ZQ'. unfold zero_obj, L5.big_at in ZQ'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in ZQ'. destruct ZQ' as (Qf & _ & Ql & _).
  assert (Hq: 0 <= qneg <= 1). { subst qneg. destruct (Z.testbit _ 1); cbn; clear; lia. }
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (AQ8: Q mod 8 = 0). { rewrite <- (mod16_mod8 _ AQ16). reflexivity. }
  assert (AX8: X mod 8 = 0). { unfold X. rewrite <- Zplus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity. }
  assert (WF: L5.writable RSEGS M (Q - 352) 352). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; flia. unfold Q; flia. }
  (* [comment removed for export] *)
  set (c3 := match std with L5.BInl _ _ => 0 | L5.BDyn cq _ => cq end). set (p3 := match std with L5.BInl _ _ => 0 | L5.BDyn _ p => p end).
  assert (LO3: local_obj M (Q - 136) fden c3 p3).
  { split. exact Df. split. exact Dfr. intros T. subst c3 p3. destruct std as [v0 v1|cq p]. { destruct DST as (T' & _). rewrite T' in T. discriminate T. }
    destruct DST as (_ & C16 & C24 & Hlc & Hcap & _ & Qlo & Qhi & _). destruct (SDYN cq p eq_refl) as (-> & _ & _). pose proof CAPB1 as CB.
    split. exactA C16. split. clear - CB; lia. split. exactA C24. clear - Qlo Qhi; lia. }
  assert (FRESH3: Z.testbit fden 0 = true -> L5C.fresh_block L LB M p3 (8 * c3)).
  { intros T. subst c3 p3. destruct std as [v0 v1|cq p]. { destruct DST as (T' & _). rewrite T' in T. discriminate T. } exact (proj1 (proj2 (SDYN cq p eq_refl))). }
  assert (EBD: LBc = (if Z.testbit fden 0 then [(p3, 8 * c3)] else []) ++ LB).
  { rewrite ELB. subst c3 p3. destruct std as [v0 v1|cq p]; destruct DST as (T' & _); rewrite T'; reflexivity. }
  rewrite EBD in HH. clear EBD.
  assert (E2: getr R (reg 2) = Z_to_bv 64 (Q - 352)). { replace (Q - 352) with spd by (unfold Q, spd; clear; lia). exact H2. }
  assert (WQ: 0 <= Q < 2 ^ 64) by (unfold Q; flia). assert (QR: 1048928 <= Q <= 140737488355328) by (unfold Q; flia).
  destruct (Z.eq_dec c L5CMPU.MAXW) as [EC|NC].
  - (* [comment removed for export] *)
    subst c.
    pose proof (d6ue4e_conc fx R M (VO Q X bo fbx 0 fnum fden 0 0 0)) as P. cbn [VO] in P.
    destruct (P WQ E2 H10 QR AQ16) as (fx1 & R1 & M1 & _ & FR1 & _ & (MS1 & K1)). clear P.
    pose proof (mem_eq M M1 FR1) as EM1. subst M1.
    unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
    apply (stage_EARLY fx1 R1 Rd M model crc qneg fnum fden c3 p3); try (rewrite K1 by inl); try assumption.
    eapply hpres_wmono. 2: exact HP. intros a _ r Hr. destruct Hr.
  - (* [comment removed for export] *)
    destruct RES as (C01 & LT & GT).
    assert (Hc: 0 <= c <= 1). { clear - C01 NC. unfold L5CMPU.MAXW in *. lia. }
    assert (NB2: (L5.bo_len bb <= 2)%nat). { destruct (Nat.le_gt_cases (L5.bo_len bb) 2) as [Hle|Hgt]. exact Hle. exfalso. apply NC. apply LT. exact Hgt. }
    assert (STI: exists v0 v1, std = L5.BInl v0 v1).
    { destruct std as [v0 v1|cq p]. eexists _, _; reflexivity. exfalso.
      destruct (SDYN cq p eq_refl) as (_ & _ & DY). pose proof (DYN3 DY) as L3. clear - L3 NB2. lia. }
    destruct STI as (v0 & v1 & ->). destruct (SINL v0 v1 eq_refl) as [STB ->]. cbn [L5.bo_data L5.bo_st] in VD. replace (Q - 136 + 16) with (Q - 120) in VD by (clear; lia).
    subst c3 p3. cbv beta iota in LO3, FRESH3, HH.
    pose proof OLD as (Ln & Wok & WB). cbn [L5.bo_len L5.bo_st] in Ln, WB.
    destruct DST as (Db0 & D16 & D24 & _ & Rb0 & Rb1). rewrite Db0 in HH. cbn [app] in HH.
    (* [comment removed for export] *)
    assert (WXr: 0 <= X < 2 ^ 64) by (unfold X; flia). assert (W1: 0 <= 1 < 2 ^ 64) by (clear; lia).
    assert (Wfx: 0 <= fbx < 2 ^ 64) by (clear - Xfr; lia). assert (Wfn: 0 <= fnum < 2 ^ 64) by (clear - Nfr; lia). assert (Wc: 0 <= c < 2 ^ 64) by (clear - Hc; lia).
    assert (XR: 1048576 <= X <= 140737488355296) by (unfold X; flia).
    assert (QR2: 1048576 <= Q <= 140737488355296) by (unfold Q; flia).
    assert (APX: Q - 352 + 352 <= X \/ X + 32 <= Q - 352) by (left; unfold Q, X; clear; lia).
    assert (APQ2: Q - 352 + 352 <= Q \/ Q + 32 <= Q - 352) by (left; clear; lia).
    assert (Bfn: 0 <= fnum <= 255) by (clear - Nfr; lia). assert (Bfx: 0 <= fbx <= 255) by (clear - Xfr; lia).
    assert (Nl2: L5.u64_at RSEGS M (Q - 176) 2) by exactA Nl. assert (D16': L5.u64_at RSEGS M (Q - 120) v0) by exactA D16.
    assert (Xl2: L5.u64_at RSEGS M (X + 8) 2) by exact Xl. assert (Ql0: L5.u64_at RSEGS M (Q + 8) 0) by exact Ql.
    (* [comment removed for export] *)
    assert (POST: forall M1, mem_grows M M1 ->
              (forall i, 0 <= i < 2 ^ 64 -> ~ (Q - 232 <= i < Q - 232 + 16) -> ~ (Q - 248 <= i < Q - 248 + 16) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
              (forall a, Q - 216 <= a < 2 ^ 64 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
              /\ hi_heap HI LB cr M1 (m_vmmaps model)
              /\ L5C.hpres L LB S SCR_OPMOD [] M0 M1
              /\ L5.img_clear M1 0x10000 0x20000).
    { intros M1 MG1 FR1.
      assert (FR1': forall i, 0 <= i < 2 ^ 64 -> ~ (Q - 248 <= i < Q - 216) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
      { intros i Hi Hn. apply FR1. exact Hi. clear - Hn; lia. clear - Hn; lia. }
      split. { intros a Ha. apply FR1'. unfold Q in *; flia. clear - Ha; lia. }
      split. { eapply (hi_heap_stackwrite LB cr M M1 _ (Q - 248) (Q - 216)). exact HH. exact FR1'. unfold Q; flia. unfold Q; flia. flia. exact MG1. }
      split. { eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [] M0 M M1 S SCR_OPMOD []). exact HP.
               - eapply (L5HP.hpres_piece L LB S SCR_OPMOD [] M M1 (fun a => Q - 248 <= a < Q - 216)). exact FR1'.
                 { intros a KA' C. assert (LBceil: forall b, In b LB -> fst b + snd b <= hl_ceil L).
                   { intros [A n] Hb. pose proof (LBdef _ _ _ _ HH A n Hb) as (_ & _ & Ahi & _). unfold hl_ceil. cbn. exact Ahi. }
                   apply (L5HP.kept_not_in_scratch _ _ _ _ _ _ KA' LBceil ltac:(unfold hl_ceil; rewrite SCR_OPMOD_val; clear - SLO'; lia) ltac:(unfold hl_ceil; rewrite IMG'; clear - SPT; lia)).
                   rewrite SCR_OPMOD_val. unfold Q in C. clear - C; lia. }
                 rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG1. exact SCR. exact MG1.
               - intros a KA'; exact KA'. - intros b Hb; exact Hb. - unfold hl_ceil; rewrite SCR_OPMOD_val; clear - SLO'; lia. - flia.
               - rewrite SCR_OPMOD_val; clear; lia. - rewrite EV; clear; lia. - flia. }
      intros i Hi. rewrite FR1'. apply IC. exact Hi. clear - Hi; lia. unfold Q; clear - Hi SLO; lia. }
    destruct (Nat.eq_dec (L5.bo_len bb) 1) as [NB1'|NBne].
    + (* [comment removed for export] *)
      assert (VS1: L5.u64_at RSEGS M (Q - 144) 1). { rewrite NB1' in VS. exact VS. }
      assert (Wv0: 0 <= v0 < 2 ^ 64) by (clear - Rb0; lia).
      destruct (Z_lt_le_dec v0 (2 ^ 32)) as [SMALL|BIG].
      * (* [comment removed for export] *)
        assert (Hv0: 1 <= v0 <= 4294967295).
        { split. 2: clear - SMALL; lia. pose proof BOK as (_ & _ & RED & _). rewrite WB, NB1' in RED. cbn in RED.
          destruct RED as [RED|RED]. discriminate RED. change (nth (length [v0] - 1) [v0] 0) with v0 in RED. clear - RED Rb0. lia. }
        assert (SR0: srl_range v0 4294967296 0 0). { unfold srl_range. rewrite Z.div_small. clear; lia. clear - Rb0 SMALL; lia. }
        pose proof (d6ue4h_conc fx R M (VO Q X bo fbx c fnum fden 0 0 v0)) as P. cbn [VO] in P.
        destruct (P WQ WXr WQ Wfx Wfn Wc Wv0 E2 H9 H10 H18 QR AQ16 WF Nf Nl2 VS1 VD D16' Hc Bfn Nb0 XR AX8 APX Xf Bfx Xb0 Xl2 QR2 AQ8 APQ2 Qf Ql0 Hv0 SR0)
          as (fx1 & R1 & M1 & MG1 & _ & FR1 & (MS1 & K1 & _ & A11 & _ & _ & _ & A21 & CVTS & CVT & CVQS & CVQ)). clear P.
        destruct (POST M1 MG1 FR1) as (KA & HH1 & HP1 & IC1).
        unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
        apply (stage_HALF fx1 R1 Rd M1 model cr qneg v0 fnum fden 0 0).
        -- rewrite (K1 2%nat) by inl. exact H2. -- rewrite (K1 3%nat) by inl. exact H3. -- rewrite (K1 4%nat) by inl. exact H4.
        -- rewrite (K1 26%nat) by inl. exact H26. -- exact Hq. -- rewrite (K1 9%nat) by inl. exact H9. -- rewrite (K1 8%nat) by inl. exact H8.
        -- exact A21. -- clear - Hv0; lia. -- exact A11. -- rewrite (K1 25%nat) by inl. exact H25.
        -- exact MBV.
        -- rewrite Db0. cbn [app]. exact HH1.
        -- exact CRA. -- exact DER.
        -- eapply div_saves_kept. 4: exact DS. intros i Hi; apply KA; unfold Q in *; flia. unfold Q; flia. unfold Q; flia.
        -- eapply top_frame_kept. 4: exact TF. intros i Hi; apply KA; unfold Q; flia. flia. flia.
        -- eapply big_at_agree1. 4: exact ZQ. intros i Hi; apply KA; unfold Q in *; flia. unfold Q; flia. unfold Q; flia.
        -- split. 2: exact NEGX. eapply big_at_agree1. 4: exact OBX. intros i Hi; apply KA; unfold Q, X in *; flia. unfold X; flia. unfold X; flia.
        -- eapply L5.defined_grows. exact MG1. exact DX.
        -- exactA CVT. -- exactA CVTS.
        -- eapply big_at_agree1. 4: exact ON. intros i Hi; apply KA; unfold Q in *; flia. unfold Q; flia. unfold Q; flia.
        -- eapply local_obj_kept. 4: exact LO3. intros i Hi; apply KA; unfold Q in *; flia. unfold Q; flia. unfold Q; flia.
        -- intros T. rewrite Db0 in T. discriminate T.
        -- eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KA; subst bo; unfold Q; flia. subst bo; flia. subst bo; flia.
        -- eapply obj_limbs_agree1. 3: exact OLB. intros cap q E; rewrite STB in E; discriminate E. intros cap q E; rewrite STB in E; discriminate E.
        -- exact NB1.
        -- eapply hpres_wmono. 2: exact HP1. intros a _ r Hr. destruct Hr.
      * (* [comment removed for export] *)
        assert (Hv0: 4294967296 <= v0 <= 18446744073709551615) by (clear - BIG Rb0; lia).
        assert (SR1: srl_range v0 4294967296 1 4294967295).
        { unfold srl_range. split. apply Z.div_le_lower_bound. clear; lia. clear - BIG; lia.
          assert (LT': v0 / 4294967296 < 4294967296). { apply Z.div_lt_upper_bound. clear; lia. clear - Rb0; lia. } clear - LT'; lia. }
        pose proof (d6ue4g1_conc fx R M (VO Q X bo fbx c fnum fden 0 0 v0)) as P. cbn [VO] in P.
        destruct (P WQ WXr WQ Wfx Wfn Wc Wv0 E2 H9 H10 H18 QR AQ16 WF Nf Nl2 VS1 VD D16' Hc Bfn Nb0 XR AX8 APX Xf Bfx Xb0 Xl2 QR2 AQ8 APQ2 Qf Ql0 Hv0 SR1)
          as (fx1 & R1 & M1 & MG1 & _ & FR1 & (MS1 & K1 & _ & _ & _ & _ & _ & _ & CVTS & CVT & CVQS & CVQ)). clear P.
        unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
        apply (gen_intro fx1 R1 Rd M M1 model fnum fden v0 v1); try (rewrite K1 by inl); try assumption.
        -- rewrite Hqn in H26. exact H26.
        -- left. exact NB1'.
        -- intros _. clear - BIG; lia.
        -- intros E2'. exfalso. clear - NB1' E2'. lia.
    + (* [comment removed for export] *)
      assert (NB2': L5.bo_len bb = 2%nat). { clear - NB1 NB2 NBne. lia. }
      assert (VS2: L5.u64_at RSEGS M (Q - 144) 2). { rewrite NB2' in VS. exact VS. }
      pose proof (d6ue4g2_conc fx R M (VO Q X bo fbx c fnum fden 0 0 0)) as P. cbn [VO] in P.
      destruct (P WQ WXr WQ Wfx Wfn Wc E2 H9 H10 H18 QR AQ16 WF Nf Nl2 VS2 Hc Bfn Nb0 XR AX8 APX Xf Bfx Xb0 Xl2 QR2 AQ8 APQ2 Qf Ql0)
        as (fx1 & R1 & M1 & MG1 & _ & FR1 & (MS1 & K1 & _ & _ & _ & _ & _ & _ & CVTS & CVT & CVQS & CVQ)). clear P.
      unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
      apply (gen_intro fx1 R1 Rd M M1 model fnum fden v0 v1); try (rewrite K1 by inl); try assumption.
      -- rewrite Hqn in H26. exact H26.
      -- right. exact NB2'.
      -- intros E1'. exfalso. clear - NB2' E1'. lia.
      -- intros _. pose proof (VEQ ltac:(rewrite NB2'; reflexivity)) as EC.
         destruct (Z_lt_le_dec (BigFactsBase.val [A0; A1]) (BigFactsBase.val wb)) as [LTv|GEv]. 2: exact GEv.
         exfalso. apply NC. rewrite EC. apply (proj2 (L5CMPU.cmp_val_lt _ _)). exact LTv.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma big_at_reflag M M' o f f' n st :
  L5.big_at RSEGS M o (L5.BO f n st) -> L5.u8_at RSEGS M' o f' -> 0 <= f' < 256 -> Z.testbit f' 0 = Z.testbit f 0 ->
  (forall i, o + 1 <= i < o + 32 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= o -> o + 32 <= 2 ^ 64 ->
  L5.big_at RSEGS M' o (L5.BO f' n st).
Proof using S fco bb FCOR DYN3.
  intros OB U F T HA Ho Hhi. unfold L5.big_at in OB |- *. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OB |- *. destruct OB as (_ & _ & U8 & ST).
  split. exact U. split. exact F. split. { eapply u64_at_agree1. 4: exact U8. intros i Hi; apply HA; lia. lia. lia. }
  destruct st as [v0 v1|c q].
  - destruct ST as (T0 & U16 & U24 & R). rewrite T. split. exact T0. split. { eapply u64_at_agree1. 4: exact U16. intros i Hi; apply HA; lia. lia. lia. }
    split. { eapply u64_at_agree1. 4: exact U24. intros i Hi; apply HA; lia. lia. lia. } exact R.
  - destruct ST as (T0 & U16 & U24 & R). rewrite T. split. exact T0. split. { eapply u64_at_agree1. 4: exact U16. intros i Hi; apply HA; lia. lia. lia. }
    split. { eapply u64_at_agree1. 4: exact U24. intros i Hi; apply HA; lia. lia. lia. } exact R.
Qed.

(* [comment removed for export] *)
Lemma stage_E3 (fx : FPState) (R Rd : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc : list (Z * Z)) (crc : credit)
      (fnum0 fden0 : Z) (std : L5.bstore) :
  let nb := L5.bo_len bb in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 19) = Z_to_bv 64 fden0 ->
  getr R (reg 20) = Z_to_bv 64 fbx -> getr R (reg 22) = Z_to_bv 64 (Q - 120) -> getr R (reg 23) = Z_to_bv 64 1 ->
  Z.testbit fden0 1 = Z.testbit (L5.bo_fb bb) 1 -> Z.testbit fnum0 1 = false ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) -> LBc = blocks_ofst std ++ LB ->
  credit_after L cr OPMOD1_K (opmod1_bytes capb) crc ->
  (forall cq p, std = L5.BDyn cq p -> cq = capb /\ L5C.fresh_block L LB M p (8 * cq) /\ L5.bo_dyn bb = true) ->
  (forall v0 v1, std = L5.BInl v0 v1 -> L5.bo_st bb = L5.BInl v0 v1 /\ crc = cr) ->
  div_entry_regs S R0 Rd -> div_saves M Q Rd -> top_frame M S R0 ->
  zero_obj M Q -> x_is_a M X fbx -> L5.defined M X 32 ->
  L5.big_at RSEGS M (Q - 184) (L5.BO fnum0 2 (L5.BInl A0 A1)) ->
  L5.big_at RSEGS M (Q - 136) (L5.BO fden0 nb std) -> L5C.obj_limbs RSEGS M (L5.BO fden0 nb std) wb ->
  L5.u64_at RSEGS M (Q - 152) (L5.bo_data (Q - 136) (L5.BO fden0 nb std)) -> L5.u64_at RSEGS M (Q - 144) (Z.of_nat nb) -> (1 <= nb)%nat ->
  L5.big_at RSEGS M bo bb -> L5C.obj_limbs RSEGS M bb wb ->
  L5C.hpres L LB S SCR_OPMOD [] M0 M -> L5.img_clear M 0x10000 0x20000 ->
  srealizes RSEGS SCFG (cfg R 0x22584 M model) K.
Proof.
  cbv zeta. intros H2 H3 H4 H8 H9 H18 H19 H20 H22 H23 FD1 FN1 MBV HH ELB CRA SDYN SINL DER DS TF ZQ XA' DX ON OD OLD VD VS NB1 OBB OLB HP IC.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP) as SCR. rewrite SCR_OPMOD_val in SCR. pose proof ERRNOV as EV. pose proof IMG as IMG'.
  pose proof XA' as [OBX NEGX]. pose proof OBX as OBX'. unfold L5.big_at in OBX'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OBX'. destruct OBX' as (Xf & Xfr & _).
  pose proof ON as ON'. unfold L5.big_at in ON'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in ON'. destruct ON' as (Nf & Nfr & Nl & Nb0 & _).
  pose proof OD as OD'. unfold L5.big_at in OD'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OD'. destruct OD' as (Df & Dfr & Dl & DST).
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (WF: L5.writable RSEGS M (Q - 352) 352). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; flia. unfold Q; flia. }
  assert (E2: getr R (reg 2) = Z_to_bv 64 (Q - 352)). { replace (Q - 352) with spd by (unfold Q, spd; clear; lia). exact H2. }
  (* [comment removed for export] *)
  pose proof (d5ue3_conc fx R M (VO Q X bo fbx 0 fnum0 fden0 0 0 0)) as P. cbn [VO] in P.
  destruct (P ltac:(unfold Q; flia) ltac:(clear - Xfr; lia) ltac:(clear - Dfr; lia) ltac:(clear - Nfr; lia) E2 H19 H20 ltac:(unfold Q; flia) AQ16 WF Nf Df
              ltac:(clear - Nfr; lia) ltac:(clear - Dfr; lia) ltac:(clear - Xfr; lia))
    as (fx1 & R1 & M1 & MG1 & _ & FR1 & (MS1 & K1 & Bra & A10 & A11 & A25 & A26 & CD & CN)). clear P.
  rewrite (L5K.land2_bit1_false fbx) in A25, A26 by (first [exact NEGX | clear - Xfr; lia]). rewrite Z.lxor_0_r in A26.
  assert (A26': getr R1 (reg 26) = Z_to_bv 64 (Z.b2z (Z.testbit (L5.bo_fb bb) 1))).
  { apply BG.word_of_unsigned. rewrite A26, <- FD1. destruct (Z.testbit fden0 1) eqn:T.
    rewrite (L5K.land2_bit1_true fden0) by (first [exact T | clear - Dfr; lia]). reflexivity.
    rewrite (L5K.land2_bit1_false fden0) by (first [exact T | clear - Dfr; lia]). reflexivity. }
  assert (A25': getr R1 (reg 25) = Z_to_bv 64 0). { apply BG.word_of_unsigned. exact A25. }
  assert (SP1: getr R1 (reg 2) = Z_to_bv 64 spd). { rewrite (K1 2%nat) by inl. exact H2. }
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  set (fnum := Z.land fnum0 253) in CN. set (fden := Z.land fden0 253) in CD.
  assert (Fn: 0 <= fnum < 256 /\ Z.testbit fnum 1 = false /\ Z.testbit fnum 0 = Z.testbit fnum0 0).
  { subst fnum. split. apply L5.land_byte_range. clear; lia. rewrite !Z.land_spec. split. apply Bool.andb_false_intro2. reflexivity. rewrite Bool.andb_true_r. reflexivity. }
  assert (Fd: 0 <= fden < 256 /\ Z.testbit fden 1 = false /\ Z.testbit fden 0 = Z.testbit fden0 0).
  { subst fden. split. apply L5.land_byte_range. clear; lia. rewrite !Z.land_spec. split. apply Bool.andb_false_intro2. reflexivity. rewrite Bool.andb_true_r. reflexivity. }
  assert (KA1: forall a, 0 <= a < 2 ^ 64 -> a <> Q - 184 -> a <> Q - 136 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N1 N2. apply FR1. exact Ha. clear - N1; lia. clear - N2; lia. }
  assert (ON1: L5.big_at RSEGS M1 (Q - 184) (L5.BO fnum 2 (L5.BInl A0 A1))).
  { eapply big_at_reflag. exact ON. exact CN. exact (proj1 Fn). exact (proj2 (proj2 Fn)). intros i Hi; apply KA1; unfold Q in *; flia. unfold Q; flia. unfold Q; flia. }
  assert (OD1: L5.big_at RSEGS M1 (Q - 136) (L5.BO fden (L5.bo_len bb) std)).
  { eapply big_at_reflag. exact OD. exact CD. exact (proj1 Fd). exact (proj2 (proj2 Fd)). intros i Hi; apply KA1; unfold Q in *; flia. unfold Q; flia. unfold Q; flia. }
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (hi_heap_stackwrite LBc crc M M1 _ (Q - 184) (Q - 135)). exact HH. { intros i Hi Hn. apply KA1. exact Hi. clear - Hn; lia. clear - Hn; lia. }
    unfold Q; flia. unfold Q; flia. flia. exact MG1. }
  assert (NBLE: Z.of_nat (L5.bo_len bb) <= 268).
  { pose proof CAPB1 as CB. unfold capb, L5.bo_cap in CB. pose proof BOK as (OB0 & _). unfold L5.big_at in OB0.
    destruct (L5.bo_st bb) as [u0 u1|c q]. destruct OB0 as (_ & _ & _ & _ & _ & _ & Hl & _). clear - Hl; lia.
    destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & _). clear - Hlc CB; lia. }
  assert (OLD1: L5C.obj_limbs RSEGS M1 (L5.BO fden (L5.bo_len bb) std) wb).
  { eapply obj_limbs_agree1. 3: exact OLD.
    + cbn [L5.bo_st L5.bo_len]. intros cq p E i Hi. subst std. destruct (SDYN cq p eq_refl) as (-> & FB & _).
      pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB) as (Plo & _ & _ & _ & Phi). unfold hl_ceil in Phi. pose proof OLD as (Ln & _). cbn [L5.bo_len] in Ln. rewrite Ln in Hi.
      pose proof CAPB1 as CB. destruct DST as (_ & _ & _ & Hlc & _).
      apply KA1. clear - Hi Plo Phi Hlc CB SPT; lia. unfold Q; clear - Hi Phi Hlc SLO'; lia. unfold Q; clear - Hi Phi Hlc SLO'; lia.
    + cbn [L5.bo_st L5.bo_len]. intros cq p E. subst std. destruct (SDYN cq p eq_refl) as (-> & FB & _).
      pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB) as (Plo & _ & _ & _ & Phi). unfold hl_ceil in Phi. pose proof OLD as (Ln & _). cbn [L5.bo_len] in Ln. rewrite Ln.
      destruct DST as (_ & _ & _ & Hlc & _). clear - Plo Phi Hlc SPT; lia.
  }
  (* [comment removed for export] *)
  eapply (CMP fx1 R1 M1 model K spd (Q - 184) (Q - 136) 0x225b8 (L5.BO fnum 2 (L5.BInl A0 A1)) (L5.BO fden (L5.bo_len bb) std) [A0; A1] wb Mh Ml SP1 A10 A11 Bra).
  - split. clear; lia. reflexivity.
  - split. exact ON1. cbn [L5.bo_fb L5.bo_len L5.bo_data L5.bo_st]. split. exact (proj1 (proj2 Fn)). split. clear; lia. split. clear; lia.
    split. { unfold Q. replace (S - 64 - 184) with (S + 8 * (-31)) by (clear; lia). apply al8. exact A16. } split. unfold Q; flia. split. unfold Q; flia. split. unfold Q; flia. split. unfold Q; flia.
    eapply L5.defined_grows. exact MG1. eapply L5.defined_sub. exact SCR. unfold Q; clear; lia. unfold Q; clear; lia.
  - split. exact OD1. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact (proj1 (proj2 Fd)). split. exact NB1. split. clear - NBLE; lia.
    split. { unfold Q. replace (S - 64 - 136) with (S + 8 * (-25)) by (clear; lia). apply al8. exact A16. } split. unfold Q; flia. split. unfold Q; flia.
    unfold L5.bo_data. cbn [L5.bo_st]. destruct std as [v0 v1|cq p].
    + destruct DST as (_ & _ & _ & Hl2 & _). split. unfold Q; flia. split. unfold Q; clear - Hl2 SLO SHI; lia.
      eapply L5.defined_grows. exact MG1. eapply L5.defined_sub. exact SCR. unfold Q; clear; lia. unfold Q; clear - Hl2; lia.
    + destruct (SDYN cq p eq_refl) as (-> & FB & _). pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB) as (Plo & _ & _ & _ & Phi). unfold hl_ceil in Phi.
      pose proof CAPB1 as CB. pose proof BOK as (OB0 & _). unfold L5.big_at in OB0.
      assert (LC: Z.of_nat (L5.bo_len bb) <= capb). { unfold capb, L5.bo_cap. destruct (L5.bo_st bb) as [u0 u1|c' q']. destruct OB0 as (_ & _ & _ & _ & _ & _ & Hl & _). clear - Hl; lia.
        destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & _). exact Hlc. }
      split. clear - Plo; lia. split. clear - Phi LC SPT; lia.
      eapply L5.defined_grows. exact MG1. destruct FB as (_ & _ & DF). eapply L5.defined_sub. exact DF. clear; lia. clear - LC; lia.
  - (* [comment removed for export] *)
    unfold L5CMPU.cmp_stack, L5CMPU.apart. cbn [L5.bo_len L5.bo_data L5.bo_st].
    split. { unfold spd. replace (S - 416) with (S + (-26) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; flia.
    split. { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_grows. exact MG1. eapply L5.defined_sub. exact SCR. unfold spd; clear; lia. unfold spd; clear; lia. unfold spd; flia. unfold spd; flia. }
    split. left; unfold spd, Q; clear; lia. split. left; unfold spd, Q; clear; lia. split. left; unfold spd, Q; clear; lia.
    destruct std as [v0 v1|cq p]; cbn [L5.bo_data L5.bo_st L5.bo_len]. left; unfold spd, Q; clear; lia.
    right. destruct (SDYN cq p eq_refl) as (-> & FB & _). pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB) as (Plo & _ & _ & _ & Phi). unfold hl_ceil in Phi.
    pose proof OLD as (Ln & _). cbn [L5.bo_len] in Ln. pose proof CAPB1 as CB. destruct DST as (_ & _ & _ & Hlc & _). unfold spd. clear - Phi Hlc CB SLO'; lia.
  - apply obj_limbs_x.
  - exact OLD1.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 (KR & RP & (c & B10 & RES & VEQ) & FR2 & MG2).
    assert (KC: forall i, 0 <= i < 2 ^ 64 -> ~ (spd - 80 <= i < spd) -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)).
    { intros i Hi Ni. apply FR2. rewrite BG.unsigned_lit by exact Hi. exact Ni. }
    assert (KA2: forall a, 0 <= a < 2 ^ 64 -> a <> Q - 184 -> a <> Q - 136 -> ~ (spd - 80 <= a < spd) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N1 N2 N3. rewrite (KC a Ha N3). apply KA1. exact Ha. exact N1. exact N2. }
    pose proof (mem_grows_trans _ _ _ MG1 MG2) as MG12.
    apply (stage_E4 fx2 R2 Rd M2 model LBc crc c (Z.b2z (Z.testbit (L5.bo_fb bb) 1)) fnum fden std); try (rewrite KR by inl); try (rewrite K1 by inl); try assumption.
    + reflexivity.
    + eapply (hi_heap_stackwrite LBc crc M1 M2 _ (spd - 80) spd). exact HH1. exact KC. unfold spd; flia. unfold spd; flia. flia. exact MG2.
    + intros cq p E. destruct (SDYN cq p E) as (A & (BR & BA & BD) & C). split. exact A. split. 2: exact C. split. exact BR. split. exact BA.
      eapply L5.defined_grows. exact MG12. exact BD.
    + eapply div_saves_kept. 4: exact DS. intros i Hi; apply KA2; unfold Q, spd in *; flia. unfold Q; flia. unfold Q; flia.
    + eapply top_frame_kept. 4: exact TF. intros i Hi; apply KA2; unfold Q, spd in *; flia. flia. flia.
    + eapply big_at_agree1. 4: exact ZQ. intros i Hi; apply KA2; unfold Q, spd in *; flia. unfold Q; flia. unfold Q; flia.
    + split. 2: exact NEGX. eapply big_at_agree1. 4: exact OBX. intros i Hi; apply KA2; unfold Q, X, spd in *; flia. unfold X; flia. unfold X; flia.
    + eapply L5.defined_grows. exact MG12. exact DX.
    + eapply big_at_agree1. 4: exact ON1. intros i Hi; apply KC; unfold Q, spd in *; flia. unfold Q; flia. unfold Q; flia.
    + exact (proj1 (proj2 Fn)).
    + eapply big_at_agree1. 4: exact OD1. intros i Hi; apply KC; unfold Q, spd in *; flia. unfold Q; flia. unfold Q; flia.
    + exact (proj1 (proj2 Fd)).
    + eapply obj_limbs_agree1. 3: exact OLD1.
      * cbn [L5.bo_st L5.bo_len]. intros cq p E i Hi. subst std. destruct (SDYN cq p eq_refl) as (-> & FB & _).
        pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB) as (Plo & _ & _ & _ & Phi). unfold hl_ceil in Phi. pose proof OLD as (Ln & _). cbn [L5.bo_len] in Ln. rewrite Ln in Hi.
        pose proof CAPB1 as CB. destruct DST as (_ & _ & _ & Hlc & _).
        apply KC. clear - Hi Plo Phi Hlc CB SPT; lia. unfold spd; clear - Hi Phi Hlc SLO'; lia.
      * cbn [L5.bo_st L5.bo_len]. intros cq p E. subst std. destruct (SDYN cq p eq_refl) as (-> & FB & _).
        pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB) as (Plo & _ & _ & _ & Phi). unfold hl_ceil in Phi. pose proof OLD as (Ln & _). cbn [L5.bo_len] in Ln. rewrite Ln.
        destruct DST as (_ & _ & _ & Hlc & _). clear - Plo Phi Hlc SPT; lia.
    + eapply u64_at_agree1. 4: exact VD. intros i Hi; apply KA2; unfold Q, spd in *; flia. unfold Q; flia. unfold Q; flia.
    + eapply u64_at_agree1. 4: exact VS. intros i Hi; apply KA2; unfold Q, spd in *; flia. unfold Q; flia. unfold Q; flia.
    + eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KA2; subst bo; unfold Q, spd; flia. subst bo; flia. subst bo; flia.
    + pose proof BOK as (OB0 & _ & _ & BST). eapply obj_limbs_agree1. 3: exact OLB.
      * intros cap q E i Hi. rewrite E in BST. destruct BST as [INB _]. pose proof OLB as (Ln & _ & _).
        unfold L5.big_at in OB0. rewrite E in OB0. destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _).
        pose proof (LBdef _ _ _ _ HH0 q (8 * cap) INB) as (_ & _ & Ahi & _).
        apply KA2. rewrite Ln in Hi; clear - Hi Hlc Qlo Qhi; lia. unfold Q; rewrite Ln in Hi; clear - Hi Hlc Ahi SLO'; lia. unfold Q; rewrite Ln in Hi; clear - Hi Hlc Ahi SLO'; lia.
        unfold spd; rewrite Ln in Hi; clear - Hi Hlc Ahi SLO'; unfold hl_ceil in *; lia.
      * intros cap q E. pose proof OLB as (Ln & _ & _). unfold L5.big_at in OB0. rewrite E in OB0.
        destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite Ln. clear - Hlc Hcap Qlo Qhi. lia.
    + eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [] M0 M M2 S SCR_OPMOD []). exact HP.
      * eapply (L5HP.hpres_piece L LB S SCR_OPMOD [] M M2 (fun a => a = Q - 184 \/ a = Q - 136 \/ (spd - 80 <= a < spd))).
        { intros a Ha Hn. apply KA2. exact Ha. clear - Hn; lia. clear - Hn; lia. clear - Hn; lia. }
        { intros a KA' C. assert (LBceil: forall b, In b LB -> fst b + snd b <= hl_ceil L).
          { intros [A n] Hb. pose proof (LBdef _ _ _ _ HH0 A n Hb) as (_ & _ & Ahi & _). unfold hl_ceil. cbn. exact Ahi. }
          apply (L5HP.kept_not_in_scratch _ _ _ _ _ _ KA' LBceil ltac:(unfold hl_ceil; rewrite SCR_OPMOD_val; clear - SLO'; lia) ltac:(unfold hl_ceil; rewrite IMG'; clear - SPT; lia)).
          rewrite SCR_OPMOD_val. unfold Q, spd in C. clear - C; lia. }
        rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG12. exact SCR. exact MG12.
      * intros a KA'; exact KA'. * intros b Hb; exact Hb. * unfold hl_ceil; rewrite SCR_OPMOD_val; clear - SLO'; lia. * flia.
      * rewrite SCR_OPMOD_val; clear; lia. * rewrite EV; clear; lia. * flia.
    + intros i Hi. rewrite KA2. apply IC. exact Hi. clear - Hi; lia. unfold Q; clear - Hi SLO; lia. unfold Q; clear - Hi SLO; lia. unfold spd; clear - Hi SLO; lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_E2 (fx : FPState) (R Rd : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc : list (Z * Z)) (crc : credit)
      (fden0 : Z) (std : L5.bstore) :
  let nb := L5.bo_len bb in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 23) = Z_to_bv 64 1 ->
  getr R (reg 20) = getr R0 (reg 20) -> getr R (reg 21) = getr R0 (reg 21) -> getr R (reg 24) = getr R0 (reg 24) -> getr R (reg 25) = getr R0 (reg 25) ->
  getr R (reg 26) = getr R0 (reg 26) -> getr R (reg 27) = getr R0 (reg 27) ->
  Z.testbit fden0 1 = Z.testbit (L5.bo_fb bb) 1 ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) -> LBc = blocks_ofst std ++ LB ->
  credit_after L cr OPMOD1_K (opmod1_bytes capb) crc ->
  (forall cq p, std = L5.BDyn cq p -> cq = capb /\ L5C.fresh_block L LB M p (8 * cq) /\ L5.bo_dyn bb = true) ->
  (forall v0 v1, std = L5.BInl v0 v1 -> L5.bo_st bb = L5.BInl v0 v1 /\ crc = cr) ->
  div_entry_regs S R0 Rd -> div_saves M Q Rd -> top_frame M S R0 ->
  zero_obj M Q -> x_is_a M X fbx -> L5.defined M X 32 ->
  L5.big_at RSEGS M (Q - 136) (L5.BO fden0 nb std) -> L5C.obj_limbs RSEGS M (L5.BO fden0 nb std) wb ->
  L5.big_at RSEGS M bo bb -> L5C.obj_limbs RSEGS M bb wb ->
  L5C.hpres L LB S SCR_OPMOD [] M0 M -> L5.img_clear M 0x10000 0x20000 ->
  srealizes RSEGS SCFG (cfg R 0x22548 M model) K.
Proof.
  cbv zeta. intros H2 H3 H4 H8 H9 H18 H23 H20 H21 H24 H25 H26 H27 FD1 MBV HH ELB CRA SDYN SINL DER DS TF ZQ XA' DX OD OLD OBB OLB HP IC.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP) as SCR. rewrite SCR_OPMOD_val in SCR. pose proof ERRNOV as EV. pose proof IMG as IMG'. pose proof IMGLO as IMGLO'.
  pose proof XA' as [OBX NEGX]. pose proof OBX as OBX'. unfold L5.big_at in OBX'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OBX'. destruct OBX' as (Xf & Xfr & Xl & Xb0 & _).
  pose proof OD as OD'. unfold L5.big_at in OD'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OD'. destruct OD' as (Df & Dfr & Dl & DST).
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (AX8: X mod 8 = 0). { unfold X. rewrite <- Zplus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity. }
  assert (WF: L5.writable RSEGS M (Q - 352) 352). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; flia. unfold Q; flia. }
  assert (E2: getr R (reg 2) = Z_to_bv 64 (Q - 352)). { replace (Q - 352) with spd by (unfold Q, spd; clear; lia). exact H2. }
  assert (WQ: 0 <= Q < 2 ^ 64) by (unfold Q; flia). assert (WXr: 0 <= X < 2 ^ 64) by (unfold X; flia). assert (W1: 0 <= 1 < 2 ^ 64) by (clear; lia).
  assert (Wfx: 0 <= fbx < 2 ^ 64) by (clear - Xfr; lia). assert (Wfd: 0 <= fden0 < 2 ^ 64) by (clear - Dfr; lia).
  assert (QR: 1048928 <= Q <= 140737488355328) by (unfold Q; flia). assert (XR: 1048576 <= X <= 140737488355296) by (unfold X; flia).
  assert (APX: Q - 352 + 352 <= X \/ X + 32 <= Q - 352) by (left; unfold Q, X; clear; lia).
  assert (Bfd: 0 <= fden0 <= 255) by (clear - Dfr; lia). assert (Bfx: 0 <= fbx <= 255) by (clear - Xfr; lia).
  assert (Dl': L5.u64_at RSEGS M (Q - 128) (Z.of_nat (L5.bo_len bb))) by exactA Dl.
  assert (NBLE: Z.of_nat (L5.bo_len bb) <= 268).
  { pose proof CAPB1 as CB. unfold capb, L5.bo_cap in CB. pose proof BOK as (OB0 & _). unfold L5.big_at in OB0.
    destruct (L5.bo_st bb) as [u0 u1|c q]. destruct OB0 as (_ & _ & _ & _ & _ & _ & Hl & _). clear - Hl; lia.
    destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & _). clear - Hlc CB; lia. }
  assert (CEIL: hl_ceil L <= S - SCR_OPMOD). { unfold hl_ceil. rewrite SCR_OPMOD_val. clear - SLO'. lia. }
  assert (LBceil: forall b, In b LB -> fst b + snd b <= hl_ceil L).
  { intros [A n] Hb. pose proof (LBdef _ _ _ _ HH0 A n Hb) as (_ & _ & Ahi & _). unfold hl_ceil. cbn. exact Ahi. }
  (* [comment removed for export] *)
  assert (VIEW: forall M1, mem_grows M M1 -> (forall i, 0 <= i < 2 ^ 64 -> ~ (Q - 152 <= i < Q - 152 + 16) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
             (forall a, 0 <= a < 2 ^ 64 -> ~ (Q - 152 <= a < Q - 136) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
             /\ hi_heap HI LBc crc M1 (m_vmmaps model)
             /\ L5C.hpres L LB S SCR_OPMOD [] M0 M1
             /\ L5.img_clear M1 0x10000 0x20000
             /\ L5.defined M1 (S - 10240) 10240).
  { intros M1 MG1 FR1.
    assert (KFR: forall a, 0 <= a < 2 ^ 64 -> ~ (Q - 152 <= a < Q - 136) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hn. apply FR1. exact Ha. clear - Hn; lia. }
    split. exact KFR.
    split. { eapply (hi_heap_stackwrite LBc crc M M1 _ (Q - 152) (Q - 136)). exact HH. exact KFR. unfold Q; flia. unfold Q; flia. flia. exact MG1. }
    split. { eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [] M0 M M1 S SCR_OPMOD []). exact HP.
             - eapply (L5HP.hpres_piece L LB S SCR_OPMOD [] M M1 (fun a => Q - 152 <= a < Q - 136)). exact KFR.
               { intros a KA' C. apply (L5HP.kept_not_in_scratch _ _ _ _ _ _ KA' LBceil CEIL ltac:(unfold hl_ceil; rewrite IMG'; clear - SPT; lia)). rewrite SCR_OPMOD_val. unfold Q in C. clear - C; lia. }
               rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG1. exact SCR. exact MG1.
             - intros a KA'; exact KA'. - intros b Hb; exact Hb. - exact CEIL. - flia. - rewrite SCR_OPMOD_val; clear; lia. - rewrite EV; clear; lia. - flia. }
    split. { intros i Hi. rewrite KFR. apply IC. exact Hi. clear - Hi; lia. unfold Q; clear - Hi SLO; lia. }
    eapply L5.defined_grows. exact MG1. exact SCR. }
  destruct (Nat.eq_dec (L5.bo_len bb) 0) as [NB0|NBnz].
  - (* [comment removed for export] *)
    assert (STI: exists v0 v1, std = L5.BInl v0 v1).
    { destruct std as [v0 v1|cq p]. eexists _, _; reflexivity. exfalso. destruct (SDYN cq p eq_refl) as (_ & _ & DY). pose proof (DYN3 DY) as L3. clear - L3 NB0. lia. }
    destruct STI as (v0 & v1 & ->). destruct (SINL v0 v1 eq_refl) as [STB ->]. rewrite ELB in HH. cbn [blocks_ofst app] in HH.
    destruct DST as (Db0 & D16 & D24 & _ & Rv0 & Rv1). rewrite NB0 in Dl'. cbn [Z.of_nat] in Dl'.
    pose proof (d6ue2z_conc fx R M (VO Q X bo fbx 0 0 fden0 0 0 0)) as P. cbn [VO] in P.
    destruct (P WQ WXr WQ WXr W1 Wfd E2 H8 H9 H18 H23 QR AQ16 WF Df Dl' Bfd Db0) as (fx1 & R1 & M1 & MG1 & _ & FR1 & (MS1 & K1 & A10 & A11 & A19 & A22 & C144 & C152)). clear P.
    rewrite ELB in VIEW. cbn [blocks_ofst app] in VIEW. destruct (VIEW M1 MG1 FR1) as (KFR & HH1 & HP1 & IC1 & SCR1).
    unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
    pose proof DER as (RD1 & RD8 & RDS).
    pose proof (div_saves_o1_saves M S R0 Rd ltac:(flia) DER DS) as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
    pose proof TF as (T1 & T8 & T3 & T4). pose proof ZQ as ZQ'. unfold zero_obj, L5.big_at in ZQ'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in ZQ'. destruct ZQ' as (Z0 & _ & Z8 & _ & Z16 & Z24 & _).
    assert (KU: forall a v, L5.u64_at RSEGS M a v -> Q - 136 <= a -> a + 8 <= S -> L5.u64_at RSEGS M1 a v).
    { intros a v U Ha Hb. eapply u64_at_agree1. 4: exact U. intros i Hi; apply KFR; unfold Q in *; flia. unfold Q in Ha; flia. flia. }
    apply (KZ fx1 R1 M1 model). 2: exact MBV. 2: exact HH1. 2:{ rewrite SCR_OPMOD_val. exact SCR1. }
    2:{ eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KFR; subst bo; unfold Q; flia. subst bo; flia. subst bo; flia. }
    2:{ eapply obj_limbs_agree1. 3: exact OLB. intros cap q E; rewrite STB in E; discriminate E. intros cap q E; rewrite STB in E; discriminate E. }
    2:{ split. 2: exact NEGX. eapply big_at_agree1. 4: exact OBX. intros i Hi; apply KFR; unfold Q, X in *; flia. unfold X; flia. unfold X; flia. }
    exists fden0, v0, v1.
    split. { etransitivity. exact (K1 2%nat ltac:(inl)). rewrite H2. unfold spd. reflexivity. }
    split. { etransitivity. exact (K1 3%nat ltac:(inl)). rewrite H3. symmetry. exact G3. } split. { etransitivity. exact (K1 4%nat ltac:(inl)). rewrite H4. symmetry. exact G4. }
    split. kreg K1 8%nat H8. split. kreg K1 9%nat H9. split. exact A10. split. kreg K1 18%nat H18. split. exact A19.
    split. kreg K1 20%nat H20. split. kreg K1 21%nat H21.
    split. { replace (S - 184) with (Q - 120) by (unfold Q; clear; lia). exact A22. }
    split. kreg K1 23%nat H23. split. kreg K1 24%nat H24. split. kreg K1 25%nat H25. split. kreg K1 26%nat H26. split. kreg K1 27%nat H27.
    split. apply KU; [exact T1 | unfold Q; clear; lia | clear; lia]. split. apply KU; [exact T8 | unfold Q; clear; lia | clear; lia].
    split. apply KU; [exact T3 | unfold Q; clear; lia | clear; lia]. split. apply KU; [exactA T4 | unfold Q; clear; lia | clear; lia].
    split. { eapply u8_at_agree1. 4: exactA Z0. intros i Hi; apply KFR; unfold Q in *; flia. flia. flia. }
    split. apply KU; [exactA Z8 | unfold Q; clear; lia | clear; lia]. split. apply KU; [exactA Z16 | unfold Q; clear; lia | clear; lia]. split. apply KU; [exactA Z24 | unfold Q; clear; lia | clear; lia].
    split. apply KU; [exactA V1 | unfold Q; clear; lia | clear; lia]. split. apply KU; [exactA V2 | unfold Q; clear; lia | clear; lia].
    split. apply KU; [exactA V3 | unfold Q; clear; lia | clear; lia]. split. apply KU; [exactA V4 | unfold Q; clear; lia | clear; lia].
    split. apply KU; [exactA V5 | unfold Q; clear; lia | clear; lia]. split. apply KU; [exactA V6 | unfold Q; clear; lia | clear; lia].
    split. apply KU; [exactA V7 | unfold Q; clear; lia | clear; lia]. split. apply KU; [exactA V8 | unfold Q; clear; lia | clear; lia].
    split. apply KU; [exactA V9 | unfold Q; clear; lia | clear; lia]. split. apply KU; [exactA V10 | unfold Q; clear; lia | clear; lia].
    split. apply KU; [exactA V11 | unfold Q; clear; lia | clear; lia]. split. apply KU; [exactA V12 | unfold Q; clear; lia | clear; lia].
    split. apply KU; [exactA V13 | unfold Q; clear; lia | clear; lia].
    split. { eapply u8_at_agree1. 4: exactA Df. intros i Hi; apply KFR; unfold Q in *; flia. flia. flia. } split. exact Dfr. split. exact Db0.
    split. apply KU; [exactA Dl' | unfold Q; clear; lia | clear; lia]. split. apply KU; [exactA D16 | unfold Q; clear; lia | clear; lia]. split. apply KU; [exactA D24 | unfold Q; clear; lia | clear; lia].
    split. { replace (S - 216) with (Q - 152) by (unfold Q; clear; lia). replace (S - 184) with (Q - 120) by (unfold Q; clear; lia). exact C152. }
    split. { replace (S - 208) with (Q - 144) by (unfold Q; clear; lia). exact C144. }
    exact HP1.
  - (* [comment removed for export] *)
    assert (NBR: 1 <= Z.of_nat (L5.bo_len bb) <= 300) by (clear - NBnz NBLE; lia).
    (* [comment removed for export] *)
    assert (STEP: exists (fx1 : FPState) R1 M1, msteps RSEGS (st fx R 0x22548 M) (st fx1 R1 0x23208 M1)
              /\ (forall x, In x [2; 3; 4; 8; 9; 18; 21; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
              /\ getr R1 (reg 1) = Z_to_bv 64 140676 /\ getr R1 (reg 10) = Z_to_bv 64 (Q - 184)
              /\ getr R1 (reg 11) = Z_to_bv 64 X /\ getr R1 (reg 19) = Z_to_bv 64 fden0 /\ getr R1 (reg 20) = Z_to_bv 64 fbx /\ getr R1 (reg 22) = Z_to_bv 64 (Q - 120)
              /\ mem_grows M M1 /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (Q - 152 <= i < Q - 152 + 16) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
              /\ L5.u64_at RSEGS M1 (Q - 144) (Z.of_nat (L5.bo_len bb))
              /\ L5.u64_at RSEGS M1 (Q - 152) (L5.bo_data (Q - 136) (L5.BO fden0 (L5.bo_len bb) std))).
    { destruct std as [v0 v1|cq p].
      + destruct DST as (Db0 & _).
        pose proof (d6ue2_conc fx R M (VO Q X bo fbx 0 0 fden0 (Z.of_nat (L5.bo_len bb)) 0 0)) as P. cbn [VO] in P.
        destruct (P WQ WXr WQ WXr W1 Wfx Wfd ltac:(clear - NBR; lia) E2 H8 H9 H18 H23 QR AQ16 WF Df Dl' Bfd Db0 NBR XR AX8 APX Xf Bfx)
          as (fx1 & R1 & M1 & MG1 & _ & FR1 & (MS1 & K1 & A1' & A10 & A11 & A12 & A19 & A20 & A22 & C144 & C152)). clear P.
        exists fx1, R1, M1. split. exact MS1.
        split. { intros x Hx. apply K1. revert Hx. apply (L5K.incl_b _ KS_d6ue2). vm_compute. reflexivity. }
        cbn [L5.bo_data L5.bo_st]. replace (Q - 136 + 16) with (Q - 120) by (clear; lia). repeat split; assumption.
      + destruct DST as (Db1 & D16 & D24 & Hlc & Hcap & _ & Plo & Phi & _).
        pose proof (d6ue2d_conc fx R M (VO Q X bo fbx 0 0 fden0 (Z.of_nat (L5.bo_len bb)) p 0)) as P. cbn [VO] in P.
        destruct (P WQ WXr WQ WXr W1 Wfx Wfd ltac:(clear - NBR; lia) ltac:(clear - Plo Phi Hcap; lia) E2 H8 H9 H18 H23 QR AQ16 WF Df Dl' ltac:(exactA D24) Bfd Db1 NBR
                    ltac:(clear - Plo Phi Hcap; lia) XR AX8 APX Xf Bfx)
          as (fx1 & R1 & M1 & MG1 & _ & FR1 & (MS1 & K1 & A1' & A10 & A11 & A12 & A19 & A20 & A22 & C144 & C152)). clear P.
        exists fx1, R1, M1. split. exact MS1.
        split. { intros x Hx. apply K1. revert Hx. apply (L5K.incl_b _ KS_d6ue2d). vm_compute. reflexivity. }
        cbn [L5.bo_data L5.bo_st]. repeat split; assumption. }
    destruct STEP as (fx1 & R1 & M1 & MS1 & K1 & A1' & A10 & A11 & A19 & A20 & A22 & MG1 & FR1 & VS1 & VD1).
    destruct (VIEW M1 MG1 FR1) as (KFR & HH1 & HP1 & IC1 & SCR1).
    pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP1) as SCR1'. rewrite SCR_OPMOD_val in SCR1'.
    assert (KU: forall a v, L5.u64_at RSEGS M a v -> Q - 136 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M1 a v).
    { intros a v U Ha Hb. eapply u64_at_agree1. 4: exact U. intros i Hi; apply KFR; unfold Q in *; flia. unfold Q in Ha; flia. exact Hb. }
    assert (OBX1: L5.big_at RSEGS M1 X (L5.BO fbx 2 (L5.BInl A0 A1))). { eapply big_at_agree1. 4: exact OBX. intros i Hi; apply KFR; unfold Q, X in *; flia. unfold X; flia. unfold X; flia. }
    assert (OD1: L5.big_at RSEGS M1 (Q - 136) (L5.BO fden0 (L5.bo_len bb) std)). { eapply big_at_agree1. 4: exact OD. intros i Hi; apply KFR; unfold Q in *; flia. unfold Q; flia. unfold Q; flia. }
    assert (OLD1': L5C.obj_limbs RSEGS M1 (L5.BO fden0 (L5.bo_len bb) std) wb).
    { eapply obj_limbs_agree1. 3: exact OLD.
      -- cbn [L5.bo_st L5.bo_len]. intros cq p E i Hi. subst std. destruct (SDYN cq p eq_refl) as (-> & FB & _).
         pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB) as (Plo & _ & _ & _ & Phi). unfold hl_ceil in Phi. pose proof OLD as (Ln & _). cbn [L5.bo_len] in Ln. rewrite Ln in Hi.
         pose proof CAPB1 as CB. destruct DST as (_ & _ & _ & Hlc & _).
         apply KFR. clear - Hi Plo Phi Hlc CB SPT; lia. unfold Q; clear - Hi Phi Hlc SLO'; lia.
      -- cbn [L5.bo_st L5.bo_len]. intros cq p E. subst std. destruct (SDYN cq p eq_refl) as (-> & FB & _).
         pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB) as (Plo & _ & _ & _ & Phi). unfold hl_ceil in Phi. pose proof OLD as (Ln & _). cbn [L5.bo_len] in Ln. rewrite Ln.
         destruct DST as (_ & _ & _ & Hlc & _). clear - Plo Phi Hlc SPT; lia. }
    assert (OBB1: L5.big_at RSEGS M1 bo bb). { eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KFR; subst bo; unfold Q; flia. subst bo; flia. subst bo; flia. }
    assert (OLB1: L5C.obj_limbs RSEGS M1 bb wb).
    { pose proof BOK as (OB0 & _ & _ & BST). eapply obj_limbs_agree1. 3: exact OLB.
      -- intros cap q E i Hi. rewrite E in BST. destruct BST as [INB _]. pose proof OLB as (Ln & _ & _).
         unfold L5.big_at in OB0. rewrite E in OB0. destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _).
         pose proof (LBdef _ _ _ _ HH0 q (8 * cap) INB) as (_ & _ & Ahi & _).
         apply KFR. rewrite Ln in Hi; clear - Hi Hlc Qlo Qhi; lia. unfold Q; rewrite Ln in Hi; clear - Hi Hlc Ahi SLO'; lia.
      -- intros cap q E. pose proof OLB as (Ln & _ & _). unfold L5.big_at in OB0. rewrite E in OB0.
         destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite Ln. clear - Hlc Hcap Qlo Qhi. lia. }
    pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK'.
    destruct (defined_byte M1 (Q - 184) ltac:(eapply L5.defined_sub; [exact SCR1' | unfold Q; clear; lia | unfold Q; clear; lia]) ltac:(unfold Q; flia) ltac:(unfold Q; flia)) as (fno & Fno & Uno).
    unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
    (* [comment removed for export] *)
    eapply (COPYA fx1 R1 M1 model K LBc crc (Q - 184) X (Q - 352) 0x22584 fno (L5.BO fbx 2 (L5.BInl A0 A1)) [A0; A1] HH1 MOK HK0 A10 A11).
    + unfold L5.bo_dyn. cbn [L5.bo_fb]. rewrite Xb0. intros F; discriminate F.
    + exact A1'.
    + split. clear; lia. reflexivity.
    + kreg K1 2%nat E2.
    + kreg K1 4%nat H4.
    + split. { unfold Q. replace (S - 64 - 352) with (S + (-26) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
      split. unfold Q; fsclia. split. unfold Q; flia. split. exact SPT. unfold Q. rewrite COPY_SCR_val. eapply L5.defined_sub. exact SCR1'. clear; lia. clear; lia.
    + exact Uno. + exact Fno.
    + unfold Q. replace (S - 64 - 184) with (S + 8 * (-31)) by (clear; lia). apply al8. exact A16.
    + unfold Q; clear; lia. + unfold Q; flia.
    + apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR1'. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; flia. unfold Q; flia.
    + exact OBX1. + apply obj_limbs_x. + exact AX8. + unfold Q, X; clear; lia. + unfold X; flia.
    + cbn. intros cap q E; discriminate E.
    + left. unfold Q, X; clear; lia.
    + (* [comment removed for export] *)
      intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
      destruct POST as (RP2 & GP). destruct g as [|A cap].
      2:{ exfalso. destruct GP as (F & _). unfold L5.bo_dyn in F. cbn [L5.bo_fb] in F. rewrite Xb0 in F. discriminate F. }
      destruct GP as (_ & -> & -> & ON2 & FR2 & MG2). cbn [L5.bo_fb L5.bo_len L5.bo_st] in ON2.
      pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2.
      assert (KA2: forall a, 0 <= a < 2 ^ 64 -> ~ (Q - 184 <= a < Q - 184 + 32) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha Hn. apply FR2. apply outside1. rewrite BG.unsigned_lit by exact Ha. exact Hn. }
      apply (stage_E3 fx2 R2 Rd M2 model2 LBc crc (copy_fb fno fbx false) fden0 std);
        try (rewrite (preserved_sregs R1 R2 _ RP2) by inl); try (rewrite K1 by inl); try assumption.
      * unfold copy_fb. rewrite !Z.lor_spec, !Z.land_spec, NEGX. cbn. rewrite Bool.andb_false_r. reflexivity.
      * exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
      * intros cq p E. destruct (SDYN cq p E) as (A & (BR & BA & BD) & C). split. exact A. split. 2: exact C. split. exact BR. split. exact BA.
        eapply L5.defined_grows. exact MG2. eapply L5.defined_grows. exact MG1. exact BD.
      * eapply div_saves_kept. 4: exact DS. intros i Hi. rewrite KA2. apply KFR. unfold Q in *; flia. unfold Q in *; flia. unfold Q in *; flia. unfold Q in *; flia. unfold Q; flia. unfold Q; flia.
      * eapply top_frame_kept. 4: exact TF. intros i Hi. rewrite KA2. apply KFR. unfold Q in *; flia. unfold Q in *; flia. unfold Q in *; flia. unfold Q in *; flia. flia. flia.
      * eapply big_at_agree1. 4: exact ZQ. intros i Hi. rewrite KA2. apply KFR. unfold Q in *; flia. unfold Q in *; flia. unfold Q in *; flia. unfold Q in *; flia. unfold Q; flia. unfold Q; flia.
      * split. 2: exact NEGX. eapply big_at_agree1. 4: exact OBX1. intros i Hi; apply KA2; unfold Q, X in *; flia. unfold X; flia. unfold X; flia.
      * eapply L5.defined_grows. exact MG2. eapply L5.defined_grows. exact MG1. exact DX.
      * eapply big_at_agree1. 4: exact OD1. intros i Hi; apply KA2; unfold Q in *; flia. unfold Q; flia. unfold Q; flia.
      * eapply obj_limbs_agree1. 3: exact OLD1'.
        -- cbn [L5.bo_st L5.bo_len]. intros cq p E i Hi. subst std. destruct (SDYN cq p eq_refl) as (-> & FB & _).
           pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB) as (Plo & _ & _ & _ & Phi). unfold hl_ceil in Phi. pose proof OLD as (Ln & _). cbn [L5.bo_len] in Ln. rewrite Ln in Hi.
           pose proof CAPB1 as CB. destruct DST as (_ & _ & _ & Hlc & _).
           apply KA2. clear - Hi Plo Phi Hlc CB SPT; lia. unfold Q; clear - Hi Phi Hlc SLO'; lia.
        -- cbn [L5.bo_st L5.bo_len]. intros cq p E. subst std. destruct (SDYN cq p eq_refl) as (-> & FB & _).
           pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB) as (Plo & _ & _ & _ & Phi). unfold hl_ceil in Phi. pose proof OLD as (Ln & _). cbn [L5.bo_len] in Ln. rewrite Ln.
           destruct DST as (_ & _ & _ & Hlc & _). clear - Plo Phi Hlc SPT; lia.
      * eapply u64_at_agree1. 4: exact VD1. intros i Hi; apply KA2; unfold Q in *; flia. unfold Q; flia. unfold Q; flia.
      * eapply u64_at_agree1. 4: exact VS1. intros i Hi; apply KA2; unfold Q in *; flia. unfold Q; flia. unfold Q; flia.
      * clear - NBnz; lia.
      * eapply big_at_agree1. 4: exact OBB1. intros i Hi; apply KA2; subst bo; unfold Q; flia. subst bo; flia. subst bo; flia.
      * pose proof BOK as (OB0 & _ & _ & BST). eapply obj_limbs_agree1. 3: exact OLB1.
        -- intros cap q E i Hi. rewrite E in BST. destruct BST as [INB _]. pose proof OLB as (Ln & _ & _).
           unfold L5.big_at in OB0. rewrite E in OB0. destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _).
           pose proof (LBdef _ _ _ _ HH0 q (8 * cap) INB) as (_ & _ & Ahi & _).
           apply KA2. rewrite Ln in Hi; clear - Hi Hlc Qlo Qhi; lia. unfold Q; rewrite Ln in Hi; clear - Hi Hlc Ahi SLO'; lia.
        -- intros cap q E. pose proof OLB as (Ln & _ & _). unfold L5.big_at in OB0. rewrite E in OB0.
           destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite Ln. clear - Hlc Hcap Qlo Qhi. lia.
      * eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [] M0 M1 M2 S SCR_OPMOD []). exact HP1.
        -- eapply (L5HP.hpres_piece L LB S SCR_OPMOD [] M1 M2 (fun a => Q - 184 <= a < Q - 184 + 32)). exact KA2.
           { intros a KA' C. apply (L5HP.kept_not_in_scratch _ _ _ _ _ _ KA' LBceil CEIL ltac:(unfold hl_ceil; rewrite IMG'; clear - SPT; lia)). rewrite SCR_OPMOD_val. unfold Q in C. clear - C; lia. }
           rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG2. exact SCR1. exact MG2.
        -- intros a KA'; exact KA'. -- intros b Hb; exact Hb. -- exact CEIL. -- flia.
        -- rewrite SCR_OPMOD_val; clear; lia. -- rewrite EV; clear; lia. -- flia.
      * intros i Hi. rewrite KA2. apply IC1. exact Hi. clear - Hi; lia. unfold Q; clear - Hi SLO; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_E1 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) :
  getr R (reg 1) = Z_to_bv 64 DIV_RET -> getr R (reg 2) = Z_to_bv 64 Q -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 10) = Z_to_bv 64 X -> getr R (reg 11) = Z_to_bv 64 bo -> getr R (reg 12) = Z_to_bv 64 Q ->
  getr R (reg 13) = Z_to_bv 64 X -> getr R (reg 14) = Z_to_bv 64 1 ->
  (forall i, In i [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg i) = getr R0 (reg i)) ->
  model_but_vm model0 model -> hi_heap HI LB cr M (m_vmmaps model) ->
  top_frame M S R0 -> zero_obj M Q -> x_is_a M X fbx -> L5.defined M X 32 -> L5.big_at RSEGS M bo bb -> L5C.obj_limbs RSEGS M bb wb ->
  L5C.hpres L LB S SCR_OPMOD [] M0 M -> L5.img_clear M 0x10000 0x20000 ->
  srealizes RSEGS SCFG (cfg R DIVIDE M model) K.
Proof.
  intros H1 H2 H3 H4 H8 H10 H11 H12 H13 H14 HRS MBV HH TF ZQ XA' DX OBB OLB HP IC.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP) as SCR. rewrite SCR_OPMOD_val in SCR. pose proof ERRNOV as EV. pose proof IMG as IMG'. pose proof CAPB1 as CB.
  pose proof XA' as [OBX NEGX]. pose proof BOK as (OB0 & _ & _ & BST).
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  (* [comment removed for export] *)
  pose proof (d5ue1_conc fx R M (VO Q X bo fbx 0 0 0 0 0 0)) as P. cbn [VO] in P.
  destruct (P ltac:(unfold Q; flia) ltac:(unfold X; flia) ltac:(subst bo; flia) ltac:(unfold Q; flia) ltac:(unfold X; flia) ltac:(clear; lia) H2 H10 H11 H12 H13 H14 ltac:(unfold Q; flia) AQ16
              ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR | unfold Q; clear; lia | unfold Q; clear; lia] | unfold Q; flia | unfold Q; flia]))
    as (fx1 & R1 & M1 & MG1 & _ & FR1 & (MS1 & K1 & A1 & A2 & A8 & A9 & A10 & A12 & A18 & A23 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)). clear P.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  assert (KA1: forall a, 0 <= a < 2 ^ 64 -> ~ (Q - 352 <= a < Q - 352 + 352) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) by exact FR1.
  assert (DER: div_entry_regs S R0 R). { split. exact H1. split. exact H8. exact HRS. }
  assert (DS1: div_saves M1 Q R). { unfold div_saves, U. repeat split; assumption. }
  assert (HH1: hi_heap HI LB cr M1 (m_vmmaps model)).
  { eapply (hi_heap_stackwrite LB cr M M1 _ (Q - 352) (Q - 352 + 352)). exact HH. exact KA1. unfold Q; flia. unfold Q; flia. flia. exact MG1. }
  destruct (defined_byte M1 (Q - 136) ltac:(eapply L5.defined_grows; [exact MG1|]; eapply L5.defined_sub; [exact SCR | unfold Q; clear; lia | unfold Q; clear; lia]) ltac:(unfold Q; flia) ltac:(unfold Q; flia)) as (fdo & Fdo & Udo).
  assert (OBB1: L5.big_at RSEGS M1 bo bb). { eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KA1; subst bo; unfold Q; flia. subst bo; flia. subst bo; flia. }
  assert (OLB1: L5C.obj_limbs RSEGS M1 bb wb).
  { eapply obj_limbs_agree1. 3: exact OLB.
    - intros cap q E i Hi. rewrite E in BST. destruct BST as [INB _]. pose proof OLB as (Ln & _ & _).
      unfold L5.big_at in OB0. rewrite E in OB0. destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _).
      pose proof (LBdef _ _ _ _ HH0 q (8 * cap) INB) as (_ & _ & Ahi & _).
      apply KA1. rewrite Ln in Hi; clear - Hi Hlc Qlo Qhi; lia. unfold Q; rewrite Ln in Hi; clear - Hi Hlc Ahi SLO'; lia.
    - intros cap q E. pose proof OLB as (Ln & _ & _). unfold L5.big_at in OB0. rewrite E in OB0.
      destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite Ln. clear - Hlc Hcap Qlo Qhi. lia. }
  (* [comment removed for export] *)
  eapply (COPYA fx1 R1 M1 model K LB cr (Q - 136) bo (Q - 352) 0x22548 fdo bb wb HH1 MOK HK0 A10 ltac:(kreg K1 11%nat H11)).
  - intros DY. split. unfold capb in CB; clear - CB; lia. pose proof CR as [C1 C2]. unfold credit_ok, OPMOD1_K, opmod1_bytes in *. pose proof KPOS. pose proof BPOS.
    unfold capb in *. split; clear - C1 C2 H H0 CB; lia.
  - exact A1.
  - split. clear; lia. reflexivity.
  - exact A2.
  - kreg K1 4%nat H4.
  - split. { unfold Q. replace (S - 64 - 352) with (S + (-26) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. unfold Q; fsclia. split. unfold Q; flia. split. exact SPT. unfold Q. rewrite COPY_SCR_val. eapply L5.defined_grows. exact MG1. eapply L5.defined_sub. exact SCR. clear; lia. clear; lia.
  - exact Udo. - exact Fdo.
  - unfold Q. replace (S - 64 - 136) with (S + 8 * (-25)) by (clear; lia). apply al8. exact A16.
  - unfold Q; clear; lia. - unfold Q; flia.
  - apply (L5C.writable_of_defined RSEGS). eapply L5.defined_grows. exact MG1. eapply L5.defined_sub. exact SCR. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; flia. unfold Q; flia.
  - exact OBB1. - exact OLB1.
  - subst bo. rewrite <- Zplus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - subst bo; unfold Q; clear; lia. - subst bo; flia.
  - intros cap q E. rewrite E in BST. exact (proj1 BST).
  - left. subst bo; unfold Q; clear; lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2. destruct POST as (RP2 & GP).
    assert (X1: x_is_a M1 X fbx). { split. 2: exact NEGX. eapply big_at_agree1. 4: exact OBX. intros i Hi; apply KA1; unfold Q, X in *; flia. unfold X; flia. unfold X; flia. }
    assert (TF1: top_frame M1 S R0). { eapply top_frame_kept. 4: exact TF. intros i Hi; apply KA1; unfold Q in *; flia. flia. flia. }
    assert (ZQ1: zero_obj M1 Q). { eapply big_at_agree1. 4: exact ZQ. intros i Hi; apply KA1; unfold Q in *; flia. unfold Q; flia. unfold Q; flia. }
    assert (DX1: L5.defined M1 X 32). { eapply L5.defined_grows. exact MG1. exact DX. }
    assert (IC1: L5.img_clear M1 0x10000 0x20000). { intros i Hi. rewrite KA1. apply IC. exact Hi. clear - Hi; lia. unfold Q; clear - Hi SLO; lia. }
    assert (CEIL: hl_ceil L <= S - SCR_OPMOD). { unfold hl_ceil. rewrite SCR_OPMOD_val. clear - SLO'. lia. }
    assert (LBceil: forall b, In b LB -> fst b + snd b <= hl_ceil L).
    { intros [A n] Hb. pose proof (LBdef _ _ _ _ HH0 A n Hb) as (_ & _ & Ahi & _). unfold hl_ceil. cbn. exact Ahi. }
    assert (HP1: L5C.hpres L LB S SCR_OPMOD [] M0 M1).
    { eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [] M0 M M1 S SCR_OPMOD []). exact HP.
      - eapply (L5HP.hpres_piece L LB S SCR_OPMOD [] M M1 (fun a => Q - 352 <= a < Q - 352 + 352)). exact KA1.
        { intros a KA' C. apply (L5HP.kept_not_in_scratch _ _ _ _ _ _ KA' LBceil CEIL ltac:(unfold hl_ceil; rewrite IMG'; clear - SPT; lia)). rewrite SCR_OPMOD_val. unfold Q in C. clear - C; lia. }
        rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG1. exact SCR. exact MG1.
      - intros a KA'; exact KA'. - intros b Hb; exact Hb. - exact CEIL. - flia. - rewrite SCR_OPMOD_val; clear; lia. - rewrite EV; clear; lia. - flia. }
    (* [comment removed for export] *)
    assert (E2r: forall i v, In i cs_all -> getr R1 (reg i) = v -> getr R2 (reg i) = v). { intros i v Hi Hv. rewrite (preserved_sregs R1 R2 i RP2) by exact Hi. exact Hv. }
    destruct g as [|A cap].
    + (* [comment removed for export] *)
      destruct GP as (DYF & -> & -> & OD2 & FR2 & MG2).
      assert (KA2: forall a, 0 <= a < 2 ^ 64 -> ~ (Q - 136 <= a < Q - 136 + 32) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha Hn. apply FR2. apply outside1. rewrite BG.unsigned_lit by exact Ha. exact Hn. }
      assert (STI: exists v0 v1, L5.bo_st bb = L5.BInl v0 v1).
      { unfold L5.bo_dyn in DYF. unfold L5.big_at in OB0. destruct (L5.bo_st bb) as [v0 v1|c q]. eexists _, _; reflexivity.
        destruct OB0 as (_ & _ & _ & T & _). rewrite T in DYF. discriminate DYF. }
      destruct STI as (v0 & v1 & STB). rewrite STB in OD2.
      apply (stage_E2 fx2 R2 R M2 model2 LB cr (copy_fb fdo (L5.bo_fb bb) false) (L5.BInl v0 v1)).
      * apply (E2r 2%nat). inl. rewrite A2. unfold Q, spd. f_equal. clear; lia.
      * apply (E2r 3%nat). inl. rewrite (K1 3%nat) by inl. exact H3.
      * apply (E2r 4%nat). inl. rewrite (K1 4%nat) by inl. exact H4.
      * apply (E2r 8%nat). inl. exact A8.
      * apply (E2r 9%nat). inl. exact A9.
      * apply (E2r 18%nat). inl. exact A18.
      * apply (E2r 23%nat). inl. exact A23.
      * apply (E2r 20%nat). inl. rewrite (K1 20%nat) by inl. apply HRS. inl.
      * apply (E2r 21%nat). inl. rewrite (K1 21%nat) by inl. apply HRS. inl.
      * apply (E2r 24%nat). inl. rewrite (K1 24%nat) by inl. apply HRS. inl.
      * apply (E2r 25%nat). inl. rewrite (K1 25%nat) by inl. apply HRS. inl.
      * apply (E2r 26%nat). inl. rewrite (K1 26%nat) by inl. apply HRS. inl.
      * apply (E2r 27%nat). inl. rewrite (K1 27%nat) by inl. apply HRS. inl.
      * unfold copy_fb. rewrite !Z.lor_spec, !Z.land_spec. cbn. rewrite Bool.andb_false_r, Bool.andb_true_r. reflexivity.
      * exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
      * exact HH2.
      * reflexivity.
      * unfold credit_after, OPMOD1_K, opmod1_bytes. pose proof KPOS. pose proof BPOS. split; clear - H H0 CB; unfold capb in *; lia.
      * intros cq p E. discriminate E.
      * intros u0 u1 E. injection E. intros <- <-. split. exact STB. reflexivity.
      * exact DER.
      * eapply div_saves_kept. 4: exact DS1. intros i Hi; apply KA2; unfold Q in *; flia. unfold Q; flia. unfold Q; flia.
      * eapply top_frame_kept. 4: exact TF1. intros i Hi; apply KA2; unfold Q in *; flia. flia. flia.
      * eapply big_at_agree1. 4: exact ZQ1. intros i Hi; apply KA2; unfold Q in *; flia. unfold Q; flia. unfold Q; flia.
      * destruct X1 as [OBX1 _]. split. 2: exact NEGX. eapply big_at_agree1. 4: exact OBX1. intros i Hi; apply KA2; unfold Q, X in *; flia. unfold X; flia. unfold X; flia.
      * eapply L5.defined_grows. exact MG2. exact DX1.
      * exact OD2.
      * pose proof OLB1 as (Ln & Fw & LA). rewrite STB in LA. split. exact Ln. split. exact Fw. exact LA.
      * eapply big_at_agree1. 4: exact OBB1. intros i Hi; apply KA2; subst bo; unfold Q; flia. subst bo; flia. subst bo; flia.
      * eapply obj_limbs_agree1. 3: exact OLB1. intros cap q E; rewrite STB in E; discriminate E. intros cap q E; rewrite STB in E; discriminate E.
      * eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [] M0 M1 M2 S SCR_OPMOD []). exact HP1.
        -- eapply (L5HP.hpres_piece L LB S SCR_OPMOD [] M1 M2 (fun a => Q - 136 <= a < Q - 136 + 32)). exact KA2.
           { intros a KA' C. apply (L5HP.kept_not_in_scratch _ _ _ _ _ _ KA' LBceil CEIL ltac:(unfold hl_ceil; rewrite IMG'; clear - SPT; lia)). rewrite SCR_OPMOD_val. unfold Q in C. clear - C; lia. }
           rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG2. exact (L5C.hpres_defined _ _ _ _ _ _ _ HP1). exact MG2.
        -- intros a KA'; exact KA'. -- intros b Hb; exact Hb. -- exact CEIL. -- flia. -- rewrite SCR_OPMOD_val; clear; lia. -- rewrite EV; clear; lia. -- flia.
      * intros i Hi. rewrite KA2. apply IC1. exact Hi. clear - Hi; lia. unfold Q; clear - Hi SLO; lia.
    + (* [comment removed for export] *)
      destruct GP as (DYT & -> & -> & -> & FB & OD2 & OL2 & HP2). cbn [L5.bo_fb L5.bo_len] in OD2, OL2.
      assert (KA2: forall a, Q - 352 <= a < 2 ^ 64 -> ~ (Q - 136 <= a < Q - 136 + 32) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha Hn. apply (kept_above M1 M2 LB (Q - 352) COPY_SCR _ a HP2). unfold Q; fsclia. rewrite COPY_SCR_val; clear; lia. flia. exact Ha. apply outside1. exact Hn. }
      assert (KB2: forall A' n a, In (A', n) LB -> A' <= a < A' + n -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros A' n a Hin Ha. pose proof (LBdef _ _ _ _ HH1 A' n Hin) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG', IMGLO in Aimg.
        apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). eapply L5C.kept_block. exact Hin. exact Ha. clear - Alo; lia. clear - Ahi SPT; lia.
        rewrite EV; clear - Aimg Ha; lia. apply outside1. unfold Q; clear - Ha Ahi SLO'; lia. }
      apply (stage_E2 fx2 R2 R M2 model2 ((A, 8 * capb) :: LB) (debit L cr (8 * capb)) (copy_fb fdo (L5.bo_fb bb) true) (L5.BDyn capb A)).
      * apply (E2r 2%nat). inl. rewrite A2. unfold Q, spd. f_equal. clear; lia.
      * apply (E2r 3%nat). inl. rewrite (K1 3%nat) by inl. exact H3.
      * apply (E2r 4%nat). inl. rewrite (K1 4%nat) by inl. exact H4.
      * apply (E2r 8%nat). inl. exact A8.
      * apply (E2r 9%nat). inl. exact A9.
      * apply (E2r 18%nat). inl. exact A18.
      * apply (E2r 23%nat). inl. exact A23.
      * apply (E2r 20%nat). inl. rewrite (K1 20%nat) by inl. apply HRS. inl.
      * apply (E2r 21%nat). inl. rewrite (K1 21%nat) by inl. apply HRS. inl.
      * apply (E2r 24%nat). inl. rewrite (K1 24%nat) by inl. apply HRS. inl.
      * apply (E2r 25%nat). inl. rewrite (K1 25%nat) by inl. apply HRS. inl.
      * apply (E2r 26%nat). inl. rewrite (K1 26%nat) by inl. apply HRS. inl.
      * apply (E2r 27%nat). inl. rewrite (K1 27%nat) by inl. apply HRS. inl.
      * unfold copy_fb. rewrite !Z.lor_spec, !Z.land_spec. cbn. rewrite Bool.andb_false_r, Bool.andb_true_r. reflexivity.
      * exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
      * exact HH2.
      * reflexivity.
      * unfold credit_after, debit, OPMOD1_K, opmod1_bytes. cbn [fst snd]. pose proof KPOS. pose proof BPOS. split; clear - H H0 CB; unfold capb in *; lia.
      * intros cq p E. injection E. intros <- <-. split. reflexivity. split. exact FB. exact DYT.
      * intros u0 u1 E. discriminate E.
      * exact DER.
      * eapply div_saves_kept. 4: exact DS1. intros i Hi; apply KA2; unfold Q in *; flia. unfold Q; flia. unfold Q; flia.
      * eapply top_frame_kept. 4: exact TF1. intros i Hi; apply KA2; unfold Q in *; flia. flia. flia.
      * eapply big_at_agree1. 4: exact ZQ1. intros i Hi; apply KA2; unfold Q in *; flia. unfold Q; flia. unfold Q; flia.
      * destruct X1 as [OBX1 _]. split. 2: exact NEGX. eapply big_at_agree1. 4: exact OBX1. intros i Hi; apply KA2; unfold Q, X in *; flia. unfold X; flia. unfold X; flia.
      * eapply (cdef_above M1 M2 LB (Q - 352) COPY_SCR _ X 32 HP2). unfold Q; fsclia. rewrite COPY_SCR_val; clear; lia. flia. unfold Q, X; clear; lia. unfold X; flia. exact DX1.
      * exact OD2.
      * exact OL2.
      * eapply big_at_agree1. 4: exact OBB1. intros i Hi; apply KA2; subst bo; unfold Q; flia. subst bo; flia. subst bo; flia.
      * eapply obj_limbs_agree1. 3: exact OLB1.
        -- intros cap q E i Hi. rewrite E in BST. destruct BST as [INB _]. pose proof OLB as (Ln & _ & _).
           unfold L5.big_at in OB0. rewrite E in OB0. destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & _). apply (KB2 q (8 * cap) i INB). rewrite Ln in Hi. clear - Hi Hlc. lia.
        -- intros cap q E. pose proof OLB as (Ln & _ & _). unfold L5.big_at in OB0. rewrite E in OB0.
           destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite Ln. clear - Hlc Hcap Qlo Qhi. lia.
      * eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [] M0 M1 M2 (Q - 352) COPY_SCR [(Q - 136, 32)]). exact HP1. exact HP2.
        -- intros a KA'. eapply L5HP.kept_mono. exact KA'. intros b Hb; exact Hb. unfold Q; fsclia. unfold Q; flia.
           intros _. apply outside1. pose proof (L5HP.kept_not_in_scratch _ _ _ _ _ _ KA' LBceil CEIL ltac:(unfold hl_ceil; rewrite IMG'; clear - SPT; lia)) as NS.
           rewrite SCR_OPMOD_val in NS. unfold Q. clear - NS; lia.
        -- intros b Hb; exact Hb. -- exact CEIL. -- flia. -- rewrite SCR_OPMOD_val; clear; lia. -- rewrite EV; clear; lia. -- flia.
      * intros i Hi. pose proof (IC1 i Hi) as E0.
        apply (L5C.hpres_kept _ _ _ _ _ _ _ i HP2) in E0 || idtac.
        rewrite <- E0. apply (L5C.hpres_kept _ _ _ _ _ _ _ i HP2). eapply L5C.kept_static. rewrite IMGLO, IMG'; clear - Hi; lia.
        { intros ST. apply (ly_static L LY) in ST. clear - ST Hi. lia. } rewrite IMGLO; clear; lia. rewrite IMG'; clear; lia. rewrite EV; clear - Hi; lia.
        apply outside1. unfold Q; clear - Hi SLO; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem o1_head : srealizes RSEGS SCFG (cfg R0 OPMODF M0 model0) K.
Proof.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof MOK0 as (Mh & Ml & _). pose proof SCR0 as SCR. pose proof ERRNOV as EV. pose proof IMG as IMG'.
  pose proof XA as [OBX NEGX]. pose proof BOK as (OB0 & OLB & _ & BST).
  assert (CEIL: hl_ceil L <= S - SCR_OPMOD). { unfold hl_ceil. rewrite SCR_OPMOD_val. clear - SLO'. lia. }
  assert (LBceil: forall b, In b LB -> fst b + snd b <= hl_ceil L).
  { intros [A n] Hb. pose proof (LBdef _ _ _ _ HH0 A n Hb) as (_ & _ & Ahi & _). unfold hl_ceil. cbn. exact Ahi. }
  assert (E10: getr R0 (reg 10) = Z_to_bv 64 (S + 96)). { replace (reg 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). exact G10. }
  assert (E11: getr R0 (reg 11) = Z_to_bv 64 (S + 64)). { replace (reg 11) with (11%bv : bv 5) by (apply bv_eq; reflexivity). exact G11. }
  assert (E12: getr R0 (reg 12) = Z_to_bv 64 bo). { replace (reg 12) with (12%bv : bv 5) by (apply bv_eq; reflexivity). exact G12. }
  assert (U11: bv_unsigned (getr R0 (reg 11)) = S + 64). { rewrite E11. apply BG.unsigned_lit. flia. }
  (* [comment removed for export] *)
  pose proof (dofu1_conc fx0 R0 M0 (VF S 0 0 0 0)) as P. cbn [VF] in P.
  destruct (P ltac:(flia) ltac:(exact G2) ltac:(flia) A16
              ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR | clear; lia | clear; lia] | flia | flia])
              ltac:(rewrite U11; flia) ltac:(rewrite U11; unfold aligned; rewrite <- Zplus_mod_idemp_l, (mod16_mod8 _ A16); reflexivity))
    as (fx1 & R1 & M1 & MG1 & _ & FR1 & (MS1 & K1 & A1 & A2 & A8 & A10 & A11 & C16 & C8)). clear P.
  rewrite E10 in A8. rewrite E11 in A10. rewrite E12 in A11.
  change (L5.u64_at RSEGS M1 (S - 16) (U R0 8)) in C16. change (L5.u64_at RSEGS M1 (S - 8) (U R0 1)) in C8.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  assert (SCR1: L5.defined M1 (S - 10240) 10240). { eapply L5.defined_grows. exact MG1. exact SCR. }
  pose proof (dopu1_conc fx1 R1 M1 (VP (S - 16) 0 0 0 0 0 0)) as P. cbn [VP] in P.
  destruct (P ltac:(flia) A2 ltac:(flia) ltac:(replace (S - 16) with (S + (-1) * 16) by (clear; lia); unfold aligned; rewrite Z_mod_plus_full; exact A16)
              ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR1 | clear; lia | clear; lia] | flia | flia]))
    as (fx2 & R2 & M2 & MG2 & _ & FR2 & (MS2 & K2 & B1 & B2 & B8 & B12 & B13 & B14 & C40 & C48 & C56 & C64 & C32 & C24)). clear P.
  rewrite A8 in C32. rewrite BG.unsigned_lit in C32 by flia. rewrite A1 in C24. rewrite BG.unsigned_lit in C24 by (clear; lia).
  rewrite A10 in B8, B13.
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS2.
  assert (KA: forall a, 0 <= a < 2 ^ 64 -> ~ (S - 64 <= a < S) -> M2 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
  { intros a Ha Hn. rewrite FR2. apply FR1. exact Ha. clear - Hn; lia. exact Ha. clear - Hn; lia. }
  pose proof (mem_grows_trans _ _ _ MG1 MG2) as MG.
  apply (stage_E1 fx2 R2 M2 model0).
  - exact B1.
  - rewrite B2. unfold Q. f_equal. clear; lia.
  - rewrite (K2 3%nat) by inl. rewrite (K1 3%nat) by inl. exact G3.
  - rewrite (K2 4%nat) by inl. rewrite (K1 4%nat) by inl. exact G4.
  - exact B8.
  - rewrite (K2 10%nat) by inl. exact A10.
  - rewrite (K2 11%nat) by inl. exact A11.
  - rewrite B12. unfold Q. f_equal. clear; lia.
  - exact B13. - exact B14.
  - intros i Hi. rewrite K2. apply K1. revert Hi. apply (L5K.incl_b _ KS_dofu1). vm_compute. reflexivity.
    revert Hi. apply (L5K.incl_b _ KS_dopu1). vm_compute. reflexivity.
  - apply L5C.model_but_vm_refl.
  - eapply (hi_heap_stackwrite LB cr M0 M2 _ (S - 64) S). exact HH0. exact KA. flia. flia. flia. exact MG.
  - split. { eapply u64_at_agree1. 4: exactA C8. intros i Hi; apply FR2; flia. flia. flia. }
    split. { eapply u64_at_agree1. 4: exactA C16. intros i Hi; apply FR2; flia. flia. flia. }
    split. { unfold OPF_BACK. exactA C24. } exactA C32.
  - unfold zero_obj, L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. unfold Q; exactA C64. split. clear; lia. split. unfold Q; exactA C56.
    split. reflexivity. split. unfold Q; exactA C48. split. unfold Q; exactA C40. clear; lia.
  - split. 2: exact NEGX. eapply big_at_agree1. 4: exact OBX. intros i Hi; apply KA; unfold X in *; flia. unfold X; flia. unfold X; flia.
  - eapply L5.defined_grows. exact MG. apply (writable_defined_hi M0 X 32 WX32). unfold L5KU.IMG_HI, X; flia. clear; lia. unfold X; flia.
  - eapply big_at_agree1. 4: exact OB0. intros i Hi; apply KA; subst bo; flia. subst bo; flia. subst bo; flia.
  - eapply obj_limbs_agree1. 3: exact OLB.
    + intros cap q E i Hi. rewrite E in BST. destruct BST as [INB _]. pose proof OLB as (Ln & _ & _).
      unfold L5.big_at in OB0. rewrite E in OB0. destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _).
      pose proof (LBdef _ _ _ _ HH0 q (8 * cap) INB) as (_ & _ & Ahi & _).
      apply KA. rewrite Ln in Hi; clear - Hi Hlc Qlo Qhi; lia. rewrite Ln in Hi; clear - Hi Hlc Ahi SLO'; lia.
    + intros cap q E. pose proof OLB as (Ln & _ & _). unfold L5.big_at in OB0. rewrite E in OB0.
      destruct OB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite Ln. clear - Hlc Hcap Qlo Qhi. lia.
  - eapply (L5HP.hpres_piece L LB S SCR_OPMOD [] M0 M2 (fun a => S - 64 <= a < S)). exact KA.
    { intros a KA' C. apply (L5HP.kept_not_in_scratch _ _ _ _ _ _ KA' LBceil CEIL ltac:(unfold hl_ceil; rewrite IMG'; clear - SPT; lia)). rewrite SCR_OPMOD_val. clear - C; lia. }
    rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG. exact SCR. exact MG.
  - intros i Hi. rewrite KA. apply IMGC. exact Hi. clear - Hi; lia. clear - Hi SLO; lia.
Qed.

End Call.
End WithHeap.
End SCFG_1.
End L5OPMOD1HU.
