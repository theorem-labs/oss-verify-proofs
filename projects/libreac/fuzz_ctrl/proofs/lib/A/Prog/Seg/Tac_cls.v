(* The per-class side of the allocator calls of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): ONE wrapper per
   allocator, so that a segment proof never takes the class machinery apart itself.

   rule 24: no function proved here; these are the class premises of the allocator contracts.

   Generation N.1 gave amalloc_at / afree_at (Contract.v:285 / :320) two per-class premises over a bound Bc:
     (i)  the CALL heap's fit: ClassConsDef.a_class_req_fits Bc H n for an allocation, the plain per-class bound
          `a_class_bytes (H1 ++ (p, n) :: H2) c <= Bc c` for a free;
     (ii) the room inequality `Bc c + QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF`.
   ENT's 14th conjunct (SlotInv.v) gives SOME BE with the entry heap under BE and BE c + BC_ctrl c <= 2 ^ 22. Each
   wrapper returns that same witness BE together with (i) and (ii) for Bc = Bc_of BE = BE + BC_ctrl (the entry
   heap's share plus the slot's own share, a Theorem Labs lane's ctrl_Bc), and the bound of the heap after the call.
   ENT itself needs no restoring: its conjunct names the ENTRY heap g_H g, which no call changes.

   (ii) comes from the shared budget: Bc c <= 2 ^ 22 <= BC_MAX c at every class (the room table below, vm_compute), and
   BC_MAX c is K_FREEARR_OFF minus the other three terms (ClassConsDef.v:136).

   in_class_a_size, in_class_not_0_5_31 and ctrl_req_slot_le are carried word for word from a Theorem Labs lane's
   CtrlClassLive.v (not in this delivery) (a working branch 61aba11640, all Qed there), because that file Requires
   SlotInvCF, whose AZ/AS dependencies do not build on the v1.9 FACTS yet; BC_ctrl is SlotInv.v's (the same body).

   Image A's allocator set (Contract.v ASYMS): malloc wrapper 0x5337c and free wrapper 0x53378 only (calloc and
   realloc are None), so there is no realloc / calloc wrapper. Call sites in v1.9 image A: the mallocs 0x8163c (R7)
   and 0x81da0 (F1), whose cuts Inv_A815ec_at / Inv_A81d40_at carry the empty slot heap list, so the call heap is
   g_H g; the frees 0x81920 (R13) and 0x8293c (F37), whose call heap is the cut's block in front of g_H g. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AZ.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AZ.Spec Require AsanCtrlProps.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ClassConsDef ClassRoomLow Contract AsanRTInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YM05 YK11 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.W6 Require QSlot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Open Scope Z_scope.

Module CCD := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ClassConsDef.
Module CRL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ClassRoomLow.
Module QS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.W6.QSlot.
Module ACx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.

(* ---- carried from CtrlClassLive.v (Qed there) ---- *)

Lemma in_class_a_size : forall c n, CCD.in_class c (ACx.a_size n) = CCD.in_class c n.
Proof.
  intros c n. unfold ACx.a_size. destruct (Z.le_gt_cases 1 n) as [H1 | H1].
  - rewrite Z.max_l by lia. reflexivity.
  - rewrite Z.max_r by lia. unfold CCD.in_class, needed_size, is_primary.
    rewrite (CRL.needed0_small 1), (CRL.needed0_small n) by lia. reflexivity.
Qed.

Lemma in_class_not_0_5_31 : forall c n, CCD.in_class c n = true -> c <> 0 /\ c <> 5 /\ c <> 31.
Proof.
  intros c n H. unfold CCD.in_class in H. apply andb_prop in H as [Hp Hc]. apply Z.eqb_eq in Hc. subst c.
  destruct (Z.le_gt_cases n 0) as [Hn0 | Hn0].
  - assert (E : needed_size n = 24).
    { unfold needed_size. rewrite Hp. exact (CRL.needed0_small n ltac:(lia)). }
    rewrite E. assert (C : class_id 24 = 1) by reflexivity. rewrite C. lia.
  - destruct (Z.le_gt_cases n 64512) as [Hn1 | Hn1].
    + exact (QS.no_request_in_classes_0_5_31 n ltac:(lia)).
    + exfalso.
      assert (R : rz_log n = 7).
      { unfold rz_log.
        destruct (Z.leb_spec n 48); [lia |]. destruct (Z.leb_spec n 96); [lia |].
        destruct (Z.leb_spec n 448); [lia |]. destruct (Z.leb_spec n 3968); [lia |].
        destruct (Z.leb_spec n 16128); [lia |]. destruct (Z.leb_spec n 32256); [lia |].
        destruct (Z.leb_spec n 64512); [lia |]. reflexivity. }
      unfold is_primary, needed0, rounded_size, rz_size in Hp. rewrite R in Hp.
      apply Z.leb_le in Hp. unfold rup, K_MAX_SIZE in Hp. rewrite Z.max_l in Hp by lia.
      change (Z.shiftl 16 7) with 2048 in Hp.
      Z.div_mod_to_equations. lia.
Qed.

Lemma ctrl_req_slot_le : forall n c, 0 <= c < K_NUM_CLASSES ->
  (if CCD.in_class c n then size_of_class c else 0) <= BC_ctrl c.
Proof.
  intros n c Hc. unfold BC_ctrl.
  pose proof (proj1 (CRL.size_of_class_le c Hc)) as S0.
  destruct (CCD.in_class c n) eqn:Hin; [| destruct ((c =? 0) || (c =? 5) || (c =? 31)); lia].
  destruct (in_class_not_0_5_31 c n Hin) as (A & B & C).
  rewrite (proj2 (Z.eqb_neq _ _) A), (proj2 (Z.eqb_neq _ _) B), (proj2 (Z.eqb_neq _ _) C).
  cbn [orb]. lia.
Qed.

(* ---- the shared budget and the room inequality ---- *)

(* The generated room table: the shared budget 2 ^ 22 is at or under BC_MAX at every one of the 32 classes. *)
Example bcmax_ge_fleet :
  forallb (fun c => 2 ^ 22 <=? CCD.BC_MAX c) (AsanCtrlProps.zseq 0 (Z.to_nat 32)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bcmax_ge_fleet_at : forall c, 0 <= c < K_NUM_CLASSES -> 2 ^ 22 <= CCD.BC_MAX c.
Proof.
  intros c Hc.
  pose proof (AsanCtrlProps.forallb_zseq (fun c => 2 ^ 22 <=? CCD.BC_MAX c) 0 (Z.to_nat 32) bcmax_ge_fleet c
                ltac:(unfold K_NUM_CLASSES in Hc; rewrite Z2Nat.id; lia)) as H.
  apply Z.leb_le in H. exact H.
Qed.

(* The whole-heap budget a call site passes as Bc: the entry heap's share BE plus the slot's own share. *)
Definition Bc_of (BE : Z -> Z) (c : Z) : Z := BE c + BC_ctrl c.

Lemma cls_room : forall BE : Z -> Z,
  (forall c, 0 <= c < K_NUM_CLASSES -> BE c + BC_ctrl c <= 2 ^ 22) ->
  forall c, 0 <= c < K_NUM_CLASSES ->
    Bc_of BE c + CCD.QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF.
Proof.
  intros BE HR c Hc. pose proof (HR c Hc). pose proof (bcmax_ge_fleet_at c Hc).
  unfold Bc_of. unfold CCD.BC_MAX in *. lia.
Qed.

Section Cls.
Context {fx : YK11.FPState} {LS : YO09.lib_shape} {rc : YM05.RunCeil}.
Variable APIf : forall rc : YM05.RunCeil, ACx.AsanAllocAPI ACx.ASYMS AsanRTInv.RT.

(* ---- malloc (AK_MALLOC, image A 0x5337c; call sites 0x8163c and 0x81da0) ---- *)

(* amalloc_at's class premises (i) and (ii) for a request n with the call heap g_H g (the slot heap list is empty
   at both malloc cuts), with Bc = Bc_of BE for ENT's own witness BE; and the heap the call returns,
   g_H g ++ [(q, a_size n)], is still under that Bc. *)
Lemma sl_malloc_cls : forall g hb mem md n,
  ENT APIf g hb mem md ->
  exists BE : Z -> Z,
    (forall c, 0 <= c < K_NUM_CLASSES -> CCD.a_class_bytes (g_H g) c <= BE c) /\
    (forall c, 0 <= c < K_NUM_CLASSES -> BE c + BC_ctrl c <= 2 ^ 22) /\
    CCD.a_class_req_fits (Bc_of BE) (g_H g) n /\
    (forall c, 0 <= c < K_NUM_CLASSES ->
       Bc_of BE c + CCD.QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF) /\
    (forall q c, 0 <= c < K_NUM_CLASSES ->
       CCD.a_class_bytes (g_H g ++ [(q, ACx.a_size n)]) c <= Bc_of BE c).
Proof.
  intros g hb mem md n HENT.
  destruct (ent_class_of APIf g hb mem md HENT) as (BE & HE & HR).
  exists BE. split; [exact HE|]. split; [exact HR|]. split; [| split; [exact (cls_room BE HR) |]].
  - intros c Hc. pose proof (HE c Hc). pose proof (ctrl_req_slot_le n c Hc). unfold Bc_of. lia.
  - intros q c Hc. rewrite CRL.a_class_bytes_snoc, in_class_a_size.
    pose proof (HE c Hc). pose proof (ctrl_req_slot_le n c Hc). unfold Bc_of. lia.
Qed.

(* ---- free (AK_FREE, image A 0x53378; call sites 0x81920 and 0x8293c) ---- *)

(* afree_at's class premises (i) and (ii) with H1 = [] and H2 = g_H g: the freed block (p, n) is the cut's own
   block, so the call heap is (p, n) :: g_H g; Bc = Bc_of BE for ENT's own witness BE. After the free the heap is
   g_H g again, which ENT's conjunct already bounds by BE. *)
Lemma sl_free_cls : forall g hb mem md p n,
  ENT APIf g hb mem md ->
  exists BE : Z -> Z,
    (forall c, 0 <= c < K_NUM_CLASSES -> CCD.a_class_bytes (g_H g) c <= BE c) /\
    (forall c, 0 <= c < K_NUM_CLASSES -> BE c + BC_ctrl c <= 2 ^ 22) /\
    (forall c, 0 <= c < K_NUM_CLASSES -> CCD.a_class_bytes ((p, n) :: g_H g) c <= Bc_of BE c) /\
    (forall c, 0 <= c < K_NUM_CLASSES ->
       Bc_of BE c + CCD.QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF).
Proof.
  intros g hb mem md p n HENT.
  destruct (ent_class_of APIf g hb mem md HENT) as (BE & HE & HR).
  exists BE. split; [exact HE|]. split; [exact HR|]. split; [| exact (cls_room BE HR)].
  intros c Hc. rewrite CRL.a_class_bytes_cons.
  pose proof (HE c Hc). pose proof (ctrl_req_slot_le n c Hc). unfold Bc_of. lia.
Qed.

End Cls.
