(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzDev.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.






(* [comment removed for export] *)
Inductive dstep : Type :=
| DRun (stops : list Z) | DLo (e : expr) (mid : Z) | DHi (e : expr) (mid : Z) | DRLo (r : nat) (mid : Z) | DRHi (r : nat) (mid : Z)
| DExt (id : nat) (args : list expr) | DFact (K : kentry) | DVia (e via : expr) (lo hi : Z) | DLe (e big : expr) (hi : Z)
| DScale (e : expr) (c hi : Z)
| DBrF | DBrT   (* [comment removed for export] *)
| DX2a (id : nat) (args : list expr) | DX2b (id : nat) (args : list expr)   (* [comment removed for export] *).

Section Stepper.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Variable bfuel : nat.

Definition dgo (gcb : nat) (cs : acs) (st : dstep) : option acs :=
  match st with
  | DRun stops => run_block_gc segs IT gcb 0%nat bfuel (stops ++ STOPS A) cs
  | DLo e mid => match erange (kn cs) e with Some (lo, hi) => Some (set_kn cs (KRange e lo mid :: kn cs)) | None => None end
  | DHi e mid => match erange (kn cs) e with Some (lo, hi) => Some (set_kn cs (KRange e (mid + 1) hi :: kn cs)) | None => None end
  | DRLo r mid => let e := reg cs r in match erange (kn cs) e with Some (lo, hi) => Some (set_kn cs (KRange e lo mid :: kn cs)) | None => None end
  | DRHi r mid => let e := reg cs r in match erange (kn cs) e with Some (lo, hi) => Some (set_kn cs (KRange e (mid + 1) hi :: kn cs)) | None => None end
  | DExt id args => XN id args cs
  | DFact K => if fact_ok (kn cs) K then Some (add_kn cs [K]) else None
  | DVia e via lo hi => if factvia_ok (kn cs) e via lo hi then Some (add_kn cs [KRange e lo hi]) else None
  | DLe e big hi => if factle_ok (kn cs) e big hi then Some (add_kn cs [KRange e 0 hi]) else None
  | DScale e c hi => if factscale_ok (kn cs) e c hi then Some (add_kn cs [KRange e 0 hi]) else None
  | DX2a id args => match XB id args cs with Some (a, _) => Some a | None => None end
  | DX2b id args => match XB id args cs with Some (_, b) => Some b | None => None end
  | DBrF | DBrT =>
      match branch_probe2 IT cs with
      | Some (e, pos) =>
          match erange (kn cs) e with
          | Some (lo, hi) =>
              let cs0 := set_kn cs (KRange e lo 0 :: probe_lin_facts (kn cs) e false ++ kn cs) in
              let cs1 := set_kn cs (KRange e (0 + 1) hi :: probe_lin_facts (kn cs) e true ++ kn cs) in
              let taken := match st with DBrT => true | _ => false end in
              Some (if Bool.eqb taken pos then cs1 else cs0)
          | None => None
          end
      | None => None
      end
  end.
(* [comment removed for export] *)
Fixpoint dpath (gcb : nat) (cs : acs) (sts : list dstep) (n : nat) : nat * acs :=
  match sts with
  | [] => (n, cs)
  | st :: r => match dgo gcb cs st with Some cs' => dpath gcb cs' r (Datatypes.S n) | None => (n, cs) end
  end.
End Stepper.

End GlzDev.
Require Stdlib.NArith.NArith Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzEntry.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma regs_ok_intro : forall E (sr : list expr) (R : bvmap 5 word),
  length sr = 32%nat ->
  (forall i : nat, (1 <= i < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R Hlen H r. unfold sr_get, getr.
  destruct (bv_eqb r 0) eqn:Hr0; [reflexivity|].
  pose proof (ridx_roundtrip r) as Hr. symmetry in Hr.
  pose proof (u5_range r) as Hu5.
  assert (Hnz : ridx r <> 0%nat).
  { intros Hz. unfold ridx in Hz. assert (H00 : bv_unsigned r = 0) by lia.
    assert (r = 0%bv) by (apply bv_eq; rewrite H00; reflexivity). subst r. rewrite bv_eqb_refl in Hr0. discriminate. }
  pose proof (ridx_range r) as Hrg.
  specialize (H (ridx r) ltac:(lia)). rewrite <- Hr in H. unfold getr in H. rewrite Hr0 in H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma know_ok_nil : forall SEGS E M, know_ok SEGS E M [].
Proof. intros. constructor. Qed.
Lemma know_ok_cons : forall SEGS E M K kn, kentry_ok SEGS E M K -> know_ok SEGS E M kn -> know_ok SEGS E M (K :: kn).
Proof. intros. constructor; assumption. Qed.
Lemma know_ok_app : forall SEGS E M k1 k2, know_ok SEGS E M k1 -> know_ok SEGS E M k2 -> know_ok SEGS E M (k1 ++ k2).
Proof. intros. unfold know_ok. apply Forall_app. split; assumption. Qed.

(* [comment removed for export] *)
Lemma kentry_ok_KRange : forall SEGS E M e lo hi,
  lo <= bv_unsigned (edenot E e) <= hi -> kentry_ok SEGS E M (KRange e lo hi).
Proof. intros SEGS E M e lo hi [H1 H2]. cbn. split; assumption. Qed.
Lemma kentry_ok_KAlign : forall SEGS E M e m,
  0 < m -> bv_unsigned (edenot E e) mod m = 0 -> kentry_ok SEGS E M (KAlign e m).
Proof. intros. cbn. split; assumption. Qed.


(* [comment removed for export] *)
Lemma kentry_ok_KImg : forall SEGS E M lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None) -> kentry_ok SEGS E M (KImg lo hi).
Proof. intros. cbn. split; [assumption | split; assumption]. Qed.




(* [comment removed for export] *)
Lemma kentry_ok_KWord : forall SEGS E M a (w : nat) v,
  (w <= 8)%nat -> flat E a (Z.of_nat w) ->
  rdn SEGS M (adenot E a) w = Some (word_to_le_bytes w (edenot E v)) ->
  kentry_ok SEGS E M (KWord a w v).
Proof. intros. cbn. split; [assumption | split; assumption]. Qed.
(* [comment removed for export] *)
Lemma rdn_of_mem : forall SEGS M n (a : word) (bs : list byte),
  length bs = n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> M (Z_to_bv 64 (bv_unsigned a + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0))) ->
  rdn SEGS M a n = Some bs.
Proof.
  intros SEGS M n. induction n as [|n IH]; intros a bs Hlen Hnw HM.
  - destruct bs; [reflexivity | discriminate].
  - destruct bs as [|b bs]; [discriminate|]. cbn [rdn].
    pose proof (HM 0%nat ltac:(lia)) as H0. cbn [nth] in H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
    destruct (Nat.eq_dec n 0) as [->|Hn0].
    { destruct bs; [reflexivity | cbn in Hlen; lia]. }
    assert (Ha1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv bs); [reflexivity | cbn in Hlen; lia | rewrite Ha1; lia |].
    intros i Hi. specialize (HM (S i) ltac:(lia)). cbn [nth] in HM. rewrite Ha1.
    replace (bv_unsigned a + 1 + Z.of_nat i) with (bv_unsigned a + Z.of_nat (S i)) by lia. exact HM.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cs_ok_intro :
  forall SEGS {RC : run_ceil} (PERMc : list (Z * Z)) (SPTOPc : Z) (FS0 : Fs.Fs) (FDS0 : list (word * FdEntry))
         (AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop)
         (FXOK : FX -> Prop) (UINV : env -> Prop)
         (E : env) (cs : acs) (fx : FX) (R : bvmap 5 word) (M : word -> option byte) (model : Model),
    regs_ok E (s_regs (a_ss cs)) R ->
    s_log (a_ss cs) = [] ->
    know_ok SEGS E M (kn cs) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    m_fs model = FS0 -> m_fds model = FDS0 ->
    AINV (blocks_den E (a_vis cs)) (bcost E (a_vis cs)) (bcount (a_vis cs)) M model ->
    UINV E -> FXOK fx ->
    wins_den E (a_ghost cs) = PERMc -> sptop_den E (a_brk cs) = SPTOPc ->
    floor_sem E (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) ->          (* [comment removed for export] *)
    GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model.
Proof. intros. constructor; assumption. Qed.




End GlzEntry.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpCalleeSub.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import GPS.

Lemma callee_contract_more_exits : forall SEGS {RC : run_ceil} SWIN G FXOK (RZ : GPS.rz_t) AINVH (c c' : gcallee),
  ce_nxf c' = ce_nxf c -> ce_tin c' = ce_tin c -> ce_bcap c' = ce_bcap c -> ce_ccap c' = ce_ccap c ->
  (forall t, In t (ce_touts c) -> In t (ce_touts c')) ->
  callee_contract SEGS SWIN G FXOK RZ AINVH c -> callee_contract SEGS SWIN G FXOK RZ AINVH c'.
Proof.
  intros SEGS RC SWIN G FXOK RZ AINVH c c' Hn Ht Hb Hc Hsub H.
  unfold callee_contract, callee_contract_when in *.
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 E fx R M mdl T HB0 HC0 HBc HCc HQ HCS HT Hk.
  rewrite Ht. rewrite Hb in HBc. rewrite Hc in HCc. rewrite Ht in HCS.
  apply (H PERMf TOPf HID M0 B0 C0 FS0 FDS0 E fx R M mdl T HB0 HC0 HBc HCc HQ HCS HT).
  intros tout E' fx' R' M' mdl' Hin Hag HCS' Hfs.
  apply (Hk tout E' fx' R' M' mdl' (Hsub tout Hin)); [rewrite Hn; exact Hag | exact HCS' | exact Hfs].
Qed.

(* [comment removed for export] *)
Lemma callee_contract_L_of_L1 : forall SEGS {RC : run_ceil} SWIN G FXOK (RZ : GPS.rz_t) AINVH nxf tin tS tL bc cc,
  callee_contract SEGS SWIN G FXOK RZ AINVH (GCE nxf tin [tL; tL] bc cc) ->
  callee_contract SEGS SWIN G FXOK RZ AINVH (c2_merged (GCE2 nxf tin [tS] [tL] bc cc)).
Proof.
  intros SEGS RC SWIN G FXOK RZ AINVH nxf tin tS tL bc cc H.
  apply (callee_contract_more_exits SEGS SWIN G FXOK RZ AINVH (GCE nxf tin [tL; tL] bc cc)); try reflexivity; [|exact H].
  intros t Ht. cbn [ce_touts c2_merged c2_touts0 c2_touts1 app] in Ht |- *. right.
  destruct Ht as [<-|Ht]; [left; reflexivity | exact Ht].
Qed.
End GpCalleeSub.
Require Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzRom OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzNodesImg.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzRom OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.





(* [comment removed for export] *)
Definition rom_load_g (segs : list Segment) (sz : msize) (sx : bool) (j : Z) : option Z :=
  match rdn segs (fun _ => None) (Z_to_bv 64 j) (GxSymStepR.msize_bytes sz) with
  | Some bs => Some (bv_unsigned (load_result sz sx bs))
  | None => None
  end.

Section WithTables.
Variable segs : list Segment.
Variable IT : itab.
Variable nx0 : nat.
Context {RCX : rom_cache rom_load_g}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint kimg_cover (k : list kentry) (lo hi : Z) : bool :=
  match k with
  | [] => false
  | KImg l h :: rest => (Z.leb l lo && Z.leb hi h) || kimg_cover rest lo hi
  | _ :: rest => kimg_cover rest lo hi
  end%bool.

(* [comment removed for export] *)
Definition rom_load (sz : msize) (sx : bool) (j : Z) : option Z :=
  match rdn segs (fun _ => None) (Z_to_bv 64 j) (GxSymStepR.msize_bytes sz) with
  | Some bs => Some (bv_unsigned (load_result sz sx bs))
  | None => None
  end.
(* [comment removed for export] *)
Definition rom_rd : msize -> bool -> Z -> option Z := rom_reader rom_load_g segs.
Lemma rom_rd_eq : rom_rd = rom_load.
Proof.
  apply functional_extensionality; intros sz. apply functional_extensionality; intros sx. apply functional_extensionality; intros j.
  unfold rom_rd. rewrite rom_reader_eq. reflexivity.
Qed.

Definition node_enumload_stride_ref (cs : acs) : option acs :=
  match itab_lookup IT (pc cs) with
  | Some (Load sz sx rd rs imm) =>
      let n := Z.of_nat (GxSymStepR.msize_bytes sz) in
      let a := eaddz (sr_get (s_regs (a_ss cs)) rs) (bv_signed imm) in
      match xlo (kn cs) a, xhi (kn cs) a with
      | Some lo, Some hi =>
          (* [comment removed for export] *)
          let g := 2 ^ Z.min (ealign (kn cs) a) 12 in
          let lo' := (lo + g - 1) / g * g in
          if (fresh_ok nx0 cs && kimg_cover (kn cs) lo (hi + n) && Z.leb 0 lo && Z.leb lo' hi && Z.leb ((hi - lo') / g) ENUM_MAX
              && Z.ltb (hi + n) two64 && negb (bv_eqb rd 0%bv)
              && Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 && Nat.eqb (length (s_regs (a_ss cs))) 32)%bool
          then match enum_minmax (fun i => rom_load sz sx (lo' + g * i)) 0 ((hi - lo') / g) with
               | Some (mn, mx) =>
                   let v := nxt cs in
                   let ss := a_ss cs in
                   Some (with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs ss) (ridx rd) (EVar v))
                                           (KRange (EVar v) mn mx :: s_know ss) (S v)))
               | None => None
               end
          else None
      | _, _ => None
      end
  | Some _ => Some cs      (* [comment removed for export] *)
  | None => Some cs        (* [comment removed for export] *)
  end.
Definition node_enumload_stride (cs : acs) : option acs :=
  match itab_lookup IT (pc cs) with
  | Some (Load sz sx rd rs imm) =>
      let n := Z.of_nat (GxSymStepR.msize_bytes sz) in
      let a := eaddz (sr_get (s_regs (a_ss cs)) rs) (bv_signed imm) in
      match xlo (kn cs) a, xhi (kn cs) a with
      | Some lo, Some hi =>
          (* [comment removed for export] *)
          let g := 2 ^ Z.min (ealign (kn cs) a) 12 in
          let lo' := (lo + g - 1) / g * g in
          if (fresh_ok nx0 cs && kimg_cover (kn cs) lo (hi + n) && Z.leb 0 lo && Z.leb lo' hi && Z.leb ((hi - lo') / g) ENUM_MAX
              && Z.ltb (hi + n) two64 && negb (bv_eqb rd 0%bv)
              && Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 && Nat.eqb (length (s_regs (a_ss cs))) 32)%bool
          then match (let rl := rom_rd in enum_minmax (fun i => rl sz sx (lo' + g * i)) 0 ((hi - lo') / g)) with
               | Some (mn, mx) =>
                   let v := nxt cs in
                   let ss := a_ss cs in
                   Some (with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs ss) (ridx rd) (EVar v))
                                           (KRange (EVar v) mn mx :: s_know ss) (S v)))
               | None => None
               end
          else None
      | _, _ => None
      end
  | Some _ => Some cs      (* [comment removed for export] *)
  | None => Some cs        (* [comment removed for export] *)
  end.
Lemma node_enumload_stride_eq : forall cs, node_enumload_stride cs = node_enumload_stride_ref cs.
Proof. intros cs. unfold node_enumload_stride, node_enumload_stride_ref. rewrite rom_rd_eq. reflexivity. Qed.

(* [comment removed for export] *)
Definition lin1 (e : expr) : option (Z * Z * expr) :=
  match lin_of e with
  | (c, [(k, x)]) => Some (c, k, x)
  | _ => None
  end.
Definition cand_load (k : list kentry) (sz : msize) (sx : bool) (n : Z) (adr : Z) : option Z :=
  if (kimg_cover k adr (adr + n) && Z.leb 0 adr && Z.ltb (adr + n) two64)%bool then rom_load sz sx adr else None.
Definition cand_loadR (rl : msize -> bool -> Z -> option Z) (k : list kentry) (sz : msize) (sx : bool) (n : Z) (adr : Z) : option Z :=
  if (kimg_cover k adr (adr + n) && Z.leb 0 adr && Z.ltb (adr + n) two64)%bool then rl sz sx adr else None.
Definition node_enumlin_ref (cs : acs) : option acs :=
  match itab_lookup IT (pc cs) with
  | Some (Load sz sx rd rs imm) =>
      let n := Z.of_nat (GxSymStepR.msize_bytes sz) in
      let a := eaddz (sr_get (s_regs (a_ss cs)) rs) (bv_signed imm) in
      match lin1 a with
      | None => None
      | Some (c0, kk, x) =>
          match xlo (kn cs) x, xhi (kn cs) x with
          | Some elo, Some ehi =>
              if (fresh_ok nx0 cs && Z.leb 0 elo && Z.leb elo ehi && Z.leb (ehi - elo) ENUM_MAX && negb (bv_eqb rd 0%bv)
                  && Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 && Nat.eqb (length (s_regs (a_ss cs))) 32)%bool
              then match enum_minmax (fun i => cand_load (kn cs) sz sx n ((c0 + kk * (elo + i)) mod two64)) 0 (ehi - elo) with
                   | Some (mn, mx) =>
                       let v := nxt cs in
                       let ss := a_ss cs in
                       Some (with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs ss) (ridx rd) (EVar v))
                                               (KRange (EVar v) mn mx :: s_know ss) (S v)))
                   | None => None
                   end
              else None
          | _, _ => None
          end
      end
  | _ => None
  end.
Definition node_enumlin (cs : acs) : option acs :=
  match itab_lookup IT (pc cs) with
  | Some (Load sz sx rd rs imm) =>
      let n := Z.of_nat (GxSymStepR.msize_bytes sz) in
      let a := eaddz (sr_get (s_regs (a_ss cs)) rs) (bv_signed imm) in
      match lin1 a with
      | None => None
      | Some (c0, kk, x) =>
          match xlo (kn cs) x, xhi (kn cs) x with
          | Some elo, Some ehi =>
              if (fresh_ok nx0 cs && Z.leb 0 elo && Z.leb elo ehi && Z.leb (ehi - elo) ENUM_MAX && negb (bv_eqb rd 0%bv)
                  && Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 && Nat.eqb (length (s_regs (a_ss cs))) 32)%bool
              then match (let rl := rom_rd in enum_minmax (fun i => cand_loadR rl (kn cs) sz sx n ((c0 + kk * (elo + i)) mod two64)) 0 (ehi - elo)) with
                   | Some (mn, mx) =>
                       let v := nxt cs in
                       let ss := a_ss cs in
                       Some (with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs ss) (ridx rd) (EVar v))
                                               (KRange (EVar v) mn mx :: s_know ss) (S v)))
                   | None => None
                   end
              else None
          | _, _ => None
          end
      end
  | _ => None
  end.
Lemma node_enumlin_eq : forall cs, node_enumlin cs = node_enumlin_ref cs.
Proof. intros cs. unfold node_enumlin, node_enumlin_ref. rewrite rom_rd_eq. reflexivity. Qed.

Definition node_enumload (cs : acs) : option acs :=
  match node_enumlin cs with Some cs' => Some cs' | None => node_enumload_stride cs end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition node_havoc64 (args : list expr) (cs : acs) : option acs :=
  match args with
  | [ELit r] =>
      if (Z.leb 1 r && Z.leb r 31 && fresh_ok nx0 cs && Nat.eqb (length (s_regs (a_ss cs))) 32)%bool then
        let v := nxt cs in
        let ss := a_ss cs in
        Some (with_ss cs (mk_ss (s_pc ss) (sr_upd (s_regs ss) (Z.to_nat r) (EVar v))
                                (KRange (EVar v) 0 (two64 - 1) :: s_know ss) (S v)))
      else None
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition popcnt_chain_ref (fk : list kentry) (x : expr) : expr :=
  let a6 := mkAluK fk ALU_SRL x (ELit 1) in
  let a6 := mkAluK fk ALU_AND a6 (ELit M55) in
  let a5 := mkAluK fk ALU_AND x (ELit (-2)) in
  let a5 := mkAluK fk ALU_SUB a5 a6 in
  let a6 := mkAluK fk ALU_AND a5 (ELit M33) in
  let a5 := mkAluK fk ALU_SRL a5 (ELit 2) in
  let a5 := mkAluK fk ALU_AND a5 (ELit M33) in
  let a5 := mkAluK fk ALU_ADD a6 a5 in
  let a6 := mkAluK fk ALU_SRL a5 (ELit 4) in
  let a5 := mkAluK fk ALU_ADD a5 a6 in
  let a5 := mkAluK fk ALU_AND a5 (ELit M0f) in
  let a5 := mkMdK fk M_MUL a5 (ELit M01) in
  mkAluK fk ALU_SRL a5 (ELit 56).
(* [comment removed for export] *)
Definition popcnt_chainB (bc : AX2B.bctx) (x : expr) : expr :=
  let a6 := AX2B.mkAluKB bc ALU_SRL x (ELit 1) in
  let a6 := AX2B.mkAluKB bc ALU_AND a6 (ELit M55) in
  let a5 := AX2B.mkAluKB bc ALU_AND x (ELit (-2)) in
  let a5 := AX2B.mkAluKB bc ALU_SUB a5 a6 in
  let a6 := AX2B.mkAluKB bc ALU_AND a5 (ELit M33) in
  let a5 := AX2B.mkAluKB bc ALU_SRL a5 (ELit 2) in
  let a5 := AX2B.mkAluKB bc ALU_AND a5 (ELit M33) in
  let a5 := AX2B.mkAluKB bc ALU_ADD a6 a5 in
  let a6 := AX2B.mkAluKB bc ALU_SRL a5 (ELit 4) in
  let a5 := AX2B.mkAluKB bc ALU_ADD a5 a6 in
  let a5 := AX2B.mkAluKB bc ALU_AND a5 (ELit M0f) in
  let a5 := AX2B.mkMdKB bc M_MUL a5 (ELit M01) in
  AX2B.mkAluKB bc ALU_SRL a5 (ELit 56).
Definition popcnt_chain (fk : list kentry) (x : expr) : expr := popcnt_chainB (AX2B.mkbc fk) x.
Lemma popcnt_chain_eq : forall fk x, popcnt_chain fk x = popcnt_chain_ref fk x.
Proof. intros. unfold popcnt_chain, popcnt_chainB, popcnt_chain_ref. rewrite !AX2B.mkAluKB_eqf, !AX2B.mkMdKB_eqf. reflexivity. Qed.

Definition node_popcnt (args : list expr) (cs : acs) : option acs :=
  match args with
  | [ELit r] =>
      if (Z.leb 1 r && Z.leb r 31)%bool then
        let x := nth (Z.to_nat r) (s_regs (a_ss cs)) (ELit 0) in
        Some (add_kn cs [KRange (popcnt_chain (facts_of (kn cs)) x) 0 64])
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_enumreg (args : list expr) (cs : acs) : option acs :=
  match args with
  | [ELit r; s] => if (Z.leb 0 r && Z.leb r 31)%bool then node_enumrange [nth (Z.to_nat r) (s_regs (a_ss cs)) (ELit 0); s] cs else None
  | _ => None
  end.

End WithTables.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kimg_cover_sound : forall segs E M k lo hi,
  know_ok segs E M k -> kimg_cover k lo hi = true -> forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.
Proof.
  intros segs E M k lo hi Hk. induction k as [|K rest IH]; intros Hc i Hi; [discriminate|].
  apply Forall_cons_iff in Hk as [HK Hrest]. cbn [kimg_cover] in Hc.
  destruct K; try exact (IH Hrest Hc i Hi).
  apply orb_prop in Hc as [Hc|Hc]; [|exact (IH Hrest Hc i Hi)].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [kentry_ok] in HK. destruct HK as (_ & _ & HK). apply HK. lia.
Qed.

Lemma rdn_overlay_none : forall segs M n (a : word),
  (forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (bv_unsigned a + i)) = None) ->
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  rdn segs M a n = rdn segs (fun _ => None) a n.
Proof.
  intros segs M n. induction n as [|n IH]; intros a HM Hn; [reflexivity|].
  cbn [rdn]. pose proof (u64_range a) as Ha.
  assert (H0 : M a = None).
  { specialize (HM 0 ltac:(lia)). rewrite Z.add_0_r, Z_to_bv_bv_unsigned in HM. exact HM. }
  rewrite H0.
  destruct (seg_rom segs a) as [b|]; [|reflexivity].
  destruct n as [|n']; [reflexivity|].
  rewrite (IH (a + 1)%bv); [reflexivity| |].
  - intros i Hi. rewrite u_add1 by lia. replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (1 + i)) by lia.
    apply HM. lia.
  - rewrite u_add1 by lia. lia.
Qed.

Lemma popcnt_chain_val : forall segs E M fk x,
  know_ok segs E M fk ->
  bv_unsigned (edenot E (popcnt_chain fk x)) = swar_popc (bv_unsigned (edenot E x)).
Proof.
  intros segs E M fk x Hk. rewrite popcnt_chain_eq. unfold popcnt_chain_ref, swar_popc. cbv zeta.
  repeat ((rewrite (mkAluK_denot segs E M fk) by exact Hk) || (rewrite (mkMdK_denot segs E M fk) by exact Hk)).
  repeat (rewrite u_srl64 || rewrite u_mul64 || rewrite u_and64 || rewrite u_add64 || rewrite u_sub64).
  cbn [edenot]. rewrite !u_lit64.
  change ((1 mod two64) mod 64) with 1. change ((2 mod two64) mod 64) with 2. change ((4 mod two64) mod 64) with 4.
  change ((56 mod two64) mod 64) with 56.
  change (M55 mod two64) with M55. change (M33 mod two64) with M33. change (M0f mod two64) with M0f. change (M01 mod two64) with M01.
  change ((-2) mod two64) with MFE.
  rewrite !Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac clear_bools := repeat match goal with
                           | H : _ = true |- _ => clear H
                           | H : _ = false |- _ => clear H
                           end.
Ltac blia := clear_bools; lia.
Ltac bnia := clear_bools; nia.

Section Sound.
Variable SEGS : list Segment.
Context {RCX : rom_cache rom_load_g}.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINV_frame : forall Lc B C M M' mdl,
  AINV Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc Lc a /\ M' a <> None) -> AINV Lc B C M' mdl.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ).

Theorem node_popcnt_sound : forall args, node1_stmt always (node_popcnt args).
Proof.
  intros args. apply (add_facts_sound SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV). intros cs cs' E fx R M model HC Hn.
  unfold node_popcnt in Hn. destruct args as [|[r| | | | | | |] [|]]; try discriminate.
  destruct ((1 <=? r) && (r <=? 31))%bool; [|discriminate]. injection Hn as <-.
  eexists. split; [reflexivity|]. constructor; [|constructor].
  cbn [kentry_ok]. rewrite (popcnt_chain_val SEGS E M (facts_of (kn cs))) by (apply facts_of_ok; exact (co_know HC)).
  apply swar_popc_bound. apply u64_range.
Qed.

Theorem node_enumload_stride_sound : node1_stmt always (node_enumload_stride SEGS IT nx0).
Proof.
  intros cs cs' E fx R M model T HC _ Hn Hk.
  rewrite node_enumload_stride_eq in Hn. unfold node_enumload_stride_ref in Hn.
  destruct (itab_lookup IT (pc cs)) as [i|] eqn:Hit.
  2:{ injection Hn as <-. apply (Hk E fx R M model); [split; apply env_agree_refl | exact HC | reflexivity]. }
  destruct i as [| | | | |sz sx rd rs imm| | | | | | | | | | | | | | | | | | | | | | | | | | | | |];
    try (injection Hn as <-; apply (Hk E fx R M model); [split; apply env_agree_refl | exact HC | reflexivity]).
  set (ae := eaddz (sr_get (s_regs (a_ss cs)) rs) (bv_signed imm)) in Hn.
  destruct (xlo (kn cs) ae) as [lo|] eqn:Hxlo; [|discriminate].
  destruct (xhi (kn cs) ae) as [hi|] eqn:Hxhi; [|discriminate].
  cbv zeta in Hn.
  set (g := 2 ^ Z.min (ealign (kn cs) ae) 12) in Hn.
  set (lo' := (lo + g - 1) / g * g) in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  destruct (enum_minmax (fun i => rom_load SEGS sz sx (lo' + g * i)) 0 ((hi - lo') / g)) as [[mn mx]|] eqn:Hen; [|discriminate].
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hlen]. apply andb_prop in Hc as [Hc Hpc4]. apply andb_prop in Hc as [Hc Hpc0].
  apply andb_prop in Hc as [Hc Hrd]. apply andb_prop in Hc as [Hc Hhi64]. apply andb_prop in Hc as [Hc Hmax].
  apply andb_prop in Hc as [Hc Hlohi]. apply andb_prop in Hc as [Hc Hlo0]. apply andb_prop in Hc as [Hfresh Hcov].
  apply Z.leb_le in Hlo0. apply Z.leb_le in Hlohi. apply Z.ltb_lt in Hhi64. apply Z.leb_le in Hpc0. apply Z.ltb_lt in Hpc4.
  apply Z.leb_le in Hmax.
  apply negb_true_iff in Hrd. apply Nat.eqb_eq in Hlen. unfold two64 in Hhi64, Hpc4.
  pose proof (IT_ok _ _ Hit) as Hen2. unfold itab_entry in Hen2.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:Hec; [discriminate|].
  destruct (decode_any w) as [[i' isz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb isz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst isz.
  injection Hen2 as ->.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_regs HC) as HR.
  pose proof (co_know HC) as HK.
  assert (Haddr : v_addi (getr R rs) (bv_signed imm) = edenot E ae).
  { unfold ae, eaddz. rewrite mkAlu_denot. rewrite (HR rs). cbn [edenot]. rewrite alu_add. unfold v_addi, v_add.
    apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. }
  pose proof (xlo_sound SEGS E M (kn cs) ae lo HK Hxlo) as Blo.
  pose proof (xhi_sound SEGS E M (kn cs) ae hi HK Hxhi) as Bhi.
  (* [comment removed for export] *)
  pose proof (kimg_cover_sound SEGS E M (kn cs) lo _ HK Hcov) as Himg.
  (* [comment removed for export] *)
  assert (Hg : 0 < g).
  { subst g. apply Z.pow_pos_nonneg; [blia|]. pose proof (ealign_sound SEGS E M (kn cs) ae HK) as [Hr _]. blia. }
  assert (Hdiv : (g | bv_unsigned (edenot E ae))).
  { pose proof (ealign_sound SEGS E M (kn cs) ae HK) as [Hr Hdv]. subst g.
    destruct Hdv as [q Hq]. exists (q * 2 ^ (ealign (kn cs) ae - Z.min (ealign (kn cs) ae) 12)). rewrite Hq at 1.
    rewrite <- Z.mul_assoc, <- Z.pow_add_r by blia. f_equal. f_equal. blia. }
  set (u := bv_unsigned (edenot E ae)) in *.
  assert (Hlo'g : (g | lo')) by (exists ((lo + g - 1) / g); subst lo'; blia).
  assert (Hlo'le : lo' <= u).
  { subst lo'. destruct Hdiv as [q Hq].
    assert (Hlt : (lo + g - 1) / g < q + 1) by (apply Z.div_lt_upper_bound; [blia|bnia]).
    assert (Hq' : (lo + g - 1) / g * g <= q * g); [|blia].
    apply Z.mul_le_mono_nonneg_r; blia. }
  set (j := (u - lo') / g).
  assert (Hj : u = lo' + g * j).
  { subst j. destruct Hdiv as [q Hq]. destruct Hlo'g as [q' Hq']. rewrite Hq, Hq'.
    replace (q * g - q' * g) with ((q - q') * g) by blia. rewrite Z.div_mul by blia. blia. }
  destruct (enum_minmax_spec _ _ _ _ _ Hen j) as (val & Hval & Hb).
  { subst j. split; [apply Z.div_pos; blia | apply Z.div_le_mono; blia]. }
  cbv beta in Hval. rewrite <- Hj in Hval.
  unfold rom_load in Hval. subst u. rewrite Z_to_bv_bv_unsigned in Hval.
  destruct (rdn SEGS (fun _ => None) (edenot E ae) (GxSymStepR.msize_bytes sz)) as [bs|] eqn:Hrdn0; [|discriminate].
  injection Hval as <-.
  assert (Hrdn : rdn SEGS M (edenot E ae) (GxSymStepR.msize_bytes sz) = Some bs).
  { rewrite rdn_overlay_none; [exact Hrdn0 | | blia]. intros i Hi. apply Himg. blia. }
  pose proof (rdn_length _ _ _ _ _ Hrdn) as Hbslen.
  set (val := load_result sz sx bs) in *.
  set (v := nxt cs) in *.
  set (E' := ext1 E v val).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  set (R' := regupd R rd val).
  assert (Hstep : RiscvSemantics.step SEGS (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))
                  = MachineOk (mkstF fx R' (Z_to_bv 64 (pc cs + 4)) M (seg_rom SEGS))).
  { unfold mkstF. rewrite <- !mkstR_None.
    rewrite (stepR_load fx SEGS R _ M (seg_rom SEGS) None w sz sx rd rs imm bs Hf Hec Hd).
    - rewrite Hrd. rewrite v_addi_pc4 by assumption. reflexivity.
    - rewrite Haddr. exact Hrdn. }
  unfold cfgF.
  eapply RZ_step; [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | exact Hstep |].
  pose proof (cs_ok_agree SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC'.
  specialize (Hk E' fx R' M model (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  unfold cfgF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. unfold pc. apply Hk; [|reflexivity].
  eapply (cs_ok_frame SEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV); [exact HC' | | reflexivity | | exact (co_fx HC) |].
  - (* [comment removed for export] *) cbn [mk_ss s_regs].
    pose proof (regs_ok_agree' (nxt cs) E E' _ R Hag Fsr HR) as HR1.
    pose proof (regs_ok_upd E' (s_regs (a_ss cs)) R rd val (EVar v) HR1) as HR2.
    rewrite Hrd in HR2. apply HR2. cbn [edenot]. unfold E'. apply ext1_at.
  - (* [comment removed for export] *) cbn [mk_ss s_know]. constructor.
    + cbn [kentry_ok edenot]. unfold E'. rewrite ext1_at. exact Hb.
    + eapply know_ok_agree'; [exact Hag | exact Fkn | exact HK].
  - (* [comment removed for export] *) intros a Ha. exfalso. apply Ha. reflexivity.
Qed.

Theorem node_enumlin_sound : node1_stmt always (node_enumlin SEGS IT nx0).
Proof.
  intros cs cs' E fx R M model T HC _ Hn Hk.
  rewrite node_enumlin_eq in Hn. unfold node_enumlin_ref in Hn.
  destruct (itab_lookup IT (pc cs)) as [i|] eqn:Hit; [|discriminate].
  destruct i as [| | | | |sz sx rd rs imm| | | | | | | | | | | | | | | | | | | | | | | | | | | | |]; try discriminate.
  set (ae := eaddz (sr_get (s_regs (a_ss cs)) rs) (bv_signed imm)) in Hn.
  destruct (lin1 ae) as [[[c0 kk] x]|] eqn:Hlin; [|discriminate].
  destruct (xlo (kn cs) x) as [elo|] eqn:Hxlo; [|discriminate].
  destruct (xhi (kn cs) x) as [ehi|] eqn:Hxhi; [|discriminate].
  cbv zeta in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  set (nb := Z.of_nat (GxSymStepR.msize_bytes sz)) in Hn.
  destruct (enum_minmax (fun i => cand_load SEGS (kn cs) sz sx nb ((c0 + kk * (elo + i)) mod two64)) 0 (ehi - elo)) as [[mn mx]|] eqn:Hen; [|discriminate].
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hlen]. apply andb_prop in Hc as [Hc Hpc4]. apply andb_prop in Hc as [Hc Hpc0].
  apply andb_prop in Hc as [Hc Hrd]. apply andb_prop in Hc as [Hc Hmax]. apply andb_prop in Hc as [Hc Hlohi].
  apply andb_prop in Hc as [Hfresh Hlo0].
  apply Z.leb_le in Hlo0. apply Z.leb_le in Hlohi. apply Z.leb_le in Hpc0. apply Z.ltb_lt in Hpc4. apply Z.leb_le in Hmax.
  apply negb_true_iff in Hrd. apply Nat.eqb_eq in Hlen. unfold two64 in Hpc4.
  pose proof (IT_ok _ _ Hit) as Hen2. unfold itab_entry in Hen2.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:Hec; [discriminate|].
  destruct (decode_any w) as [[i' isz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb isz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst isz.
  injection Hen2 as ->.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_regs HC) as HR.
  pose proof (co_know HC) as HK.
  assert (Haddr : v_addi (getr R rs) (bv_signed imm) = edenot E ae).
  { unfold ae, eaddz. rewrite mkAlu_denot. rewrite (HR rs). cbn [edenot]. rewrite alu_add. unfold v_addi, v_add.
    apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. }
  (* [comment removed for export] *)
  set (u := bv_unsigned (edenot E ae)) in *.
  pose proof (xlo_sound SEGS E M (kn cs) x elo HK Hxlo) as Bxlo.
  pose proof (xhi_sound SEGS E M (kn cs) x ehi HK Hxhi) as Bxhi.
  assert (Hu : u = (c0 + kk * bv_unsigned (edenot E x)) mod two64).
  { pose proof (lin_of_sound E ae) as [q Hq]. unfold lin1 in Hlin.
    destruct (lin_of ae) as [c ts] eqn:Hlo. destruct ts as [|[k1 x1] [|]]; try discriminate.
    injection Hlin as -> -> ->. unfold lden, tden, AX2S.uE in Hq. cbn [fst snd] in Hq.
    pose proof (u64_range (edenot E ae)) as Hur. subst u. unfold two64.
    replace (c0 + kk * bv_unsigned (edenot E x)) with (bv_unsigned (edenot E ae) + q * 2 ^ 64) by (cbn [fst snd] in Hq; blia).
    rewrite Z_mod_plus_full. rewrite Z.mod_small by blia. reflexivity. }
  set (j := bv_unsigned (edenot E x) - elo).
  destruct (enum_minmax_spec _ _ _ _ _ Hen j) as (val & Hval & Hb); [subst j; blia|].
  cbv beta in Hval. replace (elo + j) with (bv_unsigned (edenot E x)) in Hval by (subst j; blia).
  rewrite <- Hu in Hval. unfold cand_load in Hval.
  match type of Hval with (if ?c then _ else _) = _ => destruct c eqn:Hcc; [|discriminate] end.
  apply andb_prop in Hcc as [Hcc Hhi64]. apply andb_prop in Hcc as [Hcov Hu0]. apply Z.ltb_lt in Hhi64. unfold two64 in Hhi64.
  pose proof (kimg_cover_sound SEGS E M (kn cs) u _ HK Hcov) as Himg.
  unfold rom_load in Hval. subst u. rewrite Z_to_bv_bv_unsigned in Hval.
  destruct (rdn SEGS (fun _ => None) (edenot E ae) (GxSymStepR.msize_bytes sz)) as [bs|] eqn:Hrdn0; [|discriminate].
  injection Hval as <-.
  assert (Hrdn : rdn SEGS M (edenot E ae) (GxSymStepR.msize_bytes sz) = Some bs).
  { rewrite rdn_overlay_none; [exact Hrdn0 | | subst nb; blia]. intros i0 Hi0. apply Himg. subst nb. blia. }
  pose proof (rdn_length _ _ _ _ _ Hrdn) as Hbslen.
  set (val := load_result sz sx bs) in *.
  set (v := nxt cs) in *.
  set (E' := ext1 E v val).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  set (R' := regupd R rd val).
  assert (Hstep : RiscvSemantics.step SEGS (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))
                  = MachineOk (mkstF fx R' (Z_to_bv 64 (pc cs + 4)) M (seg_rom SEGS))).
  { unfold mkstF. rewrite <- !mkstR_None.
    rewrite (stepR_load fx SEGS R _ M (seg_rom SEGS) None w sz sx rd rs imm bs Hf Hec Hd).
    - rewrite Hrd. rewrite v_addi_pc4 by assumption. reflexivity.
    - rewrite Haddr. exact Hrdn. }
  unfold cfgF.
  eapply RZ_step; [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | exact Hstep |].
  pose proof (cs_ok_agree SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC'.
  specialize (Hk E' fx R' M model (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  unfold cfgF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. unfold pc. apply Hk; [|reflexivity].
  eapply (cs_ok_frame SEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV); [exact HC' | | reflexivity | | exact (co_fx HC) |].
  - (* [comment removed for export] *) cbn [mk_ss s_regs].
    pose proof (regs_ok_agree' (nxt cs) E E' _ R Hag Fsr HR) as HR1.
    pose proof (regs_ok_upd E' (s_regs (a_ss cs)) R rd val (EVar v) HR1) as HR2.
    rewrite Hrd in HR2. apply HR2. cbn [edenot]. unfold E'. apply ext1_at.
  - (* [comment removed for export] *) cbn [mk_ss s_know]. constructor.
    + cbn [kentry_ok edenot]. unfold E'. rewrite ext1_at. exact Hb.
    + eapply know_ok_agree'; [exact Hag | exact Fkn | exact HK].
  - (* [comment removed for export] *) intros a Ha. exfalso. apply Ha. reflexivity.
Qed.

Theorem node_enumload_sound : node1_stmt always (node_enumload SEGS IT nx0).
Proof.
  intros cs cs' E fx R M model T HC HT Hn Hk. unfold node_enumload in Hn.
  destruct (node_enumlin SEGS IT nx0 cs) as [cs1|] eqn:H1.
  - injection Hn as <-. exact (node_enumlin_sound cs cs1 E fx R M model T HC HT H1 Hk).
  - exact (node_enumload_stride_sound cs cs' E fx R M model T HC HT Hn Hk).
Qed.

Theorem node_enumreg_sound : forall args, node1_stmt always (node_enumreg args).
Proof.
  intros args cs cs' E fx R M model T HC Hp Hn Hk. unfold node_enumreg in Hn.
  destruct args as [|[r| | | | | | |] [|s [|]]]; try discriminate.
  destruct (Z.leb 0 r && Z.leb r 31)%bool; [|discriminate].
  exact (node_enumrange_sound SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ _ cs cs' E fx R M model T HC Hp Hn Hk).
Qed.

Theorem node_havoc64_sound : forall args, node1_stmt always (node_havoc64 nx0 args).
Proof.
  intros args cs cs' E fx R M model T HC _ Hn Hk.
  unfold node_havoc64 in Hn. destruct args as [|[r| | | | | | |] [|]]; try discriminate.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hlen]. apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hr1 Hr31].
  apply Z.leb_le in Hr1. apply Z.leb_le in Hr31. apply Nat.eqb_eq in Hlen.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  set (v := nxt cs) in *.
  set (rd := (Z_to_bv 5 r : bv 5)).
  assert (Hrd : ridx rd = Z.to_nat r).
  { unfold ridx, rd. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.iter Z.mul].
    rewrite Z.mod_small by blia. reflexivity. }
  set (val := getr R rd).
  set (E' := ext1 E v val).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  pose proof (cs_ok_agree SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC'.
  specialize (Hk E' fx R M model (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  unfold pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. unfold pc. apply Hk; [|reflexivity].
  eapply (cs_ok_frame SEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV); [exact HC' | | reflexivity | | exact (co_fx HC) |].
  - (* [comment removed for export] *) cbn [mk_ss s_regs].
    pose proof (regs_ok_agree' (nxt cs) E E' _ R Hag Fsr HR) as HR1.
    rewrite <- Hrd. apply regs_ok_pin; [exact HR1|]. cbn [edenot]. unfold E'. rewrite ext1_at. reflexivity.
  - (* [comment removed for export] *) cbn [mk_ss s_know]. constructor.
    + cbn [kentry_ok edenot]. pose proof (u64_range (ev E' v)). unfold two64. blia.
    + eapply know_ok_agree'; [exact Hag | exact Fkn | exact HK].
  - (* [comment removed for export] *) intros a Ha. exfalso. apply Ha. reflexivity.
Qed.

End Sound.
End GlzNodesImg.
Module GlzCallCert.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GlzRom OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)

Section Cert.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable A : atable.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Hypothesis RUN : GPS.RUN_SOUND SEGS FXOK.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_vm : forall L B C M mdl mdl', AINVH L B C M mdl -> m_vmmaps mdl' = m_vmmaps mdl -> AINVH L B C M mdl'.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok G b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
Hypothesis G_img_hull : 0 <= g_img_lo G <= g_img_hi G /\ g_img_hi G < 2 ^ 64.
Hypothesis G_priv : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= bv_unsigned a < g_img_hi G) -> find_segment SEGS (bv_unsigned a) 1 = None.

#[local] Notation AINVf := (AINV_f (nil_of SWIN) G AINVH).   (* [comment removed for export] *)

(* [comment removed for export] *)
Variable ce : gcallee.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable LIMIT : Z.
Variable KC bfuel fuel : nat.
Variable XN : nat -> list expr -> acs -> option acs.
(* [comment removed for export] *)
Variable Q : env -> Prop.
Hypothesis Q_agree : forall E E', env_agree (ce_nxf ce) E E' -> Q E -> Q E'.
(* [comment removed for export] *)
Hypothesis XN_sound : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> Q E) ->
  GPS.ext_stmt SEGS (ce_nxf ce) XN PERMf TOPf FS0 FDS0 (AINVf PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.
(* [comment removed for export] *)
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis XB_sound : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> Q E) ->
  GPS.ext2_stmt SEGS (ce_nxf ce) XB PERMf TOPf FS0 FDS0 (AINVf PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
(* [comment removed for export] *)
Definition XC0 : xhookB := fun _ _ _ => None.
Definition HSce (h : nat) : option acs := nth_error (ce_touts ce) h.

Variable p : plan.
Variable s : shape.
Hypothesis p_ok : gplan_ok p = true.
Hypothesis s_ok : holes_only s = true.
Hypothesis CERT : AP.check SEGS IT A (ce_nxf ce) LIMIT XN XE0 XB XC0 HSce KC bfuel fuel None (ce_tin ce) p = COk s.

Lemma sd_holes_only : forall (T : TSet) E fs sh, holes_only sh = true -> sd (fun _ _ _ => T) T E fs sh = T.
Proof.
  intros T E fs sh. induction sh; cbn [holes_only sd]; intros H; try discriminate; try reflexivity.
  apply andb_prop in H as [H1 H2]. destruct (Z.leb _ _); [apply IHsh1; exact H1 | apply IHsh2; exact H2].
Qed.

Theorem contract_of_cert_when : callee_contract_when SEGS SWIN G FXOK RZ AINVH Q ce.
Proof.
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 E fx R M mdl T HB0 HC0 HBc HCc HQ HC HT Hexits.
  set (UINV := fun E' => env_agree (ce_nxf ce) E E').
  assert (UINV_agree : forall E1 E2, env_agree (ce_nxf ce) E1 E2 -> UINV E1 -> UINV E2).
  { intros E1 E2 H12 H1. unfold UINV in *. eapply env_agree_trans; [exact H1 | exact H12]. }
  assert (UINV_Q : forall E1, UINV E1 -> Q E1).
  { intros E1 H1. eapply Q_agree; [exact H1 | exact HQ]. }
  assert (HSs : GPS.holes_stmt SEGS HSce PERMf TOPf FS0 FDS0 (AINVf PERMf TOPf HID M0 B0 C0) FXOK UINV (fun _ _ _ => T) RZ).
  { intros h ch Hh E1 fx1 R1 M1 mdl1 HC1. unfold HSce in Hh.
    apply (Hexits ch E1 fx1 R1 M1 mdl1).
    - eapply nth_error_In. exact Hh.
    - exact (co_uinv HC1).
    - destruct HC1; constructor; try assumption. exact I.
    - rewrite (co_fs HC1). symmetry. exact (co_fs HC). }
  pose proof (GPS.check_sound SEGS IT IT_ok A (ce_nxf ce) LIMIT HSce XN XE0 XB XC0 KC (nil_of SWIN) PERMf TOPf FS0 FDS0
                (AINVf PERMf TOPf HID M0 B0 C0)
                (AINV_f_frame (nil_of SWIN) G AINVH (AINVH_frame_nil SWIN AINVH AINVH_frame) AINVH_zone AINVH_disj G_ro_img G_img_ceil PERMf TOPf HID M0 B0 C0)
                FXOK UINV UINV_agree (fun _ _ _ => T) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => HT) (fun _ _ _ => eq_refl)
                RZ RZ_step RZ_msteps RZ_exit RZ_conseq RUN SEGS_in_hull HULL_ok
                (XN_sound PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc UINV_agree UINV_Q)
                ltac:(intros id args cs fd ps cs' E1 fx1 R1 M1 m1 T1 _ Hn; discriminate Hn)
                (XB_sound PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc UINV_agree UINV_Q)
                ltac:(intros id args cs csa csb E2 fx2 R2 M2 m2 Ta Tb _ Hnn; discriminate Hnn)
                HSs fuel bfuel None p (ce_tin ce) s p_ok CERT E fx R M mdl T) as X.
  rewrite (sd_holes_only T E (m_fs mdl) s s_ok) in X.
  apply X.
  - destruct HC; constructor; try assumption. unfold UINV. apply env_agree_refl.
  - exact I.
  - exact HT.
Qed.

End Cert.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CertCut.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable A : atable.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Hypothesis RUN : GPS.RUN_SOUND SEGS FXOK.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok G b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
Hypothesis G_img_hull : 0 <= g_img_lo G <= g_img_hi G /\ g_img_hi G < 2 ^ 64.
#[local] Notation AINVf := (AINV_f (nil_of SWIN) G AINVH).   (* [comment removed for export] *)
Variable ce : gcallee.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable LIMIT : Z.
Variable KC bfuel fuel : nat.
Variable XN : nat -> list expr -> acs -> option acs.
Variable Q : env -> Prop.
Hypothesis Q_agree : forall E E', env_agree (ce_nxf ce) E E' -> Q E -> Q E'.
Hypothesis XN_sound : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> Q E) ->
  GPS.ext_stmt SEGS (ce_nxf ce) XN PERMf TOPf FS0 FDS0 (AINVf PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis XB_sound : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> Q E) ->
  GPS.ext2_stmt SEGS (ce_nxf ce) XB PERMf TOPf FS0 FDS0 (AINVf PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.

(* [comment removed for export] *)
Variable CUTS : list (acs * plan).
Definition NT : nat := length (ce_touts ce).
Definition HScut (k : nat) (h : nat) : option acs :=
  if Nat.ltb h NT then nth_error (ce_touts ce) h
  else let i := (h - NT)%nat in
       if Nat.leb k i then match nth_error CUTS i with Some c => Some (fst c) | None => None end else None.
Hypothesis CUTS_ok : forall i T k, nth_error CUTS i = Some (T, k) -> exists sh,
  gplan_ok k = true /\ holes_only sh = true /\
  AP.check SEGS IT A (ce_nxf ce) LIMIT XN XE0 XB XC0 (HScut (S i)) KC bfuel fuel None T k = COk sh.
Variable p : plan.
Variable s : shape.
Hypothesis p_ok : gplan_ok p = true.
Hypothesis s_ok : holes_only s = true.
Hypothesis CERT : AP.check SEGS IT A (ce_nxf ce) LIMIT XN XE0 XB XC0 (HScut 0) KC bfuel fuel None (ce_tin ce) p = COk s.

Theorem contract_of_cert_when_cut : callee_contract_when SEGS SWIN G FXOK RZ AINVH Q ce.
Proof.
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 E fx R M mdl T HB0 HC0 HBc HCc HQ HC HT Hexits.
  set (UINV := fun E' => env_agree (ce_nxf ce) E E').
  assert (UINV_agree : forall E1 E2, env_agree (ce_nxf ce) E1 E2 -> UINV E1 -> UINV E2).
  { intros E1 E2 H12 H1. unfold UINV in *. eapply env_agree_trans; [exact H1 | exact H12]. }
  assert (UINV_Q : forall E1, UINV E1 -> Q E1).
  { intros E1 H1. eapply Q_agree; [exact H1 | exact HQ]. }
  (* [comment removed for export] *)
  #[local] Ltac exit_hole Hexits Hh HC1 HC :=
    match type of HC1 with GPS.cs_ok _ _ _ _ _ _ _ _ ?E1 ?ch ?fx1 ?R1 ?M1 ?mdl1 =>
      apply (Hexits ch E1 fx1 R1 M1 mdl1); [eapply nth_error_In; exact Hh | exact (co_uinv HC1)
                   | destruct HC1; constructor; try assumption; exact I
                   | rewrite (co_fs HC1); symmetry; exact (co_fs HC)] end.
  assert (HSall : forall d k, (length CUTS <= k + d)%nat ->
            GPS.holes_stmt SEGS (HScut k) PERMf TOPf FS0 FDS0 (AINVf PERMf TOPf HID M0 B0 C0) FXOK UINV (fun _ _ _ => T) RZ).
  { induction d as [|d IHd]; intros k Hk h ch Hh E1 fx1 R1 M1 mdl1 HC1; unfold HScut in Hh.
    - destruct (Nat.ltb h NT) eqn:Hlt; [exit_hole Hexits Hh HC1 HC|].
      destruct (Nat.leb k (h - NT)) eqn:Hle; [|discriminate]. apply Nat.leb_le in Hle.
      destruct (nth_error CUTS (h - NT)) as [c|] eqn:Hn; [|discriminate].
      exfalso. assert (Hl : (h - NT < length CUTS)%nat) by (apply nth_error_Some; rewrite Hn; discriminate). lia.
    - destruct (Nat.ltb h NT) eqn:Hlt; [exit_hole Hexits Hh HC1 HC|].
      destruct (Nat.leb k (h - NT)) eqn:Hle; [|discriminate]. apply Nat.leb_le in Hle.
      destruct (nth_error CUTS (h - NT)) as [[Tc kc]|] eqn:Hn; [|discriminate]. cbn [fst] in Hh. injection Hh as <-.
      destruct (Nat.eq_dec (h - NT) k) as [Heq|Hne].
      + (* [comment removed for export] *)
        destruct (CUTS_ok (h - NT)%nat Tc kc Hn) as (sc & Hgp & Hho & Hck).
        pose proof (GPS.check_sound SEGS IT IT_ok A (ce_nxf ce) LIMIT (HScut (S (h - NT))) XN XE0 XB XC0 KC (nil_of SWIN) PERMf TOPf FS0 FDS0
                      (AINVf PERMf TOPf HID M0 B0 C0)
                      (AINV_f_frame (nil_of SWIN) G AINVH (AINVH_frame_nil SWIN AINVH AINVH_frame) AINVH_zone AINVH_disj G_ro_img G_img_ceil PERMf TOPf HID M0 B0 C0)
                      FXOK UINV UINV_agree (fun _ _ _ => T) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => HT) (fun _ _ _ => eq_refl)
                      RZ RZ_step RZ_msteps RZ_exit RZ_conseq RUN SEGS_in_hull HULL_ok
                      (XN_sound PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc UINV_agree UINV_Q)
                      ltac:(intros id args cs fd ps cs' E2 fx2 R2 M2 m2 T2 _ Hnn; discriminate Hnn)
                      (XB_sound PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc UINV_agree UINV_Q)
                      ltac:(intros id args cs csa csb E2 fx2 R2 M2 m2 Ta Tb _ Hnn; discriminate Hnn)
                      (IHd (S (h - NT)) ltac:(lia)) fuel bfuel None kc Tc sc Hgp Hck E1 fx1 R1 M1 mdl1 T) as X.
        rewrite (sd_holes_only T E1 (m_fs mdl1) sc Hho) in X.
        apply X; [exact HC1 | exact I | exact HT].
      + (* [comment removed for export] *)
        refine (IHd (S k) ltac:(lia) h Tc _ E1 fx1 R1 M1 mdl1 HC1).
        unfold HScut. rewrite Hlt. replace (Nat.leb (S k) (h - NT)) with true by (symmetry; apply Nat.leb_le; lia).
        rewrite Hn. reflexivity. }
  pose proof (GPS.check_sound SEGS IT IT_ok A (ce_nxf ce) LIMIT (HScut 0) XN XE0 XB XC0 KC (nil_of SWIN) PERMf TOPf FS0 FDS0
                (AINVf PERMf TOPf HID M0 B0 C0)
                (AINV_f_frame (nil_of SWIN) G AINVH (AINVH_frame_nil SWIN AINVH AINVH_frame) AINVH_zone AINVH_disj G_ro_img G_img_ceil PERMf TOPf HID M0 B0 C0)
                FXOK UINV UINV_agree (fun _ _ _ => T) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => HT) (fun _ _ _ => eq_refl)
                RZ RZ_step RZ_msteps RZ_exit RZ_conseq RUN SEGS_in_hull HULL_ok
                (XN_sound PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc UINV_agree UINV_Q)
                ltac:(intros id args cs fd ps cs' E1 fx1 R1 M1 m1 T1 _ Hn; discriminate Hn)
                (XB_sound PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc UINV_agree UINV_Q)
                ltac:(intros id args cs csa csb E2 fx2 R2 M2 m2 Ta Tb _ Hnn; discriminate Hnn)
                (HSall (length CUTS) 0%nat ltac:(lia)) fuel bfuel None p (ce_tin ce) s p_ok CERT E fx R M mdl T) as X.
  rewrite (sd_holes_only T E (m_fs mdl) s s_ok) in X.
  apply X.
  - destruct HC; constructor; try assumption. unfold UINV. apply env_agree_refl.
  - exact I.
  - exact HT.
Qed.
End CertCut.

(* [comment removed for export] *)
Theorem contract_of_cert :
  forall SEGS {RC : run_ceil} A, (forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None) ->
  APS.hull_ok A -> forall SWIN G FXOK (RZ : GPS.rz_t),
  GPS.RZ_STEP SEGS RZ -> GPS.RZ_MSTEPS SEGS RZ -> GPS.RZ_EXIT SEGS RZ -> GPS.RZ_CONSEQ RZ -> GPS.RUN_SOUND SEGS FXOK ->
  forall AINVH,
  (forall L B C M M' mdl, AINVH L B C M mdl ->
     (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
     AINVH L B C M' mdl) ->
  (forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok G b m) ->
  (forall L B C M mdl L1 L2 b m b' m', AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b) ->
  g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G -> g_img_hi G <= CEIL_run ->
  forall ce IT, itab_sound SEGS IT -> forall LIMIT KC bfuel fuel XN,
  (forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
     0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
     (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
     GPS.ext_stmt SEGS (ce_nxf ce) XN PERMf TOPf FS0 FDS0 (AINV_f (nil_of SWIN) G AINVH PERMf TOPf HID M0 B0 C0) FXOK UINV RZ) ->
  forall p s, gplan_ok p = true -> holes_only s = true ->
  AP.check SEGS IT A (ce_nxf ce) LIMIT XN XE0 XB0 XC0 (HSce ce) KC bfuel fuel None (ce_tin ce) p = COk s ->
  callee_contract SEGS SWIN G FXOK RZ AINVH ce.
Proof.
  intros SEGS RC A Hh Hk SWIN G FXOK RZ RZs RZm RZe RZc RUN AINVH A1 A3 A4 G1 G2 ce IT ITok LIMIT KC bfuel fuel XN XNs p s Hp Hs CERT.
  unfold callee_contract.
  unshelve (eapply (contract_of_cert_when SEGS A Hh Hk SWIN G FXOK RZ RZs RZm RZe RZc RUN AINVH A1 A3 A4 G1 G2 ce IT ITok LIMIT KC bfuel fuel XN QTRUE _ _ XB0 _ p s Hp Hs CERT)).
  all: first [ exact Hp | exact Hs | exact CERT | (intros; exact I) | (intros; eapply XNs; eassumption)
             | (intros; intros id args cs csa csb E1 fx1 R1 M1 m1 T1 HC1 Hn; discriminate Hn) ].
Qed.

(* [comment removed for export] *)
Theorem contract_of_cert_xb :
  forall SEGS {RC : run_ceil} A, (forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None) ->
  APS.hull_ok A -> forall SWIN G FXOK (RZ : GPS.rz_t),
  GPS.RZ_STEP SEGS RZ -> GPS.RZ_MSTEPS SEGS RZ -> GPS.RZ_EXIT SEGS RZ -> GPS.RZ_CONSEQ RZ -> GPS.RUN_SOUND SEGS FXOK ->
  forall AINVH,
  (forall L B C M M' mdl, AINVH L B C M mdl ->
     (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
     AINVH L B C M' mdl) ->
  (forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok G b m) ->
  (forall L B C M mdl L1 L2 b m b' m', AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b) ->
  g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G -> g_img_hi G <= CEIL_run ->
  forall ce IT, itab_sound SEGS IT -> forall LIMIT KC bfuel fuel XN,
  (forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
     0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
     (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
     GPS.ext_stmt SEGS (ce_nxf ce) XN PERMf TOPf FS0 FDS0 (AINV_f (nil_of SWIN) G AINVH PERMf TOPf HID M0 B0 C0) FXOK UINV RZ) ->
  forall XB,
  (forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
     0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
     (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
     GPS.ext2_stmt SEGS (ce_nxf ce) XB PERMf TOPf FS0 FDS0 (AINV_f (nil_of SWIN) G AINVH PERMf TOPf HID M0 B0 C0) FXOK UINV RZ) ->
  forall p s, gplan_ok p = true -> holes_only s = true ->
  AP.check SEGS IT A (ce_nxf ce) LIMIT XN XE0 XB XC0 (HSce ce) KC bfuel fuel None (ce_tin ce) p = COk s ->
  callee_contract SEGS SWIN G FXOK RZ AINVH ce.
Proof.
  intros SEGS RC A Hh Hk SWIN G FXOK RZ RZs RZm RZe RZc RUN AINVH A1 A3 A4 G1 G2 ce IT ITok LIMIT KC bfuel fuel XN XNs XB XBs p s Hp Hs CERT.
  unfold callee_contract.
  unshelve (eapply (contract_of_cert_when SEGS A Hh Hk SWIN G FXOK RZ RZs RZm RZe RZc RUN AINVH A1 A3 A4 G1 G2 ce IT ITok LIMIT KC bfuel fuel XN QTRUE _ _ XB _ p s Hp Hs CERT)).
  all: first [ exact Hp | exact Hs | exact CERT | (intros; exact I) | (intros; eapply XNs; eassumption) | (intros; eapply XBs; eassumption) ].
Qed.

(* [comment removed for export] *)
Theorem contract_of_cert_xb_cut :
  forall SEGS {RC : run_ceil} A, (forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None) ->
  APS.hull_ok A -> forall SWIN G FXOK (RZ : GPS.rz_t),
  GPS.RZ_STEP SEGS RZ -> GPS.RZ_MSTEPS SEGS RZ -> GPS.RZ_EXIT SEGS RZ -> GPS.RZ_CONSEQ RZ -> GPS.RUN_SOUND SEGS FXOK ->
  forall AINVH,
  (forall L B C M M' mdl, AINVH L B C M mdl ->
     (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
     AINVH L B C M' mdl) ->
  (forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok G b m) ->
  (forall L B C M mdl L1 L2 b m b' m', AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b) ->
  g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G -> g_img_hi G <= CEIL_run ->
  forall ce IT, itab_sound SEGS IT -> forall LIMIT KC bfuel fuel XN,
  (forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
     0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
     (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
     GPS.ext_stmt SEGS (ce_nxf ce) XN PERMf TOPf FS0 FDS0 (AINV_f (nil_of SWIN) G AINVH PERMf TOPf HID M0 B0 C0) FXOK UINV RZ) ->
  forall XB,
  (forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
     0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
     (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
     GPS.ext2_stmt SEGS (ce_nxf ce) XB PERMf TOPf FS0 FDS0 (AINV_f (nil_of SWIN) G AINVH PERMf TOPf HID M0 B0 C0) FXOK UINV RZ) ->
  forall (CUTS : list (acs * plan)),
  (forall i T k, nth_error CUTS i = Some (T, k) -> exists sh,
     gplan_ok k = true /\ holes_only sh = true /\
     AP.check SEGS IT A (ce_nxf ce) LIMIT XN XE0 XB XC0 (HScut ce CUTS (S i)) KC bfuel fuel None T k = COk sh) ->
  forall p s, gplan_ok p = true -> holes_only s = true ->
  AP.check SEGS IT A (ce_nxf ce) LIMIT XN XE0 XB XC0 (HScut ce CUTS 0) KC bfuel fuel None (ce_tin ce) p = COk s ->
  callee_contract SEGS SWIN G FXOK RZ AINVH ce.
Proof.
  intros SEGS RC A Hh Hk SWIN G FXOK RZ RZs RZm RZe RZc RUN AINVH A1 A3 A4 G1 G2 ce IT ITok LIMIT KC bfuel fuel XN XNs XB XBs CUTS Hcuts p s Hp Hs CERT.
  unfold callee_contract.
  unshelve (eapply (contract_of_cert_when_cut SEGS A Hh Hk SWIN G FXOK RZ RZs RZm RZe RZc RUN AINVH A1 A3 A4 G1 G2 ce IT ITok LIMIT KC bfuel fuel XN QTRUE _ _ XB _ CUTS Hcuts p s Hp Hs CERT)).
  all: first [ exact Hp | exact Hs | exact CERT | (intros; exact I) | (intros; eapply XNs; eassumption) | (intros; eapply XBs; eassumption) ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Hooks.
Variable SEGS : list Segment.
Context {RCX : GlzRom.rom_cache rom_load_g}.   (* [comment removed for export] *)
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable IT : itab.
Variable A : atable.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis IT_ok : itab_sound SEGS IT.       (* [comment removed for export] *)
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable bcap ccap : Z.
Variable FXOK : FX -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok G b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
Hypothesis G_img_hull : 0 <= g_img_lo G <= g_img_hi G /\ g_img_hi G < 2 ^ 64.
Hypothesis G_priv : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= bv_unsigned a < g_img_hi G) -> find_segment SEGS (bv_unsigned a) 1 = None.
(* [comment removed for export] *)
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable HIDc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Hypothesis bcap_ok : B0c + bcap <= GBUDGET.
Hypothesis ccap_ok : C0c + ccap <= GCOUNT.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
#[local] Notation AINVc := (AINV_f SWIN G AINVH PERMc SPTOPc HIDc M0c B0c C0c).

(* [comment removed for export] *)
Variable CT : nat -> option gcallee.
Hypothesis CT_sound : forall id ce, CT id = Some ce -> callee_contract SEGS SWIN G FXOK RZ AINVH ce.

Definition XNc (id : nat) (args : list expr) (cs : acs) : option acs :=
  match CT id with
  | Some ce => node_call SEGS A nx0 bcap ccap G ce args cs
  | None =>
      match id with      (* [comment removed for export] *)
      | 42%nat => node_enumload SEGS IT nx0 cs
      | 43%nat => node_popcnt args cs
      | 44%nat => node_havoc64 nx0 args cs
      | 45%nat => node_enumreg args cs
      | _ => XNg SEGS IT A nx0 G bcap ccap id args cs
      end
  end.

Theorem XNc_sound :
  gcontracts SEGS IT A nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ G bcap ccap ->
  GPS.ext_stmt SEGS nx0 XNc PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ.
Proof.
  intros GCs id args. unfold XNc. destruct (CT id) as [ce|] eqn:Hct.
  - exact (node_call_sound SEGS A SEGS_in_hull HULL_ok SWIN G FXOK RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm G_ro_img G_img_ceil G_img_hull SWIN_img SEGS_out
             nx0 PERMc SPTOPc FS0 FDS0 HIDc M0c B0c C0c B0c_nonneg C0c_nonneg bcap ccap bcap_ok ccap_ok UINV UINV_agree
             ce args (CT_sound id ce Hct)).
  - pose proof (AINV_f_frame SWIN G AINVH AINVH_frame AINVH_zone AINVH_disj G_ro_img G_img_ceil PERMc SPTOPc HIDc M0c B0c C0c) as AF.
    do 42 (destruct id as [|id]; [exact (XNg_sound SEGS IT A nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ G bcap ccap GCs _ args)|]).
    destruct id as [|id]; [apply GPS.node1_stmt_N; exact (node_enumload_sound SEGS IT IT_ok nx0 SWIN PERMc SPTOPc FS0 FDS0 AINVc AF FXOK UINV UINV_agree RZ RZ_step)|].
    destruct id as [|id]; [apply GPS.node1_stmt_N; exact (node_popcnt_sound SEGS nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ args)|].
    destruct id as [|id]; [apply GPS.node1_stmt_N; exact (node_havoc64_sound SEGS nx0 SWIN PERMc SPTOPc FS0 FDS0 AINVc AF FXOK UINV UINV_agree RZ args)|].
    destruct id as [|id]; [apply GPS.node1_stmt_N; exact (node_enumreg_sound SEGS nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ args)|].
    exact (XNg_sound SEGS IT A nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ G bcap ccap GCs _ args).
Qed.

(* [comment removed for export] *)
Variable CT2 : nat -> option gcallee2.
Hypothesis CT2_sound : forall id c, CT2 id = Some c -> callee_contract SEGS SWIN G FXOK RZ AINVH (c2_merged c).
Definition XBc (id : nat) (args : list expr) (cs : acs) : option (acs * acs) :=
  match CT2 id with
  | Some c => node_call2 SEGS A nx0 bcap ccap G c args cs
  | None => XBg SEGS nx0 G bcap ccap id args cs
  end.
Theorem XBc_sound :
  OBL_str_resize2 SEGS nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ G bcap ccap ->
  GPS.ext2_stmt SEGS nx0 XBc PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ.
Proof.
  intros OB id args. unfold XBc. destruct (CT2 id) as [c|] eqn:Hct.
  - exact (node_call2_sound SEGS A SEGS_in_hull HULL_ok SWIN G FXOK RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm G_ro_img G_img_ceil G_img_hull SWIN_img SEGS_out
             nx0 PERMc SPTOPc FS0 FDS0 HIDc M0c B0c C0c B0c_nonneg C0c_nonneg bcap ccap bcap_ok ccap_ok UINV UINV_agree
             c args (CT2_sound id c Hct)).
  - exact (XBg_sound SEGS nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ G bcap ccap OB id args).
Qed.
End Hooks.
End GlzCallCert.
Module GlzCallRec.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition DMEAS (i : nat) (E : env) : Z := 2 ^ 64 - bv_unsigned (ev E i).
Definition Qd (i : nat) (n : Z) (E : env) : Prop := DMEAS i E <= n.

Lemma Qd_agree : forall i nxf n E E', (i < nxf)%nat -> env_agree nxf E E' -> Qd i n E -> Qd i n E'.
Proof. intros i nxf n E E' Hi [Hag _] H. unfold Qd, DMEAS in *. rewrite <- (Hag i Hi). exact H. Qed.

(* [comment removed for export] *)
Definition rec_cond (i nxf : nat) (cs : acs) (th : list expr) : bool :=
  (Nat.eqb (length th) nxf && Nat.ltb i nxf &&
   let '(b, c) := split_lit (nth i th (ELit 0)) in
   expr_eqb b (EVar i) && Z.leb 1 c
   && match xhi (kn cs) (EVar i) with Some h => Z.ltb (h + c) two64 | None => false end)%bool.

Section Rec.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable IT : itab.
Variable A : atable.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok G b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
Hypothesis G_img_hull : 0 <= g_img_lo G <= g_img_hi G /\ g_img_hi G < 2 ^ 64.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= bv_unsigned a < g_img_hi G) -> find_segment SEGS (bv_unsigned a) 1 = None.
#[local] Notation AINVf := (AINV_f SWIN G AINVH).
#[local] Notation AINV0 := (AINV_f (nil_of SWIN) G AINVH).   (* [comment removed for export] *)

Definition callee_contract_upto (i : nat) (n : Z) (ce : gcallee) : Prop :=
  callee_contract_when SEGS SWIN G FXOK RZ AINVH (Qd i n) ce.

Lemma callee_contract_of_upto : forall i ce,
  (forall n, 0 <= n -> callee_contract_upto i n ce) -> callee_contract SEGS SWIN G FXOK RZ AINVH ce.
Proof.
  intros i ce H. unfold callee_contract.
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 E fx R M mdl T HB0 HC0 HBc HCc _ HC HT Hex.
  apply (H (2 ^ 64) ltac:(lia) PERMf TOPf HID M0 B0 C0 FS0 FDS0 E fx R M mdl T HB0 HC0 HBc HCc); try assumption.
  unfold Qd, DMEAS. pose proof (u64_range (ev E i)). lia.
Qed.

(* [comment removed for export] *)
Section Caller.
Variable nx0 : nat.
Variable bcap ccap : Z.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable HIDc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Hypothesis bcap_ok : B0c + bcap <= GBUDGET.
Hypothesis ccap_ok : C0c + ccap <= GCOUNT.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
#[local] Notation AINVc := (AINVf PERMc SPTOPc HIDc M0c B0c C0c).

Definition node_callrec (i : nat) (ce : gcallee) (args : list expr) (cs : acs) : option acs :=
  node_call_cond SEGS A G nx0 bcap ccap (rec_cond i (ce_nxf ce)) ce args cs.

Theorem node_callrec_sound : forall i n ce args,
  callee_contract_upto i n ce ->
  (forall E, UINV E -> DMEAS i E <= n + 1) ->
  GPS.node1_stmtN SEGS nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ always (node_callrec i ce args).
Proof.
  intros i n ce args CC HU. unfold node_callrec.
  apply (node_call_cond_sound SEGS A SEGS_in_hull HULL_ok SWIN G FXOK RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm G_ro_img G_img_ceil G_img_hull SWIN_img SEGS_out
           nx0 PERMc SPTOPc FS0 FDS0 HIDc M0c B0c C0c B0c_nonneg C0c_nonneg bcap ccap bcap_ok ccap_ok UINV UINV_agree
           (Qd i n) (rec_cond i (ce_nxf ce)) ce args CC).
  intros cs th E fx R M model Hbind Hc HC. unfold rec_cond in Hc.
  apply andb_prop in Hc as [H12 Hlet]. apply andb_prop in H12 as [Hlen Hi].
  destruct (split_lit (nth i th (ELit 0))) as [b c] eqn:Hsp.
  apply andb_prop in Hlet as [Hlet Hx]. apply andb_prop in Hlet as [Hb H1].
  apply Nat.eqb_eq in Hlen. apply Nat.ltb_lt in Hi. apply expr_eqb_eq in Hb. subst b. apply Z.leb_le in H1.
  destruct (xhi (kn cs) (EVar i)) as [h|] eqn:Hh; [|discriminate]. apply Z.ltb_lt in Hx.
  pose proof (xhi_sound SEGS E M (kn cs) (EVar i) h (co_know HC) Hh) as Hhi. cbn [edenot] in Hhi.
  pose proof (HU E (co_uinv HC)) as HD.
  unfold Qd, DMEAS in *. cbn [tenv ev]. rewrite Hlen.
  replace (Nat.ltb i (ce_nxf ce)) with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  rewrite (split_lit_denot E (nth i th (ELit 0)) (EVar i) c Hsp). cbn [edenot].
  pose proof (u64_range (ev E i)). unfold two64 in Hx. rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Definition node_callrec2 (i : nat) (c : gcallee2) (args : list expr) (cs : acs) : option (acs * acs) :=
  node_call2_cond SEGS A nx0 bcap ccap G (rec_cond i (c2_nxf c)) c args cs.

Theorem node_callrec2_sound : forall i n c args,
  callee_contract_upto i n (c2_merged c) ->
  (forall E, UINV E -> DMEAS i E <= n + 1) ->
  node2_stmt SEGS nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ (node_callrec2 i c args).
Proof.
  intros i n c args CC HU. unfold node_callrec2.
  apply (node_call2_cond_sound SEGS A SEGS_in_hull HULL_ok SWIN G FXOK RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm G_ro_img G_img_ceil G_img_hull SWIN_img SEGS_out
           nx0 PERMc SPTOPc FS0 FDS0 HIDc M0c B0c C0c B0c_nonneg C0c_nonneg bcap ccap bcap_ok ccap_ok UINV UINV_agree
           (Qd i n) (rec_cond i (c2_nxf c)) c args CC).
  intros cs th E fx R M model Hbind Hc HC. unfold rec_cond in Hc.
  apply andb_prop in Hc as [H12 Hlet]. apply andb_prop in H12 as [Hlen Hi].
  destruct (split_lit (nth i th (ELit 0))) as [b c'] eqn:Hsp.
  apply andb_prop in Hlet as [Hlet Hx]. apply andb_prop in Hlet as [Hb H1].
  apply Nat.eqb_eq in Hlen. apply Nat.ltb_lt in Hi. apply expr_eqb_eq in Hb. subst b. apply Z.leb_le in H1.
  destruct (xhi (kn cs) (EVar i)) as [h|] eqn:Hh; [|discriminate]. apply Z.ltb_lt in Hx.
  pose proof (xhi_sound SEGS E M (kn cs) (EVar i) h (co_know HC) Hh) as Hhi. cbn [edenot] in Hhi.
  pose proof (HU E (co_uinv HC)) as HD.
  unfold Qd, DMEAS in *. cbn [tenv ev]. cbn [c2_nxf c2_class0 ce_nxf] in Hlen. rewrite Hlen.
  replace (Nat.ltb i (c2_nxf c)) with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  rewrite (split_lit_denot E (nth i th (ELit 0)) (EVar i) c' Hsp). cbn [edenot].
  pose proof (u64_range (ev E i)). unfold two64 in Hx. rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Variable self_id : nat.
Variable idepth : nat.
Variable ce_self : gcallee.
Variable CT : nat -> option gcallee.
Hypothesis CT_sound : forall id ce, CT id = Some ce -> callee_contract SEGS SWIN G FXOK RZ AINVH ce.

Definition XNr (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id self_id then node_callrec idepth ce_self args cs
  else XNc SEGS IT A nx0 G bcap ccap CT id args cs.

Theorem XNr_sound : forall n,
  gcontracts SEGS IT A nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ G bcap ccap ->
  callee_contract_upto idepth n ce_self ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  GPS.ext_stmt SEGS nx0 XNr PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ.
Proof.
  intros n GCs CC HU id args. unfold XNr. destruct (Nat.eqb id self_id).
  - exact (node_callrec_sound idepth n ce_self args CC HU).
  - exact (XNc_sound SEGS IT A SEGS_in_hull HULL_ok IT_ok nx0 SWIN G bcap ccap FXOK RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm G_ro_img G_img_ceil G_img_hull SWIN_img SEGS_out
             PERMc SPTOPc FS0 FDS0 HIDc M0c B0c C0c B0c_nonneg C0c_nonneg bcap_ok ccap_ok UINV UINV_agree CT CT_sound GCs id args).
Qed.

(* [comment removed for export] *)
Variable self2_id : nat.
Variable c2_self : gcallee2.
Variable CT2 : nat -> option gcallee2.
Hypothesis CT2_sound : forall id c, CT2 id = Some c -> callee_contract SEGS SWIN G FXOK RZ AINVH (c2_merged c).

Definition XBr (id : nat) (args : list expr) (cs : acs) : option (acs * acs) :=
  if Nat.eqb id self2_id then node_callrec2 idepth c2_self args cs
  else XBc SEGS A nx0 G bcap ccap CT2 id args cs.

Theorem XBr_sound : forall n,
  OBL_str_resize2 SEGS nx0 PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ G bcap ccap ->
  callee_contract_upto idepth n (c2_merged c2_self) ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  GPS.ext2_stmt SEGS nx0 XBr PERMc SPTOPc FS0 FDS0 AINVc FXOK UINV RZ.
Proof.
  intros n OB CC HU id args. unfold XBr. destruct (Nat.eqb id self2_id).
  - exact (node_callrec2_sound idepth n c2_self args CC HU).
  - exact (XBc_sound SEGS A SEGS_in_hull HULL_ok nx0 SWIN G bcap ccap FXOK RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm G_ro_img G_img_ceil G_img_hull SWIN_img SEGS_out
             PERMc SPTOPc FS0 FDS0 HIDc M0c B0c C0c B0c_nonneg C0c_nonneg bcap_ok ccap_ok UINV UINV_agree CT2 CT2_sound OB id args).
Qed.
End Caller.

(* [comment removed for export] *)
Section Cert.
Variable ce : gcallee.
Variable idepth : nat.
Hypothesis idepth_lt : (idepth < ce_nxf ce)%nat.
Hypothesis RUN : GPS.RUN_SOUND SEGS FXOK.
Variable LIMIT : Z.
Variable KC bfuel fuel : nat.
Variable XN : nat -> list expr -> acs -> option acs.
(* [comment removed for export] *)
Hypothesis XN_sound_rec : forall n PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= n ->
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  callee_contract_upto idepth n ce ->
  GPS.ext_stmt SEGS (ce_nxf ce) XN PERMf TOPf FS0 FDS0 (AINV0 PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.
Variable p : plan.
Variable s : shape.
Hypothesis p_ok : gplan_ok p = true.
Hypothesis s_ok : holes_only s = true.
(* [comment removed for export] *)
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis XB_sound_rec : forall n PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= n -> 0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  callee_contract_upto idepth n ce ->
  GPS.ext2_stmt SEGS (ce_nxf ce) XB PERMf TOPf FS0 FDS0 (AINV0 PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.
Hypothesis CERT : AP.check SEGS IT A (ce_nxf ce) LIMIT XN XE0 XB XC0 (HSce ce) KC bfuel fuel None (ce_tin ce) p = COk s.


End Cert.

(* [comment removed for export] *)
Section CertCut.
Variable ce : gcallee.
Variable idepth : nat.
Hypothesis idepth_lt : (idepth < ce_nxf ce)%nat.
Hypothesis RUN : GPS.RUN_SOUND SEGS FXOK.
Variable LIMIT : Z.
Variable KC bfuel fuel : nat.
Variable XN : nat -> list expr -> acs -> option acs.
(* [comment removed for export] *)
Hypothesis XN_sound_rec : forall n PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= n ->
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  callee_contract_upto idepth n ce ->
  GPS.ext_stmt SEGS (ce_nxf ce) XN PERMf TOPf FS0 FDS0 (AINV0 PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.
Variable p : plan.
Variable s : shape.
Hypothesis p_ok : gplan_ok p = true.
Hypothesis s_ok : holes_only s = true.
(* [comment removed for export] *)
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis XB_sound_rec : forall n PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= n -> 0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  callee_contract_upto idepth n ce ->
  GPS.ext2_stmt SEGS (ce_nxf ce) XB PERMf TOPf FS0 FDS0 (AINV0 PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.
Variable CUTS : list (acs * plan).
Hypothesis CUTS_ok : forall i T k, nth_error CUTS i = Some (T, k) -> exists sh,
  gplan_ok k = true /\ holes_only sh = true /\
  AP.check SEGS IT A (ce_nxf ce) LIMIT XN XE0 XB XC0 (HScut ce CUTS (S i)) KC bfuel fuel None T k = COk sh.
Hypothesis CERT : AP.check SEGS IT A (ce_nxf ce) LIMIT XN XE0 XB XC0 (HScut ce CUTS 0) KC bfuel fuel None (ce_tin ce) p = COk s.

Theorem contract_of_cert_rec_cut : forall n, 0 <= n -> callee_contract_upto idepth n ce.
Proof.
  intros n Hn. revert n Hn. refine (Wf_Z.Zlt_0_ind _ _). intros n IH Hn.
  destruct (Z.eq_dec n 0) as [->|Hnz].
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 E fx R M mdl T _ _ _ _ HQ. exfalso.
    unfold Qd, DMEAS in HQ. pose proof (u64_range (ev E idepth)). lia.
  - unfold callee_contract_upto.
    refine (contract_of_cert_when_cut SEGS A SEGS_in_hull HULL_ok SWIN G FXOK RZ RZ_step RZ_msteps RZ_exit RZ_conseq RUN AINVH AINVH_frame AINVH_zone AINVH_disj G_ro_img G_img_ceil
             ce IT IT_ok LIMIT KC bfuel fuel XN (Qd idepth n) _ _ XB _ CUTS CUTS_ok p s p_ok s_ok CERT).
    + intros E E' Hag HQ. eapply Qd_agree; [exact idepth_lt | exact Hag | exact HQ].
    + intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa HUQ.
      apply (XN_sound_rec (n - 1) PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV ltac:(lia) HB0 HC0 HBc HCc HUa).
      * intros E HE. pose proof (HUQ E HE) as X. unfold Qd in X. lia.
      * apply IH. lia.
    + intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa HUQ.
      apply (XB_sound_rec (n - 1) PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV ltac:(lia) HB0 HC0 HBc HCc HUa).
      * intros E HE. pose proof (HUQ E HE) as X. unfold Qd in X. lia.
      * apply IH. lia.
Qed.

Corollary contract_of_cert_rec_cut_all : callee_contract SEGS SWIN G FXOK RZ AINVH ce.
Proof. exact (callee_contract_of_upto idepth ce contract_of_cert_rec_cut). Qed.
End CertCut.
End Rec.
End GlzCallRec.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GlzRom OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GlzRom OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst GlzCallCert GlzCallRec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition kdead (cs : acs) : Prop := In (KRange (ELit 1) 0 0) (kn cs).
(* [comment removed for export] *)
Definition hs_sub (HS' HS : nat -> option acs) : Prop :=
  forall h ch, HS' h = Some ch -> (exists h', HS h' = Some ch) \/ kdead ch.

Lemma kdead_no_state : forall SEGS {RC : run_ceil} PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model,
  kdead cs -> ~ GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model.
Proof.
  intros SEGS RC PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model Hd HC.
  pose proof (co_know HC) as K. unfold know_ok in K. rewrite Forall_forall in K.
  pose proof (K _ Hd) as X. cbn [kentry_ok edenot] in X.
  change (bv_unsigned (Z_to_bv 64 1)) with 1 in X. lia.
Qed.

(* [comment removed for export] *)
Definition kdeadb (cs : acs) : bool := match kn cs with KRange (ELit (Zpos xH)) Z0 Z0 :: _ => true | _ => false end.
Lemma kdeadb_sound : forall cs, kdeadb cs = true -> kdead cs.
Proof.
  intros cs H. unfold kdeadb in H. unfold kdead.
  destruct (kn cs) as [|K r]; [discriminate|]. left.
  destruct K as [| | | | |e lo hi| | | | ]; try discriminate H.
  destruct e as [z| | | | | | |]; try discriminate H.
  destruct z as [|p|]; try discriminate H. destruct p; try discriminate H.
  destruct lo; try discriminate H. destruct hi; try discriminate H. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma contract_upto_of_full : forall SEGS {RC : run_ceil} SWIN G FXOK RZ AINVH i n ce,
  callee_contract SEGS SWIN G FXOK RZ AINVH ce -> callee_contract_upto SEGS SWIN G FXOK RZ AINVH i n ce.
Proof.
  intros SEGS RC SWIN G FXOK RZ AINVH i n ce H. unfold callee_contract_upto, callee_contract, callee_contract_when in *.
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 E fx R M mdl T HB0 HC0 HBc HCc HQ HC HT Hk.
  exact (H PERMf TOPf HID M0 B0 C0 FS0 FDS0 E fx R M mdl T HB0 HC0 HBc HCc I HC HT Hk).
Qed.

(* [comment removed for export] *)
Lemma holes_stmt_sub : forall SEGS {RC : run_ceil} (HS HS' : nat -> option acs) PERMc SPTOPc FS0 FDS0 AINV FXOK UINV (T : TSet) RZ,
  hs_sub HS' HS ->
  GPS.holes_stmt SEGS HS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV (fun _ _ _ => T) RZ ->
  GPS.holes_stmt SEGS HS' PERMc SPTOPc FS0 FDS0 AINV FXOK UINV (fun _ _ _ => T) RZ.
Proof.
  intros SEGS RC HS HS' PERMc SPTOPc FS0 FDS0 AINV FXOK UINV T RZ Hsub H h ch Hh E fx R M model HC.
  destruct (Hsub h ch Hh) as [[h' Hh'] | Hd].
  - exact (H h' ch Hh' E fx R M model HC).
  - exfalso. exact (kdead_no_state SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E ch fx R M model Hd HC).
Qed.

Section CertCutX.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable A : atable.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Hypothesis RUN : GPS.RUN_SOUND SEGS FXOK.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok G b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
Hypothesis G_img_hull : 0 <= g_img_lo G <= g_img_hi G /\ g_img_hi G < 2 ^ 64.
#[local] Notation AINVf := (AINV_f (nil_of SWIN) G AINVH).   (* [comment removed for export] *)
Variable ce : gcallee.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable LIMIT : Z.
Variable KC bfuel fuel : nat.
Variable XN : nat -> list expr -> acs -> option acs.
Variable Q : env -> Prop.
Hypothesis Q_agree : forall E E', env_agree (ce_nxf ce) E E' -> Q E -> Q E'.
Hypothesis XN_sound : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> Q E) ->
  GPS.ext_stmt SEGS (ce_nxf ce) XN PERMf TOPf FS0 FDS0 (AINVf PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis XB_sound : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> Q E) ->
  GPS.ext2_stmt SEGS (ce_nxf ce) XB PERMf TOPf FS0 FDS0 (AINVf PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.
(* [comment removed for export] *)
Variable XNs : nat -> list expr -> acs -> option acs.
Hypothesis XNs_sound : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> Q E) ->
  GPS.ext_stmt SEGS (ce_nxf ce) XNs PERMf TOPf FS0 FDS0 (AINVf PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.
Variable XBs : nat -> list expr -> acs -> option (acs * acs).
Hypothesis XBs_sound : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> Q E) ->
  GPS.ext2_stmt SEGS (ce_nxf ce) XBs PERMf TOPf FS0 FDS0 (AINVf PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.

(* [comment removed for export] *)
Variable CUTS : list (acs * plan).
#[local] Notation NT := (GlzCallCert.NT ce).
#[local] Notation HScut := (GlzCallCert.HScut ce CUTS).
(* [comment removed for export] *)
Hypothesis CUTS_ok : forall i T k, nth_error CUTS i = Some (T, k) -> exists sh,
  gplan_ok k = true /\ holes_only sh = true /\
  (AP.check SEGS IT A (ce_nxf ce) LIMIT XN XE0 XB XC0 (HScut (S i)) KC bfuel fuel None T k = COk sh \/
   exists HS', hs_sub HS' (HScut (S i)) /\ AP.check SEGS IT A (ce_nxf ce) LIMIT XNs XE0 XBs XC0 HS' KC bfuel fuel None T k = COk sh).
Variable p : plan.
Variable s : shape.
Hypothesis p_ok : gplan_ok p = true.
Hypothesis s_ok : holes_only s = true.
Hypothesis CERT : AP.check SEGS IT A (ce_nxf ce) LIMIT XN XE0 XB XC0 (HScut 0) KC bfuel fuel None (ce_tin ce) p = COk s.

Theorem contract_of_cert_when_cutX : callee_contract_when SEGS SWIN G FXOK RZ AINVH Q ce.
Proof.
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 E fx R M mdl T HB0 HC0 HBc HCc HQ HC HT Hexits.
  set (UINV := fun E' => env_agree (ce_nxf ce) E E').
  assert (UINV_agree : forall E1 E2, env_agree (ce_nxf ce) E1 E2 -> UINV E1 -> UINV E2).
  { intros E1 E2 H12 H1. unfold UINV in *. eapply env_agree_trans; [exact H1 | exact H12]. }
  assert (UINV_Q : forall E1, UINV E1 -> Q E1).
  { intros E1 H1. eapply Q_agree; [exact H1 | exact HQ]. }
  (* [comment removed for export] *)
  #[local] Ltac exit_hole Hexits Hh HC1 HC :=
    match type of HC1 with GPS.cs_ok _ _ _ _ _ _ _ _ ?E1 ?ch ?fx1 ?R1 ?M1 ?mdl1 =>
      apply (Hexits ch E1 fx1 R1 M1 mdl1); [eapply nth_error_In; exact Hh | exact (co_uinv HC1)
                   | destruct HC1; constructor; try assumption; exact I
                   | rewrite (co_fs HC1); symmetry; exact (co_fs HC)] end.
  assert (HSall : forall d k, (length CUTS <= k + d)%nat ->
            GPS.holes_stmt SEGS (HScut k) PERMf TOPf FS0 FDS0 (AINVf PERMf TOPf HID M0 B0 C0) FXOK UINV (fun _ _ _ => T) RZ).
  { induction d as [|d IHd]; intros k Hk h ch Hh E1 fx1 R1 M1 mdl1 HC1; unfold GlzCallCert.HScut in Hh.
    - destruct (Nat.ltb h NT) eqn:Hlt; [exit_hole Hexits Hh HC1 HC|].
      destruct (Nat.leb k (h - NT)) eqn:Hle; [|discriminate]. apply Nat.leb_le in Hle.
      destruct (nth_error CUTS (h - NT)) as [c|] eqn:Hn; [|discriminate].
      exfalso. assert (Hl : (h - NT < length CUTS)%nat) by (apply nth_error_Some; rewrite Hn; discriminate). lia.
    - destruct (Nat.ltb h NT) eqn:Hlt; [exit_hole Hexits Hh HC1 HC|].
      destruct (Nat.leb k (h - NT)) eqn:Hle; [|discriminate]. apply Nat.leb_le in Hle.
      destruct (nth_error CUTS (h - NT)) as [[Tc kc]|] eqn:Hn; [|discriminate]. cbn [fst] in Hh. injection Hh as <-.
      destruct (Nat.eq_dec (h - NT) k) as [Heq|Hne].
      + (* [comment removed for export] *)
        destruct (CUTS_ok (h - NT)%nat Tc kc Hn) as (sc & Hgp & Hho & [Hck | (HS' & Hsub & Hck)]).
        { pose proof (GPS.check_sound SEGS IT IT_ok A (ce_nxf ce) LIMIT (HScut (S (h - NT))) XN XE0 XB XC0 KC (nil_of SWIN) PERMf TOPf FS0 FDS0
                      (AINVf PERMf TOPf HID M0 B0 C0)
                      (AINV_f_frame (nil_of SWIN) G AINVH (AINVH_frame_nil SWIN AINVH AINVH_frame) AINVH_zone AINVH_disj G_ro_img G_img_ceil PERMf TOPf HID M0 B0 C0)
                      FXOK UINV UINV_agree (fun _ _ _ => T) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => HT) (fun _ _ _ => eq_refl)
                      RZ RZ_step RZ_msteps RZ_exit RZ_conseq RUN SEGS_in_hull HULL_ok
                      (XN_sound PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc UINV_agree UINV_Q)
                      ltac:(intros id args cs fd ps cs' E2 fx2 R2 M2 m2 T2 _ Hnn; discriminate Hnn)
                      (XB_sound PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc UINV_agree UINV_Q)
                      ltac:(intros id args cs csa csb E2 fx2 R2 M2 m2 Ta Tb _ Hnn; discriminate Hnn)
                      (IHd (S (h - NT)) ltac:(lia)) fuel bfuel None kc Tc sc Hgp Hck E1 fx1 R1 M1 mdl1 T) as X.
        rewrite (sd_holes_only T E1 (m_fs mdl1) sc Hho) in X.
        apply X; [exact HC1 | exact I | exact HT]. }
        pose proof (GPS.check_sound SEGS IT IT_ok A (ce_nxf ce) LIMIT HS' XNs XE0 XBs XC0 KC (nil_of SWIN) PERMf TOPf FS0 FDS0
                      (AINVf PERMf TOPf HID M0 B0 C0)
                      (AINV_f_frame (nil_of SWIN) G AINVH (AINVH_frame_nil SWIN AINVH AINVH_frame) AINVH_zone AINVH_disj G_ro_img G_img_ceil PERMf TOPf HID M0 B0 C0)
                      FXOK UINV UINV_agree (fun _ _ _ => T) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => HT) (fun _ _ _ => eq_refl)
                      RZ RZ_step RZ_msteps RZ_exit RZ_conseq RUN SEGS_in_hull HULL_ok
                      (XNs_sound PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc UINV_agree UINV_Q)
                      ltac:(intros id args cs fd ps cs' E2 fx2 R2 M2 m2 T2 _ Hnn; discriminate Hnn)
                      (XBs_sound PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc UINV_agree UINV_Q)
                      ltac:(intros id args cs csa csb E2 fx2 R2 M2 m2 Ta Tb _ Hnn; discriminate Hnn)
                      (holes_stmt_sub SEGS _ _ PERMf TOPf FS0 FDS0 _ FXOK UINV T RZ Hsub (IHd (S (h - NT)) ltac:(lia))) fuel bfuel None kc Tc sc Hgp Hck E1 fx1 R1 M1 mdl1 T) as X.
        rewrite (sd_holes_only T E1 (m_fs mdl1) sc Hho) in X.
        apply X; [exact HC1 | exact I | exact HT].
      + (* [comment removed for export] *)
        refine (IHd (S k) ltac:(lia) h Tc _ E1 fx1 R1 M1 mdl1 HC1).
        unfold GlzCallCert.HScut. rewrite Hlt. replace (Nat.leb (S k) (h - NT)) with true by (symmetry; apply Nat.leb_le; lia).
        rewrite Hn. reflexivity. }
  pose proof (GPS.check_sound SEGS IT IT_ok A (ce_nxf ce) LIMIT (HScut 0) XN XE0 XB XC0 KC (nil_of SWIN) PERMf TOPf FS0 FDS0
                (AINVf PERMf TOPf HID M0 B0 C0)
                (AINV_f_frame (nil_of SWIN) G AINVH (AINVH_frame_nil SWIN AINVH AINVH_frame) AINVH_zone AINVH_disj G_ro_img G_img_ceil PERMf TOPf HID M0 B0 C0)
                FXOK UINV UINV_agree (fun _ _ _ => T) (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => HT) (fun _ _ _ => eq_refl)
                RZ RZ_step RZ_msteps RZ_exit RZ_conseq RUN SEGS_in_hull HULL_ok
                (XN_sound PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc UINV_agree UINV_Q)
                ltac:(intros id args cs fd ps cs' E1 fx1 R1 M1 m1 T1 _ Hn; discriminate Hn)
                (XB_sound PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc UINV_agree UINV_Q)
                ltac:(intros id args cs csa csb E2 fx2 R2 M2 m2 Ta Tb _ Hnn; discriminate Hnn)
                (HSall (length CUTS) 0%nat ltac:(lia)) fuel bfuel None p (ce_tin ce) s p_ok CERT E fx R M mdl T) as X.
  rewrite (sd_holes_only T E (m_fs mdl) s s_ok) in X.
  apply X.
  - destruct HC; constructor; try assumption. unfold UINV. apply env_agree_refl.
  - exact I.
  - exact HT.
Qed.
End CertCutX.

(* [comment removed for export] *)
Section RecX.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Variable IT : itab.
Variable A : atable.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok G b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
#[local] Notation AINV0 := (AINV_f (nil_of SWIN) G AINVH).
#[local] Notation UPTO := (callee_contract_upto SEGS SWIN G FXOK RZ AINVH).
Variable ce : gcallee.
Variable idepth : nat.
Hypothesis idepth_lt : (idepth < ce_nxf ce)%nat.
Hypothesis RUN : GPS.RUN_SOUND SEGS FXOK.
Variable LIMIT : Z.
Variable KC bfuel fuel : nat.
Variable XN : nat -> list expr -> acs -> option acs.
Hypothesis XN_sound_rec : forall n PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= n ->
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  UPTO idepth n ce ->
  GPS.ext_stmt SEGS (ce_nxf ce) XN PERMf TOPf FS0 FDS0 (AINV0 PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.
Variable p : plan.
Variable s : shape.
Hypothesis p_ok : gplan_ok p = true.
Hypothesis s_ok : holes_only s = true.
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis XB_sound_rec : forall n PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= n -> 0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  UPTO idepth n ce ->
  GPS.ext2_stmt SEGS (ce_nxf ce) XB PERMf TOPf FS0 FDS0 (AINV0 PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.
Variable XNs : nat -> list expr -> acs -> option acs.
Hypothesis XNs_sound_rec : forall n PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= n ->
  0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  UPTO idepth n ce ->
  GPS.ext_stmt SEGS (ce_nxf ce) XNs PERMf TOPf FS0 FDS0 (AINV0 PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.
Variable XBs : nat -> list expr -> acs -> option (acs * acs).
Hypothesis XBs_sound_rec : forall n PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= n -> 0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
  (forall E E', env_agree (ce_nxf ce) E E' -> UINV E -> UINV E') ->
  (forall E, UINV E -> DMEAS idepth E <= n + 1) ->
  UPTO idepth n ce ->
  GPS.ext2_stmt SEGS (ce_nxf ce) XBs PERMf TOPf FS0 FDS0 (AINV0 PERMf TOPf HID M0 B0 C0) FXOK UINV RZ.
Variable CUTS : list (acs * plan).
Hypothesis CUTS_ok : forall i T k, nth_error CUTS i = Some (T, k) -> exists sh,
  gplan_ok k = true /\ holes_only sh = true /\
  (AP.check SEGS IT A (ce_nxf ce) LIMIT XN XE0 XB XC0 (HScut ce CUTS (S i)) KC bfuel fuel None T k = COk sh \/
   exists HS', hs_sub HS' (HScut ce CUTS (S i)) /\ AP.check SEGS IT A (ce_nxf ce) LIMIT XNs XE0 XBs XC0 HS' KC bfuel fuel None T k = COk sh).
Hypothesis CERT : AP.check SEGS IT A (ce_nxf ce) LIMIT XN XE0 XB XC0 (HScut ce CUTS 0) KC bfuel fuel None (ce_tin ce) p = COk s.

Theorem contract_of_cert_rec_cutX : forall n, 0 <= n -> UPTO idepth n ce.
Proof.
  intros n Hn. revert n Hn. refine (Wf_Z.Zlt_0_ind _ _). intros n IH Hn.
  destruct (Z.eq_dec n 0) as [->|Hnz].
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 E fx R M mdl T _ _ _ _ HQ. exfalso.
    unfold Qd, DMEAS in HQ. pose proof (u64_range (ev E idepth)). lia.
  - unfold callee_contract_upto.
    refine (contract_of_cert_when_cutX SEGS A SEGS_in_hull HULL_ok SWIN G FXOK RZ RZ_step RZ_msteps RZ_exit RZ_conseq RUN AINVH AINVH_frame AINVH_zone AINVH_disj G_ro_img G_img_ceil
             ce IT IT_ok LIMIT KC bfuel fuel XN (Qd idepth n) _ _ XB _ XNs _ XBs _ CUTS CUTS_ok p s p_ok s_ok CERT).
    + intros E E' Hag HQ. eapply Qd_agree; [exact idepth_lt | exact Hag | exact HQ].
    + intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa HUQ.
      apply (XN_sound_rec (n - 1) PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV ltac:(lia) HB0 HC0 HBc HCc HUa).
      * intros E HE. pose proof (HUQ E HE) as X. unfold Qd in X. lia.
      * apply IH. lia.
    + intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa HUQ.
      apply (XB_sound_rec (n - 1) PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV ltac:(lia) HB0 HC0 HBc HCc HUa).
      * intros E HE. pose proof (HUQ E HE) as X. unfold Qd in X. lia.
      * apply IH. lia.
    + intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa HUQ.
      apply (XNs_sound_rec (n - 1) PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV ltac:(lia) HB0 HC0 HBc HCc HUa).
      * intros E HE. pose proof (HUQ E HE) as X. unfold Qd in X. lia.
      * apply IH. lia.
    + intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa HUQ.
      apply (XBs_sound_rec (n - 1) PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV ltac:(lia) HB0 HC0 HBc HCc HUa).
      * intros E HE. pose proof (HUQ E HE) as X. unfold Qd in X. lia.
      * apply IH. lia.
Qed.

Corollary contract_of_cert_rec_cut_allX : callee_contract SEGS SWIN G FXOK RZ AINVH ce.
Proof. exact (callee_contract_of_upto SEGS SWIN G FXOK RZ AINVH idepth ce contract_of_cert_rec_cutX). Qed.
End RecX.
