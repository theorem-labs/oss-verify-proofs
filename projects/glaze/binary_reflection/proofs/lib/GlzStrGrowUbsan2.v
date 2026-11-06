(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemsetCode OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrResizeUbsan2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrGrowUbsan. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemsetCode OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrResizeUbsan2.UbMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.UbMuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcUbsan.UbMuslMemmove2 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrResizeUbsan2.GlzStrResizeUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrGrowUbsan.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuAtom.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.PuUnorm.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound.PuKin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac u_norm ::= pu_u_norm.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AP. Import GPS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
#[local] Ltac pa_lia_prev := Zify.zify; xlia zchecker.
#[local] Ltac lia ::= first [ solve [ pa_tiers ltac:(pa_lia_prev) ] | pa_lia_prev ].
#[local] Notation USEGS := Ubsan.M.loaded_segments.
#[local] Notation W8 v := (word_to_le_bytes 8 v).
Ltac kept_in ::= cbv [callee_kept app_saved callee_saved_regs In]; first [ kin | kin_nt ].   (* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac kept_in ::= first [ pu_kept_fast | cbv [callee_kept app_saved callee_saved_regs In]; first [ kin | kin_nt ] ].
Ltac kin_from Hx ::= cbv [callee_kept app_saved callee_saved_regs In] in Hx |- *; repeat (destruct Hx as [<-|Hx]; [ kin |]); first [ destruct Hx | tauto ].

(* [comment removed for export] *)
Lemma cell_kept_or_not : forall (M M' : word -> option byte) (a : word), M' a = M a \/ M' a <> M a.
Proof. intros. destruct (decide (M' a = M a)); [left | right]; assumption. Qed.

Lemma store_ok_cell : forall segs (M M' : word -> option byte) (a : word),
  M' a = M a -> store_ok segs M a 1 = true -> store_ok segs M' a 1 = true.
Proof.
  intros segs M M' a E H. cbn [store_ok] in *. unfold wview in *. rewrite E. exact H.
Qed.

(* [comment removed for export] *)
Lemma wbytes_defined_in : forall bs m (s a : word),
  (bv_unsigned s + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (bv_unsigned s <= bv_unsigned a < bv_unsigned s + Z.of_nat (length bs))%Z ->
  wbytes m s bs a <> None.
Proof.
  intros bs m s a Hnw Ha.
  assert (Ea : a = Z_to_bv 64 (bv_unsigned s + Z.of_nat (Z.to_nat (bv_unsigned a - bv_unsigned s)))).
  { apply bv_eq. rewrite Z2Nat.id by lia. rewrite u64_lit by (pose proof (u64_range a); lia). lia. }
  rewrite Ea. apply GCL.wbytes_defined; [exact Hnw | lia].
Qed.

Lemma ubsan_segs_wr_ok : GCL.segs_wr_ok USEGS.
Proof.
  intros seg Hin Hw. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hw] |]). destruct Hin.
Qed.

(* [comment removed for export] *)
Lemma rdn_agree : forall (M M' : word -> option byte) (a : word) k,
  (bv_unsigned a + Z.of_nat k <= 2 ^ 64)%Z ->
  (forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k)%Z -> M' x = M x) ->
  rdn USEGS M' a k = rdn USEGS M a k.
Proof. intros. apply rdn_ext; assumption. Qed.


(* [comment removed for export] *)
Lemma zkept_bv : forall R R' : bvmap 5 word,
  (forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) ->
  forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' x = getr R x.
Proof.
  intros R R' KEPT x Hx. cbv [In] in Hx.
  repeat (destruct Hx as [<-|Hx];
    [ first [ lazymatch goal with |- getr _ (@BV _ ?z _) = _ => exact (KEPT z ltac:(kept_in)) end | first [ exact (KEPT 2%Z ltac:(kept_in)) | exact (KEPT 3%Z ltac:(kept_in)) | exact (KEPT 4%Z ltac:(kept_in))
            | exact (KEPT 8%Z ltac:(kept_in)) | exact (KEPT 9%Z ltac:(kept_in)) | exact (KEPT 18%Z ltac:(kept_in))
            | exact (KEPT 19%Z ltac:(kept_in)) | exact (KEPT 20%Z ltac:(kept_in)) | exact (KEPT 21%Z ltac:(kept_in))
            | exact (KEPT 22%Z ltac:(kept_in)) | exact (KEPT 23%Z ltac:(kept_in)) | exact (KEPT 24%Z ltac:(kept_in))
            | exact (KEPT 25%Z ltac:(kept_in)) | exact (KEPT 26%Z ltac:(kept_in)) | exact (KEPT 27%Z ltac:(kept_in)) ] ] |]).
  destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma bvkept_Z : forall R R' : bvmap 5 word,
  (forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' x = getr R x) ->
  forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).
Proof.
  intros R R' KB r Hr. cbv [callee_saved_regs In] in Hr.
  repeat (destruct Hr as [<-|Hr];
    [ first [ lazymatch goal with |- getr _ ?z = _ => exact (KB z ltac:(kept_in)) end | first [ exact (KB 2%bv ltac:(kept_in)) | exact (KB 3%bv ltac:(kept_in)) | exact (KB 4%bv ltac:(kept_in))
            | exact (KB 8%bv ltac:(kept_in)) | exact (KB 9%bv ltac:(kept_in)) | exact (KB 18%bv ltac:(kept_in))
            | exact (KB 19%bv ltac:(kept_in)) | exact (KB 20%bv ltac:(kept_in)) | exact (KB 21%bv ltac:(kept_in))
            | exact (KB 22%bv ltac:(kept_in)) | exact (KB 23%bv ltac:(kept_in)) | exact (KB 24%bv ltac:(kept_in))
            | exact (KB 25%bv ltac:(kept_in)) | exact (KB 26%bv ltac:(kept_in)) | exact (KB 27%bv ltac:(kept_in)) ] ] |]).
  destruct Hr.
Qed.

Section GROW.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable FXOK : FX -> Prop.
Variable G : gtable.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
(* [comment removed for export] *)
Hypothesis AINV_app : forall Lc B C M M' mdl,
  AINV Lc B C M mdl ->
  (forall a : word, M' a <> M a -> (in_blocks Lc (bv_unsigned a) \/ (CEIL_run <= bv_unsigned a)%Z) /\ M' a <> None) ->
  AINV Lc B C M' mdl.
(* [comment removed for export] *)
Hypothesis priv_img : forall z, in_wins (g_priv G) z -> (g_img_lo G <= z < g_img_hi G)%Z.
Hypothesis img_ok : (0 <= g_img_lo G <= g_img_hi G /\ g_img_hi G <= CEIL_run)%Z.

#[local] Notation opnew_mspecR := (GlzSpecsStr.GlzContracts.opnew_mspecR USEGS AINV FXOK RZ G).
#[local] Notation free_mspecR := (GlzSpecsStr.GlzContracts.free_mspecR USEGS AINV FXOK RZ G).
#[local] Notation blk_ok := (GlzSpecsStr.GlzContracts.blk_ok G).

(* [comment removed for export] *)
Theorem resize_grow_long : forall stk bc cc, (0 <= stk)%Z ->
  opnew_mspecR stk bc cc 0x749a4 -> free_mspecR stk 0x5a5a4 ->
  forall fx R M mdl L1 L2 B C (ret sp : Z) (obj d w0 cw : word) (cap s n : Z) T,
    m_halted mdl = None -> m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] -> FXOK fx ->
    AINV (L1 ++ (bv_unsigned d, cap + 1) :: L2) B C M mdl ->
    T [] ->
    getr R (Z_to_bv 5 1) = Z_to_bv 64 ret -> (0 <= ret < 2 ^ 64)%Z -> (ret mod 2 = 0)%Z ->
    getr R (Z_to_bv 5 10) = obj -> getr R (Z_to_bv 5 11) = Z_to_bv 64 n -> getr R (Z_to_bv 5 12) = cw ->
    bv_unsigned (getr R (Z_to_bv 5 2)) = sp -> (sp mod 16 = 0)%Z -> (CEIL_run + stk + 80 <= sp)%Z ->
    getr R (Z_to_bv 5 4) = Z_to_bv 64 (g_tp G) ->
    (forall a : word, (sp - stk - 80 <= bv_unsigned a < sp)%Z -> store_ok USEGS M a 1 = true) ->
    (sp <= bv_unsigned obj)%Z -> (bv_unsigned obj + 24 <= 2 ^ 64)%Z -> store_ok USEGS M obj 24 = true ->
    rdn USEGS M obj 8 = Some (W8 w0) -> (bv_unsigned w0 = cap + 2)%Z -> ((cap + 1) mod 8 = 0)%Z -> (23 <= cap)%Z ->
    rdn USEGS M (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 s)) ->
    rdn USEGS M (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 d) ->
    (0 <= s <= cap)%Z -> (cap < n)%Z -> (4 * n <= NMAX)%Z -> (4 * cap <= NMAX)%Z ->
    blk_ok (bv_unsigned d) (cap + 1) ->
    (forall a : word, (bv_unsigned d <= bv_unsigned a < bv_unsigned d + cap + 1)%Z -> M a <> None /\ store_ok USEGS M a 1 = true) ->
    (B + mcost (galloc n cap) <= bc)%Z -> (C + MCNT <= cc)%Z ->
    (forall fx' R' M' mdl' (p : word),
        FXOK fx' ->
        (forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) ->
        getr R' (Z_to_bv 5 10) = obj ->
        (bv_unsigned p mod 16 = 0)%Z -> blk_ok (bv_unsigned p) (galloc n cap) ->
        (forall b m, In (b, m) (L1 ++ L2) -> (bv_unsigned p + galloc n cap <= b \/ b + m <= bv_unsigned p)%Z) ->
        (forall a : word, (bv_unsigned p <= bv_unsigned a < bv_unsigned p + galloc n cap)%Z -> M' a <> None /\ store_ok USEGS M' a 1 = true) ->
        rdn USEGS M' obj 8 = Some (W8 (Z_to_bv 64 (galloc n cap + 1))) ->
        rdn USEGS M' (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 n)) ->
        rdn USEGS M' (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 p) ->
        M' (Z_to_bv 64 (bv_unsigned p + n)) = Some (Z_to_bv 8 0) ->
        (forall a : word, M' a <> M a ->
           (bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24)%Z \/ alloc_changed G (stk + 80) (L1 ++ L2) sp a) ->
        (forall a : word, (sp - stk - 80 <= bv_unsigned a < sp)%Z -> store_ok USEGS M' a 1 = true) ->
        (forall a : word, (bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24)%Z -> M' a <> None) ->
        AINV ((bv_unsigned p, galloc n cap) :: L1 ++ L2)
             (Z.max 0 (B + mcost (galloc n cap) - mcost (cap + 1))) (Z.max 0 (C + MCNT - MCNT)) M' mdl' ->
        m_halted mdl' = None -> m_vm_lazy mdl' = [] -> m_vm_materialized mdl' = [] -> m_fs mdl' = m_fs mdl -> m_fds mdl' = m_fds mdl ->
        RZ (mkCfg (mkstF fx' R' (Z_to_bv 64 ret) M' (seg_rom USEGS)) mdl') T) ->
    RZ (mkCfg (mkstF fx R (Z_to_bv 64 0x5c1d8) M (seg_rom USEGS)) mdl) T.
Proof using img_ok priv_img AINV_app RZ_msteps.
  intros stk bc cc Hstk MAL FR fx R M mdl L1 L2 B C ret sp obj d w0 cw cap s n T
         Hh Hl Hm HFX HA HT0 R1 Hret Hrete R10 R11 R12 R2 Hsp16 Hceil R4 Hscr Hobjsp Hobj STO RD8 Hw0 Hcap8 Hcap23 RDs RDd
         Hs Hn HnN HcN (Hdlo & Hdhi & Hdimg) Hblk Hb Hc K.
  pose proof (@GlzConst.RunCeil.ceil_rng RC) as CR. pose proof img_ok as IMG. unfold GlzConst.PTRLO in Hdlo.
  set (Lc := L1 ++ (bv_unsigned d, cap + 1) :: L2) in *.
  set (spw := getr R (Z_to_bv 5 2)) in *. subst sp.
  set (retw := Z_to_bv 64 ret) in *.
  set (alloc := galloc n cap) in *.
  pose proof (u64_range spw) as Hspr. pose proof (u64_range obj) as Hor. pose proof (u64_range d) as Hdr.
  unfold NMAX in *.
  pose proof (lor7_bounds (Z.max n (2 * cap)) ltac:(lia)) as Lb. 
  assert (Hal : (n <= alloc - 1 /\ 2 * cap <= alloc - 1 /\ alloc <= Z.max n (2 * cap) + 8 /\ alloc mod 8 = 0)%Z).
  { subst alloc. unfold galloc. set (g := Z.max n (2 * cap)) in *.
    pose proof (Z.add_lor_land g 7) as E. pose proof (Z.land_ones g 3) as L3. change (Z.ones 3) with 7%Z in L3.
    change (2 ^ 3)%Z with 8%Z in L3. rewrite L3 in E by lia.
    pose proof (Z.mod_pos_bound g 8 ltac:(lia)). pose proof (Z.div_mod g 8 ltac:(lia)).
    split; [lia|]. split; [lia|]. split; [lia|].
    replace (Z.lor g 7 + 1)%Z with ((g / 8 + 1) * 8)%Z by lia. apply Z_mod_mult. }
  destruct Hal as (Hal1 & Hal2 & Hal3 & Hal8).
  assert (Halr : (1 <= alloc <= 2 ^ 40)%Z) by lia.
  assert (Hev : (alloc mod 2 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide alloc 8 2) by (exists 4%Z; reflexivity). rewrite Hal8. reflexivity. }
  assert (Hretok : ret_ok retw) by (apply ret_ok_even; subst retw; rewrite u64_lit by lia; exact Hrete).
  assert (R2' : getr R 2%bv = spw) by reflexivity.
  assert (Hsp80 : (80 <= bv_unsigned spw)%Z) by lia.
  assert (STF : store_ok USEGS M (Z_to_bv 64 (bv_unsigned spw - 80)) 80 = true).
  { apply store_ok_of_all; [u_norm; lia|]. intros x Hx. revert Hx. u_norm. intros Hx.
    eapply (store_ok_all USEGS M 1%nat x); [cbn; pose proof (u64_range x); lia | apply Hscr; lia | cbn; lia]. }
  assert (Hcap2 : ((cap + 1) mod 2 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide (cap + 1) 8 2) by (exists 4%Z; reflexivity). rewrite Hcap8. reflexivity. }
  assert (Odd : (bv_unsigned w0 mod 2 = 1)%Z).
  { rewrite Hw0. replace (cap + 2)%Z with (cap + 1 + 1)%Z by lia. rewrite Z.add_mod, Hcap2 by lia. reflexivity. }
  (* [comment removed for export] *)
  destruct (@rs_head_long_gt fx (seg_rom USEGS) R M obj w0 s n RD8 Odd RDs ltac:(lia) ltac:(lia) Hobj R10 R11)
    as (rA & RUNA & A11 & A10 & AK).
  (* [comment removed for export] *)
  assert (A2 : getr rA 2%bv = spw) by (rewrite (AK 2%bv) by kept_in; exact R2').
  destruct (@app_pro fx (seg_rom USEGS) rA M spw obj (Z_to_bv 64 (n - s)) A2 A10 A11 ltac:(u_norm; lia) Hsp80 STF)
    as (rB & RUNB & B2 & B8 & B9 & B10 & B12 & BK).
  rewrite (app_mem1_ext (seg_rom USEGS) M spw R rA) in RUNB by (intros x Hx; apply AK; unfold app_saved in Hx; kin_from Hx).
  set (M1 := app_mem1 M spw R) in *.
  assert (M1out : forall a : word, (bv_unsigned a < bv_unsigned spw - 80 \/ bv_unsigned spw <= bv_unsigned a)%Z -> M1 a = M a)
    by (intros a Ha; subst M1; apply app_mem1_out; [exact Hsp80 | exact Ha]).
  assert (M1grows : mem_grows M M1) by (subst M1; apply app_mem1_grows).
  assert (RD8_1 : rdn USEGS M1 obj 8 = Some (W8 w0)).
  { rewrite <- RD8. apply rdn_agree; [cbn; lia|]. intros x Hx. apply M1out. cbn in Hx. lia. }
  assert (RDs_1 : rdn USEGS M1 (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 s))).
  { rewrite <- RDs. apply rdn_agree; [cbn; u_norm; lia|]. intros x Hx. apply M1out. revert Hx. u_norm. cbn. intros Hx. lia. }
  assert (RDd_1 : rdn USEGS M1 (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 d)).
  { rewrite <- RDd. apply rdn_agree; [cbn; u_norm; lia|]. intros x Hx. apply M1out. revert Hx. u_norm. cbn. intros Hx. lia. }
  (* [comment removed for export] *)
  assert (B12' : getr rB 12%bv = cw) by (rewrite B12, (AK 12%bv) by kept_in; exact R12).
  destruct (@grow_g1_long fx (seg_rom USEGS) rB M1 obj (Z_to_bv 64 (bv_unsigned spw - 80)) w0 cw cap s (n - s)
              RD8_1 Hw0 Hcap2 RDs_1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hobj B2 B8 B9 B12')
    as (rC & RUNC & C10 & C23 & C18 & C2 & C8 & C9 & C12 & CK).
  (* [comment removed for export] *)
  destruct (@grow_g2_long fx (seg_rom USEGS) rC M1 obj (Z_to_bv 64 (bv_unsigned spw - 80)) cw d cap s (n - s)
              RDd_1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hobj C10 C23 C18 C2 C8 C9 C12)
    as (rD & RUND & D1 & D10 & D21 & D24 & D19 & D22 & D18 & D9 & D8 & D23 & D2 & DK).
  replace (s + (n - s))%Z with n in D10, D21, D22 by lia. fold alloc in D10, D21.
  (* [comment removed for export] *)
  eapply RZ_msteps; [exact Hh | exact Hl | |].
  { unfold mkstF. replace (Z_to_bv 64 0x5c1d8) with (0x5c1d8%bv : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply msteps_trans; [exact RUNA|]. eapply msteps_trans; [exact RUNB|]. eapply msteps_trans; [exact RUNC|]. exact RUND. }
  (* [comment removed for export] *)
  replace (0x749a4%bv : word) with (Z_to_bv 64 0x749a4) by (apply bv_eq; vm_compute; reflexivity).
  change (mkst rD (Z_to_bv 64 0x749a4) M1 (seg_rom USEGS)) with (mkstF fx rD (Z_to_bv 64 0x749a4) M1 (seg_rom USEGS)).
  assert (D4 : getr rD (Z_to_bv 5 4) = Z_to_bv 64 (g_tp G)).
  { etransitivity; [exact (DK 4%bv ltac:(kept_in))|]. rewrite (CK 4%bv) by kept_in. rewrite (BK 4%bv) by kept_in.
    rewrite (AK 4%bv) by kept_in. exact R4. }
  eapply (MAL fx rD M1 mdl Lc B C 0x5c12c%Z alloc (bv_unsigned spw - 80)%Z T).
  - (* [comment removed for export] *) unfold alloc_pre.
    split; [exact Hh|]. split; [exact Hl|]. split; [exact Hm|]. split; [exact HFX|].
    split. { eapply AINV_app; [exact HA|]. intros a Ha. split.
      + right. destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned spw - 80)); [exfalso; apply Ha; apply M1out; lia | lia].
      + intros Hn0. apply Ha. rewrite Hn0. destruct (M a) as [b|] eqn:HMa; [|reflexivity].
        exfalso. apply (M1grows a); [rewrite HMa; discriminate | exact Hn0]. }
    split; [etransitivity; [exact D1 | apply bv_eq; vm_compute; reflexivity]|].
    split; [lia|]. split; [reflexivity|].
    split; [transitivity (bv_unsigned (Z_to_bv 64 alloc)); [f_equal; exact D10 | u_norm; reflexivity]|].
    split; [unfold NMAX; lia|].
    split; [transitivity (bv_unsigned (Z_to_bv 64 (bv_unsigned spw - 80))); [f_equal; exact D2 | u_norm; reflexivity]|].
    split; [replace (bv_unsigned spw - 80)%Z with (bv_unsigned spw + (-5) * 16)%Z by lia; rewrite Z.mod_add by lia; exact Hsp16|].
    split; [lia|]. split; [exact D4|].
    split; [intros a Ha; eapply store_ok_mono; [exact M1grows|]; apply Hscr; lia|].
    split; [exact Hb | exact Hc].
  - exact HT0.
  - (* [comment removed for export] *)
    intros fx2 R2x M2 mdl2 p (HFX2 & KEPT2 & P10 & Pal & (Plo & Phi & Pimg) & Pdisj & Pblk & FR2 & SCR2 & HA2 & Hh2 & Hl2 & Hm2 & Hfs2 & Hfds2).
    pose proof (u64_range p) as Hpr. unfold NMAX in Pblk. unfold GlzConst.PTRLO in Plo.
    assert (InD : In (bv_unsigned d, (cap + 1)%Z) Lc) by (subst Lc; apply in_app_iff; right; left; reflexivity).
    (* [comment removed for export] *)
    assert (M2f : forall a : word, (bv_unsigned spw - 80 <= bv_unsigned a)%Z -> M2 a = M1 a).
    { intros a Ha. destruct (cell_kept_or_not M1 M2 a) as [E|NE]; [exact E|]. exfalso.
      destruct (FR2 a NE) as [(Z1 & Zi & Z2)|[SZ|PZ]]; [lia | lia | pose proof (priv_img _ PZ); lia]. }
    assert (M2d : forall a : word, (bv_unsigned d <= bv_unsigned a < bv_unsigned d + cap + 1)%Z -> M2 a = M a).
    { intros a Ha. rewrite <- (M1out a) by lia. destruct (cell_kept_or_not M1 M2 a) as [E|NE]; [exact E|]. exfalso.
      destruct (FR2 a NE) as [(Z1 & Zi & Z2)|[SZ|PZ]]; [| lia | pose proof (priv_img _ PZ); lia].
      apply Z2. exists (bv_unsigned d), (cap + 1)%Z. split; [exact InD | lia]. }
    (* [comment removed for export] *)
    assert (X18 : getr R2x 18%bv = Z_to_bv 64 s) by (etransitivity; [exact (KEPT2 18%Z ltac:(kept_in)) | exact D18]).
    assert (X19 : getr R2x 19%bv = d) by (etransitivity; [exact (KEPT2 19%Z ltac:(kept_in)) | exact D19]).
    assert (X23 : getr R2x 23%bv = Z_to_bv 64 cap) by (etransitivity; [exact (KEPT2 23%Z ltac:(kept_in)) | exact D23]).
    assert (X2 : getr R2x 2%bv = Z_to_bv 64 (bv_unsigned spw - 80)) by (etransitivity; [exact (KEPT2 2%Z ltac:(kept_in)) | exact D2]).
    (* [comment removed for export] *)
    assert (STEP3 : exists rF M3,
              msteps USEGS (@mkst fx2 R2x (0x5c12c%bv : word) M2 (seg_rom USEGS)) (@mkst fx2 rF (0x5c144%bv : word) M3 (seg_rom USEGS))
              /\ getr rF 20%bv = p
              /\ (forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rF x = getr R2x x)
              /\ (forall a : word, M3 a <> M2 a -> (bv_unsigned p <= bv_unsigned a < bv_unsigned p + s)%Z)
              /\ mem_grows M2 M3).
    { destruct (Z.eq_dec s 0) as [Hs0|Hs0].
      - destruct (@grow_g3_nomove fx2 (seg_rom USEGS) R2x M2 p P10 ltac:(rewrite X18, Hs0; reflexivity)) as (rF & RUN3 & F20 & FK).
        exists rF, M2. split; [exact RUN3|]. split; [exact F20|]. split; [exact FK|].
        split; [intros a Ha; exfalso; apply Ha; reflexivity | apply mem_grows_refl].
      - destruct (@grow_g3_move fx2 (seg_rom USEGS) R2x M2 p d s P10 X18 X19 ltac:(lia)) as (rE & RUNE & E1 & E10 & E11 & E12 & E20 & EK).
        (* [comment removed for export] *)
        assert (STs : store_ok USEGS M2 d (Z.to_nat s) = true).
        { apply store_ok_of_all; [lia|]. intros x Hx.
          eapply (store_ok_all USEGS M2 1%nat x); [cbn; pose proof (u64_range x); lia | | cbn; lia].
          eapply store_ok_cell; [apply M2d; lia | apply (proj2 (Hblk x ltac:(lia)))]. }
        destruct (GCL.store_ok_rdn USEGS ubsan_segs_wr_ok (Z.to_nat s) M2 d ltac:(lia) STs) as (bs & RDbs & Lbs).
        assert (HOK : mcH M2 p d s bs).
        { constructor.
          - lia.
          - exact Lbs.
          - rewrite Lbs. exact RDbs.
          - rewrite Lbs. apply store_ok_of_all; [lia|]. intros x Hx. eapply (store_ok_all USEGS M2 1%nat x); [cbn; pose proof (u64_range x); lia | | cbn; lia].
            apply (proj2 (Pblk x ltac:(lia))).
          - destruct (Pdisj (bv_unsigned d) (cap + 1)%Z InD); lia.
          - lia.
          - lia. }
        destruct (@memmove_apart fx2 (seg_rom USEGS) M2 p d s bs rE (0x5c144%bv : word) HOK
                    ltac:(apply ret_ok_even; reflexivity) E1 E10 E11 E12) as (rF & RUNF & FK).
        exists rF, (wbytes M2 p bs). split; [eapply msteps_trans; [exact RUNE | exact RUNF]|].
        split; [rewrite (FK 20%bv) by kept_in; exact E20|].
        split; [intros x Hx; rewrite (FK x) by (kin_from Hx); apply EK; kin_from Hx|].
        split; [| apply wbytes_grows].
        intros a Ha. destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned p)) as [L|L];
          [exfalso; apply Ha; apply wbytes_outside; [unfold in_rng; rewrite Lbs; (first [ (clear Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]) | rewrite Lbs; (first [ (clear M1out Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])]|].
        destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned p + s)) as [U|U]; [lia|].
        exfalso; apply Ha; apply wbytes_outside; [unfold in_rng; rewrite Lbs; lia | rewrite Lbs; lia]. }
    destruct STEP3 as (rF & M3 & RUN3 & F20 & FK & M3p & M3grows).
    assert (K2b : forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R2x x = getr rD x)
      by (exact (zkept_bv rD R2x KEPT2)).
    assert (M3f : forall a : word, (bv_unsigned spw - 80 <= bv_unsigned a)%Z -> M3 a = M1 a).
    { intros a Ha. rewrite <- (M2f a Ha). destruct (cell_kept_or_not M2 M3 a) as [E|NE]; [exact E|]. pose proof (M3p a NE). lia. }
    assert (M3blk : forall a : word, (bv_unsigned p <= bv_unsigned a < bv_unsigned p + alloc)%Z -> M3 a <> None /\ store_ok USEGS M3 a 1 = true).
    { intros a Ha. destruct (Pblk a Ha) as [PD PS]. split; [apply M3grows; exact PD | eapply store_ok_mono; [exact M3grows | exact PS]]. }
    (* [comment removed for export] *)
    assert (F23 : getr rF 23%bv = Z_to_bv 64 cap) by (rewrite (FK 23%bv) by kept_in; exact X23).
    assert (F19 : getr rF 19%bv = d) by (rewrite (FK 19%bv) by kept_in; exact X19).
    destruct (@grow_g4_long fx2 (seg_rom USEGS) rF M3 d cap F23 F19 ltac:(lia)) as (rG & RUNG & G1 & G10 & GK).
    eapply RZ_msteps; [exact Hh2 | exact Hl2 | |].
    { unfold mkstF. replace (Z_to_bv 64 0x5c12c) with (0x5c12c%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      eapply msteps_trans; [exact RUN3 | exact RUNG]. }
    replace (0x5a5a4%bv : word) with (Z_to_bv 64 0x5a5a4) by (apply bv_eq; vm_compute; reflexivity).
    change (mkst rG (Z_to_bv 64 0x5a5a4) M3 (seg_rom USEGS)) with (mkstF fx2 rG (Z_to_bv 64 0x5a5a4) M3 (seg_rom USEGS)).
    set (Lc2 := (bv_unsigned p, alloc) :: Lc). set (Lc3 := (bv_unsigned p, alloc) :: L1 ++ L2).
    assert (G4 : getr rG (Z_to_bv 5 4) = Z_to_bv 64 (g_tp G)).
    { etransitivity; [exact (GK 4%bv ltac:(kept_in))|]. rewrite (FK 4%bv) by kept_in. rewrite (K2b 4%bv) by kept_in. exact D4. }
    eapply (FR fx2 rG M3 mdl2 Lc2 Lc3 (B + mcost alloc)%Z (C + MCNT)%Z
              (Z.max 0 (B + mcost alloc - mcost (cap + 1)))%Z (Z.max 0 (C + MCNT - MCNT))%Z 0x5c158%Z (bv_unsigned spw - 80)%Z d T Hh2 Hl2 Hm2 HFX2).
    + eapply AINV_app; [exact HA2|]. intros a Ha. split.
      * left. exists (bv_unsigned p), alloc. split; [left; reflexivity | pose proof (M3p a Ha); lia].
      * intros N0. apply Ha. rewrite N0. destruct (M2 a) as [b|] eqn:HM2; [|reflexivity].
        exfalso. apply (M3grows a); [rewrite HM2; discriminate | exact N0].
    + etransitivity; [exact G1 | apply bv_eq; vm_compute; reflexivity].
    + lia.
    + reflexivity.
    + exact G10.
    + right. exists (cap + 1)%Z, ((bv_unsigned p, alloc) :: L1), L2. subst Lc2 Lc3 Lc. repeat split; reflexivity.
    + transitivity (bv_unsigned (Z_to_bv 64 (bv_unsigned spw - 80))); [f_equal | u_norm; reflexivity].
      etransitivity; [exact (GK 2%bv ltac:(kept_in))|]. rewrite (FK 2%bv) by kept_in. exact X2.
    + replace (bv_unsigned spw - 80)%Z with (bv_unsigned spw + (-5) * 16)%Z by lia. rewrite Z.mod_add by lia. exact Hsp16.
    + lia.
    + exact G4.
    + intros a Ha. eapply store_ok_cell; [| apply SCR2; exact Ha].
      destruct (cell_kept_or_not M2 M3 a) as [E|NE]; [exact E|]. pose proof (M3p a NE). lia.
    + (* [comment removed for export] *)
      intros fx4 R4x M4 mdl4 HFX4 KEPT4 FR4 SCR4 HA4 Hh4 Hl4 Hm4 Hfs4 Hfds4.
      assert (K4b : forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R4x x = getr rG x)
        by (exact (zkept_bv rG R4x KEPT4)).
      (* [comment removed for export] *)
      assert (InP : In (bv_unsigned p, alloc) Lc3) by (subst Lc3; left; reflexivity).
      assert (M4f : forall a : word, (bv_unsigned spw - 80 <= bv_unsigned a)%Z -> M4 a = M1 a).
      { intros a Ha. rewrite <- (M3f a Ha). destruct (cell_kept_or_not M3 M4 a) as [E|NE]; [exact E|]. exfalso.
        destruct (FR4 a NE) as [(Z1 & Zi & Z2)|[SZ|PZ]]; [(first [ (clear Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]) | (first [ (clear HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hrete; lia) | lia ]) | pose proof (priv_img _ PZ); (first [ (clear HA4 Pdisj Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hcap8 Hsp16 Hrete; lia) | lia ])]. }
      assert (M4p : forall a : word, (bv_unsigned p <= bv_unsigned a < bv_unsigned p + alloc)%Z -> M4 a = M3 a).
      { intros a Ha. destruct (cell_kept_or_not M3 M4 a) as [E|NE]; [exact E|]. exfalso.
        destruct (FR4 a NE) as [(Z1 & Zi & Z2)|[SZ|PZ]]; [| (first [ (clear HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hrete; lia) | lia ]) | pose proof (priv_img _ PZ); (first [ (clear HA4 Pdisj Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hcap8 Hsp16 Hrete; lia) | lia ])].
        apply Z2. exists (bv_unsigned p), alloc. split; [exact InP | lia]. }
      assert (M4blk : forall a : word, (bv_unsigned p <= bv_unsigned a < bv_unsigned p + alloc)%Z -> M4 a <> None /\ store_ok USEGS M4 a 1 = true).
      { intros a Ha. destruct (M3blk a Ha) as [PD PS]. rewrite (M4p a Ha). split; [exact PD|]. eapply store_ok_cell; [apply M4p; exact Ha | exact PS]. }
      assert (M4obj : forall a : word, (bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24)%Z -> M4 a = M a).
      { intros a Ha. rewrite (M4f a) by lia. apply M1out. lia. }
      assert (STO4 : store_ok USEGS M4 obj 24 = true).
      { apply store_ok_of_all; [cbn; lia|]. intros x Hx. cbn in Hx.
        eapply (store_ok_all USEGS M4 1%nat x); [cbn; pose proof (u64_range x); (first [ (clear HA4 Pdisj Pimg Pal M1out Odd Hcap2 Hev Hal8 Hal3 Lb K Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ]) | | cbn; (first [ (clear HA4 Pdisj Pimg Pal M1out Odd Hcap2 Hev Hal8 Hal3 Lb K Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])].
        eapply store_ok_cell; [apply M4obj; lia|]. eapply (store_ok_all USEGS M 24%nat obj ltac:(cbn; lia) STO) in Hx.
        apply store_ok_of_all; [cbn; pose proof (u64_range x); lia|]. intros y Hy. replace y with x; [exact Hx|]. apply bv_eq. cbn in Hy. lia. }
      (* [comment removed for export] *)
      assert (Y21 : getr R4x 21%bv = Z_to_bv 64 alloc).
      { rewrite (K4b 21%bv) by kept_in. rewrite (GK 21%bv) by kept_in. rewrite (FK 21%bv) by kept_in. rewrite (K2b 21%bv) by kept_in. exact D21. }
      assert (Y8 : getr R4x 8%bv = obj).
      { rewrite (K4b 8%bv) by kept_in. rewrite (GK 8%bv) by kept_in. rewrite (FK 8%bv) by kept_in. rewrite (K2b 8%bv) by kept_in. exact D8. }
      assert (Y18 : getr R4x 18%bv = Z_to_bv 64 s).
      { rewrite (K4b 18%bv) by kept_in. rewrite (GK 18%bv) by kept_in. rewrite (FK 18%bv) by kept_in. exact X18. }
      assert (Y20 : getr R4x 20%bv = p).
      { rewrite (K4b 20%bv) by kept_in. rewrite (GK 20%bv) by kept_in. exact F20. }
      assert (Y24 : getr R4x 24%bv = cw).
      { rewrite (K4b 24%bv) by kept_in. rewrite (GK 24%bv) by kept_in. rewrite (FK 24%bv) by kept_in. rewrite (K2b 24%bv) by kept_in. exact D24. }
      assert (Y9 : getr R4x 9%bv = Z_to_bv 64 (n - s)).
      { rewrite (K4b 9%bv) by kept_in. rewrite (GK 9%bv) by kept_in. rewrite (FK 9%bv) by kept_in. rewrite (K2b 9%bv) by kept_in. exact D9. }
      assert (Y22 : getr R4x 22%bv = Z_to_bv 64 n).
      { rewrite (K4b 22%bv) by kept_in. rewrite (GK 22%bv) by kept_in. rewrite (FK 22%bv) by kept_in. rewrite (K2b 22%bv) by kept_in. exact D22. }
      assert (Y2 : getr R4x 2%bv = Z_to_bv 64 (bv_unsigned spw - 80)).
      { rewrite (K4b 2%bv) by kept_in. rewrite (GK 2%bv) by kept_in. rewrite (FK 2%bv) by kept_in. exact X2. }
      (* [comment removed for export] *)
      destruct (@grow_g5 fx4 (seg_rom USEGS) R4x M4 obj p cw alloc s (n - s) Y21 Y8 Y18 Y20 Y24 Y9
                  ltac:((first [ (clear Pal M1out Odd Hcap2 Lb Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])) Hev ltac:((first [ (clear HA4 Pdisj Pimg Pal M1out Odd Hcap2 Hev Hal8 Hal3 Lb K Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])) ltac:((first [ (clear HA4 M1out Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])) Hobj STO4) as (rH & RUNH & H1' & H10' & H11' & H12' & HK').
      set (M5 := hdr_mem M4 obj p alloc s) in *.
      assert (M5out : forall a : word, (bv_unsigned a < bv_unsigned obj \/ bv_unsigned obj + 24 <= bv_unsigned a)%Z -> M5 a = M4 a).
      { intros a Ha. subst M5. unfold hdr_mem. rewrite !wbytes_outside by (rewrite ?lenW8; cbn; unfold in_rng; u_norm; (first [ (clear HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])). reflexivity. }
      assert (M5grows : mem_grows M4 M5).
      { subst M5. unfold hdr_mem. repeat (eapply mem_grows_trans; [| apply wbytes_grows]). apply mem_grows_refl. }
      (* [comment removed for export] *)
      assert (STM5 : store_ok USEGS M5 (Z_to_bv 64 (bv_unsigned p + s)) (Z.to_nat (n - s)) = true).
      { eapply store_ok_mono; [exact M5grows|]. apply store_ok_of_all; [u_norm; (first [ (clear M5out HA4 M1out Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])|]. intros x Hx. revert Hx. u_norm. intros Hx.
        eapply (store_ok_all USEGS M4 1%nat x); [cbn; pose proof (u64_range x); (first [ (clear M5out HA4 Pdisj Pimg Pal M1out Odd Hcap2 Hev Hal8 Hal3 Lb K Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ]) | apply (proj2 (M4blk x ltac:((first [ (clear M5out M1out Odd Hcap2 Lb Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])))) | cbn; (first [ (clear M5out HA4 Pdisj Pimg Pal M1out Odd Hcap2 Hev Hal8 Hal3 Lb K Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])]. }
      assert (Hnw5 : (bv_unsigned (Z_to_bv 64 (bv_unsigned p + s)) + (n - s) < 2 ^ 64)%Z).
      { rewrite u64_lit by (first [ (clear M5out HA4 M1out Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ]). (first [ (clear M5out HA4 M1out Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ]). }
      destruct (@memset_summary_lit fx4 M5 (Z_to_bv 64 (bv_unsigned p + s)) cw (0x5c17c%bv : word) (n - s) (seg_rom USEGS)
                  ltac:((first [ (clear M5out HA4 Pdisj Pimg Pal M1out Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])) Hnw5 STM5 ltac:(apply ret_ok_even; reflexivity) rH H10' H11' H12' H1')
        as (rI & RUNI & I10 & IAG).
      pose proof (ms_agree_keeps _ _ IAG) as IK.
      set (M6 := wbytes M5 (Z_to_bv 64 (bv_unsigned p + s)) (repeat (cbyte cw) (Z.to_nat (n - s)))) in *.
      assert (M6out : forall a : word, (bv_unsigned a < bv_unsigned p + s \/ bv_unsigned p + n <= bv_unsigned a)%Z -> M6 a = M5 a).
      { intros a Ha. subst M6. apply wbytes_outside; rewrite repeat_length; unfold in_rng; u_norm; (first [ (clear HA4 Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]). }
      assert (M6grows : mem_grows M5 M6) by (subst M6; apply wbytes_grows).
      (* [comment removed for export] *)
      assert (RD0_6 : rdn USEGS M6 obj 8 = Some (W8 (Z_to_bv 64 (alloc + 1)))).
      { transitivity (rdn USEGS M5 obj 8).
        - apply rdn_agree; [cbn; lia|]. intros x Hx. apply M6out. cbn in Hx. (first [ (clear M5out HA4 M1out Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ]).
        - subst M5. unfold hdr_mem. rewrite !rdn_wbytes_out by (rewrite ?lenW8; cbn; u_norm; (first [ (clear HA4 Pdisj Pimg Pal M1out Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])). apply rdn_wbytes_hit8. (first [ (clear HA4 Pdisj Pimg Pal M1out Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ]). }
      assert (Odd1 : (bv_unsigned (Z_to_bv 64 (alloc + 1)) mod 2 = 1)%Z).
      { rewrite u64_lit by lia. rewrite Z.add_mod, Hev by lia. reflexivity. }
      assert (ST8_6 : store_ok USEGS M6 (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = true).
      { eapply store_ok_mono; [exact M6grows|]. eapply store_ok_mono; [exact M5grows|].
        eapply (store_ok_sub USEGS M4 obj _ 24); [cbn; (first [ (clear Odd1 M6out HA4 Pdisj Pimg Pal M1out Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ]) | exact STO4 | u_norm; (first [ (clear Odd1 M6out HA4 Pdisj Pimg Pal M1out Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ]) | u_norm; cbn; (first [ (clear Odd1 M6out HA4 Pdisj Pimg Pal M1out Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])]. }
      assert (STn_6 : store_ok USEGS M6 (Z_to_bv 64 (bv_unsigned p + n)) 1 = true).
      { eapply store_ok_mono; [exact M6grows|]. eapply store_ok_mono; [exact M5grows|].
        pose proof (proj2 (M4blk (Z_to_bv 64 (bv_unsigned p + n)) ltac:(u_norm; (first [ (clear M5out M1out Odd Hcap2 Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])))) as S1. exact S1. }
      assert (I8 : getr rI 8%bv = obj) by (rewrite (IK 8%bv) by kept_in; rewrite (HK' 8%bv) by kept_in; exact Y8).
      assert (I20 : getr rI 20%bv = p) by (rewrite (IK 20%bv) by kept_in; rewrite (HK' 20%bv) by kept_in; exact Y20).
      assert (I22 : getr rI 22%bv = Z_to_bv 64 n) by (rewrite (IK 22%bv) by kept_in; rewrite (HK' 22%bv) by kept_in; exact Y22).
      destruct (@app_tail_long fx4 (seg_rom USEGS) rI M6 obj p (Z_to_bv 64 (alloc + 1)) n RD0_6 Odd1 ltac:((first [ (clear Odd1 M5out HA4 Pdisj Pimg Pal M1out Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])) Hobj
                  ltac:((first [ (clear Odd1 M5out HA4 M1out Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])) ST8_6 STn_6 I8 I20 I22) as (rJ & RUNJ & JK).
      set (M7 := wbytes (wbytes M6 (Z_to_bv 64 (bv_unsigned obj + 8)) (W8 (Z_to_bv 64 n))) (Z_to_bv 64 (bv_unsigned p + n)) [Z_to_bv 8 0]) in *.
      assert (M7out : forall a : word, (bv_unsigned a < bv_unsigned obj + 8 \/ bv_unsigned obj + 16 <= bv_unsigned a)%Z ->
                       bv_unsigned a <> (bv_unsigned p + n)%Z -> M7 a = M6 a).
      { intros a Ha Hpn. subst M7. rewrite !wbytes_outside by (rewrite ?lenW8; cbn; unfold in_rng; u_norm; (first [ (clear Odd1 HA4 Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])). reflexivity. }
      assert (M7grows : mem_grows M6 M7) by (subst M7; eapply mem_grows_trans; apply wbytes_grows).
      (* [comment removed for export] *)
      assert (J2 : getr rJ 2%bv = Z_to_bv 64 (bv_unsigned spw - 80)).
      { rewrite (JK 2%bv) by kept_in. rewrite (IK 2%bv) by kept_in. rewrite (HK' 2%bv) by kept_in. exact Y2. }
      assert (M7f : forall a : word, (bv_unsigned spw - 80 <= bv_unsigned a < bv_unsigned spw)%Z -> M7 a = M1 a).
      { intros a Ha. rewrite M7out by (first [ (clear Odd1 HA4 Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]). rewrite M6out by (first [ (clear Odd1 HA4 Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]). rewrite M5out by (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]). apply M4f. lia. }
      assert (RDF : forall k x, In (k, x) [(1%Z, 1); (2%Z, 8); (3%Z, 9); (4%Z, 18); (5%Z, 19); (6%Z, 20); (7%Z, 21); (8%Z, 22); (9%Z, 23); (10%Z, 24)]%bv ->
                rdn USEGS M7 (Z_to_bv 64 (bv_unsigned spw - 8 * k)) 8 = Some (W8 (getr R x))).
      { intros k x Hin. rewrite <- (app_rd M spw R k x Hsp80 Hin). fold M1.
        assert (Hk : (1 <= k <= 10)%Z) by (first [ solve [ clear - Hin; cbv [In] in Hin; decompose [or] Hin; try match goal with H : (_, _) = (_, _) |- _ => injection H; intros; subst end; try (first [ (clear M7out Odd1 M6out M5out HA4 Pal Pimg Pdisj M1out Odd Hcap2 Hev Hal8 Hal3 Lb K Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ]); contradiction ] | cbv [In] in Hin; decompose [or] Hin; try match goal with H : (_, _) = (_, _) |- _ => injection H; intros; subst end; try (first [ (clear M7out Odd1 M6out M5out HA4 Pal Pimg Pdisj M1out Odd Hcap2 Hev Hal8 Hal3 Lb K Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ]); contradiction ]).
        apply rdn_agree; [cbn; u_norm; (first [ (clear M7out Odd1 M6out M5out HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hrete AINV_app; lia) | lia ])|]. intros y Hy. revert Hy. u_norm. cbn. intros Hy. apply M7f. (first [ (clear M7out Odd1 M6out M5out HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hrete AINV_app; lia) | lia ]). }
      assert (R1' : getr R 1%bv = retw) by exact R1.
      assert (Hret1 : ret_ok (getr R 1%bv)) by (rewrite R1'; exact Hretok).
      destruct (@app_epi fx4 (seg_rom USEGS) rJ M7 spw R J2 Hsp80 RDF Hret1) as (rK & RUNK & K2' & K10' & KK1 & KK2).
      eapply RZ_msteps; [exact Hh4 | exact Hl4 | |].
      { unfold mkstF. replace (Z_to_bv 64 0x5c158) with (0x5c158%bv : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply msteps_trans; [exact RUNH|]. eapply msteps_trans; [exact RUNI|]. eapply msteps_trans; [exact RUNJ|]. exact RUNK. }
      rewrite R1'. change (mkst rK retw M7 (seg_rom USEGS)) with (mkstF fx4 rK retw M7 (seg_rom USEGS)).
      (* [comment removed for export] *)
      assert (M7blk : forall a : word, (bv_unsigned p <= bv_unsigned a < bv_unsigned p + alloc)%Z -> M7 a <> None /\ store_ok USEGS M7 a 1 = true).
      { intros a Ha. destruct (M4blk a Ha) as [PD PS]. split.
        - apply M7grows, M6grows, M5grows. exact PD.
        - eapply store_ok_mono; [exact M7grows|]. eapply store_ok_mono; [exact M6grows|]. eapply store_ok_mono; [exact M5grows | exact PS]. }
      apply (K fx4 rK M7 mdl4 p HFX4).
      * apply (bvkept_Z R rK). intros x Hx. cbv [In] in Hx.
        repeat (destruct Hx as [<-|Hx];
          [ lazymatch goal with |- getr _ ?y = _ =>
              first [ rewrite K2'; reflexivity
                    | rewrite (KK1 y ltac:(kept_in)); reflexivity
                    | rewrite (KK2 y ltac:(kept_in)), (JK y ltac:(kept_in)), (IK y ltac:(kept_in)), (HK' y ltac:(kept_in)),
                              (K4b y ltac:(kept_in)), (GK y ltac:(kept_in)), (FK y ltac:(kept_in)), (K2b y ltac:(kept_in)),
                              (DK y ltac:(kept_in)), (CK y ltac:(kept_in)), (BK y ltac:(kept_in));
                      apply AK; kept_in ] end |]).
        destruct Hx.
      * etransitivity; [exact K10'|]. rewrite (JK 8%bv) by kept_in. exact I8.
      * exact Pal.
      * split; [unfold GlzConst.PTRLO; lia | split; [exact Phi | exact Pimg]].
      * intros b m Hbm. apply Pdisj. subst Lc. apply in_app_iff in Hbm as [Hbm|Hbm]; apply in_app_iff; [left; exact Hbm | right; right; exact Hbm].
      * exact M7blk.
      * (* [comment removed for export] *) subst alloc. replace (galloc n cap + 1)%Z with (galloc n cap + 1)%Z by lia.
        rewrite <- RD0_6. apply rdn_agree; [cbn; lia|]. intros x Hx. cbn in Hx. apply M7out; (first [ (clear M1out Odd Hcap2 Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ]).
      * (* [comment removed for export] *) subst M7. rewrite rdn_wbytes_out by (rewrite ?lenW8; cbn; u_norm; (first [ (clear Odd1 HA4 M1out Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])). apply rdn_wbytes_hit8. u_norm. lia.
      * (* [comment removed for export] *) transitivity (rdn USEGS M5 (Z_to_bv 64 (bv_unsigned obj + 16)) 8).
        -- apply rdn_agree; [cbn; u_norm; (first [ (clear Odd1 M6out HA4 Pdisj Pimg Pal M1out Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])|]. intros x Hx. rewrite u64_lit in Hx by lia. cbn in Hx.
           rewrite M7out by ((first [ (clear Odd1 HA4 M1out Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ])). apply M6out. (first [ (clear Odd1 M5out HA4 M1out Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ]).
        -- subst M5. unfold hdr_mem. apply rdn_wbytes_hit8. u_norm. lia.
      * subst M7. apply (wbytes_fill_at1 _ _ _).
      * (* [comment removed for export] *)
        assert (Lsub : forall z, in_blocks (L1 ++ L2) z -> in_blocks Lc z /\ in_blocks Lc3 z).
        { intros z (b & m & Hin & Hz). apply in_app_iff in Hin. split; exists b, m; split; try exact Hz.
          - subst Lc. apply in_app_iff. destruct Hin; [left; assumption | right; right; assumption].
          - subst Lc3. right. apply in_app_iff. exact Hin. }
        assert (HeapP : forall a : word, (bv_unsigned p <= bv_unsigned a < bv_unsigned p + alloc)%Z ->
                        (bv_unsigned a < CEIL_run)%Z /\ ~ (g_img_lo G <= bv_unsigned a < g_img_hi G)%Z /\ ~ in_blocks (L1 ++ L2) (bv_unsigned a)).
        { intros a Ha. split; [(first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])|]. split; [(first [ (clear Odd1 HA4 Pdisj Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hcap8 Hsp16 Hrete; lia) | lia ])|]. intros (b & m & Hin & Hz).
          assert (HinLc : In (b, m) Lc) by (subst Lc; apply in_app_iff in Hin; apply in_app_iff; destruct Hin; [left | right; right]; assumption).
          destruct (Pdisj b m HinLc); (first [ (clear M5out M1out Odd Hcap2 Lb Hdimg Hcap8 Hsp16 Hrete AINV_app; lia) | lia ]). }
        intros a Ha.
        destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj)) as [Lo|Lo];
          [| destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 24)) as [Uo|Uo]; [left; lia|]];
          right; unfold alloc_changed.
        all: destruct (Z.le_gt_cases (bv_unsigned spw - stk - 80) (bv_unsigned a)) as [Ls|Ls];
          [ destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned spw)) as [Us|Us]; [right; left; (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hrete; lia) | lia ]) | exfalso; apply Ha] |].
        1,3: rewrite M7out by (first [ (clear Odd1 HA4 Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]); rewrite M6out by (first [ (clear Odd1 HA4 Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]); rewrite M5out by (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]); rewrite M4f by (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hrete; lia) | lia ]); apply M1out; (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hrete; lia) | lia ]).
        all: destruct (cell_kept_or_not M6 M7 a) as [E7|N7];
          [| left; apply HeapP; destruct (Z.eq_dec (bv_unsigned a) (bv_unsigned p + n)); [(first [ (clear Odd Hcap2 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]) | exfalso; apply N7; apply M7out; (first [ (clear Odd1 HA4 Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])] ].
        all: destruct (cell_kept_or_not M5 M6 a) as [E6|N6];
          [| left; apply HeapP; destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned p + s)); [exfalso; apply N6; apply M6out; (first [ (clear Odd1 HA4 Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])|];
             destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned p + n)); [(first [ (clear Odd Hcap2 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]) | exfalso; apply N6; apply M6out; (first [ (clear Odd1 HA4 Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])] ].
        all: destruct (cell_kept_or_not M4 M5 a) as [E5|N5]; [| exfalso; apply N5; apply M5out; (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]) ].
        all: destruct (cell_kept_or_not M3 M4 a) as [E4|N4];
          [| destruct (FR4 a N4) as [(Z1 & Zi & Z2)|[SZ|PZ]]; [left; split; [exact Z1 | split; [exact Zi | intros IB; apply Z2; apply (proj2 (Lsub _ IB))]] | (first [ (clear Odd1 HA4 Pdisj Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hcap8 Hrete; lia) | lia ]) | right; right; exact PZ] ].
        all: destruct (cell_kept_or_not M2 M3 a) as [E3|N3]; [| left; apply HeapP; pose proof (M3p a N3); (first [ (clear Odd Hcap2 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]) ].
        all: destruct (cell_kept_or_not M1 M2 a) as [E2|N2];
          [| destruct (FR2 a N2) as [(Z1 & Zi & Z2)|[SZ|PZ]]; [left; split; [exact Z1 | split; [exact Zi | intros IB; apply Z2; apply (proj1 (Lsub _ IB))]] | (first [ (clear Odd1 HA4 Pdisj Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hcap8 Hrete; lia) | lia ]) | right; right; exact PZ] ].
        all: exfalso; apply Ha; rewrite E7, E6, E5, E4, E3, E2; apply M1out; (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hrete; lia) | lia ]).
      * (* [comment removed for export] *)
        intros a Ha. 
        destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned spw - 80)) as [Lo|Hi].
        -- eapply store_ok_cell; [| exact (SCR4 a ltac:(u_norm; lia))].
           rewrite M7out by (first [ (clear Odd1 HA4 Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]). rewrite M6out by (first [ (clear Odd1 HA4 Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]). apply M5out. (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]).
        -- eapply store_ok_cell; [apply M7f; (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hrete; lia) | lia ])|]. eapply store_ok_mono; [exact M1grows|]. apply Hscr. (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hrete; lia) | lia ]).
      * (* [comment removed for export] *)
        intros a Ha N0. 
        assert (D5 : M5 a <> None).
        { subst M5. unfold hdr_mem.
          destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 16)) as [A16|A16].
          - rewrite wbytes_outside by (rewrite ?lenW8; cbn; unfold in_rng; u_norm; (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])).
            destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 8)) as [A8|A8].
            + rewrite wbytes_outside by (rewrite ?lenW8; cbn; unfold in_rng; u_norm; (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])).
              apply wbytes_defined_in; rewrite ?lenW8; cbn; (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]).
            + apply wbytes_defined_in; rewrite ?lenW8; cbn; u_norm; (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]).
          - apply wbytes_defined_in; rewrite ?lenW8; cbn; u_norm; (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]). }
        apply D5. destruct (M5 a) as [b|] eqn:HM5; [|reflexivity]. exfalso.
        apply (M7grows a); [apply M6grows; rewrite HM5; discriminate | exact N0].
      * eapply AINV_app; [exact HA4|]. intros a Ha.
        assert (CH : (bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24)%Z \/ (bv_unsigned p <= bv_unsigned a < bv_unsigned p + alloc)%Z).
        { destruct (cell_kept_or_not M6 M7 a) as [E7|N7];
            [| destruct (Z.eq_dec (bv_unsigned a) (bv_unsigned p + n)); [right; (first [ (clear Odd Hcap2 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])|];
               destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 8)); [exfalso; apply N7; apply M7out; (first [ (clear Odd1 HA4 Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])|];
               destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 16)); [left; (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]) | exfalso; apply N7; apply M7out; (first [ (clear Odd1 HA4 Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])] ].
          destruct (cell_kept_or_not M5 M6 a) as [E6|N6];
            [| right; destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned p + s)); [exfalso; apply N6; apply M6out; (first [ (clear Odd1 HA4 Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])|];
               destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned p + n)); [(first [ (clear Odd Hcap2 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]) | exfalso; apply N6; apply M6out; (first [ (clear Odd1 HA4 Odd Hcap2 Hev Hal8 Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])] ].
          destruct (cell_kept_or_not M4 M5 a) as [E5|N5];
            [| left; destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj)); [exfalso; apply N5; apply M5out; (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])|];
               destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 24)); [(first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]) | exfalso; apply N5; apply M5out; (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])] ].
          exfalso. apply Ha. rewrite E7, E6, E5. reflexivity. }
        split.
        -- destruct CH as [CH|CH]; [right; (first [ (clear Odd1 HA4 Pdisj Pimg Pal Odd Hcap2 Hev Hal8 Hal3 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ]) | left; exists (bv_unsigned p), alloc; split; [exact InP | (first [ (clear Odd Hcap2 Lb Hdimg Hcap8 Hsp16 Hrete; lia) | lia ])]].
        -- intros N0. apply Ha. rewrite N0. destruct (M4 a) as [b|] eqn:HM4; [|reflexivity].
           exfalso. apply (M7grows a); [apply M6grows, M5grows; rewrite HM4; discriminate | exact N0].
      * exact Hh4.
      * exact Hl4.
      * exact Hm4.
      * rewrite Hfs4. exact Hfs2.
      * rewrite Hfds4. exact Hfds2.
Qed.
End GROW.
