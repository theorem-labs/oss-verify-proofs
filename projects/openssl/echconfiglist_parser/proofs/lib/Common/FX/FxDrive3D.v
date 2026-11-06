(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg LazyCfg LazyAccCfg AllocLazyCfg EagerCfg CountCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn
  FxLazy FxSys FxDrive FxCellFrame FxDrive3 FxDrive3N FxDrive3S FxDrive3C.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.



(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive dtree3 : Type :=
| D3Leaf (F : fstate) (L : fledger3) (n : int) (r : stop)
| D3Fork (t1 t2 : dtree3).

Fixpoint leaf_in3 (x : fstate * fledger3 * int * stop) (t : dtree3) : Prop :=
  match t with
  | D3Leaf F L n r => x = (F, L, n, r)
  | D3Fork t1 t2 => leaf_in3 x t1 \/ leaf_in3 x t2
  end.

Section Drive3DDefs.
Local Open Scope uint63_scope.
Variable IM : fimage.
Variable code : itrie finstr.
Variable Rb Rc Lim : Z.
Variable keep : list int.
Variable shp : int -> bool.
Variable xsys3 : fstate -> fledger3 -> int -> option dres3.
Variable xask : fstate -> option (int * int).
(* [comment removed for export] *)
Variable xpc : fstate -> fledger3 -> int -> option dres3.

Definition drive_sys_own3 (F : fstate) (L3 : fledger3) (n : int) : option dres3 :=
  if negb (ecall_here code F) then None else
  match conc (rget F 17) with
  | None => None
  | Some nr =>
    if nr =? 222 then
      match conc (rget F 11), conc (rget F 12), conc (rget F 13), conc (rget F 15) with
      | Some len, Some prot, Some flags, Some o =>
          if negb (o =? 0) then None
          else if (prot =? 3) && (flags =? 34) then sys_grant3p Rb Rc Lim shp false F L3 n len
          else if (prot =? 3) && (flags =? 16418) then sys_grant3p Rb Rc Lim shp true F L3 n len
          else if (prot =? 3) && (flags =? 50) then
            match ptr (rget F 10) with
            | Some (t, off) => sys_commit3 Lim keep F L3 n t off len
            | None => None
            end
          else None
      | _, _, _, _ => None
      end
    else if nr =? 215 then
      match ptr (rget F 10), conc (rget F 11) with
      | Some (t, off), Some len => sys_unmap3p Lim keep F L3 n t off len
      | _, _ => None
      end
    else None
  end.

Definition drive_sys3 (F : fstate) (L3 : fledger3) (n : int) : option dres3 :=
  match drive_sys_own3 F L3 n with
  | Some r => Some r
  | None => xsys3 F L3 n
  end.

Definition ask_split3 (F : fstate) (L3 : fledger3) (n : int) : option (fstate * fstate) :=
  match xask F with
  | Some (t, thr) => refine3 (fl3 L3) F n t thr
  | None => None
  end.

Fixpoint drive3 (bp : int) (k : nat) (fuel : nat) (F : fstate) (L3 : fledger3) (n : int) : dtree3 :=
  match fuel with
  | O => D3Leaf F L3 n SFuel
  | S fuel' =>
      match fx_run IM code bp k F with
      | (F1, r, _) =>
          match r with
          | SFuel => drive3 bp k fuel' F1 L3 n
          | SEcall =>
              match drive_sys3 F1 L3 n with
              | Some (D3One F2 L2 n2) => drive3 bp k fuel' F2 L2 n2
              | Some (D3Two F2 L2 n2 F3 L3' n3) =>
                  D3Fork (drive3 bp k fuel' F2 L2 n2) (drive3 bp k fuel' F3 L3' n3)
              | None => D3Leaf F1 L3 n SEcall
              end
          | SStuck _ =>
              match xpc F1 L3 n with
              | Some (D3One F2 L2 n2) => drive3 bp k fuel' F2 L2 n2
              | Some (D3Two F2 L2 n2 F3 L3' n3) =>
                  D3Fork (drive3 bp k fuel' F2 L2 n2) (drive3 bp k fuel' F3 L3' n3)
              | None =>
                  match ask_split3 F1 L3 n with
                  | Some (Fa, Fb) => D3Fork (drive3 bp k fuel' Fa L3 n) (drive3 bp k fuel' Fb L3 n)
                  | None => D3Leaf F1 L3 n r
                  end
              end
          | SBreak => D3Leaf F1 L3 n r
          end
      end
  end.

End Drive3DDefs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Drive3D.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Hypothesis Halloc : sc_alloc cfg = false.
Variable R0 : list (word * word).
Variable Rb Rc Lim : Z.
Hypothesis HRb : live_bytes R0 <= Rb.
Hypothesis HRc : Z.of_nat (length R0) <= Rc.
Variable keep : list int.
Variable mem0 : word -> option byte.
Variable XI : (int -> word) -> Model -> Prop.
Variable xtags : list int.
Hypothesis XI_rho : forall rho rho' m, (forall t, In t xtags -> rho' t = rho t) -> XI rho m -> XI rho' m.
Hypothesis XI_vm : forall rho m m', same_but_vm m m' -> XI rho m -> XI rho m'.
Variable fr0 : bvmap 5 word.
Variable fc0 : bv 32.
Variable rom0 : word -> option byte.
Variable hi : word -> Prop.
(* [comment removed for export] *)
Variable wb0 : word.
Variable na0 lz0 : list (word * word).
Variable brk0 : word.
(* [comment removed for export] *)
Variable A0 : list (Z * Z).

Local Abbreviation DI := (DInv cfg segs IM R0 BIG RTgt keep mem0 XI xtags).
Local Abbreviation D3 := (DInv3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation NE := (node_ext cfg segs IM R0 BIG RTgt keep mem0 XI xtags).
Local Abbreviation Rn := (FxRn.Rn segs IM).
Local Abbreviation erase := (FxDrive3.erase wb0).

Variable shp : int -> bool.
Variable xsys3 : fstate -> fledger3 -> int -> option dres3.
Variable xask : fstate -> option (int * int).
Variable xpc : fstate -> fledger3 -> int -> option dres3.

Local Abbreviation SOK := (sys_ok3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).

(* [comment removed for export] *)
Hypothesis xsys3_sound : forall n rho F L3 ms m res,
  xsys3 F L3 n = Some res -> D3 n rho F L3 ms m ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  SOK n rho F L3 res ms m.

(* [comment removed for export] *)
Hypothesis xpc_sound : forall n rho F L3 ms m res,
  xpc F L3 n = Some res -> D3 n rho F L3 ms m ->
  pc_ok3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0 n rho F L3 res ms m.

Theorem drive_sys_own3_sound n rho F L3 ms m res :
  drive_sys_own3 code Rb Rc Lim keep shp F L3 n = Some res ->
  D3 n rho F L3 ms m ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  SOK n rho F L3 res ms m.
Proof.
  intros Hsys HD Hstep. pose proof HD as ((HRn & H0 & _) & _).
  pose proof (Rn_R _ _ _ _ _ _ HRn H0) as HR.
  unfold drive_sys_own3 in Hsys.
  destruct (ecall_here code F) eqn:Hec; cbn [negb] in Hsys; [|discriminate].
  pose proof (ecall_here_at segs code Hcode F Hec) as Hat.
  destruct (conc (FxState.rget F 17)) as [nr|] eqn:Hnr; [|discriminate].
  destruct (conc_sound R0 rho _ _ H0 Hnr) as [_ Hx8]. rewrite <- (pend_x8 segs IM rho F ms HR) in Hx8.
  destruct (nr =? 222)%uint63 eqn:E222.
  { apply eqb_lit in E222. change (to_Z 222) with 222 in E222. rewrite E222 in Hx8.
    destruct (conc (FxState.rget F 11)) as [len|] eqn:H11; [|discriminate].
    destruct (conc (FxState.rget F 12)) as [prot|] eqn:H12; [|discriminate].
    destruct (conc (FxState.rget F 13)) as [flags|] eqn:H13; [|discriminate].
    destruct (conc (FxState.rget F 15)) as [o|] eqn:H15; [|discriminate].
    destruct (conc_sound R0 rho _ _ H0 H11) as [_ Ha1]. rewrite <- (pend_gpr1 segs IM rho F ms HR) in Ha1.
    destruct (conc_sound R0 rho _ _ H0 H12) as [_ Ha2]. rewrite <- (pend_gpr2 segs IM rho F ms HR) in Ha2.
    destruct (conc_sound R0 rho _ _ H0 H13) as [_ Ha3]. rewrite <- (pend_gpr3 segs IM rho F ms HR) in Ha3.
    destruct (conc_sound R0 rho _ _ H0 H15) as [_ Ha5]. rewrite <- (pend_gpr5 segs IM rho F ms HR) in Ha5.
    destruct (o =? 0)%uint63 eqn:Eo; cbn [negb] in Hsys; [|discriminate].
    apply eqb_lit in Eo. rewrite Eo, to_Z_0 in Ha5.
    destruct ((prot =? 3)%uint63 && (flags =? 34)%uint63) eqn:Eg.
    { apply andb_true_iff in Eg as [Ep Ef]. apply eqb_lit in Ep, Ef. rewrite Ep in Ha2. rewrite Ef in Ha3.
      exact (sys_grant3p_sound cfg segs IM Halloc R0 Rb Rc Lim HRb HRc keep mem0 XI xtags XI_rho XI_vm fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0 shp
               n rho F L3 ms m false len res Hsys HD Hat Hstep Hx8 Ha1 Ha2 Ha3 Ha5). }
    destruct ((prot =? 3)%uint63 && (flags =? 16418)%uint63) eqn:Enr.
    { apply andb_true_iff in Enr as [Ep Ef]. apply eqb_lit in Ep, Ef. rewrite Ep in Ha2. rewrite Ef in Ha3.
      exact (sys_grant3p_sound cfg segs IM Halloc R0 Rb Rc Lim HRb HRc keep mem0 XI xtags XI_rho XI_vm fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0 shp
               n rho F L3 ms m true len res Hsys HD Hat Hstep Hx8 Ha1 Ha2 Ha3 Ha5). }
    destruct ((prot =? 3)%uint63 && (flags =? 50)%uint63) eqn:Ecm; [|discriminate].
    apply andb_true_iff in Ecm as [Ep Ef]. apply eqb_lit in Ep, Ef. rewrite Ep in Ha2. rewrite Ef in Ha3.
    destruct (ptr (FxState.rget F 10)) as [[t off]|] eqn:H10; [|discriminate].
    pose proof (ptr_sound rho _ _ _ H10) as Ha0. rewrite <- (pend_gpr0 segs IM rho F ms HR) in Ha0.
    exact (sys_commit3_sound cfg segs IM Halloc R0 Lim keep mem0 XI xtags XI_vm fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
             n rho F L3 ms m t off len res Hsys HD Hat Hstep Hx8 Ha0 Ha1 Ha2 Ha3 Ha5). }
  destruct (nr =? 215)%uint63 eqn:E215; [|discriminate].
  apply eqb_lit in E215. change (to_Z 215) with 215 in E215. rewrite E215 in Hx8.
  destruct (ptr (FxState.rget F 10)) as [[t off]|] eqn:H10; [|discriminate].
  destruct (conc (FxState.rget F 11)) as [len|] eqn:H11; [|discriminate].
  pose proof (ptr_sound rho _ _ _ H10) as Ha0. rewrite <- (pend_gpr0 segs IM rho F ms HR) in Ha0.
  destruct (conc_sound R0 rho _ _ H0 H11) as [_ Ha1]. rewrite <- (pend_gpr1 segs IM rho F ms HR) in Ha1.
  exact (sys_unmap3p_sound cfg segs IM R0 Lim keep mem0 XI xtags XI_vm fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0 shp
           n rho F L3 ms m t off len res Hsys HD Hat Hstep Hx8 Ha0 Ha1).
Qed.

Theorem drive_sys3_sound n rho F L3 ms m res :
  drive_sys3 code Rb Rc Lim keep shp xsys3 F L3 n = Some res ->
  D3 n rho F L3 ms m ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  SOK n rho F L3 res ms m.
Proof.
  unfold drive_sys3. intros Hsys HD Hstep.
  destruct (drive_sys_own3 code Rb Rc Lim keep shp F L3 n) as [r|] eqn:Hown.
  - injection Hsys as <-. exact (drive_sys_own3_sound n rho F L3 ms m r Hown HD Hstep).
  - exact (xsys3_sound n rho F L3 ms m res Hsys HD Hstep).
Qed.

Lemma dext_lazy_frame n rho m m1 : lazy_frame m m1 -> dext n rho m n rho m1.
Proof.
  intros Hfr. destruct (lazy_frame_facts m m1 Hfr) as (_ & Evm & _).
  split; [lia|]. split; [intros; reflexivity|]. split; [exact (lazy_frame_same_but_vm m m1 Hfr)|].
  rewrite Evm. repeat split; reflexivity.
Qed.

Local Abbreviation PX := (pext IM).
Local Abbreviation ptrans := (pext_trans IM R0).

(* [comment removed for export] *)
Lemma pext_frame n rho F L3 ms m F1 ms1 m1 :
  lazy_frame m m1 -> mfr IM rho F L3 ms n rho F1 L3 ms1 -> PX n rho F L3 ms m n rho F1 L3 ms1 m1.
Proof. intros Hfr Hm. split; [exact (dext_lazy_frame n rho m m1 Hfr) | exact Hm]. Qed.

Local Abbreviation drv3 := (drive3 IM code Rb Rc Lim keep shp xsys3 xask xpc).

(* [comment removed for export] *)
Theorem drive3_universal : forall bp k, (k <= 61)%nat -> forall fuel n rho F L3 ms m T,
  D3 n rho F L3 ms m ->
  (forall F' L3' n' r, leaf_in3 (F', L3', n', r) (drv3 bp k fuel F L3 n) ->
     forall rho' ms' m', D3 n' rho' F' L3' ms' m' -> PX n rho F L3 ms m n' rho' F' L3' ms' m' ->
       (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms')) ->
       realizes_cfg cfg segs (mkCfg ms' m') T) ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros bp k Hk fuel n0 rho0 F0 L0 ms0 m0 T HD0 Hleaf0.
  cut (forall fuel n rho F L3 ms m,
         D3 n rho F L3 ms m -> PX n0 rho0 F0 L0 ms0 m0 n rho F L3 ms m ->
         (forall F' L3' n' r, leaf_in3 (F', L3', n', r) (drv3 bp k fuel F L3 n) ->
            forall rho' ms' m', D3 n' rho' F' L3' ms' m' -> PX n0 rho0 F0 L0 ms0 m0 n' rho' F' L3' ms' m' ->
              (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms')) ->
              realizes_cfg cfg segs (mkCfg ms' m') T) ->
         realizes_cfg cfg segs (mkCfg ms m) T).
  { intros Hgen. exact (Hgen fuel n0 rho0 F0 L0 ms0 m0 HD0 (pext_refl IM R0 rom0 hi _ _ _ _ _ _) Hleaf0). }
  clear fuel HD0 Hleaf0.
  induction fuel as [|fuel IH]; intros n rho F L3 ms m HD Hext Hleaf.
  - apply (Hleaf F L3 n SFuel (eq_refl) rho ms m HD Hext). discriminate.
  - cbn [drive3] in Hleaf.
    destruct (fx_run IM code bp k F) as [[F1 r] cnt] eqn:Hrun.
    destruct (DInv3_run cfg segs IM code Hcode R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
                n rho F L3 ms m bp k F1 r cnt Hk Hrun HD) as (ms1 & Hsteps & Hec & Hmfr1 & Huniv & _).
    apply Huniv. intros m1 Hfr1 HD1.
    pose proof (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hext (pext_frame n rho F L3 ms m F1 ms1 m1 Hfr1 Hmfr1)) as Hext1.
    destruct r as [| | |c].
    + exact (IH n rho F1 L3 ms1 m1 HD1 Hext1 Hleaf).
    + destruct (drive_sys3 code Rb Rc Lim keep shp xsys3 F1 L3 n) as [res|] eqn:Hsys.
      * destruct (DInv3_pend cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0 n rho F1 L3 ms1 m1 HD1 (Hec eq_refl))
          as [Hpend _].
        apply Hpend. intros m2 Hfr2 HD2.
        pose proof (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hext1
                      (pext_frame n rho F1 L3 ms1 m1 F1 ms1 m2 Hfr2 (mfr_refl IM rho F1 L3 ms1 n))) as Hext2.
        destruct (drive_sys3_sound n rho F1 L3 ms1 m2 res Hsys HD2 (Hec eq_refl))
          as (I & i0 & nx & Hiff & Hsucc).
        apply (rzc_cases_same cfg segs _ I nx T i0).
        { apply node_ok_cfg_of_step_iff. exact Hiff. }
        intros i. destruct (Hsucc i) as (F' & L3' & n' & rho' & Hin & HD' & Hdx).
        destruct (nx i) as [msi mi]. cbn [cfg_ms cfg_model] in HD', Hdx.
        apply (IH n' rho' F' L3' msi mi HD' (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hext2 Hdx)).
        intros F'' L'' n'' r'' Hl. apply Hleaf.
        destruct res as [F2 L2 n2 | F2 L2 n2 F3 L3'' n3]; cbn [dres3_in] in Hin.
        -- injection Hin as -> -> ->. exact Hl.
        -- destruct Hin as [Hin|Hin]; injection Hin as -> -> ->; cbn [leaf_in3]; [left | right]; exact Hl.
      * exact (Hleaf F1 L3 n SEcall eq_refl rho ms1 m1 HD1 Hext1 Hec).
    + apply (Hleaf F1 L3 n SBreak eq_refl rho ms1 m1 HD1 Hext1). discriminate.
    + destruct (xpc F1 L3 n) as [res|] eqn:Hxpc.
      { destruct (xpc_sound n rho F1 L3 ms1 m1 res Hxpc HD1) as [Hcps _].
        apply Hcps. intros F' L3' n' rho' ms' m' Hin HD' Hdx.
        apply (IH n' rho' F' L3' ms' m' HD' (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hext1 Hdx)).
        intros F'' L'' n'' r'' Hl. apply Hleaf.
        destruct res as [F2 L2 n2 | F2 L2 n2 F3 L3'' n3]; cbn [dres3_in] in Hin.
        - injection Hin as -> -> ->. exact Hl.
        - destruct Hin as [Hin|Hin]; injection Hin as -> -> ->; cbn [leaf_in3]; [left | right]; exact Hl. }
      destruct (ask_split3 xask F1 L3 n) as [[Fa Fb]|] eqn:Hask.
      * unfold ask_split3 in Hask. destruct (xask F1) as [[ta thr]|]; [|discriminate].
        destruct (mfr_refine3 IM n rho F1 L3 ms1 (fl3 L3) ta thr Fa Fb Hask) as [Hma Hmb].
        destruct (DInv3_refine3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0 shp
                    n rho F1 L3 ms1 m1 ta thr Fa Fb HD1 Hask) as [HDa|HDb].
        -- apply (IH n rho Fa L3 ms1 m1 HDa
                    (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hext1 (pext_frame n rho F1 L3 ms1 m1 Fa ms1 m1 (lazy_frame_refl m1) Hma))).
           intros F'' L'' n'' r'' Hl. apply Hleaf. cbn [leaf_in3]. left. exact Hl.
        -- apply (IH n rho Fb L3 ms1 m1 HDb
                    (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hext1 (pext_frame n rho F1 L3 ms1 m1 Fb ms1 m1 (lazy_frame_refl m1) Hmb))).
           intros F'' L'' n'' r'' Hl. apply Hleaf. cbn [leaf_in3]. right. exact Hl.
      * apply (Hleaf F1 L3 n (SStuck c) eq_refl rho ms1 m1 HD1 Hext1). discriminate.
Qed.

(* [comment removed for export] *)
Theorem drive3_existential : forall bp k, (k <= 61)%nat -> forall fuel n rho F L3 ms m,
  D3 n rho F L3 ms m ->
  exists F' L3' n' r rho' ms' m',
    leaf_in3 (F', L3', n', r) (drv3 bp k fuel F L3 n)
    /\ star_cfg segs cfg (mkCfg ms m) [] (mkCfg ms' m')
    /\ D3 n' rho' F' L3' ms' m'
    /\ PX n rho F L3 ms m n' rho' F' L3' ms' m'
    /\ (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms')).
Proof.
  intros bp k Hk. induction fuel as [|fuel IH]; intros n rho F L3 ms m HD.
  - exists F, L3, n, SFuel, rho, ms, m. split; [reflexivity|]. split; [apply star_cfg_refl|].
    split; [exact HD|]. split; [apply (pext_refl IM R0 rom0 hi) | discriminate].
  - cbn [drive3].
    destruct (fx_run IM code bp k F) as [[F1 r] cnt] eqn:Hrun.
    destruct (DInv3_run cfg segs IM code Hcode R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
                n rho F L3 ms m bp k F1 r cnt Hk Hrun HD) as (ms1 & Hsteps & Hec & Hmfr1 & _ & (m1 & Hfr1 & HD1 & Hstar1)).
    pose proof (pext_frame n rho F L3 ms m F1 ms1 m1 Hfr1 Hmfr1) as Hext1.
    destruct r as [| | |c].
    + destruct (IH n rho F1 L3 ms1 m1 HD1) as (F' & L' & n' & r' & rho' & ms' & m' & Hl & Hst & HD' & Hext' & He').
      exists F', L', n', r', rho', ms', m'. split; [exact Hl|].
      split; [exact (star_cfg_trans cfg segs _ [] _ [] _ Hstar1 Hst)|]. split; [exact HD'|].
      split; [exact (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hext1 Hext') | exact He'].
    + destruct (drive_sys3 code Rb Rc Lim keep shp xsys3 F1 L3 n) as [res|] eqn:Hsys.
      * destruct (DInv3_pend cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0 n rho F1 L3 ms1 m1 HD1 (Hec eq_refl))
          as [_ (m2 & Hfr2 & HD2 & Hstar2)].
        pose proof (pext_frame n rho F1 L3 ms1 m1 F1 ms1 m2 Hfr2 (mfr_refl IM rho F1 L3 ms1 n)) as Hext2.
        destruct (drive_sys3_sound n rho F1 L3 ms1 m2 res Hsys HD2 (Hec eq_refl))
          as (I & i0 & nx & Hiff & Hsucc).
        destruct (Hsucc i0) as (F2 & L2 & n2 & rho2 & Hin & HD3 & Hdx).
        assert (Hstep : sstep_cfg segs cfg (mkCfg (ms_pend ms1) m2) [] (SNext (nx i0))).
        { apply Hiff. exists i0. split; reflexivity. }
        destruct (nx i0) as [msi mi]. cbn [cfg_ms cfg_model] in HD3, Hdx.
        destruct (IH n2 rho2 F2 L2 msi mi HD3) as (F' & L' & n' & r' & rho' & ms' & m' & Hl & Hst & HD' & Hext' & He').
        exists F', L', n', r', rho', ms', m'. split; [|split; [|split; [exact HD' | split; [|exact He']]]].
        -- destruct res as [Fa La na | Fa La na Fb Lb nb]; cbn [dres3_in] in Hin.
           ++ injection Hin as -> -> ->. exact Hl.
           ++ destruct Hin as [Hin|Hin]; injection Hin as -> -> ->; cbn [leaf_in3]; [left | right]; exact Hl.
        -- exact (star_cfg_trans cfg segs _ [] _ [] _ Hstar1
                    (star_cfg_trans cfg segs _ [] _ [] _ Hstar2
                       (star_cfg_trans cfg segs _ [] _ [] _ (star_cfg_one cfg segs _ _ _ Hstep) Hst))).
        -- exact (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hext1
                    (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hext2 (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hdx Hext'))).
      * exists F1, L3, n, SEcall, rho, ms1, m1. split; [reflexivity|]. split; [exact Hstar1|].
        split; [exact HD1|]. split; [exact Hext1 | exact Hec].
    + exists F1, L3, n, SBreak, rho, ms1, m1. split; [reflexivity|]. split; [exact Hstar1|].
      split; [exact HD1|]. split; [exact Hext1 | discriminate].
    + destruct (xpc F1 L3 n) as [res|] eqn:Hxpc.
      { destruct (xpc_sound n rho F1 L3 ms1 m1 res Hxpc HD1) as [_ (F2 & L2 & n2 & rho2 & ms2 & m2 & Hin & HD2 & Hdx & Hstar2)].
        destruct (IH n2 rho2 F2 L2 ms2 m2 HD2) as (F' & L' & n' & r' & rho' & ms' & m' & Hl & Hst & HD' & Hext' & He').
        exists F', L', n', r', rho', ms', m'. split; [|split; [|split; [exact HD' | split; [|exact He']]]].
        - destruct res as [Fa La na | Fa La na Fb Lb nb]; cbn [dres3_in] in Hin.
          + injection Hin as -> -> ->. exact Hl.
          + destruct Hin as [Hin|Hin]; injection Hin as -> -> ->; cbn [leaf_in3]; [left | right]; exact Hl.
        - exact (star_cfg_trans cfg segs _ [] _ [] _ Hstar1 (star_cfg_trans cfg segs _ [] _ [] _ Hstar2 Hst)).
        - exact (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hext1 (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hdx Hext')). }
      destruct (ask_split3 xask F1 L3 n) as [[Fa Fb]|] eqn:Hask.
      * unfold ask_split3 in Hask. destruct (xask F1) as [[ta thr]|]; [|discriminate].
        destruct (mfr_refine3 IM n rho F1 L3 ms1 (fl3 L3) ta thr Fa Fb Hask) as [Hma Hmb].
        destruct (DInv3_refine3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0 shp
                    n rho F1 L3 ms1 m1 ta thr Fa Fb HD1 Hask) as [HDa|HDb].
        -- destruct (IH n rho Fa L3 ms1 m1 HDa) as (F' & L' & n' & r' & rho' & ms' & m' & Hl & Hst & HD' & Hext' & He').
           exists F', L', n', r', rho', ms', m'. split; [cbn [leaf_in3]; left; exact Hl|].
           split; [exact (star_cfg_trans cfg segs _ [] _ [] _ Hstar1 Hst)|]. split; [exact HD'|].
           split; [|exact He'].
           exact (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hext1
                    (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pext_frame n rho F1 L3 ms1 m1 Fa ms1 m1 (lazy_frame_refl m1) Hma) Hext')).
        -- destruct (IH n rho Fb L3 ms1 m1 HDb) as (F' & L' & n' & r' & rho' & ms' & m' & Hl & Hst & HD' & Hext' & He').
           exists F', L', n', r', rho', ms', m'. split; [cbn [leaf_in3]; right; exact Hl|].
           split; [exact (star_cfg_trans cfg segs _ [] _ [] _ Hstar1 Hst)|]. split; [exact HD'|].
           split; [|exact He'].
           exact (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hext1
                    (ptrans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pext_frame n rho F1 L3 ms1 m1 Fb ms1 m1 (lazy_frame_refl m1) Hmb) Hext')).
      * exists F1, L3, n, (SStuck c), rho, ms1, m1. split; [reflexivity|]. split; [exact Hstar1|].
        split; [exact HD1|]. split; [exact Hext1 | discriminate].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma DInv3_ledger_inv n rho F L3 ms m :
  D3 n rho F L3 ms m ->
  ledger_inv R0 BIG (fl_c (fl3 L3)) (fl_S (fl3 L3)) (erase_vm wb0 (m_vmmaps m)).
Proof. intros ((_ & _ & _ & _ & Hli & _) & _). exact Hli. Qed.

Lemma DInv3_maps_facts n rho F L3 ms m :
  D3 n rho F L3 ms m ->
  let h := m_vmmaps m in
  vm_reserved h = R0
  /\ sp_window_lo <= bv_unsigned (vm_init_sp h) <= sp_window_hi
  /\ Forall (fun p => 0 < e_sz p) (vm_maps h)
  /\ Forall (fun p => e_lo p mod page_size = 0 /\ e_sz p mod page_size = 0) (vm_maps h)
  /\ Forall (fun p => 0 < e_lo p /\ e_hi p <= alloc_top h) (vm_maps h)
  /\ Forall (fun p => Forall (e_disj p) R0) (vm_maps h)
  /\ pw_disj (vm_maps h)
  /\ Z.of_nat (length (vm_maps h)) <= fl_c (fl3 L3)
  /\ live_bytes (vm_maps h) <= fl_S (fl3 L3).
Proof.
  intros HD. pose proof (DInv3_ledger_inv n rho F L3 ms m HD) as [].
  cbv zeta. repeat split; assumption.
Qed.

Lemma DInv3_halted n rho F L3 ms m : D3 n rho F L3 ms m -> m_halted m = None.
Proof. intros ((_ & _ & Hh & _) & _). exact Hh. Qed.

(* [comment removed for export] *)
Lemma DInv3_ent_in n rho F L3 ms m :
  D3 n rho F L3 ms m -> Forall (ent_in (f_mem F)) (fl_maps (fl3 L3)).
Proof.
  intros ((_ & _ & _ & _ & _ & _ & (Hm1 & _ & _) & _) & _).
  eapply Forall_impl; [|exact Hm1]. intros e He. exact (proj1 (proj1 (ent_ok_iff _ _ _ _) He)).
Qed.

(* [comment removed for export] *)
Lemma DInv3_mirrors n rho F L3 ms m :
  D3 n rho F L3 ms m ->
  vm_maps (m_vmmaps m) = map (den rho) (fl_all L3)
  /\ vm_noaccess (m_vmmaps m) = na_apply rho (fl_ops L3) na0
  /\ m_vm_lazy m = lz_apply rho (fl_ops L3) lz0
  /\ lazy_pw rho (m_vm_lazy m) (fl_lazy L3)
  /\ Forall (fun e => In e (fl_maps (fl3 L3)) \/ fent_tag e = 0%uint63 \/ iget (fent_tag e) (f_mem F) = None) (fl_all L3)
  /\ lazy_cov (fl_all L3) (fl_lazy L3)
  /\ vm_limit (m_vmmaps m) = Lim                                  (* [comment removed for export] *)
  /\ Forall (fun q => e_hi q <= 2 ^ 64) (vm_noaccess (m_vmmaps m))
  /\ Forall (fun q => e_hi q <= 2 ^ 64) (m_vm_lazy m).
Proof. intros (_ & [] & _). repeat split; assumption. Qed.

(* [comment removed for export] *)
Lemma DInv3_ops n rho F L3 ms m :
  D3 n rho F L3 ms m -> Forall (op_ok rho m (fl_all L3)) (fl_ops L3).
Proof. intros (_ & HL & _). exact (lp_opsF _ _ _ _ _ _ _ _ _ _ _ HL). Qed.

(* [comment removed for export] *)
Lemma DInv3_pages n rho F L3 ms m :
  D3 n rho F L3 ms m ->
  page_inv (allowed A0 rho L3) m
  /\ Forall (fun p => page_in_ranges p (m_vm_lazy m) = true) (m_vm_materialized m)
  /\ eager_used m <= fl_E L3
  /\ A_bytes (allowed A0 rho L3) <= fl_Ab L3
  /\ fl_E L3 + fl_Ab L3 <= Lim.
Proof.
  intros (_ & HL & _).
  split; [exact (lp_pi _ _ _ _ _ _ _ _ _ _ _ HL)|]. split; [exact (lp_mat _ _ _ _ _ _ _ _ _ _ _ HL)|].
  split; [exact (lp_E _ _ _ _ _ _ _ _ _ _ _ HL)|]. split; [exact (lp_Ab _ _ _ _ _ _ _ _ _ _ _ HL) | exact (lp_acct _ _ _ _ _ _ _ _ _ _ _ HL)].
Qed.

(* [comment removed for export] *)
Lemma DInv3_ShZ n rho F L3 ms m (x : word) :
  D3 n rho F L3 ms m -> in_shadow (bv_unsigned x) -> no_region rho (f_mem F) (bv_unsigned x) ->
  ~ exempted rho (fl_ex L3) (bv_unsigned x) ->
  rview segs (ms_mem ms) x = Some (Z_to_bv 8 0) /\ wview segs (ms_mem ms) x <> None.
Proof. intros (_ & _ & [Hz _ _ _] & _) Hx Hno Hne. exact (Hz x Hx Hno Hne). Qed.

Lemma DInv3_exempt n rho F L3 ms m : D3 n rho F L3 ms m -> lazy_cov (fl_all L3) (fl_ex L3).
Proof. intros (_ & _ & [_ _ _ He] & _). exact He. Qed.

(* [comment removed for export] *)
Lemma DInv3_ops_off_R0 n rho F L3 ms m :
  D3 n rho F L3 ms m ->
  forall o x p, In o (fl_ops L3) -> In p R0 ->
    e_lo (den rho (snd o)) <= x < e_hi (den rho (snd o)) -> ~ (e_lo p <= x < e_hi p).
Proof. intros (_ & HL & _). exact (lp_opsR _ _ _ _ _ _ _ _ _ _ _ HL). Qed.

Lemma pext_frame_image n rho F L3 ms m n' rho' F' L3' ms' m' (x : word) :
  D3 n' rho' F' L3' ms' m' -> PX n rho F L3 ms m n' rho' F' L3' ms' m' ->
  (~ claimed_wr IM rho (f_mem F) x \/ ~ cell_expl rho' (f_mem F') x) ->
  (exists p, In p R0 /\ e_lo p <= bv_unsigned x < e_hi p) ->
  ms_mem ms' x = ms_mem ms x.
Proof.
  intros HD' [_ (new & Eops & _ & HA & _)] Hnc (p & Hp & Hxp).
  apply (HA x); [|exact Hnc]. intros (o & Ho & Hx).
  apply (DInv3_ops_off_R0 n' rho' F' L3' ms' m' HD' o (bv_unsigned x) p); [|exact Hp | exact Hx | exact Hxp].
  rewrite Eops. apply in_app_iff. right. exact Ho.
Qed.

(* [comment removed for export] *)
Lemma DInv3_brk n rho F L3 ms m : D3 n rho F L3 ms m -> vm_brk (m_vmmaps m) = brk0.
Proof. intros (_ & _ & _ & (_ & _ & _ & _ & Hb)). exact Hb. Qed.

End Drive3D.
