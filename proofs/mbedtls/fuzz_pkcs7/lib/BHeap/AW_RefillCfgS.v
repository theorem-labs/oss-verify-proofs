(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AJ AKinvS AKinvM AW_Unwind AW_Unwind2 AW_MmapFixed AW_Poison AW_DepotCfg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_CfgS AW_ClassId AW_Combined AW_Refill AW_GetFrom AW_Populate AW_Populate2 AW_CfgDefs AW_PopulateCfgS AW_GetFromCfgS AW_EmbCfg AW_EmbLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ahx.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ahx. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_RefillCfgS () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_size"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.max_count"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.thr_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CfgDefs.mwc_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CfgDefs.pop_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.b12_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "ARUN_1.RefillCfgS.rf_cpostS"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.True"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_EmbCfg.exh_xpost"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Combined.A_REFILL"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Refill.pc_old"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Refill.pc_new"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.



Section RefillCfgS.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  (* [comment removed for export] *)
  Variable CSf : option bool -> option bool -> Z -> Prop.
  Hypothesis CSOKf : forall u f, cs_ok AL (CSf u f).
  Hypothesis CSmono_u : forall b f y, CSf None f y -> CSf (Some b) f y.
  Hypothesis CSmono_f : forall u b y, CSf u None y -> CSf u (Some b) y.
  Hypothesis ASB : al_sb AL = 0x7fff8000.

  (* [comment removed for export] *)
  Variables (T CTX SB RI c : Z).
  Let R := RI + 128 * c.
  Let RB := SB + c * 2^32.
  Let FA := RB + 0xE0000000.
  Hypothesis GSB : 0x10007fff9000 <= SB /\ SB mod 4096 = 0 /\ RI = SB + 2^37 /\ RI + 4096 <= ACEIL.
  Hypothesis GC : 1 <= c <= 31.
  Hypothesis GT : (Timg T /\ Tband T) /\ T + 4096 <= ACEIL /\ T mod 4096 = 0.
  Hypothesis GCTX : (0x65f000 <= CTX /\ Pband CTX 0x10000) /\ CTX + 0x10000 <= ACEIL.
  Hypothesis GSEP : ltac2:(CDefT.buildp (gd_tbl_AW_RefillCfgS ()) "(0.(1.(2.(3.VT,+1000.)VSB,)(2.(3.(3.VSB,(4.+2.+25.))+1000.)VT,))(0.(1.(2.(3.VCTX,+10000.)VT,)(2.(3.VT,+1000.)VCTX,))(1.(2.(3.VCTX,+10000.)VSB,)(2.(3.(3.VSB,(4.+2.+25.))+1000.)VCTX,))))")
(* [comment removed for export] *).
  Hypothesis CST : forall u f, crange (CSf u f) T 4096.
  Hypothesis CSCTX : forall u f, crange (CSf u f) CTX 0x10000.
  Hypothesis CSRI : forall u f, crange (CSf u f) RI 4096.

  (* [comment removed for export] *)
  Variable K : option bool -> option bool -> Model -> Prop.
  Hypothesis KL : forall u f, kinv AL (CSf u f) (K u f).
  Variables (mu mfa : Z).   (* [comment removed for export] *)
  Let UA := RB + mu.
  Let FAA := FA + mfa.
  Hypothesis LEDGER_U : ltac2:(CDefT.buildp (gd_tbl_AW_RefillCfgS ()) "Pmo,$5.P,(2.(3.Vmu,(4.+2.+12.))+>0000000.)P,A3.VK,(6.$7.)(6.$7.)R2.(0.(8.$7.(9.(:.(;.R3.))(<.&40.VUA,)(<.&40.(4.+2.+12.)))$=.)(1.(8.$7.(>.(?.(;.R3.))(<.&40.VUA,)(<.&40.(4.+2.+12.)))$=.)(8.$7.(9.(10.(11.(12.&40.)(12.&40.))(:.(;.R3.))(?.(;.R3.)))(<.&40.VUA,)(<.&40.(4.+2.+12.)))$=.)))")
(* [comment removed for export] *).
  Hypothesis TU_commit : ltac2:(CDefT.buildp (gd_tbl_AW_RefillCfgS ()) "Pmo,$5.P,(2.(3.Vmu,(4.+2.+12.))+>0000000.)P,A3.VK,(6.$7.)(6.$7.)R2.P,(8.$7.(>.(?.(;.R3.))(<.&40.VUA,)(<.&40.(4.+2.+12.)))$=.)A3.VK,(13.$7.$=.)(6.$7.)(14.+32.VUA,(4.+2.+12.)R4.)")
(* [comment removed for export] *).
  Hypothesis TU_fresh : ltac2:(CDefT.buildp (gd_tbl_AW_RefillCfgS ()) "Pmo,$5.P,(2.(3.Vmu,(4.+2.+12.))+>0000000.)P,A3.VK,(6.$7.)(6.$7.)R2.P,(8.$7.(9.(10.(11.(12.&40.)(12.&40.))(:.(;.R3.))(?.(;.R3.)))(<.&40.VUA,)(<.&40.(4.+2.+12.)))$=.)A3.VK,(13.$7.$=.)(6.$7.)(15.+32.VUA,(4.+2.+12.)R4.)")
(* [comment removed for export] *).
  Hypothesis LEDGER_F : ltac2:(CDefT.buildp (gd_tbl_AW_RefillCfgS ()) "Pu,(16.$7.)Pmo,$5.P,(1.(8.(16.$7.)R2.(6.$7.))(8.(16.$7.)R2.(13.$7.$=.)))P,A3.VK,R3.(6.$7.)R2.(0.(8.$7.(9.(:.(;.R3.))(<.&40.VFAA,)(<.&40.(4.+2.+12.)))$=.)(1.(8.$7.(>.(?.(;.R3.))(<.&40.VFAA,)(<.&40.(4.+2.+12.)))$=.)(8.$7.(9.(10.(11.(12.&40.)(12.&40.))(:.(;.R3.))(?.(;.R3.)))(<.&40.VFAA,)(<.&40.(4.+2.+12.)))$=.)))")
(* [comment removed for export] *).
  Hypothesis TF_commit : ltac2:(CDefT.buildp (gd_tbl_AW_RefillCfgS ()) "Pu,(16.$7.)Pmo,$5.P,(1.(8.(16.$7.)R2.(6.$7.))(8.(16.$7.)R2.(13.$7.$=.)))P,A3.VK,R3.(6.$7.)R2.P,(8.$7.(>.(?.(;.R3.))(<.&40.VFAA,)(<.&40.(4.+2.+12.)))$=.)A3.VK,R5.(13.$7.$=.)(14.+32.VFAA,(4.+2.+12.)R4.)")
(* [comment removed for export] *).
  Hypothesis TF_fresh : ltac2:(CDefT.buildp (gd_tbl_AW_RefillCfgS ()) "Pu,(16.$7.)Pmo,$5.P,(1.(8.(16.$7.)R2.(6.$7.))(8.(16.$7.)R2.(13.$7.$=.)))P,A3.VK,R3.(6.$7.)R2.P,(8.$7.(9.(10.(11.(12.&40.)(12.&40.))(:.(;.R3.))(?.(;.R3.)))(<.&40.VFAA,)(<.&40.(4.+2.+12.)))$=.)A3.VK,R5.(13.$7.$=.)(15.+32.VFAA,(4.+2.+12.)R4.)")
(* [comment removed for export] *).
  Hypothesis GMU : 0 <= mu /\ mu mod 4096 = 0 /\ mu <= 0xE0000000.
  Hypothesis GMFA : 0 <= mfa /\ mfa mod 2^18 = 0 /\ mfa + 2^18 <= 2^29.
  (* [comment removed for export] *)
  Hypothesis CSUz : forall f, crange (CSf (Some true) f) UA (2^18).
  Hypothesis CSFz : forall u, crange (CSf u (Some true)) FAA (2^18).
  #[using="CSmono_u CSmono_f"] Lemma CSinc : forall u f y, CSf None None y -> CSf u f y.
  Proof. intros [b|] [b'|] y H; [apply CSmono_u; apply CSmono_f; exact H| apply CSmono_u; exact H| apply CSmono_f; exact H| exact H]. Qed.
    Hypothesis ROOM_U : forall mo, mu + 2^18 <= 0xE0000000 -> K None None mo -> fixrw_grantable 0x32 UA (2^18) mo.
  (* [comment removed for export] *)
  Hypothesis SCAR_U : mu + 2^18 <= 0xE0000000 -> scar_site AL (CSf None None) (K None None) UA (2^18).
  Hypothesis ROOM_F : forall u mo, (u = None \/ u = Some true) -> K u None mo -> fixrw_grantable 0x32 FAA (2^18) mo.
  Hypothesis SCAR_F : forall u, (u = None \/ u = Some true) -> scar_site AL (CSf u None) (K u None) FAA (2^18).
  (* [comment removed for export] *)
  Variables (EP EB ECAP ESZ : Z).
  Hypothesis EWF : emb_wf EP EB ECAP ESZ.
  Hypothesis GEB : emb_geo EB T CTX SB.
  Variable CSx : Z -> Z -> Prop.
  Variable Kx : Z -> Model -> Prop.
  Hypothesis CSOKx : forall a, cs_ok AL (CSx a).
  Hypothesis KxL : forall a, kinv AL (CSx a) (Kx a).
  Hypothesis CSx_inc : forall a y, CSf None None y -> CSx a y.
  Hypothesis B12SITE : b12_siteS (CSf None None) (K None None) Kx EP EB ECAP ESZ.

  Ltac facts :=
    pose proof (cs_ok_sb _ _ (CSOKf None None)) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.


  (* [comment removed for export] *)
  Ltac2 clear_nonarith2 () :=
    let kheads := match Control.case (fun () => Control.hyp @K) with Init.Val kv => let (k, _) := kv in [(k, 3)] | Init.Err _ => [] end in
    let heads := List.append kheads
      [(constr:(@rw_cells), 4); (constr:(@ro_cells), 4); (constr:(@u32arr), 4); (constr:(@munch), 3); (constr:(@wmono), 3);
       (constr:(@stk), 4); (constr:(@mem_inv), 2); (constr:(@crange), 3); (constr:(@poison_statics), 1); (constr:(@thr_statics), 3);
       (constr:(@mwc_statics), 1); (constr:(@pop_statics), 2); (constr:(@gf_frame), 16); (constr:(@kinv), 3); (constr:(@mo_mat), 2)] in
    let rec strip c := match Constr.Unsafe.kind c with Constr.Unsafe.Cast c0 _ _ => strip c0 | _ => c end in
    let test ty :=
      match Constr.Unsafe.kind (strip ty) with
      | Constr.Unsafe.Prod _ _ => Init.true
      | Constr.Unsafe.App f args =>
          let n := Array.length args in
          List.exist (fun p => let (h, k) := p in Bool.and (Int.equal k n) (Constr.equal h f)) heads
      | _ => Init.false
      end in
    let pass () := List.fold_left (fun acc h => let (id, _, ty) := h in
                     if test ty then (match Control.case (fun () => Std.clear [id]) with Init.Val _ => Int.add acc 1 | Init.Err _ => acc end) else acc)
                     0 (List.rev (Control.hyps ())) in
    let rec loop () := if Int.lt 0 (pass ()) then loop () else () in
    loop ().
  Ltac clear_nonarith := ltac2:(Control.enter clear_nonarith2).
  Ltac glia := clear_nonarith; unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, A_INSTANCE in *; cbv zeta in *; prune_disj; clear_mods; lia.
  Ltac sglia := repeat match goal with |- _ /\ _ => split end; glia.



  (* [comment removed for export] *)
  Ltac pc_iso j Hj Hjc :=
    let P := fresh "P" in let HP := fresh "HP" in
    set (P := T + 208 + 80 * j) in *;
    assert (HP : T + 288 <= P /\ P + 80 <= T + 2768 /\ (P + 80 <= T + 208 + 80 * c \/ T + 208 + 80 * c + 80 <= P)) by (subst P; clear - Hj Hjc GC; lia);
    clearbody P; clear Hj Hjc.

  (* [comment removed for export] *)
  Definition rf_cpostS (ok : bool) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word) (F : bvmap 5 word) (fc : bv 32)
      (au nf lo : Z) (exb : bv 8) (cntw csw : word) (fa js0 ds shU shF : list _) (Wx : list (Z * Z)) (X : mem -> Prop) (m0 : mem) : config -> Prop :=
    fun cf => exists ms' mo' (res : Z) (u f : option bool) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (j1' j2' j3' stw' : word),
      let cs := class_size c in let mu' := mu + unit_if u in let mfa' := mfa + unit_if f in let nw := (mu' - au) / cs in
      let PCR := T + 208 + 80 * c in let CH := PCR + 16 in let n := max_count c / 2 in
      cf = mkCfg ms' mo'
      /\ ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None mm (seg_rom asegs)
      /\ munch ((lo, SP) :: (UA, UA + 2^18) :: (0x7fff8000 + UA / 8, 0x7fff8000 + UA / 8 + 32768)
                :: (FA, FAA + 2^18) :: (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768)
                :: (T + 2872, T + 2888) :: (T + 2792, T + 2800) :: (R, R + 8)
                :: (R + 16, R + 24) :: (R + 24, R + 32) :: (R + 32, R + 40) :: (R + 48, R + 56) :: (R + 68, R + 69) :: (R + 72, R + 80) :: Wx) m0 mm
      /\ wmono asegs m0 mm /\ mem_inv asegs mm /\ stk asegs mm lo SP
      /\ K u f mo' /\ J mm mo' /\ (mu' <= 0xE0000000 /\ mu' - au <= 2^19)
      /\ poison_statics mm /\ thr_statics mm CTX T /\ mwc_statics mm /\ pop_statics mm SB /\ ro_cells asegs mm (A_INSTANCE + 48) [C8 (Z_to_bv 64 RI)]
      /\ rw_cells asegs mm R [C8 (Z_to_bv 64 0)]
      /\ rw_cells asegs mm (R + 24) [C8 (Z_to_bv 64 mfa')] /\ rw_cells asegs mm (R + 40) [C8 (Z_to_bv 64 0)]
      /\ rw_cells asegs mm (R + 48) [C8 (Z_to_bv 64 mu')] /\ rw_cells asegs mm (R + 56) [C8 (Z_to_bv 64 0)]
      /\ rw_cells asegs mm (R + 72) [C8 stw']
      /\ rw_cells asegs mm (T + 2872) [C8 j1'; C8 j2'] /\ rw_cells asegs mm (T + 2792) [C8 j3']
      /\ (u = Some true -> rw_cells asegs mm UA [CB (Z.to_nat (2^18)) (repeat (Z_to_bv 8 0) (Z.to_nat (2^18)))]
                        /\ rw_cells asegs mm (0x7fff8000 + UA / 8) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 0xfa) (Z.to_nat 32768))])
      /\ (u <> Some true -> mu + 2^18 <= 0xE0000000 -> rw_cells asegs mm (0x7fff8000 + UA / 8) [CB (Z.to_nat 32768) shU])
      /\ (f = Some true -> rw_cells asegs mm (0x7fff8000 + FAA / 8) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 0xfa) (Z.to_nat 32768))])
      /\ (f <> Some true -> rw_cells asegs mm (0x7fff8000 + FAA / 8) [CB (Z.to_nat 32768) shF])
      /\ X mm
      /\ (if ok then (res = 1 /\ u <> Some false /\ f <> Some false
            /\ rw_cells asegs mm PCR [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 (max_count c)); C8 csw]
            /\ exists (new ws fa' rest : list word) (nf' au' : Z) (ex' : bv 8),
               fa ++ new = fa' ++ ws /\ length ws = Z.to_nat n /\ Z.of_nat (length fa') = nf'
               /\ ( (new = [] /\ u = None /\ f = None /\ n <= nf /\ au' = au /\ ex' = exb)
                  \/ (new = carve_list au cs (Z.to_nat nw) /\ nf < n /\ n - nf <= nw /\ au' = au + nw * cs /\ ex' = Z_to_bv 8 0 /\ 0 < nw
                      /\ (f = Some true -> mfa < 4 * (nf + nw))) )
               /\ rw_cells asegs mm (R + 16) [C8 (Z_to_bv 64 nf')] /\ rw_cells asegs mm (R + 32) [C8 (Z_to_bv 64 au')] /\ rw_cells asegs mm (R + 68) [C1 ex']
               /\ u32arr asegs mm FA fa' /\ u32arr asegs mm (FA + 4 * nf') rest /\ 4 * (nf' + Z.of_nat (length rest)) = mfa'
               /\ u32arr asegs mm CH (cpy (Z.to_nat n) ws ds))
          else (res = 0 /\ f <> Some true
            /\ rw_cells asegs mm PCR [C4 cntw; C4 (Z_to_bv 64 (max_count c)); C8 csw]
            /\ rw_cells asegs mm (R + 16) [C8 (Z_to_bv 64 nf)] /\ rw_cells asegs mm (R + 32) [C8 (Z_to_bv 64 au)] /\ rw_cells asegs mm (R + 68) [C1 exb]   (* [comment removed for export] *)
            /\ u32arr asegs mm FA fa /\ u32arr asegs mm (FA + 4 * nf) js0 /\ u32arr asegs mm CH ds)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "05Z0@L10191162195.7  L10197417939.12 L10197826796.4  L10212982797.13 L10339840027.13 L10654848219.13 L11330413503.7  L11330645183.18 L11330645183.19 L11330660927.11 L11332851263.8  L11334822405.4  L11636954379.13 L11802433892.3  L11802548827.12 L12015581467.13 L12098782647.14 L12098782647.4  L12115764660.13 L12601911123.168L13266555807.7  L13299539613.13 L14002027037.13 L14954004041.147L14958374359.13 L15065879321.148L15122658121.13 L15587431122.13 L16220488471.13 L16239713677.13 L16349891995.13 L16392807694.277L16681706075.13 L16892873619.7  L16938268957.13 L17118940343.13 L18169585919.13 L18186710872.13 L18186710904.14 L18926386861.198L18926758071.263L18926763017.264L18928747180.265L18941063213.199L19190373851.13 L1919947181.146 L19241880844.13 L19633127881.13 L1964695325.13  L1979631515.13  L20025864219.13 L20199931667.7  L20779001463.166L20979301405.13 L21330862034.14 L22025350102.168L22124814583.165L22380288795.13 L22454804381.146L22785913341.144L22872554921.168L23157713330.13 L23168344402.12 L23168721517.3  L23256703893.13 L23473178733.13 L23797353929.13 L2416523916.14  L2416523948.13  L2416881693.7   L24397740297.13 L24885286555.13 L25434267873.168L25583803606.168L25608327385.13 L25659858761.13 L25709194009.13 L25852636277.5  L26013379921.5  L26038281501.13 L26457962392.13 L26460522217.147L26475118923.5  L26602659732.14 L26988824989.13 L27127617376.13 L27617417609.13 L27752029762.13 L27846297964.3  L27985401527.177L28000014519.163L28004109043.146L28275996813.13 L28554005766.14 L2869134573.3   L2869282770.12  L28722154843.13 L28749915688.13 L2882334923.265 L2895800404.14  L29068914677.170L29068915659.169L29068917579.169L29886769227.148L30251443600.15 L30337598945.168L30374108841.168L30934117385.147L31239763064.13 L31239763064.5  L31533430865.5  L31540552454.146L31645532919.163L31656084727.177L31818486286.13 L32075750171.13 L32315971273.13 L32689494322.13 L33016505024.14 L33098394413.144L33217685913.147L33280020567.13 L33321251163.13 L33383325641.13 L33466295069.13 L33497480912.13 L33515502905.7  L33903200363.7  L34127075801.13 L34210848443.13 L34313566237.13 L34329410641.13 L34417722907.13 L34609459819.146L34729060546.13 L34795199150.7  L34941587412.14 L3499268102.148 L35149797815.165L35198162098.13 L35684427048.171L35684430230.170L35684432150.170L35879563402.166L36161680872.13 L36431750486.168L36504433881.14 L36530075933.13 L36767624506.171L36778327625.13 L37252228012.169L37696442802.168L3781552797.13  L38085830811.13 L38235734261.13 L38235734261.14 L38235734261.4  L38235734261.5  L38237949960.3  L38546213588.14 L38742198242.5  L38981556660.13 L39036154839.13 L39038219421.13 L39302557143.13 L39893848093.13 L39906680500.13 L40564802327.13 L40865908571.13 L41011650690.13 L41015213144.7  L41015441097.14 L41015441129.13 L41208242738.13 L41325276974.13 L41544298327.13 L41606129192.13 L41814703546.12 L41815113349.3  L41921880.166   L4202410637.13  L42070587795.7  L42366367054.168L42466912109.13 L42510505847.166L43371077505.14 L43371077537.13 L44514048283.13 L44666701613.144L44933202841.147L45194705697.0  L45221204181.5  L45244317297.13 L45284632083.7  L45646468555.13 L45646468555.14 L45646468555.4  L45646468555.5  L46068717687.166L46079677525.13 L46319545801.13 L46349820701.13 L4644374363.13  L46465297417.13 L46744425461.5  L46808305453.144L46875989211.13 L4702297241.147 L47235497906.13 L47298809302.168L47609407641.147L47690334732.147L47862922960.13 L48097119049.14 L48097119081.13 L48736482147.13 L48736484312.13 L49461236434.13 L49983981972.6  L49984559454.13 L50523288139.23 L50527340753.8  L50624451604.13 L50854936278.168L50979978864.3  L51003398944.14 L51003398944.4  L51072933591.13 L51075522461.13 L5132404781.144 L51465800966.14 L51529931677.13 L51786167833.13 L51884365430.166L51902697689.13 L51931183901.13 L52106535381.13 L52242632905.13 L52417299603.8  L52516341168.13 L52906910299.13 L52949583305.13 L53358130679.177L53358130679.179L53360292855.163L53360292855.165L53741545241.13 L54166772308.14 L54615203157.13 L54705006061.13 L54810485187.6  L5504714008.144 L55411383771.13 L55522234506.166L55588686165.0  L55776599401.147L5595038665.13  L56085964653.13 L56235262043.13 L5654079942.14  L56583794822.13 L5733193033.13  L5759149202.13  L57600663220.13 L57721544658.14 L58150738006.179L58165354070.165L58327472827.168L58365815060.169L58651980829.13 L5872547218.13  L59095036641.168L59109030405.166L59172263284.13 L59310679498.163L59310679924.168L59310680522.166L59310683082.167L59310685002.167L59314873579.169L59321099210.176L59323689553.144L59323689553.145L5953765770.166 L59850771522.13 L59887618725.5  L60220216552.13 L60298975903.13 L60298975935.14 L60299333678.7  L60352520253.144L60438092249.13 L60880885645.13 L60951472185.7  L6115894795.13  L61265671896.5  L61707373910.179L61721987926.165L61766680649.13 L61811395478.165L61816019993.13 L61821816214.179L61987289174.166L62273018057.13 L62412221001.13 L6241432505.7   L62418758342.14 L62580585650.168L62741115888.13 L62800546763.169L63111805597.13 L63152484003.147L63228287635.7  L63379813335.13 L63562516125.13 L63797787481.5  L64143838421.13 L64274725833.13 L64661504413.13 L64943164763.13 L65175065619.7  L65228120857.13 L65428237517.13 L65832345747.7  L65884286807.13 L66509687170.7  L66510045971.14 L66510046003.13 L66632305330.277L6697770711.13  L67019626837.170L67174446998.13 L67174447030.14 L67783461239.166L67867201474.13 L67875248962.13 L6796109341.146 L68137219849.13 L68150369429.13 L6850489741.13  L6937171316.13  L6992194185.13  L7289454877.13  L7327952799.14  L7349075442.13  L7377668436.14  L7464843221.13  L7635215125.12  L7635623978.3   L7989581083.13  L8413342696.3   L8413718743.12  L8854111435.14  L8854111435.4   L8948289623.13  L9218609678.13  L9438734020.2   L9599407968.13  L9735906861.144 L9870379117.13  L9931051511.166 L998301849.147  00000J00U00V00W00X00Y01201j02e03B03]03n03o04004B04C04d04i04j05h06@06A06B07E07F08J08i08j08k08l08m09L09M09g0:F0:g0:h0;;0;N0;m0<L0<k0=J0=i0=j0?a0@@0@_0A>0A?0A@0AZ0BP0BQ0BR0CN0EI0EJ0G50G^0H^0I=0IE0IF0IG0IH0Ig0J60JE0JT0K30K40Kh0Ld0Le0MD0Me0Mm0N@0NA0N`0OQ0OY0OZ0O[0P:0PY0PZ0Pa0Qb0RX0TO0TP0TQ0TR0Tb0Tc0Td0UC0UD0W70Xj0Z]0\L0]40]h0^h0_d0`F0`Q0`d0b[0cQ0dR0dS0dT0e30eR0eY0gL0hH0hI0hJ0hi0iH0iI0iZ0j20j30j40j50jV0jW0lR0lS0lm0ln0n60o[10:11e13I15415c15d16`16a17@18;18Z19S1:D1:c1:d1;F1;h1;l1<71<;1<<1<=1<>1<?1<@1<A1<B1<C1<D1<E1<F1<T1<b1=01=O1=P1=Q1=R1=`1=a1?61?71?Q1@E1@F1A<1AR1Ah1Ai1C\1DX1DY1Da1E@1EZ1F<1F^1Fb1Fm1Gc1Gd1HC1Hb1Hc1IB1IJ1K=1K>1L:1LY1MU1NQ1OM1Ol1P21P81P`1QI1QJ1QX1QY1Rm1SH1SI1TE1TP1TQ1TR1TS1TT1VG1VH1VI1Vj1W`1Wa1Wb1Wc1XB1Xd1Xe1Xf1YE1ZF1[T1\J1]M1]n1]o1^01^Q1^_1`R1`S1aB1aC1b41bS1bT1bU1bV1bW1c61c71c81c91d@1e<1f81gF1gG1gH1h<1hk1hl1iK1ij1jI1jh1kG1kf1lE1ld1mC1n21n31n41n51n=1nE1nM20@20A20B20S20T20\21c22_23>24:24;25B26b27A27`28128228c28j29`29a2:F2:`2:a2:b2:c2:d2;C2;D2;E2;_2<@2<_2=92=:2=B2=J2=R2>12>22?:2?D2?N2@D2@E2@F2B12BP2Bo2C02C12CP2Co2D:2DY2DZ2D[2Dg2Dh2Di2Dj2E62EW2E\2E]2E^2Ee2FD2H72H82Hn2IjS3hAR2RI1c2GC2lo5LOIMG3RI1S2SP2lo3SPLFFFFS3hAR3CTX2SP2lo5LOIMG3CX1S3hAR2SB2RI1c2GC3mfa3js02SP2nf2lo4LJS05LOIMG3HRI3RI13MF1S3hAR2SB2RI1c2GC3mfa2fa2SP2nf2lo4HNF23LFA5LOIMG3HRI3RI13MF1S3hAR2RI1c2GC2SP2lo5LOIMG3RI1S3hAR1T1c2GC2SP2lo5LOIMG2T1S3hAR2SP2lo5LOIMGFFS3hAR1T1c2GC2SP2T0FS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1T1cFS3hAR1T3CTX2SB2RI1c1R2RB2FA4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG3CX1S3hAR2SP2lo5LOIMG1A2k01HFFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T1FS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA3js03SB03MF03MF1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR2RI1c2GC2lo5LOIMG3RI1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T1c2SP2T03MC2S3hAR1T1c2SP2T03MCRS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF03MF14MU0'S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS3hAR2RI1c2GC2lo5LOIMG3RI1S3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1FFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2nf2lo4HNF33LFA3LDS5LOIMG3SB03HRI3RI12T13CX13MF04MU0'FS3hAR1T3CTX2SB2RI1c1R2RB2FA2GT4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2loS3hAR1T3CTX2SB2RI1c1R2RB2FA2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SP3SPHFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2RI1c1RS3hAR1T2lo5LOIMG2T1FS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC4GSEP2mu3mfa2UA3FAAS2RI1c1RFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SP2loS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI13MC22ws3LWSS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'3MC2FFFS3hAR1T1c2SP3TALFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SB03HRI3RI12T13CX13MF04MU0'3HMUS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SB03HRI3RI12T13CX13MF04MU0'3MUHS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SB03HRI3RI12T13CX13MF03MF14MU0'S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS3SB03HRI3RI13CX13MF04MU0'3MUH3MF1S3hAR2RI1c2GC2SP2lo5LOIMG3SPL3RI12d'3DG1S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T1S3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SPS2RI1c1R2SPS3hAR1T2lo5LOIMG2T1S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'3MUHS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI13MC22ws3LWSFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1c3MCRS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR2SP2lo5LOIMGS3hAR1T1c2GC2lo5LOIMG2T1FFFS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'3MUH3MF1FS3hAR2RI1c2GC2lo5LOIMG3RI1FS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2au3HAU3SB04MU0'3MUHS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA4GMFA2fa3js02SP2nf2lo4LJS05LOIMG3SB03HRIS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS3SB03HRI3RI13CX13MF04MU0'3HMUS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds3LDS3SB03HRI3RI13CX13MF03MF14MU0'S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS3SB03HRI3RI13CX13MF04MU0'3MUHS3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMGFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA1A2k01HS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC4GSEP2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2loS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2loS2loS2RI1c1R2loS2loFFFFFFFFFFFS3hAR2lo5LOIMGS3hAR2lo5LOIMGS3hAR2lo5LOIMGS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFS3hAR1T2SP3SPAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA4GMFA2fa3js02nf3LFA4LJS03SB0FS3hAR2RI1c2GC2lo5LOIMG3RI1S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAAFS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR1T2SP2lo5LOIMG2T1S3hAR1T2SP2lo5LOIMG2T1FS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRISS2RI1c1RS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2RI1c2GC2lo5LOIMG3RI1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SPS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SPS2SPS2RI1c1R2SPS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1FS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2RI1c1RS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1c2GCS1c2GCS3hAR2SB2RI1c2GC2mu2lo5LOIMG3HRI3RI13MUHS3hAR2SB2RI1c2GC3mfa2lo5LOIMG3HRI3RI13MF1FS1c3MC22ws3LWSFS3hAR1T2SB2RI1c2GC3mfa2SP2lo5LOIMG3SB03HRI3RI12T02T14SEP13MF13fa'4rest3nf'4LFA'4LNF'S3hAR1T1c2GC2SP2lo5LOIMG2T1FS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS2SB2RI3HRIFFFFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FFS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1FFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3mfa1f3fa'4rest3nf'4LFA'5LREST2UFSFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI13MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T13MC22ws3LWSS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T1S1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1c3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FS3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMGSS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC4GSEP2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG3HRI4MU0'3MUHFFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMGFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMGFFFS2SP3SPHS2SP3SPHS2SP3SPHS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FFS3hAR2SP2lo5LOIMGFS2RI1c1RS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2nf4HNF33LFA3LDS3SB03MF04MU0'S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SP2lo5LOIMGFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC4GSEP2mu3mfa2UA3FAAS1c3MC2S3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMG1A2k01HFS3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2RI1c2GC2lo5LOIMG3RI1FFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS3hAR2RI1c2GC2lo5LOIMG3RI1S1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2RI1c2GC2lo5LOIMG3RI1FS2SP3SPAS2SP3SPAS2SP3SPAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2au3HAU3SB04MU0'3MUHS3hAR1T2T1S3hAR1T2T1S3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1FFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GT4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3TALS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS3hAR1T1c2GCFFFS3hAR1T1c2GCS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1T1cFFS1c3MC1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI". (* [comment removed for export] *)
  #[using="AL IMG ALWF CSOKf CSmono_u CSmono_f ASB GSB GC GT GCTX GSEP CST CSCTX CSRI KL LEDGER_U TU_commit TU_fresh LEDGER_F TF_commit TF_fresh GMU GMFA CSUz CSFz ROOM_U SCAR_U ROOM_F SCAR_F GEB CSx CSOKx KxL CSx_inc B12SITE"] Lemma refill_cfg_noinitS : ltac2:(CDefT.buildp (gd_tbl_AW_RefillCfgS ()) "PQ,P,$17.SpPra,(12.&40.)Pgp,(12.&40.)Ptp,(12.&40.)Pt0,(12.&40.)Pt1,(12.&40.)Pt2,(12.&40.)Ps0,(12.&40.)Ps1,(12.&40.)Pa4,(12.&40.)Pa5,(12.&40.)Pa6,(12.&40.)Pa7,(12.&40.)Ps2,(12.&40.)Ps3,(12.&40.)Ps4,(12.&40.)Ps5,(12.&40.)Ps6,(12.&40.)Ps7,(12.&40.)Ps8,(12.&40.)Ps9,(12.&40.)Ps10,(12.&40.)Ps11,(12.&40.)Pt3,(12.&40.)Pt4,(12.&40.)Pt5,(12.&40.)Pt6,(12.&40.)Pexb,(12.&8.)Pj1,(12.&40.)Pj2,(12.&40.)Pj3,(12.&40.)Pstw,(12.&40.)Pcntw,(12.&40.)Pcsw,(12.&40.)Pfa,(18.(12.&40.))Pjs0,(18.(12.&40.))Pds,(18.(12.&40.))PshU,(18.(12.&8.))PshF,(18.(12.&8.))PSP,$19.PF,(1:.&5.(12.&40.))Pfc,(12.&20.)Pm,P,(12.&40.)(16.(12.&8.))Pmo,$5.Pau,$19.Pnf,$19.Plo,$19.Zcs,$19.(1;.Vc,)ZPCR,$19.(3.(3.VT,+=0.)(1<.+50.Vc,))P,(0.(2.=R5.)(2.R5.Vmu,))P,(2.(1=.Vmu,R6.)(4.+2.+13.))P,(8.$19.(1>.R7.+10.)=)P,(2.=R7.)P,(2.(1<.+4.R8.)Vmfa,)P,(2.(3.(1<.+4.(3.R9.(4.+2.+>.)))(4.+2.+12.))(4.+2.+1=.))P,(8.$19.(1?.(20.(12.&40.)R15.))R:.)P,(8.$19.(1<.+4.(3.R;.(1?.(20.(12.&40.)R15.))))Vmfa,)P,(8.$21.(20.(12.&40.)R15.)#10.)P,(22.A2.VCSf,(6.$7.)(6.$7.)VFA,Vmfa,)P,(23.$24.R11.R;.(25.$26.(27.R1;.)(25.$26.(27.(<.&40.(28.Vc,)))(25.$26.(29.R1:.)(2:.$26.)))))P,(2;.$24.R12.(3.R<.+10.)R18.)P,(23.$24.R13.VR,(25.$26.(29.(<.&40.=))(2:.$26.)))P,(23.$24.R14.(3.VR,+10.)(25.$26.(29.(<.&40.R11.))(2:.$26.)))P,(23.$24.R15.(3.VR,+18.)(25.$26.(29.(<.&40.Vmfa,))(2:.$26.)))P,(23.$24.R16.(3.VR,+20.)(25.$26.(29.(<.&40.R14.))(2:.$26.)))P,(23.$24.R17.(3.VR,+28.)(25.$26.(29.(<.&40.=))(2:.$26.)))P,(23.$24.R18.(3.VR,+30.)(25.$26.(29.(<.&40.Vmu,))(2:.$26.)))P,(23.$24.R19.(3.VR,+38.)(25.$26.(29.(<.&40.=))(2:.$26.)))P,(23.$24.R1:.(3.VR,+44.)(25.$26.(2<.R29.)(2:.$26.)))P,(23.$24.R1;.(3.VR,+48.)(25.$26.(29.R26.)(2:.$26.)))P,(23.$24.R1<.(3.VT,+;38.)(25.$26.(29.R2:.)(25.$26.(29.R29.)(2:.$26.))))P,(23.$24.R1=.(3.VT,+:>8.)(25.$26.(29.R29.)(2:.$26.)))P,(23.$24.R1>.(3.+7???8000.(2=.VUA,+8.))(25.$26.(2>.(2?.+8000.)R23.)(2:.$26.)))P,(23.$24.R1?.(3.+7???8000.(2=.VFAA,+8.))(25.$26.(2>.(2?.+8000.)R23.)(2:.$26.)))P,(2;.$24.R20.VFA,R28.)P,(2;.$24.R21.(3.VFA,(1<.+4.R1>.))R28.)P,(30.R22.)P,(31.R23.VCTX,VT,)P,(32.R24.)P,(33.R25.VSB,)P,(34.$24.R26.(3.$35.+30.)(25.$26.(29.(<.&40.VRI,))(2:.$26.)))P,(36.VEP,VEB,VECAP,VESZ,R27.)P,(37.$24.R28.R24.R2;.)P,(2.(38.VhAR,)R25.)P,(2.R26.(1=.R2=.+660.))P,(2.R2>.(4.+2.+3?.))P,(8.$19.(1>.R2?.+10.)=)P,(22.A2.VCSf,(6.$7.)(6.$7.)R29.(1=.R30.R29.))P,(39.$24.R2>.)P,(8.(12.&40.)R56.(<.&40.$3:.))P,A3.VK,(6.$7.)(6.$7.)R2?.P,(3;.R31.R30.)P,Pok,$7.Pc',$17.P,(3<.R2.R37.R5<.R5;.R57.R56.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R5=.R36.R35.R32.R31.R30.R43.R3>.R3=.R3<.R3;.R3:.R39.R38.(25.(11.$19.$19.)(3=.$19.$19.R2>.(3.R2>.+4.))(25.(11.$19.$19.)(3=.$19.$19.(3.R2>.+10.)(3.(3.R2>.+10.)(1<.+4.(2=.(28.Vc,)+2.))))(2:.(11.$19.$19.))))L,P,(12.&40.)(16.(12.&8.))$3>.R34.R1.)(3?.$24.R5?.R2.)P,Pc',$17.P,(40.VhAR,A2.VCSf,(6.$7.)(6.$7.)A2.VK,(6.$7.)(6.$7.)VKx,VEP,VEB,VECAP,VESZ,R5=.R37.R5<.R5;.R57.R56.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R36.R35.(25.(11.$19.$19.)(3=.$19.$19.R30.R37.)(25.(11.$19.$19.)(3=.$19.$19.VR,(3.VR,+8.))(25.(11.$19.$19.)(3=.$19.$19.(3.VR,+44.)(3.VR,+45.))(2:.(11.$19.$19.)))))Lmm,P,(12.&40.)(16.(12.&8.))(0.(0.(8.$19.(41.&8.R44.)=)(42.+>0000000.(3.Vmu,(4.+2.+12.))))(23.$24.R1.VR,(25.$26.(29.(<.&40.=))(2:.$26.))))VR,R30.R34.R1.)(3?.$24.R5?.R2.)(3?.$24.R5>.(43.(44.(45.R5=.(<.&40.R37.)R5<.R5;.R5:.R59.R58.R57.R56.(<.&40.(3.VT,+=0.))(<.&40.R2>.)(<.&40.$35.)(<.&40.Vc,)R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.)R36.(<.&40.$46.)R35.(6.(12.&40.))R34.(47.$24.))R33.))")
(* [comment removed for export] *).
  Proof.
    intros Q ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 exb j1 j2 j3 stw cntw csw fa js0 ds shU shF SP F fc m mo au nf lo cs PCR
      HAU HINV AUAL HNF HNF2 HNF3 LFA LJS0 LDS CSFA HPC HD MX NF MFA AU M40 MUC M56 EX STC TJ SJ SHU SHF HFAR HJS PS TS MWS PPS RIC B12S
      ST LOIMG SPL SPH SPA SCS MI TP HK0 HJ0 HC HX.
    facts.
    dpose GSB as (SB0 & SBAL & HRI & RI1). dpose GT as (T0 & T1 & TAL). pose proof GCTX as (CX0 & CX1).
    dpose GSEP as (SEP1 & SEP2 & SEP3). dpose GMFA as (MF0 & MFAL & MF1). dpose GMU as (MU0' & MUAL & MUH).
    assert (HR : R = RI + 128 * c) by reflexivity. subst cs PCR.
    pose proof (max_cached_fits c GC) as [MC1 MC2]. pose proof (max_count_range c GC) as MCR.
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (CSf None None) (K None None) _ Q _ mo (KL None None) HK0); [exact HJ0| |].
    { eapply (refill_A AL IMG ALWF (CSf None None) (CSOKf None None)) with (T := T) (c := c) (lo := lo); try exact HPC; try exact ST; try exact (CST None None); try exact SCS; try exact MI;
        clear - T0 T1 TAL GC MCR LOIMG SPL SPH SPA; try lia. }
    cbn beta. intros ms1 mo1 PO HK1 MM1 HJ1. unfold refillA_post in PO.
    ddestruct PO as (m1 & j0 & -> & MU1 & WM1 & MI1 & FR1 & ST1 & _). cbn [ms_mem MS MSsvc] in HJ1.
    (* [comment removed for export] *)
    assert (TR1 : forall A cs0, rw_cells asegs m A cs0 -> A + Z.of_nat (cells_size cs0) <= lo -> rw_cells asegs m1 A cs0).
    { intros A cs0 H H1. eapply rw_cells_transport; [exact H| exact MU1| exact WM1| cbn; split; [left; exact H1| exact I]]. }
    assert (HPC1 : rw_cells asegs m1 (T + 208 + 80 * c) [C4 cntw; C4 (Z_to_bv 64 (max_count c)); C8 csw]) by (apply (TR1 _ _ HPC); cbn; clear - T1 GC LOIMG; lia).
    assert (MX1 : rw_cells asegs m1 R [C8 (Z_to_bv 64 0)]) by (apply (TR1 _ _ MX); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (NF1 : rw_cells asegs m1 (R + 16) [C8 (Z_to_bv 64 nf)]) by (apply (TR1 _ _ NF); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (MFA1 : rw_cells asegs m1 (R + 24) [C8 (Z_to_bv 64 mfa)]) by (apply (TR1 _ _ MFA); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (AU1 : rw_cells asegs m1 (R + 32) [C8 (Z_to_bv 64 au)]) by (apply (TR1 _ _ AU); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (M401 : rw_cells asegs m1 (R + 40) [C8 (Z_to_bv 64 0)]) by (apply (TR1 _ _ M40); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (MUC1 : rw_cells asegs m1 (R + 48) [C8 (Z_to_bv 64 mu)]) by (apply (TR1 _ _ MUC); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (M561 : rw_cells asegs m1 (R + 56) [C8 (Z_to_bv 64 0)]) by (apply (TR1 _ _ M56); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (EX1 : rw_cells asegs m1 (R + 68) [C1 exb]) by (apply (TR1 _ _ EX); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (STC1 : rw_cells asegs m1 (R + 72) [C8 stw]) by (apply (TR1 _ _ STC); cbn; unfold R; clear - RI1 LOIMG GC; lia).
    assert (TJ1 : rw_cells asegs m1 (T + 2872) [C8 j1; C8 j2]) by (apply (TR1 _ _ TJ); cbn; clear - T1 LOIMG; lia).
    assert (SJ1 : rw_cells asegs m1 (T + 2792) [C8 j3]) by (apply (TR1 _ _ SJ); cbn; clear - T1 LOIMG; lia).
    assert (SHU1 : rw_cells asegs m1 (2147450880 + UA / 8) [CB (Z.to_nat 32768) shU]).
    { apply (TR1 _ _ SHU); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia. unfold UA, RB. clear - SB0 RI1 HRI LOIMG GC MU0' MUH. lia. }
    assert (SHF1 : rw_cells asegs m1 (2147450880 + FAA / 8) [CB (Z.to_nat 32768) shF]).
    { apply (TR1 _ _ SHF); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia. unfold FAA, FA, RB. clear - SB0 RI1 HRI LOIMG GC MF0 MF1. lia. }
    assert (HD1 : u32arr asegs m1 (T + 208 + 80 * c + 16) ds).
    { eapply u32arr_transport; [exact HD| exact MU1| exact WM1|]. cbn. rewrite LDS. clear - T1 GC LOIMG; lia. }
    assert (HFAR1 : u32arr asegs m1 FA fa).
    { eapply u32arr_transport; [exact HFAR| exact MU1| exact WM1|]. cbn. unfold FA, RB. clear - LFA SB0 RI1 HRI LOIMG GC HNF HNF2 MF0 MF1; lia. }
    assert (HJS1 : u32arr asegs m1 (FA + 4 * nf) js0).
    { eapply u32arr_transport; [exact HJS| exact MU1| exact WM1|]. cbn. unfold FA, RB. clear - LJS0 SB0 RI1 HRI LOIMG GC MF0 MF1 HNF; lia. }
    assert (PS1 : poison_statics m1) by (eapply poison_statics_transport; [exact PS| exact MU1| intros A k0 H; cbn; clear - H LOIMG; lia]).
    assert (TS1 : thr_statics m1 CTX T) by (eapply thr_statics_transport; [exact TS| exact MU1| | | |]; cbn; unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR; clear - LOIMG CX0 CX1; lia).
    assert (MWS1 : mwc_statics m1) by (eapply mwc_statics_transport; [exact MWS| exact MU1| intros A k0 H; cbn; clear - H LOIMG; lia]).
    assert (PPS1 : pop_statics m1 SB) by (eapply pop_statics_transport; [exact PPS| exact MU1| intros A k0 H; cbn; clear - H LOIMG; lia]).
    assert (B121 : b12_statics EP EB ECAP ESZ m1) by (eapply b12_statics_transport; [exact B12S| exact MU1| exact WM1| intros A k0 H; cbn; clear - H LOIMG; lia]).
    assert (RIC1 : ro_cells asegs m1 (A_INSTANCE + 48) [C8 (Z_to_bv 64 RI)]) by (eapply ro_cells_transport; [exact RIC| exact MU1| unfold A_INSTANCE; cbn; clear - LOIMG; lia]).
    clear TR1 HPC MX NF MFA AU M40 MUC M56 EX STC TJ SJ SHU SHF HD HFAR HJS PS TS MWS PPS RIC ST MI.
    (* [comment removed for export] *)
    eapply (getfrom_cfgS AL IMG ALWF CSf CSOKf CSmono_u CSmono_f ASB T CTX SB RI c GSB GC GT GCTX GSEP CST CSCTX CSRI K KL mu mfa
                LEDGER_U TU_commit TU_fresh LEDGER_F TF_commit TF_fresh GMU GMFA CSUz CSFz ROOM_U SCAR_U ROOM_F SCAR_F EP EB ECAP ESZ GEB CSx Kx CSOKx KxL CSx_inc B12SITE Q)
        with (lo := lo) (au := au) (nf := nf) (exb := exb) (j1 := j1) (j2 := j2) (j3 := j3) (stw := stw) (fa := fa) (js0 := js0) (ds := ds) (shU := shU) (shF := shF).
      all: lazymatch goal with
           | |- rw_cells _ _ (_ + 16) _ => exact NF1
           | |- rw_cells _ _ (_ + 24) _ => exact MFA1
           | |- rw_cells _ _ (_ + 32) _ => exact AU1
           | |- rw_cells _ _ (_ + 40) _ => exact M401
           | |- rw_cells _ _ (T + 2872) _ => exact TJ1
           | |- rw_cells _ _ (T + 2792) _ => exact SJ1
           | |- rw_cells _ _ (_ + 48) [C8 _] => exact MUC1
           | |- rw_cells _ _ (_ + 56) _ => exact M561
           | |- rw_cells _ _ (_ + 68) _ => exact EX1
           | |- rw_cells _ _ (_ + 72) _ => exact STC1
           | |- rw_cells _ _ _ [CB _ _] => first [exact SHU1 | exact SHF1]
           | |- rw_cells _ _ _ _ => exact MX1
           | |- u32arr _ _ _ _ => first [exact HFAR1 | exact HJS1 | exact HD1]
           | |- poison_statics _ => exact PS1
           | |- thr_statics _ _ _ => exact TS1
           | |- mwc_statics _ => exact MWS1
           | |- pop_statics _ _ => exact PPS1
           | |- b12_statics _ _ _ _ _ => exact B121
           | |- ro_cells _ _ _ _ => exact RIC1
           | |- stk _ _ _ _ => exact ST1
           | |- crange _ _ _ => first [ exact CSFA | (eapply crange_sub; [exact SCS| clear - SPL; lia| clear - SPL; lia]) ]
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 A_TP => exact TP
           | |- K _ _ _ => exact HK1
           | |- J _ _ => exact HJ1
           | |- forall ok c', _ => idtac
           | |- _ => idtac end.
      all: lazymatch goal with |- forall ok c', _ => idtac | |- _ => first [ exact HAU | exact HINV | exact AUAL | exact HNF | exact HNF2 | exact HNF3 | exact LFA | exact LJS0 | exact LDS | exact LOIMG | exact MC2
                 | (change (2^18) with 262144; clear - MC1; lia) | (clear - T0 T1 TAL GC SPL SPH SPA; lia) | (match goal with |- ?g => idtac "UNSOLVED" g end; fail) ] end.
    2:{ (* [comment removed for export] *)
        intros cf2 PX2. unfold exh_xpost in PX2.
        ddestruct PX2 as (ms2 & mo2 & xa & P' & d' & cap' & sz' & y5 & y6 & y7 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y28 & y29 & y30 & y31 & m2
                         & -> & -> & MU2 & WM2 & MI2 & ST2 & HK2 & HJ2 & EX2 & EMB2 & STEP2 & FRESH2 & XF2 & MX2).
        replace (ret_pc (Z_to_bv 64 0x4c798)) with (Z_to_bv 64 0x4c798) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
        destruct (emb_buf_apart (CSf None None) EP EB ECAP ESZ P' d' cap' sz' xa T CTX SB RI 4096 STEP2 FRESH2 GEB (CSRI None None) ltac:(clear; lia)
                    ltac:(left; change (2^37) with 137438953472; clear - HRI; lia)) as [DG1 DG2].
        assert (FR2 : refill_frame m2 SP j0 s1 s0 ra).
        { unfold refill_frame in FR1 |- *. eapply rw_cells_munch; [exact FR1| exact MU2|]. unfold emb_fp, A_EMB, kEmbBytes, R. cbn. clear - DG1 DG2 LOIMG RI1 GC SPL HRI SB0. lia. }
        eapply (evtA_aevtS_KJ AL (CSfx (CSf None None) CSx xa) (Kfx (K None None) Kx xa) _ Q _ mo2
                  (KLfx AL (CSf None None) (K None None) CSx Kx (KL None None) KxL xa) HK2); [exact HJ2| |].
        { eapply (refill_B_no AL IMG ALWF (CSfx (CSf None None) CSx xa) (CSOKfx AL (CSf None None) CSx (CSOKf None None) CSOKx xa)) with (m0 := m2) (W := []).
          all: lazymatch goal with
               | |- refill_frame _ _ _ _ _ _ => exact FR2
               | |- stk _ _ _ _ => exact ST2
               | |- mem_inv _ _ => exact MI2
               | |- crange _ _ _ => exact (crange_fx (CSf None None) CSx CSx_inc xa _ _ SCS)
               | |- munch _ _ _ => apply munch_refl
               | |- wmono _ _ _ => apply wmono_refl
               | |- _ => clear - SPL SPH SPA LOIMG; lia end. }
        cbn beta. intros ms3 mo3 PO HK3 MM3 HJ3.
        ddestruct PO as (m3 & -> & MU3 & WM3 & MI3 & ST3).
        apply HX. unfold exh_xpost. eexists. dexists mo3, xa, P', d', cap', sz'. deexists 14. exists m3.
        split; [reflexivity|]. split; [reflexivity|].
        split. { eapply (munch_tail2 [(lo, SP)] [(lo, SP + -32); (R, R + 8); (R + 68, R + 69)] [(lo, SP)] [(lo, SP); (R, R + 8); (R + 68, R + 69)] (emb_fp d') m m1 m2 m3).
                 - exact MU1.
                 - exact MU2.
                 - exact MU3.
                 - clear. solve_sub_fp.
                 - clear. solve_sub_fp.
                 - clear. solve_sub_fp. }
        split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3))|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact HK3|]. split; [exact HJ3|].
        split. { eapply rw_cells_transport; [exact EX2| exact MU3| exact WM3|]. cbn. unfold R. clear - LOIMG RI1 GC HRI SB0. lia. }
        split. { eapply emb_cells_transport; [exact EMB2| exact MU3| exact WM3|]. intros A k0 H. cbn. clear - H LOIMG. lia. }
        split; [exact STEP2|]. split; [exact FRESH2|]. split; [exact XF2| eapply rw_cells_transport; [exact MX2| exact MU3| exact WM3|]; cbn; unfold R; clear - LOIMG RI1 GC HRI SB0; lia]. }
    intros ok cf2 PO2. unfold gf_cpostS in PO2.
    ddestruct PO2 as (ms2 & mo2 & res & u & f & y5 & y6 & y7 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y28 & y29 & y30 & y31 & m2 & j1' & j2' & j3' & stw'
                     & -> & -> & MU2 & WMg2 & MI2 & ST2 & HK2 & HJ2 & MUB2 & REST2).
    replace (ret_pc (Z_to_bv 64 0x4c798)) with (Z_to_bv 64 0x4c798) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    (* [comment removed for export] *)
    assert (TR2 : forall A cs0, rw_cells asegs m1 A cs0 ->
              disjoint_from [(lo, SP + -32); (UA, UA + 2 ^ 18); (2147450880 + UA / 8, 2147450880 + UA / 8 + 32768); (FA, FAA + 2 ^ 18); (2147450880 + FAA / 8, 2147450880 + FAA / 8 + 32768);
                             (T + 2872, T + 2888); (T + 2792, T + 2800); (R, R + 8); (R + 16, R + 24); (R + 24, R + 32); (R + 32, R + 40); (R + 48, R + 56); (R + 68, R + 69); (R + 72, R + 80);
                             (T + 208 + 80 * c + 16, T + 208 + 80 * c + 16 + 4 * (max_count c / 2))] A (Z.of_nat (cells_size cs0)) -> rw_cells asegs m2 A cs0).
    { intros A cs0 H HD0. eapply rw_cells_munch; [exact H| exact MU2| exact HD0]. }
    assert (HPC2 : rw_cells asegs m2 (T + 208 + 80 * c) [C4 cntw; C4 (Z_to_bv 64 (max_count c)); C8 csw]).
    { apply (TR2 _ _ HPC1). cbn. unfold UA, FAA, FA, RB, R. change (2^18) with 262144. sglia. }
    assert (FR2 : refill_frame m2 SP j0 s1 s0 ra).
    { unfold refill_frame in FR1 |- *. apply (TR2 _ _ FR1). cbn. unfold UA, FAA, FA, RB, R. change (2^18) with 262144. sglia. }
    clear TR2.
    ddestruct (REST2) as (PS2 & TS2 & MWS2 & PPS2 & RIC2 & MX2 & MFA2 & M402 & MUC2 & M562 & STC2 & TJ2 & SJ2 & UOK2 & UNO2 & FOK2 & FNO2 & RES2).
    (* [comment removed for export] *)
    assert (FIN : forall (res' : Z) m3 mo' (z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word) hdr,
      K u f mo' -> J m3 mo' ->
      munch [(lo, SP); (T + 208 + 80 * c, T + 208 + 80 * c + 4)] m2 m3 -> wmono asegs m2 m3 -> mem_inv asegs m3 -> stk asegs m3 lo SP ->
      rw_cells asegs m3 (T + 208 + 80 * c) hdr ->
      (if ok then res' = 1 /\ hdr = [C4 (Z_to_bv 64 (max_count c / 2)); C4 (Z_to_bv 64 (max_count c)); C8 csw] else res' = 0 /\ hdr = [C4 cntw; C4 (Z_to_bv 64 (max_count c)); C8 csw]) ->
      rf_cpostS ok SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F fc au nf lo exb cntw csw fa js0 ds shU shF
               [(T + 208 + 80 * c, T + 208 + 80 * c + 4); (T + 208 + 80 * c + 16, T + 208 + 80 * c + 16 + 4 * (max_count c / 2))] (fun _ => True) m
        (mkCfg (MS (mkR ra (Z_to_bv 64 SP) gp tp z5 z6 z7 s0 s1 (Z_to_bv 64 res') z11 z12 z13 z14 z15 z16 z17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z28 z29 z30 z31)
                    F (ret_pc ra) fc None m3 (seg_rom asegs)) mo')).
    { intros res' m3 mo' z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 hdr HK' HJ' MU3 WM3 MI3 ST3 HDR HR'.
      assert (TR3 : forall A cs0, rw_cells asegs m2 A cs0 -> disjoint_from [(lo, SP); (T + 208 + 80 * c, T + 208 + 80 * c + 4)] A (Z.of_nat (cells_size cs0)) -> rw_cells asegs m3 A cs0).
      { intros A cs0 H HD0. eapply rw_cells_transport; [exact H| exact MU3| exact WM3| exact HD0]. }
      unfold rf_cpostS. eexists _, mo', res', u, f. deexists 19. cbv zeta. split; [reflexivity|]. split; [reflexivity|].
        split. { eapply munch_trans. { eapply munch_weaken; [| exact MU1]. clear. solve_sub_fp. }
                 eapply munch_trans. { eapply munch_weaken; [| exact MU2]. clear. solve_sub_fp. }
                 eapply munch_weaken; [| exact MU3]. clear - GC. solve_sub_fp. }
        split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WMg2 WM3))|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact HK'|]. split; [exact HJ'|]. split; [exact MUB2|].
        split. { eapply poison_statics_transport; [exact PS2| exact MU3|]. intros A k0 H; cbn; sglia. }
        split. { eapply thr_statics_transport; [exact TS2| exact MU3| | | |]; cbn; sglia. }
        split. { eapply mwc_statics_transport; [exact MWS2| exact MU3|]. intros A k0 H; cbn; sglia. }
        split. { eapply pop_statics_transport; [exact PPS2| exact MU3|]. intros A k0 H; cbn; sglia. }
        split. { eapply ro_cells_transport; [exact RIC2| exact MU3|]. cbn; sglia. }
        split; [apply (TR3 _ _ MX2); cbn; unfold R; sglia|].
        split; [apply (TR3 _ _ MFA2); cbn; unfold R; sglia|]. split; [apply (TR3 _ _ M402); cbn; unfold R; sglia|].
        split; [apply (TR3 _ _ MUC2); cbn; unfold R; sglia|]. split; [apply (TR3 _ _ M562); cbn; unfold R; sglia|].
        split; [apply (TR3 _ _ STC2); cbn; unfold R; sglia|].
        split; [apply (TR3 _ _ TJ2); cbn; sglia|]. split; [apply (TR3 _ _ SJ2); cbn; sglia|].
        split. { intros Hu'. destruct (UOK2 Hu') as [B1 B2]. split; [apply (TR3 _ _ B1) | apply (TR3 _ _ B2)]; cbn [cells_size csize disjoint_from]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold UA, RB; sglia. }
        split. { intros Hu' HMU. apply (TR3 _ _ (UNO2 Hu' HMU)); cbn [cells_size csize disjoint_from]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold UA, RB; sglia. }
        split. { intros Hf'. apply (TR3 _ _ (FOK2 Hf')); cbn [cells_size csize disjoint_from]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold FAA, FA, RB; sglia. }
        split. { intros Hf'. apply (TR3 _ _ (FNO2 Hf')); cbn [cells_size csize disjoint_from]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold FAA, FA, RB; sglia. }
        split; [exact I|].
        destruct ok; hnf in RES2; hnf in HR'; cycle 1.
        + ddestruct RES2 as (E0 & Hf & NF2 & AU2 & EX2 & HFAR2 & HJS2 & HD2). destruct HR' as (-> & ->). split; [reflexivity|]. split; [exact Hf|]. split; [exact HDR|].
          split; [apply (TR3 _ _ NF2); cbn; unfold R; sglia|]. split; [apply (TR3 _ _ AU2); cbn; unfold R; sglia|]. split; [apply (TR3 _ _ EX2); cbn; unfold R; sglia|].
          split. { eapply u32arr_transport; [exact HFAR2| exact MU3| exact WM3|]. cbn. unfold FA, RB. sglia. }
          split. { eapply u32arr_transport; [exact HJS2| exact MU3| exact WM3|]. cbn. unfold FA, RB. sglia. }
          eapply u32arr_transport; [exact HD2| exact MU3| exact WM3|]. cbn. rewrite LDS. sglia.
        + ddestruct RES2 as (E1 & Hu & Hf & new & ws & fa' & rest & nf' & au' & ex' & HSPLIT & LWS & LFA' & HNEW & NF2 & AU2 & EX2 & HFAR2 & HREST & LREST & HD2). destruct HR' as (-> & ->). split; [reflexivity|]. split; [exact Hu|]. split; [exact Hf|]. split; [exact HDR|].
          dexists new, ws, fa', rest, nf', au', ex'. split; [exact HSPLIT|]. split; [exact LWS|]. split; [exact LFA'|]. split; [exact HNEW|].
          assert (LNF' : 0 <= nf' /\ 4 * (nf' + Z.of_nat (length rest)) <= mfa + 262144).
          { assert (UF : 0 <= unit_if f <= 262144) by (destruct f as [[|]|]; cbn; lia). change (2^18) with 262144 in LREST. clear - LFA' LREST UF. lia. }
          split; [apply (TR3 _ _ NF2); cbn; unfold R; sglia|]. split; [apply (TR3 _ _ AU2); cbn; unfold R; sglia|]. split; [apply (TR3 _ _ EX2); cbn; unfold R; sglia|].
          split. { eapply u32arr_transport; [exact HFAR2| exact MU3| exact WM3|]. cbn. unfold FA, RB. clear - LNF' LFA' T0 T1 SB0 HRI RI1 GC LOIMG SEP1 MF0 MF1; lia. }
          split. { eapply u32arr_transport; [exact HREST| exact MU3| exact WM3|]. cbn. unfold FA, RB. clear - LNF' LFA' T0 T1 SB0 HRI RI1 GC LOIMG SEP1 MF0 MF1; lia. }
          split; [exact LREST|].
          eapply u32arr_transport; [exact HD2| exact MU3| exact WM3|]. cbn. rewrite cpy_length by (rewrite ?LDS; clear - LWS MC2 LDS; lia). rewrite LDS. sglia.
    }
    destruct ok; hnf in RES2; cycle 1.
    - (* [comment removed for export] *)
      destruct RES2 as (-> & RR).
      eapply (evtA_contS_KJ AL true (CSf u f) (K u f) _ Q _ mo2 (KL u f) HK2); [exact HJ2| |].
      { eapply (refill_B_no AL IMG ALWF (CSf u f) (CSOKf u f)) with (m0 := m2) (W := []).
        all: lazymatch goal with
             | |- refill_frame _ _ _ _ _ _ => exact FR2
             | |- stk _ _ _ _ => exact ST2
             | |- mem_inv _ _ => exact MI2
             | |- crange _ _ _ => exact (crange_imp _ _ _ _ (CSinc u f) SCS)
             | |- munch _ _ _ => apply munch_refl
             | |- wmono _ _ _ => apply wmono_refl
             | |- _ => clear - SPL SPH SPA LOIMG; lia end. }
      cbn beta. intros ms3 mo3 PO HK3 MM3 HJ3.
      ddestruct PO as (m3 & -> & MU3 & WM3 & MI3 & ST3). cbn [ms_mem MS MSsvc] in HJ3.
      ddestruct RR as (Hf & HPCx & RR').
      try apply orS_weaken. apply (HC false). apply (FIN 0 m3 mo3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ [C4 cntw; C4 (Z_to_bv 64 (max_count c)); C8 csw] HK3 HJ3).
      + eapply munch_weaken; [| exact MU3]. clear. solve_sub_fp.
      + exact WM3. + exact MI3. + exact ST3.
      + eapply rw_cells_transport; [exact HPC2| exact MU3| exact WM3|]. cbn. clear - T1 GC LOIMG; lia.
      + split; reflexivity.
    - (* [comment removed for export] *)
      destruct RES2 as (-> & RR).
      pose proof HPC2 as HPCs. change [C4 cntw; C4 (Z_to_bv 64 (max_count c)); C8 csw] with ([C4 cntw] ++ [C4 (Z_to_bv 64 (max_count c)); C8 csw]) in HPCs.
      apply rw_cells_app in HPCs as [HC1 HC2]. cbn [cells_size csize Nat.add] in HC2. change (Z.of_nat 4) with 4 in HC2.
      eapply (evtA_contS_KJ AL true (CSf u f) (K u f) _ Q _ mo2 (KL u f) HK2); [exact HJ2| |].
      { eapply (refill_B_ok AL IMG ALWF (CSf u f) (CSOKf u f)) with (m0 := m2) (W := []) (T := T) (c := c) (lo := lo).
        all: lazymatch goal with
             | |- rw_cells _ _ _ [C4 _] => exact HC1
             | |- refill_frame _ _ _ _ _ _ => exact FR2
             | |- stk _ _ _ _ => exact ST2
             | |- mem_inv _ _ => exact MI2
             | |- crange _ _ 4096 => exact (CST u f)
             | |- crange _ _ _ => exact (crange_imp _ _ _ _ (CSinc u f) SCS)
             | |- munch _ _ _ => apply munch_refl
             | |- wmono _ _ _ => apply wmono_refl
             | |- _ => clear - SPL SPH SPA LOIMG T0 T1 GC MC2; lia end. }
      cbn beta. intros ms3 mo3 PO HK3 MM3 HJ3.
      ddestruct PO as (m3 & -> & MU3 & WM3 & MI3 & HC1' & ST3). cbn [ms_mem MS MSsvc] in HJ3.
      try apply orS_weaken. apply (HC true). apply (FIN 1 m3 mo3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ [C4 (Z_to_bv 64 (max_count c / 2)); C4 (Z_to_bv 64 (max_count c)); C8 csw] HK3 HJ3).
      + eapply munch_weaken; [| exact MU3]. clear. solve_sub_fp.
      + exact WM3. + exact MI3. + exact ST3.
      + change [C4 (Z_to_bv 64 (max_count c / 2)); C4 (Z_to_bv 64 (max_count c)); C8 csw] with ([C4 (Z_to_bv 64 (max_count c / 2))] ++ [C4 (Z_to_bv 64 (max_count c)); C8 csw]).
        apply rw_cells_app. split; [exact HC1'|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4.
        eapply rw_cells_transport; [exact HC2| exact MU3| exact WM3|]. cbn. clear - T1 GC LOIMG; lia.
      + split; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "06:0@L10195602566.157L10197417939.12 L10197826796.4  L10210351694.15 L10341395032.15 L10657484440.15 L11137167147.15 L11330660927.11 L11332664038.9  L11332851263.8  L11638509384.15 L11802433892.3  L11802548827.12 L12012970840.15 L12098782647.4  L12114182135.15 L12601911123.175L12657856971.6  L13101100758.155L13266555807.7  L13297943774.15 L13514868359.13 L14004625502.15 L14954004041.153L14961014676.15 L15065879321.154L15121066250.15 L15590033553.15 L16223131988.15 L16238118862.15 L16352532440.15 L16392807694.287L16683300888.15 L16939819870.15 L18166954684.15 L18186710872.13 L18186710904.14 L18799879001.13 L18926386861.208L18926758071.273L18926763017.274L18928747180.275L18941063213.209L19192973208.15 L1919947181.152 L19240294223.15 L19630496650.15 L1966245214.15  L19729564509.9  L1976999384.15  L19919635993.13 L19919635993.6  L20024273496.15 L20779001463.173L2078153834.13  L20977739358.15 L21330862034.14 L22025350102.175L22124814583.171L22377677144.15 L22454804381.152L22785913341.150L22872554921.175L22973222058.10 L23159305201.15 L23168344402.12 L23168721517.3  L23255153110.15 L23474737710.15 L23794718602.15 L2416523916.14  L2416523948.13  L2416881693.7   L24396145482.15 L24887889112.15 L25434267873.175L25583803606.175L25606769306.15 L25658262794.15 L25707639130.15 L25852636277.6  L26040926046.15 L26460522217.153L26460564955.15 L26475118923.6  L26602659732.14 L26986189790.15 L27125009699.15 L27487356397.13 L27615822794.15 L27750433793.15 L27846297964.3  L27985401527.183L28000014519.169L28004109043.152L28274401998.15 L28363221667.176L28554005766.14 L2869134573.3   L2869282770.12  L28719519512.15 L28720477168.157L28748332139.15 L2882334923.275 L28826264790.155L2895800404.14  L29068914001.125L29068914677.177L29068915659.176L29068917579.176L29772069895.13 L29886769227.154L30249546824.21 L30251443600.15 L30337598945.175L30374108841.175L30934117385.153L31093078368.157L31239763064.6  L31241317947.15 L31540552454.152L31645532919.169L31656084727.183L31821121613.15 L32077332824.15 L32127951705.13 L32313363594.15 L32452642285.13 L32687932273.15 L33098394413.150L33217685913.153L33278429716.15 L33322806040.15 L33384908170.15 L33463695710.15 L33499030675.15 L34125480858.15 L34209285368.15 L34310922846.15 L34416139352.15 L34609459819.152L34731668097.15 L34941587412.14 L3499268102.154 L35149797815.171L35195522801.15 L35684427048.178L35684430230.177L35684432150.177L35879563402.173L35923448199.13 L36160090027.15 L36254154137.13 L36431750486.175L36504433881.14 L36531659614.15 L36767624506.178L36775715850.15 L36836618296.178L37252228012.176L37696442802.175L3779965150.15  L38088471256.15 L38235734261.13 L38235734261.14 L38235734261.4  L38235734261.6  L38237949960.3  L38238378678.15 L38546213588.14 L38742198242.6  L39033514388.15 L39039774430.15 L39127155118.15 L39304116116.15 L39895403102.15 L39908263159.15 L40566364500.15 L40867470616.15 L41009052353.15 L41015213144.7  L41015441097.14 L41015441129.13 L41206659185.15 L41212515002.126L41322673517.15 L41541694740.15 L41603529835.15 L41814703546.12 L41815113349.3  L41921880.172   L4199803086.15  L42366367054.175L42464312622.15 L42475409671.13 L42510505847.173L42961284182.157L43371077505.14 L43371077537.13 L43454801945.13 L43454801945.6  L44087897094.157L4448596182.155 L44511404888.15 L44666701613.150L44779457238.155L44933202841.153L45194705697.0  L45221204181.6  L45246915634.15 L45646468555.13 L45646468555.14 L45646468555.4  L45646468555.6  L46068717687.173L46082313750.15 L46181399442.14 L46321137546.15 L46347221342.15 L46466889290.15 L4647017752.15  L46744425461.6  L46808305453.150L46878592664.15 L4702297241.153 L47233902065.15 L47298809302.175L47609407641.153L47690334732.153L47864505491.15 L48097119049.14 L48097119081.13 L49424561926.155L49462823057.15 L49675877529.13 L49983981972.6  L49986110237.15 L50523273552.10 L50523288139.23 L50525401681.22 L50525401681.23 L50525451345.125L50527340753.8  L50527340882.6  L50622860887.15 L50707715512.6  L50854936278.175L50979978864.3  L51003398944.14 L51003398944.4  L5101806806.155 L51070321812.15 L51078153694.15 L5132404781.150 L51465800966.14 L51527287262.15 L51784608858.15 L51884365430.173L51901106842.15 L51933782366.15 L52108131222.15 L52241042058.15 L52417299603.8  L52516341168.13 L52904278040.15 L52951179146.15 L53358130679.183L53358130679.185L53360292855.169L53360292855.171L53738913114.15 L54120698182.14 L54166772308.14 L54617802518.15 L54810485187.6  L5504714008.150 L55414015896.15 L55522234506.173L55588686165.0  L55776599401.153L5592439178.15  L56083332398.15 L56233712152.15 L5654079942.14  L56581188293.15 L57239329095.13 L5730586378.15  L57603261687.15 L5761793745.15  L57721544658.14 L58150738006.185L58165354070.171L58327472827.175L58365815060.176L58649374302.15 L5875150801.15  L58787062638.155L59095036641.175L59109030405.173L59170705207.15 L59308583155.155L59308583155.176L59310679498.169L59310679504.123L59310679924.175L59310680522.173L59310683082.174L59310685002.174L59314873579.176L59321099210.182L59323689553.150L59323689553.151L5953765770.173 L59849184769.15 L59887618725.6  L59968877965.1  L60218658475.15 L60298975903.13 L60298975935.14 L60299333678.7  L60352520253.150L60414336007.155L60436530074.15 L60882472398.15 L6117489736.15  L61265671896.6  L61707373910.185L61721987926.171L61769292298.15 L61811395478.171L61818652250.15 L61821816214.185L61987289174.172L62275617418.15 L62413778954.15 L62418758342.14 L62495665017.157L62580585650.175L62741115888.13 L62800546763.176L63114436830.15 L63152484003.153L63377205652.15 L63564111070.15 L63797787481.6  L64146445974.15 L64277324170.15 L64290542475.13 L64290542475.6  L64659921886.15 L64940562200.15 L65226570074.15 L65430877838.15 L65886893332.15 L66509687170.7  L66510045971.14 L66510046003.13 L66632305330.287L66680329095.13 L6696174740.15  L67019626837.177L67136342570.10 L67174446998.13 L67174447030.14 L67783461239.173L67865613697.15 L67872637185.15 L6796109341.152 L68138773834.15 L68153001686.15 L6853130190.15  L6934531895.15  L6994800842.15  L7286823774.15  L7327952799.14  L7350626225.15  L7377668436.14  L7463251350.15  L7635215125.12  L7635623978.3   L7987990360.15  L8413342696.3   L8413718743.12  L8854111435.4   L8949877268.15  L9215969357.15  L9438734020.2   L9479706218.6   L9596767523.15  L9735906861.150 L9873019438.15  L9895530922.10  L9931051511.173 L998301849.153  00002@02K02L02M02N02O03303P03k04F04G04H04Z04[04`04a05_05`08108I08J08K08L09O09P0:T0;30;40;50;60;70;V0;W0<60<70<J0<]0<^0==0=\0>;0>Z0?90?:0A10AP0Ao0BN0Bk0Bl0CM0CW0CX0DN0DO0DP0DQ0EM0GH0GI0I40I]0J]0K;0KZ0Kb0Kc0Kd0Ke0LD0LS0Lb0M10MP0MQ0NE0OA0OB0Oa0PB0PJ0PK0Q<0Q[0Qc0Qd0Qe0RD0RE0Rd0Re0Rl0Sm0Tc0VZ0V[0Y@0YA0YB0YR0YS0[g0[h0\G0^X0^Y0`P0bC0d60ei0ej0gY0h^0iF0j:0k:0l60na0nl0oN11E12;13<13=13>13?13^13_14>16116m16n16o17N17m17n17o18018118219m19n19o1;71<\1=;1>f1@J1B51Bd1Be1Bf1Bg1Cc1Cd1DC1E>1E]1Gm1Hf1IW1J61J71JY1K;1K?1KJ1KN1L01L11L21L31L41L\1L]1L^1L_1L`1La1Lb1M01M>1ML1Mk1OZ1O[1O\1O]1Ok1Ol1QA1QB1R61R71R81Rn1UI1U_1V51VV1V`1Y01[A1[B1]51_F1`B1`C1`K1`j1aL1an1b21b=1c31c41cX1d71dV1e51e61e>1g11g21gn1hM1iI1jE1kA1k`1kf1kl1n=1n>1n?1nM1nN1o520J21W22c24224M24c24d24e25a25l25m25n28?28@28A2:42:52:62:W2;M2;N2;O2;P2;o2<R2<S2<T2=32>42?B2@82A;2A\2B@2BA2BB2BP2DC2DD2E32E42Ee2FD2FE2FF2FG2FH2FI2Fh2Fi2Fj2Fk2H22Hn2Ij2K82K92K:2M_2NS2OB2OC2Ob2PA2P`2Q?2Q^2R=2R\2S;2SZ2T92TX2U72Uf2Ug2Uh2Uk2Ul2V42V<2VD2X72ZH2ZI2ZJ2ZK2ZS2[Z2\V2]52^12^22_92`Y2a82aW2aX2d32dd2dk2ea2eb2fG2fH2fI2fJ2fK2fj2fk2fl2fm2fn2gO2gn2go2h72h?2hG2hf2hg2hh2j02jN2jX2jb2kX2kY2kZ2mE2md2nC2nD2nE2nd2oC2oN2om2on2oo30;30<30=30>30J30O30P30Q30X30i31H33;33<33Z34P35LS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'2T03CX04SEP14SEP23MF04MU0'3MC23MCR3CSR1u4MUB21P2HPS2SP2lo3SPLFFFFS1T2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAAS3hAR2RI1c2GC2SP2lo5LOIMG3RI1S3hAR1T2SP2lo5LOIMG2T11j2HjS3hAR1T1c2GC2SP2lo5LOIMG2T1FFS3hAR1T1c2GC2SP2T0FS1T1cFS3hAR1T3CTX2SB2RI1c1R2RB2FA4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG3CX1FS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB03HRI2T03CX03MF04MU0'3MC23MCR3CSR1u4MUB21P2HPS3hAR2SP2lo5LOIMG1A2k01HFFFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T1FS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA3js03SB03MF03MF1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T1c2SP2T03MC2S3hAR1T1c2SP2T03MCRFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF03MF14MU0'S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T2SP2lo5LOIMG2T01A2k01HFS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1T2RI1c1RFS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1FFFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2nf2lo4HNF33LFA3LDS5LOIMG3SB03HRI3RI12T13CX13MF04MU0'FS3hAR1T3CTX2SB2RI1c1R2RB2FA2GT4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2loS3hAR1T3CTX2SB2RI1c1R2RB2FA2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T1S3hAR1T3CTX2SP2lo5LOIMG2T03CX0S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SP3SPHFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2RI1c1RFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC4GSEP2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2RI1c1RFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SP2loS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI13MC22ws3LWSS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'3MC2FS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2au2lo3HAU3LDS5LOIMG4SB645ALWF'4IMG'3SB03HRI3RI12T02T13CX03CX13MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFFS3hAR1T1c2SP3TALFS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB02T03CX04SEP14SEP23MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB03HRI2T03CX03MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SB03HRI3RI12T13CX13MF04MU0'3MUH3MF1S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SB03HRI3RI12T13CX13MF04MU0'3HMUS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SB03HRI3RI12T13CX13MF04MU0'3MUHS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SB03HRI3RI12T13CX13MF03MF14MU0'FS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS3SB03HRI3RI13CX13MF04MU0'3MUH3MF1S3hAR1T2SB2RI1c2GC2SP2lo5LOIMG3SB03HRI3RI12T02T14SEP11j2d'3DG13DG32HjS3hAR2RI1c2GC2SP2lo5LOIMG3SPL3RI12d'3DG1S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T1S3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB03HRI3RI12T03CX03CX14SEP14SEP33MF04MU0'3MUH3MC23MCR3CSR1u4MUB21P2HP3MF1S2RI1c1R2SPS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SPS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'3MUHS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI13MC22ws3LWSFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFFFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'3MUH3MF1FFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2au3HAU3SB04MU0'3MUHS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA4GMFA2fa3js02SP2nf2lo4LJS05LOIMG3SB03HRIS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS3SB03HRI3RI13CX13MF04MU0'3HMUS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds3LDS3SB03HRI3RI13CX13MF03MF14MU0'S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS3SB03HRI3RI13CX13MF04MU0'3MUHS3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMGFFFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA1A2k01HS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'2T03CX04SEP14SEP23MF04MU0'3MC23MCR3CSR1u4MUB21P2HPS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC4GSEP2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2loS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2loS2loS2RI1c1R2loS2loS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2loFFFFS1T2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA3MC2FFFFFFS3hAR2lo5LOIMGS3hAR2lo5LOIMGS3hAR2lo5LOIMGS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS3SB03HRI3RI13CX13MF04MU0'3MUH3MF1FFFS3hAR1T2SP3SPAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA4GMFA2fa3js02nf3LFA4LJS03SB0FS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAAFFS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB02T03CX04SEP14SEP33MF03MF14MU0'3MC23MCR3CSR1u4MUB21P2HPS3hAR1T2SP2lo5LOIMG2T1S3hAR1T2SP2lo5LOIMG2T1S1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1T2RI1c1RS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'2T03CX04SEP14SEP23MF04MU0'3MC23MCR3CSR1u4MUB21P2HPS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB03HRI2T03CX03MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB03HRI2T03CX03MF04MU0'3MC23MCR3CSR1u4MUB21P2HPS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRISS2RI1c1RS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SPS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SPS2SPS2RI1c1R2SPS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1FS1T2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2RI1c1RS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1c2GCS1c2GCS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB03HRI2T03CX03MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFFS1c3MC22ws3LWSFS3hAR1T3CTX2SP2lo5LOIMG2T03CX03CX14SEP2S3hAR1T2SB2RI1c2GC3mfa2SP2lo5LOIMG3SB03HRI3RI12T02T14SEP13MF13fa'5rest'3nf'4LFA'4LNF'S3hAR1T2SB2RI1c2GC3mfa3js02SP2nf2lo3HNF4LJS05LOIMG3SB03HRI3RI12T02T14SEP13MF1S3hAR1T2SB2RI1c2GC3mfa2fa2SP2nf2lo4HNF23LFA5LOIMG3SB03HRI3RI12T02T14SEP13MF1S3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG3HRI3RI12T1S3hAR1T1c2GC2SP2lo5LOIMG2T1S3hAR1T2SP2lo5LOIMG2T0FFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS2SB2RI3HRIFFS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB03HRI2T03CX03MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FFS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1FFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3mfa1f3fa'5rest'3nf'4LFA'5LREST2UFSFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI13MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T13MC22ws3LWSS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T1S1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1T2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAAFFS1c3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FS3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMGSS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC4GSEP2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG3HRI4MU0'3MUHFFS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2au2lo3HAU3LDS5LOIMG4SB645ALWF'4IMG'3SB03HRI3RI12T02T13CX03CX13MF04MU0'3MC23MCR3CSR1u4MUB21P2HPS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMGFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMGFFS1TFS2SP3SPHS2SP3SPHS2SP3SPHS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB03HRI2T03CX03MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFFFS2RI1c1RS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2nf4HNF33LFA3LDS3SB03MF04MU0'S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB02T03CX04SEP14SEP33MF04MU0'3MUH3MC23MCR3CSR1u4MUB21P2HPS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC4GSEP2mu3mfa2UA3FAAS1c3MC2S3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMG1A2k01HFS3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFFS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SP3SPAS2SP3SPAS2SP3SPAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2au3HAU3SB04MU0'3MUHS3hAR1T3CTX2SP2lo5LOIMG2T03CX0S3hAR1T2T1S3hAR1T2T1S3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1FFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GT4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3TALS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS3hAR1T1c2GCFFFS3hAR1T1c2GCS1T1cFFS1c3MC1S1T1c2GC1j2Hj3HjcS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FS3hAR1T3CTX2SP2lo5LOIMG2T03CX0S3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI". (* [comment removed for export] *)
  #[using="AL IMG ALWF CSOKf CSmono_u CSmono_f ASB GSB GC GT GCTX GSEP CST CSCTX CSRI KL LEDGER_U TU_commit TU_fresh LEDGER_F TF_commit TF_fresh GMU GMFA CSUz CSFz ROOM_U SCAR_U ROOM_F SCAR_F GEB CSx CSOKx KxL CSx_inc B12SITE"] Lemma refill_cfg_initS : ltac2:(CDefT.buildp (gd_tbl_AW_RefillCfgS ()) "PQ,P,$17.SpPra,(12.&40.)Pgp,(12.&40.)Ptp,(12.&40.)Pt0,(12.&40.)Pt1,(12.&40.)Pt2,(12.&40.)Ps0,(12.&40.)Ps1,(12.&40.)Pa4,(12.&40.)Pa5,(12.&40.)Pa6,(12.&40.)Pa7,(12.&40.)Ps2,(12.&40.)Ps3,(12.&40.)Ps4,(12.&40.)Ps5,(12.&40.)Ps6,(12.&40.)Ps7,(12.&40.)Ps8,(12.&40.)Ps9,(12.&40.)Ps10,(12.&40.)Ps11,(12.&40.)Pt3,(12.&40.)Pt4,(12.&40.)Pt5,(12.&40.)Pt6,(12.&40.)Pexb,(12.&8.)Pj1,(12.&40.)Pj2,(12.&40.)Pj3,(12.&40.)Pstw,(12.&40.)Pcnt,P,$19.(12.&40.)Pmx,P,$19.(12.&40.)Pcsx,P,$19.(12.&40.)Prest,P,$19.(18.$26.)Pfa,(18.(12.&40.))Pjs0,(18.(12.&40.))Pds,(18.(12.&40.))PshU,(18.(12.&8.))PshF,(18.(12.&8.))PSP,$19.PF,(1:.&5.(12.&40.))Pfc,(12.&20.)Pm,P,(12.&40.)(16.(12.&8.))Pmo,$5.Pau,$19.Pnf,$19.Plo,$19.Zcs,$19.(1;.Vc,)ZPCR,$19.(3.(3.VT,+=0.)(1<.+50.Vc,))P,(0.(2.=R5.)(2.R5.Vmu,))P,(2.(1=.Vmu,R6.)(4.+2.+13.))P,(8.$19.(1>.R7.+10.)=)P,(2.=R7.)P,(2.(1<.+4.R8.)Vmfa,)P,(2.(3.(1<.+4.(3.R9.(4.+2.+>.)))(4.+2.+12.))(4.+2.+1=.))P,(8.$19.(1?.(20.(12.&40.)R15.))R:.)P,(8.$19.(1<.+4.(3.R;.(1?.(20.(12.&40.)R15.))))Vmfa,)P,(8.$21.(20.(12.&40.)R15.)#10.)P,(22.A2.VCSf,(6.$7.)(6.$7.)VFA,Vmfa,)P,Pj,$19.(8.$21.(48.A1.R1;.R1.)#40.)P,Pj,$19.P,(0.(2.+1.R1.)(2.R1.+1?.))(49.R14.VT,R20.R1?.R1>.R1=.R2.)P,(8.(12.&40.)A1.R1>.Vc,(<.&40.=))P,(8.(18.$26.)A1.R1=.Vc,(25.$26.(2>.#40.(4:.R1:.))(2:.$26.)))P,(23.$24.R15.VR,(25.$26.(29.(<.&40.=))(2:.$26.)))P,(23.$24.R16.(3.VR,+10.)(25.$26.(29.(<.&40.R13.))(2:.$26.)))P,(23.$24.R17.(3.VR,+18.)(25.$26.(29.(<.&40.Vmfa,))(2:.$26.)))P,(23.$24.R18.(3.VR,+20.)(25.$26.(29.(<.&40.R16.))(2:.$26.)))P,(23.$24.R19.(3.VR,+28.)(25.$26.(29.(<.&40.=))(2:.$26.)))P,(23.$24.R1:.(3.VR,+30.)(25.$26.(29.(<.&40.Vmu,))(2:.$26.)))P,(23.$24.R1;.(3.VR,+38.)(25.$26.(29.(<.&40.=))(2:.$26.)))P,(23.$24.R1<.(3.VR,+44.)(25.$26.(2<.R2=.)(2:.$26.)))P,(23.$24.R1=.(3.VR,+48.)(25.$26.(29.R2:.)(2:.$26.)))P,(23.$24.R1>.(3.VT,+;38.)(25.$26.(29.R2>.)(25.$26.(29.R2=.)(2:.$26.))))P,(23.$24.R1?.(3.VT,+:>8.)(25.$26.(29.R2=.)(2:.$26.)))P,(23.$24.R20.(3.+7???8000.(2=.VUA,+8.))(25.$26.(2>.(2?.+8000.)R25.)(2:.$26.)))P,(23.$24.R21.(3.+7???8000.(2=.VFAA,+8.))(25.$26.(2>.(2?.+8000.)R25.)(2:.$26.)))P,(2;.$24.R22.VFA,R2:.)P,(2;.$24.R23.(3.VFA,(1<.+4.R20.))R2:.)P,(30.R24.)P,(31.R25.VCTX,VT,)P,(32.R26.)P,(33.R27.VSB,)P,(34.$24.R28.(3.$35.+30.)(25.$26.(29.(<.&40.VRI,))(2:.$26.)))P,(36.VEP,VEB,VECAP,VESZ,R29.)P,(37.$24.R2:.R26.R2=.)P,(2.(38.VhAR,)R27.)P,(2.R28.(1=.R2?.+660.))P,(2.R30.(4.+2.+3?.))P,(8.$19.(1>.R31.+10.)=)P,(22.A2.VCSf,(6.$7.)(6.$7.)R2;.(1=.R32.R2;.))P,(39.$24.R30.)P,(8.(12.&40.)R5:.(<.&40.$3:.))P,A3.VK,(6.$7.)(6.$7.)R31.P,(3;.R33.R32.)P,Pok,$7.Pc',$17.P,(3<.R2.R39.R60.R5?.R5;.R5:.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R61.R38.R37.R34.R33.R32.R47.A1.R42.Vc,(<.&40.R31.)R3>.R3=.R3<.R3;.R3:.(25.(11.$19.$19.)(3=.$19.$19.(3.VT,+120.)(3.VT,+:=0.))(2:.(11.$19.$19.)))Lmm,P,(12.&40.)(16.(12.&8.))Pj,$19.P,(0.(2.+1.R1.)(2.R1.+1?.))P,(4;.(8.$19.R2.Vc,))(4<.R4.VT,R46.R43.R3.)R36.R1.)(3?.$24.R63.R2.)P,Pc',$17.P,(40.VhAR,A2.VCSf,(6.$7.)(6.$7.)A2.VK,(6.$7.)(6.$7.)VKx,VEP,VEB,VECAP,VESZ,R61.R39.R60.R5?.R5;.R5:.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R38.R37.(25.(11.$19.$19.)(3=.$19.$19.R32.R39.)(25.(11.$19.$19.)(3=.$19.$19.(3.VT,+120.)(3.VT,+:=0.))(25.(11.$19.$19.)(3=.$19.$19.VR,(3.VR,+8.))(25.(11.$19.$19.)(3=.$19.$19.(3.VR,+44.)(3.VR,+45.))(2:.(11.$19.$19.))))))Lmm,P,(12.&40.)(16.(12.&8.))(0.(0.(0.(8.$19.(41.&8.R48.)=)(42.+>0000000.(3.Vmu,(4.+2.+12.))))(23.$24.R1.VR,(25.$26.(29.(<.&40.=))(2:.$26.))))Pj,$19.P,(0.(2.+1.R1.)(2.R1.+1?.))(4<.R3.VT,R45.R42.R2.))VR,R32.R36.R1.)(3?.$24.R63.R2.)(3?.$24.R62.(43.(44.(45.R61.(<.&40.R39.)R60.R5?.R5>.R5=.R5<.R5;.R5:.(<.&40.(3.VT,+=0.))(<.&40.R30.)(<.&40.$35.)(<.&40.Vc,)R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.)R38.(<.&40.$46.)R37.(6.(12.&40.))R36.(47.$24.))R35.))")
(* [comment removed for export] *).
  Proof.
    intros Q ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 exb j1 j2 j3 stw cnt mx csx rest fa js0 ds shU shF SP F fc m mo au nf lo cs PCR
      HAU HINV AUAL HNF HNF2 HNF3 LFA LJS0 LDS CSFA REST PCS MX0 RESTC MX NF MFA AU M40 MUC M56 EX STC TJ SJ SHU SHF HFAR HJS PS TS MWS PPS RIC B12S
      ST LOIMG SPL SPH SPA SCS MI TP HK0 HJ0 HC HX.
    facts.
    dpose GSB as (SB0 & SBAL & HRI & RI1). dpose GT as (T0 & T1 & TAL). pose proof GCTX as (CX0 & CX1).
    dpose GSEP as (SEP1 & SEP2 & SEP3). dpose GMFA as (MF0 & MFAL & MF1). dpose GMU as (MU0' & MUAL & MUH).
    assert (HR : R = RI + 128 * c) by reflexivity. subst cs PCR.
    pose proof (max_cached_fits c GC) as [MC1 MC2]. pose proof (max_count_range c GC) as MCR. pose proof (class_size_range c GC) as CSR.
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (CSf None None) (K None None) _ Q _ mo (KL None None) HK0); [exact HJ0| |].
    { eapply (refill_A_init AL IMG ALWF (CSf None None) (CSOKf None None)) with (T := T) (c := c) (lo := lo); try exact REST; try exact PCS; try exact MX0; try exact ST; try exact (CST None None); try exact SCS; try exact MI;
        clear - T0 T1 TAL GC MCR LOIMG SPL SPH SPA; try lia. }
    cbn beta. intros ms1 mo1 PO HK1 MM1 HJ1. unfold refillA_post in PO.
    ddestruct PO as (x28 & x29 & x30 & m1 & j0 & -> & MU1 & WM1 & MI1 & FR1 & ST1 & PCN). cbn [ms_mem MS MSsvc] in HJ1.
    (* [comment removed for export] *)
    assert (TR1 : forall A cs0, rw_cells asegs m A cs0 -> disjoint_from [(lo, SP); (T + 288, T + 2768)] A (Z.of_nat (cells_size cs0)) -> rw_cells asegs m1 A cs0).
    { intros A cs0 H H1. eapply rw_cells_transport; [exact H| exact MU1| exact WM1| exact H1]. }
    pose proof (PCN c GC) as HPC1. unfold pc_new in HPC1. rewrite RESTC in HPC1. apply rw_cells_app in HPC1 as [HPC1 HD1]. cbn [cells_size csize Nat.add] in HD1.
    change (Z.of_nat 16) with 16 in HD1. apply u32arr_of_CB in HD1.
    assert (MX1 : rw_cells asegs m1 R [C8 (Z_to_bv 64 0)]) by (apply (TR1 _ _ MX); cbn; unfold R; glia).
    assert (NF1 : rw_cells asegs m1 (R + 16) [C8 (Z_to_bv 64 nf)]) by (apply (TR1 _ _ NF); cbn; unfold R; glia).
    assert (MFA1 : rw_cells asegs m1 (R + 24) [C8 (Z_to_bv 64 mfa)]) by (apply (TR1 _ _ MFA); cbn; unfold R; glia).
    assert (AU1 : rw_cells asegs m1 (R + 32) [C8 (Z_to_bv 64 au)]) by (apply (TR1 _ _ AU); cbn; unfold R; glia).
    assert (M401 : rw_cells asegs m1 (R + 40) [C8 (Z_to_bv 64 0)]) by (apply (TR1 _ _ M40); cbn; unfold R; glia).
    assert (MUC1 : rw_cells asegs m1 (R + 48) [C8 (Z_to_bv 64 mu)]) by (apply (TR1 _ _ MUC); cbn; unfold R; glia).
    assert (M561 : rw_cells asegs m1 (R + 56) [C8 (Z_to_bv 64 0)]) by (apply (TR1 _ _ M56); cbn; unfold R; glia).
    assert (EX1 : rw_cells asegs m1 (R + 68) [C1 exb]) by (apply (TR1 _ _ EX); cbn; unfold R; glia).
    assert (STC1 : rw_cells asegs m1 (R + 72) [C8 stw]) by (apply (TR1 _ _ STC); cbn; unfold R; glia).
    assert (TJ1 : rw_cells asegs m1 (T + 2872) [C8 j1; C8 j2]) by (apply (TR1 _ _ TJ); cbn; glia).
    assert (SJ1 : rw_cells asegs m1 (T + 2792) [C8 j3]) by (apply (TR1 _ _ SJ); cbn; glia).
    assert (SHU1 : rw_cells asegs m1 (2147450880 + UA / 8) [CB (Z.to_nat 32768) shU]).
    { apply (TR1 _ _ SHU); cbn [cells_size csize disjoint_from]; rewrite Nat.add_0_r, Z2Nat.id by lia. unfold UA, RB. sglia. }
    assert (SHF1 : rw_cells asegs m1 (2147450880 + FAA / 8) [CB (Z.to_nat 32768) shF]).
    { apply (TR1 _ _ SHF); cbn [cells_size csize disjoint_from]; rewrite Nat.add_0_r, Z2Nat.id by lia. unfold FAA, FA, RB. sglia. }
    assert (HFAR1 : u32arr asegs m1 FA fa).
    { eapply u32arr_transport; [exact HFAR| exact MU1| exact WM1|]. cbn. unfold FA, RB. clear - LFA SB0 RI1 HRI LOIMG GC HNF HNF2 MF0 MF1 T0 T1 SEP1; lia. }
    assert (HJS1 : u32arr asegs m1 (FA + 4 * nf) js0).
    { eapply u32arr_transport; [exact HJS| exact MU1| exact WM1|]. cbn. unfold FA, RB. clear - LJS0 SB0 RI1 HRI LOIMG GC MF0 MF1 HNF T0 T1 SEP1; lia. }
    assert (PS1 : poison_statics m1) by (eapply poison_statics_transport; [exact PS| exact MU1| intros A k0 H; cbn; clear - H LOIMG T0; lia]).
    assert (TS1 : thr_statics m1 CTX T) by (eapply thr_statics_transport; [exact TS| exact MU1| | | |]; cbn; unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR; clear - LOIMG CX0 CX1 T0 SEP2; lia).
    assert (MWS1 : mwc_statics m1) by (eapply mwc_statics_transport; [exact MWS| exact MU1| intros A k0 H; cbn; clear - H LOIMG T0; lia]).
    assert (PPS1 : pop_statics m1 SB) by (eapply pop_statics_transport; [exact PPS| exact MU1| intros A k0 H; cbn; clear - H LOIMG T0; lia]).
    assert (B121 : b12_statics EP EB ECAP ESZ m1) by (eapply b12_statics_transport; [exact B12S| exact MU1| exact WM1| intros A k0 H; cbn; clear - H LOIMG T0; lia]).
    assert (RIC1 : ro_cells asegs m1 (A_INSTANCE + 48) [C8 (Z_to_bv 64 RI)]) by (eapply ro_cells_transport; [exact RIC| exact MU1| unfold A_INSTANCE; cbn; clear - LOIMG T0; lia]).
    clear TR1 MX NF MFA AU M40 MUC M56 EX STC TJ SJ SHU SHF HFAR HJS PS TS MWS PPS RIC ST MI PCS.
    (* [comment removed for export] *)
    eapply (getfrom_cfgS AL IMG ALWF CSf CSOKf CSmono_u CSmono_f ASB T CTX SB RI c GSB GC GT GCTX GSEP CST CSCTX CSRI K KL mu mfa
                LEDGER_U TU_commit TU_fresh LEDGER_F TF_commit TF_fresh GMU GMFA CSUz CSFz ROOM_U SCAR_U ROOM_F SCAR_F EP EB ECAP ESZ GEB CSx Kx CSOKx KxL CSx_inc B12SITE Q)
        with (lo := lo) (au := au) (nf := nf) (exb := exb) (j1 := j1) (j2 := j2) (j3 := j3) (stw := stw) (fa := fa) (js0 := js0) (ds := ds) (shU := shU) (shF := shF).
      all: lazymatch goal with
           | |- rw_cells _ _ (_ + 16) _ => exact NF1
           | |- rw_cells _ _ (_ + 24) _ => exact MFA1
           | |- rw_cells _ _ (_ + 32) _ => exact AU1
           | |- rw_cells _ _ (_ + 40) _ => exact M401
           | |- rw_cells _ _ (T + 2872) _ => exact TJ1
           | |- rw_cells _ _ (T + 2792) _ => exact SJ1
           | |- rw_cells _ _ (_ + 48) [C8 _] => exact MUC1
           | |- rw_cells _ _ (_ + 56) _ => exact M561
           | |- rw_cells _ _ (_ + 68) _ => exact EX1
           | |- rw_cells _ _ (_ + 72) _ => exact STC1
           | |- rw_cells _ _ _ [CB _ _] => first [exact SHU1 | exact SHF1]
           | |- rw_cells _ _ _ _ => exact MX1
           | |- u32arr _ _ _ _ => first [exact HFAR1 | exact HJS1 | exact HD1]
           | |- poison_statics _ => exact PS1
           | |- thr_statics _ _ _ => exact TS1
           | |- mwc_statics _ => exact MWS1
           | |- pop_statics _ _ => exact PPS1
           | |- b12_statics _ _ _ _ _ => exact B121
           | |- ro_cells _ _ _ _ => exact RIC1
           | |- stk _ _ _ _ => exact ST1
           | |- crange _ _ _ => first [ exact CSFA | (eapply crange_sub; [exact SCS| clear - SPL; lia| clear - SPL; lia]) ]
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 A_TP => exact TP
           | |- K _ _ _ => exact HK1
           | |- J _ _ => exact HJ1
           | |- forall ok c', _ => idtac
           | |- _ => idtac end.
      all: lazymatch goal with |- forall ok c', _ => idtac | |- _ => first [ sassumption | cassumption | exact HAU | exact HINV | exact AUAL | exact HNF | exact HNF2 | exact HNF3 | exact LFA | exact LJS0 | exact LDS | exact LOIMG | exact MC2
                 | (change (2^18) with 262144; clear - MC1; lia) | (clear - T0 T1 TAL GC SPL SPH SPA; lia) ] end.
    2:{ (* [comment removed for export] *)
        intros cf2 PX2. unfold exh_xpost in PX2.
        ddestruct PX2 as (ms2 & mo2 & xa & P' & d' & cap' & sz' & y5 & y6 & y7 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y28 & y29 & y30 & y31 & m2
                         & -> & -> & MU2 & WM2 & MI2 & ST2 & HK2 & HJ2 & EX2 & EMB2 & STEP2 & FRESH2 & XF2 & MX2).
        replace (ret_pc (Z_to_bv 64 0x4c798)) with (Z_to_bv 64 0x4c798) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
        destruct (emb_buf_apart (CSf None None) EP EB ECAP ESZ P' d' cap' sz' xa T CTX SB RI 4096 STEP2 FRESH2 GEB (CSRI None None) ltac:(clear; lia)
                    ltac:(left; change (2^37) with 137438953472; clear - HRI; lia)) as [DG1 DG2].
        assert (FR2 : refill_frame m2 SP j0 s1 s0 ra).
        { unfold refill_frame in FR1 |- *. eapply rw_cells_munch; [exact FR1| exact MU2|]. unfold emb_fp, A_EMB, kEmbBytes, R. cbn. clear - DG1 DG2 LOIMG RI1 GC SPL HRI SB0. lia. }
        eapply (evtA_aevtS_KJ AL (CSfx (CSf None None) CSx xa) (Kfx (K None None) Kx xa) _ Q _ mo2
                  (KLfx AL (CSf None None) (K None None) CSx Kx (KL None None) KxL xa) HK2); [exact HJ2| |].
        { eapply (refill_B_no AL IMG ALWF (CSfx (CSf None None) CSx xa) (CSOKfx AL (CSf None None) CSx (CSOKf None None) CSOKx xa)) with (m0 := m2) (W := []).
          all: lazymatch goal with
               | |- refill_frame _ _ _ _ _ _ => exact FR2
               | |- stk _ _ _ _ => exact ST2
               | |- mem_inv _ _ => exact MI2
               | |- crange _ _ _ => exact (crange_fx (CSf None None) CSx CSx_inc xa _ _ SCS)
               | |- munch _ _ _ => apply munch_refl
               | |- wmono _ _ _ => apply wmono_refl
               | |- _ => clear - SPL SPH SPA LOIMG; lia end. }
        cbn beta. intros ms3 mo3 PO HK3 MM3 HJ3.
        ddestruct PO as (m3 & -> & MU3 & WM3 & MI3 & ST3).
        apply HX. unfold exh_xpost. eexists. dexists mo3, xa, P', d', cap', sz'. deexists 14. exists m3.
        split; [reflexivity|]. split; [reflexivity|].
        split. { eapply (munch_tail2 [(lo, SP); (T + 288, T + 2768)] [(lo, SP + -32); (R, R + 8); (R + 68, R + 69)] [(lo, SP)] [(lo, SP); (T + 288, T + 2768); (R, R + 8); (R + 68, R + 69)] (emb_fp d') m m1 m2 m3).
                 - exact MU1.
                 - exact MU2.
                 - exact MU3.
                 - clear. solve_sub_fp.
                 - clear. solve_sub_fp.
                 - clear. solve_sub_fp. }
        split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3))|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact HK3|]. split; [exact HJ3|].
        split. { eapply rw_cells_transport; [exact EX2| exact MU3| exact WM3|]. cbn. unfold R. clear - LOIMG RI1 GC HRI SB0. lia. }
        split. { eapply emb_cells_transport; [exact EMB2| exact MU3| exact WM3|]. intros A k0 H. cbn. clear - H LOIMG. lia. }
        split; [exact STEP2|]. split; [exact FRESH2|]. split; [split; [exact XF2| eapply rw_cells_transport; [exact MX2| exact MU3| exact WM3|]; cbn; unfold R; clear - LOIMG RI1 GC HRI SB0; lia]|].
        (* [comment removed for export] *)
        destruct (emb_buf_apart (CSf None None) EP EB ECAP ESZ P' d' cap' sz' xa T CTX SB T 4096 STEP2 FRESH2 GEB (CST None None) ltac:(clear; lia)
                    ltac:(right; left; clear; lia)) as [_ DG3].
        intros j Hj. specialize (PCN j Hj). unfold pc_new in PCN |- *.
        eapply rw_cells_transport; [eapply rw_cells_munch; [exact PCN| exact MU2|]| exact MU3| exact WM3|].
        - unfold emb_fp, A_EMB, kEmbBytes, R. rewrite cells_size_app. cbn [cells_size csize Nat.add]. rewrite (REST j). cbn. clear - DG1 DG3 Hj LOIMG RI1 GC SPL HRI SB0 T0 T1 SEP1. lia.
        - rewrite cells_size_app. cbn [cells_size csize Nat.add]. rewrite (REST j). cbn. clear - Hj LOIMG T0 T1. lia. }
    intros ok cf2 PO2. unfold gf_cpostS in PO2.
    ddestruct PO2 as (ms2 & mo2 & res & u & f & y5 & y6 & y7 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y28 & y29 & y30 & y31 & m2 & j1' & j2' & j3' & stw'
                     & -> & -> & MU2 & WMg2 & MI2 & ST2 & HK2 & HJ2 & MUB2 & REST2).
    replace (ret_pc (Z_to_bv 64 0x4c798)) with (Z_to_bv 64 0x4c798) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    (* [comment removed for export] *)
    assert (TR2 : forall A cs0, rw_cells asegs m1 A cs0 ->
              disjoint_from [(lo, SP + -32); (UA, UA + 2 ^ 18); (2147450880 + UA / 8, 2147450880 + UA / 8 + 32768); (FA, FAA + 2 ^ 18); (2147450880 + FAA / 8, 2147450880 + FAA / 8 + 32768);
                             (T + 2872, T + 2888); (T + 2792, T + 2800); (R, R + 8); (R + 16, R + 24); (R + 24, R + 32); (R + 32, R + 40); (R + 48, R + 56); (R + 68, R + 69); (R + 72, R + 80);
                             (T + 208 + 80 * c + 16, T + 208 + 80 * c + 16 + 4 * (max_count c / 2))] A (Z.of_nat (cells_size cs0)) -> rw_cells asegs m2 A cs0).
    { intros A cs0 H HD0. eapply rw_cells_munch; [exact H| exact MU2| exact HD0]. }
    assert (HPC2 : rw_cells asegs m2 (T + 208 + 80 * c) [C4 (cnt c); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))]).
    { apply (TR2 _ _ HPC1). cbn. unfold UA, FAA, FA, RB, R. change (2^18) with 262144. sglia. }
    assert (FR2 : refill_frame m2 SP j0 s1 s0 ra).
    { unfold refill_frame in FR1 |- *. apply (TR2 _ _ FR1). cbn. unfold UA, FAA, FA, RB, R. change (2^18) with 262144. sglia. }
    assert (PCN2 : forall j, 1 <= j <= 31 -> j <> c -> pc_new m2 T cnt rest j).
    { intros j Hj Hjc. unfold pc_new. apply (TR2 _ _ (PCN j Hj)). rewrite cells_size_app, REST. cbn [cells_size csize Nat.add]. change (Z.of_nat 80) with 80.
      cbn [disjoint_from]. pc_iso j Hj Hjc. unfold UA, FAA, FA, RB, R. change (2^18) with 262144. sglia. }
    clear TR2 PCN.
    ddestruct (REST2) as (PS2 & TS2 & MWS2 & PPS2 & RIC2 & MX2 & MFA2 & M402 & MUC2 & M562 & STC2 & TJ2 & SJ2 & UOK2 & UNO2 & FOK2 & FNO2 & RES2).
    (* [comment removed for export] *)
    assert (FIN : forall (res' : Z) m3 mo' (z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word) hdr,
      K u f mo' -> J m3 mo' ->
      munch [(lo, SP); (T + 208 + 80 * c, T + 208 + 80 * c + 4)] m2 m3 -> wmono asegs m2 m3 -> mem_inv asegs m3 -> stk asegs m3 lo SP ->
      rw_cells asegs m3 (T + 208 + 80 * c) hdr ->
      (if ok then res' = 1 /\ hdr = [C4 (Z_to_bv 64 (max_count c / 2)); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))] else res' = 0 /\ hdr = [C4 (cnt c); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))]) ->
      rf_cpostS ok SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F fc au nf lo exb (cnt c) (Z_to_bv 64 (class_size c)) fa js0 ds shU shF
               [(T + 288, T + 2768)] (fun mm => forall j, 1 <= j <= 31 -> j <> c -> pc_new mm T cnt rest j) m
        (mkCfg (MS (mkR ra (Z_to_bv 64 SP) gp tp z5 z6 z7 s0 s1 (Z_to_bv 64 res') z11 z12 z13 z14 z15 z16 z17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z28 z29 z30 z31)
                    F (ret_pc ra) fc None m3 (seg_rom asegs)) mo')).
    { intros res' m3 mo' z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 hdr HK' HJ' MU3 WM3 MI3 ST3 HDR HR'.
      assert (TR3 : forall A cs0, rw_cells asegs m2 A cs0 -> disjoint_from [(lo, SP); (T + 208 + 80 * c, T + 208 + 80 * c + 4)] A (Z.of_nat (cells_size cs0)) -> rw_cells asegs m3 A cs0).
      { intros A cs0 H HD0. eapply rw_cells_transport; [exact H| exact MU3| exact WM3| exact HD0]. }
      unfold rf_cpostS. eexists _, mo', res', u, f. deexists 19. cbv zeta. split; [reflexivity|]. split; [reflexivity|].
        split. { eapply munch_trans. { eapply munch_weaken; [| exact MU1]. clear. solve_sub_fp. }
                 eapply munch_trans. { eapply munch_weaken; [| exact MU2]. clear - GC MC2. solve_sub_fp. }
                 eapply munch_weaken; [| exact MU3]. clear - GC. solve_sub_fp. }
        split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WMg2 WM3))|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact HK'|]. split; [exact HJ'|]. split; [exact MUB2|].
        split. { eapply poison_statics_transport; [exact PS2| exact MU3|]. intros A k0 H; cbn; sglia. }
        split. { eapply thr_statics_transport; [exact TS2| exact MU3| | | |]; cbn; sglia. }
        split. { eapply mwc_statics_transport; [exact MWS2| exact MU3|]. intros A k0 H; cbn; sglia. }
        split. { eapply pop_statics_transport; [exact PPS2| exact MU3|]. intros A k0 H; cbn; sglia. }
        split. { eapply ro_cells_transport; [exact RIC2| exact MU3|]. cbn; sglia. }
        split; [apply (TR3 _ _ MX2); cbn; unfold R; sglia|].
        split; [apply (TR3 _ _ MFA2); cbn; unfold R; sglia|]. split; [apply (TR3 _ _ M402); cbn; unfold R; sglia|].
        split; [apply (TR3 _ _ MUC2); cbn; unfold R; sglia|]. split; [apply (TR3 _ _ M562); cbn; unfold R; sglia|].
        split; [apply (TR3 _ _ STC2); cbn; unfold R; sglia|].
        split; [apply (TR3 _ _ TJ2); cbn; sglia|]. split; [apply (TR3 _ _ SJ2); cbn; sglia|].
        split. { intros Hu'. destruct (UOK2 Hu') as [B1 B2]. split; [apply (TR3 _ _ B1) | apply (TR3 _ _ B2)]; cbn [cells_size csize disjoint_from]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold UA, RB; sglia. }
        split. { intros Hu' HMU. apply (TR3 _ _ (UNO2 Hu' HMU)); cbn [cells_size csize disjoint_from]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold UA, RB; sglia. }
        split. { intros Hf'. apply (TR3 _ _ (FOK2 Hf')); cbn [cells_size csize disjoint_from]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold FAA, FA, RB; sglia. }
        split. { intros Hf'. apply (TR3 _ _ (FNO2 Hf')); cbn [cells_size csize disjoint_from]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold FAA, FA, RB; sglia. }
        split. { intros j Hj Hjc. unfold pc_new. apply (TR3 _ _ (PCN2 j Hj Hjc)). rewrite cells_size_app, REST. cbn [cells_size csize Nat.add]. change (Z.of_nat 80) with 80.
                 cbn [disjoint_from]. pc_iso j Hj Hjc. sglia. }
        destruct ok; hnf in RES2; hnf in HR'; cycle 1.
        + ddestruct RES2 as (E0 & Hf & NF2 & AU2 & EX2 & HFAR2 & HJS2 & HD2). destruct HR' as (-> & ->). split; [reflexivity|]. split; [exact Hf|]. split; [exact HDR|].
          split; [apply (TR3 _ _ NF2); cbn; unfold R; sglia|]. split; [apply (TR3 _ _ AU2); cbn; unfold R; sglia|]. split; [apply (TR3 _ _ EX2); cbn; unfold R; sglia|].
          split. { eapply u32arr_transport; [exact HFAR2| exact MU3| exact WM3|]. cbn. unfold FA, RB. sglia. }
          split. { eapply u32arr_transport; [exact HJS2| exact MU3| exact WM3|]. cbn. unfold FA, RB. sglia. }
          eapply u32arr_transport; [exact HD2| exact MU3| exact WM3|]. cbn. rewrite LDS. sglia.
        + ddestruct RES2 as (E1 & Hu & Hf & new & ws & fa' & rest' & nf' & au' & ex' & HSPLIT & LWS & LFA' & HNEW & NF2 & AU2 & EX2 & HFAR2 & HREST & LREST & HD2). destruct HR' as (-> & ->). split; [reflexivity|]. split; [exact Hu|]. split; [exact Hf|]. split; [exact HDR|].
          dexists new, ws, fa', rest', nf', au', ex'. split; [exact HSPLIT|]. split; [exact LWS|]. split; [exact LFA'|]. split; [exact HNEW|].
          assert (LNF' : 0 <= nf' /\ 4 * (nf' + Z.of_nat (length rest')) <= mfa + 262144).
          { assert (UF : 0 <= unit_if f <= 262144) by (destruct f as [[|]|]; cbn; lia). change (2^18) with 262144 in LREST. clear - LFA' LREST UF. lia. }
          split; [apply (TR3 _ _ NF2); cbn; unfold R; sglia|]. split; [apply (TR3 _ _ AU2); cbn; unfold R; sglia|]. split; [apply (TR3 _ _ EX2); cbn; unfold R; sglia|].
          split. { eapply u32arr_transport; [exact HFAR2| exact MU3| exact WM3|]. cbn. unfold FA, RB. clear - LNF' LFA' T0 T1 SB0 HRI RI1 GC LOIMG SEP1 MF0 MF1; lia. }
          split. { eapply u32arr_transport; [exact HREST| exact MU3| exact WM3|]. cbn. unfold FA, RB. clear - LNF' LFA' T0 T1 SB0 HRI RI1 GC LOIMG SEP1 MF0 MF1; lia. }
          split; [exact LREST|].
          eapply u32arr_transport; [exact HD2| exact MU3| exact WM3|]. cbn. rewrite cpy_length by (rewrite ?LDS; clear - LWS MC2 LDS; lia). rewrite LDS. sglia.
    }
    destruct ok; hnf in RES2; cycle 1.
    - (* [comment removed for export] *)
      destruct RES2 as (-> & RR).
      eapply (evtA_contS_KJ AL true (CSf u f) (K u f) _ Q _ mo2 (KL u f) HK2); [exact HJ2| |].
      { eapply (refill_B_no AL IMG ALWF (CSf u f) (CSOKf u f)) with (m0 := m2) (W := []).
        all: lazymatch goal with
             | |- refill_frame _ _ _ _ _ _ => exact FR2
             | |- stk _ _ _ _ => exact ST2
             | |- mem_inv _ _ => exact MI2
             | |- crange _ _ _ => exact (crange_imp _ _ _ _ (CSinc u f) SCS)
             | |- munch _ _ _ => apply munch_refl
             | |- wmono _ _ _ => apply wmono_refl
             | |- _ => clear - SPL SPH SPA LOIMG; lia end. }
      cbn beta. intros ms3 mo3 PO HK3 MM3 HJ3.
      ddestruct PO as (m3 & -> & MU3 & WM3 & MI3 & ST3). cbn [ms_mem MS MSsvc] in HJ3.
      ddestruct RR as (Hf & HPCx & RR').
      try apply orS_weaken. apply (HC false). apply (FIN 0 m3 mo3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ [C4 (cnt c); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))] HK3 HJ3).
      + eapply munch_weaken; [| exact MU3]. clear. solve_sub_fp.
      + exact WM3. + exact MI3. + exact ST3.
      + eapply rw_cells_transport; [exact HPC2| exact MU3| exact WM3|]. cbn. clear - T1 GC LOIMG; lia.
      + split; reflexivity.
    - (* [comment removed for export] *)
      destruct RES2 as (-> & RR).
      pose proof HPC2 as HPCs. change [C4 (cnt c); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))] with ([C4 (cnt c)] ++ [C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))]) in HPCs.
      apply rw_cells_app in HPCs as [HC1 HC2]. cbn [cells_size csize Nat.add] in HC2. change (Z.of_nat 4) with 4 in HC2.
      eapply (evtA_contS_KJ AL true (CSf u f) (K u f) _ Q _ mo2 (KL u f) HK2); [exact HJ2| |].
      { eapply (refill_B_ok AL IMG ALWF (CSf u f) (CSOKf u f)) with (m0 := m2) (W := []) (T := T) (c := c) (lo := lo).
        all: lazymatch goal with
             | |- rw_cells _ _ _ [C4 _] => exact HC1
             | |- refill_frame _ _ _ _ _ _ => exact FR2
             | |- stk _ _ _ _ => exact ST2
             | |- mem_inv _ _ => exact MI2
             | |- crange _ _ 4096 => exact (CST u f)
             | |- crange _ _ _ => exact (crange_imp _ _ _ _ (CSinc u f) SCS)
             | |- munch _ _ _ => apply munch_refl
             | |- wmono _ _ _ => apply wmono_refl
             | |- _ => clear - SPL SPH SPA LOIMG T0 T1 GC MC2; lia end. }
      cbn beta. intros ms3 mo3 PO HK3 MM3 HJ3.
      ddestruct PO as (m3 & -> & MU3 & WM3 & MI3 & HC1' & ST3). cbn [ms_mem MS MSsvc] in HJ3.
      try apply orS_weaken. apply (HC true). apply (FIN 1 m3 mo3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ [C4 (Z_to_bv 64 (max_count c / 2)); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))] HK3 HJ3).
      + eapply munch_weaken; [| exact MU3]. clear. solve_sub_fp.
      + exact WM3. + exact MI3. + exact ST3.
      + change [C4 (Z_to_bv 64 (max_count c / 2)); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))]
          with ([C4 (Z_to_bv 64 (max_count c / 2))] ++ [C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))]).
        apply rw_cells_app. split; [exact HC1'|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4.
        eapply rw_cells_transport; [exact HC2| exact MU3| exact WM3|]. cbn. clear - T1 GC LOIMG; lia.
      + split; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RefillCfgS.

End ARUN_1.
