(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AJ AKinvS AKinvM AW_Unwind AW_Unwind2 AW_MmapFixed AW_Poison AW_DepotCfg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_CfgS AW_ClassId AW_Combined AW_Refill AW_GetFrom AW_Populate AW_Populate2 AW_CfgDefs AW_PopulateCfgS AW_GetFromCfgS.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_RefillCfgS ASplit AKinvSplit AW_PopulateSplit AW_GetFromSplit.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import SRz.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape.
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
Ltac2 gd_tbl_AW_RefillSplit () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"; "Corelib.Init.Datatypes.option"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.



Section RefillSplit.
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
  Hypothesis GSEP : ltac2:(CDefT.buildp (gd_tbl_AW_RefillSplit ()) "(0.(1.(2.(3.VT,+1000.)VSB,)(2.(3.(3.VSB,(4.+2.+25.))+1000.)VT,))(0.(1.(2.(3.VCTX,+10000.)VT,)(2.(3.VT,+1000.)VCTX,))(1.(2.(3.VCTX,+10000.)VSB,)(2.(3.(3.VSB,(4.+2.+25.))+1000.)VCTX,))))")
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
  Hypothesis LEDGER_U : ltac2:(CDefT.buildp (gd_tbl_AW_RefillSplit ()) "Pmo,$5.P,(2.(3.Vmu,(4.+2.+12.))+>0000000.)P,A3.VK,(6.$7.)(6.$7.)R2.(0.(8.$7.(9.(:.(;.R3.))(<.&40.VUA,)(<.&40.(4.+2.+12.)))$=.)(1.(8.$7.(>.(?.(;.R3.))(<.&40.VUA,)(<.&40.(4.+2.+12.)))$=.)(8.$7.(9.(10.(11.(12.&40.)(12.&40.))(:.(;.R3.))(?.(;.R3.)))(<.&40.VUA,)(<.&40.(4.+2.+12.)))$=.)))")
(* [comment removed for export] *).
  Hypothesis TU_commit : ltac2:(CDefT.buildp (gd_tbl_AW_RefillSplit ()) "Pmo,$5.P,(2.(3.Vmu,(4.+2.+12.))+>0000000.)P,A3.VK,(6.$7.)(6.$7.)R2.P,(8.$7.(>.(?.(;.R3.))(<.&40.VUA,)(<.&40.(4.+2.+12.)))$=.)A3.VK,(13.$7.$=.)(6.$7.)(14.+32.VUA,(4.+2.+12.)R4.)")
(* [comment removed for export] *).
  Hypothesis TU_fresh : ltac2:(CDefT.buildp (gd_tbl_AW_RefillSplit ()) "Pmo,$5.P,(2.(3.Vmu,(4.+2.+12.))+>0000000.)P,A3.VK,(6.$7.)(6.$7.)R2.P,(8.$7.(9.(10.(11.(12.&40.)(12.&40.))(:.(;.R3.))(?.(;.R3.)))(<.&40.VUA,)(<.&40.(4.+2.+12.)))$=.)A3.VK,(13.$7.$=.)(6.$7.)(15.+32.VUA,(4.+2.+12.)R4.)")
(* [comment removed for export] *).
  Hypothesis LEDGER_F : ltac2:(CDefT.buildp (gd_tbl_AW_RefillSplit ()) "Pu,(16.$7.)Pmo,$5.P,(1.(8.(16.$7.)R2.(6.$7.))(8.(16.$7.)R2.(13.$7.$=.)))P,A3.VK,R3.(6.$7.)R2.(0.(8.$7.(9.(:.(;.R3.))(<.&40.VFAA,)(<.&40.(4.+2.+12.)))$=.)(1.(8.$7.(>.(?.(;.R3.))(<.&40.VFAA,)(<.&40.(4.+2.+12.)))$=.)(8.$7.(9.(10.(11.(12.&40.)(12.&40.))(:.(;.R3.))(?.(;.R3.)))(<.&40.VFAA,)(<.&40.(4.+2.+12.)))$=.)))")
(* [comment removed for export] *).
  Hypothesis TF_commit : ltac2:(CDefT.buildp (gd_tbl_AW_RefillSplit ()) "Pu,(16.$7.)Pmo,$5.P,(1.(8.(16.$7.)R2.(6.$7.))(8.(16.$7.)R2.(13.$7.$=.)))P,A3.VK,R3.(6.$7.)R2.P,(8.$7.(>.(?.(;.R3.))(<.&40.VFAA,)(<.&40.(4.+2.+12.)))$=.)A3.VK,R5.(13.$7.$=.)(14.+32.VFAA,(4.+2.+12.)R4.)")
(* [comment removed for export] *).
  Hypothesis TF_fresh : ltac2:(CDefT.buildp (gd_tbl_AW_RefillSplit ()) "Pu,(16.$7.)Pmo,$5.P,(1.(8.(16.$7.)R2.(6.$7.))(8.(16.$7.)R2.(13.$7.$=.)))P,A3.VK,R3.(6.$7.)R2.P,(8.$7.(9.(10.(11.(12.&40.)(12.&40.))(:.(;.R3.))(?.(;.R3.)))(<.&40.VFAA,)(<.&40.(4.+2.+12.)))$=.)A3.VK,R5.(13.$7.$=.)(15.+32.VFAA,(4.+2.+12.)R4.)")
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
            /\ rw_cells asegs mm (R + 16) [C8 (Z_to_bv 64 nf)] /\ rw_cells asegs mm (R + 32) [C8 (Z_to_bv 64 au)] /\ rw_cells asegs mm (R + 68) [C1 exb]
            /\ u32arr asegs mm FA fa /\ u32arr asegs mm (FA + 4 * nf) js0 /\ u32arr asegs mm CH ds)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "05K0@L10191162195.7  L10212982797.13 L10339840027.13 L10654848219.13 L11330413503.7  L11330645183.18 L11330645183.19 L11332851263.8  L11334822405.4  L11636954379.13 L11802433892.3  L11802548827.12 L12015581467.13 L12098782647.14 L12098782647.4  L12115764660.13 L12601911123.163L13266555807.7  L13299539613.13 L14002027037.13 L14954004041.142L14958374359.13 L15065879321.143L15122658121.13 L15587431122.13 L16220488471.13 L16239713677.13 L16349891995.13 L16392807694.268L16681706075.13 L16892873619.7  L16938268957.13 L17118940343.13 L18169585919.13 L18186710872.13 L18186710904.14 L18926386861.190L18926758071.254L18926763017.255L18928747180.256L18941063213.191L19190373851.13 L1919947181.141 L19241880844.13 L19633127881.13 L1964695325.13  L1979631515.13  L20025864219.13 L20199931667.7  L20779001463.161L20979301405.13 L21330862034.14 L22025350102.163L22124814583.160L22380288795.13 L22454804381.141L22785913341.139L22872554921.163L23157713330.13 L23168344402.12 L23168721517.3  L23256703893.13 L23473178733.13 L23797353929.13 L2416523916.14  L2416523948.13  L2416881693.7   L24397740297.13 L24885286555.13 L25434267873.163L25583803606.163L25608327385.13 L25659858761.13 L25709194009.13 L26013379921.5  L26038281501.13 L26457962392.13 L26460522217.142L26602659732.14 L26988824989.13 L27127617376.13 L27617417609.13 L27752029762.13 L27846297964.3  L27985401527.172L28000014519.158L28004109043.141L28275996813.13 L28554005766.14 L2869134573.3   L2869282770.12  L28722154843.13 L28749915688.13 L2882334923.256 L2895800404.14  L29068914677.165L29068915659.164L29068917579.164L29886769227.143L30337598945.163L30374108841.163L30934117385.142L31239763064.13 L31533430865.5  L31540552454.141L31645532919.158L31656084727.172L31818486286.13 L32075750171.13 L32315971273.13 L32689494322.13 L33016505024.14 L33098394413.139L33217685913.142L33280020567.13 L33321251163.13 L33383325641.13 L33466295069.13 L33497480912.13 L33515502905.7  L33903200363.7  L34127075801.13 L34210848443.13 L34313566237.13 L34329410641.13 L34417722907.13 L34609459819.141L34729060546.13 L34795199150.7  L34941587412.14 L3499268102.143 L35149797815.160L35198162098.13 L35684427048.166L35684430230.165L35684432150.165L35879563402.161L36161680872.13 L36431750486.163L36504433881.14 L36530075933.13 L36767624506.166L36778327625.13 L37252228012.164L37696442802.163L37790192876.4  L37790603219.12 L3781552797.13  L38085830811.13 L38235734261.13 L38235734261.14 L38235734261.4  L38237949960.3  L38546213588.14 L38981556660.13 L39036154839.13 L39038219421.13 L39302557143.13 L39893848093.13 L39906680500.13 L40564802327.13 L40865908571.13 L41011650690.13 L41015213144.7  L41015441097.14 L41015441129.13 L41208242738.13 L41325276974.13 L41544298327.13 L41606129192.13 L41814703546.12 L41815113349.3  L41921880.161   L4202410637.13  L42070587795.7  L42366367054.163L42466912109.13 L42510505847.161L43371077505.14 L43371077537.13 L44514048283.13 L44666701613.139L44933202841.142L45194705697.0  L45244317297.13 L45284632083.7  L45646468555.13 L45646468555.14 L45646468555.4  L46068717687.161L46079677525.13 L46319545801.13 L46349820701.13 L4644374363.13  L46465297417.13 L46808305453.139L46875989211.13 L4702297241.142 L47235497906.13 L47298809302.163L47609407641.142L47690334732.142L47862922960.13 L48097119049.14 L48097119081.13 L48736482147.13 L48736484312.13 L49461236434.13 L49983981972.6  L49984559454.13 L50523288139.23 L50527340753.8  L50624451604.13 L50854936278.163L51003398944.14 L51003398944.4  L51072933591.13 L51075522461.13 L5132404781.139 L51465800966.14 L51529931677.13 L51786167833.13 L51884365430.161L51902697689.13 L51931183901.13 L52106535381.13 L52242632905.13 L52417299603.8  L52516341168.13 L52906910299.13 L52949583305.13 L53358130679.172L53358130679.174L53360292855.158L53360292855.160L53741545241.13 L54166772308.14 L54615203157.13 L54705006061.13 L54810485187.6  L5504714008.139 L55411383771.13 L55522234506.161L55776599401.142L5595038665.13  L56085964653.13 L56235262043.13 L5654079942.14  L56583794822.13 L5733193033.13  L5759149202.13  L57600663220.13 L57721544658.14 L58150738006.174L58165354070.160L58327472827.163L58365815060.164L58651980829.13 L5872547218.13  L59095036641.163L59109030405.161L59172263284.13 L59310679498.158L59310679924.163L59310680522.161L59310683082.162L59310685002.162L59314873579.164L59321099210.171L59323689553.139L59323689553.140L5953765770.161 L59850771522.13 L60220216552.13 L60298975903.13 L60298975935.14 L60299333678.7  L60352520253.139L60438092249.13 L60880885645.13 L60951472185.7  L6115894795.13  L61707373910.174L61721987926.160L61766680649.13 L61811395478.160L61816019993.13 L61821816214.174L61987289174.161L62273018057.13 L62412221001.13 L6241432505.7   L62418758342.14 L62580585650.163L62741115888.13 L62800546763.164L63111805597.13 L63152484003.142L63228287635.7  L63379813335.13 L63562516125.13 L64143838421.13 L64274725833.13 L64661504413.13 L64943164763.13 L65175065619.7  L65228120857.13 L65428237517.13 L65832345747.7  L65884286807.13 L66509687170.7  L66510045971.14 L66510046003.13 L66632305330.268L6697770711.13  L67019626837.165L67174446998.13 L67174447030.14 L67783461239.161L67867201474.13 L67875248962.13 L6796109341.141 L68137219849.13 L68150369429.13 L6850489741.13  L6937171316.13  L6992194185.13  L7289454877.13  L7327952799.14  L7349075442.13  L7377668436.14  L7464843221.13  L7635215125.12  L7635623978.3   L7989581083.13  L8413342696.3   L8413718743.12  L8854111435.14  L8854111435.4   L8948289623.13  L9218609678.13  L9438734020.2   L9599407968.13  L9735906861.139 L9870379117.13  L9931051511.161 L998301849.142  00000J00K00L00M00f01^02Y03403E03F03G03Y03Z04;04@04A05?05W05X05Y06\06]07a08@08A08B08C08D08c08d09>09]0:>0:?0:R0:e0;D0;c0<B0<a0=@0=A0?80?W0@60@U0@V0@W0A10Ag0Ah0Ai0Be0D>0D?0Ej0FS0GS0H20H:0H;0H<0H=0H\0Hk0I:0II0Ih0Ii0J]0KY0KZ0L90LZ0Lm0Ln0MM0N>0N?0N@0N_0O>0O?0OF0PG0Q=0S40S50S60S70SG0SH0SI0Sh0Si0U\0WO0YB0[10[e0\e0]a0^C0^V0`M0aC0bD0bE0bF0be0cD0cK0e>0f:0f;0f<0f[0g:0g;0gL0gd0ge0gf0gg0hH0hI0jD0jE0j_0j`0kh0mM0ml0oW11;12f13U13V14R14S15215m16L17E18618718B18a18b19D19f19j19n19o1:01:11:21:31:41:51:61:71:81:F1:T1:b1;A1;B1;C1;D1;R1;S1<h1<i1=C1>71>81>n1?D1?Z1?[1AN1BJ1BK1Bj1CD1Cf1DH1DL1EB1EC1Eb1FA1FB1Fa1HT1HU1IQ1J01Jl1Kh1Ld1MC1MI1MO1N71N`1Na1No1O01PD1P_1P`1Q\1Q]1Q^1Q_1Q`1SS1ST1SU1T61Tl1Tm1Tn1To1UN1V01V11V21VQ1WR1X`1YV1ZY1[:1[;1[<1[]1[k1]^1]_1^N1_?1_^1__1_`1_a1_b1`A1`B1`C1`D1aK1bG1cC1dQ1dR1dS1eG1f61f71fV1g51gT1h31hR1i11iP1io1jN1k=1k>1k?1kG1kO1kW1mJ1mK1mL1m]1m^1ne1oa20@21<21=22D23P23o24N24_24`25Q25X26N26O27427N27O27P27Q28028128228L28m29L29f29g29o2:72:?2:^2:_2;g2<12<;2=12=22=32>^2?=2?\2?]2?^2@=2@\2@g2AF2AG2AH2AT2AU2AV2AW2Ac2BD2BI2BJ2BK2BR2C12Dd2De2E[2FWS3hAR2RI1c2GC2lo5LOIMG3RI1FFFS3hAR3CTX2SP2lo5LOIMG3CX1S3hAR2SB2RI1c2GC3mfa3js02SP2nf2lo4LJS05LOIMG3HRI3RI13MF1S3hAR2SB2RI1c2GC3mfa2fa2SP2nf2lo4HNF23LFA5LOIMG3HRI3RI13MF1S3hAR1T1c2GC2SP2lo5LOIMG2T1S3hAR2SP2lo5LOIMGFFS3hAR1T1c2GC2SP2T0FS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1T1cFS3hAR1T3CTX2SB2RI1c1R2RB2FA4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG3CX1S3hAR2SP2lo5LOIMG1A2k01HFFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T1FS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA3js03SB03MF03MF1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR2RI1c2GC2lo5LOIMG3RI1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T1c2SP2T03MC2S3hAR1T1c2SP2T03MCRS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF03MF14MU0'S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS3hAR2RI1c2GC2lo5LOIMG3RI1S3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1FFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC4GSEP2mu3mfa2UA3FAA2fa2SP2nf2lo5GMISS3LFA5LOIMG3HRI3MC2FS3hAR1T3CTX2SB2RI1c1R2RB2FA2GT4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2loS3hAR1T3CTX2SB2RI1c1R2RB2FA2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SP3SPHFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T2lo5LOIMG2T1FS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC4GSEP2mu3mfa2UA3FAAFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SP2loS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI13MC22ws3LWSS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'3MC2FFFS3hAR1T1c2SP3TALFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SB03HRI3RI12T13CX13MF04MU0'3HMUS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3UOK3LDS5LOIMG3SB03HRI3RI12T13CX13MF04MU0'S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SB03HRI3RI12T13CX13MF03MF14MU0'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'4rest3nf'4LFA'4LNF'S3hAR1T1c2GC2SP2lo5LOIMG2T1FS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFFFFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FFS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1FFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3mfa1f3fa'4rest3nf'4LFA'5LREST2UFSFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI13MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T13MC22ws3LWSS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T1S1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1c3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FS3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMGS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC4GSEP2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC4GSEP2mu3mfa2UA3FAA2SP2lo3UOK5LOIMG3HRI4MU0'FFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMGFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMGFFS2SP3SPHS2SP3SPHS2SP3SPHS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FFS3hAR2SP2lo5LOIMGFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2fa2nf5GMISS3LFA3SB03MC2S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SP2lo5LOIMGFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC4GSEP2mu3mfa2UA3FAAS1c3MC2S3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMG1A2k01HFS3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2RI1c2GC2lo5LOIMG3RI1FFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS3hAR2RI1c2GC2lo5LOIMG3RI1S1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2RI1c2GC2lo5LOIMG3RI1FS2SP3SPAS2SP3SPAS2SP3SPAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2au3UOK3HAU3SB04MU0'S3hAR1T2T1S3hAR1T2T1S3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1FFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GT4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3TALS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS3hAR1T1c2GCFFFS3hAR1T1c2GCS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1T1cFFS1c3MC1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI". (* [comment removed for export] *)
  #[using="AL IMG ALWF CSOKf CSmono_u CSmono_f ASB GSB GC GT GCTX GSEP CST CSCTX CSRI KL LEDGER_U TU_commit TU_fresh LEDGER_F TF_commit TF_fresh GMU GMFA CSUz CSFz ROOM_U SCAR_U ROOM_F SCAR_F"] Lemma refill_split_noinit : forall (TA TB : TSet)
      (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (exb : bv 8)
      (j1 j2 j3 stw cntw csw : word) (fa js0 ds shU shF : list _)
      (SP : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (au nf lo : Z),
      let cs := class_size c in let PCR := T + 208 + 80 * c in
      nf < max_count c / 2 -> mu < au + cs * (max_count c / 2 - nf) -> mu + 2^18 <= 0xE0000000 ->
      0 <= au <= mu -> mu - au <= 2^19 -> au mod 16 = 0 ->
      0 <= nf -> 4 * nf <= mfa -> 4 * (nf + 2^14) + 2^18 <= 2^29 -> Z.of_nat (length fa) = nf -> 4 * (nf + Z.of_nat (length js0)) = mfa ->
      length ds = 16%nat -> crange (CSf None None) FA mfa ->
      rw_cells asegs m PCR [C4 cntw; C4 (Z_to_bv 64 (max_count c)); C8 csw] -> u32arr asegs m (PCR + 16) ds ->
      rw_cells asegs m R [C8 (Z_to_bv 64 0)] ->
      rw_cells asegs m (R + 16) [C8 (Z_to_bv 64 nf)] -> rw_cells asegs m (R + 24) [C8 (Z_to_bv 64 mfa)] ->
      rw_cells asegs m (R + 32) [C8 (Z_to_bv 64 au)] -> rw_cells asegs m (R + 40) [C8 (Z_to_bv 64 0)] ->
      rw_cells asegs m (R + 48) [C8 (Z_to_bv 64 mu)] -> rw_cells asegs m (R + 56) [C8 (Z_to_bv 64 0)] ->
      rw_cells asegs m (R + 68) [C1 exb] -> rw_cells asegs m (R + 72) [C8 stw] ->
      rw_cells asegs m (T + 2872) [C8 j1; C8 j2] -> rw_cells asegs m (T + 2792) [C8 j3] ->
      rw_cells asegs m (0x7fff8000 + UA / 8) [CB (Z.to_nat 32768) shU] ->
      rw_cells asegs m (0x7fff8000 + FAA / 8) [CB (Z.to_nat 32768) shF] ->
      u32arr asegs m FA fa -> u32arr asegs m (FA + 4 * nf) js0 ->
      poison_statics m -> thr_statics m CTX T -> mwc_statics m -> pop_statics m SB -> ro_cells asegs m (A_INSTANCE + 48) [C8 (Z_to_bv 64 RI)] ->
      stk asegs m lo SP -> ACEIL <= lo -> lo <= SP - 1760 -> SP <= 2^63 -> SP mod 16 = 0 ->
      crange (CSf None None) lo (SP - lo) -> mem_inv asegs m -> tp = Z_to_bv 64 A_TP ->
      K None None mo -> J m mo ->
      TA [] -> TB [] ->
      (forall ok c', rf_cpostS ok SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F fc au nf lo exb cntw csw fa js0 ds shU shF
                     [(PCR, PCR + 4); (PCR + 16, PCR + 16 + 4 * (max_count c / 2))] (fun _ => True) m c' -> srealizesJ asegs c' (if ok then TB else TA)) ->
      srealizesJ asegs
        (mkCfg (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (T + 208)) (Z_to_bv 64 PCR) (Z_to_bv 64 A_INSTANCE) (Z_to_bv 64 c) a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 A_REFILL) fc None m (seg_rom asegs)) mo) (t_alt2 TA TB).
  Proof.
    intros TA TB ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 exb j1 j2 j3 stw cntw csw fa js0 ds shU shF SP F fc m mo au nf lo cs PCR GMISS NEEDU UOK
      HAU HINV AUAL HNF HNF2 HNF3 LFA LJS0 LDS CSFA HPC HD MX NF MFA AU M40 MUC M56 EX STC TJ SJ SHU SHF HFAR HJS PS TS MWS PPS RIC
      ST LOIMG SPL SPH SPA SCS MI TP HK0 HJ0 A0n B0n HC.
    facts.
    dpose GSB as (SB0 & SBAL & HRI & RI1). dpose GT as (T0 & T1 & TAL). pose proof GCTX as (CX0 & CX1).
    dpose GSEP as (SEP1 & SEP2 & SEP3). dpose GMFA as (MF0 & MFAL & MF1). dpose GMU as (MU0' & MUAL & MUH).
    assert (HR : R = RI + 128 * c) by reflexivity. subst cs PCR.
    pose proof (max_cached_fits c GC) as [MC1 MC2]. pose proof (max_count_range c GC) as MCR.
    (* [comment removed for export] *)
    eapply (evtA_srzJ_KJ AL (CSf None None) (K None None) _ _ _ mo (KL None None) HK0); [exact HJ0| |].
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
    assert (RIC1 : ro_cells asegs m1 (A_INSTANCE + 48) [C8 (Z_to_bv 64 RI)]) by (eapply ro_cells_transport; [exact RIC| exact MU1| unfold A_INSTANCE; cbn; clear - LOIMG; lia]).
    clear TR1 HPC MX NF MFA AU M40 MUC M56 EX STC TJ SJ SHU SHF HD HFAR HJS PS TS MWS PPS RIC ST MI.
    (* [comment removed for export] *)
    eapply (getfrom_split AL IMG ALWF CSf CSOKf CSmono_u CSmono_f ASB T CTX SB RI c GSB GC GT GCTX GSEP CST CSCTX CSRI K KL mu mfa
                LEDGER_U TU_commit TU_fresh LEDGER_F TF_commit TF_fresh GMU GMFA CSUz CSFz ROOM_U SCAR_U ROOM_F SCAR_F TA TB)
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
           | |- ro_cells _ _ _ _ => exact RIC1
           | |- stk _ _ _ _ => exact ST1
           | |- crange _ _ _ => first [ exact CSFA | (eapply crange_sub; [exact SCS| clear - SPL; lia| clear - SPL; lia]) ]
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 A_TP => exact TP
           | |- K _ _ _ => exact HK1
           | |- J _ _ => exact HJ1
           | |- forall ok c', _ => idtac
           | |- _ => idtac end.
      all: lazymatch goal with |- forall ok c', _ => idtac | |- _ (@nil _) => assumption | |- _ => first [ exact GMISS | exact NEEDU | exact UOK | exact HAU | exact HINV | exact AUAL | exact HNF | exact HNF2 | exact HNF3 | exact LFA | exact LJS0 | exact LDS | exact LOIMG | exact MC2
                 | (change (2^18) with 262144; clear - MC1; lia) | (clear - T0 T1 TAL GC SPL SPH SPA; lia) | (match goal with |- ?g => idtac "UNSOLVED" g end; fail) ] end.
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
      eapply (evtA_srzJ_KJ AL (CSf u f) (K u f) _ _ _ mo2 (KL u f) HK2); [exact HJ2| |].
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
      apply (HC false). apply (FIN 0 m3 mo3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ [C4 cntw; C4 (Z_to_bv 64 (max_count c)); C8 csw] HK3 HJ3).
      + eapply munch_weaken; [| exact MU3]. clear. solve_sub_fp.
      + exact WM3. + exact MI3. + exact ST3.
      + eapply rw_cells_transport; [exact HPC2| exact MU3| exact WM3|]. cbn. clear - T1 GC LOIMG; lia.
      + split; reflexivity.
    - (* [comment removed for export] *)
      destruct RES2 as (-> & RR).
      pose proof HPC2 as HPCs. change [C4 cntw; C4 (Z_to_bv 64 (max_count c)); C8 csw] with ([C4 cntw] ++ [C4 (Z_to_bv 64 (max_count c)); C8 csw]) in HPCs.
      apply rw_cells_app in HPCs as [HC1 HC2]. cbn [cells_size csize Nat.add] in HC2. change (Z.of_nat 4) with 4 in HC2.
      eapply (evtA_srzJ_KJ AL (CSf u f) (K u f) _ _ _ mo2 (KL u f) HK2); [exact HJ2| |].
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
      apply (HC true). apply (FIN 1 m3 mo3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ [C4 (Z_to_bv 64 (max_count c / 2)); C4 (Z_to_bv 64 (max_count c)); C8 csw] HK3 HJ3).
      + eapply munch_weaken; [| exact MU3]. clear. solve_sub_fp.
      + exact WM3. + exact MI3. + exact ST3.
      + change [C4 (Z_to_bv 64 (max_count c / 2)); C4 (Z_to_bv 64 (max_count c)); C8 csw] with ([C4 (Z_to_bv 64 (max_count c / 2))] ++ [C4 (Z_to_bv 64 (max_count c)); C8 csw]).
        apply rw_cells_app. split; [exact HC1'|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4.
        eapply rw_cells_transport; [exact HC2| exact MU3| exact WM3|]. cbn. clear - T1 GC LOIMG; lia.
      + split; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "05b0@L10195602566.152L10210351694.15 L10341395032.15 L10657484440.15 L11137167147.15 L11332851263.8  L11638509384.15 L11802433892.3  L11802548827.12 L12012970840.15 L12098782647.4  L12114182135.15 L12601911123.170L13101100758.150L13297943774.15 L13514868359.13 L14004625502.15 L14954004041.148L14961014676.15 L15065879321.149L15121066250.15 L15590033553.15 L16223131988.15 L16238118862.15 L16352532440.15 L16392807694.278L16683300888.15 L16939819870.15 L18166954684.15 L18186710872.13 L18186710904.14 L18799879001.13 L18926386861.200L18926758071.264L18926763017.265L18928747180.266L18941063213.201L19192973208.15 L1919947181.147 L19240294223.15 L19630496650.15 L1966245214.15  L19729564509.9  L1976999384.15  L19919635993.13 L20024273496.15 L20779001463.168L2078153834.13  L20977739358.15 L21330862034.14 L22025350102.170L22124814583.166L22377677144.15 L22454804381.147L22785913341.145L22872554921.170L22973222058.10 L23159305201.15 L23168344402.12 L23168721517.3  L23255153110.15 L23474737710.15 L23794718602.15 L2416523916.14  L2416523948.13  L2416881693.7   L24396145482.15 L24887889112.15 L25434267873.170L25583803606.170L25606769306.15 L25658262794.15 L25707639130.15 L26040926046.15 L26460522217.148L26460564955.15 L26602659732.14 L26986189790.15 L27125009699.15 L27487356397.13 L27615822794.15 L27750433793.15 L27846297964.3  L27985401527.178L28000014519.164L28004109043.147L28274401998.15 L28363221667.171L28554005766.14 L2869134573.3   L2869282770.12  L28719519512.15 L28720477168.152L28748332139.15 L2882334923.266 L28826264790.150L2895800404.14  L29068914001.121L29068914677.172L29068915659.171L29068917579.171L29772069895.13 L29886769227.149L30337598945.170L30374108841.170L30934117385.148L31093078368.152L31241317947.15 L31540552454.147L31645532919.164L31656084727.178L31821121613.15 L32077332824.15 L32127951705.13 L32313363594.15 L32452642285.13 L32687932273.15 L33098394413.145L33217685913.148L33278429716.15 L33322806040.15 L33384908170.15 L33463695710.15 L33499030675.15 L34125480858.15 L34209285368.15 L34310922846.15 L34416139352.15 L34609459819.147L34731668097.15 L34941587412.14 L3499268102.149 L35149797815.166L35195522801.15 L35684427048.173L35684430230.172L35684432150.172L35879563402.168L35923448199.13 L36160090027.15 L36254154137.13 L36431750486.170L36504433881.14 L36531659614.15 L36767624506.173L36775715850.15 L36836618296.173L37252228012.171L37696442802.170L37790192876.4  L37790603219.12 L3779965150.15  L38088471256.15 L38235734261.13 L38235734261.14 L38235734261.4  L38237949960.3  L38238378678.15 L38546213588.14 L39033514388.15 L39039774430.15 L39127155118.15 L39304116116.15 L39895403102.15 L39908263159.15 L40566364500.15 L40867470616.15 L41009052353.15 L41015213144.7  L41015441097.14 L41015441129.13 L41206659185.15 L41212515002.122L41322673517.15 L41541694740.15 L41603529835.15 L41814703546.12 L41815113349.3  L41921880.167   L4199803086.15  L42366367054.170L42464312622.15 L42475409671.13 L42510505847.168L42961284182.152L43371077505.14 L43371077537.13 L43454801945.13 L44087897094.152L4448596182.150 L44511404888.15 L44666701613.145L44779457238.150L44933202841.148L45194705697.0  L45246915634.15 L45646468555.13 L45646468555.14 L45646468555.4  L46068717687.168L46082313750.15 L46181399442.14 L46321137546.15 L46347221342.15 L46466889290.15 L4647017752.15  L46808305453.145L46878592664.15 L4702297241.148 L47233902065.15 L47298809302.170L47609407641.148L47690334732.148L47864505491.15 L48097119049.14 L48097119081.13 L49424561926.150L49462823057.15 L49675877529.13 L49983981972.6  L49986110237.15 L50523273552.10 L50523288139.23 L50525401681.22 L50525401681.23 L50525451345.121L50527340753.8  L50527340882.6  L50622860887.15 L50854936278.170L51003398944.14 L51003398944.4  L5101806806.150 L51070321812.15 L51078153694.15 L5132404781.145 L51465800966.14 L51527287262.15 L51784608858.15 L51884365430.168L51901106842.15 L51933782366.15 L52108131222.15 L52241042058.15 L52417299603.8  L52516341168.13 L52904278040.15 L52951179146.15 L53358130679.178L53358130679.180L53360292855.164L53360292855.166L53738913114.15 L54120698182.14 L54166772308.14 L54617802518.15 L54810485187.6  L5504714008.145 L55414015896.15 L55522234506.168L55776599401.148L5592439178.15  L56083332398.15 L56233712152.15 L5654079942.14  L56581188293.15 L57239329095.13 L5730586378.15  L57603261687.15 L5761793745.15  L57721544658.14 L58150738006.180L58165354070.166L58327472827.170L58365815060.171L58649374302.15 L5875150801.15  L58787062638.150L59095036641.170L59109030405.168L59170705207.15 L59308583155.150L59308583155.171L59310679498.164L59310679504.119L59310679924.170L59310680522.168L59310683082.169L59310685002.169L59314873579.171L59321099210.177L59323689553.145L59323689553.146L5953765770.168 L59849184769.15 L60218658475.15 L60298975903.13 L60298975935.14 L60299333678.7  L60352520253.145L60414336007.150L60436530074.15 L60882472398.15 L6117489736.15  L61707373910.180L61721987926.166L61769292298.15 L61811395478.166L61818652250.15 L61821816214.180L61987289174.167L62275617418.15 L62413778954.15 L62418758342.14 L62495665017.152L62580585650.170L62741115888.13 L62800546763.171L63114436830.15 L63152484003.148L63377205652.15 L63564111070.15 L64146445974.15 L64277324170.15 L64290542475.13 L64659921886.15 L64940562200.15 L65226570074.15 L65430877838.15 L65886893332.15 L66509687170.7  L66510045971.14 L66510046003.13 L66632305330.278L66680329095.13 L6696174740.15  L67019626837.172L67136342570.10 L67174446998.13 L67174447030.14 L67783461239.168L67865613697.15 L67872637185.15 L6796109341.147 L68138773834.15 L68153001686.15 L6853130190.15  L6934531895.15  L6994800842.15  L7286823774.15  L7327952799.14  L7350626225.15  L7377668436.14  L7463251350.15  L7635215125.12  L7635623978.3   L7987990360.15  L8413342696.3   L8413718743.12  L8854111435.4   L8949877268.15  L9215969357.15  L9438734020.2   L9479706218.6   L9596767523.15  L9735906861.145 L9873019438.15  L9895530922.10  L9931051511.168 L998301849.148  00002@02A02B02C02g03B03C03D03V03W03\03]04[06l06m06n06o08208309709V09W09X09Y09Z0:90::0:Y0:Z0:m0;@0;A0;`0<?0<^0==0=\0=]0?T0@30@R0A10AN0AO0B00B10Bg0Bh0Bi0Bj0Cf0E?0E@0Fk0GT0HT0I20IQ0IY0IZ0I[0I\0J;0JJ0JY0Jh0KG0KH0L<0M80M90MX0N90N:0Nk0OJ0OK0OL0Ok0Ol0PK0PL0PS0QT0RJ0TA0TB0Vg0Vh0Vi0W90W:0YN0YO0Yn0\?0\@0^70_j0a]0cP0cQ0e@0f40g40h00j[0k=0m40mj0nk0nl0nm0nn0oM0oN0om11`12\12]12^13=13\13]13^13_13`13a15\15]15^16f18K18j1:U1<91=d1>S1>T1>U1>V1?R1?S1@21@m1AL1C\1DU1EF1EG1ER1F11F21FT1G61G:1G>1G`1Ga1Gb1Gc1HK1HL1HM1HN1HO1HP1HQ1H_1Hm1I;1IZ1KI1KJ1KK1KL1KZ1K[1M01M11Me1Mf1Mg1N]1Q81QN1Qd1RE1TU1Vf1Vg1XZ1Zk1[g1[h1\G1\i1]K1]O1^E1^F1^j1_I1_h1`G1`H1b;1b<1c81cW1dS1eO1fK1fj1g01g61iG1iH1iI1iW1iX1j?1kT1la1mm1o<1oW1om1on20j20k20l23=23>23?25225325425U26K26L26M26N26m27P27Q27R2812922:@2;62<92<Z2=>2=?2=@2=N2?A2?B2@12@b2AA2AB2AC2AD2AE2AF2Ae2Af2Ag2Ah2Bo2Ck2Dg2F52F62F72H\2IP2J?2J@2J_2K>2K]2L<2L[2M:2MY2N82NW2O62OU2P42Pc2Pd2Pe2Pm2Q52Q=2S02UA2UB2UC2UD2VK2WG2Wf2Xb2Xc2Yj2[62[U2\42\52^P2_A2_H2`>2`?2`d2`e2`f2`g2aF2aG2aH2aI2aj2bI2bJ2bR2bZ2bb2cA2cB2cC2dK2di2e32e=2f32f42f52g`2h?2h^2h_2h`2i?2i^2ii2jH2jI2jJ2jV2jW2jX2jY2je2jj2jk2jl2k32kD2kc2mV2mW2n52nk2ogS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'2T03CX04SEP14SEP23MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFFFS1T2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAAS3hAR1T1c2GC2SP2lo5LOIMG2T1FFS3hAR1T1c2GC2SP2T0FS1T1cFS3hAR1T3CTX2SB2RI1c1R2RB2FA4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG3CX1S3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB03HRI2T03CX03MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFFFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T1FS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA3js03SB03MF03MF1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T1c2SP2T03MC2S3hAR1T1c2SP2T03MCRFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF03MF14MU0'S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T2SP2lo5LOIMG2T01A2k01HFS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1FFFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC4GSEP2mu3mfa2UA3FAA2fa2SP2nf2lo5GMISS3LFA5LOIMG3HRI3MC2FS3hAR1T3CTX2SB2RI1c1R2RB2FA2GT4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2loS3hAR1T3CTX2SB2RI1c1R2RB2FA2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T1S3hAR1T3CTX2SP2lo5LOIMG2T03CX0S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SP3SPHFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC4GSEP2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SP2loS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI13MC22ws3LWSS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'3MC2FS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2au2lo3HAU3LDS5LOIMG4SB645ALWF'4IMG'3SB03HRI3RI12T02T13CX03CX13MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFFS3hAR1T1c2SP3TALFS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB02T03CX04SEP14SEP23MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB03HRI2T03CX03MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3UOK3LDS5LOIMG3SB03HRI3RI12T13CX13MF04MU0'3MF1S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SB03HRI3RI12T13CX13MF04MU0'3HMUS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3UOK3LDS5LOIMG3SB03HRI3RI12T13CX13MF04MU0'S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SB03HRI3RI12T13CX13MF03MF14MU0'FS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3UOK3HAU3LDS3SB03HRI3RI13CX13MF04MU0'3MF1S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T1S3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3UOK3HAU3LDS4SB645ALWF'4IMG'3SB03HRI3RI12T03CX03CX14SEP14SEP33MF04MU0'3MC23MCR3CSR1u4MUB21P2HP3MF1S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SPS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3UOK3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI13MC22ws3LWSFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFFFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3UOK3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'3MF1FFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2au3UOK3HAU3SB04MU0'S3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA4GMFA2fa3js02SP2nf2lo4LJS05LOIMG3SB03HRIS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS3SB03HRI3RI13CX13MF04MU0'3HMUS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds3LDS3SB03HRI3RI13CX13MF03MF14MU0'S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3UOK3HAU3LDS3SB03HRI3RI13CX13MF04MU0'S3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMGFFFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA1A2k01HS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'2T03CX04SEP14SEP23MF04MU0'3MC23MCR3CSR1u4MUB21P2HPS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC4GSEP2mu3mfa2UA3FAAFS2SP2lo3SPLS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2loS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2loS2loS2loS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2loFFFS1T2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA3MC2FFFFFFS3hAR2lo5LOIMGS3hAR2lo5LOIMGS3hAR2lo5LOIMGS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3UOK3HAU3LDS3SB03HRI3RI13CX13MF04MU0'3MF1FFFS3hAR1T2SP3SPAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA4GMFA2fa3js02nf3LFA4LJS03SB0FS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAAFFS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB02T03CX04SEP14SEP33MF03MF14MU0'3MC23MCR3CSR1u4MUB21P2HPS3hAR1T2SP2lo5LOIMG2T1S3hAR1T2SP2lo5LOIMG2T1S1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'2T03CX04SEP14SEP23MF04MU0'3MC23MCR3CSR1u4MUB21P2HPS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB03HRI2T03CX03MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB03HRI2T03CX03MF04MU0'3MC23MCR3CSR1u4MUB21P2HPS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRISS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SPS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SPS2SPS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1FS1T2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1c2GCS1c2GCS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB03HRI2T03CX03MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFFS1c3MC22ws3LWSFS3hAR1T3CTX2SP2lo5LOIMG2T03CX03CX14SEP2S3hAR1T2SB2RI1c2GC3mfa2SP2lo5LOIMG3SB03HRI3RI12T02T14SEP13MF13fa'5rest'3nf'4LFA'4LNF'S3hAR1T2SB2RI1c2GC3mfa3js02SP2nf2lo3HNF4LJS05LOIMG3SB03HRI3RI12T02T14SEP13MF1S3hAR1T2SB2RI1c2GC3mfa2fa2SP2nf2lo4HNF23LFA5LOIMG3SB03HRI3RI12T02T14SEP13MF1S3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG3HRI3RI12T1S3hAR1T1c2GC2SP2lo5LOIMG2T1S3hAR1T2SP2lo5LOIMG2T0FS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFFS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB03HRI2T03CX03MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FFS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1FFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3mfa1f3fa'5rest'3nf'4LFA'5LREST2UFSFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI13MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T13MC22ws3LWSS3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2SP2lo5LOIMG2T1S1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS1T2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAAFFS1c3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FS3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMGS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC4GSEP2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC4GSEP2mu3mfa2UA3FAA2SP2lo3UOK5LOIMG3HRI4MU0'FFS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2au2lo3HAU3LDS5LOIMG4SB645ALWF'4IMG'3SB03HRI3RI12T02T13CX03CX13MF04MU0'3MC23MCR3CSR1u4MUB21P2HPS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMGFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMGFFS2SP3SPHS2SP3SPHS2SP3SPHS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3HAU3LDS4SB645ALWF'4IMG'3SB03HRI2T03CX03MF04MU0'3MC23MCR3CSR1u4MUB21P2HPFFFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRIFS3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI3MC22ws3LWSS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2fa2nf5GMISS3LFA3SB03MC2S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS3hAR2AL1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2au3UOK3HAU3LDS4SB645ALWF'4IMG'3SB02T03CX04SEP14SEP33MF04MU0'3MC23MCR3CSR1u4MUB21P2HPS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC4GSEP2mu3mfa2UA3FAAS1c3MC2S3hAR2SB2RI1c1R2RB2FA2mu3mfa2UA3FAA2SP2lo5LOIMG1A2k01HFS3hAR1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFFS1T2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFS2SP3SPAS2SP3SPAS2SP3SPAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GSEP2mu3mfa2UA3FAA2au3UOK3HAU3SB04MU0'S3hAR1T3CTX2SP2lo5LOIMG2T03CX0S3hAR1T2T1S3hAR1T2T1S3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1FFS3hAR1T3CTX2SB2RI1c1R2RB2FA2GT4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'S2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3TALS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAFFS3hAR1T1c2GCFFFS3hAR1T1c2GCS1T1cFFS1c3MC1S1T1c2GC1j2Hj3HjcS2SB2RI1c1R2RB2FA2mu3mfa2UA3FAAS3hAR1T3CTX2SB2RI1c1R2RB2FA2GC2GT4GCTX4GSEP2mu3mfa2UA3FAA2fa3js02ds2SP2lo3LDS5LOIMG3SPL3SB03HRI3RI12T13CX13MF04MU0'FS3hAR1T3CTX2SP2lo5LOIMG2T03CX0S3hAR2SB2RI1c1R2RB2FA2GC2mu3mfa2UA3FAA2SP2lo5LOIMG3RI1S3hAR1T3CTX2SB2RI1c1R2RB2FA3GSB2GC2GT4GSEP2mu3mfa2UA3FAA3HRI". (* [comment removed for export] *)
  #[using="AL IMG ALWF CSOKf CSmono_u CSmono_f ASB GSB GC GT GCTX GSEP CST CSCTX CSRI KL LEDGER_U TU_commit TU_fresh LEDGER_F TF_commit TF_fresh GMU GMFA CSUz CSFz ROOM_U SCAR_U ROOM_F SCAR_F"] Lemma refill_split_init : forall (TA TB : TSet)
      (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (exb : bv 8)
      (j1 j2 j3 stw : word) (cnt mx csx : Z -> word) (rest : Z -> list cell) (fa js0 ds shU shF : list _)
      (SP : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (au nf lo : Z),
      let cs := class_size c in let PCR := T + 208 + 80 * c in
      nf < max_count c / 2 -> mu < au + cs * (max_count c / 2 - nf) -> mu + 2^18 <= 0xE0000000 ->
      0 <= au <= mu -> mu - au <= 2^19 -> au mod 16 = 0 ->
      0 <= nf -> 4 * nf <= mfa -> 4 * (nf + 2^14) + 2^18 <= 2^29 -> Z.of_nat (length fa) = nf -> 4 * (nf + Z.of_nat (length js0)) = mfa ->
      length ds = 16%nat -> crange (CSf None None) FA mfa ->
      (forall j, cells_size (rest j) = 64%nat) -> (forall j, 1 <= j <= 31 -> pc_old m T cnt mx csx rest j) -> mx c = Z_to_bv 64 0 -> rest c = [CB 64%nat (u32s ds)] ->
      rw_cells asegs m R [C8 (Z_to_bv 64 0)] ->
      rw_cells asegs m (R + 16) [C8 (Z_to_bv 64 nf)] -> rw_cells asegs m (R + 24) [C8 (Z_to_bv 64 mfa)] ->
      rw_cells asegs m (R + 32) [C8 (Z_to_bv 64 au)] -> rw_cells asegs m (R + 40) [C8 (Z_to_bv 64 0)] ->
      rw_cells asegs m (R + 48) [C8 (Z_to_bv 64 mu)] -> rw_cells asegs m (R + 56) [C8 (Z_to_bv 64 0)] ->
      rw_cells asegs m (R + 68) [C1 exb] -> rw_cells asegs m (R + 72) [C8 stw] ->
      rw_cells asegs m (T + 2872) [C8 j1; C8 j2] -> rw_cells asegs m (T + 2792) [C8 j3] ->
      rw_cells asegs m (0x7fff8000 + UA / 8) [CB (Z.to_nat 32768) shU] ->
      rw_cells asegs m (0x7fff8000 + FAA / 8) [CB (Z.to_nat 32768) shF] ->
      u32arr asegs m FA fa -> u32arr asegs m (FA + 4 * nf) js0 ->
      poison_statics m -> thr_statics m CTX T -> mwc_statics m -> pop_statics m SB -> ro_cells asegs m (A_INSTANCE + 48) [C8 (Z_to_bv 64 RI)] ->
      stk asegs m lo SP -> ACEIL <= lo -> lo <= SP - 1760 -> SP <= 2^63 -> SP mod 16 = 0 ->
      crange (CSf None None) lo (SP - lo) -> mem_inv asegs m -> tp = Z_to_bv 64 A_TP ->
      K None None mo -> J m mo ->
      TA [] -> TB [] ->
      (forall ok c', rf_cpostS ok SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F fc au nf lo exb (cnt c) (Z_to_bv 64 cs) fa js0 ds shU shF
                     [(T + 288, T + 2768)] (fun mm => forall j, 1 <= j <= 31 -> j <> c -> pc_new mm T cnt rest j) m c' -> srealizesJ asegs c' (if ok then TB else TA)) ->
      srealizesJ asegs
        (mkCfg (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (T + 208)) (Z_to_bv 64 PCR) (Z_to_bv 64 A_INSTANCE) (Z_to_bv 64 c) a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 A_REFILL) fc None m (seg_rom asegs)) mo) (t_alt2 TA TB).
  Proof.
    intros TA TB ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 exb j1 j2 j3 stw cnt mx csx rest fa js0 ds shU shF SP F fc m mo au nf lo cs PCR GMISS NEEDU UOK
      HAU HINV AUAL HNF HNF2 HNF3 LFA LJS0 LDS CSFA REST PCS MX0 RESTC MX NF MFA AU M40 MUC M56 EX STC TJ SJ SHU SHF HFAR HJS PS TS MWS PPS RIC
      ST LOIMG SPL SPH SPA SCS MI TP HK0 HJ0 A0n B0n HC.
    facts.
    dpose GSB as (SB0 & SBAL & HRI & RI1). dpose GT as (T0 & T1 & TAL). pose proof GCTX as (CX0 & CX1).
    dpose GSEP as (SEP1 & SEP2 & SEP3). dpose GMFA as (MF0 & MFAL & MF1). dpose GMU as (MU0' & MUAL & MUH).
    assert (HR : R = RI + 128 * c) by reflexivity. subst cs PCR.
    pose proof (max_cached_fits c GC) as [MC1 MC2]. pose proof (max_count_range c GC) as MCR. pose proof (class_size_range c GC) as CSR.
    (* [comment removed for export] *)
    eapply (evtA_srzJ_KJ AL (CSf None None) (K None None) _ _ _ mo (KL None None) HK0); [exact HJ0| |].
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
    assert (RIC1 : ro_cells asegs m1 (A_INSTANCE + 48) [C8 (Z_to_bv 64 RI)]) by (eapply ro_cells_transport; [exact RIC| exact MU1| unfold A_INSTANCE; cbn; clear - LOIMG T0; lia]).
    clear TR1 MX NF MFA AU M40 MUC M56 EX STC TJ SJ SHU SHF HFAR HJS PS TS MWS PPS RIC ST MI PCS.
    (* [comment removed for export] *)
    eapply (getfrom_split AL IMG ALWF CSf CSOKf CSmono_u CSmono_f ASB T CTX SB RI c GSB GC GT GCTX GSEP CST CSCTX CSRI K KL mu mfa
                LEDGER_U TU_commit TU_fresh LEDGER_F TF_commit TF_fresh GMU GMFA CSUz CSFz ROOM_U SCAR_U ROOM_F SCAR_F TA TB)
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
           | |- ro_cells _ _ _ _ => exact RIC1
           | |- stk _ _ _ _ => exact ST1
           | |- crange _ _ _ => first [ exact CSFA | (eapply crange_sub; [exact SCS| clear - SPL; lia| clear - SPL; lia]) ]
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 A_TP => exact TP
           | |- K _ _ _ => exact HK1
           | |- J _ _ => exact HJ1
           | |- forall ok c', _ => idtac
           | |- _ => idtac end.
      all: lazymatch goal with |- forall ok c', _ => idtac | |- _ (@nil _) => assumption | |- _ => first [ sassumption | cassumption | exact GMISS | exact NEEDU | exact UOK | exact HAU | exact HINV | exact AUAL | exact HNF | exact HNF2 | exact HNF3 | exact LFA | exact LJS0 | exact LDS | exact LOIMG | exact MC2
                 | (change (2^18) with 262144; clear - MC1; lia) | (clear - T0 T1 TAL GC SPL SPH SPA; lia) ] end.
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
      eapply (evtA_srzJ_KJ AL (CSf u f) (K u f) _ _ _ mo2 (KL u f) HK2); [exact HJ2| |].
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
      apply (HC false). apply (FIN 0 m3 mo3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ [C4 (cnt c); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))] HK3 HJ3).
      + eapply munch_weaken; [| exact MU3]. clear. solve_sub_fp.
      + exact WM3. + exact MI3. + exact ST3.
      + eapply rw_cells_transport; [exact HPC2| exact MU3| exact WM3|]. cbn. clear - T1 GC LOIMG; lia.
      + split; reflexivity.
    - (* [comment removed for export] *)
      destruct RES2 as (-> & RR).
      pose proof HPC2 as HPCs. change [C4 (cnt c); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))] with ([C4 (cnt c)] ++ [C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))]) in HPCs.
      apply rw_cells_app in HPCs as [HC1 HC2]. cbn [cells_size csize Nat.add] in HC2. change (Z.of_nat 4) with 4 in HC2.
      eapply (evtA_srzJ_KJ AL (CSf u f) (K u f) _ _ _ mo2 (KL u f) HK2); [exact HJ2| |].
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
      apply (HC true). apply (FIN 1 m3 mo3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ [C4 (Z_to_bv 64 (max_count c / 2)); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))] HK3 HJ3).
      + eapply munch_weaken; [| exact MU3]. clear. solve_sub_fp.
      + exact WM3. + exact MI3. + exact ST3.
      + change [C4 (Z_to_bv 64 (max_count c / 2)); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))]
          with ([C4 (Z_to_bv 64 (max_count c / 2))] ++ [C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))]).
        apply rw_cells_app. split; [exact HC1'|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4.
        eapply rw_cells_transport; [exact HC2| exact MU3| exact WM3|]. cbn. clear - T1 GC LOIMG; lia.
      + split; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RefillSplit.

End ARUN_1.
